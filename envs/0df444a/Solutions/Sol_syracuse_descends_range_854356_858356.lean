-- Prove2me | solution 1 for syracuse_descends_range_854356_858356
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:57.738979+00:00
-- url     : https://prove2.me/submissions/501b24ba-d41b-446f-8659-dbebafb88b62

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


theorem B1081345 : Blo 854356 1081345 := bbase (se 2 (by rfl) ⟨405504, by rfl⟩ : syracuseStep 1081345 = 811009) (by norm_num)
theorem B1441813 : Blo 854356 1441813 := bbase (se 6 (by rfl) ⟨33792, by rfl⟩ : syracuseStep 1441813 = 67585) (by norm_num)
theorem B2883653 : Blo 854356 2883653 := bbase (se 4 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 2883653 = 540685) (by norm_num)
theorem B1081441 : Blo 854356 1081441 := bbase (se 2 (by rfl) ⟨405540, by rfl⟩ : syracuseStep 1081441 = 811081) (by norm_num)
theorem B1441901 : Blo 854356 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B2162821 : Blo 854356 2162821 := bbase (se 4 (by rfl) ⟨202764, by rfl⟩ : syracuseStep 2162821 = 405529) (by norm_num)
theorem B1442029 : Blo 854356 1442029 := bbase (se 3 (by rfl) ⟨270380, by rfl⟩ : syracuseStep 1442029 = 540761) (by norm_num)
theorem B2162933 : Blo 854356 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1540349 : Blo 854356 1540349 := bbase (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) (by norm_num)
theorem B1081613 : Blo 854356 1081613 := bbase (se 3 (by rfl) ⟨202802, by rfl⟩ : syracuseStep 1081613 = 405605) (by norm_num)
theorem B1442117 : Blo 854356 1442117 := bbase (se 4 (by rfl) ⟨135198, by rfl⟩ : syracuseStep 1442117 = 270397) (by norm_num)
theorem B1081669 : Blo 854356 1081669 := bbase (se 4 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 1081669 = 202813) (by norm_num)
theorem B1081765 : Blo 854356 1081765 := bbase (se 4 (by rfl) ⟨101415, by rfl⟩ : syracuseStep 1081765 = 202831) (by norm_num)
theorem B2163125 : Blo 854356 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B1442245 : Blo 854356 1442245 := bbase (se 4 (by rfl) ⟨135210, by rfl⟩ : syracuseStep 1442245 = 270421) (by norm_num)
theorem B2884085 : Blo 854356 2884085 := bbase (se 5 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 2884085 = 270383) (by norm_num)
theorem B1442333 : Blo 854356 1442333 := bbase (se 3 (by rfl) ⟨270437, by rfl⟩ : syracuseStep 1442333 = 540875) (by norm_num)
theorem B1081937 : Blo 854356 1081937 := bbase (se 2 (by rfl) ⟨405726, by rfl⟩ : syracuseStep 1081937 = 811453) (by norm_num)
theorem B1081993 : Blo 854356 1081993 := bbase (se 2 (by rfl) ⟨405747, by rfl⟩ : syracuseStep 1081993 = 811495) (by norm_num)
theorem B1442461 : Blo 854356 1442461 := bbase (se 3 (by rfl) ⟨270461, by rfl⟩ : syracuseStep 1442461 = 540923) (by norm_num)
theorem B1082089 : Blo 854356 1082089 := bbase (se 2 (by rfl) ⟨405783, by rfl⟩ : syracuseStep 1082089 = 811567) (by norm_num)
theorem B1442549 : Blo 854356 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B2163469 : Blo 854356 2163469 := bbase (se 3 (by rfl) ⟨405650, by rfl⟩ : syracuseStep 2163469 = 811301) (by norm_num)
theorem B1442677 : Blo 854356 1442677 := bbase (se 5 (by rfl) ⟨67625, by rfl⟩ : syracuseStep 1442677 = 135251) (by norm_num)
theorem B2163581 : Blo 854356 2163581 := bbase (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) (by norm_num)
theorem B1082261 : Blo 854356 1082261 := bbase (se 6 (by rfl) ⟨25365, by rfl⟩ : syracuseStep 1082261 = 50731) (by norm_num)
theorem B1737629 : Blo 854356 1737629 := bbase (se 3 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 1737629 = 651611) (by norm_num)
theorem B2884517 : Blo 854356 2884517 := bbase (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) (by norm_num)
theorem B1442765 : Blo 854356 1442765 := bbase (se 3 (by rfl) ⟨270518, by rfl⟩ : syracuseStep 1442765 = 541037) (by norm_num)
theorem B1082317 : Blo 854356 1082317 := bbase (se 3 (by rfl) ⟨202934, by rfl⟩ : syracuseStep 1082317 = 405869) (by norm_num)
theorem B1082413 : Blo 854356 1082413 := bbase (se 3 (by rfl) ⟨202952, by rfl⟩ : syracuseStep 1082413 = 405905) (by norm_num)
theorem B2163773 : Blo 854356 2163773 := bbase (se 3 (by rfl) ⟨405707, by rfl⟩ : syracuseStep 2163773 = 811415) (by norm_num)
theorem B1442893 : Blo 854356 1442893 := bbase (se 3 (by rfl) ⟨270542, by rfl⟩ : syracuseStep 1442893 = 541085) (by norm_num)
theorem B4326533 : Blo 854356 4326533 := bbase (se 4 (by rfl) ⟨405612, by rfl⟩ : syracuseStep 4326533 = 811225) (by norm_num)
theorem B1442981 : Blo 854356 1442981 := bbase (se 4 (by rfl) ⟨135279, by rfl⟩ : syracuseStep 1442981 = 270559) (by norm_num)
theorem B1082585 : Blo 854356 1082585 := bbase (se 2 (by rfl) ⟨405969, by rfl⟩ : syracuseStep 1082585 = 811939) (by norm_num)
theorem B1082641 : Blo 854356 1082641 := bbase (se 2 (by rfl) ⟨405990, by rfl⟩ : syracuseStep 1082641 = 811981) (by norm_num)
theorem B1443109 : Blo 854356 1443109 := bbase (se 4 (by rfl) ⟨135291, by rfl⟩ : syracuseStep 1443109 = 270583) (by norm_num)
theorem B2884949 : Blo 854356 2884949 := bbase (se 12 (by rfl) ⟨1056, by rfl⟩ : syracuseStep 2884949 = 2113) (by norm_num)
theorem B1082737 : Blo 854356 1082737 := bbase (se 2 (by rfl) ⟨406026, by rfl⟩ : syracuseStep 1082737 = 812053) (by norm_num)
theorem B1443197 : Blo 854356 1443197 := bbase (se 3 (by rfl) ⟨270599, by rfl⟩ : syracuseStep 1443197 = 541199) (by norm_num)
theorem B2164117 : Blo 854356 2164117 := bbase (se 6 (by rfl) ⟨50721, by rfl⟩ : syracuseStep 2164117 = 101443) (by norm_num)
theorem B6489557 : Blo 854356 6489557 := bbase (se 7 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 6489557 = 152099) (by norm_num)
theorem B1443325 : Blo 854356 1443325 := bbase (se 3 (by rfl) ⟨270623, by rfl⟩ : syracuseStep 1443325 = 541247) (by norm_num)
theorem B2164229 : Blo 854356 2164229 := bbase (se 4 (by rfl) ⟨202896, by rfl⟩ : syracuseStep 2164229 = 405793) (by norm_num)
theorem B1082909 : Blo 854356 1082909 := bbase (se 3 (by rfl) ⟨203045, by rfl⟩ : syracuseStep 1082909 = 406091) (by norm_num)
theorem B1443413 : Blo 854356 1443413 := bbase (se 8 (by rfl) ⟨8457, by rfl⟩ : syracuseStep 1443413 = 16915) (by norm_num)
theorem B1082965 : Blo 854356 1082965 := bbase (se 8 (by rfl) ⟨6345, by rfl⟩ : syracuseStep 1082965 = 12691) (by norm_num)
theorem B1083061 : Blo 854356 1083061 := bbase (se 5 (by rfl) ⟨50768, by rfl⟩ : syracuseStep 1083061 = 101537) (by norm_num)
theorem B2164421 : Blo 854356 2164421 := bbase (se 4 (by rfl) ⟨202914, by rfl⟩ : syracuseStep 2164421 = 405829) (by norm_num)
theorem B1443541 : Blo 854356 1443541 := bbase (se 7 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 1443541 = 33833) (by norm_num)
theorem B2885381 : Blo 854356 2885381 := bbase (se 4 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 2885381 = 541009) (by norm_num)
theorem B1443629 : Blo 854356 1443629 := bbase (se 3 (by rfl) ⟨270680, by rfl⟩ : syracuseStep 1443629 = 541361) (by norm_num)
theorem B1083233 : Blo 854356 1083233 := bbase (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) (by norm_num)
theorem B1542037 : Blo 854356 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B1083289 : Blo 854356 1083289 := bbase (se 2 (by rfl) ⟨406233, by rfl⟩ : syracuseStep 1083289 = 812467) (by norm_num)
theorem B1443757 : Blo 854356 1443757 := bbase (se 3 (by rfl) ⟨270704, by rfl⟩ : syracuseStep 1443757 = 541409) (by norm_num)
theorem B1083385 : Blo 854356 1083385 := bbase (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) (by norm_num)
theorem B1443845 : Blo 854356 1443845 := bbase (se 4 (by rfl) ⟨135360, by rfl⟩ : syracuseStep 1443845 = 270721) (by norm_num)
theorem B3246101 : Blo 854356 3246101 := bbase (se 6 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 3246101 = 152161) (by norm_num)
theorem B2164765 : Blo 854356 2164765 := bbase (se 3 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 2164765 = 811787) (by norm_num)
theorem B1542245 : Blo 854356 1542245 := bbase (se 4 (by rfl) ⟨144585, by rfl⟩ : syracuseStep 1542245 = 289171) (by norm_num)
theorem B1542253 : Blo 854356 1542253 := bbase (se 3 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 1542253 = 578345) (by norm_num)
theorem B3082373 : Blo 854356 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B1443973 : Blo 854356 1443973 := bbase (se 4 (by rfl) ⟨135372, by rfl⟩ : syracuseStep 1443973 = 270745) (by norm_num)
theorem B2164877 : Blo 854356 2164877 := bbase (se 3 (by rfl) ⟨405914, by rfl⟩ : syracuseStep 2164877 = 811829) (by norm_num)
theorem B1083557 : Blo 854356 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B2885813 : Blo 854356 2885813 := bbase (se 5 (by rfl) ⟨135272, by rfl⟩ : syracuseStep 2885813 = 270545) (by norm_num)
theorem B1444061 : Blo 854356 1444061 := bbase (se 3 (by rfl) ⟨270761, by rfl⟩ : syracuseStep 1444061 = 541523) (by norm_num)
theorem B1083613 : Blo 854356 1083613 := bbase (se 3 (by rfl) ⟨203177, by rfl⟩ : syracuseStep 1083613 = 406355) (by norm_num)
theorem B1542397 : Blo 854356 1542397 := bbase (se 3 (by rfl) ⟨289199, by rfl⟩ : syracuseStep 1542397 = 578399) (by norm_num)
theorem B3246389 : Blo 854356 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B1083709 : Blo 854356 1083709 := bbase (se 3 (by rfl) ⟨203195, by rfl⟩ : syracuseStep 1083709 = 406391) (by norm_num)
theorem B2165069 : Blo 854356 2165069 := bbase (se 3 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 2165069 = 811901) (by norm_num)
theorem B1444189 : Blo 854356 1444189 := bbase (se 3 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 1444189 = 541571) (by norm_num)
theorem B4327829 : Blo 854356 4327829 := bbase (se 6 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 4327829 = 202867) (by norm_num)
theorem B3082645 : Blo 854356 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B1444277 : Blo 854356 1444277 := bbase (se 5 (by rfl) ⟨67700, by rfl⟩ : syracuseStep 1444277 = 135401) (by norm_num)
theorem B1083881 : Blo 854356 1083881 := bbase (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) (by norm_num)
theorem B1083937 : Blo 854356 1083937 := bbase (se 2 (by rfl) ⟨406476, by rfl⟩ : syracuseStep 1083937 = 812953) (by norm_num)
theorem B3082805 : Blo 854356 3082805 := bbase (se 5 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 3082805 = 289013) (by norm_num)
theorem B1444405 : Blo 854356 1444405 := bbase (se 5 (by rfl) ⟨67706, by rfl⟩ : syracuseStep 1444405 = 135413) (by norm_num)
theorem B2886245 : Blo 854356 2886245 := bbase (se 4 (by rfl) ⟨270585, by rfl⟩ : syracuseStep 2886245 = 541171) (by norm_num)
theorem B1084033 : Blo 854356 1084033 := bbase (se 2 (by rfl) ⟨406512, by rfl⟩ : syracuseStep 1084033 = 813025) (by norm_num)
theorem B1444493 : Blo 854356 1444493 := bbase (se 3 (by rfl) ⟨270842, by rfl⟩ : syracuseStep 1444493 = 541685) (by norm_num)
theorem B2165413 : Blo 854356 2165413 := bbase (se 4 (by rfl) ⟨203007, by rfl⟩ : syracuseStep 2165413 = 406015) (by norm_num)
theorem B1444621 : Blo 854356 1444621 := bbase (se 3 (by rfl) ⟨270866, by rfl⟩ : syracuseStep 1444621 = 541733) (by norm_num)
theorem B2165525 : Blo 854356 2165525 := bbase (se 6 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 2165525 = 101509) (by norm_num)
theorem B1084205 : Blo 854356 1084205 := bbase (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) (by norm_num)
theorem B1444709 : Blo 854356 1444709 := bbase (se 4 (by rfl) ⟨135441, by rfl⟩ : syracuseStep 1444709 = 270883) (by norm_num)
theorem B1084261 : Blo 854356 1084261 := bbase (se 4 (by rfl) ⟨101649, by rfl⟩ : syracuseStep 1084261 = 203299) (by norm_num)
theorem B1084357 : Blo 854356 1084357 := bbase (se 4 (by rfl) ⟨101658, by rfl⟩ : syracuseStep 1084357 = 203317) (by norm_num)
theorem B1543117 : Blo 854356 1543117 := bbase (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) (by norm_num)
theorem B2165717 : Blo 854356 2165717 := bbase (se 7 (by rfl) ⟨25379, by rfl⟩ : syracuseStep 2165717 = 50759) (by norm_num)
theorem B1444837 : Blo 854356 1444837 := bbase (se 4 (by rfl) ⟨135453, by rfl⟩ : syracuseStep 1444837 = 270907) (by norm_num)
theorem B6163445 : Blo 854356 6163445 := bbase (se 5 (by rfl) ⟨288911, by rfl⟩ : syracuseStep 6163445 = 577823) (by norm_num)
theorem B2886677 : Blo 854356 2886677 := bbase (se 6 (by rfl) ⟨67656, by rfl⟩ : syracuseStep 2886677 = 135313) (by norm_num)
theorem B1543205 : Blo 854356 1543205 := bbase (se 4 (by rfl) ⟨144675, by rfl⟩ : syracuseStep 1543205 = 289351) (by norm_num)
theorem B1444925 : Blo 854356 1444925 := bbase (se 3 (by rfl) ⟨270923, by rfl⟩ : syracuseStep 1444925 = 541847) (by norm_num)
theorem B1084529 : Blo 854356 1084529 := bbase (se 2 (by rfl) ⟨406698, by rfl⟩ : syracuseStep 1084529 = 813397) (by norm_num)
theorem B1084585 : Blo 854356 1084585 := bbase (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) (by norm_num)
theorem B1445053 : Blo 854356 1445053 := bbase (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) (by norm_num)
theorem B1739981 : Blo 854356 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B11144405 : Blo 854356 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B1084681 : Blo 854356 1084681 := bbase (se 2 (by rfl) ⟨406755, by rfl⟩ : syracuseStep 1084681 = 813511) (by norm_num)
theorem B1445141 : Blo 854356 1445141 := bbase (se 6 (by rfl) ⟨33870, by rfl⟩ : syracuseStep 1445141 = 67741) (by norm_num)
theorem B2166061 : Blo 854356 2166061 := bbase (se 3 (by rfl) ⟨406136, by rfl⟩ : syracuseStep 2166061 = 812273) (by norm_num)
theorem B1445269 : Blo 854356 1445269 := bbase (se 6 (by rfl) ⟨33873, by rfl⟩ : syracuseStep 1445269 = 67747) (by norm_num)
theorem B2166173 : Blo 854356 2166173 := bbase (se 3 (by rfl) ⟨406157, by rfl⟩ : syracuseStep 2166173 = 812315) (by norm_num)
theorem B4623797 : Blo 854356 4623797 := bbase (se 5 (by rfl) ⟨216740, by rfl⟩ : syracuseStep 4623797 = 433481) (by norm_num)
theorem B1084853 : Blo 854356 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B2887109 : Blo 854356 2887109 := bbase (se 4 (by rfl) ⟨270666, by rfl⟩ : syracuseStep 2887109 = 541333) (by norm_num)
theorem B3247573 : Blo 854356 3247573 := bbase (se 7 (by rfl) ⟨38057, by rfl⟩ : syracuseStep 3247573 = 76115) (by norm_num)
theorem B1543637 : Blo 854356 1543637 := bbase (se 7 (by rfl) ⟨18089, by rfl⟩ : syracuseStep 1543637 = 36179) (by norm_num)
theorem B1445357 : Blo 854356 1445357 := bbase (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) (by norm_num)
theorem B1084909 : Blo 854356 1084909 := bbase (se 3 (by rfl) ⟨203420, by rfl⟩ : syracuseStep 1084909 = 406841) (by norm_num)
theorem B1609205 : Blo 854356 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B1281557 : Blo 854356 1281557 := bbase (se 6 (by rfl) ⟨30036, by rfl⟩ : syracuseStep 1281557 = 60073) (by norm_num)
theorem B5213717 : Blo 854356 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B1281581 : Blo 854356 1281581 := bbase (se 3 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 1281581 = 480593) (by norm_num)
theorem B1281605 : Blo 854356 1281605 := bbase (se 4 (by rfl) ⟨120150, by rfl⟩ : syracuseStep 1281605 = 240301) (by norm_num)
theorem B1085005 : Blo 854356 1085005 := bbase (se 3 (by rfl) ⟨203438, by rfl⟩ : syracuseStep 1085005 = 406877) (by norm_num)
theorem B1281629 : Blo 854356 1281629 := bbase (se 3 (by rfl) ⟨240305, by rfl⟩ : syracuseStep 1281629 = 480611) (by norm_num)
theorem B2166365 : Blo 854356 2166365 := bbase (se 3 (by rfl) ⟨406193, by rfl⟩ : syracuseStep 2166365 = 812387) (by norm_num)
theorem B1543781 : Blo 854356 1543781 := bbase (se 4 (by rfl) ⟨144729, by rfl⟩ : syracuseStep 1543781 = 289459) (by norm_num)
theorem B1445485 : Blo 854356 1445485 := bbase (se 3 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 1445485 = 542057) (by norm_num)
theorem B1281653 : Blo 854356 1281653 := bbase (se 5 (by rfl) ⟨60077, by rfl⟩ : syracuseStep 1281653 = 120155) (by norm_num)
theorem B1281677 : Blo 854356 1281677 := bbase (se 3 (by rfl) ⟨240314, by rfl⟩ : syracuseStep 1281677 = 480629) (by norm_num)
theorem B1805981 : Blo 854356 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B1281701 : Blo 854356 1281701 := bbase (se 4 (by rfl) ⟨120159, by rfl⟩ : syracuseStep 1281701 = 240319) (by norm_num)
theorem B4329125 : Blo 854356 4329125 := bbase (se 4 (by rfl) ⟨405855, by rfl⟩ : syracuseStep 4329125 = 811711) (by norm_num)
theorem B1281725 : Blo 854356 1281725 := bbase (se 3 (by rfl) ⟨240323, by rfl⟩ : syracuseStep 1281725 = 480647) (by norm_num)
theorem B1445573 : Blo 854356 1445573 := bbase (se 4 (by rfl) ⟨135522, by rfl⟩ : syracuseStep 1445573 = 271045) (by norm_num)
theorem B1281749 : Blo 854356 1281749 := bbase (se 7 (by rfl) ⟨15020, by rfl⟩ : syracuseStep 1281749 = 30041) (by norm_num)
theorem B1281773 : Blo 854356 1281773 := bbase (se 3 (by rfl) ⟨240332, by rfl⟩ : syracuseStep 1281773 = 480665) (by norm_num)
theorem B1085177 : Blo 854356 1085177 := bbase (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) (by norm_num)
theorem B1281797 : Blo 854356 1281797 := bbase (se 4 (by rfl) ⟨120168, by rfl⟩ : syracuseStep 1281797 = 240337) (by norm_num)
theorem B3247877 : Blo 854356 3247877 := bbase (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) (by norm_num)
theorem B1281821 : Blo 854356 1281821 := bbase (se 3 (by rfl) ⟨240341, by rfl⟩ : syracuseStep 1281821 = 480683) (by norm_num)
theorem B1085233 : Blo 854356 1085233 := bbase (se 2 (by rfl) ⟨406962, by rfl⟩ : syracuseStep 1085233 = 813925) (by norm_num)
theorem B1281845 : Blo 854356 1281845 := bbase (se 5 (by rfl) ⟨60086, by rfl⟩ : syracuseStep 1281845 = 120173) (by norm_num)
theorem B1543997 : Blo 854356 1543997 := bbase (se 3 (by rfl) ⟨289499, by rfl⟩ : syracuseStep 1543997 = 578999) (by norm_num)
theorem B1445701 : Blo 854356 1445701 := bbase (se 4 (by rfl) ⟨135534, by rfl⟩ : syracuseStep 1445701 = 271069) (by norm_num)
theorem B1281869 : Blo 854356 1281869 := bbase (se 3 (by rfl) ⟨240350, by rfl⟩ : syracuseStep 1281869 = 480701) (by norm_num)
theorem B35163989 : Blo 854356 35163989 := bbase (se 9 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 35163989 = 206039) (by norm_num)
theorem B18550613 : Blo 854356 18550613 := bbase (se 9 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 18550613 = 108695) (by norm_num)
theorem B1281893 : Blo 854356 1281893 := bbase (se 4 (by rfl) ⟨120177, by rfl⟩ : syracuseStep 1281893 = 240355) (by norm_num)
theorem B2887541 : Blo 854356 2887541 := bbase (se 5 (by rfl) ⟨135353, by rfl⟩ : syracuseStep 2887541 = 270707) (by norm_num)
theorem B1281917 : Blo 854356 1281917 := bbase (se 3 (by rfl) ⟨240359, by rfl⟩ : syracuseStep 1281917 = 480719) (by norm_num)
theorem B1085329 : Blo 854356 1085329 := bbase (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) (by norm_num)
theorem B1281941 : Blo 854356 1281941 := bbase (se 6 (by rfl) ⟨30045, by rfl⟩ : syracuseStep 1281941 = 60091) (by norm_num)
theorem B1445789 : Blo 854356 1445789 := bbase (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) (by norm_num)
theorem B1281965 : Blo 854356 1281965 := bbase (se 3 (by rfl) ⟨240368, by rfl⟩ : syracuseStep 1281965 = 480737) (by norm_num)
theorem B2166709 : Blo 854356 2166709 := bbase (se 5 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 2166709 = 203129) (by norm_num)
theorem B1281989 : Blo 854356 1281989 := bbase (se 4 (by rfl) ⟨120186, by rfl⟩ : syracuseStep 1281989 = 240373) (by norm_num)
theorem B1282013 : Blo 854356 1282013 := bbase (se 3 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 1282013 = 480755) (by norm_num)
theorem B1282037 : Blo 854356 1282037 := bbase (se 5 (by rfl) ⟨60095, by rfl⟩ : syracuseStep 1282037 = 120191) (by norm_num)
theorem B1282061 : Blo 854356 1282061 := bbase (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) (by norm_num)
theorem B1445917 : Blo 854356 1445917 := bbase (se 3 (by rfl) ⟨271109, by rfl⟩ : syracuseStep 1445917 = 542219) (by norm_num)
theorem B1282085 : Blo 854356 1282085 := bbase (se 4 (by rfl) ⟨120195, by rfl⟩ : syracuseStep 1282085 = 240391) (by norm_num)
theorem B2166821 : Blo 854356 2166821 := bbase (se 4 (by rfl) ⟨203139, by rfl⟩ : syracuseStep 2166821 = 406279) (by norm_num)
theorem B1282109 : Blo 854356 1282109 := bbase (se 3 (by rfl) ⟨240395, by rfl⟩ : syracuseStep 1282109 = 480791) (by norm_num)
theorem B1085501 : Blo 854356 1085501 := bbase (se 3 (by rfl) ⟨203531, by rfl⟩ : syracuseStep 1085501 = 407063) (by norm_num)
theorem B1282133 : Blo 854356 1282133 := bbase (se 8 (by rfl) ⟨7512, by rfl⟩ : syracuseStep 1282133 = 15025) (by norm_num)
theorem B1282157 : Blo 854356 1282157 := bbase (se 3 (by rfl) ⟨240404, by rfl⟩ : syracuseStep 1282157 = 480809) (by norm_num)
theorem B1446005 : Blo 854356 1446005 := bbase (se 5 (by rfl) ⟨67781, by rfl⟩ : syracuseStep 1446005 = 135563) (by norm_num)
theorem B1085557 : Blo 854356 1085557 := bbase (se 5 (by rfl) ⟨50885, by rfl⟩ : syracuseStep 1085557 = 101771) (by norm_num)
theorem B1282181 : Blo 854356 1282181 := bbase (se 4 (by rfl) ⟨120204, by rfl⟩ : syracuseStep 1282181 = 240409) (by norm_num)
theorem B2199701 : Blo 854356 2199701 := bbase (se 6 (by rfl) ⟨51555, by rfl⟩ : syracuseStep 2199701 = 103111) (by norm_num)
theorem B1282205 : Blo 854356 1282205 := bbase (se 3 (by rfl) ⟨240413, by rfl⟩ : syracuseStep 1282205 = 480827) (by norm_num)
theorem B1282229 : Blo 854356 1282229 := bbase (se 5 (by rfl) ⟨60104, by rfl⟩ : syracuseStep 1282229 = 120209) (by norm_num)
theorem B1282253 : Blo 854356 1282253 := bbase (se 3 (by rfl) ⟨240422, by rfl⟩ : syracuseStep 1282253 = 480845) (by norm_num)
theorem B1085653 : Blo 854356 1085653 := bbase (se 7 (by rfl) ⟨12722, by rfl⟩ : syracuseStep 1085653 = 25445) (by norm_num)
theorem B1282277 : Blo 854356 1282277 := bbase (se 4 (by rfl) ⟨120213, by rfl⟩ : syracuseStep 1282277 = 240427) (by norm_num)
theorem B2167013 : Blo 854356 2167013 := bbase (se 4 (by rfl) ⟨203157, by rfl⟩ : syracuseStep 2167013 = 406315) (by norm_num)
theorem B1446133 : Blo 854356 1446133 := bbase (se 5 (by rfl) ⟨67787, by rfl⟩ : syracuseStep 1446133 = 135575) (by norm_num)
theorem B1282301 : Blo 854356 1282301 := bbase (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) (by norm_num)
theorem B1282325 : Blo 854356 1282325 := bbase (se 6 (by rfl) ⟨30054, by rfl⟩ : syracuseStep 1282325 = 60109) (by norm_num)
theorem B2887973 : Blo 854356 2887973 := bbase (se 4 (by rfl) ⟨270747, by rfl⟩ : syracuseStep 2887973 = 541495) (by norm_num)
theorem B1282349 : Blo 854356 1282349 := bbase (se 3 (by rfl) ⟨240440, by rfl⟩ : syracuseStep 1282349 = 480881) (by norm_num)
theorem B1282373 : Blo 854356 1282373 := bbase (se 4 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 1282373 = 240445) (by norm_num)
theorem B1446221 : Blo 854356 1446221 := bbase (se 3 (by rfl) ⟨271166, by rfl⟩ : syracuseStep 1446221 = 542333) (by norm_num)
theorem B5476693 : Blo 854356 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B1282397 : Blo 854356 1282397 := bbase (se 3 (by rfl) ⟨240449, by rfl⟩ : syracuseStep 1282397 = 480899) (by norm_num)
theorem B1282421 : Blo 854356 1282421 := bbase (se 5 (by rfl) ⟨60113, by rfl⟩ : syracuseStep 1282421 = 120227) (by norm_num)
theorem B1085825 : Blo 854356 1085825 := bbase (se 2 (by rfl) ⟨407184, by rfl⟩ : syracuseStep 1085825 = 814369) (by norm_num)
theorem B1282445 : Blo 854356 1282445 := bbase (se 3 (by rfl) ⟨240458, by rfl⟩ : syracuseStep 1282445 = 480917) (by norm_num)
theorem B1282469 : Blo 854356 1282469 := bbase (se 4 (by rfl) ⟨120231, by rfl⟩ : syracuseStep 1282469 = 240463) (by norm_num)
theorem B1085881 : Blo 854356 1085881 := bbase (se 2 (by rfl) ⟨407205, by rfl⟩ : syracuseStep 1085881 = 814411) (by norm_num)
theorem B1282493 : Blo 854356 1282493 := bbase (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) (by norm_num)
theorem B1446349 : Blo 854356 1446349 := bbase (se 3 (by rfl) ⟨271190, by rfl⟩ : syracuseStep 1446349 = 542381) (by norm_num)
theorem B1282517 : Blo 854356 1282517 := bbase (se 7 (by rfl) ⟨15029, by rfl⟩ : syracuseStep 1282517 = 30059) (by norm_num)
theorem B1282541 : Blo 854356 1282541 := bbase (se 3 (by rfl) ⟨240476, by rfl⟩ : syracuseStep 1282541 = 480953) (by norm_num)
theorem B1282565 : Blo 854356 1282565 := bbase (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) (by norm_num)
theorem B1085977 : Blo 854356 1085977 := bbase (se 2 (by rfl) ⟨407241, by rfl⟩ : syracuseStep 1085977 = 814483) (by norm_num)
theorem B1282589 : Blo 854356 1282589 := bbase (se 3 (by rfl) ⟨240485, by rfl⟩ : syracuseStep 1282589 = 480971) (by norm_num)
theorem B1446437 : Blo 854356 1446437 := bbase (se 4 (by rfl) ⟨135603, by rfl⟩ : syracuseStep 1446437 = 271207) (by norm_num)
theorem B1282613 : Blo 854356 1282613 := bbase (se 5 (by rfl) ⟨60122, by rfl⟩ : syracuseStep 1282613 = 120245) (by norm_num)
theorem B2167357 : Blo 854356 2167357 := bbase (se 3 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 2167357 = 812759) (by norm_num)
theorem B1282637 : Blo 854356 1282637 := bbase (se 3 (by rfl) ⟨240494, by rfl⟩ : syracuseStep 1282637 = 480989) (by norm_num)
theorem B1544789 : Blo 854356 1544789 := bbase (se 8 (by rfl) ⟨9051, by rfl⟩ : syracuseStep 1544789 = 18103) (by norm_num)
theorem B4887125 : Blo 854356 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B1282661 : Blo 854356 1282661 := bbase (se 4 (by rfl) ⟨120249, by rfl⟩ : syracuseStep 1282661 = 240499) (by norm_num)
theorem B1282685 : Blo 854356 1282685 := bbase (se 3 (by rfl) ⟨240503, by rfl⟩ : syracuseStep 1282685 = 481007) (by norm_num)
theorem B1282709 : Blo 854356 1282709 := bbase (se 6 (by rfl) ⟨30063, by rfl⟩ : syracuseStep 1282709 = 60127) (by norm_num)
theorem B1446565 : Blo 854356 1446565 := bbase (se 4 (by rfl) ⟨135615, by rfl⟩ : syracuseStep 1446565 = 271231) (by norm_num)
theorem B1217197 : Blo 854356 1217197 := bbase (se 3 (by rfl) ⟨228224, by rfl⟩ : syracuseStep 1217197 = 456449) (by norm_num)
theorem B1282733 : Blo 854356 1282733 := bbase (se 3 (by rfl) ⟨240512, by rfl⟩ : syracuseStep 1282733 = 481025) (by norm_num)
theorem B2167469 : Blo 854356 2167469 := bbase (se 3 (by rfl) ⟨406400, by rfl⟩ : syracuseStep 2167469 = 812801) (by norm_num)
theorem B2200253 : Blo 854356 2200253 := bbase (se 3 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 2200253 = 825095) (by norm_num)
theorem B1282757 : Blo 854356 1282757 := bbase (se 4 (by rfl) ⟨120258, by rfl⟩ : syracuseStep 1282757 = 240517) (by norm_num)
theorem B1086149 : Blo 854356 1086149 := bbase (se 4 (by rfl) ⟨101826, by rfl⟩ : syracuseStep 1086149 = 203653) (by norm_num)
theorem B2888405 : Blo 854356 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B1282781 : Blo 854356 1282781 := bbase (se 3 (by rfl) ⟨240521, by rfl⟩ : syracuseStep 1282781 = 481043) (by norm_num)
theorem B1282805 : Blo 854356 1282805 := bbase (se 5 (by rfl) ⟨60131, by rfl⟩ : syracuseStep 1282805 = 120263) (by norm_num)
theorem B1446653 : Blo 854356 1446653 := bbase (se 3 (by rfl) ⟨271247, by rfl⟩ : syracuseStep 1446653 = 542495) (by norm_num)
theorem B1086205 : Blo 854356 1086205 := bbase (se 3 (by rfl) ⟨203663, by rfl⟩ : syracuseStep 1086205 = 407327) (by norm_num)
theorem B1282829 : Blo 854356 1282829 := bbase (se 3 (by rfl) ⟨240530, by rfl⟩ : syracuseStep 1282829 = 481061) (by norm_num)
theorem B1282853 : Blo 854356 1282853 := bbase (se 4 (by rfl) ⟨120267, by rfl⟩ : syracuseStep 1282853 = 240535) (by norm_num)
theorem B1545013 : Blo 854356 1545013 := bbase (se 5 (by rfl) ⟨72422, by rfl⟩ : syracuseStep 1545013 = 144845) (by norm_num)
theorem B1282877 : Blo 854356 1282877 := bbase (se 3 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 1282877 = 481079) (by norm_num)
theorem B1282901 : Blo 854356 1282901 := bbase (se 9 (by rfl) ⟨3758, by rfl⟩ : syracuseStep 1282901 = 7517) (by norm_num)
theorem B1086301 : Blo 854356 1086301 := bbase (se 3 (by rfl) ⟨203681, by rfl⟩ : syracuseStep 1086301 = 407363) (by norm_num)
theorem B1282925 : Blo 854356 1282925 := bbase (se 3 (by rfl) ⟨240548, by rfl⟩ : syracuseStep 1282925 = 481097) (by norm_num)
theorem B2167661 : Blo 854356 2167661 := bbase (se 3 (by rfl) ⟨406436, by rfl⟩ : syracuseStep 2167661 = 812873) (by norm_num)
theorem B1446781 : Blo 854356 1446781 := bbase (se 3 (by rfl) ⟨271271, by rfl⟩ : syracuseStep 1446781 = 542543) (by norm_num)
theorem B1282949 : Blo 854356 1282949 := bbase (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) (by norm_num)
theorem B1282973 : Blo 854356 1282973 := bbase (se 3 (by rfl) ⟨240557, by rfl⟩ : syracuseStep 1282973 = 481115) (by norm_num)
theorem B1282997 : Blo 854356 1282997 := bbase (se 5 (by rfl) ⟨60140, by rfl⟩ : syracuseStep 1282997 = 120281) (by norm_num)
theorem B4330421 : Blo 854356 4330421 := bbase (se 5 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 4330421 = 405977) (by norm_num)
theorem B1283021 : Blo 854356 1283021 := bbase (se 3 (by rfl) ⟨240566, by rfl⟩ : syracuseStep 1283021 = 481133) (by norm_num)
theorem B1446869 : Blo 854356 1446869 := bbase (se 7 (by rfl) ⟨16955, by rfl⟩ : syracuseStep 1446869 = 33911) (by norm_num)
theorem B1283045 : Blo 854356 1283045 := bbase (se 4 (by rfl) ⟨120285, by rfl⟩ : syracuseStep 1283045 = 240571) (by norm_num)
theorem B1217533 : Blo 854356 1217533 := bbase (se 3 (by rfl) ⟨228287, by rfl⟩ : syracuseStep 1217533 = 456575) (by norm_num)
theorem B1283069 : Blo 854356 1283069 := bbase (se 3 (by rfl) ⟨240575, by rfl⟩ : syracuseStep 1283069 = 481151) (by norm_num)
theorem B1283093 : Blo 854356 1283093 := bbase (se 6 (by rfl) ⟨30072, by rfl⟩ : syracuseStep 1283093 = 60145) (by norm_num)
theorem B1283117 : Blo 854356 1283117 := bbase (se 3 (by rfl) ⟨240584, by rfl⟩ : syracuseStep 1283117 = 481169) (by norm_num)
theorem B1283141 : Blo 854356 1283141 := bbase (se 4 (by rfl) ⟨120294, by rfl⟩ : syracuseStep 1283141 = 240589) (by norm_num)
theorem B1446997 : Blo 854356 1446997 := bbase (se 8 (by rfl) ⟨8478, by rfl⟩ : syracuseStep 1446997 = 16957) (by norm_num)
theorem B1283165 : Blo 854356 1283165 := bbase (se 3 (by rfl) ⟨240593, by rfl⟩ : syracuseStep 1283165 = 481187) (by norm_num)
theorem B1283189 : Blo 854356 1283189 := bbase (se 5 (by rfl) ⟨60149, by rfl⟩ : syracuseStep 1283189 = 120299) (by norm_num)
theorem B2888837 : Blo 854356 2888837 := bbase (se 4 (by rfl) ⟨270828, by rfl⟩ : syracuseStep 2888837 = 541657) (by norm_num)
theorem B1283213 : Blo 854356 1283213 := bbase (se 3 (by rfl) ⟨240602, by rfl⟩ : syracuseStep 1283213 = 481205) (by norm_num)
theorem B1283237 : Blo 854356 1283237 := bbase (se 4 (by rfl) ⟨120303, by rfl⟩ : syracuseStep 1283237 = 240607) (by norm_num)
theorem B1447085 : Blo 854356 1447085 := bbase (se 3 (by rfl) ⟨271328, by rfl⟩ : syracuseStep 1447085 = 542657) (by norm_num)
theorem B1283261 : Blo 854356 1283261 := bbase (se 3 (by rfl) ⟨240611, by rfl⟩ : syracuseStep 1283261 = 481223) (by norm_num)
theorem B2168005 : Blo 854356 2168005 := bbase (se 4 (by rfl) ⟨203250, by rfl⟩ : syracuseStep 2168005 = 406501) (by norm_num)
theorem B1217749 : Blo 854356 1217749 := bbase (se 7 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 1217749 = 28541) (by norm_num)
theorem B1283285 : Blo 854356 1283285 := bbase (se 7 (by rfl) ⟨15038, by rfl⟩ : syracuseStep 1283285 = 30077) (by norm_num)
theorem B1283309 : Blo 854356 1283309 := bbase (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) (by norm_num)
theorem B1283333 : Blo 854356 1283333 := bbase (se 4 (by rfl) ⟨120312, by rfl⟩ : syracuseStep 1283333 = 240625) (by norm_num)
theorem B3085573 : Blo 854356 3085573 := bbase (se 4 (by rfl) ⟨289272, by rfl⟩ : syracuseStep 3085573 = 578545) (by norm_num)
theorem B1283357 : Blo 854356 1283357 := bbase (se 3 (by rfl) ⟨240629, by rfl⟩ : syracuseStep 1283357 = 481259) (by norm_num)
theorem B1447213 : Blo 854356 1447213 := bbase (se 3 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 1447213 = 542705) (by norm_num)
theorem B1283381 : Blo 854356 1283381 := bbase (se 5 (by rfl) ⟨60158, by rfl⟩ : syracuseStep 1283381 = 120317) (by norm_num)
theorem B2168117 : Blo 854356 2168117 := bbase (se 5 (by rfl) ⟨101630, by rfl⟩ : syracuseStep 2168117 = 203261) (by norm_num)
theorem B1283405 : Blo 854356 1283405 := bbase (se 3 (by rfl) ⟨240638, by rfl⟩ : syracuseStep 1283405 = 481277) (by norm_num)
theorem B1283429 : Blo 854356 1283429 := bbase (se 4 (by rfl) ⟨120321, by rfl⟩ : syracuseStep 1283429 = 240643) (by norm_num)
theorem B1283453 : Blo 854356 1283453 := bbase (se 3 (by rfl) ⟨240647, by rfl⟩ : syracuseStep 1283453 = 481295) (by norm_num)
theorem B1447301 : Blo 854356 1447301 := bbase (se 4 (by rfl) ⟨135684, by rfl⟩ : syracuseStep 1447301 = 271369) (by norm_num)
theorem B1283477 : Blo 854356 1283477 := bbase (se 6 (by rfl) ⟨30081, by rfl⟩ : syracuseStep 1283477 = 60163) (by norm_num)
theorem B1283501 : Blo 854356 1283501 := bbase (se 3 (by rfl) ⟨240656, by rfl⟩ : syracuseStep 1283501 = 481313) (by norm_num)
theorem B1283525 : Blo 854356 1283525 := bbase (se 4 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 1283525 = 240661) (by norm_num)
theorem B1283549 : Blo 854356 1283549 := bbase (se 3 (by rfl) ⟨240665, by rfl⟩ : syracuseStep 1283549 = 481331) (by norm_num)
theorem B1283573 : Blo 854356 1283573 := bbase (se 5 (by rfl) ⟨60167, by rfl⟩ : syracuseStep 1283573 = 120335) (by norm_num)
theorem B2168309 : Blo 854356 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B1447429 : Blo 854356 1447429 := bbase (se 4 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 1447429 = 271393) (by norm_num)
theorem B1283597 : Blo 854356 1283597 := bbase (se 3 (by rfl) ⟨240674, by rfl⟩ : syracuseStep 1283597 = 481349) (by norm_num)
theorem B1283621 : Blo 854356 1283621 := bbase (se 4 (by rfl) ⟨120339, by rfl⟩ : syracuseStep 1283621 = 240679) (by norm_num)
theorem B2889269 : Blo 854356 2889269 := bbase (se 5 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 2889269 = 270869) (by norm_num)
theorem B1283645 : Blo 854356 1283645 := bbase (se 3 (by rfl) ⟨240683, by rfl⟩ : syracuseStep 1283645 = 481367) (by norm_num)
theorem B1218125 : Blo 854356 1218125 := bbase (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) (by norm_num)
theorem B1283669 : Blo 854356 1283669 := bbase (se 8 (by rfl) ⟨7521, by rfl⟩ : syracuseStep 1283669 = 15043) (by norm_num)
theorem B1447517 : Blo 854356 1447517 := bbase (se 3 (by rfl) ⟨271409, by rfl⟩ : syracuseStep 1447517 = 542819) (by norm_num)
theorem B1283693 : Blo 854356 1283693 := bbase (se 3 (by rfl) ⟨240692, by rfl⟩ : syracuseStep 1283693 = 481385) (by norm_num)
theorem B1283717 : Blo 854356 1283717 := bbase (se 4 (by rfl) ⟨120348, by rfl⟩ : syracuseStep 1283717 = 240697) (by norm_num)
theorem B1283741 : Blo 854356 1283741 := bbase (se 3 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 1283741 = 481403) (by norm_num)
theorem B1283765 : Blo 854356 1283765 := bbase (se 5 (by rfl) ⟨60176, by rfl⟩ : syracuseStep 1283765 = 120353) (by norm_num)
theorem B1283789 : Blo 854356 1283789 := bbase (se 3 (by rfl) ⟨240710, by rfl⟩ : syracuseStep 1283789 = 481421) (by norm_num)
theorem B1447645 : Blo 854356 1447645 := bbase (se 3 (by rfl) ⟨271433, by rfl⟩ : syracuseStep 1447645 = 542867) (by norm_num)
theorem B1283813 : Blo 854356 1283813 := bbase (se 4 (by rfl) ⟨120357, by rfl⟩ : syracuseStep 1283813 = 240715) (by norm_num)
theorem B4888309 : Blo 854356 4888309 := bbase (se 5 (by rfl) ⟨229139, by rfl⟩ : syracuseStep 4888309 = 458279) (by norm_num)
theorem B1283837 : Blo 854356 1283837 := bbase (se 3 (by rfl) ⟨240719, by rfl⟩ : syracuseStep 1283837 = 481439) (by norm_num)
theorem B1283861 : Blo 854356 1283861 := bbase (se 6 (by rfl) ⟨30090, by rfl⟩ : syracuseStep 1283861 = 60181) (by norm_num)
theorem B1283885 : Blo 854356 1283885 := bbase (se 3 (by rfl) ⟨240728, by rfl⟩ : syracuseStep 1283885 = 481457) (by norm_num)
theorem B1447733 : Blo 854356 1447733 := bbase (se 5 (by rfl) ⟨67862, by rfl⟩ : syracuseStep 1447733 = 135725) (by norm_num)
theorem B1283909 : Blo 854356 1283909 := bbase (se 4 (by rfl) ⟨120366, by rfl⟩ : syracuseStep 1283909 = 240733) (by norm_num)
theorem B3249989 : Blo 854356 3249989 := bbase (se 4 (by rfl) ⟨304686, by rfl⟩ : syracuseStep 3249989 = 609373) (by norm_num)
theorem B2168653 : Blo 854356 2168653 := bbase (se 3 (by rfl) ⟨406622, by rfl⟩ : syracuseStep 2168653 = 813245) (by norm_num)
theorem B1283933 : Blo 854356 1283933 := bbase (se 3 (by rfl) ⟨240737, by rfl⟩ : syracuseStep 1283933 = 481475) (by norm_num)
theorem B1283957 : Blo 854356 1283957 := bbase (se 5 (by rfl) ⟨60185, by rfl⟩ : syracuseStep 1283957 = 120371) (by norm_num)
theorem B1283981 : Blo 854356 1283981 := bbase (se 3 (by rfl) ⟨240746, by rfl⟩ : syracuseStep 1283981 = 481493) (by norm_num)
theorem B4626325 : Blo 854356 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B1284005 : Blo 854356 1284005 := bbase (se 4 (by rfl) ⟨120375, by rfl⟩ : syracuseStep 1284005 = 240751) (by norm_num)
theorem B1447861 : Blo 854356 1447861 := bbase (se 5 (by rfl) ⟨67868, by rfl⟩ : syracuseStep 1447861 = 135737) (by norm_num)
theorem B1284029 : Blo 854356 1284029 := bbase (se 3 (by rfl) ⟨240755, by rfl⟩ : syracuseStep 1284029 = 481511) (by norm_num)
theorem B2168765 : Blo 854356 2168765 := bbase (se 3 (by rfl) ⟨406643, by rfl⟩ : syracuseStep 2168765 = 813287) (by norm_num)
theorem B1284053 : Blo 854356 1284053 := bbase (se 7 (by rfl) ⟨15047, by rfl⟩ : syracuseStep 1284053 = 30095) (by norm_num)
theorem B2889701 : Blo 854356 2889701 := bbase (se 4 (by rfl) ⟨270909, by rfl⟩ : syracuseStep 2889701 = 541819) (by norm_num)
theorem B1284077 : Blo 854356 1284077 := bbase (se 3 (by rfl) ⟨240764, by rfl⟩ : syracuseStep 1284077 = 481529) (by norm_num)
theorem B1284101 : Blo 854356 1284101 := bbase (se 4 (by rfl) ⟨120384, by rfl⟩ : syracuseStep 1284101 = 240769) (by norm_num)
theorem B1447949 : Blo 854356 1447949 := bbase (se 3 (by rfl) ⟨271490, by rfl⟩ : syracuseStep 1447949 = 542981) (by norm_num)
theorem B1284125 : Blo 854356 1284125 := bbase (se 3 (by rfl) ⟨240773, by rfl⟩ : syracuseStep 1284125 = 481547) (by norm_num)
theorem B1284149 : Blo 854356 1284149 := bbase (se 5 (by rfl) ⟨60194, by rfl⟩ : syracuseStep 1284149 = 120389) (by norm_num)
theorem B1284173 : Blo 854356 1284173 := bbase (se 3 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 1284173 = 481565) (by norm_num)
theorem B3250277 : Blo 854356 3250277 := bbase (se 4 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 3250277 = 609427) (by norm_num)
theorem B1284197 : Blo 854356 1284197 := bbase (se 4 (by rfl) ⟨120393, by rfl⟩ : syracuseStep 1284197 = 240787) (by norm_num)
theorem B1284221 : Blo 854356 1284221 := bbase (se 3 (by rfl) ⟨240791, by rfl⟩ : syracuseStep 1284221 = 481583) (by norm_num)
theorem B2168957 : Blo 854356 2168957 := bbase (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) (by norm_num)
theorem B1448077 : Blo 854356 1448077 := bbase (se 3 (by rfl) ⟨271514, by rfl⟩ : syracuseStep 1448077 = 543029) (by norm_num)
theorem B1284245 : Blo 854356 1284245 := bbase (se 6 (by rfl) ⟨30099, by rfl⟩ : syracuseStep 1284245 = 60199) (by norm_num)
theorem B1284269 : Blo 854356 1284269 := bbase (se 3 (by rfl) ⟨240800, by rfl⟩ : syracuseStep 1284269 = 481601) (by norm_num)
theorem B4331717 : Blo 854356 4331717 := bbase (se 4 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 4331717 = 812197) (by norm_num)
theorem B1284293 : Blo 854356 1284293 := bbase (se 4 (by rfl) ⟨120402, by rfl⟩ : syracuseStep 1284293 = 240805) (by norm_num)
theorem B1284317 : Blo 854356 1284317 := bbase (se 3 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 1284317 = 481619) (by norm_num)
theorem B1448165 : Blo 854356 1448165 := bbase (se 4 (by rfl) ⟨135765, by rfl⟩ : syracuseStep 1448165 = 271531) (by norm_num)
theorem B1284341 : Blo 854356 1284341 := bbase (se 5 (by rfl) ⟨60203, by rfl⟩ : syracuseStep 1284341 = 120407) (by norm_num)
theorem B1284365 : Blo 854356 1284365 := bbase (se 3 (by rfl) ⟨240818, by rfl⟩ : syracuseStep 1284365 = 481637) (by norm_num)
theorem B1284389 : Blo 854356 1284389 := bbase (se 4 (by rfl) ⟨120411, by rfl⟩ : syracuseStep 1284389 = 240823) (by norm_num)
theorem B1284413 : Blo 854356 1284413 := bbase (se 3 (by rfl) ⟨240827, by rfl⟩ : syracuseStep 1284413 = 481655) (by norm_num)
theorem B1284437 : Blo 854356 1284437 := bbase (se 10 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 1284437 = 3763) (by norm_num)
theorem B1448293 : Blo 854356 1448293 := bbase (se 4 (by rfl) ⟨135777, by rfl⟩ : syracuseStep 1448293 = 271555) (by norm_num)
theorem B1284461 : Blo 854356 1284461 := bbase (se 3 (by rfl) ⟨240836, by rfl⟩ : syracuseStep 1284461 = 481673) (by norm_num)
theorem B1284485 : Blo 854356 1284485 := bbase (se 4 (by rfl) ⟨120420, by rfl⟩ : syracuseStep 1284485 = 240841) (by norm_num)
theorem B2890133 : Blo 854356 2890133 := bbase (se 6 (by rfl) ⟨67737, by rfl⟩ : syracuseStep 2890133 = 135475) (by norm_num)
theorem B1284509 : Blo 854356 1284509 := bbase (se 3 (by rfl) ⟨240845, by rfl⟩ : syracuseStep 1284509 = 481691) (by norm_num)
theorem B1284533 : Blo 854356 1284533 := bbase (se 5 (by rfl) ⟨60212, by rfl⟩ : syracuseStep 1284533 = 120425) (by norm_num)
theorem B1448381 : Blo 854356 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B1284557 : Blo 854356 1284557 := bbase (se 3 (by rfl) ⟨240854, by rfl⟩ : syracuseStep 1284557 = 481709) (by norm_num)
theorem B2169301 : Blo 854356 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B1284581 : Blo 854356 1284581 := bbase (se 4 (by rfl) ⟨120429, by rfl⟩ : syracuseStep 1284581 = 240859) (by norm_num)
theorem B1284605 : Blo 854356 1284605 := bbase (se 3 (by rfl) ⟨240863, by rfl⟩ : syracuseStep 1284605 = 481727) (by norm_num)
theorem B1284629 : Blo 854356 1284629 := bbase (se 6 (by rfl) ⟨30108, by rfl⟩ : syracuseStep 1284629 = 60217) (by norm_num)
theorem B1284653 : Blo 854356 1284653 := bbase (se 3 (by rfl) ⟨240872, by rfl⟩ : syracuseStep 1284653 = 481745) (by norm_num)
theorem B1284677 : Blo 854356 1284677 := bbase (se 4 (by rfl) ⟨120438, by rfl⟩ : syracuseStep 1284677 = 240877) (by norm_num)
theorem B2169413 : Blo 854356 2169413 := bbase (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) (by norm_num)
theorem B1284701 : Blo 854356 1284701 := bbase (se 3 (by rfl) ⟨240881, by rfl⟩ : syracuseStep 1284701 = 481763) (by norm_num)
theorem B1284725 : Blo 854356 1284725 := bbase (se 5 (by rfl) ⟨60221, by rfl⟩ : syracuseStep 1284725 = 120443) (by norm_num)
theorem B1284749 : Blo 854356 1284749 := bbase (se 3 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 1284749 = 481781) (by norm_num)
theorem B1284773 : Blo 854356 1284773 := bbase (se 4 (by rfl) ⟨120447, by rfl⟩ : syracuseStep 1284773 = 240895) (by norm_num)
theorem B1284797 : Blo 854356 1284797 := bbase (se 3 (by rfl) ⟨240899, by rfl⟩ : syracuseStep 1284797 = 481799) (by norm_num)
theorem B1284821 : Blo 854356 1284821 := bbase (se 7 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 1284821 = 30113) (by norm_num)
theorem B1284845 : Blo 854356 1284845 := bbase (se 3 (by rfl) ⟨240908, by rfl⟩ : syracuseStep 1284845 = 481817) (by norm_num)
theorem B1284869 : Blo 854356 1284869 := bbase (se 4 (by rfl) ⟨120456, by rfl⟩ : syracuseStep 1284869 = 240913) (by norm_num)
theorem B2169605 : Blo 854356 2169605 := bbase (se 4 (by rfl) ⟨203400, by rfl⟩ : syracuseStep 2169605 = 406801) (by norm_num)
theorem B1284893 : Blo 854356 1284893 := bbase (se 3 (by rfl) ⟨240917, by rfl⟩ : syracuseStep 1284893 = 481835) (by norm_num)
theorem B1645357 : Blo 854356 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B1284917 : Blo 854356 1284917 := bbase (se 5 (by rfl) ⟨60230, by rfl⟩ : syracuseStep 1284917 = 120461) (by norm_num)
theorem B2890565 : Blo 854356 2890565 := bbase (se 4 (by rfl) ⟨270990, by rfl⟩ : syracuseStep 2890565 = 541981) (by norm_num)
theorem B1284941 : Blo 854356 1284941 := bbase (se 3 (by rfl) ⟨240926, by rfl⟩ : syracuseStep 1284941 = 481853) (by norm_num)
theorem B1284965 : Blo 854356 1284965 := bbase (se 4 (by rfl) ⟨120465, by rfl⟩ : syracuseStep 1284965 = 240931) (by norm_num)
theorem B1284989 : Blo 854356 1284989 := bbase (se 3 (by rfl) ⟨240935, by rfl⟩ : syracuseStep 1284989 = 481871) (by norm_num)
theorem B1285013 : Blo 854356 1285013 := bbase (se 6 (by rfl) ⟨30117, by rfl⟩ : syracuseStep 1285013 = 60235) (by norm_num)
theorem B1285037 : Blo 854356 1285037 := bbase (se 3 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 1285037 = 481889) (by norm_num)
theorem B1285061 : Blo 854356 1285061 := bbase (se 4 (by rfl) ⟨120474, by rfl⟩ : syracuseStep 1285061 = 240949) (by norm_num)
theorem B1219549 : Blo 854356 1219549 := bbase (se 3 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 1219549 = 457331) (by norm_num)
theorem B1285085 : Blo 854356 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B7314421 : Blo 854356 7314421 := bbase (se 5 (by rfl) ⟨342863, by rfl⟩ : syracuseStep 7314421 = 685727) (by norm_num)
theorem B1285109 : Blo 854356 1285109 := bbase (se 5 (by rfl) ⟨60239, by rfl⟩ : syracuseStep 1285109 = 120479) (by norm_num)
theorem B1285133 : Blo 854356 1285133 := bbase (se 3 (by rfl) ⟨240962, by rfl⟩ : syracuseStep 1285133 = 481925) (by norm_num)
theorem B1285157 : Blo 854356 1285157 := bbase (se 4 (by rfl) ⟨120483, by rfl⟩ : syracuseStep 1285157 = 240967) (by norm_num)
theorem B1285181 : Blo 854356 1285181 := bbase (se 3 (by rfl) ⟨240971, by rfl⟩ : syracuseStep 1285181 = 481943) (by norm_num)
theorem B1285205 : Blo 854356 1285205 := bbase (se 8 (by rfl) ⟨7530, by rfl⟩ : syracuseStep 1285205 = 15061) (by norm_num)
theorem B2169949 : Blo 854356 2169949 := bbase (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) (by norm_num)
theorem B1285229 : Blo 854356 1285229 := bbase (se 3 (by rfl) ⟨240980, by rfl⟩ : syracuseStep 1285229 = 481961) (by norm_num)
theorem B1285253 : Blo 854356 1285253 := bbase (se 4 (by rfl) ⟨120492, by rfl⟩ : syracuseStep 1285253 = 240985) (by norm_num)
theorem B1285277 : Blo 854356 1285277 := bbase (se 3 (by rfl) ⟨240989, by rfl⟩ : syracuseStep 1285277 = 481979) (by norm_num)
theorem B1285301 : Blo 854356 1285301 := bbase (se 5 (by rfl) ⟨60248, by rfl⟩ : syracuseStep 1285301 = 120497) (by norm_num)
theorem B1285325 : Blo 854356 1285325 := bbase (se 3 (by rfl) ⟨240998, by rfl⟩ : syracuseStep 1285325 = 481997) (by norm_num)
theorem B2170061 : Blo 854356 2170061 := bbase (se 3 (by rfl) ⟨406886, by rfl⟩ : syracuseStep 2170061 = 813773) (by norm_num)
theorem B1285349 : Blo 854356 1285349 := bbase (se 4 (by rfl) ⟨120501, by rfl⟩ : syracuseStep 1285349 = 241003) (by norm_num)
theorem B2890997 : Blo 854356 2890997 := bbase (se 5 (by rfl) ⟨135515, by rfl⟩ : syracuseStep 2890997 = 271031) (by norm_num)
theorem B1285373 : Blo 854356 1285373 := bbase (se 3 (by rfl) ⟨241007, by rfl⟩ : syracuseStep 1285373 = 482015) (by norm_num)
theorem B3251461 : Blo 854356 3251461 := bbase (se 4 (by rfl) ⟨304824, by rfl⟩ : syracuseStep 3251461 = 609649) (by norm_num)
theorem B1285397 : Blo 854356 1285397 := bbase (se 6 (by rfl) ⟨30126, by rfl⟩ : syracuseStep 1285397 = 60253) (by norm_num)
theorem B1285421 : Blo 854356 1285421 := bbase (se 3 (by rfl) ⟨241016, by rfl⟩ : syracuseStep 1285421 = 482033) (by norm_num)
theorem B1285445 : Blo 854356 1285445 := bbase (se 4 (by rfl) ⟨120510, by rfl⟩ : syracuseStep 1285445 = 241021) (by norm_num)
theorem B1285469 : Blo 854356 1285469 := bbase (se 3 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 1285469 = 482051) (by norm_num)
theorem B3087733 : Blo 854356 3087733 := bbase (se 5 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 3087733 = 289475) (by norm_num)
theorem B1285493 : Blo 854356 1285493 := bbase (se 5 (by rfl) ⟨60257, by rfl⟩ : syracuseStep 1285493 = 120515) (by norm_num)
theorem B1285517 : Blo 854356 1285517 := bbase (se 3 (by rfl) ⟨241034, by rfl⟩ : syracuseStep 1285517 = 482069) (by norm_num)
theorem B2170253 : Blo 854356 2170253 := bbase (se 3 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 2170253 = 813845) (by norm_num)
theorem B10722709 : Blo 854356 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B1285541 : Blo 854356 1285541 := bbase (se 4 (by rfl) ⟨120519, by rfl⟩ : syracuseStep 1285541 = 241039) (by norm_num)
theorem B1285565 : Blo 854356 1285565 := bbase (se 3 (by rfl) ⟨241043, by rfl⟩ : syracuseStep 1285565 = 482087) (by norm_num)
theorem B4333013 : Blo 854356 4333013 := bbase (se 7 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 4333013 = 101555) (by norm_num)
theorem B1285589 : Blo 854356 1285589 := bbase (se 7 (by rfl) ⟨15065, by rfl⟩ : syracuseStep 1285589 = 30131) (by norm_num)
theorem B1285613 : Blo 854356 1285613 := bbase (se 3 (by rfl) ⟨241052, by rfl⟩ : syracuseStep 1285613 = 482105) (by norm_num)
theorem B1285637 : Blo 854356 1285637 := bbase (se 4 (by rfl) ⟨120528, by rfl⟩ : syracuseStep 1285637 = 241057) (by norm_num)
theorem B1285661 : Blo 854356 1285661 := bbase (se 3 (by rfl) ⟨241061, by rfl⟩ : syracuseStep 1285661 = 482123) (by norm_num)
theorem B1220141 : Blo 854356 1220141 := bbase (se 3 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 1220141 = 457553) (by norm_num)
theorem B3251765 : Blo 854356 3251765 := bbase (se 5 (by rfl) ⟨152426, by rfl⟩ : syracuseStep 3251765 = 304853) (by norm_num)
theorem B1285685 : Blo 854356 1285685 := bbase (se 5 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 1285685 = 120533) (by norm_num)
theorem B1285709 : Blo 854356 1285709 := bbase (se 3 (by rfl) ⟨241070, by rfl⟩ : syracuseStep 1285709 = 482141) (by norm_num)
theorem B1285733 : Blo 854356 1285733 := bbase (se 4 (by rfl) ⟨120537, by rfl⟩ : syracuseStep 1285733 = 241075) (by norm_num)
theorem B1220221 : Blo 854356 1220221 := bbase (se 3 (by rfl) ⟨228791, by rfl⟩ : syracuseStep 1220221 = 457583) (by norm_num)
theorem B1285757 : Blo 854356 1285757 := bbase (se 3 (by rfl) ⟨241079, by rfl⟩ : syracuseStep 1285757 = 482159) (by norm_num)
theorem B1285781 : Blo 854356 1285781 := bbase (se 6 (by rfl) ⟨30135, by rfl⟩ : syracuseStep 1285781 = 60271) (by norm_num)
theorem B2891429 : Blo 854356 2891429 := bbase (se 4 (by rfl) ⟨271071, by rfl⟩ : syracuseStep 2891429 = 542143) (by norm_num)
theorem B1285805 : Blo 854356 1285805 := bbase (se 3 (by rfl) ⟨241088, by rfl⟩ : syracuseStep 1285805 = 482177) (by norm_num)
theorem B1285829 : Blo 854356 1285829 := bbase (se 4 (by rfl) ⟨120546, by rfl⟩ : syracuseStep 1285829 = 241093) (by norm_num)
theorem B1285853 : Blo 854356 1285853 := bbase (se 3 (by rfl) ⟨241097, by rfl⟩ : syracuseStep 1285853 = 482195) (by norm_num)
theorem B2170597 : Blo 854356 2170597 := bbase (se 4 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 2170597 = 406987) (by norm_num)
theorem B1220341 : Blo 854356 1220341 := bbase (se 5 (by rfl) ⟨57203, by rfl⟩ : syracuseStep 1220341 = 114407) (by norm_num)
theorem B1285877 : Blo 854356 1285877 := bbase (se 5 (by rfl) ⟨60275, by rfl⟩ : syracuseStep 1285877 = 120551) (by norm_num)
theorem B1285901 : Blo 854356 1285901 := bbase (se 3 (by rfl) ⟨241106, by rfl⟩ : syracuseStep 1285901 = 482213) (by norm_num)
theorem B1285925 : Blo 854356 1285925 := bbase (se 4 (by rfl) ⟨120555, by rfl⟩ : syracuseStep 1285925 = 241111) (by norm_num)
theorem B3088181 : Blo 854356 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B1285949 : Blo 854356 1285949 := bbase (se 3 (by rfl) ⟨241115, by rfl⟩ : syracuseStep 1285949 = 482231) (by norm_num)
theorem B1220437 : Blo 854356 1220437 := bbase (se 9 (by rfl) ⟨3575, by rfl⟩ : syracuseStep 1220437 = 7151) (by norm_num)
theorem B1285973 : Blo 854356 1285973 := bbase (se 9 (by rfl) ⟨3767, by rfl⟩ : syracuseStep 1285973 = 7535) (by norm_num)
theorem B2170709 : Blo 854356 2170709 := bbase (se 9 (by rfl) ⟨6359, by rfl⟩ : syracuseStep 2170709 = 12719) (by norm_num)
theorem B1285997 : Blo 854356 1285997 := bbase (se 3 (by rfl) ⟨241124, by rfl⟩ : syracuseStep 1285997 = 482249) (by norm_num)
theorem B1286021 : Blo 854356 1286021 := bbase (se 4 (by rfl) ⟨120564, by rfl⟩ : syracuseStep 1286021 = 241129) (by norm_num)
theorem B1286045 : Blo 854356 1286045 := bbase (se 3 (by rfl) ⟨241133, by rfl⟩ : syracuseStep 1286045 = 482267) (by norm_num)
theorem B1286069 : Blo 854356 1286069 := bbase (se 5 (by rfl) ⟨60284, by rfl⟩ : syracuseStep 1286069 = 120569) (by norm_num)
theorem B1286093 : Blo 854356 1286093 := bbase (se 3 (by rfl) ⟨241142, by rfl⟩ : syracuseStep 1286093 = 482285) (by norm_num)
theorem B1286117 : Blo 854356 1286117 := bbase (se 4 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 1286117 = 241147) (by norm_num)
theorem B1286141 : Blo 854356 1286141 := bbase (se 3 (by rfl) ⟨241151, by rfl⟩ : syracuseStep 1286141 = 482303) (by norm_num)
theorem B1286165 : Blo 854356 1286165 := bbase (se 6 (by rfl) ⟨30144, by rfl⟩ : syracuseStep 1286165 = 60289) (by norm_num)
theorem B2170901 : Blo 854356 2170901 := bbase (se 6 (by rfl) ⟨50880, by rfl⟩ : syracuseStep 2170901 = 101761) (by norm_num)
theorem B1286189 : Blo 854356 1286189 := bbase (se 3 (by rfl) ⟨241160, by rfl⟩ : syracuseStep 1286189 = 482321) (by norm_num)
theorem B1286213 : Blo 854356 1286213 := bbase (se 4 (by rfl) ⟨120582, by rfl⟩ : syracuseStep 1286213 = 241165) (by norm_num)
theorem B2891861 : Blo 854356 2891861 := bbase (se 8 (by rfl) ⟨16944, by rfl⟩ : syracuseStep 2891861 = 33889) (by norm_num)
theorem B1286237 : Blo 854356 1286237 := bbase (se 3 (by rfl) ⟨241169, by rfl⟩ : syracuseStep 1286237 = 482339) (by norm_num)
theorem B1286261 : Blo 854356 1286261 := bbase (se 5 (by rfl) ⟨60293, by rfl⟩ : syracuseStep 1286261 = 120587) (by norm_num)
theorem B1286285 : Blo 854356 1286285 := bbase (se 3 (by rfl) ⟨241178, by rfl⟩ : syracuseStep 1286285 = 482357) (by norm_num)
theorem B1286309 : Blo 854356 1286309 := bbase (se 4 (by rfl) ⟨120591, by rfl⟩ : syracuseStep 1286309 = 241183) (by norm_num)
theorem B1286333 : Blo 854356 1286333 := bbase (se 3 (by rfl) ⟨241187, by rfl⟩ : syracuseStep 1286333 = 482375) (by norm_num)
theorem B1286357 : Blo 854356 1286357 := bbase (se 7 (by rfl) ⟨15074, by rfl⟩ : syracuseStep 1286357 = 30149) (by norm_num)
theorem B1319141 : Blo 854356 1319141 := bbase (se 4 (by rfl) ⟨123669, by rfl⟩ : syracuseStep 1319141 = 247339) (by norm_num)
theorem B1286381 : Blo 854356 1286381 := bbase (se 3 (by rfl) ⟨241196, by rfl⟩ : syracuseStep 1286381 = 482393) (by norm_num)
theorem B6955253 : Blo 854356 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B1286405 : Blo 854356 1286405 := bbase (se 4 (by rfl) ⟨120600, by rfl⟩ : syracuseStep 1286405 = 241201) (by norm_num)
theorem B1286429 : Blo 854356 1286429 := bbase (se 3 (by rfl) ⟨241205, by rfl⟩ : syracuseStep 1286429 = 482411) (by norm_num)
theorem B1286453 : Blo 854356 1286453 := bbase (se 5 (by rfl) ⟨60302, by rfl⟩ : syracuseStep 1286453 = 120605) (by norm_num)
theorem B1220933 : Blo 854356 1220933 := bbase (se 4 (by rfl) ⟨114462, by rfl⟩ : syracuseStep 1220933 = 228925) (by norm_num)
theorem B1286477 : Blo 854356 1286477 := bbase (se 3 (by rfl) ⟨241214, by rfl⟩ : syracuseStep 1286477 = 482429) (by norm_num)
theorem B1286501 : Blo 854356 1286501 := bbase (se 4 (by rfl) ⟨120609, by rfl⟩ : syracuseStep 1286501 = 241219) (by norm_num)
theorem B2171245 : Blo 854356 2171245 := bbase (se 3 (by rfl) ⟨407108, by rfl⟩ : syracuseStep 2171245 = 814217) (by norm_num)
theorem B1286525 : Blo 854356 1286525 := bbase (se 3 (by rfl) ⟨241223, by rfl⟩ : syracuseStep 1286525 = 482447) (by norm_num)
theorem B1286549 : Blo 854356 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B1286573 : Blo 854356 1286573 := bbase (se 3 (by rfl) ⟨241232, by rfl⟩ : syracuseStep 1286573 = 482465) (by norm_num)
theorem B1286597 : Blo 854356 1286597 := bbase (se 4 (by rfl) ⟨120618, by rfl⟩ : syracuseStep 1286597 = 241237) (by norm_num)
theorem B2433493 : Blo 854356 2433493 := bbase (se 7 (by rfl) ⟨28517, by rfl⟩ : syracuseStep 2433493 = 57035) (by norm_num)
theorem B1286621 : Blo 854356 1286621 := bbase (se 3 (by rfl) ⟨241241, by rfl⟩ : syracuseStep 1286621 = 482483) (by norm_num)
theorem B2171357 : Blo 854356 2171357 := bbase (se 3 (by rfl) ⟨407129, by rfl⟩ : syracuseStep 2171357 = 814259) (by norm_num)
theorem B1286645 : Blo 854356 1286645 := bbase (se 5 (by rfl) ⟨60311, by rfl⟩ : syracuseStep 1286645 = 120623) (by norm_num)
theorem B2892293 : Blo 854356 2892293 := bbase (se 4 (by rfl) ⟨271152, by rfl⟩ : syracuseStep 2892293 = 542305) (by norm_num)
theorem B1286669 : Blo 854356 1286669 := bbase (se 3 (by rfl) ⟨241250, by rfl⟩ : syracuseStep 1286669 = 482501) (by norm_num)
theorem B1286693 : Blo 854356 1286693 := bbase (se 4 (by rfl) ⟨120627, by rfl⟩ : syracuseStep 1286693 = 241255) (by norm_num)
theorem B1286717 : Blo 854356 1286717 := bbase (se 3 (by rfl) ⟨241259, by rfl⟩ : syracuseStep 1286717 = 482519) (by norm_num)
theorem B926293 : Blo 854356 926293 := bbase (se 8 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 926293 = 10855) (by norm_num)
theorem B1286741 : Blo 854356 1286741 := bbase (se 8 (by rfl) ⟨7539, by rfl⟩ : syracuseStep 1286741 = 15079) (by norm_num)
theorem B5218901 : Blo 854356 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B1286765 : Blo 854356 1286765 := bbase (se 3 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 1286765 = 482537) (by norm_num)
theorem B1286789 : Blo 854356 1286789 := bbase (se 4 (by rfl) ⟨120636, by rfl⟩ : syracuseStep 1286789 = 241273) (by norm_num)
theorem B1286813 : Blo 854356 1286813 := bbase (se 3 (by rfl) ⟨241277, by rfl⟩ : syracuseStep 1286813 = 482555) (by norm_num)
theorem B2171549 : Blo 854356 2171549 := bbase (se 3 (by rfl) ⟨407165, by rfl⟩ : syracuseStep 2171549 = 814331) (by norm_num)
theorem B1286837 : Blo 854356 1286837 := bbase (se 5 (by rfl) ⟨60320, by rfl⟩ : syracuseStep 1286837 = 120641) (by norm_num)
theorem B1286861 : Blo 854356 1286861 := bbase (se 3 (by rfl) ⟨241286, by rfl⟩ : syracuseStep 1286861 = 482573) (by norm_num)
theorem B4334309 : Blo 854356 4334309 := bbase (se 4 (by rfl) ⟨406341, by rfl⟩ : syracuseStep 4334309 = 812683) (by norm_num)
theorem B1286885 : Blo 854356 1286885 := bbase (se 4 (by rfl) ⟨120645, by rfl⟩ : syracuseStep 1286885 = 241291) (by norm_num)
theorem B1286909 : Blo 854356 1286909 := bbase (se 3 (by rfl) ⟨241295, by rfl⟩ : syracuseStep 1286909 = 482591) (by norm_num)
theorem B1286933 : Blo 854356 1286933 := bbase (se 6 (by rfl) ⟨30162, by rfl⟩ : syracuseStep 1286933 = 60325) (by norm_num)
theorem B5219093 : Blo 854356 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B1286957 : Blo 854356 1286957 := bbase (se 3 (by rfl) ⟨241304, by rfl⟩ : syracuseStep 1286957 = 482609) (by norm_num)
theorem B1286981 : Blo 854356 1286981 := bbase (se 4 (by rfl) ⟨120654, by rfl⟩ : syracuseStep 1286981 = 241309) (by norm_num)
theorem B1287005 : Blo 854356 1287005 := bbase (se 3 (by rfl) ⟨241313, by rfl⟩ : syracuseStep 1287005 = 482627) (by norm_num)
theorem B1221485 : Blo 854356 1221485 := bbase (se 3 (by rfl) ⟨229028, by rfl⟩ : syracuseStep 1221485 = 458057) (by norm_num)
theorem B1287029 : Blo 854356 1287029 := bbase (se 5 (by rfl) ⟨60329, by rfl⟩ : syracuseStep 1287029 = 120659) (by norm_num)
theorem B1287053 : Blo 854356 1287053 := bbase (se 3 (by rfl) ⟨241322, by rfl⟩ : syracuseStep 1287053 = 482645) (by norm_num)
theorem B1287077 : Blo 854356 1287077 := bbase (se 4 (by rfl) ⟨120663, by rfl⟩ : syracuseStep 1287077 = 241327) (by norm_num)
theorem B7316405 : Blo 854356 7316405 := bbase (se 5 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 7316405 = 685913) (by norm_num)
theorem B2892725 : Blo 854356 2892725 := bbase (se 5 (by rfl) ⟨135596, by rfl⟩ : syracuseStep 2892725 = 271193) (by norm_num)
theorem B1287101 : Blo 854356 1287101 := bbase (se 3 (by rfl) ⟨241331, by rfl⟩ : syracuseStep 1287101 = 482663) (by norm_num)
theorem B12329941 : Blo 854356 12329941 := bbase (se 7 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 12329941 = 288983) (by norm_num)
theorem B1287125 : Blo 854356 1287125 := bbase (se 7 (by rfl) ⟨15083, by rfl⟩ : syracuseStep 1287125 = 30167) (by norm_num)
theorem B1287149 : Blo 854356 1287149 := bbase (se 3 (by rfl) ⟨241340, by rfl⟩ : syracuseStep 1287149 = 482681) (by norm_num)
theorem B2171893 : Blo 854356 2171893 := bbase (se 5 (by rfl) ⟨101807, by rfl⟩ : syracuseStep 2171893 = 203615) (by norm_num)
theorem B1287173 : Blo 854356 1287173 := bbase (se 4 (by rfl) ⟨120672, by rfl⟩ : syracuseStep 1287173 = 241345) (by norm_num)
theorem B1287197 : Blo 854356 1287197 := bbase (se 3 (by rfl) ⟨241349, by rfl⟩ : syracuseStep 1287197 = 482699) (by norm_num)
theorem B6497333 : Blo 854356 6497333 := bbase (se 5 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 6497333 = 609125) (by norm_num)
theorem B1287221 : Blo 854356 1287221 := bbase (se 5 (by rfl) ⟨60338, by rfl⟩ : syracuseStep 1287221 = 120677) (by norm_num)
theorem B1287245 : Blo 854356 1287245 := bbase (se 3 (by rfl) ⟨241358, by rfl⟩ : syracuseStep 1287245 = 482717) (by norm_num)
theorem B5022805 : Blo 854356 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B926821 : Blo 854356 926821 := bbase (se 4 (by rfl) ⟨86889, by rfl⟩ : syracuseStep 926821 = 173779) (by norm_num)
theorem B2172005 : Blo 854356 2172005 := bbase (se 4 (by rfl) ⟨203625, by rfl⟩ : syracuseStep 2172005 = 407251) (by norm_num)
theorem B1287269 : Blo 854356 1287269 := bbase (se 4 (by rfl) ⟨120681, by rfl⟩ : syracuseStep 1287269 = 241363) (by norm_num)
theorem B1156213 : Blo 854356 1156213 := bbase (se 5 (by rfl) ⟨54197, by rfl⟩ : syracuseStep 1156213 = 108395) (by norm_num)
theorem B1287293 : Blo 854356 1287293 := bbase (se 3 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 1287293 = 482735) (by norm_num)
theorem B1287317 : Blo 854356 1287317 := bbase (se 6 (by rfl) ⟨30171, by rfl⟩ : syracuseStep 1287317 = 60343) (by norm_num)
theorem B1287341 : Blo 854356 1287341 := bbase (se 3 (by rfl) ⟨241376, by rfl⟩ : syracuseStep 1287341 = 482753) (by norm_num)
theorem B1287365 : Blo 854356 1287365 := bbase (se 4 (by rfl) ⟨120690, by rfl⟩ : syracuseStep 1287365 = 241381) (by norm_num)
theorem B1287389 : Blo 854356 1287389 := bbase (se 3 (by rfl) ⟨241385, by rfl⟩ : syracuseStep 1287389 = 482771) (by norm_num)
theorem B1287413 : Blo 854356 1287413 := bbase (se 5 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 1287413 = 120695) (by norm_num)
theorem B1287437 : Blo 854356 1287437 := bbase (se 3 (by rfl) ⟨241394, by rfl⟩ : syracuseStep 1287437 = 482789) (by norm_num)
theorem B8234261 : Blo 854356 8234261 := bbase (se 6 (by rfl) ⟨192990, by rfl⟩ : syracuseStep 8234261 = 385981) (by norm_num)
theorem B4695317 : Blo 854356 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B2172197 : Blo 854356 2172197 := bbase (se 4 (by rfl) ⟨203643, by rfl⟩ : syracuseStep 2172197 = 407287) (by norm_num)
theorem B1287461 : Blo 854356 1287461 := bbase (se 4 (by rfl) ⟨120699, by rfl⟩ : syracuseStep 1287461 = 241399) (by norm_num)
theorem B1287485 : Blo 854356 1287485 := bbase (se 3 (by rfl) ⟨241403, by rfl⟩ : syracuseStep 1287485 = 482807) (by norm_num)
theorem B1287509 : Blo 854356 1287509 := bbase (se 12 (by rfl) ⟨471, by rfl⟩ : syracuseStep 1287509 = 943) (by norm_num)
theorem B2893157 : Blo 854356 2893157 := bbase (se 4 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 2893157 = 542467) (by norm_num)
theorem B1287533 : Blo 854356 1287533 := bbase (se 3 (by rfl) ⟨241412, by rfl⟩ : syracuseStep 1287533 = 482825) (by norm_num)
theorem B4105637 : Blo 854356 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B3712549 : Blo 854356 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B3253877 : Blo 854356 3253877 := bbase (se 5 (by rfl) ⟨152525, by rfl⟩ : syracuseStep 3253877 = 305051) (by norm_num)
theorem B2172541 : Blo 854356 2172541 := bbase (se 3 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 2172541 = 814703) (by norm_num)
theorem B2172653 : Blo 854356 2172653 := bbase (se 3 (by rfl) ⟨407372, by rfl⟩ : syracuseStep 2172653 = 814745) (by norm_num)
theorem B2893589 : Blo 854356 2893589 := bbase (se 6 (by rfl) ⟨67818, by rfl⟩ : syracuseStep 2893589 = 135637) (by norm_num)
theorem B3254165 : Blo 854356 3254165 := bbase (se 6 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 3254165 = 152539) (by norm_num)
theorem B2434997 : Blo 854356 2434997 := bbase (se 5 (by rfl) ⟨114140, by rfl⟩ : syracuseStep 2434997 = 228281) (by norm_num)
theorem B4335605 : Blo 854356 4335605 := bbase (se 5 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 4335605 = 406463) (by norm_num)
theorem B2894021 : Blo 854356 2894021 := bbase (se 4 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 2894021 = 542629) (by norm_num)
theorem B1157333 : Blo 854356 1157333 := bbase (se 7 (by rfl) ⟨13562, by rfl⟩ : syracuseStep 1157333 = 27125) (by norm_num)
theorem B5482741 : Blo 854356 5482741 := bbase (se 5 (by rfl) ⟨257003, by rfl⟩ : syracuseStep 5482741 = 514007) (by norm_num)
theorem B3909941 : Blo 854356 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B1878565 : Blo 854356 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B10693205 : Blo 854356 10693205 := bbase (se 8 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 10693205 = 125311) (by norm_num)
theorem B2894453 : Blo 854356 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B961177 : Blo 854356 961177 := bbase (se 2 (by rfl) ⟨360441, by rfl⟩ : syracuseStep 961177 = 720883) (by norm_num)
theorem B961213 : Blo 854356 961213 := bbase (se 3 (by rfl) ⟨180227, by rfl⟩ : syracuseStep 961213 = 360455) (by norm_num)
theorem B4238021 : Blo 854356 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B961249 : Blo 854356 961249 := bbase (se 2 (by rfl) ⟨360468, by rfl⟩ : syracuseStep 961249 = 720937) (by norm_num)
theorem B4106981 : Blo 854356 4106981 := bbase (se 4 (by rfl) ⟨385029, by rfl⟩ : syracuseStep 4106981 = 770059) (by norm_num)
theorem B961285 : Blo 854356 961285 := bbase (se 4 (by rfl) ⟨90120, by rfl⟩ : syracuseStep 961285 = 180241) (by norm_num)
theorem B2501381 : Blo 854356 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B961321 : Blo 854356 961321 := bbase (se 2 (by rfl) ⟨360495, by rfl⟩ : syracuseStep 961321 = 720991) (by norm_num)
theorem B961357 : Blo 854356 961357 := bbase (se 3 (by rfl) ⟨180254, by rfl⟩ : syracuseStep 961357 = 360509) (by norm_num)
theorem B961393 : Blo 854356 961393 := bbase (se 2 (by rfl) ⟨360522, by rfl⟩ : syracuseStep 961393 = 721045) (by norm_num)
theorem B961429 : Blo 854356 961429 := bbase (se 6 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 961429 = 45067) (by norm_num)
theorem B961465 : Blo 854356 961465 := bbase (se 2 (by rfl) ⟨360549, by rfl⟩ : syracuseStep 961465 = 721099) (by norm_num)
theorem B961501 : Blo 854356 961501 := bbase (se 3 (by rfl) ⟨180281, by rfl⟩ : syracuseStep 961501 = 360563) (by norm_num)
theorem B961537 : Blo 854356 961537 := bbase (se 2 (by rfl) ⟨360576, by rfl⟩ : syracuseStep 961537 = 721153) (by norm_num)
theorem B961573 : Blo 854356 961573 := bbase (se 4 (by rfl) ⟨90147, by rfl⟩ : syracuseStep 961573 = 180295) (by norm_num)
theorem B2894885 : Blo 854356 2894885 := bbase (se 4 (by rfl) ⟨271395, by rfl⟩ : syracuseStep 2894885 = 542791) (by norm_num)
theorem B3255349 : Blo 854356 3255349 := bbase (se 5 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 3255349 = 305189) (by norm_num)
theorem B961609 : Blo 854356 961609 := bbase (se 2 (by rfl) ⟨360603, by rfl⟩ : syracuseStep 961609 = 721207) (by norm_num)
theorem B961645 : Blo 854356 961645 := bbase (se 3 (by rfl) ⟨180308, by rfl⟩ : syracuseStep 961645 = 360617) (by norm_num)
theorem B961681 : Blo 854356 961681 := bbase (se 2 (by rfl) ⟨360630, by rfl⟩ : syracuseStep 961681 = 721261) (by norm_num)
theorem B961717 : Blo 854356 961717 := bbase (se 5 (by rfl) ⟨45080, by rfl⟩ : syracuseStep 961717 = 90161) (by norm_num)
theorem B961753 : Blo 854356 961753 := bbase (se 2 (by rfl) ⟨360657, by rfl⟩ : syracuseStep 961753 = 721315) (by norm_num)
theorem B961789 : Blo 854356 961789 := bbase (se 3 (by rfl) ⟨180335, by rfl⟩ : syracuseStep 961789 = 360671) (by norm_num)
theorem B4336901 : Blo 854356 4336901 := bbase (se 4 (by rfl) ⟨406584, by rfl⟩ : syracuseStep 4336901 = 813169) (by norm_num)
theorem B961825 : Blo 854356 961825 := bbase (se 2 (by rfl) ⟨360684, by rfl⟩ : syracuseStep 961825 = 721369) (by norm_num)
theorem B961861 : Blo 854356 961861 := bbase (se 4 (by rfl) ⟨90174, by rfl⟩ : syracuseStep 961861 = 180349) (by norm_num)
theorem B1027409 : Blo 854356 1027409 := bbase (se 2 (by rfl) ⟨385278, by rfl⟩ : syracuseStep 1027409 = 770557) (by norm_num)
theorem B3255653 : Blo 854356 3255653 := bbase (se 4 (by rfl) ⟨305217, by rfl⟩ : syracuseStep 3255653 = 610435) (by norm_num)
theorem B961897 : Blo 854356 961897 := bbase (se 2 (by rfl) ⟨360711, by rfl⟩ : syracuseStep 961897 = 721423) (by norm_num)
theorem B961933 : Blo 854356 961933 := bbase (se 3 (by rfl) ⟨180362, by rfl⟩ : syracuseStep 961933 = 360725) (by norm_num)
theorem B961969 : Blo 854356 961969 := bbase (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) (by norm_num)
theorem B962005 : Blo 854356 962005 := bbase (se 7 (by rfl) ⟨11273, by rfl⟩ : syracuseStep 962005 = 22547) (by norm_num)
theorem B2895317 : Blo 854356 2895317 := bbase (se 7 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 2895317 = 67859) (by norm_num)
theorem B2436581 : Blo 854356 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B962041 : Blo 854356 962041 := bbase (se 2 (by rfl) ⟨360765, by rfl⟩ : syracuseStep 962041 = 721531) (by norm_num)
theorem B962077 : Blo 854356 962077 := bbase (se 3 (by rfl) ⟨180389, by rfl⟩ : syracuseStep 962077 = 360779) (by norm_num)
theorem B962113 : Blo 854356 962113 := bbase (se 2 (by rfl) ⟨360792, by rfl⟩ : syracuseStep 962113 = 721585) (by norm_num)
theorem B962149 : Blo 854356 962149 := bbase (se 4 (by rfl) ⟨90201, by rfl⟩ : syracuseStep 962149 = 180403) (by norm_num)
theorem B962185 : Blo 854356 962185 := bbase (se 2 (by rfl) ⟨360819, by rfl⟩ : syracuseStep 962185 = 721639) (by norm_num)
theorem B962221 : Blo 854356 962221 := bbase (se 3 (by rfl) ⟨180416, by rfl⟩ : syracuseStep 962221 = 360833) (by norm_num)
theorem B1027765 : Blo 854356 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B962257 : Blo 854356 962257 := bbase (se 2 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 962257 = 721693) (by norm_num)
theorem B962293 : Blo 854356 962293 := bbase (se 5 (by rfl) ⟨45107, by rfl⟩ : syracuseStep 962293 = 90215) (by norm_num)
theorem B962329 : Blo 854356 962329 := bbase (se 2 (by rfl) ⟨360873, by rfl⟩ : syracuseStep 962329 = 721747) (by norm_num)
theorem B962365 : Blo 854356 962365 := bbase (se 3 (by rfl) ⟨180443, by rfl⟩ : syracuseStep 962365 = 360887) (by norm_num)
theorem B962401 : Blo 854356 962401 := bbase (se 2 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 962401 = 721801) (by norm_num)
theorem B1027957 : Blo 854356 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B962437 : Blo 854356 962437 := bbase (se 4 (by rfl) ⟨90228, by rfl⟩ : syracuseStep 962437 = 180457) (by norm_num)
theorem B2895749 : Blo 854356 2895749 := bbase (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) (by norm_num)
theorem B962473 : Blo 854356 962473 := bbase (se 2 (by rfl) ⟨360927, by rfl⟩ : syracuseStep 962473 = 721855) (by norm_num)
theorem B962509 : Blo 854356 962509 := bbase (se 3 (by rfl) ⟨180470, by rfl⟩ : syracuseStep 962509 = 360941) (by norm_num)
theorem B962545 : Blo 854356 962545 := bbase (se 2 (by rfl) ⟨360954, by rfl⟩ : syracuseStep 962545 = 721909) (by norm_num)
theorem B1028101 : Blo 854356 1028101 := bbase (se 4 (by rfl) ⟨96384, by rfl⟩ : syracuseStep 1028101 = 192769) (by norm_num)
theorem B962581 : Blo 854356 962581 := bbase (se 6 (by rfl) ⟨22560, by rfl⟩ : syracuseStep 962581 = 45121) (by norm_num)
theorem B962617 : Blo 854356 962617 := bbase (se 2 (by rfl) ⟨360981, by rfl⟩ : syracuseStep 962617 = 721963) (by norm_num)
theorem B962653 : Blo 854356 962653 := bbase (se 3 (by rfl) ⟨180497, by rfl⟩ : syracuseStep 962653 = 360995) (by norm_num)
theorem B962689 : Blo 854356 962689 := bbase (se 2 (by rfl) ⟨361008, by rfl⟩ : syracuseStep 962689 = 722017) (by norm_num)
theorem B2437253 : Blo 854356 2437253 := bbase (se 4 (by rfl) ⟨228492, by rfl⟩ : syracuseStep 2437253 = 456985) (by norm_num)
theorem B962725 : Blo 854356 962725 := bbase (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) (by norm_num)
theorem B962761 : Blo 854356 962761 := bbase (se 2 (by rfl) ⟨361035, by rfl⟩ : syracuseStep 962761 = 722071) (by norm_num)
theorem B962797 : Blo 854356 962797 := bbase (se 3 (by rfl) ⟨180524, by rfl⟩ : syracuseStep 962797 = 361049) (by norm_num)
theorem B962833 : Blo 854356 962833 := bbase (se 2 (by rfl) ⟨361062, by rfl⟩ : syracuseStep 962833 = 722125) (by norm_num)
theorem B962869 : Blo 854356 962869 := bbase (se 5 (by rfl) ⟨45134, by rfl⟩ : syracuseStep 962869 = 90269) (by norm_num)
theorem B2896181 : Blo 854356 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B962905 : Blo 854356 962905 := bbase (se 2 (by rfl) ⟨361089, by rfl⟩ : syracuseStep 962905 = 722179) (by norm_num)
theorem B962941 : Blo 854356 962941 := bbase (se 3 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 962941 = 361103) (by norm_num)
theorem B962977 : Blo 854356 962977 := bbase (se 2 (by rfl) ⟨361116, by rfl⟩ : syracuseStep 962977 = 722233) (by norm_num)
theorem B963013 : Blo 854356 963013 := bbase (se 4 (by rfl) ⟨90282, by rfl⟩ : syracuseStep 963013 = 180565) (by norm_num)
theorem B963049 : Blo 854356 963049 := bbase (se 2 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 963049 = 722287) (by norm_num)
theorem B963085 : Blo 854356 963085 := bbase (se 3 (by rfl) ⟨180578, by rfl⟩ : syracuseStep 963085 = 361157) (by norm_num)
theorem B4338197 : Blo 854356 4338197 := bbase (se 6 (by rfl) ⟨101676, by rfl⟩ : syracuseStep 4338197 = 203353) (by norm_num)
theorem B963121 : Blo 854356 963121 := bbase (se 2 (by rfl) ⟨361170, by rfl⟩ : syracuseStep 963121 = 722341) (by norm_num)
theorem B2437685 : Blo 854356 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B963157 : Blo 854356 963157 := bbase (se 8 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 963157 = 11287) (by norm_num)
theorem B963193 : Blo 854356 963193 := bbase (se 2 (by rfl) ⟨361197, by rfl⟩ : syracuseStep 963193 = 722395) (by norm_num)
theorem B963229 : Blo 854356 963229 := bbase (se 3 (by rfl) ⟨180605, by rfl⟩ : syracuseStep 963229 = 361211) (by norm_num)
theorem B4108981 : Blo 854356 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B963265 : Blo 854356 963265 := bbase (se 2 (by rfl) ⟨361224, by rfl⟩ : syracuseStep 963265 = 722449) (by norm_num)
theorem B963301 : Blo 854356 963301 := bbase (se 4 (by rfl) ⟨90309, by rfl⟩ : syracuseStep 963301 = 180619) (by norm_num)
theorem B2896613 : Blo 854356 2896613 := bbase (se 4 (by rfl) ⟨271557, by rfl⟩ : syracuseStep 2896613 = 543115) (by norm_num)
theorem B3912437 : Blo 854356 3912437 := bbase (se 5 (by rfl) ⟨183395, by rfl⟩ : syracuseStep 3912437 = 366791) (by norm_num)
theorem B1159933 : Blo 854356 1159933 := bbase (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) (by norm_num)
theorem B3650309 : Blo 854356 3650309 := bbase (se 4 (by rfl) ⟨342216, by rfl⟩ : syracuseStep 3650309 = 684433) (by norm_num)
theorem B963337 : Blo 854356 963337 := bbase (se 2 (by rfl) ⟨361251, by rfl⟩ : syracuseStep 963337 = 722503) (by norm_num)
theorem B963373 : Blo 854356 963373 := bbase (se 3 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 963373 = 361265) (by norm_num)
theorem B963409 : Blo 854356 963409 := bbase (se 2 (by rfl) ⟨361278, by rfl⟩ : syracuseStep 963409 = 722557) (by norm_num)
theorem B963445 : Blo 854356 963445 := bbase (se 5 (by rfl) ⟨45161, by rfl⟩ : syracuseStep 963445 = 90323) (by norm_num)
theorem B963481 : Blo 854356 963481 := bbase (se 2 (by rfl) ⟨361305, by rfl⟩ : syracuseStep 963481 = 722611) (by norm_num)
theorem B6173621 : Blo 854356 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B963517 : Blo 854356 963517 := bbase (se 3 (by rfl) ⟨180659, by rfl⟩ : syracuseStep 963517 = 361319) (by norm_num)
theorem B963553 : Blo 854356 963553 := bbase (se 2 (by rfl) ⟨361332, by rfl⟩ : syracuseStep 963553 = 722665) (by norm_num)
theorem B963589 : Blo 854356 963589 := bbase (se 4 (by rfl) ⟨90336, by rfl⟩ : syracuseStep 963589 = 180673) (by norm_num)
theorem B5485589 : Blo 854356 5485589 := bbase (se 6 (by rfl) ⟨128568, by rfl⟩ : syracuseStep 5485589 = 257137) (by norm_num)
theorem B3716117 : Blo 854356 3716117 := bbase (se 6 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 3716117 = 174193) (by norm_num)
theorem B963625 : Blo 854356 963625 := bbase (se 2 (by rfl) ⟨361359, by rfl⟩ : syracuseStep 963625 = 722719) (by norm_num)
theorem B3093557 : Blo 854356 3093557 := bbase (se 5 (by rfl) ⟨145010, by rfl⟩ : syracuseStep 3093557 = 290021) (by norm_num)
theorem B963661 : Blo 854356 963661 := bbase (se 3 (by rfl) ⟨180686, by rfl⟩ : syracuseStep 963661 = 361373) (by norm_num)
theorem B963697 : Blo 854356 963697 := bbase (se 2 (by rfl) ⟨361386, by rfl⟩ : syracuseStep 963697 = 722773) (by norm_num)
theorem B963733 : Blo 854356 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B963769 : Blo 854356 963769 := bbase (se 2 (by rfl) ⟨361413, by rfl⟩ : syracuseStep 963769 = 722827) (by norm_num)
theorem B963805 : Blo 854356 963805 := bbase (se 3 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 963805 = 361427) (by norm_num)
theorem B963841 : Blo 854356 963841 := bbase (se 2 (by rfl) ⟨361440, by rfl⟩ : syracuseStep 963841 = 722881) (by norm_num)
theorem B2438437 : Blo 854356 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B963877 : Blo 854356 963877 := bbase (se 4 (by rfl) ⟨90363, by rfl⟩ : syracuseStep 963877 = 180727) (by norm_num)
theorem B963913 : Blo 854356 963913 := bbase (se 2 (by rfl) ⟨361467, by rfl⟩ : syracuseStep 963913 = 722935) (by norm_num)
theorem B963949 : Blo 854356 963949 := bbase (se 3 (by rfl) ⟨180740, by rfl⟩ : syracuseStep 963949 = 361481) (by norm_num)
theorem B963985 : Blo 854356 963985 := bbase (se 2 (by rfl) ⟨361494, by rfl⟩ : syracuseStep 963985 = 722989) (by norm_num)
theorem B2602405 : Blo 854356 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B3257765 : Blo 854356 3257765 := bbase (se 4 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 3257765 = 610831) (by norm_num)
theorem B964021 : Blo 854356 964021 := bbase (se 5 (by rfl) ⟨45188, by rfl⟩ : syracuseStep 964021 = 90377) (by norm_num)
theorem B964057 : Blo 854356 964057 := bbase (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) (by norm_num)
theorem B964093 : Blo 854356 964093 := bbase (se 3 (by rfl) ⟨180767, by rfl⟩ : syracuseStep 964093 = 361535) (by norm_num)
theorem B1029629 : Blo 854356 1029629 := bbase (se 3 (by rfl) ⟨193055, by rfl⟩ : syracuseStep 1029629 = 386111) (by norm_num)
theorem B964129 : Blo 854356 964129 := bbase (se 2 (by rfl) ⟨361548, by rfl⟩ : syracuseStep 964129 = 723097) (by norm_num)
theorem B964165 : Blo 854356 964165 := bbase (se 4 (by rfl) ⟨90390, by rfl⟩ : syracuseStep 964165 = 180781) (by norm_num)
theorem B964201 : Blo 854356 964201 := bbase (se 2 (by rfl) ⟨361575, by rfl⟩ : syracuseStep 964201 = 723151) (by norm_num)
theorem B964237 : Blo 854356 964237 := bbase (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) (by norm_num)
theorem B964273 : Blo 854356 964273 := bbase (se 2 (by rfl) ⟨361602, by rfl⟩ : syracuseStep 964273 = 723205) (by norm_num)
theorem B3258053 : Blo 854356 3258053 := bbase (se 4 (by rfl) ⟨305442, by rfl⟩ : syracuseStep 3258053 = 610885) (by norm_num)
theorem B964309 : Blo 854356 964309 := bbase (se 7 (by rfl) ⟨11300, by rfl⟩ : syracuseStep 964309 = 22601) (by norm_num)
theorem B964345 : Blo 854356 964345 := bbase (se 2 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 964345 = 723259) (by norm_num)
theorem B964381 : Blo 854356 964381 := bbase (se 3 (by rfl) ⟨180821, by rfl⟩ : syracuseStep 964381 = 361643) (by norm_num)
theorem B4339493 : Blo 854356 4339493 := bbase (se 4 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 4339493 = 813655) (by norm_num)
theorem B1029937 : Blo 854356 1029937 := bbase (se 2 (by rfl) ⟨386226, by rfl⟩ : syracuseStep 1029937 = 772453) (by norm_num)
theorem B964417 : Blo 854356 964417 := bbase (se 2 (by rfl) ⟨361656, by rfl⟩ : syracuseStep 964417 = 723313) (by norm_num)
theorem B964453 : Blo 854356 964453 := bbase (se 4 (by rfl) ⟨90417, by rfl⟩ : syracuseStep 964453 = 180835) (by norm_num)
theorem B964489 : Blo 854356 964489 := bbase (se 2 (by rfl) ⟨361683, by rfl⟩ : syracuseStep 964489 = 723367) (by norm_num)
theorem B1030033 : Blo 854356 1030033 := bbase (se 2 (by rfl) ⟨386262, by rfl⟩ : syracuseStep 1030033 = 772525) (by norm_num)
theorem B964525 : Blo 854356 964525 := bbase (se 3 (by rfl) ⟨180848, by rfl⟩ : syracuseStep 964525 = 361697) (by norm_num)
theorem B964561 : Blo 854356 964561 := bbase (se 2 (by rfl) ⟨361710, by rfl⟩ : syracuseStep 964561 = 723421) (by norm_num)
theorem B964597 : Blo 854356 964597 := bbase (se 5 (by rfl) ⟨45215, by rfl⟩ : syracuseStep 964597 = 90431) (by norm_num)
theorem B964633 : Blo 854356 964633 := bbase (se 2 (by rfl) ⟨361737, by rfl⟩ : syracuseStep 964633 = 723475) (by norm_num)
theorem B964669 : Blo 854356 964669 := bbase (se 3 (by rfl) ⟨180875, by rfl⟩ : syracuseStep 964669 = 361751) (by norm_num)
theorem B964705 : Blo 854356 964705 := bbase (se 2 (by rfl) ⟨361764, by rfl⟩ : syracuseStep 964705 = 723529) (by norm_num)
theorem B964741 : Blo 854356 964741 := bbase (se 4 (by rfl) ⟨90444, by rfl⟩ : syracuseStep 964741 = 180889) (by norm_num)
theorem B964777 : Blo 854356 964777 := bbase (se 2 (by rfl) ⟨361791, by rfl⟩ : syracuseStep 964777 = 723583) (by norm_num)
theorem B1030321 : Blo 854356 1030321 := bbase (se 2 (by rfl) ⟨386370, by rfl⟩ : syracuseStep 1030321 = 772741) (by norm_num)
theorem B1390789 : Blo 854356 1390789 := bbase (se 4 (by rfl) ⟨130386, by rfl⟩ : syracuseStep 1390789 = 260773) (by norm_num)
theorem B964813 : Blo 854356 964813 := bbase (se 3 (by rfl) ⟨180902, by rfl⟩ : syracuseStep 964813 = 361805) (by norm_num)
theorem B964849 : Blo 854356 964849 := bbase (se 2 (by rfl) ⟨361818, by rfl⟩ : syracuseStep 964849 = 723637) (by norm_num)
theorem B964885 : Blo 854356 964885 := bbase (se 6 (by rfl) ⟨22614, by rfl⟩ : syracuseStep 964885 = 45229) (by norm_num)
theorem B964921 : Blo 854356 964921 := bbase (se 2 (by rfl) ⟨361845, by rfl⟩ : syracuseStep 964921 = 723691) (by norm_num)
theorem B964957 : Blo 854356 964957 := bbase (se 3 (by rfl) ⟨180929, by rfl⟩ : syracuseStep 964957 = 361859) (by norm_num)
theorem B1030513 : Blo 854356 1030513 := bbase (se 2 (by rfl) ⟨386442, by rfl⟩ : syracuseStep 1030513 = 772885) (by norm_num)
theorem B964993 : Blo 854356 964993 := bbase (se 2 (by rfl) ⟨361872, by rfl⟩ : syracuseStep 964993 = 723745) (by norm_num)
theorem B965029 : Blo 854356 965029 := bbase (se 4 (by rfl) ⟨90471, by rfl⟩ : syracuseStep 965029 = 180943) (by norm_num)
theorem B965065 : Blo 854356 965065 := bbase (se 2 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 965065 = 723799) (by norm_num)
theorem B1096141 : Blo 854356 1096141 := bbase (se 3 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 1096141 = 411053) (by norm_num)
theorem B965101 : Blo 854356 965101 := bbase (se 3 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 965101 = 361913) (by norm_num)
theorem B1849853 : Blo 854356 1849853 := bbase (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) (by norm_num)
theorem B965137 : Blo 854356 965137 := bbase (se 2 (by rfl) ⟨361926, by rfl⟩ : syracuseStep 965137 = 723853) (by norm_num)
theorem B2603573 : Blo 854356 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B965173 : Blo 854356 965173 := bbase (se 5 (by rfl) ⟨45242, by rfl⟩ : syracuseStep 965173 = 90485) (by norm_num)
theorem B1096249 : Blo 854356 1096249 := bbase (se 2 (by rfl) ⟨411093, by rfl⟩ : syracuseStep 1096249 = 822187) (by norm_num)
theorem B965209 : Blo 854356 965209 := bbase (se 2 (by rfl) ⟨361953, by rfl⟩ : syracuseStep 965209 = 723907) (by norm_num)
theorem B965245 : Blo 854356 965245 := bbase (se 3 (by rfl) ⟨180983, by rfl⟩ : syracuseStep 965245 = 361967) (by norm_num)
theorem B965281 : Blo 854356 965281 := bbase (se 2 (by rfl) ⟨361980, by rfl⟩ : syracuseStep 965281 = 723961) (by norm_num)
theorem B965317 : Blo 854356 965317 := bbase (se 4 (by rfl) ⟨90498, by rfl⟩ : syracuseStep 965317 = 180997) (by norm_num)
theorem B965353 : Blo 854356 965353 := bbase (se 2 (by rfl) ⟨362007, by rfl⟩ : syracuseStep 965353 = 724015) (by norm_num)
theorem B965389 : Blo 854356 965389 := bbase (se 3 (by rfl) ⟨181010, by rfl⟩ : syracuseStep 965389 = 362021) (by norm_num)
theorem B965425 : Blo 854356 965425 := bbase (se 2 (by rfl) ⟨362034, by rfl⟩ : syracuseStep 965425 = 724069) (by norm_num)
theorem B965461 : Blo 854356 965461 := bbase (se 9 (by rfl) ⟨2828, by rfl⟩ : syracuseStep 965461 = 5657) (by norm_num)
theorem B965497 : Blo 854356 965497 := bbase (se 2 (by rfl) ⟨362061, by rfl⟩ : syracuseStep 965497 = 724123) (by norm_num)
theorem B965533 : Blo 854356 965533 := bbase (se 3 (by rfl) ⟨181037, by rfl⟩ : syracuseStep 965533 = 362075) (by norm_num)
theorem B1850293 : Blo 854356 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B965569 : Blo 854356 965569 := bbase (se 2 (by rfl) ⟨362088, by rfl⟩ : syracuseStep 965569 = 724177) (by norm_num)
theorem B965605 : Blo 854356 965605 := bbase (se 4 (by rfl) ⟨90525, by rfl⟩ : syracuseStep 965605 = 181051) (by norm_num)
theorem B965641 : Blo 854356 965641 := bbase (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) (by norm_num)
theorem B4340789 : Blo 854356 4340789 := bbase (se 5 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 4340789 = 406949) (by norm_num)
theorem B1097069 : Blo 854356 1097069 := bbase (se 3 (by rfl) ⟨205700, by rfl⟩ : syracuseStep 1097069 = 411401) (by norm_num)
theorem B867773 : Blo 854356 867773 := bbase (se 3 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 867773 = 325415) (by norm_num)
theorem B2309573 : Blo 854356 2309573 := bbase (se 4 (by rfl) ⟨216522, by rfl⟩ : syracuseStep 2309573 = 433045) (by norm_num)
theorem B6602485 : Blo 854356 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B1621957 : Blo 854356 1621957 := bbase (se 4 (by rfl) ⟨152058, by rfl⟩ : syracuseStep 1621957 = 304117) (by norm_num)
theorem B868357 : Blo 854356 868357 := bbase (se 4 (by rfl) ⟨81408, by rfl⟩ : syracuseStep 868357 = 162817) (by norm_num)
theorem B3293237 : Blo 854356 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B2441285 : Blo 854356 2441285 := bbase (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) (by norm_num)
theorem B1622101 : Blo 854356 1622101 := bbase (se 8 (by rfl) ⟨9504, by rfl⟩ : syracuseStep 1622101 = 19009) (by norm_num)
theorem B30097493 : Blo 854356 30097493 := bbase (se 8 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 30097493 = 352705) (by norm_num)
theorem B1622261 : Blo 854356 1622261 := bbase (se 5 (by rfl) ⟨76043, by rfl⟩ : syracuseStep 1622261 = 152087) (by norm_num)
theorem B4342085 : Blo 854356 4342085 := bbase (se 4 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 4342085 = 814141) (by norm_num)
theorem B868717 : Blo 854356 868717 := bbase (se 3 (by rfl) ⟨162884, by rfl⟩ : syracuseStep 868717 = 325769) (by norm_num)
theorem B1622405 : Blo 854356 1622405 := bbase (se 4 (by rfl) ⟨152100, by rfl⟩ : syracuseStep 1622405 = 304201) (by norm_num)
theorem B2310805 : Blo 854356 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B6505109 : Blo 854356 6505109 := bbase (se 6 (by rfl) ⟨152463, by rfl⟩ : syracuseStep 6505109 = 304927) (by norm_num)
theorem B1622693 : Blo 854356 1622693 := bbase (se 4 (by rfl) ⟨152127, by rfl⟩ : syracuseStep 1622693 = 304255) (by norm_num)
theorem B3654341 : Blo 854356 3654341 := bbase (se 4 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 3654341 = 685189) (by norm_num)
theorem B1622845 : Blo 854356 1622845 := bbase (se 3 (by rfl) ⟨304283, by rfl⟩ : syracuseStep 1622845 = 608567) (by norm_num)
theorem B4866965 : Blo 854356 4866965 := bbase (se 6 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 4866965 = 228139) (by norm_num)
theorem B1098649 : Blo 854356 1098649 := bbase (se 2 (by rfl) ⟨411993, by rfl⟩ : syracuseStep 1098649 = 823987) (by norm_num)
theorem B1623149 : Blo 854356 1623149 := bbase (se 3 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 1623149 = 608681) (by norm_num)
theorem B2442469 : Blo 854356 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B2442629 : Blo 854356 2442629 := bbase (se 4 (by rfl) ⟨228996, by rfl⟩ : syracuseStep 2442629 = 457993) (by norm_num)
theorem B869869 : Blo 854356 869869 := bbase (se 3 (by rfl) ⟨163100, by rfl⟩ : syracuseStep 869869 = 326201) (by norm_num)
theorem B4343381 : Blo 854356 4343381 := bbase (se 8 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 4343381 = 50899) (by norm_num)
theorem B2442869 : Blo 854356 2442869 := bbase (se 5 (by rfl) ⟨114509, by rfl⟩ : syracuseStep 2442869 = 229019) (by norm_num)
theorem B2443061 : Blo 854356 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B1623901 : Blo 854356 1623901 := bbase (se 3 (by rfl) ⟨304481, by rfl⟩ : syracuseStep 1623901 = 608963) (by norm_num)
theorem B2738117 : Blo 854356 2738117 := bbase (se 4 (by rfl) ⟨256698, by rfl⟩ : syracuseStep 2738117 = 513397) (by norm_num)
theorem B1624045 : Blo 854356 1624045 := bbase (se 3 (by rfl) ⟨304508, by rfl⟩ : syracuseStep 1624045 = 609017) (by norm_num)
theorem B2738245 : Blo 854356 2738245 := bbase (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) (by norm_num)
theorem B1624205 : Blo 854356 1624205 := bbase (se 3 (by rfl) ⟨304538, by rfl⟩ : syracuseStep 1624205 = 609077) (by norm_num)
theorem B4638869 : Blo 854356 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B2508965 : Blo 854356 2508965 := bbase (se 4 (by rfl) ⟨235215, by rfl⟩ : syracuseStep 2508965 = 470431) (by norm_num)
theorem B1624349 : Blo 854356 1624349 := bbase (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) (by norm_num)
theorem B2738501 : Blo 854356 2738501 := bbase (se 4 (by rfl) ⟨256734, by rfl⟩ : syracuseStep 2738501 = 513469) (by norm_num)
theorem B2935205 : Blo 854356 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B3656117 : Blo 854356 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B4114901 : Blo 854356 4114901 := bbase (se 7 (by rfl) ⟨48221, by rfl⟩ : syracuseStep 4114901 = 96443) (by norm_num)
theorem B1624637 : Blo 854356 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B1100477 : Blo 854356 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B1624789 : Blo 854356 1624789 := bbase (se 7 (by rfl) ⟨19040, by rfl⟩ : syracuseStep 1624789 = 38081) (by norm_num)
theorem B2444053 : Blo 854356 2444053 := bbase (se 6 (by rfl) ⟨57282, by rfl⟩ : syracuseStep 2444053 = 114565) (by norm_num)
theorem B4344677 : Blo 854356 4344677 := bbase (se 4 (by rfl) ⟨407313, by rfl⟩ : syracuseStep 4344677 = 814627) (by norm_num)
theorem B5721013 : Blo 854356 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B1100785 : Blo 854356 1100785 := bbase (se 2 (by rfl) ⟨412794, by rfl⟩ : syracuseStep 1100785 = 825589) (by norm_num)
theorem B1625093 : Blo 854356 1625093 := bbase (se 4 (by rfl) ⟨152352, by rfl⟩ : syracuseStep 1625093 = 304705) (by norm_num)
theorem B4869173 : Blo 854356 4869173 := bbase (se 5 (by rfl) ⟨228242, by rfl⟩ : syracuseStep 4869173 = 456485) (by norm_num)
theorem B3657109 : Blo 854356 3657109 := bbase (se 6 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 3657109 = 171427) (by norm_num)
theorem B1756669 : Blo 854356 1756669 := bbase (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) (by norm_num)
theorem B8212117 : Blo 854356 8212117 := bbase (se 6 (by rfl) ⟨192471, by rfl⟩ : syracuseStep 8212117 = 384943) (by norm_num)
theorem B1625845 : Blo 854356 1625845 := bbase (se 5 (by rfl) ⟨76211, by rfl⟩ : syracuseStep 1625845 = 152423) (by norm_num)
theorem B1625989 : Blo 854356 1625989 := bbase (se 4 (by rfl) ⟨152436, by rfl⟩ : syracuseStep 1625989 = 304873) (by norm_num)
theorem B1626149 : Blo 854356 1626149 := bbase (se 4 (by rfl) ⟨152451, by rfl⟩ : syracuseStep 1626149 = 304903) (by norm_num)
theorem B1626293 : Blo 854356 1626293 := bbase (se 5 (by rfl) ⟨76232, by rfl⟩ : syracuseStep 1626293 = 152465) (by norm_num)
theorem B938333 : Blo 854356 938333 := bbase (se 3 (by rfl) ⟨175937, by rfl⟩ : syracuseStep 938333 = 351875) (by norm_num)
theorem B1626581 : Blo 854356 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B1626733 : Blo 854356 1626733 := bbase (se 3 (by rfl) ⟨305012, by rfl⟩ : syracuseStep 1626733 = 610025) (by norm_num)
theorem B2740949 : Blo 854356 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B4444901 : Blo 854356 4444901 := bbase (se 4 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 4444901 = 833419) (by norm_num)
theorem B7328501 : Blo 854356 7328501 := bbase (se 5 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 7328501 = 687047) (by norm_num)
theorem B1299245 : Blo 854356 1299245 := bbase (se 3 (by rfl) ⟨243608, by rfl⟩ : syracuseStep 1299245 = 487217) (by norm_num)
theorem B1627037 : Blo 854356 1627037 := bbase (se 3 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 1627037 = 610139) (by norm_num)
theorem B1922309 : Blo 854356 1922309 := bbase (se 4 (by rfl) ⟨180216, by rfl⟩ : syracuseStep 1922309 = 360433) (by norm_num)
theorem B1922381 : Blo 854356 1922381 := bbase (se 3 (by rfl) ⟨360446, by rfl⟩ : syracuseStep 1922381 = 720893) (by norm_num)
theorem B2053453 : Blo 854356 2053453 := bbase (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) (by norm_num)
theorem B1922453 : Blo 854356 1922453 := bbase (se 6 (by rfl) ⟨45057, by rfl⟩ : syracuseStep 1922453 = 90115) (by norm_num)
theorem B1070509 : Blo 854356 1070509 := bbase (se 3 (by rfl) ⟨200720, by rfl⟩ : syracuseStep 1070509 = 401441) (by norm_num)
theorem B1922525 : Blo 854356 1922525 := bbase (se 3 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 1922525 = 720947) (by norm_num)
theorem B1922597 : Blo 854356 1922597 := bbase (se 4 (by rfl) ⟨180243, by rfl⟩ : syracuseStep 1922597 = 360487) (by norm_num)
theorem B4118053 : Blo 854356 4118053 := bbase (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) (by norm_num)
theorem B1922669 : Blo 854356 1922669 := bbase (se 3 (by rfl) ⟨360500, by rfl⟩ : syracuseStep 1922669 = 721001) (by norm_num)
theorem B1627789 : Blo 854356 1627789 := bbase (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) (by norm_num)
theorem B1922741 : Blo 854356 1922741 := bbase (se 5 (by rfl) ⟨90128, by rfl⟩ : syracuseStep 1922741 = 180257) (by norm_num)
theorem B1922813 : Blo 854356 1922813 := bbase (se 3 (by rfl) ⟨360527, by rfl⟩ : syracuseStep 1922813 = 721055) (by norm_num)
theorem B1627933 : Blo 854356 1627933 := bbase (se 3 (by rfl) ⟨305237, by rfl⟩ : syracuseStep 1627933 = 610475) (by norm_num)
theorem B1922885 : Blo 854356 1922885 := bbase (se 4 (by rfl) ⟨180270, by rfl⟩ : syracuseStep 1922885 = 360541) (by norm_num)
theorem B2053973 : Blo 854356 2053973 := bbase (se 9 (by rfl) ⟨6017, by rfl⟩ : syracuseStep 2053973 = 12035) (by norm_num)
theorem B1922957 : Blo 854356 1922957 := bbase (se 3 (by rfl) ⟨360554, by rfl⟩ : syracuseStep 1922957 = 721109) (by norm_num)
theorem B2054069 : Blo 854356 2054069 := bbase (se 5 (by rfl) ⟨96284, by rfl⟩ : syracuseStep 2054069 = 192569) (by norm_num)
theorem B1628093 : Blo 854356 1628093 := bbase (se 3 (by rfl) ⟨305267, by rfl⟩ : syracuseStep 1628093 = 610535) (by norm_num)
theorem B1923029 : Blo 854356 1923029 := bbase (se 7 (by rfl) ⟨22535, by rfl⟩ : syracuseStep 1923029 = 45071) (by norm_num)
theorem B2742293 : Blo 854356 2742293 := bbase (se 6 (by rfl) ⟨64272, by rfl⟩ : syracuseStep 2742293 = 128545) (by norm_num)
theorem B1923101 : Blo 854356 1923101 := bbase (se 3 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 1923101 = 721163) (by norm_num)
theorem B2316341 : Blo 854356 2316341 := bbase (se 5 (by rfl) ⟨108578, by rfl⟩ : syracuseStep 2316341 = 217157) (by norm_num)
theorem B1628237 : Blo 854356 1628237 := bbase (se 3 (by rfl) ⟨305294, by rfl⟩ : syracuseStep 1628237 = 610589) (by norm_num)
theorem B1923173 : Blo 854356 1923173 := bbase (se 4 (by rfl) ⟨180297, by rfl⟩ : syracuseStep 1923173 = 360595) (by norm_num)
theorem B1923245 : Blo 854356 1923245 := bbase (se 3 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 1923245 = 721217) (by norm_num)
theorem B1956037 : Blo 854356 1956037 := bbase (se 4 (by rfl) ⟨183378, by rfl⟩ : syracuseStep 1956037 = 366757) (by norm_num)
theorem B1923317 : Blo 854356 1923317 := bbase (se 5 (by rfl) ⟨90155, by rfl⟩ : syracuseStep 1923317 = 180311) (by norm_num)
theorem B1923389 : Blo 854356 1923389 := bbase (se 3 (by rfl) ⟨360635, by rfl⟩ : syracuseStep 1923389 = 721271) (by norm_num)
theorem B1628525 : Blo 854356 1628525 := bbase (se 3 (by rfl) ⟨305348, by rfl⟩ : syracuseStep 1628525 = 610697) (by norm_num)
theorem B1923461 : Blo 854356 1923461 := bbase (se 4 (by rfl) ⟨180324, by rfl⟩ : syracuseStep 1923461 = 360649) (by norm_num)
theorem B8214965 : Blo 854356 8214965 := bbase (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) (by norm_num)
theorem B1923533 : Blo 854356 1923533 := bbase (se 3 (by rfl) ⟨360662, by rfl⟩ : syracuseStep 1923533 = 721325) (by norm_num)
theorem B1628677 : Blo 854356 1628677 := bbase (se 4 (by rfl) ⟨152688, by rfl⟩ : syracuseStep 1628677 = 305377) (by norm_num)
theorem B1923605 : Blo 854356 1923605 := bbase (se 6 (by rfl) ⟨45084, by rfl⟩ : syracuseStep 1923605 = 90169) (by norm_num)
theorem B13163093 : Blo 854356 13163093 := bbase (se 8 (by rfl) ⟨77127, by rfl⟩ : syracuseStep 13163093 = 154255) (by norm_num)
theorem B1923677 : Blo 854356 1923677 := bbase (se 3 (by rfl) ⟨360689, by rfl⟩ : syracuseStep 1923677 = 721379) (by norm_num)
theorem B1923749 : Blo 854356 1923749 := bbase (se 4 (by rfl) ⟨180351, by rfl⟩ : syracuseStep 1923749 = 360703) (by norm_num)
theorem B1923821 : Blo 854356 1923821 := bbase (se 3 (by rfl) ⟨360716, by rfl⟩ : syracuseStep 1923821 = 721433) (by norm_num)
theorem B1465085 : Blo 854356 1465085 := bbase (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) (by norm_num)
theorem B1923893 : Blo 854356 1923893 := bbase (se 5 (by rfl) ⟨90182, by rfl⟩ : syracuseStep 1923893 = 180365) (by norm_num)
theorem B1628981 : Blo 854356 1628981 := bbase (se 5 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 1628981 = 152717) (by norm_num)
theorem B9755477 : Blo 854356 9755477 := bbase (se 9 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 9755477 = 57161) (by norm_num)
theorem B1923965 : Blo 854356 1923965 := bbase (se 3 (by rfl) ⟨360743, by rfl⟩ : syracuseStep 1923965 = 721487) (by norm_num)
theorem B1924037 : Blo 854356 1924037 := bbase (se 4 (by rfl) ⟨180378, by rfl⟩ : syracuseStep 1924037 = 360757) (by norm_num)
theorem B1924109 : Blo 854356 1924109 := bbase (se 3 (by rfl) ⟨360770, by rfl⟩ : syracuseStep 1924109 = 721541) (by norm_num)
theorem B1924181 : Blo 854356 1924181 := bbase (se 8 (by rfl) ⟨11274, by rfl⟩ : syracuseStep 1924181 = 22549) (by norm_num)
theorem B17849429 : Blo 854356 17849429 := bbase (se 8 (by rfl) ⟨104586, by rfl⟩ : syracuseStep 17849429 = 209173) (by norm_num)
theorem B1924253 : Blo 854356 1924253 := bbase (se 3 (by rfl) ⟨360797, by rfl⟩ : syracuseStep 1924253 = 721595) (by norm_num)
theorem B1924325 : Blo 854356 1924325 := bbase (se 4 (by rfl) ⟨180405, by rfl⟩ : syracuseStep 1924325 = 360811) (by norm_num)
theorem B2055413 : Blo 854356 2055413 := bbase (se 5 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 2055413 = 192695) (by norm_num)
theorem B1826077 : Blo 854356 1826077 := bbase (se 3 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 1826077 = 684779) (by norm_num)
theorem B1924397 : Blo 854356 1924397 := bbase (se 3 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 1924397 = 721649) (by norm_num)
theorem B1924469 : Blo 854356 1924469 := bbase (se 5 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 1924469 = 180419) (by norm_num)
theorem B1564085 : Blo 854356 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B1924541 : Blo 854356 1924541 := bbase (se 3 (by rfl) ⟨360851, by rfl⟩ : syracuseStep 1924541 = 721703) (by norm_num)
theorem B1924613 : Blo 854356 1924613 := bbase (se 4 (by rfl) ⟨180432, by rfl⟩ : syracuseStep 1924613 = 360865) (by norm_num)
theorem B1924685 : Blo 854356 1924685 := bbase (se 3 (by rfl) ⟨360878, by rfl⟩ : syracuseStep 1924685 = 721757) (by norm_num)
theorem B1924757 : Blo 854356 1924757 := bbase (se 6 (by rfl) ⟨45111, by rfl⟩ : syracuseStep 1924757 = 90223) (by norm_num)
theorem B1924829 : Blo 854356 1924829 := bbase (se 3 (by rfl) ⟨360905, by rfl⟩ : syracuseStep 1924829 = 721811) (by norm_num)
theorem B1924901 : Blo 854356 1924901 := bbase (se 4 (by rfl) ⟨180459, by rfl⟩ : syracuseStep 1924901 = 360919) (by norm_num)
theorem B1924973 : Blo 854356 1924973 := bbase (se 3 (by rfl) ⟨360932, by rfl⟩ : syracuseStep 1924973 = 721865) (by norm_num)
theorem B2318213 : Blo 854356 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B974749 : Blo 854356 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B3465125 : Blo 854356 3465125 := bbase (se 4 (by rfl) ⟨324855, by rfl⟩ : syracuseStep 3465125 = 649711) (by norm_num)
theorem B1925045 : Blo 854356 1925045 := bbase (se 5 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 1925045 = 180473) (by norm_num)
theorem B2744293 : Blo 854356 2744293 := bbase (se 4 (by rfl) ⟨257277, by rfl⟩ : syracuseStep 2744293 = 514555) (by norm_num)
theorem B1925117 : Blo 854356 1925117 := bbase (se 3 (by rfl) ⟨360959, by rfl⟩ : syracuseStep 1925117 = 721919) (by norm_num)
theorem B1302589 : Blo 854356 1302589 := bbase (se 3 (by rfl) ⟨244235, by rfl⟩ : syracuseStep 1302589 = 488471) (by norm_num)
theorem B1925189 : Blo 854356 1925189 := bbase (se 4 (by rfl) ⟨180486, by rfl⟩ : syracuseStep 1925189 = 360973) (by norm_num)
theorem B1925261 : Blo 854356 1925261 := bbase (se 3 (by rfl) ⟨360986, by rfl⟩ : syracuseStep 1925261 = 721973) (by norm_num)
theorem B1826965 : Blo 854356 1826965 := bbase (se 6 (by rfl) ⟨42819, by rfl⟩ : syracuseStep 1826965 = 85639) (by norm_num)
theorem B1925333 : Blo 854356 1925333 := bbase (se 7 (by rfl) ⟨22562, by rfl⟩ : syracuseStep 1925333 = 45125) (by norm_num)
theorem B21979349 : Blo 854356 21979349 := bbase (se 7 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 21979349 = 515141) (by norm_num)
theorem B4940021 : Blo 854356 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B6512885 : Blo 854356 6512885 := bbase (se 5 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 6512885 = 610583) (by norm_num)
theorem B1925405 : Blo 854356 1925405 := bbase (se 3 (by rfl) ⟨361013, by rfl⟩ : syracuseStep 1925405 = 722027) (by norm_num)
theorem B3662117 : Blo 854356 3662117 := bbase (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) (by norm_num)
theorem B4120901 : Blo 854356 4120901 := bbase (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) (by norm_num)
theorem B1925477 : Blo 854356 1925477 := bbase (se 4 (by rfl) ⟨180513, by rfl⟩ : syracuseStep 1925477 = 361027) (by norm_num)
theorem B1925549 : Blo 854356 1925549 := bbase (se 3 (by rfl) ⟨361040, by rfl⟩ : syracuseStep 1925549 = 722081) (by norm_num)
theorem B1040833 : Blo 854356 1040833 := bbase (se 2 (by rfl) ⟨390312, by rfl⟩ : syracuseStep 1040833 = 780625) (by norm_num)
theorem B1925621 : Blo 854356 1925621 := bbase (se 5 (by rfl) ⟨90263, by rfl⟩ : syracuseStep 1925621 = 180527) (by norm_num)
theorem B1925693 : Blo 854356 1925693 := bbase (se 3 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 1925693 = 722135) (by norm_num)
theorem B3662405 : Blo 854356 3662405 := bbase (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) (by norm_num)
theorem B1827461 : Blo 854356 1827461 := bbase (se 4 (by rfl) ⟨171324, by rfl⟩ : syracuseStep 1827461 = 342649) (by norm_num)
theorem B1925765 : Blo 854356 1925765 := bbase (se 4 (by rfl) ⟨180540, by rfl⟩ : syracuseStep 1925765 = 361081) (by norm_num)
theorem B1270453 : Blo 854356 1270453 := bbase (se 5 (by rfl) ⟨59552, by rfl⟩ : syracuseStep 1270453 = 119105) (by norm_num)
theorem B1925837 : Blo 854356 1925837 := bbase (se 3 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 1925837 = 722189) (by norm_num)
theorem B1925909 : Blo 854356 1925909 := bbase (se 6 (by rfl) ⟨45138, by rfl⟩ : syracuseStep 1925909 = 90277) (by norm_num)
theorem B1925981 : Blo 854356 1925981 := bbase (se 3 (by rfl) ⟨361121, by rfl⟩ : syracuseStep 1925981 = 722243) (by norm_num)
theorem B1926053 : Blo 854356 1926053 := bbase (se 4 (by rfl) ⟨180567, by rfl⟩ : syracuseStep 1926053 = 361135) (by norm_num)
theorem B1041349 : Blo 854356 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B1369045 : Blo 854356 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B1926125 : Blo 854356 1926125 := bbase (se 3 (by rfl) ⟨361148, by rfl⟩ : syracuseStep 1926125 = 722297) (by norm_num)
theorem B1926197 : Blo 854356 1926197 := bbase (se 5 (by rfl) ⟨90290, by rfl⟩ : syracuseStep 1926197 = 180581) (by norm_num)
theorem B1926269 : Blo 854356 1926269 := bbase (se 3 (by rfl) ⟨361175, by rfl⟩ : syracuseStep 1926269 = 722351) (by norm_num)
theorem B1926341 : Blo 854356 1926341 := bbase (se 4 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 1926341 = 361189) (by norm_num)
theorem B2057413 : Blo 854356 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B1926413 : Blo 854356 1926413 := bbase (se 3 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 1926413 = 722405) (by norm_num)
theorem B5203253 : Blo 854356 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B3663157 : Blo 854356 3663157 := bbase (se 5 (by rfl) ⟨171710, by rfl⟩ : syracuseStep 3663157 = 343421) (by norm_num)
theorem B1926485 : Blo 854356 1926485 := bbase (se 12 (by rfl) ⟨705, by rfl⟩ : syracuseStep 1926485 = 1411) (by norm_num)
theorem B2057557 : Blo 854356 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B976249 : Blo 854356 976249 := bbase (se 2 (by rfl) ⟨366093, by rfl⟩ : syracuseStep 976249 = 732187) (by norm_num)
theorem B1369469 : Blo 854356 1369469 := bbase (se 3 (by rfl) ⟨256775, by rfl⟩ : syracuseStep 1369469 = 513551) (by norm_num)
theorem B5203349 : Blo 854356 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B1926557 : Blo 854356 1926557 := bbase (se 3 (by rfl) ⟨361229, by rfl⟩ : syracuseStep 1926557 = 722459) (by norm_num)
theorem B1467821 : Blo 854356 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B1828325 : Blo 854356 1828325 := bbase (se 4 (by rfl) ⟨171405, by rfl⟩ : syracuseStep 1828325 = 342811) (by norm_num)
theorem B1926629 : Blo 854356 1926629 := bbase (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) (by norm_num)
theorem B1926701 : Blo 854356 1926701 := bbase (se 3 (by rfl) ⟨361256, by rfl⟩ : syracuseStep 1926701 = 722513) (by norm_num)
theorem B1828469 : Blo 854356 1828469 := bbase (se 5 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 1828469 = 171419) (by norm_num)
theorem B1926773 : Blo 854356 1926773 := bbase (se 5 (by rfl) ⟨90317, by rfl⟩ : syracuseStep 1926773 = 180635) (by norm_num)
theorem B4122245 : Blo 854356 4122245 := bbase (se 4 (by rfl) ⟨386460, by rfl⟩ : syracuseStep 4122245 = 772921) (by norm_num)
theorem B1369757 : Blo 854356 1369757 := bbase (se 3 (by rfl) ⟨256829, by rfl⟩ : syracuseStep 1369757 = 513659) (by norm_num)
theorem B1926845 : Blo 854356 1926845 := bbase (se 3 (by rfl) ⟨361283, by rfl⟩ : syracuseStep 1926845 = 722567) (by norm_num)
theorem B878297 : Blo 854356 878297 := bbase (se 2 (by rfl) ⟨329361, by rfl⟩ : syracuseStep 878297 = 658723) (by norm_num)
theorem B1042157 : Blo 854356 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B1926917 : Blo 854356 1926917 := bbase (se 4 (by rfl) ⟨180648, by rfl⟩ : syracuseStep 1926917 = 361297) (by norm_num)
theorem B1926989 : Blo 854356 1926989 := bbase (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) (by norm_num)
theorem B1369981 : Blo 854356 1369981 := bbase (se 3 (by rfl) ⟨256871, by rfl⟩ : syracuseStep 1369981 = 513743) (by norm_num)
theorem B1927061 : Blo 854356 1927061 := bbase (se 6 (by rfl) ⟨45165, by rfl⟩ : syracuseStep 1927061 = 90331) (by norm_num)
theorem B3762085 : Blo 854356 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B2058173 : Blo 854356 2058173 := bbase (se 3 (by rfl) ⟨385907, by rfl⟩ : syracuseStep 2058173 = 771815) (by norm_num)
theorem B5498837 : Blo 854356 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B1927133 : Blo 854356 1927133 := bbase (se 3 (by rfl) ⟨361337, by rfl⟩ : syracuseStep 1927133 = 722675) (by norm_num)
theorem B3663893 : Blo 854356 3663893 := bbase (se 6 (by rfl) ⟨85872, by rfl⟩ : syracuseStep 3663893 = 171745) (by norm_num)
theorem B1304597 : Blo 854356 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B1927205 : Blo 854356 1927205 := bbase (se 4 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 1927205 = 361351) (by norm_num)
theorem B1927277 : Blo 854356 1927277 := bbase (se 3 (by rfl) ⟨361364, by rfl⟩ : syracuseStep 1927277 = 722729) (by norm_num)
theorem B878729 : Blo 854356 878729 := bbase (se 2 (by rfl) ⟨329523, by rfl⟩ : syracuseStep 878729 = 659047) (by norm_num)
theorem B1927349 : Blo 854356 1927349 := bbase (se 5 (by rfl) ⟨90344, by rfl⟩ : syracuseStep 1927349 = 180689) (by norm_num)
theorem B1927421 : Blo 854356 1927421 := bbase (se 3 (by rfl) ⟨361391, by rfl⟩ : syracuseStep 1927421 = 722783) (by norm_num)
theorem B2058509 : Blo 854356 2058509 := bbase (se 3 (by rfl) ⟨385970, by rfl⟩ : syracuseStep 2058509 = 771941) (by norm_num)
theorem B1927493 : Blo 854356 1927493 := bbase (se 4 (by rfl) ⟨180702, by rfl⟩ : syracuseStep 1927493 = 361405) (by norm_num)
theorem B1829213 : Blo 854356 1829213 := bbase (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) (by norm_num)
theorem B2058605 : Blo 854356 2058605 := bbase (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) (by norm_num)
theorem B1927565 : Blo 854356 1927565 := bbase (se 3 (by rfl) ⟨361418, by rfl⟩ : syracuseStep 1927565 = 722837) (by norm_num)
theorem B1927637 : Blo 854356 1927637 := bbase (se 7 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 1927637 = 45179) (by norm_num)
theorem B6941173 : Blo 854356 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B1927709 : Blo 854356 1927709 := bbase (se 3 (by rfl) ⟨361445, by rfl⟩ : syracuseStep 1927709 = 722891) (by norm_num)
theorem B2058797 : Blo 854356 2058797 := bbase (se 3 (by rfl) ⟨386024, by rfl⟩ : syracuseStep 2058797 = 772049) (by norm_num)
theorem B3467861 : Blo 854356 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B1927781 : Blo 854356 1927781 := bbase (se 4 (by rfl) ⟨180729, by rfl⟩ : syracuseStep 1927781 = 361459) (by norm_num)
theorem B1174181 : Blo 854356 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B1927853 : Blo 854356 1927853 := bbase (se 3 (by rfl) ⟨361472, by rfl⟩ : syracuseStep 1927853 = 722945) (by norm_num)
theorem B1927925 : Blo 854356 1927925 := bbase (se 5 (by rfl) ⟨90371, by rfl⟩ : syracuseStep 1927925 = 180743) (by norm_num)
theorem B1927997 : Blo 854356 1927997 := bbase (se 3 (by rfl) ⟨361499, by rfl⟩ : syracuseStep 1927997 = 722999) (by norm_num)
theorem B1928069 : Blo 854356 1928069 := bbase (se 4 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 1928069 = 361513) (by norm_num)
theorem B2747317 : Blo 854356 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B1928141 : Blo 854356 1928141 := bbase (se 3 (by rfl) ⟨361526, by rfl⟩ : syracuseStep 1928141 = 723053) (by norm_num)
theorem B1371109 : Blo 854356 1371109 := bbase (se 4 (by rfl) ⟨128541, by rfl⟩ : syracuseStep 1371109 = 257083) (by norm_num)
theorem B912389 : Blo 854356 912389 := bbase (se 4 (by rfl) ⟨85536, by rfl⟩ : syracuseStep 912389 = 171073) (by norm_num)
theorem B1928213 : Blo 854356 1928213 := bbase (se 6 (by rfl) ⟨45192, by rfl⟩ : syracuseStep 1928213 = 90385) (by norm_num)
theorem B1829965 : Blo 854356 1829965 := bbase (se 3 (by rfl) ⟨343118, by rfl⟩ : syracuseStep 1829965 = 686237) (by norm_num)
theorem B1928285 : Blo 854356 1928285 := bbase (se 3 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 1928285 = 723107) (by norm_num)
theorem B4942997 : Blo 854356 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B1928357 : Blo 854356 1928357 := bbase (se 4 (by rfl) ⟨180783, by rfl⟩ : syracuseStep 1928357 = 361567) (by norm_num)
theorem B1830109 : Blo 854356 1830109 := bbase (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) (by norm_num)
theorem B1928429 : Blo 854356 1928429 := bbase (se 3 (by rfl) ⟨361580, by rfl⟩ : syracuseStep 1928429 = 723161) (by norm_num)
theorem B912637 : Blo 854356 912637 := bbase (se 3 (by rfl) ⟨171119, by rfl⟩ : syracuseStep 912637 = 342239) (by norm_num)
theorem B1928501 : Blo 854356 1928501 := bbase (se 5 (by rfl) ⟨90398, by rfl⟩ : syracuseStep 1928501 = 180797) (by norm_num)
theorem B1928573 : Blo 854356 1928573 := bbase (se 3 (by rfl) ⟨361607, by rfl⟩ : syracuseStep 1928573 = 723215) (by norm_num)
theorem B1371557 : Blo 854356 1371557 := bbase (se 4 (by rfl) ⟨128583, by rfl⟩ : syracuseStep 1371557 = 257167) (by norm_num)
theorem B1928645 : Blo 854356 1928645 := bbase (se 4 (by rfl) ⟨180810, by rfl⟩ : syracuseStep 1928645 = 361621) (by norm_num)
theorem B1928717 : Blo 854356 1928717 := bbase (se 3 (by rfl) ⟨361634, by rfl⟩ : syracuseStep 1928717 = 723269) (by norm_num)
theorem B1830485 : Blo 854356 1830485 := bbase (se 8 (by rfl) ⟨10725, by rfl⟩ : syracuseStep 1830485 = 21451) (by norm_num)
theorem B1928789 : Blo 854356 1928789 := bbase (se 8 (by rfl) ⟨11301, by rfl⟩ : syracuseStep 1928789 = 22603) (by norm_num)
theorem B1928861 : Blo 854356 1928861 := bbase (se 3 (by rfl) ⟨361661, by rfl⟩ : syracuseStep 1928861 = 723323) (by norm_num)
theorem B913069 : Blo 854356 913069 := bbase (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) (by norm_num)
theorem B2059949 : Blo 854356 2059949 := bbase (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) (by norm_num)
theorem B1732309 : Blo 854356 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B978653 : Blo 854356 978653 := bbase (se 3 (by rfl) ⟨183497, by rfl⟩ : syracuseStep 978653 = 366995) (by norm_num)
theorem B1928933 : Blo 854356 1928933 := bbase (se 4 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 1928933 = 361675) (by norm_num)
theorem B913141 : Blo 854356 913141 := bbase (se 5 (by rfl) ⟨42803, by rfl⟩ : syracuseStep 913141 = 85607) (by norm_num)
theorem B1929005 : Blo 854356 1929005 := bbase (se 3 (by rfl) ⟨361688, by rfl⟩ : syracuseStep 1929005 = 723377) (by norm_num)
theorem B978785 : Blo 854356 978785 := bbase (se 2 (by rfl) ⟨367044, by rfl⟩ : syracuseStep 978785 = 734089) (by norm_num)
theorem B1929077 : Blo 854356 1929077 := bbase (se 5 (by rfl) ⟨90425, by rfl⟩ : syracuseStep 1929077 = 180851) (by norm_num)
theorem B1929149 : Blo 854356 1929149 := bbase (se 3 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 1929149 = 723431) (by norm_num)
theorem B1830853 : Blo 854356 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B1929221 : Blo 854356 1929221 := bbase (se 4 (by rfl) ⟨180864, by rfl⟩ : syracuseStep 1929221 = 361729) (by norm_num)
theorem B1929293 : Blo 854356 1929293 := bbase (se 3 (by rfl) ⟨361742, by rfl⟩ : syracuseStep 1929293 = 723485) (by norm_num)
theorem B913513 : Blo 854356 913513 := bbase (se 2 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 913513 = 685135) (by norm_num)
theorem B1929365 : Blo 854356 1929365 := bbase (se 6 (by rfl) ⟨45219, by rfl⟩ : syracuseStep 1929365 = 90439) (by norm_num)
theorem B1929437 : Blo 854356 1929437 := bbase (se 3 (by rfl) ⟨361769, by rfl⟩ : syracuseStep 1929437 = 723539) (by norm_num)
theorem B1929509 : Blo 854356 1929509 := bbase (se 4 (by rfl) ⟨180891, by rfl⟩ : syracuseStep 1929509 = 361783) (by norm_num)
theorem B5566805 : Blo 854356 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B1929581 : Blo 854356 1929581 := bbase (se 3 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 1929581 = 723593) (by norm_num)
theorem B6025589 : Blo 854356 6025589 := bbase (se 5 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 6025589 = 564899) (by norm_num)
theorem B1929653 : Blo 854356 1929653 := bbase (se 5 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 1929653 = 180905) (by norm_num)
theorem B913889 : Blo 854356 913889 := bbase (se 2 (by rfl) ⟨342708, by rfl⟩ : syracuseStep 913889 = 685417) (by norm_num)
theorem B1929725 : Blo 854356 1929725 := bbase (se 3 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 1929725 = 723647) (by norm_num)
theorem B913961 : Blo 854356 913961 := bbase (se 2 (by rfl) ⟨342735, by rfl⟩ : syracuseStep 913961 = 685471) (by norm_num)
theorem B1929797 : Blo 854356 1929797 := bbase (se 4 (by rfl) ⟨180918, by rfl⟩ : syracuseStep 1929797 = 361837) (by norm_num)
theorem B1929869 : Blo 854356 1929869 := bbase (se 3 (by rfl) ⟨361850, by rfl⟩ : syracuseStep 1929869 = 723701) (by norm_num)
theorem B4879061 : Blo 854356 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B1929941 : Blo 854356 1929941 := bbase (se 7 (by rfl) ⟨22616, by rfl⟩ : syracuseStep 1929941 = 45233) (by norm_num)
theorem B914149 : Blo 854356 914149 := bbase (se 4 (by rfl) ⟨85701, by rfl⟩ : syracuseStep 914149 = 171403) (by norm_num)
theorem B1930013 : Blo 854356 1930013 := bbase (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) (by norm_num)
theorem B1930085 : Blo 854356 1930085 := bbase (se 4 (by rfl) ⟨180945, by rfl⟩ : syracuseStep 1930085 = 361891) (by norm_num)
theorem B1373069 : Blo 854356 1373069 := bbase (se 3 (by rfl) ⟨257450, by rfl⟩ : syracuseStep 1373069 = 514901) (by norm_num)
theorem B914333 : Blo 854356 914333 := bbase (se 3 (by rfl) ⟨171437, by rfl⟩ : syracuseStep 914333 = 342875) (by norm_num)
theorem B1930157 : Blo 854356 1930157 := bbase (se 3 (by rfl) ⟨361904, by rfl⟩ : syracuseStep 1930157 = 723809) (by norm_num)
theorem B1930229 : Blo 854356 1930229 := bbase (se 5 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 1930229 = 180959) (by norm_num)
theorem B1373197 : Blo 854356 1373197 := bbase (se 3 (by rfl) ⟨257474, by rfl⟩ : syracuseStep 1373197 = 514949) (by norm_num)
theorem B1930301 : Blo 854356 1930301 := bbase (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) (by norm_num)
theorem B1930373 : Blo 854356 1930373 := bbase (se 4 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 1930373 = 361945) (by norm_num)
theorem B1930445 : Blo 854356 1930445 := bbase (se 3 (by rfl) ⟨361958, by rfl⟩ : syracuseStep 1930445 = 723917) (by norm_num)
theorem B1930517 : Blo 854356 1930517 := bbase (se 6 (by rfl) ⟨45246, by rfl⟩ : syracuseStep 1930517 = 90493) (by norm_num)
theorem B1930589 : Blo 854356 1930589 := bbase (se 3 (by rfl) ⟨361985, by rfl⟩ : syracuseStep 1930589 = 723971) (by norm_num)
theorem B1832357 : Blo 854356 1832357 := bbase (se 4 (by rfl) ⟨171783, by rfl⟩ : syracuseStep 1832357 = 343567) (by norm_num)
theorem B1930661 : Blo 854356 1930661 := bbase (se 4 (by rfl) ⟨180999, by rfl⟩ : syracuseStep 1930661 = 361999) (by norm_num)
theorem B1734061 : Blo 854356 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B1668541 : Blo 854356 1668541 := bbase (se 3 (by rfl) ⟨312851, by rfl⟩ : syracuseStep 1668541 = 625703) (by norm_num)
theorem B1930733 : Blo 854356 1930733 := bbase (se 3 (by rfl) ⟨362012, by rfl⟩ : syracuseStep 1930733 = 724025) (by norm_num)
theorem B4388357 : Blo 854356 4388357 := bbase (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) (by norm_num)
theorem B1832501 : Blo 854356 1832501 := bbase (se 5 (by rfl) ⟨85898, by rfl⟩ : syracuseStep 1832501 = 171797) (by norm_num)
theorem B1930805 : Blo 854356 1930805 := bbase (se 5 (by rfl) ⟨90506, by rfl⟩ : syracuseStep 1930805 = 181013) (by norm_num)
theorem B1930877 : Blo 854356 1930877 := bbase (se 3 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 1930877 = 724079) (by norm_num)
theorem B2061949 : Blo 854356 2061949 := bbase (se 3 (by rfl) ⟨386615, by rfl⟩ : syracuseStep 2061949 = 773231) (by norm_num)
theorem B915085 : Blo 854356 915085 := bbase (se 3 (by rfl) ⟨171578, by rfl⟩ : syracuseStep 915085 = 343157) (by norm_num)
theorem B2291381 : Blo 854356 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B1930949 : Blo 854356 1930949 := bbase (se 4 (by rfl) ⟨181026, by rfl⟩ : syracuseStep 1930949 = 362053) (by norm_num)
theorem B915157 : Blo 854356 915157 := bbase (se 7 (by rfl) ⟨10724, by rfl⟩ : syracuseStep 915157 = 21449) (by norm_num)
theorem B2062045 : Blo 854356 2062045 := bbase (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) (by norm_num)
theorem B1931021 : Blo 854356 1931021 := bbase (se 3 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 1931021 = 724133) (by norm_num)
theorem B3471173 : Blo 854356 3471173 := bbase (se 4 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 3471173 = 650845) (by norm_num)
theorem B1931093 : Blo 854356 1931093 := bbase (se 9 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 1931093 = 11315) (by norm_num)
theorem B915337 : Blo 854356 915337 := bbase (se 2 (by rfl) ⟨343251, by rfl⟩ : syracuseStep 915337 = 686503) (by norm_num)
theorem B1832861 : Blo 854356 1832861 := bbase (se 3 (by rfl) ⟨343661, by rfl⟩ : syracuseStep 1832861 = 687323) (by norm_num)
theorem B1931165 : Blo 854356 1931165 := bbase (se 3 (by rfl) ⟨362093, by rfl⟩ : syracuseStep 1931165 = 724187) (by norm_num)
theorem B1931237 : Blo 854356 1931237 := bbase (se 4 (by rfl) ⟨181053, by rfl⟩ : syracuseStep 1931237 = 362107) (by norm_num)
theorem B2193685 : Blo 854356 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B915781 : Blo 854356 915781 := bbase (se 4 (by rfl) ⟨85854, by rfl⟩ : syracuseStep 915781 = 171709) (by norm_num)
theorem B1374581 : Blo 854356 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B915905 : Blo 854356 915905 := bbase (se 2 (by rfl) ⟨343464, by rfl⟩ : syracuseStep 915905 = 686929) (by norm_num)
theorem B1735157 : Blo 854356 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B7043573 : Blo 854356 7043573 := bbase (se 5 (by rfl) ⟨330167, by rfl⟩ : syracuseStep 7043573 = 660335) (by norm_num)
theorem B12352085 : Blo 854356 12352085 := bbase (se 8 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 12352085 = 144751) (by norm_num)
theorem B916157 : Blo 854356 916157 := bbase (se 3 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 916157 = 343559) (by norm_num)
theorem B2194253 : Blo 854356 2194253 := bbase (se 3 (by rfl) ⟨411422, by rfl⟩ : syracuseStep 2194253 = 822845) (by norm_num)
theorem B2227301 : Blo 854356 2227301 := bbase (se 4 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 2227301 = 417619) (by norm_num)
theorem B916601 : Blo 854356 916601 := bbase (se 2 (by rfl) ⟨343725, by rfl⟩ : syracuseStep 916601 = 687451) (by norm_num)
theorem B1736461 : Blo 854356 1736461 := bbase (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) (by norm_num)
theorem B4325237 : Blo 854356 4325237 := bbase (se 5 (by rfl) ⟨202745, by rfl⟩ : syracuseStep 4325237 = 405491) (by norm_num)
theorem B3243989 : Blo 854356 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B1441793 : Blo 854356 1441793 := bstep (se 2 (by rfl) ⟨540672, by rfl⟩ : syracuseStep 1441793 = 1081345) B1081345
theorem B9732149 : Blo 854356 9732149 := bstep (se 5 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 9732149 = 912389) B912389
theorem B1736785 : Blo 854356 1736785 := bstep (se 2 (by rfl) ⟨651294, by rfl⟩ : syracuseStep 1736785 = 1302589) B1302589
theorem B2162801 : Blo 854356 2162801 := bstep (se 2 (by rfl) ⟨811050, by rfl⟩ : syracuseStep 2162801 = 1622101) B1622101
theorem B1441921 : Blo 854356 1441921 := bstep (se 2 (by rfl) ⟨540720, by rfl⟩ : syracuseStep 1441921 = 1081441) B1081441
theorem B8781965 : Blo 854356 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B1441955 : Blo 854356 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B1081507 : Blo 854356 1081507 := bstep (se 1 (by rfl) ⟨811130, by rfl⟩ : syracuseStep 1081507 = 1622261) B1622261
theorem B2883761 : Blo 854356 2883761 := bstep (se 2 (by rfl) ⟨1081410, by rfl⟩ : syracuseStep 2883761 = 2162821) B2162821
theorem B1081603 : Blo 854356 1081603 := bstep (se 1 (by rfl) ⟨811202, by rfl⟩ : syracuseStep 1081603 = 1622405) B1622405
theorem B1442083 : Blo 854356 1442083 := bstep (se 1 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 1442083 = 2163125) B2163125
theorem B1442225 : Blo 854356 1442225 := bstep (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) B1081669
theorem B1442353 : Blo 854356 1442353 := bstep (se 2 (by rfl) ⟨540882, by rfl⟩ : syracuseStep 1442353 = 1081765) B1081765
theorem B1442387 : Blo 854356 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B3244643 : Blo 854356 3244643 := bstep (se 1 (by rfl) ⟨2433482, by rfl⟩ : syracuseStep 3244643 = 4866965) B4866965
theorem B3244657 : Blo 854356 3244657 := bstep (se 2 (by rfl) ⟨1216746, by rfl⟩ : syracuseStep 3244657 = 2433493) B2433493
theorem B2884301 : Blo 854356 2884301 := bstep (se 3 (by rfl) ⟨540806, by rfl⟩ : syracuseStep 2884301 = 1081613) B1081613
theorem B1442515 : Blo 854356 1442515 := bstep (se 1 (by rfl) ⟨1081886, by rfl⟩ : syracuseStep 1442515 = 2163773) B2163773
theorem B1082099 : Blo 854356 1082099 := bstep (se 1 (by rfl) ⟨811574, by rfl⟩ : syracuseStep 1082099 = 1623149) B1623149
theorem B2884355 : Blo 854356 2884355 := bstep (se 1 (by rfl) ⟨2163266, by rfl⟩ : syracuseStep 2884355 = 4326533) B4326533
theorem B1442657 : Blo 854356 1442657 := bstep (se 2 (by rfl) ⟨540996, by rfl⟩ : syracuseStep 1442657 = 1081993) B1081993
theorem B3081073 : Blo 854356 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B1442785 : Blo 854356 1442785 := bstep (se 2 (by rfl) ⟨541044, by rfl⟩ : syracuseStep 1442785 = 1082089) B1082089
theorem B4326371 : Blo 854356 4326371 := bstep (se 1 (by rfl) ⟨3244778, by rfl⟩ : syracuseStep 4326371 = 6489557) B6489557
theorem B1442819 : Blo 854356 1442819 := bstep (se 1 (by rfl) ⟨1082114, by rfl⟩ : syracuseStep 1442819 = 2164229) B2164229
theorem B2884625 : Blo 854356 2884625 := bstep (se 2 (by rfl) ⟨1081734, by rfl⟩ : syracuseStep 2884625 = 2163469) B2163469
theorem B16450613 : Blo 854356 16450613 := bstep (se 5 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 16450613 = 1542245) B1542245
theorem B2163793 : Blo 854356 2163793 := bstep (se 2 (by rfl) ⟨811422, by rfl⟩ : syracuseStep 2163793 = 1622845) B1622845
theorem B1442947 : Blo 854356 1442947 := bstep (se 1 (by rfl) ⟨1082210, by rfl⟩ : syracuseStep 1442947 = 2164421) B2164421
theorem B1443089 : Blo 854356 1443089 := bstep (se 2 (by rfl) ⟨541158, by rfl⟩ : syracuseStep 1443089 = 1082317) B1082317
theorem B2164067 : Blo 854356 2164067 := bstep (se 1 (by rfl) ⟨1623050, by rfl⟩ : syracuseStep 2164067 = 3246101) B3246101
theorem B1443217 : Blo 854356 1443217 := bstep (se 2 (by rfl) ⟨541206, by rfl⟩ : syracuseStep 1443217 = 1082413) B1082413
theorem B1443251 : Blo 854356 1443251 := bstep (se 1 (by rfl) ⟨1082438, by rfl⟩ : syracuseStep 1443251 = 2164877) B2164877
theorem B1082803 : Blo 854356 1082803 := bstep (se 1 (by rfl) ⟨812102, by rfl⟩ : syracuseStep 1082803 = 1624205) B1624205
theorem B1672643 : Blo 854356 1672643 := bstep (se 1 (by rfl) ⟨1254482, by rfl⟩ : syracuseStep 1672643 = 2508965) B2508965
theorem B11699653 : Blo 854356 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B1082899 : Blo 854356 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B2164259 : Blo 854356 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B2885165 : Blo 854356 2885165 := bstep (se 3 (by rfl) ⟨540968, by rfl⟩ : syracuseStep 2885165 = 1081937) B1081937
theorem B1443379 : Blo 854356 1443379 := bstep (se 1 (by rfl) ⟨1082534, by rfl⟩ : syracuseStep 1443379 = 2165069) B2165069
theorem B2885219 : Blo 854356 2885219 := bstep (se 1 (by rfl) ⟨2163914, by rfl⟩ : syracuseStep 2885219 = 4327829) B4327829
theorem B1443521 : Blo 854356 1443521 := bstep (se 2 (by rfl) ⟨541320, by rfl⟩ : syracuseStep 1443521 = 1082641) B1082641
theorem B4884209 : Blo 854356 4884209 := bstep (se 2 (by rfl) ⟨1831578, by rfl⟩ : syracuseStep 4884209 = 3663157) B3663157
theorem B4327181 : Blo 854356 4327181 := bstep (se 3 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 4327181 = 1622693) B1622693
theorem B1443649 : Blo 854356 1443649 := bstep (se 2 (by rfl) ⟨541368, by rfl⟩ : syracuseStep 1443649 = 1082737) B1082737
theorem B1443683 : Blo 854356 1443683 := bstep (se 1 (by rfl) ⟨1082762, by rfl⟩ : syracuseStep 1443683 = 2165525) B2165525
theorem B2885489 : Blo 854356 2885489 := bstep (se 2 (by rfl) ⟨1082058, by rfl⟩ : syracuseStep 2885489 = 2164117) B2164117
theorem B1443811 : Blo 854356 1443811 := bstep (se 1 (by rfl) ⟨1082858, by rfl⟩ : syracuseStep 1443811 = 2165717) B2165717
theorem B1083395 : Blo 854356 1083395 := bstep (se 1 (by rfl) ⟨812546, by rfl⟩ : syracuseStep 1083395 = 1625093) B1625093
theorem B3246115 : Blo 854356 3246115 := bstep (se 1 (by rfl) ⟨2434586, by rfl⟩ : syracuseStep 3246115 = 4869173) B4869173
theorem B4950065 : Blo 854356 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B1443953 : Blo 854356 1443953 := bstep (se 2 (by rfl) ⟨541482, by rfl⟩ : syracuseStep 1443953 = 1082965) B1082965
theorem B1444081 : Blo 854356 1444081 := bstep (se 2 (by rfl) ⟨541530, by rfl⟩ : syracuseStep 1444081 = 1083061) B1083061
theorem B1444115 : Blo 854356 1444115 := bstep (se 1 (by rfl) ⟨1083086, by rfl⟩ : syracuseStep 1444115 = 2166173) B2166173
theorem B3082531 : Blo 854356 3082531 := bstep (se 1 (by rfl) ⟨2311898, by rfl⟩ : syracuseStep 3082531 = 4623797) B4623797
theorem B854371 : Blo 854356 854371 := bstep (se 1 (by rfl) ⟨640778, by rfl⟩ : syracuseStep 854371 = 1281557) B1281557
theorem B3475811 : Blo 854356 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B854387 : Blo 854356 854387 := bstep (se 1 (by rfl) ⟨640790, by rfl⟩ : syracuseStep 854387 = 1281581) B1281581
theorem B854403 : Blo 854356 854403 := bstep (se 1 (by rfl) ⟨640802, by rfl⟩ : syracuseStep 854403 = 1281605) B1281605
theorem B2886029 : Blo 854356 2886029 := bstep (se 3 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 2886029 = 1082261) B1082261
theorem B854419 : Blo 854356 854419 := bstep (se 1 (by rfl) ⟨640814, by rfl⟩ : syracuseStep 854419 = 1281629) B1281629
theorem B1444243 : Blo 854356 1444243 := bstep (se 1 (by rfl) ⟨1083182, by rfl⟩ : syracuseStep 1444243 = 2166365) B2166365
theorem B854435 : Blo 854356 854435 := bstep (se 1 (by rfl) ⟨640826, by rfl⟩ : syracuseStep 854435 = 1281653) B1281653
theorem B854451 : Blo 854356 854451 := bstep (se 1 (by rfl) ⟨640838, by rfl⟩ : syracuseStep 854451 = 1281677) B1281677
theorem B854467 : Blo 854356 854467 := bstep (se 1 (by rfl) ⟨640850, by rfl⟩ : syracuseStep 854467 = 1281701) B1281701
theorem B2886083 : Blo 854356 2886083 := bstep (se 1 (by rfl) ⟨2164562, by rfl⟩ : syracuseStep 2886083 = 4329125) B4329125
theorem B2165201 : Blo 854356 2165201 := bstep (se 2 (by rfl) ⟨811950, by rfl⟩ : syracuseStep 2165201 = 1623901) B1623901
theorem B854483 : Blo 854356 854483 := bstep (se 1 (by rfl) ⟨640862, by rfl⟩ : syracuseStep 854483 = 1281725) B1281725
theorem B854499 : Blo 854356 854499 := bstep (se 1 (by rfl) ⟨640874, by rfl⟩ : syracuseStep 854499 = 1281749) B1281749
theorem B854515 : Blo 854356 854515 := bstep (se 1 (by rfl) ⟨640886, by rfl⟩ : syracuseStep 854515 = 1281773) B1281773
theorem B854531 : Blo 854356 854531 := bstep (se 1 (by rfl) ⟨640898, by rfl⟩ : syracuseStep 854531 = 1281797) B1281797
theorem B2165251 : Blo 854356 2165251 := bstep (se 1 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 2165251 = 3247877) B3247877
theorem B854547 : Blo 854356 854547 := bstep (se 1 (by rfl) ⟨640910, by rfl⟩ : syracuseStep 854547 = 1281821) B1281821
theorem B1444385 : Blo 854356 1444385 := bstep (se 2 (by rfl) ⟨541644, by rfl⟩ : syracuseStep 1444385 = 1083289) B1083289
theorem B854563 : Blo 854356 854563 := bstep (se 1 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 854563 = 1281845) B1281845
theorem B5016113 : Blo 854356 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B854579 : Blo 854356 854579 := bstep (se 1 (by rfl) ⟨640934, by rfl⟩ : syracuseStep 854579 = 1281869) B1281869
theorem B854595 : Blo 854356 854595 := bstep (se 1 (by rfl) ⟨640946, by rfl⟩ : syracuseStep 854595 = 1281893) B1281893
theorem B854611 : Blo 854356 854611 := bstep (se 1 (by rfl) ⟨640958, by rfl⟩ : syracuseStep 854611 = 1281917) B1281917
theorem B854627 : Blo 854356 854627 := bstep (se 1 (by rfl) ⟨640970, by rfl⟩ : syracuseStep 854627 = 1281941) B1281941
theorem B854643 : Blo 854356 854643 := bstep (se 1 (by rfl) ⟨640982, by rfl⟩ : syracuseStep 854643 = 1281965) B1281965
theorem B854659 : Blo 854356 854659 := bstep (se 1 (by rfl) ⟨640994, by rfl⟩ : syracuseStep 854659 = 1281989) B1281989
theorem B2165393 : Blo 854356 2165393 := bstep (se 2 (by rfl) ⟨812022, by rfl⟩ : syracuseStep 2165393 = 1624045) B1624045
theorem B854675 : Blo 854356 854675 := bstep (se 1 (by rfl) ⟨641006, by rfl⟩ : syracuseStep 854675 = 1282013) B1282013
theorem B1444513 : Blo 854356 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B854691 : Blo 854356 854691 := bstep (se 1 (by rfl) ⟨641018, by rfl⟩ : syracuseStep 854691 = 1282037) B1282037
theorem B854707 : Blo 854356 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B854723 : Blo 854356 854723 := bstep (se 1 (by rfl) ⟨641042, by rfl⟩ : syracuseStep 854723 = 1282085) B1282085
theorem B1444547 : Blo 854356 1444547 := bstep (se 1 (by rfl) ⟨1083410, by rfl⟩ : syracuseStep 1444547 = 2166821) B2166821
theorem B1084099 : Blo 854356 1084099 := bstep (se 1 (by rfl) ⟨813074, by rfl⟩ : syracuseStep 1084099 = 1626149) B1626149
theorem B2886353 : Blo 854356 2886353 := bstep (se 2 (by rfl) ⟨1082382, by rfl⟩ : syracuseStep 2886353 = 2164765) B2164765
theorem B854739 : Blo 854356 854739 := bstep (se 1 (by rfl) ⟨641054, by rfl⟩ : syracuseStep 854739 = 1282109) B1282109
theorem B854755 : Blo 854356 854755 := bstep (se 1 (by rfl) ⟨641066, by rfl⟩ : syracuseStep 854755 = 1282133) B1282133
theorem B854771 : Blo 854356 854771 := bstep (se 1 (by rfl) ⟨641078, by rfl⟩ : syracuseStep 854771 = 1282157) B1282157
theorem B854787 : Blo 854356 854787 := bstep (se 1 (by rfl) ⟨641090, by rfl⟩ : syracuseStep 854787 = 1282181) B1282181
theorem B854803 : Blo 854356 854803 := bstep (se 1 (by rfl) ⟨641102, by rfl⟩ : syracuseStep 854803 = 1282205) B1282205
theorem B854819 : Blo 854356 854819 := bstep (se 1 (by rfl) ⟨641114, by rfl⟩ : syracuseStep 854819 = 1282229) B1282229
theorem B1084195 : Blo 854356 1084195 := bstep (se 1 (by rfl) ⟨813146, by rfl⟩ : syracuseStep 1084195 = 1626293) B1626293
theorem B854835 : Blo 854356 854835 := bstep (se 1 (by rfl) ⟨641126, by rfl⟩ : syracuseStep 854835 = 1282253) B1282253
theorem B854851 : Blo 854356 854851 := bstep (se 1 (by rfl) ⟨641138, by rfl⟩ : syracuseStep 854851 = 1282277) B1282277
theorem B1444675 : Blo 854356 1444675 := bstep (se 1 (by rfl) ⟨1083506, by rfl⟩ : syracuseStep 1444675 = 2167013) B2167013
theorem B854867 : Blo 854356 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B854883 : Blo 854356 854883 := bstep (se 1 (by rfl) ⟨641162, by rfl⟩ : syracuseStep 854883 = 1282325) B1282325
theorem B854899 : Blo 854356 854899 := bstep (se 1 (by rfl) ⟨641174, by rfl⟩ : syracuseStep 854899 = 1282349) B1282349
theorem B854915 : Blo 854356 854915 := bstep (se 1 (by rfl) ⟨641186, by rfl⟩ : syracuseStep 854915 = 1282373) B1282373
theorem B854931 : Blo 854356 854931 := bstep (se 1 (by rfl) ⟨641198, by rfl⟩ : syracuseStep 854931 = 1282397) B1282397
theorem B854947 : Blo 854356 854947 := bstep (se 1 (by rfl) ⟨641210, by rfl⟩ : syracuseStep 854947 = 1282421) B1282421
theorem B854963 : Blo 854356 854963 := bstep (se 1 (by rfl) ⟨641222, by rfl⟩ : syracuseStep 854963 = 1282445) B1282445
theorem B854979 : Blo 854356 854979 := bstep (se 1 (by rfl) ⟨641234, by rfl⟩ : syracuseStep 854979 = 1282469) B1282469
theorem B1444817 : Blo 854356 1444817 := bstep (se 2 (by rfl) ⟨541806, by rfl⟩ : syracuseStep 1444817 = 1083613) B1083613
theorem B854995 : Blo 854356 854995 := bstep (se 1 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 854995 = 1282493) B1282493
theorem B855011 : Blo 854356 855011 := bstep (se 1 (by rfl) ⟨641258, by rfl⟩ : syracuseStep 855011 = 1282517) B1282517
theorem B7310321 : Blo 854356 7310321 := bstep (se 2 (by rfl) ⟨2741370, by rfl⟩ : syracuseStep 7310321 = 5482741) B5482741
theorem B855027 : Blo 854356 855027 := bstep (se 1 (by rfl) ⟨641270, by rfl⟩ : syracuseStep 855027 = 1282541) B1282541
theorem B855043 : Blo 854356 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B855059 : Blo 854356 855059 := bstep (se 1 (by rfl) ⟨641294, by rfl⟩ : syracuseStep 855059 = 1282589) B1282589
theorem B855075 : Blo 854356 855075 := bstep (se 1 (by rfl) ⟨641306, by rfl⟩ : syracuseStep 855075 = 1282613) B1282613
theorem B855091 : Blo 854356 855091 := bstep (se 1 (by rfl) ⟨641318, by rfl⟩ : syracuseStep 855091 = 1282637) B1282637
theorem B855107 : Blo 854356 855107 := bstep (se 1 (by rfl) ⟨641330, by rfl⟩ : syracuseStep 855107 = 1282661) B1282661
theorem B1444945 : Blo 854356 1444945 := bstep (se 2 (by rfl) ⟨541854, by rfl⟩ : syracuseStep 1444945 = 1083709) B1083709
theorem B855123 : Blo 854356 855123 := bstep (se 1 (by rfl) ⟨641342, by rfl⟩ : syracuseStep 855123 = 1282685) B1282685
theorem B855139 : Blo 854356 855139 := bstep (se 1 (by rfl) ⟨641354, by rfl⟩ : syracuseStep 855139 = 1282709) B1282709
theorem B855155 : Blo 854356 855155 := bstep (se 1 (by rfl) ⟨641366, by rfl⟩ : syracuseStep 855155 = 1282733) B1282733
theorem B1444979 : Blo 854356 1444979 := bstep (se 1 (by rfl) ⟨1083734, by rfl⟩ : syracuseStep 1444979 = 2167469) B2167469
theorem B855171 : Blo 854356 855171 := bstep (se 1 (by rfl) ⟨641378, by rfl⟩ : syracuseStep 855171 = 1282757) B1282757
theorem B855187 : Blo 854356 855187 := bstep (se 1 (by rfl) ⟨641390, by rfl⟩ : syracuseStep 855187 = 1282781) B1282781
theorem B855203 : Blo 854356 855203 := bstep (se 1 (by rfl) ⟨641402, by rfl⟩ : syracuseStep 855203 = 1282805) B1282805
theorem B4885667 : Blo 854356 4885667 := bstep (se 1 (by rfl) ⟨3664250, by rfl⟩ : syracuseStep 4885667 = 7328501) B7328501
theorem B855219 : Blo 854356 855219 := bstep (se 1 (by rfl) ⟨641414, by rfl⟩ : syracuseStep 855219 = 1282829) B1282829
theorem B855235 : Blo 854356 855235 := bstep (se 1 (by rfl) ⟨641426, by rfl⟩ : syracuseStep 855235 = 1282853) B1282853
theorem B855251 : Blo 854356 855251 := bstep (se 1 (by rfl) ⟨641438, by rfl⟩ : syracuseStep 855251 = 1282877) B1282877
theorem B855267 : Blo 854356 855267 := bstep (se 1 (by rfl) ⟨641450, by rfl⟩ : syracuseStep 855267 = 1282901) B1282901
theorem B2886893 : Blo 854356 2886893 := bstep (se 3 (by rfl) ⟨541292, by rfl⟩ : syracuseStep 2886893 = 1082585) B1082585
theorem B855283 : Blo 854356 855283 := bstep (se 1 (by rfl) ⟨641462, by rfl⟩ : syracuseStep 855283 = 1282925) B1282925
theorem B1445107 : Blo 854356 1445107 := bstep (se 1 (by rfl) ⟨1083830, by rfl⟩ : syracuseStep 1445107 = 2167661) B2167661
theorem B855299 : Blo 854356 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B855315 : Blo 854356 855315 := bstep (se 1 (by rfl) ⟨641486, by rfl⟩ : syracuseStep 855315 = 1282973) B1282973
theorem B1084691 : Blo 854356 1084691 := bstep (se 1 (by rfl) ⟨813518, by rfl⟩ : syracuseStep 1084691 = 1627037) B1627037
theorem B855331 : Blo 854356 855331 := bstep (se 1 (by rfl) ⟨641498, by rfl⟩ : syracuseStep 855331 = 1282997) B1282997
theorem B2886947 : Blo 854356 2886947 := bstep (se 1 (by rfl) ⟨2165210, by rfl⟩ : syracuseStep 2886947 = 4330421) B4330421
theorem B855347 : Blo 854356 855347 := bstep (se 1 (by rfl) ⟨641510, by rfl⟩ : syracuseStep 855347 = 1283021) B1283021
theorem B855363 : Blo 854356 855363 := bstep (se 1 (by rfl) ⟨641522, by rfl⟩ : syracuseStep 855363 = 1283045) B1283045
theorem B855379 : Blo 854356 855379 := bstep (se 1 (by rfl) ⟨641534, by rfl⟩ : syracuseStep 855379 = 1283069) B1283069
theorem B855395 : Blo 854356 855395 := bstep (se 1 (by rfl) ⟨641546, by rfl⟩ : syracuseStep 855395 = 1283093) B1283093
theorem B855411 : Blo 854356 855411 := bstep (se 1 (by rfl) ⟨641558, by rfl⟩ : syracuseStep 855411 = 1283117) B1283117
theorem B1445249 : Blo 854356 1445249 := bstep (se 2 (by rfl) ⟨541968, by rfl⟩ : syracuseStep 1445249 = 1083937) B1083937
theorem B855427 : Blo 854356 855427 := bstep (se 1 (by rfl) ⟨641570, by rfl⟩ : syracuseStep 855427 = 1283141) B1283141
theorem B855443 : Blo 854356 855443 := bstep (se 1 (by rfl) ⟨641582, by rfl⟩ : syracuseStep 855443 = 1283165) B1283165
theorem B855459 : Blo 854356 855459 := bstep (se 1 (by rfl) ⟨641594, by rfl⟩ : syracuseStep 855459 = 1283189) B1283189
theorem B855475 : Blo 854356 855475 := bstep (se 1 (by rfl) ⟨641606, by rfl⟩ : syracuseStep 855475 = 1283213) B1283213
theorem B855491 : Blo 854356 855491 := bstep (se 1 (by rfl) ⟨641618, by rfl⟩ : syracuseStep 855491 = 1283237) B1283237
theorem B855507 : Blo 854356 855507 := bstep (se 1 (by rfl) ⟨641630, by rfl⟩ : syracuseStep 855507 = 1283261) B1283261
theorem B855523 : Blo 854356 855523 := bstep (se 1 (by rfl) ⟨641642, by rfl⟩ : syracuseStep 855523 = 1283285) B1283285
theorem B855539 : Blo 854356 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B1445377 : Blo 854356 1445377 := bstep (se 2 (by rfl) ⟨542016, by rfl⟩ : syracuseStep 1445377 = 1084033) B1084033
theorem B1281539 : Blo 854356 1281539 := bstep (se 1 (by rfl) ⟨961154, by rfl⟩ : syracuseStep 1281539 = 1922309) B1922309
theorem B855555 : Blo 854356 855555 := bstep (se 1 (by rfl) ⟨641666, by rfl⟩ : syracuseStep 855555 = 1283333) B1283333
theorem B855571 : Blo 854356 855571 := bstep (se 1 (by rfl) ⟨641678, by rfl⟩ : syracuseStep 855571 = 1283357) B1283357
theorem B1281569 : Blo 854356 1281569 := bstep (se 2 (by rfl) ⟨480588, by rfl⟩ : syracuseStep 1281569 = 961177) B961177
theorem B855587 : Blo 854356 855587 := bstep (se 1 (by rfl) ⟨641690, by rfl⟩ : syracuseStep 855587 = 1283381) B1283381
theorem B1445411 : Blo 854356 1445411 := bstep (se 1 (by rfl) ⟨1084058, by rfl⟩ : syracuseStep 1445411 = 2168117) B2168117
theorem B2887217 : Blo 854356 2887217 := bstep (se 2 (by rfl) ⟨1082706, by rfl⟩ : syracuseStep 2887217 = 2165413) B2165413
theorem B1281587 : Blo 854356 1281587 := bstep (se 1 (by rfl) ⟨961190, by rfl⟩ : syracuseStep 1281587 = 1922381) B1922381
theorem B855603 : Blo 854356 855603 := bstep (se 1 (by rfl) ⟨641702, by rfl⟩ : syracuseStep 855603 = 1283405) B1283405
theorem B855619 : Blo 854356 855619 := bstep (se 1 (by rfl) ⟨641714, by rfl⟩ : syracuseStep 855619 = 1283429) B1283429
theorem B1281617 : Blo 854356 1281617 := bstep (se 2 (by rfl) ⟨480606, by rfl⟩ : syracuseStep 1281617 = 961213) B961213
theorem B855635 : Blo 854356 855635 := bstep (se 1 (by rfl) ⟨641726, by rfl⟩ : syracuseStep 855635 = 1283453) B1283453
theorem B1281635 : Blo 854356 1281635 := bstep (se 1 (by rfl) ⟨961226, by rfl⟩ : syracuseStep 1281635 = 1922453) B1922453
theorem B855651 : Blo 854356 855651 := bstep (se 1 (by rfl) ⟨641738, by rfl⟩ : syracuseStep 855651 = 1283477) B1283477
theorem B2166385 : Blo 854356 2166385 := bstep (se 2 (by rfl) ⟨812394, by rfl⟩ : syracuseStep 2166385 = 1624789) B1624789
theorem B855667 : Blo 854356 855667 := bstep (se 1 (by rfl) ⟨641750, by rfl⟩ : syracuseStep 855667 = 1283501) B1283501
theorem B1281665 : Blo 854356 1281665 := bstep (se 2 (by rfl) ⟨480624, by rfl⟩ : syracuseStep 1281665 = 961249) B961249
theorem B855683 : Blo 854356 855683 := bstep (se 1 (by rfl) ⟨641762, by rfl⟩ : syracuseStep 855683 = 1283525) B1283525
theorem B1281683 : Blo 854356 1281683 := bstep (se 1 (by rfl) ⟨961262, by rfl⟩ : syracuseStep 1281683 = 1922525) B1922525
theorem B855699 : Blo 854356 855699 := bstep (se 1 (by rfl) ⟨641774, by rfl⟩ : syracuseStep 855699 = 1283549) B1283549
theorem B855715 : Blo 854356 855715 := bstep (se 1 (by rfl) ⟨641786, by rfl⟩ : syracuseStep 855715 = 1283573) B1283573
theorem B1445539 : Blo 854356 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B1281713 : Blo 854356 1281713 := bstep (se 2 (by rfl) ⟨480642, by rfl⟩ : syracuseStep 1281713 = 961285) B961285
theorem B855731 : Blo 854356 855731 := bstep (se 1 (by rfl) ⟨641798, by rfl⟩ : syracuseStep 855731 = 1283597) B1283597
theorem B1281731 : Blo 854356 1281731 := bstep (se 1 (by rfl) ⟨961298, by rfl⟩ : syracuseStep 1281731 = 1922597) B1922597
theorem B855747 : Blo 854356 855747 := bstep (se 1 (by rfl) ⟨641810, by rfl⟩ : syracuseStep 855747 = 1283621) B1283621
theorem B855763 : Blo 854356 855763 := bstep (se 1 (by rfl) ⟨641822, by rfl⟩ : syracuseStep 855763 = 1283645) B1283645
theorem B1281761 : Blo 854356 1281761 := bstep (se 2 (by rfl) ⟨480660, by rfl⟩ : syracuseStep 1281761 = 961321) B961321
theorem B855779 : Blo 854356 855779 := bstep (se 1 (by rfl) ⟨641834, by rfl⟩ : syracuseStep 855779 = 1283669) B1283669
theorem B1281779 : Blo 854356 1281779 := bstep (se 1 (by rfl) ⟨961334, by rfl⟩ : syracuseStep 1281779 = 1922669) B1922669
theorem B855795 : Blo 854356 855795 := bstep (se 1 (by rfl) ⟨641846, by rfl⟩ : syracuseStep 855795 = 1283693) B1283693
theorem B855811 : Blo 854356 855811 := bstep (se 1 (by rfl) ⟨641858, by rfl⟩ : syracuseStep 855811 = 1283717) B1283717
theorem B1281809 : Blo 854356 1281809 := bstep (se 2 (by rfl) ⟨480678, by rfl⟩ : syracuseStep 1281809 = 961357) B961357
theorem B855827 : Blo 854356 855827 := bstep (se 1 (by rfl) ⟨641870, by rfl⟩ : syracuseStep 855827 = 1283741) B1283741
theorem B1281827 : Blo 854356 1281827 := bstep (se 1 (by rfl) ⟨961370, by rfl⟩ : syracuseStep 1281827 = 1922741) B1922741
theorem B855843 : Blo 854356 855843 := bstep (se 1 (by rfl) ⟨641882, by rfl⟩ : syracuseStep 855843 = 1283765) B1283765
theorem B1445681 : Blo 854356 1445681 := bstep (se 2 (by rfl) ⟨542130, by rfl⟩ : syracuseStep 1445681 = 1084261) B1084261
theorem B855859 : Blo 854356 855859 := bstep (se 1 (by rfl) ⟨641894, by rfl⟩ : syracuseStep 855859 = 1283789) B1283789
theorem B11702069 : Blo 854356 11702069 := bstep (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) B1097069
theorem B1281857 : Blo 854356 1281857 := bstep (se 2 (by rfl) ⟨480696, by rfl⟩ : syracuseStep 1281857 = 961393) B961393
theorem B855875 : Blo 854356 855875 := bstep (se 1 (by rfl) ⟨641906, by rfl⟩ : syracuseStep 855875 = 1283813) B1283813
theorem B1281875 : Blo 854356 1281875 := bstep (se 1 (by rfl) ⟨961406, by rfl⟩ : syracuseStep 1281875 = 1922813) B1922813
theorem B855891 : Blo 854356 855891 := bstep (se 1 (by rfl) ⟨641918, by rfl⟩ : syracuseStep 855891 = 1283837) B1283837
theorem B855907 : Blo 854356 855907 := bstep (se 1 (by rfl) ⟨641930, by rfl⟩ : syracuseStep 855907 = 1283861) B1283861
theorem B1281905 : Blo 854356 1281905 := bstep (se 2 (by rfl) ⟨480714, by rfl⟩ : syracuseStep 1281905 = 961429) B961429
theorem B855923 : Blo 854356 855923 := bstep (se 1 (by rfl) ⟨641942, by rfl⟩ : syracuseStep 855923 = 1283885) B1283885
theorem B1281923 : Blo 854356 1281923 := bstep (se 1 (by rfl) ⟨961442, by rfl⟩ : syracuseStep 1281923 = 1922885) B1922885
theorem B855939 : Blo 854356 855939 := bstep (se 1 (by rfl) ⟨641954, by rfl⟩ : syracuseStep 855939 = 1283909) B1283909
theorem B2166659 : Blo 854356 2166659 := bstep (se 1 (by rfl) ⟨1624994, by rfl⟩ : syracuseStep 2166659 = 3249989) B3249989
theorem B855955 : Blo 854356 855955 := bstep (se 1 (by rfl) ⟨641966, by rfl⟩ : syracuseStep 855955 = 1283933) B1283933
theorem B1281953 : Blo 854356 1281953 := bstep (se 2 (by rfl) ⟨480732, by rfl⟩ : syracuseStep 1281953 = 961465) B961465
theorem B855971 : Blo 854356 855971 := bstep (se 1 (by rfl) ⟨641978, by rfl⟩ : syracuseStep 855971 = 1283957) B1283957
theorem B1445809 : Blo 854356 1445809 := bstep (se 2 (by rfl) ⟨542178, by rfl⟩ : syracuseStep 1445809 = 1084357) B1084357
theorem B1281971 : Blo 854356 1281971 := bstep (se 1 (by rfl) ⟨961478, by rfl⟩ : syracuseStep 1281971 = 1922957) B1922957
theorem B855987 : Blo 854356 855987 := bstep (se 1 (by rfl) ⟨641990, by rfl⟩ : syracuseStep 855987 = 1283981) B1283981
theorem B856003 : Blo 854356 856003 := bstep (se 1 (by rfl) ⟨642002, by rfl⟩ : syracuseStep 856003 = 1284005) B1284005
theorem B1282001 : Blo 854356 1282001 := bstep (se 2 (by rfl) ⟨480750, by rfl⟩ : syracuseStep 1282001 = 961501) B961501
theorem B856019 : Blo 854356 856019 := bstep (se 1 (by rfl) ⟨642014, by rfl⟩ : syracuseStep 856019 = 1284029) B1284029
theorem B1445843 : Blo 854356 1445843 := bstep (se 1 (by rfl) ⟨1084382, by rfl⟩ : syracuseStep 1445843 = 2168765) B2168765
theorem B1085395 : Blo 854356 1085395 := bstep (se 1 (by rfl) ⟨814046, by rfl⟩ : syracuseStep 1085395 = 1628093) B1628093
theorem B1282019 : Blo 854356 1282019 := bstep (se 1 (by rfl) ⟨961514, by rfl⟩ : syracuseStep 1282019 = 1923029) B1923029
theorem B856035 : Blo 854356 856035 := bstep (se 1 (by rfl) ⟨642026, by rfl⟩ : syracuseStep 856035 = 1284053) B1284053
theorem B856051 : Blo 854356 856051 := bstep (se 1 (by rfl) ⟨642038, by rfl⟩ : syracuseStep 856051 = 1284077) B1284077
theorem B1282049 : Blo 854356 1282049 := bstep (se 2 (by rfl) ⟨480768, by rfl⟩ : syracuseStep 1282049 = 961537) B961537
theorem B856067 : Blo 854356 856067 := bstep (se 1 (by rfl) ⟨642050, by rfl⟩ : syracuseStep 856067 = 1284101) B1284101
theorem B1282067 : Blo 854356 1282067 := bstep (se 1 (by rfl) ⟨961550, by rfl⟩ : syracuseStep 1282067 = 1923101) B1923101
theorem B856083 : Blo 854356 856083 := bstep (se 1 (by rfl) ⟨642062, by rfl⟩ : syracuseStep 856083 = 1284125) B1284125
theorem B856099 : Blo 854356 856099 := bstep (se 1 (by rfl) ⟨642074, by rfl⟩ : syracuseStep 856099 = 1284149) B1284149
theorem B1544227 : Blo 854356 1544227 := bstep (se 1 (by rfl) ⟨1158170, by rfl⟩ : syracuseStep 1544227 = 2316341) B2316341
theorem B1282097 : Blo 854356 1282097 := bstep (se 2 (by rfl) ⟨480786, by rfl⟩ : syracuseStep 1282097 = 961573) B961573
theorem B856115 : Blo 854356 856115 := bstep (se 1 (by rfl) ⟨642086, by rfl⟩ : syracuseStep 856115 = 1284173) B1284173
theorem B1085491 : Blo 854356 1085491 := bstep (se 1 (by rfl) ⟨814118, by rfl⟩ : syracuseStep 1085491 = 1628237) B1628237
theorem B1282115 : Blo 854356 1282115 := bstep (se 1 (by rfl) ⟨961586, by rfl⟩ : syracuseStep 1282115 = 1923173) B1923173
theorem B2166851 : Blo 854356 2166851 := bstep (se 1 (by rfl) ⟨1625138, by rfl⟩ : syracuseStep 2166851 = 3250277) B3250277
theorem B856131 : Blo 854356 856131 := bstep (se 1 (by rfl) ⟨642098, by rfl⟩ : syracuseStep 856131 = 1284197) B1284197
theorem B2887757 : Blo 854356 2887757 := bstep (se 3 (by rfl) ⟨541454, by rfl⟩ : syracuseStep 2887757 = 1082909) B1082909
theorem B856147 : Blo 854356 856147 := bstep (se 1 (by rfl) ⟨642110, by rfl⟩ : syracuseStep 856147 = 1284221) B1284221
theorem B1445971 : Blo 854356 1445971 := bstep (se 1 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 1445971 = 2168957) B2168957
theorem B1282145 : Blo 854356 1282145 := bstep (se 2 (by rfl) ⟨480804, by rfl⟩ : syracuseStep 1282145 = 961609) B961609
theorem B856163 : Blo 854356 856163 := bstep (se 1 (by rfl) ⟨642122, by rfl⟩ : syracuseStep 856163 = 1284245) B1284245
theorem B1282163 : Blo 854356 1282163 := bstep (se 1 (by rfl) ⟨961622, by rfl⟩ : syracuseStep 1282163 = 1923245) B1923245
theorem B856179 : Blo 854356 856179 := bstep (se 1 (by rfl) ⟨642134, by rfl⟩ : syracuseStep 856179 = 1284269) B1284269
theorem B2887811 : Blo 854356 2887811 := bstep (se 1 (by rfl) ⟨2165858, by rfl⟩ : syracuseStep 2887811 = 4331717) B4331717
theorem B856195 : Blo 854356 856195 := bstep (se 1 (by rfl) ⟨642146, by rfl⟩ : syracuseStep 856195 = 1284293) B1284293
theorem B4886669 : Blo 854356 4886669 := bstep (se 3 (by rfl) ⟨916250, by rfl⟩ : syracuseStep 4886669 = 1832501) B1832501
theorem B1282193 : Blo 854356 1282193 := bstep (se 2 (by rfl) ⟨480822, by rfl⟩ : syracuseStep 1282193 = 961645) B961645
theorem B856211 : Blo 854356 856211 := bstep (se 1 (by rfl) ⟨642158, by rfl⟩ : syracuseStep 856211 = 1284317) B1284317
theorem B1282211 : Blo 854356 1282211 := bstep (se 1 (by rfl) ⟨961658, by rfl⟩ : syracuseStep 1282211 = 1923317) B1923317
theorem B856227 : Blo 854356 856227 := bstep (se 1 (by rfl) ⟨642170, by rfl⟩ : syracuseStep 856227 = 1284341) B1284341
theorem B856243 : Blo 854356 856243 := bstep (se 1 (by rfl) ⟨642182, by rfl⟩ : syracuseStep 856243 = 1284365) B1284365
theorem B1282241 : Blo 854356 1282241 := bstep (se 2 (by rfl) ⟨480840, by rfl⟩ : syracuseStep 1282241 = 961681) B961681
theorem B856259 : Blo 854356 856259 := bstep (se 1 (by rfl) ⟨642194, by rfl⟩ : syracuseStep 856259 = 1284389) B1284389
theorem B3248333 : Blo 854356 3248333 := bstep (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) B1218125
theorem B1282259 : Blo 854356 1282259 := bstep (se 1 (by rfl) ⟨961694, by rfl⟩ : syracuseStep 1282259 = 1923389) B1923389
theorem B856275 : Blo 854356 856275 := bstep (se 1 (by rfl) ⟨642206, by rfl⟩ : syracuseStep 856275 = 1284413) B1284413
theorem B1446113 : Blo 854356 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B856291 : Blo 854356 856291 := bstep (se 1 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 856291 = 1284437) B1284437
theorem B1282289 : Blo 854356 1282289 := bstep (se 2 (by rfl) ⟨480858, by rfl⟩ : syracuseStep 1282289 = 961717) B961717
theorem B856307 : Blo 854356 856307 := bstep (se 1 (by rfl) ⟨642230, by rfl⟩ : syracuseStep 856307 = 1284461) B1284461
theorem B1282307 : Blo 854356 1282307 := bstep (se 1 (by rfl) ⟨961730, by rfl⟩ : syracuseStep 1282307 = 1923461) B1923461
theorem B856323 : Blo 854356 856323 := bstep (se 1 (by rfl) ⟨642242, by rfl⟩ : syracuseStep 856323 = 1284485) B1284485
theorem B856339 : Blo 854356 856339 := bstep (se 1 (by rfl) ⟨642254, by rfl⟩ : syracuseStep 856339 = 1284509) B1284509
theorem B1282337 : Blo 854356 1282337 := bstep (se 2 (by rfl) ⟨480876, by rfl⟩ : syracuseStep 1282337 = 961753) B961753
theorem B5476643 : Blo 854356 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B856355 : Blo 854356 856355 := bstep (se 1 (by rfl) ⟨642266, by rfl⟩ : syracuseStep 856355 = 1284533) B1284533
theorem B1282355 : Blo 854356 1282355 := bstep (se 1 (by rfl) ⟨961766, by rfl⟩ : syracuseStep 1282355 = 1923533) B1923533
theorem B856371 : Blo 854356 856371 := bstep (se 1 (by rfl) ⟨642278, by rfl⟩ : syracuseStep 856371 = 1284557) B1284557
theorem B856387 : Blo 854356 856387 := bstep (se 1 (by rfl) ⟨642290, by rfl⟩ : syracuseStep 856387 = 1284581) B1284581
theorem B1282385 : Blo 854356 1282385 := bstep (se 2 (by rfl) ⟨480894, by rfl⟩ : syracuseStep 1282385 = 961789) B961789
theorem B856403 : Blo 854356 856403 := bstep (se 1 (by rfl) ⟨642302, by rfl⟩ : syracuseStep 856403 = 1284605) B1284605
theorem B1446241 : Blo 854356 1446241 := bstep (se 2 (by rfl) ⟨542340, by rfl⟩ : syracuseStep 1446241 = 1084681) B1084681
theorem B1282403 : Blo 854356 1282403 := bstep (se 1 (by rfl) ⟨961802, by rfl⟩ : syracuseStep 1282403 = 1923605) B1923605
theorem B856419 : Blo 854356 856419 := bstep (se 1 (by rfl) ⟨642314, by rfl⟩ : syracuseStep 856419 = 1284629) B1284629
theorem B856435 : Blo 854356 856435 := bstep (se 1 (by rfl) ⟨642326, by rfl⟩ : syracuseStep 856435 = 1284653) B1284653
theorem B1282433 : Blo 854356 1282433 := bstep (se 2 (by rfl) ⟨480912, by rfl⟩ : syracuseStep 1282433 = 961825) B961825
theorem B856451 : Blo 854356 856451 := bstep (se 1 (by rfl) ⟨642338, by rfl⟩ : syracuseStep 856451 = 1284677) B1284677
theorem B1446275 : Blo 854356 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B2888081 : Blo 854356 2888081 := bstep (se 2 (by rfl) ⟨1083030, by rfl⟩ : syracuseStep 2888081 = 2166061) B2166061
theorem B1282451 : Blo 854356 1282451 := bstep (se 1 (by rfl) ⟨961838, by rfl⟩ : syracuseStep 1282451 = 1923677) B1923677
theorem B856467 : Blo 854356 856467 := bstep (se 1 (by rfl) ⟨642350, by rfl⟩ : syracuseStep 856467 = 1284701) B1284701
theorem B856483 : Blo 854356 856483 := bstep (se 1 (by rfl) ⟨642362, by rfl⟩ : syracuseStep 856483 = 1284725) B1284725
theorem B1282481 : Blo 854356 1282481 := bstep (se 2 (by rfl) ⟨480930, by rfl⟩ : syracuseStep 1282481 = 961861) B961861
theorem B856499 : Blo 854356 856499 := bstep (se 1 (by rfl) ⟨642374, by rfl⟩ : syracuseStep 856499 = 1284749) B1284749
theorem B1282499 : Blo 854356 1282499 := bstep (se 1 (by rfl) ⟨961874, by rfl⟩ : syracuseStep 1282499 = 1923749) B1923749
theorem B856515 : Blo 854356 856515 := bstep (se 1 (by rfl) ⟨642386, by rfl⟩ : syracuseStep 856515 = 1284773) B1284773
theorem B856531 : Blo 854356 856531 := bstep (se 1 (by rfl) ⟨642398, by rfl⟩ : syracuseStep 856531 = 1284797) B1284797
theorem B1282529 : Blo 854356 1282529 := bstep (se 2 (by rfl) ⟨480948, by rfl⟩ : syracuseStep 1282529 = 961897) B961897
theorem B856547 : Blo 854356 856547 := bstep (se 1 (by rfl) ⟨642410, by rfl⟩ : syracuseStep 856547 = 1284821) B1284821
theorem B1282547 : Blo 854356 1282547 := bstep (se 1 (by rfl) ⟨961910, by rfl⟩ : syracuseStep 1282547 = 1923821) B1923821
theorem B856563 : Blo 854356 856563 := bstep (se 1 (by rfl) ⟨642422, by rfl⟩ : syracuseStep 856563 = 1284845) B1284845
theorem B856579 : Blo 854356 856579 := bstep (se 1 (by rfl) ⟨642434, by rfl⟩ : syracuseStep 856579 = 1284869) B1284869
theorem B1446403 : Blo 854356 1446403 := bstep (se 1 (by rfl) ⟨1084802, by rfl⟩ : syracuseStep 1446403 = 2169605) B2169605
theorem B1282577 : Blo 854356 1282577 := bstep (se 2 (by rfl) ⟨480966, by rfl⟩ : syracuseStep 1282577 = 961933) B961933
theorem B856595 : Blo 854356 856595 := bstep (se 1 (by rfl) ⟨642446, by rfl⟩ : syracuseStep 856595 = 1284893) B1284893
theorem B1282595 : Blo 854356 1282595 := bstep (se 1 (by rfl) ⟨961946, by rfl⟩ : syracuseStep 1282595 = 1923893) B1923893
theorem B856611 : Blo 854356 856611 := bstep (se 1 (by rfl) ⟨642458, by rfl⟩ : syracuseStep 856611 = 1284917) B1284917
theorem B1085987 : Blo 854356 1085987 := bstep (se 1 (by rfl) ⟨814490, by rfl⟩ : syracuseStep 1085987 = 1628981) B1628981
theorem B856627 : Blo 854356 856627 := bstep (se 1 (by rfl) ⟨642470, by rfl⟩ : syracuseStep 856627 = 1284941) B1284941
theorem B1282625 : Blo 854356 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B856643 : Blo 854356 856643 := bstep (se 1 (by rfl) ⟨642482, by rfl⟩ : syracuseStep 856643 = 1284965) B1284965
theorem B1282643 : Blo 854356 1282643 := bstep (se 1 (by rfl) ⟨961982, by rfl⟩ : syracuseStep 1282643 = 1923965) B1923965
theorem B856659 : Blo 854356 856659 := bstep (se 1 (by rfl) ⟨642494, by rfl⟩ : syracuseStep 856659 = 1284989) B1284989
theorem B856675 : Blo 854356 856675 := bstep (se 1 (by rfl) ⟨642506, by rfl⟩ : syracuseStep 856675 = 1285013) B1285013
theorem B1282673 : Blo 854356 1282673 := bstep (se 2 (by rfl) ⟨481002, by rfl⟩ : syracuseStep 1282673 = 962005) B962005
theorem B4330097 : Blo 854356 4330097 := bstep (se 2 (by rfl) ⟨1623786, by rfl⟩ : syracuseStep 4330097 = 3247573) B3247573
theorem B856691 : Blo 854356 856691 := bstep (se 1 (by rfl) ⟨642518, by rfl⟩ : syracuseStep 856691 = 1285037) B1285037
theorem B1282691 : Blo 854356 1282691 := bstep (se 1 (by rfl) ⟨962018, by rfl⟩ : syracuseStep 1282691 = 1924037) B1924037
theorem B856707 : Blo 854356 856707 := bstep (se 1 (by rfl) ⟨642530, by rfl⟩ : syracuseStep 856707 = 1285061) B1285061
theorem B1446545 : Blo 854356 1446545 := bstep (se 2 (by rfl) ⟨542454, by rfl⟩ : syracuseStep 1446545 = 1084909) B1084909
theorem B856723 : Blo 854356 856723 := bstep (se 1 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 856723 = 1285085) B1285085
theorem B1282721 : Blo 854356 1282721 := bstep (se 2 (by rfl) ⟨481020, by rfl⟩ : syracuseStep 1282721 = 962041) B962041
theorem B856739 : Blo 854356 856739 := bstep (se 1 (by rfl) ⟨642554, by rfl⟩ : syracuseStep 856739 = 1285109) B1285109
theorem B1282739 : Blo 854356 1282739 := bstep (se 1 (by rfl) ⟨962054, by rfl⟩ : syracuseStep 1282739 = 1924109) B1924109
theorem B856755 : Blo 854356 856755 := bstep (se 1 (by rfl) ⟨642566, by rfl⟩ : syracuseStep 856755 = 1285133) B1285133
theorem B856771 : Blo 854356 856771 := bstep (se 1 (by rfl) ⟨642578, by rfl⟩ : syracuseStep 856771 = 1285157) B1285157
theorem B1282769 : Blo 854356 1282769 := bstep (se 2 (by rfl) ⟨481038, by rfl⟩ : syracuseStep 1282769 = 962077) B962077
theorem B856787 : Blo 854356 856787 := bstep (se 1 (by rfl) ⟨642590, by rfl⟩ : syracuseStep 856787 = 1285181) B1285181
theorem B1282787 : Blo 854356 1282787 := bstep (se 1 (by rfl) ⟨962090, by rfl⟩ : syracuseStep 1282787 = 1924181) B1924181
theorem B856803 : Blo 854356 856803 := bstep (se 1 (by rfl) ⟨642602, by rfl⟩ : syracuseStep 856803 = 1285205) B1285205
theorem B11899619 : Blo 854356 11899619 := bstep (se 1 (by rfl) ⟨8924714, by rfl⟩ : syracuseStep 11899619 = 17849429) B17849429
theorem B856819 : Blo 854356 856819 := bstep (se 1 (by rfl) ⟨642614, by rfl⟩ : syracuseStep 856819 = 1285229) B1285229
theorem B1282817 : Blo 854356 1282817 := bstep (se 2 (by rfl) ⟨481056, by rfl⟩ : syracuseStep 1282817 = 962113) B962113
theorem B856835 : Blo 854356 856835 := bstep (se 1 (by rfl) ⟨642626, by rfl⟩ : syracuseStep 856835 = 1285253) B1285253
theorem B1446673 : Blo 854356 1446673 := bstep (se 2 (by rfl) ⟨542502, by rfl⟩ : syracuseStep 1446673 = 1085005) B1085005
theorem B1282835 : Blo 854356 1282835 := bstep (se 1 (by rfl) ⟨962126, by rfl⟩ : syracuseStep 1282835 = 1924253) B1924253
theorem B856851 : Blo 854356 856851 := bstep (se 1 (by rfl) ⟨642638, by rfl⟩ : syracuseStep 856851 = 1285277) B1285277
theorem B856867 : Blo 854356 856867 := bstep (se 1 (by rfl) ⟨642650, by rfl⟩ : syracuseStep 856867 = 1285301) B1285301
theorem B1282865 : Blo 854356 1282865 := bstep (se 2 (by rfl) ⟨481074, by rfl⟩ : syracuseStep 1282865 = 962149) B962149
theorem B856883 : Blo 854356 856883 := bstep (se 1 (by rfl) ⟨642662, by rfl⟩ : syracuseStep 856883 = 1285325) B1285325
theorem B1446707 : Blo 854356 1446707 := bstep (se 1 (by rfl) ⟨1085030, by rfl⟩ : syracuseStep 1446707 = 2170061) B2170061
theorem B1282883 : Blo 854356 1282883 := bstep (se 1 (by rfl) ⟨962162, by rfl⟩ : syracuseStep 1282883 = 1924325) B1924325
theorem B856899 : Blo 854356 856899 := bstep (se 1 (by rfl) ⟨642674, by rfl⟩ : syracuseStep 856899 = 1285349) B1285349
theorem B856915 : Blo 854356 856915 := bstep (se 1 (by rfl) ⟨642686, by rfl⟩ : syracuseStep 856915 = 1285373) B1285373
theorem B1282913 : Blo 854356 1282913 := bstep (se 2 (by rfl) ⟨481092, by rfl⟩ : syracuseStep 1282913 = 962185) B962185
theorem B856931 : Blo 854356 856931 := bstep (se 1 (by rfl) ⟨642698, by rfl⟩ : syracuseStep 856931 = 1285397) B1285397
theorem B10949489 : Blo 854356 10949489 := bstep (se 2 (by rfl) ⟨4106058, by rfl⟩ : syracuseStep 10949489 = 8212117) B8212117
theorem B1282931 : Blo 854356 1282931 := bstep (se 1 (by rfl) ⟨962198, by rfl⟩ : syracuseStep 1282931 = 1924397) B1924397
theorem B856947 : Blo 854356 856947 := bstep (se 1 (by rfl) ⟨642710, by rfl⟩ : syracuseStep 856947 = 1285421) B1285421
theorem B856963 : Blo 854356 856963 := bstep (se 1 (by rfl) ⟨642722, by rfl⟩ : syracuseStep 856963 = 1285445) B1285445
theorem B1217425 : Blo 854356 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B1282961 : Blo 854356 1282961 := bstep (se 2 (by rfl) ⟨481110, by rfl⟩ : syracuseStep 1282961 = 962221) B962221
theorem B856979 : Blo 854356 856979 := bstep (se 1 (by rfl) ⟨642734, by rfl⟩ : syracuseStep 856979 = 1285469) B1285469
theorem B1282979 : Blo 854356 1282979 := bstep (se 1 (by rfl) ⟨962234, by rfl⟩ : syracuseStep 1282979 = 1924469) B1924469
theorem B856995 : Blo 854356 856995 := bstep (se 1 (by rfl) ⟨642746, by rfl⟩ : syracuseStep 856995 = 1285493) B1285493
theorem B2888621 : Blo 854356 2888621 := bstep (se 3 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 2888621 = 1083233) B1083233
theorem B857011 : Blo 854356 857011 := bstep (se 1 (by rfl) ⟨642758, by rfl⟩ : syracuseStep 857011 = 1285517) B1285517
theorem B1446835 : Blo 854356 1446835 := bstep (se 1 (by rfl) ⟨1085126, by rfl⟩ : syracuseStep 1446835 = 2170253) B2170253
theorem B1283009 : Blo 854356 1283009 := bstep (se 2 (by rfl) ⟨481128, by rfl⟩ : syracuseStep 1283009 = 962257) B962257
theorem B857027 : Blo 854356 857027 := bstep (se 1 (by rfl) ⟨642770, by rfl⟩ : syracuseStep 857027 = 1285541) B1285541
theorem B1283027 : Blo 854356 1283027 := bstep (se 1 (by rfl) ⟨962270, by rfl⟩ : syracuseStep 1283027 = 1924541) B1924541
theorem B857043 : Blo 854356 857043 := bstep (se 1 (by rfl) ⟨642782, by rfl⟩ : syracuseStep 857043 = 1285565) B1285565
theorem B2888675 : Blo 854356 2888675 := bstep (se 1 (by rfl) ⟨2166506, by rfl⟩ : syracuseStep 2888675 = 4333013) B4333013
theorem B857059 : Blo 854356 857059 := bstep (se 1 (by rfl) ⟨642794, by rfl⟩ : syracuseStep 857059 = 1285589) B1285589
theorem B1217521 : Blo 854356 1217521 := bstep (se 2 (by rfl) ⟨456570, by rfl⟩ : syracuseStep 1217521 = 913141) B913141
theorem B1283057 : Blo 854356 1283057 := bstep (se 2 (by rfl) ⟨481146, by rfl⟩ : syracuseStep 1283057 = 962293) B962293
theorem B2167793 : Blo 854356 2167793 := bstep (se 2 (by rfl) ⟨812922, by rfl⟩ : syracuseStep 2167793 = 1625845) B1625845
theorem B857075 : Blo 854356 857075 := bstep (se 1 (by rfl) ⟨642806, by rfl⟩ : syracuseStep 857075 = 1285613) B1285613
theorem B1283075 : Blo 854356 1283075 := bstep (se 1 (by rfl) ⟨962306, by rfl⟩ : syracuseStep 1283075 = 1924613) B1924613
theorem B857091 : Blo 854356 857091 := bstep (se 1 (by rfl) ⟨642818, by rfl⟩ : syracuseStep 857091 = 1285637) B1285637
theorem B857107 : Blo 854356 857107 := bstep (se 1 (by rfl) ⟨642830, by rfl⟩ : syracuseStep 857107 = 1285661) B1285661
theorem B1283105 : Blo 854356 1283105 := bstep (se 2 (by rfl) ⟨481164, by rfl⟩ : syracuseStep 1283105 = 962329) B962329
theorem B2167843 : Blo 854356 2167843 := bstep (se 1 (by rfl) ⟨1625882, by rfl⟩ : syracuseStep 2167843 = 3251765) B3251765
theorem B857123 : Blo 854356 857123 := bstep (se 1 (by rfl) ⟨642842, by rfl⟩ : syracuseStep 857123 = 1285685) B1285685
theorem B1283123 : Blo 854356 1283123 := bstep (se 1 (by rfl) ⟨962342, by rfl⟩ : syracuseStep 1283123 = 1924685) B1924685
theorem B857139 : Blo 854356 857139 := bstep (se 1 (by rfl) ⟨642854, by rfl⟩ : syracuseStep 857139 = 1285709) B1285709
theorem B1446977 : Blo 854356 1446977 := bstep (se 2 (by rfl) ⟨542616, by rfl⟩ : syracuseStep 1446977 = 1085233) B1085233
theorem B857155 : Blo 854356 857155 := bstep (se 1 (by rfl) ⟨642866, by rfl⟩ : syracuseStep 857155 = 1285733) B1285733
theorem B1283153 : Blo 854356 1283153 := bstep (se 2 (by rfl) ⟨481182, by rfl⟩ : syracuseStep 1283153 = 962365) B962365
theorem B857171 : Blo 854356 857171 := bstep (se 1 (by rfl) ⟨642878, by rfl⟩ : syracuseStep 857171 = 1285757) B1285757
theorem B1283171 : Blo 854356 1283171 := bstep (se 1 (by rfl) ⟨962378, by rfl⟩ : syracuseStep 1283171 = 1924757) B1924757
theorem B857187 : Blo 854356 857187 := bstep (se 1 (by rfl) ⟨642890, by rfl⟩ : syracuseStep 857187 = 1285781) B1285781
theorem B857203 : Blo 854356 857203 := bstep (se 1 (by rfl) ⟨642902, by rfl⟩ : syracuseStep 857203 = 1285805) B1285805
theorem B1283201 : Blo 854356 1283201 := bstep (se 2 (by rfl) ⟨481200, by rfl⟩ : syracuseStep 1283201 = 962401) B962401
theorem B857219 : Blo 854356 857219 := bstep (se 1 (by rfl) ⟨642914, by rfl⟩ : syracuseStep 857219 = 1285829) B1285829
theorem B1283219 : Blo 854356 1283219 := bstep (se 1 (by rfl) ⟨962414, by rfl⟩ : syracuseStep 1283219 = 1924829) B1924829
theorem B857235 : Blo 854356 857235 := bstep (se 1 (by rfl) ⟨642926, by rfl⟩ : syracuseStep 857235 = 1285853) B1285853
theorem B857251 : Blo 854356 857251 := bstep (se 1 (by rfl) ⟨642938, by rfl⟩ : syracuseStep 857251 = 1285877) B1285877
theorem B1283249 : Blo 854356 1283249 := bstep (se 2 (by rfl) ⟨481218, by rfl⟩ : syracuseStep 1283249 = 962437) B962437
theorem B2167985 : Blo 854356 2167985 := bstep (se 2 (by rfl) ⟨812994, by rfl⟩ : syracuseStep 2167985 = 1625989) B1625989
theorem B857267 : Blo 854356 857267 := bstep (se 1 (by rfl) ⟨642950, by rfl⟩ : syracuseStep 857267 = 1285901) B1285901
theorem B1447105 : Blo 854356 1447105 := bstep (se 2 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 1447105 = 1085329) B1085329
theorem B1283267 : Blo 854356 1283267 := bstep (se 1 (by rfl) ⟨962450, by rfl⟩ : syracuseStep 1283267 = 1924901) B1924901
theorem B857283 : Blo 854356 857283 := bstep (se 1 (by rfl) ⟨642962, by rfl⟩ : syracuseStep 857283 = 1285925) B1285925
theorem B857299 : Blo 854356 857299 := bstep (se 1 (by rfl) ⟨642974, by rfl⟩ : syracuseStep 857299 = 1285949) B1285949
theorem B1283297 : Blo 854356 1283297 := bstep (se 2 (by rfl) ⟨481236, by rfl⟩ : syracuseStep 1283297 = 962473) B962473
theorem B857315 : Blo 854356 857315 := bstep (se 1 (by rfl) ⟨642986, by rfl⟩ : syracuseStep 857315 = 1285973) B1285973
theorem B1447139 : Blo 854356 1447139 := bstep (se 1 (by rfl) ⟨1085354, by rfl⟩ : syracuseStep 1447139 = 2170709) B2170709
theorem B2888945 : Blo 854356 2888945 := bstep (se 2 (by rfl) ⟨1083354, by rfl⟩ : syracuseStep 2888945 = 2166709) B2166709
theorem B1283315 : Blo 854356 1283315 := bstep (se 1 (by rfl) ⟨962486, by rfl⟩ : syracuseStep 1283315 = 1924973) B1924973
theorem B857331 : Blo 854356 857331 := bstep (se 1 (by rfl) ⟨642998, by rfl⟩ : syracuseStep 857331 = 1285997) B1285997
theorem B857347 : Blo 854356 857347 := bstep (se 1 (by rfl) ⟨643010, by rfl⟩ : syracuseStep 857347 = 1286021) B1286021
theorem B1545475 : Blo 854356 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B1283345 : Blo 854356 1283345 := bstep (se 2 (by rfl) ⟨481254, by rfl⟩ : syracuseStep 1283345 = 962509) B962509
theorem B857363 : Blo 854356 857363 := bstep (se 1 (by rfl) ⟨643022, by rfl⟩ : syracuseStep 857363 = 1286045) B1286045
theorem B1283363 : Blo 854356 1283363 := bstep (se 1 (by rfl) ⟨962522, by rfl⟩ : syracuseStep 1283363 = 1925045) B1925045
theorem B857379 : Blo 854356 857379 := bstep (se 1 (by rfl) ⟨643034, by rfl⟩ : syracuseStep 857379 = 1286069) B1286069
theorem B857395 : Blo 854356 857395 := bstep (se 1 (by rfl) ⟨643046, by rfl⟩ : syracuseStep 857395 = 1286093) B1286093
theorem B1283393 : Blo 854356 1283393 := bstep (se 2 (by rfl) ⟨481272, by rfl⟩ : syracuseStep 1283393 = 962545) B962545
theorem B857411 : Blo 854356 857411 := bstep (se 1 (by rfl) ⟨643058, by rfl⟩ : syracuseStep 857411 = 1286117) B1286117
theorem B1283411 : Blo 854356 1283411 := bstep (se 1 (by rfl) ⟨962558, by rfl⟩ : syracuseStep 1283411 = 1925117) B1925117
theorem B857427 : Blo 854356 857427 := bstep (se 1 (by rfl) ⟨643070, by rfl⟩ : syracuseStep 857427 = 1286141) B1286141
theorem B857443 : Blo 854356 857443 := bstep (se 1 (by rfl) ⟨643082, by rfl⟩ : syracuseStep 857443 = 1286165) B1286165
theorem B1447267 : Blo 854356 1447267 := bstep (se 1 (by rfl) ⟨1085450, by rfl⟩ : syracuseStep 1447267 = 2170901) B2170901
theorem B1283441 : Blo 854356 1283441 := bstep (se 2 (by rfl) ⟨481290, by rfl⟩ : syracuseStep 1283441 = 962581) B962581
theorem B857459 : Blo 854356 857459 := bstep (se 1 (by rfl) ⟨643094, by rfl⟩ : syracuseStep 857459 = 1286189) B1286189
theorem B1283459 : Blo 854356 1283459 := bstep (se 1 (by rfl) ⟨962594, by rfl⟩ : syracuseStep 1283459 = 1925189) B1925189
theorem B857475 : Blo 854356 857475 := bstep (se 1 (by rfl) ⟨643106, by rfl⟩ : syracuseStep 857475 = 1286213) B1286213
theorem B7312781 : Blo 854356 7312781 := bstep (se 3 (by rfl) ⟨1371146, by rfl⟩ : syracuseStep 7312781 = 2742293) B2742293
theorem B3478925 : Blo 854356 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B857491 : Blo 854356 857491 := bstep (se 1 (by rfl) ⟨643118, by rfl⟩ : syracuseStep 857491 = 1286237) B1286237
theorem B1283489 : Blo 854356 1283489 := bstep (se 2 (by rfl) ⟨481308, by rfl⟩ : syracuseStep 1283489 = 962617) B962617
theorem B857507 : Blo 854356 857507 := bstep (se 1 (by rfl) ⟨643130, by rfl⟩ : syracuseStep 857507 = 1286261) B1286261
theorem B1283507 : Blo 854356 1283507 := bstep (se 1 (by rfl) ⟨962630, by rfl⟩ : syracuseStep 1283507 = 1925261) B1925261
theorem B857523 : Blo 854356 857523 := bstep (se 1 (by rfl) ⟨643142, by rfl⟩ : syracuseStep 857523 = 1286285) B1286285
theorem B857539 : Blo 854356 857539 := bstep (se 1 (by rfl) ⟨643154, by rfl⟩ : syracuseStep 857539 = 1286309) B1286309
theorem B1283537 : Blo 854356 1283537 := bstep (se 2 (by rfl) ⟨481326, by rfl⟩ : syracuseStep 1283537 = 962653) B962653
theorem B857555 : Blo 854356 857555 := bstep (se 1 (by rfl) ⟨643166, by rfl⟩ : syracuseStep 857555 = 1286333) B1286333
theorem B1218017 : Blo 854356 1218017 := bstep (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) B913513
theorem B1283555 : Blo 854356 1283555 := bstep (se 1 (by rfl) ⟨962666, by rfl⟩ : syracuseStep 1283555 = 1925333) B1925333
theorem B857571 : Blo 854356 857571 := bstep (se 1 (by rfl) ⟨643178, by rfl⟩ : syracuseStep 857571 = 1286357) B1286357
theorem B14652899 : Blo 854356 14652899 := bstep (se 1 (by rfl) ⟨10989674, by rfl⟩ : syracuseStep 14652899 = 21979349) B21979349
theorem B1447409 : Blo 854356 1447409 := bstep (se 2 (by rfl) ⟨542778, by rfl⟩ : syracuseStep 1447409 = 1085557) B1085557
theorem B857587 : Blo 854356 857587 := bstep (se 1 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 857587 = 1286381) B1286381
theorem B1283585 : Blo 854356 1283585 := bstep (se 2 (by rfl) ⟨481344, by rfl⟩ : syracuseStep 1283585 = 962689) B962689
theorem B857603 : Blo 854356 857603 := bstep (se 1 (by rfl) ⟨643202, by rfl⟩ : syracuseStep 857603 = 1286405) B1286405
theorem B1283603 : Blo 854356 1283603 := bstep (se 1 (by rfl) ⟨962702, by rfl⟩ : syracuseStep 1283603 = 1925405) B1925405
theorem B857619 : Blo 854356 857619 := bstep (se 1 (by rfl) ⟨643214, by rfl⟩ : syracuseStep 857619 = 1286429) B1286429
theorem B857635 : Blo 854356 857635 := bstep (se 1 (by rfl) ⟨643226, by rfl⟩ : syracuseStep 857635 = 1286453) B1286453
theorem B1283633 : Blo 854356 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B857651 : Blo 854356 857651 := bstep (se 1 (by rfl) ⟨643238, by rfl⟩ : syracuseStep 857651 = 1286477) B1286477
theorem B1283651 : Blo 854356 1283651 := bstep (se 1 (by rfl) ⟨962738, by rfl⟩ : syracuseStep 1283651 = 1925477) B1925477
theorem B857667 : Blo 854356 857667 := bstep (se 1 (by rfl) ⟨643250, by rfl⟩ : syracuseStep 857667 = 1286501) B1286501
theorem B857683 : Blo 854356 857683 := bstep (se 1 (by rfl) ⟨643262, by rfl⟩ : syracuseStep 857683 = 1286525) B1286525
theorem B1283681 : Blo 854356 1283681 := bstep (se 2 (by rfl) ⟨481380, by rfl⟩ : syracuseStep 1283681 = 962761) B962761
theorem B857699 : Blo 854356 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B1447537 : Blo 854356 1447537 := bstep (se 2 (by rfl) ⟨542826, by rfl⟩ : syracuseStep 1447537 = 1085653) B1085653
theorem B1283699 : Blo 854356 1283699 := bstep (se 1 (by rfl) ⟨962774, by rfl⟩ : syracuseStep 1283699 = 1925549) B1925549
theorem B857715 : Blo 854356 857715 := bstep (se 1 (by rfl) ⟨643286, by rfl⟩ : syracuseStep 857715 = 1286573) B1286573
theorem B857731 : Blo 854356 857731 := bstep (se 1 (by rfl) ⟨643298, by rfl⟩ : syracuseStep 857731 = 1286597) B1286597
theorem B1283729 : Blo 854356 1283729 := bstep (se 2 (by rfl) ⟨481398, by rfl⟩ : syracuseStep 1283729 = 962797) B962797
theorem B857747 : Blo 854356 857747 := bstep (se 1 (by rfl) ⟨643310, by rfl⟩ : syracuseStep 857747 = 1286621) B1286621
theorem B1447571 : Blo 854356 1447571 := bstep (se 1 (by rfl) ⟨1085678, by rfl⟩ : syracuseStep 1447571 = 2171357) B2171357
theorem B1283747 : Blo 854356 1283747 := bstep (se 1 (by rfl) ⟨962810, by rfl⟩ : syracuseStep 1283747 = 1925621) B1925621
theorem B857763 : Blo 854356 857763 := bstep (se 1 (by rfl) ⟨643322, by rfl⟩ : syracuseStep 857763 = 1286645) B1286645
theorem B857779 : Blo 854356 857779 := bstep (se 1 (by rfl) ⟨643334, by rfl⟩ : syracuseStep 857779 = 1286669) B1286669
theorem B1283777 : Blo 854356 1283777 := bstep (se 2 (by rfl) ⟨481416, by rfl⟩ : syracuseStep 1283777 = 962833) B962833
theorem B857795 : Blo 854356 857795 := bstep (se 1 (by rfl) ⟨643346, by rfl⟩ : syracuseStep 857795 = 1286693) B1286693
theorem B1283795 : Blo 854356 1283795 := bstep (se 1 (by rfl) ⟨962846, by rfl⟩ : syracuseStep 1283795 = 1925693) B1925693
theorem B857811 : Blo 854356 857811 := bstep (se 1 (by rfl) ⟨643358, by rfl⟩ : syracuseStep 857811 = 1286717) B1286717
theorem B857827 : Blo 854356 857827 := bstep (se 1 (by rfl) ⟨643370, by rfl⟩ : syracuseStep 857827 = 1286741) B1286741
theorem B3479267 : Blo 854356 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B1283825 : Blo 854356 1283825 := bstep (se 2 (by rfl) ⟨481434, by rfl⟩ : syracuseStep 1283825 = 962869) B962869
theorem B857843 : Blo 854356 857843 := bstep (se 1 (by rfl) ⟨643382, by rfl⟩ : syracuseStep 857843 = 1286765) B1286765
theorem B1283843 : Blo 854356 1283843 := bstep (se 1 (by rfl) ⟨962882, by rfl⟩ : syracuseStep 1283843 = 1925765) B1925765
theorem B857859 : Blo 854356 857859 := bstep (se 1 (by rfl) ⟨643394, by rfl⟩ : syracuseStep 857859 = 1286789) B1286789
theorem B2889485 : Blo 854356 2889485 := bstep (se 3 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 2889485 = 1083557) B1083557
theorem B857875 : Blo 854356 857875 := bstep (se 1 (by rfl) ⟨643406, by rfl⟩ : syracuseStep 857875 = 1286813) B1286813
theorem B1447699 : Blo 854356 1447699 := bstep (se 1 (by rfl) ⟨1085774, by rfl⟩ : syracuseStep 1447699 = 2171549) B2171549
theorem B1283873 : Blo 854356 1283873 := bstep (se 2 (by rfl) ⟨481452, by rfl⟩ : syracuseStep 1283873 = 962905) B962905
theorem B857891 : Blo 854356 857891 := bstep (se 1 (by rfl) ⟨643418, by rfl⟩ : syracuseStep 857891 = 1286837) B1286837
theorem B1283891 : Blo 854356 1283891 := bstep (se 1 (by rfl) ⟨962918, by rfl⟩ : syracuseStep 1283891 = 1925837) B1925837
theorem B857907 : Blo 854356 857907 := bstep (se 1 (by rfl) ⟨643430, by rfl⟩ : syracuseStep 857907 = 1286861) B1286861
theorem B2889539 : Blo 854356 2889539 := bstep (se 1 (by rfl) ⟨2167154, by rfl⟩ : syracuseStep 2889539 = 4334309) B4334309
theorem B857923 : Blo 854356 857923 := bstep (se 1 (by rfl) ⟨643442, by rfl⟩ : syracuseStep 857923 = 1286885) B1286885
theorem B1283921 : Blo 854356 1283921 := bstep (se 2 (by rfl) ⟨481470, by rfl⟩ : syracuseStep 1283921 = 962941) B962941
theorem B857939 : Blo 854356 857939 := bstep (se 1 (by rfl) ⟨643454, by rfl⟩ : syracuseStep 857939 = 1286909) B1286909
theorem B1283939 : Blo 854356 1283939 := bstep (se 1 (by rfl) ⟨962954, by rfl⟩ : syracuseStep 1283939 = 1925909) B1925909
theorem B857955 : Blo 854356 857955 := bstep (se 1 (by rfl) ⟨643466, by rfl⟩ : syracuseStep 857955 = 1286933) B1286933
theorem B3479395 : Blo 854356 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B857971 : Blo 854356 857971 := bstep (se 1 (by rfl) ⟨643478, by rfl⟩ : syracuseStep 857971 = 1286957) B1286957
theorem B1283969 : Blo 854356 1283969 := bstep (se 2 (by rfl) ⟨481488, by rfl⟩ : syracuseStep 1283969 = 962977) B962977
theorem B857987 : Blo 854356 857987 := bstep (se 1 (by rfl) ⟨643490, by rfl⟩ : syracuseStep 857987 = 1286981) B1286981
theorem B1283987 : Blo 854356 1283987 := bstep (se 1 (by rfl) ⟨962990, by rfl⟩ : syracuseStep 1283987 = 1925981) B1925981
theorem B858003 : Blo 854356 858003 := bstep (se 1 (by rfl) ⟨643502, by rfl⟩ : syracuseStep 858003 = 1287005) B1287005
theorem B1447841 : Blo 854356 1447841 := bstep (se 2 (by rfl) ⟨542940, by rfl⟩ : syracuseStep 1447841 = 1085881) B1085881
theorem B858019 : Blo 854356 858019 := bstep (se 1 (by rfl) ⟨643514, by rfl⟩ : syracuseStep 858019 = 1287029) B1287029
theorem B1284017 : Blo 854356 1284017 := bstep (se 2 (by rfl) ⟨481506, by rfl⟩ : syracuseStep 1284017 = 963013) B963013
theorem B858035 : Blo 854356 858035 := bstep (se 1 (by rfl) ⟨643526, by rfl⟩ : syracuseStep 858035 = 1287053) B1287053
theorem B1284035 : Blo 854356 1284035 := bstep (se 1 (by rfl) ⟨963026, by rfl⟩ : syracuseStep 1284035 = 1926053) B1926053
theorem B858051 : Blo 854356 858051 := bstep (se 1 (by rfl) ⟨643538, by rfl⟩ : syracuseStep 858051 = 1287077) B1287077
theorem B6166469 : Blo 854356 6166469 := bstep (se 4 (by rfl) ⟨578106, by rfl⟩ : syracuseStep 6166469 = 1156213) B1156213
theorem B858067 : Blo 854356 858067 := bstep (se 1 (by rfl) ⟨643550, by rfl⟩ : syracuseStep 858067 = 1287101) B1287101
theorem B1284065 : Blo 854356 1284065 := bstep (se 2 (by rfl) ⟨481524, by rfl⟩ : syracuseStep 1284065 = 963049) B963049
theorem B858083 : Blo 854356 858083 := bstep (se 1 (by rfl) ⟨643562, by rfl⟩ : syracuseStep 858083 = 1287125) B1287125
theorem B1284083 : Blo 854356 1284083 := bstep (se 1 (by rfl) ⟨963062, by rfl⟩ : syracuseStep 1284083 = 1926125) B1926125
theorem B858099 : Blo 854356 858099 := bstep (se 1 (by rfl) ⟨643574, by rfl⟩ : syracuseStep 858099 = 1287149) B1287149
theorem B858115 : Blo 854356 858115 := bstep (se 1 (by rfl) ⟨643586, by rfl⟩ : syracuseStep 858115 = 1287173) B1287173
theorem B1284113 : Blo 854356 1284113 := bstep (se 2 (by rfl) ⟨481542, by rfl⟩ : syracuseStep 1284113 = 963085) B963085
theorem B858131 : Blo 854356 858131 := bstep (se 1 (by rfl) ⟨643598, by rfl⟩ : syracuseStep 858131 = 1287197) B1287197
theorem B1447969 : Blo 854356 1447969 := bstep (se 2 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 1447969 = 1085977) B1085977
theorem B4331555 : Blo 854356 4331555 := bstep (se 1 (by rfl) ⟨3248666, by rfl⟩ : syracuseStep 4331555 = 6497333) B6497333
theorem B1284131 : Blo 854356 1284131 := bstep (se 1 (by rfl) ⟨963098, by rfl⟩ : syracuseStep 1284131 = 1926197) B1926197
theorem B858147 : Blo 854356 858147 := bstep (se 1 (by rfl) ⟨643610, by rfl⟩ : syracuseStep 858147 = 1287221) B1287221
theorem B858163 : Blo 854356 858163 := bstep (se 1 (by rfl) ⟨643622, by rfl⟩ : syracuseStep 858163 = 1287245) B1287245
theorem B1284161 : Blo 854356 1284161 := bstep (se 2 (by rfl) ⟨481560, by rfl⟩ : syracuseStep 1284161 = 963121) B963121
theorem B1448003 : Blo 854356 1448003 := bstep (se 1 (by rfl) ⟨1086002, by rfl⟩ : syracuseStep 1448003 = 2172005) B2172005
theorem B858179 : Blo 854356 858179 := bstep (se 1 (by rfl) ⟨643634, by rfl⟩ : syracuseStep 858179 = 1287269) B1287269
theorem B2889809 : Blo 854356 2889809 := bstep (se 2 (by rfl) ⟨1083678, by rfl⟩ : syracuseStep 2889809 = 2167357) B2167357
theorem B1284179 : Blo 854356 1284179 := bstep (se 1 (by rfl) ⟨963134, by rfl⟩ : syracuseStep 1284179 = 1926269) B1926269
theorem B858195 : Blo 854356 858195 := bstep (se 1 (by rfl) ⟨643646, by rfl⟩ : syracuseStep 858195 = 1287293) B1287293
theorem B858211 : Blo 854356 858211 := bstep (se 1 (by rfl) ⟨643658, by rfl⟩ : syracuseStep 858211 = 1287317) B1287317
theorem B1284209 : Blo 854356 1284209 := bstep (se 2 (by rfl) ⟨481578, by rfl⟩ : syracuseStep 1284209 = 963157) B963157
theorem B858227 : Blo 854356 858227 := bstep (se 1 (by rfl) ⟨643670, by rfl⟩ : syracuseStep 858227 = 1287341) B1287341
theorem B1284227 : Blo 854356 1284227 := bstep (se 1 (by rfl) ⟨963170, by rfl⟩ : syracuseStep 1284227 = 1926341) B1926341
theorem B858243 : Blo 854356 858243 := bstep (se 1 (by rfl) ⟨643682, by rfl⟩ : syracuseStep 858243 = 1287365) B1287365
theorem B2168977 : Blo 854356 2168977 := bstep (se 2 (by rfl) ⟨813366, by rfl⟩ : syracuseStep 2168977 = 1626733) B1626733
theorem B858259 : Blo 854356 858259 := bstep (se 1 (by rfl) ⟨643694, by rfl⟩ : syracuseStep 858259 = 1287389) B1287389
theorem B1284257 : Blo 854356 1284257 := bstep (se 2 (by rfl) ⟨481596, by rfl⟩ : syracuseStep 1284257 = 963193) B963193
theorem B858275 : Blo 854356 858275 := bstep (se 1 (by rfl) ⟨643706, by rfl⟩ : syracuseStep 858275 = 1287413) B1287413
theorem B1284275 : Blo 854356 1284275 := bstep (se 1 (by rfl) ⟨963206, by rfl⟩ : syracuseStep 1284275 = 1926413) B1926413
theorem B858291 : Blo 854356 858291 := bstep (se 1 (by rfl) ⟨643718, by rfl⟩ : syracuseStep 858291 = 1287437) B1287437
theorem B1448131 : Blo 854356 1448131 := bstep (se 1 (by rfl) ⟨1086098, by rfl⟩ : syracuseStep 1448131 = 2172197) B2172197
theorem B858307 : Blo 854356 858307 := bstep (se 1 (by rfl) ⟨643730, by rfl⟩ : syracuseStep 858307 = 1287461) B1287461
theorem B1284305 : Blo 854356 1284305 := bstep (se 2 (by rfl) ⟨481614, by rfl⟩ : syracuseStep 1284305 = 963229) B963229
theorem B858323 : Blo 854356 858323 := bstep (se 1 (by rfl) ⟨643742, by rfl⟩ : syracuseStep 858323 = 1287485) B1287485
theorem B1284323 : Blo 854356 1284323 := bstep (se 1 (by rfl) ⟨963242, by rfl⟩ : syracuseStep 1284323 = 1926485) B1926485
theorem B858339 : Blo 854356 858339 := bstep (se 1 (by rfl) ⟨643754, by rfl⟩ : syracuseStep 858339 = 1287509) B1287509
theorem B5478641 : Blo 854356 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B858355 : Blo 854356 858355 := bstep (se 1 (by rfl) ⟨643766, by rfl⟩ : syracuseStep 858355 = 1287533) B1287533
theorem B1284353 : Blo 854356 1284353 := bstep (se 2 (by rfl) ⟨481632, by rfl⟩ : syracuseStep 1284353 = 963265) B963265
theorem B1284371 : Blo 854356 1284371 := bstep (se 1 (by rfl) ⟨963278, by rfl⟩ : syracuseStep 1284371 = 1926557) B1926557
theorem B1284401 : Blo 854356 1284401 := bstep (se 2 (by rfl) ⟨481650, by rfl⟩ : syracuseStep 1284401 = 963301) B963301
theorem B1218883 : Blo 854356 1218883 := bstep (se 1 (by rfl) ⟨914162, by rfl⟩ : syracuseStep 1218883 = 1828325) B1828325
theorem B1284419 : Blo 854356 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B1448273 : Blo 854356 1448273 := bstep (se 2 (by rfl) ⟨543102, by rfl⟩ : syracuseStep 1448273 = 1086205) B1086205
theorem B1546577 : Blo 854356 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B1284449 : Blo 854356 1284449 := bstep (se 2 (by rfl) ⟨481668, by rfl⟩ : syracuseStep 1284449 = 963337) B963337
theorem B1284467 : Blo 854356 1284467 := bstep (se 1 (by rfl) ⟨963350, by rfl⟩ : syracuseStep 1284467 = 1926701) B1926701
theorem B1284497 : Blo 854356 1284497 := bstep (se 2 (by rfl) ⟨481686, by rfl⟩ : syracuseStep 1284497 = 963373) B963373
theorem B1218979 : Blo 854356 1218979 := bstep (se 1 (by rfl) ⟨914234, by rfl⟩ : syracuseStep 1218979 = 1828469) B1828469
theorem B1284515 : Blo 854356 1284515 := bstep (se 1 (by rfl) ⟨963386, by rfl⟩ : syracuseStep 1284515 = 1926773) B1926773
theorem B2169251 : Blo 854356 2169251 := bstep (se 1 (by rfl) ⟨1626938, by rfl⟩ : syracuseStep 2169251 = 3253877) B3253877
theorem B1284545 : Blo 854356 1284545 := bstep (se 2 (by rfl) ⟨481704, by rfl⟩ : syracuseStep 1284545 = 963409) B963409
theorem B1448401 : Blo 854356 1448401 := bstep (se 2 (by rfl) ⟨543150, by rfl⟩ : syracuseStep 1448401 = 1086301) B1086301
theorem B1284563 : Blo 854356 1284563 := bstep (se 1 (by rfl) ⟨963422, by rfl⟩ : syracuseStep 1284563 = 1926845) B1926845
theorem B1284593 : Blo 854356 1284593 := bstep (se 2 (by rfl) ⟨481722, by rfl⟩ : syracuseStep 1284593 = 963445) B963445
theorem B1448435 : Blo 854356 1448435 := bstep (se 1 (by rfl) ⟨1086326, by rfl⟩ : syracuseStep 1448435 = 2172653) B2172653
theorem B1284611 : Blo 854356 1284611 := bstep (se 1 (by rfl) ⟨963458, by rfl⟩ : syracuseStep 1284611 = 1926917) B1926917
theorem B1284641 : Blo 854356 1284641 := bstep (se 2 (by rfl) ⟨481740, by rfl⟩ : syracuseStep 1284641 = 963481) B963481
theorem B1284659 : Blo 854356 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B1284689 : Blo 854356 1284689 := bstep (se 2 (by rfl) ⟨481758, by rfl⟩ : syracuseStep 1284689 = 963517) B963517
theorem B1284707 : Blo 854356 1284707 := bstep (se 1 (by rfl) ⟨963530, by rfl⟩ : syracuseStep 1284707 = 1927061) B1927061
theorem B2169443 : Blo 854356 2169443 := bstep (se 1 (by rfl) ⟨1627082, by rfl⟩ : syracuseStep 2169443 = 3254165) B3254165
theorem B2890349 : Blo 854356 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B1284737 : Blo 854356 1284737 := bstep (se 2 (by rfl) ⟨481776, by rfl⟩ : syracuseStep 1284737 = 963553) B963553
theorem B1284755 : Blo 854356 1284755 := bstep (se 1 (by rfl) ⟨963566, by rfl⟩ : syracuseStep 1284755 = 1927133) B1927133
theorem B2890403 : Blo 854356 2890403 := bstep (se 1 (by rfl) ⟨2167802, by rfl⟩ : syracuseStep 2890403 = 4335605) B4335605
theorem B1284785 : Blo 854356 1284785 := bstep (se 2 (by rfl) ⟨481794, by rfl⟩ : syracuseStep 1284785 = 963589) B963589
theorem B1284803 : Blo 854356 1284803 := bstep (se 1 (by rfl) ⟨963602, by rfl⟩ : syracuseStep 1284803 = 1927205) B1927205
theorem B1284833 : Blo 854356 1284833 := bstep (se 2 (by rfl) ⟨481812, by rfl⟩ : syracuseStep 1284833 = 963625) B963625
theorem B1284851 : Blo 854356 1284851 := bstep (se 1 (by rfl) ⟨963638, by rfl⟩ : syracuseStep 1284851 = 1927277) B1927277
theorem B1284881 : Blo 854356 1284881 := bstep (se 2 (by rfl) ⟨481830, by rfl⟩ : syracuseStep 1284881 = 963661) B963661
theorem B1284899 : Blo 854356 1284899 := bstep (se 1 (by rfl) ⟨963674, by rfl⟩ : syracuseStep 1284899 = 1927349) B1927349
theorem B1284929 : Blo 854356 1284929 := bstep (se 2 (by rfl) ⟨481848, by rfl⟩ : syracuseStep 1284929 = 963697) B963697
theorem B4332365 : Blo 854356 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B1284947 : Blo 854356 1284947 := bstep (se 1 (by rfl) ⟨963710, by rfl⟩ : syracuseStep 1284947 = 1927421) B1927421
theorem B1284977 : Blo 854356 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B1284995 : Blo 854356 1284995 := bstep (se 1 (by rfl) ⟨963746, by rfl⟩ : syracuseStep 1284995 = 1927493) B1927493
theorem B1219475 : Blo 854356 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B1285025 : Blo 854356 1285025 := bstep (se 2 (by rfl) ⟨481884, by rfl⟩ : syracuseStep 1285025 = 963769) B963769
theorem B2890673 : Blo 854356 2890673 := bstep (se 2 (by rfl) ⟨1084002, by rfl⟩ : syracuseStep 2890673 = 2168005) B2168005
theorem B1285043 : Blo 854356 1285043 := bstep (se 1 (by rfl) ⟨963782, by rfl⟩ : syracuseStep 1285043 = 1927565) B1927565
theorem B1285073 : Blo 854356 1285073 := bstep (se 2 (by rfl) ⟨481902, by rfl⟩ : syracuseStep 1285073 = 963805) B963805
theorem B1285091 : Blo 854356 1285091 := bstep (se 1 (by rfl) ⟨963818, by rfl⟩ : syracuseStep 1285091 = 1927637) B1927637
theorem B1285121 : Blo 854356 1285121 := bstep (se 2 (by rfl) ⟨481920, by rfl⟩ : syracuseStep 1285121 = 963841) B963841
theorem B1285139 : Blo 854356 1285139 := bstep (se 1 (by rfl) ⟨963854, by rfl⟩ : syracuseStep 1285139 = 1927709) B1927709
theorem B3251249 : Blo 854356 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B1285169 : Blo 854356 1285169 := bstep (se 2 (by rfl) ⟨481938, by rfl⟩ : syracuseStep 1285169 = 963877) B963877
theorem B1285187 : Blo 854356 1285187 := bstep (se 1 (by rfl) ⟨963890, by rfl⟩ : syracuseStep 1285187 = 1927781) B1927781
theorem B1285217 : Blo 854356 1285217 := bstep (se 2 (by rfl) ⟨481956, by rfl⟩ : syracuseStep 1285217 = 963913) B963913
theorem B1285235 : Blo 854356 1285235 := bstep (se 1 (by rfl) ⟨963926, by rfl⟩ : syracuseStep 1285235 = 1927853) B1927853
theorem B1285265 : Blo 854356 1285265 := bstep (se 2 (by rfl) ⟨481974, by rfl⟩ : syracuseStep 1285265 = 963949) B963949
theorem B1285283 : Blo 854356 1285283 := bstep (se 1 (by rfl) ⟨963962, by rfl⟩ : syracuseStep 1285283 = 1927925) B1927925
theorem B1285313 : Blo 854356 1285313 := bstep (se 2 (by rfl) ⟨481992, by rfl⟩ : syracuseStep 1285313 = 963985) B963985
theorem B1285331 : Blo 854356 1285331 := bstep (se 1 (by rfl) ⟨963998, by rfl⟩ : syracuseStep 1285331 = 1927997) B1927997
theorem B1285361 : Blo 854356 1285361 := bstep (se 2 (by rfl) ⟨482010, by rfl⟩ : syracuseStep 1285361 = 964021) B964021
theorem B1285379 : Blo 854356 1285379 := bstep (se 1 (by rfl) ⟨964034, by rfl⟩ : syracuseStep 1285379 = 1928069) B1928069
theorem B10951949 : Blo 854356 10951949 := bstep (se 3 (by rfl) ⟨2053490, by rfl⟩ : syracuseStep 10951949 = 4106981) B4106981
theorem B1285409 : Blo 854356 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B1285427 : Blo 854356 1285427 := bstep (se 1 (by rfl) ⟨964070, by rfl⟩ : syracuseStep 1285427 = 1928141) B1928141
theorem B23469365 : Blo 854356 23469365 := bstep (se 5 (by rfl) ⟨1100126, by rfl⟩ : syracuseStep 23469365 = 2200253) B2200253
theorem B3906893 : Blo 854356 3906893 := bstep (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) B1465085
theorem B1285457 : Blo 854356 1285457 := bstep (se 2 (by rfl) ⟨482046, by rfl⟩ : syracuseStep 1285457 = 964093) B964093
theorem B1285475 : Blo 854356 1285475 := bstep (se 1 (by rfl) ⟨964106, by rfl⟩ : syracuseStep 1285475 = 1928213) B1928213
theorem B1285505 : Blo 854356 1285505 := bstep (se 2 (by rfl) ⟨482064, by rfl⟩ : syracuseStep 1285505 = 964129) B964129
theorem B1285523 : Blo 854356 1285523 := bstep (se 1 (by rfl) ⟨964142, by rfl⟩ : syracuseStep 1285523 = 1928285) B1928285
theorem B1285553 : Blo 854356 1285553 := bstep (se 2 (by rfl) ⟨482082, by rfl⟩ : syracuseStep 1285553 = 964165) B964165
theorem B1285571 : Blo 854356 1285571 := bstep (se 1 (by rfl) ⟨964178, by rfl⟩ : syracuseStep 1285571 = 1928357) B1928357
theorem B57187781 : Blo 854356 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B2891213 : Blo 854356 2891213 := bstep (se 3 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 2891213 = 1084205) B1084205
theorem B1285601 : Blo 854356 1285601 := bstep (se 2 (by rfl) ⟨482100, by rfl⟩ : syracuseStep 1285601 = 964201) B964201
theorem B1285619 : Blo 854356 1285619 := bstep (se 1 (by rfl) ⟨964214, by rfl⟩ : syracuseStep 1285619 = 1928429) B1928429
theorem B2891267 : Blo 854356 2891267 := bstep (se 1 (by rfl) ⟨2168450, by rfl⟩ : syracuseStep 2891267 = 4336901) B4336901
theorem B1220113 : Blo 854356 1220113 := bstep (se 2 (by rfl) ⟨457542, by rfl⟩ : syracuseStep 1220113 = 915085) B915085
theorem B1285649 : Blo 854356 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B2170385 : Blo 854356 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B1285667 : Blo 854356 1285667 := bstep (se 1 (by rfl) ⟨964250, by rfl⟩ : syracuseStep 1285667 = 1928501) B1928501
theorem B1285697 : Blo 854356 1285697 := bstep (se 2 (by rfl) ⟨482136, by rfl⟩ : syracuseStep 1285697 = 964273) B964273
theorem B2170435 : Blo 854356 2170435 := bstep (se 1 (by rfl) ⟨1627826, by rfl⟩ : syracuseStep 2170435 = 3255653) B3255653
theorem B1285715 : Blo 854356 1285715 := bstep (se 1 (by rfl) ⟨964286, by rfl⟩ : syracuseStep 1285715 = 1928573) B1928573
theorem B1285745 : Blo 854356 1285745 := bstep (se 2 (by rfl) ⟨482154, by rfl⟩ : syracuseStep 1285745 = 964309) B964309
theorem B1285763 : Blo 854356 1285763 := bstep (se 1 (by rfl) ⟨964322, by rfl⟩ : syracuseStep 1285763 = 1928645) B1928645
theorem B1285793 : Blo 854356 1285793 := bstep (se 2 (by rfl) ⟨482172, by rfl⟩ : syracuseStep 1285793 = 964345) B964345
theorem B1285811 : Blo 854356 1285811 := bstep (se 1 (by rfl) ⟨964358, by rfl⟩ : syracuseStep 1285811 = 1928717) B1928717
theorem B1285841 : Blo 854356 1285841 := bstep (se 2 (by rfl) ⟨482190, by rfl⟩ : syracuseStep 1285841 = 964381) B964381
theorem B2170577 : Blo 854356 2170577 := bstep (se 2 (by rfl) ⟨813966, by rfl⟩ : syracuseStep 2170577 = 1627933) B1627933
theorem B1285859 : Blo 854356 1285859 := bstep (se 1 (by rfl) ⟨964394, by rfl⟩ : syracuseStep 1285859 = 1928789) B1928789
theorem B1285889 : Blo 854356 1285889 := bstep (se 2 (by rfl) ⟨482208, by rfl⟩ : syracuseStep 1285889 = 964417) B964417
theorem B2891537 : Blo 854356 2891537 := bstep (se 2 (by rfl) ⟨1084326, by rfl⟩ : syracuseStep 2891537 = 2168653) B2168653
theorem B1285907 : Blo 854356 1285907 := bstep (se 1 (by rfl) ⟨964430, by rfl⟩ : syracuseStep 1285907 = 1928861) B1928861
theorem B1285937 : Blo 854356 1285937 := bstep (se 2 (by rfl) ⟨482226, by rfl⟩ : syracuseStep 1285937 = 964453) B964453
theorem B1285955 : Blo 854356 1285955 := bstep (se 1 (by rfl) ⟨964466, by rfl⟩ : syracuseStep 1285955 = 1928933) B1928933
theorem B1220449 : Blo 854356 1220449 := bstep (se 2 (by rfl) ⟨457668, by rfl⟩ : syracuseStep 1220449 = 915337) B915337
theorem B1285985 : Blo 854356 1285985 := bstep (se 2 (by rfl) ⟨482244, by rfl⟩ : syracuseStep 1285985 = 964489) B964489
theorem B6168433 : Blo 854356 6168433 := bstep (se 2 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 6168433 = 4626325) B4626325
theorem B1286003 : Blo 854356 1286003 := bstep (se 1 (by rfl) ⟨964502, by rfl⟩ : syracuseStep 1286003 = 1929005) B1929005
theorem B1286033 : Blo 854356 1286033 := bstep (se 2 (by rfl) ⟨482262, by rfl⟩ : syracuseStep 1286033 = 964525) B964525
theorem B1286051 : Blo 854356 1286051 := bstep (se 1 (by rfl) ⟨964538, by rfl⟩ : syracuseStep 1286051 = 1929077) B1929077
theorem B1286081 : Blo 854356 1286081 := bstep (se 2 (by rfl) ⟨482280, by rfl⟩ : syracuseStep 1286081 = 964561) B964561
theorem B1286099 : Blo 854356 1286099 := bstep (se 1 (by rfl) ⟨964574, by rfl⟩ : syracuseStep 1286099 = 1929149) B1929149
theorem B1286129 : Blo 854356 1286129 := bstep (se 2 (by rfl) ⟨482298, by rfl⟩ : syracuseStep 1286129 = 964597) B964597
theorem B1286147 : Blo 854356 1286147 := bstep (se 1 (by rfl) ⟨964610, by rfl⟩ : syracuseStep 1286147 = 1929221) B1929221
theorem B1286177 : Blo 854356 1286177 := bstep (se 2 (by rfl) ⟨482316, by rfl⟩ : syracuseStep 1286177 = 964633) B964633
theorem B1286195 : Blo 854356 1286195 := bstep (se 1 (by rfl) ⟨964646, by rfl⟩ : syracuseStep 1286195 = 1929293) B1929293
theorem B1286225 : Blo 854356 1286225 := bstep (se 2 (by rfl) ⟨482334, by rfl⟩ : syracuseStep 1286225 = 964669) B964669
theorem B1286243 : Blo 854356 1286243 := bstep (se 1 (by rfl) ⟨964682, by rfl⟩ : syracuseStep 1286243 = 1929365) B1929365
theorem B1286273 : Blo 854356 1286273 := bstep (se 2 (by rfl) ⟨482352, by rfl⟩ : syracuseStep 1286273 = 964705) B964705
theorem B1286291 : Blo 854356 1286291 := bstep (se 1 (by rfl) ⟨964718, by rfl⟩ : syracuseStep 1286291 = 1929437) B1929437
theorem B1286321 : Blo 854356 1286321 := bstep (se 2 (by rfl) ⟨482370, by rfl⟩ : syracuseStep 1286321 = 964741) B964741
theorem B1286339 : Blo 854356 1286339 := bstep (se 1 (by rfl) ⟨964754, by rfl⟩ : syracuseStep 1286339 = 1929509) B1929509
theorem B1286369 : Blo 854356 1286369 := bstep (se 2 (by rfl) ⟨482388, by rfl⟩ : syracuseStep 1286369 = 964777) B964777
theorem B3711203 : Blo 854356 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B1286387 : Blo 854356 1286387 := bstep (se 1 (by rfl) ⟨964790, by rfl⟩ : syracuseStep 1286387 = 1929581) B1929581
theorem B1286417 : Blo 854356 1286417 := bstep (se 2 (by rfl) ⟨482406, by rfl⟩ : syracuseStep 1286417 = 964813) B964813
theorem B1286435 : Blo 854356 1286435 := bstep (se 1 (by rfl) ⟨964826, by rfl⟩ : syracuseStep 1286435 = 1929653) B1929653
theorem B2892077 : Blo 854356 2892077 := bstep (se 3 (by rfl) ⟨542264, by rfl⟩ : syracuseStep 2892077 = 1084529) B1084529
theorem B1286465 : Blo 854356 1286465 := bstep (se 2 (by rfl) ⟨482424, by rfl⟩ : syracuseStep 1286465 = 964849) B964849
theorem B1286483 : Blo 854356 1286483 := bstep (se 1 (by rfl) ⟨964862, by rfl⟩ : syracuseStep 1286483 = 1929725) B1929725
theorem B2892131 : Blo 854356 2892131 := bstep (se 1 (by rfl) ⟨2169098, by rfl⟩ : syracuseStep 2892131 = 4338197) B4338197
theorem B1286513 : Blo 854356 1286513 := bstep (se 2 (by rfl) ⟨482442, by rfl⟩ : syracuseStep 1286513 = 964885) B964885
theorem B1286531 : Blo 854356 1286531 := bstep (se 1 (by rfl) ⟨964898, by rfl⟩ : syracuseStep 1286531 = 1929797) B1929797
theorem B1286561 : Blo 854356 1286561 := bstep (se 2 (by rfl) ⟨482460, by rfl⟩ : syracuseStep 1286561 = 964921) B964921
theorem B1221041 : Blo 854356 1221041 := bstep (se 2 (by rfl) ⟨457890, by rfl⟩ : syracuseStep 1221041 = 915781) B915781
theorem B1286579 : Blo 854356 1286579 := bstep (se 1 (by rfl) ⟨964934, by rfl⟩ : syracuseStep 1286579 = 1929869) B1929869
theorem B1286609 : Blo 854356 1286609 := bstep (se 2 (by rfl) ⟨482478, by rfl⟩ : syracuseStep 1286609 = 964957) B964957
theorem B3252707 : Blo 854356 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B1286627 : Blo 854356 1286627 := bstep (se 1 (by rfl) ⟨964970, by rfl⟩ : syracuseStep 1286627 = 1929941) B1929941
theorem B1286657 : Blo 854356 1286657 := bstep (se 2 (by rfl) ⟨482496, by rfl⟩ : syracuseStep 1286657 = 964993) B964993
theorem B2433539 : Blo 854356 2433539 := bstep (se 1 (by rfl) ⟨1825154, by rfl⟩ : syracuseStep 2433539 = 3650309) B3650309
theorem B1286675 : Blo 854356 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B1286705 : Blo 854356 1286705 := bstep (se 2 (by rfl) ⟨482514, by rfl⟩ : syracuseStep 1286705 = 965029) B965029
theorem B1286723 : Blo 854356 1286723 := bstep (se 1 (by rfl) ⟨965042, by rfl⟩ : syracuseStep 1286723 = 1930085) B1930085
theorem B1286753 : Blo 854356 1286753 := bstep (se 2 (by rfl) ⟨482532, by rfl⟩ : syracuseStep 1286753 = 965065) B965065
theorem B2892401 : Blo 854356 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B1286771 : Blo 854356 1286771 := bstep (se 1 (by rfl) ⟨965078, by rfl⟩ : syracuseStep 1286771 = 1930157) B1930157
theorem B5481101 : Blo 854356 5481101 := bstep (se 3 (by rfl) ⟨1027706, by rfl⟩ : syracuseStep 5481101 = 2055413) B2055413
theorem B1286801 : Blo 854356 1286801 := bstep (se 2 (by rfl) ⟨482550, by rfl⟩ : syracuseStep 1286801 = 965101) B965101
theorem B1286819 : Blo 854356 1286819 := bstep (se 1 (by rfl) ⟨965114, by rfl⟩ : syracuseStep 1286819 = 1930229) B1930229
theorem B2171569 : Blo 854356 2171569 := bstep (se 2 (by rfl) ⟨814338, by rfl⟩ : syracuseStep 2171569 = 1628677) B1628677
theorem B1286849 : Blo 854356 1286849 := bstep (se 2 (by rfl) ⟨482568, by rfl⟩ : syracuseStep 1286849 = 965137) B965137
theorem B1286867 : Blo 854356 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B1286897 : Blo 854356 1286897 := bstep (se 2 (by rfl) ⟨482586, by rfl⟩ : syracuseStep 1286897 = 965173) B965173
theorem B1286915 : Blo 854356 1286915 := bstep (se 1 (by rfl) ⟨965186, by rfl⟩ : syracuseStep 1286915 = 1930373) B1930373
theorem B1286945 : Blo 854356 1286945 := bstep (se 2 (by rfl) ⟨482604, by rfl⟩ : syracuseStep 1286945 = 965209) B965209
theorem B1286963 : Blo 854356 1286963 := bstep (se 1 (by rfl) ⟨965222, by rfl⟩ : syracuseStep 1286963 = 1930445) B1930445
theorem B1286993 : Blo 854356 1286993 := bstep (se 2 (by rfl) ⟨482622, by rfl⟩ : syracuseStep 1286993 = 965245) B965245
theorem B1287011 : Blo 854356 1287011 := bstep (se 1 (by rfl) ⟨965258, by rfl⟩ : syracuseStep 1287011 = 1930517) B1930517
theorem B1287041 : Blo 854356 1287041 := bstep (se 2 (by rfl) ⟨482640, by rfl⟩ : syracuseStep 1287041 = 965281) B965281
theorem B1287059 : Blo 854356 1287059 := bstep (se 1 (by rfl) ⟨965294, by rfl⟩ : syracuseStep 1287059 = 1930589) B1930589
theorem B1287089 : Blo 854356 1287089 := bstep (se 2 (by rfl) ⟨482658, by rfl⟩ : syracuseStep 1287089 = 965317) B965317
theorem B1221571 : Blo 854356 1221571 := bstep (se 1 (by rfl) ⟨916178, by rfl⟩ : syracuseStep 1221571 = 1832357) B1832357
theorem B2171843 : Blo 854356 2171843 := bstep (se 1 (by rfl) ⟨1628882, by rfl⟩ : syracuseStep 2171843 = 3257765) B3257765
theorem B1287107 : Blo 854356 1287107 := bstep (se 1 (by rfl) ⟨965330, by rfl⟩ : syracuseStep 1287107 = 1930661) B1930661
theorem B1287137 : Blo 854356 1287137 := bstep (se 2 (by rfl) ⟨482676, by rfl⟩ : syracuseStep 1287137 = 965353) B965353
theorem B1287155 : Blo 854356 1287155 := bstep (se 1 (by rfl) ⟨965366, by rfl⟩ : syracuseStep 1287155 = 1930733) B1930733
theorem B2925571 : Blo 854356 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B1287185 : Blo 854356 1287185 := bstep (se 2 (by rfl) ⟨482694, by rfl⟩ : syracuseStep 1287185 = 965389) B965389
theorem B1287203 : Blo 854356 1287203 := bstep (se 1 (by rfl) ⟨965402, by rfl⟩ : syracuseStep 1287203 = 1930805) B1930805
theorem B1287233 : Blo 854356 1287233 := bstep (se 2 (by rfl) ⟨482712, by rfl⟩ : syracuseStep 1287233 = 965425) B965425
theorem B1287251 : Blo 854356 1287251 := bstep (se 1 (by rfl) ⟨965438, by rfl⟩ : syracuseStep 1287251 = 1930877) B1930877
theorem B1287281 : Blo 854356 1287281 := bstep (se 2 (by rfl) ⟨482730, by rfl⟩ : syracuseStep 1287281 = 965461) B965461
theorem B2172035 : Blo 854356 2172035 := bstep (se 1 (by rfl) ⟨1629026, by rfl⟩ : syracuseStep 2172035 = 3258053) B3258053
theorem B1287299 : Blo 854356 1287299 := bstep (se 1 (by rfl) ⟨965474, by rfl⟩ : syracuseStep 1287299 = 1930949) B1930949
theorem B2892941 : Blo 854356 2892941 := bstep (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) B1084853
theorem B1287329 : Blo 854356 1287329 := bstep (se 2 (by rfl) ⟨482748, by rfl⟩ : syracuseStep 1287329 = 965497) B965497
theorem B1287347 : Blo 854356 1287347 := bstep (se 1 (by rfl) ⟨965510, by rfl⟩ : syracuseStep 1287347 = 1931021) B1931021
theorem B2892995 : Blo 854356 2892995 := bstep (se 1 (by rfl) ⟨2169746, by rfl⟩ : syracuseStep 2892995 = 4339493) B4339493
theorem B1287377 : Blo 854356 1287377 := bstep (se 2 (by rfl) ⟨482766, by rfl⟩ : syracuseStep 1287377 = 965533) B965533
theorem B1287395 : Blo 854356 1287395 := bstep (se 1 (by rfl) ⟨965546, by rfl⟩ : syracuseStep 1287395 = 1931093) B1931093
theorem B2467057 : Blo 854356 2467057 := bstep (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) B1850293
theorem B1287425 : Blo 854356 1287425 := bstep (se 2 (by rfl) ⟨482784, by rfl⟩ : syracuseStep 1287425 = 965569) B965569
theorem B1221907 : Blo 854356 1221907 := bstep (se 1 (by rfl) ⟨916430, by rfl⟩ : syracuseStep 1221907 = 1832861) B1832861
theorem B1287443 : Blo 854356 1287443 := bstep (se 1 (by rfl) ⟨965582, by rfl⟩ : syracuseStep 1287443 = 1931165) B1931165
theorem B1287473 : Blo 854356 1287473 := bstep (se 2 (by rfl) ⟨482802, by rfl⟩ : syracuseStep 1287473 = 965605) B965605
theorem B1287491 : Blo 854356 1287491 := bstep (se 1 (by rfl) ⟨965618, by rfl⟩ : syracuseStep 1287491 = 1931237) B1931237
theorem B1287521 : Blo 854356 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B3253709 : Blo 854356 3253709 := bstep (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) B1220141
theorem B2893265 : Blo 854356 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B1156771 : Blo 854356 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B4695715 : Blo 854356 4695715 := bstep (se 1 (by rfl) ⟨3521786, by rfl⟩ : syracuseStep 4695715 = 7043573) B7043573
theorem B4335281 : Blo 854356 4335281 := bstep (se 2 (by rfl) ⟨1625730, by rfl⟩ : syracuseStep 4335281 = 3251461) B3251461
theorem B2434769 : Blo 854356 2434769 := bstep (se 2 (by rfl) ⟨913038, by rfl⟩ : syracuseStep 2434769 = 1826077) B1826077
theorem B8234723 : Blo 854356 8234723 := bstep (se 1 (by rfl) ⟨6176042, by rfl⟩ : syracuseStep 8234723 = 12352085) B12352085
theorem B2893805 : Blo 854356 2893805 := bstep (se 3 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 2893805 = 1085177) B1085177
theorem B2893859 : Blo 854356 2893859 := bstep (se 1 (by rfl) ⟨2170394, by rfl⟩ : syracuseStep 2893859 = 4340789) B4340789
theorem B1484867 : Blo 854356 1484867 := bstep (se 1 (by rfl) ⟨1113650, by rfl⟩ : syracuseStep 1484867 = 2227301) B2227301
theorem B2894129 : Blo 854356 2894129 := bstep (se 2 (by rfl) ⟨1085298, by rfl⟩ : syracuseStep 2894129 = 2170597) B2170597
theorem B1157809 : Blo 854356 1157809 := bstep (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) B868357
theorem B20064995 : Blo 854356 20064995 := bstep (se 1 (by rfl) ⟨15048746, by rfl⟩ : syracuseStep 20064995 = 30097493) B30097493
theorem B961267 : Blo 854356 961267 := bstep (se 1 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 961267 = 1441901) B1441901
theorem B2894669 : Blo 854356 2894669 := bstep (se 3 (by rfl) ⟨542750, by rfl⟩ : syracuseStep 2894669 = 1085501) B1085501
theorem B1026899 : Blo 854356 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B961411 : Blo 854356 961411 := bstep (se 1 (by rfl) ⟨721058, by rfl⟩ : syracuseStep 961411 = 1442117) B1442117
theorem B2894723 : Blo 854356 2894723 := bstep (se 1 (by rfl) ⟨2171042, by rfl⟩ : syracuseStep 2894723 = 4342085) B4342085
theorem B961555 : Blo 854356 961555 := bstep (se 1 (by rfl) ⟨721166, by rfl⟩ : syracuseStep 961555 = 1442333) B1442333
theorem B4336739 : Blo 854356 4336739 := bstep (se 1 (by rfl) ⟨3252554, by rfl⟩ : syracuseStep 4336739 = 6505109) B6505109
theorem B2436227 : Blo 854356 2436227 := bstep (se 1 (by rfl) ⟨1827170, by rfl⟩ : syracuseStep 2436227 = 3654341) B3654341
theorem B1158289 : Blo 854356 1158289 := bstep (se 2 (by rfl) ⟨434358, by rfl⟩ : syracuseStep 1158289 = 868717) B868717
theorem B2894993 : Blo 854356 2894993 := bstep (se 2 (by rfl) ⟨1085622, by rfl⟩ : syracuseStep 2894993 = 2171245) B2171245
theorem B961699 : Blo 854356 961699 := bstep (se 1 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 961699 = 1442549) B1442549
theorem B1387777 : Blo 854356 1387777 := bstep (se 2 (by rfl) ⟨520416, by rfl⟩ : syracuseStep 1387777 = 1040833) B1040833
theorem B1158419 : Blo 854356 1158419 := bstep (se 1 (by rfl) ⟨868814, by rfl⟩ : syracuseStep 1158419 = 1737629) B1737629
theorem B961843 : Blo 854356 961843 := bstep (se 1 (by rfl) ⟨721382, by rfl⟩ : syracuseStep 961843 = 1442765) B1442765
theorem B961987 : Blo 854356 961987 := bstep (se 1 (by rfl) ⟨721490, by rfl⟩ : syracuseStep 961987 = 1442981) B1442981
theorem B9743813 : Blo 854356 9743813 := bstep (se 4 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 9743813 = 1826965) B1826965
theorem B3255821 : Blo 854356 3255821 := bstep (se 3 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 3255821 = 1220933) B1220933
theorem B962131 : Blo 854356 962131 := bstep (se 1 (by rfl) ⟨721598, by rfl⟩ : syracuseStep 962131 = 1443197) B1443197
theorem B2895533 : Blo 854356 2895533 := bstep (se 3 (by rfl) ⟨542912, by rfl⟩ : syracuseStep 2895533 = 1085825) B1085825
theorem B7417541 : Blo 854356 7417541 := bstep (se 4 (by rfl) ⟨695394, by rfl⟩ : syracuseStep 7417541 = 1390789) B1390789
theorem B962275 : Blo 854356 962275 := bstep (se 1 (by rfl) ⟨721706, by rfl⟩ : syracuseStep 962275 = 1443413) B1443413
theorem B2895587 : Blo 854356 2895587 := bstep (se 1 (by rfl) ⟨2171690, by rfl⟩ : syracuseStep 2895587 = 4343381) B4343381
theorem B962419 : Blo 854356 962419 := bstep (se 1 (by rfl) ⟨721814, by rfl⟩ : syracuseStep 962419 = 1443629) B1443629
theorem B4337549 : Blo 854356 4337549 := bstep (se 3 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 4337549 = 1626581) B1626581
theorem B2437037 : Blo 854356 2437037 := bstep (se 3 (by rfl) ⟨456944, by rfl⟩ : syracuseStep 2437037 = 913889) B913889
theorem B1388465 : Blo 854356 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B2895857 : Blo 854356 2895857 := bstep (se 2 (by rfl) ⟨1085946, by rfl⟩ : syracuseStep 2895857 = 2171893) B2171893
theorem B962563 : Blo 854356 962563 := bstep (se 1 (by rfl) ⟨721922, by rfl⟩ : syracuseStep 962563 = 1443845) B1443845
theorem B3092579 : Blo 854356 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B2437229 : Blo 854356 2437229 := bstep (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) B913961
theorem B6697073 : Blo 854356 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B962707 : Blo 854356 962707 := bstep (se 1 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 962707 = 1444061) B1444061
theorem B962851 : Blo 854356 962851 := bstep (se 1 (by rfl) ⟨722138, by rfl⟩ : syracuseStep 962851 = 1444277) B1444277
theorem B3256625 : Blo 854356 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B962995 : Blo 854356 962995 := bstep (se 1 (by rfl) ⟨722246, by rfl⟩ : syracuseStep 962995 = 1444493) B1444493
theorem B2896397 : Blo 854356 2896397 := bstep (se 3 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 2896397 = 1086149) B1086149
theorem B963139 : Blo 854356 963139 := bstep (se 1 (by rfl) ⟨722354, by rfl⟩ : syracuseStep 963139 = 1444709) B1444709
theorem B2896451 : Blo 854356 2896451 := bstep (se 1 (by rfl) ⟨2172338, by rfl⟩ : syracuseStep 2896451 = 4344677) B4344677
theorem B4108963 : Blo 854356 4108963 := bstep (se 1 (by rfl) ⟨3081722, by rfl⟩ : syracuseStep 4108963 = 6163445) B6163445
theorem B1028803 : Blo 854356 1028803 := bstep (se 1 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 1028803 = 1543205) B1543205
theorem B963283 : Blo 854356 963283 := bstep (se 1 (by rfl) ⟨722462, by rfl⟩ : syracuseStep 963283 = 1444925) B1444925
theorem B2896721 : Blo 854356 2896721 := bstep (se 2 (by rfl) ⟨1086270, by rfl⟩ : syracuseStep 2896721 = 2172541) B2172541
theorem B963427 : Blo 854356 963427 := bstep (se 1 (by rfl) ⟨722570, by rfl⟩ : syracuseStep 963427 = 1445141) B1445141
theorem B3257293 : Blo 854356 3257293 := bstep (se 3 (by rfl) ⟨610742, by rfl⟩ : syracuseStep 3257293 = 1221485) B1221485
theorem B1029091 : Blo 854356 1029091 := bstep (se 1 (by rfl) ⟨771818, by rfl⟩ : syracuseStep 1029091 = 1543637) B1543637
theorem B963571 : Blo 854356 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B1029187 : Blo 854356 1029187 := bstep (se 1 (by rfl) ⟨771890, by rfl⟩ : syracuseStep 1029187 = 1543781) B1543781
theorem B2438221 : Blo 854356 2438221 := bstep (se 3 (by rfl) ⟨457166, by rfl⟩ : syracuseStep 2438221 = 914333) B914333
theorem B963715 : Blo 854356 963715 := bstep (se 1 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 963715 = 1445573) B1445573
theorem B1029331 : Blo 854356 1029331 := bstep (se 1 (by rfl) ⟨771998, by rfl⟩ : syracuseStep 1029331 = 1543997) B1543997
theorem B23442659 : Blo 854356 23442659 := bstep (se 1 (by rfl) ⟨17581994, by rfl⟩ : syracuseStep 23442659 = 35163989) B35163989
theorem B12367075 : Blo 854356 12367075 := bstep (se 1 (by rfl) ⟨9275306, by rfl⟩ : syracuseStep 12367075 = 18550613) B18550613
theorem B963859 : Blo 854356 963859 := bstep (se 1 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 963859 = 1445789) B1445789
theorem B964003 : Blo 854356 964003 := bstep (se 1 (by rfl) ⟨723002, by rfl⟩ : syracuseStep 964003 = 1446005) B1446005
theorem B3650993 : Blo 854356 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B964147 : Blo 854356 964147 := bstep (se 1 (by rfl) ⟨723110, by rfl⟩ : syracuseStep 964147 = 1446221) B1446221
theorem B964291 : Blo 854356 964291 := bstep (se 1 (by rfl) ⟨723218, by rfl⟩ : syracuseStep 964291 = 1446437) B1446437
theorem B3258083 : Blo 854356 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B2963267 : Blo 854356 2963267 := bstep (se 1 (by rfl) ⟨2222450, by rfl⟩ : syracuseStep 2963267 = 4444901) B4444901
theorem B964435 : Blo 854356 964435 := bstep (se 1 (by rfl) ⟨723326, by rfl⟩ : syracuseStep 964435 = 1446653) B1446653
theorem B4110193 : Blo 854356 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B964579 : Blo 854356 964579 := bstep (se 1 (by rfl) ⟨723434, by rfl⟩ : syracuseStep 964579 = 1446869) B1446869
theorem B9254897 : Blo 854356 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B2504753 : Blo 854356 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B964723 : Blo 854356 964723 := bstep (se 1 (by rfl) ⟨723542, by rfl⟩ : syracuseStep 964723 = 1447085) B1447085
theorem B964867 : Blo 854356 964867 := bstep (se 1 (by rfl) ⟨723650, by rfl⟩ : syracuseStep 964867 = 1447301) B1447301
theorem B3258737 : Blo 854356 3258737 := bstep (se 2 (by rfl) ⟨1222026, by rfl⟩ : syracuseStep 3258737 = 2444053) B2444053
theorem B965011 : Blo 854356 965011 := bstep (se 1 (by rfl) ⟨723758, by rfl⟩ : syracuseStep 965011 = 1447517) B1447517
theorem B3914189 : Blo 854356 3914189 := bstep (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) B1467821
theorem B965155 : Blo 854356 965155 := bstep (se 1 (by rfl) ⟨723866, by rfl⟩ : syracuseStep 965155 = 1447733) B1447733
theorem B965299 : Blo 854356 965299 := bstep (se 1 (by rfl) ⟨723974, by rfl⟩ : syracuseStep 965299 = 1447949) B1447949
theorem B4340465 : Blo 854356 4340465 := bstep (se 2 (by rfl) ⟨1627674, by rfl⟩ : syracuseStep 4340465 = 3255349) B3255349
theorem B2439953 : Blo 854356 2439953 := bstep (se 2 (by rfl) ⟨914982, by rfl⟩ : syracuseStep 2439953 = 1829965) B1829965
theorem B965443 : Blo 854356 965443 := bstep (se 1 (by rfl) ⟨724082, by rfl⟩ : syracuseStep 965443 = 1448165) B1448165
theorem B8240069 : Blo 854356 8240069 := bstep (se 4 (by rfl) ⟨772506, by rfl⟩ : syracuseStep 8240069 = 1545013) B1545013
theorem B2440145 : Blo 854356 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B965587 : Blo 854356 965587 := bstep (se 1 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 965587 = 1448381) B1448381
theorem B3652685 : Blo 854356 3652685 := bstep (se 3 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 3652685 = 1369757) B1369757
theorem B6503651 : Blo 854356 6503651 := bstep (se 1 (by rfl) ⟨4877738, by rfl⟩ : syracuseStep 6503651 = 9755477) B9755477
theorem B2342125 : Blo 854356 2342125 := bstep (se 3 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 2342125 = 878297) B878297
theorem B2342225 : Blo 854356 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B2441137 : Blo 854356 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B2310083 : Blo 854356 2310083 := bstep (se 1 (by rfl) ⟨1732562, by rfl⟩ : syracuseStep 2310083 = 3465125) B3465125
theorem B3293347 : Blo 854356 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B4341923 : Blo 854356 4341923 := bstep (se 1 (by rfl) ⟨3256442, by rfl⟩ : syracuseStep 4341923 = 6512885) B6512885
theorem B4636835 : Blo 854356 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B2441411 : Blo 854356 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B2343277 : Blo 854356 2343277 := bstep (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) B878729
theorem B2441603 : Blo 854356 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B5489507 : Blo 854356 5489507 := bstep (se 1 (by rfl) ⟨4117130, by rfl⟩ : syracuseStep 5489507 = 8234261) B8234261
theorem B3130211 : Blo 854356 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B1622929 : Blo 854356 1622929 := bstep (se 2 (by rfl) ⟨608598, by rfl⟩ : syracuseStep 1622929 = 1217197) B1217197
theorem B2737091 : Blo 854356 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B4342733 : Blo 854356 4342733 := bstep (se 3 (by rfl) ⟨814262, by rfl⟩ : syracuseStep 4342733 = 1628525) B1628525
theorem B9749645 : Blo 854356 9749645 := bstep (se 3 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 9749645 = 3656117) B3656117
theorem B2442413 : Blo 854356 2442413 := bstep (se 3 (by rfl) ⟨457952, by rfl⟩ : syracuseStep 2442413 = 915905) B915905
theorem B1623331 : Blo 854356 1623331 := bstep (se 1 (by rfl) ⟨1217498, by rfl⟩ : syracuseStep 1623331 = 2434997) B2434997
theorem B4867397 : Blo 854356 4867397 := bstep (se 4 (by rfl) ⟨456318, by rfl⟩ : syracuseStep 4867397 = 912637) B912637
theorem B1623377 : Blo 854356 1623377 := bstep (se 2 (by rfl) ⟨608766, by rfl⟩ : syracuseStep 1623377 = 1217533) B1217533
theorem B2442595 : Blo 854356 2442595 := bstep (se 1 (by rfl) ⟨1831946, by rfl⟩ : syracuseStep 2442595 = 3663893) B3663893
theorem B2606627 : Blo 854356 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1623665 : Blo 854356 1623665 := bstep (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) B1217749
theorem B4114097 : Blo 854356 4114097 := bstep (se 2 (by rfl) ⟨1542786, by rfl⟩ : syracuseStep 4114097 = 3085573) B3085573
theorem B2311907 : Blo 854356 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B7128803 : Blo 854356 7128803 := bstep (se 1 (by rfl) ⟨5346602, by rfl⟩ : syracuseStep 7128803 = 10693205) B10693205
theorem B3131149 : Blo 854356 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B2737937 : Blo 854356 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B2934605 : Blo 854356 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B2443085 : Blo 854356 2443085 := bstep (se 3 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 2443085 = 916157) B916157
theorem B2312081 : Blo 854356 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B1427345 : Blo 854356 1427345 := bstep (se 2 (by rfl) ⟨535254, by rfl⟩ : syracuseStep 1427345 = 1070509) B1070509
theorem B6670349 : Blo 854356 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B5490737 : Blo 854356 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B3295331 : Blo 854356 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B1624387 : Blo 854356 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B4639301 : Blo 854356 4639301 := bstep (se 4 (by rfl) ⟨434934, by rfl⟩ : syracuseStep 4639301 = 869869) B869869
theorem B1624835 : Blo 854356 1624835 := bstep (se 1 (by rfl) ⟨1218626, by rfl⟩ : syracuseStep 1624835 = 2437253) B2437253
theorem B4017059 : Blo 854356 4017059 := bstep (se 1 (by rfl) ⟨3012794, by rfl⟩ : syracuseStep 4017059 = 6025589) B6025589
theorem B2608049 : Blo 854356 2608049 := bstep (se 2 (by rfl) ⟨978018, by rfl⟩ : syracuseStep 2608049 = 1956037) B1956037
theorem B2444269 : Blo 854356 2444269 := bstep (se 3 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 2444269 = 916601) B916601
theorem B1625123 : Blo 854356 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B2608291 : Blo 854356 2608291 := bstep (se 1 (by rfl) ⟨1956218, by rfl⟩ : syracuseStep 2608291 = 3912437) B3912437
theorem B4639949 : Blo 854356 4639949 := bstep (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) B1739981
theorem B1461521 : Blo 854356 1461521 := bstep (se 2 (by rfl) ⟨548070, by rfl⟩ : syracuseStep 1461521 = 1096141) B1096141
theorem B4115747 : Blo 854356 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B3657059 : Blo 854356 3657059 := bstep (se 1 (by rfl) ⟨2742794, by rfl⟩ : syracuseStep 3657059 = 5485589) B5485589
theorem B2477411 : Blo 854356 2477411 := bstep (se 1 (by rfl) ⟨1858058, by rfl⟩ : syracuseStep 2477411 = 3716117) B3716117
theorem B1461665 : Blo 854356 1461665 := bstep (se 2 (by rfl) ⟨548124, by rfl⟩ : syracuseStep 1461665 = 1096249) B1096249
theorem B2739757 : Blo 854356 2739757 := bstep (se 3 (by rfl) ⟨513704, by rfl⟩ : syracuseStep 2739757 = 1027409) B1027409
theorem B10440373 : Blo 854356 10440373 := bstep (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) B978785
theorem B1527587 : Blo 854356 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B2314061 : Blo 854356 2314061 := bstep (se 3 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 2314061 = 867773) B867773
theorem B2314115 : Blo 854356 2314115 := bstep (se 1 (by rfl) ⟨1735586, by rfl⟩ : syracuseStep 2314115 = 3471173) B3471173
theorem B1626065 : Blo 854356 1626065 := bstep (se 2 (by rfl) ⟨609774, by rfl⟩ : syracuseStep 1626065 = 1219549) B1219549
theorem B9752561 : Blo 854356 9752561 := bstep (se 2 (by rfl) ⟨3657210, by rfl⟩ : syracuseStep 9752561 = 7314421) B7314421
theorem B9261125 : Blo 854356 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B1233235 : Blo 854356 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B6508997 : Blo 854356 6508997 := bstep (se 4 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 6508997 = 1220437) B1220437
theorem B5493197 : Blo 854356 5493197 := bstep (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) B2059949
theorem B4116977 : Blo 854356 4116977 := bstep (se 2 (by rfl) ⟨1543866, by rfl⟩ : syracuseStep 4116977 = 3087733) B3087733
theorem B1462835 : Blo 854356 1462835 := bstep (se 1 (by rfl) ⟨1097126, by rfl⟩ : syracuseStep 1462835 = 2194253) B2194253
theorem B2609741 : Blo 854356 2609741 := bstep (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) B978653
theorem B1626961 : Blo 854356 1626961 := bstep (se 2 (by rfl) ⟨610110, by rfl⟩ : syracuseStep 1626961 = 1220221) B1220221
theorem B1627121 : Blo 854356 1627121 := bstep (se 2 (by rfl) ⟨610170, by rfl⟩ : syracuseStep 1627121 = 1220341) B1220341
theorem B8803313 : Blo 854356 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B1299665 : Blo 854356 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B3659057 : Blo 854356 3659057 := bstep (se 2 (by rfl) ⟨1372146, by rfl⟩ : syracuseStep 3659057 = 2744293) B2744293
theorem B1922417 : Blo 854356 1922417 := bstep (se 2 (by rfl) ⟨720906, by rfl⟩ : syracuseStep 1922417 = 1441813) B1441813
theorem B1922435 : Blo 854356 1922435 := bstep (se 1 (by rfl) ⟨1441826, by rfl⟩ : syracuseStep 1922435 = 2883653) B2883653
theorem B1627523 : Blo 854356 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B1922705 : Blo 854356 1922705 := bstep (se 2 (by rfl) ⟨721014, by rfl⟩ : syracuseStep 1922705 = 1442029) B1442029
theorem B1922723 : Blo 854356 1922723 := bstep (se 1 (by rfl) ⟨1442042, by rfl⟩ : syracuseStep 1922723 = 2884085) B2884085
theorem B1922993 : Blo 854356 1922993 := bstep (se 2 (by rfl) ⟨721122, by rfl⟩ : syracuseStep 1922993 = 1442245) B1442245
theorem B1923011 : Blo 854356 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B1235057 : Blo 854356 1235057 := bstep (se 2 (by rfl) ⟨463146, by rfl⟩ : syracuseStep 1235057 = 926293) B926293
theorem B1923281 : Blo 854356 1923281 := bstep (se 2 (by rfl) ⟨721230, by rfl⟩ : syracuseStep 1923281 = 1442461) B1442461
theorem B1923299 : Blo 854356 1923299 := bstep (se 1 (by rfl) ⟨1442474, by rfl⟩ : syracuseStep 1923299 = 2884949) B2884949
theorem B1693937 : Blo 854356 1693937 := bstep (se 2 (by rfl) ⟨635226, by rfl⟩ : syracuseStep 1693937 = 1270453) B1270453
theorem B1628419 : Blo 854356 1628419 := bstep (se 1 (by rfl) ⟨1221314, by rfl⟩ : syracuseStep 1628419 = 2442629) B2442629
theorem B1628579 : Blo 854356 1628579 := bstep (se 1 (by rfl) ⟨1221434, by rfl⟩ : syracuseStep 1628579 = 2442869) B2442869
theorem B1923569 : Blo 854356 1923569 := bstep (se 2 (by rfl) ⟨721338, by rfl⟩ : syracuseStep 1923569 = 1442677) B1442677
theorem B1923587 : Blo 854356 1923587 := bstep (se 1 (by rfl) ⟨1442690, by rfl⟩ : syracuseStep 1923587 = 2885381) B2885381
theorem B16439921 : Blo 854356 16439921 := bstep (se 2 (by rfl) ⟨6164970, by rfl⟩ : syracuseStep 16439921 = 12329941) B12329941
theorem B1825411 : Blo 854356 1825411 := bstep (se 1 (by rfl) ⟨1369058, by rfl⟩ : syracuseStep 1825411 = 2738117) B2738117
theorem B2054915 : Blo 854356 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B1923857 : Blo 854356 1923857 := bstep (se 2 (by rfl) ⟨721446, by rfl⟩ : syracuseStep 1923857 = 1442893) B1442893
theorem B1923875 : Blo 854356 1923875 := bstep (se 1 (by rfl) ⟨1442906, by rfl⟩ : syracuseStep 1923875 = 2885813) B2885813
theorem B1825667 : Blo 854356 1825667 := bstep (se 1 (by rfl) ⟨1369250, by rfl⟩ : syracuseStep 1825667 = 2738501) B2738501
theorem B4119437 : Blo 854356 4119437 := bstep (se 3 (by rfl) ⟨772394, by rfl⟩ : syracuseStep 4119437 = 1544789) B1544789
theorem B2743217 : Blo 854356 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B1956803 : Blo 854356 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B4873229 : Blo 854356 4873229 := bstep (se 3 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 4873229 = 1827461) B1827461
theorem B2055203 : Blo 854356 2055203 := bstep (se 1 (by rfl) ⟨1541402, by rfl⟩ : syracuseStep 2055203 = 3082805) B3082805
theorem B1924145 : Blo 854356 1924145 := bstep (se 2 (by rfl) ⟨721554, by rfl⟩ : syracuseStep 1924145 = 1443109) B1443109
theorem B1924163 : Blo 854356 1924163 := bstep (se 1 (by rfl) ⟨1443122, by rfl⟩ : syracuseStep 1924163 = 2886245) B2886245
theorem B2743409 : Blo 854356 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B1301665 : Blo 854356 1301665 := bstep (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) B976249
theorem B1924433 : Blo 854356 1924433 := bstep (se 2 (by rfl) ⟨721662, by rfl⟩ : syracuseStep 1924433 = 1443325) B1443325
theorem B1924451 : Blo 854356 1924451 := bstep (se 1 (by rfl) ⟨1443338, by rfl⟩ : syracuseStep 1924451 = 2886677) B2886677
theorem B3464653 : Blo 854356 3464653 := bstep (se 3 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 3464653 = 1299245) B1299245
theorem B12344885 : Blo 854356 12344885 := bstep (se 5 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 12344885 = 1157333) B1157333
theorem B1924721 : Blo 854356 1924721 := bstep (se 2 (by rfl) ⟨721770, by rfl⟩ : syracuseStep 1924721 = 1443541) B1443541
theorem B1924739 : Blo 854356 1924739 := bstep (se 1 (by rfl) ⟨1443554, by rfl⟩ : syracuseStep 1924739 = 2887109) B2887109
theorem B3661517 : Blo 854356 3661517 := bstep (se 3 (by rfl) ⟨686534, by rfl⟩ : syracuseStep 3661517 = 1373069) B1373069
theorem B1826641 : Blo 854356 1826641 := bstep (se 2 (by rfl) ⟨684990, by rfl⟩ : syracuseStep 1826641 = 1369981) B1369981
theorem B2056049 : Blo 854356 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B1925009 : Blo 854356 1925009 := bstep (se 2 (by rfl) ⟨721878, by rfl⟩ : syracuseStep 1925009 = 1443757) B1443757
theorem B1925027 : Blo 854356 1925027 := bstep (se 1 (by rfl) ⟨1443770, by rfl⟩ : syracuseStep 1925027 = 2887541) B2887541
theorem B1466467 : Blo 854356 1466467 := bstep (se 1 (by rfl) ⟨1099850, by rfl⟩ : syracuseStep 1466467 = 2199701) B2199701
theorem B8249485 : Blo 854356 8249485 := bstep (se 3 (by rfl) ⟨1546778, by rfl⟩ : syracuseStep 8249485 = 3093557) B3093557
theorem B2056337 : Blo 854356 2056337 := bstep (se 2 (by rfl) ⟨771126, by rfl⟩ : syracuseStep 2056337 = 1542253) B1542253
theorem B1925297 : Blo 854356 1925297 := bstep (se 2 (by rfl) ⟨721986, by rfl⟩ : syracuseStep 1925297 = 1443973) B1443973
theorem B1925315 : Blo 854356 1925315 := bstep (se 1 (by rfl) ⟨1443986, by rfl⟩ : syracuseStep 1925315 = 2887973) B2887973
theorem B2056529 : Blo 854356 2056529 := bstep (se 2 (by rfl) ⟨771198, by rfl⟩ : syracuseStep 2056529 = 1542397) B1542397
theorem B1925585 : Blo 854356 1925585 := bstep (se 2 (by rfl) ⟨722094, by rfl⟩ : syracuseStep 1925585 = 1444189) B1444189
theorem B1827299 : Blo 854356 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B1925603 : Blo 854356 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B1925873 : Blo 854356 1925873 := bstep (se 2 (by rfl) ⟨722202, by rfl⟩ : syracuseStep 1925873 = 1444405) B1444405
theorem B1925891 : Blo 854356 1925891 := bstep (se 1 (by rfl) ⟨1444418, by rfl⟩ : syracuseStep 1925891 = 2888837) B2888837
theorem B1926161 : Blo 854356 1926161 := bstep (se 2 (by rfl) ⟨722310, by rfl⟩ : syracuseStep 1926161 = 1444621) B1444621
theorem B1926179 : Blo 854356 1926179 := bstep (se 1 (by rfl) ⟨1444634, by rfl⟩ : syracuseStep 1926179 = 2889269) B2889269
theorem B4875461 : Blo 854356 4875461 := bstep (se 4 (by rfl) ⟨457074, by rfl⟩ : syracuseStep 4875461 = 914149) B914149
theorem B40035541 : Blo 854356 40035541 := bstep (se 7 (by rfl) ⟨469166, by rfl⟩ : syracuseStep 40035541 = 938333) B938333
theorem B1369315 : Blo 854356 1369315 := bstep (se 1 (by rfl) ⟨1026986, by rfl⟩ : syracuseStep 1369315 = 2053973) B2053973
theorem B7628017 : Blo 854356 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B3663089 : Blo 854356 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B2057489 : Blo 854356 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B1369379 : Blo 854356 1369379 := bstep (se 1 (by rfl) ⟨1027034, by rfl⟩ : syracuseStep 1369379 = 2054069) B2054069
theorem B1828145 : Blo 854356 1828145 := bstep (se 2 (by rfl) ⟨685554, by rfl⟩ : syracuseStep 1828145 = 1371109) B1371109
theorem B1926449 : Blo 854356 1926449 := bstep (se 2 (by rfl) ⟨722418, by rfl⟩ : syracuseStep 1926449 = 1444837) B1444837
theorem B1467713 : Blo 854356 1467713 := bstep (se 2 (by rfl) ⟨550392, by rfl⟩ : syracuseStep 1467713 = 1100785) B1100785
theorem B1926467 : Blo 854356 1926467 := bstep (se 1 (by rfl) ⟨1444850, by rfl⟩ : syracuseStep 1926467 = 2889701) B2889701
theorem B2745677 : Blo 854356 2745677 := bstep (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) B1029629
theorem B1926737 : Blo 854356 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B1926755 : Blo 854356 1926755 := bstep (se 1 (by rfl) ⟨1445066, by rfl⟩ : syracuseStep 1926755 = 2890133) B2890133
theorem B8775395 : Blo 854356 8775395 := bstep (se 1 (by rfl) ⟨6581546, by rfl⟩ : syracuseStep 8775395 = 13163093) B13163093
theorem B4876145 : Blo 854356 4876145 := bstep (se 2 (by rfl) ⟨1828554, by rfl⟩ : syracuseStep 4876145 = 3657109) B3657109
theorem B1927025 : Blo 854356 1927025 := bstep (se 2 (by rfl) ⟨722634, by rfl⟩ : syracuseStep 1927025 = 1445269) B1445269
theorem B1927043 : Blo 854356 1927043 := bstep (se 1 (by rfl) ⟨1445282, by rfl⟩ : syracuseStep 1927043 = 2890565) B2890565
theorem B2779085 : Blo 854356 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B5859461 : Blo 854356 5859461 := bstep (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) B1098649
theorem B6514829 : Blo 854356 6514829 := bstep (se 3 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 6514829 = 2443061) B2443061
theorem B1927313 : Blo 854356 1927313 := bstep (se 2 (by rfl) ⟨722742, by rfl⟩ : syracuseStep 1927313 = 1445485) B1445485
theorem B1927331 : Blo 854356 1927331 := bstep (se 1 (by rfl) ⟨1445498, by rfl⟩ : syracuseStep 1927331 = 2890997) B2890997
theorem B1370353 : Blo 854356 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B1042723 : Blo 854356 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B1927601 : Blo 854356 1927601 := bstep (se 2 (by rfl) ⟨722850, by rfl⟩ : syracuseStep 1927601 = 1445701) B1445701
theorem B1927619 : Blo 854356 1927619 := bstep (se 1 (by rfl) ⟨1445714, by rfl⟩ : syracuseStep 1927619 = 2891429) B2891429
theorem B7301573 : Blo 854356 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B1370609 : Blo 854356 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B2058787 : Blo 854356 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B1370801 : Blo 854356 1370801 := bstep (se 2 (by rfl) ⟨514050, by rfl⟩ : syracuseStep 1370801 = 1028101) B1028101
theorem B1927889 : Blo 854356 1927889 := bstep (se 2 (by rfl) ⟨722958, by rfl⟩ : syracuseStep 1927889 = 1445917) B1445917
theorem B1927907 : Blo 854356 1927907 := bstep (se 1 (by rfl) ⟨1445930, by rfl⟩ : syracuseStep 1927907 = 2891861) B2891861
theorem B879427 : Blo 854356 879427 := bstep (se 1 (by rfl) ⟨659570, by rfl⟩ : syracuseStep 879427 = 1319141) B1319141
theorem B2747267 : Blo 854356 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B1928177 : Blo 854356 1928177 := bstep (se 2 (by rfl) ⟨723066, by rfl⟩ : syracuseStep 1928177 = 1446133) B1446133
theorem B1928195 : Blo 854356 1928195 := bstep (se 1 (by rfl) ⟨1446146, by rfl⟩ : syracuseStep 1928195 = 2892293) B2892293
theorem B7302257 : Blo 854356 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B4943045 : Blo 854356 4943045 := bstep (se 4 (by rfl) ⟨463410, by rfl⟩ : syracuseStep 4943045 = 926821) B926821
theorem B1928465 : Blo 854356 1928465 := bstep (se 2 (by rfl) ⟨723174, by rfl⟩ : syracuseStep 1928465 = 1446349) B1446349
theorem B4877603 : Blo 854356 4877603 := bstep (se 1 (by rfl) ⟨3658202, by rfl⟩ : syracuseStep 4877603 = 7316405) B7316405
theorem B1928483 : Blo 854356 1928483 := bstep (se 1 (by rfl) ⟨1446362, by rfl⟩ : syracuseStep 1928483 = 2892725) B2892725
theorem B3468835 : Blo 854356 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B1928753 : Blo 854356 1928753 := bstep (se 2 (by rfl) ⟨723282, by rfl⟩ : syracuseStep 1928753 = 1446565) B1446565
theorem B1928771 : Blo 854356 1928771 := bstep (se 1 (by rfl) ⟨1446578, by rfl⟩ : syracuseStep 1928771 = 2893157) B2893157
theorem B912979 : Blo 854356 912979 := bstep (se 1 (by rfl) ⟨684734, by rfl⟩ : syracuseStep 912979 = 1369469) B1369469
theorem B3468899 : Blo 854356 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B3665549 : Blo 854356 3665549 := bstep (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) B1374581
theorem B2748163 : Blo 854356 2748163 := bstep (se 1 (by rfl) ⟨2061122, by rfl⟩ : syracuseStep 2748163 = 4122245) B4122245
theorem B1929041 : Blo 854356 1929041 := bstep (se 2 (by rfl) ⟨723390, by rfl⟩ : syracuseStep 1929041 = 1446781) B1446781
theorem B1929059 : Blo 854356 1929059 := bstep (se 1 (by rfl) ⟨1446794, by rfl⟩ : syracuseStep 1929059 = 2893589) B2893589
theorem B10973069 : Blo 854356 10973069 := bstep (se 3 (by rfl) ⟨2057450, by rfl⟩ : syracuseStep 10973069 = 4114901) B4114901
theorem B1372115 : Blo 854356 1372115 := bstep (se 1 (by rfl) ⟨1029086, by rfl⟩ : syracuseStep 1372115 = 2058173) B2058173
theorem B3665891 : Blo 854356 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B1830929 : Blo 854356 1830929 := bstep (se 2 (by rfl) ⟨686598, by rfl⟩ : syracuseStep 1830929 = 1373197) B1373197
theorem B1929329 : Blo 854356 1929329 := bstep (se 2 (by rfl) ⟨723498, by rfl⟩ : syracuseStep 1929329 = 1446997) B1446997
theorem B1929347 : Blo 854356 1929347 := bstep (se 1 (by rfl) ⟨1447010, by rfl⟩ : syracuseStep 1929347 = 2894021) B2894021
theorem B1372339 : Blo 854356 1372339 := bstep (se 1 (by rfl) ⟨1029254, by rfl⟩ : syracuseStep 1372339 = 2058509) B2058509
theorem B1372403 : Blo 854356 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B1372531 : Blo 854356 1372531 := bstep (se 1 (by rfl) ⟨1029398, by rfl⟩ : syracuseStep 1372531 = 2058797) B2058797
theorem B1929617 : Blo 854356 1929617 := bstep (se 2 (by rfl) ⟨723606, by rfl⟩ : syracuseStep 1929617 = 1447213) B1447213
theorem B1929635 : Blo 854356 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B11301389 : Blo 854356 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B3469873 : Blo 854356 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B2224721 : Blo 854356 2224721 := bstep (se 2 (by rfl) ⟨834270, by rfl⟩ : syracuseStep 2224721 = 1668541) B1668541
theorem B1929905 : Blo 854356 1929905 := bstep (se 2 (by rfl) ⟨723714, by rfl⟩ : syracuseStep 1929905 = 1447429) B1447429
theorem B1929923 : Blo 854356 1929923 := bstep (se 1 (by rfl) ⟨1447442, by rfl⟩ : syracuseStep 1929923 = 2894885) B2894885
theorem B2749265 : Blo 854356 2749265 := bstep (se 2 (by rfl) ⟨1030974, by rfl⟩ : syracuseStep 2749265 = 2061949) B2061949
theorem B914371 : Blo 854356 914371 := bstep (se 1 (by rfl) ⟨685778, by rfl⟩ : syracuseStep 914371 = 1371557) B1371557
theorem B1930193 : Blo 854356 1930193 := bstep (se 2 (by rfl) ⟨723822, by rfl⟩ : syracuseStep 1930193 = 1447645) B1447645
theorem B2749393 : Blo 854356 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B1930211 : Blo 854356 1930211 := bstep (se 1 (by rfl) ⟨1447658, by rfl⟩ : syracuseStep 1930211 = 2895317) B2895317
theorem B6517745 : Blo 854356 6517745 := bstep (se 2 (by rfl) ⟨2444154, by rfl⟩ : syracuseStep 6517745 = 4888309) B4888309
theorem B1373249 : Blo 854356 1373249 := bstep (se 2 (by rfl) ⟨514968, by rfl⟩ : syracuseStep 1373249 = 1029937) B1029937
theorem B1373377 : Blo 854356 1373377 := bstep (se 2 (by rfl) ⟨515016, by rfl⟩ : syracuseStep 1373377 = 1030033) B1030033
theorem B1930481 : Blo 854356 1930481 := bstep (se 2 (by rfl) ⟨723930, by rfl⟩ : syracuseStep 1930481 = 1447861) B1447861
theorem B1930499 : Blo 854356 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B1930769 : Blo 854356 1930769 := bstep (se 2 (by rfl) ⟨724038, by rfl⟩ : syracuseStep 1930769 = 1448077) B1448077
theorem B1930787 : Blo 854356 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B1373761 : Blo 854356 1373761 := bstep (se 2 (by rfl) ⟨515160, by rfl⟩ : syracuseStep 1373761 = 1030321) B1030321
theorem B1931057 : Blo 854356 1931057 := bstep (se 2 (by rfl) ⟨724146, by rfl⟩ : syracuseStep 1931057 = 1448293) B1448293
theorem B1374017 : Blo 854356 1374017 := bstep (se 2 (by rfl) ⟨515256, by rfl⟩ : syracuseStep 1374017 = 1030513) B1030513
theorem B1931075 : Blo 854356 1931075 := bstep (se 1 (by rfl) ⟨1448306, by rfl⟩ : syracuseStep 1931075 = 2896613) B2896613
theorem B29718413 : Blo 854356 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B2193809 : Blo 854356 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B9238981 : Blo 854356 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B4880837 : Blo 854356 4880837 := bstep (se 4 (by rfl) ⟨457578, by rfl⟩ : syracuseStep 4880837 = 915157) B915157
theorem B4291213 : Blo 854356 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B4881293 : Blo 854356 4881293 := bstep (se 3 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 4881293 = 1830485) B1830485
theorem B1735715 : Blo 854356 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B4815949 : Blo 854356 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B1539715 : Blo 854356 1539715 := bstep (se 1 (by rfl) ⟨1154786, by rfl⟩ : syracuseStep 1539715 = 2309573) B2309573
theorem B2883491 : Blo 854356 2883491 := bstep (se 1 (by rfl) ⟨2162618, by rfl⟩ : syracuseStep 2883491 = 4325237) B4325237
theorem B2162609 : Blo 854356 2162609 := bstep (se 2 (by rfl) ⟨810978, by rfl⟩ : syracuseStep 2162609 = 1621957) B1621957
theorem B2162659 : Blo 854356 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B6488099 : Blo 854356 6488099 := bstep (se 1 (by rfl) ⟨4866074, by rfl⟩ : syracuseStep 6488099 = 9732149) B9732149
theorem B4882477 : Blo 854356 4882477 := bstep (se 3 (by rfl) ⟨915464, by rfl⟩ : syracuseStep 4882477 = 1830929) B1830929
theorem B1441867 : Blo 854356 1441867 := bstep (se 1 (by rfl) ⟨1081400, by rfl⟩ : syracuseStep 1441867 = 2162801) B2162801
theorem B1442009 : Blo 854356 1442009 := bstep (se 2 (by rfl) ⟨540753, by rfl⟩ : syracuseStep 1442009 = 1081507) B1081507
theorem B4391129 : Blo 854356 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B1442137 : Blo 854356 1442137 := bstep (se 2 (by rfl) ⟨540801, by rfl⟩ : syracuseStep 1442137 = 1081603) B1081603
theorem B2163095 : Blo 854356 2163095 := bstep (se 1 (by rfl) ⟨1622321, by rfl⟩ : syracuseStep 2163095 = 3244643) B3244643
theorem B2884247 : Blo 854356 2884247 := bstep (se 1 (by rfl) ⟨2163185, by rfl⟩ : syracuseStep 2884247 = 4326371) B4326371
theorem B4326209 : Blo 854356 4326209 := bstep (se 2 (by rfl) ⟨1622328, by rfl⟩ : syracuseStep 4326209 = 3244657) B3244657
theorem B3244931 : Blo 854356 3244931 := bstep (se 1 (by rfl) ⟨2433698, by rfl⟩ : syracuseStep 3244931 = 4867397) B4867397
theorem B1082251 : Blo 854356 1082251 := bstep (se 1 (by rfl) ⟨811688, by rfl⟩ : syracuseStep 1082251 = 1623377) B1623377
theorem B1442711 : Blo 854356 1442711 := bstep (se 1 (by rfl) ⟨1082033, by rfl⟩ : syracuseStep 1442711 = 2164067) B2164067
theorem B1115095 : Blo 854356 1115095 := bstep (se 1 (by rfl) ⟨836321, by rfl⟩ : syracuseStep 1115095 = 1672643) B1672643
theorem B1442839 : Blo 854356 1442839 := bstep (se 1 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 1442839 = 2164259) B2164259
theorem B4752535 : Blo 854356 4752535 := bstep (se 1 (by rfl) ⟨3564401, by rfl⟩ : syracuseStep 4752535 = 7128803) B7128803
theorem B2884787 : Blo 854356 2884787 := bstep (se 1 (by rfl) ⟨2163590, by rfl⟩ : syracuseStep 2884787 = 4327181) B4327181
theorem B13173941 : Blo 854356 13173941 := bstep (se 5 (by rfl) ⟨617528, by rfl⟩ : syracuseStep 13173941 = 1235057) B1235057
theorem B2163905 : Blo 854356 2163905 := bstep (se 2 (by rfl) ⟨811464, by rfl⟩ : syracuseStep 2163905 = 1622929) B1622929
theorem B14648525 : Blo 854356 14648525 := bstep (se 3 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 14648525 = 5493197) B5493197
theorem B1541387 : Blo 854356 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B3900761 : Blo 854356 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B2196887 : Blo 854356 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B2885057 : Blo 854356 2885057 := bstep (se 2 (by rfl) ⟨1081896, by rfl⟩ : syracuseStep 2885057 = 2163793) B2163793
theorem B53380721 : Blo 854356 53380721 := bstep (se 2 (by rfl) ⟨20017770, by rfl⟩ : syracuseStep 53380721 = 40035541) B40035541
theorem B1443467 : Blo 854356 1443467 := bstep (se 1 (by rfl) ⟨1082600, by rfl⟩ : syracuseStep 1443467 = 2165201) B2165201
theorem B3344075 : Blo 854356 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B2164441 : Blo 854356 2164441 := bstep (se 2 (by rfl) ⟨811665, by rfl⟩ : syracuseStep 2164441 = 1623331) B1623331
theorem B1443595 : Blo 854356 1443595 := bstep (se 1 (by rfl) ⟨1082696, by rfl⟩ : syracuseStep 1443595 = 2165393) B2165393
theorem B1083223 : Blo 854356 1083223 := bstep (se 1 (by rfl) ⟨812417, by rfl⟩ : syracuseStep 1083223 = 1624835) B1624835
theorem B1443737 : Blo 854356 1443737 := bstep (se 2 (by rfl) ⟨541401, by rfl⟩ : syracuseStep 1443737 = 1082803) B1082803
theorem B15599537 : Blo 854356 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B2885597 : Blo 854356 2885597 := bstep (se 3 (by rfl) ⟨541049, by rfl⟩ : syracuseStep 2885597 = 1082099) B1082099
theorem B1443865 : Blo 854356 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B854359 : Blo 854356 854359 := bstep (se 1 (by rfl) ⟨640769, by rfl⟩ : syracuseStep 854359 = 1281539) B1281539
theorem B854379 : Blo 854356 854379 := bstep (se 1 (by rfl) ⟨640784, by rfl⟩ : syracuseStep 854379 = 1281569) B1281569
theorem B854391 : Blo 854356 854391 := bstep (se 1 (by rfl) ⟨640793, by rfl⟩ : syracuseStep 854391 = 1281587) B1281587
theorem B854411 : Blo 854356 854411 := bstep (se 1 (by rfl) ⟨640808, by rfl⟩ : syracuseStep 854411 = 1281617) B1281617
theorem B854423 : Blo 854356 854423 := bstep (se 1 (by rfl) ⟨640817, by rfl⟩ : syracuseStep 854423 = 1281635) B1281635
theorem B854443 : Blo 854356 854443 := bstep (se 1 (by rfl) ⟨640832, by rfl⟩ : syracuseStep 854443 = 1281665) B1281665
theorem B854455 : Blo 854356 854455 := bstep (se 1 (by rfl) ⟨640841, by rfl⟩ : syracuseStep 854455 = 1281683) B1281683
theorem B854475 : Blo 854356 854475 := bstep (se 1 (by rfl) ⟨640856, by rfl⟩ : syracuseStep 854475 = 1281713) B1281713
theorem B854487 : Blo 854356 854487 := bstep (se 1 (by rfl) ⟨640865, by rfl⟩ : syracuseStep 854487 = 1281731) B1281731
theorem B854507 : Blo 854356 854507 := bstep (se 1 (by rfl) ⟨640880, by rfl⟩ : syracuseStep 854507 = 1281761) B1281761
theorem B854519 : Blo 854356 854519 := bstep (se 1 (by rfl) ⟨640889, by rfl⟩ : syracuseStep 854519 = 1281779) B1281779
theorem B854539 : Blo 854356 854539 := bstep (se 1 (by rfl) ⟨640904, by rfl⟩ : syracuseStep 854539 = 1281809) B1281809
theorem B854551 : Blo 854356 854551 := bstep (se 1 (by rfl) ⟨640913, by rfl⟩ : syracuseStep 854551 = 1281827) B1281827
theorem B1018391 : Blo 854356 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B7801379 : Blo 854356 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B854571 : Blo 854356 854571 := bstep (se 1 (by rfl) ⟨640928, by rfl⟩ : syracuseStep 854571 = 1281857) B1281857
theorem B1542707 : Blo 854356 1542707 := bstep (se 1 (by rfl) ⟨1157030, by rfl⟩ : syracuseStep 1542707 = 2314061) B2314061
theorem B854583 : Blo 854356 854583 := bstep (se 1 (by rfl) ⟨640937, by rfl⟩ : syracuseStep 854583 = 1281875) B1281875
theorem B854603 : Blo 854356 854603 := bstep (se 1 (by rfl) ⟨640952, by rfl⟩ : syracuseStep 854603 = 1281905) B1281905
theorem B854615 : Blo 854356 854615 := bstep (se 1 (by rfl) ⟨640961, by rfl⟩ : syracuseStep 854615 = 1281923) B1281923
theorem B1444439 : Blo 854356 1444439 := bstep (se 1 (by rfl) ⟨1083329, by rfl⟩ : syracuseStep 1444439 = 2166659) B2166659
theorem B1542743 : Blo 854356 1542743 := bstep (se 1 (by rfl) ⟨1157057, by rfl⟩ : syracuseStep 1542743 = 2314115) B2314115
theorem B854635 : Blo 854356 854635 := bstep (se 1 (by rfl) ⟨640976, by rfl⟩ : syracuseStep 854635 = 1281953) B1281953
theorem B854647 : Blo 854356 854647 := bstep (se 1 (by rfl) ⟨640985, by rfl⟩ : syracuseStep 854647 = 1281971) B1281971
theorem B854667 : Blo 854356 854667 := bstep (se 1 (by rfl) ⟨641000, by rfl⟩ : syracuseStep 854667 = 1282001) B1282001
theorem B1084043 : Blo 854356 1084043 := bstep (se 1 (by rfl) ⟨813032, by rfl⟩ : syracuseStep 1084043 = 1626065) B1626065
theorem B854679 : Blo 854356 854679 := bstep (se 1 (by rfl) ⟨641009, by rfl⟩ : syracuseStep 854679 = 1282019) B1282019
theorem B854699 : Blo 854356 854699 := bstep (se 1 (by rfl) ⟨641024, by rfl⟩ : syracuseStep 854699 = 1282049) B1282049
theorem B854711 : Blo 854356 854711 := bstep (se 1 (by rfl) ⟨641033, by rfl⟩ : syracuseStep 854711 = 1282067) B1282067
theorem B854731 : Blo 854356 854731 := bstep (se 1 (by rfl) ⟨641048, by rfl⟩ : syracuseStep 854731 = 1282097) B1282097
theorem B854743 : Blo 854356 854743 := bstep (se 1 (by rfl) ⟨641057, by rfl⟩ : syracuseStep 854743 = 1282115) B1282115
theorem B1444567 : Blo 854356 1444567 := bstep (se 1 (by rfl) ⟨1083425, by rfl⟩ : syracuseStep 1444567 = 2166851) B2166851
theorem B4328153 : Blo 854356 4328153 := bstep (se 2 (by rfl) ⟨1623057, by rfl⟩ : syracuseStep 4328153 = 3246115) B3246115
theorem B854763 : Blo 854356 854763 := bstep (se 1 (by rfl) ⟨641072, by rfl⟩ : syracuseStep 854763 = 1282145) B1282145
theorem B854775 : Blo 854356 854775 := bstep (se 1 (by rfl) ⟨641081, by rfl⟩ : syracuseStep 854775 = 1282163) B1282163
theorem B854795 : Blo 854356 854795 := bstep (se 1 (by rfl) ⟨641096, by rfl⟩ : syracuseStep 854795 = 1282193) B1282193
theorem B854807 : Blo 854356 854807 := bstep (se 1 (by rfl) ⟨641105, by rfl⟩ : syracuseStep 854807 = 1282211) B1282211
theorem B854827 : Blo 854356 854827 := bstep (se 1 (by rfl) ⟨641120, by rfl⟩ : syracuseStep 854827 = 1282241) B1282241
theorem B2165555 : Blo 854356 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B854839 : Blo 854356 854839 := bstep (se 1 (by rfl) ⟨641129, by rfl⟩ : syracuseStep 854839 = 1282259) B1282259
theorem B854859 : Blo 854356 854859 := bstep (se 1 (by rfl) ⟨641144, by rfl⟩ : syracuseStep 854859 = 1282289) B1282289
theorem B854871 : Blo 854356 854871 := bstep (se 1 (by rfl) ⟨641153, by rfl⟩ : syracuseStep 854871 = 1282307) B1282307
theorem B10980197 : Blo 854356 10980197 := bstep (se 4 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 10980197 = 2058787) B2058787
theorem B854891 : Blo 854356 854891 := bstep (se 1 (by rfl) ⟨641168, by rfl⟩ : syracuseStep 854891 = 1282337) B1282337
theorem B854903 : Blo 854356 854903 := bstep (se 1 (by rfl) ⟨641177, by rfl⟩ : syracuseStep 854903 = 1282355) B1282355
theorem B854923 : Blo 854356 854923 := bstep (se 1 (by rfl) ⟨641192, by rfl⟩ : syracuseStep 854923 = 1282385) B1282385
theorem B854935 : Blo 854356 854935 := bstep (se 1 (by rfl) ⟨641201, by rfl⟩ : syracuseStep 854935 = 1282403) B1282403
theorem B854955 : Blo 854356 854955 := bstep (se 1 (by rfl) ⟨641216, by rfl⟩ : syracuseStep 854955 = 1282433) B1282433
theorem B854967 : Blo 854356 854967 := bstep (se 1 (by rfl) ⟨641225, by rfl⟩ : syracuseStep 854967 = 1282451) B1282451
theorem B854987 : Blo 854356 854987 := bstep (se 1 (by rfl) ⟨641240, by rfl⟩ : syracuseStep 854987 = 1282481) B1282481
theorem B854999 : Blo 854356 854999 := bstep (se 1 (by rfl) ⟨641249, by rfl⟩ : syracuseStep 854999 = 1282499) B1282499
theorem B855019 : Blo 854356 855019 := bstep (se 1 (by rfl) ⟨641264, by rfl⟩ : syracuseStep 855019 = 1282529) B1282529
theorem B855031 : Blo 854356 855031 := bstep (se 1 (by rfl) ⟨641273, by rfl⟩ : syracuseStep 855031 = 1282547) B1282547
theorem B855051 : Blo 854356 855051 := bstep (se 1 (by rfl) ⟨641288, by rfl⟩ : syracuseStep 855051 = 1282577) B1282577
theorem B855063 : Blo 854356 855063 := bstep (se 1 (by rfl) ⟨641297, by rfl⟩ : syracuseStep 855063 = 1282595) B1282595
theorem B855083 : Blo 854356 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B1739827 : Blo 854356 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B855095 : Blo 854356 855095 := bstep (se 1 (by rfl) ⟨641321, by rfl⟩ : syracuseStep 855095 = 1282643) B1282643
theorem B855115 : Blo 854356 855115 := bstep (se 1 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 855115 = 1282673) B1282673
theorem B2886731 : Blo 854356 2886731 := bstep (se 1 (by rfl) ⟨2165048, by rfl⟩ : syracuseStep 2886731 = 4330097) B4330097
theorem B855127 : Blo 854356 855127 := bstep (se 1 (by rfl) ⟨641345, by rfl⟩ : syracuseStep 855127 = 1282691) B1282691
theorem B2165849 : Blo 854356 2165849 := bstep (se 2 (by rfl) ⟨812193, by rfl⟩ : syracuseStep 2165849 = 1624387) B1624387
theorem B855147 : Blo 854356 855147 := bstep (se 1 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 855147 = 1282721) B1282721
theorem B855159 : Blo 854356 855159 := bstep (se 1 (by rfl) ⟨641369, by rfl⟩ : syracuseStep 855159 = 1282739) B1282739
theorem B855179 : Blo 854356 855179 := bstep (se 1 (by rfl) ⟨641384, by rfl⟩ : syracuseStep 855179 = 1282769) B1282769
theorem B855191 : Blo 854356 855191 := bstep (se 1 (by rfl) ⟨641393, by rfl⟩ : syracuseStep 855191 = 1282787) B1282787
theorem B7933079 : Blo 854356 7933079 := bstep (se 1 (by rfl) ⟨5949809, by rfl⟩ : syracuseStep 7933079 = 11899619) B11899619
theorem B855211 : Blo 854356 855211 := bstep (se 1 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 855211 = 1282817) B1282817
theorem B855223 : Blo 854356 855223 := bstep (se 1 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 855223 = 1282835) B1282835
theorem B855243 : Blo 854356 855243 := bstep (se 1 (by rfl) ⟨641432, by rfl⟩ : syracuseStep 855243 = 1282865) B1282865
theorem B855255 : Blo 854356 855255 := bstep (se 1 (by rfl) ⟨641441, by rfl⟩ : syracuseStep 855255 = 1282883) B1282883
theorem B855275 : Blo 854356 855275 := bstep (se 1 (by rfl) ⟨641456, by rfl⟩ : syracuseStep 855275 = 1282913) B1282913
theorem B855287 : Blo 854356 855287 := bstep (se 1 (by rfl) ⟨641465, by rfl⟩ : syracuseStep 855287 = 1282931) B1282931
theorem B855307 : Blo 854356 855307 := bstep (se 1 (by rfl) ⟨641480, by rfl⟩ : syracuseStep 855307 = 1282961) B1282961
theorem B855319 : Blo 854356 855319 := bstep (se 1 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 855319 = 1282979) B1282979
theorem B855339 : Blo 854356 855339 := bstep (se 1 (by rfl) ⟨641504, by rfl⟩ : syracuseStep 855339 = 1283009) B1283009
theorem B855351 : Blo 854356 855351 := bstep (se 1 (by rfl) ⟨641513, by rfl⟩ : syracuseStep 855351 = 1283027) B1283027
theorem B855371 : Blo 854356 855371 := bstep (se 1 (by rfl) ⟨641528, by rfl⟩ : syracuseStep 855371 = 1283057) B1283057
theorem B1445195 : Blo 854356 1445195 := bstep (se 1 (by rfl) ⟨1083896, by rfl⟩ : syracuseStep 1445195 = 2167793) B2167793
theorem B1084747 : Blo 854356 1084747 := bstep (se 1 (by rfl) ⟨813560, by rfl⟩ : syracuseStep 1084747 = 1627121) B1627121
theorem B5868875 : Blo 854356 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B855383 : Blo 854356 855383 := bstep (se 1 (by rfl) ⟨641537, by rfl⟩ : syracuseStep 855383 = 1283075) B1283075
theorem B2887001 : Blo 854356 2887001 := bstep (se 2 (by rfl) ⟨1082625, by rfl⟩ : syracuseStep 2887001 = 2165251) B2165251
theorem B855403 : Blo 854356 855403 := bstep (se 1 (by rfl) ⟨641552, by rfl⟩ : syracuseStep 855403 = 1283105) B1283105
theorem B855415 : Blo 854356 855415 := bstep (se 1 (by rfl) ⟨641561, by rfl⟩ : syracuseStep 855415 = 1283123) B1283123
theorem B855435 : Blo 854356 855435 := bstep (se 1 (by rfl) ⟨641576, by rfl⟩ : syracuseStep 855435 = 1283153) B1283153
theorem B855447 : Blo 854356 855447 := bstep (se 1 (by rfl) ⟨641585, by rfl⟩ : syracuseStep 855447 = 1283171) B1283171
theorem B855467 : Blo 854356 855467 := bstep (se 1 (by rfl) ⟨641600, by rfl⟩ : syracuseStep 855467 = 1283201) B1283201
theorem B855479 : Blo 854356 855479 := bstep (se 1 (by rfl) ⟨641609, by rfl⟩ : syracuseStep 855479 = 1283219) B1283219
theorem B855499 : Blo 854356 855499 := bstep (se 1 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 855499 = 1283249) B1283249
theorem B1445323 : Blo 854356 1445323 := bstep (se 1 (by rfl) ⟨1083992, by rfl⟩ : syracuseStep 1445323 = 2167985) B2167985
theorem B855511 : Blo 854356 855511 := bstep (se 1 (by rfl) ⟨641633, by rfl⟩ : syracuseStep 855511 = 1283267) B1283267
theorem B855531 : Blo 854356 855531 := bstep (se 1 (by rfl) ⟨641648, by rfl⟩ : syracuseStep 855531 = 1283297) B1283297
theorem B855543 : Blo 854356 855543 := bstep (se 1 (by rfl) ⟨641657, by rfl⟩ : syracuseStep 855543 = 1283315) B1283315
theorem B855563 : Blo 854356 855563 := bstep (se 1 (by rfl) ⟨641672, by rfl⟩ : syracuseStep 855563 = 1283345) B1283345
theorem B855575 : Blo 854356 855575 := bstep (se 1 (by rfl) ⟨641681, by rfl⟩ : syracuseStep 855575 = 1283363) B1283363
theorem B855595 : Blo 854356 855595 := bstep (se 1 (by rfl) ⟨641696, by rfl⟩ : syracuseStep 855595 = 1283393) B1283393
theorem B855607 : Blo 854356 855607 := bstep (se 1 (by rfl) ⟨641705, by rfl⟩ : syracuseStep 855607 = 1283411) B1283411
theorem B1543745 : Blo 854356 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B1281611 : Blo 854356 1281611 := bstep (se 1 (by rfl) ⟨961208, by rfl⟩ : syracuseStep 1281611 = 1922417) B1922417
theorem B855627 : Blo 854356 855627 := bstep (se 1 (by rfl) ⟨641720, by rfl⟩ : syracuseStep 855627 = 1283441) B1283441
theorem B1281623 : Blo 854356 1281623 := bstep (se 1 (by rfl) ⟨961217, by rfl⟩ : syracuseStep 1281623 = 1922435) B1922435
theorem B855639 : Blo 854356 855639 := bstep (se 1 (by rfl) ⟨641729, by rfl⟩ : syracuseStep 855639 = 1283459) B1283459
theorem B1445465 : Blo 854356 1445465 := bstep (se 2 (by rfl) ⟨542049, by rfl⟩ : syracuseStep 1445465 = 1084099) B1084099
theorem B1085015 : Blo 854356 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B855659 : Blo 854356 855659 := bstep (se 1 (by rfl) ⟨641744, by rfl⟩ : syracuseStep 855659 = 1283489) B1283489
theorem B855671 : Blo 854356 855671 := bstep (se 1 (by rfl) ⟨641753, by rfl⟩ : syracuseStep 855671 = 1283507) B1283507
theorem B855691 : Blo 854356 855691 := bstep (se 1 (by rfl) ⟨641768, by rfl⟩ : syracuseStep 855691 = 1283537) B1283537
theorem B855703 : Blo 854356 855703 := bstep (se 1 (by rfl) ⟨641777, by rfl⟩ : syracuseStep 855703 = 1283555) B1283555
theorem B9768599 : Blo 854356 9768599 := bstep (se 1 (by rfl) ⟨7326449, by rfl⟩ : syracuseStep 9768599 = 14652899) B14652899
theorem B1281689 : Blo 854356 1281689 := bstep (se 2 (by rfl) ⟨480633, by rfl⟩ : syracuseStep 1281689 = 961267) B961267
theorem B855723 : Blo 854356 855723 := bstep (se 1 (by rfl) ⟨641792, by rfl⟩ : syracuseStep 855723 = 1283585) B1283585
theorem B855735 : Blo 854356 855735 := bstep (se 1 (by rfl) ⟨641801, by rfl⟩ : syracuseStep 855735 = 1283603) B1283603
theorem B855755 : Blo 854356 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B855767 : Blo 854356 855767 := bstep (se 1 (by rfl) ⟨641825, by rfl⟩ : syracuseStep 855767 = 1283651) B1283651
theorem B1445593 : Blo 854356 1445593 := bstep (se 2 (by rfl) ⟨542097, by rfl⟩ : syracuseStep 1445593 = 1084195) B1084195
theorem B855787 : Blo 854356 855787 := bstep (se 1 (by rfl) ⟨641840, by rfl⟩ : syracuseStep 855787 = 1283681) B1283681
theorem B855799 : Blo 854356 855799 := bstep (se 1 (by rfl) ⟨641849, by rfl⟩ : syracuseStep 855799 = 1283699) B1283699
theorem B1281803 : Blo 854356 1281803 := bstep (se 1 (by rfl) ⟨961352, by rfl⟩ : syracuseStep 1281803 = 1922705) B1922705
theorem B855819 : Blo 854356 855819 := bstep (se 1 (by rfl) ⟨641864, by rfl⟩ : syracuseStep 855819 = 1283729) B1283729
theorem B1281815 : Blo 854356 1281815 := bstep (se 1 (by rfl) ⟨961361, by rfl⟩ : syracuseStep 1281815 = 1922723) B1922723
theorem B855831 : Blo 854356 855831 := bstep (se 1 (by rfl) ⟨641873, by rfl⟩ : syracuseStep 855831 = 1283747) B1283747
theorem B855851 : Blo 854356 855851 := bstep (se 1 (by rfl) ⟨641888, by rfl⟩ : syracuseStep 855851 = 1283777) B1283777
theorem B855863 : Blo 854356 855863 := bstep (se 1 (by rfl) ⟨641897, by rfl⟩ : syracuseStep 855863 = 1283795) B1283795
theorem B855883 : Blo 854356 855883 := bstep (se 1 (by rfl) ⟨641912, by rfl⟩ : syracuseStep 855883 = 1283825) B1283825
theorem B855895 : Blo 854356 855895 := bstep (se 1 (by rfl) ⟨641921, by rfl⟩ : syracuseStep 855895 = 1283843) B1283843
theorem B1281881 : Blo 854356 1281881 := bstep (se 2 (by rfl) ⟨480705, by rfl⟩ : syracuseStep 1281881 = 961411) B961411
theorem B855915 : Blo 854356 855915 := bstep (se 1 (by rfl) ⟨641936, by rfl⟩ : syracuseStep 855915 = 1283873) B1283873
theorem B855927 : Blo 854356 855927 := bstep (se 1 (by rfl) ⟨641945, by rfl⟩ : syracuseStep 855927 = 1283891) B1283891
theorem B855947 : Blo 854356 855947 := bstep (se 1 (by rfl) ⟨641960, by rfl⟩ : syracuseStep 855947 = 1283921) B1283921
theorem B855959 : Blo 854356 855959 := bstep (se 1 (by rfl) ⟨641969, by rfl⟩ : syracuseStep 855959 = 1283939) B1283939
theorem B855979 : Blo 854356 855979 := bstep (se 1 (by rfl) ⟨641984, by rfl⟩ : syracuseStep 855979 = 1283969) B1283969
theorem B3248045 : Blo 854356 3248045 := bstep (se 3 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 3248045 = 1218017) B1218017
theorem B855991 : Blo 854356 855991 := bstep (se 1 (by rfl) ⟨641993, by rfl⟩ : syracuseStep 855991 = 1283987) B1283987
theorem B1281995 : Blo 854356 1281995 := bstep (se 1 (by rfl) ⟨961496, by rfl⟩ : syracuseStep 1281995 = 1922993) B1922993
theorem B856011 : Blo 854356 856011 := bstep (se 1 (by rfl) ⟨642008, by rfl⟩ : syracuseStep 856011 = 1284017) B1284017
theorem B1282007 : Blo 854356 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B856023 : Blo 854356 856023 := bstep (se 1 (by rfl) ⟨642017, by rfl⟩ : syracuseStep 856023 = 1284035) B1284035
theorem B856043 : Blo 854356 856043 := bstep (se 1 (by rfl) ⟨642032, by rfl⟩ : syracuseStep 856043 = 1284065) B1284065
theorem B856055 : Blo 854356 856055 := bstep (se 1 (by rfl) ⟨642041, by rfl⟩ : syracuseStep 856055 = 1284083) B1284083
theorem B856075 : Blo 854356 856075 := bstep (se 1 (by rfl) ⟨642056, by rfl⟩ : syracuseStep 856075 = 1284113) B1284113
theorem B2887703 : Blo 854356 2887703 := bstep (se 1 (by rfl) ⟨2165777, by rfl⟩ : syracuseStep 2887703 = 4331555) B4331555
theorem B1282073 : Blo 854356 1282073 := bstep (se 2 (by rfl) ⟨480777, by rfl⟩ : syracuseStep 1282073 = 961555) B961555
theorem B856087 : Blo 854356 856087 := bstep (se 1 (by rfl) ⟨642065, by rfl⟩ : syracuseStep 856087 = 1284131) B1284131
theorem B856107 : Blo 854356 856107 := bstep (se 1 (by rfl) ⟨642080, by rfl⟩ : syracuseStep 856107 = 1284161) B1284161
theorem B856119 : Blo 854356 856119 := bstep (se 1 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 856119 = 1284179) B1284179
theorem B856139 : Blo 854356 856139 := bstep (se 1 (by rfl) ⟨642104, by rfl⟩ : syracuseStep 856139 = 1284209) B1284209
theorem B856151 : Blo 854356 856151 := bstep (se 1 (by rfl) ⟨642113, by rfl⟩ : syracuseStep 856151 = 1284227) B1284227
theorem B6951005 : Blo 854356 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B856171 : Blo 854356 856171 := bstep (se 1 (by rfl) ⟨642128, by rfl⟩ : syracuseStep 856171 = 1284257) B1284257
theorem B856183 : Blo 854356 856183 := bstep (se 1 (by rfl) ⟨642137, by rfl⟩ : syracuseStep 856183 = 1284275) B1284275
theorem B1282187 : Blo 854356 1282187 := bstep (se 1 (by rfl) ⟨961640, by rfl⟩ : syracuseStep 1282187 = 1923281) B1923281
theorem B856203 : Blo 854356 856203 := bstep (se 1 (by rfl) ⟨642152, by rfl⟩ : syracuseStep 856203 = 1284305) B1284305
theorem B1282199 : Blo 854356 1282199 := bstep (se 1 (by rfl) ⟨961649, by rfl⟩ : syracuseStep 1282199 = 1923299) B1923299
theorem B856215 : Blo 854356 856215 := bstep (se 1 (by rfl) ⟨642161, by rfl⟩ : syracuseStep 856215 = 1284323) B1284323
theorem B856235 : Blo 854356 856235 := bstep (se 1 (by rfl) ⟨642176, by rfl⟩ : syracuseStep 856235 = 1284353) B1284353
theorem B856247 : Blo 854356 856247 := bstep (se 1 (by rfl) ⟨642185, by rfl⟩ : syracuseStep 856247 = 1284371) B1284371
theorem B856267 : Blo 854356 856267 := bstep (se 1 (by rfl) ⟨642200, by rfl⟩ : syracuseStep 856267 = 1284401) B1284401
theorem B856279 : Blo 854356 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B1282265 : Blo 854356 1282265 := bstep (se 2 (by rfl) ⟨480849, by rfl⟩ : syracuseStep 1282265 = 961699) B961699
theorem B856299 : Blo 854356 856299 := bstep (se 1 (by rfl) ⟨642224, by rfl⟩ : syracuseStep 856299 = 1284449) B1284449
theorem B856311 : Blo 854356 856311 := bstep (se 1 (by rfl) ⟨642233, by rfl⟩ : syracuseStep 856311 = 1284467) B1284467
theorem B856331 : Blo 854356 856331 := bstep (se 1 (by rfl) ⟨642248, by rfl⟩ : syracuseStep 856331 = 1284497) B1284497
theorem B856343 : Blo 854356 856343 := bstep (se 1 (by rfl) ⟨642257, by rfl⟩ : syracuseStep 856343 = 1284515) B1284515
theorem B1446167 : Blo 854356 1446167 := bstep (se 1 (by rfl) ⟨1084625, by rfl⟩ : syracuseStep 1446167 = 2169251) B2169251
theorem B1085719 : Blo 854356 1085719 := bstep (se 1 (by rfl) ⟨814289, by rfl⟩ : syracuseStep 1085719 = 1628579) B1628579
theorem B856363 : Blo 854356 856363 := bstep (se 1 (by rfl) ⟨642272, by rfl⟩ : syracuseStep 856363 = 1284545) B1284545
theorem B4329773 : Blo 854356 4329773 := bstep (se 3 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 4329773 = 1623665) B1623665
theorem B856375 : Blo 854356 856375 := bstep (se 1 (by rfl) ⟨642281, by rfl⟩ : syracuseStep 856375 = 1284563) B1284563
theorem B1282379 : Blo 854356 1282379 := bstep (se 1 (by rfl) ⟨961784, by rfl⟩ : syracuseStep 1282379 = 1923569) B1923569
theorem B856395 : Blo 854356 856395 := bstep (se 1 (by rfl) ⟨642296, by rfl⟩ : syracuseStep 856395 = 1284593) B1284593
theorem B1282391 : Blo 854356 1282391 := bstep (se 1 (by rfl) ⟨961793, by rfl⟩ : syracuseStep 1282391 = 1923587) B1923587
theorem B856407 : Blo 854356 856407 := bstep (se 1 (by rfl) ⟨642305, by rfl⟩ : syracuseStep 856407 = 1284611) B1284611
theorem B856427 : Blo 854356 856427 := bstep (se 1 (by rfl) ⟨642320, by rfl⟩ : syracuseStep 856427 = 1284641) B1284641
theorem B856439 : Blo 854356 856439 := bstep (se 1 (by rfl) ⟨642329, by rfl⟩ : syracuseStep 856439 = 1284659) B1284659
theorem B856459 : Blo 854356 856459 := bstep (se 1 (by rfl) ⟨642344, by rfl⟩ : syracuseStep 856459 = 1284689) B1284689
theorem B856471 : Blo 854356 856471 := bstep (se 1 (by rfl) ⟨642353, by rfl⟩ : syracuseStep 856471 = 1284707) B1284707
theorem B1446295 : Blo 854356 1446295 := bstep (se 1 (by rfl) ⟨1084721, by rfl⟩ : syracuseStep 1446295 = 2169443) B2169443
theorem B1282457 : Blo 854356 1282457 := bstep (se 2 (by rfl) ⟨480921, by rfl⟩ : syracuseStep 1282457 = 961843) B961843
theorem B856491 : Blo 854356 856491 := bstep (se 1 (by rfl) ⟨642368, by rfl⟩ : syracuseStep 856491 = 1284737) B1284737
theorem B856503 : Blo 854356 856503 := bstep (se 1 (by rfl) ⟨642377, by rfl⟩ : syracuseStep 856503 = 1284755) B1284755
theorem B856523 : Blo 854356 856523 := bstep (se 1 (by rfl) ⟨642392, by rfl⟩ : syracuseStep 856523 = 1284785) B1284785
theorem B856535 : Blo 854356 856535 := bstep (se 1 (by rfl) ⟨642401, by rfl⟩ : syracuseStep 856535 = 1284803) B1284803
theorem B856555 : Blo 854356 856555 := bstep (se 1 (by rfl) ⟨642416, by rfl⟩ : syracuseStep 856555 = 1284833) B1284833
theorem B856567 : Blo 854356 856567 := bstep (se 1 (by rfl) ⟨642425, by rfl⟩ : syracuseStep 856567 = 1284851) B1284851
theorem B1282571 : Blo 854356 1282571 := bstep (se 1 (by rfl) ⟨961928, by rfl⟩ : syracuseStep 1282571 = 1923857) B1923857
theorem B856587 : Blo 854356 856587 := bstep (se 1 (by rfl) ⟨642440, by rfl⟩ : syracuseStep 856587 = 1284881) B1284881
theorem B1282583 : Blo 854356 1282583 := bstep (se 1 (by rfl) ⟨961937, by rfl⟩ : syracuseStep 1282583 = 1923875) B1923875
theorem B856599 : Blo 854356 856599 := bstep (se 1 (by rfl) ⟨642449, by rfl⟩ : syracuseStep 856599 = 1284899) B1284899
theorem B856619 : Blo 854356 856619 := bstep (se 1 (by rfl) ⟨642464, by rfl⟩ : syracuseStep 856619 = 1284929) B1284929
theorem B2888243 : Blo 854356 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B856631 : Blo 854356 856631 := bstep (se 1 (by rfl) ⟨642473, by rfl⟩ : syracuseStep 856631 = 1284947) B1284947
theorem B856651 : Blo 854356 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B1217111 : Blo 854356 1217111 := bstep (se 1 (by rfl) ⟨912833, by rfl⟩ : syracuseStep 1217111 = 1825667) B1825667
theorem B856663 : Blo 854356 856663 := bstep (se 1 (by rfl) ⟨642497, by rfl⟩ : syracuseStep 856663 = 1284995) B1284995
theorem B1282649 : Blo 854356 1282649 := bstep (se 2 (by rfl) ⟨480993, by rfl⟩ : syracuseStep 1282649 = 961987) B961987
theorem B6165085 : Blo 854356 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B856683 : Blo 854356 856683 := bstep (se 1 (by rfl) ⟨642512, by rfl⟩ : syracuseStep 856683 = 1285025) B1285025
theorem B856695 : Blo 854356 856695 := bstep (se 1 (by rfl) ⟨642521, by rfl⟩ : syracuseStep 856695 = 1285043) B1285043
theorem B856715 : Blo 854356 856715 := bstep (se 1 (by rfl) ⟨642536, by rfl⟩ : syracuseStep 856715 = 1285073) B1285073
theorem B856727 : Blo 854356 856727 := bstep (se 1 (by rfl) ⟨642545, by rfl⟩ : syracuseStep 856727 = 1285091) B1285091
theorem B856747 : Blo 854356 856747 := bstep (se 1 (by rfl) ⟨642560, by rfl⟩ : syracuseStep 856747 = 1285121) B1285121
theorem B3248819 : Blo 854356 3248819 := bstep (se 1 (by rfl) ⟨2436614, by rfl⟩ : syracuseStep 3248819 = 4873229) B4873229
theorem B856759 : Blo 854356 856759 := bstep (se 1 (by rfl) ⟨642569, by rfl⟩ : syracuseStep 856759 = 1285139) B1285139
theorem B1282763 : Blo 854356 1282763 := bstep (se 1 (by rfl) ⟨962072, by rfl⟩ : syracuseStep 1282763 = 1924145) B1924145
theorem B2167499 : Blo 854356 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B856779 : Blo 854356 856779 := bstep (se 1 (by rfl) ⟨642584, by rfl⟩ : syracuseStep 856779 = 1285169) B1285169
theorem B1282775 : Blo 854356 1282775 := bstep (se 1 (by rfl) ⟨962081, by rfl⟩ : syracuseStep 1282775 = 1924163) B1924163
theorem B856791 : Blo 854356 856791 := bstep (se 1 (by rfl) ⟨642593, by rfl⟩ : syracuseStep 856791 = 1285187) B1285187
theorem B4625113 : Blo 854356 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B856811 : Blo 854356 856811 := bstep (se 1 (by rfl) ⟨642608, by rfl⟩ : syracuseStep 856811 = 1285217) B1285217
theorem B856823 : Blo 854356 856823 := bstep (se 1 (by rfl) ⟨642617, by rfl⟩ : syracuseStep 856823 = 1285235) B1285235
theorem B856843 : Blo 854356 856843 := bstep (se 1 (by rfl) ⟨642632, by rfl⟩ : syracuseStep 856843 = 1285265) B1285265
theorem B856855 : Blo 854356 856855 := bstep (se 1 (by rfl) ⟨642641, by rfl⟩ : syracuseStep 856855 = 1285283) B1285283
theorem B1217305 : Blo 854356 1217305 := bstep (se 2 (by rfl) ⟨456489, by rfl⟩ : syracuseStep 1217305 = 912979) B912979
theorem B1282841 : Blo 854356 1282841 := bstep (se 2 (by rfl) ⟨481065, by rfl⟩ : syracuseStep 1282841 = 962131) B962131
theorem B856875 : Blo 854356 856875 := bstep (se 1 (by rfl) ⟨642656, by rfl⟩ : syracuseStep 856875 = 1285313) B1285313
theorem B856887 : Blo 854356 856887 := bstep (se 1 (by rfl) ⟨642665, by rfl⟩ : syracuseStep 856887 = 1285331) B1285331
theorem B2888513 : Blo 854356 2888513 := bstep (se 2 (by rfl) ⟨1083192, by rfl⟩ : syracuseStep 2888513 = 2166385) B2166385
theorem B856907 : Blo 854356 856907 := bstep (se 1 (by rfl) ⟨642680, by rfl⟩ : syracuseStep 856907 = 1285361) B1285361
theorem B856919 : Blo 854356 856919 := bstep (se 1 (by rfl) ⟨642689, by rfl⟩ : syracuseStep 856919 = 1285379) B1285379
theorem B856939 : Blo 854356 856939 := bstep (se 1 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 856939 = 1285409) B1285409
theorem B856951 : Blo 854356 856951 := bstep (se 1 (by rfl) ⟨642713, by rfl⟩ : syracuseStep 856951 = 1285427) B1285427
theorem B1282955 : Blo 854356 1282955 := bstep (se 1 (by rfl) ⟨962216, by rfl⟩ : syracuseStep 1282955 = 1924433) B1924433
theorem B856971 : Blo 854356 856971 := bstep (se 1 (by rfl) ⟨642728, by rfl⟩ : syracuseStep 856971 = 1285457) B1285457
theorem B1282967 : Blo 854356 1282967 := bstep (se 1 (by rfl) ⟨962225, by rfl⟩ : syracuseStep 1282967 = 1924451) B1924451
theorem B856983 : Blo 854356 856983 := bstep (se 1 (by rfl) ⟨642737, by rfl⟩ : syracuseStep 856983 = 1285475) B1285475
theorem B857003 : Blo 854356 857003 := bstep (se 1 (by rfl) ⟨642752, by rfl⟩ : syracuseStep 857003 = 1285505) B1285505
theorem B857015 : Blo 854356 857015 := bstep (se 1 (by rfl) ⟨642761, by rfl⟩ : syracuseStep 857015 = 1285523) B1285523
theorem B857035 : Blo 854356 857035 := bstep (se 1 (by rfl) ⟨642776, by rfl⟩ : syracuseStep 857035 = 1285553) B1285553
theorem B857047 : Blo 854356 857047 := bstep (se 1 (by rfl) ⟨642785, by rfl⟩ : syracuseStep 857047 = 1285571) B1285571
theorem B1283033 : Blo 854356 1283033 := bstep (se 2 (by rfl) ⟨481137, by rfl⟩ : syracuseStep 1283033 = 962275) B962275
theorem B857067 : Blo 854356 857067 := bstep (se 1 (by rfl) ⟨642800, by rfl⟩ : syracuseStep 857067 = 1285601) B1285601
theorem B857079 : Blo 854356 857079 := bstep (se 1 (by rfl) ⟨642809, by rfl⟩ : syracuseStep 857079 = 1285619) B1285619
theorem B857099 : Blo 854356 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B1446923 : Blo 854356 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B857111 : Blo 854356 857111 := bstep (se 1 (by rfl) ⟨642833, by rfl⟩ : syracuseStep 857111 = 1285667) B1285667
theorem B8229923 : Blo 854356 8229923 := bstep (se 1 (by rfl) ⟨6172442, by rfl⟩ : syracuseStep 8229923 = 12344885) B12344885
theorem B857131 : Blo 854356 857131 := bstep (se 1 (by rfl) ⟨642848, by rfl⟩ : syracuseStep 857131 = 1285697) B1285697
theorem B857143 : Blo 854356 857143 := bstep (se 1 (by rfl) ⟨642857, by rfl⟩ : syracuseStep 857143 = 1285715) B1285715
theorem B1283147 : Blo 854356 1283147 := bstep (se 1 (by rfl) ⟨962360, by rfl⟩ : syracuseStep 1283147 = 1924721) B1924721
theorem B857163 : Blo 854356 857163 := bstep (se 1 (by rfl) ⟨642872, by rfl⟩ : syracuseStep 857163 = 1285745) B1285745
theorem B1283159 : Blo 854356 1283159 := bstep (se 1 (by rfl) ⟨962369, by rfl⟩ : syracuseStep 1283159 = 1924739) B1924739
theorem B857175 : Blo 854356 857175 := bstep (se 1 (by rfl) ⟨642881, by rfl⟩ : syracuseStep 857175 = 1285763) B1285763
theorem B857195 : Blo 854356 857195 := bstep (se 1 (by rfl) ⟨642896, by rfl⟩ : syracuseStep 857195 = 1285793) B1285793
theorem B857207 : Blo 854356 857207 := bstep (se 1 (by rfl) ⟨642905, by rfl⟩ : syracuseStep 857207 = 1285811) B1285811
theorem B857227 : Blo 854356 857227 := bstep (se 1 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 857227 = 1285841) B1285841
theorem B1447051 : Blo 854356 1447051 := bstep (se 1 (by rfl) ⟨1085288, by rfl⟩ : syracuseStep 1447051 = 2170577) B2170577
theorem B857239 : Blo 854356 857239 := bstep (se 1 (by rfl) ⟨642929, by rfl⟩ : syracuseStep 857239 = 1285859) B1285859
theorem B1283225 : Blo 854356 1283225 := bstep (se 2 (by rfl) ⟨481209, by rfl⟩ : syracuseStep 1283225 = 962419) B962419
theorem B857259 : Blo 854356 857259 := bstep (se 1 (by rfl) ⟨642944, by rfl⟩ : syracuseStep 857259 = 1285889) B1285889
theorem B857271 : Blo 854356 857271 := bstep (se 1 (by rfl) ⟨642953, by rfl⟩ : syracuseStep 857271 = 1285907) B1285907
theorem B857291 : Blo 854356 857291 := bstep (se 1 (by rfl) ⟨642968, by rfl⟩ : syracuseStep 857291 = 1285937) B1285937
theorem B857303 : Blo 854356 857303 := bstep (se 1 (by rfl) ⟨642977, by rfl⟩ : syracuseStep 857303 = 1285955) B1285955
theorem B857323 : Blo 854356 857323 := bstep (se 1 (by rfl) ⟨642992, by rfl⟩ : syracuseStep 857323 = 1285985) B1285985
theorem B857335 : Blo 854356 857335 := bstep (se 1 (by rfl) ⟨643001, by rfl⟩ : syracuseStep 857335 = 1286003) B1286003
theorem B6493445 : Blo 854356 6493445 := bstep (se 4 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 6493445 = 1217521) B1217521
theorem B1283339 : Blo 854356 1283339 := bstep (se 1 (by rfl) ⟨962504, by rfl⟩ : syracuseStep 1283339 = 1925009) B1925009
theorem B857355 : Blo 854356 857355 := bstep (se 1 (by rfl) ⟨643016, by rfl⟩ : syracuseStep 857355 = 1286033) B1286033
theorem B1283351 : Blo 854356 1283351 := bstep (se 1 (by rfl) ⟨962513, by rfl⟩ : syracuseStep 1283351 = 1925027) B1925027
theorem B857367 : Blo 854356 857367 := bstep (se 1 (by rfl) ⟨643025, by rfl⟩ : syracuseStep 857367 = 1286051) B1286051
theorem B1447193 : Blo 854356 1447193 := bstep (se 2 (by rfl) ⟨542697, by rfl⟩ : syracuseStep 1447193 = 1085395) B1085395
theorem B857387 : Blo 854356 857387 := bstep (se 1 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 857387 = 1286081) B1286081
theorem B857399 : Blo 854356 857399 := bstep (se 1 (by rfl) ⟨643049, by rfl⟩ : syracuseStep 857399 = 1286099) B1286099
theorem B857419 : Blo 854356 857419 := bstep (se 1 (by rfl) ⟨643064, by rfl⟩ : syracuseStep 857419 = 1286129) B1286129
theorem B857431 : Blo 854356 857431 := bstep (se 1 (by rfl) ⟨643073, by rfl⟩ : syracuseStep 857431 = 1286147) B1286147
theorem B1283417 : Blo 854356 1283417 := bstep (se 2 (by rfl) ⟨481281, by rfl⟩ : syracuseStep 1283417 = 962563) B962563
theorem B2889053 : Blo 854356 2889053 := bstep (se 3 (by rfl) ⟨541697, by rfl⟩ : syracuseStep 2889053 = 1083395) B1083395
theorem B857451 : Blo 854356 857451 := bstep (se 1 (by rfl) ⟨643088, by rfl⟩ : syracuseStep 857451 = 1286177) B1286177
theorem B857463 : Blo 854356 857463 := bstep (se 1 (by rfl) ⟨643097, by rfl⟩ : syracuseStep 857463 = 1286195) B1286195
theorem B857483 : Blo 854356 857483 := bstep (se 1 (by rfl) ⟨643112, by rfl⟩ : syracuseStep 857483 = 1286225) B1286225
theorem B857495 : Blo 854356 857495 := bstep (se 1 (by rfl) ⟨643121, by rfl⟩ : syracuseStep 857495 = 1286243) B1286243
theorem B1447321 : Blo 854356 1447321 := bstep (se 2 (by rfl) ⟨542745, by rfl⟩ : syracuseStep 1447321 = 1085491) B1085491
theorem B857515 : Blo 854356 857515 := bstep (se 1 (by rfl) ⟨643136, by rfl⟩ : syracuseStep 857515 = 1286273) B1286273
theorem B857527 : Blo 854356 857527 := bstep (se 1 (by rfl) ⟨643145, by rfl⟩ : syracuseStep 857527 = 1286291) B1286291
theorem B1283531 : Blo 854356 1283531 := bstep (se 1 (by rfl) ⟨962648, by rfl⟩ : syracuseStep 1283531 = 1925297) B1925297
theorem B857547 : Blo 854356 857547 := bstep (se 1 (by rfl) ⟨643160, by rfl⟩ : syracuseStep 857547 = 1286321) B1286321
theorem B1283543 : Blo 854356 1283543 := bstep (se 1 (by rfl) ⟨962657, by rfl⟩ : syracuseStep 1283543 = 1925315) B1925315
theorem B857559 : Blo 854356 857559 := bstep (se 1 (by rfl) ⟨643169, by rfl⟩ : syracuseStep 857559 = 1286339) B1286339
theorem B857579 : Blo 854356 857579 := bstep (se 1 (by rfl) ⟨643184, by rfl⟩ : syracuseStep 857579 = 1286369) B1286369
theorem B857591 : Blo 854356 857591 := bstep (se 1 (by rfl) ⟨643193, by rfl⟩ : syracuseStep 857591 = 1286387) B1286387
theorem B857611 : Blo 854356 857611 := bstep (se 1 (by rfl) ⟨643208, by rfl⟩ : syracuseStep 857611 = 1286417) B1286417
theorem B857623 : Blo 854356 857623 := bstep (se 1 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 857623 = 1286435) B1286435
theorem B1283609 : Blo 854356 1283609 := bstep (se 2 (by rfl) ⟨481353, by rfl⟩ : syracuseStep 1283609 = 962707) B962707
theorem B857643 : Blo 854356 857643 := bstep (se 1 (by rfl) ⟨643232, by rfl⟩ : syracuseStep 857643 = 1286465) B1286465
theorem B857655 : Blo 854356 857655 := bstep (se 1 (by rfl) ⟨643241, by rfl⟩ : syracuseStep 857655 = 1286483) B1286483
theorem B857675 : Blo 854356 857675 := bstep (se 1 (by rfl) ⟨643256, by rfl⟩ : syracuseStep 857675 = 1286513) B1286513
theorem B857687 : Blo 854356 857687 := bstep (se 1 (by rfl) ⟨643265, by rfl⟩ : syracuseStep 857687 = 1286531) B1286531
theorem B857707 : Blo 854356 857707 := bstep (se 1 (by rfl) ⟨643280, by rfl⟩ : syracuseStep 857707 = 1286561) B1286561
theorem B857719 : Blo 854356 857719 := bstep (se 1 (by rfl) ⟨643289, by rfl⟩ : syracuseStep 857719 = 1286579) B1286579
theorem B1283723 : Blo 854356 1283723 := bstep (se 1 (by rfl) ⟨962792, by rfl⟩ : syracuseStep 1283723 = 1925585) B1925585
theorem B857739 : Blo 854356 857739 := bstep (se 1 (by rfl) ⟨643304, by rfl⟩ : syracuseStep 857739 = 1286609) B1286609
theorem B1283735 : Blo 854356 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B2168471 : Blo 854356 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B857751 : Blo 854356 857751 := bstep (se 1 (by rfl) ⟨643313, by rfl⟩ : syracuseStep 857751 = 1286627) B1286627
theorem B857771 : Blo 854356 857771 := bstep (se 1 (by rfl) ⟨643328, by rfl⟩ : syracuseStep 857771 = 1286657) B1286657
theorem B857783 : Blo 854356 857783 := bstep (se 1 (by rfl) ⟨643337, by rfl⟩ : syracuseStep 857783 = 1286675) B1286675
theorem B857803 : Blo 854356 857803 := bstep (se 1 (by rfl) ⟨643352, by rfl⟩ : syracuseStep 857803 = 1286705) B1286705
theorem B857815 : Blo 854356 857815 := bstep (se 1 (by rfl) ⟨643361, by rfl⟩ : syracuseStep 857815 = 1286723) B1286723
theorem B1283801 : Blo 854356 1283801 := bstep (se 2 (by rfl) ⟨481425, by rfl⟩ : syracuseStep 1283801 = 962851) B962851
theorem B857835 : Blo 854356 857835 := bstep (se 1 (by rfl) ⟨643376, by rfl⟩ : syracuseStep 857835 = 1286753) B1286753
theorem B857847 : Blo 854356 857847 := bstep (se 1 (by rfl) ⟨643385, by rfl⟩ : syracuseStep 857847 = 1286771) B1286771
theorem B857867 : Blo 854356 857867 := bstep (se 1 (by rfl) ⟨643400, by rfl⟩ : syracuseStep 857867 = 1286801) B1286801
theorem B857879 : Blo 854356 857879 := bstep (se 1 (by rfl) ⟨643409, by rfl⟩ : syracuseStep 857879 = 1286819) B1286819
theorem B1644313 : Blo 854356 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B857899 : Blo 854356 857899 := bstep (se 1 (by rfl) ⟨643424, by rfl⟩ : syracuseStep 857899 = 1286849) B1286849
theorem B857911 : Blo 854356 857911 := bstep (se 1 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 857911 = 1286867) B1286867
theorem B1283915 : Blo 854356 1283915 := bstep (se 1 (by rfl) ⟨962936, by rfl⟩ : syracuseStep 1283915 = 1925873) B1925873
theorem B857931 : Blo 854356 857931 := bstep (se 1 (by rfl) ⟨643448, by rfl⟩ : syracuseStep 857931 = 1286897) B1286897
theorem B1283927 : Blo 854356 1283927 := bstep (se 1 (by rfl) ⟨962945, by rfl⟩ : syracuseStep 1283927 = 1925891) B1925891
theorem B857943 : Blo 854356 857943 := bstep (se 1 (by rfl) ⟨643457, by rfl⟩ : syracuseStep 857943 = 1286915) B1286915
theorem B857963 : Blo 854356 857963 := bstep (se 1 (by rfl) ⟨643472, by rfl⟩ : syracuseStep 857963 = 1286945) B1286945
theorem B857975 : Blo 854356 857975 := bstep (se 1 (by rfl) ⟨643481, by rfl⟩ : syracuseStep 857975 = 1286963) B1286963
theorem B857995 : Blo 854356 857995 := bstep (se 1 (by rfl) ⟨643496, by rfl⟩ : syracuseStep 857995 = 1286993) B1286993
theorem B858007 : Blo 854356 858007 := bstep (se 1 (by rfl) ⟨643505, by rfl⟩ : syracuseStep 858007 = 1287011) B1287011
theorem B1283993 : Blo 854356 1283993 := bstep (se 2 (by rfl) ⟨481497, by rfl⟩ : syracuseStep 1283993 = 962995) B962995
theorem B858027 : Blo 854356 858027 := bstep (se 1 (by rfl) ⟨643520, by rfl⟩ : syracuseStep 858027 = 1287041) B1287041
theorem B858039 : Blo 854356 858039 := bstep (se 1 (by rfl) ⟨643529, by rfl⟩ : syracuseStep 858039 = 1287059) B1287059
theorem B858059 : Blo 854356 858059 := bstep (se 1 (by rfl) ⟨643544, by rfl⟩ : syracuseStep 858059 = 1287089) B1287089
theorem B1447895 : Blo 854356 1447895 := bstep (se 1 (by rfl) ⟨1085921, by rfl⟩ : syracuseStep 1447895 = 2171843) B2171843
theorem B858071 : Blo 854356 858071 := bstep (se 1 (by rfl) ⟨643553, by rfl⟩ : syracuseStep 858071 = 1287107) B1287107
theorem B858091 : Blo 854356 858091 := bstep (se 1 (by rfl) ⟨643568, by rfl⟩ : syracuseStep 858091 = 1287137) B1287137
theorem B858103 : Blo 854356 858103 := bstep (se 1 (by rfl) ⟨643577, by rfl⟩ : syracuseStep 858103 = 1287155) B1287155
theorem B1284107 : Blo 854356 1284107 := bstep (se 1 (by rfl) ⟨963080, by rfl⟩ : syracuseStep 1284107 = 1926161) B1926161
theorem B858123 : Blo 854356 858123 := bstep (se 1 (by rfl) ⟨643592, by rfl⟩ : syracuseStep 858123 = 1287185) B1287185
theorem B1284119 : Blo 854356 1284119 := bstep (se 1 (by rfl) ⟨963089, by rfl⟩ : syracuseStep 1284119 = 1926179) B1926179
theorem B858135 : Blo 854356 858135 := bstep (se 1 (by rfl) ⟨643601, by rfl⟩ : syracuseStep 858135 = 1287203) B1287203
theorem B858155 : Blo 854356 858155 := bstep (se 1 (by rfl) ⟨643616, by rfl⟩ : syracuseStep 858155 = 1287233) B1287233
theorem B858167 : Blo 854356 858167 := bstep (se 1 (by rfl) ⟨643625, by rfl⟩ : syracuseStep 858167 = 1287251) B1287251
theorem B4626497 : Blo 854356 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B858187 : Blo 854356 858187 := bstep (se 1 (by rfl) ⟨643640, by rfl⟩ : syracuseStep 858187 = 1287281) B1287281
theorem B1448023 : Blo 854356 1448023 := bstep (se 1 (by rfl) ⟨1086017, by rfl⟩ : syracuseStep 1448023 = 2172035) B2172035
theorem B858199 : Blo 854356 858199 := bstep (se 1 (by rfl) ⟨643649, by rfl⟩ : syracuseStep 858199 = 1287299) B1287299
theorem B1284185 : Blo 854356 1284185 := bstep (se 2 (by rfl) ⟨481569, by rfl⟩ : syracuseStep 1284185 = 963139) B963139
theorem B858219 : Blo 854356 858219 := bstep (se 1 (by rfl) ⟨643664, by rfl⟩ : syracuseStep 858219 = 1287329) B1287329
theorem B858231 : Blo 854356 858231 := bstep (se 1 (by rfl) ⟨643673, by rfl⟩ : syracuseStep 858231 = 1287347) B1287347
theorem B3250307 : Blo 854356 3250307 := bstep (se 1 (by rfl) ⟨2437730, by rfl⟩ : syracuseStep 3250307 = 4875461) B4875461
theorem B858251 : Blo 854356 858251 := bstep (se 1 (by rfl) ⟨643688, by rfl⟩ : syracuseStep 858251 = 1287377) B1287377
theorem B858263 : Blo 854356 858263 := bstep (se 1 (by rfl) ⟨643697, by rfl⟩ : syracuseStep 858263 = 1287395) B1287395
theorem B858283 : Blo 854356 858283 := bstep (se 1 (by rfl) ⟨643712, by rfl⟩ : syracuseStep 858283 = 1287425) B1287425
theorem B858295 : Blo 854356 858295 := bstep (se 1 (by rfl) ⟨643721, by rfl⟩ : syracuseStep 858295 = 1287443) B1287443
theorem B1218763 : Blo 854356 1218763 := bstep (se 1 (by rfl) ⟨914072, by rfl⟩ : syracuseStep 1218763 = 1828145) B1828145
theorem B1284299 : Blo 854356 1284299 := bstep (se 1 (by rfl) ⟨963224, by rfl⟩ : syracuseStep 1284299 = 1926449) B1926449
theorem B858315 : Blo 854356 858315 := bstep (se 1 (by rfl) ⟨643736, by rfl⟩ : syracuseStep 858315 = 1287473) B1287473
theorem B1284311 : Blo 854356 1284311 := bstep (se 1 (by rfl) ⟨963233, by rfl⟩ : syracuseStep 1284311 = 1926467) B1926467
theorem B858327 : Blo 854356 858327 := bstep (se 1 (by rfl) ⟨643745, by rfl⟩ : syracuseStep 858327 = 1287491) B1287491
theorem B5478617 : Blo 854356 5478617 := bstep (se 2 (by rfl) ⟨2054481, by rfl⟩ : syracuseStep 5478617 = 4108963) B4108963
theorem B858347 : Blo 854356 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B1284377 : Blo 854356 1284377 := bstep (se 2 (by rfl) ⟨481641, by rfl⟩ : syracuseStep 1284377 = 963283) B963283
theorem B2169139 : Blo 854356 2169139 := bstep (se 1 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 2169139 = 3253709) B3253709
theorem B1284491 : Blo 854356 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B1284503 : Blo 854356 1284503 := bstep (se 1 (by rfl) ⟨963377, by rfl⟩ : syracuseStep 1284503 = 1926755) B1926755
theorem B2169281 : Blo 854356 2169281 := bstep (se 2 (by rfl) ⟨813480, by rfl⟩ : syracuseStep 2169281 = 1626961) B1626961
theorem B2890187 : Blo 854356 2890187 := bstep (se 1 (by rfl) ⟨2167640, by rfl⟩ : syracuseStep 2890187 = 4335281) B4335281
theorem B1284569 : Blo 854356 1284569 := bstep (se 2 (by rfl) ⟨481713, by rfl⟩ : syracuseStep 1284569 = 963427) B963427
theorem B12491333 : Blo 854356 12491333 := bstep (se 4 (by rfl) ⟨1171062, by rfl⟩ : syracuseStep 12491333 = 2342125) B2342125
theorem B3250763 : Blo 854356 3250763 := bstep (se 1 (by rfl) ⟨2438072, by rfl⟩ : syracuseStep 3250763 = 4876145) B4876145
theorem B1284683 : Blo 854356 1284683 := bstep (se 1 (by rfl) ⟨963512, by rfl⟩ : syracuseStep 1284683 = 1927025) B1927025
theorem B1284695 : Blo 854356 1284695 := bstep (se 1 (by rfl) ⟨963521, by rfl⟩ : syracuseStep 1284695 = 1927043) B1927043
theorem B1284761 : Blo 854356 1284761 := bstep (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) B963571
theorem B989911 : Blo 854356 989911 := bstep (se 1 (by rfl) ⟨742433, by rfl⟩ : syracuseStep 989911 = 1484867) B1484867
theorem B2890457 : Blo 854356 2890457 := bstep (se 2 (by rfl) ⟨1083921, by rfl⟩ : syracuseStep 2890457 = 2167843) B2167843
theorem B3906307 : Blo 854356 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B1284875 : Blo 854356 1284875 := bstep (se 1 (by rfl) ⟨963656, by rfl⟩ : syracuseStep 1284875 = 1927313) B1927313
theorem B3250961 : Blo 854356 3250961 := bstep (se 2 (by rfl) ⟨1219110, by rfl⟩ : syracuseStep 3250961 = 2438221) B2438221
theorem B1284887 : Blo 854356 1284887 := bstep (se 1 (by rfl) ⟨963665, by rfl⟩ : syracuseStep 1284887 = 1927331) B1927331
theorem B1284953 : Blo 854356 1284953 := bstep (se 2 (by rfl) ⟨481857, by rfl⟩ : syracuseStep 1284953 = 963715) B963715
theorem B1285067 : Blo 854356 1285067 := bstep (se 1 (by rfl) ⟨963800, by rfl⟩ : syracuseStep 1285067 = 1927601) B1927601
theorem B1285079 : Blo 854356 1285079 := bstep (se 1 (by rfl) ⟨963809, by rfl⟩ : syracuseStep 1285079 = 1927619) B1927619
theorem B16489433 : Blo 854356 16489433 := bstep (se 2 (by rfl) ⟨6183537, by rfl⟩ : syracuseStep 16489433 = 12367075) B12367075
theorem B1285145 : Blo 854356 1285145 := bstep (se 2 (by rfl) ⟨481929, by rfl⟩ : syracuseStep 1285145 = 963859) B963859
theorem B1285259 : Blo 854356 1285259 := bstep (se 1 (by rfl) ⟨963944, by rfl⟩ : syracuseStep 1285259 = 1927889) B1927889
theorem B1285271 : Blo 854356 1285271 := bstep (se 1 (by rfl) ⟨963953, by rfl⟩ : syracuseStep 1285271 = 1927907) B1927907
theorem B13376663 : Blo 854356 13376663 := bstep (se 1 (by rfl) ⟨10032497, by rfl⟩ : syracuseStep 13376663 = 20064995) B20064995
theorem B1285337 : Blo 854356 1285337 := bstep (se 2 (by rfl) ⟨482001, by rfl⟩ : syracuseStep 1285337 = 964003) B964003
theorem B1285451 : Blo 854356 1285451 := bstep (se 1 (by rfl) ⟨964088, by rfl⟩ : syracuseStep 1285451 = 1928177) B1928177
theorem B1285463 : Blo 854356 1285463 := bstep (se 1 (by rfl) ⟨964097, by rfl⟩ : syracuseStep 1285463 = 1928195) B1928195
theorem B2891159 : Blo 854356 2891159 := bstep (se 1 (by rfl) ⟨2168369, by rfl⟩ : syracuseStep 2891159 = 4336739) B4336739
theorem B1285529 : Blo 854356 1285529 := bstep (se 2 (by rfl) ⟨482073, by rfl⟩ : syracuseStep 1285529 = 964147) B964147
theorem B1285643 : Blo 854356 1285643 := bstep (se 1 (by rfl) ⟨964232, by rfl⟩ : syracuseStep 1285643 = 1928465) B1928465
theorem B3251735 : Blo 854356 3251735 := bstep (se 1 (by rfl) ⟨2438801, by rfl⟩ : syracuseStep 3251735 = 4877603) B4877603
theorem B1285655 : Blo 854356 1285655 := bstep (se 1 (by rfl) ⟨964241, by rfl⟩ : syracuseStep 1285655 = 1928483) B1928483
theorem B1285721 : Blo 854356 1285721 := bstep (se 2 (by rfl) ⟨482145, by rfl⟩ : syracuseStep 1285721 = 964291) B964291
theorem B6495875 : Blo 854356 6495875 := bstep (se 1 (by rfl) ⟨4871906, by rfl⟩ : syracuseStep 6495875 = 9743813) B9743813
theorem B2170547 : Blo 854356 2170547 := bstep (se 1 (by rfl) ⟨1627910, by rfl⟩ : syracuseStep 2170547 = 3255821) B3255821
theorem B1285835 : Blo 854356 1285835 := bstep (se 1 (by rfl) ⟨964376, by rfl⟩ : syracuseStep 1285835 = 1928753) B1928753
theorem B10985165 : Blo 854356 10985165 := bstep (se 3 (by rfl) ⟨2059718, by rfl⟩ : syracuseStep 10985165 = 4119437) B4119437
theorem B1285847 : Blo 854356 1285847 := bstep (se 1 (by rfl) ⟨964385, by rfl⟩ : syracuseStep 1285847 = 1928771) B1928771
theorem B3251933 : Blo 854356 3251933 := bstep (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) B1219475
theorem B1285913 : Blo 854356 1285913 := bstep (se 2 (by rfl) ⟨482217, by rfl⟩ : syracuseStep 1285913 = 964435) B964435
theorem B6954797 : Blo 854356 6954797 := bstep (se 3 (by rfl) ⟨1304024, by rfl⟩ : syracuseStep 6954797 = 2608049) B2608049
theorem B5480257 : Blo 854356 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B5218141 : Blo 854356 5218141 := bstep (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) B1956803
theorem B1286027 : Blo 854356 1286027 := bstep (se 1 (by rfl) ⟨964520, by rfl⟩ : syracuseStep 1286027 = 1929041) B1929041
theorem B1286039 : Blo 854356 1286039 := bstep (se 1 (by rfl) ⟨964529, by rfl⟩ : syracuseStep 1286039 = 1929059) B1929059
theorem B7315379 : Blo 854356 7315379 := bstep (se 1 (by rfl) ⟨5486534, by rfl⟩ : syracuseStep 7315379 = 10973069) B10973069
theorem B2891699 : Blo 854356 2891699 := bstep (se 1 (by rfl) ⟨2168774, by rfl⟩ : syracuseStep 2891699 = 4337549) B4337549
theorem B925643 : Blo 854356 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B1286105 : Blo 854356 1286105 := bstep (se 2 (by rfl) ⟨482289, by rfl⟩ : syracuseStep 1286105 = 964579) B964579
theorem B1286219 : Blo 854356 1286219 := bstep (se 1 (by rfl) ⟨964664, by rfl⟩ : syracuseStep 1286219 = 1929329) B1929329
theorem B4464715 : Blo 854356 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B1286231 : Blo 854356 1286231 := bstep (se 1 (by rfl) ⟨964673, by rfl⟩ : syracuseStep 1286231 = 1929347) B1929347
theorem B4333661 : Blo 854356 4333661 := bstep (se 3 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 4333661 = 1625123) B1625123
theorem B4628573 : Blo 854356 4628573 := bstep (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) B1735715
theorem B1286297 : Blo 854356 1286297 := bstep (se 2 (by rfl) ⟨482361, by rfl⟩ : syracuseStep 1286297 = 964723) B964723
theorem B2891969 : Blo 854356 2891969 := bstep (se 2 (by rfl) ⟨1084488, by rfl⟩ : syracuseStep 2891969 = 2168977) B2168977
theorem B2171083 : Blo 854356 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B1286411 : Blo 854356 1286411 := bstep (se 1 (by rfl) ⟨964808, by rfl⟩ : syracuseStep 1286411 = 1929617) B1929617
theorem B1286423 : Blo 854356 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B7315757 : Blo 854356 7315757 := bstep (se 3 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 7315757 = 2743409) B2743409
theorem B1286489 : Blo 854356 1286489 := bstep (se 2 (by rfl) ⟨482433, by rfl⟩ : syracuseStep 1286489 = 964867) B964867
theorem B2171225 : Blo 854356 2171225 := bstep (se 2 (by rfl) ⟨814209, by rfl⟩ : syracuseStep 2171225 = 1628419) B1628419
theorem B1483147 : Blo 854356 1483147 := bstep (se 1 (by rfl) ⟨1112360, by rfl⟩ : syracuseStep 1483147 = 2224721) B2224721
theorem B1286603 : Blo 854356 1286603 := bstep (se 1 (by rfl) ⟨964952, by rfl⟩ : syracuseStep 1286603 = 1929905) B1929905
theorem B1286615 : Blo 854356 1286615 := bstep (se 1 (by rfl) ⟨964961, by rfl⟩ : syracuseStep 1286615 = 1929923) B1929923
theorem B13181453 : Blo 854356 13181453 := bstep (se 3 (by rfl) ⟨2471522, by rfl⟩ : syracuseStep 13181453 = 4943045) B4943045
theorem B1286681 : Blo 854356 1286681 := bstep (se 2 (by rfl) ⟨482505, by rfl⟩ : syracuseStep 1286681 = 965011) B965011
theorem B1286795 : Blo 854356 1286795 := bstep (se 1 (by rfl) ⟨965096, by rfl⟩ : syracuseStep 1286795 = 1930193) B1930193
theorem B1286807 : Blo 854356 1286807 := bstep (se 1 (by rfl) ⟨965105, by rfl⟩ : syracuseStep 1286807 = 1930211) B1930211
theorem B1286873 : Blo 854356 1286873 := bstep (se 2 (by rfl) ⟨482577, by rfl⟩ : syracuseStep 1286873 = 965155) B965155
theorem B2892509 : Blo 854356 2892509 := bstep (se 3 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 2892509 = 1084691) B1084691
theorem B3089117 : Blo 854356 3089117 := bstep (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) B1158419
theorem B1286987 : Blo 854356 1286987 := bstep (se 1 (by rfl) ⟨965240, by rfl⟩ : syracuseStep 1286987 = 1930481) B1930481
theorem B1286999 : Blo 854356 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B2433881 : Blo 854356 2433881 := bstep (se 2 (by rfl) ⟨912705, by rfl⟩ : syracuseStep 2433881 = 1825411) B1825411
theorem B6169445 : Blo 854356 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B25043813 : Blo 854356 25043813 := bstep (se 4 (by rfl) ⟨2347857, by rfl⟩ : syracuseStep 25043813 = 4695715) B4695715
theorem B10953589 : Blo 854356 10953589 := bstep (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) B1026899
theorem B1287065 : Blo 854356 1287065 := bstep (se 2 (by rfl) ⟨482649, by rfl⟩ : syracuseStep 1287065 = 965299) B965299
theorem B2433995 : Blo 854356 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B1287179 : Blo 854356 1287179 := bstep (se 1 (by rfl) ⟨965384, by rfl⟩ : syracuseStep 1287179 = 1930769) B1930769
theorem B1287191 : Blo 854356 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B1287257 : Blo 854356 1287257 := bstep (se 2 (by rfl) ⟨482721, by rfl⟩ : syracuseStep 1287257 = 965443) B965443
theorem B2172055 : Blo 854356 2172055 := bstep (se 1 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 2172055 = 3258083) B3258083
theorem B1287371 : Blo 854356 1287371 := bstep (se 1 (by rfl) ⟨965528, by rfl⟩ : syracuseStep 1287371 = 1931057) B1931057
theorem B1975511 : Blo 854356 1975511 := bstep (se 1 (by rfl) ⟨1481633, by rfl⟩ : syracuseStep 1975511 = 2963267) B2963267
theorem B1287383 : Blo 854356 1287383 := bstep (se 1 (by rfl) ⟨965537, by rfl⟩ : syracuseStep 1287383 = 1931075) B1931075
theorem B1287449 : Blo 854356 1287449 := bstep (se 2 (by rfl) ⟨482793, by rfl⟩ : syracuseStep 1287449 = 965587) B965587
theorem B6169931 : Blo 854356 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B2172491 : Blo 854356 2172491 := bstep (se 1 (by rfl) ⟨1629368, by rfl⟩ : syracuseStep 2172491 = 3258737) B3258737
theorem B3253891 : Blo 854356 3253891 := bstep (se 1 (by rfl) ⟨2440418, by rfl⟩ : syracuseStep 3253891 = 4880837) B4880837
theorem B2893643 : Blo 854356 2893643 := bstep (se 1 (by rfl) ⟨2170232, by rfl⟩ : syracuseStep 2893643 = 4340465) B4340465
theorem B3254195 : Blo 854356 3254195 := bstep (se 1 (by rfl) ⟨2440646, by rfl⟩ : syracuseStep 3254195 = 4881293) B4881293
theorem B2435123 : Blo 854356 2435123 := bstep (se 1 (by rfl) ⟨1826342, by rfl⟩ : syracuseStep 2435123 = 3652685) B3652685
theorem B2893913 : Blo 854356 2893913 := bstep (se 2 (by rfl) ⟨1085217, by rfl⟩ : syracuseStep 2893913 = 2170435) B2170435
theorem B4335767 : Blo 854356 4335767 := bstep (se 1 (by rfl) ⟨3251825, by rfl⟩ : syracuseStep 4335767 = 6503651) B6503651
theorem B2435521 : Blo 854356 2435521 := bstep (se 2 (by rfl) ⟨913320, by rfl⟩ : syracuseStep 2435521 = 1826641) B1826641
theorem B3254849 : Blo 854356 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B961195 : Blo 854356 961195 := bstep (se 1 (by rfl) ⟨720896, by rfl⟩ : syracuseStep 961195 = 1441793) B1441793
theorem B961303 : Blo 854356 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B2894615 : Blo 854356 2894615 := bstep (se 1 (by rfl) ⟨2170961, by rfl⟩ : syracuseStep 2894615 = 4341923) B4341923
theorem B3091223 : Blo 854356 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B8235877 : Blo 854356 8235877 := bstep (se 4 (by rfl) ⟨772113, by rfl⟩ : syracuseStep 8235877 = 1544227) B1544227
theorem B961483 : Blo 854356 961483 := bstep (se 1 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 961483 = 1442225) B1442225
theorem B6499277 : Blo 854356 6499277 := bstep (se 3 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 6499277 = 2437229) B2437229
theorem B961591 : Blo 854356 961591 := bstep (se 1 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 961591 = 1442387) B1442387
theorem B3124369 : Blo 854356 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B961771 : Blo 854356 961771 := bstep (se 1 (by rfl) ⟨721328, by rfl⟩ : syracuseStep 961771 = 1442657) B1442657
theorem B2895155 : Blo 854356 2895155 := bstep (se 1 (by rfl) ⟨2171366, by rfl⟩ : syracuseStep 2895155 = 4342733) B4342733
theorem B961879 : Blo 854356 961879 := bstep (se 1 (by rfl) ⟨721409, by rfl⟩ : syracuseStep 961879 = 1442819) B1442819
theorem B6499763 : Blo 854356 6499763 := bstep (se 1 (by rfl) ⟨4874822, by rfl⟩ : syracuseStep 6499763 = 9749645) B9749645
theorem B962059 : Blo 854356 962059 := bstep (se 1 (by rfl) ⟨721544, by rfl⟩ : syracuseStep 962059 = 1443089) B1443089
theorem B2895425 : Blo 854356 2895425 := bstep (se 2 (by rfl) ⟨1085784, by rfl⟩ : syracuseStep 2895425 = 2171569) B2171569
theorem B962167 : Blo 854356 962167 := bstep (se 1 (by rfl) ⟨721625, by rfl⟩ : syracuseStep 962167 = 1443251) B1443251
theorem B962347 : Blo 854356 962347 := bstep (se 1 (by rfl) ⟨721760, by rfl⟩ : syracuseStep 962347 = 1443521) B1443521
theorem B3256109 : Blo 854356 3256109 := bstep (se 3 (by rfl) ⟨610520, by rfl⟩ : syracuseStep 3256109 = 1221041) B1221041
theorem B4108097 : Blo 854356 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B3256139 : Blo 854356 3256139 := bstep (se 1 (by rfl) ⟨2442104, by rfl⟩ : syracuseStep 3256139 = 4884209) B4884209
theorem B962455 : Blo 854356 962455 := bstep (se 1 (by rfl) ⟨721841, by rfl⟩ : syracuseStep 962455 = 1443683) B1443683
theorem B962635 : Blo 854356 962635 := bstep (se 1 (by rfl) ⟨721976, by rfl⟩ : syracuseStep 962635 = 1443953) B1443953
theorem B2895965 : Blo 854356 2895965 := bstep (se 3 (by rfl) ⟨542993, by rfl⟩ : syracuseStep 2895965 = 1085987) B1085987
theorem B962743 : Blo 854356 962743 := bstep (se 1 (by rfl) ⟨722057, by rfl⟩ : syracuseStep 962743 = 1444115) B1444115
theorem B3289409 : Blo 854356 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B10170689 : Blo 854356 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B962923 : Blo 854356 962923 := bstep (se 1 (by rfl) ⟨722192, by rfl⟩ : syracuseStep 962923 = 1444385) B1444385
theorem B3092867 : Blo 854356 3092867 := bstep (se 1 (by rfl) ⟨2319650, by rfl⟩ : syracuseStep 3092867 = 4639301) B4639301
theorem B963031 : Blo 854356 963031 := bstep (se 1 (by rfl) ⟨722273, by rfl⟩ : syracuseStep 963031 = 1444547) B1444547
theorem B3256793 : Blo 854356 3256793 := bstep (se 2 (by rfl) ⟨1221297, by rfl⟩ : syracuseStep 3256793 = 2442595) B2442595
theorem B963211 : Blo 854356 963211 := bstep (se 1 (by rfl) ⟨722408, by rfl⟩ : syracuseStep 963211 = 1444817) B1444817
theorem B963319 : Blo 854356 963319 := bstep (se 1 (by rfl) ⟨722489, by rfl⟩ : syracuseStep 963319 = 1444979) B1444979
theorem B3257111 : Blo 854356 3257111 := bstep (se 1 (by rfl) ⟨2442833, by rfl⟩ : syracuseStep 3257111 = 4885667) B4885667
theorem B3093299 : Blo 854356 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B6501221 : Blo 854356 6501221 := bstep (se 4 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 6501221 = 1218979) B1218979
theorem B2438039 : Blo 854356 2438039 := bstep (se 1 (by rfl) ⟨1828529, by rfl⟩ : syracuseStep 2438039 = 3657059) B3657059
theorem B1651607 : Blo 854356 1651607 := bstep (se 1 (by rfl) ⟨1238705, by rfl⟩ : syracuseStep 1651607 = 2477411) B2477411
theorem B963499 : Blo 854356 963499 := bstep (se 1 (by rfl) ⟨722624, by rfl⟩ : syracuseStep 963499 = 1445249) B1445249
theorem B4174865 : Blo 854356 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B963607 : Blo 854356 963607 := bstep (se 1 (by rfl) ⟨722705, by rfl⟩ : syracuseStep 963607 = 1445411) B1445411
theorem B963787 : Blo 854356 963787 := bstep (se 1 (by rfl) ⟨722840, by rfl⟩ : syracuseStep 963787 = 1445681) B1445681
theorem B963895 : Blo 854356 963895 := bstep (se 1 (by rfl) ⟨722921, by rfl⟩ : syracuseStep 963895 = 1445843) B1445843
theorem B6501707 : Blo 854356 6501707 := bstep (se 1 (by rfl) ⟨4876280, by rfl⟩ : syracuseStep 6501707 = 9752561) B9752561
theorem B6174083 : Blo 854356 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B3257779 : Blo 854356 3257779 := bstep (se 1 (by rfl) ⟨2443334, by rfl⟩ : syracuseStep 3257779 = 4886669) B4886669
theorem B964075 : Blo 854356 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B3651095 : Blo 854356 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B964183 : Blo 854356 964183 := bstep (se 1 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 964183 = 1446275) B1446275
theorem B4339331 : Blo 854356 4339331 := bstep (se 1 (by rfl) ⟨3254498, by rfl⟩ : syracuseStep 4339331 = 6508997) B6508997
theorem B4110041 : Blo 854356 4110041 := bstep (se 2 (by rfl) ⟨1541265, by rfl⟩ : syracuseStep 4110041 = 3082531) B3082531
theorem B964363 : Blo 854356 964363 := bstep (se 1 (by rfl) ⟨723272, by rfl⟩ : syracuseStep 964363 = 1446545) B1446545
theorem B964471 : Blo 854356 964471 := bstep (se 1 (by rfl) ⟨723353, by rfl⟩ : syracuseStep 964471 = 1446707) B1446707
theorem B964651 : Blo 854356 964651 := bstep (se 1 (by rfl) ⟨723488, by rfl⟩ : syracuseStep 964651 = 1446977) B1446977
theorem B964759 : Blo 854356 964759 := bstep (se 1 (by rfl) ⟨723569, by rfl⟩ : syracuseStep 964759 = 1447139) B1447139
theorem B2439371 : Blo 854356 2439371 := bstep (se 1 (by rfl) ⟨1829528, by rfl⟩ : syracuseStep 2439371 = 3659057) B3659057
theorem B964939 : Blo 854356 964939 := bstep (se 1 (by rfl) ⟨723704, by rfl⟩ : syracuseStep 964939 = 1447409) B1447409
theorem B965047 : Blo 854356 965047 := bstep (se 1 (by rfl) ⟨723785, by rfl⟩ : syracuseStep 965047 = 1447571) B1447571
theorem B965227 : Blo 854356 965227 := bstep (se 1 (by rfl) ⟨723920, by rfl⟩ : syracuseStep 965227 = 1447841) B1447841
theorem B3259025 : Blo 854356 3259025 := bstep (se 2 (by rfl) ⟨1222134, by rfl⟩ : syracuseStep 3259025 = 2444269) B2444269
theorem B965335 : Blo 854356 965335 := bstep (se 1 (by rfl) ⟨724001, by rfl⟩ : syracuseStep 965335 = 1448003) B1448003
theorem B3652427 : Blo 854356 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B1129291 : Blo 854356 1129291 := bstep (se 1 (by rfl) ⟨846968, by rfl⟩ : syracuseStep 1129291 = 1693937) B1693937
theorem B965515 : Blo 854356 965515 := bstep (se 1 (by rfl) ⟨724136, by rfl⟩ : syracuseStep 965515 = 1448273) B1448273
theorem B1031051 : Blo 854356 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B965623 : Blo 854356 965623 := bstep (se 1 (by rfl) ⟨724217, by rfl⟩ : syracuseStep 965623 = 1448435) B1448435
theorem B1850369 : Blo 854356 1850369 := bstep (se 2 (by rfl) ⟨693888, by rfl⟩ : syracuseStep 1850369 = 1387777) B1387777
theorem B10959947 : Blo 854356 10959947 := bstep (se 1 (by rfl) ⟨8219960, by rfl⟩ : syracuseStep 10959947 = 16439921) B16439921
theorem B3653009 : Blo 854356 3653009 := bstep (se 2 (by rfl) ⟨1369878, by rfl⟩ : syracuseStep 3653009 = 2739757) B2739757
theorem B15646243 : Blo 854356 15646243 := bstep (se 1 (by rfl) ⟨11734682, by rfl⟩ : syracuseStep 15646243 = 23469365) B23469365
theorem B2604595 : Blo 854356 2604595 := bstep (se 1 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 2604595 = 3906893) B3906893
theorem B38125187 : Blo 854356 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B2441011 : Blo 854356 2441011 := bstep (se 1 (by rfl) ⟨1830758, by rfl⟩ : syracuseStep 2441011 = 3661517) B3661517
theorem B2474135 : Blo 854356 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B1622359 : Blo 854356 1622359 := bstep (se 1 (by rfl) ⟨1216769, by rfl⟩ : syracuseStep 1622359 = 2433539) B2433539
theorem B3654067 : Blo 854356 3654067 := bstep (se 1 (by rfl) ⟨2740550, by rfl⟩ : syracuseStep 3654067 = 5481101) B5481101
theorem B6177541 : Blo 854356 6177541 := bstep (se 4 (by rfl) ⟨579144, by rfl⟩ : syracuseStep 6177541 = 1158289) B1158289
theorem B2442059 : Blo 854356 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B13910885 : Blo 854356 13910885 := bstep (se 4 (by rfl) ⟨1304145, by rfl⟩ : syracuseStep 13910885 = 2608291) B2608291
theorem B5850157 : Blo 854356 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B5489765 : Blo 854356 5489765 := bstep (se 4 (by rfl) ⟨514665, by rfl⟩ : syracuseStep 5489765 = 1029331) B1029331
theorem B1623179 : Blo 854356 1623179 := bstep (se 1 (by rfl) ⟨1217384, by rfl⟩ : syracuseStep 1623179 = 2434769) B2434769
theorem B5850263 : Blo 854356 5850263 := bstep (se 1 (by rfl) ⟨4387697, by rfl⟩ : syracuseStep 5850263 = 8775395) B8775395
theorem B5489815 : Blo 854356 5489815 := bstep (se 1 (by rfl) ⟨4117361, by rfl⟩ : syracuseStep 5489815 = 8234723) B8234723
theorem B1623233 : Blo 854356 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B4343057 : Blo 854356 4343057 := bstep (se 2 (by rfl) ⟨1628646, by rfl⟩ : syracuseStep 4343057 = 3257293) B3257293
theorem B1852723 : Blo 854356 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B4343219 : Blo 854356 4343219 := bstep (se 1 (by rfl) ⟨3257414, by rfl⟩ : syracuseStep 4343219 = 6514829) B6514829
theorem B4867715 : Blo 854356 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B3655469 : Blo 854356 3655469 := bstep (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) B1370801
theorem B4868171 : Blo 854356 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B1624151 : Blo 854356 1624151 := bstep (se 1 (by rfl) ⟨1218113, by rfl⟩ : syracuseStep 1624151 = 2436227) B2436227
theorem B2312599 : Blo 854356 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B2443699 : Blo 854356 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B4639193 : Blo 854356 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B6507053 : Blo 854356 6507053 := bstep (se 3 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 6507053 = 2440145) B2440145
theorem B1624691 : Blo 854356 1624691 := bstep (se 1 (by rfl) ⟨1218518, by rfl⟩ : syracuseStep 1624691 = 2437037) B2437037
theorem B2443927 : Blo 854356 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B1625177 : Blo 854356 1625177 := bstep (se 2 (by rfl) ⟨609441, by rfl⟩ : syracuseStep 1625177 = 1218883) B1218883
theorem B4345163 : Blo 854356 4345163 := bstep (se 1 (by rfl) ⟨3258872, by rfl⟩ : syracuseStep 4345163 = 6517745) B6517745
theorem B5721617 : Blo 854356 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B19812275 : Blo 854356 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B15225013 : Blo 854356 15225013 := bstep (se 5 (by rfl) ⟨713672, by rfl⟩ : syracuseStep 15225013 = 1427345) B1427345
theorem B2609459 : Blo 854356 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B1626635 : Blo 854356 1626635 := bstep (se 1 (by rfl) ⟨1219976, by rfl⟩ : syracuseStep 1626635 = 2439953) B2439953
theorem B19780109 : Blo 854356 19780109 := bstep (se 3 (by rfl) ⟨3708770, by rfl⟩ : syracuseStep 19780109 = 7417541) B7417541
theorem B5493379 : Blo 854356 5493379 := bstep (se 1 (by rfl) ⟨4120034, by rfl⟩ : syracuseStep 5493379 = 8240069) B8240069
theorem B1626817 : Blo 854356 1626817 := bstep (se 2 (by rfl) ⟨610056, by rfl⟩ : syracuseStep 1626817 = 1220113) B1220113
theorem B2052953 : Blo 854356 2052953 := bstep (se 2 (by rfl) ⟨769857, by rfl⟩ : syracuseStep 2052953 = 1539715) B1539715
theorem B1561483 : Blo 854356 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B1627265 : Blo 854356 1627265 := bstep (se 2 (by rfl) ⟨610224, by rfl⟩ : syracuseStep 1627265 = 1220449) B1220449
theorem B1922327 : Blo 854356 1922327 := bstep (se 1 (by rfl) ⟨1441745, by rfl⟩ : syracuseStep 1922327 = 2883491) B2883491
theorem B5854643 : Blo 854356 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B2315713 : Blo 854356 2315713 := bstep (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) B1736785
theorem B1922507 : Blo 854356 1922507 := bstep (se 1 (by rfl) ⟨1441880, by rfl⟩ : syracuseStep 1922507 = 2883761) B2883761
theorem B1627607 : Blo 854356 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B1922561 : Blo 854356 1922561 := bstep (se 2 (by rfl) ⟨720960, by rfl⟩ : syracuseStep 1922561 = 1441921) B1441921
theorem B10999313 : Blo 854356 10999313 := bstep (se 2 (by rfl) ⟨4124742, by rfl⟩ : syracuseStep 10999313 = 8249485) B8249485
theorem B1922777 : Blo 854356 1922777 := bstep (se 2 (by rfl) ⟨721041, by rfl⟩ : syracuseStep 1922777 = 1442083) B1442083
theorem B1922867 : Blo 854356 1922867 := bstep (se 1 (by rfl) ⟨1442150, by rfl⟩ : syracuseStep 1922867 = 2884301) B2884301
theorem B1922903 : Blo 854356 1922903 := bstep (se 1 (by rfl) ⟨1442177, by rfl⟩ : syracuseStep 1922903 = 2884355) B2884355
theorem B7821157 : Blo 854356 7821157 := bstep (se 4 (by rfl) ⟨733233, by rfl⟩ : syracuseStep 7821157 = 1466467) B1466467
theorem B3659671 : Blo 854356 3659671 := bstep (se 1 (by rfl) ⟨2744753, by rfl⟩ : syracuseStep 3659671 = 5489507) B5489507
theorem B3659741 : Blo 854356 3659741 := bstep (se 3 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 3659741 = 1372403) B1372403
theorem B1923083 : Blo 854356 1923083 := bstep (se 1 (by rfl) ⟨1442312, by rfl⟩ : syracuseStep 1923083 = 2884625) B2884625
theorem B10967075 : Blo 854356 10967075 := bstep (se 1 (by rfl) ⟨8225306, by rfl⟩ : syracuseStep 10967075 = 16450613) B16450613
theorem B1923137 : Blo 854356 1923137 := bstep (se 2 (by rfl) ⟨721176, by rfl⟩ : syracuseStep 1923137 = 1442353) B1442353
theorem B1628275 : Blo 854356 1628275 := bstep (se 1 (by rfl) ⟨1221206, by rfl⟩ : syracuseStep 1628275 = 2442413) B2442413
theorem B1923353 : Blo 854356 1923353 := bstep (se 2 (by rfl) ⟨721257, by rfl⟩ : syracuseStep 1923353 = 1442515) B1442515
theorem B6510941 : Blo 854356 6510941 := bstep (se 3 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 6510941 = 2441603) B2441603
theorem B1923443 : Blo 854356 1923443 := bstep (se 1 (by rfl) ⟨1442582, by rfl⟩ : syracuseStep 1923443 = 2885165) B2885165
theorem B1923479 : Blo 854356 1923479 := bstep (se 1 (by rfl) ⟨1442609, by rfl⟩ : syracuseStep 1923479 = 2885219) B2885219
theorem B2742731 : Blo 854356 2742731 := bstep (se 1 (by rfl) ⟨2057048, by rfl⟩ : syracuseStep 2742731 = 4114097) B4114097
theorem B1825291 : Blo 854356 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B1956403 : Blo 854356 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1628723 : Blo 854356 1628723 := bstep (se 1 (by rfl) ⟨1221542, by rfl⟩ : syracuseStep 1628723 = 2443085) B2443085
theorem B1923659 : Blo 854356 1923659 := bstep (se 1 (by rfl) ⟨1442744, by rfl⟩ : syracuseStep 1923659 = 2885489) B2885489
theorem B1628761 : Blo 854356 1628761 := bstep (se 2 (by rfl) ⟨610785, by rfl⟩ : syracuseStep 1628761 = 1221571) B1221571
theorem B4872797 : Blo 854356 4872797 := bstep (se 3 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 4872797 = 1827299) B1827299
theorem B1923713 : Blo 854356 1923713 := bstep (se 2 (by rfl) ⟨721392, by rfl⟩ : syracuseStep 1923713 = 1442785) B1442785
theorem B4446899 : Blo 854356 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B3660491 : Blo 854356 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B3300043 : Blo 854356 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B1923929 : Blo 854356 1923929 := bstep (se 2 (by rfl) ⟨721473, by rfl⟩ : syracuseStep 1923929 = 1442947) B1442947
theorem B5561189 : Blo 854356 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B2317207 : Blo 854356 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B1924019 : Blo 854356 1924019 := bstep (se 1 (by rfl) ⟨1443014, by rfl⟩ : syracuseStep 1924019 = 2886029) B2886029
theorem B1924055 : Blo 854356 1924055 := bstep (se 1 (by rfl) ⟨1443041, by rfl⟩ : syracuseStep 1924055 = 2886083) B2886083
theorem B1825753 : Blo 854356 1825753 := bstep (se 2 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 1825753 = 1369315) B1369315
theorem B1629209 : Blo 854356 1629209 := bstep (se 2 (by rfl) ⟨610953, by rfl⟩ : syracuseStep 1629209 = 1221907) B1221907
theorem B1924235 : Blo 854356 1924235 := bstep (se 1 (by rfl) ⟨1443176, by rfl⟩ : syracuseStep 1924235 = 2886353) B2886353
theorem B1924289 : Blo 854356 1924289 := bstep (se 2 (by rfl) ⟨721608, by rfl⟩ : syracuseStep 1924289 = 1443217) B1443217
theorem B2678039 : Blo 854356 2678039 := bstep (se 1 (by rfl) ⟨2008529, by rfl⟩ : syracuseStep 2678039 = 4017059) B4017059
theorem B4873547 : Blo 854356 4873547 := bstep (se 1 (by rfl) ⟨3655160, by rfl⟩ : syracuseStep 4873547 = 7310321) B7310321
theorem B1924505 : Blo 854356 1924505 := bstep (se 2 (by rfl) ⟨721689, by rfl⟩ : syracuseStep 1924505 = 1443379) B1443379
theorem B1924595 : Blo 854356 1924595 := bstep (se 1 (by rfl) ⟨1443446, by rfl⟩ : syracuseStep 1924595 = 2886893) B2886893
theorem B1924631 : Blo 854356 1924631 := bstep (se 1 (by rfl) ⟨1443473, by rfl⟩ : syracuseStep 1924631 = 2886947) B2886947
theorem B2743831 : Blo 854356 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B8347229 : Blo 854356 8347229 := bstep (se 3 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 8347229 = 3130211) B3130211
theorem B974443 : Blo 854356 974443 := bstep (se 1 (by rfl) ⟨730832, by rfl⟩ : syracuseStep 974443 = 1461665) B1461665
theorem B1924811 : Blo 854356 1924811 := bstep (se 1 (by rfl) ⟨1443608, by rfl⟩ : syracuseStep 1924811 = 2887217) B2887217
theorem B1924865 : Blo 854356 1924865 := bstep (se 2 (by rfl) ⟨721824, by rfl⟩ : syracuseStep 1924865 = 1443649) B1443649
theorem B7298909 : Blo 854356 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1925081 : Blo 854356 1925081 := bstep (se 2 (by rfl) ⟨721905, by rfl⟩ : syracuseStep 1925081 = 1443811) B1443811
theorem B1925171 : Blo 854356 1925171 := bstep (se 1 (by rfl) ⟨1443878, by rfl⟩ : syracuseStep 1925171 = 2887757) B2887757
theorem B1925207 : Blo 854356 1925207 := bstep (se 1 (by rfl) ⟨1443905, by rfl⟩ : syracuseStep 1925207 = 2887811) B2887811
theorem B1925387 : Blo 854356 1925387 := bstep (se 1 (by rfl) ⟨1444040, by rfl⟩ : syracuseStep 1925387 = 2888081) B2888081
theorem B1827137 : Blo 854356 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B1925441 : Blo 854356 1925441 := bstep (se 2 (by rfl) ⟨722040, by rfl⟩ : syracuseStep 1925441 = 1444081) B1444081
theorem B2744651 : Blo 854356 2744651 := bstep (se 1 (by rfl) ⟨2058488, by rfl⟩ : syracuseStep 2744651 = 4116977) B4116977
theorem B975223 : Blo 854356 975223 := bstep (se 1 (by rfl) ⟨731417, by rfl⟩ : syracuseStep 975223 = 1462835) B1462835
theorem B1925657 : Blo 854356 1925657 := bstep (se 2 (by rfl) ⟨722121, by rfl⟩ : syracuseStep 1925657 = 1444243) B1444243
theorem B3465773 : Blo 854356 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B7299659 : Blo 854356 7299659 := bstep (se 1 (by rfl) ⟨5474744, by rfl⟩ : syracuseStep 7299659 = 10949489) B10949489
theorem B1925747 : Blo 854356 1925747 := bstep (se 1 (by rfl) ⟨1444310, by rfl⟩ : syracuseStep 1925747 = 2888621) B2888621
theorem B1925783 : Blo 854356 1925783 := bstep (se 1 (by rfl) ⟨1444337, by rfl⟩ : syracuseStep 1925783 = 2888675) B2888675
theorem B1925963 : Blo 854356 1925963 := bstep (se 1 (by rfl) ⟨1444472, by rfl⟩ : syracuseStep 1925963 = 2888945) B2888945
theorem B1926017 : Blo 854356 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B4875187 : Blo 854356 4875187 := bstep (se 1 (by rfl) ⟨3656390, by rfl⟩ : syracuseStep 4875187 = 7312781) B7312781
theorem B2319283 : Blo 854356 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B1172569 : Blo 854356 1172569 := bstep (se 2 (by rfl) ⟨439713, by rfl⟩ : syracuseStep 1172569 = 879427) B879427
theorem B1926233 : Blo 854356 1926233 := bstep (se 2 (by rfl) ⟨722337, by rfl⟩ : syracuseStep 1926233 = 1444675) B1444675
theorem B2319511 : Blo 854356 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B1926323 : Blo 854356 1926323 := bstep (se 1 (by rfl) ⟨1444742, by rfl⟩ : syracuseStep 1926323 = 2889485) B2889485
theorem B1926359 : Blo 854356 1926359 := bstep (se 1 (by rfl) ⟨1444769, by rfl⟩ : syracuseStep 1926359 = 2889539) B2889539
theorem B1926539 : Blo 854356 1926539 := bstep (se 1 (by rfl) ⟨1444904, by rfl⟩ : syracuseStep 1926539 = 2889809) B2889809
theorem B1926593 : Blo 854356 1926593 := bstep (se 2 (by rfl) ⟨722472, by rfl⟩ : syracuseStep 1926593 = 1444945) B1444945
theorem B1926809 : Blo 854356 1926809 := bstep (se 2 (by rfl) ⟨722553, by rfl⟩ : syracuseStep 1926809 = 1445107) B1445107
theorem B1926899 : Blo 854356 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B1926935 : Blo 854356 1926935 := bstep (se 1 (by rfl) ⟨1445201, by rfl⟩ : syracuseStep 1926935 = 2890403) B2890403
theorem B1369943 : Blo 854356 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B1828811 : Blo 854356 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B1927115 : Blo 854356 1927115 := bstep (se 1 (by rfl) ⟨1445336, by rfl⟩ : syracuseStep 1927115 = 2890673) B2890673
theorem B1927169 : Blo 854356 1927169 := bstep (se 2 (by rfl) ⟨722688, by rfl⟩ : syracuseStep 1927169 = 1445377) B1445377
theorem B1370135 : Blo 854356 1370135 := bstep (se 1 (by rfl) ⟨1027601, by rfl⟩ : syracuseStep 1370135 = 2055203) B2055203
theorem B3664045 : Blo 854356 3664045 := bstep (se 3 (by rfl) ⟨687008, by rfl⟩ : syracuseStep 3664045 = 1374017) B1374017
theorem B7301299 : Blo 854356 7301299 := bstep (se 1 (by rfl) ⟨5475974, by rfl⟩ : syracuseStep 7301299 = 10951949) B10951949
theorem B1927385 : Blo 854356 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B13920497 : Blo 854356 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B1927475 : Blo 854356 1927475 := bstep (se 1 (by rfl) ⟨1445606, by rfl⟩ : syracuseStep 1927475 = 2891213) B2891213
theorem B1927511 : Blo 854356 1927511 := bstep (se 1 (by rfl) ⟨1445633, by rfl⟩ : syracuseStep 1927511 = 2891267) B2891267
theorem B3664217 : Blo 854356 3664217 := bstep (se 2 (by rfl) ⟨1374081, by rfl⟩ : syracuseStep 3664217 = 2748163) B2748163
theorem B4876645 : Blo 854356 4876645 := bstep (se 4 (by rfl) ⟨457185, by rfl⟩ : syracuseStep 4876645 = 914371) B914371
theorem B1927691 : Blo 854356 1927691 := bstep (se 1 (by rfl) ⟨1445768, by rfl⟩ : syracuseStep 1927691 = 2891537) B2891537
theorem B16443917 : Blo 854356 16443917 := bstep (se 3 (by rfl) ⟨3083234, by rfl⟩ : syracuseStep 16443917 = 6166469) B6166469
theorem B1927745 : Blo 854356 1927745 := bstep (se 2 (by rfl) ⟨722904, by rfl⟩ : syracuseStep 1927745 = 1445809) B1445809
theorem B1370699 : Blo 854356 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B1370891 : Blo 854356 1370891 := bstep (se 1 (by rfl) ⟨1028168, by rfl⟩ : syracuseStep 1370891 = 2056337) B2056337
theorem B1927961 : Blo 854356 1927961 := bstep (se 2 (by rfl) ⟨722985, by rfl⟩ : syracuseStep 1927961 = 1445971) B1445971
theorem B1928051 : Blo 854356 1928051 := bstep (se 1 (by rfl) ⟨1446038, by rfl⟩ : syracuseStep 1928051 = 2892077) B2892077
theorem B1371019 : Blo 854356 1371019 := bstep (se 1 (by rfl) ⟨1028264, by rfl⟩ : syracuseStep 1371019 = 2056529) B2056529
theorem B1928087 : Blo 854356 1928087 := bstep (se 1 (by rfl) ⟨1446065, by rfl⟩ : syracuseStep 1928087 = 2892131) B2892131
theorem B1829785 : Blo 854356 1829785 := bstep (se 2 (by rfl) ⟨686169, by rfl⟩ : syracuseStep 1829785 = 1372339) B1372339
theorem B1928267 : Blo 854356 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B1928321 : Blo 854356 1928321 := bstep (se 2 (by rfl) ⟨723120, by rfl⟩ : syracuseStep 1928321 = 1446241) B1446241
theorem B1830041 : Blo 854356 1830041 := bstep (se 2 (by rfl) ⟨686265, by rfl⟩ : syracuseStep 1830041 = 1372531) B1372531
theorem B1928537 : Blo 854356 1928537 := bstep (se 2 (by rfl) ⟨723201, by rfl⟩ : syracuseStep 1928537 = 1446403) B1446403
theorem B1928627 : Blo 854356 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B1928663 : Blo 854356 1928663 := bstep (se 1 (by rfl) ⟨1446497, by rfl⟩ : syracuseStep 1928663 = 2892995) B2892995
theorem B1371659 : Blo 854356 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B912919 : Blo 854356 912919 := bstep (se 1 (by rfl) ⟨684689, by rfl⟩ : syracuseStep 912919 = 1369379) B1369379
theorem B978475 : Blo 854356 978475 := bstep (se 1 (by rfl) ⟨733856, by rfl⟩ : syracuseStep 978475 = 1467713) B1467713
theorem B1830451 : Blo 854356 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B1371737 : Blo 854356 1371737 := bstep (se 2 (by rfl) ⟨514401, by rfl⟩ : syracuseStep 1371737 = 1028803) B1028803
theorem B1928843 : Blo 854356 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B1928897 : Blo 854356 1928897 := bstep (se 2 (by rfl) ⟨723336, by rfl⟩ : syracuseStep 1928897 = 1446673) B1446673
theorem B1929113 : Blo 854356 1929113 := bstep (se 2 (by rfl) ⟨723417, by rfl⟩ : syracuseStep 1929113 = 1446835) B1446835
theorem B3665857 : Blo 854356 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B1372121 : Blo 854356 1372121 := bstep (se 2 (by rfl) ⟨514545, by rfl⟩ : syracuseStep 1372121 = 1029091) B1029091
theorem B1929203 : Blo 854356 1929203 := bstep (se 1 (by rfl) ⟨1446902, by rfl⟩ : syracuseStep 1929203 = 2893805) B2893805
theorem B1929239 : Blo 854356 1929239 := bstep (se 1 (by rfl) ⟨1446929, by rfl⟩ : syracuseStep 1929239 = 2893859) B2893859
theorem B1372249 : Blo 854356 1372249 := bstep (se 2 (by rfl) ⟨514593, by rfl⟩ : syracuseStep 1372249 = 1029187) B1029187
theorem B1929419 : Blo 854356 1929419 := bstep (se 1 (by rfl) ⟨1447064, by rfl⟩ : syracuseStep 1929419 = 2894129) B2894129
theorem B1831169 : Blo 854356 1831169 := bstep (se 2 (by rfl) ⟨686688, by rfl⟩ : syracuseStep 1831169 = 1373377) B1373377
theorem B1929473 : Blo 854356 1929473 := bstep (se 2 (by rfl) ⟨723552, by rfl⟩ : syracuseStep 1929473 = 1447105) B1447105
theorem B913739 : Blo 854356 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B2060633 : Blo 854356 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B1929689 : Blo 854356 1929689 := bstep (se 2 (by rfl) ⟨723633, by rfl⟩ : syracuseStep 1929689 = 1447267) B1447267
theorem B1929779 : Blo 854356 1929779 := bstep (se 1 (by rfl) ⟨1447334, by rfl⟩ : syracuseStep 1929779 = 2894669) B2894669
theorem B1831511 : Blo 854356 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B1929815 : Blo 854356 1929815 := bstep (se 1 (by rfl) ⟨1447361, by rfl⟩ : syracuseStep 1929815 = 2894723) B2894723
theorem B1831681 : Blo 854356 1831681 := bstep (se 2 (by rfl) ⟨686880, by rfl⟩ : syracuseStep 1831681 = 1373761) B1373761
theorem B1929995 : Blo 854356 1929995 := bstep (se 1 (by rfl) ⟨1447496, by rfl⟩ : syracuseStep 1929995 = 2894993) B2894993
theorem B1930049 : Blo 854356 1930049 := bstep (se 2 (by rfl) ⟨723768, by rfl⟩ : syracuseStep 1930049 = 1447537) B1447537
theorem B1930265 : Blo 854356 1930265 := bstep (se 2 (by rfl) ⟨723849, by rfl⟩ : syracuseStep 1930265 = 1447699) B1447699
theorem B1930355 : Blo 854356 1930355 := bstep (se 1 (by rfl) ⟨1447766, by rfl⟩ : syracuseStep 1930355 = 2895533) B2895533
theorem B1930391 : Blo 854356 1930391 := bstep (se 1 (by rfl) ⟨1447793, by rfl⟩ : syracuseStep 1930391 = 2895587) B2895587
theorem B914743 : Blo 854356 914743 := bstep (se 1 (by rfl) ⟨686057, by rfl⟩ : syracuseStep 914743 = 1372115) B1372115
theorem B1930571 : Blo 854356 1930571 := bstep (se 1 (by rfl) ⟨1447928, by rfl⟩ : syracuseStep 1930571 = 2895857) B2895857
theorem B1930625 : Blo 854356 1930625 := bstep (se 2 (by rfl) ⟨723984, by rfl⟩ : syracuseStep 1930625 = 1447969) B1447969
theorem B2061719 : Blo 854356 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B1930841 : Blo 854356 1930841 := bstep (se 2 (by rfl) ⟨724065, by rfl⟩ : syracuseStep 1930841 = 1448131) B1448131
theorem B7534259 : Blo 854356 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B1930931 : Blo 854356 1930931 := bstep (se 1 (by rfl) ⟨1448198, by rfl⟩ : syracuseStep 1930931 = 2896397) B2896397
theorem B1930967 : Blo 854356 1930967 := bstep (se 1 (by rfl) ⟨1448225, by rfl⟩ : syracuseStep 1930967 = 2896451) B2896451
theorem B1832843 : Blo 854356 1832843 := bstep (se 1 (by rfl) ⟨1374632, by rfl⟩ : syracuseStep 1832843 = 2749265) B2749265
theorem B1931147 : Blo 854356 1931147 := bstep (se 1 (by rfl) ⟨1448360, by rfl⟩ : syracuseStep 1931147 = 2896721) B2896721
theorem B12318641 : Blo 854356 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B1931201 : Blo 854356 1931201 := bstep (se 2 (by rfl) ⟨724200, by rfl⟩ : syracuseStep 1931201 = 1448401) B1448401
theorem B915499 : Blo 854356 915499 := bstep (se 1 (by rfl) ⟨686624, by rfl⟩ : syracuseStep 915499 = 1373249) B1373249
theorem B3897389 : Blo 854356 3897389 := bstep (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) B1461521
theorem B15628439 : Blo 854356 15628439 := bstep (se 1 (by rfl) ⟨11721329, by rfl⟩ : syracuseStep 15628439 = 23442659) B23442659
theorem B1669835 : Blo 854356 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B6421265 : Blo 854356 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B1735553 : Blo 854356 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B4619537 : Blo 854356 4619537 := bstep (se 2 (by rfl) ⟨1732326, by rfl⟩ : syracuseStep 4619537 = 3464653) B3464653
theorem B8224577 : Blo 854356 8224577 := bstep (se 2 (by rfl) ⟨3084216, by rfl⟩ : syracuseStep 8224577 = 6168433) B6168433
theorem B1441739 : Blo 854356 1441739 := bstep (se 1 (by rfl) ⟨1081304, by rfl⟩ : syracuseStep 1441739 = 2162609) B2162609
theorem B1540055 : Blo 854356 1540055 := bstep (se 1 (by rfl) ⟨1155041, by rfl⟩ : syracuseStep 1540055 = 2310083) B2310083
theorem B2883545 : Blo 854356 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B4325399 : Blo 854356 4325399 := bstep (se 1 (by rfl) ⟨3244049, by rfl⟩ : syracuseStep 4325399 = 6488099) B6488099
theorem B1442063 : Blo 854356 1442063 := bstep (se 1 (by rfl) ⟨1081547, by rfl⟩ : syracuseStep 1442063 = 2163095) B2163095
theorem B2163145 : Blo 854356 2163145 := bstep (se 2 (by rfl) ⟨811179, by rfl⟩ : syracuseStep 2163145 = 1622359) B1622359
theorem B2884139 : Blo 854356 2884139 := bstep (se 1 (by rfl) ⟨2163104, by rfl⟩ : syracuseStep 2884139 = 4326209) B4326209
theorem B9273923 : Blo 854356 9273923 := bstep (se 1 (by rfl) ⟨6955442, by rfl⟩ : syracuseStep 9273923 = 13910885) B13910885
theorem B2163287 : Blo 854356 2163287 := bstep (se 1 (by rfl) ⟨1622465, by rfl⟩ : syracuseStep 2163287 = 3244931) B3244931
theorem B8782627 : Blo 854356 8782627 := bstep (se 1 (by rfl) ⟨6586970, by rfl⟩ : syracuseStep 8782627 = 13173941) B13173941
theorem B1442603 : Blo 854356 1442603 := bstep (se 1 (by rfl) ⟨1081952, by rfl⟩ : syracuseStep 1442603 = 2163905) B2163905
theorem B1082155 : Blo 854356 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B9765683 : Blo 854356 9765683 := bstep (se 1 (by rfl) ⟨7324262, by rfl⟩ : syracuseStep 9765683 = 14648525) B14648525
theorem B35587147 : Blo 854356 35587147 := bstep (se 1 (by rfl) ⟨26690360, by rfl⟩ : syracuseStep 35587147 = 53380721) B53380721
theorem B3245143 : Blo 854356 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B2229383 : Blo 854356 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B1443001 : Blo 854356 1443001 := bstep (se 2 (by rfl) ⟨541125, by rfl⟩ : syracuseStep 1443001 = 1082251) B1082251
theorem B3245447 : Blo 854356 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B7800209 : Blo 854356 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B3245629 : Blo 854356 3245629 := bstep (se 3 (by rfl) ⟨608555, by rfl⟩ : syracuseStep 3245629 = 1217111) B1217111
theorem B1083127 : Blo 854356 1083127 := bstep (se 1 (by rfl) ⟨812345, by rfl⟩ : syracuseStep 1083127 = 1624691) B1624691
theorem B2885435 : Blo 854356 2885435 := bstep (se 1 (by rfl) ⟨2164076, by rfl⟩ : syracuseStep 2885435 = 4328153) B4328153
theorem B1443703 : Blo 854356 1443703 := bstep (se 1 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 1443703 = 2165555) B2165555
theorem B1443899 : Blo 854356 1443899 := bstep (se 1 (by rfl) ⟨1082924, by rfl⟩ : syracuseStep 1443899 = 2165849) B2165849
theorem B1083451 : Blo 854356 1083451 := bstep (se 1 (by rfl) ⟨812588, by rfl⟩ : syracuseStep 1083451 = 1625177) B1625177
theorem B2885921 : Blo 854356 2885921 := bstep (se 2 (by rfl) ⟨1082220, by rfl⟩ : syracuseStep 2885921 = 2164441) B2164441
theorem B854407 : Blo 854356 854407 := bstep (se 1 (by rfl) ⟨640805, by rfl⟩ : syracuseStep 854407 = 1281611) B1281611
theorem B854415 : Blo 854356 854415 := bstep (se 1 (by rfl) ⟨640811, by rfl⟩ : syracuseStep 854415 = 1281623) B1281623
theorem B854459 : Blo 854356 854459 := bstep (se 1 (by rfl) ⟨640844, by rfl⟩ : syracuseStep 854459 = 1281689) B1281689
theorem B1444297 : Blo 854356 1444297 := bstep (se 2 (by rfl) ⟨541611, by rfl⟩ : syracuseStep 1444297 = 1083223) B1083223
theorem B854535 : Blo 854356 854535 := bstep (se 1 (by rfl) ⟨640901, by rfl⟩ : syracuseStep 854535 = 1281803) B1281803
theorem B854543 : Blo 854356 854543 := bstep (se 1 (by rfl) ⟨640907, by rfl⟩ : syracuseStep 854543 = 1281815) B1281815
theorem B854587 : Blo 854356 854587 := bstep (se 1 (by rfl) ⟨640940, by rfl⟩ : syracuseStep 854587 = 1281881) B1281881
theorem B2165363 : Blo 854356 2165363 := bstep (se 1 (by rfl) ⟨1624022, by rfl⟩ : syracuseStep 2165363 = 3248045) B3248045
theorem B13208183 : Blo 854356 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B854663 : Blo 854356 854663 := bstep (se 1 (by rfl) ⟨640997, by rfl⟩ : syracuseStep 854663 = 1281995) B1281995
theorem B854671 : Blo 854356 854671 := bstep (se 1 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 854671 = 1282007) B1282007
theorem B854715 : Blo 854356 854715 := bstep (se 1 (by rfl) ⟨641036, by rfl⟩ : syracuseStep 854715 = 1282073) B1282073
theorem B854791 : Blo 854356 854791 := bstep (se 1 (by rfl) ⟨641093, by rfl⟩ : syracuseStep 854791 = 1282187) B1282187
theorem B854799 : Blo 854356 854799 := bstep (se 1 (by rfl) ⟨641099, by rfl⟩ : syracuseStep 854799 = 1282199) B1282199
theorem B854843 : Blo 854356 854843 := bstep (se 1 (by rfl) ⟨641132, by rfl⟩ : syracuseStep 854843 = 1282265) B1282265
theorem B2886515 : Blo 854356 2886515 := bstep (se 1 (by rfl) ⟨2164886, by rfl⟩ : syracuseStep 2886515 = 4329773) B4329773
theorem B1739639 : Blo 854356 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B854919 : Blo 854356 854919 := bstep (se 1 (by rfl) ⟨641189, by rfl⟩ : syracuseStep 854919 = 1282379) B1282379
theorem B854927 : Blo 854356 854927 := bstep (se 1 (by rfl) ⟨641195, by rfl⟩ : syracuseStep 854927 = 1282391) B1282391
theorem B4885393 : Blo 854356 4885393 := bstep (se 2 (by rfl) ⟨1832022, by rfl⟩ : syracuseStep 4885393 = 3664045) B3664045
theorem B9735065 : Blo 854356 9735065 := bstep (se 2 (by rfl) ⟨3650649, by rfl⟩ : syracuseStep 9735065 = 7301299) B7301299
theorem B854971 : Blo 854356 854971 := bstep (se 1 (by rfl) ⟨641228, by rfl⟩ : syracuseStep 854971 = 1282457) B1282457
theorem B855047 : Blo 854356 855047 := bstep (se 1 (by rfl) ⟨641285, by rfl⟩ : syracuseStep 855047 = 1282571) B1282571
theorem B1084423 : Blo 854356 1084423 := bstep (se 1 (by rfl) ⟨813317, by rfl⟩ : syracuseStep 1084423 = 1626635) B1626635
theorem B855055 : Blo 854356 855055 := bstep (se 1 (by rfl) ⟨641291, by rfl⟩ : syracuseStep 855055 = 1282583) B1282583
theorem B4328477 : Blo 854356 4328477 := bstep (se 3 (by rfl) ⟨811589, by rfl⟩ : syracuseStep 4328477 = 1623179) B1623179
theorem B855099 : Blo 854356 855099 := bstep (se 1 (by rfl) ⟨641324, by rfl⟩ : syracuseStep 855099 = 1282649) B1282649
theorem B15600701 : Blo 854356 15600701 := bstep (se 3 (by rfl) ⟨2925131, by rfl⟩ : syracuseStep 15600701 = 5850263) B5850263
theorem B2165879 : Blo 854356 2165879 := bstep (se 1 (by rfl) ⟨1624409, by rfl⟩ : syracuseStep 2165879 = 3248819) B3248819
theorem B855175 : Blo 854356 855175 := bstep (se 1 (by rfl) ⟨641381, by rfl⟩ : syracuseStep 855175 = 1282763) B1282763
theorem B1444999 : Blo 854356 1444999 := bstep (se 1 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 1444999 = 2167499) B2167499
theorem B855183 : Blo 854356 855183 := bstep (se 1 (by rfl) ⟨641387, by rfl⟩ : syracuseStep 855183 = 1282775) B1282775
theorem B855227 : Blo 854356 855227 := bstep (se 1 (by rfl) ⟨641420, by rfl⟩ : syracuseStep 855227 = 1282841) B1282841
theorem B3083465 : Blo 854356 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B3247361 : Blo 854356 3247361 := bstep (se 2 (by rfl) ⟨1217760, by rfl⟩ : syracuseStep 3247361 = 2435521) B2435521
theorem B855303 : Blo 854356 855303 := bstep (se 1 (by rfl) ⟨641477, by rfl⟩ : syracuseStep 855303 = 1282955) B1282955
theorem B855311 : Blo 854356 855311 := bstep (se 1 (by rfl) ⟨641483, by rfl⟩ : syracuseStep 855311 = 1282967) B1282967
theorem B855355 : Blo 854356 855355 := bstep (se 1 (by rfl) ⟨641516, by rfl⟩ : syracuseStep 855355 = 1283033) B1283033
theorem B855431 : Blo 854356 855431 := bstep (se 1 (by rfl) ⟨641573, by rfl⟩ : syracuseStep 855431 = 1283147) B1283147
theorem B855439 : Blo 854356 855439 := bstep (se 1 (by rfl) ⟨641579, by rfl⟩ : syracuseStep 855439 = 1283159) B1283159
theorem B1084843 : Blo 854356 1084843 := bstep (se 1 (by rfl) ⟨813632, by rfl⟩ : syracuseStep 1084843 = 1627265) B1627265
theorem B855483 : Blo 854356 855483 := bstep (se 1 (by rfl) ⟨641612, by rfl⟩ : syracuseStep 855483 = 1283225) B1283225
theorem B4328963 : Blo 854356 4328963 := bstep (se 1 (by rfl) ⟨3246722, by rfl⟩ : syracuseStep 4328963 = 6493445) B6493445
theorem B855559 : Blo 854356 855559 := bstep (se 1 (by rfl) ⟨641669, by rfl⟩ : syracuseStep 855559 = 1283339) B1283339
theorem B1281551 : Blo 854356 1281551 := bstep (se 1 (by rfl) ⟨961163, by rfl⟩ : syracuseStep 1281551 = 1922327) B1922327
theorem B855567 : Blo 854356 855567 := bstep (se 1 (by rfl) ⟨641675, by rfl⟩ : syracuseStep 855567 = 1283351) B1283351
theorem B1281593 : Blo 854356 1281593 := bstep (se 2 (by rfl) ⟨480597, by rfl⟩ : syracuseStep 1281593 = 961195) B961195
theorem B855611 : Blo 854356 855611 := bstep (se 1 (by rfl) ⟨641708, by rfl⟩ : syracuseStep 855611 = 1283417) B1283417
theorem B3903095 : Blo 854356 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B1281671 : Blo 854356 1281671 := bstep (se 1 (by rfl) ⟨961253, by rfl⟩ : syracuseStep 1281671 = 1922507) B1922507
theorem B855687 : Blo 854356 855687 := bstep (se 1 (by rfl) ⟨641765, by rfl⟩ : syracuseStep 855687 = 1283531) B1283531
theorem B855695 : Blo 854356 855695 := bstep (se 1 (by rfl) ⟨641771, by rfl⟩ : syracuseStep 855695 = 1283543) B1283543
theorem B1085071 : Blo 854356 1085071 := bstep (se 1 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 1085071 = 1627607) B1627607
theorem B1281707 : Blo 854356 1281707 := bstep (se 1 (by rfl) ⟨961280, by rfl⟩ : syracuseStep 1281707 = 1922561) B1922561
theorem B855739 : Blo 854356 855739 := bstep (se 1 (by rfl) ⟨641804, by rfl⟩ : syracuseStep 855739 = 1283609) B1283609
theorem B1281737 : Blo 854356 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B855815 : Blo 854356 855815 := bstep (se 1 (by rfl) ⟨641861, by rfl⟩ : syracuseStep 855815 = 1283723) B1283723
theorem B855823 : Blo 854356 855823 := bstep (se 1 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 855823 = 1283735) B1283735
theorem B1445647 : Blo 854356 1445647 := bstep (se 1 (by rfl) ⟨1084235, by rfl⟩ : syracuseStep 1445647 = 2168471) B2168471
theorem B5279525 : Blo 854356 5279525 := bstep (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) B989911
theorem B10981169 : Blo 854356 10981169 := bstep (se 2 (by rfl) ⟨4117938, by rfl⟩ : syracuseStep 10981169 = 8235877) B8235877
theorem B1281851 : Blo 854356 1281851 := bstep (se 1 (by rfl) ⟨961388, by rfl⟩ : syracuseStep 1281851 = 1922777) B1922777
theorem B855867 : Blo 854356 855867 := bstep (se 1 (by rfl) ⟨641900, by rfl⟩ : syracuseStep 855867 = 1283801) B1283801
theorem B1281911 : Blo 854356 1281911 := bstep (se 1 (by rfl) ⟨961433, by rfl⟩ : syracuseStep 1281911 = 1922867) B1922867
theorem B855943 : Blo 854356 855943 := bstep (se 1 (by rfl) ⟨641957, by rfl⟩ : syracuseStep 855943 = 1283915) B1283915
theorem B1281935 : Blo 854356 1281935 := bstep (se 1 (by rfl) ⟨961451, by rfl⟩ : syracuseStep 1281935 = 1922903) B1922903
theorem B855951 : Blo 854356 855951 := bstep (se 1 (by rfl) ⟨641963, by rfl⟩ : syracuseStep 855951 = 1283927) B1283927
theorem B1281977 : Blo 854356 1281977 := bstep (se 2 (by rfl) ⟨480741, by rfl⟩ : syracuseStep 1281977 = 961483) B961483
theorem B855995 : Blo 854356 855995 := bstep (se 1 (by rfl) ⟨641996, by rfl⟩ : syracuseStep 855995 = 1283993) B1283993
theorem B1282055 : Blo 854356 1282055 := bstep (se 1 (by rfl) ⟨961541, by rfl⟩ : syracuseStep 1282055 = 1923083) B1923083
theorem B856071 : Blo 854356 856071 := bstep (se 1 (by rfl) ⟨642053, by rfl⟩ : syracuseStep 856071 = 1284107) B1284107
theorem B856079 : Blo 854356 856079 := bstep (se 1 (by rfl) ⟨642059, by rfl⟩ : syracuseStep 856079 = 1284119) B1284119
theorem B7311383 : Blo 854356 7311383 := bstep (se 1 (by rfl) ⟨5483537, by rfl⟩ : syracuseStep 7311383 = 10967075) B10967075
theorem B1282091 : Blo 854356 1282091 := bstep (se 1 (by rfl) ⟨961568, by rfl⟩ : syracuseStep 1282091 = 1923137) B1923137
theorem B3084331 : Blo 854356 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B856123 : Blo 854356 856123 := bstep (se 1 (by rfl) ⟨642092, by rfl⟩ : syracuseStep 856123 = 1284185) B1284185
theorem B1282121 : Blo 854356 1282121 := bstep (se 2 (by rfl) ⟨480795, by rfl⟩ : syracuseStep 1282121 = 961591) B961591
theorem B2166871 : Blo 854356 2166871 := bstep (se 1 (by rfl) ⟨1625153, by rfl⟩ : syracuseStep 2166871 = 3250307) B3250307
theorem B856199 : Blo 854356 856199 := bstep (se 1 (by rfl) ⟨642149, by rfl⟩ : syracuseStep 856199 = 1284299) B1284299
theorem B856207 : Blo 854356 856207 := bstep (se 1 (by rfl) ⟨642155, by rfl⟩ : syracuseStep 856207 = 1284311) B1284311
theorem B1282235 : Blo 854356 1282235 := bstep (se 1 (by rfl) ⟨961676, by rfl⟩ : syracuseStep 1282235 = 1923353) B1923353
theorem B856251 : Blo 854356 856251 := bstep (se 1 (by rfl) ⟨642188, by rfl⟩ : syracuseStep 856251 = 1284377) B1284377
theorem B4165825 : Blo 854356 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B23433461 : Blo 854356 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B1282295 : Blo 854356 1282295 := bstep (se 1 (by rfl) ⟨961721, by rfl⟩ : syracuseStep 1282295 = 1923443) B1923443
theorem B856327 : Blo 854356 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B1282319 : Blo 854356 1282319 := bstep (se 1 (by rfl) ⟨961739, by rfl⟩ : syracuseStep 1282319 = 1923479) B1923479
theorem B856335 : Blo 854356 856335 := bstep (se 1 (by rfl) ⟨642251, by rfl⟩ : syracuseStep 856335 = 1284503) B1284503
theorem B1446187 : Blo 854356 1446187 := bstep (se 1 (by rfl) ⟨1084640, by rfl⟩ : syracuseStep 1446187 = 2169281) B2169281
theorem B1282361 : Blo 854356 1282361 := bstep (se 2 (by rfl) ⟨480885, by rfl⟩ : syracuseStep 1282361 = 961771) B961771
theorem B856379 : Blo 854356 856379 := bstep (se 1 (by rfl) ⟨642284, by rfl⟩ : syracuseStep 856379 = 1284569) B1284569
theorem B1085815 : Blo 854356 1085815 := bstep (se 1 (by rfl) ⟨814361, by rfl⟩ : syracuseStep 1085815 = 1628723) B1628723
theorem B8327555 : Blo 854356 8327555 := bstep (se 1 (by rfl) ⟨6245666, by rfl⟩ : syracuseStep 8327555 = 12491333) B12491333
theorem B1282439 : Blo 854356 1282439 := bstep (se 1 (by rfl) ⟨961829, by rfl⟩ : syracuseStep 1282439 = 1923659) B1923659
theorem B2167175 : Blo 854356 2167175 := bstep (se 1 (by rfl) ⟨1625381, by rfl⟩ : syracuseStep 2167175 = 3250763) B3250763
theorem B856455 : Blo 854356 856455 := bstep (se 1 (by rfl) ⟨642341, by rfl⟩ : syracuseStep 856455 = 1284683) B1284683
theorem B856463 : Blo 854356 856463 := bstep (se 1 (by rfl) ⟨642347, by rfl⟩ : syracuseStep 856463 = 1284695) B1284695
theorem B3248531 : Blo 854356 3248531 := bstep (se 1 (by rfl) ⟨2436398, by rfl⟩ : syracuseStep 3248531 = 4872797) B4872797
theorem B1282475 : Blo 854356 1282475 := bstep (se 1 (by rfl) ⟨961856, by rfl⟩ : syracuseStep 1282475 = 1923713) B1923713
theorem B1446329 : Blo 854356 1446329 := bstep (se 2 (by rfl) ⟨542373, by rfl⟩ : syracuseStep 1446329 = 1084747) B1084747
theorem B856507 : Blo 854356 856507 := bstep (se 1 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 856507 = 1284761) B1284761
theorem B1282505 : Blo 854356 1282505 := bstep (se 2 (by rfl) ⟨480939, by rfl⟩ : syracuseStep 1282505 = 961879) B961879
theorem B856583 : Blo 854356 856583 := bstep (se 1 (by rfl) ⟨642437, by rfl⟩ : syracuseStep 856583 = 1284875) B1284875
theorem B2167307 : Blo 854356 2167307 := bstep (se 1 (by rfl) ⟨1625480, by rfl⟩ : syracuseStep 2167307 = 3250961) B3250961
theorem B856591 : Blo 854356 856591 := bstep (se 1 (by rfl) ⟨642443, by rfl⟩ : syracuseStep 856591 = 1284887) B1284887
theorem B1282619 : Blo 854356 1282619 := bstep (se 1 (by rfl) ⟨961964, by rfl⟩ : syracuseStep 1282619 = 1923929) B1923929
theorem B856635 : Blo 854356 856635 := bstep (se 1 (by rfl) ⟨642476, by rfl⟩ : syracuseStep 856635 = 1284953) B1284953
theorem B3707459 : Blo 854356 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B1282679 : Blo 854356 1282679 := bstep (se 1 (by rfl) ⟨962009, by rfl⟩ : syracuseStep 1282679 = 1924019) B1924019
theorem B856711 : Blo 854356 856711 := bstep (se 1 (by rfl) ⟨642533, by rfl⟩ : syracuseStep 856711 = 1285067) B1285067
theorem B1282703 : Blo 854356 1282703 := bstep (se 1 (by rfl) ⟨962027, by rfl⟩ : syracuseStep 1282703 = 1924055) B1924055
theorem B856719 : Blo 854356 856719 := bstep (se 1 (by rfl) ⟨642539, by rfl⟩ : syracuseStep 856719 = 1285079) B1285079
theorem B1282745 : Blo 854356 1282745 := bstep (se 2 (by rfl) ⟨481029, by rfl⟩ : syracuseStep 1282745 = 962059) B962059
theorem B856763 : Blo 854356 856763 := bstep (se 1 (by rfl) ⟨642572, by rfl⟩ : syracuseStep 856763 = 1285145) B1285145
theorem B1086139 : Blo 854356 1086139 := bstep (se 1 (by rfl) ⟨814604, by rfl⟩ : syracuseStep 1086139 = 1629209) B1629209
theorem B1217225 : Blo 854356 1217225 := bstep (se 2 (by rfl) ⟨456459, by rfl⟩ : syracuseStep 1217225 = 912919) B912919
theorem B8327909 : Blo 854356 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B1282823 : Blo 854356 1282823 := bstep (se 1 (by rfl) ⟨962117, by rfl⟩ : syracuseStep 1282823 = 1924235) B1924235
theorem B856839 : Blo 854356 856839 := bstep (se 1 (by rfl) ⟨642629, by rfl⟩ : syracuseStep 856839 = 1285259) B1285259
theorem B856847 : Blo 854356 856847 := bstep (se 1 (by rfl) ⟨642635, by rfl⟩ : syracuseStep 856847 = 1285271) B1285271
theorem B8917775 : Blo 854356 8917775 := bstep (se 1 (by rfl) ⟨6688331, by rfl⟩ : syracuseStep 8917775 = 13376663) B13376663
theorem B1282859 : Blo 854356 1282859 := bstep (se 1 (by rfl) ⟨962144, by rfl⟩ : syracuseStep 1282859 = 1924289) B1924289
theorem B856891 : Blo 854356 856891 := bstep (se 1 (by rfl) ⟨642668, by rfl⟩ : syracuseStep 856891 = 1285337) B1285337
theorem B1282889 : Blo 854356 1282889 := bstep (se 2 (by rfl) ⟨481083, by rfl⟩ : syracuseStep 1282889 = 962167) B962167
theorem B3249031 : Blo 854356 3249031 := bstep (se 1 (by rfl) ⟨2436773, by rfl⟩ : syracuseStep 3249031 = 4873547) B4873547
theorem B856967 : Blo 854356 856967 := bstep (se 1 (by rfl) ⟨642725, by rfl⟩ : syracuseStep 856967 = 1285451) B1285451
theorem B856975 : Blo 854356 856975 := bstep (se 1 (by rfl) ⟨642731, by rfl⟩ : syracuseStep 856975 = 1285463) B1285463
theorem B1283003 : Blo 854356 1283003 := bstep (se 1 (by rfl) ⟨962252, by rfl⟩ : syracuseStep 1283003 = 1924505) B1924505
theorem B857019 : Blo 854356 857019 := bstep (se 1 (by rfl) ⟨642764, by rfl⟩ : syracuseStep 857019 = 1285529) B1285529
theorem B1283063 : Blo 854356 1283063 := bstep (se 1 (by rfl) ⟨962297, by rfl⟩ : syracuseStep 1283063 = 1924595) B1924595
theorem B857095 : Blo 854356 857095 := bstep (se 1 (by rfl) ⟨642821, by rfl⟩ : syracuseStep 857095 = 1285643) B1285643
theorem B1283087 : Blo 854356 1283087 := bstep (se 1 (by rfl) ⟨962315, by rfl⟩ : syracuseStep 1283087 = 1924631) B1924631
theorem B2167823 : Blo 854356 2167823 := bstep (se 1 (by rfl) ⟨1625867, by rfl⟩ : syracuseStep 2167823 = 3251735) B3251735
theorem B857103 : Blo 854356 857103 := bstep (se 1 (by rfl) ⟨642827, by rfl⟩ : syracuseStep 857103 = 1285655) B1285655
theorem B1283129 : Blo 854356 1283129 := bstep (se 2 (by rfl) ⟨481173, by rfl⟩ : syracuseStep 1283129 = 962347) B962347
theorem B857147 : Blo 854356 857147 := bstep (se 1 (by rfl) ⟨642860, by rfl⟩ : syracuseStep 857147 = 1285721) B1285721
theorem B4330583 : Blo 854356 4330583 := bstep (se 1 (by rfl) ⟨3247937, by rfl⟩ : syracuseStep 4330583 = 6495875) B6495875
theorem B1447031 : Blo 854356 1447031 := bstep (se 1 (by rfl) ⟨1085273, by rfl⟩ : syracuseStep 1447031 = 2170547) B2170547
theorem B1283207 : Blo 854356 1283207 := bstep (se 1 (by rfl) ⟨962405, by rfl⟩ : syracuseStep 1283207 = 1924811) B1924811
theorem B857223 : Blo 854356 857223 := bstep (se 1 (by rfl) ⟨642917, by rfl⟩ : syracuseStep 857223 = 1285835) B1285835
theorem B857231 : Blo 854356 857231 := bstep (se 1 (by rfl) ⟨642923, by rfl⟩ : syracuseStep 857231 = 1285847) B1285847
theorem B2167955 : Blo 854356 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B1283243 : Blo 854356 1283243 := bstep (se 1 (by rfl) ⟨962432, by rfl⟩ : syracuseStep 1283243 = 1924865) B1924865
theorem B857275 : Blo 854356 857275 := bstep (se 1 (by rfl) ⟨642956, by rfl⟩ : syracuseStep 857275 = 1285913) B1285913
theorem B1283273 : Blo 854356 1283273 := bstep (se 2 (by rfl) ⟨481227, by rfl⟩ : syracuseStep 1283273 = 962455) B962455
theorem B4887809 : Blo 854356 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B857351 : Blo 854356 857351 := bstep (se 1 (by rfl) ⟨643013, by rfl⟩ : syracuseStep 857351 = 1286027) B1286027
theorem B857359 : Blo 854356 857359 := bstep (se 1 (by rfl) ⟨643019, by rfl⟩ : syracuseStep 857359 = 1286039) B1286039
theorem B1283387 : Blo 854356 1283387 := bstep (se 1 (by rfl) ⟨962540, by rfl⟩ : syracuseStep 1283387 = 1925081) B1925081
theorem B857403 : Blo 854356 857403 := bstep (se 1 (by rfl) ⟨643052, by rfl⟩ : syracuseStep 857403 = 1286105) B1286105
theorem B1283447 : Blo 854356 1283447 := bstep (se 1 (by rfl) ⟨962585, by rfl⟩ : syracuseStep 1283447 = 1925171) B1925171
theorem B857479 : Blo 854356 857479 := bstep (se 1 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 857479 = 1286219) B1286219
theorem B1283471 : Blo 854356 1283471 := bstep (se 1 (by rfl) ⟨962603, by rfl⟩ : syracuseStep 1283471 = 1925207) B1925207
theorem B857487 : Blo 854356 857487 := bstep (se 1 (by rfl) ⟨643115, by rfl⟩ : syracuseStep 857487 = 1286231) B1286231
theorem B2889107 : Blo 854356 2889107 := bstep (se 1 (by rfl) ⟨2166830, by rfl⟩ : syracuseStep 2889107 = 4333661) B4333661
theorem B3085715 : Blo 854356 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B1283513 : Blo 854356 1283513 := bstep (se 2 (by rfl) ⟨481317, by rfl⟩ : syracuseStep 1283513 = 962635) B962635
theorem B857531 : Blo 854356 857531 := bstep (se 1 (by rfl) ⟨643148, by rfl⟩ : syracuseStep 857531 = 1286297) B1286297
theorem B1283591 : Blo 854356 1283591 := bstep (se 1 (by rfl) ⟨962693, by rfl⟩ : syracuseStep 1283591 = 1925387) B1925387
theorem B857607 : Blo 854356 857607 := bstep (se 1 (by rfl) ⟨643205, by rfl⟩ : syracuseStep 857607 = 1286411) B1286411
theorem B857615 : Blo 854356 857615 := bstep (se 1 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 857615 = 1286423) B1286423
theorem B1218091 : Blo 854356 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B1283627 : Blo 854356 1283627 := bstep (se 1 (by rfl) ⟨962720, by rfl⟩ : syracuseStep 1283627 = 1925441) B1925441
theorem B857659 : Blo 854356 857659 := bstep (se 1 (by rfl) ⟨643244, by rfl⟩ : syracuseStep 857659 = 1286489) B1286489
theorem B1447483 : Blo 854356 1447483 := bstep (se 1 (by rfl) ⟨1085612, by rfl⟩ : syracuseStep 1447483 = 2171225) B2171225
theorem B4331069 : Blo 854356 4331069 := bstep (se 3 (by rfl) ⟨812075, by rfl⟩ : syracuseStep 4331069 = 1624151) B1624151
theorem B1283657 : Blo 854356 1283657 := bstep (se 2 (by rfl) ⟨481371, by rfl⟩ : syracuseStep 1283657 = 962743) B962743
theorem B857735 : Blo 854356 857735 := bstep (se 1 (by rfl) ⟨643301, by rfl⟩ : syracuseStep 857735 = 1286603) B1286603
theorem B857743 : Blo 854356 857743 := bstep (se 1 (by rfl) ⟨643307, by rfl⟩ : syracuseStep 857743 = 1286615) B1286615
theorem B8787635 : Blo 854356 8787635 := bstep (se 1 (by rfl) ⟨6590726, by rfl⟩ : syracuseStep 8787635 = 13181453) B13181453
theorem B1283771 : Blo 854356 1283771 := bstep (se 1 (by rfl) ⟨962828, by rfl⟩ : syracuseStep 1283771 = 1925657) B1925657
theorem B857787 : Blo 854356 857787 := bstep (se 1 (by rfl) ⟨643340, by rfl⟩ : syracuseStep 857787 = 1286681) B1286681
theorem B1447625 : Blo 854356 1447625 := bstep (se 2 (by rfl) ⟨542859, by rfl⟩ : syracuseStep 1447625 = 1085719) B1085719
theorem B1283831 : Blo 854356 1283831 := bstep (se 1 (by rfl) ⟨962873, by rfl⟩ : syracuseStep 1283831 = 1925747) B1925747
theorem B857863 : Blo 854356 857863 := bstep (se 1 (by rfl) ⟨643397, by rfl⟩ : syracuseStep 857863 = 1286795) B1286795
theorem B1283855 : Blo 854356 1283855 := bstep (se 1 (by rfl) ⟨962891, by rfl⟩ : syracuseStep 1283855 = 1925783) B1925783
theorem B857871 : Blo 854356 857871 := bstep (se 1 (by rfl) ⟨643403, by rfl⟩ : syracuseStep 857871 = 1286807) B1286807
theorem B1283897 : Blo 854356 1283897 := bstep (se 2 (by rfl) ⟨481461, by rfl⟩ : syracuseStep 1283897 = 962923) B962923
theorem B857915 : Blo 854356 857915 := bstep (se 1 (by rfl) ⟨643436, by rfl⟩ : syracuseStep 857915 = 1286873) B1286873
theorem B1283975 : Blo 854356 1283975 := bstep (se 1 (by rfl) ⟨962981, by rfl⟩ : syracuseStep 1283975 = 1925963) B1925963
theorem B857991 : Blo 854356 857991 := bstep (se 1 (by rfl) ⟨643493, by rfl⟩ : syracuseStep 857991 = 1286987) B1286987
theorem B857999 : Blo 854356 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B1284011 : Blo 854356 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B858043 : Blo 854356 858043 := bstep (se 1 (by rfl) ⟨643532, by rfl⟩ : syracuseStep 858043 = 1287065) B1287065
theorem B1284041 : Blo 854356 1284041 := bstep (se 2 (by rfl) ⟨481515, by rfl⟩ : syracuseStep 1284041 = 963031) B963031
theorem B858119 : Blo 854356 858119 := bstep (se 1 (by rfl) ⟨643589, by rfl⟩ : syracuseStep 858119 = 1287179) B1287179
theorem B858127 : Blo 854356 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B1284155 : Blo 854356 1284155 := bstep (se 1 (by rfl) ⟨963116, by rfl⟩ : syracuseStep 1284155 = 1926233) B1926233
theorem B858171 : Blo 854356 858171 := bstep (se 1 (by rfl) ⟨643628, by rfl⟩ : syracuseStep 858171 = 1287257) B1287257
theorem B1284215 : Blo 854356 1284215 := bstep (se 1 (by rfl) ⟨963161, by rfl⟩ : syracuseStep 1284215 = 1926323) B1926323
theorem B858247 : Blo 854356 858247 := bstep (se 1 (by rfl) ⟨643685, by rfl⟩ : syracuseStep 858247 = 1287371) B1287371
theorem B1317007 : Blo 854356 1317007 := bstep (se 1 (by rfl) ⟨987755, by rfl⟩ : syracuseStep 1317007 = 1975511) B1975511
theorem B1284239 : Blo 854356 1284239 := bstep (se 1 (by rfl) ⟨963179, by rfl⟩ : syracuseStep 1284239 = 1926359) B1926359
theorem B858255 : Blo 854356 858255 := bstep (se 1 (by rfl) ⟨643691, by rfl⟩ : syracuseStep 858255 = 1287383) B1287383
theorem B1284281 : Blo 854356 1284281 := bstep (se 2 (by rfl) ⟨481605, by rfl⟩ : syracuseStep 1284281 = 963211) B963211
theorem B858299 : Blo 854356 858299 := bstep (se 1 (by rfl) ⟨643724, by rfl⟩ : syracuseStep 858299 = 1287449) B1287449
theorem B2169089 : Blo 854356 2169089 := bstep (se 2 (by rfl) ⟨813408, by rfl⟩ : syracuseStep 2169089 = 1626817) B1626817
theorem B1284359 : Blo 854356 1284359 := bstep (se 1 (by rfl) ⟨963269, by rfl⟩ : syracuseStep 1284359 = 1926539) B1926539
theorem B6166817 : Blo 854356 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B1284395 : Blo 854356 1284395 := bstep (se 1 (by rfl) ⟨963296, by rfl⟩ : syracuseStep 1284395 = 1926593) B1926593
theorem B1284425 : Blo 854356 1284425 := bstep (se 2 (by rfl) ⟨481659, by rfl⟩ : syracuseStep 1284425 = 963319) B963319
theorem B1448327 : Blo 854356 1448327 := bstep (se 1 (by rfl) ⟨1086245, by rfl⟩ : syracuseStep 1448327 = 2172491) B2172491
theorem B1284539 : Blo 854356 1284539 := bstep (se 1 (by rfl) ⟨963404, by rfl⟩ : syracuseStep 1284539 = 1926809) B1926809
theorem B1284599 : Blo 854356 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B1284623 : Blo 854356 1284623 := bstep (se 1 (by rfl) ⟨963467, by rfl⟩ : syracuseStep 1284623 = 1926935) B1926935
theorem B1284665 : Blo 854356 1284665 := bstep (se 2 (by rfl) ⟨481749, by rfl⟩ : syracuseStep 1284665 = 963499) B963499
theorem B2169463 : Blo 854356 2169463 := bstep (se 1 (by rfl) ⟨1627097, by rfl⟩ : syracuseStep 2169463 = 3254195) B3254195
theorem B1219207 : Blo 854356 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B1284743 : Blo 854356 1284743 := bstep (se 1 (by rfl) ⟨963557, by rfl⟩ : syracuseStep 1284743 = 1927115) B1927115
theorem B1284779 : Blo 854356 1284779 := bstep (se 1 (by rfl) ⟨963584, by rfl⟩ : syracuseStep 1284779 = 1927169) B1927169
theorem B1284809 : Blo 854356 1284809 := bstep (se 2 (by rfl) ⟨481803, by rfl⟩ : syracuseStep 1284809 = 963607) B963607
theorem B2890511 : Blo 854356 2890511 := bstep (se 1 (by rfl) ⟨2167883, by rfl⟩ : syracuseStep 2890511 = 4335767) B4335767
theorem B1284923 : Blo 854356 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B9280331 : Blo 854356 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B1284983 : Blo 854356 1284983 := bstep (se 1 (by rfl) ⟨963737, by rfl⟩ : syracuseStep 1284983 = 1927475) B1927475
theorem B1285007 : Blo 854356 1285007 := bstep (se 1 (by rfl) ⟨963755, by rfl⟩ : syracuseStep 1285007 = 1927511) B1927511
theorem B1285049 : Blo 854356 1285049 := bstep (se 2 (by rfl) ⟨481893, by rfl⟩ : syracuseStep 1285049 = 963787) B963787
theorem B1285127 : Blo 854356 1285127 := bstep (se 1 (by rfl) ⟨963845, by rfl⟩ : syracuseStep 1285127 = 1927691) B1927691
theorem B2890781 : Blo 854356 2890781 := bstep (se 3 (by rfl) ⟨542021, by rfl⟩ : syracuseStep 2890781 = 1084043) B1084043
theorem B1285163 : Blo 854356 1285163 := bstep (se 1 (by rfl) ⟨963872, by rfl⟩ : syracuseStep 1285163 = 1927745) B1927745
theorem B2169899 : Blo 854356 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B1285193 : Blo 854356 1285193 := bstep (se 2 (by rfl) ⟨481947, by rfl⟩ : syracuseStep 1285193 = 963895) B963895
theorem B1285307 : Blo 854356 1285307 := bstep (se 1 (by rfl) ⟨963980, by rfl⟩ : syracuseStep 1285307 = 1927961) B1927961
theorem B1285367 : Blo 854356 1285367 := bstep (se 1 (by rfl) ⟨964025, by rfl⟩ : syracuseStep 1285367 = 1928051) B1928051
theorem B3087617 : Blo 854356 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B1285391 : Blo 854356 1285391 := bstep (se 1 (by rfl) ⟨964043, by rfl⟩ : syracuseStep 1285391 = 1928087) B1928087
theorem B4332851 : Blo 854356 4332851 := bstep (se 1 (by rfl) ⟨3249638, by rfl⟩ : syracuseStep 4332851 = 6499277) B6499277
theorem B1285433 : Blo 854356 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B1285511 : Blo 854356 1285511 := bstep (se 1 (by rfl) ⟨964133, by rfl⟩ : syracuseStep 1285511 = 1928267) B1928267
theorem B1285547 : Blo 854356 1285547 := bstep (se 1 (by rfl) ⟨964160, by rfl⟩ : syracuseStep 1285547 = 1928321) B1928321
theorem B1220027 : Blo 854356 1220027 := bstep (se 1 (by rfl) ⟨915020, by rfl⟩ : syracuseStep 1220027 = 1830041) B1830041
theorem B1285577 : Blo 854356 1285577 := bstep (se 2 (by rfl) ⟨482091, by rfl⟩ : syracuseStep 1285577 = 964183) B964183
theorem B1285691 : Blo 854356 1285691 := bstep (se 1 (by rfl) ⟨964268, by rfl⟩ : syracuseStep 1285691 = 1928537) B1928537
theorem B4333175 : Blo 854356 4333175 := bstep (se 1 (by rfl) ⟨3249881, by rfl⟩ : syracuseStep 4333175 = 6499763) B6499763
theorem B1285751 : Blo 854356 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B1285775 : Blo 854356 1285775 := bstep (se 1 (by rfl) ⟨964331, by rfl⟩ : syracuseStep 1285775 = 1928663) B1928663
theorem B4628141 : Blo 854356 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B1285817 : Blo 854356 1285817 := bstep (se 2 (by rfl) ⟨482181, by rfl⟩ : syracuseStep 1285817 = 964363) B964363
theorem B1285895 : Blo 854356 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B1285931 : Blo 854356 1285931 := bstep (se 1 (by rfl) ⟨964448, by rfl⟩ : syracuseStep 1285931 = 1928897) B1928897
theorem B10428209 : Blo 854356 10428209 := bstep (se 2 (by rfl) ⟨3910578, by rfl⟩ : syracuseStep 10428209 = 7821157) B7821157
theorem B1285961 : Blo 854356 1285961 := bstep (se 2 (by rfl) ⟨482235, by rfl⟩ : syracuseStep 1285961 = 964471) B964471
theorem B2170739 : Blo 854356 2170739 := bstep (se 1 (by rfl) ⟨1628054, by rfl⟩ : syracuseStep 2170739 = 3256109) B3256109
theorem B2170759 : Blo 854356 2170759 := bstep (se 1 (by rfl) ⟨1628069, by rfl⟩ : syracuseStep 2170759 = 3256139) B3256139
theorem B1286075 : Blo 854356 1286075 := bstep (se 1 (by rfl) ⟨964556, by rfl⟩ : syracuseStep 1286075 = 1929113) B1929113
theorem B1286135 : Blo 854356 1286135 := bstep (se 1 (by rfl) ⟨964601, by rfl⟩ : syracuseStep 1286135 = 1929203) B1929203
theorem B1286159 : Blo 854356 1286159 := bstep (se 1 (by rfl) ⟨964619, by rfl⟩ : syracuseStep 1286159 = 1929239) B1929239
theorem B1220665 : Blo 854356 1220665 := bstep (se 2 (by rfl) ⟨457749, by rfl⟩ : syracuseStep 1220665 = 915499) B915499
theorem B1286201 : Blo 854356 1286201 := bstep (se 2 (by rfl) ⟨482325, by rfl⟩ : syracuseStep 1286201 = 964651) B964651
theorem B1286279 : Blo 854356 1286279 := bstep (se 1 (by rfl) ⟨964709, by rfl⟩ : syracuseStep 1286279 = 1929419) B1929419
theorem B2171033 : Blo 854356 2171033 := bstep (se 2 (by rfl) ⟨814137, by rfl⟩ : syracuseStep 2171033 = 1628275) B1628275
theorem B1220779 : Blo 854356 1220779 := bstep (se 1 (by rfl) ⟨915584, by rfl⟩ : syracuseStep 1220779 = 1831169) B1831169
theorem B1286315 : Blo 854356 1286315 := bstep (se 1 (by rfl) ⟨964736, by rfl⟩ : syracuseStep 1286315 = 1929473) B1929473
theorem B1286345 : Blo 854356 1286345 := bstep (se 2 (by rfl) ⟨482379, by rfl⟩ : syracuseStep 1286345 = 964759) B964759
theorem B1286459 : Blo 854356 1286459 := bstep (se 1 (by rfl) ⟨964844, by rfl⟩ : syracuseStep 1286459 = 1929689) B1929689
theorem B2171195 : Blo 854356 2171195 := bstep (se 1 (by rfl) ⟨1628396, by rfl⟩ : syracuseStep 2171195 = 3256793) B3256793
theorem B1286519 : Blo 854356 1286519 := bstep (se 1 (by rfl) ⟨964889, by rfl⟩ : syracuseStep 1286519 = 1929779) B1929779
theorem B1221007 : Blo 854356 1221007 := bstep (se 1 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 1221007 = 1831511) B1831511
theorem B1286543 : Blo 854356 1286543 := bstep (se 1 (by rfl) ⟨964907, by rfl⟩ : syracuseStep 1286543 = 1929815) B1929815
theorem B2892185 : Blo 854356 2892185 := bstep (se 2 (by rfl) ⟨1084569, by rfl⟩ : syracuseStep 2892185 = 2169139) B2169139
theorem B1286585 : Blo 854356 1286585 := bstep (se 2 (by rfl) ⟨482469, by rfl⟩ : syracuseStep 1286585 = 964939) B964939
theorem B1286663 : Blo 854356 1286663 := bstep (se 1 (by rfl) ⟨964997, by rfl⟩ : syracuseStep 1286663 = 1929995) B1929995
theorem B2171407 : Blo 854356 2171407 := bstep (se 1 (by rfl) ⟨1628555, by rfl⟩ : syracuseStep 2171407 = 3257111) B3257111
theorem B1286699 : Blo 854356 1286699 := bstep (se 1 (by rfl) ⟨965024, by rfl⟩ : syracuseStep 1286699 = 1930049) B1930049
theorem B4334147 : Blo 854356 4334147 := bstep (se 1 (by rfl) ⟨3250610, by rfl⟩ : syracuseStep 4334147 = 6501221) B6501221
theorem B1286729 : Blo 854356 1286729 := bstep (se 2 (by rfl) ⟨482523, by rfl⟩ : syracuseStep 1286729 = 965047) B965047
theorem B2433721 : Blo 854356 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B1286843 : Blo 854356 1286843 := bstep (se 1 (by rfl) ⟨965132, by rfl⟩ : syracuseStep 1286843 = 1930265) B1930265
theorem B1286903 : Blo 854356 1286903 := bstep (se 1 (by rfl) ⟨965177, by rfl⟩ : syracuseStep 1286903 = 1930355) B1930355
theorem B1286927 : Blo 854356 1286927 := bstep (se 1 (by rfl) ⟨965195, by rfl⟩ : syracuseStep 1286927 = 1930391) B1930391
theorem B2171681 : Blo 854356 2171681 := bstep (se 2 (by rfl) ⟨814380, by rfl⟩ : syracuseStep 2171681 = 1628761) B1628761
theorem B1286969 : Blo 854356 1286969 := bstep (se 2 (by rfl) ⟨482613, by rfl⟩ : syracuseStep 1286969 = 965227) B965227
theorem B4334471 : Blo 854356 4334471 := bstep (se 1 (by rfl) ⟨3250853, by rfl⟩ : syracuseStep 4334471 = 6501707) B6501707
theorem B1287047 : Blo 854356 1287047 := bstep (se 1 (by rfl) ⟨965285, by rfl⟩ : syracuseStep 1287047 = 1930571) B1930571
theorem B1287083 : Blo 854356 1287083 := bstep (se 1 (by rfl) ⟨965312, by rfl⟩ : syracuseStep 1287083 = 1930625) B1930625
theorem B4400057 : Blo 854356 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B1287113 : Blo 854356 1287113 := bstep (se 2 (by rfl) ⟨482667, by rfl⟩ : syracuseStep 1287113 = 965335) B965335
theorem B2434063 : Blo 854356 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B1287227 : Blo 854356 1287227 := bstep (se 1 (by rfl) ⟨965420, by rfl⟩ : syracuseStep 1287227 = 1930841) B1930841
theorem B2892887 : Blo 854356 2892887 := bstep (se 1 (by rfl) ⟨2169665, by rfl⟩ : syracuseStep 2892887 = 4339331) B4339331
theorem B5022839 : Blo 854356 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B1287287 : Blo 854356 1287287 := bstep (se 1 (by rfl) ⟨965465, by rfl⟩ : syracuseStep 1287287 = 1930931) B1930931
theorem B1287311 : Blo 854356 1287311 := bstep (se 1 (by rfl) ⟨965483, by rfl⟩ : syracuseStep 1287311 = 1930967) B1930967
theorem B1287353 : Blo 854356 1287353 := bstep (se 2 (by rfl) ⟨482757, by rfl⟩ : syracuseStep 1287353 = 965515) B965515
theorem B3089609 : Blo 854356 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B1221895 : Blo 854356 1221895 := bstep (se 1 (by rfl) ⟨916421, by rfl⟩ : syracuseStep 1221895 = 1832843) B1832843
theorem B1287431 : Blo 854356 1287431 := bstep (se 1 (by rfl) ⟨965573, by rfl⟩ : syracuseStep 1287431 = 1931147) B1931147
theorem B2434337 : Blo 854356 2434337 := bstep (se 2 (by rfl) ⟨912876, by rfl⟩ : syracuseStep 2434337 = 1825753) B1825753
theorem B1287467 : Blo 854356 1287467 := bstep (se 1 (by rfl) ⟨965600, by rfl⟩ : syracuseStep 1287467 = 1931201) B1931201
theorem B1287497 : Blo 854356 1287497 := bstep (se 2 (by rfl) ⟨482811, by rfl⟩ : syracuseStep 1287497 = 965623) B965623
theorem B2598259 : Blo 854356 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B2893373 : Blo 854356 2893373 := bstep (se 3 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 2893373 = 1085015) B1085015
theorem B2172683 : Blo 854356 2172683 := bstep (se 1 (by rfl) ⟨1629512, by rfl⟩ : syracuseStep 2172683 = 3259025) B3259025
theorem B2434951 : Blo 854356 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B10954925 : Blo 854356 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B2435339 : Blo 854356 2435339 := bstep (se 1 (by rfl) ⟨1826504, by rfl⟩ : syracuseStep 2435339 = 3653009) B3653009
theorem B3254681 : Blo 854356 3254681 := bstep (se 2 (by rfl) ⟨1220505, by rfl⟩ : syracuseStep 3254681 = 2441011) B2441011
theorem B6957521 : Blo 854356 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B2468381 : Blo 854356 2468381 := bstep (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) B925643
theorem B5483051 : Blo 854356 5483051 := bstep (se 1 (by rfl) ⟨4112288, by rfl⟩ : syracuseStep 5483051 = 8224577) B8224577
theorem B961159 : Blo 854356 961159 := bstep (se 1 (by rfl) ⟨720869, by rfl⟩ : syracuseStep 961159 = 1441739) B1441739
theorem B1026703 : Blo 854356 1026703 := bstep (se 1 (by rfl) ⟨770027, by rfl⟩ : syracuseStep 1026703 = 1540055) B1540055
theorem B1649423 : Blo 854356 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B961339 : Blo 854356 961339 := bstep (se 1 (by rfl) ⟨721004, by rfl⟩ : syracuseStep 961339 = 1442009) B1442009
theorem B2894777 : Blo 854356 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B1977529 : Blo 854356 1977529 := bstep (se 2 (by rfl) ⟨741573, by rfl⟩ : syracuseStep 1977529 = 1483147) B1483147
theorem B11709677 : Blo 854356 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B961807 : Blo 854356 961807 := bstep (se 1 (by rfl) ⟨721355, by rfl⟩ : syracuseStep 961807 = 1442711) B1442711
theorem B2895371 : Blo 854356 2895371 := bstep (se 1 (by rfl) ⟨2171528, by rfl⟩ : syracuseStep 2895371 = 4343057) B4343057
theorem B2436637 : Blo 854356 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B7319069 : Blo 854356 7319069 := bstep (se 3 (by rfl) ⟨1372325, by rfl⟩ : syracuseStep 7319069 = 2744651) B2744651
theorem B2600507 : Blo 854356 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B2895479 : Blo 854356 2895479 := bstep (se 1 (by rfl) ⟨2171609, by rfl⟩ : syracuseStep 2895479 = 4343219) B4343219
theorem B8236721 : Blo 854356 8236721 := bstep (se 2 (by rfl) ⟨3088770, by rfl⟩ : syracuseStep 8236721 = 6177541) B6177541
theorem B962311 : Blo 854356 962311 := bstep (se 1 (by rfl) ⟨721733, by rfl⟩ : syracuseStep 962311 = 1443467) B1443467
theorem B2436979 : Blo 854356 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B6500249 : Blo 854356 6500249 := bstep (se 2 (by rfl) ⟨2437593, by rfl⟩ : syracuseStep 6500249 = 4875187) B4875187
theorem B3092377 : Blo 854356 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B962491 : Blo 854356 962491 := bstep (se 1 (by rfl) ⟨721868, by rfl⟩ : syracuseStep 962491 = 1443737) B1443737
theorem B1486793 : Blo 854356 1486793 := bstep (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) B1115095
theorem B10399691 : Blo 854356 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B6336713 : Blo 854356 6336713 := bstep (se 2 (by rfl) ⟨2376267, by rfl⟩ : syracuseStep 6336713 = 4752535) B4752535
theorem B7319753 : Blo 854356 7319753 := bstep (se 2 (by rfl) ⟨2744907, by rfl⟩ : syracuseStep 7319753 = 5489815) B5489815
theorem B2896073 : Blo 854356 2896073 := bstep (se 2 (by rfl) ⟨1086027, by rfl⟩ : syracuseStep 2896073 = 2172055) B2172055
theorem B3092681 : Blo 854356 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B3092795 : Blo 854356 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B4338035 : Blo 854356 4338035 := bstep (se 1 (by rfl) ⟨3253526, by rfl⟩ : syracuseStep 4338035 = 6507053) B6507053
theorem B1028471 : Blo 854356 1028471 := bstep (se 1 (by rfl) ⟨771353, by rfl⟩ : syracuseStep 1028471 = 1542707) B1542707
theorem B962959 : Blo 854356 962959 := bstep (se 1 (by rfl) ⟨722219, by rfl⟩ : syracuseStep 962959 = 1444439) B1444439
theorem B1028495 : Blo 854356 1028495 := bstep (se 1 (by rfl) ⟨771371, by rfl⟩ : syracuseStep 1028495 = 1542743) B1542743
theorem B7320131 : Blo 854356 7320131 := bstep (se 1 (by rfl) ⟨5490098, by rfl⟩ : syracuseStep 7320131 = 10980197) B10980197
theorem B8237645 : Blo 854356 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B5288719 : Blo 854356 5288719 := bstep (se 1 (by rfl) ⟨3966539, by rfl⟩ : syracuseStep 5288719 = 7933079) B7933079
theorem B4338521 : Blo 854356 4338521 := bstep (se 2 (by rfl) ⟨1626945, by rfl⟩ : syracuseStep 4338521 = 3253891) B3253891
theorem B963463 : Blo 854356 963463 := bstep (se 1 (by rfl) ⟨722597, by rfl⟩ : syracuseStep 963463 = 1445195) B1445195
theorem B2896775 : Blo 854356 2896775 := bstep (se 1 (by rfl) ⟨2172581, by rfl⟩ : syracuseStep 2896775 = 4345163) B4345163
theorem B3814411 : Blo 854356 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B963643 : Blo 854356 963643 := bstep (se 1 (by rfl) ⟨722732, by rfl⟩ : syracuseStep 963643 = 1445465) B1445465
theorem B4634003 : Blo 854356 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B964111 : Blo 854356 964111 := bstep (se 1 (by rfl) ⟨723083, by rfl⟩ : syracuseStep 964111 = 1446167) B1446167
theorem B13186739 : Blo 854356 13186739 := bstep (se 1 (by rfl) ⟨9890054, by rfl⟩ : syracuseStep 13186739 = 19780109) B19780109
theorem B6502193 : Blo 854356 6502193 := bstep (se 2 (by rfl) ⟨2438322, by rfl⟩ : syracuseStep 6502193 = 4876645) B4876645
theorem B3258265 : Blo 854356 3258265 := bstep (se 2 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 3258265 = 2443699) B2443699
theorem B964615 : Blo 854356 964615 := bstep (se 1 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 964615 = 1446923) B1446923
theorem B5486615 : Blo 854356 5486615 := bstep (se 1 (by rfl) ⟨4114961, by rfl⟩ : syracuseStep 5486615 = 8229923) B8229923
theorem B4110365 : Blo 854356 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B964795 : Blo 854356 964795 := bstep (se 1 (by rfl) ⟨723596, by rfl⟩ : syracuseStep 964795 = 1447193) B1447193
theorem B3258569 : Blo 854356 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B2439713 : Blo 854356 2439713 := bstep (se 2 (by rfl) ⟨914892, by rfl⟩ : syracuseStep 2439713 = 1829785) B1829785
theorem B965263 : Blo 854356 965263 := bstep (se 1 (by rfl) ⟨723947, by rfl⟩ : syracuseStep 965263 = 1447895) B1447895
theorem B2439827 : Blo 854356 2439827 := bstep (se 1 (by rfl) ⟨1829870, by rfl⟩ : syracuseStep 2439827 = 3659741) B3659741
theorem B3652411 : Blo 854356 3652411 := bstep (se 1 (by rfl) ⟨2739308, by rfl⟩ : syracuseStep 3652411 = 5478617) B5478617
theorem B4340627 : Blo 854356 4340627 := bstep (se 1 (by rfl) ⟨3255470, by rfl⟩ : syracuseStep 4340627 = 6510941) B6510941
theorem B2964599 : Blo 854356 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B10992955 : Blo 854356 10992955 := bstep (se 1 (by rfl) ⟨8244716, by rfl⟩ : syracuseStep 10992955 = 16489433) B16489433
theorem B2440601 : Blo 854356 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B1785359 : Blo 854356 1785359 := bstep (se 1 (by rfl) ⟨1339019, by rfl⟩ : syracuseStep 1785359 = 2678039) B2678039
theorem B7323443 : Blo 854356 7323443 := bstep (se 1 (by rfl) ⟨5492582, by rfl⟩ : syracuseStep 7323443 = 10985165) B10985165
theorem B4636531 : Blo 854356 4636531 := bstep (se 1 (by rfl) ⟨3477398, by rfl⟩ : syracuseStep 4636531 = 6954797) B6954797
theorem B4865939 : Blo 854356 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B3653693 : Blo 854356 3653693 := bstep (se 3 (by rfl) ⟨685067, by rfl⟩ : syracuseStep 3653693 = 1370135) B1370135
theorem B14631029 : Blo 854356 14631029 := bstep (se 5 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 14631029 = 1371659) B1371659
theorem B20300017 : Blo 854356 20300017 := bstep (se 2 (by rfl) ⟨7612506, by rfl⟩ : syracuseStep 20300017 = 15225013) B15225013
theorem B2310515 : Blo 854356 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B4866439 : Blo 854356 4866439 := bstep (se 1 (by rfl) ⟨3649829, by rfl⟩ : syracuseStep 4866439 = 7299659) B7299659
theorem B1622587 : Blo 854356 1622587 := bstep (se 1 (by rfl) ⟨1216940, by rfl⟩ : syracuseStep 1622587 = 2433881) B2433881
theorem B4112963 : Blo 854356 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B16695875 : Blo 854356 16695875 := bstep (se 1 (by rfl) ⟨12521906, by rfl⟩ : syracuseStep 16695875 = 25043813) B25043813
theorem B1622663 : Blo 854356 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B7324505 : Blo 854356 7324505 := bstep (se 2 (by rfl) ⟨2746689, by rfl⟩ : syracuseStep 7324505 = 5493379) B5493379
theorem B4113287 : Blo 854356 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B2442241 : Blo 854356 2442241 := bstep (se 2 (by rfl) ⟨915840, by rfl⟩ : syracuseStep 2442241 = 1831681) B1831681
theorem B1623073 : Blo 854356 1623073 := bstep (se 2 (by rfl) ⟨608652, by rfl⟩ : syracuseStep 1623073 = 1217305) B1217305
theorem B1623415 : Blo 854356 1623415 := bstep (se 1 (by rfl) ⟨1217561, by rfl⟩ : syracuseStep 1623415 = 2435123) B2435123
theorem B2442811 : Blo 854356 2442811 := bstep (se 1 (by rfl) ⟨1832108, by rfl⟩ : syracuseStep 2442811 = 3664217) B3664217
theorem B9881189 : Blo 854356 9881189 := bstep (se 4 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 9881189 = 1852723) B1852723
theorem B10962611 : Blo 854356 10962611 := bstep (se 1 (by rfl) ⟨8221958, by rfl⟩ : syracuseStep 10962611 = 16443917) B16443917
theorem B4343705 : Blo 854356 4343705 := bstep (se 2 (by rfl) ⟨1628889, by rfl⟩ : syracuseStep 4343705 = 3257779) B3257779
theorem B4934317 : Blo 854356 4934317 := bstep (se 3 (by rfl) ⟨925184, by rfl⟩ : syracuseStep 4934317 = 1850369) B1850369
theorem B1625017 : Blo 854356 1625017 := bstep (se 2 (by rfl) ⟨609381, by rfl⟩ : syracuseStep 1625017 = 1218763) B1218763
theorem B1625359 : Blo 854356 1625359 := bstep (se 1 (by rfl) ⟨1219019, by rfl⟩ : syracuseStep 1625359 = 2438039) B2438039
theorem B1101071 : Blo 854356 1101071 := bstep (se 1 (by rfl) ⟨825803, by rfl⟩ : syracuseStep 1101071 = 1651607) B1651607
theorem B2608537 : Blo 854356 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B15650333 : Blo 854356 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B4116055 : Blo 854356 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B2740027 : Blo 854356 2740027 := bstep (se 1 (by rfl) ⟨2055020, by rfl⟩ : syracuseStep 2740027 = 4110041) B4110041
theorem B8212427 : Blo 854356 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B1626247 : Blo 854356 1626247 := bstep (se 1 (by rfl) ⟨1219685, by rfl⟩ : syracuseStep 1626247 = 2439371) B2439371
theorem B4116653 : Blo 854356 4116653 := bstep (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) B1543745
theorem B4280843 : Blo 854356 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B3658441 : Blo 854356 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B20861657 : Blo 854356 20861657 := bstep (se 2 (by rfl) ⟨7823121, by rfl⟩ : syracuseStep 20861657 = 15646243) B15646243
theorem B1299257 : Blo 854356 1299257 := bstep (se 2 (by rfl) ⟨487221, by rfl⟩ : syracuseStep 1299257 = 974443) B974443
theorem B25416791 : Blo 854356 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B1922363 : Blo 854356 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B6509969 : Blo 854356 6509969 := bstep (se 2 (by rfl) ⟨2441238, by rfl⟩ : syracuseStep 6509969 = 4882477) B4882477
theorem B1922489 : Blo 854356 1922489 := bstep (se 2 (by rfl) ⟨720933, by rfl⟩ : syracuseStep 1922489 = 1441867) B1441867
theorem B5952953 : Blo 854356 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B1922831 : Blo 854356 1922831 := bstep (se 1 (by rfl) ⟨1442123, by rfl⟩ : syracuseStep 1922831 = 2884247) B2884247
theorem B1922849 : Blo 854356 1922849 := bstep (se 2 (by rfl) ⟨721068, by rfl⟩ : syracuseStep 1922849 = 1442137) B1442137
theorem B1300297 : Blo 854356 1300297 := bstep (se 2 (by rfl) ⟨487611, by rfl⟩ : syracuseStep 1300297 = 975223) B975223
theorem B1628039 : Blo 854356 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B4872089 : Blo 854356 4872089 := bstep (se 2 (by rfl) ⟨1827033, by rfl⟩ : syracuseStep 4872089 = 3654067) B3654067
theorem B3659843 : Blo 854356 3659843 := bstep (se 1 (by rfl) ⟨2744882, by rfl⟩ : syracuseStep 3659843 = 5489765) B5489765
theorem B1923191 : Blo 854356 1923191 := bstep (se 1 (by rfl) ⟨1442393, by rfl⟩ : syracuseStep 1923191 = 2884787) B2884787
theorem B27121837 : Blo 854356 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B1923371 : Blo 854356 1923371 := bstep (se 1 (by rfl) ⟨1442528, by rfl⟩ : syracuseStep 1923371 = 2885057) B2885057
theorem B14604785 : Blo 854356 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B1923731 : Blo 854356 1923731 := bstep (se 1 (by rfl) ⟨1442798, by rfl⟩ : syracuseStep 1923731 = 2885597) B2885597
theorem B1923785 : Blo 854356 1923785 := bstep (se 2 (by rfl) ⟨721419, by rfl⟩ : syracuseStep 1923785 = 1442839) B1442839
theorem B1563425 : Blo 854356 1563425 := bstep (se 2 (by rfl) ⟨586284, by rfl⟩ : syracuseStep 1563425 = 1172569) B1172569
theorem B5200919 : Blo 854356 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B1924487 : Blo 854356 1924487 := bstep (se 1 (by rfl) ⟨1443365, by rfl⟩ : syracuseStep 1924487 = 2886731) B2886731
theorem B1924667 : Blo 854356 1924667 := bstep (se 1 (by rfl) ⟨1443500, by rfl⟩ : syracuseStep 1924667 = 2887001) B2887001
theorem B1924793 : Blo 854356 1924793 := bstep (se 2 (by rfl) ⟨721797, by rfl⟩ : syracuseStep 1924793 = 1443595) B1443595
theorem B6512399 : Blo 854356 6512399 := bstep (se 1 (by rfl) ⟨4884299, by rfl⟩ : syracuseStep 6512399 = 9768599) B9768599
theorem B1925135 : Blo 854356 1925135 := bstep (se 1 (by rfl) ⟨1443851, by rfl⟩ : syracuseStep 1925135 = 2887703) B2887703
theorem B1925153 : Blo 854356 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B1925495 : Blo 854356 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B1925675 : Blo 854356 1925675 := bstep (se 1 (by rfl) ⟨1444256, by rfl⟩ : syracuseStep 1925675 = 2888513) B2888513
theorem B1368635 : Blo 854356 1368635 := bstep (se 1 (by rfl) ⟨1026476, by rfl⟩ : syracuseStep 1368635 = 2052953) B2052953
theorem B1926035 : Blo 854356 1926035 := bstep (se 1 (by rfl) ⟨1444526, by rfl⟩ : syracuseStep 1926035 = 2889053) B2889053
theorem B1926089 : Blo 854356 1926089 := bstep (se 2 (by rfl) ⟨722283, by rfl⟩ : syracuseStep 1926089 = 1444567) B1444567
theorem B7332875 : Blo 854356 7332875 := bstep (se 1 (by rfl) ⟨5499656, by rfl⟩ : syracuseStep 7332875 = 10999313) B10999313
theorem B1828025 : Blo 854356 1828025 := bstep (se 2 (by rfl) ⟨685509, by rfl⟩ : syracuseStep 1828025 = 1371019) B1371019
theorem B2319769 : Blo 854356 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B1828487 : Blo 854356 1828487 := bstep (se 1 (by rfl) ⟨1371365, by rfl⟩ : syracuseStep 1828487 = 2742731) B2742731
theorem B1926791 : Blo 854356 1926791 := bstep (se 1 (by rfl) ⟨1445093, by rfl⟩ : syracuseStep 1926791 = 2890187) B2890187
theorem B6022885 : Blo 854356 6022885 := bstep (se 4 (by rfl) ⟨564645, by rfl⟩ : syracuseStep 6022885 = 1129291) B1129291
theorem B1926971 : Blo 854356 1926971 := bstep (se 1 (by rfl) ⟨1445228, by rfl⟩ : syracuseStep 1926971 = 2890457) B2890457
theorem B1927097 : Blo 854356 1927097 := bstep (se 2 (by rfl) ⟨722661, by rfl⟩ : syracuseStep 1927097 = 1445323) B1445323
theorem B1304633 : Blo 854356 1304633 := bstep (se 2 (by rfl) ⟨489237, by rfl⟩ : syracuseStep 1304633 = 978475) B978475
theorem B1927439 : Blo 854356 1927439 := bstep (se 1 (by rfl) ⟨1445579, by rfl⟩ : syracuseStep 1927439 = 2891159) B2891159
theorem B1927457 : Blo 854356 1927457 := bstep (se 2 (by rfl) ⟨722796, by rfl⟩ : syracuseStep 1927457 = 1445593) B1445593
theorem B5564819 : Blo 854356 5564819 := bstep (se 1 (by rfl) ⟨4173614, by rfl⟩ : syracuseStep 5564819 = 8347229) B8347229
theorem B4876919 : Blo 854356 4876919 := bstep (se 1 (by rfl) ⟨3657689, by rfl⟩ : syracuseStep 4876919 = 7315379) B7315379
theorem B1927799 : Blo 854356 1927799 := bstep (se 1 (by rfl) ⟨1445849, by rfl⟩ : syracuseStep 1927799 = 2891699) B2891699
theorem B1829665 : Blo 854356 1829665 := bstep (se 2 (by rfl) ⟨686124, by rfl⟩ : syracuseStep 1829665 = 1372249) B1372249
theorem B1927979 : Blo 854356 1927979 := bstep (se 1 (by rfl) ⟨1445984, by rfl⟩ : syracuseStep 1927979 = 2891969) B2891969
theorem B4877171 : Blo 854356 4877171 := bstep (se 1 (by rfl) ⟨3657878, by rfl⟩ : syracuseStep 4877171 = 7315757) B7315757
theorem B1928339 : Blo 854356 1928339 := bstep (se 1 (by rfl) ⟨1446254, by rfl⟩ : syracuseStep 1928339 = 2892509) B2892509
theorem B1928393 : Blo 854356 1928393 := bstep (se 2 (by rfl) ⟨723147, by rfl⟩ : syracuseStep 1928393 = 1446295) B1446295
theorem B8220113 : Blo 854356 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B1929095 : Blo 854356 1929095 := bstep (se 1 (by rfl) ⟨1446821, by rfl⟩ : syracuseStep 1929095 = 2893643) B2893643
theorem B913295 : Blo 854356 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B1929275 : Blo 854356 1929275 := bstep (se 1 (by rfl) ⟨1446956, by rfl⟩ : syracuseStep 1929275 = 2893913) B2893913
theorem B2715709 : Blo 854356 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B1929401 : Blo 854356 1929401 := bstep (se 2 (by rfl) ⟨723525, by rfl⟩ : syracuseStep 1929401 = 1447051) B1447051
theorem B4878629 : Blo 854356 4878629 := bstep (se 4 (by rfl) ⟨457371, by rfl⟩ : syracuseStep 4878629 = 914743) B914743
theorem B913799 : Blo 854356 913799 := bstep (se 1 (by rfl) ⟨685349, by rfl⟩ : syracuseStep 913799 = 1370699) B1370699
theorem B913927 : Blo 854356 913927 := bstep (se 1 (by rfl) ⟨685445, by rfl⟩ : syracuseStep 913927 = 1370891) B1370891
theorem B1929743 : Blo 854356 1929743 := bstep (se 1 (by rfl) ⟨1447307, by rfl⟩ : syracuseStep 1929743 = 2894615) B2894615
theorem B2060815 : Blo 854356 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B4452893 : Blo 854356 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B9761309 : Blo 854356 9761309 := bstep (se 3 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 9761309 = 3660491) B3660491
theorem B1929761 : Blo 854356 1929761 := bstep (se 2 (by rfl) ⟨723660, by rfl⟩ : syracuseStep 1929761 = 1447321) B1447321
theorem B1930103 : Blo 854356 1930103 := bstep (se 1 (by rfl) ⟨1447577, by rfl⟩ : syracuseStep 1930103 = 2895155) B2895155
theorem B2749469 : Blo 854356 2749469 := bstep (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) B1031051
theorem B2192417 : Blo 854356 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B1930283 : Blo 854356 1930283 := bstep (se 1 (by rfl) ⟨1447712, by rfl⟩ : syracuseStep 1930283 = 2895425) B2895425
theorem B914491 : Blo 854356 914491 := bstep (se 1 (by rfl) ⟨685868, by rfl⟩ : syracuseStep 914491 = 1371737) B1371737
theorem B4879561 : Blo 854356 4879561 := bstep (se 2 (by rfl) ⟨1829835, by rfl⟩ : syracuseStep 4879561 = 3659671) B3659671
theorem B914747 : Blo 854356 914747 := bstep (se 1 (by rfl) ⟨686060, by rfl⟩ : syracuseStep 914747 = 1372121) B1372121
theorem B1930643 : Blo 854356 1930643 := bstep (se 1 (by rfl) ⟨1447982, by rfl⟩ : syracuseStep 1930643 = 2895965) B2895965
theorem B1930697 : Blo 854356 1930697 := bstep (se 2 (by rfl) ⟨724011, by rfl⟩ : syracuseStep 1930697 = 1448023) B1448023
theorem B2192939 : Blo 854356 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B1373755 : Blo 854356 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B2061911 : Blo 854356 2061911 := bstep (se 1 (by rfl) ⟨1546433, by rfl⟩ : syracuseStep 2061911 = 3092867) B3092867
theorem B2062199 : Blo 854356 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B2783243 : Blo 854356 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B1374479 : Blo 854356 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B5208409 : Blo 854356 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B10418959 : Blo 854356 10418959 := bstep (se 1 (by rfl) ⟨7814219, by rfl⟩ : syracuseStep 10418959 = 15628439) B15628439
theorem B7306631 : Blo 854356 7306631 := bstep (se 1 (by rfl) ⟨5479973, by rfl⟩ : syracuseStep 7306631 = 10959947) B10959947
theorem B3472793 : Blo 854356 3472793 := bstep (se 2 (by rfl) ⟨1302297, by rfl⟩ : syracuseStep 3472793 = 2604595) B2604595
theorem B3079691 : Blo 854356 3079691 := bstep (se 1 (by rfl) ⟨2309768, by rfl⟩ : syracuseStep 3079691 = 4619537) B4619537
theorem B7307009 : Blo 854356 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B2883599 : Blo 854356 2883599 := bstep (se 1 (by rfl) ⟨2162699, by rfl⟩ : syracuseStep 2883599 = 4325399) B4325399
theorem B1540343 : Blo 854356 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B27066689 : Blo 854356 27066689 := bstep (se 2 (by rfl) ⟨10150008, by rfl⟩ : syracuseStep 27066689 = 20300017) B20300017
theorem B1442191 : Blo 854356 1442191 := bstep (se 1 (by rfl) ⟨1081643, by rfl⟩ : syracuseStep 1442191 = 2163287) B2163287
theorem B1081775 : Blo 854356 1081775 := bstep (se 1 (by rfl) ⟨811331, by rfl⟩ : syracuseStep 1081775 = 1622663) B1622663
theorem B6488585 : Blo 854356 6488585 := bstep (se 2 (by rfl) ⟨2433219, by rfl⟩ : syracuseStep 6488585 = 4866439) B4866439
theorem B4883003 : Blo 854356 4883003 := bstep (se 1 (by rfl) ⟨3662252, by rfl⟩ : syracuseStep 4883003 = 7324505) B7324505
theorem B2884193 : Blo 854356 2884193 := bstep (se 2 (by rfl) ⟨1081572, by rfl⟩ : syracuseStep 2884193 = 2163145) B2163145
theorem B2163449 : Blo 854356 2163449 := bstep (se 2 (by rfl) ⟨811293, by rfl⟩ : syracuseStep 2163449 = 1622587) B1622587
theorem B3244961 : Blo 854356 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B2163631 : Blo 854356 2163631 := bstep (se 1 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 2163631 = 3245447) B3245447
theorem B1442873 : Blo 854356 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B6587459 : Blo 854356 6587459 := bstep (se 1 (by rfl) ⟨4940594, by rfl⟩ : syracuseStep 6587459 = 9881189) B9881189
theorem B7308407 : Blo 854356 7308407 := bstep (se 1 (by rfl) ⟨5481305, by rfl⟩ : syracuseStep 7308407 = 10962611) B10962611
theorem B3245417 : Blo 854356 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B2164097 : Blo 854356 2164097 := bstep (se 2 (by rfl) ⟨811536, by rfl⟩ : syracuseStep 2164097 = 1623073) B1623073
theorem B47449529 : Blo 854356 47449529 := bstep (se 2 (by rfl) ⟨17793573, by rfl⟩ : syracuseStep 47449529 = 35587147) B35587147
theorem B4326857 : Blo 854356 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B1443575 : Blo 854356 1443575 := bstep (se 1 (by rfl) ⟨1082681, by rfl⟩ : syracuseStep 1443575 = 2165363) B2165363
theorem B2164553 : Blo 854356 2164553 := bstep (se 2 (by rfl) ⟨811707, by rfl⟩ : syracuseStep 2164553 = 1623415) B1623415
theorem B3245933 : Blo 854356 3245933 := bstep (se 3 (by rfl) ⟨608612, by rfl⟩ : syracuseStep 3245933 = 1217225) B1217225
theorem B6490043 : Blo 854356 6490043 := bstep (se 1 (by rfl) ⟨4867532, by rfl⟩ : syracuseStep 6490043 = 9735065) B9735065
theorem B2885651 : Blo 854356 2885651 := bstep (se 1 (by rfl) ⟨2164238, by rfl⟩ : syracuseStep 2885651 = 4328477) B4328477
theorem B1443919 : Blo 854356 1443919 := bstep (se 1 (by rfl) ⟨1082939, by rfl⟩ : syracuseStep 1443919 = 2165879) B2165879
theorem B4327505 : Blo 854356 4327505 := bstep (se 2 (by rfl) ⟨1622814, by rfl⟩ : syracuseStep 4327505 = 3245629) B3245629
theorem B2164907 : Blo 854356 2164907 := bstep (se 1 (by rfl) ⟨1623680, by rfl⟩ : syracuseStep 2164907 = 3247361) B3247361
theorem B8030513 : Blo 854356 8030513 := bstep (se 2 (by rfl) ⟨3011442, by rfl⟩ : syracuseStep 8030513 = 6022885) B6022885
theorem B1444169 : Blo 854356 1444169 := bstep (se 2 (by rfl) ⟨541563, by rfl⟩ : syracuseStep 1444169 = 1083127) B1083127
theorem B2885975 : Blo 854356 2885975 := bstep (se 1 (by rfl) ⟨2164481, by rfl⟩ : syracuseStep 2885975 = 4328963) B4328963
theorem B854367 : Blo 854356 854367 := bstep (se 1 (by rfl) ⟨640775, by rfl⟩ : syracuseStep 854367 = 1281551) B1281551
theorem B854395 : Blo 854356 854395 := bstep (se 1 (by rfl) ⟨640796, by rfl⟩ : syracuseStep 854395 = 1281593) B1281593
theorem B854447 : Blo 854356 854447 := bstep (se 1 (by rfl) ⟨640835, by rfl⟩ : syracuseStep 854447 = 1281671) B1281671
theorem B854471 : Blo 854356 854471 := bstep (se 1 (by rfl) ⟨640853, by rfl⟩ : syracuseStep 854471 = 1281707) B1281707
theorem B854491 : Blo 854356 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B3246601 : Blo 854356 3246601 := bstep (se 2 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 3246601 = 2434951) B2434951
theorem B854567 : Blo 854356 854567 := bstep (se 1 (by rfl) ⟨640925, by rfl⟩ : syracuseStep 854567 = 1281851) B1281851
theorem B854607 : Blo 854356 854607 := bstep (se 1 (by rfl) ⟨640955, by rfl⟩ : syracuseStep 854607 = 1281911) B1281911
theorem B854623 : Blo 854356 854623 := bstep (se 1 (by rfl) ⟨640967, by rfl⟩ : syracuseStep 854623 = 1281935) B1281935
theorem B854651 : Blo 854356 854651 := bstep (se 1 (by rfl) ⟨640988, by rfl⟩ : syracuseStep 854651 = 1281977) B1281977
theorem B5474951 : Blo 854356 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B854703 : Blo 854356 854703 := bstep (se 1 (by rfl) ⟨641027, by rfl⟩ : syracuseStep 854703 = 1282055) B1282055
theorem B854727 : Blo 854356 854727 := bstep (se 1 (by rfl) ⟨641045, by rfl⟩ : syracuseStep 854727 = 1282091) B1282091
theorem B854747 : Blo 854356 854747 := bstep (se 1 (by rfl) ⟨641060, by rfl⟩ : syracuseStep 854747 = 1282121) B1282121
theorem B1444601 : Blo 854356 1444601 := bstep (se 2 (by rfl) ⟨541725, by rfl⟩ : syracuseStep 1444601 = 1083451) B1083451
theorem B854823 : Blo 854356 854823 := bstep (se 1 (by rfl) ⟨641117, by rfl⟩ : syracuseStep 854823 = 1282235) B1282235
theorem B854863 : Blo 854356 854863 := bstep (se 1 (by rfl) ⟨641147, by rfl⟩ : syracuseStep 854863 = 1282295) B1282295
theorem B854879 : Blo 854356 854879 := bstep (se 1 (by rfl) ⟨641159, by rfl⟩ : syracuseStep 854879 = 1282319) B1282319
theorem B854907 : Blo 854356 854907 := bstep (se 1 (by rfl) ⟨641180, by rfl⟩ : syracuseStep 854907 = 1282361) B1282361
theorem B854959 : Blo 854356 854959 := bstep (se 1 (by rfl) ⟨641219, by rfl⟩ : syracuseStep 854959 = 1282439) B1282439
theorem B1444783 : Blo 854356 1444783 := bstep (se 1 (by rfl) ⟨1083587, by rfl⟩ : syracuseStep 1444783 = 2167175) B2167175
theorem B2165687 : Blo 854356 2165687 := bstep (se 1 (by rfl) ⟨1624265, by rfl⟩ : syracuseStep 2165687 = 3248531) B3248531
theorem B854983 : Blo 854356 854983 := bstep (se 1 (by rfl) ⟨641237, by rfl⟩ : syracuseStep 854983 = 1282475) B1282475
theorem B855003 : Blo 854356 855003 := bstep (se 1 (by rfl) ⟨641252, by rfl⟩ : syracuseStep 855003 = 1282505) B1282505
theorem B2853895 : Blo 854356 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B1444871 : Blo 854356 1444871 := bstep (se 1 (by rfl) ⟨1083653, by rfl⟩ : syracuseStep 1444871 = 2167307) B2167307
theorem B855079 : Blo 854356 855079 := bstep (se 1 (by rfl) ⟨641309, by rfl⟩ : syracuseStep 855079 = 1282619) B1282619
theorem B855119 : Blo 854356 855119 := bstep (se 1 (by rfl) ⟨641339, by rfl⟩ : syracuseStep 855119 = 1282679) B1282679
theorem B855135 : Blo 854356 855135 := bstep (se 1 (by rfl) ⟨641351, by rfl⟩ : syracuseStep 855135 = 1282703) B1282703
theorem B855163 : Blo 854356 855163 := bstep (se 1 (by rfl) ⟨641372, by rfl⟩ : syracuseStep 855163 = 1282745) B1282745
theorem B855215 : Blo 854356 855215 := bstep (se 1 (by rfl) ⟨641411, by rfl⟩ : syracuseStep 855215 = 1282823) B1282823
theorem B855239 : Blo 854356 855239 := bstep (se 1 (by rfl) ⟨641429, by rfl⟩ : syracuseStep 855239 = 1282859) B1282859
theorem B855259 : Blo 854356 855259 := bstep (se 1 (by rfl) ⟨641444, by rfl⟩ : syracuseStep 855259 = 1282889) B1282889
theorem B855335 : Blo 854356 855335 := bstep (se 1 (by rfl) ⟨641501, by rfl⟩ : syracuseStep 855335 = 1283003) B1283003
theorem B855375 : Blo 854356 855375 := bstep (se 1 (by rfl) ⟨641531, by rfl⟩ : syracuseStep 855375 = 1283063) B1283063
theorem B855391 : Blo 854356 855391 := bstep (se 1 (by rfl) ⟨641543, by rfl⟩ : syracuseStep 855391 = 1283087) B1283087
theorem B1445215 : Blo 854356 1445215 := bstep (se 1 (by rfl) ⟨1083911, by rfl⟩ : syracuseStep 1445215 = 2167823) B2167823
theorem B855419 : Blo 854356 855419 := bstep (se 1 (by rfl) ⟨641564, by rfl⟩ : syracuseStep 855419 = 1283129) B1283129
theorem B2887055 : Blo 854356 2887055 := bstep (se 1 (by rfl) ⟨2165291, by rfl⟩ : syracuseStep 2887055 = 4330583) B4330583
theorem B16944527 : Blo 854356 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B855471 : Blo 854356 855471 := bstep (se 1 (by rfl) ⟨641603, by rfl⟩ : syracuseStep 855471 = 1283207) B1283207
theorem B1445303 : Blo 854356 1445303 := bstep (se 1 (by rfl) ⟨1083977, by rfl⟩ : syracuseStep 1445303 = 2167955) B2167955
theorem B855495 : Blo 854356 855495 := bstep (se 1 (by rfl) ⟨641621, by rfl⟩ : syracuseStep 855495 = 1283243) B1283243
theorem B855515 : Blo 854356 855515 := bstep (se 1 (by rfl) ⟨641636, by rfl⟩ : syracuseStep 855515 = 1283273) B1283273
theorem B1281545 : Blo 854356 1281545 := bstep (se 2 (by rfl) ⟨480579, by rfl⟩ : syracuseStep 1281545 = 961159) B961159
theorem B1281575 : Blo 854356 1281575 := bstep (se 1 (by rfl) ⟨961181, by rfl⟩ : syracuseStep 1281575 = 1922363) B1922363
theorem B855591 : Blo 854356 855591 := bstep (se 1 (by rfl) ⟨641693, by rfl⟩ : syracuseStep 855591 = 1283387) B1283387
theorem B855631 : Blo 854356 855631 := bstep (se 1 (by rfl) ⟨641723, by rfl⟩ : syracuseStep 855631 = 1283447) B1283447
theorem B855647 : Blo 854356 855647 := bstep (se 1 (by rfl) ⟨641735, by rfl⟩ : syracuseStep 855647 = 1283471) B1283471
theorem B1281659 : Blo 854356 1281659 := bstep (se 1 (by rfl) ⟨961244, by rfl⟩ : syracuseStep 1281659 = 1922489) B1922489
theorem B855675 : Blo 854356 855675 := bstep (se 1 (by rfl) ⟨641756, by rfl⟩ : syracuseStep 855675 = 1283513) B1283513
theorem B3968635 : Blo 854356 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B855727 : Blo 854356 855727 := bstep (se 1 (by rfl) ⟨641795, by rfl⟩ : syracuseStep 855727 = 1283591) B1283591
theorem B855751 : Blo 854356 855751 := bstep (se 1 (by rfl) ⟨641813, by rfl⟩ : syracuseStep 855751 = 1283627) B1283627
theorem B2887379 : Blo 854356 2887379 := bstep (se 1 (by rfl) ⟨2165534, by rfl⟩ : syracuseStep 2887379 = 4331069) B4331069
theorem B855771 : Blo 854356 855771 := bstep (se 1 (by rfl) ⟨641828, by rfl⟩ : syracuseStep 855771 = 1283657) B1283657
theorem B8228573 : Blo 854356 8228573 := bstep (se 3 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 8228573 = 3085715) B3085715
theorem B1281785 : Blo 854356 1281785 := bstep (se 2 (by rfl) ⟨480669, by rfl⟩ : syracuseStep 1281785 = 961339) B961339
theorem B855847 : Blo 854356 855847 := bstep (se 1 (by rfl) ⟨641885, by rfl⟩ : syracuseStep 855847 = 1283771) B1283771
theorem B855887 : Blo 854356 855887 := bstep (se 1 (by rfl) ⟨641915, by rfl⟩ : syracuseStep 855887 = 1283831) B1283831
theorem B1281887 : Blo 854356 1281887 := bstep (se 1 (by rfl) ⟨961415, by rfl⟩ : syracuseStep 1281887 = 1922831) B1922831
theorem B855903 : Blo 854356 855903 := bstep (se 1 (by rfl) ⟨641927, by rfl⟩ : syracuseStep 855903 = 1283855) B1283855
theorem B1281899 : Blo 854356 1281899 := bstep (se 1 (by rfl) ⟨961424, by rfl⟩ : syracuseStep 1281899 = 1922849) B1922849
theorem B855931 : Blo 854356 855931 := bstep (se 1 (by rfl) ⟨641948, by rfl⟩ : syracuseStep 855931 = 1283897) B1283897
theorem B2166689 : Blo 854356 2166689 := bstep (se 2 (by rfl) ⟨812508, by rfl⟩ : syracuseStep 2166689 = 1625017) B1625017
theorem B855983 : Blo 854356 855983 := bstep (se 1 (by rfl) ⟨641987, by rfl⟩ : syracuseStep 855983 = 1283975) B1283975
theorem B3248059 : Blo 854356 3248059 := bstep (se 1 (by rfl) ⟨2436044, by rfl⟩ : syracuseStep 3248059 = 4872089) B4872089
theorem B856007 : Blo 854356 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B856027 : Blo 854356 856027 := bstep (se 1 (by rfl) ⟨642020, by rfl⟩ : syracuseStep 856027 = 1284041) B1284041
theorem B1445897 : Blo 854356 1445897 := bstep (se 2 (by rfl) ⟨542211, by rfl⟩ : syracuseStep 1445897 = 1084423) B1084423
theorem B856103 : Blo 854356 856103 := bstep (se 1 (by rfl) ⟨642077, by rfl⟩ : syracuseStep 856103 = 1284155) B1284155
theorem B1282127 : Blo 854356 1282127 := bstep (se 1 (by rfl) ⟨961595, by rfl⟩ : syracuseStep 1282127 = 1923191) B1923191
theorem B856143 : Blo 854356 856143 := bstep (se 1 (by rfl) ⟨642107, by rfl⟩ : syracuseStep 856143 = 1284215) B1284215
theorem B856159 : Blo 854356 856159 := bstep (se 1 (by rfl) ⟨642119, by rfl⟩ : syracuseStep 856159 = 1284239) B1284239
theorem B856187 : Blo 854356 856187 := bstep (se 1 (by rfl) ⟨642140, by rfl⟩ : syracuseStep 856187 = 1284281) B1284281
theorem B1446059 : Blo 854356 1446059 := bstep (se 1 (by rfl) ⟨1084544, by rfl⟩ : syracuseStep 1446059 = 2169089) B2169089
theorem B856239 : Blo 854356 856239 := bstep (se 1 (by rfl) ⟨642179, by rfl⟩ : syracuseStep 856239 = 1284359) B1284359
theorem B1282247 : Blo 854356 1282247 := bstep (se 1 (by rfl) ⟨961685, by rfl⟩ : syracuseStep 1282247 = 1923371) B1923371
theorem B856263 : Blo 854356 856263 := bstep (se 1 (by rfl) ⟨642197, by rfl⟩ : syracuseStep 856263 = 1284395) B1284395
theorem B856283 : Blo 854356 856283 := bstep (se 1 (by rfl) ⟨642212, by rfl⟩ : syracuseStep 856283 = 1284425) B1284425
theorem B856359 : Blo 854356 856359 := bstep (se 1 (by rfl) ⟨642269, by rfl⟩ : syracuseStep 856359 = 1284539) B1284539
theorem B9736523 : Blo 854356 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B856399 : Blo 854356 856399 := bstep (se 1 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 856399 = 1284599) B1284599
theorem B856415 : Blo 854356 856415 := bstep (se 1 (by rfl) ⟨642311, by rfl⟩ : syracuseStep 856415 = 1284623) B1284623
theorem B1282409 : Blo 854356 1282409 := bstep (se 2 (by rfl) ⟨480903, by rfl⟩ : syracuseStep 1282409 = 961807) B961807
theorem B2167145 : Blo 854356 2167145 := bstep (se 2 (by rfl) ⟨812679, by rfl⟩ : syracuseStep 2167145 = 1625359) B1625359
theorem B856443 : Blo 854356 856443 := bstep (se 1 (by rfl) ⟨642332, by rfl⟩ : syracuseStep 856443 = 1284665) B1284665
theorem B856495 : Blo 854356 856495 := bstep (se 1 (by rfl) ⟨642371, by rfl⟩ : syracuseStep 856495 = 1284743) B1284743
theorem B1282487 : Blo 854356 1282487 := bstep (se 1 (by rfl) ⟨961865, by rfl⟩ : syracuseStep 1282487 = 1923731) B1923731
theorem B856519 : Blo 854356 856519 := bstep (se 1 (by rfl) ⟨642389, by rfl⟩ : syracuseStep 856519 = 1284779) B1284779
theorem B1282523 : Blo 854356 1282523 := bstep (se 1 (by rfl) ⟨961892, by rfl⟩ : syracuseStep 1282523 = 1923785) B1923785
theorem B856539 : Blo 854356 856539 := bstep (se 1 (by rfl) ⟨642404, by rfl⟩ : syracuseStep 856539 = 1284809) B1284809
theorem B35164637 : Blo 854356 35164637 := bstep (se 3 (by rfl) ⟨6593369, by rfl⟩ : syracuseStep 35164637 = 13186739) B13186739
theorem B3478049 : Blo 854356 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B856615 : Blo 854356 856615 := bstep (se 1 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 856615 = 1284923) B1284923
theorem B1446457 : Blo 854356 1446457 := bstep (se 2 (by rfl) ⟨542421, by rfl⟩ : syracuseStep 1446457 = 1084843) B1084843
theorem B856655 : Blo 854356 856655 := bstep (se 1 (by rfl) ⟨642491, by rfl⟩ : syracuseStep 856655 = 1284983) B1284983
theorem B856671 : Blo 854356 856671 := bstep (se 1 (by rfl) ⟨642503, by rfl⟩ : syracuseStep 856671 = 1285007) B1285007
theorem B856699 : Blo 854356 856699 := bstep (se 1 (by rfl) ⟨642524, by rfl⟩ : syracuseStep 856699 = 1285049) B1285049
theorem B856751 : Blo 854356 856751 := bstep (se 1 (by rfl) ⟨642563, by rfl⟩ : syracuseStep 856751 = 1285127) B1285127
theorem B856775 : Blo 854356 856775 := bstep (se 1 (by rfl) ⟨642581, by rfl⟩ : syracuseStep 856775 = 1285163) B1285163
theorem B1446599 : Blo 854356 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B3248849 : Blo 854356 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B856795 : Blo 854356 856795 := bstep (se 1 (by rfl) ⟨642596, by rfl⟩ : syracuseStep 856795 = 1285193) B1285193
theorem B856871 : Blo 854356 856871 := bstep (se 1 (by rfl) ⟨642653, by rfl⟩ : syracuseStep 856871 = 1285307) B1285307
theorem B856911 : Blo 854356 856911 := bstep (se 1 (by rfl) ⟨642683, by rfl⟩ : syracuseStep 856911 = 1285367) B1285367
theorem B856927 : Blo 854356 856927 := bstep (se 1 (by rfl) ⟨642695, by rfl⟩ : syracuseStep 856927 = 1285391) B1285391
theorem B1446761 : Blo 854356 1446761 := bstep (se 2 (by rfl) ⟨542535, by rfl⟩ : syracuseStep 1446761 = 1085071) B1085071
theorem B2888567 : Blo 854356 2888567 := bstep (se 1 (by rfl) ⟨2166425, by rfl⟩ : syracuseStep 2888567 = 4332851) B4332851
theorem B856955 : Blo 854356 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B1282991 : Blo 854356 1282991 := bstep (se 1 (by rfl) ⟨962243, by rfl⟩ : syracuseStep 1282991 = 1924487) B1924487
theorem B857007 : Blo 854356 857007 := bstep (se 1 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 857007 = 1285511) B1285511
theorem B857031 : Blo 854356 857031 := bstep (se 1 (by rfl) ⟨642773, by rfl⟩ : syracuseStep 857031 = 1285547) B1285547
theorem B857051 : Blo 854356 857051 := bstep (se 1 (by rfl) ⟨642788, by rfl⟩ : syracuseStep 857051 = 1285577) B1285577
theorem B1283081 : Blo 854356 1283081 := bstep (se 2 (by rfl) ⟨481155, by rfl⟩ : syracuseStep 1283081 = 962311) B962311
theorem B1283111 : Blo 854356 1283111 := bstep (se 1 (by rfl) ⟨962333, by rfl⟩ : syracuseStep 1283111 = 1924667) B1924667
theorem B857127 : Blo 854356 857127 := bstep (se 1 (by rfl) ⟨642845, by rfl⟩ : syracuseStep 857127 = 1285691) B1285691
theorem B2888783 : Blo 854356 2888783 := bstep (se 1 (by rfl) ⟨2166587, by rfl⟩ : syracuseStep 2888783 = 4333175) B4333175
theorem B857167 : Blo 854356 857167 := bstep (se 1 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 857167 = 1285751) B1285751
theorem B857183 : Blo 854356 857183 := bstep (se 1 (by rfl) ⟨642887, by rfl⟩ : syracuseStep 857183 = 1285775) B1285775
theorem B3085427 : Blo 854356 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B1283195 : Blo 854356 1283195 := bstep (se 1 (by rfl) ⟨962396, by rfl⟩ : syracuseStep 1283195 = 1924793) B1924793
theorem B857211 : Blo 854356 857211 := bstep (se 1 (by rfl) ⟨642908, by rfl⟩ : syracuseStep 857211 = 1285817) B1285817
theorem B3249305 : Blo 854356 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B857263 : Blo 854356 857263 := bstep (se 1 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 857263 = 1285895) B1285895
theorem B857287 : Blo 854356 857287 := bstep (se 1 (by rfl) ⟨642965, by rfl⟩ : syracuseStep 857287 = 1285931) B1285931
theorem B6952139 : Blo 854356 6952139 := bstep (se 1 (by rfl) ⟨5214104, by rfl⟩ : syracuseStep 6952139 = 10428209) B10428209
theorem B857307 : Blo 854356 857307 := bstep (se 1 (by rfl) ⟨642980, by rfl⟩ : syracuseStep 857307 = 1285961) B1285961
theorem B1447159 : Blo 854356 1447159 := bstep (se 1 (by rfl) ⟨1085369, by rfl⟩ : syracuseStep 1447159 = 2170739) B2170739
theorem B1283321 : Blo 854356 1283321 := bstep (se 2 (by rfl) ⟨481245, by rfl⟩ : syracuseStep 1283321 = 962491) B962491
theorem B857383 : Blo 854356 857383 := bstep (se 1 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 857383 = 1286075) B1286075
theorem B857423 : Blo 854356 857423 := bstep (se 1 (by rfl) ⟨643067, by rfl⟩ : syracuseStep 857423 = 1286135) B1286135
theorem B1283423 : Blo 854356 1283423 := bstep (se 1 (by rfl) ⟨962567, by rfl⟩ : syracuseStep 1283423 = 1925135) B1925135
theorem B857439 : Blo 854356 857439 := bstep (se 1 (by rfl) ⟨643079, by rfl⟩ : syracuseStep 857439 = 1286159) B1286159
theorem B1283435 : Blo 854356 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B857467 : Blo 854356 857467 := bstep (se 1 (by rfl) ⟨643100, by rfl⟩ : syracuseStep 857467 = 1286201) B1286201
theorem B857519 : Blo 854356 857519 := bstep (se 1 (by rfl) ⟨643139, by rfl⟩ : syracuseStep 857519 = 1286279) B1286279
theorem B1447355 : Blo 854356 1447355 := bstep (se 1 (by rfl) ⟨1085516, by rfl⟩ : syracuseStep 1447355 = 2171033) B2171033
theorem B857543 : Blo 854356 857543 := bstep (se 1 (by rfl) ⟨643157, by rfl⟩ : syracuseStep 857543 = 1286315) B1286315
theorem B2889161 : Blo 854356 2889161 := bstep (se 2 (by rfl) ⟨1083435, by rfl⟩ : syracuseStep 2889161 = 2166871) B2166871
theorem B857563 : Blo 854356 857563 := bstep (se 1 (by rfl) ⟨643172, by rfl⟩ : syracuseStep 857563 = 1286345) B1286345
theorem B3479021 : Blo 854356 3479021 := bstep (se 3 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 3479021 = 1304633) B1304633
theorem B2168329 : Blo 854356 2168329 := bstep (se 2 (by rfl) ⟨813123, by rfl⟩ : syracuseStep 2168329 = 1626247) B1626247
theorem B857639 : Blo 854356 857639 := bstep (se 1 (by rfl) ⟨643229, by rfl⟩ : syracuseStep 857639 = 1286459) B1286459
theorem B1447463 : Blo 854356 1447463 := bstep (se 1 (by rfl) ⟨1085597, by rfl⟩ : syracuseStep 1447463 = 2171195) B2171195
theorem B1283663 : Blo 854356 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B857679 : Blo 854356 857679 := bstep (se 1 (by rfl) ⟨643259, by rfl⟩ : syracuseStep 857679 = 1286519) B1286519
theorem B857695 : Blo 854356 857695 := bstep (se 1 (by rfl) ⟨643271, by rfl⟩ : syracuseStep 857695 = 1286543) B1286543
theorem B857723 : Blo 854356 857723 := bstep (se 1 (by rfl) ⟨643292, by rfl⟩ : syracuseStep 857723 = 1286585) B1286585
theorem B857775 : Blo 854356 857775 := bstep (se 1 (by rfl) ⟨643331, by rfl⟩ : syracuseStep 857775 = 1286663) B1286663
theorem B1283783 : Blo 854356 1283783 := bstep (se 1 (by rfl) ⟨962837, by rfl⟩ : syracuseStep 1283783 = 1925675) B1925675
theorem B857799 : Blo 854356 857799 := bstep (se 1 (by rfl) ⟨643349, by rfl⟩ : syracuseStep 857799 = 1286699) B1286699
theorem B2889431 : Blo 854356 2889431 := bstep (se 1 (by rfl) ⟨2167073, by rfl⟩ : syracuseStep 2889431 = 4334147) B4334147
theorem B857819 : Blo 854356 857819 := bstep (se 1 (by rfl) ⟨643364, by rfl⟩ : syracuseStep 857819 = 1286729) B1286729
theorem B857895 : Blo 854356 857895 := bstep (se 1 (by rfl) ⟨643421, by rfl⟩ : syracuseStep 857895 = 1286843) B1286843
theorem B1447753 : Blo 854356 1447753 := bstep (se 2 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 1447753 = 1085815) B1085815
theorem B857935 : Blo 854356 857935 := bstep (se 1 (by rfl) ⟨643451, by rfl⟩ : syracuseStep 857935 = 1286903) B1286903
theorem B857951 : Blo 854356 857951 := bstep (se 1 (by rfl) ⟨643463, by rfl⟩ : syracuseStep 857951 = 1286927) B1286927
theorem B1283945 : Blo 854356 1283945 := bstep (se 2 (by rfl) ⟨481479, by rfl⟩ : syracuseStep 1283945 = 962959) B962959
theorem B1447787 : Blo 854356 1447787 := bstep (se 1 (by rfl) ⟨1085840, by rfl⟩ : syracuseStep 1447787 = 2171681) B2171681
theorem B857979 : Blo 854356 857979 := bstep (se 1 (by rfl) ⟨643484, by rfl⟩ : syracuseStep 857979 = 1286969) B1286969
theorem B2889647 : Blo 854356 2889647 := bstep (se 1 (by rfl) ⟨2167235, by rfl⟩ : syracuseStep 2889647 = 4334471) B4334471
theorem B858031 : Blo 854356 858031 := bstep (se 1 (by rfl) ⟨643523, by rfl⟩ : syracuseStep 858031 = 1287047) B1287047
theorem B1284023 : Blo 854356 1284023 := bstep (se 1 (by rfl) ⟨963017, by rfl⟩ : syracuseStep 1284023 = 1926035) B1926035
theorem B858055 : Blo 854356 858055 := bstep (se 1 (by rfl) ⟨643541, by rfl⟩ : syracuseStep 858055 = 1287083) B1287083
theorem B1284059 : Blo 854356 1284059 := bstep (se 1 (by rfl) ⟨963044, by rfl⟩ : syracuseStep 1284059 = 1926089) B1926089
theorem B858075 : Blo 854356 858075 := bstep (se 1 (by rfl) ⟨643556, by rfl⟩ : syracuseStep 858075 = 1287113) B1287113
theorem B4888583 : Blo 854356 4888583 := bstep (se 1 (by rfl) ⟨3666437, by rfl⟩ : syracuseStep 4888583 = 7332875) B7332875
theorem B1218569 : Blo 854356 1218569 := bstep (se 2 (by rfl) ⟨456963, by rfl⟩ : syracuseStep 1218569 = 913927) B913927
theorem B858151 : Blo 854356 858151 := bstep (se 1 (by rfl) ⟨643613, by rfl⟩ : syracuseStep 858151 = 1287227) B1287227
theorem B3348559 : Blo 854356 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B858191 : Blo 854356 858191 := bstep (se 1 (by rfl) ⟨643643, by rfl⟩ : syracuseStep 858191 = 1287287) B1287287
theorem B858207 : Blo 854356 858207 := bstep (se 1 (by rfl) ⟨643655, by rfl⟩ : syracuseStep 858207 = 1287311) B1287311
theorem B1218683 : Blo 854356 1218683 := bstep (se 1 (by rfl) ⟨914012, by rfl⟩ : syracuseStep 1218683 = 1828025) B1828025
theorem B858235 : Blo 854356 858235 := bstep (se 1 (by rfl) ⟨643676, by rfl⟩ : syracuseStep 858235 = 1287353) B1287353
theorem B858287 : Blo 854356 858287 := bstep (se 1 (by rfl) ⟨643715, by rfl⟩ : syracuseStep 858287 = 1287431) B1287431
theorem B858311 : Blo 854356 858311 := bstep (se 1 (by rfl) ⟨643733, by rfl⟩ : syracuseStep 858311 = 1287467) B1287467
theorem B858331 : Blo 854356 858331 := bstep (se 1 (by rfl) ⟨643748, by rfl⟩ : syracuseStep 858331 = 1287497) B1287497
theorem B1448185 : Blo 854356 1448185 := bstep (se 2 (by rfl) ⟨543069, by rfl⟩ : syracuseStep 1448185 = 1086139) B1086139
theorem B7051625 : Blo 854356 7051625 := bstep (se 2 (by rfl) ⟨2644359, by rfl⟩ : syracuseStep 7051625 = 5288719) B5288719
theorem B1218991 : Blo 854356 1218991 := bstep (se 1 (by rfl) ⟨914243, by rfl⟩ : syracuseStep 1218991 = 1828487) B1828487
theorem B1284527 : Blo 854356 1284527 := bstep (se 1 (by rfl) ⟨963395, by rfl⟩ : syracuseStep 1284527 = 1926791) B1926791
theorem B1448455 : Blo 854356 1448455 := bstep (se 1 (by rfl) ⟨1086341, by rfl⟩ : syracuseStep 1448455 = 2172683) B2172683
theorem B4332041 : Blo 854356 4332041 := bstep (se 2 (by rfl) ⟨1624515, by rfl⟩ : syracuseStep 4332041 = 3249031) B3249031
theorem B1284617 : Blo 854356 1284617 := bstep (se 2 (by rfl) ⟨481731, by rfl⟩ : syracuseStep 1284617 = 963463) B963463
theorem B1284647 : Blo 854356 1284647 := bstep (se 1 (by rfl) ⟨963485, by rfl⟩ : syracuseStep 1284647 = 1926971) B1926971
theorem B1284731 : Blo 854356 1284731 := bstep (se 1 (by rfl) ⟨963548, by rfl⟩ : syracuseStep 1284731 = 1927097) B1927097
theorem B5085881 : Blo 854356 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B1219321 : Blo 854356 1219321 := bstep (se 2 (by rfl) ⟨457245, by rfl⟩ : syracuseStep 1219321 = 914491) B914491
theorem B1284857 : Blo 854356 1284857 := bstep (se 2 (by rfl) ⟨481821, by rfl⟩ : syracuseStep 1284857 = 963643) B963643
theorem B1284959 : Blo 854356 1284959 := bstep (se 1 (by rfl) ⟨963719, by rfl⟩ : syracuseStep 1284959 = 1927439) B1927439
theorem B1284971 : Blo 854356 1284971 := bstep (se 1 (by rfl) ⟨963728, by rfl⟩ : syracuseStep 1284971 = 1927457) B1927457
theorem B2169787 : Blo 854356 2169787 := bstep (se 1 (by rfl) ⟨1627340, by rfl⟩ : syracuseStep 2169787 = 3254681) B3254681
theorem B3251279 : Blo 854356 3251279 := bstep (se 1 (by rfl) ⟨2438459, by rfl⟩ : syracuseStep 3251279 = 4876919) B4876919
theorem B1285199 : Blo 854356 1285199 := bstep (se 1 (by rfl) ⟨963899, by rfl⟩ : syracuseStep 1285199 = 1927799) B1927799
theorem B1285319 : Blo 854356 1285319 := bstep (se 1 (by rfl) ⟨963989, by rfl⟩ : syracuseStep 1285319 = 1927979) B1927979
theorem B3251447 : Blo 854356 3251447 := bstep (se 1 (by rfl) ⟨2438585, by rfl⟩ : syracuseStep 3251447 = 4877171) B4877171
theorem B1285481 : Blo 854356 1285481 := bstep (se 2 (by rfl) ⟨482055, by rfl⟩ : syracuseStep 1285481 = 964111) B964111
theorem B4398461 : Blo 854356 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B1285559 : Blo 854356 1285559 := bstep (se 1 (by rfl) ⟨964169, by rfl⟩ : syracuseStep 1285559 = 1928339) B1928339
theorem B1285595 : Blo 854356 1285595 := bstep (se 1 (by rfl) ⟨964196, by rfl⟩ : syracuseStep 1285595 = 1928393) B1928393
theorem B7806451 : Blo 854356 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B5480075 : Blo 854356 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B1286063 : Blo 854356 1286063 := bstep (se 1 (by rfl) ⟨964547, by rfl⟩ : syracuseStep 1286063 = 1929095) B1929095
theorem B4333499 : Blo 854356 4333499 := bstep (se 1 (by rfl) ⟨3250124, by rfl⟩ : syracuseStep 4333499 = 6500249) B6500249
theorem B1286153 : Blo 854356 1286153 := bstep (se 2 (by rfl) ⟨482307, by rfl⟩ : syracuseStep 1286153 = 964615) B964615
theorem B1286183 : Blo 854356 1286183 := bstep (se 1 (by rfl) ⟨964637, by rfl⟩ : syracuseStep 1286183 = 1929275) B1929275
theorem B1286267 : Blo 854356 1286267 := bstep (se 1 (by rfl) ⟨964700, by rfl⟩ : syracuseStep 1286267 = 1929401) B1929401
theorem B3252419 : Blo 854356 3252419 := bstep (se 1 (by rfl) ⟨2439314, by rfl⟩ : syracuseStep 3252419 = 4878629) B4878629
theorem B2892023 : Blo 854356 2892023 := bstep (se 1 (by rfl) ⟨2169017, by rfl⟩ : syracuseStep 2892023 = 4338035) B4338035
theorem B1286393 : Blo 854356 1286393 := bstep (se 2 (by rfl) ⟨482397, by rfl⟩ : syracuseStep 1286393 = 964795) B964795
theorem B1286495 : Blo 854356 1286495 := bstep (se 1 (by rfl) ⟨964871, by rfl⟩ : syracuseStep 1286495 = 1929743) B1929743
theorem B1286507 : Blo 854356 1286507 := bstep (se 1 (by rfl) ⟨964880, by rfl⟩ : syracuseStep 1286507 = 1929761) B1929761
theorem B2892347 : Blo 854356 2892347 := bstep (se 1 (by rfl) ⟨2169260, by rfl⟩ : syracuseStep 2892347 = 4338521) B4338521
theorem B1286735 : Blo 854356 1286735 := bstep (se 1 (by rfl) ⟨965051, by rfl⟩ : syracuseStep 1286735 = 1930103) B1930103
theorem B8233645 : Blo 854356 8233645 := bstep (se 3 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 8233645 = 3087617) B3087617
theorem B1286855 : Blo 854356 1286855 := bstep (se 1 (by rfl) ⟨965141, by rfl⟩ : syracuseStep 1286855 = 1930283) B1930283
theorem B2892617 : Blo 854356 2892617 := bstep (se 2 (by rfl) ⟨1084731, by rfl⟩ : syracuseStep 2892617 = 2169463) B2169463
theorem B1287017 : Blo 854356 1287017 := bstep (se 2 (by rfl) ⟨482631, by rfl⟩ : syracuseStep 1287017 = 965263) B965263
theorem B3089335 : Blo 854356 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B1287095 : Blo 854356 1287095 := bstep (se 1 (by rfl) ⟨965321, by rfl⟩ : syracuseStep 1287095 = 1930643) B1930643
theorem B1287131 : Blo 854356 1287131 := bstep (se 1 (by rfl) ⟨965348, by rfl⟩ : syracuseStep 1287131 = 1930697) B1930697
theorem B3253405 : Blo 854356 3253405 := bstep (se 3 (by rfl) ⟨610013, by rfl⟩ : syracuseStep 3253405 = 1220027) B1220027
theorem B4334795 : Blo 854356 4334795 := bstep (se 1 (by rfl) ⟨3251096, by rfl⟩ : syracuseStep 4334795 = 6502193) B6502193
theorem B4760957 : Blo 854356 4760957 := bstep (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) B1785359
theorem B2172379 : Blo 854356 2172379 := bstep (se 1 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 2172379 = 3258569) B3258569
theorem B14657273 : Blo 854356 14657273 := bstep (se 2 (by rfl) ⟨5496477, by rfl⟩ : syracuseStep 14657273 = 10992955) B10992955
theorem B2893751 : Blo 854356 2893751 := bstep (se 1 (by rfl) ⟨2170313, by rfl⟩ : syracuseStep 2893751 = 4340627) B4340627
theorem B1976399 : Blo 854356 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B2435453 : Blo 854356 2435453 := bstep (se 3 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 2435453 = 913295) B913295
theorem B2894345 : Blo 854356 2894345 := bstep (se 2 (by rfl) ⟨1085379, by rfl⟩ : syracuseStep 2894345 = 2170759) B2170759
theorem B2435795 : Blo 854356 2435795 := bstep (se 1 (by rfl) ⟨1826846, by rfl⟩ : syracuseStep 2435795 = 3653693) B3653693
theorem B961375 : Blo 854356 961375 := bstep (se 1 (by rfl) ⟨721031, by rfl⟩ : syracuseStep 961375 = 1442063) B1442063
theorem B961735 : Blo 854356 961735 := bstep (se 1 (by rfl) ⟨721301, by rfl⟩ : syracuseStep 961735 = 1442603) B1442603
theorem B2895209 : Blo 854356 2895209 := bstep (se 2 (by rfl) ⟨1085703, by rfl⟩ : syracuseStep 2895209 = 2171407) B2171407
theorem B1486255 : Blo 854356 1486255 := bstep (se 1 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 1486255 = 2229383) B2229383
theorem B2436797 : Blo 854356 2436797 := bstep (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) B913799
theorem B11710169 : Blo 854356 11710169 := bstep (se 2 (by rfl) ⟨4391313, by rfl⟩ : syracuseStep 11710169 = 8782627) B8782627
theorem B2895803 : Blo 854356 2895803 := bstep (se 1 (by rfl) ⟨2171852, by rfl⟩ : syracuseStep 2895803 = 4343705) B4343705
theorem B3256321 : Blo 854356 3256321 := bstep (se 2 (by rfl) ⟨1221120, by rfl⟩ : syracuseStep 3256321 = 2442241) B2442241
theorem B962599 : Blo 854356 962599 := bstep (se 1 (by rfl) ⟨721949, by rfl⟩ : syracuseStep 962599 = 1443899) B1443899
theorem B3649693 : Blo 854356 3649693 := bstep (se 3 (by rfl) ⟨684317, by rfl⟩ : syracuseStep 3649693 = 1368635) B1368635
theorem B10400467 : Blo 854356 10400467 := bstep (se 1 (by rfl) ⟨7800350, by rfl⟩ : syracuseStep 10400467 = 15600701) B15600701
theorem B3257081 : Blo 854356 3257081 := bstep (se 2 (by rfl) ⟨1221405, by rfl⟩ : syracuseStep 3257081 = 2442811) B2442811
theorem B10433555 : Blo 854356 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B2602063 : Blo 854356 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B3519683 : Blo 854356 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B7320779 : Blo 854356 7320779 := bstep (se 1 (by rfl) ⟨5490584, by rfl⟩ : syracuseStep 7320779 = 10981169) B10981169
theorem B5551703 : Blo 854356 5551703 := bstep (se 1 (by rfl) ⟨4163777, by rfl⟩ : syracuseStep 5551703 = 8327555) B8327555
theorem B964219 : Blo 854356 964219 := bstep (se 1 (by rfl) ⟨723164, by rfl⟩ : syracuseStep 964219 = 1446329) B1446329
theorem B2471639 : Blo 854356 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B13907771 : Blo 854356 13907771 := bstep (se 1 (by rfl) ⟨10430828, by rfl⟩ : syracuseStep 13907771 = 20861657) B20861657
theorem B5551939 : Blo 854356 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B5945183 : Blo 854356 5945183 := bstep (se 1 (by rfl) ⟨4458887, by rfl⟩ : syracuseStep 5945183 = 8917775) B8917775
theorem B866171 : Blo 854356 866171 := bstep (se 1 (by rfl) ⟨649628, by rfl⟩ : syracuseStep 866171 = 1299257) B1299257
theorem B964687 : Blo 854356 964687 := bstep (se 1 (by rfl) ⟨723515, by rfl⟩ : syracuseStep 964687 = 1447031) B1447031
theorem B2439325 : Blo 854356 2439325 := bstep (se 3 (by rfl) ⟨457373, by rfl⟩ : syracuseStep 2439325 = 914747) B914747
theorem B3258539 : Blo 854356 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B4339979 : Blo 854356 4339979 := bstep (se 1 (by rfl) ⟨3254984, by rfl⟩ : syracuseStep 4339979 = 6509969) B6509969
theorem B2439553 : Blo 854356 2439553 := bstep (se 2 (by rfl) ⟨914832, by rfl⟩ : syracuseStep 2439553 = 1829665) B1829665
theorem B965083 : Blo 854356 965083 := bstep (se 1 (by rfl) ⟨723812, by rfl⟩ : syracuseStep 965083 = 1447625) B1447625
theorem B2439895 : Blo 854356 2439895 := bstep (se 1 (by rfl) ⟨1829921, by rfl⟩ : syracuseStep 2439895 = 3659843) B3659843
theorem B4111211 : Blo 854356 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B2636705 : Blo 854356 2636705 := bstep (se 2 (by rfl) ⟨988764, by rfl⟩ : syracuseStep 2636705 = 1977529) B1977529
theorem B965551 : Blo 854356 965551 := bstep (se 1 (by rfl) ⟨724163, by rfl⟩ : syracuseStep 965551 = 1448327) B1448327
theorem B5488073 : Blo 854356 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B4341437 : Blo 854356 4341437 := bstep (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) B1628039
theorem B3653369 : Blo 854356 3653369 := bstep (se 2 (by rfl) ⟨1370013, by rfl⟩ : syracuseStep 3653369 = 2740027) B2740027
theorem B4341599 : Blo 854356 4341599 := bstep (se 1 (by rfl) ⟨3256199, by rfl⟩ : syracuseStep 4341599 = 6512399) B6512399
theorem B4112441 : Blo 854356 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B3620945 : Blo 854356 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B5554433 : Blo 854356 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B2933371 : Blo 854356 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B1622891 : Blo 854356 1622891 := bstep (se 1 (by rfl) ⟨1217168, by rfl⟩ : syracuseStep 1622891 = 2434337) B2434337
theorem B1623559 : Blo 854356 1623559 := bstep (se 1 (by rfl) ⟨1217669, by rfl⟩ : syracuseStep 1623559 = 2435339) B2435339
theorem B6506081 : Blo 854356 6506081 := bstep (se 2 (by rfl) ⟨2439780, by rfl⟩ : syracuseStep 6506081 = 4879561) B4879561
theorem B4638347 : Blo 854356 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B3655367 : Blo 854356 3655367 := bstep (se 1 (by rfl) ⟨2741525, by rfl⟩ : syracuseStep 3655367 = 5483051) B5483051
theorem B1624121 : Blo 854356 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B12372101 : Blo 854356 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B4639037 : Blo 854356 4639037 := bstep (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) B1739639
theorem B5491147 : Blo 854356 5491147 := bstep (se 1 (by rfl) ⟨4118360, by rfl⟩ : syracuseStep 5491147 = 8236721) B8236721
theorem B4344353 : Blo 854356 4344353 := bstep (se 2 (by rfl) ⟨1629132, by rfl⟩ : syracuseStep 4344353 = 3258265) B3258265
theorem B6933127 : Blo 854356 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B1756009 : Blo 854356 1756009 := bstep (se 2 (by rfl) ⟨658503, by rfl⟩ : syracuseStep 1756009 = 1317007) B1317007
theorem B36162449 : Blo 854356 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B2968595 : Blo 854356 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B6507539 : Blo 854356 6507539 := bstep (se 1 (by rfl) ⟨4880654, by rfl⟩ : syracuseStep 6507539 = 9761309) B9761309
theorem B5491763 : Blo 854356 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B1461611 : Blo 854356 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B2936189 : Blo 854356 2936189 := bstep (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) B1101071
theorem B1625609 : Blo 854356 1625609 := bstep (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) B1219207
theorem B1461959 : Blo 854356 1461959 := bstep (se 1 (by rfl) ⟨1096469, by rfl⟩ : syracuseStep 1461959 = 2192939) B2192939
theorem B4869881 : Blo 854356 4869881 := bstep (se 2 (by rfl) ⟨1826205, by rfl⟩ : syracuseStep 4869881 = 3652411) B3652411
theorem B1855495 : Blo 854356 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B3657743 : Blo 854356 3657743 := bstep (se 1 (by rfl) ⟨2743307, by rfl⟩ : syracuseStep 3657743 = 5486615) B5486615
theorem B2740243 : Blo 854356 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B1626475 : Blo 854356 1626475 := bstep (se 1 (by rfl) ⟨1219856, by rfl⟩ : syracuseStep 1626475 = 2439713) B2439713
theorem B1626551 : Blo 854356 1626551 := bstep (se 1 (by rfl) ⟨1219913, by rfl⟩ : syracuseStep 1626551 = 2439827) B2439827
theorem B4871087 : Blo 854356 4871087 := bstep (se 1 (by rfl) ⟨3653315, by rfl⟩ : syracuseStep 4871087 = 7306631) B7306631
theorem B2315195 : Blo 854356 2315195 := bstep (se 1 (by rfl) ⟨1736396, by rfl⟩ : syracuseStep 2315195 = 3472793) B3472793
theorem B1627067 : Blo 854356 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B2053127 : Blo 854356 2053127 := bstep (se 1 (by rfl) ⟨1539845, by rfl⟩ : syracuseStep 2053127 = 3079691) B3079691
theorem B6182041 : Blo 854356 6182041 := bstep (se 2 (by rfl) ⟨2318265, by rfl⟩ : syracuseStep 6182041 = 4636531) B4636531
theorem B4871339 : Blo 854356 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B1627553 : Blo 854356 1627553 := bstep (se 2 (by rfl) ⟨610332, by rfl⟩ : syracuseStep 1627553 = 1220665) B1220665
theorem B9754019 : Blo 854356 9754019 := bstep (se 1 (by rfl) ⟨7315514, by rfl⟩ : syracuseStep 9754019 = 14631029) B14631029
theorem B1627705 : Blo 854356 1627705 := bstep (se 2 (by rfl) ⟨610389, by rfl⟩ : syracuseStep 1627705 = 1220779) B1220779
theorem B1922759 : Blo 854356 1922759 := bstep (se 1 (by rfl) ⟨1442069, by rfl⟩ : syracuseStep 1922759 = 2884139) B2884139
theorem B2741975 : Blo 854356 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B11130583 : Blo 854356 11130583 := bstep (se 1 (by rfl) ⟨8347937, by rfl⟩ : syracuseStep 11130583 = 16695875) B16695875
theorem B6182615 : Blo 854356 6182615 := bstep (se 1 (by rfl) ⟨4636961, by rfl⟩ : syracuseStep 6182615 = 9273923) B9273923
theorem B1628009 : Blo 854356 1628009 := bstep (se 2 (by rfl) ⟨610503, by rfl⟩ : syracuseStep 1628009 = 1221007) B1221007
theorem B16897901 : Blo 854356 16897901 := bstep (se 3 (by rfl) ⟨3168356, by rfl⟩ : syracuseStep 16897901 = 6336713) B6336713
theorem B6510455 : Blo 854356 6510455 := bstep (se 1 (by rfl) ⟨4882841, by rfl⟩ : syracuseStep 6510455 = 9765683) B9765683
theorem B2742191 : Blo 854356 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B5200139 : Blo 854356 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B2742589 : Blo 854356 2742589 := bstep (se 3 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 2742589 = 1028471) B1028471
theorem B2742653 : Blo 854356 2742653 := bstep (se 3 (by rfl) ⟨514247, by rfl⟩ : syracuseStep 2742653 = 1028495) B1028495
theorem B1923623 : Blo 854356 1923623 := bstep (se 1 (by rfl) ⟨1442717, by rfl⟩ : syracuseStep 1923623 = 2885435) B2885435
theorem B1923947 : Blo 854356 1923947 := bstep (se 1 (by rfl) ⟨1442960, by rfl⟩ : syracuseStep 1923947 = 2885921) B2885921
theorem B1924001 : Blo 854356 1924001 := bstep (se 2 (by rfl) ⟨721500, by rfl⟩ : syracuseStep 1924001 = 1443001) B1443001
theorem B8805455 : Blo 854356 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B3464345 : Blo 854356 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B1924343 : Blo 854356 1924343 := bstep (se 1 (by rfl) ⟨1443257, by rfl⟩ : syracuseStep 1924343 = 2886515) B2886515
theorem B1924937 : Blo 854356 1924937 := bstep (se 2 (by rfl) ⟨721851, by rfl⟩ : syracuseStep 1924937 = 1443703) B1443703
theorem B4874255 : Blo 854356 4874255 := bstep (se 1 (by rfl) ⟨3655691, by rfl⟩ : syracuseStep 4874255 = 7311383) B7311383
theorem B7331917 : Blo 854356 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B2744435 : Blo 854356 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B15622307 : Blo 854356 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B1925729 : Blo 854356 1925729 := bstep (se 2 (by rfl) ⟨722148, by rfl⟩ : syracuseStep 1925729 = 1444297) B1444297
theorem B1368937 : Blo 854356 1368937 := bstep (se 2 (by rfl) ⟨513351, by rfl⟩ : syracuseStep 1368937 = 1026703) B1026703
theorem B6579089 : Blo 854356 6579089 := bstep (se 2 (by rfl) ⟨2467158, by rfl⟩ : syracuseStep 6579089 = 4934317) B4934317
theorem B1926071 : Blo 854356 1926071 := bstep (se 1 (by rfl) ⟨1444553, by rfl⟩ : syracuseStep 1926071 = 2889107) B2889107
theorem B5858423 : Blo 854356 5858423 := bstep (se 1 (by rfl) ⟨4393817, by rfl⟩ : syracuseStep 5858423 = 8787635) B8787635
theorem B6513857 : Blo 854356 6513857 := bstep (se 2 (by rfl) ⟨2442696, by rfl⟩ : syracuseStep 6513857 = 4885393) B4885393
theorem B1926665 : Blo 854356 1926665 := bstep (se 2 (by rfl) ⟨722499, by rfl⟩ : syracuseStep 1926665 = 1444999) B1444999
theorem B1927007 : Blo 854356 1927007 := bstep (se 1 (by rfl) ⟨1445255, by rfl⟩ : syracuseStep 1927007 = 2890511) B2890511
theorem B6186887 : Blo 854356 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B3467279 : Blo 854356 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B1927187 : Blo 854356 1927187 := bstep (se 1 (by rfl) ⟨1445390, by rfl⟩ : syracuseStep 1927187 = 2890781) B2890781
theorem B5499197 : Blo 854356 5499197 := bstep (se 3 (by rfl) ⟨1031099, by rfl⟩ : syracuseStep 5499197 = 2062199) B2062199
theorem B1927529 : Blo 854356 1927529 := bstep (se 2 (by rfl) ⟨722823, by rfl⟩ : syracuseStep 1927529 = 1445647) B1445647
theorem B4123169 : Blo 854356 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B1928123 : Blo 854356 1928123 := bstep (se 1 (by rfl) ⟨1446092, by rfl⟩ : syracuseStep 1928123 = 2892185) B2892185
theorem B1928249 : Blo 854356 1928249 := bstep (se 2 (by rfl) ⟨723093, by rfl⟩ : syracuseStep 1928249 = 1446187) B1446187
theorem B2747753 : Blo 854356 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B1928591 : Blo 854356 1928591 := bstep (se 1 (by rfl) ⟨1446443, by rfl⟩ : syracuseStep 1928591 = 2892887) B2892887
theorem B2059739 : Blo 854356 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B4877921 : Blo 854356 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B1928915 : Blo 854356 1928915 := bstep (se 1 (by rfl) ⟨1446686, by rfl⟩ : syracuseStep 1928915 = 2893373) B2893373
theorem B14839517 : Blo 854356 14839517 := bstep (se 3 (by rfl) ⟨2782409, by rfl⟩ : syracuseStep 14839517 = 5564819) B5564819
theorem B6516773 : Blo 854356 6516773 := bstep (se 4 (by rfl) ⟨610947, by rfl⟩ : syracuseStep 6516773 = 1221895) B1221895
theorem B6582349 : Blo 854356 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B7303283 : Blo 854356 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B1929851 : Blo 854356 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B1831673 : Blo 854356 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B1929977 : Blo 854356 1929977 := bstep (se 2 (by rfl) ⟨723741, by rfl⟩ : syracuseStep 1929977 = 1447483) B1447483
theorem B1930247 : Blo 854356 1930247 := bstep (se 1 (by rfl) ⟨1447685, by rfl⟩ : syracuseStep 1930247 = 2895371) B2895371
theorem B4879379 : Blo 854356 4879379 := bstep (se 1 (by rfl) ⟨3659534, by rfl⟩ : syracuseStep 4879379 = 7319069) B7319069
theorem B1733671 : Blo 854356 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B1930319 : Blo 854356 1930319 := bstep (se 1 (by rfl) ⟨1447739, by rfl⟩ : syracuseStep 1930319 = 2895479) B2895479
theorem B1733729 : Blo 854356 1733729 := bstep (se 2 (by rfl) ⟨650148, by rfl⟩ : syracuseStep 1733729 = 1300297) B1300297
theorem B4879835 : Blo 854356 4879835 := bstep (se 1 (by rfl) ⟨3659876, by rfl⟩ : syracuseStep 4879835 = 7319753) B7319753
theorem B1930715 : Blo 854356 1930715 := bstep (se 1 (by rfl) ⟨1448036, by rfl⟩ : syracuseStep 1930715 = 2896073) B2896073
theorem B2061787 : Blo 854356 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B2061863 : Blo 854356 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B16676533 : Blo 854356 16676533 := bstep (se 5 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 16676533 = 1563425) B1563425
theorem B4880087 : Blo 854356 4880087 := bstep (se 1 (by rfl) ⟨3660065, by rfl⟩ : syracuseStep 4880087 = 7320131) B7320131
theorem B6944545 : Blo 854356 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B8222573 : Blo 854356 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B1931183 : Blo 854356 1931183 := bstep (se 1 (by rfl) ⟨1448387, by rfl⟩ : syracuseStep 1931183 = 2896775) B2896775
theorem B13891945 : Blo 854356 13891945 := bstep (se 2 (by rfl) ⟨5209479, by rfl⟩ : syracuseStep 13891945 = 10418959) B10418959
theorem B1374607 : Blo 854356 1374607 := bstep (se 1 (by rfl) ⟨1030955, by rfl⟩ : syracuseStep 1374607 = 2061911) B2061911
theorem B916319 : Blo 854356 916319 := bstep (se 1 (by rfl) ⟨687239, by rfl⟩ : syracuseStep 916319 = 1374479) B1374479
theorem B3964781 : Blo 854356 3964781 := bstep (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) B1486793
theorem B4882295 : Blo 854356 4882295 := bstep (se 1 (by rfl) ⟨3661721, by rfl⟩ : syracuseStep 4882295 = 7323443) B7323443
theorem B3243959 : Blo 854356 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B4325723 : Blo 854356 4325723 := bstep (se 1 (by rfl) ⟨3244292, by rfl⟩ : syracuseStep 4325723 = 6488585) B6488585
theorem B17858981 : Blo 854356 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B1442299 : Blo 854356 1442299 := bstep (se 1 (by rfl) ⟨1081724, by rfl⟩ : syracuseStep 1442299 = 2163449) B2163449
theorem B1081927 : Blo 854356 1081927 := bstep (se 1 (by rfl) ⟨811445, by rfl⟩ : syracuseStep 1081927 = 1622891) B1622891
theorem B2163307 : Blo 854356 2163307 := bstep (se 1 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 2163307 = 3244961) B3244961
theorem B14811821 : Blo 854356 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B4391639 : Blo 854356 4391639 := bstep (se 1 (by rfl) ⟨3293729, by rfl⟩ : syracuseStep 4391639 = 6587459) B6587459
theorem B10978193 : Blo 854356 10978193 := bstep (se 2 (by rfl) ⟨4116822, by rfl⟩ : syracuseStep 10978193 = 8233645) B8233645
theorem B2163611 : Blo 854356 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B1442731 : Blo 854356 1442731 := bstep (se 1 (by rfl) ⟨1082048, by rfl⟩ : syracuseStep 1442731 = 2164097) B2164097
theorem B2884571 : Blo 854356 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B2884733 : Blo 854356 2884733 := bstep (se 3 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 2884733 = 1081775) B1081775
theorem B1443035 : Blo 854356 1443035 := bstep (se 1 (by rfl) ⟨1082276, by rfl⟩ : syracuseStep 1443035 = 2164553) B2164553
theorem B2884841 : Blo 854356 2884841 := bstep (se 2 (by rfl) ⟨1081815, by rfl⟩ : syracuseStep 2884841 = 2163631) B2163631
theorem B2163955 : Blo 854356 2163955 := bstep (se 1 (by rfl) ⟨1622966, by rfl⟩ : syracuseStep 2163955 = 3245933) B3245933
theorem B4326695 : Blo 854356 4326695 := bstep (se 1 (by rfl) ⟨3245021, by rfl⟩ : syracuseStep 4326695 = 6490043) B6490043
theorem B1082747 : Blo 854356 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B2885003 : Blo 854356 2885003 := bstep (se 1 (by rfl) ⟨2163752, by rfl⟩ : syracuseStep 2885003 = 4327505) B4327505
theorem B1443271 : Blo 854356 1443271 := bstep (se 1 (by rfl) ⟨1082453, by rfl⟩ : syracuseStep 1443271 = 2164907) B2164907
theorem B1443791 : Blo 854356 1443791 := bstep (se 1 (by rfl) ⟨1082843, by rfl⟩ : syracuseStep 1443791 = 2165687) B2165687
theorem B4884461 : Blo 854356 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B2164745 : Blo 854356 2164745 := bstep (se 2 (by rfl) ⟨811779, by rfl⟩ : syracuseStep 2164745 = 1623559) B1623559
theorem B854363 : Blo 854356 854363 := bstep (se 1 (by rfl) ⟨640772, by rfl⟩ : syracuseStep 854363 = 1281545) B1281545
theorem B854383 : Blo 854356 854383 := bstep (se 1 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 854383 = 1281575) B1281575
theorem B854439 : Blo 854356 854439 := bstep (se 1 (by rfl) ⟨640829, by rfl⟩ : syracuseStep 854439 = 1281659) B1281659
theorem B854523 : Blo 854356 854523 := bstep (se 1 (by rfl) ⟨640892, by rfl⟩ : syracuseStep 854523 = 1281785) B1281785
theorem B3246587 : Blo 854356 3246587 := bstep (se 1 (by rfl) ⟨2434940, by rfl⟩ : syracuseStep 3246587 = 4869881) B4869881
theorem B854591 : Blo 854356 854591 := bstep (se 1 (by rfl) ⟨640943, by rfl⟩ : syracuseStep 854591 = 1281887) B1281887
theorem B854599 : Blo 854356 854599 := bstep (se 1 (by rfl) ⟨640949, by rfl⟩ : syracuseStep 854599 = 1281899) B1281899
theorem B1444459 : Blo 854356 1444459 := bstep (se 1 (by rfl) ⟨1083344, by rfl⟩ : syracuseStep 1444459 = 2166689) B2166689
theorem B854751 : Blo 854356 854751 := bstep (se 1 (by rfl) ⟨641063, by rfl⟩ : syracuseStep 854751 = 1282127) B1282127
theorem B854831 : Blo 854356 854831 := bstep (se 1 (by rfl) ⟨641123, by rfl⟩ : syracuseStep 854831 = 1282247) B1282247
theorem B6491015 : Blo 854356 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B854939 : Blo 854356 854939 := bstep (se 1 (by rfl) ⟨641204, by rfl⟩ : syracuseStep 854939 = 1282409) B1282409
theorem B1444763 : Blo 854356 1444763 := bstep (se 1 (by rfl) ⟨1083572, by rfl⟩ : syracuseStep 1444763 = 2167145) B2167145
theorem B4623277 : Blo 854356 4623277 := bstep (se 3 (by rfl) ⟨866864, by rfl⟩ : syracuseStep 4623277 = 1733729) B1733729
theorem B854991 : Blo 854356 854991 := bstep (se 1 (by rfl) ⟨641243, by rfl⟩ : syracuseStep 854991 = 1282487) B1282487
theorem B1084367 : Blo 854356 1084367 := bstep (se 1 (by rfl) ⟨813275, by rfl⟩ : syracuseStep 1084367 = 1626551) B1626551
theorem B855015 : Blo 854356 855015 := bstep (se 1 (by rfl) ⟨641261, by rfl⟩ : syracuseStep 855015 = 1282523) B1282523
theorem B2165899 : Blo 854356 2165899 := bstep (se 1 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 2165899 = 3248849) B3248849
theorem B3247391 : Blo 854356 3247391 := bstep (se 1 (by rfl) ⟨2435543, by rfl⟩ : syracuseStep 3247391 = 4871087) B4871087
theorem B855327 : Blo 854356 855327 := bstep (se 1 (by rfl) ⟨641495, by rfl⟩ : syracuseStep 855327 = 1282991) B1282991
theorem B1543463 : Blo 854356 1543463 := bstep (se 1 (by rfl) ⟨1157597, by rfl⟩ : syracuseStep 1543463 = 2315195) B2315195
theorem B49483061 : Blo 854356 49483061 := bstep (se 5 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 49483061 = 4639037) B4639037
theorem B855387 : Blo 854356 855387 := bstep (se 1 (by rfl) ⟨641540, by rfl⟩ : syracuseStep 855387 = 1283081) B1283081
theorem B4328801 : Blo 854356 4328801 := bstep (se 2 (by rfl) ⟨1623300, by rfl⟩ : syracuseStep 4328801 = 3246601) B3246601
theorem B855407 : Blo 854356 855407 := bstep (se 1 (by rfl) ⟨641555, by rfl⟩ : syracuseStep 855407 = 1283111) B1283111
theorem B855463 : Blo 854356 855463 := bstep (se 1 (by rfl) ⟨641597, by rfl⟩ : syracuseStep 855463 = 1283195) B1283195
theorem B2166203 : Blo 854356 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B3247559 : Blo 854356 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B855547 : Blo 854356 855547 := bstep (se 1 (by rfl) ⟨641660, by rfl⟩ : syracuseStep 855547 = 1283321) B1283321
theorem B9244169 : Blo 854356 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B855615 : Blo 854356 855615 := bstep (se 1 (by rfl) ⟨641711, by rfl⟩ : syracuseStep 855615 = 1283423) B1283423
theorem B855623 : Blo 854356 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B855775 : Blo 854356 855775 := bstep (se 1 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 855775 = 1283663) B1283663
theorem B1281833 : Blo 854356 1281833 := bstep (se 2 (by rfl) ⟨480687, by rfl⟩ : syracuseStep 1281833 = 961375) B961375
theorem B1281839 : Blo 854356 1281839 := bstep (se 1 (by rfl) ⟨961379, by rfl⟩ : syracuseStep 1281839 = 1922759) B1922759
theorem B855855 : Blo 854356 855855 := bstep (se 1 (by rfl) ⟨641891, by rfl⟩ : syracuseStep 855855 = 1283783) B1283783
theorem B855963 : Blo 854356 855963 := bstep (se 1 (by rfl) ⟨641972, by rfl⟩ : syracuseStep 855963 = 1283945) B1283945
theorem B1085339 : Blo 854356 1085339 := bstep (se 1 (by rfl) ⟨814004, by rfl⟩ : syracuseStep 1085339 = 1628009) B1628009
theorem B856015 : Blo 854356 856015 := bstep (se 1 (by rfl) ⟨642011, by rfl⟩ : syracuseStep 856015 = 1284023) B1284023
theorem B856039 : Blo 854356 856039 := bstep (se 1 (by rfl) ⟨642029, by rfl⟩ : syracuseStep 856039 = 1284059) B1284059
theorem B3805193 : Blo 854356 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B1282313 : Blo 854356 1282313 := bstep (se 2 (by rfl) ⟨480867, by rfl⟩ : syracuseStep 1282313 = 961735) B961735
theorem B856351 : Blo 854356 856351 := bstep (se 1 (by rfl) ⟨642263, by rfl⟩ : syracuseStep 856351 = 1284527) B1284527
theorem B2888027 : Blo 854356 2888027 := bstep (se 1 (by rfl) ⟨2166020, by rfl⟩ : syracuseStep 2888027 = 4332041) B4332041
theorem B856411 : Blo 854356 856411 := bstep (se 1 (by rfl) ⟨642308, by rfl⟩ : syracuseStep 856411 = 1284617) B1284617
theorem B1282415 : Blo 854356 1282415 := bstep (se 1 (by rfl) ⟨961811, by rfl⟩ : syracuseStep 1282415 = 1923623) B1923623
theorem B856431 : Blo 854356 856431 := bstep (se 1 (by rfl) ⟨642323, by rfl⟩ : syracuseStep 856431 = 1284647) B1284647
theorem B856487 : Blo 854356 856487 := bstep (se 1 (by rfl) ⟨642365, by rfl⟩ : syracuseStep 856487 = 1284731) B1284731
theorem B856571 : Blo 854356 856571 := bstep (se 1 (by rfl) ⟨642428, by rfl⟩ : syracuseStep 856571 = 1284857) B1284857
theorem B16486973 : Blo 854356 16486973 := bstep (se 3 (by rfl) ⟨3091307, by rfl⟩ : syracuseStep 16486973 = 6182615) B6182615
theorem B856639 : Blo 854356 856639 := bstep (se 1 (by rfl) ⟨642479, by rfl⟩ : syracuseStep 856639 = 1284959) B1284959
theorem B1282631 : Blo 854356 1282631 := bstep (se 1 (by rfl) ⟨961973, by rfl⟩ : syracuseStep 1282631 = 1923947) B1923947
theorem B856647 : Blo 854356 856647 := bstep (se 1 (by rfl) ⟨642485, by rfl⟩ : syracuseStep 856647 = 1284971) B1284971
theorem B1282667 : Blo 854356 1282667 := bstep (se 1 (by rfl) ⟨962000, by rfl⟩ : syracuseStep 1282667 = 1924001) B1924001
theorem B2167519 : Blo 854356 2167519 := bstep (se 1 (by rfl) ⟨1625639, by rfl⟩ : syracuseStep 2167519 = 3251279) B3251279
theorem B856799 : Blo 854356 856799 := bstep (se 1 (by rfl) ⟨642599, by rfl⟩ : syracuseStep 856799 = 1285199) B1285199
theorem B5870303 : Blo 854356 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B856879 : Blo 854356 856879 := bstep (se 1 (by rfl) ⟨642659, by rfl⟩ : syracuseStep 856879 = 1285319) B1285319
theorem B1282895 : Blo 854356 1282895 := bstep (se 1 (by rfl) ⟨962171, by rfl⟩ : syracuseStep 1282895 = 1924343) B1924343
theorem B2167631 : Blo 854356 2167631 := bstep (se 1 (by rfl) ⟨1625723, by rfl⟩ : syracuseStep 2167631 = 3251447) B3251447
theorem B856987 : Blo 854356 856987 := bstep (se 1 (by rfl) ⟨642740, by rfl⟩ : syracuseStep 856987 = 1285481) B1285481
theorem B21926861 : Blo 854356 21926861 := bstep (se 3 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 21926861 = 8222573) B8222573
theorem B45061069 : Blo 854356 45061069 := bstep (se 3 (by rfl) ⟨8448950, by rfl⟩ : syracuseStep 45061069 = 16897901) B16897901
theorem B857039 : Blo 854356 857039 := bstep (se 1 (by rfl) ⟨642779, by rfl⟩ : syracuseStep 857039 = 1285559) B1285559
theorem B857063 : Blo 854356 857063 := bstep (se 1 (by rfl) ⟨642797, by rfl⟩ : syracuseStep 857063 = 1285595) B1285595
theorem B1283291 : Blo 854356 1283291 := bstep (se 1 (by rfl) ⟨962468, by rfl⟩ : syracuseStep 1283291 = 1924937) B1924937
theorem B4330745 : Blo 854356 4330745 := bstep (se 2 (by rfl) ⟨1624029, by rfl⟩ : syracuseStep 4330745 = 3248059) B3248059
theorem B857375 : Blo 854356 857375 := bstep (se 1 (by rfl) ⟨643031, by rfl⟩ : syracuseStep 857375 = 1286063) B1286063
theorem B2888999 : Blo 854356 2888999 := bstep (se 1 (by rfl) ⟨2166749, by rfl⟩ : syracuseStep 2888999 = 4333499) B4333499
theorem B857435 : Blo 854356 857435 := bstep (se 1 (by rfl) ⟨643076, by rfl⟩ : syracuseStep 857435 = 1286153) B1286153
theorem B3249503 : Blo 854356 3249503 := bstep (se 1 (by rfl) ⟨2437127, by rfl⟩ : syracuseStep 3249503 = 4874255) B4874255
theorem B3249517 : Blo 854356 3249517 := bstep (se 3 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 3249517 = 1218569) B1218569
theorem B857455 : Blo 854356 857455 := bstep (se 1 (by rfl) ⟨643091, by rfl⟩ : syracuseStep 857455 = 1286183) B1286183
theorem B1283465 : Blo 854356 1283465 := bstep (se 2 (by rfl) ⟨481299, by rfl⟩ : syracuseStep 1283465 = 962599) B962599
theorem B857511 : Blo 854356 857511 := bstep (se 1 (by rfl) ⟨643133, by rfl⟩ : syracuseStep 857511 = 1286267) B1286267
theorem B2168279 : Blo 854356 2168279 := bstep (se 1 (by rfl) ⟨1626209, by rfl⟩ : syracuseStep 2168279 = 3252419) B3252419
theorem B857595 : Blo 854356 857595 := bstep (se 1 (by rfl) ⟨643196, by rfl⟩ : syracuseStep 857595 = 1286393) B1286393
theorem B857663 : Blo 854356 857663 := bstep (se 1 (by rfl) ⟨643247, by rfl⟩ : syracuseStep 857663 = 1286495) B1286495
theorem B857671 : Blo 854356 857671 := bstep (se 1 (by rfl) ⟨643253, by rfl⟩ : syracuseStep 857671 = 1286507) B1286507
theorem B3249821 : Blo 854356 3249821 := bstep (se 3 (by rfl) ⟨609341, by rfl⟩ : syracuseStep 3249821 = 1218683) B1218683
theorem B857823 : Blo 854356 857823 := bstep (se 1 (by rfl) ⟨643367, by rfl⟩ : syracuseStep 857823 = 1286735) B1286735
theorem B1283819 : Blo 854356 1283819 := bstep (se 1 (by rfl) ⟨962864, by rfl⟩ : syracuseStep 1283819 = 1925729) B1925729
theorem B857903 : Blo 854356 857903 := bstep (se 1 (by rfl) ⟨643427, by rfl⟩ : syracuseStep 857903 = 1286855) B1286855
theorem B2168633 : Blo 854356 2168633 := bstep (se 2 (by rfl) ⟨813237, by rfl⟩ : syracuseStep 2168633 = 1626475) B1626475
theorem B858011 : Blo 854356 858011 := bstep (se 1 (by rfl) ⟨643508, by rfl⟩ : syracuseStep 858011 = 1287017) B1287017
theorem B1284047 : Blo 854356 1284047 := bstep (se 1 (by rfl) ⟨963035, by rfl⟩ : syracuseStep 1284047 = 1926071) B1926071
theorem B858063 : Blo 854356 858063 := bstep (se 1 (by rfl) ⟨643547, by rfl⟩ : syracuseStep 858063 = 1287095) B1287095
theorem B858087 : Blo 854356 858087 := bstep (se 1 (by rfl) ⟨643565, by rfl⟩ : syracuseStep 858087 = 1287131) B1287131
theorem B13867037 : Blo 854356 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B3905615 : Blo 854356 3905615 := bstep (se 1 (by rfl) ⟨2929211, by rfl⟩ : syracuseStep 3905615 = 5858423) B5858423
theorem B2889863 : Blo 854356 2889863 := bstep (se 1 (by rfl) ⟨2167397, by rfl⟩ : syracuseStep 2889863 = 4334795) B4334795
theorem B13867289 : Blo 854356 13867289 := bstep (se 2 (by rfl) ⟨5200233, by rfl⟩ : syracuseStep 13867289 = 10400467) B10400467
theorem B1284443 : Blo 854356 1284443 := bstep (se 1 (by rfl) ⟨963332, by rfl⟩ : syracuseStep 1284443 = 1926665) B1926665
theorem B9771515 : Blo 854356 9771515 := bstep (se 1 (by rfl) ⟨7328636, by rfl⟩ : syracuseStep 9771515 = 14657273) B14657273
theorem B1284671 : Blo 854356 1284671 := bstep (se 1 (by rfl) ⟨963503, by rfl⟩ : syracuseStep 1284671 = 1927007) B1927007
theorem B1284791 : Blo 854356 1284791 := bstep (se 1 (by rfl) ⟨963593, by rfl⟩ : syracuseStep 1284791 = 1927187) B1927187
theorem B1317599 : Blo 854356 1317599 := bstep (se 1 (by rfl) ⟨988199, by rfl⟩ : syracuseStep 1317599 = 1976399) B1976399
theorem B1285019 : Blo 854356 1285019 := bstep (se 1 (by rfl) ⟨963764, by rfl⟩ : syracuseStep 1285019 = 1927529) B1927529
theorem B1285415 : Blo 854356 1285415 := bstep (se 1 (by rfl) ⟨964061, by rfl⟩ : syracuseStep 1285415 = 1928123) B1928123
theorem B2891105 : Blo 854356 2891105 := bstep (se 2 (by rfl) ⟨1084164, by rfl⟩ : syracuseStep 2891105 = 2168329) B2168329
theorem B1285499 : Blo 854356 1285499 := bstep (se 1 (by rfl) ⟨964124, by rfl⟩ : syracuseStep 1285499 = 1928249) B1928249
theorem B2170273 : Blo 854356 2170273 := bstep (se 2 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 2170273 = 1627705) B1627705
theorem B1285625 : Blo 854356 1285625 := bstep (se 2 (by rfl) ⟨482109, by rfl⟩ : syracuseStep 1285625 = 964219) B964219
theorem B1285727 : Blo 854356 1285727 := bstep (se 1 (by rfl) ⟨964295, by rfl⟩ : syracuseStep 1285727 = 1928591) B1928591
theorem B3251947 : Blo 854356 3251947 := bstep (se 1 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 3251947 = 4877921) B4877921
theorem B1285943 : Blo 854356 1285943 := bstep (se 1 (by rfl) ⟨964457, by rfl⟩ : syracuseStep 1285943 = 1928915) B1928915
theorem B7806779 : Blo 854356 7806779 := bstep (se 1 (by rfl) ⟨5855084, by rfl⟩ : syracuseStep 7806779 = 11710169) B11710169
theorem B1286249 : Blo 854356 1286249 := bstep (se 2 (by rfl) ⟨482343, by rfl⟩ : syracuseStep 1286249 = 964687) B964687
theorem B3252433 : Blo 854356 3252433 := bstep (se 2 (by rfl) ⟨1219662, by rfl⟩ : syracuseStep 3252433 = 2439325) B2439325
theorem B1286567 : Blo 854356 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B18522593 : Blo 854356 18522593 := bstep (se 2 (by rfl) ⟨6945972, by rfl⟩ : syracuseStep 18522593 = 13891945) B13891945
theorem B1286651 : Blo 854356 1286651 := bstep (se 1 (by rfl) ⟨964988, by rfl⟩ : syracuseStep 1286651 = 1929977) B1929977
theorem B2171387 : Blo 854356 2171387 := bstep (se 1 (by rfl) ⟨1628540, by rfl⟩ : syracuseStep 2171387 = 3257081) B3257081
theorem B3252737 : Blo 854356 3252737 := bstep (se 2 (by rfl) ⟨1219776, by rfl⟩ : syracuseStep 3252737 = 2439553) B2439553
theorem B1286777 : Blo 854356 1286777 := bstep (se 2 (by rfl) ⟨482541, by rfl⟩ : syracuseStep 1286777 = 965083) B965083
theorem B1286831 : Blo 854356 1286831 := bstep (se 1 (by rfl) ⟨965123, by rfl⟩ : syracuseStep 1286831 = 1930247) B1930247
theorem B3252919 : Blo 854356 3252919 := bstep (se 1 (by rfl) ⟨2439689, by rfl⟩ : syracuseStep 3252919 = 4879379) B4879379
theorem B6955703 : Blo 854356 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B1286879 : Blo 854356 1286879 := bstep (se 1 (by rfl) ⟨965159, by rfl⟩ : syracuseStep 1286879 = 1930319) B1930319
theorem B88941509 : Blo 854356 88941509 := bstep (se 4 (by rfl) ⟨8338266, by rfl⟩ : syracuseStep 88941509 = 16676533) B16676533
theorem B3253193 : Blo 854356 3253193 := bstep (se 2 (by rfl) ⟨1219947, by rfl⟩ : syracuseStep 3253193 = 2439895) B2439895
theorem B3253223 : Blo 854356 3253223 := bstep (se 1 (by rfl) ⟨2439917, by rfl⟩ : syracuseStep 3253223 = 4879835) B4879835
theorem B1287143 : Blo 854356 1287143 := bstep (se 1 (by rfl) ⟨965357, by rfl⟩ : syracuseStep 1287143 = 1930715) B1930715
theorem B3253391 : Blo 854356 3253391 := bstep (se 1 (by rfl) ⟨2440043, by rfl⟩ : syracuseStep 3253391 = 4880087) B4880087
theorem B1287401 : Blo 854356 1287401 := bstep (se 2 (by rfl) ⟨482775, by rfl⟩ : syracuseStep 1287401 = 965551) B965551
theorem B2893049 : Blo 854356 2893049 := bstep (se 2 (by rfl) ⟨1084893, by rfl⟩ : syracuseStep 2893049 = 2169787) B2169787
theorem B1287455 : Blo 854356 1287455 := bstep (se 1 (by rfl) ⟨965591, by rfl⟩ : syracuseStep 1287455 = 1931183) B1931183
theorem B4334957 : Blo 854356 4334957 := bstep (se 3 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 4334957 = 1625609) B1625609
theorem B2172359 : Blo 854356 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B2893319 : Blo 854356 2893319 := bstep (se 1 (by rfl) ⟨2169989, by rfl⟩ : syracuseStep 2893319 = 4339979) B4339979
theorem B2894291 : Blo 854356 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B2435579 : Blo 854356 2435579 := bstep (se 1 (by rfl) ⟨1826684, by rfl⟩ : syracuseStep 2435579 = 3653369) B3653369
theorem B2894399 : Blo 854356 2894399 := bstep (se 1 (by rfl) ⟨2170799, by rfl⟩ : syracuseStep 2894399 = 4341599) B4341599
theorem B3254863 : Blo 854356 3254863 := bstep (se 1 (by rfl) ⟨2441147, by rfl⟩ : syracuseStep 3254863 = 4882295) B4882295
theorem B9775889 : Blo 854356 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B3255335 : Blo 854356 3255335 := bstep (se 1 (by rfl) ⟨2441501, by rfl⟩ : syracuseStep 3255335 = 4883003) B4883003
theorem B35105861 : Blo 854356 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B4107581 : Blo 854356 4107581 := bstep (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) B1540343
theorem B961915 : Blo 854356 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B3911161 : Blo 854356 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B31633019 : Blo 854356 31633019 := bstep (se 1 (by rfl) ⟨23724764, by rfl⟩ : syracuseStep 31633019 = 47449529) B47449529
theorem B4337387 : Blo 854356 4337387 := bstep (se 1 (by rfl) ⟨3253040, by rfl⟩ : syracuseStep 4337387 = 6506081) B6506081
theorem B3092231 : Blo 854356 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B2436911 : Blo 854356 2436911 := bstep (se 1 (by rfl) ⟨1827683, by rfl⟩ : syracuseStep 2436911 = 3655367) B3655367
theorem B962383 : Blo 854356 962383 := bstep (se 1 (by rfl) ⟨721787, by rfl⟩ : syracuseStep 962383 = 1443575) B1443575
theorem B5353675 : Blo 854356 5353675 := bstep (se 1 (by rfl) ⟨4015256, by rfl⟩ : syracuseStep 5353675 = 8030513) B8030513
theorem B4337873 : Blo 854356 4337873 := bstep (se 2 (by rfl) ⟨1626702, by rfl⟩ : syracuseStep 4337873 = 3253405) B3253405
theorem B962779 : Blo 854356 962779 := bstep (se 1 (by rfl) ⟨722084, by rfl⟩ : syracuseStep 962779 = 1444169) B1444169
theorem B2896235 : Blo 854356 2896235 := bstep (se 1 (by rfl) ⟨2172176, by rfl⟩ : syracuseStep 2896235 = 4344353) B4344353
theorem B3649967 : Blo 854356 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B963067 : Blo 854356 963067 := bstep (se 1 (by rfl) ⟨722300, by rfl⟩ : syracuseStep 963067 = 1444601) B1444601
theorem B2896505 : Blo 854356 2896505 := bstep (se 2 (by rfl) ⟨1086189, by rfl⟩ : syracuseStep 2896505 = 2172379) B2172379
theorem B963247 : Blo 854356 963247 := bstep (se 1 (by rfl) ⟨722435, by rfl⟩ : syracuseStep 963247 = 1444871) B1444871
theorem B1979063 : Blo 854356 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B4338359 : Blo 854356 4338359 := bstep (se 1 (by rfl) ⟨3253769, by rfl⟩ : syracuseStep 4338359 = 6507539) B6507539
theorem B963535 : Blo 854356 963535 := bstep (se 1 (by rfl) ⟨722651, by rfl⟩ : syracuseStep 963535 = 1445303) B1445303
theorem B5485715 : Blo 854356 5485715 := bstep (se 1 (by rfl) ⟨4114286, by rfl⟩ : syracuseStep 5485715 = 8228573) B8228573
theorem B4338845 : Blo 854356 4338845 := bstep (se 3 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 4338845 = 1627067) B1627067
theorem B963931 : Blo 854356 963931 := bstep (se 1 (by rfl) ⟨722948, by rfl⟩ : syracuseStep 963931 = 1445897) B1445897
theorem B2438495 : Blo 854356 2438495 := bstep (se 1 (by rfl) ⟨1828871, by rfl⟩ : syracuseStep 2438495 = 3657743) B3657743
theorem B964039 : Blo 854356 964039 := bstep (se 1 (by rfl) ⟨723029, by rfl⟩ : syracuseStep 964039 = 1446059) B1446059
theorem B23443091 : Blo 854356 23443091 := bstep (se 1 (by rfl) ⟨17582318, by rfl⟩ : syracuseStep 23443091 = 35164637) B35164637
theorem B964399 : Blo 854356 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B964507 : Blo 854356 964507 := bstep (se 1 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 964507 = 1446761) B1446761
theorem B7321529 : Blo 854356 7321529 := bstep (se 2 (by rfl) ⟨2745573, by rfl⟩ : syracuseStep 7321529 = 5491147) B5491147
theorem B4634759 : Blo 854356 4634759 := bstep (se 1 (by rfl) ⟨3476069, by rfl⟩ : syracuseStep 4634759 = 6952139) B6952139
theorem B6502679 : Blo 854356 6502679 := bstep (se 1 (by rfl) ⟨4877009, by rfl⟩ : syracuseStep 6502679 = 9754019) B9754019
theorem B964903 : Blo 854356 964903 := bstep (se 1 (by rfl) ⟨723677, by rfl⟩ : syracuseStep 964903 = 1447355) B1447355
theorem B964975 : Blo 854356 964975 := bstep (se 1 (by rfl) ⟨723731, by rfl⟩ : syracuseStep 964975 = 1447463) B1447463
theorem B4340141 : Blo 854356 4340141 := bstep (se 3 (by rfl) ⟨813776, by rfl⟩ : syracuseStep 4340141 = 1627553) B1627553
theorem B2341345 : Blo 854356 2341345 := bstep (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) B1756009
theorem B965191 : Blo 854356 965191 := bstep (se 1 (by rfl) ⟨723893, by rfl⟩ : syracuseStep 965191 = 1447787) B1447787
theorem B4340303 : Blo 854356 4340303 := bstep (se 1 (by rfl) ⟨3255227, by rfl⟩ : syracuseStep 4340303 = 6510455) B6510455
theorem B3259055 : Blo 854356 3259055 := bstep (se 1 (by rfl) ⟨2444291, by rfl⟩ : syracuseStep 3259055 = 4888583) B4888583
theorem B4701083 : Blo 854356 4701083 := bstep (se 1 (by rfl) ⟨3525812, by rfl⟩ : syracuseStep 4701083 = 7051625) B7051625
theorem B3390587 : Blo 854356 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B1981673 : Blo 854356 1981673 := bstep (se 2 (by rfl) ⟨743127, by rfl⟩ : syracuseStep 1981673 = 1486255) B1486255
theorem B2309563 : Blo 854356 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B5291513 : Blo 854356 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B2932307 : Blo 854356 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B2309789 : Blo 854356 2309789 := bstep (se 3 (by rfl) ⟨433085, by rfl⟩ : syracuseStep 2309789 = 866171) B866171
theorem B4341761 : Blo 854356 4341761 := bstep (se 2 (by rfl) ⟨1628160, by rfl⟩ : syracuseStep 4341761 = 3256321) B3256321
theorem B2473993 : Blo 854356 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B3653657 : Blo 854356 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B4866257 : Blo 854356 4866257 := bstep (se 2 (by rfl) ⟨1824846, by rfl⟩ : syracuseStep 4866257 = 3649693) B3649693
theorem B13877669 : Blo 854356 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B4342571 : Blo 854356 4342571 := bstep (se 1 (by rfl) ⟨3256928, by rfl⟩ : syracuseStep 4342571 = 6513857) B6513857
theorem B2311519 : Blo 854356 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B2311561 : Blo 854356 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B8242721 : Blo 854356 8242721 := bstep (se 2 (by rfl) ⟨3091020, by rfl⟩ : syracuseStep 8242721 = 6182041) B6182041
theorem B1623635 : Blo 854356 1623635 := bstep (se 1 (by rfl) ⟨1217726, by rfl⟩ : syracuseStep 1623635 = 2435453) B2435453
theorem B1623863 : Blo 854356 1623863 := bstep (se 1 (by rfl) ⟨1217897, by rfl⟩ : syracuseStep 1623863 = 2435795) B2435795
theorem B26364149 : Blo 854356 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B2443517 : Blo 854356 2443517 := bstep (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) B916319
theorem B9259393 : Blo 854356 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B1624531 : Blo 854356 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B4344515 : Blo 854356 4344515 := bstep (se 1 (by rfl) ⟨3258386, by rfl⟩ : syracuseStep 4344515 = 6516773) B6516773
theorem B4868855 : Blo 854356 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B3656785 : Blo 854356 3656785 := bstep (se 2 (by rfl) ⟨1371294, by rfl⟩ : syracuseStep 3656785 = 2742589) B2742589
theorem B1625321 : Blo 854356 1625321 := bstep (se 2 (by rfl) ⟨609495, by rfl⟩ : syracuseStep 1625321 = 1218991) B1218991
theorem B2346455 : Blo 854356 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B1625761 : Blo 854356 1625761 := bstep (se 2 (by rfl) ⟨609660, by rfl⟩ : syracuseStep 1625761 = 1219321) B1219321
theorem B2740807 : Blo 854356 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B1757803 : Blo 854356 1757803 := bstep (se 1 (by rfl) ⟨1318352, by rfl⟩ : syracuseStep 1757803 = 2636705) B2636705
theorem B10408601 : Blo 854356 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B10572749 : Blo 854356 10572749 := bstep (se 3 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 10572749 = 3964781) B3964781
theorem B3658715 : Blo 854356 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B1922399 : Blo 854356 1922399 := bstep (se 1 (by rfl) ⟨1441799, by rfl⟩ : syracuseStep 1922399 = 2883599) B2883599
theorem B2741627 : Blo 854356 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B18044459 : Blo 854356 18044459 := bstep (se 1 (by rfl) ⟨13533344, by rfl⟩ : syracuseStep 18044459 = 27066689) B27066689
theorem B9655853 : Blo 854356 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B1922795 : Blo 854356 1922795 := bstep (se 1 (by rfl) ⟨1442096, by rfl⟩ : syracuseStep 1922795 = 2884193) B2884193
theorem B1922921 : Blo 854356 1922921 := bstep (se 2 (by rfl) ⟨721095, by rfl⟩ : syracuseStep 1922921 = 1442191) B1442191
theorem B4872271 : Blo 854356 4872271 := bstep (se 1 (by rfl) ⟨3654203, by rfl⟩ : syracuseStep 4872271 = 7308407) B7308407
theorem B1825249 : Blo 854356 1825249 := bstep (se 2 (by rfl) ⟨684468, by rfl⟩ : syracuseStep 1825249 = 1368937) B1368937
theorem B4119113 : Blo 854356 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1923767 : Blo 854356 1923767 := bstep (se 1 (by rfl) ⟨1442825, by rfl⟩ : syracuseStep 1923767 = 2885651) B2885651
theorem B8248067 : Blo 854356 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B1923983 : Blo 854356 1923983 := bstep (se 1 (by rfl) ⟨1442987, by rfl⟩ : syracuseStep 1923983 = 2885975) B2885975
theorem B24108299 : Blo 854356 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B3661175 : Blo 854356 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B1924703 : Blo 854356 1924703 := bstep (se 1 (by rfl) ⟨1443527, by rfl⟩ : syracuseStep 1924703 = 2887055) B2887055
theorem B11296351 : Blo 854356 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B974639 : Blo 854356 974639 := bstep (se 1 (by rfl) ⟨730979, by rfl⟩ : syracuseStep 974639 = 1461959) B1461959
theorem B1924919 : Blo 854356 1924919 := bstep (se 1 (by rfl) ⟨1443689, by rfl⟩ : syracuseStep 1924919 = 2887379) B2887379
theorem B1925225 : Blo 854356 1925225 := bstep (se 2 (by rfl) ⟨721959, by rfl⟩ : syracuseStep 1925225 = 1443919) B1443919
theorem B2318699 : Blo 854356 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B1925711 : Blo 854356 1925711 := bstep (se 1 (by rfl) ⟨1444283, by rfl⟩ : syracuseStep 1925711 = 2888567) B2888567
theorem B1368751 : Blo 854356 1368751 := bstep (se 1 (by rfl) ⟨1026563, by rfl⟩ : syracuseStep 1368751 = 2053127) B2053127
theorem B1925855 : Blo 854356 1925855 := bstep (se 1 (by rfl) ⟨1444391, by rfl⟩ : syracuseStep 1925855 = 2888783) B2888783
theorem B2056951 : Blo 854356 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B1926107 : Blo 854356 1926107 := bstep (se 1 (by rfl) ⟨1444580, by rfl⟩ : syracuseStep 1926107 = 2889161) B2889161
theorem B2319347 : Blo 854356 2319347 := bstep (se 1 (by rfl) ⟨1739510, by rfl⟩ : syracuseStep 2319347 = 3479021) B3479021
theorem B1827983 : Blo 854356 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B1926287 : Blo 854356 1926287 := bstep (se 1 (by rfl) ⟨1444715, by rfl⟩ : syracuseStep 1926287 = 2889431) B2889431
theorem B1926377 : Blo 854356 1926377 := bstep (se 2 (by rfl) ⟨722391, by rfl⟩ : syracuseStep 1926377 = 1444783) B1444783
theorem B1828127 : Blo 854356 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B1926431 : Blo 854356 1926431 := bstep (se 1 (by rfl) ⟨1444823, by rfl⟩ : syracuseStep 1926431 = 2889647) B2889647
theorem B1828435 : Blo 854356 1828435 := bstep (se 1 (by rfl) ⟨1371326, by rfl⟩ : syracuseStep 1828435 = 2742653) B2742653
theorem B1926953 : Blo 854356 1926953 := bstep (se 2 (by rfl) ⟨722607, by rfl⟩ : syracuseStep 1926953 = 1445215) B1445215
theorem B1829623 : Blo 854356 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B10414871 : Blo 854356 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B1928015 : Blo 854356 1928015 := bstep (se 1 (by rfl) ⟨1446011, by rfl⟩ : syracuseStep 1928015 = 2892023) B2892023
theorem B1928231 : Blo 854356 1928231 := bstep (se 1 (by rfl) ⟨1446173, by rfl⟩ : syracuseStep 1928231 = 2892347) B2892347
theorem B1928411 : Blo 854356 1928411 := bstep (se 1 (by rfl) ⟨1446308, by rfl⟩ : syracuseStep 1928411 = 2892617) B2892617
theorem B4386059 : Blo 854356 4386059 := bstep (se 1 (by rfl) ⟨3289544, by rfl⟩ : syracuseStep 4386059 = 6579089) B6579089
theorem B1928609 : Blo 854356 1928609 := bstep (se 2 (by rfl) ⟨723228, by rfl⟩ : syracuseStep 1928609 = 1446457) B1446457
theorem B3173971 : Blo 854356 3173971 := bstep (se 1 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 3173971 = 4760957) B4760957
theorem B4124591 : Blo 854356 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B1929167 : Blo 854356 1929167 := bstep (se 1 (by rfl) ⟨1446875, by rfl⟩ : syracuseStep 1929167 = 2893751) B2893751
theorem B3666131 : Blo 854356 3666131 := bstep (se 1 (by rfl) ⟨2749598, by rfl⟩ : syracuseStep 3666131 = 5499197) B5499197
theorem B1929545 : Blo 854356 1929545 := bstep (se 2 (by rfl) ⟨723579, by rfl⟩ : syracuseStep 1929545 = 1447159) B1447159
theorem B1929563 : Blo 854356 1929563 := bstep (se 1 (by rfl) ⟨1447172, by rfl⟩ : syracuseStep 1929563 = 2894345) B2894345
theorem B2748779 : Blo 854356 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B2749049 : Blo 854356 2749049 := bstep (se 2 (by rfl) ⟨1030893, by rfl⟩ : syracuseStep 2749049 = 2061787) B2061787
theorem B1831835 : Blo 854356 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B1930139 : Blo 854356 1930139 := bstep (se 1 (by rfl) ⟨1447604, by rfl⟩ : syracuseStep 1930139 = 2895209) B2895209
theorem B14840777 : Blo 854356 14840777 := bstep (se 2 (by rfl) ⟨5565291, by rfl⟩ : syracuseStep 14840777 = 11130583) B11130583
theorem B1373159 : Blo 854356 1373159 := bstep (se 1 (by rfl) ⟨1029869, by rfl⟩ : syracuseStep 1373159 = 2059739) B2059739
theorem B7402585 : Blo 854356 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B1930337 : Blo 854356 1930337 := bstep (se 2 (by rfl) ⟨723876, by rfl⟩ : syracuseStep 1930337 = 1447753) B1447753
theorem B9893011 : Blo 854356 9893011 := bstep (se 1 (by rfl) ⟨7419758, by rfl⟩ : syracuseStep 9893011 = 14839517) B14839517
theorem B1930535 : Blo 854356 1930535 := bstep (se 1 (by rfl) ⟨1447901, by rfl⟩ : syracuseStep 1930535 = 2895803) B2895803
theorem B1930913 : Blo 854356 1930913 := bstep (se 2 (by rfl) ⟨724092, by rfl⟩ : syracuseStep 1930913 = 1448185) B1448185
theorem B1832809 : Blo 854356 1832809 := bstep (se 2 (by rfl) ⟨687303, by rfl⟩ : syracuseStep 1832809 = 1374607) B1374607
theorem B1931273 : Blo 854356 1931273 := bstep (se 2 (by rfl) ⟨724227, by rfl⟩ : syracuseStep 1931273 = 1448455) B1448455
theorem B4880519 : Blo 854356 4880519 := bstep (se 1 (by rfl) ⟨3660389, by rfl⟩ : syracuseStep 4880519 = 7320779) B7320779
theorem B3897629 : Blo 854356 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B7829837 : Blo 854356 7829837 := bstep (se 3 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 7829837 = 2936189) B2936189
theorem B1374575 : Blo 854356 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B3701135 : Blo 854356 3701135 := bstep (se 1 (by rfl) ⟨2775851, by rfl⟩ : syracuseStep 3701135 = 5551703) B5551703
theorem B9271847 : Blo 854356 9271847 := bstep (se 1 (by rfl) ⟨6953885, by rfl⟩ : syracuseStep 9271847 = 13907771) B13907771
theorem B3963455 : Blo 854356 3963455 := bstep (se 1 (by rfl) ⟨2972591, by rfl⟩ : syracuseStep 3963455 = 5945183) B5945183
theorem B14613533 : Blo 854356 14613533 := bstep (se 3 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 14613533 = 5480075) B5480075
theorem B2162639 : Blo 854356 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B3244171 : Blo 854356 3244171 := bstep (se 1 (by rfl) ⟨2433128, by rfl⟩ : syracuseStep 3244171 = 4866257) B4866257
theorem B2883815 : Blo 854356 2883815 := bstep (se 1 (by rfl) ⟨2162861, by rfl⟩ : syracuseStep 2883815 = 4325723) B4325723
theorem B1442407 : Blo 854356 1442407 := bstep (se 1 (by rfl) ⟨1081805, by rfl⟩ : syracuseStep 1442407 = 2163611) B2163611
theorem B1442569 : Blo 854356 1442569 := bstep (se 2 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 1442569 = 1081927) B1081927
theorem B2884409 : Blo 854356 2884409 := bstep (se 2 (by rfl) ⟨1081653, by rfl⟩ : syracuseStep 2884409 = 2163307) B2163307
theorem B2884463 : Blo 854356 2884463 := bstep (se 1 (by rfl) ⟨2163347, by rfl⟩ : syracuseStep 2884463 = 4326695) B4326695
theorem B1082423 : Blo 854356 1082423 := bstep (se 1 (by rfl) ⟨811817, by rfl⟩ : syracuseStep 1082423 = 1623635) B1623635
theorem B1082575 : Blo 854356 1082575 := bstep (se 1 (by rfl) ⟨811931, by rfl⟩ : syracuseStep 1082575 = 1623863) B1623863
theorem B1443163 : Blo 854356 1443163 := bstep (se 1 (by rfl) ⟨1082372, by rfl⟩ : syracuseStep 1443163 = 2164745) B2164745
theorem B2885273 : Blo 854356 2885273 := bstep (se 2 (by rfl) ⟨1081977, by rfl⟩ : syracuseStep 2885273 = 2163955) B2163955
theorem B2164391 : Blo 854356 2164391 := bstep (se 1 (by rfl) ⟨1623293, by rfl⟩ : syracuseStep 2164391 = 3246587) B3246587
theorem B3082025 : Blo 854356 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B3245903 : Blo 854356 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B4327343 : Blo 854356 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B1083547 : Blo 854356 1083547 := bstep (se 1 (by rfl) ⟨812660, by rfl⟩ : syracuseStep 1083547 = 1625321) B1625321
theorem B2164927 : Blo 854356 2164927 := bstep (se 1 (by rfl) ⟨1623695, by rfl⟩ : syracuseStep 2164927 = 3247391) B3247391
theorem B2885867 : Blo 854356 2885867 := bstep (se 1 (by rfl) ⟨2164400, by rfl⟩ : syracuseStep 2885867 = 4328801) B4328801
theorem B1444135 : Blo 854356 1444135 := bstep (se 1 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 1444135 = 2166203) B2166203
theorem B2165039 : Blo 854356 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B6162779 : Blo 854356 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B4884893 : Blo 854356 4884893 := bstep (se 3 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 4884893 = 1831835) B1831835
theorem B854555 : Blo 854356 854555 := bstep (se 1 (by rfl) ⟨640916, by rfl⟩ : syracuseStep 854555 = 1281833) B1281833
theorem B854559 : Blo 854356 854559 := bstep (se 1 (by rfl) ⟨640919, by rfl⟩ : syracuseStep 854559 = 1281839) B1281839
theorem B854875 : Blo 854356 854875 := bstep (se 1 (by rfl) ⟨641156, by rfl⟩ : syracuseStep 854875 = 1282313) B1282313
theorem B854943 : Blo 854356 854943 := bstep (se 1 (by rfl) ⟨641207, by rfl⟩ : syracuseStep 854943 = 1282415) B1282415
theorem B855087 : Blo 854356 855087 := bstep (se 1 (by rfl) ⟨641315, by rfl⟩ : syracuseStep 855087 = 1282631) B1282631
theorem B855111 : Blo 854356 855111 := bstep (se 1 (by rfl) ⟨641333, by rfl⟩ : syracuseStep 855111 = 1282667) B1282667
theorem B855263 : Blo 854356 855263 := bstep (se 1 (by rfl) ⟨641447, by rfl⟩ : syracuseStep 855263 = 1282895) B1282895
theorem B1445087 : Blo 854356 1445087 := bstep (se 1 (by rfl) ⟨1083815, by rfl⟩ : syracuseStep 1445087 = 2167631) B2167631
theorem B2166041 : Blo 854356 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B14617907 : Blo 854356 14617907 := bstep (se 1 (by rfl) ⟨10963430, by rfl⟩ : syracuseStep 14617907 = 21926861) B21926861
theorem B7048499 : Blo 854356 7048499 := bstep (se 1 (by rfl) ⟨5286374, by rfl⟩ : syracuseStep 7048499 = 10572749) B10572749
theorem B855527 : Blo 854356 855527 := bstep (se 1 (by rfl) ⟨641645, by rfl⟩ : syracuseStep 855527 = 1283291) B1283291
theorem B2887163 : Blo 854356 2887163 := bstep (se 1 (by rfl) ⟨2165372, by rfl⟩ : syracuseStep 2887163 = 4330745) B4330745
theorem B1281599 : Blo 854356 1281599 := bstep (se 1 (by rfl) ⟨961199, by rfl⟩ : syracuseStep 1281599 = 1922399) B1922399
theorem B2166335 : Blo 854356 2166335 := bstep (se 1 (by rfl) ⟨1624751, by rfl⟩ : syracuseStep 2166335 = 3249503) B3249503
theorem B855643 : Blo 854356 855643 := bstep (se 1 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 855643 = 1283465) B1283465
theorem B1445519 : Blo 854356 1445519 := bstep (se 1 (by rfl) ⟨1084139, by rfl⟩ : syracuseStep 1445519 = 2168279) B2168279
theorem B2887325 : Blo 854356 2887325 := bstep (se 3 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 2887325 = 1082747) B1082747
theorem B7311005 : Blo 854356 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B12029639 : Blo 854356 12029639 := bstep (se 1 (by rfl) ⟨9022229, by rfl⟩ : syracuseStep 12029639 = 18044459) B18044459
theorem B2166547 : Blo 854356 2166547 := bstep (se 1 (by rfl) ⟨1624910, by rfl⟩ : syracuseStep 2166547 = 3249821) B3249821
theorem B1281863 : Blo 854356 1281863 := bstep (se 1 (by rfl) ⟨961397, by rfl⟩ : syracuseStep 1281863 = 1922795) B1922795
theorem B855879 : Blo 854356 855879 := bstep (se 1 (by rfl) ⟨641909, by rfl⟩ : syracuseStep 855879 = 1283819) B1283819
theorem B1445755 : Blo 854356 1445755 := bstep (se 1 (by rfl) ⟨1084316, by rfl⟩ : syracuseStep 1445755 = 2168633) B2168633
theorem B6164369 : Blo 854356 6164369 := bstep (se 2 (by rfl) ⟨2311638, by rfl⟩ : syracuseStep 6164369 = 4623277) B4623277
theorem B1281947 : Blo 854356 1281947 := bstep (se 1 (by rfl) ⟨961460, by rfl⟩ : syracuseStep 1281947 = 1922921) B1922921
theorem B856031 : Blo 854356 856031 := bstep (se 1 (by rfl) ⟨642023, by rfl⟩ : syracuseStep 856031 = 1284047) B1284047
theorem B9244691 : Blo 854356 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B2887865 : Blo 854356 2887865 := bstep (se 2 (by rfl) ⟨1082949, by rfl⟩ : syracuseStep 2887865 = 2165899) B2165899
theorem B9244859 : Blo 854356 9244859 := bstep (se 1 (by rfl) ⟨6933644, by rfl⟩ : syracuseStep 9244859 = 13867289) B13867289
theorem B856295 : Blo 854356 856295 := bstep (se 1 (by rfl) ⟨642221, by rfl⟩ : syracuseStep 856295 = 1284443) B1284443
theorem B856447 : Blo 854356 856447 := bstep (se 1 (by rfl) ⟨642335, by rfl⟩ : syracuseStep 856447 = 1284671) B1284671
theorem B1282511 : Blo 854356 1282511 := bstep (se 1 (by rfl) ⟨961883, by rfl⟩ : syracuseStep 1282511 = 1923767) B1923767
theorem B856527 : Blo 854356 856527 := bstep (se 1 (by rfl) ⟨642395, by rfl⟩ : syracuseStep 856527 = 1284791) B1284791
theorem B1282553 : Blo 854356 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B1282655 : Blo 854356 1282655 := bstep (se 1 (by rfl) ⟨961991, by rfl⟩ : syracuseStep 1282655 = 1923983) B1923983
theorem B856679 : Blo 854356 856679 := bstep (se 1 (by rfl) ⟨642509, by rfl⟩ : syracuseStep 856679 = 1285019) B1285019
theorem B5214881 : Blo 854356 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B4231961 : Blo 854356 4231961 := bstep (se 2 (by rfl) ⟨1586985, by rfl⟩ : syracuseStep 4231961 = 3173971) B3173971
theorem B856943 : Blo 854356 856943 := bstep (se 1 (by rfl) ⟨642707, by rfl⟩ : syracuseStep 856943 = 1285415) B1285415
theorem B2167681 : Blo 854356 2167681 := bstep (se 2 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 2167681 = 1625761) B1625761
theorem B856999 : Blo 854356 856999 := bstep (se 1 (by rfl) ⟨642749, by rfl⟩ : syracuseStep 856999 = 1285499) B1285499
theorem B857083 : Blo 854356 857083 := bstep (se 1 (by rfl) ⟨642812, by rfl⟩ : syracuseStep 857083 = 1285625) B1285625
theorem B1283135 : Blo 854356 1283135 := bstep (se 1 (by rfl) ⟨962351, by rfl⟩ : syracuseStep 1283135 = 1924703) B1924703
theorem B857151 : Blo 854356 857151 := bstep (se 1 (by rfl) ⟨642863, by rfl⟩ : syracuseStep 857151 = 1285727) B1285727
theorem B1283177 : Blo 854356 1283177 := bstep (se 2 (by rfl) ⟨481191, by rfl⟩ : syracuseStep 1283177 = 962383) B962383
theorem B1283279 : Blo 854356 1283279 := bstep (se 1 (by rfl) ⟨962459, by rfl⟩ : syracuseStep 1283279 = 1924919) B1924919
theorem B857295 : Blo 854356 857295 := bstep (se 1 (by rfl) ⟨642971, by rfl⟩ : syracuseStep 857295 = 1285943) B1285943
theorem B1283483 : Blo 854356 1283483 := bstep (se 1 (by rfl) ⟨962612, by rfl⟩ : syracuseStep 1283483 = 1925225) B1925225
theorem B857499 : Blo 854356 857499 := bstep (se 1 (by rfl) ⟨643124, by rfl⟩ : syracuseStep 857499 = 1286249) B1286249
theorem B1545799 : Blo 854356 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B857711 : Blo 854356 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B1283705 : Blo 854356 1283705 := bstep (se 2 (by rfl) ⟨481389, by rfl⟩ : syracuseStep 1283705 = 962779) B962779
theorem B857767 : Blo 854356 857767 := bstep (se 1 (by rfl) ⟨643325, by rfl⟩ : syracuseStep 857767 = 1286651) B1286651
theorem B1447591 : Blo 854356 1447591 := bstep (se 1 (by rfl) ⟨1085693, by rfl⟩ : syracuseStep 1447591 = 2171387) B2171387
theorem B2168491 : Blo 854356 2168491 := bstep (se 1 (by rfl) ⟨1626368, by rfl⟩ : syracuseStep 2168491 = 3252737) B3252737
theorem B1283807 : Blo 854356 1283807 := bstep (se 1 (by rfl) ⟨962855, by rfl⟩ : syracuseStep 1283807 = 1925711) B1925711
theorem B857851 : Blo 854356 857851 := bstep (se 1 (by rfl) ⟨643388, by rfl⟩ : syracuseStep 857851 = 1286777) B1286777
theorem B857887 : Blo 854356 857887 := bstep (se 1 (by rfl) ⟨643415, by rfl⟩ : syracuseStep 857887 = 1286831) B1286831
theorem B1283903 : Blo 854356 1283903 := bstep (se 1 (by rfl) ⟨962927, by rfl⟩ : syracuseStep 1283903 = 1925855) B1925855
theorem B857919 : Blo 854356 857919 := bstep (se 1 (by rfl) ⟨643439, by rfl⟩ : syracuseStep 857919 = 1286879) B1286879
theorem B2168795 : Blo 854356 2168795 := bstep (se 1 (by rfl) ⟨1626596, by rfl⟩ : syracuseStep 2168795 = 3253193) B3253193
theorem B1284071 : Blo 854356 1284071 := bstep (se 1 (by rfl) ⟨963053, by rfl⟩ : syracuseStep 1284071 = 1926107) B1926107
theorem B2168815 : Blo 854356 2168815 := bstep (se 1 (by rfl) ⟨1626611, by rfl⟩ : syracuseStep 2168815 = 3253223) B3253223
theorem B858095 : Blo 854356 858095 := bstep (se 1 (by rfl) ⟨643571, by rfl⟩ : syracuseStep 858095 = 1287143) B1287143
theorem B1546231 : Blo 854356 1546231 := bstep (se 1 (by rfl) ⟨1159673, by rfl⟩ : syracuseStep 1546231 = 2319347) B2319347
theorem B1284089 : Blo 854356 1284089 := bstep (se 2 (by rfl) ⟨481533, by rfl⟩ : syracuseStep 1284089 = 963067) B963067
theorem B1218655 : Blo 854356 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B1284191 : Blo 854356 1284191 := bstep (se 1 (by rfl) ⟨963143, by rfl⟩ : syracuseStep 1284191 = 1926287) B1926287
theorem B2168927 : Blo 854356 2168927 := bstep (se 1 (by rfl) ⟨1626695, by rfl⟩ : syracuseStep 2168927 = 3253391) B3253391
theorem B1284251 : Blo 854356 1284251 := bstep (se 1 (by rfl) ⟨963188, by rfl⟩ : syracuseStep 1284251 = 1926377) B1926377
theorem B858267 : Blo 854356 858267 := bstep (se 1 (by rfl) ⟨643700, by rfl⟩ : syracuseStep 858267 = 1287401) B1287401
theorem B1284287 : Blo 854356 1284287 := bstep (se 1 (by rfl) ⟨963215, by rfl⟩ : syracuseStep 1284287 = 1926431) B1926431
theorem B858303 : Blo 854356 858303 := bstep (se 1 (by rfl) ⟨643727, by rfl⟩ : syracuseStep 858303 = 1287455) B1287455
theorem B1284329 : Blo 854356 1284329 := bstep (se 2 (by rfl) ⟨481623, by rfl⟩ : syracuseStep 1284329 = 963247) B963247
theorem B2889971 : Blo 854356 2889971 := bstep (se 1 (by rfl) ⟨2167478, by rfl⟩ : syracuseStep 2889971 = 4334957) B4334957
theorem B2890025 : Blo 854356 2890025 := bstep (se 2 (by rfl) ⟨1083759, by rfl⟩ : syracuseStep 2890025 = 2167519) B2167519
theorem B1448239 : Blo 854356 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B1284635 : Blo 854356 1284635 := bstep (se 1 (by rfl) ⟨963476, by rfl⟩ : syracuseStep 1284635 = 1926953) B1926953
theorem B1284713 : Blo 854356 1284713 := bstep (se 2 (by rfl) ⟨481767, by rfl⟩ : syracuseStep 1284713 = 963535) B963535
theorem B9870113 : Blo 854356 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B1285241 : Blo 854356 1285241 := bstep (se 2 (by rfl) ⟨481965, by rfl⟩ : syracuseStep 1285241 = 963931) B963931
theorem B4332689 : Blo 854356 4332689 := bstep (se 2 (by rfl) ⟨1624758, by rfl⟩ : syracuseStep 4332689 = 3249517) B3249517
theorem B1285343 : Blo 854356 1285343 := bstep (se 1 (by rfl) ⟨964007, by rfl⟩ : syracuseStep 1285343 = 1928015) B1928015
theorem B1285385 : Blo 854356 1285385 := bstep (se 2 (by rfl) ⟨482019, by rfl⟩ : syracuseStep 1285385 = 964039) B964039
theorem B1285487 : Blo 854356 1285487 := bstep (se 1 (by rfl) ⟨964115, by rfl⟩ : syracuseStep 1285487 = 1928231) B1928231
theorem B2170223 : Blo 854356 2170223 := bstep (se 1 (by rfl) ⟨1627667, by rfl⟩ : syracuseStep 2170223 = 3255335) B3255335
theorem B23403907 : Blo 854356 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B12328325 : Blo 854356 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B1285607 : Blo 854356 1285607 := bstep (se 1 (by rfl) ⟨964205, by rfl⟩ : syracuseStep 1285607 = 1928411) B1928411
theorem B2924039 : Blo 854356 2924039 := bstep (se 1 (by rfl) ⟨2193029, by rfl⟩ : syracuseStep 2924039 = 4386059) B4386059
theorem B1285739 : Blo 854356 1285739 := bstep (se 1 (by rfl) ⟨964304, by rfl⟩ : syracuseStep 1285739 = 1928609) B1928609
theorem B1285865 : Blo 854356 1285865 := bstep (se 2 (by rfl) ⟨482199, by rfl⟩ : syracuseStep 1285865 = 964399) B964399
theorem B2891591 : Blo 854356 2891591 := bstep (se 1 (by rfl) ⟨2168693, by rfl⟩ : syracuseStep 2891591 = 4337387) B4337387
theorem B1286009 : Blo 854356 1286009 := bstep (se 2 (by rfl) ⟨482253, by rfl⟩ : syracuseStep 1286009 = 964507) B964507
theorem B2891645 : Blo 854356 2891645 := bstep (se 3 (by rfl) ⟨542183, by rfl⟩ : syracuseStep 2891645 = 1084367) B1084367
theorem B1286111 : Blo 854356 1286111 := bstep (se 1 (by rfl) ⟨964583, by rfl⟩ : syracuseStep 1286111 = 1929167) B1929167
theorem B6496361 : Blo 854356 6496361 := bstep (se 2 (by rfl) ⟨2436135, by rfl⟩ : syracuseStep 6496361 = 4872271) B4872271
theorem B2891915 : Blo 854356 2891915 := bstep (se 1 (by rfl) ⟨2168936, by rfl⟩ : syracuseStep 2891915 = 4337873) B4337873
theorem B1286363 : Blo 854356 1286363 := bstep (se 1 (by rfl) ⟨964772, by rfl⟩ : syracuseStep 1286363 = 1929545) B1929545
theorem B1286375 : Blo 854356 1286375 := bstep (se 1 (by rfl) ⟨964781, by rfl⟩ : syracuseStep 1286375 = 1929563) B1929563
theorem B2433311 : Blo 854356 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B1286537 : Blo 854356 1286537 := bstep (se 2 (by rfl) ⟨482451, by rfl⟩ : syracuseStep 1286537 = 964903) B964903
theorem B1319375 : Blo 854356 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B2892239 : Blo 854356 2892239 := bstep (se 1 (by rfl) ⟨2169179, by rfl⟩ : syracuseStep 2892239 = 4338359) B4338359
theorem B1286633 : Blo 854356 1286633 := bstep (se 2 (by rfl) ⟨482487, by rfl⟩ : syracuseStep 1286633 = 964975) B964975
theorem B1286759 : Blo 854356 1286759 := bstep (se 1 (by rfl) ⟨965069, by rfl⟩ : syracuseStep 1286759 = 1930139) B1930139
theorem B3121793 : Blo 854356 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B2433665 : Blo 854356 2433665 := bstep (se 2 (by rfl) ⟨912624, by rfl⟩ : syracuseStep 2433665 = 1825249) B1825249
theorem B1286891 : Blo 854356 1286891 := bstep (se 1 (by rfl) ⟨965168, by rfl⟩ : syracuseStep 1286891 = 1930337) B1930337
theorem B1286921 : Blo 854356 1286921 := bstep (se 2 (by rfl) ⟨482595, by rfl⟩ : syracuseStep 1286921 = 965191) B965191
theorem B2892563 : Blo 854356 2892563 := bstep (se 1 (by rfl) ⟨2169422, by rfl⟩ : syracuseStep 2892563 = 4338845) B4338845
theorem B1287023 : Blo 854356 1287023 := bstep (se 1 (by rfl) ⟨965267, by rfl⟩ : syracuseStep 1287023 = 1930535) B1930535
theorem B1287275 : Blo 854356 1287275 := bstep (se 1 (by rfl) ⟨965456, by rfl⟩ : syracuseStep 1287275 = 1930913) B1930913
theorem B1287515 : Blo 854356 1287515 := bstep (se 1 (by rfl) ⟨965636, by rfl⟩ : syracuseStep 1287515 = 1931273) B1931273
theorem B3253679 : Blo 854356 3253679 := bstep (se 1 (by rfl) ⟨2440259, by rfl⟩ : syracuseStep 3253679 = 4880519) B4880519
theorem B3089839 : Blo 854356 3089839 := bstep (se 1 (by rfl) ⟨2317379, by rfl⟩ : syracuseStep 3089839 = 4634759) B4634759
theorem B4335119 : Blo 854356 4335119 := bstep (se 1 (by rfl) ⟨3251339, by rfl⟩ : syracuseStep 4335119 = 6502679) B6502679
theorem B2598419 : Blo 854356 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B5219891 : Blo 854356 5219891 := bstep (se 1 (by rfl) ⟨3914918, by rfl⟩ : syracuseStep 5219891 = 7829837) B7829837
theorem B2467423 : Blo 854356 2467423 := bstep (se 1 (by rfl) ⟨1850567, by rfl⟩ : syracuseStep 2467423 = 3701135) B3701135
theorem B2893427 : Blo 854356 2893427 := bstep (se 1 (by rfl) ⟨2170070, by rfl⟩ : syracuseStep 2893427 = 4340141) B4340141
theorem B2893535 : Blo 854356 2893535 := bstep (se 1 (by rfl) ⟨2170151, by rfl⟩ : syracuseStep 2893535 = 4340303) B4340303
theorem B2172703 : Blo 854356 2172703 := bstep (se 1 (by rfl) ⟨1629527, by rfl⟩ : syracuseStep 2172703 = 3259055) B3259055
theorem B2893697 : Blo 854356 2893697 := bstep (se 2 (by rfl) ⟨1085136, by rfl⟩ : syracuseStep 2893697 = 2170273) B2170273
theorem B9742355 : Blo 854356 9742355 := bstep (se 1 (by rfl) ⟨7306766, by rfl⟩ : syracuseStep 9742355 = 14613533) B14613533
theorem B2599037 : Blo 854356 2599037 := bstep (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) B974639
theorem B1321115 : Blo 854356 1321115 := bstep (se 1 (by rfl) ⟨990836, by rfl⟩ : syracuseStep 1321115 = 1981673) B1981673
theorem B4335929 : Blo 854356 4335929 := bstep (se 2 (by rfl) ⟨1625973, by rfl⟩ : syracuseStep 4335929 = 3251947) B3251947
theorem B2894237 : Blo 854356 2894237 := bstep (se 3 (by rfl) ⟨542669, by rfl⟩ : syracuseStep 2894237 = 1085339) B1085339
theorem B2894507 : Blo 854356 2894507 := bstep (se 1 (by rfl) ⟨2170880, by rfl⟩ : syracuseStep 2894507 = 4341761) B4341761
theorem B2435771 : Blo 854356 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B4336577 : Blo 854356 4336577 := bstep (se 2 (by rfl) ⟨1626216, by rfl⟩ : syracuseStep 4336577 = 3252433) B3252433
theorem B11905987 : Blo 854356 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B9874547 : Blo 854356 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B2927759 : Blo 854356 2927759 := bstep (se 1 (by rfl) ⟨2195819, by rfl⟩ : syracuseStep 2927759 = 4391639) B4391639
theorem B2895047 : Blo 854356 2895047 := bstep (se 1 (by rfl) ⟨2171285, by rfl⟩ : syracuseStep 2895047 = 4342571) B4342571
theorem B7318795 : Blo 854356 7318795 := bstep (se 1 (by rfl) ⟨5489096, by rfl⟩ : syracuseStep 7318795 = 10978193) B10978193
theorem B962023 : Blo 854356 962023 := bstep (se 1 (by rfl) ⟨721517, by rfl⟩ : syracuseStep 962023 = 1443035) B1443035
theorem B4337225 : Blo 854356 4337225 := bstep (se 2 (by rfl) ⟨1626459, by rfl⟩ : syracuseStep 4337225 = 3252919) B3252919
theorem B28552933 : Blo 854356 28552933 := bstep (se 4 (by rfl) ⟨2676837, by rfl⟩ : syracuseStep 28552933 = 5353675) B5353675
theorem B37007117 : Blo 854356 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B962527 : Blo 854356 962527 := bstep (se 1 (by rfl) ⟨721895, by rfl⟩ : syracuseStep 962527 = 1443791) B1443791
theorem B3256307 : Blo 854356 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B17576099 : Blo 854356 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B2896343 : Blo 854356 2896343 := bstep (se 1 (by rfl) ⟨2172257, by rfl⟩ : syracuseStep 2896343 = 4344515) B4344515
theorem B963175 : Blo 854356 963175 := bstep (se 1 (by rfl) ⟨722381, by rfl⟩ : syracuseStep 963175 = 1444763) B1444763
theorem B2437913 : Blo 854356 2437913 := bstep (se 2 (by rfl) ⟨914217, by rfl⟩ : syracuseStep 2437913 = 1828435) B1828435
theorem B1028975 : Blo 854356 1028975 := bstep (se 1 (by rfl) ⟨771731, by rfl⟩ : syracuseStep 1028975 = 1543463) B1543463
theorem B2536795 : Blo 854356 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B10991315 : Blo 854356 10991315 := bstep (se 1 (by rfl) ⟨8243486, by rfl⟩ : syracuseStep 10991315 = 16486973) B16486973
theorem B3913535 : Blo 854356 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B2439143 : Blo 854356 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B4339817 : Blo 854356 4339817 := bstep (se 2 (by rfl) ⟨1627431, by rfl⟩ : syracuseStep 4339817 = 3254863) B3254863
theorem B2439497 : Blo 854356 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B16072199 : Blo 854356 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B2440783 : Blo 854356 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B4637135 : Blo 854356 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B59294339 : Blo 854356 59294339 := bstep (se 1 (by rfl) ⟨44470754, by rfl⟩ : syracuseStep 59294339 = 88941509) B88941509
theorem B3654409 : Blo 854356 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B2343737 : Blo 854356 2343737 := bstep (se 2 (by rfl) ⟨878901, by rfl⟩ : syracuseStep 2343737 = 1757803) B1757803
theorem B60081425 : Blo 854356 60081425 := bstep (se 2 (by rfl) ⟨22530534, by rfl⟩ : syracuseStep 60081425 = 45061069) B45061069
theorem B24724925 : Blo 854356 24724925 := bstep (se 3 (by rfl) ⟨4635923, by rfl⟩ : syracuseStep 24724925 = 9271847) B9271847
theorem B13190681 : Blo 854356 13190681 := bstep (se 2 (by rfl) ⟨4946505, by rfl⟩ : syracuseStep 13190681 = 9893011) B9893011
theorem B1623719 : Blo 854356 1623719 := bstep (se 1 (by rfl) ⟨1217789, by rfl⟩ : syracuseStep 1623719 = 2435579) B2435579
theorem B2738387 : Blo 854356 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B12536221 : Blo 854356 12536221 := bstep (se 3 (by rfl) ⟨2350541, by rfl⟩ : syracuseStep 12536221 = 4701083) B4701083
theorem B21088679 : Blo 854356 21088679 := bstep (se 1 (by rfl) ⟨15816509, by rfl⟩ : syracuseStep 21088679 = 31633019) B31633019
theorem B2443745 : Blo 854356 2443745 := bstep (se 2 (by rfl) ⟨916404, by rfl⟩ : syracuseStep 2443745 = 1832809) B1832809
theorem B1624607 : Blo 854356 1624607 := bstep (se 1 (by rfl) ⟨1218455, by rfl⟩ : syracuseStep 1624607 = 2436911) B2436911
theorem B2444087 : Blo 854356 2444087 := bstep (se 1 (by rfl) ⟨1833065, by rfl⟩ : syracuseStep 2444087 = 3666131) B3666131
theorem B3657143 : Blo 854356 3657143 := bstep (se 1 (by rfl) ⟨2742857, by rfl⟩ : syracuseStep 3657143 = 5485715) B5485715
theorem B1625663 : Blo 854356 1625663 := bstep (se 1 (by rfl) ⟨1219247, by rfl⟩ : syracuseStep 1625663 = 2438495) B2438495
theorem B2642303 : Blo 854356 2642303 := bstep (se 1 (by rfl) ⟨1981727, by rfl⟩ : syracuseStep 2642303 = 3963455) B3963455
theorem B15061801 : Blo 854356 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B3527675 : Blo 854356 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B1954871 : Blo 854356 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B3298657 : Blo 854356 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B1923047 : Blo 854356 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B1923065 : Blo 854356 1923065 := bstep (se 2 (by rfl) ⟨721149, by rfl⟩ : syracuseStep 1923065 = 1442299) B1442299
theorem B1923155 : Blo 854356 1923155 := bstep (se 1 (by rfl) ⟨1442366, by rfl⟩ : syracuseStep 1923155 = 2884733) B2884733
theorem B1923227 : Blo 854356 1923227 := bstep (se 1 (by rfl) ⟨1442420, by rfl⟩ : syracuseStep 1923227 = 2884841) B2884841
theorem B1825001 : Blo 854356 1825001 := bstep (se 2 (by rfl) ⟨684375, by rfl⟩ : syracuseStep 1825001 = 1368751) B1368751
theorem B1923335 : Blo 854356 1923335 := bstep (se 1 (by rfl) ⟨1442501, by rfl⟩ : syracuseStep 1923335 = 2885003) B2885003
theorem B2742601 : Blo 854356 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B5495147 : Blo 854356 5495147 := bstep (se 1 (by rfl) ⟨4121360, by rfl⟩ : syracuseStep 5495147 = 8242721) B8242721
theorem B1923641 : Blo 854356 1923641 := bstep (se 2 (by rfl) ⟨721365, by rfl⟩ : syracuseStep 1923641 = 1442731) B1442731
theorem B1629011 : Blo 854356 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B1924361 : Blo 854356 1924361 := bstep (se 2 (by rfl) ⟨721635, by rfl⟩ : syracuseStep 1924361 = 1443271) B1443271
theorem B32988707 : Blo 854356 32988707 := bstep (se 1 (by rfl) ⟨24741530, by rfl⟩ : syracuseStep 32988707 = 49483061) B49483061
theorem B1564303 : Blo 854356 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B39575405 : Blo 854356 39575405 := bstep (se 3 (by rfl) ⟨7420388, by rfl⟩ : syracuseStep 39575405 = 14840777) B14840777
theorem B3661757 : Blo 854356 3661757 := bstep (se 3 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 3661757 = 1373159) B1373159
theorem B1925351 : Blo 854356 1925351 := bstep (se 1 (by rfl) ⟨1444013, by rfl⟩ : syracuseStep 1925351 = 2888027) B2888027
theorem B6939067 : Blo 854356 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B12345857 : Blo 854356 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B4875005 : Blo 854356 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B1925945 : Blo 854356 1925945 := bstep (se 2 (by rfl) ⟨722229, by rfl⟩ : syracuseStep 1925945 = 1444459) B1444459
theorem B1925999 : Blo 854356 1925999 := bstep (se 1 (by rfl) ⟨1444499, by rfl⟩ : syracuseStep 1925999 = 2888999) B2888999
theorem B1926575 : Blo 854356 1926575 := bstep (se 1 (by rfl) ⟨1444931, by rfl⟩ : syracuseStep 1926575 = 2889863) B2889863
theorem B4875713 : Blo 854356 4875713 := bstep (se 2 (by rfl) ⟨1828392, by rfl⟩ : syracuseStep 4875713 = 3656785) B3656785
theorem B25748941 : Blo 854356 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B6514343 : Blo 854356 6514343 := bstep (se 1 (by rfl) ⟨4885757, by rfl⟩ : syracuseStep 6514343 = 9771515) B9771515
theorem B2746075 : Blo 854356 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B878399 : Blo 854356 878399 := bstep (se 1 (by rfl) ⟨658799, by rfl⟩ : syracuseStep 878399 = 1317599) B1317599
theorem B5498711 : Blo 854356 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B1927403 : Blo 854356 1927403 := bstep (se 1 (by rfl) ⟨1445552, by rfl⟩ : syracuseStep 1927403 = 2891105) B2891105
theorem B5204519 : Blo 854356 5204519 := bstep (se 1 (by rfl) ⟨3903389, by rfl⟩ : syracuseStep 5204519 = 7806779) B7806779
theorem B10414973 : Blo 854356 10414973 := bstep (se 3 (by rfl) ⟨1952807, by rfl⟩ : syracuseStep 10414973 = 3905615) B3905615
theorem B12348395 : Blo 854356 12348395 := bstep (se 1 (by rfl) ⟨9261296, by rfl⟩ : syracuseStep 12348395 = 18522593) B18522593
theorem B1928699 : Blo 854356 1928699 := bstep (se 1 (by rfl) ⟨1446524, by rfl⟩ : syracuseStep 1928699 = 2893049) B2893049
theorem B3665533 : Blo 854356 3665533 := bstep (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) B1374575
theorem B1928879 : Blo 854356 1928879 := bstep (se 1 (by rfl) ⟨1446659, by rfl⟩ : syracuseStep 1928879 = 2893319) B2893319
theorem B1929527 : Blo 854356 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B1929599 : Blo 854356 1929599 := bstep (se 1 (by rfl) ⟨1447199, by rfl⟩ : syracuseStep 1929599 = 2894399) B2894399
theorem B6517259 : Blo 854356 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B6943247 : Blo 854356 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B2061487 : Blo 854356 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B2749727 : Blo 854356 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B1832519 : Blo 854356 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B1930823 : Blo 854356 1930823 := bstep (se 1 (by rfl) ⟨1448117, by rfl⟩ : syracuseStep 1930823 = 2896235) B2896235
theorem B1832699 : Blo 854356 1832699 := bstep (se 1 (by rfl) ⟨1374524, by rfl⟩ : syracuseStep 1832699 = 2749049) B2749049
theorem B1931003 : Blo 854356 1931003 := bstep (se 1 (by rfl) ⟨1448252, by rfl⟩ : syracuseStep 1931003 = 2896505) B2896505
theorem B15628727 : Blo 854356 15628727 := bstep (se 1 (by rfl) ⟨11721545, by rfl⟩ : syracuseStep 15628727 = 23443091) B23443091
theorem B4881019 : Blo 854356 4881019 := bstep (se 1 (by rfl) ⟨3660764, by rfl⟩ : syracuseStep 4881019 = 7321529) B7321529
theorem B3079417 : Blo 854356 3079417 := bstep (se 2 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 3079417 = 2309563) B2309563
theorem B2260391 : Blo 854356 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B1539859 : Blo 854356 1539859 := bstep (se 1 (by rfl) ⟨1154894, by rfl⟩ : syracuseStep 1539859 = 2309789) B2309789
theorem B1441759 : Blo 854356 1441759 := bstep (se 1 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 1441759 = 2162639) B2162639
theorem B4325561 : Blo 854356 4325561 := bstep (se 2 (by rfl) ⟨1622085, by rfl⟩ : syracuseStep 4325561 = 3244171) B3244171
theorem B16483283 : Blo 854356 16483283 := bstep (se 1 (by rfl) ⟨12362462, by rfl⟩ : syracuseStep 16483283 = 24724925) B24724925
theorem B1442927 : Blo 854356 1442927 := bstep (se 1 (by rfl) ⟨1082195, by rfl⟩ : syracuseStep 1442927 = 2164391) B2164391
theorem B1082479 : Blo 854356 1082479 := bstep (se 1 (by rfl) ⟨811859, by rfl⟩ : syracuseStep 1082479 = 1623719) B1623719
theorem B2163935 : Blo 854356 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B2884895 : Blo 854356 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B1443359 : Blo 854356 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B1443433 : Blo 854356 1443433 := bstep (se 2 (by rfl) ⟨541287, by rfl⟩ : syracuseStep 1443433 = 1082575) B1082575
theorem B1083071 : Blo 854356 1083071 := bstep (se 1 (by rfl) ⟨812303, by rfl⟩ : syracuseStep 1083071 = 1624607) B1624607
theorem B1444027 : Blo 854356 1444027 := bstep (se 1 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 1444027 = 2166041) B2166041
theorem B854399 : Blo 854356 854399 := bstep (se 1 (by rfl) ⟨640799, by rfl⟩ : syracuseStep 854399 = 1281599) B1281599
theorem B1444223 : Blo 854356 1444223 := bstep (se 1 (by rfl) ⟨1083167, by rfl⟩ : syracuseStep 1444223 = 2166335) B2166335
theorem B1083775 : Blo 854356 1083775 := bstep (se 1 (by rfl) ⟨812831, by rfl⟩ : syracuseStep 1083775 = 1625663) B1625663
theorem B854575 : Blo 854356 854575 := bstep (se 1 (by rfl) ⟨640931, by rfl⟩ : syracuseStep 854575 = 1281863) B1281863
theorem B854631 : Blo 854356 854631 := bstep (se 1 (by rfl) ⟨640973, by rfl⟩ : syracuseStep 854631 = 1281947) B1281947
theorem B6163127 : Blo 854356 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B2886461 : Blo 854356 2886461 := bstep (se 3 (by rfl) ⟨541211, by rfl⟩ : syracuseStep 2886461 = 1082423) B1082423
theorem B1444729 : Blo 854356 1444729 := bstep (se 2 (by rfl) ⟨541773, by rfl⟩ : syracuseStep 1444729 = 1083547) B1083547
theorem B2886569 : Blo 854356 2886569 := bstep (se 2 (by rfl) ⟨1082463, by rfl⟩ : syracuseStep 2886569 = 2164927) B2164927
theorem B855007 : Blo 854356 855007 := bstep (se 1 (by rfl) ⟨641255, by rfl⟩ : syracuseStep 855007 = 1282511) B1282511
theorem B855035 : Blo 854356 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B855103 : Blo 854356 855103 := bstep (se 1 (by rfl) ⟨641327, by rfl⟩ : syracuseStep 855103 = 1282655) B1282655
theorem B2821307 : Blo 854356 2821307 := bstep (se 1 (by rfl) ⟨2115980, by rfl⟩ : syracuseStep 2821307 = 4231961) B4231961
theorem B16714961 : Blo 854356 16714961 := bstep (se 2 (by rfl) ⟨6268110, by rfl⟩ : syracuseStep 16714961 = 12536221) B12536221
theorem B855423 : Blo 854356 855423 := bstep (se 1 (by rfl) ⟨641567, by rfl⟩ : syracuseStep 855423 = 1283135) B1283135
theorem B855451 : Blo 854356 855451 := bstep (se 1 (by rfl) ⟨641588, by rfl⟩ : syracuseStep 855451 = 1283177) B1283177
theorem B855519 : Blo 854356 855519 := bstep (se 1 (by rfl) ⟨641639, by rfl⟩ : syracuseStep 855519 = 1283279) B1283279
theorem B855655 : Blo 854356 855655 := bstep (se 1 (by rfl) ⟨641741, by rfl⟩ : syracuseStep 855655 = 1283483) B1283483
theorem B855803 : Blo 854356 855803 := bstep (se 1 (by rfl) ⟨641852, by rfl⟩ : syracuseStep 855803 = 1283705) B1283705
theorem B855871 : Blo 854356 855871 := bstep (se 1 (by rfl) ⟨641903, by rfl⟩ : syracuseStep 855871 = 1283807) B1283807
theorem B855935 : Blo 854356 855935 := bstep (se 1 (by rfl) ⟨641951, by rfl⟩ : syracuseStep 855935 = 1283903) B1283903
theorem B1445863 : Blo 854356 1445863 := bstep (se 1 (by rfl) ⟨1084397, by rfl⟩ : syracuseStep 1445863 = 2168795) B2168795
theorem B1282031 : Blo 854356 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B856047 : Blo 854356 856047 := bstep (se 1 (by rfl) ⟨642035, by rfl⟩ : syracuseStep 856047 = 1284071) B1284071
theorem B1282043 : Blo 854356 1282043 := bstep (se 1 (by rfl) ⟨961532, by rfl⟩ : syracuseStep 1282043 = 1923065) B1923065
theorem B856059 : Blo 854356 856059 := bstep (se 1 (by rfl) ⟨642044, by rfl⟩ : syracuseStep 856059 = 1284089) B1284089
theorem B1282103 : Blo 854356 1282103 := bstep (se 1 (by rfl) ⟨961577, by rfl⟩ : syracuseStep 1282103 = 1923155) B1923155
theorem B856127 : Blo 854356 856127 := bstep (se 1 (by rfl) ⟨642095, by rfl⟩ : syracuseStep 856127 = 1284191) B1284191
theorem B1445951 : Blo 854356 1445951 := bstep (se 1 (by rfl) ⟨1084463, by rfl⟩ : syracuseStep 1445951 = 2168927) B2168927
theorem B1282151 : Blo 854356 1282151 := bstep (se 1 (by rfl) ⟨961613, by rfl⟩ : syracuseStep 1282151 = 1923227) B1923227
theorem B856167 : Blo 854356 856167 := bstep (se 1 (by rfl) ⟨642125, by rfl⟩ : syracuseStep 856167 = 1284251) B1284251
theorem B856191 : Blo 854356 856191 := bstep (se 1 (by rfl) ⟨642143, by rfl⟩ : syracuseStep 856191 = 1284287) B1284287
theorem B1216667 : Blo 854356 1216667 := bstep (se 1 (by rfl) ⟨912500, by rfl⟩ : syracuseStep 1216667 = 1825001) B1825001
theorem B856219 : Blo 854356 856219 := bstep (se 1 (by rfl) ⟨642164, by rfl⟩ : syracuseStep 856219 = 1284329) B1284329
theorem B1282223 : Blo 854356 1282223 := bstep (se 1 (by rfl) ⟨961667, by rfl⟩ : syracuseStep 1282223 = 1923335) B1923335
theorem B856423 : Blo 854356 856423 := bstep (se 1 (by rfl) ⟨642317, by rfl⟩ : syracuseStep 856423 = 1284635) B1284635
theorem B1282427 : Blo 854356 1282427 := bstep (se 1 (by rfl) ⟨961820, by rfl⟩ : syracuseStep 1282427 = 1923641) B1923641
theorem B856475 : Blo 854356 856475 := bstep (se 1 (by rfl) ⟨642356, by rfl⟩ : syracuseStep 856475 = 1284713) B1284713
theorem B1282697 : Blo 854356 1282697 := bstep (se 2 (by rfl) ⟨481011, by rfl⟩ : syracuseStep 1282697 = 962023) B962023
theorem B856827 : Blo 854356 856827 := bstep (se 1 (by rfl) ⟨642620, by rfl⟩ : syracuseStep 856827 = 1285241) B1285241
theorem B2888459 : Blo 854356 2888459 := bstep (se 1 (by rfl) ⟨2166344, by rfl⟩ : syracuseStep 2888459 = 4332689) B4332689
theorem B856895 : Blo 854356 856895 := bstep (se 1 (by rfl) ⟨642671, by rfl⟩ : syracuseStep 856895 = 1285343) B1285343
theorem B4887377 : Blo 854356 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B1282907 : Blo 854356 1282907 := bstep (se 1 (by rfl) ⟨962180, by rfl⟩ : syracuseStep 1282907 = 1924361) B1924361
theorem B856923 : Blo 854356 856923 := bstep (se 1 (by rfl) ⟨642692, by rfl⟩ : syracuseStep 856923 = 1285385) B1285385
theorem B856991 : Blo 854356 856991 := bstep (se 1 (by rfl) ⟨642743, by rfl⟩ : syracuseStep 856991 = 1285487) B1285487
theorem B1446815 : Blo 854356 1446815 := bstep (se 1 (by rfl) ⟨1085111, by rfl⟩ : syracuseStep 1446815 = 2170223) B2170223
theorem B857071 : Blo 854356 857071 := bstep (se 1 (by rfl) ⟨642803, by rfl⟩ : syracuseStep 857071 = 1285607) B1285607
theorem B21992471 : Blo 854356 21992471 := bstep (se 1 (by rfl) ⟨16494353, by rfl⟩ : syracuseStep 21992471 = 32988707) B32988707
theorem B2888729 : Blo 854356 2888729 := bstep (se 2 (by rfl) ⟨1083273, by rfl⟩ : syracuseStep 2888729 = 2166547) B2166547
theorem B857159 : Blo 854356 857159 := bstep (se 1 (by rfl) ⟨642869, by rfl⟩ : syracuseStep 857159 = 1285739) B1285739
theorem B857243 : Blo 854356 857243 := bstep (se 1 (by rfl) ⟨642932, by rfl⟩ : syracuseStep 857243 = 1285865) B1285865
theorem B26383603 : Blo 854356 26383603 := bstep (se 1 (by rfl) ⟨19787702, by rfl⟩ : syracuseStep 26383603 = 39575405) B39575405
theorem B857339 : Blo 854356 857339 := bstep (se 1 (by rfl) ⟨643004, by rfl⟩ : syracuseStep 857339 = 1286009) B1286009
theorem B1283369 : Blo 854356 1283369 := bstep (se 2 (by rfl) ⟨481263, by rfl⟩ : syracuseStep 1283369 = 962527) B962527
theorem B857407 : Blo 854356 857407 := bstep (se 1 (by rfl) ⟨643055, by rfl⟩ : syracuseStep 857407 = 1286111) B1286111
theorem B4330907 : Blo 854356 4330907 := bstep (se 1 (by rfl) ⟨3248180, by rfl⟩ : syracuseStep 4330907 = 6496361) B6496361
theorem B857575 : Blo 854356 857575 := bstep (se 1 (by rfl) ⟨643181, by rfl⟩ : syracuseStep 857575 = 1286363) B1286363
theorem B1283567 : Blo 854356 1283567 := bstep (se 1 (by rfl) ⟨962675, by rfl⟩ : syracuseStep 1283567 = 1925351) B1925351
theorem B857583 : Blo 854356 857583 := bstep (se 1 (by rfl) ⟨643187, by rfl⟩ : syracuseStep 857583 = 1286375) B1286375
theorem B857691 : Blo 854356 857691 := bstep (se 1 (by rfl) ⟨643268, by rfl⟩ : syracuseStep 857691 = 1286537) B1286537
theorem B857755 : Blo 854356 857755 := bstep (se 1 (by rfl) ⟨643316, by rfl⟩ : syracuseStep 857755 = 1286633) B1286633
theorem B8230571 : Blo 854356 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B857839 : Blo 854356 857839 := bstep (se 1 (by rfl) ⟨643379, by rfl⟩ : syracuseStep 857839 = 1286759) B1286759
theorem B857927 : Blo 854356 857927 := bstep (se 1 (by rfl) ⟨643445, by rfl⟩ : syracuseStep 857927 = 1286891) B1286891
theorem B3250003 : Blo 854356 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B857947 : Blo 854356 857947 := bstep (se 1 (by rfl) ⟨643460, by rfl⟩ : syracuseStep 857947 = 1286921) B1286921
theorem B1283963 : Blo 854356 1283963 := bstep (se 1 (by rfl) ⟨962972, by rfl⟩ : syracuseStep 1283963 = 1925945) B1925945
theorem B1283999 : Blo 854356 1283999 := bstep (se 1 (by rfl) ⟨962999, by rfl⟩ : syracuseStep 1283999 = 1925999) B1925999
theorem B858015 : Blo 854356 858015 := bstep (se 1 (by rfl) ⟨643511, by rfl⟩ : syracuseStep 858015 = 1287023) B1287023
theorem B858183 : Blo 854356 858183 := bstep (se 1 (by rfl) ⟨643637, by rfl⟩ : syracuseStep 858183 = 1287275) B1287275
theorem B1284233 : Blo 854356 1284233 := bstep (se 2 (by rfl) ⟨481587, by rfl⟩ : syracuseStep 1284233 = 963175) B963175
theorem B858343 : Blo 854356 858343 := bstep (se 1 (by rfl) ⟨643757, by rfl⟩ : syracuseStep 858343 = 1287515) B1287515
theorem B1284383 : Blo 854356 1284383 := bstep (se 1 (by rfl) ⟨963287, by rfl⟩ : syracuseStep 1284383 = 1926575) B1926575
theorem B2169119 : Blo 854356 2169119 := bstep (se 1 (by rfl) ⟨1626839, by rfl⟩ : syracuseStep 2169119 = 3253679) B3253679
theorem B3250475 : Blo 854356 3250475 := bstep (se 1 (by rfl) ⟨2437856, by rfl⟩ : syracuseStep 3250475 = 4875713) B4875713
theorem B2890079 : Blo 854356 2890079 := bstep (se 1 (by rfl) ⟨2167559, by rfl⟩ : syracuseStep 2890079 = 4335119) B4335119
theorem B3479927 : Blo 854356 3479927 := bstep (se 1 (by rfl) ⟨2609945, by rfl⟩ : syracuseStep 3479927 = 5219891) B5219891
theorem B56236477 : Blo 854356 56236477 := bstep (se 3 (by rfl) ⟨10544339, by rfl⟩ : syracuseStep 56236477 = 21088679) B21088679
theorem B2890241 : Blo 854356 2890241 := bstep (se 2 (by rfl) ⟨1083840, by rfl⟩ : syracuseStep 2890241 = 2167681) B2167681
theorem B6494903 : Blo 854356 6494903 := bstep (se 1 (by rfl) ⟨4871177, by rfl⟩ : syracuseStep 6494903 = 9742355) B9742355
theorem B1284935 : Blo 854356 1284935 := bstep (se 1 (by rfl) ⟨963701, by rfl⟩ : syracuseStep 1284935 = 1927403) B1927403
theorem B2890619 : Blo 854356 2890619 := bstep (se 1 (by rfl) ⟨2167964, by rfl⟩ : syracuseStep 2890619 = 4335929) B4335929
theorem B3382393 : Blo 854356 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B4398209 : Blo 854356 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B6495389 : Blo 854356 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B2891051 : Blo 854356 2891051 := bstep (se 1 (by rfl) ⟨2168288, by rfl⟩ : syracuseStep 2891051 = 4336577) B4336577
theorem B8232263 : Blo 854356 8232263 := bstep (se 1 (by rfl) ⟨6174197, by rfl⟩ : syracuseStep 8232263 = 12348395) B12348395
theorem B2891321 : Blo 854356 2891321 := bstep (se 2 (by rfl) ⟨1084245, by rfl⟩ : syracuseStep 2891321 = 2168491) B2168491
theorem B1285799 : Blo 854356 1285799 := bstep (se 1 (by rfl) ⟨964349, by rfl⟩ : syracuseStep 1285799 = 1928699) B1928699
theorem B2891483 : Blo 854356 2891483 := bstep (se 1 (by rfl) ⟨2168612, by rfl⟩ : syracuseStep 2891483 = 4337225) B4337225
theorem B1285919 : Blo 854356 1285919 := bstep (se 1 (by rfl) ⟨964439, by rfl⟩ : syracuseStep 1285919 = 1928879) B1928879
theorem B2891753 : Blo 854356 2891753 := bstep (se 2 (by rfl) ⟨1084407, by rfl⟩ : syracuseStep 2891753 = 2168815) B2168815
theorem B2170871 : Blo 854356 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B1286351 : Blo 854356 1286351 := bstep (se 1 (by rfl) ⟨964763, by rfl⟩ : syracuseStep 1286351 = 1929527) B1929527
theorem B1286399 : Blo 854356 1286399 := bstep (se 1 (by rfl) ⟨964799, by rfl⟩ : syracuseStep 1286399 = 1929599) B1929599
theorem B4628831 : Blo 854356 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B7807357 : Blo 854356 7807357 := bstep (se 3 (by rfl) ⟨1463879, by rfl⟩ : syracuseStep 7807357 = 2927759) B2927759
theorem B1221679 : Blo 854356 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B1287215 : Blo 854356 1287215 := bstep (se 1 (by rfl) ⟨965411, by rfl⟩ : syracuseStep 1287215 = 1930823) B1930823
theorem B1221799 : Blo 854356 1221799 := bstep (se 1 (by rfl) ⟨916349, by rfl⟩ : syracuseStep 1221799 = 1832699) B1832699
theorem B1287335 : Blo 854356 1287335 := bstep (se 1 (by rfl) ⟨965501, by rfl⟩ : syracuseStep 1287335 = 1931003) B1931003
theorem B2893211 : Blo 854356 2893211 := bstep (se 1 (by rfl) ⟨2169908, by rfl⟩ : syracuseStep 2893211 = 4339817) B4339817
theorem B4105889 : Blo 854356 4105889 := bstep (se 2 (by rfl) ⟨1539708, by rfl⟩ : syracuseStep 4105889 = 3079417) B3079417
theorem B31205209 : Blo 854356 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B3254377 : Blo 854356 3254377 := bstep (se 2 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 3254377 = 2440783) B2440783
theorem B39529559 : Blo 854356 39529559 := bstep (se 1 (by rfl) ⟨29647169, by rfl⟩ : syracuseStep 39529559 = 59294339) B59294339
theorem B24652957 : Blo 854356 24652957 := bstep (se 3 (by rfl) ⟨4622429, by rfl⟩ : syracuseStep 24652957 = 9244859) B9244859
theorem B9252089 : Blo 854356 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B40054283 : Blo 854356 40054283 := bstep (se 1 (by rfl) ⟨30040712, by rfl⟩ : syracuseStep 40054283 = 60081425) B60081425
theorem B8793787 : Blo 854356 8793787 := bstep (se 1 (by rfl) ⟨6595340, by rfl⟩ : syracuseStep 8793787 = 13190681) B13190681
theorem B3518333 : Blo 854356 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B12365693 : Blo 854356 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B4108519 : Blo 854356 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B3256595 : Blo 854356 3256595 := bstep (se 1 (by rfl) ⟨2442446, by rfl⟩ : syracuseStep 3256595 = 4884893) B4884893
theorem B13906349 : Blo 854356 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B963391 : Blo 854356 963391 := bstep (se 1 (by rfl) ⟨722543, by rfl⟩ : syracuseStep 963391 = 1445087) B1445087
theorem B9745271 : Blo 854356 9745271 := bstep (se 1 (by rfl) ⟨7308953, by rfl⟩ : syracuseStep 9745271 = 14617907) B14617907
theorem B2438095 : Blo 854356 2438095 := bstep (se 1 (by rfl) ⟨1828571, by rfl⟩ : syracuseStep 2438095 = 3657143) B3657143
theorem B2896937 : Blo 854356 2896937 := bstep (se 2 (by rfl) ⟨1086351, by rfl⟩ : syracuseStep 2896937 = 2172703) B2172703
theorem B963679 : Blo 854356 963679 := bstep (se 1 (by rfl) ⟨722759, by rfl⟩ : syracuseStep 963679 = 1445519) B1445519
theorem B4109579 : Blo 854356 4109579 := bstep (se 1 (by rfl) ⟨3082184, by rfl⟩ : syracuseStep 4109579 = 6164369) B6164369
theorem B15874649 : Blo 854356 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B1949359 : Blo 854356 1949359 := bstep (se 1 (by rfl) ⟨1462019, by rfl⟩ : syracuseStep 1949359 = 2924039) B2924039
theorem B2441171 : Blo 854356 2441171 := bstep (se 1 (by rfl) ⟨1830878, by rfl⟩ : syracuseStep 2441171 = 3661757) B3661757
theorem B1622207 : Blo 854356 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B3522973 : Blo 854356 3522973 := bstep (se 3 (by rfl) ⟨660557, by rfl⟩ : syracuseStep 3522973 = 1321115) B1321115
theorem B1622443 : Blo 854356 1622443 := bstep (se 1 (by rfl) ⟨1216832, by rfl⟩ : syracuseStep 1622443 = 2433665) B2433665
theorem B4342895 : Blo 854356 4342895 := bstep (se 1 (by rfl) ⟨3257171, by rfl⟩ : syracuseStep 4342895 = 6514343) B6514343
theorem B4344029 : Blo 854356 4344029 := bstep (se 3 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 4344029 = 1629011) B1629011
theorem B11717399 : Blo 854356 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B1624873 : Blo 854356 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B4344839 : Blo 854356 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B3656801 : Blo 854356 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B13159589 : Blo 854356 13159589 := bstep (se 4 (by rfl) ⟨1233711, by rfl⟩ : syracuseStep 13159589 = 2467423) B2467423
theorem B1625275 : Blo 854356 1625275 := bstep (se 1 (by rfl) ⟨1218956, by rfl⟩ : syracuseStep 1625275 = 2437913) B2437913
theorem B18795997 : Blo 854356 18795997 := bstep (se 3 (by rfl) ⟨3524249, by rfl⟩ : syracuseStep 18795997 = 7048499) B7048499
theorem B6508025 : Blo 854356 6508025 := bstep (se 2 (by rfl) ⟨2440509, by rfl⟩ : syracuseStep 6508025 = 4881019) B4881019
theorem B7327543 : Blo 854356 7327543 := bstep (se 1 (by rfl) ⟨5495657, by rfl⟩ : syracuseStep 7327543 = 10991315) B10991315
theorem B2609023 : Blo 854356 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B1626095 : Blo 854356 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B1626331 : Blo 854356 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B2053145 : Blo 854356 2053145 := bstep (se 2 (by rfl) ⟨769929, by rfl⟩ : syracuseStep 2053145 = 1539859) B1539859
theorem B1922345 : Blo 854356 1922345 := bstep (se 2 (by rfl) ⟨720879, by rfl⟩ : syracuseStep 1922345 = 1441759) B1441759
theorem B1922543 : Blo 854356 1922543 := bstep (se 1 (by rfl) ⟨1441907, by rfl⟩ : syracuseStep 1922543 = 2883815) B2883815
theorem B1922939 : Blo 854356 1922939 := bstep (se 1 (by rfl) ⟨1442204, by rfl⟩ : syracuseStep 1922939 = 2884409) B2884409
theorem B1562491 : Blo 854356 1562491 := bstep (se 1 (by rfl) ⟨1171868, by rfl⟩ : syracuseStep 1562491 = 2343737) B2343737
theorem B1922975 : Blo 854356 1922975 := bstep (se 1 (by rfl) ⟨1442231, by rfl⟩ : syracuseStep 1922975 = 2884463) B2884463
theorem B1923209 : Blo 854356 1923209 := bstep (se 2 (by rfl) ⟨721203, by rfl⟩ : syracuseStep 1923209 = 1442407) B1442407
theorem B1923425 : Blo 854356 1923425 := bstep (se 2 (by rfl) ⟨721284, by rfl⟩ : syracuseStep 1923425 = 1442569) B1442569
theorem B4872545 : Blo 854356 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B1923515 : Blo 854356 1923515 := bstep (se 1 (by rfl) ⟨1442636, by rfl⟩ : syracuseStep 1923515 = 2885273) B2885273
theorem B2054683 : Blo 854356 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B133487189 : Blo 854356 133487189 := bstep (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) B1564303
theorem B1825591 : Blo 854356 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B1923911 : Blo 854356 1923911 := bstep (se 1 (by rfl) ⟨1442933, by rfl⟩ : syracuseStep 1923911 = 2885867) B2885867
theorem B1629163 : Blo 854356 1629163 := bstep (se 1 (by rfl) ⟨1221872, by rfl⟩ : syracuseStep 1629163 = 2443745) B2443745
theorem B1924217 : Blo 854356 1924217 := bstep (se 2 (by rfl) ⟨721581, by rfl⟩ : syracuseStep 1924217 = 1443163) B1443163
theorem B1629391 : Blo 854356 1629391 := bstep (se 1 (by rfl) ⟨1222043, by rfl⟩ : syracuseStep 1629391 = 2444087) B2444087
theorem B4119785 : Blo 854356 4119785 := bstep (se 2 (by rfl) ⟨1544919, by rfl⟩ : syracuseStep 4119785 = 3089839) B3089839
theorem B34331921 : Blo 854356 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B3661433 : Blo 854356 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B1924775 : Blo 854356 1924775 := bstep (se 1 (by rfl) ⟨1443581, by rfl⟩ : syracuseStep 1924775 = 2887163) B2887163
theorem B1924883 : Blo 854356 1924883 := bstep (se 1 (by rfl) ⟨1443662, by rfl⟩ : syracuseStep 1924883 = 2887325) B2887325
theorem B4874003 : Blo 854356 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B1925243 : Blo 854356 1925243 := bstep (se 1 (by rfl) ⟨1443932, by rfl⟩ : syracuseStep 1925243 = 2887865) B2887865
theorem B1761535 : Blo 854356 1761535 := bstep (se 1 (by rfl) ⟨1321151, by rfl⟩ : syracuseStep 1761535 = 2642303) B2642303
theorem B1925513 : Blo 854356 1925513 := bstep (se 2 (by rfl) ⟨722067, by rfl⟩ : syracuseStep 1925513 = 1444135) B1444135
theorem B2351783 : Blo 854356 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1303247 : Blo 854356 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B1926647 : Blo 854356 1926647 := bstep (se 1 (by rfl) ⟨1444985, by rfl⟩ : syracuseStep 1926647 = 2889971) B2889971
theorem B1926683 : Blo 854356 1926683 := bstep (se 1 (by rfl) ⟨1445012, by rfl⟩ : syracuseStep 1926683 = 2890025) B2890025
theorem B3663431 : Blo 854356 3663431 := bstep (se 1 (by rfl) ⟨2747573, by rfl⟩ : syracuseStep 3663431 = 5495147) B5495147
theorem B9758393 : Blo 854356 9758393 := bstep (se 2 (by rfl) ⟨3659397, by rfl⟩ : syracuseStep 9758393 = 7318795) B7318795
theorem B6580075 : Blo 854356 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B8218883 : Blo 854356 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B38070577 : Blo 854356 38070577 := bstep (se 2 (by rfl) ⟨14276466, by rfl⟩ : syracuseStep 38070577 = 28552933) B28552933
theorem B1927673 : Blo 854356 1927673 := bstep (se 2 (by rfl) ⟨722877, by rfl⟩ : syracuseStep 1927673 = 1445755) B1445755
theorem B1927727 : Blo 854356 1927727 := bstep (se 1 (by rfl) ⟨1445795, by rfl⟩ : syracuseStep 1927727 = 2891591) B2891591
theorem B1927763 : Blo 854356 1927763 := bstep (se 1 (by rfl) ⟨1445822, by rfl⟩ : syracuseStep 1927763 = 2891645) B2891645
theorem B133196501 : Blo 854356 133196501 := bstep (se 7 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 133196501 = 3121793) B3121793
theorem B1927943 : Blo 854356 1927943 := bstep (se 1 (by rfl) ⟨1445957, by rfl⟩ : syracuseStep 1927943 = 2891915) B2891915
theorem B1928159 : Blo 854356 1928159 := bstep (se 1 (by rfl) ⟨1446119, by rfl⟩ : syracuseStep 1928159 = 2892239) B2892239
theorem B1928375 : Blo 854356 1928375 := bstep (se 1 (by rfl) ⟨1446281, by rfl⟩ : syracuseStep 1928375 = 2892563) B2892563
theorem B1732279 : Blo 854356 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B20082401 : Blo 854356 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B1928951 : Blo 854356 1928951 := bstep (se 1 (by rfl) ⟨1446713, by rfl⟩ : syracuseStep 1928951 = 2893427) B2893427
theorem B1929023 : Blo 854356 1929023 := bstep (se 1 (by rfl) ⟨1446767, by rfl⟩ : syracuseStep 1929023 = 2893535) B2893535
theorem B3665807 : Blo 854356 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B1929131 : Blo 854356 1929131 := bstep (se 1 (by rfl) ⟨1446848, by rfl⟩ : syracuseStep 1929131 = 2893697) B2893697
theorem B1732691 : Blo 854356 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B2748649 : Blo 854356 2748649 := bstep (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) B2061487
theorem B1929491 : Blo 854356 1929491 := bstep (se 1 (by rfl) ⟨1447118, by rfl⟩ : syracuseStep 1929491 = 2894237) B2894237
theorem B3469679 : Blo 854356 3469679 := bstep (se 1 (by rfl) ⟨2602259, by rfl⟩ : syracuseStep 3469679 = 5204519) B5204519
theorem B1929671 : Blo 854356 1929671 := bstep (se 1 (by rfl) ⟨1447253, by rfl⟩ : syracuseStep 1929671 = 2894507) B2894507
theorem B6943315 : Blo 854356 6943315 := bstep (se 1 (by rfl) ⟨5207486, by rfl⟩ : syracuseStep 6943315 = 10414973) B10414973
theorem B6583031 : Blo 854356 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B2061065 : Blo 854356 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B1930031 : Blo 854356 1930031 := bstep (se 1 (by rfl) ⟨1447523, by rfl⟩ : syracuseStep 1930031 = 2895047) B2895047
theorem B1930121 : Blo 854356 1930121 := bstep (se 2 (by rfl) ⟨723795, by rfl⟩ : syracuseStep 1930121 = 1447591) B1447591
theorem B24671411 : Blo 854356 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B2061641 : Blo 854356 2061641 := bstep (se 2 (by rfl) ⟨773115, by rfl⟩ : syracuseStep 2061641 = 1546231) B1546231
theorem B1930895 : Blo 854356 1930895 := bstep (se 1 (by rfl) ⟨1448171, by rfl⟩ : syracuseStep 1930895 = 2896343) B2896343
theorem B1930985 : Blo 854356 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B9369589 : Blo 854356 9369589 := bstep (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) B878399
theorem B1833151 : Blo 854356 1833151 := bstep (se 1 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 1833151 = 2749727) B2749727
theorem B6027709 : Blo 854356 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B10975733 : Blo 854356 10975733 := bstep (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) B1028975
theorem B10419151 : Blo 854356 10419151 := bstep (se 1 (by rfl) ⟨7814363, by rfl⟩ : syracuseStep 10419151 = 15628727) B15628727
theorem B32079037 : Blo 854356 32079037 := bstep (se 3 (by rfl) ⟨6014819, by rfl⟩ : syracuseStep 32079037 = 12029639) B12029639
theorem B10714799 : Blo 854356 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B2883707 : Blo 854356 2883707 := bstep (se 1 (by rfl) ⟨2162780, by rfl⟩ : syracuseStep 2883707 = 4325561) B4325561
theorem B4620509 : Blo 854356 4620509 := bstep (se 3 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 4620509 = 1732691) B1732691
theorem B3244445 : Blo 854356 3244445 := bstep (se 3 (by rfl) ⟨608333, by rfl⟩ : syracuseStep 3244445 = 1216667) B1216667
theorem B4325885 : Blo 854356 4325885 := bstep (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) B1622207
theorem B2163257 : Blo 854356 2163257 := bstep (se 2 (by rfl) ⟨811221, by rfl⟩ : syracuseStep 2163257 = 1622443) B1622443
theorem B1442623 : Blo 854356 1442623 := bstep (se 1 (by rfl) ⟨1081967, by rfl⟩ : syracuseStep 1442623 = 2163935) B2163935
theorem B1443305 : Blo 854356 1443305 := bstep (se 2 (by rfl) ⟨541239, by rfl⟩ : syracuseStep 1443305 = 1082479) B1082479
theorem B3475325 : Blo 854356 3475325 := bstep (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) B1303247
theorem B11143307 : Blo 854356 11143307 := bstep (se 1 (by rfl) ⟨8357480, by rfl⟩ : syracuseStep 11143307 = 16714961) B16714961
theorem B854687 : Blo 854356 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B854695 : Blo 854356 854695 := bstep (se 1 (by rfl) ⟨641021, by rfl⟩ : syracuseStep 854695 = 1282043) B1282043
theorem B854735 : Blo 854356 854735 := bstep (se 1 (by rfl) ⟨641051, by rfl⟩ : syracuseStep 854735 = 1282103) B1282103
theorem B5475053 : Blo 854356 5475053 := bstep (se 3 (by rfl) ⟨1026572, by rfl⟩ : syracuseStep 5475053 = 2053145) B2053145
theorem B854767 : Blo 854356 854767 := bstep (se 1 (by rfl) ⟨641075, by rfl⟩ : syracuseStep 854767 = 1282151) B1282151
theorem B854815 : Blo 854356 854815 := bstep (se 1 (by rfl) ⟨641111, by rfl⟩ : syracuseStep 854815 = 1282223) B1282223
theorem B854951 : Blo 854356 854951 := bstep (se 1 (by rfl) ⟨641213, by rfl⟩ : syracuseStep 854951 = 1282427) B1282427
theorem B50760769 : Blo 854356 50760769 := bstep (se 2 (by rfl) ⟨19035288, by rfl⟩ : syracuseStep 50760769 = 38070577) B38070577
theorem B855131 : Blo 854356 855131 := bstep (se 1 (by rfl) ⟨641348, by rfl⟩ : syracuseStep 855131 = 1282697) B1282697
theorem B1445033 : Blo 854356 1445033 := bstep (se 2 (by rfl) ⟨541887, by rfl⟩ : syracuseStep 1445033 = 1083775) B1083775
theorem B855271 : Blo 854356 855271 := bstep (se 1 (by rfl) ⟨641453, by rfl⟩ : syracuseStep 855271 = 1282907) B1282907
theorem B1281563 : Blo 854356 1281563 := bstep (se 1 (by rfl) ⟨961172, by rfl⟩ : syracuseStep 1281563 = 1922345) B1922345
theorem B855579 : Blo 854356 855579 := bstep (se 1 (by rfl) ⟨641684, by rfl⟩ : syracuseStep 855579 = 1283369) B1283369
theorem B2887271 : Blo 854356 2887271 := bstep (se 1 (by rfl) ⟨2165453, by rfl⟩ : syracuseStep 2887271 = 4330907) B4330907
theorem B1281695 : Blo 854356 1281695 := bstep (se 1 (by rfl) ⟨961271, by rfl⟩ : syracuseStep 1281695 = 1922543) B1922543
theorem B855711 : Blo 854356 855711 := bstep (se 1 (by rfl) ⟨641783, by rfl⟩ : syracuseStep 855711 = 1283567) B1283567
theorem B2166497 : Blo 854356 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1281959 : Blo 854356 1281959 := bstep (se 1 (by rfl) ⟨961469, by rfl⟩ : syracuseStep 1281959 = 1922939) B1922939
theorem B855975 : Blo 854356 855975 := bstep (se 1 (by rfl) ⟨641981, by rfl⟩ : syracuseStep 855975 = 1283963) B1283963
theorem B1281983 : Blo 854356 1281983 := bstep (se 1 (by rfl) ⟨961487, by rfl⟩ : syracuseStep 1281983 = 1922975) B1922975
theorem B855999 : Blo 854356 855999 := bstep (se 1 (by rfl) ⟨641999, by rfl⟩ : syracuseStep 855999 = 1283999) B1283999
theorem B1282139 : Blo 854356 1282139 := bstep (se 1 (by rfl) ⟨961604, by rfl⟩ : syracuseStep 1282139 = 1923209) B1923209
theorem B856155 : Blo 854356 856155 := bstep (se 1 (by rfl) ⟨642116, by rfl⟩ : syracuseStep 856155 = 1284233) B1284233
theorem B856255 : Blo 854356 856255 := bstep (se 1 (by rfl) ⟨642191, by rfl⟩ : syracuseStep 856255 = 1284383) B1284383
theorem B1446079 : Blo 854356 1446079 := bstep (se 1 (by rfl) ⟨1084559, by rfl⟩ : syracuseStep 1446079 = 2169119) B2169119
theorem B2166983 : Blo 854356 2166983 := bstep (se 1 (by rfl) ⟨1625237, by rfl⟩ : syracuseStep 2166983 = 3250475) B3250475
theorem B32870609 : Blo 854356 32870609 := bstep (se 2 (by rfl) ⟨12326478, by rfl⟩ : syracuseStep 32870609 = 24652957) B24652957
theorem B1282283 : Blo 854356 1282283 := bstep (se 1 (by rfl) ⟨961712, by rfl⟩ : syracuseStep 1282283 = 1923425) B1923425
theorem B3248363 : Blo 854356 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B2167033 : Blo 854356 2167033 := bstep (se 2 (by rfl) ⟨812637, by rfl⟩ : syracuseStep 2167033 = 1625275) B1625275
theorem B1282343 : Blo 854356 1282343 := bstep (se 1 (by rfl) ⟨961757, by rfl⟩ : syracuseStep 1282343 = 1923515) B1923515
theorem B4329935 : Blo 854356 4329935 := bstep (se 1 (by rfl) ⟨3247451, by rfl⟩ : syracuseStep 4329935 = 6494903) B6494903
theorem B2888189 : Blo 854356 2888189 := bstep (se 3 (by rfl) ⟨541535, by rfl⟩ : syracuseStep 2888189 = 1083071) B1083071
theorem B1282607 : Blo 854356 1282607 := bstep (se 1 (by rfl) ⟨961955, by rfl⟩ : syracuseStep 1282607 = 1923911) B1923911
theorem B856623 : Blo 854356 856623 := bstep (se 1 (by rfl) ⟨642467, by rfl⟩ : syracuseStep 856623 = 1284935) B1284935
theorem B1282811 : Blo 854356 1282811 := bstep (se 1 (by rfl) ⟨962108, by rfl⟩ : syracuseStep 1282811 = 1924217) B1924217
theorem B4330259 : Blo 854356 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B9770057 : Blo 854356 9770057 := bstep (se 2 (by rfl) ⟨3663771, by rfl⟩ : syracuseStep 9770057 = 7327543) B7327543
theorem B1283183 : Blo 854356 1283183 := bstep (se 1 (by rfl) ⟨962387, by rfl⟩ : syracuseStep 1283183 = 1924775) B1924775
theorem B857199 : Blo 854356 857199 := bstep (se 1 (by rfl) ⟨642899, by rfl⟩ : syracuseStep 857199 = 1285799) B1285799
theorem B3478697 : Blo 854356 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B1283255 : Blo 854356 1283255 := bstep (se 1 (by rfl) ⟨962441, by rfl⟩ : syracuseStep 1283255 = 1924883) B1924883
theorem B3249335 : Blo 854356 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B857279 : Blo 854356 857279 := bstep (se 1 (by rfl) ⟨642959, by rfl⟩ : syracuseStep 857279 = 1285919) B1285919
theorem B1447247 : Blo 854356 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B1283495 : Blo 854356 1283495 := bstep (se 1 (by rfl) ⟨962621, by rfl⟩ : syracuseStep 1283495 = 1925243) B1925243
theorem B857567 : Blo 854356 857567 := bstep (se 1 (by rfl) ⟨643175, by rfl⟩ : syracuseStep 857567 = 1286351) B1286351
theorem B857599 : Blo 854356 857599 := bstep (se 1 (by rfl) ⟨643199, by rfl⟩ : syracuseStep 857599 = 1286399) B1286399
theorem B1283675 : Blo 854356 1283675 := bstep (se 1 (by rfl) ⟨962756, by rfl⟩ : syracuseStep 1283675 = 1925513) B1925513
theorem B2168441 : Blo 854356 2168441 := bstep (se 2 (by rfl) ⟨813165, by rfl⟩ : syracuseStep 2168441 = 1626331) B1626331
theorem B5478025 : Blo 854356 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B858143 : Blo 854356 858143 := bstep (se 1 (by rfl) ⟨643607, by rfl⟩ : syracuseStep 858143 = 1287215) B1287215
theorem B858223 : Blo 854356 858223 := bstep (se 1 (by rfl) ⟨643667, by rfl⟩ : syracuseStep 858223 = 1287335) B1287335
theorem B1284431 : Blo 854356 1284431 := bstep (se 1 (by rfl) ⟨963323, by rfl⟩ : syracuseStep 1284431 = 1926647) B1926647
theorem B1284455 : Blo 854356 1284455 := bstep (se 1 (by rfl) ⟨963341, by rfl⟩ : syracuseStep 1284455 = 1926683) B1926683
theorem B1284521 : Blo 854356 1284521 := bstep (se 2 (by rfl) ⟨481695, by rfl⟩ : syracuseStep 1284521 = 963391) B963391
theorem B3250793 : Blo 854356 3250793 := bstep (se 2 (by rfl) ⟨1219047, by rfl⟩ : syracuseStep 3250793 = 2438095) B2438095
theorem B1284905 : Blo 854356 1284905 := bstep (se 2 (by rfl) ⟨481839, by rfl⟩ : syracuseStep 1284905 = 963679) B963679
theorem B5479255 : Blo 854356 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B1285115 : Blo 854356 1285115 := bstep (se 1 (by rfl) ⟨963836, by rfl⟩ : syracuseStep 1285115 = 1927673) B1927673
theorem B1285151 : Blo 854356 1285151 := bstep (se 1 (by rfl) ⟨963863, by rfl⟩ : syracuseStep 1285151 = 1927727) B1927727
theorem B1285175 : Blo 854356 1285175 := bstep (se 1 (by rfl) ⟨963881, by rfl⟩ : syracuseStep 1285175 = 1927763) B1927763
theorem B1285295 : Blo 854356 1285295 := bstep (se 1 (by rfl) ⟨963971, by rfl⟩ : syracuseStep 1285295 = 1927943) B1927943
theorem B1285439 : Blo 854356 1285439 := bstep (se 1 (by rfl) ⟨964079, by rfl⟩ : syracuseStep 1285439 = 1928159) B1928159
theorem B26353039 : Blo 854356 26353039 := bstep (se 1 (by rfl) ⟨19764779, by rfl⟩ : syracuseStep 26353039 = 39529559) B39529559
theorem B1285583 : Blo 854356 1285583 := bstep (se 1 (by rfl) ⟨964187, by rfl⟩ : syracuseStep 1285583 = 1928375) B1928375
theorem B6168059 : Blo 854356 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B4333337 : Blo 854356 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B1285967 : Blo 854356 1285967 := bstep (se 1 (by rfl) ⟨964475, by rfl⟩ : syracuseStep 1285967 = 1928951) B1928951
theorem B1286015 : Blo 854356 1286015 := bstep (se 1 (by rfl) ⟨964511, by rfl⟩ : syracuseStep 1286015 = 1929023) B1929023
theorem B1286087 : Blo 854356 1286087 := bstep (se 1 (by rfl) ⟨964565, by rfl⟩ : syracuseStep 1286087 = 1929131) B1929131
theorem B12492785 : Blo 854356 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B1286327 : Blo 854356 1286327 := bstep (se 1 (by rfl) ⟨964745, by rfl⟩ : syracuseStep 1286327 = 1929491) B1929491
theorem B2171063 : Blo 854356 2171063 := bstep (se 1 (by rfl) ⟨1628297, by rfl⟩ : syracuseStep 2171063 = 3256595) B3256595
theorem B1286447 : Blo 854356 1286447 := bstep (se 1 (by rfl) ⟨964835, by rfl⟩ : syracuseStep 1286447 = 1929671) B1929671
theorem B1286687 : Blo 854356 1286687 := bstep (se 1 (by rfl) ⟨965015, by rfl⟩ : syracuseStep 1286687 = 1930031) B1930031
theorem B6496847 : Blo 854356 6496847 := bstep (se 1 (by rfl) ⟨4872635, by rfl⟩ : syracuseStep 6496847 = 9745271) B9745271
theorem B74981969 : Blo 854356 74981969 := bstep (se 2 (by rfl) ⟨28118238, by rfl⟩ : syracuseStep 74981969 = 56236477) B56236477
theorem B8036945 : Blo 854356 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B1286747 : Blo 854356 1286747 := bstep (se 1 (by rfl) ⟨965060, by rfl⟩ : syracuseStep 1286747 = 1930121) B1930121
theorem B2434121 : Blo 854356 2434121 := bstep (se 2 (by rfl) ⟨912795, by rfl⟩ : syracuseStep 2434121 = 1825591) B1825591
theorem B1287263 : Blo 854356 1287263 := bstep (se 1 (by rfl) ⟨965447, by rfl⟩ : syracuseStep 1287263 = 1930895) B1930895
theorem B1287323 : Blo 854356 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B2172217 : Blo 854356 2172217 := bstep (se 2 (by rfl) ⟨814581, by rfl⟩ : syracuseStep 2172217 = 1629163) B1629163
theorem B42772049 : Blo 854356 42772049 := bstep (se 2 (by rfl) ⟨16039518, by rfl⟩ : syracuseStep 42772049 = 32079037) B32079037
theorem B2172521 : Blo 854356 2172521 := bstep (se 2 (by rfl) ⟨814695, by rfl⟩ : syracuseStep 2172521 = 1629391) B1629391
theorem B7317155 : Blo 854356 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B2599145 : Blo 854356 2599145 := bstep (se 2 (by rfl) ⟨974679, by rfl⟩ : syracuseStep 2599145 = 1949359) B1949359
theorem B4336253 : Blo 854356 4336253 := bstep (se 3 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 4336253 = 1626095) B1626095
theorem B4697297 : Blo 854356 4697297 := bstep (se 2 (by rfl) ⟨1761486, by rfl⟩ : syracuseStep 4697297 = 3522973) B3522973
theorem B10988855 : Blo 854356 10988855 := bstep (se 1 (by rfl) ⟨8241641, by rfl⟩ : syracuseStep 10988855 = 16483283) B16483283
theorem B961951 : Blo 854356 961951 := bstep (se 1 (by rfl) ⟨721463, by rfl⟩ : syracuseStep 961951 = 1442927) B1442927
theorem B2895263 : Blo 854356 2895263 := bstep (se 1 (by rfl) ⟨2171447, by rfl⟩ : syracuseStep 2895263 = 4342895) B4342895
theorem B962239 : Blo 854356 962239 := bstep (se 1 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 962239 = 1443359) B1443359
theorem B2896019 : Blo 854356 2896019 := bstep (se 1 (by rfl) ⟨2172014, by rfl⟩ : syracuseStep 2896019 = 4344029) B4344029
theorem B962815 : Blo 854356 962815 := bstep (se 1 (by rfl) ⟨722111, by rfl⟩ : syracuseStep 962815 = 1444223) B1444223
theorem B4108751 : Blo 854356 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B7811599 : Blo 854356 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B2896559 : Blo 854356 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B2437867 : Blo 854356 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B4338683 : Blo 854356 4338683 := bstep (se 1 (by rfl) ⟨3254012, by rfl⟩ : syracuseStep 4338683 = 6508025) B6508025
theorem B963967 : Blo 854356 963967 := bstep (se 1 (by rfl) ⟨722975, by rfl⟩ : syracuseStep 963967 = 1445951) B1445951
theorem B4339169 : Blo 854356 4339169 := bstep (se 2 (by rfl) ⟨1627188, by rfl⟩ : syracuseStep 4339169 = 3254377) B3254377
theorem B3258251 : Blo 854356 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B964543 : Blo 854356 964543 := bstep (se 1 (by rfl) ⟨723407, by rfl⟩ : syracuseStep 964543 = 1446815) B1446815
theorem B14661647 : Blo 854356 14661647 := bstep (se 1 (by rfl) ⟨10996235, by rfl⟩ : syracuseStep 14661647 = 21992471) B21992471
theorem B5487047 : Blo 854356 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B2932139 : Blo 854356 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B22887947 : Blo 854356 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B5488175 : Blo 854356 5488175 := bstep (se 1 (by rfl) ⟨4116131, by rfl⟩ : syracuseStep 5488175 = 8232263) B8232263
theorem B2309705 : Blo 854356 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B2440955 : Blo 854356 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B9257753 : Blo 854356 9257753 := bstep (se 2 (by rfl) ⟨3471657, by rfl⟩ : syracuseStep 9257753 = 6943315) B6943315
theorem B2442287 : Blo 854356 2442287 := bstep (se 1 (by rfl) ⟨1831715, by rfl⟩ : syracuseStep 2442287 = 3663431) B3663431
theorem B2737259 : Blo 854356 2737259 := bstep (se 1 (by rfl) ⟨2052944, by rfl⟩ : syracuseStep 2737259 = 4105889) B4105889
theorem B6505595 : Blo 854356 6505595 := bstep (se 1 (by rfl) ⟨4879196, by rfl⟩ : syracuseStep 6505595 = 9758393) B9758393
theorem B35178137 : Blo 854356 35178137 := bstep (se 2 (by rfl) ⟨13191801, by rfl⟩ : syracuseStep 35178137 = 26383603) B26383603
theorem B13388267 : Blo 854356 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B2083321 : Blo 854356 2083321 := bstep (se 2 (by rfl) ⟨781245, by rfl⟩ : syracuseStep 2083321 = 1562491) B1562491
theorem B2345555 : Blo 854356 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B8243795 : Blo 854356 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B2443871 : Blo 854356 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B2313119 : Blo 854356 2313119 := bstep (se 1 (by rfl) ⟨1734839, by rfl⟩ : syracuseStep 2313119 = 3469679) B3469679
theorem B2444201 : Blo 854356 2444201 := bstep (se 2 (by rfl) ⟨916575, by rfl⟩ : syracuseStep 2444201 = 1833151) B1833151
theorem B7523485 : Blo 854356 7523485 := bstep (se 3 (by rfl) ⟨1410653, by rfl⟩ : syracuseStep 7523485 = 2821307) B2821307
theorem B2739577 : Blo 854356 2739577 := bstep (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) B2054683
theorem B2739719 : Blo 854356 2739719 := bstep (se 1 (by rfl) ⟨2054789, by rfl⟩ : syracuseStep 2739719 = 4109579) B4109579
theorem B4509857 : Blo 854356 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B1627447 : Blo 854356 1627447 := bstep (se 1 (by rfl) ⟨1220585, by rfl⟩ : syracuseStep 1627447 = 2441171) B2441171
theorem B2348713 : Blo 854356 2348713 := bstep (se 2 (by rfl) ⟨880767, by rfl⟩ : syracuseStep 2348713 = 1761535) B1761535
theorem B10409809 : Blo 854356 10409809 := bstep (se 2 (by rfl) ⟨3903678, by rfl⟩ : syracuseStep 10409809 = 7807357) B7807357
theorem B1923263 : Blo 854356 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B12343549 : Blo 854356 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B1628905 : Blo 854356 1628905 := bstep (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) B1221679
theorem B1629065 : Blo 854356 1629065 := bstep (se 2 (by rfl) ⟨610899, by rfl⟩ : syracuseStep 1629065 = 1221799) B1221799
theorem B1924307 : Blo 854356 1924307 := bstep (se 1 (by rfl) ⟨1443230, by rfl⟩ : syracuseStep 1924307 = 2886461) B2886461
theorem B1924379 : Blo 854356 1924379 := bstep (se 1 (by rfl) ⟨1443284, by rfl⟩ : syracuseStep 1924379 = 2886569) B2886569
theorem B5496173 : Blo 854356 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B1924577 : Blo 854356 1924577 := bstep (se 2 (by rfl) ⟨721716, by rfl⟩ : syracuseStep 1924577 = 1443433) B1443433
theorem B41606945 : Blo 854356 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B8773433 : Blo 854356 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B1925369 : Blo 854356 1925369 := bstep (se 2 (by rfl) ⟨722013, by rfl⟩ : syracuseStep 1925369 = 1444027) B1444027
theorem B1925639 : Blo 854356 1925639 := bstep (se 1 (by rfl) ⟨1444229, by rfl⟩ : syracuseStep 1925639 = 2888459) B2888459
theorem B1925819 : Blo 854356 1925819 := bstep (se 1 (by rfl) ⟨1444364, by rfl⟩ : syracuseStep 1925819 = 2888729) B2888729
theorem B1926305 : Blo 854356 1926305 := bstep (se 2 (by rfl) ⟨722364, by rfl⟩ : syracuseStep 1926305 = 1444729) B1444729
theorem B37119221 : Blo 854356 37119221 := bstep (se 5 (by rfl) ⟨1739963, by rfl⟩ : syracuseStep 37119221 = 3479927) B3479927
theorem B1926719 : Blo 854356 1926719 := bstep (se 1 (by rfl) ⟨1445039, by rfl⟩ : syracuseStep 1926719 = 2890079) B2890079
theorem B1926827 : Blo 854356 1926827 := bstep (se 1 (by rfl) ⟨1445120, by rfl⟩ : syracuseStep 1926827 = 2890241) B2890241
theorem B88991459 : Blo 854356 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B1927079 : Blo 854356 1927079 := bstep (se 1 (by rfl) ⟨1445309, by rfl⟩ : syracuseStep 1927079 = 2890619) B2890619
theorem B25061329 : Blo 854356 25061329 := bstep (se 2 (by rfl) ⟨9397998, by rfl⟩ : syracuseStep 25061329 = 18795997) B18795997
theorem B2746523 : Blo 854356 2746523 := bstep (se 1 (by rfl) ⟨2059892, by rfl⟩ : syracuseStep 2746523 = 4119785) B4119785
theorem B1927367 : Blo 854356 1927367 := bstep (se 1 (by rfl) ⟨1445525, by rfl⟩ : syracuseStep 1927367 = 2891051) B2891051
theorem B11725049 : Blo 854356 11725049 := bstep (se 2 (by rfl) ⟨4396893, by rfl⟩ : syracuseStep 11725049 = 8793787) B8793787
theorem B1927547 : Blo 854356 1927547 := bstep (se 1 (by rfl) ⟨1445660, by rfl⟩ : syracuseStep 1927547 = 2891321) B2891321
theorem B1927655 : Blo 854356 1927655 := bstep (se 1 (by rfl) ⟨1445741, by rfl⟩ : syracuseStep 1927655 = 2891483) B2891483
theorem B1927817 : Blo 854356 1927817 := bstep (se 2 (by rfl) ⟨722931, by rfl⟩ : syracuseStep 1927817 = 1445863) B1445863
theorem B1927835 : Blo 854356 1927835 := bstep (se 1 (by rfl) ⟨1445876, by rfl⟩ : syracuseStep 1927835 = 2891753) B2891753
theorem B3664865 : Blo 854356 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B1567855 : Blo 854356 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1928807 : Blo 854356 1928807 := bstep (se 1 (by rfl) ⟨1446605, by rfl⟩ : syracuseStep 1928807 = 2893211) B2893211
theorem B88797667 : Blo 854356 88797667 := bstep (se 1 (by rfl) ⟨66598250, by rfl⟩ : syracuseStep 88797667 = 133196501) B133196501
theorem B26702855 : Blo 854356 26702855 := bstep (se 1 (by rfl) ⟨20027141, by rfl⟩ : syracuseStep 26702855 = 40054283) B40054283
theorem B9270899 : Blo 854356 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B35092237 : Blo 854356 35092237 := bstep (se 3 (by rfl) ⟨6579794, by rfl⟩ : syracuseStep 35092237 = 13159589) B13159589
theorem B4388687 : Blo 854356 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B1931291 : Blo 854356 1931291 := bstep (se 1 (by rfl) ⟨1448468, by rfl⟩ : syracuseStep 1931291 = 2896937) B2896937
theorem B16447607 : Blo 854356 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B1374427 : Blo 854356 1374427 := bstep (se 1 (by rfl) ⟨1030820, by rfl⟩ : syracuseStep 1374427 = 2061641) B2061641
theorem B13892201 : Blo 854356 13892201 := bstep (se 2 (by rfl) ⟨5209575, by rfl⟩ : syracuseStep 13892201 = 10419151) B10419151
theorem B10583099 : Blo 854356 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B28572797 : Blo 854356 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B3080339 : Blo 854356 3080339 := bstep (se 1 (by rfl) ⟨2310254, by rfl⟩ : syracuseStep 3080339 = 4620509) B4620509
theorem B2162963 : Blo 854356 2162963 := bstep (se 1 (by rfl) ⟨1622222, by rfl⟩ : syracuseStep 2162963 = 3244445) B3244445
theorem B2883923 : Blo 854356 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B1442171 : Blo 854356 1442171 := bstep (se 1 (by rfl) ⟨1081628, by rfl⟩ : syracuseStep 1442171 = 2163257) B2163257
theorem B1542079 : Blo 854356 1542079 := bstep (se 1 (by rfl) ⟨1156559, by rfl⟩ : syracuseStep 1542079 = 2313119) B2313119
theorem B854375 : Blo 854356 854375 := bstep (se 1 (by rfl) ⟨640781, by rfl⟩ : syracuseStep 854375 = 1281563) B1281563
theorem B854463 : Blo 854356 854463 := bstep (se 1 (by rfl) ⟨640847, by rfl⟩ : syracuseStep 854463 = 1281695) B1281695
theorem B1444331 : Blo 854356 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B854639 : Blo 854356 854639 := bstep (se 1 (by rfl) ⟨640979, by rfl⟩ : syracuseStep 854639 = 1281959) B1281959
theorem B854655 : Blo 854356 854655 := bstep (se 1 (by rfl) ⟨640991, by rfl⟩ : syracuseStep 854655 = 1281983) B1281983
theorem B854759 : Blo 854356 854759 := bstep (se 1 (by rfl) ⟨641069, by rfl⟩ : syracuseStep 854759 = 1282139) B1282139
theorem B1444655 : Blo 854356 1444655 := bstep (se 1 (by rfl) ⟨1083491, by rfl⟩ : syracuseStep 1444655 = 2166983) B2166983
theorem B854855 : Blo 854356 854855 := bstep (se 1 (by rfl) ⟨641141, by rfl⟩ : syracuseStep 854855 = 1282283) B1282283
theorem B2165575 : Blo 854356 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B854895 : Blo 854356 854895 := bstep (se 1 (by rfl) ⟨641171, by rfl⟩ : syracuseStep 854895 = 1282343) B1282343
theorem B2886623 : Blo 854356 2886623 := bstep (se 1 (by rfl) ⟨2164967, by rfl⟩ : syracuseStep 2886623 = 4329935) B4329935
theorem B855071 : Blo 854356 855071 := bstep (se 1 (by rfl) ⟨641303, by rfl⟩ : syracuseStep 855071 = 1282607) B1282607
theorem B855207 : Blo 854356 855207 := bstep (se 1 (by rfl) ⟨641405, by rfl⟩ : syracuseStep 855207 = 1282811) B1282811
theorem B2886839 : Blo 854356 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B160501013 : Blo 854356 160501013 := bstep (se 6 (by rfl) ⟨3761742, by rfl⟩ : syracuseStep 160501013 = 7523485) B7523485
theorem B855455 : Blo 854356 855455 := bstep (se 1 (by rfl) ⟨641591, by rfl⟩ : syracuseStep 855455 = 1283183) B1283183
theorem B855503 : Blo 854356 855503 := bstep (se 1 (by rfl) ⟨641627, by rfl⟩ : syracuseStep 855503 = 1283255) B1283255
theorem B2166223 : Blo 854356 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B855663 : Blo 854356 855663 := bstep (se 1 (by rfl) ⟨641747, by rfl⟩ : syracuseStep 855663 = 1283495) B1283495
theorem B855783 : Blo 854356 855783 := bstep (se 1 (by rfl) ⟨641837, by rfl⟩ : syracuseStep 855783 = 1283675) B1283675
theorem B1445627 : Blo 854356 1445627 := bstep (se 1 (by rfl) ⟨1084220, by rfl⟩ : syracuseStep 1445627 = 2168441) B2168441
theorem B1282175 : Blo 854356 1282175 := bstep (se 1 (by rfl) ⟨961631, by rfl⟩ : syracuseStep 1282175 = 1923263) B1923263
theorem B856287 : Blo 854356 856287 := bstep (se 1 (by rfl) ⟨642215, by rfl⟩ : syracuseStep 856287 = 1284431) B1284431
theorem B856303 : Blo 854356 856303 := bstep (se 1 (by rfl) ⟨642227, by rfl⟩ : syracuseStep 856303 = 1284455) B1284455
theorem B856347 : Blo 854356 856347 := bstep (se 1 (by rfl) ⟨642260, by rfl⟩ : syracuseStep 856347 = 1284521) B1284521
theorem B2167195 : Blo 854356 2167195 := bstep (se 1 (by rfl) ⟨1625396, by rfl⟩ : syracuseStep 2167195 = 3250793) B3250793
theorem B856603 : Blo 854356 856603 := bstep (se 1 (by rfl) ⟨642452, by rfl⟩ : syracuseStep 856603 = 1284905) B1284905
theorem B1282601 : Blo 854356 1282601 := bstep (se 2 (by rfl) ⟨480975, by rfl⟩ : syracuseStep 1282601 = 961951) B961951
theorem B1086043 : Blo 854356 1086043 := bstep (se 1 (by rfl) ⟨814532, by rfl⟩ : syracuseStep 1086043 = 1629065) B1629065
theorem B856743 : Blo 854356 856743 := bstep (se 1 (by rfl) ⟨642557, by rfl⟩ : syracuseStep 856743 = 1285115) B1285115
theorem B856767 : Blo 854356 856767 := bstep (se 1 (by rfl) ⟨642575, by rfl⟩ : syracuseStep 856767 = 1285151) B1285151
theorem B856783 : Blo 854356 856783 := bstep (se 1 (by rfl) ⟨642587, by rfl⟩ : syracuseStep 856783 = 1285175) B1285175
theorem B856863 : Blo 854356 856863 := bstep (se 1 (by rfl) ⟨642647, by rfl⟩ : syracuseStep 856863 = 1285295) B1285295
theorem B1282871 : Blo 854356 1282871 := bstep (se 1 (by rfl) ⟨962153, by rfl⟩ : syracuseStep 1282871 = 1924307) B1924307
theorem B1282919 : Blo 854356 1282919 := bstep (se 1 (by rfl) ⟨962189, by rfl⟩ : syracuseStep 1282919 = 1924379) B1924379
theorem B856959 : Blo 854356 856959 := bstep (se 1 (by rfl) ⟨642719, by rfl⟩ : syracuseStep 856959 = 1285439) B1285439
theorem B1282985 : Blo 854356 1282985 := bstep (se 2 (by rfl) ⟨481119, by rfl⟩ : syracuseStep 1282985 = 962239) B962239
theorem B857055 : Blo 854356 857055 := bstep (se 1 (by rfl) ⟨642791, by rfl⟩ : syracuseStep 857055 = 1285583) B1285583
theorem B1283051 : Blo 854356 1283051 := bstep (se 1 (by rfl) ⟨962288, by rfl⟩ : syracuseStep 1283051 = 1924577) B1924577
theorem B2888891 : Blo 854356 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B857311 : Blo 854356 857311 := bstep (se 1 (by rfl) ⟨642983, by rfl⟩ : syracuseStep 857311 = 1285967) B1285967
theorem B857343 : Blo 854356 857343 := bstep (se 1 (by rfl) ⟨643007, by rfl⟩ : syracuseStep 857343 = 1286015) B1286015
theorem B857391 : Blo 854356 857391 := bstep (se 1 (by rfl) ⟨643043, by rfl⟩ : syracuseStep 857391 = 1286087) B1286087
theorem B857551 : Blo 854356 857551 := bstep (se 1 (by rfl) ⟨643163, by rfl⟩ : syracuseStep 857551 = 1286327) B1286327
theorem B1447375 : Blo 854356 1447375 := bstep (se 1 (by rfl) ⟨1085531, by rfl⟩ : syracuseStep 1447375 = 2171063) B2171063
theorem B1283579 : Blo 854356 1283579 := bstep (se 1 (by rfl) ⟨962684, by rfl⟩ : syracuseStep 1283579 = 1925369) B1925369
theorem B857631 : Blo 854356 857631 := bstep (se 1 (by rfl) ⟨643223, by rfl⟩ : syracuseStep 857631 = 1286447) B1286447
theorem B2889377 : Blo 854356 2889377 := bstep (se 2 (by rfl) ⟨1083516, by rfl⟩ : syracuseStep 2889377 = 2167033) B2167033
theorem B1283753 : Blo 854356 1283753 := bstep (se 2 (by rfl) ⟨481407, by rfl⟩ : syracuseStep 1283753 = 962815) B962815
theorem B1283759 : Blo 854356 1283759 := bstep (se 1 (by rfl) ⟨962819, by rfl⟩ : syracuseStep 1283759 = 1925639) B1925639
theorem B857791 : Blo 854356 857791 := bstep (se 1 (by rfl) ⟨643343, by rfl⟩ : syracuseStep 857791 = 1286687) B1286687
theorem B4331231 : Blo 854356 4331231 := bstep (se 1 (by rfl) ⟨3248423, by rfl⟩ : syracuseStep 4331231 = 6496847) B6496847
theorem B857831 : Blo 854356 857831 := bstep (se 1 (by rfl) ⟨643373, by rfl⟩ : syracuseStep 857831 = 1286747) B1286747
theorem B1283879 : Blo 854356 1283879 := bstep (se 1 (by rfl) ⟨962909, by rfl⟩ : syracuseStep 1283879 = 1925819) B1925819
theorem B118396889 : Blo 854356 118396889 := bstep (se 2 (by rfl) ⟨44398833, by rfl⟩ : syracuseStep 118396889 = 88797667) B88797667
theorem B858175 : Blo 854356 858175 := bstep (se 1 (by rfl) ⟨643631, by rfl⟩ : syracuseStep 858175 = 1287263) B1287263
theorem B858215 : Blo 854356 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B1284203 : Blo 854356 1284203 := bstep (se 1 (by rfl) ⟨963152, by rfl⟩ : syracuseStep 1284203 = 1926305) B1926305
theorem B24746147 : Blo 854356 24746147 := bstep (se 1 (by rfl) ⟨18559610, by rfl⟩ : syracuseStep 24746147 = 37119221) B37119221
theorem B3250489 : Blo 854356 3250489 := bstep (se 2 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 3250489 = 2437867) B2437867
theorem B1284479 : Blo 854356 1284479 := bstep (se 1 (by rfl) ⟨963359, by rfl⟩ : syracuseStep 1284479 = 1926719) B1926719
theorem B28514699 : Blo 854356 28514699 := bstep (se 1 (by rfl) ⟨21386024, by rfl⟩ : syracuseStep 28514699 = 42772049) B42772049
theorem B1448347 : Blo 854356 1448347 := bstep (se 1 (by rfl) ⟨1086260, by rfl⟩ : syracuseStep 1448347 = 2172521) B2172521
theorem B1284551 : Blo 854356 1284551 := bstep (se 1 (by rfl) ⟨963413, by rfl⟩ : syracuseStep 1284551 = 1926827) B1926827
theorem B1284719 : Blo 854356 1284719 := bstep (se 1 (by rfl) ⟨963539, by rfl⟩ : syracuseStep 1284719 = 1927079) B1927079
theorem B1284911 : Blo 854356 1284911 := bstep (se 1 (by rfl) ⟨963683, by rfl⟩ : syracuseStep 1284911 = 1927367) B1927367
theorem B1285031 : Blo 854356 1285031 := bstep (se 1 (by rfl) ⟨963773, by rfl⟩ : syracuseStep 1285031 = 1927547) B1927547
theorem B1285103 : Blo 854356 1285103 := bstep (se 1 (by rfl) ⟨963827, by rfl⟩ : syracuseStep 1285103 = 1927655) B1927655
theorem B2169929 : Blo 854356 2169929 := bstep (se 2 (by rfl) ⟨813723, by rfl⟩ : syracuseStep 2169929 = 1627447) B1627447
theorem B2890835 : Blo 854356 2890835 := bstep (se 1 (by rfl) ⟨2168126, by rfl⟩ : syracuseStep 2890835 = 4336253) B4336253
theorem B1285211 : Blo 854356 1285211 := bstep (se 1 (by rfl) ⟨963908, by rfl⟩ : syracuseStep 1285211 = 1927817) B1927817
theorem B1285223 : Blo 854356 1285223 := bstep (se 1 (by rfl) ⟨963917, by rfl⟩ : syracuseStep 1285223 = 1927835) B1927835
theorem B1285289 : Blo 854356 1285289 := bstep (se 2 (by rfl) ⟨481983, by rfl⟩ : syracuseStep 1285289 = 963967) B963967
theorem B1285871 : Blo 854356 1285871 := bstep (se 1 (by rfl) ⟨964403, by rfl⟩ : syracuseStep 1285871 = 1928807) B1928807
theorem B1286057 : Blo 854356 1286057 := bstep (se 2 (by rfl) ⟨482271, by rfl⟩ : syracuseStep 1286057 = 964543) B964543
theorem B9772973 : Blo 854356 9772973 := bstep (se 3 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 9772973 = 3664865) B3664865
theorem B16458065 : Blo 854356 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B2892455 : Blo 854356 2892455 := bstep (se 1 (by rfl) ⟨2169341, by rfl⟩ : syracuseStep 2892455 = 4338683) B4338683
theorem B17801903 : Blo 854356 17801903 := bstep (se 1 (by rfl) ⟨13351427, by rfl⟩ : syracuseStep 17801903 = 26702855) B26702855
theorem B2171873 : Blo 854356 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B2892779 : Blo 854356 2892779 := bstep (se 1 (by rfl) ⟨2169584, by rfl⟩ : syracuseStep 2892779 = 4339169) B4339169
theorem B2925791 : Blo 854356 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B2172167 : Blo 854356 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B9774431 : Blo 854356 9774431 := bstep (se 1 (by rfl) ⟨7330823, by rfl⟩ : syracuseStep 9774431 = 14661647) B14661647
theorem B1287527 : Blo 854356 1287527 := bstep (se 1 (by rfl) ⟨965645, by rfl⟩ : syracuseStep 1287527 = 1931291) B1931291
theorem B35137385 : Blo 854356 35137385 := bstep (se 2 (by rfl) ⟨13176519, by rfl⟩ : syracuseStep 35137385 = 26353039) B26353039
theorem B7055399 : Blo 854356 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B19048531 : Blo 854356 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B6171835 : Blo 854356 6171835 := bstep (se 1 (by rfl) ⟨4628876, by rfl⟩ : syracuseStep 6171835 = 9257753) B9257753
theorem B4337063 : Blo 854356 4337063 := bstep (se 1 (by rfl) ⟨3252797, by rfl⟩ : syracuseStep 4337063 = 6505595) B6505595
theorem B962203 : Blo 854356 962203 := bstep (se 1 (by rfl) ⟨721652, by rfl⟩ : syracuseStep 962203 = 1443305) B1443305
theorem B2896289 : Blo 854356 2896289 := bstep (se 2 (by rfl) ⟨1086108, by rfl⟩ : syracuseStep 2896289 = 2172217) B2172217
theorem B3650035 : Blo 854356 3650035 := bstep (se 1 (by rfl) ⟨2737526, by rfl⟩ : syracuseStep 3650035 = 5475053) B5475053
theorem B963355 : Blo 854356 963355 := bstep (se 1 (by rfl) ⟨722516, by rfl⟩ : syracuseStep 963355 = 1445033) B1445033
theorem B964831 : Blo 854356 964831 := bstep (se 1 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 964831 = 1447247) B1447247
theorem B67681025 : Blo 854356 67681025 := bstep (se 2 (by rfl) ⟨25380384, by rfl⟩ : syracuseStep 67681025 = 50760769) B50760769
theorem B3652769 : Blo 854356 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B4112039 : Blo 854356 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B27737963 : Blo 854356 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B5848955 : Blo 854356 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B49987979 : Blo 854356 49987979 := bstep (se 1 (by rfl) ⟨37490984, by rfl⟩ : syracuseStep 49987979 = 74981969) B74981969
theorem B5357963 : Blo 854356 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B1622747 : Blo 854356 1622747 := bstep (se 1 (by rfl) ⟨1217060, by rfl⟩ : syracuseStep 1622747 = 2434121) B2434121
theorem B59327639 : Blo 854356 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B35702045 : Blo 854356 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B7816699 : Blo 854356 7816699 := bstep (se 1 (by rfl) ⟨5862524, by rfl⟩ : syracuseStep 7816699 = 11725049) B11725049
theorem B3131531 : Blo 854356 3131531 := bstep (se 1 (by rfl) ⟨2348648, by rfl⟩ : syracuseStep 3131531 = 4697297) B4697297
theorem B7325903 : Blo 854356 7325903 := bstep (se 1 (by rfl) ⟨5494427, by rfl⟩ : syracuseStep 7325903 = 10988855) B10988855
theorem B3131617 : Blo 854356 3131617 := bstep (se 2 (by rfl) ⟨1174356, by rfl⟩ : syracuseStep 3131617 = 2348713) B2348713
theorem B13879745 : Blo 854356 13879745 := bstep (se 2 (by rfl) ⟨5204904, by rfl⟩ : syracuseStep 13879745 = 10409809) B10409809
theorem B2739167 : Blo 854356 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B6180599 : Blo 854356 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B10965071 : Blo 854356 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B3658031 : Blo 854356 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B9261467 : Blo 854356 9261467 := bstep (se 1 (by rfl) ⟨6946100, by rfl⟩ : syracuseStep 9261467 = 13892201) B13892201
theorem B1954759 : Blo 854356 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B15258631 : Blo 854356 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B3658783 : Blo 854356 3658783 := bstep (se 1 (by rfl) ⟨2744087, by rfl⟩ : syracuseStep 3658783 = 5488175) B5488175
theorem B1627303 : Blo 854356 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B33314093 : Blo 854356 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B1922471 : Blo 854356 1922471 := bstep (se 1 (by rfl) ⟨1441853, by rfl⟩ : syracuseStep 1922471 = 2883707) B2883707
theorem B1628191 : Blo 854356 1628191 := bstep (se 1 (by rfl) ⟨1221143, by rfl⟩ : syracuseStep 1628191 = 2442287) B2442287
theorem B1824839 : Blo 854356 1824839 := bstep (se 1 (by rfl) ⟨1368629, by rfl⟩ : syracuseStep 1824839 = 2737259) B2737259
theorem B1923497 : Blo 854356 1923497 := bstep (se 2 (by rfl) ⟨721311, by rfl⟩ : syracuseStep 1923497 = 1442623) B1442623
theorem B23452091 : Blo 854356 23452091 := bstep (se 1 (by rfl) ⟨17589068, by rfl⟩ : syracuseStep 23452091 = 35178137) B35178137
theorem B7330277 : Blo 854356 7330277 := bstep (se 4 (by rfl) ⟨687213, by rfl⟩ : syracuseStep 7330277 = 1374427) B1374427
theorem B2316883 : Blo 854356 2316883 := bstep (se 1 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 2316883 = 3475325) B3475325
theorem B7428871 : Blo 854356 7428871 := bstep (se 1 (by rfl) ⟨5571653, by rfl⟩ : syracuseStep 7428871 = 11143307) B11143307
theorem B5495863 : Blo 854356 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B1629247 : Blo 854356 1629247 := bstep (se 1 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 1629247 = 2443871) B2443871
theorem B1629467 : Blo 854356 1629467 := bstep (se 1 (by rfl) ⟨1222100, by rfl⟩ : syracuseStep 1629467 = 2444201) B2444201
theorem B1826479 : Blo 854356 1826479 := bstep (se 1 (by rfl) ⟨1369859, by rfl⟩ : syracuseStep 1826479 = 2739719) B2739719
theorem B1924847 : Blo 854356 1924847 := bstep (se 1 (by rfl) ⟨1443635, by rfl⟩ : syracuseStep 1924847 = 2887271) B2887271
theorem B33415105 : Blo 854356 33415105 := bstep (se 2 (by rfl) ⟨12530664, by rfl⟩ : syracuseStep 33415105 = 25061329) B25061329
theorem B3006571 : Blo 854356 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B21913739 : Blo 854356 21913739 := bstep (se 1 (by rfl) ⟨16435304, by rfl⟩ : syracuseStep 21913739 = 32870609) B32870609
theorem B1925459 : Blo 854356 1925459 := bstep (se 1 (by rfl) ⟨1444094, by rfl⟩ : syracuseStep 1925459 = 2888189) B2888189
theorem B2777761 : Blo 854356 2777761 := bstep (se 2 (by rfl) ⟨1041660, by rfl⟩ : syracuseStep 2777761 = 2083321) B2083321
theorem B6513371 : Blo 854356 6513371 := bstep (se 1 (by rfl) ⟨4885028, by rfl⟩ : syracuseStep 6513371 = 9770057) B9770057
theorem B2319131 : Blo 854356 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B2090473 : Blo 854356 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B3664115 : Blo 854356 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B1928105 : Blo 854356 1928105 := bstep (se 2 (by rfl) ⟨723039, by rfl⟩ : syracuseStep 1928105 = 1446079) B1446079
theorem B10415465 : Blo 854356 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B4878103 : Blo 854356 4878103 := bstep (se 1 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 4878103 = 7317155) B7317155
theorem B1831015 : Blo 854356 1831015 := bstep (se 1 (by rfl) ⟨1373261, by rfl⟩ : syracuseStep 1831015 = 2746523) B2746523
theorem B1732763 : Blo 854356 1732763 := bstep (se 1 (by rfl) ⟨1299572, by rfl⟩ : syracuseStep 1732763 = 2599145) B2599145
theorem B6254813 : Blo 854356 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B7304033 : Blo 854356 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B1930175 : Blo 854356 1930175 := bstep (se 1 (by rfl) ⟨1447631, by rfl⟩ : syracuseStep 1930175 = 2895263) B2895263
theorem B46789649 : Blo 854356 46789649 := bstep (se 2 (by rfl) ⟨17546118, by rfl⟩ : syracuseStep 46789649 = 35092237) B35092237
theorem B1930679 : Blo 854356 1930679 := bstep (se 1 (by rfl) ⟨1448009, by rfl⟩ : syracuseStep 1930679 = 2896019) B2896019
theorem B1931039 : Blo 854356 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B7305673 : Blo 854356 7305673 := bstep (se 2 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 7305673 = 5479255) B5479255
theorem B1539803 : Blo 854356 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B1441975 : Blo 854356 1441975 := bstep (se 1 (by rfl) ⟨1081481, by rfl⟩ : syracuseStep 1441975 = 2162963) B2162963
theorem B33325319 : Blo 854356 33325319 := bstep (se 1 (by rfl) ⟨24993989, by rfl⟩ : syracuseStep 33325319 = 49987979) B49987979
theorem B3571975 : Blo 854356 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B4620701 : Blo 854356 4620701 := bstep (se 3 (by rfl) ⟨866381, by rfl⟩ : syracuseStep 4620701 = 1732763) B1732763
theorem B1081831 : Blo 854356 1081831 := bstep (se 1 (by rfl) ⟨811373, by rfl⟩ : syracuseStep 1081831 = 1622747) B1622747
theorem B39551759 : Blo 854356 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B3703681 : Blo 854356 3703681 := bstep (se 2 (by rfl) ⟨1388880, by rfl⟩ : syracuseStep 3703681 = 2777761) B2777761
theorem B4883935 : Blo 854356 4883935 := bstep (se 1 (by rfl) ⟨3662951, by rfl⟩ : syracuseStep 4883935 = 7325903) B7325903
theorem B10422265 : Blo 854356 10422265 := bstep (se 2 (by rfl) ⟨3908349, by rfl⟩ : syracuseStep 10422265 = 7816699) B7816699
theorem B7310047 : Blo 854356 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B854783 : Blo 854356 854783 := bstep (se 1 (by rfl) ⟨641087, by rfl⟩ : syracuseStep 854783 = 1282175) B1282175
theorem B25398041 : Blo 854356 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B855067 : Blo 854356 855067 := bstep (se 1 (by rfl) ⟨641300, by rfl⟩ : syracuseStep 855067 = 1282601) B1282601
theorem B855247 : Blo 854356 855247 := bstep (se 1 (by rfl) ⟨641435, by rfl⟩ : syracuseStep 855247 = 1282871) B1282871
theorem B855279 : Blo 854356 855279 := bstep (se 1 (by rfl) ⟨641459, by rfl⟩ : syracuseStep 855279 = 1282919) B1282919
theorem B855323 : Blo 854356 855323 := bstep (se 1 (by rfl) ⟨641492, by rfl⟩ : syracuseStep 855323 = 1282985) B1282985
theorem B855367 : Blo 854356 855367 := bstep (se 1 (by rfl) ⟨641525, by rfl⟩ : syracuseStep 855367 = 1283051) B1283051
theorem B1281647 : Blo 854356 1281647 := bstep (se 1 (by rfl) ⟨961235, by rfl⟩ : syracuseStep 1281647 = 1922471) B1922471
theorem B855719 : Blo 854356 855719 := bstep (se 1 (by rfl) ⟨641789, by rfl⟩ : syracuseStep 855719 = 1283579) B1283579
theorem B2887433 : Blo 854356 2887433 := bstep (se 2 (by rfl) ⟨1082787, by rfl⟩ : syracuseStep 2887433 = 2165575) B2165575
theorem B855835 : Blo 854356 855835 := bstep (se 1 (by rfl) ⟨641876, by rfl⟩ : syracuseStep 855835 = 1283753) B1283753
theorem B855839 : Blo 854356 855839 := bstep (se 1 (by rfl) ⟨641879, by rfl⟩ : syracuseStep 855839 = 1283759) B1283759
theorem B2887487 : Blo 854356 2887487 := bstep (se 1 (by rfl) ⟨2165615, by rfl⟩ : syracuseStep 2887487 = 4331231) B4331231
theorem B855919 : Blo 854356 855919 := bstep (se 1 (by rfl) ⟨641939, by rfl⟩ : syracuseStep 855919 = 1283879) B1283879
theorem B1216559 : Blo 854356 1216559 := bstep (se 1 (by rfl) ⟨912419, by rfl⟩ : syracuseStep 1216559 = 1824839) B1824839
theorem B856135 : Blo 854356 856135 := bstep (se 1 (by rfl) ⟨642101, by rfl⟩ : syracuseStep 856135 = 1284203) B1284203
theorem B8229113 : Blo 854356 8229113 := bstep (se 2 (by rfl) ⟨3085917, by rfl⟩ : syracuseStep 8229113 = 6171835) B6171835
theorem B856319 : Blo 854356 856319 := bstep (se 1 (by rfl) ⟨642239, by rfl⟩ : syracuseStep 856319 = 1284479) B1284479
theorem B19009799 : Blo 854356 19009799 := bstep (se 1 (by rfl) ⟨14257349, by rfl⟩ : syracuseStep 19009799 = 28514699) B28514699
theorem B1282331 : Blo 854356 1282331 := bstep (se 1 (by rfl) ⟨961748, by rfl⟩ : syracuseStep 1282331 = 1923497) B1923497
theorem B15634727 : Blo 854356 15634727 := bstep (se 1 (by rfl) ⟨11726045, by rfl⟩ : syracuseStep 15634727 = 23452091) B23452091
theorem B856367 : Blo 854356 856367 := bstep (se 1 (by rfl) ⟨642275, by rfl⟩ : syracuseStep 856367 = 1284551) B1284551
theorem B4886851 : Blo 854356 4886851 := bstep (se 1 (by rfl) ⟨3665138, by rfl⟩ : syracuseStep 4886851 = 7330277) B7330277
theorem B856479 : Blo 854356 856479 := bstep (se 1 (by rfl) ⟨642359, by rfl⟩ : syracuseStep 856479 = 1284719) B1284719
theorem B856607 : Blo 854356 856607 := bstep (se 1 (by rfl) ⟨642455, by rfl⟩ : syracuseStep 856607 = 1284911) B1284911
theorem B2888297 : Blo 854356 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B856687 : Blo 854356 856687 := bstep (se 1 (by rfl) ⟨642515, by rfl⟩ : syracuseStep 856687 = 1285031) B1285031
theorem B856735 : Blo 854356 856735 := bstep (se 1 (by rfl) ⟨642551, by rfl⟩ : syracuseStep 856735 = 1285103) B1285103
theorem B1446619 : Blo 854356 1446619 := bstep (se 1 (by rfl) ⟨1084964, by rfl⟩ : syracuseStep 1446619 = 2169929) B2169929
theorem B856807 : Blo 854356 856807 := bstep (se 1 (by rfl) ⟨642605, by rfl⟩ : syracuseStep 856807 = 1285211) B1285211
theorem B856815 : Blo 854356 856815 := bstep (se 1 (by rfl) ⟨642611, by rfl⟩ : syracuseStep 856815 = 1285223) B1285223
theorem B856859 : Blo 854356 856859 := bstep (se 1 (by rfl) ⟨642644, by rfl⟩ : syracuseStep 856859 = 1285289) B1285289
theorem B1086311 : Blo 854356 1086311 := bstep (se 1 (by rfl) ⟨814733, by rfl⟩ : syracuseStep 1086311 = 1629467) B1629467
theorem B1282937 : Blo 854356 1282937 := bstep (se 2 (by rfl) ⟨481101, by rfl⟩ : syracuseStep 1282937 = 962203) B962203
theorem B1283231 : Blo 854356 1283231 := bstep (se 1 (by rfl) ⟨962423, by rfl⟩ : syracuseStep 1283231 = 1924847) B1924847
theorem B857247 : Blo 854356 857247 := bstep (se 1 (by rfl) ⟨642935, by rfl⟩ : syracuseStep 857247 = 1285871) B1285871
theorem B857371 : Blo 854356 857371 := bstep (se 1 (by rfl) ⟨643028, by rfl⟩ : syracuseStep 857371 = 1286057) B1286057
theorem B1283639 : Blo 854356 1283639 := bstep (se 1 (by rfl) ⟨962729, by rfl⟩ : syracuseStep 1283639 = 1925459) B1925459
theorem B2889593 : Blo 854356 2889593 := bstep (se 2 (by rfl) ⟨1083597, by rfl⟩ : syracuseStep 2889593 = 2167195) B2167195
theorem B1447915 : Blo 854356 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B1448057 : Blo 854356 1448057 := bstep (se 2 (by rfl) ⟨543021, by rfl⟩ : syracuseStep 1448057 = 1086043) B1086043
theorem B1448111 : Blo 854356 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B858351 : Blo 854356 858351 := bstep (se 1 (by rfl) ⟨643763, by rfl⟩ : syracuseStep 858351 = 1287527) B1287527
theorem B1284473 : Blo 854356 1284473 := bstep (se 2 (by rfl) ⟨481677, by rfl⟩ : syracuseStep 1284473 = 963355) B963355
theorem B2169737 : Blo 854356 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B1285403 : Blo 854356 1285403 := bstep (se 1 (by rfl) ⟨964052, by rfl⟩ : syracuseStep 1285403 = 1928105) B1928105
theorem B2891375 : Blo 854356 2891375 := bstep (se 1 (by rfl) ⟨2168531, by rfl⟩ : syracuseStep 2891375 = 4337063) B4337063
theorem B2170921 : Blo 854356 2170921 := bstep (se 2 (by rfl) ⟨814095, by rfl⟩ : syracuseStep 2170921 = 1628191) B1628191
theorem B4169875 : Blo 854356 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B1286441 : Blo 854356 1286441 := bstep (se 2 (by rfl) ⟨482415, by rfl⟩ : syracuseStep 1286441 = 964831) B964831
theorem B4333985 : Blo 854356 4333985 := bstep (se 2 (by rfl) ⟨1625244, by rfl⟩ : syracuseStep 4333985 = 3250489) B3250489
theorem B9740897 : Blo 854356 9740897 := bstep (se 2 (by rfl) ⟨3652836, by rfl⟩ : syracuseStep 9740897 = 7305673) B7305673
theorem B1286783 : Blo 854356 1286783 := bstep (se 1 (by rfl) ⟨965087, by rfl⟩ : syracuseStep 1286783 = 1930175) B1930175
theorem B3089177 : Blo 854356 3089177 := bstep (se 2 (by rfl) ⟨1158441, by rfl⟩ : syracuseStep 3089177 = 2316883) B2316883
theorem B1287119 : Blo 854356 1287119 := bstep (se 1 (by rfl) ⟨965339, by rfl⟩ : syracuseStep 1287119 = 1930679) B1930679
theorem B9905161 : Blo 854356 9905161 := bstep (se 2 (by rfl) ⟨3714435, by rfl⟩ : syracuseStep 9905161 = 7428871) B7428871
theorem B1287359 : Blo 854356 1287359 := bstep (se 1 (by rfl) ⟨965519, by rfl⟩ : syracuseStep 1287359 = 1931039) B1931039
theorem B2172329 : Blo 854356 2172329 := bstep (se 2 (by rfl) ⟨814623, by rfl⟩ : syracuseStep 2172329 = 1629247) B1629247
theorem B2435179 : Blo 854356 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B2435305 : Blo 854356 2435305 := bstep (se 2 (by rfl) ⟨913239, by rfl⟩ : syracuseStep 2435305 = 1826479) B1826479
theorem B1026535 : Blo 854356 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B18491975 : Blo 854356 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B4008761 : Blo 854356 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B961447 : Blo 854356 961447 := bstep (se 1 (by rfl) ⟨721085, by rfl⟩ : syracuseStep 961447 = 1442171) B1442171
theorem B23801363 : Blo 854356 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B9253163 : Blo 854356 9253163 := bstep (se 1 (by rfl) ⟨6939872, by rfl⟩ : syracuseStep 9253163 = 13879745) B13879745
theorem B962887 : Blo 854356 962887 := bstep (se 1 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 962887 = 1444331) B1444331
theorem B963103 : Blo 854356 963103 := bstep (se 1 (by rfl) ⟨722327, by rfl⟩ : syracuseStep 963103 = 1444655) B1444655
theorem B107000675 : Blo 854356 107000675 := bstep (se 1 (by rfl) ⟨80250506, by rfl⟩ : syracuseStep 107000675 = 160501013) B160501013
theorem B963751 : Blo 854356 963751 := bstep (se 1 (by rfl) ⟨722813, by rfl⟩ : syracuseStep 963751 = 1445627) B1445627
theorem B2438687 : Blo 854356 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B6174311 : Blo 854356 6174311 := bstep (se 1 (by rfl) ⟨4630733, by rfl⟩ : syracuseStep 6174311 = 9261467) B9261467
theorem B4175489 : Blo 854356 4175489 := bstep (se 2 (by rfl) ⟨1565808, by rfl⟩ : syracuseStep 4175489 = 3131617) B3131617
theorem B16497431 : Blo 854356 16497431 := bstep (se 1 (by rfl) ⟨12373073, by rfl⟩ : syracuseStep 16497431 = 24746147) B24746147
theorem B6504137 : Blo 854356 6504137 := bstep (se 2 (by rfl) ⟨2439051, by rfl⟩ : syracuseStep 6504137 = 4878103) B4878103
theorem B2441353 : Blo 854356 2441353 := bstep (se 2 (by rfl) ⟨915507, by rfl⟩ : syracuseStep 2441353 = 1831015) B1831015
theorem B4342247 : Blo 854356 4342247 := bstep (se 1 (by rfl) ⟨3256685, by rfl⟩ : syracuseStep 4342247 = 6513371) B6513371
theorem B4866713 : Blo 854356 4866713 := bstep (se 2 (by rfl) ⟨1825017, by rfl⟩ : syracuseStep 4866713 = 3650035) B3650035
theorem B1950527 : Blo 854356 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B2606345 : Blo 854356 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B4703599 : Blo 854356 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B2442743 : Blo 854356 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B4869355 : Blo 854356 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B7327817 : Blo 854356 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B2741359 : Blo 854356 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B44553473 : Blo 854356 44553473 := bstep (se 2 (by rfl) ⟨16707552, by rfl⟩ : syracuseStep 44553473 = 33415105) B33415105
theorem B2053559 : Blo 854356 2053559 := bstep (se 1 (by rfl) ⟨1540169, by rfl⟩ : syracuseStep 2053559 = 3080339) B3080339
theorem B1922615 : Blo 854356 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B2087687 : Blo 854356 2087687 := bstep (se 1 (by rfl) ⟨1565765, by rfl⟩ : syracuseStep 2087687 = 3131531) B3131531
theorem B47471741 : Blo 854356 47471741 := bstep (se 3 (by rfl) ⟨8900951, by rfl⟩ : syracuseStep 47471741 = 17801903) B17801903
theorem B1826111 : Blo 854356 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B1924415 : Blo 854356 1924415 := bstep (se 1 (by rfl) ⟨1443311, by rfl⟩ : syracuseStep 1924415 = 2886623) B2886623
theorem B6184349 : Blo 854356 6184349 := bstep (se 3 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 6184349 = 2319131) B2319131
theorem B1924559 : Blo 854356 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B4120399 : Blo 854356 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B2056105 : Blo 854356 2056105 := bstep (se 2 (by rfl) ⟨771039, by rfl⟩ : syracuseStep 2056105 = 1542079) B1542079
theorem B1925927 : Blo 854356 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B22209395 : Blo 854356 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B1926251 : Blo 854356 1926251 := bstep (se 1 (by rfl) ⟨1444688, by rfl⟩ : syracuseStep 1926251 = 2889377) B2889377
theorem B78931259 : Blo 854356 78931259 := bstep (se 1 (by rfl) ⟨59198444, by rfl⟩ : syracuseStep 78931259 = 118396889) B118396889
theorem B1927223 : Blo 854356 1927223 := bstep (se 1 (by rfl) ⟨1445417, by rfl⟩ : syracuseStep 1927223 = 2890835) B2890835
theorem B6515315 : Blo 854356 6515315 := bstep (se 1 (by rfl) ⟨4886486, by rfl⟩ : syracuseStep 6515315 = 9772973) B9772973
theorem B14609159 : Blo 854356 14609159 := bstep (se 1 (by rfl) ⟨10956869, by rfl⟩ : syracuseStep 14609159 = 21913739) B21913739
theorem B10972043 : Blo 854356 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B1928303 : Blo 854356 1928303 := bstep (se 1 (by rfl) ⟨1446227, by rfl⟩ : syracuseStep 1928303 = 2892455) B2892455
theorem B1928519 : Blo 854356 1928519 := bstep (se 1 (by rfl) ⟨1446389, by rfl⟩ : syracuseStep 1928519 = 2892779) B2892779
theorem B6516287 : Blo 854356 6516287 := bstep (se 1 (by rfl) ⟨4887215, by rfl⟩ : syracuseStep 6516287 = 9774431) B9774431
theorem B23424923 : Blo 854356 23424923 := bstep (se 1 (by rfl) ⟨17568692, by rfl⟩ : syracuseStep 23424923 = 35137385) B35137385
theorem B20344841 : Blo 854356 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B4878377 : Blo 854356 4878377 := bstep (se 2 (by rfl) ⟨1829391, by rfl⟩ : syracuseStep 4878377 = 3658783) B3658783
theorem B1929833 : Blo 854356 1929833 := bstep (se 2 (by rfl) ⟨723687, by rfl⟩ : syracuseStep 1929833 = 1447375) B1447375
theorem B6943643 : Blo 854356 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B1930859 : Blo 854356 1930859 := bstep (se 1 (by rfl) ⟨1448144, by rfl⟩ : syracuseStep 1930859 = 2896289) B2896289
theorem B1931129 : Blo 854356 1931129 := bstep (se 2 (by rfl) ⟨724173, by rfl⟩ : syracuseStep 1931129 = 1448347) B1448347
theorem B31193099 : Blo 854356 31193099 := bstep (se 1 (by rfl) ⟨23394824, by rfl⟩ : syracuseStep 31193099 = 46789649) B46789649
theorem B45120683 : Blo 854356 45120683 := bstep (se 1 (by rfl) ⟨33840512, by rfl⟩ : syracuseStep 45120683 = 67681025) B67681025
theorem B44596757 : Blo 854356 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B3899303 : Blo 854356 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B3244157 : Blo 854356 3244157 := bstep (se 3 (by rfl) ⟨608279, by rfl⟩ : syracuseStep 3244157 = 1216559) B1216559
theorem B22216879 : Blo 854356 22216879 := bstep (se 1 (by rfl) ⟨16662659, by rfl⟩ : syracuseStep 22216879 = 33325319) B33325319
theorem B3080467 : Blo 854356 3080467 := bstep (se 1 (by rfl) ⟨2310350, by rfl⟩ : syracuseStep 3080467 = 4620701) B4620701
theorem B3244475 : Blo 854356 3244475 := bstep (se 1 (by rfl) ⟨2433356, by rfl⟩ : syracuseStep 3244475 = 4866713) B4866713
theorem B1442441 : Blo 854356 1442441 := bstep (se 2 (by rfl) ⟨540915, by rfl⟩ : syracuseStep 1442441 = 1081831) B1081831
theorem B24675101 : Blo 854356 24675101 := bstep (se 3 (by rfl) ⟨4626581, by rfl⟩ : syracuseStep 24675101 = 9253163) B9253163
theorem B1737563 : Blo 854356 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B13206881 : Blo 854356 13206881 := bstep (se 2 (by rfl) ⟨4952580, by rfl⟩ : syracuseStep 13206881 = 9905161) B9905161
theorem B854431 : Blo 854356 854431 := bstep (se 1 (by rfl) ⟨640823, by rfl⟩ : syracuseStep 854431 = 1281647) B1281647
theorem B13896353 : Blo 854356 13896353 := bstep (se 2 (by rfl) ⟨5211132, by rfl⟩ : syracuseStep 13896353 = 10422265) B10422265
theorem B4885211 : Blo 854356 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B3246905 : Blo 854356 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B854887 : Blo 854356 854887 := bstep (se 1 (by rfl) ⟨641165, by rfl⟩ : syracuseStep 854887 = 1282331) B1282331
theorem B10423151 : Blo 854356 10423151 := bstep (se 1 (by rfl) ⟨7817363, by rfl⟩ : syracuseStep 10423151 = 15634727) B15634727
theorem B3247073 : Blo 854356 3247073 := bstep (se 2 (by rfl) ⟨1217652, by rfl⟩ : syracuseStep 3247073 = 2435305) B2435305
theorem B855291 : Blo 854356 855291 := bstep (se 1 (by rfl) ⟨641468, by rfl⟩ : syracuseStep 855291 = 1282937) B1282937
theorem B855487 : Blo 854356 855487 := bstep (se 1 (by rfl) ⟨641615, by rfl⟩ : syracuseStep 855487 = 1283231) B1283231
theorem B1281743 : Blo 854356 1281743 := bstep (se 1 (by rfl) ⟨961307, by rfl⟩ : syracuseStep 1281743 = 1922615) B1922615
theorem B855759 : Blo 854356 855759 := bstep (se 1 (by rfl) ⟨641819, by rfl⟩ : syracuseStep 855759 = 1283639) B1283639
theorem B5476157 : Blo 854356 5476157 := bstep (se 3 (by rfl) ⟨1026779, by rfl⟩ : syracuseStep 5476157 = 2053559) B2053559
theorem B1281929 : Blo 854356 1281929 := bstep (se 2 (by rfl) ⟨480723, by rfl⟩ : syracuseStep 1281929 = 961447) B961447
theorem B856315 : Blo 854356 856315 := bstep (se 1 (by rfl) ⟨642236, by rfl⟩ : syracuseStep 856315 = 1284473) B1284473
theorem B6492473 : Blo 854356 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B1446491 : Blo 854356 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B856935 : Blo 854356 856935 := bstep (se 1 (by rfl) ⟨642701, by rfl⟩ : syracuseStep 856935 = 1285403) B1285403
theorem B1282943 : Blo 854356 1282943 := bstep (se 1 (by rfl) ⟨962207, by rfl⟩ : syracuseStep 1282943 = 1924415) B1924415
theorem B1283039 : Blo 854356 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B857627 : Blo 854356 857627 := bstep (se 1 (by rfl) ⟨643220, by rfl⟩ : syracuseStep 857627 = 1286441) B1286441
theorem B2889323 : Blo 854356 2889323 := bstep (se 1 (by rfl) ⟨2166992, by rfl⟩ : syracuseStep 2889323 = 4333985) B4333985
theorem B6493931 : Blo 854356 6493931 := bstep (se 1 (by rfl) ⟨4870448, by rfl⟩ : syracuseStep 6493931 = 9740897) B9740897
theorem B857855 : Blo 854356 857855 := bstep (se 1 (by rfl) ⟨643391, by rfl⟩ : syracuseStep 857855 = 1286783) B1286783
theorem B1283849 : Blo 854356 1283849 := bstep (se 2 (by rfl) ⟨481443, by rfl⟩ : syracuseStep 1283849 = 962887) B962887
theorem B1283951 : Blo 854356 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B858079 : Blo 854356 858079 := bstep (se 1 (by rfl) ⟨643559, by rfl⟩ : syracuseStep 858079 = 1287119) B1287119
theorem B1284137 : Blo 854356 1284137 := bstep (se 2 (by rfl) ⟨481551, by rfl⟩ : syracuseStep 1284137 = 963103) B963103
theorem B1284167 : Blo 854356 1284167 := bstep (se 1 (by rfl) ⟨963125, by rfl⟩ : syracuseStep 1284167 = 1926251) B1926251
theorem B858239 : Blo 854356 858239 := bstep (se 1 (by rfl) ⟨643679, by rfl⟩ : syracuseStep 858239 = 1287359) B1287359
theorem B1448219 : Blo 854356 1448219 := bstep (se 1 (by rfl) ⟨1086164, by rfl⟩ : syracuseStep 1448219 = 2172329) B2172329
theorem B1284815 : Blo 854356 1284815 := bstep (se 1 (by rfl) ⟨963611, by rfl⟩ : syracuseStep 1284815 = 1927223) B1927223
theorem B1285001 : Blo 854356 1285001 := bstep (se 2 (by rfl) ⟨481875, by rfl⟩ : syracuseStep 1285001 = 963751) B963751
theorem B12327983 : Blo 854356 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B9739439 : Blo 854356 9739439 := bstep (se 1 (by rfl) ⟨7304579, by rfl⟩ : syracuseStep 9739439 = 14609159) B14609159
theorem B7314695 : Blo 854356 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B1285535 : Blo 854356 1285535 := bstep (se 1 (by rfl) ⟨964151, by rfl⟩ : syracuseStep 1285535 = 1928303) B1928303
theorem B1285679 : Blo 854356 1285679 := bstep (se 1 (by rfl) ⟨964259, by rfl⟩ : syracuseStep 1285679 = 1928519) B1928519
theorem B15867575 : Blo 854356 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B3252251 : Blo 854356 3252251 := bstep (se 1 (by rfl) ⟨2439188, by rfl⟩ : syracuseStep 3252251 = 4878377) B4878377
theorem B1286555 : Blo 854356 1286555 := bstep (se 1 (by rfl) ⟨964916, by rfl⟩ : syracuseStep 1286555 = 1929833) B1929833
theorem B4629095 : Blo 854356 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B1287239 : Blo 854356 1287239 := bstep (se 1 (by rfl) ⟨965429, by rfl⟩ : syracuseStep 1287239 = 1930859) B1930859
theorem B1287419 : Blo 854356 1287419 := bstep (se 1 (by rfl) ⟨965564, by rfl⟩ : syracuseStep 1287419 = 1931129) B1931129
theorem B29731171 : Blo 854356 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B62466461 : Blo 854356 62466461 := bstep (se 3 (by rfl) ⟨11712461, by rfl⟩ : syracuseStep 62466461 = 23424923) B23424923
theorem B4336091 : Blo 854356 4336091 := bstep (se 1 (by rfl) ⟨3252068, by rfl⟩ : syracuseStep 4336091 = 6504137) B6504137
theorem B2599535 : Blo 854356 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B2894561 : Blo 854356 2894561 := bstep (se 2 (by rfl) ⟨1085460, by rfl⟩ : syracuseStep 2894561 = 2170921) B2170921
theorem B3255137 : Blo 854356 3255137 := bstep (se 2 (by rfl) ⟨1220676, by rfl⟩ : syracuseStep 3255137 = 2441353) B2441353
theorem B2894831 : Blo 854356 2894831 := bstep (se 1 (by rfl) ⟨2171123, by rfl⟩ : syracuseStep 2894831 = 4342247) B4342247
theorem B4762633 : Blo 854356 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B2896829 : Blo 854356 2896829 := bstep (se 3 (by rfl) ⟨543155, by rfl⟩ : syracuseStep 2896829 = 1086311) B1086311
theorem B5486075 : Blo 854356 5486075 := bstep (se 1 (by rfl) ⟨4114556, by rfl⟩ : syracuseStep 5486075 = 8229113) B8229113
theorem B29702315 : Blo 854356 29702315 := bstep (se 1 (by rfl) ⟨22276736, by rfl⟩ : syracuseStep 29702315 = 44553473) B44553473
theorem B9746729 : Blo 854356 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B965371 : Blo 854356 965371 := bstep (se 1 (by rfl) ⟨724028, by rfl⟩ : syracuseStep 965371 = 1448057) B1448057
theorem B6503165 : Blo 854356 6503165 := bstep (se 3 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 6503165 = 2438687) B2438687
theorem B965407 : Blo 854356 965407 := bstep (se 1 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 965407 = 1448111) B1448111
theorem B16464829 : Blo 854356 16464829 := bstep (se 3 (by rfl) ⟨3087155, by rfl⟩ : syracuseStep 16464829 = 6174311) B6174311
theorem B1391791 : Blo 854356 1391791 := bstep (se 1 (by rfl) ⟨1043843, by rfl⟩ : syracuseStep 1391791 = 2087687) B2087687
theorem B3655145 : Blo 854356 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B4343543 : Blo 854356 4343543 := bstep (se 1 (by rfl) ⟨3257657, by rfl⟩ : syracuseStep 4343543 = 6515315) B6515315
theorem B2672507 : Blo 854356 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B25085861 : Blo 854356 25085861 := bstep (se 4 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 25085861 = 4703599) B4703599
theorem B4344191 : Blo 854356 4344191 := bstep (se 1 (by rfl) ⟨3258143, by rfl⟩ : syracuseStep 4344191 = 6516287) B6516287
theorem B270912437 : Blo 854356 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B4869629 : Blo 854356 4869629 := bstep (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) B1826111
theorem B236900213 : Blo 854356 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B20795399 : Blo 854356 20795399 := bstep (se 1 (by rfl) ⟨15596549, by rfl⟩ : syracuseStep 20795399 = 31193099) B31193099
theorem B10998287 : Blo 854356 10998287 := bstep (se 1 (by rfl) ⟨8248715, by rfl⟩ : syracuseStep 10998287 = 16497431) B16497431
theorem B5493865 : Blo 854356 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B2741473 : Blo 854356 2741473 := bstep (se 2 (by rfl) ⟨1028052, by rfl⟩ : syracuseStep 2741473 = 2056105) B2056105
theorem B5559833 : Blo 854356 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B1922633 : Blo 854356 1922633 := bstep (se 2 (by rfl) ⟨720987, by rfl⟩ : syracuseStep 1922633 = 1441975) B1441975
theorem B26367839 : Blo 854356 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B1628495 : Blo 854356 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B4938241 : Blo 854356 4938241 := bstep (se 2 (by rfl) ⟨1851840, by rfl⟩ : syracuseStep 4938241 = 3703681) B3703681
theorem B6511913 : Blo 854356 6511913 := bstep (se 2 (by rfl) ⟨2441967, by rfl⟩ : syracuseStep 6511913 = 4883935) B4883935
theorem B5201405 : Blo 854356 5201405 := bstep (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) B1950527
theorem B1924955 : Blo 854356 1924955 := bstep (se 1 (by rfl) ⟨1443716, by rfl⟩ : syracuseStep 1924955 = 2887433) B2887433
theorem B1924991 : Blo 854356 1924991 := bstep (se 1 (by rfl) ⟨1443743, by rfl⟩ : syracuseStep 1924991 = 2887487) B2887487
theorem B12673199 : Blo 854356 12673199 := bstep (se 1 (by rfl) ⟨9504899, by rfl⟩ : syracuseStep 12673199 = 19009799) B19009799
theorem B1925531 : Blo 854356 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B1368713 : Blo 854356 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B1926395 : Blo 854356 1926395 := bstep (se 1 (by rfl) ⟨1444796, by rfl⟩ : syracuseStep 1926395 = 2889593) B2889593
theorem B31647827 : Blo 854356 31647827 := bstep (se 1 (by rfl) ⟨23735870, by rfl⟩ : syracuseStep 31647827 = 47471741) B47471741
theorem B4122899 : Blo 854356 4122899 := bstep (se 1 (by rfl) ⟨3092174, by rfl⟩ : syracuseStep 4122899 = 6184349) B6184349
theorem B1927583 : Blo 854356 1927583 := bstep (se 1 (by rfl) ⟨1445687, by rfl⟩ : syracuseStep 1927583 = 2891375) B2891375
theorem B6515801 : Blo 854356 6515801 := bstep (se 2 (by rfl) ⟨2443425, by rfl⟩ : syracuseStep 6515801 = 4886851) B4886851
theorem B2059451 : Blo 854356 2059451 := bstep (se 1 (by rfl) ⟨1544588, by rfl⟩ : syracuseStep 2059451 = 3089177) B3089177
theorem B52620839 : Blo 854356 52620839 := bstep (se 1 (by rfl) ⟨39465629, by rfl⟩ : syracuseStep 52620839 = 78931259) B78931259
theorem B1928825 : Blo 854356 1928825 := bstep (se 2 (by rfl) ⟨723309, by rfl⟩ : syracuseStep 1928825 = 1446619) B1446619
theorem B1930553 : Blo 854356 1930553 := bstep (se 2 (by rfl) ⟨723957, by rfl⟩ : syracuseStep 1930553 = 1447915) B1447915
theorem B13563227 : Blo 854356 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B120321821 : Blo 854356 120321821 := bstep (se 3 (by rfl) ⟨22560341, by rfl⟩ : syracuseStep 120321821 = 45120683) B45120683
theorem B71333783 : Blo 854356 71333783 := bstep (se 1 (by rfl) ⟨53500337, by rfl⟩ : syracuseStep 71333783 = 107000675) B107000675
theorem B2783659 : Blo 854356 2783659 := bstep (se 1 (by rfl) ⟨2087744, by rfl⟩ : syracuseStep 2783659 = 4175489) B4175489
theorem B2162771 : Blo 854356 2162771 := bstep (se 1 (by rfl) ⟨1622078, by rfl⟩ : syracuseStep 2162771 = 3244157) B3244157
theorem B29622505 : Blo 854356 29622505 := bstep (se 2 (by rfl) ⟨11108439, by rfl⟩ : syracuseStep 29622505 = 22216879) B22216879
theorem B2162983 : Blo 854356 2162983 := bstep (se 1 (by rfl) ⟨1622237, by rfl⟩ : syracuseStep 2162983 = 3244475) B3244475
theorem B16450067 : Blo 854356 16450067 := bstep (se 1 (by rfl) ⟨12337550, by rfl⟩ : syracuseStep 16450067 = 24675101) B24675101
theorem B2164603 : Blo 854356 2164603 := bstep (se 1 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 2164603 = 3246905) B3246905
theorem B6948767 : Blo 854356 6948767 := bstep (se 1 (by rfl) ⟨5211575, by rfl⟩ : syracuseStep 6948767 = 10423151) B10423151
theorem B2164715 : Blo 854356 2164715 := bstep (se 1 (by rfl) ⟨1623536, by rfl⟩ : syracuseStep 2164715 = 3247073) B3247073
theorem B3246419 : Blo 854356 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B854495 : Blo 854356 854495 := bstep (se 1 (by rfl) ⟨640871, by rfl⟩ : syracuseStep 854495 = 1281743) B1281743
theorem B854619 : Blo 854356 854619 := bstep (se 1 (by rfl) ⟨640964, by rfl⟩ : syracuseStep 854619 = 1281929) B1281929
theorem B13863599 : Blo 854356 13863599 := bstep (se 1 (by rfl) ⟨10397699, by rfl⟩ : syracuseStep 13863599 = 20795399) B20795399
theorem B4328315 : Blo 854356 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B855295 : Blo 854356 855295 := bstep (se 1 (by rfl) ⟨641471, by rfl⟩ : syracuseStep 855295 = 1282943) B1282943
theorem B855359 : Blo 854356 855359 := bstep (se 1 (by rfl) ⟨641519, by rfl⟩ : syracuseStep 855359 = 1283039) B1283039
theorem B3706555 : Blo 854356 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B1281755 : Blo 854356 1281755 := bstep (se 1 (by rfl) ⟨961316, by rfl⟩ : syracuseStep 1281755 = 1922633) B1922633
theorem B4329287 : Blo 854356 4329287 := bstep (se 1 (by rfl) ⟨3246965, by rfl⟩ : syracuseStep 4329287 = 6493931) B6493931
theorem B855899 : Blo 854356 855899 := bstep (se 1 (by rfl) ⟨641924, by rfl⟩ : syracuseStep 855899 = 1283849) B1283849
theorem B855967 : Blo 854356 855967 := bstep (se 1 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 855967 = 1283951) B1283951
theorem B856091 : Blo 854356 856091 := bstep (se 1 (by rfl) ⟨642068, by rfl⟩ : syracuseStep 856091 = 1284137) B1284137
theorem B856111 : Blo 854356 856111 := bstep (se 1 (by rfl) ⟨642083, by rfl⟩ : syracuseStep 856111 = 1284167) B1284167
theorem B1085663 : Blo 854356 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B856543 : Blo 854356 856543 := bstep (se 1 (by rfl) ⟨642407, by rfl⟩ : syracuseStep 856543 = 1284815) B1284815
theorem B856667 : Blo 854356 856667 := bstep (se 1 (by rfl) ⟨642500, by rfl⟩ : syracuseStep 856667 = 1285001) B1285001
theorem B6492959 : Blo 854356 6492959 := bstep (se 1 (by rfl) ⟨4869719, by rfl⟩ : syracuseStep 6492959 = 9739439) B9739439
theorem B857023 : Blo 854356 857023 := bstep (se 1 (by rfl) ⟨642767, by rfl⟩ : syracuseStep 857023 = 1285535) B1285535
theorem B857119 : Blo 854356 857119 := bstep (se 1 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 857119 = 1285679) B1285679
theorem B1283303 : Blo 854356 1283303 := bstep (se 1 (by rfl) ⟨962477, by rfl⟩ : syracuseStep 1283303 = 1924955) B1924955
theorem B1283327 : Blo 854356 1283327 := bstep (se 1 (by rfl) ⟨962495, by rfl⟩ : syracuseStep 1283327 = 1924991) B1924991
theorem B2168167 : Blo 854356 2168167 := bstep (se 1 (by rfl) ⟨1626125, by rfl⟩ : syracuseStep 2168167 = 3252251) B3252251
theorem B1283687 : Blo 854356 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B857703 : Blo 854356 857703 := bstep (se 1 (by rfl) ⟨643277, by rfl⟩ : syracuseStep 857703 = 1286555) B1286555
theorem B3086063 : Blo 854356 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B858159 : Blo 854356 858159 := bstep (se 1 (by rfl) ⟨643619, by rfl⟩ : syracuseStep 858159 = 1287239) B1287239
theorem B1284263 : Blo 854356 1284263 := bstep (se 1 (by rfl) ⟨963197, by rfl⟩ : syracuseStep 1284263 = 1926395) B1926395
theorem B858279 : Blo 854356 858279 := bstep (se 1 (by rfl) ⟨643709, by rfl⟩ : syracuseStep 858279 = 1287419) B1287419
theorem B1285055 : Blo 854356 1285055 := bstep (se 1 (by rfl) ⟨963791, by rfl⟩ : syracuseStep 1285055 = 1927583) B1927583
theorem B2890727 : Blo 854356 2890727 := bstep (se 1 (by rfl) ⟨2168045, by rfl⟩ : syracuseStep 2890727 = 4336091) B4336091
theorem B2170091 : Blo 854356 2170091 := bstep (se 1 (by rfl) ⟨1627568, by rfl⟩ : syracuseStep 2170091 = 3255137) B3255137
theorem B1285883 : Blo 854356 1285883 := bstep (se 1 (by rfl) ⟨964412, by rfl⟩ : syracuseStep 1285883 = 1928825) B1928825
theorem B3711545 : Blo 854356 3711545 := bstep (se 2 (by rfl) ⟨1391829, by rfl⟩ : syracuseStep 3711545 = 2783659) B2783659
theorem B1287035 : Blo 854356 1287035 := bstep (se 1 (by rfl) ⟨965276, by rfl⟩ : syracuseStep 1287035 = 1930553) B1930553
theorem B1287161 : Blo 854356 1287161 := bstep (se 2 (by rfl) ⟨482685, by rfl⟩ : syracuseStep 1287161 = 965371) B965371
theorem B1287209 : Blo 854356 1287209 := bstep (se 2 (by rfl) ⟨482703, by rfl⟩ : syracuseStep 1287209 = 965407) B965407
theorem B47555855 : Blo 854356 47555855 := bstep (se 1 (by rfl) ⟨35666891, by rfl⟩ : syracuseStep 47555855 = 71333783) B71333783
theorem B19801543 : Blo 854356 19801543 := bstep (se 1 (by rfl) ⟨14851157, by rfl⟩ : syracuseStep 19801543 = 29702315) B29702315
theorem B6497819 : Blo 854356 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B4335443 : Blo 854356 4335443 := bstep (se 1 (by rfl) ⟨3251582, by rfl⟩ : syracuseStep 4335443 = 6503165) B6503165
theorem B4107289 : Blo 854356 4107289 := bstep (se 2 (by rfl) ⟨1540233, by rfl⟩ : syracuseStep 4107289 = 3080467) B3080467
theorem B961627 : Blo 854356 961627 := bstep (se 1 (by rfl) ⟨721220, by rfl⟩ : syracuseStep 961627 = 1442441) B1442441
theorem B2436763 : Blo 854356 2436763 := bstep (se 1 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 2436763 = 3655145) B3655145
theorem B2895695 : Blo 854356 2895695 := bstep (se 1 (by rfl) ⟨2171771, by rfl⟩ : syracuseStep 2895695 = 4343543) B4343543
theorem B1781671 : Blo 854356 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B16723907 : Blo 854356 16723907 := bstep (se 1 (by rfl) ⟨12542930, by rfl⟩ : syracuseStep 16723907 = 25085861) B25085861
theorem B2896127 : Blo 854356 2896127 := bstep (se 1 (by rfl) ⟨2172095, by rfl⟩ : syracuseStep 2896127 = 4344191) B4344191
theorem B3256807 : Blo 854356 3256807 := bstep (se 1 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 3256807 = 4885211) B4885211
theorem B3650771 : Blo 854356 3650771 := bstep (se 1 (by rfl) ⟨2738078, by rfl⟩ : syracuseStep 3650771 = 5476157) B5476157
theorem B964327 : Blo 854356 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B17578559 : Blo 854356 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B965479 : Blo 854356 965479 := bstep (se 1 (by rfl) ⟨724109, by rfl⟩ : syracuseStep 965479 = 1448219) B1448219
theorem B4341275 : Blo 854356 4341275 := bstep (se 1 (by rfl) ⟨3255956, by rfl⟩ : syracuseStep 4341275 = 6511913) B6511913
theorem B7325153 : Blo 854356 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B3655297 : Blo 854356 3655297 := bstep (se 2 (by rfl) ⟨1370736, by rfl⟩ : syracuseStep 3655297 = 2741473) B2741473
theorem B4343867 : Blo 854356 4343867 := bstep (se 1 (by rfl) ⟨3257900, by rfl⟩ : syracuseStep 4343867 = 6515801) B6515801
theorem B35080559 : Blo 854356 35080559 := bstep (se 1 (by rfl) ⟨26310419, by rfl⟩ : syracuseStep 35080559 = 52620839) B52620839
theorem B18534005 : Blo 854356 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B3657383 : Blo 854356 3657383 := bstep (se 1 (by rfl) ⟨2743037, by rfl⟩ : syracuseStep 3657383 = 5486075) B5486075
theorem B1855721 : Blo 854356 1855721 := bstep (se 2 (by rfl) ⟨695895, by rfl⟩ : syracuseStep 1855721 = 1391791) B1391791
theorem B8804587 : Blo 854356 8804587 := bstep (se 1 (by rfl) ⟨6603440, by rfl⟩ : syracuseStep 8804587 = 13206881) B13206881
theorem B9264235 : Blo 854356 9264235 := bstep (se 1 (by rfl) ⟨6948176, by rfl⟩ : syracuseStep 9264235 = 13896353) B13896353
theorem B180608291 : Blo 854356 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B157933475 : Blo 854356 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B7332191 : Blo 854356 7332191 := bstep (se 1 (by rfl) ⟨5499143, by rfl⟩ : syracuseStep 7332191 = 10998287) B10998287
theorem B39641561 : Blo 854356 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B1926215 : Blo 854356 1926215 := bstep (se 1 (by rfl) ⟨1444661, by rfl⟩ : syracuseStep 1926215 = 2889323) B2889323
theorem B6350177 : Blo 854356 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B8218655 : Blo 854356 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B4876463 : Blo 854356 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B3467603 : Blo 854356 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B10578383 : Blo 854356 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B8448799 : Blo 854356 8448799 := bstep (se 1 (by rfl) ⟨6336599, by rfl⟩ : syracuseStep 8448799 = 12673199) B12673199
theorem B912475 : Blo 854356 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B21098551 : Blo 854356 21098551 := bstep (se 1 (by rfl) ⟨15823913, by rfl⟩ : syracuseStep 21098551 = 31647827) B31647827
theorem B2748599 : Blo 854356 2748599 := bstep (se 1 (by rfl) ⟨2061449, by rfl⟩ : syracuseStep 2748599 = 4122899) B4122899
theorem B41644307 : Blo 854356 41644307 := bstep (se 1 (by rfl) ⟨31233230, by rfl⟩ : syracuseStep 41644307 = 62466461) B62466461
theorem B1733023 : Blo 854356 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B1929707 : Blo 854356 1929707 := bstep (se 1 (by rfl) ⟨1447280, by rfl⟩ : syracuseStep 1929707 = 2894561) B2894561
theorem B1929887 : Blo 854356 1929887 := bstep (se 1 (by rfl) ⟨1447415, by rfl⟩ : syracuseStep 1929887 = 2894831) B2894831
theorem B1372967 : Blo 854356 1372967 := bstep (se 1 (by rfl) ⟨1029725, by rfl⟩ : syracuseStep 1372967 = 2059451) B2059451
theorem B1931219 : Blo 854356 1931219 := bstep (se 1 (by rfl) ⟨1448414, by rfl⟩ : syracuseStep 1931219 = 2896829) B2896829
theorem B6584321 : Blo 854356 6584321 := bstep (se 2 (by rfl) ⟨2469120, by rfl⟩ : syracuseStep 6584321 = 4938241) B4938241
theorem B9042151 : Blo 854356 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B80214547 : Blo 854356 80214547 := bstep (se 1 (by rfl) ⟨60160910, by rfl⟩ : syracuseStep 80214547 = 120321821) B120321821
theorem B21953105 : Blo 854356 21953105 := bstep (se 2 (by rfl) ⟨8232414, by rfl⟩ : syracuseStep 21953105 = 16464829) B16464829
theorem B1441847 : Blo 854356 1441847 := bstep (se 1 (by rfl) ⟨1081385, by rfl⟩ : syracuseStep 1441847 = 2162771) B2162771
theorem B2883977 : Blo 854356 2883977 := bstep (se 2 (by rfl) ⟨1081491, by rfl⟩ : syracuseStep 2883977 = 2162983) B2162983
theorem B4948589 : Blo 854356 4948589 := bstep (se 3 (by rfl) ⟨927860, by rfl⟩ : syracuseStep 4948589 = 1855721) B1855721
theorem B4883435 : Blo 854356 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B1443143 : Blo 854356 1443143 := bstep (se 1 (by rfl) ⟨1082357, by rfl⟩ : syracuseStep 1443143 = 2164715) B2164715
theorem B2164279 : Blo 854356 2164279 := bstep (se 1 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 2164279 = 3246419) B3246419
theorem B9242399 : Blo 854356 9242399 := bstep (se 1 (by rfl) ⟨6931799, by rfl⟩ : syracuseStep 9242399 = 13863599) B13863599
theorem B2885543 : Blo 854356 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B12356003 : Blo 854356 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B854503 : Blo 854356 854503 := bstep (se 1 (by rfl) ⟨640877, by rfl⟩ : syracuseStep 854503 = 1281755) B1281755
theorem B2886137 : Blo 854356 2886137 := bstep (se 2 (by rfl) ⟨1082301, by rfl⟩ : syracuseStep 2886137 = 2164603) B2164603
theorem B2886191 : Blo 854356 2886191 := bstep (se 1 (by rfl) ⟨2164643, by rfl⟩ : syracuseStep 2886191 = 4329287) B4329287
theorem B4328639 : Blo 854356 4328639 := bstep (se 1 (by rfl) ⟨3246479, by rfl⟩ : syracuseStep 4328639 = 6492959) B6492959
theorem B855535 : Blo 854356 855535 := bstep (se 1 (by rfl) ⟨641651, by rfl⟩ : syracuseStep 855535 = 1283303) B1283303
theorem B855551 : Blo 854356 855551 := bstep (se 1 (by rfl) ⟨641663, by rfl⟩ : syracuseStep 855551 = 1283327) B1283327
theorem B855791 : Blo 854356 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B5476385 : Blo 854356 5476385 := bstep (se 2 (by rfl) ⟨2053644, by rfl⟩ : syracuseStep 5476385 = 4107289) B4107289
theorem B856175 : Blo 854356 856175 := bstep (se 1 (by rfl) ⟨642131, by rfl⟩ : syracuseStep 856175 = 1284263) B1284263
theorem B1216633 : Blo 854356 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B1282169 : Blo 854356 1282169 := bstep (se 2 (by rfl) ⟨480813, by rfl⟩ : syracuseStep 1282169 = 961627) B961627
theorem B856703 : Blo 854356 856703 := bstep (se 1 (by rfl) ⟨642527, by rfl⟩ : syracuseStep 856703 = 1285055) B1285055
theorem B1446727 : Blo 854356 1446727 := bstep (se 1 (by rfl) ⟨1085045, by rfl⟩ : syracuseStep 1446727 = 2170091) B2170091
theorem B3249017 : Blo 854356 3249017 := bstep (se 2 (by rfl) ⟨1218381, by rfl⟩ : syracuseStep 3249017 = 2436763) B2436763
theorem B857255 : Blo 854356 857255 := bstep (se 1 (by rfl) ⟨642941, by rfl⟩ : syracuseStep 857255 = 1285883) B1285883
theorem B105288983 : Blo 854356 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B4888127 : Blo 854356 4888127 := bstep (se 1 (by rfl) ⟨3666095, by rfl⟩ : syracuseStep 4888127 = 7332191) B7332191
theorem B858023 : Blo 854356 858023 := bstep (se 1 (by rfl) ⟨643517, by rfl⟩ : syracuseStep 858023 = 1287035) B1287035
theorem B858107 : Blo 854356 858107 := bstep (se 1 (by rfl) ⟨643580, by rfl⟩ : syracuseStep 858107 = 1287161) B1287161
theorem B858139 : Blo 854356 858139 := bstep (se 1 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 858139 = 1287209) B1287209
theorem B1284143 : Blo 854356 1284143 := bstep (se 1 (by rfl) ⟨963107, by rfl⟩ : syracuseStep 1284143 = 1926215) B1926215
theorem B4331879 : Blo 854356 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B2890295 : Blo 854356 2890295 := bstep (se 1 (by rfl) ⟨2167721, by rfl⟩ : syracuseStep 2890295 = 4335443) B4335443
theorem B5479103 : Blo 854356 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B3250975 : Blo 854356 3250975 := bstep (se 1 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 3250975 = 4876463) B4876463
theorem B7052255 : Blo 854356 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B2890889 : Blo 854356 2890889 := bstep (se 2 (by rfl) ⟨1084083, by rfl⟩ : syracuseStep 2890889 = 2168167) B2168167
theorem B1285769 : Blo 854356 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B11149271 : Blo 854356 11149271 := bstep (se 1 (by rfl) ⟨8361953, by rfl⟩ : syracuseStep 11149271 = 16723907) B16723907
theorem B27762871 : Blo 854356 27762871 := bstep (se 1 (by rfl) ⟨20822153, by rfl⟩ : syracuseStep 27762871 = 41644307) B41644307
theorem B11739449 : Blo 854356 11739449 := bstep (se 2 (by rfl) ⟨4402293, by rfl⟩ : syracuseStep 11739449 = 8804587) B8804587
theorem B1286471 : Blo 854356 1286471 := bstep (se 1 (by rfl) ⟨964853, by rfl⟩ : syracuseStep 1286471 = 1929707) B1929707
theorem B1286591 : Blo 854356 1286591 := bstep (se 1 (by rfl) ⟨964943, by rfl⟩ : syracuseStep 1286591 = 1929887) B1929887
theorem B2433847 : Blo 854356 2433847 := bstep (se 1 (by rfl) ⟨1825385, by rfl⟩ : syracuseStep 2433847 = 3650771) B3650771
theorem B1287305 : Blo 854356 1287305 := bstep (se 2 (by rfl) ⟨482739, by rfl⟩ : syracuseStep 1287305 = 965479) B965479
theorem B1287479 : Blo 854356 1287479 := bstep (se 1 (by rfl) ⟨965609, by rfl⟩ : syracuseStep 1287479 = 1931219) B1931219
theorem B2894183 : Blo 854356 2894183 := bstep (se 1 (by rfl) ⟨2170637, by rfl⟩ : syracuseStep 2894183 = 4341275) B4341275
theorem B39496673 : Blo 854356 39496673 := bstep (se 2 (by rfl) ⟨14811252, by rfl⟩ : syracuseStep 39496673 = 29622505) B29622505
theorem B2895101 : Blo 854356 2895101 := bstep (se 3 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 2895101 = 1085663) B1085663
theorem B4632511 : Blo 854356 4632511 := bstep (se 1 (by rfl) ⟨3474383, by rfl⟩ : syracuseStep 4632511 = 6948767) B6948767
theorem B2895911 : Blo 854356 2895911 := bstep (se 1 (by rfl) ⟨2171933, by rfl⟩ : syracuseStep 2895911 = 4343867) B4343867
theorem B2438255 : Blo 854356 2438255 := bstep (se 1 (by rfl) ⟨1828691, by rfl⟩ : syracuseStep 2438255 = 3657383) B3657383
theorem B120405527 : Blo 854356 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B2375561 : Blo 854356 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B28131401 : Blo 854356 28131401 := bstep (se 2 (by rfl) ⟨10549275, by rfl⟩ : syracuseStep 28131401 = 21098551) B21098551
theorem B26427707 : Blo 854356 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B2474363 : Blo 854356 2474363 := bstep (se 1 (by rfl) ⟨1855772, by rfl⟩ : syracuseStep 2474363 = 3711545) B3711545
theorem B2310697 : Blo 854356 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B4342409 : Blo 854356 4342409 := bstep (se 2 (by rfl) ⟨1628403, by rfl⟩ : syracuseStep 4342409 = 3256807) B3256807
theorem B31703903 : Blo 854356 31703903 := bstep (se 1 (by rfl) ⟨23777927, by rfl⟩ : syracuseStep 31703903 = 47555855) B47555855
theorem B2311735 : Blo 854356 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B11719039 : Blo 854356 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B14635403 : Blo 854356 14635403 := bstep (se 1 (by rfl) ⟨10976552, by rfl⟩ : syracuseStep 14635403 = 21953105) B21953105
theorem B10966711 : Blo 854356 10966711 := bstep (se 1 (by rfl) ⟨8225033, by rfl⟩ : syracuseStep 10966711 = 16450067) B16450067
theorem B23387039 : Blo 854356 23387039 := bstep (se 1 (by rfl) ⟨17540279, by rfl⟩ : syracuseStep 23387039 = 35080559) B35080559
theorem B26402057 : Blo 854356 26402057 := bstep (se 2 (by rfl) ⟨9900771, by rfl⟩ : syracuseStep 26402057 = 19801543) B19801543
theorem B4873729 : Blo 854356 4873729 := bstep (se 2 (by rfl) ⟨1827648, by rfl⟩ : syracuseStep 4873729 = 3655297) B3655297
theorem B16933805 : Blo 854356 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B11265065 : Blo 854356 11265065 := bstep (se 2 (by rfl) ⟨4224399, by rfl⟩ : syracuseStep 11265065 = 8448799) B8448799
theorem B2057375 : Blo 854356 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1927151 : Blo 854356 1927151 := bstep (se 1 (by rfl) ⟨1445363, by rfl⟩ : syracuseStep 1927151 = 2890727) B2890727
theorem B4942073 : Blo 854356 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B1930463 : Blo 854356 1930463 := bstep (se 1 (by rfl) ⟨1447847, by rfl⟩ : syracuseStep 1930463 = 2895695) B2895695
theorem B1832399 : Blo 854356 1832399 := bstep (se 1 (by rfl) ⟨1374299, by rfl⟩ : syracuseStep 1832399 = 2748599) B2748599
theorem B1930751 : Blo 854356 1930751 := bstep (se 1 (by rfl) ⟨1448063, by rfl⟩ : syracuseStep 1930751 = 2896127) B2896127
theorem B12056201 : Blo 854356 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B915311 : Blo 854356 915311 := bstep (se 1 (by rfl) ⟨686483, by rfl⟩ : syracuseStep 915311 = 1372967) B1372967
theorem B106952729 : Blo 854356 106952729 := bstep (se 2 (by rfl) ⟨40107273, by rfl⟩ : syracuseStep 106952729 = 80214547) B80214547
theorem B4389547 : Blo 854356 4389547 := bstep (se 1 (by rfl) ⟨3292160, by rfl⟩ : syracuseStep 4389547 = 6584321) B6584321
theorem B12352313 : Blo 854356 12352313 := bstep (se 2 (by rfl) ⟨4632117, by rfl⟩ : syracuseStep 12352313 = 9264235) B9264235
theorem B21135935 : Blo 854356 21135935 := bstep (se 1 (by rfl) ⟨15851951, by rfl⟩ : syracuseStep 21135935 = 31703903) B31703903
theorem B3080929 : Blo 854356 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B3245129 : Blo 854356 3245129 := bstep (se 2 (by rfl) ⟨1216923, by rfl⟩ : syracuseStep 3245129 = 2433847) B2433847
theorem B6161599 : Blo 854356 6161599 := bstep (se 1 (by rfl) ⟨4621199, by rfl⟩ : syracuseStep 6161599 = 9242399) B9242399
theorem B2885705 : Blo 854356 2885705 := bstep (se 2 (by rfl) ⟨1082139, by rfl⟩ : syracuseStep 2885705 = 2164279) B2164279
theorem B3082313 : Blo 854356 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B2885759 : Blo 854356 2885759 := bstep (se 1 (by rfl) ⟨2164319, by rfl⟩ : syracuseStep 2885759 = 4328639) B4328639
theorem B854779 : Blo 854356 854779 := bstep (se 1 (by rfl) ⟨641084, by rfl⟩ : syracuseStep 854779 = 1282169) B1282169
theorem B2166011 : Blo 854356 2166011 := bstep (se 1 (by rfl) ⟨1624508, by rfl⟩ : syracuseStep 2166011 = 3249017) B3249017
theorem B70192655 : Blo 854356 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B856095 : Blo 854356 856095 := bstep (se 1 (by rfl) ⟨642071, by rfl⟩ : syracuseStep 856095 = 1284143) B1284143
theorem B2887919 : Blo 854356 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B17601371 : Blo 854356 17601371 := bstep (se 1 (by rfl) ⟨13201028, by rfl⟩ : syracuseStep 17601371 = 26402057) B26402057
theorem B857179 : Blo 854356 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B857647 : Blo 854356 857647 := bstep (se 1 (by rfl) ⟨643235, by rfl⟩ : syracuseStep 857647 = 1286471) B1286471
theorem B857727 : Blo 854356 857727 := bstep (se 1 (by rfl) ⟨643295, by rfl⟩ : syracuseStep 857727 = 1286591) B1286591
theorem B13178861 : Blo 854356 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B7510043 : Blo 854356 7510043 := bstep (se 1 (by rfl) ⟨5632532, by rfl⟩ : syracuseStep 7510043 = 11265065) B11265065
theorem B858203 : Blo 854356 858203 := bstep (se 1 (by rfl) ⟨643652, by rfl⟩ : syracuseStep 858203 = 1287305) B1287305
theorem B858319 : Blo 854356 858319 := bstep (se 1 (by rfl) ⟨643739, by rfl⟩ : syracuseStep 858319 = 1287479) B1287479
theorem B1284767 : Blo 854356 1284767 := bstep (se 1 (by rfl) ⟨963575, by rfl⟩ : syracuseStep 1284767 = 1927151) B1927151
theorem B14622281 : Blo 854356 14622281 := bstep (se 2 (by rfl) ⟨5483355, by rfl⟩ : syracuseStep 14622281 = 10966711) B10966711
theorem B1286975 : Blo 854356 1286975 := bstep (se 1 (by rfl) ⟨965231, by rfl⟩ : syracuseStep 1286975 = 1930463) B1930463
theorem B1221599 : Blo 854356 1221599 := bstep (se 1 (by rfl) ⟨916199, by rfl⟩ : syracuseStep 1221599 = 1832399) B1832399
theorem B1287167 : Blo 854356 1287167 := bstep (se 1 (by rfl) ⟨965375, by rfl⟩ : syracuseStep 1287167 = 1930751) B1930751
theorem B4334633 : Blo 854356 4334633 := bstep (se 2 (by rfl) ⟨1625487, by rfl⟩ : syracuseStep 4334633 = 3250975) B3250975
theorem B8037467 : Blo 854356 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B8234875 : Blo 854356 8234875 := bstep (se 1 (by rfl) ⟨6176156, by rfl⟩ : syracuseStep 8234875 = 12352313) B12352313
theorem B6498305 : Blo 854356 6498305 := bstep (se 2 (by rfl) ⟨2436864, by rfl⟩ : syracuseStep 6498305 = 4873729) B4873729
theorem B1583707 : Blo 854356 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B961231 : Blo 854356 961231 := bstep (se 1 (by rfl) ⟨720923, by rfl⟩ : syracuseStep 961231 = 1441847) B1441847
theorem B18754267 : Blo 854356 18754267 := bstep (se 1 (by rfl) ⟨14065700, by rfl⟩ : syracuseStep 18754267 = 28131401) B28131401
theorem B1649575 : Blo 854356 1649575 := bstep (se 1 (by rfl) ⟨1237181, by rfl⟩ : syracuseStep 1649575 = 2474363) B2474363
theorem B1140829109 : Blo 854356 1140829109 := bstep (se 5 (by rfl) ⟨53476364, by rfl⟩ : syracuseStep 1140829109 = 106952729) B106952729
theorem B2894939 : Blo 854356 2894939 := bstep (se 1 (by rfl) ⟨2171204, by rfl⟩ : syracuseStep 2894939 = 4342409) B4342409
theorem B3255623 : Blo 854356 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B31305197 : Blo 854356 31305197 := bstep (se 3 (by rfl) ⟨5869724, by rfl⟩ : syracuseStep 31305197 = 11739449) B11739449
theorem B962095 : Blo 854356 962095 := bstep (se 1 (by rfl) ⟨721571, by rfl⟩ : syracuseStep 962095 = 1443143) B1443143
theorem B3650923 : Blo 854356 3650923 := bstep (se 1 (by rfl) ⟨2738192, by rfl⟩ : syracuseStep 3650923 = 5476385) B5476385
theorem B3258751 : Blo 854356 3258751 := bstep (se 1 (by rfl) ⟨2444063, by rfl⟩ : syracuseStep 3258751 = 4888127) B4888127
theorem B3652735 : Blo 854356 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B4701503 : Blo 854356 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B2440829 : Blo 854356 2440829 := bstep (se 3 (by rfl) ⟨457655, by rfl⟩ : syracuseStep 2440829 = 915311) B915311
theorem B6176681 : Blo 854356 6176681 := bstep (se 2 (by rfl) ⟨2316255, by rfl⟩ : syracuseStep 6176681 = 4632511) B4632511
theorem B1622177 : Blo 854356 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B11289203 : Blo 854356 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B32949341 : Blo 854356 32949341 := bstep (se 3 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 32949341 = 12356003) B12356003
theorem B26331115 : Blo 854356 26331115 := bstep (se 1 (by rfl) ⟨19748336, by rfl⟩ : syracuseStep 26331115 = 39496673) B39496673
theorem B1625503 : Blo 854356 1625503 := bstep (se 1 (by rfl) ⟨1219127, by rfl⟩ : syracuseStep 1625503 = 2438255) B2438255
theorem B5852729 : Blo 854356 5852729 := bstep (se 2 (by rfl) ⟨2194773, by rfl⟩ : syracuseStep 5852729 = 4389547) B4389547
theorem B80270351 : Blo 854356 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B17618471 : Blo 854356 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B37017161 : Blo 854356 37017161 := bstep (se 2 (by rfl) ⟨13881435, by rfl⟩ : syracuseStep 37017161 = 27762871) B27762871
theorem B1922651 : Blo 854356 1922651 := bstep (se 1 (by rfl) ⟨1441988, by rfl⟩ : syracuseStep 1922651 = 2883977) B2883977
theorem B3299059 : Blo 854356 3299059 := bstep (se 1 (by rfl) ⟨2474294, by rfl⟩ : syracuseStep 3299059 = 4948589) B4948589
theorem B1923695 : Blo 854356 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B1924091 : Blo 854356 1924091 := bstep (se 1 (by rfl) ⟨1443068, by rfl⟩ : syracuseStep 1924091 = 2886137) B2886137
theorem B1924127 : Blo 854356 1924127 := bstep (se 1 (by rfl) ⟨1443095, by rfl⟩ : syracuseStep 1924127 = 2886191) B2886191
theorem B9756935 : Blo 854356 9756935 := bstep (se 1 (by rfl) ⟨7317701, by rfl⟩ : syracuseStep 9756935 = 14635403) B14635403
theorem B1926863 : Blo 854356 1926863 := bstep (se 1 (by rfl) ⟨1445147, by rfl⟩ : syracuseStep 1926863 = 2890295) B2890295
theorem B15591359 : Blo 854356 15591359 := bstep (se 1 (by rfl) ⟨11693519, by rfl⟩ : syracuseStep 15591359 = 23387039) B23387039
theorem B1927259 : Blo 854356 1927259 := bstep (se 1 (by rfl) ⟨1445444, by rfl⟩ : syracuseStep 1927259 = 2890889) B2890889
theorem B7432847 : Blo 854356 7432847 := bstep (se 1 (by rfl) ⟨5574635, by rfl⟩ : syracuseStep 7432847 = 11149271) B11149271
theorem B15625385 : Blo 854356 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B1371583 : Blo 854356 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B1928969 : Blo 854356 1928969 := bstep (se 2 (by rfl) ⟨723363, by rfl⟩ : syracuseStep 1928969 = 1446727) B1446727
theorem B1929455 : Blo 854356 1929455 := bstep (se 1 (by rfl) ⟨1447091, by rfl⟩ : syracuseStep 1929455 = 2894183) B2894183
theorem B1930067 : Blo 854356 1930067 := bstep (se 1 (by rfl) ⟨1447550, by rfl⟩ : syracuseStep 1930067 = 2895101) B2895101
theorem B1930607 : Blo 854356 1930607 := bstep (se 1 (by rfl) ⟨1447955, by rfl⟩ : syracuseStep 1930607 = 2895911) B2895911
theorem B1081451 : Blo 854356 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B2163419 : Blo 854356 2163419 := bstep (se 1 (by rfl) ⟨1622564, by rfl⟩ : syracuseStep 2163419 = 3245129) B3245129
theorem B56362493 : Blo 854356 56362493 := bstep (se 3 (by rfl) ⟨10567967, by rfl⟩ : syracuseStep 56362493 = 21135935) B21135935
theorem B1444007 : Blo 854356 1444007 := bstep (se 1 (by rfl) ⟨1083005, by rfl⟩ : syracuseStep 1444007 = 2166011) B2166011
theorem B46795103 : Blo 854356 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B3901819 : Blo 854356 3901819 := bstep (se 1 (by rfl) ⟨2926364, by rfl⟩ : syracuseStep 3901819 = 5852729) B5852729
theorem B10979833 : Blo 854356 10979833 := bstep (se 2 (by rfl) ⟨4117437, by rfl⟩ : syracuseStep 10979833 = 8234875) B8234875
theorem B11734247 : Blo 854356 11734247 := bstep (se 1 (by rfl) ⟨8800685, by rfl⟩ : syracuseStep 11734247 = 17601371) B17601371
theorem B53513567 : Blo 854356 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B1281641 : Blo 854356 1281641 := bstep (se 2 (by rfl) ⟨480615, by rfl⟩ : syracuseStep 1281641 = 961231) B961231
theorem B25005689 : Blo 854356 25005689 := bstep (se 2 (by rfl) ⟨9377133, by rfl⟩ : syracuseStep 25005689 = 18754267) B18754267
theorem B24678107 : Blo 854356 24678107 := bstep (se 1 (by rfl) ⟨18508580, by rfl⟩ : syracuseStep 24678107 = 37017161) B37017161
theorem B1281767 : Blo 854356 1281767 := bstep (se 1 (by rfl) ⟨961325, by rfl⟩ : syracuseStep 1281767 = 1922651) B1922651
theorem B8785907 : Blo 854356 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B1282463 : Blo 854356 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B856511 : Blo 854356 856511 := bstep (se 1 (by rfl) ⟨642383, by rfl⟩ : syracuseStep 856511 = 1284767) B1284767
theorem B2167337 : Blo 854356 2167337 := bstep (se 2 (by rfl) ⟨812751, by rfl⟩ : syracuseStep 2167337 = 1625503) B1625503
theorem B1282727 : Blo 854356 1282727 := bstep (se 1 (by rfl) ⟨962045, by rfl⟩ : syracuseStep 1282727 = 1924091) B1924091
theorem B1282751 : Blo 854356 1282751 := bstep (se 1 (by rfl) ⟨962063, by rfl⟩ : syracuseStep 1282751 = 1924127) B1924127
theorem B1282793 : Blo 854356 1282793 := bstep (se 2 (by rfl) ⟨481047, by rfl⟩ : syracuseStep 1282793 = 962095) B962095
theorem B20026781 : Blo 854356 20026781 := bstep (se 3 (by rfl) ⟨3755021, by rfl⟩ : syracuseStep 20026781 = 7510043) B7510043
theorem B857983 : Blo 854356 857983 := bstep (se 1 (by rfl) ⟨643487, by rfl⟩ : syracuseStep 857983 = 1286975) B1286975
theorem B858111 : Blo 854356 858111 := bstep (se 1 (by rfl) ⟨643583, by rfl⟩ : syracuseStep 858111 = 1287167) B1287167
theorem B2889755 : Blo 854356 2889755 := bstep (se 1 (by rfl) ⟨2167316, by rfl⟩ : syracuseStep 2889755 = 4334633) B4334633
theorem B1284575 : Blo 854356 1284575 := bstep (se 1 (by rfl) ⟨963431, by rfl⟩ : syracuseStep 1284575 = 1926863) B1926863
theorem B10394239 : Blo 854356 10394239 := bstep (se 1 (by rfl) ⟨7795679, by rfl⟩ : syracuseStep 10394239 = 15591359) B15591359
theorem B4332203 : Blo 854356 4332203 := bstep (se 1 (by rfl) ⟨3249152, by rfl⟩ : syracuseStep 4332203 = 6498305) B6498305
theorem B1284839 : Blo 854356 1284839 := bstep (se 1 (by rfl) ⟨963629, by rfl⟩ : syracuseStep 1284839 = 1927259) B1927259
theorem B4955231 : Blo 854356 4955231 := bstep (se 1 (by rfl) ⟨3716423, by rfl⟩ : syracuseStep 4955231 = 7432847) B7432847
theorem B760552739 : Blo 854356 760552739 := bstep (se 1 (by rfl) ⟨570414554, by rfl⟩ : syracuseStep 760552739 = 1140829109) B1140829109
theorem B2170415 : Blo 854356 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B4398745 : Blo 854356 4398745 := bstep (se 2 (by rfl) ⟨1649529, by rfl⟩ : syracuseStep 4398745 = 3299059) B3299059
theorem B1285979 : Blo 854356 1285979 := bstep (se 1 (by rfl) ⟨964484, by rfl⟩ : syracuseStep 1285979 = 1928969) B1928969
theorem B1286303 : Blo 854356 1286303 := bstep (se 1 (by rfl) ⟨964727, by rfl⟩ : syracuseStep 1286303 = 1929455) B1929455
theorem B1286711 : Blo 854356 1286711 := bstep (se 1 (by rfl) ⟨965033, by rfl⟩ : syracuseStep 1286711 = 1930067) B1930067
theorem B1287071 : Blo 854356 1287071 := bstep (se 1 (by rfl) ⟨965303, by rfl⟩ : syracuseStep 1287071 = 1930607) B1930607
theorem B21966227 : Blo 854356 21966227 := bstep (se 1 (by rfl) ⟨16474670, by rfl⟩ : syracuseStep 21966227 = 32949341) B32949341
theorem B4107905 : Blo 854356 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B3257597 : Blo 854356 3257597 := bstep (se 3 (by rfl) ⟨610799, by rfl⟩ : syracuseStep 3257597 = 1221599) B1221599
theorem B35108153 : Blo 854356 35108153 := bstep (se 2 (by rfl) ⟨13165557, by rfl⟩ : syracuseStep 35108153 = 26331115) B26331115
theorem B2111609 : Blo 854356 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B11745647 : Blo 854356 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B8797733 : Blo 854356 8797733 := bstep (se 4 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 8797733 = 1649575) B1649575
theorem B9748187 : Blo 854356 9748187 := bstep (se 1 (by rfl) ⟨7311140, by rfl⟩ : syracuseStep 9748187 = 14622281) B14622281
theorem B6504623 : Blo 854356 6504623 := bstep (se 1 (by rfl) ⟨4878467, by rfl⟩ : syracuseStep 6504623 = 9756935) B9756935
theorem B5358311 : Blo 854356 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B4867897 : Blo 854356 4867897 := bstep (se 2 (by rfl) ⟨1825461, by rfl⟩ : syracuseStep 4867897 = 3650923) B3650923
theorem B4345001 : Blo 854356 4345001 := bstep (se 2 (by rfl) ⟨1629375, by rfl⟩ : syracuseStep 4345001 = 3258751) B3258751
theorem B12537341 : Blo 854356 12537341 := bstep (se 3 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 12537341 = 4701503) B4701503
theorem B4870313 : Blo 854356 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B1627219 : Blo 854356 1627219 := bstep (se 1 (by rfl) ⟨1220414, by rfl⟩ : syracuseStep 1627219 = 2440829) B2440829
theorem B4117787 : Blo 854356 4117787 := bstep (se 1 (by rfl) ⟨3088340, by rfl⟩ : syracuseStep 4117787 = 6176681) B6176681
theorem B7526135 : Blo 854356 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B1923803 : Blo 854356 1923803 := bstep (se 1 (by rfl) ⟨1442852, by rfl⟩ : syracuseStep 1923803 = 2885705) B2885705
theorem B2054875 : Blo 854356 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B1923839 : Blo 854356 1923839 := bstep (se 1 (by rfl) ⟨1442879, by rfl⟩ : syracuseStep 1923839 = 2885759) B2885759
theorem B8215465 : Blo 854356 8215465 := bstep (se 2 (by rfl) ⟨3080799, by rfl⟩ : syracuseStep 8215465 = 6161599) B6161599
theorem B1925279 : Blo 854356 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B1828777 : Blo 854356 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B1929959 : Blo 854356 1929959 := bstep (se 1 (by rfl) ⟨1447469, by rfl⟩ : syracuseStep 1929959 = 2894939) B2894939
theorem B10416923 : Blo 854356 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B20870131 : Blo 854356 20870131 := bstep (se 1 (by rfl) ⟨15652598, by rfl⟩ : syracuseStep 20870131 = 31305197) B31305197
theorem B2883869 : Blo 854356 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B1442279 : Blo 854356 1442279 := bstep (se 1 (by rfl) ⟨1081709, by rfl⟩ : syracuseStep 1442279 = 2163419) B2163419
theorem B3572207 : Blo 854356 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B31196735 : Blo 854356 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B8358227 : Blo 854356 8358227 := bstep (se 1 (by rfl) ⟨6268670, by rfl⟩ : syracuseStep 8358227 = 12537341) B12537341
theorem B854427 : Blo 854356 854427 := bstep (se 1 (by rfl) ⟨640820, by rfl⟩ : syracuseStep 854427 = 1281641) B1281641
theorem B6490529 : Blo 854356 6490529 := bstep (se 2 (by rfl) ⟨2433948, by rfl⟩ : syracuseStep 6490529 = 4867897) B4867897
theorem B16452071 : Blo 854356 16452071 := bstep (se 1 (by rfl) ⟨12339053, by rfl⟩ : syracuseStep 16452071 = 24678107) B24678107
theorem B854511 : Blo 854356 854511 := bstep (se 1 (by rfl) ⟨640883, by rfl⟩ : syracuseStep 854511 = 1281767) B1281767
theorem B3246875 : Blo 854356 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B854975 : Blo 854356 854975 := bstep (se 1 (by rfl) ⟨641231, by rfl⟩ : syracuseStep 854975 = 1282463) B1282463
theorem B1444891 : Blo 854356 1444891 := bstep (se 1 (by rfl) ⟨1083668, by rfl⟩ : syracuseStep 1444891 = 2167337) B2167337
theorem B855151 : Blo 854356 855151 := bstep (se 1 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 855151 = 1282727) B1282727
theorem B855167 : Blo 854356 855167 := bstep (se 1 (by rfl) ⟨641375, by rfl⟩ : syracuseStep 855167 = 1282751) B1282751
theorem B855195 : Blo 854356 855195 := bstep (se 1 (by rfl) ⟨641396, by rfl⟩ : syracuseStep 855195 = 1282793) B1282793
theorem B5017423 : Blo 854356 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B856383 : Blo 854356 856383 := bstep (se 1 (by rfl) ⟨642287, by rfl⟩ : syracuseStep 856383 = 1284575) B1284575
theorem B2888135 : Blo 854356 2888135 := bstep (se 1 (by rfl) ⟨2166101, by rfl⟩ : syracuseStep 2888135 = 4332203) B4332203
theorem B1282535 : Blo 854356 1282535 := bstep (se 1 (by rfl) ⟨961901, by rfl⟩ : syracuseStep 1282535 = 1923803) B1923803
theorem B856559 : Blo 854356 856559 := bstep (se 1 (by rfl) ⟨642419, by rfl⟩ : syracuseStep 856559 = 1284839) B1284839
theorem B1282559 : Blo 854356 1282559 := bstep (se 1 (by rfl) ⟨961919, by rfl⟩ : syracuseStep 1282559 = 1923839) B1923839
theorem B1446943 : Blo 854356 1446943 := bstep (se 1 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 1446943 = 2170415) B2170415
theorem B857319 : Blo 854356 857319 := bstep (se 1 (by rfl) ⟨642989, by rfl⟩ : syracuseStep 857319 = 1285979) B1285979
theorem B1283519 : Blo 854356 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B857535 : Blo 854356 857535 := bstep (se 1 (by rfl) ⟨643151, by rfl⟩ : syracuseStep 857535 = 1286303) B1286303
theorem B857807 : Blo 854356 857807 := bstep (se 1 (by rfl) ⟨643355, by rfl⟩ : syracuseStep 857807 = 1286711) B1286711
theorem B858047 : Blo 854356 858047 := bstep (se 1 (by rfl) ⟨643535, by rfl⟩ : syracuseStep 858047 = 1287071) B1287071
theorem B27826841 : Blo 854356 27826841 := bstep (se 2 (by rfl) ⟨10435065, by rfl⟩ : syracuseStep 27826841 = 20870131) B20870131
theorem B2169625 : Blo 854356 2169625 := bstep (se 2 (by rfl) ⟨813609, by rfl⟩ : syracuseStep 2169625 = 1627219) B1627219
theorem B13213949 : Blo 854356 13213949 := bstep (se 3 (by rfl) ⟨2477615, by rfl⟩ : syracuseStep 13213949 = 4955231) B4955231
theorem B1286639 : Blo 854356 1286639 := bstep (se 1 (by rfl) ⟨964979, by rfl⟩ : syracuseStep 1286639 = 1929959) B1929959
theorem B2171731 : Blo 854356 2171731 := bstep (se 1 (by rfl) ⟨1628798, by rfl⟩ : syracuseStep 2171731 = 3257597) B3257597
theorem B23405435 : Blo 854356 23405435 := bstep (se 1 (by rfl) ⟨17554076, by rfl⟩ : syracuseStep 23405435 = 35108153) B35108153
theorem B10953953 : Blo 854356 10953953 := bstep (se 2 (by rfl) ⟨4107732, by rfl⟩ : syracuseStep 10953953 = 8215465) B8215465
theorem B6498791 : Blo 854356 6498791 := bstep (se 1 (by rfl) ⟨4874093, by rfl⟩ : syracuseStep 6498791 = 9748187) B9748187
theorem B4336415 : Blo 854356 4336415 := bstep (se 1 (by rfl) ⟨3252311, by rfl⟩ : syracuseStep 4336415 = 6504623) B6504623
theorem B962671 : Blo 854356 962671 := bstep (se 1 (by rfl) ⟨722003, by rfl⟩ : syracuseStep 962671 = 1444007) B1444007
theorem B2896667 : Blo 854356 2896667 := bstep (se 1 (by rfl) ⟨2172500, by rfl⟩ : syracuseStep 2896667 = 4345001) B4345001
theorem B2438369 : Blo 854356 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B13351187 : Blo 854356 13351187 := bstep (se 1 (by rfl) ⟨10013390, by rfl⟩ : syracuseStep 13351187 = 20026781) B20026781
theorem B507035159 : Blo 854356 507035159 := bstep (se 1 (by rfl) ⟨380276369, by rfl⟩ : syracuseStep 507035159 = 760552739) B760552739
theorem B2738603 : Blo 854356 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B2739833 : Blo 854356 2739833 := bstep (se 2 (by rfl) ⟨1027437, by rfl⟩ : syracuseStep 2739833 = 2054875) B2054875
theorem B7822831 : Blo 854356 7822831 := bstep (se 1 (by rfl) ⟨5867123, by rfl⟩ : syracuseStep 7822831 = 11734247) B11734247
theorem B35675711 : Blo 854356 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B16670459 : Blo 854356 16670459 := bstep (se 1 (by rfl) ⟨12502844, by rfl⟩ : syracuseStep 16670459 = 25005689) B25005689
theorem B5857271 : Blo 854356 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B5202425 : Blo 854356 5202425 := bstep (se 2 (by rfl) ⟨1950909, by rfl⟩ : syracuseStep 5202425 = 3901819) B3901819
theorem B14639777 : Blo 854356 14639777 := bstep (se 2 (by rfl) ⟨5489916, by rfl⟩ : syracuseStep 14639777 = 10979833) B10979833
theorem B2745191 : Blo 854356 2745191 := bstep (se 1 (by rfl) ⟨2058893, by rfl⟩ : syracuseStep 2745191 = 4117787) B4117787
theorem B150299981 : Blo 854356 150299981 := bstep (se 3 (by rfl) ⟨28181246, by rfl⟩ : syracuseStep 150299981 = 56362493) B56362493
theorem B1926503 : Blo 854356 1926503 := bstep (se 1 (by rfl) ⟨1444877, by rfl⟩ : syracuseStep 1926503 = 2889755) B2889755
theorem B5630957 : Blo 854356 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B14644151 : Blo 854356 14644151 := bstep (se 1 (by rfl) ⟨10983113, by rfl⟩ : syracuseStep 14644151 = 21966227) B21966227
theorem B6944615 : Blo 854356 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B13858985 : Blo 854356 13858985 := bstep (se 2 (by rfl) ⟨5197119, by rfl⟩ : syracuseStep 13858985 = 10394239) B10394239
theorem B7830431 : Blo 854356 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B5864993 : Blo 854356 5864993 := bstep (se 2 (by rfl) ⟨2199372, by rfl⟩ : syracuseStep 5864993 = 4398745) B4398745
theorem B5865155 : Blo 854356 5865155 := bstep (se 1 (by rfl) ⟨4398866, by rfl⟩ : syracuseStep 5865155 = 8797733) B8797733
theorem B5572151 : Blo 854356 5572151 := bstep (se 1 (by rfl) ⟨4179113, by rfl⟩ : syracuseStep 5572151 = 8358227) B8358227
theorem B4327019 : Blo 854356 4327019 := bstep (se 1 (by rfl) ⟨3245264, by rfl⟩ : syracuseStep 4327019 = 6490529) B6490529
theorem B2164583 : Blo 854356 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B855023 : Blo 854356 855023 := bstep (se 1 (by rfl) ⟨641267, by rfl⟩ : syracuseStep 855023 = 1282535) B1282535
theorem B855039 : Blo 854356 855039 := bstep (se 1 (by rfl) ⟨641279, by rfl⟩ : syracuseStep 855039 = 1282559) B1282559
theorem B855679 : Blo 854356 855679 := bstep (se 1 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 855679 = 1283519) B1283519
theorem B18551227 : Blo 854356 18551227 := bstep (se 1 (by rfl) ⟨13913420, by rfl⟩ : syracuseStep 18551227 = 27826841) B27826841
theorem B6689897 : Blo 854356 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B3904847 : Blo 854356 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B1283561 : Blo 854356 1283561 := bstep (se 2 (by rfl) ⟨481335, by rfl⟩ : syracuseStep 1283561 = 962671) B962671
theorem B857759 : Blo 854356 857759 := bstep (se 1 (by rfl) ⟨643319, by rfl⟩ : syracuseStep 857759 = 1286639) B1286639
theorem B15603623 : Blo 854356 15603623 := bstep (se 1 (by rfl) ⟨11702717, by rfl⟩ : syracuseStep 15603623 = 23405435) B23405435
theorem B1284335 : Blo 854356 1284335 := bstep (se 1 (by rfl) ⟨963251, by rfl⟩ : syracuseStep 1284335 = 1926503) B1926503
theorem B4332527 : Blo 854356 4332527 := bstep (se 1 (by rfl) ⟨3249395, by rfl⟩ : syracuseStep 4332527 = 6498791) B6498791
theorem B2890943 : Blo 854356 2890943 := bstep (se 1 (by rfl) ⟨2168207, by rfl⟩ : syracuseStep 2890943 = 4336415) B4336415
theorem B2892833 : Blo 854356 2892833 := bstep (se 2 (by rfl) ⟨1084812, by rfl⟩ : syracuseStep 2892833 = 2169625) B2169625
theorem B4629743 : Blo 854356 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B5220287 : Blo 854356 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B10430441 : Blo 854356 10430441 := bstep (se 2 (by rfl) ⟨3911415, by rfl⟩ : syracuseStep 10430441 = 7822831) B7822831
theorem B3909995 : Blo 854356 3909995 := bstep (se 1 (by rfl) ⟨2932496, by rfl⟩ : syracuseStep 3909995 = 5864993) B5864993
theorem B3910103 : Blo 854356 3910103 := bstep (se 1 (by rfl) ⟨2932577, by rfl⟩ : syracuseStep 3910103 = 5865155) B5865155
theorem B961519 : Blo 854356 961519 := bstep (se 1 (by rfl) ⟨721139, by rfl⟩ : syracuseStep 961519 = 1442279) B1442279
theorem B35237197 : Blo 854356 35237197 := bstep (se 3 (by rfl) ⟨6606974, by rfl⟩ : syracuseStep 35237197 = 13213949) B13213949
theorem B2895641 : Blo 854356 2895641 := bstep (se 2 (by rfl) ⟨1085865, by rfl⟩ : syracuseStep 2895641 = 2171731) B2171731
theorem B13873133 : Blo 854356 13873133 := bstep (se 3 (by rfl) ⟨2601212, by rfl⟩ : syracuseStep 13873133 = 5202425) B5202425
theorem B35603165 : Blo 854356 35603165 := bstep (se 3 (by rfl) ⟨6675593, by rfl⟩ : syracuseStep 35603165 = 13351187) B13351187
theorem B3753971 : Blo 854356 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B1625579 : Blo 854356 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B44454557 : Blo 854356 44454557 := bstep (se 3 (by rfl) ⟨8335229, by rfl⟩ : syracuseStep 44454557 = 16670459) B16670459
theorem B338023439 : Blo 854356 338023439 := bstep (se 1 (by rfl) ⟨253517579, by rfl⟩ : syracuseStep 338023439 = 507035159) B507035159
theorem B1922579 : Blo 854356 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B2381471 : Blo 854356 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B20797823 : Blo 854356 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B1825735 : Blo 854356 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B10968047 : Blo 854356 10968047 := bstep (se 1 (by rfl) ⟨8226035, by rfl⟩ : syracuseStep 10968047 = 16452071) B16452071
theorem B1826555 : Blo 854356 1826555 := bstep (se 1 (by rfl) ⟨1369916, by rfl⟩ : syracuseStep 1826555 = 2739833) B2739833
theorem B1925423 : Blo 854356 1925423 := bstep (se 1 (by rfl) ⟨1444067, by rfl⟩ : syracuseStep 1925423 = 2888135) B2888135
theorem B1926521 : Blo 854356 1926521 := bstep (se 2 (by rfl) ⟨722445, by rfl⟩ : syracuseStep 1926521 = 1444891) B1444891
theorem B23783807 : Blo 854356 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B9759851 : Blo 854356 9759851 := bstep (se 1 (by rfl) ⟨7319888, by rfl⟩ : syracuseStep 9759851 = 14639777) B14639777
theorem B36957293 : Blo 854356 36957293 := bstep (se 3 (by rfl) ⟨6929492, by rfl⟩ : syracuseStep 36957293 = 13858985) B13858985
theorem B1830127 : Blo 854356 1830127 := bstep (se 1 (by rfl) ⟨1372595, by rfl⟩ : syracuseStep 1830127 = 2745191) B2745191
theorem B7302635 : Blo 854356 7302635 := bstep (se 1 (by rfl) ⟨5476976, by rfl⟩ : syracuseStep 7302635 = 10953953) B10953953
theorem B100199987 : Blo 854356 100199987 := bstep (se 1 (by rfl) ⟨75149990, by rfl⟩ : syracuseStep 100199987 = 150299981) B150299981
theorem B1929257 : Blo 854356 1929257 := bstep (se 2 (by rfl) ⟨723471, by rfl⟩ : syracuseStep 1929257 = 1446943) B1446943
theorem B1931111 : Blo 854356 1931111 := bstep (se 1 (by rfl) ⟨1448333, by rfl⟩ : syracuseStep 1931111 = 2896667) B2896667
theorem B9762767 : Blo 854356 9762767 := bstep (se 1 (by rfl) ⟨7322075, by rfl⟩ : syracuseStep 9762767 = 14644151) B14644151
theorem B2884679 : Blo 854356 2884679 := bstep (se 1 (by rfl) ⟨2163509, by rfl⟩ : syracuseStep 2884679 = 4327019) B4327019
theorem B1443055 : Blo 854356 1443055 := bstep (se 1 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 1443055 = 2164583) B2164583
theorem B1083719 : Blo 854356 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B225348959 : Blo 854356 225348959 := bstep (se 1 (by rfl) ⟨169011719, by rfl⟩ : syracuseStep 225348959 = 338023439) B338023439
theorem B4459931 : Blo 854356 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B855707 : Blo 854356 855707 := bstep (se 1 (by rfl) ⟨641780, by rfl⟩ : syracuseStep 855707 = 1283561) B1283561
theorem B1281719 : Blo 854356 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B1282025 : Blo 854356 1282025 := bstep (se 2 (by rfl) ⟨480759, by rfl⟩ : syracuseStep 1282025 = 961519) B961519
theorem B856223 : Blo 854356 856223 := bstep (se 1 (by rfl) ⟨642167, by rfl⟩ : syracuseStep 856223 = 1284335) B1284335
theorem B13865215 : Blo 854356 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B2888351 : Blo 854356 2888351 := bstep (se 1 (by rfl) ⟨2166263, by rfl⟩ : syracuseStep 2888351 = 4332527) B4332527
theorem B7312031 : Blo 854356 7312031 := bstep (se 1 (by rfl) ⟨5484023, by rfl⟩ : syracuseStep 7312031 = 10968047) B10968047
theorem B1283615 : Blo 854356 1283615 := bstep (se 1 (by rfl) ⟨962711, by rfl⟩ : syracuseStep 1283615 = 1925423) B1925423
theorem B3086495 : Blo 854356 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B1284347 : Blo 854356 1284347 := bstep (se 1 (by rfl) ⟨963260, by rfl⟩ : syracuseStep 1284347 = 1926521) B1926521
theorem B3480191 : Blo 854356 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B6953627 : Blo 854356 6953627 := bstep (se 1 (by rfl) ⟨5215220, by rfl⟩ : syracuseStep 6953627 = 10430441) B10430441
theorem B9248755 : Blo 854356 9248755 := bstep (se 1 (by rfl) ⟨6936566, by rfl⟩ : syracuseStep 9248755 = 13873133) B13873133
theorem B1286171 : Blo 854356 1286171 := bstep (se 1 (by rfl) ⟨964628, by rfl⟩ : syracuseStep 1286171 = 1929257) B1929257
theorem B1287407 : Blo 854356 1287407 := bstep (se 1 (by rfl) ⟨965555, by rfl⟩ : syracuseStep 1287407 = 1931111) B1931111
theorem B2434313 : Blo 854356 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B23735443 : Blo 854356 23735443 := bstep (se 1 (by rfl) ⟨17801582, by rfl⟩ : syracuseStep 23735443 = 35603165) B35603165
theorem B3714767 : Blo 854356 3714767 := bstep (se 1 (by rfl) ⟨2786075, by rfl⟩ : syracuseStep 3714767 = 5572151) B5572151
theorem B2502647 : Blo 854356 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B29636371 : Blo 854356 29636371 := bstep (se 1 (by rfl) ⟨22227278, by rfl⟩ : syracuseStep 29636371 = 44454557) B44454557
theorem B2603231 : Blo 854356 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B1587647 : Blo 854356 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B10402415 : Blo 854356 10402415 := bstep (se 1 (by rfl) ⟨7801811, by rfl⟩ : syracuseStep 10402415 = 15603623) B15603623
theorem B2440169 : Blo 854356 2440169 := bstep (se 2 (by rfl) ⟨915063, by rfl⟩ : syracuseStep 2440169 = 1830127) B1830127
theorem B2606663 : Blo 854356 2606663 := bstep (se 1 (by rfl) ⟨1954997, by rfl⟩ : syracuseStep 2606663 = 3909995) B3909995
theorem B2606735 : Blo 854356 2606735 := bstep (se 1 (by rfl) ⟨1955051, by rfl⟩ : syracuseStep 2606735 = 3910103) B3910103
theorem B6506567 : Blo 854356 6506567 := bstep (se 1 (by rfl) ⟨4879925, by rfl⟩ : syracuseStep 6506567 = 9759851) B9759851
theorem B4868423 : Blo 854356 4868423 := bstep (se 1 (by rfl) ⟨3651317, by rfl⟩ : syracuseStep 4868423 = 7302635) B7302635
theorem B66799991 : Blo 854356 66799991 := bstep (se 1 (by rfl) ⟨50099993, by rfl⟩ : syracuseStep 66799991 = 100199987) B100199987
theorem B6508511 : Blo 854356 6508511 := bstep (se 1 (by rfl) ⟨4881383, by rfl⟩ : syracuseStep 6508511 = 9762767) B9762767
theorem B4870813 : Blo 854356 4870813 := bstep (se 3 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 4870813 = 1826555) B1826555
theorem B46982929 : Blo 854356 46982929 := bstep (se 2 (by rfl) ⟨17618598, by rfl⟩ : syracuseStep 46982929 = 35237197) B35237197
theorem B1927295 : Blo 854356 1927295 := bstep (se 1 (by rfl) ⟨1445471, by rfl⟩ : syracuseStep 1927295 = 2890943) B2890943
theorem B24734969 : Blo 854356 24734969 := bstep (se 2 (by rfl) ⟨9275613, by rfl⟩ : syracuseStep 24734969 = 18551227) B18551227
theorem B1928555 : Blo 854356 1928555 := bstep (se 1 (by rfl) ⟨1446416, by rfl⟩ : syracuseStep 1928555 = 2892833) B2892833
theorem B15855871 : Blo 854356 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B24638195 : Blo 854356 24638195 := bstep (se 1 (by rfl) ⟨18478646, by rfl⟩ : syracuseStep 24638195 = 36957293) B36957293
theorem B1930427 : Blo 854356 1930427 := bstep (se 1 (by rfl) ⟨1447820, by rfl⟩ : syracuseStep 1930427 = 2895641) B2895641
theorem B1737775 : Blo 854356 1737775 := bstep (se 1 (by rfl) ⟨1303331, by rfl⟩ : syracuseStep 1737775 = 2606663) B2606663
theorem B1737823 : Blo 854356 1737823 := bstep (se 1 (by rfl) ⟨1303367, by rfl⟩ : syracuseStep 1737823 = 2606735) B2606735
theorem B3245615 : Blo 854356 3245615 := bstep (se 1 (by rfl) ⟨2434211, by rfl⟩ : syracuseStep 3245615 = 4868423) B4868423
theorem B44533327 : Blo 854356 44533327 := bstep (se 1 (by rfl) ⟨33399995, by rfl⟩ : syracuseStep 44533327 = 66799991) B66799991
theorem B854479 : Blo 854356 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B854683 : Blo 854356 854683 := bstep (se 1 (by rfl) ⟨641012, by rfl⟩ : syracuseStep 854683 = 1282025) B1282025
theorem B6491501 : Blo 854356 6491501 := bstep (se 3 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 6491501 = 2434313) B2434313
theorem B855743 : Blo 854356 855743 := bstep (se 1 (by rfl) ⟨641807, by rfl⟩ : syracuseStep 855743 = 1283615) B1283615
theorem B856231 : Blo 854356 856231 := bstep (se 1 (by rfl) ⟨642173, by rfl⟩ : syracuseStep 856231 = 1284347) B1284347
theorem B857447 : Blo 854356 857447 := bstep (se 1 (by rfl) ⟨643085, by rfl⟩ : syracuseStep 857447 = 1286171) B1286171
theorem B18486953 : Blo 854356 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B21141161 : Blo 854356 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B858271 : Blo 854356 858271 := bstep (se 1 (by rfl) ⟨643703, by rfl⟩ : syracuseStep 858271 = 1287407) B1287407
theorem B2889917 : Blo 854356 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B6494417 : Blo 854356 6494417 := bstep (se 2 (by rfl) ⟨2435406, by rfl⟩ : syracuseStep 6494417 = 4870813) B4870813
theorem B4233725 : Blo 854356 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B1284863 : Blo 854356 1284863 := bstep (se 1 (by rfl) ⟨963647, by rfl⟩ : syracuseStep 1284863 = 1927295) B1927295
theorem B16489979 : Blo 854356 16489979 := bstep (se 1 (by rfl) ⟨12367484, by rfl⟩ : syracuseStep 16489979 = 24734969) B24734969
theorem B1285703 : Blo 854356 1285703 := bstep (se 1 (by rfl) ⟨964277, by rfl⟩ : syracuseStep 1285703 = 1928555) B1928555
theorem B16425463 : Blo 854356 16425463 := bstep (se 1 (by rfl) ⟨12319097, by rfl⟩ : syracuseStep 16425463 = 24638195) B24638195
theorem B1286951 : Blo 854356 1286951 := bstep (se 1 (by rfl) ⟨965213, by rfl⟩ : syracuseStep 1286951 = 1930427) B1930427
theorem B12331673 : Blo 854356 12331673 := bstep (se 2 (by rfl) ⟨4624377, by rfl⟩ : syracuseStep 12331673 = 9248755) B9248755
theorem B4337711 : Blo 854356 4337711 := bstep (se 1 (by rfl) ⟨3253283, by rfl⟩ : syracuseStep 4337711 = 6506567) B6506567
theorem B4339007 : Blo 854356 4339007 := bstep (se 1 (by rfl) ⟨3254255, by rfl⟩ : syracuseStep 4339007 = 6508511) B6508511
theorem B2476511 : Blo 854356 2476511 := bstep (se 1 (by rfl) ⟨1857383, by rfl⟩ : syracuseStep 2476511 = 3714767) B3714767
theorem B6934943 : Blo 854356 6934943 := bstep (se 1 (by rfl) ⟨5201207, by rfl⟩ : syracuseStep 6934943 = 10402415) B10402415
theorem B1626779 : Blo 854356 1626779 := bstep (se 1 (by rfl) ⟨1220084, by rfl⟩ : syracuseStep 1626779 = 2440169) B2440169
theorem B1923119 : Blo 854356 1923119 := bstep (se 1 (by rfl) ⟨1442339, by rfl⟩ : syracuseStep 1923119 = 2884679) B2884679
theorem B1924073 : Blo 854356 1924073 := bstep (se 2 (by rfl) ⟨721527, by rfl⟩ : syracuseStep 1924073 = 1443055) B1443055
theorem B150232639 : Blo 854356 150232639 := bstep (se 1 (by rfl) ⟨112674479, by rfl⟩ : syracuseStep 150232639 = 225348959) B225348959
theorem B2973287 : Blo 854356 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B62643905 : Blo 854356 62643905 := bstep (se 2 (by rfl) ⟨23491464, by rfl⟩ : syracuseStep 62643905 = 46982929) B46982929
theorem B1925567 : Blo 854356 1925567 := bstep (se 1 (by rfl) ⟨1444175, by rfl⟩ : syracuseStep 1925567 = 2888351) B2888351
theorem B4874687 : Blo 854356 4874687 := bstep (se 1 (by rfl) ⟨3656015, by rfl⟩ : syracuseStep 4874687 = 7312031) B7312031
theorem B2057663 : Blo 854356 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B31647257 : Blo 854356 31647257 := bstep (se 2 (by rfl) ⟨11867721, by rfl⟩ : syracuseStep 31647257 = 23735443) B23735443
theorem B2320127 : Blo 854356 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B18543005 : Blo 854356 18543005 := bstep (se 3 (by rfl) ⟨3476813, by rfl⟩ : syracuseStep 18543005 = 6953627) B6953627
theorem B39515161 : Blo 854356 39515161 := bstep (se 2 (by rfl) ⟨14818185, by rfl⟩ : syracuseStep 39515161 = 29636371) B29636371
theorem B1668431 : Blo 854356 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B1735487 : Blo 854356 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B2163743 : Blo 854356 2163743 := bstep (se 1 (by rfl) ⟨1622807, by rfl⟩ : syracuseStep 2163743 = 3245615) B3245615
theorem B59377769 : Blo 854356 59377769 := bstep (se 2 (by rfl) ⟨22266663, by rfl⟩ : syracuseStep 59377769 = 44533327) B44533327
theorem B4327667 : Blo 854356 4327667 := bstep (se 1 (by rfl) ⟨3245750, by rfl⟩ : syracuseStep 4327667 = 6491501) B6491501
theorem B1084519 : Blo 854356 1084519 := bstep (se 1 (by rfl) ⟨813389, by rfl⟩ : syracuseStep 1084519 = 1626779) B1626779
theorem B12324635 : Blo 854356 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B14094107 : Blo 854356 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B1282079 : Blo 854356 1282079 := bstep (se 1 (by rfl) ⟨961559, by rfl⟩ : syracuseStep 1282079 = 1923119) B1923119
theorem B4329611 : Blo 854356 4329611 := bstep (se 1 (by rfl) ⟨3247208, by rfl⟩ : syracuseStep 4329611 = 6494417) B6494417
theorem B2822483 : Blo 854356 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B856575 : Blo 854356 856575 := bstep (se 1 (by rfl) ⟨642431, by rfl⟩ : syracuseStep 856575 = 1284863) B1284863
theorem B1282715 : Blo 854356 1282715 := bstep (se 1 (by rfl) ⟨962036, by rfl⟩ : syracuseStep 1282715 = 1924073) B1924073
theorem B857135 : Blo 854356 857135 := bstep (se 1 (by rfl) ⟨642851, by rfl⟩ : syracuseStep 857135 = 1285703) B1285703
theorem B1283711 : Blo 854356 1283711 := bstep (se 1 (by rfl) ⟨962783, by rfl⟩ : syracuseStep 1283711 = 1925567) B1925567
theorem B3249791 : Blo 854356 3249791 := bstep (se 1 (by rfl) ⟨2437343, by rfl⟩ : syracuseStep 3249791 = 4874687) B4874687
theorem B857967 : Blo 854356 857967 := bstep (se 1 (by rfl) ⟨643475, by rfl⟩ : syracuseStep 857967 = 1286951) B1286951
theorem B1546751 : Blo 854356 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B2891807 : Blo 854356 2891807 := bstep (se 1 (by rfl) ⟨2168855, by rfl⟩ : syracuseStep 2891807 = 4337711) B4337711
theorem B12362003 : Blo 854356 12362003 := bstep (se 1 (by rfl) ⟨9271502, by rfl⟩ : syracuseStep 12362003 = 18543005) B18543005
theorem B2892671 : Blo 854356 2892671 := bstep (se 1 (by rfl) ⟨2169503, by rfl⟩ : syracuseStep 2892671 = 4339007) B4339007
theorem B21900617 : Blo 854356 21900617 := bstep (se 2 (by rfl) ⟨8212731, by rfl⟩ : syracuseStep 21900617 = 16425463) B16425463
theorem B18493181 : Blo 854356 18493181 := bstep (se 3 (by rfl) ⟨3467471, by rfl⟩ : syracuseStep 18493181 = 6934943) B6934943
theorem B1651007 : Blo 854356 1651007 := bstep (se 1 (by rfl) ⟨1238255, by rfl⟩ : syracuseStep 1651007 = 2476511) B2476511
theorem B5487101 : Blo 854356 5487101 := bstep (se 3 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 5487101 = 2057663) B2057663
theorem B10993319 : Blo 854356 10993319 := bstep (se 1 (by rfl) ⟨8244989, by rfl⟩ : syracuseStep 10993319 = 16489979) B16489979
theorem B41762603 : Blo 854356 41762603 := bstep (se 1 (by rfl) ⟨31321952, by rfl⟩ : syracuseStep 41762603 = 62643905) B62643905
theorem B2317033 : Blo 854356 2317033 := bstep (se 2 (by rfl) ⟨868887, by rfl⟩ : syracuseStep 2317033 = 1737775) B1737775
theorem B2317097 : Blo 854356 2317097 := bstep (se 2 (by rfl) ⟨868911, by rfl⟩ : syracuseStep 2317097 = 1737823) B1737823
theorem B74047445 : Blo 854356 74047445 := bstep (se 7 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 74047445 = 1735487) B1735487
theorem B4449149 : Blo 854356 4449149 := bstep (se 3 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 4449149 = 1668431) B1668431
theorem B1926611 : Blo 854356 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B21098171 : Blo 854356 21098171 := bstep (se 1 (by rfl) ⟨15823628, by rfl⟩ : syracuseStep 21098171 = 31647257) B31647257
theorem B52686881 : Blo 854356 52686881 := bstep (se 2 (by rfl) ⟨19757580, by rfl⟩ : syracuseStep 52686881 = 39515161) B39515161
theorem B8221115 : Blo 854356 8221115 := bstep (se 1 (by rfl) ⟨6165836, by rfl⟩ : syracuseStep 8221115 = 12331673) B12331673
theorem B7928765 : Blo 854356 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B200310185 : Blo 854356 200310185 := bstep (se 2 (by rfl) ⟨75116319, by rfl⟩ : syracuseStep 200310185 = 150232639) B150232639
theorem B1442495 : Blo 854356 1442495 := bstep (se 1 (by rfl) ⟨1081871, by rfl⟩ : syracuseStep 1442495 = 2163743) B2163743
theorem B39585179 : Blo 854356 39585179 := bstep (se 1 (by rfl) ⟨29688884, by rfl⟩ : syracuseStep 39585179 = 59377769) B59377769
theorem B2885111 : Blo 854356 2885111 := bstep (se 1 (by rfl) ⟨2163833, by rfl⟩ : syracuseStep 2885111 = 4327667) B4327667
theorem B854719 : Blo 854356 854719 := bstep (se 1 (by rfl) ⟨641039, by rfl⟩ : syracuseStep 854719 = 1282079) B1282079
theorem B2886407 : Blo 854356 2886407 := bstep (se 1 (by rfl) ⟨2164805, by rfl⟩ : syracuseStep 2886407 = 4329611) B4329611
theorem B855143 : Blo 854356 855143 := bstep (se 1 (by rfl) ⟨641357, by rfl⟩ : syracuseStep 855143 = 1282715) B1282715
theorem B855807 : Blo 854356 855807 := bstep (se 1 (by rfl) ⟨641855, by rfl⟩ : syracuseStep 855807 = 1283711) B1283711
theorem B2166527 : Blo 854356 2166527 := bstep (se 1 (by rfl) ⟨1624895, by rfl⟩ : syracuseStep 2166527 = 3249791) B3249791
theorem B1446025 : Blo 854356 1446025 := bstep (se 2 (by rfl) ⟨542259, by rfl⟩ : syracuseStep 1446025 = 1084519) B1084519
theorem B1284407 : Blo 854356 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B14065447 : Blo 854356 14065447 := bstep (se 1 (by rfl) ⟨10549085, by rfl⟩ : syracuseStep 14065447 = 21098171) B21098171
theorem B12328787 : Blo 854356 12328787 := bstep (se 1 (by rfl) ⟨9246590, by rfl⟩ : syracuseStep 12328787 = 18493181) B18493181
theorem B5480743 : Blo 854356 5480743 := bstep (se 1 (by rfl) ⟨4110557, by rfl⟩ : syracuseStep 5480743 = 8221115) B8221115
theorem B3089377 : Blo 854356 3089377 := bstep (se 2 (by rfl) ⟨1158516, by rfl⟩ : syracuseStep 3089377 = 2317033) B2317033
theorem B5285843 : Blo 854356 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B133540123 : Blo 854356 133540123 := bstep (se 1 (by rfl) ⟨100155092, by rfl⟩ : syracuseStep 133540123 = 200310185) B200310185
theorem B1031167 : Blo 854356 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B49364963 : Blo 854356 49364963 := bstep (se 1 (by rfl) ⟨37023722, by rfl⟩ : syracuseStep 49364963 = 74047445) B74047445
theorem B8241335 : Blo 854356 8241335 := bstep (se 1 (by rfl) ⟨6181001, by rfl⟩ : syracuseStep 8241335 = 12362003) B12362003
theorem B2966099 : Blo 854356 2966099 := bstep (se 1 (by rfl) ⟨2224574, by rfl⟩ : syracuseStep 2966099 = 4449149) B4449149
theorem B6178925 : Blo 854356 6178925 := bstep (se 3 (by rfl) ⟨1158548, by rfl⟩ : syracuseStep 6178925 = 2317097) B2317097
theorem B14600411 : Blo 854356 14600411 := bstep (se 1 (by rfl) ⟨10950308, by rfl⟩ : syracuseStep 14600411 = 21900617) B21900617
theorem B1100671 : Blo 854356 1100671 := bstep (se 1 (by rfl) ⟨825503, by rfl⟩ : syracuseStep 1100671 = 1651007) B1651007
theorem B3658067 : Blo 854356 3658067 := bstep (se 1 (by rfl) ⟨2743550, by rfl⟩ : syracuseStep 3658067 = 5487101) B5487101
theorem B7328879 : Blo 854356 7328879 := bstep (se 1 (by rfl) ⟨5496659, by rfl⟩ : syracuseStep 7328879 = 10993319) B10993319
theorem B27841735 : Blo 854356 27841735 := bstep (se 1 (by rfl) ⟨20881301, by rfl⟩ : syracuseStep 27841735 = 41762603) B41762603
theorem B7526621 : Blo 854356 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B8216423 : Blo 854356 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B9396071 : Blo 854356 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B1927871 : Blo 854356 1927871 := bstep (se 1 (by rfl) ⟨1445903, by rfl⟩ : syracuseStep 1927871 = 2891807) B2891807
theorem B1928447 : Blo 854356 1928447 := bstep (se 1 (by rfl) ⟨1446335, by rfl⟩ : syracuseStep 1928447 = 2892671) B2892671
theorem B35124587 : Blo 854356 35124587 := bstep (se 1 (by rfl) ⟨26343440, by rfl⟩ : syracuseStep 35124587 = 52686881) B52686881
theorem B7307657 : Blo 854356 7307657 := bstep (se 2 (by rfl) ⟨2740371, by rfl⟩ : syracuseStep 7307657 = 5480743) B5480743
theorem B9733607 : Blo 854356 9733607 := bstep (se 1 (by rfl) ⟨7300205, by rfl⟩ : syracuseStep 9733607 = 14600411) B14600411
theorem B1444351 : Blo 854356 1444351 := bstep (se 1 (by rfl) ⟨1083263, by rfl⟩ : syracuseStep 1444351 = 2166527) B2166527
theorem B4885919 : Blo 854356 4885919 := bstep (se 1 (by rfl) ⟨3664439, by rfl⟩ : syracuseStep 4885919 = 7328879) B7328879
theorem B856271 : Blo 854356 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B5870245 : Blo 854356 5870245 := bstep (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) B1100671
theorem B5477615 : Blo 854356 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B6264047 : Blo 854356 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B1285247 : Blo 854356 1285247 := bstep (se 1 (by rfl) ⟨963935, by rfl⟩ : syracuseStep 1285247 = 1927871) B1927871
theorem B1285631 : Blo 854356 1285631 := bstep (se 1 (by rfl) ⟨964223, by rfl⟩ : syracuseStep 1285631 = 1928447) B1928447
theorem B18753929 : Blo 854356 18753929 := bstep (se 2 (by rfl) ⟨7032723, by rfl⟩ : syracuseStep 18753929 = 14065447) B14065447
theorem B32909975 : Blo 854356 32909975 := bstep (se 1 (by rfl) ⟨24682481, by rfl⟩ : syracuseStep 32909975 = 49364963) B49364963
theorem B961663 : Blo 854356 961663 := bstep (se 1 (by rfl) ⟨721247, by rfl⟩ : syracuseStep 961663 = 1442495) B1442495
theorem B26390119 : Blo 854356 26390119 := bstep (se 1 (by rfl) ⟨19792589, by rfl⟩ : syracuseStep 26390119 = 39585179) B39585179
theorem B7909597 : Blo 854356 7909597 := bstep (se 3 (by rfl) ⟨1483049, by rfl⟩ : syracuseStep 7909597 = 2966099) B2966099
theorem B2438711 : Blo 854356 2438711 := bstep (se 1 (by rfl) ⟨1829033, by rfl⟩ : syracuseStep 2438711 = 3658067) B3658067
theorem B20070989 : Blo 854356 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B3523895 : Blo 854356 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B23416391 : Blo 854356 23416391 := bstep (se 1 (by rfl) ⟨17562293, by rfl⟩ : syracuseStep 23416391 = 35124587) B35124587
theorem B5494223 : Blo 854356 5494223 := bstep (se 1 (by rfl) ⟨4120667, by rfl⟩ : syracuseStep 5494223 = 8241335) B8241335
theorem B1923407 : Blo 854356 1923407 := bstep (se 1 (by rfl) ⟨1442555, by rfl⟩ : syracuseStep 1923407 = 2885111) B2885111
theorem B4119169 : Blo 854356 4119169 := bstep (se 2 (by rfl) ⟨1544688, by rfl⟩ : syracuseStep 4119169 = 3089377) B3089377
theorem B4119283 : Blo 854356 4119283 := bstep (se 1 (by rfl) ⟨3089462, by rfl⟩ : syracuseStep 4119283 = 6178925) B6178925
theorem B1924271 : Blo 854356 1924271 := bstep (se 1 (by rfl) ⟨1443203, by rfl⟩ : syracuseStep 1924271 = 2886407) B2886407
theorem B178053497 : Blo 854356 178053497 := bstep (se 2 (by rfl) ⟨66770061, by rfl⟩ : syracuseStep 178053497 = 133540123) B133540123
theorem B8219191 : Blo 854356 8219191 := bstep (se 1 (by rfl) ⟨6164393, by rfl⟩ : syracuseStep 8219191 = 12328787) B12328787
theorem B1928033 : Blo 854356 1928033 := bstep (se 2 (by rfl) ⟨723012, by rfl⟩ : syracuseStep 1928033 = 1446025) B1446025
theorem B37122313 : Blo 854356 37122313 := bstep (se 2 (by rfl) ⟨13920867, by rfl⟩ : syracuseStep 37122313 = 27841735) B27841735
theorem B1374889 : Blo 854356 1374889 := bstep (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) B1031167
theorem B6489071 : Blo 854356 6489071 := bstep (se 1 (by rfl) ⟨4866803, by rfl⟩ : syracuseStep 6489071 = 9733607) B9733607
theorem B1282217 : Blo 854356 1282217 := bstep (se 2 (by rfl) ⟨480831, by rfl⟩ : syracuseStep 1282217 = 961663) B961663
theorem B1282271 : Blo 854356 1282271 := bstep (se 1 (by rfl) ⟨961703, by rfl⟩ : syracuseStep 1282271 = 1923407) B1923407
theorem B856831 : Blo 854356 856831 := bstep (se 1 (by rfl) ⟨642623, by rfl⟩ : syracuseStep 856831 = 1285247) B1285247
theorem B1282847 : Blo 854356 1282847 := bstep (se 1 (by rfl) ⟨962135, by rfl⟩ : syracuseStep 1282847 = 1924271) B1924271
theorem B857087 : Blo 854356 857087 := bstep (se 1 (by rfl) ⟨642815, by rfl⟩ : syracuseStep 857087 = 1285631) B1285631
theorem B1285355 : Blo 854356 1285355 := bstep (se 1 (by rfl) ⟨964016, by rfl⟩ : syracuseStep 1285355 = 1928033) B1928033
theorem B13380659 : Blo 854356 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B3257279 : Blo 854356 3257279 := bstep (se 1 (by rfl) ⟨2442959, by rfl⟩ : syracuseStep 3257279 = 4885919) B4885919
theorem B15610927 : Blo 854356 15610927 := bstep (se 1 (by rfl) ⟨11708195, by rfl⟩ : syracuseStep 15610927 = 23416391) B23416391
theorem B10958921 : Blo 854356 10958921 := bstep (se 2 (by rfl) ⟨4109595, by rfl⟩ : syracuseStep 10958921 = 8219191) B8219191
theorem B3651743 : Blo 854356 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B4176031 : Blo 854356 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B118702331 : Blo 854356 118702331 := bstep (se 1 (by rfl) ⟨89026748, by rfl⟩ : syracuseStep 118702331 = 178053497) B178053497
theorem B49496417 : Blo 854356 49496417 := bstep (se 2 (by rfl) ⟨18561156, by rfl⟩ : syracuseStep 49496417 = 37122313) B37122313
theorem B12502619 : Blo 854356 12502619 := bstep (se 1 (by rfl) ⟨9376964, by rfl⟩ : syracuseStep 12502619 = 18753929) B18753929
theorem B21939983 : Blo 854356 21939983 := bstep (se 1 (by rfl) ⟨16454987, by rfl⟩ : syracuseStep 21939983 = 32909975) B32909975
theorem B5492225 : Blo 854356 5492225 := bstep (se 2 (by rfl) ⟨2059584, by rfl⟩ : syracuseStep 5492225 = 4119169) B4119169
theorem B5492377 : Blo 854356 5492377 := bstep (se 2 (by rfl) ⟨2059641, by rfl⟩ : syracuseStep 5492377 = 4119283) B4119283
theorem B1625807 : Blo 854356 1625807 := bstep (se 1 (by rfl) ⟨1219355, by rfl⟩ : syracuseStep 1625807 = 2438711) B2438711
theorem B4871771 : Blo 854356 4871771 := bstep (se 1 (by rfl) ⟨3653828, by rfl⟩ : syracuseStep 4871771 = 7307657) B7307657
theorem B2349263 : Blo 854356 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B1925801 : Blo 854356 1925801 := bstep (se 2 (by rfl) ⟨722175, by rfl⟩ : syracuseStep 1925801 = 1444351) B1444351
theorem B3662815 : Blo 854356 3662815 := bstep (se 1 (by rfl) ⟨2747111, by rfl⟩ : syracuseStep 3662815 = 5494223) B5494223
theorem B35186825 : Blo 854356 35186825 := bstep (se 2 (by rfl) ⟨13195059, by rfl⟩ : syracuseStep 35186825 = 26390119) B26390119
theorem B10546129 : Blo 854356 10546129 := bstep (se 2 (by rfl) ⟨3954798, by rfl⟩ : syracuseStep 10546129 = 7909597) B7909597
theorem B7826993 : Blo 854356 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B1833185 : Blo 854356 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B79134887 : Blo 854356 79134887 := bstep (se 1 (by rfl) ⟨59351165, by rfl⟩ : syracuseStep 79134887 = 118702331) B118702331
theorem B32997611 : Blo 854356 32997611 := bstep (se 1 (by rfl) ⟨24748208, by rfl⟩ : syracuseStep 32997611 = 49496417) B49496417
theorem B4326047 : Blo 854356 4326047 := bstep (se 1 (by rfl) ⟨3244535, by rfl⟩ : syracuseStep 4326047 = 6489071) B6489071
theorem B4883753 : Blo 854356 4883753 := bstep (se 2 (by rfl) ⟨1831407, by rfl⟩ : syracuseStep 4883753 = 3662815) B3662815
theorem B1083871 : Blo 854356 1083871 := bstep (se 1 (by rfl) ⟨812903, by rfl⟩ : syracuseStep 1083871 = 1625807) B1625807
theorem B854811 : Blo 854356 854811 := bstep (se 1 (by rfl) ⟨641108, by rfl⟩ : syracuseStep 854811 = 1282217) B1282217
theorem B854847 : Blo 854356 854847 := bstep (se 1 (by rfl) ⟨641135, by rfl⟩ : syracuseStep 854847 = 1282271) B1282271
theorem B855231 : Blo 854356 855231 := bstep (se 1 (by rfl) ⟨641423, by rfl⟩ : syracuseStep 855231 = 1282847) B1282847
theorem B3247847 : Blo 854356 3247847 := bstep (se 1 (by rfl) ⟨2435885, by rfl⟩ : syracuseStep 3247847 = 4871771) B4871771
theorem B14061505 : Blo 854356 14061505 := bstep (se 2 (by rfl) ⟨5273064, by rfl⟩ : syracuseStep 14061505 = 10546129) B10546129
theorem B856903 : Blo 854356 856903 := bstep (se 1 (by rfl) ⟨642677, by rfl⟩ : syracuseStep 856903 = 1285355) B1285355
theorem B9737981 : Blo 854356 9737981 := bstep (se 3 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 9737981 = 3651743) B3651743
theorem B1283867 : Blo 854356 1283867 := bstep (se 1 (by rfl) ⟨962900, by rfl⟩ : syracuseStep 1283867 = 1925801) B1925801
theorem B20814569 : Blo 854356 20814569 := bstep (se 2 (by rfl) ⟨7805463, by rfl⟩ : syracuseStep 20814569 = 15610927) B15610927
theorem B8920439 : Blo 854356 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B5217995 : Blo 854356 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B2171519 : Blo 854356 2171519 := bstep (se 1 (by rfl) ⟨1628639, by rfl⟩ : syracuseStep 2171519 = 3257279) B3257279
theorem B1222123 : Blo 854356 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B8335079 : Blo 854356 8335079 := bstep (se 1 (by rfl) ⟨6251309, by rfl⟩ : syracuseStep 8335079 = 12502619) B12502619
theorem B14626655 : Blo 854356 14626655 := bstep (se 1 (by rfl) ⟨10969991, by rfl⟩ : syracuseStep 14626655 = 21939983) B21939983
theorem B7323169 : Blo 854356 7323169 := bstep (se 2 (by rfl) ⟨2746188, by rfl⟩ : syracuseStep 7323169 = 5492377) B5492377
theorem B3661483 : Blo 854356 3661483 := bstep (se 1 (by rfl) ⟨2746112, by rfl⟩ : syracuseStep 3661483 = 5492225) B5492225
theorem B1566175 : Blo 854356 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B23457883 : Blo 854356 23457883 := bstep (se 1 (by rfl) ⟨17593412, by rfl⟩ : syracuseStep 23457883 = 35186825) B35186825
theorem B5568041 : Blo 854356 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B7305947 : Blo 854356 7305947 := bstep (se 1 (by rfl) ⟨5479460, by rfl⟩ : syracuseStep 7305947 = 10958921) B10958921
theorem B52756591 : Blo 854356 52756591 := bstep (se 1 (by rfl) ⟨39567443, by rfl⟩ : syracuseStep 52756591 = 79134887) B79134887
theorem B2884031 : Blo 854356 2884031 := bstep (se 1 (by rfl) ⟨2163023, by rfl⟩ : syracuseStep 2884031 = 4326047) B4326047
theorem B2165231 : Blo 854356 2165231 := bstep (se 1 (by rfl) ⟨1623923, by rfl⟩ : syracuseStep 2165231 = 3247847) B3247847
theorem B1445161 : Blo 854356 1445161 := bstep (se 2 (by rfl) ⟨541935, by rfl⟩ : syracuseStep 1445161 = 1083871) B1083871
theorem B6491987 : Blo 854356 6491987 := bstep (se 1 (by rfl) ⟨4868990, by rfl⟩ : syracuseStep 6491987 = 9737981) B9737981
theorem B855911 : Blo 854356 855911 := bstep (se 1 (by rfl) ⟨641933, by rfl⟩ : syracuseStep 855911 = 1283867) B1283867
theorem B14848109 : Blo 854356 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B3478663 : Blo 854356 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B18748673 : Blo 854356 18748673 := bstep (se 2 (by rfl) ⟨7030752, by rfl⟩ : syracuseStep 18748673 = 14061505) B14061505
theorem B1447679 : Blo 854356 1447679 := bstep (se 1 (by rfl) ⟨1085759, by rfl⟩ : syracuseStep 1447679 = 2171519) B2171519
theorem B21998407 : Blo 854356 21998407 := bstep (se 1 (by rfl) ⟨16498805, by rfl⟩ : syracuseStep 21998407 = 32997611) B32997611
theorem B3255835 : Blo 854356 3255835 := bstep (se 1 (by rfl) ⟨2441876, by rfl⟩ : syracuseStep 3255835 = 4883753) B4883753
theorem B13876379 : Blo 854356 13876379 := bstep (se 1 (by rfl) ⟨10407284, by rfl⟩ : syracuseStep 13876379 = 20814569) B20814569
theorem B5946959 : Blo 854356 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B31277177 : Blo 854356 31277177 := bstep (se 2 (by rfl) ⟨11728941, by rfl⟩ : syracuseStep 31277177 = 23457883) B23457883
theorem B5556719 : Blo 854356 5556719 := bstep (se 1 (by rfl) ⟨4167539, by rfl⟩ : syracuseStep 5556719 = 8335079) B8335079
theorem B9751103 : Blo 854356 9751103 := bstep (se 1 (by rfl) ⟨7313327, by rfl⟩ : syracuseStep 9751103 = 14626655) B14626655
theorem B4870631 : Blo 854356 4870631 := bstep (se 1 (by rfl) ⟨3652973, by rfl⟩ : syracuseStep 4870631 = 7305947) B7305947
theorem B2088233 : Blo 854356 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B1629497 : Blo 854356 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B9764225 : Blo 854356 9764225 := bstep (se 2 (by rfl) ⟨3661584, by rfl⟩ : syracuseStep 9764225 = 7323169) B7323169
theorem B4881977 : Blo 854356 4881977 := bstep (se 2 (by rfl) ⟨1830741, by rfl⟩ : syracuseStep 4881977 = 3661483) B3661483
theorem B1443487 : Blo 854356 1443487 := bstep (se 1 (by rfl) ⟨1082615, by rfl⟩ : syracuseStep 1443487 = 2165231) B2165231
theorem B4327991 : Blo 854356 4327991 := bstep (se 1 (by rfl) ⟨3245993, by rfl⟩ : syracuseStep 4327991 = 6491987) B6491987
theorem B9898739 : Blo 854356 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B3247087 : Blo 854356 3247087 := bstep (se 1 (by rfl) ⟨2435315, by rfl⟩ : syracuseStep 3247087 = 4870631) B4870631
theorem B29331209 : Blo 854356 29331209 := bstep (se 2 (by rfl) ⟨10999203, by rfl⟩ : syracuseStep 29331209 = 21998407) B21998407
theorem B14817917 : Blo 854356 14817917 := bstep (se 3 (by rfl) ⟨2778359, by rfl⟩ : syracuseStep 14817917 = 5556719) B5556719
theorem B9250919 : Blo 854356 9250919 := bstep (se 1 (by rfl) ⟨6938189, by rfl⟩ : syracuseStep 9250919 = 13876379) B13876379
theorem B3254651 : Blo 854356 3254651 := bstep (se 1 (by rfl) ⟨2440988, by rfl⟩ : syracuseStep 3254651 = 4881977) B4881977
theorem B20851451 : Blo 854356 20851451 := bstep (se 1 (by rfl) ⟨15638588, by rfl⟩ : syracuseStep 20851451 = 31277177) B31277177
theorem B6500735 : Blo 854356 6500735 := bstep (se 1 (by rfl) ⟨4875551, by rfl⟩ : syracuseStep 6500735 = 9751103) B9751103
theorem B12499115 : Blo 854356 12499115 := bstep (se 1 (by rfl) ⟨9374336, by rfl⟩ : syracuseStep 12499115 = 18748673) B18748673
theorem B965119 : Blo 854356 965119 := bstep (se 1 (by rfl) ⟨723839, by rfl⟩ : syracuseStep 965119 = 1447679) B1447679
theorem B4341113 : Blo 854356 4341113 := bstep (se 2 (by rfl) ⟨1627917, by rfl⟩ : syracuseStep 4341113 = 3255835) B3255835
theorem B1392155 : Blo 854356 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B4638217 : Blo 854356 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B4345325 : Blo 854356 4345325 := bstep (se 3 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 4345325 = 1629497) B1629497
theorem B6509483 : Blo 854356 6509483 := bstep (se 1 (by rfl) ⟨4882112, by rfl⟩ : syracuseStep 6509483 = 9764225) B9764225
theorem B70342121 : Blo 854356 70342121 := bstep (se 2 (by rfl) ⟨26378295, by rfl⟩ : syracuseStep 70342121 = 52756591) B52756591
theorem B1922687 : Blo 854356 1922687 := bstep (se 1 (by rfl) ⟨1442015, by rfl⟩ : syracuseStep 1922687 = 2884031) B2884031
theorem B1926881 : Blo 854356 1926881 := bstep (se 2 (by rfl) ⟨722580, by rfl⟩ : syracuseStep 1926881 = 1445161) B1445161
theorem B3964639 : Blo 854356 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B2885327 : Blo 854356 2885327 := bstep (se 1 (by rfl) ⟨2163995, by rfl⟩ : syracuseStep 2885327 = 4327991) B4327991
theorem B46894747 : Blo 854356 46894747 := bstep (se 1 (by rfl) ⟨35171060, by rfl⟩ : syracuseStep 46894747 = 70342121) B70342121
theorem B1281791 : Blo 854356 1281791 := bstep (se 1 (by rfl) ⟨961343, by rfl⟩ : syracuseStep 1281791 = 1922687) B1922687
theorem B4329449 : Blo 854356 4329449 := bstep (se 2 (by rfl) ⟨1623543, by rfl⟩ : syracuseStep 4329449 = 3247087) B3247087
theorem B33330973 : Blo 854356 33330973 := bstep (se 3 (by rfl) ⟨6249557, by rfl⟩ : syracuseStep 33330973 = 12499115) B12499115
theorem B1284587 : Blo 854356 1284587 := bstep (se 1 (by rfl) ⟨963440, by rfl⟩ : syracuseStep 1284587 = 1926881) B1926881
theorem B6167279 : Blo 854356 6167279 := bstep (se 1 (by rfl) ⟨4625459, by rfl⟩ : syracuseStep 6167279 = 9250919) B9250919
theorem B2169767 : Blo 854356 2169767 := bstep (se 1 (by rfl) ⟨1627325, by rfl⟩ : syracuseStep 2169767 = 3254651) B3254651
theorem B13900967 : Blo 854356 13900967 := bstep (se 1 (by rfl) ⟨10425725, by rfl⟩ : syracuseStep 13900967 = 20851451) B20851451
theorem B4333823 : Blo 854356 4333823 := bstep (se 1 (by rfl) ⟨3250367, by rfl⟩ : syracuseStep 4333823 = 6500735) B6500735
theorem B1286825 : Blo 854356 1286825 := bstep (se 2 (by rfl) ⟨482559, by rfl⟩ : syracuseStep 1286825 = 965119) B965119
theorem B2894075 : Blo 854356 2894075 := bstep (se 1 (by rfl) ⟨2170556, by rfl⟩ : syracuseStep 2894075 = 4341113) B4341113
theorem B5286185 : Blo 854356 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B928103 : Blo 854356 928103 := bstep (se 1 (by rfl) ⟨696077, by rfl⟩ : syracuseStep 928103 = 1392155) B1392155
theorem B6599159 : Blo 854356 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B2896883 : Blo 854356 2896883 := bstep (se 1 (by rfl) ⟨2172662, by rfl⟩ : syracuseStep 2896883 = 4345325) B4345325
theorem B4339655 : Blo 854356 4339655 := bstep (se 1 (by rfl) ⟨3254741, by rfl⟩ : syracuseStep 4339655 = 6509483) B6509483
theorem B9878611 : Blo 854356 9878611 := bstep (se 1 (by rfl) ⟨7408958, by rfl⟩ : syracuseStep 9878611 = 14817917) B14817917
theorem B6184289 : Blo 854356 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B1924649 : Blo 854356 1924649 := bstep (se 2 (by rfl) ⟨721743, by rfl⟩ : syracuseStep 1924649 = 1443487) B1443487
theorem B19554139 : Blo 854356 19554139 := bstep (se 1 (by rfl) ⟨14665604, by rfl⟩ : syracuseStep 19554139 = 29331209) B29331209
theorem B854527 : Blo 854356 854527 := bstep (se 1 (by rfl) ⟨640895, by rfl⟩ : syracuseStep 854527 = 1281791) B1281791
theorem B2886299 : Blo 854356 2886299 := bstep (se 1 (by rfl) ⟨2164724, by rfl⟩ : syracuseStep 2886299 = 4329449) B4329449
theorem B9899765 : Blo 854356 9899765 := bstep (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) B928103
theorem B856391 : Blo 854356 856391 := bstep (se 1 (by rfl) ⟨642293, by rfl⟩ : syracuseStep 856391 = 1284587) B1284587
theorem B1446511 : Blo 854356 1446511 := bstep (se 1 (by rfl) ⟨1084883, by rfl⟩ : syracuseStep 1446511 = 2169767) B2169767
theorem B62526329 : Blo 854356 62526329 := bstep (se 2 (by rfl) ⟨23447373, by rfl⟩ : syracuseStep 62526329 = 46894747) B46894747
theorem B1283099 : Blo 854356 1283099 := bstep (se 1 (by rfl) ⟨962324, by rfl⟩ : syracuseStep 1283099 = 1924649) B1924649
theorem B2889215 : Blo 854356 2889215 := bstep (se 1 (by rfl) ⟨2166911, by rfl⟩ : syracuseStep 2889215 = 4333823) B4333823
theorem B857883 : Blo 854356 857883 := bstep (se 1 (by rfl) ⟨643412, by rfl⟩ : syracuseStep 857883 = 1286825) B1286825
theorem B44441297 : Blo 854356 44441297 := bstep (se 2 (by rfl) ⟨16665486, by rfl⟩ : syracuseStep 44441297 = 33330973) B33330973
theorem B4399439 : Blo 854356 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B16491437 : Blo 854356 16491437 := bstep (se 3 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 16491437 = 6184289) B6184289
theorem B2893103 : Blo 854356 2893103 := bstep (se 1 (by rfl) ⟨2169827, by rfl⟩ : syracuseStep 2893103 = 4339655) B4339655
theorem B4111519 : Blo 854356 4111519 := bstep (se 1 (by rfl) ⟨3083639, by rfl⟩ : syracuseStep 4111519 = 6167279) B6167279
theorem B3524123 : Blo 854356 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B104288741 : Blo 854356 104288741 := bstep (se 4 (by rfl) ⟨9777069, by rfl⟩ : syracuseStep 104288741 = 19554139) B19554139
theorem B1923551 : Blo 854356 1923551 := bstep (se 1 (by rfl) ⟨1442663, by rfl⟩ : syracuseStep 1923551 = 2885327) B2885327
theorem B9267311 : Blo 854356 9267311 := bstep (se 1 (by rfl) ⟨6950483, by rfl⟩ : syracuseStep 9267311 = 13900967) B13900967
theorem B1929383 : Blo 854356 1929383 := bstep (se 1 (by rfl) ⟨1447037, by rfl⟩ : syracuseStep 1929383 = 2894075) B2894075
theorem B1931255 : Blo 854356 1931255 := bstep (se 1 (by rfl) ⟨1448441, by rfl⟩ : syracuseStep 1931255 = 2896883) B2896883
theorem B13171481 : Blo 854356 13171481 := bstep (se 2 (by rfl) ⟨4939305, by rfl⟩ : syracuseStep 13171481 = 9878611) B9878611
theorem B41684219 : Blo 854356 41684219 := bstep (se 1 (by rfl) ⟨31263164, by rfl⟩ : syracuseStep 41684219 = 62526329) B62526329
theorem B855399 : Blo 854356 855399 := bstep (se 1 (by rfl) ⟨641549, by rfl⟩ : syracuseStep 855399 = 1283099) B1283099
theorem B46927349 : Blo 854356 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B1282367 : Blo 854356 1282367 := bstep (se 1 (by rfl) ⟨961775, by rfl⟩ : syracuseStep 1282367 = 1923551) B1923551
theorem B29627531 : Blo 854356 29627531 := bstep (se 1 (by rfl) ⟨22220648, by rfl⟩ : syracuseStep 29627531 = 44441297) B44441297
theorem B1286255 : Blo 854356 1286255 := bstep (se 1 (by rfl) ⟨964691, by rfl⟩ : syracuseStep 1286255 = 1929383) B1929383
theorem B1287503 : Blo 854356 1287503 := bstep (se 1 (by rfl) ⟨965627, by rfl⟩ : syracuseStep 1287503 = 1931255) B1931255
theorem B5482025 : Blo 854356 5482025 := bstep (se 2 (by rfl) ⟨2055759, by rfl⟩ : syracuseStep 5482025 = 4111519) B4111519
theorem B6599843 : Blo 854356 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B10994291 : Blo 854356 10994291 := bstep (se 1 (by rfl) ⟨8245718, by rfl⟩ : syracuseStep 10994291 = 16491437) B16491437
theorem B6178207 : Blo 854356 6178207 := bstep (se 1 (by rfl) ⟨4633655, by rfl⟩ : syracuseStep 6178207 = 9267311) B9267311
theorem B2349415 : Blo 854356 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B1924199 : Blo 854356 1924199 := bstep (se 1 (by rfl) ⟨1443149, by rfl⟩ : syracuseStep 1924199 = 2886299) B2886299
theorem B69525827 : Blo 854356 69525827 := bstep (se 1 (by rfl) ⟨52144370, by rfl⟩ : syracuseStep 69525827 = 104288741) B104288741
theorem B1926143 : Blo 854356 1926143 := bstep (se 1 (by rfl) ⟨1444607, by rfl⟩ : syracuseStep 1926143 = 2889215) B2889215
theorem B1928681 : Blo 854356 1928681 := bstep (se 2 (by rfl) ⟨723255, by rfl⟩ : syracuseStep 1928681 = 1446511) B1446511
theorem B1928735 : Blo 854356 1928735 := bstep (se 1 (by rfl) ⟨1446551, by rfl⟩ : syracuseStep 1928735 = 2893103) B2893103
theorem B8780987 : Blo 854356 8780987 := bstep (se 1 (by rfl) ⟨6585740, by rfl⟩ : syracuseStep 8780987 = 13171481) B13171481
theorem B27789479 : Blo 854356 27789479 := bstep (se 1 (by rfl) ⟨20842109, by rfl⟩ : syracuseStep 27789479 = 41684219) B41684219
theorem B854911 : Blo 854356 854911 := bstep (se 1 (by rfl) ⟨641183, by rfl⟩ : syracuseStep 854911 = 1282367) B1282367
theorem B1282799 : Blo 854356 1282799 := bstep (se 1 (by rfl) ⟨962099, by rfl⟩ : syracuseStep 1282799 = 1924199) B1924199
theorem B857503 : Blo 854356 857503 := bstep (se 1 (by rfl) ⟨643127, by rfl⟩ : syracuseStep 857503 = 1286255) B1286255
theorem B1284095 : Blo 854356 1284095 := bstep (se 1 (by rfl) ⟨963071, by rfl⟩ : syracuseStep 1284095 = 1926143) B1926143
theorem B858335 : Blo 854356 858335 := bstep (se 1 (by rfl) ⟨643751, by rfl⟩ : syracuseStep 858335 = 1287503) B1287503
theorem B1285787 : Blo 854356 1285787 := bstep (se 1 (by rfl) ⟨964340, by rfl⟩ : syracuseStep 1285787 = 1928681) B1928681
theorem B1285823 : Blo 854356 1285823 := bstep (se 1 (by rfl) ⟨964367, by rfl⟩ : syracuseStep 1285823 = 1928735) B1928735
theorem B4399895 : Blo 854356 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B12530213 : Blo 854356 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B8237609 : Blo 854356 8237609 := bstep (se 2 (by rfl) ⟨3089103, by rfl⟩ : syracuseStep 8237609 = 6178207) B6178207
theorem B46350551 : Blo 854356 46350551 := bstep (se 1 (by rfl) ⟨34762913, by rfl⟩ : syracuseStep 46350551 = 69525827) B69525827
theorem B3654683 : Blo 854356 3654683 := bstep (se 1 (by rfl) ⟨2741012, by rfl⟩ : syracuseStep 3654683 = 5482025) B5482025
theorem B5853991 : Blo 854356 5853991 := bstep (se 1 (by rfl) ⟨4390493, by rfl⟩ : syracuseStep 5853991 = 8780987) B8780987
theorem B7329527 : Blo 854356 7329527 := bstep (se 1 (by rfl) ⟨5497145, by rfl⟩ : syracuseStep 7329527 = 10994291) B10994291
theorem B31284899 : Blo 854356 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B19751687 : Blo 854356 19751687 := bstep (se 1 (by rfl) ⟨14813765, by rfl⟩ : syracuseStep 19751687 = 29627531) B29627531
theorem B30900367 : Blo 854356 30900367 := bstep (se 1 (by rfl) ⟨23175275, by rfl⟩ : syracuseStep 30900367 = 46350551) B46350551
theorem B855199 : Blo 854356 855199 := bstep (se 1 (by rfl) ⟨641399, by rfl⟩ : syracuseStep 855199 = 1282799) B1282799
theorem B4886351 : Blo 854356 4886351 := bstep (se 1 (by rfl) ⟨3664763, by rfl⟩ : syracuseStep 4886351 = 7329527) B7329527
theorem B856063 : Blo 854356 856063 := bstep (se 1 (by rfl) ⟨642047, by rfl⟩ : syracuseStep 856063 = 1284095) B1284095
theorem B857191 : Blo 854356 857191 := bstep (se 1 (by rfl) ⟨642893, by rfl⟩ : syracuseStep 857191 = 1285787) B1285787
theorem B857215 : Blo 854356 857215 := bstep (se 1 (by rfl) ⟨642911, by rfl⟩ : syracuseStep 857215 = 1285823) B1285823
theorem B7805321 : Blo 854356 7805321 := bstep (se 2 (by rfl) ⟨2926995, by rfl⟩ : syracuseStep 7805321 = 5853991) B5853991
theorem B2436455 : Blo 854356 2436455 := bstep (se 1 (by rfl) ⟨1827341, by rfl⟩ : syracuseStep 2436455 = 3654683) B3654683
theorem B18526319 : Blo 854356 18526319 := bstep (se 1 (by rfl) ⟨13894739, by rfl⟩ : syracuseStep 18526319 = 27789479) B27789479
theorem B20856599 : Blo 854356 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B2933263 : Blo 854356 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B5491739 : Blo 854356 5491739 := bstep (se 1 (by rfl) ⟨4118804, by rfl⟩ : syracuseStep 5491739 = 8237609) B8237609
theorem B13167791 : Blo 854356 13167791 := bstep (se 1 (by rfl) ⟨9875843, by rfl⟩ : syracuseStep 13167791 = 19751687) B19751687
theorem B8353475 : Blo 854356 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B13904399 : Blo 854356 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B41200489 : Blo 854356 41200489 := bstep (se 2 (by rfl) ⟨15450183, by rfl⟩ : syracuseStep 41200489 = 30900367) B30900367
theorem B3911017 : Blo 854356 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B3257567 : Blo 854356 3257567 := bstep (se 1 (by rfl) ⟨2443175, by rfl⟩ : syracuseStep 3257567 = 4886351) B4886351
theorem B1624303 : Blo 854356 1624303 := bstep (se 1 (by rfl) ⟨1218227, by rfl⟩ : syracuseStep 1624303 = 2436455) B2436455
theorem B3661159 : Blo 854356 3661159 := bstep (se 1 (by rfl) ⟨2745869, by rfl⟩ : syracuseStep 3661159 = 5491739) B5491739
theorem B5203547 : Blo 854356 5203547 := bstep (se 1 (by rfl) ⟨3902660, by rfl⟩ : syracuseStep 5203547 = 7805321) B7805321
theorem B8778527 : Blo 854356 8778527 := bstep (se 1 (by rfl) ⟨6583895, by rfl⟩ : syracuseStep 8778527 = 13167791) B13167791
theorem B12350879 : Blo 854356 12350879 := bstep (se 1 (by rfl) ⟨9263159, by rfl⟩ : syracuseStep 12350879 = 18526319) B18526319
theorem B5568983 : Blo 854356 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B2165737 : Blo 854356 2165737 := bstep (se 2 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 2165737 = 1624303) B1624303
theorem B5214689 : Blo 854356 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B2171711 : Blo 854356 2171711 := bstep (se 1 (by rfl) ⟨1628783, by rfl⟩ : syracuseStep 2171711 = 3257567) B3257567
theorem B8233919 : Blo 854356 8233919 := bstep (se 1 (by rfl) ⟨6175439, by rfl⟩ : syracuseStep 8233919 = 12350879) B12350879
theorem B3712655 : Blo 854356 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B54933985 : Blo 854356 54933985 := bstep (se 2 (by rfl) ⟨20600244, by rfl⟩ : syracuseStep 54933985 = 41200489) B41200489
theorem B37078397 : Blo 854356 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B5852351 : Blo 854356 5852351 := bstep (se 1 (by rfl) ⟨4389263, by rfl⟩ : syracuseStep 5852351 = 8778527) B8778527
theorem B3469031 : Blo 854356 3469031 := bstep (se 1 (by rfl) ⟨2601773, by rfl⟩ : syracuseStep 3469031 = 5203547) B5203547
theorem B4881545 : Blo 854356 4881545 := bstep (se 2 (by rfl) ⟨1830579, by rfl⟩ : syracuseStep 4881545 = 3661159) B3661159
theorem B3901567 : Blo 854356 3901567 := bstep (se 1 (by rfl) ⟨2926175, by rfl⟩ : syracuseStep 3901567 = 5852351) B5852351
theorem B3476459 : Blo 854356 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B2887649 : Blo 854356 2887649 := bstep (se 2 (by rfl) ⟨1082868, by rfl⟩ : syracuseStep 2887649 = 2165737) B2165737
theorem B9900413 : Blo 854356 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B1447807 : Blo 854356 1447807 := bstep (se 1 (by rfl) ⟨1085855, by rfl⟩ : syracuseStep 1447807 = 2171711) B2171711
theorem B73245313 : Blo 854356 73245313 := bstep (se 2 (by rfl) ⟨27466992, by rfl⟩ : syracuseStep 73245313 = 54933985) B54933985
theorem B3254363 : Blo 854356 3254363 := bstep (se 1 (by rfl) ⟨2440772, by rfl⟩ : syracuseStep 3254363 = 4881545) B4881545
theorem B24718931 : Blo 854356 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B5489279 : Blo 854356 5489279 := bstep (se 1 (by rfl) ⟨4116959, by rfl⟩ : syracuseStep 5489279 = 8233919) B8233919
theorem B2312687 : Blo 854356 2312687 := bstep (se 1 (by rfl) ⟨1734515, by rfl⟩ : syracuseStep 2312687 = 3469031) B3469031
theorem B1541791 : Blo 854356 1541791 := bstep (se 1 (by rfl) ⟨1156343, by rfl⟩ : syracuseStep 1541791 = 2312687) B2312687
theorem B2169575 : Blo 854356 2169575 := bstep (se 1 (by rfl) ⟨1627181, by rfl⟩ : syracuseStep 2169575 = 3254363) B3254363
theorem B97660417 : Blo 854356 97660417 := bstep (se 2 (by rfl) ⟨36622656, by rfl⟩ : syracuseStep 97660417 = 73245313) B73245313
theorem B6600275 : Blo 854356 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B3659519 : Blo 854356 3659519 := bstep (se 1 (by rfl) ⟨2744639, by rfl⟩ : syracuseStep 3659519 = 5489279) B5489279
theorem B1925099 : Blo 854356 1925099 := bstep (se 1 (by rfl) ⟨1443824, by rfl⟩ : syracuseStep 1925099 = 2887649) B2887649
theorem B5202089 : Blo 854356 5202089 := bstep (se 2 (by rfl) ⟨1950783, by rfl⟩ : syracuseStep 5202089 = 3901567) B3901567
theorem B16479287 : Blo 854356 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B1930409 : Blo 854356 1930409 := bstep (se 2 (by rfl) ⟨723903, by rfl⟩ : syracuseStep 1930409 = 1447807) B1447807
theorem B9270557 : Blo 854356 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B1446383 : Blo 854356 1446383 := bstep (se 1 (by rfl) ⟨1084787, by rfl⟩ : syracuseStep 1446383 = 2169575) B2169575
theorem B1283399 : Blo 854356 1283399 := bstep (se 1 (by rfl) ⟨962549, by rfl⟩ : syracuseStep 1283399 = 1925099) B1925099
theorem B10986191 : Blo 854356 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B1286939 : Blo 854356 1286939 := bstep (se 1 (by rfl) ⟨965204, by rfl⟩ : syracuseStep 1286939 = 1930409) B1930409
theorem B4400183 : Blo 854356 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B2439679 : Blo 854356 2439679 := bstep (se 1 (by rfl) ⟨1829759, by rfl⟩ : syracuseStep 2439679 = 3659519) B3659519
theorem B6180371 : Blo 854356 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B2055721 : Blo 854356 2055721 := bstep (se 2 (by rfl) ⟨770895, by rfl⟩ : syracuseStep 2055721 = 1541791) B1541791
theorem B130213889 : Blo 854356 130213889 := bstep (se 2 (by rfl) ⟨48830208, by rfl⟩ : syracuseStep 130213889 = 97660417) B97660417
theorem B3468059 : Blo 854356 3468059 := bstep (se 1 (by rfl) ⟨2601044, by rfl⟩ : syracuseStep 3468059 = 5202089) B5202089
theorem B855599 : Blo 854356 855599 := bstep (se 1 (by rfl) ⟨641699, by rfl⟩ : syracuseStep 855599 = 1283399) B1283399
theorem B857959 : Blo 854356 857959 := bstep (se 1 (by rfl) ⟨643469, by rfl⟩ : syracuseStep 857959 = 1286939) B1286939
theorem B86809259 : Blo 854356 86809259 := bstep (se 1 (by rfl) ⟨65106944, by rfl⟩ : syracuseStep 86809259 = 130213889) B130213889
theorem B3252905 : Blo 854356 3252905 := bstep (se 2 (by rfl) ⟨1219839, by rfl⟩ : syracuseStep 3252905 = 2439679) B2439679
theorem B964255 : Blo 854356 964255 := bstep (se 1 (by rfl) ⟨723191, by rfl⟩ : syracuseStep 964255 = 1446383) B1446383
theorem B7324127 : Blo 854356 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B2933455 : Blo 854356 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B2312039 : Blo 854356 2312039 := bstep (se 1 (by rfl) ⟨1734029, by rfl⟩ : syracuseStep 2312039 = 3468059) B3468059
theorem B2740961 : Blo 854356 2740961 := bstep (se 2 (by rfl) ⟨1027860, by rfl⟩ : syracuseStep 2740961 = 2055721) B2055721
theorem B4120247 : Blo 854356 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B4882751 : Blo 854356 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B1541359 : Blo 854356 1541359 := bstep (se 1 (by rfl) ⟨1156019, by rfl⟩ : syracuseStep 1541359 = 2312039) B2312039
theorem B57872839 : Blo 854356 57872839 := bstep (se 1 (by rfl) ⟨43404629, by rfl⟩ : syracuseStep 57872839 = 86809259) B86809259
theorem B2168603 : Blo 854356 2168603 := bstep (se 1 (by rfl) ⟨1626452, by rfl⟩ : syracuseStep 2168603 = 3252905) B3252905
theorem B1285673 : Blo 854356 1285673 := bstep (se 2 (by rfl) ⟨482127, by rfl⟩ : syracuseStep 1285673 = 964255) B964255
theorem B3911273 : Blo 854356 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B1827307 : Blo 854356 1827307 := bstep (se 1 (by rfl) ⟨1370480, by rfl⟩ : syracuseStep 1827307 = 2740961) B2740961
theorem B2746831 : Blo 854356 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B1445735 : Blo 854356 1445735 := bstep (se 1 (by rfl) ⟨1084301, by rfl⟩ : syracuseStep 1445735 = 2168603) B2168603
theorem B857115 : Blo 854356 857115 := bstep (se 1 (by rfl) ⟨642836, by rfl⟩ : syracuseStep 857115 = 1285673) B1285673
theorem B3255167 : Blo 854356 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B2436409 : Blo 854356 2436409 := bstep (se 2 (by rfl) ⟨913653, by rfl⟩ : syracuseStep 2436409 = 1827307) B1827307
theorem B2607515 : Blo 854356 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B2055145 : Blo 854356 2055145 := bstep (se 2 (by rfl) ⟨770679, by rfl⟩ : syracuseStep 2055145 = 1541359) B1541359
theorem B3662441 : Blo 854356 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B77163785 : Blo 854356 77163785 := bstep (se 2 (by rfl) ⟨28936419, by rfl⟩ : syracuseStep 77163785 = 57872839) B57872839
theorem B1738343 : Blo 854356 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B3248545 : Blo 854356 3248545 := bstep (se 2 (by rfl) ⟨1218204, by rfl⟩ : syracuseStep 3248545 = 2436409) B2436409
theorem B2170111 : Blo 854356 2170111 := bstep (se 1 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 2170111 = 3255167) B3255167
theorem B963823 : Blo 854356 963823 := bstep (se 1 (by rfl) ⟨722867, by rfl⟩ : syracuseStep 963823 = 1445735) B1445735
theorem B2441627 : Blo 854356 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B2740193 : Blo 854356 2740193 := bstep (se 2 (by rfl) ⟨1027572, by rfl⟩ : syracuseStep 2740193 = 2055145) B2055145
theorem B51442523 : Blo 854356 51442523 := bstep (se 1 (by rfl) ⟨38581892, by rfl⟩ : syracuseStep 51442523 = 77163785) B77163785
theorem B4331393 : Blo 854356 4331393 := bstep (se 2 (by rfl) ⟨1624272, by rfl⟩ : syracuseStep 4331393 = 3248545) B3248545
theorem B1285097 : Blo 854356 1285097 := bstep (se 2 (by rfl) ⟨481911, by rfl⟩ : syracuseStep 1285097 = 963823) B963823
theorem B2893481 : Blo 854356 2893481 := bstep (se 2 (by rfl) ⟨1085055, by rfl⟩ : syracuseStep 2893481 = 2170111) B2170111
theorem B1158895 : Blo 854356 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B34295015 : Blo 854356 34295015 := bstep (se 1 (by rfl) ⟨25721261, by rfl⟩ : syracuseStep 34295015 = 51442523) B51442523
theorem B1627751 : Blo 854356 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B1826795 : Blo 854356 1826795 := bstep (se 1 (by rfl) ⟨1370096, by rfl⟩ : syracuseStep 1826795 = 2740193) B2740193
theorem B1085167 : Blo 854356 1085167 := bstep (se 1 (by rfl) ⟨813875, by rfl⟩ : syracuseStep 1085167 = 1627751) B1627751
theorem B2887595 : Blo 854356 2887595 := bstep (se 1 (by rfl) ⟨2165696, by rfl⟩ : syracuseStep 2887595 = 4331393) B4331393
theorem B856731 : Blo 854356 856731 := bstep (se 1 (by rfl) ⟨642548, by rfl⟩ : syracuseStep 856731 = 1285097) B1285097
theorem B1545193 : Blo 854356 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B1217863 : Blo 854356 1217863 := bstep (se 1 (by rfl) ⟨913397, by rfl⟩ : syracuseStep 1217863 = 1826795) B1826795
theorem B22863343 : Blo 854356 22863343 := bstep (se 1 (by rfl) ⟨17147507, by rfl⟩ : syracuseStep 22863343 = 34295015) B34295015
theorem B1928987 : Blo 854356 1928987 := bstep (se 1 (by rfl) ⟨1446740, by rfl⟩ : syracuseStep 1928987 = 2893481) B2893481
theorem B1446889 : Blo 854356 1446889 := bstep (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) B1085167
theorem B1285991 : Blo 854356 1285991 := bstep (se 1 (by rfl) ⟨964493, by rfl⟩ : syracuseStep 1285991 = 1928987) B1928987
theorem B30484457 : Blo 854356 30484457 := bstep (se 2 (by rfl) ⟨11431671, by rfl⟩ : syracuseStep 30484457 = 22863343) B22863343
theorem B1623817 : Blo 854356 1623817 := bstep (se 2 (by rfl) ⟨608931, by rfl⟩ : syracuseStep 1623817 = 1217863) B1217863
theorem B1925063 : Blo 854356 1925063 := bstep (se 1 (by rfl) ⟨1443797, by rfl⟩ : syracuseStep 1925063 = 2887595) B2887595
theorem B2060257 : Blo 854356 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B2165089 : Blo 854356 2165089 := bstep (se 2 (by rfl) ⟨811908, by rfl⟩ : syracuseStep 2165089 = 1623817) B1623817
theorem B857327 : Blo 854356 857327 := bstep (se 1 (by rfl) ⟨642995, by rfl⟩ : syracuseStep 857327 = 1285991) B1285991
theorem B1283375 : Blo 854356 1283375 := bstep (se 1 (by rfl) ⟨962531, by rfl⟩ : syracuseStep 1283375 = 1925063) B1925063
theorem B20322971 : Blo 854356 20322971 := bstep (se 1 (by rfl) ⟨15242228, by rfl⟩ : syracuseStep 20322971 = 30484457) B30484457
theorem B2747009 : Blo 854356 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B1929185 : Blo 854356 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B2886785 : Blo 854356 2886785 := bstep (se 2 (by rfl) ⟨1082544, by rfl⟩ : syracuseStep 2886785 = 2165089) B2165089
theorem B855583 : Blo 854356 855583 := bstep (se 1 (by rfl) ⟨641687, by rfl⟩ : syracuseStep 855583 = 1283375) B1283375
theorem B1286123 : Blo 854356 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B13548647 : Blo 854356 13548647 := bstep (se 1 (by rfl) ⟨10161485, by rfl⟩ : syracuseStep 13548647 = 20322971) B20322971
theorem B1831339 : Blo 854356 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B9767141 : Blo 854356 9767141 := bstep (se 4 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 9767141 = 1831339) B1831339
theorem B857415 : Blo 854356 857415 := bstep (se 1 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 857415 = 1286123) B1286123
theorem B36129725 : Blo 854356 36129725 := bstep (se 3 (by rfl) ⟨6774323, by rfl⟩ : syracuseStep 36129725 = 13548647) B13548647
theorem B1924523 : Blo 854356 1924523 := bstep (se 1 (by rfl) ⟨1443392, by rfl⟩ : syracuseStep 1924523 = 2886785) B2886785
theorem B24086483 : Blo 854356 24086483 := bstep (se 1 (by rfl) ⟨18064862, by rfl⟩ : syracuseStep 24086483 = 36129725) B36129725
theorem B1283015 : Blo 854356 1283015 := bstep (se 1 (by rfl) ⟨962261, by rfl⟩ : syracuseStep 1283015 = 1924523) B1924523
theorem B6511427 : Blo 854356 6511427 := bstep (se 1 (by rfl) ⟨4883570, by rfl⟩ : syracuseStep 6511427 = 9767141) B9767141
theorem B16057655 : Blo 854356 16057655 := bstep (se 1 (by rfl) ⟨12043241, by rfl⟩ : syracuseStep 16057655 = 24086483) B24086483
theorem B855343 : Blo 854356 855343 := bstep (se 1 (by rfl) ⟨641507, by rfl⟩ : syracuseStep 855343 = 1283015) B1283015
theorem B4340951 : Blo 854356 4340951 := bstep (se 1 (by rfl) ⟨3255713, by rfl⟩ : syracuseStep 4340951 = 6511427) B6511427
theorem B2893967 : Blo 854356 2893967 := bstep (se 1 (by rfl) ⟨2170475, by rfl⟩ : syracuseStep 2893967 = 4340951) B4340951
theorem B10705103 : Blo 854356 10705103 := bstep (se 1 (by rfl) ⟨8028827, by rfl⟩ : syracuseStep 10705103 = 16057655) B16057655
theorem B114187765 : Blo 854356 114187765 := bstep (se 5 (by rfl) ⟨5352551, by rfl⟩ : syracuseStep 114187765 = 10705103) B10705103
theorem B1929311 : Blo 854356 1929311 := bstep (se 1 (by rfl) ⟨1446983, by rfl⟩ : syracuseStep 1929311 = 2893967) B2893967
theorem B1286207 : Blo 854356 1286207 := bstep (se 1 (by rfl) ⟨964655, by rfl⟩ : syracuseStep 1286207 = 1929311) B1929311
theorem B152250353 : Blo 854356 152250353 := bstep (se 2 (by rfl) ⟨57093882, by rfl⟩ : syracuseStep 152250353 = 114187765) B114187765
theorem B857471 : Blo 854356 857471 := bstep (se 1 (by rfl) ⟨643103, by rfl⟩ : syracuseStep 857471 = 1286207) B1286207
theorem B101500235 : Blo 854356 101500235 := bstep (se 1 (by rfl) ⟨76125176, by rfl⟩ : syracuseStep 101500235 = 152250353) B152250353
theorem B67666823 : Blo 854356 67666823 := bstep (se 1 (by rfl) ⟨50750117, by rfl⟩ : syracuseStep 67666823 = 101500235) B101500235
theorem B45111215 : Blo 854356 45111215 := bstep (se 1 (by rfl) ⟨33833411, by rfl⟩ : syracuseStep 45111215 = 67666823) B67666823
theorem B120296573 : Blo 854356 120296573 := bstep (se 3 (by rfl) ⟨22555607, by rfl⟩ : syracuseStep 120296573 = 45111215) B45111215
theorem B80197715 : Blo 854356 80197715 := bstep (se 1 (by rfl) ⟨60148286, by rfl⟩ : syracuseStep 80197715 = 120296573) B120296573
theorem B53465143 : Blo 854356 53465143 := bstep (se 1 (by rfl) ⟨40098857, by rfl⟩ : syracuseStep 53465143 = 80197715) B80197715
theorem B71286857 : Blo 854356 71286857 := bstep (se 2 (by rfl) ⟨26732571, by rfl⟩ : syracuseStep 71286857 = 53465143) B53465143
theorem B47524571 : Blo 854356 47524571 := bstep (se 1 (by rfl) ⟨35643428, by rfl⟩ : syracuseStep 47524571 = 71286857) B71286857
theorem B31683047 : Blo 854356 31683047 := bstep (se 1 (by rfl) ⟨23762285, by rfl⟩ : syracuseStep 31683047 = 47524571) B47524571
theorem B84488125 : Blo 854356 84488125 := bstep (se 3 (by rfl) ⟨15841523, by rfl⟩ : syracuseStep 84488125 = 31683047) B31683047
theorem B112650833 : Blo 854356 112650833 := bstep (se 2 (by rfl) ⟨42244062, by rfl⟩ : syracuseStep 112650833 = 84488125) B84488125
theorem B75100555 : Blo 854356 75100555 := bstep (se 1 (by rfl) ⟨56325416, by rfl⟩ : syracuseStep 75100555 = 112650833) B112650833
theorem B100134073 : Blo 854356 100134073 := bstep (se 2 (by rfl) ⟨37550277, by rfl⟩ : syracuseStep 100134073 = 75100555) B75100555
theorem B133512097 : Blo 854356 133512097 := bstep (se 2 (by rfl) ⟨50067036, by rfl⟩ : syracuseStep 133512097 = 100134073) B100134073
theorem B178016129 : Blo 854356 178016129 := bstep (se 2 (by rfl) ⟨66756048, by rfl⟩ : syracuseStep 178016129 = 133512097) B133512097
theorem B118677419 : Blo 854356 118677419 := bstep (se 1 (by rfl) ⟨89008064, by rfl⟩ : syracuseStep 118677419 = 178016129) B178016129
theorem B79118279 : Blo 854356 79118279 := bstep (se 1 (by rfl) ⟨59338709, by rfl⟩ : syracuseStep 79118279 = 118677419) B118677419
theorem B52745519 : Blo 854356 52745519 := bstep (se 1 (by rfl) ⟨39559139, by rfl⟩ : syracuseStep 52745519 = 79118279) B79118279
theorem B35163679 : Blo 854356 35163679 := bstep (se 1 (by rfl) ⟨26372759, by rfl⟩ : syracuseStep 35163679 = 52745519) B52745519
theorem B46884905 : Blo 854356 46884905 := bstep (se 2 (by rfl) ⟨17581839, by rfl⟩ : syracuseStep 46884905 = 35163679) B35163679
theorem B31256603 : Blo 854356 31256603 := bstep (se 1 (by rfl) ⟨23442452, by rfl⟩ : syracuseStep 31256603 = 46884905) B46884905
theorem B20837735 : Blo 854356 20837735 := bstep (se 1 (by rfl) ⟨15628301, by rfl⟩ : syracuseStep 20837735 = 31256603) B31256603
theorem B13891823 : Blo 854356 13891823 := bstep (se 1 (by rfl) ⟨10418867, by rfl⟩ : syracuseStep 13891823 = 20837735) B20837735
theorem B9261215 : Blo 854356 9261215 := bstep (se 1 (by rfl) ⟨6945911, by rfl⟩ : syracuseStep 9261215 = 13891823) B13891823
theorem B6174143 : Blo 854356 6174143 := bstep (se 1 (by rfl) ⟨4630607, by rfl⟩ : syracuseStep 6174143 = 9261215) B9261215
theorem B4116095 : Blo 854356 4116095 := bstep (se 1 (by rfl) ⟨3087071, by rfl⟩ : syracuseStep 4116095 = 6174143) B6174143
theorem B2744063 : Blo 854356 2744063 := bstep (se 1 (by rfl) ⟨2058047, by rfl⟩ : syracuseStep 2744063 = 4116095) B4116095
theorem B1829375 : Blo 854356 1829375 := bstep (se 1 (by rfl) ⟨1372031, by rfl⟩ : syracuseStep 1829375 = 2744063) B2744063
theorem B1219583 : Blo 854356 1219583 := bstep (se 1 (by rfl) ⟨914687, by rfl⟩ : syracuseStep 1219583 = 1829375) B1829375
theorem B3252221 : Blo 854356 3252221 := bstep (se 3 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 3252221 = 1219583) B1219583
theorem B2168147 : Blo 854356 2168147 := bstep (se 1 (by rfl) ⟨1626110, by rfl⟩ : syracuseStep 2168147 = 3252221) B3252221
theorem B1445431 : Blo 854356 1445431 := bstep (se 1 (by rfl) ⟨1084073, by rfl⟩ : syracuseStep 1445431 = 2168147) B2168147
theorem B1927241 : Blo 854356 1927241 := bstep (se 2 (by rfl) ⟨722715, by rfl⟩ : syracuseStep 1927241 = 1445431) B1445431
theorem B1284827 : Blo 854356 1284827 := bstep (se 1 (by rfl) ⟨963620, by rfl⟩ : syracuseStep 1284827 = 1927241) B1927241
theorem B856551 : Blo 854356 856551 := bstep (se 1 (by rfl) ⟨642413, by rfl⟩ : syracuseStep 856551 = 1284827) B1284827

theorem C0 (j : ℕ) (h1 : 213589 ≤ j) (h2 : j ≤ 214288) : Blo 854356 (4 * j + 3) := by
  interval_cases j
  · exact B854359
  · exact B854363
  · exact B854367
  · exact B854371
  · exact B854375
  · exact B854379
  · exact B854383
  · exact B854387
  · exact B854391
  · exact B854395
  · exact B854399
  · exact B854403
  · exact B854407
  · exact B854411
  · exact B854415
  · exact B854419
  · exact B854423
  · exact B854427
  · exact B854431
  · exact B854435
  · exact B854439
  · exact B854443
  · exact B854447
  · exact B854451
  · exact B854455
  · exact B854459
  · exact B854463
  · exact B854467
  · exact B854471
  · exact B854475
  · exact B854479
  · exact B854483
  · exact B854487
  · exact B854491
  · exact B854495
  · exact B854499
  · exact B854503
  · exact B854507
  · exact B854511
  · exact B854515
  · exact B854519
  · exact B854523
  · exact B854527
  · exact B854531
  · exact B854535
  · exact B854539
  · exact B854543
  · exact B854547
  · exact B854551
  · exact B854555
  · exact B854559
  · exact B854563
  · exact B854567
  · exact B854571
  · exact B854575
  · exact B854579
  · exact B854583
  · exact B854587
  · exact B854591
  · exact B854595
  · exact B854599
  · exact B854603
  · exact B854607
  · exact B854611
  · exact B854615
  · exact B854619
  · exact B854623
  · exact B854627
  · exact B854631
  · exact B854635
  · exact B854639
  · exact B854643
  · exact B854647
  · exact B854651
  · exact B854655
  · exact B854659
  · exact B854663
  · exact B854667
  · exact B854671
  · exact B854675
  · exact B854679
  · exact B854683
  · exact B854687
  · exact B854691
  · exact B854695
  · exact B854699
  · exact B854703
  · exact B854707
  · exact B854711
  · exact B854715
  · exact B854719
  · exact B854723
  · exact B854727
  · exact B854731
  · exact B854735
  · exact B854739
  · exact B854743
  · exact B854747
  · exact B854751
  · exact B854755
  · exact B854759
  · exact B854763
  · exact B854767
  · exact B854771
  · exact B854775
  · exact B854779
  · exact B854783
  · exact B854787
  · exact B854791
  · exact B854795
  · exact B854799
  · exact B854803
  · exact B854807
  · exact B854811
  · exact B854815
  · exact B854819
  · exact B854823
  · exact B854827
  · exact B854831
  · exact B854835
  · exact B854839
  · exact B854843
  · exact B854847
  · exact B854851
  · exact B854855
  · exact B854859
  · exact B854863
  · exact B854867
  · exact B854871
  · exact B854875
  · exact B854879
  · exact B854883
  · exact B854887
  · exact B854891
  · exact B854895
  · exact B854899
  · exact B854903
  · exact B854907
  · exact B854911
  · exact B854915
  · exact B854919
  · exact B854923
  · exact B854927
  · exact B854931
  · exact B854935
  · exact B854939
  · exact B854943
  · exact B854947
  · exact B854951
  · exact B854955
  · exact B854959
  · exact B854963
  · exact B854967
  · exact B854971
  · exact B854975
  · exact B854979
  · exact B854983
  · exact B854987
  · exact B854991
  · exact B854995
  · exact B854999
  · exact B855003
  · exact B855007
  · exact B855011
  · exact B855015
  · exact B855019
  · exact B855023
  · exact B855027
  · exact B855031
  · exact B855035
  · exact B855039
  · exact B855043
  · exact B855047
  · exact B855051
  · exact B855055
  · exact B855059
  · exact B855063
  · exact B855067
  · exact B855071
  · exact B855075
  · exact B855079
  · exact B855083
  · exact B855087
  · exact B855091
  · exact B855095
  · exact B855099
  · exact B855103
  · exact B855107
  · exact B855111
  · exact B855115
  · exact B855119
  · exact B855123
  · exact B855127
  · exact B855131
  · exact B855135
  · exact B855139
  · exact B855143
  · exact B855147
  · exact B855151
  · exact B855155
  · exact B855159
  · exact B855163
  · exact B855167
  · exact B855171
  · exact B855175
  · exact B855179
  · exact B855183
  · exact B855187
  · exact B855191
  · exact B855195
  · exact B855199
  · exact B855203
  · exact B855207
  · exact B855211
  · exact B855215
  · exact B855219
  · exact B855223
  · exact B855227
  · exact B855231
  · exact B855235
  · exact B855239
  · exact B855243
  · exact B855247
  · exact B855251
  · exact B855255
  · exact B855259
  · exact B855263
  · exact B855267
  · exact B855271
  · exact B855275
  · exact B855279
  · exact B855283
  · exact B855287
  · exact B855291
  · exact B855295
  · exact B855299
  · exact B855303
  · exact B855307
  · exact B855311
  · exact B855315
  · exact B855319
  · exact B855323
  · exact B855327
  · exact B855331
  · exact B855335
  · exact B855339
  · exact B855343
  · exact B855347
  · exact B855351
  · exact B855355
  · exact B855359
  · exact B855363
  · exact B855367
  · exact B855371
  · exact B855375
  · exact B855379
  · exact B855383
  · exact B855387
  · exact B855391
  · exact B855395
  · exact B855399
  · exact B855403
  · exact B855407
  · exact B855411
  · exact B855415
  · exact B855419
  · exact B855423
  · exact B855427
  · exact B855431
  · exact B855435
  · exact B855439
  · exact B855443
  · exact B855447
  · exact B855451
  · exact B855455
  · exact B855459
  · exact B855463
  · exact B855467
  · exact B855471
  · exact B855475
  · exact B855479
  · exact B855483
  · exact B855487
  · exact B855491
  · exact B855495
  · exact B855499
  · exact B855503
  · exact B855507
  · exact B855511
  · exact B855515
  · exact B855519
  · exact B855523
  · exact B855527
  · exact B855531
  · exact B855535
  · exact B855539
  · exact B855543
  · exact B855547
  · exact B855551
  · exact B855555
  · exact B855559
  · exact B855563
  · exact B855567
  · exact B855571
  · exact B855575
  · exact B855579
  · exact B855583
  · exact B855587
  · exact B855591
  · exact B855595
  · exact B855599
  · exact B855603
  · exact B855607
  · exact B855611
  · exact B855615
  · exact B855619
  · exact B855623
  · exact B855627
  · exact B855631
  · exact B855635
  · exact B855639
  · exact B855643
  · exact B855647
  · exact B855651
  · exact B855655
  · exact B855659
  · exact B855663
  · exact B855667
  · exact B855671
  · exact B855675
  · exact B855679
  · exact B855683
  · exact B855687
  · exact B855691
  · exact B855695
  · exact B855699
  · exact B855703
  · exact B855707
  · exact B855711
  · exact B855715
  · exact B855719
  · exact B855723
  · exact B855727
  · exact B855731
  · exact B855735
  · exact B855739
  · exact B855743
  · exact B855747
  · exact B855751
  · exact B855755
  · exact B855759
  · exact B855763
  · exact B855767
  · exact B855771
  · exact B855775
  · exact B855779
  · exact B855783
  · exact B855787
  · exact B855791
  · exact B855795
  · exact B855799
  · exact B855803
  · exact B855807
  · exact B855811
  · exact B855815
  · exact B855819
  · exact B855823
  · exact B855827
  · exact B855831
  · exact B855835
  · exact B855839
  · exact B855843
  · exact B855847
  · exact B855851
  · exact B855855
  · exact B855859
  · exact B855863
  · exact B855867
  · exact B855871
  · exact B855875
  · exact B855879
  · exact B855883
  · exact B855887
  · exact B855891
  · exact B855895
  · exact B855899
  · exact B855903
  · exact B855907
  · exact B855911
  · exact B855915
  · exact B855919
  · exact B855923
  · exact B855927
  · exact B855931
  · exact B855935
  · exact B855939
  · exact B855943
  · exact B855947
  · exact B855951
  · exact B855955
  · exact B855959
  · exact B855963
  · exact B855967
  · exact B855971
  · exact B855975
  · exact B855979
  · exact B855983
  · exact B855987
  · exact B855991
  · exact B855995
  · exact B855999
  · exact B856003
  · exact B856007
  · exact B856011
  · exact B856015
  · exact B856019
  · exact B856023
  · exact B856027
  · exact B856031
  · exact B856035
  · exact B856039
  · exact B856043
  · exact B856047
  · exact B856051
  · exact B856055
  · exact B856059
  · exact B856063
  · exact B856067
  · exact B856071
  · exact B856075
  · exact B856079
  · exact B856083
  · exact B856087
  · exact B856091
  · exact B856095
  · exact B856099
  · exact B856103
  · exact B856107
  · exact B856111
  · exact B856115
  · exact B856119
  · exact B856123
  · exact B856127
  · exact B856131
  · exact B856135
  · exact B856139
  · exact B856143
  · exact B856147
  · exact B856151
  · exact B856155
  · exact B856159
  · exact B856163
  · exact B856167
  · exact B856171
  · exact B856175
  · exact B856179
  · exact B856183
  · exact B856187
  · exact B856191
  · exact B856195
  · exact B856199
  · exact B856203
  · exact B856207
  · exact B856211
  · exact B856215
  · exact B856219
  · exact B856223
  · exact B856227
  · exact B856231
  · exact B856235
  · exact B856239
  · exact B856243
  · exact B856247
  · exact B856251
  · exact B856255
  · exact B856259
  · exact B856263
  · exact B856267
  · exact B856271
  · exact B856275
  · exact B856279
  · exact B856283
  · exact B856287
  · exact B856291
  · exact B856295
  · exact B856299
  · exact B856303
  · exact B856307
  · exact B856311
  · exact B856315
  · exact B856319
  · exact B856323
  · exact B856327
  · exact B856331
  · exact B856335
  · exact B856339
  · exact B856343
  · exact B856347
  · exact B856351
  · exact B856355
  · exact B856359
  · exact B856363
  · exact B856367
  · exact B856371
  · exact B856375
  · exact B856379
  · exact B856383
  · exact B856387
  · exact B856391
  · exact B856395
  · exact B856399
  · exact B856403
  · exact B856407
  · exact B856411
  · exact B856415
  · exact B856419
  · exact B856423
  · exact B856427
  · exact B856431
  · exact B856435
  · exact B856439
  · exact B856443
  · exact B856447
  · exact B856451
  · exact B856455
  · exact B856459
  · exact B856463
  · exact B856467
  · exact B856471
  · exact B856475
  · exact B856479
  · exact B856483
  · exact B856487
  · exact B856491
  · exact B856495
  · exact B856499
  · exact B856503
  · exact B856507
  · exact B856511
  · exact B856515
  · exact B856519
  · exact B856523
  · exact B856527
  · exact B856531
  · exact B856535
  · exact B856539
  · exact B856543
  · exact B856547
  · exact B856551
  · exact B856555
  · exact B856559
  · exact B856563
  · exact B856567
  · exact B856571
  · exact B856575
  · exact B856579
  · exact B856583
  · exact B856587
  · exact B856591
  · exact B856595
  · exact B856599
  · exact B856603
  · exact B856607
  · exact B856611
  · exact B856615
  · exact B856619
  · exact B856623
  · exact B856627
  · exact B856631
  · exact B856635
  · exact B856639
  · exact B856643
  · exact B856647
  · exact B856651
  · exact B856655
  · exact B856659
  · exact B856663
  · exact B856667
  · exact B856671
  · exact B856675
  · exact B856679
  · exact B856683
  · exact B856687
  · exact B856691
  · exact B856695
  · exact B856699
  · exact B856703
  · exact B856707
  · exact B856711
  · exact B856715
  · exact B856719
  · exact B856723
  · exact B856727
  · exact B856731
  · exact B856735
  · exact B856739
  · exact B856743
  · exact B856747
  · exact B856751
  · exact B856755
  · exact B856759
  · exact B856763
  · exact B856767
  · exact B856771
  · exact B856775
  · exact B856779
  · exact B856783
  · exact B856787
  · exact B856791
  · exact B856795
  · exact B856799
  · exact B856803
  · exact B856807
  · exact B856811
  · exact B856815
  · exact B856819
  · exact B856823
  · exact B856827
  · exact B856831
  · exact B856835
  · exact B856839
  · exact B856843
  · exact B856847
  · exact B856851
  · exact B856855
  · exact B856859
  · exact B856863
  · exact B856867
  · exact B856871
  · exact B856875
  · exact B856879
  · exact B856883
  · exact B856887
  · exact B856891
  · exact B856895
  · exact B856899
  · exact B856903
  · exact B856907
  · exact B856911
  · exact B856915
  · exact B856919
  · exact B856923
  · exact B856927
  · exact B856931
  · exact B856935
  · exact B856939
  · exact B856943
  · exact B856947
  · exact B856951
  · exact B856955
  · exact B856959
  · exact B856963
  · exact B856967
  · exact B856971
  · exact B856975
  · exact B856979
  · exact B856983
  · exact B856987
  · exact B856991
  · exact B856995
  · exact B856999
  · exact B857003
  · exact B857007
  · exact B857011
  · exact B857015
  · exact B857019
  · exact B857023
  · exact B857027
  · exact B857031
  · exact B857035
  · exact B857039
  · exact B857043
  · exact B857047
  · exact B857051
  · exact B857055
  · exact B857059
  · exact B857063
  · exact B857067
  · exact B857071
  · exact B857075
  · exact B857079
  · exact B857083
  · exact B857087
  · exact B857091
  · exact B857095
  · exact B857099
  · exact B857103
  · exact B857107
  · exact B857111
  · exact B857115
  · exact B857119
  · exact B857123
  · exact B857127
  · exact B857131
  · exact B857135
  · exact B857139
  · exact B857143
  · exact B857147
  · exact B857151
  · exact B857155

theorem C1 (j : ℕ) (h1 : 214289 ≤ j) (h2 : j ≤ 214588) : Blo 854356 (4 * j + 3) := by
  interval_cases j
  · exact B857159
  · exact B857163
  · exact B857167
  · exact B857171
  · exact B857175
  · exact B857179
  · exact B857183
  · exact B857187
  · exact B857191
  · exact B857195
  · exact B857199
  · exact B857203
  · exact B857207
  · exact B857211
  · exact B857215
  · exact B857219
  · exact B857223
  · exact B857227
  · exact B857231
  · exact B857235
  · exact B857239
  · exact B857243
  · exact B857247
  · exact B857251
  · exact B857255
  · exact B857259
  · exact B857263
  · exact B857267
  · exact B857271
  · exact B857275
  · exact B857279
  · exact B857283
  · exact B857287
  · exact B857291
  · exact B857295
  · exact B857299
  · exact B857303
  · exact B857307
  · exact B857311
  · exact B857315
  · exact B857319
  · exact B857323
  · exact B857327
  · exact B857331
  · exact B857335
  · exact B857339
  · exact B857343
  · exact B857347
  · exact B857351
  · exact B857355
  · exact B857359
  · exact B857363
  · exact B857367
  · exact B857371
  · exact B857375
  · exact B857379
  · exact B857383
  · exact B857387
  · exact B857391
  · exact B857395
  · exact B857399
  · exact B857403
  · exact B857407
  · exact B857411
  · exact B857415
  · exact B857419
  · exact B857423
  · exact B857427
  · exact B857431
  · exact B857435
  · exact B857439
  · exact B857443
  · exact B857447
  · exact B857451
  · exact B857455
  · exact B857459
  · exact B857463
  · exact B857467
  · exact B857471
  · exact B857475
  · exact B857479
  · exact B857483
  · exact B857487
  · exact B857491
  · exact B857495
  · exact B857499
  · exact B857503
  · exact B857507
  · exact B857511
  · exact B857515
  · exact B857519
  · exact B857523
  · exact B857527
  · exact B857531
  · exact B857535
  · exact B857539
  · exact B857543
  · exact B857547
  · exact B857551
  · exact B857555
  · exact B857559
  · exact B857563
  · exact B857567
  · exact B857571
  · exact B857575
  · exact B857579
  · exact B857583
  · exact B857587
  · exact B857591
  · exact B857595
  · exact B857599
  · exact B857603
  · exact B857607
  · exact B857611
  · exact B857615
  · exact B857619
  · exact B857623
  · exact B857627
  · exact B857631
  · exact B857635
  · exact B857639
  · exact B857643
  · exact B857647
  · exact B857651
  · exact B857655
  · exact B857659
  · exact B857663
  · exact B857667
  · exact B857671
  · exact B857675
  · exact B857679
  · exact B857683
  · exact B857687
  · exact B857691
  · exact B857695
  · exact B857699
  · exact B857703
  · exact B857707
  · exact B857711
  · exact B857715
  · exact B857719
  · exact B857723
  · exact B857727
  · exact B857731
  · exact B857735
  · exact B857739
  · exact B857743
  · exact B857747
  · exact B857751
  · exact B857755
  · exact B857759
  · exact B857763
  · exact B857767
  · exact B857771
  · exact B857775
  · exact B857779
  · exact B857783
  · exact B857787
  · exact B857791
  · exact B857795
  · exact B857799
  · exact B857803
  · exact B857807
  · exact B857811
  · exact B857815
  · exact B857819
  · exact B857823
  · exact B857827
  · exact B857831
  · exact B857835
  · exact B857839
  · exact B857843
  · exact B857847
  · exact B857851
  · exact B857855
  · exact B857859
  · exact B857863
  · exact B857867
  · exact B857871
  · exact B857875
  · exact B857879
  · exact B857883
  · exact B857887
  · exact B857891
  · exact B857895
  · exact B857899
  · exact B857903
  · exact B857907
  · exact B857911
  · exact B857915
  · exact B857919
  · exact B857923
  · exact B857927
  · exact B857931
  · exact B857935
  · exact B857939
  · exact B857943
  · exact B857947
  · exact B857951
  · exact B857955
  · exact B857959
  · exact B857963
  · exact B857967
  · exact B857971
  · exact B857975
  · exact B857979
  · exact B857983
  · exact B857987
  · exact B857991
  · exact B857995
  · exact B857999
  · exact B858003
  · exact B858007
  · exact B858011
  · exact B858015
  · exact B858019
  · exact B858023
  · exact B858027
  · exact B858031
  · exact B858035
  · exact B858039
  · exact B858043
  · exact B858047
  · exact B858051
  · exact B858055
  · exact B858059
  · exact B858063
  · exact B858067
  · exact B858071
  · exact B858075
  · exact B858079
  · exact B858083
  · exact B858087
  · exact B858091
  · exact B858095
  · exact B858099
  · exact B858103
  · exact B858107
  · exact B858111
  · exact B858115
  · exact B858119
  · exact B858123
  · exact B858127
  · exact B858131
  · exact B858135
  · exact B858139
  · exact B858143
  · exact B858147
  · exact B858151
  · exact B858155
  · exact B858159
  · exact B858163
  · exact B858167
  · exact B858171
  · exact B858175
  · exact B858179
  · exact B858183
  · exact B858187
  · exact B858191
  · exact B858195
  · exact B858199
  · exact B858203
  · exact B858207
  · exact B858211
  · exact B858215
  · exact B858219
  · exact B858223
  · exact B858227
  · exact B858231
  · exact B858235
  · exact B858239
  · exact B858243
  · exact B858247
  · exact B858251
  · exact B858255
  · exact B858259
  · exact B858263
  · exact B858267
  · exact B858271
  · exact B858275
  · exact B858279
  · exact B858283
  · exact B858287
  · exact B858291
  · exact B858295
  · exact B858299
  · exact B858303
  · exact B858307
  · exact B858311
  · exact B858315
  · exact B858319
  · exact B858323
  · exact B858327
  · exact B858331
  · exact B858335
  · exact B858339
  · exact B858343
  · exact B858347
  · exact B858351
  · exact B858355

theorem solution (m : ℕ) (hlo : 854356 ≤ m) (hhi : m ≤ 858356) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 213589 ≤ j := by omega
    have hj2 : j ≤ 214588 := by omega
    have hb : Blo 854356 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 214289 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
