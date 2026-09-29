-- Prove2me | solution 1 for syracuse_descends_range_1506950_1508950
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:05.958853+00:00
-- url     : https://prove2.me/submissions/70c9aa5a-ee61-47b9-af26-27746ddaf190

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


theorem B2260997 : Blo 1506950 2260997 := bbase (se 4 (by rfl) ⟨211968, by rfl⟩ : syracuseStep 2260997 = 423937) (by norm_num)
theorem B6881285 : Blo 1506950 6881285 := bbase (se 4 (by rfl) ⟨645120, by rfl⟩ : syracuseStep 6881285 = 1290241) (by norm_num)
theorem B1695757 : Blo 1506950 1695757 := bbase (se 3 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 1695757 = 635909) (by norm_num)
theorem B2261021 : Blo 1506950 2261021 := bbase (se 3 (by rfl) ⟨423941, by rfl⟩ : syracuseStep 2261021 = 847883) (by norm_num)
theorem B1695793 : Blo 1506950 1695793 := bbase (se 2 (by rfl) ⟨635922, by rfl⟩ : syracuseStep 1695793 = 1271845) (by norm_num)
theorem B1908785 : Blo 1506950 1908785 := bbase (se 2 (by rfl) ⟨715794, by rfl⟩ : syracuseStep 1908785 = 1431589) (by norm_num)
theorem B5087285 : Blo 1506950 5087285 := bbase (se 5 (by rfl) ⟨238466, by rfl⟩ : syracuseStep 5087285 = 476933) (by norm_num)
theorem B3391541 : Blo 1506950 3391541 := bbase (se 5 (by rfl) ⟨158978, by rfl⟩ : syracuseStep 3391541 = 317957) (by norm_num)
theorem B2261045 : Blo 1506950 2261045 := bbase (se 5 (by rfl) ⟨105986, by rfl⟩ : syracuseStep 2261045 = 211973) (by norm_num)
theorem B2261069 : Blo 1506950 2261069 := bbase (se 3 (by rfl) ⟨423950, by rfl⟩ : syracuseStep 2261069 = 847901) (by norm_num)
theorem B1695829 : Blo 1506950 1695829 := bbase (se 8 (by rfl) ⟨9936, by rfl⟩ : syracuseStep 1695829 = 19873) (by norm_num)
theorem B1810525 : Blo 1506950 1810525 := bbase (se 3 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 1810525 = 678947) (by norm_num)
theorem B2261093 : Blo 1506950 2261093 := bbase (se 4 (by rfl) ⟨211977, by rfl⟩ : syracuseStep 2261093 = 423955) (by norm_num)
theorem B1908841 : Blo 1506950 1908841 := bbase (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) (by norm_num)
theorem B1695865 : Blo 1506950 1695865 := bbase (se 2 (by rfl) ⟨635949, by rfl⟩ : syracuseStep 1695865 = 1271899) (by norm_num)
theorem B3391613 : Blo 1506950 3391613 := bbase (se 3 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 3391613 = 1271855) (by norm_num)
theorem B2261117 : Blo 1506950 2261117 := bbase (se 3 (by rfl) ⟨423959, by rfl⟩ : syracuseStep 2261117 = 847919) (by norm_num)
theorem B2900117 : Blo 1506950 2900117 := bbase (se 6 (by rfl) ⟨67971, by rfl⟩ : syracuseStep 2900117 = 135943) (by norm_num)
theorem B2261141 : Blo 1506950 2261141 := bbase (se 6 (by rfl) ⟨52995, by rfl⟩ : syracuseStep 2261141 = 105991) (by norm_num)
theorem B1695901 : Blo 1506950 1695901 := bbase (se 3 (by rfl) ⟨317981, by rfl⟩ : syracuseStep 1695901 = 635963) (by norm_num)
theorem B3055781 : Blo 1506950 3055781 := bbase (se 4 (by rfl) ⟨286479, by rfl⟩ : syracuseStep 3055781 = 572959) (by norm_num)
theorem B2261165 : Blo 1506950 2261165 := bbase (se 3 (by rfl) ⟨423968, by rfl⟩ : syracuseStep 2261165 = 847937) (by norm_num)
theorem B1695937 : Blo 1506950 1695937 := bbase (se 2 (by rfl) ⟨635976, by rfl⟩ : syracuseStep 1695937 = 1271953) (by norm_num)
theorem B3391685 : Blo 1506950 3391685 := bbase (se 4 (by rfl) ⟨317970, by rfl⟩ : syracuseStep 3391685 = 635941) (by norm_num)
theorem B2261189 : Blo 1506950 2261189 := bbase (se 4 (by rfl) ⟨211986, by rfl⟩ : syracuseStep 2261189 = 423973) (by norm_num)
theorem B1908937 : Blo 1506950 1908937 := bbase (se 2 (by rfl) ⟨715851, by rfl⟩ : syracuseStep 1908937 = 1431703) (by norm_num)
theorem B2261213 : Blo 1506950 2261213 := bbase (se 3 (by rfl) ⟨423977, by rfl⟩ : syracuseStep 2261213 = 847955) (by norm_num)
theorem B1695973 : Blo 1506950 1695973 := bbase (se 4 (by rfl) ⟨158997, by rfl⟩ : syracuseStep 1695973 = 317995) (by norm_num)
theorem B2261237 : Blo 1506950 2261237 := bbase (se 5 (by rfl) ⟨105995, by rfl⟩ : syracuseStep 2261237 = 211991) (by norm_num)
theorem B3219709 : Blo 1506950 3219709 := bbase (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) (by norm_num)
theorem B1696009 : Blo 1506950 1696009 := bbase (se 2 (by rfl) ⟨636003, by rfl⟩ : syracuseStep 1696009 = 1272007) (by norm_num)
theorem B3391757 : Blo 1506950 3391757 := bbase (se 3 (by rfl) ⟨635954, by rfl⟩ : syracuseStep 3391757 = 1271909) (by norm_num)
theorem B2261261 : Blo 1506950 2261261 := bbase (se 3 (by rfl) ⟨423986, by rfl⟩ : syracuseStep 2261261 = 847973) (by norm_num)
theorem B7635221 : Blo 1506950 7635221 := bbase (se 6 (by rfl) ⟨178950, by rfl⟩ : syracuseStep 7635221 = 357901) (by norm_num)
theorem B1810721 : Blo 1506950 1810721 := bbase (se 2 (by rfl) ⟨679020, by rfl⟩ : syracuseStep 1810721 = 1358041) (by norm_num)
theorem B2261285 : Blo 1506950 2261285 := bbase (se 4 (by rfl) ⟨211995, by rfl⟩ : syracuseStep 2261285 = 423991) (by norm_num)
theorem B1696045 : Blo 1506950 1696045 := bbase (se 3 (by rfl) ⟨318008, by rfl⟩ : syracuseStep 1696045 = 636017) (by norm_num)
theorem B2261309 : Blo 1506950 2261309 := bbase (se 3 (by rfl) ⟨423995, by rfl⟩ : syracuseStep 2261309 = 847991) (by norm_num)
theorem B1696081 : Blo 1506950 1696081 := bbase (se 2 (by rfl) ⟨636030, by rfl⟩ : syracuseStep 1696081 = 1272061) (by norm_num)
theorem B3391829 : Blo 1506950 3391829 := bbase (se 10 (by rfl) ⟨4968, by rfl⟩ : syracuseStep 3391829 = 9937) (by norm_num)
theorem B2261333 : Blo 1506950 2261333 := bbase (se 10 (by rfl) ⟨3312, by rfl⟩ : syracuseStep 2261333 = 6625) (by norm_num)
theorem B3817813 : Blo 1506950 3817813 := bbase (se 10 (by rfl) ⟨5592, by rfl⟩ : syracuseStep 3817813 = 11185) (by norm_num)
theorem B2261357 : Blo 1506950 2261357 := bbase (se 3 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 2261357 = 848009) (by norm_num)
theorem B1696117 : Blo 1506950 1696117 := bbase (se 5 (by rfl) ⟨79505, by rfl⟩ : syracuseStep 1696117 = 159011) (by norm_num)
theorem B1909109 : Blo 1506950 1909109 := bbase (se 5 (by rfl) ⟨89489, by rfl⟩ : syracuseStep 1909109 = 178979) (by norm_num)
theorem B2261381 : Blo 1506950 2261381 := bbase (se 4 (by rfl) ⟨212004, by rfl⟩ : syracuseStep 2261381 = 424009) (by norm_num)
theorem B4293013 : Blo 1506950 4293013 := bbase (se 6 (by rfl) ⟨100617, by rfl⟩ : syracuseStep 4293013 = 201235) (by norm_num)
theorem B8151445 : Blo 1506950 8151445 := bbase (se 6 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 8151445 = 382099) (by norm_num)
theorem B1696153 : Blo 1506950 1696153 := bbase (se 2 (by rfl) ⟨636057, by rfl⟩ : syracuseStep 1696153 = 1272115) (by norm_num)
theorem B3391901 : Blo 1506950 3391901 := bbase (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) (by norm_num)
theorem B2261405 : Blo 1506950 2261405 := bbase (se 3 (by rfl) ⟨424013, by rfl⟩ : syracuseStep 2261405 = 848027) (by norm_num)
theorem B1909165 : Blo 1506950 1909165 := bbase (se 3 (by rfl) ⟨357968, by rfl⟩ : syracuseStep 1909165 = 715937) (by norm_num)
theorem B2261429 : Blo 1506950 2261429 := bbase (se 5 (by rfl) ⟨106004, by rfl⟩ : syracuseStep 2261429 = 212009) (by norm_num)
theorem B5726645 : Blo 1506950 5726645 := bbase (se 5 (by rfl) ⟨268436, by rfl⟩ : syracuseStep 5726645 = 536873) (by norm_num)
theorem B1696189 : Blo 1506950 1696189 := bbase (se 3 (by rfl) ⟨318035, by rfl⟩ : syracuseStep 1696189 = 636071) (by norm_num)
theorem B3817925 : Blo 1506950 3817925 := bbase (se 4 (by rfl) ⟨357930, by rfl⟩ : syracuseStep 3817925 = 715861) (by norm_num)
theorem B2261453 : Blo 1506950 2261453 := bbase (se 3 (by rfl) ⟨424022, by rfl⟩ : syracuseStep 2261453 = 848045) (by norm_num)
theorem B1696225 : Blo 1506950 1696225 := bbase (se 2 (by rfl) ⟨636084, by rfl⟩ : syracuseStep 1696225 = 1272169) (by norm_num)
theorem B5087717 : Blo 1506950 5087717 := bbase (se 4 (by rfl) ⟨476973, by rfl⟩ : syracuseStep 5087717 = 953947) (by norm_num)
theorem B3391973 : Blo 1506950 3391973 := bbase (se 4 (by rfl) ⟨317997, by rfl⟩ : syracuseStep 3391973 = 635995) (by norm_num)
theorem B2261477 : Blo 1506950 2261477 := bbase (se 4 (by rfl) ⟨212013, by rfl⟩ : syracuseStep 2261477 = 424027) (by norm_num)
theorem B3621365 : Blo 1506950 3621365 := bbase (se 5 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 3621365 = 339503) (by norm_num)
theorem B2261501 : Blo 1506950 2261501 := bbase (se 3 (by rfl) ⟨424031, by rfl⟩ : syracuseStep 2261501 = 848063) (by norm_num)
theorem B1696261 : Blo 1506950 1696261 := bbase (se 4 (by rfl) ⟨159024, by rfl⟩ : syracuseStep 1696261 = 318049) (by norm_num)
theorem B1909261 : Blo 1506950 1909261 := bbase (se 3 (by rfl) ⟨357986, by rfl⟩ : syracuseStep 1909261 = 715973) (by norm_num)
theorem B2261525 : Blo 1506950 2261525 := bbase (se 6 (by rfl) ⟨53004, by rfl⟩ : syracuseStep 2261525 = 106009) (by norm_num)
theorem B2146837 : Blo 1506950 2146837 := bbase (se 6 (by rfl) ⟨50316, by rfl⟩ : syracuseStep 2146837 = 100633) (by norm_num)
theorem B1696297 : Blo 1506950 1696297 := bbase (se 2 (by rfl) ⟨636111, by rfl⟩ : syracuseStep 1696297 = 1272223) (by norm_num)
theorem B3392045 : Blo 1506950 3392045 := bbase (se 3 (by rfl) ⟨636008, by rfl⟩ : syracuseStep 3392045 = 1272017) (by norm_num)
theorem B2261549 : Blo 1506950 2261549 := bbase (se 3 (by rfl) ⟨424040, by rfl⟩ : syracuseStep 2261549 = 848081) (by norm_num)
theorem B2261573 : Blo 1506950 2261573 := bbase (se 4 (by rfl) ⟨212022, by rfl⟩ : syracuseStep 2261573 = 424045) (by norm_num)
theorem B1696333 : Blo 1506950 1696333 := bbase (se 3 (by rfl) ⟨318062, by rfl⟩ : syracuseStep 1696333 = 636125) (by norm_num)
theorem B2261597 : Blo 1506950 2261597 := bbase (se 3 (by rfl) ⟨424049, by rfl⟩ : syracuseStep 2261597 = 848099) (by norm_num)
theorem B1696369 : Blo 1506950 1696369 := bbase (se 2 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 1696369 = 1272277) (by norm_num)
theorem B3392117 : Blo 1506950 3392117 := bbase (se 5 (by rfl) ⟨159005, by rfl⟩ : syracuseStep 3392117 = 318011) (by norm_num)
theorem B2261621 : Blo 1506950 2261621 := bbase (se 5 (by rfl) ⟨106013, by rfl⟩ : syracuseStep 2261621 = 212027) (by norm_num)
theorem B3818117 : Blo 1506950 3818117 := bbase (se 4 (by rfl) ⟨357948, by rfl⟩ : syracuseStep 3818117 = 715897) (by norm_num)
theorem B2261645 : Blo 1506950 2261645 := bbase (se 3 (by rfl) ⟨424058, by rfl⟩ : syracuseStep 2261645 = 848117) (by norm_num)
theorem B1696405 : Blo 1506950 1696405 := bbase (se 6 (by rfl) ⟨39759, by rfl⟩ : syracuseStep 1696405 = 79519) (by norm_num)
theorem B2261669 : Blo 1506950 2261669 := bbase (se 4 (by rfl) ⟨212031, by rfl⟩ : syracuseStep 2261669 = 424063) (by norm_num)
theorem B1696441 : Blo 1506950 1696441 := bbase (se 2 (by rfl) ⟨636165, by rfl⟩ : syracuseStep 1696441 = 1272331) (by norm_num)
theorem B3392189 : Blo 1506950 3392189 := bbase (se 3 (by rfl) ⟨636035, by rfl⟩ : syracuseStep 3392189 = 1272071) (by norm_num)
theorem B2261693 : Blo 1506950 2261693 := bbase (se 3 (by rfl) ⟨424067, by rfl⟩ : syracuseStep 2261693 = 848135) (by norm_num)
theorem B1909433 : Blo 1506950 1909433 := bbase (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) (by norm_num)
theorem B2261717 : Blo 1506950 2261717 := bbase (se 7 (by rfl) ⟨26504, by rfl⟩ : syracuseStep 2261717 = 53009) (by norm_num)
theorem B5726933 : Blo 1506950 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B1696477 : Blo 1506950 1696477 := bbase (se 3 (by rfl) ⟨318089, by rfl⟩ : syracuseStep 1696477 = 636179) (by norm_num)
theorem B2261741 : Blo 1506950 2261741 := bbase (se 3 (by rfl) ⟨424076, by rfl⟩ : syracuseStep 2261741 = 848153) (by norm_num)
theorem B1909489 : Blo 1506950 1909489 := bbase (se 2 (by rfl) ⟨716058, by rfl⟩ : syracuseStep 1909489 = 1432117) (by norm_num)
theorem B1696513 : Blo 1506950 1696513 := bbase (se 2 (by rfl) ⟨636192, by rfl⟩ : syracuseStep 1696513 = 1272385) (by norm_num)
theorem B3097349 : Blo 1506950 3097349 := bbase (se 4 (by rfl) ⟨290376, by rfl⟩ : syracuseStep 3097349 = 580753) (by norm_num)
theorem B3392261 : Blo 1506950 3392261 := bbase (se 4 (by rfl) ⟨318024, by rfl⟩ : syracuseStep 3392261 = 636049) (by norm_num)
theorem B2261765 : Blo 1506950 2261765 := bbase (se 4 (by rfl) ⟨212040, by rfl⟩ : syracuseStep 2261765 = 424081) (by norm_num)
theorem B2261789 : Blo 1506950 2261789 := bbase (se 3 (by rfl) ⟨424085, by rfl⟩ : syracuseStep 2261789 = 848171) (by norm_num)
theorem B1696549 : Blo 1506950 1696549 := bbase (se 4 (by rfl) ⟨159051, by rfl⟩ : syracuseStep 1696549 = 318103) (by norm_num)
theorem B7250725 : Blo 1506950 7250725 := bbase (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) (by norm_num)
theorem B2261813 : Blo 1506950 2261813 := bbase (se 5 (by rfl) ⟨106022, by rfl⟩ : syracuseStep 2261813 = 212045) (by norm_num)
theorem B1811269 : Blo 1506950 1811269 := bbase (se 4 (by rfl) ⟨169806, by rfl⟩ : syracuseStep 1811269 = 339613) (by norm_num)
theorem B1696585 : Blo 1506950 1696585 := bbase (se 2 (by rfl) ⟨636219, by rfl⟩ : syracuseStep 1696585 = 1272439) (by norm_num)
theorem B3392333 : Blo 1506950 3392333 := bbase (se 3 (by rfl) ⟨636062, by rfl⟩ : syracuseStep 3392333 = 1272125) (by norm_num)
theorem B2261837 : Blo 1506950 2261837 := bbase (se 3 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 2261837 = 848189) (by norm_num)
theorem B1909585 : Blo 1506950 1909585 := bbase (se 2 (by rfl) ⟨716094, by rfl⟩ : syracuseStep 1909585 = 1432189) (by norm_num)
theorem B2261861 : Blo 1506950 2261861 := bbase (se 4 (by rfl) ⟨212049, by rfl⟩ : syracuseStep 2261861 = 424099) (by norm_num)
theorem B1696621 : Blo 1506950 1696621 := bbase (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) (by norm_num)
theorem B2261885 : Blo 1506950 2261885 := bbase (se 3 (by rfl) ⟨424103, by rfl⟩ : syracuseStep 2261885 = 848207) (by norm_num)
theorem B1549201 : Blo 1506950 1549201 := bbase (se 2 (by rfl) ⟨580950, by rfl⟩ : syracuseStep 1549201 = 1161901) (by norm_num)
theorem B1696657 : Blo 1506950 1696657 := bbase (se 2 (by rfl) ⟨636246, by rfl⟩ : syracuseStep 1696657 = 1272493) (by norm_num)
theorem B5088149 : Blo 1506950 5088149 := bbase (se 6 (by rfl) ⟨119253, by rfl⟩ : syracuseStep 5088149 = 238507) (by norm_num)
theorem B3392405 : Blo 1506950 3392405 := bbase (se 6 (by rfl) ⟨79509, by rfl⟩ : syracuseStep 3392405 = 159019) (by norm_num)
theorem B2261909 : Blo 1506950 2261909 := bbase (se 6 (by rfl) ⟨53013, by rfl⟩ : syracuseStep 2261909 = 106027) (by norm_num)
theorem B2261933 : Blo 1506950 2261933 := bbase (se 3 (by rfl) ⟨424112, by rfl⟩ : syracuseStep 2261933 = 848225) (by norm_num)
theorem B1696693 : Blo 1506950 1696693 := bbase (se 5 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 1696693 = 159065) (by norm_num)
theorem B2261957 : Blo 1506950 2261957 := bbase (se 4 (by rfl) ⟨212058, by rfl⟩ : syracuseStep 2261957 = 424117) (by norm_num)
theorem B3867605 : Blo 1506950 3867605 := bbase (se 7 (by rfl) ⟨45323, by rfl⟩ : syracuseStep 3867605 = 90647) (by norm_num)
theorem B1811413 : Blo 1506950 1811413 := bbase (se 7 (by rfl) ⟨21227, by rfl⟩ : syracuseStep 1811413 = 42455) (by norm_num)
theorem B48915413 : Blo 1506950 48915413 := bbase (se 7 (by rfl) ⟨573227, by rfl⟩ : syracuseStep 48915413 = 1146455) (by norm_num)
theorem B1696729 : Blo 1506950 1696729 := bbase (se 2 (by rfl) ⟨636273, by rfl⟩ : syracuseStep 1696729 = 1272547) (by norm_num)
theorem B3392477 : Blo 1506950 3392477 := bbase (se 3 (by rfl) ⟨636089, by rfl⟩ : syracuseStep 3392477 = 1272179) (by norm_num)
theorem B2261981 : Blo 1506950 2261981 := bbase (se 3 (by rfl) ⟨424121, by rfl⟩ : syracuseStep 2261981 = 848243) (by norm_num)
theorem B3818461 : Blo 1506950 3818461 := bbase (se 3 (by rfl) ⟨715961, by rfl⟩ : syracuseStep 3818461 = 1431923) (by norm_num)
theorem B2262005 : Blo 1506950 2262005 := bbase (se 5 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 2262005 = 212063) (by norm_num)
theorem B1696765 : Blo 1506950 1696765 := bbase (se 3 (by rfl) ⟨318143, by rfl⟩ : syracuseStep 1696765 = 636287) (by norm_num)
theorem B1909757 : Blo 1506950 1909757 := bbase (se 3 (by rfl) ⟨358079, by rfl⟩ : syracuseStep 1909757 = 716159) (by norm_num)
theorem B2262029 : Blo 1506950 2262029 := bbase (se 3 (by rfl) ⟨424130, by rfl⟩ : syracuseStep 2262029 = 848261) (by norm_num)
theorem B1696801 : Blo 1506950 1696801 := bbase (se 2 (by rfl) ⟨636300, by rfl⟩ : syracuseStep 1696801 = 1272601) (by norm_num)
theorem B3392549 : Blo 1506950 3392549 := bbase (se 4 (by rfl) ⟨318051, by rfl⟩ : syracuseStep 3392549 = 636103) (by norm_num)
theorem B2262053 : Blo 1506950 2262053 := bbase (se 4 (by rfl) ⟨212067, by rfl⟩ : syracuseStep 2262053 = 424135) (by norm_num)
theorem B2262077 : Blo 1506950 2262077 := bbase (se 3 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 2262077 = 848279) (by norm_num)
theorem B1696837 : Blo 1506950 1696837 := bbase (se 4 (by rfl) ⟨159078, by rfl⟩ : syracuseStep 1696837 = 318157) (by norm_num)
theorem B3818573 : Blo 1506950 3818573 := bbase (se 3 (by rfl) ⟨715982, by rfl⟩ : syracuseStep 3818573 = 1431965) (by norm_num)
theorem B2262101 : Blo 1506950 2262101 := bbase (se 8 (by rfl) ⟨13254, by rfl⟩ : syracuseStep 2262101 = 26509) (by norm_num)
theorem B6530149 : Blo 1506950 6530149 := bbase (se 4 (by rfl) ⟨612201, by rfl⟩ : syracuseStep 6530149 = 1224403) (by norm_num)
theorem B2147429 : Blo 1506950 2147429 := bbase (se 4 (by rfl) ⟨201321, by rfl⟩ : syracuseStep 2147429 = 402643) (by norm_num)
theorem B1696873 : Blo 1506950 1696873 := bbase (se 2 (by rfl) ⟨636327, by rfl⟩ : syracuseStep 1696873 = 1272655) (by norm_num)
theorem B3392621 : Blo 1506950 3392621 := bbase (se 3 (by rfl) ⟨636116, by rfl⟩ : syracuseStep 3392621 = 1272233) (by norm_num)
theorem B2262125 : Blo 1506950 2262125 := bbase (se 3 (by rfl) ⟨424148, by rfl⟩ : syracuseStep 2262125 = 848297) (by norm_num)
theorem B3220597 : Blo 1506950 3220597 := bbase (se 5 (by rfl) ⟨150965, by rfl⟩ : syracuseStep 3220597 = 301931) (by norm_num)
theorem B6882421 : Blo 1506950 6882421 := bbase (se 5 (by rfl) ⟨322613, by rfl⟩ : syracuseStep 6882421 = 645227) (by norm_num)
theorem B3671165 : Blo 1506950 3671165 := bbase (se 3 (by rfl) ⟨688343, by rfl⟩ : syracuseStep 3671165 = 1376687) (by norm_num)
theorem B5432453 : Blo 1506950 5432453 := bbase (se 4 (by rfl) ⟨509292, by rfl⟩ : syracuseStep 5432453 = 1018585) (by norm_num)
theorem B2262149 : Blo 1506950 2262149 := bbase (se 4 (by rfl) ⟨212076, by rfl⟩ : syracuseStep 2262149 = 424153) (by norm_num)
theorem B1696909 : Blo 1506950 1696909 := bbase (se 3 (by rfl) ⟨318170, by rfl⟩ : syracuseStep 1696909 = 636341) (by norm_num)
theorem B2262173 : Blo 1506950 2262173 := bbase (se 3 (by rfl) ⟨424157, by rfl⟩ : syracuseStep 2262173 = 848315) (by norm_num)
theorem B1696945 : Blo 1506950 1696945 := bbase (se 2 (by rfl) ⟨636354, by rfl⟩ : syracuseStep 1696945 = 1272709) (by norm_num)
theorem B3392693 : Blo 1506950 3392693 := bbase (se 5 (by rfl) ⟨159032, by rfl⟩ : syracuseStep 3392693 = 318065) (by norm_num)
theorem B2262197 : Blo 1506950 2262197 := bbase (se 5 (by rfl) ⟨106040, by rfl⟩ : syracuseStep 2262197 = 212081) (by norm_num)
theorem B2147509 : Blo 1506950 2147509 := bbase (se 5 (by rfl) ⟨100664, by rfl⟩ : syracuseStep 2147509 = 201329) (by norm_num)
theorem B2262221 : Blo 1506950 2262221 := bbase (se 3 (by rfl) ⟨424166, by rfl⟩ : syracuseStep 2262221 = 848333) (by norm_num)
theorem B1696981 : Blo 1506950 1696981 := bbase (se 7 (by rfl) ⟨19886, by rfl⟩ : syracuseStep 1696981 = 39773) (by norm_num)
theorem B2262245 : Blo 1506950 2262245 := bbase (se 4 (by rfl) ⟨212085, by rfl⟩ : syracuseStep 2262245 = 424171) (by norm_num)
theorem B3220717 : Blo 1506950 3220717 := bbase (se 3 (by rfl) ⟨603884, by rfl⟩ : syracuseStep 3220717 = 1207769) (by norm_num)
theorem B1697017 : Blo 1506950 1697017 := bbase (se 2 (by rfl) ⟨636381, by rfl⟩ : syracuseStep 1697017 = 1272763) (by norm_num)
theorem B3392765 : Blo 1506950 3392765 := bbase (se 3 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 3392765 = 1272287) (by norm_num)
theorem B2262269 : Blo 1506950 2262269 := bbase (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) (by norm_num)
theorem B3818765 : Blo 1506950 3818765 := bbase (se 3 (by rfl) ⟨716018, by rfl⟩ : syracuseStep 3818765 = 1432037) (by norm_num)
theorem B2262293 : Blo 1506950 2262293 := bbase (se 6 (by rfl) ⟨53022, by rfl⟩ : syracuseStep 2262293 = 106045) (by norm_num)
theorem B1697053 : Blo 1506950 1697053 := bbase (se 3 (by rfl) ⟨318197, by rfl⟩ : syracuseStep 1697053 = 636395) (by norm_num)
theorem B2262317 : Blo 1506950 2262317 := bbase (se 3 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 2262317 = 848369) (by norm_num)
theorem B2147629 : Blo 1506950 2147629 := bbase (se 3 (by rfl) ⟨402680, by rfl⟩ : syracuseStep 2147629 = 805361) (by norm_num)
theorem B1697089 : Blo 1506950 1697089 := bbase (se 2 (by rfl) ⟨636408, by rfl⟩ : syracuseStep 1697089 = 1272817) (by norm_num)
theorem B5088581 : Blo 1506950 5088581 := bbase (se 4 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 5088581 = 954109) (by norm_num)
theorem B3392837 : Blo 1506950 3392837 := bbase (se 4 (by rfl) ⟨318078, by rfl⟩ : syracuseStep 3392837 = 636157) (by norm_num)
theorem B2262341 : Blo 1506950 2262341 := bbase (se 4 (by rfl) ⟨212094, by rfl⟩ : syracuseStep 2262341 = 424189) (by norm_num)
theorem B6112597 : Blo 1506950 6112597 := bbase (se 12 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 6112597 = 4477) (by norm_num)
theorem B2262365 : Blo 1506950 2262365 := bbase (se 3 (by rfl) ⟨424193, by rfl⟩ : syracuseStep 2262365 = 848387) (by norm_num)
theorem B1697125 : Blo 1506950 1697125 := bbase (se 4 (by rfl) ⟨159105, by rfl⟩ : syracuseStep 1697125 = 318211) (by norm_num)
theorem B2262389 : Blo 1506950 2262389 := bbase (se 5 (by rfl) ⟨106049, by rfl⟩ : syracuseStep 2262389 = 212099) (by norm_num)
theorem B1697161 : Blo 1506950 1697161 := bbase (se 2 (by rfl) ⟨636435, by rfl⟩ : syracuseStep 1697161 = 1272871) (by norm_num)
theorem B3392909 : Blo 1506950 3392909 := bbase (se 3 (by rfl) ⟨636170, by rfl⟩ : syracuseStep 3392909 = 1272341) (by norm_num)
theorem B2262413 : Blo 1506950 2262413 := bbase (se 3 (by rfl) ⟨424202, by rfl⟩ : syracuseStep 2262413 = 848405) (by norm_num)
theorem B2147725 : Blo 1506950 2147725 := bbase (se 3 (by rfl) ⟨402698, by rfl⟩ : syracuseStep 2147725 = 805397) (by norm_num)
theorem B5432741 : Blo 1506950 5432741 := bbase (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) (by norm_num)
theorem B2262437 : Blo 1506950 2262437 := bbase (se 4 (by rfl) ⟨212103, by rfl⟩ : syracuseStep 2262437 = 424207) (by norm_num)
theorem B1697197 : Blo 1506950 1697197 := bbase (se 3 (by rfl) ⟨318224, by rfl⟩ : syracuseStep 1697197 = 636449) (by norm_num)
theorem B2262461 : Blo 1506950 2262461 := bbase (se 3 (by rfl) ⟨424211, by rfl⟩ : syracuseStep 2262461 = 848423) (by norm_num)
theorem B1697233 : Blo 1506950 1697233 := bbase (se 2 (by rfl) ⟨636462, by rfl⟩ : syracuseStep 1697233 = 1272925) (by norm_num)
theorem B3392981 : Blo 1506950 3392981 := bbase (se 7 (by rfl) ⟨39761, by rfl⟩ : syracuseStep 3392981 = 79523) (by norm_num)
theorem B2262485 : Blo 1506950 2262485 := bbase (se 7 (by rfl) ⟨26513, by rfl⟩ : syracuseStep 2262485 = 53027) (by norm_num)
theorem B3220973 : Blo 1506950 3220973 := bbase (se 3 (by rfl) ⟨603932, by rfl⟩ : syracuseStep 3220973 = 1207865) (by norm_num)
theorem B2262509 : Blo 1506950 2262509 := bbase (se 3 (by rfl) ⟨424220, by rfl⟩ : syracuseStep 2262509 = 848441) (by norm_num)
theorem B1697269 : Blo 1506950 1697269 := bbase (se 5 (by rfl) ⟨79559, by rfl⟩ : syracuseStep 1697269 = 159119) (by norm_num)
theorem B3057149 : Blo 1506950 3057149 := bbase (se 3 (by rfl) ⟨573215, by rfl⟩ : syracuseStep 3057149 = 1146431) (by norm_num)
theorem B2262533 : Blo 1506950 2262533 := bbase (se 4 (by rfl) ⟨212112, by rfl⟩ : syracuseStep 2262533 = 424225) (by norm_num)
theorem B1697305 : Blo 1506950 1697305 := bbase (se 2 (by rfl) ⟨636489, by rfl⟩ : syracuseStep 1697305 = 1272979) (by norm_num)
theorem B3393053 : Blo 1506950 3393053 := bbase (se 3 (by rfl) ⟨636197, by rfl⟩ : syracuseStep 3393053 = 1272395) (by norm_num)
theorem B2262557 : Blo 1506950 2262557 := bbase (se 3 (by rfl) ⟨424229, by rfl⟩ : syracuseStep 2262557 = 848459) (by norm_num)
theorem B2516509 : Blo 1506950 2516509 := bbase (se 3 (by rfl) ⟨471845, by rfl⟩ : syracuseStep 2516509 = 943691) (by norm_num)
theorem B7636517 : Blo 1506950 7636517 := bbase (se 4 (by rfl) ⟨715923, by rfl⟩ : syracuseStep 7636517 = 1431847) (by norm_num)
theorem B5432885 : Blo 1506950 5432885 := bbase (se 5 (by rfl) ⟨254666, by rfl⟩ : syracuseStep 5432885 = 509333) (by norm_num)
theorem B2262581 : Blo 1506950 2262581 := bbase (se 5 (by rfl) ⟨106058, by rfl⟩ : syracuseStep 2262581 = 212117) (by norm_num)
theorem B1697341 : Blo 1506950 1697341 := bbase (se 3 (by rfl) ⟨318251, by rfl⟩ : syracuseStep 1697341 = 636503) (by norm_num)
theorem B2262605 : Blo 1506950 2262605 := bbase (se 3 (by rfl) ⟨424238, by rfl⟩ : syracuseStep 2262605 = 848477) (by norm_num)
theorem B1697377 : Blo 1506950 1697377 := bbase (se 2 (by rfl) ⟨636516, by rfl⟩ : syracuseStep 1697377 = 1273033) (by norm_num)
theorem B3393125 : Blo 1506950 3393125 := bbase (se 4 (by rfl) ⟨318105, by rfl⟩ : syracuseStep 3393125 = 636211) (by norm_num)
theorem B2262629 : Blo 1506950 2262629 := bbase (se 4 (by rfl) ⟨212121, by rfl⟩ : syracuseStep 2262629 = 424243) (by norm_num)
theorem B3819109 : Blo 1506950 3819109 := bbase (se 4 (by rfl) ⟨358041, by rfl⟩ : syracuseStep 3819109 = 716083) (by norm_num)
theorem B2262653 : Blo 1506950 2262653 := bbase (se 3 (by rfl) ⟨424247, by rfl⟩ : syracuseStep 2262653 = 848495) (by norm_num)
theorem B1697413 : Blo 1506950 1697413 := bbase (se 4 (by rfl) ⟨159132, by rfl⟩ : syracuseStep 1697413 = 318265) (by norm_num)
theorem B2262677 : Blo 1506950 2262677 := bbase (se 6 (by rfl) ⟨53031, by rfl⟩ : syracuseStep 2262677 = 106063) (by norm_num)
theorem B1697449 : Blo 1506950 1697449 := bbase (se 2 (by rfl) ⟨636543, by rfl⟩ : syracuseStep 1697449 = 1273087) (by norm_num)
theorem B3393197 : Blo 1506950 3393197 := bbase (se 3 (by rfl) ⟨636224, by rfl⟩ : syracuseStep 3393197 = 1272449) (by norm_num)
theorem B2262701 : Blo 1506950 2262701 := bbase (se 3 (by rfl) ⟨424256, by rfl⟩ : syracuseStep 2262701 = 848513) (by norm_num)
theorem B2262725 : Blo 1506950 2262725 := bbase (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) (by norm_num)
theorem B1697485 : Blo 1506950 1697485 := bbase (se 3 (by rfl) ⟨318278, by rfl⟩ : syracuseStep 1697485 = 636557) (by norm_num)
theorem B3819221 : Blo 1506950 3819221 := bbase (se 7 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 3819221 = 89513) (by norm_num)
theorem B2262749 : Blo 1506950 2262749 := bbase (se 3 (by rfl) ⟨424265, by rfl⟩ : syracuseStep 2262749 = 848531) (by norm_num)
theorem B1697521 : Blo 1506950 1697521 := bbase (se 2 (by rfl) ⟨636570, by rfl⟩ : syracuseStep 1697521 = 1273141) (by norm_num)
theorem B5089013 : Blo 1506950 5089013 := bbase (se 5 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 5089013 = 477095) (by norm_num)
theorem B3393269 : Blo 1506950 3393269 := bbase (se 5 (by rfl) ⟨159059, by rfl⟩ : syracuseStep 3393269 = 318119) (by norm_num)
theorem B2262773 : Blo 1506950 2262773 := bbase (se 5 (by rfl) ⟨106067, by rfl⟩ : syracuseStep 2262773 = 212135) (by norm_num)
theorem B2262797 : Blo 1506950 2262797 := bbase (se 3 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 2262797 = 848549) (by norm_num)
theorem B1697557 : Blo 1506950 1697557 := bbase (se 6 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 1697557 = 79573) (by norm_num)
theorem B2262821 : Blo 1506950 2262821 := bbase (se 4 (by rfl) ⟨212139, by rfl⟩ : syracuseStep 2262821 = 424279) (by norm_num)
theorem B3393341 : Blo 1506950 3393341 := bbase (se 3 (by rfl) ⟨636251, by rfl⟩ : syracuseStep 3393341 = 1272503) (by norm_num)
theorem B2262845 : Blo 1506950 2262845 := bbase (se 3 (by rfl) ⟨424283, by rfl⟩ : syracuseStep 2262845 = 848567) (by norm_num)
theorem B2262869 : Blo 1506950 2262869 := bbase (se 9 (by rfl) ⟨6629, by rfl⟩ : syracuseStep 2262869 = 13259) (by norm_num)
theorem B2262893 : Blo 1506950 2262893 := bbase (se 3 (by rfl) ⟨424292, by rfl⟩ : syracuseStep 2262893 = 848585) (by norm_num)
theorem B5728117 : Blo 1506950 5728117 := bbase (se 5 (by rfl) ⟨268505, by rfl⟩ : syracuseStep 5728117 = 537011) (by norm_num)
theorem B2148221 : Blo 1506950 2148221 := bbase (se 3 (by rfl) ⟨402791, by rfl⟩ : syracuseStep 2148221 = 805583) (by norm_num)
theorem B3393413 : Blo 1506950 3393413 := bbase (se 4 (by rfl) ⟨318132, by rfl⟩ : syracuseStep 3393413 = 636265) (by norm_num)
theorem B2262917 : Blo 1506950 2262917 := bbase (se 4 (by rfl) ⟨212148, by rfl⟩ : syracuseStep 2262917 = 424297) (by norm_num)
theorem B3819413 : Blo 1506950 3819413 := bbase (se 6 (by rfl) ⟨89517, by rfl⟩ : syracuseStep 3819413 = 179035) (by norm_num)
theorem B2262941 : Blo 1506950 2262941 := bbase (se 3 (by rfl) ⟨424301, by rfl⟩ : syracuseStep 2262941 = 848603) (by norm_num)
theorem B9168821 : Blo 1506950 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B2262965 : Blo 1506950 2262965 := bbase (se 5 (by rfl) ⟨106076, by rfl⟩ : syracuseStep 2262965 = 212153) (by norm_num)
theorem B3393485 : Blo 1506950 3393485 := bbase (se 3 (by rfl) ⟨636278, by rfl⟩ : syracuseStep 3393485 = 1272557) (by norm_num)
theorem B2262989 : Blo 1506950 2262989 := bbase (se 3 (by rfl) ⟨424310, by rfl⟩ : syracuseStep 2262989 = 848621) (by norm_num)
theorem B2861021 : Blo 1506950 2861021 := bbase (se 3 (by rfl) ⟨536441, by rfl⟩ : syracuseStep 2861021 = 1072883) (by norm_num)
theorem B2263013 : Blo 1506950 2263013 := bbase (se 4 (by rfl) ⟨212157, by rfl⟩ : syracuseStep 2263013 = 424315) (by norm_num)
theorem B1812461 : Blo 1506950 1812461 := bbase (se 3 (by rfl) ⟨339836, by rfl⟩ : syracuseStep 1812461 = 679673) (by norm_num)
theorem B1935353 : Blo 1506950 1935353 := bbase (se 2 (by rfl) ⟨725757, by rfl⟩ : syracuseStep 1935353 = 1451515) (by norm_num)
theorem B2263037 : Blo 1506950 2263037 := bbase (se 3 (by rfl) ⟨424319, by rfl⟩ : syracuseStep 2263037 = 848639) (by norm_num)
theorem B3393557 : Blo 1506950 3393557 := bbase (se 6 (by rfl) ⟨79536, by rfl⟩ : syracuseStep 3393557 = 159073) (by norm_num)
theorem B2263061 : Blo 1506950 2263061 := bbase (se 6 (by rfl) ⟨53040, by rfl⟩ : syracuseStep 2263061 = 106081) (by norm_num)
theorem B2263085 : Blo 1506950 2263085 := bbase (se 3 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 2263085 = 848657) (by norm_num)
theorem B2263109 : Blo 1506950 2263109 := bbase (se 4 (by rfl) ⟨212166, by rfl⟩ : syracuseStep 2263109 = 424333) (by norm_num)
theorem B3393629 : Blo 1506950 3393629 := bbase (se 3 (by rfl) ⟨636305, by rfl⟩ : syracuseStep 3393629 = 1272611) (by norm_num)
theorem B2263133 : Blo 1506950 2263133 := bbase (se 3 (by rfl) ⟨424337, by rfl⟩ : syracuseStep 2263133 = 848675) (by norm_num)
theorem B2861173 : Blo 1506950 2861173 := bbase (se 5 (by rfl) ⟨134117, by rfl⟩ : syracuseStep 2861173 = 268235) (by norm_num)
theorem B2263157 : Blo 1506950 2263157 := bbase (se 5 (by rfl) ⟨106085, by rfl⟩ : syracuseStep 2263157 = 212171) (by norm_num)
theorem B2263181 : Blo 1506950 2263181 := bbase (se 3 (by rfl) ⟨424346, by rfl⟩ : syracuseStep 2263181 = 848693) (by norm_num)
theorem B5089445 : Blo 1506950 5089445 := bbase (se 4 (by rfl) ⟨477135, by rfl⟩ : syracuseStep 5089445 = 954271) (by norm_num)
theorem B3393701 : Blo 1506950 3393701 := bbase (se 4 (by rfl) ⟨318159, by rfl⟩ : syracuseStep 3393701 = 636319) (by norm_num)
theorem B5728421 : Blo 1506950 5728421 := bbase (se 4 (by rfl) ⟨537039, by rfl⟩ : syracuseStep 5728421 = 1074079) (by norm_num)
theorem B2263205 : Blo 1506950 2263205 := bbase (se 4 (by rfl) ⟨212175, by rfl⟩ : syracuseStep 2263205 = 424351) (by norm_num)
theorem B2263229 : Blo 1506950 2263229 := bbase (se 3 (by rfl) ⟨424355, by rfl⟩ : syracuseStep 2263229 = 848711) (by norm_num)
theorem B3623125 : Blo 1506950 3623125 := bbase (se 7 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 3623125 = 84917) (by norm_num)
theorem B2263253 : Blo 1506950 2263253 := bbase (se 7 (by rfl) ⟨26522, by rfl⟩ : syracuseStep 2263253 = 53045) (by norm_num)
theorem B3262693 : Blo 1506950 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B3393773 : Blo 1506950 3393773 := bbase (se 3 (by rfl) ⟨636332, by rfl⟩ : syracuseStep 3393773 = 1272665) (by norm_num)
theorem B2263277 : Blo 1506950 2263277 := bbase (se 3 (by rfl) ⟨424364, by rfl⟩ : syracuseStep 2263277 = 848729) (by norm_num)
theorem B2263301 : Blo 1506950 2263301 := bbase (se 4 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 2263301 = 424369) (by norm_num)
theorem B2263325 : Blo 1506950 2263325 := bbase (se 3 (by rfl) ⟨424373, by rfl⟩ : syracuseStep 2263325 = 848747) (by norm_num)
theorem B3393845 : Blo 1506950 3393845 := bbase (se 5 (by rfl) ⟨159086, by rfl⟩ : syracuseStep 3393845 = 318173) (by norm_num)
theorem B2263349 : Blo 1506950 2263349 := bbase (se 5 (by rfl) ⟨106094, by rfl⟩ : syracuseStep 2263349 = 212189) (by norm_num)
theorem B2263373 : Blo 1506950 2263373 := bbase (se 3 (by rfl) ⟨424382, by rfl⟩ : syracuseStep 2263373 = 848765) (by norm_num)
theorem B3221861 : Blo 1506950 3221861 := bbase (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) (by norm_num)
theorem B2263397 : Blo 1506950 2263397 := bbase (se 4 (by rfl) ⟨212193, by rfl⟩ : syracuseStep 2263397 = 424387) (by norm_num)
theorem B14494069 : Blo 1506950 14494069 := bbase (se 5 (by rfl) ⟨679409, by rfl⟩ : syracuseStep 14494069 = 1358819) (by norm_num)
theorem B2902397 : Blo 1506950 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B3393917 : Blo 1506950 3393917 := bbase (se 3 (by rfl) ⟨636359, by rfl⟩ : syracuseStep 3393917 = 1272719) (by norm_num)
theorem B2263421 : Blo 1506950 2263421 := bbase (se 3 (by rfl) ⟨424391, by rfl⟩ : syracuseStep 2263421 = 848783) (by norm_num)
theorem B2861477 : Blo 1506950 2861477 := bbase (se 4 (by rfl) ⟨268263, by rfl⟩ : syracuseStep 2861477 = 536527) (by norm_num)
theorem B3393989 : Blo 1506950 3393989 := bbase (se 4 (by rfl) ⟨318186, by rfl⟩ : syracuseStep 3393989 = 636373) (by norm_num)
theorem B2615765 : Blo 1506950 2615765 := bbase (se 7 (by rfl) ⟨30653, by rfl⟩ : syracuseStep 2615765 = 61307) (by norm_num)
theorem B3394061 : Blo 1506950 3394061 := bbase (se 3 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 3394061 = 1272773) (by norm_num)
theorem B5089877 : Blo 1506950 5089877 := bbase (se 8 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 5089877 = 59647) (by norm_num)
theorem B3394133 : Blo 1506950 3394133 := bbase (se 8 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 3394133 = 39775) (by norm_num)
theorem B3222101 : Blo 1506950 3222101 := bbase (se 8 (by rfl) ⟨18879, by rfl⟩ : syracuseStep 3222101 = 37759) (by norm_num)
theorem B6441605 : Blo 1506950 6441605 := bbase (se 4 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 6441605 = 1207801) (by norm_num)
theorem B3394205 : Blo 1506950 3394205 := bbase (se 3 (by rfl) ⟨636413, by rfl⟩ : syracuseStep 3394205 = 1272827) (by norm_num)
theorem B3058381 : Blo 1506950 3058381 := bbase (se 3 (by rfl) ⟨573446, by rfl⟩ : syracuseStep 3058381 = 1146893) (by norm_num)
theorem B3394277 : Blo 1506950 3394277 := bbase (se 4 (by rfl) ⟨318213, by rfl⟩ : syracuseStep 3394277 = 636427) (by norm_num)
theorem B8702741 : Blo 1506950 8702741 := bbase (se 6 (by rfl) ⟨203970, by rfl⟩ : syracuseStep 8702741 = 407941) (by norm_num)
theorem B25758485 : Blo 1506950 25758485 := bbase (se 6 (by rfl) ⟨603714, by rfl⟩ : syracuseStep 25758485 = 1207429) (by norm_num)
theorem B3394349 : Blo 1506950 3394349 := bbase (se 3 (by rfl) ⟨636440, by rfl⟩ : syracuseStep 3394349 = 1272881) (by norm_num)
theorem B7637813 : Blo 1506950 7637813 := bbase (se 5 (by rfl) ⟨358022, by rfl⟩ : syracuseStep 7637813 = 716045) (by norm_num)
theorem B3623741 : Blo 1506950 3623741 := bbase (se 3 (by rfl) ⟨679451, by rfl⟩ : syracuseStep 3623741 = 1358903) (by norm_num)
theorem B3869525 : Blo 1506950 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B3394421 : Blo 1506950 3394421 := bbase (se 5 (by rfl) ⟨159113, by rfl⟩ : syracuseStep 3394421 = 318227) (by norm_num)
theorem B8588213 : Blo 1506950 8588213 := bbase (se 5 (by rfl) ⟨402572, by rfl⟩ : syracuseStep 8588213 = 805145) (by norm_num)
theorem B3394493 : Blo 1506950 3394493 := bbase (se 3 (by rfl) ⟨636467, by rfl⟩ : syracuseStep 3394493 = 1272935) (by norm_num)
theorem B5090309 : Blo 1506950 5090309 := bbase (se 4 (by rfl) ⟨477216, by rfl⟩ : syracuseStep 5090309 = 954433) (by norm_num)
theorem B3394565 : Blo 1506950 3394565 := bbase (se 4 (by rfl) ⟨318240, by rfl⟩ : syracuseStep 3394565 = 636481) (by norm_num)
theorem B3394637 : Blo 1506950 3394637 := bbase (se 3 (by rfl) ⟨636494, by rfl⟩ : syracuseStep 3394637 = 1272989) (by norm_num)
theorem B3222605 : Blo 1506950 3222605 := bbase (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) (by norm_num)
theorem B3222613 : Blo 1506950 3222613 := bbase (se 8 (by rfl) ⟨18882, by rfl⟩ : syracuseStep 3222613 = 37765) (by norm_num)
theorem B3058805 : Blo 1506950 3058805 := bbase (se 5 (by rfl) ⟨143381, by rfl⟩ : syracuseStep 3058805 = 286763) (by norm_num)
theorem B2862229 : Blo 1506950 2862229 := bbase (se 6 (by rfl) ⟨67083, by rfl⟩ : syracuseStep 2862229 = 134167) (by norm_num)
theorem B3394709 : Blo 1506950 3394709 := bbase (se 6 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 3394709 = 159127) (by norm_num)
theorem B4295861 : Blo 1506950 4295861 := bbase (se 5 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 4295861 = 402737) (by norm_num)
theorem B4828373 : Blo 1506950 4828373 := bbase (se 7 (by rfl) ⟨56582, by rfl⟩ : syracuseStep 4828373 = 113165) (by norm_num)
theorem B7630037 : Blo 1506950 7630037 := bbase (se 7 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 7630037 = 178829) (by norm_num)
theorem B3394781 : Blo 1506950 3394781 := bbase (se 3 (by rfl) ⟨636521, by rfl⟩ : syracuseStep 3394781 = 1273043) (by norm_num)
theorem B17173781 : Blo 1506950 17173781 := bbase (se 6 (by rfl) ⟨402510, by rfl⟩ : syracuseStep 17173781 = 805021) (by norm_num)
theorem B2862373 : Blo 1506950 2862373 := bbase (se 4 (by rfl) ⟨268347, by rfl⟩ : syracuseStep 2862373 = 536695) (by norm_num)
theorem B3394853 : Blo 1506950 3394853 := bbase (se 4 (by rfl) ⟨318267, by rfl⟩ : syracuseStep 3394853 = 636535) (by norm_num)
theorem B2649437 : Blo 1506950 2649437 := bbase (se 3 (by rfl) ⟨496769, by rfl⟩ : syracuseStep 2649437 = 993539) (by norm_num)
theorem B3394925 : Blo 1506950 3394925 := bbase (se 3 (by rfl) ⟨636548, by rfl⟩ : syracuseStep 3394925 = 1273097) (by norm_num)
theorem B2542981 : Blo 1506950 2542981 := bbase (se 4 (by rfl) ⟨238404, by rfl⟩ : syracuseStep 2542981 = 476809) (by norm_num)
theorem B5090741 : Blo 1506950 5090741 := bbase (se 5 (by rfl) ⟨238628, by rfl⟩ : syracuseStep 5090741 = 477257) (by norm_num)
theorem B3394997 : Blo 1506950 3394997 := bbase (se 5 (by rfl) ⟨159140, by rfl⟩ : syracuseStep 3394997 = 318281) (by norm_num)
theorem B2862533 : Blo 1506950 2862533 := bbase (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) (by norm_num)
theorem B2543069 : Blo 1506950 2543069 := bbase (se 3 (by rfl) ⟨476825, by rfl⟩ : syracuseStep 2543069 = 953651) (by norm_num)
theorem B3395069 : Blo 1506950 3395069 := bbase (se 3 (by rfl) ⟨636575, by rfl⟩ : syracuseStep 3395069 = 1273151) (by norm_num)
theorem B1609265 : Blo 1506950 1609265 := bbase (se 2 (by rfl) ⟨603474, by rfl⟩ : syracuseStep 1609265 = 1206949) (by norm_num)
theorem B3624509 : Blo 1506950 3624509 := bbase (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) (by norm_num)
theorem B3624517 : Blo 1506950 3624517 := bbase (se 4 (by rfl) ⟨339798, by rfl⟩ : syracuseStep 3624517 = 679597) (by norm_num)
theorem B2862677 : Blo 1506950 2862677 := bbase (se 8 (by rfl) ⟨16773, by rfl⟩ : syracuseStep 2862677 = 33547) (by norm_num)
theorem B2543197 : Blo 1506950 2543197 := bbase (se 3 (by rfl) ⟨476849, by rfl⟩ : syracuseStep 2543197 = 953699) (by norm_num)
theorem B1609393 : Blo 1506950 1609393 := bbase (se 2 (by rfl) ⟨603522, by rfl⟩ : syracuseStep 1609393 = 1207045) (by norm_num)
theorem B2543285 : Blo 1506950 2543285 := bbase (se 5 (by rfl) ⟨119216, by rfl⟩ : syracuseStep 2543285 = 238433) (by norm_num)
theorem B2543413 : Blo 1506950 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B5091173 : Blo 1506950 5091173 := bbase (se 4 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 5091173 = 954595) (by norm_num)
theorem B2862965 : Blo 1506950 2862965 := bbase (se 5 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 2862965 = 268403) (by norm_num)
theorem B2543501 : Blo 1506950 2543501 := bbase (se 3 (by rfl) ⟨476906, by rfl⟩ : syracuseStep 2543501 = 953813) (by norm_num)
theorem B2543629 : Blo 1506950 2543629 := bbase (se 3 (by rfl) ⟨476930, by rfl⟩ : syracuseStep 2543629 = 953861) (by norm_num)
theorem B2863117 : Blo 1506950 2863117 := bbase (se 3 (by rfl) ⟨536834, by rfl⟩ : syracuseStep 2863117 = 1073669) (by norm_num)
theorem B2543717 : Blo 1506950 2543717 := bbase (se 4 (by rfl) ⟨238473, by rfl⟩ : syracuseStep 2543717 = 476947) (by norm_num)
theorem B1609837 : Blo 1506950 1609837 := bbase (se 3 (by rfl) ⟨301844, by rfl⟩ : syracuseStep 1609837 = 603689) (by norm_num)
theorem B12390517 : Blo 1506950 12390517 := bbase (se 5 (by rfl) ⟨580805, by rfl⟩ : syracuseStep 12390517 = 1161611) (by norm_num)
theorem B7246037 : Blo 1506950 7246037 := bbase (se 7 (by rfl) ⟨84914, by rfl⟩ : syracuseStep 7246037 = 169829) (by norm_num)
theorem B2543845 : Blo 1506950 2543845 := bbase (se 4 (by rfl) ⟨238485, by rfl⟩ : syracuseStep 2543845 = 476971) (by norm_num)
theorem B1609957 : Blo 1506950 1609957 := bbase (se 4 (by rfl) ⟨150933, by rfl⟩ : syracuseStep 1609957 = 301867) (by norm_num)
theorem B4075765 : Blo 1506950 4075765 := bbase (se 5 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 4075765 = 382103) (by norm_num)
theorem B5091605 : Blo 1506950 5091605 := bbase (se 6 (by rfl) ⟨119334, by rfl⟩ : syracuseStep 5091605 = 238669) (by norm_num)
theorem B2543933 : Blo 1506950 2543933 := bbase (se 3 (by rfl) ⟨476987, by rfl⟩ : syracuseStep 2543933 = 953975) (by norm_num)
theorem B2863421 : Blo 1506950 2863421 := bbase (se 3 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 2863421 = 1073783) (by norm_num)
theorem B3625325 : Blo 1506950 3625325 := bbase (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) (by norm_num)
theorem B6443381 : Blo 1506950 6443381 := bbase (se 5 (by rfl) ⟨302033, by rfl⟩ : syracuseStep 6443381 = 604067) (by norm_num)
theorem B3723661 : Blo 1506950 3723661 := bbase (se 3 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 3723661 = 1396373) (by norm_num)
theorem B2544061 : Blo 1506950 2544061 := bbase (se 3 (by rfl) ⟨477011, by rfl⟩ : syracuseStep 2544061 = 954023) (by norm_num)
theorem B1610209 : Blo 1506950 1610209 := bbase (se 2 (by rfl) ⟨603828, by rfl⟩ : syracuseStep 1610209 = 1207657) (by norm_num)
theorem B7631333 : Blo 1506950 7631333 := bbase (se 4 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 7631333 = 1430875) (by norm_num)
theorem B1610213 : Blo 1506950 1610213 := bbase (se 4 (by rfl) ⟨150957, by rfl⟩ : syracuseStep 1610213 = 301915) (by norm_num)
theorem B24441365 : Blo 1506950 24441365 := bbase (se 6 (by rfl) ⟨572844, by rfl⟩ : syracuseStep 24441365 = 1145689) (by norm_num)
theorem B2544149 : Blo 1506950 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B6443621 : Blo 1506950 6443621 := bbase (se 4 (by rfl) ⟨604089, by rfl⟩ : syracuseStep 6443621 = 1208179) (by norm_num)
theorem B5722757 : Blo 1506950 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B11604629 : Blo 1506950 11604629 := bbase (se 6 (by rfl) ⟨271983, by rfl⟩ : syracuseStep 11604629 = 543967) (by norm_num)
theorem B2544277 : Blo 1506950 2544277 := bbase (se 6 (by rfl) ⟨59631, by rfl⟩ : syracuseStep 2544277 = 119263) (by norm_num)
theorem B5436085 : Blo 1506950 5436085 := bbase (se 5 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 5436085 = 509633) (by norm_num)
theorem B5092037 : Blo 1506950 5092037 := bbase (se 4 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 5092037 = 954757) (by norm_num)
theorem B7443173 : Blo 1506950 7443173 := bbase (se 4 (by rfl) ⟨697797, by rfl⟩ : syracuseStep 7443173 = 1395595) (by norm_num)
theorem B2544365 : Blo 1506950 2544365 := bbase (se 3 (by rfl) ⟨477068, by rfl⟩ : syracuseStep 2544365 = 954137) (by norm_num)
theorem B2716421 : Blo 1506950 2716421 := bbase (se 4 (by rfl) ⟨254664, by rfl⟩ : syracuseStep 2716421 = 509329) (by norm_num)
theorem B1528669 : Blo 1506950 1528669 := bbase (se 3 (by rfl) ⟨286625, by rfl⟩ : syracuseStep 1528669 = 573251) (by norm_num)
theorem B3437413 : Blo 1506950 3437413 := bbase (se 4 (by rfl) ⟨322257, by rfl⟩ : syracuseStep 3437413 = 644515) (by norm_num)
theorem B2544493 : Blo 1506950 2544493 := bbase (se 3 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 2544493 = 954185) (by norm_num)
theorem B5723045 : Blo 1506950 5723045 := bbase (se 4 (by rfl) ⟨536535, by rfl⟩ : syracuseStep 5723045 = 1073071) (by norm_num)
theorem B2544581 : Blo 1506950 2544581 := bbase (se 4 (by rfl) ⟨238554, by rfl⟩ : syracuseStep 2544581 = 477109) (by norm_num)
theorem B4830229 : Blo 1506950 4830229 := bbase (se 6 (by rfl) ⟨113208, by rfl⟩ : syracuseStep 4830229 = 226417) (by norm_num)
theorem B1610777 : Blo 1506950 1610777 := bbase (se 2 (by rfl) ⟨604041, by rfl⟩ : syracuseStep 1610777 = 1208083) (by norm_num)
theorem B2864173 : Blo 1506950 2864173 := bbase (se 3 (by rfl) ⟨537032, by rfl⟩ : syracuseStep 2864173 = 1074065) (by norm_num)
theorem B2544709 : Blo 1506950 2544709 := bbase (se 4 (by rfl) ⟨238566, by rfl⟩ : syracuseStep 2544709 = 477133) (by norm_num)
theorem B5436533 : Blo 1506950 5436533 := bbase (se 5 (by rfl) ⟨254837, by rfl⟩ : syracuseStep 5436533 = 509675) (by norm_num)
theorem B5092469 : Blo 1506950 5092469 := bbase (se 5 (by rfl) ⟨238709, by rfl⟩ : syracuseStep 5092469 = 477419) (by norm_num)
theorem B2544797 : Blo 1506950 2544797 := bbase (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) (by norm_num)
theorem B3814573 : Blo 1506950 3814573 := bbase (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) (by norm_num)
theorem B2864317 : Blo 1506950 2864317 := bbase (se 3 (by rfl) ⟨537059, by rfl⟩ : syracuseStep 2864317 = 1074119) (by norm_num)
theorem B1610965 : Blo 1506950 1610965 := bbase (se 7 (by rfl) ⟨18878, by rfl⟩ : syracuseStep 1610965 = 37757) (by norm_num)
theorem B1766677 : Blo 1506950 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B3814685 : Blo 1506950 3814685 := bbase (se 3 (by rfl) ⟨715253, by rfl⟩ : syracuseStep 3814685 = 1430507) (by norm_num)
theorem B2544925 : Blo 1506950 2544925 := bbase (se 3 (by rfl) ⟨477173, by rfl⟩ : syracuseStep 2544925 = 954347) (by norm_num)
theorem B2864477 : Blo 1506950 2864477 := bbase (se 3 (by rfl) ⟨537089, by rfl⟩ : syracuseStep 2864477 = 1074179) (by norm_num)
theorem B2577773 : Blo 1506950 2577773 := bbase (se 3 (by rfl) ⟨483332, by rfl⟩ : syracuseStep 2577773 = 966665) (by norm_num)
theorem B2545013 : Blo 1506950 2545013 := bbase (se 5 (by rfl) ⟨119297, by rfl⟩ : syracuseStep 2545013 = 238595) (by norm_num)
theorem B2176381 : Blo 1506950 2176381 := bbase (se 3 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 2176381 = 816143) (by norm_num)
theorem B3814877 : Blo 1506950 3814877 := bbase (se 3 (by rfl) ⟨715289, by rfl⟩ : syracuseStep 3814877 = 1430579) (by norm_num)
theorem B2864621 : Blo 1506950 2864621 := bbase (se 3 (by rfl) ⟨537116, by rfl⟩ : syracuseStep 2864621 = 1074233) (by norm_num)
theorem B2545141 : Blo 1506950 2545141 := bbase (se 5 (by rfl) ⟨119303, by rfl⟩ : syracuseStep 2545141 = 238607) (by norm_num)
theorem B1529353 : Blo 1506950 1529353 := bbase (se 2 (by rfl) ⟨573507, by rfl⟩ : syracuseStep 1529353 = 1147015) (by norm_num)
theorem B2414141 : Blo 1506950 2414141 := bbase (se 3 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 2414141 = 905303) (by norm_num)
theorem B2545229 : Blo 1506950 2545229 := bbase (se 3 (by rfl) ⟨477230, by rfl⟩ : syracuseStep 2545229 = 954461) (by norm_num)
theorem B41293397 : Blo 1506950 41293397 := bbase (se 8 (by rfl) ⟨241953, by rfl⟩ : syracuseStep 41293397 = 483907) (by norm_num)
theorem B2545357 : Blo 1506950 2545357 := bbase (se 3 (by rfl) ⟨477254, by rfl⟩ : syracuseStep 2545357 = 954509) (by norm_num)
theorem B7632629 : Blo 1506950 7632629 := bbase (se 5 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 7632629 = 715559) (by norm_num)
theorem B2545445 : Blo 1506950 2545445 := bbase (se 4 (by rfl) ⟨238635, by rfl⟩ : syracuseStep 2545445 = 477271) (by norm_num)
theorem B3815221 : Blo 1506950 3815221 := bbase (se 5 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 3815221 = 357677) (by norm_num)
theorem B11458421 : Blo 1506950 11458421 := bbase (se 5 (by rfl) ⟨537113, by rfl⟩ : syracuseStep 11458421 = 1074227) (by norm_num)
theorem B3815333 : Blo 1506950 3815333 := bbase (se 4 (by rfl) ⟨357687, by rfl⟩ : syracuseStep 3815333 = 715375) (by norm_num)
theorem B2545573 : Blo 1506950 2545573 := bbase (se 4 (by rfl) ⟨238647, by rfl⟩ : syracuseStep 2545573 = 477295) (by norm_num)
theorem B3438509 : Blo 1506950 3438509 := bbase (se 3 (by rfl) ⟨644720, by rfl⟩ : syracuseStep 3438509 = 1289441) (by norm_num)
theorem B8148917 : Blo 1506950 8148917 := bbase (se 5 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 8148917 = 763961) (by norm_num)
theorem B15480757 : Blo 1506950 15480757 := bbase (se 5 (by rfl) ⟨725660, by rfl⟩ : syracuseStep 15480757 = 1451321) (by norm_num)
theorem B12228565 : Blo 1506950 12228565 := bbase (se 7 (by rfl) ⟨143303, by rfl⟩ : syracuseStep 12228565 = 286607) (by norm_num)
theorem B2545661 : Blo 1506950 2545661 := bbase (se 3 (by rfl) ⟨477311, by rfl⟩ : syracuseStep 2545661 = 954623) (by norm_num)
theorem B2414653 : Blo 1506950 2414653 := bbase (se 3 (by rfl) ⟨452747, by rfl⟩ : syracuseStep 2414653 = 905495) (by norm_num)
theorem B5724229 : Blo 1506950 5724229 := bbase (se 4 (by rfl) ⟨536646, by rfl⟩ : syracuseStep 5724229 = 1073293) (by norm_num)
theorem B3815525 : Blo 1506950 3815525 := bbase (se 4 (by rfl) ⟨357705, by rfl⟩ : syracuseStep 3815525 = 715411) (by norm_num)
theorem B2545789 : Blo 1506950 2545789 := bbase (se 3 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 2545789 = 954671) (by norm_num)
theorem B2717869 : Blo 1506950 2717869 := bbase (se 3 (by rfl) ⟨509600, by rfl⟩ : syracuseStep 2717869 = 1019201) (by norm_num)
theorem B2545877 : Blo 1506950 2545877 := bbase (se 7 (by rfl) ⟨29834, by rfl⟩ : syracuseStep 2545877 = 59669) (by norm_num)
theorem B11450645 : Blo 1506950 11450645 := bbase (se 6 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 11450645 = 536749) (by norm_num)
theorem B2546005 : Blo 1506950 2546005 := bbase (se 10 (by rfl) ⟨3729, by rfl⟩ : syracuseStep 2546005 = 7459) (by norm_num)
theorem B1743193 : Blo 1506950 1743193 := bbase (se 2 (by rfl) ⟨653697, by rfl⟩ : syracuseStep 1743193 = 1307395) (by norm_num)
theorem B4831589 : Blo 1506950 4831589 := bbase (se 4 (by rfl) ⟨452961, by rfl⟩ : syracuseStep 4831589 = 905923) (by norm_num)
theorem B5724533 : Blo 1506950 5724533 := bbase (se 5 (by rfl) ⟨268337, by rfl⟩ : syracuseStep 5724533 = 536675) (by norm_num)
theorem B2546093 : Blo 1506950 2546093 := bbase (se 3 (by rfl) ⟨477392, by rfl⟩ : syracuseStep 2546093 = 954785) (by norm_num)
theorem B3815869 : Blo 1506950 3815869 := bbase (se 3 (by rfl) ⟨715475, by rfl⟩ : syracuseStep 3815869 = 1430951) (by norm_num)
theorem B6437333 : Blo 1506950 6437333 := bbase (se 7 (by rfl) ⟨75437, by rfl⟩ : syracuseStep 6437333 = 150875) (by norm_num)
theorem B2292181 : Blo 1506950 2292181 := bbase (se 7 (by rfl) ⟨26861, by rfl⟩ : syracuseStep 2292181 = 53723) (by norm_num)
theorem B20691413 : Blo 1506950 20691413 := bbase (se 7 (by rfl) ⟨242477, by rfl⟩ : syracuseStep 20691413 = 484955) (by norm_num)
theorem B2415109 : Blo 1506950 2415109 := bbase (se 4 (by rfl) ⟨226416, by rfl⟩ : syracuseStep 2415109 = 452833) (by norm_num)
theorem B3815981 : Blo 1506950 3815981 := bbase (se 3 (by rfl) ⟨715496, by rfl⟩ : syracuseStep 3815981 = 1430993) (by norm_num)
theorem B2546221 : Blo 1506950 2546221 := bbase (se 3 (by rfl) ⟨477416, by rfl⟩ : syracuseStep 2546221 = 954833) (by norm_num)
theorem B1907317 : Blo 1506950 1907317 := bbase (se 5 (by rfl) ⟨89405, by rfl⟩ : syracuseStep 1907317 = 178811) (by norm_num)
theorem B2546309 : Blo 1506950 2546309 := bbase (se 4 (by rfl) ⟨238716, by rfl⟩ : syracuseStep 2546309 = 477433) (by norm_num)
theorem B9665173 : Blo 1506950 9665173 := bbase (se 6 (by rfl) ⟨226527, by rfl⟩ : syracuseStep 9665173 = 453055) (by norm_num)
theorem B3816173 : Blo 1506950 3816173 := bbase (se 3 (by rfl) ⟨715532, by rfl⟩ : syracuseStep 3816173 = 1431065) (by norm_num)
theorem B1907489 : Blo 1506950 1907489 := bbase (se 2 (by rfl) ⟨715308, by rfl⟩ : syracuseStep 1907489 = 1430617) (by norm_num)
theorem B5085989 : Blo 1506950 5085989 := bbase (se 4 (by rfl) ⟨476811, by rfl⟩ : syracuseStep 5085989 = 953623) (by norm_num)
theorem B2480965 : Blo 1506950 2480965 := bbase (se 4 (by rfl) ⟨232590, by rfl⟩ : syracuseStep 2480965 = 465181) (by norm_num)
theorem B2038613 : Blo 1506950 2038613 := bbase (se 9 (by rfl) ⟨5972, by rfl⟩ : syracuseStep 2038613 = 11945) (by norm_num)
theorem B1907545 : Blo 1506950 1907545 := bbase (se 2 (by rfl) ⟨715329, by rfl⟩ : syracuseStep 1907545 = 1430659) (by norm_num)
theorem B1907641 : Blo 1506950 1907641 := bbase (se 2 (by rfl) ⟨715365, by rfl⟩ : syracuseStep 1907641 = 1430731) (by norm_num)
theorem B2718677 : Blo 1506950 2718677 := bbase (se 7 (by rfl) ⟨31859, by rfl⟩ : syracuseStep 2718677 = 63719) (by norm_num)
theorem B7633925 : Blo 1506950 7633925 := bbase (se 4 (by rfl) ⟨715680, by rfl⟩ : syracuseStep 7633925 = 1431361) (by norm_num)
theorem B2718749 : Blo 1506950 2718749 := bbase (se 3 (by rfl) ⟨509765, by rfl⟩ : syracuseStep 2718749 = 1019531) (by norm_num)
theorem B9428021 : Blo 1506950 9428021 := bbase (se 5 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 9428021 = 883877) (by norm_num)
theorem B3816517 : Blo 1506950 3816517 := bbase (se 4 (by rfl) ⟨357798, by rfl⟩ : syracuseStep 3816517 = 715597) (by norm_num)
theorem B1907813 : Blo 1506950 1907813 := bbase (se 4 (by rfl) ⟨178857, by rfl⟩ : syracuseStep 1907813 = 357715) (by norm_num)
theorem B1907869 : Blo 1506950 1907869 := bbase (se 3 (by rfl) ⟨357725, by rfl⟩ : syracuseStep 1907869 = 715451) (by norm_num)
theorem B2415781 : Blo 1506950 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B3816629 : Blo 1506950 3816629 := bbase (se 5 (by rfl) ⟨178904, by rfl⟩ : syracuseStep 3816629 = 357809) (by norm_num)
theorem B3390677 : Blo 1506950 3390677 := bbase (se 7 (by rfl) ⟨39734, by rfl⟩ : syracuseStep 3390677 = 79469) (by norm_num)
theorem B5086421 : Blo 1506950 5086421 := bbase (se 7 (by rfl) ⟨59606, by rfl⟩ : syracuseStep 5086421 = 119213) (by norm_num)
theorem B4291829 : Blo 1506950 4291829 := bbase (se 5 (by rfl) ⟨201179, by rfl⟩ : syracuseStep 4291829 = 402359) (by norm_num)
theorem B2718965 : Blo 1506950 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B1907965 : Blo 1506950 1907965 := bbase (se 3 (by rfl) ⟨357743, by rfl⟩ : syracuseStep 1907965 = 715487) (by norm_num)
theorem B3390749 : Blo 1506950 3390749 := bbase (se 3 (by rfl) ⟨635765, by rfl⟩ : syracuseStep 3390749 = 1271531) (by norm_num)
theorem B2235701 : Blo 1506950 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B3439949 : Blo 1506950 3439949 := bbase (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) (by norm_num)
theorem B3390821 : Blo 1506950 3390821 := bbase (se 4 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 3390821 = 635779) (by norm_num)
theorem B3816821 : Blo 1506950 3816821 := bbase (se 5 (by rfl) ⟨178913, by rfl⟩ : syracuseStep 3816821 = 357827) (by norm_num)
theorem B1908137 : Blo 1506950 1908137 := bbase (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) (by norm_num)
theorem B3390893 : Blo 1506950 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B2260445 : Blo 1506950 2260445 := bbase (se 3 (by rfl) ⟨423833, by rfl⟩ : syracuseStep 2260445 = 847667) (by norm_num)
theorem B1908193 : Blo 1506950 1908193 := bbase (se 2 (by rfl) ⟨715572, by rfl⟩ : syracuseStep 1908193 = 1431145) (by norm_num)
theorem B2260469 : Blo 1506950 2260469 := bbase (se 5 (by rfl) ⟨105959, by rfl⟩ : syracuseStep 2260469 = 211919) (by norm_num)
theorem B3390965 : Blo 1506950 3390965 := bbase (se 5 (by rfl) ⟨158951, by rfl⟩ : syracuseStep 3390965 = 317903) (by norm_num)
theorem B2260493 : Blo 1506950 2260493 := bbase (se 3 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 2260493 = 847685) (by norm_num)
theorem B3218957 : Blo 1506950 3218957 := bbase (se 3 (by rfl) ⟨603554, by rfl⟩ : syracuseStep 3218957 = 1207109) (by norm_num)
theorem B2260517 : Blo 1506950 2260517 := bbase (se 4 (by rfl) ⟨211923, by rfl⟩ : syracuseStep 2260517 = 423847) (by norm_num)
theorem B2260541 : Blo 1506950 2260541 := bbase (se 3 (by rfl) ⟨423851, by rfl⟩ : syracuseStep 2260541 = 847703) (by norm_num)
theorem B3391037 : Blo 1506950 3391037 := bbase (se 3 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 3391037 = 1271639) (by norm_num)
theorem B1908289 : Blo 1506950 1908289 := bbase (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) (by norm_num)
theorem B5226053 : Blo 1506950 5226053 := bbase (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) (by norm_num)
theorem B2416205 : Blo 1506950 2416205 := bbase (se 3 (by rfl) ⟨453038, by rfl⟩ : syracuseStep 2416205 = 906077) (by norm_num)
theorem B2260565 : Blo 1506950 2260565 := bbase (se 8 (by rfl) ⟨13245, by rfl⟩ : syracuseStep 2260565 = 26491) (by norm_num)
theorem B1695325 : Blo 1506950 1695325 := bbase (se 3 (by rfl) ⟨317873, by rfl⟩ : syracuseStep 1695325 = 635747) (by norm_num)
theorem B2260589 : Blo 1506950 2260589 := bbase (se 3 (by rfl) ⟨423860, by rfl⟩ : syracuseStep 2260589 = 847721) (by norm_num)
theorem B1695361 : Blo 1506950 1695361 := bbase (se 2 (by rfl) ⟨635760, by rfl⟩ : syracuseStep 1695361 = 1271521) (by norm_num)
theorem B2260613 : Blo 1506950 2260613 := bbase (se 4 (by rfl) ⟨211932, by rfl⟩ : syracuseStep 2260613 = 423865) (by norm_num)
theorem B3391109 : Blo 1506950 3391109 := bbase (se 4 (by rfl) ⟨317916, by rfl⟩ : syracuseStep 3391109 = 635833) (by norm_num)
theorem B5086853 : Blo 1506950 5086853 := bbase (se 4 (by rfl) ⟨476892, by rfl⟩ : syracuseStep 5086853 = 953785) (by norm_num)
theorem B3219077 : Blo 1506950 3219077 := bbase (se 4 (by rfl) ⟨301788, by rfl⟩ : syracuseStep 3219077 = 603577) (by norm_num)
theorem B2293397 : Blo 1506950 2293397 := bbase (se 6 (by rfl) ⟨53751, by rfl⟩ : syracuseStep 2293397 = 107503) (by norm_num)
theorem B2260637 : Blo 1506950 2260637 := bbase (se 3 (by rfl) ⟨423869, by rfl⟩ : syracuseStep 2260637 = 847739) (by norm_num)
theorem B1695397 : Blo 1506950 1695397 := bbase (se 4 (by rfl) ⟨158943, by rfl⟩ : syracuseStep 1695397 = 317887) (by norm_num)
theorem B4292261 : Blo 1506950 4292261 := bbase (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) (by norm_num)
theorem B2260661 : Blo 1506950 2260661 := bbase (se 5 (by rfl) ⟨105968, by rfl⟩ : syracuseStep 2260661 = 211937) (by norm_num)
theorem B1695433 : Blo 1506950 1695433 := bbase (se 2 (by rfl) ⟨635787, by rfl⟩ : syracuseStep 1695433 = 1271575) (by norm_num)
theorem B2260685 : Blo 1506950 2260685 := bbase (se 3 (by rfl) ⟨423878, by rfl⟩ : syracuseStep 2260685 = 847757) (by norm_num)
theorem B3391181 : Blo 1506950 3391181 := bbase (se 3 (by rfl) ⟨635846, by rfl⟩ : syracuseStep 3391181 = 1271693) (by norm_num)
theorem B3817165 : Blo 1506950 3817165 := bbase (se 3 (by rfl) ⟨715718, by rfl⟩ : syracuseStep 3817165 = 1431437) (by norm_num)
theorem B2260709 : Blo 1506950 2260709 := bbase (se 4 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 2260709 = 423883) (by norm_num)
theorem B1695469 : Blo 1506950 1695469 := bbase (se 3 (by rfl) ⟨317900, by rfl⟩ : syracuseStep 1695469 = 635801) (by norm_num)
theorem B1908461 : Blo 1506950 1908461 := bbase (se 3 (by rfl) ⟨357836, by rfl⟩ : syracuseStep 1908461 = 715673) (by norm_num)
theorem B2260733 : Blo 1506950 2260733 := bbase (se 3 (by rfl) ⟨423887, by rfl⟩ : syracuseStep 2260733 = 847775) (by norm_num)
theorem B1695505 : Blo 1506950 1695505 := bbase (se 2 (by rfl) ⟨635814, by rfl⟩ : syracuseStep 1695505 = 1271629) (by norm_num)
theorem B2260757 : Blo 1506950 2260757 := bbase (se 6 (by rfl) ⟨52986, by rfl⟩ : syracuseStep 2260757 = 105973) (by norm_num)
theorem B3391253 : Blo 1506950 3391253 := bbase (se 6 (by rfl) ⟨79482, by rfl⟩ : syracuseStep 3391253 = 158965) (by norm_num)
theorem B1908517 : Blo 1506950 1908517 := bbase (se 4 (by rfl) ⟨178923, by rfl⟩ : syracuseStep 1908517 = 357847) (by norm_num)
theorem B2260781 : Blo 1506950 2260781 := bbase (se 3 (by rfl) ⟨423896, by rfl⟩ : syracuseStep 2260781 = 847793) (by norm_num)
theorem B1695541 : Blo 1506950 1695541 := bbase (se 5 (by rfl) ⟨79478, by rfl⟩ : syracuseStep 1695541 = 158957) (by norm_num)
theorem B3817277 : Blo 1506950 3817277 := bbase (se 3 (by rfl) ⟨715739, by rfl⟩ : syracuseStep 3817277 = 1431479) (by norm_num)
theorem B2260805 : Blo 1506950 2260805 := bbase (se 4 (by rfl) ⟨211950, by rfl⟩ : syracuseStep 2260805 = 423901) (by norm_num)
theorem B55754581 : Blo 1506950 55754581 := bbase (se 9 (by rfl) ⟨163343, by rfl⟩ : syracuseStep 55754581 = 326687) (by norm_num)
theorem B12910421 : Blo 1506950 12910421 := bbase (se 9 (by rfl) ⟨37823, by rfl⟩ : syracuseStep 12910421 = 75647) (by norm_num)
theorem B1695577 : Blo 1506950 1695577 := bbase (se 2 (by rfl) ⟨635841, by rfl⟩ : syracuseStep 1695577 = 1271683) (by norm_num)
theorem B2260829 : Blo 1506950 2260829 := bbase (se 3 (by rfl) ⟨423905, by rfl⟩ : syracuseStep 2260829 = 847811) (by norm_num)
theorem B3391325 : Blo 1506950 3391325 := bbase (se 3 (by rfl) ⟨635873, by rfl⟩ : syracuseStep 3391325 = 1271747) (by norm_num)
theorem B2416493 : Blo 1506950 2416493 := bbase (se 3 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 2416493 = 906185) (by norm_num)
theorem B2260853 : Blo 1506950 2260853 := bbase (se 5 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 2260853 = 211955) (by norm_num)
theorem B1695613 : Blo 1506950 1695613 := bbase (se 3 (by rfl) ⟨317927, by rfl⟩ : syracuseStep 1695613 = 635855) (by norm_num)
theorem B1908613 : Blo 1506950 1908613 := bbase (se 4 (by rfl) ⟨178932, by rfl⟩ : syracuseStep 1908613 = 357865) (by norm_num)
theorem B2260877 : Blo 1506950 2260877 := bbase (se 3 (by rfl) ⟨423914, by rfl⟩ : syracuseStep 2260877 = 847829) (by norm_num)
theorem B1695649 : Blo 1506950 1695649 := bbase (se 2 (by rfl) ⟨635868, by rfl⟩ : syracuseStep 1695649 = 1271737) (by norm_num)
theorem B2260901 : Blo 1506950 2260901 := bbase (se 4 (by rfl) ⟨211959, by rfl⟩ : syracuseStep 2260901 = 423919) (by norm_num)
theorem B3391397 : Blo 1506950 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B7241653 : Blo 1506950 7241653 := bbase (se 5 (by rfl) ⟨339452, by rfl⟩ : syracuseStep 7241653 = 678905) (by norm_num)
theorem B2260925 : Blo 1506950 2260925 := bbase (se 3 (by rfl) ⟨423923, by rfl⟩ : syracuseStep 2260925 = 847847) (by norm_num)
theorem B1695685 : Blo 1506950 1695685 := bbase (se 4 (by rfl) ⟨158970, by rfl⟩ : syracuseStep 1695685 = 317941) (by norm_num)
theorem B2260949 : Blo 1506950 2260949 := bbase (se 7 (by rfl) ⟨26495, by rfl⟩ : syracuseStep 2260949 = 52991) (by norm_num)
theorem B1810409 : Blo 1506950 1810409 := bbase (se 2 (by rfl) ⟨678903, by rfl⟩ : syracuseStep 1810409 = 1357807) (by norm_num)
theorem B1695721 : Blo 1506950 1695721 := bbase (se 2 (by rfl) ⟨635895, by rfl⟩ : syracuseStep 1695721 = 1271791) (by norm_num)
theorem B2260973 : Blo 1506950 2260973 := bbase (se 3 (by rfl) ⟨423932, by rfl⟩ : syracuseStep 2260973 = 847865) (by norm_num)
theorem B3391469 : Blo 1506950 3391469 := bbase (se 3 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 3391469 = 1271801) (by norm_num)
theorem B3817469 : Blo 1506950 3817469 := bbase (se 3 (by rfl) ⟨715775, by rfl⟩ : syracuseStep 3817469 = 1431551) (by norm_num)
theorem B1507331 : Blo 1506950 1507331 := bstep (se 1 (by rfl) ⟨1130498, by rfl⟩ : syracuseStep 1507331 = 2260997) B2260997
theorem B4587523 : Blo 1506950 4587523 := bstep (se 1 (by rfl) ⟨3440642, by rfl⟩ : syracuseStep 4587523 = 6881285) B6881285
theorem B3391505 : Blo 1506950 3391505 := bstep (se 2 (by rfl) ⟨1271814, by rfl⟩ : syracuseStep 3391505 = 2543629) B2543629
theorem B2261009 : Blo 1506950 2261009 := bstep (se 2 (by rfl) ⟨847878, by rfl⟩ : syracuseStep 2261009 = 1695757) B1695757
theorem B1507347 : Blo 1506950 1507347 := bstep (se 1 (by rfl) ⟨1130510, by rfl⟩ : syracuseStep 1507347 = 2261021) B2261021
theorem B3817489 : Blo 1506950 3817489 := bstep (se 2 (by rfl) ⟨1431558, by rfl⟩ : syracuseStep 3817489 = 2863117) B2863117
theorem B3391523 : Blo 1506950 3391523 := bstep (se 1 (by rfl) ⟨2543642, by rfl⟩ : syracuseStep 3391523 = 5087285) B5087285
theorem B2261027 : Blo 1506950 2261027 := bstep (se 1 (by rfl) ⟨1695770, by rfl⟩ : syracuseStep 2261027 = 3391541) B3391541
theorem B1507363 : Blo 1506950 1507363 := bstep (se 1 (by rfl) ⟨1130522, by rfl⟩ : syracuseStep 1507363 = 2261045) B2261045
theorem B1507379 : Blo 1506950 1507379 := bstep (se 1 (by rfl) ⟨1130534, by rfl⟩ : syracuseStep 1507379 = 2261069) B2261069
theorem B2261057 : Blo 1506950 2261057 := bstep (se 2 (by rfl) ⟨847896, by rfl⟩ : syracuseStep 2261057 = 1695793) B1695793
theorem B1695811 : Blo 1506950 1695811 := bstep (se 1 (by rfl) ⟨1271858, by rfl⟩ : syracuseStep 1695811 = 2543717) B2543717
theorem B1507395 : Blo 1506950 1507395 := bstep (se 1 (by rfl) ⟨1130546, by rfl⟩ : syracuseStep 1507395 = 2261093) B2261093
theorem B2261075 : Blo 1506950 2261075 := bstep (se 1 (by rfl) ⟨1695806, by rfl⟩ : syracuseStep 2261075 = 3391613) B3391613
theorem B1507411 : Blo 1506950 1507411 := bstep (se 1 (by rfl) ⟨1130558, by rfl⟩ : syracuseStep 1507411 = 2261117) B2261117
theorem B1507427 : Blo 1506950 1507427 := bstep (se 1 (by rfl) ⟨1130570, by rfl⟩ : syracuseStep 1507427 = 2261141) B2261141
theorem B2261105 : Blo 1506950 2261105 := bstep (se 2 (by rfl) ⟨847914, by rfl⟩ : syracuseStep 2261105 = 1695829) B1695829
theorem B1507443 : Blo 1506950 1507443 := bstep (se 1 (by rfl) ⟨1130582, by rfl⟩ : syracuseStep 1507443 = 2261165) B2261165
theorem B2261123 : Blo 1506950 2261123 := bstep (se 1 (by rfl) ⟨1695842, by rfl⟩ : syracuseStep 2261123 = 3391685) B3391685
theorem B1507459 : Blo 1506950 1507459 := bstep (se 1 (by rfl) ⟨1130594, by rfl⟩ : syracuseStep 1507459 = 2261189) B2261189
theorem B1507475 : Blo 1506950 1507475 := bstep (se 1 (by rfl) ⟨1130606, by rfl⟩ : syracuseStep 1507475 = 2261213) B2261213
theorem B2261153 : Blo 1506950 2261153 := bstep (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) B1695865
theorem B1507491 : Blo 1506950 1507491 := bstep (se 1 (by rfl) ⟨1130618, by rfl⟩ : syracuseStep 1507491 = 2261237) B2261237
theorem B2261171 : Blo 1506950 2261171 := bstep (se 1 (by rfl) ⟨1695878, by rfl⟩ : syracuseStep 2261171 = 3391757) B3391757
theorem B1507507 : Blo 1506950 1507507 := bstep (se 1 (by rfl) ⟨1130630, by rfl⟩ : syracuseStep 1507507 = 2261261) B2261261
theorem B1507523 : Blo 1506950 1507523 := bstep (se 1 (by rfl) ⟨1130642, by rfl⟩ : syracuseStep 1507523 = 2261285) B2261285
theorem B8593613 : Blo 1506950 8593613 := bstep (se 3 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 8593613 = 3222605) B3222605
theorem B2261201 : Blo 1506950 2261201 := bstep (se 2 (by rfl) ⟨847950, by rfl⟩ : syracuseStep 2261201 = 1695901) B1695901
theorem B1695955 : Blo 1506950 1695955 := bstep (se 1 (by rfl) ⟨1271966, by rfl⟩ : syracuseStep 1695955 = 2543933) B2543933
theorem B1507539 : Blo 1506950 1507539 := bstep (se 1 (by rfl) ⟨1130654, by rfl⟩ : syracuseStep 1507539 = 2261309) B2261309
theorem B1908947 : Blo 1506950 1908947 := bstep (se 1 (by rfl) ⟨1431710, by rfl⟩ : syracuseStep 1908947 = 2863421) B2863421
theorem B2261219 : Blo 1506950 2261219 := bstep (se 1 (by rfl) ⟨1695914, by rfl⟩ : syracuseStep 2261219 = 3391829) B3391829
theorem B1507555 : Blo 1506950 1507555 := bstep (se 1 (by rfl) ⟨1130666, by rfl⟩ : syracuseStep 1507555 = 2261333) B2261333
theorem B1507571 : Blo 1506950 1507571 := bstep (se 1 (by rfl) ⟨1130678, by rfl⟩ : syracuseStep 1507571 = 2261357) B2261357
theorem B2416883 : Blo 1506950 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B2261249 : Blo 1506950 2261249 := bstep (se 2 (by rfl) ⟨847968, by rfl⟩ : syracuseStep 2261249 = 1695937) B1695937
theorem B1507587 : Blo 1506950 1507587 := bstep (se 1 (by rfl) ⟨1130690, by rfl⟩ : syracuseStep 1507587 = 2261381) B2261381
theorem B5087501 : Blo 1506950 5087501 := bstep (se 3 (by rfl) ⟨953906, by rfl⟩ : syracuseStep 5087501 = 1907813) B1907813
theorem B5726477 : Blo 1506950 5726477 := bstep (se 3 (by rfl) ⟨1073714, by rfl⟩ : syracuseStep 5726477 = 2147429) B2147429
theorem B2261267 : Blo 1506950 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B1507603 : Blo 1506950 1507603 := bstep (se 1 (by rfl) ⟨1130702, by rfl⟩ : syracuseStep 1507603 = 2261405) B2261405
theorem B1507619 : Blo 1506950 1507619 := bstep (se 1 (by rfl) ⟨1130714, by rfl⟩ : syracuseStep 1507619 = 2261429) B2261429
theorem B3817763 : Blo 1506950 3817763 := bstep (se 1 (by rfl) ⟨2863322, by rfl⟩ : syracuseStep 3817763 = 5726645) B5726645
theorem B4350257 : Blo 1506950 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B3391793 : Blo 1506950 3391793 := bstep (se 2 (by rfl) ⟨1271922, by rfl⟩ : syracuseStep 3391793 = 2543845) B2543845
theorem B2261297 : Blo 1506950 2261297 := bstep (se 2 (by rfl) ⟨847986, by rfl⟩ : syracuseStep 2261297 = 1695973) B1695973
theorem B2146609 : Blo 1506950 2146609 := bstep (se 2 (by rfl) ⟨804978, by rfl⟩ : syracuseStep 2146609 = 1609957) B1609957
theorem B1507635 : Blo 1506950 1507635 := bstep (se 1 (by rfl) ⟨1130726, by rfl⟩ : syracuseStep 1507635 = 2261453) B2261453
theorem B5087555 : Blo 1506950 5087555 := bstep (se 1 (by rfl) ⟨3815666, by rfl⟩ : syracuseStep 5087555 = 7631333) B7631333
theorem B3391811 : Blo 1506950 3391811 := bstep (se 1 (by rfl) ⟨2543858, by rfl⟩ : syracuseStep 3391811 = 5087717) B5087717
theorem B12878149 : Blo 1506950 12878149 := bstep (se 4 (by rfl) ⟨1207326, by rfl⟩ : syracuseStep 12878149 = 2414653) B2414653
theorem B2261315 : Blo 1506950 2261315 := bstep (se 1 (by rfl) ⟨1695986, by rfl⟩ : syracuseStep 2261315 = 3391973) B3391973
theorem B1507651 : Blo 1506950 1507651 := bstep (se 1 (by rfl) ⟨1130738, by rfl⟩ : syracuseStep 1507651 = 2261477) B2261477
theorem B4292945 : Blo 1506950 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B1507667 : Blo 1506950 1507667 := bstep (se 1 (by rfl) ⟨1130750, by rfl⟩ : syracuseStep 1507667 = 2261501) B2261501
theorem B2261345 : Blo 1506950 2261345 := bstep (se 2 (by rfl) ⟨848004, by rfl⟩ : syracuseStep 2261345 = 1696009) B1696009
theorem B16294243 : Blo 1506950 16294243 := bstep (se 1 (by rfl) ⟨12220682, by rfl⟩ : syracuseStep 16294243 = 24441365) B24441365
theorem B1696099 : Blo 1506950 1696099 := bstep (se 1 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 1696099 = 2544149) B2544149
theorem B1507683 : Blo 1506950 1507683 := bstep (se 1 (by rfl) ⟨1130762, by rfl⟩ : syracuseStep 1507683 = 2261525) B2261525
theorem B2261363 : Blo 1506950 2261363 := bstep (se 1 (by rfl) ⟨1696022, by rfl⟩ : syracuseStep 2261363 = 3392045) B3392045
theorem B1507699 : Blo 1506950 1507699 := bstep (se 1 (by rfl) ⟨1130774, by rfl⟩ : syracuseStep 1507699 = 2261549) B2261549
theorem B1507715 : Blo 1506950 1507715 := bstep (se 1 (by rfl) ⟨1130786, by rfl⟩ : syracuseStep 1507715 = 2261573) B2261573
theorem B7733645 : Blo 1506950 7733645 := bstep (se 3 (by rfl) ⟨1450058, by rfl⟩ : syracuseStep 7733645 = 2900117) B2900117
theorem B2261393 : Blo 1506950 2261393 := bstep (se 2 (by rfl) ⟨848022, by rfl⟩ : syracuseStep 2261393 = 1696045) B1696045
theorem B1507731 : Blo 1506950 1507731 := bstep (se 1 (by rfl) ⟨1130798, by rfl⟩ : syracuseStep 1507731 = 2261597) B2261597
theorem B2261411 : Blo 1506950 2261411 := bstep (se 1 (by rfl) ⟨1696058, by rfl⟩ : syracuseStep 2261411 = 3392117) B3392117
theorem B1507747 : Blo 1506950 1507747 := bstep (se 1 (by rfl) ⟨1130810, by rfl⟩ : syracuseStep 1507747 = 2261621) B2261621
theorem B1507763 : Blo 1506950 1507763 := bstep (se 1 (by rfl) ⟨1130822, by rfl⟩ : syracuseStep 1507763 = 2261645) B2261645
theorem B2261441 : Blo 1506950 2261441 := bstep (se 2 (by rfl) ⟨848040, by rfl⟩ : syracuseStep 2261441 = 1696081) B1696081
theorem B1507779 : Blo 1506950 1507779 := bstep (se 1 (by rfl) ⟨1130834, by rfl⟩ : syracuseStep 1507779 = 2261669) B2261669
theorem B2261459 : Blo 1506950 2261459 := bstep (se 1 (by rfl) ⟨1696094, by rfl⟩ : syracuseStep 2261459 = 3392189) B3392189
theorem B1507795 : Blo 1506950 1507795 := bstep (se 1 (by rfl) ⟨1130846, by rfl⟩ : syracuseStep 1507795 = 2261693) B2261693
theorem B1507811 : Blo 1506950 1507811 := bstep (se 1 (by rfl) ⟨1130858, by rfl⟩ : syracuseStep 1507811 = 2261717) B2261717
theorem B3817955 : Blo 1506950 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B2261489 : Blo 1506950 2261489 := bstep (se 2 (by rfl) ⟨848058, by rfl⟩ : syracuseStep 2261489 = 1696117) B1696117
theorem B19325425 : Blo 1506950 19325425 := bstep (se 2 (by rfl) ⟨7247034, by rfl⟩ : syracuseStep 19325425 = 14494069) B14494069
theorem B1696243 : Blo 1506950 1696243 := bstep (se 1 (by rfl) ⟨1272182, by rfl⟩ : syracuseStep 1696243 = 2544365) B2544365
theorem B1507827 : Blo 1506950 1507827 := bstep (se 1 (by rfl) ⟨1130870, by rfl⟩ : syracuseStep 1507827 = 2261741) B2261741
theorem B2064899 : Blo 1506950 2064899 := bstep (se 1 (by rfl) ⟨1548674, by rfl⟩ : syracuseStep 2064899 = 3097349) B3097349
theorem B2261507 : Blo 1506950 2261507 := bstep (se 1 (by rfl) ⟨1696130, by rfl⟩ : syracuseStep 2261507 = 3392261) B3392261
theorem B1507843 : Blo 1506950 1507843 := bstep (se 1 (by rfl) ⟨1130882, by rfl⟩ : syracuseStep 1507843 = 2261765) B2261765
theorem B1507859 : Blo 1506950 1507859 := bstep (se 1 (by rfl) ⟨1130894, by rfl⟩ : syracuseStep 1507859 = 2261789) B2261789
theorem B2261537 : Blo 1506950 2261537 := bstep (se 2 (by rfl) ⟨848076, by rfl⟩ : syracuseStep 2261537 = 1696153) B1696153
theorem B1507875 : Blo 1506950 1507875 := bstep (se 1 (by rfl) ⟨1130906, by rfl⟩ : syracuseStep 1507875 = 2261813) B2261813
theorem B2261555 : Blo 1506950 2261555 := bstep (se 1 (by rfl) ⟨1696166, by rfl⟩ : syracuseStep 2261555 = 3392333) B3392333
theorem B1507891 : Blo 1506950 1507891 := bstep (se 1 (by rfl) ⟨1130918, by rfl⟩ : syracuseStep 1507891 = 2261837) B2261837
theorem B1507907 : Blo 1506950 1507907 := bstep (se 1 (by rfl) ⟨1130930, by rfl⟩ : syracuseStep 1507907 = 2261861) B2261861
theorem B8585797 : Blo 1506950 8585797 := bstep (se 4 (by rfl) ⟨804918, by rfl⟩ : syracuseStep 8585797 = 1609837) B1609837
theorem B5087825 : Blo 1506950 5087825 := bstep (se 2 (by rfl) ⟨1907934, by rfl⟩ : syracuseStep 5087825 = 3815869) B3815869
theorem B3392081 : Blo 1506950 3392081 := bstep (se 2 (by rfl) ⟨1272030, by rfl⟩ : syracuseStep 3392081 = 2544061) B2544061
theorem B2261585 : Blo 1506950 2261585 := bstep (se 2 (by rfl) ⟨848094, by rfl⟩ : syracuseStep 2261585 = 1696189) B1696189
theorem B1507923 : Blo 1506950 1507923 := bstep (se 1 (by rfl) ⟨1130942, by rfl⟩ : syracuseStep 1507923 = 2261885) B2261885
theorem B3392099 : Blo 1506950 3392099 := bstep (se 1 (by rfl) ⟨2544074, by rfl⟩ : syracuseStep 3392099 = 5088149) B5088149
theorem B2261603 : Blo 1506950 2261603 := bstep (se 1 (by rfl) ⟨1696202, by rfl⟩ : syracuseStep 2261603 = 3392405) B3392405
theorem B1507939 : Blo 1506950 1507939 := bstep (se 1 (by rfl) ⟨1130954, by rfl⟩ : syracuseStep 1507939 = 2261909) B2261909
theorem B1507955 : Blo 1506950 1507955 := bstep (se 1 (by rfl) ⟨1130966, by rfl⟩ : syracuseStep 1507955 = 2261933) B2261933
theorem B2261633 : Blo 1506950 2261633 := bstep (se 2 (by rfl) ⟨848112, by rfl⟩ : syracuseStep 2261633 = 1696225) B1696225
theorem B1696387 : Blo 1506950 1696387 := bstep (se 1 (by rfl) ⟨1272290, by rfl⟩ : syracuseStep 1696387 = 2544581) B2544581
theorem B1507971 : Blo 1506950 1507971 := bstep (se 1 (by rfl) ⟨1130978, by rfl⟩ : syracuseStep 1507971 = 2261957) B2261957
theorem B7250573 : Blo 1506950 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B2261651 : Blo 1506950 2261651 := bstep (se 1 (by rfl) ⟨1696238, by rfl⟩ : syracuseStep 2261651 = 3392477) B3392477
theorem B1507987 : Blo 1506950 1507987 := bstep (se 1 (by rfl) ⟨1130990, by rfl⟩ : syracuseStep 1507987 = 2261981) B2261981
theorem B1508003 : Blo 1506950 1508003 := bstep (se 1 (by rfl) ⟨1131002, by rfl⟩ : syracuseStep 1508003 = 2262005) B2262005
theorem B3220145 : Blo 1506950 3220145 := bstep (se 2 (by rfl) ⟨1207554, by rfl⟩ : syracuseStep 3220145 = 2415109) B2415109
theorem B2261681 : Blo 1506950 2261681 := bstep (se 2 (by rfl) ⟨848130, by rfl⟩ : syracuseStep 2261681 = 1696261) B1696261
theorem B1508019 : Blo 1506950 1508019 := bstep (se 1 (by rfl) ⟨1131014, by rfl⟩ : syracuseStep 1508019 = 2262029) B2262029
theorem B2261699 : Blo 1506950 2261699 := bstep (se 1 (by rfl) ⟨1696274, by rfl⟩ : syracuseStep 2261699 = 3392549) B3392549
theorem B1508035 : Blo 1506950 1508035 := bstep (se 1 (by rfl) ⟨1131026, by rfl⟩ : syracuseStep 1508035 = 2262053) B2262053
theorem B1508051 : Blo 1506950 1508051 := bstep (se 1 (by rfl) ⟨1131038, by rfl⟩ : syracuseStep 1508051 = 2262077) B2262077
theorem B2261729 : Blo 1506950 2261729 := bstep (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) B1696297
theorem B1508067 : Blo 1506950 1508067 := bstep (se 1 (by rfl) ⟨1131050, by rfl⟩ : syracuseStep 1508067 = 2262101) B2262101
theorem B2261747 : Blo 1506950 2261747 := bstep (se 1 (by rfl) ⟨1696310, by rfl⟩ : syracuseStep 2261747 = 3392621) B3392621
theorem B1508083 : Blo 1506950 1508083 := bstep (se 1 (by rfl) ⟨1131062, by rfl⟩ : syracuseStep 1508083 = 2262125) B2262125
theorem B3621635 : Blo 1506950 3621635 := bstep (se 1 (by rfl) ⟨2716226, by rfl⟩ : syracuseStep 3621635 = 5432453) B5432453
theorem B1508099 : Blo 1506950 1508099 := bstep (se 1 (by rfl) ⟨1131074, by rfl⟩ : syracuseStep 1508099 = 2262149) B2262149
theorem B2261777 : Blo 1506950 2261777 := bstep (se 2 (by rfl) ⟨848166, by rfl⟩ : syracuseStep 2261777 = 1696333) B1696333
theorem B1696531 : Blo 1506950 1696531 := bstep (se 1 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 1696531 = 2544797) B2544797
theorem B1508115 : Blo 1506950 1508115 := bstep (se 1 (by rfl) ⟨1131086, by rfl⟩ : syracuseStep 1508115 = 2262173) B2262173
theorem B2261795 : Blo 1506950 2261795 := bstep (se 1 (by rfl) ⟨1696346, by rfl⟩ : syracuseStep 2261795 = 3392693) B3392693
theorem B1508131 : Blo 1506950 1508131 := bstep (se 1 (by rfl) ⟨1131098, by rfl⟩ : syracuseStep 1508131 = 2262197) B2262197
theorem B1508147 : Blo 1506950 1508147 := bstep (se 1 (by rfl) ⟨1131110, by rfl⟩ : syracuseStep 1508147 = 2262221) B2262221
theorem B2261825 : Blo 1506950 2261825 := bstep (se 2 (by rfl) ⟨848184, by rfl⟩ : syracuseStep 2261825 = 1696369) B1696369
theorem B1508163 : Blo 1506950 1508163 := bstep (se 1 (by rfl) ⟨1131122, by rfl⟩ : syracuseStep 1508163 = 2262245) B2262245
theorem B2261843 : Blo 1506950 2261843 := bstep (se 1 (by rfl) ⟨1696382, by rfl⟩ : syracuseStep 2261843 = 3392765) B3392765
theorem B1508179 : Blo 1506950 1508179 := bstep (se 1 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 1508179 = 2262269) B2262269
theorem B1508195 : Blo 1506950 1508195 := bstep (se 1 (by rfl) ⟨1131146, by rfl⟩ : syracuseStep 1508195 = 2262293) B2262293
theorem B3392369 : Blo 1506950 3392369 := bstep (se 2 (by rfl) ⟨1272138, by rfl⟩ : syracuseStep 3392369 = 2544277) B2544277
theorem B2261873 : Blo 1506950 2261873 := bstep (se 2 (by rfl) ⟨848202, by rfl⟩ : syracuseStep 2261873 = 1696405) B1696405
theorem B1508211 : Blo 1506950 1508211 := bstep (se 1 (by rfl) ⟨1131158, by rfl⟩ : syracuseStep 1508211 = 2262317) B2262317
theorem B12886897 : Blo 1506950 12886897 := bstep (se 2 (by rfl) ⟨4832586, by rfl⟩ : syracuseStep 12886897 = 9665173) B9665173
theorem B3392387 : Blo 1506950 3392387 := bstep (se 1 (by rfl) ⟨2544290, by rfl⟩ : syracuseStep 3392387 = 5088581) B5088581
theorem B2261891 : Blo 1506950 2261891 := bstep (se 1 (by rfl) ⟨1696418, by rfl⟩ : syracuseStep 2261891 = 3392837) B3392837
theorem B1508227 : Blo 1506950 1508227 := bstep (se 1 (by rfl) ⟨1131170, by rfl⟩ : syracuseStep 1508227 = 2262341) B2262341
theorem B1508243 : Blo 1506950 1508243 := bstep (se 1 (by rfl) ⟨1131182, by rfl⟩ : syracuseStep 1508243 = 2262365) B2262365
theorem B1909651 : Blo 1506950 1909651 := bstep (se 1 (by rfl) ⟨1432238, by rfl⟩ : syracuseStep 1909651 = 2864477) B2864477
theorem B2261921 : Blo 1506950 2261921 := bstep (se 2 (by rfl) ⟨848220, by rfl⟩ : syracuseStep 2261921 = 1696441) B1696441
theorem B1696675 : Blo 1506950 1696675 := bstep (se 1 (by rfl) ⟨1272506, by rfl⟩ : syracuseStep 1696675 = 2545013) B2545013
theorem B1508259 : Blo 1506950 1508259 := bstep (se 1 (by rfl) ⟨1131194, by rfl⟩ : syracuseStep 1508259 = 2262389) B2262389
theorem B2261939 : Blo 1506950 2261939 := bstep (se 1 (by rfl) ⟨1696454, by rfl⟩ : syracuseStep 2261939 = 3392909) B3392909
theorem B1508275 : Blo 1506950 1508275 := bstep (se 1 (by rfl) ⟨1131206, by rfl⟩ : syracuseStep 1508275 = 2262413) B2262413
theorem B3621827 : Blo 1506950 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B1508291 : Blo 1506950 1508291 := bstep (se 1 (by rfl) ⟨1131218, by rfl⟩ : syracuseStep 1508291 = 2262437) B2262437
theorem B2261969 : Blo 1506950 2261969 := bstep (se 2 (by rfl) ⟨848238, by rfl⟩ : syracuseStep 2261969 = 1696477) B1696477
theorem B1508307 : Blo 1506950 1508307 := bstep (se 1 (by rfl) ⟨1131230, by rfl⟩ : syracuseStep 1508307 = 2262461) B2262461
theorem B2261987 : Blo 1506950 2261987 := bstep (se 1 (by rfl) ⟨1696490, by rfl⟩ : syracuseStep 2261987 = 3392981) B3392981
theorem B1508323 : Blo 1506950 1508323 := bstep (se 1 (by rfl) ⟨1131242, by rfl⟩ : syracuseStep 1508323 = 2262485) B2262485
theorem B2147315 : Blo 1506950 2147315 := bstep (se 1 (by rfl) ⟨1610486, by rfl⟩ : syracuseStep 2147315 = 3220973) B3220973
theorem B1508339 : Blo 1506950 1508339 := bstep (se 1 (by rfl) ⟨1131254, by rfl⟩ : syracuseStep 1508339 = 2262509) B2262509
theorem B1909747 : Blo 1506950 1909747 := bstep (se 1 (by rfl) ⟨1432310, by rfl⟩ : syracuseStep 1909747 = 2864621) B2864621
theorem B2262017 : Blo 1506950 2262017 := bstep (se 2 (by rfl) ⟨848256, by rfl⟩ : syracuseStep 2262017 = 1696513) B1696513
theorem B1508355 : Blo 1506950 1508355 := bstep (se 1 (by rfl) ⟨1131266, by rfl⟩ : syracuseStep 1508355 = 2262533) B2262533
theorem B2262035 : Blo 1506950 2262035 := bstep (se 1 (by rfl) ⟨1696526, by rfl⟩ : syracuseStep 2262035 = 3393053) B3393053
theorem B1508371 : Blo 1506950 1508371 := bstep (se 1 (by rfl) ⟨1131278, by rfl⟩ : syracuseStep 1508371 = 2262557) B2262557
theorem B3621923 : Blo 1506950 3621923 := bstep (se 1 (by rfl) ⟨2716442, by rfl⟩ : syracuseStep 3621923 = 5432885) B5432885
theorem B1508387 : Blo 1506950 1508387 := bstep (se 1 (by rfl) ⟨1131290, by rfl⟩ : syracuseStep 1508387 = 2262581) B2262581
theorem B2262065 : Blo 1506950 2262065 := bstep (se 2 (by rfl) ⟨848274, by rfl⟩ : syracuseStep 2262065 = 1696549) B1696549
theorem B1696819 : Blo 1506950 1696819 := bstep (se 1 (by rfl) ⟨1272614, by rfl⟩ : syracuseStep 1696819 = 2545229) B2545229
theorem B1508403 : Blo 1506950 1508403 := bstep (se 1 (by rfl) ⟨1131302, by rfl⟩ : syracuseStep 1508403 = 2262605) B2262605
theorem B2262083 : Blo 1506950 2262083 := bstep (se 1 (by rfl) ⟨1696562, by rfl⟩ : syracuseStep 2262083 = 3393125) B3393125
theorem B1508419 : Blo 1506950 1508419 := bstep (se 1 (by rfl) ⟨1131314, by rfl⟩ : syracuseStep 1508419 = 2262629) B2262629
theorem B16311365 : Blo 1506950 16311365 := bstep (se 4 (by rfl) ⟨1529190, by rfl⟩ : syracuseStep 16311365 = 3058381) B3058381
theorem B1508435 : Blo 1506950 1508435 := bstep (se 1 (by rfl) ⟨1131326, by rfl⟩ : syracuseStep 1508435 = 2262653) B2262653
theorem B2262113 : Blo 1506950 2262113 := bstep (se 2 (by rfl) ⟨848292, by rfl⟩ : syracuseStep 2262113 = 1696585) B1696585
theorem B1508451 : Blo 1506950 1508451 := bstep (se 1 (by rfl) ⟨1131338, by rfl⟩ : syracuseStep 1508451 = 2262677) B2262677
theorem B5088365 : Blo 1506950 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B2262131 : Blo 1506950 2262131 := bstep (se 1 (by rfl) ⟨1696598, by rfl⟩ : syracuseStep 2262131 = 3393197) B3393197
theorem B1508467 : Blo 1506950 1508467 := bstep (se 1 (by rfl) ⟨1131350, by rfl⟩ : syracuseStep 1508467 = 2262701) B2262701
theorem B1508483 : Blo 1506950 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B3392657 : Blo 1506950 3392657 := bstep (se 2 (by rfl) ⟨1272246, by rfl⟩ : syracuseStep 3392657 = 2544493) B2544493
theorem B2262161 : Blo 1506950 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B1508499 : Blo 1506950 1508499 := bstep (se 1 (by rfl) ⟨1131374, by rfl⟩ : syracuseStep 1508499 = 2262749) B2262749
theorem B5088419 : Blo 1506950 5088419 := bstep (se 1 (by rfl) ⟨3816314, by rfl⟩ : syracuseStep 5088419 = 7632629) B7632629
theorem B3392675 : Blo 1506950 3392675 := bstep (se 1 (by rfl) ⟨2544506, by rfl⟩ : syracuseStep 3392675 = 5089013) B5089013
theorem B2262179 : Blo 1506950 2262179 := bstep (se 1 (by rfl) ⟨1696634, by rfl⟩ : syracuseStep 2262179 = 3393269) B3393269
theorem B1508515 : Blo 1506950 1508515 := bstep (se 1 (by rfl) ⟨1131386, by rfl⟩ : syracuseStep 1508515 = 2262773) B2262773
theorem B1508531 : Blo 1506950 1508531 := bstep (se 1 (by rfl) ⟨1131398, by rfl⟩ : syracuseStep 1508531 = 2262797) B2262797
theorem B2065601 : Blo 1506950 2065601 := bstep (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) B1549201
theorem B2262209 : Blo 1506950 2262209 := bstep (se 2 (by rfl) ⟨848328, by rfl⟩ : syracuseStep 2262209 = 1696657) B1696657
theorem B1696963 : Blo 1506950 1696963 := bstep (se 1 (by rfl) ⟨1272722, by rfl⟩ : syracuseStep 1696963 = 2545445) B2545445
theorem B1508547 : Blo 1506950 1508547 := bstep (se 1 (by rfl) ⟨1131410, by rfl⟩ : syracuseStep 1508547 = 2262821) B2262821
theorem B2262227 : Blo 1506950 2262227 := bstep (se 1 (by rfl) ⟨1696670, by rfl⟩ : syracuseStep 2262227 = 3393341) B3393341
theorem B1508563 : Blo 1506950 1508563 := bstep (se 1 (by rfl) ⟨1131422, by rfl⟩ : syracuseStep 1508563 = 2262845) B2262845
theorem B1508579 : Blo 1506950 1508579 := bstep (se 1 (by rfl) ⟨1131434, by rfl⟩ : syracuseStep 1508579 = 2262869) B2262869
theorem B2262257 : Blo 1506950 2262257 := bstep (se 2 (by rfl) ⟨848346, by rfl⟩ : syracuseStep 2262257 = 1696693) B1696693
theorem B1508595 : Blo 1506950 1508595 := bstep (se 1 (by rfl) ⟨1131446, by rfl⟩ : syracuseStep 1508595 = 2262893) B2262893
theorem B2262275 : Blo 1506950 2262275 := bstep (se 1 (by rfl) ⟨1696706, by rfl⟩ : syracuseStep 2262275 = 3393413) B3393413
theorem B1508611 : Blo 1506950 1508611 := bstep (se 1 (by rfl) ⟨1131458, by rfl⟩ : syracuseStep 1508611 = 2262917) B2262917
theorem B4293901 : Blo 1506950 4293901 := bstep (se 3 (by rfl) ⟨805106, by rfl⟩ : syracuseStep 4293901 = 1610213) B1610213
theorem B1508627 : Blo 1506950 1508627 := bstep (se 1 (by rfl) ⟨1131470, by rfl⟩ : syracuseStep 1508627 = 2262941) B2262941
theorem B2262305 : Blo 1506950 2262305 := bstep (se 2 (by rfl) ⟨848364, by rfl⟩ : syracuseStep 2262305 = 1696729) B1696729
theorem B5432611 : Blo 1506950 5432611 := bstep (se 1 (by rfl) ⟨4074458, by rfl⟩ : syracuseStep 5432611 = 8148917) B8148917
theorem B6112547 : Blo 1506950 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B1508643 : Blo 1506950 1508643 := bstep (se 1 (by rfl) ⟨1131482, by rfl⟩ : syracuseStep 1508643 = 2262965) B2262965
theorem B2262323 : Blo 1506950 2262323 := bstep (se 1 (by rfl) ⟨1696742, by rfl⟩ : syracuseStep 2262323 = 3393485) B3393485
theorem B1508659 : Blo 1506950 1508659 := bstep (se 1 (by rfl) ⟨1131494, by rfl⟩ : syracuseStep 1508659 = 2262989) B2262989
theorem B1508675 : Blo 1506950 1508675 := bstep (se 1 (by rfl) ⟨1131506, by rfl⟩ : syracuseStep 1508675 = 2263013) B2263013
theorem B8152397 : Blo 1506950 8152397 := bstep (se 3 (by rfl) ⟨1528574, by rfl⟩ : syracuseStep 8152397 = 3057149) B3057149
theorem B2262353 : Blo 1506950 2262353 := bstep (se 2 (by rfl) ⟨848382, by rfl⟩ : syracuseStep 2262353 = 1696765) B1696765
theorem B1697107 : Blo 1506950 1697107 := bstep (se 1 (by rfl) ⟨1272830, by rfl⟩ : syracuseStep 1697107 = 2545661) B2545661
theorem B1508691 : Blo 1506950 1508691 := bstep (se 1 (by rfl) ⟨1131518, by rfl⟩ : syracuseStep 1508691 = 2263037) B2263037
theorem B2262371 : Blo 1506950 2262371 := bstep (se 1 (by rfl) ⟨1696778, by rfl⟩ : syracuseStep 2262371 = 3393557) B3393557
theorem B1508707 : Blo 1506950 1508707 := bstep (se 1 (by rfl) ⟨1131530, by rfl⟩ : syracuseStep 1508707 = 2263061) B2263061
theorem B6440305 : Blo 1506950 6440305 := bstep (se 2 (by rfl) ⟨2415114, by rfl⟩ : syracuseStep 6440305 = 4830229) B4830229
theorem B1508723 : Blo 1506950 1508723 := bstep (se 1 (by rfl) ⟨1131542, by rfl⟩ : syracuseStep 1508723 = 2263085) B2263085
theorem B2262401 : Blo 1506950 2262401 := bstep (se 2 (by rfl) ⟨848400, by rfl⟩ : syracuseStep 2262401 = 1696801) B1696801
theorem B1508739 : Blo 1506950 1508739 := bstep (se 1 (by rfl) ⟨1131554, by rfl⟩ : syracuseStep 1508739 = 2263109) B2263109
theorem B3818897 : Blo 1506950 3818897 := bstep (se 2 (by rfl) ⟨1432086, by rfl⟩ : syracuseStep 3818897 = 2864173) B2864173
theorem B2262419 : Blo 1506950 2262419 := bstep (se 1 (by rfl) ⟨1696814, by rfl⟩ : syracuseStep 2262419 = 3393629) B3393629
theorem B1508755 : Blo 1506950 1508755 := bstep (se 1 (by rfl) ⟨1131566, by rfl⟩ : syracuseStep 1508755 = 2263133) B2263133
theorem B1508771 : Blo 1506950 1508771 := bstep (se 1 (by rfl) ⟨1131578, by rfl⟩ : syracuseStep 1508771 = 2263157) B2263157
theorem B5088689 : Blo 1506950 5088689 := bstep (se 2 (by rfl) ⟨1908258, by rfl⟩ : syracuseStep 5088689 = 3816517) B3816517
theorem B3392945 : Blo 1506950 3392945 := bstep (se 2 (by rfl) ⟨1272354, by rfl⟩ : syracuseStep 3392945 = 2544709) B2544709
theorem B2262449 : Blo 1506950 2262449 := bstep (se 2 (by rfl) ⟨848418, by rfl⟩ : syracuseStep 2262449 = 1696837) B1696837
theorem B1508787 : Blo 1506950 1508787 := bstep (se 1 (by rfl) ⟨1131590, by rfl⟩ : syracuseStep 1508787 = 2263181) B2263181
theorem B3392963 : Blo 1506950 3392963 := bstep (se 1 (by rfl) ⟨2544722, by rfl⟩ : syracuseStep 3392963 = 5089445) B5089445
theorem B2262467 : Blo 1506950 2262467 := bstep (se 1 (by rfl) ⟨1696850, by rfl⟩ : syracuseStep 2262467 = 3393701) B3393701
theorem B3818947 : Blo 1506950 3818947 := bstep (se 1 (by rfl) ⟨2864210, by rfl⟩ : syracuseStep 3818947 = 5728421) B5728421
theorem B1508803 : Blo 1506950 1508803 := bstep (se 1 (by rfl) ⟨1131602, by rfl⟩ : syracuseStep 1508803 = 2263205) B2263205
theorem B1508819 : Blo 1506950 1508819 := bstep (se 1 (by rfl) ⟨1131614, by rfl⟩ : syracuseStep 1508819 = 2263229) B2263229
theorem B2262497 : Blo 1506950 2262497 := bstep (se 2 (by rfl) ⟨848436, by rfl⟩ : syracuseStep 2262497 = 1696873) B1696873
theorem B1697251 : Blo 1506950 1697251 := bstep (se 1 (by rfl) ⟨1272938, by rfl⟩ : syracuseStep 1697251 = 2545877) B2545877
theorem B1508835 : Blo 1506950 1508835 := bstep (se 1 (by rfl) ⟨1131626, by rfl⟩ : syracuseStep 1508835 = 2263253) B2263253
theorem B4294129 : Blo 1506950 4294129 := bstep (se 2 (by rfl) ⟨1610298, by rfl⟩ : syracuseStep 4294129 = 3220597) B3220597
theorem B9176561 : Blo 1506950 9176561 := bstep (se 2 (by rfl) ⟨3441210, by rfl⟩ : syracuseStep 9176561 = 6882421) B6882421
theorem B2262515 : Blo 1506950 2262515 := bstep (se 1 (by rfl) ⟨1696886, by rfl⟩ : syracuseStep 2262515 = 3393773) B3393773
theorem B1508851 : Blo 1506950 1508851 := bstep (se 1 (by rfl) ⟨1131638, by rfl⟩ : syracuseStep 1508851 = 2263277) B2263277
theorem B1508867 : Blo 1506950 1508867 := bstep (se 1 (by rfl) ⟨1131650, by rfl⟩ : syracuseStep 1508867 = 2263301) B2263301
theorem B13936141 : Blo 1506950 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B2262545 : Blo 1506950 2262545 := bstep (se 2 (by rfl) ⟨848454, by rfl⟩ : syracuseStep 2262545 = 1696909) B1696909
theorem B1508883 : Blo 1506950 1508883 := bstep (se 1 (by rfl) ⟨1131662, by rfl⟩ : syracuseStep 1508883 = 2263325) B2263325
theorem B2262563 : Blo 1506950 2262563 := bstep (se 1 (by rfl) ⟨1696922, by rfl⟩ : syracuseStep 2262563 = 3393845) B3393845
theorem B1508899 : Blo 1506950 1508899 := bstep (se 1 (by rfl) ⟨1131674, by rfl⟩ : syracuseStep 1508899 = 2263349) B2263349
theorem B3221041 : Blo 1506950 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B1508915 : Blo 1506950 1508915 := bstep (se 1 (by rfl) ⟨1131686, by rfl⟩ : syracuseStep 1508915 = 2263373) B2263373
theorem B2262593 : Blo 1506950 2262593 := bstep (se 2 (by rfl) ⟨848472, by rfl⟩ : syracuseStep 2262593 = 1696945) B1696945
theorem B3221059 : Blo 1506950 3221059 := bstep (se 1 (by rfl) ⟨2415794, by rfl⟩ : syracuseStep 3221059 = 4831589) B4831589
theorem B1508931 : Blo 1506950 1508931 := bstep (se 1 (by rfl) ⟨1131698, by rfl⟩ : syracuseStep 1508931 = 2263397) B2263397
theorem B3819089 : Blo 1506950 3819089 := bstep (se 2 (by rfl) ⟨1432158, by rfl⟩ : syracuseStep 3819089 = 2864317) B2864317
theorem B2262611 : Blo 1506950 2262611 := bstep (se 1 (by rfl) ⟨1696958, by rfl⟩ : syracuseStep 2262611 = 3393917) B3393917
theorem B1508947 : Blo 1506950 1508947 := bstep (se 1 (by rfl) ⟨1131710, by rfl⟩ : syracuseStep 1508947 = 2263421) B2263421
theorem B2262641 : Blo 1506950 2262641 := bstep (se 2 (by rfl) ⟨848490, by rfl⟩ : syracuseStep 2262641 = 1696981) B1696981
theorem B2147953 : Blo 1506950 2147953 := bstep (se 2 (by rfl) ⟨805482, by rfl⟩ : syracuseStep 2147953 = 1610965) B1610965
theorem B1697395 : Blo 1506950 1697395 := bstep (se 1 (by rfl) ⟨1273046, by rfl⟩ : syracuseStep 1697395 = 2546093) B2546093
theorem B2262659 : Blo 1506950 2262659 := bstep (se 1 (by rfl) ⟨1696994, by rfl⟩ : syracuseStep 2262659 = 3393989) B3393989
theorem B4294289 : Blo 1506950 4294289 := bstep (se 2 (by rfl) ⟨1610358, by rfl⟩ : syracuseStep 4294289 = 3220717) B3220717
theorem B2262689 : Blo 1506950 2262689 := bstep (se 2 (by rfl) ⟨848508, by rfl⟩ : syracuseStep 2262689 = 1697017) B1697017
theorem B2262707 : Blo 1506950 2262707 := bstep (se 1 (by rfl) ⟨1697030, by rfl⟩ : syracuseStep 2262707 = 3394061) B3394061
theorem B13231813 : Blo 1506950 13231813 := bstep (se 4 (by rfl) ⟨1240482, by rfl⟩ : syracuseStep 13231813 = 2480965) B2480965
theorem B3393233 : Blo 1506950 3393233 := bstep (se 2 (by rfl) ⟨1272462, by rfl⟩ : syracuseStep 3393233 = 2544925) B2544925
theorem B2262737 : Blo 1506950 2262737 := bstep (se 2 (by rfl) ⟨848526, by rfl⟩ : syracuseStep 2262737 = 1697053) B1697053
theorem B3393251 : Blo 1506950 3393251 := bstep (se 1 (by rfl) ⟨2544938, by rfl⟩ : syracuseStep 3393251 = 5089877) B5089877
theorem B2262755 : Blo 1506950 2262755 := bstep (se 1 (by rfl) ⟨1697066, by rfl⟩ : syracuseStep 2262755 = 3394133) B3394133
theorem B2148067 : Blo 1506950 2148067 := bstep (se 1 (by rfl) ⟨1611050, by rfl⟩ : syracuseStep 2148067 = 3222101) B3222101
theorem B2262785 : Blo 1506950 2262785 := bstep (se 2 (by rfl) ⟨848544, by rfl⟩ : syracuseStep 2262785 = 1697089) B1697089
theorem B4294403 : Blo 1506950 4294403 := bstep (se 1 (by rfl) ⟨3220802, by rfl⟩ : syracuseStep 4294403 = 6441605) B6441605
theorem B1697539 : Blo 1506950 1697539 := bstep (se 1 (by rfl) ⟨1273154, by rfl⟩ : syracuseStep 1697539 = 2546309) B2546309
theorem B2262803 : Blo 1506950 2262803 := bstep (se 1 (by rfl) ⟨1697102, by rfl⟩ : syracuseStep 2262803 = 3394205) B3394205
theorem B2262833 : Blo 1506950 2262833 := bstep (se 2 (by rfl) ⟨848562, by rfl⟩ : syracuseStep 2262833 = 1697125) B1697125
theorem B2262851 : Blo 1506950 2262851 := bstep (se 1 (by rfl) ⟨1697138, by rfl⟩ : syracuseStep 2262851 = 3394277) B3394277
theorem B2901841 : Blo 1506950 2901841 := bstep (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) B2176381
theorem B5801827 : Blo 1506950 5801827 := bstep (se 1 (by rfl) ⟨4351370, by rfl⟩ : syracuseStep 5801827 = 8702741) B8702741
theorem B17172323 : Blo 1506950 17172323 := bstep (se 1 (by rfl) ⟨12879242, by rfl⟩ : syracuseStep 17172323 = 25758485) B25758485
theorem B2262881 : Blo 1506950 2262881 := bstep (se 2 (by rfl) ⟨848580, by rfl⟩ : syracuseStep 2262881 = 1697161) B1697161
theorem B2262899 : Blo 1506950 2262899 := bstep (se 1 (by rfl) ⟨1697174, by rfl⟩ : syracuseStep 2262899 = 3394349) B3394349
theorem B2262929 : Blo 1506950 2262929 := bstep (se 2 (by rfl) ⟨848598, by rfl⟩ : syracuseStep 2262929 = 1697197) B1697197
theorem B2262947 : Blo 1506950 2262947 := bstep (se 1 (by rfl) ⟨1697210, by rfl⟩ : syracuseStep 2262947 = 3394421) B3394421
theorem B2262977 : Blo 1506950 2262977 := bstep (se 2 (by rfl) ⟨848616, by rfl⟩ : syracuseStep 2262977 = 1697233) B1697233
theorem B5089229 : Blo 1506950 5089229 := bstep (se 3 (by rfl) ⟨954230, by rfl⟩ : syracuseStep 5089229 = 1908461) B1908461
theorem B2262995 : Blo 1506950 2262995 := bstep (se 1 (by rfl) ⟨1697246, by rfl⟩ : syracuseStep 2262995 = 3394493) B3394493
theorem B1812451 : Blo 1506950 1812451 := bstep (se 1 (by rfl) ⟨1359338, by rfl⟩ : syracuseStep 1812451 = 2718677) B2718677
theorem B3393521 : Blo 1506950 3393521 := bstep (se 2 (by rfl) ⟨1272570, by rfl⟩ : syracuseStep 3393521 = 2545141) B2545141
theorem B2263025 : Blo 1506950 2263025 := bstep (se 2 (by rfl) ⟨848634, by rfl⟩ : syracuseStep 2263025 = 1697269) B1697269
theorem B5089283 : Blo 1506950 5089283 := bstep (se 1 (by rfl) ⟨3816962, by rfl⟩ : syracuseStep 5089283 = 7633925) B7633925
theorem B3393539 : Blo 1506950 3393539 := bstep (se 1 (by rfl) ⟨2545154, by rfl⟩ : syracuseStep 3393539 = 5090309) B5090309
theorem B2263043 : Blo 1506950 2263043 := bstep (se 1 (by rfl) ⟨1697282, by rfl⟩ : syracuseStep 2263043 = 3394565) B3394565
theorem B7243789 : Blo 1506950 7243789 := bstep (se 3 (by rfl) ⟨1358210, by rfl⟩ : syracuseStep 7243789 = 2716421) B2716421
theorem B1812499 : Blo 1506950 1812499 := bstep (se 1 (by rfl) ⟨1359374, by rfl⟩ : syracuseStep 1812499 = 2718749) B2718749
theorem B2263073 : Blo 1506950 2263073 := bstep (se 2 (by rfl) ⟨848652, by rfl⟩ : syracuseStep 2263073 = 1697305) B1697305
theorem B6285347 : Blo 1506950 6285347 := bstep (se 1 (by rfl) ⟨4714010, by rfl⟩ : syracuseStep 6285347 = 9428021) B9428021
theorem B2263091 : Blo 1506950 2263091 := bstep (se 1 (by rfl) ⟨1697318, by rfl⟩ : syracuseStep 2263091 = 3394637) B3394637
theorem B19859525 : Blo 1506950 19859525 := bstep (se 4 (by rfl) ⟨1861830, by rfl⟩ : syracuseStep 19859525 = 3723661) B3723661
theorem B11454533 : Blo 1506950 11454533 := bstep (se 4 (by rfl) ⟨1073862, by rfl⟩ : syracuseStep 11454533 = 2147725) B2147725
theorem B2263121 : Blo 1506950 2263121 := bstep (se 2 (by rfl) ⟨848670, by rfl⟩ : syracuseStep 2263121 = 1697341) B1697341
theorem B2263139 : Blo 1506950 2263139 := bstep (se 1 (by rfl) ⟨1697354, by rfl⟩ : syracuseStep 2263139 = 3394709) B3394709
theorem B2263169 : Blo 1506950 2263169 := bstep (se 2 (by rfl) ⟨848688, by rfl⟩ : syracuseStep 2263169 = 1697377) B1697377
theorem B2263187 : Blo 1506950 2263187 := bstep (se 1 (by rfl) ⟨1697390, by rfl⟩ : syracuseStep 2263187 = 3394781) B3394781
theorem B2861219 : Blo 1506950 2861219 := bstep (se 1 (by rfl) ⟨2145914, by rfl⟩ : syracuseStep 2861219 = 4291829) B4291829
theorem B2263217 : Blo 1506950 2263217 := bstep (se 2 (by rfl) ⟨848706, by rfl⟩ : syracuseStep 2263217 = 1697413) B1697413
theorem B2263235 : Blo 1506950 2263235 := bstep (se 1 (by rfl) ⟨1697426, by rfl⟩ : syracuseStep 2263235 = 3394853) B3394853
theorem B2263265 : Blo 1506950 2263265 := bstep (se 2 (by rfl) ⟨848724, by rfl⟩ : syracuseStep 2263265 = 1697449) B1697449
theorem B2263283 : Blo 1506950 2263283 := bstep (se 1 (by rfl) ⟨1697462, by rfl⟩ : syracuseStep 2263283 = 3394925) B3394925
theorem B5089553 : Blo 1506950 5089553 := bstep (se 2 (by rfl) ⟨1908582, by rfl⟩ : syracuseStep 5089553 = 3817165) B3817165
theorem B3393809 : Blo 1506950 3393809 := bstep (se 2 (by rfl) ⟨1272678, by rfl⟩ : syracuseStep 3393809 = 2545357) B2545357
theorem B2263313 : Blo 1506950 2263313 := bstep (se 2 (by rfl) ⟨848742, by rfl⟩ : syracuseStep 2263313 = 1697485) B1697485
theorem B3393827 : Blo 1506950 3393827 := bstep (se 1 (by rfl) ⟨2545370, by rfl⟩ : syracuseStep 3393827 = 5090741) B5090741
theorem B2263331 : Blo 1506950 2263331 := bstep (se 1 (by rfl) ⟨1697498, by rfl⟩ : syracuseStep 2263331 = 3394997) B3394997
theorem B2263361 : Blo 1506950 2263361 := bstep (se 2 (by rfl) ⟨848760, by rfl⟩ : syracuseStep 2263361 = 1697521) B1697521
theorem B5728589 : Blo 1506950 5728589 := bstep (se 3 (by rfl) ⟨1074110, by rfl⟩ : syracuseStep 5728589 = 2148221) B2148221
theorem B2263379 : Blo 1506950 2263379 := bstep (se 1 (by rfl) ⟨1697534, by rfl⟩ : syracuseStep 2263379 = 3395069) B3395069
theorem B2263409 : Blo 1506950 2263409 := bstep (se 2 (by rfl) ⟨848778, by rfl⟩ : syracuseStep 2263409 = 1697557) B1697557
theorem B2861507 : Blo 1506950 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B12224965 : Blo 1506950 12224965 := bstep (se 4 (by rfl) ⟨1146090, by rfl⟩ : syracuseStep 12224965 = 2292181) B2292181
theorem B9660869 : Blo 1506950 9660869 := bstep (se 4 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 9660869 = 1811413) B1811413
theorem B9169357 : Blo 1506950 9169357 := bstep (se 3 (by rfl) ⟨1719254, by rfl⟩ : syracuseStep 9169357 = 3438509) B3438509
theorem B7637489 : Blo 1506950 7637489 := bstep (se 2 (by rfl) ⟨2864058, by rfl⟩ : syracuseStep 7637489 = 5728117) B5728117
theorem B8587781 : Blo 1506950 8587781 := bstep (se 4 (by rfl) ⟨805104, by rfl⟩ : syracuseStep 8587781 = 1610209) B1610209
theorem B3394097 : Blo 1506950 3394097 := bstep (se 2 (by rfl) ⟨1272786, by rfl⟩ : syracuseStep 3394097 = 2545573) B2545573
theorem B3394115 : Blo 1506950 3394115 := bstep (se 1 (by rfl) ⟨2545586, by rfl⟩ : syracuseStep 3394115 = 5091173) B5091173
theorem B7629389 : Blo 1506950 7629389 := bstep (se 3 (by rfl) ⟨1430510, by rfl⟩ : syracuseStep 7629389 = 2861021) B2861021
theorem B4827757 : Blo 1506950 4827757 := bstep (se 3 (by rfl) ⟨905204, by rfl⟩ : syracuseStep 4827757 = 1810409) B1810409
theorem B16304753 : Blo 1506950 16304753 := bstep (se 2 (by rfl) ⟨6114282, by rfl⟩ : syracuseStep 16304753 = 12228565) B12228565
theorem B4295405 : Blo 1506950 4295405 := bstep (se 3 (by rfl) ⟨805388, by rfl⟩ : syracuseStep 4295405 = 1610777) B1610777
theorem B5090093 : Blo 1506950 5090093 := bstep (se 3 (by rfl) ⟨954392, by rfl⟩ : syracuseStep 5090093 = 1908785) B1908785
theorem B3394385 : Blo 1506950 3394385 := bstep (se 2 (by rfl) ⟨1272894, by rfl⟩ : syracuseStep 3394385 = 2545789) B2545789
theorem B5090147 : Blo 1506950 5090147 := bstep (se 1 (by rfl) ⟨3817610, by rfl⟩ : syracuseStep 5090147 = 7635221) B7635221
theorem B3394403 : Blo 1506950 3394403 := bstep (se 1 (by rfl) ⟨2545802, by rfl⟩ : syracuseStep 3394403 = 5091605) B5091605
theorem B3623825 : Blo 1506950 3623825 := bstep (se 2 (by rfl) ⟨1358934, by rfl⟩ : syracuseStep 3623825 = 2717869) B2717869
theorem B4295587 : Blo 1506950 4295587 := bstep (se 1 (by rfl) ⟨3221690, by rfl⟩ : syracuseStep 4295587 = 6443381) B6443381
theorem B4295747 : Blo 1506950 4295747 := bstep (se 1 (by rfl) ⟨3221810, by rfl⟩ : syracuseStep 4295747 = 6443621) B6443621
theorem B7736419 : Blo 1506950 7736419 := bstep (se 1 (by rfl) ⟨5802314, by rfl⟩ : syracuseStep 7736419 = 11604629) B11604629
theorem B5090417 : Blo 1506950 5090417 := bstep (se 2 (by rfl) ⟨1908906, by rfl⟩ : syracuseStep 5090417 = 3817813) B3817813
theorem B3394673 : Blo 1506950 3394673 := bstep (se 2 (by rfl) ⟨1273002, by rfl⟩ : syracuseStep 3394673 = 2546005) B2546005
theorem B3394691 : Blo 1506950 3394691 := bstep (se 1 (by rfl) ⟨2546018, by rfl⟩ : syracuseStep 3394691 = 5092037) B5092037
theorem B2862449 : Blo 1506950 2862449 := bstep (se 2 (by rfl) ⟨1073418, by rfl⟩ : syracuseStep 2862449 = 2146837) B2146837
theorem B3394961 : Blo 1506950 3394961 := bstep (se 2 (by rfl) ⟨1273110, by rfl⟩ : syracuseStep 3394961 = 2546221) B2546221
theorem B3624355 : Blo 1506950 3624355 := bstep (se 1 (by rfl) ⟨2718266, by rfl⟩ : syracuseStep 3624355 = 5436533) B5436533
theorem B3394979 : Blo 1506950 3394979 := bstep (se 1 (by rfl) ⟨2546234, by rfl⟩ : syracuseStep 3394979 = 5092469) B5092469
theorem B4828589 : Blo 1506950 4828589 := bstep (se 3 (by rfl) ⟨905360, by rfl⟩ : syracuseStep 4828589 = 1810721) B1810721
theorem B2543089 : Blo 1506950 2543089 := bstep (se 2 (by rfl) ⟨953658, by rfl⟩ : syracuseStep 2543089 = 1907317) B1907317
theorem B2543123 : Blo 1506950 2543123 := bstep (se 1 (by rfl) ⟨1907342, by rfl⟩ : syracuseStep 2543123 = 3814685) B3814685
theorem B21745205 : Blo 1506950 21745205 := bstep (se 5 (by rfl) ⟨1019306, by rfl⟩ : syracuseStep 21745205 = 2038613) B2038613
theorem B5090957 : Blo 1506950 5090957 := bstep (se 3 (by rfl) ⟨954554, by rfl⟩ : syracuseStep 5090957 = 1909109) B1909109
theorem B2543251 : Blo 1506950 2543251 := bstep (se 1 (by rfl) ⟨1907438, by rfl⟩ : syracuseStep 2543251 = 3814877) B3814877
theorem B5091011 : Blo 1506950 5091011 := bstep (se 1 (by rfl) ⟨3818258, by rfl⟩ : syracuseStep 5091011 = 7636517) B7636517
theorem B1609427 : Blo 1506950 1609427 := bstep (se 1 (by rfl) ⟨1207070, by rfl⟩ : syracuseStep 1609427 = 2414141) B2414141
theorem B27528931 : Blo 1506950 27528931 := bstep (se 1 (by rfl) ⟨20646698, by rfl⟩ : syracuseStep 27528931 = 41293397) B41293397
theorem B2543393 : Blo 1506950 2543393 := bstep (se 2 (by rfl) ⟨953772, by rfl⟩ : syracuseStep 2543393 = 1907545) B1907545
theorem B2543521 : Blo 1506950 2543521 := bstep (se 2 (by rfl) ⟨953820, by rfl⟩ : syracuseStep 2543521 = 1907641) B1907641
theorem B7638947 : Blo 1506950 7638947 := bstep (se 1 (by rfl) ⟨5729210, by rfl⟩ : syracuseStep 7638947 = 11458421) B11458421
theorem B2543555 : Blo 1506950 2543555 := bstep (se 1 (by rfl) ⟨1907666, by rfl⟩ : syracuseStep 2543555 = 3815333) B3815333
theorem B21737413 : Blo 1506950 21737413 := bstep (se 4 (by rfl) ⟨2037882, by rfl⟩ : syracuseStep 21737413 = 4075765) B4075765
theorem B5091281 : Blo 1506950 5091281 := bstep (se 2 (by rfl) ⟨1909230, by rfl⟩ : syracuseStep 5091281 = 3818461) B3818461
theorem B2543683 : Blo 1506950 2543683 := bstep (se 1 (by rfl) ⟨1907762, by rfl⟩ : syracuseStep 2543683 = 3815525) B3815525
theorem B4296817 : Blo 1506950 4296817 := bstep (se 2 (by rfl) ⟨1611306, by rfl⟩ : syracuseStep 4296817 = 3222613) B3222613
theorem B38670533 : Blo 1506950 38670533 := bstep (se 4 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 38670533 = 7250725) B7250725
theorem B2543825 : Blo 1506950 2543825 := bstep (se 2 (by rfl) ⟨953934, by rfl⟩ : syracuseStep 2543825 = 1907869) B1907869
theorem B2863345 : Blo 1506950 2863345 := bstep (se 2 (by rfl) ⟨1073754, by rfl⟩ : syracuseStep 2863345 = 2147509) B2147509
theorem B2543953 : Blo 1506950 2543953 := bstep (se 2 (by rfl) ⟨953982, by rfl⟩ : syracuseStep 2543953 = 1907965) B1907965
theorem B2355569 : Blo 1506950 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B2543987 : Blo 1506950 2543987 := bstep (se 1 (by rfl) ⟨1907990, by rfl⟩ : syracuseStep 2543987 = 3815981) B3815981
theorem B2863505 : Blo 1506950 2863505 := bstep (se 2 (by rfl) ⟨1073814, by rfl⟩ : syracuseStep 2863505 = 2147629) B2147629
theorem B5091821 : Blo 1506950 5091821 := bstep (se 3 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 5091821 = 1909433) B1909433
theorem B2544115 : Blo 1506950 2544115 := bstep (se 1 (by rfl) ⟨1908086, by rfl⟩ : syracuseStep 2544115 = 3816173) B3816173
theorem B5091875 : Blo 1506950 5091875 := bstep (se 1 (by rfl) ⟨3818906, by rfl⟩ : syracuseStep 5091875 = 7637813) B7637813
theorem B2544257 : Blo 1506950 2544257 := bstep (se 2 (by rfl) ⟨954096, by rfl⟩ : syracuseStep 2544257 = 1908193) B1908193
theorem B3355345 : Blo 1506950 3355345 := bstep (se 2 (by rfl) ⟨1258254, by rfl⟩ : syracuseStep 3355345 = 2516509) B2516509
theorem B2544385 : Blo 1506950 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B73331477 : Blo 1506950 73331477 := bstep (se 6 (by rfl) ⟨1718706, by rfl⟩ : syracuseStep 73331477 = 3437413) B3437413
theorem B2544419 : Blo 1506950 2544419 := bstep (se 1 (by rfl) ⟨1908314, by rfl⟩ : syracuseStep 2544419 = 3816629) B3816629
theorem B2863907 : Blo 1506950 2863907 := bstep (se 1 (by rfl) ⟨2147930, by rfl⟩ : syracuseStep 2863907 = 4295861) B4295861
theorem B5092145 : Blo 1506950 5092145 := bstep (se 2 (by rfl) ⟨1909554, by rfl⟩ : syracuseStep 5092145 = 3819109) B3819109
theorem B11449187 : Blo 1506950 11449187 := bstep (se 1 (by rfl) ⟨8586890, by rfl⟩ : syracuseStep 11449187 = 17173781) B17173781
theorem B1766291 : Blo 1506950 1766291 := bstep (se 1 (by rfl) ⟨1324718, by rfl⟩ : syracuseStep 1766291 = 2649437) B2649437
theorem B2544547 : Blo 1506950 2544547 := bstep (se 1 (by rfl) ⟨1908410, by rfl⟩ : syracuseStep 2544547 = 3816821) B3816821
theorem B6443981 : Blo 1506950 6443981 := bstep (se 3 (by rfl) ⟨1208246, by rfl⟩ : syracuseStep 6443981 = 2416493) B2416493
theorem B2544689 : Blo 1506950 2544689 := bstep (se 2 (by rfl) ⟨954258, by rfl⟩ : syracuseStep 2544689 = 1908517) B1908517
theorem B1610803 : Blo 1506950 1610803 := bstep (se 1 (by rfl) ⟨1208102, by rfl⟩ : syracuseStep 1610803 = 2416205) B2416205
theorem B1528931 : Blo 1506950 1528931 := bstep (se 1 (by rfl) ⟨1146698, by rfl⟩ : syracuseStep 1528931 = 2293397) B2293397
theorem B74339441 : Blo 1506950 74339441 := bstep (se 2 (by rfl) ⟨27877290, by rfl⟩ : syracuseStep 74339441 = 55754581) B55754581
theorem B2544817 : Blo 1506950 2544817 := bstep (se 2 (by rfl) ⟨954306, by rfl⟩ : syracuseStep 2544817 = 1908613) B1908613
theorem B2544851 : Blo 1506950 2544851 := bstep (se 1 (by rfl) ⟨1908638, by rfl⟩ : syracuseStep 2544851 = 3817277) B3817277
theorem B8606947 : Blo 1506950 8606947 := bstep (se 1 (by rfl) ⟨6455210, by rfl⟩ : syracuseStep 8606947 = 12910421) B12910421
theorem B9655537 : Blo 1506950 9655537 := bstep (se 2 (by rfl) ⟨3620826, by rfl⟩ : syracuseStep 9655537 = 7241653) B7241653
theorem B20641009 : Blo 1506950 20641009 := bstep (se 2 (by rfl) ⟨7740378, by rfl⟩ : syracuseStep 20641009 = 15480757) B15480757
theorem B5092685 : Blo 1506950 5092685 := bstep (se 3 (by rfl) ⟨954878, by rfl⟩ : syracuseStep 5092685 = 1909757) B1909757
theorem B2544979 : Blo 1506950 2544979 := bstep (se 1 (by rfl) ⟨1908734, by rfl⟩ : syracuseStep 2544979 = 3817469) B3817469
theorem B7632305 : Blo 1506950 7632305 := bstep (se 2 (by rfl) ⟨2862114, by rfl⟩ : syracuseStep 7632305 = 5724229) B5724229
theorem B2037187 : Blo 1506950 2037187 := bstep (se 1 (by rfl) ⟨1527890, by rfl⟩ : syracuseStep 2037187 = 3055781) B3055781
theorem B2414033 : Blo 1506950 2414033 := bstep (se 2 (by rfl) ⟨905262, by rfl⟩ : syracuseStep 2414033 = 1810525) B1810525
theorem B2545121 : Blo 1506950 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B4830691 : Blo 1506950 4830691 := bstep (se 1 (by rfl) ⟨3623018, by rfl⟩ : syracuseStep 4830691 = 7246037) B7246037
theorem B3814897 : Blo 1506950 3814897 := bstep (se 2 (by rfl) ⟨1430586, by rfl⟩ : syracuseStep 3814897 = 2861173) B2861173
theorem B16520689 : Blo 1506950 16520689 := bstep (se 2 (by rfl) ⟨6195258, by rfl⟩ : syracuseStep 16520689 = 12390517) B12390517
theorem B2545249 : Blo 1506950 2545249 := bstep (se 2 (by rfl) ⟨954468, by rfl⟩ : syracuseStep 2545249 = 1908937) B1908937
theorem B4830833 : Blo 1506950 4830833 := bstep (se 2 (by rfl) ⟨1811562, by rfl⟩ : syracuseStep 4830833 = 3623125) B3623125
theorem B2545283 : Blo 1506950 2545283 := bstep (se 1 (by rfl) ⟨1908962, by rfl⟩ : syracuseStep 2545283 = 3817925) B3817925
theorem B2414243 : Blo 1506950 2414243 := bstep (se 1 (by rfl) ⟨1810682, by rfl⟩ : syracuseStep 2414243 = 3621365) B3621365
theorem B19330757 : Blo 1506950 19330757 := bstep (se 4 (by rfl) ⟨1812258, by rfl⟩ : syracuseStep 19330757 = 3624517) B3624517
theorem B3815171 : Blo 1506950 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B2545411 : Blo 1506950 2545411 := bstep (se 1 (by rfl) ⟨1909058, by rfl⟩ : syracuseStep 2545411 = 3818117) B3818117
theorem B2324257 : Blo 1506950 2324257 := bstep (se 2 (by rfl) ⟨871596, by rfl⟩ : syracuseStep 2324257 = 1743193) B1743193
theorem B4962115 : Blo 1506950 4962115 := bstep (se 1 (by rfl) ⟨3721586, by rfl⟩ : syracuseStep 4962115 = 7443173) B7443173
theorem B5724017 : Blo 1506950 5724017 := bstep (se 2 (by rfl) ⟨2146506, by rfl⟩ : syracuseStep 5724017 = 4293013) B4293013
theorem B10868593 : Blo 1506950 10868593 := bstep (se 2 (by rfl) ⟨4075722, by rfl⟩ : syracuseStep 10868593 = 8151445) B8151445
theorem B2545553 : Blo 1506950 2545553 := bstep (se 2 (by rfl) ⟨954582, by rfl⟩ : syracuseStep 2545553 = 1909165) B1909165
theorem B3815363 : Blo 1506950 3815363 := bstep (se 1 (by rfl) ⟨2861522, by rfl⟩ : syracuseStep 3815363 = 5723045) B5723045
theorem B2578403 : Blo 1506950 2578403 := bstep (se 1 (by rfl) ⟨1933802, by rfl⟩ : syracuseStep 2578403 = 3867605) B3867605
theorem B32610275 : Blo 1506950 32610275 := bstep (se 1 (by rfl) ⟨24457706, by rfl⟩ : syracuseStep 32610275 = 48915413) B48915413
theorem B2545681 : Blo 1506950 2545681 := bstep (se 2 (by rfl) ⟨954630, by rfl⟩ : syracuseStep 2545681 = 1909261) B1909261
theorem B2545715 : Blo 1506950 2545715 := bstep (se 1 (by rfl) ⟨1909286, by rfl⟩ : syracuseStep 2545715 = 3818573) B3818573
theorem B2447443 : Blo 1506950 2447443 := bstep (se 1 (by rfl) ⟨1835582, by rfl⟩ : syracuseStep 2447443 = 3671165) B3671165
theorem B5961869 : Blo 1506950 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B2545843 : Blo 1506950 2545843 := bstep (se 1 (by rfl) ⟨1909382, by rfl⟩ : syracuseStep 2545843 = 3818765) B3818765
theorem B9173197 : Blo 1506950 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B7248113 : Blo 1506950 7248113 := bstep (se 2 (by rfl) ⟨2718042, by rfl⟩ : syracuseStep 7248113 = 5436085) B5436085
theorem B1718515 : Blo 1506950 1718515 := bstep (se 1 (by rfl) ⟨1288886, by rfl⟩ : syracuseStep 1718515 = 2577773) B2577773
theorem B8591629 : Blo 1506950 8591629 := bstep (se 3 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 8591629 = 3221861) B3221861
theorem B2545985 : Blo 1506950 2545985 := bstep (se 2 (by rfl) ⟨954744, by rfl⟩ : syracuseStep 2545985 = 1909489) B1909489
theorem B7739725 : Blo 1506950 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B2415025 : Blo 1506950 2415025 := bstep (se 2 (by rfl) ⟨905634, by rfl⟩ : syracuseStep 2415025 = 1811269) B1811269
theorem B2546113 : Blo 1506950 2546113 := bstep (se 2 (by rfl) ⟨954792, by rfl⟩ : syracuseStep 2546113 = 1909585) B1909585
theorem B2038225 : Blo 1506950 2038225 := bstep (se 2 (by rfl) ⟨764334, by rfl⟩ : syracuseStep 2038225 = 1528669) B1528669
theorem B2546147 : Blo 1506950 2546147 := bstep (se 1 (by rfl) ⟨1909610, by rfl⟩ : syracuseStep 2546147 = 3819221) B3819221
theorem B2546275 : Blo 1506950 2546275 := bstep (se 1 (by rfl) ⟨1909706, by rfl⟩ : syracuseStep 2546275 = 3819413) B3819413
theorem B4291373 : Blo 1506950 4291373 := bstep (se 3 (by rfl) ⟨804632, by rfl⟩ : syracuseStep 4291373 = 1609265) B1609265
theorem B8706865 : Blo 1506950 8706865 := bstep (se 2 (by rfl) ⟨3265074, by rfl⟩ : syracuseStep 8706865 = 6530149) B6530149
theorem B7633763 : Blo 1506950 7633763 := bstep (se 1 (by rfl) ⟨5725322, by rfl⟩ : syracuseStep 7633763 = 11450645) B11450645
theorem B3816305 : Blo 1506950 3816305 := bstep (se 2 (by rfl) ⟨1431114, by rfl⟩ : syracuseStep 3816305 = 2862229) B2862229
theorem B5086097 : Blo 1506950 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B3816355 : Blo 1506950 3816355 := bstep (se 1 (by rfl) ⟨2862266, by rfl⟩ : syracuseStep 3816355 = 5724533) B5724533
theorem B1907651 : Blo 1506950 1907651 := bstep (se 1 (by rfl) ⟨1430738, by rfl⟩ : syracuseStep 1907651 = 2861477) B2861477
theorem B4291555 : Blo 1506950 4291555 := bstep (se 1 (by rfl) ⟨3218666, by rfl⟩ : syracuseStep 4291555 = 6437333) B6437333
theorem B13794275 : Blo 1506950 13794275 := bstep (se 1 (by rfl) ⟨10345706, by rfl⟩ : syracuseStep 13794275 = 20691413) B20691413
theorem B3816497 : Blo 1506950 3816497 := bstep (se 2 (by rfl) ⟨1431186, by rfl⟩ : syracuseStep 3816497 = 2862373) B2862373
theorem B8150129 : Blo 1506950 8150129 := bstep (se 2 (by rfl) ⟨3056298, by rfl⟩ : syracuseStep 8150129 = 6112597) B6112597
theorem B3390641 : Blo 1506950 3390641 := bstep (se 2 (by rfl) ⟨1271490, by rfl⟩ : syracuseStep 3390641 = 2542981) B2542981
theorem B3390659 : Blo 1506950 3390659 := bstep (se 1 (by rfl) ⟨2542994, by rfl⟩ : syracuseStep 3390659 = 5085989) B5085989
theorem B2415827 : Blo 1506950 2415827 := bstep (se 1 (by rfl) ⟨1811870, by rfl⟩ : syracuseStep 2415827 = 3623741) B3623741
theorem B2579683 : Blo 1506950 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B5725475 : Blo 1506950 5725475 := bstep (se 1 (by rfl) ⟨4294106, by rfl⟩ : syracuseStep 5725475 = 8588213) B8588213
theorem B2039137 : Blo 1506950 2039137 := bstep (se 2 (by rfl) ⟨764676, by rfl⟩ : syracuseStep 2039137 = 1529353) B1529353
theorem B2039203 : Blo 1506950 2039203 := bstep (se 1 (by rfl) ⟨1529402, by rfl⟩ : syracuseStep 2039203 = 3058805) B3058805
theorem B5086637 : Blo 1506950 5086637 := bstep (se 3 (by rfl) ⟨953744, by rfl⟩ : syracuseStep 5086637 = 1907489) B1907489
theorem B2260433 : Blo 1506950 2260433 := bstep (se 2 (by rfl) ⟨847662, by rfl⟩ : syracuseStep 2260433 = 1695325) B1695325
theorem B3390929 : Blo 1506950 3390929 := bstep (se 2 (by rfl) ⟨1271598, by rfl⟩ : syracuseStep 3390929 = 2543197) B2543197
theorem B2260451 : Blo 1506950 2260451 := bstep (se 1 (by rfl) ⟨1695338, by rfl⟩ : syracuseStep 2260451 = 3390677) B3390677
theorem B3390947 : Blo 1506950 3390947 := bstep (se 1 (by rfl) ⟨2543210, by rfl⟩ : syracuseStep 3390947 = 5086421) B5086421
theorem B3218915 : Blo 1506950 3218915 := bstep (se 1 (by rfl) ⟨2414186, by rfl⟩ : syracuseStep 3218915 = 4828373) B4828373
theorem B5086691 : Blo 1506950 5086691 := bstep (se 1 (by rfl) ⟨3815018, by rfl⟩ : syracuseStep 5086691 = 7630037) B7630037
theorem B2260481 : Blo 1506950 2260481 := bstep (se 2 (by rfl) ⟨847680, by rfl⟩ : syracuseStep 2260481 = 1695361) B1695361
theorem B2260499 : Blo 1506950 2260499 := bstep (se 1 (by rfl) ⟨1695374, by rfl⟩ : syracuseStep 2260499 = 3390749) B3390749
theorem B2260529 : Blo 1506950 2260529 := bstep (se 2 (by rfl) ⟨847698, by rfl⟩ : syracuseStep 2260529 = 1695397) B1695397
theorem B27901493 : Blo 1506950 27901493 := bstep (se 5 (by rfl) ⟨1307882, by rfl⟩ : syracuseStep 27901493 = 2615765) B2615765
theorem B2145857 : Blo 1506950 2145857 := bstep (se 2 (by rfl) ⟨804696, by rfl⟩ : syracuseStep 2145857 = 1609393) B1609393
theorem B2260547 : Blo 1506950 2260547 := bstep (se 1 (by rfl) ⟨1695410, by rfl⟩ : syracuseStep 2260547 = 3390821) B3390821
theorem B2260577 : Blo 1506950 2260577 := bstep (se 2 (by rfl) ⟨847716, by rfl⟩ : syracuseStep 2260577 = 1695433) B1695433
theorem B2260595 : Blo 1506950 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B1908355 : Blo 1506950 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B7634573 : Blo 1506950 7634573 := bstep (se 3 (by rfl) ⟨1431482, by rfl⟩ : syracuseStep 7634573 = 2862965) B2862965
theorem B2260625 : Blo 1506950 2260625 := bstep (se 2 (by rfl) ⟨847734, by rfl⟩ : syracuseStep 2260625 = 1695469) B1695469
theorem B1506963 : Blo 1506950 1506963 := bstep (se 1 (by rfl) ⟨1130222, by rfl⟩ : syracuseStep 1506963 = 2260445) B2260445
theorem B1695379 : Blo 1506950 1695379 := bstep (se 1 (by rfl) ⟨1271534, by rfl⟩ : syracuseStep 1695379 = 2543069) B2543069
theorem B1506979 : Blo 1506950 1506979 := bstep (se 1 (by rfl) ⟨1130234, by rfl⟩ : syracuseStep 1506979 = 2260469) B2260469
theorem B2260643 : Blo 1506950 2260643 := bstep (se 1 (by rfl) ⟨1695482, by rfl⟩ : syracuseStep 2260643 = 3390965) B3390965
theorem B1506995 : Blo 1506950 1506995 := bstep (se 1 (by rfl) ⟨1130246, by rfl⟩ : syracuseStep 1506995 = 2260493) B2260493
theorem B2145971 : Blo 1506950 2145971 := bstep (se 1 (by rfl) ⟨1609478, by rfl⟩ : syracuseStep 2145971 = 3218957) B3218957
theorem B2260673 : Blo 1506950 2260673 := bstep (se 2 (by rfl) ⟨847752, by rfl⟩ : syracuseStep 2260673 = 1695505) B1695505
theorem B1507011 : Blo 1506950 1507011 := bstep (se 1 (by rfl) ⟨1130258, by rfl⟩ : syracuseStep 1507011 = 2260517) B2260517
theorem B1507027 : Blo 1506950 1507027 := bstep (se 1 (by rfl) ⟨1130270, by rfl⟩ : syracuseStep 1507027 = 2260541) B2260541
theorem B2260691 : Blo 1506950 2260691 := bstep (se 1 (by rfl) ⟨1695518, by rfl⟩ : syracuseStep 2260691 = 3391037) B3391037
theorem B2416339 : Blo 1506950 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B1507043 : Blo 1506950 1507043 := bstep (se 1 (by rfl) ⟨1130282, by rfl⟩ : syracuseStep 1507043 = 2260565) B2260565
theorem B1908451 : Blo 1506950 1908451 := bstep (se 1 (by rfl) ⟨1431338, by rfl⟩ : syracuseStep 1908451 = 2862677) B2862677
theorem B2260721 : Blo 1506950 2260721 := bstep (se 2 (by rfl) ⟨847770, by rfl⟩ : syracuseStep 2260721 = 1695541) B1695541
theorem B3391217 : Blo 1506950 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B1507059 : Blo 1506950 1507059 := bstep (se 1 (by rfl) ⟨1130294, by rfl⟩ : syracuseStep 1507059 = 2260589) B2260589
theorem B5086961 : Blo 1506950 5086961 := bstep (se 2 (by rfl) ⟨1907610, by rfl⟩ : syracuseStep 5086961 = 3815221) B3815221
theorem B1507075 : Blo 1506950 1507075 := bstep (se 1 (by rfl) ⟨1130306, by rfl⟩ : syracuseStep 1507075 = 2260613) B2260613
theorem B2260739 : Blo 1506950 2260739 := bstep (se 1 (by rfl) ⟨1695554, by rfl⟩ : syracuseStep 2260739 = 3391109) B3391109
theorem B3391235 : Blo 1506950 3391235 := bstep (se 1 (by rfl) ⟨2543426, by rfl⟩ : syracuseStep 3391235 = 5086853) B5086853
theorem B2146051 : Blo 1506950 2146051 := bstep (se 1 (by rfl) ⟨1609538, by rfl⟩ : syracuseStep 2146051 = 3219077) B3219077
theorem B1507091 : Blo 1506950 1507091 := bstep (se 1 (by rfl) ⟨1130318, by rfl⟩ : syracuseStep 1507091 = 2260637) B2260637
theorem B2260769 : Blo 1506950 2260769 := bstep (se 2 (by rfl) ⟨847788, by rfl⟩ : syracuseStep 2260769 = 1695577) B1695577
theorem B1507107 : Blo 1506950 1507107 := bstep (se 1 (by rfl) ⟨1130330, by rfl⟩ : syracuseStep 1507107 = 2260661) B2260661
theorem B1695523 : Blo 1506950 1695523 := bstep (se 1 (by rfl) ⟨1271642, by rfl⟩ : syracuseStep 1695523 = 2543285) B2543285
theorem B1507123 : Blo 1506950 1507123 := bstep (se 1 (by rfl) ⟨1130342, by rfl⟩ : syracuseStep 1507123 = 2260685) B2260685
theorem B2260787 : Blo 1506950 2260787 := bstep (se 1 (by rfl) ⟨1695590, by rfl⟩ : syracuseStep 2260787 = 3391181) B3391181
theorem B1507139 : Blo 1506950 1507139 := bstep (se 1 (by rfl) ⟨1130354, by rfl⟩ : syracuseStep 1507139 = 2260709) B2260709
theorem B2260817 : Blo 1506950 2260817 := bstep (se 2 (by rfl) ⟨847806, by rfl⟩ : syracuseStep 2260817 = 1695613) B1695613
theorem B1507155 : Blo 1506950 1507155 := bstep (se 1 (by rfl) ⟨1130366, by rfl⟩ : syracuseStep 1507155 = 2260733) B2260733
theorem B1507171 : Blo 1506950 1507171 := bstep (se 1 (by rfl) ⟨1130378, by rfl⟩ : syracuseStep 1507171 = 2260757) B2260757
theorem B2260835 : Blo 1506950 2260835 := bstep (se 1 (by rfl) ⟨1695626, by rfl⟩ : syracuseStep 2260835 = 3391253) B3391253
theorem B1507187 : Blo 1506950 1507187 := bstep (se 1 (by rfl) ⟨1130390, by rfl⟩ : syracuseStep 1507187 = 2260781) B2260781
theorem B2260865 : Blo 1506950 2260865 := bstep (se 2 (by rfl) ⟨847824, by rfl⟩ : syracuseStep 2260865 = 1695649) B1695649
theorem B1507203 : Blo 1506950 1507203 := bstep (se 1 (by rfl) ⟨1130402, by rfl⟩ : syracuseStep 1507203 = 2260805) B2260805
theorem B1507219 : Blo 1506950 1507219 := bstep (se 1 (by rfl) ⟨1130414, by rfl⟩ : syracuseStep 1507219 = 2260829) B2260829
theorem B2260883 : Blo 1506950 2260883 := bstep (se 1 (by rfl) ⟨1695662, by rfl⟩ : syracuseStep 2260883 = 3391325) B3391325
theorem B1507235 : Blo 1506950 1507235 := bstep (se 1 (by rfl) ⟨1130426, by rfl⟩ : syracuseStep 1507235 = 2260853) B2260853
theorem B2260913 : Blo 1506950 2260913 := bstep (se 2 (by rfl) ⟨847842, by rfl⟩ : syracuseStep 2260913 = 1695685) B1695685
theorem B1507251 : Blo 1506950 1507251 := bstep (se 1 (by rfl) ⟨1130438, by rfl⟩ : syracuseStep 1507251 = 2260877) B2260877
theorem B1695667 : Blo 1506950 1695667 := bstep (se 1 (by rfl) ⟨1271750, by rfl⟩ : syracuseStep 1695667 = 2543501) B2543501
theorem B1507267 : Blo 1506950 1507267 := bstep (se 1 (by rfl) ⟨1130450, by rfl⟩ : syracuseStep 1507267 = 2260901) B2260901
theorem B2260931 : Blo 1506950 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B4833229 : Blo 1506950 4833229 := bstep (se 3 (by rfl) ⟨906230, by rfl⟩ : syracuseStep 4833229 = 1812461) B1812461
theorem B1507283 : Blo 1506950 1507283 := bstep (se 1 (by rfl) ⟨1130462, by rfl⟩ : syracuseStep 1507283 = 2260925) B2260925
theorem B2260961 : Blo 1506950 2260961 := bstep (se 2 (by rfl) ⟨847860, by rfl⟩ : syracuseStep 2260961 = 1695721) B1695721
theorem B1507299 : Blo 1506950 1507299 := bstep (se 1 (by rfl) ⟨1130474, by rfl⟩ : syracuseStep 1507299 = 2260949) B2260949
theorem B5160941 : Blo 1506950 5160941 := bstep (se 3 (by rfl) ⟨967676, by rfl⟩ : syracuseStep 5160941 = 1935353) B1935353
theorem B1507315 : Blo 1506950 1507315 := bstep (se 1 (by rfl) ⟨1130486, by rfl⟩ : syracuseStep 1507315 = 2260973) B2260973
theorem B2260979 : Blo 1506950 2260979 := bstep (se 1 (by rfl) ⟨1695734, by rfl⟩ : syracuseStep 2260979 = 3391469) B3391469
theorem B2261003 : Blo 1506950 2261003 := bstep (se 1 (by rfl) ⟨1695752, by rfl⟩ : syracuseStep 2261003 = 3391505) B3391505
theorem B1507339 : Blo 1506950 1507339 := bstep (se 1 (by rfl) ⟨1130504, by rfl⟩ : syracuseStep 1507339 = 2261009) B2261009
theorem B9658385 : Blo 1506950 9658385 := bstep (se 2 (by rfl) ⟨3621894, by rfl⟩ : syracuseStep 9658385 = 7243789) B7243789
theorem B2261015 : Blo 1506950 2261015 := bstep (se 1 (by rfl) ⟨1695761, by rfl⟩ : syracuseStep 2261015 = 3391523) B3391523
theorem B1507351 : Blo 1506950 1507351 := bstep (se 1 (by rfl) ⟨1130513, by rfl⟩ : syracuseStep 1507351 = 2261027) B2261027
theorem B1507371 : Blo 1506950 1507371 := bstep (se 1 (by rfl) ⟨1130528, by rfl⟩ : syracuseStep 1507371 = 2261057) B2261057
theorem B1507383 : Blo 1506950 1507383 := bstep (se 1 (by rfl) ⟨1130537, by rfl⟩ : syracuseStep 1507383 = 2261075) B2261075
theorem B74326085 : Blo 1506950 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B1507403 : Blo 1506950 1507403 := bstep (se 1 (by rfl) ⟨1130552, by rfl⟩ : syracuseStep 1507403 = 2261105) B2261105
theorem B1507415 : Blo 1506950 1507415 := bstep (se 1 (by rfl) ⟨1130561, by rfl⟩ : syracuseStep 1507415 = 2261123) B2261123
theorem B3391577 : Blo 1506950 3391577 := bstep (se 2 (by rfl) ⟨1271841, by rfl⟩ : syracuseStep 3391577 = 2543683) B2543683
theorem B2261081 : Blo 1506950 2261081 := bstep (se 2 (by rfl) ⟨847905, by rfl⟩ : syracuseStep 2261081 = 1695811) B1695811
theorem B9666661 : Blo 1506950 9666661 := bstep (se 4 (by rfl) ⟨906249, by rfl⟩ : syracuseStep 9666661 = 1812499) B1812499
theorem B1507435 : Blo 1506950 1507435 := bstep (se 1 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 1507435 = 2261153) B2261153
theorem B1507447 : Blo 1506950 1507447 := bstep (se 1 (by rfl) ⟨1130585, by rfl⟩ : syracuseStep 1507447 = 2261171) B2261171
theorem B25780355 : Blo 1506950 25780355 := bstep (se 1 (by rfl) ⟨19335266, by rfl⟩ : syracuseStep 25780355 = 38670533) B38670533
theorem B1695883 : Blo 1506950 1695883 := bstep (se 1 (by rfl) ⟨1271912, by rfl⟩ : syracuseStep 1695883 = 2543825) B2543825
theorem B1507467 : Blo 1506950 1507467 := bstep (se 1 (by rfl) ⟨1130600, by rfl⟩ : syracuseStep 1507467 = 2261201) B2261201
theorem B1507479 : Blo 1506950 1507479 := bstep (se 1 (by rfl) ⟨1130609, by rfl⟩ : syracuseStep 1507479 = 2261219) B2261219
theorem B1507499 : Blo 1506950 1507499 := bstep (se 1 (by rfl) ⟨1130624, by rfl⟩ : syracuseStep 1507499 = 2261249) B2261249
theorem B3391667 : Blo 1506950 3391667 := bstep (se 1 (by rfl) ⟨2543750, by rfl⟩ : syracuseStep 3391667 = 5087501) B5087501
theorem B1507511 : Blo 1506950 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B3817651 : Blo 1506950 3817651 := bstep (se 1 (by rfl) ⟨2863238, by rfl⟩ : syracuseStep 3817651 = 5726477) B5726477
theorem B2261195 : Blo 1506950 2261195 := bstep (se 1 (by rfl) ⟨1695896, by rfl⟩ : syracuseStep 2261195 = 3391793) B3391793
theorem B1507531 : Blo 1506950 1507531 := bstep (se 1 (by rfl) ⟨1130648, by rfl⟩ : syracuseStep 1507531 = 2261297) B2261297
theorem B3391703 : Blo 1506950 3391703 := bstep (se 1 (by rfl) ⟨2543777, by rfl⟩ : syracuseStep 3391703 = 5087555) B5087555
theorem B2261207 : Blo 1506950 2261207 := bstep (se 1 (by rfl) ⟨1695905, by rfl⟩ : syracuseStep 2261207 = 3391811) B3391811
theorem B1507543 : Blo 1506950 1507543 := bstep (se 1 (by rfl) ⟨1130657, by rfl⟩ : syracuseStep 1507543 = 2261315) B2261315
theorem B1507563 : Blo 1506950 1507563 := bstep (se 1 (by rfl) ⟨1130672, by rfl⟩ : syracuseStep 1507563 = 2261345) B2261345
theorem B1695991 : Blo 1506950 1695991 := bstep (se 1 (by rfl) ⟨1271993, by rfl⟩ : syracuseStep 1695991 = 2543987) B2543987
theorem B1507575 : Blo 1506950 1507575 := bstep (se 1 (by rfl) ⟨1130681, by rfl⟩ : syracuseStep 1507575 = 2261363) B2261363
theorem B1507595 : Blo 1506950 1507595 := bstep (se 1 (by rfl) ⟨1130696, by rfl⟩ : syracuseStep 1507595 = 2261393) B2261393
theorem B1909003 : Blo 1506950 1909003 := bstep (se 1 (by rfl) ⟨1431752, by rfl⟩ : syracuseStep 1909003 = 2863505) B2863505
theorem B12230929 : Blo 1506950 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B1507607 : Blo 1506950 1507607 := bstep (se 1 (by rfl) ⟨1130705, by rfl⟩ : syracuseStep 1507607 = 2261411) B2261411
theorem B2261273 : Blo 1506950 2261273 := bstep (se 2 (by rfl) ⟨847977, by rfl⟩ : syracuseStep 2261273 = 1695955) B1695955
theorem B1507627 : Blo 1506950 1507627 := bstep (se 1 (by rfl) ⟨1130720, by rfl⟩ : syracuseStep 1507627 = 2261441) B2261441
theorem B1507639 : Blo 1506950 1507639 := bstep (se 1 (by rfl) ⟨1130729, by rfl⟩ : syracuseStep 1507639 = 2261459) B2261459
theorem B3817793 : Blo 1506950 3817793 := bstep (se 2 (by rfl) ⟨1431672, by rfl⟩ : syracuseStep 3817793 = 2863345) B2863345
theorem B1507659 : Blo 1506950 1507659 := bstep (se 1 (by rfl) ⟨1130744, by rfl⟩ : syracuseStep 1507659 = 2261489) B2261489
theorem B1507671 : Blo 1506950 1507671 := bstep (se 1 (by rfl) ⟨1130753, by rfl⟩ : syracuseStep 1507671 = 2261507) B2261507
theorem B1507691 : Blo 1506950 1507691 := bstep (se 1 (by rfl) ⟨1130768, by rfl⟩ : syracuseStep 1507691 = 2261537) B2261537
theorem B1507703 : Blo 1506950 1507703 := bstep (se 1 (by rfl) ⟨1130777, by rfl⟩ : syracuseStep 1507703 = 2261555) B2261555
theorem B3391883 : Blo 1506950 3391883 := bstep (se 1 (by rfl) ⟨2543912, by rfl⟩ : syracuseStep 3391883 = 5087825) B5087825
theorem B2261387 : Blo 1506950 2261387 := bstep (se 1 (by rfl) ⟨1696040, by rfl⟩ : syracuseStep 2261387 = 3392081) B3392081
theorem B1507723 : Blo 1506950 1507723 := bstep (se 1 (by rfl) ⟨1130792, by rfl⟩ : syracuseStep 1507723 = 2261585) B2261585
theorem B2261399 : Blo 1506950 2261399 := bstep (se 1 (by rfl) ⟨1696049, by rfl⟩ : syracuseStep 2261399 = 3392099) B3392099
theorem B1507735 : Blo 1506950 1507735 := bstep (se 1 (by rfl) ⟨1130801, by rfl⟩ : syracuseStep 1507735 = 2261603) B2261603
theorem B1696171 : Blo 1506950 1696171 := bstep (se 1 (by rfl) ⟨1272128, by rfl⟩ : syracuseStep 1696171 = 2544257) B2544257
theorem B1507755 : Blo 1506950 1507755 := bstep (se 1 (by rfl) ⟨1130816, by rfl⟩ : syracuseStep 1507755 = 2261633) B2261633
theorem B17170865 : Blo 1506950 17170865 := bstep (se 2 (by rfl) ⟨6439074, by rfl⟩ : syracuseStep 17170865 = 12878149) B12878149
theorem B1507767 : Blo 1506950 1507767 := bstep (se 1 (by rfl) ⟨1130825, by rfl⟩ : syracuseStep 1507767 = 2261651) B2261651
theorem B4833715 : Blo 1506950 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B3391937 : Blo 1506950 3391937 := bstep (se 2 (by rfl) ⟨1271976, by rfl⟩ : syracuseStep 3391937 = 2543953) B2543953
theorem B2146763 : Blo 1506950 2146763 := bstep (se 1 (by rfl) ⟨1610072, by rfl⟩ : syracuseStep 2146763 = 3220145) B3220145
theorem B1507787 : Blo 1506950 1507787 := bstep (se 1 (by rfl) ⟨1130840, by rfl⟩ : syracuseStep 1507787 = 2261681) B2261681
theorem B1507799 : Blo 1506950 1507799 := bstep (se 1 (by rfl) ⟨1130849, by rfl⟩ : syracuseStep 1507799 = 2261699) B2261699
theorem B21725657 : Blo 1506950 21725657 := bstep (se 2 (by rfl) ⟨8147121, by rfl⟩ : syracuseStep 21725657 = 16294243) B16294243
theorem B2261465 : Blo 1506950 2261465 := bstep (se 2 (by rfl) ⟨848049, by rfl⟩ : syracuseStep 2261465 = 1696099) B1696099
theorem B1507819 : Blo 1506950 1507819 := bstep (se 1 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 1507819 = 2261729) B2261729
theorem B1507831 : Blo 1506950 1507831 := bstep (se 1 (by rfl) ⟨1130873, by rfl⟩ : syracuseStep 1507831 = 2261747) B2261747
theorem B1507851 : Blo 1506950 1507851 := bstep (se 1 (by rfl) ⟨1130888, by rfl⟩ : syracuseStep 1507851 = 2261777) B2261777
theorem B1696279 : Blo 1506950 1696279 := bstep (se 1 (by rfl) ⟨1272209, by rfl⟩ : syracuseStep 1696279 = 2544419) B2544419
theorem B1507863 : Blo 1506950 1507863 := bstep (se 1 (by rfl) ⟨1130897, by rfl⟩ : syracuseStep 1507863 = 2261795) B2261795
theorem B1909271 : Blo 1506950 1909271 := bstep (se 1 (by rfl) ⟨1431953, by rfl⟩ : syracuseStep 1909271 = 2863907) B2863907
theorem B1507883 : Blo 1506950 1507883 := bstep (se 1 (by rfl) ⟨1130912, by rfl⟩ : syracuseStep 1507883 = 2261825) B2261825
theorem B1507895 : Blo 1506950 1507895 := bstep (se 1 (by rfl) ⟨1130921, by rfl⟩ : syracuseStep 1507895 = 2261843) B2261843
theorem B2261579 : Blo 1506950 2261579 := bstep (se 1 (by rfl) ⟨1696184, by rfl⟩ : syracuseStep 2261579 = 3392369) B3392369
theorem B1507915 : Blo 1506950 1507915 := bstep (se 1 (by rfl) ⟨1130936, by rfl⟩ : syracuseStep 1507915 = 2261873) B2261873
theorem B2261591 : Blo 1506950 2261591 := bstep (se 1 (by rfl) ⟨1696193, by rfl⟩ : syracuseStep 2261591 = 3392387) B3392387
theorem B1507927 : Blo 1506950 1507927 := bstep (se 1 (by rfl) ⟨1130945, by rfl⟩ : syracuseStep 1507927 = 2261891) B2261891
theorem B1507947 : Blo 1506950 1507947 := bstep (se 1 (by rfl) ⟨1130960, by rfl⟩ : syracuseStep 1507947 = 2261921) B2261921
theorem B1507959 : Blo 1506950 1507959 := bstep (se 1 (by rfl) ⟨1130969, by rfl⟩ : syracuseStep 1507959 = 2261939) B2261939
theorem B1507979 : Blo 1506950 1507979 := bstep (se 1 (by rfl) ⟨1130984, by rfl⟩ : syracuseStep 1507979 = 2261969) B2261969
theorem B1507991 : Blo 1506950 1507991 := bstep (se 1 (by rfl) ⟨1130993, by rfl⟩ : syracuseStep 1507991 = 2261987) B2261987
theorem B3392153 : Blo 1506950 3392153 := bstep (se 2 (by rfl) ⟨1272057, by rfl⟩ : syracuseStep 3392153 = 2544115) B2544115
theorem B2261657 : Blo 1506950 2261657 := bstep (se 2 (by rfl) ⟨848121, by rfl⟩ : syracuseStep 2261657 = 1696243) B1696243
theorem B1508011 : Blo 1506950 1508011 := bstep (se 1 (by rfl) ⟨1131008, by rfl⟩ : syracuseStep 1508011 = 2262017) B2262017
theorem B1508023 : Blo 1506950 1508023 := bstep (se 1 (by rfl) ⟨1131017, by rfl⟩ : syracuseStep 1508023 = 2262035) B2262035
theorem B1696459 : Blo 1506950 1696459 := bstep (se 1 (by rfl) ⟨1272344, by rfl⟩ : syracuseStep 1696459 = 2544689) B2544689
theorem B1508043 : Blo 1506950 1508043 := bstep (se 1 (by rfl) ⟨1131032, by rfl⟩ : syracuseStep 1508043 = 2262065) B2262065
theorem B1508055 : Blo 1506950 1508055 := bstep (se 1 (by rfl) ⟨1131041, by rfl⟩ : syracuseStep 1508055 = 2262083) B2262083
theorem B1508075 : Blo 1506950 1508075 := bstep (se 1 (by rfl) ⟨1131056, by rfl⟩ : syracuseStep 1508075 = 2262113) B2262113
theorem B3392243 : Blo 1506950 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B1508087 : Blo 1506950 1508087 := bstep (se 1 (by rfl) ⟨1131065, by rfl⟩ : syracuseStep 1508087 = 2262131) B2262131
theorem B2261771 : Blo 1506950 2261771 := bstep (se 1 (by rfl) ⟨1696328, by rfl⟩ : syracuseStep 2261771 = 3392657) B3392657
theorem B1508107 : Blo 1506950 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B3392279 : Blo 1506950 3392279 := bstep (se 1 (by rfl) ⟨2544209, by rfl⟩ : syracuseStep 3392279 = 5088419) B5088419
theorem B2261783 : Blo 1506950 2261783 := bstep (se 1 (by rfl) ⟨1696337, by rfl⟩ : syracuseStep 2261783 = 3392675) B3392675
theorem B1508119 : Blo 1506950 1508119 := bstep (se 1 (by rfl) ⟨1131089, by rfl⟩ : syracuseStep 1508119 = 2262179) B2262179
theorem B1508139 : Blo 1506950 1508139 := bstep (se 1 (by rfl) ⟨1131104, by rfl⟩ : syracuseStep 1508139 = 2262209) B2262209
theorem B1696567 : Blo 1506950 1696567 := bstep (se 1 (by rfl) ⟨1272425, by rfl⟩ : syracuseStep 1696567 = 2544851) B2544851
theorem B1508151 : Blo 1506950 1508151 := bstep (se 1 (by rfl) ⟨1131113, by rfl⟩ : syracuseStep 1508151 = 2262227) B2262227
theorem B1508171 : Blo 1506950 1508171 := bstep (se 1 (by rfl) ⟨1131128, by rfl⟩ : syracuseStep 1508171 = 2262257) B2262257
theorem B1508183 : Blo 1506950 1508183 := bstep (se 1 (by rfl) ⟨1131137, by rfl⟩ : syracuseStep 1508183 = 2262275) B2262275
theorem B2261849 : Blo 1506950 2261849 := bstep (se 2 (by rfl) ⟨848193, by rfl⟩ : syracuseStep 2261849 = 1696387) B1696387
theorem B1508203 : Blo 1506950 1508203 := bstep (se 1 (by rfl) ⟨1131152, by rfl⟩ : syracuseStep 1508203 = 2262305) B2262305
theorem B1508215 : Blo 1506950 1508215 := bstep (se 1 (by rfl) ⟨1131161, by rfl⟩ : syracuseStep 1508215 = 2262323) B2262323
theorem B1508235 : Blo 1506950 1508235 := bstep (se 1 (by rfl) ⟨1131176, by rfl⟩ : syracuseStep 1508235 = 2262353) B2262353
theorem B1508247 : Blo 1506950 1508247 := bstep (se 1 (by rfl) ⟨1131185, by rfl⟩ : syracuseStep 1508247 = 2262371) B2262371
theorem B1508267 : Blo 1506950 1508267 := bstep (se 1 (by rfl) ⟨1131200, by rfl⟩ : syracuseStep 1508267 = 2262401) B2262401
theorem B1508279 : Blo 1506950 1508279 := bstep (se 1 (by rfl) ⟨1131209, by rfl⟩ : syracuseStep 1508279 = 2262419) B2262419
theorem B5088203 : Blo 1506950 5088203 := bstep (se 1 (by rfl) ⟨3816152, by rfl⟩ : syracuseStep 5088203 = 7632305) B7632305
theorem B3392459 : Blo 1506950 3392459 := bstep (se 1 (by rfl) ⟨2544344, by rfl⟩ : syracuseStep 3392459 = 5088689) B5088689
theorem B2261963 : Blo 1506950 2261963 := bstep (se 1 (by rfl) ⟨1696472, by rfl⟩ : syracuseStep 2261963 = 3392945) B3392945
theorem B1508299 : Blo 1506950 1508299 := bstep (se 1 (by rfl) ⟨1131224, by rfl⟩ : syracuseStep 1508299 = 2262449) B2262449
theorem B2261975 : Blo 1506950 2261975 := bstep (se 1 (by rfl) ⟨1696481, by rfl⟩ : syracuseStep 2261975 = 3392963) B3392963
theorem B1508311 : Blo 1506950 1508311 := bstep (se 1 (by rfl) ⟨1131233, by rfl⟩ : syracuseStep 1508311 = 2262467) B2262467
theorem B1696747 : Blo 1506950 1696747 := bstep (se 1 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 1696747 = 2545121) B2545121
theorem B1508331 : Blo 1506950 1508331 := bstep (se 1 (by rfl) ⟨1131248, by rfl⟩ : syracuseStep 1508331 = 2262497) B2262497
theorem B1508343 : Blo 1506950 1508343 := bstep (se 1 (by rfl) ⟨1131257, by rfl⟩ : syracuseStep 1508343 = 2262515) B2262515
theorem B3392513 : Blo 1506950 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B1508363 : Blo 1506950 1508363 := bstep (se 1 (by rfl) ⟨1131272, by rfl⟩ : syracuseStep 1508363 = 2262545) B2262545
theorem B1508375 : Blo 1506950 1508375 := bstep (se 1 (by rfl) ⟨1131281, by rfl⟩ : syracuseStep 1508375 = 2262563) B2262563
theorem B2262041 : Blo 1506950 2262041 := bstep (se 2 (by rfl) ⟨848265, by rfl⟩ : syracuseStep 2262041 = 1696531) B1696531
theorem B1508395 : Blo 1506950 1508395 := bstep (se 1 (by rfl) ⟨1131296, by rfl⟩ : syracuseStep 1508395 = 2262593) B2262593
theorem B1508407 : Blo 1506950 1508407 := bstep (se 1 (by rfl) ⟨1131305, by rfl⟩ : syracuseStep 1508407 = 2262611) B2262611
theorem B11609153 : Blo 1506950 11609153 := bstep (se 2 (by rfl) ⟨4353432, by rfl⟩ : syracuseStep 11609153 = 8706865) B8706865
theorem B3220555 : Blo 1506950 3220555 := bstep (se 1 (by rfl) ⟨2415416, by rfl⟩ : syracuseStep 3220555 = 4830833) B4830833
theorem B1508427 : Blo 1506950 1508427 := bstep (se 1 (by rfl) ⟨1131320, by rfl⟩ : syracuseStep 1508427 = 2262641) B2262641
theorem B1696855 : Blo 1506950 1696855 := bstep (se 1 (by rfl) ⟨1272641, by rfl⟩ : syracuseStep 1696855 = 2545283) B2545283
theorem B1508439 : Blo 1506950 1508439 := bstep (se 1 (by rfl) ⟨1131329, by rfl⟩ : syracuseStep 1508439 = 2262659) B2262659
theorem B1508459 : Blo 1506950 1508459 := bstep (se 1 (by rfl) ⟨1131344, by rfl⟩ : syracuseStep 1508459 = 2262689) B2262689
theorem B1508471 : Blo 1506950 1508471 := bstep (se 1 (by rfl) ⟨1131353, by rfl⟩ : syracuseStep 1508471 = 2262707) B2262707
theorem B12887171 : Blo 1506950 12887171 := bstep (se 1 (by rfl) ⟨9665378, by rfl⟩ : syracuseStep 12887171 = 19330757) B19330757
theorem B2262155 : Blo 1506950 2262155 := bstep (se 1 (by rfl) ⟨1696616, by rfl⟩ : syracuseStep 2262155 = 3393233) B3393233
theorem B1508491 : Blo 1506950 1508491 := bstep (se 1 (by rfl) ⟨1131368, by rfl⟩ : syracuseStep 1508491 = 2262737) B2262737
theorem B2262167 : Blo 1506950 2262167 := bstep (se 1 (by rfl) ⟨1696625, by rfl⟩ : syracuseStep 2262167 = 3393251) B3393251
theorem B1508503 : Blo 1506950 1508503 := bstep (se 1 (by rfl) ⟨1131377, by rfl⟩ : syracuseStep 1508503 = 2262755) B2262755
theorem B1508523 : Blo 1506950 1508523 := bstep (se 1 (by rfl) ⟨1131392, by rfl⟩ : syracuseStep 1508523 = 2262785) B2262785
theorem B1508535 : Blo 1506950 1508535 := bstep (se 1 (by rfl) ⟨1131401, by rfl⟩ : syracuseStep 1508535 = 2262803) B2262803
theorem B1508555 : Blo 1506950 1508555 := bstep (se 1 (by rfl) ⟨1131416, by rfl⟩ : syracuseStep 1508555 = 2262833) B2262833
theorem B1508567 : Blo 1506950 1508567 := bstep (se 1 (by rfl) ⟨1131425, by rfl⟩ : syracuseStep 1508567 = 2262851) B2262851
theorem B5088473 : Blo 1506950 5088473 := bstep (se 2 (by rfl) ⟨1908177, by rfl⟩ : syracuseStep 5088473 = 3816355) B3816355
theorem B3392729 : Blo 1506950 3392729 := bstep (se 2 (by rfl) ⟨1272273, by rfl⟩ : syracuseStep 3392729 = 2544547) B2544547
theorem B2262233 : Blo 1506950 2262233 := bstep (se 2 (by rfl) ⟨848337, by rfl⟩ : syracuseStep 2262233 = 1696675) B1696675
theorem B5727449 : Blo 1506950 5727449 := bstep (se 2 (by rfl) ⟨2147793, by rfl⟩ : syracuseStep 5727449 = 4295587) B4295587
theorem B1508587 : Blo 1506950 1508587 := bstep (se 1 (by rfl) ⟨1131440, by rfl⟩ : syracuseStep 1508587 = 2262881) B2262881
theorem B1508599 : Blo 1506950 1508599 := bstep (se 1 (by rfl) ⟨1131449, by rfl⟩ : syracuseStep 1508599 = 2262899) B2262899
theorem B1697035 : Blo 1506950 1697035 := bstep (se 1 (by rfl) ⟨1272776, by rfl⟩ : syracuseStep 1697035 = 2545553) B2545553
theorem B1508619 : Blo 1506950 1508619 := bstep (se 1 (by rfl) ⟨1131464, by rfl⟩ : syracuseStep 1508619 = 2262929) B2262929
theorem B1508631 : Blo 1506950 1508631 := bstep (se 1 (by rfl) ⟨1131473, by rfl⟩ : syracuseStep 1508631 = 2262947) B2262947
theorem B1508651 : Blo 1506950 1508651 := bstep (se 1 (by rfl) ⟨1131488, by rfl⟩ : syracuseStep 1508651 = 2262977) B2262977
theorem B3392819 : Blo 1506950 3392819 := bstep (se 1 (by rfl) ⟨2544614, by rfl⟩ : syracuseStep 3392819 = 5089229) B5089229
theorem B1508663 : Blo 1506950 1508663 := bstep (se 1 (by rfl) ⟨1131497, by rfl⟩ : syracuseStep 1508663 = 2262995) B2262995
theorem B2262347 : Blo 1506950 2262347 := bstep (se 1 (by rfl) ⟨1696760, by rfl⟩ : syracuseStep 2262347 = 3393521) B3393521
theorem B1508683 : Blo 1506950 1508683 := bstep (se 1 (by rfl) ⟨1131512, by rfl⟩ : syracuseStep 1508683 = 2263025) B2263025
theorem B3392855 : Blo 1506950 3392855 := bstep (se 1 (by rfl) ⟨2544641, by rfl⟩ : syracuseStep 3392855 = 5089283) B5089283
theorem B2262359 : Blo 1506950 2262359 := bstep (se 1 (by rfl) ⟨1696769, by rfl⟩ : syracuseStep 2262359 = 3393539) B3393539
theorem B1508695 : Blo 1506950 1508695 := bstep (se 1 (by rfl) ⟨1131521, by rfl⟩ : syracuseStep 1508695 = 2263043) B2263043
theorem B5506397 : Blo 1506950 5506397 := bstep (se 3 (by rfl) ⟨1032449, by rfl⟩ : syracuseStep 5506397 = 2064899) B2064899
theorem B1508715 : Blo 1506950 1508715 := bstep (se 1 (by rfl) ⟨1131536, by rfl⟩ : syracuseStep 1508715 = 2263073) B2263073
theorem B1697143 : Blo 1506950 1697143 := bstep (se 1 (by rfl) ⟨1272857, by rfl⟩ : syracuseStep 1697143 = 2545715) B2545715
theorem B1508727 : Blo 1506950 1508727 := bstep (se 1 (by rfl) ⟨1131545, by rfl⟩ : syracuseStep 1508727 = 2263091) B2263091
theorem B13239683 : Blo 1506950 13239683 := bstep (se 1 (by rfl) ⟨9929762, by rfl⟩ : syracuseStep 13239683 = 19859525) B19859525
theorem B7636355 : Blo 1506950 7636355 := bstep (se 1 (by rfl) ⟨5727266, by rfl⟩ : syracuseStep 7636355 = 11454533) B11454533
theorem B1508747 : Blo 1506950 1508747 := bstep (se 1 (by rfl) ⟨1131560, by rfl⟩ : syracuseStep 1508747 = 2263121) B2263121
theorem B1508759 : Blo 1506950 1508759 := bstep (se 1 (by rfl) ⟨1131569, by rfl⟩ : syracuseStep 1508759 = 2263139) B2263139
theorem B2262425 : Blo 1506950 2262425 := bstep (se 2 (by rfl) ⟨848409, by rfl⟩ : syracuseStep 2262425 = 1696819) B1696819
theorem B2147737 : Blo 1506950 2147737 := bstep (se 2 (by rfl) ⟨805401, by rfl⟩ : syracuseStep 2147737 = 1610803) B1610803
theorem B1508779 : Blo 1506950 1508779 := bstep (se 1 (by rfl) ⟨1131584, by rfl⟩ : syracuseStep 1508779 = 2263169) B2263169
theorem B3974579 : Blo 1506950 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B1508791 : Blo 1506950 1508791 := bstep (se 1 (by rfl) ⟨1131593, by rfl⟩ : syracuseStep 1508791 = 2263187) B2263187
theorem B1508811 : Blo 1506950 1508811 := bstep (se 1 (by rfl) ⟨1131608, by rfl⟩ : syracuseStep 1508811 = 2263217) B2263217
theorem B1508823 : Blo 1506950 1508823 := bstep (se 1 (by rfl) ⟨1131617, by rfl⟩ : syracuseStep 1508823 = 2263235) B2263235
theorem B10315225 : Blo 1506950 10315225 := bstep (se 2 (by rfl) ⟨3868209, by rfl⟩ : syracuseStep 10315225 = 7736419) B7736419
theorem B1508843 : Blo 1506950 1508843 := bstep (se 1 (by rfl) ⟨1131632, by rfl⟩ : syracuseStep 1508843 = 2263265) B2263265
theorem B1508855 : Blo 1506950 1508855 := bstep (se 1 (by rfl) ⟨1131641, by rfl⟩ : syracuseStep 1508855 = 2263283) B2263283
theorem B12396037 : Blo 1506950 12396037 := bstep (se 4 (by rfl) ⟨1162128, by rfl⟩ : syracuseStep 12396037 = 2324257) B2324257
theorem B3393035 : Blo 1506950 3393035 := bstep (se 1 (by rfl) ⟨2544776, by rfl⟩ : syracuseStep 3393035 = 5089553) B5089553
theorem B2262539 : Blo 1506950 2262539 := bstep (se 1 (by rfl) ⟨1696904, by rfl⟩ : syracuseStep 2262539 = 3393809) B3393809
theorem B1508875 : Blo 1506950 1508875 := bstep (se 1 (by rfl) ⟨1131656, by rfl⟩ : syracuseStep 1508875 = 2263313) B2263313
theorem B2262551 : Blo 1506950 2262551 := bstep (se 1 (by rfl) ⟨1696913, by rfl⟩ : syracuseStep 2262551 = 3393827) B3393827
theorem B1508887 : Blo 1506950 1508887 := bstep (se 1 (by rfl) ⟨1131665, by rfl⟩ : syracuseStep 1508887 = 2263331) B2263331
theorem B1697323 : Blo 1506950 1697323 := bstep (se 1 (by rfl) ⟨1272992, by rfl⟩ : syracuseStep 1697323 = 2545985) B2545985
theorem B1508907 : Blo 1506950 1508907 := bstep (se 1 (by rfl) ⟨1131680, by rfl⟩ : syracuseStep 1508907 = 2263361) B2263361
theorem B3819059 : Blo 1506950 3819059 := bstep (se 1 (by rfl) ⟨2864294, by rfl⟩ : syracuseStep 3819059 = 5728589) B5728589
theorem B1508919 : Blo 1506950 1508919 := bstep (se 1 (by rfl) ⟨1131689, by rfl⟩ : syracuseStep 1508919 = 2263379) B2263379
theorem B3393089 : Blo 1506950 3393089 := bstep (se 2 (by rfl) ⟨1272408, by rfl⟩ : syracuseStep 3393089 = 2544817) B2544817
theorem B1508939 : Blo 1506950 1508939 := bstep (se 1 (by rfl) ⟨1131704, by rfl⟩ : syracuseStep 1508939 = 2263409) B2263409
theorem B2262617 : Blo 1506950 2262617 := bstep (se 2 (by rfl) ⟨848481, by rfl⟩ : syracuseStep 2262617 = 1696963) B1696963
theorem B6440579 : Blo 1506950 6440579 := bstep (se 1 (by rfl) ⟨4830434, by rfl⟩ : syracuseStep 6440579 = 9660869) B9660869
theorem B1697431 : Blo 1506950 1697431 := bstep (se 1 (by rfl) ⟨1273073, by rfl⟩ : syracuseStep 1697431 = 2546147) B2546147
theorem B2262731 : Blo 1506950 2262731 := bstep (se 1 (by rfl) ⟨1697048, by rfl⟩ : syracuseStep 2262731 = 3394097) B3394097
theorem B2262743 : Blo 1506950 2262743 := bstep (se 1 (by rfl) ⟨1697057, by rfl⟩ : syracuseStep 2262743 = 3394115) B3394115
theorem B7243481 : Blo 1506950 7243481 := bstep (se 2 (by rfl) ⟨2716305, by rfl⟩ : syracuseStep 7243481 = 5432611) B5432611
theorem B3393305 : Blo 1506950 3393305 := bstep (se 2 (by rfl) ⟨1272489, by rfl⟩ : syracuseStep 3393305 = 2544979) B2544979
theorem B2262809 : Blo 1506950 2262809 := bstep (se 2 (by rfl) ⟨848553, by rfl⟩ : syracuseStep 2262809 = 1697107) B1697107
theorem B8587073 : Blo 1506950 8587073 := bstep (se 2 (by rfl) ⟨3220152, by rfl⟩ : syracuseStep 8587073 = 6440305) B6440305
theorem B2860915 : Blo 1506950 2860915 := bstep (se 1 (by rfl) ⟨2145686, by rfl⟩ : syracuseStep 2860915 = 4291373) B4291373
theorem B3393395 : Blo 1506950 3393395 := bstep (se 1 (by rfl) ⟨2545046, by rfl⟩ : syracuseStep 3393395 = 5090093) B5090093
theorem B2262923 : Blo 1506950 2262923 := bstep (se 1 (by rfl) ⟨1697192, by rfl⟩ : syracuseStep 2262923 = 3394385) B3394385
theorem B5089175 : Blo 1506950 5089175 := bstep (se 1 (by rfl) ⟨3816881, by rfl⟩ : syracuseStep 5089175 = 7633763) B7633763
theorem B3393431 : Blo 1506950 3393431 := bstep (se 1 (by rfl) ⟨2545073, by rfl⟩ : syracuseStep 3393431 = 5090147) B5090147
theorem B2262935 : Blo 1506950 2262935 := bstep (se 1 (by rfl) ⟨1697201, by rfl⟩ : syracuseStep 2262935 = 3394403) B3394403
theorem B6440921 : Blo 1506950 6440921 := bstep (se 2 (by rfl) ⟨2415345, by rfl⟩ : syracuseStep 6440921 = 4830691) B4830691
theorem B2263001 : Blo 1506950 2263001 := bstep (se 2 (by rfl) ⟨848625, by rfl⟩ : syracuseStep 2263001 = 1697251) B1697251
theorem B4294721 : Blo 1506950 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B5433419 : Blo 1506950 5433419 := bstep (se 1 (by rfl) ⟨4075064, by rfl⟩ : syracuseStep 5433419 = 8150129) B8150129
theorem B3393611 : Blo 1506950 3393611 := bstep (se 1 (by rfl) ⟨2545208, by rfl⟩ : syracuseStep 3393611 = 5090417) B5090417
theorem B2263115 : Blo 1506950 2263115 := bstep (se 1 (by rfl) ⟨1697336, by rfl⟩ : syracuseStep 2263115 = 3394673) B3394673
theorem B2263127 : Blo 1506950 2263127 := bstep (se 1 (by rfl) ⟨1697345, by rfl⟩ : syracuseStep 2263127 = 3394691) B3394691
theorem B4294745 : Blo 1506950 4294745 := bstep (se 2 (by rfl) ⟨1610529, by rfl⟩ : syracuseStep 4294745 = 3221059) B3221059
theorem B3393665 : Blo 1506950 3393665 := bstep (se 2 (by rfl) ⟨1272624, by rfl⟩ : syracuseStep 3393665 = 2545249) B2545249
theorem B2263193 : Blo 1506950 2263193 := bstep (se 2 (by rfl) ⟨848697, by rfl⟩ : syracuseStep 2263193 = 1697395) B1697395
theorem B12880133 : Blo 1506950 12880133 := bstep (se 4 (by rfl) ⟨1207512, by rfl⟩ : syracuseStep 12880133 = 2415025) B2415025
theorem B2263307 : Blo 1506950 2263307 := bstep (se 1 (by rfl) ⟨1697480, by rfl⟩ : syracuseStep 2263307 = 3394961) B3394961
theorem B2263319 : Blo 1506950 2263319 := bstep (se 1 (by rfl) ⟨1697489, by rfl⟩ : syracuseStep 2263319 = 3394979) B3394979
theorem B3221785 : Blo 1506950 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B2861401 : Blo 1506950 2861401 := bstep (se 2 (by rfl) ⟨1073025, by rfl⟩ : syracuseStep 2861401 = 2146051) B2146051
theorem B3393881 : Blo 1506950 3393881 := bstep (se 2 (by rfl) ⟨1272705, by rfl⟩ : syracuseStep 3393881 = 2545411) B2545411
theorem B2263385 : Blo 1506950 2263385 := bstep (se 2 (by rfl) ⟨848769, by rfl⟩ : syracuseStep 2263385 = 1697539) B1697539
theorem B5089715 : Blo 1506950 5089715 := bstep (se 1 (by rfl) ⟨3817286, by rfl⟩ : syracuseStep 5089715 = 7634573) B7634573
theorem B3393971 : Blo 1506950 3393971 := bstep (se 1 (by rfl) ⟨2545478, by rfl⟩ : syracuseStep 3393971 = 5090957) B5090957
theorem B3394007 : Blo 1506950 3394007 := bstep (se 1 (by rfl) ⟨2545505, by rfl⟩ : syracuseStep 3394007 = 5091011) B5091011
theorem B7735769 : Blo 1506950 7735769 := bstep (se 2 (by rfl) ⟨2900913, by rfl⟩ : syracuseStep 7735769 = 5801827) B5801827
theorem B6875741 : Blo 1506950 6875741 := bstep (se 3 (by rfl) ⟨1289201, by rfl⟩ : syracuseStep 6875741 = 2578403) B2578403
theorem B3394187 : Blo 1506950 3394187 := bstep (se 1 (by rfl) ⟨2545640, by rfl⟩ : syracuseStep 3394187 = 5091281) B5091281
theorem B5089985 : Blo 1506950 5089985 := bstep (se 2 (by rfl) ⟨1908744, by rfl⟩ : syracuseStep 5089985 = 3817489) B3817489
theorem B3394241 : Blo 1506950 3394241 := bstep (se 2 (by rfl) ⟨1272840, by rfl⟩ : syracuseStep 3394241 = 2545681) B2545681
theorem B3263257 : Blo 1506950 3263257 := bstep (se 2 (by rfl) ⟨1223721, by rfl⟩ : syracuseStep 3263257 = 2447443) B2447443
theorem B5729075 : Blo 1506950 5729075 := bstep (se 1 (by rfl) ⟨4296806, by rfl⟩ : syracuseStep 5729075 = 8593613) B8593613
theorem B5729089 : Blo 1506950 5729089 := bstep (se 2 (by rfl) ⟨2148408, by rfl⟩ : syracuseStep 5729089 = 4296817) B4296817
theorem B2861963 : Blo 1506950 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B3394457 : Blo 1506950 3394457 := bstep (se 2 (by rfl) ⟨1272921, by rfl⟩ : syracuseStep 3394457 = 2545843) B2545843
theorem B5155763 : Blo 1506950 5155763 := bstep (se 1 (by rfl) ⟨3866822, by rfl⟩ : syracuseStep 5155763 = 7733645) B7733645
theorem B3394547 : Blo 1506950 3394547 := bstep (se 1 (by rfl) ⟨2545910, by rfl⟩ : syracuseStep 3394547 = 5091821) B5091821
theorem B11455505 : Blo 1506950 11455505 := bstep (se 2 (by rfl) ⟨4295814, by rfl⟩ : syracuseStep 11455505 = 8591629) B8591629
theorem B3394583 : Blo 1506950 3394583 := bstep (se 1 (by rfl) ⟨2545937, by rfl⟩ : syracuseStep 3394583 = 5091875) B5091875
theorem B2862145 : Blo 1506950 2862145 := bstep (se 2 (by rfl) ⟨1073304, by rfl⟩ : syracuseStep 2862145 = 2146609) B2146609
theorem B5508269 : Blo 1506950 5508269 := bstep (se 3 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 5508269 = 2065601) B2065601
theorem B46402741 : Blo 1506950 46402741 := bstep (se 5 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 46402741 = 4350257) B4350257
theorem B3394763 : Blo 1506950 3394763 := bstep (se 1 (by rfl) ⟨2546072, by rfl⟩ : syracuseStep 3394763 = 5092145) B5092145
theorem B5090525 : Blo 1506950 5090525 := bstep (se 3 (by rfl) ⟨954473, by rfl⟩ : syracuseStep 5090525 = 1908947) B1908947
theorem B3394817 : Blo 1506950 3394817 := bstep (se 2 (by rfl) ⟨1273056, by rfl⟩ : syracuseStep 3394817 = 2546113) B2546113
theorem B12225809 : Blo 1506950 12225809 := bstep (se 2 (by rfl) ⟨4584678, by rfl⟩ : syracuseStep 12225809 = 9169357) B9169357
theorem B4295987 : Blo 1506950 4295987 := bstep (se 1 (by rfl) ⟨3221990, by rfl⟩ : syracuseStep 4295987 = 6443981) B6443981
theorem B25767233 : Blo 1506950 25767233 := bstep (se 2 (by rfl) ⟨9662712, by rfl⟩ : syracuseStep 25767233 = 19325425) B19325425
theorem B10874243 : Blo 1506950 10874243 := bstep (se 1 (by rfl) ⟨8155682, by rfl⟩ : syracuseStep 10874243 = 16311365) B16311365
theorem B11447729 : Blo 1506950 11447729 := bstep (se 2 (by rfl) ⟨4292898, by rfl⟩ : syracuseStep 11447729 = 8585797) B8585797
theorem B3395033 : Blo 1506950 3395033 := bstep (se 2 (by rfl) ⟨1273137, by rfl⟩ : syracuseStep 3395033 = 2546275) B2546275
theorem B4075031 : Blo 1506950 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B5434931 : Blo 1506950 5434931 := bstep (se 1 (by rfl) ⟨4076198, by rfl⟩ : syracuseStep 5434931 = 8152397) B8152397
theorem B3395123 : Blo 1506950 3395123 := bstep (se 1 (by rfl) ⟨2546342, by rfl⟩ : syracuseStep 3395123 = 5092685) B5092685
theorem B1609355 : Blo 1506950 1609355 := bstep (se 1 (by rfl) ⟨1207016, by rfl⟩ : syracuseStep 1609355 = 2414033) B2414033
theorem B17895173 : Blo 1506950 17895173 := bstep (se 4 (by rfl) ⟨1677672, by rfl⟩ : syracuseStep 17895173 = 3355345) B3355345
theorem B2862859 : Blo 1506950 2862859 := bstep (se 1 (by rfl) ⟨2147144, by rfl⟩ : syracuseStep 2862859 = 4294289) B4294289
theorem B17182529 : Blo 1506950 17182529 := bstep (se 2 (by rfl) ⟨6443448, by rfl⟩ : syracuseStep 17182529 = 12886897) B12886897
theorem B2543447 : Blo 1506950 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B2862935 : Blo 1506950 2862935 := bstep (se 1 (by rfl) ⟨2147201, by rfl⟩ : syracuseStep 2862935 = 4294403) B4294403
theorem B7630685 : Blo 1506950 7630685 := bstep (se 3 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 7630685 = 2861507) B2861507
theorem B11448215 : Blo 1506950 11448215 := bstep (se 1 (by rfl) ⟨8586161, by rfl⟩ : syracuseStep 11448215 = 17172323) B17172323
theorem B2543575 : Blo 1506950 2543575 := bstep (se 1 (by rfl) ⟨1907681, by rfl⟩ : syracuseStep 2543575 = 3815363) B3815363
theorem B5722073 : Blo 1506950 5722073 := bstep (se 2 (by rfl) ⟨2145777, by rfl⟩ : syracuseStep 5722073 = 4291555) B4291555
theorem B4190231 : Blo 1506950 4190231 := bstep (se 1 (by rfl) ⟨3142673, by rfl⟩ : syracuseStep 4190231 = 6285347) B6285347
theorem B5722285 : Blo 1506950 5722285 := bstep (se 3 (by rfl) ⟨1072928, by rfl⟩ : syracuseStep 5722285 = 2145857) B2145857
theorem B12874049 : Blo 1506950 12874049 := bstep (se 2 (by rfl) ⟨4827768, by rfl⟩ : syracuseStep 12874049 = 9655537) B9655537
theorem B27521345 : Blo 1506950 27521345 := bstep (se 2 (by rfl) ⟨10320504, by rfl⟩ : syracuseStep 27521345 = 20641009) B20641009
theorem B5091659 : Blo 1506950 5091659 := bstep (se 1 (by rfl) ⟨3818744, by rfl⟩ : syracuseStep 5091659 = 7637489) B7637489
theorem B5722589 : Blo 1506950 5722589 := bstep (se 3 (by rfl) ⟨1072985, by rfl⟩ : syracuseStep 5722589 = 2145971) B2145971
theorem B2863603 : Blo 1506950 2863603 := bstep (se 1 (by rfl) ⟨2147702, by rfl⟩ : syracuseStep 2863603 = 4295405) B4295405
theorem B10875397 : Blo 1506950 10875397 := bstep (se 4 (by rfl) ⟨1019568, by rfl⟩ : syracuseStep 10875397 = 2039137) B2039137
theorem B2544203 : Blo 1506950 2544203 := bstep (se 1 (by rfl) ⟨1908152, by rfl⟩ : syracuseStep 2544203 = 3816305) B3816305
theorem B2716249 : Blo 1506950 2716249 := bstep (se 2 (by rfl) ⟨1018593, by rfl⟩ : syracuseStep 2716249 = 2037187) B2037187
theorem B5091929 : Blo 1506950 5091929 := bstep (se 2 (by rfl) ⟨1909473, by rfl⟩ : syracuseStep 5091929 = 3818947) B3818947
theorem B9196183 : Blo 1506950 9196183 := bstep (se 1 (by rfl) ⟨6897137, by rfl⟩ : syracuseStep 9196183 = 13794275) B13794275
theorem B2544331 : Blo 1506950 2544331 := bstep (se 1 (by rfl) ⟨1908248, by rfl⟩ : syracuseStep 2544331 = 3816497) B3816497
theorem B2863831 : Blo 1506950 2863831 := bstep (se 1 (by rfl) ⟨2147873, by rfl⟩ : syracuseStep 2863831 = 4295747) B4295747
theorem B1610551 : Blo 1506950 1610551 := bstep (se 1 (by rfl) ⟨1207913, by rfl⟩ : syracuseStep 1610551 = 2415827) B2415827
theorem B2863937 : Blo 1506950 2863937 := bstep (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) B2147953
theorem B2544473 : Blo 1506950 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B17642417 : Blo 1506950 17642417 := bstep (se 2 (by rfl) ⟨6615906, by rfl⟩ : syracuseStep 17642417 = 13231813) B13231813
theorem B2544601 : Blo 1506950 2544601 := bstep (se 2 (by rfl) ⟨954225, by rfl⟩ : syracuseStep 2544601 = 1908451) B1908451
theorem B2864089 : Blo 1506950 2864089 := bstep (se 2 (by rfl) ⟨1074033, by rfl⟩ : syracuseStep 2864089 = 2148067) B2148067
theorem B36705241 : Blo 1506950 36705241 := bstep (se 2 (by rfl) ⟨13764465, by rfl⟩ : syracuseStep 36705241 = 27528931) B27528931
theorem B14496803 : Blo 1506950 14496803 := bstep (se 1 (by rfl) ⟨10872602, by rfl⟩ : syracuseStep 14496803 = 21745205) B21745205
theorem B18600995 : Blo 1506950 18600995 := bstep (se 1 (by rfl) ⟨13950746, by rfl⟩ : syracuseStep 18600995 = 27901493) B27901493
theorem B9663533 : Blo 1506950 9663533 := bstep (se 3 (by rfl) ⟨1811912, by rfl⟩ : syracuseStep 9663533 = 3623825) B3623825
theorem B6616153 : Blo 1506950 6616153 := bstep (se 2 (by rfl) ⟨2481057, by rfl⟩ : syracuseStep 6616153 = 4962115) B4962115
theorem B6444305 : Blo 1506950 6444305 := bstep (se 2 (by rfl) ⟨2416614, by rfl⟩ : syracuseStep 6444305 = 4833229) B4833229
theorem B5092631 : Blo 1506950 5092631 := bstep (se 1 (by rfl) ⟨3819473, by rfl⟩ : syracuseStep 5092631 = 7638947) B7638947
theorem B24466789 : Blo 1506950 24466789 := bstep (se 4 (by rfl) ⟨2293761, by rfl⟩ : syracuseStep 24466789 = 4587523) B4587523
theorem B2545175 : Blo 1506950 2545175 := bstep (se 1 (by rfl) ⟨1908881, by rfl⟩ : syracuseStep 2545175 = 3817763) B3817763
theorem B1570379 : Blo 1506950 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B4077149 : Blo 1506950 4077149 := bstep (se 3 (by rfl) ⟨764465, by rfl⟩ : syracuseStep 4077149 = 1528931) B1528931
theorem B2545303 : Blo 1506950 2545303 := bstep (se 1 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 2545303 = 3817955) B3817955
theorem B10319633 : Blo 1506950 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B2414423 : Blo 1506950 2414423 := bstep (se 1 (by rfl) ⟨1810817, by rfl⟩ : syracuseStep 2414423 = 3621635) B3621635
theorem B48887651 : Blo 1506950 48887651 := bstep (se 1 (by rfl) ⟨36665738, by rfl⟩ : syracuseStep 48887651 = 73331477) B73331477
theorem B7632791 : Blo 1506950 7632791 := bstep (se 1 (by rfl) ⟨5724593, by rfl⟩ : syracuseStep 7632791 = 11449187) B11449187
theorem B16299953 : Blo 1506950 16299953 := bstep (se 2 (by rfl) ⟨6112482, by rfl⟩ : syracuseStep 16299953 = 12224965) B12224965
theorem B2717633 : Blo 1506950 2717633 := bstep (se 2 (by rfl) ⟨1019112, by rfl⟩ : syracuseStep 2717633 = 2038225) B2038225
theorem B2414551 : Blo 1506950 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B6445021 : Blo 1506950 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B2414615 : Blo 1506950 2414615 := bstep (se 1 (by rfl) ⟨1810961, by rfl⟩ : syracuseStep 2414615 = 3621923) B3621923
theorem B49559627 : Blo 1506950 49559627 := bstep (se 1 (by rfl) ⟨37169720, by rfl⟩ : syracuseStep 49559627 = 74339441) B74339441
theorem B6437009 : Blo 1506950 6437009 := bstep (se 2 (by rfl) ⟨2413878, by rfl⟩ : syracuseStep 6437009 = 4827757) B4827757
theorem B2545931 : Blo 1506950 2545931 := bstep (se 1 (by rfl) ⟨1909448, by rfl⟩ : syracuseStep 2545931 = 3818897) B3818897
theorem B6117707 : Blo 1506950 6117707 := bstep (se 1 (by rfl) ⟨4588280, by rfl⟩ : syracuseStep 6117707 = 9176561) B9176561
theorem B2546059 : Blo 1506950 2546059 := bstep (se 1 (by rfl) ⟨1909544, by rfl⟩ : syracuseStep 2546059 = 3819089) B3819089
theorem B2546201 : Blo 1506950 2546201 := bstep (se 2 (by rfl) ⟨954825, by rfl⟩ : syracuseStep 2546201 = 1909651) B1909651
theorem B3816011 : Blo 1506950 3816011 := bstep (se 1 (by rfl) ⟨2862008, by rfl⟩ : syracuseStep 3816011 = 5724017) B5724017
theorem B9165413 : Blo 1506950 9165413 := bstep (se 4 (by rfl) ⟨859257, by rfl⟩ : syracuseStep 9165413 = 1718515) B1718515
theorem B21740183 : Blo 1506950 21740183 := bstep (se 1 (by rfl) ⟨16305137, by rfl⟩ : syracuseStep 21740183 = 32610275) B32610275
theorem B2546329 : Blo 1506950 2546329 := bstep (se 2 (by rfl) ⟨954873, by rfl⟩ : syracuseStep 2546329 = 1909747) B1909747
theorem B1907479 : Blo 1506950 1907479 := bstep (se 1 (by rfl) ⟨1430609, by rfl⟩ : syracuseStep 1907479 = 2861219) B2861219
theorem B4832075 : Blo 1506950 4832075 := bstep (se 1 (by rfl) ⟨3624056, by rfl⟩ : syracuseStep 4832075 = 7248113) B7248113
theorem B18840437 : Blo 1506950 18840437 := bstep (se 5 (by rfl) ⟨883145, by rfl⟩ : syracuseStep 18840437 = 1766291) B1766291
theorem B11475929 : Blo 1506950 11475929 := bstep (se 2 (by rfl) ⟨4303473, by rfl⟩ : syracuseStep 11475929 = 8606947) B8606947
theorem B3439577 : Blo 1506950 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B5725187 : Blo 1506950 5725187 := bstep (se 1 (by rfl) ⟨4293890, by rfl⟩ : syracuseStep 5725187 = 8587781) B8587781
theorem B5725201 : Blo 1506950 5725201 := bstep (se 2 (by rfl) ⟨2146950, by rfl⟩ : syracuseStep 5725201 = 4293901) B4293901
theorem B61905941 : Blo 1506950 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B5086259 : Blo 1506950 5086259 := bstep (se 1 (by rfl) ⟨3814694, by rfl⟩ : syracuseStep 5086259 = 7629389) B7629389
theorem B10869835 : Blo 1506950 10869835 := bstep (se 1 (by rfl) ⟨8152376, by rfl⟩ : syracuseStep 10869835 = 16304753) B16304753
theorem B6437981 : Blo 1506950 6437981 := bstep (se 3 (by rfl) ⟨1207121, by rfl⟩ : syracuseStep 6437981 = 2414243) B2414243
theorem B4832473 : Blo 1506950 4832473 := bstep (se 2 (by rfl) ⟨1812177, by rfl⟩ : syracuseStep 4832473 = 3624355) B3624355
theorem B2718937 : Blo 1506950 2718937 := bstep (se 2 (by rfl) ⟨1019601, by rfl⟩ : syracuseStep 2718937 = 2039203) B2039203
theorem B4291805 : Blo 1506950 4291805 := bstep (se 3 (by rfl) ⟨804713, by rfl⟩ : syracuseStep 4291805 = 1609427) B1609427
theorem B3390731 : Blo 1506950 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B3390785 : Blo 1506950 3390785 := bstep (se 2 (by rfl) ⟨1271544, by rfl⟩ : syracuseStep 3390785 = 2543089) B2543089
theorem B5086529 : Blo 1506950 5086529 := bstep (se 2 (by rfl) ⟨1907448, by rfl⟩ : syracuseStep 5086529 = 3814897) B3814897
theorem B22027585 : Blo 1506950 22027585 := bstep (se 2 (by rfl) ⟨8260344, by rfl⟩ : syracuseStep 22027585 = 16520689) B16520689
theorem B5725505 : Blo 1506950 5725505 := bstep (se 2 (by rfl) ⟨2147064, by rfl⟩ : syracuseStep 5725505 = 4294129) B4294129
theorem B2260427 : Blo 1506950 2260427 := bstep (se 1 (by rfl) ⟨1695320, by rfl⟩ : syracuseStep 2260427 = 3390641) B3390641
theorem B2260439 : Blo 1506950 2260439 := bstep (se 1 (by rfl) ⟨1695329, by rfl⟩ : syracuseStep 2260439 = 3390659) B3390659
theorem B3816983 : Blo 1506950 3816983 := bstep (se 1 (by rfl) ⟨2862737, by rfl⟩ : syracuseStep 3816983 = 5725475) B5725475
theorem B2260505 : Blo 1506950 2260505 := bstep (se 2 (by rfl) ⟨847689, by rfl⟩ : syracuseStep 2260505 = 1695379) B1695379
theorem B3391001 : Blo 1506950 3391001 := bstep (se 2 (by rfl) ⟨1271625, by rfl⟩ : syracuseStep 3391001 = 2543251) B2543251
theorem B1908299 : Blo 1506950 1908299 := bstep (se 1 (by rfl) ⟨1431224, by rfl⟩ : syracuseStep 1908299 = 2862449) B2862449
theorem B3391091 : Blo 1506950 3391091 := bstep (se 1 (by rfl) ⟨2543318, by rfl⟩ : syracuseStep 3391091 = 5086637) B5086637
theorem B3219059 : Blo 1506950 3219059 := bstep (se 1 (by rfl) ⟨2414294, by rfl⟩ : syracuseStep 3219059 = 4828589) B4828589
theorem B1506955 : Blo 1506950 1506955 := bstep (se 1 (by rfl) ⟨1130216, by rfl⟩ : syracuseStep 1506955 = 2260433) B2260433
theorem B2260619 : Blo 1506950 2260619 := bstep (se 1 (by rfl) ⟨1695464, by rfl⟩ : syracuseStep 2260619 = 3390929) B3390929
theorem B1506967 : Blo 1506950 1506967 := bstep (se 1 (by rfl) ⟨1130225, by rfl⟩ : syracuseStep 1506967 = 2260451) B2260451
theorem B2260631 : Blo 1506950 2260631 := bstep (se 1 (by rfl) ⟨1695473, by rfl⟩ : syracuseStep 2260631 = 3390947) B3390947
theorem B2145943 : Blo 1506950 2145943 := bstep (se 1 (by rfl) ⟨1609457, by rfl⟩ : syracuseStep 2145943 = 3218915) B3218915
theorem B3391127 : Blo 1506950 3391127 := bstep (se 1 (by rfl) ⟨2543345, by rfl⟩ : syracuseStep 3391127 = 5086691) B5086691
theorem B1506987 : Blo 1506950 1506987 := bstep (se 1 (by rfl) ⟨1130240, by rfl⟩ : syracuseStep 1506987 = 2260481) B2260481
theorem B1506999 : Blo 1506950 1506999 := bstep (se 1 (by rfl) ⟨1130249, by rfl⟩ : syracuseStep 1506999 = 2260499) B2260499
theorem B1695415 : Blo 1506950 1695415 := bstep (se 1 (by rfl) ⟨1271561, by rfl⟩ : syracuseStep 1695415 = 2543123) B2543123
theorem B1507019 : Blo 1506950 1507019 := bstep (se 1 (by rfl) ⟨1130264, by rfl⟩ : syracuseStep 1507019 = 2260529) B2260529
theorem B1507031 : Blo 1506950 1507031 := bstep (se 1 (by rfl) ⟨1130273, by rfl⟩ : syracuseStep 1507031 = 2260547) B2260547
theorem B2260697 : Blo 1506950 2260697 := bstep (se 2 (by rfl) ⟨847761, by rfl⟩ : syracuseStep 2260697 = 1695523) B1695523
theorem B1507051 : Blo 1506950 1507051 := bstep (se 1 (by rfl) ⟨1130288, by rfl⟩ : syracuseStep 1507051 = 2260577) B2260577
theorem B1507063 : Blo 1506950 1507063 := bstep (se 1 (by rfl) ⟨1130297, by rfl⟩ : syracuseStep 1507063 = 2260595) B2260595
theorem B1507083 : Blo 1506950 1507083 := bstep (se 1 (by rfl) ⟨1130312, by rfl⟩ : syracuseStep 1507083 = 2260625) B2260625
theorem B1507095 : Blo 1506950 1507095 := bstep (se 1 (by rfl) ⟨1130321, by rfl⟩ : syracuseStep 1507095 = 2260643) B2260643
theorem B1507115 : Blo 1506950 1507115 := bstep (se 1 (by rfl) ⟨1130336, by rfl⟩ : syracuseStep 1507115 = 2260673) B2260673
theorem B1507127 : Blo 1506950 1507127 := bstep (se 1 (by rfl) ⟨1130345, by rfl⟩ : syracuseStep 1507127 = 2260691) B2260691
theorem B14491457 : Blo 1506950 14491457 := bstep (se 2 (by rfl) ⟨5434296, by rfl⟩ : syracuseStep 14491457 = 10868593) B10868593
theorem B1507147 : Blo 1506950 1507147 := bstep (se 1 (by rfl) ⟨1130360, by rfl⟩ : syracuseStep 1507147 = 2260721) B2260721
theorem B2260811 : Blo 1506950 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B3391307 : Blo 1506950 3391307 := bstep (se 1 (by rfl) ⟨2543480, by rfl⟩ : syracuseStep 3391307 = 5086961) B5086961
theorem B1507159 : Blo 1506950 1507159 := bstep (se 1 (by rfl) ⟨1130369, by rfl⟩ : syracuseStep 1507159 = 2260739) B2260739
theorem B2260823 : Blo 1506950 2260823 := bstep (se 1 (by rfl) ⟨1695617, by rfl⟩ : syracuseStep 2260823 = 3391235) B3391235
theorem B5087069 : Blo 1506950 5087069 := bstep (se 3 (by rfl) ⟨953825, by rfl⟩ : syracuseStep 5087069 = 1907651) B1907651
theorem B1507179 : Blo 1506950 1507179 := bstep (se 1 (by rfl) ⟨1130384, by rfl⟩ : syracuseStep 1507179 = 2260769) B2260769
theorem B1695595 : Blo 1506950 1695595 := bstep (se 1 (by rfl) ⟨1271696, by rfl⟩ : syracuseStep 1695595 = 2543393) B2543393
theorem B1507191 : Blo 1506950 1507191 := bstep (se 1 (by rfl) ⟨1130393, by rfl⟩ : syracuseStep 1507191 = 2260787) B2260787
theorem B3391361 : Blo 1506950 3391361 := bstep (se 2 (by rfl) ⟨1271760, by rfl⟩ : syracuseStep 3391361 = 2543521) B2543521
theorem B1507211 : Blo 1506950 1507211 := bstep (se 1 (by rfl) ⟨1130408, by rfl⟩ : syracuseStep 1507211 = 2260817) B2260817
theorem B1507223 : Blo 1506950 1507223 := bstep (se 1 (by rfl) ⟨1130417, by rfl⟩ : syracuseStep 1507223 = 2260835) B2260835
theorem B2260889 : Blo 1506950 2260889 := bstep (se 2 (by rfl) ⟨847833, by rfl⟩ : syracuseStep 2260889 = 1695667) B1695667
theorem B1507243 : Blo 1506950 1507243 := bstep (se 1 (by rfl) ⟨1130432, by rfl⟩ : syracuseStep 1507243 = 2260865) B2260865
theorem B28983217 : Blo 1506950 28983217 := bstep (se 2 (by rfl) ⟨10868706, by rfl⟩ : syracuseStep 28983217 = 21737413) B21737413
theorem B1507255 : Blo 1506950 1507255 := bstep (se 1 (by rfl) ⟨1130441, by rfl⟩ : syracuseStep 1507255 = 2260883) B2260883
theorem B1507275 : Blo 1506950 1507275 := bstep (se 1 (by rfl) ⟨1130456, by rfl⟩ : syracuseStep 1507275 = 2260913) B2260913
theorem B1507287 : Blo 1506950 1507287 := bstep (se 1 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 1507287 = 2260931) B2260931
theorem B1695703 : Blo 1506950 1695703 := bstep (se 1 (by rfl) ⟨1271777, by rfl⟩ : syracuseStep 1695703 = 2543555) B2543555
theorem B2416601 : Blo 1506950 2416601 := bstep (se 2 (by rfl) ⟨906225, by rfl⟩ : syracuseStep 2416601 = 1812451) B1812451
theorem B5726173 : Blo 1506950 5726173 := bstep (se 3 (by rfl) ⟨1073657, by rfl⟩ : syracuseStep 5726173 = 2147315) B2147315
theorem B1507307 : Blo 1506950 1507307 := bstep (se 1 (by rfl) ⟨1130480, by rfl⟩ : syracuseStep 1507307 = 2260961) B2260961
theorem B3440627 : Blo 1506950 3440627 := bstep (se 1 (by rfl) ⟨2580470, by rfl⟩ : syracuseStep 3440627 = 5160941) B5160941
theorem B1507319 : Blo 1506950 1507319 := bstep (se 1 (by rfl) ⟨1130489, by rfl⟩ : syracuseStep 1507319 = 2260979) B2260979
theorem B1507335 : Blo 1506950 1507335 := bstep (se 1 (by rfl) ⟨1130501, by rfl⟩ : syracuseStep 1507335 = 2261003) B2261003
theorem B6438923 : Blo 1506950 6438923 := bstep (se 1 (by rfl) ⟨4829192, by rfl⟩ : syracuseStep 6438923 = 9658385) B9658385
theorem B1507343 : Blo 1506950 1507343 := bstep (se 1 (by rfl) ⟨1130507, by rfl⟩ : syracuseStep 1507343 = 2261015) B2261015
theorem B2261051 : Blo 1506950 2261051 := bstep (se 1 (by rfl) ⟨1695788, by rfl⟩ : syracuseStep 2261051 = 3391577) B3391577
theorem B1507387 : Blo 1506950 1507387 := bstep (se 1 (by rfl) ⟨1130540, by rfl⟩ : syracuseStep 1507387 = 2261081) B2261081
theorem B6438973 : Blo 1506950 6438973 := bstep (se 3 (by rfl) ⟨1207307, by rfl⟩ : syracuseStep 6438973 = 2414615) B2414615
theorem B17186903 : Blo 1506950 17186903 := bstep (se 1 (by rfl) ⟨12890177, by rfl⟩ : syracuseStep 17186903 = 25780355) B25780355
theorem B2261111 : Blo 1506950 2261111 := bstep (se 1 (by rfl) ⟨1695833, by rfl⟩ : syracuseStep 2261111 = 3391667) B3391667
theorem B1507463 : Blo 1506950 1507463 := bstep (se 1 (by rfl) ⟨1130597, by rfl⟩ : syracuseStep 1507463 = 2261195) B2261195
theorem B2261135 : Blo 1506950 2261135 := bstep (se 1 (by rfl) ⟨1695851, by rfl⟩ : syracuseStep 2261135 = 3391703) B3391703
theorem B1507471 : Blo 1506950 1507471 := bstep (se 1 (by rfl) ⟨1130603, by rfl⟩ : syracuseStep 1507471 = 2261207) B2261207
theorem B11452589 : Blo 1506950 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B2261177 : Blo 1506950 2261177 := bstep (se 2 (by rfl) ⟨847941, by rfl⟩ : syracuseStep 2261177 = 1695883) B1695883
theorem B1507515 : Blo 1506950 1507515 := bstep (se 1 (by rfl) ⟨1130636, by rfl⟩ : syracuseStep 1507515 = 2261273) B2261273
theorem B2261255 : Blo 1506950 2261255 := bstep (se 1 (by rfl) ⟨1695941, by rfl⟩ : syracuseStep 2261255 = 3391883) B3391883
theorem B1507591 : Blo 1506950 1507591 := bstep (se 1 (by rfl) ⟨1130693, by rfl⟩ : syracuseStep 1507591 = 2261387) B2261387
theorem B1507599 : Blo 1506950 1507599 := bstep (se 1 (by rfl) ⟨1130699, by rfl⟩ : syracuseStep 1507599 = 2261399) B2261399
theorem B2261291 : Blo 1506950 2261291 := bstep (se 1 (by rfl) ⟨1695968, by rfl⟩ : syracuseStep 2261291 = 3391937) B3391937
theorem B14483771 : Blo 1506950 14483771 := bstep (se 1 (by rfl) ⟨10862828, by rfl⟩ : syracuseStep 14483771 = 21725657) B21725657
theorem B1507643 : Blo 1506950 1507643 := bstep (se 1 (by rfl) ⟨1130732, by rfl⟩ : syracuseStep 1507643 = 2261465) B2261465
theorem B2261321 : Blo 1506950 2261321 := bstep (se 2 (by rfl) ⟨847995, by rfl⟩ : syracuseStep 2261321 = 1695991) B1695991
theorem B1696135 : Blo 1506950 1696135 := bstep (se 1 (by rfl) ⟨1272101, by rfl⟩ : syracuseStep 1696135 = 2544203) B2544203
theorem B1507719 : Blo 1506950 1507719 := bstep (se 1 (by rfl) ⟨1130789, by rfl⟩ : syracuseStep 1507719 = 2261579) B2261579
theorem B1507727 : Blo 1506950 1507727 := bstep (se 1 (by rfl) ⟨1130795, by rfl⟩ : syracuseStep 1507727 = 2261591) B2261591
theorem B2261435 : Blo 1506950 2261435 := bstep (se 1 (by rfl) ⟨1696076, by rfl⟩ : syracuseStep 2261435 = 3392153) B3392153
theorem B1507771 : Blo 1506950 1507771 := bstep (se 1 (by rfl) ⟨1130828, by rfl⟩ : syracuseStep 1507771 = 2261657) B2261657
theorem B2261495 : Blo 1506950 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B1507847 : Blo 1506950 1507847 := bstep (se 1 (by rfl) ⟨1130885, by rfl⟩ : syracuseStep 1507847 = 2261771) B2261771
theorem B2261519 : Blo 1506950 2261519 := bstep (se 1 (by rfl) ⟨1696139, by rfl⟩ : syracuseStep 2261519 = 3392279) B3392279
theorem B1507855 : Blo 1506950 1507855 := bstep (se 1 (by rfl) ⟨1130891, by rfl⟩ : syracuseStep 1507855 = 2261783) B2261783
theorem B2261561 : Blo 1506950 2261561 := bstep (se 2 (by rfl) ⟨848085, by rfl⟩ : syracuseStep 2261561 = 1696171) B1696171
theorem B1696315 : Blo 1506950 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B1507899 : Blo 1506950 1507899 := bstep (se 1 (by rfl) ⟨1130924, by rfl⟩ : syracuseStep 1507899 = 2261849) B2261849
theorem B11444813 : Blo 1506950 11444813 := bstep (se 3 (by rfl) ⟨2145902, by rfl⟩ : syracuseStep 11444813 = 4291805) B4291805
theorem B3392135 : Blo 1506950 3392135 := bstep (se 1 (by rfl) ⟨2544101, by rfl⟩ : syracuseStep 3392135 = 5088203) B5088203
theorem B2261639 : Blo 1506950 2261639 := bstep (se 1 (by rfl) ⟨1696229, by rfl⟩ : syracuseStep 2261639 = 3392459) B3392459
theorem B1507975 : Blo 1506950 1507975 := bstep (se 1 (by rfl) ⟨1130981, by rfl⟩ : syracuseStep 1507975 = 2261963) B2261963
theorem B1507983 : Blo 1506950 1507983 := bstep (se 1 (by rfl) ⟨1130987, by rfl⟩ : syracuseStep 1507983 = 2261975) B2261975
theorem B3818137 : Blo 1506950 3818137 := bstep (se 2 (by rfl) ⟨1431801, by rfl⟩ : syracuseStep 3818137 = 2863603) B2863603
theorem B2261675 : Blo 1506950 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B14500529 : Blo 1506950 14500529 := bstep (se 2 (by rfl) ⟨5437698, by rfl⟩ : syracuseStep 14500529 = 10875397) B10875397
theorem B1508027 : Blo 1506950 1508027 := bstep (se 1 (by rfl) ⟨1131020, by rfl⟩ : syracuseStep 1508027 = 2262041) B2262041
theorem B2261705 : Blo 1506950 2261705 := bstep (se 2 (by rfl) ⟨848139, by rfl⟩ : syracuseStep 2261705 = 1696279) B1696279
theorem B1508103 : Blo 1506950 1508103 := bstep (se 1 (by rfl) ⟨1131077, by rfl⟩ : syracuseStep 1508103 = 2262155) B2262155
theorem B1508111 : Blo 1506950 1508111 := bstep (se 1 (by rfl) ⟨1131083, by rfl⟩ : syracuseStep 1508111 = 2262167) B2262167
theorem B3621665 : Blo 1506950 3621665 := bstep (se 2 (by rfl) ⟨1358124, by rfl⟩ : syracuseStep 3621665 = 2716249) B2716249
theorem B3392315 : Blo 1506950 3392315 := bstep (se 1 (by rfl) ⟨2544236, by rfl⟩ : syracuseStep 3392315 = 5088473) B5088473
theorem B2261819 : Blo 1506950 2261819 := bstep (se 1 (by rfl) ⟨1696364, by rfl⟩ : syracuseStep 2261819 = 3392729) B3392729
theorem B1508155 : Blo 1506950 1508155 := bstep (se 1 (by rfl) ⟨1131116, by rfl⟩ : syracuseStep 1508155 = 2262233) B2262233
theorem B3818299 : Blo 1506950 3818299 := bstep (se 1 (by rfl) ⟨2863724, by rfl⟩ : syracuseStep 3818299 = 5727449) B5727449
theorem B2261879 : Blo 1506950 2261879 := bstep (se 1 (by rfl) ⟨1696409, by rfl⟩ : syracuseStep 2261879 = 3392819) B3392819
theorem B1508231 : Blo 1506950 1508231 := bstep (se 1 (by rfl) ⟨1131173, by rfl⟩ : syracuseStep 1508231 = 2262347) B2262347
theorem B2261903 : Blo 1506950 2261903 := bstep (se 1 (by rfl) ⟨1696427, by rfl⟩ : syracuseStep 2261903 = 3392855) B3392855
theorem B1508239 : Blo 1506950 1508239 := bstep (se 1 (by rfl) ⟨1131179, by rfl⟩ : syracuseStep 1508239 = 2262359) B2262359
theorem B3670931 : Blo 1506950 3670931 := bstep (se 1 (by rfl) ⟨2753198, by rfl⟩ : syracuseStep 3670931 = 5506397) B5506397
theorem B3392441 : Blo 1506950 3392441 := bstep (se 2 (by rfl) ⟨1272165, by rfl⟩ : syracuseStep 3392441 = 2544331) B2544331
theorem B2261945 : Blo 1506950 2261945 := bstep (se 2 (by rfl) ⟨848229, by rfl⟩ : syracuseStep 2261945 = 1696459) B1696459
theorem B1508283 : Blo 1506950 1508283 := bstep (se 1 (by rfl) ⟨1131212, by rfl⟩ : syracuseStep 1508283 = 2262425) B2262425
theorem B3818441 : Blo 1506950 3818441 := bstep (se 2 (by rfl) ⟨1431915, by rfl⟩ : syracuseStep 3818441 = 2863831) B2863831
theorem B2262023 : Blo 1506950 2262023 := bstep (se 1 (by rfl) ⟨1696517, by rfl⟩ : syracuseStep 2262023 = 3393035) B3393035
theorem B1508359 : Blo 1506950 1508359 := bstep (se 1 (by rfl) ⟨1131269, by rfl⟩ : syracuseStep 1508359 = 2262539) B2262539
theorem B1696783 : Blo 1506950 1696783 := bstep (se 1 (by rfl) ⟨1272587, by rfl⟩ : syracuseStep 1696783 = 2545175) B2545175
theorem B1508367 : Blo 1506950 1508367 := bstep (se 1 (by rfl) ⟨1131275, by rfl⟩ : syracuseStep 1508367 = 2262551) B2262551
theorem B4351009 : Blo 1506950 4351009 := bstep (se 2 (by rfl) ⟨1631628, by rfl⟩ : syracuseStep 4351009 = 3263257) B3263257
theorem B2262059 : Blo 1506950 2262059 := bstep (se 1 (by rfl) ⟨1696544, by rfl⟩ : syracuseStep 2262059 = 3393089) B3393089
theorem B1508411 : Blo 1506950 1508411 := bstep (se 1 (by rfl) ⟨1131308, by rfl⟩ : syracuseStep 1508411 = 2262617) B2262617
theorem B2262089 : Blo 1506950 2262089 := bstep (se 2 (by rfl) ⟨848283, by rfl⟩ : syracuseStep 2262089 = 1696567) B1696567
theorem B2147401 : Blo 1506950 2147401 := bstep (se 2 (by rfl) ⟨805275, by rfl⟩ : syracuseStep 2147401 = 1610551) B1610551
theorem B4293719 : Blo 1506950 4293719 := bstep (se 1 (by rfl) ⟨3220289, by rfl⟩ : syracuseStep 4293719 = 6440579) B6440579
theorem B1508487 : Blo 1506950 1508487 := bstep (se 1 (by rfl) ⟨1131365, by rfl⟩ : syracuseStep 1508487 = 2262731) B2262731
theorem B1508495 : Blo 1506950 1508495 := bstep (se 1 (by rfl) ⟨1131371, by rfl⟩ : syracuseStep 1508495 = 2262743) B2262743
theorem B2262203 : Blo 1506950 2262203 := bstep (se 1 (by rfl) ⟨1696652, by rfl⟩ : syracuseStep 2262203 = 3393305) B3393305
theorem B1508539 : Blo 1506950 1508539 := bstep (se 1 (by rfl) ⟨1131404, by rfl⟩ : syracuseStep 1508539 = 2262809) B2262809
theorem B2262263 : Blo 1506950 2262263 := bstep (se 1 (by rfl) ⟨1696697, by rfl⟩ : syracuseStep 2262263 = 3393395) B3393395
theorem B1508615 : Blo 1506950 1508615 := bstep (se 1 (by rfl) ⟨1131461, by rfl⟩ : syracuseStep 1508615 = 2262923) B2262923
theorem B5088527 : Blo 1506950 5088527 := bstep (se 1 (by rfl) ⟨3816395, by rfl⟩ : syracuseStep 5088527 = 7632791) B7632791
theorem B3392783 : Blo 1506950 3392783 := bstep (se 1 (by rfl) ⟨2544587, by rfl⟩ : syracuseStep 3392783 = 5089175) B5089175
theorem B2262287 : Blo 1506950 2262287 := bstep (se 1 (by rfl) ⟨1696715, by rfl⟩ : syracuseStep 2262287 = 3393431) B3393431
theorem B1508623 : Blo 1506950 1508623 := bstep (se 1 (by rfl) ⟨1131467, by rfl⟩ : syracuseStep 1508623 = 2262935) B2262935
theorem B3392801 : Blo 1506950 3392801 := bstep (se 2 (by rfl) ⟨1272300, by rfl⟩ : syracuseStep 3392801 = 2544601) B2544601
theorem B3818785 : Blo 1506950 3818785 := bstep (se 2 (by rfl) ⟨1432044, by rfl⟩ : syracuseStep 3818785 = 2864089) B2864089
theorem B48940321 : Blo 1506950 48940321 := bstep (se 2 (by rfl) ⟨18352620, by rfl⟩ : syracuseStep 48940321 = 36705241) B36705241
theorem B1811755 : Blo 1506950 1811755 := bstep (se 1 (by rfl) ⟨1358816, by rfl⟩ : syracuseStep 1811755 = 2717633) B2717633
theorem B2262329 : Blo 1506950 2262329 := bstep (se 2 (by rfl) ⟨848373, by rfl⟩ : syracuseStep 2262329 = 1696747) B1696747
theorem B4293947 : Blo 1506950 4293947 := bstep (se 1 (by rfl) ⟨3220460, by rfl⟩ : syracuseStep 4293947 = 6440921) B6440921
theorem B1508667 : Blo 1506950 1508667 := bstep (se 1 (by rfl) ⟨1131500, by rfl⟩ : syracuseStep 1508667 = 2263001) B2263001
theorem B2262407 : Blo 1506950 2262407 := bstep (se 1 (by rfl) ⟨1696805, by rfl⟩ : syracuseStep 2262407 = 3393611) B3393611
theorem B1508743 : Blo 1506950 1508743 := bstep (se 1 (by rfl) ⟨1131557, by rfl⟩ : syracuseStep 1508743 = 2263115) B2263115
theorem B1508751 : Blo 1506950 1508751 := bstep (se 1 (by rfl) ⟨1131563, by rfl⟩ : syracuseStep 1508751 = 2263127) B2263127
theorem B2262443 : Blo 1506950 2262443 := bstep (se 1 (by rfl) ⟨1696832, by rfl⟩ : syracuseStep 2262443 = 3393665) B3393665
theorem B4294073 : Blo 1506950 4294073 := bstep (se 2 (by rfl) ⟨1610277, by rfl⟩ : syracuseStep 4294073 = 3220555) B3220555
theorem B14493113 : Blo 1506950 14493113 := bstep (se 2 (by rfl) ⟨5434917, by rfl⟩ : syracuseStep 14493113 = 10869835) B10869835
theorem B1508795 : Blo 1506950 1508795 := bstep (se 1 (by rfl) ⟨1131596, by rfl⟩ : syracuseStep 1508795 = 2263193) B2263193
theorem B2262473 : Blo 1506950 2262473 := bstep (se 2 (by rfl) ⟨848427, by rfl⟩ : syracuseStep 2262473 = 1696855) B1696855
theorem B8586755 : Blo 1506950 8586755 := bstep (se 1 (by rfl) ⟨6440066, by rfl⟩ : syracuseStep 8586755 = 12880133) B12880133
theorem B1697287 : Blo 1506950 1697287 := bstep (se 1 (by rfl) ⟨1272965, by rfl⟩ : syracuseStep 1697287 = 2545931) B2545931
theorem B1508871 : Blo 1506950 1508871 := bstep (se 1 (by rfl) ⟨1131653, by rfl⟩ : syracuseStep 1508871 = 2263307) B2263307
theorem B1508879 : Blo 1506950 1508879 := bstep (se 1 (by rfl) ⟨1131659, by rfl⟩ : syracuseStep 1508879 = 2263319) B2263319
theorem B5088797 : Blo 1506950 5088797 := bstep (se 3 (by rfl) ⟨954149, by rfl⟩ : syracuseStep 5088797 = 1908299) B1908299
theorem B2262587 : Blo 1506950 2262587 := bstep (se 1 (by rfl) ⟨1696940, by rfl⟩ : syracuseStep 2262587 = 3393881) B3393881
theorem B1508923 : Blo 1506950 1508923 := bstep (se 1 (by rfl) ⟨1131692, by rfl⟩ : syracuseStep 1508923 = 2263385) B2263385
theorem B10872397 : Blo 1506950 10872397 := bstep (se 3 (by rfl) ⟨2038574, by rfl⟩ : syracuseStep 10872397 = 4077149) B4077149
theorem B3393143 : Blo 1506950 3393143 := bstep (se 1 (by rfl) ⟨2544857, by rfl⟩ : syracuseStep 3393143 = 5089715) B5089715
theorem B2262647 : Blo 1506950 2262647 := bstep (se 1 (by rfl) ⟨1696985, by rfl⟩ : syracuseStep 2262647 = 3393971) B3393971
theorem B2262671 : Blo 1506950 2262671 := bstep (se 1 (by rfl) ⟨1697003, by rfl⟩ : syracuseStep 2262671 = 3394007) B3394007
theorem B2262713 : Blo 1506950 2262713 := bstep (se 2 (by rfl) ⟨848517, by rfl⟩ : syracuseStep 2262713 = 1697035) B1697035
theorem B1697467 : Blo 1506950 1697467 := bstep (se 1 (by rfl) ⟨1273100, by rfl⟩ : syracuseStep 1697467 = 2546201) B2546201
theorem B29370113 : Blo 1506950 29370113 := bstep (se 2 (by rfl) ⟨11013792, by rfl⟩ : syracuseStep 29370113 = 22027585) B22027585
theorem B2262791 : Blo 1506950 2262791 := bstep (se 1 (by rfl) ⟨1697093, by rfl⟩ : syracuseStep 2262791 = 3394187) B3394187
theorem B14493455 : Blo 1506950 14493455 := bstep (se 1 (by rfl) ⟨10870091, by rfl⟩ : syracuseStep 14493455 = 21740183) B21740183
theorem B3393323 : Blo 1506950 3393323 := bstep (se 1 (by rfl) ⟨2544992, by rfl⟩ : syracuseStep 3393323 = 5089985) B5089985
theorem B2262827 : Blo 1506950 2262827 := bstep (se 1 (by rfl) ⟨1697120, by rfl⟩ : syracuseStep 2262827 = 3394241) B3394241
theorem B32622385 : Blo 1506950 32622385 := bstep (se 2 (by rfl) ⟨12233394, by rfl⟩ : syracuseStep 32622385 = 24466789) B24466789
theorem B2262857 : Blo 1506950 2262857 := bstep (se 2 (by rfl) ⟨848571, by rfl⟩ : syracuseStep 2262857 = 1697143) B1697143
theorem B3819383 : Blo 1506950 3819383 := bstep (se 1 (by rfl) ⟨2864537, by rfl⟩ : syracuseStep 3819383 = 5729075) B5729075
theorem B3221383 : Blo 1506950 3221383 := bstep (se 1 (by rfl) ⟨2416037, by rfl⟩ : syracuseStep 3221383 = 4832075) B4832075
theorem B12560291 : Blo 1506950 12560291 := bstep (se 1 (by rfl) ⟨9420218, by rfl⟩ : syracuseStep 12560291 = 18840437) B18840437
theorem B2262971 : Blo 1506950 2262971 := bstep (se 1 (by rfl) ⟨1697228, by rfl⟩ : syracuseStep 2262971 = 3394457) B3394457
theorem B2263031 : Blo 1506950 2263031 := bstep (se 1 (by rfl) ⟨1697273, by rfl⟩ : syracuseStep 2263031 = 3394547) B3394547
theorem B7637003 : Blo 1506950 7637003 := bstep (se 1 (by rfl) ⟨5727752, by rfl⟩ : syracuseStep 7637003 = 11455505) B11455505
theorem B47720461 : Blo 1506950 47720461 := bstep (se 3 (by rfl) ⟨8947586, by rfl⟩ : syracuseStep 47720461 = 17895173) B17895173
theorem B2263055 : Blo 1506950 2263055 := bstep (se 1 (by rfl) ⟨1697291, by rfl⟩ : syracuseStep 2263055 = 3394583) B3394583
theorem B2263097 : Blo 1506950 2263097 := bstep (se 2 (by rfl) ⟨848661, by rfl⟩ : syracuseStep 2263097 = 1697323) B1697323
theorem B3672179 : Blo 1506950 3672179 := bstep (se 1 (by rfl) ⟨2754134, by rfl⟩ : syracuseStep 3672179 = 5508269) B5508269
theorem B2263175 : Blo 1506950 2263175 := bstep (se 1 (by rfl) ⟨1697381, by rfl⟩ : syracuseStep 2263175 = 3394763) B3394763
theorem B3393683 : Blo 1506950 3393683 := bstep (se 1 (by rfl) ⟨2545262, by rfl⟩ : syracuseStep 3393683 = 5090525) B5090525
theorem B2263211 : Blo 1506950 2263211 := bstep (se 1 (by rfl) ⟨1697408, by rfl⟩ : syracuseStep 2263211 = 3394817) B3394817
theorem B7637165 : Blo 1506950 7637165 := bstep (se 3 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 7637165 = 2863937) B2863937
theorem B2861257 : Blo 1506950 2861257 := bstep (se 2 (by rfl) ⟨1072971, by rfl⟩ : syracuseStep 2861257 = 2145943) B2145943
theorem B3393737 : Blo 1506950 3393737 := bstep (se 2 (by rfl) ⟨1272651, by rfl⟩ : syracuseStep 3393737 = 2545303) B2545303
theorem B2263241 : Blo 1506950 2263241 := bstep (se 2 (by rfl) ⟨848715, by rfl⟩ : syracuseStep 2263241 = 1697431) B1697431
theorem B2263355 : Blo 1506950 2263355 := bstep (se 1 (by rfl) ⟨1697516, by rfl⟩ : syracuseStep 2263355 = 3395033) B3395033
theorem B3623287 : Blo 1506950 3623287 := bstep (se 1 (by rfl) ⟨2717465, by rfl⟩ : syracuseStep 3623287 = 5434931) B5434931
theorem B2263415 : Blo 1506950 2263415 := bstep (se 1 (by rfl) ⟨1697561, by rfl⟩ : syracuseStep 2263415 = 3395123) B3395123
theorem B13748701 : Blo 1506950 13748701 := bstep (se 3 (by rfl) ⟨2577881, by rfl⟩ : syracuseStep 13748701 = 5155763) B5155763
theorem B9660971 : Blo 1506950 9660971 := bstep (se 1 (by rfl) ⟨7245728, by rfl⟩ : syracuseStep 9660971 = 14491457) B14491457
theorem B11455019 : Blo 1506950 11455019 := bstep (se 1 (by rfl) ⟨8591264, by rfl⟩ : syracuseStep 11455019 = 17182529) B17182529
theorem B38644289 : Blo 1506950 38644289 := bstep (se 2 (by rfl) ⟨14491608, by rfl⟩ : syracuseStep 38644289 = 28983217) B28983217
theorem B12888881 : Blo 1506950 12888881 := bstep (se 2 (by rfl) ⟨4833330, by rfl⟩ : syracuseStep 12888881 = 9666661) B9666661
theorem B3394439 : Blo 1506950 3394439 := bstep (se 1 (by rfl) ⟨2545829, by rfl⟩ : syracuseStep 3394439 = 5091659) B5091659
theorem B7629713 : Blo 1506950 7629713 := bstep (se 2 (by rfl) ⟨2861142, by rfl⟩ : syracuseStep 7629713 = 5722285) B5722285
theorem B5090201 : Blo 1506950 5090201 := bstep (se 2 (by rfl) ⟨1908825, by rfl⟩ : syracuseStep 5090201 = 3817651) B3817651
theorem B11447243 : Blo 1506950 11447243 := bstep (se 1 (by rfl) ⟨8585432, by rfl⟩ : syracuseStep 11447243 = 17170865) B17170865
theorem B4295713 : Blo 1506950 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B3394619 : Blo 1506950 3394619 := bstep (se 1 (by rfl) ⟨2545964, by rfl⟩ : syracuseStep 3394619 = 5091929) B5091929
theorem B3394745 : Blo 1506950 3394745 := bstep (se 2 (by rfl) ⟨1273029, by rfl⟩ : syracuseStep 3394745 = 2546059) B2546059
theorem B6442355 : Blo 1506950 6442355 := bstep (se 1 (by rfl) ⟨4831766, by rfl⟩ : syracuseStep 6442355 = 9663533) B9663533
theorem B4296203 : Blo 1506950 4296203 := bstep (se 1 (by rfl) ⟨3222152, by rfl⟩ : syracuseStep 4296203 = 6444305) B6444305
theorem B3395087 : Blo 1506950 3395087 := bstep (se 1 (by rfl) ⟨2546315, by rfl⟩ : syracuseStep 3395087 = 5092631) B5092631
theorem B3395105 : Blo 1506950 3395105 := bstep (se 2 (by rfl) ⟨1273164, by rfl⟩ : syracuseStep 3395105 = 2546329) B2546329
theorem B8826455 : Blo 1506950 8826455 := bstep (se 1 (by rfl) ⟨6619841, by rfl⟩ : syracuseStep 8826455 = 13239683) B13239683
theorem B5090903 : Blo 1506950 5090903 := bstep (se 1 (by rfl) ⟨3818177, by rfl⟩ : syracuseStep 5090903 = 7636355) B7636355
theorem B2649719 : Blo 1506950 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B2543305 : Blo 1506950 2543305 := bstep (se 2 (by rfl) ⟨953739, by rfl⟩ : syracuseStep 2543305 = 1907479) B1907479
theorem B7638785 : Blo 1506950 7638785 := bstep (se 2 (by rfl) ⟨2864544, by rfl⟩ : syracuseStep 7638785 = 5729089) B5729089
theorem B4828987 : Blo 1506950 4828987 := bstep (se 1 (by rfl) ⟨3621740, by rfl⟩ : syracuseStep 4828987 = 7243481) B7243481
theorem B1609615 : Blo 1506950 1609615 := bstep (se 1 (by rfl) ⟨1207211, by rfl⟩ : syracuseStep 1609615 = 2414423) B2414423
theorem B32591767 : Blo 1506950 32591767 := bstep (se 1 (by rfl) ⟨24443825, by rfl⟩ : syracuseStep 32591767 = 48887651) B48887651
theorem B10866635 : Blo 1506950 10866635 := bstep (se 1 (by rfl) ⟨8149976, by rfl⟩ : syracuseStep 10866635 = 16299953) B16299953
theorem B2863163 : Blo 1506950 2863163 := bstep (se 1 (by rfl) ⟨2147372, by rfl⟩ : syracuseStep 2863163 = 4294745) B4294745
theorem B5091389 : Blo 1506950 5091389 := bstep (se 3 (by rfl) ⟨954635, by rfl⟩ : syracuseStep 5091389 = 1909271) B1909271
theorem B61870321 : Blo 1506950 61870321 := bstep (se 2 (by rfl) ⟨23201370, by rfl⟩ : syracuseStep 61870321 = 46402741) B46402741
theorem B24441101 : Blo 1506950 24441101 := bstep (se 3 (by rfl) ⟨4582706, by rfl⟩ : syracuseStep 24441101 = 9165413) B9165413
theorem B6443297 : Blo 1506950 6443297 := bstep (se 2 (by rfl) ⟨2416236, by rfl⟩ : syracuseStep 6443297 = 4832473) B4832473
theorem B3625249 : Blo 1506950 3625249 := bstep (se 2 (by rfl) ⟨1359468, by rfl⟩ : syracuseStep 3625249 = 2718937) B2718937
theorem B5157179 : Blo 1506950 5157179 := bstep (se 1 (by rfl) ⟨3867884, by rfl⟩ : syracuseStep 5157179 = 7735769) B7735769
theorem B2544007 : Blo 1506950 2544007 := bstep (se 1 (by rfl) ⟨1908005, by rfl⟩ : syracuseStep 2544007 = 3816011) B3816011
theorem B4583827 : Blo 1506950 4583827 := bstep (se 1 (by rfl) ⟨3437870, by rfl⟩ : syracuseStep 4583827 = 6875741) B6875741
theorem B2863649 : Blo 1506950 2863649 := bstep (se 2 (by rfl) ⟨1073868, by rfl⟩ : syracuseStep 2863649 = 2147737) B2147737
theorem B16528049 : Blo 1506950 16528049 := bstep (se 2 (by rfl) ⟨6198018, by rfl⟩ : syracuseStep 16528049 = 12396037) B12396037
theorem B2863991 : Blo 1506950 2863991 := bstep (se 1 (by rfl) ⟨2147993, by rfl⟩ : syracuseStep 2863991 = 4295987) B4295987
theorem B7631819 : Blo 1506950 7631819 := bstep (se 1 (by rfl) ⟨5723864, by rfl⟩ : syracuseStep 7631819 = 11447729) B11447729
theorem B2716687 : Blo 1506950 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B2544655 : Blo 1506950 2544655 := bstep (se 1 (by rfl) ⟨1908491, by rfl⟩ : syracuseStep 2544655 = 3816983) B3816983
theorem B3814553 : Blo 1506950 3814553 := bstep (se 2 (by rfl) ⟨1430457, by rfl⟩ : syracuseStep 3814553 = 2860915) B2860915
theorem B30602477 : Blo 1506950 30602477 := bstep (se 3 (by rfl) ⟨5737964, by rfl⟩ : syracuseStep 30602477 = 11475929) B11475929
theorem B6444269 : Blo 1506950 6444269 := bstep (se 3 (by rfl) ⟨1208300, by rfl⟩ : syracuseStep 6444269 = 2416601) B2416601
theorem B7632143 : Blo 1506950 7632143 := bstep (se 1 (by rfl) ⟨5724107, by rfl⟩ : syracuseStep 7632143 = 11448215) B11448215
theorem B3814715 : Blo 1506950 3814715 := bstep (se 1 (by rfl) ⟨2861036, by rfl⟩ : syracuseStep 3814715 = 5722073) B5722073
theorem B2793487 : Blo 1506950 2793487 := bstep (se 1 (by rfl) ⟨2095115, by rfl⟩ : syracuseStep 2793487 = 4190231) B4190231
theorem B49550723 : Blo 1506950 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B132159005 : Blo 1506950 132159005 := bstep (se 3 (by rfl) ⟨24779813, by rfl⟩ : syracuseStep 132159005 = 49559627) B49559627
theorem B14489117 : Blo 1506950 14489117 := bstep (se 3 (by rfl) ⟨2716709, by rfl⟩ : syracuseStep 14489117 = 5433419) B5433419
theorem B8582699 : Blo 1506950 8582699 := bstep (se 1 (by rfl) ⟨6437024, by rfl⟩ : syracuseStep 8582699 = 12874049) B12874049
theorem B2545195 : Blo 1506950 2545195 := bstep (se 1 (by rfl) ⟨1908896, by rfl⟩ : syracuseStep 2545195 = 3817793) B3817793
theorem B18347563 : Blo 1506950 18347563 := bstep (se 1 (by rfl) ⟨13760672, by rfl⟩ : syracuseStep 18347563 = 27521345) B27521345
theorem B17167949 : Blo 1506950 17167949 := bstep (se 3 (by rfl) ⟨3218990, by rfl⟩ : syracuseStep 17167949 = 6437981) B6437981
theorem B3815059 : Blo 1506950 3815059 := bstep (se 1 (by rfl) ⟨2861294, by rfl⟩ : syracuseStep 3815059 = 5722589) B5722589
theorem B2545337 : Blo 1506950 2545337 := bstep (se 2 (by rfl) ⟨954501, by rfl⟩ : syracuseStep 2545337 = 1909003) B1909003
theorem B16307905 : Blo 1506950 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B3815201 : Blo 1506950 3815201 := bstep (se 2 (by rfl) ⟨1430700, by rfl⟩ : syracuseStep 3815201 = 2861401) B2861401
theorem B6444953 : Blo 1506950 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B2293751 : Blo 1506950 2293751 := bstep (se 1 (by rfl) ⟨1720313, by rfl⟩ : syracuseStep 2293751 = 3440627) B3440627
theorem B9664535 : Blo 1506950 9664535 := bstep (se 1 (by rfl) ⟨7248401, by rfl⟩ : syracuseStep 9664535 = 14496803) B14496803
theorem B12400663 : Blo 1506950 12400663 := bstep (se 1 (by rfl) ⟨9300497, by rfl⟩ : syracuseStep 12400663 = 18600995) B18600995
theorem B7739435 : Blo 1506950 7739435 := bstep (se 1 (by rfl) ⟨5804576, by rfl⟩ : syracuseStep 7739435 = 11609153) B11609153
theorem B8591447 : Blo 1506950 8591447 := bstep (se 1 (by rfl) ⟨6443585, by rfl⟩ : syracuseStep 8591447 = 12887171) B12887171
theorem B16750709 : Blo 1506950 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B12261577 : Blo 1506950 12261577 := bstep (se 2 (by rfl) ⟨4598091, by rfl⟩ : syracuseStep 12261577 = 9196183) B9196183
theorem B2546039 : Blo 1506950 2546039 := bstep (se 1 (by rfl) ⟨1909529, by rfl⟩ : syracuseStep 2546039 = 3819059) B3819059
theorem B6879755 : Blo 1506950 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B5724701 : Blo 1506950 5724701 := bstep (se 3 (by rfl) ⟨1073381, by rfl⟩ : syracuseStep 5724701 = 2146763) B2146763
theorem B5724715 : Blo 1506950 5724715 := bstep (se 1 (by rfl) ⟨4293536, by rfl⟩ : syracuseStep 5724715 = 8587073) B8587073
theorem B7633601 : Blo 1506950 7633601 := bstep (se 2 (by rfl) ⟨2862600, by rfl⟩ : syracuseStep 7633601 = 5725201) B5725201
theorem B3816193 : Blo 1506950 3816193 := bstep (se 2 (by rfl) ⟨1431072, by rfl⟩ : syracuseStep 3816193 = 2862145) B2862145
theorem B4291339 : Blo 1506950 4291339 := bstep (se 1 (by rfl) ⟨3218504, by rfl⟩ : syracuseStep 4291339 = 6437009) B6437009
theorem B8821537 : Blo 1506950 8821537 := bstep (se 2 (by rfl) ⟨3308076, by rfl⟩ : syracuseStep 8821537 = 6616153) B6616153
theorem B4078471 : Blo 1506950 4078471 := bstep (se 1 (by rfl) ⟨3058853, by rfl⟩ : syracuseStep 4078471 = 6117707) B6117707
theorem B8584157 : Blo 1506950 8584157 := bstep (se 3 (by rfl) ⟨1609529, by rfl⟩ : syracuseStep 8584157 = 3219059) B3219059
theorem B4291613 : Blo 1506950 4291613 := bstep (se 3 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 4291613 = 1609355) B1609355
theorem B188185781 : Blo 1506950 188185781 := bstep (se 5 (by rfl) ⟨8821208, by rfl⟩ : syracuseStep 188185781 = 17642417) B17642417
theorem B1907975 : Blo 1506950 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B13753633 : Blo 1506950 13753633 := bstep (se 2 (by rfl) ⟨5157612, by rfl⟩ : syracuseStep 13753633 = 10315225) B10315225
theorem B2293051 : Blo 1506950 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B3816791 : Blo 1506950 3816791 := bstep (se 1 (by rfl) ⟨2862593, by rfl⟩ : syracuseStep 3816791 = 5725187) B5725187
theorem B41270627 : Blo 1506950 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B3390839 : Blo 1506950 3390839 := bstep (se 1 (by rfl) ⟨2543129, by rfl⟩ : syracuseStep 3390839 = 5086259) B5086259
theorem B2260487 : Blo 1506950 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B8150539 : Blo 1506950 8150539 := bstep (se 1 (by rfl) ⟨6112904, by rfl⟩ : syracuseStep 8150539 = 12225809) B12225809
theorem B2260523 : Blo 1506950 2260523 := bstep (se 1 (by rfl) ⟨1695392, by rfl⟩ : syracuseStep 2260523 = 3390785) B3390785
theorem B3391019 : Blo 1506950 3391019 := bstep (se 1 (by rfl) ⟨2543264, by rfl⟩ : syracuseStep 3391019 = 5086529) B5086529
theorem B3817003 : Blo 1506950 3817003 := bstep (se 1 (by rfl) ⟨2862752, by rfl⟩ : syracuseStep 3817003 = 5725505) B5725505
theorem B17178155 : Blo 1506950 17178155 := bstep (se 1 (by rfl) ⟨12883616, by rfl⟩ : syracuseStep 17178155 = 25767233) B25767233
theorem B2260553 : Blo 1506950 2260553 := bstep (se 2 (by rfl) ⟨847707, by rfl⟩ : syracuseStep 2260553 = 1695415) B1695415
theorem B7249495 : Blo 1506950 7249495 := bstep (se 1 (by rfl) ⟨5437121, by rfl⟩ : syracuseStep 7249495 = 10874243) B10874243
theorem B1506951 : Blo 1506950 1506951 := bstep (se 1 (by rfl) ⟨1130213, by rfl⟩ : syracuseStep 1506951 = 2260427) B2260427
theorem B1506959 : Blo 1506950 1506959 := bstep (se 1 (by rfl) ⟨1130219, by rfl⟩ : syracuseStep 1506959 = 2260439) B2260439
theorem B3817145 : Blo 1506950 3817145 := bstep (se 2 (by rfl) ⟨1431429, by rfl⟩ : syracuseStep 3817145 = 2862859) B2862859
theorem B1507003 : Blo 1506950 1507003 := bstep (se 1 (by rfl) ⟨1130252, by rfl⟩ : syracuseStep 1507003 = 2260505) B2260505
theorem B2260667 : Blo 1506950 2260667 := bstep (se 1 (by rfl) ⟨1695500, by rfl⟩ : syracuseStep 2260667 = 3391001) B3391001
theorem B2260727 : Blo 1506950 2260727 := bstep (se 1 (by rfl) ⟨1695545, by rfl⟩ : syracuseStep 2260727 = 3391091) B3391091
theorem B1507079 : Blo 1506950 1507079 := bstep (se 1 (by rfl) ⟨1130309, by rfl⟩ : syracuseStep 1507079 = 2260619) B2260619
theorem B1507087 : Blo 1506950 1507087 := bstep (se 1 (by rfl) ⟨1130315, by rfl⟩ : syracuseStep 1507087 = 2260631) B2260631
theorem B2260751 : Blo 1506950 2260751 := bstep (se 1 (by rfl) ⟨1695563, by rfl⟩ : syracuseStep 2260751 = 3391127) B3391127
theorem B2260793 : Blo 1506950 2260793 := bstep (se 2 (by rfl) ⟨847797, by rfl⟩ : syracuseStep 2260793 = 1695595) B1695595
theorem B1507131 : Blo 1506950 1507131 := bstep (se 1 (by rfl) ⟨1130348, by rfl⟩ : syracuseStep 1507131 = 2260697) B2260697
theorem B1507207 : Blo 1506950 1507207 := bstep (se 1 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 1507207 = 2260811) B2260811
theorem B2260871 : Blo 1506950 2260871 := bstep (se 1 (by rfl) ⟨1695653, by rfl⟩ : syracuseStep 2260871 = 3391307) B3391307
theorem B1507215 : Blo 1506950 1507215 := bstep (se 1 (by rfl) ⟨1130411, by rfl⟩ : syracuseStep 1507215 = 2260823) B2260823
theorem B1695631 : Blo 1506950 1695631 := bstep (se 1 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 1695631 = 2543447) B2543447
theorem B1908623 : Blo 1506950 1908623 := bstep (se 1 (by rfl) ⟨1431467, by rfl⟩ : syracuseStep 1908623 = 2862935) B2862935
theorem B3391379 : Blo 1506950 3391379 := bstep (se 1 (by rfl) ⟨2543534, by rfl⟩ : syracuseStep 3391379 = 5087069) B5087069
theorem B5087123 : Blo 1506950 5087123 := bstep (se 1 (by rfl) ⟨3815342, by rfl⟩ : syracuseStep 5087123 = 7630685) B7630685
theorem B2260907 : Blo 1506950 2260907 := bstep (se 1 (by rfl) ⟨1695680, by rfl⟩ : syracuseStep 2260907 = 3391361) B3391361
theorem B1507259 : Blo 1506950 1507259 := bstep (se 1 (by rfl) ⟨1130444, by rfl⟩ : syracuseStep 1507259 = 2260889) B2260889
theorem B2260937 : Blo 1506950 2260937 := bstep (se 2 (by rfl) ⟨847851, by rfl⟩ : syracuseStep 2260937 = 1695703) B1695703
theorem B3391433 : Blo 1506950 3391433 := bstep (se 2 (by rfl) ⟨1271787, by rfl⟩ : syracuseStep 3391433 = 2543575) B2543575
theorem B3219401 : Blo 1506950 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B7634897 : Blo 1506950 7634897 := bstep (se 2 (by rfl) ⟨2863086, by rfl⟩ : syracuseStep 7634897 = 5726173) B5726173
theorem B8593361 : Blo 1506950 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B4292615 : Blo 1506950 4292615 := bstep (se 1 (by rfl) ⟨3219461, by rfl⟩ : syracuseStep 4292615 = 6438923) B6438923
theorem B63627281 : Blo 1506950 63627281 := bstep (se 2 (by rfl) ⟨23860230, by rfl⟩ : syracuseStep 63627281 = 47720461) B47720461
theorem B1507367 : Blo 1506950 1507367 := bstep (se 1 (by rfl) ⟨1130525, by rfl⟩ : syracuseStep 1507367 = 2261051) B2261051
theorem B1908775 : Blo 1506950 1908775 := bstep (se 1 (by rfl) ⟨1431581, by rfl⟩ : syracuseStep 1908775 = 2863163) B2863163
theorem B1507407 : Blo 1506950 1507407 := bstep (se 1 (by rfl) ⟨1130555, by rfl⟩ : syracuseStep 1507407 = 2261111) B2261111
theorem B8585297 : Blo 1506950 8585297 := bstep (se 2 (by rfl) ⟨3219486, by rfl⟩ : syracuseStep 8585297 = 6438973) B6438973
theorem B1507423 : Blo 1506950 1507423 := bstep (se 1 (by rfl) ⟨1130567, by rfl⟩ : syracuseStep 1507423 = 2261135) B2261135
theorem B7635059 : Blo 1506950 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B1507451 : Blo 1506950 1507451 := bstep (se 1 (by rfl) ⟨1130588, by rfl⟩ : syracuseStep 1507451 = 2261177) B2261177
theorem B1507503 : Blo 1506950 1507503 := bstep (se 1 (by rfl) ⟨1130627, by rfl⟩ : syracuseStep 1507503 = 2261255) B2261255
theorem B16294067 : Blo 1506950 16294067 := bstep (se 1 (by rfl) ⟨12220550, by rfl⟩ : syracuseStep 16294067 = 24441101) B24441101
theorem B1507527 : Blo 1506950 1507527 := bstep (se 1 (by rfl) ⟨1130645, by rfl⟩ : syracuseStep 1507527 = 2261291) B2261291
theorem B1507547 : Blo 1506950 1507547 := bstep (se 1 (by rfl) ⟨1130660, by rfl⟩ : syracuseStep 1507547 = 2261321) B2261321
theorem B1507623 : Blo 1506950 1507623 := bstep (se 1 (by rfl) ⟨1130717, by rfl⟩ : syracuseStep 1507623 = 2261435) B2261435
theorem B82493761 : Blo 1506950 82493761 := bstep (se 2 (by rfl) ⟨30935160, by rfl⟩ : syracuseStep 82493761 = 61870321) B61870321
theorem B1507663 : Blo 1506950 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B1507679 : Blo 1506950 1507679 := bstep (se 1 (by rfl) ⟨1130759, by rfl⟩ : syracuseStep 1507679 = 2261519) B2261519
theorem B1909099 : Blo 1506950 1909099 := bstep (se 1 (by rfl) ⟨1431824, by rfl⟩ : syracuseStep 1909099 = 2863649) B2863649
theorem B1507707 : Blo 1506950 1507707 := bstep (se 1 (by rfl) ⟨1130780, by rfl⟩ : syracuseStep 1507707 = 2261561) B2261561
theorem B4833665 : Blo 1506950 4833665 := bstep (se 2 (by rfl) ⟨1812624, by rfl⟩ : syracuseStep 4833665 = 3625249) B3625249
theorem B2261423 : Blo 1506950 2261423 := bstep (se 1 (by rfl) ⟨1696067, by rfl⟩ : syracuseStep 2261423 = 3392135) B3392135
theorem B1507759 : Blo 1506950 1507759 := bstep (se 1 (by rfl) ⟨1130819, by rfl⟩ : syracuseStep 1507759 = 2261639) B2261639
theorem B1507783 : Blo 1506950 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B11018699 : Blo 1506950 11018699 := bstep (se 1 (by rfl) ⟨8264024, by rfl⟩ : syracuseStep 11018699 = 16528049) B16528049
theorem B1507803 : Blo 1506950 1507803 := bstep (se 1 (by rfl) ⟨1130852, by rfl⟩ : syracuseStep 1507803 = 2261705) B2261705
theorem B3392009 : Blo 1506950 3392009 := bstep (se 2 (by rfl) ⟨1272003, by rfl⟩ : syracuseStep 3392009 = 2544007) B2544007
theorem B2261513 : Blo 1506950 2261513 := bstep (se 2 (by rfl) ⟨848067, by rfl⟩ : syracuseStep 2261513 = 1696135) B1696135
theorem B6111769 : Blo 1506950 6111769 := bstep (se 2 (by rfl) ⟨2291913, by rfl⟩ : syracuseStep 6111769 = 4583827) B4583827
theorem B2261543 : Blo 1506950 2261543 := bstep (se 1 (by rfl) ⟨1696157, by rfl⟩ : syracuseStep 2261543 = 3392315) B3392315
theorem B1507879 : Blo 1506950 1507879 := bstep (se 1 (by rfl) ⟨1130909, by rfl⟩ : syracuseStep 1507879 = 2261819) B2261819
theorem B1507919 : Blo 1506950 1507919 := bstep (se 1 (by rfl) ⟨1130939, by rfl⟩ : syracuseStep 1507919 = 2261879) B2261879
theorem B1909327 : Blo 1506950 1909327 := bstep (se 1 (by rfl) ⟨1431995, by rfl⟩ : syracuseStep 1909327 = 2863991) B2863991
theorem B1507935 : Blo 1506950 1507935 := bstep (se 1 (by rfl) ⟨1130951, by rfl⟩ : syracuseStep 1507935 = 2261903) B2261903
theorem B2261627 : Blo 1506950 2261627 := bstep (se 1 (by rfl) ⟨1696220, by rfl⟩ : syracuseStep 2261627 = 3392441) B3392441
theorem B1507963 : Blo 1506950 1507963 := bstep (se 1 (by rfl) ⟨1130972, by rfl⟩ : syracuseStep 1507963 = 2261945) B2261945
theorem B5087879 : Blo 1506950 5087879 := bstep (se 1 (by rfl) ⟨3815909, by rfl⟩ : syracuseStep 5087879 = 7631819) B7631819
theorem B1508015 : Blo 1506950 1508015 := bstep (se 1 (by rfl) ⟨1131011, by rfl⟩ : syracuseStep 1508015 = 2262023) B2262023
theorem B5087933 : Blo 1506950 5087933 := bstep (se 3 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 5087933 = 1907975) B1907975
theorem B1508039 : Blo 1506950 1508039 := bstep (se 1 (by rfl) ⟨1131029, by rfl⟩ : syracuseStep 1508039 = 2262059) B2262059
theorem B1508059 : Blo 1506950 1508059 := bstep (se 1 (by rfl) ⟨1131044, by rfl⟩ : syracuseStep 1508059 = 2262089) B2262089
theorem B2261753 : Blo 1506950 2261753 := bstep (se 2 (by rfl) ⟨848157, by rfl⟩ : syracuseStep 2261753 = 1696315) B1696315
theorem B1508135 : Blo 1506950 1508135 := bstep (se 1 (by rfl) ⟨1131101, by rfl⟩ : syracuseStep 1508135 = 2262203) B2262203
theorem B1508175 : Blo 1506950 1508175 := bstep (se 1 (by rfl) ⟨1131131, by rfl⟩ : syracuseStep 1508175 = 2262263) B2262263
theorem B5088095 : Blo 1506950 5088095 := bstep (se 1 (by rfl) ⟨3816071, by rfl⟩ : syracuseStep 5088095 = 7632143) B7632143
theorem B3392351 : Blo 1506950 3392351 := bstep (se 1 (by rfl) ⟨2544263, by rfl⟩ : syracuseStep 3392351 = 5088527) B5088527
theorem B2261855 : Blo 1506950 2261855 := bstep (se 1 (by rfl) ⟨1696391, by rfl⟩ : syracuseStep 2261855 = 3392783) B3392783
theorem B1508191 : Blo 1506950 1508191 := bstep (se 1 (by rfl) ⟨1131143, by rfl⟩ : syracuseStep 1508191 = 2262287) B2262287
theorem B2261867 : Blo 1506950 2261867 := bstep (se 1 (by rfl) ⟨1696400, by rfl⟩ : syracuseStep 2261867 = 3392801) B3392801
theorem B1508219 : Blo 1506950 1508219 := bstep (se 1 (by rfl) ⟨1131164, by rfl⟩ : syracuseStep 1508219 = 2262329) B2262329
theorem B1508271 : Blo 1506950 1508271 := bstep (se 1 (by rfl) ⟨1131203, by rfl⟩ : syracuseStep 1508271 = 2262407) B2262407
theorem B1508295 : Blo 1506950 1508295 := bstep (se 1 (by rfl) ⟨1131221, by rfl⟩ : syracuseStep 1508295 = 2262443) B2262443
theorem B17179613 : Blo 1506950 17179613 := bstep (se 3 (by rfl) ⟨3221177, by rfl⟩ : syracuseStep 17179613 = 6442355) B6442355
theorem B1508315 : Blo 1506950 1508315 := bstep (se 1 (by rfl) ⟨1131236, by rfl⟩ : syracuseStep 1508315 = 2262473) B2262473
theorem B5088257 : Blo 1506950 5088257 := bstep (se 2 (by rfl) ⟨1908096, by rfl⟩ : syracuseStep 5088257 = 3816193) B3816193
theorem B88106003 : Blo 1506950 88106003 := bstep (se 1 (by rfl) ⟨66079502, by rfl⟩ : syracuseStep 88106003 = 132159005) B132159005
theorem B9659411 : Blo 1506950 9659411 := bstep (se 1 (by rfl) ⟨7244558, by rfl⟩ : syracuseStep 9659411 = 14489117) B14489117
theorem B3392531 : Blo 1506950 3392531 := bstep (se 1 (by rfl) ⟨2544398, by rfl⟩ : syracuseStep 3392531 = 5088797) B5088797
theorem B1508391 : Blo 1506950 1508391 := bstep (se 1 (by rfl) ⟨1131293, by rfl⟩ : syracuseStep 1508391 = 2262587) B2262587
theorem B11445299 : Blo 1506950 11445299 := bstep (se 1 (by rfl) ⟨8583974, by rfl⟩ : syracuseStep 11445299 = 17167949) B17167949
theorem B2262095 : Blo 1506950 2262095 := bstep (se 1 (by rfl) ⟨1696571, by rfl⟩ : syracuseStep 2262095 = 3393143) B3393143
theorem B1508431 : Blo 1506950 1508431 := bstep (se 1 (by rfl) ⟨1131323, by rfl⟩ : syracuseStep 1508431 = 2262647) B2262647
theorem B1508447 : Blo 1506950 1508447 := bstep (se 1 (by rfl) ⟨1131335, by rfl⟩ : syracuseStep 1508447 = 2262671) B2262671
theorem B1696891 : Blo 1506950 1696891 := bstep (se 1 (by rfl) ⟨1272668, by rfl⟩ : syracuseStep 1696891 = 2545337) B2545337
theorem B1508475 : Blo 1506950 1508475 := bstep (se 1 (by rfl) ⟨1131356, by rfl⟩ : syracuseStep 1508475 = 2262713) B2262713
theorem B19580075 : Blo 1506950 19580075 := bstep (se 1 (by rfl) ⟨14685056, by rfl⟩ : syracuseStep 19580075 = 29370113) B29370113
theorem B1508527 : Blo 1506950 1508527 := bstep (se 1 (by rfl) ⟨1131395, by rfl⟩ : syracuseStep 1508527 = 2262791) B2262791
theorem B2262215 : Blo 1506950 2262215 := bstep (se 1 (by rfl) ⟨1696661, by rfl⟩ : syracuseStep 2262215 = 3393323) B3393323
theorem B1508551 : Blo 1506950 1508551 := bstep (se 1 (by rfl) ⟨1131413, by rfl⟩ : syracuseStep 1508551 = 2262827) B2262827
theorem B1508571 : Blo 1506950 1508571 := bstep (se 1 (by rfl) ⟨1131428, by rfl⟩ : syracuseStep 1508571 = 2262857) B2262857
theorem B9667019 : Blo 1506950 9667019 := bstep (se 1 (by rfl) ⟨7250264, by rfl⟩ : syracuseStep 9667019 = 14500529) B14500529
theorem B8373527 : Blo 1506950 8373527 := bstep (se 1 (by rfl) ⟨6280145, by rfl⟩ : syracuseStep 8373527 = 12560291) B12560291
theorem B1508647 : Blo 1506950 1508647 := bstep (se 1 (by rfl) ⟨1131485, by rfl⟩ : syracuseStep 1508647 = 2262971) B2262971
theorem B1508687 : Blo 1506950 1508687 := bstep (se 1 (by rfl) ⟨1131515, by rfl⟩ : syracuseStep 1508687 = 2263031) B2263031
theorem B1508703 : Blo 1506950 1508703 := bstep (se 1 (by rfl) ⟨1131527, by rfl⟩ : syracuseStep 1508703 = 2263055) B2263055
theorem B3622249 : Blo 1506950 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B3392873 : Blo 1506950 3392873 := bstep (se 2 (by rfl) ⟨1272327, by rfl⟩ : syracuseStep 3392873 = 2544655) B2544655
theorem B2262377 : Blo 1506950 2262377 := bstep (se 2 (by rfl) ⟨848391, by rfl⟩ : syracuseStep 2262377 = 1696783) B1696783
theorem B5801345 : Blo 1506950 5801345 := bstep (se 2 (by rfl) ⟨2175504, by rfl⟩ : syracuseStep 5801345 = 4351009) B4351009
theorem B5727617 : Blo 1506950 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B5727631 : Blo 1506950 5727631 := bstep (se 1 (by rfl) ⟨4295723, by rfl⟩ : syracuseStep 5727631 = 8591447) B8591447
theorem B11167139 : Blo 1506950 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B1508783 : Blo 1506950 1508783 := bstep (se 1 (by rfl) ⟨1131587, by rfl⟩ : syracuseStep 1508783 = 2263175) B2263175
theorem B2262455 : Blo 1506950 2262455 := bstep (se 1 (by rfl) ⟨1696841, by rfl⟩ : syracuseStep 2262455 = 3393683) B3393683
theorem B1508807 : Blo 1506950 1508807 := bstep (se 1 (by rfl) ⟨1131605, by rfl⟩ : syracuseStep 1508807 = 2263211) B2263211
theorem B2262491 : Blo 1506950 2262491 := bstep (se 1 (by rfl) ⟨1696868, by rfl⟩ : syracuseStep 2262491 = 3393737) B3393737
theorem B1508827 : Blo 1506950 1508827 := bstep (se 1 (by rfl) ⟨1131620, by rfl⟩ : syracuseStep 1508827 = 2263241) B2263241
theorem B47048197 : Blo 1506950 47048197 := bstep (se 4 (by rfl) ⟨4410768, by rfl⟩ : syracuseStep 47048197 = 8821537) B8821537
theorem B1508903 : Blo 1506950 1508903 := bstep (se 1 (by rfl) ⟨1131677, by rfl⟩ : syracuseStep 1508903 = 2263355) B2263355
theorem B23537213 : Blo 1506950 23537213 := bstep (se 3 (by rfl) ⟨4413227, by rfl⟩ : syracuseStep 23537213 = 8826455) B8826455
theorem B1697359 : Blo 1506950 1697359 := bstep (se 1 (by rfl) ⟨1273019, by rfl⟩ : syracuseStep 1697359 = 2546039) B2546039
theorem B1508943 : Blo 1506950 1508943 := bstep (se 1 (by rfl) ⟨1131707, by rfl⟩ : syracuseStep 1508943 = 2263415) B2263415
theorem B6440647 : Blo 1506950 6440647 := bstep (se 1 (by rfl) ⟨4830485, by rfl⟩ : syracuseStep 6440647 = 9660971) B9660971
theorem B7636679 : Blo 1506950 7636679 := bstep (se 1 (by rfl) ⟨5727509, by rfl⟩ : syracuseStep 7636679 = 11455019) B11455019
theorem B3057401 : Blo 1506950 3057401 := bstep (se 2 (by rfl) ⟨1146525, by rfl⟩ : syracuseStep 3057401 = 2293051) B2293051
theorem B5089067 : Blo 1506950 5089067 := bstep (se 1 (by rfl) ⟨3816800, by rfl⟩ : syracuseStep 5089067 = 7633601) B7633601
theorem B2262959 : Blo 1506950 2262959 := bstep (se 1 (by rfl) ⟨1697219, by rfl⟩ : syracuseStep 2262959 = 3394439) B3394439
theorem B3393467 : Blo 1506950 3393467 := bstep (se 1 (by rfl) ⟨2545100, by rfl⟩ : syracuseStep 3393467 = 5090201) B5090201
theorem B2263049 : Blo 1506950 2263049 := bstep (se 2 (by rfl) ⟨848643, by rfl⟩ : syracuseStep 2263049 = 1697287) B1697287
theorem B2861075 : Blo 1506950 2861075 := bstep (se 1 (by rfl) ⟨2145806, by rfl⟩ : syracuseStep 2861075 = 4291613) B4291613
theorem B2263079 : Blo 1506950 2263079 := bstep (se 1 (by rfl) ⟨1697309, by rfl⟩ : syracuseStep 2263079 = 3394619) B3394619
theorem B5089337 : Blo 1506950 5089337 := bstep (se 2 (by rfl) ⟨1908501, by rfl⟩ : syracuseStep 5089337 = 3817003) B3817003
theorem B3393593 : Blo 1506950 3393593 := bstep (se 2 (by rfl) ⟨1272597, by rfl⟩ : syracuseStep 3393593 = 2545195) B2545195
theorem B24463417 : Blo 1506950 24463417 := bstep (se 2 (by rfl) ⟨9173781, by rfl⟩ : syracuseStep 24463417 = 18347563) B18347563
theorem B2263163 : Blo 1506950 2263163 := bstep (se 1 (by rfl) ⟨1697372, by rfl⟩ : syracuseStep 2263163 = 3394745) B3394745
theorem B2263289 : Blo 1506950 2263289 := bstep (se 2 (by rfl) ⟨848733, by rfl⟩ : syracuseStep 2263289 = 1697467) B1697467
theorem B21743873 : Blo 1506950 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B2263391 : Blo 1506950 2263391 := bstep (se 1 (by rfl) ⟨1697543, by rfl⟩ : syracuseStep 2263391 = 3395087) B3395087
theorem B2263403 : Blo 1506950 2263403 := bstep (se 1 (by rfl) ⟨1697552, by rfl⟩ : syracuseStep 2263403 = 3395105) B3395105
theorem B5089661 : Blo 1506950 5089661 := bstep (se 3 (by rfl) ⟨954311, by rfl⟩ : syracuseStep 5089661 = 1908623) B1908623
theorem B3393935 : Blo 1506950 3393935 := bstep (se 1 (by rfl) ⟨2545451, by rfl⟩ : syracuseStep 3393935 = 5090903) B5090903
theorem B4295177 : Blo 1506950 4295177 := bstep (se 2 (by rfl) ⟨1610691, by rfl⟩ : syracuseStep 4295177 = 3221383) B3221383
theorem B7244423 : Blo 1506950 7244423 := bstep (se 1 (by rfl) ⟨5433317, by rfl⟩ : syracuseStep 7244423 = 10866635) B10866635
theorem B5089931 : Blo 1506950 5089931 := bstep (se 1 (by rfl) ⟨3817448, by rfl⟩ : syracuseStep 5089931 = 7634897) B7634897
theorem B5728907 : Blo 1506950 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B16534217 : Blo 1506950 16534217 := bstep (se 2 (by rfl) ⟨6200331, by rfl⟩ : syracuseStep 16534217 = 12400663) B12400663
theorem B3394259 : Blo 1506950 3394259 := bstep (se 1 (by rfl) ⟨2545694, by rfl⟩ : syracuseStep 3394259 = 5091389) B5091389
theorem B4295531 : Blo 1506950 4295531 := bstep (se 1 (by rfl) ⟨3221648, by rfl⟩ : syracuseStep 4295531 = 6443297) B6443297
theorem B7629875 : Blo 1506950 7629875 := bstep (se 1 (by rfl) ⟨5722406, by rfl⟩ : syracuseStep 7629875 = 11444813) B11444813
theorem B57986117 : Blo 1506950 57986117 := bstep (se 4 (by rfl) ⟨5436198, by rfl⟩ : syracuseStep 57986117 = 10872397) B10872397
theorem B2862479 : Blo 1506950 2862479 := bstep (se 1 (by rfl) ⟨2146859, by rfl⟩ : syracuseStep 2862479 = 4293719) B4293719
theorem B2543035 : Blo 1506950 2543035 := bstep (se 1 (by rfl) ⟨1907276, by rfl⟩ : syracuseStep 2543035 = 3814553) B3814553
theorem B20401651 : Blo 1506950 20401651 := bstep (se 1 (by rfl) ⟨15301238, by rfl⟩ : syracuseStep 20401651 = 30602477) B30602477
theorem B4296179 : Blo 1506950 4296179 := bstep (se 1 (by rfl) ⟨3222134, by rfl⟩ : syracuseStep 4296179 = 6444269) B6444269
theorem B5090849 : Blo 1506950 5090849 := bstep (se 2 (by rfl) ⟨1909068, by rfl⟩ : syracuseStep 5090849 = 3818137) B3818137
theorem B2543143 : Blo 1506950 2543143 := bstep (se 1 (by rfl) ⟨1907357, by rfl⟩ : syracuseStep 2543143 = 3814715) B3814715
theorem B2862631 : Blo 1506950 2862631 := bstep (se 1 (by rfl) ⟨2146973, by rfl⟩ : syracuseStep 2862631 = 4293947) B4293947
theorem B33033815 : Blo 1506950 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B2862715 : Blo 1506950 2862715 := bstep (se 1 (by rfl) ⟨2147036, by rfl⟩ : syracuseStep 2862715 = 4294073) B4294073
theorem B9662075 : Blo 1506950 9662075 := bstep (se 1 (by rfl) ⟨7246556, by rfl⟩ : syracuseStep 9662075 = 14493113) B14493113
theorem B5721785 : Blo 1506950 5721785 := bstep (se 2 (by rfl) ⟨2145669, by rfl⟩ : syracuseStep 5721785 = 4291339) B4291339
theorem B5721799 : Blo 1506950 5721799 := bstep (se 1 (by rfl) ⟨4291349, by rfl⟩ : syracuseStep 5721799 = 8582699) B8582699
theorem B5091065 : Blo 1506950 5091065 := bstep (se 2 (by rfl) ⟨1909149, by rfl⟩ : syracuseStep 5091065 = 3818299) B3818299
theorem B9662303 : Blo 1506950 9662303 := bstep (se 1 (by rfl) ⟨7246727, by rfl⟩ : syracuseStep 9662303 = 14493455) B14493455
theorem B2543467 : Blo 1506950 2543467 := bstep (se 1 (by rfl) ⟨1907600, by rfl⟩ : syracuseStep 2543467 = 3815201) B3815201
theorem B4296635 : Blo 1506950 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B5091335 : Blo 1506950 5091335 := bstep (se 1 (by rfl) ⟨3818501, by rfl⟩ : syracuseStep 5091335 = 7637003) B7637003
theorem B6443023 : Blo 1506950 6443023 := bstep (se 1 (by rfl) ⟨4832267, by rfl⟩ : syracuseStep 6443023 = 9664535) B9664535
theorem B18346013 : Blo 1506950 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B2863201 : Blo 1506950 2863201 := bstep (se 2 (by rfl) ⟨1073700, by rfl⟩ : syracuseStep 2863201 = 2147401) B2147401
theorem B5091443 : Blo 1506950 5091443 := bstep (se 1 (by rfl) ⟨3818582, by rfl⟩ : syracuseStep 5091443 = 7637165) B7637165
theorem B7065917 : Blo 1506950 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B18338177 : Blo 1506950 18338177 := bstep (se 2 (by rfl) ⟨6876816, by rfl⟩ : syracuseStep 18338177 = 13753633) B13753633
theorem B5091713 : Blo 1506950 5091713 := bstep (se 2 (by rfl) ⟨1909392, by rfl⟩ : syracuseStep 5091713 = 3818785) B3818785
theorem B65253761 : Blo 1506950 65253761 := bstep (se 2 (by rfl) ⟨24470160, by rfl⟩ : syracuseStep 65253761 = 48940321) B48940321
theorem B7631495 : Blo 1506950 7631495 := bstep (se 1 (by rfl) ⟨5723621, by rfl⟩ : syracuseStep 7631495 = 11447243) B11447243
theorem B5722771 : Blo 1506950 5722771 := bstep (se 1 (by rfl) ⟨4292078, by rfl⟩ : syracuseStep 5722771 = 8584157) B8584157
theorem B10867385 : Blo 1506950 10867385 := bstep (se 2 (by rfl) ⟨4075269, by rfl⟩ : syracuseStep 10867385 = 8150539) B8150539
theorem B125457187 : Blo 1506950 125457187 := bstep (se 1 (by rfl) ⟨94092890, by rfl⟩ : syracuseStep 125457187 = 188185781) B188185781
theorem B2544527 : Blo 1506950 2544527 := bstep (se 1 (by rfl) ⟨1908395, by rfl⟩ : syracuseStep 2544527 = 3816791) B3816791
theorem B1508731 : Blo 1506950 1508731 := bstep (se 1 (by rfl) ⟨1131548, by rfl⟩ : syracuseStep 1508731 = 2263097) B2263097
theorem B27513751 : Blo 1506950 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B2864135 : Blo 1506950 2864135 := bstep (se 1 (by rfl) ⟨2148101, by rfl⟩ : syracuseStep 2864135 = 4296203) B4296203
theorem B43496513 : Blo 1506950 43496513 := bstep (se 2 (by rfl) ⟨16311192, by rfl⟩ : syracuseStep 43496513 = 32622385) B32622385
theorem B2544763 : Blo 1506950 2544763 := bstep (se 1 (by rfl) ⟨1908572, by rfl⟩ : syracuseStep 2544763 = 3817145) B3817145
theorem B5092523 : Blo 1506950 5092523 := bstep (se 1 (by rfl) ⟨3819392, by rfl⟩ : syracuseStep 5092523 = 7638785) B7638785
theorem B43455689 : Blo 1506950 43455689 := bstep (se 2 (by rfl) ⟨16295883, by rfl⟩ : syracuseStep 43455689 = 32591767) B32591767
theorem B1529167 : Blo 1506950 1529167 := bstep (se 1 (by rfl) ⟨1146875, by rfl⟩ : syracuseStep 1529167 = 2293751) B2293751
theorem B3724649 : Blo 1506950 3724649 := bstep (se 2 (by rfl) ⟨1396743, by rfl⟩ : syracuseStep 3724649 = 2793487) B2793487
theorem B11457935 : Blo 1506950 11457935 := bstep (se 1 (by rfl) ⟨8593451, by rfl⟩ : syracuseStep 11457935 = 17186903) B17186903
theorem B9655847 : Blo 1506950 9655847 := bstep (se 1 (by rfl) ⟨7241885, by rfl⟩ : syracuseStep 9655847 = 14483771) B14483771
theorem B3438119 : Blo 1506950 3438119 := bstep (se 1 (by rfl) ⟨2578589, by rfl⟩ : syracuseStep 3438119 = 5157179) B5157179
theorem B3815009 : Blo 1506950 3815009 := bstep (se 2 (by rfl) ⟨1430628, by rfl⟩ : syracuseStep 3815009 = 2861257) B2861257
theorem B16348769 : Blo 1506950 16348769 := bstep (se 2 (by rfl) ⟨6130788, by rfl⟩ : syracuseStep 16348769 = 12261577) B12261577
theorem B4831049 : Blo 1506950 4831049 := bstep (se 2 (by rfl) ⟨1811643, by rfl⟩ : syracuseStep 4831049 = 3623287) B3623287
theorem B2414443 : Blo 1506950 2414443 := bstep (se 1 (by rfl) ⟨1810832, by rfl⟩ : syracuseStep 2414443 = 3621665) B3621665
theorem B18331601 : Blo 1506950 18331601 := bstep (se 2 (by rfl) ⟨6874350, by rfl⟩ : syracuseStep 18331601 = 13748701) B13748701
theorem B2545627 : Blo 1506950 2545627 := bstep (se 1 (by rfl) ⟨1909220, by rfl⟩ : syracuseStep 2545627 = 3818441) B3818441
theorem B7632953 : Blo 1506950 7632953 := bstep (se 2 (by rfl) ⟨2862357, by rfl⟩ : syracuseStep 7632953 = 5724715) B5724715
theorem B5724503 : Blo 1506950 5724503 := bstep (se 1 (by rfl) ⟨4293377, by rfl⟩ : syracuseStep 5724503 = 8586755) B8586755
theorem B5437961 : Blo 1506950 5437961 := bstep (se 2 (by rfl) ⟨2039235, by rfl⟩ : syracuseStep 5437961 = 4078471) B4078471
theorem B2546255 : Blo 1506950 2546255 := bstep (se 1 (by rfl) ⟨1909691, by rfl⟩ : syracuseStep 2546255 = 3819383) B3819383
theorem B5159623 : Blo 1506950 5159623 := bstep (se 1 (by rfl) ⟨3869717, by rfl⟩ : syracuseStep 5159623 = 7739435) B7739435
theorem B2448119 : Blo 1506950 2448119 := bstep (se 1 (by rfl) ⟨1836089, by rfl⟩ : syracuseStep 2448119 = 3672179) B3672179
theorem B3816467 : Blo 1506950 3816467 := bstep (se 1 (by rfl) ⟨2862350, by rfl⟩ : syracuseStep 3816467 = 5724701) B5724701
theorem B25762859 : Blo 1506950 25762859 := bstep (se 1 (by rfl) ⟨19322144, by rfl⟩ : syracuseStep 25762859 = 38644289) B38644289
theorem B2415673 : Blo 1506950 2415673 := bstep (se 2 (by rfl) ⟨905877, by rfl⟩ : syracuseStep 2415673 = 1811755) B1811755
theorem B8592587 : Blo 1506950 8592587 := bstep (se 1 (by rfl) ⟨6444440, by rfl⟩ : syracuseStep 8592587 = 12888881) B12888881
theorem B5086475 : Blo 1506950 5086475 := bstep (se 1 (by rfl) ⟨3814856, by rfl⟩ : syracuseStep 5086475 = 7629713) B7629713
theorem B8584613 : Blo 1506950 8584613 := bstep (se 4 (by rfl) ⟨804807, by rfl⟩ : syracuseStep 8584613 = 1609615) B1609615
theorem B9665993 : Blo 1506950 9665993 := bstep (se 2 (by rfl) ⟨3624747, by rfl⟩ : syracuseStep 9665993 = 7249495) B7249495
theorem B5086745 : Blo 1506950 5086745 := bstep (se 2 (by rfl) ⟨1907529, by rfl⟩ : syracuseStep 5086745 = 3815059) B3815059
theorem B2260559 : Blo 1506950 2260559 := bstep (se 1 (by rfl) ⟨1695419, by rfl⟩ : syracuseStep 2260559 = 3390839) B3390839
theorem B3391073 : Blo 1506950 3391073 := bstep (se 2 (by rfl) ⟨1271652, by rfl⟩ : syracuseStep 3391073 = 2543305) B2543305
theorem B1506991 : Blo 1506950 1506991 := bstep (se 1 (by rfl) ⟨1130243, by rfl⟩ : syracuseStep 1506991 = 2260487) B2260487
theorem B1507015 : Blo 1506950 1507015 := bstep (se 1 (by rfl) ⟨1130261, by rfl⟩ : syracuseStep 1507015 = 2260523) B2260523
theorem B2260679 : Blo 1506950 2260679 := bstep (se 1 (by rfl) ⟨1695509, by rfl⟩ : syracuseStep 2260679 = 3391019) B3391019
theorem B11452103 : Blo 1506950 11452103 := bstep (se 1 (by rfl) ⟨8589077, by rfl⟩ : syracuseStep 11452103 = 17178155) B17178155
theorem B1507035 : Blo 1506950 1507035 := bstep (se 1 (by rfl) ⟨1130276, by rfl⟩ : syracuseStep 1507035 = 2260553) B2260553
theorem B9789149 : Blo 1506950 9789149 := bstep (se 3 (by rfl) ⟨1835465, by rfl⟩ : syracuseStep 9789149 = 3670931) B3670931
theorem B6438649 : Blo 1506950 6438649 := bstep (se 2 (by rfl) ⟨2414493, by rfl⟩ : syracuseStep 6438649 = 4828987) B4828987
theorem B1507111 : Blo 1506950 1507111 := bstep (se 1 (by rfl) ⟨1130333, by rfl⟩ : syracuseStep 1507111 = 2260667) B2260667
theorem B1507151 : Blo 1506950 1507151 := bstep (se 1 (by rfl) ⟨1130363, by rfl⟩ : syracuseStep 1507151 = 2260727) B2260727
theorem B1507167 : Blo 1506950 1507167 := bstep (se 1 (by rfl) ⟨1130375, by rfl⟩ : syracuseStep 1507167 = 2260751) B2260751
theorem B2260841 : Blo 1506950 2260841 := bstep (se 2 (by rfl) ⟨847815, by rfl⟩ : syracuseStep 2260841 = 1695631) B1695631
theorem B1507195 : Blo 1506950 1507195 := bstep (se 1 (by rfl) ⟨1130396, by rfl⟩ : syracuseStep 1507195 = 2260793) B2260793
theorem B1507247 : Blo 1506950 1507247 := bstep (se 1 (by rfl) ⟨1130435, by rfl⟩ : syracuseStep 1507247 = 2260871) B2260871
theorem B2260919 : Blo 1506950 2260919 := bstep (se 1 (by rfl) ⟨1695689, by rfl⟩ : syracuseStep 2260919 = 3391379) B3391379
theorem B3391415 : Blo 1506950 3391415 := bstep (se 1 (by rfl) ⟨2543561, by rfl⟩ : syracuseStep 3391415 = 5087123) B5087123
theorem B1507271 : Blo 1506950 1507271 := bstep (se 1 (by rfl) ⟨1130453, by rfl⟩ : syracuseStep 1507271 = 2260907) B2260907
theorem B1507291 : Blo 1506950 1507291 := bstep (se 1 (by rfl) ⟨1130468, by rfl⟩ : syracuseStep 1507291 = 2260937) B2260937
theorem B2260955 : Blo 1506950 2260955 := bstep (se 1 (by rfl) ⟨1695716, by rfl⟩ : syracuseStep 2260955 = 3391433) B3391433
theorem B2146267 : Blo 1506950 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B42418187 : Blo 1506950 42418187 := bstep (se 1 (by rfl) ⟨31813640, by rfl⟩ : syracuseStep 42418187 = 63627281) B63627281
theorem B12230675 : Blo 1506950 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B10862711 : Blo 1506950 10862711 := bstep (se 1 (by rfl) ⟨8147033, by rfl⟩ : syracuseStep 10862711 = 16294067) B16294067
theorem B3817601 : Blo 1506950 3817601 := bstep (se 2 (by rfl) ⟨1431600, by rfl⟩ : syracuseStep 3817601 = 2863201) B2863201
theorem B4710611 : Blo 1506950 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B1507615 : Blo 1506950 1507615 := bstep (se 1 (by rfl) ⟨1130711, by rfl⟩ : syracuseStep 1507615 = 2261423) B2261423
theorem B2261339 : Blo 1506950 2261339 := bstep (se 1 (by rfl) ⟨1696004, by rfl⟩ : syracuseStep 2261339 = 3392009) B3392009
theorem B1507675 : Blo 1506950 1507675 := bstep (se 1 (by rfl) ⟨1130756, by rfl⟩ : syracuseStep 1507675 = 2261513) B2261513
theorem B1507695 : Blo 1506950 1507695 := bstep (se 1 (by rfl) ⟨1130771, by rfl⟩ : syracuseStep 1507695 = 2261543) B2261543
theorem B1507751 : Blo 1506950 1507751 := bstep (se 1 (by rfl) ⟨1130813, by rfl⟩ : syracuseStep 1507751 = 2261627) B2261627
theorem B5087663 : Blo 1506950 5087663 := bstep (se 1 (by rfl) ⟨3815747, by rfl⟩ : syracuseStep 5087663 = 7631495) B7631495
theorem B3391919 : Blo 1506950 3391919 := bstep (se 1 (by rfl) ⟨2543939, by rfl⟩ : syracuseStep 3391919 = 5087879) B5087879
theorem B3391955 : Blo 1506950 3391955 := bstep (se 1 (by rfl) ⟨2543966, by rfl⟩ : syracuseStep 3391955 = 5087933) B5087933
theorem B1507835 : Blo 1506950 1507835 := bstep (se 1 (by rfl) ⟨1130876, by rfl⟩ : syracuseStep 1507835 = 2261753) B2261753
theorem B3392063 : Blo 1506950 3392063 := bstep (se 1 (by rfl) ⟨2544047, by rfl⟩ : syracuseStep 3392063 = 5088095) B5088095
theorem B2261567 : Blo 1506950 2261567 := bstep (se 1 (by rfl) ⟨1696175, by rfl⟩ : syracuseStep 2261567 = 3392351) B3392351
theorem B1507903 : Blo 1506950 1507903 := bstep (se 1 (by rfl) ⟨1130927, by rfl⟩ : syracuseStep 1507903 = 2261855) B2261855
theorem B1507911 : Blo 1506950 1507911 := bstep (se 1 (by rfl) ⟨1130933, by rfl⟩ : syracuseStep 1507911 = 2261867) B2261867
theorem B1696351 : Blo 1506950 1696351 := bstep (se 1 (by rfl) ⟨1272263, by rfl⟩ : syracuseStep 1696351 = 2544527) B2544527
theorem B11453075 : Blo 1506950 11453075 := bstep (se 1 (by rfl) ⟨8589806, by rfl⟩ : syracuseStep 11453075 = 17179613) B17179613
theorem B3392171 : Blo 1506950 3392171 := bstep (se 1 (by rfl) ⟨2544128, by rfl⟩ : syracuseStep 3392171 = 5088257) B5088257
theorem B1909423 : Blo 1506950 1909423 := bstep (se 1 (by rfl) ⟨1432067, by rfl⟩ : syracuseStep 1909423 = 2864135) B2864135
theorem B58737335 : Blo 1506950 58737335 := bstep (se 1 (by rfl) ⟨44053001, by rfl⟩ : syracuseStep 58737335 = 88106003) B88106003
theorem B6439607 : Blo 1506950 6439607 := bstep (se 1 (by rfl) ⟨4829705, by rfl⟩ : syracuseStep 6439607 = 9659411) B9659411
theorem B2261687 : Blo 1506950 2261687 := bstep (se 1 (by rfl) ⟨1696265, by rfl⟩ : syracuseStep 2261687 = 3392531) B3392531
theorem B1508063 : Blo 1506950 1508063 := bstep (se 1 (by rfl) ⟨1131047, by rfl⟩ : syracuseStep 1508063 = 2262095) B2262095
theorem B1508143 : Blo 1506950 1508143 := bstep (se 1 (by rfl) ⟨1131107, by rfl⟩ : syracuseStep 1508143 = 2262215) B2262215
theorem B2261915 : Blo 1506950 2261915 := bstep (se 1 (by rfl) ⟨1696436, by rfl⟩ : syracuseStep 2261915 = 3392873) B3392873
theorem B1508251 : Blo 1506950 1508251 := bstep (se 1 (by rfl) ⟨1131188, by rfl⟩ : syracuseStep 1508251 = 2262377) B2262377
theorem B2483099 : Blo 1506950 2483099 := bstep (se 1 (by rfl) ⟨1862324, by rfl⟩ : syracuseStep 2483099 = 3724649) B3724649
theorem B3867563 : Blo 1506950 3867563 := bstep (se 1 (by rfl) ⟨2900672, by rfl⟩ : syracuseStep 3867563 = 5801345) B5801345
theorem B3818411 : Blo 1506950 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B1508303 : Blo 1506950 1508303 := bstep (se 1 (by rfl) ⟨1131227, by rfl⟩ : syracuseStep 1508303 = 2262455) B2262455
theorem B1508327 : Blo 1506950 1508327 := bstep (se 1 (by rfl) ⟨1131245, by rfl⟩ : syracuseStep 1508327 = 2262491) B2262491
theorem B3392711 : Blo 1506950 3392711 := bstep (se 1 (by rfl) ⟨2544533, by rfl⟩ : syracuseStep 3392711 = 5089067) B5089067
theorem B36685001 : Blo 1506950 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B1508639 : Blo 1506950 1508639 := bstep (se 1 (by rfl) ⟨1131479, by rfl⟩ : syracuseStep 1508639 = 2262959) B2262959
theorem B2262311 : Blo 1506950 2262311 := bstep (se 1 (by rfl) ⟨1696733, by rfl⟩ : syracuseStep 2262311 = 3393467) B3393467
theorem B1508699 : Blo 1506950 1508699 := bstep (se 1 (by rfl) ⟨1131524, by rfl⟩ : syracuseStep 1508699 = 2263049) B2263049
theorem B1508719 : Blo 1506950 1508719 := bstep (se 1 (by rfl) ⟨1131539, by rfl⟩ : syracuseStep 1508719 = 2263079) B2263079
theorem B5088635 : Blo 1506950 5088635 := bstep (se 1 (by rfl) ⟨3816476, by rfl⟩ : syracuseStep 5088635 = 7632953) B7632953
theorem B3392891 : Blo 1506950 3392891 := bstep (se 1 (by rfl) ⟨2544668, by rfl⟩ : syracuseStep 3392891 = 5089337) B5089337
theorem B2262395 : Blo 1506950 2262395 := bstep (se 1 (by rfl) ⟨1696796, by rfl⟩ : syracuseStep 2262395 = 3393593) B3393593
theorem B3220897 : Blo 1506950 3220897 := bstep (se 2 (by rfl) ⟨1207836, by rfl⟩ : syracuseStep 3220897 = 2415673) B2415673
theorem B1508775 : Blo 1506950 1508775 := bstep (se 1 (by rfl) ⟨1131581, by rfl⟩ : syracuseStep 1508775 = 2263163) B2263163
theorem B3393017 : Blo 1506950 3393017 := bstep (se 2 (by rfl) ⟨1272381, by rfl⟩ : syracuseStep 3393017 = 2544763) B2544763
theorem B2262521 : Blo 1506950 2262521 := bstep (se 2 (by rfl) ⟨848445, by rfl⟩ : syracuseStep 2262521 = 1696891) B1696891
theorem B1508859 : Blo 1506950 1508859 := bstep (se 1 (by rfl) ⟨1131644, by rfl⟩ : syracuseStep 1508859 = 2263289) B2263289
theorem B1508927 : Blo 1506950 1508927 := bstep (se 1 (by rfl) ⟨1131695, by rfl⟩ : syracuseStep 1508927 = 2263391) B2263391
theorem B1508935 : Blo 1506950 1508935 := bstep (se 1 (by rfl) ⟨1131701, by rfl⟩ : syracuseStep 1508935 = 2263403) B2263403
theorem B3393107 : Blo 1506950 3393107 := bstep (se 1 (by rfl) ⟨2544830, by rfl⟩ : syracuseStep 3393107 = 5089661) B5089661
theorem B2262623 : Blo 1506950 2262623 := bstep (se 1 (by rfl) ⟨1696967, by rfl⟩ : syracuseStep 2262623 = 3393935) B3393935
theorem B1697503 : Blo 1506950 1697503 := bstep (se 1 (by rfl) ⟨1273127, by rfl⟩ : syracuseStep 1697503 = 2546255) B2546255
theorem B3393287 : Blo 1506950 3393287 := bstep (se 1 (by rfl) ⟨2544965, by rfl⟩ : syracuseStep 3393287 = 5089931) B5089931
theorem B3819271 : Blo 1506950 3819271 := bstep (se 1 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 3819271 = 5728907) B5728907
theorem B2262839 : Blo 1506950 2262839 := bstep (se 1 (by rfl) ⟨1697129, by rfl⟩ : syracuseStep 2262839 = 3394259) B3394259
theorem B1632079 : Blo 1506950 1632079 := bstep (se 1 (by rfl) ⟨1224059, by rfl⟩ : syracuseStep 1632079 = 2448119) B2448119
theorem B7636841 : Blo 1506950 7636841 := bstep (se 2 (by rfl) ⟨2863815, by rfl⟩ : syracuseStep 7636841 = 5727631) B5727631
theorem B44091245 : Blo 1506950 44091245 := bstep (se 3 (by rfl) ⟨8267108, by rfl⟩ : syracuseStep 44091245 = 16534217) B16534217
theorem B19318661 : Blo 1506950 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B2263145 : Blo 1506950 2263145 := bstep (se 2 (by rfl) ⟨848679, by rfl⟩ : syracuseStep 2263145 = 1697359) B1697359
theorem B5728391 : Blo 1506950 5728391 := bstep (se 1 (by rfl) ⟨4296293, by rfl⟩ : syracuseStep 5728391 = 8592587) B8592587
theorem B7629065 : Blo 1506950 7629065 := bstep (se 2 (by rfl) ⟨2860899, by rfl⟩ : syracuseStep 7629065 = 5721799) B5721799
theorem B8587529 : Blo 1506950 8587529 := bstep (se 2 (by rfl) ⟨3220323, by rfl⟩ : syracuseStep 8587529 = 6440647) B6440647
theorem B3393899 : Blo 1506950 3393899 := bstep (se 1 (by rfl) ⟨2545424, by rfl⟩ : syracuseStep 3393899 = 5090849) B5090849
theorem B22022543 : Blo 1506950 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B6441383 : Blo 1506950 6441383 := bstep (se 1 (by rfl) ⟨4831037, by rfl⟩ : syracuseStep 6441383 = 9662075) B9662075
theorem B11446757 : Blo 1506950 11446757 := bstep (se 4 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 11446757 = 2146267) B2146267
theorem B3394043 : Blo 1506950 3394043 := bstep (se 1 (by rfl) ⟨2545532, by rfl⟩ : syracuseStep 3394043 = 5091065) B5091065
theorem B48884269 : Blo 1506950 48884269 := bstep (se 3 (by rfl) ⟨9165800, by rfl⟩ : syracuseStep 48884269 = 18331601) B18331601
theorem B6441535 : Blo 1506950 6441535 := bstep (se 1 (by rfl) ⟨4831151, by rfl⟩ : syracuseStep 6441535 = 9662303) B9662303
theorem B108808805 : Blo 1506950 108808805 := bstep (se 4 (by rfl) ⟨10200825, by rfl⟩ : syracuseStep 108808805 = 20401651) B20401651
theorem B3394169 : Blo 1506950 3394169 := bstep (se 2 (by rfl) ⟨1272813, by rfl⟩ : syracuseStep 3394169 = 2545627) B2545627
theorem B2861743 : Blo 1506950 2861743 := bstep (se 1 (by rfl) ⟨2146307, by rfl⟩ : syracuseStep 2861743 = 4292615) B4292615
theorem B3394223 : Blo 1506950 3394223 := bstep (se 1 (by rfl) ⟨2545667, by rfl⟩ : syracuseStep 3394223 = 5091335) B5091335
theorem B5090039 : Blo 1506950 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B3394295 : Blo 1506950 3394295 := bstep (se 1 (by rfl) ⟨2545721, by rfl⟩ : syracuseStep 3394295 = 5091443) B5091443
theorem B12225451 : Blo 1506950 12225451 := bstep (se 1 (by rfl) ⟨9169088, by rfl⟩ : syracuseStep 12225451 = 18338177) B18338177
theorem B3394475 : Blo 1506950 3394475 := bstep (se 1 (by rfl) ⟨2545856, by rfl⟩ : syracuseStep 3394475 = 5091713) B5091713
theorem B43502507 : Blo 1506950 43502507 := bstep (se 1 (by rfl) ⟨32626880, by rfl⟩ : syracuseStep 43502507 = 65253761) B65253761
theorem B3222443 : Blo 1506950 3222443 := bstep (se 1 (by rfl) ⟨2416832, by rfl⟩ : syracuseStep 3222443 = 4833665) B4833665
theorem B7244923 : Blo 1506950 7244923 := bstep (se 1 (by rfl) ⟨5433692, by rfl⟩ : syracuseStep 7244923 = 10867385) B10867385
theorem B7630199 : Blo 1506950 7630199 := bstep (se 1 (by rfl) ⟨5722649, by rfl⟩ : syracuseStep 7630199 = 11445299) B11445299
theorem B13053383 : Blo 1506950 13053383 := bstep (se 1 (by rfl) ⟨9790037, by rfl⟩ : syracuseStep 13053383 = 19580075) B19580075
theorem B3395015 : Blo 1506950 3395015 := bstep (se 1 (by rfl) ⟨2546261, by rfl⟩ : syracuseStep 3395015 = 5092523) B5092523
theorem B28970459 : Blo 1506950 28970459 := bstep (se 1 (by rfl) ⟨21727844, by rfl⟩ : syracuseStep 28970459 = 43455689) B43455689
theorem B5582351 : Blo 1506950 5582351 := bstep (se 1 (by rfl) ⟨4186763, by rfl⟩ : syracuseStep 5582351 = 8373527) B8373527
theorem B7630361 : Blo 1506950 7630361 := bstep (se 2 (by rfl) ⟨2861385, by rfl⟩ : syracuseStep 7630361 = 5722771) B5722771
theorem B7638623 : Blo 1506950 7638623 := bstep (se 1 (by rfl) ⟨5728967, by rfl⟩ : syracuseStep 7638623 = 11457935) B11457935
theorem B15691475 : Blo 1506950 15691475 := bstep (se 1 (by rfl) ⟨11768606, by rfl⟩ : syracuseStep 15691475 = 23537213) B23537213
theorem B167276249 : Blo 1506950 167276249 := bstep (se 2 (by rfl) ⟨62728593, by rfl⟩ : syracuseStep 167276249 = 125457187) B125457187
theorem B2543339 : Blo 1506950 2543339 := bstep (se 1 (by rfl) ⟨1907504, by rfl⟩ : syracuseStep 2543339 = 3815009) B3815009
theorem B10899179 : Blo 1506950 10899179 := bstep (se 1 (by rfl) ⟨8174384, by rfl⟩ : syracuseStep 10899179 = 16348769) B16348769
theorem B5091119 : Blo 1506950 5091119 := bstep (se 1 (by rfl) ⟨3818339, by rfl⟩ : syracuseStep 5091119 = 7636679) B7636679
theorem B25775981 : Blo 1506950 25775981 := bstep (se 3 (by rfl) ⟨4832996, by rfl⟩ : syracuseStep 25775981 = 9665993) B9665993
theorem B11456477 : Blo 1506950 11456477 := bstep (se 3 (by rfl) ⟨2148089, by rfl⟩ : syracuseStep 11456477 = 4296179) B4296179
theorem B14495915 : Blo 1506950 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B2863451 : Blo 1506950 2863451 := bstep (se 1 (by rfl) ⟨2147588, by rfl⟩ : syracuseStep 2863451 = 4295177) B4295177
theorem B3625307 : Blo 1506950 3625307 := bstep (se 1 (by rfl) ⟨2718980, by rfl⟩ : syracuseStep 3625307 = 5437961) B5437961
theorem B4829615 : Blo 1506950 4829615 := bstep (se 1 (by rfl) ⟨3622211, by rfl⟩ : syracuseStep 4829615 = 7244423) B7244423
theorem B2863687 : Blo 1506950 2863687 := bstep (se 1 (by rfl) ⟨2147765, by rfl⟩ : syracuseStep 2863687 = 4295531) B4295531
theorem B62730929 : Blo 1506950 62730929 := bstep (se 2 (by rfl) ⟨23524098, by rfl⟩ : syracuseStep 62730929 = 47048197) B47048197
theorem B2544311 : Blo 1506950 2544311 := bstep (se 1 (by rfl) ⟨1908233, by rfl⟩ : syracuseStep 2544311 = 3816467) B3816467
theorem B17175239 : Blo 1506950 17175239 := bstep (se 1 (by rfl) ⟨12881429, by rfl⟩ : syracuseStep 17175239 = 25762859) B25762859
theorem B12882797 : Blo 1506950 12882797 := bstep (se 3 (by rfl) ⟨2415524, by rfl⟩ : syracuseStep 12882797 = 4831049) B4831049
theorem B5723075 : Blo 1506950 5723075 := bstep (se 1 (by rfl) ⟨4292306, by rfl⟩ : syracuseStep 5723075 = 8584613) B8584613
theorem B3814523 : Blo 1506950 3814523 := bstep (se 1 (by rfl) ⟨2860892, by rfl⟩ : syracuseStep 3814523 = 5721785) B5721785
theorem B6526099 : Blo 1506950 6526099 := bstep (se 1 (by rfl) ⟨4894574, by rfl⟩ : syracuseStep 6526099 = 9789149) B9789149
theorem B2864423 : Blo 1506950 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B8590697 : Blo 1506950 8590697 := bstep (se 2 (by rfl) ⟨3221511, by rfl⟩ : syracuseStep 8590697 = 6443023) B6443023
theorem B2545033 : Blo 1506950 2545033 := bstep (se 2 (by rfl) ⟨954387, by rfl⟩ : syracuseStep 2545033 = 1908775) B1908775
theorem B5723531 : Blo 1506950 5723531 := bstep (se 1 (by rfl) ⟨4292648, by rfl⟩ : syracuseStep 5723531 = 8585297) B8585297
theorem B32617889 : Blo 1506950 32617889 := bstep (se 2 (by rfl) ⟨12231708, by rfl⟩ : syracuseStep 32617889 = 24463417) B24463417
theorem B7345799 : Blo 1506950 7345799 := bstep (se 1 (by rfl) ⟨5509349, by rfl⟩ : syracuseStep 7345799 = 11018699) B11018699
theorem B6444679 : Blo 1506950 6444679 := bstep (se 1 (by rfl) ⟨4833509, by rfl⟩ : syracuseStep 6444679 = 9667019) B9667019
theorem B109991681 : Blo 1506950 109991681 := bstep (se 2 (by rfl) ⟨41246880, by rfl⟩ : syracuseStep 109991681 = 82493761) B82493761
theorem B2545465 : Blo 1506950 2545465 := bstep (se 2 (by rfl) ⟨954549, by rfl⟩ : syracuseStep 2545465 = 1909099) B1909099
theorem B8149025 : Blo 1506950 8149025 := bstep (se 2 (by rfl) ⟨3055884, by rfl⟩ : syracuseStep 8149025 = 6111769) B6111769
theorem B28997675 : Blo 1506950 28997675 := bstep (se 1 (by rfl) ⟨21748256, by rfl⟩ : syracuseStep 28997675 = 43496513) B43496513
theorem B2545769 : Blo 1506950 2545769 := bstep (se 2 (by rfl) ⟨954663, by rfl⟩ : syracuseStep 2545769 = 1909327) B1909327
theorem B6879497 : Blo 1506950 6879497 := bstep (se 2 (by rfl) ⟨2579811, by rfl⟩ : syracuseStep 6879497 = 5159623) B5159623
theorem B7444759 : Blo 1506950 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B6437231 : Blo 1506950 6437231 := bstep (se 1 (by rfl) ⟨4827923, by rfl⟩ : syracuseStep 6437231 = 9655847) B9655847
theorem B2292079 : Blo 1506950 2292079 := bstep (se 1 (by rfl) ⟨1719059, by rfl⟩ : syracuseStep 2292079 = 3438119) B3438119
theorem B7633277 : Blo 1506950 7633277 := bstep (se 3 (by rfl) ⟨1431239, by rfl⟩ : syracuseStep 7633277 = 2862479) B2862479
theorem B2038267 : Blo 1506950 2038267 := bstep (se 1 (by rfl) ⟨1528700, by rfl⟩ : syracuseStep 2038267 = 3057401) B3057401
theorem B1907383 : Blo 1506950 1907383 := bstep (se 1 (by rfl) ⟨1430537, by rfl⟩ : syracuseStep 1907383 = 2861075) B2861075
theorem B3816335 : Blo 1506950 3816335 := bstep (se 1 (by rfl) ⟨2862251, by rfl⟩ : syracuseStep 3816335 = 5724503) B5724503
theorem B2038889 : Blo 1506950 2038889 := bstep (se 2 (by rfl) ⟨764583, by rfl⟩ : syracuseStep 2038889 = 1529167) B1529167
theorem B3390713 : Blo 1506950 3390713 := bstep (se 2 (by rfl) ⟨1271517, by rfl⟩ : syracuseStep 3390713 = 2543035) B2543035
theorem B5086583 : Blo 1506950 5086583 := bstep (se 1 (by rfl) ⟨3814937, by rfl⟩ : syracuseStep 5086583 = 7629875) B7629875
theorem B38657411 : Blo 1506950 38657411 := bstep (se 1 (by rfl) ⟨28993058, by rfl⟩ : syracuseStep 38657411 = 57986117) B57986117
theorem B3390857 : Blo 1506950 3390857 := bstep (se 2 (by rfl) ⟨1271571, by rfl⟩ : syracuseStep 3390857 = 2543143) B2543143
theorem B3816841 : Blo 1506950 3816841 := bstep (se 2 (by rfl) ⟨1431315, by rfl⟩ : syracuseStep 3816841 = 2862631) B2862631
theorem B3816953 : Blo 1506950 3816953 := bstep (se 2 (by rfl) ⟨1431357, by rfl⟩ : syracuseStep 3816953 = 2862715) B2862715
theorem B3390983 : Blo 1506950 3390983 := bstep (se 1 (by rfl) ⟨2543237, by rfl⟩ : syracuseStep 3390983 = 5086475) B5086475
theorem B8584865 : Blo 1506950 8584865 := bstep (se 2 (by rfl) ⟨3219324, by rfl⟩ : syracuseStep 8584865 = 6438649) B6438649
theorem B3391163 : Blo 1506950 3391163 := bstep (se 1 (by rfl) ⟨2543372, by rfl⟩ : syracuseStep 3391163 = 5086745) B5086745
theorem B1507039 : Blo 1506950 1507039 := bstep (se 1 (by rfl) ⟨1130279, by rfl⟩ : syracuseStep 1507039 = 2260559) B2260559
theorem B2260715 : Blo 1506950 2260715 := bstep (se 1 (by rfl) ⟨1695536, by rfl⟩ : syracuseStep 2260715 = 3391073) B3391073
theorem B1507119 : Blo 1506950 1507119 := bstep (se 1 (by rfl) ⟨1130339, by rfl⟩ : syracuseStep 1507119 = 2260679) B2260679
theorem B7634735 : Blo 1506950 7634735 := bstep (se 1 (by rfl) ⟨5726051, by rfl⟩ : syracuseStep 7634735 = 11452103) B11452103
theorem B3391289 : Blo 1506950 3391289 := bstep (se 2 (by rfl) ⟨1271733, by rfl⟩ : syracuseStep 3391289 = 2543467) B2543467
theorem B3219257 : Blo 1506950 3219257 := bstep (se 2 (by rfl) ⟨1207221, by rfl⟩ : syracuseStep 3219257 = 2414443) B2414443
theorem B1507227 : Blo 1506950 1507227 := bstep (se 1 (by rfl) ⟨1130420, by rfl⟩ : syracuseStep 1507227 = 2260841) B2260841
theorem B1507279 : Blo 1506950 1507279 := bstep (se 1 (by rfl) ⟨1130459, by rfl⟩ : syracuseStep 1507279 = 2260919) B2260919
theorem B2260943 : Blo 1506950 2260943 := bstep (se 1 (by rfl) ⟨1695707, by rfl⟩ : syracuseStep 2260943 = 3391415) B3391415
theorem B1507303 : Blo 1506950 1507303 := bstep (se 1 (by rfl) ⟨1130477, by rfl⟩ : syracuseStep 1507303 = 2260955) B2260955
theorem B28278791 : Blo 1506950 28278791 := bstep (se 1 (by rfl) ⟨21209093, by rfl⟩ : syracuseStep 28278791 = 42418187) B42418187
theorem B7241807 : Blo 1506950 7241807 := bstep (se 1 (by rfl) ⟨5431355, by rfl⟩ : syracuseStep 7241807 = 10862711) B10862711
theorem B1507559 : Blo 1506950 1507559 := bstep (se 1 (by rfl) ⟨1130669, by rfl⟩ : syracuseStep 1507559 = 2261339) B2261339
theorem B2416871 : Blo 1506950 2416871 := bstep (se 1 (by rfl) ⟨1812653, by rfl⟩ : syracuseStep 2416871 = 3625307) B3625307
theorem B3391775 : Blo 1506950 3391775 := bstep (se 1 (by rfl) ⟨2543831, by rfl⟩ : syracuseStep 3391775 = 5087663) B5087663
theorem B2261279 : Blo 1506950 2261279 := bstep (se 1 (by rfl) ⟨1695959, by rfl⟩ : syracuseStep 2261279 = 3391919) B3391919
theorem B3219743 : Blo 1506950 3219743 := bstep (se 1 (by rfl) ⟨2414807, by rfl⟩ : syracuseStep 3219743 = 4829615) B4829615
theorem B2261303 : Blo 1506950 2261303 := bstep (se 1 (by rfl) ⟨1695977, by rfl⟩ : syracuseStep 2261303 = 3391955) B3391955
theorem B2261375 : Blo 1506950 2261375 := bstep (se 1 (by rfl) ⟨1696031, by rfl⟩ : syracuseStep 2261375 = 3392063) B3392063
theorem B1507711 : Blo 1506950 1507711 := bstep (se 1 (by rfl) ⟨1130783, by rfl⟩ : syracuseStep 1507711 = 2261567) B2261567
theorem B7635383 : Blo 1506950 7635383 := bstep (se 1 (by rfl) ⟨5726537, by rfl⟩ : syracuseStep 7635383 = 11453075) B11453075
theorem B2261447 : Blo 1506950 2261447 := bstep (se 1 (by rfl) ⟨1696085, by rfl⟩ : syracuseStep 2261447 = 3392171) B3392171
theorem B41820619 : Blo 1506950 41820619 := bstep (se 1 (by rfl) ⟨31365464, by rfl⟩ : syracuseStep 41820619 = 62730929) B62730929
theorem B4293071 : Blo 1506950 4293071 := bstep (se 1 (by rfl) ⟨3219803, by rfl⟩ : syracuseStep 4293071 = 6439607) B6439607
theorem B1696207 : Blo 1506950 1696207 := bstep (se 1 (by rfl) ⟨1272155, by rfl⟩ : syracuseStep 1696207 = 2544311) B2544311
theorem B1507791 : Blo 1506950 1507791 := bstep (se 1 (by rfl) ⟨1130843, by rfl⟩ : syracuseStep 1507791 = 2261687) B2261687
theorem B3056105 : Blo 1506950 3056105 := bstep (se 2 (by rfl) ⟨1146039, by rfl⟩ : syracuseStep 3056105 = 2292079) B2292079
theorem B1507943 : Blo 1506950 1507943 := bstep (se 1 (by rfl) ⟨1130957, by rfl⟩ : syracuseStep 1507943 = 2261915) B2261915
theorem B1655399 : Blo 1506950 1655399 := bstep (se 1 (by rfl) ⟨1241549, by rfl⟩ : syracuseStep 1655399 = 2483099) B2483099
theorem B3818249 : Blo 1506950 3818249 := bstep (se 2 (by rfl) ⟨1431843, by rfl⟩ : syracuseStep 3818249 = 2863687) B2863687
theorem B2261801 : Blo 1506950 2261801 := bstep (se 2 (by rfl) ⟨848175, by rfl⟩ : syracuseStep 2261801 = 1696351) B1696351
theorem B2261807 : Blo 1506950 2261807 := bstep (se 1 (by rfl) ⟨1696355, by rfl⟩ : syracuseStep 2261807 = 3392711) B3392711
theorem B1508207 : Blo 1506950 1508207 := bstep (se 1 (by rfl) ⟨1131155, by rfl⟩ : syracuseStep 1508207 = 2262311) B2262311
theorem B7635869 : Blo 1506950 7635869 := bstep (se 3 (by rfl) ⟨1431725, by rfl⟩ : syracuseStep 7635869 = 2863451) B2863451
theorem B5727131 : Blo 1506950 5727131 := bstep (se 1 (by rfl) ⟨4295348, by rfl⟩ : syracuseStep 5727131 = 8590697) B8590697
theorem B3392423 : Blo 1506950 3392423 := bstep (se 1 (by rfl) ⟨2544317, by rfl⟩ : syracuseStep 3392423 = 5088635) B5088635
theorem B2261927 : Blo 1506950 2261927 := bstep (se 1 (by rfl) ⟨1696445, by rfl⟩ : syracuseStep 2261927 = 3392891) B3392891
theorem B1508263 : Blo 1506950 1508263 := bstep (se 1 (by rfl) ⟨1131197, by rfl⟩ : syracuseStep 1508263 = 2262395) B2262395
theorem B2262011 : Blo 1506950 2262011 := bstep (se 1 (by rfl) ⟨1696508, by rfl⟩ : syracuseStep 2262011 = 3393017) B3393017
theorem B1508347 : Blo 1506950 1508347 := bstep (se 1 (by rfl) ⟨1131260, by rfl⟩ : syracuseStep 1508347 = 2262521) B2262521
theorem B2262071 : Blo 1506950 2262071 := bstep (se 1 (by rfl) ⟨1696553, by rfl⟩ : syracuseStep 2262071 = 3393107) B3393107
theorem B1508415 : Blo 1506950 1508415 := bstep (se 1 (by rfl) ⟨1131311, by rfl⟩ : syracuseStep 1508415 = 2262623) B2262623
theorem B73327787 : Blo 1506950 73327787 := bstep (se 1 (by rfl) ⟨54995840, by rfl⟩ : syracuseStep 73327787 = 109991681) B109991681
theorem B2262191 : Blo 1506950 2262191 := bstep (se 1 (by rfl) ⟨1696643, by rfl⟩ : syracuseStep 2262191 = 3393287) B3393287
theorem B1508559 : Blo 1506950 1508559 := bstep (se 1 (by rfl) ⟨1131419, by rfl⟩ : syracuseStep 1508559 = 2262839) B2262839
theorem B29394163 : Blo 1506950 29394163 := bstep (se 1 (by rfl) ⟨22045622, by rfl⟩ : syracuseStep 29394163 = 44091245) B44091245
theorem B12879107 : Blo 1506950 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B5432683 : Blo 1506950 5432683 := bstep (se 1 (by rfl) ⟨4074512, by rfl⟩ : syracuseStep 5432683 = 8149025) B8149025
theorem B14886269 : Blo 1506950 14886269 := bstep (se 3 (by rfl) ⟨2791175, by rfl⟩ : syracuseStep 14886269 = 5582351) B5582351
theorem B1697179 : Blo 1506950 1697179 := bstep (se 1 (by rfl) ⟨1272884, by rfl⟩ : syracuseStep 1697179 = 2545769) B2545769
theorem B1508763 : Blo 1506950 1508763 := bstep (se 1 (by rfl) ⟨1131572, by rfl⟩ : syracuseStep 1508763 = 2263145) B2263145
theorem B3818927 : Blo 1506950 3818927 := bstep (se 1 (by rfl) ⟨2864195, by rfl⟩ : syracuseStep 3818927 = 5728391) B5728391
theorem B9659897 : Blo 1506950 9659897 := bstep (se 2 (by rfl) ⟨3622461, by rfl⟩ : syracuseStep 9659897 = 7244923) B7244923
theorem B8701465 : Blo 1506950 8701465 := bstep (se 2 (by rfl) ⟨3263049, by rfl⟩ : syracuseStep 8701465 = 6526099) B6526099
theorem B2262599 : Blo 1506950 2262599 := bstep (se 1 (by rfl) ⟨1696949, by rfl⟩ : syracuseStep 2262599 = 3393899) B3393899
theorem B5088851 : Blo 1506950 5088851 := bstep (se 1 (by rfl) ⟨3816638, by rfl⟩ : syracuseStep 5088851 = 7633277) B7633277
theorem B14681695 : Blo 1506950 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B4294255 : Blo 1506950 4294255 := bstep (se 1 (by rfl) ⟨3220691, by rfl⟩ : syracuseStep 4294255 = 6441383) B6441383
theorem B2262695 : Blo 1506950 2262695 := bstep (se 1 (by rfl) ⟨1697021, by rfl⟩ : syracuseStep 2262695 = 3394043) B3394043
theorem B2262779 : Blo 1506950 2262779 := bstep (se 1 (by rfl) ⟨1697084, by rfl⟩ : syracuseStep 2262779 = 3394169) B3394169
theorem B2262815 : Blo 1506950 2262815 := bstep (se 1 (by rfl) ⟨1697111, by rfl⟩ : syracuseStep 2262815 = 3394223) B3394223
theorem B3393359 : Blo 1506950 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B2262863 : Blo 1506950 2262863 := bstep (se 1 (by rfl) ⟨1697147, by rfl⟩ : syracuseStep 2262863 = 3394295) B3394295
theorem B5089121 : Blo 1506950 5089121 := bstep (se 2 (by rfl) ⟨1908420, by rfl⟩ : syracuseStep 5089121 = 3816841) B3816841
theorem B3393377 : Blo 1506950 3393377 := bstep (se 2 (by rfl) ⟨1272516, by rfl⟩ : syracuseStep 3393377 = 2545033) B2545033
theorem B4294529 : Blo 1506950 4294529 := bstep (se 2 (by rfl) ⟨1610448, by rfl⟩ : syracuseStep 4294529 = 3220897) B3220897
theorem B2262983 : Blo 1506950 2262983 := bstep (se 1 (by rfl) ⟨1697237, by rfl⟩ : syracuseStep 2262983 = 3394475) B3394475
theorem B29001671 : Blo 1506950 29001671 := bstep (se 1 (by rfl) ⟨21751253, by rfl⟩ : syracuseStep 29001671 = 43502507) B43502507
theorem B2148295 : Blo 1506950 2148295 := bstep (se 1 (by rfl) ⟨1611221, by rfl⟩ : syracuseStep 2148295 = 3222443) B3222443
theorem B2263337 : Blo 1506950 2263337 := bstep (se 2 (by rfl) ⟨848751, by rfl⟩ : syracuseStep 2263337 = 1697503) B1697503
theorem B8702255 : Blo 1506950 8702255 := bstep (se 1 (by rfl) ⟨6526691, by rfl⟩ : syracuseStep 8702255 = 13053383) B13053383
theorem B2263343 : Blo 1506950 2263343 := bstep (se 1 (by rfl) ⟨1697507, by rfl⟩ : syracuseStep 2263343 = 3395015) B3395015
theorem B3393953 : Blo 1506950 3393953 := bstep (se 2 (by rfl) ⟨1272732, by rfl⟩ : syracuseStep 3393953 = 2545465) B2545465
theorem B5089823 : Blo 1506950 5089823 := bstep (se 1 (by rfl) ⟨3817367, by rfl⟩ : syracuseStep 5089823 = 7634735) B7634735
theorem B3394079 : Blo 1506950 3394079 := bstep (se 1 (by rfl) ⟨2545559, by rfl⟩ : syracuseStep 3394079 = 5091119) B5091119
theorem B7637651 : Blo 1506950 7637651 := bstep (se 1 (by rfl) ⟨5728238, by rfl⟩ : syracuseStep 7637651 = 11456477) B11456477
theorem B8153783 : Blo 1506950 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B3140407 : Blo 1506950 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B8588531 : Blo 1506950 8588531 := bstep (se 1 (by rfl) ⟨6441398, by rfl⟩ : syracuseStep 8588531 = 12882797) B12882797
theorem B65179025 : Blo 1506950 65179025 := bstep (se 2 (by rfl) ⟨24442134, by rfl⟩ : syracuseStep 65179025 = 48884269) B48884269
theorem B2543015 : Blo 1506950 2543015 := bstep (se 1 (by rfl) ⟨1907261, by rfl⟩ : syracuseStep 2543015 = 3814523) B3814523
theorem B8588713 : Blo 1506950 8588713 := bstep (se 2 (by rfl) ⟨3220767, by rfl⟩ : syracuseStep 8588713 = 6441535) B6441535
theorem B7638461 : Blo 1506950 7638461 := bstep (se 3 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 7638461 = 2864423) B2864423
theorem B24456667 : Blo 1506950 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B2543177 : Blo 1506950 2543177 := bstep (se 2 (by rfl) ⟨953691, by rfl⟩ : syracuseStep 2543177 = 1907383) B1907383
theorem B21745259 : Blo 1506950 21745259 := bstep (se 1 (by rfl) ⟨16308944, by rfl⟩ : syracuseStep 21745259 = 32617889) B32617889
theorem B5091227 : Blo 1506950 5091227 := bstep (se 1 (by rfl) ⟨3818420, by rfl⟩ : syracuseStep 5091227 = 7636841) B7636841
theorem B290156813 : Blo 1506950 290156813 := bstep (se 3 (by rfl) ⟨54404402, by rfl⟩ : syracuseStep 290156813 = 108808805) B108808805
theorem B7631171 : Blo 1506950 7631171 := bstep (se 1 (by rfl) ⟨5723378, by rfl⟩ : syracuseStep 7631171 = 11446757) B11446757
theorem B8704421 : Blo 1506950 8704421 := bstep (se 4 (by rfl) ⟨816039, by rfl⟩ : syracuseStep 8704421 = 1632079) B1632079
theorem B465031637 : Blo 1506950 465031637 := bstep (se 7 (by rfl) ⟨5449589, by rfl⟩ : syracuseStep 465031637 = 10899179) B10899179
theorem B2544223 : Blo 1506950 2544223 := bstep (se 1 (by rfl) ⟨1908167, by rfl⟩ : syracuseStep 2544223 = 3816335) B3816335
theorem B19313639 : Blo 1506950 19313639 := bstep (se 1 (by rfl) ⟨14485229, by rfl⟩ : syracuseStep 19313639 = 28970459) B28970459
theorem B2544635 : Blo 1506950 2544635 := bstep (se 1 (by rfl) ⟨1908476, by rfl⟩ : syracuseStep 2544635 = 3816953) B3816953
theorem B5092361 : Blo 1506950 5092361 := bstep (se 2 (by rfl) ⟨1909635, by rfl⟩ : syracuseStep 5092361 = 3819271) B3819271
theorem B5092415 : Blo 1506950 5092415 := bstep (se 1 (by rfl) ⟨3819311, by rfl⟩ : syracuseStep 5092415 = 7638623) B7638623
theorem B5723243 : Blo 1506950 5723243 := bstep (se 1 (by rfl) ⟨4292432, by rfl⟩ : syracuseStep 5723243 = 8584865) B8584865
theorem B17183987 : Blo 1506950 17183987 := bstep (se 1 (by rfl) ⟨12887990, by rfl⟩ : syracuseStep 17183987 = 25775981) B25775981
theorem B2545067 : Blo 1506950 2545067 := bstep (se 1 (by rfl) ⟨1908800, by rfl⟩ : syracuseStep 2545067 = 3817601) B3817601
theorem B73381301 : Blo 1506950 73381301 := bstep (se 5 (by rfl) ⟨3439748, by rfl⟩ : syracuseStep 73381301 = 6879497) B6879497
theorem B9663943 : Blo 1506950 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B5437037 : Blo 1506950 5437037 := bstep (se 3 (by rfl) ⟨1019444, by rfl⟩ : syracuseStep 5437037 = 2038889) B2038889
theorem B9926345 : Blo 1506950 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B11450159 : Blo 1506950 11450159 := bstep (se 1 (by rfl) ⟨8587619, by rfl⟩ : syracuseStep 11450159 = 17175239) B17175239
theorem B2578375 : Blo 1506950 2578375 := bstep (se 1 (by rfl) ⟨1933781, by rfl⟩ : syracuseStep 2578375 = 3867563) B3867563
theorem B2545607 : Blo 1506950 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B3815383 : Blo 1506950 3815383 := bstep (se 1 (by rfl) ⟨2861537, by rfl⟩ : syracuseStep 3815383 = 5723075) B5723075
theorem B3815657 : Blo 1506950 3815657 := bstep (se 2 (by rfl) ⟨1430871, by rfl⟩ : syracuseStep 3815657 = 2861743) B2861743
theorem B2545897 : Blo 1506950 2545897 := bstep (se 2 (by rfl) ⟨954711, by rfl⟩ : syracuseStep 2545897 = 1909423) B1909423
theorem B3815687 : Blo 1506950 3815687 := bstep (se 1 (by rfl) ⟨2861765, by rfl⟩ : syracuseStep 3815687 = 5723531) B5723531
theorem B4897199 : Blo 1506950 4897199 := bstep (se 1 (by rfl) ⟨3672899, by rfl⟩ : syracuseStep 4897199 = 7345799) B7345799
theorem B16300601 : Blo 1506950 16300601 := bstep (se 2 (by rfl) ⟨6112725, by rfl⟩ : syracuseStep 16300601 = 12225451) B12225451
theorem B19331783 : Blo 1506950 19331783 := bstep (se 1 (by rfl) ⟨14498837, by rfl⟩ : syracuseStep 19331783 = 28997675) B28997675
theorem B5086043 : Blo 1506950 5086043 := bstep (se 1 (by rfl) ⟨3814532, by rfl⟩ : syracuseStep 5086043 = 7629065) B7629065
theorem B5725019 : Blo 1506950 5725019 := bstep (se 1 (by rfl) ⟨4293764, by rfl⟩ : syracuseStep 5725019 = 8587529) B8587529
theorem B4291487 : Blo 1506950 4291487 := bstep (se 1 (by rfl) ⟨3218615, by rfl⟩ : syracuseStep 4291487 = 6437231) B6437231
theorem B626531573 : Blo 1506950 626531573 := bstep (se 5 (by rfl) ⟨29368667, by rfl⟩ : syracuseStep 626531573 = 58737335) B58737335
theorem B2260475 : Blo 1506950 2260475 := bstep (se 1 (by rfl) ⟨1695356, by rfl⟩ : syracuseStep 2260475 = 3390713) B3390713
theorem B8592905 : Blo 1506950 8592905 := bstep (se 2 (by rfl) ⟨3222339, by rfl⟩ : syracuseStep 8592905 = 6444679) B6444679
theorem B3391055 : Blo 1506950 3391055 := bstep (se 1 (by rfl) ⟨2543291, by rfl⟩ : syracuseStep 3391055 = 5086583) B5086583
theorem B5086799 : Blo 1506950 5086799 := bstep (se 1 (by rfl) ⟨3815099, by rfl⟩ : syracuseStep 5086799 = 7630199) B7630199
theorem B25771607 : Blo 1506950 25771607 := bstep (se 1 (by rfl) ⟨19328705, by rfl⟩ : syracuseStep 25771607 = 38657411) B38657411
theorem B2260571 : Blo 1506950 2260571 := bstep (se 1 (by rfl) ⟨1695428, by rfl⟩ : syracuseStep 2260571 = 3390857) B3390857
theorem B2260655 : Blo 1506950 2260655 := bstep (se 1 (by rfl) ⟨1695491, by rfl⟩ : syracuseStep 2260655 = 3390983) B3390983
theorem B5086907 : Blo 1506950 5086907 := bstep (se 1 (by rfl) ⟨3815180, by rfl⟩ : syracuseStep 5086907 = 7630361) B7630361
theorem B2260775 : Blo 1506950 2260775 := bstep (se 1 (by rfl) ⟨1695581, by rfl⟩ : syracuseStep 2260775 = 3391163) B3391163
theorem B10460983 : Blo 1506950 10460983 := bstep (se 1 (by rfl) ⟨7845737, by rfl⟩ : syracuseStep 10460983 = 15691475) B15691475
theorem B111517499 : Blo 1506950 111517499 := bstep (se 1 (by rfl) ⟨83638124, by rfl⟩ : syracuseStep 111517499 = 167276249) B167276249
theorem B1507143 : Blo 1506950 1507143 := bstep (se 1 (by rfl) ⟨1130357, by rfl⟩ : syracuseStep 1507143 = 2260715) B2260715
theorem B1695559 : Blo 1506950 1695559 := bstep (se 1 (by rfl) ⟨1271669, by rfl⟩ : syracuseStep 1695559 = 2543339) B2543339
theorem B2260859 : Blo 1506950 2260859 := bstep (se 1 (by rfl) ⟨1695644, by rfl⟩ : syracuseStep 2260859 = 3391289) B3391289
theorem B2146171 : Blo 1506950 2146171 := bstep (se 1 (by rfl) ⟨1609628, by rfl⟩ : syracuseStep 2146171 = 3219257) B3219257
theorem B1507295 : Blo 1506950 1507295 := bstep (se 1 (by rfl) ⟨1130471, by rfl⟩ : syracuseStep 1507295 = 2260943) B2260943
theorem B10870757 : Blo 1506950 10870757 := bstep (se 4 (by rfl) ⟨1019133, by rfl⟩ : syracuseStep 10870757 = 2038267) B2038267
theorem B193437875 : Blo 1506950 193437875 := bstep (se 1 (by rfl) ⟨145078406, by rfl⟩ : syracuseStep 193437875 = 290156813) B290156813
theorem B2261183 : Blo 1506950 2261183 := bstep (se 1 (by rfl) ⟨1695887, by rfl⟩ : syracuseStep 2261183 = 3391775) B3391775
theorem B1507519 : Blo 1506950 1507519 := bstep (se 1 (by rfl) ⟨1130639, by rfl⟩ : syracuseStep 1507519 = 2261279) B2261279
theorem B2146495 : Blo 1506950 2146495 := bstep (se 1 (by rfl) ⟨1609871, by rfl⟩ : syracuseStep 2146495 = 3219743) B3219743
theorem B1507535 : Blo 1506950 1507535 := bstep (se 1 (by rfl) ⟨1130651, by rfl⟩ : syracuseStep 1507535 = 2261303) B2261303
theorem B5087447 : Blo 1506950 5087447 := bstep (se 1 (by rfl) ⟨3815585, by rfl⟩ : syracuseStep 5087447 = 7631171) B7631171
theorem B1507583 : Blo 1506950 1507583 := bstep (se 1 (by rfl) ⟨1130687, by rfl⟩ : syracuseStep 1507583 = 2261375) B2261375
theorem B1507631 : Blo 1506950 1507631 := bstep (se 1 (by rfl) ⟨1130723, by rfl⟩ : syracuseStep 1507631 = 2261447) B2261447
theorem B1507867 : Blo 1506950 1507867 := bstep (se 1 (by rfl) ⟨1130900, by rfl⟩ : syracuseStep 1507867 = 2261801) B2261801
theorem B1507871 : Blo 1506950 1507871 := bstep (se 1 (by rfl) ⟨1130903, by rfl⟩ : syracuseStep 1507871 = 2261807) B2261807
theorem B3818087 : Blo 1506950 3818087 := bstep (se 1 (by rfl) ⟨2863565, by rfl⟩ : syracuseStep 3818087 = 5727131) B5727131
theorem B2261609 : Blo 1506950 2261609 := bstep (se 2 (by rfl) ⟨848103, by rfl⟩ : syracuseStep 2261609 = 1696207) B1696207
theorem B2261615 : Blo 1506950 2261615 := bstep (se 1 (by rfl) ⟨1696211, by rfl⟩ : syracuseStep 2261615 = 3392423) B3392423
theorem B1507951 : Blo 1506950 1507951 := bstep (se 1 (by rfl) ⟨1130963, by rfl⟩ : syracuseStep 1507951 = 2261927) B2261927
theorem B1696423 : Blo 1506950 1696423 := bstep (se 1 (by rfl) ⟨1272317, by rfl⟩ : syracuseStep 1696423 = 2544635) B2544635
theorem B1508007 : Blo 1506950 1508007 := bstep (se 1 (by rfl) ⟨1131005, by rfl⟩ : syracuseStep 1508007 = 2262011) B2262011
theorem B1508047 : Blo 1506950 1508047 := bstep (se 1 (by rfl) ⟨1131035, by rfl⟩ : syracuseStep 1508047 = 2262071) B2262071
theorem B1508127 : Blo 1506950 1508127 := bstep (se 1 (by rfl) ⟨1131095, by rfl⟩ : syracuseStep 1508127 = 2262191) B2262191
theorem B3392297 : Blo 1506950 3392297 := bstep (se 2 (by rfl) ⟨1272111, by rfl⟩ : syracuseStep 3392297 = 2544223) B2544223
theorem B8586071 : Blo 1506950 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B1696711 : Blo 1506950 1696711 := bstep (se 1 (by rfl) ⟨1272533, by rfl⟩ : syracuseStep 1696711 = 2545067) B2545067
theorem B6439931 : Blo 1506950 6439931 := bstep (se 1 (by rfl) ⟨4829948, by rfl⟩ : syracuseStep 6439931 = 9659897) B9659897
theorem B1508399 : Blo 1506950 1508399 := bstep (se 1 (by rfl) ⟨1131299, by rfl⟩ : syracuseStep 1508399 = 2262599) B2262599
theorem B3392567 : Blo 1506950 3392567 := bstep (se 1 (by rfl) ⟨2544425, by rfl⟩ : syracuseStep 3392567 = 5088851) B5088851
theorem B4187209 : Blo 1506950 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B1508463 : Blo 1506950 1508463 := bstep (se 1 (by rfl) ⟨1131347, by rfl⟩ : syracuseStep 1508463 = 2262695) B2262695
theorem B1508519 : Blo 1506950 1508519 := bstep (se 1 (by rfl) ⟨1131389, by rfl⟩ : syracuseStep 1508519 = 2262779) B2262779
theorem B1508543 : Blo 1506950 1508543 := bstep (se 1 (by rfl) ⟨1131407, by rfl⟩ : syracuseStep 1508543 = 2262815) B2262815
theorem B2262239 : Blo 1506950 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B1508575 : Blo 1506950 1508575 := bstep (se 1 (by rfl) ⟨1131431, by rfl⟩ : syracuseStep 1508575 = 2262863) B2262863
theorem B3392747 : Blo 1506950 3392747 := bstep (se 1 (by rfl) ⟨2544560, by rfl⟩ : syracuseStep 3392747 = 5089121) B5089121
theorem B2262251 : Blo 1506950 2262251 := bstep (se 1 (by rfl) ⟨1696688, by rfl⟩ : syracuseStep 2262251 = 3393377) B3393377
theorem B1697071 : Blo 1506950 1697071 := bstep (se 1 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 1697071 = 2545607) B2545607
theorem B1508655 : Blo 1506950 1508655 := bstep (se 1 (by rfl) ⟨1131491, by rfl⟩ : syracuseStep 1508655 = 2262983) B2262983
theorem B19334447 : Blo 1506950 19334447 := bstep (se 1 (by rfl) ⟨14500835, by rfl⟩ : syracuseStep 19334447 = 29001671) B29001671
theorem B5801503 : Blo 1506950 5801503 := bstep (se 1 (by rfl) ⟨4351127, by rfl⟩ : syracuseStep 5801503 = 8702255) B8702255
theorem B1508891 : Blo 1506950 1508891 := bstep (se 1 (by rfl) ⟨1131668, by rfl⟩ : syracuseStep 1508891 = 2263337) B2263337
theorem B1508895 : Blo 1506950 1508895 := bstep (se 1 (by rfl) ⟨1131671, by rfl⟩ : syracuseStep 1508895 = 2263343) B2263343
theorem B2262635 : Blo 1506950 2262635 := bstep (se 1 (by rfl) ⟨1696976, by rfl⟩ : syracuseStep 2262635 = 3393953) B3393953
theorem B39192217 : Blo 1506950 39192217 := bstep (se 2 (by rfl) ⟨14697081, by rfl⟩ : syracuseStep 39192217 = 29394163) B29394163
theorem B3393215 : Blo 1506950 3393215 := bstep (se 1 (by rfl) ⟨2544911, by rfl⟩ : syracuseStep 3393215 = 5089823) B5089823
theorem B2262719 : Blo 1506950 2262719 := bstep (se 1 (by rfl) ⟨1697039, by rfl⟩ : syracuseStep 2262719 = 3394079) B3394079
theorem B12887855 : Blo 1506950 12887855 := bstep (se 1 (by rfl) ⟨9665891, by rfl⟩ : syracuseStep 12887855 = 19331783) B19331783
theorem B7243577 : Blo 1506950 7243577 := bstep (se 2 (by rfl) ⟨2716341, by rfl⟩ : syracuseStep 7243577 = 5432683) B5432683
theorem B26470253 : Blo 1506950 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B2262905 : Blo 1506950 2262905 := bstep (se 2 (by rfl) ⟨848589, by rfl⟩ : syracuseStep 2262905 = 1697179) B1697179
theorem B2860991 : Blo 1506950 2860991 := bstep (se 1 (by rfl) ⟨2145743, by rfl⟩ : syracuseStep 2860991 = 4291487) B4291487
theorem B11601953 : Blo 1506950 11601953 := bstep (se 2 (by rfl) ⟨4350732, by rfl⟩ : syracuseStep 11601953 = 8701465) B8701465
theorem B417687715 : Blo 1506950 417687715 := bstep (se 1 (by rfl) ⟨313265786, by rfl⟩ : syracuseStep 417687715 = 626531573) B626531573
theorem B43452683 : Blo 1506950 43452683 := bstep (se 1 (by rfl) ⟨32589512, by rfl⟩ : syracuseStep 43452683 = 65179025) B65179025
theorem B5728603 : Blo 1506950 5728603 := bstep (se 1 (by rfl) ⟨4296452, by rfl⟩ : syracuseStep 5728603 = 8592905) B8592905
theorem B17181071 : Blo 1506950 17181071 := bstep (se 1 (by rfl) ⟨12885803, by rfl⟩ : syracuseStep 17181071 = 25771607) B25771607
theorem B2861561 : Blo 1506950 2861561 := bstep (se 2 (by rfl) ⟨1073085, by rfl⟩ : syracuseStep 2861561 = 2146171) B2146171
theorem B74344999 : Blo 1506950 74344999 := bstep (se 1 (by rfl) ⟨55758749, by rfl⟩ : syracuseStep 74344999 = 111517499) B111517499
theorem B3394151 : Blo 1506950 3394151 := bstep (se 1 (by rfl) ⟨2545613, by rfl⟩ : syracuseStep 3394151 = 5091227) B5091227
theorem B18852527 : Blo 1506950 18852527 := bstep (se 1 (by rfl) ⟨14139395, by rfl⟩ : syracuseStep 18852527 = 28278791) B28278791
theorem B4827871 : Blo 1506950 4827871 := bstep (se 1 (by rfl) ⟨3620903, by rfl⟩ : syracuseStep 4827871 = 7241807) B7241807
theorem B5802947 : Blo 1506950 5802947 := bstep (se 1 (by rfl) ⟨4352210, by rfl⟩ : syracuseStep 5802947 = 8704421) B8704421
theorem B5090255 : Blo 1506950 5090255 := bstep (se 1 (by rfl) ⟨3817691, by rfl⟩ : syracuseStep 5090255 = 7635383) B7635383
theorem B2862047 : Blo 1506950 2862047 := bstep (se 1 (by rfl) ⟨2146535, by rfl⟩ : syracuseStep 2862047 = 4293071) B4293071
theorem B3394529 : Blo 1506950 3394529 := bstep (se 2 (by rfl) ⟨1272948, by rfl⟩ : syracuseStep 3394529 = 2545897) B2545897
theorem B310021091 : Blo 1506950 310021091 := bstep (se 1 (by rfl) ⟨232515818, by rfl⟩ : syracuseStep 310021091 = 465031637) B465031637
theorem B5090579 : Blo 1506950 5090579 := bstep (se 1 (by rfl) ⟨3817934, by rfl⟩ : syracuseStep 5090579 = 7635869) B7635869
theorem B3394907 : Blo 1506950 3394907 := bstep (se 1 (by rfl) ⟨2546180, by rfl⟩ : syracuseStep 3394907 = 5092361) B5092361
theorem B3394943 : Blo 1506950 3394943 := bstep (se 1 (by rfl) ⟨2546207, by rfl⟩ : syracuseStep 3394943 = 5092415) B5092415
theorem B48885191 : Blo 1506950 48885191 := bstep (se 1 (by rfl) ⟨36663893, by rfl⟩ : syracuseStep 48885191 = 73327787) B73327787
theorem B11455991 : Blo 1506950 11455991 := bstep (se 1 (by rfl) ⟨8591993, by rfl⟩ : syracuseStep 11455991 = 17183987) B17183987
theorem B9924179 : Blo 1506950 9924179 := bstep (se 1 (by rfl) ⟨7443134, by rfl⟩ : syracuseStep 9924179 = 14886269) B14886269
theorem B3624691 : Blo 1506950 3624691 := bstep (se 1 (by rfl) ⟨2718518, by rfl⟩ : syracuseStep 3624691 = 5437037) B5437037
theorem B2863019 : Blo 1506950 2863019 := bstep (se 1 (by rfl) ⟨2147264, by rfl⟩ : syracuseStep 2863019 = 4294529) B4294529
theorem B2543771 : Blo 1506950 2543771 := bstep (se 1 (by rfl) ⟨1907828, by rfl⟩ : syracuseStep 2543771 = 3815657) B3815657
theorem B2543791 : Blo 1506950 2543791 := bstep (se 1 (by rfl) ⟨1907843, by rfl⟩ : syracuseStep 2543791 = 3815687) B3815687
theorem B3264799 : Blo 1506950 3264799 := bstep (se 1 (by rfl) ⟨2448599, by rfl⟩ : syracuseStep 3264799 = 4897199) B4897199
theorem B10867067 : Blo 1506950 10867067 := bstep (se 1 (by rfl) ⟨8150300, by rfl⟩ : syracuseStep 10867067 = 16300601) B16300601
theorem B5091767 : Blo 1506950 5091767 := bstep (se 1 (by rfl) ⟨3818825, by rfl⟩ : syracuseStep 5091767 = 7637651) B7637651
theorem B5435855 : Blo 1506950 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B32608889 : Blo 1506950 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B19575593 : Blo 1506950 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B5092307 : Blo 1506950 5092307 := bstep (se 1 (by rfl) ⟨3819230, by rfl⟩ : syracuseStep 5092307 = 7638461) B7638461
theorem B13751333 : Blo 1506950 13751333 := bstep (se 4 (by rfl) ⟨1289187, by rfl⟩ : syracuseStep 13751333 = 2578375) B2578375
theorem B14496839 : Blo 1506950 14496839 := bstep (se 1 (by rfl) ⟨10872629, by rfl⟩ : syracuseStep 14496839 = 21745259) B21745259
theorem B13947977 : Blo 1506950 13947977 := bstep (se 2 (by rfl) ⟨5230491, by rfl⟩ : syracuseStep 13947977 = 10460983) B10460983
theorem B2864393 : Blo 1506950 2864393 := bstep (se 2 (by rfl) ⟨1074147, by rfl⟩ : syracuseStep 2864393 = 2148295) B2148295
theorem B7247171 : Blo 1506950 7247171 := bstep (se 1 (by rfl) ⟨5435378, by rfl⟩ : syracuseStep 7247171 = 10870757) B10870757
theorem B1611247 : Blo 1506950 1611247 := bstep (se 1 (by rfl) ⟨1208435, by rfl⟩ : syracuseStep 1611247 = 2416871) B2416871
theorem B2037403 : Blo 1506950 2037403 := bstep (se 1 (by rfl) ⟨1528052, by rfl⟩ : syracuseStep 2037403 = 3056105) B3056105
theorem B2545499 : Blo 1506950 2545499 := bstep (se 1 (by rfl) ⟨1909124, by rfl⟩ : syracuseStep 2545499 = 3818249) B3818249
theorem B55760825 : Blo 1506950 55760825 := bstep (se 2 (by rfl) ⟨20910309, by rfl⟩ : syracuseStep 55760825 = 41820619) B41820619
theorem B12875759 : Blo 1506950 12875759 := bstep (se 1 (by rfl) ⟨9656819, by rfl⟩ : syracuseStep 12875759 = 19313639) B19313639
theorem B3815495 : Blo 1506950 3815495 := bstep (se 1 (by rfl) ⟨2861621, by rfl⟩ : syracuseStep 3815495 = 5723243) B5723243
theorem B2545951 : Blo 1506950 2545951 := bstep (se 1 (by rfl) ⟨1909463, by rfl⟩ : syracuseStep 2545951 = 3818927) B3818927
theorem B48920867 : Blo 1506950 48920867 := bstep (se 1 (by rfl) ⟨36690650, by rfl⟩ : syracuseStep 48920867 = 73381301) B73381301
theorem B7633439 : Blo 1506950 7633439 := bstep (se 1 (by rfl) ⟨5725079, by rfl⟩ : syracuseStep 7633439 = 11450159) B11450159
theorem B4414397 : Blo 1506950 4414397 := bstep (se 3 (by rfl) ⟨827699, by rfl⟩ : syracuseStep 4414397 = 1655399) B1655399
theorem B11451617 : Blo 1506950 11451617 := bstep (se 2 (by rfl) ⟨4294356, by rfl⟩ : syracuseStep 11451617 = 8588713) B8588713
theorem B3390695 : Blo 1506950 3390695 := bstep (se 1 (by rfl) ⟨2543021, by rfl⟩ : syracuseStep 3390695 = 5086043) B5086043
theorem B3816679 : Blo 1506950 3816679 := bstep (se 1 (by rfl) ⟨2862509, by rfl⟩ : syracuseStep 3816679 = 5725019) B5725019
theorem B12885257 : Blo 1506950 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B5725673 : Blo 1506950 5725673 := bstep (se 2 (by rfl) ⟨2147127, by rfl⟩ : syracuseStep 5725673 = 4294255) B4294255
theorem B5725687 : Blo 1506950 5725687 := bstep (se 1 (by rfl) ⟨4294265, by rfl⟩ : syracuseStep 5725687 = 8588531) B8588531
theorem B1695343 : Blo 1506950 1695343 := bstep (se 1 (by rfl) ⟨1271507, by rfl⟩ : syracuseStep 1695343 = 2543015) B2543015
theorem B1506983 : Blo 1506950 1506983 := bstep (se 1 (by rfl) ⟨1130237, by rfl⟩ : syracuseStep 1506983 = 2260475) B2260475
theorem B1695451 : Blo 1506950 1695451 := bstep (se 1 (by rfl) ⟨1271588, by rfl⟩ : syracuseStep 1695451 = 2543177) B2543177
theorem B2260703 : Blo 1506950 2260703 := bstep (se 1 (by rfl) ⟨1695527, by rfl⟩ : syracuseStep 2260703 = 3391055) B3391055
theorem B3391199 : Blo 1506950 3391199 := bstep (se 1 (by rfl) ⟨2543399, by rfl⟩ : syracuseStep 3391199 = 5086799) B5086799
theorem B1507047 : Blo 1506950 1507047 := bstep (se 1 (by rfl) ⟨1130285, by rfl⟩ : syracuseStep 1507047 = 2260571) B2260571
theorem B2260745 : Blo 1506950 2260745 := bstep (se 2 (by rfl) ⟨847779, by rfl⟩ : syracuseStep 2260745 = 1695559) B1695559
theorem B1507103 : Blo 1506950 1507103 := bstep (se 1 (by rfl) ⟨1130327, by rfl⟩ : syracuseStep 1507103 = 2260655) B2260655
theorem B3391271 : Blo 1506950 3391271 := bstep (se 1 (by rfl) ⟨2543453, by rfl⟩ : syracuseStep 3391271 = 5086907) B5086907
theorem B1507183 : Blo 1506950 1507183 := bstep (se 1 (by rfl) ⟨1130387, by rfl⟩ : syracuseStep 1507183 = 2260775) B2260775
theorem B1507239 : Blo 1506950 1507239 := bstep (se 1 (by rfl) ⟨1130429, by rfl⟩ : syracuseStep 1507239 = 2260859) B2260859
theorem B5087177 : Blo 1506950 5087177 := bstep (se 2 (by rfl) ⟨1907691, by rfl⟩ : syracuseStep 5087177 = 3815383) B3815383
theorem B1695847 : Blo 1506950 1695847 := bstep (se 1 (by rfl) ⟨1271885, by rfl⟩ : syracuseStep 1695847 = 2543771) B2543771
theorem B128958583 : Blo 1506950 128958583 := bstep (se 1 (by rfl) ⟨96718937, by rfl⟩ : syracuseStep 128958583 = 193437875) B193437875
theorem B1507455 : Blo 1506950 1507455 := bstep (se 1 (by rfl) ⟨1130591, by rfl⟩ : syracuseStep 1507455 = 2261183) B2261183
theorem B3391631 : Blo 1506950 3391631 := bstep (se 1 (by rfl) ⟨2543723, by rfl⟩ : syracuseStep 3391631 = 5087447) B5087447
theorem B556916953 : Blo 1506950 556916953 := bstep (se 2 (by rfl) ⟨208843857, by rfl⟩ : syracuseStep 556916953 = 417687715) B417687715
theorem B3391721 : Blo 1506950 3391721 := bstep (se 2 (by rfl) ⟨1271895, by rfl⟩ : syracuseStep 3391721 = 2543791) B2543791
theorem B1507739 : Blo 1506950 1507739 := bstep (se 1 (by rfl) ⟨1130804, by rfl⟩ : syracuseStep 1507739 = 2261609) B2261609
theorem B1507743 : Blo 1506950 1507743 := bstep (se 1 (by rfl) ⟨1130807, by rfl⟩ : syracuseStep 1507743 = 2261615) B2261615
theorem B13050395 : Blo 1506950 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B2261531 : Blo 1506950 2261531 := bstep (se 1 (by rfl) ⟨1696148, by rfl⟩ : syracuseStep 2261531 = 3392297) B3392297
theorem B4293287 : Blo 1506950 4293287 := bstep (se 1 (by rfl) ⟨3219965, by rfl⟩ : syracuseStep 4293287 = 6439931) B6439931
theorem B9167555 : Blo 1506950 9167555 := bstep (se 1 (by rfl) ⟨6875666, by rfl⟩ : syracuseStep 9167555 = 13751333) B13751333
theorem B2261711 : Blo 1506950 2261711 := bstep (se 1 (by rfl) ⟨1696283, by rfl⟩ : syracuseStep 2261711 = 3392567) B3392567
theorem B9298651 : Blo 1506950 9298651 := bstep (se 1 (by rfl) ⟨6973988, by rfl⟩ : syracuseStep 9298651 = 13947977) B13947977
theorem B1508159 : Blo 1506950 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B2261831 : Blo 1506950 2261831 := bstep (se 1 (by rfl) ⟨1696373, by rfl⟩ : syracuseStep 2261831 = 3392747) B3392747
theorem B1508167 : Blo 1506950 1508167 := bstep (se 1 (by rfl) ⟨1131125, by rfl⟩ : syracuseStep 1508167 = 2262251) B2262251
theorem B19325789 : Blo 1506950 19325789 := bstep (se 3 (by rfl) ⟨3623585, by rfl⟩ : syracuseStep 19325789 = 7247171) B7247171
theorem B1909595 : Blo 1506950 1909595 := bstep (se 1 (by rfl) ⟨1432196, by rfl⟩ : syracuseStep 1909595 = 2864393) B2864393
theorem B2261897 : Blo 1506950 2261897 := bstep (se 2 (by rfl) ⟨848211, by rfl⟩ : syracuseStep 2261897 = 1696423) B1696423
theorem B1508423 : Blo 1506950 1508423 := bstep (se 1 (by rfl) ⟨1131317, by rfl⟩ : syracuseStep 1508423 = 2262635) B2262635
theorem B2262143 : Blo 1506950 2262143 := bstep (se 1 (by rfl) ⟨1696607, by rfl⟩ : syracuseStep 2262143 = 3393215) B3393215
theorem B1508479 : Blo 1506950 1508479 := bstep (se 1 (by rfl) ⟨1131359, by rfl⟩ : syracuseStep 1508479 = 2262719) B2262719
theorem B1696999 : Blo 1506950 1696999 := bstep (se 1 (by rfl) ⟨1272749, by rfl⟩ : syracuseStep 1696999 = 2545499) B2545499
theorem B17646835 : Blo 1506950 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B1508603 : Blo 1506950 1508603 := bstep (se 1 (by rfl) ⟨1131452, by rfl⟩ : syracuseStep 1508603 = 2262905) B2262905
theorem B2262281 : Blo 1506950 2262281 := bstep (se 2 (by rfl) ⟨848355, by rfl⟩ : syracuseStep 2262281 = 1696711) B1696711
theorem B7734635 : Blo 1506950 7734635 := bstep (se 1 (by rfl) ⟨5800976, by rfl⟩ : syracuseStep 7734635 = 11601953) B11601953
theorem B28968455 : Blo 1506950 28968455 := bstep (se 1 (by rfl) ⟨21726341, by rfl⟩ : syracuseStep 28968455 = 43452683) B43452683
theorem B32613911 : Blo 1506950 32613911 := bstep (se 1 (by rfl) ⟨24460433, by rfl⟩ : syracuseStep 32613911 = 48920867) B48920867
theorem B11454047 : Blo 1506950 11454047 := bstep (se 1 (by rfl) ⟨8590535, by rfl⟩ : syracuseStep 11454047 = 17181071) B17181071
theorem B5088905 : Blo 1506950 5088905 := bstep (se 2 (by rfl) ⟨1908339, by rfl⟩ : syracuseStep 5088905 = 3816679) B3816679
theorem B5088959 : Blo 1506950 5088959 := bstep (se 1 (by rfl) ⟨3816719, by rfl⟩ : syracuseStep 5088959 = 7633439) B7633439
theorem B2262761 : Blo 1506950 2262761 := bstep (se 2 (by rfl) ⟨848535, by rfl⟩ : syracuseStep 2262761 = 1697071) B1697071
theorem B2262767 : Blo 1506950 2262767 := bstep (se 1 (by rfl) ⟨1697075, by rfl⟩ : syracuseStep 2262767 = 3394151) B3394151
theorem B3868631 : Blo 1506950 3868631 := bstep (se 1 (by rfl) ⟨2901473, by rfl⟩ : syracuseStep 3868631 = 5802947) B5802947
theorem B3393503 : Blo 1506950 3393503 := bstep (se 1 (by rfl) ⟨2545127, by rfl⟩ : syracuseStep 3393503 = 5090255) B5090255
theorem B2148329 : Blo 1506950 2148329 := bstep (se 2 (by rfl) ⟨805623, by rfl⟩ : syracuseStep 2148329 = 1611247) B1611247
theorem B2263019 : Blo 1506950 2263019 := bstep (se 1 (by rfl) ⟨1697264, by rfl⟩ : syracuseStep 2263019 = 3394529) B3394529
theorem B7735337 : Blo 1506950 7735337 := bstep (se 2 (by rfl) ⟨2900751, by rfl⟩ : syracuseStep 7735337 = 5801503) B5801503
theorem B3393719 : Blo 1506950 3393719 := bstep (se 1 (by rfl) ⟨2545289, by rfl⟩ : syracuseStep 3393719 = 5090579) B5090579
theorem B2263271 : Blo 1506950 2263271 := bstep (se 1 (by rfl) ⟨1697453, by rfl⟩ : syracuseStep 2263271 = 3394907) B3394907
theorem B2263295 : Blo 1506950 2263295 := bstep (se 1 (by rfl) ⟨1697471, by rfl⟩ : syracuseStep 2263295 = 3394943) B3394943
theorem B32590127 : Blo 1506950 32590127 := bstep (se 1 (by rfl) ⟨24442595, by rfl⟩ : syracuseStep 32590127 = 48885191) B48885191
theorem B7637327 : Blo 1506950 7637327 := bstep (se 1 (by rfl) ⟨5727995, by rfl⟩ : syracuseStep 7637327 = 11455991) B11455991
theorem B148695533 : Blo 1506950 148695533 := bstep (se 3 (by rfl) ⟨27880412, by rfl⟩ : syracuseStep 148695533 = 55760825) B55760825
theorem B7244711 : Blo 1506950 7244711 := bstep (se 1 (by rfl) ⟨5433533, by rfl⟩ : syracuseStep 7244711 = 10867067) B10867067
theorem B2861993 : Blo 1506950 2861993 := bstep (se 2 (by rfl) ⟨1073247, by rfl⟩ : syracuseStep 2861993 = 2146495) B2146495
theorem B3394511 : Blo 1506950 3394511 := bstep (se 1 (by rfl) ⟨2545883, by rfl⟩ : syracuseStep 3394511 = 5091767) B5091767
theorem B3623903 : Blo 1506950 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B4353065 : Blo 1506950 4353065 := bstep (se 2 (by rfl) ⟨1632399, by rfl⟩ : syracuseStep 4353065 = 3264799) B3264799
theorem B3394601 : Blo 1506950 3394601 := bstep (se 2 (by rfl) ⟨1272975, by rfl⟩ : syracuseStep 3394601 = 2545951) B2545951
theorem B7638137 : Blo 1506950 7638137 := bstep (se 2 (by rfl) ⟨2864301, by rfl⟩ : syracuseStep 7638137 = 5728603) B5728603
theorem B3394871 : Blo 1506950 3394871 := bstep (se 1 (by rfl) ⟨2546153, by rfl⟩ : syracuseStep 3394871 = 5092307) B5092307
theorem B99126665 : Blo 1506950 99126665 := bstep (se 2 (by rfl) ⟨37172499, by rfl⟩ : syracuseStep 99126665 = 74344999) B74344999
theorem B12889631 : Blo 1506950 12889631 := bstep (se 1 (by rfl) ⟨9667223, by rfl⟩ : syracuseStep 12889631 = 19334447) B19334447
theorem B4829051 : Blo 1506950 4829051 := bstep (se 1 (by rfl) ⟨3621788, by rfl⟩ : syracuseStep 4829051 = 7243577) B7243577
theorem B2543663 : Blo 1506950 2543663 := bstep (se 1 (by rfl) ⟨1907747, by rfl⟩ : syracuseStep 2543663 = 3815495) B3815495
theorem B5582945 : Blo 1506950 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B26464477 : Blo 1506950 26464477 := bstep (se 3 (by rfl) ⟨4962089, by rfl⟩ : syracuseStep 26464477 = 9924179) B9924179
theorem B206680727 : Blo 1506950 206680727 := bstep (se 1 (by rfl) ⟨155010545, by rfl⟩ : syracuseStep 206680727 = 310021091) B310021091
theorem B8590171 : Blo 1506950 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B2716537 : Blo 1506950 2716537 := bstep (se 2 (by rfl) ⟨1018701, by rfl⟩ : syracuseStep 2716537 = 2037403) B2037403
theorem B2545391 : Blo 1506950 2545391 := bstep (se 1 (by rfl) ⟨1909043, by rfl⟩ : syracuseStep 2545391 = 3818087) B3818087
theorem B21739259 : Blo 1506950 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B5724047 : Blo 1506950 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B9664559 : Blo 1506950 9664559 := bstep (se 1 (by rfl) ⟨7248419, by rfl⟩ : syracuseStep 9664559 = 14496839) B14496839
theorem B209025157 : Blo 1506950 209025157 := bstep (se 4 (by rfl) ⟨19596108, by rfl⟩ : syracuseStep 209025157 = 39192217) B39192217
theorem B6437161 : Blo 1506950 6437161 := bstep (se 2 (by rfl) ⟨2413935, by rfl⟩ : syracuseStep 6437161 = 4827871) B4827871
theorem B8591903 : Blo 1506950 8591903 := bstep (se 1 (by rfl) ⟨6443927, by rfl⟩ : syracuseStep 8591903 = 12887855) B12887855
theorem B1907327 : Blo 1506950 1907327 := bstep (se 1 (by rfl) ⟨1430495, by rfl⟩ : syracuseStep 1907327 = 2860991) B2860991
theorem B8583839 : Blo 1506950 8583839 := bstep (se 1 (by rfl) ⟨6437879, by rfl⟩ : syracuseStep 8583839 = 12875759) B12875759
theorem B1907707 : Blo 1506950 1907707 := bstep (se 1 (by rfl) ⟨1430780, by rfl⟩ : syracuseStep 1907707 = 2861561) B2861561
theorem B50273405 : Blo 1506950 50273405 := bstep (se 3 (by rfl) ⟨9426263, by rfl⟩ : syracuseStep 50273405 = 18852527) B18852527
theorem B1908031 : Blo 1506950 1908031 := bstep (se 1 (by rfl) ⟨1431023, by rfl⟩ : syracuseStep 1908031 = 2862047) B2862047
theorem B7634249 : Blo 1506950 7634249 := bstep (se 2 (by rfl) ⟨2862843, by rfl⟩ : syracuseStep 7634249 = 5725687) B5725687
theorem B2260457 : Blo 1506950 2260457 := bstep (se 2 (by rfl) ⟨847671, by rfl⟩ : syracuseStep 2260457 = 1695343) B1695343
theorem B7634411 : Blo 1506950 7634411 := bstep (se 1 (by rfl) ⟨5725808, by rfl⟩ : syracuseStep 7634411 = 11451617) B11451617
theorem B2260463 : Blo 1506950 2260463 := bstep (se 1 (by rfl) ⟨1695347, by rfl⟩ : syracuseStep 2260463 = 3390695) B3390695
theorem B2260601 : Blo 1506950 2260601 := bstep (se 2 (by rfl) ⟨847725, by rfl⟩ : syracuseStep 2260601 = 1695451) B1695451
theorem B3817115 : Blo 1506950 3817115 := bstep (se 1 (by rfl) ⟨2862836, by rfl⟩ : syracuseStep 3817115 = 5725673) B5725673
theorem B4832921 : Blo 1506950 4832921 := bstep (se 2 (by rfl) ⟨1812345, by rfl⟩ : syracuseStep 4832921 = 3624691) B3624691
theorem B1507135 : Blo 1506950 1507135 := bstep (se 1 (by rfl) ⟨1130351, by rfl⟩ : syracuseStep 1507135 = 2260703) B2260703
theorem B2260799 : Blo 1506950 2260799 := bstep (se 1 (by rfl) ⟨1695599, by rfl⟩ : syracuseStep 2260799 = 3391199) B3391199
theorem B11771725 : Blo 1506950 11771725 := bstep (se 3 (by rfl) ⟨2207198, by rfl⟩ : syracuseStep 11771725 = 4414397) B4414397
theorem B1507163 : Blo 1506950 1507163 := bstep (se 1 (by rfl) ⟨1130372, by rfl⟩ : syracuseStep 1507163 = 2260745) B2260745
theorem B2260847 : Blo 1506950 2260847 := bstep (se 1 (by rfl) ⟨1695635, by rfl⟩ : syracuseStep 2260847 = 3391271) B3391271
theorem B1908679 : Blo 1506950 1908679 := bstep (se 1 (by rfl) ⟨1431509, by rfl⟩ : syracuseStep 1908679 = 2863019) B2863019
theorem B3391451 : Blo 1506950 3391451 := bstep (se 1 (by rfl) ⟨2543588, by rfl⟩ : syracuseStep 3391451 = 5087177) B5087177
theorem B1695775 : Blo 1506950 1695775 := bstep (se 1 (by rfl) ⟨1271831, by rfl⟩ : syracuseStep 1695775 = 2543663) B2543663
theorem B2261087 : Blo 1506950 2261087 := bstep (se 1 (by rfl) ⟨1695815, by rfl⟩ : syracuseStep 2261087 = 3391631) B3391631
theorem B2261129 : Blo 1506950 2261129 := bstep (se 2 (by rfl) ⟨847923, by rfl⟩ : syracuseStep 2261129 = 1695847) B1695847
theorem B2261147 : Blo 1506950 2261147 := bstep (se 1 (by rfl) ⟨1695860, by rfl⟩ : syracuseStep 2261147 = 3391721) B3391721
theorem B278700209 : Blo 1506950 278700209 := bstep (se 2 (by rfl) ⟨104512578, by rfl⟩ : syracuseStep 278700209 = 209025157) B209025157
theorem B742555937 : Blo 1506950 742555937 := bstep (se 2 (by rfl) ⟨278458476, by rfl⟩ : syracuseStep 742555937 = 556916953) B556916953
theorem B8700263 : Blo 1506950 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B1507687 : Blo 1506950 1507687 := bstep (se 1 (by rfl) ⟨1130765, by rfl⟩ : syracuseStep 1507687 = 2261531) B2261531
theorem B6111703 : Blo 1506950 6111703 := bstep (se 1 (by rfl) ⟨4583777, by rfl⟩ : syracuseStep 6111703 = 9167555) B9167555
theorem B1507807 : Blo 1506950 1507807 := bstep (se 1 (by rfl) ⟨1130855, by rfl⟩ : syracuseStep 1507807 = 2261711) B2261711
theorem B1507887 : Blo 1506950 1507887 := bstep (se 1 (by rfl) ⟨1130915, by rfl⟩ : syracuseStep 1507887 = 2261831) B2261831
theorem B1507931 : Blo 1506950 1507931 := bstep (se 1 (by rfl) ⟨1130948, by rfl⟩ : syracuseStep 1507931 = 2261897) B2261897
theorem B1508095 : Blo 1506950 1508095 := bstep (se 1 (by rfl) ⟨1131071, by rfl⟩ : syracuseStep 1508095 = 2262143) B2262143
theorem B1508187 : Blo 1506950 1508187 := bstep (se 1 (by rfl) ⟨1131140, by rfl⟩ : syracuseStep 1508187 = 2262281) B2262281
theorem B21742607 : Blo 1506950 21742607 := bstep (se 1 (by rfl) ⟨16306955, by rfl⟩ : syracuseStep 21742607 = 32613911) B32613911
theorem B7636031 : Blo 1506950 7636031 := bstep (se 1 (by rfl) ⟨5727023, by rfl⟩ : syracuseStep 7636031 = 11454047) B11454047
theorem B3392603 : Blo 1506950 3392603 := bstep (se 1 (by rfl) ⟨2544452, by rfl⟩ : syracuseStep 3392603 = 5088905) B5088905
theorem B11453561 : Blo 1506950 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B3392639 : Blo 1506950 3392639 := bstep (se 1 (by rfl) ⟨2544479, by rfl⟩ : syracuseStep 3392639 = 5088959) B5088959
theorem B1508507 : Blo 1506950 1508507 := bstep (se 1 (by rfl) ⟨1131380, by rfl⟩ : syracuseStep 1508507 = 2262761) B2262761
theorem B1696927 : Blo 1506950 1696927 := bstep (se 1 (by rfl) ⟨1272695, by rfl⟩ : syracuseStep 1696927 = 2545391) B2545391
theorem B1508511 : Blo 1506950 1508511 := bstep (se 1 (by rfl) ⟨1131383, by rfl⟩ : syracuseStep 1508511 = 2262767) B2262767
theorem B3622049 : Blo 1506950 3622049 := bstep (se 2 (by rfl) ⟨1358268, by rfl⟩ : syracuseStep 3622049 = 2716537) B2716537
theorem B14492839 : Blo 1506950 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B2262335 : Blo 1506950 2262335 := bstep (se 1 (by rfl) ⟨1696751, by rfl⟩ : syracuseStep 2262335 = 3393503) B3393503
theorem B1508679 : Blo 1506950 1508679 := bstep (se 1 (by rfl) ⟨1131509, by rfl⟩ : syracuseStep 1508679 = 2263019) B2263019
theorem B2262479 : Blo 1506950 2262479 := bstep (se 1 (by rfl) ⟨1696859, by rfl⟩ : syracuseStep 2262479 = 3393719) B3393719
theorem B1508847 : Blo 1506950 1508847 := bstep (se 1 (by rfl) ⟨1131635, by rfl⟩ : syracuseStep 1508847 = 2263271) B2263271
theorem B1508863 : Blo 1506950 1508863 := bstep (se 1 (by rfl) ⟨1131647, by rfl⟩ : syracuseStep 1508863 = 2263295) B2263295
theorem B21726751 : Blo 1506950 21726751 := bstep (se 1 (by rfl) ⟨16295063, by rfl⟩ : syracuseStep 21726751 = 32590127) B32590127
theorem B2262665 : Blo 1506950 2262665 := bstep (se 2 (by rfl) ⟨848499, by rfl⟩ : syracuseStep 2262665 = 1696999) B1696999
theorem B23529113 : Blo 1506950 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B5727935 : Blo 1506950 5727935 := bstep (se 1 (by rfl) ⟨4295951, by rfl⟩ : syracuseStep 5727935 = 8591903) B8591903
theorem B2263007 : Blo 1506950 2263007 := bstep (se 1 (by rfl) ⟨1697255, by rfl⟩ : syracuseStep 2263007 = 3394511) B3394511
theorem B2902043 : Blo 1506950 2902043 := bstep (se 1 (by rfl) ⟨2176532, by rfl⟩ : syracuseStep 2902043 = 4353065) B4353065
theorem B2263067 : Blo 1506950 2263067 := bstep (se 1 (by rfl) ⟨1697300, by rfl⟩ : syracuseStep 2263067 = 3394601) B3394601
theorem B33515603 : Blo 1506950 33515603 := bstep (se 1 (by rfl) ⟨25136702, by rfl⟩ : syracuseStep 33515603 = 50273405) B50273405
theorem B2263247 : Blo 1506950 2263247 := bstep (se 1 (by rfl) ⟨1697435, by rfl⟩ : syracuseStep 2263247 = 3394871) B3394871
theorem B5089499 : Blo 1506950 5089499 := bstep (se 1 (by rfl) ⟨3817124, by rfl⟩ : syracuseStep 5089499 = 7634249) B7634249
theorem B5089607 : Blo 1506950 5089607 := bstep (se 1 (by rfl) ⟨3817205, by rfl⟩ : syracuseStep 5089607 = 7634411) B7634411
theorem B3221947 : Blo 1506950 3221947 := bstep (se 1 (by rfl) ⟨2416460, by rfl⟩ : syracuseStep 3221947 = 4832921) B4832921
theorem B5728877 : Blo 1506950 5728877 := bstep (se 3 (by rfl) ⟨1074164, by rfl⟩ : syracuseStep 5728877 = 2148329) B2148329
theorem B3721963 : Blo 1506950 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B171944777 : Blo 1506950 171944777 := bstep (se 2 (by rfl) ⟨64479291, by rfl⟩ : syracuseStep 171944777 = 128958583) B128958583
theorem B35285969 : Blo 1506950 35285969 := bstep (se 2 (by rfl) ⟨13232238, by rfl⟩ : syracuseStep 35285969 = 26464477) B26464477
theorem B2862191 : Blo 1506950 2862191 := bstep (se 1 (by rfl) ⟨2146643, by rfl⟩ : syracuseStep 2862191 = 4293287) B4293287
theorem B5156423 : Blo 1506950 5156423 := bstep (se 1 (by rfl) ⟨3867317, by rfl⟩ : syracuseStep 5156423 = 7734635) B7734635
theorem B12398201 : Blo 1506950 12398201 := bstep (se 2 (by rfl) ⟨4649325, by rfl⟩ : syracuseStep 12398201 = 9298651) B9298651
theorem B19312303 : Blo 1506950 19312303 := bstep (se 1 (by rfl) ⟨14484227, by rfl⟩ : syracuseStep 19312303 = 28968455) B28968455
theorem B2543609 : Blo 1506950 2543609 := bstep (se 2 (by rfl) ⟨953853, by rfl⟩ : syracuseStep 2543609 = 1907707) B1907707
theorem B5156891 : Blo 1506950 5156891 := bstep (se 1 (by rfl) ⟨3867668, by rfl⟩ : syracuseStep 5156891 = 7735337) B7735337
theorem B6443039 : Blo 1506950 6443039 := bstep (se 1 (by rfl) ⟨4832279, by rfl⟩ : syracuseStep 6443039 = 9664559) B9664559
theorem B5091551 : Blo 1506950 5091551 := bstep (se 1 (by rfl) ⟨3818663, by rfl⟩ : syracuseStep 5091551 = 7637327) B7637327
theorem B2544041 : Blo 1506950 2544041 := bstep (se 2 (by rfl) ⟨954015, by rfl⟩ : syracuseStep 2544041 = 1908031) B1908031
theorem B5722559 : Blo 1506950 5722559 := bstep (se 1 (by rfl) ⟨4291919, by rfl⟩ : syracuseStep 5722559 = 8583839) B8583839
theorem B4829807 : Blo 1506950 4829807 := bstep (se 1 (by rfl) ⟨3622355, by rfl⟩ : syracuseStep 4829807 = 7244711) B7244711
theorem B5092091 : Blo 1506950 5092091 := bstep (se 1 (by rfl) ⟨3819068, by rfl⟩ : syracuseStep 5092091 = 7638137) B7638137
theorem B5092253 : Blo 1506950 5092253 := bstep (se 3 (by rfl) ⟨954797, by rfl⟩ : syracuseStep 5092253 = 1909595) B1909595
theorem B2544743 : Blo 1506950 2544743 := bstep (se 1 (by rfl) ⟨1908557, by rfl⟩ : syracuseStep 2544743 = 3817115) B3817115
theorem B7631981 : Blo 1506950 7631981 := bstep (se 3 (by rfl) ⟨1430996, by rfl⟩ : syracuseStep 7631981 = 2861993) B2861993
theorem B2544905 : Blo 1506950 2544905 := bstep (se 2 (by rfl) ⟨954339, by rfl⟩ : syracuseStep 2544905 = 1908679) B1908679
theorem B8582881 : Blo 1506950 8582881 := bstep (se 2 (by rfl) ⟨3218580, by rfl⟩ : syracuseStep 8582881 = 6437161) B6437161
theorem B137787151 : Blo 1506950 137787151 := bstep (se 1 (by rfl) ⟨103340363, by rfl⟩ : syracuseStep 137787151 = 206680727) B206680727
theorem B12883859 : Blo 1506950 12883859 := bstep (se 1 (by rfl) ⟨9662894, by rfl⟩ : syracuseStep 12883859 = 19325789) B19325789
theorem B3816031 : Blo 1506950 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B2579087 : Blo 1506950 2579087 := bstep (se 1 (by rfl) ⟨1934315, by rfl⟩ : syracuseStep 2579087 = 3868631) B3868631
theorem B99130355 : Blo 1506950 99130355 := bstep (se 1 (by rfl) ⟨74347766, by rfl⟩ : syracuseStep 99130355 = 148695533) B148695533
theorem B5086205 : Blo 1506950 5086205 := bstep (se 3 (by rfl) ⟨953663, by rfl⟩ : syracuseStep 5086205 = 1907327) B1907327
theorem B2415935 : Blo 1506950 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B66084443 : Blo 1506950 66084443 := bstep (se 1 (by rfl) ⟨49563332, by rfl⟩ : syracuseStep 66084443 = 99126665) B99126665
theorem B1506971 : Blo 1506950 1506971 := bstep (se 1 (by rfl) ⟨1130228, by rfl⟩ : syracuseStep 1506971 = 2260457) B2260457
theorem B1506975 : Blo 1506950 1506975 := bstep (se 1 (by rfl) ⟨1130231, by rfl⟩ : syracuseStep 1506975 = 2260463) B2260463
theorem B8593087 : Blo 1506950 8593087 := bstep (se 1 (by rfl) ⟨6444815, by rfl⟩ : syracuseStep 8593087 = 12889631) B12889631
theorem B1507067 : Blo 1506950 1507067 := bstep (se 1 (by rfl) ⟨1130300, by rfl⟩ : syracuseStep 1507067 = 2260601) B2260601
theorem B15695633 : Blo 1506950 15695633 := bstep (se 2 (by rfl) ⟨5885862, by rfl⟩ : syracuseStep 15695633 = 11771725) B11771725
theorem B1507199 : Blo 1506950 1507199 := bstep (se 1 (by rfl) ⟨1130399, by rfl⟩ : syracuseStep 1507199 = 2260799) B2260799
theorem B1507231 : Blo 1506950 1507231 := bstep (se 1 (by rfl) ⟨1130423, by rfl⟩ : syracuseStep 1507231 = 2260847) B2260847
theorem B3219367 : Blo 1506950 3219367 := bstep (se 1 (by rfl) ⟨2414525, by rfl⟩ : syracuseStep 3219367 = 4829051) B4829051
theorem B2260967 : Blo 1506950 2260967 := bstep (se 1 (by rfl) ⟨1695725, by rfl⟩ : syracuseStep 2260967 = 3391451) B3391451
theorem B2261033 : Blo 1506950 2261033 := bstep (se 2 (by rfl) ⟨847887, by rfl⟩ : syracuseStep 2261033 = 1695775) B1695775
theorem B1507391 : Blo 1506950 1507391 := bstep (se 1 (by rfl) ⟨1130543, by rfl⟩ : syracuseStep 1507391 = 2261087) B2261087
theorem B1507419 : Blo 1506950 1507419 := bstep (se 1 (by rfl) ⟨1130564, by rfl⟩ : syracuseStep 1507419 = 2261129) B2261129
theorem B1507431 : Blo 1506950 1507431 := bstep (se 1 (by rfl) ⟨1130573, by rfl⟩ : syracuseStep 1507431 = 2261147) B2261147
theorem B5800175 : Blo 1506950 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B1696027 : Blo 1506950 1696027 := bstep (se 1 (by rfl) ⟨1272020, by rfl⟩ : syracuseStep 1696027 = 2544041) B2544041
theorem B2261735 : Blo 1506950 2261735 := bstep (se 1 (by rfl) ⟨1696301, by rfl⟩ : syracuseStep 2261735 = 3392603) B3392603
theorem B1696495 : Blo 1506950 1696495 := bstep (se 1 (by rfl) ⟨1272371, by rfl⟩ : syracuseStep 1696495 = 2544743) B2544743
theorem B5087987 : Blo 1506950 5087987 := bstep (se 1 (by rfl) ⟨3815990, by rfl⟩ : syracuseStep 5087987 = 7631981) B7631981
theorem B7635707 : Blo 1506950 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B2261759 : Blo 1506950 2261759 := bstep (se 1 (by rfl) ⟨1696319, by rfl⟩ : syracuseStep 2261759 = 3392639) B3392639
theorem B5088041 : Blo 1506950 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B1696603 : Blo 1506950 1696603 := bstep (se 1 (by rfl) ⟨1272452, by rfl⟩ : syracuseStep 1696603 = 2544905) B2544905
theorem B1508223 : Blo 1506950 1508223 := bstep (se 1 (by rfl) ⟨1131167, by rfl⟩ : syracuseStep 1508223 = 2262335) B2262335
theorem B1508319 : Blo 1506950 1508319 := bstep (se 1 (by rfl) ⟨1131239, by rfl⟩ : syracuseStep 1508319 = 2262479) B2262479
theorem B1508443 : Blo 1506950 1508443 := bstep (se 1 (by rfl) ⟨1131332, by rfl⟩ : syracuseStep 1508443 = 2262665) B2262665
theorem B3818623 : Blo 1506950 3818623 := bstep (se 1 (by rfl) ⟨2863967, by rfl⟩ : syracuseStep 3818623 = 5727935) B5727935
theorem B1508671 : Blo 1506950 1508671 := bstep (se 1 (by rfl) ⟨1131503, by rfl⟩ : syracuseStep 1508671 = 2263007) B2263007
theorem B1934695 : Blo 1506950 1934695 := bstep (se 1 (by rfl) ⟨1451021, by rfl⟩ : syracuseStep 1934695 = 2902043) B2902043
theorem B1508711 : Blo 1506950 1508711 := bstep (se 1 (by rfl) ⟨1131533, by rfl⟩ : syracuseStep 1508711 = 2263067) B2263067
theorem B1508831 : Blo 1506950 1508831 := bstep (se 1 (by rfl) ⟨1131623, by rfl⟩ : syracuseStep 1508831 = 2263247) B2263247
theorem B3392999 : Blo 1506950 3392999 := bstep (se 1 (by rfl) ⟨2544749, by rfl⟩ : syracuseStep 3392999 = 5089499) B5089499
theorem B2262569 : Blo 1506950 2262569 := bstep (se 2 (by rfl) ⟨848463, by rfl⟩ : syracuseStep 2262569 = 1696927) B1696927
theorem B3393071 : Blo 1506950 3393071 := bstep (se 1 (by rfl) ⟨2544803, by rfl⟩ : syracuseStep 3393071 = 5089607) B5089607
theorem B12879485 : Blo 1506950 12879485 := bstep (se 3 (by rfl) ⟨2414903, by rfl⟩ : syracuseStep 12879485 = 4829807) B4829807
theorem B3819251 : Blo 1506950 3819251 := bstep (se 1 (by rfl) ⟨2864438, by rfl⟩ : syracuseStep 3819251 = 5728877) B5728877
theorem B66086903 : Blo 1506950 66086903 := bstep (se 1 (by rfl) ⟨49565177, by rfl⟩ : syracuseStep 66086903 = 99130355) B99130355
theorem B28969001 : Blo 1506950 28969001 := bstep (se 2 (by rfl) ⟨10863375, by rfl⟩ : syracuseStep 28969001 = 21726751) B21726751
theorem B25749737 : Blo 1506950 25749737 := bstep (se 2 (by rfl) ⟨9656151, by rfl⟩ : syracuseStep 25749737 = 19312303) B19312303
theorem B183716201 : Blo 1506950 183716201 := bstep (se 2 (by rfl) ⟨68893575, by rfl⟩ : syracuseStep 183716201 = 137787151) B137787151
theorem B10463755 : Blo 1506950 10463755 := bstep (se 1 (by rfl) ⟨7847816, by rfl⟩ : syracuseStep 10463755 = 15695633) B15695633
theorem B94095917 : Blo 1506950 94095917 := bstep (se 3 (by rfl) ⟨17642984, by rfl⟩ : syracuseStep 94095917 = 35285969) B35285969
theorem B4295359 : Blo 1506950 4295359 := bstep (se 1 (by rfl) ⟨3221519, by rfl⟩ : syracuseStep 4295359 = 6443039) B6443039
theorem B3394367 : Blo 1506950 3394367 := bstep (se 1 (by rfl) ⟨2545775, by rfl⟩ : syracuseStep 3394367 = 5091551) B5091551
theorem B495037291 : Blo 1506950 495037291 := bstep (se 1 (by rfl) ⟨371277968, by rfl⟩ : syracuseStep 495037291 = 742555937) B742555937
theorem B3394727 : Blo 1506950 3394727 := bstep (se 1 (by rfl) ⟨2546045, by rfl⟩ : syracuseStep 3394727 = 5092091) B5092091
theorem B4295929 : Blo 1506950 4295929 := bstep (se 2 (by rfl) ⟨1610973, by rfl⟩ : syracuseStep 4295929 = 3221947) B3221947
theorem B3394835 : Blo 1506950 3394835 := bstep (se 1 (by rfl) ⟨2546126, by rfl⟩ : syracuseStep 3394835 = 5092253) B5092253
theorem B14495071 : Blo 1506950 14495071 := bstep (se 1 (by rfl) ⟨10871303, by rfl⟩ : syracuseStep 14495071 = 21742607) B21742607
theorem B5090687 : Blo 1506950 5090687 := bstep (se 1 (by rfl) ⟨3818015, by rfl⟩ : syracuseStep 5090687 = 7636031) B7636031
theorem B8589239 : Blo 1506950 8589239 := bstep (se 1 (by rfl) ⟨6441929, by rfl⟩ : syracuseStep 8589239 = 12883859) B12883859
theorem B22343735 : Blo 1506950 22343735 := bstep (se 1 (by rfl) ⟨16757801, by rfl⟩ : syracuseStep 22343735 = 33515603) B33515603
theorem B1610623 : Blo 1506950 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B11457449 : Blo 1506950 11457449 := bstep (se 2 (by rfl) ⟨4296543, by rfl⟩ : syracuseStep 11457449 = 8593087) B8593087
theorem B3437615 : Blo 1506950 3437615 := bstep (se 1 (by rfl) ⟨2578211, by rfl⟩ : syracuseStep 3437615 = 5156423) B5156423
theorem B3437927 : Blo 1506950 3437927 := bstep (se 1 (by rfl) ⟨2578445, by rfl⟩ : syracuseStep 3437927 = 5156891) B5156891
theorem B185800139 : Blo 1506950 185800139 := bstep (se 1 (by rfl) ⟨139350104, by rfl⟩ : syracuseStep 185800139 = 278700209) B278700209
theorem B3815039 : Blo 1506950 3815039 := bstep (se 1 (by rfl) ⟨2861279, by rfl⟩ : syracuseStep 3815039 = 5722559) B5722559
theorem B8148937 : Blo 1506950 8148937 := bstep (se 2 (by rfl) ⟨3055851, by rfl⟩ : syracuseStep 8148937 = 6111703) B6111703
theorem B2414699 : Blo 1506950 2414699 := bstep (se 1 (by rfl) ⟨1811024, by rfl⟩ : syracuseStep 2414699 = 3622049) B3622049
theorem B4962617 : Blo 1506950 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B15686075 : Blo 1506950 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B19323785 : Blo 1506950 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B1719391 : Blo 1506950 1719391 := bstep (se 1 (by rfl) ⟨1289543, by rfl⟩ : syracuseStep 1719391 = 2579087) B2579087
theorem B114629851 : Blo 1506950 114629851 := bstep (se 1 (by rfl) ⟨85972388, by rfl⟩ : syracuseStep 114629851 = 171944777) B171944777
theorem B3390803 : Blo 1506950 3390803 := bstep (se 1 (by rfl) ⟨2543102, by rfl⟩ : syracuseStep 3390803 = 5086205) B5086205
theorem B1908127 : Blo 1506950 1908127 := bstep (se 1 (by rfl) ⟨1431095, by rfl⟩ : syracuseStep 1908127 = 2862191) B2862191
theorem B11443841 : Blo 1506950 11443841 := bstep (se 2 (by rfl) ⟨4291440, by rfl⟩ : syracuseStep 11443841 = 8582881) B8582881
theorem B44056295 : Blo 1506950 44056295 := bstep (se 1 (by rfl) ⟨33042221, by rfl⟩ : syracuseStep 44056295 = 66084443) B66084443
theorem B8265467 : Blo 1506950 8265467 := bstep (se 1 (by rfl) ⟨6199100, by rfl⟩ : syracuseStep 8265467 = 12398201) B12398201
theorem B4292489 : Blo 1506950 4292489 := bstep (se 2 (by rfl) ⟨1609683, by rfl⟩ : syracuseStep 4292489 = 3219367) B3219367
theorem B1507311 : Blo 1506950 1507311 := bstep (se 1 (by rfl) ⟨1130483, by rfl⟩ : syracuseStep 1507311 = 2260967) B2260967
theorem B1695739 : Blo 1506950 1695739 := bstep (se 1 (by rfl) ⟨1271804, by rfl⟩ : syracuseStep 1695739 = 2543609) B2543609
theorem B1507355 : Blo 1506950 1507355 := bstep (se 1 (by rfl) ⟨1130516, by rfl⟩ : syracuseStep 1507355 = 2261033) B2261033
theorem B3866783 : Blo 1506950 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B2261369 : Blo 1506950 2261369 := bstep (se 2 (by rfl) ⟨848013, by rfl⟩ : syracuseStep 2261369 = 1696027) B1696027
theorem B1507823 : Blo 1506950 1507823 := bstep (se 1 (by rfl) ⟨1130867, by rfl⟩ : syracuseStep 1507823 = 2261735) B2261735
theorem B3391991 : Blo 1506950 3391991 := bstep (se 1 (by rfl) ⟨2543993, by rfl⟩ : syracuseStep 3391991 = 5087987) B5087987
theorem B1507839 : Blo 1506950 1507839 := bstep (se 1 (by rfl) ⟨1130879, by rfl⟩ : syracuseStep 1507839 = 2261759) B2261759
theorem B3392027 : Blo 1506950 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B13951673 : Blo 1506950 13951673 := bstep (se 2 (by rfl) ⟨5231877, by rfl⟩ : syracuseStep 13951673 = 10463755) B10463755
theorem B5727145 : Blo 1506950 5727145 := bstep (se 2 (by rfl) ⟨2147679, by rfl⟩ : syracuseStep 5727145 = 4295359) B4295359
theorem B2261993 : Blo 1506950 2261993 := bstep (se 2 (by rfl) ⟨848247, by rfl⟩ : syracuseStep 2261993 = 1696495) B1696495
theorem B2261999 : Blo 1506950 2261999 := bstep (se 1 (by rfl) ⟨1696499, by rfl⟩ : syracuseStep 2261999 = 3392999) B3392999
theorem B1508379 : Blo 1506950 1508379 := bstep (se 1 (by rfl) ⟨1131284, by rfl⟩ : syracuseStep 1508379 = 2262569) B2262569
theorem B2262047 : Blo 1506950 2262047 := bstep (se 1 (by rfl) ⟨1696535, by rfl⟩ : syracuseStep 2262047 = 3393071) B3393071
theorem B8586323 : Blo 1506950 8586323 := bstep (se 1 (by rfl) ⟨6439742, by rfl⟩ : syracuseStep 8586323 = 12879485) B12879485
theorem B2262137 : Blo 1506950 2262137 := bstep (se 2 (by rfl) ⟨848301, by rfl⟩ : syracuseStep 2262137 = 1696603) B1696603
theorem B41829533 : Blo 1506950 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B44057935 : Blo 1506950 44057935 := bstep (se 1 (by rfl) ⟨33043451, by rfl⟩ : syracuseStep 44057935 = 66086903) B66086903
theorem B152839801 : Blo 1506950 152839801 := bstep (se 2 (by rfl) ⟨57314925, by rfl⟩ : syracuseStep 152839801 = 114629851) B114629851
theorem B5727905 : Blo 1506950 5727905 := bstep (se 2 (by rfl) ⟨2147964, by rfl⟩ : syracuseStep 5727905 = 4295929) B4295929
theorem B19326761 : Blo 1506950 19326761 := bstep (se 2 (by rfl) ⟨7247535, by rfl⟩ : syracuseStep 19326761 = 14495071) B14495071
theorem B2262911 : Blo 1506950 2262911 := bstep (se 1 (by rfl) ⟨1697183, by rfl⟩ : syracuseStep 2262911 = 3394367) B3394367
theorem B2263151 : Blo 1506950 2263151 := bstep (se 1 (by rfl) ⟨1697363, by rfl⟩ : syracuseStep 2263151 = 3394727) B3394727
theorem B2263223 : Blo 1506950 2263223 := bstep (se 1 (by rfl) ⟨1697417, by rfl⟩ : syracuseStep 2263223 = 3394835) B3394835
theorem B3393791 : Blo 1506950 3393791 := bstep (se 1 (by rfl) ⟨2545343, by rfl⟩ : syracuseStep 3393791 = 5090687) B5090687
theorem B7629227 : Blo 1506950 7629227 := bstep (se 1 (by rfl) ⟨5721920, by rfl⟩ : syracuseStep 7629227 = 11443841) B11443841
theorem B29370863 : Blo 1506950 29370863 := bstep (se 1 (by rfl) ⟨22028147, by rfl⟩ : syracuseStep 29370863 = 44056295) B44056295
theorem B2861659 : Blo 1506950 2861659 := bstep (se 1 (by rfl) ⟨2146244, by rfl⟩ : syracuseStep 2861659 = 4292489) B4292489
theorem B10865249 : Blo 1506950 10865249 := bstep (se 2 (by rfl) ⟨4074468, by rfl⟩ : syracuseStep 10865249 = 8148937) B8148937
theorem B59583293 : Blo 1506950 59583293 := bstep (se 3 (by rfl) ⟨11171867, by rfl⟩ : syracuseStep 59583293 = 22343735) B22343735
theorem B5090471 : Blo 1506950 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B7638299 : Blo 1506950 7638299 := bstep (se 1 (by rfl) ⟨5728724, by rfl⟩ : syracuseStep 7638299 = 11457449) B11457449
theorem B123866759 : Blo 1506950 123866759 := bstep (se 1 (by rfl) ⟨92900069, by rfl⟩ : syracuseStep 123866759 = 185800139) B185800139
theorem B2543359 : Blo 1506950 2543359 := bstep (se 1 (by rfl) ⟨1907519, by rfl⟩ : syracuseStep 2543359 = 3815039) B3815039
theorem B660049721 : Blo 1506950 660049721 := bstep (se 2 (by rfl) ⟨247518645, by rfl⟩ : syracuseStep 660049721 = 495037291) B495037291
theorem B19312667 : Blo 1506950 19312667 := bstep (se 1 (by rfl) ⟨14484500, by rfl⟩ : syracuseStep 19312667 = 28969001) B28969001
theorem B1609799 : Blo 1506950 1609799 := bstep (se 1 (by rfl) ⟨1207349, by rfl⟩ : syracuseStep 1609799 = 2414699) B2414699
theorem B17166491 : Blo 1506950 17166491 := bstep (se 1 (by rfl) ⟨12874868, by rfl⟩ : syracuseStep 17166491 = 25749737) B25749737
theorem B5091497 : Blo 1506950 5091497 := bstep (se 2 (by rfl) ⟨1909311, by rfl⟩ : syracuseStep 5091497 = 3818623) B3818623
theorem B62730611 : Blo 1506950 62730611 := bstep (se 1 (by rfl) ⟨47047958, by rfl⟩ : syracuseStep 62730611 = 94095917) B94095917
theorem B10318373 : Blo 1506950 10318373 := bstep (se 4 (by rfl) ⟨967347, by rfl⟩ : syracuseStep 10318373 = 1934695) B1934695
theorem B2544169 : Blo 1506950 2544169 := bstep (se 2 (by rfl) ⟨954063, by rfl⟩ : syracuseStep 2544169 = 1908127) B1908127
theorem B12882523 : Blo 1506950 12882523 := bstep (se 1 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 12882523 = 19323785) B19323785
theorem B8589989 : Blo 1506950 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B5510311 : Blo 1506950 5510311 := bstep (se 1 (by rfl) ⟨4132733, by rfl⟩ : syracuseStep 5510311 = 8265467) B8265467
theorem B2291743 : Blo 1506950 2291743 := bstep (se 1 (by rfl) ⟨1718807, by rfl⟩ : syracuseStep 2291743 = 3437615) B3437615
theorem B2291951 : Blo 1506950 2291951 := bstep (se 1 (by rfl) ⟨1718963, by rfl⟩ : syracuseStep 2291951 = 3437927) B3437927
theorem B2546167 : Blo 1506950 2546167 := bstep (se 1 (by rfl) ⟨1909625, by rfl⟩ : syracuseStep 2546167 = 3819251) B3819251
theorem B2292521 : Blo 1506950 2292521 := bstep (se 2 (by rfl) ⟨859695, by rfl⟩ : syracuseStep 2292521 = 1719391) B1719391
theorem B3308411 : Blo 1506950 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B122477467 : Blo 1506950 122477467 := bstep (se 1 (by rfl) ⟨91858100, by rfl⟩ : syracuseStep 122477467 = 183716201) B183716201
theorem B2260535 : Blo 1506950 2260535 := bstep (se 1 (by rfl) ⟨1695401, by rfl⟩ : syracuseStep 2260535 = 3390803) B3390803
theorem B5726159 : Blo 1506950 5726159 := bstep (se 1 (by rfl) ⟨4294619, by rfl⟩ : syracuseStep 5726159 = 8589239) B8589239
theorem B2260985 : Blo 1506950 2260985 := bstep (se 2 (by rfl) ⟨847869, by rfl⟩ : syracuseStep 2260985 = 1695739) B1695739
theorem B3055657 : Blo 1506950 3055657 := bstep (se 2 (by rfl) ⟨1145871, by rfl⟩ : syracuseStep 3055657 = 2291743) B2291743
theorem B11444327 : Blo 1506950 11444327 := bstep (se 1 (by rfl) ⟨8583245, by rfl⟩ : syracuseStep 11444327 = 17166491) B17166491
theorem B4292797 : Blo 1506950 4292797 := bstep (se 3 (by rfl) ⟨804899, by rfl⟩ : syracuseStep 4292797 = 1609799) B1609799
theorem B41820407 : Blo 1506950 41820407 := bstep (se 1 (by rfl) ⟨31365305, by rfl⟩ : syracuseStep 41820407 = 62730611) B62730611
theorem B1507579 : Blo 1506950 1507579 := bstep (se 1 (by rfl) ⟨1130684, by rfl⟩ : syracuseStep 1507579 = 2261369) B2261369
theorem B2261327 : Blo 1506950 2261327 := bstep (se 1 (by rfl) ⟨1695995, by rfl⟩ : syracuseStep 2261327 = 3391991) B3391991
theorem B2261351 : Blo 1506950 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B5726659 : Blo 1506950 5726659 := bstep (se 1 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 5726659 = 8589989) B8589989
theorem B1507995 : Blo 1506950 1507995 := bstep (se 1 (by rfl) ⟨1130996, by rfl⟩ : syracuseStep 1507995 = 2261993) B2261993
theorem B1507999 : Blo 1506950 1507999 := bstep (se 1 (by rfl) ⟨1130999, by rfl⟩ : syracuseStep 1507999 = 2261999) B2261999
theorem B1508031 : Blo 1506950 1508031 := bstep (se 1 (by rfl) ⟨1131023, by rfl⟩ : syracuseStep 1508031 = 2262047) B2262047
theorem B3392225 : Blo 1506950 3392225 := bstep (se 2 (by rfl) ⟨1272084, by rfl⟩ : syracuseStep 3392225 = 2544169) B2544169
theorem B1508091 : Blo 1506950 1508091 := bstep (se 1 (by rfl) ⟨1131068, by rfl⟩ : syracuseStep 1508091 = 2262137) B2262137
theorem B27886355 : Blo 1506950 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B3818603 : Blo 1506950 3818603 := bstep (se 1 (by rfl) ⟨2863952, by rfl⟩ : syracuseStep 3818603 = 5727905) B5727905
theorem B7636193 : Blo 1506950 7636193 := bstep (se 2 (by rfl) ⟨2863572, by rfl⟩ : syracuseStep 7636193 = 5727145) B5727145
theorem B1508607 : Blo 1506950 1508607 := bstep (se 1 (by rfl) ⟨1131455, by rfl⟩ : syracuseStep 1508607 = 2262911) B2262911
theorem B1508767 : Blo 1506950 1508767 := bstep (se 1 (by rfl) ⟨1131575, by rfl⟩ : syracuseStep 1508767 = 2263151) B2263151
theorem B1508815 : Blo 1506950 1508815 := bstep (se 1 (by rfl) ⟨1131611, by rfl⟩ : syracuseStep 1508815 = 2263223) B2263223
theorem B2262527 : Blo 1506950 2262527 := bstep (se 1 (by rfl) ⟨1696895, by rfl⟩ : syracuseStep 2262527 = 3393791) B3393791
theorem B7243499 : Blo 1506950 7243499 := bstep (se 1 (by rfl) ⟨5432624, by rfl⟩ : syracuseStep 7243499 = 10865249) B10865249
theorem B2205607 : Blo 1506950 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B6113389 : Blo 1506950 6113389 := bstep (se 3 (by rfl) ⟨1146260, by rfl⟩ : syracuseStep 6113389 = 2292521) B2292521
theorem B3393647 : Blo 1506950 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B203786401 : Blo 1506950 203786401 := bstep (se 2 (by rfl) ⟨76419900, by rfl⟩ : syracuseStep 203786401 = 152839801) B152839801
theorem B82577839 : Blo 1506950 82577839 := bstep (se 1 (by rfl) ⟨61933379, by rfl⟩ : syracuseStep 82577839 = 123866759) B123866759
theorem B3394331 : Blo 1506950 3394331 := bstep (se 1 (by rfl) ⟨2545748, by rfl⟩ : syracuseStep 3394331 = 5091497) B5091497
theorem B9301115 : Blo 1506950 9301115 := bstep (se 1 (by rfl) ⟨6975836, by rfl⟩ : syracuseStep 9301115 = 13951673) B13951673
theorem B3394889 : Blo 1506950 3394889 := bstep (se 2 (by rfl) ⟨1273083, by rfl⟩ : syracuseStep 3394889 = 2546167) B2546167
theorem B163303289 : Blo 1506950 163303289 := bstep (se 2 (by rfl) ⟨61238733, by rfl⟩ : syracuseStep 163303289 = 122477467) B122477467
theorem B1527967 : Blo 1506950 1527967 := bstep (se 1 (by rfl) ⟨1145975, by rfl⟩ : syracuseStep 1527967 = 2291951) B2291951
theorem B234975653 : Blo 1506950 234975653 := bstep (se 4 (by rfl) ⟨22028967, by rfl⟩ : syracuseStep 234975653 = 44057935) B44057935
theorem B5092199 : Blo 1506950 5092199 := bstep (se 1 (by rfl) ⟨3819149, by rfl⟩ : syracuseStep 5092199 = 7638299) B7638299
theorem B12875111 : Blo 1506950 12875111 := bstep (se 1 (by rfl) ⟨9656333, by rfl⟩ : syracuseStep 12875111 = 19312667) B19312667
theorem B6878915 : Blo 1506950 6878915 := bstep (se 1 (by rfl) ⟨5159186, by rfl⟩ : syracuseStep 6878915 = 10318373) B10318373
theorem B10311421 : Blo 1506950 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B1507323 : Blo 1506950 1507323 := bstep (se 1 (by rfl) ⟨1130492, by rfl⟩ : syracuseStep 1507323 = 2260985) B2260985
theorem B5724215 : Blo 1506950 5724215 := bstep (se 1 (by rfl) ⟨4293161, by rfl⟩ : syracuseStep 5724215 = 8586323) B8586323
theorem B3815545 : Blo 1506950 3815545 := bstep (se 2 (by rfl) ⟨1430829, by rfl⟩ : syracuseStep 3815545 = 2861659) B2861659
theorem B17176697 : Blo 1506950 17176697 := bstep (se 2 (by rfl) ⟨6441261, by rfl⟩ : syracuseStep 17176697 = 12882523) B12882523
theorem B117553301 : Blo 1506950 117553301 := bstep (se 6 (by rfl) ⟨2755155, by rfl⟩ : syracuseStep 117553301 = 5510311) B5510311
theorem B12884507 : Blo 1506950 12884507 := bstep (se 1 (by rfl) ⟨9663380, by rfl⟩ : syracuseStep 12884507 = 19326761) B19326761
theorem B78322301 : Blo 1506950 78322301 := bstep (se 3 (by rfl) ⟨14685431, by rfl⟩ : syracuseStep 78322301 = 29370863) B29370863
theorem B5086151 : Blo 1506950 5086151 := bstep (se 1 (by rfl) ⟨3814613, by rfl⟩ : syracuseStep 5086151 = 7629227) B7629227
theorem B39722195 : Blo 1506950 39722195 := bstep (se 1 (by rfl) ⟨29791646, by rfl⟩ : syracuseStep 39722195 = 59583293) B59583293
theorem B3391145 : Blo 1506950 3391145 := bstep (se 2 (by rfl) ⟨1271679, by rfl⟩ : syracuseStep 3391145 = 2543359) B2543359
theorem B1507023 : Blo 1506950 1507023 := bstep (se 1 (by rfl) ⟨1130267, by rfl⟩ : syracuseStep 1507023 = 2260535) B2260535
theorem B440033147 : Blo 1506950 440033147 := bstep (se 1 (by rfl) ⟨330024860, by rfl⟩ : syracuseStep 440033147 = 660049721) B660049721
theorem B3817439 : Blo 1506950 3817439 := bstep (se 1 (by rfl) ⟨2863079, by rfl⟩ : syracuseStep 3817439 = 5726159) B5726159
theorem B8151185 : Blo 1506950 8151185 := bstep (se 2 (by rfl) ⟨3056694, by rfl⟩ : syracuseStep 8151185 = 6113389) B6113389
theorem B5087393 : Blo 1506950 5087393 := bstep (se 2 (by rfl) ⟨1907772, by rfl⟩ : syracuseStep 5087393 = 3815545) B3815545
theorem B1507551 : Blo 1506950 1507551 := bstep (se 1 (by rfl) ⟨1130663, by rfl⟩ : syracuseStep 1507551 = 2261327) B2261327
theorem B1507567 : Blo 1506950 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B2261483 : Blo 1506950 2261483 := bstep (se 1 (by rfl) ⟨1696112, by rfl⟩ : syracuseStep 2261483 = 3392225) B3392225
theorem B7635545 : Blo 1506950 7635545 := bstep (se 2 (by rfl) ⟨2863329, by rfl⟩ : syracuseStep 7635545 = 5726659) B5726659
theorem B1508351 : Blo 1506950 1508351 := bstep (se 1 (by rfl) ⟨1131263, by rfl⟩ : syracuseStep 1508351 = 2262527) B2262527
theorem B2262431 : Blo 1506950 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B2262887 : Blo 1506950 2262887 := bstep (se 1 (by rfl) ⟨1697165, by rfl⟩ : syracuseStep 2262887 = 3394331) B3394331
theorem B2263259 : Blo 1506950 2263259 := bstep (se 1 (by rfl) ⟨1697444, by rfl⟩ : syracuseStep 2263259 = 3394889) B3394889
theorem B13748561 : Blo 1506950 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B4074209 : Blo 1506950 4074209 := bstep (se 2 (by rfl) ⟨1527828, by rfl⟩ : syracuseStep 4074209 = 3055657) B3055657
theorem B7629551 : Blo 1506950 7629551 := bstep (se 1 (by rfl) ⟨5722163, by rfl⟩ : syracuseStep 7629551 = 11444327) B11444327
theorem B27880271 : Blo 1506950 27880271 := bstep (se 1 (by rfl) ⟨20910203, by rfl⟩ : syracuseStep 27880271 = 41820407) B41820407
theorem B271715201 : Blo 1506950 271715201 := bstep (se 2 (by rfl) ⟨101893200, by rfl⟩ : syracuseStep 271715201 = 203786401) B203786401
theorem B156650435 : Blo 1506950 156650435 := bstep (se 1 (by rfl) ⟨117487826, by rfl⟩ : syracuseStep 156650435 = 234975653) B234975653
theorem B18590903 : Blo 1506950 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B105925853 : Blo 1506950 105925853 := bstep (se 3 (by rfl) ⟨19861097, by rfl⟩ : syracuseStep 105925853 = 39722195) B39722195
theorem B110103785 : Blo 1506950 110103785 := bstep (se 2 (by rfl) ⟨41288919, by rfl⟩ : syracuseStep 110103785 = 82577839) B82577839
theorem B3394799 : Blo 1506950 3394799 := bstep (se 1 (by rfl) ⟨2546099, by rfl⟩ : syracuseStep 3394799 = 5092199) B5092199
theorem B5090795 : Blo 1506950 5090795 := bstep (se 1 (by rfl) ⟨3818096, by rfl⟩ : syracuseStep 5090795 = 7636193) B7636193
theorem B4828999 : Blo 1506950 4828999 := bstep (se 1 (by rfl) ⟨3621749, by rfl⟩ : syracuseStep 4828999 = 7243499) B7243499
theorem B78368867 : Blo 1506950 78368867 := bstep (se 1 (by rfl) ⟨58776650, by rfl⟩ : syracuseStep 78368867 = 117553301) B117553301
theorem B8589671 : Blo 1506950 8589671 := bstep (se 1 (by rfl) ⟨6442253, by rfl⟩ : syracuseStep 8589671 = 12884507) B12884507
theorem B108868859 : Blo 1506950 108868859 := bstep (se 1 (by rfl) ⟨81651644, by rfl⟩ : syracuseStep 108868859 = 163303289) B163303289
theorem B2544959 : Blo 1506950 2544959 := bstep (se 1 (by rfl) ⟨1908719, by rfl⟩ : syracuseStep 2544959 = 3817439) B3817439
theorem B5723729 : Blo 1506950 5723729 := bstep (se 2 (by rfl) ⟨2146398, by rfl⟩ : syracuseStep 5723729 = 4292797) B4292797
theorem B24802973 : Blo 1506950 24802973 := bstep (se 3 (by rfl) ⟨4650557, by rfl⟩ : syracuseStep 24802973 = 9301115) B9301115
theorem B2545735 : Blo 1506950 2545735 := bstep (se 1 (by rfl) ⟨1909301, by rfl⟩ : syracuseStep 2545735 = 3818603) B3818603
theorem B8149157 : Blo 1506950 8149157 := bstep (se 4 (by rfl) ⟨763983, by rfl⟩ : syracuseStep 8149157 = 1527967) B1527967
theorem B8583407 : Blo 1506950 8583407 := bstep (se 1 (by rfl) ⟨6437555, by rfl⟩ : syracuseStep 8583407 = 12875111) B12875111
theorem B4585943 : Blo 1506950 4585943 := bstep (se 1 (by rfl) ⟨3439457, by rfl⟩ : syracuseStep 4585943 = 6878915) B6878915
theorem B3816143 : Blo 1506950 3816143 := bstep (se 1 (by rfl) ⟨2862107, by rfl⟩ : syracuseStep 3816143 = 5724215) B5724215
theorem B11451131 : Blo 1506950 11451131 := bstep (se 1 (by rfl) ⟨8588348, by rfl⟩ : syracuseStep 11451131 = 17176697) B17176697
theorem B52214867 : Blo 1506950 52214867 := bstep (se 1 (by rfl) ⟨39161150, by rfl⟩ : syracuseStep 52214867 = 78322301) B78322301
theorem B3390767 : Blo 1506950 3390767 := bstep (se 1 (by rfl) ⟨2543075, by rfl⟩ : syracuseStep 3390767 = 5086151) B5086151
theorem B2260763 : Blo 1506950 2260763 := bstep (se 1 (by rfl) ⟨1695572, by rfl⟩ : syracuseStep 2260763 = 3391145) B3391145
theorem B2940809 : Blo 1506950 2940809 := bstep (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) B2205607
theorem B293355431 : Blo 1506950 293355431 := bstep (se 1 (by rfl) ⟨220016573, by rfl⟩ : syracuseStep 293355431 = 440033147) B440033147
theorem B3391595 : Blo 1506950 3391595 := bstep (se 1 (by rfl) ⟨2543696, by rfl⟩ : syracuseStep 3391595 = 5087393) B5087393
theorem B5726447 : Blo 1506950 5726447 := bstep (se 1 (by rfl) ⟨4294835, by rfl⟩ : syracuseStep 5726447 = 8589671) B8589671
theorem B1507655 : Blo 1506950 1507655 := bstep (se 1 (by rfl) ⟨1130741, by rfl⟩ : syracuseStep 1507655 = 2261483) B2261483
theorem B282468941 : Blo 1506950 282468941 := bstep (se 3 (by rfl) ⟨52962926, by rfl⟩ : syracuseStep 282468941 = 105925853) B105925853
theorem B1696639 : Blo 1506950 1696639 := bstep (se 1 (by rfl) ⟨1272479, by rfl⟩ : syracuseStep 1696639 = 2544959) B2544959
theorem B1508287 : Blo 1506950 1508287 := bstep (se 1 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 1508287 = 2262431) B2262431
theorem B1508591 : Blo 1506950 1508591 := bstep (se 1 (by rfl) ⟨1131443, by rfl⟩ : syracuseStep 1508591 = 2262887) B2262887
theorem B31368629 : Blo 1506950 31368629 := bstep (se 5 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 31368629 = 2940809) B2940809
theorem B5432771 : Blo 1506950 5432771 := bstep (se 1 (by rfl) ⟨4074578, by rfl⟩ : syracuseStep 5432771 = 8149157) B8149157
theorem B1508839 : Blo 1506950 1508839 := bstep (se 1 (by rfl) ⟨1131629, by rfl⟩ : syracuseStep 1508839 = 2263259) B2263259
theorem B181143467 : Blo 1506950 181143467 := bstep (se 1 (by rfl) ⟨135857600, by rfl⟩ : syracuseStep 181143467 = 271715201) B271715201
theorem B104433623 : Blo 1506950 104433623 := bstep (se 1 (by rfl) ⟨78325217, by rfl⟩ : syracuseStep 104433623 = 156650435) B156650435
theorem B34809911 : Blo 1506950 34809911 := bstep (se 1 (by rfl) ⟨26107433, by rfl⟩ : syracuseStep 34809911 = 52214867) B52214867
theorem B73402523 : Blo 1506950 73402523 := bstep (se 1 (by rfl) ⟨55051892, by rfl⟩ : syracuseStep 73402523 = 110103785) B110103785
theorem B2263199 : Blo 1506950 2263199 := bstep (se 1 (by rfl) ⟨1697399, by rfl⟩ : syracuseStep 2263199 = 3394799) B3394799
theorem B3393863 : Blo 1506950 3393863 := bstep (se 1 (by rfl) ⟨2545397, by rfl⟩ : syracuseStep 3393863 = 5090795) B5090795
theorem B195570287 : Blo 1506950 195570287 := bstep (se 1 (by rfl) ⟨146677715, by rfl⟩ : syracuseStep 195570287 = 293355431) B293355431
theorem B3394313 : Blo 1506950 3394313 := bstep (se 2 (by rfl) ⟨1272867, by rfl⟩ : syracuseStep 3394313 = 2545735) B2545735
theorem B5434123 : Blo 1506950 5434123 := bstep (se 1 (by rfl) ⟨4075592, by rfl⟩ : syracuseStep 5434123 = 8151185) B8151185
theorem B5090363 : Blo 1506950 5090363 := bstep (se 1 (by rfl) ⟨3817772, by rfl⟩ : syracuseStep 5090363 = 7635545) B7635545
theorem B16535315 : Blo 1506950 16535315 := bstep (se 1 (by rfl) ⟨12401486, by rfl⟩ : syracuseStep 16535315 = 24802973) B24802973
theorem B5722271 : Blo 1506950 5722271 := bstep (se 1 (by rfl) ⟨4291703, by rfl⟩ : syracuseStep 5722271 = 8583407) B8583407
theorem B2544095 : Blo 1506950 2544095 := bstep (se 1 (by rfl) ⟨1908071, by rfl⟩ : syracuseStep 2544095 = 3816143) B3816143
theorem B2716139 : Blo 1506950 2716139 := bstep (se 1 (by rfl) ⟨2037104, by rfl⟩ : syracuseStep 2716139 = 4074209) B4074209
theorem B52245911 : Blo 1506950 52245911 := bstep (se 1 (by rfl) ⟨39184433, by rfl⟩ : syracuseStep 52245911 = 78368867) B78368867
theorem B72579239 : Blo 1506950 72579239 := bstep (se 1 (by rfl) ⟨54434429, by rfl⟩ : syracuseStep 72579239 = 108868859) B108868859
theorem B3815819 : Blo 1506950 3815819 := bstep (se 1 (by rfl) ⟨2861864, by rfl⟩ : syracuseStep 3815819 = 5723729) B5723729
theorem B12229181 : Blo 1506950 12229181 := bstep (se 3 (by rfl) ⟨2292971, by rfl⟩ : syracuseStep 12229181 = 4585943) B4585943
theorem B9165707 : Blo 1506950 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B5086367 : Blo 1506950 5086367 := bstep (se 1 (by rfl) ⟨3814775, by rfl⟩ : syracuseStep 5086367 = 7629551) B7629551
theorem B7634087 : Blo 1506950 7634087 := bstep (se 1 (by rfl) ⟨5725565, by rfl⟩ : syracuseStep 7634087 = 11451131) B11451131
theorem B18586847 : Blo 1506950 18586847 := bstep (se 1 (by rfl) ⟨13940135, by rfl⟩ : syracuseStep 18586847 = 27880271) B27880271
theorem B12393935 : Blo 1506950 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B2260511 : Blo 1506950 2260511 := bstep (se 1 (by rfl) ⟨1695383, by rfl⟩ : syracuseStep 2260511 = 3390767) B3390767
theorem B6438665 : Blo 1506950 6438665 := bstep (se 2 (by rfl) ⟨2414499, by rfl⟩ : syracuseStep 6438665 = 4828999) B4828999
theorem B1507175 : Blo 1506950 1507175 := bstep (se 1 (by rfl) ⟨1130381, by rfl⟩ : syracuseStep 1507175 = 2260763) B2260763
theorem B2261063 : Blo 1506950 2261063 := bstep (se 1 (by rfl) ⟨1695797, by rfl⟩ : syracuseStep 2261063 = 3391595) B3391595
theorem B3817631 : Blo 1506950 3817631 := bstep (se 1 (by rfl) ⟨2863223, by rfl⟩ : syracuseStep 3817631 = 5726447) B5726447
theorem B1696063 : Blo 1506950 1696063 := bstep (se 1 (by rfl) ⟨1272047, by rfl⟩ : syracuseStep 1696063 = 2544095) B2544095
theorem B3621847 : Blo 1506950 3621847 := bstep (se 1 (by rfl) ⟨2716385, by rfl⟩ : syracuseStep 3621847 = 5432771) B5432771
theorem B2262185 : Blo 1506950 2262185 := bstep (se 2 (by rfl) ⟨848319, by rfl⟩ : syracuseStep 2262185 = 1696639) B1696639
theorem B7243037 : Blo 1506950 7243037 := bstep (se 3 (by rfl) ⟨1358069, by rfl⟩ : syracuseStep 7243037 = 2716139) B2716139
theorem B1508799 : Blo 1506950 1508799 := bstep (se 1 (by rfl) ⟨1131599, by rfl⟩ : syracuseStep 1508799 = 2263199) B2263199
theorem B2262575 : Blo 1506950 2262575 := bstep (se 1 (by rfl) ⟨1696931, by rfl⟩ : syracuseStep 2262575 = 3393863) B3393863
theorem B8152787 : Blo 1506950 8152787 := bstep (se 1 (by rfl) ⟨6114590, by rfl⟩ : syracuseStep 8152787 = 12229181) B12229181
theorem B2262875 : Blo 1506950 2262875 := bstep (se 1 (by rfl) ⟨1697156, by rfl⟩ : syracuseStep 2262875 = 3394313) B3394313
theorem B3393575 : Blo 1506950 3393575 := bstep (se 1 (by rfl) ⟨2545181, by rfl⟩ : syracuseStep 3393575 = 5090363) B5090363
theorem B5089391 : Blo 1506950 5089391 := bstep (se 1 (by rfl) ⟨3817043, by rfl⟩ : syracuseStep 5089391 = 7634087) B7634087
theorem B188312627 : Blo 1506950 188312627 := bstep (se 1 (by rfl) ⟨141234470, by rfl⟩ : syracuseStep 188312627 = 282468941) B282468941
theorem B7245497 : Blo 1506950 7245497 := bstep (se 2 (by rfl) ⟨2717061, by rfl⟩ : syracuseStep 7245497 = 5434123) B5434123
theorem B120762311 : Blo 1506950 120762311 := bstep (se 1 (by rfl) ⟨90571733, by rfl⟩ : syracuseStep 120762311 = 181143467) B181143467
theorem B48935015 : Blo 1506950 48935015 := bstep (se 1 (by rfl) ⟨36701261, by rfl⟩ : syracuseStep 48935015 = 73402523) B73402523
theorem B48386159 : Blo 1506950 48386159 := bstep (se 1 (by rfl) ⟨36289619, by rfl⟩ : syracuseStep 48386159 = 72579239) B72579239
theorem B2543879 : Blo 1506950 2543879 := bstep (se 1 (by rfl) ⟨1907909, by rfl⟩ : syracuseStep 2543879 = 3815819) B3815819
theorem B130380191 : Blo 1506950 130380191 := bstep (se 1 (by rfl) ⟨97785143, by rfl⟩ : syracuseStep 130380191 = 195570287) B195570287
theorem B12391231 : Blo 1506950 12391231 := bstep (se 1 (by rfl) ⟨9293423, by rfl⟩ : syracuseStep 12391231 = 18586847) B18586847
theorem B8262623 : Blo 1506950 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B11023543 : Blo 1506950 11023543 := bstep (se 1 (by rfl) ⟨8267657, by rfl⟩ : syracuseStep 11023543 = 16535315) B16535315
theorem B3814847 : Blo 1506950 3814847 := bstep (se 1 (by rfl) ⟨2861135, by rfl⟩ : syracuseStep 3814847 = 5722271) B5722271
theorem B34830607 : Blo 1506950 34830607 := bstep (se 1 (by rfl) ⟨26122955, by rfl⟩ : syracuseStep 34830607 = 52245911) B52245911
theorem B20912419 : Blo 1506950 20912419 := bstep (se 1 (by rfl) ⟨15684314, by rfl⟩ : syracuseStep 20912419 = 31368629) B31368629
theorem B69622415 : Blo 1506950 69622415 := bstep (se 1 (by rfl) ⟨52216811, by rfl⟩ : syracuseStep 69622415 = 104433623) B104433623
theorem B23206607 : Blo 1506950 23206607 := bstep (se 1 (by rfl) ⟨17404955, by rfl⟩ : syracuseStep 23206607 = 34809911) B34809911
theorem B6110471 : Blo 1506950 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B3390911 : Blo 1506950 3390911 := bstep (se 1 (by rfl) ⟨2543183, by rfl⟩ : syracuseStep 3390911 = 5086367) B5086367
theorem B1507007 : Blo 1506950 1507007 := bstep (se 1 (by rfl) ⟨1130255, by rfl⟩ : syracuseStep 1507007 = 2260511) B2260511
theorem B4292443 : Blo 1506950 4292443 := bstep (se 1 (by rfl) ⟨3219332, by rfl⟩ : syracuseStep 4292443 = 6438665) B6438665
theorem B1507375 : Blo 1506950 1507375 := bstep (se 1 (by rfl) ⟨1130531, by rfl⟩ : syracuseStep 1507375 = 2261063) B2261063
theorem B1695919 : Blo 1506950 1695919 := bstep (se 1 (by rfl) ⟨1271939, by rfl⟩ : syracuseStep 1695919 = 2543879) B2543879
theorem B46440809 : Blo 1506950 46440809 := bstep (se 2 (by rfl) ⟨17415303, by rfl⟩ : syracuseStep 46440809 = 34830607) B34830607
theorem B2261417 : Blo 1506950 2261417 := bstep (se 2 (by rfl) ⟨848031, by rfl⟩ : syracuseStep 2261417 = 1696063) B1696063
theorem B1508123 : Blo 1506950 1508123 := bstep (se 1 (by rfl) ⟨1131092, by rfl⟩ : syracuseStep 1508123 = 2262185) B2262185
theorem B1508383 : Blo 1506950 1508383 := bstep (se 1 (by rfl) ⟨1131287, by rfl⟩ : syracuseStep 1508383 = 2262575) B2262575
theorem B1508583 : Blo 1506950 1508583 := bstep (se 1 (by rfl) ⟨1131437, by rfl⟩ : syracuseStep 1508583 = 2262875) B2262875
theorem B2262383 : Blo 1506950 2262383 := bstep (se 1 (by rfl) ⟨1696787, by rfl⟩ : syracuseStep 2262383 = 3393575) B3393575
theorem B3392927 : Blo 1506950 3392927 := bstep (se 1 (by rfl) ⟨2544695, by rfl⟩ : syracuseStep 3392927 = 5089391) B5089391
theorem B14698057 : Blo 1506950 14698057 := bstep (se 2 (by rfl) ⟨5511771, by rfl⟩ : syracuseStep 14698057 = 11023543) B11023543
theorem B4073647 : Blo 1506950 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B32623343 : Blo 1506950 32623343 := bstep (se 1 (by rfl) ⟨24467507, by rfl⟩ : syracuseStep 32623343 = 48935015) B48935015
theorem B86920127 : Blo 1506950 86920127 := bstep (se 1 (by rfl) ⟨65190095, by rfl⟩ : syracuseStep 86920127 = 130380191) B130380191
theorem B5508415 : Blo 1506950 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B4828691 : Blo 1506950 4828691 := bstep (se 1 (by rfl) ⟨3621518, by rfl⟩ : syracuseStep 4828691 = 7243037) B7243037
theorem B2543231 : Blo 1506950 2543231 := bstep (se 1 (by rfl) ⟨1907423, by rfl⟩ : syracuseStep 2543231 = 3814847) B3814847
theorem B5435191 : Blo 1506950 5435191 := bstep (se 1 (by rfl) ⟨4076393, by rfl⟩ : syracuseStep 5435191 = 8152787) B8152787
theorem B4829129 : Blo 1506950 4829129 := bstep (se 2 (by rfl) ⟨1810923, by rfl⟩ : syracuseStep 4829129 = 3621847) B3621847
theorem B15471071 : Blo 1506950 15471071 := bstep (se 1 (by rfl) ⟨11603303, by rfl⟩ : syracuseStep 15471071 = 23206607) B23206607
theorem B19321325 : Blo 1506950 19321325 := bstep (se 3 (by rfl) ⟨3622748, by rfl⟩ : syracuseStep 19321325 = 7245497) B7245497
theorem B5723257 : Blo 1506950 5723257 := bstep (se 2 (by rfl) ⟨2146221, by rfl⟩ : syracuseStep 5723257 = 4292443) B4292443
theorem B322032829 : Blo 1506950 322032829 := bstep (se 3 (by rfl) ⟨60381155, by rfl⟩ : syracuseStep 322032829 = 120762311) B120762311
theorem B32257439 : Blo 1506950 32257439 := bstep (se 1 (by rfl) ⟨24193079, by rfl⟩ : syracuseStep 32257439 = 48386159) B48386159
theorem B2545087 : Blo 1506950 2545087 := bstep (se 1 (by rfl) ⟨1908815, by rfl⟩ : syracuseStep 2545087 = 3817631) B3817631
theorem B27883225 : Blo 1506950 27883225 := bstep (se 2 (by rfl) ⟨10456209, by rfl⟩ : syracuseStep 27883225 = 20912419) B20912419
theorem B16521641 : Blo 1506950 16521641 := bstep (se 2 (by rfl) ⟨6195615, by rfl⟩ : syracuseStep 16521641 = 12391231) B12391231
theorem B46414943 : Blo 1506950 46414943 := bstep (se 1 (by rfl) ⟨34811207, by rfl⟩ : syracuseStep 46414943 = 69622415) B69622415
theorem B125541751 : Blo 1506950 125541751 := bstep (se 1 (by rfl) ⟨94156313, by rfl⟩ : syracuseStep 125541751 = 188312627) B188312627
theorem B2260607 : Blo 1506950 2260607 := bstep (se 1 (by rfl) ⟨1695455, by rfl⟩ : syracuseStep 2260607 = 3390911) B3390911
theorem B5431529 : Blo 1506950 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B2261225 : Blo 1506950 2261225 := bstep (se 2 (by rfl) ⟨847959, by rfl⟩ : syracuseStep 2261225 = 1695919) B1695919
theorem B1507611 : Blo 1506950 1507611 := bstep (se 1 (by rfl) ⟨1130708, by rfl⟩ : syracuseStep 1507611 = 2261417) B2261417
theorem B10314047 : Blo 1506950 10314047 := bstep (se 1 (by rfl) ⟨7735535, by rfl⟩ : syracuseStep 10314047 = 15471071) B15471071
theorem B1508255 : Blo 1506950 1508255 := bstep (se 1 (by rfl) ⟨1131191, by rfl⟩ : syracuseStep 1508255 = 2262383) B2262383
theorem B2261951 : Blo 1506950 2261951 := bstep (se 1 (by rfl) ⟨1696463, by rfl⟩ : syracuseStep 2261951 = 3392927) B3392927
theorem B21504959 : Blo 1506950 21504959 := bstep (se 1 (by rfl) ⟨16128719, by rfl⟩ : syracuseStep 21504959 = 32257439) B32257439
theorem B429377105 : Blo 1506950 429377105 := bstep (se 2 (by rfl) ⟨161016414, by rfl⟩ : syracuseStep 429377105 = 322032829) B322032829
theorem B29378213 : Blo 1506950 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B167389001 : Blo 1506950 167389001 := bstep (se 2 (by rfl) ⟨62770875, by rfl⟩ : syracuseStep 167389001 = 125541751) B125541751
theorem B3393449 : Blo 1506950 3393449 := bstep (se 2 (by rfl) ⟨1272543, by rfl⟩ : syracuseStep 3393449 = 2545087) B2545087
theorem B30943295 : Blo 1506950 30943295 := bstep (se 1 (by rfl) ⟨23207471, by rfl⟩ : syracuseStep 30943295 = 46414943) B46414943
theorem B19597409 : Blo 1506950 19597409 := bstep (se 2 (by rfl) ⟨7349028, by rfl⟩ : syracuseStep 19597409 = 14698057) B14698057
theorem B37177633 : Blo 1506950 37177633 := bstep (se 2 (by rfl) ⟨13941612, by rfl⟩ : syracuseStep 37177633 = 27883225) B27883225
theorem B30960539 : Blo 1506950 30960539 := bstep (se 1 (by rfl) ⟨23220404, by rfl⟩ : syracuseStep 30960539 = 46440809) B46440809
theorem B12880883 : Blo 1506950 12880883 := bstep (se 1 (by rfl) ⟨9660662, by rfl⟩ : syracuseStep 12880883 = 19321325) B19321325
theorem B7631009 : Blo 1506950 7631009 := bstep (se 2 (by rfl) ⟨2861628, by rfl⟩ : syracuseStep 7631009 = 5723257) B5723257
theorem B11014427 : Blo 1506950 11014427 := bstep (se 1 (by rfl) ⟨8260820, by rfl⟩ : syracuseStep 11014427 = 16521641) B16521641
theorem B57946751 : Blo 1506950 57946751 := bstep (se 1 (by rfl) ⟨43460063, by rfl⟩ : syracuseStep 57946751 = 86920127) B86920127
theorem B7246921 : Blo 1506950 7246921 := bstep (se 2 (by rfl) ⟨2717595, by rfl⟩ : syracuseStep 7246921 = 5435191) B5435191
theorem B12876509 : Blo 1506950 12876509 := bstep (se 3 (by rfl) ⟨2414345, by rfl⟩ : syracuseStep 12876509 = 4828691) B4828691
theorem B21748895 : Blo 1506950 21748895 := bstep (se 1 (by rfl) ⟨16311671, by rfl⟩ : syracuseStep 21748895 = 32623343) B32623343
theorem B1507071 : Blo 1506950 1507071 := bstep (se 1 (by rfl) ⟨1130303, by rfl⟩ : syracuseStep 1507071 = 2260607) B2260607
theorem B1695487 : Blo 1506950 1695487 := bstep (se 1 (by rfl) ⟨1271615, by rfl⟩ : syracuseStep 1695487 = 2543231) B2543231
theorem B3219419 : Blo 1506950 3219419 := bstep (se 1 (by rfl) ⟨2414564, by rfl⟩ : syracuseStep 3219419 = 4829129) B4829129
theorem B5087339 : Blo 1506950 5087339 := bstep (se 1 (by rfl) ⟨3815504, by rfl⟩ : syracuseStep 5087339 = 7631009) B7631009
theorem B3621019 : Blo 1506950 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B1507483 : Blo 1506950 1507483 := bstep (se 1 (by rfl) ⟨1130612, by rfl⟩ : syracuseStep 1507483 = 2261225) B2261225
theorem B49570177 : Blo 1506950 49570177 := bstep (se 2 (by rfl) ⟨18588816, by rfl⟩ : syracuseStep 49570177 = 37177633) B37177633
theorem B1507967 : Blo 1506950 1507967 := bstep (se 1 (by rfl) ⟨1130975, by rfl⟩ : syracuseStep 1507967 = 2261951) B2261951
theorem B14336639 : Blo 1506950 14336639 := bstep (se 1 (by rfl) ⟨10752479, by rfl⟩ : syracuseStep 14336639 = 21504959) B21504959
theorem B111592667 : Blo 1506950 111592667 := bstep (se 1 (by rfl) ⟨83694500, by rfl⟩ : syracuseStep 111592667 = 167389001) B167389001
theorem B2262299 : Blo 1506950 2262299 := bstep (se 1 (by rfl) ⟨1696724, by rfl⟩ : syracuseStep 2262299 = 3393449) B3393449
theorem B20628863 : Blo 1506950 20628863 := bstep (se 1 (by rfl) ⟨15471647, by rfl⟩ : syracuseStep 20628863 = 30943295) B30943295
theorem B8587255 : Blo 1506950 8587255 := bstep (se 1 (by rfl) ⟨6440441, by rfl⟩ : syracuseStep 8587255 = 12880883) B12880883
theorem B6876031 : Blo 1506950 6876031 := bstep (se 1 (by rfl) ⟨5157023, by rfl⟩ : syracuseStep 6876031 = 10314047) B10314047
theorem B29371805 : Blo 1506950 29371805 := bstep (se 3 (by rfl) ⟨5507213, by rfl⟩ : syracuseStep 29371805 = 11014427) B11014427
theorem B9662561 : Blo 1506950 9662561 := bstep (se 2 (by rfl) ⟨3623460, by rfl⟩ : syracuseStep 9662561 = 7246921) B7246921
theorem B20640359 : Blo 1506950 20640359 := bstep (se 1 (by rfl) ⟨15480269, by rfl⟩ : syracuseStep 20640359 = 30960539) B30960539
theorem B38631167 : Blo 1506950 38631167 := bstep (se 1 (by rfl) ⟨28973375, by rfl⟩ : syracuseStep 38631167 = 57946751) B57946751
theorem B286251403 : Blo 1506950 286251403 := bstep (se 1 (by rfl) ⟨214688552, by rfl⟩ : syracuseStep 286251403 = 429377105) B429377105
theorem B19585475 : Blo 1506950 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B13064939 : Blo 1506950 13064939 := bstep (se 1 (by rfl) ⟨9798704, by rfl⟩ : syracuseStep 13064939 = 19597409) B19597409
theorem B8584339 : Blo 1506950 8584339 := bstep (se 1 (by rfl) ⟨6438254, by rfl⟩ : syracuseStep 8584339 = 12876509) B12876509
theorem B14499263 : Blo 1506950 14499263 := bstep (se 1 (by rfl) ⟨10874447, by rfl⟩ : syracuseStep 14499263 = 21748895) B21748895
theorem B2260649 : Blo 1506950 2260649 := bstep (se 2 (by rfl) ⟨847743, by rfl⟩ : syracuseStep 2260649 = 1695487) B1695487
theorem B2146279 : Blo 1506950 2146279 := bstep (se 1 (by rfl) ⟨1609709, by rfl⟩ : syracuseStep 2146279 = 3219419) B3219419
theorem B3391559 : Blo 1506950 3391559 := bstep (se 1 (by rfl) ⟨2543669, by rfl⟩ : syracuseStep 3391559 = 5087339) B5087339
theorem B66093569 : Blo 1506950 66093569 := bstep (se 2 (by rfl) ⟨24785088, by rfl⟩ : syracuseStep 66093569 = 49570177) B49570177
theorem B1508199 : Blo 1506950 1508199 := bstep (se 1 (by rfl) ⟨1131149, by rfl⟩ : syracuseStep 1508199 = 2262299) B2262299
theorem B9168041 : Blo 1506950 9168041 := bstep (se 2 (by rfl) ⟨3438015, by rfl⟩ : syracuseStep 9168041 = 6876031) B6876031
theorem B11445785 : Blo 1506950 11445785 := bstep (se 2 (by rfl) ⟨4292169, by rfl⟩ : syracuseStep 11445785 = 8584339) B8584339
theorem B8709959 : Blo 1506950 8709959 := bstep (se 1 (by rfl) ⟨6532469, by rfl⟩ : syracuseStep 8709959 = 13064939) B13064939
theorem B19581203 : Blo 1506950 19581203 := bstep (se 1 (by rfl) ⟨14685902, by rfl⟩ : syracuseStep 19581203 = 29371805) B29371805
theorem B2861705 : Blo 1506950 2861705 := bstep (se 2 (by rfl) ⟨1073139, by rfl⟩ : syracuseStep 2861705 = 2146279) B2146279
theorem B6441707 : Blo 1506950 6441707 := bstep (se 1 (by rfl) ⟨4831280, by rfl⟩ : syracuseStep 6441707 = 9662561) B9662561
theorem B4828025 : Blo 1506950 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B381668537 : Blo 1506950 381668537 := bstep (se 2 (by rfl) ⟨143125701, by rfl⟩ : syracuseStep 381668537 = 286251403) B286251403
theorem B74395111 : Blo 1506950 74395111 := bstep (se 1 (by rfl) ⟨55796333, by rfl⟩ : syracuseStep 74395111 = 111592667) B111592667
theorem B11449673 : Blo 1506950 11449673 := bstep (se 2 (by rfl) ⟨4293627, by rfl⟩ : syracuseStep 11449673 = 8587255) B8587255
theorem B13760239 : Blo 1506950 13760239 := bstep (se 1 (by rfl) ⟨10320179, by rfl⟩ : syracuseStep 13760239 = 20640359) B20640359
theorem B9557759 : Blo 1506950 9557759 := bstep (se 1 (by rfl) ⟨7168319, by rfl⟩ : syracuseStep 9557759 = 14336639) B14336639
theorem B13752575 : Blo 1506950 13752575 := bstep (se 1 (by rfl) ⟨10314431, by rfl⟩ : syracuseStep 13752575 = 20628863) B20628863
theorem B25754111 : Blo 1506950 25754111 := bstep (se 1 (by rfl) ⟨19315583, by rfl⟩ : syracuseStep 25754111 = 38631167) B38631167
theorem B13056983 : Blo 1506950 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B9666175 : Blo 1506950 9666175 := bstep (se 1 (by rfl) ⟨7249631, by rfl⟩ : syracuseStep 9666175 = 14499263) B14499263
theorem B1507099 : Blo 1506950 1507099 := bstep (se 1 (by rfl) ⟨1130324, by rfl⟩ : syracuseStep 1507099 = 2260649) B2260649
theorem B2261039 : Blo 1506950 2261039 := bstep (se 1 (by rfl) ⟨1695779, by rfl⟩ : syracuseStep 2261039 = 3391559) B3391559
theorem B1017782765 : Blo 1506950 1017782765 := bstep (se 3 (by rfl) ⟨190834268, by rfl⟩ : syracuseStep 1017782765 = 381668537) B381668537
theorem B6112027 : Blo 1506950 6112027 := bstep (se 1 (by rfl) ⟨4584020, by rfl⟩ : syracuseStep 6112027 = 9168041) B9168041
theorem B9168383 : Blo 1506950 9168383 := bstep (se 1 (by rfl) ⟨6876287, by rfl⟩ : syracuseStep 9168383 = 13752575) B13752575
theorem B4294471 : Blo 1506950 4294471 := bstep (se 1 (by rfl) ⟨3220853, by rfl⟩ : syracuseStep 4294471 = 6441707) B6441707
theorem B12888233 : Blo 1506950 12888233 := bstep (se 2 (by rfl) ⟨4833087, by rfl⟩ : syracuseStep 12888233 = 9666175) B9666175
theorem B7630523 : Blo 1506950 7630523 := bstep (se 1 (by rfl) ⟨5722892, by rfl⟩ : syracuseStep 7630523 = 11445785) B11445785
theorem B13054135 : Blo 1506950 13054135 := bstep (se 1 (by rfl) ⟨9790601, by rfl⟩ : syracuseStep 13054135 = 19581203) B19581203
theorem B99193481 : Blo 1506950 99193481 := bstep (se 2 (by rfl) ⟨37197555, by rfl⟩ : syracuseStep 99193481 = 74395111) B74395111
theorem B8704655 : Blo 1506950 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B18346985 : Blo 1506950 18346985 := bstep (se 2 (by rfl) ⟨6880119, by rfl⟩ : syracuseStep 18346985 = 13760239) B13760239
theorem B12874733 : Blo 1506950 12874733 := bstep (se 3 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 12874733 = 4828025) B4828025
theorem B44062379 : Blo 1506950 44062379 := bstep (se 1 (by rfl) ⟨33046784, by rfl⟩ : syracuseStep 44062379 = 66093569) B66093569
theorem B7633115 : Blo 1506950 7633115 := bstep (se 1 (by rfl) ⟨5724836, by rfl⟩ : syracuseStep 7633115 = 11449673) B11449673
theorem B6371839 : Blo 1506950 6371839 := bstep (se 1 (by rfl) ⟨4778879, by rfl⟩ : syracuseStep 6371839 = 9557759) B9557759
theorem B5806639 : Blo 1506950 5806639 := bstep (se 1 (by rfl) ⟨4354979, by rfl⟩ : syracuseStep 5806639 = 8709959) B8709959
theorem B17169407 : Blo 1506950 17169407 := bstep (se 1 (by rfl) ⟨12877055, by rfl⟩ : syracuseStep 17169407 = 25754111) B25754111
theorem B1907803 : Blo 1506950 1907803 := bstep (se 1 (by rfl) ⟨1430852, by rfl⟩ : syracuseStep 1907803 = 2861705) B2861705
theorem B1507359 : Blo 1506950 1507359 := bstep (se 1 (by rfl) ⟨1130519, by rfl⟩ : syracuseStep 1507359 = 2261039) B2261039
theorem B12231323 : Blo 1506950 12231323 := bstep (se 1 (by rfl) ⟨9173492, by rfl⟩ : syracuseStep 12231323 = 18346985) B18346985
theorem B8495785 : Blo 1506950 8495785 := bstep (se 2 (by rfl) ⟨3185919, by rfl⟩ : syracuseStep 8495785 = 6371839) B6371839
theorem B7742185 : Blo 1506950 7742185 := bstep (se 2 (by rfl) ⟨2903319, by rfl⟩ : syracuseStep 7742185 = 5806639) B5806639
theorem B6112255 : Blo 1506950 6112255 := bstep (se 1 (by rfl) ⟨4584191, by rfl⟩ : syracuseStep 6112255 = 9168383) B9168383
theorem B32597477 : Blo 1506950 32597477 := bstep (se 4 (by rfl) ⟨3056013, by rfl⟩ : syracuseStep 32597477 = 6112027) B6112027
theorem B5088743 : Blo 1506950 5088743 := bstep (se 1 (by rfl) ⟨3816557, by rfl⟩ : syracuseStep 5088743 = 7633115) B7633115
theorem B11446271 : Blo 1506950 11446271 := bstep (se 1 (by rfl) ⟨8584703, by rfl⟩ : syracuseStep 11446271 = 17169407) B17169407
theorem B678521843 : Blo 1506950 678521843 := bstep (se 1 (by rfl) ⟨508891382, by rfl⟩ : syracuseStep 678521843 = 1017782765) B1017782765
theorem B66128987 : Blo 1506950 66128987 := bstep (se 1 (by rfl) ⟨49596740, by rfl⟩ : syracuseStep 66128987 = 99193481) B99193481
theorem B5803103 : Blo 1506950 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B2543737 : Blo 1506950 2543737 := bstep (se 2 (by rfl) ⟨953901, by rfl⟩ : syracuseStep 2543737 = 1907803) B1907803
theorem B17405513 : Blo 1506950 17405513 := bstep (se 2 (by rfl) ⟨6527067, by rfl⟩ : syracuseStep 17405513 = 13054135) B13054135
theorem B8583155 : Blo 1506950 8583155 := bstep (se 1 (by rfl) ⟨6437366, by rfl⟩ : syracuseStep 8583155 = 12874733) B12874733
theorem B29374919 : Blo 1506950 29374919 := bstep (se 1 (by rfl) ⟨22031189, by rfl⟩ : syracuseStep 29374919 = 44062379) B44062379
theorem B8592155 : Blo 1506950 8592155 := bstep (se 1 (by rfl) ⟨6444116, by rfl⟩ : syracuseStep 8592155 = 12888233) B12888233
theorem B5725961 : Blo 1506950 5725961 := bstep (se 2 (by rfl) ⟨2147235, by rfl⟩ : syracuseStep 5725961 = 4294471) B4294471
theorem B5087015 : Blo 1506950 5087015 := bstep (se 1 (by rfl) ⟨3815261, by rfl⟩ : syracuseStep 5087015 = 7630523) B7630523
theorem B3391649 : Blo 1506950 3391649 := bstep (se 2 (by rfl) ⟨1271868, by rfl⟩ : syracuseStep 3391649 = 2543737) B2543737
theorem B45310853 : Blo 1506950 45310853 := bstep (se 4 (by rfl) ⟨4247892, by rfl⟩ : syracuseStep 45310853 = 8495785) B8495785
theorem B3392495 : Blo 1506950 3392495 := bstep (se 1 (by rfl) ⟨2544371, by rfl⟩ : syracuseStep 3392495 = 5088743) B5088743
theorem B5728103 : Blo 1506950 5728103 := bstep (se 1 (by rfl) ⟨4296077, by rfl⟩ : syracuseStep 5728103 = 8592155) B8592155
theorem B452347895 : Blo 1506950 452347895 := bstep (se 1 (by rfl) ⟨339260921, by rfl⟩ : syracuseStep 452347895 = 678521843) B678521843
theorem B3868735 : Blo 1506950 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B8154215 : Blo 1506950 8154215 := bstep (se 1 (by rfl) ⟨6115661, by rfl⟩ : syracuseStep 8154215 = 12231323) B12231323
theorem B11603675 : Blo 1506950 11603675 := bstep (se 1 (by rfl) ⟨8702756, by rfl⟩ : syracuseStep 11603675 = 17405513) B17405513
theorem B41291653 : Blo 1506950 41291653 := bstep (se 4 (by rfl) ⟨3871092, by rfl⟩ : syracuseStep 41291653 = 7742185) B7742185
theorem B5722103 : Blo 1506950 5722103 := bstep (se 1 (by rfl) ⟨4291577, by rfl⟩ : syracuseStep 5722103 = 8583155) B8583155
theorem B7630847 : Blo 1506950 7630847 := bstep (se 1 (by rfl) ⟨5723135, by rfl⟩ : syracuseStep 7630847 = 11446271) B11446271
theorem B19583279 : Blo 1506950 19583279 := bstep (se 1 (by rfl) ⟨14687459, by rfl⟩ : syracuseStep 19583279 = 29374919) B29374919
theorem B44085991 : Blo 1506950 44085991 := bstep (se 1 (by rfl) ⟨33064493, by rfl⟩ : syracuseStep 44085991 = 66128987) B66128987
theorem B21731651 : Blo 1506950 21731651 := bstep (se 1 (by rfl) ⟨16298738, by rfl⟩ : syracuseStep 21731651 = 32597477) B32597477
theorem B8149673 : Blo 1506950 8149673 := bstep (se 2 (by rfl) ⟨3056127, by rfl⟩ : syracuseStep 8149673 = 6112255) B6112255
theorem B3817307 : Blo 1506950 3817307 := bstep (se 1 (by rfl) ⟨2862980, by rfl⟩ : syracuseStep 3817307 = 5725961) B5725961
theorem B3391343 : Blo 1506950 3391343 := bstep (se 1 (by rfl) ⟨2543507, by rfl⟩ : syracuseStep 3391343 = 5087015) B5087015
theorem B2261099 : Blo 1506950 2261099 := bstep (se 1 (by rfl) ⟨1695824, by rfl⟩ : syracuseStep 2261099 = 3391649) B3391649
theorem B2261663 : Blo 1506950 2261663 := bstep (se 1 (by rfl) ⟨1696247, by rfl⟩ : syracuseStep 2261663 = 3392495) B3392495
theorem B3818735 : Blo 1506950 3818735 := bstep (se 1 (by rfl) ⟨2864051, by rfl⟩ : syracuseStep 3818735 = 5728103) B5728103
theorem B301565263 : Blo 1506950 301565263 := bstep (se 1 (by rfl) ⟨226173947, by rfl⟩ : syracuseStep 301565263 = 452347895) B452347895
theorem B7735783 : Blo 1506950 7735783 := bstep (se 1 (by rfl) ⟨5801837, by rfl⟩ : syracuseStep 7735783 = 11603675) B11603675
theorem B5087231 : Blo 1506950 5087231 := bstep (se 1 (by rfl) ⟨3815423, by rfl⟩ : syracuseStep 5087231 = 7630847) B7630847
theorem B58781321 : Blo 1506950 58781321 := bstep (se 2 (by rfl) ⟨22042995, by rfl⟩ : syracuseStep 58781321 = 44085991) B44085991
theorem B14487767 : Blo 1506950 14487767 := bstep (se 1 (by rfl) ⟨10865825, by rfl⟩ : syracuseStep 14487767 = 21731651) B21731651
theorem B5436143 : Blo 1506950 5436143 := bstep (se 1 (by rfl) ⟨4077107, by rfl⟩ : syracuseStep 5436143 = 8154215) B8154215
theorem B120828941 : Blo 1506950 120828941 := bstep (se 3 (by rfl) ⟨22655426, by rfl⟩ : syracuseStep 120828941 = 45310853) B45310853
theorem B55055537 : Blo 1506950 55055537 := bstep (se 2 (by rfl) ⟨20645826, by rfl⟩ : syracuseStep 55055537 = 41291653) B41291653
theorem B2544871 : Blo 1506950 2544871 := bstep (se 1 (by rfl) ⟨1908653, by rfl⟩ : syracuseStep 2544871 = 3817307) B3817307
theorem B3814735 : Blo 1506950 3814735 := bstep (se 1 (by rfl) ⟨2861051, by rfl⟩ : syracuseStep 3814735 = 5722103) B5722103
theorem B5158313 : Blo 1506950 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B13055519 : Blo 1506950 13055519 := bstep (se 1 (by rfl) ⟨9791639, by rfl⟩ : syracuseStep 13055519 = 19583279) B19583279
theorem B21732461 : Blo 1506950 21732461 := bstep (se 3 (by rfl) ⟨4074836, by rfl⟩ : syracuseStep 21732461 = 8149673) B8149673
theorem B2260895 : Blo 1506950 2260895 := bstep (se 1 (by rfl) ⟨1695671, by rfl⟩ : syracuseStep 2260895 = 3391343) B3391343
theorem B1507399 : Blo 1506950 1507399 := bstep (se 1 (by rfl) ⟨1130549, by rfl⟩ : syracuseStep 1507399 = 2261099) B2261099
theorem B9658511 : Blo 1506950 9658511 := bstep (se 1 (by rfl) ⟨7243883, by rfl⟩ : syracuseStep 9658511 = 14487767) B14487767
theorem B1507775 : Blo 1506950 1507775 := bstep (se 1 (by rfl) ⟨1130831, by rfl⟩ : syracuseStep 1507775 = 2261663) B2261663
theorem B10314377 : Blo 1506950 10314377 := bstep (se 2 (by rfl) ⟨3867891, by rfl⟩ : syracuseStep 10314377 = 7735783) B7735783
theorem B80552627 : Blo 1506950 80552627 := bstep (se 1 (by rfl) ⟨60414470, by rfl⟩ : syracuseStep 80552627 = 120828941) B120828941
theorem B3393161 : Blo 1506950 3393161 := bstep (se 2 (by rfl) ⟨1272435, by rfl⟩ : syracuseStep 3393161 = 2544871) B2544871
theorem B3624095 : Blo 1506950 3624095 := bstep (se 1 (by rfl) ⟨2718071, by rfl⟩ : syracuseStep 3624095 = 5436143) B5436143
theorem B36703691 : Blo 1506950 36703691 := bstep (se 1 (by rfl) ⟨27527768, by rfl⟩ : syracuseStep 36703691 = 55055537) B55055537
theorem B14488307 : Blo 1506950 14488307 := bstep (se 1 (by rfl) ⟨10866230, by rfl⟩ : syracuseStep 14488307 = 21732461) B21732461
theorem B39187547 : Blo 1506950 39187547 := bstep (se 1 (by rfl) ⟨29390660, by rfl⟩ : syracuseStep 39187547 = 58781321) B58781321
theorem B2545823 : Blo 1506950 2545823 := bstep (se 1 (by rfl) ⟨1909367, by rfl⟩ : syracuseStep 2545823 = 3818735) B3818735
theorem B3438875 : Blo 1506950 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B34814717 : Blo 1506950 34814717 := bstep (se 3 (by rfl) ⟨6527759, by rfl⟩ : syracuseStep 34814717 = 13055519) B13055519
theorem B5086313 : Blo 1506950 5086313 := bstep (se 2 (by rfl) ⟨1907367, by rfl⟩ : syracuseStep 5086313 = 3814735) B3814735
theorem B402087017 : Blo 1506950 402087017 := bstep (se 2 (by rfl) ⟨150782631, by rfl⟩ : syracuseStep 402087017 = 301565263) B301565263
theorem B3391487 : Blo 1506950 3391487 := bstep (se 1 (by rfl) ⟨2543615, by rfl⟩ : syracuseStep 3391487 = 5087231) B5087231
theorem B1507263 : Blo 1506950 1507263 := bstep (se 1 (by rfl) ⟨1130447, by rfl⟩ : syracuseStep 1507263 = 2260895) B2260895
theorem B6439007 : Blo 1506950 6439007 := bstep (se 1 (by rfl) ⟨4829255, by rfl⟩ : syracuseStep 6439007 = 9658511) B9658511
theorem B9658871 : Blo 1506950 9658871 := bstep (se 1 (by rfl) ⟨7244153, by rfl⟩ : syracuseStep 9658871 = 14488307) B14488307
theorem B26125031 : Blo 1506950 26125031 := bstep (se 1 (by rfl) ⟨19593773, by rfl⟩ : syracuseStep 26125031 = 39187547) B39187547
theorem B2262107 : Blo 1506950 2262107 := bstep (se 1 (by rfl) ⟨1696580, by rfl⟩ : syracuseStep 2262107 = 3393161) B3393161
theorem B1697215 : Blo 1506950 1697215 := bstep (se 1 (by rfl) ⟨1272911, by rfl⟩ : syracuseStep 1697215 = 2545823) B2545823
theorem B23209811 : Blo 1506950 23209811 := bstep (se 1 (by rfl) ⟨17407358, by rfl⟩ : syracuseStep 23209811 = 34814717) B34814717
theorem B6876251 : Blo 1506950 6876251 := bstep (se 1 (by rfl) ⟨5157188, by rfl⟩ : syracuseStep 6876251 = 10314377) B10314377
theorem B53701751 : Blo 1506950 53701751 := bstep (se 1 (by rfl) ⟨40276313, by rfl⟩ : syracuseStep 53701751 = 80552627) B80552627
theorem B9170333 : Blo 1506950 9170333 := bstep (se 3 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 9170333 = 3438875) B3438875
theorem B3390875 : Blo 1506950 3390875 := bstep (se 1 (by rfl) ⟨2543156, by rfl⟩ : syracuseStep 3390875 = 5086313) B5086313
theorem B268058011 : Blo 1506950 268058011 := bstep (se 1 (by rfl) ⟨201043508, by rfl⟩ : syracuseStep 268058011 = 402087017) B402087017
theorem B2416063 : Blo 1506950 2416063 := bstep (se 1 (by rfl) ⟨1812047, by rfl⟩ : syracuseStep 2416063 = 3624095) B3624095
theorem B24469127 : Blo 1506950 24469127 := bstep (se 1 (by rfl) ⟨18351845, by rfl⟩ : syracuseStep 24469127 = 36703691) B36703691
theorem B2260991 : Blo 1506950 2260991 := bstep (se 1 (by rfl) ⟨1695743, by rfl⟩ : syracuseStep 2260991 = 3391487) B3391487
theorem B4292671 : Blo 1506950 4292671 := bstep (se 1 (by rfl) ⟨3219503, by rfl⟩ : syracuseStep 4292671 = 6439007) B6439007
theorem B143204669 : Blo 1506950 143204669 := bstep (se 3 (by rfl) ⟨26850875, by rfl⟩ : syracuseStep 143204669 = 53701751) B53701751
theorem B6439247 : Blo 1506950 6439247 := bstep (se 1 (by rfl) ⟨4829435, by rfl⟩ : syracuseStep 6439247 = 9658871) B9658871
theorem B1508071 : Blo 1506950 1508071 := bstep (se 1 (by rfl) ⟨1131053, by rfl⟩ : syracuseStep 1508071 = 2262107) B2262107
theorem B357410681 : Blo 1506950 357410681 := bstep (se 2 (by rfl) ⟨134029005, by rfl⟩ : syracuseStep 357410681 = 268058011) B268058011
theorem B3221417 : Blo 1506950 3221417 := bstep (se 2 (by rfl) ⟨1208031, by rfl⟩ : syracuseStep 3221417 = 2416063) B2416063
theorem B2262953 : Blo 1506950 2262953 := bstep (se 2 (by rfl) ⟨848607, by rfl⟩ : syracuseStep 2262953 = 1697215) B1697215
theorem B69666749 : Blo 1506950 69666749 := bstep (se 3 (by rfl) ⟨13062515, by rfl⟩ : syracuseStep 69666749 = 26125031) B26125031
theorem B6113555 : Blo 1506950 6113555 := bstep (se 1 (by rfl) ⟨4585166, by rfl⟩ : syracuseStep 6113555 = 9170333) B9170333
theorem B16312751 : Blo 1506950 16312751 := bstep (se 1 (by rfl) ⟨12234563, by rfl⟩ : syracuseStep 16312751 = 24469127) B24469127
theorem B4584167 : Blo 1506950 4584167 := bstep (se 1 (by rfl) ⟨3438125, by rfl⟩ : syracuseStep 4584167 = 6876251) B6876251
theorem B1507327 : Blo 1506950 1507327 := bstep (se 1 (by rfl) ⟨1130495, by rfl⟩ : syracuseStep 1507327 = 2260991) B2260991
theorem B15473207 : Blo 1506950 15473207 := bstep (se 1 (by rfl) ⟨11604905, by rfl⟩ : syracuseStep 15473207 = 23209811) B23209811
theorem B2260583 : Blo 1506950 2260583 := bstep (se 1 (by rfl) ⟨1695437, by rfl⟩ : syracuseStep 2260583 = 3390875) B3390875
theorem B4292831 : Blo 1506950 4292831 := bstep (se 1 (by rfl) ⟨3219623, by rfl⟩ : syracuseStep 4292831 = 6439247) B6439247
theorem B3056111 : Blo 1506950 3056111 := bstep (se 1 (by rfl) ⟨2292083, by rfl⟩ : syracuseStep 3056111 = 4584167) B4584167
theorem B238273787 : Blo 1506950 238273787 := bstep (se 1 (by rfl) ⟨178705340, by rfl⟩ : syracuseStep 238273787 = 357410681) B357410681
theorem B1508635 : Blo 1506950 1508635 := bstep (se 1 (by rfl) ⟨1131476, by rfl⟩ : syracuseStep 1508635 = 2262953) B2262953
theorem B10315471 : Blo 1506950 10315471 := bstep (se 1 (by rfl) ⟨7736603, by rfl⟩ : syracuseStep 10315471 = 15473207) B15473207
theorem B95469779 : Blo 1506950 95469779 := bstep (se 1 (by rfl) ⟨71602334, by rfl⟩ : syracuseStep 95469779 = 143204669) B143204669
theorem B46444499 : Blo 1506950 46444499 := bstep (se 1 (by rfl) ⟨34833374, by rfl⟩ : syracuseStep 46444499 = 69666749) B69666749
theorem B4075703 : Blo 1506950 4075703 := bstep (se 1 (by rfl) ⟨3056777, by rfl⟩ : syracuseStep 4075703 = 6113555) B6113555
theorem B10875167 : Blo 1506950 10875167 := bstep (se 1 (by rfl) ⟨8156375, by rfl⟩ : syracuseStep 10875167 = 16312751) B16312751
theorem B8590445 : Blo 1506950 8590445 := bstep (se 3 (by rfl) ⟨1610708, by rfl⟩ : syracuseStep 8590445 = 3221417) B3221417
theorem B5723561 : Blo 1506950 5723561 := bstep (se 2 (by rfl) ⟨2146335, by rfl⟩ : syracuseStep 5723561 = 4292671) B4292671
theorem B1507055 : Blo 1506950 1507055 := bstep (se 1 (by rfl) ⟨1130291, by rfl⟩ : syracuseStep 1507055 = 2260583) B2260583
theorem B7250111 : Blo 1506950 7250111 := bstep (se 1 (by rfl) ⟨5437583, by rfl⟩ : syracuseStep 7250111 = 10875167) B10875167
theorem B5726963 : Blo 1506950 5726963 := bstep (se 1 (by rfl) ⟨4295222, by rfl⟩ : syracuseStep 5726963 = 8590445) B8590445
theorem B63646519 : Blo 1506950 63646519 := bstep (se 1 (by rfl) ⟨47734889, by rfl⟩ : syracuseStep 63646519 = 95469779) B95469779
theorem B2861887 : Blo 1506950 2861887 := bstep (se 1 (by rfl) ⟨2146415, by rfl⟩ : syracuseStep 2861887 = 4292831) B4292831
theorem B30962999 : Blo 1506950 30962999 := bstep (se 1 (by rfl) ⟨23222249, by rfl⟩ : syracuseStep 30962999 = 46444499) B46444499
theorem B2717135 : Blo 1506950 2717135 := bstep (se 1 (by rfl) ⟨2037851, by rfl⟩ : syracuseStep 2717135 = 4075703) B4075703
theorem B2037407 : Blo 1506950 2037407 := bstep (se 1 (by rfl) ⟨1528055, by rfl⟩ : syracuseStep 2037407 = 3056111) B3056111
theorem B158849191 : Blo 1506950 158849191 := bstep (se 1 (by rfl) ⟨119136893, by rfl⟩ : syracuseStep 158849191 = 238273787) B238273787
theorem B3815707 : Blo 1506950 3815707 := bstep (se 1 (by rfl) ⟨2861780, by rfl⟩ : syracuseStep 3815707 = 5723561) B5723561
theorem B13753961 : Blo 1506950 13753961 := bstep (se 2 (by rfl) ⟨5157735, by rfl⟩ : syracuseStep 13753961 = 10315471) B10315471
theorem B4833407 : Blo 1506950 4833407 := bstep (se 1 (by rfl) ⟨3625055, by rfl⟩ : syracuseStep 4833407 = 7250111) B7250111
theorem B5087609 : Blo 1506950 5087609 := bstep (se 2 (by rfl) ⟨1907853, by rfl⟩ : syracuseStep 5087609 = 3815707) B3815707
theorem B3817975 : Blo 1506950 3817975 := bstep (se 1 (by rfl) ⟨2863481, by rfl⟩ : syracuseStep 3817975 = 5726963) B5726963
theorem B1811423 : Blo 1506950 1811423 := bstep (se 1 (by rfl) ⟨1358567, by rfl⟩ : syracuseStep 1811423 = 2717135) B2717135
theorem B84862025 : Blo 1506950 84862025 := bstep (se 2 (by rfl) ⟨31823259, by rfl⟩ : syracuseStep 84862025 = 63646519) B63646519
theorem B5433085 : Blo 1506950 5433085 := bstep (se 3 (by rfl) ⟨1018703, by rfl⟩ : syracuseStep 5433085 = 2037407) B2037407
theorem B9169307 : Blo 1506950 9169307 := bstep (se 1 (by rfl) ⟨6876980, by rfl⟩ : syracuseStep 9169307 = 13753961) B13753961
theorem B847195685 : Blo 1506950 847195685 := bstep (se 4 (by rfl) ⟨79424595, by rfl⟩ : syracuseStep 847195685 = 158849191) B158849191
theorem B20641999 : Blo 1506950 20641999 := bstep (se 1 (by rfl) ⟨15481499, by rfl⟩ : syracuseStep 20641999 = 30962999) B30962999
theorem B3815849 : Blo 1506950 3815849 := bstep (se 2 (by rfl) ⟨1430943, by rfl⟩ : syracuseStep 3815849 = 2861887) B2861887
theorem B3391739 : Blo 1506950 3391739 := bstep (se 1 (by rfl) ⟨2543804, by rfl⟩ : syracuseStep 3391739 = 5087609) B5087609
theorem B56574683 : Blo 1506950 56574683 := bstep (se 1 (by rfl) ⟨42431012, by rfl⟩ : syracuseStep 56574683 = 84862025) B84862025
theorem B28976453 : Blo 1506950 28976453 := bstep (se 4 (by rfl) ⟨2716542, by rfl⟩ : syracuseStep 28976453 = 5433085) B5433085
theorem B6112871 : Blo 1506950 6112871 := bstep (se 1 (by rfl) ⟨4584653, by rfl⟩ : syracuseStep 6112871 = 9169307) B9169307
theorem B3222271 : Blo 1506950 3222271 := bstep (se 1 (by rfl) ⟨2416703, by rfl⟩ : syracuseStep 3222271 = 4833407) B4833407
theorem B5090633 : Blo 1506950 5090633 := bstep (se 2 (by rfl) ⟨1908987, by rfl⟩ : syracuseStep 5090633 = 3817975) B3817975
theorem B2543899 : Blo 1506950 2543899 := bstep (se 1 (by rfl) ⟨1907924, by rfl⟩ : syracuseStep 2543899 = 3815849) B3815849
theorem B4830461 : Blo 1506950 4830461 := bstep (se 3 (by rfl) ⟨905711, by rfl⟩ : syracuseStep 4830461 = 1811423) B1811423
theorem B27522665 : Blo 1506950 27522665 := bstep (se 2 (by rfl) ⟨10320999, by rfl⟩ : syracuseStep 27522665 = 20641999) B20641999
theorem B564797123 : Blo 1506950 564797123 := bstep (se 1 (by rfl) ⟨423597842, by rfl⟩ : syracuseStep 564797123 = 847195685) B847195685
theorem B2261159 : Blo 1506950 2261159 := bstep (se 1 (by rfl) ⟨1695869, by rfl⟩ : syracuseStep 2261159 = 3391739) B3391739
theorem B3391865 : Blo 1506950 3391865 := bstep (se 2 (by rfl) ⟨1271949, by rfl⟩ : syracuseStep 3391865 = 2543899) B2543899
theorem B37716455 : Blo 1506950 37716455 := bstep (se 1 (by rfl) ⟨28287341, by rfl⟩ : syracuseStep 37716455 = 56574683) B56574683
theorem B3220307 : Blo 1506950 3220307 := bstep (se 1 (by rfl) ⟨2415230, by rfl⟩ : syracuseStep 3220307 = 4830461) B4830461
theorem B19317635 : Blo 1506950 19317635 := bstep (se 1 (by rfl) ⟨14488226, by rfl⟩ : syracuseStep 19317635 = 28976453) B28976453
theorem B3393755 : Blo 1506950 3393755 := bstep (se 1 (by rfl) ⟨2545316, by rfl⟩ : syracuseStep 3393755 = 5090633) B5090633
theorem B376531415 : Blo 1506950 376531415 := bstep (se 1 (by rfl) ⟨282398561, by rfl⟩ : syracuseStep 376531415 = 564797123) B564797123
theorem B4075247 : Blo 1506950 4075247 := bstep (se 1 (by rfl) ⟨3056435, by rfl⟩ : syracuseStep 4075247 = 6112871) B6112871
theorem B18348443 : Blo 1506950 18348443 := bstep (se 1 (by rfl) ⟨13761332, by rfl⟩ : syracuseStep 18348443 = 27522665) B27522665
theorem B17185445 : Blo 1506950 17185445 := bstep (se 4 (by rfl) ⟨1611135, by rfl⟩ : syracuseStep 17185445 = 3222271) B3222271
theorem B1507439 : Blo 1506950 1507439 := bstep (se 1 (by rfl) ⟨1130579, by rfl⟩ : syracuseStep 1507439 = 2261159) B2261159
theorem B2261243 : Blo 1506950 2261243 := bstep (se 1 (by rfl) ⟨1695932, by rfl⟩ : syracuseStep 2261243 = 3391865) B3391865
theorem B2146871 : Blo 1506950 2146871 := bstep (se 1 (by rfl) ⟨1610153, by rfl⟩ : syracuseStep 2146871 = 3220307) B3220307
theorem B12878423 : Blo 1506950 12878423 := bstep (se 1 (by rfl) ⟨9658817, by rfl⟩ : syracuseStep 12878423 = 19317635) B19317635
theorem B2262503 : Blo 1506950 2262503 := bstep (se 1 (by rfl) ⟨1696877, by rfl⟩ : syracuseStep 2262503 = 3393755) B3393755
theorem B12232295 : Blo 1506950 12232295 := bstep (se 1 (by rfl) ⟨9174221, by rfl⟩ : syracuseStep 12232295 = 18348443) B18348443
theorem B251020943 : Blo 1506950 251020943 := bstep (se 1 (by rfl) ⟨188265707, by rfl⟩ : syracuseStep 251020943 = 376531415) B376531415
theorem B25144303 : Blo 1506950 25144303 := bstep (se 1 (by rfl) ⟨18858227, by rfl⟩ : syracuseStep 25144303 = 37716455) B37716455
theorem B11456963 : Blo 1506950 11456963 := bstep (se 1 (by rfl) ⟨8592722, by rfl⟩ : syracuseStep 11456963 = 17185445) B17185445
theorem B2716831 : Blo 1506950 2716831 := bstep (se 1 (by rfl) ⟨2037623, by rfl⟩ : syracuseStep 2716831 = 4075247) B4075247
theorem B1507495 : Blo 1506950 1507495 := bstep (se 1 (by rfl) ⟨1130621, by rfl⟩ : syracuseStep 1507495 = 2261243) B2261243
theorem B8585615 : Blo 1506950 8585615 := bstep (se 1 (by rfl) ⟨6439211, by rfl⟩ : syracuseStep 8585615 = 12878423) B12878423
theorem B1508335 : Blo 1506950 1508335 := bstep (se 1 (by rfl) ⟨1131251, by rfl⟩ : syracuseStep 1508335 = 2262503) B2262503
theorem B167347295 : Blo 1506950 167347295 := bstep (se 1 (by rfl) ⟨125510471, by rfl⟩ : syracuseStep 167347295 = 251020943) B251020943
theorem B7637975 : Blo 1506950 7637975 := bstep (se 1 (by rfl) ⟨5728481, by rfl⟩ : syracuseStep 7637975 = 11456963) B11456963
theorem B8154863 : Blo 1506950 8154863 := bstep (se 1 (by rfl) ⟨6116147, by rfl⟩ : syracuseStep 8154863 = 12232295) B12232295
theorem B33525737 : Blo 1506950 33525737 := bstep (se 2 (by rfl) ⟨12572151, by rfl⟩ : syracuseStep 33525737 = 25144303) B25144303
theorem B14489765 : Blo 1506950 14489765 := bstep (se 4 (by rfl) ⟨1358415, by rfl⟩ : syracuseStep 14489765 = 2716831) B2716831
theorem B5724989 : Blo 1506950 5724989 := bstep (se 3 (by rfl) ⟨1073435, by rfl⟩ : syracuseStep 5724989 = 2146871) B2146871
theorem B9659843 : Blo 1506950 9659843 := bstep (se 1 (by rfl) ⟨7244882, by rfl⟩ : syracuseStep 9659843 = 14489765) B14489765
theorem B22350491 : Blo 1506950 22350491 := bstep (se 1 (by rfl) ⟨16762868, by rfl⟩ : syracuseStep 22350491 = 33525737) B33525737
theorem B5091983 : Blo 1506950 5091983 := bstep (se 1 (by rfl) ⟨3818987, by rfl⟩ : syracuseStep 5091983 = 7637975) B7637975
theorem B5436575 : Blo 1506950 5436575 := bstep (se 1 (by rfl) ⟨4077431, by rfl⟩ : syracuseStep 5436575 = 8154863) B8154863
theorem B5723743 : Blo 1506950 5723743 := bstep (se 1 (by rfl) ⟨4292807, by rfl⟩ : syracuseStep 5723743 = 8585615) B8585615
theorem B111564863 : Blo 1506950 111564863 := bstep (se 1 (by rfl) ⟨83673647, by rfl⟩ : syracuseStep 111564863 = 167347295) B167347295
theorem B3816659 : Blo 1506950 3816659 := bstep (se 1 (by rfl) ⟨2862494, by rfl⟩ : syracuseStep 3816659 = 5724989) B5724989
theorem B6439895 : Blo 1506950 6439895 := bstep (se 1 (by rfl) ⟨4829921, by rfl⟩ : syracuseStep 6439895 = 9659843) B9659843
theorem B74376575 : Blo 1506950 74376575 := bstep (se 1 (by rfl) ⟨55782431, by rfl⟩ : syracuseStep 74376575 = 111564863) B111564863
theorem B3394655 : Blo 1506950 3394655 := bstep (se 1 (by rfl) ⟨2545991, by rfl⟩ : syracuseStep 3394655 = 5091983) B5091983
theorem B3624383 : Blo 1506950 3624383 := bstep (se 1 (by rfl) ⟨2718287, by rfl⟩ : syracuseStep 3624383 = 5436575) B5436575
theorem B7631657 : Blo 1506950 7631657 := bstep (se 2 (by rfl) ⟨2861871, by rfl⟩ : syracuseStep 7631657 = 5723743) B5723743
theorem B2544439 : Blo 1506950 2544439 := bstep (se 1 (by rfl) ⟨1908329, by rfl⟩ : syracuseStep 2544439 = 3816659) B3816659
theorem B14900327 : Blo 1506950 14900327 := bstep (se 1 (by rfl) ⟨11175245, by rfl⟩ : syracuseStep 14900327 = 22350491) B22350491
theorem B5087771 : Blo 1506950 5087771 := bstep (se 1 (by rfl) ⟨3815828, by rfl⟩ : syracuseStep 5087771 = 7631657) B7631657
theorem B4293263 : Blo 1506950 4293263 := bstep (se 1 (by rfl) ⟨3219947, by rfl⟩ : syracuseStep 4293263 = 6439895) B6439895
theorem B3392585 : Blo 1506950 3392585 := bstep (se 2 (by rfl) ⟨1272219, by rfl⟩ : syracuseStep 3392585 = 2544439) B2544439
theorem B2263103 : Blo 1506950 2263103 := bstep (se 1 (by rfl) ⟨1697327, by rfl⟩ : syracuseStep 2263103 = 3394655) B3394655
theorem B9933551 : Blo 1506950 9933551 := bstep (se 1 (by rfl) ⟨7450163, by rfl⟩ : syracuseStep 9933551 = 14900327) B14900327
theorem B49584383 : Blo 1506950 49584383 := bstep (se 1 (by rfl) ⟨37188287, by rfl⟩ : syracuseStep 49584383 = 74376575) B74376575
theorem B9665021 : Blo 1506950 9665021 := bstep (se 3 (by rfl) ⟨1812191, by rfl⟩ : syracuseStep 9665021 = 3624383) B3624383
theorem B3391847 : Blo 1506950 3391847 := bstep (se 1 (by rfl) ⟨2543885, by rfl⟩ : syracuseStep 3391847 = 5087771) B5087771
theorem B2261723 : Blo 1506950 2261723 := bstep (se 1 (by rfl) ⟨1696292, by rfl⟩ : syracuseStep 2261723 = 3392585) B3392585
theorem B1508735 : Blo 1506950 1508735 := bstep (se 1 (by rfl) ⟨1131551, by rfl⟩ : syracuseStep 1508735 = 2263103) B2263103
theorem B33056255 : Blo 1506950 33056255 := bstep (se 1 (by rfl) ⟨24792191, by rfl⟩ : syracuseStep 33056255 = 49584383) B49584383
theorem B6622367 : Blo 1506950 6622367 := bstep (se 1 (by rfl) ⟨4966775, by rfl⟩ : syracuseStep 6622367 = 9933551) B9933551
theorem B6443347 : Blo 1506950 6443347 := bstep (se 1 (by rfl) ⟨4832510, by rfl⟩ : syracuseStep 6443347 = 9665021) B9665021
theorem B11448701 : Blo 1506950 11448701 := bstep (se 3 (by rfl) ⟨2146631, by rfl⟩ : syracuseStep 11448701 = 4293263) B4293263
theorem B2261231 : Blo 1506950 2261231 := bstep (se 1 (by rfl) ⟨1695923, by rfl⟩ : syracuseStep 2261231 = 3391847) B3391847
theorem B1507815 : Blo 1506950 1507815 := bstep (se 1 (by rfl) ⟨1130861, by rfl⟩ : syracuseStep 1507815 = 2261723) B2261723
theorem B22037503 : Blo 1506950 22037503 := bstep (se 1 (by rfl) ⟨16528127, by rfl⟩ : syracuseStep 22037503 = 33056255) B33056255
theorem B7632467 : Blo 1506950 7632467 := bstep (se 1 (by rfl) ⟨5724350, by rfl⟩ : syracuseStep 7632467 = 11448701) B11448701
theorem B8591129 : Blo 1506950 8591129 := bstep (se 2 (by rfl) ⟨3221673, by rfl⟩ : syracuseStep 8591129 = 6443347) B6443347
theorem B70638581 : Blo 1506950 70638581 := bstep (se 5 (by rfl) ⟨3311183, by rfl⟩ : syracuseStep 70638581 = 6622367) B6622367
theorem B1507487 : Blo 1506950 1507487 := bstep (se 1 (by rfl) ⟨1130615, by rfl⟩ : syracuseStep 1507487 = 2261231) B2261231
theorem B5088311 : Blo 1506950 5088311 := bstep (se 1 (by rfl) ⟨3816233, by rfl⟩ : syracuseStep 5088311 = 7632467) B7632467
theorem B5727419 : Blo 1506950 5727419 := bstep (se 1 (by rfl) ⟨4295564, by rfl⟩ : syracuseStep 5727419 = 8591129) B8591129
theorem B47092387 : Blo 1506950 47092387 := bstep (se 1 (by rfl) ⟨35319290, by rfl⟩ : syracuseStep 47092387 = 70638581) B70638581
theorem B29383337 : Blo 1506950 29383337 := bstep (se 2 (by rfl) ⟨11018751, by rfl⟩ : syracuseStep 29383337 = 22037503) B22037503
theorem B3392207 : Blo 1506950 3392207 := bstep (se 1 (by rfl) ⟨2544155, by rfl⟩ : syracuseStep 3392207 = 5088311) B5088311
theorem B3818279 : Blo 1506950 3818279 := bstep (se 1 (by rfl) ⟨2863709, by rfl⟩ : syracuseStep 3818279 = 5727419) B5727419
theorem B19588891 : Blo 1506950 19588891 := bstep (se 1 (by rfl) ⟨14691668, by rfl⟩ : syracuseStep 19588891 = 29383337) B29383337
theorem B62789849 : Blo 1506950 62789849 := bstep (se 2 (by rfl) ⟨23546193, by rfl⟩ : syracuseStep 62789849 = 47092387) B47092387
theorem B2261471 : Blo 1506950 2261471 := bstep (se 1 (by rfl) ⟨1696103, by rfl⟩ : syracuseStep 2261471 = 3392207) B3392207
theorem B26118521 : Blo 1506950 26118521 := bstep (se 2 (by rfl) ⟨9794445, by rfl⟩ : syracuseStep 26118521 = 19588891) B19588891
theorem B2545519 : Blo 1506950 2545519 := bstep (se 1 (by rfl) ⟨1909139, by rfl⟩ : syracuseStep 2545519 = 3818279) B3818279
theorem B41859899 : Blo 1506950 41859899 := bstep (se 1 (by rfl) ⟨31394924, by rfl⟩ : syracuseStep 41859899 = 62789849) B62789849
theorem B1507647 : Blo 1506950 1507647 := bstep (se 1 (by rfl) ⟨1130735, by rfl⟩ : syracuseStep 1507647 = 2261471) B2261471
theorem B3394025 : Blo 1506950 3394025 := bstep (se 2 (by rfl) ⟨1272759, by rfl⟩ : syracuseStep 3394025 = 2545519) B2545519
theorem B17412347 : Blo 1506950 17412347 := bstep (se 1 (by rfl) ⟨13059260, by rfl⟩ : syracuseStep 17412347 = 26118521) B26118521
theorem B27906599 : Blo 1506950 27906599 := bstep (se 1 (by rfl) ⟨20929949, by rfl⟩ : syracuseStep 27906599 = 41859899) B41859899
theorem B11608231 : Blo 1506950 11608231 := bstep (se 1 (by rfl) ⟨8706173, by rfl⟩ : syracuseStep 11608231 = 17412347) B17412347
theorem B18604399 : Blo 1506950 18604399 := bstep (se 1 (by rfl) ⟨13953299, by rfl⟩ : syracuseStep 18604399 = 27906599) B27906599
theorem B2262683 : Blo 1506950 2262683 := bstep (se 1 (by rfl) ⟨1697012, by rfl⟩ : syracuseStep 2262683 = 3394025) B3394025
theorem B24805865 : Blo 1506950 24805865 := bstep (se 2 (by rfl) ⟨9302199, by rfl⟩ : syracuseStep 24805865 = 18604399) B18604399
theorem B1508455 : Blo 1506950 1508455 := bstep (se 1 (by rfl) ⟨1131341, by rfl⟩ : syracuseStep 1508455 = 2262683) B2262683
theorem B15477641 : Blo 1506950 15477641 := bstep (se 2 (by rfl) ⟨5804115, by rfl⟩ : syracuseStep 15477641 = 11608231) B11608231
theorem B10318427 : Blo 1506950 10318427 := bstep (se 1 (by rfl) ⟨7738820, by rfl⟩ : syracuseStep 10318427 = 15477641) B15477641
theorem B66148973 : Blo 1506950 66148973 := bstep (se 3 (by rfl) ⟨12402932, by rfl⟩ : syracuseStep 66148973 = 24805865) B24805865
theorem B44099315 : Blo 1506950 44099315 := bstep (se 1 (by rfl) ⟨33074486, by rfl⟩ : syracuseStep 44099315 = 66148973) B66148973
theorem B6878951 : Blo 1506950 6878951 := bstep (se 1 (by rfl) ⟨5159213, by rfl⟩ : syracuseStep 6878951 = 10318427) B10318427
theorem B4585967 : Blo 1506950 4585967 := bstep (se 1 (by rfl) ⟨3439475, by rfl⟩ : syracuseStep 4585967 = 6878951) B6878951
theorem B29399543 : Blo 1506950 29399543 := bstep (se 1 (by rfl) ⟨22049657, by rfl⟩ : syracuseStep 29399543 = 44099315) B44099315
theorem B3057311 : Blo 1506950 3057311 := bstep (se 1 (by rfl) ⟨2292983, by rfl⟩ : syracuseStep 3057311 = 4585967) B4585967
theorem B19599695 : Blo 1506950 19599695 := bstep (se 1 (by rfl) ⟨14699771, by rfl⟩ : syracuseStep 19599695 = 29399543) B29399543
theorem B13066463 : Blo 1506950 13066463 := bstep (se 1 (by rfl) ⟨9799847, by rfl⟩ : syracuseStep 13066463 = 19599695) B19599695
theorem B8152829 : Blo 1506950 8152829 := bstep (se 3 (by rfl) ⟨1528655, by rfl⟩ : syracuseStep 8152829 = 3057311) B3057311
theorem B8710975 : Blo 1506950 8710975 := bstep (se 1 (by rfl) ⟨6533231, by rfl⟩ : syracuseStep 8710975 = 13066463) B13066463
theorem B5435219 : Blo 1506950 5435219 := bstep (se 1 (by rfl) ⟨4076414, by rfl⟩ : syracuseStep 5435219 = 8152829) B8152829
theorem B14493917 : Blo 1506950 14493917 := bstep (se 3 (by rfl) ⟨2717609, by rfl⟩ : syracuseStep 14493917 = 5435219) B5435219
theorem B11614633 : Blo 1506950 11614633 := bstep (se 2 (by rfl) ⟨4355487, by rfl⟩ : syracuseStep 11614633 = 8710975) B8710975
theorem B9662611 : Blo 1506950 9662611 := bstep (se 1 (by rfl) ⟨7246958, by rfl⟩ : syracuseStep 9662611 = 14493917) B14493917
theorem B61944709 : Blo 1506950 61944709 := bstep (se 4 (by rfl) ⟨5807316, by rfl⟩ : syracuseStep 61944709 = 11614633) B11614633
theorem B82592945 : Blo 1506950 82592945 := bstep (se 2 (by rfl) ⟨30972354, by rfl⟩ : syracuseStep 82592945 = 61944709) B61944709
theorem B12883481 : Blo 1506950 12883481 := bstep (se 2 (by rfl) ⟨4831305, by rfl⟩ : syracuseStep 12883481 = 9662611) B9662611
theorem B55061963 : Blo 1506950 55061963 := bstep (se 1 (by rfl) ⟨41296472, by rfl⟩ : syracuseStep 55061963 = 82592945) B82592945
theorem B8588987 : Blo 1506950 8588987 := bstep (se 1 (by rfl) ⟨6441740, by rfl⟩ : syracuseStep 8588987 = 12883481) B12883481
theorem B36707975 : Blo 1506950 36707975 := bstep (se 1 (by rfl) ⟨27530981, by rfl⟩ : syracuseStep 36707975 = 55061963) B55061963
theorem B5725991 : Blo 1506950 5725991 := bstep (se 1 (by rfl) ⟨4294493, by rfl⟩ : syracuseStep 5725991 = 8588987) B8588987
theorem B24471983 : Blo 1506950 24471983 := bstep (se 1 (by rfl) ⟨18353987, by rfl⟩ : syracuseStep 24471983 = 36707975) B36707975
theorem B3817327 : Blo 1506950 3817327 := bstep (se 1 (by rfl) ⟨2862995, by rfl⟩ : syracuseStep 3817327 = 5725991) B5725991
theorem B5089769 : Blo 1506950 5089769 := bstep (se 2 (by rfl) ⟨1908663, by rfl⟩ : syracuseStep 5089769 = 3817327) B3817327
theorem B16314655 : Blo 1506950 16314655 := bstep (se 1 (by rfl) ⟨12235991, by rfl⟩ : syracuseStep 16314655 = 24471983) B24471983
theorem B3393179 : Blo 1506950 3393179 := bstep (se 1 (by rfl) ⟨2544884, by rfl⟩ : syracuseStep 3393179 = 5089769) B5089769
theorem B21752873 : Blo 1506950 21752873 := bstep (se 2 (by rfl) ⟨8157327, by rfl⟩ : syracuseStep 21752873 = 16314655) B16314655
theorem B2262119 : Blo 1506950 2262119 := bstep (se 1 (by rfl) ⟨1696589, by rfl⟩ : syracuseStep 2262119 = 3393179) B3393179
theorem B14501915 : Blo 1506950 14501915 := bstep (se 1 (by rfl) ⟨10876436, by rfl⟩ : syracuseStep 14501915 = 21752873) B21752873
theorem B1508079 : Blo 1506950 1508079 := bstep (se 1 (by rfl) ⟨1131059, by rfl⟩ : syracuseStep 1508079 = 2262119) B2262119
theorem B9667943 : Blo 1506950 9667943 := bstep (se 1 (by rfl) ⟨7250957, by rfl⟩ : syracuseStep 9667943 = 14501915) B14501915
theorem B6445295 : Blo 1506950 6445295 := bstep (se 1 (by rfl) ⟨4833971, by rfl⟩ : syracuseStep 6445295 = 9667943) B9667943
theorem B4296863 : Blo 1506950 4296863 := bstep (se 1 (by rfl) ⟨3222647, by rfl⟩ : syracuseStep 4296863 = 6445295) B6445295
theorem B2864575 : Blo 1506950 2864575 := bstep (se 1 (by rfl) ⟨2148431, by rfl⟩ : syracuseStep 2864575 = 4296863) B4296863
theorem B3819433 : Blo 1506950 3819433 := bstep (se 2 (by rfl) ⟨1432287, by rfl⟩ : syracuseStep 3819433 = 2864575) B2864575
theorem B5092577 : Blo 1506950 5092577 := bstep (se 2 (by rfl) ⟨1909716, by rfl⟩ : syracuseStep 5092577 = 3819433) B3819433
theorem B3395051 : Blo 1506950 3395051 := bstep (se 1 (by rfl) ⟨2546288, by rfl⟩ : syracuseStep 3395051 = 5092577) B5092577
theorem B2263367 : Blo 1506950 2263367 := bstep (se 1 (by rfl) ⟨1697525, by rfl⟩ : syracuseStep 2263367 = 3395051) B3395051
theorem B1508911 : Blo 1506950 1508911 := bstep (se 1 (by rfl) ⟨1131683, by rfl⟩ : syracuseStep 1508911 = 2263367) B2263367

theorem C0 (j : ℕ) (h1 : 376737 ≤ j) (h2 : j ≤ 377236) : Blo 1506950 (4 * j + 3) := by
  interval_cases j
  · exact B1506951
  · exact B1506955
  · exact B1506959
  · exact B1506963
  · exact B1506967
  · exact B1506971
  · exact B1506975
  · exact B1506979
  · exact B1506983
  · exact B1506987
  · exact B1506991
  · exact B1506995
  · exact B1506999
  · exact B1507003
  · exact B1507007
  · exact B1507011
  · exact B1507015
  · exact B1507019
  · exact B1507023
  · exact B1507027
  · exact B1507031
  · exact B1507035
  · exact B1507039
  · exact B1507043
  · exact B1507047
  · exact B1507051
  · exact B1507055
  · exact B1507059
  · exact B1507063
  · exact B1507067
  · exact B1507071
  · exact B1507075
  · exact B1507079
  · exact B1507083
  · exact B1507087
  · exact B1507091
  · exact B1507095
  · exact B1507099
  · exact B1507103
  · exact B1507107
  · exact B1507111
  · exact B1507115
  · exact B1507119
  · exact B1507123
  · exact B1507127
  · exact B1507131
  · exact B1507135
  · exact B1507139
  · exact B1507143
  · exact B1507147
  · exact B1507151
  · exact B1507155
  · exact B1507159
  · exact B1507163
  · exact B1507167
  · exact B1507171
  · exact B1507175
  · exact B1507179
  · exact B1507183
  · exact B1507187
  · exact B1507191
  · exact B1507195
  · exact B1507199
  · exact B1507203
  · exact B1507207
  · exact B1507211
  · exact B1507215
  · exact B1507219
  · exact B1507223
  · exact B1507227
  · exact B1507231
  · exact B1507235
  · exact B1507239
  · exact B1507243
  · exact B1507247
  · exact B1507251
  · exact B1507255
  · exact B1507259
  · exact B1507263
  · exact B1507267
  · exact B1507271
  · exact B1507275
  · exact B1507279
  · exact B1507283
  · exact B1507287
  · exact B1507291
  · exact B1507295
  · exact B1507299
  · exact B1507303
  · exact B1507307
  · exact B1507311
  · exact B1507315
  · exact B1507319
  · exact B1507323
  · exact B1507327
  · exact B1507331
  · exact B1507335
  · exact B1507339
  · exact B1507343
  · exact B1507347
  · exact B1507351
  · exact B1507355
  · exact B1507359
  · exact B1507363
  · exact B1507367
  · exact B1507371
  · exact B1507375
  · exact B1507379
  · exact B1507383
  · exact B1507387
  · exact B1507391
  · exact B1507395
  · exact B1507399
  · exact B1507403
  · exact B1507407
  · exact B1507411
  · exact B1507415
  · exact B1507419
  · exact B1507423
  · exact B1507427
  · exact B1507431
  · exact B1507435
  · exact B1507439
  · exact B1507443
  · exact B1507447
  · exact B1507451
  · exact B1507455
  · exact B1507459
  · exact B1507463
  · exact B1507467
  · exact B1507471
  · exact B1507475
  · exact B1507479
  · exact B1507483
  · exact B1507487
  · exact B1507491
  · exact B1507495
  · exact B1507499
  · exact B1507503
  · exact B1507507
  · exact B1507511
  · exact B1507515
  · exact B1507519
  · exact B1507523
  · exact B1507527
  · exact B1507531
  · exact B1507535
  · exact B1507539
  · exact B1507543
  · exact B1507547
  · exact B1507551
  · exact B1507555
  · exact B1507559
  · exact B1507563
  · exact B1507567
  · exact B1507571
  · exact B1507575
  · exact B1507579
  · exact B1507583
  · exact B1507587
  · exact B1507591
  · exact B1507595
  · exact B1507599
  · exact B1507603
  · exact B1507607
  · exact B1507611
  · exact B1507615
  · exact B1507619
  · exact B1507623
  · exact B1507627
  · exact B1507631
  · exact B1507635
  · exact B1507639
  · exact B1507643
  · exact B1507647
  · exact B1507651
  · exact B1507655
  · exact B1507659
  · exact B1507663
  · exact B1507667
  · exact B1507671
  · exact B1507675
  · exact B1507679
  · exact B1507683
  · exact B1507687
  · exact B1507691
  · exact B1507695
  · exact B1507699
  · exact B1507703
  · exact B1507707
  · exact B1507711
  · exact B1507715
  · exact B1507719
  · exact B1507723
  · exact B1507727
  · exact B1507731
  · exact B1507735
  · exact B1507739
  · exact B1507743
  · exact B1507747
  · exact B1507751
  · exact B1507755
  · exact B1507759
  · exact B1507763
  · exact B1507767
  · exact B1507771
  · exact B1507775
  · exact B1507779
  · exact B1507783
  · exact B1507787
  · exact B1507791
  · exact B1507795
  · exact B1507799
  · exact B1507803
  · exact B1507807
  · exact B1507811
  · exact B1507815
  · exact B1507819
  · exact B1507823
  · exact B1507827
  · exact B1507831
  · exact B1507835
  · exact B1507839
  · exact B1507843
  · exact B1507847
  · exact B1507851
  · exact B1507855
  · exact B1507859
  · exact B1507863
  · exact B1507867
  · exact B1507871
  · exact B1507875
  · exact B1507879
  · exact B1507883
  · exact B1507887
  · exact B1507891
  · exact B1507895
  · exact B1507899
  · exact B1507903
  · exact B1507907
  · exact B1507911
  · exact B1507915
  · exact B1507919
  · exact B1507923
  · exact B1507927
  · exact B1507931
  · exact B1507935
  · exact B1507939
  · exact B1507943
  · exact B1507947
  · exact B1507951
  · exact B1507955
  · exact B1507959
  · exact B1507963
  · exact B1507967
  · exact B1507971
  · exact B1507975
  · exact B1507979
  · exact B1507983
  · exact B1507987
  · exact B1507991
  · exact B1507995
  · exact B1507999
  · exact B1508003
  · exact B1508007
  · exact B1508011
  · exact B1508015
  · exact B1508019
  · exact B1508023
  · exact B1508027
  · exact B1508031
  · exact B1508035
  · exact B1508039
  · exact B1508043
  · exact B1508047
  · exact B1508051
  · exact B1508055
  · exact B1508059
  · exact B1508063
  · exact B1508067
  · exact B1508071
  · exact B1508075
  · exact B1508079
  · exact B1508083
  · exact B1508087
  · exact B1508091
  · exact B1508095
  · exact B1508099
  · exact B1508103
  · exact B1508107
  · exact B1508111
  · exact B1508115
  · exact B1508119
  · exact B1508123
  · exact B1508127
  · exact B1508131
  · exact B1508135
  · exact B1508139
  · exact B1508143
  · exact B1508147
  · exact B1508151
  · exact B1508155
  · exact B1508159
  · exact B1508163
  · exact B1508167
  · exact B1508171
  · exact B1508175
  · exact B1508179
  · exact B1508183
  · exact B1508187
  · exact B1508191
  · exact B1508195
  · exact B1508199
  · exact B1508203
  · exact B1508207
  · exact B1508211
  · exact B1508215
  · exact B1508219
  · exact B1508223
  · exact B1508227
  · exact B1508231
  · exact B1508235
  · exact B1508239
  · exact B1508243
  · exact B1508247
  · exact B1508251
  · exact B1508255
  · exact B1508259
  · exact B1508263
  · exact B1508267
  · exact B1508271
  · exact B1508275
  · exact B1508279
  · exact B1508283
  · exact B1508287
  · exact B1508291
  · exact B1508295
  · exact B1508299
  · exact B1508303
  · exact B1508307
  · exact B1508311
  · exact B1508315
  · exact B1508319
  · exact B1508323
  · exact B1508327
  · exact B1508331
  · exact B1508335
  · exact B1508339
  · exact B1508343
  · exact B1508347
  · exact B1508351
  · exact B1508355
  · exact B1508359
  · exact B1508363
  · exact B1508367
  · exact B1508371
  · exact B1508375
  · exact B1508379
  · exact B1508383
  · exact B1508387
  · exact B1508391
  · exact B1508395
  · exact B1508399
  · exact B1508403
  · exact B1508407
  · exact B1508411
  · exact B1508415
  · exact B1508419
  · exact B1508423
  · exact B1508427
  · exact B1508431
  · exact B1508435
  · exact B1508439
  · exact B1508443
  · exact B1508447
  · exact B1508451
  · exact B1508455
  · exact B1508459
  · exact B1508463
  · exact B1508467
  · exact B1508471
  · exact B1508475
  · exact B1508479
  · exact B1508483
  · exact B1508487
  · exact B1508491
  · exact B1508495
  · exact B1508499
  · exact B1508503
  · exact B1508507
  · exact B1508511
  · exact B1508515
  · exact B1508519
  · exact B1508523
  · exact B1508527
  · exact B1508531
  · exact B1508535
  · exact B1508539
  · exact B1508543
  · exact B1508547
  · exact B1508551
  · exact B1508555
  · exact B1508559
  · exact B1508563
  · exact B1508567
  · exact B1508571
  · exact B1508575
  · exact B1508579
  · exact B1508583
  · exact B1508587
  · exact B1508591
  · exact B1508595
  · exact B1508599
  · exact B1508603
  · exact B1508607
  · exact B1508611
  · exact B1508615
  · exact B1508619
  · exact B1508623
  · exact B1508627
  · exact B1508631
  · exact B1508635
  · exact B1508639
  · exact B1508643
  · exact B1508647
  · exact B1508651
  · exact B1508655
  · exact B1508659
  · exact B1508663
  · exact B1508667
  · exact B1508671
  · exact B1508675
  · exact B1508679
  · exact B1508683
  · exact B1508687
  · exact B1508691
  · exact B1508695
  · exact B1508699
  · exact B1508703
  · exact B1508707
  · exact B1508711
  · exact B1508715
  · exact B1508719
  · exact B1508723
  · exact B1508727
  · exact B1508731
  · exact B1508735
  · exact B1508739
  · exact B1508743
  · exact B1508747
  · exact B1508751
  · exact B1508755
  · exact B1508759
  · exact B1508763
  · exact B1508767
  · exact B1508771
  · exact B1508775
  · exact B1508779
  · exact B1508783
  · exact B1508787
  · exact B1508791
  · exact B1508795
  · exact B1508799
  · exact B1508803
  · exact B1508807
  · exact B1508811
  · exact B1508815
  · exact B1508819
  · exact B1508823
  · exact B1508827
  · exact B1508831
  · exact B1508835
  · exact B1508839
  · exact B1508843
  · exact B1508847
  · exact B1508851
  · exact B1508855
  · exact B1508859
  · exact B1508863
  · exact B1508867
  · exact B1508871
  · exact B1508875
  · exact B1508879
  · exact B1508883
  · exact B1508887
  · exact B1508891
  · exact B1508895
  · exact B1508899
  · exact B1508903
  · exact B1508907
  · exact B1508911
  · exact B1508915
  · exact B1508919
  · exact B1508923
  · exact B1508927
  · exact B1508931
  · exact B1508935
  · exact B1508939
  · exact B1508943
  · exact B1508947

theorem solution (m : ℕ) (hlo : 1506950 ≤ m) (hhi : m ≤ 1508950) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 376737 ≤ j := by omega
    have hj2 : j ≤ 377236 := by omega
    have hb : Blo 1506950 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
