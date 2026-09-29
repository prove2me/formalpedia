-- Prove2me | solution 1 for syracuse_descends_range_1786094_1788094
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:45:58.130142+00:00
-- url     : https://prove2.me/submissions/583c2e07-595f-4456-af5e-4e7af6eafafd

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


theorem B9043973 : Blo 1786094 9043973 := bbase (se 4 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 9043973 = 1695745) (by norm_num)
theorem B3817477 : Blo 1786094 3817477 := bbase (se 4 (by rfl) ⟨357888, by rfl⟩ : syracuseStep 3817477 = 715777) (by norm_num)
theorem B2261029 : Blo 1786094 2261029 := bbase (se 4 (by rfl) ⟨211971, by rfl⟩ : syracuseStep 2261029 = 423943) (by norm_num)
theorem B10174517 : Blo 1786094 10174517 := bbase (se 5 (by rfl) ⟨476930, by rfl⟩ : syracuseStep 10174517 = 953861) (by norm_num)
theorem B5161013 : Blo 1786094 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B4022333 : Blo 1786094 4022333 := bbase (se 3 (by rfl) ⟨754187, by rfl⟩ : syracuseStep 4022333 = 1508375) (by norm_num)
theorem B3014725 : Blo 1786094 3014725 := bbase (se 4 (by rfl) ⟨282630, by rfl⟩ : syracuseStep 3014725 = 565261) (by norm_num)
theorem B2261125 : Blo 1786094 2261125 := bbase (se 4 (by rfl) ⟨211980, by rfl⟩ : syracuseStep 2261125 = 423961) (by norm_num)
theorem B4022405 : Blo 1786094 4022405 := bbase (se 4 (by rfl) ⟨377100, by rfl⟩ : syracuseStep 4022405 = 754201) (by norm_num)
theorem B8585365 : Blo 1786094 8585365 := bbase (se 6 (by rfl) ⟨201219, by rfl⟩ : syracuseStep 8585365 = 402439) (by norm_num)
theorem B2146457 : Blo 1786094 2146457 := bbase (se 2 (by rfl) ⟨804921, by rfl⟩ : syracuseStep 2146457 = 1609843) (by norm_num)
theorem B3014813 : Blo 1786094 3014813 := bbase (se 3 (by rfl) ⟨565277, by rfl⟩ : syracuseStep 3014813 = 1130555) (by norm_num)
theorem B6029477 : Blo 1786094 6029477 := bbase (se 4 (by rfl) ⟨565263, by rfl⟩ : syracuseStep 6029477 = 1130527) (by norm_num)
theorem B6439109 : Blo 1786094 6439109 := bbase (se 4 (by rfl) ⟨603666, by rfl⟩ : syracuseStep 6439109 = 1207333) (by norm_num)
theorem B4522189 : Blo 1786094 4522189 := bbase (se 3 (by rfl) ⟨847910, by rfl⟩ : syracuseStep 4522189 = 1695821) (by norm_num)
theorem B4022477 : Blo 1786094 4022477 := bbase (se 3 (by rfl) ⟨754214, by rfl⟩ : syracuseStep 4022477 = 1508429) (by norm_num)
theorem B3391733 : Blo 1786094 3391733 := bbase (se 5 (by rfl) ⟨158987, by rfl⟩ : syracuseStep 3391733 = 317975) (by norm_num)
theorem B4022549 : Blo 1786094 4022549 := bbase (se 6 (by rfl) ⟨94278, by rfl⟩ : syracuseStep 4022549 = 188557) (by norm_num)
theorem B3014941 : Blo 1786094 3014941 := bbase (se 3 (by rfl) ⟨565301, by rfl⟩ : syracuseStep 3014941 = 1130603) (by norm_num)
theorem B2261297 : Blo 1786094 2261297 := bbase (se 2 (by rfl) ⟨847986, by rfl⟩ : syracuseStep 2261297 = 1695973) (by norm_num)
theorem B4522301 : Blo 1786094 4522301 := bbase (se 3 (by rfl) ⟨847931, by rfl⟩ : syracuseStep 4522301 = 1695863) (by norm_num)
theorem B5431637 : Blo 1786094 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B4022621 : Blo 1786094 4022621 := bbase (se 3 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 4022621 = 1508483) (by norm_num)
theorem B2261353 : Blo 1786094 2261353 := bbase (se 2 (by rfl) ⟨848007, by rfl⟩ : syracuseStep 2261353 = 1696015) (by norm_num)
theorem B2679149 : Blo 1786094 2679149 := bbase (se 3 (by rfl) ⟨502340, by rfl⟩ : syracuseStep 2679149 = 1004681) (by norm_num)
theorem B17170805 : Blo 1786094 17170805 := bbase (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) (by norm_num)
theorem B3015029 : Blo 1786094 3015029 := bbase (se 5 (by rfl) ⟨141329, by rfl⟩ : syracuseStep 3015029 = 282659) (by norm_num)
theorem B2679173 : Blo 1786094 2679173 := bbase (se 4 (by rfl) ⟨251172, by rfl⟩ : syracuseStep 2679173 = 502345) (by norm_num)
theorem B3391885 : Blo 1786094 3391885 := bbase (se 3 (by rfl) ⟨635978, by rfl⟩ : syracuseStep 3391885 = 1271957) (by norm_num)
theorem B2679197 : Blo 1786094 2679197 := bbase (se 3 (by rfl) ⟨502349, by rfl⟩ : syracuseStep 2679197 = 1004699) (by norm_num)
theorem B3096997 : Blo 1786094 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B4022693 : Blo 1786094 4022693 := bbase (se 4 (by rfl) ⟨377127, by rfl⟩ : syracuseStep 4022693 = 754255) (by norm_num)
theorem B2679221 : Blo 1786094 2679221 := bbase (se 5 (by rfl) ⟨125588, by rfl⟩ : syracuseStep 2679221 = 251177) (by norm_num)
theorem B13762997 : Blo 1786094 13762997 := bbase (se 5 (by rfl) ⟨645140, by rfl⟩ : syracuseStep 13762997 = 1290281) (by norm_num)
theorem B2261449 : Blo 1786094 2261449 := bbase (se 2 (by rfl) ⟨848043, by rfl⟩ : syracuseStep 2261449 = 1696087) (by norm_num)
theorem B2679245 : Blo 1786094 2679245 := bbase (se 3 (by rfl) ⟨502358, by rfl⟩ : syracuseStep 2679245 = 1004717) (by norm_num)
theorem B2146765 : Blo 1786094 2146765 := bbase (se 3 (by rfl) ⟨402518, by rfl⟩ : syracuseStep 2146765 = 805037) (by norm_num)
theorem B2679269 : Blo 1786094 2679269 := bbase (se 4 (by rfl) ⟨251181, by rfl⟩ : syracuseStep 2679269 = 502363) (by norm_num)
theorem B1909217 : Blo 1786094 1909217 := bbase (se 2 (by rfl) ⟨715956, by rfl⟩ : syracuseStep 1909217 = 1431913) (by norm_num)
theorem B4022765 : Blo 1786094 4022765 := bbase (se 3 (by rfl) ⟨754268, by rfl⟩ : syracuseStep 4022765 = 1508537) (by norm_num)
theorem B3015157 : Blo 1786094 3015157 := bbase (se 5 (by rfl) ⟨141335, by rfl⟩ : syracuseStep 3015157 = 282671) (by norm_num)
theorem B2679293 : Blo 1786094 2679293 := bbase (se 3 (by rfl) ⟨502367, by rfl⟩ : syracuseStep 2679293 = 1004735) (by norm_num)
theorem B4522493 : Blo 1786094 4522493 := bbase (se 3 (by rfl) ⟨847967, by rfl⟩ : syracuseStep 4522493 = 1695935) (by norm_num)
theorem B4293125 : Blo 1786094 4293125 := bbase (se 4 (by rfl) ⟨402480, by rfl⟩ : syracuseStep 4293125 = 804961) (by norm_num)
theorem B2679317 : Blo 1786094 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B6439445 : Blo 1786094 6439445 := bbase (se 6 (by rfl) ⟨150924, by rfl⟩ : syracuseStep 6439445 = 301849) (by norm_num)
theorem B2679341 : Blo 1786094 2679341 := bbase (se 3 (by rfl) ⟨502376, by rfl⟩ : syracuseStep 2679341 = 1004753) (by norm_num)
theorem B4022837 : Blo 1786094 4022837 := bbase (se 5 (by rfl) ⟨188570, by rfl⟩ : syracuseStep 4022837 = 377141) (by norm_num)
theorem B3310141 : Blo 1786094 3310141 := bbase (se 3 (by rfl) ⟨620651, by rfl⟩ : syracuseStep 3310141 = 1241303) (by norm_num)
theorem B2679365 : Blo 1786094 2679365 := bbase (se 4 (by rfl) ⟨251190, by rfl⟩ : syracuseStep 2679365 = 502381) (by norm_num)
theorem B3015245 : Blo 1786094 3015245 := bbase (se 3 (by rfl) ⟨565358, by rfl⟩ : syracuseStep 3015245 = 1130717) (by norm_num)
theorem B6029909 : Blo 1786094 6029909 := bbase (se 8 (by rfl) ⟨35331, by rfl⟩ : syracuseStep 6029909 = 70663) (by norm_num)
theorem B12231253 : Blo 1786094 12231253 := bbase (se 8 (by rfl) ⟨71667, by rfl⟩ : syracuseStep 12231253 = 143335) (by norm_num)
theorem B2679389 : Blo 1786094 2679389 := bbase (se 3 (by rfl) ⟨502385, by rfl⟩ : syracuseStep 2679389 = 1004771) (by norm_num)
theorem B2482781 : Blo 1786094 2482781 := bbase (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) (by norm_num)
theorem B2679413 : Blo 1786094 2679413 := bbase (se 5 (by rfl) ⟨125597, by rfl⟩ : syracuseStep 2679413 = 251195) (by norm_num)
theorem B2261621 : Blo 1786094 2261621 := bbase (se 5 (by rfl) ⟨106013, by rfl⟩ : syracuseStep 2261621 = 212027) (by norm_num)
theorem B4022909 : Blo 1786094 4022909 := bbase (se 3 (by rfl) ⟨754295, by rfl⟩ : syracuseStep 4022909 = 1508591) (by norm_num)
theorem B2679437 : Blo 1786094 2679437 := bbase (se 3 (by rfl) ⟨502394, by rfl⟩ : syracuseStep 2679437 = 1004789) (by norm_num)
theorem B2679461 : Blo 1786094 2679461 := bbase (se 4 (by rfl) ⟨251199, by rfl⟩ : syracuseStep 2679461 = 502399) (by norm_num)
theorem B2146981 : Blo 1786094 2146981 := bbase (se 4 (by rfl) ⟨201279, by rfl⟩ : syracuseStep 2146981 = 402559) (by norm_num)
theorem B2261677 : Blo 1786094 2261677 := bbase (se 3 (by rfl) ⟨424064, by rfl⟩ : syracuseStep 2261677 = 848129) (by norm_num)
theorem B7635637 : Blo 1786094 7635637 := bbase (se 5 (by rfl) ⟨357920, by rfl⟩ : syracuseStep 7635637 = 715841) (by norm_num)
theorem B2679485 : Blo 1786094 2679485 := bbase (se 3 (by rfl) ⟨502403, by rfl⟩ : syracuseStep 2679485 = 1004807) (by norm_num)
theorem B3392189 : Blo 1786094 3392189 := bbase (se 3 (by rfl) ⟨636035, by rfl⟩ : syracuseStep 3392189 = 1272071) (by norm_num)
theorem B4293317 : Blo 1786094 4293317 := bbase (se 4 (by rfl) ⟨402498, by rfl⟩ : syracuseStep 4293317 = 804997) (by norm_num)
theorem B4022981 : Blo 1786094 4022981 := bbase (se 4 (by rfl) ⟨377154, by rfl⟩ : syracuseStep 4022981 = 754309) (by norm_num)
theorem B3015373 : Blo 1786094 3015373 := bbase (se 3 (by rfl) ⟨565382, by rfl⟩ : syracuseStep 3015373 = 1130765) (by norm_num)
theorem B2679509 : Blo 1786094 2679509 := bbase (se 7 (by rfl) ⟨31400, by rfl⟩ : syracuseStep 2679509 = 62801) (by norm_num)
theorem B2679533 : Blo 1786094 2679533 := bbase (se 3 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 2679533 = 1004825) (by norm_num)
theorem B2679557 : Blo 1786094 2679557 := bbase (se 4 (by rfl) ⟨251208, by rfl⟩ : syracuseStep 2679557 = 502417) (by norm_num)
theorem B6619909 : Blo 1786094 6619909 := bbase (se 4 (by rfl) ⟨620616, by rfl⟩ : syracuseStep 6619909 = 1241233) (by norm_num)
theorem B2261773 : Blo 1786094 2261773 := bbase (se 3 (by rfl) ⟨424082, by rfl⟩ : syracuseStep 2261773 = 848165) (by norm_num)
theorem B4023053 : Blo 1786094 4023053 := bbase (se 3 (by rfl) ⟨754322, by rfl⟩ : syracuseStep 4023053 = 1508645) (by norm_num)
theorem B2679581 : Blo 1786094 2679581 := bbase (se 3 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 2679581 = 1004843) (by norm_num)
theorem B3015461 : Blo 1786094 3015461 := bbase (se 4 (by rfl) ⟨282699, by rfl⟩ : syracuseStep 3015461 = 565399) (by norm_num)
theorem B2679605 : Blo 1786094 2679605 := bbase (se 5 (by rfl) ⟨125606, by rfl⟩ : syracuseStep 2679605 = 251213) (by norm_num)
theorem B2679629 : Blo 1786094 2679629 := bbase (se 3 (by rfl) ⟨502430, by rfl⟩ : syracuseStep 2679629 = 1004861) (by norm_num)
theorem B4522837 : Blo 1786094 4522837 := bbase (se 9 (by rfl) ⟨13250, by rfl⟩ : syracuseStep 4522837 = 26501) (by norm_num)
theorem B4023125 : Blo 1786094 4023125 := bbase (se 9 (by rfl) ⟨11786, by rfl⟩ : syracuseStep 4023125 = 23573) (by norm_num)
theorem B2679653 : Blo 1786094 2679653 := bbase (se 4 (by rfl) ⟨251217, by rfl⟩ : syracuseStep 2679653 = 502435) (by norm_num)
theorem B2679677 : Blo 1786094 2679677 := bbase (se 3 (by rfl) ⟨502439, by rfl⟩ : syracuseStep 2679677 = 1004879) (by norm_num)
theorem B2679701 : Blo 1786094 2679701 := bbase (se 6 (by rfl) ⟨62805, by rfl⟩ : syracuseStep 2679701 = 125611) (by norm_num)
theorem B4023197 : Blo 1786094 4023197 := bbase (se 3 (by rfl) ⟨754349, by rfl⟩ : syracuseStep 4023197 = 1508699) (by norm_num)
theorem B3015589 : Blo 1786094 3015589 := bbase (se 4 (by rfl) ⟨282711, by rfl⟩ : syracuseStep 3015589 = 565423) (by norm_num)
theorem B2679725 : Blo 1786094 2679725 := bbase (se 3 (by rfl) ⟨502448, by rfl⟩ : syracuseStep 2679725 = 1004897) (by norm_num)
theorem B2261945 : Blo 1786094 2261945 := bbase (se 2 (by rfl) ⟨848229, by rfl⟩ : syracuseStep 2261945 = 1696459) (by norm_num)
theorem B2679749 : Blo 1786094 2679749 := bbase (se 4 (by rfl) ⟨251226, by rfl⟩ : syracuseStep 2679749 = 502453) (by norm_num)
theorem B4522949 : Blo 1786094 4522949 := bbase (se 4 (by rfl) ⟨424026, by rfl⟩ : syracuseStep 4522949 = 848053) (by norm_num)
theorem B2679773 : Blo 1786094 2679773 := bbase (se 3 (by rfl) ⟨502457, by rfl⟩ : syracuseStep 2679773 = 1004915) (by norm_num)
theorem B4293605 : Blo 1786094 4293605 := bbase (se 4 (by rfl) ⟨402525, by rfl⟩ : syracuseStep 4293605 = 805051) (by norm_num)
theorem B2262001 : Blo 1786094 2262001 := bbase (se 2 (by rfl) ⟨848250, by rfl⟩ : syracuseStep 2262001 = 1696501) (by norm_num)
theorem B2679797 : Blo 1786094 2679797 := bbase (se 5 (by rfl) ⟨125615, by rfl⟩ : syracuseStep 2679797 = 251231) (by norm_num)
theorem B3015677 : Blo 1786094 3015677 := bbase (se 3 (by rfl) ⟨565439, by rfl⟩ : syracuseStep 3015677 = 1130879) (by norm_num)
theorem B6030341 : Blo 1786094 6030341 := bbase (se 4 (by rfl) ⟨565344, by rfl⟩ : syracuseStep 6030341 = 1130689) (by norm_num)
theorem B2679821 : Blo 1786094 2679821 := bbase (se 3 (by rfl) ⟨502466, by rfl⟩ : syracuseStep 2679821 = 1004933) (by norm_num)
theorem B2679845 : Blo 1786094 2679845 := bbase (se 4 (by rfl) ⟨251235, by rfl⟩ : syracuseStep 2679845 = 502471) (by norm_num)
theorem B2679869 : Blo 1786094 2679869 := bbase (se 3 (by rfl) ⟨502475, by rfl⟩ : syracuseStep 2679869 = 1004951) (by norm_num)
theorem B2262097 : Blo 1786094 2262097 := bbase (se 2 (by rfl) ⟨848286, by rfl⟩ : syracuseStep 2262097 = 1696573) (by norm_num)
theorem B2679893 : Blo 1786094 2679893 := bbase (se 8 (by rfl) ⟨15702, by rfl⟩ : syracuseStep 2679893 = 31405) (by norm_num)
theorem B6530149 : Blo 1786094 6530149 := bbase (se 4 (by rfl) ⟨612201, by rfl⟩ : syracuseStep 6530149 = 1224403) (by norm_num)
theorem B2679917 : Blo 1786094 2679917 := bbase (se 3 (by rfl) ⟨502484, by rfl⟩ : syracuseStep 2679917 = 1004969) (by norm_num)
theorem B3818605 : Blo 1786094 3818605 := bbase (se 3 (by rfl) ⟨715988, by rfl⟩ : syracuseStep 3818605 = 1431977) (by norm_num)
theorem B3015805 : Blo 1786094 3015805 := bbase (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) (by norm_num)
theorem B2679941 : Blo 1786094 2679941 := bbase (se 4 (by rfl) ⟨251244, by rfl⟩ : syracuseStep 2679941 = 502489) (by norm_num)
theorem B4523141 : Blo 1786094 4523141 := bbase (se 4 (by rfl) ⟨424044, by rfl⟩ : syracuseStep 4523141 = 848089) (by norm_num)
theorem B2679965 : Blo 1786094 2679965 := bbase (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) (by norm_num)
theorem B2679989 : Blo 1786094 2679989 := bbase (se 5 (by rfl) ⟨125624, by rfl⟩ : syracuseStep 2679989 = 251249) (by norm_num)
theorem B6784181 : Blo 1786094 6784181 := bbase (se 5 (by rfl) ⟨318008, by rfl⟩ : syracuseStep 6784181 = 636017) (by norm_num)
theorem B2680013 : Blo 1786094 2680013 := bbase (se 3 (by rfl) ⟨502502, by rfl⟩ : syracuseStep 2680013 = 1005005) (by norm_num)
theorem B11445461 : Blo 1786094 11445461 := bbase (se 7 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 11445461 = 268253) (by norm_num)
theorem B3015893 : Blo 1786094 3015893 := bbase (se 7 (by rfl) ⟨35342, by rfl⟩ : syracuseStep 3015893 = 70685) (by norm_num)
theorem B2680037 : Blo 1786094 2680037 := bbase (se 4 (by rfl) ⟨251253, by rfl⟩ : syracuseStep 2680037 = 502507) (by norm_num)
theorem B2680061 : Blo 1786094 2680061 := bbase (se 3 (by rfl) ⟨502511, by rfl⟩ : syracuseStep 2680061 = 1005023) (by norm_num)
theorem B2262269 : Blo 1786094 2262269 := bbase (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) (by norm_num)
theorem B2147581 : Blo 1786094 2147581 := bbase (se 3 (by rfl) ⟨402671, by rfl⟩ : syracuseStep 2147581 = 805343) (by norm_num)
theorem B9045269 : Blo 1786094 9045269 := bbase (se 6 (by rfl) ⟨211998, by rfl⟩ : syracuseStep 9045269 = 423997) (by norm_num)
theorem B2680085 : Blo 1786094 2680085 := bbase (se 6 (by rfl) ⟨62814, by rfl⟩ : syracuseStep 2680085 = 125629) (by norm_num)
theorem B2680109 : Blo 1786094 2680109 := bbase (se 3 (by rfl) ⟨502520, by rfl⟩ : syracuseStep 2680109 = 1005041) (by norm_num)
theorem B2262325 : Blo 1786094 2262325 := bbase (se 5 (by rfl) ⟨106046, by rfl⟩ : syracuseStep 2262325 = 212093) (by norm_num)
theorem B2680133 : Blo 1786094 2680133 := bbase (se 4 (by rfl) ⟨251262, by rfl⟩ : syracuseStep 2680133 = 502525) (by norm_num)
theorem B3016021 : Blo 1786094 3016021 := bbase (se 12 (by rfl) ⟨1104, by rfl⟩ : syracuseStep 3016021 = 2209) (by norm_num)
theorem B2680157 : Blo 1786094 2680157 := bbase (se 3 (by rfl) ⟨502529, by rfl⟩ : syracuseStep 2680157 = 1005059) (by norm_num)
theorem B2680181 : Blo 1786094 2680181 := bbase (se 5 (by rfl) ⟨125633, by rfl⟩ : syracuseStep 2680181 = 251267) (by norm_num)
theorem B1860989 : Blo 1786094 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B2680205 : Blo 1786094 2680205 := bbase (se 3 (by rfl) ⟨502538, by rfl⟩ : syracuseStep 2680205 = 1005077) (by norm_num)
theorem B7243157 : Blo 1786094 7243157 := bbase (se 6 (by rfl) ⟨169761, by rfl⟩ : syracuseStep 7243157 = 339523) (by norm_num)
theorem B2262421 : Blo 1786094 2262421 := bbase (se 6 (by rfl) ⟨53025, by rfl⟩ : syracuseStep 2262421 = 106051) (by norm_num)
theorem B2680229 : Blo 1786094 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B3392941 : Blo 1786094 3392941 := bbase (se 3 (by rfl) ⟨636176, by rfl⟩ : syracuseStep 3392941 = 1272353) (by norm_num)
theorem B3016109 : Blo 1786094 3016109 := bbase (se 3 (by rfl) ⟨565520, by rfl⟩ : syracuseStep 3016109 = 1131041) (by norm_num)
theorem B6030773 : Blo 1786094 6030773 := bbase (se 5 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 6030773 = 565385) (by norm_num)
theorem B2680253 : Blo 1786094 2680253 := bbase (se 3 (by rfl) ⟨502547, by rfl⟩ : syracuseStep 2680253 = 1005095) (by norm_num)
theorem B2680277 : Blo 1786094 2680277 := bbase (se 7 (by rfl) ⟨31409, by rfl⟩ : syracuseStep 2680277 = 62819) (by norm_num)
theorem B6784469 : Blo 1786094 6784469 := bbase (se 7 (by rfl) ⟨79505, by rfl⟩ : syracuseStep 6784469 = 159011) (by norm_num)
theorem B4523485 : Blo 1786094 4523485 := bbase (se 3 (by rfl) ⟨848153, by rfl⟩ : syracuseStep 4523485 = 1696307) (by norm_num)
theorem B2680301 : Blo 1786094 2680301 := bbase (se 3 (by rfl) ⟨502556, by rfl⟩ : syracuseStep 2680301 = 1005113) (by norm_num)
theorem B2680325 : Blo 1786094 2680325 := bbase (se 4 (by rfl) ⟨251280, by rfl⟩ : syracuseStep 2680325 = 502561) (by norm_num)
theorem B2680349 : Blo 1786094 2680349 := bbase (se 3 (by rfl) ⟨502565, by rfl⟩ : syracuseStep 2680349 = 1005131) (by norm_num)
theorem B3016237 : Blo 1786094 3016237 := bbase (se 3 (by rfl) ⟨565544, by rfl⟩ : syracuseStep 3016237 = 1131089) (by norm_num)
theorem B2680373 : Blo 1786094 2680373 := bbase (se 5 (by rfl) ⟨125642, by rfl⟩ : syracuseStep 2680373 = 251285) (by norm_num)
theorem B3393085 : Blo 1786094 3393085 := bbase (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) (by norm_num)
theorem B2262593 : Blo 1786094 2262593 := bbase (se 2 (by rfl) ⟨848472, by rfl⟩ : syracuseStep 2262593 = 1696945) (by norm_num)
theorem B2680397 : Blo 1786094 2680397 := bbase (se 3 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 2680397 = 1005149) (by norm_num)
theorem B4523597 : Blo 1786094 4523597 := bbase (se 3 (by rfl) ⟨848174, by rfl⟩ : syracuseStep 4523597 = 1696349) (by norm_num)
theorem B2680421 : Blo 1786094 2680421 := bbase (se 4 (by rfl) ⟨251289, by rfl⟩ : syracuseStep 2680421 = 502579) (by norm_num)
theorem B2262649 : Blo 1786094 2262649 := bbase (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) (by norm_num)
theorem B2680445 : Blo 1786094 2680445 := bbase (se 3 (by rfl) ⟨502583, by rfl⟩ : syracuseStep 2680445 = 1005167) (by norm_num)
theorem B8152709 : Blo 1786094 8152709 := bbase (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) (by norm_num)
theorem B3016325 : Blo 1786094 3016325 := bbase (se 4 (by rfl) ⟨282780, by rfl⟩ : syracuseStep 3016325 = 565561) (by norm_num)
theorem B2680469 : Blo 1786094 2680469 := bbase (se 6 (by rfl) ⟨62823, by rfl⟩ : syracuseStep 2680469 = 125647) (by norm_num)
theorem B6440597 : Blo 1786094 6440597 := bbase (se 6 (by rfl) ⟨150951, by rfl⟩ : syracuseStep 6440597 = 301903) (by norm_num)
theorem B6874789 : Blo 1786094 6874789 := bbase (se 4 (by rfl) ⟨644511, by rfl⟩ : syracuseStep 6874789 = 1289023) (by norm_num)
theorem B2680493 : Blo 1786094 2680493 := bbase (se 3 (by rfl) ⟨502592, by rfl⟩ : syracuseStep 2680493 = 1005185) (by norm_num)
theorem B2901677 : Blo 1786094 2901677 := bbase (se 3 (by rfl) ⟨544064, by rfl⟩ : syracuseStep 2901677 = 1088129) (by norm_num)
theorem B2680517 : Blo 1786094 2680517 := bbase (se 4 (by rfl) ⟨251298, by rfl⟩ : syracuseStep 2680517 = 502597) (by norm_num)
theorem B2262745 : Blo 1786094 2262745 := bbase (se 2 (by rfl) ⟨848529, by rfl⟩ : syracuseStep 2262745 = 1697059) (by norm_num)
theorem B2680541 : Blo 1786094 2680541 := bbase (se 3 (by rfl) ⟨502601, by rfl⟩ : syracuseStep 2680541 = 1005203) (by norm_num)
theorem B3393245 : Blo 1786094 3393245 := bbase (se 3 (by rfl) ⟨636233, by rfl⟩ : syracuseStep 3393245 = 1272467) (by norm_num)
theorem B3221221 : Blo 1786094 3221221 := bbase (se 4 (by rfl) ⟨301989, by rfl⟩ : syracuseStep 3221221 = 603979) (by norm_num)
theorem B2680565 : Blo 1786094 2680565 := bbase (se 5 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 2680565 = 251303) (by norm_num)
theorem B5089013 : Blo 1786094 5089013 := bbase (se 5 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 5089013 = 477095) (by norm_num)
theorem B3016453 : Blo 1786094 3016453 := bbase (se 4 (by rfl) ⟨282792, by rfl⟩ : syracuseStep 3016453 = 565585) (by norm_num)
theorem B2680589 : Blo 1786094 2680589 := bbase (se 3 (by rfl) ⟨502610, by rfl⟩ : syracuseStep 2680589 = 1005221) (by norm_num)
theorem B4523789 : Blo 1786094 4523789 := bbase (se 3 (by rfl) ⟨848210, by rfl⟩ : syracuseStep 4523789 = 1696421) (by norm_num)
theorem B3868445 : Blo 1786094 3868445 := bbase (se 3 (by rfl) ⟨725333, by rfl⟩ : syracuseStep 3868445 = 1450667) (by norm_num)
theorem B2680613 : Blo 1786094 2680613 := bbase (se 4 (by rfl) ⟨251307, by rfl⟩ : syracuseStep 2680613 = 502615) (by norm_num)
theorem B2680637 : Blo 1786094 2680637 := bbase (se 3 (by rfl) ⟨502619, by rfl⟩ : syracuseStep 2680637 = 1005239) (by norm_num)
theorem B4360013 : Blo 1786094 4360013 := bbase (se 3 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 4360013 = 1635005) (by norm_num)
theorem B2680661 : Blo 1786094 2680661 := bbase (se 9 (by rfl) ⟨7853, by rfl⟩ : syracuseStep 2680661 = 15707) (by norm_num)
theorem B3016541 : Blo 1786094 3016541 := bbase (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) (by norm_num)
theorem B6031205 : Blo 1786094 6031205 := bbase (se 4 (by rfl) ⟨565425, by rfl⟩ : syracuseStep 6031205 = 1130851) (by norm_num)
theorem B2680685 : Blo 1786094 2680685 := bbase (se 3 (by rfl) ⟨502628, by rfl⟩ : syracuseStep 2680685 = 1005257) (by norm_num)
theorem B3393389 : Blo 1786094 3393389 := bbase (se 3 (by rfl) ⟨636260, by rfl⟩ : syracuseStep 3393389 = 1272521) (by norm_num)
theorem B2680709 : Blo 1786094 2680709 := bbase (se 4 (by rfl) ⟨251316, by rfl⟩ : syracuseStep 2680709 = 502633) (by norm_num)
theorem B2262917 : Blo 1786094 2262917 := bbase (se 4 (by rfl) ⟨212148, by rfl⟩ : syracuseStep 2262917 = 424297) (by norm_num)
theorem B2680733 : Blo 1786094 2680733 := bbase (se 3 (by rfl) ⟨502637, by rfl⟩ : syracuseStep 2680733 = 1005275) (by norm_num)
theorem B2680757 : Blo 1786094 2680757 := bbase (se 5 (by rfl) ⟨125660, by rfl⟩ : syracuseStep 2680757 = 251321) (by norm_num)
theorem B2262973 : Blo 1786094 2262973 := bbase (se 3 (by rfl) ⟨424307, by rfl⟩ : syracuseStep 2262973 = 848615) (by norm_num)
theorem B2680781 : Blo 1786094 2680781 := bbase (se 3 (by rfl) ⟨502646, by rfl⟩ : syracuseStep 2680781 = 1005293) (by norm_num)
theorem B3016669 : Blo 1786094 3016669 := bbase (se 3 (by rfl) ⟨565625, by rfl⟩ : syracuseStep 3016669 = 1131251) (by norm_num)
theorem B2680805 : Blo 1786094 2680805 := bbase (se 4 (by rfl) ⟨251325, by rfl⟩ : syracuseStep 2680805 = 502651) (by norm_num)
theorem B4646909 : Blo 1786094 4646909 := bbase (se 3 (by rfl) ⟨871295, by rfl⟩ : syracuseStep 4646909 = 1742591) (by norm_num)
theorem B2680829 : Blo 1786094 2680829 := bbase (se 3 (by rfl) ⟨502655, by rfl⟩ : syracuseStep 2680829 = 1005311) (by norm_num)
theorem B2680853 : Blo 1786094 2680853 := bbase (se 6 (by rfl) ⟨62832, by rfl⟩ : syracuseStep 2680853 = 125665) (by norm_num)
theorem B2680877 : Blo 1786094 2680877 := bbase (se 3 (by rfl) ⟨502664, by rfl⟩ : syracuseStep 2680877 = 1005329) (by norm_num)
theorem B3016757 : Blo 1786094 3016757 := bbase (se 5 (by rfl) ⟨141410, by rfl⟩ : syracuseStep 3016757 = 282821) (by norm_num)
theorem B2680901 : Blo 1786094 2680901 := bbase (se 4 (by rfl) ⟨251334, by rfl⟩ : syracuseStep 2680901 = 502669) (by norm_num)
theorem B2680925 : Blo 1786094 2680925 := bbase (se 3 (by rfl) ⟨502673, by rfl⟩ : syracuseStep 2680925 = 1005347) (by norm_num)
theorem B4524133 : Blo 1786094 4524133 := bbase (se 4 (by rfl) ⟨424137, by rfl⟩ : syracuseStep 4524133 = 848275) (by norm_num)
theorem B2861173 : Blo 1786094 2861173 := bbase (se 5 (by rfl) ⟨134117, by rfl⟩ : syracuseStep 2861173 = 268235) (by norm_num)
theorem B2680949 : Blo 1786094 2680949 := bbase (se 5 (by rfl) ⟨125669, by rfl⟩ : syracuseStep 2680949 = 251339) (by norm_num)
theorem B7637125 : Blo 1786094 7637125 := bbase (se 4 (by rfl) ⟨715980, by rfl⟩ : syracuseStep 7637125 = 1431961) (by norm_num)
theorem B2680973 : Blo 1786094 2680973 := bbase (se 3 (by rfl) ⟨502682, by rfl⟩ : syracuseStep 2680973 = 1005365) (by norm_num)
theorem B3393677 : Blo 1786094 3393677 := bbase (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) (by norm_num)
theorem B30517397 : Blo 1786094 30517397 := bbase (se 6 (by rfl) ⟨715251, by rfl⟩ : syracuseStep 30517397 = 1430503) (by norm_num)
theorem B7637141 : Blo 1786094 7637141 := bbase (se 6 (by rfl) ⟨178995, by rfl⟩ : syracuseStep 7637141 = 357991) (by norm_num)
theorem B9291941 : Blo 1786094 9291941 := bbase (se 4 (by rfl) ⟨871119, by rfl⟩ : syracuseStep 9291941 = 1742239) (by norm_num)
theorem B2680997 : Blo 1786094 2680997 := bbase (se 4 (by rfl) ⟨251343, by rfl⟩ : syracuseStep 2680997 = 502687) (by norm_num)
theorem B3016885 : Blo 1786094 3016885 := bbase (se 5 (by rfl) ⟨141416, by rfl⟩ : syracuseStep 3016885 = 282833) (by norm_num)
theorem B2681021 : Blo 1786094 2681021 := bbase (se 3 (by rfl) ⟨502691, by rfl⟩ : syracuseStep 2681021 = 1005383) (by norm_num)
theorem B4524245 : Blo 1786094 4524245 := bbase (se 7 (by rfl) ⟨53018, by rfl⟩ : syracuseStep 4524245 = 106037) (by norm_num)
theorem B2681045 : Blo 1786094 2681045 := bbase (se 7 (by rfl) ⟨31418, by rfl⟩ : syracuseStep 2681045 = 62837) (by norm_num)
theorem B2681069 : Blo 1786094 2681069 := bbase (se 3 (by rfl) ⟨502700, by rfl⟩ : syracuseStep 2681069 = 1005401) (by norm_num)
theorem B2681093 : Blo 1786094 2681093 := bbase (se 4 (by rfl) ⟨251352, by rfl⟩ : syracuseStep 2681093 = 502705) (by norm_num)
theorem B3016973 : Blo 1786094 3016973 := bbase (se 3 (by rfl) ⟨565682, by rfl⟩ : syracuseStep 3016973 = 1131365) (by norm_num)
theorem B6031637 : Blo 1786094 6031637 := bbase (se 6 (by rfl) ⟨141366, by rfl⟩ : syracuseStep 6031637 = 282733) (by norm_num)
theorem B2681117 : Blo 1786094 2681117 := bbase (se 3 (by rfl) ⟨502709, by rfl⟩ : syracuseStep 2681117 = 1005419) (by norm_num)
theorem B3393829 : Blo 1786094 3393829 := bbase (se 4 (by rfl) ⟨318171, by rfl⟩ : syracuseStep 3393829 = 636343) (by norm_num)
theorem B2009389 : Blo 1786094 2009389 := bbase (se 3 (by rfl) ⟨376760, by rfl⟩ : syracuseStep 2009389 = 753521) (by norm_num)
theorem B2681141 : Blo 1786094 2681141 := bbase (se 5 (by rfl) ⟨125678, by rfl⟩ : syracuseStep 2681141 = 251357) (by norm_num)
theorem B2681165 : Blo 1786094 2681165 := bbase (se 3 (by rfl) ⟨502718, by rfl⟩ : syracuseStep 2681165 = 1005437) (by norm_num)
theorem B2009425 : Blo 1786094 2009425 := bbase (se 2 (by rfl) ⟨753534, by rfl⟩ : syracuseStep 2009425 = 1507069) (by norm_num)
theorem B2681189 : Blo 1786094 2681189 := bbase (se 4 (by rfl) ⟨251361, by rfl⟩ : syracuseStep 2681189 = 502723) (by norm_num)
theorem B2009461 : Blo 1786094 2009461 := bbase (se 5 (by rfl) ⟨94193, by rfl⟩ : syracuseStep 2009461 = 188387) (by norm_num)
theorem B2681213 : Blo 1786094 2681213 := bbase (se 3 (by rfl) ⟨502727, by rfl⟩ : syracuseStep 2681213 = 1005455) (by norm_num)
theorem B3017101 : Blo 1786094 3017101 := bbase (se 3 (by rfl) ⟨565706, by rfl⟩ : syracuseStep 3017101 = 1131413) (by norm_num)
theorem B4524437 : Blo 1786094 4524437 := bbase (se 6 (by rfl) ⟨106041, by rfl⟩ : syracuseStep 4524437 = 212083) (by norm_num)
theorem B2681237 : Blo 1786094 2681237 := bbase (se 6 (by rfl) ⟨62841, by rfl⟩ : syracuseStep 2681237 = 125683) (by norm_num)
theorem B2009497 : Blo 1786094 2009497 := bbase (se 2 (by rfl) ⟨753561, by rfl⟩ : syracuseStep 2009497 = 1507123) (by norm_num)
theorem B2681261 : Blo 1786094 2681261 := bbase (se 3 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 2681261 = 1005473) (by norm_num)
theorem B2009533 : Blo 1786094 2009533 := bbase (se 3 (by rfl) ⟨376787, by rfl⟩ : syracuseStep 2009533 = 753575) (by norm_num)
theorem B2681285 : Blo 1786094 2681285 := bbase (se 4 (by rfl) ⟨251370, by rfl⟩ : syracuseStep 2681285 = 502741) (by norm_num)
theorem B2681309 : Blo 1786094 2681309 := bbase (se 3 (by rfl) ⟨502745, by rfl⟩ : syracuseStep 2681309 = 1005491) (by norm_num)
theorem B2009569 : Blo 1786094 2009569 := bbase (se 2 (by rfl) ⟨753588, by rfl⟩ : syracuseStep 2009569 = 1507177) (by norm_num)
theorem B7244261 : Blo 1786094 7244261 := bbase (se 4 (by rfl) ⟨679149, by rfl⟩ : syracuseStep 7244261 = 1358299) (by norm_num)
theorem B3017189 : Blo 1786094 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B2681333 : Blo 1786094 2681333 := bbase (se 5 (by rfl) ⟨125687, by rfl⟩ : syracuseStep 2681333 = 251375) (by norm_num)
theorem B2009605 : Blo 1786094 2009605 := bbase (se 4 (by rfl) ⟨188400, by rfl⟩ : syracuseStep 2009605 = 376801) (by norm_num)
theorem B2681357 : Blo 1786094 2681357 := bbase (se 3 (by rfl) ⟨502754, by rfl⟩ : syracuseStep 2681357 = 1005509) (by norm_num)
theorem B9046565 : Blo 1786094 9046565 := bbase (se 4 (by rfl) ⟨848115, by rfl⟩ : syracuseStep 9046565 = 1696231) (by norm_num)
theorem B2681381 : Blo 1786094 2681381 := bbase (se 4 (by rfl) ⟨251379, by rfl⟩ : syracuseStep 2681381 = 502759) (by norm_num)
theorem B2009641 : Blo 1786094 2009641 := bbase (se 2 (by rfl) ⟨753615, by rfl⟩ : syracuseStep 2009641 = 1507231) (by norm_num)
theorem B2681405 : Blo 1786094 2681405 := bbase (se 3 (by rfl) ⟨502763, by rfl⟩ : syracuseStep 2681405 = 1005527) (by norm_num)
theorem B2009677 : Blo 1786094 2009677 := bbase (se 3 (by rfl) ⟨376814, by rfl⟩ : syracuseStep 2009677 = 753629) (by norm_num)
theorem B2681429 : Blo 1786094 2681429 := bbase (se 8 (by rfl) ⟨15711, by rfl⟩ : syracuseStep 2681429 = 31423) (by norm_num)
theorem B3394133 : Blo 1786094 3394133 := bbase (se 8 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 3394133 = 39775) (by norm_num)
theorem B3623525 : Blo 1786094 3623525 := bbase (se 4 (by rfl) ⟨339705, by rfl⟩ : syracuseStep 3623525 = 679411) (by norm_num)
theorem B3017317 : Blo 1786094 3017317 := bbase (se 4 (by rfl) ⟨282873, by rfl⟩ : syracuseStep 3017317 = 565747) (by norm_num)
theorem B2681453 : Blo 1786094 2681453 := bbase (se 3 (by rfl) ⟨502772, by rfl⟩ : syracuseStep 2681453 = 1005545) (by norm_num)
theorem B2009713 : Blo 1786094 2009713 := bbase (se 2 (by rfl) ⟨753642, by rfl⟩ : syracuseStep 2009713 = 1507285) (by norm_num)
theorem B6785653 : Blo 1786094 6785653 := bbase (se 5 (by rfl) ⟨318077, by rfl⟩ : syracuseStep 6785653 = 636155) (by norm_num)
theorem B2681477 : Blo 1786094 2681477 := bbase (se 4 (by rfl) ⟨251388, by rfl⟩ : syracuseStep 2681477 = 502777) (by norm_num)
theorem B2009749 : Blo 1786094 2009749 := bbase (se 6 (by rfl) ⟨47103, by rfl⟩ : syracuseStep 2009749 = 94207) (by norm_num)
theorem B2681501 : Blo 1786094 2681501 := bbase (se 3 (by rfl) ⟨502781, by rfl⟩ : syracuseStep 2681501 = 1005563) (by norm_num)
theorem B2681525 : Blo 1786094 2681525 := bbase (se 5 (by rfl) ⟨125696, by rfl⟩ : syracuseStep 2681525 = 251393) (by norm_num)
theorem B2009785 : Blo 1786094 2009785 := bbase (se 2 (by rfl) ⟨753669, by rfl⟩ : syracuseStep 2009785 = 1507339) (by norm_num)
theorem B3017405 : Blo 1786094 3017405 := bbase (se 3 (by rfl) ⟨565763, by rfl⟩ : syracuseStep 3017405 = 1131527) (by norm_num)
theorem B6032069 : Blo 1786094 6032069 := bbase (se 4 (by rfl) ⟨565506, by rfl⟩ : syracuseStep 6032069 = 1131013) (by norm_num)
theorem B2681549 : Blo 1786094 2681549 := bbase (se 3 (by rfl) ⟨502790, by rfl⟩ : syracuseStep 2681549 = 1005581) (by norm_num)
theorem B2009821 : Blo 1786094 2009821 := bbase (se 3 (by rfl) ⟨376841, by rfl⟩ : syracuseStep 2009821 = 753683) (by norm_num)
theorem B2681573 : Blo 1786094 2681573 := bbase (se 4 (by rfl) ⟨251397, by rfl⟩ : syracuseStep 2681573 = 502795) (by norm_num)
theorem B2755301 : Blo 1786094 2755301 := bbase (se 4 (by rfl) ⟨258309, by rfl⟩ : syracuseStep 2755301 = 516619) (by norm_num)
theorem B4524781 : Blo 1786094 4524781 := bbase (se 3 (by rfl) ⟨848396, by rfl⟩ : syracuseStep 4524781 = 1696793) (by norm_num)
theorem B6875893 : Blo 1786094 6875893 := bbase (se 5 (by rfl) ⟨322307, by rfl⟩ : syracuseStep 6875893 = 644615) (by norm_num)
theorem B2861821 : Blo 1786094 2861821 := bbase (se 3 (by rfl) ⟨536591, by rfl⟩ : syracuseStep 2861821 = 1073183) (by norm_num)
theorem B2681597 : Blo 1786094 2681597 := bbase (se 3 (by rfl) ⟨502799, by rfl⟩ : syracuseStep 2681597 = 1005599) (by norm_num)
theorem B2009857 : Blo 1786094 2009857 := bbase (se 2 (by rfl) ⟨753696, by rfl⟩ : syracuseStep 2009857 = 1507393) (by norm_num)
theorem B2681621 : Blo 1786094 2681621 := bbase (se 6 (by rfl) ⟨62850, by rfl⟩ : syracuseStep 2681621 = 125701) (by norm_num)
theorem B2009893 : Blo 1786094 2009893 := bbase (se 4 (by rfl) ⟨188427, by rfl⟩ : syracuseStep 2009893 = 376855) (by norm_num)
theorem B2681645 : Blo 1786094 2681645 := bbase (se 3 (by rfl) ⟨502808, by rfl⟩ : syracuseStep 2681645 = 1005617) (by norm_num)
theorem B2681669 : Blo 1786094 2681669 := bbase (se 4 (by rfl) ⟨251406, by rfl⟩ : syracuseStep 2681669 = 502813) (by norm_num)
theorem B2009929 : Blo 1786094 2009929 := bbase (se 2 (by rfl) ⟨753723, by rfl⟩ : syracuseStep 2009929 = 1507447) (by norm_num)
theorem B4524893 : Blo 1786094 4524893 := bbase (se 3 (by rfl) ⟨848417, by rfl⟩ : syracuseStep 4524893 = 1696835) (by norm_num)
theorem B2681693 : Blo 1786094 2681693 := bbase (se 3 (by rfl) ⟨502817, by rfl⟩ : syracuseStep 2681693 = 1005635) (by norm_num)
theorem B3058525 : Blo 1786094 3058525 := bbase (se 3 (by rfl) ⟨573473, by rfl⟩ : syracuseStep 3058525 = 1146947) (by norm_num)
theorem B2009965 : Blo 1786094 2009965 := bbase (se 3 (by rfl) ⟨376868, by rfl⟩ : syracuseStep 2009965 = 753737) (by norm_num)
theorem B2681717 : Blo 1786094 2681717 := bbase (se 5 (by rfl) ⟨125705, by rfl⟩ : syracuseStep 2681717 = 251411) (by norm_num)
theorem B2681741 : Blo 1786094 2681741 := bbase (se 3 (by rfl) ⟨502826, by rfl⟩ : syracuseStep 2681741 = 1005653) (by norm_num)
theorem B2010001 : Blo 1786094 2010001 := bbase (se 2 (by rfl) ⟨753750, by rfl⟩ : syracuseStep 2010001 = 1507501) (by norm_num)
theorem B6441877 : Blo 1786094 6441877 := bbase (se 6 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 6441877 = 301963) (by norm_num)
theorem B5090197 : Blo 1786094 5090197 := bbase (se 6 (by rfl) ⟨119301, by rfl⟩ : syracuseStep 5090197 = 238603) (by norm_num)
theorem B6785957 : Blo 1786094 6785957 := bbase (se 4 (by rfl) ⟨636183, by rfl⟩ : syracuseStep 6785957 = 1272367) (by norm_num)
theorem B2681765 : Blo 1786094 2681765 := bbase (se 4 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 2681765 = 502831) (by norm_num)
theorem B2010037 : Blo 1786094 2010037 := bbase (se 5 (by rfl) ⟨94220, by rfl⟩ : syracuseStep 2010037 = 188441) (by norm_num)
theorem B4295605 : Blo 1786094 4295605 := bbase (se 5 (by rfl) ⟨201356, by rfl⟩ : syracuseStep 4295605 = 402713) (by norm_num)
theorem B2681789 : Blo 1786094 2681789 := bbase (se 3 (by rfl) ⟨502835, by rfl⟩ : syracuseStep 2681789 = 1005671) (by norm_num)
theorem B2681813 : Blo 1786094 2681813 := bbase (se 7 (by rfl) ⟨31427, by rfl⟩ : syracuseStep 2681813 = 62855) (by norm_num)
theorem B2010073 : Blo 1786094 2010073 := bbase (se 2 (by rfl) ⟨753777, by rfl⟩ : syracuseStep 2010073 = 1507555) (by norm_num)
theorem B2681837 : Blo 1786094 2681837 := bbase (se 3 (by rfl) ⟨502844, by rfl⟩ : syracuseStep 2681837 = 1005689) (by norm_num)
theorem B2010109 : Blo 1786094 2010109 := bbase (se 3 (by rfl) ⟨376895, by rfl⟩ : syracuseStep 2010109 = 753791) (by norm_num)
theorem B2681861 : Blo 1786094 2681861 := bbase (se 4 (by rfl) ⟨251424, by rfl⟩ : syracuseStep 2681861 = 502849) (by norm_num)
theorem B4525085 : Blo 1786094 4525085 := bbase (se 3 (by rfl) ⟨848453, by rfl⟩ : syracuseStep 4525085 = 1696907) (by norm_num)
theorem B2681885 : Blo 1786094 2681885 := bbase (se 3 (by rfl) ⟨502853, by rfl⟩ : syracuseStep 2681885 = 1005707) (by norm_num)
theorem B2010145 : Blo 1786094 2010145 := bbase (se 2 (by rfl) ⟨753804, by rfl⟩ : syracuseStep 2010145 = 1507609) (by norm_num)
theorem B5090357 : Blo 1786094 5090357 := bbase (se 5 (by rfl) ⟨238610, by rfl⟩ : syracuseStep 5090357 = 477221) (by norm_num)
theorem B2681909 : Blo 1786094 2681909 := bbase (se 5 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 2681909 = 251429) (by norm_num)
theorem B2010181 : Blo 1786094 2010181 := bbase (se 4 (by rfl) ⟨188454, by rfl⟩ : syracuseStep 2010181 = 376909) (by norm_num)
theorem B2681933 : Blo 1786094 2681933 := bbase (se 3 (by rfl) ⟨502862, by rfl⟩ : syracuseStep 2681933 = 1005725) (by norm_num)
theorem B2681957 : Blo 1786094 2681957 := bbase (se 4 (by rfl) ⟨251433, by rfl⟩ : syracuseStep 2681957 = 502867) (by norm_num)
theorem B2010217 : Blo 1786094 2010217 := bbase (se 2 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 2010217 = 1507663) (by norm_num)
theorem B6032501 : Blo 1786094 6032501 := bbase (se 5 (by rfl) ⟨282773, by rfl⟩ : syracuseStep 6032501 = 565547) (by norm_num)
theorem B2681981 : Blo 1786094 2681981 := bbase (se 3 (by rfl) ⟨502871, by rfl⟩ : syracuseStep 2681981 = 1005743) (by norm_num)
theorem B2010253 : Blo 1786094 2010253 := bbase (se 3 (by rfl) ⟨376922, by rfl⟩ : syracuseStep 2010253 = 753845) (by norm_num)
theorem B2682005 : Blo 1786094 2682005 := bbase (se 6 (by rfl) ⟨62859, by rfl⟩ : syracuseStep 2682005 = 125719) (by norm_num)
theorem B2682029 : Blo 1786094 2682029 := bbase (se 3 (by rfl) ⟨502880, by rfl⟩ : syracuseStep 2682029 = 1005761) (by norm_num)
theorem B2010289 : Blo 1786094 2010289 := bbase (se 2 (by rfl) ⟨753858, by rfl⟩ : syracuseStep 2010289 = 1507717) (by norm_num)
theorem B2682053 : Blo 1786094 2682053 := bbase (se 4 (by rfl) ⟨251442, by rfl⟩ : syracuseStep 2682053 = 502885) (by norm_num)
theorem B4828373 : Blo 1786094 4828373 := bbase (se 7 (by rfl) ⟨56582, by rfl⟩ : syracuseStep 4828373 = 113165) (by norm_num)
theorem B2010325 : Blo 1786094 2010325 := bbase (se 7 (by rfl) ⟨23558, by rfl⟩ : syracuseStep 2010325 = 47117) (by norm_num)
theorem B2682077 : Blo 1786094 2682077 := bbase (se 3 (by rfl) ⟨502889, by rfl⟩ : syracuseStep 2682077 = 1005779) (by norm_num)
theorem B2682101 : Blo 1786094 2682101 := bbase (se 5 (by rfl) ⟨125723, by rfl⟩ : syracuseStep 2682101 = 251447) (by norm_num)
theorem B2010361 : Blo 1786094 2010361 := bbase (se 2 (by rfl) ⟨753885, by rfl⟩ : syracuseStep 2010361 = 1507771) (by norm_num)
theorem B2682125 : Blo 1786094 2682125 := bbase (se 3 (by rfl) ⟨502898, by rfl⟩ : syracuseStep 2682125 = 1005797) (by norm_num)
theorem B2010397 : Blo 1786094 2010397 := bbase (se 3 (by rfl) ⟨376949, by rfl⟩ : syracuseStep 2010397 = 753899) (by norm_num)
theorem B5090597 : Blo 1786094 5090597 := bbase (se 4 (by rfl) ⟨477243, by rfl⟩ : syracuseStep 5090597 = 954487) (by norm_num)
theorem B2010433 : Blo 1786094 2010433 := bbase (se 2 (by rfl) ⟨753912, by rfl⟩ : syracuseStep 2010433 = 1507825) (by norm_num)
theorem B2010469 : Blo 1786094 2010469 := bbase (se 4 (by rfl) ⟨188481, by rfl⟩ : syracuseStep 2010469 = 376963) (by norm_num)
theorem B4525429 : Blo 1786094 4525429 := bbase (se 5 (by rfl) ⟨212129, by rfl⟩ : syracuseStep 4525429 = 424259) (by norm_num)
theorem B2010505 : Blo 1786094 2010505 := bbase (se 2 (by rfl) ⟨753939, by rfl⟩ : syracuseStep 2010505 = 1507879) (by norm_num)
theorem B2010541 : Blo 1786094 2010541 := bbase (se 3 (by rfl) ⟨376976, by rfl⟩ : syracuseStep 2010541 = 753953) (by norm_num)
theorem B2010577 : Blo 1786094 2010577 := bbase (se 2 (by rfl) ⟨753966, by rfl⟩ : syracuseStep 2010577 = 1507933) (by norm_num)
theorem B5090789 : Blo 1786094 5090789 := bbase (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) (by norm_num)
theorem B4525541 : Blo 1786094 4525541 := bbase (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) (by norm_num)
theorem B2010613 : Blo 1786094 2010613 := bbase (se 5 (by rfl) ⟨94247, by rfl⟩ : syracuseStep 2010613 = 188495) (by norm_num)
theorem B15273461 : Blo 1786094 15273461 := bbase (se 5 (by rfl) ⟨715943, by rfl⟩ : syracuseStep 15273461 = 1431887) (by norm_num)
theorem B2010649 : Blo 1786094 2010649 := bbase (se 2 (by rfl) ⟨753993, by rfl⟩ : syracuseStep 2010649 = 1507987) (by norm_num)
theorem B6032933 : Blo 1786094 6032933 := bbase (se 4 (by rfl) ⟨565587, by rfl⟩ : syracuseStep 6032933 = 1131175) (by norm_num)
theorem B2010685 : Blo 1786094 2010685 := bbase (se 3 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 2010685 = 754007) (by norm_num)
theorem B2010721 : Blo 1786094 2010721 := bbase (se 2 (by rfl) ⟨754020, by rfl⟩ : syracuseStep 2010721 = 1508041) (by norm_num)
theorem B7245413 : Blo 1786094 7245413 := bbase (se 4 (by rfl) ⟨679257, by rfl⟩ : syracuseStep 7245413 = 1358515) (by norm_num)
theorem B2010757 : Blo 1786094 2010757 := bbase (se 4 (by rfl) ⟨188508, by rfl⟩ : syracuseStep 2010757 = 377017) (by norm_num)
theorem B2862749 : Blo 1786094 2862749 := bbase (se 3 (by rfl) ⟨536765, by rfl⟩ : syracuseStep 2862749 = 1073531) (by norm_num)
theorem B4525733 : Blo 1786094 4525733 := bbase (se 4 (by rfl) ⟨424287, by rfl⟩ : syracuseStep 4525733 = 848575) (by norm_num)
theorem B2010793 : Blo 1786094 2010793 := bbase (se 2 (by rfl) ⟨754047, by rfl⟩ : syracuseStep 2010793 = 1508095) (by norm_num)
theorem B17166005 : Blo 1786094 17166005 := bbase (se 5 (by rfl) ⟨804656, by rfl⟩ : syracuseStep 17166005 = 1609313) (by norm_num)
theorem B2010829 : Blo 1786094 2010829 := bbase (se 3 (by rfl) ⟨377030, by rfl⟩ : syracuseStep 2010829 = 754061) (by norm_num)
theorem B2010865 : Blo 1786094 2010865 := bbase (se 2 (by rfl) ⟨754074, by rfl⟩ : syracuseStep 2010865 = 1508149) (by norm_num)
theorem B7245557 : Blo 1786094 7245557 := bbase (se 5 (by rfl) ⟨339635, by rfl⟩ : syracuseStep 7245557 = 679271) (by norm_num)
theorem B2010901 : Blo 1786094 2010901 := bbase (se 6 (by rfl) ⟨47130, by rfl⟩ : syracuseStep 2010901 = 94261) (by norm_num)
theorem B3624725 : Blo 1786094 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B2543413 : Blo 1786094 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B9047861 : Blo 1786094 9047861 := bbase (se 5 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 9047861 = 848237) (by norm_num)
theorem B2010937 : Blo 1786094 2010937 := bbase (se 2 (by rfl) ⟨754101, by rfl⟩ : syracuseStep 2010937 = 1508203) (by norm_num)
theorem B2010973 : Blo 1786094 2010973 := bbase (se 3 (by rfl) ⟨377057, by rfl⟩ : syracuseStep 2010973 = 754115) (by norm_num)
theorem B2011009 : Blo 1786094 2011009 := bbase (se 2 (by rfl) ⟨754128, by rfl⟩ : syracuseStep 2011009 = 1508257) (by norm_num)
theorem B2011045 : Blo 1786094 2011045 := bbase (se 4 (by rfl) ⟨188535, by rfl⟩ : syracuseStep 2011045 = 377071) (by norm_num)
theorem B2011081 : Blo 1786094 2011081 := bbase (se 2 (by rfl) ⟨754155, by rfl⟩ : syracuseStep 2011081 = 1508311) (by norm_num)
theorem B6033365 : Blo 1786094 6033365 := bbase (se 7 (by rfl) ⟨70703, by rfl⟩ : syracuseStep 6033365 = 141407) (by norm_num)
theorem B6115301 : Blo 1786094 6115301 := bbase (se 4 (by rfl) ⟨573309, by rfl⟩ : syracuseStep 6115301 = 1146619) (by norm_num)
theorem B2011117 : Blo 1786094 2011117 := bbase (se 3 (by rfl) ⟨377084, by rfl⟩ : syracuseStep 2011117 = 754169) (by norm_num)
theorem B12881909 : Blo 1786094 12881909 := bbase (se 5 (by rfl) ⟨603839, by rfl⟩ : syracuseStep 12881909 = 1207679) (by norm_num)
theorem B4526077 : Blo 1786094 4526077 := bbase (se 3 (by rfl) ⟨848639, by rfl⟩ : syracuseStep 4526077 = 1697279) (by norm_num)
theorem B2011153 : Blo 1786094 2011153 := bbase (se 2 (by rfl) ⟨754182, by rfl⟩ : syracuseStep 2011153 = 1508365) (by norm_num)
theorem B2011189 : Blo 1786094 2011189 := bbase (se 5 (by rfl) ⟨94274, by rfl⟩ : syracuseStep 2011189 = 188549) (by norm_num)
theorem B2011225 : Blo 1786094 2011225 := bbase (se 2 (by rfl) ⟨754209, by rfl⟩ : syracuseStep 2011225 = 1508419) (by norm_num)
theorem B2863205 : Blo 1786094 2863205 := bbase (se 4 (by rfl) ⟨268425, by rfl⟩ : syracuseStep 2863205 = 536851) (by norm_num)
theorem B2011261 : Blo 1786094 2011261 := bbase (se 3 (by rfl) ⟨377111, by rfl⟩ : syracuseStep 2011261 = 754223) (by norm_num)
theorem B2011297 : Blo 1786094 2011297 := bbase (se 2 (by rfl) ⟨754236, by rfl⟩ : syracuseStep 2011297 = 1508473) (by norm_num)
theorem B9662645 : Blo 1786094 9662645 := bbase (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) (by norm_num)
theorem B2011333 : Blo 1786094 2011333 := bbase (se 4 (by rfl) ⟨188562, by rfl⟩ : syracuseStep 2011333 = 377125) (by norm_num)
theorem B2011369 : Blo 1786094 2011369 := bbase (se 2 (by rfl) ⟨754263, by rfl⟩ : syracuseStep 2011369 = 1508527) (by norm_num)
theorem B3870965 : Blo 1786094 3870965 := bbase (se 5 (by rfl) ⟨181451, by rfl⟩ : syracuseStep 3870965 = 362903) (by norm_num)
theorem B2011405 : Blo 1786094 2011405 := bbase (se 3 (by rfl) ⟨377138, by rfl⟩ : syracuseStep 2011405 = 754277) (by norm_num)
theorem B2011441 : Blo 1786094 2011441 := bbase (se 2 (by rfl) ⟨754290, by rfl⟩ : syracuseStep 2011441 = 1508581) (by norm_num)
theorem B2011477 : Blo 1786094 2011477 := bbase (se 10 (by rfl) ⟨2946, by rfl⟩ : syracuseStep 2011477 = 5893) (by norm_num)
theorem B2011513 : Blo 1786094 2011513 := bbase (se 2 (by rfl) ⟨754317, by rfl⟩ : syracuseStep 2011513 = 1508635) (by norm_num)
theorem B2544005 : Blo 1786094 2544005 := bbase (se 4 (by rfl) ⟨238500, by rfl⟩ : syracuseStep 2544005 = 477001) (by norm_num)
theorem B6033797 : Blo 1786094 6033797 := bbase (se 4 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 6033797 = 1131337) (by norm_num)
theorem B2011549 : Blo 1786094 2011549 := bbase (se 3 (by rfl) ⟨377165, by rfl⟩ : syracuseStep 2011549 = 754331) (by norm_num)
theorem B2011585 : Blo 1786094 2011585 := bbase (se 2 (by rfl) ⟨754344, by rfl⟩ : syracuseStep 2011585 = 1508689) (by norm_num)
theorem B5091781 : Blo 1786094 5091781 := bbase (se 4 (by rfl) ⟨477354, by rfl⟩ : syracuseStep 5091781 = 954709) (by norm_num)
theorem B2544085 : Blo 1786094 2544085 := bbase (se 7 (by rfl) ⟨29813, by rfl⟩ : syracuseStep 2544085 = 59627) (by norm_num)
theorem B7631333 : Blo 1786094 7631333 := bbase (se 4 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 7631333 = 1430875) (by norm_num)
theorem B4018733 : Blo 1786094 4018733 := bbase (se 3 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 4018733 = 1507025) (by norm_num)
theorem B2544205 : Blo 1786094 2544205 := bbase (se 3 (by rfl) ⟨477038, by rfl⟩ : syracuseStep 2544205 = 954077) (by norm_num)
theorem B3265117 : Blo 1786094 3265117 := bbase (se 3 (by rfl) ⟨612209, by rfl⟩ : syracuseStep 3265117 = 1224419) (by norm_num)
theorem B4018805 : Blo 1786094 4018805 := bbase (se 5 (by rfl) ⟨188381, by rfl⟩ : syracuseStep 4018805 = 376763) (by norm_num)
theorem B5722757 : Blo 1786094 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B2544301 : Blo 1786094 2544301 := bbase (se 3 (by rfl) ⟨477056, by rfl⟩ : syracuseStep 2544301 = 954113) (by norm_num)
theorem B4018877 : Blo 1786094 4018877 := bbase (se 3 (by rfl) ⟨753539, by rfl⟩ : syracuseStep 4018877 = 1507079) (by norm_num)
theorem B73355989 : Blo 1786094 73355989 := bbase (se 7 (by rfl) ⟨859640, by rfl⟩ : syracuseStep 73355989 = 1719281) (by norm_num)
theorem B4018949 : Blo 1786094 4018949 := bbase (se 4 (by rfl) ⟨376776, by rfl⟩ : syracuseStep 4018949 = 753553) (by norm_num)
theorem B3265309 : Blo 1786094 3265309 := bbase (se 3 (by rfl) ⟨612245, by rfl⟩ : syracuseStep 3265309 = 1224491) (by norm_num)
theorem B6034229 : Blo 1786094 6034229 := bbase (se 5 (by rfl) ⟨282854, by rfl⟩ : syracuseStep 6034229 = 565709) (by norm_num)
theorem B4019021 : Blo 1786094 4019021 := bbase (se 3 (by rfl) ⟨753566, by rfl⟩ : syracuseStep 4019021 = 1507133) (by norm_num)
theorem B4019093 : Blo 1786094 4019093 := bbase (se 6 (by rfl) ⟨94197, by rfl⟩ : syracuseStep 4019093 = 188395) (by norm_num)
theorem B4019165 : Blo 1786094 4019165 := bbase (se 3 (by rfl) ⟨753593, by rfl⟩ : syracuseStep 4019165 = 1507187) (by norm_num)
theorem B6788069 : Blo 1786094 6788069 := bbase (se 4 (by rfl) ⟨636381, by rfl⟩ : syracuseStep 6788069 = 1272763) (by norm_num)
theorem B2036773 : Blo 1786094 2036773 := bbase (se 4 (by rfl) ⟨190947, by rfl⟩ : syracuseStep 2036773 = 381895) (by norm_num)
theorem B4019237 : Blo 1786094 4019237 := bbase (se 4 (by rfl) ⟨376803, by rfl⟩ : syracuseStep 4019237 = 753607) (by norm_num)
theorem B9049157 : Blo 1786094 9049157 := bbase (se 4 (by rfl) ⟨848358, by rfl⟩ : syracuseStep 9049157 = 1696717) (by norm_num)
theorem B4019309 : Blo 1786094 4019309 := bbase (se 3 (by rfl) ⟨753620, by rfl⟩ : syracuseStep 4019309 = 1507241) (by norm_num)
theorem B2544797 : Blo 1786094 2544797 := bbase (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) (by norm_num)
theorem B4019381 : Blo 1786094 4019381 := bbase (se 5 (by rfl) ⟨188408, by rfl⟩ : syracuseStep 4019381 = 376817) (by norm_num)
theorem B6034661 : Blo 1786094 6034661 := bbase (se 4 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 6034661 = 1131499) (by norm_num)
theorem B4019453 : Blo 1786094 4019453 := bbase (se 3 (by rfl) ⟨753647, by rfl⟩ : syracuseStep 4019453 = 1507295) (by norm_num)
theorem B6788357 : Blo 1786094 6788357 := bbase (se 4 (by rfl) ⟨636408, by rfl⟩ : syracuseStep 6788357 = 1272817) (by norm_num)
theorem B3265813 : Blo 1786094 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B2176313 : Blo 1786094 2176313 := bbase (se 2 (by rfl) ⟨816117, by rfl⟩ : syracuseStep 2176313 = 1632235) (by norm_num)
theorem B4019525 : Blo 1786094 4019525 := bbase (se 4 (by rfl) ⟨376830, by rfl⟩ : syracuseStep 4019525 = 753661) (by norm_num)
theorem B4019597 : Blo 1786094 4019597 := bbase (se 3 (by rfl) ⟨753674, by rfl⟩ : syracuseStep 4019597 = 1507349) (by norm_num)
theorem B17184149 : Blo 1786094 17184149 := bbase (se 6 (by rfl) ⟨402753, by rfl⟩ : syracuseStep 17184149 = 805507) (by norm_num)
theorem B4019669 : Blo 1786094 4019669 := bbase (se 7 (by rfl) ⟨47105, by rfl⟩ : syracuseStep 4019669 = 94211) (by norm_num)
theorem B20346389 : Blo 1786094 20346389 := bbase (se 6 (by rfl) ⟨476868, by rfl⟩ : syracuseStep 20346389 = 953737) (by norm_num)
theorem B4019741 : Blo 1786094 4019741 := bbase (se 3 (by rfl) ⟨753701, by rfl⟩ : syracuseStep 4019741 = 1507403) (by norm_num)
theorem B119101013 : Blo 1786094 119101013 := bbase (se 8 (by rfl) ⟨697857, by rfl⟩ : syracuseStep 119101013 = 1395715) (by norm_num)
theorem B4019813 : Blo 1786094 4019813 := bbase (se 4 (by rfl) ⟨376857, by rfl⟩ : syracuseStep 4019813 = 753715) (by norm_num)
theorem B4019885 : Blo 1786094 4019885 := bbase (se 3 (by rfl) ⟨753728, by rfl⟩ : syracuseStep 4019885 = 1507457) (by norm_num)
theorem B2545349 : Blo 1786094 2545349 := bbase (se 4 (by rfl) ⟨238626, by rfl⟩ : syracuseStep 2545349 = 477253) (by norm_num)
theorem B19314389 : Blo 1786094 19314389 := bbase (se 7 (by rfl) ⟨226340, by rfl⟩ : syracuseStep 19314389 = 452681) (by norm_num)
theorem B4019957 : Blo 1786094 4019957 := bbase (se 5 (by rfl) ⟨188435, by rfl⟩ : syracuseStep 4019957 = 376871) (by norm_num)
theorem B2037521 : Blo 1786094 2037521 := bbase (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) (by norm_num)
theorem B2324257 : Blo 1786094 2324257 := bbase (se 2 (by rfl) ⟨871596, by rfl⟩ : syracuseStep 2324257 = 1743193) (by norm_num)
theorem B4020029 : Blo 1786094 4020029 := bbase (se 3 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 4020029 = 1507511) (by norm_num)
theorem B4020101 : Blo 1786094 4020101 := bbase (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) (by norm_num)
theorem B4585349 : Blo 1786094 4585349 := bbase (se 4 (by rfl) ⟨429876, by rfl⟩ : syracuseStep 4585349 = 859753) (by norm_num)
theorem B4020173 : Blo 1786094 4020173 := bbase (se 3 (by rfl) ⟨753782, by rfl⟩ : syracuseStep 4020173 = 1507565) (by norm_num)
theorem B4020245 : Blo 1786094 4020245 := bbase (se 6 (by rfl) ⟨94224, by rfl⟩ : syracuseStep 4020245 = 188449) (by norm_num)
theorem B3815461 : Blo 1786094 3815461 := bbase (se 4 (by rfl) ⟨357699, by rfl⟩ : syracuseStep 3815461 = 715399) (by norm_num)
theorem B2717741 : Blo 1786094 2717741 := bbase (se 3 (by rfl) ⟨509576, by rfl⟩ : syracuseStep 2717741 = 1019153) (by norm_num)
theorem B8149045 : Blo 1786094 8149045 := bbase (se 5 (by rfl) ⟨381986, by rfl⟩ : syracuseStep 8149045 = 763973) (by norm_num)
theorem B4020317 : Blo 1786094 4020317 := bbase (se 3 (by rfl) ⟨753809, by rfl⟩ : syracuseStep 4020317 = 1507619) (by norm_num)
theorem B3815581 : Blo 1786094 3815581 := bbase (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) (by norm_num)
theorem B4020389 : Blo 1786094 4020389 := bbase (se 4 (by rfl) ⟨376911, by rfl⟩ : syracuseStep 4020389 = 753823) (by norm_num)
theorem B7633109 : Blo 1786094 7633109 := bbase (se 7 (by rfl) ⟨89450, by rfl⟩ : syracuseStep 7633109 = 178901) (by norm_num)
theorem B13760725 : Blo 1786094 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B4020461 : Blo 1786094 4020461 := bbase (se 3 (by rfl) ⟨753836, by rfl⟩ : syracuseStep 4020461 = 1507673) (by norm_num)
theorem B4020533 : Blo 1786094 4020533 := bbase (se 5 (by rfl) ⟨188462, by rfl⟩ : syracuseStep 4020533 = 376925) (by norm_num)
theorem B9050453 : Blo 1786094 9050453 := bbase (se 10 (by rfl) ⟨13257, by rfl⟩ : syracuseStep 9050453 = 26515) (by norm_num)
theorem B2038105 : Blo 1786094 2038105 := bbase (se 2 (by rfl) ⟨764289, by rfl⟩ : syracuseStep 2038105 = 1528579) (by norm_num)
theorem B4020605 : Blo 1786094 4020605 := bbase (se 3 (by rfl) ⟨753863, by rfl⟩ : syracuseStep 4020605 = 1507727) (by norm_num)
theorem B2038141 : Blo 1786094 2038141 := bbase (se 3 (by rfl) ⟨382151, by rfl⟩ : syracuseStep 2038141 = 764303) (by norm_num)
theorem B3815837 : Blo 1786094 3815837 := bbase (se 3 (by rfl) ⟨715469, by rfl⟩ : syracuseStep 3815837 = 1430939) (by norm_num)
theorem B2685349 : Blo 1786094 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B4020677 : Blo 1786094 4020677 := bbase (se 4 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 4020677 = 753877) (by norm_num)
theorem B7633349 : Blo 1786094 7633349 := bbase (se 4 (by rfl) ⟨715626, by rfl⟩ : syracuseStep 7633349 = 1431253) (by norm_num)
theorem B2038225 : Blo 1786094 2038225 := bbase (se 2 (by rfl) ⟨764334, by rfl⟩ : syracuseStep 2038225 = 1528669) (by norm_num)
theorem B4020749 : Blo 1786094 4020749 := bbase (se 3 (by rfl) ⟨753890, by rfl⟩ : syracuseStep 4020749 = 1507781) (by norm_num)
theorem B4020821 : Blo 1786094 4020821 := bbase (se 8 (by rfl) ⟨23559, by rfl⟩ : syracuseStep 4020821 = 47119) (by norm_num)
theorem B2718301 : Blo 1786094 2718301 := bbase (se 3 (by rfl) ⟨509681, by rfl⟩ : syracuseStep 2718301 = 1019363) (by norm_num)
theorem B4020893 : Blo 1786094 4020893 := bbase (se 3 (by rfl) ⟨753917, by rfl⟩ : syracuseStep 4020893 = 1507835) (by norm_num)
theorem B1907389 : Blo 1786094 1907389 := bbase (se 3 (by rfl) ⟨357635, by rfl⟩ : syracuseStep 1907389 = 715271) (by norm_num)
theorem B4020965 : Blo 1786094 4020965 := bbase (se 4 (by rfl) ⟨376965, by rfl⟩ : syracuseStep 4020965 = 753931) (by norm_num)
theorem B9042677 : Blo 1786094 9042677 := bbase (se 5 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 9042677 = 847751) (by norm_num)
theorem B8583941 : Blo 1786094 8583941 := bbase (se 4 (by rfl) ⟨804744, by rfl⟩ : syracuseStep 8583941 = 1609489) (by norm_num)
theorem B4021037 : Blo 1786094 4021037 := bbase (se 3 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 4021037 = 1507889) (by norm_num)
theorem B6781765 : Blo 1786094 6781765 := bbase (se 4 (by rfl) ⟨635790, by rfl⟩ : syracuseStep 6781765 = 1271581) (by norm_num)
theorem B2292581 : Blo 1786094 2292581 := bbase (se 4 (by rfl) ⟨214929, by rfl⟩ : syracuseStep 2292581 = 429859) (by norm_num)
theorem B18840437 : Blo 1786094 18840437 := bbase (se 5 (by rfl) ⟨883145, by rfl⟩ : syracuseStep 18840437 = 1766291) (by norm_num)
theorem B4021109 : Blo 1786094 4021109 := bbase (se 5 (by rfl) ⟨188489, by rfl⟩ : syracuseStep 4021109 = 376979) (by norm_num)
theorem B11451253 : Blo 1786094 11451253 := bbase (se 5 (by rfl) ⟨536777, by rfl⟩ : syracuseStep 11451253 = 1073555) (by norm_num)
theorem B8592245 : Blo 1786094 8592245 := bbase (se 5 (by rfl) ⟨402761, by rfl⟩ : syracuseStep 8592245 = 805523) (by norm_num)
theorem B2718605 : Blo 1786094 2718605 := bbase (se 3 (by rfl) ⟨509738, by rfl⟩ : syracuseStep 2718605 = 1019477) (by norm_num)
theorem B6028181 : Blo 1786094 6028181 := bbase (se 6 (by rfl) ⟨141285, by rfl⟩ : syracuseStep 6028181 = 282571) (by norm_num)
theorem B1907641 : Blo 1786094 1907641 := bbase (se 2 (by rfl) ⟨715365, by rfl⟩ : syracuseStep 1907641 = 1430731) (by norm_num)
theorem B1907645 : Blo 1786094 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B4021181 : Blo 1786094 4021181 := bbase (se 3 (by rfl) ⟨753971, by rfl⟩ : syracuseStep 4021181 = 1507943) (by norm_num)
theorem B9796565 : Blo 1786094 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B4021253 : Blo 1786094 4021253 := bbase (se 4 (by rfl) ⟨376992, by rfl⟩ : syracuseStep 4021253 = 753985) (by norm_num)
theorem B4021325 : Blo 1786094 4021325 := bbase (se 3 (by rfl) ⟨753998, by rfl⟩ : syracuseStep 4021325 = 1507997) (by norm_num)
theorem B6782069 : Blo 1786094 6782069 := bbase (se 5 (by rfl) ⟨317909, by rfl⟩ : syracuseStep 6782069 = 635819) (by norm_num)
theorem B4021397 : Blo 1786094 4021397 := bbase (se 6 (by rfl) ⟨94251, by rfl⟩ : syracuseStep 4021397 = 188503) (by norm_num)
theorem B4832405 : Blo 1786094 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B4021469 : Blo 1786094 4021469 := bbase (se 3 (by rfl) ⟨754025, by rfl⟩ : syracuseStep 4021469 = 1508051) (by norm_num)
theorem B4521197 : Blo 1786094 4521197 := bbase (se 3 (by rfl) ⟨847724, by rfl⟩ : syracuseStep 4521197 = 1695449) (by norm_num)
theorem B3816725 : Blo 1786094 3816725 := bbase (se 6 (by rfl) ⟨89454, by rfl⟩ : syracuseStep 3816725 = 178909) (by norm_num)
theorem B4021541 : Blo 1786094 4021541 := bbase (se 4 (by rfl) ⟨377019, by rfl⟩ : syracuseStep 4021541 = 754039) (by norm_num)
theorem B6028613 : Blo 1786094 6028613 := bbase (se 4 (by rfl) ⟨565182, by rfl⟩ : syracuseStep 6028613 = 1130365) (by norm_num)
theorem B3439949 : Blo 1786094 3439949 := bbase (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) (by norm_num)
theorem B24452437 : Blo 1786094 24452437 := bbase (se 11 (by rfl) ⟨17909, by rfl⟩ : syracuseStep 24452437 = 35819) (by norm_num)
theorem B5725525 : Blo 1786094 5725525 := bbase (se 11 (by rfl) ⟨4193, by rfl⟩ : syracuseStep 5725525 = 8387) (by norm_num)
theorem B4021613 : Blo 1786094 4021613 := bbase (se 3 (by rfl) ⟨754052, by rfl⟩ : syracuseStep 4021613 = 1508105) (by norm_num)
theorem B13573493 : Blo 1786094 13573493 := bbase (se 5 (by rfl) ⟨636257, by rfl⟩ : syracuseStep 13573493 = 1272515) (by norm_num)
theorem B4021685 : Blo 1786094 4021685 := bbase (se 5 (by rfl) ⟨188516, by rfl⟩ : syracuseStep 4021685 = 377033) (by norm_num)
theorem B3014077 : Blo 1786094 3014077 := bbase (se 3 (by rfl) ⟨565139, by rfl⟩ : syracuseStep 3014077 = 1130279) (by norm_num)
theorem B1908209 : Blo 1786094 1908209 := bbase (se 2 (by rfl) ⟨715578, by rfl⟩ : syracuseStep 1908209 = 1431157) (by norm_num)
theorem B4021757 : Blo 1786094 4021757 := bbase (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) (by norm_num)
theorem B3816965 : Blo 1786094 3816965 := bbase (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) (by norm_num)
theorem B3014165 : Blo 1786094 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B3390997 : Blo 1786094 3390997 := bbase (se 6 (by rfl) ⟨79476, by rfl⟩ : syracuseStep 3390997 = 158953) (by norm_num)
theorem B5226053 : Blo 1786094 5226053 := bbase (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) (by norm_num)
theorem B4521541 : Blo 1786094 4521541 := bbase (se 4 (by rfl) ⟨423894, by rfl⟩ : syracuseStep 4521541 = 847789) (by norm_num)
theorem B4021829 : Blo 1786094 4021829 := bbase (se 4 (by rfl) ⟨377046, by rfl⟩ : syracuseStep 4021829 = 754093) (by norm_num)
theorem B9051749 : Blo 1786094 9051749 := bbase (se 4 (by rfl) ⟨848601, by rfl⟩ : syracuseStep 9051749 = 1697203) (by norm_num)
theorem B4021901 : Blo 1786094 4021901 := bbase (se 3 (by rfl) ⟨754106, by rfl⟩ : syracuseStep 4021901 = 1508213) (by norm_num)
theorem B3014293 : Blo 1786094 3014293 := bbase (se 6 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 3014293 = 141295) (by norm_num)
theorem B3391141 : Blo 1786094 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B2260649 : Blo 1786094 2260649 := bbase (se 2 (by rfl) ⟨847743, by rfl⟩ : syracuseStep 2260649 = 1695487) (by norm_num)
theorem B1908397 : Blo 1786094 1908397 := bbase (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) (by norm_num)
theorem B4521653 : Blo 1786094 4521653 := bbase (se 5 (by rfl) ⟨211952, by rfl⟩ : syracuseStep 4521653 = 423905) (by norm_num)
theorem B4021973 : Blo 1786094 4021973 := bbase (se 7 (by rfl) ⟨47132, by rfl⟩ : syracuseStep 4021973 = 94265) (by norm_num)
theorem B2260705 : Blo 1786094 2260705 := bbase (se 2 (by rfl) ⟨847764, by rfl⟩ : syracuseStep 2260705 = 1695529) (by norm_num)
theorem B3014381 : Blo 1786094 3014381 := bbase (se 3 (by rfl) ⟨565196, by rfl⟩ : syracuseStep 3014381 = 1130393) (by norm_num)
theorem B6029045 : Blo 1786094 6029045 := bbase (se 5 (by rfl) ⟨282611, by rfl⟩ : syracuseStep 6029045 = 565223) (by norm_num)
theorem B13565717 : Blo 1786094 13565717 := bbase (se 6 (by rfl) ⟨317946, by rfl⟩ : syracuseStep 13565717 = 635893) (by norm_num)
theorem B4022045 : Blo 1786094 4022045 := bbase (se 3 (by rfl) ⟨754133, by rfl⟩ : syracuseStep 4022045 = 1508267) (by norm_num)
theorem B2260801 : Blo 1786094 2260801 := bbase (se 2 (by rfl) ⟨847800, by rfl⟩ : syracuseStep 2260801 = 1695601) (by norm_num)
theorem B3391301 : Blo 1786094 3391301 := bbase (se 4 (by rfl) ⟨317934, by rfl⟩ : syracuseStep 3391301 = 635869) (by norm_num)
theorem B4022117 : Blo 1786094 4022117 := bbase (se 4 (by rfl) ⟨377073, by rfl⟩ : syracuseStep 4022117 = 754147) (by norm_num)
theorem B3014509 : Blo 1786094 3014509 := bbase (se 3 (by rfl) ⟨565220, by rfl⟩ : syracuseStep 3014509 = 1130441) (by norm_num)
theorem B4521845 : Blo 1786094 4521845 := bbase (se 5 (by rfl) ⟨211961, by rfl⟩ : syracuseStep 4521845 = 423923) (by norm_num)
theorem B4292509 : Blo 1786094 4292509 := bbase (se 3 (by rfl) ⟨804845, by rfl⟩ : syracuseStep 4292509 = 1609691) (by norm_num)
theorem B4022189 : Blo 1786094 4022189 := bbase (se 3 (by rfl) ⟨754160, by rfl⟩ : syracuseStep 4022189 = 1508321) (by norm_num)
theorem B10182581 : Blo 1786094 10182581 := bbase (se 5 (by rfl) ⟨477308, by rfl⟩ : syracuseStep 10182581 = 954617) (by norm_num)
theorem B3014597 : Blo 1786094 3014597 := bbase (se 4 (by rfl) ⟨282618, by rfl⟩ : syracuseStep 3014597 = 565237) (by norm_num)
theorem B3391445 : Blo 1786094 3391445 := bbase (se 7 (by rfl) ⟨39743, by rfl⟩ : syracuseStep 3391445 = 79487) (by norm_num)
theorem B2260973 : Blo 1786094 2260973 := bbase (se 3 (by rfl) ⟨423932, by rfl⟩ : syracuseStep 2260973 = 847865) (by norm_num)
theorem B4022261 : Blo 1786094 4022261 := bbase (se 5 (by rfl) ⟨188543, by rfl⟩ : syracuseStep 4022261 = 377087) (by norm_num)
theorem B3817469 : Blo 1786094 3817469 := bbase (se 3 (by rfl) ⟨715775, by rfl⟩ : syracuseStep 3817469 = 1431551) (by norm_num)
theorem B6029315 : Blo 1786094 6029315 := bstep (se 1 (by rfl) ⟨4521986, by rfl⟩ : syracuseStep 6029315 = 9043973) B9043973
theorem B6783011 : Blo 1786094 6783011 := bstep (se 1 (by rfl) ⟨5087258, by rfl⟩ : syracuseStep 6783011 = 10174517) B10174517
theorem B3440675 : Blo 1786094 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B5087281 : Blo 1786094 5087281 := bstep (se 2 (by rfl) ⟨1907730, by rfl⟩ : syracuseStep 5087281 = 3815461) B3815461
theorem B3014705 : Blo 1786094 3014705 := bstep (se 2 (by rfl) ⟨1130514, by rfl⟩ : syracuseStep 3014705 = 2261029) B2261029
theorem B1908803 : Blo 1786094 1908803 := bstep (se 1 (by rfl) ⟨1431602, by rfl⟩ : syracuseStep 1908803 = 2863205) B2863205
theorem B2580643 : Blo 1786094 2580643 := bstep (se 1 (by rfl) ⟨1935482, by rfl⟩ : syracuseStep 2580643 = 3870965) B3870965
theorem B3014833 : Blo 1786094 3014833 := bstep (se 2 (by rfl) ⟨1130562, by rfl⟩ : syracuseStep 3014833 = 2261125) B2261125
theorem B10182833 : Blo 1786094 10182833 := bstep (se 2 (by rfl) ⟨3818562, by rfl⟩ : syracuseStep 10182833 = 7637125) B7637125
theorem B5087441 : Blo 1786094 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B3014867 : Blo 1786094 3014867 := bstep (se 1 (by rfl) ⟨2261150, by rfl⟩ : syracuseStep 3014867 = 4522301) B4522301
theorem B4022513 : Blo 1786094 4022513 := bstep (se 2 (by rfl) ⟨1508442, by rfl⟩ : syracuseStep 4022513 = 3016885) B3016885
theorem B1786099 : Blo 1786094 1786099 := bstep (se 1 (by rfl) ⟨1339574, by rfl⟩ : syracuseStep 1786099 = 2679149) B2679149
theorem B1786115 : Blo 1786094 1786115 := bstep (se 1 (by rfl) ⟨1339586, by rfl⟩ : syracuseStep 1786115 = 2679173) B2679173
theorem B4022531 : Blo 1786094 4022531 := bstep (se 1 (by rfl) ⟨3016898, by rfl⟩ : syracuseStep 4022531 = 6033797) B6033797
theorem B6029585 : Blo 1786094 6029585 := bstep (se 2 (by rfl) ⟨2261094, by rfl⟩ : syracuseStep 6029585 = 4522189) B4522189
theorem B1786131 : Blo 1786094 1786131 := bstep (se 1 (by rfl) ⟨1339598, by rfl⟩ : syracuseStep 1786131 = 2679197) B2679197
theorem B1786147 : Blo 1786094 1786147 := bstep (se 1 (by rfl) ⟨1339610, by rfl⟩ : syracuseStep 1786147 = 2679221) B2679221
theorem B9175331 : Blo 1786094 9175331 := bstep (se 1 (by rfl) ⟨6881498, by rfl⟩ : syracuseStep 9175331 = 13762997) B13762997
theorem B1786163 : Blo 1786094 1786163 := bstep (se 1 (by rfl) ⟨1339622, by rfl⟩ : syracuseStep 1786163 = 2679245) B2679245
theorem B1786179 : Blo 1786094 1786179 := bstep (se 1 (by rfl) ⟨1339634, by rfl⟩ : syracuseStep 1786179 = 2679269) B2679269
theorem B5087555 : Blo 1786094 5087555 := bstep (se 1 (by rfl) ⟨3815666, by rfl⟩ : syracuseStep 5087555 = 7631333) B7631333
theorem B1786195 : Blo 1786094 1786195 := bstep (se 1 (by rfl) ⟨1339646, by rfl⟩ : syracuseStep 1786195 = 2679293) B2679293
theorem B3014995 : Blo 1786094 3014995 := bstep (se 1 (by rfl) ⟨2261246, by rfl⟩ : syracuseStep 3014995 = 4522493) B4522493
theorem B1786211 : Blo 1786094 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B4292963 : Blo 1786094 4292963 := bstep (se 1 (by rfl) ⟨3219722, by rfl⟩ : syracuseStep 4292963 = 6439445) B6439445
theorem B2679155 : Blo 1786094 2679155 := bstep (se 1 (by rfl) ⟨2009366, by rfl⟩ : syracuseStep 2679155 = 4018733) B4018733
theorem B1786227 : Blo 1786094 1786227 := bstep (se 1 (by rfl) ⟨1339670, by rfl⟩ : syracuseStep 1786227 = 2679341) B2679341
theorem B1786243 : Blo 1786094 1786243 := bstep (se 1 (by rfl) ⟨1339682, by rfl⟩ : syracuseStep 1786243 = 2679365) B2679365
theorem B2679185 : Blo 1786094 2679185 := bstep (se 2 (by rfl) ⟨1004694, by rfl⟩ : syracuseStep 2679185 = 2009389) B2009389
theorem B1786259 : Blo 1786094 1786259 := bstep (se 1 (by rfl) ⟨1339694, by rfl⟩ : syracuseStep 1786259 = 2679389) B2679389
theorem B2679203 : Blo 1786094 2679203 := bstep (se 1 (by rfl) ⟨2009402, by rfl⟩ : syracuseStep 2679203 = 4018805) B4018805
theorem B1786275 : Blo 1786094 1786275 := bstep (se 1 (by rfl) ⟨1339706, by rfl⟩ : syracuseStep 1786275 = 2679413) B2679413
theorem B1786291 : Blo 1786094 1786291 := bstep (se 1 (by rfl) ⟨1339718, by rfl⟩ : syracuseStep 1786291 = 2679437) B2679437
theorem B2679233 : Blo 1786094 2679233 := bstep (se 2 (by rfl) ⟨1004712, by rfl⟩ : syracuseStep 2679233 = 2009425) B2009425
theorem B1786307 : Blo 1786094 1786307 := bstep (se 1 (by rfl) ⟨1339730, by rfl⟩ : syracuseStep 1786307 = 2679461) B2679461
theorem B65233349 : Blo 1786094 65233349 := bstep (se 4 (by rfl) ⟨6115626, by rfl⟩ : syracuseStep 65233349 = 12231253) B12231253
theorem B2679251 : Blo 1786094 2679251 := bstep (se 1 (by rfl) ⟨2009438, by rfl⟩ : syracuseStep 2679251 = 4018877) B4018877
theorem B1786323 : Blo 1786094 1786323 := bstep (se 1 (by rfl) ⟨1339742, by rfl⟩ : syracuseStep 1786323 = 2679485) B2679485
theorem B2261459 : Blo 1786094 2261459 := bstep (se 1 (by rfl) ⟨1696094, by rfl⟩ : syracuseStep 2261459 = 3392189) B3392189
theorem B3015137 : Blo 1786094 3015137 := bstep (se 2 (by rfl) ⟨1130676, by rfl⟩ : syracuseStep 3015137 = 2261353) B2261353
theorem B1786339 : Blo 1786094 1786339 := bstep (se 1 (by rfl) ⟨1339754, by rfl⟩ : syracuseStep 1786339 = 2679509) B2679509
theorem B2679281 : Blo 1786094 2679281 := bstep (se 2 (by rfl) ⟨1004730, by rfl⟩ : syracuseStep 2679281 = 2009461) B2009461
theorem B1786355 : Blo 1786094 1786355 := bstep (se 1 (by rfl) ⟨1339766, by rfl⟩ : syracuseStep 1786355 = 2679533) B2679533
theorem B2679299 : Blo 1786094 2679299 := bstep (se 1 (by rfl) ⟨2009474, by rfl⟩ : syracuseStep 2679299 = 4018949) B4018949
theorem B1786371 : Blo 1786094 1786371 := bstep (se 1 (by rfl) ⟨1339778, by rfl⟩ : syracuseStep 1786371 = 2679557) B2679557
theorem B17170957 : Blo 1786094 17170957 := bstep (se 3 (by rfl) ⟨3219554, by rfl⟩ : syracuseStep 17170957 = 6439109) B6439109
theorem B4522513 : Blo 1786094 4522513 := bstep (se 2 (by rfl) ⟨1695942, by rfl⟩ : syracuseStep 4522513 = 3391885) B3391885
theorem B1786387 : Blo 1786094 1786387 := bstep (se 1 (by rfl) ⟨1339790, by rfl⟩ : syracuseStep 1786387 = 2679581) B2679581
theorem B4022801 : Blo 1786094 4022801 := bstep (se 2 (by rfl) ⟨1508550, by rfl⟩ : syracuseStep 4022801 = 3017101) B3017101
theorem B2679329 : Blo 1786094 2679329 := bstep (se 2 (by rfl) ⟨1004748, by rfl⟩ : syracuseStep 2679329 = 2009497) B2009497
theorem B1786403 : Blo 1786094 1786403 := bstep (se 1 (by rfl) ⟨1339802, by rfl⟩ : syracuseStep 1786403 = 2679605) B2679605
theorem B4022819 : Blo 1786094 4022819 := bstep (se 1 (by rfl) ⟨3017114, by rfl⟩ : syracuseStep 4022819 = 6034229) B6034229
theorem B3580465 : Blo 1786094 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B2679347 : Blo 1786094 2679347 := bstep (se 1 (by rfl) ⟨2009510, by rfl⟩ : syracuseStep 2679347 = 4019021) B4019021
theorem B1786419 : Blo 1786094 1786419 := bstep (se 1 (by rfl) ⟨1339814, by rfl⟩ : syracuseStep 1786419 = 2679629) B2679629
theorem B1786435 : Blo 1786094 1786435 := bstep (se 1 (by rfl) ⟨1339826, by rfl⟩ : syracuseStep 1786435 = 2679653) B2679653
theorem B2679377 : Blo 1786094 2679377 := bstep (se 2 (by rfl) ⟨1004766, by rfl⟩ : syracuseStep 2679377 = 2009533) B2009533
theorem B1786451 : Blo 1786094 1786451 := bstep (se 1 (by rfl) ⟨1339838, by rfl⟩ : syracuseStep 1786451 = 2679677) B2679677
theorem B3015265 : Blo 1786094 3015265 := bstep (se 2 (by rfl) ⟨1130724, by rfl⟩ : syracuseStep 3015265 = 2261449) B2261449
theorem B2679395 : Blo 1786094 2679395 := bstep (se 1 (by rfl) ⟨2009546, by rfl⟩ : syracuseStep 2679395 = 4019093) B4019093
theorem B1786467 : Blo 1786094 1786467 := bstep (se 1 (by rfl) ⟨1339850, by rfl⟩ : syracuseStep 1786467 = 2679701) B2679701
theorem B3392113 : Blo 1786094 3392113 := bstep (se 2 (by rfl) ⟨1272042, by rfl⟩ : syracuseStep 3392113 = 2544085) B2544085
theorem B1786483 : Blo 1786094 1786483 := bstep (se 1 (by rfl) ⟨1339862, by rfl⟩ : syracuseStep 1786483 = 2679725) B2679725
theorem B2679425 : Blo 1786094 2679425 := bstep (se 2 (by rfl) ⟨1004784, by rfl⟩ : syracuseStep 2679425 = 2009569) B2009569
theorem B1786499 : Blo 1786094 1786499 := bstep (se 1 (by rfl) ⟨1339874, by rfl⟩ : syracuseStep 1786499 = 2679749) B2679749
theorem B3015299 : Blo 1786094 3015299 := bstep (se 1 (by rfl) ⟨2261474, by rfl⟩ : syracuseStep 3015299 = 4522949) B4522949
theorem B9044621 : Blo 1786094 9044621 := bstep (se 3 (by rfl) ⟨1695866, by rfl⟩ : syracuseStep 9044621 = 3391733) B3391733
theorem B2679443 : Blo 1786094 2679443 := bstep (se 1 (by rfl) ⟨2009582, by rfl⟩ : syracuseStep 2679443 = 4019165) B4019165
theorem B1786515 : Blo 1786094 1786515 := bstep (se 1 (by rfl) ⟨1339886, by rfl⟩ : syracuseStep 1786515 = 2679773) B2679773
theorem B1786531 : Blo 1786094 1786531 := bstep (se 1 (by rfl) ⟨1339898, by rfl⟩ : syracuseStep 1786531 = 2679797) B2679797
theorem B2679473 : Blo 1786094 2679473 := bstep (se 2 (by rfl) ⟨1004802, by rfl⟩ : syracuseStep 2679473 = 2009605) B2009605
theorem B1786547 : Blo 1786094 1786547 := bstep (se 1 (by rfl) ⟨1339910, by rfl⟩ : syracuseStep 1786547 = 2679821) B2679821
theorem B2679491 : Blo 1786094 2679491 := bstep (se 1 (by rfl) ⟨2009618, by rfl⟩ : syracuseStep 2679491 = 4019237) B4019237
theorem B1786563 : Blo 1786094 1786563 := bstep (se 1 (by rfl) ⟨1339922, by rfl⟩ : syracuseStep 1786563 = 2679845) B2679845
theorem B1786579 : Blo 1786094 1786579 := bstep (se 1 (by rfl) ⟨1339934, by rfl⟩ : syracuseStep 1786579 = 2679869) B2679869
theorem B2679521 : Blo 1786094 2679521 := bstep (se 2 (by rfl) ⟨1004820, by rfl⟩ : syracuseStep 2679521 = 2009641) B2009641
theorem B1786595 : Blo 1786094 1786595 := bstep (se 1 (by rfl) ⟨1339946, by rfl⟩ : syracuseStep 1786595 = 2679893) B2679893
theorem B2679539 : Blo 1786094 2679539 := bstep (se 1 (by rfl) ⟨2009654, by rfl⟩ : syracuseStep 2679539 = 4019309) B4019309
theorem B1786611 : Blo 1786094 1786611 := bstep (se 1 (by rfl) ⟨1339958, by rfl⟩ : syracuseStep 1786611 = 2679917) B2679917
theorem B1786627 : Blo 1786094 1786627 := bstep (se 1 (by rfl) ⟨1339970, by rfl⟩ : syracuseStep 1786627 = 2679941) B2679941
theorem B3015427 : Blo 1786094 3015427 := bstep (se 1 (by rfl) ⟨2261570, by rfl⟩ : syracuseStep 3015427 = 4523141) B4523141
theorem B2679569 : Blo 1786094 2679569 := bstep (se 2 (by rfl) ⟨1004838, by rfl⟩ : syracuseStep 2679569 = 2009677) B2009677
theorem B3392273 : Blo 1786094 3392273 := bstep (se 2 (by rfl) ⟨1272102, by rfl⟩ : syracuseStep 3392273 = 2544205) B2544205
theorem B1786643 : Blo 1786094 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B66069269 : Blo 1786094 66069269 := bstep (se 6 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 66069269 = 3096997) B3096997
theorem B2679587 : Blo 1786094 2679587 := bstep (se 1 (by rfl) ⟨2009690, by rfl⟩ : syracuseStep 2679587 = 4019381) B4019381
theorem B1786659 : Blo 1786094 1786659 := bstep (se 1 (by rfl) ⟨1339994, by rfl⟩ : syracuseStep 1786659 = 2679989) B2679989
theorem B4522787 : Blo 1786094 4522787 := bstep (se 1 (by rfl) ⟨3392090, by rfl⟩ : syracuseStep 4522787 = 6784181) B6784181
theorem B6030125 : Blo 1786094 6030125 := bstep (se 3 (by rfl) ⟨1130648, by rfl⟩ : syracuseStep 6030125 = 2261297) B2261297
theorem B4023089 : Blo 1786094 4023089 := bstep (se 2 (by rfl) ⟨1508658, by rfl⟩ : syracuseStep 4023089 = 3017317) B3017317
theorem B1786675 : Blo 1786094 1786675 := bstep (se 1 (by rfl) ⟨1340006, by rfl⟩ : syracuseStep 1786675 = 2680013) B2680013
theorem B2679617 : Blo 1786094 2679617 := bstep (se 2 (by rfl) ⟨1004856, by rfl⟩ : syracuseStep 2679617 = 2009713) B2009713
theorem B1786691 : Blo 1786094 1786691 := bstep (se 1 (by rfl) ⟨1340018, by rfl⟩ : syracuseStep 1786691 = 2680037) B2680037
theorem B4023107 : Blo 1786094 4023107 := bstep (se 1 (by rfl) ⟨3017330, by rfl⟩ : syracuseStep 4023107 = 6034661) B6034661
theorem B2679635 : Blo 1786094 2679635 := bstep (se 1 (by rfl) ⟨2009726, by rfl⟩ : syracuseStep 2679635 = 4019453) B4019453
theorem B1786707 : Blo 1786094 1786707 := bstep (se 1 (by rfl) ⟨1340030, by rfl⟩ : syracuseStep 1786707 = 2680061) B2680061
theorem B6030179 : Blo 1786094 6030179 := bstep (se 1 (by rfl) ⟨4522634, by rfl⟩ : syracuseStep 6030179 = 9045269) B9045269
theorem B1786723 : Blo 1786094 1786723 := bstep (se 1 (by rfl) ⟨1340042, by rfl⟩ : syracuseStep 1786723 = 2680085) B2680085
theorem B2679665 : Blo 1786094 2679665 := bstep (se 2 (by rfl) ⟨1004874, by rfl⟩ : syracuseStep 2679665 = 2009749) B2009749
theorem B1786739 : Blo 1786094 1786739 := bstep (se 1 (by rfl) ⟨1340054, by rfl⟩ : syracuseStep 1786739 = 2680109) B2680109
theorem B2679683 : Blo 1786094 2679683 := bstep (se 1 (by rfl) ⟨2009762, by rfl⟩ : syracuseStep 2679683 = 4019525) B4019525
theorem B1786755 : Blo 1786094 1786755 := bstep (se 1 (by rfl) ⟨1340066, by rfl⟩ : syracuseStep 1786755 = 2680133) B2680133
theorem B14484365 : Blo 1786094 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B3015569 : Blo 1786094 3015569 := bstep (se 2 (by rfl) ⟨1130838, by rfl⟩ : syracuseStep 3015569 = 2261677) B2261677
theorem B1786771 : Blo 1786094 1786771 := bstep (se 1 (by rfl) ⟨1340078, by rfl⟩ : syracuseStep 1786771 = 2680157) B2680157
theorem B2679713 : Blo 1786094 2679713 := bstep (se 2 (by rfl) ⟨1004892, by rfl⟩ : syracuseStep 2679713 = 2009785) B2009785
theorem B1786787 : Blo 1786094 1786787 := bstep (se 1 (by rfl) ⟨1340090, by rfl⟩ : syracuseStep 1786787 = 2680181) B2680181
theorem B2679731 : Blo 1786094 2679731 := bstep (se 1 (by rfl) ⟨2009798, by rfl⟩ : syracuseStep 2679731 = 4019597) B4019597
theorem B1786803 : Blo 1786094 1786803 := bstep (se 1 (by rfl) ⟨1340102, by rfl⟩ : syracuseStep 1786803 = 2680205) B2680205
theorem B1786819 : Blo 1786094 1786819 := bstep (se 1 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 1786819 = 2680229) B2680229
theorem B2679761 : Blo 1786094 2679761 := bstep (se 2 (by rfl) ⟨1004910, by rfl⟩ : syracuseStep 2679761 = 2009821) B2009821
theorem B1786835 : Blo 1786094 1786835 := bstep (se 1 (by rfl) ⟨1340126, by rfl⟩ : syracuseStep 1786835 = 2680253) B2680253
theorem B2679779 : Blo 1786094 2679779 := bstep (se 1 (by rfl) ⟨2009834, by rfl⟩ : syracuseStep 2679779 = 4019669) B4019669
theorem B1786851 : Blo 1786094 1786851 := bstep (se 1 (by rfl) ⟨1340138, by rfl⟩ : syracuseStep 1786851 = 2680277) B2680277
theorem B4522979 : Blo 1786094 4522979 := bstep (se 1 (by rfl) ⟨3392234, by rfl⟩ : syracuseStep 4522979 = 6784469) B6784469
theorem B1786867 : Blo 1786094 1786867 := bstep (se 1 (by rfl) ⟨1340150, by rfl⟩ : syracuseStep 1786867 = 2680301) B2680301
theorem B2679809 : Blo 1786094 2679809 := bstep (se 2 (by rfl) ⟨1004928, by rfl⟩ : syracuseStep 2679809 = 2009857) B2009857
theorem B1786883 : Blo 1786094 1786883 := bstep (se 1 (by rfl) ⟨1340162, by rfl⟩ : syracuseStep 1786883 = 2680325) B2680325
theorem B6784013 : Blo 1786094 6784013 := bstep (se 3 (by rfl) ⟨1272002, by rfl⟩ : syracuseStep 6784013 = 2544005) B2544005
theorem B3015697 : Blo 1786094 3015697 := bstep (se 2 (by rfl) ⟨1130886, by rfl⟩ : syracuseStep 3015697 = 2261773) B2261773
theorem B2679827 : Blo 1786094 2679827 := bstep (se 1 (by rfl) ⟨2009870, by rfl⟩ : syracuseStep 2679827 = 4019741) B4019741
theorem B1786899 : Blo 1786094 1786899 := bstep (se 1 (by rfl) ⟨1340174, by rfl⟩ : syracuseStep 1786899 = 2680349) B2680349
theorem B1786915 : Blo 1786094 1786915 := bstep (se 1 (by rfl) ⟨1340186, by rfl⟩ : syracuseStep 1786915 = 2680373) B2680373
theorem B2679857 : Blo 1786094 2679857 := bstep (se 2 (by rfl) ⟨1004946, by rfl⟩ : syracuseStep 2679857 = 2009893) B2009893
theorem B1786931 : Blo 1786094 1786931 := bstep (se 1 (by rfl) ⟨1340198, by rfl⟩ : syracuseStep 1786931 = 2680397) B2680397
theorem B3015731 : Blo 1786094 3015731 := bstep (se 1 (by rfl) ⟨2261798, by rfl⟩ : syracuseStep 3015731 = 4523597) B4523597
theorem B2679875 : Blo 1786094 2679875 := bstep (se 1 (by rfl) ⟨2009906, by rfl⟩ : syracuseStep 2679875 = 4019813) B4019813
theorem B1786947 : Blo 1786094 1786947 := bstep (se 1 (by rfl) ⟨1340210, by rfl⟩ : syracuseStep 1786947 = 2680421) B2680421
theorem B1786963 : Blo 1786094 1786963 := bstep (se 1 (by rfl) ⟨1340222, by rfl⟩ : syracuseStep 1786963 = 2680445) B2680445
theorem B2679905 : Blo 1786094 2679905 := bstep (se 2 (by rfl) ⟨1004964, by rfl⟩ : syracuseStep 2679905 = 2009929) B2009929
theorem B1786979 : Blo 1786094 1786979 := bstep (se 1 (by rfl) ⟨1340234, by rfl⟩ : syracuseStep 1786979 = 2680469) B2680469
theorem B4293731 : Blo 1786094 4293731 := bstep (se 1 (by rfl) ⟨3220298, by rfl⟩ : syracuseStep 4293731 = 6440597) B6440597
theorem B6030449 : Blo 1786094 6030449 := bstep (se 2 (by rfl) ⟨2261418, by rfl⟩ : syracuseStep 6030449 = 4522837) B4522837
theorem B2679923 : Blo 1786094 2679923 := bstep (se 1 (by rfl) ⟨2009942, by rfl⟩ : syracuseStep 2679923 = 4019885) B4019885
theorem B1786995 : Blo 1786094 1786995 := bstep (se 1 (by rfl) ⟨1340246, by rfl⟩ : syracuseStep 1786995 = 2680493) B2680493
theorem B1787011 : Blo 1786094 1787011 := bstep (se 1 (by rfl) ⟨1340258, by rfl⟩ : syracuseStep 1787011 = 2680517) B2680517
theorem B2679953 : Blo 1786094 2679953 := bstep (se 2 (by rfl) ⟨1004982, by rfl⟩ : syracuseStep 2679953 = 2009965) B2009965
theorem B1787027 : Blo 1786094 1787027 := bstep (se 1 (by rfl) ⟨1340270, by rfl⟩ : syracuseStep 1787027 = 2680541) B2680541
theorem B2262163 : Blo 1786094 2262163 := bstep (se 1 (by rfl) ⟨1696622, by rfl⟩ : syracuseStep 2262163 = 3393245) B3393245
theorem B2679971 : Blo 1786094 2679971 := bstep (se 1 (by rfl) ⟨2009978, by rfl⟩ : syracuseStep 2679971 = 4019957) B4019957
theorem B1787043 : Blo 1786094 1787043 := bstep (se 1 (by rfl) ⟨1340282, by rfl⟩ : syracuseStep 1787043 = 2680565) B2680565
theorem B3392675 : Blo 1786094 3392675 := bstep (se 1 (by rfl) ⟨2544506, by rfl⟩ : syracuseStep 3392675 = 5089013) B5089013
theorem B1787059 : Blo 1786094 1787059 := bstep (se 1 (by rfl) ⟨1340294, by rfl⟩ : syracuseStep 1787059 = 2680589) B2680589
theorem B3015859 : Blo 1786094 3015859 := bstep (se 1 (by rfl) ⟨2261894, by rfl⟩ : syracuseStep 3015859 = 4523789) B4523789
theorem B2680001 : Blo 1786094 2680001 := bstep (se 2 (by rfl) ⟨1005000, by rfl⟩ : syracuseStep 2680001 = 2010001) B2010001
theorem B1787075 : Blo 1786094 1787075 := bstep (se 1 (by rfl) ⟨1340306, by rfl⟩ : syracuseStep 1787075 = 2680613) B2680613
theorem B2680019 : Blo 1786094 2680019 := bstep (se 1 (by rfl) ⟨2010014, by rfl⟩ : syracuseStep 2680019 = 4020029) B4020029
theorem B1787091 : Blo 1786094 1787091 := bstep (se 1 (by rfl) ⟨1340318, by rfl⟩ : syracuseStep 1787091 = 2680637) B2680637
theorem B1787107 : Blo 1786094 1787107 := bstep (se 1 (by rfl) ⟨1340330, by rfl⟩ : syracuseStep 1787107 = 2680661) B2680661
theorem B2680049 : Blo 1786094 2680049 := bstep (se 2 (by rfl) ⟨1005018, by rfl⟩ : syracuseStep 2680049 = 2010037) B2010037
theorem B5727473 : Blo 1786094 5727473 := bstep (se 2 (by rfl) ⟨2147802, by rfl⟩ : syracuseStep 5727473 = 4295605) B4295605
theorem B1787123 : Blo 1786094 1787123 := bstep (se 1 (by rfl) ⟨1340342, by rfl⟩ : syracuseStep 1787123 = 2680685) B2680685
theorem B2262259 : Blo 1786094 2262259 := bstep (se 1 (by rfl) ⟨1696694, by rfl⟩ : syracuseStep 2262259 = 3393389) B3393389
theorem B2680067 : Blo 1786094 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B3056899 : Blo 1786094 3056899 := bstep (se 1 (by rfl) ⟨2292674, by rfl⟩ : syracuseStep 3056899 = 4585349) B4585349
theorem B1787139 : Blo 1786094 1787139 := bstep (se 1 (by rfl) ⟨1340354, by rfl⟩ : syracuseStep 1787139 = 2680709) B2680709
theorem B13575437 : Blo 1786094 13575437 := bstep (se 3 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 13575437 = 5090789) B5090789
theorem B1787155 : Blo 1786094 1787155 := bstep (se 1 (by rfl) ⟨1340366, by rfl⟩ : syracuseStep 1787155 = 2680733) B2680733
theorem B2680097 : Blo 1786094 2680097 := bstep (se 2 (by rfl) ⟨1005036, by rfl⟩ : syracuseStep 2680097 = 2010073) B2010073
theorem B1787171 : Blo 1786094 1787171 := bstep (se 1 (by rfl) ⟨1340378, by rfl⟩ : syracuseStep 1787171 = 2680757) B2680757
theorem B5088557 : Blo 1786094 5088557 := bstep (se 3 (by rfl) ⟨954104, by rfl⟩ : syracuseStep 5088557 = 1908209) B1908209
theorem B2680115 : Blo 1786094 2680115 := bstep (se 1 (by rfl) ⟨2010086, by rfl⟩ : syracuseStep 2680115 = 4020173) B4020173
theorem B1787187 : Blo 1786094 1787187 := bstep (se 1 (by rfl) ⟨1340390, by rfl⟩ : syracuseStep 1787187 = 2680781) B2680781
theorem B3016001 : Blo 1786094 3016001 := bstep (se 2 (by rfl) ⟨1131000, by rfl⟩ : syracuseStep 3016001 = 2262001) B2262001
theorem B1787203 : Blo 1786094 1787203 := bstep (se 1 (by rfl) ⟨1340402, by rfl⟩ : syracuseStep 1787203 = 2680805) B2680805
theorem B2680145 : Blo 1786094 2680145 := bstep (se 2 (by rfl) ⟨1005054, by rfl⟩ : syracuseStep 2680145 = 2010109) B2010109
theorem B3097939 : Blo 1786094 3097939 := bstep (se 1 (by rfl) ⟨2323454, by rfl⟩ : syracuseStep 3097939 = 4646909) B4646909
theorem B1787219 : Blo 1786094 1787219 := bstep (se 1 (by rfl) ⟨1340414, by rfl⟩ : syracuseStep 1787219 = 2680829) B2680829
theorem B2680163 : Blo 1786094 2680163 := bstep (se 1 (by rfl) ⟨2010122, by rfl⟩ : syracuseStep 2680163 = 4020245) B4020245
theorem B1787235 : Blo 1786094 1787235 := bstep (se 1 (by rfl) ⟨1340426, by rfl⟩ : syracuseStep 1787235 = 2680853) B2680853
theorem B1787251 : Blo 1786094 1787251 := bstep (se 1 (by rfl) ⟨1340438, by rfl⟩ : syracuseStep 1787251 = 2680877) B2680877
theorem B1811827 : Blo 1786094 1811827 := bstep (se 1 (by rfl) ⟨1358870, by rfl⟩ : syracuseStep 1811827 = 2717741) B2717741
theorem B2680193 : Blo 1786094 2680193 := bstep (se 2 (by rfl) ⟨1005072, by rfl⟩ : syracuseStep 2680193 = 2010145) B2010145
theorem B1787267 : Blo 1786094 1787267 := bstep (se 1 (by rfl) ⟨1340450, by rfl⟩ : syracuseStep 1787267 = 2680901) B2680901
theorem B2680211 : Blo 1786094 2680211 := bstep (se 1 (by rfl) ⟨2010158, by rfl⟩ : syracuseStep 2680211 = 4020317) B4020317
theorem B1787283 : Blo 1786094 1787283 := bstep (se 1 (by rfl) ⟨1340462, by rfl⟩ : syracuseStep 1787283 = 2680925) B2680925
theorem B1787299 : Blo 1786094 1787299 := bstep (se 1 (by rfl) ⟨1340474, by rfl⟩ : syracuseStep 1787299 = 2680949) B2680949
theorem B2680241 : Blo 1786094 2680241 := bstep (se 2 (by rfl) ⟨1005090, by rfl⟩ : syracuseStep 2680241 = 2010181) B2010181
theorem B1787315 : Blo 1786094 1787315 := bstep (se 1 (by rfl) ⟨1340486, by rfl⟩ : syracuseStep 1787315 = 2680973) B2680973
theorem B3016129 : Blo 1786094 3016129 := bstep (se 2 (by rfl) ⟨1131048, by rfl⟩ : syracuseStep 3016129 = 2262097) B2262097
theorem B6194627 : Blo 1786094 6194627 := bstep (se 1 (by rfl) ⟨4645970, by rfl⟩ : syracuseStep 6194627 = 9291941) B9291941
theorem B2680259 : Blo 1786094 2680259 := bstep (se 1 (by rfl) ⟨2010194, by rfl⟩ : syracuseStep 2680259 = 4020389) B4020389
theorem B1787331 : Blo 1786094 1787331 := bstep (se 1 (by rfl) ⟨1340498, by rfl⟩ : syracuseStep 1787331 = 2680997) B2680997
theorem B1787347 : Blo 1786094 1787347 := bstep (se 1 (by rfl) ⟨1340510, by rfl⟩ : syracuseStep 1787347 = 2681021) B2681021
theorem B2680289 : Blo 1786094 2680289 := bstep (se 2 (by rfl) ⟨1005108, by rfl⟩ : syracuseStep 2680289 = 2010217) B2010217
theorem B5088739 : Blo 1786094 5088739 := bstep (se 1 (by rfl) ⟨3816554, by rfl⟩ : syracuseStep 5088739 = 7633109) B7633109
theorem B3016163 : Blo 1786094 3016163 := bstep (se 1 (by rfl) ⟨2262122, by rfl⟩ : syracuseStep 3016163 = 4524245) B4524245
theorem B1787363 : Blo 1786094 1787363 := bstep (se 1 (by rfl) ⟨1340522, by rfl⟩ : syracuseStep 1787363 = 2681045) B2681045
theorem B2680307 : Blo 1786094 2680307 := bstep (se 1 (by rfl) ⟨2010230, by rfl⟩ : syracuseStep 2680307 = 4020461) B4020461
theorem B1787379 : Blo 1786094 1787379 := bstep (se 1 (by rfl) ⟨1340534, by rfl⟩ : syracuseStep 1787379 = 2681069) B2681069
theorem B1787395 : Blo 1786094 1787395 := bstep (se 1 (by rfl) ⟨1340546, by rfl⟩ : syracuseStep 1787395 = 2681093) B2681093
theorem B12396037 : Blo 1786094 12396037 := bstep (se 4 (by rfl) ⟨1162128, by rfl⟩ : syracuseStep 12396037 = 2324257) B2324257
theorem B13936141 : Blo 1786094 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B2680337 : Blo 1786094 2680337 := bstep (se 2 (by rfl) ⟨1005126, by rfl⟩ : syracuseStep 2680337 = 2010253) B2010253
theorem B1787411 : Blo 1786094 1787411 := bstep (se 1 (by rfl) ⟨1340558, by rfl⟩ : syracuseStep 1787411 = 2681117) B2681117
theorem B2680355 : Blo 1786094 2680355 := bstep (se 1 (by rfl) ⟨2010266, by rfl⟩ : syracuseStep 2680355 = 4020533) B4020533
theorem B1787427 : Blo 1786094 1787427 := bstep (se 1 (by rfl) ⟨1340570, by rfl⟩ : syracuseStep 1787427 = 2681141) B2681141
theorem B1787443 : Blo 1786094 1787443 := bstep (se 1 (by rfl) ⟨1340582, by rfl⟩ : syracuseStep 1787443 = 2681165) B2681165
theorem B2680385 : Blo 1786094 2680385 := bstep (se 2 (by rfl) ⟨1005144, by rfl⟩ : syracuseStep 2680385 = 2010289) B2010289
theorem B1787459 : Blo 1786094 1787459 := bstep (se 1 (by rfl) ⟨1340594, by rfl⟩ : syracuseStep 1787459 = 2681189) B2681189
theorem B2680403 : Blo 1786094 2680403 := bstep (se 1 (by rfl) ⟨2010302, by rfl⟩ : syracuseStep 2680403 = 4020605) B4020605
theorem B1787475 : Blo 1786094 1787475 := bstep (se 1 (by rfl) ⟨1340606, by rfl⟩ : syracuseStep 1787475 = 2681213) B2681213
theorem B3016291 : Blo 1786094 3016291 := bstep (se 1 (by rfl) ⟨2262218, by rfl⟩ : syracuseStep 3016291 = 4524437) B4524437
theorem B1787491 : Blo 1786094 1787491 := bstep (se 1 (by rfl) ⟨1340618, by rfl⟩ : syracuseStep 1787491 = 2681237) B2681237
theorem B2680433 : Blo 1786094 2680433 := bstep (se 2 (by rfl) ⟨1005162, by rfl⟩ : syracuseStep 2680433 = 2010325) B2010325
theorem B1787507 : Blo 1786094 1787507 := bstep (se 1 (by rfl) ⟨1340630, by rfl⟩ : syracuseStep 1787507 = 2681261) B2681261
theorem B2680451 : Blo 1786094 2680451 := bstep (se 1 (by rfl) ⟨2010338, by rfl⟩ : syracuseStep 2680451 = 4020677) B4020677
theorem B5088899 : Blo 1786094 5088899 := bstep (se 1 (by rfl) ⟨3816674, by rfl⟩ : syracuseStep 5088899 = 7633349) B7633349
theorem B1787523 : Blo 1786094 1787523 := bstep (se 1 (by rfl) ⟨1340642, by rfl⟩ : syracuseStep 1787523 = 2681285) B2681285
theorem B6030989 : Blo 1786094 6030989 := bstep (se 3 (by rfl) ⟨1130810, by rfl⟩ : syracuseStep 6030989 = 2261621) B2261621
theorem B1787539 : Blo 1786094 1787539 := bstep (se 1 (by rfl) ⟨1340654, by rfl⟩ : syracuseStep 1787539 = 2681309) B2681309
theorem B2680481 : Blo 1786094 2680481 := bstep (se 2 (by rfl) ⟨1005180, by rfl⟩ : syracuseStep 2680481 = 2010361) B2010361
theorem B1787555 : Blo 1786094 1787555 := bstep (se 1 (by rfl) ⟨1340666, by rfl⟩ : syracuseStep 1787555 = 2681333) B2681333
theorem B2680499 : Blo 1786094 2680499 := bstep (se 1 (by rfl) ⟨2010374, by rfl⟩ : syracuseStep 2680499 = 4020749) B4020749
theorem B1787571 : Blo 1786094 1787571 := bstep (se 1 (by rfl) ⟨1340678, by rfl⟩ : syracuseStep 1787571 = 2681357) B2681357
theorem B6031043 : Blo 1786094 6031043 := bstep (se 1 (by rfl) ⟨4523282, by rfl⟩ : syracuseStep 6031043 = 9046565) B9046565
theorem B1787587 : Blo 1786094 1787587 := bstep (se 1 (by rfl) ⟨1340690, by rfl⟩ : syracuseStep 1787587 = 2681381) B2681381
theorem B2680529 : Blo 1786094 2680529 := bstep (se 2 (by rfl) ⟨1005198, by rfl⟩ : syracuseStep 2680529 = 2010397) B2010397
theorem B1787603 : Blo 1786094 1787603 := bstep (se 1 (by rfl) ⟨1340702, by rfl⟩ : syracuseStep 1787603 = 2681405) B2681405
theorem B2680547 : Blo 1786094 2680547 := bstep (se 1 (by rfl) ⟨2010410, by rfl⟩ : syracuseStep 2680547 = 4020821) B4020821
theorem B1787619 : Blo 1786094 1787619 := bstep (se 1 (by rfl) ⟨1340714, by rfl⟩ : syracuseStep 1787619 = 2681429) B2681429
theorem B2262755 : Blo 1786094 2262755 := bstep (se 1 (by rfl) ⟨1697066, by rfl⟩ : syracuseStep 2262755 = 3394133) B3394133
theorem B3016433 : Blo 1786094 3016433 := bstep (se 2 (by rfl) ⟨1131162, by rfl⟩ : syracuseStep 3016433 = 2262325) B2262325
theorem B1787635 : Blo 1786094 1787635 := bstep (se 1 (by rfl) ⟨1340726, by rfl⟩ : syracuseStep 1787635 = 2681453) B2681453
theorem B2680577 : Blo 1786094 2680577 := bstep (se 2 (by rfl) ⟨1005216, by rfl⟩ : syracuseStep 2680577 = 2010433) B2010433
theorem B1787651 : Blo 1786094 1787651 := bstep (se 1 (by rfl) ⟨1340738, by rfl⟩ : syracuseStep 1787651 = 2681477) B2681477
theorem B2680595 : Blo 1786094 2680595 := bstep (se 1 (by rfl) ⟨2010446, by rfl⟩ : syracuseStep 2680595 = 4020893) B4020893
theorem B1787667 : Blo 1786094 1787667 := bstep (se 1 (by rfl) ⟨1340750, by rfl⟩ : syracuseStep 1787667 = 2681501) B2681501
theorem B1787683 : Blo 1786094 1787683 := bstep (se 1 (by rfl) ⟨1340762, by rfl⟩ : syracuseStep 1787683 = 2681525) B2681525
theorem B2680625 : Blo 1786094 2680625 := bstep (se 2 (by rfl) ⟨1005234, by rfl⟩ : syracuseStep 2680625 = 2010469) B2010469
theorem B1787699 : Blo 1786094 1787699 := bstep (se 1 (by rfl) ⟨1340774, by rfl⟩ : syracuseStep 1787699 = 2681549) B2681549
theorem B2680643 : Blo 1786094 2680643 := bstep (se 1 (by rfl) ⟨2010482, by rfl⟩ : syracuseStep 2680643 = 4020965) B4020965
theorem B1787715 : Blo 1786094 1787715 := bstep (se 1 (by rfl) ⟨1340786, by rfl⟩ : syracuseStep 1787715 = 2681573) B2681573
theorem B16312133 : Blo 1786094 16312133 := bstep (se 4 (by rfl) ⟨1529262, by rfl⟩ : syracuseStep 16312133 = 3058525) B3058525
theorem B1787731 : Blo 1786094 1787731 := bstep (se 1 (by rfl) ⟨1340798, by rfl⟩ : syracuseStep 1787731 = 2681597) B2681597
theorem B2680673 : Blo 1786094 2680673 := bstep (se 2 (by rfl) ⟨1005252, by rfl⟩ : syracuseStep 2680673 = 2010505) B2010505
theorem B1787747 : Blo 1786094 1787747 := bstep (se 1 (by rfl) ⟨1340810, by rfl⟩ : syracuseStep 1787747 = 2681621) B2681621
theorem B3016561 : Blo 1786094 3016561 := bstep (se 2 (by rfl) ⟨1131210, by rfl⟩ : syracuseStep 3016561 = 2262421) B2262421
theorem B2680691 : Blo 1786094 2680691 := bstep (se 1 (by rfl) ⟨2010518, by rfl⟩ : syracuseStep 2680691 = 4021037) B4021037
theorem B1787763 : Blo 1786094 1787763 := bstep (se 1 (by rfl) ⟨1340822, by rfl⟩ : syracuseStep 1787763 = 2681645) B2681645
theorem B1787779 : Blo 1786094 1787779 := bstep (se 1 (by rfl) ⟨1340834, by rfl⟩ : syracuseStep 1787779 = 2681669) B2681669
theorem B2680721 : Blo 1786094 2680721 := bstep (se 2 (by rfl) ⟨1005270, by rfl⟩ : syracuseStep 2680721 = 2010541) B2010541
theorem B4523921 : Blo 1786094 4523921 := bstep (se 2 (by rfl) ⟨1696470, by rfl⟩ : syracuseStep 4523921 = 3392941) B3392941
theorem B3016595 : Blo 1786094 3016595 := bstep (se 1 (by rfl) ⟨2262446, by rfl⟩ : syracuseStep 3016595 = 4524893) B4524893
theorem B1787795 : Blo 1786094 1787795 := bstep (se 1 (by rfl) ⟨1340846, by rfl⟩ : syracuseStep 1787795 = 2681693) B2681693
theorem B12560291 : Blo 1786094 12560291 := bstep (se 1 (by rfl) ⟨9420218, by rfl⟩ : syracuseStep 12560291 = 18840437) B18840437
theorem B2680739 : Blo 1786094 2680739 := bstep (se 1 (by rfl) ⟨2010554, by rfl⟩ : syracuseStep 2680739 = 4021109) B4021109
theorem B1787811 : Blo 1786094 1787811 := bstep (se 1 (by rfl) ⟨1340858, by rfl⟩ : syracuseStep 1787811 = 2681717) B2681717
theorem B5728163 : Blo 1786094 5728163 := bstep (se 1 (by rfl) ⟨4296122, by rfl⟩ : syracuseStep 5728163 = 8592245) B8592245
theorem B1787827 : Blo 1786094 1787827 := bstep (se 1 (by rfl) ⟨1340870, by rfl⟩ : syracuseStep 1787827 = 2681741) B2681741
theorem B1812403 : Blo 1786094 1812403 := bstep (se 1 (by rfl) ⟨1359302, by rfl⟩ : syracuseStep 1812403 = 2718605) B2718605
theorem B2680769 : Blo 1786094 2680769 := bstep (se 2 (by rfl) ⟨1005288, by rfl⟩ : syracuseStep 2680769 = 2010577) B2010577
theorem B4523971 : Blo 1786094 4523971 := bstep (se 1 (by rfl) ⟨3392978, by rfl⟩ : syracuseStep 4523971 = 6785957) B6785957
theorem B1787843 : Blo 1786094 1787843 := bstep (se 1 (by rfl) ⟨1340882, by rfl⟩ : syracuseStep 1787843 = 2681765) B2681765
theorem B6031313 : Blo 1786094 6031313 := bstep (se 2 (by rfl) ⟨2261742, by rfl⟩ : syracuseStep 6031313 = 4523485) B4523485
theorem B2680787 : Blo 1786094 2680787 := bstep (se 1 (by rfl) ⟨2010590, by rfl⟩ : syracuseStep 2680787 = 4021181) B4021181
theorem B1787859 : Blo 1786094 1787859 := bstep (se 1 (by rfl) ⟨1340894, by rfl⟩ : syracuseStep 1787859 = 2681789) B2681789
theorem B6531043 : Blo 1786094 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B1787875 : Blo 1786094 1787875 := bstep (se 1 (by rfl) ⟨1340906, by rfl⟩ : syracuseStep 1787875 = 2681813) B2681813
theorem B2680817 : Blo 1786094 2680817 := bstep (se 2 (by rfl) ⟨1005306, by rfl⟩ : syracuseStep 2680817 = 2010613) B2010613
theorem B1787891 : Blo 1786094 1787891 := bstep (se 1 (by rfl) ⟨1340918, by rfl⟩ : syracuseStep 1787891 = 2681837) B2681837
theorem B2680835 : Blo 1786094 2680835 := bstep (se 1 (by rfl) ⟨2010626, by rfl⟩ : syracuseStep 2680835 = 4021253) B4021253
theorem B1787907 : Blo 1786094 1787907 := bstep (se 1 (by rfl) ⟨1340930, by rfl⟩ : syracuseStep 1787907 = 2681861) B2681861
theorem B22890509 : Blo 1786094 22890509 := bstep (se 3 (by rfl) ⟨4291970, by rfl⟩ : syracuseStep 22890509 = 8583941) B8583941
theorem B3016723 : Blo 1786094 3016723 := bstep (se 1 (by rfl) ⟨2262542, by rfl⟩ : syracuseStep 3016723 = 4525085) B4525085
theorem B1787923 : Blo 1786094 1787923 := bstep (se 1 (by rfl) ⟨1340942, by rfl⟩ : syracuseStep 1787923 = 2681885) B2681885
theorem B2680865 : Blo 1786094 2680865 := bstep (se 2 (by rfl) ⟨1005324, by rfl⟩ : syracuseStep 2680865 = 2010649) B2010649
theorem B3393571 : Blo 1786094 3393571 := bstep (se 1 (by rfl) ⟨2545178, by rfl⟩ : syracuseStep 3393571 = 5090357) B5090357
theorem B1787939 : Blo 1786094 1787939 := bstep (se 1 (by rfl) ⟨1340954, by rfl⟩ : syracuseStep 1787939 = 2681909) B2681909
theorem B5433389 : Blo 1786094 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B2680883 : Blo 1786094 2680883 := bstep (se 1 (by rfl) ⟨2010662, by rfl⟩ : syracuseStep 2680883 = 4021325) B4021325
theorem B1787955 : Blo 1786094 1787955 := bstep (se 1 (by rfl) ⟨1340966, by rfl⟩ : syracuseStep 1787955 = 2681933) B2681933
theorem B1787971 : Blo 1786094 1787971 := bstep (se 1 (by rfl) ⟨1340978, by rfl⟩ : syracuseStep 1787971 = 2681957) B2681957
theorem B2680913 : Blo 1786094 2680913 := bstep (se 2 (by rfl) ⟨1005342, by rfl⟩ : syracuseStep 2680913 = 2010685) B2010685
theorem B4524113 : Blo 1786094 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B1787987 : Blo 1786094 1787987 := bstep (se 1 (by rfl) ⟨1340990, by rfl⟩ : syracuseStep 1787987 = 2681981) B2681981
theorem B2680931 : Blo 1786094 2680931 := bstep (se 1 (by rfl) ⟨2010698, by rfl⟩ : syracuseStep 2680931 = 4021397) B4021397
theorem B3221603 : Blo 1786094 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B1788003 : Blo 1786094 1788003 := bstep (se 1 (by rfl) ⟨1341002, by rfl⟩ : syracuseStep 1788003 = 2682005) B2682005
theorem B1788019 : Blo 1786094 1788019 := bstep (se 1 (by rfl) ⟨1341014, by rfl⟩ : syracuseStep 1788019 = 2682029) B2682029
theorem B2680961 : Blo 1786094 2680961 := bstep (se 2 (by rfl) ⟨1005360, by rfl⟩ : syracuseStep 2680961 = 2010721) B2010721
theorem B1788035 : Blo 1786094 1788035 := bstep (se 1 (by rfl) ⟨1341026, by rfl⟩ : syracuseStep 1788035 = 2682053) B2682053
theorem B2680979 : Blo 1786094 2680979 := bstep (se 1 (by rfl) ⟨2010734, by rfl⟩ : syracuseStep 2680979 = 4021469) B4021469
theorem B1788051 : Blo 1786094 1788051 := bstep (se 1 (by rfl) ⟨1341038, by rfl⟩ : syracuseStep 1788051 = 2682077) B2682077
theorem B3016865 : Blo 1786094 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B1788067 : Blo 1786094 1788067 := bstep (se 1 (by rfl) ⟨1341050, by rfl⟩ : syracuseStep 1788067 = 2682101) B2682101
theorem B2681009 : Blo 1786094 2681009 := bstep (se 2 (by rfl) ⟨1005378, by rfl⟩ : syracuseStep 2681009 = 2010757) B2010757
theorem B1788083 : Blo 1786094 1788083 := bstep (se 1 (by rfl) ⟨1341062, by rfl⟩ : syracuseStep 1788083 = 2682125) B2682125
theorem B2681027 : Blo 1786094 2681027 := bstep (se 1 (by rfl) ⟨2010770, by rfl⟩ : syracuseStep 2681027 = 4021541) B4021541
theorem B3393731 : Blo 1786094 3393731 := bstep (se 1 (by rfl) ⟨2545298, by rfl⟩ : syracuseStep 3393731 = 5090597) B5090597
theorem B2681057 : Blo 1786094 2681057 := bstep (se 2 (by rfl) ⟨1005396, by rfl⟩ : syracuseStep 2681057 = 2010793) B2010793
theorem B2681075 : Blo 1786094 2681075 := bstep (se 1 (by rfl) ⟨2010806, by rfl⟩ : syracuseStep 2681075 = 4021613) B4021613
theorem B6113549 : Blo 1786094 6113549 := bstep (se 3 (by rfl) ⟨1146290, by rfl⟩ : syracuseStep 6113549 = 2292581) B2292581
theorem B2681105 : Blo 1786094 2681105 := bstep (se 2 (by rfl) ⟨1005414, by rfl⟩ : syracuseStep 2681105 = 2010829) B2010829
theorem B3016993 : Blo 1786094 3016993 := bstep (se 2 (by rfl) ⟨1131372, by rfl⟩ : syracuseStep 3016993 = 2262745) B2262745
theorem B2681123 : Blo 1786094 2681123 := bstep (se 1 (by rfl) ⟨2010842, by rfl⟩ : syracuseStep 2681123 = 4021685) B4021685
theorem B4294961 : Blo 1786094 4294961 := bstep (se 2 (by rfl) ⟨1610610, by rfl⟩ : syracuseStep 4294961 = 3221221) B3221221
theorem B2681153 : Blo 1786094 2681153 := bstep (se 2 (by rfl) ⟨1005432, by rfl⟩ : syracuseStep 2681153 = 2010865) B2010865
theorem B3017027 : Blo 1786094 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B2681171 : Blo 1786094 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B2009443 : Blo 1786094 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B2681201 : Blo 1786094 2681201 := bstep (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) B2010901
theorem B2681219 : Blo 1786094 2681219 := bstep (se 1 (by rfl) ⟨2010914, by rfl⟩ : syracuseStep 2681219 = 4021829) B4021829
theorem B2681249 : Blo 1786094 2681249 := bstep (se 2 (by rfl) ⟨1005468, by rfl⟩ : syracuseStep 2681249 = 2010937) B2010937
theorem B2681267 : Blo 1786094 2681267 := bstep (se 1 (by rfl) ⟨2010950, by rfl⟩ : syracuseStep 2681267 = 4021901) B4021901
theorem B3017155 : Blo 1786094 3017155 := bstep (se 1 (by rfl) ⟨2262866, by rfl⟩ : syracuseStep 3017155 = 4525733) B4525733
theorem B2681297 : Blo 1786094 2681297 := bstep (se 2 (by rfl) ⟨1005486, by rfl⟩ : syracuseStep 2681297 = 2010973) B2010973
theorem B2681315 : Blo 1786094 2681315 := bstep (se 1 (by rfl) ⟨2010986, by rfl⟩ : syracuseStep 2681315 = 4021973) B4021973
theorem B6031853 : Blo 1786094 6031853 := bstep (se 3 (by rfl) ⟨1130972, by rfl⟩ : syracuseStep 6031853 = 2261945) B2261945
theorem B2009587 : Blo 1786094 2009587 := bstep (se 1 (by rfl) ⟨1507190, by rfl⟩ : syracuseStep 2009587 = 3014381) B3014381
theorem B2681345 : Blo 1786094 2681345 := bstep (se 2 (by rfl) ⟨1005504, by rfl⟩ : syracuseStep 2681345 = 2011009) B2011009
theorem B2681363 : Blo 1786094 2681363 := bstep (se 1 (by rfl) ⟨2011022, by rfl⟩ : syracuseStep 2681363 = 4022045) B4022045
theorem B6031907 : Blo 1786094 6031907 := bstep (se 1 (by rfl) ⟨4523930, by rfl⟩ : syracuseStep 6031907 = 9047861) B9047861
theorem B2681393 : Blo 1786094 2681393 := bstep (se 2 (by rfl) ⟨1005522, by rfl⟩ : syracuseStep 2681393 = 2011045) B2011045
theorem B2681411 : Blo 1786094 2681411 := bstep (se 1 (by rfl) ⟨2011058, by rfl⟩ : syracuseStep 2681411 = 4022117) B4022117
theorem B3017297 : Blo 1786094 3017297 := bstep (se 2 (by rfl) ⟨1131486, by rfl⟩ : syracuseStep 3017297 = 2262973) B2262973
theorem B2681441 : Blo 1786094 2681441 := bstep (se 2 (by rfl) ⟨1005540, by rfl⟩ : syracuseStep 2681441 = 2011081) B2011081
theorem B2681459 : Blo 1786094 2681459 := bstep (se 1 (by rfl) ⟨2011094, by rfl⟩ : syracuseStep 2681459 = 4022189) B4022189
theorem B2009731 : Blo 1786094 2009731 := bstep (se 1 (by rfl) ⟨1507298, by rfl⟩ : syracuseStep 2009731 = 3014597) B3014597
theorem B2681489 : Blo 1786094 2681489 := bstep (se 2 (by rfl) ⟨1005558, by rfl⟩ : syracuseStep 2681489 = 2011117) B2011117
theorem B8587939 : Blo 1786094 8587939 := bstep (se 1 (by rfl) ⟨6440954, by rfl⟩ : syracuseStep 8587939 = 12881909) B12881909
theorem B2681507 : Blo 1786094 2681507 := bstep (se 1 (by rfl) ⟨2011130, by rfl⟩ : syracuseStep 2681507 = 4022261) B4022261
theorem B5089969 : Blo 1786094 5089969 := bstep (se 2 (by rfl) ⟨1908738, by rfl⟩ : syracuseStep 5089969 = 3817477) B3817477
theorem B2681537 : Blo 1786094 2681537 := bstep (se 2 (by rfl) ⟨1005576, by rfl⟩ : syracuseStep 2681537 = 2011153) B2011153
theorem B2681555 : Blo 1786094 2681555 := bstep (se 1 (by rfl) ⟨2011166, by rfl⟩ : syracuseStep 2681555 = 4022333) B4022333
theorem B10865393 : Blo 1786094 10865393 := bstep (se 2 (by rfl) ⟨4074522, by rfl⟩ : syracuseStep 10865393 = 8149045) B8149045
theorem B2681585 : Blo 1786094 2681585 := bstep (se 2 (by rfl) ⟨1005594, by rfl⟩ : syracuseStep 2681585 = 2011189) B2011189
theorem B2681603 : Blo 1786094 2681603 := bstep (se 1 (by rfl) ⟨2011202, by rfl⟩ : syracuseStep 2681603 = 4022405) B4022405
theorem B2009875 : Blo 1786094 2009875 := bstep (se 1 (by rfl) ⟨1507406, by rfl⟩ : syracuseStep 2009875 = 3014813) B3014813
theorem B2681633 : Blo 1786094 2681633 := bstep (se 2 (by rfl) ⟨1005612, by rfl⟩ : syracuseStep 2681633 = 2011225) B2011225
theorem B6441763 : Blo 1786094 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B6032177 : Blo 1786094 6032177 := bstep (se 2 (by rfl) ⟨2262066, by rfl⟩ : syracuseStep 6032177 = 4524133) B4524133
theorem B2681651 : Blo 1786094 2681651 := bstep (se 1 (by rfl) ⟨2011238, by rfl⟩ : syracuseStep 2681651 = 4022477) B4022477
theorem B2681681 : Blo 1786094 2681681 := bstep (se 2 (by rfl) ⟨1005630, by rfl⟩ : syracuseStep 2681681 = 2011261) B2011261
theorem B2681699 : Blo 1786094 2681699 := bstep (se 1 (by rfl) ⟨2011274, by rfl⟩ : syracuseStep 2681699 = 4022549) B4022549
theorem B11447153 : Blo 1786094 11447153 := bstep (se 2 (by rfl) ⟨4292682, by rfl⟩ : syracuseStep 11447153 = 8585365) B8585365
theorem B2681729 : Blo 1786094 2681729 := bstep (se 2 (by rfl) ⟨1005648, by rfl⟩ : syracuseStep 2681729 = 2011297) B2011297
theorem B2681747 : Blo 1786094 2681747 := bstep (se 1 (by rfl) ⟨2011310, by rfl⟩ : syracuseStep 2681747 = 4022621) B4022621
theorem B11447203 : Blo 1786094 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B2010019 : Blo 1786094 2010019 := bstep (se 1 (by rfl) ⟨1507514, by rfl⟩ : syracuseStep 2010019 = 3015029) B3015029
theorem B2681777 : Blo 1786094 2681777 := bstep (se 2 (by rfl) ⟨1005666, by rfl⟩ : syracuseStep 2681777 = 2011333) B2011333
theorem B2681795 : Blo 1786094 2681795 := bstep (se 1 (by rfl) ⟨2011346, by rfl⟩ : syracuseStep 2681795 = 4022693) B4022693
theorem B2681825 : Blo 1786094 2681825 := bstep (se 2 (by rfl) ⟨1005684, by rfl⟩ : syracuseStep 2681825 = 2011369) B2011369
theorem B2681843 : Blo 1786094 2681843 := bstep (se 1 (by rfl) ⟨2011382, by rfl⟩ : syracuseStep 2681843 = 4022765) B4022765
theorem B2862083 : Blo 1786094 2862083 := bstep (se 1 (by rfl) ⟨2146562, by rfl⟩ : syracuseStep 2862083 = 4293125) B4293125
theorem B2681873 : Blo 1786094 2681873 := bstep (se 2 (by rfl) ⟨1005702, by rfl⟩ : syracuseStep 2681873 = 2011405) B2011405
theorem B2681891 : Blo 1786094 2681891 := bstep (se 1 (by rfl) ⟨2011418, by rfl⟩ : syracuseStep 2681891 = 4022837) B4022837
theorem B4525105 : Blo 1786094 4525105 := bstep (se 2 (by rfl) ⟨1696914, by rfl⟩ : syracuseStep 4525105 = 3393829) B3393829
theorem B2010163 : Blo 1786094 2010163 := bstep (se 1 (by rfl) ⟨1507622, by rfl⟩ : syracuseStep 2010163 = 3015245) B3015245
theorem B2681921 : Blo 1786094 2681921 := bstep (se 2 (by rfl) ⟨1005720, by rfl⟩ : syracuseStep 2681921 = 2011441) B2011441
theorem B6786125 : Blo 1786094 6786125 := bstep (se 3 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 6786125 = 2544797) B2544797
theorem B2681939 : Blo 1786094 2681939 := bstep (se 1 (by rfl) ⟨2011454, by rfl⟩ : syracuseStep 2681939 = 4022909) B4022909
theorem B2681969 : Blo 1786094 2681969 := bstep (se 2 (by rfl) ⟨1005738, by rfl⟩ : syracuseStep 2681969 = 2011477) B2011477
theorem B2862211 : Blo 1786094 2862211 := bstep (se 1 (by rfl) ⟨2146658, by rfl⟩ : syracuseStep 2862211 = 4293317) B4293317
theorem B2681987 : Blo 1786094 2681987 := bstep (se 1 (by rfl) ⟨2011490, by rfl⟩ : syracuseStep 2681987 = 4022981) B4022981
theorem B2682017 : Blo 1786094 2682017 := bstep (se 2 (by rfl) ⟨1005756, by rfl⟩ : syracuseStep 2682017 = 2011513) B2011513
theorem B2682035 : Blo 1786094 2682035 := bstep (se 1 (by rfl) ⟨2011526, by rfl⟩ : syracuseStep 2682035 = 4023053) B4023053
theorem B2010307 : Blo 1786094 2010307 := bstep (se 1 (by rfl) ⟨1507730, by rfl⟩ : syracuseStep 2010307 = 3015461) B3015461
theorem B2682065 : Blo 1786094 2682065 := bstep (se 2 (by rfl) ⟨1005774, by rfl⟩ : syracuseStep 2682065 = 2011549) B2011549
theorem B2682083 : Blo 1786094 2682083 := bstep (se 1 (by rfl) ⟨2011562, by rfl⟩ : syracuseStep 2682083 = 4023125) B4023125
theorem B2682113 : Blo 1786094 2682113 := bstep (se 2 (by rfl) ⟨1005792, by rfl⟩ : syracuseStep 2682113 = 2011585) B2011585
theorem B2862353 : Blo 1786094 2862353 := bstep (se 2 (by rfl) ⟨1073382, by rfl⟩ : syracuseStep 2862353 = 2146765) B2146765
theorem B2682131 : Blo 1786094 2682131 := bstep (se 1 (by rfl) ⟨2011598, by rfl⟩ : syracuseStep 2682131 = 4023197) B4023197
theorem B4525379 : Blo 1786094 4525379 := bstep (se 1 (by rfl) ⟨3394034, by rfl⟩ : syracuseStep 4525379 = 6788069) B6788069
theorem B6032717 : Blo 1786094 6032717 := bstep (se 3 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 6032717 = 2262269) B2262269
theorem B2010451 : Blo 1786094 2010451 := bstep (se 1 (by rfl) ⟨1507838, by rfl⟩ : syracuseStep 2010451 = 3015677) B3015677
theorem B6032771 : Blo 1786094 6032771 := bstep (se 1 (by rfl) ⟨4524578, by rfl⟩ : syracuseStep 6032771 = 9049157) B9049157
theorem B10177933 : Blo 1786094 10177933 := bstep (se 3 (by rfl) ⟨1908362, by rfl⟩ : syracuseStep 10177933 = 3816725) B3816725
theorem B3624401 : Blo 1786094 3624401 := bstep (se 2 (by rfl) ⟨1359150, by rfl⟩ : syracuseStep 3624401 = 2718301) B2718301
theorem B7630307 : Blo 1786094 7630307 := bstep (se 1 (by rfl) ⟨5722730, by rfl⟩ : syracuseStep 7630307 = 11445461) B11445461
theorem B2010595 : Blo 1786094 2010595 := bstep (se 1 (by rfl) ⟨1507946, by rfl⟩ : syracuseStep 2010595 = 3015893) B3015893
theorem B5803501 : Blo 1786094 5803501 := bstep (se 3 (by rfl) ⟨1088156, by rfl⟩ : syracuseStep 5803501 = 2176313) B2176313
theorem B9047537 : Blo 1786094 9047537 := bstep (se 2 (by rfl) ⟨3392826, by rfl⟩ : syracuseStep 9047537 = 6785653) B6785653
theorem B4525571 : Blo 1786094 4525571 := bstep (se 1 (by rfl) ⟨3394178, by rfl⟩ : syracuseStep 4525571 = 6788357) B6788357
theorem B2862641 : Blo 1786094 2862641 := bstep (se 2 (by rfl) ⟨1073490, by rfl⟩ : syracuseStep 2862641 = 2146981) B2146981
theorem B13569605 : Blo 1786094 13569605 := bstep (se 4 (by rfl) ⟨1272150, by rfl⟩ : syracuseStep 13569605 = 2544301) B2544301
theorem B2543185 : Blo 1786094 2543185 := bstep (se 2 (by rfl) ⟨953694, by rfl⟩ : syracuseStep 2543185 = 1907389) B1907389
theorem B4828771 : Blo 1786094 4828771 := bstep (se 1 (by rfl) ⟨3621578, by rfl⟩ : syracuseStep 4828771 = 7243157) B7243157
theorem B11456099 : Blo 1786094 11456099 := bstep (se 1 (by rfl) ⟨8592074, by rfl⟩ : syracuseStep 11456099 = 17184149) B17184149
theorem B97807985 : Blo 1786094 97807985 := bstep (se 2 (by rfl) ⟨36677994, by rfl⟩ : syracuseStep 97807985 = 73355989) B73355989
theorem B2010739 : Blo 1786094 2010739 := bstep (se 1 (by rfl) ⟨1508054, by rfl⟩ : syracuseStep 2010739 = 3016109) B3016109
theorem B6033041 : Blo 1786094 6033041 := bstep (se 2 (by rfl) ⟨2262390, by rfl⟩ : syracuseStep 6033041 = 4524781) B4524781
theorem B8826545 : Blo 1786094 8826545 := bstep (se 2 (by rfl) ⟨3309954, by rfl⟩ : syracuseStep 8826545 = 6619909) B6619909
theorem B4353745 : Blo 1786094 4353745 := bstep (se 2 (by rfl) ⟨1632654, by rfl⟩ : syracuseStep 4353745 = 3265309) B3265309
theorem B79400675 : Blo 1786094 79400675 := bstep (se 1 (by rfl) ⟨59550506, by rfl⟩ : syracuseStep 79400675 = 119101013) B119101013
theorem B2010883 : Blo 1786094 2010883 := bstep (se 1 (by rfl) ⟨1508162, by rfl⟩ : syracuseStep 2010883 = 3016325) B3016325
theorem B8589169 : Blo 1786094 8589169 := bstep (se 2 (by rfl) ⟨3220938, by rfl⟩ : syracuseStep 8589169 = 6441877) B6441877
theorem B6786929 : Blo 1786094 6786929 := bstep (se 2 (by rfl) ⟨2545098, by rfl⟩ : syracuseStep 6786929 = 5090197) B5090197
theorem B2011027 : Blo 1786094 2011027 := bstep (se 1 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 2011027 = 3016541) B3016541
theorem B5091245 : Blo 1786094 5091245 := bstep (se 3 (by rfl) ⟨954608, by rfl⟩ : syracuseStep 5091245 = 1909217) B1909217
theorem B36671429 : Blo 1786094 36671429 := bstep (se 4 (by rfl) ⟨3437946, by rfl⟩ : syracuseStep 36671429 = 6875893) B6875893
theorem B2011171 : Blo 1786094 2011171 := bstep (se 1 (by rfl) ⟨1508378, by rfl⟩ : syracuseStep 2011171 = 3016757) B3016757
theorem B2715697 : Blo 1786094 2715697 := bstep (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) B2036773
theorem B20344931 : Blo 1786094 20344931 := bstep (se 1 (by rfl) ⟨15258698, by rfl⟩ : syracuseStep 20344931 = 30517397) B30517397
theorem B5091427 : Blo 1786094 5091427 := bstep (se 1 (by rfl) ⟨3818570, by rfl⟩ : syracuseStep 5091427 = 7637141) B7637141
theorem B5091473 : Blo 1786094 5091473 := bstep (se 2 (by rfl) ⟨1909302, by rfl⟩ : syracuseStep 5091473 = 3818605) B3818605
theorem B6033581 : Blo 1786094 6033581 := bstep (se 3 (by rfl) ⟨1131296, by rfl⟩ : syracuseStep 6033581 = 2262593) B2262593
theorem B2011315 : Blo 1786094 2011315 := bstep (se 1 (by rfl) ⟨1508486, by rfl⟩ : syracuseStep 2011315 = 3016973) B3016973
theorem B6033635 : Blo 1786094 6033635 := bstep (se 1 (by rfl) ⟨4525226, by rfl⟩ : syracuseStep 6033635 = 9050453) B9050453
theorem B2543891 : Blo 1786094 2543891 := bstep (se 1 (by rfl) ⟨1907918, by rfl⟩ : syracuseStep 2543891 = 3815837) B3815837
theorem B4829507 : Blo 1786094 4829507 := bstep (se 1 (by rfl) ⟨3622130, by rfl⟩ : syracuseStep 4829507 = 7244261) B7244261
theorem B2011459 : Blo 1786094 2011459 := bstep (se 1 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 2011459 = 3017189) B3017189
theorem B2863441 : Blo 1786094 2863441 := bstep (se 2 (by rfl) ⟨1073790, by rfl⟩ : syracuseStep 2863441 = 2147581) B2147581
theorem B4354417 : Blo 1786094 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B7737805 : Blo 1786094 7737805 := bstep (se 3 (by rfl) ⟨1450838, by rfl⟩ : syracuseStep 7737805 = 2901677) B2901677
theorem B2011603 : Blo 1786094 2011603 := bstep (se 1 (by rfl) ⟨1508702, by rfl⟩ : syracuseStep 2011603 = 3017405) B3017405
theorem B6033905 : Blo 1786094 6033905 := bstep (se 2 (by rfl) ⟨2262714, by rfl⟩ : syracuseStep 6033905 = 4525429) B4525429
theorem B6787597 : Blo 1786094 6787597 := bstep (se 3 (by rfl) ⟨1272674, by rfl⟩ : syracuseStep 6787597 = 2545349) B2545349
theorem B4018769 : Blo 1786094 4018769 := bstep (se 2 (by rfl) ⟨1507038, by rfl⟩ : syracuseStep 4018769 = 3014077) B3014077
theorem B4018787 : Blo 1786094 4018787 := bstep (se 1 (by rfl) ⟨3014090, by rfl⟩ : syracuseStep 4018787 = 6028181) B6028181
theorem B4019057 : Blo 1786094 4019057 := bstep (se 2 (by rfl) ⟨1507146, by rfl⟩ : syracuseStep 4019057 = 3014293) B3014293
theorem B4019075 : Blo 1786094 4019075 := bstep (se 1 (by rfl) ⟨3014306, by rfl⟩ : syracuseStep 4019075 = 6028613) B6028613
theorem B2544529 : Blo 1786094 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B9048995 : Blo 1786094 9048995 := bstep (se 1 (by rfl) ⟨6786746, by rfl⟩ : syracuseStep 9048995 = 13573493) B13573493
theorem B2544643 : Blo 1786094 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B6034445 : Blo 1786094 6034445 := bstep (se 3 (by rfl) ⟨1131458, by rfl⟩ : syracuseStep 6034445 = 2262917) B2262917
theorem B4830275 : Blo 1786094 4830275 := bstep (se 1 (by rfl) ⟨3622706, by rfl⟩ : syracuseStep 4830275 = 7245413) B7245413
theorem B6034499 : Blo 1786094 6034499 := bstep (se 1 (by rfl) ⟨4525874, by rfl⟩ : syracuseStep 6034499 = 9051749) B9051749
theorem B4019345 : Blo 1786094 4019345 := bstep (se 2 (by rfl) ⟨1507254, by rfl⟩ : syracuseStep 4019345 = 3014509) B3014509
theorem B4019363 : Blo 1786094 4019363 := bstep (se 1 (by rfl) ⟨3014522, by rfl⟩ : syracuseStep 4019363 = 6029045) B6029045
theorem B4830371 : Blo 1786094 4830371 := bstep (se 1 (by rfl) ⟨3622778, by rfl⟩ : syracuseStep 4830371 = 7245557) B7245557
theorem B5723345 : Blo 1786094 5723345 := bstep (se 2 (by rfl) ⟨2146254, by rfl⟩ : syracuseStep 5723345 = 4292509) B4292509
theorem B11449613 : Blo 1786094 11449613 := bstep (se 3 (by rfl) ⟨2146802, by rfl⟩ : syracuseStep 11449613 = 4293605) B4293605
theorem B6788387 : Blo 1786094 6788387 := bstep (se 1 (by rfl) ⟨5091290, by rfl⟩ : syracuseStep 6788387 = 10182581) B10182581
theorem B4076867 : Blo 1786094 4076867 := bstep (se 1 (by rfl) ⟨3057650, by rfl⟩ : syracuseStep 4076867 = 6115301) B6115301
theorem B10179917 : Blo 1786094 10179917 := bstep (se 3 (by rfl) ⟨1908734, by rfl⟩ : syracuseStep 10179917 = 3817469) B3817469
theorem B6034769 : Blo 1786094 6034769 := bstep (se 2 (by rfl) ⟨2263038, by rfl⟩ : syracuseStep 6034769 = 4526077) B4526077
theorem B4019633 : Blo 1786094 4019633 := bstep (se 2 (by rfl) ⟨1507362, by rfl⟩ : syracuseStep 4019633 = 3014725) B3014725
theorem B4019651 : Blo 1786094 4019651 := bstep (se 1 (by rfl) ⟨3014738, by rfl⟩ : syracuseStep 4019651 = 6029477) B6029477
theorem B18347633 : Blo 1786094 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B9049805 : Blo 1786094 9049805 := bstep (se 3 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 9049805 = 3393677) B3393677
theorem B4019921 : Blo 1786094 4019921 := bstep (se 2 (by rfl) ⟨1507470, by rfl⟩ : syracuseStep 4019921 = 3014941) B3014941
theorem B4019939 : Blo 1786094 4019939 := bstep (se 1 (by rfl) ⟨3014954, by rfl⟩ : syracuseStep 4019939 = 6029909) B6029909
theorem B5723885 : Blo 1786094 5723885 := bstep (se 3 (by rfl) ⟨1073228, by rfl⟩ : syracuseStep 5723885 = 2146457) B2146457
theorem B3815171 : Blo 1786094 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B2717473 : Blo 1786094 2717473 := bstep (se 2 (by rfl) ⟨1019052, by rfl⟩ : syracuseStep 2717473 = 2038105) B2038105
theorem B17413957 : Blo 1786094 17413957 := bstep (se 4 (by rfl) ⟨1632558, by rfl⟩ : syracuseStep 17413957 = 3265117) B3265117
theorem B6789041 : Blo 1786094 6789041 := bstep (se 2 (by rfl) ⟨2545890, by rfl⟩ : syracuseStep 6789041 = 5091781) B5091781
theorem B2717633 : Blo 1786094 2717633 := bstep (se 2 (by rfl) ⟨1019112, by rfl⟩ : syracuseStep 2717633 = 2038225) B2038225
theorem B15259589 : Blo 1786094 15259589 := bstep (se 4 (by rfl) ⟨1430586, by rfl⟩ : syracuseStep 15259589 = 2861173) B2861173
theorem B4020209 : Blo 1786094 4020209 := bstep (se 2 (by rfl) ⟨1507578, by rfl⟩ : syracuseStep 4020209 = 3015157) B3015157
theorem B4020227 : Blo 1786094 4020227 := bstep (se 1 (by rfl) ⟨3015170, by rfl⟩ : syracuseStep 4020227 = 6030341) B6030341
theorem B4413521 : Blo 1786094 4413521 := bstep (se 2 (by rfl) ⟨1655070, by rfl⟩ : syracuseStep 4413521 = 3310141) B3310141
theorem B9173197 : Blo 1786094 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B10180849 : Blo 1786094 10180849 := bstep (se 2 (by rfl) ⟨3817818, by rfl⟩ : syracuseStep 10180849 = 7635637) B7635637
theorem B4020497 : Blo 1786094 4020497 := bstep (se 2 (by rfl) ⟨1507686, by rfl⟩ : syracuseStep 4020497 = 3015373) B3015373
theorem B4020515 : Blo 1786094 4020515 := bstep (se 1 (by rfl) ⟨3015386, by rfl⟩ : syracuseStep 4020515 = 6030773) B6030773
theorem B26482997 : Blo 1786094 26482997 := bstep (se 5 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 26482997 = 2482781) B2482781
theorem B4962637 : Blo 1786094 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B3815761 : Blo 1786094 3815761 := bstep (se 2 (by rfl) ⟨1430910, by rfl⟩ : syracuseStep 3815761 = 2861821) B2861821
theorem B13564259 : Blo 1786094 13564259 := bstep (se 1 (by rfl) ⟨10173194, by rfl⟩ : syracuseStep 13564259 = 20346389) B20346389
theorem B9042353 : Blo 1786094 9042353 := bstep (se 2 (by rfl) ⟨3390882, by rfl⟩ : syracuseStep 9042353 = 6781765) B6781765
theorem B12876259 : Blo 1786094 12876259 := bstep (se 1 (by rfl) ⟨9657194, by rfl⟩ : syracuseStep 12876259 = 19314389) B19314389
theorem B15268337 : Blo 1786094 15268337 := bstep (se 2 (by rfl) ⟨5725626, by rfl⟩ : syracuseStep 15268337 = 11451253) B11451253
theorem B2578963 : Blo 1786094 2578963 := bstep (se 1 (by rfl) ⟨1934222, by rfl⟩ : syracuseStep 2578963 = 3868445) B3868445
theorem B4020785 : Blo 1786094 4020785 := bstep (se 2 (by rfl) ⟨1507794, by rfl⟩ : syracuseStep 4020785 = 3015589) B3015589
theorem B2906675 : Blo 1786094 2906675 := bstep (se 1 (by rfl) ⟨2180006, by rfl⟩ : syracuseStep 2906675 = 4360013) B4360013
theorem B4020803 : Blo 1786094 4020803 := bstep (se 1 (by rfl) ⟨3015602, by rfl⟩ : syracuseStep 4020803 = 6031205) B6031205
theorem B8706865 : Blo 1786094 8706865 := bstep (se 2 (by rfl) ⟨3265074, by rfl⟩ : syracuseStep 8706865 = 6530149) B6530149
theorem B4021073 : Blo 1786094 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B4021091 : Blo 1786094 4021091 := bstep (se 1 (by rfl) ⟨3015818, by rfl⟩ : syracuseStep 4021091 = 6031637) B6031637
theorem B21740557 : Blo 1786094 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B2415683 : Blo 1786094 2415683 := bstep (se 1 (by rfl) ⟨1811762, by rfl⟩ : syracuseStep 2415683 = 3623525) B3623525
theorem B7633997 : Blo 1786094 7633997 := bstep (se 3 (by rfl) ⟨1431374, by rfl⟩ : syracuseStep 7633997 = 2862749) B2862749
theorem B6028397 : Blo 1786094 6028397 := bstep (se 3 (by rfl) ⟨1130324, by rfl⟩ : syracuseStep 6028397 = 2260649) B2260649
theorem B32603249 : Blo 1786094 32603249 := bstep (se 2 (by rfl) ⟨12226218, by rfl⟩ : syracuseStep 32603249 = 24452437) B24452437
theorem B7634033 : Blo 1786094 7634033 := bstep (se 2 (by rfl) ⟨2862762, by rfl⟩ : syracuseStep 7634033 = 5725525) B5725525
theorem B4021361 : Blo 1786094 4021361 := bstep (se 2 (by rfl) ⟨1508010, by rfl⟩ : syracuseStep 4021361 = 3016021) B3016021
theorem B4021379 : Blo 1786094 4021379 := bstep (se 1 (by rfl) ⟨3016034, by rfl⟩ : syracuseStep 4021379 = 6032069) B6032069
theorem B6028451 : Blo 1786094 6028451 := bstep (se 1 (by rfl) ⟨4521338, by rfl⟩ : syracuseStep 6028451 = 9042677) B9042677
theorem B7347469 : Blo 1786094 7347469 := bstep (se 3 (by rfl) ⟨1377650, by rfl⟩ : syracuseStep 7347469 = 2755301) B2755301
theorem B10870085 : Blo 1786094 10870085 := bstep (se 4 (by rfl) ⟨1019070, by rfl⟩ : syracuseStep 10870085 = 2038141) B2038141
theorem B4521329 : Blo 1786094 4521329 := bstep (se 2 (by rfl) ⟨1695498, by rfl⟩ : syracuseStep 4521329 = 3390997) B3390997
theorem B4021649 : Blo 1786094 4021649 := bstep (se 2 (by rfl) ⟨1508118, by rfl⟩ : syracuseStep 4021649 = 3016237) B3016237
theorem B4521379 : Blo 1786094 4521379 := bstep (se 1 (by rfl) ⟨3391034, by rfl⟩ : syracuseStep 4521379 = 6782069) B6782069
theorem B4021667 : Blo 1786094 4021667 := bstep (se 1 (by rfl) ⟨3016250, by rfl⟩ : syracuseStep 4021667 = 6032501) B6032501
theorem B6028721 : Blo 1786094 6028721 := bstep (se 2 (by rfl) ⟨2260770, by rfl⟩ : syracuseStep 6028721 = 4521541) B4521541
theorem B3218915 : Blo 1786094 3218915 := bstep (se 1 (by rfl) ⟨2414186, by rfl⟩ : syracuseStep 3218915 = 4828373) B4828373
theorem B3014131 : Blo 1786094 3014131 := bstep (se 1 (by rfl) ⟨2260598, by rfl⟩ : syracuseStep 3014131 = 4521197) B4521197
theorem B9166385 : Blo 1786094 9166385 := bstep (se 2 (by rfl) ⟨3437394, by rfl⟩ : syracuseStep 9166385 = 6874789) B6874789
theorem B4521521 : Blo 1786094 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B3014273 : Blo 1786094 3014273 := bstep (se 2 (by rfl) ⟨1130352, by rfl⟩ : syracuseStep 3014273 = 2260705) B2260705
theorem B10174085 : Blo 1786094 10174085 := bstep (se 4 (by rfl) ⟨953820, by rfl⟩ : syracuseStep 10174085 = 1907641) B1907641
theorem B10182307 : Blo 1786094 10182307 := bstep (se 1 (by rfl) ⟨7636730, by rfl⟩ : syracuseStep 10182307 = 15273461) B15273461
theorem B4021937 : Blo 1786094 4021937 := bstep (se 2 (by rfl) ⟨1508226, by rfl⟩ : syracuseStep 4021937 = 3016453) B3016453
theorem B4021955 : Blo 1786094 4021955 := bstep (se 1 (by rfl) ⟨3016466, by rfl⟩ : syracuseStep 4021955 = 6032933) B6032933
theorem B3391217 : Blo 1786094 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B3014401 : Blo 1786094 3014401 := bstep (se 2 (by rfl) ⟨1130400, by rfl⟩ : syracuseStep 3014401 = 2260801) B2260801
theorem B11444003 : Blo 1786094 11444003 := bstep (se 1 (by rfl) ⟨8583002, by rfl⟩ : syracuseStep 11444003 = 17166005) B17166005
theorem B3014435 : Blo 1786094 3014435 := bstep (se 1 (by rfl) ⟨2260826, by rfl⟩ : syracuseStep 3014435 = 4521653) B4521653
theorem B5087053 : Blo 1786094 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B9043811 : Blo 1786094 9043811 := bstep (se 1 (by rfl) ⟨6782858, by rfl⟩ : syracuseStep 9043811 = 13565717) B13565717
theorem B2416483 : Blo 1786094 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B2260867 : Blo 1786094 2260867 := bstep (se 1 (by rfl) ⟨1695650, by rfl⟩ : syracuseStep 2260867 = 3391301) B3391301
theorem B3014563 : Blo 1786094 3014563 := bstep (se 1 (by rfl) ⟨2260922, by rfl⟩ : syracuseStep 3014563 = 4521845) B4521845
theorem B6029261 : Blo 1786094 6029261 := bstep (se 3 (by rfl) ⟨1130486, by rfl⟩ : syracuseStep 6029261 = 2260973) B2260973
theorem B4022225 : Blo 1786094 4022225 := bstep (se 2 (by rfl) ⟨1508334, by rfl⟩ : syracuseStep 4022225 = 3016669) B3016669
theorem B2260963 : Blo 1786094 2260963 := bstep (se 1 (by rfl) ⟨1695722, by rfl⟩ : syracuseStep 2260963 = 3391445) B3391445
theorem B4022243 : Blo 1786094 4022243 := bstep (se 1 (by rfl) ⟨3016682, by rfl⟩ : syracuseStep 4022243 = 6033365) B6033365
theorem B4522007 : Blo 1786094 4522007 := bstep (se 1 (by rfl) ⟨3391505, by rfl⟩ : syracuseStep 4522007 = 6783011) B6783011
theorem B4022297 : Blo 1786094 4022297 := bstep (se 2 (by rfl) ⟨1508361, by rfl⟩ : syracuseStep 4022297 = 3016723) B3016723
theorem B6783041 : Blo 1786094 6783041 := bstep (se 2 (by rfl) ⟨2543640, by rfl⟩ : syracuseStep 6783041 = 5087281) B5087281
theorem B74326085 : Blo 1786094 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B9175133 : Blo 1786094 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B4022387 : Blo 1786094 4022387 := bstep (se 1 (by rfl) ⟨3016790, by rfl⟩ : syracuseStep 4022387 = 6033581) B6033581
theorem B3391627 : Blo 1786094 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B4022423 : Blo 1786094 4022423 := bstep (se 1 (by rfl) ⟨3016817, by rfl⟩ : syracuseStep 4022423 = 6033635) B6033635
theorem B3391703 : Blo 1786094 3391703 := bstep (se 1 (by rfl) ⟨2543777, by rfl⟩ : syracuseStep 3391703 = 5087555) B5087555
theorem B3219671 : Blo 1786094 3219671 := bstep (se 1 (by rfl) ⟨2414753, by rfl⟩ : syracuseStep 3219671 = 4829507) B4829507
theorem B1786103 : Blo 1786094 1786103 := bstep (se 1 (by rfl) ⟨1339577, by rfl⟩ : syracuseStep 1786103 = 2679155) B2679155
theorem B14483717 : Blo 1786094 14483717 := bstep (se 4 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 14483717 = 2715697) B2715697
theorem B1786123 : Blo 1786094 1786123 := bstep (se 1 (by rfl) ⟨1339592, by rfl⟩ : syracuseStep 1786123 = 2679185) B2679185
theorem B12230929 : Blo 1786094 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B1786135 : Blo 1786094 1786135 := bstep (se 1 (by rfl) ⟨1339601, by rfl⟩ : syracuseStep 1786135 = 2679203) B2679203
theorem B1786155 : Blo 1786094 1786155 := bstep (se 1 (by rfl) ⟨1339616, by rfl⟩ : syracuseStep 1786155 = 2679233) B2679233
theorem B86941997 : Blo 1786094 86941997 := bstep (se 3 (by rfl) ⟨16301624, by rfl⟩ : syracuseStep 86941997 = 32603249) B32603249
theorem B1786167 : Blo 1786094 1786167 := bstep (se 1 (by rfl) ⟨1339625, by rfl⟩ : syracuseStep 1786167 = 2679251) B2679251
theorem B13574465 : Blo 1786094 13574465 := bstep (se 2 (by rfl) ⟨5090424, by rfl⟩ : syracuseStep 13574465 = 10180849) B10180849
theorem B1786187 : Blo 1786094 1786187 := bstep (se 1 (by rfl) ⟨1339640, by rfl⟩ : syracuseStep 1786187 = 2679281) B2679281
theorem B4022603 : Blo 1786094 4022603 := bstep (se 1 (by rfl) ⟨3016952, by rfl⟩ : syracuseStep 4022603 = 6033905) B6033905
theorem B1786199 : Blo 1786094 1786199 := bstep (se 1 (by rfl) ⟨1339649, by rfl⟩ : syracuseStep 1786199 = 2679299) B2679299
theorem B1786219 : Blo 1786094 1786219 := bstep (se 1 (by rfl) ⟨1339664, by rfl⟩ : syracuseStep 1786219 = 2679329) B2679329
theorem B1786231 : Blo 1786094 1786231 := bstep (se 1 (by rfl) ⟨1339673, by rfl⟩ : syracuseStep 1786231 = 2679347) B2679347
theorem B4022657 : Blo 1786094 4022657 := bstep (se 2 (by rfl) ⟨1508496, by rfl⟩ : syracuseStep 4022657 = 3016993) B3016993
theorem B2679179 : Blo 1786094 2679179 := bstep (se 1 (by rfl) ⟨2009384, by rfl⟩ : syracuseStep 2679179 = 4018769) B4018769
theorem B1786251 : Blo 1786094 1786251 := bstep (se 1 (by rfl) ⟨1339688, by rfl⟩ : syracuseStep 1786251 = 2679377) B2679377
theorem B2679191 : Blo 1786094 2679191 := bstep (se 1 (by rfl) ⟨2009393, by rfl⟩ : syracuseStep 2679191 = 4018787) B4018787
theorem B1786263 : Blo 1786094 1786263 := bstep (se 1 (by rfl) ⟨1339697, by rfl⟩ : syracuseStep 1786263 = 2679395) B2679395
theorem B1786283 : Blo 1786094 1786283 := bstep (se 1 (by rfl) ⟨1339712, by rfl⟩ : syracuseStep 1786283 = 2679425) B2679425
theorem B6029747 : Blo 1786094 6029747 := bstep (se 1 (by rfl) ⟨4522310, by rfl⟩ : syracuseStep 6029747 = 9044621) B9044621
theorem B1786295 : Blo 1786094 1786295 := bstep (se 1 (by rfl) ⟨1339721, by rfl⟩ : syracuseStep 1786295 = 2679443) B2679443
theorem B5087681 : Blo 1786094 5087681 := bstep (se 2 (by rfl) ⟨1907880, by rfl⟩ : syracuseStep 5087681 = 3815761) B3815761
theorem B1786315 : Blo 1786094 1786315 := bstep (se 1 (by rfl) ⟨1339736, by rfl⟩ : syracuseStep 1786315 = 2679473) B2679473
theorem B1786327 : Blo 1786094 1786327 := bstep (se 1 (by rfl) ⟨1339745, by rfl⟩ : syracuseStep 1786327 = 2679491) B2679491
theorem B2679257 : Blo 1786094 2679257 := bstep (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) B2009443
theorem B1786347 : Blo 1786094 1786347 := bstep (se 1 (by rfl) ⟨1339760, by rfl⟩ : syracuseStep 1786347 = 2679521) B2679521
theorem B1786359 : Blo 1786094 1786359 := bstep (se 1 (by rfl) ⟨1339769, by rfl⟩ : syracuseStep 1786359 = 2679539) B2679539
theorem B1786379 : Blo 1786094 1786379 := bstep (se 1 (by rfl) ⟨1339784, by rfl⟩ : syracuseStep 1786379 = 2679569) B2679569
theorem B2261515 : Blo 1786094 2261515 := bstep (se 1 (by rfl) ⟨1696136, by rfl⟩ : syracuseStep 2261515 = 3392273) B3392273
theorem B1786391 : Blo 1786094 1786391 := bstep (se 1 (by rfl) ⟨1339793, by rfl⟩ : syracuseStep 1786391 = 2679587) B2679587
theorem B3015191 : Blo 1786094 3015191 := bstep (se 1 (by rfl) ⟨2261393, by rfl⟩ : syracuseStep 3015191 = 4522787) B4522787
theorem B1786411 : Blo 1786094 1786411 := bstep (se 1 (by rfl) ⟨1339808, by rfl⟩ : syracuseStep 1786411 = 2679617) B2679617
theorem B15262253 : Blo 1786094 15262253 := bstep (se 3 (by rfl) ⟨2861672, by rfl⟩ : syracuseStep 15262253 = 5723345) B5723345
theorem B1786423 : Blo 1786094 1786423 := bstep (se 1 (by rfl) ⟨1339817, by rfl⟩ : syracuseStep 1786423 = 2679635) B2679635
theorem B2679371 : Blo 1786094 2679371 := bstep (se 1 (by rfl) ⟨2009528, by rfl⟩ : syracuseStep 2679371 = 4019057) B4019057
theorem B1786443 : Blo 1786094 1786443 := bstep (se 1 (by rfl) ⟨1339832, by rfl⟩ : syracuseStep 1786443 = 2679665) B2679665
theorem B2679383 : Blo 1786094 2679383 := bstep (se 1 (by rfl) ⟨2009537, by rfl⟩ : syracuseStep 2679383 = 4019075) B4019075
theorem B1786455 : Blo 1786094 1786455 := bstep (se 1 (by rfl) ⟨1339841, by rfl⟩ : syracuseStep 1786455 = 2679683) B2679683
theorem B4022873 : Blo 1786094 4022873 := bstep (se 2 (by rfl) ⟨1508577, by rfl⟩ : syracuseStep 4022873 = 3017155) B3017155
theorem B1786475 : Blo 1786094 1786475 := bstep (se 1 (by rfl) ⟨1339856, by rfl⟩ : syracuseStep 1786475 = 2679713) B2679713
theorem B1786487 : Blo 1786094 1786487 := bstep (se 1 (by rfl) ⟨1339865, by rfl⟩ : syracuseStep 1786487 = 2679731) B2679731
theorem B1786507 : Blo 1786094 1786507 := bstep (se 1 (by rfl) ⟨1339880, by rfl⟩ : syracuseStep 1786507 = 2679761) B2679761
theorem B1786519 : Blo 1786094 1786519 := bstep (se 1 (by rfl) ⟨1339889, by rfl⟩ : syracuseStep 1786519 = 2679779) B2679779
theorem B3015319 : Blo 1786094 3015319 := bstep (se 1 (by rfl) ⟨2261489, by rfl⟩ : syracuseStep 3015319 = 4522979) B4522979
theorem B2679449 : Blo 1786094 2679449 := bstep (se 2 (by rfl) ⟨1004793, by rfl⟩ : syracuseStep 2679449 = 2009587) B2009587
theorem B1786539 : Blo 1786094 1786539 := bstep (se 1 (by rfl) ⟨1339904, by rfl⟩ : syracuseStep 1786539 = 2679809) B2679809
theorem B4522675 : Blo 1786094 4522675 := bstep (se 1 (by rfl) ⟨3392006, by rfl⟩ : syracuseStep 4522675 = 6784013) B6784013
theorem B4022963 : Blo 1786094 4022963 := bstep (se 1 (by rfl) ⟨3017222, by rfl⟩ : syracuseStep 4022963 = 6034445) B6034445
theorem B1786551 : Blo 1786094 1786551 := bstep (se 1 (by rfl) ⟨1339913, by rfl⟩ : syracuseStep 1786551 = 2679827) B2679827
theorem B6030017 : Blo 1786094 6030017 := bstep (se 2 (by rfl) ⟨2261256, by rfl⟩ : syracuseStep 6030017 = 4522513) B4522513
theorem B1786571 : Blo 1786094 1786571 := bstep (se 1 (by rfl) ⟨1339928, by rfl⟩ : syracuseStep 1786571 = 2679857) B2679857
theorem B1786583 : Blo 1786094 1786583 := bstep (se 1 (by rfl) ⟨1339937, by rfl⟩ : syracuseStep 1786583 = 2679875) B2679875
theorem B3220183 : Blo 1786094 3220183 := bstep (se 1 (by rfl) ⟨2415137, by rfl⟩ : syracuseStep 3220183 = 4830275) B4830275
theorem B4022999 : Blo 1786094 4022999 := bstep (se 1 (by rfl) ⟨3017249, by rfl⟩ : syracuseStep 4022999 = 6034499) B6034499
theorem B6783709 : Blo 1786094 6783709 := bstep (se 3 (by rfl) ⟨1271945, by rfl⟩ : syracuseStep 6783709 = 2543891) B2543891
theorem B1786603 : Blo 1786094 1786603 := bstep (se 1 (by rfl) ⟨1339952, by rfl⟩ : syracuseStep 1786603 = 2679905) B2679905
theorem B1786615 : Blo 1786094 1786615 := bstep (se 1 (by rfl) ⟨1339961, by rfl⟩ : syracuseStep 1786615 = 2679923) B2679923
theorem B2679563 : Blo 1786094 2679563 := bstep (se 1 (by rfl) ⟨2009672, by rfl⟩ : syracuseStep 2679563 = 4019345) B4019345
theorem B1786635 : Blo 1786094 1786635 := bstep (se 1 (by rfl) ⟨1339976, by rfl⟩ : syracuseStep 1786635 = 2679953) B2679953
theorem B2679575 : Blo 1786094 2679575 := bstep (se 1 (by rfl) ⟨2009681, by rfl⟩ : syracuseStep 2679575 = 4019363) B4019363
theorem B1786647 : Blo 1786094 1786647 := bstep (se 1 (by rfl) ⟨1339985, by rfl⟩ : syracuseStep 1786647 = 2679971) B2679971
theorem B3220247 : Blo 1786094 3220247 := bstep (se 1 (by rfl) ⟨2415185, by rfl⟩ : syracuseStep 3220247 = 4830371) B4830371
theorem B2261783 : Blo 1786094 2261783 := bstep (se 1 (by rfl) ⟨1696337, by rfl⟩ : syracuseStep 2261783 = 3392675) B3392675
theorem B1786667 : Blo 1786094 1786667 := bstep (se 1 (by rfl) ⟨1340000, by rfl⟩ : syracuseStep 1786667 = 2680001) B2680001
theorem B1786679 : Blo 1786094 1786679 := bstep (se 1 (by rfl) ⟨1340009, by rfl⟩ : syracuseStep 1786679 = 2680019) B2680019
theorem B4522817 : Blo 1786094 4522817 := bstep (se 2 (by rfl) ⟨1696056, by rfl⟩ : syracuseStep 4522817 = 3392113) B3392113
theorem B1786699 : Blo 1786094 1786699 := bstep (se 1 (by rfl) ⟨1340024, by rfl⟩ : syracuseStep 1786699 = 2680049) B2680049
theorem B3818315 : Blo 1786094 3818315 := bstep (se 1 (by rfl) ⟨2863736, by rfl⟩ : syracuseStep 3818315 = 5727473) B5727473
theorem B1786711 : Blo 1786094 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B2679641 : Blo 1786094 2679641 := bstep (se 2 (by rfl) ⟨1004865, by rfl⟩ : syracuseStep 2679641 = 2009731) B2009731
theorem B13763429 : Blo 1786094 13763429 := bstep (se 4 (by rfl) ⟨1290321, by rfl⟩ : syracuseStep 13763429 = 2580643) B2580643
theorem B1786731 : Blo 1786094 1786731 := bstep (se 1 (by rfl) ⟨1340048, by rfl⟩ : syracuseStep 1786731 = 2680097) B2680097
theorem B3392371 : Blo 1786094 3392371 := bstep (se 1 (by rfl) ⟨2544278, by rfl⟩ : syracuseStep 3392371 = 5088557) B5088557
theorem B1786743 : Blo 1786094 1786743 := bstep (se 1 (by rfl) ⟨1340057, by rfl⟩ : syracuseStep 1786743 = 2680115) B2680115
theorem B1786763 : Blo 1786094 1786763 := bstep (se 1 (by rfl) ⟨1340072, by rfl⟩ : syracuseStep 1786763 = 2680145) B2680145
theorem B4023179 : Blo 1786094 4023179 := bstep (se 1 (by rfl) ⟨3017384, by rfl⟩ : syracuseStep 4023179 = 6034769) B6034769
theorem B1786775 : Blo 1786094 1786775 := bstep (se 1 (by rfl) ⟨1340081, by rfl⟩ : syracuseStep 1786775 = 2680163) B2680163
theorem B1786795 : Blo 1786094 1786795 := bstep (se 1 (by rfl) ⟨1340096, by rfl⟩ : syracuseStep 1786795 = 2680193) B2680193
theorem B1786807 : Blo 1786094 1786807 := bstep (se 1 (by rfl) ⟨1340105, by rfl⟩ : syracuseStep 1786807 = 2680211) B2680211
theorem B2679755 : Blo 1786094 2679755 := bstep (se 1 (by rfl) ⟨2009816, by rfl⟩ : syracuseStep 2679755 = 4019633) B4019633
theorem B1786827 : Blo 1786094 1786827 := bstep (se 1 (by rfl) ⟨1340120, by rfl⟩ : syracuseStep 1786827 = 2680241) B2680241
theorem B4129751 : Blo 1786094 4129751 := bstep (se 1 (by rfl) ⟨3097313, by rfl⟩ : syracuseStep 4129751 = 6194627) B6194627
theorem B2679767 : Blo 1786094 2679767 := bstep (se 1 (by rfl) ⟨2009825, by rfl⟩ : syracuseStep 2679767 = 4019651) B4019651
theorem B1786839 : Blo 1786094 1786839 := bstep (se 1 (by rfl) ⟨1340129, by rfl⟩ : syracuseStep 1786839 = 2680259) B2680259
theorem B1786859 : Blo 1786094 1786859 := bstep (se 1 (by rfl) ⟨1340144, by rfl⟩ : syracuseStep 1786859 = 2680289) B2680289
theorem B1786871 : Blo 1786094 1786871 := bstep (se 1 (by rfl) ⟨1340153, by rfl⟩ : syracuseStep 1786871 = 2680307) B2680307
theorem B1786891 : Blo 1786094 1786891 := bstep (se 1 (by rfl) ⟨1340168, by rfl⟩ : syracuseStep 1786891 = 2680337) B2680337
theorem B1786903 : Blo 1786094 1786903 := bstep (se 1 (by rfl) ⟨1340177, by rfl⟩ : syracuseStep 1786903 = 2680355) B2680355
theorem B2679833 : Blo 1786094 2679833 := bstep (se 2 (by rfl) ⟨1004937, by rfl⟩ : syracuseStep 2679833 = 2009875) B2009875
theorem B1786923 : Blo 1786094 1786923 := bstep (se 1 (by rfl) ⟨1340192, by rfl⟩ : syracuseStep 1786923 = 2680385) B2680385
theorem B1786935 : Blo 1786094 1786935 := bstep (se 1 (by rfl) ⟨1340201, by rfl⟩ : syracuseStep 1786935 = 2680403) B2680403
theorem B11609153 : Blo 1786094 11609153 := bstep (se 2 (by rfl) ⟨4353432, by rfl⟩ : syracuseStep 11609153 = 8706865) B8706865
theorem B1786955 : Blo 1786094 1786955 := bstep (se 1 (by rfl) ⟨1340216, by rfl⟩ : syracuseStep 1786955 = 2680433) B2680433
theorem B12231755 : Blo 1786094 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B1786967 : Blo 1786094 1786967 := bstep (se 1 (by rfl) ⟨1340225, by rfl⟩ : syracuseStep 1786967 = 2680451) B2680451
theorem B3392599 : Blo 1786094 3392599 := bstep (se 1 (by rfl) ⟨2544449, by rfl⟩ : syracuseStep 3392599 = 5088899) B5088899
theorem B1786987 : Blo 1786094 1786987 := bstep (se 1 (by rfl) ⟨1340240, by rfl⟩ : syracuseStep 1786987 = 2680481) B2680481
theorem B1786999 : Blo 1786094 1786999 := bstep (se 1 (by rfl) ⟨1340249, by rfl⟩ : syracuseStep 1786999 = 2680499) B2680499
theorem B2679947 : Blo 1786094 2679947 := bstep (se 1 (by rfl) ⟨2009960, by rfl⟩ : syracuseStep 2679947 = 4019921) B4019921
theorem B1787019 : Blo 1786094 1787019 := bstep (se 1 (by rfl) ⟨1340264, by rfl⟩ : syracuseStep 1787019 = 2680529) B2680529
theorem B2679959 : Blo 1786094 2679959 := bstep (se 1 (by rfl) ⟨2009969, by rfl⟩ : syracuseStep 2679959 = 4019939) B4019939
theorem B1787031 : Blo 1786094 1787031 := bstep (se 1 (by rfl) ⟨1340273, by rfl⟩ : syracuseStep 1787031 = 2680547) B2680547
theorem B1787051 : Blo 1786094 1787051 := bstep (se 1 (by rfl) ⟨1340288, by rfl⟩ : syracuseStep 1787051 = 2680577) B2680577
theorem B1787063 : Blo 1786094 1787063 := bstep (se 1 (by rfl) ⟨1340297, by rfl⟩ : syracuseStep 1787063 = 2680595) B2680595
theorem B3392705 : Blo 1786094 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B1787083 : Blo 1786094 1787083 := bstep (se 1 (by rfl) ⟨1340312, by rfl⟩ : syracuseStep 1787083 = 2680625) B2680625
theorem B1787095 : Blo 1786094 1787095 := bstep (se 1 (by rfl) ⟨1340321, by rfl⟩ : syracuseStep 1787095 = 2680643) B2680643
theorem B15262937 : Blo 1786094 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B2680025 : Blo 1786094 2680025 := bstep (se 2 (by rfl) ⟨1005009, by rfl⟩ : syracuseStep 2680025 = 2010019) B2010019
theorem B6030557 : Blo 1786094 6030557 := bstep (se 3 (by rfl) ⟨1130729, by rfl⟩ : syracuseStep 6030557 = 2261459) B2261459
theorem B1787115 : Blo 1786094 1787115 := bstep (se 1 (by rfl) ⟨1340336, by rfl⟩ : syracuseStep 1787115 = 2680673) B2680673
theorem B1787127 : Blo 1786094 1787127 := bstep (se 1 (by rfl) ⟨1340345, by rfl⟩ : syracuseStep 1787127 = 2680691) B2680691
theorem B1787147 : Blo 1786094 1787147 := bstep (se 1 (by rfl) ⟨1340360, by rfl⟩ : syracuseStep 1787147 = 2680721) B2680721
theorem B3015947 : Blo 1786094 3015947 := bstep (se 1 (by rfl) ⟨2261960, by rfl⟩ : syracuseStep 3015947 = 4523921) B4523921
theorem B8373527 : Blo 1786094 8373527 := bstep (se 1 (by rfl) ⟨6280145, by rfl⟩ : syracuseStep 8373527 = 12560291) B12560291
theorem B1787159 : Blo 1786094 1787159 := bstep (se 1 (by rfl) ⟨1340369, by rfl⟩ : syracuseStep 1787159 = 2680739) B2680739
theorem B1787179 : Blo 1786094 1787179 := bstep (se 1 (by rfl) ⟨1340384, by rfl⟩ : syracuseStep 1787179 = 2680769) B2680769
theorem B1811755 : Blo 1786094 1811755 := bstep (se 1 (by rfl) ⟨1358816, by rfl⟩ : syracuseStep 1811755 = 2717633) B2717633
theorem B1787191 : Blo 1786094 1787191 := bstep (se 1 (by rfl) ⟨1340393, by rfl⟩ : syracuseStep 1787191 = 2680787) B2680787
theorem B2680139 : Blo 1786094 2680139 := bstep (se 1 (by rfl) ⟨2010104, by rfl⟩ : syracuseStep 2680139 = 4020209) B4020209
theorem B1787211 : Blo 1786094 1787211 := bstep (se 1 (by rfl) ⟨1340408, by rfl⟩ : syracuseStep 1787211 = 2680817) B2680817
theorem B2680151 : Blo 1786094 2680151 := bstep (se 1 (by rfl) ⟨2010113, by rfl⟩ : syracuseStep 2680151 = 4020227) B4020227
theorem B1787223 : Blo 1786094 1787223 := bstep (se 1 (by rfl) ⟨1340417, by rfl⟩ : syracuseStep 1787223 = 2680835) B2680835
theorem B3392857 : Blo 1786094 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B1787243 : Blo 1786094 1787243 := bstep (se 1 (by rfl) ⟨1340432, by rfl⟩ : syracuseStep 1787243 = 2680865) B2680865
theorem B3622259 : Blo 1786094 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B1787255 : Blo 1786094 1787255 := bstep (se 1 (by rfl) ⟨1340441, by rfl⟩ : syracuseStep 1787255 = 2680883) B2680883
theorem B1787275 : Blo 1786094 1787275 := bstep (se 1 (by rfl) ⟨1340456, by rfl⟩ : syracuseStep 1787275 = 2680913) B2680913
theorem B3016075 : Blo 1786094 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B2942347 : Blo 1786094 2942347 := bstep (se 1 (by rfl) ⟨2206760, by rfl⟩ : syracuseStep 2942347 = 4413521) B4413521
theorem B1787287 : Blo 1786094 1787287 := bstep (se 1 (by rfl) ⟨1340465, by rfl⟩ : syracuseStep 1787287 = 2680931) B2680931
theorem B2147735 : Blo 1786094 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B2680217 : Blo 1786094 2680217 := bstep (se 2 (by rfl) ⟨1005081, by rfl⟩ : syracuseStep 2680217 = 2010163) B2010163
theorem B1787307 : Blo 1786094 1787307 := bstep (se 1 (by rfl) ⟨1340480, by rfl⟩ : syracuseStep 1787307 = 2680961) B2680961
theorem B1787319 : Blo 1786094 1787319 := bstep (se 1 (by rfl) ⟨1340489, by rfl⟩ : syracuseStep 1787319 = 2680979) B2680979
theorem B1787339 : Blo 1786094 1787339 := bstep (se 1 (by rfl) ⟨1340504, by rfl⟩ : syracuseStep 1787339 = 2681009) B2681009
theorem B1787351 : Blo 1786094 1787351 := bstep (se 1 (by rfl) ⟨1340513, by rfl⟩ : syracuseStep 1787351 = 2681027) B2681027
theorem B2262487 : Blo 1786094 2262487 := bstep (se 1 (by rfl) ⟨1696865, by rfl⟩ : syracuseStep 2262487 = 3393731) B3393731
theorem B1787371 : Blo 1786094 1787371 := bstep (se 1 (by rfl) ⟨1340528, by rfl⟩ : syracuseStep 1787371 = 2681057) B2681057
theorem B1787383 : Blo 1786094 1787383 := bstep (se 1 (by rfl) ⟨1340537, by rfl⟩ : syracuseStep 1787383 = 2681075) B2681075
theorem B2680331 : Blo 1786094 2680331 := bstep (se 1 (by rfl) ⟨2010248, by rfl⟩ : syracuseStep 2680331 = 4020497) B4020497
theorem B1787403 : Blo 1786094 1787403 := bstep (se 1 (by rfl) ⟨1340552, by rfl⟩ : syracuseStep 1787403 = 2681105) B2681105
theorem B2680343 : Blo 1786094 2680343 := bstep (se 1 (by rfl) ⟨2010257, by rfl⟩ : syracuseStep 2680343 = 4020515) B4020515
theorem B1787415 : Blo 1786094 1787415 := bstep (se 1 (by rfl) ⟨1340561, by rfl⟩ : syracuseStep 1787415 = 2681123) B2681123
theorem B3016217 : Blo 1786094 3016217 := bstep (se 2 (by rfl) ⟨1131081, by rfl⟩ : syracuseStep 3016217 = 2262163) B2262163
theorem B17655331 : Blo 1786094 17655331 := bstep (se 1 (by rfl) ⟨13241498, by rfl⟩ : syracuseStep 17655331 = 26482997) B26482997
theorem B1787435 : Blo 1786094 1787435 := bstep (se 1 (by rfl) ⟨1340576, by rfl⟩ : syracuseStep 1787435 = 2681153) B2681153
theorem B1787447 : Blo 1786094 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B1787467 : Blo 1786094 1787467 := bstep (se 1 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 1787467 = 2681201) B2681201
theorem B1787479 : Blo 1786094 1787479 := bstep (se 1 (by rfl) ⟨1340609, by rfl⟩ : syracuseStep 1787479 = 2681219) B2681219
theorem B2680409 : Blo 1786094 2680409 := bstep (se 2 (by rfl) ⟨1005153, by rfl⟩ : syracuseStep 2680409 = 2010307) B2010307
theorem B1787499 : Blo 1786094 1787499 := bstep (se 1 (by rfl) ⟨1340624, by rfl⟩ : syracuseStep 1787499 = 2681249) B2681249
theorem B1787511 : Blo 1786094 1787511 := bstep (se 1 (by rfl) ⟨1340633, by rfl⟩ : syracuseStep 1787511 = 2681267) B2681267
theorem B1787531 : Blo 1786094 1787531 := bstep (se 1 (by rfl) ⟨1340648, by rfl⟩ : syracuseStep 1787531 = 2681297) B2681297
theorem B1787543 : Blo 1786094 1787543 := bstep (se 1 (by rfl) ⟨1340657, by rfl⟩ : syracuseStep 1787543 = 2681315) B2681315
theorem B3016345 : Blo 1786094 3016345 := bstep (se 2 (by rfl) ⟨1131129, by rfl⟩ : syracuseStep 3016345 = 2262259) B2262259
theorem B1787563 : Blo 1786094 1787563 := bstep (se 1 (by rfl) ⟨1340672, by rfl⟩ : syracuseStep 1787563 = 2681345) B2681345
theorem B1787575 : Blo 1786094 1787575 := bstep (se 1 (by rfl) ⟨1340681, by rfl⟩ : syracuseStep 1787575 = 2681363) B2681363
theorem B2680523 : Blo 1786094 2680523 := bstep (se 1 (by rfl) ⟨2010392, by rfl⟩ : syracuseStep 2680523 = 4020785) B4020785
theorem B1787595 : Blo 1786094 1787595 := bstep (se 1 (by rfl) ⟨1340696, by rfl⟩ : syracuseStep 1787595 = 2681393) B2681393
theorem B2680535 : Blo 1786094 2680535 := bstep (se 1 (by rfl) ⟨2010401, by rfl⟩ : syracuseStep 2680535 = 4020803) B4020803
theorem B1787607 : Blo 1786094 1787607 := bstep (se 1 (by rfl) ⟨1340705, by rfl⟩ : syracuseStep 1787607 = 2681411) B2681411
theorem B1787627 : Blo 1786094 1787627 := bstep (se 1 (by rfl) ⟨1340720, by rfl⟩ : syracuseStep 1787627 = 2681441) B2681441
theorem B1787639 : Blo 1786094 1787639 := bstep (se 1 (by rfl) ⟨1340729, by rfl⟩ : syracuseStep 1787639 = 2681459) B2681459
theorem B15271685 : Blo 1786094 15271685 := bstep (se 4 (by rfl) ⟨1431720, by rfl⟩ : syracuseStep 15271685 = 2863441) B2863441
theorem B1787659 : Blo 1786094 1787659 := bstep (se 1 (by rfl) ⟨1340744, by rfl⟩ : syracuseStep 1787659 = 2681489) B2681489
theorem B1787671 : Blo 1786094 1787671 := bstep (se 1 (by rfl) ⟨1340753, by rfl⟩ : syracuseStep 1787671 = 2681507) B2681507
theorem B4130585 : Blo 1786094 4130585 := bstep (se 2 (by rfl) ⟨1548969, by rfl⟩ : syracuseStep 4130585 = 3097939) B3097939
theorem B2680601 : Blo 1786094 2680601 := bstep (se 2 (by rfl) ⟨1005225, by rfl⟩ : syracuseStep 2680601 = 2010451) B2010451
theorem B1787691 : Blo 1786094 1787691 := bstep (se 1 (by rfl) ⟨1340768, by rfl⟩ : syracuseStep 1787691 = 2681537) B2681537
theorem B1787703 : Blo 1786094 1787703 := bstep (se 1 (by rfl) ⟨1340777, by rfl⟩ : syracuseStep 1787703 = 2681555) B2681555
theorem B7243595 : Blo 1786094 7243595 := bstep (se 1 (by rfl) ⟨5432696, by rfl⟩ : syracuseStep 7243595 = 10865393) B10865393
theorem B1787723 : Blo 1786094 1787723 := bstep (se 1 (by rfl) ⟨1340792, by rfl⟩ : syracuseStep 1787723 = 2681585) B2681585
theorem B1787735 : Blo 1786094 1787735 := bstep (se 1 (by rfl) ⟨1340801, by rfl⟩ : syracuseStep 1787735 = 2681603) B2681603
theorem B12887909 : Blo 1786094 12887909 := bstep (se 4 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 12887909 = 2416483) B2416483
theorem B1787755 : Blo 1786094 1787755 := bstep (se 1 (by rfl) ⟨1340816, by rfl⟩ : syracuseStep 1787755 = 2681633) B2681633
theorem B1787767 : Blo 1786094 1787767 := bstep (se 1 (by rfl) ⟨1340825, by rfl⟩ : syracuseStep 1787767 = 2681651) B2681651
theorem B2680715 : Blo 1786094 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B1787787 : Blo 1786094 1787787 := bstep (se 1 (by rfl) ⟨1340840, by rfl⟩ : syracuseStep 1787787 = 2681681) B2681681
theorem B2680727 : Blo 1786094 2680727 := bstep (se 1 (by rfl) ⟨2010545, by rfl⟩ : syracuseStep 2680727 = 4021091) B4021091
theorem B1787799 : Blo 1786094 1787799 := bstep (se 1 (by rfl) ⟨1340849, by rfl⟩ : syracuseStep 1787799 = 2681699) B2681699
theorem B1787819 : Blo 1786094 1787819 := bstep (se 1 (by rfl) ⟨1340864, by rfl⟩ : syracuseStep 1787819 = 2681729) B2681729
theorem B1787831 : Blo 1786094 1787831 := bstep (se 1 (by rfl) ⟨1340873, by rfl⟩ : syracuseStep 1787831 = 2681747) B2681747
theorem B1787851 : Blo 1786094 1787851 := bstep (se 1 (by rfl) ⟨1340888, by rfl⟩ : syracuseStep 1787851 = 2681777) B2681777
theorem B1787863 : Blo 1786094 1787863 := bstep (se 1 (by rfl) ⟨1340897, by rfl⟩ : syracuseStep 1787863 = 2681795) B2681795
theorem B6784985 : Blo 1786094 6784985 := bstep (se 2 (by rfl) ⟨2544369, by rfl⟩ : syracuseStep 6784985 = 5088739) B5088739
theorem B2680793 : Blo 1786094 2680793 := bstep (se 2 (by rfl) ⟨1005297, by rfl⟩ : syracuseStep 2680793 = 2010595) B2010595
theorem B1787883 : Blo 1786094 1787883 := bstep (se 1 (by rfl) ⟨1340912, by rfl⟩ : syracuseStep 1787883 = 2681825) B2681825
theorem B1787895 : Blo 1786094 1787895 := bstep (se 1 (by rfl) ⟨1340921, by rfl⟩ : syracuseStep 1787895 = 2681843) B2681843
theorem B1787915 : Blo 1786094 1787915 := bstep (se 1 (by rfl) ⟨1340936, by rfl⟩ : syracuseStep 1787915 = 2681873) B2681873
theorem B1787927 : Blo 1786094 1787927 := bstep (se 1 (by rfl) ⟨1340945, by rfl⟩ : syracuseStep 1787927 = 2681891) B2681891
theorem B1787947 : Blo 1786094 1787947 := bstep (se 1 (by rfl) ⟨1340960, by rfl⟩ : syracuseStep 1787947 = 2681921) B2681921
theorem B5089331 : Blo 1786094 5089331 := bstep (se 1 (by rfl) ⟨3816998, by rfl⟩ : syracuseStep 5089331 = 7633997) B7633997
theorem B4524083 : Blo 1786094 4524083 := bstep (se 1 (by rfl) ⟨3393062, by rfl⟩ : syracuseStep 4524083 = 6786125) B6786125
theorem B1787959 : Blo 1786094 1787959 := bstep (se 1 (by rfl) ⟨1340969, by rfl⟩ : syracuseStep 1787959 = 2681939) B2681939
theorem B5089355 : Blo 1786094 5089355 := bstep (se 1 (by rfl) ⟨3817016, by rfl⟩ : syracuseStep 5089355 = 7634033) B7634033
theorem B2680907 : Blo 1786094 2680907 := bstep (se 1 (by rfl) ⟨2010680, by rfl⟩ : syracuseStep 2680907 = 4021361) B4021361
theorem B1787979 : Blo 1786094 1787979 := bstep (se 1 (by rfl) ⟨1340984, by rfl⟩ : syracuseStep 1787979 = 2681969) B2681969
theorem B2680919 : Blo 1786094 2680919 := bstep (se 1 (by rfl) ⟨2010689, by rfl⟩ : syracuseStep 2680919 = 4021379) B4021379
theorem B1787991 : Blo 1786094 1787991 := bstep (se 1 (by rfl) ⟨1340993, by rfl⟩ : syracuseStep 1787991 = 2681987) B2681987
theorem B1788011 : Blo 1786094 1788011 := bstep (se 1 (by rfl) ⟨1341008, by rfl⟩ : syracuseStep 1788011 = 2682017) B2682017
theorem B1788023 : Blo 1786094 1788023 := bstep (se 1 (by rfl) ⟨1341017, by rfl⟩ : syracuseStep 1788023 = 2682035) B2682035
theorem B1788043 : Blo 1786094 1788043 := bstep (se 1 (by rfl) ⟨1341032, by rfl⟩ : syracuseStep 1788043 = 2682065) B2682065
theorem B1788055 : Blo 1786094 1788055 := bstep (se 1 (by rfl) ⟨1341041, by rfl⟩ : syracuseStep 1788055 = 2682083) B2682083
theorem B2680985 : Blo 1786094 2680985 := bstep (se 2 (by rfl) ⟨1005369, by rfl⟩ : syracuseStep 2680985 = 2010739) B2010739
theorem B1788075 : Blo 1786094 1788075 := bstep (se 1 (by rfl) ⟨1341056, by rfl⟩ : syracuseStep 1788075 = 2682113) B2682113
theorem B1788087 : Blo 1786094 1788087 := bstep (se 1 (by rfl) ⟨1341065, by rfl⟩ : syracuseStep 1788087 = 2682131) B2682131
theorem B3016919 : Blo 1786094 3016919 := bstep (se 1 (by rfl) ⟨2262689, by rfl⟩ : syracuseStep 3016919 = 4525379) B4525379
theorem B13576409 : Blo 1786094 13576409 := bstep (se 2 (by rfl) ⟨5091153, by rfl⟩ : syracuseStep 13576409 = 10182307) B10182307
theorem B2681099 : Blo 1786094 2681099 := bstep (se 1 (by rfl) ⟨2010824, by rfl⟩ : syracuseStep 2681099 = 4021649) B4021649
theorem B2681111 : Blo 1786094 2681111 := bstep (se 1 (by rfl) ⟨2010833, by rfl⟩ : syracuseStep 2681111 = 4021667) B4021667
theorem B6031691 : Blo 1786094 6031691 := bstep (se 1 (by rfl) ⟨4523768, by rfl⟩ : syracuseStep 6031691 = 9047537) B9047537
theorem B3017047 : Blo 1786094 3017047 := bstep (se 1 (by rfl) ⟨2262785, by rfl⟩ : syracuseStep 3017047 = 4525571) B4525571
theorem B2681177 : Blo 1786094 2681177 := bstep (se 2 (by rfl) ⟨1005441, by rfl⟩ : syracuseStep 2681177 = 2010883) B2010883
theorem B3623297 : Blo 1786094 3623297 := bstep (se 2 (by rfl) ⟨1358736, by rfl⟩ : syracuseStep 3623297 = 2717473) B2717473
theorem B9046403 : Blo 1786094 9046403 := bstep (se 1 (by rfl) ⟨6784802, by rfl⟩ : syracuseStep 9046403 = 13569605) B13569605
theorem B7637399 : Blo 1786094 7637399 := bstep (se 1 (by rfl) ⟨5728049, by rfl⟩ : syracuseStep 7637399 = 11456099) B11456099
theorem B2009515 : Blo 1786094 2009515 := bstep (se 1 (by rfl) ⟨1507136, by rfl⟩ : syracuseStep 2009515 = 3014273) B3014273
theorem B23218609 : Blo 1786094 23218609 := bstep (se 2 (by rfl) ⟨8706978, by rfl⟩ : syracuseStep 23218609 = 17413957) B17413957
theorem B2681291 : Blo 1786094 2681291 := bstep (se 1 (by rfl) ⟨2010968, by rfl⟩ : syracuseStep 2681291 = 4021937) B4021937
theorem B5884363 : Blo 1786094 5884363 := bstep (se 1 (by rfl) ⟨4413272, by rfl⟩ : syracuseStep 5884363 = 8826545) B8826545
theorem B2681303 : Blo 1786094 2681303 := bstep (se 1 (by rfl) ⟨2010977, by rfl⟩ : syracuseStep 2681303 = 4021955) B4021955
theorem B7629335 : Blo 1786094 7629335 := bstep (se 1 (by rfl) ⟨5722001, by rfl⟩ : syracuseStep 7629335 = 11444003) B11444003
theorem B2009623 : Blo 1786094 2009623 := bstep (se 1 (by rfl) ⟨1507217, by rfl⟩ : syracuseStep 2009623 = 3014435) B3014435
theorem B2681369 : Blo 1786094 2681369 := bstep (se 2 (by rfl) ⟨1005513, by rfl⟩ : syracuseStep 2681369 = 2011027) B2011027
theorem B4524619 : Blo 1786094 4524619 := bstep (se 1 (by rfl) ⟨3393464, by rfl⟩ : syracuseStep 4524619 = 6786929) B6786929
theorem B6031961 : Blo 1786094 6031961 := bstep (se 2 (by rfl) ⟨2261985, by rfl⟩ : syracuseStep 6031961 = 4523971) B4523971
theorem B3394163 : Blo 1786094 3394163 := bstep (se 1 (by rfl) ⟨2545622, by rfl⟩ : syracuseStep 3394163 = 5091245) B5091245
theorem B24447619 : Blo 1786094 24447619 := bstep (se 1 (by rfl) ⟨18335714, by rfl⟩ : syracuseStep 24447619 = 36671429) B36671429
theorem B2681483 : Blo 1786094 2681483 := bstep (se 1 (by rfl) ⟨2011112, by rfl⟩ : syracuseStep 2681483 = 4022225) B4022225
theorem B2681495 : Blo 1786094 2681495 := bstep (se 1 (by rfl) ⟨2011121, by rfl⟩ : syracuseStep 2681495 = 4022243) B4022243
theorem B2009803 : Blo 1786094 2009803 := bstep (se 1 (by rfl) ⟨1507352, by rfl⟩ : syracuseStep 2009803 = 3014705) B3014705
theorem B4524761 : Blo 1786094 4524761 := bstep (se 2 (by rfl) ⟨1696785, by rfl⟩ : syracuseStep 4524761 = 3393571) B3393571
theorem B2681561 : Blo 1786094 2681561 := bstep (se 2 (by rfl) ⟨1005585, by rfl⟩ : syracuseStep 2681561 = 2011171) B2011171
theorem B3394315 : Blo 1786094 3394315 := bstep (se 1 (by rfl) ⟨2545736, by rfl⟩ : syracuseStep 3394315 = 5091473) B5091473
theorem B2009911 : Blo 1786094 2009911 := bstep (se 1 (by rfl) ⟨1507433, by rfl⟩ : syracuseStep 2009911 = 3014867) B3014867
theorem B2681675 : Blo 1786094 2681675 := bstep (se 1 (by rfl) ⟨2011256, by rfl⟩ : syracuseStep 2681675 = 4022513) B4022513
theorem B2681687 : Blo 1786094 2681687 := bstep (se 1 (by rfl) ⟨2011265, by rfl⟩ : syracuseStep 2681687 = 4022531) B4022531
theorem B6441821 : Blo 1786094 6441821 := bstep (se 3 (by rfl) ⟨1207841, by rfl⟩ : syracuseStep 6441821 = 2415683) B2415683
theorem B5090141 : Blo 1786094 5090141 := bstep (se 3 (by rfl) ⟨954401, by rfl⟩ : syracuseStep 5090141 = 1908803) B1908803
theorem B2861975 : Blo 1786094 2861975 := bstep (se 1 (by rfl) ⟨2146481, by rfl⟩ : syracuseStep 2861975 = 4292963) B4292963
theorem B2681753 : Blo 1786094 2681753 := bstep (se 2 (by rfl) ⟨1005657, by rfl⟩ : syracuseStep 2681753 = 2011315) B2011315
theorem B2010091 : Blo 1786094 2010091 := bstep (se 1 (by rfl) ⟨1507568, by rfl⟩ : syracuseStep 2010091 = 3015137) B3015137
theorem B2681867 : Blo 1786094 2681867 := bstep (se 1 (by rfl) ⟨2011400, by rfl⟩ : syracuseStep 2681867 = 4022801) B4022801
theorem B2681879 : Blo 1786094 2681879 := bstep (se 1 (by rfl) ⟨2011409, by rfl⟩ : syracuseStep 2681879 = 4022819) B4022819
theorem B2010199 : Blo 1786094 2010199 := bstep (se 1 (by rfl) ⟨1507649, by rfl⟩ : syracuseStep 2010199 = 3015299) B3015299
theorem B2681945 : Blo 1786094 2681945 := bstep (se 2 (by rfl) ⟨1005729, by rfl⟩ : syracuseStep 2681945 = 2011459) B2011459
theorem B2682059 : Blo 1786094 2682059 := bstep (se 1 (by rfl) ⟨2011544, by rfl⟩ : syracuseStep 2682059 = 4023089) B4023089
theorem B2682071 : Blo 1786094 2682071 := bstep (se 1 (by rfl) ⟨2011553, by rfl⟩ : syracuseStep 2682071 = 4023107) B4023107
theorem B2010379 : Blo 1786094 2010379 := bstep (se 1 (by rfl) ⟨1507784, by rfl⟩ : syracuseStep 2010379 = 3015569) B3015569
theorem B10317073 : Blo 1786094 10317073 := bstep (se 2 (by rfl) ⟨3868902, by rfl⟩ : syracuseStep 10317073 = 7737805) B7737805
theorem B6032663 : Blo 1786094 6032663 := bstep (se 1 (by rfl) ⟨4524497, by rfl⟩ : syracuseStep 6032663 = 9048995) B9048995
theorem B2682137 : Blo 1786094 2682137 := bstep (se 2 (by rfl) ⟨1005801, by rfl⟩ : syracuseStep 2682137 = 2011603) B2011603
theorem B2010487 : Blo 1786094 2010487 := bstep (se 1 (by rfl) ⟨1507865, by rfl⟩ : syracuseStep 2010487 = 3015731) B3015731
theorem B2862487 : Blo 1786094 2862487 := bstep (se 1 (by rfl) ⟨2146865, by rfl⟩ : syracuseStep 2862487 = 4293731) B4293731
theorem B28986893 : Blo 1786094 28986893 := bstep (se 3 (by rfl) ⟨5435042, by rfl⟩ : syracuseStep 28986893 = 10870085) B10870085
theorem B4525591 : Blo 1786094 4525591 := bstep (se 1 (by rfl) ⟨3394193, by rfl⟩ : syracuseStep 4525591 = 6788387) B6788387
theorem B2010667 : Blo 1786094 2010667 := bstep (se 1 (by rfl) ⟨1508000, by rfl⟩ : syracuseStep 2010667 = 3016001) B3016001
theorem B6786611 : Blo 1786094 6786611 := bstep (se 1 (by rfl) ⟨5089958, by rfl⟩ : syracuseStep 6786611 = 10179917) B10179917
theorem B6786625 : Blo 1786094 6786625 := bstep (se 2 (by rfl) ⟨2544984, by rfl⟩ : syracuseStep 6786625 = 5089969) B5089969
theorem B2010775 : Blo 1786094 2010775 := bstep (se 1 (by rfl) ⟨1508081, by rfl⟩ : syracuseStep 2010775 = 3016163) B3016163
theorem B8589017 : Blo 1786094 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B6033203 : Blo 1786094 6033203 := bstep (se 1 (by rfl) ⟨4524902, by rfl⟩ : syracuseStep 6033203 = 9049805) B9049805
theorem B2010955 : Blo 1786094 2010955 := bstep (se 1 (by rfl) ⟨1508216, by rfl⟩ : syracuseStep 2010955 = 3016433) B3016433
theorem B2543447 : Blo 1786094 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B10874755 : Blo 1786094 10874755 := bstep (se 1 (by rfl) ⟨8156066, by rfl⟩ : syracuseStep 10874755 = 16312133) B16312133
theorem B2011063 : Blo 1786094 2011063 := bstep (se 1 (by rfl) ⟨1508297, by rfl⟩ : syracuseStep 2011063 = 3016595) B3016595
theorem B4526027 : Blo 1786094 4526027 := bstep (se 1 (by rfl) ⟨3394520, by rfl⟩ : syracuseStep 4526027 = 6789041) B6789041
theorem B28987409 : Blo 1786094 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B6033473 : Blo 1786094 6033473 := bstep (se 2 (by rfl) ⟨2262552, by rfl⟩ : syracuseStep 6033473 = 4525105) B4525105
theorem B2011243 : Blo 1786094 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B4075699 : Blo 1786094 4075699 := bstep (se 1 (by rfl) ⟨3056774, by rfl⟩ : syracuseStep 4075699 = 6113549) B6113549
theorem B2863307 : Blo 1786094 2863307 := bstep (se 1 (by rfl) ⟨2147480, by rfl⟩ : syracuseStep 2863307 = 4294961) B4294961
theorem B2011351 : Blo 1786094 2011351 := bstep (se 1 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 2011351 = 3017027) B3017027
theorem B10178891 : Blo 1786094 10178891 := bstep (se 1 (by rfl) ⟨7634168, by rfl⟩ : syracuseStep 10178891 = 15268337) B15268337
theorem B4075865 : Blo 1786094 4075865 := bstep (se 2 (by rfl) ⟨1528449, by rfl⟩ : syracuseStep 4075865 = 3056899) B3056899
theorem B1937783 : Blo 1786094 1937783 := bstep (se 1 (by rfl) ⟨1453337, by rfl⟩ : syracuseStep 1937783 = 2906675) B2906675
theorem B2011531 : Blo 1786094 2011531 := bstep (se 1 (by rfl) ⟨1508648, by rfl⟩ : syracuseStep 2011531 = 3017297) B3017297
theorem B13570577 : Blo 1786094 13570577 := bstep (se 2 (by rfl) ⟨5088966, by rfl⟩ : syracuseStep 13570577 = 10177933) B10177933
theorem B7631435 : Blo 1786094 7631435 := bstep (se 1 (by rfl) ⟨5723576, by rfl⟩ : syracuseStep 7631435 = 11447153) B11447153
theorem B6034013 : Blo 1786094 6034013 := bstep (se 3 (by rfl) ⟨1131377, by rfl⟩ : syracuseStep 6034013 = 2262755) B2262755
theorem B9663077 : Blo 1786094 9663077 := bstep (se 4 (by rfl) ⟨905913, by rfl⟩ : syracuseStep 9663077 = 1811827) B1811827
theorem B7738001 : Blo 1786094 7738001 := bstep (se 2 (by rfl) ⟨2901750, by rfl⟩ : syracuseStep 7738001 = 5803501) B5803501
theorem B4018841 : Blo 1786094 4018841 := bstep (se 2 (by rfl) ⟨1507065, by rfl⟩ : syracuseStep 4018841 = 3014131) B3014131
theorem B16528049 : Blo 1786094 16528049 := bstep (se 2 (by rfl) ⟨6198018, by rfl⟩ : syracuseStep 16528049 = 12396037) B12396037
theorem B4018931 : Blo 1786094 4018931 := bstep (se 1 (by rfl) ⟨3014198, by rfl⟩ : syracuseStep 4018931 = 6028397) B6028397
theorem B4018967 : Blo 1786094 4018967 := bstep (se 1 (by rfl) ⟨3014225, by rfl⟩ : syracuseStep 4018967 = 6028451) B6028451
theorem B5804993 : Blo 1786094 5804993 := bstep (se 2 (by rfl) ⟨2176872, by rfl⟩ : syracuseStep 5804993 = 4353745) B4353745
theorem B4019147 : Blo 1786094 4019147 := bstep (se 1 (by rfl) ⟨3014360, by rfl⟩ : syracuseStep 4019147 = 6028721) B6028721
theorem B4019201 : Blo 1786094 4019201 := bstep (se 2 (by rfl) ⟨1507200, by rfl⟩ : syracuseStep 4019201 = 3014401) B3014401
theorem B65205323 : Blo 1786094 65205323 := bstep (se 1 (by rfl) ⟨48903992, by rfl⟩ : syracuseStep 65205323 = 97807985) B97807985
theorem B15275101 : Blo 1786094 15275101 := bstep (se 3 (by rfl) ⟨2864081, by rfl⟩ : syracuseStep 15275101 = 5728163) B5728163
theorem B52933783 : Blo 1786094 52933783 := bstep (se 1 (by rfl) ⟨39700337, by rfl⟩ : syracuseStep 52933783 = 79400675) B79400675
theorem B4019417 : Blo 1786094 4019417 := bstep (se 2 (by rfl) ⟨1507281, by rfl⟩ : syracuseStep 4019417 = 3014563) B3014563
theorem B4019507 : Blo 1786094 4019507 := bstep (se 1 (by rfl) ⟨3014630, by rfl⟩ : syracuseStep 4019507 = 6029261) B6029261
theorem B4019543 : Blo 1786094 4019543 := bstep (se 1 (by rfl) ⟨3014657, by rfl⟩ : syracuseStep 4019543 = 6029315) B6029315
theorem B13563287 : Blo 1786094 13563287 := bstep (se 1 (by rfl) ⟨10172465, by rfl⟩ : syracuseStep 13563287 = 20344931) B20344931
theorem B6788555 : Blo 1786094 6788555 := bstep (se 1 (by rfl) ⟨5091416, by rfl⟩ : syracuseStep 6788555 = 10182833) B10182833
theorem B6788569 : Blo 1786094 6788569 := bstep (se 2 (by rfl) ⟨2545713, by rfl⟩ : syracuseStep 6788569 = 5091427) B5091427
theorem B4019723 : Blo 1786094 4019723 := bstep (se 1 (by rfl) ⟨3014792, by rfl⟩ : syracuseStep 4019723 = 6029585) B6029585
theorem B6116887 : Blo 1786094 6116887 := bstep (se 1 (by rfl) ⟨4587665, by rfl⟩ : syracuseStep 6116887 = 9175331) B9175331
theorem B4019777 : Blo 1786094 4019777 := bstep (se 2 (by rfl) ⟨1507416, by rfl⟩ : syracuseStep 4019777 = 3014833) B3014833
theorem B43488899 : Blo 1786094 43488899 := bstep (se 1 (by rfl) ⟨32616674, by rfl⟩ : syracuseStep 43488899 = 65233349) B65233349
theorem B6616849 : Blo 1786094 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B4019993 : Blo 1786094 4019993 := bstep (se 2 (by rfl) ⟨1507497, by rfl⟩ : syracuseStep 4019993 = 3014995) B3014995
theorem B44046179 : Blo 1786094 44046179 := bstep (se 1 (by rfl) ⟨33034634, by rfl⟩ : syracuseStep 44046179 = 66069269) B66069269
theorem B4020083 : Blo 1786094 4020083 := bstep (se 1 (by rfl) ⟨3015062, by rfl⟩ : syracuseStep 4020083 = 6030125) B6030125
theorem B4020119 : Blo 1786094 4020119 := bstep (se 1 (by rfl) ⟨3015089, by rfl⟩ : syracuseStep 4020119 = 6030179) B6030179
theorem B9656243 : Blo 1786094 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B17168345 : Blo 1786094 17168345 := bstep (se 2 (by rfl) ⟨6438129, by rfl⟩ : syracuseStep 17168345 = 12876259) B12876259
theorem B22894609 : Blo 1786094 22894609 := bstep (se 2 (by rfl) ⟨8585478, by rfl⟩ : syracuseStep 22894609 = 17170957) B17170957
theorem B9050129 : Blo 1786094 9050129 := bstep (se 2 (by rfl) ⟨3393798, by rfl⟩ : syracuseStep 9050129 = 6787597) B6787597
theorem B3438617 : Blo 1786094 3438617 := bstep (se 2 (by rfl) ⟨1289481, by rfl⟩ : syracuseStep 3438617 = 2578963) B2578963
theorem B4773953 : Blo 1786094 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B4020299 : Blo 1786094 4020299 := bstep (se 1 (by rfl) ⟨3015224, by rfl⟩ : syracuseStep 4020299 = 6030449) B6030449
theorem B4020353 : Blo 1786094 4020353 := bstep (se 2 (by rfl) ⟨1507632, by rfl⟩ : syracuseStep 4020353 = 3015265) B3015265
theorem B7633075 : Blo 1786094 7633075 := bstep (se 1 (by rfl) ⟨5724806, by rfl⟩ : syracuseStep 7633075 = 11449613) B11449613
theorem B9050291 : Blo 1786094 9050291 := bstep (se 1 (by rfl) ⟨6787718, by rfl⟩ : syracuseStep 9050291 = 13575437) B13575437
theorem B2717911 : Blo 1786094 2717911 := bstep (se 1 (by rfl) ⟨2038433, by rfl⟩ : syracuseStep 2717911 = 4076867) B4076867
theorem B11450585 : Blo 1786094 11450585 := bstep (se 2 (by rfl) ⟨4293969, by rfl⟩ : syracuseStep 11450585 = 8587939) B8587939
theorem B4020569 : Blo 1786094 4020569 := bstep (se 2 (by rfl) ⟨1507713, by rfl⟩ : syracuseStep 4020569 = 3015427) B3015427
theorem B4020659 : Blo 1786094 4020659 := bstep (se 1 (by rfl) ⟨3015494, by rfl⟩ : syracuseStep 4020659 = 6030989) B6030989
theorem B4020695 : Blo 1786094 4020695 := bstep (se 1 (by rfl) ⟨3015521, by rfl⟩ : syracuseStep 4020695 = 6031043) B6031043
theorem B3815923 : Blo 1786094 3815923 := bstep (se 1 (by rfl) ⟨2861942, by rfl⟩ : syracuseStep 3815923 = 5723885) B5723885
theorem B10173059 : Blo 1786094 10173059 := bstep (se 1 (by rfl) ⟨7629794, by rfl⟩ : syracuseStep 10173059 = 15259589) B15259589
theorem B4020875 : Blo 1786094 4020875 := bstep (se 1 (by rfl) ⟨3015656, by rfl⟩ : syracuseStep 4020875 = 6031313) B6031313
theorem B15260339 : Blo 1786094 15260339 := bstep (se 1 (by rfl) ⟨11445254, by rfl⟩ : syracuseStep 15260339 = 22890509) B22890509
theorem B4020929 : Blo 1786094 4020929 := bstep (se 2 (by rfl) ⟨1507848, by rfl⟩ : syracuseStep 4020929 = 3015697) B3015697
theorem B7633709 : Blo 1786094 7633709 := bstep (se 3 (by rfl) ⟨1431320, by rfl⟩ : syracuseStep 7633709 = 2862641) B2862641
theorem B3816281 : Blo 1786094 3816281 := bstep (se 2 (by rfl) ⟨1431105, by rfl⟩ : syracuseStep 3816281 = 2862211) B2862211
theorem B9042839 : Blo 1786094 9042839 := bstep (se 1 (by rfl) ⟨6782129, by rfl⟩ : syracuseStep 9042839 = 13564259) B13564259
theorem B4021145 : Blo 1786094 4021145 := bstep (se 2 (by rfl) ⟨1507929, by rfl⟩ : syracuseStep 4021145 = 3015859) B3015859
theorem B6028235 : Blo 1786094 6028235 := bstep (se 1 (by rfl) ⟨4521176, by rfl⟩ : syracuseStep 6028235 = 9042353) B9042353
theorem B4021235 : Blo 1786094 4021235 := bstep (se 1 (by rfl) ⟨3015926, by rfl⟩ : syracuseStep 4021235 = 6031853) B6031853
theorem B9796625 : Blo 1786094 9796625 := bstep (se 2 (by rfl) ⟨3673734, by rfl⟩ : syracuseStep 9796625 = 7347469) B7347469
theorem B4021271 : Blo 1786094 4021271 := bstep (se 1 (by rfl) ⟨3015953, by rfl⟩ : syracuseStep 4021271 = 6031907) B6031907
theorem B4021451 : Blo 1786094 4021451 := bstep (se 1 (by rfl) ⟨3016088, by rfl⟩ : syracuseStep 4021451 = 6032177) B6032177
theorem B6028505 : Blo 1786094 6028505 := bstep (se 2 (by rfl) ⟨2260689, by rfl⟩ : syracuseStep 6028505 = 4521379) B4521379
theorem B4021505 : Blo 1786094 4021505 := bstep (se 2 (by rfl) ⟨1508064, by rfl⟩ : syracuseStep 4021505 = 3016129) B3016129
theorem B45808901 : Blo 1786094 45808901 := bstep (se 4 (by rfl) ⟨4294584, by rfl⟩ : syracuseStep 45808901 = 8589169) B8589169
theorem B23223557 : Blo 1786094 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B1908055 : Blo 1786094 1908055 := bstep (se 1 (by rfl) ⟨1431041, by rfl⟩ : syracuseStep 1908055 = 2862083) B2862083
theorem B3390913 : Blo 1786094 3390913 := bstep (se 2 (by rfl) ⟨1271592, by rfl⟩ : syracuseStep 3390913 = 2543185) B2543185
theorem B6438361 : Blo 1786094 6438361 := bstep (se 2 (by rfl) ⟨2414385, by rfl⟩ : syracuseStep 6438361 = 4828771) B4828771
theorem B4021721 : Blo 1786094 4021721 := bstep (se 2 (by rfl) ⟨1508145, by rfl⟩ : syracuseStep 4021721 = 3016291) B3016291
theorem B1908235 : Blo 1786094 1908235 := bstep (se 1 (by rfl) ⟨1431176, by rfl⟩ : syracuseStep 1908235 = 2862353) B2862353
theorem B4021811 : Blo 1786094 4021811 := bstep (se 1 (by rfl) ⟨3016358, by rfl⟩ : syracuseStep 4021811 = 6032717) B6032717
theorem B3014219 : Blo 1786094 3014219 := bstep (se 1 (by rfl) ⟨2260664, by rfl⟩ : syracuseStep 3014219 = 4521329) B4521329
theorem B4021847 : Blo 1786094 4021847 := bstep (se 1 (by rfl) ⟨3016385, by rfl⟩ : syracuseStep 4021847 = 6032771) B6032771
theorem B2416267 : Blo 1786094 2416267 := bstep (se 1 (by rfl) ⟨1812200, by rfl⟩ : syracuseStep 2416267 = 3624401) B3624401
theorem B2145943 : Blo 1786094 2145943 := bstep (se 1 (by rfl) ⟨1609457, by rfl⟩ : syracuseStep 2145943 = 3218915) B3218915
theorem B5086871 : Blo 1786094 5086871 := bstep (se 1 (by rfl) ⟨3815153, by rfl⟩ : syracuseStep 5086871 = 7630307) B7630307
theorem B6110923 : Blo 1786094 6110923 := bstep (se 1 (by rfl) ⟨4583192, by rfl⟩ : syracuseStep 6110923 = 9166385) B9166385
theorem B3014347 : Blo 1786094 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B6782723 : Blo 1786094 6782723 := bstep (se 1 (by rfl) ⟨5087042, by rfl⟩ : syracuseStep 6782723 = 10174085) B10174085
theorem B4022027 : Blo 1786094 4022027 := bstep (se 1 (by rfl) ⟨3016520, by rfl⟩ : syracuseStep 4022027 = 6033041) B6033041
theorem B6782737 : Blo 1786094 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B4022081 : Blo 1786094 4022081 := bstep (se 2 (by rfl) ⟨1508280, by rfl⟩ : syracuseStep 4022081 = 3016561) B3016561
theorem B2260811 : Blo 1786094 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B3014489 : Blo 1786094 3014489 := bstep (se 2 (by rfl) ⟨1130433, by rfl⟩ : syracuseStep 3014489 = 2260867) B2260867
theorem B6029207 : Blo 1786094 6029207 := bstep (se 1 (by rfl) ⟨4521905, by rfl⟩ : syracuseStep 6029207 = 9043811) B9043811
theorem B2416537 : Blo 1786094 2416537 := bstep (se 2 (by rfl) ⟨906201, by rfl⟩ : syracuseStep 2416537 = 1812403) B1812403
theorem B3014617 : Blo 1786094 3014617 := bstep (se 2 (by rfl) ⟨1130481, by rfl⟩ : syracuseStep 3014617 = 2260963) B2260963
theorem B8708057 : Blo 1786094 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B3014671 : Blo 1786094 3014671 := bstep (se 1 (by rfl) ⟨2261003, by rfl⟩ : syracuseStep 3014671 = 4522007) B4522007
theorem B4522027 : Blo 1786094 4522027 := bstep (se 1 (by rfl) ⟨3391520, by rfl⟩ : syracuseStep 4522027 = 6783041) B6783041
theorem B4022315 : Blo 1786094 4022315 := bstep (se 1 (by rfl) ⟨3016736, by rfl⟩ : syracuseStep 4022315 = 6033473) B6033473
theorem B77299757 : Blo 1786094 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B2261135 : Blo 1786094 2261135 := bstep (se 1 (by rfl) ⟨1695851, by rfl⟩ : syracuseStep 2261135 = 3391703) B3391703
theorem B2146447 : Blo 1786094 2146447 := bstep (se 1 (by rfl) ⟨1609835, by rfl⟩ : syracuseStep 2146447 = 3219671) B3219671
theorem B4522169 : Blo 1786094 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B1786119 : Blo 1786094 1786119 := bstep (se 1 (by rfl) ⟨1339589, by rfl⟩ : syracuseStep 1786119 = 2679179) B2679179
theorem B1786127 : Blo 1786094 1786127 := bstep (se 1 (by rfl) ⟨1339595, by rfl⟩ : syracuseStep 1786127 = 2679191) B2679191
theorem B3391787 : Blo 1786094 3391787 := bstep (se 1 (by rfl) ⟨2543840, by rfl⟩ : syracuseStep 3391787 = 5087681) B5087681
theorem B1786171 : Blo 1786094 1786171 := bstep (se 1 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 1786171 = 2679257) B2679257
theorem B10174835 : Blo 1786094 10174835 := bstep (se 1 (by rfl) ⟨7631126, by rfl⟩ : syracuseStep 10174835 = 15262253) B15262253
theorem B1786247 : Blo 1786094 1786247 := bstep (se 1 (by rfl) ⟨1339685, by rfl⟩ : syracuseStep 1786247 = 2679371) B2679371
theorem B5087623 : Blo 1786094 5087623 := bstep (se 1 (by rfl) ⟨3815717, by rfl⟩ : syracuseStep 5087623 = 7631435) B7631435
theorem B1786255 : Blo 1786094 1786255 := bstep (se 1 (by rfl) ⟨1339691, by rfl⟩ : syracuseStep 1786255 = 2679383) B2679383
theorem B4022675 : Blo 1786094 4022675 := bstep (se 1 (by rfl) ⟨3017006, by rfl⟩ : syracuseStep 4022675 = 6034013) B6034013
theorem B2679227 : Blo 1786094 2679227 := bstep (se 1 (by rfl) ⟨2009420, by rfl⟩ : syracuseStep 2679227 = 4018841) B4018841
theorem B1786299 : Blo 1786094 1786299 := bstep (se 1 (by rfl) ⟨1339724, by rfl⟩ : syracuseStep 1786299 = 2679449) B2679449
theorem B4022729 : Blo 1786094 4022729 := bstep (se 2 (by rfl) ⟨1508523, by rfl⟩ : syracuseStep 4022729 = 3017047) B3017047
theorem B11018699 : Blo 1786094 11018699 := bstep (se 1 (by rfl) ⟨8264024, by rfl⟩ : syracuseStep 11018699 = 16528049) B16528049
theorem B2679287 : Blo 1786094 2679287 := bstep (se 1 (by rfl) ⟨2009465, by rfl⟩ : syracuseStep 2679287 = 4018931) B4018931
theorem B1786375 : Blo 1786094 1786375 := bstep (se 1 (by rfl) ⟨1339781, by rfl⟩ : syracuseStep 1786375 = 2679563) B2679563
theorem B2679311 : Blo 1786094 2679311 := bstep (se 1 (by rfl) ⟨2009483, by rfl⟩ : syracuseStep 2679311 = 4018967) B4018967
theorem B1786383 : Blo 1786094 1786383 := bstep (se 1 (by rfl) ⟨1339787, by rfl⟩ : syracuseStep 1786383 = 2679575) B2679575
theorem B2146831 : Blo 1786094 2146831 := bstep (se 1 (by rfl) ⟨1610123, by rfl⟩ : syracuseStep 2146831 = 3220247) B3220247
theorem B7635485 : Blo 1786094 7635485 := bstep (se 3 (by rfl) ⟨1431653, by rfl⟩ : syracuseStep 7635485 = 2863307) B2863307
theorem B3015211 : Blo 1786094 3015211 := bstep (se 1 (by rfl) ⟨2261408, by rfl⟩ : syracuseStep 3015211 = 4522817) B4522817
theorem B2679353 : Blo 1786094 2679353 := bstep (se 2 (by rfl) ⟨1004757, by rfl⟩ : syracuseStep 2679353 = 2009515) B2009515
theorem B1786427 : Blo 1786094 1786427 := bstep (se 1 (by rfl) ⟨1339820, by rfl⟩ : syracuseStep 1786427 = 2679641) B2679641
theorem B30958145 : Blo 1786094 30958145 := bstep (se 2 (by rfl) ⟨11609304, by rfl⟩ : syracuseStep 30958145 = 23218609) B23218609
theorem B9175619 : Blo 1786094 9175619 := bstep (se 1 (by rfl) ⟨6881714, by rfl⟩ : syracuseStep 9175619 = 13763429) B13763429
theorem B2679431 : Blo 1786094 2679431 := bstep (se 1 (by rfl) ⟨2009573, by rfl⟩ : syracuseStep 2679431 = 4019147) B4019147
theorem B1786503 : Blo 1786094 1786503 := bstep (se 1 (by rfl) ⟨1339877, by rfl⟩ : syracuseStep 1786503 = 2679755) B2679755
theorem B2753167 : Blo 1786094 2753167 := bstep (se 1 (by rfl) ⟨2064875, by rfl⟩ : syracuseStep 2753167 = 4129751) B4129751
theorem B1786511 : Blo 1786094 1786511 := bstep (se 1 (by rfl) ⟨1339883, by rfl⟩ : syracuseStep 1786511 = 2679767) B2679767
theorem B5087897 : Blo 1786094 5087897 := bstep (se 2 (by rfl) ⟨1907961, by rfl⟩ : syracuseStep 5087897 = 3815923) B3815923
theorem B2679467 : Blo 1786094 2679467 := bstep (se 1 (by rfl) ⟨2009600, by rfl⟩ : syracuseStep 2679467 = 4019201) B4019201
theorem B3015353 : Blo 1786094 3015353 := bstep (se 2 (by rfl) ⟨1130757, by rfl⟩ : syracuseStep 3015353 = 2261515) B2261515
theorem B1786555 : Blo 1786094 1786555 := bstep (se 1 (by rfl) ⟨1339916, by rfl⟩ : syracuseStep 1786555 = 2679833) B2679833
theorem B2679497 : Blo 1786094 2679497 := bstep (se 2 (by rfl) ⟨1004811, by rfl⟩ : syracuseStep 2679497 = 2009623) B2009623
theorem B1786631 : Blo 1786094 1786631 := bstep (se 1 (by rfl) ⟨1339973, by rfl⟩ : syracuseStep 1786631 = 2679947) B2679947
theorem B1786639 : Blo 1786094 1786639 := bstep (se 1 (by rfl) ⟨1339979, by rfl⟩ : syracuseStep 1786639 = 2679959) B2679959
theorem B2679611 : Blo 1786094 2679611 := bstep (se 1 (by rfl) ⟨2009708, by rfl⟩ : syracuseStep 2679611 = 4019417) B4019417
theorem B10175291 : Blo 1786094 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1786683 : Blo 1786094 1786683 := bstep (se 1 (by rfl) ⟨1340012, by rfl⟩ : syracuseStep 1786683 = 2680025) B2680025
theorem B32596825 : Blo 1786094 32596825 := bstep (se 2 (by rfl) ⟨12223809, by rfl⟩ : syracuseStep 32596825 = 24447619) B24447619
theorem B2679671 : Blo 1786094 2679671 := bstep (se 1 (by rfl) ⟨2009753, by rfl⟩ : syracuseStep 2679671 = 4019507) B4019507
theorem B1786759 : Blo 1786094 1786759 := bstep (se 1 (by rfl) ⟨1340069, by rfl⟩ : syracuseStep 1786759 = 2680139) B2680139
theorem B2679695 : Blo 1786094 2679695 := bstep (se 1 (by rfl) ⟨2009771, by rfl⟩ : syracuseStep 2679695 = 4019543) B4019543
theorem B1786767 : Blo 1786094 1786767 := bstep (se 1 (by rfl) ⟨1340075, by rfl⟩ : syracuseStep 1786767 = 2680151) B2680151
theorem B6030233 : Blo 1786094 6030233 := bstep (se 2 (by rfl) ⟨2261337, by rfl⟩ : syracuseStep 6030233 = 4522675) B4522675
theorem B2679737 : Blo 1786094 2679737 := bstep (se 2 (by rfl) ⟨1004901, by rfl⟩ : syracuseStep 2679737 = 2009803) B2009803
theorem B1786811 : Blo 1786094 1786811 := bstep (se 1 (by rfl) ⟨1340108, by rfl⟩ : syracuseStep 1786811 = 2680217) B2680217
theorem B4293577 : Blo 1786094 4293577 := bstep (se 2 (by rfl) ⟨1610091, by rfl⟩ : syracuseStep 4293577 = 3220183) B3220183
theorem B9044945 : Blo 1786094 9044945 := bstep (se 2 (by rfl) ⟨3391854, by rfl⟩ : syracuseStep 9044945 = 6783709) B6783709
theorem B9659357 : Blo 1786094 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B2679815 : Blo 1786094 2679815 := bstep (se 1 (by rfl) ⟨2009861, by rfl⟩ : syracuseStep 2679815 = 4019723) B4019723
theorem B1786887 : Blo 1786094 1786887 := bstep (se 1 (by rfl) ⟨1340165, by rfl⟩ : syracuseStep 1786887 = 2680331) B2680331
theorem B1786895 : Blo 1786094 1786895 := bstep (se 1 (by rfl) ⟨1340171, by rfl⟩ : syracuseStep 1786895 = 2680343) B2680343
theorem B2679851 : Blo 1786094 2679851 := bstep (se 1 (by rfl) ⟨2009888, by rfl⟩ : syracuseStep 2679851 = 4019777) B4019777
theorem B1786939 : Blo 1786094 1786939 := bstep (se 1 (by rfl) ⟨1340204, by rfl⟩ : syracuseStep 1786939 = 2680409) B2680409
theorem B5727293 : Blo 1786094 5727293 := bstep (se 3 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 5727293 = 2147735) B2147735
theorem B2679881 : Blo 1786094 2679881 := bstep (se 2 (by rfl) ⟨1004955, by rfl⟩ : syracuseStep 2679881 = 2009911) B2009911
theorem B28992599 : Blo 1786094 28992599 := bstep (se 1 (by rfl) ⟨21744449, by rfl⟩ : syracuseStep 28992599 = 43488899) B43488899
theorem B1787015 : Blo 1786094 1787015 := bstep (se 1 (by rfl) ⟨1340261, by rfl⟩ : syracuseStep 1787015 = 2680523) B2680523
theorem B1787023 : Blo 1786094 1787023 := bstep (se 1 (by rfl) ⟨1340267, by rfl⟩ : syracuseStep 1787023 = 2680535) B2680535
theorem B4523161 : Blo 1786094 4523161 := bstep (se 2 (by rfl) ⟨1696185, by rfl⟩ : syracuseStep 4523161 = 3392371) B3392371
theorem B2679995 : Blo 1786094 2679995 := bstep (se 1 (by rfl) ⟨2009996, by rfl⟩ : syracuseStep 2679995 = 4019993) B4019993
theorem B2753723 : Blo 1786094 2753723 := bstep (se 1 (by rfl) ⟨2065292, by rfl⟩ : syracuseStep 2753723 = 4130585) B4130585
theorem B1787067 : Blo 1786094 1787067 := bstep (se 1 (by rfl) ⟨1340300, by rfl⟩ : syracuseStep 1787067 = 2680601) B2680601
theorem B2680055 : Blo 1786094 2680055 := bstep (se 1 (by rfl) ⟨2010041, by rfl⟩ : syracuseStep 2680055 = 4020083) B4020083
theorem B1787143 : Blo 1786094 1787143 := bstep (se 1 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 1787143 = 2680715) B2680715
theorem B2680079 : Blo 1786094 2680079 := bstep (se 1 (by rfl) ⟨2010059, by rfl⟩ : syracuseStep 2680079 = 4020119) B4020119
theorem B1787151 : Blo 1786094 1787151 := bstep (se 1 (by rfl) ⟨1340363, by rfl⟩ : syracuseStep 1787151 = 2680727) B2680727
theorem B2680121 : Blo 1786094 2680121 := bstep (se 2 (by rfl) ⟨1005045, by rfl⟩ : syracuseStep 2680121 = 2010091) B2010091
theorem B11445563 : Blo 1786094 11445563 := bstep (se 1 (by rfl) ⟨8584172, by rfl⟩ : syracuseStep 11445563 = 17168345) B17168345
theorem B4523323 : Blo 1786094 4523323 := bstep (se 1 (by rfl) ⟨3392492, by rfl⟩ : syracuseStep 4523323 = 6784985) B6784985
theorem B1787195 : Blo 1786094 1787195 := bstep (se 1 (by rfl) ⟨1340396, by rfl⟩ : syracuseStep 1787195 = 2680793) B2680793
theorem B3016055 : Blo 1786094 3016055 := bstep (se 1 (by rfl) ⟨2262041, by rfl⟩ : syracuseStep 3016055 = 4524083) B4524083
theorem B2680199 : Blo 1786094 2680199 := bstep (se 1 (by rfl) ⟨2010149, by rfl⟩ : syracuseStep 2680199 = 4020299) B4020299
theorem B3392903 : Blo 1786094 3392903 := bstep (se 1 (by rfl) ⟨2544677, by rfl⟩ : syracuseStep 3392903 = 5089355) B5089355
theorem B1787271 : Blo 1786094 1787271 := bstep (se 1 (by rfl) ⟨1340453, by rfl⟩ : syracuseStep 1787271 = 2680907) B2680907
theorem B1787279 : Blo 1786094 1787279 := bstep (se 1 (by rfl) ⟨1340459, by rfl⟩ : syracuseStep 1787279 = 2680919) B2680919
theorem B2680235 : Blo 1786094 2680235 := bstep (se 1 (by rfl) ⟨2010176, by rfl⟩ : syracuseStep 2680235 = 4020353) B4020353
theorem B1787323 : Blo 1786094 1787323 := bstep (se 1 (by rfl) ⟨1340492, by rfl⟩ : syracuseStep 1787323 = 2680985) B2680985
theorem B2680265 : Blo 1786094 2680265 := bstep (se 2 (by rfl) ⟨1005099, by rfl⟩ : syracuseStep 2680265 = 2010199) B2010199
theorem B4523465 : Blo 1786094 4523465 := bstep (se 2 (by rfl) ⟨1696299, by rfl⟩ : syracuseStep 4523465 = 3392599) B3392599
theorem B20366801 : Blo 1786094 20366801 := bstep (se 2 (by rfl) ⟨7637550, by rfl⟩ : syracuseStep 20366801 = 15275101) B15275101
theorem B1787399 : Blo 1786094 1787399 := bstep (se 1 (by rfl) ⟨1340549, by rfl⟩ : syracuseStep 1787399 = 2681099) B2681099
theorem B1787407 : Blo 1786094 1787407 := bstep (se 1 (by rfl) ⟨1340555, by rfl⟩ : syracuseStep 1787407 = 2681111) B2681111
theorem B2680379 : Blo 1786094 2680379 := bstep (se 1 (by rfl) ⟨2010284, by rfl⟩ : syracuseStep 2680379 = 4020569) B4020569
theorem B1787451 : Blo 1786094 1787451 := bstep (se 1 (by rfl) ⟨1340588, by rfl⟩ : syracuseStep 1787451 = 2681177) B2681177
theorem B6030935 : Blo 1786094 6030935 := bstep (se 1 (by rfl) ⟨4523201, by rfl⟩ : syracuseStep 6030935 = 9046403) B9046403
theorem B2680439 : Blo 1786094 2680439 := bstep (se 1 (by rfl) ⟨2010329, by rfl⟩ : syracuseStep 2680439 = 4020659) B4020659
theorem B1787527 : Blo 1786094 1787527 := bstep (se 1 (by rfl) ⟨1340645, by rfl⟩ : syracuseStep 1787527 = 2681291) B2681291
theorem B2680463 : Blo 1786094 2680463 := bstep (se 1 (by rfl) ⟨2010347, by rfl⟩ : syracuseStep 2680463 = 4020695) B4020695
theorem B1787535 : Blo 1786094 1787535 := bstep (se 1 (by rfl) ⟨1340651, by rfl⟩ : syracuseStep 1787535 = 2681303) B2681303
theorem B2680505 : Blo 1786094 2680505 := bstep (se 2 (by rfl) ⟨1005189, by rfl⟩ : syracuseStep 2680505 = 2010379) B2010379
theorem B1787579 : Blo 1786094 1787579 := bstep (se 1 (by rfl) ⟨1340684, by rfl⟩ : syracuseStep 1787579 = 2681369) B2681369
theorem B13756097 : Blo 1786094 13756097 := bstep (se 2 (by rfl) ⟨5158536, by rfl⟩ : syracuseStep 13756097 = 10317073) B10317073
theorem B2680583 : Blo 1786094 2680583 := bstep (se 1 (by rfl) ⟨2010437, by rfl⟩ : syracuseStep 2680583 = 4020875) B4020875
theorem B1787655 : Blo 1786094 1787655 := bstep (se 1 (by rfl) ⟨1340741, by rfl⟩ : syracuseStep 1787655 = 2681483) B2681483
theorem B1787663 : Blo 1786094 1787663 := bstep (se 1 (by rfl) ⟨1340747, by rfl⟩ : syracuseStep 1787663 = 2681495) B2681495
theorem B4523809 : Blo 1786094 4523809 := bstep (se 2 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 4523809 = 3392857) B3392857
theorem B10176293 : Blo 1786094 10176293 := bstep (se 4 (by rfl) ⟨954027, by rfl⟩ : syracuseStep 10176293 = 1908055) B1908055
theorem B2680619 : Blo 1786094 2680619 := bstep (se 1 (by rfl) ⟨2010464, by rfl⟩ : syracuseStep 2680619 = 4020929) B4020929
theorem B3016507 : Blo 1786094 3016507 := bstep (se 1 (by rfl) ⟨2262380, by rfl⟩ : syracuseStep 3016507 = 4524761) B4524761
theorem B1787707 : Blo 1786094 1787707 := bstep (se 1 (by rfl) ⟨1340780, by rfl⟩ : syracuseStep 1787707 = 2681561) B2681561
theorem B2680649 : Blo 1786094 2680649 := bstep (se 2 (by rfl) ⟨1005243, by rfl⟩ : syracuseStep 2680649 = 2010487) B2010487
theorem B5089139 : Blo 1786094 5089139 := bstep (se 1 (by rfl) ⟨3816854, by rfl⟩ : syracuseStep 5089139 = 7633709) B7633709
theorem B1787783 : Blo 1786094 1787783 := bstep (se 1 (by rfl) ⟨1340837, by rfl⟩ : syracuseStep 1787783 = 2681675) B2681675
theorem B1787791 : Blo 1786094 1787791 := bstep (se 1 (by rfl) ⟨1340843, by rfl⟩ : syracuseStep 1787791 = 2681687) B2681687
theorem B4294547 : Blo 1786094 4294547 := bstep (se 1 (by rfl) ⟨3220910, by rfl⟩ : syracuseStep 4294547 = 6441821) B6441821
theorem B3393427 : Blo 1786094 3393427 := bstep (se 1 (by rfl) ⟨2545070, by rfl⟩ : syracuseStep 3393427 = 5090141) B5090141
theorem B2680763 : Blo 1786094 2680763 := bstep (se 1 (by rfl) ⟨2010572, by rfl⟩ : syracuseStep 2680763 = 4021145) B4021145
theorem B1787835 : Blo 1786094 1787835 := bstep (se 1 (by rfl) ⟨1340876, by rfl⟩ : syracuseStep 1787835 = 2681753) B2681753
theorem B3016649 : Blo 1786094 3016649 := bstep (se 2 (by rfl) ⟨1131243, by rfl⟩ : syracuseStep 3016649 = 2262487) B2262487
theorem B2680823 : Blo 1786094 2680823 := bstep (se 1 (by rfl) ⟨2010617, by rfl⟩ : syracuseStep 2680823 = 4021235) B4021235
theorem B1787911 : Blo 1786094 1787911 := bstep (se 1 (by rfl) ⟨1340933, by rfl⟩ : syracuseStep 1787911 = 2681867) B2681867
theorem B6531083 : Blo 1786094 6531083 := bstep (se 1 (by rfl) ⟨4898312, by rfl⟩ : syracuseStep 6531083 = 9796625) B9796625
theorem B2680847 : Blo 1786094 2680847 := bstep (se 1 (by rfl) ⟨2010635, by rfl⟩ : syracuseStep 2680847 = 4021271) B4021271
theorem B1787919 : Blo 1786094 1787919 := bstep (se 1 (by rfl) ⟨1340939, by rfl⟩ : syracuseStep 1787919 = 2681879) B2681879
theorem B2680889 : Blo 1786094 2680889 := bstep (se 2 (by rfl) ⟨1005333, by rfl⟩ : syracuseStep 2680889 = 2010667) B2010667
theorem B1787963 : Blo 1786094 1787963 := bstep (se 1 (by rfl) ⟨1340972, by rfl⟩ : syracuseStep 1787963 = 2681945) B2681945
theorem B6031421 : Blo 1786094 6031421 := bstep (se 3 (by rfl) ⟨1130891, by rfl⟩ : syracuseStep 6031421 = 2261783) B2261783
theorem B12888197 : Blo 1786094 12888197 := bstep (se 4 (by rfl) ⟨1208268, by rfl⟩ : syracuseStep 12888197 = 2416537) B2416537
theorem B2680967 : Blo 1786094 2680967 := bstep (se 1 (by rfl) ⟨2010725, by rfl⟩ : syracuseStep 2680967 = 4021451) B4021451
theorem B1788039 : Blo 1786094 1788039 := bstep (se 1 (by rfl) ⟨1341029, by rfl⟩ : syracuseStep 1788039 = 2682059) B2682059
theorem B1788047 : Blo 1786094 1788047 := bstep (se 1 (by rfl) ⟨1341035, by rfl⟩ : syracuseStep 1788047 = 2682071) B2682071
theorem B2681003 : Blo 1786094 2681003 := bstep (se 1 (by rfl) ⟨2010752, by rfl⟩ : syracuseStep 2681003 = 4021505) B4021505
theorem B3221689 : Blo 1786094 3221689 := bstep (se 2 (by rfl) ⟨1208133, by rfl⟩ : syracuseStep 3221689 = 2416267) B2416267
theorem B1788091 : Blo 1786094 1788091 := bstep (se 1 (by rfl) ⟨1341068, by rfl⟩ : syracuseStep 1788091 = 2682137) B2682137
theorem B2861257 : Blo 1786094 2861257 := bstep (se 2 (by rfl) ⟨1072971, by rfl⟩ : syracuseStep 2861257 = 2145943) B2145943
theorem B2681033 : Blo 1786094 2681033 := bstep (se 2 (by rfl) ⟨1005387, by rfl⟩ : syracuseStep 2681033 = 2010775) B2010775
theorem B10176749 : Blo 1786094 10176749 := bstep (se 3 (by rfl) ⟨1908140, by rfl⟩ : syracuseStep 10176749 = 3816281) B3816281
theorem B2681147 : Blo 1786094 2681147 := bstep (se 1 (by rfl) ⟨2010860, by rfl⟩ : syracuseStep 2681147 = 4021721) B4021721
theorem B4524407 : Blo 1786094 4524407 := bstep (se 1 (by rfl) ⟨3393305, by rfl⟩ : syracuseStep 4524407 = 6786611) B6786611
theorem B2681207 : Blo 1786094 2681207 := bstep (se 1 (by rfl) ⟨2010905, by rfl⟩ : syracuseStep 2681207 = 4021811) B4021811
theorem B2009479 : Blo 1786094 2009479 := bstep (se 1 (by rfl) ⟨1507109, by rfl⟩ : syracuseStep 2009479 = 3014219) B3014219
theorem B2681231 : Blo 1786094 2681231 := bstep (se 1 (by rfl) ⟨2010923, by rfl⟩ : syracuseStep 2681231 = 4021847) B4021847
theorem B2681273 : Blo 1786094 2681273 := bstep (se 2 (by rfl) ⟨1005477, by rfl⟩ : syracuseStep 2681273 = 2010955) B2010955
theorem B2681351 : Blo 1786094 2681351 := bstep (se 1 (by rfl) ⟨2011013, by rfl⟩ : syracuseStep 2681351 = 4022027) B4022027
theorem B2681387 : Blo 1786094 2681387 := bstep (se 1 (by rfl) ⟨2011040, by rfl⟩ : syracuseStep 2681387 = 4022081) B4022081
theorem B2009659 : Blo 1786094 2009659 := bstep (se 1 (by rfl) ⟨1507244, by rfl⟩ : syracuseStep 2009659 = 3014489) B3014489
theorem B2681417 : Blo 1786094 2681417 := bstep (se 2 (by rfl) ⟨1005531, by rfl⟩ : syracuseStep 2681417 = 2011063) B2011063
theorem B3017351 : Blo 1786094 3017351 := bstep (se 1 (by rfl) ⟨2263013, by rfl⟩ : syracuseStep 3017351 = 4526027) B4526027
theorem B2681531 : Blo 1786094 2681531 := bstep (se 1 (by rfl) ⟨2011148, by rfl⟩ : syracuseStep 2681531 = 4022297) B4022297
theorem B30526145 : Blo 1786094 30526145 := bstep (se 2 (by rfl) ⟨11447304, by rfl⟩ : syracuseStep 30526145 = 22894609) B22894609
theorem B2681591 : Blo 1786094 2681591 := bstep (se 1 (by rfl) ⟨2011193, by rfl⟩ : syracuseStep 2681591 = 4022387) B4022387
theorem B2681615 : Blo 1786094 2681615 := bstep (se 1 (by rfl) ⟨2011211, by rfl⟩ : syracuseStep 2681615 = 4022423) B4022423
theorem B32623397 : Blo 1786094 32623397 := bstep (se 4 (by rfl) ⟨3058443, by rfl⟩ : syracuseStep 32623397 = 6116887) B6116887
theorem B2681657 : Blo 1786094 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B57961331 : Blo 1786094 57961331 := bstep (se 1 (by rfl) ⟨43470998, by rfl⟩ : syracuseStep 57961331 = 86941997) B86941997
theorem B6785927 : Blo 1786094 6785927 := bstep (se 1 (by rfl) ⟨5089445, by rfl⟩ : syracuseStep 6785927 = 10178891) B10178891
theorem B2681735 : Blo 1786094 2681735 := bstep (se 1 (by rfl) ⟨2011301, by rfl⟩ : syracuseStep 2681735 = 4022603) B4022603
theorem B10177433 : Blo 1786094 10177433 := bstep (se 2 (by rfl) ⟨3816537, by rfl⟩ : syracuseStep 10177433 = 7633075) B7633075
theorem B5434265 : Blo 1786094 5434265 := bstep (se 2 (by rfl) ⟨2037849, by rfl⟩ : syracuseStep 5434265 = 4075699) B4075699
theorem B2681771 : Blo 1786094 2681771 := bstep (se 1 (by rfl) ⟨2011328, by rfl⟩ : syracuseStep 2681771 = 4022657) B4022657
theorem B36678581 : Blo 1786094 36678581 := bstep (se 5 (by rfl) ⟨1719308, by rfl⟩ : syracuseStep 36678581 = 3438617) B3438617
theorem B3623881 : Blo 1786094 3623881 := bstep (se 2 (by rfl) ⟨1358955, by rfl⟩ : syracuseStep 3623881 = 2717911) B2717911
theorem B2681801 : Blo 1786094 2681801 := bstep (se 2 (by rfl) ⟨1005675, by rfl⟩ : syracuseStep 2681801 = 2011351) B2011351
theorem B9047051 : Blo 1786094 9047051 := bstep (se 1 (by rfl) ⟨6785288, by rfl⟩ : syracuseStep 9047051 = 13570577) B13570577
theorem B2010127 : Blo 1786094 2010127 := bstep (se 1 (by rfl) ⟨1507595, by rfl⟩ : syracuseStep 2010127 = 3015191) B3015191
theorem B2681915 : Blo 1786094 2681915 := bstep (se 1 (by rfl) ⟨2011436, by rfl⟩ : syracuseStep 2681915 = 4022873) B4022873
theorem B2681975 : Blo 1786094 2681975 := bstep (se 1 (by rfl) ⟨2011481, by rfl⟩ : syracuseStep 2681975 = 4022963) B4022963
theorem B2681999 : Blo 1786094 2681999 := bstep (se 1 (by rfl) ⟨2011499, by rfl⟩ : syracuseStep 2681999 = 4022999) B4022999
theorem B9047213 : Blo 1786094 9047213 := bstep (se 3 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 9047213 = 3392705) B3392705
theorem B2682041 : Blo 1786094 2682041 := bstep (se 2 (by rfl) ⟨1005765, by rfl⟩ : syracuseStep 2682041 = 2011531) B2011531
theorem B30534893 : Blo 1786094 30534893 := bstep (se 3 (by rfl) ⟨5725292, by rfl⟩ : syracuseStep 30534893 = 11450585) B11450585
theorem B2682119 : Blo 1786094 2682119 := bstep (se 1 (by rfl) ⟨2011589, by rfl⟩ : syracuseStep 2682119 = 4023179) B4023179
theorem B43470215 : Blo 1786094 43470215 := bstep (se 1 (by rfl) ⟨32602661, by rfl⟩ : syracuseStep 43470215 = 65205323) B65205323
theorem B8154503 : Blo 1786094 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B6032825 : Blo 1786094 6032825 := bstep (se 2 (by rfl) ⟨2262309, by rfl⟩ : syracuseStep 6032825 = 4524619) B4524619
theorem B2010631 : Blo 1786094 2010631 := bstep (se 1 (by rfl) ⟨1507973, by rfl⟩ : syracuseStep 2010631 = 3015947) B3015947
theorem B5582351 : Blo 1786094 5582351 := bstep (se 1 (by rfl) ⟨4186763, by rfl⟩ : syracuseStep 5582351 = 8373527) B8373527
theorem B4525703 : Blo 1786094 4525703 := bstep (se 1 (by rfl) ⟨3394277, by rfl⟩ : syracuseStep 4525703 = 6788555) B6788555
theorem B9662125 : Blo 1786094 9662125 := bstep (se 3 (by rfl) ⟨1811648, by rfl⟩ : syracuseStep 9662125 = 3623297) B3623297
theorem B4525753 : Blo 1786094 4525753 := bstep (se 2 (by rfl) ⟨1697157, by rfl⟩ : syracuseStep 4525753 = 3394315) B3394315
theorem B2010811 : Blo 1786094 2010811 := bstep (se 1 (by rfl) ⟨1508108, by rfl⟩ : syracuseStep 2010811 = 3016217) B3016217
theorem B4829063 : Blo 1786094 4829063 := bstep (se 1 (by rfl) ⟨3621797, by rfl⟩ : syracuseStep 4829063 = 7243595) B7243595
theorem B29364119 : Blo 1786094 29364119 := bstep (se 1 (by rfl) ⟨22023089, by rfl⟩ : syracuseStep 29364119 = 44046179) B44046179
theorem B6033419 : Blo 1786094 6033419 := bstep (se 1 (by rfl) ⟨4525064, by rfl⟩ : syracuseStep 6033419 = 9050129) B9050129
theorem B3182635 : Blo 1786094 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B6033527 : Blo 1786094 6033527 := bstep (se 1 (by rfl) ⟨4525145, by rfl⟩ : syracuseStep 6033527 = 9050291) B9050291
theorem B2011279 : Blo 1786094 2011279 := bstep (se 1 (by rfl) ⟨1508459, by rfl⟩ : syracuseStep 2011279 = 3016919) B3016919
theorem B70578377 : Blo 1786094 70578377 := bstep (se 2 (by rfl) ⟨26466891, by rfl⟩ : syracuseStep 70578377 = 52933783) B52933783
theorem B25768205 : Blo 1786094 25768205 := bstep (se 3 (by rfl) ⟨4831538, by rfl⟩ : syracuseStep 25768205 = 9663077) B9663077
theorem B5091599 : Blo 1786094 5091599 := bstep (se 1 (by rfl) ⟨3818699, by rfl⟩ : syracuseStep 5091599 = 7637399) B7637399
theorem B4018823 : Blo 1786094 4018823 := bstep (se 1 (by rfl) ⟨3014117, by rfl⟩ : syracuseStep 4018823 = 6028235) B6028235
theorem B2544313 : Blo 1786094 2544313 := bstep (se 2 (by rfl) ⟨954117, by rfl⟩ : syracuseStep 2544313 = 1908235) B1908235
theorem B6034121 : Blo 1786094 6034121 := bstep (se 2 (by rfl) ⟨2262795, by rfl⟩ : syracuseStep 6034121 = 4525591) B4525591
theorem B23540441 : Blo 1786094 23540441 := bstep (se 2 (by rfl) ⟨8827665, by rfl⟩ : syracuseStep 23540441 = 17655331) B17655331
theorem B9048833 : Blo 1786094 9048833 := bstep (se 2 (by rfl) ⟨3393312, by rfl⟩ : syracuseStep 9048833 = 6786625) B6786625
theorem B4019003 : Blo 1786094 4019003 := bstep (se 1 (by rfl) ⟨3014252, by rfl⟩ : syracuseStep 4019003 = 6028505) B6028505
theorem B8147897 : Blo 1786094 8147897 := bstep (se 2 (by rfl) ⟨3055461, by rfl⟩ : syracuseStep 8147897 = 6110923) B6110923
theorem B4019129 : Blo 1786094 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B15479981 : Blo 1786094 15479981 := bstep (se 3 (by rfl) ⟨2902496, by rfl⟩ : syracuseStep 15479981 = 5804993) B5804993
theorem B4019471 : Blo 1786094 4019471 := bstep (se 1 (by rfl) ⟨3014603, by rfl⟩ : syracuseStep 4019471 = 6029207) B6029207
theorem B4019489 : Blo 1786094 4019489 := bstep (se 2 (by rfl) ⟨1507308, by rfl⟩ : syracuseStep 4019489 = 3014617) B3014617
theorem B5805371 : Blo 1786094 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B49550723 : Blo 1786094 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B6116755 : Blo 1786094 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B13571549 : Blo 1786094 13571549 := bstep (se 3 (by rfl) ⟨2544665, by rfl⟩ : syracuseStep 13571549 = 5089331) B5089331
theorem B9655811 : Blo 1786094 9655811 := bstep (se 1 (by rfl) ⟨7241858, by rfl⟩ : syracuseStep 9655811 = 14483717) B14483717
theorem B9049643 : Blo 1786094 9049643 := bstep (se 1 (by rfl) ⟨6787232, by rfl⟩ : syracuseStep 9049643 = 13574465) B13574465
theorem B2717243 : Blo 1786094 2717243 := bstep (se 1 (by rfl) ⟨2037932, by rfl⟩ : syracuseStep 2717243 = 4075865) B4075865
theorem B4019831 : Blo 1786094 4019831 := bstep (se 1 (by rfl) ⟨3014873, by rfl⟩ : syracuseStep 4019831 = 6029747) B6029747
theorem B16307905 : Blo 1786094 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B5158667 : Blo 1786094 5158667 := bstep (se 1 (by rfl) ⟨3869000, by rfl⟩ : syracuseStep 5158667 = 7738001) B7738001
theorem B4020011 : Blo 1786094 4020011 := bstep (se 1 (by rfl) ⟨3015008, by rfl⟩ : syracuseStep 4020011 = 6030017) B6030017
theorem B2545543 : Blo 1786094 2545543 := bstep (se 1 (by rfl) ⟨1909157, by rfl⟩ : syracuseStep 2545543 = 3818315) B3818315
theorem B7845817 : Blo 1786094 7845817 := bstep (se 2 (by rfl) ⟨2942181, by rfl⟩ : syracuseStep 7845817 = 5884363) B5884363
theorem B61929485 : Blo 1786094 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B7739435 : Blo 1786094 7739435 := bstep (se 1 (by rfl) ⟨5804576, by rfl⟩ : syracuseStep 7739435 = 11609153) B11609153
theorem B4020371 : Blo 1786094 4020371 := bstep (se 1 (by rfl) ⟨3015278, by rfl⟩ : syracuseStep 4020371 = 6030557) B6030557
theorem B4020425 : Blo 1786094 4020425 := bstep (se 2 (by rfl) ⟨1507659, by rfl⟩ : syracuseStep 4020425 = 3015319) B3015319
theorem B9042191 : Blo 1786094 9042191 := bstep (se 1 (by rfl) ⟨6781643, by rfl⟩ : syracuseStep 9042191 = 13563287) B13563287
theorem B5167421 : Blo 1786094 5167421 := bstep (se 3 (by rfl) ⟨968891, by rfl⟩ : syracuseStep 5167421 = 1937783) B1937783
theorem B10181123 : Blo 1786094 10181123 := bstep (se 1 (by rfl) ⟨7635842, by rfl⟩ : syracuseStep 10181123 = 15271685) B15271685
theorem B8591939 : Blo 1786094 8591939 := bstep (se 1 (by rfl) ⟨6443954, by rfl⟩ : syracuseStep 8591939 = 12887909) B12887909
theorem B6437495 : Blo 1786094 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B9050939 : Blo 1786094 9050939 := bstep (se 1 (by rfl) ⟨6788204, by rfl⟩ : syracuseStep 9050939 = 13576409) B13576409
theorem B4021127 : Blo 1786094 4021127 := bstep (se 1 (by rfl) ⟨3015845, by rfl⟩ : syracuseStep 4021127 = 6031691) B6031691
theorem B9051101 : Blo 1786094 9051101 := bstep (se 3 (by rfl) ⟨1697081, by rfl⟩ : syracuseStep 9051101 = 3394163) B3394163
theorem B5086223 : Blo 1786094 5086223 := bstep (se 1 (by rfl) ⟨3814667, by rfl⟩ : syracuseStep 5086223 = 7629335) B7629335
theorem B2415673 : Blo 1786094 2415673 := bstep (se 2 (by rfl) ⟨905877, by rfl⟩ : syracuseStep 2415673 = 1811755) B1811755
theorem B4021307 : Blo 1786094 4021307 := bstep (se 1 (by rfl) ⟨3015980, by rfl⟩ : syracuseStep 4021307 = 6031961) B6031961
theorem B6782039 : Blo 1786094 6782039 := bstep (se 1 (by rfl) ⟨5086529, by rfl⟩ : syracuseStep 6782039 = 10173059) B10173059
theorem B10173559 : Blo 1786094 10173559 := bstep (se 1 (by rfl) ⟨7630169, by rfl⟩ : syracuseStep 10173559 = 15260339) B15260339
theorem B4021433 : Blo 1786094 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B3923129 : Blo 1786094 3923129 := bstep (se 2 (by rfl) ⟨1471173, by rfl⟩ : syracuseStep 3923129 = 2942347) B2942347
theorem B3816649 : Blo 1786094 3816649 := bstep (se 2 (by rfl) ⟨1431243, by rfl⟩ : syracuseStep 3816649 = 2862487) B2862487
theorem B4521217 : Blo 1786094 4521217 := bstep (se 2 (by rfl) ⟨1695456, by rfl⟩ : syracuseStep 4521217 = 3390913) B3390913
theorem B6028559 : Blo 1786094 6028559 := bstep (se 1 (by rfl) ⟨4521419, by rfl⟩ : syracuseStep 6028559 = 9042839) B9042839
theorem B1907983 : Blo 1786094 1907983 := bstep (se 1 (by rfl) ⟨1430987, by rfl⟩ : syracuseStep 1907983 = 2861975) B2861975
theorem B8584481 : Blo 1786094 8584481 := bstep (se 2 (by rfl) ⟨3219180, by rfl⟩ : syracuseStep 8584481 = 6438361) B6438361
theorem B9051425 : Blo 1786094 9051425 := bstep (se 2 (by rfl) ⟨3394284, by rfl⟩ : syracuseStep 9051425 = 6788569) B6788569
theorem B57998693 : Blo 1786094 57998693 := bstep (se 4 (by rfl) ⟨5437377, by rfl⟩ : syracuseStep 57998693 = 10874755) B10874755
theorem B30539267 : Blo 1786094 30539267 := bstep (se 1 (by rfl) ⟨22904450, by rfl⟩ : syracuseStep 30539267 = 45808901) B45808901
theorem B4021775 : Blo 1786094 4021775 := bstep (se 1 (by rfl) ⟨3016331, by rfl⟩ : syracuseStep 4021775 = 6032663) B6032663
theorem B6028829 : Blo 1786094 6028829 := bstep (se 3 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 6028829 = 2260811) B2260811
theorem B4021793 : Blo 1786094 4021793 := bstep (se 2 (by rfl) ⟨1508172, by rfl⟩ : syracuseStep 4021793 = 3016345) B3016345
theorem B6782525 : Blo 1786094 6782525 := bstep (se 3 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 6782525 = 2543447) B2543447
theorem B19324595 : Blo 1786094 19324595 := bstep (se 1 (by rfl) ⟨14493446, by rfl⟩ : syracuseStep 19324595 = 28986893) B28986893
theorem B9043649 : Blo 1786094 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B8822465 : Blo 1786094 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B3391247 : Blo 1786094 3391247 := bstep (se 1 (by rfl) ⟨2543435, by rfl⟩ : syracuseStep 3391247 = 5086871) B5086871
theorem B5726011 : Blo 1786094 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B4521815 : Blo 1786094 4521815 := bstep (se 1 (by rfl) ⟨3391361, by rfl⟩ : syracuseStep 4521815 = 6782723) B6782723
theorem B4022135 : Blo 1786094 4022135 := bstep (se 1 (by rfl) ⟨3016601, by rfl⟩ : syracuseStep 4022135 = 6033203) B6033203
theorem B4022279 : Blo 1786094 4022279 := bstep (se 1 (by rfl) ⟨3016709, by rfl⟩ : syracuseStep 4022279 = 6033419) B6033419
theorem B6029369 : Blo 1786094 6029369 := bstep (se 2 (by rfl) ⟨2261013, by rfl⟩ : syracuseStep 6029369 = 4522027) B4522027
theorem B4243513 : Blo 1786094 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B4022351 : Blo 1786094 4022351 := bstep (se 1 (by rfl) ⟨3016763, by rfl⟩ : syracuseStep 4022351 = 6033527) B6033527
theorem B3014779 : Blo 1786094 3014779 := bstep (se 1 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 3014779 = 4522169) B4522169
theorem B17178803 : Blo 1786094 17178803 := bstep (se 1 (by rfl) ⟨12884102, by rfl⟩ : syracuseStep 17178803 = 25768205) B25768205
theorem B2261191 : Blo 1786094 2261191 := bstep (se 1 (by rfl) ⟨1695893, by rfl⟩ : syracuseStep 2261191 = 3391787) B3391787
theorem B6783223 : Blo 1786094 6783223 := bstep (se 1 (by rfl) ⟨5087417, by rfl⟩ : syracuseStep 6783223 = 10174835) B10174835
theorem B1786151 : Blo 1786094 1786151 := bstep (se 1 (by rfl) ⟨1339613, by rfl⟩ : syracuseStep 1786151 = 2679227) B2679227
theorem B1786191 : Blo 1786094 1786191 := bstep (se 1 (by rfl) ⟨1339643, by rfl⟩ : syracuseStep 1786191 = 2679287) B2679287
theorem B1786207 : Blo 1786094 1786207 := bstep (se 1 (by rfl) ⟨1339655, by rfl⟩ : syracuseStep 1786207 = 2679311) B2679311
theorem B1786235 : Blo 1786094 1786235 := bstep (se 1 (by rfl) ⟨1339676, by rfl⟩ : syracuseStep 1786235 = 2679353) B2679353
theorem B6029693 : Blo 1786094 6029693 := bstep (se 3 (by rfl) ⟨1130567, by rfl⟩ : syracuseStep 6029693 = 2261135) B2261135
theorem B2679215 : Blo 1786094 2679215 := bstep (se 1 (by rfl) ⟨2009411, by rfl⟩ : syracuseStep 2679215 = 4018823) B4018823
theorem B1786287 : Blo 1786094 1786287 := bstep (se 1 (by rfl) ⟨1339715, by rfl⟩ : syracuseStep 1786287 = 2679431) B2679431
theorem B3391931 : Blo 1786094 3391931 := bstep (se 1 (by rfl) ⟨2543948, by rfl⟩ : syracuseStep 3391931 = 5087897) B5087897
theorem B1786311 : Blo 1786094 1786311 := bstep (se 1 (by rfl) ⟨1339733, by rfl⟩ : syracuseStep 1786311 = 2679467) B2679467
theorem B1786331 : Blo 1786094 1786331 := bstep (se 1 (by rfl) ⟨1339748, by rfl⟩ : syracuseStep 1786331 = 2679497) B2679497
theorem B4022747 : Blo 1786094 4022747 := bstep (se 1 (by rfl) ⟨3017060, by rfl⟩ : syracuseStep 4022747 = 6034121) B6034121
theorem B2679305 : Blo 1786094 2679305 := bstep (se 2 (by rfl) ⟨1004739, by rfl⟩ : syracuseStep 2679305 = 2009479) B2009479
theorem B6783497 : Blo 1786094 6783497 := bstep (se 2 (by rfl) ⟨2543811, by rfl⟩ : syracuseStep 6783497 = 5087623) B5087623
theorem B2679335 : Blo 1786094 2679335 := bstep (se 1 (by rfl) ⟨2009501, by rfl⟩ : syracuseStep 2679335 = 4019003) B4019003
theorem B1786407 : Blo 1786094 1786407 := bstep (se 1 (by rfl) ⟨1339805, by rfl⟩ : syracuseStep 1786407 = 2679611) B2679611
theorem B6783527 : Blo 1786094 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B1786447 : Blo 1786094 1786447 := bstep (se 1 (by rfl) ⟨1339835, by rfl⟩ : syracuseStep 1786447 = 2679671) B2679671
theorem B1786463 : Blo 1786094 1786463 := bstep (se 1 (by rfl) ⟨1339847, by rfl⟩ : syracuseStep 1786463 = 2679695) B2679695
theorem B5431931 : Blo 1786094 5431931 := bstep (se 1 (by rfl) ⟨4073948, by rfl⟩ : syracuseStep 5431931 = 8147897) B8147897
theorem B2679419 : Blo 1786094 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B1786491 : Blo 1786094 1786491 := bstep (se 1 (by rfl) ⟨1339868, by rfl⟩ : syracuseStep 1786491 = 2679737) B2679737
theorem B6029963 : Blo 1786094 6029963 := bstep (se 1 (by rfl) ⟨4522472, by rfl⟩ : syracuseStep 6029963 = 9044945) B9044945
theorem B6439571 : Blo 1786094 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B1786543 : Blo 1786094 1786543 := bstep (se 1 (by rfl) ⟨1339907, by rfl⟩ : syracuseStep 1786543 = 2679815) B2679815
theorem B1786567 : Blo 1786094 1786567 := bstep (se 1 (by rfl) ⟨1339925, by rfl⟩ : syracuseStep 1786567 = 2679851) B2679851
theorem B3818195 : Blo 1786094 3818195 := bstep (se 1 (by rfl) ⟨2863646, by rfl⟩ : syracuseStep 3818195 = 5727293) B5727293
theorem B1786587 : Blo 1786094 1786587 := bstep (se 1 (by rfl) ⟨1339940, by rfl⟩ : syracuseStep 1786587 = 2679881) B2679881
theorem B2679545 : Blo 1786094 2679545 := bstep (se 2 (by rfl) ⟨1004829, by rfl⟩ : syracuseStep 2679545 = 2009659) B2009659
theorem B1786663 : Blo 1786094 1786663 := bstep (se 1 (by rfl) ⟨1339997, by rfl⟩ : syracuseStep 1786663 = 2679995) B2679995
theorem B1786703 : Blo 1786094 1786703 := bstep (se 1 (by rfl) ⟨1340027, by rfl⟩ : syracuseStep 1786703 = 2680055) B2680055
theorem B2679647 : Blo 1786094 2679647 := bstep (se 1 (by rfl) ⟨2009735, by rfl⟩ : syracuseStep 2679647 = 4019471) B4019471
theorem B1786719 : Blo 1786094 1786719 := bstep (se 1 (by rfl) ⟨1340039, by rfl⟩ : syracuseStep 1786719 = 2680079) B2680079
theorem B3670889 : Blo 1786094 3670889 := bstep (se 2 (by rfl) ⟨1376583, by rfl⟩ : syracuseStep 3670889 = 2753167) B2753167
theorem B2679659 : Blo 1786094 2679659 := bstep (se 1 (by rfl) ⟨2009744, by rfl⟩ : syracuseStep 2679659 = 4019489) B4019489
theorem B1786747 : Blo 1786094 1786747 := bstep (se 1 (by rfl) ⟨1340060, by rfl⟩ : syracuseStep 1786747 = 2680121) B2680121
theorem B3392417 : Blo 1786094 3392417 := bstep (se 2 (by rfl) ⟨1272156, by rfl⟩ : syracuseStep 3392417 = 2544313) B2544313
theorem B1786799 : Blo 1786094 1786799 := bstep (se 1 (by rfl) ⟨1340099, by rfl⟩ : syracuseStep 1786799 = 2680199) B2680199
theorem B2261935 : Blo 1786094 2261935 := bstep (se 1 (by rfl) ⟨1696451, by rfl⟩ : syracuseStep 2261935 = 3392903) B3392903
theorem B1786823 : Blo 1786094 1786823 := bstep (se 1 (by rfl) ⟨1340117, by rfl⟩ : syracuseStep 1786823 = 2680235) B2680235
theorem B1786843 : Blo 1786094 1786843 := bstep (se 1 (by rfl) ⟨1340132, by rfl⟩ : syracuseStep 1786843 = 2680265) B2680265
theorem B3015643 : Blo 1786094 3015643 := bstep (se 1 (by rfl) ⟨2261732, by rfl⟩ : syracuseStep 3015643 = 4523465) B4523465
theorem B1786919 : Blo 1786094 1786919 := bstep (se 1 (by rfl) ⟨1340189, by rfl⟩ : syracuseStep 1786919 = 2680379) B2680379
theorem B1811495 : Blo 1786094 1811495 := bstep (se 1 (by rfl) ⟨1358621, by rfl⟩ : syracuseStep 1811495 = 2717243) B2717243
theorem B2679887 : Blo 1786094 2679887 := bstep (se 1 (by rfl) ⟨2009915, by rfl⟩ : syracuseStep 2679887 = 4019831) B4019831
theorem B1786959 : Blo 1786094 1786959 := bstep (se 1 (by rfl) ⟨1340219, by rfl⟩ : syracuseStep 1786959 = 2680439) B2680439
theorem B1786975 : Blo 1786094 1786975 := bstep (se 1 (by rfl) ⟨1340231, by rfl⟩ : syracuseStep 1786975 = 2680463) B2680463
theorem B1787003 : Blo 1786094 1787003 := bstep (se 1 (by rfl) ⟨1340252, by rfl⟩ : syracuseStep 1787003 = 2680505) B2680505
theorem B1787055 : Blo 1786094 1787055 := bstep (se 1 (by rfl) ⟨1340291, by rfl⟩ : syracuseStep 1787055 = 2680583) B2680583
theorem B6784195 : Blo 1786094 6784195 := bstep (se 1 (by rfl) ⟨5088146, by rfl⟩ : syracuseStep 6784195 = 10176293) B10176293
theorem B2680007 : Blo 1786094 2680007 := bstep (se 1 (by rfl) ⟨2010005, by rfl⟩ : syracuseStep 2680007 = 4020011) B4020011
theorem B1787079 : Blo 1786094 1787079 := bstep (se 1 (by rfl) ⟨1340309, by rfl⟩ : syracuseStep 1787079 = 2680619) B2680619
theorem B1787099 : Blo 1786094 1787099 := bstep (se 1 (by rfl) ⟨1340324, by rfl⟩ : syracuseStep 1787099 = 2680649) B2680649
theorem B3392759 : Blo 1786094 3392759 := bstep (se 1 (by rfl) ⟨2544569, by rfl⟩ : syracuseStep 3392759 = 5089139) B5089139
theorem B1787175 : Blo 1786094 1787175 := bstep (se 1 (by rfl) ⟨1340381, by rfl⟩ : syracuseStep 1787175 = 2680763) B2680763
theorem B1787215 : Blo 1786094 1787215 := bstep (se 1 (by rfl) ⟨1340411, by rfl⟩ : syracuseStep 1787215 = 2680823) B2680823
theorem B1787231 : Blo 1786094 1787231 := bstep (se 1 (by rfl) ⟨1340423, by rfl⟩ : syracuseStep 1787231 = 2680847) B2680847
theorem B2680169 : Blo 1786094 2680169 := bstep (se 2 (by rfl) ⟨1005063, by rfl⟩ : syracuseStep 2680169 = 2010127) B2010127
theorem B1787259 : Blo 1786094 1787259 := bstep (se 1 (by rfl) ⟨1340444, by rfl⟩ : syracuseStep 1787259 = 2680889) B2680889
theorem B14886269 : Blo 1786094 14886269 := bstep (se 3 (by rfl) ⟨2791175, by rfl⟩ : syracuseStep 14886269 = 5582351) B5582351
theorem B3220897 : Blo 1786094 3220897 := bstep (se 2 (by rfl) ⟨1207836, by rfl⟩ : syracuseStep 3220897 = 2415673) B2415673
theorem B1787311 : Blo 1786094 1787311 := bstep (se 1 (by rfl) ⟨1340483, by rfl⟩ : syracuseStep 1787311 = 2680967) B2680967
theorem B2680247 : Blo 1786094 2680247 := bstep (se 1 (by rfl) ⟨2010185, by rfl⟩ : syracuseStep 2680247 = 4020371) B4020371
theorem B1787335 : Blo 1786094 1787335 := bstep (se 1 (by rfl) ⟨1340501, by rfl⟩ : syracuseStep 1787335 = 2681003) B2681003
theorem B2680283 : Blo 1786094 2680283 := bstep (se 1 (by rfl) ⟨2010212, by rfl⟩ : syracuseStep 2680283 = 4020425) B4020425
theorem B1787355 : Blo 1786094 1787355 := bstep (se 1 (by rfl) ⟨1340516, by rfl⟩ : syracuseStep 1787355 = 2681033) B2681033
theorem B6784499 : Blo 1786094 6784499 := bstep (se 1 (by rfl) ⟨5088374, by rfl⟩ : syracuseStep 6784499 = 10176749) B10176749
theorem B6030881 : Blo 1786094 6030881 := bstep (se 2 (by rfl) ⟨2261580, by rfl⟩ : syracuseStep 6030881 = 4523161) B4523161
theorem B1787431 : Blo 1786094 1787431 := bstep (se 1 (by rfl) ⟨1340573, by rfl⟩ : syracuseStep 1787431 = 2681147) B2681147
theorem B3016271 : Blo 1786094 3016271 := bstep (se 1 (by rfl) ⟨2262203, by rfl⟩ : syracuseStep 3016271 = 4524407) B4524407
theorem B1787471 : Blo 1786094 1787471 := bstep (se 1 (by rfl) ⟨1340603, by rfl⟩ : syracuseStep 1787471 = 2681207) B2681207
theorem B5088865 : Blo 1786094 5088865 := bstep (se 2 (by rfl) ⟨1908324, by rfl⟩ : syracuseStep 5088865 = 3816649) B3816649
theorem B1787487 : Blo 1786094 1787487 := bstep (se 1 (by rfl) ⟨1340615, by rfl⟩ : syracuseStep 1787487 = 2681231) B2681231
theorem B1787515 : Blo 1786094 1787515 := bstep (se 1 (by rfl) ⟨1340636, by rfl⟩ : syracuseStep 1787515 = 2681273) B2681273
theorem B1787567 : Blo 1786094 1787567 := bstep (se 1 (by rfl) ⟨1340675, by rfl⟩ : syracuseStep 1787567 = 2681351) B2681351
theorem B1787591 : Blo 1786094 1787591 := bstep (se 1 (by rfl) ⟨1340693, by rfl⟩ : syracuseStep 1787591 = 2681387) B2681387
theorem B5727959 : Blo 1786094 5727959 := bstep (se 1 (by rfl) ⟨4295969, by rfl⟩ : syracuseStep 5727959 = 8591939) B8591939
theorem B1787611 : Blo 1786094 1787611 := bstep (se 1 (by rfl) ⟨1340708, by rfl⟩ : syracuseStep 1787611 = 2681417) B2681417
theorem B6031097 : Blo 1786094 6031097 := bstep (se 2 (by rfl) ⟨2261661, by rfl⟩ : syracuseStep 6031097 = 4523323) B4523323
theorem B1787687 : Blo 1786094 1787687 := bstep (se 1 (by rfl) ⟨1340765, by rfl⟩ : syracuseStep 1787687 = 2681531) B2681531
theorem B20350763 : Blo 1786094 20350763 := bstep (se 1 (by rfl) ⟨15263072, by rfl⟩ : syracuseStep 20350763 = 30526145) B30526145
theorem B1787727 : Blo 1786094 1787727 := bstep (se 1 (by rfl) ⟨1340795, by rfl⟩ : syracuseStep 1787727 = 2681591) B2681591
theorem B1787743 : Blo 1786094 1787743 := bstep (se 1 (by rfl) ⟨1340807, by rfl⟩ : syracuseStep 1787743 = 2681615) B2681615
theorem B1787771 : Blo 1786094 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B2680751 : Blo 1786094 2680751 := bstep (se 1 (by rfl) ⟨2010563, by rfl⟩ : syracuseStep 2680751 = 4021127) B4021127
theorem B4523951 : Blo 1786094 4523951 := bstep (se 1 (by rfl) ⟨3392963, by rfl⟩ : syracuseStep 4523951 = 6785927) B6785927
theorem B1787823 : Blo 1786094 1787823 := bstep (se 1 (by rfl) ⟨1340867, by rfl⟩ : syracuseStep 1787823 = 2681735) B2681735
theorem B6784955 : Blo 1786094 6784955 := bstep (se 1 (by rfl) ⟨5088716, by rfl⟩ : syracuseStep 6784955 = 10177433) B10177433
theorem B3622843 : Blo 1786094 3622843 := bstep (se 1 (by rfl) ⟨2717132, by rfl⟩ : syracuseStep 3622843 = 5434265) B5434265
theorem B1787847 : Blo 1786094 1787847 := bstep (se 1 (by rfl) ⟨1340885, by rfl⟩ : syracuseStep 1787847 = 2681771) B2681771
theorem B1787867 : Blo 1786094 1787867 := bstep (se 1 (by rfl) ⟨1340900, by rfl⟩ : syracuseStep 1787867 = 2681801) B2681801
theorem B6031367 : Blo 1786094 6031367 := bstep (se 1 (by rfl) ⟨4523525, by rfl⟩ : syracuseStep 6031367 = 9047051) B9047051
theorem B2680841 : Blo 1786094 2680841 := bstep (se 2 (by rfl) ⟨1005315, by rfl⟩ : syracuseStep 2680841 = 2010631) B2010631
theorem B2680871 : Blo 1786094 2680871 := bstep (se 1 (by rfl) ⟨2010653, by rfl⟩ : syracuseStep 2680871 = 4021307) B4021307
theorem B1787943 : Blo 1786094 1787943 := bstep (se 1 (by rfl) ⟨1340957, by rfl⟩ : syracuseStep 1787943 = 2681915) B2681915
theorem B1787983 : Blo 1786094 1787983 := bstep (se 1 (by rfl) ⟨1340987, by rfl⟩ : syracuseStep 1787983 = 2681975) B2681975
theorem B1787999 : Blo 1786094 1787999 := bstep (se 1 (by rfl) ⟨1340999, by rfl⟩ : syracuseStep 1787999 = 2681999) B2681999
theorem B6031475 : Blo 1786094 6031475 := bstep (se 1 (by rfl) ⟨4523606, by rfl⟩ : syracuseStep 6031475 = 9047213) B9047213
theorem B2680955 : Blo 1786094 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B2615419 : Blo 1786094 2615419 := bstep (se 1 (by rfl) ⟨1961564, by rfl⟩ : syracuseStep 2615419 = 3923129) B3923129
theorem B1788027 : Blo 1786094 1788027 := bstep (se 1 (by rfl) ⟨1341020, by rfl⟩ : syracuseStep 1788027 = 2682041) B2682041
theorem B1788079 : Blo 1786094 1788079 := bstep (se 1 (by rfl) ⟨1341059, by rfl⟩ : syracuseStep 1788079 = 2682119) B2682119
theorem B2681081 : Blo 1786094 2681081 := bstep (se 2 (by rfl) ⟨1005405, by rfl⟩ : syracuseStep 2681081 = 2010811) B2010811
theorem B21743873 : Blo 1786094 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B20359511 : Blo 1786094 20359511 := bstep (se 1 (by rfl) ⟨15269633, by rfl⟩ : syracuseStep 20359511 = 30539267) B30539267
theorem B2681183 : Blo 1786094 2681183 := bstep (se 1 (by rfl) ⟨2010887, by rfl⟩ : syracuseStep 2681183 = 4021775) B4021775
theorem B2681195 : Blo 1786094 2681195 := bstep (se 1 (by rfl) ⟨2010896, by rfl⟩ : syracuseStep 2681195 = 4021793) B4021793
theorem B6031745 : Blo 1786094 6031745 := bstep (se 2 (by rfl) ⟨2261904, by rfl⟩ : syracuseStep 6031745 = 4523809) B4523809
theorem B3017135 : Blo 1786094 3017135 := bstep (se 1 (by rfl) ⟨2262851, by rfl⟩ : syracuseStep 3017135 = 4525703) B4525703
theorem B3394057 : Blo 1786094 3394057 := bstep (se 2 (by rfl) ⟨1272771, by rfl⟩ : syracuseStep 3394057 = 2545543) B2545543
theorem B4524569 : Blo 1786094 4524569 := bstep (se 2 (by rfl) ⟨1696713, by rfl⟩ : syracuseStep 4524569 = 3393427) B3393427
theorem B2681423 : Blo 1786094 2681423 := bstep (se 1 (by rfl) ⟨2011067, by rfl⟩ : syracuseStep 2681423 = 4022135) B4022135
theorem B2681543 : Blo 1786094 2681543 := bstep (se 1 (by rfl) ⟨2011157, by rfl⟩ : syracuseStep 2681543 = 4022315) B4022315
theorem B3394399 : Blo 1786094 3394399 := bstep (se 1 (by rfl) ⟨2545799, by rfl⟩ : syracuseStep 3394399 = 5091599) B5091599
theorem B2861929 : Blo 1786094 2861929 := bstep (se 2 (by rfl) ⟨1073223, by rfl⟩ : syracuseStep 2861929 = 2146447) B2146447
theorem B2681705 : Blo 1786094 2681705 := bstep (se 2 (by rfl) ⟨1005639, by rfl⟩ : syracuseStep 2681705 = 2011279) B2011279
theorem B4295585 : Blo 1786094 4295585 := bstep (se 2 (by rfl) ⟨1610844, by rfl⟩ : syracuseStep 4295585 = 3221689) B3221689
theorem B2681783 : Blo 1786094 2681783 := bstep (se 1 (by rfl) ⟨2011337, by rfl⟩ : syracuseStep 2681783 = 4022675) B4022675
theorem B2681819 : Blo 1786094 2681819 := bstep (se 1 (by rfl) ⟨2011364, by rfl⟩ : syracuseStep 2681819 = 4022729) B4022729
theorem B5090323 : Blo 1786094 5090323 := bstep (se 1 (by rfl) ⟨3817742, by rfl⟩ : syracuseStep 5090323 = 7635485) B7635485
theorem B20638763 : Blo 1786094 20638763 := bstep (se 1 (by rfl) ⟨15479072, by rfl⟩ : syracuseStep 20638763 = 30958145) B30958145
theorem B2010235 : Blo 1786094 2010235 := bstep (se 1 (by rfl) ⟨1507676, by rfl⟩ : syracuseStep 2010235 = 3015353) B3015353
theorem B7343261 : Blo 1786094 7343261 := bstep (se 3 (by rfl) ⟨1376861, by rfl⟩ : syracuseStep 7343261 = 2753723) B2753723
theorem B6032555 : Blo 1786094 6032555 := bstep (se 1 (by rfl) ⟨4524416, by rfl⟩ : syracuseStep 6032555 = 9048833) B9048833
theorem B19328399 : Blo 1786094 19328399 := bstep (se 1 (by rfl) ⟨14496299, by rfl⟩ : syracuseStep 19328399 = 28992599) B28992599
theorem B7630375 : Blo 1786094 7630375 := bstep (se 1 (by rfl) ⟨5722781, by rfl⟩ : syracuseStep 7630375 = 11445563) B11445563
theorem B3870247 : Blo 1786094 3870247 := bstep (se 1 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 3870247 = 5805371) B5805371
theorem B2010703 : Blo 1786094 2010703 := bstep (se 1 (by rfl) ⟨1508027, by rfl⟩ : syracuseStep 2010703 = 3016055) B3016055
theorem B33033815 : Blo 1786094 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B13577867 : Blo 1786094 13577867 := bstep (se 1 (by rfl) ⟨10183400, by rfl⟩ : syracuseStep 13577867 = 20366801) B20366801
theorem B9047699 : Blo 1786094 9047699 := bstep (se 1 (by rfl) ⟨6785774, by rfl⟩ : syracuseStep 9047699 = 13571549) B13571549
theorem B6033095 : Blo 1786094 6033095 := bstep (se 1 (by rfl) ⟨4524821, by rfl⟩ : syracuseStep 6033095 = 9049643) B9049643
theorem B43462433 : Blo 1786094 43462433 := bstep (se 2 (by rfl) ⟨16298412, by rfl⟩ : syracuseStep 43462433 = 32596825) B32596825
theorem B9170731 : Blo 1786094 9170731 := bstep (se 1 (by rfl) ⟨6878048, by rfl⟩ : syracuseStep 9170731 = 13756097) B13756097
theorem B2863031 : Blo 1786094 2863031 := bstep (se 1 (by rfl) ⟨2147273, by rfl⟩ : syracuseStep 2863031 = 4294547) B4294547
theorem B2011099 : Blo 1786094 2011099 := bstep (se 1 (by rfl) ⟨1508324, by rfl⟩ : syracuseStep 2011099 = 3016649) B3016649
theorem B4354055 : Blo 1786094 4354055 := bstep (se 1 (by rfl) ⟨3265541, by rfl⟩ : syracuseStep 4354055 = 6531083) B6531083
theorem B3444947 : Blo 1786094 3444947 := bstep (se 1 (by rfl) ⟨2583710, by rfl⟩ : syracuseStep 3444947 = 5167421) B5167421
theorem B17166653 : Blo 1786094 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B6787415 : Blo 1786094 6787415 := bstep (se 1 (by rfl) ⟨5090561, by rfl⟩ : syracuseStep 6787415 = 10181123) B10181123
theorem B2543977 : Blo 1786094 2543977 := bstep (se 2 (by rfl) ⟨953991, by rfl⟩ : syracuseStep 2543977 = 1907983) B1907983
theorem B2011567 : Blo 1786094 2011567 := bstep (se 1 (by rfl) ⟨1508675, by rfl⟩ : syracuseStep 2011567 = 3017351) B3017351
theorem B8155673 : Blo 1786094 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B6033959 : Blo 1786094 6033959 := bstep (se 1 (by rfl) ⟨4525469, by rfl⟩ : syracuseStep 6033959 = 9050939) B9050939
theorem B6034067 : Blo 1786094 6034067 := bstep (se 1 (by rfl) ⟨4525550, by rfl⟩ : syracuseStep 6034067 = 9051101) B9051101
theorem B4019039 : Blo 1786094 4019039 := bstep (se 1 (by rfl) ⟨3014279, by rfl⟩ : syracuseStep 4019039 = 6028559) B6028559
theorem B5722987 : Blo 1786094 5722987 := bstep (se 1 (by rfl) ⟨4292240, by rfl⟩ : syracuseStep 5722987 = 8584481) B8584481
theorem B6034283 : Blo 1786094 6034283 := bstep (se 1 (by rfl) ⟨4525712, by rfl⟩ : syracuseStep 6034283 = 9051425) B9051425
theorem B12882833 : Blo 1786094 12882833 := bstep (se 2 (by rfl) ⟨4831062, by rfl⟩ : syracuseStep 12882833 = 9662125) B9662125
theorem B6034337 : Blo 1786094 6034337 := bstep (se 2 (by rfl) ⟨2262876, by rfl⟩ : syracuseStep 6034337 = 4525753) B4525753
theorem B28980143 : Blo 1786094 28980143 := bstep (se 1 (by rfl) ⟨21735107, by rfl⟩ : syracuseStep 28980143 = 43470215) B43470215
theorem B5436335 : Blo 1786094 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B4019219 : Blo 1786094 4019219 := bstep (se 1 (by rfl) ⟨3014414, by rfl⟩ : syracuseStep 4019219 = 6028829) B6028829
theorem B12883063 : Blo 1786094 12883063 := bstep (se 1 (by rfl) ⟨9662297, by rfl⟩ : syracuseStep 12883063 = 19324595) B19324595
theorem B19576079 : Blo 1786094 19576079 := bstep (se 1 (by rfl) ⟨14682059, by rfl⟩ : syracuseStep 19576079 = 29364119) B29364119
theorem B4019561 : Blo 1786094 4019561 := bstep (se 2 (by rfl) ⟨1507335, by rfl⟩ : syracuseStep 4019561 = 3014671) B3014671
theorem B51533171 : Blo 1786094 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B11449765 : Blo 1786094 11449765 := bstep (se 4 (by rfl) ⟨1073415, by rfl⟩ : syracuseStep 11449765 = 2146831) B2146831
theorem B47052251 : Blo 1786094 47052251 := bstep (se 1 (by rfl) ⟨35289188, by rfl⟩ : syracuseStep 47052251 = 70578377) B70578377
theorem B3815009 : Blo 1786094 3815009 := bstep (se 2 (by rfl) ⟨1430628, by rfl⟩ : syracuseStep 3815009 = 2861257) B2861257
theorem B7345799 : Blo 1786094 7345799 := bstep (se 1 (by rfl) ⟨5509349, by rfl⟩ : syracuseStep 7345799 = 11018699) B11018699
theorem B4020155 : Blo 1786094 4020155 := bstep (se 1 (by rfl) ⟨3015116, by rfl⟩ : syracuseStep 4020155 = 6030233) B6030233
theorem B4020281 : Blo 1786094 4020281 := bstep (se 2 (by rfl) ⟨1507605, by rfl⟩ : syracuseStep 4020281 = 3015211) B3015211
theorem B10319987 : Blo 1786094 10319987 := bstep (se 1 (by rfl) ⟨7739990, by rfl⟩ : syracuseStep 10319987 = 15479981) B15479981
theorem B6437207 : Blo 1786094 6437207 := bstep (se 1 (by rfl) ⟨4827905, by rfl⟩ : syracuseStep 6437207 = 9655811) B9655811
theorem B4020623 : Blo 1786094 4020623 := bstep (se 1 (by rfl) ⟨3015467, by rfl⟩ : syracuseStep 4020623 = 6030935) B6030935
theorem B3439111 : Blo 1786094 3439111 := bstep (se 1 (by rfl) ⟨2579333, by rfl⟩ : syracuseStep 3439111 = 5158667) B5158667
theorem B5724769 : Blo 1786094 5724769 := bstep (se 2 (by rfl) ⟨2146788, by rfl⟩ : syracuseStep 5724769 = 4293577) B4293577
theorem B4831841 : Blo 1786094 4831841 := bstep (se 2 (by rfl) ⟨1811940, by rfl⟩ : syracuseStep 4831841 = 3623881) B3623881
theorem B41286323 : Blo 1786094 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B5159623 : Blo 1786094 5159623 := bstep (se 1 (by rfl) ⟨3869717, by rfl⟩ : syracuseStep 5159623 = 7739435) B7739435
theorem B4020947 : Blo 1786094 4020947 := bstep (se 1 (by rfl) ⟨3015710, by rfl⟩ : syracuseStep 4020947 = 6031421) B6031421
theorem B8592131 : Blo 1786094 8592131 := bstep (se 1 (by rfl) ⟨6444098, by rfl⟩ : syracuseStep 8592131 = 12888197) B12888197
theorem B13564745 : Blo 1786094 13564745 := bstep (se 2 (by rfl) ⟨5086779, by rfl⟩ : syracuseStep 13564745 = 10173559) B10173559
theorem B24468317 : Blo 1786094 24468317 := bstep (se 3 (by rfl) ⟨4587809, by rfl⟩ : syracuseStep 24468317 = 9175619) B9175619
theorem B6028127 : Blo 1786094 6028127 := bstep (se 1 (by rfl) ⟨4521095, by rfl⟩ : syracuseStep 6028127 = 9042191) B9042191
theorem B6028289 : Blo 1786094 6028289 := bstep (se 2 (by rfl) ⟨2260608, by rfl⟩ : syracuseStep 6028289 = 4521217) B4521217
theorem B21748931 : Blo 1786094 21748931 := bstep (se 1 (by rfl) ⟨16311698, by rfl⟩ : syracuseStep 21748931 = 32623397) B32623397
theorem B62774509 : Blo 1786094 62774509 := bstep (se 3 (by rfl) ⟨11770220, by rfl⟩ : syracuseStep 62774509 = 23540441) B23540441
theorem B38640887 : Blo 1786094 38640887 := bstep (se 1 (by rfl) ⟨28980665, by rfl⟩ : syracuseStep 38640887 = 57961331) B57961331
theorem B24452387 : Blo 1786094 24452387 := bstep (se 1 (by rfl) ⟨18339290, by rfl⟩ : syracuseStep 24452387 = 36678581) B36678581
theorem B3390815 : Blo 1786094 3390815 := bstep (se 1 (by rfl) ⟨2543111, by rfl⟩ : syracuseStep 3390815 = 5086223) B5086223
theorem B9043325 : Blo 1786094 9043325 := bstep (se 3 (by rfl) ⟨1695623, by rfl⟩ : syracuseStep 9043325 = 3391247) B3391247
theorem B4521359 : Blo 1786094 4521359 := bstep (se 1 (by rfl) ⟨3391019, by rfl⟩ : syracuseStep 4521359 = 6782039) B6782039
theorem B20356595 : Blo 1786094 20356595 := bstep (se 1 (by rfl) ⟨15267446, by rfl⟩ : syracuseStep 20356595 = 30534893) B30534893
theorem B38665795 : Blo 1786094 38665795 := bstep (se 1 (by rfl) ⟨28999346, by rfl⟩ : syracuseStep 38665795 = 57998693) B57998693
theorem B4021883 : Blo 1786094 4021883 := bstep (se 1 (by rfl) ⟨3016412, by rfl⟩ : syracuseStep 4021883 = 6032825) B6032825
theorem B12877501 : Blo 1786094 12877501 := bstep (se 3 (by rfl) ⟨2414531, by rfl⟩ : syracuseStep 12877501 = 4829063) B4829063
theorem B4521683 : Blo 1786094 4521683 := bstep (se 1 (by rfl) ⟨3391262, by rfl⟩ : syracuseStep 4521683 = 6782525) B6782525
theorem B7634681 : Blo 1786094 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B4022009 : Blo 1786094 4022009 := bstep (se 2 (by rfl) ⟨1508253, by rfl⟩ : syracuseStep 4022009 = 3016507) B3016507
theorem B6029099 : Blo 1786094 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B5881643 : Blo 1786094 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3014543 : Blo 1786094 3014543 := bstep (se 1 (by rfl) ⟨2260907, by rfl⟩ : syracuseStep 3014543 = 4521815) B4521815
theorem B10461089 : Blo 1786094 10461089 := bstep (se 2 (by rfl) ⟨3922908, by rfl⟩ : syracuseStep 10461089 = 7845817) B7845817
theorem B11452535 : Blo 1786094 11452535 := bstep (se 1 (by rfl) ⟨8589401, by rfl⟩ : syracuseStep 11452535 = 17178803) B17178803
theorem B11444435 : Blo 1786094 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B3014921 : Blo 1786094 3014921 := bstep (se 2 (by rfl) ⟨1130595, by rfl⟩ : syracuseStep 3014921 = 2261191) B2261191
theorem B1786143 : Blo 1786094 1786143 := bstep (se 1 (by rfl) ⟨1339607, by rfl⟩ : syracuseStep 1786143 = 2679215) B2679215
theorem B2261287 : Blo 1786094 2261287 := bstep (se 1 (by rfl) ⟨1695965, by rfl⟩ : syracuseStep 2261287 = 3391931) B3391931
theorem B9044297 : Blo 1786094 9044297 := bstep (se 2 (by rfl) ⟨3391611, by rfl⟩ : syracuseStep 9044297 = 6783223) B6783223
theorem B1786203 : Blo 1786094 1786203 := bstep (se 1 (by rfl) ⟨1339652, by rfl⟩ : syracuseStep 1786203 = 2679305) B2679305
theorem B4522331 : Blo 1786094 4522331 := bstep (se 1 (by rfl) ⟨3391748, by rfl⟩ : syracuseStep 4522331 = 6783497) B6783497
theorem B1786223 : Blo 1786094 1786223 := bstep (se 1 (by rfl) ⟨1339667, by rfl⟩ : syracuseStep 1786223 = 2679335) B2679335
theorem B4522351 : Blo 1786094 4522351 := bstep (se 1 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 4522351 = 6783527) B6783527
theorem B4022639 : Blo 1786094 4022639 := bstep (se 1 (by rfl) ⟨3016979, by rfl⟩ : syracuseStep 4022639 = 6033959) B6033959
theorem B3621287 : Blo 1786094 3621287 := bstep (se 1 (by rfl) ⟨2715965, by rfl⟩ : syracuseStep 3621287 = 5431931) B5431931
theorem B1786279 : Blo 1786094 1786279 := bstep (se 1 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 1786279 = 2679419) B2679419
theorem B4293047 : Blo 1786094 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B4022711 : Blo 1786094 4022711 := bstep (se 1 (by rfl) ⟨3017033, by rfl⟩ : syracuseStep 4022711 = 6034067) B6034067
theorem B3391969 : Blo 1786094 3391969 := bstep (se 2 (by rfl) ⟨1271988, by rfl⟩ : syracuseStep 3391969 = 2543977) B2543977
theorem B1786363 : Blo 1786094 1786363 := bstep (se 1 (by rfl) ⟨1339772, by rfl⟩ : syracuseStep 1786363 = 2679545) B2679545
theorem B2679359 : Blo 1786094 2679359 := bstep (se 1 (by rfl) ⟨2009519, by rfl⟩ : syracuseStep 2679359 = 4019039) B4019039
theorem B1786431 : Blo 1786094 1786431 := bstep (se 1 (by rfl) ⟨1339823, by rfl⟩ : syracuseStep 1786431 = 2679647) B2679647
theorem B1786439 : Blo 1786094 1786439 := bstep (se 1 (by rfl) ⟨1339829, by rfl⟩ : syracuseStep 1786439 = 2679659) B2679659
theorem B4022855 : Blo 1786094 4022855 := bstep (se 1 (by rfl) ⟨3017141, by rfl⟩ : syracuseStep 4022855 = 6034283) B6034283
theorem B2261611 : Blo 1786094 2261611 := bstep (se 1 (by rfl) ⟨1696208, by rfl⟩ : syracuseStep 2261611 = 3392417) B3392417
theorem B4022891 : Blo 1786094 4022891 := bstep (se 1 (by rfl) ⟨3017168, by rfl⟩ : syracuseStep 4022891 = 6034337) B6034337
theorem B2679479 : Blo 1786094 2679479 := bstep (se 1 (by rfl) ⟨2009609, by rfl⟩ : syracuseStep 2679479 = 4019219) B4019219
theorem B1786591 : Blo 1786094 1786591 := bstep (se 1 (by rfl) ⟨1339943, by rfl⟩ : syracuseStep 1786591 = 2679887) B2679887
theorem B1786671 : Blo 1786094 1786671 := bstep (se 1 (by rfl) ⟨1340003, by rfl⟩ : syracuseStep 1786671 = 2680007) B2680007
theorem B2261839 : Blo 1786094 2261839 := bstep (se 1 (by rfl) ⟨1696379, by rfl⟩ : syracuseStep 2261839 = 3392759) B3392759
theorem B13050719 : Blo 1786094 13050719 := bstep (se 1 (by rfl) ⟨9788039, by rfl⟩ : syracuseStep 13050719 = 19576079) B19576079
theorem B2679707 : Blo 1786094 2679707 := bstep (se 1 (by rfl) ⟨2009780, by rfl⟩ : syracuseStep 2679707 = 4019561) B4019561
theorem B1786779 : Blo 1786094 1786779 := bstep (se 1 (by rfl) ⟨1340084, by rfl⟩ : syracuseStep 1786779 = 2680169) B2680169
theorem B1786831 : Blo 1786094 1786831 := bstep (se 1 (by rfl) ⟨1340123, by rfl⟩ : syracuseStep 1786831 = 2680247) B2680247
theorem B31368167 : Blo 1786094 31368167 := bstep (se 1 (by rfl) ⟨23526125, by rfl⟩ : syracuseStep 31368167 = 47052251) B47052251
theorem B1786855 : Blo 1786094 1786855 := bstep (se 1 (by rfl) ⟨1340141, by rfl⟩ : syracuseStep 1786855 = 2680283) B2680283
theorem B4522999 : Blo 1786094 4522999 := bstep (se 1 (by rfl) ⟨3392249, by rfl⟩ : syracuseStep 4522999 = 6784499) B6784499
theorem B3818639 : Blo 1786094 3818639 := bstep (se 1 (by rfl) ⟨2863979, by rfl⟩ : syracuseStep 3818639 = 5727959) B5727959
theorem B13567175 : Blo 1786094 13567175 := bstep (se 1 (by rfl) ⟨10175381, by rfl⟩ : syracuseStep 13567175 = 20350763) B20350763
theorem B3015913 : Blo 1786094 3015913 := bstep (se 2 (by rfl) ⟨1130967, by rfl⟩ : syracuseStep 3015913 = 2261935) B2261935
theorem B1787167 : Blo 1786094 1787167 := bstep (se 1 (by rfl) ⟨1340375, by rfl⟩ : syracuseStep 1787167 = 2680751) B2680751
theorem B3015967 : Blo 1786094 3015967 := bstep (se 1 (by rfl) ⟨2261975, by rfl⟩ : syracuseStep 3015967 = 4523951) B4523951
theorem B2680103 : Blo 1786094 2680103 := bstep (se 1 (by rfl) ⟨2010077, by rfl⟩ : syracuseStep 2680103 = 4020155) B4020155
theorem B4523303 : Blo 1786094 4523303 := bstep (se 1 (by rfl) ⟨3392477, by rfl⟩ : syracuseStep 4523303 = 6784955) B6784955
theorem B1787227 : Blo 1786094 1787227 := bstep (se 1 (by rfl) ⟨1340420, by rfl⟩ : syracuseStep 1787227 = 2680841) B2680841
theorem B1787247 : Blo 1786094 1787247 := bstep (se 1 (by rfl) ⟨1340435, by rfl⟩ : syracuseStep 1787247 = 2680871) B2680871
theorem B2680187 : Blo 1786094 2680187 := bstep (se 1 (by rfl) ⟨2010140, by rfl⟩ : syracuseStep 2680187 = 4020281) B4020281
theorem B1787303 : Blo 1786094 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B2680313 : Blo 1786094 2680313 := bstep (se 2 (by rfl) ⟨1005117, by rfl⟩ : syracuseStep 2680313 = 2010235) B2010235
theorem B1787387 : Blo 1786094 1787387 := bstep (se 1 (by rfl) ⟨1340540, by rfl⟩ : syracuseStep 1787387 = 2681081) B2681081
theorem B1787455 : Blo 1786094 1787455 := bstep (se 1 (by rfl) ⟨1340591, by rfl⟩ : syracuseStep 1787455 = 2681183) B2681183
theorem B1787463 : Blo 1786094 1787463 := bstep (se 1 (by rfl) ⟨1340597, by rfl⟩ : syracuseStep 1787463 = 2681195) B2681195
theorem B9045593 : Blo 1786094 9045593 := bstep (se 2 (by rfl) ⟨3392097, by rfl⟩ : syracuseStep 9045593 = 6784195) B6784195
theorem B2680415 : Blo 1786094 2680415 := bstep (se 1 (by rfl) ⟨2010311, by rfl⟩ : syracuseStep 2680415 = 4020623) B4020623
theorem B83699345 : Blo 1786094 83699345 := bstep (se 2 (by rfl) ⟨31387254, by rfl⟩ : syracuseStep 83699345 = 62774509) B62774509
theorem B3016379 : Blo 1786094 3016379 := bstep (se 1 (by rfl) ⟨2262284, by rfl⟩ : syracuseStep 3016379 = 4524569) B4524569
theorem B1787615 : Blo 1786094 1787615 := bstep (se 1 (by rfl) ⟨1340711, by rfl⟩ : syracuseStep 1787615 = 2681423) B2681423
theorem B3221227 : Blo 1786094 3221227 := bstep (se 1 (by rfl) ⟨2415920, by rfl⟩ : syracuseStep 3221227 = 4831841) B4831841
theorem B1787695 : Blo 1786094 1787695 := bstep (se 1 (by rfl) ⟨1340771, by rfl⟩ : syracuseStep 1787695 = 2681543) B2681543
theorem B2680631 : Blo 1786094 2680631 := bstep (se 1 (by rfl) ⟨2010473, by rfl⟩ : syracuseStep 2680631 = 4020947) B4020947
theorem B5728087 : Blo 1786094 5728087 := bstep (se 1 (by rfl) ⟨4296065, by rfl⟩ : syracuseStep 5728087 = 8592131) B8592131
theorem B4294529 : Blo 1786094 4294529 := bstep (se 2 (by rfl) ⟨1610448, by rfl⟩ : syracuseStep 4294529 = 3220897) B3220897
theorem B16312211 : Blo 1786094 16312211 := bstep (se 1 (by rfl) ⟨12234158, by rfl⟩ : syracuseStep 16312211 = 24468317) B24468317
theorem B1787803 : Blo 1786094 1787803 := bstep (se 1 (by rfl) ⟨1340852, by rfl⟩ : syracuseStep 1787803 = 2681705) B2681705
theorem B1787855 : Blo 1786094 1787855 := bstep (se 1 (by rfl) ⟨1340891, by rfl⟩ : syracuseStep 1787855 = 2681783) B2681783
theorem B1787879 : Blo 1786094 1787879 := bstep (se 1 (by rfl) ⟨1340909, by rfl⟩ : syracuseStep 1787879 = 2681819) B2681819
theorem B51554393 : Blo 1786094 51554393 := bstep (se 2 (by rfl) ⟨19332897, by rfl⟩ : syracuseStep 51554393 = 38665795) B38665795
theorem B2680937 : Blo 1786094 2680937 := bstep (se 2 (by rfl) ⟨1005351, by rfl⟩ : syracuseStep 2680937 = 2010703) B2010703
theorem B6785153 : Blo 1786094 6785153 := bstep (se 2 (by rfl) ⟨2544432, by rfl⟩ : syracuseStep 6785153 = 5088865) B5088865
theorem B22022543 : Blo 1786094 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B2681255 : Blo 1786094 2681255 := bstep (se 1 (by rfl) ⟨2010941, by rfl⟩ : syracuseStep 2681255 = 4021883) B4021883
theorem B6031799 : Blo 1786094 6031799 := bstep (se 1 (by rfl) ⟨4523849, by rfl⟩ : syracuseStep 6031799 = 9047699) B9047699
theorem B5089787 : Blo 1786094 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B2681339 : Blo 1786094 2681339 := bstep (se 1 (by rfl) ⟨2011004, by rfl⟩ : syracuseStep 2681339 = 4022009) B4022009
theorem B2009695 : Blo 1786094 2009695 := bstep (se 1 (by rfl) ⟨1507271, by rfl⟩ : syracuseStep 2009695 = 3014543) B3014543
theorem B6974059 : Blo 1786094 6974059 := bstep (se 1 (by rfl) ⟨5230544, by rfl⟩ : syracuseStep 6974059 = 10461089) B10461089
theorem B2681465 : Blo 1786094 2681465 := bstep (se 2 (by rfl) ⟨1005549, by rfl⟩ : syracuseStep 2681465 = 2011099) B2011099
theorem B2681519 : Blo 1786094 2681519 := bstep (se 1 (by rfl) ⟨2011139, by rfl⟩ : syracuseStep 2681519 = 4022279) B4022279
theorem B2681567 : Blo 1786094 2681567 := bstep (se 1 (by rfl) ⟨2011175, by rfl⟩ : syracuseStep 2681567 = 4022351) B4022351
theorem B46443253 : Blo 1786094 46443253 := bstep (se 5 (by rfl) ⟨2177027, by rfl⟩ : syracuseStep 46443253 = 4354055) B4354055
theorem B2296631 : Blo 1786094 2296631 := bstep (se 1 (by rfl) ⟨1722473, by rfl⟩ : syracuseStep 2296631 = 3444947) B3444947
theorem B4524943 : Blo 1786094 4524943 := bstep (se 1 (by rfl) ⟨3393707, by rfl⟩ : syracuseStep 4524943 = 6787415) B6787415
theorem B2681831 : Blo 1786094 2681831 := bstep (se 1 (by rfl) ⟨2011373, by rfl⟩ : syracuseStep 2681831 = 4022747) B4022747
theorem B2682089 : Blo 1786094 2682089 := bstep (se 2 (by rfl) ⟨1005783, by rfl⟩ : syracuseStep 2682089 = 2011567) B2011567
theorem B8588555 : Blo 1786094 8588555 := bstep (se 1 (by rfl) ⟨6441416, by rfl⟩ : syracuseStep 8588555 = 12882833) B12882833
theorem B19320095 : Blo 1786094 19320095 := bstep (se 1 (by rfl) ⟨14490071, by rfl⟩ : syracuseStep 19320095 = 28980143) B28980143
theorem B4525409 : Blo 1786094 4525409 := bstep (se 2 (by rfl) ⟨1697028, by rfl⟩ : syracuseStep 4525409 = 3394057) B3394057
theorem B9924179 : Blo 1786094 9924179 := bstep (se 1 (by rfl) ⟨7443134, by rfl⟩ : syracuseStep 9924179 = 14886269) B14886269
theorem B2010847 : Blo 1786094 2010847 := bstep (se 1 (by rfl) ⟨1508135, by rfl⟩ : syracuseStep 2010847 = 3016271) B3016271
theorem B2543339 : Blo 1786094 2543339 := bstep (se 1 (by rfl) ⟨1907504, by rfl⟩ : syracuseStep 2543339 = 3815009) B3815009
theorem B4525865 : Blo 1786094 4525865 := bstep (se 2 (by rfl) ⟨1697199, by rfl⟩ : syracuseStep 4525865 = 3394399) B3394399
theorem B7630649 : Blo 1786094 7630649 := bstep (se 2 (by rfl) ⟨2861493, by rfl⟩ : syracuseStep 7630649 = 5722987) B5722987
theorem B6787097 : Blo 1786094 6787097 := bstep (se 2 (by rfl) ⟨2545161, by rfl⟩ : syracuseStep 6787097 = 5090323) B5090323
theorem B14495915 : Blo 1786094 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B2011423 : Blo 1786094 2011423 := bstep (se 1 (by rfl) ⟨1508567, by rfl⟩ : syracuseStep 2011423 = 3017135) B3017135
theorem B15266353 : Blo 1786094 15266353 := bstep (se 2 (by rfl) ⟨5724882, by rfl⟩ : syracuseStep 15266353 = 11449765) B11449765
theorem B4018751 : Blo 1786094 4018751 := bstep (se 1 (by rfl) ⟨3014063, by rfl⟩ : syracuseStep 4018751 = 6028127) B6028127
theorem B2863723 : Blo 1786094 2863723 := bstep (se 1 (by rfl) ⟨2147792, by rfl⟩ : syracuseStep 2863723 = 4295585) B4295585
theorem B4018859 : Blo 1786094 4018859 := bstep (se 1 (by rfl) ⟨3014144, by rfl⟩ : syracuseStep 4018859 = 6028289) B6028289
theorem B13759175 : Blo 1786094 13759175 := bstep (se 1 (by rfl) ⟨10319381, by rfl⟩ : syracuseStep 13759175 = 20638763) B20638763
theorem B4895507 : Blo 1786094 4895507 := bstep (se 1 (by rfl) ⟨3671630, by rfl⟩ : syracuseStep 4895507 = 7343261) B7343261
theorem B25760591 : Blo 1786094 25760591 := bstep (se 1 (by rfl) ⟨19320443, by rfl⟩ : syracuseStep 25760591 = 38640887) B38640887
theorem B13571063 : Blo 1786094 13571063 := bstep (se 1 (by rfl) ⟨10178297, by rfl⟩ : syracuseStep 13571063 = 20356595) B20356595
theorem B12227641 : Blo 1786094 12227641 := bstep (se 2 (by rfl) ⟨4585365, by rfl⟩ : syracuseStep 12227641 = 9170731) B9170731
theorem B14496893 : Blo 1786094 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B4019399 : Blo 1786094 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B3921095 : Blo 1786094 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B4830457 : Blo 1786094 4830457 := bstep (se 2 (by rfl) ⟨1811421, by rfl⟩ : syracuseStep 4830457 = 3622843) B3622843
theorem B4019579 : Blo 1786094 4019579 := bstep (se 1 (by rfl) ⟨3014684, by rfl⟩ : syracuseStep 4019579 = 6029369) B6029369
theorem B5658017 : Blo 1786094 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B4830653 : Blo 1786094 4830653 := bstep (se 3 (by rfl) ⟨905747, by rfl⟩ : syracuseStep 4830653 = 1811495) B1811495
theorem B4019705 : Blo 1786094 4019705 := bstep (se 2 (by rfl) ⟨1507389, by rfl⟩ : syracuseStep 4019705 = 3014779) B3014779
theorem B4019795 : Blo 1786094 4019795 := bstep (se 1 (by rfl) ⟨3014846, by rfl⟩ : syracuseStep 4019795 = 6029693) B6029693
theorem B5437115 : Blo 1786094 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B4019975 : Blo 1786094 4019975 := bstep (se 1 (by rfl) ⟨3014981, by rfl⟩ : syracuseStep 4019975 = 6029963) B6029963
theorem B2545463 : Blo 1786094 2545463 := bstep (se 1 (by rfl) ⟨1909097, by rfl⟩ : syracuseStep 2545463 = 3818195) B3818195
theorem B13948901 : Blo 1786094 13948901 := bstep (se 4 (by rfl) ⟨1307709, by rfl⟩ : syracuseStep 13948901 = 2615419) B2615419
theorem B4585481 : Blo 1786094 4585481 := bstep (se 2 (by rfl) ⟨1719555, by rfl⟩ : syracuseStep 4585481 = 3439111) B3439111
theorem B7633025 : Blo 1786094 7633025 := bstep (se 2 (by rfl) ⟨2862384, by rfl⟩ : syracuseStep 7633025 = 5724769) B5724769
theorem B34355447 : Blo 1786094 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B6879497 : Blo 1786094 6879497 := bstep (se 2 (by rfl) ⟨2579811, by rfl⟩ : syracuseStep 6879497 = 5159623) B5159623
theorem B4020587 : Blo 1786094 4020587 := bstep (se 1 (by rfl) ⟨3015440, by rfl⟩ : syracuseStep 4020587 = 6030881) B6030881
theorem B4897199 : Blo 1786094 4897199 := bstep (se 1 (by rfl) ⟨3672899, by rfl⟩ : syracuseStep 4897199 = 7345799) B7345799
theorem B39156149 : Blo 1786094 39156149 := bstep (se 5 (by rfl) ⟨1835444, by rfl⟩ : syracuseStep 39156149 = 3670889) B3670889
theorem B3815905 : Blo 1786094 3815905 := bstep (se 2 (by rfl) ⟨1430964, by rfl⟩ : syracuseStep 3815905 = 2861929) B2861929
theorem B4020731 : Blo 1786094 4020731 := bstep (se 1 (by rfl) ⟨3015548, by rfl⟩ : syracuseStep 4020731 = 6031097) B6031097
theorem B4020857 : Blo 1786094 4020857 := bstep (se 2 (by rfl) ⟨1507821, by rfl⟩ : syracuseStep 4020857 = 3015643) B3015643
theorem B4020911 : Blo 1786094 4020911 := bstep (se 1 (by rfl) ⟨3015683, by rfl⟩ : syracuseStep 4020911 = 6031367) B6031367
theorem B4020983 : Blo 1786094 4020983 := bstep (se 1 (by rfl) ⟨3015737, by rfl⟩ : syracuseStep 4020983 = 6031475) B6031475
theorem B6879991 : Blo 1786094 6879991 := bstep (se 1 (by rfl) ⟨5159993, by rfl⟩ : syracuseStep 6879991 = 10319987) B10319987
theorem B17177417 : Blo 1786094 17177417 := bstep (se 2 (by rfl) ⟨6441531, by rfl⟩ : syracuseStep 17177417 = 12883063) B12883063
theorem B4291471 : Blo 1786094 4291471 := bstep (se 1 (by rfl) ⟨3218603, by rfl⟩ : syracuseStep 4291471 = 6437207) B6437207
theorem B13573007 : Blo 1786094 13573007 := bstep (se 1 (by rfl) ⟨10179755, by rfl⟩ : syracuseStep 13573007 = 20359511) B20359511
theorem B4021163 : Blo 1786094 4021163 := bstep (se 1 (by rfl) ⟨3015872, by rfl⟩ : syracuseStep 4021163 = 6031745) B6031745
theorem B27524215 : Blo 1786094 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B9043163 : Blo 1786094 9043163 := bstep (se 1 (by rfl) ⟨6782372, by rfl⟩ : syracuseStep 9043163 = 13564745) B13564745
theorem B10173833 : Blo 1786094 10173833 := bstep (se 2 (by rfl) ⟨3815187, by rfl⟩ : syracuseStep 10173833 = 7630375) B7630375
theorem B5160329 : Blo 1786094 5160329 := bstep (se 2 (by rfl) ⟨1935123, by rfl⟩ : syracuseStep 5160329 = 3870247) B3870247
theorem B4021703 : Blo 1786094 4021703 := bstep (se 1 (by rfl) ⟨3016277, by rfl⟩ : syracuseStep 4021703 = 6032555) B6032555
theorem B14499287 : Blo 1786094 14499287 := bstep (se 1 (by rfl) ⟨10874465, by rfl⟩ : syracuseStep 14499287 = 21748931) B21748931
theorem B16301591 : Blo 1786094 16301591 := bstep (se 1 (by rfl) ⟨12226193, by rfl⟩ : syracuseStep 16301591 = 24452387) B24452387
theorem B2260543 : Blo 1786094 2260543 := bstep (se 1 (by rfl) ⟨1695407, by rfl⟩ : syracuseStep 2260543 = 3390815) B3390815
theorem B17170001 : Blo 1786094 17170001 := bstep (se 2 (by rfl) ⟨6438750, by rfl⟩ : syracuseStep 17170001 = 12877501) B12877501
theorem B6028883 : Blo 1786094 6028883 := bstep (se 1 (by rfl) ⟨4521662, by rfl⟩ : syracuseStep 6028883 = 9043325) B9043325
theorem B3014239 : Blo 1786094 3014239 := bstep (se 1 (by rfl) ⟨2260679, by rfl⟩ : syracuseStep 3014239 = 4521359) B4521359
theorem B12885599 : Blo 1786094 12885599 := bstep (se 1 (by rfl) ⟨9664199, by rfl⟩ : syracuseStep 12885599 = 19328399) B19328399
theorem B9051911 : Blo 1786094 9051911 := bstep (se 1 (by rfl) ⟨6788933, by rfl⟩ : syracuseStep 9051911 = 13577867) B13577867
theorem B4022063 : Blo 1786094 4022063 := bstep (se 1 (by rfl) ⟨3016547, by rfl⟩ : syracuseStep 4022063 = 6033095) B6033095
theorem B3014455 : Blo 1786094 3014455 := bstep (se 1 (by rfl) ⟨2260841, by rfl⟩ : syracuseStep 3014455 = 4521683) B4521683
theorem B7634749 : Blo 1786094 7634749 := bstep (se 3 (by rfl) ⟨1431515, by rfl⟩ : syracuseStep 7634749 = 2863031) B2863031
theorem B28974955 : Blo 1786094 28974955 := bstep (se 1 (by rfl) ⟨21731216, by rfl⟩ : syracuseStep 28974955 = 43462433) B43462433
theorem B7635023 : Blo 1786094 7635023 := bstep (se 1 (by rfl) ⟨5726267, by rfl⟩ : syracuseStep 7635023 = 11452535) B11452535
theorem B6029531 : Blo 1786094 6029531 := bstep (se 1 (by rfl) ⟨4522148, by rfl⟩ : syracuseStep 6029531 = 9044297) B9044297
theorem B3014887 : Blo 1786094 3014887 := bstep (se 1 (by rfl) ⟨2261165, by rfl⟩ : syracuseStep 3014887 = 4522331) B4522331
theorem B2679167 : Blo 1786094 2679167 := bstep (se 1 (by rfl) ⟨2009375, by rfl⟩ : syracuseStep 2679167 = 4018751) B4018751
theorem B1786239 : Blo 1786094 1786239 := bstep (se 1 (by rfl) ⟨1339679, by rfl⟩ : syracuseStep 1786239 = 2679359) B2679359
theorem B3015049 : Blo 1786094 3015049 := bstep (se 2 (by rfl) ⟨1130643, by rfl⟩ : syracuseStep 3015049 = 2261287) B2261287
theorem B2679239 : Blo 1786094 2679239 := bstep (se 1 (by rfl) ⟨2009429, by rfl⟩ : syracuseStep 2679239 = 4018859) B4018859
theorem B1786319 : Blo 1786094 1786319 := bstep (se 1 (by rfl) ⟨1339739, by rfl⟩ : syracuseStep 1786319 = 2679479) B2679479
theorem B6029801 : Blo 1786094 6029801 := bstep (se 2 (by rfl) ⟨2261175, by rfl⟩ : syracuseStep 6029801 = 4522351) B4522351
theorem B8700479 : Blo 1786094 8700479 := bstep (se 1 (by rfl) ⟨6525359, by rfl⟩ : syracuseStep 8700479 = 13050719) B13050719
theorem B1786471 : Blo 1786094 1786471 := bstep (se 1 (by rfl) ⟨1339853, by rfl⟩ : syracuseStep 1786471 = 2679707) B2679707
theorem B5087873 : Blo 1786094 5087873 := bstep (se 2 (by rfl) ⟨1907952, by rfl⟩ : syracuseStep 5087873 = 3815905) B3815905
theorem B4522625 : Blo 1786094 4522625 := bstep (se 2 (by rfl) ⟨1695984, by rfl⟩ : syracuseStep 4522625 = 3391969) B3391969
theorem B2679593 : Blo 1786094 2679593 := bstep (se 2 (by rfl) ⟨1004847, by rfl⟩ : syracuseStep 2679593 = 2009695) B2009695
theorem B2679599 : Blo 1786094 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B9044783 : Blo 1786094 9044783 := bstep (se 1 (by rfl) ⟨6783587, by rfl⟩ : syracuseStep 9044783 = 13567175) B13567175
theorem B3015481 : Blo 1786094 3015481 := bstep (se 2 (by rfl) ⟨1130805, by rfl⟩ : syracuseStep 3015481 = 2261611) B2261611
theorem B9298745 : Blo 1786094 9298745 := bstep (se 2 (by rfl) ⟨3487029, by rfl⟩ : syracuseStep 9298745 = 6974059) B6974059
theorem B3818297 : Blo 1786094 3818297 := bstep (se 2 (by rfl) ⟨1431861, by rfl⟩ : syracuseStep 3818297 = 2863723) B2863723
theorem B1786735 : Blo 1786094 1786735 := bstep (se 1 (by rfl) ⟨1340051, by rfl⟩ : syracuseStep 1786735 = 2680103) B2680103
theorem B3015535 : Blo 1786094 3015535 := bstep (se 1 (by rfl) ⟨2261651, by rfl⟩ : syracuseStep 3015535 = 4523303) B4523303
theorem B2679719 : Blo 1786094 2679719 := bstep (se 1 (by rfl) ⟨2009789, by rfl⟩ : syracuseStep 2679719 = 4019579) B4019579
theorem B1786791 : Blo 1786094 1786791 := bstep (se 1 (by rfl) ⟨1340093, by rfl⟩ : syracuseStep 1786791 = 2680187) B2680187
theorem B3220435 : Blo 1786094 3220435 := bstep (se 1 (by rfl) ⟨2415326, by rfl⟩ : syracuseStep 3220435 = 4830653) B4830653
theorem B61924337 : Blo 1786094 61924337 := bstep (se 2 (by rfl) ⟨23221626, by rfl⟩ : syracuseStep 61924337 = 46443253) B46443253
theorem B2679803 : Blo 1786094 2679803 := bstep (se 1 (by rfl) ⟨2009852, by rfl⟩ : syracuseStep 2679803 = 4019705) B4019705
theorem B1786875 : Blo 1786094 1786875 := bstep (se 1 (by rfl) ⟨1340156, by rfl⟩ : syracuseStep 1786875 = 2680313) B2680313
theorem B2679863 : Blo 1786094 2679863 := bstep (se 1 (by rfl) ⟨2009897, by rfl⟩ : syracuseStep 2679863 = 4019795) B4019795
theorem B6030395 : Blo 1786094 6030395 := bstep (se 1 (by rfl) ⟨4522796, by rfl⟩ : syracuseStep 6030395 = 9045593) B9045593
theorem B1786943 : Blo 1786094 1786943 := bstep (se 1 (by rfl) ⟨1340207, by rfl⟩ : syracuseStep 1786943 = 2680415) B2680415
theorem B3015785 : Blo 1786094 3015785 := bstep (se 2 (by rfl) ⟨1130919, by rfl⟩ : syracuseStep 3015785 = 2261839) B2261839
theorem B2679983 : Blo 1786094 2679983 := bstep (se 1 (by rfl) ⟨2009987, by rfl⟩ : syracuseStep 2679983 = 4019975) B4019975
theorem B1787087 : Blo 1786094 1787087 := bstep (se 1 (by rfl) ⟨1340315, by rfl⟩ : syracuseStep 1787087 = 2680631) B2680631
theorem B17179877 : Blo 1786094 17179877 := bstep (se 4 (by rfl) ⟨1610613, by rfl⟩ : syracuseStep 17179877 = 3221227) B3221227
theorem B9299267 : Blo 1786094 9299267 := bstep (se 1 (by rfl) ⟨6974450, by rfl⟩ : syracuseStep 9299267 = 13948901) B13948901
theorem B6030665 : Blo 1786094 6030665 := bstep (se 2 (by rfl) ⟨2261499, by rfl⟩ : syracuseStep 6030665 = 4522999) B4522999
theorem B3056987 : Blo 1786094 3056987 := bstep (se 1 (by rfl) ⟨2292740, by rfl⟩ : syracuseStep 3056987 = 4585481) B4585481
theorem B1787291 : Blo 1786094 1787291 := bstep (se 1 (by rfl) ⟨1340468, by rfl⟩ : syracuseStep 1787291 = 2680937) B2680937
theorem B5088683 : Blo 1786094 5088683 := bstep (se 1 (by rfl) ⟨3816512, by rfl⟩ : syracuseStep 5088683 = 7633025) B7633025
theorem B4523435 : Blo 1786094 4523435 := bstep (se 1 (by rfl) ⟨3392576, by rfl⟩ : syracuseStep 4523435 = 6785153) B6785153
theorem B55043509 : Blo 1786094 55043509 := bstep (se 5 (by rfl) ⟨2580164, by rfl⟩ : syracuseStep 55043509 = 5160329) B5160329
theorem B2680391 : Blo 1786094 2680391 := bstep (se 1 (by rfl) ⟨2010293, by rfl⟩ : syracuseStep 2680391 = 4020587) B4020587
theorem B14681695 : Blo 1786094 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B1787503 : Blo 1786094 1787503 := bstep (se 1 (by rfl) ⟨1340627, by rfl⟩ : syracuseStep 1787503 = 2681255) B2681255
theorem B6440609 : Blo 1786094 6440609 := bstep (se 2 (by rfl) ⟨2415228, by rfl⟩ : syracuseStep 6440609 = 4830457) B4830457
theorem B2680487 : Blo 1786094 2680487 := bstep (se 1 (by rfl) ⟨2010365, by rfl⟩ : syracuseStep 2680487 = 4020731) B4020731
theorem B3393191 : Blo 1786094 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B1787559 : Blo 1786094 1787559 := bstep (se 1 (by rfl) ⟨1340669, by rfl⟩ : syracuseStep 1787559 = 2681339) B2681339
theorem B2680571 : Blo 1786094 2680571 := bstep (se 1 (by rfl) ⟨2010428, by rfl⟩ : syracuseStep 2680571 = 4020857) B4020857
theorem B1787643 : Blo 1786094 1787643 := bstep (se 1 (by rfl) ⟨1340732, by rfl⟩ : syracuseStep 1787643 = 2681465) B2681465
theorem B2680607 : Blo 1786094 2680607 := bstep (se 1 (by rfl) ⟨2010455, by rfl⟩ : syracuseStep 2680607 = 4020911) B4020911
theorem B1787679 : Blo 1786094 1787679 := bstep (se 1 (by rfl) ⟨1340759, by rfl⟩ : syracuseStep 1787679 = 2681519) B2681519
theorem B1787711 : Blo 1786094 1787711 := bstep (se 1 (by rfl) ⟨1340783, by rfl⟩ : syracuseStep 1787711 = 2681567) B2681567
theorem B2680655 : Blo 1786094 2680655 := bstep (se 1 (by rfl) ⟨2010491, by rfl⟩ : syracuseStep 2680655 = 4020983) B4020983
theorem B2680775 : Blo 1786094 2680775 := bstep (se 1 (by rfl) ⟨2010581, by rfl⟩ : syracuseStep 2680775 = 4021163) B4021163
theorem B1787887 : Blo 1786094 1787887 := bstep (se 1 (by rfl) ⟨1340915, by rfl⟩ : syracuseStep 1787887 = 2681831) B2681831
theorem B1788059 : Blo 1786094 1788059 := bstep (se 1 (by rfl) ⟨1341044, by rfl⟩ : syracuseStep 1788059 = 2682089) B2682089
theorem B12880063 : Blo 1786094 12880063 := bstep (se 1 (by rfl) ⟨9660047, by rfl⟩ : syracuseStep 12880063 = 19320095) B19320095
theorem B3016939 : Blo 1786094 3016939 := bstep (se 1 (by rfl) ⟨2262704, by rfl⟩ : syracuseStep 3016939 = 4525409) B4525409
theorem B2681129 : Blo 1786094 2681129 := bstep (se 2 (by rfl) ⟨1005423, by rfl⟩ : syracuseStep 2681129 = 2010847) B2010847
theorem B2681135 : Blo 1786094 2681135 := bstep (se 1 (by rfl) ⟨2010851, by rfl⟩ : syracuseStep 2681135 = 4021703) B4021703
theorem B11446667 : Blo 1786094 11446667 := bstep (se 1 (by rfl) ⟨8585000, by rfl⟩ : syracuseStep 11446667 = 17170001) B17170001
theorem B7637449 : Blo 1786094 7637449 := bstep (se 2 (by rfl) ⟨2864043, by rfl⟩ : syracuseStep 7637449 = 5728087) B5728087
theorem B3017243 : Blo 1786094 3017243 := bstep (se 1 (by rfl) ⟨2262932, by rfl⟩ : syracuseStep 3017243 = 4525865) B4525865
theorem B2681375 : Blo 1786094 2681375 := bstep (se 1 (by rfl) ⟨2011031, by rfl⟩ : syracuseStep 2681375 = 4022063) B4022063
theorem B4524731 : Blo 1786094 4524731 := bstep (se 1 (by rfl) ⟨3393548, by rfl⟩ : syracuseStep 4524731 = 6787097) B6787097
theorem B7629623 : Blo 1786094 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B2009947 : Blo 1786094 2009947 := bstep (se 1 (by rfl) ⟨1507460, by rfl⟩ : syracuseStep 2009947 = 3014921) B3014921
theorem B2681759 : Blo 1786094 2681759 := bstep (se 1 (by rfl) ⟨2011319, by rfl⟩ : syracuseStep 2681759 = 4022639) B4022639
theorem B2681807 : Blo 1786094 2681807 := bstep (se 1 (by rfl) ⟨2011355, by rfl⟩ : syracuseStep 2681807 = 4022711) B4022711
theorem B2681897 : Blo 1786094 2681897 := bstep (se 2 (by rfl) ⟨1005711, by rfl⟩ : syracuseStep 2681897 = 2011423) B2011423
theorem B2681903 : Blo 1786094 2681903 := bstep (se 1 (by rfl) ⟨2011427, by rfl⟩ : syracuseStep 2681903 = 4022855) B4022855
theorem B2681927 : Blo 1786094 2681927 := bstep (se 1 (by rfl) ⟨2011445, by rfl⟩ : syracuseStep 2681927 = 4022891) B4022891
theorem B3263671 : Blo 1786094 3263671 := bstep (se 1 (by rfl) ⟨2447753, by rfl⟩ : syracuseStep 3263671 = 4895507) B4895507
theorem B10456253 : Blo 1786094 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B17173727 : Blo 1786094 17173727 := bstep (se 1 (by rfl) ⟨12880295, by rfl⟩ : syracuseStep 17173727 = 25760591) B25760591
theorem B146795813 : Blo 1786094 146795813 := bstep (se 4 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 146795813 = 27524215) B27524215
theorem B9047375 : Blo 1786094 9047375 := bstep (se 1 (by rfl) ⟨6785531, by rfl⟩ : syracuseStep 9047375 = 13571063) B13571063
theorem B55799563 : Blo 1786094 55799563 := bstep (se 1 (by rfl) ⟨41849672, by rfl⟩ : syracuseStep 55799563 = 83699345) B83699345
theorem B2010919 : Blo 1786094 2010919 := bstep (se 1 (by rfl) ⟨1508189, by rfl⟩ : syracuseStep 2010919 = 3016379) B3016379
theorem B3624743 : Blo 1786094 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B11448125 : Blo 1786094 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B6033257 : Blo 1786094 6033257 := bstep (se 2 (by rfl) ⟨2262471, by rfl⟩ : syracuseStep 6033257 = 4524943) B4524943
theorem B2863019 : Blo 1786094 2863019 := bstep (se 1 (by rfl) ⟨2147264, by rfl⟩ : syracuseStep 2863019 = 4294529) B4294529
theorem B10874807 : Blo 1786094 10874807 := bstep (se 1 (by rfl) ⟨8156105, by rfl⟩ : syracuseStep 10874807 = 16312211) B16312211
theorem B34369595 : Blo 1786094 34369595 := bstep (se 1 (by rfl) ⟨25777196, by rfl⟩ : syracuseStep 34369595 = 51554393) B51554393
theorem B26464477 : Blo 1786094 26464477 := bstep (se 3 (by rfl) ⟨4962089, by rfl⟩ : syracuseStep 26464477 = 9924179) B9924179
theorem B34361597 : Blo 1786094 34361597 := bstep (se 3 (by rfl) ⟨6442799, by rfl⟩ : syracuseStep 34361597 = 12885599) B12885599
theorem B3264799 : Blo 1786094 3264799 := bstep (se 1 (by rfl) ⟨2448599, by rfl⟩ : syracuseStep 3264799 = 4897199) B4897199
theorem B26104099 : Blo 1786094 26104099 := bstep (se 1 (by rfl) ⟨19578074, by rfl⟩ : syracuseStep 26104099 = 39156149) B39156149
theorem B9048671 : Blo 1786094 9048671 := bstep (se 1 (by rfl) ⟨6786503, by rfl⟩ : syracuseStep 9048671 = 13573007) B13573007
theorem B4018985 : Blo 1786094 4018985 := bstep (se 2 (by rfl) ⟨1507119, by rfl⟩ : syracuseStep 4018985 = 3014239) B3014239
theorem B6124349 : Blo 1786094 6124349 := bstep (se 3 (by rfl) ⟨1148315, by rfl⟩ : syracuseStep 6124349 = 2296631) B2296631
theorem B6787901 : Blo 1786094 6787901 := bstep (se 3 (by rfl) ⟨1272731, by rfl⟩ : syracuseStep 6787901 = 2545463) B2545463
theorem B10867727 : Blo 1786094 10867727 := bstep (se 1 (by rfl) ⟨8150795, by rfl⟩ : syracuseStep 10867727 = 16301591) B16301591
theorem B4019255 : Blo 1786094 4019255 := bstep (se 1 (by rfl) ⟨3014441, by rfl⟩ : syracuseStep 4019255 = 6028883) B6028883
theorem B4019273 : Blo 1786094 4019273 := bstep (se 2 (by rfl) ⟨1507227, by rfl⟩ : syracuseStep 4019273 = 3014455) B3014455
theorem B10179665 : Blo 1786094 10179665 := bstep (se 2 (by rfl) ⟨3817374, by rfl⟩ : syracuseStep 10179665 = 7634749) B7634749
theorem B6034607 : Blo 1786094 6034607 := bstep (se 1 (by rfl) ⟨4525955, by rfl⟩ : syracuseStep 6034607 = 9051911) B9051911
theorem B73381301 : Blo 1786094 73381301 := bstep (se 5 (by rfl) ⟨3439748, by rfl⟩ : syracuseStep 73381301 = 6879497) B6879497
theorem B9663943 : Blo 1786094 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B2414191 : Blo 1786094 2414191 := bstep (se 1 (by rfl) ⟨1810643, by rfl⟩ : syracuseStep 2414191 = 3621287) B3621287
theorem B65214085 : Blo 1786094 65214085 := bstep (se 4 (by rfl) ⟨6113820, by rfl⟩ : syracuseStep 65214085 = 12227641) B12227641
theorem B9172783 : Blo 1786094 9172783 := bstep (se 1 (by rfl) ⟨6879587, by rfl⟩ : syracuseStep 9172783 = 13759175) B13759175
theorem B20912111 : Blo 1786094 20912111 := bstep (se 1 (by rfl) ⟨15684083, by rfl⟩ : syracuseStep 20912111 = 31368167) B31368167
theorem B20355137 : Blo 1786094 20355137 := bstep (se 2 (by rfl) ⟨7633176, by rfl⟩ : syracuseStep 20355137 = 15266353) B15266353
theorem B9664595 : Blo 1786094 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B2545759 : Blo 1786094 2545759 := bstep (se 1 (by rfl) ⟨1909319, by rfl⟩ : syracuseStep 2545759 = 3818639) B3818639
theorem B9173321 : Blo 1786094 9173321 := bstep (se 2 (by rfl) ⟨3439995, by rfl⟩ : syracuseStep 9173321 = 6879991) B6879991
theorem B15088045 : Blo 1786094 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B22903631 : Blo 1786094 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B4021199 : Blo 1786094 4021199 := bstep (se 1 (by rfl) ⟨3015899, by rfl⟩ : syracuseStep 4021199 = 6031799) B6031799
theorem B4021217 : Blo 1786094 4021217 := bstep (se 2 (by rfl) ⟨1507956, by rfl⟩ : syracuseStep 4021217 = 3015913) B3015913
theorem B4021289 : Blo 1786094 4021289 := bstep (se 2 (by rfl) ⟨1507983, by rfl⟩ : syracuseStep 4021289 = 3015967) B3015967
theorem B11451611 : Blo 1786094 11451611 := bstep (se 1 (by rfl) ⟨8588708, by rfl⟩ : syracuseStep 11451611 = 17177417) B17177417
theorem B6782237 : Blo 1786094 6782237 := bstep (se 3 (by rfl) ⟨1271669, by rfl⟩ : syracuseStep 6782237 = 2543339) B2543339
theorem B22887845 : Blo 1786094 22887845 := bstep (se 4 (by rfl) ⟨2145735, by rfl⟩ : syracuseStep 22887845 = 4291471) B4291471
theorem B3014057 : Blo 1786094 3014057 := bstep (se 2 (by rfl) ⟨1130271, by rfl⟩ : syracuseStep 3014057 = 2260543) B2260543
theorem B6028775 : Blo 1786094 6028775 := bstep (se 1 (by rfl) ⟨4521581, by rfl⟩ : syracuseStep 6028775 = 9043163) B9043163
theorem B5725703 : Blo 1786094 5725703 := bstep (se 1 (by rfl) ⟨4294277, by rfl⟩ : syracuseStep 5725703 = 8588555) B8588555
theorem B6782555 : Blo 1786094 6782555 := bstep (se 1 (by rfl) ⟨5086916, by rfl⟩ : syracuseStep 6782555 = 10173833) B10173833
theorem B9666191 : Blo 1786094 9666191 := bstep (se 1 (by rfl) ⟨7249643, by rfl⟩ : syracuseStep 9666191 = 14499287) B14499287
theorem B38633273 : Blo 1786094 38633273 := bstep (se 2 (by rfl) ⟨14487477, by rfl⟩ : syracuseStep 38633273 = 28974955) B28974955
theorem B5087099 : Blo 1786094 5087099 := bstep (se 1 (by rfl) ⟨3815324, by rfl⟩ : syracuseStep 5087099 = 7630649) B7630649
theorem B22913063 : Blo 1786094 22913063 := bstep (se 1 (by rfl) ⟨17184797, by rfl⟩ : syracuseStep 22913063 = 34369595) B34369595
theorem B1786111 : Blo 1786094 1786111 := bstep (se 1 (by rfl) ⟨1339583, by rfl⟩ : syracuseStep 1786111 = 2679167) B2679167
theorem B1786159 : Blo 1786094 1786159 := bstep (se 1 (by rfl) ⟨1339619, by rfl⟩ : syracuseStep 1786159 = 2679239) B2679239
theorem B4022585 : Blo 1786094 4022585 := bstep (se 2 (by rfl) ⟨1508469, by rfl⟩ : syracuseStep 4022585 = 3016939) B3016939
theorem B5800319 : Blo 1786094 5800319 := bstep (se 1 (by rfl) ⟨4350239, by rfl⟩ : syracuseStep 5800319 = 8700479) B8700479
theorem B3015083 : Blo 1786094 3015083 := bstep (se 1 (by rfl) ⟨2261312, by rfl⟩ : syracuseStep 3015083 = 4522625) B4522625
theorem B2679323 : Blo 1786094 2679323 := bstep (se 1 (by rfl) ⟨2009492, by rfl⟩ : syracuseStep 2679323 = 4018985) B4018985
theorem B1786395 : Blo 1786094 1786395 := bstep (se 1 (by rfl) ⟨1339796, by rfl⟩ : syracuseStep 1786395 = 2679593) B2679593
theorem B1786399 : Blo 1786094 1786399 := bstep (se 1 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 1786399 = 2679599) B2679599
theorem B6029855 : Blo 1786094 6029855 := bstep (se 1 (by rfl) ⟨4522391, by rfl⟩ : syracuseStep 6029855 = 9044783) B9044783
theorem B10183265 : Blo 1786094 10183265 := bstep (se 2 (by rfl) ⟨3818724, by rfl⟩ : syracuseStep 10183265 = 7637449) B7637449
theorem B1786479 : Blo 1786094 1786479 := bstep (se 1 (by rfl) ⟨1339859, by rfl⟩ : syracuseStep 1786479 = 2679719) B2679719
theorem B1786535 : Blo 1786094 1786535 := bstep (se 1 (by rfl) ⟨1339901, by rfl⟩ : syracuseStep 1786535 = 2679803) B2679803
theorem B2679503 : Blo 1786094 2679503 := bstep (se 1 (by rfl) ⟨2009627, by rfl⟩ : syracuseStep 2679503 = 4019255) B4019255
theorem B1786575 : Blo 1786094 1786575 := bstep (se 1 (by rfl) ⟨1339931, by rfl⟩ : syracuseStep 1786575 = 2679863) B2679863
theorem B2679515 : Blo 1786094 2679515 := bstep (se 1 (by rfl) ⟨2009636, by rfl⟩ : syracuseStep 2679515 = 4019273) B4019273
theorem B1786655 : Blo 1786094 1786655 := bstep (se 1 (by rfl) ⟨1339991, by rfl⟩ : syracuseStep 1786655 = 2679983) B2679983
theorem B4023071 : Blo 1786094 4023071 := bstep (se 1 (by rfl) ⟨3017303, by rfl⟩ : syracuseStep 4023071 = 6034607) B6034607
theorem B11453251 : Blo 1786094 11453251 := bstep (se 1 (by rfl) ⟨8589938, by rfl⟩ : syracuseStep 11453251 = 17179877) B17179877
theorem B3392455 : Blo 1786094 3392455 := bstep (se 1 (by rfl) ⟨2544341, by rfl⟩ : syracuseStep 3392455 = 5088683) B5088683
theorem B3015623 : Blo 1786094 3015623 := bstep (se 1 (by rfl) ⟨2261717, by rfl⟩ : syracuseStep 3015623 = 4523435) B4523435
theorem B1786927 : Blo 1786094 1786927 := bstep (se 1 (by rfl) ⟨1340195, by rfl⟩ : syracuseStep 1786927 = 2680391) B2680391
theorem B4293739 : Blo 1786094 4293739 := bstep (se 1 (by rfl) ⟨3220304, by rfl⟩ : syracuseStep 4293739 = 6440609) B6440609
theorem B1786991 : Blo 1786094 1786991 := bstep (se 1 (by rfl) ⟨1340243, by rfl⟩ : syracuseStep 1786991 = 2680487) B2680487
theorem B2679929 : Blo 1786094 2679929 := bstep (se 2 (by rfl) ⟨1004973, by rfl⟩ : syracuseStep 2679929 = 2009947) B2009947
theorem B1787047 : Blo 1786094 1787047 := bstep (se 1 (by rfl) ⟨1340285, by rfl⟩ : syracuseStep 1787047 = 2680571) B2680571
theorem B1787071 : Blo 1786094 1787071 := bstep (se 1 (by rfl) ⟨1340303, by rfl⟩ : syracuseStep 1787071 = 2680607) B2680607
theorem B1787103 : Blo 1786094 1787103 := bstep (se 1 (by rfl) ⟨1340327, by rfl⟩ : syracuseStep 1787103 = 2680655) B2680655
theorem B4293913 : Blo 1786094 4293913 := bstep (se 2 (by rfl) ⟨1610217, by rfl⟩ : syracuseStep 4293913 = 3220435) B3220435
theorem B1787183 : Blo 1786094 1787183 := bstep (se 1 (by rfl) ⟨1340387, by rfl⟩ : syracuseStep 1787183 = 2680775) B2680775
theorem B1787419 : Blo 1786094 1787419 := bstep (se 1 (by rfl) ⟨1340564, by rfl⟩ : syracuseStep 1787419 = 2681129) B2681129
theorem B1787423 : Blo 1786094 1787423 := bstep (se 1 (by rfl) ⟨1340567, by rfl⟩ : syracuseStep 1787423 = 2681135) B2681135
theorem B13567661 : Blo 1786094 13567661 := bstep (se 3 (by rfl) ⟨2543936, by rfl⟩ : syracuseStep 13567661 = 5087873) B5087873
theorem B1787583 : Blo 1786094 1787583 := bstep (se 1 (by rfl) ⟨1340687, by rfl⟩ : syracuseStep 1787583 = 2681375) B2681375
theorem B3016487 : Blo 1786094 3016487 := bstep (se 1 (by rfl) ⟨2262365, by rfl⟩ : syracuseStep 3016487 = 4524731) B4524731
theorem B1787839 : Blo 1786094 1787839 := bstep (se 1 (by rfl) ⟨1340879, by rfl⟩ : syracuseStep 1787839 = 2681759) B2681759
theorem B2680799 : Blo 1786094 2680799 := bstep (se 1 (by rfl) ⟨2010599, by rfl⟩ : syracuseStep 2680799 = 4021199) B4021199
theorem B1787871 : Blo 1786094 1787871 := bstep (se 1 (by rfl) ⟨1340903, by rfl⟩ : syracuseStep 1787871 = 2681807) B2681807
theorem B2680811 : Blo 1786094 2680811 := bstep (se 1 (by rfl) ⟨2010608, by rfl⟩ : syracuseStep 2680811 = 4021217) B4021217
theorem B2680859 : Blo 1786094 2680859 := bstep (se 1 (by rfl) ⟨2010644, by rfl⟩ : syracuseStep 2680859 = 4021289) B4021289
theorem B1787931 : Blo 1786094 1787931 := bstep (se 1 (by rfl) ⟨1340948, by rfl⟩ : syracuseStep 1787931 = 2681897) B2681897
theorem B1787935 : Blo 1786094 1787935 := bstep (se 1 (by rfl) ⟨1340951, by rfl⟩ : syracuseStep 1787935 = 2681903) B2681903
theorem B1787951 : Blo 1786094 1787951 := bstep (se 1 (by rfl) ⟨1340963, by rfl⟩ : syracuseStep 1787951 = 2681927) B2681927
theorem B86952113 : Blo 1786094 86952113 := bstep (se 2 (by rfl) ⟨32607042, by rfl⟩ : syracuseStep 86952113 = 65214085) B65214085
theorem B97863875 : Blo 1786094 97863875 := bstep (se 1 (by rfl) ⟨73397906, by rfl⟩ : syracuseStep 97863875 = 146795813) B146795813
theorem B6031583 : Blo 1786094 6031583 := bstep (se 1 (by rfl) ⟨4523687, by rfl⟩ : syracuseStep 6031583 = 9047375) B9047375
theorem B2009371 : Blo 1786094 2009371 := bstep (se 1 (by rfl) ⟨1507028, by rfl⟩ : syracuseStep 2009371 = 3014057) B3014057
theorem B2681225 : Blo 1786094 2681225 := bstep (se 2 (by rfl) ⟨1005459, by rfl⟩ : syracuseStep 2681225 = 2010919) B2010919
theorem B5090015 : Blo 1786094 5090015 := bstep (se 1 (by rfl) ⟨3817511, by rfl⟩ : syracuseStep 5090015 = 7635023) B7635023
theorem B22907731 : Blo 1786094 22907731 := bstep (se 1 (by rfl) ⟨17180798, by rfl⟩ : syracuseStep 22907731 = 34361597) B34361597
theorem B35285969 : Blo 1786094 35285969 := bstep (se 2 (by rfl) ⟨13232238, by rfl⟩ : syracuseStep 35285969 = 26464477) B26464477
theorem B4353065 : Blo 1786094 4353065 := bstep (se 2 (by rfl) ⟨1632399, by rfl⟩ : syracuseStep 4353065 = 3264799) B3264799
theorem B6032447 : Blo 1786094 6032447 := bstep (se 1 (by rfl) ⟨4524335, by rfl⟩ : syracuseStep 6032447 = 9048671) B9048671
theorem B13577381 : Blo 1786094 13577381 := bstep (se 4 (by rfl) ⟨1272879, by rfl⟩ : syracuseStep 13577381 = 2545759) B2545759
theorem B4082899 : Blo 1786094 4082899 := bstep (se 1 (by rfl) ⟨3062174, by rfl⟩ : syracuseStep 4082899 = 6124349) B6124349
theorem B4525267 : Blo 1786094 4525267 := bstep (se 1 (by rfl) ⟨3393950, by rfl⟩ : syracuseStep 4525267 = 6787901) B6787901
theorem B41282891 : Blo 1786094 41282891 := bstep (se 1 (by rfl) ⟨30962168, by rfl⟩ : syracuseStep 41282891 = 61924337) B61924337
theorem B6786443 : Blo 1786094 6786443 := bstep (se 1 (by rfl) ⟨5089832, by rfl⟩ : syracuseStep 6786443 = 10179665) B10179665
theorem B2010523 : Blo 1786094 2010523 := bstep (se 1 (by rfl) ⟨1507892, by rfl⟩ : syracuseStep 2010523 = 3015785) B3015785
theorem B68693669 : Blo 1786094 68693669 := bstep (se 4 (by rfl) ⟨6440031, by rfl⟩ : syracuseStep 68693669 = 12880063) B12880063
theorem B13570091 : Blo 1786094 13570091 := bstep (se 1 (by rfl) ⟨10177568, by rfl⟩ : syracuseStep 13570091 = 20355137) B20355137
theorem B6443063 : Blo 1786094 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B6115547 : Blo 1786094 6115547 := bstep (se 1 (by rfl) ⟨4586660, by rfl⟩ : syracuseStep 6115547 = 9173321) B9173321
theorem B7631111 : Blo 1786094 7631111 := bstep (se 1 (by rfl) ⟨5723333, by rfl⟩ : syracuseStep 7631111 = 11446667) B11446667
theorem B2011495 : Blo 1786094 2011495 := bstep (se 1 (by rfl) ⟨1508621, by rfl⟩ : syracuseStep 2011495 = 3017243) B3017243
theorem B9048509 : Blo 1786094 9048509 := bstep (se 3 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 9048509 = 3393191) B3393191
theorem B19575593 : Blo 1786094 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B11449151 : Blo 1786094 11449151 := bstep (se 1 (by rfl) ⟨8586863, by rfl⟩ : syracuseStep 11449151 = 17173727) B17173727
theorem B15258563 : Blo 1786094 15258563 := bstep (se 1 (by rfl) ⟨11443922, by rfl⟩ : syracuseStep 15258563 = 22887845) B22887845
theorem B4019183 : Blo 1786094 4019183 := bstep (se 1 (by rfl) ⟨3014387, by rfl⟩ : syracuseStep 4019183 = 6028775) B6028775
theorem B6444127 : Blo 1786094 6444127 := bstep (se 1 (by rfl) ⟨4833095, by rfl⟩ : syracuseStep 6444127 = 9666191) B9666191
theorem B7632083 : Blo 1786094 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B28980605 : Blo 1786094 28980605 := bstep (se 3 (by rfl) ⟨5433863, by rfl⟩ : syracuseStep 28980605 = 10867727) B10867727
theorem B4019687 : Blo 1786094 4019687 := bstep (se 1 (by rfl) ⟨3014765, by rfl⟩ : syracuseStep 4019687 = 6029531) B6029531
theorem B4019849 : Blo 1786094 4019849 := bstep (se 2 (by rfl) ⟨1507443, by rfl⟩ : syracuseStep 4019849 = 3014887) B3014887
theorem B4019867 : Blo 1786094 4019867 := bstep (se 1 (by rfl) ⟨3014900, by rfl⟩ : syracuseStep 4019867 = 6029801) B6029801
theorem B34805465 : Blo 1786094 34805465 := bstep (se 2 (by rfl) ⟨13052049, by rfl⟩ : syracuseStep 34805465 = 26104099) B26104099
theorem B4020065 : Blo 1786094 4020065 := bstep (se 2 (by rfl) ⟨1507524, by rfl⟩ : syracuseStep 4020065 = 3015049) B3015049
theorem B6199163 : Blo 1786094 6199163 := bstep (se 1 (by rfl) ⟨4649372, by rfl⟩ : syracuseStep 6199163 = 9298745) B9298745
theorem B20117393 : Blo 1786094 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B4020263 : Blo 1786094 4020263 := bstep (se 1 (by rfl) ⟨3015197, by rfl⟩ : syracuseStep 4020263 = 6030395) B6030395
theorem B6199511 : Blo 1786094 6199511 := bstep (se 1 (by rfl) ⟨4649633, by rfl⟩ : syracuseStep 6199511 = 9299267) B9299267
theorem B4020443 : Blo 1786094 4020443 := bstep (se 1 (by rfl) ⟨3015332, by rfl⟩ : syracuseStep 4020443 = 6030665) B6030665
theorem B2037991 : Blo 1786094 2037991 := bstep (se 1 (by rfl) ⟨1528493, by rfl⟩ : syracuseStep 2037991 = 3056987) B3056987
theorem B48920867 : Blo 1786094 48920867 := bstep (se 1 (by rfl) ⟨36690650, by rfl⟩ : syracuseStep 48920867 = 73381301) B73381301
theorem B17406245 : Blo 1786094 17406245 := bstep (se 4 (by rfl) ⟨1631835, by rfl⟩ : syracuseStep 17406245 = 3263671) B3263671
theorem B4020641 : Blo 1786094 4020641 := bstep (se 2 (by rfl) ⟨1507740, by rfl⟩ : syracuseStep 4020641 = 3015481) B3015481
theorem B4020713 : Blo 1786094 4020713 := bstep (se 2 (by rfl) ⟨1507767, by rfl⟩ : syracuseStep 4020713 = 3015535) B3015535
theorem B13941407 : Blo 1786094 13941407 := bstep (se 1 (by rfl) ⟨10456055, by rfl⟩ : syracuseStep 13941407 = 20912111) B20912111
theorem B48921509 : Blo 1786094 48921509 := bstep (se 4 (by rfl) ⟨4586391, by rfl⟩ : syracuseStep 48921509 = 9172783) B9172783
theorem B5086415 : Blo 1786094 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B15269087 : Blo 1786094 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B73391345 : Blo 1786094 73391345 := bstep (se 2 (by rfl) ⟨27521754, by rfl⟩ : syracuseStep 73391345 = 55043509) B55043509
theorem B12885257 : Blo 1786094 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B6970835 : Blo 1786094 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B7634407 : Blo 1786094 7634407 := bstep (se 1 (by rfl) ⟨5725805, by rfl⟩ : syracuseStep 7634407 = 11451611) B11451611
theorem B3218921 : Blo 1786094 3218921 := bstep (se 2 (by rfl) ⟨1207095, by rfl⟩ : syracuseStep 3218921 = 2414191) B2414191
theorem B10182125 : Blo 1786094 10182125 := bstep (se 3 (by rfl) ⟨1909148, by rfl⟩ : syracuseStep 10182125 = 3818297) B3818297
theorem B4521491 : Blo 1786094 4521491 := bstep (se 1 (by rfl) ⟨3391118, by rfl⟩ : syracuseStep 4521491 = 6782237) B6782237
theorem B3817135 : Blo 1786094 3817135 := bstep (se 1 (by rfl) ⟨2862851, by rfl⟩ : syracuseStep 3817135 = 5725703) B5725703
theorem B74399417 : Blo 1786094 74399417 := bstep (se 2 (by rfl) ⟨27899781, by rfl⟩ : syracuseStep 74399417 = 55799563) B55799563
theorem B4521703 : Blo 1786094 4521703 := bstep (se 1 (by rfl) ⟨3391277, by rfl⟩ : syracuseStep 4521703 = 6782555) B6782555
theorem B2416495 : Blo 1786094 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B25755515 : Blo 1786094 25755515 := bstep (se 1 (by rfl) ⟨19316636, by rfl⟩ : syracuseStep 25755515 = 38633273) B38633273
theorem B4022171 : Blo 1786094 4022171 := bstep (se 1 (by rfl) ⟨3016628, by rfl⟩ : syracuseStep 4022171 = 6033257) B6033257
theorem B3391399 : Blo 1786094 3391399 := bstep (se 1 (by rfl) ⟨2543549, by rfl⟩ : syracuseStep 3391399 = 5087099) B5087099
theorem B1908679 : Blo 1786094 1908679 := bstep (se 1 (by rfl) ⟨1431509, by rfl⟩ : syracuseStep 1908679 = 2863019) B2863019
theorem B7249871 : Blo 1786094 7249871 := bstep (se 1 (by rfl) ⟨5437403, by rfl⟩ : syracuseStep 7249871 = 10874807) B10874807
theorem B5087407 : Blo 1786094 5087407 := bstep (se 1 (by rfl) ⟨3815555, by rfl⟩ : syracuseStep 5087407 = 7631111) B7631111
theorem B3866879 : Blo 1786094 3866879 := bstep (se 1 (by rfl) ⟨2900159, by rfl⟩ : syracuseStep 3866879 = 5800319) B5800319
theorem B1786215 : Blo 1786094 1786215 := bstep (se 1 (by rfl) ⟨1339661, by rfl⟩ : syracuseStep 1786215 = 2679323) B2679323
theorem B2679161 : Blo 1786094 2679161 := bstep (se 2 (by rfl) ⟨1004685, by rfl⟩ : syracuseStep 2679161 = 2009371) B2009371
theorem B1786335 : Blo 1786094 1786335 := bstep (se 1 (by rfl) ⟨1339751, by rfl⟩ : syracuseStep 1786335 = 2679503) B2679503
theorem B1786343 : Blo 1786094 1786343 := bstep (se 1 (by rfl) ⟨1339757, by rfl⟩ : syracuseStep 1786343 = 2679515) B2679515
theorem B13050395 : Blo 1786094 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B16532029 : Blo 1786094 16532029 := bstep (se 3 (by rfl) ⟨3099755, by rfl⟩ : syracuseStep 16532029 = 6199511) B6199511
theorem B2679455 : Blo 1786094 2679455 := bstep (se 1 (by rfl) ⟨2009591, by rfl⟩ : syracuseStep 2679455 = 4019183) B4019183
theorem B1786619 : Blo 1786094 1786619 := bstep (se 1 (by rfl) ⟨1339964, by rfl⟩ : syracuseStep 1786619 = 2679929) B2679929
theorem B20358053 : Blo 1786094 20358053 := bstep (se 4 (by rfl) ⟨1908567, by rfl⟩ : syracuseStep 20358053 = 3817135) B3817135
theorem B2679791 : Blo 1786094 2679791 := bstep (se 1 (by rfl) ⟨2009843, by rfl⟩ : syracuseStep 2679791 = 4019687) B4019687
theorem B15271001 : Blo 1786094 15271001 := bstep (se 2 (by rfl) ⟨5726625, by rfl⟩ : syracuseStep 15271001 = 11453251) B11453251
theorem B2679899 : Blo 1786094 2679899 := bstep (se 1 (by rfl) ⟨2009924, by rfl⟩ : syracuseStep 2679899 = 4019849) B4019849
theorem B2679911 : Blo 1786094 2679911 := bstep (se 1 (by rfl) ⟨2009933, by rfl⟩ : syracuseStep 2679911 = 4019867) B4019867
theorem B9045107 : Blo 1786094 9045107 := bstep (se 1 (by rfl) ⟨6783830, by rfl⟩ : syracuseStep 9045107 = 13567661) B13567661
theorem B2680043 : Blo 1786094 2680043 := bstep (se 1 (by rfl) ⟨2010032, by rfl⟩ : syracuseStep 2680043 = 4020065) B4020065
theorem B4523273 : Blo 1786094 4523273 := bstep (se 2 (by rfl) ⟨1696227, by rfl⟩ : syracuseStep 4523273 = 3392455) B3392455
theorem B13411595 : Blo 1786094 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B1787199 : Blo 1786094 1787199 := bstep (se 1 (by rfl) ⟨1340399, by rfl⟩ : syracuseStep 1787199 = 2680799) B2680799
theorem B1787207 : Blo 1786094 1787207 := bstep (se 1 (by rfl) ⟨1340405, by rfl⟩ : syracuseStep 1787207 = 2680811) B2680811
theorem B1787239 : Blo 1786094 1787239 := bstep (se 1 (by rfl) ⟨1340429, by rfl⟩ : syracuseStep 1787239 = 2680859) B2680859
theorem B2680175 : Blo 1786094 2680175 := bstep (se 1 (by rfl) ⟨2010131, by rfl⟩ : syracuseStep 2680175 = 4020263) B4020263
theorem B57968075 : Blo 1786094 57968075 := bstep (se 1 (by rfl) ⟨43476056, by rfl⟩ : syracuseStep 57968075 = 86952113) B86952113
theorem B65242583 : Blo 1786094 65242583 := bstep (se 1 (by rfl) ⟨48931937, by rfl⟩ : syracuseStep 65242583 = 97863875) B97863875
theorem B2680295 : Blo 1786094 2680295 := bstep (se 1 (by rfl) ⟨2010221, by rfl⟩ : syracuseStep 2680295 = 4020443) B4020443
theorem B32613911 : Blo 1786094 32613911 := bstep (se 1 (by rfl) ⟨24460433, by rfl⟩ : syracuseStep 32613911 = 48920867) B48920867
theorem B1787483 : Blo 1786094 1787483 := bstep (se 1 (by rfl) ⟨1340612, by rfl⟩ : syracuseStep 1787483 = 2681225) B2681225
theorem B2680427 : Blo 1786094 2680427 := bstep (se 1 (by rfl) ⟨2010320, by rfl⟩ : syracuseStep 2680427 = 4020641) B4020641
theorem B2680475 : Blo 1786094 2680475 := bstep (se 1 (by rfl) ⟨2010356, by rfl⟩ : syracuseStep 2680475 = 4020713) B4020713
theorem B3393343 : Blo 1786094 3393343 := bstep (se 1 (by rfl) ⟨2545007, by rfl⟩ : syracuseStep 3393343 = 5090015) B5090015
theorem B2680697 : Blo 1786094 2680697 := bstep (se 2 (by rfl) ⟨1005261, by rfl⟩ : syracuseStep 2680697 = 2010523) B2010523
theorem B32614339 : Blo 1786094 32614339 := bstep (se 1 (by rfl) ⟨24460754, by rfl⟩ : syracuseStep 32614339 = 48921509) B48921509
theorem B2902043 : Blo 1786094 2902043 := bstep (se 1 (by rfl) ⟨2176532, by rfl⟩ : syracuseStep 2902043 = 4353065) B4353065
theorem B4524295 : Blo 1786094 4524295 := bstep (se 1 (by rfl) ⟨3393221, by rfl⟩ : syracuseStep 4524295 = 6786443) B6786443
theorem B4647223 : Blo 1786094 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B45795779 : Blo 1786094 45795779 := bstep (se 1 (by rfl) ⟨34346834, by rfl⟩ : syracuseStep 45795779 = 68693669) B68693669
theorem B3221993 : Blo 1786094 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B94095917 : Blo 1786094 94095917 := bstep (se 3 (by rfl) ⟨17642984, by rfl⟩ : syracuseStep 94095917 = 35285969) B35285969
theorem B2681447 : Blo 1786094 2681447 := bstep (se 1 (by rfl) ⟨2011085, by rfl⟩ : syracuseStep 2681447 = 4022171) B4022171
theorem B9046727 : Blo 1786094 9046727 := bstep (se 1 (by rfl) ⟨6785045, by rfl⟩ : syracuseStep 9046727 = 13570091) B13570091
theorem B4295375 : Blo 1786094 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B2681723 : Blo 1786094 2681723 := bstep (se 1 (by rfl) ⟨2011292, by rfl⟩ : syracuseStep 2681723 = 4022585) B4022585
theorem B2010055 : Blo 1786094 2010055 := bstep (se 1 (by rfl) ⟨1507541, by rfl⟩ : syracuseStep 2010055 = 3015083) B3015083
theorem B6032339 : Blo 1786094 6032339 := bstep (se 1 (by rfl) ⟨4524254, by rfl⟩ : syracuseStep 6032339 = 9048509) B9048509
theorem B2681993 : Blo 1786094 2681993 := bstep (se 2 (by rfl) ⟨1005747, by rfl⟩ : syracuseStep 2681993 = 2011495) B2011495
theorem B2682047 : Blo 1786094 2682047 := bstep (se 1 (by rfl) ⟨2011535, by rfl⟩ : syracuseStep 2682047 = 4023071) B4023071
theorem B20352221 : Blo 1786094 20352221 := bstep (se 3 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 20352221 = 7632083) B7632083
theorem B22899941 : Blo 1786094 22899941 := bstep (se 4 (by rfl) ⟨2146869, by rfl⟩ : syracuseStep 22899941 = 4293739) B4293739
theorem B2010415 : Blo 1786094 2010415 := bstep (se 1 (by rfl) ⟨1507811, by rfl⟩ : syracuseStep 2010415 = 3015623) B3015623
theorem B19320403 : Blo 1786094 19320403 := bstep (se 1 (by rfl) ⟨14490302, by rfl⟩ : syracuseStep 19320403 = 28980605) B28980605
theorem B30543641 : Blo 1786094 30543641 := bstep (se 2 (by rfl) ⟨11453865, by rfl⟩ : syracuseStep 30543641 = 22907731) B22907731
theorem B23203643 : Blo 1786094 23203643 := bstep (se 1 (by rfl) ⟨17402732, by rfl⟩ : syracuseStep 23203643 = 34805465) B34805465
theorem B2010991 : Blo 1786094 2010991 := bstep (se 1 (by rfl) ⟨1508243, by rfl⟩ : syracuseStep 2010991 = 3016487) B3016487
theorem B4132775 : Blo 1786094 4132775 := bstep (se 1 (by rfl) ⟨3099581, by rfl⟩ : syracuseStep 4132775 = 6199163) B6199163
theorem B11604163 : Blo 1786094 11604163 := bstep (se 1 (by rfl) ⟨8703122, by rfl⟩ : syracuseStep 11604163 = 17406245) B17406245
theorem B5443865 : Blo 1786094 5443865 := bstep (se 2 (by rfl) ⟨2041449, by rfl⟩ : syracuseStep 5443865 = 4082899) B4082899
theorem B6033689 : Blo 1786094 6033689 := bstep (se 2 (by rfl) ⟨2262633, by rfl⟩ : syracuseStep 6033689 = 4525267) B4525267
theorem B9294271 : Blo 1786094 9294271 := bstep (se 1 (by rfl) ⟨6970703, by rfl⟩ : syracuseStep 9294271 = 13941407) B13941407
theorem B10179209 : Blo 1786094 10179209 := bstep (se 2 (by rfl) ⟨3817203, by rfl⟩ : syracuseStep 10179209 = 7634407) B7634407
theorem B10179391 : Blo 1786094 10179391 := bstep (se 1 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 10179391 = 15269087) B15269087
theorem B48927563 : Blo 1786094 48927563 := bstep (se 1 (by rfl) ⟨36695672, by rfl⟩ : syracuseStep 48927563 = 73391345) B73391345
theorem B8590171 : Blo 1786094 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B27521927 : Blo 1786094 27521927 := bstep (se 1 (by rfl) ⟨20641445, by rfl⟩ : syracuseStep 27521927 = 41282891) B41282891
theorem B6788083 : Blo 1786094 6788083 := bstep (se 1 (by rfl) ⟨5091062, by rfl⟩ : syracuseStep 6788083 = 10182125) B10182125
theorem B49599611 : Blo 1786094 49599611 := bstep (se 1 (by rfl) ⟨37199708, by rfl⟩ : syracuseStep 49599611 = 74399417) B74399417
theorem B2544905 : Blo 1786094 2544905 := bstep (se 2 (by rfl) ⟨954339, by rfl⟩ : syracuseStep 2544905 = 1908679) B1908679
theorem B15275375 : Blo 1786094 15275375 := bstep (se 1 (by rfl) ⟨11456531, by rfl⟩ : syracuseStep 15275375 = 22913063) B22913063
theorem B2717321 : Blo 1786094 2717321 := bstep (se 2 (by rfl) ⟨1018995, by rfl⟩ : syracuseStep 2717321 = 2037991) B2037991
theorem B4019903 : Blo 1786094 4019903 := bstep (se 1 (by rfl) ⟨3014927, by rfl⟩ : syracuseStep 4019903 = 6029855) B6029855
theorem B6788843 : Blo 1786094 6788843 := bstep (se 1 (by rfl) ⟨5091632, by rfl⟩ : syracuseStep 6788843 = 10183265) B10183265
theorem B13563773 : Blo 1786094 13563773 := bstep (se 3 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 13563773 = 5086415) B5086415
theorem B7632767 : Blo 1786094 7632767 := bstep (se 1 (by rfl) ⟨5724575, by rfl⟩ : syracuseStep 7632767 = 11449151) B11449151
theorem B16308125 : Blo 1786094 16308125 := bstep (se 3 (by rfl) ⟨3057773, by rfl⟩ : syracuseStep 16308125 = 6115547) B6115547
theorem B10172375 : Blo 1786094 10172375 := bstep (se 1 (by rfl) ⟨7629281, by rfl⟩ : syracuseStep 10172375 = 15258563) B15258563
theorem B8592169 : Blo 1786094 8592169 := bstep (se 2 (by rfl) ⟨3222063, by rfl⟩ : syracuseStep 8592169 = 6444127) B6444127
theorem B4021055 : Blo 1786094 4021055 := bstep (se 1 (by rfl) ⟨3015791, by rfl⟩ : syracuseStep 4021055 = 6031583) B6031583
theorem B5725217 : Blo 1786094 5725217 := bstep (se 2 (by rfl) ⟨2146956, by rfl⟩ : syracuseStep 5725217 = 4293913) B4293913
theorem B4021631 : Blo 1786094 4021631 := bstep (se 1 (by rfl) ⟨3016223, by rfl⟩ : syracuseStep 4021631 = 6032447) B6032447
theorem B9051587 : Blo 1786094 9051587 := bstep (se 1 (by rfl) ⟨6788690, by rfl⟩ : syracuseStep 9051587 = 13577381) B13577381
theorem B6028937 : Blo 1786094 6028937 := bstep (se 2 (by rfl) ⟨2260851, by rfl⟩ : syracuseStep 6028937 = 4521703) B4521703
theorem B2145947 : Blo 1786094 2145947 := bstep (se 1 (by rfl) ⟨1609460, by rfl⟩ : syracuseStep 2145947 = 3218921) B3218921
theorem B3014327 : Blo 1786094 3014327 := bstep (se 1 (by rfl) ⟨2260745, by rfl⟩ : syracuseStep 3014327 = 4521491) B4521491
theorem B19332989 : Blo 1786094 19332989 := bstep (se 3 (by rfl) ⟨3624935, by rfl⟩ : syracuseStep 19332989 = 7249871) B7249871
theorem B4521865 : Blo 1786094 4521865 := bstep (se 2 (by rfl) ⟨1695699, by rfl⟩ : syracuseStep 4521865 = 3391399) B3391399
theorem B17170343 : Blo 1786094 17170343 := bstep (se 1 (by rfl) ⟨12877757, by rfl⟩ : syracuseStep 17170343 = 25755515) B25755515
theorem B3629243 : Blo 1786094 3629243 := bstep (se 1 (by rfl) ⟨2721932, by rfl⟩ : syracuseStep 3629243 = 5443865) B5443865
theorem B4022459 : Blo 1786094 4022459 := bstep (se 1 (by rfl) ⟨3016844, by rfl⟩ : syracuseStep 4022459 = 6033689) B6033689
theorem B6783209 : Blo 1786094 6783209 := bstep (se 2 (by rfl) ⟨2543703, by rfl⟩ : syracuseStep 6783209 = 5087407) B5087407
theorem B1786107 : Blo 1786094 1786107 := bstep (se 1 (by rfl) ⟨1339580, by rfl⟩ : syracuseStep 1786107 = 2679161) B2679161
theorem B8700263 : Blo 1786094 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B1786303 : Blo 1786094 1786303 := bstep (se 1 (by rfl) ⟨1339727, by rfl⟩ : syracuseStep 1786303 = 2679455) B2679455
theorem B1786527 : Blo 1786094 1786527 := bstep (se 1 (by rfl) ⟨1339895, by rfl⟩ : syracuseStep 1786527 = 2679791) B2679791
theorem B1786599 : Blo 1786094 1786599 := bstep (se 1 (by rfl) ⟨1339949, by rfl⟩ : syracuseStep 1786599 = 2679899) B2679899
theorem B1786607 : Blo 1786094 1786607 := bstep (se 1 (by rfl) ⟨1339955, by rfl⟩ : syracuseStep 1786607 = 2679911) B2679911
theorem B6030071 : Blo 1786094 6030071 := bstep (se 1 (by rfl) ⟨4522553, by rfl⟩ : syracuseStep 6030071 = 9045107) B9045107
theorem B1786695 : Blo 1786094 1786695 := bstep (se 1 (by rfl) ⟨1340021, by rfl⟩ : syracuseStep 1786695 = 2680043) B2680043
theorem B3015515 : Blo 1786094 3015515 := bstep (se 1 (by rfl) ⟨2261636, by rfl⟩ : syracuseStep 3015515 = 4523273) B4523273
theorem B1786783 : Blo 1786094 1786783 := bstep (se 1 (by rfl) ⟨1340087, by rfl⟩ : syracuseStep 1786783 = 2680175) B2680175
theorem B10183583 : Blo 1786094 10183583 := bstep (se 1 (by rfl) ⟨7637687, by rfl⟩ : syracuseStep 10183583 = 15275375) B15275375
theorem B1786863 : Blo 1786094 1786863 := bstep (se 1 (by rfl) ⟨1340147, by rfl⟩ : syracuseStep 1786863 = 2680295) B2680295
theorem B21742607 : Blo 1786094 21742607 := bstep (se 1 (by rfl) ⟨16306955, by rfl⟩ : syracuseStep 21742607 = 32613911) B32613911
theorem B1786951 : Blo 1786094 1786951 := bstep (se 1 (by rfl) ⟨1340213, by rfl⟩ : syracuseStep 1786951 = 2680427) B2680427
theorem B1786983 : Blo 1786094 1786983 := bstep (se 1 (by rfl) ⟨1340237, by rfl⟩ : syracuseStep 1786983 = 2680475) B2680475
theorem B11453561 : Blo 1786094 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B2679935 : Blo 1786094 2679935 := bstep (se 1 (by rfl) ⟨2009951, by rfl⟩ : syracuseStep 2679935 = 4019903) B4019903
theorem B1787131 : Blo 1786094 1787131 := bstep (se 1 (by rfl) ⟨1340348, by rfl⟩ : syracuseStep 1787131 = 2680697) B2680697
theorem B5088511 : Blo 1786094 5088511 := bstep (se 1 (by rfl) ⟨3816383, by rfl⟩ : syracuseStep 5088511 = 7632767) B7632767
theorem B2680073 : Blo 1786094 2680073 := bstep (se 2 (by rfl) ⟨1005027, by rfl⟩ : syracuseStep 2680073 = 2010055) B2010055
theorem B10872083 : Blo 1786094 10872083 := bstep (se 1 (by rfl) ⟨8154062, by rfl⟩ : syracuseStep 10872083 = 16308125) B16308125
theorem B1934695 : Blo 1786094 1934695 := bstep (se 1 (by rfl) ⟨1451021, by rfl⟩ : syracuseStep 1934695 = 2902043) B2902043
theorem B2147995 : Blo 1786094 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B2680553 : Blo 1786094 2680553 := bstep (se 2 (by rfl) ⟨1005207, by rfl⟩ : syracuseStep 2680553 = 2010415) B2010415
theorem B1787631 : Blo 1786094 1787631 := bstep (se 1 (by rfl) ⟨1340723, by rfl⟩ : syracuseStep 1787631 = 2681447) B2681447
theorem B6031151 : Blo 1786094 6031151 := bstep (se 1 (by rfl) ⟨4523363, by rfl⟩ : syracuseStep 6031151 = 9046727) B9046727
theorem B2680703 : Blo 1786094 2680703 := bstep (se 1 (by rfl) ⟨2010527, by rfl⟩ : syracuseStep 2680703 = 4021055) B4021055
theorem B1787815 : Blo 1786094 1787815 := bstep (se 1 (by rfl) ⟨1340861, by rfl⟩ : syracuseStep 1787815 = 2681723) B2681723
theorem B1787995 : Blo 1786094 1787995 := bstep (se 1 (by rfl) ⟨1340996, by rfl⟩ : syracuseStep 1787995 = 2681993) B2681993
theorem B1788031 : Blo 1786094 1788031 := bstep (se 1 (by rfl) ⟨1341023, by rfl⟩ : syracuseStep 1788031 = 2682047) B2682047
theorem B13568147 : Blo 1786094 13568147 := bstep (se 1 (by rfl) ⟨10176110, by rfl⟩ : syracuseStep 13568147 = 20352221) B20352221
theorem B61876381 : Blo 1786094 61876381 := bstep (se 3 (by rfl) ⟨11601821, by rfl⟩ : syracuseStep 61876381 = 23203643) B23203643
theorem B2681087 : Blo 1786094 2681087 := bstep (se 1 (by rfl) ⟨2010815, by rfl⟩ : syracuseStep 2681087 = 4021631) B4021631
theorem B4524457 : Blo 1786094 4524457 := bstep (se 2 (by rfl) ⟨1696671, by rfl⟩ : syracuseStep 4524457 = 3393343) B3393343
theorem B11020733 : Blo 1786094 11020733 := bstep (se 3 (by rfl) ⟨2066387, by rfl⟩ : syracuseStep 11020733 = 4132775) B4132775
theorem B2009551 : Blo 1786094 2009551 := bstep (se 1 (by rfl) ⟨1507163, by rfl⟩ : syracuseStep 2009551 = 3014327) B3014327
theorem B2681321 : Blo 1786094 2681321 := bstep (se 2 (by rfl) ⟨1005495, by rfl⟩ : syracuseStep 2681321 = 2010991) B2010991
theorem B12888659 : Blo 1786094 12888659 := bstep (se 1 (by rfl) ⟨9666494, by rfl⟩ : syracuseStep 12888659 = 19332989) B19332989
theorem B43485785 : Blo 1786094 43485785 := bstep (se 2 (by rfl) ⟨16307169, by rfl⟩ : syracuseStep 43485785 = 32614339) B32614339
theorem B11446895 : Blo 1786094 11446895 := bstep (se 1 (by rfl) ⟨8585171, by rfl⟩ : syracuseStep 11446895 = 17170343) B17170343
theorem B6032393 : Blo 1786094 6032393 := bstep (se 2 (by rfl) ⟨2262147, by rfl⟩ : syracuseStep 6032393 = 4524295) B4524295
theorem B6786139 : Blo 1786094 6786139 := bstep (se 1 (by rfl) ⟨5089604, by rfl⟩ : syracuseStep 6786139 = 10179209) B10179209
theorem B6786413 : Blo 1786094 6786413 := bstep (se 3 (by rfl) ⟨1272452, by rfl⟩ : syracuseStep 6786413 = 2544905) B2544905
theorem B33066407 : Blo 1786094 33066407 := bstep (se 1 (by rfl) ⟨24799805, by rfl⟩ : syracuseStep 33066407 = 49599611) B49599611
theorem B38645383 : Blo 1786094 38645383 := bstep (se 1 (by rfl) ⟨28984037, by rfl⟩ : syracuseStep 38645383 = 57968075) B57968075
theorem B43495055 : Blo 1786094 43495055 := bstep (se 1 (by rfl) ⟨32621291, by rfl⟩ : syracuseStep 43495055 = 65242583) B65242583
theorem B11456225 : Blo 1786094 11456225 := bstep (se 2 (by rfl) ⟨4296084, by rfl⟩ : syracuseStep 11456225 = 8592169) B8592169
theorem B4525895 : Blo 1786094 4525895 := bstep (se 1 (by rfl) ⟨3394421, by rfl⟩ : syracuseStep 4525895 = 6788843) B6788843
theorem B24785189 : Blo 1786094 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B7246189 : Blo 1786094 7246189 := bstep (se 3 (by rfl) ⟨1358660, by rfl⟩ : syracuseStep 7246189 = 2717321) B2717321
theorem B62730611 : Blo 1786094 62730611 := bstep (se 1 (by rfl) ⟨47047958, by rfl⟩ : syracuseStep 62730611 = 94095917) B94095917
theorem B5722525 : Blo 1786094 5722525 := bstep (se 3 (by rfl) ⟨1072973, by rfl⟩ : syracuseStep 5722525 = 2145947) B2145947
theorem B2863583 : Blo 1786094 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B25760537 : Blo 1786094 25760537 := bstep (se 2 (by rfl) ⟨9660201, by rfl⟩ : syracuseStep 25760537 = 19320403) B19320403
theorem B15266627 : Blo 1786094 15266627 := bstep (se 1 (by rfl) ⟨11449970, by rfl⟩ : syracuseStep 15266627 = 22899941) B22899941
theorem B6034391 : Blo 1786094 6034391 := bstep (se 1 (by rfl) ⟨4525793, by rfl⟩ : syracuseStep 6034391 = 9051587) B9051587
theorem B4019291 : Blo 1786094 4019291 := bstep (se 1 (by rfl) ⟨3014468, by rfl⟩ : syracuseStep 4019291 = 6028937) B6028937
theorem B20362427 : Blo 1786094 20362427 := bstep (se 1 (by rfl) ⟨15271820, by rfl⟩ : syracuseStep 20362427 = 30543641) B30543641
theorem B2577919 : Blo 1786094 2577919 := bstep (se 1 (by rfl) ⟨1933439, by rfl⟩ : syracuseStep 2577919 = 3866879) B3866879
theorem B15472217 : Blo 1786094 15472217 := bstep (se 2 (by rfl) ⟨5802081, by rfl⟩ : syracuseStep 15472217 = 11604163) B11604163
theorem B32618375 : Blo 1786094 32618375 := bstep (se 1 (by rfl) ⟨24463781, by rfl⟩ : syracuseStep 32618375 = 48927563) B48927563
theorem B18347951 : Blo 1786094 18347951 := bstep (se 1 (by rfl) ⟨13760963, by rfl⟩ : syracuseStep 18347951 = 27521927) B27521927
theorem B13572035 : Blo 1786094 13572035 := bstep (se 1 (by rfl) ⟨10179026, by rfl⟩ : syracuseStep 13572035 = 20358053) B20358053
theorem B35764253 : Blo 1786094 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B10180667 : Blo 1786094 10180667 := bstep (se 1 (by rfl) ⟨7635500, by rfl⟩ : syracuseStep 10180667 = 15271001) B15271001
theorem B22042705 : Blo 1786094 22042705 := bstep (se 2 (by rfl) ⟨8266014, by rfl⟩ : syracuseStep 22042705 = 16532029) B16532029
theorem B13572521 : Blo 1786094 13572521 := bstep (se 2 (by rfl) ⟨5089695, by rfl⟩ : syracuseStep 13572521 = 10179391) B10179391
theorem B9042515 : Blo 1786094 9042515 := bstep (se 1 (by rfl) ⟨6781886, by rfl⟩ : syracuseStep 9042515 = 13563773) B13563773
theorem B6781583 : Blo 1786094 6781583 := bstep (se 1 (by rfl) ⟨5086187, by rfl⟩ : syracuseStep 6781583 = 10172375) B10172375
theorem B9050777 : Blo 1786094 9050777 := bstep (se 2 (by rfl) ⟨3394041, by rfl⟩ : syracuseStep 9050777 = 6788083) B6788083
theorem B30530519 : Blo 1786094 30530519 := bstep (se 1 (by rfl) ⟨22897889, by rfl⟩ : syracuseStep 30530519 = 45795779) B45795779
theorem B4021559 : Blo 1786094 4021559 := bstep (se 1 (by rfl) ⟨3016169, by rfl⟩ : syracuseStep 4021559 = 6032339) B6032339
theorem B3816811 : Blo 1786094 3816811 := bstep (se 1 (by rfl) ⟨2862608, by rfl⟩ : syracuseStep 3816811 = 5725217) B5725217
theorem B49569445 : Blo 1786094 49569445 := bstep (se 4 (by rfl) ⟨4647135, by rfl⟩ : syracuseStep 49569445 = 9294271) B9294271
theorem B6029153 : Blo 1786094 6029153 := bstep (se 2 (by rfl) ⟨2260932, by rfl⟩ : syracuseStep 6029153 = 4521865) B4521865
theorem B4522139 : Blo 1786094 4522139 := bstep (se 1 (by rfl) ⟨3391604, by rfl⟩ : syracuseStep 4522139 = 6783209) B6783209
theorem B16523459 : Blo 1786094 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B82501841 : Blo 1786094 82501841 := bstep (se 2 (by rfl) ⟨30938190, by rfl⟩ : syracuseStep 82501841 = 61876381) B61876381
theorem B5800175 : Blo 1786094 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B41820407 : Blo 1786094 41820407 := bstep (se 1 (by rfl) ⟨31365305, by rfl⟩ : syracuseStep 41820407 = 62730611) B62730611
theorem B1909055 : Blo 1786094 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B2679401 : Blo 1786094 2679401 := bstep (se 2 (by rfl) ⟨1004775, by rfl⟩ : syracuseStep 2679401 = 2009551) B2009551
theorem B4022927 : Blo 1786094 4022927 := bstep (se 1 (by rfl) ⟨3017195, by rfl⟩ : syracuseStep 4022927 = 6034391) B6034391
theorem B2679527 : Blo 1786094 2679527 := bstep (se 1 (by rfl) ⟨2009645, by rfl⟩ : syracuseStep 2679527 = 4019291) B4019291
theorem B7635707 : Blo 1786094 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B1786623 : Blo 1786094 1786623 := bstep (se 1 (by rfl) ⟨1339967, by rfl⟩ : syracuseStep 1786623 = 2679935) B2679935
theorem B13574951 : Blo 1786094 13574951 := bstep (se 1 (by rfl) ⟨10181213, by rfl⟩ : syracuseStep 13574951 = 20362427) B20362427
theorem B1786715 : Blo 1786094 1786715 := bstep (se 1 (by rfl) ⟨1340036, by rfl⟩ : syracuseStep 1786715 = 2680073) B2680073
theorem B10314811 : Blo 1786094 10314811 := bstep (se 1 (by rfl) ⟨7736108, by rfl⟩ : syracuseStep 10314811 = 15472217) B15472217
theorem B1787035 : Blo 1786094 1787035 := bstep (se 1 (by rfl) ⟨1340276, by rfl⟩ : syracuseStep 1787035 = 2680553) B2680553
theorem B1787135 : Blo 1786094 1787135 := bstep (se 1 (by rfl) ⟨1340351, by rfl⟩ : syracuseStep 1787135 = 2680703) B2680703
theorem B12231967 : Blo 1786094 12231967 := bstep (se 1 (by rfl) ⟨9173975, by rfl⟩ : syracuseStep 12231967 = 18347951) B18347951
theorem B9045431 : Blo 1786094 9045431 := bstep (se 1 (by rfl) ⟨6784073, by rfl⟩ : syracuseStep 9045431 = 13568147) B13568147
theorem B1787391 : Blo 1786094 1787391 := bstep (se 1 (by rfl) ⟨1340543, by rfl⟩ : syracuseStep 1787391 = 2681087) B2681087
theorem B1787547 : Blo 1786094 1787547 := bstep (se 1 (by rfl) ⟨1340660, by rfl⟩ : syracuseStep 1787547 = 2681321) B2681321
theorem B6784681 : Blo 1786094 6784681 := bstep (se 2 (by rfl) ⟨2544255, by rfl⟩ : syracuseStep 6784681 = 5088511) B5088511
theorem B5089081 : Blo 1786094 5089081 := bstep (se 2 (by rfl) ⟨1908405, by rfl⟩ : syracuseStep 5089081 = 3816811) B3816811
theorem B2681039 : Blo 1786094 2681039 := bstep (se 1 (by rfl) ⟨2010779, by rfl⟩ : syracuseStep 2681039 = 4021559) B4021559
theorem B4524275 : Blo 1786094 4524275 := bstep (se 1 (by rfl) ⟨3393206, by rfl⟩ : syracuseStep 4524275 = 6786413) B6786413
theorem B7637483 : Blo 1786094 7637483 := bstep (se 1 (by rfl) ⟨5728112, by rfl⟩ : syracuseStep 7637483 = 11456225) B11456225
theorem B3017263 : Blo 1786094 3017263 := bstep (se 1 (by rfl) ⟨2262947, by rfl⟩ : syracuseStep 3017263 = 4525895) B4525895
theorem B2681639 : Blo 1786094 2681639 := bstep (se 1 (by rfl) ⟨2011229, by rfl⟩ : syracuseStep 2681639 = 4022459) B4022459
theorem B9677981 : Blo 1786094 9677981 := bstep (se 3 (by rfl) ⟨1814621, by rfl⟩ : syracuseStep 9677981 = 3629243) B3629243
theorem B17173691 : Blo 1786094 17173691 := bstep (se 1 (by rfl) ⟨12880268, by rfl⟩ : syracuseStep 17173691 = 25760537) B25760537
theorem B7630033 : Blo 1786094 7630033 := bstep (se 2 (by rfl) ⟨2861262, by rfl⟩ : syracuseStep 7630033 = 5722525) B5722525
theorem B10177751 : Blo 1786094 10177751 := bstep (se 1 (by rfl) ⟨7633313, by rfl⟩ : syracuseStep 10177751 = 15266627) B15266627
theorem B6032609 : Blo 1786094 6032609 := bstep (se 2 (by rfl) ⟨2262228, by rfl⟩ : syracuseStep 6032609 = 4524457) B4524457
theorem B2010343 : Blo 1786094 2010343 := bstep (se 1 (by rfl) ⟨1507757, by rfl⟩ : syracuseStep 2010343 = 3015515) B3015515
theorem B14495071 : Blo 1786094 14495071 := bstep (se 1 (by rfl) ⟨10871303, by rfl⟩ : syracuseStep 14495071 = 21742607) B21742607
theorem B21745583 : Blo 1786094 21745583 := bstep (se 1 (by rfl) ⟨16309187, by rfl⟩ : syracuseStep 21745583 = 32618375) B32618375
theorem B9048023 : Blo 1786094 9048023 := bstep (se 1 (by rfl) ⟨6786017, by rfl⟩ : syracuseStep 9048023 = 13572035) B13572035
theorem B23842835 : Blo 1786094 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B6787111 : Blo 1786094 6787111 := bstep (se 1 (by rfl) ⟨5090333, by rfl⟩ : syracuseStep 6787111 = 10180667) B10180667
theorem B9048185 : Blo 1786094 9048185 := bstep (se 2 (by rfl) ⟨3393069, by rfl⟩ : syracuseStep 9048185 = 6786139) B6786139
theorem B9048347 : Blo 1786094 9048347 := bstep (se 1 (by rfl) ⟨6786260, by rfl⟩ : syracuseStep 9048347 = 13572521) B13572521
theorem B7631263 : Blo 1786094 7631263 := bstep (se 1 (by rfl) ⟨5723447, by rfl⟩ : syracuseStep 7631263 = 11446895) B11446895
theorem B6033851 : Blo 1786094 6033851 := bstep (se 1 (by rfl) ⟨4525388, by rfl⟩ : syracuseStep 6033851 = 9050777) B9050777
theorem B10318373 : Blo 1786094 10318373 := bstep (se 4 (by rfl) ⟨967347, by rfl⟩ : syracuseStep 10318373 = 1934695) B1934695
theorem B38646341 : Blo 1786094 38646341 := bstep (se 4 (by rfl) ⟨3623094, by rfl⟩ : syracuseStep 38646341 = 7246189) B7246189
theorem B20353679 : Blo 1786094 20353679 := bstep (se 1 (by rfl) ⟨15265259, by rfl⟩ : syracuseStep 20353679 = 30530519) B30530519
theorem B3437225 : Blo 1786094 3437225 := bstep (se 2 (by rfl) ⟨1288959, by rfl⟩ : syracuseStep 3437225 = 2577919) B2577919
theorem B2863993 : Blo 1786094 2863993 := bstep (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) B2147995
theorem B28996703 : Blo 1786094 28996703 := bstep (se 1 (by rfl) ⟨21747527, by rfl⟩ : syracuseStep 28996703 = 43495055) B43495055
theorem B4019435 : Blo 1786094 4019435 := bstep (se 1 (by rfl) ⟨3014576, by rfl⟩ : syracuseStep 4019435 = 6029153) B6029153
theorem B29390273 : Blo 1786094 29390273 := bstep (se 2 (by rfl) ⟨11021352, by rfl⟩ : syracuseStep 29390273 = 22042705) B22042705
theorem B4020047 : Blo 1786094 4020047 := bstep (se 1 (by rfl) ⟨3015035, by rfl⟩ : syracuseStep 4020047 = 6030071) B6030071
theorem B6789055 : Blo 1786094 6789055 := bstep (se 1 (by rfl) ⟨5091791, by rfl⟩ : syracuseStep 6789055 = 10183583) B10183583
theorem B7248055 : Blo 1786094 7248055 := bstep (se 1 (by rfl) ⟨5436041, by rfl⟩ : syracuseStep 7248055 = 10872083) B10872083
theorem B88177085 : Blo 1786094 88177085 := bstep (se 3 (by rfl) ⟨16533203, by rfl⟩ : syracuseStep 88177085 = 33066407) B33066407
theorem B4020767 : Blo 1786094 4020767 := bstep (se 1 (by rfl) ⟨3015575, by rfl⟩ : syracuseStep 4020767 = 6031151) B6031151
theorem B7347155 : Blo 1786094 7347155 := bstep (se 1 (by rfl) ⟨5510366, by rfl⟩ : syracuseStep 7347155 = 11020733) B11020733
theorem B6028343 : Blo 1786094 6028343 := bstep (se 1 (by rfl) ⟨4521257, by rfl⟩ : syracuseStep 6028343 = 9042515) B9042515
theorem B8592439 : Blo 1786094 8592439 := bstep (se 1 (by rfl) ⟨6444329, by rfl⟩ : syracuseStep 8592439 = 12888659) B12888659
theorem B28990523 : Blo 1786094 28990523 := bstep (se 1 (by rfl) ⟨21742892, by rfl⟩ : syracuseStep 28990523 = 43485785) B43485785
theorem B4521055 : Blo 1786094 4521055 := bstep (se 1 (by rfl) ⟨3390791, by rfl⟩ : syracuseStep 4521055 = 6781583) B6781583
theorem B4021595 : Blo 1786094 4021595 := bstep (se 1 (by rfl) ⟨3016196, by rfl⟩ : syracuseStep 4021595 = 6032393) B6032393
theorem B51527177 : Blo 1786094 51527177 := bstep (se 2 (by rfl) ⟨19322691, by rfl⟩ : syracuseStep 51527177 = 38645383) B38645383
theorem B66092593 : Blo 1786094 66092593 := bstep (se 2 (by rfl) ⟨24784722, by rfl⟩ : syracuseStep 66092593 = 49569445) B49569445
theorem B3014759 : Blo 1786094 3014759 := bstep (se 1 (by rfl) ⟨2261069, by rfl⟩ : syracuseStep 3014759 = 4522139) B4522139
theorem B3866783 : Blo 1786094 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B4022567 : Blo 1786094 4022567 := bstep (se 1 (by rfl) ⟨3016925, by rfl⟩ : syracuseStep 4022567 = 6033851) B6033851
theorem B25764227 : Blo 1786094 25764227 := bstep (se 1 (by rfl) ⟨19323170, by rfl⟩ : syracuseStep 25764227 = 38646341) B38646341
theorem B1786267 : Blo 1786094 1786267 := bstep (se 1 (by rfl) ⟨1339700, by rfl⟩ : syracuseStep 1786267 = 2679401) B2679401
theorem B1786351 : Blo 1786094 1786351 := bstep (se 1 (by rfl) ⟨1339763, by rfl⟩ : syracuseStep 1786351 = 2679527) B2679527
theorem B10175017 : Blo 1786094 10175017 := bstep (se 2 (by rfl) ⟨3815631, by rfl⟩ : syracuseStep 10175017 = 7631263) B7631263
theorem B220004909 : Blo 1786094 220004909 := bstep (se 3 (by rfl) ⟨41250920, by rfl⟩ : syracuseStep 220004909 = 82501841) B82501841
theorem B4023017 : Blo 1786094 4023017 := bstep (se 2 (by rfl) ⟨1508631, by rfl⟩ : syracuseStep 4023017 = 3017263) B3017263
theorem B2679623 : Blo 1786094 2679623 := bstep (se 1 (by rfl) ⟨2009717, by rfl⟩ : syracuseStep 2679623 = 4019435) B4019435
theorem B6030287 : Blo 1786094 6030287 := bstep (se 1 (by rfl) ⟨4522715, by rfl⟩ : syracuseStep 6030287 = 9045431) B9045431
theorem B3818657 : Blo 1786094 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B2680031 : Blo 1786094 2680031 := bstep (se 1 (by rfl) ⟨2010023, by rfl⟩ : syracuseStep 2680031 = 4020047) B4020047
theorem B1787359 : Blo 1786094 1787359 := bstep (se 1 (by rfl) ⟨1340519, by rfl⟩ : syracuseStep 1787359 = 2681039) B2681039
theorem B3016183 : Blo 1786094 3016183 := bstep (se 1 (by rfl) ⟨2262137, by rfl⟩ : syracuseStep 3016183 = 4524275) B4524275
theorem B2680457 : Blo 1786094 2680457 := bstep (se 2 (by rfl) ⟨1005171, by rfl⟩ : syracuseStep 2680457 = 2010343) B2010343
theorem B2680511 : Blo 1786094 2680511 := bstep (se 1 (by rfl) ⟨2010383, by rfl⟩ : syracuseStep 2680511 = 4020767) B4020767
theorem B19326761 : Blo 1786094 19326761 := bstep (se 2 (by rfl) ⟨7247535, by rfl⟩ : syracuseStep 19326761 = 14495071) B14495071
theorem B1787759 : Blo 1786094 1787759 := bstep (se 1 (by rfl) ⟨1340819, by rfl⟩ : syracuseStep 1787759 = 2681639) B2681639
theorem B19327015 : Blo 1786094 19327015 := bstep (se 1 (by rfl) ⟨14495261, by rfl⟩ : syracuseStep 19327015 = 28990523) B28990523
theorem B88123457 : Blo 1786094 88123457 := bstep (se 2 (by rfl) ⟨33046296, by rfl⟩ : syracuseStep 88123457 = 66092593) B66092593
theorem B6785167 : Blo 1786094 6785167 := bstep (se 1 (by rfl) ⟨5088875, by rfl⟩ : syracuseStep 6785167 = 10177751) B10177751
theorem B9046241 : Blo 1786094 9046241 := bstep (se 2 (by rfl) ⟨3392340, by rfl⟩ : syracuseStep 9046241 = 6784681) B6784681
theorem B2681063 : Blo 1786094 2681063 := bstep (se 1 (by rfl) ⟨2010797, by rfl⟩ : syracuseStep 2681063 = 4021595) B4021595
theorem B34351451 : Blo 1786094 34351451 := bstep (se 1 (by rfl) ⟨25763588, by rfl⟩ : syracuseStep 34351451 = 51527177) B51527177
theorem B6785441 : Blo 1786094 6785441 := bstep (se 2 (by rfl) ⟨2544540, by rfl⟩ : syracuseStep 6785441 = 5089081) B5089081
theorem B6032015 : Blo 1786094 6032015 := bstep (se 1 (by rfl) ⟨4524011, by rfl⟩ : syracuseStep 6032015 = 9048023) B9048023
theorem B15895223 : Blo 1786094 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B6032123 : Blo 1786094 6032123 := bstep (se 1 (by rfl) ⟨4524092, by rfl⟩ : syracuseStep 6032123 = 9048185) B9048185
theorem B27880271 : Blo 1786094 27880271 := bstep (se 1 (by rfl) ⟨20910203, by rfl⟩ : syracuseStep 27880271 = 41820407) B41820407
theorem B6032231 : Blo 1786094 6032231 := bstep (se 1 (by rfl) ⟨4524173, by rfl⟩ : syracuseStep 6032231 = 9048347) B9048347
theorem B13569119 : Blo 1786094 13569119 := bstep (se 1 (by rfl) ⟨10176839, by rfl⟩ : syracuseStep 13569119 = 20353679) B20353679
theorem B2681951 : Blo 1786094 2681951 := bstep (se 1 (by rfl) ⟨2011463, by rfl⟩ : syracuseStep 2681951 = 4022927) B4022927
theorem B5090471 : Blo 1786094 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B5090813 : Blo 1786094 5090813 := bstep (se 3 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 5090813 = 1909055) B1909055
theorem B11456585 : Blo 1786094 11456585 := bstep (se 2 (by rfl) ⟨4296219, by rfl⟩ : syracuseStep 11456585 = 8592439) B8592439
theorem B5091655 : Blo 1786094 5091655 := bstep (se 1 (by rfl) ⟨3818741, by rfl⟩ : syracuseStep 5091655 = 7637483) B7637483
theorem B4018895 : Blo 1786094 4018895 := bstep (se 1 (by rfl) ⟨3014171, by rfl⟩ : syracuseStep 4018895 = 6028343) B6028343
theorem B6451987 : Blo 1786094 6451987 := bstep (se 1 (by rfl) ⟨4838990, by rfl⟩ : syracuseStep 6451987 = 9677981) B9677981
theorem B11449127 : Blo 1786094 11449127 := bstep (se 1 (by rfl) ⟨8586845, by rfl⟩ : syracuseStep 11449127 = 17173691) B17173691
theorem B78369653 : Blo 1786094 78369653 := bstep (se 5 (by rfl) ⟨3673577, by rfl⟩ : syracuseStep 78369653 = 7347155) B7347155
theorem B14497055 : Blo 1786094 14497055 := bstep (se 1 (by rfl) ⟨10872791, by rfl⟩ : syracuseStep 14497055 = 21745583) B21745583
theorem B9049481 : Blo 1786094 9049481 := bstep (se 2 (by rfl) ⟨3393555, by rfl⟩ : syracuseStep 9049481 = 6787111) B6787111
theorem B11015639 : Blo 1786094 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B9664073 : Blo 1786094 9664073 := bstep (se 2 (by rfl) ⟨3624027, by rfl⟩ : syracuseStep 9664073 = 7248055) B7248055
theorem B6878915 : Blo 1786094 6878915 := bstep (se 1 (by rfl) ⟨5159186, by rfl⟩ : syracuseStep 6878915 = 10318373) B10318373
theorem B2291483 : Blo 1786094 2291483 := bstep (se 1 (by rfl) ⟨1718612, by rfl⟩ : syracuseStep 2291483 = 3437225) B3437225
theorem B9049967 : Blo 1786094 9049967 := bstep (se 1 (by rfl) ⟨6787475, by rfl⟩ : syracuseStep 9049967 = 13574951) B13574951
theorem B19331135 : Blo 1786094 19331135 := bstep (se 1 (by rfl) ⟨14498351, by rfl⟩ : syracuseStep 19331135 = 28996703) B28996703
theorem B19593515 : Blo 1786094 19593515 := bstep (se 1 (by rfl) ⟨14695136, by rfl⟩ : syracuseStep 19593515 = 29390273) B29390273
theorem B13753081 : Blo 1786094 13753081 := bstep (se 2 (by rfl) ⟨5157405, by rfl⟩ : syracuseStep 13753081 = 10314811) B10314811
theorem B6028073 : Blo 1786094 6028073 := bstep (se 2 (by rfl) ⟨2260527, by rfl⟩ : syracuseStep 6028073 = 4521055) B4521055
theorem B10173377 : Blo 1786094 10173377 := bstep (se 2 (by rfl) ⟨3815016, by rfl⟩ : syracuseStep 10173377 = 7630033) B7630033
theorem B58784723 : Blo 1786094 58784723 := bstep (se 1 (by rfl) ⟨44088542, by rfl⟩ : syracuseStep 58784723 = 88177085) B88177085
theorem B16309289 : Blo 1786094 16309289 := bstep (se 2 (by rfl) ⟨6115983, by rfl⟩ : syracuseStep 16309289 = 12231967) B12231967
theorem B4021739 : Blo 1786094 4021739 := bstep (se 1 (by rfl) ⟨3016304, by rfl⟩ : syracuseStep 4021739 = 6032609) B6032609
theorem B9052073 : Blo 1786094 9052073 := bstep (se 2 (by rfl) ⟨3394527, by rfl⟩ : syracuseStep 9052073 = 6789055) B6789055
theorem B146669939 : Blo 1786094 146669939 := bstep (se 1 (by rfl) ⟨110002454, by rfl⟩ : syracuseStep 146669939 = 220004909) B220004909
theorem B2679263 : Blo 1786094 2679263 := bstep (se 1 (by rfl) ⟨2009447, by rfl⟩ : syracuseStep 2679263 = 4018895) B4018895
theorem B1786415 : Blo 1786094 1786415 := bstep (se 1 (by rfl) ⟨1339811, by rfl⟩ : syracuseStep 1786415 = 2679623) B2679623
theorem B13566689 : Blo 1786094 13566689 := bstep (se 2 (by rfl) ⟨5087508, by rfl⟩ : syracuseStep 13566689 = 10175017) B10175017
theorem B1786687 : Blo 1786094 1786687 := bstep (se 1 (by rfl) ⟨1340015, by rfl⟩ : syracuseStep 1786687 = 2680031) B2680031
theorem B8602649 : Blo 1786094 8602649 := bstep (se 2 (by rfl) ⟨3225993, by rfl⟩ : syracuseStep 8602649 = 6451987) B6451987
theorem B1786971 : Blo 1786094 1786971 := bstep (se 1 (by rfl) ⟨1340228, by rfl⟩ : syracuseStep 1786971 = 2680457) B2680457
theorem B1787007 : Blo 1786094 1787007 := bstep (se 1 (by rfl) ⟨1340255, by rfl⟩ : syracuseStep 1787007 = 2680511) B2680511
theorem B12887423 : Blo 1786094 12887423 := bstep (se 1 (by rfl) ⟨9665567, by rfl⟩ : syracuseStep 12887423 = 19331135) B19331135
theorem B6030827 : Blo 1786094 6030827 := bstep (se 1 (by rfl) ⟨4523120, by rfl⟩ : syracuseStep 6030827 = 9046241) B9046241
theorem B1787375 : Blo 1786094 1787375 := bstep (se 1 (by rfl) ⟨1340531, by rfl⟩ : syracuseStep 1787375 = 2681063) B2681063
theorem B4523627 : Blo 1786094 4523627 := bstep (se 1 (by rfl) ⟨3392720, by rfl⟩ : syracuseStep 4523627 = 6785441) B6785441
theorem B10872859 : Blo 1786094 10872859 := bstep (se 1 (by rfl) ⟨8154644, by rfl⟩ : syracuseStep 10872859 = 16309289) B16309289
theorem B9046079 : Blo 1786094 9046079 := bstep (se 1 (by rfl) ⟨6784559, by rfl⟩ : syracuseStep 9046079 = 13569119) B13569119
theorem B1787967 : Blo 1786094 1787967 := bstep (se 1 (by rfl) ⟨1340975, by rfl⟩ : syracuseStep 1787967 = 2681951) B2681951
theorem B3393647 : Blo 1786094 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B2681159 : Blo 1786094 2681159 := bstep (se 1 (by rfl) ⟨2010869, by rfl⟩ : syracuseStep 2681159 = 4021739) B4021739
theorem B3393875 : Blo 1786094 3393875 := bstep (se 1 (by rfl) ⟨2545406, by rfl⟩ : syracuseStep 3393875 = 5090813) B5090813
theorem B7637723 : Blo 1786094 7637723 := bstep (se 1 (by rfl) ⟨5728292, by rfl⟩ : syracuseStep 7637723 = 11456585) B11456585
theorem B2009839 : Blo 1786094 2009839 := bstep (se 1 (by rfl) ⟨1507379, by rfl⟩ : syracuseStep 2009839 = 3014759) B3014759
theorem B9046889 : Blo 1786094 9046889 := bstep (se 2 (by rfl) ⟨3392583, by rfl⟩ : syracuseStep 9046889 = 6785167) B6785167
theorem B2681711 : Blo 1786094 2681711 := bstep (se 1 (by rfl) ⟨2011283, by rfl⟩ : syracuseStep 2681711 = 4022567) B4022567
theorem B2682011 : Blo 1786094 2682011 := bstep (se 1 (by rfl) ⟨2011508, by rfl⟩ : syracuseStep 2682011 = 4023017) B4023017
theorem B6032987 : Blo 1786094 6032987 := bstep (se 1 (by rfl) ⟨4524740, by rfl⟩ : syracuseStep 6032987 = 9049481) B9049481
theorem B7343759 : Blo 1786094 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B18337441 : Blo 1786094 18337441 := bstep (se 2 (by rfl) ⟨6876540, by rfl⟩ : syracuseStep 18337441 = 13753081) B13753081
theorem B6442715 : Blo 1786094 6442715 := bstep (se 1 (by rfl) ⟨4832036, by rfl⟩ : syracuseStep 6442715 = 9664073) B9664073
theorem B6033311 : Blo 1786094 6033311 := bstep (se 1 (by rfl) ⟨4524983, by rfl⟩ : syracuseStep 6033311 = 9049967) B9049967
theorem B58748971 : Blo 1786094 58748971 := bstep (se 1 (by rfl) ⟨44061728, by rfl⟩ : syracuseStep 58748971 = 88123457) B88123457
theorem B13062343 : Blo 1786094 13062343 := bstep (se 1 (by rfl) ⟨9796757, by rfl⟩ : syracuseStep 13062343 = 19593515) B19593515
theorem B22900967 : Blo 1786094 22900967 := bstep (se 1 (by rfl) ⟨17175725, by rfl⟩ : syracuseStep 22900967 = 34351451) B34351451
theorem B10596815 : Blo 1786094 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B4018715 : Blo 1786094 4018715 := bstep (se 1 (by rfl) ⟨3014036, by rfl⟩ : syracuseStep 4018715 = 6028073) B6028073
theorem B6034715 : Blo 1786094 6034715 := bstep (se 1 (by rfl) ⟨4526036, by rfl⟩ : syracuseStep 6034715 = 9052073) B9052073
theorem B25769353 : Blo 1786094 25769353 := bstep (se 2 (by rfl) ⟨9663507, by rfl⟩ : syracuseStep 25769353 = 19327015) B19327015
theorem B17176151 : Blo 1786094 17176151 := bstep (se 1 (by rfl) ⟨12882113, by rfl⟩ : syracuseStep 17176151 = 25764227) B25764227
theorem B10311421 : Blo 1786094 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B6788873 : Blo 1786094 6788873 := bstep (se 2 (by rfl) ⟨2545827, by rfl⟩ : syracuseStep 6788873 = 5091655) B5091655
theorem B7632751 : Blo 1786094 7632751 := bstep (se 1 (by rfl) ⟨5724563, by rfl⟩ : syracuseStep 7632751 = 11449127) B11449127
theorem B4020191 : Blo 1786094 4020191 := bstep (se 1 (by rfl) ⟨3015143, by rfl⟩ : syracuseStep 4020191 = 6030287) B6030287
theorem B2545771 : Blo 1786094 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B9664703 : Blo 1786094 9664703 := bstep (se 1 (by rfl) ⟨7248527, by rfl⟩ : syracuseStep 9664703 = 14497055) B14497055
theorem B4585943 : Blo 1786094 4585943 := bstep (se 1 (by rfl) ⟨3439457, by rfl⟩ : syracuseStep 4585943 = 6878915) B6878915
theorem B12884507 : Blo 1786094 12884507 := bstep (se 1 (by rfl) ⟨9663380, by rfl⟩ : syracuseStep 12884507 = 19326761) B19326761
theorem B4021343 : Blo 1786094 4021343 := bstep (se 1 (by rfl) ⟨3016007, by rfl⟩ : syracuseStep 4021343 = 6032015) B6032015
theorem B4021415 : Blo 1786094 4021415 := bstep (se 1 (by rfl) ⟨3016061, by rfl⟩ : syracuseStep 4021415 = 6032123) B6032123
theorem B18586847 : Blo 1786094 18586847 := bstep (se 1 (by rfl) ⟨13940135, by rfl⟩ : syracuseStep 18586847 = 27880271) B27880271
theorem B4021487 : Blo 1786094 4021487 := bstep (se 1 (by rfl) ⟨3016115, by rfl⟩ : syracuseStep 4021487 = 6032231) B6032231
theorem B6782251 : Blo 1786094 6782251 := bstep (se 1 (by rfl) ⟨5086688, by rfl⟩ : syracuseStep 6782251 = 10173377) B10173377
theorem B39189815 : Blo 1786094 39189815 := bstep (se 1 (by rfl) ⟨29392361, by rfl⟩ : syracuseStep 39189815 = 58784723) B58784723
theorem B4021577 : Blo 1786094 4021577 := bstep (se 2 (by rfl) ⟨1508091, by rfl⟩ : syracuseStep 4021577 = 3016183) B3016183
theorem B6110621 : Blo 1786094 6110621 := bstep (se 3 (by rfl) ⟨1145741, by rfl⟩ : syracuseStep 6110621 = 2291483) B2291483
theorem B208985741 : Blo 1786094 208985741 := bstep (se 3 (by rfl) ⟨39184826, by rfl⟩ : syracuseStep 208985741 = 78369653) B78369653
theorem B78331961 : Blo 1786094 78331961 := bstep (se 2 (by rfl) ⟨29374485, by rfl⟩ : syracuseStep 78331961 = 58748971) B58748971
theorem B97779959 : Blo 1786094 97779959 := bstep (se 1 (by rfl) ⟨73334969, by rfl⟩ : syracuseStep 97779959 = 146669939) B146669939
theorem B17416457 : Blo 1786094 17416457 := bstep (se 2 (by rfl) ⟨6531171, by rfl⟩ : syracuseStep 17416457 = 13062343) B13062343
theorem B1786175 : Blo 1786094 1786175 := bstep (se 1 (by rfl) ⟨1339631, by rfl⟩ : syracuseStep 1786175 = 2679263) B2679263
theorem B2679143 : Blo 1786094 2679143 := bstep (se 1 (by rfl) ⟨2009357, by rfl⟩ : syracuseStep 2679143 = 4018715) B4018715
theorem B9044459 : Blo 1786094 9044459 := bstep (se 1 (by rfl) ⟨6783344, by rfl⟩ : syracuseStep 9044459 = 13566689) B13566689
theorem B5735099 : Blo 1786094 5735099 := bstep (se 1 (by rfl) ⟨4301324, by rfl⟩ : syracuseStep 5735099 = 8602649) B8602649
theorem B4023143 : Blo 1786094 4023143 := bstep (se 1 (by rfl) ⟨3017357, by rfl⟩ : syracuseStep 4023143 = 6034715) B6034715
theorem B2679785 : Blo 1786094 2679785 := bstep (se 2 (by rfl) ⟨1004919, by rfl⟩ : syracuseStep 2679785 = 2009839) B2009839
theorem B3015751 : Blo 1786094 3015751 := bstep (se 1 (by rfl) ⟨2261813, by rfl⟩ : syracuseStep 3015751 = 4523627) B4523627
theorem B2680127 : Blo 1786094 2680127 := bstep (se 1 (by rfl) ⟨2010095, by rfl⟩ : syracuseStep 2680127 = 4020191) B4020191
theorem B6030719 : Blo 1786094 6030719 := bstep (se 1 (by rfl) ⟨4523039, by rfl⟩ : syracuseStep 6030719 = 9046079) B9046079
theorem B2262431 : Blo 1786094 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B1787439 : Blo 1786094 1787439 := bstep (se 1 (by rfl) ⟨1340579, by rfl⟩ : syracuseStep 1787439 = 2681159) B2681159
theorem B2262583 : Blo 1786094 2262583 := bstep (se 1 (by rfl) ⟨1696937, by rfl⟩ : syracuseStep 2262583 = 3393875) B3393875
theorem B34359137 : Blo 1786094 34359137 := bstep (se 2 (by rfl) ⟨12884676, by rfl⟩ : syracuseStep 34359137 = 25769353) B25769353
theorem B6031259 : Blo 1786094 6031259 := bstep (se 1 (by rfl) ⟨4523444, by rfl⟩ : syracuseStep 6031259 = 9046889) B9046889
theorem B1787807 : Blo 1786094 1787807 := bstep (se 1 (by rfl) ⟨1340855, by rfl⟩ : syracuseStep 1787807 = 2681711) B2681711
theorem B2680895 : Blo 1786094 2680895 := bstep (se 1 (by rfl) ⟨2010671, by rfl⟩ : syracuseStep 2680895 = 4021343) B4021343
theorem B1788007 : Blo 1786094 1788007 := bstep (se 1 (by rfl) ⟨1341005, by rfl⟩ : syracuseStep 1788007 = 2682011) B2682011
theorem B2680943 : Blo 1786094 2680943 := bstep (se 1 (by rfl) ⟨2010707, by rfl⟩ : syracuseStep 2680943 = 4021415) B4021415
theorem B2680991 : Blo 1786094 2680991 := bstep (se 1 (by rfl) ⟨2010743, by rfl⟩ : syracuseStep 2680991 = 4021487) B4021487
theorem B26126543 : Blo 1786094 26126543 := bstep (se 1 (by rfl) ⟨19594907, by rfl⟩ : syracuseStep 26126543 = 39189815) B39189815
theorem B2681051 : Blo 1786094 2681051 := bstep (se 1 (by rfl) ⟨2010788, by rfl⟩ : syracuseStep 2681051 = 4021577) B4021577
theorem B4073747 : Blo 1786094 4073747 := bstep (se 1 (by rfl) ⟨3055310, by rfl⟩ : syracuseStep 4073747 = 6110621) B6110621
theorem B13748561 : Blo 1786094 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B139323827 : Blo 1786094 139323827 := bstep (se 1 (by rfl) ⟨104492870, by rfl⟩ : syracuseStep 139323827 = 208985741) B208985741
theorem B4295143 : Blo 1786094 4295143 := bstep (se 1 (by rfl) ⟨3221357, by rfl⟩ : syracuseStep 4295143 = 6442715) B6442715
theorem B10177001 : Blo 1786094 10177001 := bstep (se 2 (by rfl) ⟨3816375, by rfl⟩ : syracuseStep 10177001 = 7632751) B7632751
theorem B3394361 : Blo 1786094 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B7064543 : Blo 1786094 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B4525915 : Blo 1786094 4525915 := bstep (se 1 (by rfl) ⟨3394436, by rfl⟩ : syracuseStep 4525915 = 6788873) B6788873
theorem B6443135 : Blo 1786094 6443135 := bstep (se 1 (by rfl) ⟨4832351, by rfl⟩ : syracuseStep 6443135 = 9664703) B9664703
theorem B8589671 : Blo 1786094 8589671 := bstep (se 1 (by rfl) ⟨6442253, by rfl⟩ : syracuseStep 8589671 = 12884507) B12884507
theorem B5091815 : Blo 1786094 5091815 := bstep (se 1 (by rfl) ⟨3818861, by rfl⟩ : syracuseStep 5091815 = 7637723) B7637723
theorem B12391231 : Blo 1786094 12391231 := bstep (se 1 (by rfl) ⟨9293423, by rfl⟩ : syracuseStep 12391231 = 18586847) B18586847
theorem B24449921 : Blo 1786094 24449921 := bstep (se 2 (by rfl) ⟨9168720, by rfl⟩ : syracuseStep 24449921 = 18337441) B18337441
theorem B4895839 : Blo 1786094 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B14497145 : Blo 1786094 14497145 := bstep (se 2 (by rfl) ⟨5436429, by rfl⟩ : syracuseStep 14497145 = 10872859) B10872859
theorem B15267311 : Blo 1786094 15267311 := bstep (se 1 (by rfl) ⟨11450483, by rfl⟩ : syracuseStep 15267311 = 22900967) B22900967
theorem B8591615 : Blo 1786094 8591615 := bstep (se 1 (by rfl) ⟨6443711, by rfl⟩ : syracuseStep 8591615 = 12887423) B12887423
theorem B4020551 : Blo 1786094 4020551 := bstep (se 1 (by rfl) ⟨3015413, by rfl⟩ : syracuseStep 4020551 = 6030827) B6030827
theorem B11450767 : Blo 1786094 11450767 := bstep (se 1 (by rfl) ⟨8588075, by rfl⟩ : syracuseStep 11450767 = 17176151) B17176151
theorem B12229181 : Blo 1786094 12229181 := bstep (se 3 (by rfl) ⟨2292971, by rfl⟩ : syracuseStep 12229181 = 4585943) B4585943
theorem B9043001 : Blo 1786094 9043001 := bstep (se 2 (by rfl) ⟨3391125, by rfl⟩ : syracuseStep 9043001 = 6782251) B6782251
theorem B4021991 : Blo 1786094 4021991 := bstep (se 1 (by rfl) ⟨3016493, by rfl⟩ : syracuseStep 4021991 = 6032987) B6032987
theorem B4022207 : Blo 1786094 4022207 := bstep (se 1 (by rfl) ⟨3016655, by rfl⟩ : syracuseStep 4022207 = 6033311) B6033311
theorem B1786095 : Blo 1786094 1786095 := bstep (se 1 (by rfl) ⟨1339571, by rfl⟩ : syracuseStep 1786095 = 2679143) B2679143
theorem B5726447 : Blo 1786094 5726447 := bstep (se 1 (by rfl) ⟨4294835, by rfl⟩ : syracuseStep 5726447 = 8589671) B8589671
theorem B6029639 : Blo 1786094 6029639 := bstep (se 1 (by rfl) ⟨4522229, by rfl⟩ : syracuseStep 6029639 = 9044459) B9044459
theorem B5726857 : Blo 1786094 5726857 := bstep (se 2 (by rfl) ⟨2147571, by rfl⟩ : syracuseStep 5726857 = 4295143) B4295143
theorem B1786523 : Blo 1786094 1786523 := bstep (se 1 (by rfl) ⟨1339892, by rfl⟩ : syracuseStep 1786523 = 2679785) B2679785
theorem B10863325 : Blo 1786094 10863325 := bstep (se 3 (by rfl) ⟨2036873, by rfl⟩ : syracuseStep 10863325 = 4073747) B4073747
theorem B1786751 : Blo 1786094 1786751 := bstep (se 1 (by rfl) ⟨1340063, by rfl⟩ : syracuseStep 1786751 = 2680127) B2680127
theorem B22906091 : Blo 1786094 22906091 := bstep (se 1 (by rfl) ⟨17179568, by rfl⟩ : syracuseStep 22906091 = 34359137) B34359137
theorem B1787263 : Blo 1786094 1787263 := bstep (se 1 (by rfl) ⟨1340447, by rfl⟩ : syracuseStep 1787263 = 2680895) B2680895
theorem B1787295 : Blo 1786094 1787295 := bstep (se 1 (by rfl) ⟨1340471, by rfl⟩ : syracuseStep 1787295 = 2680943) B2680943
theorem B1787327 : Blo 1786094 1787327 := bstep (se 1 (by rfl) ⟨1340495, by rfl⟩ : syracuseStep 1787327 = 2680991) B2680991
theorem B1787367 : Blo 1786094 1787367 := bstep (se 1 (by rfl) ⟨1340525, by rfl⟩ : syracuseStep 1787367 = 2681051) B2681051
theorem B5727743 : Blo 1786094 5727743 := bstep (se 1 (by rfl) ⟨4295807, by rfl⟩ : syracuseStep 5727743 = 8591615) B8591615
theorem B2680367 : Blo 1786094 2680367 := bstep (se 1 (by rfl) ⟨2010275, by rfl⟩ : syracuseStep 2680367 = 4020551) B4020551
theorem B92882551 : Blo 1786094 92882551 := bstep (se 1 (by rfl) ⟨69661913, by rfl⟩ : syracuseStep 92882551 = 139323827) B139323827
theorem B6784667 : Blo 1786094 6784667 := bstep (se 1 (by rfl) ⟨5088500, by rfl⟩ : syracuseStep 6784667 = 10177001) B10177001
theorem B8152787 : Blo 1786094 8152787 := bstep (se 1 (by rfl) ⟨6114590, by rfl⟩ : syracuseStep 8152787 = 12229181) B12229181
theorem B2262907 : Blo 1786094 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B3016777 : Blo 1786094 3016777 := bstep (se 2 (by rfl) ⟨1131291, by rfl⟩ : syracuseStep 3016777 = 2262583) B2262583
theorem B2681327 : Blo 1786094 2681327 := bstep (se 1 (by rfl) ⟨2010995, by rfl⟩ : syracuseStep 2681327 = 4021991) B4021991
theorem B2681471 : Blo 1786094 2681471 := bstep (se 1 (by rfl) ⟨2011103, by rfl⟩ : syracuseStep 2681471 = 4022207) B4022207
theorem B4295423 : Blo 1786094 4295423 := bstep (se 1 (by rfl) ⟨3221567, by rfl⟩ : syracuseStep 4295423 = 6443135) B6443135
theorem B65186639 : Blo 1786094 65186639 := bstep (se 1 (by rfl) ⟨48889979, by rfl⟩ : syracuseStep 65186639 = 97779959) B97779959
theorem B11610971 : Blo 1786094 11610971 := bstep (se 1 (by rfl) ⟨8708228, by rfl⟩ : syracuseStep 11610971 = 17416457) B17416457
theorem B3394543 : Blo 1786094 3394543 := bstep (se 1 (by rfl) ⟨2545907, by rfl⟩ : syracuseStep 3394543 = 5091815) B5091815
theorem B2682095 : Blo 1786094 2682095 := bstep (se 1 (by rfl) ⟨2011571, by rfl⟩ : syracuseStep 2682095 = 4023143) B4023143
theorem B10178207 : Blo 1786094 10178207 := bstep (se 1 (by rfl) ⟨7633655, by rfl⟩ : syracuseStep 10178207 = 15267311) B15267311
theorem B6033149 : Blo 1786094 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B6034553 : Blo 1786094 6034553 := bstep (se 2 (by rfl) ⟨2262957, by rfl⟩ : syracuseStep 6034553 = 4525915) B4525915
theorem B18838781 : Blo 1786094 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B52221307 : Blo 1786094 52221307 := bstep (se 1 (by rfl) ⟨39165980, by rfl⟩ : syracuseStep 52221307 = 78331961) B78331961
theorem B3823399 : Blo 1786094 3823399 := bstep (se 1 (by rfl) ⟨2867549, by rfl⟩ : syracuseStep 3823399 = 5735099) B5735099
theorem B15267689 : Blo 1786094 15267689 := bstep (se 2 (by rfl) ⟨5725383, by rfl⟩ : syracuseStep 15267689 = 11450767) B11450767
theorem B69670781 : Blo 1786094 69670781 := bstep (se 3 (by rfl) ⟨13063271, by rfl⟩ : syracuseStep 69670781 = 26126543) B26126543
theorem B16299947 : Blo 1786094 16299947 := bstep (se 1 (by rfl) ⟨12224960, by rfl⟩ : syracuseStep 16299947 = 24449921) B24449921
theorem B9664763 : Blo 1786094 9664763 := bstep (se 1 (by rfl) ⟨7248572, by rfl⟩ : syracuseStep 9664763 = 14497145) B14497145
theorem B4020479 : Blo 1786094 4020479 := bstep (se 1 (by rfl) ⟨3015359, by rfl⟩ : syracuseStep 4020479 = 6030719) B6030719
theorem B16521641 : Blo 1786094 16521641 := bstep (se 2 (by rfl) ⟨6195615, by rfl⟩ : syracuseStep 16521641 = 12391231) B12391231
theorem B4020839 : Blo 1786094 4020839 := bstep (se 1 (by rfl) ⟨3015629, by rfl⟩ : syracuseStep 4020839 = 6031259) B6031259
theorem B4021001 : Blo 1786094 4021001 := bstep (se 2 (by rfl) ⟨1507875, by rfl⟩ : syracuseStep 4021001 = 3015751) B3015751
theorem B6527785 : Blo 1786094 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B9165707 : Blo 1786094 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B6028667 : Blo 1786094 6028667 := bstep (se 1 (by rfl) ⟨4521500, by rfl⟩ : syracuseStep 6028667 = 9043001) B9043001
theorem B4022369 : Blo 1786094 4022369 := bstep (se 2 (by rfl) ⟨1508388, by rfl⟩ : syracuseStep 4022369 = 3016777) B3016777
theorem B3817631 : Blo 1786094 3817631 := bstep (se 1 (by rfl) ⟨2863223, by rfl⟩ : syracuseStep 3817631 = 5726447) B5726447
theorem B25772701 : Blo 1786094 25772701 := bstep (se 3 (by rfl) ⟨4832381, by rfl⟩ : syracuseStep 25772701 = 9664763) B9664763
theorem B4023035 : Blo 1786094 4023035 := bstep (se 1 (by rfl) ⟨3017276, by rfl⟩ : syracuseStep 4023035 = 6034553) B6034553
theorem B15270727 : Blo 1786094 15270727 := bstep (se 1 (by rfl) ⟨11453045, by rfl⟩ : syracuseStep 15270727 = 22906091) B22906091
theorem B12559187 : Blo 1786094 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B7635809 : Blo 1786094 7635809 := bstep (se 2 (by rfl) ⟨2863428, by rfl⟩ : syracuseStep 7635809 = 5726857) B5726857
theorem B14484433 : Blo 1786094 14484433 := bstep (se 2 (by rfl) ⟨5431662, by rfl⟩ : syracuseStep 14484433 = 10863325) B10863325
theorem B3818495 : Blo 1786094 3818495 := bstep (se 1 (by rfl) ⟨2863871, by rfl⟩ : syracuseStep 3818495 = 5727743) B5727743
theorem B1786911 : Blo 1786094 1786911 := bstep (se 1 (by rfl) ⟨1340183, by rfl⟩ : syracuseStep 1786911 = 2680367) B2680367
theorem B4523111 : Blo 1786094 4523111 := bstep (se 1 (by rfl) ⟨3392333, by rfl⟩ : syracuseStep 4523111 = 6784667) B6784667
theorem B2680319 : Blo 1786094 2680319 := bstep (se 1 (by rfl) ⟨2010239, by rfl⟩ : syracuseStep 2680319 = 4020479) B4020479
theorem B1787551 : Blo 1786094 1787551 := bstep (se 1 (by rfl) ⟨1340663, by rfl⟩ : syracuseStep 1787551 = 2681327) B2681327
theorem B2680559 : Blo 1786094 2680559 := bstep (se 1 (by rfl) ⟨2010419, by rfl⟩ : syracuseStep 2680559 = 4020839) B4020839
theorem B1787647 : Blo 1786094 1787647 := bstep (se 1 (by rfl) ⟨1340735, by rfl⟩ : syracuseStep 1787647 = 2681471) B2681471
theorem B2680667 : Blo 1786094 2680667 := bstep (se 1 (by rfl) ⟨2010500, by rfl⟩ : syracuseStep 2680667 = 4021001) B4021001
theorem B1788063 : Blo 1786094 1788063 := bstep (se 1 (by rfl) ⟨1341047, by rfl⟩ : syracuseStep 1788063 = 2682095) B2682095
theorem B5097865 : Blo 1786094 5097865 := bstep (se 2 (by rfl) ⟨1911699, by rfl⟩ : syracuseStep 5097865 = 3823399) B3823399
theorem B6785471 : Blo 1786094 6785471 := bstep (se 1 (by rfl) ⟨5089103, by rfl⟩ : syracuseStep 6785471 = 10178207) B10178207
theorem B3017209 : Blo 1786094 3017209 := bstep (se 2 (by rfl) ⟨1131453, by rfl⟩ : syracuseStep 3017209 = 2262907) B2262907
theorem B8703713 : Blo 1786094 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B5435191 : Blo 1786094 5435191 := bstep (se 1 (by rfl) ⟨4076393, by rfl⟩ : syracuseStep 5435191 = 8152787) B8152787
theorem B10178459 : Blo 1786094 10178459 := bstep (se 1 (by rfl) ⟨7633844, by rfl⟩ : syracuseStep 10178459 = 15267689) B15267689
theorem B10866631 : Blo 1786094 10866631 := bstep (se 1 (by rfl) ⟨8149973, by rfl⟩ : syracuseStep 10866631 = 16299947) B16299947
theorem B4526057 : Blo 1786094 4526057 := bstep (se 2 (by rfl) ⟨1697271, by rfl⟩ : syracuseStep 4526057 = 3394543) B3394543
theorem B11014427 : Blo 1786094 11014427 := bstep (se 1 (by rfl) ⟨8260820, by rfl⟩ : syracuseStep 11014427 = 16521641) B16521641
theorem B69628409 : Blo 1786094 69628409 := bstep (se 2 (by rfl) ⟨26110653, by rfl⟩ : syracuseStep 69628409 = 52221307) B52221307
theorem B2863615 : Blo 1786094 2863615 := bstep (se 1 (by rfl) ⟨2147711, by rfl⟩ : syracuseStep 2863615 = 4295423) B4295423
theorem B123843401 : Blo 1786094 123843401 := bstep (se 2 (by rfl) ⟨46441275, by rfl⟩ : syracuseStep 123843401 = 92882551) B92882551
theorem B4019111 : Blo 1786094 4019111 := bstep (se 1 (by rfl) ⟨3014333, by rfl⟩ : syracuseStep 4019111 = 6028667) B6028667
theorem B4019759 : Blo 1786094 4019759 := bstep (se 1 (by rfl) ⟨3014819, by rfl⟩ : syracuseStep 4019759 = 6029639) B6029639
theorem B46447187 : Blo 1786094 46447187 := bstep (se 1 (by rfl) ⟨34835390, by rfl⟩ : syracuseStep 46447187 = 69670781) B69670781
theorem B43457759 : Blo 1786094 43457759 := bstep (se 1 (by rfl) ⟨32593319, by rfl⟩ : syracuseStep 43457759 = 65186639) B65186639
theorem B7740647 : Blo 1786094 7740647 := bstep (se 1 (by rfl) ⟨5805485, by rfl⟩ : syracuseStep 7740647 = 11610971) B11610971
theorem B6110471 : Blo 1786094 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B4022099 : Blo 1786094 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B8372791 : Blo 1786094 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B2679407 : Blo 1786094 2679407 := bstep (se 1 (by rfl) ⟨2009555, by rfl⟩ : syracuseStep 2679407 = 4019111) B4019111
theorem B4022945 : Blo 1786094 4022945 := bstep (se 2 (by rfl) ⟨1508604, by rfl⟩ : syracuseStep 4022945 = 3017209) B3017209
theorem B3818153 : Blo 1786094 3818153 := bstep (se 2 (by rfl) ⟨1431807, by rfl⟩ : syracuseStep 3818153 = 2863615) B2863615
theorem B3015407 : Blo 1786094 3015407 := bstep (se 1 (by rfl) ⟨2261555, by rfl⟩ : syracuseStep 3015407 = 4523111) B4523111
theorem B495436661 : Blo 1786094 495436661 := bstep (se 5 (by rfl) ⟨23223593, by rfl⟩ : syracuseStep 495436661 = 46447187) B46447187
theorem B1786879 : Blo 1786094 1786879 := bstep (se 1 (by rfl) ⟨1340159, by rfl⟩ : syracuseStep 1786879 = 2680319) B2680319
theorem B2679839 : Blo 1786094 2679839 := bstep (se 1 (by rfl) ⟨2009879, by rfl⟩ : syracuseStep 2679839 = 4019759) B4019759
theorem B1787039 : Blo 1786094 1787039 := bstep (se 1 (by rfl) ⟨1340279, by rfl⟩ : syracuseStep 1787039 = 2680559) B2680559
theorem B1787111 : Blo 1786094 1787111 := bstep (se 1 (by rfl) ⟨1340333, by rfl⟩ : syracuseStep 1787111 = 2680667) B2680667
theorem B4523647 : Blo 1786094 4523647 := bstep (se 1 (by rfl) ⟨3392735, by rfl⟩ : syracuseStep 4523647 = 6785471) B6785471
theorem B23209901 : Blo 1786094 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B4073647 : Blo 1786094 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B2681399 : Blo 1786094 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B6785639 : Blo 1786094 6785639 := bstep (se 1 (by rfl) ⟨5089229, by rfl⟩ : syracuseStep 6785639 = 10178459) B10178459
theorem B3017371 : Blo 1786094 3017371 := bstep (se 1 (by rfl) ⟨2263028, by rfl⟩ : syracuseStep 3017371 = 4526057) B4526057
theorem B2681579 : Blo 1786094 2681579 := bstep (se 1 (by rfl) ⟨2011184, by rfl⟩ : syracuseStep 2681579 = 4022369) B4022369
theorem B46418939 : Blo 1786094 46418939 := bstep (se 1 (by rfl) ⟨34814204, by rfl⟩ : syracuseStep 46418939 = 69628409) B69628409
theorem B2682023 : Blo 1786094 2682023 := bstep (se 1 (by rfl) ⟨2011517, by rfl⟩ : syracuseStep 2682023 = 4023035) B4023035
theorem B82562267 : Blo 1786094 82562267 := bstep (se 1 (by rfl) ⟨61921700, by rfl⟩ : syracuseStep 82562267 = 123843401) B123843401
theorem B5090539 : Blo 1786094 5090539 := bstep (se 1 (by rfl) ⟨3817904, by rfl⟩ : syracuseStep 5090539 = 7635809) B7635809
theorem B29371805 : Blo 1786094 29371805 := bstep (se 3 (by rfl) ⟨5507213, by rfl⟩ : syracuseStep 29371805 = 11014427) B11014427
theorem B20360969 : Blo 1786094 20360969 := bstep (se 2 (by rfl) ⟨7635363, by rfl⟩ : syracuseStep 20360969 = 15270727) B15270727
theorem B19312577 : Blo 1786094 19312577 := bstep (se 2 (by rfl) ⟨7242216, by rfl⟩ : syracuseStep 19312577 = 14484433) B14484433
theorem B28971839 : Blo 1786094 28971839 := bstep (se 1 (by rfl) ⟨21728879, by rfl⟩ : syracuseStep 28971839 = 43457759) B43457759
theorem B7246921 : Blo 1786094 7246921 := bstep (se 2 (by rfl) ⟨2717595, by rfl⟩ : syracuseStep 7246921 = 5435191) B5435191
theorem B14488841 : Blo 1786094 14488841 := bstep (se 2 (by rfl) ⟨5433315, by rfl⟩ : syracuseStep 14488841 = 10866631) B10866631
theorem B10180349 : Blo 1786094 10180349 := bstep (se 3 (by rfl) ⟨1908815, by rfl⟩ : syracuseStep 10180349 = 3817631) B3817631
theorem B6797153 : Blo 1786094 6797153 := bstep (se 2 (by rfl) ⟨2548932, by rfl⟩ : syracuseStep 6797153 = 5097865) B5097865
theorem B2545663 : Blo 1786094 2545663 := bstep (se 1 (by rfl) ⟨1909247, by rfl⟩ : syracuseStep 2545663 = 3818495) B3818495
theorem B34363601 : Blo 1786094 34363601 := bstep (se 2 (by rfl) ⟨12886350, by rfl⟩ : syracuseStep 34363601 = 25772701) B25772701
theorem B5160431 : Blo 1786094 5160431 := bstep (se 1 (by rfl) ⟨3870323, by rfl⟩ : syracuseStep 5160431 = 7740647) B7740647
theorem B5431529 : Blo 1786094 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B44654885 : Blo 1786094 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B1786271 : Blo 1786094 1786271 := bstep (se 1 (by rfl) ⟨1339703, by rfl⟩ : syracuseStep 1786271 = 2679407) B2679407
theorem B1786559 : Blo 1786094 1786559 := bstep (se 1 (by rfl) ⟨1339919, by rfl⟩ : syracuseStep 1786559 = 2679839) B2679839
theorem B4023161 : Blo 1786094 4023161 := bstep (se 2 (by rfl) ⟨1508685, by rfl⟩ : syracuseStep 4023161 = 3017371) B3017371
theorem B1787599 : Blo 1786094 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B4523759 : Blo 1786094 4523759 := bstep (se 1 (by rfl) ⟨3392819, by rfl⟩ : syracuseStep 4523759 = 6785639) B6785639
theorem B1787719 : Blo 1786094 1787719 := bstep (se 1 (by rfl) ⟨1340789, by rfl⟩ : syracuseStep 1787719 = 2681579) B2681579
theorem B1788015 : Blo 1786094 1788015 := bstep (se 1 (by rfl) ⟨1341011, by rfl⟩ : syracuseStep 1788015 = 2682023) B2682023
theorem B6031529 : Blo 1786094 6031529 := bstep (se 2 (by rfl) ⟨2261823, by rfl⟩ : syracuseStep 6031529 = 4523647) B4523647
theorem B19581203 : Blo 1786094 19581203 := bstep (se 1 (by rfl) ⟨14685902, by rfl⟩ : syracuseStep 19581203 = 29371805) B29371805
theorem B3394217 : Blo 1786094 3394217 := bstep (se 2 (by rfl) ⟨1272831, by rfl⟩ : syracuseStep 3394217 = 2545663) B2545663
theorem B2681963 : Blo 1786094 2681963 := bstep (se 1 (by rfl) ⟨2011472, by rfl⟩ : syracuseStep 2681963 = 4022945) B4022945
theorem B2010271 : Blo 1786094 2010271 := bstep (se 1 (by rfl) ⟨1507703, by rfl⟩ : syracuseStep 2010271 = 3015407) B3015407
theorem B38636909 : Blo 1786094 38636909 := bstep (se 3 (by rfl) ⟨7244420, by rfl⟩ : syracuseStep 38636909 = 14488841) B14488841
theorem B6786899 : Blo 1786094 6786899 := bstep (se 1 (by rfl) ⟨5090174, by rfl⟩ : syracuseStep 6786899 = 10180349) B10180349
theorem B9662561 : Blo 1786094 9662561 := bstep (se 2 (by rfl) ⟨3623460, by rfl⟩ : syracuseStep 9662561 = 7246921) B7246921
theorem B22909067 : Blo 1786094 22909067 := bstep (se 1 (by rfl) ⟨17181800, by rfl⟩ : syracuseStep 22909067 = 34363601) B34363601
theorem B6787385 : Blo 1786094 6787385 := bstep (se 2 (by rfl) ⟨2545269, by rfl⟩ : syracuseStep 6787385 = 5090539) B5090539
theorem B30945959 : Blo 1786094 30945959 := bstep (se 1 (by rfl) ⟨23209469, by rfl⟩ : syracuseStep 30945959 = 46418939) B46418939
theorem B18125741 : Blo 1786094 18125741 := bstep (se 3 (by rfl) ⟨3398576, by rfl⟩ : syracuseStep 18125741 = 6797153) B6797153
theorem B12875051 : Blo 1786094 12875051 := bstep (se 1 (by rfl) ⟨9656288, by rfl⟩ : syracuseStep 12875051 = 19312577) B19312577
theorem B2545435 : Blo 1786094 2545435 := bstep (se 1 (by rfl) ⟨1909076, by rfl⟩ : syracuseStep 2545435 = 3818153) B3818153
theorem B19314559 : Blo 1786094 19314559 := bstep (se 1 (by rfl) ⟨14485919, by rfl⟩ : syracuseStep 19314559 = 28971839) B28971839
theorem B330291107 : Blo 1786094 330291107 := bstep (se 1 (by rfl) ⟨247718330, by rfl⟩ : syracuseStep 330291107 = 495436661) B495436661
theorem B15473267 : Blo 1786094 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B55041511 : Blo 1786094 55041511 := bstep (se 1 (by rfl) ⟨41281133, by rfl⟩ : syracuseStep 55041511 = 82562267) B82562267
theorem B3440287 : Blo 1786094 3440287 := bstep (se 1 (by rfl) ⟨2580215, by rfl⟩ : syracuseStep 3440287 = 5160431) B5160431
theorem B13573979 : Blo 1786094 13573979 := bstep (se 1 (by rfl) ⟨10180484, by rfl⟩ : syracuseStep 13573979 = 20360969) B20360969
theorem B3621019 : Blo 1786094 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B29769923 : Blo 1786094 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B12083827 : Blo 1786094 12083827 := bstep (se 1 (by rfl) ⟨9062870, by rfl⟩ : syracuseStep 12083827 = 18125741) B18125741
theorem B3015839 : Blo 1786094 3015839 := bstep (se 1 (by rfl) ⟨2261879, by rfl⟩ : syracuseStep 3015839 = 4523759) B4523759
theorem B220194071 : Blo 1786094 220194071 := bstep (se 1 (by rfl) ⟨165145553, by rfl⟩ : syracuseStep 220194071 = 330291107) B330291107
theorem B2680361 : Blo 1786094 2680361 := bstep (se 2 (by rfl) ⟨1005135, by rfl⟩ : syracuseStep 2680361 = 2010271) B2010271
theorem B10315511 : Blo 1786094 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B2262811 : Blo 1786094 2262811 := bstep (se 1 (by rfl) ⟨1697108, by rfl⟩ : syracuseStep 2262811 = 3394217) B3394217
theorem B1787975 : Blo 1786094 1787975 := bstep (se 1 (by rfl) ⟨1340981, by rfl⟩ : syracuseStep 1787975 = 2681963) B2681963
theorem B25757939 : Blo 1786094 25757939 := bstep (se 1 (by rfl) ⟨19318454, by rfl⟩ : syracuseStep 25757939 = 38636909) B38636909
theorem B3393913 : Blo 1786094 3393913 := bstep (se 2 (by rfl) ⟨1272717, by rfl⟩ : syracuseStep 3393913 = 2545435) B2545435
theorem B4524599 : Blo 1786094 4524599 := bstep (se 1 (by rfl) ⟨3393449, by rfl⟩ : syracuseStep 4524599 = 6786899) B6786899
theorem B6441707 : Blo 1786094 6441707 := bstep (se 1 (by rfl) ⟨4831280, by rfl⟩ : syracuseStep 6441707 = 9662561) B9662561
theorem B15272711 : Blo 1786094 15272711 := bstep (se 1 (by rfl) ⟨11454533, by rfl⟩ : syracuseStep 15272711 = 22909067) B22909067
theorem B4524923 : Blo 1786094 4524923 := bstep (se 1 (by rfl) ⟨3393692, by rfl⟩ : syracuseStep 4524923 = 6787385) B6787385
theorem B20630639 : Blo 1786094 20630639 := bstep (se 1 (by rfl) ⟨15472979, by rfl⟩ : syracuseStep 20630639 = 30945959) B30945959
theorem B2682107 : Blo 1786094 2682107 := bstep (se 1 (by rfl) ⟨2011580, by rfl⟩ : syracuseStep 2682107 = 4023161) B4023161
theorem B13054135 : Blo 1786094 13054135 := bstep (se 1 (by rfl) ⟨9790601, by rfl⟩ : syracuseStep 13054135 = 19581203) B19581203
theorem B73388681 : Blo 1786094 73388681 := bstep (se 2 (by rfl) ⟨27520755, by rfl⟩ : syracuseStep 73388681 = 55041511) B55041511
theorem B25752745 : Blo 1786094 25752745 := bstep (se 2 (by rfl) ⟨9657279, by rfl⟩ : syracuseStep 25752745 = 19314559) B19314559
theorem B9049319 : Blo 1786094 9049319 := bstep (se 1 (by rfl) ⟨6786989, by rfl⟩ : syracuseStep 9049319 = 13573979) B13573979
theorem B8583367 : Blo 1786094 8583367 := bstep (se 1 (by rfl) ⟨6437525, by rfl⟩ : syracuseStep 8583367 = 12875051) B12875051
theorem B4021019 : Blo 1786094 4021019 := bstep (se 1 (by rfl) ⟨3015764, by rfl⟩ : syracuseStep 4021019 = 6031529) B6031529
theorem B4587049 : Blo 1786094 4587049 := bstep (se 2 (by rfl) ⟨1720143, by rfl⟩ : syracuseStep 4587049 = 3440287) B3440287
theorem B11444489 : Blo 1786094 11444489 := bstep (se 2 (by rfl) ⟨4291683, by rfl⟩ : syracuseStep 11444489 = 8583367) B8583367
theorem B1786907 : Blo 1786094 1786907 := bstep (se 1 (by rfl) ⟨1340180, by rfl⟩ : syracuseStep 1786907 = 2680361) B2680361
theorem B17171959 : Blo 1786094 17171959 := bstep (se 1 (by rfl) ⟨12878969, by rfl⟩ : syracuseStep 17171959 = 25757939) B25757939
theorem B3016399 : Blo 1786094 3016399 := bstep (se 1 (by rfl) ⟨2262299, by rfl⟩ : syracuseStep 3016399 = 4524599) B4524599
theorem B4294471 : Blo 1786094 4294471 := bstep (se 1 (by rfl) ⟨3220853, by rfl⟩ : syracuseStep 4294471 = 6441707) B6441707
theorem B2680679 : Blo 1786094 2680679 := bstep (se 1 (by rfl) ⟨2010509, by rfl⟩ : syracuseStep 2680679 = 4021019) B4021019
theorem B3016615 : Blo 1786094 3016615 := bstep (se 1 (by rfl) ⟨2262461, by rfl⟩ : syracuseStep 3016615 = 4524923) B4524923
theorem B1788071 : Blo 1786094 1788071 := bstep (se 1 (by rfl) ⟨1341053, by rfl⟩ : syracuseStep 1788071 = 2682107) B2682107
theorem B3017081 : Blo 1786094 3017081 := bstep (se 2 (by rfl) ⟨1131405, by rfl⟩ : syracuseStep 3017081 = 2262811) B2262811
theorem B4828025 : Blo 1786094 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B24464261 : Blo 1786094 24464261 := bstep (se 4 (by rfl) ⟨2293524, by rfl⟩ : syracuseStep 24464261 = 4587049) B4587049
theorem B48925787 : Blo 1786094 48925787 := bstep (se 1 (by rfl) ⟨36694340, by rfl⟩ : syracuseStep 48925787 = 73388681) B73388681
theorem B4525217 : Blo 1786094 4525217 := bstep (se 2 (by rfl) ⟨1696956, by rfl⟩ : syracuseStep 4525217 = 3393913) B3393913
theorem B2010559 : Blo 1786094 2010559 := bstep (se 1 (by rfl) ⟨1507919, by rfl⟩ : syracuseStep 2010559 = 3015839) B3015839
theorem B6032879 : Blo 1786094 6032879 := bstep (se 1 (by rfl) ⟨4524659, by rfl⟩ : syracuseStep 6032879 = 9049319) B9049319
theorem B146796047 : Blo 1786094 146796047 := bstep (se 1 (by rfl) ⟨110097035, by rfl⟩ : syracuseStep 146796047 = 220194071) B220194071
theorem B6877007 : Blo 1786094 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B34336993 : Blo 1786094 34336993 := bstep (se 2 (by rfl) ⟨12876372, by rfl⟩ : syracuseStep 34336993 = 25752745) B25752745
theorem B19846615 : Blo 1786094 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B17405513 : Blo 1786094 17405513 := bstep (se 2 (by rfl) ⟨6527067, by rfl⟩ : syracuseStep 17405513 = 13054135) B13054135
theorem B16111769 : Blo 1786094 16111769 := bstep (se 2 (by rfl) ⟨6041913, by rfl⟩ : syracuseStep 16111769 = 12083827) B12083827
theorem B10181807 : Blo 1786094 10181807 := bstep (se 1 (by rfl) ⟨7636355, by rfl⟩ : syracuseStep 10181807 = 15272711) B15272711
theorem B13753759 : Blo 1786094 13753759 := bstep (se 1 (by rfl) ⟨10315319, by rfl⟩ : syracuseStep 13753759 = 20630639) B20630639
theorem B1787119 : Blo 1786094 1787119 := bstep (se 1 (by rfl) ⟨1340339, by rfl⟩ : syracuseStep 1787119 = 2680679) B2680679
theorem B2680745 : Blo 1786094 2680745 := bstep (se 2 (by rfl) ⟨1005279, by rfl⟩ : syracuseStep 2680745 = 2010559) B2010559
theorem B26462153 : Blo 1786094 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B3016811 : Blo 1786094 3016811 := bstep (se 1 (by rfl) ⟨2262608, by rfl⟩ : syracuseStep 3016811 = 4525217) B4525217
theorem B97864031 : Blo 1786094 97864031 := bstep (se 1 (by rfl) ⟨73398023, by rfl⟩ : syracuseStep 97864031 = 146796047) B146796047
theorem B7629659 : Blo 1786094 7629659 := bstep (se 1 (by rfl) ⟨5722244, by rfl⟩ : syracuseStep 7629659 = 11444489) B11444489
theorem B130468765 : Blo 1786094 130468765 := bstep (se 3 (by rfl) ⟨24462893, by rfl⟩ : syracuseStep 130468765 = 48925787) B48925787
theorem B11603675 : Blo 1786094 11603675 := bstep (se 1 (by rfl) ⟨8702756, by rfl⟩ : syracuseStep 11603675 = 17405513) B17405513
theorem B2011387 : Blo 1786094 2011387 := bstep (se 1 (by rfl) ⟨1508540, by rfl⟩ : syracuseStep 2011387 = 3017081) B3017081
theorem B18338345 : Blo 1786094 18338345 := bstep (se 2 (by rfl) ⟨6876879, by rfl⟩ : syracuseStep 18338345 = 13753759) B13753759
theorem B6787871 : Blo 1786094 6787871 := bstep (se 1 (by rfl) ⟨5090903, by rfl⟩ : syracuseStep 6787871 = 10181807) B10181807
theorem B12874733 : Blo 1786094 12874733 := bstep (se 3 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 12874733 = 4828025) B4828025
theorem B4584671 : Blo 1786094 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B45782657 : Blo 1786094 45782657 := bstep (se 2 (by rfl) ⟨17168496, by rfl⟩ : syracuseStep 45782657 = 34336993) B34336993
theorem B42964717 : Blo 1786094 42964717 := bstep (se 3 (by rfl) ⟨8055884, by rfl⟩ : syracuseStep 42964717 = 16111769) B16111769
theorem B16309507 : Blo 1786094 16309507 := bstep (se 1 (by rfl) ⟨12232130, by rfl⟩ : syracuseStep 16309507 = 24464261) B24464261
theorem B22895945 : Blo 1786094 22895945 := bstep (se 2 (by rfl) ⟨8585979, by rfl⟩ : syracuseStep 22895945 = 17171959) B17171959
theorem B4021865 : Blo 1786094 4021865 := bstep (se 2 (by rfl) ⟨1508199, by rfl⟩ : syracuseStep 4021865 = 3016399) B3016399
theorem B4021919 : Blo 1786094 4021919 := bstep (se 1 (by rfl) ⟨3016439, by rfl⟩ : syracuseStep 4021919 = 6032879) B6032879
theorem B5725961 : Blo 1786094 5725961 := bstep (se 2 (by rfl) ⟨2147235, by rfl⟩ : syracuseStep 5725961 = 4294471) B4294471
theorem B4022153 : Blo 1786094 4022153 := bstep (se 2 (by rfl) ⟨1508307, by rfl⟩ : syracuseStep 4022153 = 3016615) B3016615
theorem B3056447 : Blo 1786094 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B173958353 : Blo 1786094 173958353 := bstep (se 2 (by rfl) ⟨65234382, by rfl⟩ : syracuseStep 173958353 = 130468765) B130468765
theorem B1787163 : Blo 1786094 1787163 := bstep (se 1 (by rfl) ⟨1340372, by rfl⟩ : syracuseStep 1787163 = 2680745) B2680745
theorem B65242687 : Blo 1786094 65242687 := bstep (se 1 (by rfl) ⟨48932015, by rfl⟩ : syracuseStep 65242687 = 97864031) B97864031
theorem B15263963 : Blo 1786094 15263963 := bstep (se 1 (by rfl) ⟨11447972, by rfl⟩ : syracuseStep 15263963 = 22895945) B22895945
theorem B2681243 : Blo 1786094 2681243 := bstep (se 1 (by rfl) ⟨2010932, by rfl⟩ : syracuseStep 2681243 = 4021865) B4021865
theorem B2681279 : Blo 1786094 2681279 := bstep (se 1 (by rfl) ⟨2010959, by rfl⟩ : syracuseStep 2681279 = 4021919) B4021919
theorem B7735783 : Blo 1786094 7735783 := bstep (se 1 (by rfl) ⟨5801837, by rfl⟩ : syracuseStep 7735783 = 11603675) B11603675
theorem B2681435 : Blo 1786094 2681435 := bstep (se 1 (by rfl) ⟨2011076, by rfl⟩ : syracuseStep 2681435 = 4022153) B4022153
theorem B2681849 : Blo 1786094 2681849 := bstep (se 2 (by rfl) ⟨1005693, by rfl⟩ : syracuseStep 2681849 = 2011387) B2011387
theorem B12225563 : Blo 1786094 12225563 := bstep (se 1 (by rfl) ⟨9169172, by rfl⟩ : syracuseStep 12225563 = 18338345) B18338345
theorem B4525247 : Blo 1786094 4525247 := bstep (se 1 (by rfl) ⟨3393935, by rfl⟩ : syracuseStep 4525247 = 6787871) B6787871
theorem B2011207 : Blo 1786094 2011207 := bstep (se 1 (by rfl) ⟨1508405, by rfl⟩ : syracuseStep 2011207 = 3016811) B3016811
theorem B21746009 : Blo 1786094 21746009 := bstep (se 2 (by rfl) ⟨8154753, by rfl⟩ : syracuseStep 21746009 = 16309507) B16309507
theorem B8583155 : Blo 1786094 8583155 := bstep (se 1 (by rfl) ⟨6437366, by rfl⟩ : syracuseStep 8583155 = 12874733) B12874733
theorem B30521771 : Blo 1786094 30521771 := bstep (se 1 (by rfl) ⟨22891328, by rfl⟩ : syracuseStep 30521771 = 45782657) B45782657
theorem B5086439 : Blo 1786094 5086439 := bstep (se 1 (by rfl) ⟨3814829, by rfl⟩ : syracuseStep 5086439 = 7629659) B7629659
theorem B57286289 : Blo 1786094 57286289 := bstep (se 2 (by rfl) ⟨21482358, by rfl⟩ : syracuseStep 57286289 = 42964717) B42964717
theorem B3817307 : Blo 1786094 3817307 := bstep (se 1 (by rfl) ⟨2862980, by rfl⟩ : syracuseStep 3817307 = 5725961) B5725961
theorem B70565741 : Blo 1786094 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B10314377 : Blo 1786094 10314377 := bstep (se 2 (by rfl) ⟨3867891, by rfl⟩ : syracuseStep 10314377 = 7735783) B7735783
theorem B10175975 : Blo 1786094 10175975 := bstep (se 1 (by rfl) ⟨7631981, by rfl⟩ : syracuseStep 10175975 = 15263963) B15263963
theorem B1787495 : Blo 1786094 1787495 := bstep (se 1 (by rfl) ⟨1340621, by rfl⟩ : syracuseStep 1787495 = 2681243) B2681243
theorem B1787519 : Blo 1786094 1787519 := bstep (se 1 (by rfl) ⟨1340639, by rfl⟩ : syracuseStep 1787519 = 2681279) B2681279
theorem B1787623 : Blo 1786094 1787623 := bstep (se 1 (by rfl) ⟨1340717, by rfl⟩ : syracuseStep 1787623 = 2681435) B2681435
theorem B1787899 : Blo 1786094 1787899 := bstep (se 1 (by rfl) ⟨1340924, by rfl⟩ : syracuseStep 1787899 = 2681849) B2681849
theorem B3016831 : Blo 1786094 3016831 := bstep (se 1 (by rfl) ⟨2262623, by rfl⟩ : syracuseStep 3016831 = 4525247) B4525247
theorem B2681609 : Blo 1786094 2681609 := bstep (se 2 (by rfl) ⟨1005603, by rfl⟩ : syracuseStep 2681609 = 2011207) B2011207
theorem B5722103 : Blo 1786094 5722103 := bstep (se 1 (by rfl) ⟨4291577, by rfl⟩ : syracuseStep 5722103 = 8583155) B8583155
theorem B2544871 : Blo 1786094 2544871 := bstep (se 1 (by rfl) ⟨1908653, by rfl⟩ : syracuseStep 2544871 = 3817307) B3817307
theorem B47043827 : Blo 1786094 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B14497339 : Blo 1786094 14497339 := bstep (se 1 (by rfl) ⟨10873004, by rfl⟩ : syracuseStep 14497339 = 21746009) B21746009
theorem B2037631 : Blo 1786094 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B115972235 : Blo 1786094 115972235 := bstep (se 1 (by rfl) ⟨86979176, by rfl⟩ : syracuseStep 115972235 = 173958353) B173958353
theorem B20347847 : Blo 1786094 20347847 := bstep (se 1 (by rfl) ⟨15260885, by rfl⟩ : syracuseStep 20347847 = 30521771) B30521771
theorem B152763437 : Blo 1786094 152763437 := bstep (se 3 (by rfl) ⟨28643144, by rfl⟩ : syracuseStep 152763437 = 57286289) B57286289
theorem B8150375 : Blo 1786094 8150375 := bstep (se 1 (by rfl) ⟨6112781, by rfl⟩ : syracuseStep 8150375 = 12225563) B12225563
theorem B86990249 : Blo 1786094 86990249 := bstep (se 2 (by rfl) ⟨32621343, by rfl⟩ : syracuseStep 86990249 = 65242687) B65242687
theorem B3390959 : Blo 1786094 3390959 := bstep (se 1 (by rfl) ⟨2543219, by rfl⟩ : syracuseStep 3390959 = 5086439) B5086439
theorem B4022441 : Blo 1786094 4022441 := bstep (se 2 (by rfl) ⟨1508415, by rfl⟩ : syracuseStep 4022441 = 3016831) B3016831
theorem B6783983 : Blo 1786094 6783983 := bstep (se 1 (by rfl) ⟨5087987, by rfl⟩ : syracuseStep 6783983 = 10175975) B10175975
theorem B3393161 : Blo 1786094 3393161 := bstep (se 2 (by rfl) ⟨1272435, by rfl⟩ : syracuseStep 3393161 = 2544871) B2544871
theorem B1787739 : Blo 1786094 1787739 := bstep (se 1 (by rfl) ⟨1340804, by rfl⟩ : syracuseStep 1787739 = 2681609) B2681609
theorem B5433583 : Blo 1786094 5433583 := bstep (se 1 (by rfl) ⟨4075187, by rfl⟩ : syracuseStep 5433583 = 8150375) B8150375
theorem B57993499 : Blo 1786094 57993499 := bstep (se 1 (by rfl) ⟨43495124, by rfl⟩ : syracuseStep 57993499 = 86990249) B86990249
theorem B6876251 : Blo 1786094 6876251 := bstep (se 1 (by rfl) ⟨5157188, by rfl⟩ : syracuseStep 6876251 = 10314377) B10314377
theorem B31362551 : Blo 1786094 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B19329785 : Blo 1786094 19329785 := bstep (se 2 (by rfl) ⟨7248669, by rfl⟩ : syracuseStep 19329785 = 14497339) B14497339
theorem B2716841 : Blo 1786094 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B15258941 : Blo 1786094 15258941 := bstep (se 3 (by rfl) ⟨2861051, by rfl⟩ : syracuseStep 15258941 = 5722103) B5722103
theorem B77314823 : Blo 1786094 77314823 := bstep (se 1 (by rfl) ⟨57986117, by rfl⟩ : syracuseStep 77314823 = 115972235) B115972235
theorem B13565231 : Blo 1786094 13565231 := bstep (se 1 (by rfl) ⟨10173923, by rfl⟩ : syracuseStep 13565231 = 20347847) B20347847
theorem B101842291 : Blo 1786094 101842291 := bstep (se 1 (by rfl) ⟨76381718, by rfl⟩ : syracuseStep 101842291 = 152763437) B152763437
theorem B2260639 : Blo 1786094 2260639 := bstep (se 1 (by rfl) ⟨1695479, by rfl⟩ : syracuseStep 2260639 = 3390959) B3390959
theorem B77324665 : Blo 1786094 77324665 := bstep (se 2 (by rfl) ⟨28996749, by rfl⟩ : syracuseStep 77324665 = 57993499) B57993499
theorem B12886523 : Blo 1786094 12886523 := bstep (se 1 (by rfl) ⟨9664892, by rfl⟩ : syracuseStep 12886523 = 19329785) B19329785
theorem B4522655 : Blo 1786094 4522655 := bstep (se 1 (by rfl) ⟨3391991, by rfl⟩ : syracuseStep 4522655 = 6783983) B6783983
theorem B2262107 : Blo 1786094 2262107 := bstep (se 1 (by rfl) ⟨1696580, by rfl⟩ : syracuseStep 2262107 = 3393161) B3393161
theorem B20908367 : Blo 1786094 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B2681627 : Blo 1786094 2681627 := bstep (se 1 (by rfl) ⟨2011220, by rfl⟩ : syracuseStep 2681627 = 4022441) B4022441
theorem B7244777 : Blo 1786094 7244777 := bstep (se 2 (by rfl) ⟨2716791, by rfl⟩ : syracuseStep 7244777 = 5433583) B5433583
theorem B7244909 : Blo 1786094 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B543158885 : Blo 1786094 543158885 := bstep (se 4 (by rfl) ⟨50921145, by rfl⟩ : syracuseStep 543158885 = 101842291) B101842291
theorem B4584167 : Blo 1786094 4584167 := bstep (se 1 (by rfl) ⟨3438125, by rfl⟩ : syracuseStep 4584167 = 6876251) B6876251
theorem B10172627 : Blo 1786094 10172627 := bstep (se 1 (by rfl) ⟨7629470, by rfl⟩ : syracuseStep 10172627 = 15258941) B15258941
theorem B51543215 : Blo 1786094 51543215 := bstep (se 1 (by rfl) ⟨38657411, by rfl⟩ : syracuseStep 51543215 = 77314823) B77314823
theorem B9043487 : Blo 1786094 9043487 := bstep (se 1 (by rfl) ⟨6782615, by rfl⟩ : syracuseStep 9043487 = 13565231) B13565231
theorem B3014185 : Blo 1786094 3014185 := bstep (se 2 (by rfl) ⟨1130319, by rfl⟩ : syracuseStep 3014185 = 2260639) B2260639
theorem B3015103 : Blo 1786094 3015103 := bstep (se 1 (by rfl) ⟨2261327, by rfl⟩ : syracuseStep 3015103 = 4522655) B4522655
theorem B3056111 : Blo 1786094 3056111 := bstep (se 1 (by rfl) ⟨2292083, by rfl⟩ : syracuseStep 3056111 = 4584167) B4584167
theorem B1787751 : Blo 1786094 1787751 := bstep (se 1 (by rfl) ⟨1340813, by rfl⟩ : syracuseStep 1787751 = 2681627) B2681627
theorem B6032285 : Blo 1786094 6032285 := bstep (se 3 (by rfl) ⟨1131053, by rfl⟩ : syracuseStep 6032285 = 2262107) B2262107
theorem B362105923 : Blo 1786094 362105923 := bstep (se 1 (by rfl) ⟨271579442, by rfl⟩ : syracuseStep 362105923 = 543158885) B543158885
theorem B103099553 : Blo 1786094 103099553 := bstep (se 2 (by rfl) ⟨38662332, by rfl⟩ : syracuseStep 103099553 = 77324665) B77324665
theorem B13938911 : Blo 1786094 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B4829851 : Blo 1786094 4829851 := bstep (se 1 (by rfl) ⟨3622388, by rfl⟩ : syracuseStep 4829851 = 7244777) B7244777
theorem B4018913 : Blo 1786094 4018913 := bstep (se 2 (by rfl) ⟨1507092, by rfl⟩ : syracuseStep 4018913 = 3014185) B3014185
theorem B4829939 : Blo 1786094 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B34362143 : Blo 1786094 34362143 := bstep (se 1 (by rfl) ⟨25771607, by rfl⟩ : syracuseStep 34362143 = 51543215) B51543215
theorem B8591015 : Blo 1786094 8591015 := bstep (se 1 (by rfl) ⟨6443261, by rfl⟩ : syracuseStep 8591015 = 12886523) B12886523
theorem B6781751 : Blo 1786094 6781751 := bstep (se 1 (by rfl) ⟨5086313, by rfl⟩ : syracuseStep 6781751 = 10172627) B10172627
theorem B6028991 : Blo 1786094 6028991 := bstep (se 1 (by rfl) ⟨4521743, by rfl⟩ : syracuseStep 6028991 = 9043487) B9043487
theorem B2679275 : Blo 1786094 2679275 := bstep (se 1 (by rfl) ⟨2009456, by rfl⟩ : syracuseStep 2679275 = 4018913) B4018913
theorem B3219959 : Blo 1786094 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B5727343 : Blo 1786094 5727343 := bstep (se 1 (by rfl) ⟨4295507, by rfl⟩ : syracuseStep 5727343 = 8591015) B8591015
theorem B68733035 : Blo 1786094 68733035 := bstep (se 1 (by rfl) ⟨51549776, by rfl⟩ : syracuseStep 68733035 = 103099553) B103099553
theorem B9292607 : Blo 1786094 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B22908095 : Blo 1786094 22908095 := bstep (se 1 (by rfl) ⟨17181071, by rfl⟩ : syracuseStep 22908095 = 34362143) B34362143
theorem B25759205 : Blo 1786094 25759205 := bstep (se 4 (by rfl) ⟨2414925, by rfl⟩ : syracuseStep 25759205 = 4829851) B4829851
theorem B482807897 : Blo 1786094 482807897 := bstep (se 2 (by rfl) ⟨181052961, by rfl⟩ : syracuseStep 482807897 = 362105923) B362105923
theorem B4019327 : Blo 1786094 4019327 := bstep (se 1 (by rfl) ⟨3014495, by rfl⟩ : syracuseStep 4019327 = 6028991) B6028991
theorem B2037407 : Blo 1786094 2037407 := bstep (se 1 (by rfl) ⟨1528055, by rfl⟩ : syracuseStep 2037407 = 3056111) B3056111
theorem B4020137 : Blo 1786094 4020137 := bstep (se 2 (by rfl) ⟨1507551, by rfl⟩ : syracuseStep 4020137 = 3015103) B3015103
theorem B4521167 : Blo 1786094 4521167 := bstep (se 1 (by rfl) ⟨3390875, by rfl⟩ : syracuseStep 4521167 = 6781751) B6781751
theorem B4021523 : Blo 1786094 4021523 := bstep (se 1 (by rfl) ⟨3016142, by rfl⟩ : syracuseStep 4021523 = 6032285) B6032285
theorem B321871931 : Blo 1786094 321871931 := bstep (se 1 (by rfl) ⟨241403948, by rfl⟩ : syracuseStep 321871931 = 482807897) B482807897
theorem B1786183 : Blo 1786094 1786183 := bstep (se 1 (by rfl) ⟨1339637, by rfl⟩ : syracuseStep 1786183 = 2679275) B2679275
theorem B2679551 : Blo 1786094 2679551 := bstep (se 1 (by rfl) ⟨2009663, by rfl⟩ : syracuseStep 2679551 = 4019327) B4019327
theorem B2680091 : Blo 1786094 2680091 := bstep (se 1 (by rfl) ⟨2010068, by rfl⟩ : syracuseStep 2680091 = 4020137) B4020137
theorem B8586557 : Blo 1786094 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B7636457 : Blo 1786094 7636457 := bstep (se 2 (by rfl) ⟨2863671, by rfl⟩ : syracuseStep 7636457 = 5727343) B5727343
theorem B5433085 : Blo 1786094 5433085 := bstep (se 3 (by rfl) ⟨1018703, by rfl⟩ : syracuseStep 5433085 = 2037407) B2037407
theorem B6195071 : Blo 1786094 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B15272063 : Blo 1786094 15272063 := bstep (se 1 (by rfl) ⟨11454047, by rfl⟩ : syracuseStep 15272063 = 22908095) B22908095
theorem B2681015 : Blo 1786094 2681015 := bstep (se 1 (by rfl) ⟨2010761, by rfl⟩ : syracuseStep 2681015 = 4021523) B4021523
theorem B17172803 : Blo 1786094 17172803 := bstep (se 1 (by rfl) ⟨12879602, by rfl⟩ : syracuseStep 17172803 = 25759205) B25759205
theorem B45822023 : Blo 1786094 45822023 := bstep (se 1 (by rfl) ⟨34366517, by rfl⟩ : syracuseStep 45822023 = 68733035) B68733035
theorem B3014111 : Blo 1786094 3014111 := bstep (se 1 (by rfl) ⟨2260583, by rfl⟩ : syracuseStep 3014111 = 4521167) B4521167
theorem B214581287 : Blo 1786094 214581287 := bstep (se 1 (by rfl) ⟨160935965, by rfl⟩ : syracuseStep 214581287 = 321871931) B321871931
theorem B30548015 : Blo 1786094 30548015 := bstep (se 1 (by rfl) ⟨22911011, by rfl⟩ : syracuseStep 30548015 = 45822023) B45822023
theorem B1786367 : Blo 1786094 1786367 := bstep (se 1 (by rfl) ⟨1339775, by rfl⟩ : syracuseStep 1786367 = 2679551) B2679551
theorem B1786727 : Blo 1786094 1786727 := bstep (se 1 (by rfl) ⟨1340045, by rfl⟩ : syracuseStep 1786727 = 2680091) B2680091
theorem B4130047 : Blo 1786094 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B28976453 : Blo 1786094 28976453 := bstep (se 4 (by rfl) ⟨2716542, by rfl⟩ : syracuseStep 28976453 = 5433085) B5433085
theorem B1787343 : Blo 1786094 1787343 := bstep (se 1 (by rfl) ⟨1340507, by rfl⟩ : syracuseStep 1787343 = 2681015) B2681015
theorem B2009407 : Blo 1786094 2009407 := bstep (se 1 (by rfl) ⟨1507055, by rfl⟩ : syracuseStep 2009407 = 3014111) B3014111
theorem B11448535 : Blo 1786094 11448535 := bstep (se 1 (by rfl) ⟨8586401, by rfl⟩ : syracuseStep 11448535 = 17172803) B17172803
theorem B5724371 : Blo 1786094 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B20363885 : Blo 1786094 20363885 := bstep (se 3 (by rfl) ⟨3818228, by rfl⟩ : syracuseStep 20363885 = 7636457) B7636457
theorem B10181375 : Blo 1786094 10181375 := bstep (se 1 (by rfl) ⟨7636031, by rfl⟩ : syracuseStep 10181375 = 15272063) B15272063
theorem B20365343 : Blo 1786094 20365343 := bstep (se 1 (by rfl) ⟨15274007, by rfl⟩ : syracuseStep 20365343 = 30548015) B30548015
theorem B2679209 : Blo 1786094 2679209 := bstep (se 2 (by rfl) ⟨1004703, by rfl⟩ : syracuseStep 2679209 = 2009407) B2009407
theorem B19317635 : Blo 1786094 19317635 := bstep (se 1 (by rfl) ⟨14488226, by rfl⟩ : syracuseStep 19317635 = 28976453) B28976453
theorem B13575923 : Blo 1786094 13575923 := bstep (se 1 (by rfl) ⟨10181942, by rfl⟩ : syracuseStep 13575923 = 20363885) B20363885
theorem B15264713 : Blo 1786094 15264713 := bstep (se 2 (by rfl) ⟨5724267, by rfl⟩ : syracuseStep 15264713 = 11448535) B11448535
theorem B6787583 : Blo 1786094 6787583 := bstep (se 1 (by rfl) ⟨5090687, by rfl⟩ : syracuseStep 6787583 = 10181375) B10181375
theorem B143054191 : Blo 1786094 143054191 := bstep (se 1 (by rfl) ⟨107290643, by rfl⟩ : syracuseStep 143054191 = 214581287) B214581287
theorem B22026917 : Blo 1786094 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B3816247 : Blo 1786094 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B1786139 : Blo 1786094 1786139 := bstep (se 1 (by rfl) ⟨1339604, by rfl⟩ : syracuseStep 1786139 = 2679209) B2679209
theorem B12878423 : Blo 1786094 12878423 := bstep (se 1 (by rfl) ⟨9658817, by rfl⟩ : syracuseStep 12878423 = 19317635) B19317635
theorem B5088329 : Blo 1786094 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B10176475 : Blo 1786094 10176475 := bstep (se 1 (by rfl) ⟨7632356, by rfl⟩ : syracuseStep 10176475 = 15264713) B15264713
theorem B13576895 : Blo 1786094 13576895 := bstep (se 1 (by rfl) ⟨10182671, by rfl⟩ : syracuseStep 13576895 = 20365343) B20365343
theorem B4525055 : Blo 1786094 4525055 := bstep (se 1 (by rfl) ⟨3393791, by rfl⟩ : syracuseStep 4525055 = 6787583) B6787583
theorem B14684611 : Blo 1786094 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B190738921 : Blo 1786094 190738921 := bstep (se 2 (by rfl) ⟨71527095, by rfl⟩ : syracuseStep 190738921 = 143054191) B143054191
theorem B9050615 : Blo 1786094 9050615 := bstep (se 1 (by rfl) ⟨6787961, by rfl⟩ : syracuseStep 9050615 = 13575923) B13575923
theorem B8585615 : Blo 1786094 8585615 := bstep (se 1 (by rfl) ⟨6439211, by rfl⟩ : syracuseStep 8585615 = 12878423) B12878423
theorem B19579481 : Blo 1786094 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B3392219 : Blo 1786094 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B3016703 : Blo 1786094 3016703 := bstep (se 1 (by rfl) ⟨2262527, by rfl⟩ : syracuseStep 3016703 = 4525055) B4525055
theorem B13568633 : Blo 1786094 13568633 := bstep (se 2 (by rfl) ⟨5088237, by rfl⟩ : syracuseStep 13568633 = 10176475) B10176475
theorem B6033743 : Blo 1786094 6033743 := bstep (se 1 (by rfl) ⟨4525307, by rfl⟩ : syracuseStep 6033743 = 9050615) B9050615
theorem B254318561 : Blo 1786094 254318561 := bstep (se 2 (by rfl) ⟨95369460, by rfl⟩ : syracuseStep 254318561 = 190738921) B190738921
theorem B9051263 : Blo 1786094 9051263 := bstep (se 1 (by rfl) ⟨6788447, by rfl⟩ : syracuseStep 9051263 = 13576895) B13576895
theorem B4022495 : Blo 1786094 4022495 := bstep (se 1 (by rfl) ⟨3016871, by rfl⟩ : syracuseStep 4022495 = 6033743) B6033743
theorem B9045755 : Blo 1786094 9045755 := bstep (se 1 (by rfl) ⟨6784316, by rfl⟩ : syracuseStep 9045755 = 13568633) B13568633
theorem B9045917 : Blo 1786094 9045917 := bstep (se 3 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 9045917 = 3392219) B3392219
theorem B13052987 : Blo 1786094 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B169545707 : Blo 1786094 169545707 := bstep (se 1 (by rfl) ⟨127159280, by rfl⟩ : syracuseStep 169545707 = 254318561) B254318561
theorem B2011135 : Blo 1786094 2011135 := bstep (se 1 (by rfl) ⟨1508351, by rfl⟩ : syracuseStep 2011135 = 3016703) B3016703
theorem B6034175 : Blo 1786094 6034175 := bstep (se 1 (by rfl) ⟨4525631, by rfl⟩ : syracuseStep 6034175 = 9051263) B9051263
theorem B22894973 : Blo 1786094 22894973 := bstep (se 3 (by rfl) ⟨4292807, by rfl⟩ : syracuseStep 22894973 = 8585615) B8585615
theorem B4022783 : Blo 1786094 4022783 := bstep (se 1 (by rfl) ⟨3017087, by rfl⟩ : syracuseStep 4022783 = 6034175) B6034175
theorem B6030503 : Blo 1786094 6030503 := bstep (se 1 (by rfl) ⟨4522877, by rfl⟩ : syracuseStep 6030503 = 9045755) B9045755
theorem B6030611 : Blo 1786094 6030611 := bstep (se 1 (by rfl) ⟨4522958, by rfl⟩ : syracuseStep 6030611 = 9045917) B9045917
theorem B15263315 : Blo 1786094 15263315 := bstep (se 1 (by rfl) ⟨11447486, by rfl⟩ : syracuseStep 15263315 = 22894973) B22894973
theorem B8701991 : Blo 1786094 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B2681513 : Blo 1786094 2681513 := bstep (se 2 (by rfl) ⟨1005567, by rfl⟩ : syracuseStep 2681513 = 2011135) B2011135
theorem B2681663 : Blo 1786094 2681663 := bstep (se 1 (by rfl) ⟨2011247, by rfl⟩ : syracuseStep 2681663 = 4022495) B4022495
theorem B113030471 : Blo 1786094 113030471 := bstep (se 1 (by rfl) ⟨84772853, by rfl⟩ : syracuseStep 113030471 = 169545707) B169545707
theorem B10175543 : Blo 1786094 10175543 := bstep (se 1 (by rfl) ⟨7631657, by rfl⟩ : syracuseStep 10175543 = 15263315) B15263315
theorem B5801327 : Blo 1786094 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B1787675 : Blo 1786094 1787675 := bstep (se 1 (by rfl) ⟨1340756, by rfl⟩ : syracuseStep 1787675 = 2681513) B2681513
theorem B1787775 : Blo 1786094 1787775 := bstep (se 1 (by rfl) ⟨1340831, by rfl⟩ : syracuseStep 1787775 = 2681663) B2681663
theorem B2681855 : Blo 1786094 2681855 := bstep (se 1 (by rfl) ⟨2011391, by rfl⟩ : syracuseStep 2681855 = 4022783) B4022783
theorem B75353647 : Blo 1786094 75353647 := bstep (se 1 (by rfl) ⟨56515235, by rfl⟩ : syracuseStep 75353647 = 113030471) B113030471
theorem B4020335 : Blo 1786094 4020335 := bstep (se 1 (by rfl) ⟨3015251, by rfl⟩ : syracuseStep 4020335 = 6030503) B6030503
theorem B4020407 : Blo 1786094 4020407 := bstep (se 1 (by rfl) ⟨3015305, by rfl⟩ : syracuseStep 4020407 = 6030611) B6030611
theorem B6783695 : Blo 1786094 6783695 := bstep (se 1 (by rfl) ⟨5087771, by rfl⟩ : syracuseStep 6783695 = 10175543) B10175543
theorem B3867551 : Blo 1786094 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B2680223 : Blo 1786094 2680223 := bstep (se 1 (by rfl) ⟨2010167, by rfl⟩ : syracuseStep 2680223 = 4020335) B4020335
theorem B2680271 : Blo 1786094 2680271 := bstep (se 1 (by rfl) ⟨2010203, by rfl⟩ : syracuseStep 2680271 = 4020407) B4020407
theorem B1787903 : Blo 1786094 1787903 := bstep (se 1 (by rfl) ⟨1340927, by rfl⟩ : syracuseStep 1787903 = 2681855) B2681855
theorem B100471529 : Blo 1786094 100471529 := bstep (se 2 (by rfl) ⟨37676823, by rfl⟩ : syracuseStep 100471529 = 75353647) B75353647
theorem B4522463 : Blo 1786094 4522463 := bstep (se 1 (by rfl) ⟨3391847, by rfl⟩ : syracuseStep 4522463 = 6783695) B6783695
theorem B1786815 : Blo 1786094 1786815 := bstep (se 1 (by rfl) ⟨1340111, by rfl⟩ : syracuseStep 1786815 = 2680223) B2680223
theorem B1786847 : Blo 1786094 1786847 := bstep (se 1 (by rfl) ⟨1340135, by rfl⟩ : syracuseStep 1786847 = 2680271) B2680271
theorem B66981019 : Blo 1786094 66981019 := bstep (se 1 (by rfl) ⟨50235764, by rfl⟩ : syracuseStep 66981019 = 100471529) B100471529
theorem B41253877 : Blo 1786094 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B3014975 : Blo 1786094 3014975 := bstep (se 1 (by rfl) ⟨2261231, by rfl⟩ : syracuseStep 3014975 = 4522463) B4522463
theorem B55005169 : Blo 1786094 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B89308025 : Blo 1786094 89308025 := bstep (se 2 (by rfl) ⟨33490509, by rfl⟩ : syracuseStep 89308025 = 66981019) B66981019
theorem B2009983 : Blo 1786094 2009983 := bstep (se 1 (by rfl) ⟨1507487, by rfl⟩ : syracuseStep 2009983 = 3014975) B3014975
theorem B73340225 : Blo 1786094 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B59538683 : Blo 1786094 59538683 := bstep (se 1 (by rfl) ⟨44654012, by rfl⟩ : syracuseStep 59538683 = 89308025) B89308025
theorem B158769821 : Blo 1786094 158769821 := bstep (se 3 (by rfl) ⟨29769341, by rfl⟩ : syracuseStep 158769821 = 59538683) B59538683
theorem B2679977 : Blo 1786094 2679977 := bstep (se 2 (by rfl) ⟨1004991, by rfl⟩ : syracuseStep 2679977 = 2009983) B2009983
theorem B48893483 : Blo 1786094 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B1786651 : Blo 1786094 1786651 := bstep (se 1 (by rfl) ⟨1339988, by rfl⟩ : syracuseStep 1786651 = 2679977) B2679977
theorem B105846547 : Blo 1786094 105846547 := bstep (se 1 (by rfl) ⟨79384910, by rfl⟩ : syracuseStep 105846547 = 158769821) B158769821
theorem B130382621 : Blo 1786094 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B86921747 : Blo 1786094 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B141128729 : Blo 1786094 141128729 := bstep (se 2 (by rfl) ⟨52923273, by rfl⟩ : syracuseStep 141128729 = 105846547) B105846547
theorem B94085819 : Blo 1786094 94085819 := bstep (se 1 (by rfl) ⟨70564364, by rfl⟩ : syracuseStep 94085819 = 141128729) B141128729
theorem B57947831 : Blo 1786094 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B62723879 : Blo 1786094 62723879 := bstep (se 1 (by rfl) ⟨47042909, by rfl⟩ : syracuseStep 62723879 = 94085819) B94085819
theorem B38631887 : Blo 1786094 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B41815919 : Blo 1786094 41815919 := bstep (se 1 (by rfl) ⟨31361939, by rfl⟩ : syracuseStep 41815919 = 62723879) B62723879
theorem B25754591 : Blo 1786094 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B17169727 : Blo 1786094 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B27877279 : Blo 1786094 27877279 := bstep (se 1 (by rfl) ⟨20907959, by rfl⟩ : syracuseStep 27877279 = 41815919) B41815919
theorem B37169705 : Blo 1786094 37169705 := bstep (se 2 (by rfl) ⟨13938639, by rfl⟩ : syracuseStep 37169705 = 27877279) B27877279
theorem B22892969 : Blo 1786094 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B15261979 : Blo 1786094 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B99119213 : Blo 1786094 99119213 := bstep (se 3 (by rfl) ⟨18584852, by rfl⟩ : syracuseStep 99119213 = 37169705) B37169705
theorem B20349305 : Blo 1786094 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B66079475 : Blo 1786094 66079475 := bstep (se 1 (by rfl) ⟨49559606, by rfl⟩ : syracuseStep 66079475 = 99119213) B99119213
theorem B13566203 : Blo 1786094 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B44052983 : Blo 1786094 44052983 := bstep (se 1 (by rfl) ⟨33039737, by rfl⟩ : syracuseStep 44052983 = 66079475) B66079475
theorem B9044135 : Blo 1786094 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B29368655 : Blo 1786094 29368655 := bstep (se 1 (by rfl) ⟨22026491, by rfl⟩ : syracuseStep 29368655 = 44052983) B44052983
theorem B6029423 : Blo 1786094 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B19579103 : Blo 1786094 19579103 := bstep (se 1 (by rfl) ⟨14684327, by rfl⟩ : syracuseStep 19579103 = 29368655) B29368655
theorem B13052735 : Blo 1786094 13052735 := bstep (se 1 (by rfl) ⟨9789551, by rfl⟩ : syracuseStep 13052735 = 19579103) B19579103
theorem B4019615 : Blo 1786094 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B2679743 : Blo 1786094 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B8701823 : Blo 1786094 8701823 := bstep (se 1 (by rfl) ⟨6526367, by rfl⟩ : syracuseStep 8701823 = 13052735) B13052735
theorem B1786495 : Blo 1786094 1786495 := bstep (se 1 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 1786495 = 2679743) B2679743
theorem B5801215 : Blo 1786094 5801215 := bstep (se 1 (by rfl) ⟨4350911, by rfl⟩ : syracuseStep 5801215 = 8701823) B8701823
theorem B7734953 : Blo 1786094 7734953 := bstep (se 2 (by rfl) ⟨2900607, by rfl⟩ : syracuseStep 7734953 = 5801215) B5801215
theorem B5156635 : Blo 1786094 5156635 := bstep (se 1 (by rfl) ⟨3867476, by rfl⟩ : syracuseStep 5156635 = 7734953) B7734953
theorem B6875513 : Blo 1786094 6875513 := bstep (se 2 (by rfl) ⟨2578317, by rfl⟩ : syracuseStep 6875513 = 5156635) B5156635
theorem B4583675 : Blo 1786094 4583675 := bstep (se 1 (by rfl) ⟨3437756, by rfl⟩ : syracuseStep 4583675 = 6875513) B6875513
theorem B12223133 : Blo 1786094 12223133 := bstep (se 3 (by rfl) ⟨2291837, by rfl⟩ : syracuseStep 12223133 = 4583675) B4583675
theorem B8148755 : Blo 1786094 8148755 := bstep (se 1 (by rfl) ⟨6111566, by rfl⟩ : syracuseStep 8148755 = 12223133) B12223133
theorem B5432503 : Blo 1786094 5432503 := bstep (se 1 (by rfl) ⟨4074377, by rfl⟩ : syracuseStep 5432503 = 8148755) B8148755
theorem B7243337 : Blo 1786094 7243337 := bstep (se 2 (by rfl) ⟨2716251, by rfl⟩ : syracuseStep 7243337 = 5432503) B5432503
theorem B4828891 : Blo 1786094 4828891 := bstep (se 1 (by rfl) ⟨3621668, by rfl⟩ : syracuseStep 4828891 = 7243337) B7243337
theorem B6438521 : Blo 1786094 6438521 := bstep (se 2 (by rfl) ⟨2414445, by rfl⟩ : syracuseStep 6438521 = 4828891) B4828891
theorem B4292347 : Blo 1786094 4292347 := bstep (se 1 (by rfl) ⟨3219260, by rfl⟩ : syracuseStep 4292347 = 6438521) B6438521
theorem B5723129 : Blo 1786094 5723129 := bstep (se 2 (by rfl) ⟨2146173, by rfl⟩ : syracuseStep 5723129 = 4292347) B4292347
theorem B3815419 : Blo 1786094 3815419 := bstep (se 1 (by rfl) ⟨2861564, by rfl⟩ : syracuseStep 3815419 = 5723129) B5723129
theorem B5087225 : Blo 1786094 5087225 := bstep (se 2 (by rfl) ⟨1907709, by rfl⟩ : syracuseStep 5087225 = 3815419) B3815419
theorem B3391483 : Blo 1786094 3391483 := bstep (se 1 (by rfl) ⟨2543612, by rfl⟩ : syracuseStep 3391483 = 5087225) B5087225
theorem B4521977 : Blo 1786094 4521977 := bstep (se 2 (by rfl) ⟨1695741, by rfl⟩ : syracuseStep 4521977 = 3391483) B3391483
theorem B3014651 : Blo 1786094 3014651 := bstep (se 1 (by rfl) ⟨2260988, by rfl⟩ : syracuseStep 3014651 = 4521977) B4521977
theorem B2009767 : Blo 1786094 2009767 := bstep (se 1 (by rfl) ⟨1507325, by rfl⟩ : syracuseStep 2009767 = 3014651) B3014651
theorem B2679689 : Blo 1786094 2679689 := bstep (se 2 (by rfl) ⟨1004883, by rfl⟩ : syracuseStep 2679689 = 2009767) B2009767
theorem B1786459 : Blo 1786094 1786459 := bstep (se 1 (by rfl) ⟨1339844, by rfl⟩ : syracuseStep 1786459 = 2679689) B2679689

theorem C0 (j : ℕ) (h1 : 446523 ≤ j) (h2 : j ≤ 447022) : Blo 1786094 (4 * j + 3) := by
  interval_cases j
  · exact B1786095
  · exact B1786099
  · exact B1786103
  · exact B1786107
  · exact B1786111
  · exact B1786115
  · exact B1786119
  · exact B1786123
  · exact B1786127
  · exact B1786131
  · exact B1786135
  · exact B1786139
  · exact B1786143
  · exact B1786147
  · exact B1786151
  · exact B1786155
  · exact B1786159
  · exact B1786163
  · exact B1786167
  · exact B1786171
  · exact B1786175
  · exact B1786179
  · exact B1786183
  · exact B1786187
  · exact B1786191
  · exact B1786195
  · exact B1786199
  · exact B1786203
  · exact B1786207
  · exact B1786211
  · exact B1786215
  · exact B1786219
  · exact B1786223
  · exact B1786227
  · exact B1786231
  · exact B1786235
  · exact B1786239
  · exact B1786243
  · exact B1786247
  · exact B1786251
  · exact B1786255
  · exact B1786259
  · exact B1786263
  · exact B1786267
  · exact B1786271
  · exact B1786275
  · exact B1786279
  · exact B1786283
  · exact B1786287
  · exact B1786291
  · exact B1786295
  · exact B1786299
  · exact B1786303
  · exact B1786307
  · exact B1786311
  · exact B1786315
  · exact B1786319
  · exact B1786323
  · exact B1786327
  · exact B1786331
  · exact B1786335
  · exact B1786339
  · exact B1786343
  · exact B1786347
  · exact B1786351
  · exact B1786355
  · exact B1786359
  · exact B1786363
  · exact B1786367
  · exact B1786371
  · exact B1786375
  · exact B1786379
  · exact B1786383
  · exact B1786387
  · exact B1786391
  · exact B1786395
  · exact B1786399
  · exact B1786403
  · exact B1786407
  · exact B1786411
  · exact B1786415
  · exact B1786419
  · exact B1786423
  · exact B1786427
  · exact B1786431
  · exact B1786435
  · exact B1786439
  · exact B1786443
  · exact B1786447
  · exact B1786451
  · exact B1786455
  · exact B1786459
  · exact B1786463
  · exact B1786467
  · exact B1786471
  · exact B1786475
  · exact B1786479
  · exact B1786483
  · exact B1786487
  · exact B1786491
  · exact B1786495
  · exact B1786499
  · exact B1786503
  · exact B1786507
  · exact B1786511
  · exact B1786515
  · exact B1786519
  · exact B1786523
  · exact B1786527
  · exact B1786531
  · exact B1786535
  · exact B1786539
  · exact B1786543
  · exact B1786547
  · exact B1786551
  · exact B1786555
  · exact B1786559
  · exact B1786563
  · exact B1786567
  · exact B1786571
  · exact B1786575
  · exact B1786579
  · exact B1786583
  · exact B1786587
  · exact B1786591
  · exact B1786595
  · exact B1786599
  · exact B1786603
  · exact B1786607
  · exact B1786611
  · exact B1786615
  · exact B1786619
  · exact B1786623
  · exact B1786627
  · exact B1786631
  · exact B1786635
  · exact B1786639
  · exact B1786643
  · exact B1786647
  · exact B1786651
  · exact B1786655
  · exact B1786659
  · exact B1786663
  · exact B1786667
  · exact B1786671
  · exact B1786675
  · exact B1786679
  · exact B1786683
  · exact B1786687
  · exact B1786691
  · exact B1786695
  · exact B1786699
  · exact B1786703
  · exact B1786707
  · exact B1786711
  · exact B1786715
  · exact B1786719
  · exact B1786723
  · exact B1786727
  · exact B1786731
  · exact B1786735
  · exact B1786739
  · exact B1786743
  · exact B1786747
  · exact B1786751
  · exact B1786755
  · exact B1786759
  · exact B1786763
  · exact B1786767
  · exact B1786771
  · exact B1786775
  · exact B1786779
  · exact B1786783
  · exact B1786787
  · exact B1786791
  · exact B1786795
  · exact B1786799
  · exact B1786803
  · exact B1786807
  · exact B1786811
  · exact B1786815
  · exact B1786819
  · exact B1786823
  · exact B1786827
  · exact B1786831
  · exact B1786835
  · exact B1786839
  · exact B1786843
  · exact B1786847
  · exact B1786851
  · exact B1786855
  · exact B1786859
  · exact B1786863
  · exact B1786867
  · exact B1786871
  · exact B1786875
  · exact B1786879
  · exact B1786883
  · exact B1786887
  · exact B1786891
  · exact B1786895
  · exact B1786899
  · exact B1786903
  · exact B1786907
  · exact B1786911
  · exact B1786915
  · exact B1786919
  · exact B1786923
  · exact B1786927
  · exact B1786931
  · exact B1786935
  · exact B1786939
  · exact B1786943
  · exact B1786947
  · exact B1786951
  · exact B1786955
  · exact B1786959
  · exact B1786963
  · exact B1786967
  · exact B1786971
  · exact B1786975
  · exact B1786979
  · exact B1786983
  · exact B1786987
  · exact B1786991
  · exact B1786995
  · exact B1786999
  · exact B1787003
  · exact B1787007
  · exact B1787011
  · exact B1787015
  · exact B1787019
  · exact B1787023
  · exact B1787027
  · exact B1787031
  · exact B1787035
  · exact B1787039
  · exact B1787043
  · exact B1787047
  · exact B1787051
  · exact B1787055
  · exact B1787059
  · exact B1787063
  · exact B1787067
  · exact B1787071
  · exact B1787075
  · exact B1787079
  · exact B1787083
  · exact B1787087
  · exact B1787091
  · exact B1787095
  · exact B1787099
  · exact B1787103
  · exact B1787107
  · exact B1787111
  · exact B1787115
  · exact B1787119
  · exact B1787123
  · exact B1787127
  · exact B1787131
  · exact B1787135
  · exact B1787139
  · exact B1787143
  · exact B1787147
  · exact B1787151
  · exact B1787155
  · exact B1787159
  · exact B1787163
  · exact B1787167
  · exact B1787171
  · exact B1787175
  · exact B1787179
  · exact B1787183
  · exact B1787187
  · exact B1787191
  · exact B1787195
  · exact B1787199
  · exact B1787203
  · exact B1787207
  · exact B1787211
  · exact B1787215
  · exact B1787219
  · exact B1787223
  · exact B1787227
  · exact B1787231
  · exact B1787235
  · exact B1787239
  · exact B1787243
  · exact B1787247
  · exact B1787251
  · exact B1787255
  · exact B1787259
  · exact B1787263
  · exact B1787267
  · exact B1787271
  · exact B1787275
  · exact B1787279
  · exact B1787283
  · exact B1787287
  · exact B1787291
  · exact B1787295
  · exact B1787299
  · exact B1787303
  · exact B1787307
  · exact B1787311
  · exact B1787315
  · exact B1787319
  · exact B1787323
  · exact B1787327
  · exact B1787331
  · exact B1787335
  · exact B1787339
  · exact B1787343
  · exact B1787347
  · exact B1787351
  · exact B1787355
  · exact B1787359
  · exact B1787363
  · exact B1787367
  · exact B1787371
  · exact B1787375
  · exact B1787379
  · exact B1787383
  · exact B1787387
  · exact B1787391
  · exact B1787395
  · exact B1787399
  · exact B1787403
  · exact B1787407
  · exact B1787411
  · exact B1787415
  · exact B1787419
  · exact B1787423
  · exact B1787427
  · exact B1787431
  · exact B1787435
  · exact B1787439
  · exact B1787443
  · exact B1787447
  · exact B1787451
  · exact B1787455
  · exact B1787459
  · exact B1787463
  · exact B1787467
  · exact B1787471
  · exact B1787475
  · exact B1787479
  · exact B1787483
  · exact B1787487
  · exact B1787491
  · exact B1787495
  · exact B1787499
  · exact B1787503
  · exact B1787507
  · exact B1787511
  · exact B1787515
  · exact B1787519
  · exact B1787523
  · exact B1787527
  · exact B1787531
  · exact B1787535
  · exact B1787539
  · exact B1787543
  · exact B1787547
  · exact B1787551
  · exact B1787555
  · exact B1787559
  · exact B1787563
  · exact B1787567
  · exact B1787571
  · exact B1787575
  · exact B1787579
  · exact B1787583
  · exact B1787587
  · exact B1787591
  · exact B1787595
  · exact B1787599
  · exact B1787603
  · exact B1787607
  · exact B1787611
  · exact B1787615
  · exact B1787619
  · exact B1787623
  · exact B1787627
  · exact B1787631
  · exact B1787635
  · exact B1787639
  · exact B1787643
  · exact B1787647
  · exact B1787651
  · exact B1787655
  · exact B1787659
  · exact B1787663
  · exact B1787667
  · exact B1787671
  · exact B1787675
  · exact B1787679
  · exact B1787683
  · exact B1787687
  · exact B1787691
  · exact B1787695
  · exact B1787699
  · exact B1787703
  · exact B1787707
  · exact B1787711
  · exact B1787715
  · exact B1787719
  · exact B1787723
  · exact B1787727
  · exact B1787731
  · exact B1787735
  · exact B1787739
  · exact B1787743
  · exact B1787747
  · exact B1787751
  · exact B1787755
  · exact B1787759
  · exact B1787763
  · exact B1787767
  · exact B1787771
  · exact B1787775
  · exact B1787779
  · exact B1787783
  · exact B1787787
  · exact B1787791
  · exact B1787795
  · exact B1787799
  · exact B1787803
  · exact B1787807
  · exact B1787811
  · exact B1787815
  · exact B1787819
  · exact B1787823
  · exact B1787827
  · exact B1787831
  · exact B1787835
  · exact B1787839
  · exact B1787843
  · exact B1787847
  · exact B1787851
  · exact B1787855
  · exact B1787859
  · exact B1787863
  · exact B1787867
  · exact B1787871
  · exact B1787875
  · exact B1787879
  · exact B1787883
  · exact B1787887
  · exact B1787891
  · exact B1787895
  · exact B1787899
  · exact B1787903
  · exact B1787907
  · exact B1787911
  · exact B1787915
  · exact B1787919
  · exact B1787923
  · exact B1787927
  · exact B1787931
  · exact B1787935
  · exact B1787939
  · exact B1787943
  · exact B1787947
  · exact B1787951
  · exact B1787955
  · exact B1787959
  · exact B1787963
  · exact B1787967
  · exact B1787971
  · exact B1787975
  · exact B1787979
  · exact B1787983
  · exact B1787987
  · exact B1787991
  · exact B1787995
  · exact B1787999
  · exact B1788003
  · exact B1788007
  · exact B1788011
  · exact B1788015
  · exact B1788019
  · exact B1788023
  · exact B1788027
  · exact B1788031
  · exact B1788035
  · exact B1788039
  · exact B1788043
  · exact B1788047
  · exact B1788051
  · exact B1788055
  · exact B1788059
  · exact B1788063
  · exact B1788067
  · exact B1788071
  · exact B1788075
  · exact B1788079
  · exact B1788083
  · exact B1788087
  · exact B1788091

theorem solution (m : ℕ) (hlo : 1786094 ≤ m) (hhi : m ≤ 1788094) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 446523 ≤ j := by omega
    have hj2 : j ≤ 447022 := by omega
    have hb : Blo 1786094 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
