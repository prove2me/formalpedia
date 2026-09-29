-- Prove2me | solution 1 for syracuse_descends_range_758332_762332
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:19.877605+00:00
-- url     : https://prove2.me/submissions/841b7547-fbdc-4b93-aab7-714803071df8

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


theorem B2162693 : Blo 758332 2162693 := bbase (se 4 (by rfl) ⟨202752, by rfl⟩ : syracuseStep 2162693 = 405505) (by norm_num)
theorem B1441901 : Blo 758332 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B1081517 : Blo 758332 1081517 := bbase (se 3 (by rfl) ⟨202784, by rfl⟩ : syracuseStep 1081517 = 405569) (by norm_num)
theorem B2162933 : Blo 758332 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1540349 : Blo 758332 1540349 := bbase (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) (by norm_num)
theorem B1442053 : Blo 758332 1442053 := bbase (se 4 (by rfl) ⟨135192, by rfl⟩ : syracuseStep 1442053 = 270385) (by norm_num)
theorem B2163125 : Blo 758332 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B1442357 : Blo 758332 1442357 := bbase (se 5 (by rfl) ⟨67610, by rfl⟩ : syracuseStep 1442357 = 135221) (by norm_num)
theorem B21955157 : Blo 758332 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B6488693 : Blo 758332 6488693 := bbase (se 5 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 6488693 = 608315) (by norm_num)
theorem B1082269 : Blo 758332 1082269 := bbase (se 3 (by rfl) ⟨202925, by rfl⟩ : syracuseStep 1082269 = 405851) (by norm_num)
theorem B1737629 : Blo 758332 1737629 := bbase (se 3 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 1737629 = 651611) (by norm_num)
theorem B2884517 : Blo 758332 2884517 := bbase (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) (by norm_num)
theorem B9765845 : Blo 758332 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B853141 : Blo 758332 853141 := bbase (se 6 (by rfl) ⟨19995, by rfl⟩ : syracuseStep 853141 = 39991) (by norm_num)
theorem B853177 : Blo 758332 853177 := bbase (se 2 (by rfl) ⟨319941, by rfl⟩ : syracuseStep 853177 = 639883) (by norm_num)
theorem B2884805 : Blo 758332 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B853213 : Blo 758332 853213 := bbase (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) (by norm_num)
theorem B853249 : Blo 758332 853249 := bbase (se 2 (by rfl) ⟨319968, by rfl⟩ : syracuseStep 853249 = 639937) (by norm_num)
theorem B853285 : Blo 758332 853285 := bbase (se 4 (by rfl) ⟨79995, by rfl⟩ : syracuseStep 853285 = 159991) (by norm_num)
theorem B1443109 : Blo 758332 1443109 := bbase (se 4 (by rfl) ⟨135291, by rfl⟩ : syracuseStep 1443109 = 270583) (by norm_num)
theorem B853321 : Blo 758332 853321 := bbase (se 2 (by rfl) ⟨319995, by rfl⟩ : syracuseStep 853321 = 639991) (by norm_num)
theorem B853357 : Blo 758332 853357 := bbase (se 3 (by rfl) ⟨160004, by rfl⟩ : syracuseStep 853357 = 320009) (by norm_num)
theorem B853393 : Blo 758332 853393 := bbase (se 2 (by rfl) ⟨320022, by rfl⟩ : syracuseStep 853393 = 640045) (by norm_num)
theorem B2164117 : Blo 758332 2164117 := bbase (se 6 (by rfl) ⟨50721, by rfl⟩ : syracuseStep 2164117 = 101443) (by norm_num)
theorem B853429 : Blo 758332 853429 := bbase (se 5 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 853429 = 80009) (by norm_num)
theorem B1443253 : Blo 758332 1443253 := bbase (se 5 (by rfl) ⟨67652, by rfl⟩ : syracuseStep 1443253 = 135305) (by norm_num)
theorem B853465 : Blo 758332 853465 := bbase (se 2 (by rfl) ⟨320049, by rfl⟩ : syracuseStep 853465 = 640099) (by norm_num)
theorem B853501 : Blo 758332 853501 := bbase (se 3 (by rfl) ⟨160031, by rfl⟩ : syracuseStep 853501 = 320063) (by norm_num)
theorem B853537 : Blo 758332 853537 := bbase (se 2 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 853537 = 640153) (by norm_num)
theorem B853573 : Blo 758332 853573 := bbase (se 4 (by rfl) ⟨80022, by rfl⟩ : syracuseStep 853573 = 160045) (by norm_num)
theorem B1443413 : Blo 758332 1443413 := bbase (se 8 (by rfl) ⟨8457, by rfl⟩ : syracuseStep 1443413 = 16915) (by norm_num)
theorem B853609 : Blo 758332 853609 := bbase (se 2 (by rfl) ⟨320103, by rfl⟩ : syracuseStep 853609 = 640207) (by norm_num)
theorem B853645 : Blo 758332 853645 := bbase (se 3 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 853645 = 320117) (by norm_num)
theorem B853681 : Blo 758332 853681 := bbase (se 2 (by rfl) ⟨320130, by rfl⟩ : syracuseStep 853681 = 640261) (by norm_num)
theorem B1083061 : Blo 758332 1083061 := bbase (se 5 (by rfl) ⟨50768, by rfl⟩ : syracuseStep 1083061 = 101537) (by norm_num)
theorem B853717 : Blo 758332 853717 := bbase (se 7 (by rfl) ⟨10004, by rfl⟩ : syracuseStep 853717 = 20009) (by norm_num)
theorem B15599317 : Blo 758332 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B1443557 : Blo 758332 1443557 := bbase (se 4 (by rfl) ⟨135333, by rfl⟩ : syracuseStep 1443557 = 270667) (by norm_num)
theorem B853753 : Blo 758332 853753 := bbase (se 2 (by rfl) ⟨320157, by rfl⟩ : syracuseStep 853753 = 640315) (by norm_num)
theorem B853789 : Blo 758332 853789 := bbase (se 3 (by rfl) ⟨160085, by rfl⟩ : syracuseStep 853789 = 320171) (by norm_num)
theorem B853825 : Blo 758332 853825 := bbase (se 2 (by rfl) ⟨320184, by rfl⟩ : syracuseStep 853825 = 640369) (by norm_num)
theorem B1279813 : Blo 758332 1279813 := bbase (se 4 (by rfl) ⟨119982, by rfl⟩ : syracuseStep 1279813 = 239965) (by norm_num)
theorem B4327253 : Blo 758332 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B853861 : Blo 758332 853861 := bbase (se 4 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 853861 = 160099) (by norm_num)
theorem B853897 : Blo 758332 853897 := bbase (se 2 (by rfl) ⟨320211, by rfl⟩ : syracuseStep 853897 = 640423) (by norm_num)
theorem B1542037 : Blo 758332 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B3475349 : Blo 758332 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B1279901 : Blo 758332 1279901 := bbase (se 3 (by rfl) ⟨239981, by rfl⟩ : syracuseStep 1279901 = 479963) (by norm_num)
theorem B853933 : Blo 758332 853933 := bbase (se 3 (by rfl) ⟨160112, by rfl⟩ : syracuseStep 853933 = 320225) (by norm_num)
theorem B853969 : Blo 758332 853969 := bbase (se 2 (by rfl) ⟨320238, by rfl⟩ : syracuseStep 853969 = 640477) (by norm_num)
theorem B854005 : Blo 758332 854005 := bbase (se 5 (by rfl) ⟨40031, by rfl⟩ : syracuseStep 854005 = 80063) (by norm_num)
theorem B1443845 : Blo 758332 1443845 := bbase (se 4 (by rfl) ⟨135360, by rfl⟩ : syracuseStep 1443845 = 270721) (by norm_num)
theorem B1083397 : Blo 758332 1083397 := bbase (se 4 (by rfl) ⟨101568, by rfl⟩ : syracuseStep 1083397 = 203137) (by norm_num)
theorem B854041 : Blo 758332 854041 := bbase (se 2 (by rfl) ⟨320265, by rfl⟩ : syracuseStep 854041 = 640531) (by norm_num)
theorem B1280029 : Blo 758332 1280029 := bbase (se 3 (by rfl) ⟨240005, by rfl⟩ : syracuseStep 1280029 = 480011) (by norm_num)
theorem B854077 : Blo 758332 854077 := bbase (se 3 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 854077 = 320279) (by norm_num)
theorem B854113 : Blo 758332 854113 := bbase (se 2 (by rfl) ⟨320292, by rfl⟩ : syracuseStep 854113 = 640585) (by norm_num)
theorem B1280117 : Blo 758332 1280117 := bbase (se 5 (by rfl) ⟨60005, by rfl⟩ : syracuseStep 1280117 = 120011) (by norm_num)
theorem B854149 : Blo 758332 854149 := bbase (se 4 (by rfl) ⟨80076, by rfl⟩ : syracuseStep 854149 = 160153) (by norm_num)
theorem B3082373 : Blo 758332 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B1443997 : Blo 758332 1443997 := bbase (se 3 (by rfl) ⟨270749, by rfl⟩ : syracuseStep 1443997 = 541499) (by norm_num)
theorem B854185 : Blo 758332 854185 := bbase (se 2 (by rfl) ⟨320319, by rfl⟩ : syracuseStep 854185 = 640639) (by norm_num)
theorem B854221 : Blo 758332 854221 := bbase (se 3 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 854221 = 320333) (by norm_num)
theorem B1083613 : Blo 758332 1083613 := bbase (se 3 (by rfl) ⟨203177, by rfl⟩ : syracuseStep 1083613 = 406355) (by norm_num)
theorem B854257 : Blo 758332 854257 := bbase (se 2 (by rfl) ⟨320346, by rfl⟩ : syracuseStep 854257 = 640693) (by norm_num)
theorem B1280245 : Blo 758332 1280245 := bbase (se 5 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 1280245 = 120023) (by norm_num)
theorem B854293 : Blo 758332 854293 := bbase (se 6 (by rfl) ⟨20022, by rfl⟩ : syracuseStep 854293 = 40045) (by norm_num)
theorem B854329 : Blo 758332 854329 := bbase (se 2 (by rfl) ⟨320373, by rfl⟩ : syracuseStep 854329 = 640747) (by norm_num)
theorem B1706309 : Blo 758332 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B1280333 : Blo 758332 1280333 := bbase (se 3 (by rfl) ⟨240062, by rfl⟩ : syracuseStep 1280333 = 480125) (by norm_num)
theorem B854365 : Blo 758332 854365 := bbase (se 3 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 854365 = 320387) (by norm_num)
theorem B2885989 : Blo 758332 2885989 := bbase (se 4 (by rfl) ⟨270561, by rfl⟩ : syracuseStep 2885989 = 541123) (by norm_num)
theorem B854401 : Blo 758332 854401 := bbase (se 2 (by rfl) ⟨320400, by rfl⟩ : syracuseStep 854401 = 640801) (by norm_num)
theorem B1706381 : Blo 758332 1706381 := bbase (se 3 (by rfl) ⟨319946, by rfl⟩ : syracuseStep 1706381 = 639893) (by norm_num)
theorem B3082645 : Blo 758332 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B1542557 : Blo 758332 1542557 := bbase (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) (by norm_num)
theorem B854437 : Blo 758332 854437 := bbase (se 4 (by rfl) ⟨80103, by rfl⟩ : syracuseStep 854437 = 160207) (by norm_num)
theorem B854473 : Blo 758332 854473 := bbase (se 2 (by rfl) ⟨320427, by rfl⟩ : syracuseStep 854473 = 640855) (by norm_num)
theorem B1280461 : Blo 758332 1280461 := bbase (se 3 (by rfl) ⟨240086, by rfl⟩ : syracuseStep 1280461 = 480173) (by norm_num)
theorem B1444301 : Blo 758332 1444301 := bbase (se 3 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 1444301 = 541613) (by norm_num)
theorem B1706453 : Blo 758332 1706453 := bbase (se 7 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 1706453 = 39995) (by norm_num)
theorem B2165221 : Blo 758332 2165221 := bbase (se 4 (by rfl) ⟨202989, by rfl⟩ : syracuseStep 2165221 = 405979) (by norm_num)
theorem B854509 : Blo 758332 854509 := bbase (se 3 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 854509 = 320441) (by norm_num)
theorem B1542653 : Blo 758332 1542653 := bbase (se 3 (by rfl) ⟨289247, by rfl⟩ : syracuseStep 1542653 = 578495) (by norm_num)
theorem B854545 : Blo 758332 854545 := bbase (se 2 (by rfl) ⟨320454, by rfl⟩ : syracuseStep 854545 = 640909) (by norm_num)
theorem B1706525 : Blo 758332 1706525 := bbase (se 3 (by rfl) ⟨319973, by rfl⟩ : syracuseStep 1706525 = 639947) (by norm_num)
theorem B1280549 : Blo 758332 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B854581 : Blo 758332 854581 := bbase (se 5 (by rfl) ⟨40058, by rfl⟩ : syracuseStep 854581 = 80117) (by norm_num)
theorem B1083989 : Blo 758332 1083989 := bbase (se 8 (by rfl) ⟨6351, by rfl⟩ : syracuseStep 1083989 = 12703) (by norm_num)
theorem B854617 : Blo 758332 854617 := bbase (se 2 (by rfl) ⟨320481, by rfl⟩ : syracuseStep 854617 = 640963) (by norm_num)
theorem B1706597 : Blo 758332 1706597 := bbase (se 4 (by rfl) ⟨159993, by rfl⟩ : syracuseStep 1706597 = 319987) (by norm_num)
theorem B854653 : Blo 758332 854653 := bbase (se 3 (by rfl) ⟨160247, by rfl⟩ : syracuseStep 854653 = 320495) (by norm_num)
theorem B2886293 : Blo 758332 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B854689 : Blo 758332 854689 := bbase (se 2 (by rfl) ⟨320508, by rfl⟩ : syracuseStep 854689 = 641017) (by norm_num)
theorem B1280677 : Blo 758332 1280677 := bbase (se 4 (by rfl) ⟨120063, by rfl⟩ : syracuseStep 1280677 = 240127) (by norm_num)
theorem B1706669 : Blo 758332 1706669 := bbase (se 3 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 1706669 = 640001) (by norm_num)
theorem B854725 : Blo 758332 854725 := bbase (se 4 (by rfl) ⟨80130, by rfl⟩ : syracuseStep 854725 = 160261) (by norm_num)
theorem B854761 : Blo 758332 854761 := bbase (se 2 (by rfl) ⟨320535, by rfl⟩ : syracuseStep 854761 = 641071) (by norm_num)
theorem B1706741 : Blo 758332 1706741 := bbase (se 5 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 1706741 = 160007) (by norm_num)
theorem B1280765 : Blo 758332 1280765 := bbase (se 3 (by rfl) ⟨240143, by rfl⟩ : syracuseStep 1280765 = 480287) (by norm_num)
theorem B854797 : Blo 758332 854797 := bbase (se 3 (by rfl) ⟨160274, by rfl⟩ : syracuseStep 854797 = 320549) (by norm_num)
theorem B854833 : Blo 758332 854833 := bbase (se 2 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 854833 = 641125) (by norm_num)
theorem B1706813 : Blo 758332 1706813 := bbase (se 3 (by rfl) ⟨320027, by rfl⟩ : syracuseStep 1706813 = 640055) (by norm_num)
theorem B854869 : Blo 758332 854869 := bbase (se 9 (by rfl) ⟨2504, by rfl⟩ : syracuseStep 854869 = 5009) (by norm_num)
theorem B854905 : Blo 758332 854905 := bbase (se 2 (by rfl) ⟨320589, by rfl⟩ : syracuseStep 854905 = 641179) (by norm_num)
theorem B1280893 : Blo 758332 1280893 := bbase (se 3 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 1280893 = 480335) (by norm_num)
theorem B1706885 : Blo 758332 1706885 := bbase (se 4 (by rfl) ⟨160020, by rfl⟩ : syracuseStep 1706885 = 320041) (by norm_num)
theorem B854941 : Blo 758332 854941 := bbase (se 3 (by rfl) ⟨160301, by rfl⟩ : syracuseStep 854941 = 320603) (by norm_num)
theorem B854977 : Blo 758332 854977 := bbase (se 2 (by rfl) ⟨320616, by rfl⟩ : syracuseStep 854977 = 641233) (by norm_num)
theorem B1706957 : Blo 758332 1706957 := bbase (se 3 (by rfl) ⟨320054, by rfl⟩ : syracuseStep 1706957 = 640109) (by norm_num)
theorem B1280981 : Blo 758332 1280981 := bbase (se 7 (by rfl) ⟨15011, by rfl⟩ : syracuseStep 1280981 = 30023) (by norm_num)
theorem B855013 : Blo 758332 855013 := bbase (se 4 (by rfl) ⟨80157, by rfl⟩ : syracuseStep 855013 = 160315) (by norm_num)
theorem B4328437 : Blo 758332 4328437 := bbase (se 5 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 4328437 = 405791) (by norm_num)
theorem B6163445 : Blo 758332 6163445 := bbase (se 5 (by rfl) ⟨288911, by rfl⟩ : syracuseStep 6163445 = 577823) (by norm_num)
theorem B855049 : Blo 758332 855049 := bbase (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) (by norm_num)
theorem B1707029 : Blo 758332 1707029 := bbase (se 6 (by rfl) ⟨40008, by rfl⟩ : syracuseStep 1707029 = 80017) (by norm_num)
theorem B1543205 : Blo 758332 1543205 := bbase (se 4 (by rfl) ⟨144675, by rfl⟩ : syracuseStep 1543205 = 289351) (by norm_num)
theorem B855085 : Blo 758332 855085 := bbase (se 3 (by rfl) ⟨160328, by rfl⟩ : syracuseStep 855085 = 320657) (by norm_num)
theorem B855121 : Blo 758332 855121 := bbase (se 2 (by rfl) ⟨320670, by rfl⟩ : syracuseStep 855121 = 641341) (by norm_num)
theorem B1281109 : Blo 758332 1281109 := bbase (se 8 (by rfl) ⟨7506, by rfl⟩ : syracuseStep 1281109 = 15013) (by norm_num)
theorem B1707101 : Blo 758332 1707101 := bbase (se 3 (by rfl) ⟨320081, by rfl⟩ : syracuseStep 1707101 = 640163) (by norm_num)
theorem B1215605 : Blo 758332 1215605 := bbase (se 5 (by rfl) ⟨56981, by rfl⟩ : syracuseStep 1215605 = 113963) (by norm_num)
theorem B855157 : Blo 758332 855157 := bbase (se 5 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 855157 = 80171) (by norm_num)
theorem B855193 : Blo 758332 855193 := bbase (se 2 (by rfl) ⟨320697, by rfl⟩ : syracuseStep 855193 = 641395) (by norm_num)
theorem B1707173 : Blo 758332 1707173 := bbase (se 4 (by rfl) ⟨160047, by rfl⟩ : syracuseStep 1707173 = 320095) (by norm_num)
theorem B1281197 : Blo 758332 1281197 := bbase (se 3 (by rfl) ⟨240224, by rfl⟩ : syracuseStep 1281197 = 480449) (by norm_num)
theorem B3247285 : Blo 758332 3247285 := bbase (se 5 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 3247285 = 304433) (by norm_num)
theorem B855229 : Blo 758332 855229 := bbase (se 3 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 855229 = 320711) (by norm_num)
theorem B1445053 : Blo 758332 1445053 := bbase (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) (by norm_num)
theorem B855265 : Blo 758332 855265 := bbase (se 2 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 855265 = 641449) (by norm_num)
theorem B1707245 : Blo 758332 1707245 := bbase (se 3 (by rfl) ⟨320108, by rfl⟩ : syracuseStep 1707245 = 640217) (by norm_num)
theorem B1215733 : Blo 758332 1215733 := bbase (se 5 (by rfl) ⟨56987, by rfl⟩ : syracuseStep 1215733 = 113975) (by norm_num)
theorem B855301 : Blo 758332 855301 := bbase (se 4 (by rfl) ⟨80184, by rfl⟩ : syracuseStep 855301 = 160369) (by norm_num)
theorem B855337 : Blo 758332 855337 := bbase (se 2 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 855337 = 641503) (by norm_num)
theorem B1281325 : Blo 758332 1281325 := bbase (se 3 (by rfl) ⟨240248, by rfl⟩ : syracuseStep 1281325 = 480497) (by norm_num)
theorem B1707317 : Blo 758332 1707317 := bbase (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) (by norm_num)
theorem B855373 : Blo 758332 855373 := bbase (se 3 (by rfl) ⟨160382, by rfl⟩ : syracuseStep 855373 = 320765) (by norm_num)
theorem B1445197 : Blo 758332 1445197 := bbase (se 3 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 1445197 = 541949) (by norm_num)
theorem B855409 : Blo 758332 855409 := bbase (se 2 (by rfl) ⟨320778, by rfl⟩ : syracuseStep 855409 = 641557) (by norm_num)
theorem B5475701 : Blo 758332 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B1707389 : Blo 758332 1707389 := bbase (se 3 (by rfl) ⟨320135, by rfl⟩ : syracuseStep 1707389 = 640271) (by norm_num)
theorem B1281413 : Blo 758332 1281413 := bbase (se 4 (by rfl) ⟨120132, by rfl⟩ : syracuseStep 1281413 = 240265) (by norm_num)
theorem B855445 : Blo 758332 855445 := bbase (se 6 (by rfl) ⟨20049, by rfl⟩ : syracuseStep 855445 = 40099) (by norm_num)
theorem B855481 : Blo 758332 855481 := bbase (se 2 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 855481 = 641611) (by norm_num)
theorem B1707461 : Blo 758332 1707461 := bbase (se 4 (by rfl) ⟨160074, by rfl⟩ : syracuseStep 1707461 = 320149) (by norm_num)
theorem B855517 : Blo 758332 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B1445357 : Blo 758332 1445357 := bbase (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) (by norm_num)
theorem B855553 : Blo 758332 855553 := bbase (se 2 (by rfl) ⟨320832, by rfl⟩ : syracuseStep 855553 = 641665) (by norm_num)
theorem B1281541 : Blo 758332 1281541 := bbase (se 4 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 1281541 = 240289) (by norm_num)
theorem B1707533 : Blo 758332 1707533 := bbase (se 3 (by rfl) ⟨320162, by rfl⟩ : syracuseStep 1707533 = 640325) (by norm_num)
theorem B855589 : Blo 758332 855589 := bbase (se 4 (by rfl) ⟨80211, by rfl⟩ : syracuseStep 855589 = 160423) (by norm_num)
theorem B855625 : Blo 758332 855625 := bbase (se 2 (by rfl) ⟨320859, by rfl⟩ : syracuseStep 855625 = 641719) (by norm_num)
theorem B1707605 : Blo 758332 1707605 := bbase (se 8 (by rfl) ⟨10005, by rfl⟩ : syracuseStep 1707605 = 20011) (by norm_num)
theorem B1281629 : Blo 758332 1281629 := bbase (se 3 (by rfl) ⟨240305, by rfl⟩ : syracuseStep 1281629 = 480611) (by norm_num)
theorem B1543781 : Blo 758332 1543781 := bbase (se 4 (by rfl) ⟨144729, by rfl⟩ : syracuseStep 1543781 = 289459) (by norm_num)
theorem B855661 : Blo 758332 855661 := bbase (se 3 (by rfl) ⟨160436, by rfl⟩ : syracuseStep 855661 = 320873) (by norm_num)
theorem B1445501 : Blo 758332 1445501 := bbase (se 3 (by rfl) ⟨271031, by rfl⟩ : syracuseStep 1445501 = 542063) (by norm_num)
theorem B855697 : Blo 758332 855697 := bbase (se 2 (by rfl) ⟨320886, by rfl⟩ : syracuseStep 855697 = 641773) (by norm_num)
theorem B6950549 : Blo 758332 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B1707677 : Blo 758332 1707677 := bbase (se 3 (by rfl) ⟨320189, by rfl⟩ : syracuseStep 1707677 = 640379) (by norm_num)
theorem B2559653 : Blo 758332 2559653 := bbase (se 4 (by rfl) ⟨239967, by rfl⟩ : syracuseStep 2559653 = 479935) (by norm_num)
theorem B1543853 : Blo 758332 1543853 := bbase (se 3 (by rfl) ⟨289472, by rfl⟩ : syracuseStep 1543853 = 578945) (by norm_num)
theorem B855733 : Blo 758332 855733 := bbase (se 5 (by rfl) ⟨40112, by rfl⟩ : syracuseStep 855733 = 80225) (by norm_num)
theorem B855769 : Blo 758332 855769 := bbase (se 2 (by rfl) ⟨320913, by rfl⟩ : syracuseStep 855769 = 641827) (by norm_num)
theorem B1281757 : Blo 758332 1281757 := bbase (se 3 (by rfl) ⟨240329, by rfl⟩ : syracuseStep 1281757 = 480659) (by norm_num)
theorem B1707749 : Blo 758332 1707749 := bbase (se 4 (by rfl) ⟨160101, by rfl⟩ : syracuseStep 1707749 = 320203) (by norm_num)
theorem B855805 : Blo 758332 855805 := bbase (se 3 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 855805 = 320927) (by norm_num)
theorem B855841 : Blo 758332 855841 := bbase (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) (by norm_num)
theorem B1707821 : Blo 758332 1707821 := bbase (se 3 (by rfl) ⟨320216, by rfl⟩ : syracuseStep 1707821 = 640433) (by norm_num)
theorem B1281845 : Blo 758332 1281845 := bbase (se 5 (by rfl) ⟨60086, by rfl⟩ : syracuseStep 1281845 = 120173) (by norm_num)
theorem B986941 : Blo 758332 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B855877 : Blo 758332 855877 := bbase (se 4 (by rfl) ⟨80238, by rfl⟩ : syracuseStep 855877 = 160477) (by norm_num)
theorem B855913 : Blo 758332 855913 := bbase (se 2 (by rfl) ⟨320967, by rfl⟩ : syracuseStep 855913 = 641935) (by norm_num)
theorem B1707893 : Blo 758332 1707893 := bbase (se 5 (by rfl) ⟨80057, by rfl⟩ : syracuseStep 1707893 = 160115) (by norm_num)
theorem B855949 : Blo 758332 855949 := bbase (se 3 (by rfl) ⟨160490, by rfl⟩ : syracuseStep 855949 = 320981) (by norm_num)
theorem B1445789 : Blo 758332 1445789 := bbase (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) (by norm_num)
theorem B855985 : Blo 758332 855985 := bbase (se 2 (by rfl) ⟨320994, by rfl⟩ : syracuseStep 855985 = 641989) (by norm_num)
theorem B1281973 : Blo 758332 1281973 := bbase (se 5 (by rfl) ⟨60092, by rfl⟩ : syracuseStep 1281973 = 120185) (by norm_num)
theorem B1707965 : Blo 758332 1707965 := bbase (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) (by norm_num)
theorem B2166725 : Blo 758332 2166725 := bbase (se 4 (by rfl) ⟨203130, by rfl⟩ : syracuseStep 2166725 = 406261) (by norm_num)
theorem B856021 : Blo 758332 856021 := bbase (se 7 (by rfl) ⟨10031, by rfl⟩ : syracuseStep 856021 = 20063) (by norm_num)
theorem B1085413 : Blo 758332 1085413 := bbase (se 4 (by rfl) ⟨101757, by rfl⟩ : syracuseStep 1085413 = 203515) (by norm_num)
theorem B856057 : Blo 758332 856057 := bbase (se 2 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 856057 = 642043) (by norm_num)
theorem B1708037 : Blo 758332 1708037 := bbase (se 4 (by rfl) ⟨160128, by rfl⟩ : syracuseStep 1708037 = 320257) (by norm_num)
theorem B1282061 : Blo 758332 1282061 := bbase (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) (by norm_num)
theorem B856093 : Blo 758332 856093 := bbase (se 3 (by rfl) ⟨160517, by rfl⟩ : syracuseStep 856093 = 321035) (by norm_num)
theorem B1445941 : Blo 758332 1445941 := bbase (se 5 (by rfl) ⟨67778, by rfl⟩ : syracuseStep 1445941 = 135557) (by norm_num)
theorem B856129 : Blo 758332 856129 := bbase (se 2 (by rfl) ⟨321048, by rfl⟩ : syracuseStep 856129 = 642097) (by norm_num)
theorem B1708109 : Blo 758332 1708109 := bbase (se 3 (by rfl) ⟨320270, by rfl⟩ : syracuseStep 1708109 = 640541) (by norm_num)
theorem B2560085 : Blo 758332 2560085 := bbase (se 8 (by rfl) ⟨15000, by rfl⟩ : syracuseStep 2560085 = 30001) (by norm_num)
theorem B856165 : Blo 758332 856165 := bbase (se 4 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 856165 = 160531) (by norm_num)
theorem B856201 : Blo 758332 856201 := bbase (se 2 (by rfl) ⟨321075, by rfl⟩ : syracuseStep 856201 = 642151) (by norm_num)
theorem B1282189 : Blo 758332 1282189 := bbase (se 3 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 1282189 = 480821) (by norm_num)
theorem B1708181 : Blo 758332 1708181 := bbase (se 6 (by rfl) ⟨40035, by rfl⟩ : syracuseStep 1708181 = 80071) (by norm_num)
theorem B856237 : Blo 758332 856237 := bbase (se 3 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 856237 = 321089) (by norm_num)
theorem B856273 : Blo 758332 856273 := bbase (se 2 (by rfl) ⟨321102, by rfl⟩ : syracuseStep 856273 = 642205) (by norm_num)
theorem B1708253 : Blo 758332 1708253 := bbase (se 3 (by rfl) ⟨320297, by rfl⟩ : syracuseStep 1708253 = 640595) (by norm_num)
theorem B1282277 : Blo 758332 1282277 := bbase (se 4 (by rfl) ⟨120213, by rfl⟩ : syracuseStep 1282277 = 240427) (by norm_num)
theorem B856309 : Blo 758332 856309 := bbase (se 5 (by rfl) ⟨40139, by rfl⟩ : syracuseStep 856309 = 80279) (by norm_num)
theorem B856345 : Blo 758332 856345 := bbase (se 2 (by rfl) ⟨321129, by rfl⟩ : syracuseStep 856345 = 642259) (by norm_num)
theorem B1708325 : Blo 758332 1708325 := bbase (se 4 (by rfl) ⟨160155, by rfl⟩ : syracuseStep 1708325 = 320311) (by norm_num)
theorem B856381 : Blo 758332 856381 := bbase (se 3 (by rfl) ⟨160571, by rfl⟩ : syracuseStep 856381 = 321143) (by norm_num)
theorem B19796309 : Blo 758332 19796309 := bbase (se 10 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 19796309 = 57997) (by norm_num)
theorem B856417 : Blo 758332 856417 := bbase (se 2 (by rfl) ⟨321156, by rfl⟩ : syracuseStep 856417 = 642313) (by norm_num)
theorem B1282405 : Blo 758332 1282405 := bbase (se 4 (by rfl) ⟨120225, by rfl⟩ : syracuseStep 1282405 = 240451) (by norm_num)
theorem B1446245 : Blo 758332 1446245 := bbase (se 4 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 1446245 = 271171) (by norm_num)
theorem B1708397 : Blo 758332 1708397 := bbase (se 3 (by rfl) ⟨320324, by rfl⟩ : syracuseStep 1708397 = 640649) (by norm_num)
theorem B856453 : Blo 758332 856453 := bbase (se 4 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 856453 = 160585) (by norm_num)
theorem B856489 : Blo 758332 856489 := bbase (se 2 (by rfl) ⟨321183, by rfl⟩ : syracuseStep 856489 = 642367) (by norm_num)
theorem B1708469 : Blo 758332 1708469 := bbase (se 5 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 1708469 = 160169) (by norm_num)
theorem B1282493 : Blo 758332 1282493 := bbase (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) (by norm_num)
theorem B856525 : Blo 758332 856525 := bbase (se 3 (by rfl) ⟨160598, by rfl⟩ : syracuseStep 856525 = 321197) (by norm_num)
theorem B856561 : Blo 758332 856561 := bbase (se 2 (by rfl) ⟨321210, by rfl⟩ : syracuseStep 856561 = 642421) (by norm_num)
theorem B1708541 : Blo 758332 1708541 := bbase (se 3 (by rfl) ⟨320351, by rfl⟩ : syracuseStep 1708541 = 640703) (by norm_num)
theorem B2560517 : Blo 758332 2560517 := bbase (se 4 (by rfl) ⟨240048, by rfl⟩ : syracuseStep 2560517 = 480097) (by norm_num)
theorem B856597 : Blo 758332 856597 := bbase (se 6 (by rfl) ⟨20076, by rfl⟩ : syracuseStep 856597 = 40153) (by norm_num)
theorem B856633 : Blo 758332 856633 := bbase (se 2 (by rfl) ⟨321237, by rfl⟩ : syracuseStep 856633 = 642475) (by norm_num)
theorem B1282621 : Blo 758332 1282621 := bbase (se 3 (by rfl) ⟨240491, by rfl⟩ : syracuseStep 1282621 = 480983) (by norm_num)
theorem B1708613 : Blo 758332 1708613 := bbase (se 4 (by rfl) ⟨160182, by rfl⟩ : syracuseStep 1708613 = 320365) (by norm_num)
theorem B1217117 : Blo 758332 1217117 := bbase (se 3 (by rfl) ⟨228209, by rfl⟩ : syracuseStep 1217117 = 456419) (by norm_num)
theorem B856669 : Blo 758332 856669 := bbase (se 3 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 856669 = 321251) (by norm_num)
theorem B856705 : Blo 758332 856705 := bbase (se 2 (by rfl) ⟨321264, by rfl⟩ : syracuseStep 856705 = 642529) (by norm_num)
theorem B1708685 : Blo 758332 1708685 := bbase (se 3 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 1708685 = 640757) (by norm_num)
theorem B1282709 : Blo 758332 1282709 := bbase (se 6 (by rfl) ⟨30063, by rfl⟩ : syracuseStep 1282709 = 60127) (by norm_num)
theorem B856741 : Blo 758332 856741 := bbase (se 4 (by rfl) ⟨80319, by rfl⟩ : syracuseStep 856741 = 160639) (by norm_num)
theorem B856777 : Blo 758332 856777 := bbase (se 2 (by rfl) ⟨321291, by rfl⟩ : syracuseStep 856777 = 642583) (by norm_num)
theorem B1708757 : Blo 758332 1708757 := bbase (se 7 (by rfl) ⟨20024, by rfl⟩ : syracuseStep 1708757 = 40049) (by norm_num)
theorem B2888405 : Blo 758332 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B856813 : Blo 758332 856813 := bbase (se 3 (by rfl) ⟨160652, by rfl⟩ : syracuseStep 856813 = 321305) (by norm_num)
theorem B856849 : Blo 758332 856849 := bbase (se 2 (by rfl) ⟨321318, by rfl⟩ : syracuseStep 856849 = 642637) (by norm_num)
theorem B1282837 : Blo 758332 1282837 := bbase (se 6 (by rfl) ⟨30066, by rfl⟩ : syracuseStep 1282837 = 60133) (by norm_num)
theorem B1708829 : Blo 758332 1708829 := bbase (se 3 (by rfl) ⟨320405, by rfl⟩ : syracuseStep 1708829 = 640811) (by norm_num)
theorem B856885 : Blo 758332 856885 := bbase (se 5 (by rfl) ⟨40166, by rfl⟩ : syracuseStep 856885 = 80333) (by norm_num)
theorem B1545013 : Blo 758332 1545013 := bbase (se 5 (by rfl) ⟨72422, by rfl⟩ : syracuseStep 1545013 = 144845) (by norm_num)
theorem B856921 : Blo 758332 856921 := bbase (se 2 (by rfl) ⟨321345, by rfl⟩ : syracuseStep 856921 = 642691) (by norm_num)
theorem B1708901 : Blo 758332 1708901 := bbase (se 4 (by rfl) ⟨160209, by rfl⟩ : syracuseStep 1708901 = 320419) (by norm_num)
theorem B1282925 : Blo 758332 1282925 := bbase (se 3 (by rfl) ⟨240548, by rfl⟩ : syracuseStep 1282925 = 481097) (by norm_num)
theorem B856957 : Blo 758332 856957 := bbase (se 3 (by rfl) ⟨160679, by rfl⟩ : syracuseStep 856957 = 321359) (by norm_num)
theorem B856993 : Blo 758332 856993 := bbase (se 2 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 856993 = 642745) (by norm_num)
theorem B1708973 : Blo 758332 1708973 := bbase (se 3 (by rfl) ⟨320432, by rfl⟩ : syracuseStep 1708973 = 640865) (by norm_num)
theorem B2560949 : Blo 758332 2560949 := bbase (se 5 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 2560949 = 240089) (by norm_num)
theorem B4330421 : Blo 758332 4330421 := bbase (se 5 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 4330421 = 405977) (by norm_num)
theorem B857029 : Blo 758332 857029 := bbase (se 4 (by rfl) ⟨80346, by rfl⟩ : syracuseStep 857029 = 160693) (by norm_num)
theorem B857065 : Blo 758332 857065 := bbase (se 2 (by rfl) ⟨321399, by rfl⟩ : syracuseStep 857065 = 642799) (by norm_num)
theorem B1283053 : Blo 758332 1283053 := bbase (se 3 (by rfl) ⟨240572, by rfl⟩ : syracuseStep 1283053 = 481145) (by norm_num)
theorem B1709045 : Blo 758332 1709045 := bbase (se 5 (by rfl) ⟨80111, by rfl⟩ : syracuseStep 1709045 = 160223) (by norm_num)
theorem B2888693 : Blo 758332 2888693 := bbase (se 5 (by rfl) ⟨135407, by rfl⟩ : syracuseStep 2888693 = 270815) (by norm_num)
theorem B857101 : Blo 758332 857101 := bbase (se 3 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 857101 = 321413) (by norm_num)
theorem B857137 : Blo 758332 857137 := bbase (se 2 (by rfl) ⟨321426, by rfl⟩ : syracuseStep 857137 = 642853) (by norm_num)
theorem B1709117 : Blo 758332 1709117 := bbase (se 3 (by rfl) ⟨320459, by rfl⟩ : syracuseStep 1709117 = 640919) (by norm_num)
theorem B1283141 : Blo 758332 1283141 := bbase (se 4 (by rfl) ⟨120294, by rfl⟩ : syracuseStep 1283141 = 240589) (by norm_num)
theorem B857173 : Blo 758332 857173 := bbase (se 8 (by rfl) ⟨5022, by rfl⟩ : syracuseStep 857173 = 10045) (by norm_num)
theorem B1446997 : Blo 758332 1446997 := bbase (se 8 (by rfl) ⟨8478, by rfl⟩ : syracuseStep 1446997 = 16957) (by norm_num)
theorem B857209 : Blo 758332 857209 := bbase (se 2 (by rfl) ⟨321453, by rfl⟩ : syracuseStep 857209 = 642907) (by norm_num)
theorem B1709189 : Blo 758332 1709189 := bbase (se 4 (by rfl) ⟨160236, by rfl⟩ : syracuseStep 1709189 = 320473) (by norm_num)
theorem B857245 : Blo 758332 857245 := bbase (se 3 (by rfl) ⟨160733, by rfl⟩ : syracuseStep 857245 = 321467) (by norm_num)
theorem B857281 : Blo 758332 857281 := bbase (se 2 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 857281 = 642961) (by norm_num)
theorem B1283269 : Blo 758332 1283269 := bbase (se 4 (by rfl) ⟨120306, by rfl⟩ : syracuseStep 1283269 = 240613) (by norm_num)
theorem B1709261 : Blo 758332 1709261 := bbase (se 3 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 1709261 = 640973) (by norm_num)
theorem B857317 : Blo 758332 857317 := bbase (se 4 (by rfl) ⟨80373, by rfl⟩ : syracuseStep 857317 = 160747) (by norm_num)
theorem B1447141 : Blo 758332 1447141 := bbase (se 4 (by rfl) ⟨135669, by rfl⟩ : syracuseStep 1447141 = 271339) (by norm_num)
theorem B3839237 : Blo 758332 3839237 := bbase (se 4 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 3839237 = 719857) (by norm_num)
theorem B857353 : Blo 758332 857353 := bbase (se 2 (by rfl) ⟨321507, by rfl⟩ : syracuseStep 857353 = 643015) (by norm_num)
theorem B1709333 : Blo 758332 1709333 := bbase (se 6 (by rfl) ⟨40062, by rfl⟩ : syracuseStep 1709333 = 80125) (by norm_num)
theorem B1283357 : Blo 758332 1283357 := bbase (se 3 (by rfl) ⟨240629, by rfl⟩ : syracuseStep 1283357 = 481259) (by norm_num)
theorem B857389 : Blo 758332 857389 := bbase (se 3 (by rfl) ⟨160760, by rfl⟩ : syracuseStep 857389 = 321521) (by norm_num)
theorem B857425 : Blo 758332 857425 := bbase (se 2 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 857425 = 643069) (by norm_num)
theorem B1709405 : Blo 758332 1709405 := bbase (se 3 (by rfl) ⟨320513, by rfl⟩ : syracuseStep 1709405 = 641027) (by norm_num)
theorem B2561381 : Blo 758332 2561381 := bbase (se 4 (by rfl) ⟨240129, by rfl⟩ : syracuseStep 2561381 = 480259) (by norm_num)
theorem B857461 : Blo 758332 857461 := bbase (se 5 (by rfl) ⟨40193, by rfl⟩ : syracuseStep 857461 = 80387) (by norm_num)
theorem B857497 : Blo 758332 857497 := bbase (se 2 (by rfl) ⟨321561, by rfl⟩ : syracuseStep 857497 = 643123) (by norm_num)
theorem B1283485 : Blo 758332 1283485 := bbase (se 3 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 1283485 = 481307) (by norm_num)
theorem B1709477 : Blo 758332 1709477 := bbase (se 4 (by rfl) ⟨160263, by rfl⟩ : syracuseStep 1709477 = 320527) (by norm_num)
theorem B857533 : Blo 758332 857533 := bbase (se 3 (by rfl) ⟨160787, by rfl⟩ : syracuseStep 857533 = 321575) (by norm_num)
theorem B857569 : Blo 758332 857569 := bbase (se 2 (by rfl) ⟨321588, by rfl⟩ : syracuseStep 857569 = 643177) (by norm_num)
theorem B1709549 : Blo 758332 1709549 := bbase (se 3 (by rfl) ⟨320540, by rfl⟩ : syracuseStep 1709549 = 641081) (by norm_num)
theorem B1283573 : Blo 758332 1283573 := bbase (se 5 (by rfl) ⟨60167, by rfl⟩ : syracuseStep 1283573 = 120335) (by norm_num)
theorem B2168309 : Blo 758332 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B1218053 : Blo 758332 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B857605 : Blo 758332 857605 := bbase (se 4 (by rfl) ⟨80400, by rfl⟩ : syracuseStep 857605 = 160801) (by norm_num)
theorem B1709621 : Blo 758332 1709621 := bbase (se 5 (by rfl) ⟨80138, by rfl⟩ : syracuseStep 1709621 = 160277) (by norm_num)
theorem B1283701 : Blo 758332 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B1709693 : Blo 758332 1709693 := bbase (se 3 (by rfl) ⟨320567, by rfl⟩ : syracuseStep 1709693 = 641135) (by norm_num)
theorem B1709765 : Blo 758332 1709765 := bbase (se 4 (by rfl) ⟨160290, by rfl⟩ : syracuseStep 1709765 = 320581) (by norm_num)
theorem B1283789 : Blo 758332 1283789 := bbase (se 3 (by rfl) ⟨240710, by rfl⟩ : syracuseStep 1283789 = 481421) (by norm_num)
theorem B1709837 : Blo 758332 1709837 := bbase (se 3 (by rfl) ⟨320594, by rfl⟩ : syracuseStep 1709837 = 641189) (by norm_num)
theorem B2561813 : Blo 758332 2561813 := bbase (se 6 (by rfl) ⟨60042, by rfl⟩ : syracuseStep 2561813 = 120085) (by norm_num)
theorem B1283917 : Blo 758332 1283917 := bbase (se 3 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 1283917 = 481469) (by norm_num)
theorem B1709909 : Blo 758332 1709909 := bbase (se 9 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 1709909 = 10019) (by norm_num)
theorem B7313237 : Blo 758332 7313237 := bbase (se 9 (by rfl) ⟨21425, by rfl⟩ : syracuseStep 7313237 = 42851) (by norm_num)
theorem B2463605 : Blo 758332 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B1709981 : Blo 758332 1709981 := bbase (se 3 (by rfl) ⟨320621, by rfl⟩ : syracuseStep 1709981 = 641243) (by norm_num)
theorem B1284005 : Blo 758332 1284005 := bbase (se 4 (by rfl) ⟨120375, by rfl⟩ : syracuseStep 1284005 = 240751) (by norm_num)
theorem B1710053 : Blo 758332 1710053 := bbase (se 4 (by rfl) ⟨160317, by rfl⟩ : syracuseStep 1710053 = 320635) (by norm_num)
theorem B1284133 : Blo 758332 1284133 := bbase (se 4 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 1284133 = 240775) (by norm_num)
theorem B1710125 : Blo 758332 1710125 := bbase (se 3 (by rfl) ⟨320648, by rfl⟩ : syracuseStep 1710125 = 641297) (by norm_num)
theorem B3250277 : Blo 758332 3250277 := bbase (se 4 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 3250277 = 609427) (by norm_num)
theorem B1710197 : Blo 758332 1710197 := bbase (se 5 (by rfl) ⟨80165, by rfl⟩ : syracuseStep 1710197 = 160331) (by norm_num)
theorem B1284221 : Blo 758332 1284221 := bbase (se 3 (by rfl) ⟨240791, by rfl⟩ : syracuseStep 1284221 = 481583) (by norm_num)
theorem B1218701 : Blo 758332 1218701 := bbase (se 3 (by rfl) ⟨228506, by rfl⟩ : syracuseStep 1218701 = 457013) (by norm_num)
theorem B2889877 : Blo 758332 2889877 := bbase (se 6 (by rfl) ⟨67731, by rfl⟩ : syracuseStep 2889877 = 135463) (by norm_num)
theorem B2168981 : Blo 758332 2168981 := bbase (se 6 (by rfl) ⟨50835, by rfl⟩ : syracuseStep 2168981 = 101671) (by norm_num)
theorem B4102325 : Blo 758332 4102325 := bbase (se 5 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 4102325 = 384593) (by norm_num)
theorem B1710269 : Blo 758332 1710269 := bbase (se 3 (by rfl) ⟨320675, by rfl⟩ : syracuseStep 1710269 = 641351) (by norm_num)
theorem B2562245 : Blo 758332 2562245 := bbase (se 4 (by rfl) ⟨240210, by rfl⟩ : syracuseStep 2562245 = 480421) (by norm_num)
theorem B1284349 : Blo 758332 1284349 := bbase (se 3 (by rfl) ⟨240815, by rfl⟩ : syracuseStep 1284349 = 481631) (by norm_num)
theorem B1710341 : Blo 758332 1710341 := bbase (se 4 (by rfl) ⟨160344, by rfl⟩ : syracuseStep 1710341 = 320689) (by norm_num)
theorem B1710413 : Blo 758332 1710413 := bbase (se 3 (by rfl) ⟨320702, by rfl⟩ : syracuseStep 1710413 = 641405) (by norm_num)
theorem B1284437 : Blo 758332 1284437 := bbase (se 10 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 1284437 = 3763) (by norm_num)
theorem B1710485 : Blo 758332 1710485 := bbase (se 6 (by rfl) ⟨40089, by rfl⟩ : syracuseStep 1710485 = 80179) (by norm_num)
theorem B2890181 : Blo 758332 2890181 := bbase (se 4 (by rfl) ⟨270954, by rfl⟩ : syracuseStep 2890181 = 541909) (by norm_num)
theorem B1284565 : Blo 758332 1284565 := bbase (se 7 (by rfl) ⟨15053, by rfl⟩ : syracuseStep 1284565 = 30107) (by norm_num)
theorem B1710557 : Blo 758332 1710557 := bbase (se 3 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 1710557 = 641459) (by norm_num)
theorem B3840533 : Blo 758332 3840533 := bbase (se 6 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 3840533 = 180025) (by norm_num)
theorem B1710629 : Blo 758332 1710629 := bbase (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) (by norm_num)
theorem B1284653 : Blo 758332 1284653 := bbase (se 3 (by rfl) ⟨240872, by rfl⟩ : syracuseStep 1284653 = 481745) (by norm_num)
theorem B2169413 : Blo 758332 2169413 := bbase (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) (by norm_num)
theorem B2464357 : Blo 758332 2464357 := bbase (se 4 (by rfl) ⟨231033, by rfl⟩ : syracuseStep 2464357 = 462067) (by norm_num)
theorem B1710701 : Blo 758332 1710701 := bbase (se 3 (by rfl) ⟨320756, by rfl⟩ : syracuseStep 1710701 = 641513) (by norm_num)
theorem B2562677 : Blo 758332 2562677 := bbase (se 5 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 2562677 = 240251) (by norm_num)
theorem B1284781 : Blo 758332 1284781 := bbase (se 3 (by rfl) ⟨240896, by rfl⟩ : syracuseStep 1284781 = 481793) (by norm_num)
theorem B1710773 : Blo 758332 1710773 := bbase (se 5 (by rfl) ⟨80192, by rfl⟩ : syracuseStep 1710773 = 160385) (by norm_num)
theorem B1710845 : Blo 758332 1710845 := bbase (se 3 (by rfl) ⟨320783, by rfl⟩ : syracuseStep 1710845 = 641567) (by norm_num)
theorem B1284869 : Blo 758332 1284869 := bbase (se 4 (by rfl) ⟨120456, by rfl⟩ : syracuseStep 1284869 = 240913) (by norm_num)
theorem B1710917 : Blo 758332 1710917 := bbase (se 4 (by rfl) ⟨160398, by rfl⟩ : syracuseStep 1710917 = 320797) (by norm_num)
theorem B5774165 : Blo 758332 5774165 := bbase (se 9 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 5774165 = 33833) (by norm_num)
theorem B3644261 : Blo 758332 3644261 := bbase (se 4 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 3644261 = 683299) (by norm_num)
theorem B1284997 : Blo 758332 1284997 := bbase (se 4 (by rfl) ⟨120468, by rfl⟩ : syracuseStep 1284997 = 240937) (by norm_num)
theorem B1710989 : Blo 758332 1710989 := bbase (se 3 (by rfl) ⟨320810, by rfl⟩ : syracuseStep 1710989 = 641621) (by norm_num)
theorem B1711061 : Blo 758332 1711061 := bbase (se 7 (by rfl) ⟨20051, by rfl⟩ : syracuseStep 1711061 = 40103) (by norm_num)
theorem B1285085 : Blo 758332 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B1711133 : Blo 758332 1711133 := bbase (se 3 (by rfl) ⟨320837, by rfl⟩ : syracuseStep 1711133 = 641675) (by norm_num)
theorem B2563109 : Blo 758332 2563109 := bbase (se 4 (by rfl) ⟨240291, by rfl⟩ : syracuseStep 2563109 = 480583) (by norm_num)
theorem B3251285 : Blo 758332 3251285 := bbase (se 8 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 3251285 = 38101) (by norm_num)
theorem B4332629 : Blo 758332 4332629 := bbase (se 8 (by rfl) ⟨25386, by rfl⟩ : syracuseStep 4332629 = 50773) (by norm_num)
theorem B1285213 : Blo 758332 1285213 := bbase (se 3 (by rfl) ⟨240977, by rfl⟩ : syracuseStep 1285213 = 481955) (by norm_num)
theorem B1711205 : Blo 758332 1711205 := bbase (se 4 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 1711205 = 320851) (by norm_num)
theorem B1219693 : Blo 758332 1219693 := bbase (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) (by norm_num)
theorem B1711277 : Blo 758332 1711277 := bbase (se 3 (by rfl) ⟨320864, by rfl⟩ : syracuseStep 1711277 = 641729) (by norm_num)
theorem B1875125 : Blo 758332 1875125 := bbase (se 5 (by rfl) ⟨87896, by rfl⟩ : syracuseStep 1875125 = 175793) (by norm_num)
theorem B1285301 : Blo 758332 1285301 := bbase (se 5 (by rfl) ⟨60248, by rfl⟩ : syracuseStep 1285301 = 120497) (by norm_num)
theorem B1711349 : Blo 758332 1711349 := bbase (se 5 (by rfl) ⟨80219, by rfl⟩ : syracuseStep 1711349 = 160439) (by norm_num)
theorem B1285429 : Blo 758332 1285429 := bbase (se 5 (by rfl) ⟨60254, by rfl⟩ : syracuseStep 1285429 = 120509) (by norm_num)
theorem B2170165 : Blo 758332 2170165 := bbase (se 5 (by rfl) ⟨101726, by rfl⟩ : syracuseStep 2170165 = 203453) (by norm_num)
theorem B1711421 : Blo 758332 1711421 := bbase (se 3 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 1711421 = 641783) (by norm_num)
theorem B2432389 : Blo 758332 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B1711493 : Blo 758332 1711493 := bbase (se 4 (by rfl) ⟨160452, by rfl⟩ : syracuseStep 1711493 = 320905) (by norm_num)
theorem B1285517 : Blo 758332 1285517 := bbase (se 3 (by rfl) ⟨241034, by rfl⟩ : syracuseStep 1285517 = 482069) (by norm_num)
theorem B1711565 : Blo 758332 1711565 := bbase (se 3 (by rfl) ⟨320918, by rfl⟩ : syracuseStep 1711565 = 641837) (by norm_num)
theorem B2563541 : Blo 758332 2563541 := bbase (se 7 (by rfl) ⟨30041, by rfl⟩ : syracuseStep 2563541 = 60083) (by norm_num)
theorem B3907061 : Blo 758332 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B1154557 : Blo 758332 1154557 := bbase (se 3 (by rfl) ⟨216479, by rfl⟩ : syracuseStep 1154557 = 432959) (by norm_num)
theorem B1285645 : Blo 758332 1285645 := bbase (se 3 (by rfl) ⟨241058, by rfl⟩ : syracuseStep 1285645 = 482117) (by norm_num)
theorem B1711637 : Blo 758332 1711637 := bbase (se 6 (by rfl) ⟨40116, by rfl⟩ : syracuseStep 1711637 = 80233) (by norm_num)
theorem B1220141 : Blo 758332 1220141 := bbase (se 3 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 1220141 = 457553) (by norm_num)
theorem B4628053 : Blo 758332 4628053 := bbase (se 8 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 4628053 = 54235) (by norm_num)
theorem B1711709 : Blo 758332 1711709 := bbase (se 3 (by rfl) ⟨320945, by rfl⟩ : syracuseStep 1711709 = 641891) (by norm_num)
theorem B1285733 : Blo 758332 1285733 := bbase (se 4 (by rfl) ⟨120537, by rfl⟩ : syracuseStep 1285733 = 241075) (by norm_num)
theorem B8756885 : Blo 758332 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B1711781 : Blo 758332 1711781 := bbase (se 4 (by rfl) ⟨160479, by rfl⟩ : syracuseStep 1711781 = 320959) (by norm_num)
theorem B1285861 : Blo 758332 1285861 := bbase (se 4 (by rfl) ⟨120549, by rfl⟩ : syracuseStep 1285861 = 241099) (by norm_num)
theorem B1711853 : Blo 758332 1711853 := bbase (se 3 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 1711853 = 641945) (by norm_num)
theorem B1220341 : Blo 758332 1220341 := bbase (se 5 (by rfl) ⟨57203, by rfl⟩ : syracuseStep 1220341 = 114407) (by norm_num)
theorem B1154837 : Blo 758332 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B3841829 : Blo 758332 3841829 := bbase (se 4 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 3841829 = 720343) (by norm_num)
theorem B1711925 : Blo 758332 1711925 := bbase (se 5 (by rfl) ⟨80246, by rfl⟩ : syracuseStep 1711925 = 160493) (by norm_num)
theorem B1285949 : Blo 758332 1285949 := bbase (se 3 (by rfl) ⟨241115, by rfl⟩ : syracuseStep 1285949 = 482231) (by norm_num)
theorem B1711997 : Blo 758332 1711997 := bbase (se 3 (by rfl) ⟨320999, by rfl⟩ : syracuseStep 1711997 = 641999) (by norm_num)
theorem B2563973 : Blo 758332 2563973 := bbase (se 4 (by rfl) ⟨240372, by rfl⟩ : syracuseStep 2563973 = 480745) (by norm_num)
theorem B1286077 : Blo 758332 1286077 := bbase (se 3 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 1286077 = 482279) (by norm_num)
theorem B1712069 : Blo 758332 1712069 := bbase (se 4 (by rfl) ⟨160506, by rfl⟩ : syracuseStep 1712069 = 321013) (by norm_num)
theorem B1646557 : Blo 758332 1646557 := bbase (se 3 (by rfl) ⟨308729, by rfl⟩ : syracuseStep 1646557 = 617459) (by norm_num)
theorem B1220597 : Blo 758332 1220597 := bbase (se 5 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 1220597 = 114431) (by norm_num)
theorem B1712141 : Blo 758332 1712141 := bbase (se 3 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 1712141 = 642053) (by norm_num)
theorem B1286165 : Blo 758332 1286165 := bbase (se 6 (by rfl) ⟨30144, by rfl⟩ : syracuseStep 1286165 = 60289) (by norm_num)
theorem B1712213 : Blo 758332 1712213 := bbase (se 8 (by rfl) ⟨10032, by rfl⟩ : syracuseStep 1712213 = 20065) (by norm_num)
theorem B1286293 : Blo 758332 1286293 := bbase (se 6 (by rfl) ⟨30147, by rfl⟩ : syracuseStep 1286293 = 60295) (by norm_num)
theorem B1712285 : Blo 758332 1712285 := bbase (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) (by norm_num)
theorem B1712357 : Blo 758332 1712357 := bbase (se 4 (by rfl) ⟨160533, by rfl⟩ : syracuseStep 1712357 = 321067) (by norm_num)
theorem B1286381 : Blo 758332 1286381 := bbase (se 3 (by rfl) ⟨241196, by rfl⟩ : syracuseStep 1286381 = 482393) (by norm_num)
theorem B1712429 : Blo 758332 1712429 := bbase (se 3 (by rfl) ⟨321080, by rfl⟩ : syracuseStep 1712429 = 642161) (by norm_num)
theorem B2564405 : Blo 758332 2564405 := bbase (se 5 (by rfl) ⟨120206, by rfl⟩ : syracuseStep 2564405 = 240413) (by norm_num)
theorem B1155421 : Blo 758332 1155421 := bbase (se 3 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 1155421 = 433283) (by norm_num)
theorem B1712501 : Blo 758332 1712501 := bbase (se 5 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 1712501 = 160547) (by norm_num)
theorem B1712573 : Blo 758332 1712573 := bbase (se 3 (by rfl) ⟨321107, by rfl⟩ : syracuseStep 1712573 = 642215) (by norm_num)
theorem B6496757 : Blo 758332 6496757 := bbase (se 5 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 6496757 = 609071) (by norm_num)
theorem B1712645 : Blo 758332 1712645 := bbase (se 4 (by rfl) ⟨160560, by rfl⟩ : syracuseStep 1712645 = 321121) (by norm_num)
theorem B2892293 : Blo 758332 2892293 := bbase (se 4 (by rfl) ⟨271152, by rfl⟩ : syracuseStep 2892293 = 542305) (by norm_num)
theorem B6595093 : Blo 758332 6595093 := bbase (se 6 (by rfl) ⟨154572, by rfl⟩ : syracuseStep 6595093 = 309145) (by norm_num)
theorem B1712717 : Blo 758332 1712717 := bbase (se 3 (by rfl) ⟨321134, by rfl⟩ : syracuseStep 1712717 = 642269) (by norm_num)
theorem B1712789 : Blo 758332 1712789 := bbase (se 6 (by rfl) ⟨40143, by rfl⟩ : syracuseStep 1712789 = 80287) (by norm_num)
theorem B5415605 : Blo 758332 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B1712861 : Blo 758332 1712861 := bbase (se 3 (by rfl) ⟨321161, by rfl⟩ : syracuseStep 1712861 = 642323) (by norm_num)
theorem B2564837 : Blo 758332 2564837 := bbase (se 4 (by rfl) ⟨240453, by rfl⟩ : syracuseStep 2564837 = 480907) (by norm_num)
theorem B1712933 : Blo 758332 1712933 := bbase (se 4 (by rfl) ⟨160587, by rfl⟩ : syracuseStep 1712933 = 321175) (by norm_num)
theorem B2892581 : Blo 758332 2892581 := bbase (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) (by norm_num)
theorem B3253061 : Blo 758332 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B1713005 : Blo 758332 1713005 := bbase (se 3 (by rfl) ⟨321188, by rfl⟩ : syracuseStep 1713005 = 642377) (by norm_num)
theorem B1713077 : Blo 758332 1713077 := bbase (se 5 (by rfl) ⟨80300, by rfl⟩ : syracuseStep 1713077 = 160601) (by norm_num)
theorem B1713149 : Blo 758332 1713149 := bbase (se 3 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 1713149 = 642431) (by norm_num)
theorem B3843125 : Blo 758332 3843125 := bbase (se 5 (by rfl) ⟨180146, by rfl⟩ : syracuseStep 3843125 = 360293) (by norm_num)
theorem B1713221 : Blo 758332 1713221 := bbase (se 4 (by rfl) ⟨160614, by rfl⟩ : syracuseStep 1713221 = 321229) (by norm_num)
theorem B1713293 : Blo 758332 1713293 := bbase (se 3 (by rfl) ⟨321242, by rfl⟩ : syracuseStep 1713293 = 642485) (by norm_num)
theorem B2565269 : Blo 758332 2565269 := bbase (se 6 (by rfl) ⟨60123, by rfl⟩ : syracuseStep 2565269 = 120247) (by norm_num)
theorem B1713365 : Blo 758332 1713365 := bbase (se 7 (by rfl) ⟨20078, by rfl⟩ : syracuseStep 1713365 = 40157) (by norm_num)
theorem B4695317 : Blo 758332 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B1713437 : Blo 758332 1713437 := bbase (se 3 (by rfl) ⟨321269, by rfl⟩ : syracuseStep 1713437 = 642539) (by norm_num)
theorem B959789 : Blo 758332 959789 := bbase (se 3 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 959789 = 359921) (by norm_num)
theorem B959845 : Blo 758332 959845 := bbase (se 4 (by rfl) ⟨89985, by rfl⟩ : syracuseStep 959845 = 179971) (by norm_num)
theorem B1713509 : Blo 758332 1713509 := bbase (se 4 (by rfl) ⟨160641, by rfl⟩ : syracuseStep 1713509 = 321283) (by norm_num)
theorem B6235541 : Blo 758332 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B1713581 : Blo 758332 1713581 := bbase (se 3 (by rfl) ⟨321296, by rfl⟩ : syracuseStep 1713581 = 642593) (by norm_num)
theorem B959941 : Blo 758332 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B1156589 : Blo 758332 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B1713653 : Blo 758332 1713653 := bbase (se 5 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 1713653 = 160655) (by norm_num)
theorem B3712549 : Blo 758332 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B1713725 : Blo 758332 1713725 := bbase (se 3 (by rfl) ⟨321323, by rfl⟩ : syracuseStep 1713725 = 642647) (by norm_num)
theorem B3647045 : Blo 758332 3647045 := bbase (se 4 (by rfl) ⟨341910, by rfl⟩ : syracuseStep 3647045 = 683821) (by norm_num)
theorem B2565701 : Blo 758332 2565701 := bbase (se 4 (by rfl) ⟨240534, by rfl⟩ : syracuseStep 2565701 = 481069) (by norm_num)
theorem B960113 : Blo 758332 960113 := bbase (se 2 (by rfl) ⟨360042, by rfl⟩ : syracuseStep 960113 = 720085) (by norm_num)
theorem B1713797 : Blo 758332 1713797 := bbase (se 4 (by rfl) ⟨160668, by rfl⟩ : syracuseStep 1713797 = 321337) (by norm_num)
theorem B960169 : Blo 758332 960169 := bbase (se 2 (by rfl) ⟨360063, by rfl⟩ : syracuseStep 960169 = 720127) (by norm_num)
theorem B1713869 : Blo 758332 1713869 := bbase (se 3 (by rfl) ⟨321350, by rfl⟩ : syracuseStep 1713869 = 642701) (by norm_num)
theorem B960265 : Blo 758332 960265 := bbase (se 2 (by rfl) ⟨360099, by rfl⟩ : syracuseStep 960265 = 720199) (by norm_num)
theorem B1713941 : Blo 758332 1713941 := bbase (se 6 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 1713941 = 80341) (by norm_num)
theorem B1714013 : Blo 758332 1714013 := bbase (se 3 (by rfl) ⟨321377, by rfl⟩ : syracuseStep 1714013 = 642755) (by norm_num)
theorem B1714085 : Blo 758332 1714085 := bbase (se 4 (by rfl) ⟨160695, by rfl⟩ : syracuseStep 1714085 = 321391) (by norm_num)
theorem B960437 : Blo 758332 960437 := bbase (se 5 (by rfl) ⟨45020, by rfl⟩ : syracuseStep 960437 = 90041) (by norm_num)
theorem B2893765 : Blo 758332 2893765 := bbase (se 4 (by rfl) ⟨271290, by rfl⟩ : syracuseStep 2893765 = 542581) (by norm_num)
theorem B960493 : Blo 758332 960493 := bbase (se 3 (by rfl) ⟨180092, by rfl⟩ : syracuseStep 960493 = 360185) (by norm_num)
theorem B1714157 : Blo 758332 1714157 := bbase (se 3 (by rfl) ⟨321404, by rfl⟩ : syracuseStep 1714157 = 642809) (by norm_num)
theorem B2566133 : Blo 758332 2566133 := bbase (se 5 (by rfl) ⟨120287, by rfl⟩ : syracuseStep 2566133 = 240575) (by norm_num)
theorem B1714229 : Blo 758332 1714229 := bbase (se 5 (by rfl) ⟨80354, by rfl⟩ : syracuseStep 1714229 = 160709) (by norm_num)
theorem B960589 : Blo 758332 960589 := bbase (se 3 (by rfl) ⟨180110, by rfl⟩ : syracuseStep 960589 = 360221) (by norm_num)
theorem B1714301 : Blo 758332 1714301 := bbase (se 3 (by rfl) ⟨321431, by rfl⟩ : syracuseStep 1714301 = 642863) (by norm_num)
theorem B1714373 : Blo 758332 1714373 := bbase (se 4 (by rfl) ⟨160722, by rfl⟩ : syracuseStep 1714373 = 321445) (by norm_num)
theorem B2435285 : Blo 758332 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B1222901 : Blo 758332 1222901 := bbase (se 5 (by rfl) ⟨57323, by rfl⟩ : syracuseStep 1222901 = 114647) (by norm_num)
theorem B2894069 : Blo 758332 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B960761 : Blo 758332 960761 := bbase (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) (by norm_num)
theorem B1714445 : Blo 758332 1714445 := bbase (se 3 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 1714445 = 642917) (by norm_num)
theorem B960817 : Blo 758332 960817 := bbase (se 2 (by rfl) ⟨360306, by rfl⟩ : syracuseStep 960817 = 720613) (by norm_num)
theorem B3844421 : Blo 758332 3844421 := bbase (se 4 (by rfl) ⟨360414, by rfl⟩ : syracuseStep 3844421 = 720829) (by norm_num)
theorem B1714517 : Blo 758332 1714517 := bbase (se 10 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 1714517 = 5023) (by norm_num)
theorem B960913 : Blo 758332 960913 := bbase (se 2 (by rfl) ⟨360342, by rfl⟩ : syracuseStep 960913 = 720685) (by norm_num)
theorem B1714589 : Blo 758332 1714589 := bbase (se 3 (by rfl) ⟨321485, by rfl⟩ : syracuseStep 1714589 = 642971) (by norm_num)
theorem B2566565 : Blo 758332 2566565 := bbase (se 4 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 2566565 = 481231) (by norm_num)
theorem B1714661 : Blo 758332 1714661 := bbase (se 4 (by rfl) ⟨160749, by rfl⟩ : syracuseStep 1714661 = 321499) (by norm_num)
theorem B1714733 : Blo 758332 1714733 := bbase (se 3 (by rfl) ⟨321512, by rfl⟩ : syracuseStep 1714733 = 643025) (by norm_num)
theorem B1321525 : Blo 758332 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B961085 : Blo 758332 961085 := bbase (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) (by norm_num)
theorem B2108005 : Blo 758332 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B961141 : Blo 758332 961141 := bbase (se 5 (by rfl) ⟨45053, by rfl⟩ : syracuseStep 961141 = 90107) (by norm_num)
theorem B1714805 : Blo 758332 1714805 := bbase (se 5 (by rfl) ⟨80381, by rfl⟩ : syracuseStep 1714805 = 160763) (by norm_num)
theorem B1714877 : Blo 758332 1714877 := bbase (se 3 (by rfl) ⟨321539, by rfl⟩ : syracuseStep 1714877 = 643079) (by norm_num)
theorem B6925013 : Blo 758332 6925013 := bbase (se 7 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 6925013 = 162305) (by norm_num)
theorem B961237 : Blo 758332 961237 := bbase (se 7 (by rfl) ⟨11264, by rfl⟩ : syracuseStep 961237 = 22529) (by norm_num)
theorem B1714949 : Blo 758332 1714949 := bbase (se 4 (by rfl) ⟨160776, by rfl⟩ : syracuseStep 1714949 = 321553) (by norm_num)
theorem B1715021 : Blo 758332 1715021 := bbase (se 3 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 1715021 = 643133) (by norm_num)
theorem B2566997 : Blo 758332 2566997 := bbase (se 9 (by rfl) ⟨7520, by rfl⟩ : syracuseStep 2566997 = 15041) (by norm_num)
theorem B4107125 : Blo 758332 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B961409 : Blo 758332 961409 := bbase (se 2 (by rfl) ⟨360528, by rfl⟩ : syracuseStep 961409 = 721057) (by norm_num)
theorem B1026965 : Blo 758332 1026965 := bbase (se 6 (by rfl) ⟨24069, by rfl⟩ : syracuseStep 1026965 = 48139) (by norm_num)
theorem B1715093 : Blo 758332 1715093 := bbase (se 6 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 1715093 = 80395) (by norm_num)
theorem B961465 : Blo 758332 961465 := bbase (se 2 (by rfl) ⟨360549, by rfl⟩ : syracuseStep 961465 = 721099) (by norm_num)
theorem B1158085 : Blo 758332 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B1715165 : Blo 758332 1715165 := bbase (se 3 (by rfl) ⟨321593, by rfl⟩ : syracuseStep 1715165 = 643187) (by norm_num)
theorem B961561 : Blo 758332 961561 := bbase (se 2 (by rfl) ⟨360585, by rfl⟩ : syracuseStep 961561 = 721171) (by norm_num)
theorem B1715237 : Blo 758332 1715237 := bbase (se 4 (by rfl) ⟨160803, by rfl⟩ : syracuseStep 1715237 = 321607) (by norm_num)
theorem B961733 : Blo 758332 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B961789 : Blo 758332 961789 := bbase (se 3 (by rfl) ⟨180335, by rfl⟩ : syracuseStep 961789 = 360671) (by norm_num)
theorem B2567429 : Blo 758332 2567429 := bbase (se 4 (by rfl) ⟨240696, by rfl⟩ : syracuseStep 2567429 = 481393) (by norm_num)
theorem B961885 : Blo 758332 961885 := bbase (se 3 (by rfl) ⟨180353, by rfl⟩ : syracuseStep 961885 = 360707) (by norm_num)
theorem B2436581 : Blo 758332 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B962057 : Blo 758332 962057 := bbase (se 2 (by rfl) ⟨360771, by rfl⟩ : syracuseStep 962057 = 721543) (by norm_num)
theorem B962113 : Blo 758332 962113 := bbase (se 2 (by rfl) ⟨360792, by rfl⟩ : syracuseStep 962113 = 721585) (by norm_num)
theorem B2928197 : Blo 758332 2928197 := bbase (se 4 (by rfl) ⟨274518, by rfl⟩ : syracuseStep 2928197 = 549037) (by norm_num)
theorem B3845717 : Blo 758332 3845717 := bbase (se 8 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 3845717 = 45067) (by norm_num)
theorem B962209 : Blo 758332 962209 := bbase (se 2 (by rfl) ⟨360828, by rfl⟩ : syracuseStep 962209 = 721657) (by norm_num)
theorem B2567861 : Blo 758332 2567861 := bbase (se 5 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 2567861 = 240737) (by norm_num)
theorem B1388261 : Blo 758332 1388261 := bbase (se 4 (by rfl) ⟨130149, by rfl⟩ : syracuseStep 1388261 = 260299) (by norm_num)
theorem B962381 : Blo 758332 962381 := bbase (se 3 (by rfl) ⟨180446, by rfl⟩ : syracuseStep 962381 = 360893) (by norm_num)
theorem B962437 : Blo 758332 962437 := bbase (se 4 (by rfl) ⟨90228, by rfl⟩ : syracuseStep 962437 = 180457) (by norm_num)
theorem B1027981 : Blo 758332 1027981 := bbase (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) (by norm_num)
theorem B962533 : Blo 758332 962533 := bbase (se 4 (by rfl) ⟨90237, by rfl⟩ : syracuseStep 962533 = 180475) (by norm_num)
theorem B3518549 : Blo 758332 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B1028197 : Blo 758332 1028197 := bbase (se 4 (by rfl) ⟨96393, by rfl⟩ : syracuseStep 1028197 = 192787) (by norm_num)
theorem B2568293 : Blo 758332 2568293 := bbase (se 4 (by rfl) ⟨240777, by rfl⟩ : syracuseStep 2568293 = 481555) (by norm_num)
theorem B962705 : Blo 758332 962705 := bbase (se 2 (by rfl) ⟨361014, by rfl⟩ : syracuseStep 962705 = 722029) (by norm_num)
theorem B962761 : Blo 758332 962761 := bbase (se 2 (by rfl) ⟨361035, by rfl⟩ : syracuseStep 962761 = 722071) (by norm_num)
theorem B13021397 : Blo 758332 13021397 := bbase (se 7 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 13021397 = 305189) (by norm_num)
theorem B962857 : Blo 758332 962857 := bbase (se 2 (by rfl) ⟨361071, by rfl⟩ : syracuseStep 962857 = 722143) (by norm_num)
theorem B9744725 : Blo 758332 9744725 := bbase (se 10 (by rfl) ⟨14274, by rfl⟩ : syracuseStep 9744725 = 28549) (by norm_num)
theorem B963029 : Blo 758332 963029 := bbase (se 7 (by rfl) ⟨11285, by rfl⟩ : syracuseStep 963029 = 22571) (by norm_num)
theorem B963085 : Blo 758332 963085 := bbase (se 3 (by rfl) ⟨180578, by rfl⟩ : syracuseStep 963085 = 361157) (by norm_num)
theorem B2568725 : Blo 758332 2568725 := bbase (se 6 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 2568725 = 120409) (by norm_num)
theorem B4993589 : Blo 758332 4993589 := bbase (se 5 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 4993589 = 468149) (by norm_num)
theorem B864841 : Blo 758332 864841 := bbase (se 2 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 864841 = 648631) (by norm_num)
theorem B963181 : Blo 758332 963181 := bbase (se 3 (by rfl) ⟨180596, by rfl⟩ : syracuseStep 963181 = 361193) (by norm_num)
theorem B4108981 : Blo 758332 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B2667269 : Blo 758332 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B963353 : Blo 758332 963353 := bbase (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) (by norm_num)
theorem B963409 : Blo 758332 963409 := bbase (se 2 (by rfl) ⟨361278, by rfl⟩ : syracuseStep 963409 = 722557) (by norm_num)
theorem B3847013 : Blo 758332 3847013 := bbase (se 4 (by rfl) ⟨360657, by rfl⟩ : syracuseStep 3847013 = 721315) (by norm_num)
theorem B963505 : Blo 758332 963505 := bbase (se 2 (by rfl) ⟨361314, by rfl⟩ : syracuseStep 963505 = 722629) (by norm_num)
theorem B2569157 : Blo 758332 2569157 := bbase (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) (by norm_num)
theorem B963677 : Blo 758332 963677 := bbase (se 3 (by rfl) ⟨180689, by rfl⟩ : syracuseStep 963677 = 361379) (by norm_num)
theorem B1094797 : Blo 758332 1094797 := bbase (se 3 (by rfl) ⟨205274, by rfl⟩ : syracuseStep 1094797 = 410549) (by norm_num)
theorem B963733 : Blo 758332 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B963829 : Blo 758332 963829 := bbase (se 5 (by rfl) ⟨45179, by rfl⟩ : syracuseStep 963829 = 90359) (by norm_num)
theorem B2438437 : Blo 758332 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B2569589 : Blo 758332 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B964001 : Blo 758332 964001 := bbase (se 2 (by rfl) ⟨361500, by rfl⟩ : syracuseStep 964001 = 723001) (by norm_num)
theorem B2602405 : Blo 758332 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B865753 : Blo 758332 865753 := bbase (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) (by norm_num)
theorem B964057 : Blo 758332 964057 := bbase (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) (by norm_num)
theorem B964153 : Blo 758332 964153 := bbase (se 2 (by rfl) ⟨361557, by rfl⟩ : syracuseStep 964153 = 723115) (by norm_num)
theorem B1390189 : Blo 758332 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B964325 : Blo 758332 964325 := bbase (se 4 (by rfl) ⟨90405, by rfl⟩ : syracuseStep 964325 = 180811) (by norm_num)
theorem B964381 : Blo 758332 964381 := bbase (se 3 (by rfl) ⟨180821, by rfl⟩ : syracuseStep 964381 = 361643) (by norm_num)
theorem B2570021 : Blo 758332 2570021 := bbase (se 4 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 2570021 = 481879) (by norm_num)
theorem B1947493 : Blo 758332 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B964477 : Blo 758332 964477 := bbase (se 3 (by rfl) ⟨180839, by rfl⟩ : syracuseStep 964477 = 361679) (by norm_num)
theorem B2308117 : Blo 758332 2308117 := bbase (se 6 (by rfl) ⟨54096, by rfl⟩ : syracuseStep 2308117 = 108193) (by norm_num)
theorem B964649 : Blo 758332 964649 := bbase (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) (by norm_num)
theorem B1620013 : Blo 758332 1620013 := bbase (se 3 (by rfl) ⟨303752, by rfl⟩ : syracuseStep 1620013 = 607505) (by norm_num)
theorem B964705 : Blo 758332 964705 := bbase (se 2 (by rfl) ⟨361764, by rfl⟩ : syracuseStep 964705 = 723529) (by norm_num)
theorem B3848309 : Blo 758332 3848309 := bbase (se 5 (by rfl) ⟨180389, by rfl⟩ : syracuseStep 3848309 = 360779) (by norm_num)
theorem B5486773 : Blo 758332 5486773 := bbase (se 5 (by rfl) ⟨257192, by rfl⟩ : syracuseStep 5486773 = 514385) (by norm_num)
theorem B1620157 : Blo 758332 1620157 := bbase (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) (by norm_num)
theorem B964801 : Blo 758332 964801 := bbase (se 2 (by rfl) ⟨361800, by rfl⟩ : syracuseStep 964801 = 723601) (by norm_num)
theorem B2570453 : Blo 758332 2570453 := bbase (se 7 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 2570453 = 60245) (by norm_num)
theorem B833933 : Blo 758332 833933 := bbase (se 3 (by rfl) ⟨156362, by rfl⟩ : syracuseStep 833933 = 312725) (by norm_num)
theorem B3127733 : Blo 758332 3127733 := bbase (se 5 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 3127733 = 293225) (by norm_num)
theorem B5781941 : Blo 758332 5781941 := bbase (se 5 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 5781941 = 542057) (by norm_num)
theorem B1620533 : Blo 758332 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B2570885 : Blo 758332 2570885 := bbase (se 4 (by rfl) ⟨241020, by rfl⟩ : syracuseStep 2570885 = 482041) (by norm_num)
theorem B6175541 : Blo 758332 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B1620901 : Blo 758332 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B2571317 : Blo 758332 2571317 := bbase (se 5 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 2571317 = 241061) (by norm_num)
theorem B769105 : Blo 758332 769105 := bbase (se 2 (by rfl) ⟨288414, by rfl⟩ : syracuseStep 769105 = 576829) (by norm_num)
theorem B2309285 : Blo 758332 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B11124053 : Blo 758332 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B3849605 : Blo 758332 3849605 := bbase (se 4 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 3849605 = 721801) (by norm_num)
theorem B2571749 : Blo 758332 2571749 := bbase (se 4 (by rfl) ⟨241101, by rfl⟩ : syracuseStep 2571749 = 482203) (by norm_num)
theorem B2637413 : Blo 758332 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B2572181 : Blo 758332 2572181 := bbase (se 6 (by rfl) ⟨60285, by rfl⟩ : syracuseStep 2572181 = 120571) (by norm_num)
theorem B770029 : Blo 758332 770029 := bbase (se 3 (by rfl) ⟨144380, by rfl⟩ : syracuseStep 770029 = 288761) (by norm_num)
theorem B770045 : Blo 758332 770045 := bbase (se 3 (by rfl) ⟨144383, by rfl⟩ : syracuseStep 770045 = 288767) (by norm_num)
theorem B3293237 : Blo 758332 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B7291093 : Blo 758332 7291093 := bbase (se 7 (by rfl) ⟨85442, by rfl⟩ : syracuseStep 7291093 = 170885) (by norm_num)
theorem B2572613 : Blo 758332 2572613 := bbase (se 4 (by rfl) ⟨241182, by rfl⟩ : syracuseStep 2572613 = 482365) (by norm_num)
theorem B868709 : Blo 758332 868709 := bbase (se 4 (by rfl) ⟨81441, by rfl⟩ : syracuseStep 868709 = 162883) (by norm_num)
theorem B1622405 : Blo 758332 1622405 := bbase (se 4 (by rfl) ⟨152100, by rfl⟩ : syracuseStep 1622405 = 304201) (by norm_num)
theorem B3523061 : Blo 758332 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B6242837 : Blo 758332 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B1622549 : Blo 758332 1622549 := bbase (se 6 (by rfl) ⟨38028, by rfl⟩ : syracuseStep 1622549 = 76057) (by norm_num)
theorem B3654197 : Blo 758332 3654197 := bbase (se 5 (by rfl) ⟨171290, by rfl⟩ : syracuseStep 3654197 = 342581) (by norm_num)
theorem B2310805 : Blo 758332 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B3850901 : Blo 758332 3850901 := bbase (se 6 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 3850901 = 180511) (by norm_num)
theorem B770905 : Blo 758332 770905 := bbase (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) (by norm_num)
theorem B1622909 : Blo 758332 1622909 := bbase (se 3 (by rfl) ⟨304295, by rfl⟩ : syracuseStep 1622909 = 608591) (by norm_num)
theorem B869293 : Blo 758332 869293 := bbase (se 3 (by rfl) ⟨162992, by rfl⟩ : syracuseStep 869293 = 325985) (by norm_num)
theorem B1099045 : Blo 758332 1099045 := bbase (se 4 (by rfl) ⟨103035, by rfl⟩ : syracuseStep 1099045 = 206071) (by norm_num)
theorem B1951253 : Blo 758332 1951253 := bbase (se 6 (by rfl) ⟨45732, by rfl⟩ : syracuseStep 1951253 = 91465) (by norm_num)
theorem B1099333 : Blo 758332 1099333 := bbase (se 4 (by rfl) ⟨103062, by rfl⟩ : syracuseStep 1099333 = 206125) (by norm_num)
theorem B1623797 : Blo 758332 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B3852197 : Blo 758332 3852197 := bbase (se 4 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 3852197 = 722287) (by norm_num)
theorem B1624045 : Blo 758332 1624045 := bbase (se 3 (by rfl) ⟨304508, by rfl⟩ : syracuseStep 1624045 = 609017) (by norm_num)
theorem B1755245 : Blo 758332 1755245 := bbase (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) (by norm_num)
theorem B1460405 : Blo 758332 1460405 := bbase (se 5 (by rfl) ⟨68456, by rfl⟩ : syracuseStep 1460405 = 136913) (by norm_num)
theorem B2738501 : Blo 758332 2738501 := bbase (se 4 (by rfl) ⟨256734, by rfl⟩ : syracuseStep 2738501 = 513469) (by norm_num)
theorem B1624549 : Blo 758332 1624549 := bbase (se 4 (by rfl) ⟨152301, by rfl⟩ : syracuseStep 1624549 = 304603) (by norm_num)
theorem B772669 : Blo 758332 772669 := bbase (se 3 (by rfl) ⟨144875, by rfl⟩ : syracuseStep 772669 = 289751) (by norm_num)
theorem B7785173 : Blo 758332 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B1919821 : Blo 758332 1919821 := bbase (se 3 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 1919821 = 719933) (by norm_num)
theorem B4868981 : Blo 758332 4868981 := bbase (se 5 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 4868981 = 456467) (by norm_num)
theorem B1919933 : Blo 758332 1919933 := bbase (se 3 (by rfl) ⟨359987, by rfl⟩ : syracuseStep 1919933 = 719975) (by norm_num)
theorem B1920125 : Blo 758332 1920125 := bbase (se 3 (by rfl) ⟨360023, by rfl⟩ : syracuseStep 1920125 = 720047) (by norm_num)
theorem B3853493 : Blo 758332 3853493 := bbase (se 5 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 3853493 = 361265) (by norm_num)
theorem B1625437 : Blo 758332 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B1920469 : Blo 758332 1920469 := bbase (se 7 (by rfl) ⟨22505, by rfl⟩ : syracuseStep 1920469 = 45011) (by norm_num)
theorem B1920581 : Blo 758332 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B937597 : Blo 758332 937597 := bbase (se 3 (by rfl) ⟨175799, by rfl⟩ : syracuseStep 937597 = 351599) (by norm_num)
theorem B1920773 : Blo 758332 1920773 := bbase (se 4 (by rfl) ⟨180072, by rfl⟩ : syracuseStep 1920773 = 360145) (by norm_num)
theorem B4378421 : Blo 758332 4378421 := bbase (se 5 (by rfl) ⟨205238, by rfl⟩ : syracuseStep 4378421 = 410477) (by norm_num)
theorem B1625933 : Blo 758332 1625933 := bbase (se 3 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 1625933 = 609725) (by norm_num)
theorem B1298357 : Blo 758332 1298357 := bbase (se 5 (by rfl) ⟨60860, by rfl⟩ : syracuseStep 1298357 = 121721) (by norm_num)
theorem B1921117 : Blo 758332 1921117 := bbase (se 3 (by rfl) ⟨360209, by rfl⟩ : syracuseStep 1921117 = 720419) (by norm_num)
theorem B1921229 : Blo 758332 1921229 := bbase (se 3 (by rfl) ⟨360230, by rfl⟩ : syracuseStep 1921229 = 720461) (by norm_num)
theorem B7295285 : Blo 758332 7295285 := bbase (se 5 (by rfl) ⟨341966, by rfl⟩ : syracuseStep 7295285 = 683933) (by norm_num)
theorem B2314565 : Blo 758332 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B3658117 : Blo 758332 3658117 := bbase (se 4 (by rfl) ⟨342948, by rfl⟩ : syracuseStep 3658117 = 685897) (by norm_num)
theorem B1921421 : Blo 758332 1921421 := bbase (se 3 (by rfl) ⟨360266, by rfl⟩ : syracuseStep 1921421 = 720533) (by norm_num)
theorem B1855885 : Blo 758332 1855885 := bbase (se 3 (by rfl) ⟨347978, by rfl⟩ : syracuseStep 1855885 = 695957) (by norm_num)
theorem B3854789 : Blo 758332 3854789 := bbase (se 4 (by rfl) ⟨361386, by rfl⟩ : syracuseStep 3854789 = 722773) (by norm_num)
theorem B1626821 : Blo 758332 1626821 := bbase (se 4 (by rfl) ⟨152514, by rfl⟩ : syracuseStep 1626821 = 305029) (by norm_num)
theorem B1921765 : Blo 758332 1921765 := bbase (se 4 (by rfl) ⟨180165, by rfl⟩ : syracuseStep 1921765 = 360331) (by norm_num)
theorem B1626941 : Blo 758332 1626941 := bbase (se 3 (by rfl) ⟨305051, by rfl⟩ : syracuseStep 1626941 = 610103) (by norm_num)
theorem B1921877 : Blo 758332 1921877 := bbase (se 9 (by rfl) ⟨5630, by rfl⟩ : syracuseStep 1921877 = 11261) (by norm_num)
theorem B1922069 : Blo 758332 1922069 := bbase (se 6 (by rfl) ⟨45048, by rfl⟩ : syracuseStep 1922069 = 90097) (by norm_num)
theorem B1824061 : Blo 758332 1824061 := bbase (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) (by norm_num)
theorem B1922413 : Blo 758332 1922413 := bbase (se 3 (by rfl) ⟨360452, by rfl⟩ : syracuseStep 1922413 = 720905) (by norm_num)
theorem B1627573 : Blo 758332 1627573 := bbase (se 5 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 1627573 = 152585) (by norm_num)
theorem B1922525 : Blo 758332 1922525 := bbase (se 3 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 1922525 = 720947) (by norm_num)
theorem B1922717 : Blo 758332 1922717 := bbase (se 3 (by rfl) ⟨360509, by rfl⟩ : syracuseStep 1922717 = 721019) (by norm_num)
theorem B1824437 : Blo 758332 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B3856085 : Blo 758332 3856085 := bbase (se 7 (by rfl) ⟨45188, by rfl⟩ : syracuseStep 3856085 = 90377) (by norm_num)
theorem B13850453 : Blo 758332 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B2053973 : Blo 758332 2053973 := bbase (se 9 (by rfl) ⟨6017, by rfl⟩ : syracuseStep 2053973 = 12035) (by norm_num)
theorem B1923061 : Blo 758332 1923061 := bbase (se 5 (by rfl) ⟨90143, by rfl⟩ : syracuseStep 1923061 = 180287) (by norm_num)
theorem B1824869 : Blo 758332 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B1923173 : Blo 758332 1923173 := bbase (se 4 (by rfl) ⟨180297, by rfl⟩ : syracuseStep 1923173 = 360595) (by norm_num)
theorem B1923365 : Blo 758332 1923365 := bbase (se 4 (by rfl) ⟨180315, by rfl⟩ : syracuseStep 1923365 = 360631) (by norm_num)
theorem B1923709 : Blo 758332 1923709 := bbase (se 3 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 1923709 = 721391) (by norm_num)
theorem B1825445 : Blo 758332 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B1923821 : Blo 758332 1923821 := bbase (se 3 (by rfl) ⟨360716, by rfl⟩ : syracuseStep 1923821 = 721433) (by norm_num)
theorem B1465085 : Blo 758332 1465085 := bbase (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) (by norm_num)
theorem B1137509 : Blo 758332 1137509 := bbase (se 4 (by rfl) ⟨106641, by rfl⟩ : syracuseStep 1137509 = 213283) (by norm_num)
theorem B1137533 : Blo 758332 1137533 := bbase (se 3 (by rfl) ⟨213287, by rfl⟩ : syracuseStep 1137533 = 426575) (by norm_num)
theorem B1137557 : Blo 758332 1137557 := bbase (se 6 (by rfl) ⟨26661, by rfl⟩ : syracuseStep 1137557 = 53323) (by norm_num)
theorem B1137581 : Blo 758332 1137581 := bbase (se 3 (by rfl) ⟨213296, by rfl⟩ : syracuseStep 1137581 = 426593) (by norm_num)
theorem B1924013 : Blo 758332 1924013 := bbase (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) (by norm_num)
theorem B1137605 : Blo 758332 1137605 := bbase (se 4 (by rfl) ⟨106650, by rfl⟩ : syracuseStep 1137605 = 213301) (by norm_num)
theorem B1137629 : Blo 758332 1137629 := bbase (se 3 (by rfl) ⟨213305, by rfl⟩ : syracuseStep 1137629 = 426611) (by norm_num)
theorem B3857381 : Blo 758332 3857381 := bbase (se 4 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 3857381 = 723259) (by norm_num)
theorem B1137653 : Blo 758332 1137653 := bbase (se 5 (by rfl) ⟨53327, by rfl⟩ : syracuseStep 1137653 = 106655) (by norm_num)
theorem B1137677 : Blo 758332 1137677 := bbase (se 3 (by rfl) ⟨213314, by rfl⟩ : syracuseStep 1137677 = 426629) (by norm_num)
theorem B1137701 : Blo 758332 1137701 := bbase (se 4 (by rfl) ⟨106659, by rfl⟩ : syracuseStep 1137701 = 213319) (by norm_num)
theorem B1137725 : Blo 758332 1137725 := bbase (se 3 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 1137725 = 426647) (by norm_num)
theorem B973901 : Blo 758332 973901 := bbase (se 3 (by rfl) ⟨182606, by rfl⟩ : syracuseStep 973901 = 365213) (by norm_num)
theorem B1137749 : Blo 758332 1137749 := bbase (se 8 (by rfl) ⟨6666, by rfl⟩ : syracuseStep 1137749 = 13333) (by norm_num)
theorem B1236061 : Blo 758332 1236061 := bbase (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) (by norm_num)
theorem B1137773 : Blo 758332 1137773 := bbase (se 3 (by rfl) ⟨213332, by rfl⟩ : syracuseStep 1137773 = 426665) (by norm_num)
theorem B810109 : Blo 758332 810109 := bbase (se 3 (by rfl) ⟨151895, by rfl⟩ : syracuseStep 810109 = 303791) (by norm_num)
theorem B1137797 : Blo 758332 1137797 := bbase (se 4 (by rfl) ⟨106668, by rfl⟩ : syracuseStep 1137797 = 213337) (by norm_num)
theorem B1137821 : Blo 758332 1137821 := bbase (se 3 (by rfl) ⟨213341, by rfl⟩ : syracuseStep 1137821 = 426683) (by norm_num)
theorem B1137845 : Blo 758332 1137845 := bbase (se 5 (by rfl) ⟨53336, by rfl⟩ : syracuseStep 1137845 = 106673) (by norm_num)
theorem B810181 : Blo 758332 810181 := bbase (se 4 (by rfl) ⟨75954, by rfl⟩ : syracuseStep 810181 = 151909) (by norm_num)
theorem B1137869 : Blo 758332 1137869 := bbase (se 3 (by rfl) ⟨213350, by rfl⟩ : syracuseStep 1137869 = 426701) (by norm_num)
theorem B1137893 : Blo 758332 1137893 := bbase (se 4 (by rfl) ⟨106677, by rfl⟩ : syracuseStep 1137893 = 213355) (by norm_num)
theorem B1465573 : Blo 758332 1465573 := bbase (se 4 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 1465573 = 274795) (by norm_num)
theorem B1137917 : Blo 758332 1137917 := bbase (se 3 (by rfl) ⟨213359, by rfl⟩ : syracuseStep 1137917 = 426719) (by norm_num)
theorem B1924357 : Blo 758332 1924357 := bbase (se 4 (by rfl) ⟨180408, by rfl⟩ : syracuseStep 1924357 = 360817) (by norm_num)
theorem B1137941 : Blo 758332 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B1137965 : Blo 758332 1137965 := bbase (se 3 (by rfl) ⟨213368, by rfl⟩ : syracuseStep 1137965 = 426737) (by norm_num)
theorem B1137989 : Blo 758332 1137989 := bbase (se 4 (by rfl) ⟨106686, by rfl⟩ : syracuseStep 1137989 = 213373) (by norm_num)
theorem B1138013 : Blo 758332 1138013 := bbase (se 3 (by rfl) ⟨213377, by rfl⟩ : syracuseStep 1138013 = 426755) (by norm_num)
theorem B1138037 : Blo 758332 1138037 := bbase (se 5 (by rfl) ⟨53345, by rfl⟩ : syracuseStep 1138037 = 106691) (by norm_num)
theorem B1924469 : Blo 758332 1924469 := bbase (se 5 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 1924469 = 180419) (by norm_num)
theorem B810361 : Blo 758332 810361 := bbase (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) (by norm_num)
theorem B1138061 : Blo 758332 1138061 := bbase (se 3 (by rfl) ⟨213386, by rfl⟩ : syracuseStep 1138061 = 426773) (by norm_num)
theorem B1138085 : Blo 758332 1138085 := bbase (se 4 (by rfl) ⟨106695, by rfl⟩ : syracuseStep 1138085 = 213391) (by norm_num)
theorem B1138109 : Blo 758332 1138109 := bbase (se 3 (by rfl) ⟨213395, by rfl⟩ : syracuseStep 1138109 = 426791) (by norm_num)
theorem B1138133 : Blo 758332 1138133 := bbase (se 7 (by rfl) ⟨13337, by rfl⟩ : syracuseStep 1138133 = 26675) (by norm_num)
theorem B1138157 : Blo 758332 1138157 := bbase (se 3 (by rfl) ⟨213404, by rfl⟩ : syracuseStep 1138157 = 426809) (by norm_num)
theorem B1138181 : Blo 758332 1138181 := bbase (se 4 (by rfl) ⟨106704, by rfl⟩ : syracuseStep 1138181 = 213409) (by norm_num)
theorem B1138205 : Blo 758332 1138205 := bbase (se 3 (by rfl) ⟨213413, by rfl⟩ : syracuseStep 1138205 = 426827) (by norm_num)
theorem B1138229 : Blo 758332 1138229 := bbase (se 5 (by rfl) ⟨53354, by rfl⟩ : syracuseStep 1138229 = 106709) (by norm_num)
theorem B1924661 : Blo 758332 1924661 := bbase (se 5 (by rfl) ⟨90218, by rfl⟩ : syracuseStep 1924661 = 180437) (by norm_num)
theorem B2743877 : Blo 758332 2743877 := bbase (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) (by norm_num)
theorem B1138253 : Blo 758332 1138253 := bbase (se 3 (by rfl) ⟨213422, by rfl⟩ : syracuseStep 1138253 = 426845) (by norm_num)
theorem B1138277 : Blo 758332 1138277 := bbase (se 4 (by rfl) ⟨106713, by rfl⟩ : syracuseStep 1138277 = 213427) (by norm_num)
theorem B2252405 : Blo 758332 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1138301 : Blo 758332 1138301 := bbase (se 3 (by rfl) ⟨213431, by rfl⟩ : syracuseStep 1138301 = 426863) (by norm_num)
theorem B5758613 : Blo 758332 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B1138325 : Blo 758332 1138325 := bbase (se 6 (by rfl) ⟨26679, by rfl⟩ : syracuseStep 1138325 = 53359) (by norm_num)
theorem B1138349 : Blo 758332 1138349 := bbase (se 3 (by rfl) ⟨213440, by rfl⟩ : syracuseStep 1138349 = 426881) (by norm_num)
theorem B1138373 : Blo 758332 1138373 := bbase (se 4 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 1138373 = 213445) (by norm_num)
theorem B1138397 : Blo 758332 1138397 := bbase (se 3 (by rfl) ⟨213449, by rfl⟩ : syracuseStep 1138397 = 426899) (by norm_num)
theorem B1138421 : Blo 758332 1138421 := bbase (se 5 (by rfl) ⟨53363, by rfl⟩ : syracuseStep 1138421 = 106727) (by norm_num)
theorem B1138445 : Blo 758332 1138445 := bbase (se 3 (by rfl) ⟨213458, by rfl⟩ : syracuseStep 1138445 = 426917) (by norm_num)
theorem B1138469 : Blo 758332 1138469 := bbase (se 4 (by rfl) ⟨106731, by rfl⟩ : syracuseStep 1138469 = 213463) (by norm_num)
theorem B810805 : Blo 758332 810805 := bbase (se 5 (by rfl) ⟨38006, by rfl⟩ : syracuseStep 810805 = 76013) (by norm_num)
theorem B1138493 : Blo 758332 1138493 := bbase (se 3 (by rfl) ⟨213467, by rfl⟩ : syracuseStep 1138493 = 426935) (by norm_num)
theorem B1138517 : Blo 758332 1138517 := bbase (se 9 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 1138517 = 6671) (by norm_num)
theorem B1138541 : Blo 758332 1138541 := bbase (se 3 (by rfl) ⟨213476, by rfl⟩ : syracuseStep 1138541 = 426953) (by norm_num)
theorem B1138565 : Blo 758332 1138565 := bbase (se 4 (by rfl) ⟨106740, by rfl⟩ : syracuseStep 1138565 = 213481) (by norm_num)
theorem B1925005 : Blo 758332 1925005 := bbase (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) (by norm_num)
theorem B1138589 : Blo 758332 1138589 := bbase (se 3 (by rfl) ⟨213485, by rfl⟩ : syracuseStep 1138589 = 426971) (by norm_num)
theorem B974749 : Blo 758332 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B810929 : Blo 758332 810929 := bbase (se 2 (by rfl) ⟨304098, by rfl⟩ : syracuseStep 810929 = 608197) (by norm_num)
theorem B1138613 : Blo 758332 1138613 := bbase (se 5 (by rfl) ⟨53372, by rfl⟩ : syracuseStep 1138613 = 106745) (by norm_num)
theorem B1138637 : Blo 758332 1138637 := bbase (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) (by norm_num)
theorem B1138661 : Blo 758332 1138661 := bbase (se 4 (by rfl) ⟨106749, by rfl⟩ : syracuseStep 1138661 = 213499) (by norm_num)
theorem B1925117 : Blo 758332 1925117 := bbase (se 3 (by rfl) ⟨360959, by rfl⟩ : syracuseStep 1925117 = 721919) (by norm_num)
theorem B1138685 : Blo 758332 1138685 := bbase (se 3 (by rfl) ⟨213503, by rfl⟩ : syracuseStep 1138685 = 427007) (by norm_num)
theorem B1138709 : Blo 758332 1138709 := bbase (se 6 (by rfl) ⟨26688, by rfl⟩ : syracuseStep 1138709 = 53377) (by norm_num)
theorem B1138733 : Blo 758332 1138733 := bbase (se 3 (by rfl) ⟨213512, by rfl⟩ : syracuseStep 1138733 = 427025) (by norm_num)
theorem B1138757 : Blo 758332 1138757 := bbase (se 4 (by rfl) ⟨106758, by rfl⟩ : syracuseStep 1138757 = 213517) (by norm_num)
theorem B1138781 : Blo 758332 1138781 := bbase (se 3 (by rfl) ⟨213521, by rfl⟩ : syracuseStep 1138781 = 427043) (by norm_num)
theorem B1138805 : Blo 758332 1138805 := bbase (se 5 (by rfl) ⟨53381, by rfl⟩ : syracuseStep 1138805 = 106763) (by norm_num)
theorem B1138829 : Blo 758332 1138829 := bbase (se 3 (by rfl) ⟨213530, by rfl⟩ : syracuseStep 1138829 = 427061) (by norm_num)
theorem B1138853 : Blo 758332 1138853 := bbase (se 4 (by rfl) ⟨106767, by rfl⟩ : syracuseStep 1138853 = 213535) (by norm_num)
theorem B811181 : Blo 758332 811181 := bbase (se 3 (by rfl) ⟨152096, by rfl⟩ : syracuseStep 811181 = 304193) (by norm_num)
theorem B1138877 : Blo 758332 1138877 := bbase (se 3 (by rfl) ⟨213539, by rfl⟩ : syracuseStep 1138877 = 427079) (by norm_num)
theorem B1925309 : Blo 758332 1925309 := bbase (se 3 (by rfl) ⟨360995, by rfl⟩ : syracuseStep 1925309 = 721991) (by norm_num)
theorem B1138901 : Blo 758332 1138901 := bbase (se 7 (by rfl) ⟨13346, by rfl⟩ : syracuseStep 1138901 = 26693) (by norm_num)
theorem B1138925 : Blo 758332 1138925 := bbase (se 3 (by rfl) ⟨213548, by rfl⟩ : syracuseStep 1138925 = 427097) (by norm_num)
theorem B3858677 : Blo 758332 3858677 := bbase (se 5 (by rfl) ⟨180875, by rfl⟩ : syracuseStep 3858677 = 361751) (by norm_num)
theorem B1138949 : Blo 758332 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B1138973 : Blo 758332 1138973 := bbase (se 3 (by rfl) ⟨213557, by rfl⟩ : syracuseStep 1138973 = 427115) (by norm_num)
theorem B3662117 : Blo 758332 3662117 := bbase (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) (by norm_num)
theorem B1138997 : Blo 758332 1138997 := bbase (se 5 (by rfl) ⟨53390, by rfl⟩ : syracuseStep 1138997 = 106781) (by norm_num)
theorem B1139021 : Blo 758332 1139021 := bbase (se 3 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 1139021 = 427133) (by norm_num)
theorem B18702677 : Blo 758332 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B1139045 : Blo 758332 1139045 := bbase (se 4 (by rfl) ⟨106785, by rfl⟩ : syracuseStep 1139045 = 213571) (by norm_num)
theorem B1139069 : Blo 758332 1139069 := bbase (se 3 (by rfl) ⟨213575, by rfl⟩ : syracuseStep 1139069 = 427151) (by norm_num)
theorem B1139093 : Blo 758332 1139093 := bbase (se 6 (by rfl) ⟨26697, by rfl⟩ : syracuseStep 1139093 = 53395) (by norm_num)
theorem B1139117 : Blo 758332 1139117 := bbase (se 3 (by rfl) ⟨213584, by rfl⟩ : syracuseStep 1139117 = 427169) (by norm_num)
theorem B1139141 : Blo 758332 1139141 := bbase (se 4 (by rfl) ⟨106794, by rfl⟩ : syracuseStep 1139141 = 213589) (by norm_num)
theorem B1139165 : Blo 758332 1139165 := bbase (se 3 (by rfl) ⟨213593, by rfl⟩ : syracuseStep 1139165 = 427187) (by norm_num)
theorem B1139189 : Blo 758332 1139189 := bbase (se 5 (by rfl) ⟨53399, by rfl⟩ : syracuseStep 1139189 = 106799) (by norm_num)
theorem B1139213 : Blo 758332 1139213 := bbase (se 3 (by rfl) ⟨213602, by rfl⟩ : syracuseStep 1139213 = 427205) (by norm_num)
theorem B1925653 : Blo 758332 1925653 := bbase (se 6 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 1925653 = 90265) (by norm_num)
theorem B1139237 : Blo 758332 1139237 := bbase (se 4 (by rfl) ⟨106803, by rfl⟩ : syracuseStep 1139237 = 213607) (by norm_num)
theorem B1139261 : Blo 758332 1139261 := bbase (se 3 (by rfl) ⟨213611, by rfl⟩ : syracuseStep 1139261 = 427223) (by norm_num)
theorem B3662405 : Blo 758332 3662405 := bbase (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) (by norm_num)
theorem B1139285 : Blo 758332 1139285 := bbase (se 8 (by rfl) ⟨6675, by rfl⟩ : syracuseStep 1139285 = 13351) (by norm_num)
theorem B811625 : Blo 758332 811625 := bbase (se 2 (by rfl) ⟨304359, by rfl⟩ : syracuseStep 811625 = 608719) (by norm_num)
theorem B1139309 : Blo 758332 1139309 := bbase (se 3 (by rfl) ⟨213620, by rfl⟩ : syracuseStep 1139309 = 427241) (by norm_num)
theorem B1139333 : Blo 758332 1139333 := bbase (se 4 (by rfl) ⟨106812, by rfl⟩ : syracuseStep 1139333 = 213625) (by norm_num)
theorem B1925765 : Blo 758332 1925765 := bbase (se 4 (by rfl) ⟨180540, by rfl⟩ : syracuseStep 1925765 = 361081) (by norm_num)
theorem B1139357 : Blo 758332 1139357 := bbase (se 3 (by rfl) ⟨213629, by rfl⟩ : syracuseStep 1139357 = 427259) (by norm_num)
theorem B1139381 : Blo 758332 1139381 := bbase (se 5 (by rfl) ⟨53408, by rfl⟩ : syracuseStep 1139381 = 106817) (by norm_num)
theorem B1139405 : Blo 758332 1139405 := bbase (se 3 (by rfl) ⟨213638, by rfl⟩ : syracuseStep 1139405 = 427277) (by norm_num)
theorem B1172173 : Blo 758332 1172173 := bbase (se 3 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 1172173 = 439565) (by norm_num)
theorem B1139429 : Blo 758332 1139429 := bbase (se 4 (by rfl) ⟨106821, by rfl⟩ : syracuseStep 1139429 = 213643) (by norm_num)
theorem B1139453 : Blo 758332 1139453 := bbase (se 3 (by rfl) ⟨213647, by rfl⟩ : syracuseStep 1139453 = 427295) (by norm_num)
theorem B1139477 : Blo 758332 1139477 := bbase (se 6 (by rfl) ⟨26706, by rfl⟩ : syracuseStep 1139477 = 53413) (by norm_num)
theorem B4875029 : Blo 758332 4875029 := bbase (se 6 (by rfl) ⟨114258, by rfl⟩ : syracuseStep 4875029 = 228517) (by norm_num)
theorem B1139501 : Blo 758332 1139501 := bbase (se 3 (by rfl) ⟨213656, by rfl⟩ : syracuseStep 1139501 = 427313) (by norm_num)
theorem B1139525 : Blo 758332 1139525 := bbase (se 4 (by rfl) ⟨106830, by rfl⟩ : syracuseStep 1139525 = 213661) (by norm_num)
theorem B1925957 : Blo 758332 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B1139549 : Blo 758332 1139549 := bbase (se 3 (by rfl) ⟨213665, by rfl⟩ : syracuseStep 1139549 = 427331) (by norm_num)
theorem B811873 : Blo 758332 811873 := bbase (se 2 (by rfl) ⟨304452, by rfl⟩ : syracuseStep 811873 = 608905) (by norm_num)
theorem B1139573 : Blo 758332 1139573 := bbase (se 5 (by rfl) ⟨53417, by rfl⟩ : syracuseStep 1139573 = 106835) (by norm_num)
theorem B1139597 : Blo 758332 1139597 := bbase (se 3 (by rfl) ⟨213674, by rfl⟩ : syracuseStep 1139597 = 427349) (by norm_num)
theorem B1139621 : Blo 758332 1139621 := bbase (se 4 (by rfl) ⟨106839, by rfl⟩ : syracuseStep 1139621 = 213679) (by norm_num)
theorem B1139645 : Blo 758332 1139645 := bbase (se 3 (by rfl) ⟨213683, by rfl⟩ : syracuseStep 1139645 = 427367) (by norm_num)
theorem B1041349 : Blo 758332 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B1139669 : Blo 758332 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B1139693 : Blo 758332 1139693 := bbase (se 3 (by rfl) ⟨213692, by rfl⟩ : syracuseStep 1139693 = 427385) (by norm_num)
theorem B1139717 : Blo 758332 1139717 := bbase (se 4 (by rfl) ⟨106848, by rfl⟩ : syracuseStep 1139717 = 213697) (by norm_num)
theorem B1139741 : Blo 758332 1139741 := bbase (se 3 (by rfl) ⟨213701, by rfl⟩ : syracuseStep 1139741 = 427403) (by norm_num)
theorem B1139765 : Blo 758332 1139765 := bbase (se 5 (by rfl) ⟨53426, by rfl⟩ : syracuseStep 1139765 = 106853) (by norm_num)
theorem B1139789 : Blo 758332 1139789 := bbase (se 3 (by rfl) ⟨213710, by rfl⟩ : syracuseStep 1139789 = 427421) (by norm_num)
theorem B1139813 : Blo 758332 1139813 := bbase (se 4 (by rfl) ⟨106857, by rfl⟩ : syracuseStep 1139813 = 213715) (by norm_num)
theorem B1139837 : Blo 758332 1139837 := bbase (se 3 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 1139837 = 427439) (by norm_num)
theorem B1139861 : Blo 758332 1139861 := bbase (se 6 (by rfl) ⟨26715, by rfl⟩ : syracuseStep 1139861 = 53431) (by norm_num)
theorem B1926301 : Blo 758332 1926301 := bbase (se 3 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 1926301 = 722363) (by norm_num)
theorem B1139885 : Blo 758332 1139885 := bbase (se 3 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 1139885 = 427457) (by norm_num)
theorem B1828021 : Blo 758332 1828021 := bbase (se 5 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 1828021 = 171377) (by norm_num)
theorem B1139909 : Blo 758332 1139909 := bbase (se 4 (by rfl) ⟨106866, by rfl⟩ : syracuseStep 1139909 = 213733) (by norm_num)
theorem B1139933 : Blo 758332 1139933 := bbase (se 3 (by rfl) ⟨213737, by rfl⟩ : syracuseStep 1139933 = 427475) (by norm_num)
theorem B1139957 : Blo 758332 1139957 := bbase (se 5 (by rfl) ⟨53435, by rfl⟩ : syracuseStep 1139957 = 106871) (by norm_num)
theorem B1139981 : Blo 758332 1139981 := bbase (se 3 (by rfl) ⟨213746, by rfl⟩ : syracuseStep 1139981 = 427493) (by norm_num)
theorem B1926413 : Blo 758332 1926413 := bbase (se 3 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 1926413 = 722405) (by norm_num)
theorem B812317 : Blo 758332 812317 := bbase (se 3 (by rfl) ⟨152309, by rfl⟩ : syracuseStep 812317 = 304619) (by norm_num)
theorem B1729829 : Blo 758332 1729829 := bbase (se 4 (by rfl) ⟨162171, by rfl⟩ : syracuseStep 1729829 = 324343) (by norm_num)
theorem B1140005 : Blo 758332 1140005 := bbase (se 4 (by rfl) ⟨106875, by rfl⟩ : syracuseStep 1140005 = 213751) (by norm_num)
theorem B5203253 : Blo 758332 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B1140029 : Blo 758332 1140029 := bbase (se 3 (by rfl) ⟨213755, by rfl⟩ : syracuseStep 1140029 = 427511) (by norm_num)
theorem B1303885 : Blo 758332 1303885 := bbase (se 3 (by rfl) ⟨244478, by rfl⟩ : syracuseStep 1303885 = 488957) (by norm_num)
theorem B1140053 : Blo 758332 1140053 := bbase (se 12 (by rfl) ⟨417, by rfl⟩ : syracuseStep 1140053 = 835) (by norm_num)
theorem B812377 : Blo 758332 812377 := bbase (se 2 (by rfl) ⟨304641, by rfl⟩ : syracuseStep 812377 = 609283) (by norm_num)
theorem B1140077 : Blo 758332 1140077 := bbase (se 3 (by rfl) ⟨213764, by rfl⟩ : syracuseStep 1140077 = 427529) (by norm_num)
theorem B1140101 : Blo 758332 1140101 := bbase (se 4 (by rfl) ⟨106884, by rfl⟩ : syracuseStep 1140101 = 213769) (by norm_num)
theorem B1140125 : Blo 758332 1140125 := bbase (se 3 (by rfl) ⟨213773, by rfl⟩ : syracuseStep 1140125 = 427547) (by norm_num)
theorem B1140149 : Blo 758332 1140149 := bbase (se 5 (by rfl) ⟨53444, by rfl⟩ : syracuseStep 1140149 = 106889) (by norm_num)
theorem B1140173 : Blo 758332 1140173 := bbase (se 3 (by rfl) ⟨213782, by rfl⟩ : syracuseStep 1140173 = 427565) (by norm_num)
theorem B1926605 : Blo 758332 1926605 := bbase (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) (by norm_num)
theorem B1140197 : Blo 758332 1140197 := bbase (se 4 (by rfl) ⟨106893, by rfl⟩ : syracuseStep 1140197 = 213787) (by norm_num)
theorem B1140221 : Blo 758332 1140221 := bbase (se 3 (by rfl) ⟨213791, by rfl⟩ : syracuseStep 1140221 = 427583) (by norm_num)
theorem B1140245 : Blo 758332 1140245 := bbase (se 6 (by rfl) ⟨26724, by rfl⟩ : syracuseStep 1140245 = 53449) (by norm_num)
theorem B1140269 : Blo 758332 1140269 := bbase (se 3 (by rfl) ⟨213800, by rfl⟩ : syracuseStep 1140269 = 427601) (by norm_num)
theorem B1140293 : Blo 758332 1140293 := bbase (se 4 (by rfl) ⟨106902, by rfl⟩ : syracuseStep 1140293 = 213805) (by norm_num)
theorem B1140317 : Blo 758332 1140317 := bbase (se 3 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 1140317 = 427619) (by norm_num)
theorem B1140341 : Blo 758332 1140341 := bbase (se 5 (by rfl) ⟨53453, by rfl⟩ : syracuseStep 1140341 = 106907) (by norm_num)
theorem B1140365 : Blo 758332 1140365 := bbase (se 3 (by rfl) ⟨213818, by rfl⟩ : syracuseStep 1140365 = 427637) (by norm_num)
theorem B812693 : Blo 758332 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B1140389 : Blo 758332 1140389 := bbase (se 4 (by rfl) ⟨106911, by rfl⟩ : syracuseStep 1140389 = 213823) (by norm_num)
theorem B1140413 : Blo 758332 1140413 := bbase (se 3 (by rfl) ⟨213827, by rfl⟩ : syracuseStep 1140413 = 427655) (by norm_num)
theorem B1140437 : Blo 758332 1140437 := bbase (se 7 (by rfl) ⟨13364, by rfl⟩ : syracuseStep 1140437 = 26729) (by norm_num)
theorem B1140461 : Blo 758332 1140461 := bbase (se 3 (by rfl) ⟨213836, by rfl⟩ : syracuseStep 1140461 = 427673) (by norm_num)
theorem B911089 : Blo 758332 911089 := bbase (se 2 (by rfl) ⟨341658, by rfl⟩ : syracuseStep 911089 = 683317) (by norm_num)
theorem B1140485 : Blo 758332 1140485 := bbase (se 4 (by rfl) ⟨106920, by rfl⟩ : syracuseStep 1140485 = 213841) (by norm_num)
theorem B1140509 : Blo 758332 1140509 := bbase (se 3 (by rfl) ⟨213845, by rfl⟩ : syracuseStep 1140509 = 427691) (by norm_num)
theorem B1926949 : Blo 758332 1926949 := bbase (se 4 (by rfl) ⟨180651, by rfl⟩ : syracuseStep 1926949 = 361303) (by norm_num)
theorem B1140533 : Blo 758332 1140533 := bbase (se 5 (by rfl) ⟨53462, by rfl⟩ : syracuseStep 1140533 = 106925) (by norm_num)
theorem B1140557 : Blo 758332 1140557 := bbase (se 3 (by rfl) ⟨213854, by rfl⟩ : syracuseStep 1140557 = 427709) (by norm_num)
theorem B1140581 : Blo 758332 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B1140605 : Blo 758332 1140605 := bbase (se 3 (by rfl) ⟨213863, by rfl⟩ : syracuseStep 1140605 = 427727) (by norm_num)
theorem B911233 : Blo 758332 911233 := bbase (se 2 (by rfl) ⟨341712, by rfl⟩ : syracuseStep 911233 = 683425) (by norm_num)
theorem B1140629 : Blo 758332 1140629 := bbase (se 6 (by rfl) ⟨26733, by rfl⟩ : syracuseStep 1140629 = 53467) (by norm_num)
theorem B1927061 : Blo 758332 1927061 := bbase (se 6 (by rfl) ⟨45165, by rfl⟩ : syracuseStep 1927061 = 90331) (by norm_num)
theorem B3762085 : Blo 758332 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B1140653 : Blo 758332 1140653 := bbase (se 3 (by rfl) ⟨213872, by rfl⟩ : syracuseStep 1140653 = 427745) (by norm_num)
theorem B1140677 : Blo 758332 1140677 := bbase (se 4 (by rfl) ⟨106938, by rfl⟩ : syracuseStep 1140677 = 213877) (by norm_num)
theorem B4319189 : Blo 758332 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B1140701 : Blo 758332 1140701 := bbase (se 3 (by rfl) ⟨213881, by rfl⟩ : syracuseStep 1140701 = 427763) (by norm_num)
theorem B1370093 : Blo 758332 1370093 := bbase (se 3 (by rfl) ⟨256892, by rfl⟩ : syracuseStep 1370093 = 513785) (by norm_num)
theorem B1140725 : Blo 758332 1140725 := bbase (se 5 (by rfl) ⟨53471, by rfl⟩ : syracuseStep 1140725 = 106943) (by norm_num)
theorem B1730557 : Blo 758332 1730557 := bbase (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) (by norm_num)
theorem B1140749 : Blo 758332 1140749 := bbase (se 3 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 1140749 = 427781) (by norm_num)
theorem B1140773 : Blo 758332 1140773 := bbase (se 4 (by rfl) ⟨106947, by rfl⟩ : syracuseStep 1140773 = 213895) (by norm_num)
theorem B1140797 : Blo 758332 1140797 := bbase (se 3 (by rfl) ⟨213899, by rfl⟩ : syracuseStep 1140797 = 427799) (by norm_num)
theorem B813137 : Blo 758332 813137 := bbase (se 2 (by rfl) ⟨304926, by rfl⟩ : syracuseStep 813137 = 609853) (by norm_num)
theorem B1140821 : Blo 758332 1140821 := bbase (se 8 (by rfl) ⟨6684, by rfl⟩ : syracuseStep 1140821 = 13369) (by norm_num)
theorem B1927253 : Blo 758332 1927253 := bbase (se 8 (by rfl) ⟨11292, by rfl⟩ : syracuseStep 1927253 = 22585) (by norm_num)
theorem B1140845 : Blo 758332 1140845 := bbase (se 3 (by rfl) ⟨213908, by rfl⟩ : syracuseStep 1140845 = 427817) (by norm_num)
theorem B1140869 : Blo 758332 1140869 := bbase (se 4 (by rfl) ⟨106956, by rfl⟩ : syracuseStep 1140869 = 213913) (by norm_num)
theorem B813197 : Blo 758332 813197 := bbase (se 3 (by rfl) ⟨152474, by rfl⟩ : syracuseStep 813197 = 304949) (by norm_num)
theorem B1140893 : Blo 758332 1140893 := bbase (se 3 (by rfl) ⟨213917, by rfl⟩ : syracuseStep 1140893 = 427835) (by norm_num)
theorem B1140917 : Blo 758332 1140917 := bbase (se 5 (by rfl) ⟨53480, by rfl⟩ : syracuseStep 1140917 = 106961) (by norm_num)
theorem B1140941 : Blo 758332 1140941 := bbase (se 3 (by rfl) ⟨213926, by rfl⟩ : syracuseStep 1140941 = 427853) (by norm_num)
theorem B1140965 : Blo 758332 1140965 := bbase (se 4 (by rfl) ⟨106965, by rfl⟩ : syracuseStep 1140965 = 213931) (by norm_num)
theorem B1140989 : Blo 758332 1140989 := bbase (se 3 (by rfl) ⟨213935, by rfl⟩ : syracuseStep 1140989 = 427871) (by norm_num)
theorem B813325 : Blo 758332 813325 := bbase (se 3 (by rfl) ⟨152498, by rfl⟩ : syracuseStep 813325 = 304997) (by norm_num)
theorem B1141013 : Blo 758332 1141013 := bbase (se 6 (by rfl) ⟨26742, by rfl⟩ : syracuseStep 1141013 = 53485) (by norm_num)
theorem B1141037 : Blo 758332 1141037 := bbase (se 3 (by rfl) ⟨213944, by rfl⟩ : syracuseStep 1141037 = 427889) (by norm_num)
theorem B1141061 : Blo 758332 1141061 := bbase (se 4 (by rfl) ⟨106974, by rfl⟩ : syracuseStep 1141061 = 213949) (by norm_num)
theorem B1141085 : Blo 758332 1141085 := bbase (se 3 (by rfl) ⟨213953, by rfl⟩ : syracuseStep 1141085 = 427907) (by norm_num)
theorem B1829213 : Blo 758332 1829213 := bbase (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) (by norm_num)
theorem B1141109 : Blo 758332 1141109 := bbase (se 5 (by rfl) ⟨53489, by rfl⟩ : syracuseStep 1141109 = 106979) (by norm_num)
theorem B1141133 : Blo 758332 1141133 := bbase (se 3 (by rfl) ⟨213962, by rfl⟩ : syracuseStep 1141133 = 427925) (by norm_num)
theorem B1141157 : Blo 758332 1141157 := bbase (se 4 (by rfl) ⟨106983, by rfl⟩ : syracuseStep 1141157 = 213967) (by norm_num)
theorem B1927597 : Blo 758332 1927597 := bbase (se 3 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 1927597 = 722849) (by norm_num)
theorem B1141181 : Blo 758332 1141181 := bbase (se 3 (by rfl) ⟨213971, by rfl⟩ : syracuseStep 1141181 = 427943) (by norm_num)
theorem B1141205 : Blo 758332 1141205 := bbase (se 7 (by rfl) ⟨13373, by rfl⟩ : syracuseStep 1141205 = 26747) (by norm_num)
theorem B1141229 : Blo 758332 1141229 := bbase (se 3 (by rfl) ⟨213980, by rfl⟩ : syracuseStep 1141229 = 427961) (by norm_num)
theorem B6941173 : Blo 758332 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B1141253 : Blo 758332 1141253 := bbase (se 4 (by rfl) ⟨106992, by rfl⟩ : syracuseStep 1141253 = 213985) (by norm_num)
theorem B1141277 : Blo 758332 1141277 := bbase (se 3 (by rfl) ⟨213989, by rfl⟩ : syracuseStep 1141277 = 427979) (by norm_num)
theorem B1829405 : Blo 758332 1829405 := bbase (se 3 (by rfl) ⟨343013, by rfl⟩ : syracuseStep 1829405 = 686027) (by norm_num)
theorem B1927709 : Blo 758332 1927709 := bbase (se 3 (by rfl) ⟨361445, by rfl⟩ : syracuseStep 1927709 = 722891) (by norm_num)
theorem B1141301 : Blo 758332 1141301 := bbase (se 5 (by rfl) ⟨53498, by rfl⟩ : syracuseStep 1141301 = 106997) (by norm_num)
theorem B1141325 : Blo 758332 1141325 := bbase (se 3 (by rfl) ⟨213998, by rfl⟩ : syracuseStep 1141325 = 427997) (by norm_num)
theorem B1141349 : Blo 758332 1141349 := bbase (se 4 (by rfl) ⟨107001, by rfl⟩ : syracuseStep 1141349 = 214003) (by norm_num)
theorem B1141373 : Blo 758332 1141373 := bbase (se 3 (by rfl) ⟨214007, by rfl⟩ : syracuseStep 1141373 = 428015) (by norm_num)
theorem B977545 : Blo 758332 977545 := bbase (se 2 (by rfl) ⟨366579, by rfl⟩ : syracuseStep 977545 = 733159) (by norm_num)
theorem B1141397 : Blo 758332 1141397 := bbase (se 6 (by rfl) ⟨26751, by rfl⟩ : syracuseStep 1141397 = 53503) (by norm_num)
theorem B1141421 : Blo 758332 1141421 := bbase (se 3 (by rfl) ⟨214016, by rfl⟩ : syracuseStep 1141421 = 428033) (by norm_num)
theorem B1141445 : Blo 758332 1141445 := bbase (se 4 (by rfl) ⟨107010, by rfl⟩ : syracuseStep 1141445 = 214021) (by norm_num)
theorem B813769 : Blo 758332 813769 := bbase (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) (by norm_num)
theorem B1141469 : Blo 758332 1141469 := bbase (se 3 (by rfl) ⟨214025, by rfl⟩ : syracuseStep 1141469 = 428051) (by norm_num)
theorem B1927901 : Blo 758332 1927901 := bbase (se 3 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 1927901 = 722963) (by norm_num)
theorem B2190053 : Blo 758332 2190053 := bbase (se 4 (by rfl) ⟨205317, by rfl⟩ : syracuseStep 2190053 = 410635) (by norm_num)
theorem B1141493 : Blo 758332 1141493 := bbase (se 5 (by rfl) ⟨53507, by rfl⟩ : syracuseStep 1141493 = 107015) (by norm_num)
theorem B1141517 : Blo 758332 1141517 := bbase (se 3 (by rfl) ⟨214034, by rfl⟩ : syracuseStep 1141517 = 428069) (by norm_num)
theorem B1141541 : Blo 758332 1141541 := bbase (se 4 (by rfl) ⟨107019, by rfl⟩ : syracuseStep 1141541 = 214039) (by norm_num)
theorem B1141565 : Blo 758332 1141565 := bbase (se 3 (by rfl) ⟨214043, by rfl⟩ : syracuseStep 1141565 = 428087) (by norm_num)
theorem B813889 : Blo 758332 813889 := bbase (se 2 (by rfl) ⟨305208, by rfl⟩ : syracuseStep 813889 = 610417) (by norm_num)
theorem B1141589 : Blo 758332 1141589 := bbase (se 9 (by rfl) ⟨3344, by rfl⟩ : syracuseStep 1141589 = 6689) (by norm_num)
theorem B1141613 : Blo 758332 1141613 := bbase (se 3 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 1141613 = 428105) (by norm_num)
theorem B1141637 : Blo 758332 1141637 := bbase (se 4 (by rfl) ⟨107028, by rfl⟩ : syracuseStep 1141637 = 214057) (by norm_num)
theorem B1141661 : Blo 758332 1141661 := bbase (se 3 (by rfl) ⟨214061, by rfl⟩ : syracuseStep 1141661 = 428123) (by norm_num)
theorem B1141685 : Blo 758332 1141685 := bbase (se 5 (by rfl) ⟨53516, by rfl⟩ : syracuseStep 1141685 = 107033) (by norm_num)
theorem B1141709 : Blo 758332 1141709 := bbase (se 3 (by rfl) ⟨214070, by rfl⟩ : syracuseStep 1141709 = 428141) (by norm_num)
theorem B1141733 : Blo 758332 1141733 := bbase (se 4 (by rfl) ⟨107037, by rfl⟩ : syracuseStep 1141733 = 214075) (by norm_num)
theorem B1141757 : Blo 758332 1141757 := bbase (se 3 (by rfl) ⟨214079, by rfl⟩ : syracuseStep 1141757 = 428159) (by norm_num)
theorem B1141781 : Blo 758332 1141781 := bbase (se 6 (by rfl) ⟨26760, by rfl⟩ : syracuseStep 1141781 = 53521) (by norm_num)
theorem B1141805 : Blo 758332 1141805 := bbase (se 3 (by rfl) ⟨214088, by rfl⟩ : syracuseStep 1141805 = 428177) (by norm_num)
theorem B1928245 : Blo 758332 1928245 := bbase (se 5 (by rfl) ⟨90386, by rfl⟩ : syracuseStep 1928245 = 180773) (by norm_num)
theorem B1141829 : Blo 758332 1141829 := bbase (se 4 (by rfl) ⟨107046, by rfl⟩ : syracuseStep 1141829 = 214093) (by norm_num)
theorem B1141853 : Blo 758332 1141853 := bbase (se 3 (by rfl) ⟨214097, by rfl⟩ : syracuseStep 1141853 = 428195) (by norm_num)
theorem B1141877 : Blo 758332 1141877 := bbase (se 5 (by rfl) ⟨53525, by rfl⟩ : syracuseStep 1141877 = 107051) (by norm_num)
theorem B1141901 : Blo 758332 1141901 := bbase (se 3 (by rfl) ⟨214106, by rfl⟩ : syracuseStep 1141901 = 428213) (by norm_num)
theorem B4942997 : Blo 758332 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B1141925 : Blo 758332 1141925 := bbase (se 4 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 1141925 = 214111) (by norm_num)
theorem B1928357 : Blo 758332 1928357 := bbase (se 4 (by rfl) ⟨180783, by rfl⟩ : syracuseStep 1928357 = 361567) (by norm_num)
theorem B1141949 : Blo 758332 1141949 := bbase (se 3 (by rfl) ⟨214115, by rfl⟩ : syracuseStep 1141949 = 428231) (by norm_num)
theorem B1141973 : Blo 758332 1141973 := bbase (se 7 (by rfl) ⟨13382, by rfl⟩ : syracuseStep 1141973 = 26765) (by norm_num)
theorem B1141997 : Blo 758332 1141997 := bbase (se 3 (by rfl) ⟨214124, by rfl⟩ : syracuseStep 1141997 = 428249) (by norm_num)
theorem B3075317 : Blo 758332 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B1142021 : Blo 758332 1142021 := bbase (se 4 (by rfl) ⟨107064, by rfl⟩ : syracuseStep 1142021 = 214129) (by norm_num)
theorem B1142045 : Blo 758332 1142045 := bbase (se 3 (by rfl) ⟨214133, by rfl⟩ : syracuseStep 1142045 = 428267) (by norm_num)
theorem B1142069 : Blo 758332 1142069 := bbase (se 5 (by rfl) ⟨53534, by rfl⟩ : syracuseStep 1142069 = 107069) (by norm_num)
theorem B1142093 : Blo 758332 1142093 := bbase (se 3 (by rfl) ⟨214142, by rfl⟩ : syracuseStep 1142093 = 428285) (by norm_num)
theorem B1142117 : Blo 758332 1142117 := bbase (se 4 (by rfl) ⟨107073, by rfl⟩ : syracuseStep 1142117 = 214147) (by norm_num)
theorem B1928549 : Blo 758332 1928549 := bbase (se 4 (by rfl) ⟨180801, by rfl⟩ : syracuseStep 1928549 = 361603) (by norm_num)
theorem B1142141 : Blo 758332 1142141 := bbase (se 3 (by rfl) ⟨214151, by rfl⟩ : syracuseStep 1142141 = 428303) (by norm_num)
theorem B1142165 : Blo 758332 1142165 := bbase (se 6 (by rfl) ⟨26769, by rfl⟩ : syracuseStep 1142165 = 53539) (by norm_num)
theorem B1371557 : Blo 758332 1371557 := bbase (se 4 (by rfl) ⟨128583, by rfl⟩ : syracuseStep 1371557 = 257167) (by norm_num)
theorem B1142189 : Blo 758332 1142189 := bbase (se 3 (by rfl) ⟨214160, by rfl⟩ : syracuseStep 1142189 = 428321) (by norm_num)
theorem B1142213 : Blo 758332 1142213 := bbase (se 4 (by rfl) ⟨107082, by rfl⟩ : syracuseStep 1142213 = 214165) (by norm_num)
theorem B1142237 : Blo 758332 1142237 := bbase (se 3 (by rfl) ⟨214169, by rfl⟩ : syracuseStep 1142237 = 428339) (by norm_num)
theorem B1142261 : Blo 758332 1142261 := bbase (se 5 (by rfl) ⟨53543, by rfl⟩ : syracuseStep 1142261 = 107087) (by norm_num)
theorem B1142285 : Blo 758332 1142285 := bbase (se 3 (by rfl) ⟨214178, by rfl⟩ : syracuseStep 1142285 = 428357) (by norm_num)
theorem B1142309 : Blo 758332 1142309 := bbase (se 4 (by rfl) ⟨107091, by rfl⟩ : syracuseStep 1142309 = 214183) (by norm_num)
theorem B912953 : Blo 758332 912953 := bbase (se 2 (by rfl) ⟨342357, by rfl⟩ : syracuseStep 912953 = 684715) (by norm_num)
theorem B1142333 : Blo 758332 1142333 := bbase (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) (by norm_num)
theorem B1142357 : Blo 758332 1142357 := bbase (se 8 (by rfl) ⟨6693, by rfl⟩ : syracuseStep 1142357 = 13387) (by norm_num)
theorem B1142381 : Blo 758332 1142381 := bbase (se 3 (by rfl) ⟨214196, by rfl⟩ : syracuseStep 1142381 = 428393) (by norm_num)
theorem B1142405 : Blo 758332 1142405 := bbase (se 4 (by rfl) ⟨107100, by rfl⟩ : syracuseStep 1142405 = 214201) (by norm_num)
theorem B1142429 : Blo 758332 1142429 := bbase (se 3 (by rfl) ⟨214205, by rfl⟩ : syracuseStep 1142429 = 428411) (by norm_num)
theorem B913069 : Blo 758332 913069 := bbase (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) (by norm_num)
theorem B1142453 : Blo 758332 1142453 := bbase (se 5 (by rfl) ⟨53552, by rfl⟩ : syracuseStep 1142453 = 107105) (by norm_num)
theorem B1928893 : Blo 758332 1928893 := bbase (se 3 (by rfl) ⟨361667, by rfl⟩ : syracuseStep 1928893 = 723335) (by norm_num)
theorem B1142477 : Blo 758332 1142477 := bbase (se 3 (by rfl) ⟨214214, by rfl⟩ : syracuseStep 1142477 = 428429) (by norm_num)
theorem B1142501 : Blo 758332 1142501 := bbase (se 4 (by rfl) ⟨107109, by rfl⟩ : syracuseStep 1142501 = 214219) (by norm_num)
theorem B913141 : Blo 758332 913141 := bbase (se 5 (by rfl) ⟨42803, by rfl⟩ : syracuseStep 913141 = 85607) (by norm_num)
theorem B1142525 : Blo 758332 1142525 := bbase (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) (by norm_num)
theorem B1142549 : Blo 758332 1142549 := bbase (se 6 (by rfl) ⟨26778, by rfl⟩ : syracuseStep 1142549 = 53557) (by norm_num)
theorem B1142573 : Blo 758332 1142573 := bbase (se 3 (by rfl) ⟨214232, by rfl⟩ : syracuseStep 1142573 = 428465) (by norm_num)
theorem B1929005 : Blo 758332 1929005 := bbase (se 3 (by rfl) ⟨361688, by rfl⟩ : syracuseStep 1929005 = 723377) (by norm_num)
theorem B1142597 : Blo 758332 1142597 := bbase (se 4 (by rfl) ⟨107118, by rfl⟩ : syracuseStep 1142597 = 214237) (by norm_num)
theorem B19459925 : Blo 758332 19459925 := bbase (se 9 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 19459925 = 114023) (by norm_num)
theorem B1142621 : Blo 758332 1142621 := bbase (se 3 (by rfl) ⟨214241, by rfl⟩ : syracuseStep 1142621 = 428483) (by norm_num)
theorem B913261 : Blo 758332 913261 := bbase (se 3 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 913261 = 342473) (by norm_num)
theorem B1142645 : Blo 758332 1142645 := bbase (se 5 (by rfl) ⟨53561, by rfl⟩ : syracuseStep 1142645 = 107123) (by norm_num)
theorem B1142669 : Blo 758332 1142669 := bbase (se 3 (by rfl) ⟨214250, by rfl⟩ : syracuseStep 1142669 = 428501) (by norm_num)
theorem B1142693 : Blo 758332 1142693 := bbase (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) (by norm_num)
theorem B1142717 : Blo 758332 1142717 := bbase (se 3 (by rfl) ⟨214259, by rfl⟩ : syracuseStep 1142717 = 428519) (by norm_num)
theorem B1142741 : Blo 758332 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B1142765 : Blo 758332 1142765 := bbase (se 3 (by rfl) ⟨214268, by rfl⟩ : syracuseStep 1142765 = 428537) (by norm_num)
theorem B1929197 : Blo 758332 1929197 := bbase (se 3 (by rfl) ⟨361724, by rfl⟩ : syracuseStep 1929197 = 723449) (by norm_num)
theorem B1142789 : Blo 758332 1142789 := bbase (se 4 (by rfl) ⟨107136, by rfl⟩ : syracuseStep 1142789 = 214273) (by norm_num)
theorem B2060309 : Blo 758332 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B1142813 : Blo 758332 1142813 := bbase (se 3 (by rfl) ⟨214277, by rfl⟩ : syracuseStep 1142813 = 428555) (by norm_num)
theorem B1142837 : Blo 758332 1142837 := bbase (se 5 (by rfl) ⟨53570, by rfl⟩ : syracuseStep 1142837 = 107141) (by norm_num)
theorem B1142861 : Blo 758332 1142861 := bbase (se 3 (by rfl) ⟨214286, by rfl⟩ : syracuseStep 1142861 = 428573) (by norm_num)
theorem B1142885 : Blo 758332 1142885 := bbase (se 4 (by rfl) ⟨107145, by rfl⟩ : syracuseStep 1142885 = 214291) (by norm_num)
theorem B1142909 : Blo 758332 1142909 := bbase (se 3 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 1142909 = 428591) (by norm_num)
theorem B1142933 : Blo 758332 1142933 := bbase (se 6 (by rfl) ⟨26787, by rfl⟩ : syracuseStep 1142933 = 53575) (by norm_num)
theorem B1142957 : Blo 758332 1142957 := bbase (se 3 (by rfl) ⟨214304, by rfl⟩ : syracuseStep 1142957 = 428609) (by norm_num)
theorem B1142981 : Blo 758332 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B1143005 : Blo 758332 1143005 := bbase (se 3 (by rfl) ⟨214313, by rfl⟩ : syracuseStep 1143005 = 428627) (by norm_num)
theorem B913645 : Blo 758332 913645 := bbase (se 3 (by rfl) ⟨171308, by rfl⟩ : syracuseStep 913645 = 342617) (by norm_num)
theorem B1143029 : Blo 758332 1143029 := bbase (se 5 (by rfl) ⟨53579, by rfl⟩ : syracuseStep 1143029 = 107159) (by norm_num)
theorem B1143053 : Blo 758332 1143053 := bbase (se 3 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 1143053 = 428645) (by norm_num)
theorem B1143077 : Blo 758332 1143077 := bbase (se 4 (by rfl) ⟨107163, by rfl⟩ : syracuseStep 1143077 = 214327) (by norm_num)
theorem B1143101 : Blo 758332 1143101 := bbase (se 3 (by rfl) ⟨214331, by rfl⟩ : syracuseStep 1143101 = 428663) (by norm_num)
theorem B1929541 : Blo 758332 1929541 := bbase (se 4 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 1929541 = 361789) (by norm_num)
theorem B1143125 : Blo 758332 1143125 := bbase (se 10 (by rfl) ⟨1674, by rfl⟩ : syracuseStep 1143125 = 3349) (by norm_num)
theorem B1143149 : Blo 758332 1143149 := bbase (se 3 (by rfl) ⟨214340, by rfl⟩ : syracuseStep 1143149 = 428681) (by norm_num)
theorem B1143173 : Blo 758332 1143173 := bbase (se 4 (by rfl) ⟨107172, by rfl⟩ : syracuseStep 1143173 = 214345) (by norm_num)
theorem B1143197 : Blo 758332 1143197 := bbase (se 3 (by rfl) ⟨214349, by rfl⟩ : syracuseStep 1143197 = 428699) (by norm_num)
theorem B1143221 : Blo 758332 1143221 := bbase (se 5 (by rfl) ⟨53588, by rfl⟩ : syracuseStep 1143221 = 107177) (by norm_num)
theorem B1929653 : Blo 758332 1929653 := bbase (se 5 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 1929653 = 180905) (by norm_num)
theorem B1143245 : Blo 758332 1143245 := bbase (se 3 (by rfl) ⟨214358, by rfl⟩ : syracuseStep 1143245 = 428717) (by norm_num)
theorem B1143269 : Blo 758332 1143269 := bbase (se 4 (by rfl) ⟨107181, by rfl⟩ : syracuseStep 1143269 = 214363) (by norm_num)
theorem B1143293 : Blo 758332 1143293 := bbase (se 3 (by rfl) ⟨214367, by rfl⟩ : syracuseStep 1143293 = 428735) (by norm_num)
theorem B1143317 : Blo 758332 1143317 := bbase (se 6 (by rfl) ⟨26796, by rfl⟩ : syracuseStep 1143317 = 53593) (by norm_num)
theorem B1372717 : Blo 758332 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B1143341 : Blo 758332 1143341 := bbase (se 3 (by rfl) ⟨214376, by rfl⟩ : syracuseStep 1143341 = 428753) (by norm_num)
theorem B3076661 : Blo 758332 3076661 := bbase (se 5 (by rfl) ⟨144218, by rfl⟩ : syracuseStep 3076661 = 288437) (by norm_num)
theorem B1143365 : Blo 758332 1143365 := bbase (se 4 (by rfl) ⟨107190, by rfl⟩ : syracuseStep 1143365 = 214381) (by norm_num)
theorem B1143389 : Blo 758332 1143389 := bbase (se 3 (by rfl) ⟨214385, by rfl⟩ : syracuseStep 1143389 = 428771) (by norm_num)
theorem B1143413 : Blo 758332 1143413 := bbase (se 5 (by rfl) ⟨53597, by rfl⟩ : syracuseStep 1143413 = 107195) (by norm_num)
theorem B1143437 : Blo 758332 1143437 := bbase (se 3 (by rfl) ⟨214394, by rfl⟩ : syracuseStep 1143437 = 428789) (by norm_num)
theorem B1143461 : Blo 758332 1143461 := bbase (se 4 (by rfl) ⟨107199, by rfl⟩ : syracuseStep 1143461 = 214399) (by norm_num)
theorem B1143485 : Blo 758332 1143485 := bbase (se 3 (by rfl) ⟨214403, by rfl⟩ : syracuseStep 1143485 = 428807) (by norm_num)
theorem B5206837 : Blo 758332 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1373021 : Blo 758332 1373021 := bbase (se 3 (by rfl) ⟨257441, by rfl⟩ : syracuseStep 1373021 = 514883) (by norm_num)
theorem B914333 : Blo 758332 914333 := bbase (se 3 (by rfl) ⟨171437, by rfl⟩ : syracuseStep 914333 = 342875) (by norm_num)
theorem B1733557 : Blo 758332 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B1110997 : Blo 758332 1110997 := bbase (se 7 (by rfl) ⟨13019, by rfl⟩ : syracuseStep 1110997 = 26039) (by norm_num)
theorem B2880629 : Blo 758332 2880629 := bbase (se 5 (by rfl) ⟨135029, by rfl⟩ : syracuseStep 2880629 = 270059) (by norm_num)
theorem B2880917 : Blo 758332 2880917 := bbase (se 6 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 2880917 = 135043) (by norm_num)
theorem B1734061 : Blo 758332 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B914933 : Blo 758332 914933 := bbase (se 5 (by rfl) ⟨42887, by rfl⟩ : syracuseStep 914933 = 85775) (by norm_num)
theorem B1734173 : Blo 758332 1734173 := bbase (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) (by norm_num)
theorem B915241 : Blo 758332 915241 := bbase (se 2 (by rfl) ⟨343215, by rfl⟩ : syracuseStep 915241 = 686431) (by norm_num)
theorem B3471173 : Blo 758332 3471173 := bbase (se 4 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 3471173 = 650845) (by norm_num)
theorem B915337 : Blo 758332 915337 := bbase (se 2 (by rfl) ⟨343251, by rfl⟩ : syracuseStep 915337 = 686503) (by norm_num)
theorem B4618133 : Blo 758332 4618133 := bbase (se 6 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 4618133 = 216475) (by norm_num)
theorem B1439669 : Blo 758332 1439669 := bbase (se 5 (by rfl) ⟨67484, by rfl⟩ : syracuseStep 1439669 = 134969) (by norm_num)
theorem B915385 : Blo 758332 915385 := bbase (se 2 (by rfl) ⟨343269, by rfl⟩ : syracuseStep 915385 = 686539) (by norm_num)
theorem B1439957 : Blo 758332 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B3242213 : Blo 758332 3242213 := bbase (se 4 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 3242213 = 607915) (by norm_num)
theorem B1440109 : Blo 758332 1440109 := bbase (se 3 (by rfl) ⟨270020, by rfl⟩ : syracuseStep 1440109 = 540041) (by norm_num)
theorem B1538461 : Blo 758332 1538461 := bbase (se 3 (by rfl) ⟨288461, by rfl⟩ : syracuseStep 1538461 = 576923) (by norm_num)
theorem B1735157 : Blo 758332 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B7043573 : Blo 758332 7043573 := bbase (se 5 (by rfl) ⟨330167, by rfl⟩ : syracuseStep 7043573 = 660335) (by norm_num)
theorem B3242501 : Blo 758332 3242501 := bbase (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) (by norm_num)
theorem B2882101 : Blo 758332 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B1440413 : Blo 758332 1440413 := bbase (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) (by norm_num)
theorem B2161349 : Blo 758332 2161349 := bbase (se 4 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 2161349 = 405253) (by norm_num)
theorem B2882405 : Blo 758332 2882405 := bbase (se 4 (by rfl) ⟨270225, by rfl⟩ : syracuseStep 2882405 = 540451) (by norm_num)
theorem B1080173 : Blo 758332 1080173 := bbase (se 3 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 1080173 = 405065) (by norm_num)
theorem B8682389 : Blo 758332 8682389 := bbase (se 6 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 8682389 = 406987) (by norm_num)
theorem B1080253 : Blo 758332 1080253 := bbase (se 3 (by rfl) ⟨202547, by rfl⟩ : syracuseStep 1080253 = 405095) (by norm_num)
theorem B1080373 : Blo 758332 1080373 := bbase (se 5 (by rfl) ⟨50642, by rfl⟩ : syracuseStep 1080373 = 101285) (by norm_num)
theorem B1539181 : Blo 758332 1539181 := bbase (se 3 (by rfl) ⟨288596, by rfl⟩ : syracuseStep 1539181 = 577193) (by norm_num)
theorem B1080469 : Blo 758332 1080469 := bbase (se 6 (by rfl) ⟨25323, by rfl⟩ : syracuseStep 1080469 = 50647) (by norm_num)
theorem B3243253 : Blo 758332 3243253 := bbase (se 5 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 3243253 = 304055) (by norm_num)
theorem B5766389 : Blo 758332 5766389 := bbase (se 5 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 5766389 = 540599) (by norm_num)
theorem B1441165 : Blo 758332 1441165 := bbase (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) (by norm_num)
theorem B3898853 : Blo 758332 3898853 := bbase (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) (by norm_num)
theorem B1441309 : Blo 758332 1441309 := bbase (se 3 (by rfl) ⟨270245, by rfl⟩ : syracuseStep 1441309 = 540491) (by norm_num)
theorem B1080965 : Blo 758332 1080965 := bbase (se 4 (by rfl) ⟨101340, by rfl⟩ : syracuseStep 1080965 = 202681) (by norm_num)
theorem B12025493 : Blo 758332 12025493 := bbase (se 6 (by rfl) ⟨281847, by rfl⟩ : syracuseStep 12025493 = 563695) (by norm_num)
theorem B1441469 : Blo 758332 1441469 := bbase (se 3 (by rfl) ⟨270275, by rfl⟩ : syracuseStep 1441469 = 540551) (by norm_num)
theorem B1736461 : Blo 758332 1736461 := bbase (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) (by norm_num)
theorem B1441613 : Blo 758332 1441613 := bbase (se 3 (by rfl) ⟨270302, by rfl⟩ : syracuseStep 1441613 = 540605) (by norm_num)
theorem B3702613 : Blo 758332 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B2162533 : Blo 758332 2162533 := bbase (se 4 (by rfl) ⟨202737, by rfl⟩ : syracuseStep 2162533 = 405475) (by norm_num)
theorem B3243989 : Blo 758332 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B1441795 : Blo 758332 1441795 := bstep (se 1 (by rfl) ⟨1081346, by rfl⟩ : syracuseStep 1441795 = 2162693) B2162693
theorem B8781965 : Blo 758332 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B1441955 : Blo 758332 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B1081603 : Blo 758332 1081603 := bstep (se 1 (by rfl) ⟨811202, by rfl⟩ : syracuseStep 1081603 = 1622405) B1622405
theorem B4325795 : Blo 758332 4325795 := bstep (se 1 (by rfl) ⟨3244346, by rfl⟩ : syracuseStep 4325795 = 6488693) B6488693
theorem B2884045 : Blo 758332 2884045 := bstep (se 3 (by rfl) ⟨540758, by rfl⟩ : syracuseStep 2884045 = 1081517) B1081517
theorem B2163149 : Blo 758332 2163149 := bstep (se 3 (by rfl) ⟨405590, by rfl⟩ : syracuseStep 2163149 = 811181) B811181
theorem B1540561 : Blo 758332 1540561 := bstep (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) B1155421
theorem B1081939 : Blo 758332 1081939 := bstep (se 1 (by rfl) ⟨811454, by rfl⟩ : syracuseStep 1081939 = 1622909) B1622909
theorem B3081073 : Blo 758332 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B49873805 : Blo 758332 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B1082497 : Blo 758332 1082497 := bstep (se 2 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 1082497 = 811873) B811873
theorem B5768333 : Blo 758332 5768333 := bstep (se 3 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 5768333 = 2163125) B2163125
theorem B1082531 : Blo 758332 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B1443025 : Blo 758332 1443025 := bstep (se 2 (by rfl) ⟨541134, by rfl⟩ : syracuseStep 1443025 = 1082269) B1082269
theorem B2884835 : Blo 758332 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B853267 : Blo 758332 853267 := bstep (se 1 (by rfl) ⟨639950, by rfl⟩ : syracuseStep 853267 = 1279901) B1279901
theorem B16647565 : Blo 758332 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B4326797 : Blo 758332 4326797 := bstep (se 3 (by rfl) ⟨811274, by rfl⟩ : syracuseStep 4326797 = 1622549) B1622549
theorem B853411 : Blo 758332 853411 := bstep (se 1 (by rfl) ⟨640058, by rfl⟩ : syracuseStep 853411 = 1280117) B1280117
theorem B853555 : Blo 758332 853555 := bstep (se 1 (by rfl) ⟨640166, by rfl⟩ : syracuseStep 853555 = 1280333) B1280333
theorem B3245645 : Blo 758332 3245645 := bstep (se 3 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 3245645 = 1217117) B1217117
theorem B2164333 : Blo 758332 2164333 := bstep (se 3 (by rfl) ⟨405812, by rfl⟩ : syracuseStep 2164333 = 811625) B811625
theorem B853699 : Blo 758332 853699 := bstep (se 1 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 853699 = 1280549) B1280549
theorem B1083089 : Blo 758332 1083089 := bstep (se 2 (by rfl) ⟨406158, by rfl⟩ : syracuseStep 1083089 = 812317) B812317
theorem B1738513 : Blo 758332 1738513 := bstep (se 2 (by rfl) ⟨651942, by rfl⟩ : syracuseStep 1738513 = 1303885) B1303885
theorem B1083169 : Blo 758332 1083169 := bstep (se 2 (by rfl) ⟨406188, by rfl⟩ : syracuseStep 1083169 = 812377) B812377
theorem B1279793 : Blo 758332 1279793 := bstep (se 2 (by rfl) ⟨479922, by rfl⟩ : syracuseStep 1279793 = 959845) B959845
theorem B853843 : Blo 758332 853843 := bstep (se 1 (by rfl) ⟨640382, by rfl⟩ : syracuseStep 853843 = 1280765) B1280765
theorem B2885489 : Blo 758332 2885489 := bstep (se 2 (by rfl) ⟨1082058, by rfl⟩ : syracuseStep 2885489 = 2164117) B2164117
theorem B3245987 : Blo 758332 3245987 := bstep (se 1 (by rfl) ⟨2434490, by rfl⟩ : syracuseStep 3245987 = 4868981) B4868981
theorem B1279921 : Blo 758332 1279921 := bstep (se 2 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 1279921 = 959941) B959941
theorem B1279955 : Blo 758332 1279955 := bstep (se 1 (by rfl) ⟨959966, by rfl⟩ : syracuseStep 1279955 = 1919933) B1919933
theorem B853987 : Blo 758332 853987 := bstep (se 1 (by rfl) ⟨640490, by rfl⟩ : syracuseStep 853987 = 1280981) B1280981
theorem B7112717 : Blo 758332 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B4950065 : Blo 758332 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B1280083 : Blo 758332 1280083 := bstep (se 1 (by rfl) ⟨960062, by rfl⟩ : syracuseStep 1280083 = 1920125) B1920125
theorem B854131 : Blo 758332 854131 := bstep (se 1 (by rfl) ⟨640598, by rfl⟩ : syracuseStep 854131 = 1281197) B1281197
theorem B1280225 : Blo 758332 1280225 := bstep (se 2 (by rfl) ⟨480084, by rfl⟩ : syracuseStep 1280225 = 960169) B960169
theorem B1444081 : Blo 758332 1444081 := bstep (se 2 (by rfl) ⟨541530, by rfl⟩ : syracuseStep 1444081 = 1083061) B1083061
theorem B854275 : Blo 758332 854275 := bstep (se 1 (by rfl) ⟨640706, by rfl⟩ : syracuseStep 854275 = 1281413) B1281413
theorem B1214785 : Blo 758332 1214785 := bstep (se 2 (by rfl) ⟨455544, by rfl⟩ : syracuseStep 1214785 = 911089) B911089
theorem B1280353 : Blo 758332 1280353 := bstep (se 2 (by rfl) ⟨480132, by rfl⟩ : syracuseStep 1280353 = 960265) B960265
theorem B1280387 : Blo 758332 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B854419 : Blo 758332 854419 := bstep (se 1 (by rfl) ⟨640814, by rfl⟩ : syracuseStep 854419 = 1281629) B1281629
theorem B1706417 : Blo 758332 1706417 := bstep (se 2 (by rfl) ⟨639906, by rfl⟩ : syracuseStep 1706417 = 1279813) B1279813
theorem B1706435 : Blo 758332 1706435 := bstep (se 1 (by rfl) ⟨1279826, by rfl⟩ : syracuseStep 1706435 = 2559653) B2559653
theorem B1280515 : Blo 758332 1280515 := bstep (se 1 (by rfl) ⟨960386, by rfl⟩ : syracuseStep 1280515 = 1920773) B1920773
theorem B2918947 : Blo 758332 2918947 := bstep (se 1 (by rfl) ⟨2189210, by rfl⟩ : syracuseStep 2918947 = 4378421) B4378421
theorem B854563 : Blo 758332 854563 := bstep (se 1 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 854563 = 1281845) B1281845
theorem B5016113 : Blo 758332 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B1083955 : Blo 758332 1083955 := bstep (se 1 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 1083955 = 1625933) B1625933
theorem B1444483 : Blo 758332 1444483 := bstep (se 1 (by rfl) ⟨1083362, by rfl⟩ : syracuseStep 1444483 = 2166725) B2166725
theorem B1280657 : Blo 758332 1280657 := bstep (se 2 (by rfl) ⟨480246, by rfl⟩ : syracuseStep 1280657 = 960493) B960493
theorem B2165393 : Blo 758332 2165393 := bstep (se 2 (by rfl) ⟨812022, by rfl⟩ : syracuseStep 2165393 = 1624045) B1624045
theorem B1444529 : Blo 758332 1444529 := bstep (se 2 (by rfl) ⟨541698, by rfl⟩ : syracuseStep 1444529 = 1083397) B1083397
theorem B854707 : Blo 758332 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B1706705 : Blo 758332 1706705 := bstep (se 2 (by rfl) ⟨640014, by rfl⟩ : syracuseStep 1706705 = 1280029) B1280029
theorem B1706723 : Blo 758332 1706723 := bstep (se 1 (by rfl) ⟨1280042, by rfl⟩ : syracuseStep 1706723 = 2560085) B2560085
theorem B1280785 : Blo 758332 1280785 := bstep (se 2 (by rfl) ⟨480294, by rfl⟩ : syracuseStep 1280785 = 960589) B960589
theorem B1280819 : Blo 758332 1280819 := bstep (se 1 (by rfl) ⟨960614, by rfl⟩ : syracuseStep 1280819 = 1921229) B1921229
theorem B854851 : Blo 758332 854851 := bstep (se 1 (by rfl) ⟨641138, by rfl⟩ : syracuseStep 854851 = 1282277) B1282277
theorem B1543043 : Blo 758332 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B1280947 : Blo 758332 1280947 := bstep (se 1 (by rfl) ⟨960710, by rfl⟩ : syracuseStep 1280947 = 1921421) B1921421
theorem B7048133 : Blo 758332 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B1444817 : Blo 758332 1444817 := bstep (se 2 (by rfl) ⟨541806, by rfl⟩ : syracuseStep 1444817 = 1083613) B1083613
theorem B854995 : Blo 758332 854995 := bstep (se 1 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 854995 = 1282493) B1282493
theorem B1706993 : Blo 758332 1706993 := bstep (se 2 (by rfl) ⟨640122, by rfl⟩ : syracuseStep 1706993 = 1280245) B1280245
theorem B1707011 : Blo 758332 1707011 := bstep (se 1 (by rfl) ⟨1280258, by rfl⟩ : syracuseStep 1707011 = 2560517) B2560517
theorem B1084433 : Blo 758332 1084433 := bstep (se 2 (by rfl) ⟨406662, by rfl⟩ : syracuseStep 1084433 = 813325) B813325
theorem B1281089 : Blo 758332 1281089 := bstep (se 2 (by rfl) ⟨480408, by rfl⟩ : syracuseStep 1281089 = 960817) B960817
theorem B855139 : Blo 758332 855139 := bstep (se 1 (by rfl) ⟨641354, by rfl⟩ : syracuseStep 855139 = 1282709) B1282709
theorem B1084547 : Blo 758332 1084547 := bstep (se 1 (by rfl) ⟨813410, by rfl⟩ : syracuseStep 1084547 = 1626821) B1626821
theorem B1281217 : Blo 758332 1281217 := bstep (se 2 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 1281217 = 960913) B960913
theorem B1084627 : Blo 758332 1084627 := bstep (se 1 (by rfl) ⟨813470, by rfl⟩ : syracuseStep 1084627 = 1626941) B1626941
theorem B1281251 : Blo 758332 1281251 := bstep (se 1 (by rfl) ⟨960938, by rfl⟩ : syracuseStep 1281251 = 1921877) B1921877
theorem B855283 : Blo 758332 855283 := bstep (se 1 (by rfl) ⟨641462, by rfl⟩ : syracuseStep 855283 = 1282925) B1282925
theorem B1707281 : Blo 758332 1707281 := bstep (se 2 (by rfl) ⟨640230, by rfl⟩ : syracuseStep 1707281 = 1280461) B1280461
theorem B1707299 : Blo 758332 1707299 := bstep (se 1 (by rfl) ⟨1280474, by rfl⟩ : syracuseStep 1707299 = 2560949) B2560949
theorem B2886947 : Blo 758332 2886947 := bstep (se 1 (by rfl) ⟨2165210, by rfl⟩ : syracuseStep 2886947 = 4330421) B4330421
theorem B2886961 : Blo 758332 2886961 := bstep (se 2 (by rfl) ⟨1082610, by rfl⟩ : syracuseStep 2886961 = 2165221) B2165221
theorem B2166065 : Blo 758332 2166065 := bstep (se 2 (by rfl) ⟨812274, by rfl⟩ : syracuseStep 2166065 = 1624549) B1624549
theorem B1281379 : Blo 758332 1281379 := bstep (se 1 (by rfl) ⟨961034, by rfl⟩ : syracuseStep 1281379 = 1922069) B1922069
theorem B855427 : Blo 758332 855427 := bstep (se 1 (by rfl) ⟨641570, by rfl⟩ : syracuseStep 855427 = 1283141) B1283141
theorem B2559437 : Blo 758332 2559437 := bstep (se 3 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 2559437 = 959789) B959789
theorem B1281521 : Blo 758332 1281521 := bstep (se 2 (by rfl) ⟨480570, by rfl⟩ : syracuseStep 1281521 = 961141) B961141
theorem B2559491 : Blo 758332 2559491 := bstep (se 1 (by rfl) ⟨1919618, by rfl⟩ : syracuseStep 2559491 = 3839237) B3839237
theorem B855571 : Blo 758332 855571 := bstep (se 1 (by rfl) ⟨641678, by rfl⟩ : syracuseStep 855571 = 1283357) B1283357
theorem B1707569 : Blo 758332 1707569 := bstep (se 2 (by rfl) ⟨640338, by rfl⟩ : syracuseStep 1707569 = 1280677) B1280677
theorem B1707587 : Blo 758332 1707587 := bstep (se 1 (by rfl) ⟨1280690, by rfl⟩ : syracuseStep 1707587 = 2561381) B2561381
theorem B1281649 : Blo 758332 1281649 := bstep (se 2 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 1281649 = 961237) B961237
theorem B1281683 : Blo 758332 1281683 := bstep (se 1 (by rfl) ⟨961262, by rfl⟩ : syracuseStep 1281683 = 1922525) B1922525
theorem B855715 : Blo 758332 855715 := bstep (se 1 (by rfl) ⟨641786, by rfl⟩ : syracuseStep 855715 = 1283573) B1283573
theorem B1445539 : Blo 758332 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B1085185 : Blo 758332 1085185 := bstep (se 2 (by rfl) ⟨406944, by rfl⟩ : syracuseStep 1085185 = 813889) B813889
theorem B2559761 : Blo 758332 2559761 := bstep (se 2 (by rfl) ⟨959910, by rfl⟩ : syracuseStep 2559761 = 1919821) B1919821
theorem B1281811 : Blo 758332 1281811 := bstep (se 1 (by rfl) ⟨961358, by rfl⟩ : syracuseStep 1281811 = 1922717) B1922717
theorem B1216291 : Blo 758332 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B855859 : Blo 758332 855859 := bstep (se 1 (by rfl) ⟨641894, by rfl⟩ : syracuseStep 855859 = 1283789) B1283789
theorem B1707857 : Blo 758332 1707857 := bstep (se 2 (by rfl) ⟨640446, by rfl⟩ : syracuseStep 1707857 = 1280893) B1280893
theorem B1707875 : Blo 758332 1707875 := bstep (se 1 (by rfl) ⟨1280906, by rfl⟩ : syracuseStep 1707875 = 2561813) B2561813
theorem B1281953 : Blo 758332 1281953 := bstep (se 2 (by rfl) ⟨480732, by rfl⟩ : syracuseStep 1281953 = 961465) B961465
theorem B1642403 : Blo 758332 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B1544113 : Blo 758332 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B856003 : Blo 758332 856003 := bstep (se 1 (by rfl) ⟨642002, by rfl⟩ : syracuseStep 856003 = 1284005) B1284005
theorem B5771249 : Blo 758332 5771249 := bstep (se 2 (by rfl) ⟨2164218, by rfl⟩ : syracuseStep 5771249 = 4328437) B4328437
theorem B1282081 : Blo 758332 1282081 := bstep (se 2 (by rfl) ⟨480780, by rfl⟩ : syracuseStep 1282081 = 961561) B961561
theorem B1282115 : Blo 758332 1282115 := bstep (se 1 (by rfl) ⟨961586, by rfl⟩ : syracuseStep 1282115 = 1923173) B1923173
theorem B2166851 : Blo 758332 2166851 := bstep (se 1 (by rfl) ⟨1625138, by rfl⟩ : syracuseStep 2166851 = 3250277) B3250277
theorem B856147 : Blo 758332 856147 := bstep (se 1 (by rfl) ⟨642110, by rfl⟩ : syracuseStep 856147 = 1284221) B1284221
theorem B1445987 : Blo 758332 1445987 := bstep (se 1 (by rfl) ⟨1084490, by rfl⟩ : syracuseStep 1445987 = 2168981) B2168981
theorem B1708145 : Blo 758332 1708145 := bstep (se 2 (by rfl) ⟨640554, by rfl⟩ : syracuseStep 1708145 = 1281109) B1281109
theorem B1708163 : Blo 758332 1708163 := bstep (se 1 (by rfl) ⟨1281122, by rfl⟩ : syracuseStep 1708163 = 2562245) B2562245
theorem B1282243 : Blo 758332 1282243 := bstep (se 1 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 1282243 = 1923365) B1923365
theorem B856291 : Blo 758332 856291 := bstep (se 1 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 856291 = 1284437) B1284437
theorem B4329713 : Blo 758332 4329713 := bstep (se 2 (by rfl) ⟨1623642, by rfl⟩ : syracuseStep 4329713 = 3247285) B3247285
theorem B2560301 : Blo 758332 2560301 := bstep (se 3 (by rfl) ⟨480056, by rfl⟩ : syracuseStep 2560301 = 960113) B960113
theorem B1282385 : Blo 758332 1282385 := bstep (se 2 (by rfl) ⟨480894, by rfl⟩ : syracuseStep 1282385 = 961789) B961789
theorem B2560355 : Blo 758332 2560355 := bstep (se 1 (by rfl) ⟨1920266, by rfl⟩ : syracuseStep 2560355 = 3840533) B3840533
theorem B856435 : Blo 758332 856435 := bstep (se 1 (by rfl) ⟨642326, by rfl⟩ : syracuseStep 856435 = 1284653) B1284653
theorem B1446275 : Blo 758332 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B2167181 : Blo 758332 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B1708433 : Blo 758332 1708433 := bstep (se 2 (by rfl) ⟨640662, by rfl⟩ : syracuseStep 1708433 = 1281325) B1281325
theorem B1708451 : Blo 758332 1708451 := bstep (se 1 (by rfl) ⟨1281338, by rfl⟩ : syracuseStep 1708451 = 2562677) B2562677
theorem B1216963 : Blo 758332 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B1282513 : Blo 758332 1282513 := bstep (se 2 (by rfl) ⟨480942, by rfl⟩ : syracuseStep 1282513 = 961885) B961885
theorem B2167249 : Blo 758332 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B1282547 : Blo 758332 1282547 := bstep (se 1 (by rfl) ⟨961910, by rfl⟩ : syracuseStep 1282547 = 1923821) B1923821
theorem B856579 : Blo 758332 856579 := bstep (se 1 (by rfl) ⟨642434, by rfl⟩ : syracuseStep 856579 = 1284869) B1284869
theorem B758339 : Blo 758332 758339 := bstep (se 1 (by rfl) ⟨568754, by rfl⟩ : syracuseStep 758339 = 1137509) B1137509
theorem B2429507 : Blo 758332 2429507 := bstep (se 1 (by rfl) ⟨1822130, by rfl⟩ : syracuseStep 2429507 = 3644261) B3644261
theorem B758355 : Blo 758332 758355 := bstep (se 1 (by rfl) ⟨568766, by rfl⟩ : syracuseStep 758355 = 1137533) B1137533
theorem B758371 : Blo 758332 758371 := bstep (se 1 (by rfl) ⟨568778, by rfl⟩ : syracuseStep 758371 = 1137557) B1137557
theorem B2560625 : Blo 758332 2560625 := bstep (se 2 (by rfl) ⟨960234, by rfl⟩ : syracuseStep 2560625 = 1920469) B1920469
theorem B758387 : Blo 758332 758387 := bstep (se 1 (by rfl) ⟨568790, by rfl⟩ : syracuseStep 758387 = 1137581) B1137581
theorem B1282675 : Blo 758332 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B758403 : Blo 758332 758403 := bstep (se 1 (by rfl) ⟨568802, by rfl⟩ : syracuseStep 758403 = 1137605) B1137605
theorem B758419 : Blo 758332 758419 := bstep (se 1 (by rfl) ⟨568814, by rfl⟩ : syracuseStep 758419 = 1137629) B1137629
theorem B856723 : Blo 758332 856723 := bstep (se 1 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 856723 = 1285085) B1285085
theorem B758435 : Blo 758332 758435 := bstep (se 1 (by rfl) ⟨568826, by rfl⟩ : syracuseStep 758435 = 1137653) B1137653
theorem B1708721 : Blo 758332 1708721 := bstep (se 2 (by rfl) ⟨640770, by rfl⟩ : syracuseStep 1708721 = 1281541) B1281541
theorem B758451 : Blo 758332 758451 := bstep (se 1 (by rfl) ⟨568838, by rfl⟩ : syracuseStep 758451 = 1137677) B1137677
theorem B758467 : Blo 758332 758467 := bstep (se 1 (by rfl) ⟨568850, by rfl⟩ : syracuseStep 758467 = 1137701) B1137701
theorem B1708739 : Blo 758332 1708739 := bstep (se 1 (by rfl) ⟨1281554, by rfl⟩ : syracuseStep 1708739 = 2563109) B2563109
theorem B758483 : Blo 758332 758483 := bstep (se 1 (by rfl) ⟨568862, by rfl⟩ : syracuseStep 758483 = 1137725) B1137725
theorem B758499 : Blo 758332 758499 := bstep (se 1 (by rfl) ⟨568874, by rfl⟩ : syracuseStep 758499 = 1137749) B1137749
theorem B2888419 : Blo 758332 2888419 := bstep (se 1 (by rfl) ⟨2166314, by rfl⟩ : syracuseStep 2888419 = 4332629) B4332629
theorem B2167523 : Blo 758332 2167523 := bstep (se 1 (by rfl) ⟨1625642, by rfl⟩ : syracuseStep 2167523 = 3251285) B3251285
theorem B758515 : Blo 758332 758515 := bstep (se 1 (by rfl) ⟨568886, by rfl⟩ : syracuseStep 758515 = 1137773) B1137773
theorem B1282817 : Blo 758332 1282817 := bstep (se 2 (by rfl) ⟨481056, by rfl⟩ : syracuseStep 1282817 = 962113) B962113
theorem B758531 : Blo 758332 758531 := bstep (se 1 (by rfl) ⟨568898, by rfl⟩ : syracuseStep 758531 = 1137797) B1137797
theorem B758547 : Blo 758332 758547 := bstep (se 1 (by rfl) ⟨568910, by rfl⟩ : syracuseStep 758547 = 1137821) B1137821
theorem B758563 : Blo 758332 758563 := bstep (se 1 (by rfl) ⟨568922, by rfl⟩ : syracuseStep 758563 = 1137845) B1137845
theorem B1250083 : Blo 758332 1250083 := bstep (se 1 (by rfl) ⟨937562, by rfl⟩ : syracuseStep 1250083 = 1875125) B1875125
theorem B856867 : Blo 758332 856867 := bstep (se 1 (by rfl) ⟨642650, by rfl⟩ : syracuseStep 856867 = 1285301) B1285301
theorem B758579 : Blo 758332 758579 := bstep (se 1 (by rfl) ⟨568934, by rfl⟩ : syracuseStep 758579 = 1137869) B1137869
theorem B758595 : Blo 758332 758595 := bstep (se 1 (by rfl) ⟨568946, by rfl⟩ : syracuseStep 758595 = 1137893) B1137893
theorem B1250129 : Blo 758332 1250129 := bstep (se 2 (by rfl) ⟨468798, by rfl⟩ : syracuseStep 1250129 = 937597) B937597
theorem B758611 : Blo 758332 758611 := bstep (se 1 (by rfl) ⟨568958, by rfl⟩ : syracuseStep 758611 = 1137917) B1137917
theorem B758627 : Blo 758332 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B758643 : Blo 758332 758643 := bstep (se 1 (by rfl) ⟨568982, by rfl⟩ : syracuseStep 758643 = 1137965) B1137965
theorem B1282945 : Blo 758332 1282945 := bstep (se 2 (by rfl) ⟨481104, by rfl⟩ : syracuseStep 1282945 = 962209) B962209
theorem B758659 : Blo 758332 758659 := bstep (se 1 (by rfl) ⟨568994, by rfl⟩ : syracuseStep 758659 = 1137989) B1137989
theorem B1217425 : Blo 758332 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B758675 : Blo 758332 758675 := bstep (se 1 (by rfl) ⟨569006, by rfl⟩ : syracuseStep 758675 = 1138013) B1138013
theorem B758691 : Blo 758332 758691 := bstep (se 1 (by rfl) ⟨569018, by rfl⟩ : syracuseStep 758691 = 1138037) B1138037
theorem B1282979 : Blo 758332 1282979 := bstep (se 1 (by rfl) ⟨962234, by rfl⟩ : syracuseStep 1282979 = 1924469) B1924469
theorem B758707 : Blo 758332 758707 := bstep (se 1 (by rfl) ⟨569030, by rfl⟩ : syracuseStep 758707 = 1138061) B1138061
theorem B857011 : Blo 758332 857011 := bstep (se 1 (by rfl) ⟨642758, by rfl⟩ : syracuseStep 857011 = 1285517) B1285517
theorem B758723 : Blo 758332 758723 := bstep (se 1 (by rfl) ⟨569042, by rfl⟩ : syracuseStep 758723 = 1138085) B1138085
theorem B1709009 : Blo 758332 1709009 := bstep (se 2 (by rfl) ⟨640878, by rfl⟩ : syracuseStep 1709009 = 1281757) B1281757
theorem B758739 : Blo 758332 758739 := bstep (se 1 (by rfl) ⟨569054, by rfl⟩ : syracuseStep 758739 = 1138109) B1138109
theorem B758755 : Blo 758332 758755 := bstep (se 1 (by rfl) ⟨569066, by rfl⟩ : syracuseStep 758755 = 1138133) B1138133
theorem B1709027 : Blo 758332 1709027 := bstep (se 1 (by rfl) ⟨1281770, by rfl⟩ : syracuseStep 1709027 = 2563541) B2563541
theorem B1217521 : Blo 758332 1217521 := bstep (se 2 (by rfl) ⟨456570, by rfl⟩ : syracuseStep 1217521 = 913141) B913141
theorem B758771 : Blo 758332 758771 := bstep (se 1 (by rfl) ⟨569078, by rfl⟩ : syracuseStep 758771 = 1138157) B1138157
theorem B758787 : Blo 758332 758787 := bstep (se 1 (by rfl) ⟨569090, by rfl⟩ : syracuseStep 758787 = 1138181) B1138181
theorem B758803 : Blo 758332 758803 := bstep (se 1 (by rfl) ⟨569102, by rfl⟩ : syracuseStep 758803 = 1138205) B1138205
theorem B758819 : Blo 758332 758819 := bstep (se 1 (by rfl) ⟨569114, by rfl⟩ : syracuseStep 758819 = 1138229) B1138229
theorem B1283107 : Blo 758332 1283107 := bstep (se 1 (by rfl) ⟨962330, by rfl⟩ : syracuseStep 1283107 = 1924661) B1924661
theorem B758835 : Blo 758332 758835 := bstep (se 1 (by rfl) ⟨569126, by rfl⟩ : syracuseStep 758835 = 1138253) B1138253
theorem B758851 : Blo 758332 758851 := bstep (se 1 (by rfl) ⟨569138, by rfl⟩ : syracuseStep 758851 = 1138277) B1138277
theorem B857155 : Blo 758332 857155 := bstep (se 1 (by rfl) ⟨642866, by rfl⟩ : syracuseStep 857155 = 1285733) B1285733
theorem B1315921 : Blo 758332 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B758867 : Blo 758332 758867 := bstep (se 1 (by rfl) ⟨569150, by rfl⟩ : syracuseStep 758867 = 1138301) B1138301
theorem B3839075 : Blo 758332 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B5837923 : Blo 758332 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B758883 : Blo 758332 758883 := bstep (se 1 (by rfl) ⟨569162, by rfl⟩ : syracuseStep 758883 = 1138325) B1138325
theorem B758899 : Blo 758332 758899 := bstep (se 1 (by rfl) ⟨569174, by rfl⟩ : syracuseStep 758899 = 1138349) B1138349
theorem B758915 : Blo 758332 758915 := bstep (se 1 (by rfl) ⟨569186, by rfl⟩ : syracuseStep 758915 = 1138373) B1138373
theorem B2561165 : Blo 758332 2561165 := bstep (se 3 (by rfl) ⟨480218, by rfl⟩ : syracuseStep 2561165 = 960437) B960437
theorem B1217681 : Blo 758332 1217681 := bstep (se 2 (by rfl) ⟨456630, by rfl⟩ : syracuseStep 1217681 = 913261) B913261
theorem B758931 : Blo 758332 758931 := bstep (se 1 (by rfl) ⟨569198, by rfl⟩ : syracuseStep 758931 = 1138397) B1138397
theorem B758947 : Blo 758332 758947 := bstep (se 1 (by rfl) ⟨569210, by rfl⟩ : syracuseStep 758947 = 1138421) B1138421
theorem B1283249 : Blo 758332 1283249 := bstep (se 2 (by rfl) ⟨481218, by rfl⟩ : syracuseStep 1283249 = 962437) B962437
theorem B758963 : Blo 758332 758963 := bstep (se 1 (by rfl) ⟨569222, by rfl⟩ : syracuseStep 758963 = 1138445) B1138445
theorem B2561219 : Blo 758332 2561219 := bstep (se 1 (by rfl) ⟨1920914, by rfl⟩ : syracuseStep 2561219 = 3841829) B3841829
theorem B758979 : Blo 758332 758979 := bstep (se 1 (by rfl) ⟨569234, by rfl⟩ : syracuseStep 758979 = 1138469) B1138469
theorem B758995 : Blo 758332 758995 := bstep (se 1 (by rfl) ⟨569246, by rfl⟩ : syracuseStep 758995 = 1138493) B1138493
theorem B857299 : Blo 758332 857299 := bstep (se 1 (by rfl) ⟨642974, by rfl⟩ : syracuseStep 857299 = 1285949) B1285949
theorem B759011 : Blo 758332 759011 := bstep (se 1 (by rfl) ⟨569258, by rfl⟩ : syracuseStep 759011 = 1138517) B1138517
theorem B1709297 : Blo 758332 1709297 := bstep (se 2 (by rfl) ⟨640986, by rfl⟩ : syracuseStep 1709297 = 1281973) B1281973
theorem B759027 : Blo 758332 759027 := bstep (se 1 (by rfl) ⟨569270, by rfl⟩ : syracuseStep 759027 = 1138541) B1138541
theorem B759043 : Blo 758332 759043 := bstep (se 1 (by rfl) ⟨569282, by rfl⟩ : syracuseStep 759043 = 1138565) B1138565
theorem B1709315 : Blo 758332 1709315 := bstep (se 1 (by rfl) ⟨1281986, by rfl⟩ : syracuseStep 1709315 = 2563973) B2563973
theorem B759059 : Blo 758332 759059 := bstep (se 1 (by rfl) ⟨569294, by rfl⟩ : syracuseStep 759059 = 1138589) B1138589
theorem B759075 : Blo 758332 759075 := bstep (se 1 (by rfl) ⟨569306, by rfl⟩ : syracuseStep 759075 = 1138613) B1138613
theorem B1283377 : Blo 758332 1283377 := bstep (se 2 (by rfl) ⟨481266, by rfl⟩ : syracuseStep 1283377 = 962533) B962533
theorem B1447217 : Blo 758332 1447217 := bstep (se 2 (by rfl) ⟨542706, by rfl⟩ : syracuseStep 1447217 = 1085413) B1085413
theorem B759091 : Blo 758332 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B759107 : Blo 758332 759107 := bstep (se 1 (by rfl) ⟨569330, by rfl⟩ : syracuseStep 759107 = 1138661) B1138661
theorem B759123 : Blo 758332 759123 := bstep (se 1 (by rfl) ⟨569342, by rfl⟩ : syracuseStep 759123 = 1138685) B1138685
theorem B1283411 : Blo 758332 1283411 := bstep (se 1 (by rfl) ⟨962558, by rfl⟩ : syracuseStep 1283411 = 1925117) B1925117
theorem B759139 : Blo 758332 759139 := bstep (se 1 (by rfl) ⟨569354, by rfl⟩ : syracuseStep 759139 = 1138709) B1138709
theorem B857443 : Blo 758332 857443 := bstep (se 1 (by rfl) ⟨643082, by rfl⟩ : syracuseStep 857443 = 1286165) B1286165
theorem B759155 : Blo 758332 759155 := bstep (se 1 (by rfl) ⟨569366, by rfl⟩ : syracuseStep 759155 = 1138733) B1138733
theorem B759171 : Blo 758332 759171 := bstep (se 1 (by rfl) ⟨569378, by rfl⟩ : syracuseStep 759171 = 1138757) B1138757
theorem B759187 : Blo 758332 759187 := bstep (se 1 (by rfl) ⟨569390, by rfl⟩ : syracuseStep 759187 = 1138781) B1138781
theorem B759203 : Blo 758332 759203 := bstep (se 1 (by rfl) ⟨569402, by rfl⟩ : syracuseStep 759203 = 1138805) B1138805
theorem B759219 : Blo 758332 759219 := bstep (se 1 (by rfl) ⟨569414, by rfl⟩ : syracuseStep 759219 = 1138829) B1138829
theorem B759235 : Blo 758332 759235 := bstep (se 1 (by rfl) ⟨569426, by rfl⟩ : syracuseStep 759235 = 1138853) B1138853
theorem B2561489 : Blo 758332 2561489 := bstep (se 2 (by rfl) ⟨960558, by rfl⟩ : syracuseStep 2561489 = 1921117) B1921117
theorem B759251 : Blo 758332 759251 := bstep (se 1 (by rfl) ⟨569438, by rfl⟩ : syracuseStep 759251 = 1138877) B1138877
theorem B1283539 : Blo 758332 1283539 := bstep (se 1 (by rfl) ⟨962654, by rfl⟩ : syracuseStep 1283539 = 1925309) B1925309
theorem B759267 : Blo 758332 759267 := bstep (se 1 (by rfl) ⟨569450, by rfl⟩ : syracuseStep 759267 = 1138901) B1138901
theorem B759283 : Blo 758332 759283 := bstep (se 1 (by rfl) ⟨569462, by rfl⟩ : syracuseStep 759283 = 1138925) B1138925
theorem B857587 : Blo 758332 857587 := bstep (se 1 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 857587 = 1286381) B1286381
theorem B759299 : Blo 758332 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B1709585 : Blo 758332 1709585 := bstep (se 2 (by rfl) ⟨641094, by rfl⟩ : syracuseStep 1709585 = 1282189) B1282189
theorem B759315 : Blo 758332 759315 := bstep (se 1 (by rfl) ⟨569486, by rfl⟩ : syracuseStep 759315 = 1138973) B1138973
theorem B759331 : Blo 758332 759331 := bstep (se 1 (by rfl) ⟨569498, by rfl⟩ : syracuseStep 759331 = 1138997) B1138997
theorem B1709603 : Blo 758332 1709603 := bstep (se 1 (by rfl) ⟨1282202, by rfl⟩ : syracuseStep 1709603 = 2564405) B2564405
theorem B2168365 : Blo 758332 2168365 := bstep (se 3 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 2168365 = 813137) B813137
theorem B759347 : Blo 758332 759347 := bstep (se 1 (by rfl) ⟨569510, by rfl⟩ : syracuseStep 759347 = 1139021) B1139021
theorem B759363 : Blo 758332 759363 := bstep (se 1 (by rfl) ⟨569522, by rfl⟩ : syracuseStep 759363 = 1139045) B1139045
theorem B759379 : Blo 758332 759379 := bstep (se 1 (by rfl) ⟨569534, by rfl⟩ : syracuseStep 759379 = 1139069) B1139069
theorem B1283681 : Blo 758332 1283681 := bstep (se 2 (by rfl) ⟨481380, by rfl⟩ : syracuseStep 1283681 = 962761) B962761
theorem B759395 : Blo 758332 759395 := bstep (se 1 (by rfl) ⟨569546, by rfl⟩ : syracuseStep 759395 = 1139093) B1139093
theorem B759411 : Blo 758332 759411 := bstep (se 1 (by rfl) ⟨569558, by rfl⟩ : syracuseStep 759411 = 1139117) B1139117
theorem B759427 : Blo 758332 759427 := bstep (se 1 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 759427 = 1139141) B1139141
theorem B759443 : Blo 758332 759443 := bstep (se 1 (by rfl) ⟨569582, by rfl⟩ : syracuseStep 759443 = 1139165) B1139165
theorem B759459 : Blo 758332 759459 := bstep (se 1 (by rfl) ⟨569594, by rfl⟩ : syracuseStep 759459 = 1139189) B1139189
theorem B4331171 : Blo 758332 4331171 := bstep (se 1 (by rfl) ⟨3248378, by rfl⟩ : syracuseStep 4331171 = 6496757) B6496757
theorem B759475 : Blo 758332 759475 := bstep (se 1 (by rfl) ⟨569606, by rfl⟩ : syracuseStep 759475 = 1139213) B1139213
theorem B759491 : Blo 758332 759491 := bstep (se 1 (by rfl) ⟨569618, by rfl⟩ : syracuseStep 759491 = 1139237) B1139237
theorem B2168525 : Blo 758332 2168525 := bstep (se 3 (by rfl) ⟨406598, by rfl⟩ : syracuseStep 2168525 = 813197) B813197
theorem B759507 : Blo 758332 759507 := bstep (se 1 (by rfl) ⟨569630, by rfl⟩ : syracuseStep 759507 = 1139261) B1139261
theorem B1283809 : Blo 758332 1283809 := bstep (se 2 (by rfl) ⟨481428, by rfl⟩ : syracuseStep 1283809 = 962857) B962857
theorem B759523 : Blo 758332 759523 := bstep (se 1 (by rfl) ⟨569642, by rfl⟩ : syracuseStep 759523 = 1139285) B1139285
theorem B759539 : Blo 758332 759539 := bstep (se 1 (by rfl) ⟨569654, by rfl⟩ : syracuseStep 759539 = 1139309) B1139309
theorem B759555 : Blo 758332 759555 := bstep (se 1 (by rfl) ⟨569666, by rfl⟩ : syracuseStep 759555 = 1139333) B1139333
theorem B1283843 : Blo 758332 1283843 := bstep (se 1 (by rfl) ⟨962882, by rfl⟩ : syracuseStep 1283843 = 1925765) B1925765
theorem B759571 : Blo 758332 759571 := bstep (se 1 (by rfl) ⟨569678, by rfl⟩ : syracuseStep 759571 = 1139357) B1139357
theorem B759587 : Blo 758332 759587 := bstep (se 1 (by rfl) ⟨569690, by rfl⟩ : syracuseStep 759587 = 1139381) B1139381
theorem B3610403 : Blo 758332 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B1709873 : Blo 758332 1709873 := bstep (se 2 (by rfl) ⟨641202, by rfl⟩ : syracuseStep 1709873 = 1282405) B1282405
theorem B759603 : Blo 758332 759603 := bstep (se 1 (by rfl) ⟨569702, by rfl⟩ : syracuseStep 759603 = 1139405) B1139405
theorem B759619 : Blo 758332 759619 := bstep (se 1 (by rfl) ⟨569714, by rfl⟩ : syracuseStep 759619 = 1139429) B1139429
theorem B1709891 : Blo 758332 1709891 := bstep (se 1 (by rfl) ⟨1282418, by rfl⟩ : syracuseStep 1709891 = 2564837) B2564837
theorem B759635 : Blo 758332 759635 := bstep (se 1 (by rfl) ⟨569726, by rfl⟩ : syracuseStep 759635 = 1139453) B1139453
theorem B759651 : Blo 758332 759651 := bstep (se 1 (by rfl) ⟨569738, by rfl⟩ : syracuseStep 759651 = 1139477) B1139477
theorem B3250019 : Blo 758332 3250019 := bstep (se 1 (by rfl) ⟨2437514, by rfl⟩ : syracuseStep 3250019 = 4875029) B4875029
theorem B759667 : Blo 758332 759667 := bstep (se 1 (by rfl) ⟨569750, by rfl⟩ : syracuseStep 759667 = 1139501) B1139501
theorem B759683 : Blo 758332 759683 := bstep (se 1 (by rfl) ⟨569762, by rfl⟩ : syracuseStep 759683 = 1139525) B1139525
theorem B1283971 : Blo 758332 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B2168707 : Blo 758332 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B3839885 : Blo 758332 3839885 := bstep (se 3 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 3839885 = 1439957) B1439957
theorem B6494093 : Blo 758332 6494093 := bstep (se 3 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 6494093 = 2435285) B2435285
theorem B759699 : Blo 758332 759699 := bstep (se 1 (by rfl) ⟨569774, by rfl⟩ : syracuseStep 759699 = 1139549) B1139549
theorem B759715 : Blo 758332 759715 := bstep (se 1 (by rfl) ⟨569786, by rfl⟩ : syracuseStep 759715 = 1139573) B1139573
theorem B759731 : Blo 758332 759731 := bstep (se 1 (by rfl) ⟨569798, by rfl⟩ : syracuseStep 759731 = 1139597) B1139597
theorem B759747 : Blo 758332 759747 := bstep (se 1 (by rfl) ⟨569810, by rfl⟩ : syracuseStep 759747 = 1139621) B1139621
theorem B759763 : Blo 758332 759763 := bstep (se 1 (by rfl) ⟨569822, by rfl⟩ : syracuseStep 759763 = 1139645) B1139645
theorem B759779 : Blo 758332 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B2562029 : Blo 758332 2562029 := bstep (se 3 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 2562029 = 960761) B960761
theorem B759795 : Blo 758332 759795 := bstep (se 1 (by rfl) ⟨569846, by rfl⟩ : syracuseStep 759795 = 1139693) B1139693
theorem B759811 : Blo 758332 759811 := bstep (se 1 (by rfl) ⟨569858, by rfl⟩ : syracuseStep 759811 = 1139717) B1139717
theorem B1284113 : Blo 758332 1284113 := bstep (se 2 (by rfl) ⟨481542, by rfl⟩ : syracuseStep 1284113 = 963085) B963085
theorem B759827 : Blo 758332 759827 := bstep (se 1 (by rfl) ⟨569870, by rfl⟩ : syracuseStep 759827 = 1139741) B1139741
theorem B2562083 : Blo 758332 2562083 := bstep (se 1 (by rfl) ⟨1921562, by rfl⟩ : syracuseStep 2562083 = 3843125) B3843125
theorem B759843 : Blo 758332 759843 := bstep (se 1 (by rfl) ⟨569882, by rfl⟩ : syracuseStep 759843 = 1139765) B1139765
theorem B759859 : Blo 758332 759859 := bstep (se 1 (by rfl) ⟨569894, by rfl⟩ : syracuseStep 759859 = 1139789) B1139789
theorem B759875 : Blo 758332 759875 := bstep (se 1 (by rfl) ⟨569906, by rfl⟩ : syracuseStep 759875 = 1139813) B1139813
theorem B1710161 : Blo 758332 1710161 := bstep (se 2 (by rfl) ⟨641310, by rfl⟩ : syracuseStep 1710161 = 1282621) B1282621
theorem B759891 : Blo 758332 759891 := bstep (se 1 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 759891 = 1139837) B1139837
theorem B1153121 : Blo 758332 1153121 := bstep (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) B864841
theorem B759907 : Blo 758332 759907 := bstep (se 1 (by rfl) ⟨569930, by rfl⟩ : syracuseStep 759907 = 1139861) B1139861
theorem B1710179 : Blo 758332 1710179 := bstep (se 1 (by rfl) ⟨1282634, by rfl⟩ : syracuseStep 1710179 = 2565269) B2565269
theorem B759923 : Blo 758332 759923 := bstep (se 1 (by rfl) ⟨569942, by rfl⟩ : syracuseStep 759923 = 1139885) B1139885
theorem B759939 : Blo 758332 759939 := bstep (se 1 (by rfl) ⟨569954, by rfl⟩ : syracuseStep 759939 = 1139909) B1139909
theorem B1284241 : Blo 758332 1284241 := bstep (se 2 (by rfl) ⟨481590, by rfl⟩ : syracuseStep 1284241 = 963181) B963181
theorem B759955 : Blo 758332 759955 := bstep (se 1 (by rfl) ⟨569966, by rfl⟩ : syracuseStep 759955 = 1139933) B1139933
theorem B759971 : Blo 758332 759971 := bstep (se 1 (by rfl) ⟨569978, by rfl⟩ : syracuseStep 759971 = 1139957) B1139957
theorem B759987 : Blo 758332 759987 := bstep (se 1 (by rfl) ⟨569990, by rfl⟩ : syracuseStep 759987 = 1139981) B1139981
theorem B1284275 : Blo 758332 1284275 := bstep (se 1 (by rfl) ⟨963206, by rfl⟩ : syracuseStep 1284275 = 1926413) B1926413
theorem B1153219 : Blo 758332 1153219 := bstep (se 1 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 1153219 = 1729829) B1729829
theorem B760003 : Blo 758332 760003 := bstep (se 1 (by rfl) ⟨570002, by rfl⟩ : syracuseStep 760003 = 1140005) B1140005
theorem B760019 : Blo 758332 760019 := bstep (se 1 (by rfl) ⟨570014, by rfl⟩ : syracuseStep 760019 = 1140029) B1140029
theorem B760035 : Blo 758332 760035 := bstep (se 1 (by rfl) ⟨570026, by rfl⟩ : syracuseStep 760035 = 1140053) B1140053
theorem B5478641 : Blo 758332 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B760051 : Blo 758332 760051 := bstep (se 1 (by rfl) ⟨570038, by rfl⟩ : syracuseStep 760051 = 1140077) B1140077
theorem B760067 : Blo 758332 760067 := bstep (se 1 (by rfl) ⟨570050, by rfl⟩ : syracuseStep 760067 = 1140101) B1140101
theorem B760083 : Blo 758332 760083 := bstep (se 1 (by rfl) ⟨570062, by rfl⟩ : syracuseStep 760083 = 1140125) B1140125
theorem B760099 : Blo 758332 760099 := bstep (se 1 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 760099 = 1140149) B1140149
theorem B2562353 : Blo 758332 2562353 := bstep (se 2 (by rfl) ⟨960882, by rfl⟩ : syracuseStep 2562353 = 1921765) B1921765
theorem B760115 : Blo 758332 760115 := bstep (se 1 (by rfl) ⟨570086, by rfl⟩ : syracuseStep 760115 = 1140173) B1140173
theorem B1284403 : Blo 758332 1284403 := bstep (se 1 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 1284403 = 1926605) B1926605
theorem B760131 : Blo 758332 760131 := bstep (se 1 (by rfl) ⟨570098, by rfl⟩ : syracuseStep 760131 = 1140197) B1140197
theorem B760147 : Blo 758332 760147 := bstep (se 1 (by rfl) ⟨570110, by rfl⟩ : syracuseStep 760147 = 1140221) B1140221
theorem B760163 : Blo 758332 760163 := bstep (se 1 (by rfl) ⟨570122, by rfl⟩ : syracuseStep 760163 = 1140245) B1140245
theorem B1710449 : Blo 758332 1710449 := bstep (se 2 (by rfl) ⟨641418, by rfl⟩ : syracuseStep 1710449 = 1282837) B1282837
theorem B760179 : Blo 758332 760179 := bstep (se 1 (by rfl) ⟨570134, by rfl⟩ : syracuseStep 760179 = 1140269) B1140269
theorem B760195 : Blo 758332 760195 := bstep (se 1 (by rfl) ⟨570146, by rfl⟩ : syracuseStep 760195 = 1140293) B1140293
theorem B1710467 : Blo 758332 1710467 := bstep (se 1 (by rfl) ⟨1282850, by rfl⟩ : syracuseStep 1710467 = 2565701) B2565701
theorem B760211 : Blo 758332 760211 := bstep (se 1 (by rfl) ⟨570158, by rfl⟩ : syracuseStep 760211 = 1140317) B1140317
theorem B760227 : Blo 758332 760227 := bstep (se 1 (by rfl) ⟨570170, by rfl⟩ : syracuseStep 760227 = 1140341) B1140341
theorem B760243 : Blo 758332 760243 := bstep (se 1 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 760243 = 1140365) B1140365
theorem B1284545 : Blo 758332 1284545 := bstep (se 2 (by rfl) ⟨481704, by rfl⟩ : syracuseStep 1284545 = 963409) B963409
theorem B760259 : Blo 758332 760259 := bstep (se 1 (by rfl) ⟨570194, by rfl⟩ : syracuseStep 760259 = 1140389) B1140389
theorem B760275 : Blo 758332 760275 := bstep (se 1 (by rfl) ⟨570206, by rfl⟩ : syracuseStep 760275 = 1140413) B1140413
theorem B760291 : Blo 758332 760291 := bstep (se 1 (by rfl) ⟨570218, by rfl⟩ : syracuseStep 760291 = 1140437) B1140437
theorem B760307 : Blo 758332 760307 := bstep (se 1 (by rfl) ⟨570230, by rfl⟩ : syracuseStep 760307 = 1140461) B1140461
theorem B760323 : Blo 758332 760323 := bstep (se 1 (by rfl) ⟨570242, by rfl⟩ : syracuseStep 760323 = 1140485) B1140485
theorem B760339 : Blo 758332 760339 := bstep (se 1 (by rfl) ⟨570254, by rfl⟩ : syracuseStep 760339 = 1140509) B1140509
theorem B760355 : Blo 758332 760355 := bstep (se 1 (by rfl) ⟨570266, by rfl⟩ : syracuseStep 760355 = 1140533) B1140533
theorem B760371 : Blo 758332 760371 := bstep (se 1 (by rfl) ⟨570278, by rfl⟩ : syracuseStep 760371 = 1140557) B1140557
theorem B1284673 : Blo 758332 1284673 := bstep (se 2 (by rfl) ⟨481752, by rfl⟩ : syracuseStep 1284673 = 963505) B963505
theorem B760387 : Blo 758332 760387 := bstep (se 1 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 760387 = 1140581) B1140581
theorem B760403 : Blo 758332 760403 := bstep (se 1 (by rfl) ⟨570302, by rfl⟩ : syracuseStep 760403 = 1140605) B1140605
theorem B760419 : Blo 758332 760419 := bstep (se 1 (by rfl) ⟨570314, by rfl⟩ : syracuseStep 760419 = 1140629) B1140629
theorem B1284707 : Blo 758332 1284707 := bstep (se 1 (by rfl) ⟨963530, by rfl⟩ : syracuseStep 1284707 = 1927061) B1927061
theorem B1481329 : Blo 758332 1481329 := bstep (se 2 (by rfl) ⟨555498, by rfl⟩ : syracuseStep 1481329 = 1110997) B1110997
theorem B760435 : Blo 758332 760435 := bstep (se 1 (by rfl) ⟨570326, by rfl⟩ : syracuseStep 760435 = 1140653) B1140653
theorem B760451 : Blo 758332 760451 := bstep (se 1 (by rfl) ⟨570338, by rfl⟩ : syracuseStep 760451 = 1140677) B1140677
theorem B1710737 : Blo 758332 1710737 := bstep (se 2 (by rfl) ⟨641526, by rfl⟩ : syracuseStep 1710737 = 1283053) B1283053
theorem B760467 : Blo 758332 760467 := bstep (se 1 (by rfl) ⟨570350, by rfl⟩ : syracuseStep 760467 = 1140701) B1140701
theorem B1710755 : Blo 758332 1710755 := bstep (se 1 (by rfl) ⟨1283066, by rfl⟩ : syracuseStep 1710755 = 2566133) B2566133
theorem B760483 : Blo 758332 760483 := bstep (se 1 (by rfl) ⟨570362, by rfl⟩ : syracuseStep 760483 = 1140725) B1140725
theorem B760499 : Blo 758332 760499 := bstep (se 1 (by rfl) ⟨570374, by rfl⟩ : syracuseStep 760499 = 1140749) B1140749
theorem B760515 : Blo 758332 760515 := bstep (se 1 (by rfl) ⟨570386, by rfl⟩ : syracuseStep 760515 = 1140773) B1140773
theorem B760531 : Blo 758332 760531 := bstep (se 1 (by rfl) ⟨570398, by rfl⟩ : syracuseStep 760531 = 1140797) B1140797
theorem B760547 : Blo 758332 760547 := bstep (se 1 (by rfl) ⟨570410, by rfl⟩ : syracuseStep 760547 = 1140821) B1140821
theorem B1284835 : Blo 758332 1284835 := bstep (se 1 (by rfl) ⟨963626, by rfl⟩ : syracuseStep 1284835 = 1927253) B1927253
theorem B760563 : Blo 758332 760563 := bstep (se 1 (by rfl) ⟨570422, by rfl⟩ : syracuseStep 760563 = 1140845) B1140845
theorem B760579 : Blo 758332 760579 := bstep (se 1 (by rfl) ⟨570434, by rfl⟩ : syracuseStep 760579 = 1140869) B1140869
theorem B760595 : Blo 758332 760595 := bstep (se 1 (by rfl) ⟨570446, by rfl⟩ : syracuseStep 760595 = 1140893) B1140893
theorem B760611 : Blo 758332 760611 := bstep (se 1 (by rfl) ⟨570458, by rfl⟩ : syracuseStep 760611 = 1140917) B1140917
theorem B760627 : Blo 758332 760627 := bstep (se 1 (by rfl) ⟨570470, by rfl⟩ : syracuseStep 760627 = 1140941) B1140941
theorem B760643 : Blo 758332 760643 := bstep (se 1 (by rfl) ⟨570482, by rfl⟩ : syracuseStep 760643 = 1140965) B1140965
theorem B2562893 : Blo 758332 2562893 := bstep (se 3 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 2562893 = 961085) B961085
theorem B760659 : Blo 758332 760659 := bstep (se 1 (by rfl) ⟨570494, by rfl⟩ : syracuseStep 760659 = 1140989) B1140989
theorem B760675 : Blo 758332 760675 := bstep (se 1 (by rfl) ⟨570506, by rfl⟩ : syracuseStep 760675 = 1141013) B1141013
theorem B1284977 : Blo 758332 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B760691 : Blo 758332 760691 := bstep (se 1 (by rfl) ⟨570518, by rfl⟩ : syracuseStep 760691 = 1141037) B1141037
theorem B2562947 : Blo 758332 2562947 := bstep (se 1 (by rfl) ⟨1922210, by rfl⟩ : syracuseStep 2562947 = 3844421) B3844421
theorem B760707 : Blo 758332 760707 := bstep (se 1 (by rfl) ⟨570530, by rfl⟩ : syracuseStep 760707 = 1141061) B1141061
theorem B2890637 : Blo 758332 2890637 := bstep (se 3 (by rfl) ⟨541994, by rfl⟩ : syracuseStep 2890637 = 1083989) B1083989
theorem B760723 : Blo 758332 760723 := bstep (se 1 (by rfl) ⟨570542, by rfl⟩ : syracuseStep 760723 = 1141085) B1141085
theorem B1219475 : Blo 758332 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B760739 : Blo 758332 760739 := bstep (se 1 (by rfl) ⟨570554, by rfl⟩ : syracuseStep 760739 = 1141109) B1141109
theorem B1711025 : Blo 758332 1711025 := bstep (se 2 (by rfl) ⟨641634, by rfl⟩ : syracuseStep 1711025 = 1283269) B1283269
theorem B760755 : Blo 758332 760755 := bstep (se 1 (by rfl) ⟨570566, by rfl⟩ : syracuseStep 760755 = 1141133) B1141133
theorem B1711043 : Blo 758332 1711043 := bstep (se 1 (by rfl) ⟨1283282, by rfl⟩ : syracuseStep 1711043 = 2566565) B2566565
theorem B760771 : Blo 758332 760771 := bstep (se 1 (by rfl) ⟨570578, by rfl⟩ : syracuseStep 760771 = 1141157) B1141157
theorem B760787 : Blo 758332 760787 := bstep (se 1 (by rfl) ⟨570590, by rfl⟩ : syracuseStep 760787 = 1141181) B1141181
theorem B760803 : Blo 758332 760803 := bstep (se 1 (by rfl) ⟨570602, by rfl⟩ : syracuseStep 760803 = 1141205) B1141205
theorem B1285105 : Blo 758332 1285105 := bstep (se 2 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 1285105 = 963829) B963829
theorem B760819 : Blo 758332 760819 := bstep (se 1 (by rfl) ⟨570614, by rfl⟩ : syracuseStep 760819 = 1141229) B1141229
theorem B760835 : Blo 758332 760835 := bstep (se 1 (by rfl) ⟨570626, by rfl⟩ : syracuseStep 760835 = 1141253) B1141253
theorem B760851 : Blo 758332 760851 := bstep (se 1 (by rfl) ⟨570638, by rfl⟩ : syracuseStep 760851 = 1141277) B1141277
theorem B1285139 : Blo 758332 1285139 := bstep (se 1 (by rfl) ⟨963854, by rfl⟩ : syracuseStep 1285139 = 1927709) B1927709
theorem B760867 : Blo 758332 760867 := bstep (se 1 (by rfl) ⟨570650, by rfl⟩ : syracuseStep 760867 = 1141301) B1141301
theorem B3251249 : Blo 758332 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B760883 : Blo 758332 760883 := bstep (se 1 (by rfl) ⟨570662, by rfl⟩ : syracuseStep 760883 = 1141325) B1141325
theorem B760899 : Blo 758332 760899 := bstep (se 1 (by rfl) ⟨570674, by rfl⟩ : syracuseStep 760899 = 1141349) B1141349
theorem B2432081 : Blo 758332 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B760915 : Blo 758332 760915 := bstep (se 1 (by rfl) ⟨570686, by rfl⟩ : syracuseStep 760915 = 1141373) B1141373
theorem B760931 : Blo 758332 760931 := bstep (se 1 (by rfl) ⟨570698, by rfl⟩ : syracuseStep 760931 = 1141397) B1141397
theorem B760947 : Blo 758332 760947 := bstep (se 1 (by rfl) ⟨570710, by rfl⟩ : syracuseStep 760947 = 1141421) B1141421
theorem B760963 : Blo 758332 760963 := bstep (se 1 (by rfl) ⟨570722, by rfl⟩ : syracuseStep 760963 = 1141445) B1141445
theorem B2563217 : Blo 758332 2563217 := bstep (se 2 (by rfl) ⟨961206, by rfl⟩ : syracuseStep 2563217 = 1922413) B1922413
theorem B760979 : Blo 758332 760979 := bstep (se 1 (by rfl) ⟨570734, by rfl⟩ : syracuseStep 760979 = 1141469) B1141469
theorem B1285267 : Blo 758332 1285267 := bstep (se 1 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 1285267 = 1927901) B1927901
theorem B760995 : Blo 758332 760995 := bstep (se 1 (by rfl) ⟨570746, by rfl⟩ : syracuseStep 760995 = 1141493) B1141493
theorem B761011 : Blo 758332 761011 := bstep (se 1 (by rfl) ⟨570758, by rfl⟩ : syracuseStep 761011 = 1141517) B1141517
theorem B761027 : Blo 758332 761027 := bstep (se 1 (by rfl) ⟨570770, by rfl⟩ : syracuseStep 761027 = 1141541) B1141541
theorem B1711313 : Blo 758332 1711313 := bstep (se 2 (by rfl) ⟨641742, by rfl⟩ : syracuseStep 1711313 = 1283485) B1283485
theorem B761043 : Blo 758332 761043 := bstep (se 1 (by rfl) ⟨570782, by rfl⟩ : syracuseStep 761043 = 1141565) B1141565
theorem B1711331 : Blo 758332 1711331 := bstep (se 1 (by rfl) ⟨1283498, by rfl⟩ : syracuseStep 1711331 = 2566997) B2566997
theorem B761059 : Blo 758332 761059 := bstep (se 1 (by rfl) ⟨570794, by rfl⟩ : syracuseStep 761059 = 1141589) B1141589
theorem B2170097 : Blo 758332 2170097 := bstep (se 2 (by rfl) ⟨813786, by rfl⟩ : syracuseStep 2170097 = 1627573) B1627573
theorem B761075 : Blo 758332 761075 := bstep (se 1 (by rfl) ⟨570806, by rfl⟩ : syracuseStep 761075 = 1141613) B1141613
theorem B761091 : Blo 758332 761091 := bstep (se 1 (by rfl) ⟨570818, by rfl⟩ : syracuseStep 761091 = 1141637) B1141637
theorem B761107 : Blo 758332 761107 := bstep (se 1 (by rfl) ⟨570830, by rfl⟩ : syracuseStep 761107 = 1141661) B1141661
theorem B1285409 : Blo 758332 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B761123 : Blo 758332 761123 := bstep (se 1 (by rfl) ⟨570842, by rfl⟩ : syracuseStep 761123 = 1141685) B1141685
theorem B761139 : Blo 758332 761139 := bstep (se 1 (by rfl) ⟨570854, by rfl⟩ : syracuseStep 761139 = 1141709) B1141709
theorem B761155 : Blo 758332 761155 := bstep (se 1 (by rfl) ⟨570866, by rfl⟩ : syracuseStep 761155 = 1141733) B1141733
theorem B3906893 : Blo 758332 3906893 := bstep (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) B1465085
theorem B761171 : Blo 758332 761171 := bstep (se 1 (by rfl) ⟨570878, by rfl⟩ : syracuseStep 761171 = 1141757) B1141757
theorem B761187 : Blo 758332 761187 := bstep (se 1 (by rfl) ⟨570890, by rfl⟩ : syracuseStep 761187 = 1141781) B1141781
theorem B761203 : Blo 758332 761203 := bstep (se 1 (by rfl) ⟨570902, by rfl⟩ : syracuseStep 761203 = 1141805) B1141805
theorem B761219 : Blo 758332 761219 := bstep (se 1 (by rfl) ⟨570914, by rfl⟩ : syracuseStep 761219 = 1141829) B1141829
theorem B761235 : Blo 758332 761235 := bstep (se 1 (by rfl) ⟨570926, by rfl⟩ : syracuseStep 761235 = 1141853) B1141853
theorem B1285537 : Blo 758332 1285537 := bstep (se 2 (by rfl) ⟨482076, by rfl⟩ : syracuseStep 1285537 = 964153) B964153
theorem B761251 : Blo 758332 761251 := bstep (se 1 (by rfl) ⟨570938, by rfl⟩ : syracuseStep 761251 = 1141877) B1141877
theorem B761267 : Blo 758332 761267 := bstep (se 1 (by rfl) ⟨570950, by rfl⟩ : syracuseStep 761267 = 1141901) B1141901
theorem B761283 : Blo 758332 761283 := bstep (se 1 (by rfl) ⟨570962, by rfl⟩ : syracuseStep 761283 = 1141925) B1141925
theorem B1285571 : Blo 758332 1285571 := bstep (se 1 (by rfl) ⟨964178, by rfl⟩ : syracuseStep 1285571 = 1928357) B1928357
theorem B761299 : Blo 758332 761299 := bstep (se 1 (by rfl) ⟨570974, by rfl⟩ : syracuseStep 761299 = 1141949) B1141949
theorem B761315 : Blo 758332 761315 := bstep (se 1 (by rfl) ⟨570986, by rfl⟩ : syracuseStep 761315 = 1141973) B1141973
theorem B1711601 : Blo 758332 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B761331 : Blo 758332 761331 := bstep (se 1 (by rfl) ⟨570998, by rfl⟩ : syracuseStep 761331 = 1141997) B1141997
theorem B1711619 : Blo 758332 1711619 := bstep (se 1 (by rfl) ⟨1283714, by rfl⟩ : syracuseStep 1711619 = 2567429) B2567429
theorem B761347 : Blo 758332 761347 := bstep (se 1 (by rfl) ⟨571010, by rfl⟩ : syracuseStep 761347 = 1142021) B1142021
theorem B761363 : Blo 758332 761363 := bstep (se 1 (by rfl) ⟨571022, by rfl⟩ : syracuseStep 761363 = 1142045) B1142045
theorem B761379 : Blo 758332 761379 := bstep (se 1 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 761379 = 1142069) B1142069
theorem B761395 : Blo 758332 761395 := bstep (se 1 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 761395 = 1142093) B1142093
theorem B761411 : Blo 758332 761411 := bstep (se 1 (by rfl) ⟨571058, by rfl⟩ : syracuseStep 761411 = 1142117) B1142117
theorem B1285699 : Blo 758332 1285699 := bstep (se 1 (by rfl) ⟨964274, by rfl⟩ : syracuseStep 1285699 = 1928549) B1928549
theorem B761427 : Blo 758332 761427 := bstep (se 1 (by rfl) ⟨571070, by rfl⟩ : syracuseStep 761427 = 1142141) B1142141
theorem B761443 : Blo 758332 761443 := bstep (se 1 (by rfl) ⟨571082, by rfl⟩ : syracuseStep 761443 = 1142165) B1142165
theorem B761459 : Blo 758332 761459 := bstep (se 1 (by rfl) ⟨571094, by rfl⟩ : syracuseStep 761459 = 1142189) B1142189
theorem B761475 : Blo 758332 761475 := bstep (se 1 (by rfl) ⟨571106, by rfl⟩ : syracuseStep 761475 = 1142213) B1142213
theorem B761491 : Blo 758332 761491 := bstep (se 1 (by rfl) ⟨571118, by rfl⟩ : syracuseStep 761491 = 1142237) B1142237
theorem B761507 : Blo 758332 761507 := bstep (se 1 (by rfl) ⟨571130, by rfl⟩ : syracuseStep 761507 = 1142261) B1142261
theorem B2563757 : Blo 758332 2563757 := bstep (se 3 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 2563757 = 961409) B961409
theorem B761523 : Blo 758332 761523 := bstep (se 1 (by rfl) ⟨571142, by rfl⟩ : syracuseStep 761523 = 1142285) B1142285
theorem B761539 : Blo 758332 761539 := bstep (se 1 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 761539 = 1142309) B1142309
theorem B1285841 : Blo 758332 1285841 := bstep (se 2 (by rfl) ⟨482190, by rfl⟩ : syracuseStep 1285841 = 964381) B964381
theorem B761555 : Blo 758332 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B1220321 : Blo 758332 1220321 := bstep (se 2 (by rfl) ⟨457620, by rfl⟩ : syracuseStep 1220321 = 915241) B915241
theorem B2563811 : Blo 758332 2563811 := bstep (se 1 (by rfl) ⟨1922858, by rfl⟩ : syracuseStep 2563811 = 3845717) B3845717
theorem B761571 : Blo 758332 761571 := bstep (se 1 (by rfl) ⟨571178, by rfl⟩ : syracuseStep 761571 = 1142357) B1142357
theorem B761587 : Blo 758332 761587 := bstep (se 1 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 761587 = 1142381) B1142381
theorem B761603 : Blo 758332 761603 := bstep (se 1 (by rfl) ⟨571202, by rfl⟩ : syracuseStep 761603 = 1142405) B1142405
theorem B1711889 : Blo 758332 1711889 := bstep (se 2 (by rfl) ⟨641958, by rfl⟩ : syracuseStep 1711889 = 1283917) B1283917
theorem B761619 : Blo 758332 761619 := bstep (se 1 (by rfl) ⟨571214, by rfl⟩ : syracuseStep 761619 = 1142429) B1142429
theorem B1711907 : Blo 758332 1711907 := bstep (se 1 (by rfl) ⟨1283930, by rfl⟩ : syracuseStep 1711907 = 2567861) B2567861
theorem B761635 : Blo 758332 761635 := bstep (se 1 (by rfl) ⟨571226, by rfl⟩ : syracuseStep 761635 = 1142453) B1142453
theorem B761651 : Blo 758332 761651 := bstep (se 1 (by rfl) ⟨571238, by rfl⟩ : syracuseStep 761651 = 1142477) B1142477
theorem B761667 : Blo 758332 761667 := bstep (se 1 (by rfl) ⟨571250, by rfl⟩ : syracuseStep 761667 = 1142501) B1142501
theorem B1285969 : Blo 758332 1285969 := bstep (se 2 (by rfl) ⟨482238, by rfl⟩ : syracuseStep 1285969 = 964477) B964477
theorem B761683 : Blo 758332 761683 := bstep (se 1 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 761683 = 1142525) B1142525
theorem B1220449 : Blo 758332 1220449 := bstep (se 2 (by rfl) ⟨457668, by rfl⟩ : syracuseStep 1220449 = 915337) B915337
theorem B761699 : Blo 758332 761699 := bstep (se 1 (by rfl) ⟨571274, by rfl⟩ : syracuseStep 761699 = 1142549) B1142549
theorem B761715 : Blo 758332 761715 := bstep (se 1 (by rfl) ⟨571286, by rfl⟩ : syracuseStep 761715 = 1142573) B1142573
theorem B1286003 : Blo 758332 1286003 := bstep (se 1 (by rfl) ⟨964502, by rfl⟩ : syracuseStep 1286003 = 1929005) B1929005
theorem B761731 : Blo 758332 761731 := bstep (se 1 (by rfl) ⟨571298, by rfl⟩ : syracuseStep 761731 = 1142597) B1142597
theorem B761747 : Blo 758332 761747 := bstep (se 1 (by rfl) ⟨571310, by rfl⟩ : syracuseStep 761747 = 1142621) B1142621
theorem B1220513 : Blo 758332 1220513 := bstep (se 2 (by rfl) ⟨457692, by rfl⟩ : syracuseStep 1220513 = 915385) B915385
theorem B761763 : Blo 758332 761763 := bstep (se 1 (by rfl) ⟨571322, by rfl⟩ : syracuseStep 761763 = 1142645) B1142645
theorem B761779 : Blo 758332 761779 := bstep (se 1 (by rfl) ⟨571334, by rfl⟩ : syracuseStep 761779 = 1142669) B1142669
theorem B761795 : Blo 758332 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B761811 : Blo 758332 761811 := bstep (se 1 (by rfl) ⟨571358, by rfl⟩ : syracuseStep 761811 = 1142717) B1142717
theorem B761827 : Blo 758332 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B2564081 : Blo 758332 2564081 := bstep (se 2 (by rfl) ⟨961530, by rfl⟩ : syracuseStep 2564081 = 1923061) B1923061
theorem B761843 : Blo 758332 761843 := bstep (se 1 (by rfl) ⟨571382, by rfl⟩ : syracuseStep 761843 = 1142765) B1142765
theorem B1286131 : Blo 758332 1286131 := bstep (se 1 (by rfl) ⟨964598, by rfl⟩ : syracuseStep 1286131 = 1929197) B1929197
theorem B761859 : Blo 758332 761859 := bstep (se 1 (by rfl) ⟨571394, by rfl⟩ : syracuseStep 761859 = 1142789) B1142789
theorem B761875 : Blo 758332 761875 := bstep (se 1 (by rfl) ⟨571406, by rfl⟩ : syracuseStep 761875 = 1142813) B1142813
theorem B761891 : Blo 758332 761891 := bstep (se 1 (by rfl) ⟨571418, by rfl⟩ : syracuseStep 761891 = 1142837) B1142837
theorem B1712177 : Blo 758332 1712177 := bstep (se 2 (by rfl) ⟨642066, by rfl⟩ : syracuseStep 1712177 = 1284133) B1284133
theorem B761907 : Blo 758332 761907 := bstep (se 1 (by rfl) ⟨571430, by rfl⟩ : syracuseStep 761907 = 1142861) B1142861
theorem B1712195 : Blo 758332 1712195 := bstep (se 1 (by rfl) ⟨1284146, by rfl⟩ : syracuseStep 1712195 = 2568293) B2568293
theorem B761923 : Blo 758332 761923 := bstep (se 1 (by rfl) ⟨571442, by rfl⟩ : syracuseStep 761923 = 1142885) B1142885
theorem B761939 : Blo 758332 761939 := bstep (se 1 (by rfl) ⟨571454, by rfl⟩ : syracuseStep 761939 = 1142909) B1142909
theorem B761955 : Blo 758332 761955 := bstep (se 1 (by rfl) ⟨571466, by rfl⟩ : syracuseStep 761955 = 1142933) B1142933
theorem B761971 : Blo 758332 761971 := bstep (se 1 (by rfl) ⟨571478, by rfl⟩ : syracuseStep 761971 = 1142957) B1142957
theorem B1286273 : Blo 758332 1286273 := bstep (se 2 (by rfl) ⟨482352, by rfl⟩ : syracuseStep 1286273 = 964705) B964705
theorem B761987 : Blo 758332 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B762003 : Blo 758332 762003 := bstep (se 1 (by rfl) ⟨571502, by rfl⟩ : syracuseStep 762003 = 1143005) B1143005
theorem B762019 : Blo 758332 762019 := bstep (se 1 (by rfl) ⟨571514, by rfl⟩ : syracuseStep 762019 = 1143029) B1143029
theorem B762035 : Blo 758332 762035 := bstep (se 1 (by rfl) ⟨571526, by rfl⟩ : syracuseStep 762035 = 1143053) B1143053
theorem B762051 : Blo 758332 762051 := bstep (se 1 (by rfl) ⟨571538, by rfl⟩ : syracuseStep 762051 = 1143077) B1143077
theorem B2597069 : Blo 758332 2597069 := bstep (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) B973901
theorem B762067 : Blo 758332 762067 := bstep (se 1 (by rfl) ⟨571550, by rfl⟩ : syracuseStep 762067 = 1143101) B1143101
theorem B6496483 : Blo 758332 6496483 := bstep (se 1 (by rfl) ⟨4872362, by rfl⟩ : syracuseStep 6496483 = 9744725) B9744725
theorem B762083 : Blo 758332 762083 := bstep (se 1 (by rfl) ⟨571562, by rfl⟩ : syracuseStep 762083 = 1143125) B1143125
theorem B7315697 : Blo 758332 7315697 := bstep (se 2 (by rfl) ⟨2743386, by rfl⟩ : syracuseStep 7315697 = 5486773) B5486773
theorem B762099 : Blo 758332 762099 := bstep (se 1 (by rfl) ⟨571574, by rfl⟩ : syracuseStep 762099 = 1143149) B1143149
theorem B1286401 : Blo 758332 1286401 := bstep (se 2 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 1286401 = 964801) B964801
theorem B762115 : Blo 758332 762115 := bstep (se 1 (by rfl) ⟨571586, by rfl⟩ : syracuseStep 762115 = 1143173) B1143173
theorem B762131 : Blo 758332 762131 := bstep (se 1 (by rfl) ⟨571598, by rfl⟩ : syracuseStep 762131 = 1143197) B1143197
theorem B762147 : Blo 758332 762147 := bstep (se 1 (by rfl) ⟨571610, by rfl⟩ : syracuseStep 762147 = 1143221) B1143221
theorem B1286435 : Blo 758332 1286435 := bstep (se 1 (by rfl) ⟨964826, by rfl⟩ : syracuseStep 1286435 = 1929653) B1929653
theorem B762163 : Blo 758332 762163 := bstep (se 1 (by rfl) ⟨571622, by rfl⟩ : syracuseStep 762163 = 1143245) B1143245
theorem B762179 : Blo 758332 762179 := bstep (se 1 (by rfl) ⟨571634, by rfl⟩ : syracuseStep 762179 = 1143269) B1143269
theorem B1712465 : Blo 758332 1712465 := bstep (se 2 (by rfl) ⟨642174, by rfl⟩ : syracuseStep 1712465 = 1284349) B1284349
theorem B762195 : Blo 758332 762195 := bstep (se 1 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 762195 = 1143293) B1143293
theorem B1712483 : Blo 758332 1712483 := bstep (se 1 (by rfl) ⟨1284362, by rfl⟩ : syracuseStep 1712483 = 2568725) B2568725
theorem B762211 : Blo 758332 762211 := bstep (se 1 (by rfl) ⟨571658, by rfl⟩ : syracuseStep 762211 = 1143317) B1143317
theorem B762227 : Blo 758332 762227 := bstep (se 1 (by rfl) ⟨571670, by rfl⟩ : syracuseStep 762227 = 1143341) B1143341
theorem B762243 : Blo 758332 762243 := bstep (se 1 (by rfl) ⟨571682, by rfl⟩ : syracuseStep 762243 = 1143365) B1143365
theorem B762259 : Blo 758332 762259 := bstep (se 1 (by rfl) ⟨571694, by rfl⟩ : syracuseStep 762259 = 1143389) B1143389
theorem B762275 : Blo 758332 762275 := bstep (se 1 (by rfl) ⟨571706, by rfl⟩ : syracuseStep 762275 = 1143413) B1143413
theorem B762291 : Blo 758332 762291 := bstep (se 1 (by rfl) ⟨571718, by rfl⟩ : syracuseStep 762291 = 1143437) B1143437
theorem B762307 : Blo 758332 762307 := bstep (se 1 (by rfl) ⟨571730, by rfl⟩ : syracuseStep 762307 = 1143461) B1143461
theorem B762323 : Blo 758332 762323 := bstep (se 1 (by rfl) ⟨571742, by rfl⟩ : syracuseStep 762323 = 1143485) B1143485
theorem B2564621 : Blo 758332 2564621 := bstep (se 3 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 2564621 = 961733) B961733
theorem B2564675 : Blo 758332 2564675 := bstep (se 1 (by rfl) ⟨1923506, by rfl⟩ : syracuseStep 2564675 = 3847013) B3847013
theorem B1712753 : Blo 758332 1712753 := bstep (se 2 (by rfl) ⟨642282, by rfl⟩ : syracuseStep 1712753 = 1284565) B1284565
theorem B1712771 : Blo 758332 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B3842801 : Blo 758332 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B3285809 : Blo 758332 3285809 := bstep (se 2 (by rfl) ⟨1232178, by rfl⟩ : syracuseStep 3285809 = 2464357) B2464357
theorem B2564945 : Blo 758332 2564945 := bstep (se 2 (by rfl) ⟨961854, by rfl⟩ : syracuseStep 2564945 = 1923709) B1923709
theorem B1713041 : Blo 758332 1713041 := bstep (se 2 (by rfl) ⟨642390, by rfl⟩ : syracuseStep 1713041 = 1284781) B1284781
theorem B1713059 : Blo 758332 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B1156115 : Blo 758332 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B1713329 : Blo 758332 1713329 := bstep (se 2 (by rfl) ⟨642498, by rfl⟩ : syracuseStep 1713329 = 1284997) B1284997
theorem B1713347 : Blo 758332 1713347 := bstep (se 1 (by rfl) ⟨1285010, by rfl⟩ : syracuseStep 1713347 = 2570021) B2570021
theorem B959779 : Blo 758332 959779 := bstep (se 1 (by rfl) ⟨719834, by rfl⟩ : syracuseStep 959779 = 1439669) B1439669
theorem B2565485 : Blo 758332 2565485 := bstep (se 3 (by rfl) ⟨481028, by rfl⟩ : syracuseStep 2565485 = 962057) B962057
theorem B2565539 : Blo 758332 2565539 := bstep (se 1 (by rfl) ⟨1924154, by rfl⟩ : syracuseStep 2565539 = 3848309) B3848309
theorem B1025473 : Blo 758332 1025473 := bstep (se 2 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 1025473 = 769105) B769105
theorem B3253709 : Blo 758332 3253709 := bstep (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) B1220141
theorem B1648081 : Blo 758332 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B1713617 : Blo 758332 1713617 := bstep (se 2 (by rfl) ⟨642606, by rfl⟩ : syracuseStep 1713617 = 1285213) B1285213
theorem B1713635 : Blo 758332 1713635 := bstep (se 1 (by rfl) ⟨1285226, by rfl⟩ : syracuseStep 1713635 = 2570453) B2570453
theorem B2434541 : Blo 758332 2434541 := bstep (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) B912953
theorem B6006413 : Blo 758332 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1156771 : Blo 758332 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B4695715 : Blo 758332 4695715 := bstep (se 1 (by rfl) ⟨3521786, by rfl⟩ : syracuseStep 4695715 = 7043573) B7043573
theorem B2565809 : Blo 758332 2565809 := bstep (se 2 (by rfl) ⟨962178, by rfl⟩ : syracuseStep 2565809 = 1924357) B1924357
theorem B1713905 : Blo 758332 1713905 := bstep (se 2 (by rfl) ⟨642714, by rfl⟩ : syracuseStep 1713905 = 1285429) B1285429
theorem B2893553 : Blo 758332 2893553 := bstep (se 2 (by rfl) ⟨1085082, by rfl⟩ : syracuseStep 2893553 = 2170165) B2170165
theorem B1713923 : Blo 758332 1713923 := bstep (se 1 (by rfl) ⟨1285442, by rfl⟩ : syracuseStep 1713923 = 2570885) B2570885
theorem B960275 : Blo 758332 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B4859909 : Blo 758332 4859909 := bstep (se 4 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 4859909 = 911233) B911233
theorem B1714193 : Blo 758332 1714193 := bstep (se 2 (by rfl) ⟨642822, by rfl⟩ : syracuseStep 1714193 = 1285645) B1285645
theorem B1714211 : Blo 758332 1714211 := bstep (se 1 (by rfl) ⟨1285658, by rfl⟩ : syracuseStep 1714211 = 2571317) B2571317
theorem B5482565 : Blo 758332 5482565 := bstep (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) B1027981
theorem B6170737 : Blo 758332 6170737 := bstep (se 2 (by rfl) ⟨2314026, by rfl⟩ : syracuseStep 6170737 = 4628053) B4628053
theorem B3844259 : Blo 758332 3844259 := bstep (se 1 (by rfl) ⟨2883194, by rfl⟩ : syracuseStep 3844259 = 5766389) B5766389
theorem B2566349 : Blo 758332 2566349 := bstep (se 3 (by rfl) ⟨481190, by rfl⟩ : syracuseStep 2566349 = 962381) B962381
theorem B7416035 : Blo 758332 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B2566403 : Blo 758332 2566403 := bstep (se 1 (by rfl) ⟨1924802, by rfl⟩ : syracuseStep 2566403 = 3849605) B3849605
theorem B1714481 : Blo 758332 1714481 := bstep (se 2 (by rfl) ⟨642930, by rfl⟩ : syracuseStep 1714481 = 1285861) B1285861
theorem B2599235 : Blo 758332 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B1714499 : Blo 758332 1714499 := bstep (se 1 (by rfl) ⟨1285874, by rfl⟩ : syracuseStep 1714499 = 2571749) B2571749
theorem B960979 : Blo 758332 960979 := bstep (se 1 (by rfl) ⟨720734, by rfl⟩ : syracuseStep 960979 = 1441469) B1441469
theorem B2566673 : Blo 758332 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B961075 : Blo 758332 961075 := bstep (se 1 (by rfl) ⟨720806, by rfl⟩ : syracuseStep 961075 = 1441613) B1441613
theorem B4106821 : Blo 758332 4106821 := bstep (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) B770029
theorem B1714769 : Blo 758332 1714769 := bstep (se 2 (by rfl) ⟨643038, by rfl⟩ : syracuseStep 1714769 = 1286077) B1286077
theorem B1714787 : Blo 758332 1714787 := bstep (se 1 (by rfl) ⟨1286090, by rfl⟩ : syracuseStep 1714787 = 2572181) B2572181
theorem B1026899 : Blo 758332 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B1715057 : Blo 758332 1715057 := bstep (se 2 (by rfl) ⟨643146, by rfl⟩ : syracuseStep 1715057 = 1286293) B1286293
theorem B1715075 : Blo 758332 1715075 := bstep (se 1 (by rfl) ⟨1286306, by rfl⟩ : syracuseStep 1715075 = 2572613) B2572613
theorem B3845069 : Blo 758332 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B961571 : Blo 758332 961571 := bstep (se 1 (by rfl) ⟨721178, by rfl⟩ : syracuseStep 961571 = 1442357) B1442357
theorem B2436131 : Blo 758332 2436131 := bstep (se 1 (by rfl) ⟨1827098, by rfl⟩ : syracuseStep 2436131 = 3654197) B3654197
theorem B2567213 : Blo 758332 2567213 := bstep (se 3 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 2567213 = 962705) B962705
theorem B2567267 : Blo 758332 2567267 := bstep (se 1 (by rfl) ⟨1925450, by rfl⟩ : syracuseStep 2567267 = 3850901) B3850901
theorem B1158419 : Blo 758332 1158419 := bstep (se 1 (by rfl) ⟨868814, by rfl⟩ : syracuseStep 1158419 = 1737629) B1737629
theorem B2567537 : Blo 758332 2567537 := bstep (se 2 (by rfl) ⟨962826, by rfl⟩ : syracuseStep 2567537 = 1925653) B1925653
theorem B962275 : Blo 758332 962275 := bstep (se 1 (by rfl) ⟨721706, by rfl⟩ : syracuseStep 962275 = 1443413) B1443413
theorem B1027873 : Blo 758332 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B962371 : Blo 758332 962371 := bstep (se 1 (by rfl) ⟨721778, by rfl⟩ : syracuseStep 962371 = 1443557) B1443557
theorem B2568077 : Blo 758332 2568077 := bstep (se 3 (by rfl) ⟨481514, by rfl⟩ : syracuseStep 2568077 = 963029) B963029
theorem B1159057 : Blo 758332 1159057 := bstep (se 2 (by rfl) ⟨434646, by rfl⟩ : syracuseStep 1159057 = 869293) B869293
theorem B1388465 : Blo 758332 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B2568131 : Blo 758332 2568131 := bstep (se 1 (by rfl) ⟨1926098, by rfl⟩ : syracuseStep 2568131 = 3852197) B3852197
theorem B8204429 : Blo 758332 8204429 := bstep (se 3 (by rfl) ⟨1538330, by rfl⟩ : syracuseStep 8204429 = 3076661) B3076661
theorem B2568401 : Blo 758332 2568401 := bstep (se 2 (by rfl) ⟨963150, by rfl⟩ : syracuseStep 2568401 = 1926301) B1926301
theorem B2437361 : Blo 758332 2437361 := bstep (se 2 (by rfl) ⟨914010, by rfl⟩ : syracuseStep 2437361 = 1828021) B1828021
theorem B1028371 : Blo 758332 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B962867 : Blo 758332 962867 := bstep (se 1 (by rfl) ⟨722150, by rfl⟩ : syracuseStep 962867 = 1444301) B1444301
theorem B1028435 : Blo 758332 1028435 := bstep (se 1 (by rfl) ⟨771326, by rfl⟩ : syracuseStep 1028435 = 1542653) B1542653
theorem B4108963 : Blo 758332 4108963 := bstep (se 1 (by rfl) ⟨3081722, by rfl⟩ : syracuseStep 4108963 = 6163445) B6163445
theorem B1028803 : Blo 758332 1028803 := bstep (se 1 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 1028803 = 1543205) B1543205
theorem B2568941 : Blo 758332 2568941 := bstep (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) B963353
theorem B44970773 : Blo 758332 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B2568995 : Blo 758332 2568995 := bstep (se 1 (by rfl) ⟨1926746, by rfl⟩ : syracuseStep 2568995 = 3853493) B3853493
theorem B963571 : Blo 758332 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B2569265 : Blo 758332 2569265 := bstep (se 2 (by rfl) ⟨963474, by rfl⟩ : syracuseStep 2569265 = 1926949) B1926949
theorem B1029187 : Blo 758332 1029187 := bstep (se 1 (by rfl) ⟨771890, by rfl⟩ : syracuseStep 1029187 = 1543781) B1543781
theorem B2438221 : Blo 758332 2438221 := bstep (se 3 (by rfl) ⟨457166, by rfl⟩ : syracuseStep 2438221 = 914333) B914333
theorem B963667 : Blo 758332 963667 := bstep (se 1 (by rfl) ⟨722750, by rfl⟩ : syracuseStep 963667 = 1445501) B1445501
theorem B4633699 : Blo 758332 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B1029235 : Blo 758332 1029235 := bstep (se 1 (by rfl) ⟨771926, by rfl⟩ : syracuseStep 1029235 = 1543853) B1543853
theorem B865571 : Blo 758332 865571 := bstep (se 1 (by rfl) ⟨649178, by rfl⟩ : syracuseStep 865571 = 1298357) B1298357
theorem B2307409 : Blo 758332 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B35173829 : Blo 758332 35173829 := bstep (se 4 (by rfl) ⟨3297546, by rfl⟩ : syracuseStep 35173829 = 6595093) B6595093
theorem B4863523 : Blo 758332 4863523 := bstep (se 1 (by rfl) ⟨3647642, by rfl⟩ : syracuseStep 4863523 = 7295285) B7295285
theorem B964163 : Blo 758332 964163 := bstep (se 1 (by rfl) ⟨723122, by rfl⟩ : syracuseStep 964163 = 1446245) B1446245
theorem B2569805 : Blo 758332 2569805 := bstep (se 3 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 2569805 = 963677) B963677
theorem B2569859 : Blo 758332 2569859 := bstep (se 1 (by rfl) ⟨1927394, by rfl⟩ : syracuseStep 2569859 = 3854789) B3854789
theorem B3847985 : Blo 758332 3847985 := bstep (se 2 (by rfl) ⟨1442994, by rfl⟩ : syracuseStep 3847985 = 2885989) B2885989
theorem B4110193 : Blo 758332 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B2570129 : Blo 758332 2570129 := bstep (se 2 (by rfl) ⟨963798, by rfl⟩ : syracuseStep 2570129 = 1927597) B1927597
theorem B9254897 : Blo 758332 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B4340101 : Blo 758332 4340101 := bstep (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) B813769
theorem B2570669 : Blo 758332 2570669 := bstep (se 3 (by rfl) ⟨482000, by rfl⟩ : syracuseStep 2570669 = 964001) B964001
theorem B2570723 : Blo 758332 2570723 := bstep (se 1 (by rfl) ⟨1928042, by rfl⟩ : syracuseStep 2570723 = 3856085) B3856085
theorem B2439821 : Blo 758332 2439821 := bstep (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) B914933
theorem B2570993 : Blo 758332 2570993 := bstep (se 2 (by rfl) ⟨964122, by rfl⟩ : syracuseStep 2570993 = 1928245) B1928245
theorem B2734883 : Blo 758332 2734883 := bstep (se 1 (by rfl) ⟨2051162, by rfl⟩ : syracuseStep 2734883 = 4102325) B4102325
theorem B8240069 : Blo 758332 8240069 := bstep (se 4 (by rfl) ⟨772506, by rfl⟩ : syracuseStep 8240069 = 1545013) B1545013
theorem B1620977 : Blo 758332 1620977 := bstep (se 2 (by rfl) ⟨607866, by rfl⟩ : syracuseStep 1620977 = 1215733) B1215733
theorem B3849443 : Blo 758332 3849443 := bstep (se 1 (by rfl) ⟨2887082, by rfl⟩ : syracuseStep 3849443 = 5774165) B5774165
theorem B2571533 : Blo 758332 2571533 := bstep (se 3 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 2571533 = 964325) B964325
theorem B2571587 : Blo 758332 2571587 := bstep (se 1 (by rfl) ⟨1928690, by rfl⟩ : syracuseStep 2571587 = 3857381) B3857381
theorem B2571857 : Blo 758332 2571857 := bstep (se 2 (by rfl) ⟨964446, by rfl⟩ : syracuseStep 2571857 = 1928893) B1928893
theorem B2604707 : Blo 758332 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B3653581 : Blo 758332 3653581 := bstep (se 3 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 3653581 = 1370093) B1370093
theorem B3850253 : Blo 758332 3850253 := bstep (se 3 (by rfl) ⟨721922, by rfl⟩ : syracuseStep 3850253 = 1443845) B1443845
theorem B2572397 : Blo 758332 2572397 := bstep (se 3 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 2572397 = 964649) B964649
theorem B2572451 : Blo 758332 2572451 := bstep (se 1 (by rfl) ⟨1929338, by rfl⟩ : syracuseStep 2572451 = 3858677) B3858677
theorem B2441411 : Blo 758332 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B4866317 : Blo 758332 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B2441603 : Blo 758332 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B2572721 : Blo 758332 2572721 := bstep (se 2 (by rfl) ⟨964770, by rfl⟩ : syracuseStep 2572721 = 1929541) B1929541
theorem B2474513 : Blo 758332 2474513 := bstep (se 2 (by rfl) ⟨927942, by rfl⟩ : syracuseStep 2474513 = 1855885) B1855885
theorem B8208965 : Blo 758332 8208965 := bstep (se 4 (by rfl) ⟨769590, by rfl⟩ : syracuseStep 8208965 = 1539181) B1539181
theorem B3130211 : Blo 758332 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B771059 : Blo 758332 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B2311409 : Blo 758332 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B1459729 : Blo 758332 1459729 := bstep (se 2 (by rfl) ⟨547398, by rfl⟩ : syracuseStep 1459729 = 1094797) B1094797
theorem B1460035 : Blo 758332 1460035 := bstep (se 1 (by rfl) ⟨1095026, by rfl⟩ : syracuseStep 1460035 = 2190053) B2190053
theorem B20760461 : Blo 758332 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B2312081 : Blo 758332 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B2738083 : Blo 758332 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B3295331 : Blo 758332 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B16468109 : Blo 758332 16468109 := bstep (se 3 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 16468109 = 6175541) B6175541
theorem B1853585 : Blo 758332 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B2050211 : Blo 758332 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B1624387 : Blo 758332 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B1952131 : Blo 758332 1952131 := bstep (se 1 (by rfl) ⟨1464098, by rfl⟩ : syracuseStep 1952131 = 2928197) B2928197
theorem B2738573 : Blo 758332 2738573 := bstep (se 3 (by rfl) ⟨513482, by rfl⟩ : syracuseStep 2738573 = 1026965) B1026965
theorem B2345699 : Blo 758332 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B3853169 : Blo 758332 3853169 := bstep (se 2 (by rfl) ⟨1444938, by rfl⟩ : syracuseStep 3853169 = 2889877) B2889877
theorem B3329059 : Blo 758332 3329059 := bstep (se 1 (by rfl) ⟨2496794, by rfl⟩ : syracuseStep 3329059 = 4993589) B4993589
theorem B1920145 : Blo 758332 1920145 := bstep (se 2 (by rfl) ⟨720054, by rfl⟩ : syracuseStep 1920145 = 1440109) B1440109
theorem B2051281 : Blo 758332 2051281 := bstep (se 2 (by rfl) ⟨769230, by rfl⟩ : syracuseStep 2051281 = 1538461) B1538461
theorem B1920419 : Blo 758332 1920419 := bstep (se 1 (by rfl) ⟨1440314, by rfl⟩ : syracuseStep 1920419 = 2880629) B2880629
theorem B1920611 : Blo 758332 1920611 := bstep (se 1 (by rfl) ⟨1440458, by rfl⟩ : syracuseStep 1920611 = 2880917) B2880917
theorem B14601869 : Blo 758332 14601869 := bstep (se 3 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 14601869 = 5475701) B5475701
theorem B2314115 : Blo 758332 2314115 := bstep (se 1 (by rfl) ⟨1735586, by rfl⟩ : syracuseStep 2314115 = 3471173) B3471173
theorem B9261125 : Blo 758332 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B1626257 : Blo 758332 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B2085155 : Blo 758332 2085155 := bstep (se 1 (by rfl) ⟨1563866, by rfl⟩ : syracuseStep 2085155 = 3127733) B3127733
theorem B3854627 : Blo 758332 3854627 := bstep (se 1 (by rfl) ⟨2890970, by rfl⟩ : syracuseStep 3854627 = 5781941) B5781941
theorem B1954097 : Blo 758332 1954097 := bstep (se 2 (by rfl) ⟨732786, by rfl⟩ : syracuseStep 1954097 = 1465573) B1465573
theorem B1921553 : Blo 758332 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B18469397 : Blo 758332 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B1921603 : Blo 758332 1921603 := bstep (se 1 (by rfl) ⟨1441202, by rfl⟩ : syracuseStep 1921603 = 2882405) B2882405
theorem B5788259 : Blo 758332 5788259 := bstep (se 1 (by rfl) ⟨4341194, by rfl⟩ : syracuseStep 5788259 = 8682389) B8682389
theorem B1921745 : Blo 758332 1921745 := bstep (se 2 (by rfl) ⟨720654, by rfl⟩ : syracuseStep 1921745 = 1441309) B1441309
theorem B1627121 : Blo 758332 1627121 := bstep (se 2 (by rfl) ⟨610170, by rfl⟩ : syracuseStep 1627121 = 1220341) B1220341
theorem B1758275 : Blo 758332 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B3855437 : Blo 758332 3855437 := bstep (se 3 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 3855437 = 1445789) B1445789
theorem B8016995 : Blo 758332 8016995 := bstep (se 1 (by rfl) ⟨6012746, by rfl⟩ : syracuseStep 8016995 = 12025493) B12025493
theorem B4936817 : Blo 758332 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B1299665 : Blo 758332 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B2053453 : Blo 758332 2053453 := bstep (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) B770045
theorem B9721457 : Blo 758332 9721457 := bstep (se 2 (by rfl) ⟨3645546, by rfl⟩ : syracuseStep 9721457 = 7291093) B7291093
theorem B1922737 : Blo 758332 1922737 := bstep (se 2 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 1922737 = 1442053) B1442053
theorem B14636771 : Blo 758332 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B1923011 : Blo 758332 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B6510563 : Blo 758332 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B1923203 : Blo 758332 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B2316557 : Blo 758332 2316557 := bstep (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) B868709
theorem B1562897 : Blo 758332 1562897 := bstep (se 2 (by rfl) ⟨586086, by rfl⟩ : syracuseStep 1562897 = 1172173) B1172173
theorem B1300835 : Blo 758332 1300835 := bstep (se 1 (by rfl) ⟨975626, by rfl⟩ : syracuseStep 1300835 = 1951253) B1951253
theorem B4872773 : Blo 758332 4872773 := bstep (se 4 (by rfl) ⟨456822, by rfl⟩ : syracuseStep 4872773 = 913645) B913645
theorem B2316899 : Blo 758332 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B9394829 : Blo 758332 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B1170163 : Blo 758332 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B2054915 : Blo 758332 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B973603 : Blo 758332 973603 := bstep (se 1 (by rfl) ⟨730202, by rfl⟩ : syracuseStep 973603 = 1460405) B1460405
theorem B1137521 : Blo 758332 1137521 := bstep (se 2 (by rfl) ⟨426570, by rfl⟩ : syracuseStep 1137521 = 853141) B853141
theorem B1137539 : Blo 758332 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B1825667 : Blo 758332 1825667 := bstep (se 1 (by rfl) ⟨1369250, by rfl⟩ : syracuseStep 1825667 = 2738501) B2738501
theorem B1137569 : Blo 758332 1137569 := bstep (se 2 (by rfl) ⟨426588, by rfl⟩ : syracuseStep 1137569 = 853177) B853177
theorem B1137587 : Blo 758332 1137587 := bstep (se 1 (by rfl) ⟨853190, by rfl⟩ : syracuseStep 1137587 = 1706381) B1706381
theorem B1137617 : Blo 758332 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B1137635 : Blo 758332 1137635 := bstep (se 1 (by rfl) ⟨853226, by rfl⟩ : syracuseStep 1137635 = 1706453) B1706453
theorem B1137665 : Blo 758332 1137665 := bstep (se 2 (by rfl) ⟨426624, by rfl⟩ : syracuseStep 1137665 = 853249) B853249
theorem B1137683 : Blo 758332 1137683 := bstep (se 1 (by rfl) ⟨853262, by rfl⟩ : syracuseStep 1137683 = 1706525) B1706525
theorem B1137713 : Blo 758332 1137713 := bstep (se 2 (by rfl) ⟨426642, by rfl⟩ : syracuseStep 1137713 = 853285) B853285
theorem B1924145 : Blo 758332 1924145 := bstep (se 2 (by rfl) ⟨721554, by rfl⟩ : syracuseStep 1924145 = 1443109) B1443109
theorem B1465393 : Blo 758332 1465393 := bstep (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) B1099045
theorem B1137731 : Blo 758332 1137731 := bstep (se 1 (by rfl) ⟨853298, by rfl⟩ : syracuseStep 1137731 = 1706597) B1706597
theorem B1137761 : Blo 758332 1137761 := bstep (se 2 (by rfl) ⟨426660, by rfl⟩ : syracuseStep 1137761 = 853321) B853321
theorem B1924195 : Blo 758332 1924195 := bstep (se 1 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 1924195 = 2886293) B2886293
theorem B1137779 : Blo 758332 1137779 := bstep (se 1 (by rfl) ⟨853334, by rfl⟩ : syracuseStep 1137779 = 1706669) B1706669
theorem B1137809 : Blo 758332 1137809 := bstep (se 2 (by rfl) ⟨426678, by rfl⟩ : syracuseStep 1137809 = 853357) B853357
theorem B1137827 : Blo 758332 1137827 := bstep (se 1 (by rfl) ⟨853370, by rfl⟩ : syracuseStep 1137827 = 1706741) B1706741
theorem B1137857 : Blo 758332 1137857 := bstep (se 2 (by rfl) ⟨426696, by rfl⟩ : syracuseStep 1137857 = 853393) B853393
theorem B1137875 : Blo 758332 1137875 := bstep (se 1 (by rfl) ⟨853406, by rfl⟩ : syracuseStep 1137875 = 1706813) B1706813
theorem B1137905 : Blo 758332 1137905 := bstep (se 2 (by rfl) ⟨426714, by rfl⟩ : syracuseStep 1137905 = 853429) B853429
theorem B1924337 : Blo 758332 1924337 := bstep (se 2 (by rfl) ⟨721626, by rfl⟩ : syracuseStep 1924337 = 1443253) B1443253
theorem B1137923 : Blo 758332 1137923 := bstep (se 1 (by rfl) ⟨853442, by rfl⟩ : syracuseStep 1137923 = 1706885) B1706885
theorem B1137953 : Blo 758332 1137953 := bstep (se 2 (by rfl) ⟨426732, by rfl⟩ : syracuseStep 1137953 = 853465) B853465
theorem B1137971 : Blo 758332 1137971 := bstep (se 1 (by rfl) ⟨853478, by rfl⟩ : syracuseStep 1137971 = 1706957) B1706957
theorem B1138001 : Blo 758332 1138001 := bstep (se 2 (by rfl) ⟨426750, by rfl⟩ : syracuseStep 1138001 = 853501) B853501
theorem B1138019 : Blo 758332 1138019 := bstep (se 1 (by rfl) ⟨853514, by rfl⟩ : syracuseStep 1138019 = 1707029) B1707029
theorem B1138049 : Blo 758332 1138049 := bstep (se 2 (by rfl) ⟨426768, by rfl⟩ : syracuseStep 1138049 = 853537) B853537
theorem B1138067 : Blo 758332 1138067 := bstep (se 1 (by rfl) ⟨853550, by rfl⟩ : syracuseStep 1138067 = 1707101) B1707101
theorem B1138097 : Blo 758332 1138097 := bstep (se 2 (by rfl) ⟨426786, by rfl⟩ : syracuseStep 1138097 = 853573) B853573
theorem B1465777 : Blo 758332 1465777 := bstep (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) B1099333
theorem B1138115 : Blo 758332 1138115 := bstep (se 1 (by rfl) ⟨853586, by rfl⟩ : syracuseStep 1138115 = 1707173) B1707173
theorem B1138145 : Blo 758332 1138145 := bstep (se 2 (by rfl) ⟨426804, by rfl⟩ : syracuseStep 1138145 = 853609) B853609
theorem B1138163 : Blo 758332 1138163 := bstep (se 1 (by rfl) ⟨853622, by rfl⟩ : syracuseStep 1138163 = 1707245) B1707245
theorem B1138193 : Blo 758332 1138193 := bstep (se 2 (by rfl) ⟨426822, by rfl⟩ : syracuseStep 1138193 = 853645) B853645
theorem B1138211 : Blo 758332 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B1138241 : Blo 758332 1138241 := bstep (se 2 (by rfl) ⟨426840, by rfl⟩ : syracuseStep 1138241 = 853681) B853681
theorem B1138259 : Blo 758332 1138259 := bstep (se 1 (by rfl) ⟨853694, by rfl⟩ : syracuseStep 1138259 = 1707389) B1707389
theorem B1138289 : Blo 758332 1138289 := bstep (se 2 (by rfl) ⟨426858, by rfl⟩ : syracuseStep 1138289 = 853717) B853717
theorem B20799089 : Blo 758332 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B1138307 : Blo 758332 1138307 := bstep (se 1 (by rfl) ⟨853730, by rfl⟩ : syracuseStep 1138307 = 1707461) B1707461
theorem B1138337 : Blo 758332 1138337 := bstep (se 2 (by rfl) ⟨426876, by rfl⟩ : syracuseStep 1138337 = 853753) B853753
theorem B1138355 : Blo 758332 1138355 := bstep (se 1 (by rfl) ⟨853766, by rfl⟩ : syracuseStep 1138355 = 1707533) B1707533
theorem B1138385 : Blo 758332 1138385 := bstep (se 2 (by rfl) ⟨426894, by rfl⟩ : syracuseStep 1138385 = 853789) B853789
theorem B1138403 : Blo 758332 1138403 := bstep (se 1 (by rfl) ⟨853802, by rfl⟩ : syracuseStep 1138403 = 1707605) B1707605
theorem B1138433 : Blo 758332 1138433 := bstep (se 2 (by rfl) ⟨426912, by rfl⟩ : syracuseStep 1138433 = 853825) B853825
theorem B1138451 : Blo 758332 1138451 := bstep (se 1 (by rfl) ⟨853838, by rfl⟩ : syracuseStep 1138451 = 1707677) B1707677
theorem B1138481 : Blo 758332 1138481 := bstep (se 2 (by rfl) ⟨426930, by rfl⟩ : syracuseStep 1138481 = 853861) B853861
theorem B1138499 : Blo 758332 1138499 := bstep (se 1 (by rfl) ⟨853874, by rfl⟩ : syracuseStep 1138499 = 1707749) B1707749
theorem B1138529 : Blo 758332 1138529 := bstep (se 2 (by rfl) ⟨426948, by rfl⟩ : syracuseStep 1138529 = 853897) B853897
theorem B2056049 : Blo 758332 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B1138547 : Blo 758332 1138547 := bstep (se 1 (by rfl) ⟨853910, by rfl⟩ : syracuseStep 1138547 = 1707821) B1707821
theorem B1138577 : Blo 758332 1138577 := bstep (se 2 (by rfl) ⟨426966, by rfl⟩ : syracuseStep 1138577 = 853933) B853933
theorem B1138595 : Blo 758332 1138595 := bstep (se 1 (by rfl) ⟨853946, by rfl⟩ : syracuseStep 1138595 = 1707893) B1707893
theorem B3858353 : Blo 758332 3858353 := bstep (se 2 (by rfl) ⟨1446882, by rfl⟩ : syracuseStep 3858353 = 2893765) B2893765
theorem B1138625 : Blo 758332 1138625 := bstep (se 2 (by rfl) ⟨426984, by rfl⟩ : syracuseStep 1138625 = 853969) B853969
theorem B1138643 : Blo 758332 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B1138673 : Blo 758332 1138673 := bstep (se 2 (by rfl) ⟨427002, by rfl⟩ : syracuseStep 1138673 = 854005) B854005
theorem B1138691 : Blo 758332 1138691 := bstep (se 1 (by rfl) ⟨854018, by rfl⟩ : syracuseStep 1138691 = 1708037) B1708037
theorem B1138721 : Blo 758332 1138721 := bstep (se 2 (by rfl) ⟨427020, by rfl⟩ : syracuseStep 1138721 = 854041) B854041
theorem B1138739 : Blo 758332 1138739 := bstep (se 1 (by rfl) ⟨854054, by rfl⟩ : syracuseStep 1138739 = 1708109) B1708109
theorem B1138769 : Blo 758332 1138769 := bstep (se 2 (by rfl) ⟨427038, by rfl⟩ : syracuseStep 1138769 = 854077) B854077
theorem B1138787 : Blo 758332 1138787 := bstep (se 1 (by rfl) ⟨854090, by rfl⟩ : syracuseStep 1138787 = 1708181) B1708181
theorem B1138817 : Blo 758332 1138817 := bstep (se 2 (by rfl) ⟨427056, by rfl⟩ : syracuseStep 1138817 = 854113) B854113
theorem B1138835 : Blo 758332 1138835 := bstep (se 1 (by rfl) ⟨854126, by rfl⟩ : syracuseStep 1138835 = 1708253) B1708253
theorem B1138865 : Blo 758332 1138865 := bstep (se 2 (by rfl) ⟨427074, by rfl⟩ : syracuseStep 1138865 = 854149) B854149
theorem B1138883 : Blo 758332 1138883 := bstep (se 1 (by rfl) ⟨854162, by rfl⟩ : syracuseStep 1138883 = 1708325) B1708325
theorem B1925329 : Blo 758332 1925329 := bstep (se 2 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 1925329 = 1443997) B1443997
theorem B1138913 : Blo 758332 1138913 := bstep (se 2 (by rfl) ⟨427092, by rfl⟩ : syracuseStep 1138913 = 854185) B854185
theorem B13197539 : Blo 758332 13197539 := bstep (se 1 (by rfl) ⟨9898154, by rfl⟩ : syracuseStep 13197539 = 19796309) B19796309
theorem B1138931 : Blo 758332 1138931 := bstep (se 1 (by rfl) ⟨854198, by rfl⟩ : syracuseStep 1138931 = 1708397) B1708397
theorem B1138961 : Blo 758332 1138961 := bstep (se 2 (by rfl) ⟨427110, by rfl⟩ : syracuseStep 1138961 = 854221) B854221
theorem B1138979 : Blo 758332 1138979 := bstep (se 1 (by rfl) ⟨854234, by rfl⟩ : syracuseStep 1138979 = 1708469) B1708469
theorem B1139009 : Blo 758332 1139009 := bstep (se 2 (by rfl) ⟨427128, by rfl⟩ : syracuseStep 1139009 = 854257) B854257
theorem B4120901 : Blo 758332 4120901 := bstep (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) B772669
theorem B1139027 : Blo 758332 1139027 := bstep (se 1 (by rfl) ⟨854270, by rfl⟩ : syracuseStep 1139027 = 1708541) B1708541
theorem B1139057 : Blo 758332 1139057 := bstep (se 2 (by rfl) ⟨427146, by rfl⟩ : syracuseStep 1139057 = 854293) B854293
theorem B1139075 : Blo 758332 1139075 := bstep (se 1 (by rfl) ⟨854306, by rfl⟩ : syracuseStep 1139075 = 1708613) B1708613
theorem B1139105 : Blo 758332 1139105 := bstep (se 2 (by rfl) ⟨427164, by rfl⟩ : syracuseStep 1139105 = 854329) B854329
theorem B1139123 : Blo 758332 1139123 := bstep (se 1 (by rfl) ⟨854342, by rfl⟩ : syracuseStep 1139123 = 1708685) B1708685
theorem B1139153 : Blo 758332 1139153 := bstep (se 2 (by rfl) ⟨427182, by rfl⟩ : syracuseStep 1139153 = 854365) B854365
theorem B1139171 : Blo 758332 1139171 := bstep (se 1 (by rfl) ⟨854378, by rfl⟩ : syracuseStep 1139171 = 1708757) B1708757
theorem B1925603 : Blo 758332 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B1139201 : Blo 758332 1139201 := bstep (se 2 (by rfl) ⟨427200, by rfl⟩ : syracuseStep 1139201 = 854401) B854401
theorem B1139219 : Blo 758332 1139219 := bstep (se 1 (by rfl) ⟨854414, by rfl⟩ : syracuseStep 1139219 = 1708829) B1708829
theorem B1139249 : Blo 758332 1139249 := bstep (se 2 (by rfl) ⟨427218, by rfl⟩ : syracuseStep 1139249 = 854437) B854437
theorem B1139267 : Blo 758332 1139267 := bstep (se 1 (by rfl) ⟨854450, by rfl⟩ : syracuseStep 1139267 = 1708901) B1708901
theorem B1139297 : Blo 758332 1139297 := bstep (se 2 (by rfl) ⟨427236, by rfl⟩ : syracuseStep 1139297 = 854473) B854473
theorem B1139315 : Blo 758332 1139315 := bstep (se 1 (by rfl) ⟨854486, by rfl⟩ : syracuseStep 1139315 = 1708973) B1708973
theorem B1139345 : Blo 758332 1139345 := bstep (se 2 (by rfl) ⟨427254, by rfl⟩ : syracuseStep 1139345 = 854509) B854509
theorem B1139363 : Blo 758332 1139363 := bstep (se 1 (by rfl) ⟨854522, by rfl⟩ : syracuseStep 1139363 = 1709045) B1709045
theorem B1925795 : Blo 758332 1925795 := bstep (se 1 (by rfl) ⟨1444346, by rfl⟩ : syracuseStep 1925795 = 2888693) B2888693
theorem B1139393 : Blo 758332 1139393 := bstep (se 2 (by rfl) ⟨427272, by rfl⟩ : syracuseStep 1139393 = 854545) B854545
theorem B1139411 : Blo 758332 1139411 := bstep (se 1 (by rfl) ⟨854558, by rfl⟩ : syracuseStep 1139411 = 1709117) B1709117
theorem B1139441 : Blo 758332 1139441 := bstep (se 2 (by rfl) ⟨427290, by rfl⟩ : syracuseStep 1139441 = 854581) B854581
theorem B1139459 : Blo 758332 1139459 := bstep (se 1 (by rfl) ⟨854594, by rfl⟩ : syracuseStep 1139459 = 1709189) B1709189
theorem B1139489 : Blo 758332 1139489 := bstep (se 2 (by rfl) ⟨427308, by rfl⟩ : syracuseStep 1139489 = 854617) B854617
theorem B1139507 : Blo 758332 1139507 := bstep (se 1 (by rfl) ⟨854630, by rfl⟩ : syracuseStep 1139507 = 1709261) B1709261
theorem B1139537 : Blo 758332 1139537 := bstep (se 2 (by rfl) ⟨427326, by rfl⟩ : syracuseStep 1139537 = 854653) B854653
theorem B1303393 : Blo 758332 1303393 := bstep (se 2 (by rfl) ⟨488772, by rfl⟩ : syracuseStep 1303393 = 977545) B977545
theorem B1139555 : Blo 758332 1139555 := bstep (se 1 (by rfl) ⟨854666, by rfl⟩ : syracuseStep 1139555 = 1709333) B1709333
theorem B1139585 : Blo 758332 1139585 := bstep (se 2 (by rfl) ⟨427344, by rfl⟩ : syracuseStep 1139585 = 854689) B854689
theorem B1139603 : Blo 758332 1139603 := bstep (se 1 (by rfl) ⟨854702, by rfl⟩ : syracuseStep 1139603 = 1709405) B1709405
theorem B1139633 : Blo 758332 1139633 := bstep (se 2 (by rfl) ⟨427362, by rfl⟩ : syracuseStep 1139633 = 854725) B854725
theorem B1139651 : Blo 758332 1139651 := bstep (se 1 (by rfl) ⟨854738, by rfl⟩ : syracuseStep 1139651 = 1709477) B1709477
theorem B1139681 : Blo 758332 1139681 := bstep (se 2 (by rfl) ⟨427380, by rfl⟩ : syracuseStep 1139681 = 854761) B854761
theorem B1139699 : Blo 758332 1139699 := bstep (se 1 (by rfl) ⟨854774, by rfl⟩ : syracuseStep 1139699 = 1709549) B1709549
theorem B812035 : Blo 758332 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B1139729 : Blo 758332 1139729 := bstep (se 2 (by rfl) ⟨427398, by rfl⟩ : syracuseStep 1139729 = 854797) B854797
theorem B1139747 : Blo 758332 1139747 := bstep (se 1 (by rfl) ⟨854810, by rfl⟩ : syracuseStep 1139747 = 1709621) B1709621
theorem B1139777 : Blo 758332 1139777 := bstep (se 2 (by rfl) ⟨427416, by rfl⟩ : syracuseStep 1139777 = 854833) B854833
theorem B1139795 : Blo 758332 1139795 := bstep (se 1 (by rfl) ⟨854846, by rfl⟩ : syracuseStep 1139795 = 1709693) B1709693
theorem B1139825 : Blo 758332 1139825 := bstep (se 2 (by rfl) ⟨427434, by rfl⟩ : syracuseStep 1139825 = 854869) B854869
theorem B1139843 : Blo 758332 1139843 := bstep (se 1 (by rfl) ⟨854882, by rfl⟩ : syracuseStep 1139843 = 1709765) B1709765
theorem B1139873 : Blo 758332 1139873 := bstep (se 2 (by rfl) ⟨427452, by rfl⟩ : syracuseStep 1139873 = 854905) B854905
theorem B1139891 : Blo 758332 1139891 := bstep (se 1 (by rfl) ⟨854918, by rfl⟩ : syracuseStep 1139891 = 1709837) B1709837
theorem B1139921 : Blo 758332 1139921 := bstep (se 2 (by rfl) ⟨427470, by rfl⟩ : syracuseStep 1139921 = 854941) B854941
theorem B9233635 : Blo 758332 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B1369315 : Blo 758332 1369315 := bstep (se 1 (by rfl) ⟨1026986, by rfl⟩ : syracuseStep 1369315 = 2053973) B2053973
theorem B1139939 : Blo 758332 1139939 := bstep (se 1 (by rfl) ⟨854954, by rfl⟩ : syracuseStep 1139939 = 1709909) B1709909
theorem B4875491 : Blo 758332 4875491 := bstep (se 1 (by rfl) ⟨3656618, by rfl⟩ : syracuseStep 4875491 = 7313237) B7313237
theorem B1139969 : Blo 758332 1139969 := bstep (se 2 (by rfl) ⟨427488, by rfl⟩ : syracuseStep 1139969 = 854977) B854977
theorem B1139987 : Blo 758332 1139987 := bstep (se 1 (by rfl) ⟨854990, by rfl⟩ : syracuseStep 1139987 = 1709981) B1709981
theorem B1140017 : Blo 758332 1140017 := bstep (se 2 (by rfl) ⟨427506, by rfl⟩ : syracuseStep 1140017 = 855013) B855013
theorem B1140035 : Blo 758332 1140035 := bstep (se 1 (by rfl) ⟨855026, by rfl⟩ : syracuseStep 1140035 = 1710053) B1710053
theorem B1140065 : Blo 758332 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B1140083 : Blo 758332 1140083 := bstep (se 1 (by rfl) ⟨855062, by rfl⟩ : syracuseStep 1140083 = 1710125) B1710125
theorem B1140113 : Blo 758332 1140113 := bstep (se 2 (by rfl) ⟨427542, by rfl⟩ : syracuseStep 1140113 = 855085) B855085
theorem B1140131 : Blo 758332 1140131 := bstep (se 1 (by rfl) ⟨855098, by rfl⟩ : syracuseStep 1140131 = 1710197) B1710197
theorem B812467 : Blo 758332 812467 := bstep (se 1 (by rfl) ⟨609350, by rfl⟩ : syracuseStep 812467 = 1218701) B1218701
theorem B1140161 : Blo 758332 1140161 := bstep (se 2 (by rfl) ⟨427560, by rfl⟩ : syracuseStep 1140161 = 855121) B855121
theorem B1140179 : Blo 758332 1140179 := bstep (se 1 (by rfl) ⟨855134, by rfl⟩ : syracuseStep 1140179 = 1710269) B1710269
theorem B1140209 : Blo 758332 1140209 := bstep (se 2 (by rfl) ⟨427578, by rfl⟩ : syracuseStep 1140209 = 855157) B855157
theorem B1140227 : Blo 758332 1140227 := bstep (se 1 (by rfl) ⟨855170, by rfl⟩ : syracuseStep 1140227 = 1710341) B1710341
theorem B9725453 : Blo 758332 9725453 := bstep (se 3 (by rfl) ⟨1823522, by rfl⟩ : syracuseStep 9725453 = 3647045) B3647045
theorem B1140257 : Blo 758332 1140257 := bstep (se 2 (by rfl) ⟨427596, by rfl⟩ : syracuseStep 1140257 = 855193) B855193
theorem B1140275 : Blo 758332 1140275 := bstep (se 1 (by rfl) ⟨855206, by rfl⟩ : syracuseStep 1140275 = 1710413) B1710413
theorem B1140305 : Blo 758332 1140305 := bstep (se 2 (by rfl) ⟨427614, by rfl⟩ : syracuseStep 1140305 = 855229) B855229
theorem B1926737 : Blo 758332 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B1140323 : Blo 758332 1140323 := bstep (se 1 (by rfl) ⟨855242, by rfl⟩ : syracuseStep 1140323 = 1710485) B1710485
theorem B1140353 : Blo 758332 1140353 := bstep (se 2 (by rfl) ⟨427632, by rfl⟩ : syracuseStep 1140353 = 855265) B855265
theorem B1926787 : Blo 758332 1926787 := bstep (se 1 (by rfl) ⟨1445090, by rfl⟩ : syracuseStep 1926787 = 2890181) B2890181
theorem B1140371 : Blo 758332 1140371 := bstep (se 1 (by rfl) ⟨855278, by rfl⟩ : syracuseStep 1140371 = 1710557) B1710557
theorem B1140401 : Blo 758332 1140401 := bstep (se 2 (by rfl) ⟨427650, by rfl⟩ : syracuseStep 1140401 = 855301) B855301
theorem B1140419 : Blo 758332 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B1140449 : Blo 758332 1140449 := bstep (se 2 (by rfl) ⟨427668, by rfl⟩ : syracuseStep 1140449 = 855337) B855337
theorem B1140467 : Blo 758332 1140467 := bstep (se 1 (by rfl) ⟨855350, by rfl⟩ : syracuseStep 1140467 = 1710701) B1710701
theorem B1140497 : Blo 758332 1140497 := bstep (se 2 (by rfl) ⟨427686, by rfl⟩ : syracuseStep 1140497 = 855373) B855373
theorem B1926929 : Blo 758332 1926929 := bstep (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) B1445197
theorem B1140515 : Blo 758332 1140515 := bstep (se 1 (by rfl) ⟨855386, by rfl⟩ : syracuseStep 1140515 = 1710773) B1710773
theorem B1140545 : Blo 758332 1140545 := bstep (se 2 (by rfl) ⟨427704, by rfl⟩ : syracuseStep 1140545 = 855409) B855409
theorem B1140563 : Blo 758332 1140563 := bstep (se 1 (by rfl) ⟨855422, by rfl⟩ : syracuseStep 1140563 = 1710845) B1710845
theorem B1140593 : Blo 758332 1140593 := bstep (se 2 (by rfl) ⟨427722, by rfl⟩ : syracuseStep 1140593 = 855445) B855445
theorem B1140611 : Blo 758332 1140611 := bstep (se 1 (by rfl) ⟨855458, by rfl⟩ : syracuseStep 1140611 = 1710917) B1710917
theorem B1140641 : Blo 758332 1140641 := bstep (se 2 (by rfl) ⟨427740, by rfl⟩ : syracuseStep 1140641 = 855481) B855481
theorem B1140659 : Blo 758332 1140659 := bstep (se 1 (by rfl) ⟨855494, by rfl⟩ : syracuseStep 1140659 = 1710989) B1710989
theorem B1140689 : Blo 758332 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B1140707 : Blo 758332 1140707 := bstep (se 1 (by rfl) ⟨855530, by rfl⟩ : syracuseStep 1140707 = 1711061) B1711061
theorem B1140737 : Blo 758332 1140737 := bstep (se 2 (by rfl) ⟨427776, by rfl⟩ : syracuseStep 1140737 = 855553) B855553
theorem B1140755 : Blo 758332 1140755 := bstep (se 1 (by rfl) ⟨855566, by rfl⟩ : syracuseStep 1140755 = 1711133) B1711133
theorem B1140785 : Blo 758332 1140785 := bstep (se 2 (by rfl) ⟨427794, by rfl⟩ : syracuseStep 1140785 = 855589) B855589
theorem B1140803 : Blo 758332 1140803 := bstep (se 1 (by rfl) ⟨855602, by rfl⟩ : syracuseStep 1140803 = 1711205) B1711205
theorem B1140833 : Blo 758332 1140833 := bstep (se 2 (by rfl) ⟨427812, by rfl⟩ : syracuseStep 1140833 = 855625) B855625
theorem B1140851 : Blo 758332 1140851 := bstep (se 1 (by rfl) ⟨855638, by rfl⟩ : syracuseStep 1140851 = 1711277) B1711277
theorem B1140881 : Blo 758332 1140881 := bstep (se 2 (by rfl) ⟨427830, by rfl⟩ : syracuseStep 1140881 = 855661) B855661
theorem B1140899 : Blo 758332 1140899 := bstep (se 1 (by rfl) ⟨855674, by rfl⟩ : syracuseStep 1140899 = 1711349) B1711349
theorem B1140929 : Blo 758332 1140929 := bstep (se 2 (by rfl) ⟨427848, by rfl⟩ : syracuseStep 1140929 = 855697) B855697
theorem B1140947 : Blo 758332 1140947 := bstep (se 1 (by rfl) ⟨855710, by rfl⟩ : syracuseStep 1140947 = 1711421) B1711421
theorem B1140977 : Blo 758332 1140977 := bstep (se 2 (by rfl) ⟨427866, by rfl⟩ : syracuseStep 1140977 = 855733) B855733
theorem B1140995 : Blo 758332 1140995 := bstep (se 1 (by rfl) ⟨855746, by rfl⟩ : syracuseStep 1140995 = 1711493) B1711493
theorem B1141025 : Blo 758332 1141025 := bstep (se 2 (by rfl) ⟨427884, by rfl⟩ : syracuseStep 1141025 = 855769) B855769
theorem B1141043 : Blo 758332 1141043 := bstep (se 1 (by rfl) ⟨855782, by rfl⟩ : syracuseStep 1141043 = 1711565) B1711565
theorem B1141073 : Blo 758332 1141073 := bstep (se 2 (by rfl) ⟨427902, by rfl⟩ : syracuseStep 1141073 = 855805) B855805
theorem B1141091 : Blo 758332 1141091 := bstep (se 1 (by rfl) ⟨855818, by rfl⟩ : syracuseStep 1141091 = 1711637) B1711637
theorem B1141121 : Blo 758332 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B1829251 : Blo 758332 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B1141139 : Blo 758332 1141139 := bstep (se 1 (by rfl) ⟨855854, by rfl⟩ : syracuseStep 1141139 = 1711709) B1711709
theorem B1141169 : Blo 758332 1141169 := bstep (se 2 (by rfl) ⟨427938, by rfl⟩ : syracuseStep 1141169 = 855877) B855877
theorem B1141187 : Blo 758332 1141187 := bstep (se 1 (by rfl) ⟨855890, by rfl⟩ : syracuseStep 1141187 = 1711781) B1711781
theorem B1141217 : Blo 758332 1141217 := bstep (se 2 (by rfl) ⟨427956, by rfl⟩ : syracuseStep 1141217 = 855913) B855913
theorem B1141235 : Blo 758332 1141235 := bstep (se 1 (by rfl) ⟨855926, by rfl⟩ : syracuseStep 1141235 = 1711853) B1711853
theorem B1141265 : Blo 758332 1141265 := bstep (se 2 (by rfl) ⟨427974, by rfl⟩ : syracuseStep 1141265 = 855949) B855949
theorem B1141283 : Blo 758332 1141283 := bstep (se 1 (by rfl) ⟨855962, by rfl⟩ : syracuseStep 1141283 = 1711925) B1711925
theorem B1141313 : Blo 758332 1141313 := bstep (se 2 (by rfl) ⟨427992, by rfl⟩ : syracuseStep 1141313 = 855985) B855985
theorem B1141331 : Blo 758332 1141331 := bstep (se 1 (by rfl) ⟨855998, by rfl⟩ : syracuseStep 1141331 = 1711997) B1711997
theorem B1141361 : Blo 758332 1141361 := bstep (se 2 (by rfl) ⟨428010, by rfl⟩ : syracuseStep 1141361 = 856021) B856021
theorem B1141379 : Blo 758332 1141379 := bstep (se 1 (by rfl) ⟨856034, by rfl⟩ : syracuseStep 1141379 = 1712069) B1712069
theorem B1141409 : Blo 758332 1141409 := bstep (se 2 (by rfl) ⟨428028, by rfl⟩ : syracuseStep 1141409 = 856057) B856057
theorem B813731 : Blo 758332 813731 := bstep (se 1 (by rfl) ⟨610298, by rfl⟩ : syracuseStep 813731 = 1220597) B1220597
theorem B1141427 : Blo 758332 1141427 := bstep (se 1 (by rfl) ⟨856070, by rfl⟩ : syracuseStep 1141427 = 1712141) B1712141
theorem B1141457 : Blo 758332 1141457 := bstep (se 2 (by rfl) ⟨428046, by rfl⟩ : syracuseStep 1141457 = 856093) B856093
theorem B1141475 : Blo 758332 1141475 := bstep (se 1 (by rfl) ⟨856106, by rfl⟩ : syracuseStep 1141475 = 1712213) B1712213
theorem B1927921 : Blo 758332 1927921 := bstep (se 2 (by rfl) ⟨722970, by rfl⟩ : syracuseStep 1927921 = 1445941) B1445941
theorem B1141505 : Blo 758332 1141505 := bstep (se 2 (by rfl) ⟨428064, by rfl⟩ : syracuseStep 1141505 = 856129) B856129
theorem B1141523 : Blo 758332 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B1370929 : Blo 758332 1370929 := bstep (se 2 (by rfl) ⟨514098, by rfl⟩ : syracuseStep 1370929 = 1028197) B1028197
theorem B1141553 : Blo 758332 1141553 := bstep (se 2 (by rfl) ⟨428082, by rfl⟩ : syracuseStep 1141553 = 856165) B856165
theorem B1141571 : Blo 758332 1141571 := bstep (se 1 (by rfl) ⟨856178, by rfl⟩ : syracuseStep 1141571 = 1712357) B1712357
theorem B1141601 : Blo 758332 1141601 := bstep (se 2 (by rfl) ⟨428100, by rfl⟩ : syracuseStep 1141601 = 856201) B856201
theorem B1141619 : Blo 758332 1141619 := bstep (se 1 (by rfl) ⟨856214, by rfl⟩ : syracuseStep 1141619 = 1712429) B1712429
theorem B1141649 : Blo 758332 1141649 := bstep (se 2 (by rfl) ⟨428118, by rfl⟩ : syracuseStep 1141649 = 856237) B856237
theorem B1141667 : Blo 758332 1141667 := bstep (se 1 (by rfl) ⟨856250, by rfl⟩ : syracuseStep 1141667 = 1712501) B1712501
theorem B1141697 : Blo 758332 1141697 := bstep (se 2 (by rfl) ⟨428136, by rfl⟩ : syracuseStep 1141697 = 856273) B856273
theorem B1141715 : Blo 758332 1141715 := bstep (se 1 (by rfl) ⟨856286, by rfl⟩ : syracuseStep 1141715 = 1712573) B1712573
theorem B1141745 : Blo 758332 1141745 := bstep (se 2 (by rfl) ⟨428154, by rfl⟩ : syracuseStep 1141745 = 856309) B856309
theorem B1141763 : Blo 758332 1141763 := bstep (se 1 (by rfl) ⟨856322, by rfl⟩ : syracuseStep 1141763 = 1712645) B1712645
theorem B1928195 : Blo 758332 1928195 := bstep (se 1 (by rfl) ⟨1446146, by rfl⟩ : syracuseStep 1928195 = 2892293) B2892293
theorem B1141793 : Blo 758332 1141793 := bstep (se 2 (by rfl) ⟨428172, by rfl⟩ : syracuseStep 1141793 = 856345) B856345
theorem B1141811 : Blo 758332 1141811 := bstep (se 1 (by rfl) ⟨856358, by rfl⟩ : syracuseStep 1141811 = 1712717) B1712717
theorem B1141841 : Blo 758332 1141841 := bstep (se 2 (by rfl) ⟨428190, by rfl⟩ : syracuseStep 1141841 = 856381) B856381
theorem B1141859 : Blo 758332 1141859 := bstep (se 1 (by rfl) ⟨856394, by rfl⟩ : syracuseStep 1141859 = 1712789) B1712789
theorem B1141889 : Blo 758332 1141889 := bstep (se 2 (by rfl) ⟨428208, by rfl⟩ : syracuseStep 1141889 = 856417) B856417
theorem B1141907 : Blo 758332 1141907 := bstep (se 1 (by rfl) ⟨856430, by rfl⟩ : syracuseStep 1141907 = 1712861) B1712861
theorem B4877489 : Blo 758332 4877489 := bstep (se 2 (by rfl) ⟨1829058, by rfl⟩ : syracuseStep 4877489 = 3658117) B3658117
theorem B1141937 : Blo 758332 1141937 := bstep (se 2 (by rfl) ⟨428226, by rfl⟩ : syracuseStep 1141937 = 856453) B856453
theorem B1141955 : Blo 758332 1141955 := bstep (se 1 (by rfl) ⟨856466, by rfl⟩ : syracuseStep 1141955 = 1712933) B1712933
theorem B1928387 : Blo 758332 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B1141985 : Blo 758332 1141985 := bstep (se 2 (by rfl) ⟨428244, by rfl⟩ : syracuseStep 1141985 = 856489) B856489
theorem B1142003 : Blo 758332 1142003 := bstep (se 1 (by rfl) ⟨856502, by rfl⟩ : syracuseStep 1142003 = 1713005) B1713005
theorem B1142033 : Blo 758332 1142033 := bstep (se 2 (by rfl) ⟨428262, by rfl⟩ : syracuseStep 1142033 = 856525) B856525
theorem B1142051 : Blo 758332 1142051 := bstep (se 1 (by rfl) ⟨856538, by rfl⟩ : syracuseStep 1142051 = 1713077) B1713077
theorem B1142081 : Blo 758332 1142081 := bstep (se 2 (by rfl) ⟨428280, by rfl⟩ : syracuseStep 1142081 = 856561) B856561
theorem B1142099 : Blo 758332 1142099 := bstep (se 1 (by rfl) ⟨856574, by rfl⟩ : syracuseStep 1142099 = 1713149) B1713149
theorem B1142129 : Blo 758332 1142129 := bstep (se 2 (by rfl) ⟨428298, by rfl⟩ : syracuseStep 1142129 = 856597) B856597
theorem B1142147 : Blo 758332 1142147 := bstep (se 1 (by rfl) ⟨856610, by rfl⟩ : syracuseStep 1142147 = 1713221) B1713221
theorem B1830289 : Blo 758332 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1142177 : Blo 758332 1142177 := bstep (se 2 (by rfl) ⟨428316, by rfl⟩ : syracuseStep 1142177 = 856633) B856633
theorem B1142195 : Blo 758332 1142195 := bstep (se 1 (by rfl) ⟨856646, by rfl⟩ : syracuseStep 1142195 = 1713293) B1713293
theorem B5762501 : Blo 758332 5762501 := bstep (se 4 (by rfl) ⟨540234, by rfl⟩ : syracuseStep 5762501 = 1080469) B1080469
theorem B1142225 : Blo 758332 1142225 := bstep (se 2 (by rfl) ⟨428334, by rfl⟩ : syracuseStep 1142225 = 856669) B856669
theorem B1142243 : Blo 758332 1142243 := bstep (se 1 (by rfl) ⟨856682, by rfl⟩ : syracuseStep 1142243 = 1713365) B1713365
theorem B1142273 : Blo 758332 1142273 := bstep (se 2 (by rfl) ⟨428352, by rfl⟩ : syracuseStep 1142273 = 856705) B856705
theorem B1142291 : Blo 758332 1142291 := bstep (se 1 (by rfl) ⟨856718, by rfl⟩ : syracuseStep 1142291 = 1713437) B1713437
theorem B3468835 : Blo 758332 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B1142321 : Blo 758332 1142321 := bstep (se 2 (by rfl) ⟨428370, by rfl⟩ : syracuseStep 1142321 = 856741) B856741
theorem B1142339 : Blo 758332 1142339 := bstep (se 1 (by rfl) ⟨856754, by rfl⟩ : syracuseStep 1142339 = 1713509) B1713509
theorem B1142369 : Blo 758332 1142369 := bstep (se 2 (by rfl) ⟨428388, by rfl⟩ : syracuseStep 1142369 = 856777) B856777
theorem B4157027 : Blo 758332 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B1142387 : Blo 758332 1142387 := bstep (se 1 (by rfl) ⟨856790, by rfl⟩ : syracuseStep 1142387 = 1713581) B1713581
theorem B1142417 : Blo 758332 1142417 := bstep (se 2 (by rfl) ⟨428406, by rfl⟩ : syracuseStep 1142417 = 856813) B856813
theorem B1142435 : Blo 758332 1142435 := bstep (se 1 (by rfl) ⟨856826, by rfl⟩ : syracuseStep 1142435 = 1713653) B1713653
theorem B1142465 : Blo 758332 1142465 := bstep (se 2 (by rfl) ⟨428424, by rfl⟩ : syracuseStep 1142465 = 856849) B856849
theorem B4320965 : Blo 758332 4320965 := bstep (se 4 (by rfl) ⟨405090, by rfl⟩ : syracuseStep 4320965 = 810181) B810181
theorem B2223821 : Blo 758332 2223821 := bstep (se 3 (by rfl) ⟨416966, by rfl⟩ : syracuseStep 2223821 = 833933) B833933
theorem B1142483 : Blo 758332 1142483 := bstep (se 1 (by rfl) ⟨856862, by rfl⟩ : syracuseStep 1142483 = 1713725) B1713725
theorem B6942449 : Blo 758332 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B1142513 : Blo 758332 1142513 := bstep (se 2 (by rfl) ⟨428442, by rfl⟩ : syracuseStep 1142513 = 856885) B856885
theorem B1142531 : Blo 758332 1142531 := bstep (se 1 (by rfl) ⟨856898, by rfl⟩ : syracuseStep 1142531 = 1713797) B1713797
theorem B1142561 : Blo 758332 1142561 := bstep (se 2 (by rfl) ⟨428460, by rfl⟩ : syracuseStep 1142561 = 856921) B856921
theorem B1142579 : Blo 758332 1142579 := bstep (se 1 (by rfl) ⟨856934, by rfl⟩ : syracuseStep 1142579 = 1713869) B1713869
theorem B1142609 : Blo 758332 1142609 := bstep (se 2 (by rfl) ⟨428478, by rfl⟩ : syracuseStep 1142609 = 856957) B856957
theorem B1142627 : Blo 758332 1142627 := bstep (se 1 (by rfl) ⟨856970, by rfl⟩ : syracuseStep 1142627 = 1713941) B1713941
theorem B1142657 : Blo 758332 1142657 := bstep (se 2 (by rfl) ⟨428496, by rfl⟩ : syracuseStep 1142657 = 856993) B856993
theorem B1142675 : Blo 758332 1142675 := bstep (se 1 (by rfl) ⟨857006, by rfl⟩ : syracuseStep 1142675 = 1714013) B1714013
theorem B1142705 : Blo 758332 1142705 := bstep (se 2 (by rfl) ⟨428514, by rfl⟩ : syracuseStep 1142705 = 857029) B857029
theorem B1142723 : Blo 758332 1142723 := bstep (se 1 (by rfl) ⟨857042, by rfl⟩ : syracuseStep 1142723 = 1714085) B1714085
theorem B1142753 : Blo 758332 1142753 := bstep (se 2 (by rfl) ⟨428532, by rfl⟩ : syracuseStep 1142753 = 857065) B857065
theorem B2879459 : Blo 758332 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B1142771 : Blo 758332 1142771 := bstep (se 1 (by rfl) ⟨857078, by rfl⟩ : syracuseStep 1142771 = 1714157) B1714157
theorem B1142801 : Blo 758332 1142801 := bstep (se 2 (by rfl) ⟨428550, by rfl⟩ : syracuseStep 1142801 = 857101) B857101
theorem B1142819 : Blo 758332 1142819 := bstep (se 1 (by rfl) ⟨857114, by rfl⟩ : syracuseStep 1142819 = 1714229) B1714229
theorem B1142849 : Blo 758332 1142849 := bstep (se 2 (by rfl) ⟨428568, by rfl⟩ : syracuseStep 1142849 = 857137) B857137
theorem B4878413 : Blo 758332 4878413 := bstep (se 3 (by rfl) ⟨914702, by rfl⟩ : syracuseStep 4878413 = 1829405) B1829405
theorem B1142867 : Blo 758332 1142867 := bstep (se 1 (by rfl) ⟨857150, by rfl⟩ : syracuseStep 1142867 = 1714301) B1714301
theorem B1142897 : Blo 758332 1142897 := bstep (se 2 (by rfl) ⟨428586, by rfl⟩ : syracuseStep 1142897 = 857173) B857173
theorem B1929329 : Blo 758332 1929329 := bstep (se 2 (by rfl) ⟨723498, by rfl⟩ : syracuseStep 1929329 = 1446997) B1446997
theorem B1142915 : Blo 758332 1142915 := bstep (se 1 (by rfl) ⟨857186, by rfl⟩ : syracuseStep 1142915 = 1714373) B1714373
theorem B4321421 : Blo 758332 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B1142945 : Blo 758332 1142945 := bstep (se 2 (by rfl) ⟨428604, by rfl⟩ : syracuseStep 1142945 = 857209) B857209
theorem B815267 : Blo 758332 815267 := bstep (se 1 (by rfl) ⟨611450, by rfl⟩ : syracuseStep 815267 = 1222901) B1222901
theorem B1929379 : Blo 758332 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B1142963 : Blo 758332 1142963 := bstep (se 1 (by rfl) ⟨857222, by rfl⟩ : syracuseStep 1142963 = 1714445) B1714445
theorem B1142993 : Blo 758332 1142993 := bstep (se 2 (by rfl) ⟨428622, by rfl⟩ : syracuseStep 1142993 = 857245) B857245
theorem B1143011 : Blo 758332 1143011 := bstep (se 1 (by rfl) ⟨857258, by rfl⟩ : syracuseStep 1143011 = 1714517) B1714517
theorem B1143041 : Blo 758332 1143041 := bstep (se 2 (by rfl) ⟨428640, by rfl⟩ : syracuseStep 1143041 = 857281) B857281
theorem B1143059 : Blo 758332 1143059 := bstep (se 1 (by rfl) ⟨857294, by rfl⟩ : syracuseStep 1143059 = 1714589) B1714589
theorem B1143089 : Blo 758332 1143089 := bstep (se 2 (by rfl) ⟨428658, by rfl⟩ : syracuseStep 1143089 = 857317) B857317
theorem B1929521 : Blo 758332 1929521 := bstep (se 2 (by rfl) ⟨723570, by rfl⟩ : syracuseStep 1929521 = 1447141) B1447141
theorem B1143107 : Blo 758332 1143107 := bstep (se 1 (by rfl) ⟨857330, by rfl⟩ : syracuseStep 1143107 = 1714661) B1714661
theorem B1143137 : Blo 758332 1143137 := bstep (se 2 (by rfl) ⟨428676, by rfl⟩ : syracuseStep 1143137 = 857353) B857353
theorem B1143155 : Blo 758332 1143155 := bstep (se 1 (by rfl) ⟨857366, by rfl⟩ : syracuseStep 1143155 = 1714733) B1714733
theorem B1143185 : Blo 758332 1143185 := bstep (se 2 (by rfl) ⟨428694, by rfl⟩ : syracuseStep 1143185 = 857389) B857389
theorem B1143203 : Blo 758332 1143203 := bstep (se 1 (by rfl) ⟨857402, by rfl⟩ : syracuseStep 1143203 = 1714805) B1714805
theorem B1143233 : Blo 758332 1143233 := bstep (se 2 (by rfl) ⟨428712, by rfl⟩ : syracuseStep 1143233 = 857425) B857425
theorem B1143251 : Blo 758332 1143251 := bstep (se 1 (by rfl) ⟨857438, by rfl⟩ : syracuseStep 1143251 = 1714877) B1714877
theorem B4616675 : Blo 758332 4616675 := bstep (se 1 (by rfl) ⟨3462506, by rfl⟩ : syracuseStep 4616675 = 6925013) B6925013
theorem B1143281 : Blo 758332 1143281 := bstep (se 2 (by rfl) ⟨428730, by rfl⟩ : syracuseStep 1143281 = 857461) B857461
theorem B1143299 : Blo 758332 1143299 := bstep (se 1 (by rfl) ⟨857474, by rfl⟩ : syracuseStep 1143299 = 1714949) B1714949
theorem B1143329 : Blo 758332 1143329 := bstep (se 2 (by rfl) ⟨428748, by rfl⟩ : syracuseStep 1143329 = 857497) B857497
theorem B3469873 : Blo 758332 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B1143347 : Blo 758332 1143347 := bstep (se 1 (by rfl) ⟨857510, by rfl⟩ : syracuseStep 1143347 = 1715021) B1715021
theorem B1143377 : Blo 758332 1143377 := bstep (se 2 (by rfl) ⟨428766, by rfl⟩ : syracuseStep 1143377 = 857533) B857533
theorem B1143395 : Blo 758332 1143395 := bstep (se 1 (by rfl) ⟨857546, by rfl⟩ : syracuseStep 1143395 = 1715093) B1715093
theorem B1143425 : Blo 758332 1143425 := bstep (se 2 (by rfl) ⟨428784, by rfl⟩ : syracuseStep 1143425 = 857569) B857569
theorem B1143443 : Blo 758332 1143443 := bstep (se 1 (by rfl) ⟨857582, by rfl⟩ : syracuseStep 1143443 = 1715165) B1715165
theorem B1143473 : Blo 758332 1143473 := bstep (se 2 (by rfl) ⟨428802, by rfl⟩ : syracuseStep 1143473 = 857605) B857605
theorem B1143491 : Blo 758332 1143491 := bstep (se 1 (by rfl) ⟨857618, by rfl⟩ : syracuseStep 1143491 = 1715237) B1715237
theorem B914371 : Blo 758332 914371 := bstep (se 1 (by rfl) ⟨685778, by rfl⟩ : syracuseStep 914371 = 1371557) B1371557
theorem B2880461 : Blo 758332 2880461 := bstep (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) B1080173
theorem B12973283 : Blo 758332 12973283 := bstep (se 1 (by rfl) ⟨9729962, by rfl⟩ : syracuseStep 12973283 = 19459925) B19459925
theorem B1373539 : Blo 758332 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B3077489 : Blo 758332 3077489 := bstep (se 2 (by rfl) ⟨1154058, by rfl⟩ : syracuseStep 3077489 = 2308117) B2308117
theorem B2160017 : Blo 758332 2160017 := bstep (se 2 (by rfl) ⟨810006, by rfl⟩ : syracuseStep 2160017 = 1620013) B1620013
theorem B8680931 : Blo 758332 8680931 := bstep (se 1 (by rfl) ⟨6510698, by rfl⟩ : syracuseStep 8680931 = 13021397) B13021397
theorem B2160209 : Blo 758332 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B3241613 : Blo 758332 3241613 := bstep (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) B1215605
theorem B915347 : Blo 758332 915347 := bstep (se 1 (by rfl) ⟨686510, by rfl⟩ : syracuseStep 915347 = 1373021) B1373021
theorem B2161201 : Blo 758332 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B1440337 : Blo 758332 1440337 := bstep (se 2 (by rfl) ⟨540126, by rfl⟩ : syracuseStep 1440337 = 1080253) B1080253
theorem B3078755 : Blo 758332 3078755 := bstep (se 1 (by rfl) ⟨2309066, by rfl⟩ : syracuseStep 3078755 = 4618133) B4618133
theorem B1440497 : Blo 758332 1440497 := bstep (se 2 (by rfl) ⟨540186, by rfl⟩ : syracuseStep 1440497 = 1080373) B1080373
theorem B2161475 : Blo 758332 2161475 := bstep (se 1 (by rfl) ⟨1621106, by rfl⟩ : syracuseStep 2161475 = 3242213) B3242213
theorem B1080145 : Blo 758332 1080145 := bstep (se 2 (by rfl) ⟨405054, by rfl⟩ : syracuseStep 1080145 = 810109) B810109
theorem B4324337 : Blo 758332 4324337 := bstep (se 2 (by rfl) ⟨1621626, by rfl⟩ : syracuseStep 4324337 = 3243253) B3243253
theorem B2161667 : Blo 758332 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B2882573 : Blo 758332 2882573 := bstep (se 3 (by rfl) ⟨540482, by rfl⟩ : syracuseStep 2882573 = 1080965) B1080965
theorem B1440899 : Blo 758332 1440899 := bstep (se 1 (by rfl) ⟨1080674, by rfl⟩ : syracuseStep 1440899 = 2161349) B2161349
theorem B1080481 : Blo 758332 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B3243185 : Blo 758332 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B10386629 : Blo 758332 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B3702029 : Blo 758332 3702029 := bstep (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) B1388261
theorem B1539409 : Blo 758332 1539409 := bstep (se 2 (by rfl) ⟨577278, by rfl⟩ : syracuseStep 1539409 = 1154557) B1154557
theorem B3079565 : Blo 758332 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1539523 : Blo 758332 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B1081073 : Blo 758332 1081073 := bstep (se 2 (by rfl) ⟨405402, by rfl⟩ : syracuseStep 1081073 = 810805) B810805
theorem B2162477 : Blo 758332 2162477 := bstep (se 3 (by rfl) ⟨405464, by rfl⟩ : syracuseStep 2162477 = 810929) B810929
theorem B2883377 : Blo 758332 2883377 := bstep (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) B2162533
theorem B8781637 : Blo 758332 8781637 := bstep (se 4 (by rfl) ⟨823278, by rfl⟩ : syracuseStep 8781637 = 1646557) B1646557
theorem B2162659 : Blo 758332 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B3244211 : Blo 758332 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B2883863 : Blo 758332 2883863 := bstep (se 1 (by rfl) ⟨2162897, by rfl⟩ : syracuseStep 2883863 = 4325795) B4325795
theorem B1442099 : Blo 758332 1442099 := bstep (se 1 (by rfl) ⟨1081574, by rfl⟩ : syracuseStep 1442099 = 2163149) B2163149
theorem B1442137 : Blo 758332 1442137 := bstep (se 2 (by rfl) ⟨540801, by rfl⟩ : syracuseStep 1442137 = 1081603) B1081603
theorem B35193437 : Blo 758332 35193437 := bstep (se 3 (by rfl) ⟨6598769, by rfl⟩ : syracuseStep 35193437 = 13197539) B13197539
theorem B1442585 : Blo 758332 1442585 := bstep (se 2 (by rfl) ⟨540969, by rfl⟩ : syracuseStep 1442585 = 1081939) B1081939
theorem B1540939 : Blo 758332 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B2884531 : Blo 758332 2884531 := bstep (se 1 (by rfl) ⟨2163398, by rfl⟩ : syracuseStep 2884531 = 4326797) B4326797
theorem B2163763 : Blo 758332 2163763 := bstep (se 1 (by rfl) ⟨1622822, by rfl⟩ : syracuseStep 2163763 = 3245645) B3245645
theorem B1737857 : Blo 758332 1737857 := bstep (se 2 (by rfl) ⟨651696, by rfl⟩ : syracuseStep 1737857 = 1303393) B1303393
theorem B853195 : Blo 758332 853195 := bstep (se 1 (by rfl) ⟨639896, by rfl⟩ : syracuseStep 853195 = 1279793) B1279793
theorem B1541387 : Blo 758332 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B2163991 : Blo 758332 2163991 := bstep (se 1 (by rfl) ⟨1622993, by rfl⟩ : syracuseStep 2163991 = 3245987) B3245987
theorem B853303 : Blo 758332 853303 := bstep (se 1 (by rfl) ⟨639977, by rfl⟩ : syracuseStep 853303 = 1279955) B1279955
theorem B2196887 : Blo 758332 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B10978739 : Blo 758332 10978739 := bstep (se 1 (by rfl) ⟨8234054, by rfl⟩ : syracuseStep 10978739 = 16468109) B16468109
theorem B853483 : Blo 758332 853483 := bstep (se 1 (by rfl) ⟨640112, by rfl⟩ : syracuseStep 853483 = 1280225) B1280225
theorem B1443329 : Blo 758332 1443329 := bstep (se 2 (by rfl) ⟨541248, by rfl⟩ : syracuseStep 1443329 = 1082497) B1082497
theorem B21890573 : Blo 758332 21890573 := bstep (se 3 (by rfl) ⟨4104482, by rfl⟩ : syracuseStep 21890573 = 8208965) B8208965
theorem B853591 : Blo 758332 853591 := bstep (se 1 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 853591 = 1280387) B1280387
theorem B3344075 : Blo 758332 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B1279705 : Blo 758332 1279705 := bstep (se 2 (by rfl) ⟨479889, by rfl⟩ : syracuseStep 1279705 = 959779) B959779
theorem B853771 : Blo 758332 853771 := bstep (se 1 (by rfl) ⟨640328, by rfl⟩ : syracuseStep 853771 = 1280657) B1280657
theorem B1443595 : Blo 758332 1443595 := bstep (se 1 (by rfl) ⟨1082696, by rfl⟩ : syracuseStep 1443595 = 2165393) B2165393
theorem B853879 : Blo 758332 853879 := bstep (se 1 (by rfl) ⟨640409, by rfl⟩ : syracuseStep 853879 = 1280819) B1280819
theorem B1083289 : Blo 758332 1083289 := bstep (se 2 (by rfl) ⟨406233, by rfl⟩ : syracuseStep 1083289 = 812467) B812467
theorem B2197441 : Blo 758332 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B854059 : Blo 758332 854059 := bstep (se 1 (by rfl) ⟨640544, by rfl⟩ : syracuseStep 854059 = 1281089) B1281089
theorem B2885777 : Blo 758332 2885777 := bstep (se 2 (by rfl) ⟨1082166, by rfl⟩ : syracuseStep 2885777 = 2164333) B2164333
theorem B854167 : Blo 758332 854167 := bstep (se 1 (by rfl) ⟨640625, by rfl⟩ : syracuseStep 854167 = 1281251) B1281251
theorem B1444043 : Blo 758332 1444043 := bstep (se 1 (by rfl) ⟨1083032, by rfl⟩ : syracuseStep 1444043 = 2166065) B2166065
theorem B1280279 : Blo 758332 1280279 := bstep (se 1 (by rfl) ⟨960209, by rfl⟩ : syracuseStep 1280279 = 1920419) B1920419
theorem B1706291 : Blo 758332 1706291 := bstep (se 1 (by rfl) ⟨1279718, by rfl⟩ : syracuseStep 1706291 = 2559437) B2559437
theorem B854347 : Blo 758332 854347 := bstep (se 1 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 854347 = 1281521) B1281521
theorem B1706327 : Blo 758332 1706327 := bstep (se 1 (by rfl) ⟨1279745, by rfl⟩ : syracuseStep 1706327 = 2559491) B2559491
theorem B6490469 : Blo 758332 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B1444225 : Blo 758332 1444225 := bstep (se 2 (by rfl) ⟨541584, by rfl⟩ : syracuseStep 1444225 = 1083169) B1083169
theorem B1280407 : Blo 758332 1280407 := bstep (se 1 (by rfl) ⟨960305, by rfl⟩ : syracuseStep 1280407 = 1920611) B1920611
theorem B9734579 : Blo 758332 9734579 := bstep (se 1 (by rfl) ⟨7300934, by rfl⟩ : syracuseStep 9734579 = 14601869) B14601869
theorem B854455 : Blo 758332 854455 := bstep (se 1 (by rfl) ⟨640841, by rfl⟩ : syracuseStep 854455 = 1281683) B1281683
theorem B1706507 : Blo 758332 1706507 := bstep (se 1 (by rfl) ⟨1279880, by rfl⟩ : syracuseStep 1706507 = 2559761) B2559761
theorem B1706561 : Blo 758332 1706561 := bstep (se 2 (by rfl) ⟨639960, by rfl⟩ : syracuseStep 1706561 = 1279921) B1279921
theorem B1542743 : Blo 758332 1542743 := bstep (se 1 (by rfl) ⟨1157057, by rfl⟩ : syracuseStep 1542743 = 2314115) B2314115
theorem B854635 : Blo 758332 854635 := bstep (se 1 (by rfl) ⟨640976, by rfl⟩ : syracuseStep 854635 = 1281953) B1281953
theorem B854743 : Blo 758332 854743 := bstep (se 1 (by rfl) ⟨641057, by rfl⟩ : syracuseStep 854743 = 1282115) B1282115
theorem B1444567 : Blo 758332 1444567 := bstep (se 1 (by rfl) ⟨1083425, by rfl⟩ : syracuseStep 1444567 = 2166851) B2166851
theorem B1706777 : Blo 758332 1706777 := bstep (se 2 (by rfl) ⟨640041, by rfl⟩ : syracuseStep 1706777 = 1280083) B1280083
theorem B8227649 : Blo 758332 8227649 := bstep (se 2 (by rfl) ⟨3085368, by rfl⟩ : syracuseStep 8227649 = 6170737) B6170737
theorem B2886475 : Blo 758332 2886475 := bstep (se 1 (by rfl) ⟨2164856, by rfl⟩ : syracuseStep 2886475 = 4329713) B4329713
theorem B1706867 : Blo 758332 1706867 := bstep (se 1 (by rfl) ⟨1280150, by rfl⟩ : syracuseStep 1706867 = 2560301) B2560301
theorem B854923 : Blo 758332 854923 := bstep (se 1 (by rfl) ⟨641192, by rfl⟩ : syracuseStep 854923 = 1282385) B1282385
theorem B1706903 : Blo 758332 1706903 := bstep (se 1 (by rfl) ⟨1280177, by rfl⟩ : syracuseStep 1706903 = 2560355) B2560355
theorem B1444787 : Blo 758332 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B855031 : Blo 758332 855031 := bstep (se 1 (by rfl) ⟨641273, by rfl⟩ : syracuseStep 855031 = 1282547) B1282547
theorem B1281035 : Blo 758332 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B1707083 : Blo 758332 1707083 := bstep (se 1 (by rfl) ⟨1280312, by rfl⟩ : syracuseStep 1707083 = 2560625) B2560625
theorem B2165849 : Blo 758332 2165849 := bstep (se 2 (by rfl) ⟨812193, by rfl⟩ : syracuseStep 2165849 = 1624387) B1624387
theorem B2886749 : Blo 758332 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B1707137 : Blo 758332 1707137 := bstep (se 2 (by rfl) ⟨640176, by rfl⟩ : syracuseStep 1707137 = 1280353) B1280353
theorem B1281163 : Blo 758332 1281163 := bstep (se 1 (by rfl) ⟨960872, by rfl⟩ : syracuseStep 1281163 = 1921745) B1921745
theorem B1445015 : Blo 758332 1445015 := bstep (se 1 (by rfl) ⟨1083761, by rfl⟩ : syracuseStep 1445015 = 2167523) B2167523
theorem B855211 : Blo 758332 855211 := bstep (se 1 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 855211 = 1282817) B1282817
theorem B855319 : Blo 758332 855319 := bstep (se 1 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 855319 = 1282979) B1282979
theorem B1281305 : Blo 758332 1281305 := bstep (se 2 (by rfl) ⟨480489, by rfl⟩ : syracuseStep 1281305 = 960979) B960979
theorem B1084747 : Blo 758332 1084747 := bstep (se 1 (by rfl) ⟨813560, by rfl⟩ : syracuseStep 1084747 = 1627121) B1627121
theorem B1707353 : Blo 758332 1707353 := bstep (se 2 (by rfl) ⟨640257, by rfl⟩ : syracuseStep 1707353 = 1280515) B1280515
theorem B2559383 : Blo 758332 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B5344663 : Blo 758332 5344663 := bstep (se 1 (by rfl) ⟨4008497, by rfl⟩ : syracuseStep 5344663 = 8016995) B8016995
theorem B1281433 : Blo 758332 1281433 := bstep (se 2 (by rfl) ⟨480537, by rfl⟩ : syracuseStep 1281433 = 961075) B961075
theorem B1445273 : Blo 758332 1445273 := bstep (se 2 (by rfl) ⟨541977, by rfl⟩ : syracuseStep 1445273 = 1083955) B1083955
theorem B5475761 : Blo 758332 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B1707443 : Blo 758332 1707443 := bstep (se 1 (by rfl) ⟨1280582, by rfl⟩ : syracuseStep 1707443 = 2561165) B2561165
theorem B855499 : Blo 758332 855499 := bstep (se 1 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 855499 = 1283249) B1283249
theorem B43814357 : Blo 758332 43814357 := bstep (se 7 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 43814357 = 1026899) B1026899
theorem B1707479 : Blo 758332 1707479 := bstep (se 1 (by rfl) ⟨1280609, by rfl⟩ : syracuseStep 1707479 = 2561219) B2561219
theorem B855607 : Blo 758332 855607 := bstep (se 1 (by rfl) ⟨641705, by rfl⟩ : syracuseStep 855607 = 1283411) B1283411
theorem B1707659 : Blo 758332 1707659 := bstep (se 1 (by rfl) ⟨1280744, by rfl⟩ : syracuseStep 1707659 = 2561489) B2561489
theorem B1707713 : Blo 758332 1707713 := bstep (se 2 (by rfl) ⟨640392, by rfl⟩ : syracuseStep 1707713 = 1280785) B1280785
theorem B855787 : Blo 758332 855787 := bstep (se 1 (by rfl) ⟨641840, by rfl⟩ : syracuseStep 855787 = 1283681) B1283681
theorem B2887447 : Blo 758332 2887447 := bstep (se 1 (by rfl) ⟨2165585, by rfl⟩ : syracuseStep 2887447 = 4331171) B4331171
theorem B1445683 : Blo 758332 1445683 := bstep (se 1 (by rfl) ⟨1084262, by rfl⟩ : syracuseStep 1445683 = 2168525) B2168525
theorem B855895 : Blo 758332 855895 := bstep (se 1 (by rfl) ⟨641921, by rfl⟩ : syracuseStep 855895 = 1283843) B1283843
theorem B2166679 : Blo 758332 2166679 := bstep (se 1 (by rfl) ⟨1625009, by rfl⟩ : syracuseStep 2166679 = 3250019) B3250019
theorem B1707929 : Blo 758332 1707929 := bstep (se 2 (by rfl) ⟨640473, by rfl⟩ : syracuseStep 1707929 = 1280947) B1280947
theorem B2559923 : Blo 758332 2559923 := bstep (se 1 (by rfl) ⟨1919942, by rfl⟩ : syracuseStep 2559923 = 3839885) B3839885
theorem B4329395 : Blo 758332 4329395 := bstep (se 1 (by rfl) ⟨3247046, by rfl⟩ : syracuseStep 4329395 = 6494093) B6494093
theorem B6492109 : Blo 758332 6492109 := bstep (se 3 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 6492109 = 2434541) B2434541
theorem B1282007 : Blo 758332 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B1708019 : Blo 758332 1708019 := bstep (se 1 (by rfl) ⟨1281014, by rfl⟩ : syracuseStep 1708019 = 2562029) B2562029
theorem B856075 : Blo 758332 856075 := bstep (se 1 (by rfl) ⟨642056, by rfl⟩ : syracuseStep 856075 = 1284113) B1284113
theorem B1708055 : Blo 758332 1708055 := bstep (se 1 (by rfl) ⟨1281041, by rfl⟩ : syracuseStep 1708055 = 2562083) B2562083
theorem B1282135 : Blo 758332 1282135 := bstep (se 1 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 1282135 = 1923203) B1923203
theorem B856183 : Blo 758332 856183 := bstep (se 1 (by rfl) ⟨642137, by rfl⟩ : syracuseStep 856183 = 1284275) B1284275
theorem B2560193 : Blo 758332 2560193 := bstep (se 2 (by rfl) ⟨960072, by rfl⟩ : syracuseStep 2560193 = 1920145) B1920145
theorem B1708235 : Blo 758332 1708235 := bstep (se 1 (by rfl) ⟨1281176, by rfl⟩ : syracuseStep 1708235 = 2562353) B2562353
theorem B1708289 : Blo 758332 1708289 := bstep (se 2 (by rfl) ⟨640608, by rfl⟩ : syracuseStep 1708289 = 1281217) B1281217
theorem B1446169 : Blo 758332 1446169 := bstep (se 2 (by rfl) ⟨542313, by rfl⟩ : syracuseStep 1446169 = 1084627) B1084627
theorem B856363 : Blo 758332 856363 := bstep (se 1 (by rfl) ⟨642272, by rfl⟩ : syracuseStep 856363 = 1284545) B1284545
theorem B3248515 : Blo 758332 3248515 := bstep (se 1 (by rfl) ⟨2436386, by rfl⟩ : syracuseStep 3248515 = 4872773) B4872773
theorem B856471 : Blo 758332 856471 := bstep (se 1 (by rfl) ⟨642353, by rfl⟩ : syracuseStep 856471 = 1284707) B1284707
theorem B1544599 : Blo 758332 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B6263219 : Blo 758332 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B1708505 : Blo 758332 1708505 := bstep (se 2 (by rfl) ⟨640689, by rfl⟩ : syracuseStep 1708505 = 1281379) B1281379
theorem B2888237 : Blo 758332 2888237 := bstep (se 3 (by rfl) ⟨541544, by rfl⟩ : syracuseStep 2888237 = 1083089) B1083089
theorem B1708595 : Blo 758332 1708595 := bstep (se 1 (by rfl) ⟨1281446, by rfl⟩ : syracuseStep 1708595 = 2562893) B2562893
theorem B758347 : Blo 758332 758347 := bstep (se 1 (by rfl) ⟨568760, by rfl⟩ : syracuseStep 758347 = 1137521) B1137521
theorem B856651 : Blo 758332 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B758359 : Blo 758332 758359 := bstep (se 1 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 758359 = 1137539) B1137539
theorem B1708631 : Blo 758332 1708631 := bstep (se 1 (by rfl) ⟨1281473, by rfl⟩ : syracuseStep 1708631 = 2562947) B2562947
theorem B1217111 : Blo 758332 1217111 := bstep (se 1 (by rfl) ⟨912833, by rfl⟩ : syracuseStep 1217111 = 1825667) B1825667
theorem B758379 : Blo 758332 758379 := bstep (se 1 (by rfl) ⟨568784, by rfl⟩ : syracuseStep 758379 = 1137569) B1137569
theorem B758391 : Blo 758332 758391 := bstep (se 1 (by rfl) ⟨568793, by rfl⟩ : syracuseStep 758391 = 1137587) B1137587
theorem B758411 : Blo 758332 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B758423 : Blo 758332 758423 := bstep (se 1 (by rfl) ⟨568817, by rfl⟩ : syracuseStep 758423 = 1137635) B1137635
theorem B758443 : Blo 758332 758443 := bstep (se 1 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 758443 = 1137665) B1137665
theorem B758455 : Blo 758332 758455 := bstep (se 1 (by rfl) ⟨568841, by rfl⟩ : syracuseStep 758455 = 1137683) B1137683
theorem B856759 : Blo 758332 856759 := bstep (se 1 (by rfl) ⟨642569, by rfl⟩ : syracuseStep 856759 = 1285139) B1285139
theorem B758475 : Blo 758332 758475 := bstep (se 1 (by rfl) ⟨568856, by rfl⟩ : syracuseStep 758475 = 1137713) B1137713
theorem B1282763 : Blo 758332 1282763 := bstep (se 1 (by rfl) ⟨962072, by rfl⟩ : syracuseStep 1282763 = 1924145) B1924145
theorem B2167499 : Blo 758332 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B758487 : Blo 758332 758487 := bstep (se 1 (by rfl) ⟨568865, by rfl⟩ : syracuseStep 758487 = 1137731) B1137731
theorem B4625113 : Blo 758332 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B2560733 : Blo 758332 2560733 := bstep (se 3 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 2560733 = 960275) B960275
theorem B758507 : Blo 758332 758507 := bstep (se 1 (by rfl) ⟨568880, by rfl⟩ : syracuseStep 758507 = 1137761) B1137761
theorem B758519 : Blo 758332 758519 := bstep (se 1 (by rfl) ⟨568889, by rfl⟩ : syracuseStep 758519 = 1137779) B1137779
theorem B758539 : Blo 758332 758539 := bstep (se 1 (by rfl) ⟨568904, by rfl⟩ : syracuseStep 758539 = 1137809) B1137809
theorem B1708811 : Blo 758332 1708811 := bstep (se 1 (by rfl) ⟨1281608, by rfl⟩ : syracuseStep 1708811 = 2563217) B2563217
theorem B758551 : Blo 758332 758551 := bstep (se 1 (by rfl) ⟨568913, by rfl⟩ : syracuseStep 758551 = 1137827) B1137827
theorem B758571 : Blo 758332 758571 := bstep (se 1 (by rfl) ⟨568928, by rfl⟩ : syracuseStep 758571 = 1137857) B1137857
theorem B758583 : Blo 758332 758583 := bstep (se 1 (by rfl) ⟨568937, by rfl⟩ : syracuseStep 758583 = 1137875) B1137875
theorem B1708865 : Blo 758332 1708865 := bstep (se 2 (by rfl) ⟨640824, by rfl⟩ : syracuseStep 1708865 = 1281649) B1281649
theorem B758603 : Blo 758332 758603 := bstep (se 1 (by rfl) ⟨568952, by rfl⟩ : syracuseStep 758603 = 1137905) B1137905
theorem B1282891 : Blo 758332 1282891 := bstep (se 1 (by rfl) ⟨962168, by rfl⟩ : syracuseStep 1282891 = 1924337) B1924337
theorem B1446731 : Blo 758332 1446731 := bstep (se 1 (by rfl) ⟨1085048, by rfl⟩ : syracuseStep 1446731 = 2170097) B2170097
theorem B758615 : Blo 758332 758615 := bstep (se 1 (by rfl) ⟨568961, by rfl⟩ : syracuseStep 758615 = 1137923) B1137923
theorem B758635 : Blo 758332 758635 := bstep (se 1 (by rfl) ⟨568976, by rfl⟩ : syracuseStep 758635 = 1137953) B1137953
theorem B856939 : Blo 758332 856939 := bstep (se 1 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 856939 = 1285409) B1285409
theorem B758647 : Blo 758332 758647 := bstep (se 1 (by rfl) ⟨568985, by rfl⟩ : syracuseStep 758647 = 1137971) B1137971
theorem B758667 : Blo 758332 758667 := bstep (se 1 (by rfl) ⟨569000, by rfl⟩ : syracuseStep 758667 = 1138001) B1138001
theorem B758679 : Blo 758332 758679 := bstep (se 1 (by rfl) ⟨569009, by rfl⟩ : syracuseStep 758679 = 1138019) B1138019
theorem B758699 : Blo 758332 758699 := bstep (se 1 (by rfl) ⟨569024, by rfl⟩ : syracuseStep 758699 = 1138049) B1138049
theorem B758711 : Blo 758332 758711 := bstep (se 1 (by rfl) ⟨569033, by rfl⟩ : syracuseStep 758711 = 1138067) B1138067
theorem B758731 : Blo 758332 758731 := bstep (se 1 (by rfl) ⟨569048, by rfl⟩ : syracuseStep 758731 = 1138097) B1138097
theorem B758743 : Blo 758332 758743 := bstep (se 1 (by rfl) ⟨569057, by rfl⟩ : syracuseStep 758743 = 1138115) B1138115
theorem B857047 : Blo 758332 857047 := bstep (se 1 (by rfl) ⟨642785, by rfl⟩ : syracuseStep 857047 = 1285571) B1285571
theorem B1283033 : Blo 758332 1283033 := bstep (se 2 (by rfl) ⟨481137, by rfl⟩ : syracuseStep 1283033 = 962275) B962275
theorem B758763 : Blo 758332 758763 := bstep (se 1 (by rfl) ⟨569072, by rfl⟩ : syracuseStep 758763 = 1138145) B1138145
theorem B758775 : Blo 758332 758775 := bstep (se 1 (by rfl) ⟨569081, by rfl⟩ : syracuseStep 758775 = 1138163) B1138163
theorem B1446913 : Blo 758332 1446913 := bstep (se 2 (by rfl) ⟨542592, by rfl⟩ : syracuseStep 1446913 = 1085185) B1085185
theorem B758795 : Blo 758332 758795 := bstep (se 1 (by rfl) ⟨569096, by rfl⟩ : syracuseStep 758795 = 1138193) B1138193
theorem B758807 : Blo 758332 758807 := bstep (se 1 (by rfl) ⟨569105, by rfl⟩ : syracuseStep 758807 = 1138211) B1138211
theorem B1709081 : Blo 758332 1709081 := bstep (se 2 (by rfl) ⟨640905, by rfl⟩ : syracuseStep 1709081 = 1281811) B1281811
theorem B758827 : Blo 758332 758827 := bstep (se 1 (by rfl) ⟨569120, by rfl⟩ : syracuseStep 758827 = 1138241) B1138241
theorem B758839 : Blo 758332 758839 := bstep (se 1 (by rfl) ⟨569129, by rfl⟩ : syracuseStep 758839 = 1138259) B1138259
theorem B758859 : Blo 758332 758859 := bstep (se 1 (by rfl) ⟨569144, by rfl⟩ : syracuseStep 758859 = 1138289) B1138289
theorem B13866059 : Blo 758332 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B758871 : Blo 758332 758871 := bstep (se 1 (by rfl) ⟨569153, by rfl⟩ : syracuseStep 758871 = 1138307) B1138307
theorem B1283161 : Blo 758332 1283161 := bstep (se 2 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 1283161 = 962371) B962371
theorem B758891 : Blo 758332 758891 := bstep (se 1 (by rfl) ⟨569168, by rfl⟩ : syracuseStep 758891 = 1138337) B1138337
theorem B1709171 : Blo 758332 1709171 := bstep (se 1 (by rfl) ⟨1281878, by rfl⟩ : syracuseStep 1709171 = 2563757) B2563757
theorem B758903 : Blo 758332 758903 := bstep (se 1 (by rfl) ⟨569177, by rfl⟩ : syracuseStep 758903 = 1138355) B1138355
theorem B758923 : Blo 758332 758923 := bstep (se 1 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 758923 = 1138385) B1138385
theorem B857227 : Blo 758332 857227 := bstep (se 1 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 857227 = 1285841) B1285841
theorem B758935 : Blo 758332 758935 := bstep (se 1 (by rfl) ⟨569201, by rfl⟩ : syracuseStep 758935 = 1138403) B1138403
theorem B1709207 : Blo 758332 1709207 := bstep (se 1 (by rfl) ⟨1281905, by rfl⟩ : syracuseStep 1709207 = 2563811) B2563811
theorem B758955 : Blo 758332 758955 := bstep (se 1 (by rfl) ⟨569216, by rfl⟩ : syracuseStep 758955 = 1138433) B1138433
theorem B758967 : Blo 758332 758967 := bstep (se 1 (by rfl) ⟨569225, by rfl⟩ : syracuseStep 758967 = 1138451) B1138451
theorem B1545409 : Blo 758332 1545409 := bstep (se 2 (by rfl) ⟨579528, by rfl⟩ : syracuseStep 1545409 = 1159057) B1159057
theorem B758987 : Blo 758332 758987 := bstep (se 1 (by rfl) ⟨569240, by rfl⟩ : syracuseStep 758987 = 1138481) B1138481
theorem B758999 : Blo 758332 758999 := bstep (se 1 (by rfl) ⟨569249, by rfl⟩ : syracuseStep 758999 = 1138499) B1138499
theorem B759019 : Blo 758332 759019 := bstep (se 1 (by rfl) ⟨569264, by rfl⟩ : syracuseStep 759019 = 1138529) B1138529
theorem B759031 : Blo 758332 759031 := bstep (se 1 (by rfl) ⟨569273, by rfl⟩ : syracuseStep 759031 = 1138547) B1138547
theorem B857335 : Blo 758332 857335 := bstep (se 1 (by rfl) ⟨643001, by rfl⟩ : syracuseStep 857335 = 1286003) B1286003
theorem B6493445 : Blo 758332 6493445 := bstep (se 4 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 6493445 = 1217521) B1217521
theorem B759051 : Blo 758332 759051 := bstep (se 1 (by rfl) ⟨569288, by rfl⟩ : syracuseStep 759051 = 1138577) B1138577
theorem B759063 : Blo 758332 759063 := bstep (se 1 (by rfl) ⟨569297, by rfl⟩ : syracuseStep 759063 = 1138595) B1138595
theorem B759083 : Blo 758332 759083 := bstep (se 1 (by rfl) ⟨569312, by rfl⟩ : syracuseStep 759083 = 1138625) B1138625
theorem B759095 : Blo 758332 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B759115 : Blo 758332 759115 := bstep (se 1 (by rfl) ⟨569336, by rfl⟩ : syracuseStep 759115 = 1138673) B1138673
theorem B1709387 : Blo 758332 1709387 := bstep (se 1 (by rfl) ⟨1282040, by rfl⟩ : syracuseStep 1709387 = 2564081) B2564081
theorem B759127 : Blo 758332 759127 := bstep (se 1 (by rfl) ⟨569345, by rfl⟩ : syracuseStep 759127 = 1138691) B1138691
theorem B4330853 : Blo 758332 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B759147 : Blo 758332 759147 := bstep (se 1 (by rfl) ⟨569360, by rfl⟩ : syracuseStep 759147 = 1138721) B1138721
theorem B759159 : Blo 758332 759159 := bstep (se 1 (by rfl) ⟨569369, by rfl⟩ : syracuseStep 759159 = 1138739) B1138739
theorem B1709441 : Blo 758332 1709441 := bstep (se 2 (by rfl) ⟨641040, by rfl⟩ : syracuseStep 1709441 = 1282081) B1282081
theorem B759179 : Blo 758332 759179 := bstep (se 1 (by rfl) ⟨569384, by rfl⟩ : syracuseStep 759179 = 1138769) B1138769
theorem B759191 : Blo 758332 759191 := bstep (se 1 (by rfl) ⟨569393, by rfl⟩ : syracuseStep 759191 = 1138787) B1138787
theorem B759211 : Blo 758332 759211 := bstep (se 1 (by rfl) ⟨569408, by rfl⟩ : syracuseStep 759211 = 1138817) B1138817
theorem B857515 : Blo 758332 857515 := bstep (se 1 (by rfl) ⟨643136, by rfl⟩ : syracuseStep 857515 = 1286273) B1286273
theorem B759223 : Blo 758332 759223 := bstep (se 1 (by rfl) ⟨569417, by rfl⟩ : syracuseStep 759223 = 1138835) B1138835
theorem B759243 : Blo 758332 759243 := bstep (se 1 (by rfl) ⟨569432, by rfl⟩ : syracuseStep 759243 = 1138865) B1138865
theorem B759255 : Blo 758332 759255 := bstep (se 1 (by rfl) ⟨569441, by rfl⟩ : syracuseStep 759255 = 1138883) B1138883
theorem B759275 : Blo 758332 759275 := bstep (se 1 (by rfl) ⟨569456, by rfl⟩ : syracuseStep 759275 = 1138913) B1138913
theorem B759287 : Blo 758332 759287 := bstep (se 1 (by rfl) ⟨569465, by rfl⟩ : syracuseStep 759287 = 1138931) B1138931
theorem B759307 : Blo 758332 759307 := bstep (se 1 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 759307 = 1138961) B1138961
theorem B759319 : Blo 758332 759319 := bstep (se 1 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 759319 = 1138979) B1138979
theorem B857623 : Blo 758332 857623 := bstep (se 1 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 857623 = 1286435) B1286435
theorem B759339 : Blo 758332 759339 := bstep (se 1 (by rfl) ⟨569504, by rfl⟩ : syracuseStep 759339 = 1139009) B1139009
theorem B759351 : Blo 758332 759351 := bstep (se 1 (by rfl) ⟨569513, by rfl⟩ : syracuseStep 759351 = 1139027) B1139027
theorem B759371 : Blo 758332 759371 := bstep (se 1 (by rfl) ⟨569528, by rfl⟩ : syracuseStep 759371 = 1139057) B1139057
theorem B759383 : Blo 758332 759383 := bstep (se 1 (by rfl) ⟨569537, by rfl⟩ : syracuseStep 759383 = 1139075) B1139075
theorem B1709657 : Blo 758332 1709657 := bstep (se 2 (by rfl) ⟨641121, by rfl⟩ : syracuseStep 1709657 = 1282243) B1282243
theorem B759403 : Blo 758332 759403 := bstep (se 1 (by rfl) ⟨569552, by rfl⟩ : syracuseStep 759403 = 1139105) B1139105
theorem B759415 : Blo 758332 759415 := bstep (se 1 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 759415 = 1139123) B1139123
theorem B759435 : Blo 758332 759435 := bstep (se 1 (by rfl) ⟨569576, by rfl⟩ : syracuseStep 759435 = 1139153) B1139153
theorem B759447 : Blo 758332 759447 := bstep (se 1 (by rfl) ⟨569585, by rfl⟩ : syracuseStep 759447 = 1139171) B1139171
theorem B1283735 : Blo 758332 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B759467 : Blo 758332 759467 := bstep (se 1 (by rfl) ⟨569600, by rfl⟩ : syracuseStep 759467 = 1139201) B1139201
theorem B1709747 : Blo 758332 1709747 := bstep (se 1 (by rfl) ⟨1282310, by rfl⟩ : syracuseStep 1709747 = 2564621) B2564621
theorem B759479 : Blo 758332 759479 := bstep (se 1 (by rfl) ⟨569609, by rfl⟩ : syracuseStep 759479 = 1139219) B1139219
theorem B759499 : Blo 758332 759499 := bstep (se 1 (by rfl) ⟨569624, by rfl⟩ : syracuseStep 759499 = 1139249) B1139249
theorem B759511 : Blo 758332 759511 := bstep (se 1 (by rfl) ⟨569633, by rfl⟩ : syracuseStep 759511 = 1139267) B1139267
theorem B1709783 : Blo 758332 1709783 := bstep (se 1 (by rfl) ⟨1282337, by rfl⟩ : syracuseStep 1709783 = 2564675) B2564675
theorem B759531 : Blo 758332 759531 := bstep (se 1 (by rfl) ⟨569648, by rfl⟩ : syracuseStep 759531 = 1139297) B1139297
theorem B759543 : Blo 758332 759543 := bstep (se 1 (by rfl) ⟨569657, by rfl⟩ : syracuseStep 759543 = 1139315) B1139315
theorem B759563 : Blo 758332 759563 := bstep (se 1 (by rfl) ⟨569672, by rfl⟩ : syracuseStep 759563 = 1139345) B1139345
theorem B759575 : Blo 758332 759575 := bstep (se 1 (by rfl) ⟨569681, by rfl⟩ : syracuseStep 759575 = 1139363) B1139363
theorem B1283863 : Blo 758332 1283863 := bstep (se 1 (by rfl) ⟨962897, by rfl⟩ : syracuseStep 1283863 = 1925795) B1925795
theorem B759595 : Blo 758332 759595 := bstep (se 1 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 759595 = 1139393) B1139393
theorem B759607 : Blo 758332 759607 := bstep (se 1 (by rfl) ⟨569705, by rfl⟩ : syracuseStep 759607 = 1139411) B1139411
theorem B2561867 : Blo 758332 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B759627 : Blo 758332 759627 := bstep (se 1 (by rfl) ⟨569720, by rfl⟩ : syracuseStep 759627 = 1139441) B1139441
theorem B759639 : Blo 758332 759639 := bstep (se 1 (by rfl) ⟨569729, by rfl⟩ : syracuseStep 759639 = 1139459) B1139459
theorem B31135589 : Blo 758332 31135589 := bstep (se 4 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 31135589 = 5837923) B5837923
theorem B759659 : Blo 758332 759659 := bstep (se 1 (by rfl) ⟨569744, by rfl⟩ : syracuseStep 759659 = 1139489) B1139489
theorem B759671 : Blo 758332 759671 := bstep (se 1 (by rfl) ⟨569753, by rfl⟩ : syracuseStep 759671 = 1139507) B1139507
theorem B759691 : Blo 758332 759691 := bstep (se 1 (by rfl) ⟨569768, by rfl⟩ : syracuseStep 759691 = 1139537) B1139537
theorem B1709963 : Blo 758332 1709963 := bstep (se 1 (by rfl) ⟨1282472, by rfl⟩ : syracuseStep 1709963 = 2564945) B2564945
theorem B759703 : Blo 758332 759703 := bstep (se 1 (by rfl) ⟨569777, by rfl⟩ : syracuseStep 759703 = 1139555) B1139555
theorem B759723 : Blo 758332 759723 := bstep (se 1 (by rfl) ⟨569792, by rfl⟩ : syracuseStep 759723 = 1139585) B1139585
theorem B759735 : Blo 758332 759735 := bstep (se 1 (by rfl) ⟨569801, by rfl⟩ : syracuseStep 759735 = 1139603) B1139603
theorem B1710017 : Blo 758332 1710017 := bstep (se 2 (by rfl) ⟨641256, by rfl⟩ : syracuseStep 1710017 = 1282513) B1282513
theorem B2889665 : Blo 758332 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B759755 : Blo 758332 759755 := bstep (se 1 (by rfl) ⟨569816, by rfl⟩ : syracuseStep 759755 = 1139633) B1139633
theorem B759767 : Blo 758332 759767 := bstep (se 1 (by rfl) ⟨569825, by rfl⟩ : syracuseStep 759767 = 1139651) B1139651
theorem B759787 : Blo 758332 759787 := bstep (se 1 (by rfl) ⟨569840, by rfl⟩ : syracuseStep 759787 = 1139681) B1139681
theorem B759799 : Blo 758332 759799 := bstep (se 1 (by rfl) ⟨569849, by rfl⟩ : syracuseStep 759799 = 1139699) B1139699
theorem B759819 : Blo 758332 759819 := bstep (se 1 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 759819 = 1139729) B1139729
theorem B759831 : Blo 758332 759831 := bstep (se 1 (by rfl) ⟨569873, by rfl⟩ : syracuseStep 759831 = 1139747) B1139747
theorem B759851 : Blo 758332 759851 := bstep (se 1 (by rfl) ⟨569888, by rfl⟩ : syracuseStep 759851 = 1139777) B1139777
theorem B759863 : Blo 758332 759863 := bstep (se 1 (by rfl) ⟨569897, by rfl⟩ : syracuseStep 759863 = 1139795) B1139795
theorem B4626497 : Blo 758332 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B759883 : Blo 758332 759883 := bstep (se 1 (by rfl) ⟨569912, by rfl⟩ : syracuseStep 759883 = 1139825) B1139825
theorem B759895 : Blo 758332 759895 := bstep (se 1 (by rfl) ⟨569921, by rfl⟩ : syracuseStep 759895 = 1139843) B1139843
theorem B2562137 : Blo 758332 2562137 := bstep (se 2 (by rfl) ⟨960801, by rfl⟩ : syracuseStep 2562137 = 1921603) B1921603
theorem B759915 : Blo 758332 759915 := bstep (se 1 (by rfl) ⟨569936, by rfl⟩ : syracuseStep 759915 = 1139873) B1139873
theorem B759927 : Blo 758332 759927 := bstep (se 1 (by rfl) ⟨569945, by rfl⟩ : syracuseStep 759927 = 1139891) B1139891
theorem B759947 : Blo 758332 759947 := bstep (se 1 (by rfl) ⟨569960, by rfl⟩ : syracuseStep 759947 = 1139921) B1139921
theorem B759959 : Blo 758332 759959 := bstep (se 1 (by rfl) ⟨569969, by rfl⟩ : syracuseStep 759959 = 1139939) B1139939
theorem B3250327 : Blo 758332 3250327 := bstep (se 1 (by rfl) ⟨2437745, by rfl⟩ : syracuseStep 3250327 = 4875491) B4875491
theorem B1710233 : Blo 758332 1710233 := bstep (se 2 (by rfl) ⟨641337, by rfl⟩ : syracuseStep 1710233 = 1282675) B1282675
theorem B759979 : Blo 758332 759979 := bstep (se 1 (by rfl) ⟨569984, by rfl⟩ : syracuseStep 759979 = 1139969) B1139969
theorem B759991 : Blo 758332 759991 := bstep (se 1 (by rfl) ⟨569993, by rfl⟩ : syracuseStep 759991 = 1139987) B1139987
theorem B760011 : Blo 758332 760011 := bstep (se 1 (by rfl) ⟨570008, by rfl⟩ : syracuseStep 760011 = 1140017) B1140017
theorem B760023 : Blo 758332 760023 := bstep (se 1 (by rfl) ⟨570017, by rfl⟩ : syracuseStep 760023 = 1140035) B1140035
theorem B5478617 : Blo 758332 5478617 := bstep (se 2 (by rfl) ⟨2054481, by rfl⟩ : syracuseStep 5478617 = 4108963) B4108963
theorem B760043 : Blo 758332 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B1710323 : Blo 758332 1710323 := bstep (se 1 (by rfl) ⟨1282742, by rfl⟩ : syracuseStep 1710323 = 2565485) B2565485
theorem B760055 : Blo 758332 760055 := bstep (se 1 (by rfl) ⟨570041, by rfl⟩ : syracuseStep 760055 = 1140083) B1140083
theorem B760075 : Blo 758332 760075 := bstep (se 1 (by rfl) ⟨570056, by rfl⟩ : syracuseStep 760075 = 1140113) B1140113
theorem B760087 : Blo 758332 760087 := bstep (se 1 (by rfl) ⟨570065, by rfl⟩ : syracuseStep 760087 = 1140131) B1140131
theorem B1710359 : Blo 758332 1710359 := bstep (se 1 (by rfl) ⟨1282769, by rfl⟩ : syracuseStep 1710359 = 2565539) B2565539
theorem B760107 : Blo 758332 760107 := bstep (se 1 (by rfl) ⟨570080, by rfl⟩ : syracuseStep 760107 = 1140161) B1140161
theorem B760119 : Blo 758332 760119 := bstep (se 1 (by rfl) ⟨570089, by rfl⟩ : syracuseStep 760119 = 1140179) B1140179
theorem B760139 : Blo 758332 760139 := bstep (se 1 (by rfl) ⟨570104, by rfl⟩ : syracuseStep 760139 = 1140209) B1140209
theorem B760151 : Blo 758332 760151 := bstep (se 1 (by rfl) ⟨570113, by rfl⟩ : syracuseStep 760151 = 1140227) B1140227
theorem B760171 : Blo 758332 760171 := bstep (se 1 (by rfl) ⟨570128, by rfl⟩ : syracuseStep 760171 = 1140257) B1140257
theorem B760183 : Blo 758332 760183 := bstep (se 1 (by rfl) ⟨570137, by rfl⟩ : syracuseStep 760183 = 1140275) B1140275
theorem B760203 : Blo 758332 760203 := bstep (se 1 (by rfl) ⟨570152, by rfl⟩ : syracuseStep 760203 = 1140305) B1140305
theorem B1284491 : Blo 758332 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B760215 : Blo 758332 760215 := bstep (se 1 (by rfl) ⟨570161, by rfl⟩ : syracuseStep 760215 = 1140323) B1140323
theorem B760235 : Blo 758332 760235 := bstep (se 1 (by rfl) ⟨570176, by rfl⟩ : syracuseStep 760235 = 1140353) B1140353
theorem B4004275 : Blo 758332 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B760247 : Blo 758332 760247 := bstep (se 1 (by rfl) ⟨570185, by rfl⟩ : syracuseStep 760247 = 1140371) B1140371
theorem B1710539 : Blo 758332 1710539 := bstep (se 1 (by rfl) ⟨1282904, by rfl⟩ : syracuseStep 1710539 = 2565809) B2565809
theorem B760267 : Blo 758332 760267 := bstep (se 1 (by rfl) ⟨570200, by rfl⟩ : syracuseStep 760267 = 1140401) B1140401
theorem B760279 : Blo 758332 760279 := bstep (se 1 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 760279 = 1140419) B1140419
theorem B760299 : Blo 758332 760299 := bstep (se 1 (by rfl) ⟨570224, by rfl⟩ : syracuseStep 760299 = 1140449) B1140449
theorem B760311 : Blo 758332 760311 := bstep (se 1 (by rfl) ⟨570233, by rfl⟩ : syracuseStep 760311 = 1140467) B1140467
theorem B1710593 : Blo 758332 1710593 := bstep (se 2 (by rfl) ⟨641472, by rfl⟩ : syracuseStep 1710593 = 1282945) B1282945
theorem B760331 : Blo 758332 760331 := bstep (se 1 (by rfl) ⟨570248, by rfl⟩ : syracuseStep 760331 = 1140497) B1140497
theorem B1284619 : Blo 758332 1284619 := bstep (se 1 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 1284619 = 1926929) B1926929
theorem B760343 : Blo 758332 760343 := bstep (se 1 (by rfl) ⟨570257, by rfl⟩ : syracuseStep 760343 = 1140515) B1140515
theorem B760363 : Blo 758332 760363 := bstep (se 1 (by rfl) ⟨570272, by rfl⟩ : syracuseStep 760363 = 1140545) B1140545
theorem B760375 : Blo 758332 760375 := bstep (se 1 (by rfl) ⟨570281, by rfl⟩ : syracuseStep 760375 = 1140563) B1140563
theorem B760395 : Blo 758332 760395 := bstep (se 1 (by rfl) ⟨570296, by rfl⟩ : syracuseStep 760395 = 1140593) B1140593
theorem B760407 : Blo 758332 760407 := bstep (se 1 (by rfl) ⟨570305, by rfl⟩ : syracuseStep 760407 = 1140611) B1140611
theorem B760427 : Blo 758332 760427 := bstep (se 1 (by rfl) ⟨570320, by rfl⟩ : syracuseStep 760427 = 1140641) B1140641
theorem B760439 : Blo 758332 760439 := bstep (se 1 (by rfl) ⟨570329, by rfl⟩ : syracuseStep 760439 = 1140659) B1140659
theorem B760459 : Blo 758332 760459 := bstep (se 1 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 760459 = 1140689) B1140689
theorem B760471 : Blo 758332 760471 := bstep (se 1 (by rfl) ⟨570353, by rfl⟩ : syracuseStep 760471 = 1140707) B1140707
theorem B1284761 : Blo 758332 1284761 := bstep (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) B963571
theorem B760491 : Blo 758332 760491 := bstep (se 1 (by rfl) ⟨570368, by rfl⟩ : syracuseStep 760491 = 1140737) B1140737
theorem B760503 : Blo 758332 760503 := bstep (se 1 (by rfl) ⟨570377, by rfl⟩ : syracuseStep 760503 = 1140755) B1140755
theorem B760523 : Blo 758332 760523 := bstep (se 1 (by rfl) ⟨570392, by rfl⟩ : syracuseStep 760523 = 1140785) B1140785
theorem B760535 : Blo 758332 760535 := bstep (se 1 (by rfl) ⟨570401, by rfl⟩ : syracuseStep 760535 = 1140803) B1140803
theorem B1710809 : Blo 758332 1710809 := bstep (se 2 (by rfl) ⟨641553, by rfl⟩ : syracuseStep 1710809 = 1283107) B1283107
theorem B760555 : Blo 758332 760555 := bstep (se 1 (by rfl) ⟨570416, by rfl⟩ : syracuseStep 760555 = 1140833) B1140833
theorem B760567 : Blo 758332 760567 := bstep (se 1 (by rfl) ⟨570425, by rfl⟩ : syracuseStep 760567 = 1140851) B1140851
theorem B760587 : Blo 758332 760587 := bstep (se 1 (by rfl) ⟨570440, by rfl⟩ : syracuseStep 760587 = 1140881) B1140881
theorem B3250961 : Blo 758332 3250961 := bstep (se 2 (by rfl) ⟨1219110, by rfl⟩ : syracuseStep 3250961 = 2438221) B2438221
theorem B2562839 : Blo 758332 2562839 := bstep (se 1 (by rfl) ⟨1922129, by rfl⟩ : syracuseStep 2562839 = 3844259) B3844259
theorem B760599 : Blo 758332 760599 := bstep (se 1 (by rfl) ⟨570449, by rfl⟩ : syracuseStep 760599 = 1140899) B1140899
theorem B1284889 : Blo 758332 1284889 := bstep (se 2 (by rfl) ⟨481833, by rfl⟩ : syracuseStep 1284889 = 963667) B963667
theorem B760619 : Blo 758332 760619 := bstep (se 1 (by rfl) ⟨570464, by rfl⟩ : syracuseStep 760619 = 1140929) B1140929
theorem B1710899 : Blo 758332 1710899 := bstep (se 1 (by rfl) ⟨1283174, by rfl⟩ : syracuseStep 1710899 = 2566349) B2566349
theorem B760631 : Blo 758332 760631 := bstep (se 1 (by rfl) ⟨570473, by rfl⟩ : syracuseStep 760631 = 1140947) B1140947
theorem B760651 : Blo 758332 760651 := bstep (se 1 (by rfl) ⟨570488, by rfl⟩ : syracuseStep 760651 = 1140977) B1140977
theorem B1710935 : Blo 758332 1710935 := bstep (se 1 (by rfl) ⟨1283201, by rfl⟩ : syracuseStep 1710935 = 2566403) B2566403
theorem B760663 : Blo 758332 760663 := bstep (se 1 (by rfl) ⟨570497, by rfl⟩ : syracuseStep 760663 = 1140995) B1140995
theorem B760683 : Blo 758332 760683 := bstep (se 1 (by rfl) ⟨570512, by rfl⟩ : syracuseStep 760683 = 1141025) B1141025
theorem B760695 : Blo 758332 760695 := bstep (se 1 (by rfl) ⟨570521, by rfl⟩ : syracuseStep 760695 = 1141043) B1141043
theorem B760715 : Blo 758332 760715 := bstep (se 1 (by rfl) ⟨570536, by rfl⟩ : syracuseStep 760715 = 1141073) B1141073
theorem B760727 : Blo 758332 760727 := bstep (se 1 (by rfl) ⟨570545, by rfl⟩ : syracuseStep 760727 = 1141091) B1141091
theorem B760747 : Blo 758332 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B760759 : Blo 758332 760759 := bstep (se 1 (by rfl) ⟨570569, by rfl⟩ : syracuseStep 760759 = 1141139) B1141139
theorem B760779 : Blo 758332 760779 := bstep (se 1 (by rfl) ⟨570584, by rfl⟩ : syracuseStep 760779 = 1141169) B1141169
theorem B760791 : Blo 758332 760791 := bstep (se 1 (by rfl) ⟨570593, by rfl⟩ : syracuseStep 760791 = 1141187) B1141187
theorem B760811 : Blo 758332 760811 := bstep (se 1 (by rfl) ⟨570608, by rfl⟩ : syracuseStep 760811 = 1141217) B1141217
theorem B760823 : Blo 758332 760823 := bstep (se 1 (by rfl) ⟨570617, by rfl⟩ : syracuseStep 760823 = 1141235) B1141235
theorem B1711115 : Blo 758332 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B760843 : Blo 758332 760843 := bstep (se 1 (by rfl) ⟨570632, by rfl⟩ : syracuseStep 760843 = 1141265) B1141265
theorem B760855 : Blo 758332 760855 := bstep (se 1 (by rfl) ⟨570641, by rfl⟩ : syracuseStep 760855 = 1141283) B1141283
theorem B760875 : Blo 758332 760875 := bstep (se 1 (by rfl) ⟨570656, by rfl⟩ : syracuseStep 760875 = 1141313) B1141313
theorem B760887 : Blo 758332 760887 := bstep (se 1 (by rfl) ⟨570665, by rfl⟩ : syracuseStep 760887 = 1141331) B1141331
theorem B1711169 : Blo 758332 1711169 := bstep (se 2 (by rfl) ⟨641688, by rfl⟩ : syracuseStep 1711169 = 1283377) B1283377
theorem B760907 : Blo 758332 760907 := bstep (se 1 (by rfl) ⟨570680, by rfl⟩ : syracuseStep 760907 = 1141361) B1141361
theorem B760919 : Blo 758332 760919 := bstep (se 1 (by rfl) ⟨570689, by rfl⟩ : syracuseStep 760919 = 1141379) B1141379
theorem B2169949 : Blo 758332 2169949 := bstep (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) B813731
theorem B760939 : Blo 758332 760939 := bstep (se 1 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 760939 = 1141409) B1141409
theorem B760951 : Blo 758332 760951 := bstep (se 1 (by rfl) ⟨570713, by rfl⟩ : syracuseStep 760951 = 1141427) B1141427
theorem B760971 : Blo 758332 760971 := bstep (se 1 (by rfl) ⟨570728, by rfl⟩ : syracuseStep 760971 = 1141457) B1141457
theorem B760983 : Blo 758332 760983 := bstep (se 1 (by rfl) ⟨570737, by rfl⟩ : syracuseStep 760983 = 1141475) B1141475
theorem B761003 : Blo 758332 761003 := bstep (se 1 (by rfl) ⟨570752, by rfl⟩ : syracuseStep 761003 = 1141505) B1141505
theorem B761015 : Blo 758332 761015 := bstep (se 1 (by rfl) ⟨570761, by rfl⟩ : syracuseStep 761015 = 1141523) B1141523
theorem B761035 : Blo 758332 761035 := bstep (se 1 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 761035 = 1141553) B1141553
theorem B761047 : Blo 758332 761047 := bstep (se 1 (by rfl) ⟨570785, by rfl⟩ : syracuseStep 761047 = 1141571) B1141571
theorem B761067 : Blo 758332 761067 := bstep (se 1 (by rfl) ⟨570800, by rfl⟩ : syracuseStep 761067 = 1141601) B1141601
theorem B761079 : Blo 758332 761079 := bstep (se 1 (by rfl) ⟨570809, by rfl⟩ : syracuseStep 761079 = 1141619) B1141619
theorem B761099 : Blo 758332 761099 := bstep (se 1 (by rfl) ⟨570824, by rfl⟩ : syracuseStep 761099 = 1141649) B1141649
theorem B761111 : Blo 758332 761111 := bstep (se 1 (by rfl) ⟨570833, by rfl⟩ : syracuseStep 761111 = 1141667) B1141667
theorem B1711385 : Blo 758332 1711385 := bstep (se 2 (by rfl) ⟨641769, by rfl⟩ : syracuseStep 1711385 = 1283539) B1283539
theorem B761131 : Blo 758332 761131 := bstep (se 1 (by rfl) ⟨570848, by rfl⟩ : syracuseStep 761131 = 1141697) B1141697
theorem B2563379 : Blo 758332 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B761143 : Blo 758332 761143 := bstep (se 1 (by rfl) ⟨570857, by rfl⟩ : syracuseStep 761143 = 1141715) B1141715
theorem B761163 : Blo 758332 761163 := bstep (se 1 (by rfl) ⟨570872, by rfl⟩ : syracuseStep 761163 = 1141745) B1141745
theorem B761175 : Blo 758332 761175 := bstep (se 1 (by rfl) ⟨570881, by rfl⟩ : syracuseStep 761175 = 1141763) B1141763
theorem B1285463 : Blo 758332 1285463 := bstep (se 1 (by rfl) ⟨964097, by rfl⟩ : syracuseStep 1285463 = 1928195) B1928195
theorem B761195 : Blo 758332 761195 := bstep (se 1 (by rfl) ⟨570896, by rfl⟩ : syracuseStep 761195 = 1141793) B1141793
theorem B1711475 : Blo 758332 1711475 := bstep (se 1 (by rfl) ⟨1283606, by rfl⟩ : syracuseStep 1711475 = 2567213) B2567213
theorem B761207 : Blo 758332 761207 := bstep (se 1 (by rfl) ⟨570905, by rfl⟩ : syracuseStep 761207 = 1141811) B1141811
theorem B761227 : Blo 758332 761227 := bstep (se 1 (by rfl) ⟨570920, by rfl⟩ : syracuseStep 761227 = 1141841) B1141841
theorem B2891153 : Blo 758332 2891153 := bstep (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) B2168365
theorem B1711511 : Blo 758332 1711511 := bstep (se 1 (by rfl) ⟨1283633, by rfl⟩ : syracuseStep 1711511 = 2567267) B2567267
theorem B761239 : Blo 758332 761239 := bstep (se 1 (by rfl) ⟨570929, by rfl⟩ : syracuseStep 761239 = 1141859) B1141859
theorem B761259 : Blo 758332 761259 := bstep (se 1 (by rfl) ⟨570944, by rfl⟩ : syracuseStep 761259 = 1141889) B1141889
theorem B761271 : Blo 758332 761271 := bstep (se 1 (by rfl) ⟨570953, by rfl⟩ : syracuseStep 761271 = 1141907) B1141907
theorem B3251659 : Blo 758332 3251659 := bstep (se 1 (by rfl) ⟨2438744, by rfl⟩ : syracuseStep 3251659 = 4877489) B4877489
theorem B761291 : Blo 758332 761291 := bstep (se 1 (by rfl) ⟨570968, by rfl⟩ : syracuseStep 761291 = 1141937) B1141937
theorem B761303 : Blo 758332 761303 := bstep (se 1 (by rfl) ⟨570977, by rfl⟩ : syracuseStep 761303 = 1141955) B1141955
theorem B1285591 : Blo 758332 1285591 := bstep (se 1 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 1285591 = 1928387) B1928387
theorem B761323 : Blo 758332 761323 := bstep (se 1 (by rfl) ⟨570992, by rfl⟩ : syracuseStep 761323 = 1141985) B1141985
theorem B761335 : Blo 758332 761335 := bstep (se 1 (by rfl) ⟨571001, by rfl⟩ : syracuseStep 761335 = 1142003) B1142003
theorem B761355 : Blo 758332 761355 := bstep (se 1 (by rfl) ⟨571016, by rfl⟩ : syracuseStep 761355 = 1142033) B1142033
theorem B761367 : Blo 758332 761367 := bstep (se 1 (by rfl) ⟨571025, by rfl⟩ : syracuseStep 761367 = 1142051) B1142051
theorem B761387 : Blo 758332 761387 := bstep (se 1 (by rfl) ⟨571040, by rfl⟩ : syracuseStep 761387 = 1142081) B1142081
theorem B761399 : Blo 758332 761399 := bstep (se 1 (by rfl) ⟨571049, by rfl⟩ : syracuseStep 761399 = 1142099) B1142099
theorem B2563649 : Blo 758332 2563649 := bstep (se 2 (by rfl) ⟨961368, by rfl⟩ : syracuseStep 2563649 = 1922737) B1922737
theorem B1711691 : Blo 758332 1711691 := bstep (se 1 (by rfl) ⟨1283768, by rfl⟩ : syracuseStep 1711691 = 2567537) B2567537
theorem B761419 : Blo 758332 761419 := bstep (se 1 (by rfl) ⟨571064, by rfl⟩ : syracuseStep 761419 = 1142129) B1142129
theorem B761431 : Blo 758332 761431 := bstep (se 1 (by rfl) ⟨571073, by rfl⟩ : syracuseStep 761431 = 1142147) B1142147
theorem B761451 : Blo 758332 761451 := bstep (se 1 (by rfl) ⟨571088, by rfl⟩ : syracuseStep 761451 = 1142177) B1142177
theorem B761463 : Blo 758332 761463 := bstep (se 1 (by rfl) ⟨571097, by rfl⟩ : syracuseStep 761463 = 1142195) B1142195
theorem B1711745 : Blo 758332 1711745 := bstep (se 2 (by rfl) ⟨641904, by rfl⟩ : syracuseStep 1711745 = 1283809) B1283809
theorem B3841667 : Blo 758332 3841667 := bstep (se 1 (by rfl) ⟨2881250, by rfl⟩ : syracuseStep 3841667 = 5762501) B5762501
theorem B761483 : Blo 758332 761483 := bstep (se 1 (by rfl) ⟨571112, by rfl⟩ : syracuseStep 761483 = 1142225) B1142225
theorem B761495 : Blo 758332 761495 := bstep (se 1 (by rfl) ⟨571121, by rfl⟩ : syracuseStep 761495 = 1142243) B1142243
theorem B761515 : Blo 758332 761515 := bstep (se 1 (by rfl) ⟨571136, by rfl⟩ : syracuseStep 761515 = 1142273) B1142273
theorem B761527 : Blo 758332 761527 := bstep (se 1 (by rfl) ⟨571145, by rfl⟩ : syracuseStep 761527 = 1142291) B1142291
theorem B761547 : Blo 758332 761547 := bstep (se 1 (by rfl) ⟨571160, by rfl⟩ : syracuseStep 761547 = 1142321) B1142321
theorem B761559 : Blo 758332 761559 := bstep (se 1 (by rfl) ⟨571169, by rfl⟩ : syracuseStep 761559 = 1142339) B1142339
theorem B3251933 : Blo 758332 3251933 := bstep (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) B1219475
theorem B761579 : Blo 758332 761579 := bstep (se 1 (by rfl) ⟨571184, by rfl⟩ : syracuseStep 761579 = 1142369) B1142369
theorem B761591 : Blo 758332 761591 := bstep (se 1 (by rfl) ⟨571193, by rfl⟩ : syracuseStep 761591 = 1142387) B1142387
theorem B761611 : Blo 758332 761611 := bstep (se 1 (by rfl) ⟨571208, by rfl⟩ : syracuseStep 761611 = 1142417) B1142417
theorem B761623 : Blo 758332 761623 := bstep (se 1 (by rfl) ⟨571217, by rfl⟩ : syracuseStep 761623 = 1142435) B1142435
theorem B761643 : Blo 758332 761643 := bstep (se 1 (by rfl) ⟨571232, by rfl⟩ : syracuseStep 761643 = 1142465) B1142465
theorem B1482547 : Blo 758332 1482547 := bstep (se 1 (by rfl) ⟨1111910, by rfl⟩ : syracuseStep 1482547 = 2223821) B2223821
theorem B761655 : Blo 758332 761655 := bstep (se 1 (by rfl) ⟨571241, by rfl⟩ : syracuseStep 761655 = 1142483) B1142483
theorem B5480257 : Blo 758332 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B761675 : Blo 758332 761675 := bstep (se 1 (by rfl) ⟨571256, by rfl⟩ : syracuseStep 761675 = 1142513) B1142513
theorem B761687 : Blo 758332 761687 := bstep (se 1 (by rfl) ⟨571265, by rfl⟩ : syracuseStep 761687 = 1142531) B1142531
theorem B1711961 : Blo 758332 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B2891609 : Blo 758332 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B761707 : Blo 758332 761707 := bstep (se 1 (by rfl) ⟨571280, by rfl⟩ : syracuseStep 761707 = 1142561) B1142561
theorem B761719 : Blo 758332 761719 := bstep (se 1 (by rfl) ⟨571289, by rfl⟩ : syracuseStep 761719 = 1142579) B1142579
theorem B761739 : Blo 758332 761739 := bstep (se 1 (by rfl) ⟨571304, by rfl⟩ : syracuseStep 761739 = 1142609) B1142609
theorem B761751 : Blo 758332 761751 := bstep (se 1 (by rfl) ⟨571313, by rfl⟩ : syracuseStep 761751 = 1142627) B1142627
theorem B761771 : Blo 758332 761771 := bstep (se 1 (by rfl) ⟨571328, by rfl⟩ : syracuseStep 761771 = 1142657) B1142657
theorem B1712051 : Blo 758332 1712051 := bstep (se 1 (by rfl) ⟨1284038, by rfl⟩ : syracuseStep 1712051 = 2568077) B2568077
theorem B761783 : Blo 758332 761783 := bstep (se 1 (by rfl) ⟨571337, by rfl⟩ : syracuseStep 761783 = 1142675) B1142675
theorem B925643 : Blo 758332 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B761803 : Blo 758332 761803 := bstep (se 1 (by rfl) ⟨571352, by rfl⟩ : syracuseStep 761803 = 1142705) B1142705
theorem B1712087 : Blo 758332 1712087 := bstep (se 1 (by rfl) ⟨1284065, by rfl⟩ : syracuseStep 1712087 = 2568131) B2568131
theorem B761815 : Blo 758332 761815 := bstep (se 1 (by rfl) ⟨571361, by rfl⟩ : syracuseStep 761815 = 1142723) B1142723
theorem B761835 : Blo 758332 761835 := bstep (se 1 (by rfl) ⟨571376, by rfl⟩ : syracuseStep 761835 = 1142753) B1142753
theorem B761847 : Blo 758332 761847 := bstep (se 1 (by rfl) ⟨571385, by rfl⟩ : syracuseStep 761847 = 1142771) B1142771
theorem B761867 : Blo 758332 761867 := bstep (se 1 (by rfl) ⟨571400, by rfl⟩ : syracuseStep 761867 = 1142801) B1142801
theorem B761879 : Blo 758332 761879 := bstep (se 1 (by rfl) ⟨571409, by rfl⟩ : syracuseStep 761879 = 1142819) B1142819
theorem B761899 : Blo 758332 761899 := bstep (se 1 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 761899 = 1142849) B1142849
theorem B2891821 : Blo 758332 2891821 := bstep (se 3 (by rfl) ⟨542216, by rfl⟩ : syracuseStep 2891821 = 1084433) B1084433
theorem B3252275 : Blo 758332 3252275 := bstep (se 1 (by rfl) ⟨2439206, by rfl⟩ : syracuseStep 3252275 = 4878413) B4878413
theorem B761911 : Blo 758332 761911 := bstep (se 1 (by rfl) ⟨571433, by rfl⟩ : syracuseStep 761911 = 1142867) B1142867
theorem B761931 : Blo 758332 761931 := bstep (se 1 (by rfl) ⟨571448, by rfl⟩ : syracuseStep 761931 = 1142897) B1142897
theorem B1286219 : Blo 758332 1286219 := bstep (se 1 (by rfl) ⟨964664, by rfl⟩ : syracuseStep 1286219 = 1929329) B1929329
theorem B761943 : Blo 758332 761943 := bstep (se 1 (by rfl) ⟨571457, by rfl⟩ : syracuseStep 761943 = 1142915) B1142915
theorem B2564189 : Blo 758332 2564189 := bstep (se 3 (by rfl) ⟨480785, by rfl⟩ : syracuseStep 2564189 = 961571) B961571
theorem B761963 : Blo 758332 761963 := bstep (se 1 (by rfl) ⟨571472, by rfl⟩ : syracuseStep 761963 = 1142945) B1142945
theorem B761975 : Blo 758332 761975 := bstep (se 1 (by rfl) ⟨571481, by rfl⟩ : syracuseStep 761975 = 1142963) B1142963
theorem B1712267 : Blo 758332 1712267 := bstep (se 1 (by rfl) ⟨1284200, by rfl⟩ : syracuseStep 1712267 = 2568401) B2568401
theorem B761995 : Blo 758332 761995 := bstep (se 1 (by rfl) ⟨571496, by rfl⟩ : syracuseStep 761995 = 1142993) B1142993
theorem B762007 : Blo 758332 762007 := bstep (se 1 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 762007 = 1143011) B1143011
theorem B762027 : Blo 758332 762027 := bstep (se 1 (by rfl) ⟨571520, by rfl⟩ : syracuseStep 762027 = 1143041) B1143041
theorem B762039 : Blo 758332 762039 := bstep (se 1 (by rfl) ⟨571529, by rfl⟩ : syracuseStep 762039 = 1143059) B1143059
theorem B1712321 : Blo 758332 1712321 := bstep (se 2 (by rfl) ⟨642120, by rfl⟩ : syracuseStep 1712321 = 1284241) B1284241
theorem B762059 : Blo 758332 762059 := bstep (se 1 (by rfl) ⟨571544, by rfl⟩ : syracuseStep 762059 = 1143089) B1143089
theorem B1286347 : Blo 758332 1286347 := bstep (se 1 (by rfl) ⟨964760, by rfl⟩ : syracuseStep 1286347 = 1929521) B1929521
theorem B762071 : Blo 758332 762071 := bstep (se 1 (by rfl) ⟨571553, by rfl⟩ : syracuseStep 762071 = 1143107) B1143107
theorem B762091 : Blo 758332 762091 := bstep (se 1 (by rfl) ⟨571568, by rfl⟩ : syracuseStep 762091 = 1143137) B1143137
theorem B762103 : Blo 758332 762103 := bstep (se 1 (by rfl) ⟨571577, by rfl⟩ : syracuseStep 762103 = 1143155) B1143155
theorem B762123 : Blo 758332 762123 := bstep (se 1 (by rfl) ⟨571592, by rfl⟩ : syracuseStep 762123 = 1143185) B1143185
theorem B762135 : Blo 758332 762135 := bstep (se 1 (by rfl) ⟨571601, by rfl⟩ : syracuseStep 762135 = 1143203) B1143203
theorem B762155 : Blo 758332 762155 := bstep (se 1 (by rfl) ⟨571616, by rfl⟩ : syracuseStep 762155 = 1143233) B1143233
theorem B762167 : Blo 758332 762167 := bstep (se 1 (by rfl) ⟨571625, by rfl⟩ : syracuseStep 762167 = 1143251) B1143251
theorem B762187 : Blo 758332 762187 := bstep (se 1 (by rfl) ⟨571640, by rfl⟩ : syracuseStep 762187 = 1143281) B1143281
theorem B762199 : Blo 758332 762199 := bstep (se 1 (by rfl) ⟨571649, by rfl⟩ : syracuseStep 762199 = 1143299) B1143299
theorem B2892125 : Blo 758332 2892125 := bstep (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) B1084547
theorem B762219 : Blo 758332 762219 := bstep (se 1 (by rfl) ⟨571664, by rfl⟩ : syracuseStep 762219 = 1143329) B1143329
theorem B762231 : Blo 758332 762231 := bstep (se 1 (by rfl) ⟨571673, by rfl⟩ : syracuseStep 762231 = 1143347) B1143347
theorem B762251 : Blo 758332 762251 := bstep (se 1 (by rfl) ⟨571688, by rfl⟩ : syracuseStep 762251 = 1143377) B1143377
theorem B762263 : Blo 758332 762263 := bstep (se 1 (by rfl) ⟨571697, by rfl⟩ : syracuseStep 762263 = 1143395) B1143395
theorem B1712537 : Blo 758332 1712537 := bstep (se 2 (by rfl) ⟨642201, by rfl⟩ : syracuseStep 1712537 = 1284403) B1284403
theorem B762283 : Blo 758332 762283 := bstep (se 1 (by rfl) ⟨571712, by rfl⟩ : syracuseStep 762283 = 1143425) B1143425
theorem B762295 : Blo 758332 762295 := bstep (se 1 (by rfl) ⟨571721, by rfl⟩ : syracuseStep 762295 = 1143443) B1143443
theorem B762315 : Blo 758332 762315 := bstep (se 1 (by rfl) ⟨571736, by rfl⟩ : syracuseStep 762315 = 1143473) B1143473
theorem B762327 : Blo 758332 762327 := bstep (se 1 (by rfl) ⟨571745, by rfl⟩ : syracuseStep 762327 = 1143491) B1143491
theorem B1712627 : Blo 758332 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B1712663 : Blo 758332 1712663 := bstep (se 1 (by rfl) ⟨1284497, by rfl⟩ : syracuseStep 1712663 = 2568995) B2568995
theorem B1712843 : Blo 758332 1712843 := bstep (se 1 (by rfl) ⟨1284632, by rfl⟩ : syracuseStep 1712843 = 2569265) B2569265
theorem B9872077 : Blo 758332 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B3089117 : Blo 758332 3089117 := bstep (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) B1158419
theorem B1712897 : Blo 758332 1712897 := bstep (se 2 (by rfl) ⟨642336, by rfl⟩ : syracuseStep 1712897 = 1284673) B1284673
theorem B1975105 : Blo 758332 1975105 := bstep (se 2 (by rfl) ⟨740664, by rfl⟩ : syracuseStep 1975105 = 1481329) B1481329
theorem B6169445 : Blo 758332 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B25043813 : Blo 758332 25043813 := bstep (se 4 (by rfl) ⟨2347857, by rfl⟩ : syracuseStep 25043813 = 4695715) B4695715
theorem B1713113 : Blo 758332 1713113 := bstep (se 2 (by rfl) ⟨642417, by rfl⟩ : syracuseStep 1713113 = 1284835) B1284835
theorem B1713203 : Blo 758332 1713203 := bstep (se 1 (by rfl) ⟨1284902, by rfl⟩ : syracuseStep 1713203 = 2569805) B2569805
theorem B1713239 : Blo 758332 1713239 := bstep (se 1 (by rfl) ⟨1284929, by rfl⟩ : syracuseStep 1713239 = 2569859) B2569859
theorem B2565323 : Blo 758332 2565323 := bstep (se 1 (by rfl) ⟨1923992, by rfl⟩ : syracuseStep 2565323 = 3847985) B3847985
theorem B1713419 : Blo 758332 1713419 := bstep (se 1 (by rfl) ⟨1285064, by rfl⟩ : syracuseStep 1713419 = 2570129) B2570129
theorem B1713473 : Blo 758332 1713473 := bstep (se 2 (by rfl) ⟨642552, by rfl⟩ : syracuseStep 1713473 = 1285105) B1285105
theorem B6169931 : Blo 758332 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B2565593 : Blo 758332 2565593 := bstep (se 2 (by rfl) ⟨962097, by rfl⟩ : syracuseStep 2565593 = 1924195) B1924195
theorem B5481989 : Blo 758332 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B1713689 : Blo 758332 1713689 := bstep (se 2 (by rfl) ⟨642633, by rfl⟩ : syracuseStep 1713689 = 1285267) B1285267
theorem B1713779 : Blo 758332 1713779 := bstep (se 1 (by rfl) ⟨1285334, by rfl⟩ : syracuseStep 1713779 = 2570669) B2570669
theorem B1713815 : Blo 758332 1713815 := bstep (se 1 (by rfl) ⟨1285361, by rfl⟩ : syracuseStep 1713815 = 2570723) B2570723
theorem B960331 : Blo 758332 960331 := bstep (se 1 (by rfl) ⟨720248, by rfl⟩ : syracuseStep 960331 = 1440497) B1440497
theorem B1713995 : Blo 758332 1713995 := bstep (se 1 (by rfl) ⟨1285496, by rfl⟩ : syracuseStep 1713995 = 2570993) B2570993
theorem B1714049 : Blo 758332 1714049 := bstep (se 2 (by rfl) ⟨642768, by rfl⟩ : syracuseStep 1714049 = 1285537) B1285537
theorem B960599 : Blo 758332 960599 := bstep (se 1 (by rfl) ⟨720449, by rfl⟩ : syracuseStep 960599 = 1440899) B1440899
theorem B1714265 : Blo 758332 1714265 := bstep (se 2 (by rfl) ⟨642849, by rfl⟩ : syracuseStep 1714265 = 1285699) B1285699
theorem B6924419 : Blo 758332 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B2566295 : Blo 758332 2566295 := bstep (se 1 (by rfl) ⟨1924721, by rfl⟩ : syracuseStep 2566295 = 3849443) B3849443
theorem B1714355 : Blo 758332 1714355 := bstep (se 1 (by rfl) ⟨1285766, by rfl⟩ : syracuseStep 1714355 = 2571533) B2571533
theorem B1714391 : Blo 758332 1714391 := bstep (se 1 (by rfl) ⟨1285793, by rfl⟩ : syracuseStep 1714391 = 2571587) B2571587
theorem B1714571 : Blo 758332 1714571 := bstep (se 1 (by rfl) ⟨1285928, by rfl⟩ : syracuseStep 1714571 = 2571857) B2571857
theorem B3254701 : Blo 758332 3254701 := bstep (se 3 (by rfl) ⟨610256, by rfl⟩ : syracuseStep 3254701 = 1220513) B1220513
theorem B11708849 : Blo 758332 11708849 := bstep (se 2 (by rfl) ⟨4390818, by rfl⟩ : syracuseStep 11708849 = 8781637) B8781637
theorem B1714625 : Blo 758332 1714625 := bstep (se 2 (by rfl) ⟨642984, by rfl⟩ : syracuseStep 1714625 = 1285969) B1285969
theorem B1714841 : Blo 758332 1714841 := bstep (se 2 (by rfl) ⟨643065, by rfl⟩ : syracuseStep 1714841 = 1286131) B1286131
theorem B2566835 : Blo 758332 2566835 := bstep (se 1 (by rfl) ⟨1925126, by rfl⟩ : syracuseStep 2566835 = 3850253) B3850253
theorem B1714931 : Blo 758332 1714931 := bstep (se 1 (by rfl) ⟨1286198, by rfl⟩ : syracuseStep 1714931 = 2572397) B2572397
theorem B961303 : Blo 758332 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B1714967 : Blo 758332 1714967 := bstep (se 1 (by rfl) ⟨1286225, by rfl⟩ : syracuseStep 1714967 = 2572451) B2572451
theorem B2567105 : Blo 758332 2567105 := bstep (se 2 (by rfl) ⟨962664, by rfl⟩ : syracuseStep 2567105 = 1925329) B1925329
theorem B1715147 : Blo 758332 1715147 := bstep (se 1 (by rfl) ⟨1286360, by rfl⟩ : syracuseStep 1715147 = 2572721) B2572721
theorem B8661977 : Blo 758332 8661977 := bstep (se 2 (by rfl) ⟨3248241, by rfl⟩ : syracuseStep 8661977 = 6496483) B6496483
theorem B1715201 : Blo 758332 1715201 := bstep (se 2 (by rfl) ⟨643200, by rfl⟩ : syracuseStep 1715201 = 1286401) B1286401
theorem B1649675 : Blo 758332 1649675 := bstep (se 1 (by rfl) ⟨1237256, by rfl⟩ : syracuseStep 1649675 = 2474513) B2474513
theorem B4336685 : Blo 758332 4336685 := bstep (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) B1626257
theorem B2174045 : Blo 758332 2174045 := bstep (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) B815267
theorem B3845393 : Blo 758332 3845393 := bstep (se 2 (by rfl) ⟨1442022, by rfl⟩ : syracuseStep 3845393 = 2884045) B2884045
theorem B3845555 : Blo 758332 3845555 := bstep (se 1 (by rfl) ⟨2884166, by rfl⟩ : syracuseStep 3845555 = 5768333) B5768333
theorem B2567645 : Blo 758332 2567645 := bstep (se 3 (by rfl) ⟨481433, by rfl⟩ : syracuseStep 2567645 = 962867) B962867
theorem B4108097 : Blo 758332 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B13840307 : Blo 758332 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B963019 : Blo 758332 963019 := bstep (se 1 (by rfl) ⟨722264, by rfl⟩ : syracuseStep 963019 = 1444529) B1444529
theorem B22196753 : Blo 758332 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B2568779 : Blo 758332 2568779 := bstep (se 1 (by rfl) ⟨1926584, by rfl⟩ : syracuseStep 2568779 = 3853169) B3853169
theorem B1028695 : Blo 758332 1028695 := bstep (se 1 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 1028695 = 1543043) B1543043
theorem B4698755 : Blo 758332 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B1946305 : Blo 758332 1946305 := bstep (se 2 (by rfl) ⟨729864, by rfl⟩ : syracuseStep 1946305 = 1459729) B1459729
theorem B2569049 : Blo 758332 2569049 := bstep (se 2 (by rfl) ⟨963393, by rfl⟩ : syracuseStep 2569049 = 1926787) B1926787
theorem B3650777 : Blo 758332 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B3847499 : Blo 758332 3847499 := bstep (se 1 (by rfl) ⟨2885624, by rfl⟩ : syracuseStep 3847499 = 5771249) B5771249
theorem B6174083 : Blo 758332 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B963991 : Blo 758332 963991 := bstep (se 1 (by rfl) ⟨722993, by rfl⟩ : syracuseStep 963991 = 1445987) B1445987
theorem B1390103 : Blo 758332 1390103 := bstep (se 1 (by rfl) ⟨1042577, by rfl⟩ : syracuseStep 1390103 = 2085155) B2085155
theorem B2569751 : Blo 758332 2569751 := bstep (se 1 (by rfl) ⟨1927313, by rfl⟩ : syracuseStep 2569751 = 3854627) B3854627
theorem B1619671 : Blo 758332 1619671 := bstep (se 1 (by rfl) ⟨1214753, by rfl⟩ : syracuseStep 1619671 = 2429507) B2429507
theorem B1619713 : Blo 758332 1619713 := bstep (se 2 (by rfl) ⟨607392, by rfl⟩ : syracuseStep 1619713 = 1214785) B1214785
theorem B2439001 : Blo 758332 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B833419 : Blo 758332 833419 := bstep (se 1 (by rfl) ⟨625064, by rfl⟩ : syracuseStep 833419 = 1250129) B1250129
theorem B2570291 : Blo 758332 2570291 := bstep (se 1 (by rfl) ⟨1927718, by rfl⟩ : syracuseStep 2570291 = 3855437) B3855437
theorem B3291211 : Blo 758332 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B2308189 : Blo 758332 2308189 := bstep (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) B865571
theorem B964811 : Blo 758332 964811 := bstep (se 1 (by rfl) ⟨723608, by rfl⟩ : syracuseStep 964811 = 1447217) B1447217
theorem B2570561 : Blo 758332 2570561 := bstep (se 2 (by rfl) ⟨963960, by rfl⟩ : syracuseStep 2570561 = 1927921) B1927921
theorem B2406935 : Blo 758332 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B4340375 : Blo 758332 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B4438745 : Blo 758332 4438745 := bstep (se 2 (by rfl) ⟨1664529, by rfl⟩ : syracuseStep 4438745 = 3329059) B3329059
theorem B3652427 : Blo 758332 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B2571101 : Blo 758332 2571101 := bstep (se 3 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 2571101 = 964163) B964163
theorem B5192549 : Blo 758332 5192549 := bstep (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) B973603
theorem B867223 : Blo 758332 867223 := bstep (se 1 (by rfl) ⟨650417, by rfl⟩ : syracuseStep 867223 = 1300835) B1300835
theorem B2735041 : Blo 758332 2735041 := bstep (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) B2051281
theorem B3849281 : Blo 758332 3849281 := bstep (se 2 (by rfl) ⟨1443480, by rfl⟩ : syracuseStep 3849281 = 2886961) B2886961
theorem B2440385 : Blo 758332 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B1621387 : Blo 758332 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B2604595 : Blo 758332 2604595 := bstep (se 1 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 2604595 = 3906893) B3906893
theorem B1621721 : Blo 758332 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B2440925 : Blo 758332 2440925 := bstep (se 3 (by rfl) ⟨457673, by rfl⟩ : syracuseStep 2440925 = 915347) B915347
theorem B2572235 : Blo 758332 2572235 := bstep (se 1 (by rfl) ⟨1929176, by rfl⟩ : syracuseStep 2572235 = 3858353) B3858353
theorem B2572505 : Blo 758332 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B770743 : Blo 758332 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B6177485 : Blo 758332 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B79086293 : Blo 758332 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B3851225 : Blo 758332 3851225 := bstep (se 2 (by rfl) ⟨1444209, by rfl⟩ : syracuseStep 3851225 = 2888419) B2888419
theorem B1623233 : Blo 758332 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B3655043 : Blo 758332 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B1754561 : Blo 758332 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B6178265 : Blo 758332 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B6506189 : Blo 758332 6506189 := bstep (se 3 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 6506189 = 2439821) B2439821
theorem B12306181 : Blo 758332 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B2737937 : Blo 758332 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B1624087 : Blo 758332 1624087 := bstep (se 1 (by rfl) ⟨1218065, by rfl⟩ : syracuseStep 1624087 = 2436131) B2436131
theorem B7817477 : Blo 758332 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B2771351 : Blo 758332 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B3852845 : Blo 758332 3852845 := bstep (se 3 (by rfl) ⟨722408, by rfl⟩ : syracuseStep 3852845 = 1444817) B1444817
theorem B1919639 : Blo 758332 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B1624907 : Blo 758332 1624907 := bstep (se 1 (by rfl) ⟨1218680, by rfl⟩ : syracuseStep 1624907 = 2437361) B2437361
theorem B5786801 : Blo 758332 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B1920307 : Blo 758332 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B1920449 : Blo 758332 1920449 := bstep (se 2 (by rfl) ⟨720168, by rfl⟩ : syracuseStep 1920449 = 1440337) B1440337
theorem B2051659 : Blo 758332 2051659 := bstep (se 1 (by rfl) ⟨1538744, by rfl⟩ : syracuseStep 2051659 = 3077489) B3077489
theorem B23449219 : Blo 758332 23449219 := bstep (se 1 (by rfl) ⟨17586914, by rfl⟩ : syracuseStep 23449219 = 35173829) B35173829
theorem B5787287 : Blo 758332 5787287 := bstep (se 1 (by rfl) ⟨4340465, by rfl⟩ : syracuseStep 5787287 = 8680931) B8680931
theorem B1560217 : Blo 758332 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B1953857 : Blo 758332 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B7786853 : Blo 758332 7786853 := bstep (se 4 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 7786853 = 1460035) B1460035
theorem B2052503 : Blo 758332 2052503 := bstep (se 1 (by rfl) ⟨1539377, by rfl⟩ : syracuseStep 2052503 = 3078755) B3078755
theorem B2052545 : Blo 758332 2052545 := bstep (se 2 (by rfl) ⟨769704, by rfl⟩ : syracuseStep 2052545 = 1539409) B1539409
theorem B1823255 : Blo 758332 1823255 := bstep (se 1 (by rfl) ⟨1367441, by rfl⟩ : syracuseStep 1823255 = 2734883) B2734883
theorem B2052697 : Blo 758332 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B5493379 : Blo 758332 5493379 := bstep (se 1 (by rfl) ⟨4120034, by rfl⟩ : syracuseStep 5493379 = 8240069) B8240069
theorem B1921715 : Blo 758332 1921715 := bstep (se 1 (by rfl) ⟨1441286, by rfl⟩ : syracuseStep 1921715 = 2882573) B2882573
theorem B2053043 : Blo 758332 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B4379741 : Blo 758332 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B1627265 : Blo 758332 1627265 := bstep (se 2 (by rfl) ⟨610224, by rfl⟩ : syracuseStep 1627265 = 1220449) B1220449
theorem B1922251 : Blo 758332 1922251 := bstep (se 1 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 1922251 = 2883377) B2883377
theorem B4871441 : Blo 758332 4871441 := bstep (se 2 (by rfl) ⟨1826790, by rfl⟩ : syracuseStep 4871441 = 3653581) B3653581
theorem B1922393 : Blo 758332 1922393 := bstep (se 2 (by rfl) ⟨720897, by rfl⟩ : syracuseStep 1922393 = 1441795) B1441795
theorem B5854643 : Blo 758332 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B1627607 : Blo 758332 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B166581845 : Blo 758332 166581845 := bstep (se 8 (by rfl) ⟨976065, by rfl⟩ : syracuseStep 166581845 = 1952131) B1952131
theorem B33249203 : Blo 758332 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B2054081 : Blo 758332 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B1923223 : Blo 758332 1923223 := bstep (se 1 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 1923223 = 2884835) B2884835
theorem B2742493 : Blo 758332 2742493 := bstep (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) B1028435
theorem B3856733 : Blo 758332 3856733 := bstep (se 3 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 3856733 = 1446275) B1446275
theorem B6510941 : Blo 758332 6510941 := bstep (se 3 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 6510941 = 2441603) B2441603
theorem B1923659 : Blo 758332 1923659 := bstep (se 1 (by rfl) ⟨1442744, by rfl⟩ : syracuseStep 1923659 = 2885489) B2885489
theorem B4741811 : Blo 758332 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B3300043 : Blo 758332 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B1366807 : Blo 758332 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B1825715 : Blo 758332 1825715 := bstep (se 1 (by rfl) ⟨1369286, by rfl⟩ : syracuseStep 1825715 = 2738573) B2738573
theorem B1924033 : Blo 758332 1924033 := bstep (se 2 (by rfl) ⟨721512, by rfl⟩ : syracuseStep 1924033 = 1443025) B1443025
theorem B1137611 : Blo 758332 1137611 := bstep (se 1 (by rfl) ⟨853208, by rfl⟩ : syracuseStep 1137611 = 1706417) B1706417
theorem B1137623 : Blo 758332 1137623 := bstep (se 1 (by rfl) ⟨853217, by rfl⟩ : syracuseStep 1137623 = 1706435) B1706435
theorem B12311513 : Blo 758332 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B1825753 : Blo 758332 1825753 := bstep (se 2 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 1825753 = 1369315) B1369315
theorem B1137689 : Blo 758332 1137689 := bstep (se 2 (by rfl) ⟨426633, by rfl⟩ : syracuseStep 1137689 = 853267) B853267
theorem B1137803 : Blo 758332 1137803 := bstep (se 1 (by rfl) ⟨853352, by rfl⟩ : syracuseStep 1137803 = 1706705) B1706705
theorem B1137815 : Blo 758332 1137815 := bstep (se 1 (by rfl) ⟨853361, by rfl⟩ : syracuseStep 1137815 = 1706723) B1706723
theorem B1137881 : Blo 758332 1137881 := bstep (se 2 (by rfl) ⟨426705, by rfl⟩ : syracuseStep 1137881 = 853411) B853411
theorem B1367297 : Blo 758332 1367297 := bstep (se 2 (by rfl) ⟨512736, by rfl⟩ : syracuseStep 1367297 = 1025473) B1025473
theorem B1137995 : Blo 758332 1137995 := bstep (se 1 (by rfl) ⟨853496, by rfl⟩ : syracuseStep 1137995 = 1706993) B1706993
theorem B1138007 : Blo 758332 1138007 := bstep (se 1 (by rfl) ⟨853505, by rfl⟩ : syracuseStep 1138007 = 1707011) B1707011
theorem B119922061 : Blo 758332 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B1138073 : Blo 758332 1138073 := bstep (se 2 (by rfl) ⟨426777, by rfl⟩ : syracuseStep 1138073 = 853555) B853555
theorem B1138187 : Blo 758332 1138187 := bstep (se 1 (by rfl) ⟨853640, by rfl⟩ : syracuseStep 1138187 = 1707281) B1707281
theorem B1138199 : Blo 758332 1138199 := bstep (se 1 (by rfl) ⟨853649, by rfl⟩ : syracuseStep 1138199 = 1707299) B1707299
theorem B1924631 : Blo 758332 1924631 := bstep (se 1 (by rfl) ⟨1443473, by rfl⟩ : syracuseStep 1924631 = 2886947) B2886947
theorem B1138265 : Blo 758332 1138265 := bstep (se 2 (by rfl) ⟨426849, by rfl⟩ : syracuseStep 1138265 = 853699) B853699
theorem B8347229 : Blo 758332 8347229 := bstep (se 3 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 8347229 = 3130211) B3130211
theorem B1138379 : Blo 758332 1138379 := bstep (se 1 (by rfl) ⟨853784, by rfl⟩ : syracuseStep 1138379 = 1707569) B1707569
theorem B1138391 : Blo 758332 1138391 := bstep (se 1 (by rfl) ⟨853793, by rfl⟩ : syracuseStep 1138391 = 1707587) B1707587
theorem B1138457 : Blo 758332 1138457 := bstep (se 2 (by rfl) ⟨426921, by rfl⟩ : syracuseStep 1138457 = 853843) B853843
theorem B1138571 : Blo 758332 1138571 := bstep (se 1 (by rfl) ⟨853928, by rfl⟩ : syracuseStep 1138571 = 1707857) B1707857
theorem B1138583 : Blo 758332 1138583 := bstep (se 1 (by rfl) ⟨853937, by rfl⟩ : syracuseStep 1138583 = 1707875) B1707875
theorem B1138649 : Blo 758332 1138649 := bstep (se 2 (by rfl) ⟨426993, by rfl⟩ : syracuseStep 1138649 = 853987) B853987
theorem B2056157 : Blo 758332 2056157 := bstep (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) B771059
theorem B1138763 : Blo 758332 1138763 := bstep (se 1 (by rfl) ⟨854072, by rfl⟩ : syracuseStep 1138763 = 1708145) B1708145
theorem B1138775 : Blo 758332 1138775 := bstep (se 1 (by rfl) ⟨854081, by rfl⟩ : syracuseStep 1138775 = 1708163) B1708163
theorem B1138841 : Blo 758332 1138841 := bstep (se 2 (by rfl) ⟨427065, by rfl⟩ : syracuseStep 1138841 = 854131) B854131
theorem B1302731 : Blo 758332 1302731 := bstep (se 1 (by rfl) ⟨977048, by rfl⟩ : syracuseStep 1302731 = 1954097) B1954097
theorem B1138955 : Blo 758332 1138955 := bstep (se 1 (by rfl) ⟨854216, by rfl⟩ : syracuseStep 1138955 = 1708433) B1708433
theorem B1138967 : Blo 758332 1138967 := bstep (se 1 (by rfl) ⟨854225, by rfl⟩ : syracuseStep 1138967 = 1708451) B1708451
theorem B1925441 : Blo 758332 1925441 := bstep (se 2 (by rfl) ⟨722040, by rfl⟩ : syracuseStep 1925441 = 1444081) B1444081
theorem B1139033 : Blo 758332 1139033 := bstep (se 2 (by rfl) ⟨427137, by rfl⟩ : syracuseStep 1139033 = 854275) B854275
theorem B12312931 : Blo 758332 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B3858839 : Blo 758332 3858839 := bstep (se 1 (by rfl) ⟨2894129, by rfl⟩ : syracuseStep 3858839 = 5788259) B5788259
theorem B1139147 : Blo 758332 1139147 := bstep (se 1 (by rfl) ⟨854360, by rfl⟩ : syracuseStep 1139147 = 1708721) B1708721
theorem B1139159 : Blo 758332 1139159 := bstep (se 1 (by rfl) ⟨854369, by rfl⟩ : syracuseStep 1139159 = 1708739) B1708739
theorem B1139225 : Blo 758332 1139225 := bstep (se 2 (by rfl) ⟨427209, by rfl⟩ : syracuseStep 1139225 = 854419) B854419
theorem B3465773 : Blo 758332 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B1139339 : Blo 758332 1139339 := bstep (se 1 (by rfl) ⟨854504, by rfl⟩ : syracuseStep 1139339 = 1709009) B1709009
theorem B1139351 : Blo 758332 1139351 := bstep (se 1 (by rfl) ⟨854513, by rfl⟩ : syracuseStep 1139351 = 1709027) B1709027
theorem B1172183 : Blo 758332 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B3891929 : Blo 758332 3891929 := bstep (se 2 (by rfl) ⟨1459473, by rfl⟩ : syracuseStep 3891929 = 2918947) B2918947
theorem B1139417 : Blo 758332 1139417 := bstep (se 2 (by rfl) ⟨427281, by rfl⟩ : syracuseStep 1139417 = 854563) B854563
theorem B811787 : Blo 758332 811787 := bstep (se 1 (by rfl) ⟨608840, by rfl⟩ : syracuseStep 811787 = 1217681) B1217681
theorem B1139531 : Blo 758332 1139531 := bstep (se 1 (by rfl) ⟨854648, by rfl⟩ : syracuseStep 1139531 = 1709297) B1709297
theorem B1139543 : Blo 758332 1139543 := bstep (se 1 (by rfl) ⟨854657, by rfl⟩ : syracuseStep 1139543 = 1709315) B1709315
theorem B1925977 : Blo 758332 1925977 := bstep (se 2 (by rfl) ⟨722241, by rfl⟩ : syracuseStep 1925977 = 1444483) B1444483
theorem B1139609 : Blo 758332 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B1139723 : Blo 758332 1139723 := bstep (se 1 (by rfl) ⟨854792, by rfl⟩ : syracuseStep 1139723 = 1709585) B1709585
theorem B1139735 : Blo 758332 1139735 := bstep (se 1 (by rfl) ⟨854801, by rfl⟩ : syracuseStep 1139735 = 1709603) B1709603
theorem B1827905 : Blo 758332 1827905 := bstep (se 2 (by rfl) ⟨685464, by rfl⟩ : syracuseStep 1827905 = 1370929) B1370929
theorem B6480971 : Blo 758332 6480971 := bstep (se 1 (by rfl) ⟨4860728, by rfl⟩ : syracuseStep 6480971 = 9721457) B9721457
theorem B1139801 : Blo 758332 1139801 := bstep (se 2 (by rfl) ⟨427425, by rfl⟩ : syracuseStep 1139801 = 854851) B854851
theorem B9757847 : Blo 758332 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B1139915 : Blo 758332 1139915 := bstep (se 1 (by rfl) ⟨854936, by rfl⟩ : syracuseStep 1139915 = 1709873) B1709873
theorem B8676557 : Blo 758332 8676557 := bstep (se 3 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 8676557 = 3253709) B3253709
theorem B1139927 : Blo 758332 1139927 := bstep (se 1 (by rfl) ⟨854945, by rfl⟩ : syracuseStep 1139927 = 1709891) B1709891
theorem B1139993 : Blo 758332 1139993 := bstep (se 2 (by rfl) ⟨427497, by rfl⟩ : syracuseStep 1139993 = 854995) B854995
theorem B1140107 : Blo 758332 1140107 := bstep (se 1 (by rfl) ⟨855080, by rfl⟩ : syracuseStep 1140107 = 1710161) B1710161
theorem B1140119 : Blo 758332 1140119 := bstep (se 1 (by rfl) ⟨855089, by rfl⟩ : syracuseStep 1140119 = 1710179) B1710179
theorem B1140185 : Blo 758332 1140185 := bstep (se 2 (by rfl) ⟨427569, by rfl⟩ : syracuseStep 1140185 = 855139) B855139
theorem B1041931 : Blo 758332 1041931 := bstep (se 1 (by rfl) ⟨781448, by rfl⟩ : syracuseStep 1041931 = 1562897) B1562897
theorem B5760557 : Blo 758332 5760557 := bstep (se 3 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 5760557 = 2160209) B2160209
theorem B1140299 : Blo 758332 1140299 := bstep (se 1 (by rfl) ⟨855224, by rfl⟩ : syracuseStep 1140299 = 1710449) B1710449
theorem B1140311 : Blo 758332 1140311 := bstep (se 1 (by rfl) ⟨855233, by rfl⟩ : syracuseStep 1140311 = 1710467) B1710467
theorem B1140377 : Blo 758332 1140377 := bstep (se 2 (by rfl) ⟨427641, by rfl⟩ : syracuseStep 1140377 = 855283) B855283
theorem B1140491 : Blo 758332 1140491 := bstep (se 1 (by rfl) ⟨855368, by rfl⟩ : syracuseStep 1140491 = 1710737) B1710737
theorem B1140503 : Blo 758332 1140503 := bstep (se 1 (by rfl) ⟨855377, by rfl⟩ : syracuseStep 1140503 = 1710755) B1710755
theorem B1369943 : Blo 758332 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B1140569 : Blo 758332 1140569 := bstep (se 2 (by rfl) ⟨427713, by rfl⟩ : syracuseStep 1140569 = 855427) B855427
theorem B1927091 : Blo 758332 1927091 := bstep (se 1 (by rfl) ⟨1445318, by rfl⟩ : syracuseStep 1927091 = 2890637) B2890637
theorem B1140683 : Blo 758332 1140683 := bstep (se 1 (by rfl) ⟨855512, by rfl⟩ : syracuseStep 1140683 = 1711025) B1711025
theorem B1140695 : Blo 758332 1140695 := bstep (se 1 (by rfl) ⟨855521, by rfl⟩ : syracuseStep 1140695 = 1711043) B1711043
theorem B1140761 : Blo 758332 1140761 := bstep (se 2 (by rfl) ⟨427785, by rfl⟩ : syracuseStep 1140761 = 855571) B855571
theorem B1140875 : Blo 758332 1140875 := bstep (se 1 (by rfl) ⟨855656, by rfl⟩ : syracuseStep 1140875 = 1711313) B1711313
theorem B1140887 : Blo 758332 1140887 := bstep (se 1 (by rfl) ⟨855665, by rfl⟩ : syracuseStep 1140887 = 1711331) B1711331
theorem B1140953 : Blo 758332 1140953 := bstep (se 2 (by rfl) ⟨427857, by rfl⟩ : syracuseStep 1140953 = 855715) B855715
theorem B1927385 : Blo 758332 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1141067 : Blo 758332 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B1141079 : Blo 758332 1141079 := bstep (se 1 (by rfl) ⟨855809, by rfl⟩ : syracuseStep 1141079 = 1711619) B1711619
theorem B4876645 : Blo 758332 4876645 := bstep (se 4 (by rfl) ⟨457185, by rfl⟩ : syracuseStep 4876645 = 914371) B914371
theorem B1141145 : Blo 758332 1141145 := bstep (se 2 (by rfl) ⟨427929, by rfl⟩ : syracuseStep 1141145 = 855859) B855859
theorem B813547 : Blo 758332 813547 := bstep (se 1 (by rfl) ⟨610160, by rfl⟩ : syracuseStep 813547 = 1220321) B1220321
theorem B1141259 : Blo 758332 1141259 := bstep (se 1 (by rfl) ⟨855944, by rfl⟩ : syracuseStep 1141259 = 1711889) B1711889
theorem B1141271 : Blo 758332 1141271 := bstep (se 1 (by rfl) ⟨855953, by rfl⟩ : syracuseStep 1141271 = 1711907) B1711907
theorem B2058817 : Blo 758332 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B1370699 : Blo 758332 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B1141337 : Blo 758332 1141337 := bstep (se 2 (by rfl) ⟨428001, by rfl⟩ : syracuseStep 1141337 = 856003) B856003
theorem B1141451 : Blo 758332 1141451 := bstep (se 1 (by rfl) ⟨856088, by rfl⟩ : syracuseStep 1141451 = 1712177) B1712177
theorem B1141463 : Blo 758332 1141463 := bstep (se 1 (by rfl) ⟨856097, by rfl⟩ : syracuseStep 1141463 = 1712195) B1712195
theorem B1141529 : Blo 758332 1141529 := bstep (se 2 (by rfl) ⟨428073, by rfl⟩ : syracuseStep 1141529 = 856147) B856147
theorem B1731379 : Blo 758332 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B4877131 : Blo 758332 4877131 := bstep (se 1 (by rfl) ⟨3657848, by rfl⟩ : syracuseStep 4877131 = 7315697) B7315697
theorem B2747267 : Blo 758332 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B1141643 : Blo 758332 1141643 := bstep (se 1 (by rfl) ⟨856232, by rfl⟩ : syracuseStep 1141643 = 1712465) B1712465
theorem B1141655 : Blo 758332 1141655 := bstep (se 1 (by rfl) ⟨856241, by rfl⟩ : syracuseStep 1141655 = 1712483) B1712483
theorem B3074989 : Blo 758332 3074989 := bstep (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) B1153121
theorem B1141721 : Blo 758332 1141721 := bstep (se 2 (by rfl) ⟨428145, by rfl⟩ : syracuseStep 1141721 = 856291) B856291
theorem B1371161 : Blo 758332 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B1141835 : Blo 758332 1141835 := bstep (se 1 (by rfl) ⟨856376, by rfl⟩ : syracuseStep 1141835 = 1712753) B1712753
theorem B1141847 : Blo 758332 1141847 := bstep (se 1 (by rfl) ⟨856385, by rfl⟩ : syracuseStep 1141847 = 1712771) B1712771
theorem B1141913 : Blo 758332 1141913 := bstep (se 2 (by rfl) ⟨428217, by rfl⟩ : syracuseStep 1141913 = 856435) B856435
theorem B2190539 : Blo 758332 2190539 := bstep (se 1 (by rfl) ⟨1642904, by rfl⟩ : syracuseStep 2190539 = 3285809) B3285809
theorem B1142027 : Blo 758332 1142027 := bstep (se 1 (by rfl) ⟨856520, by rfl⟩ : syracuseStep 1142027 = 1713041) B1713041
theorem B1142039 : Blo 758332 1142039 := bstep (se 1 (by rfl) ⟨856529, by rfl⟩ : syracuseStep 1142039 = 1713059) B1713059
theorem B1142105 : Blo 758332 1142105 := bstep (se 2 (by rfl) ⟨428289, by rfl⟩ : syracuseStep 1142105 = 856579) B856579
theorem B1142219 : Blo 758332 1142219 := bstep (se 1 (by rfl) ⟨856664, by rfl⟩ : syracuseStep 1142219 = 1713329) B1713329
theorem B1142231 : Blo 758332 1142231 := bstep (se 1 (by rfl) ⟨856673, by rfl⟩ : syracuseStep 1142231 = 1713347) B1713347
theorem B1142297 : Blo 758332 1142297 := bstep (se 2 (by rfl) ⟨428361, by rfl⟩ : syracuseStep 1142297 = 856723) B856723
theorem B1371737 : Blo 758332 1371737 := bstep (se 2 (by rfl) ⟨514401, by rfl⟩ : syracuseStep 1371737 = 1028803) B1028803
theorem B1142411 : Blo 758332 1142411 := bstep (se 1 (by rfl) ⟨856808, by rfl⟩ : syracuseStep 1142411 = 1713617) B1713617
theorem B1142423 : Blo 758332 1142423 := bstep (se 1 (by rfl) ⟨856817, by rfl⟩ : syracuseStep 1142423 = 1713635) B1713635
theorem B6483635 : Blo 758332 6483635 := bstep (se 1 (by rfl) ⟨4862726, by rfl⟩ : syracuseStep 6483635 = 9725453) B9725453
theorem B1666777 : Blo 758332 1666777 := bstep (se 2 (by rfl) ⟨625041, by rfl⟩ : syracuseStep 1666777 = 1250083) B1250083
theorem B1142489 : Blo 758332 1142489 := bstep (se 2 (by rfl) ⟨428433, by rfl⟩ : syracuseStep 1142489 = 856867) B856867
theorem B1142603 : Blo 758332 1142603 := bstep (se 1 (by rfl) ⟨856952, by rfl⟩ : syracuseStep 1142603 = 1713905) B1713905
theorem B1929035 : Blo 758332 1929035 := bstep (se 1 (by rfl) ⟨1446776, by rfl⟩ : syracuseStep 1929035 = 2893553) B2893553
theorem B1142615 : Blo 758332 1142615 := bstep (se 1 (by rfl) ⟨856961, by rfl⟩ : syracuseStep 1142615 = 1713923) B1713923
theorem B1142681 : Blo 758332 1142681 := bstep (se 2 (by rfl) ⟨428505, by rfl⟩ : syracuseStep 1142681 = 857011) B857011
theorem B3239939 : Blo 758332 3239939 := bstep (se 1 (by rfl) ⟨2429954, by rfl⟩ : syracuseStep 3239939 = 4859909) B4859909
theorem B1142795 : Blo 758332 1142795 := bstep (se 1 (by rfl) ⟨857096, by rfl⟩ : syracuseStep 1142795 = 1714193) B1714193
theorem B1142807 : Blo 758332 1142807 := bstep (se 1 (by rfl) ⟨857105, by rfl⟩ : syracuseStep 1142807 = 1714211) B1714211
theorem B1372249 : Blo 758332 1372249 := bstep (se 2 (by rfl) ⟨514593, by rfl⟩ : syracuseStep 1372249 = 1029187) B1029187
theorem B1142873 : Blo 758332 1142873 := bstep (se 2 (by rfl) ⟨428577, by rfl⟩ : syracuseStep 1142873 = 857155) B857155
theorem B4944023 : Blo 758332 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B1372313 : Blo 758332 1372313 := bstep (se 2 (by rfl) ⟨514617, by rfl⟩ : syracuseStep 1372313 = 1029235) B1029235
theorem B1142987 : Blo 758332 1142987 := bstep (se 1 (by rfl) ⟨857240, by rfl⟩ : syracuseStep 1142987 = 1714481) B1714481
theorem B1732823 : Blo 758332 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B1142999 : Blo 758332 1142999 := bstep (se 1 (by rfl) ⟨857249, by rfl⟩ : syracuseStep 1142999 = 1714499) B1714499
theorem B1143065 : Blo 758332 1143065 := bstep (se 2 (by rfl) ⟨428649, by rfl⟩ : syracuseStep 1143065 = 857299) B857299
theorem B1143179 : Blo 758332 1143179 := bstep (se 1 (by rfl) ⟨857384, by rfl⟩ : syracuseStep 1143179 = 1714769) B1714769
theorem B1143191 : Blo 758332 1143191 := bstep (se 1 (by rfl) ⟨857393, by rfl⟩ : syracuseStep 1143191 = 1714787) B1714787
theorem B1143257 : Blo 758332 1143257 := bstep (se 2 (by rfl) ⟨428721, by rfl⟩ : syracuseStep 1143257 = 857443) B857443
theorem B1831385 : Blo 758332 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B1143371 : Blo 758332 1143371 := bstep (se 1 (by rfl) ⟨857528, by rfl⟩ : syracuseStep 1143371 = 1715057) B1715057
theorem B1143383 : Blo 758332 1143383 := bstep (se 1 (by rfl) ⟨857537, by rfl⟩ : syracuseStep 1143383 = 1715075) B1715075
theorem B6255197 : Blo 758332 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B1143449 : Blo 758332 1143449 := bstep (se 2 (by rfl) ⟨428793, by rfl⟩ : syracuseStep 1143449 = 857587) B857587
theorem B6484697 : Blo 758332 6484697 := bstep (se 2 (by rfl) ⟨2431761, by rfl⟩ : syracuseStep 6484697 = 4863523) B4863523
theorem B2880643 : Blo 758332 2880643 := bstep (se 1 (by rfl) ⟨2160482, by rfl⟩ : syracuseStep 2880643 = 4320965) B4320965
theorem B4322605 : Blo 758332 4322605 := bstep (se 3 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 4322605 = 1620977) B1620977
theorem B5764445 : Blo 758332 5764445 := bstep (se 3 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 5764445 = 2161667) B2161667
theorem B2880947 : Blo 758332 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B5469619 : Blo 758332 5469619 := bstep (se 1 (by rfl) ⟨4102214, by rfl⟩ : syracuseStep 5469619 = 8204429) B8204429
theorem B1537625 : Blo 758332 1537625 := bstep (se 2 (by rfl) ⟨576609, by rfl⟩ : syracuseStep 1537625 = 1153219) B1153219
theorem B3077783 : Blo 758332 3077783 := bstep (se 1 (by rfl) ⟨2308337, by rfl⟩ : syracuseStep 3077783 = 4616675) B4616675
theorem B2881601 : Blo 758332 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B8648855 : Blo 758332 8648855 := bstep (se 1 (by rfl) ⟨6486641, by rfl⟩ : syracuseStep 8648855 = 12973283) B12973283
theorem B1440011 : Blo 758332 1440011 := bstep (se 1 (by rfl) ⟨1080008, by rfl⟩ : syracuseStep 1440011 = 2160017) B2160017
theorem B2161075 : Blo 758332 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B1440193 : Blo 758332 1440193 := bstep (se 2 (by rfl) ⟨540072, by rfl⟩ : syracuseStep 1440193 = 1080145) B1080145
theorem B9272069 : Blo 758332 9272069 := bstep (se 4 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 9272069 = 1738513) B1738513
theorem B1440641 : Blo 758332 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B1440983 : Blo 758332 1440983 := bstep (se 1 (by rfl) ⟨1080737, by rfl⟩ : syracuseStep 1440983 = 2161475) B2161475
theorem B2882861 : Blo 758332 2882861 := bstep (se 3 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 2882861 = 1081073) B1081073
theorem B18513197 : Blo 758332 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B2882891 : Blo 758332 2882891 := bstep (se 1 (by rfl) ⟨2162168, by rfl⟩ : syracuseStep 2882891 = 4324337) B4324337
theorem B2162123 : Blo 758332 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B1736471 : Blo 758332 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B1441651 : Blo 758332 1441651 := bstep (se 1 (by rfl) ⟨1081238, by rfl⟩ : syracuseStep 1441651 = 2162477) B2162477
theorem B2883545 : Blo 758332 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B2162807 : Blo 758332 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B23462291 : Blo 758332 23462291 := bstep (se 1 (by rfl) ⟨17596718, by rfl⟩ : syracuseStep 23462291 = 35193437) B35193437
theorem B16417241 : Blo 758332 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B52724195 : Blo 758332 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B1082155 : Blo 758332 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B2229383 : Blo 758332 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B5473453 : Blo 758332 5473453 := bstep (se 3 (by rfl) ⟨1026272, by rfl⟩ : syracuseStep 5473453 = 2052545) B2052545
theorem B2885017 : Blo 758332 2885017 := bstep (se 2 (by rfl) ⟨1081881, by rfl⟩ : syracuseStep 2885017 = 2163763) B2163763
theorem B853519 : Blo 758332 853519 := bstep (se 1 (by rfl) ⟨640139, by rfl⟩ : syracuseStep 853519 = 1280279) B1280279
theorem B3245629 : Blo 758332 3245629 := bstep (se 3 (by rfl) ⟨608555, by rfl⟩ : syracuseStep 3245629 = 1217111) B1217111
theorem B4326979 : Blo 758332 4326979 := bstep (se 1 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 4326979 = 6490469) B6490469
theorem B6489719 : Blo 758332 6489719 := bstep (se 1 (by rfl) ⟨4867289, by rfl⟩ : syracuseStep 6489719 = 9734579) B9734579
theorem B2885321 : Blo 758332 2885321 := bstep (se 2 (by rfl) ⟨1081995, by rfl⟩ : syracuseStep 2885321 = 2163991) B2163991
theorem B1279759 : Blo 758332 1279759 := bstep (se 1 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 1279759 = 1919639) B1919639
theorem B854023 : Blo 758332 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B1443899 : Blo 758332 1443899 := bstep (se 1 (by rfl) ⟨1082924, by rfl⟩ : syracuseStep 1443899 = 2165849) B2165849
theorem B854203 : Blo 758332 854203 := bstep (se 1 (by rfl) ⟨640652, by rfl⟩ : syracuseStep 854203 = 1281305) B1281305
theorem B1706255 : Blo 758332 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B1706273 : Blo 758332 1706273 := bstep (se 2 (by rfl) ⟨639852, by rfl⟩ : syracuseStep 1706273 = 1279705) B1279705
theorem B1280299 : Blo 758332 1280299 := bstep (se 1 (by rfl) ⟨960224, by rfl⟩ : syracuseStep 1280299 = 1920449) B1920449
theorem B1280441 : Blo 758332 1280441 := bstep (se 2 (by rfl) ⟨480165, by rfl⟩ : syracuseStep 1280441 = 960331) B960331
theorem B1444385 : Blo 758332 1444385 := bstep (se 2 (by rfl) ⟨541644, by rfl⟩ : syracuseStep 1444385 = 1083289) B1083289
theorem B1706615 : Blo 758332 1706615 := bstep (se 1 (by rfl) ⟨1279961, by rfl⟩ : syracuseStep 1706615 = 2559923) B2559923
theorem B2886263 : Blo 758332 2886263 := bstep (se 1 (by rfl) ⟨2164697, by rfl⟩ : syracuseStep 2886263 = 4329395) B4329395
theorem B854671 : Blo 758332 854671 := bstep (se 1 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 854671 = 1282007) B1282007
theorem B2165449 : Blo 758332 2165449 := bstep (se 2 (by rfl) ⟨812043, by rfl⟩ : syracuseStep 2165449 = 1624087) B1624087
theorem B1706795 : Blo 758332 1706795 := bstep (se 1 (by rfl) ⟨1280096, by rfl⟩ : syracuseStep 1706795 = 2560193) B2560193
theorem B1215503 : Blo 758332 1215503 := bstep (se 1 (by rfl) ⟨911627, by rfl⟩ : syracuseStep 1215503 = 1823255) B1823255
theorem B1281143 : Blo 758332 1281143 := bstep (se 1 (by rfl) ⟨960857, by rfl⟩ : syracuseStep 1281143 = 1921715) B1921715
theorem B855175 : Blo 758332 855175 := bstep (se 1 (by rfl) ⟨641381, by rfl⟩ : syracuseStep 855175 = 1282763) B1282763
theorem B1707155 : Blo 758332 1707155 := bstep (se 1 (by rfl) ⟨1280366, by rfl⟩ : syracuseStep 1707155 = 2560733) B2560733
theorem B1707209 : Blo 758332 1707209 := bstep (se 2 (by rfl) ⟨640203, by rfl⟩ : syracuseStep 1707209 = 1280407) B1280407
theorem B855355 : Blo 758332 855355 := bstep (se 1 (by rfl) ⟨641516, by rfl⟩ : syracuseStep 855355 = 1283033) B1283033
theorem B9244039 : Blo 758332 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B2919827 : Blo 758332 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B1084843 : Blo 758332 1084843 := bstep (se 1 (by rfl) ⟨813632, by rfl⟩ : syracuseStep 1084843 = 1627265) B1627265
theorem B4328963 : Blo 758332 4328963 := bstep (se 1 (by rfl) ⟨3246722, by rfl⟩ : syracuseStep 4328963 = 6493445) B6493445
theorem B3247627 : Blo 758332 3247627 := bstep (se 1 (by rfl) ⟨2435720, by rfl⟩ : syracuseStep 3247627 = 4871441) B4871441
theorem B1281595 : Blo 758332 1281595 := bstep (se 1 (by rfl) ⟨961196, by rfl⟩ : syracuseStep 1281595 = 1922393) B1922393
theorem B2887235 : Blo 758332 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B3903095 : Blo 758332 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B1085071 : Blo 758332 1085071 := bstep (se 1 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 1085071 = 1627607) B1627607
theorem B1281737 : Blo 758332 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B111054563 : Blo 758332 111054563 := bstep (se 1 (by rfl) ⟨83290922, by rfl⟩ : syracuseStep 111054563 = 166581845) B166581845
theorem B855823 : Blo 758332 855823 := bstep (se 1 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 855823 = 1283735) B1283735
theorem B1707911 : Blo 758332 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B4099985 : Blo 758332 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B3084331 : Blo 758332 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B1708091 : Blo 758332 1708091 := bstep (se 1 (by rfl) ⟨1281068, by rfl⟩ : syracuseStep 1708091 = 2562137) B2562137
theorem B1708217 : Blo 758332 1708217 := bstep (se 2 (by rfl) ⟨640581, by rfl⟩ : syracuseStep 1708217 = 1281163) B1281163
theorem B23433461 : Blo 758332 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B856327 : Blo 758332 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B1282439 : Blo 758332 1282439 := bstep (se 1 (by rfl) ⟨961829, by rfl⟩ : syracuseStep 1282439 = 1923659) B1923659
theorem B2560409 : Blo 758332 2560409 := bstep (se 2 (by rfl) ⟨960153, by rfl⟩ : syracuseStep 2560409 = 1920307) B1920307
theorem B1446329 : Blo 758332 1446329 := bstep (se 2 (by rfl) ⟨542373, by rfl⟩ : syracuseStep 1446329 = 1084747) B1084747
theorem B856507 : Blo 758332 856507 := bstep (se 1 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 856507 = 1284761) B1284761
theorem B2167307 : Blo 758332 2167307 := bstep (se 1 (by rfl) ⟨1625480, by rfl⟩ : syracuseStep 2167307 = 3250961) B3250961
theorem B1708559 : Blo 758332 1708559 := bstep (se 1 (by rfl) ⟨1281419, by rfl⟩ : syracuseStep 1708559 = 2562839) B2562839
theorem B1708577 : Blo 758332 1708577 := bstep (se 2 (by rfl) ⟨640716, by rfl⟩ : syracuseStep 1708577 = 1281433) B1281433
theorem B1217143 : Blo 758332 1217143 := bstep (se 1 (by rfl) ⟨912857, by rfl⟩ : syracuseStep 1217143 = 1825715) B1825715
theorem B758407 : Blo 758332 758407 := bstep (se 1 (by rfl) ⟨568805, by rfl⟩ : syracuseStep 758407 = 1137611) B1137611
theorem B758415 : Blo 758332 758415 := bstep (se 1 (by rfl) ⟨568811, by rfl⟩ : syracuseStep 758415 = 1137623) B1137623
theorem B758459 : Blo 758332 758459 := bstep (se 1 (by rfl) ⟨568844, by rfl⟩ : syracuseStep 758459 = 1137689) B1137689
theorem B758535 : Blo 758332 758535 := bstep (se 1 (by rfl) ⟨568901, by rfl⟩ : syracuseStep 758535 = 1137803) B1137803
theorem B758543 : Blo 758332 758543 := bstep (se 1 (by rfl) ⟨568907, by rfl⟩ : syracuseStep 758543 = 1137815) B1137815
theorem B758587 : Blo 758332 758587 := bstep (se 1 (by rfl) ⟨568940, by rfl⟩ : syracuseStep 758587 = 1137881) B1137881
theorem B1708919 : Blo 758332 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B758663 : Blo 758332 758663 := bstep (se 1 (by rfl) ⟨568997, by rfl⟩ : syracuseStep 758663 = 1137995) B1137995
theorem B758671 : Blo 758332 758671 := bstep (se 1 (by rfl) ⟨569003, by rfl⟩ : syracuseStep 758671 = 1138007) B1138007
theorem B856975 : Blo 758332 856975 := bstep (se 1 (by rfl) ⟨642731, by rfl⟩ : syracuseStep 856975 = 1285463) B1285463
theorem B758715 : Blo 758332 758715 := bstep (se 1 (by rfl) ⟨569036, by rfl⟩ : syracuseStep 758715 = 1138073) B1138073
theorem B758791 : Blo 758332 758791 := bstep (se 1 (by rfl) ⟨569093, by rfl⟩ : syracuseStep 758791 = 1138187) B1138187
theorem B758799 : Blo 758332 758799 := bstep (se 1 (by rfl) ⟨569099, by rfl⟩ : syracuseStep 758799 = 1138199) B1138199
theorem B1283087 : Blo 758332 1283087 := bstep (se 1 (by rfl) ⟨962315, by rfl⟩ : syracuseStep 1283087 = 1924631) B1924631
theorem B1709099 : Blo 758332 1709099 := bstep (se 1 (by rfl) ⟨1281824, by rfl⟩ : syracuseStep 1709099 = 2563649) B2563649
theorem B758843 : Blo 758332 758843 := bstep (se 1 (by rfl) ⟨569132, by rfl⟩ : syracuseStep 758843 = 1138265) B1138265
theorem B2561111 : Blo 758332 2561111 := bstep (se 1 (by rfl) ⟨1920833, by rfl⟩ : syracuseStep 2561111 = 3841667) B3841667
theorem B758919 : Blo 758332 758919 := bstep (se 1 (by rfl) ⟨569189, by rfl⟩ : syracuseStep 758919 = 1138379) B1138379
theorem B758927 : Blo 758332 758927 := bstep (se 1 (by rfl) ⟨569195, by rfl⟩ : syracuseStep 758927 = 1138391) B1138391
theorem B2167955 : Blo 758332 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B758971 : Blo 758332 758971 := bstep (se 1 (by rfl) ⟨569228, by rfl⟩ : syracuseStep 758971 = 1138457) B1138457
theorem B2888905 : Blo 758332 2888905 := bstep (se 2 (by rfl) ⟨1083339, by rfl⟩ : syracuseStep 2888905 = 2166679) B2166679
theorem B759047 : Blo 758332 759047 := bstep (se 1 (by rfl) ⟨569285, by rfl⟩ : syracuseStep 759047 = 1138571) B1138571
theorem B759055 : Blo 758332 759055 := bstep (se 1 (by rfl) ⟨569291, by rfl⟩ : syracuseStep 759055 = 1138583) B1138583
theorem B8656145 : Blo 758332 8656145 := bstep (se 2 (by rfl) ⟨3246054, by rfl⟩ : syracuseStep 8656145 = 6492109) B6492109
theorem B759099 : Blo 758332 759099 := bstep (se 1 (by rfl) ⟨569324, by rfl⟩ : syracuseStep 759099 = 1138649) B1138649
theorem B2168183 : Blo 758332 2168183 := bstep (se 1 (by rfl) ⟨1626137, by rfl⟩ : syracuseStep 2168183 = 3252275) B3252275
theorem B759175 : Blo 758332 759175 := bstep (se 1 (by rfl) ⟨569381, by rfl⟩ : syracuseStep 759175 = 1138763) B1138763
theorem B857479 : Blo 758332 857479 := bstep (se 1 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 857479 = 1286219) B1286219
theorem B759183 : Blo 758332 759183 := bstep (se 1 (by rfl) ⟨569387, by rfl⟩ : syracuseStep 759183 = 1138775) B1138775
theorem B1709459 : Blo 758332 1709459 := bstep (se 1 (by rfl) ⟨1282094, by rfl⟩ : syracuseStep 1709459 = 2564189) B2564189
theorem B759227 : Blo 758332 759227 := bstep (se 1 (by rfl) ⟨569420, by rfl⟩ : syracuseStep 759227 = 1138841) B1138841
theorem B1709513 : Blo 758332 1709513 := bstep (se 2 (by rfl) ⟨641067, by rfl⟩ : syracuseStep 1709513 = 1282135) B1282135
theorem B759303 : Blo 758332 759303 := bstep (se 1 (by rfl) ⟨569477, by rfl⟩ : syracuseStep 759303 = 1138955) B1138955
theorem B759311 : Blo 758332 759311 := bstep (se 1 (by rfl) ⟨569483, by rfl⟩ : syracuseStep 759311 = 1138967) B1138967
theorem B1283627 : Blo 758332 1283627 := bstep (se 1 (by rfl) ⟨962720, by rfl⟩ : syracuseStep 1283627 = 1925441) B1925441
theorem B759355 : Blo 758332 759355 := bstep (se 1 (by rfl) ⟨569516, by rfl⟩ : syracuseStep 759355 = 1139033) B1139033
theorem B2561597 : Blo 758332 2561597 := bstep (se 3 (by rfl) ⟨480299, by rfl⟩ : syracuseStep 2561597 = 960599) B960599
theorem B759431 : Blo 758332 759431 := bstep (se 1 (by rfl) ⟨569573, by rfl⟩ : syracuseStep 759431 = 1139147) B1139147
theorem B759439 : Blo 758332 759439 := bstep (se 1 (by rfl) ⟨569579, by rfl⟩ : syracuseStep 759439 = 1139159) B1139159
theorem B759483 : Blo 758332 759483 := bstep (se 1 (by rfl) ⟨569612, by rfl⟩ : syracuseStep 759483 = 1139225) B1139225
theorem B759559 : Blo 758332 759559 := bstep (se 1 (by rfl) ⟨569669, by rfl⟩ : syracuseStep 759559 = 1139339) B1139339
theorem B759567 : Blo 758332 759567 := bstep (se 1 (by rfl) ⟨569675, by rfl⟩ : syracuseStep 759567 = 1139351) B1139351
theorem B759611 : Blo 758332 759611 := bstep (se 1 (by rfl) ⟨569708, by rfl⟩ : syracuseStep 759611 = 1139417) B1139417
theorem B4331353 : Blo 758332 4331353 := bstep (se 2 (by rfl) ⟨1624257, by rfl⟩ : syracuseStep 4331353 = 3248515) B3248515
theorem B759687 : Blo 758332 759687 := bstep (se 1 (by rfl) ⟨569765, by rfl⟩ : syracuseStep 759687 = 1139531) B1139531
theorem B759695 : Blo 758332 759695 := bstep (se 1 (by rfl) ⟨569771, by rfl⟩ : syracuseStep 759695 = 1139543) B1139543
theorem B1284025 : Blo 758332 1284025 := bstep (se 2 (by rfl) ⟨481509, by rfl⟩ : syracuseStep 1284025 = 963019) B963019
theorem B759739 : Blo 758332 759739 := bstep (se 1 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 759739 = 1139609) B1139609
theorem B759815 : Blo 758332 759815 := bstep (se 1 (by rfl) ⟨569861, by rfl⟩ : syracuseStep 759815 = 1139723) B1139723
theorem B20846605 : Blo 758332 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B759823 : Blo 758332 759823 := bstep (se 1 (by rfl) ⟨569867, by rfl⟩ : syracuseStep 759823 = 1139735) B1139735
theorem B759867 : Blo 758332 759867 := bstep (se 1 (by rfl) ⟨569900, by rfl⟩ : syracuseStep 759867 = 1139801) B1139801
theorem B759943 : Blo 758332 759943 := bstep (se 1 (by rfl) ⟨569957, by rfl⟩ : syracuseStep 759943 = 1139915) B1139915
theorem B1710215 : Blo 758332 1710215 := bstep (se 1 (by rfl) ⟨1282661, by rfl⟩ : syracuseStep 1710215 = 2565323) B2565323
theorem B759951 : Blo 758332 759951 := bstep (se 1 (by rfl) ⟨569963, by rfl⟩ : syracuseStep 759951 = 1139927) B1139927
theorem B759995 : Blo 758332 759995 := bstep (se 1 (by rfl) ⟨569996, by rfl⟩ : syracuseStep 759995 = 1139993) B1139993
theorem B2595073 : Blo 758332 2595073 := bstep (se 2 (by rfl) ⟨973152, by rfl⟩ : syracuseStep 2595073 = 1946305) B1946305
theorem B760071 : Blo 758332 760071 := bstep (se 1 (by rfl) ⟨570053, by rfl⟩ : syracuseStep 760071 = 1140107) B1140107
theorem B760079 : Blo 758332 760079 := bstep (se 1 (by rfl) ⟨570059, by rfl⟩ : syracuseStep 760079 = 1140119) B1140119
theorem B6166817 : Blo 758332 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B760123 : Blo 758332 760123 := bstep (se 1 (by rfl) ⟨570092, by rfl⟩ : syracuseStep 760123 = 1140185) B1140185
theorem B1710395 : Blo 758332 1710395 := bstep (se 1 (by rfl) ⟨1282796, by rfl⟩ : syracuseStep 1710395 = 2565593) B2565593
theorem B3840371 : Blo 758332 3840371 := bstep (se 1 (by rfl) ⟨2880278, by rfl⟩ : syracuseStep 3840371 = 5760557) B5760557
theorem B760199 : Blo 758332 760199 := bstep (se 1 (by rfl) ⟨570149, by rfl⟩ : syracuseStep 760199 = 1140299) B1140299
theorem B760207 : Blo 758332 760207 := bstep (se 1 (by rfl) ⟨570155, by rfl⟩ : syracuseStep 760207 = 1140311) B1140311
theorem B1710521 : Blo 758332 1710521 := bstep (se 2 (by rfl) ⟨641445, by rfl⟩ : syracuseStep 1710521 = 1282891) B1282891
theorem B760251 : Blo 758332 760251 := bstep (se 1 (by rfl) ⟨570188, by rfl⟩ : syracuseStep 760251 = 1140377) B1140377
theorem B760327 : Blo 758332 760327 := bstep (se 1 (by rfl) ⟨570245, by rfl⟩ : syracuseStep 760327 = 1140491) B1140491
theorem B760335 : Blo 758332 760335 := bstep (se 1 (by rfl) ⟨570251, by rfl⟩ : syracuseStep 760335 = 1140503) B1140503
theorem B760379 : Blo 758332 760379 := bstep (se 1 (by rfl) ⟨570284, by rfl⟩ : syracuseStep 760379 = 1140569) B1140569
theorem B1284727 : Blo 758332 1284727 := bstep (se 1 (by rfl) ⟨963545, by rfl⟩ : syracuseStep 1284727 = 1927091) B1927091
theorem B760455 : Blo 758332 760455 := bstep (se 1 (by rfl) ⟨570341, by rfl⟩ : syracuseStep 760455 = 1140683) B1140683
theorem B760463 : Blo 758332 760463 := bstep (se 1 (by rfl) ⟨570347, by rfl⟩ : syracuseStep 760463 = 1140695) B1140695
theorem B760507 : Blo 758332 760507 := bstep (se 1 (by rfl) ⟨570380, by rfl⟩ : syracuseStep 760507 = 1140761) B1140761
theorem B760583 : Blo 758332 760583 := bstep (se 1 (by rfl) ⟨570437, by rfl⟩ : syracuseStep 760583 = 1140875) B1140875
theorem B1710863 : Blo 758332 1710863 := bstep (se 1 (by rfl) ⟨1283147, by rfl⟩ : syracuseStep 1710863 = 2566295) B2566295
theorem B760591 : Blo 758332 760591 := bstep (se 1 (by rfl) ⟨570443, by rfl⟩ : syracuseStep 760591 = 1140887) B1140887
theorem B1710881 : Blo 758332 1710881 := bstep (se 2 (by rfl) ⟨641580, by rfl⟩ : syracuseStep 1710881 = 1283161) B1283161
theorem B760635 : Blo 758332 760635 := bstep (se 1 (by rfl) ⟨570476, by rfl⟩ : syracuseStep 760635 = 1140953) B1140953
theorem B1284923 : Blo 758332 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B3840857 : Blo 758332 3840857 := bstep (se 2 (by rfl) ⟨1440321, by rfl⟩ : syracuseStep 3840857 = 2880643) B2880643
theorem B760711 : Blo 758332 760711 := bstep (se 1 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 760711 = 1141067) B1141067
theorem B760719 : Blo 758332 760719 := bstep (se 1 (by rfl) ⟨570539, by rfl⟩ : syracuseStep 760719 = 1141079) B1141079
theorem B2563001 : Blo 758332 2563001 := bstep (se 2 (by rfl) ⟨961125, by rfl⟩ : syracuseStep 2563001 = 1922251) B1922251
theorem B760763 : Blo 758332 760763 := bstep (se 1 (by rfl) ⟨570572, by rfl⟩ : syracuseStep 760763 = 1141145) B1141145
theorem B7805899 : Blo 758332 7805899 := bstep (se 1 (by rfl) ⟨5854424, by rfl⟩ : syracuseStep 7805899 = 11708849) B11708849
theorem B760839 : Blo 758332 760839 := bstep (se 1 (by rfl) ⟨570629, by rfl⟩ : syracuseStep 760839 = 1141259) B1141259
theorem B760847 : Blo 758332 760847 := bstep (se 1 (by rfl) ⟨570635, by rfl⟩ : syracuseStep 760847 = 1141271) B1141271
theorem B760891 : Blo 758332 760891 := bstep (se 1 (by rfl) ⟨570668, by rfl⟩ : syracuseStep 760891 = 1141337) B1141337
theorem B1711223 : Blo 758332 1711223 := bstep (se 1 (by rfl) ⟨1283417, by rfl⟩ : syracuseStep 1711223 = 2566835) B2566835
theorem B760967 : Blo 758332 760967 := bstep (se 1 (by rfl) ⟨570725, by rfl⟩ : syracuseStep 760967 = 1141451) B1141451
theorem B760975 : Blo 758332 760975 := bstep (se 1 (by rfl) ⟨570731, by rfl⟩ : syracuseStep 760975 = 1141463) B1141463
theorem B761019 : Blo 758332 761019 := bstep (se 1 (by rfl) ⟨570764, by rfl⟩ : syracuseStep 761019 = 1141529) B1141529
theorem B1285321 : Blo 758332 1285321 := bstep (se 2 (by rfl) ⟨481995, by rfl⟩ : syracuseStep 1285321 = 963991) B963991
theorem B761095 : Blo 758332 761095 := bstep (se 1 (by rfl) ⟨570821, by rfl⟩ : syracuseStep 761095 = 1141643) B1141643
theorem B761103 : Blo 758332 761103 := bstep (se 1 (by rfl) ⟨570827, by rfl⟩ : syracuseStep 761103 = 1141655) B1141655
theorem B1711403 : Blo 758332 1711403 := bstep (se 1 (by rfl) ⟨1283552, by rfl⟩ : syracuseStep 1711403 = 2567105) B2567105
theorem B5774651 : Blo 758332 5774651 := bstep (se 1 (by rfl) ⟨4330988, by rfl⟩ : syracuseStep 5774651 = 8661977) B8661977
theorem B761147 : Blo 758332 761147 := bstep (se 1 (by rfl) ⟨570860, by rfl⟩ : syracuseStep 761147 = 1141721) B1141721
theorem B2891123 : Blo 758332 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B761223 : Blo 758332 761223 := bstep (se 1 (by rfl) ⟨570917, by rfl⟩ : syracuseStep 761223 = 1141835) B1141835
theorem B761231 : Blo 758332 761231 := bstep (se 1 (by rfl) ⟨570923, by rfl⟩ : syracuseStep 761231 = 1141847) B1141847
theorem B761275 : Blo 758332 761275 := bstep (se 1 (by rfl) ⟨570956, by rfl⟩ : syracuseStep 761275 = 1141913) B1141913
theorem B761351 : Blo 758332 761351 := bstep (se 1 (by rfl) ⟨571013, by rfl⟩ : syracuseStep 761351 = 1142027) B1142027
theorem B2563595 : Blo 758332 2563595 := bstep (se 1 (by rfl) ⟨1922696, by rfl⟩ : syracuseStep 2563595 = 3845393) B3845393
theorem B761359 : Blo 758332 761359 := bstep (se 1 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 761359 = 1142039) B1142039
theorem B4333085 : Blo 758332 4333085 := bstep (se 3 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 4333085 = 1624907) B1624907
theorem B761403 : Blo 758332 761403 := bstep (se 1 (by rfl) ⟨571052, by rfl⟩ : syracuseStep 761403 = 1142105) B1142105
theorem B2563703 : Blo 758332 2563703 := bstep (se 1 (by rfl) ⟨1922777, by rfl⟩ : syracuseStep 2563703 = 3845555) B3845555
theorem B761479 : Blo 758332 761479 := bstep (se 1 (by rfl) ⟨571109, by rfl⟩ : syracuseStep 761479 = 1142219) B1142219
theorem B761487 : Blo 758332 761487 := bstep (se 1 (by rfl) ⟨571115, by rfl⟩ : syracuseStep 761487 = 1142231) B1142231
theorem B1711763 : Blo 758332 1711763 := bstep (se 1 (by rfl) ⟨1283822, by rfl⟩ : syracuseStep 1711763 = 2567645) B2567645
theorem B761531 : Blo 758332 761531 := bstep (se 1 (by rfl) ⟨571148, by rfl⟩ : syracuseStep 761531 = 1142297) B1142297
theorem B1711817 : Blo 758332 1711817 := bstep (se 2 (by rfl) ⟨641931, by rfl⟩ : syracuseStep 1711817 = 1283863) B1283863
theorem B761607 : Blo 758332 761607 := bstep (se 1 (by rfl) ⟨571205, by rfl⟩ : syracuseStep 761607 = 1142411) B1142411
theorem B761615 : Blo 758332 761615 := bstep (se 1 (by rfl) ⟨571211, by rfl⟩ : syracuseStep 761615 = 1142423) B1142423
theorem B3252001 : Blo 758332 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B761659 : Blo 758332 761659 := bstep (se 1 (by rfl) ⟨571244, by rfl⟩ : syracuseStep 761659 = 1142489) B1142489
theorem B761735 : Blo 758332 761735 := bstep (se 1 (by rfl) ⟨571301, by rfl⟩ : syracuseStep 761735 = 1142603) B1142603
theorem B1286023 : Blo 758332 1286023 := bstep (se 1 (by rfl) ⟨964517, by rfl⟩ : syracuseStep 1286023 = 1929035) B1929035
theorem B761743 : Blo 758332 761743 := bstep (se 1 (by rfl) ⟨571307, by rfl⟩ : syracuseStep 761743 = 1142615) B1142615
theorem B761787 : Blo 758332 761787 := bstep (se 1 (by rfl) ⟨571340, by rfl⟩ : syracuseStep 761787 = 1142681) B1142681
theorem B761863 : Blo 758332 761863 := bstep (se 1 (by rfl) ⟨571397, by rfl⟩ : syracuseStep 761863 = 1142795) B1142795
theorem B761871 : Blo 758332 761871 := bstep (se 1 (by rfl) ⟨571403, by rfl⟩ : syracuseStep 761871 = 1142807) B1142807
theorem B761915 : Blo 758332 761915 := bstep (se 1 (by rfl) ⟨571436, by rfl⟩ : syracuseStep 761915 = 1142873) B1142873
theorem B8659061 : Blo 758332 8659061 := bstep (se 5 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 8659061 = 811787) B811787
theorem B761991 : Blo 758332 761991 := bstep (se 1 (by rfl) ⟨571493, by rfl⟩ : syracuseStep 761991 = 1142987) B1142987
theorem B1155215 : Blo 758332 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B761999 : Blo 758332 761999 := bstep (se 1 (by rfl) ⟨571499, by rfl⟩ : syracuseStep 761999 = 1142999) B1142999
theorem B762043 : Blo 758332 762043 := bstep (se 1 (by rfl) ⟨571532, by rfl⟩ : syracuseStep 762043 = 1143065) B1143065
theorem B2564297 : Blo 758332 2564297 := bstep (se 2 (by rfl) ⟨961611, by rfl⟩ : syracuseStep 2564297 = 1923223) B1923223
theorem B4333769 : Blo 758332 4333769 := bstep (se 2 (by rfl) ⟨1625163, by rfl⟩ : syracuseStep 4333769 = 3250327) B3250327
theorem B762119 : Blo 758332 762119 := bstep (se 1 (by rfl) ⟨571589, by rfl⟩ : syracuseStep 762119 = 1143179) B1143179
theorem B762127 : Blo 758332 762127 := bstep (se 1 (by rfl) ⟨571595, by rfl⟩ : syracuseStep 762127 = 1143191) B1143191
theorem B762171 : Blo 758332 762171 := bstep (se 1 (by rfl) ⟨571628, by rfl⟩ : syracuseStep 762171 = 1143257) B1143257
theorem B1220923 : Blo 758332 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B1712519 : Blo 758332 1712519 := bstep (se 1 (by rfl) ⟨1284389, by rfl⟩ : syracuseStep 1712519 = 2568779) B2568779
theorem B762247 : Blo 758332 762247 := bstep (se 1 (by rfl) ⟨571685, by rfl⟩ : syracuseStep 762247 = 1143371) B1143371
theorem B762255 : Blo 758332 762255 := bstep (se 1 (by rfl) ⟨571691, by rfl⟩ : syracuseStep 762255 = 1143383) B1143383
theorem B4170131 : Blo 758332 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B762299 : Blo 758332 762299 := bstep (se 1 (by rfl) ⟨571724, by rfl⟩ : syracuseStep 762299 = 1143449) B1143449
theorem B1712699 : Blo 758332 1712699 := bstep (se 1 (by rfl) ⟨1284524, by rfl⟩ : syracuseStep 1712699 = 2569049) B2569049
theorem B1712825 : Blo 758332 1712825 := bstep (se 2 (by rfl) ⟨642309, by rfl⟩ : syracuseStep 1712825 = 1284619) B1284619
theorem B2433851 : Blo 758332 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B2564999 : Blo 758332 2564999 := bstep (se 1 (by rfl) ⟨1923749, by rfl⟩ : syracuseStep 2564999 = 3847499) B3847499
theorem B3842963 : Blo 758332 3842963 := bstep (se 1 (by rfl) ⟨2882222, by rfl⟩ : syracuseStep 3842963 = 5764445) B5764445
theorem B4400057 : Blo 758332 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B926735 : Blo 758332 926735 := bstep (se 1 (by rfl) ⟨695051, by rfl⟩ : syracuseStep 926735 = 1390103) B1390103
theorem B1713167 : Blo 758332 1713167 := bstep (se 1 (by rfl) ⟨1284875, by rfl⟩ : syracuseStep 1713167 = 2569751) B2569751
theorem B1713185 : Blo 758332 1713185 := bstep (se 2 (by rfl) ⟨642444, by rfl⟩ : syracuseStep 1713185 = 1284889) B1284889
theorem B1025083 : Blo 758332 1025083 := bstep (se 1 (by rfl) ⟨768812, by rfl⟩ : syracuseStep 1025083 = 1537625) B1537625
theorem B1156297 : Blo 758332 1156297 := bstep (se 2 (by rfl) ⟨433611, by rfl⟩ : syracuseStep 1156297 = 867223) B867223
theorem B3646721 : Blo 758332 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B2565377 : Blo 758332 2565377 := bstep (se 2 (by rfl) ⟨962016, by rfl⟩ : syracuseStep 2565377 = 1924033) B1924033
theorem B2434337 : Blo 758332 2434337 := bstep (se 2 (by rfl) ⟨912876, by rfl⟩ : syracuseStep 2434337 = 1825753) B1825753
theorem B1713527 : Blo 758332 1713527 := bstep (se 1 (by rfl) ⟨1285145, by rfl⟩ : syracuseStep 1713527 = 2570291) B2570291
theorem B2893265 : Blo 758332 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B960007 : Blo 758332 960007 := bstep (se 1 (by rfl) ⟨720005, by rfl⟩ : syracuseStep 960007 = 1440011) B1440011
theorem B1713707 : Blo 758332 1713707 := bstep (se 1 (by rfl) ⟨1285280, by rfl⟩ : syracuseStep 1713707 = 2570561) B2570561
theorem B2893583 : Blo 758332 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B2959163 : Blo 758332 2959163 := bstep (se 1 (by rfl) ⟨2219372, by rfl⟩ : syracuseStep 2959163 = 4438745) B4438745
theorem B2434951 : Blo 758332 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B1714067 : Blo 758332 1714067 := bstep (se 1 (by rfl) ⟨1285550, by rfl⟩ : syracuseStep 1714067 = 2571101) B2571101
theorem B960427 : Blo 758332 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B4335545 : Blo 758332 4335545 := bstep (se 2 (by rfl) ⟨1625829, by rfl⟩ : syracuseStep 4335545 = 3251659) B3251659
theorem B1714121 : Blo 758332 1714121 := bstep (se 2 (by rfl) ⟨642795, by rfl⟩ : syracuseStep 1714121 = 1285591) B1285591
theorem B2566187 : Blo 758332 2566187 := bstep (se 1 (by rfl) ⟨1924640, by rfl⟩ : syracuseStep 2566187 = 3849281) B3849281
theorem B960655 : Blo 758332 960655 := bstep (se 1 (by rfl) ⟨720491, by rfl⟩ : syracuseStep 960655 = 1440983) B1440983
theorem B10954925 : Blo 758332 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B1976729 : Blo 758332 1976729 := bstep (se 2 (by rfl) ⟨741273, by rfl⟩ : syracuseStep 1976729 = 1482547) B1482547
theorem B1157647 : Blo 758332 1157647 := bstep (se 1 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 1157647 = 1736471) B1736471
theorem B2468381 : Blo 758332 2468381 := bstep (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) B925643
theorem B1714823 : Blo 758332 1714823 := bstep (se 1 (by rfl) ⟨1286117, by rfl⟩ : syracuseStep 1714823 = 2572235) B2572235
theorem B1715003 : Blo 758332 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B961399 : Blo 758332 961399 := bstep (se 1 (by rfl) ⟨721049, by rfl⟩ : syracuseStep 961399 = 1442099) B1442099
theorem B1715129 : Blo 758332 1715129 := bstep (se 2 (by rfl) ⟨643173, by rfl⟩ : syracuseStep 1715129 = 1286347) B1286347
theorem B961723 : Blo 758332 961723 := bstep (se 1 (by rfl) ⟨721292, by rfl⟩ : syracuseStep 961723 = 1442585) B1442585
theorem B2567483 : Blo 758332 2567483 := bstep (se 1 (by rfl) ⟨1925612, by rfl⟩ : syracuseStep 2567483 = 3851225) B3851225
theorem B1158571 : Blo 758332 1158571 := bstep (se 1 (by rfl) ⟨868928, by rfl⟩ : syracuseStep 1158571 = 1737857) B1737857
theorem B1027591 : Blo 758332 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B1027657 : Blo 758332 1027657 := bstep (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) B770743
theorem B2436695 : Blo 758332 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B7319159 : Blo 758332 7319159 := bstep (se 1 (by rfl) ⟨5489369, by rfl⟩ : syracuseStep 7319159 = 10978739) B10978739
theorem B962219 : Blo 758332 962219 := bstep (se 1 (by rfl) ⟨721664, by rfl⟩ : syracuseStep 962219 = 1443329) B1443329
theorem B14593715 : Blo 758332 14593715 := bstep (se 1 (by rfl) ⟨10945286, by rfl⟩ : syracuseStep 14593715 = 21890573) B21890573
theorem B2633473 : Blo 758332 2633473 := bstep (se 2 (by rfl) ⟨987552, by rfl⟩ : syracuseStep 2633473 = 1975105) B1975105
theorem B2567969 : Blo 758332 2567969 := bstep (se 2 (by rfl) ⟨962988, by rfl⟩ : syracuseStep 2567969 = 1925977) B1925977
theorem B4337459 : Blo 758332 4337459 := bstep (se 1 (by rfl) ⟨3253094, by rfl⟩ : syracuseStep 4337459 = 6506189) B6506189
theorem B3846041 : Blo 758332 3846041 := bstep (se 2 (by rfl) ⟨1442265, by rfl⟩ : syracuseStep 3846041 = 2884531) B2884531
theorem B962695 : Blo 758332 962695 := bstep (se 1 (by rfl) ⟨722021, by rfl⟩ : syracuseStep 962695 = 1444043) B1444043
theorem B1847567 : Blo 758332 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B2568563 : Blo 758332 2568563 := bstep (se 1 (by rfl) ⟨1926422, by rfl⟩ : syracuseStep 2568563 = 3852845) B3852845
theorem B1028495 : Blo 758332 1028495 := bstep (se 1 (by rfl) ⟨771371, by rfl⟩ : syracuseStep 1028495 = 1542743) B1542743
theorem B5779997 : Blo 758332 5779997 := bstep (se 3 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 5779997 = 2167499) B2167499
theorem B5485099 : Blo 758332 5485099 := bstep (se 1 (by rfl) ⟨4113824, by rfl⟩ : syracuseStep 5485099 = 8227649) B8227649
theorem B8237645 : Blo 758332 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B963191 : Blo 758332 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B1389241 : Blo 758332 1389241 := bstep (se 2 (by rfl) ⟨520965, by rfl⟩ : syracuseStep 1389241 = 1041931) B1041931
theorem B963343 : Blo 758332 963343 := bstep (se 1 (by rfl) ⟨722507, by rfl⟩ : syracuseStep 963343 = 1445015) B1445015
theorem B8237861 : Blo 758332 8237861 := bstep (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) B1544599
theorem B963515 : Blo 758332 963515 := bstep (se 1 (by rfl) ⟨722636, by rfl⟩ : syracuseStep 963515 = 1445273) B1445273
theorem B3650507 : Blo 758332 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B29209571 : Blo 758332 29209571 := bstep (se 1 (by rfl) ⟨21907178, by rfl⟩ : syracuseStep 29209571 = 43814357) B43814357
theorem B4338917 : Blo 758332 4338917 := bstep (se 4 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 4338917 = 813547) B813547
theorem B5191235 : Blo 758332 5191235 := bstep (se 1 (by rfl) ⟨3893426, by rfl⟩ : syracuseStep 5191235 = 7786853) B7786853
theorem B4175479 : Blo 758332 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B6502193 : Blo 758332 6502193 := bstep (se 2 (by rfl) ⟨2438322, by rfl⟩ : syracuseStep 6502193 = 4876645) B4876645
theorem B964487 : Blo 758332 964487 := bstep (se 1 (by rfl) ⟨723365, by rfl⟩ : syracuseStep 964487 = 1446731) B1446731
theorem B4339601 : Blo 758332 4339601 := bstep (se 2 (by rfl) ⟨1627350, by rfl⟩ : syracuseStep 4339601 = 3254701) B3254701
theorem B2308505 : Blo 758332 2308505 := bstep (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) B1731379
theorem B3848633 : Blo 758332 3848633 := bstep (se 2 (by rfl) ⟨1443237, by rfl⟩ : syracuseStep 3848633 = 2886475) B2886475
theorem B6502841 : Blo 758332 6502841 := bstep (se 2 (by rfl) ⟨2438565, by rfl⟩ : syracuseStep 6502841 = 4877131) B4877131
theorem B20757059 : Blo 758332 20757059 := bstep (se 1 (by rfl) ⟨15567794, by rfl⟩ : syracuseStep 20757059 = 31135589) B31135589
theorem B22166135 : Blo 758332 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B3652411 : Blo 758332 3652411 := bstep (se 1 (by rfl) ⟨2739308, by rfl⟩ : syracuseStep 3652411 = 5478617) B5478617
theorem B2571155 : Blo 758332 2571155 := bstep (se 1 (by rfl) ⟨1928366, by rfl⟩ : syracuseStep 2571155 = 3856733) B3856733
theorem B4340627 : Blo 758332 4340627 := bstep (se 1 (by rfl) ⟨3255470, by rfl⟩ : syracuseStep 4340627 = 6510941) B6510941
theorem B3161207 : Blo 758332 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B7126217 : Blo 758332 7126217 := bstep (se 2 (by rfl) ⟨2672331, by rfl⟩ : syracuseStep 7126217 = 5344663) B5344663
theorem B8207675 : Blo 758332 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B2735545 : Blo 758332 2735545 := bstep (se 2 (by rfl) ⟨1025829, by rfl⟩ : syracuseStep 2735545 = 2051659) B2051659
theorem B2080289 : Blo 758332 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B3849929 : Blo 758332 3849929 := bstep (se 2 (by rfl) ⟨1443723, by rfl⟩ : syracuseStep 3849929 = 2887447) B2887447
theorem B868487 : Blo 758332 868487 := bstep (se 1 (by rfl) ⟨651365, by rfl⟩ : syracuseStep 868487 = 1302731) B1302731
theorem B2572559 : Blo 758332 2572559 := bstep (se 1 (by rfl) ⟨1929419, by rfl⟩ : syracuseStep 2572559 = 3858839) B3858839
theorem B2310515 : Blo 758332 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B2572829 : Blo 758332 2572829 := bstep (se 3 (by rfl) ⟨482405, by rfl⟩ : syracuseStep 2572829 = 964811) B964811
theorem B4112963 : Blo 758332 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B16695875 : Blo 758332 16695875 := bstep (se 1 (by rfl) ⟨12521906, by rfl⟩ : syracuseStep 16695875 = 25043813) B25043813
theorem B6505231 : Blo 758332 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B2736929 : Blo 758332 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B5784371 : Blo 758332 5784371 := bstep (se 1 (by rfl) ⟨4338278, by rfl⟩ : syracuseStep 5784371 = 8676557) B8676557
theorem B7324505 : Blo 758332 7324505 := bstep (se 2 (by rfl) ⟨2746689, by rfl⟩ : syracuseStep 7324505 = 5493379) B5493379
theorem B4113287 : Blo 758332 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B3654659 : Blo 758332 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B8242181 : Blo 758332 8242181 := bstep (se 4 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 8242181 = 1545409) B1545409
theorem B7292825 : Blo 758332 7292825 := bstep (se 2 (by rfl) ⟨2734809, by rfl⟩ : syracuseStep 7292825 = 5469619) B5469619
theorem B1099783 : Blo 758332 1099783 := bstep (se 1 (by rfl) ⟨824837, by rfl⟩ : syracuseStep 1099783 = 1649675) B1649675
theorem B1460359 : Blo 758332 1460359 := bstep (se 1 (by rfl) ⟨1095269, by rfl⟩ : syracuseStep 1460359 = 2190539) B2190539
theorem B12503285 : Blo 758332 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B9226871 : Blo 758332 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B3296015 : Blo 758332 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B3656657 : Blo 758332 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B14797835 : Blo 758332 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B3132503 : Blo 758332 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B1920257 : Blo 758332 1920257 := bstep (se 2 (by rfl) ⟨720096, by rfl⟩ : syracuseStep 1920257 = 1440193) B1440193
theorem B125062501 : Blo 758332 125062501 := bstep (se 4 (by rfl) ⟨11724609, by rfl⟩ : syracuseStep 125062501 = 23449219) B23449219
theorem B4116055 : Blo 758332 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B1920631 : Blo 758332 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B1822409 : Blo 758332 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B2051855 : Blo 758332 2051855 := bstep (se 1 (by rfl) ⟨1538891, by rfl⟩ : syracuseStep 2051855 = 3077783) B3077783
theorem B1921067 : Blo 758332 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B6181379 : Blo 758332 6181379 := bstep (se 1 (by rfl) ⟨4636034, by rfl⟩ : syracuseStep 6181379 = 9272069) B9272069
theorem B159896081 : Blo 758332 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B3461699 : Blo 758332 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B4444901 : Blo 758332 4444901 := bstep (se 4 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 4444901 = 833419) B833419
theorem B1626923 : Blo 758332 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B1921907 : Blo 758332 1921907 := bstep (se 1 (by rfl) ⟨1441430, by rfl⟩ : syracuseStep 1921907 = 2882861) B2882861
theorem B12342131 : Blo 758332 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1921927 : Blo 758332 1921927 := bstep (se 1 (by rfl) ⟨1441445, by rfl⟩ : syracuseStep 1921927 = 2882891) B2882891
theorem B11719685 : Blo 758332 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B1627283 : Blo 758332 1627283 := bstep (se 1 (by rfl) ⟨1220462, by rfl⟩ : syracuseStep 1627283 = 2440925) B2440925
theorem B1922201 : Blo 758332 1922201 := bstep (se 2 (by rfl) ⟨720825, by rfl⟩ : syracuseStep 1922201 = 1441651) B1441651
theorem B1922363 : Blo 758332 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B3855761 : Blo 758332 3855761 := bstep (se 2 (by rfl) ⟨1445910, by rfl⟩ : syracuseStep 3855761 = 2891821) B2891821
theorem B1922575 : Blo 758332 1922575 := bstep (se 1 (by rfl) ⟨1441931, by rfl⟩ : syracuseStep 1922575 = 2883863) B2883863
theorem B17553125 : Blo 758332 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B3659501 : Blo 758332 3659501 := bstep (se 3 (by rfl) ⟨686156, by rfl⟩ : syracuseStep 3659501 = 1372313) B1372313
theorem B1922849 : Blo 758332 1922849 := bstep (se 2 (by rfl) ⟨721068, by rfl⟩ : syracuseStep 1922849 = 1442137) B1442137
theorem B4118323 : Blo 758332 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B13162769 : Blo 758332 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B4118843 : Blo 758332 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B2054585 : Blo 758332 2054585 := bstep (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) B1540939
theorem B1825291 : Blo 758332 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B1923851 : Blo 758332 1923851 := bstep (se 1 (by rfl) ⟨1442888, by rfl⟩ : syracuseStep 1923851 = 2885777) B2885777
theorem B1137527 : Blo 758332 1137527 := bstep (se 1 (by rfl) ⟨853145, by rfl⟩ : syracuseStep 1137527 = 1706291) B1706291
theorem B1137551 : Blo 758332 1137551 := bstep (se 1 (by rfl) ⟨853163, by rfl⟩ : syracuseStep 1137551 = 1706327) B1706327
theorem B1137593 : Blo 758332 1137593 := bstep (se 2 (by rfl) ⟨426597, by rfl⟩ : syracuseStep 1137593 = 853195) B853195
theorem B1137671 : Blo 758332 1137671 := bstep (se 1 (by rfl) ⟨853253, by rfl⟩ : syracuseStep 1137671 = 1706507) B1706507
theorem B1137707 : Blo 758332 1137707 := bstep (se 1 (by rfl) ⟨853280, by rfl⟩ : syracuseStep 1137707 = 1706561) B1706561
theorem B1137737 : Blo 758332 1137737 := bstep (se 2 (by rfl) ⟨426651, by rfl⟩ : syracuseStep 1137737 = 853303) B853303
theorem B1137851 : Blo 758332 1137851 := bstep (se 1 (by rfl) ⟨853388, by rfl⟩ : syracuseStep 1137851 = 1706777) B1706777
theorem B10378477 : Blo 758332 10378477 := bstep (se 3 (by rfl) ⟨1945964, by rfl⟩ : syracuseStep 10378477 = 3891929) B3891929
theorem B1137911 : Blo 758332 1137911 := bstep (se 1 (by rfl) ⟨853433, by rfl⟩ : syracuseStep 1137911 = 1706867) B1706867
theorem B1137935 : Blo 758332 1137935 := bstep (se 1 (by rfl) ⟨853451, by rfl⟩ : syracuseStep 1137935 = 1706903) B1706903
theorem B1137977 : Blo 758332 1137977 := bstep (se 2 (by rfl) ⟨426741, by rfl⟩ : syracuseStep 1137977 = 853483) B853483
theorem B1138055 : Blo 758332 1138055 := bstep (se 1 (by rfl) ⟨853541, by rfl⟩ : syracuseStep 1138055 = 1707083) B1707083
theorem B1924499 : Blo 758332 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B1138091 : Blo 758332 1138091 := bstep (se 1 (by rfl) ⟨853568, by rfl⟩ : syracuseStep 1138091 = 1707137) B1707137
theorem B1138121 : Blo 758332 1138121 := bstep (se 2 (by rfl) ⟨426795, by rfl⟩ : syracuseStep 1138121 = 853591) B853591
theorem B3857867 : Blo 758332 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B1138235 : Blo 758332 1138235 := bstep (se 1 (by rfl) ⟨853676, by rfl⟩ : syracuseStep 1138235 = 1707353) B1707353
theorem B1138295 : Blo 758332 1138295 := bstep (se 1 (by rfl) ⟨853721, by rfl⟩ : syracuseStep 1138295 = 1707443) B1707443
theorem B1138319 : Blo 758332 1138319 := bstep (se 1 (by rfl) ⟨853739, by rfl⟩ : syracuseStep 1138319 = 1707479) B1707479
theorem B16408241 : Blo 758332 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B1138361 : Blo 758332 1138361 := bstep (se 2 (by rfl) ⟨426885, by rfl⟩ : syracuseStep 1138361 = 853771) B853771
theorem B1924793 : Blo 758332 1924793 := bstep (se 2 (by rfl) ⟨721797, by rfl⟩ : syracuseStep 1924793 = 1443595) B1443595
theorem B1138439 : Blo 758332 1138439 := bstep (se 1 (by rfl) ⟨853829, by rfl⟩ : syracuseStep 1138439 = 1707659) B1707659
theorem B3858191 : Blo 758332 3858191 := bstep (se 1 (by rfl) ⟨2893643, by rfl⟩ : syracuseStep 3858191 = 5787287) B5787287
theorem B1138475 : Blo 758332 1138475 := bstep (se 1 (by rfl) ⟨853856, by rfl⟩ : syracuseStep 1138475 = 1707713) B1707713
theorem B1138505 : Blo 758332 1138505 := bstep (se 2 (by rfl) ⟨426939, by rfl⟩ : syracuseStep 1138505 = 853879) B853879
theorem B1138619 : Blo 758332 1138619 := bstep (se 1 (by rfl) ⟨853964, by rfl⟩ : syracuseStep 1138619 = 1707929) B1707929
theorem B1138679 : Blo 758332 1138679 := bstep (se 1 (by rfl) ⟨854009, by rfl⟩ : syracuseStep 1138679 = 1708019) B1708019
theorem B1138703 : Blo 758332 1138703 := bstep (se 1 (by rfl) ⟨854027, by rfl⟩ : syracuseStep 1138703 = 1708055) B1708055
theorem B1302571 : Blo 758332 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B1138745 : Blo 758332 1138745 := bstep (se 2 (by rfl) ⟨427029, by rfl⟩ : syracuseStep 1138745 = 854059) B854059
theorem B1138823 : Blo 758332 1138823 := bstep (se 1 (by rfl) ⟨854117, by rfl⟩ : syracuseStep 1138823 = 1708235) B1708235
theorem B1138859 : Blo 758332 1138859 := bstep (se 1 (by rfl) ⟨854144, by rfl⟩ : syracuseStep 1138859 = 1708289) B1708289
theorem B4874413 : Blo 758332 4874413 := bstep (se 3 (by rfl) ⟨913952, by rfl⟩ : syracuseStep 4874413 = 1827905) B1827905
theorem B1138889 : Blo 758332 1138889 := bstep (se 2 (by rfl) ⟨427083, by rfl⟩ : syracuseStep 1138889 = 854167) B854167
theorem B1368335 : Blo 758332 1368335 := bstep (se 1 (by rfl) ⟨1026251, by rfl⟩ : syracuseStep 1368335 = 2052503) B2052503
theorem B1139003 : Blo 758332 1139003 := bstep (se 1 (by rfl) ⟨854252, by rfl⟩ : syracuseStep 1139003 = 1708505) B1708505
theorem B1925491 : Blo 758332 1925491 := bstep (se 1 (by rfl) ⟨1444118, by rfl⟩ : syracuseStep 1925491 = 2888237) B2888237
theorem B1139063 : Blo 758332 1139063 := bstep (se 1 (by rfl) ⟨854297, by rfl⟩ : syracuseStep 1139063 = 1708595) B1708595
theorem B1139087 : Blo 758332 1139087 := bstep (se 1 (by rfl) ⟨854315, by rfl⟩ : syracuseStep 1139087 = 1708631) B1708631
theorem B1139129 : Blo 758332 1139129 := bstep (se 2 (by rfl) ⟨427173, by rfl⟩ : syracuseStep 1139129 = 854347) B854347
theorem B1925633 : Blo 758332 1925633 := bstep (se 2 (by rfl) ⟨722112, by rfl⟩ : syracuseStep 1925633 = 1444225) B1444225
theorem B1139207 : Blo 758332 1139207 := bstep (se 1 (by rfl) ⟨854405, by rfl⟩ : syracuseStep 1139207 = 1708811) B1708811
theorem B1139243 : Blo 758332 1139243 := bstep (se 1 (by rfl) ⟨854432, by rfl⟩ : syracuseStep 1139243 = 1708865) B1708865
theorem B1139273 : Blo 758332 1139273 := bstep (se 2 (by rfl) ⟨427227, by rfl⟩ : syracuseStep 1139273 = 854455) B854455
theorem B1368695 : Blo 758332 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1139387 : Blo 758332 1139387 := bstep (se 1 (by rfl) ⟨854540, by rfl⟩ : syracuseStep 1139387 = 1709081) B1709081
theorem B1139447 : Blo 758332 1139447 := bstep (se 1 (by rfl) ⟨854585, by rfl⟩ : syracuseStep 1139447 = 1709171) B1709171
theorem B2745089 : Blo 758332 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B1139471 : Blo 758332 1139471 := bstep (se 1 (by rfl) ⟨854603, by rfl⟩ : syracuseStep 1139471 = 1709207) B1709207
theorem B1139513 : Blo 758332 1139513 := bstep (se 2 (by rfl) ⟨427317, by rfl⟩ : syracuseStep 1139513 = 854635) B854635
theorem B1139591 : Blo 758332 1139591 := bstep (se 1 (by rfl) ⟨854693, by rfl⟩ : syracuseStep 1139591 = 1709387) B1709387
theorem B1139627 : Blo 758332 1139627 := bstep (se 1 (by rfl) ⟨854720, by rfl⟩ : syracuseStep 1139627 = 1709441) B1709441
theorem B1139657 : Blo 758332 1139657 := bstep (se 2 (by rfl) ⟨427371, by rfl⟩ : syracuseStep 1139657 = 854743) B854743
theorem B1926089 : Blo 758332 1926089 := bstep (se 2 (by rfl) ⟨722283, by rfl⟩ : syracuseStep 1926089 = 1444567) B1444567
theorem B1139771 : Blo 758332 1139771 := bstep (se 1 (by rfl) ⟨854828, by rfl⟩ : syracuseStep 1139771 = 1709657) B1709657
theorem B1139831 : Blo 758332 1139831 := bstep (se 1 (by rfl) ⟨854873, by rfl⟩ : syracuseStep 1139831 = 1709747) B1709747
theorem B1139855 : Blo 758332 1139855 := bstep (se 1 (by rfl) ⟨854891, by rfl⟩ : syracuseStep 1139855 = 1709783) B1709783
theorem B4678829 : Blo 758332 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1139897 : Blo 758332 1139897 := bstep (se 2 (by rfl) ⟨427461, by rfl⟩ : syracuseStep 1139897 = 854923) B854923
theorem B1139975 : Blo 758332 1139975 := bstep (se 1 (by rfl) ⟨854981, by rfl⟩ : syracuseStep 1139975 = 1709963) B1709963
theorem B1369387 : Blo 758332 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B1140011 : Blo 758332 1140011 := bstep (se 1 (by rfl) ⟨855008, by rfl⟩ : syracuseStep 1140011 = 1710017) B1710017
theorem B1926443 : Blo 758332 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B1140041 : Blo 758332 1140041 := bstep (se 2 (by rfl) ⟨427515, by rfl⟩ : syracuseStep 1140041 = 855031) B855031
theorem B1140155 : Blo 758332 1140155 := bstep (se 1 (by rfl) ⟨855116, by rfl⟩ : syracuseStep 1140155 = 1710233) B1710233
theorem B1140215 : Blo 758332 1140215 := bstep (se 1 (by rfl) ⟨855161, by rfl⟩ : syracuseStep 1140215 = 1710323) B1710323
theorem B1140239 : Blo 758332 1140239 := bstep (se 1 (by rfl) ⟨855179, by rfl⟩ : syracuseStep 1140239 = 1710359) B1710359
theorem B1140281 : Blo 758332 1140281 := bstep (se 2 (by rfl) ⟨427605, by rfl⟩ : syracuseStep 1140281 = 855211) B855211
theorem B1140359 : Blo 758332 1140359 := bstep (se 1 (by rfl) ⟨855269, by rfl⟩ : syracuseStep 1140359 = 1710539) B1710539
theorem B1140395 : Blo 758332 1140395 := bstep (se 1 (by rfl) ⟨855296, by rfl⟩ : syracuseStep 1140395 = 1710593) B1710593
theorem B1140425 : Blo 758332 1140425 := bstep (se 2 (by rfl) ⟨427659, by rfl⟩ : syracuseStep 1140425 = 855319) B855319
theorem B1140539 : Blo 758332 1140539 := bstep (se 1 (by rfl) ⟨855404, by rfl⟩ : syracuseStep 1140539 = 1710809) B1710809
theorem B1140599 : Blo 758332 1140599 := bstep (se 1 (by rfl) ⟨855449, by rfl⟩ : syracuseStep 1140599 = 1710899) B1710899
theorem B1140623 : Blo 758332 1140623 := bstep (se 1 (by rfl) ⟨855467, by rfl⟩ : syracuseStep 1140623 = 1710935) B1710935
theorem B1140665 : Blo 758332 1140665 := bstep (se 2 (by rfl) ⟨427749, by rfl⟩ : syracuseStep 1140665 = 855499) B855499
theorem B1140743 : Blo 758332 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B1140779 : Blo 758332 1140779 := bstep (se 1 (by rfl) ⟨855584, by rfl⟩ : syracuseStep 1140779 = 1711169) B1711169
theorem B1140809 : Blo 758332 1140809 := bstep (se 2 (by rfl) ⟨427803, by rfl⟩ : syracuseStep 1140809 = 855607) B855607
theorem B911531 : Blo 758332 911531 := bstep (se 1 (by rfl) ⟨683648, by rfl⟩ : syracuseStep 911531 = 1367297) B1367297
theorem B1140923 : Blo 758332 1140923 := bstep (se 1 (by rfl) ⟨855692, by rfl⟩ : syracuseStep 1140923 = 1711385) B1711385
theorem B1140983 : Blo 758332 1140983 := bstep (se 1 (by rfl) ⟨855737, by rfl⟩ : syracuseStep 1140983 = 1711475) B1711475
theorem B1927435 : Blo 758332 1927435 := bstep (se 1 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 1927435 = 2891153) B2891153
theorem B1141007 : Blo 758332 1141007 := bstep (se 1 (by rfl) ⟨855755, by rfl⟩ : syracuseStep 1141007 = 1711511) B1711511
theorem B2222369 : Blo 758332 2222369 := bstep (se 2 (by rfl) ⟨833388, by rfl⟩ : syracuseStep 2222369 = 1666777) B1666777
theorem B1141049 : Blo 758332 1141049 := bstep (se 2 (by rfl) ⟨427893, by rfl⟩ : syracuseStep 1141049 = 855787) B855787
theorem B1141127 : Blo 758332 1141127 := bstep (se 1 (by rfl) ⟨855845, by rfl⟩ : syracuseStep 1141127 = 1711691) B1711691
theorem B5564819 : Blo 758332 5564819 := bstep (se 1 (by rfl) ⟨4173614, by rfl⟩ : syracuseStep 5564819 = 8347229) B8347229
theorem B1927577 : Blo 758332 1927577 := bstep (se 2 (by rfl) ⟨722841, by rfl⟩ : syracuseStep 1927577 = 1445683) B1445683
theorem B1141163 : Blo 758332 1141163 := bstep (se 1 (by rfl) ⟨855872, by rfl⟩ : syracuseStep 1141163 = 1711745) B1711745
theorem B1141193 : Blo 758332 1141193 := bstep (se 2 (by rfl) ⟨427947, by rfl⟩ : syracuseStep 1141193 = 855895) B855895
theorem B1141307 : Blo 758332 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B1927739 : Blo 758332 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B1141367 : Blo 758332 1141367 := bstep (se 1 (by rfl) ⟨856025, by rfl⟩ : syracuseStep 1141367 = 1712051) B1712051
theorem B1141391 : Blo 758332 1141391 := bstep (se 1 (by rfl) ⟨856043, by rfl⟩ : syracuseStep 1141391 = 1712087) B1712087
theorem B1370771 : Blo 758332 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B1141433 : Blo 758332 1141433 := bstep (se 2 (by rfl) ⟨428037, by rfl⟩ : syracuseStep 1141433 = 856075) B856075
theorem B1141511 : Blo 758332 1141511 := bstep (se 1 (by rfl) ⟨856133, by rfl⟩ : syracuseStep 1141511 = 1712267) B1712267
theorem B1829665 : Blo 758332 1829665 := bstep (se 2 (by rfl) ⟨686124, by rfl⟩ : syracuseStep 1829665 = 1372249) B1372249
theorem B1141547 : Blo 758332 1141547 := bstep (se 1 (by rfl) ⟨856160, by rfl⟩ : syracuseStep 1141547 = 1712321) B1712321
theorem B1141577 : Blo 758332 1141577 := bstep (se 2 (by rfl) ⟨428091, by rfl⟩ : syracuseStep 1141577 = 856183) B856183
theorem B1928083 : Blo 758332 1928083 := bstep (se 1 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 1928083 = 2892125) B2892125
theorem B1141691 : Blo 758332 1141691 := bstep (se 1 (by rfl) ⟨856268, by rfl⟩ : syracuseStep 1141691 = 1712537) B1712537
theorem B1141751 : Blo 758332 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B1141775 : Blo 758332 1141775 := bstep (se 1 (by rfl) ⟨856331, by rfl⟩ : syracuseStep 1141775 = 1712663) B1712663
theorem B1928225 : Blo 758332 1928225 := bstep (se 2 (by rfl) ⟨723084, by rfl⟩ : syracuseStep 1928225 = 1446169) B1446169
theorem B1141817 : Blo 758332 1141817 := bstep (se 2 (by rfl) ⟨428181, by rfl⟩ : syracuseStep 1141817 = 856363) B856363
theorem B1141895 : Blo 758332 1141895 := bstep (se 1 (by rfl) ⟨856421, by rfl⟩ : syracuseStep 1141895 = 1712843) B1712843
theorem B1141931 : Blo 758332 1141931 := bstep (se 1 (by rfl) ⟨856448, by rfl⟩ : syracuseStep 1141931 = 1712897) B1712897
theorem B1141961 : Blo 758332 1141961 := bstep (se 2 (by rfl) ⟨428235, by rfl⟩ : syracuseStep 1141961 = 856471) B856471
theorem B1142075 : Blo 758332 1142075 := bstep (se 1 (by rfl) ⟨856556, by rfl⟩ : syracuseStep 1142075 = 1713113) B1713113
theorem B1142135 : Blo 758332 1142135 := bstep (se 1 (by rfl) ⟨856601, by rfl⟩ : syracuseStep 1142135 = 1713203) B1713203
theorem B4320647 : Blo 758332 4320647 := bstep (se 1 (by rfl) ⟨3240485, by rfl⟩ : syracuseStep 4320647 = 6480971) B6480971
theorem B1142159 : Blo 758332 1142159 := bstep (se 1 (by rfl) ⟨856619, by rfl⟩ : syracuseStep 1142159 = 1713239) B1713239
theorem B1142201 : Blo 758332 1142201 := bstep (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) B856651
theorem B1371593 : Blo 758332 1371593 := bstep (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) B1028695
theorem B1142279 : Blo 758332 1142279 := bstep (se 1 (by rfl) ⟨856709, by rfl⟩ : syracuseStep 1142279 = 1713419) B1713419
theorem B1142315 : Blo 758332 1142315 := bstep (se 1 (by rfl) ⟨856736, by rfl⟩ : syracuseStep 1142315 = 1713473) B1713473
theorem B1142345 : Blo 758332 1142345 := bstep (se 2 (by rfl) ⟨428379, by rfl⟩ : syracuseStep 1142345 = 856759) B856759
theorem B1142459 : Blo 758332 1142459 := bstep (se 1 (by rfl) ⟨856844, by rfl⟩ : syracuseStep 1142459 = 1713689) B1713689
theorem B1142519 : Blo 758332 1142519 := bstep (se 1 (by rfl) ⟨856889, by rfl⟩ : syracuseStep 1142519 = 1713779) B1713779
theorem B1142543 : Blo 758332 1142543 := bstep (se 1 (by rfl) ⟨856907, by rfl⟩ : syracuseStep 1142543 = 1713815) B1713815
theorem B1142585 : Blo 758332 1142585 := bstep (se 2 (by rfl) ⟨428469, by rfl⟩ : syracuseStep 1142585 = 856939) B856939
theorem B1142663 : Blo 758332 1142663 := bstep (se 1 (by rfl) ⟨856997, by rfl⟩ : syracuseStep 1142663 = 1713995) B1713995
theorem B913295 : Blo 758332 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B1142699 : Blo 758332 1142699 := bstep (se 1 (by rfl) ⟨857024, by rfl⟩ : syracuseStep 1142699 = 1714049) B1714049
theorem B1142729 : Blo 758332 1142729 := bstep (se 2 (by rfl) ⟨428523, by rfl⟩ : syracuseStep 1142729 = 857047) B857047
theorem B1929217 : Blo 758332 1929217 := bstep (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) B1446913
theorem B1142843 : Blo 758332 1142843 := bstep (se 1 (by rfl) ⟨857132, by rfl⟩ : syracuseStep 1142843 = 1714265) B1714265
theorem B4616279 : Blo 758332 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B1142903 : Blo 758332 1142903 := bstep (se 1 (by rfl) ⟨857177, by rfl⟩ : syracuseStep 1142903 = 1714355) B1714355
theorem B1142927 : Blo 758332 1142927 := bstep (se 1 (by rfl) ⟨857195, by rfl⟩ : syracuseStep 1142927 = 1714391) B1714391
theorem B1142969 : Blo 758332 1142969 := bstep (se 2 (by rfl) ⟨428613, by rfl⟩ : syracuseStep 1142969 = 857227) B857227
theorem B1143047 : Blo 758332 1143047 := bstep (se 1 (by rfl) ⟨857285, by rfl⟩ : syracuseStep 1143047 = 1714571) B1714571
theorem B1143083 : Blo 758332 1143083 := bstep (se 1 (by rfl) ⟨857312, by rfl⟩ : syracuseStep 1143083 = 1714625) B1714625
theorem B1143113 : Blo 758332 1143113 := bstep (se 2 (by rfl) ⟨428667, by rfl⟩ : syracuseStep 1143113 = 857335) B857335
theorem B913799 : Blo 758332 913799 := bstep (se 1 (by rfl) ⟨685349, by rfl⟩ : syracuseStep 913799 = 1370699) B1370699
theorem B5763473 : Blo 758332 5763473 := bstep (se 2 (by rfl) ⟨2161302, by rfl⟩ : syracuseStep 5763473 = 4322605) B4322605
theorem B1143227 : Blo 758332 1143227 := bstep (se 1 (by rfl) ⟨857420, by rfl⟩ : syracuseStep 1143227 = 1714841) B1714841
theorem B1143287 : Blo 758332 1143287 := bstep (se 1 (by rfl) ⟨857465, by rfl⟩ : syracuseStep 1143287 = 1714931) B1714931
theorem B1143311 : Blo 758332 1143311 := bstep (se 1 (by rfl) ⟨857483, by rfl⟩ : syracuseStep 1143311 = 1714967) B1714967
theorem B1143353 : Blo 758332 1143353 := bstep (se 2 (by rfl) ⟨428757, by rfl⟩ : syracuseStep 1143353 = 857515) B857515
theorem B1831511 : Blo 758332 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B1143431 : Blo 758332 1143431 := bstep (se 1 (by rfl) ⟨857573, by rfl⟩ : syracuseStep 1143431 = 1715147) B1715147
theorem B1143467 : Blo 758332 1143467 := bstep (se 1 (by rfl) ⟨857600, by rfl⟩ : syracuseStep 1143467 = 1715201) B1715201
theorem B914107 : Blo 758332 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B1143497 : Blo 758332 1143497 := bstep (se 2 (by rfl) ⟨428811, by rfl⟩ : syracuseStep 1143497 = 857623) B857623
theorem B8647397 : Blo 758332 8647397 := bstep (se 4 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 8647397 = 1621387) B1621387
theorem B2159561 : Blo 758332 2159561 := bstep (se 2 (by rfl) ⟨809835, by rfl⟩ : syracuseStep 2159561 = 1619671) B1619671
theorem B2159617 : Blo 758332 2159617 := bstep (se 2 (by rfl) ⟨809856, by rfl⟩ : syracuseStep 2159617 = 1619713) B1619713
theorem B914491 : Blo 758332 914491 := bstep (se 1 (by rfl) ⟨685868, by rfl⟩ : syracuseStep 914491 = 1371737) B1371737
theorem B4322423 : Blo 758332 4322423 := bstep (se 1 (by rfl) ⟨3241817, by rfl⟩ : syracuseStep 4322423 = 6483635) B6483635
theorem B2159959 : Blo 758332 2159959 := bstep (se 1 (by rfl) ⟨1619969, by rfl⟩ : syracuseStep 2159959 = 3239939) B3239939
theorem B3077585 : Blo 758332 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B5797453 : Blo 758332 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B4323131 : Blo 758332 4323131 := bstep (se 1 (by rfl) ⟨3242348, by rfl⟩ : syracuseStep 4323131 = 6484697) B6484697
theorem B2881433 : Blo 758332 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B5339033 : Blo 758332 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B5765903 : Blo 758332 5765903 := bstep (se 1 (by rfl) ⟨4324427, by rfl⟩ : syracuseStep 5765903 = 8648855) B8648855
theorem B1604623 : Blo 758332 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B4324589 : Blo 758332 4324589 := bstep (se 3 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 4324589 = 1621721) B1621721
theorem B3472793 : Blo 758332 3472793 := bstep (se 2 (by rfl) ⟨1302297, by rfl⟩ : syracuseStep 3472793 = 2604595) B2604595
theorem B1441415 : Blo 758332 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B7307009 : Blo 758332 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B5865509 : Blo 758332 5865509 := bstep (se 4 (by rfl) ⟨549891, by rfl⟩ : syracuseStep 5865509 = 1099783) B1099783
theorem B1441871 : Blo 758332 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B21921941 : Blo 758332 21921941 := bstep (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) B1027591
theorem B6947045 : Blo 758332 6947045 := bstep (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) B1302571
theorem B1540343 : Blo 758332 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B10944827 : Blo 758332 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B4883003 : Blo 758332 4883003 := bstep (se 1 (by rfl) ⟨3662252, by rfl⟩ : syracuseStep 4883003 = 7324505) B7324505
theorem B1442873 : Blo 758332 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B4326479 : Blo 758332 4326479 := bstep (se 1 (by rfl) ⟨3244859, by rfl⟩ : syracuseStep 4326479 = 6489719) B6489719
theorem B1541729 : Blo 758332 1541729 := bstep (se 2 (by rfl) ⟨578148, by rfl⟩ : syracuseStep 1541729 = 1156297) B1156297
theorem B853627 : Blo 758332 853627 := bstep (se 1 (by rfl) ⟨640220, by rfl⟩ : syracuseStep 853627 = 1280441) B1280441
theorem B2197343 : Blo 758332 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B9865223 : Blo 758332 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B1280009 : Blo 758332 1280009 := bstep (se 2 (by rfl) ⟨480003, by rfl⟩ : syracuseStep 1280009 = 960007) B960007
theorem B854095 : Blo 758332 854095 := bstep (se 1 (by rfl) ⟨640571, by rfl⟩ : syracuseStep 854095 = 1281143) B1281143
theorem B4327505 : Blo 758332 4327505 := bstep (se 2 (by rfl) ⟨1622814, by rfl⟩ : syracuseStep 4327505 = 3245629) B3245629
theorem B5769305 : Blo 758332 5769305 := bstep (se 2 (by rfl) ⟨2163489, by rfl⟩ : syracuseStep 5769305 = 4326979) B4326979
theorem B1280171 : Blo 758332 1280171 := bstep (se 1 (by rfl) ⟨960128, by rfl⟩ : syracuseStep 1280171 = 1920257) B1920257
theorem B2885975 : Blo 758332 2885975 := bstep (se 1 (by rfl) ⟨2164481, by rfl⟩ : syracuseStep 2885975 = 4328963) B4328963
theorem B1706345 : Blo 758332 1706345 := bstep (se 2 (by rfl) ⟨639879, by rfl⟩ : syracuseStep 1706345 = 1279759) B1279759
theorem B1214939 : Blo 758332 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B854491 : Blo 758332 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B1280569 : Blo 758332 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B1280711 : Blo 758332 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B1280873 : Blo 758332 1280873 := bstep (se 2 (by rfl) ⟨480327, by rfl⟩ : syracuseStep 1280873 = 960655) B960655
theorem B854959 : Blo 758332 854959 := bstep (se 1 (by rfl) ⟨641219, by rfl⟩ : syracuseStep 854959 = 1282439) B1282439
theorem B1706939 : Blo 758332 1706939 := bstep (se 1 (by rfl) ⟨1280204, by rfl⟩ : syracuseStep 1706939 = 2560409) B2560409
theorem B1444871 : Blo 758332 1444871 := bstep (se 1 (by rfl) ⟨1083653, by rfl⟩ : syracuseStep 1444871 = 2167307) B2167307
theorem B106597387 : Blo 758332 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B1707065 : Blo 758332 1707065 := bstep (se 2 (by rfl) ⟨640149, by rfl⟩ : syracuseStep 1707065 = 1280299) B1280299
theorem B1281271 : Blo 758332 1281271 := bstep (se 1 (by rfl) ⟨960953, by rfl⟩ : syracuseStep 1281271 = 1921907) B1921907
theorem B8228087 : Blo 758332 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B855391 : Blo 758332 855391 := bstep (se 1 (by rfl) ⟨641543, by rfl⟩ : syracuseStep 855391 = 1283087) B1283087
theorem B1543529 : Blo 758332 1543529 := bstep (se 2 (by rfl) ⟨578823, by rfl⟩ : syracuseStep 1543529 = 1157647) B1157647
theorem B1707407 : Blo 758332 1707407 := bstep (se 1 (by rfl) ⟨1280555, by rfl⟩ : syracuseStep 1707407 = 2561111) B2561111
theorem B1445303 : Blo 758332 1445303 := bstep (se 1 (by rfl) ⟨1083977, by rfl⟩ : syracuseStep 1445303 = 2167955) B2167955
theorem B1084855 : Blo 758332 1084855 := bstep (se 1 (by rfl) ⟨813641, by rfl⟩ : syracuseStep 1084855 = 1627283) B1627283
theorem B1281467 : Blo 758332 1281467 := bstep (se 1 (by rfl) ⟨961100, by rfl⟩ : syracuseStep 1281467 = 1922201) B1922201
theorem B5770763 : Blo 758332 5770763 := bstep (se 1 (by rfl) ⟨4328072, by rfl⟩ : syracuseStep 5770763 = 8656145) B8656145
theorem B1281575 : Blo 758332 1281575 := bstep (se 1 (by rfl) ⟨961181, by rfl⟩ : syracuseStep 1281575 = 1922363) B1922363
theorem B1445455 : Blo 758332 1445455 := bstep (se 1 (by rfl) ⟨1084091, by rfl⟩ : syracuseStep 1445455 = 2168183) B2168183
theorem B2887265 : Blo 758332 2887265 := bstep (se 2 (by rfl) ⟨1082724, by rfl⟩ : syracuseStep 2887265 = 2165449) B2165449
theorem B855751 : Blo 758332 855751 := bstep (se 1 (by rfl) ⟨641813, by rfl⟩ : syracuseStep 855751 = 1283627) B1283627
theorem B1707731 : Blo 758332 1707731 := bstep (se 1 (by rfl) ⟨1280798, by rfl⟩ : syracuseStep 1707731 = 2561597) B2561597
theorem B11702083 : Blo 758332 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B1281865 : Blo 758332 1281865 := bstep (se 2 (by rfl) ⟨480699, by rfl⟩ : syracuseStep 1281865 = 961399) B961399
theorem B1281899 : Blo 758332 1281899 := bstep (se 1 (by rfl) ⟨961424, by rfl⟩ : syracuseStep 1281899 = 1922849) B1922849
theorem B2560247 : Blo 758332 2560247 := bstep (se 1 (by rfl) ⟨1920185, by rfl⟩ : syracuseStep 2560247 = 3840371) B3840371
theorem B1282297 : Blo 758332 1282297 := bstep (se 2 (by rfl) ⟨480861, by rfl⟩ : syracuseStep 1282297 = 961723) B961723
theorem B1282567 : Blo 758332 1282567 := bstep (se 1 (by rfl) ⟨961925, by rfl⟩ : syracuseStep 1282567 = 1923851) B1923851
theorem B12325385 : Blo 758332 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B856615 : Blo 758332 856615 := bstep (se 1 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 856615 = 1284923) B1284923
theorem B1544761 : Blo 758332 1544761 := bstep (se 2 (by rfl) ⟨579285, by rfl⟩ : syracuseStep 1544761 = 1158571) B1158571
theorem B2560571 : Blo 758332 2560571 := bstep (se 1 (by rfl) ⟨1920428, by rfl⟩ : syracuseStep 2560571 = 3840857) B3840857
theorem B758351 : Blo 758332 758351 := bstep (se 1 (by rfl) ⟨568763, by rfl⟩ : syracuseStep 758351 = 1137527) B1137527
theorem B758367 : Blo 758332 758367 := bstep (se 1 (by rfl) ⟨568775, by rfl⟩ : syracuseStep 758367 = 1137551) B1137551
theorem B758395 : Blo 758332 758395 := bstep (se 1 (by rfl) ⟨568796, by rfl⟩ : syracuseStep 758395 = 1137593) B1137593
theorem B1708667 : Blo 758332 1708667 := bstep (se 1 (by rfl) ⟨1281500, by rfl⟩ : syracuseStep 1708667 = 2563001) B2563001
theorem B758447 : Blo 758332 758447 := bstep (se 1 (by rfl) ⟨568835, by rfl⟩ : syracuseStep 758447 = 1137671) B1137671
theorem B4330169 : Blo 758332 4330169 := bstep (se 2 (by rfl) ⟨1623813, by rfl⟩ : syracuseStep 4330169 = 3247627) B3247627
theorem B758471 : Blo 758332 758471 := bstep (se 1 (by rfl) ⟨568853, by rfl⟩ : syracuseStep 758471 = 1137707) B1137707
theorem B758491 : Blo 758332 758491 := bstep (se 1 (by rfl) ⟨568868, by rfl⟩ : syracuseStep 758491 = 1137737) B1137737
theorem B1708793 : Blo 758332 1708793 := bstep (se 2 (by rfl) ⟨640797, by rfl⟩ : syracuseStep 1708793 = 1281595) B1281595
theorem B758567 : Blo 758332 758567 := bstep (se 1 (by rfl) ⟨568925, by rfl⟩ : syracuseStep 758567 = 1137851) B1137851
theorem B2560841 : Blo 758332 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B758607 : Blo 758332 758607 := bstep (se 1 (by rfl) ⟨568955, by rfl⟩ : syracuseStep 758607 = 1137911) B1137911
theorem B758623 : Blo 758332 758623 := bstep (se 1 (by rfl) ⟨568967, by rfl⟩ : syracuseStep 758623 = 1137935) B1137935
theorem B1446761 : Blo 758332 1446761 := bstep (se 2 (by rfl) ⟨542535, by rfl⟩ : syracuseStep 1446761 = 1085071) B1085071
theorem B758651 : Blo 758332 758651 := bstep (se 1 (by rfl) ⟨568988, by rfl⟩ : syracuseStep 758651 = 1137977) B1137977
theorem B758703 : Blo 758332 758703 := bstep (se 1 (by rfl) ⟨569027, by rfl⟩ : syracuseStep 758703 = 1138055) B1138055
theorem B1282999 : Blo 758332 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B758727 : Blo 758332 758727 := bstep (se 1 (by rfl) ⟨569045, by rfl⟩ : syracuseStep 758727 = 1138091) B1138091
theorem B758747 : Blo 758332 758747 := bstep (se 1 (by rfl) ⟨569060, by rfl⟩ : syracuseStep 758747 = 1138121) B1138121
theorem B3511297 : Blo 758332 3511297 := bstep (se 2 (by rfl) ⟨1316736, by rfl⟩ : syracuseStep 3511297 = 2633473) B2633473
theorem B1709063 : Blo 758332 1709063 := bstep (se 1 (by rfl) ⟨1281797, by rfl⟩ : syracuseStep 1709063 = 2563595) B2563595
theorem B2888723 : Blo 758332 2888723 := bstep (se 1 (by rfl) ⟨2166542, by rfl⟩ : syracuseStep 2888723 = 4333085) B4333085
theorem B758823 : Blo 758332 758823 := bstep (se 1 (by rfl) ⟨569117, by rfl⟩ : syracuseStep 758823 = 1138235) B1138235
theorem B758863 : Blo 758332 758863 := bstep (se 1 (by rfl) ⟨569147, by rfl⟩ : syracuseStep 758863 = 1138295) B1138295
theorem B1709135 : Blo 758332 1709135 := bstep (se 1 (by rfl) ⟨1281851, by rfl⟩ : syracuseStep 1709135 = 2563703) B2563703
theorem B758879 : Blo 758332 758879 := bstep (se 1 (by rfl) ⟨569159, by rfl⟩ : syracuseStep 758879 = 1138319) B1138319
theorem B758907 : Blo 758332 758907 := bstep (se 1 (by rfl) ⟨569180, by rfl⟩ : syracuseStep 758907 = 1138361) B1138361
theorem B1283195 : Blo 758332 1283195 := bstep (se 1 (by rfl) ⟨962396, by rfl⟩ : syracuseStep 1283195 = 1924793) B1924793
theorem B758959 : Blo 758332 758959 := bstep (se 1 (by rfl) ⟨569219, by rfl⟩ : syracuseStep 758959 = 1138439) B1138439
theorem B758983 : Blo 758332 758983 := bstep (se 1 (by rfl) ⟨569237, by rfl⟩ : syracuseStep 758983 = 1138475) B1138475
theorem B759003 : Blo 758332 759003 := bstep (se 1 (by rfl) ⟨569252, by rfl⟩ : syracuseStep 759003 = 1138505) B1138505
theorem B759079 : Blo 758332 759079 := bstep (se 1 (by rfl) ⟨569309, by rfl⟩ : syracuseStep 759079 = 1138619) B1138619
theorem B759119 : Blo 758332 759119 := bstep (se 1 (by rfl) ⟨569339, by rfl⟩ : syracuseStep 759119 = 1138679) B1138679
theorem B759135 : Blo 758332 759135 := bstep (se 1 (by rfl) ⟨569351, by rfl⟩ : syracuseStep 759135 = 1138703) B1138703
theorem B759163 : Blo 758332 759163 := bstep (se 1 (by rfl) ⟨569372, by rfl⟩ : syracuseStep 759163 = 1138745) B1138745
theorem B5772707 : Blo 758332 5772707 := bstep (se 1 (by rfl) ⟨4329530, by rfl⟩ : syracuseStep 5772707 = 8659061) B8659061
theorem B759215 : Blo 758332 759215 := bstep (se 1 (by rfl) ⟨569411, by rfl⟩ : syracuseStep 759215 = 1138823) B1138823
theorem B759239 : Blo 758332 759239 := bstep (se 1 (by rfl) ⟨569429, by rfl⟩ : syracuseStep 759239 = 1138859) B1138859
theorem B759259 : Blo 758332 759259 := bstep (se 1 (by rfl) ⟨569444, by rfl⟩ : syracuseStep 759259 = 1138889) B1138889
theorem B1709531 : Blo 758332 1709531 := bstep (se 1 (by rfl) ⟨1282148, by rfl⟩ : syracuseStep 1709531 = 2564297) B2564297
theorem B2889179 : Blo 758332 2889179 := bstep (se 1 (by rfl) ⟨2166884, by rfl⟩ : syracuseStep 2889179 = 4333769) B4333769
theorem B1283593 : Blo 758332 1283593 := bstep (se 2 (by rfl) ⟨481347, by rfl⟩ : syracuseStep 1283593 = 962695) B962695
theorem B759335 : Blo 758332 759335 := bstep (se 1 (by rfl) ⟨569501, by rfl⟩ : syracuseStep 759335 = 1139003) B1139003
theorem B759375 : Blo 758332 759375 := bstep (se 1 (by rfl) ⟨569531, by rfl⟩ : syracuseStep 759375 = 1139063) B1139063
theorem B759391 : Blo 758332 759391 := bstep (se 1 (by rfl) ⟨569543, by rfl⟩ : syracuseStep 759391 = 1139087) B1139087
theorem B759419 : Blo 758332 759419 := bstep (se 1 (by rfl) ⟨569564, by rfl⟩ : syracuseStep 759419 = 1139129) B1139129
theorem B1283755 : Blo 758332 1283755 := bstep (se 1 (by rfl) ⟨962816, by rfl⟩ : syracuseStep 1283755 = 1925633) B1925633
theorem B759471 : Blo 758332 759471 := bstep (se 1 (by rfl) ⟨569603, by rfl⟩ : syracuseStep 759471 = 1139207) B1139207
theorem B759495 : Blo 758332 759495 := bstep (se 1 (by rfl) ⟨569621, by rfl⟩ : syracuseStep 759495 = 1139243) B1139243
theorem B759515 : Blo 758332 759515 := bstep (se 1 (by rfl) ⟨569636, by rfl⟩ : syracuseStep 759515 = 1139273) B1139273
theorem B2430749 : Blo 758332 2430749 := bstep (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) B911531
theorem B759591 : Blo 758332 759591 := bstep (se 1 (by rfl) ⟨569693, by rfl⟩ : syracuseStep 759591 = 1139387) B1139387
theorem B759631 : Blo 758332 759631 := bstep (se 1 (by rfl) ⟨569723, by rfl⟩ : syracuseStep 759631 = 1139447) B1139447
theorem B759647 : Blo 758332 759647 := bstep (se 1 (by rfl) ⟨569735, by rfl⟩ : syracuseStep 759647 = 1139471) B1139471
theorem B759675 : Blo 758332 759675 := bstep (se 1 (by rfl) ⟨569756, by rfl⟩ : syracuseStep 759675 = 1139513) B1139513
theorem B759727 : Blo 758332 759727 := bstep (se 1 (by rfl) ⟨569795, by rfl⟩ : syracuseStep 759727 = 1139591) B1139591
theorem B1709999 : Blo 758332 1709999 := bstep (se 1 (by rfl) ⟨1282499, by rfl⟩ : syracuseStep 1709999 = 2564999) B2564999
theorem B2561975 : Blo 758332 2561975 := bstep (se 1 (by rfl) ⟨1921481, by rfl⟩ : syracuseStep 2561975 = 3842963) B3842963
theorem B759751 : Blo 758332 759751 := bstep (se 1 (by rfl) ⟨569813, by rfl⟩ : syracuseStep 759751 = 1139627) B1139627
theorem B759771 : Blo 758332 759771 := bstep (se 1 (by rfl) ⟨569828, by rfl⟩ : syracuseStep 759771 = 1139657) B1139657
theorem B1284059 : Blo 758332 1284059 := bstep (se 1 (by rfl) ⟨963044, by rfl⟩ : syracuseStep 1284059 = 1926089) B1926089
theorem B759847 : Blo 758332 759847 := bstep (se 1 (by rfl) ⟨569885, by rfl⟩ : syracuseStep 759847 = 1139771) B1139771
theorem B7313465 : Blo 758332 7313465 := bstep (se 2 (by rfl) ⟨2742549, by rfl⟩ : syracuseStep 7313465 = 5485099) B5485099
theorem B759887 : Blo 758332 759887 := bstep (se 1 (by rfl) ⟨569915, by rfl⟩ : syracuseStep 759887 = 1139831) B1139831
theorem B759903 : Blo 758332 759903 := bstep (se 1 (by rfl) ⟨569927, by rfl⟩ : syracuseStep 759903 = 1139855) B1139855
theorem B3119219 : Blo 758332 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B759931 : Blo 758332 759931 := bstep (se 1 (by rfl) ⟨569948, by rfl⟩ : syracuseStep 759931 = 1139897) B1139897
theorem B2431147 : Blo 758332 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B1710251 : Blo 758332 1710251 := bstep (se 1 (by rfl) ⟨1282688, by rfl⟩ : syracuseStep 1710251 = 2565377) B2565377
theorem B759983 : Blo 758332 759983 := bstep (se 1 (by rfl) ⟨569987, by rfl⟩ : syracuseStep 759983 = 1139975) B1139975
theorem B760007 : Blo 758332 760007 := bstep (se 1 (by rfl) ⟨570005, by rfl⟩ : syracuseStep 760007 = 1140011) B1140011
theorem B1284295 : Blo 758332 1284295 := bstep (se 1 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 1284295 = 1926443) B1926443
theorem B760027 : Blo 758332 760027 := bstep (se 1 (by rfl) ⟨570020, by rfl⟩ : syracuseStep 760027 = 1140041) B1140041
theorem B1218809 : Blo 758332 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B760103 : Blo 758332 760103 := bstep (se 1 (by rfl) ⟨570077, by rfl⟩ : syracuseStep 760103 = 1140155) B1140155
theorem B760143 : Blo 758332 760143 := bstep (se 1 (by rfl) ⟨570107, by rfl⟩ : syracuseStep 760143 = 1140215) B1140215
theorem B760159 : Blo 758332 760159 := bstep (se 1 (by rfl) ⟨570119, by rfl⟩ : syracuseStep 760159 = 1140239) B1140239
theorem B1284457 : Blo 758332 1284457 := bstep (se 2 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 1284457 = 963343) B963343
theorem B760187 : Blo 758332 760187 := bstep (se 1 (by rfl) ⟨570140, by rfl⟩ : syracuseStep 760187 = 1140281) B1140281
theorem B760239 : Blo 758332 760239 := bstep (se 1 (by rfl) ⟨570179, by rfl⟩ : syracuseStep 760239 = 1140359) B1140359
theorem B760263 : Blo 758332 760263 := bstep (se 1 (by rfl) ⟨570197, by rfl⟩ : syracuseStep 760263 = 1140395) B1140395
theorem B760283 : Blo 758332 760283 := bstep (se 1 (by rfl) ⟨570212, by rfl⟩ : syracuseStep 760283 = 1140425) B1140425
theorem B2562569 : Blo 758332 2562569 := bstep (se 2 (by rfl) ⟨960963, by rfl⟩ : syracuseStep 2562569 = 1921927) B1921927
theorem B1972775 : Blo 758332 1972775 := bstep (se 1 (by rfl) ⟨1479581, by rfl⟩ : syracuseStep 1972775 = 2959163) B2959163
theorem B760359 : Blo 758332 760359 := bstep (se 1 (by rfl) ⟨570269, by rfl⟩ : syracuseStep 760359 = 1140539) B1140539
theorem B760399 : Blo 758332 760399 := bstep (se 1 (by rfl) ⟨570299, by rfl⟩ : syracuseStep 760399 = 1140599) B1140599
theorem B760415 : Blo 758332 760415 := bstep (se 1 (by rfl) ⟨570311, by rfl⟩ : syracuseStep 760415 = 1140623) B1140623
theorem B760443 : Blo 758332 760443 := bstep (se 1 (by rfl) ⟨570332, by rfl⟩ : syracuseStep 760443 = 1140665) B1140665
theorem B2890363 : Blo 758332 2890363 := bstep (se 1 (by rfl) ⟨2167772, by rfl⟩ : syracuseStep 2890363 = 4335545) B4335545
theorem B760495 : Blo 758332 760495 := bstep (se 1 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 760495 = 1140743) B1140743
theorem B1710791 : Blo 758332 1710791 := bstep (se 1 (by rfl) ⟨1283093, by rfl⟩ : syracuseStep 1710791 = 2566187) B2566187
theorem B760519 : Blo 758332 760519 := bstep (se 1 (by rfl) ⟨570389, by rfl⟩ : syracuseStep 760519 = 1140779) B1140779
theorem B760539 : Blo 758332 760539 := bstep (se 1 (by rfl) ⟨570404, by rfl⟩ : syracuseStep 760539 = 1140809) B1140809
theorem B1219321 : Blo 758332 1219321 := bstep (se 2 (by rfl) ⟨457245, by rfl⟩ : syracuseStep 1219321 = 914491) B914491
theorem B760615 : Blo 758332 760615 := bstep (se 1 (by rfl) ⟨570461, by rfl⟩ : syracuseStep 760615 = 1140923) B1140923
theorem B760655 : Blo 758332 760655 := bstep (se 1 (by rfl) ⟨570491, by rfl⟩ : syracuseStep 760655 = 1140983) B1140983
theorem B760671 : Blo 758332 760671 := bstep (se 1 (by rfl) ⟨570503, by rfl⟩ : syracuseStep 760671 = 1141007) B1141007
theorem B1481579 : Blo 758332 1481579 := bstep (se 1 (by rfl) ⟨1111184, by rfl⟩ : syracuseStep 1481579 = 2222369) B2222369
theorem B760699 : Blo 758332 760699 := bstep (se 1 (by rfl) ⟨570524, by rfl⟩ : syracuseStep 760699 = 1141049) B1141049
theorem B760751 : Blo 758332 760751 := bstep (se 1 (by rfl) ⟨570563, by rfl⟩ : syracuseStep 760751 = 1141127) B1141127
theorem B1285051 : Blo 758332 1285051 := bstep (se 1 (by rfl) ⟨963788, by rfl⟩ : syracuseStep 1285051 = 1927577) B1927577
theorem B760775 : Blo 758332 760775 := bstep (se 1 (by rfl) ⟨570581, by rfl⟩ : syracuseStep 760775 = 1141163) B1141163
theorem B760795 : Blo 758332 760795 := bstep (se 1 (by rfl) ⟨570596, by rfl⟩ : syracuseStep 760795 = 1141193) B1141193
theorem B760871 : Blo 758332 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B1285159 : Blo 758332 1285159 := bstep (se 1 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 1285159 = 1927739) B1927739
theorem B760911 : Blo 758332 760911 := bstep (se 1 (by rfl) ⟨570683, by rfl⟩ : syracuseStep 760911 = 1141367) B1141367
theorem B760927 : Blo 758332 760927 := bstep (se 1 (by rfl) ⟨570695, by rfl⟩ : syracuseStep 760927 = 1141391) B1141391
theorem B760955 : Blo 758332 760955 := bstep (se 1 (by rfl) ⟨570716, by rfl⟩ : syracuseStep 760955 = 1141433) B1141433
theorem B761007 : Blo 758332 761007 := bstep (se 1 (by rfl) ⟨570755, by rfl⟩ : syracuseStep 761007 = 1141511) B1141511
theorem B761031 : Blo 758332 761031 := bstep (se 1 (by rfl) ⟨570773, by rfl⟩ : syracuseStep 761031 = 1141547) B1141547
theorem B761051 : Blo 758332 761051 := bstep (se 1 (by rfl) ⟨570788, by rfl⟩ : syracuseStep 761051 = 1141577) B1141577
theorem B761127 : Blo 758332 761127 := bstep (se 1 (by rfl) ⟨570845, by rfl⟩ : syracuseStep 761127 = 1141691) B1141691
theorem B761167 : Blo 758332 761167 := bstep (se 1 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 761167 = 1141751) B1141751
theorem B761183 : Blo 758332 761183 := bstep (se 1 (by rfl) ⟨570887, by rfl⟩ : syracuseStep 761183 = 1141775) B1141775
theorem B2563433 : Blo 758332 2563433 := bstep (se 2 (by rfl) ⟨961287, by rfl⟩ : syracuseStep 2563433 = 1922575) B1922575
theorem B1285483 : Blo 758332 1285483 := bstep (se 1 (by rfl) ⟨964112, by rfl⟩ : syracuseStep 1285483 = 1928225) B1928225
theorem B761211 : Blo 758332 761211 := bstep (se 1 (by rfl) ⟨570908, by rfl⟩ : syracuseStep 761211 = 1141817) B1141817
theorem B761263 : Blo 758332 761263 := bstep (se 1 (by rfl) ⟨570947, by rfl⟩ : syracuseStep 761263 = 1141895) B1141895
theorem B761287 : Blo 758332 761287 := bstep (se 1 (by rfl) ⟨570965, by rfl⟩ : syracuseStep 761287 = 1141931) B1141931
theorem B761307 : Blo 758332 761307 := bstep (se 1 (by rfl) ⟨570980, by rfl⟩ : syracuseStep 761307 = 1141961) B1141961
theorem B1711655 : Blo 758332 1711655 := bstep (se 1 (by rfl) ⟨1283741, by rfl⟩ : syracuseStep 1711655 = 2567483) B2567483
theorem B761383 : Blo 758332 761383 := bstep (se 1 (by rfl) ⟨571037, by rfl⟩ : syracuseStep 761383 = 1142075) B1142075
theorem B761423 : Blo 758332 761423 := bstep (se 1 (by rfl) ⟨571067, by rfl⟩ : syracuseStep 761423 = 1142135) B1142135
theorem B761439 : Blo 758332 761439 := bstep (se 1 (by rfl) ⟨571079, by rfl⟩ : syracuseStep 761439 = 1142159) B1142159
theorem B761467 : Blo 758332 761467 := bstep (se 1 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 761467 = 1142201) B1142201
theorem B761519 : Blo 758332 761519 := bstep (se 1 (by rfl) ⟨571139, by rfl⟩ : syracuseStep 761519 = 1142279) B1142279
theorem B761543 : Blo 758332 761543 := bstep (se 1 (by rfl) ⟨571157, by rfl⟩ : syracuseStep 761543 = 1142315) B1142315
theorem B761563 : Blo 758332 761563 := bstep (se 1 (by rfl) ⟨571172, by rfl⟩ : syracuseStep 761563 = 1142345) B1142345
theorem B5775137 : Blo 758332 5775137 := bstep (se 2 (by rfl) ⟨2165676, by rfl⟩ : syracuseStep 5775137 = 4331353) B4331353
theorem B761639 : Blo 758332 761639 := bstep (se 1 (by rfl) ⟨571229, by rfl⟩ : syracuseStep 761639 = 1142459) B1142459
theorem B761679 : Blo 758332 761679 := bstep (se 1 (by rfl) ⟨571259, by rfl⟩ : syracuseStep 761679 = 1142519) B1142519
theorem B761695 : Blo 758332 761695 := bstep (se 1 (by rfl) ⟨571271, by rfl⟩ : syracuseStep 761695 = 1142543) B1142543
theorem B1711979 : Blo 758332 1711979 := bstep (se 1 (by rfl) ⟨1283984, by rfl⟩ : syracuseStep 1711979 = 2567969) B2567969
theorem B2891639 : Blo 758332 2891639 := bstep (se 1 (by rfl) ⟨2168729, by rfl⟩ : syracuseStep 2891639 = 4337459) B4337459
theorem B761723 : Blo 758332 761723 := bstep (se 1 (by rfl) ⟨571292, by rfl⟩ : syracuseStep 761723 = 1142585) B1142585
theorem B1712033 : Blo 758332 1712033 := bstep (se 2 (by rfl) ⟨642012, by rfl⟩ : syracuseStep 1712033 = 1284025) B1284025
theorem B761775 : Blo 758332 761775 := bstep (se 1 (by rfl) ⟨571331, by rfl⟩ : syracuseStep 761775 = 1142663) B1142663
theorem B2564027 : Blo 758332 2564027 := bstep (se 1 (by rfl) ⟨1923020, by rfl⟩ : syracuseStep 2564027 = 3846041) B3846041
theorem B761799 : Blo 758332 761799 := bstep (se 1 (by rfl) ⟨571349, by rfl⟩ : syracuseStep 761799 = 1142699) B1142699
theorem B761819 : Blo 758332 761819 := bstep (se 1 (by rfl) ⟨571364, by rfl⟩ : syracuseStep 761819 = 1142729) B1142729
theorem B27795473 : Blo 758332 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B761895 : Blo 758332 761895 := bstep (se 1 (by rfl) ⟨571421, by rfl⟩ : syracuseStep 761895 = 1142843) B1142843
theorem B761935 : Blo 758332 761935 := bstep (se 1 (by rfl) ⟨571451, by rfl⟩ : syracuseStep 761935 = 1142903) B1142903
theorem B761951 : Blo 758332 761951 := bstep (se 1 (by rfl) ⟨571463, by rfl⟩ : syracuseStep 761951 = 1142927) B1142927
theorem B761979 : Blo 758332 761979 := bstep (se 1 (by rfl) ⟨571484, by rfl⟩ : syracuseStep 761979 = 1142969) B1142969
theorem B762031 : Blo 758332 762031 := bstep (se 1 (by rfl) ⟨571523, by rfl⟩ : syracuseStep 762031 = 1143047) B1143047
theorem B762055 : Blo 758332 762055 := bstep (se 1 (by rfl) ⟨571541, by rfl⟩ : syracuseStep 762055 = 1143083) B1143083
theorem B762075 : Blo 758332 762075 := bstep (se 1 (by rfl) ⟨571556, by rfl⟩ : syracuseStep 762075 = 1143113) B1143113
theorem B1712375 : Blo 758332 1712375 := bstep (se 1 (by rfl) ⟨1284281, by rfl⟩ : syracuseStep 1712375 = 2568563) B2568563
theorem B3842315 : Blo 758332 3842315 := bstep (se 1 (by rfl) ⟨2881736, by rfl⟩ : syracuseStep 3842315 = 5763473) B5763473
theorem B762151 : Blo 758332 762151 := bstep (se 1 (by rfl) ⟨571613, by rfl⟩ : syracuseStep 762151 = 1143227) B1143227
theorem B762191 : Blo 758332 762191 := bstep (se 1 (by rfl) ⟨571643, by rfl⟩ : syracuseStep 762191 = 1143287) B1143287
theorem B762207 : Blo 758332 762207 := bstep (se 1 (by rfl) ⟨571655, by rfl⟩ : syracuseStep 762207 = 1143311) B1143311
theorem B762235 : Blo 758332 762235 := bstep (se 1 (by rfl) ⟨571676, by rfl⟩ : syracuseStep 762235 = 1143353) B1143353
theorem B1221007 : Blo 758332 1221007 := bstep (se 1 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 1221007 = 1831511) B1831511
theorem B762287 : Blo 758332 762287 := bstep (se 1 (by rfl) ⟨571715, by rfl⟩ : syracuseStep 762287 = 1143431) B1143431
theorem B762311 : Blo 758332 762311 := bstep (se 1 (by rfl) ⟨571733, by rfl⟩ : syracuseStep 762311 = 1143467) B1143467
theorem B762331 : Blo 758332 762331 := bstep (se 1 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 762331 = 1143497) B1143497
theorem B2433671 : Blo 758332 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B19473047 : Blo 758332 19473047 := bstep (se 1 (by rfl) ⟨14604785, by rfl⟩ : syracuseStep 19473047 = 29209571) B29209571
theorem B2433721 : Blo 758332 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B2892611 : Blo 758332 2892611 := bstep (se 1 (by rfl) ⟨2169458, by rfl⟩ : syracuseStep 2892611 = 4338917) B4338917
theorem B1712969 : Blo 758332 1712969 := bstep (se 2 (by rfl) ⟨642363, by rfl⟩ : syracuseStep 1712969 = 1284727) B1284727
theorem B4334795 : Blo 758332 4334795 := bstep (se 1 (by rfl) ⟨3251096, by rfl⟩ : syracuseStep 4334795 = 6502193) B6502193
theorem B2893067 : Blo 758332 2893067 := bstep (se 1 (by rfl) ⟨2169800, by rfl⟩ : syracuseStep 2893067 = 4339601) B4339601
theorem B2139497 : Blo 758332 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B5547437 : Blo 758332 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B1713761 : Blo 758332 1713761 := bstep (se 2 (by rfl) ⟨642660, by rfl⟩ : syracuseStep 1713761 = 1285321) B1285321
theorem B2565755 : Blo 758332 2565755 := bstep (se 1 (by rfl) ⟨1924316, by rfl⟩ : syracuseStep 2565755 = 3848633) B3848633
theorem B4335227 : Blo 758332 4335227 := bstep (se 1 (by rfl) ⟨3251420, by rfl⟩ : syracuseStep 4335227 = 6502841) B6502841
theorem B13837969 : Blo 758332 13837969 := bstep (se 2 (by rfl) ⟨5189238, by rfl⟩ : syracuseStep 13837969 = 10378477) B10378477
theorem B3843773 : Blo 758332 3843773 := bstep (se 3 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 3843773 = 1441415) B1441415
theorem B13838039 : Blo 758332 13838039 := bstep (se 1 (by rfl) ⟨10378529, by rfl⟩ : syracuseStep 13838039 = 20757059) B20757059
theorem B2565917 : Blo 758332 2565917 := bstep (se 3 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 2565917 = 962219) B962219
theorem B3843935 : Blo 758332 3843935 := bstep (se 1 (by rfl) ⟨2882951, by rfl⟩ : syracuseStep 3843935 = 5765903) B5765903
theorem B3647393 : Blo 758332 3647393 := bstep (se 2 (by rfl) ⟨1367772, by rfl⟩ : syracuseStep 3647393 = 2735545) B2735545
theorem B1714103 : Blo 758332 1714103 := bstep (se 1 (by rfl) ⟨1285577, by rfl⟩ : syracuseStep 1714103 = 2571155) B2571155
theorem B2893751 : Blo 758332 2893751 := bstep (se 1 (by rfl) ⟨2170313, by rfl⟩ : syracuseStep 2893751 = 4340627) B4340627
theorem B12986405 : Blo 758332 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B2107471 : Blo 758332 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B2435453 : Blo 758332 2435453 := bstep (se 3 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 2435453 = 913295) B913295
theorem B4336001 : Blo 758332 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B2566619 : Blo 758332 2566619 := bstep (se 1 (by rfl) ⟨1924964, by rfl⟩ : syracuseStep 2566619 = 3849929) B3849929
theorem B1714697 : Blo 758332 1714697 := bstep (se 2 (by rfl) ⟨643011, by rfl⟩ : syracuseStep 1714697 = 1286023) B1286023
theorem B1715039 : Blo 758332 1715039 := bstep (se 1 (by rfl) ⟨1286279, by rfl⟩ : syracuseStep 1715039 = 2572559) B2572559
theorem B6499217 : Blo 758332 6499217 := bstep (se 2 (by rfl) ⟨2437206, by rfl⟩ : syracuseStep 6499217 = 4874413) B4874413
theorem B15641527 : Blo 758332 15641527 := bstep (se 1 (by rfl) ⟨11731145, by rfl⟩ : syracuseStep 15641527 = 23462291) B23462291
theorem B1715219 : Blo 758332 1715219 := bstep (se 1 (by rfl) ⟨1286414, by rfl⟩ : syracuseStep 1715219 = 2572829) B2572829
theorem B2567321 : Blo 758332 2567321 := bstep (se 2 (by rfl) ⟨962745, by rfl⟩ : syracuseStep 2567321 = 1925491) B1925491
theorem B2436439 : Blo 758332 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B4926845 : Blo 758332 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B1486255 : Blo 758332 1486255 := bstep (se 1 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 1486255 = 2229383) B2229383
theorem B2436797 : Blo 758332 2436797 := bstep (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) B913799
theorem B4861883 : Blo 758332 4861883 := bstep (se 1 (by rfl) ⟨3646412, by rfl⟩ : syracuseStep 4861883 = 7292825) B7292825
theorem B962599 : Blo 758332 962599 := bstep (se 1 (by rfl) ⟨721949, by rfl⟩ : syracuseStep 962599 = 1443899) B1443899
theorem B8335523 : Blo 758332 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B3649853 : Blo 758332 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B2568509 : Blo 758332 2568509 := bstep (se 3 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 2568509 = 963191) B963191
theorem B962923 : Blo 758332 962923 := bstep (se 1 (by rfl) ⟨722192, by rfl⟩ : syracuseStep 962923 = 1444385) B1444385
theorem B3846689 : Blo 758332 3846689 := bstep (se 2 (by rfl) ⟨1442508, by rfl⟩ : syracuseStep 3846689 = 2885017) B2885017
theorem B2437771 : Blo 758332 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B4338461 : Blo 758332 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B1946551 : Blo 758332 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B2602063 : Blo 758332 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B74036375 : Blo 758332 74036375 := bstep (se 1 (by rfl) ⟨55527281, by rfl⟩ : syracuseStep 74036375 = 111054563) B111054563
theorem B2569373 : Blo 758332 2569373 := bstep (se 3 (by rfl) ⟨481757, by rfl⟩ : syracuseStep 2569373 = 963515) B963515
theorem B2733323 : Blo 758332 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B2471293 : Blo 758332 2471293 := bstep (se 3 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 2471293 = 926735) B926735
theorem B964219 : Blo 758332 964219 := bstep (se 1 (by rfl) ⟨723164, by rfl⟩ : syracuseStep 964219 = 1446329) B1446329
theorem B2569913 : Blo 758332 2569913 := bstep (se 2 (by rfl) ⟨963717, by rfl⟩ : syracuseStep 2569913 = 1927435) B1927435
theorem B2307799 : Blo 758332 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B2963267 : Blo 758332 2963267 := bstep (se 1 (by rfl) ⟨2222450, by rfl⟩ : syracuseStep 2963267 = 4444901) B4444901
theorem B2570507 : Blo 758332 2570507 := bstep (se 1 (by rfl) ⟨1927880, by rfl⟩ : syracuseStep 2570507 = 3855761) B3855761
theorem B2439553 : Blo 758332 2439553 := bstep (se 2 (by rfl) ⟨914832, by rfl⟩ : syracuseStep 2439553 = 1829665) B1829665
theorem B2439667 : Blo 758332 2439667 := bstep (se 1 (by rfl) ⟨1829750, by rfl⟩ : syracuseStep 2439667 = 3659501) B3659501
theorem B2570777 : Blo 758332 2570777 := bstep (se 2 (by rfl) ⟨964041, by rfl⟩ : syracuseStep 2570777 = 1928083) B1928083
theorem B4111211 : Blo 758332 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B21085109 : Blo 758332 21085109 := bstep (se 5 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 21085109 = 1976729) B1976729
theorem B5488073 : Blo 758332 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B3849767 : Blo 758332 3849767 := bstep (se 1 (by rfl) ⟨2887325, by rfl⟩ : syracuseStep 3849767 = 5774651) B5774651
theorem B2571911 : Blo 758332 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B2571965 : Blo 758332 2571965 := bstep (se 3 (by rfl) ⟨482243, by rfl⟩ : syracuseStep 2571965 = 964487) B964487
theorem B2572127 : Blo 758332 2572127 := bstep (se 1 (by rfl) ⟨1929095, by rfl⟩ : syracuseStep 2572127 = 3858191) B3858191
theorem B2572289 : Blo 758332 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B4112441 : Blo 758332 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B770143 : Blo 758332 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B1622567 : Blo 758332 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B2933371 : Blo 758332 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B1622857 : Blo 758332 1622857 := bstep (se 2 (by rfl) ⟨608571, by rfl⟩ : syracuseStep 1622857 = 1217143) B1217143
theorem B1622891 : Blo 758332 1622891 := bstep (se 1 (by rfl) ⟨1217168, by rfl⟩ : syracuseStep 1622891 = 2434337) B2434337
theorem B1852321 : Blo 758332 1852321 := bstep (se 2 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 1852321 = 1389241) B1389241
theorem B3851873 : Blo 758332 3851873 := bstep (se 2 (by rfl) ⟨1444452, by rfl⟩ : syracuseStep 3851873 = 2888905) B2888905
theorem B5785829 : Blo 758332 5785829 := bstep (se 4 (by rfl) ⟨542421, by rfl⟩ : syracuseStep 5785829 = 1084843) B1084843
theorem B1624463 : Blo 758332 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B5491097 : Blo 758332 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B3460097 : Blo 758332 3460097 := bstep (se 2 (by rfl) ⟨1297536, by rfl⟩ : syracuseStep 3460097 = 2595073) B2595073
theorem B3853331 : Blo 758332 3853331 := bstep (se 1 (by rfl) ⟨2889998, by rfl⟩ : syracuseStep 3853331 = 5779997) B5779997
theorem B5491763 : Blo 758332 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B5491907 : Blo 758332 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B2051723 : Blo 758332 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B3460823 : Blo 758332 3460823 := bstep (se 1 (by rfl) ⟨2595617, by rfl⟩ : syracuseStep 3460823 = 5191235) B5191235
theorem B4869881 : Blo 758332 4869881 := bstep (se 2 (by rfl) ⟨1826205, by rfl⟩ : syracuseStep 4869881 = 3652411) B3652411
theorem B3657581 : Blo 758332 3657581 := bstep (se 3 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 3657581 = 1371593) B1371593
theorem B10407865 : Blo 758332 10407865 := bstep (se 2 (by rfl) ⟨3902949, by rfl⟩ : syracuseStep 10407865 = 7805899) B7805899
theorem B1920955 : Blo 758332 1920955 := bstep (se 1 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 1920955 = 2881433) B2881433
theorem B3559355 : Blo 758332 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B2315195 : Blo 758332 2315195 := bstep (se 1 (by rfl) ⟨1736396, by rfl⟩ : syracuseStep 2315195 = 3472793) B3472793
theorem B4871339 : Blo 758332 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B35149463 : Blo 758332 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B2315965 : Blo 758332 2315965 := bstep (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) B868487
theorem B2741975 : Blo 758332 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B11130583 : Blo 758332 11130583 := bstep (se 1 (by rfl) ⟨8347937, by rfl⟩ : syracuseStep 11130583 = 16695875) B16695875
theorem B1824619 : Blo 758332 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B3856247 : Blo 758332 3856247 := bstep (se 1 (by rfl) ⟨2892185, by rfl⟩ : syracuseStep 3856247 = 5784371) B5784371
theorem B2742191 : Blo 758332 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B5494787 : Blo 758332 5494787 := bstep (se 1 (by rfl) ⟨4121090, by rfl⟩ : syracuseStep 5494787 = 8242181) B8242181
theorem B7788581 : Blo 758332 7788581 := bstep (se 4 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 7788581 = 1460359) B1460359
theorem B8673641 : Blo 758332 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B2742653 : Blo 758332 2742653 := bstep (se 3 (by rfl) ⟨514247, by rfl⟩ : syracuseStep 2742653 = 1028495) B1028495
theorem B1923547 : Blo 758332 1923547 := bstep (se 1 (by rfl) ⟨1442660, by rfl⟩ : syracuseStep 1923547 = 2885321) B2885321
theorem B1366777 : Blo 758332 1366777 := bstep (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) B1025083
theorem B1137503 : Blo 758332 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B1137515 : Blo 758332 1137515 := bstep (se 1 (by rfl) ⟨853136, by rfl⟩ : syracuseStep 1137515 = 1706273) B1706273
theorem B7297937 : Blo 758332 7297937 := bstep (se 2 (by rfl) ⟨2736726, by rfl⟩ : syracuseStep 7297937 = 5473453) B5473453
theorem B6511589 : Blo 758332 6511589 := bstep (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) B1220923
theorem B1825849 : Blo 758332 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B1137743 : Blo 758332 1137743 := bstep (se 1 (by rfl) ⟨853307, by rfl⟩ : syracuseStep 1137743 = 1706615) B1706615
theorem B6151247 : Blo 758332 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B1924175 : Blo 758332 1924175 := bstep (se 1 (by rfl) ⟨1443131, by rfl⟩ : syracuseStep 1924175 = 2886263) B2886263
theorem B1137863 : Blo 758332 1137863 := bstep (se 1 (by rfl) ⟨853397, by rfl⟩ : syracuseStep 1137863 = 1706795) B1706795
theorem B810335 : Blo 758332 810335 := bstep (se 1 (by rfl) ⟨607751, by rfl⟩ : syracuseStep 810335 = 1215503) B1215503
theorem B1138025 : Blo 758332 1138025 := bstep (se 2 (by rfl) ⟨426759, by rfl⟩ : syracuseStep 1138025 = 853519) B853519
theorem B2088335 : Blo 758332 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B1138103 : Blo 758332 1138103 := bstep (se 1 (by rfl) ⟨853577, by rfl⟩ : syracuseStep 1138103 = 1707155) B1707155
theorem B1138139 : Blo 758332 1138139 := bstep (se 1 (by rfl) ⟨853604, by rfl⟩ : syracuseStep 1138139 = 1707209) B1707209
theorem B1924823 : Blo 758332 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B1367903 : Blo 758332 1367903 := bstep (se 1 (by rfl) ⟨1025927, by rfl⟩ : syracuseStep 1367903 = 2051855) B2051855
theorem B1138607 : Blo 758332 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B1138697 : Blo 758332 1138697 := bstep (se 2 (by rfl) ⟨427011, by rfl⟩ : syracuseStep 1138697 = 854023) B854023
theorem B31252493 : Blo 758332 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B1138727 : Blo 758332 1138727 := bstep (se 1 (by rfl) ⟨854045, by rfl⟩ : syracuseStep 1138727 = 1708091) B1708091
theorem B1138811 : Blo 758332 1138811 := bstep (se 1 (by rfl) ⟨854108, by rfl⟩ : syracuseStep 1138811 = 1708217) B1708217
theorem B15622307 : Blo 758332 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B1138937 : Blo 758332 1138937 := bstep (se 2 (by rfl) ⟨427101, by rfl⟩ : syracuseStep 1138937 = 854203) B854203
theorem B4120919 : Blo 758332 4120919 := bstep (se 1 (by rfl) ⟨3090689, by rfl⟩ : syracuseStep 4120919 = 6181379) B6181379
theorem B1139039 : Blo 758332 1139039 := bstep (se 1 (by rfl) ⟨854279, by rfl⟩ : syracuseStep 1139039 = 1708559) B1708559
theorem B1139051 : Blo 758332 1139051 := bstep (se 1 (by rfl) ⟨854288, by rfl⟩ : syracuseStep 1139051 = 1708577) B1708577
theorem B1139279 : Blo 758332 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B1139399 : Blo 758332 1139399 := bstep (se 1 (by rfl) ⟨854549, by rfl⟩ : syracuseStep 1139399 = 1709099) B1709099
theorem B1139561 : Blo 758332 1139561 := bstep (se 2 (by rfl) ⟨427335, by rfl⟩ : syracuseStep 1139561 = 854671) B854671
theorem B1139639 : Blo 758332 1139639 := bstep (se 1 (by rfl) ⟨854729, by rfl⟩ : syracuseStep 1139639 = 1709459) B1709459
theorem B1139675 : Blo 758332 1139675 := bstep (se 1 (by rfl) ⟨854756, by rfl⟩ : syracuseStep 1139675 = 1709513) B1709513
theorem B1140143 : Blo 758332 1140143 := bstep (se 1 (by rfl) ⟨855107, by rfl⟩ : syracuseStep 1140143 = 1710215) B1710215
theorem B1140233 : Blo 758332 1140233 := bstep (se 2 (by rfl) ⟨427587, by rfl⟩ : syracuseStep 1140233 = 855175) B855175
theorem B8775179 : Blo 758332 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B1140263 : Blo 758332 1140263 := bstep (se 1 (by rfl) ⟨855197, by rfl⟩ : syracuseStep 1140263 = 1710395) B1710395
theorem B2745895 : Blo 758332 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B1369723 : Blo 758332 1369723 := bstep (se 1 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 1369723 = 2054585) B2054585
theorem B1140347 : Blo 758332 1140347 := bstep (se 1 (by rfl) ⟨855260, by rfl⟩ : syracuseStep 1140347 = 1710521) B1710521
theorem B1140473 : Blo 758332 1140473 := bstep (se 2 (by rfl) ⟨427677, by rfl⟩ : syracuseStep 1140473 = 855355) B855355
theorem B166750001 : Blo 758332 166750001 := bstep (se 2 (by rfl) ⟨62531250, by rfl⟩ : syracuseStep 166750001 = 125062501) B125062501
theorem B1140575 : Blo 758332 1140575 := bstep (se 1 (by rfl) ⟨855431, by rfl⟩ : syracuseStep 1140575 = 1710863) B1710863
theorem B1140587 : Blo 758332 1140587 := bstep (se 1 (by rfl) ⟨855440, by rfl⟩ : syracuseStep 1140587 = 1710881) B1710881
theorem B1140815 : Blo 758332 1140815 := bstep (se 1 (by rfl) ⟨855611, by rfl⟩ : syracuseStep 1140815 = 1711223) B1711223
theorem B1370209 : Blo 758332 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B1140935 : Blo 758332 1140935 := bstep (se 1 (by rfl) ⟨855701, by rfl⟩ : syracuseStep 1140935 = 1711403) B1711403
theorem B1927415 : Blo 758332 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B1141097 : Blo 758332 1141097 := bstep (se 2 (by rfl) ⟨427911, by rfl⟩ : syracuseStep 1141097 = 855823) B855823
theorem B1141175 : Blo 758332 1141175 := bstep (se 1 (by rfl) ⟨855881, by rfl⟩ : syracuseStep 1141175 = 1711763) B1711763
theorem B10938827 : Blo 758332 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B1141211 : Blo 758332 1141211 := bstep (se 1 (by rfl) ⟨855908, by rfl⟩ : syracuseStep 1141211 = 1711817) B1711817
theorem B912223 : Blo 758332 912223 := bstep (se 1 (by rfl) ⟨684167, by rfl⟩ : syracuseStep 912223 = 1368335) B1368335
theorem B1141679 : Blo 758332 1141679 := bstep (se 1 (by rfl) ⟨856259, by rfl⟩ : syracuseStep 1141679 = 1712519) B1712519
theorem B2780087 : Blo 758332 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B1141769 : Blo 758332 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B1141799 : Blo 758332 1141799 := bstep (se 1 (by rfl) ⟨856349, by rfl⟩ : syracuseStep 1141799 = 1712699) B1712699
theorem B1141883 : Blo 758332 1141883 := bstep (se 1 (by rfl) ⟨856412, by rfl⟩ : syracuseStep 1141883 = 1712825) B1712825
theorem B1830059 : Blo 758332 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B1142009 : Blo 758332 1142009 := bstep (se 2 (by rfl) ⟨428253, by rfl⟩ : syracuseStep 1142009 = 856507) B856507
theorem B1142111 : Blo 758332 1142111 := bstep (se 1 (by rfl) ⟨856583, by rfl⟩ : syracuseStep 1142111 = 1713167) B1713167
theorem B1142123 : Blo 758332 1142123 := bstep (se 1 (by rfl) ⟨856592, by rfl⟩ : syracuseStep 1142123 = 1713185) B1713185
theorem B1142351 : Blo 758332 1142351 := bstep (se 1 (by rfl) ⟨856763, by rfl⟩ : syracuseStep 1142351 = 1713527) B1713527
theorem B1928843 : Blo 758332 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B1142471 : Blo 758332 1142471 := bstep (se 1 (by rfl) ⟨856853, by rfl⟩ : syracuseStep 1142471 = 1713707) B1713707
theorem B14839517 : Blo 758332 14839517 := bstep (se 3 (by rfl) ⟨2782409, by rfl⟩ : syracuseStep 14839517 = 5564819) B5564819
theorem B6156013 : Blo 758332 6156013 := bstep (se 3 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 6156013 = 2308505) B2308505
theorem B1929055 : Blo 758332 1929055 := bstep (se 1 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 1929055 = 2893583) B2893583
theorem B1142633 : Blo 758332 1142633 := bstep (se 2 (by rfl) ⟨428487, by rfl⟩ : syracuseStep 1142633 = 856975) B856975
theorem B1142711 : Blo 758332 1142711 := bstep (se 1 (by rfl) ⟨857033, by rfl⟩ : syracuseStep 1142711 = 1714067) B1714067
theorem B1142747 : Blo 758332 1142747 := bstep (se 1 (by rfl) ⟨857060, by rfl⟩ : syracuseStep 1142747 = 1714121) B1714121
theorem B2879489 : Blo 758332 2879489 := bstep (se 2 (by rfl) ⟨1079808, by rfl⟩ : syracuseStep 2879489 = 2159617) B2159617
theorem B6582349 : Blo 758332 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B7303283 : Blo 758332 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B1143215 : Blo 758332 1143215 := bstep (se 1 (by rfl) ⟨857411, by rfl⟩ : syracuseStep 1143215 = 1714823) B1714823
theorem B913847 : Blo 758332 913847 := bstep (se 1 (by rfl) ⟨685385, by rfl⟩ : syracuseStep 913847 = 1370771) B1370771
theorem B2879945 : Blo 758332 2879945 := bstep (se 2 (by rfl) ⟨1079979, by rfl⟩ : syracuseStep 2879945 = 2159959) B2159959
theorem B1143305 : Blo 758332 1143305 := bstep (se 2 (by rfl) ⟨428739, by rfl⟩ : syracuseStep 1143305 = 857479) B857479
theorem B1143335 : Blo 758332 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B1143419 : Blo 758332 1143419 := bstep (se 1 (by rfl) ⟨857564, by rfl⟩ : syracuseStep 1143419 = 1715129) B1715129
theorem B7729937 : Blo 758332 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B5567305 : Blo 758332 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B2880431 : Blo 758332 2880431 := bstep (se 1 (by rfl) ⟨2160323, by rfl⟩ : syracuseStep 2880431 = 4320647) B4320647
theorem B4879439 : Blo 758332 4879439 := bstep (se 1 (by rfl) ⟨3659579, by rfl⟩ : syracuseStep 4879439 = 7319159) B7319159
theorem B9729143 : Blo 758332 9729143 := bstep (se 1 (by rfl) ⟨7296857, by rfl⟩ : syracuseStep 9729143 = 14593715) B14593715
theorem B3077519 : Blo 758332 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B5764931 : Blo 758332 5764931 := bstep (se 1 (by rfl) ⟨4323698, by rfl⟩ : syracuseStep 5764931 = 8647397) B8647397
theorem B1439707 : Blo 758332 1439707 := bstep (se 1 (by rfl) ⟨1079780, by rfl⟩ : syracuseStep 1439707 = 2159561) B2159561
theorem B2881615 : Blo 758332 2881615 := bstep (se 1 (by rfl) ⟨2161211, by rfl⟩ : syracuseStep 2881615 = 4322423) B4322423
theorem B2882087 : Blo 758332 2882087 := bstep (se 1 (by rfl) ⟨2161565, by rfl⟩ : syracuseStep 2882087 = 4323131) B4323131
theorem B14777423 : Blo 758332 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B4750811 : Blo 758332 4750811 := bstep (se 1 (by rfl) ⟨3563108, by rfl⟩ : syracuseStep 4750811 = 7126217) B7126217
theorem B2883059 : Blo 758332 2883059 := bstep (se 1 (by rfl) ⟨2162294, by rfl⟩ : syracuseStep 2883059 = 4324589) B4324589
theorem B5471783 : Blo 758332 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B14614627 : Blo 758332 14614627 := bstep (se 1 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 14614627 = 21921941) B21921941
theorem B1081711 : Blo 758332 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B1081927 : Blo 758332 1081927 := bstep (se 1 (by rfl) ⟨811445, by rfl⟩ : syracuseStep 1081927 = 1622891) B1622891
theorem B2884319 : Blo 758332 2884319 := bstep (se 1 (by rfl) ⟨2163239, by rfl⟩ : syracuseStep 2884319 = 4326479) B4326479
theorem B3244961 : Blo 758332 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B2163809 : Blo 758332 2163809 := bstep (se 2 (by rfl) ⟨811428, by rfl⟩ : syracuseStep 2163809 = 1622857) B1622857
theorem B853339 : Blo 758332 853339 := bstep (se 1 (by rfl) ⟨640004, by rfl⟩ : syracuseStep 853339 = 1280009) B1280009
theorem B32867693 : Blo 758332 32867693 := bstep (se 3 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 32867693 = 12325385) B12325385
theorem B2885003 : Blo 758332 2885003 := bstep (se 1 (by rfl) ⟨2163752, by rfl⟩ : syracuseStep 2885003 = 4327505) B4327505
theorem B853447 : Blo 758332 853447 := bstep (se 1 (by rfl) ⟨640085, by rfl⟩ : syracuseStep 853447 = 1280171) B1280171
theorem B1082975 : Blo 758332 1082975 := bstep (se 1 (by rfl) ⟨812231, by rfl⟩ : syracuseStep 1082975 = 1624463) B1624463
theorem B853807 : Blo 758332 853807 := bstep (se 1 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 853807 = 1280711) B1280711
theorem B853915 : Blo 758332 853915 := bstep (se 1 (by rfl) ⟨640436, by rfl⟩ : syracuseStep 853915 = 1280873) B1280873
theorem B18450625 : Blo 758332 18450625 := bstep (se 2 (by rfl) ⟨6918984, by rfl⟩ : syracuseStep 18450625 = 13837969) B13837969
theorem B854311 : Blo 758332 854311 := bstep (se 1 (by rfl) ⟨640733, by rfl⟩ : syracuseStep 854311 = 1281467) B1281467
theorem B854383 : Blo 758332 854383 := bstep (se 1 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 854383 = 1281575) B1281575
theorem B3246587 : Blo 758332 3246587 := bstep (se 1 (by rfl) ⟨2434940, by rfl⟩ : syracuseStep 3246587 = 4869881) B4869881
theorem B854599 : Blo 758332 854599 := bstep (se 1 (by rfl) ⟨640949, by rfl⟩ : syracuseStep 854599 = 1281899) B1281899
theorem B1706831 : Blo 758332 1706831 := bstep (se 1 (by rfl) ⟨1280123, by rfl⟩ : syracuseStep 1706831 = 2560247) B2560247
theorem B1707047 : Blo 758332 1707047 := bstep (se 1 (by rfl) ⟨1280285, by rfl⟩ : syracuseStep 1707047 = 2560571) B2560571
theorem B2886779 : Blo 758332 2886779 := bstep (se 1 (by rfl) ⟨2165084, by rfl⟩ : syracuseStep 2886779 = 4330169) B4330169
theorem B1707227 : Blo 758332 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B1543463 : Blo 758332 1543463 := bstep (se 1 (by rfl) ⟨1157597, by rfl⟩ : syracuseStep 1543463 = 2315195) B2315195
theorem B1707425 : Blo 758332 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B855463 : Blo 758332 855463 := bstep (se 1 (by rfl) ⟨641597, by rfl⟩ : syracuseStep 855463 = 1283195) B1283195
theorem B3247559 : Blo 758332 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B23432975 : Blo 758332 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B1216297 : Blo 758332 1216297 := bstep (se 2 (by rfl) ⟨456111, by rfl⟩ : syracuseStep 1216297 = 912223) B912223
theorem B1707983 : Blo 758332 1707983 := bstep (se 1 (by rfl) ⟨1280987, by rfl⟩ : syracuseStep 1707983 = 2561975) B2561975
theorem B856039 : Blo 758332 856039 := bstep (se 1 (by rfl) ⟨642029, by rfl⟩ : syracuseStep 856039 = 1284059) B1284059
theorem B1708361 : Blo 758332 1708361 := bstep (se 2 (by rfl) ⟨640635, by rfl⟩ : syracuseStep 1708361 = 1281271) B1281271
theorem B1708379 : Blo 758332 1708379 := bstep (se 1 (by rfl) ⟨1281284, by rfl⟩ : syracuseStep 1708379 = 2562569) B2562569
theorem B1315183 : Blo 758332 1315183 := bstep (se 1 (by rfl) ⟨986387, by rfl⟩ : syracuseStep 1315183 = 1972775) B1972775
theorem B3248585 : Blo 758332 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B758335 : Blo 758332 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B758343 : Blo 758332 758343 := bstep (se 1 (by rfl) ⟨568757, by rfl⟩ : syracuseStep 758343 = 1137515) B1137515
theorem B987719 : Blo 758332 987719 := bstep (se 1 (by rfl) ⟨740789, by rfl⟩ : syracuseStep 987719 = 1481579) B1481579
theorem B1446473 : Blo 758332 1446473 := bstep (se 2 (by rfl) ⟨542427, by rfl⟩ : syracuseStep 1446473 = 1084855) B1084855
theorem B758495 : Blo 758332 758495 := bstep (se 1 (by rfl) ⟨568871, by rfl⟩ : syracuseStep 758495 = 1137743) B1137743
theorem B4100831 : Blo 758332 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B1282783 : Blo 758332 1282783 := bstep (se 1 (by rfl) ⟨962087, by rfl⟩ : syracuseStep 1282783 = 1924175) B1924175
theorem B758575 : Blo 758332 758575 := bstep (se 1 (by rfl) ⟨568931, by rfl⟩ : syracuseStep 758575 = 1137863) B1137863
theorem B758683 : Blo 758332 758683 := bstep (se 1 (by rfl) ⟨569012, by rfl⟩ : syracuseStep 758683 = 1138025) B1138025
theorem B1708955 : Blo 758332 1708955 := bstep (se 1 (by rfl) ⟨1281716, by rfl⟩ : syracuseStep 1708955 = 2563433) B2563433
theorem B758735 : Blo 758332 758735 := bstep (se 1 (by rfl) ⟨569051, by rfl⟩ : syracuseStep 758735 = 1138103) B1138103
theorem B758759 : Blo 758332 758759 := bstep (se 1 (by rfl) ⟨569069, by rfl⟩ : syracuseStep 758759 = 1138139) B1138139
theorem B15602777 : Blo 758332 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B1709153 : Blo 758332 1709153 := bstep (se 2 (by rfl) ⟨640932, by rfl⟩ : syracuseStep 1709153 = 1281865) B1281865
theorem B1283215 : Blo 758332 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B2561273 : Blo 758332 2561273 := bstep (se 2 (by rfl) ⟨960477, by rfl⟩ : syracuseStep 2561273 = 1920955) B1920955
theorem B759071 : Blo 758332 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B1709351 : Blo 758332 1709351 := bstep (se 1 (by rfl) ⟨1282013, by rfl⟩ : syracuseStep 1709351 = 2564027) B2564027
theorem B759131 : Blo 758332 759131 := bstep (se 1 (by rfl) ⟨569348, by rfl⟩ : syracuseStep 759131 = 1138697) B1138697
theorem B759151 : Blo 758332 759151 := bstep (se 1 (by rfl) ⟨569363, by rfl⟩ : syracuseStep 759151 = 1138727) B1138727
theorem B1283465 : Blo 758332 1283465 := bstep (se 2 (by rfl) ⟨481299, by rfl⟩ : syracuseStep 1283465 = 962599) B962599
theorem B759207 : Blo 758332 759207 := bstep (se 1 (by rfl) ⟨569405, by rfl⟩ : syracuseStep 759207 = 1138811) B1138811
theorem B759291 : Blo 758332 759291 := bstep (se 1 (by rfl) ⟨569468, by rfl⟩ : syracuseStep 759291 = 1138937) B1138937
theorem B2561543 : Blo 758332 2561543 := bstep (se 1 (by rfl) ⟨1921157, by rfl⟩ : syracuseStep 2561543 = 3842315) B3842315
theorem B759359 : Blo 758332 759359 := bstep (se 1 (by rfl) ⟨569519, by rfl⟩ : syracuseStep 759359 = 1139039) B1139039
theorem B759367 : Blo 758332 759367 := bstep (se 1 (by rfl) ⟨569525, by rfl⟩ : syracuseStep 759367 = 1139051) B1139051
theorem B1709729 : Blo 758332 1709729 := bstep (se 2 (by rfl) ⟨641148, by rfl⟩ : syracuseStep 1709729 = 1282297) B1282297
theorem B759519 : Blo 758332 759519 := bstep (se 1 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 759519 = 1139279) B1139279
theorem B12982031 : Blo 758332 12982031 := bstep (se 1 (by rfl) ⟨9736523, by rfl⟩ : syracuseStep 12982031 = 19473047) B19473047
theorem B759599 : Blo 758332 759599 := bstep (se 1 (by rfl) ⟨569699, by rfl⟩ : syracuseStep 759599 = 1139399) B1139399
theorem B1283897 : Blo 758332 1283897 := bstep (se 2 (by rfl) ⟨481461, by rfl⟩ : syracuseStep 1283897 = 962923) B962923
theorem B759707 : Blo 758332 759707 := bstep (se 1 (by rfl) ⟨569780, by rfl⟩ : syracuseStep 759707 = 1139561) B1139561
theorem B759759 : Blo 758332 759759 := bstep (se 1 (by rfl) ⟨569819, by rfl⟩ : syracuseStep 759759 = 1139639) B1139639
theorem B759783 : Blo 758332 759783 := bstep (se 1 (by rfl) ⟨569837, by rfl⟩ : syracuseStep 759783 = 1139675) B1139675
theorem B1710089 : Blo 758332 1710089 := bstep (se 2 (by rfl) ⟨641283, by rfl⟩ : syracuseStep 1710089 = 1282567) B1282567
theorem B2889863 : Blo 758332 2889863 := bstep (se 1 (by rfl) ⟨2167397, by rfl⟩ : syracuseStep 2889863 = 4334795) B4334795
theorem B3250361 : Blo 758332 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B760095 : Blo 758332 760095 := bstep (se 1 (by rfl) ⟨570071, by rfl⟩ : syracuseStep 760095 = 1140143) B1140143
theorem B760155 : Blo 758332 760155 := bstep (se 1 (by rfl) ⟨570116, by rfl⟩ : syracuseStep 760155 = 1140233) B1140233
theorem B760175 : Blo 758332 760175 := bstep (se 1 (by rfl) ⟨570131, by rfl⟩ : syracuseStep 760175 = 1140263) B1140263
theorem B1710503 : Blo 758332 1710503 := bstep (se 1 (by rfl) ⟨1282877, by rfl⟩ : syracuseStep 1710503 = 2565755) B2565755
theorem B760231 : Blo 758332 760231 := bstep (se 1 (by rfl) ⟨570173, by rfl⟩ : syracuseStep 760231 = 1140347) B1140347
theorem B2890151 : Blo 758332 2890151 := bstep (se 1 (by rfl) ⟨2167613, by rfl⟩ : syracuseStep 2890151 = 4335227) B4335227
theorem B2562515 : Blo 758332 2562515 := bstep (se 1 (by rfl) ⟨1921886, by rfl⟩ : syracuseStep 2562515 = 3843773) B3843773
theorem B760315 : Blo 758332 760315 := bstep (se 1 (by rfl) ⟨570236, by rfl⟩ : syracuseStep 760315 = 1140473) B1140473
theorem B1710611 : Blo 758332 1710611 := bstep (se 1 (by rfl) ⟨1282958, by rfl⟩ : syracuseStep 1710611 = 2565917) B2565917
theorem B29170205 : Blo 758332 29170205 := bstep (se 3 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 29170205 = 10938827) B10938827
theorem B2562623 : Blo 758332 2562623 := bstep (se 1 (by rfl) ⟨1921967, by rfl⟩ : syracuseStep 2562623 = 3843935) B3843935
theorem B760383 : Blo 758332 760383 := bstep (se 1 (by rfl) ⟨570287, by rfl⟩ : syracuseStep 760383 = 1140575) B1140575
theorem B760391 : Blo 758332 760391 := bstep (se 1 (by rfl) ⟨570293, by rfl⟩ : syracuseStep 760391 = 1140587) B1140587
theorem B2595401 : Blo 758332 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B1710665 : Blo 758332 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B2431595 : Blo 758332 2431595 := bstep (se 1 (by rfl) ⟨1823696, by rfl⟩ : syracuseStep 2431595 = 3647393) B3647393
theorem B8657603 : Blo 758332 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B760543 : Blo 758332 760543 := bstep (se 1 (by rfl) ⟨570407, by rfl⟩ : syracuseStep 760543 = 1140815) B1140815
theorem B760623 : Blo 758332 760623 := bstep (se 1 (by rfl) ⟨570467, by rfl⟩ : syracuseStep 760623 = 1140935) B1140935
theorem B1284943 : Blo 758332 1284943 := bstep (se 1 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 1284943 = 1927415) B1927415
theorem B760731 : Blo 758332 760731 := bstep (se 1 (by rfl) ⟨570548, by rfl⟩ : syracuseStep 760731 = 1141097) B1141097
theorem B2890667 : Blo 758332 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B760783 : Blo 758332 760783 := bstep (se 1 (by rfl) ⟨570587, by rfl⟩ : syracuseStep 760783 = 1141175) B1141175
theorem B1711079 : Blo 758332 1711079 := bstep (se 1 (by rfl) ⟨1283309, by rfl⟩ : syracuseStep 1711079 = 2566619) B2566619
theorem B760807 : Blo 758332 760807 := bstep (se 1 (by rfl) ⟨570605, by rfl⟩ : syracuseStep 760807 = 1141211) B1141211
theorem B4332811 : Blo 758332 4332811 := bstep (se 1 (by rfl) ⟨3249608, by rfl⟩ : syracuseStep 4332811 = 6499217) B6499217
theorem B761119 : Blo 758332 761119 := bstep (se 1 (by rfl) ⟨570839, by rfl⟩ : syracuseStep 761119 = 1141679) B1141679
theorem B13180229 : Blo 758332 13180229 := bstep (se 4 (by rfl) ⟨1235646, by rfl⟩ : syracuseStep 13180229 = 2471293) B2471293
theorem B761179 : Blo 758332 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B1711457 : Blo 758332 1711457 := bstep (se 2 (by rfl) ⟨641796, by rfl⟩ : syracuseStep 1711457 = 1283593) B1283593
theorem B761199 : Blo 758332 761199 := bstep (se 1 (by rfl) ⟨570899, by rfl⟩ : syracuseStep 761199 = 1141799) B1141799
theorem B761255 : Blo 758332 761255 := bstep (se 1 (by rfl) ⟨570941, by rfl⟩ : syracuseStep 761255 = 1141883) B1141883
theorem B1711547 : Blo 758332 1711547 := bstep (se 1 (by rfl) ⟨1283660, by rfl⟩ : syracuseStep 1711547 = 2567321) B2567321
theorem B1220039 : Blo 758332 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B1285625 : Blo 758332 1285625 := bstep (se 2 (by rfl) ⟨482109, by rfl⟩ : syracuseStep 1285625 = 964219) B964219
theorem B761339 : Blo 758332 761339 := bstep (se 1 (by rfl) ⟨571004, by rfl⟩ : syracuseStep 761339 = 1142009) B1142009
theorem B1711673 : Blo 758332 1711673 := bstep (se 2 (by rfl) ⟨641877, by rfl⟩ : syracuseStep 1711673 = 1283755) B1283755
theorem B761407 : Blo 758332 761407 := bstep (se 1 (by rfl) ⟨571055, by rfl⟩ : syracuseStep 761407 = 1142111) B1142111
theorem B761415 : Blo 758332 761415 := bstep (se 1 (by rfl) ⟨571061, by rfl⟩ : syracuseStep 761415 = 1142123) B1142123
theorem B3087953 : Blo 758332 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B3284563 : Blo 758332 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B761567 : Blo 758332 761567 := bstep (se 1 (by rfl) ⟨571175, by rfl⟩ : syracuseStep 761567 = 1142351) B1142351
theorem B1285895 : Blo 758332 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B761647 : Blo 758332 761647 := bstep (se 1 (by rfl) ⟨571235, by rfl⟩ : syracuseStep 761647 = 1142471) B1142471
theorem B2432825 : Blo 758332 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B7413565 : Blo 758332 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B761755 : Blo 758332 761755 := bstep (se 1 (by rfl) ⟨571316, by rfl⟩ : syracuseStep 761755 = 1142633) B1142633
theorem B761807 : Blo 758332 761807 := bstep (se 1 (by rfl) ⟨571355, by rfl⟩ : syracuseStep 761807 = 1142711) B1142711
theorem B761831 : Blo 758332 761831 := bstep (se 1 (by rfl) ⟨571373, by rfl⟩ : syracuseStep 761831 = 1142747) B1142747
theorem B3842153 : Blo 758332 3842153 := bstep (se 2 (by rfl) ⟨1440807, by rfl⟩ : syracuseStep 3842153 = 2881615) B2881615
theorem B2433235 : Blo 758332 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B1712339 : Blo 758332 1712339 := bstep (se 1 (by rfl) ⟨1284254, by rfl⟩ : syracuseStep 1712339 = 2568509) B2568509
theorem B1712393 : Blo 758332 1712393 := bstep (se 2 (by rfl) ⟨642147, by rfl⟩ : syracuseStep 1712393 = 1284295) B1284295
theorem B762143 : Blo 758332 762143 := bstep (se 1 (by rfl) ⟨571607, by rfl⟩ : syracuseStep 762143 = 1143215) B1143215
theorem B762203 : Blo 758332 762203 := bstep (se 1 (by rfl) ⟨571652, by rfl⟩ : syracuseStep 762203 = 1143305) B1143305
theorem B2564459 : Blo 758332 2564459 := bstep (se 1 (by rfl) ⟨1923344, by rfl⟩ : syracuseStep 2564459 = 3846689) B3846689
theorem B762223 : Blo 758332 762223 := bstep (se 1 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 762223 = 1143335) B1143335
theorem B762279 : Blo 758332 762279 := bstep (se 1 (by rfl) ⟨571709, by rfl⟩ : syracuseStep 762279 = 1143419) B1143419
theorem B1712609 : Blo 758332 1712609 := bstep (se 2 (by rfl) ⟨642228, by rfl⟩ : syracuseStep 1712609 = 1284457) B1284457
theorem B3252737 : Blo 758332 3252737 := bstep (se 2 (by rfl) ⟨1219776, by rfl⟩ : syracuseStep 3252737 = 2439553) B2439553
theorem B5153291 : Blo 758332 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B2892307 : Blo 758332 2892307 := bstep (se 1 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 2892307 = 4338461) B4338461
theorem B2564729 : Blo 758332 2564729 := bstep (se 2 (by rfl) ⟨961773, by rfl⟩ : syracuseStep 2564729 = 1923547) B1923547
theorem B3252889 : Blo 758332 3252889 := bstep (se 2 (by rfl) ⟨1219833, by rfl⟩ : syracuseStep 3252889 = 2439667) B2439667
theorem B3252959 : Blo 758332 3252959 := bstep (se 1 (by rfl) ⟨2439719, by rfl⟩ : syracuseStep 3252959 = 4879439) B4879439
theorem B49357583 : Blo 758332 49357583 := bstep (se 1 (by rfl) ⟨37018187, by rfl⟩ : syracuseStep 49357583 = 74036375) B74036375
theorem B1712915 : Blo 758332 1712915 := bstep (se 1 (by rfl) ⟨1284686, by rfl⟩ : syracuseStep 1712915 = 2569373) B2569373
theorem B1713275 : Blo 758332 1713275 := bstep (se 1 (by rfl) ⟨1284956, by rfl⟩ : syracuseStep 1713275 = 2569913) B2569913
theorem B3843287 : Blo 758332 3843287 := bstep (se 1 (by rfl) ⟨2882465, by rfl⟩ : syracuseStep 3843287 = 5764931) B5764931
theorem B1975511 : Blo 758332 1975511 := bstep (se 1 (by rfl) ⟨1481633, by rfl⟩ : syracuseStep 1975511 = 2963267) B2963267
theorem B1713401 : Blo 758332 1713401 := bstep (se 2 (by rfl) ⟨642525, by rfl⟩ : syracuseStep 1713401 = 1285051) B1285051
theorem B1713545 : Blo 758332 1713545 := bstep (se 2 (by rfl) ⟨642579, by rfl⟩ : syracuseStep 1713545 = 1285159) B1285159
theorem B2434465 : Blo 758332 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B1713671 : Blo 758332 1713671 := bstep (se 1 (by rfl) ⟨1285253, by rfl⟩ : syracuseStep 1713671 = 2570507) B2570507
theorem B1713851 : Blo 758332 1713851 := bstep (se 1 (by rfl) ⟨1285388, by rfl⟩ : syracuseStep 1713851 = 2570777) B2570777
theorem B1713977 : Blo 758332 1713977 := bstep (se 2 (by rfl) ⟨642741, by rfl⟩ : syracuseStep 1713977 = 1285483) B1285483
theorem B3647855 : Blo 758332 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B2566511 : Blo 758332 2566511 := bstep (se 1 (by rfl) ⟨1924883, by rfl⟩ : syracuseStep 2566511 = 3849767) B3849767
theorem B1714607 : Blo 758332 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B1714643 : Blo 758332 1714643 := bstep (se 1 (by rfl) ⟨1285982, by rfl⟩ : syracuseStep 1714643 = 2571965) B2571965
theorem B1714751 : Blo 758332 1714751 := bstep (se 1 (by rfl) ⟨1286063, by rfl⟩ : syracuseStep 1714751 = 2572127) B2572127
theorem B1714859 : Blo 758332 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B3910339 : Blo 758332 3910339 := bstep (se 1 (by rfl) ⟨2932754, by rfl⟩ : syracuseStep 3910339 = 5865509) B5865509
theorem B961247 : Blo 758332 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B1026857 : Blo 758332 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B4631363 : Blo 758332 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B3255335 : Blo 758332 3255335 := bstep (se 1 (by rfl) ⟨2441501, by rfl⟩ : syracuseStep 3255335 = 4883003) B4883003
theorem B35105861 : Blo 758332 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B4107581 : Blo 758332 4107581 := bstep (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) B1540343
theorem B3911161 : Blo 758332 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B1027819 : Blo 758332 1027819 := bstep (se 1 (by rfl) ⟨770864, by rfl⟩ : syracuseStep 1027819 = 1541729) B1541729
theorem B2567915 : Blo 758332 2567915 := bstep (se 1 (by rfl) ⟨1925936, by rfl⟩ : syracuseStep 2567915 = 3851873) B3851873
theorem B2469761 : Blo 758332 2469761 := bstep (se 2 (by rfl) ⟨926160, by rfl⟩ : syracuseStep 2469761 = 1852321) B1852321
theorem B3846203 : Blo 758332 3846203 := bstep (se 1 (by rfl) ⟨2884652, by rfl⟩ : syracuseStep 3846203 = 5769305) B5769305
theorem B2306731 : Blo 758332 2306731 := bstep (se 1 (by rfl) ⟨1730048, by rfl⟩ : syracuseStep 2306731 = 3460097) B3460097
theorem B963247 : Blo 758332 963247 := bstep (se 1 (by rfl) ⟨722435, by rfl⟩ : syracuseStep 963247 = 1444871) B1444871
theorem B2568887 : Blo 758332 2568887 := bstep (se 1 (by rfl) ⟨1926665, by rfl⟩ : syracuseStep 2568887 = 3853331) B3853331
theorem B5485391 : Blo 758332 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B1029019 : Blo 758332 1029019 := bstep (se 1 (by rfl) ⟨771764, by rfl⟩ : syracuseStep 1029019 = 1543529) B1543529
theorem B3847175 : Blo 758332 3847175 := bstep (se 1 (by rfl) ⟨2885381, by rfl⟩ : syracuseStep 3847175 = 5770763) B5770763
theorem B2307215 : Blo 758332 2307215 := bstep (se 1 (by rfl) ⟨1730411, by rfl⟩ : syracuseStep 2307215 = 3460823) B3460823
theorem B2438387 : Blo 758332 2438387 := bstep (se 1 (by rfl) ⟨1828790, by rfl⟩ : syracuseStep 2438387 = 3657581) B3657581
theorem B2372903 : Blo 758332 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B3847661 : Blo 758332 3847661 := bstep (se 3 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 3847661 = 1442873) B1442873
theorem B7288861 : Blo 758332 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B3848471 : Blo 758332 3848471 := bstep (se 1 (by rfl) ⟨2886353, by rfl⟩ : syracuseStep 3848471 = 5772707) B5772707
theorem B1620499 : Blo 758332 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B20855369 : Blo 758332 20855369 := bstep (se 2 (by rfl) ⟨7820763, by rfl⟩ : syracuseStep 20855369 = 15641527) B15641527
theorem B2570831 : Blo 758332 2570831 := bstep (se 1 (by rfl) ⟨1928123, by rfl⟩ : syracuseStep 2570831 = 3856247) B3856247
theorem B7289477 : Blo 758332 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B5192387 : Blo 758332 5192387 := bstep (se 1 (by rfl) ⟨3894290, by rfl⟩ : syracuseStep 5192387 = 7788581) B7788581
theorem B2079479 : Blo 758332 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B5782427 : Blo 758332 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B1981673 : Blo 758332 1981673 := bstep (se 2 (by rfl) ⟨743127, by rfl⟩ : syracuseStep 1981673 = 1486255) B1486255
theorem B9747701 : Blo 758332 9747701 := bstep (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) B913847
theorem B4865291 : Blo 758332 4865291 := bstep (se 1 (by rfl) ⟨3648968, by rfl⟩ : syracuseStep 4865291 = 7297937) B7297937
theorem B4341059 : Blo 758332 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B1392223 : Blo 758332 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B8208017 : Blo 758332 8208017 := bstep (se 2 (by rfl) ⟨3078006, by rfl⟩ : syracuseStep 8208017 = 6156013) B6156013
theorem B2572073 : Blo 758332 2572073 := bstep (se 2 (by rfl) ⟨964527, by rfl⟩ : syracuseStep 2572073 = 1929055) B1929055
theorem B3850091 : Blo 758332 3850091 := bstep (se 1 (by rfl) ⟨2887568, by rfl⟩ : syracuseStep 3850091 = 5775137) B5775137
theorem B13877153 : Blo 758332 13877153 := bstep (se 2 (by rfl) ⟨5203932, by rfl⟩ : syracuseStep 13877153 = 10407865) B10407865
theorem B18530315 : Blo 758332 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B13877669 : Blo 758332 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B1622447 : Blo 758332 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B1426331 : Blo 758332 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B5850119 : Blo 758332 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B7423073 : Blo 758332 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B9225359 : Blo 758332 9225359 := bstep (se 1 (by rfl) ⟨6919019, by rfl⟩ : syracuseStep 9225359 = 13838039) B13838039
theorem B111166667 : Blo 758332 111166667 := bstep (se 1 (by rfl) ⟨83375000, by rfl⟩ : syracuseStep 111166667 = 166750001) B166750001
theorem B1623635 : Blo 758332 1623635 := bstep (se 1 (by rfl) ⟨1217726, by rfl⟩ : syracuseStep 1623635 = 2435453) B2435453
theorem B1624531 : Blo 758332 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B1919609 : Blo 758332 1919609 := bstep (se 2 (by rfl) ⟨719853, by rfl⟩ : syracuseStep 1919609 = 1439707) B1439707
theorem B1919659 : Blo 758332 1919659 := bstep (se 1 (by rfl) ⟨1439744, by rfl⟩ : syracuseStep 1919659 = 2879489) B2879489
theorem B4868855 : Blo 758332 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B5557015 : Blo 758332 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B1919963 : Blo 758332 1919963 := bstep (se 1 (by rfl) ⟨1439972, by rfl⟩ : syracuseStep 1919963 = 2879945) B2879945
theorem B1920287 : Blo 758332 1920287 := bstep (se 1 (by rfl) ⟨1440215, by rfl⟩ : syracuseStep 1920287 = 2880431) B2880431
theorem B3853817 : Blo 758332 3853817 := bstep (se 2 (by rfl) ⟨1445181, by rfl⟩ : syracuseStep 3853817 = 2890363) B2890363
theorem B1625761 : Blo 758332 1625761 := bstep (se 2 (by rfl) ⟨609660, by rfl⟩ : syracuseStep 1625761 = 1219321) B1219321
theorem B3854141 : Blo 758332 3854141 := bstep (se 3 (by rfl) ⟨722651, by rfl⟩ : syracuseStep 3854141 = 1445303) B1445303
theorem B1921391 : Blo 758332 1921391 := bstep (se 1 (by rfl) ⟨1441043, by rfl⟩ : syracuseStep 1921391 = 2882087) B2882087
theorem B2740807 : Blo 758332 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B9851615 : Blo 758332 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B3658715 : Blo 758332 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B3167207 : Blo 758332 3167207 := bstep (se 1 (by rfl) ⟨2375405, by rfl⟩ : syracuseStep 3167207 = 4750811) B4750811
theorem B1922039 : Blo 758332 1922039 := bstep (se 1 (by rfl) ⟨1441529, by rfl⟩ : syracuseStep 1922039 = 2883059) B2883059
theorem B2741627 : Blo 758332 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B7296551 : Blo 758332 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B1628009 : Blo 758332 1628009 := bstep (se 2 (by rfl) ⟨610503, by rfl⟩ : syracuseStep 1628009 = 1221007) B1221007
theorem B1464895 : Blo 758332 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B6576815 : Blo 758332 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B3857219 : Blo 758332 3857219 := bstep (se 1 (by rfl) ⟨2892914, by rfl⟩ : syracuseStep 3857219 = 5785829) B5785829
theorem B1923983 : Blo 758332 1923983 := bstep (se 1 (by rfl) ⟨1442987, by rfl⟩ : syracuseStep 1923983 = 2885975) B2885975
theorem B1137563 : Blo 758332 1137563 := bstep (se 1 (by rfl) ⟨853172, by rfl⟩ : syracuseStep 1137563 = 1706345) B1706345
theorem B3660731 : Blo 758332 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B1137959 : Blo 758332 1137959 := bstep (se 1 (by rfl) ⟨853469, by rfl⟩ : syracuseStep 1137959 = 1706939) B1706939
theorem B3661175 : Blo 758332 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B1138043 : Blo 758332 1138043 := bstep (se 1 (by rfl) ⟨853532, by rfl⟩ : syracuseStep 1138043 = 1707065) B1707065
theorem B3661193 : Blo 758332 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B3661271 : Blo 758332 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B1826297 : Blo 758332 1826297 := bstep (se 2 (by rfl) ⟨684861, by rfl⟩ : syracuseStep 1826297 = 1369723) B1369723
theorem B1138169 : Blo 758332 1138169 := bstep (se 2 (by rfl) ⟨426813, by rfl⟩ : syracuseStep 1138169 = 853627) B853627
theorem B1138271 : Blo 758332 1138271 := bstep (se 1 (by rfl) ⟨853703, by rfl⟩ : syracuseStep 1138271 = 1707407) B1707407
theorem B3858029 : Blo 758332 3858029 := bstep (se 3 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 3858029 = 1446761) B1446761
theorem B1924843 : Blo 758332 1924843 := bstep (se 1 (by rfl) ⟨1443632, by rfl⟩ : syracuseStep 1924843 = 2887265) B2887265
theorem B1367815 : Blo 758332 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B1138487 : Blo 758332 1138487 := bstep (se 1 (by rfl) ⟨853865, by rfl⟩ : syracuseStep 1138487 = 1707731) B1707731
theorem B2809961 : Blo 758332 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B1138793 : Blo 758332 1138793 := bstep (se 2 (by rfl) ⟨427047, by rfl⟩ : syracuseStep 1138793 = 854095) B854095
theorem B1826945 : Blo 758332 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B1139111 : Blo 758332 1139111 := bstep (se 1 (by rfl) ⟨854333, by rfl⟩ : syracuseStep 1139111 = 1708667) B1708667
theorem B1139195 : Blo 758332 1139195 := bstep (se 1 (by rfl) ⟨854396, by rfl⟩ : syracuseStep 1139195 = 1708793) B1708793
theorem B1139321 : Blo 758332 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B1139375 : Blo 758332 1139375 := bstep (se 1 (by rfl) ⟨854531, by rfl⟩ : syracuseStep 1139375 = 1709063) B1709063
theorem B1925815 : Blo 758332 1925815 := bstep (se 1 (by rfl) ⟨1444361, by rfl⟩ : syracuseStep 1925815 = 2888723) B2888723
theorem B1139423 : Blo 758332 1139423 := bstep (se 1 (by rfl) ⟨854567, by rfl⟩ : syracuseStep 1139423 = 1709135) B1709135
theorem B1139687 : Blo 758332 1139687 := bstep (se 1 (by rfl) ⟨854765, by rfl⟩ : syracuseStep 1139687 = 1709531) B1709531
theorem B1926119 : Blo 758332 1926119 := bstep (se 1 (by rfl) ⟨1444589, by rfl⟩ : syracuseStep 1926119 = 2889179) B2889179
theorem B1827983 : Blo 758332 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B1139945 : Blo 758332 1139945 := bstep (se 2 (by rfl) ⟨427479, by rfl⟩ : syracuseStep 1139945 = 854959) B854959
theorem B1139999 : Blo 758332 1139999 := bstep (se 1 (by rfl) ⟨854999, by rfl⟩ : syracuseStep 1139999 = 1709999) B1709999
theorem B1828127 : Blo 758332 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B3663191 : Blo 758332 3663191 := bstep (se 1 (by rfl) ⟨2747393, by rfl⟩ : syracuseStep 3663191 = 5494787) B5494787
theorem B4875643 : Blo 758332 4875643 := bstep (se 1 (by rfl) ⟨3656732, by rfl⟩ : syracuseStep 4875643 = 7313465) B7313465
theorem B1140167 : Blo 758332 1140167 := bstep (se 1 (by rfl) ⟨855125, by rfl⟩ : syracuseStep 1140167 = 1710251) B1710251
theorem B32826869 : Blo 758332 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B812539 : Blo 758332 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B1828435 : Blo 758332 1828435 := bstep (se 1 (by rfl) ⟨1371326, by rfl⟩ : syracuseStep 1828435 = 2742653) B2742653
theorem B1140521 : Blo 758332 1140521 := bstep (se 2 (by rfl) ⟨427695, by rfl⟩ : syracuseStep 1140521 = 855391) B855391
theorem B1140527 : Blo 758332 1140527 := bstep (se 1 (by rfl) ⟨855395, by rfl⟩ : syracuseStep 1140527 = 1710791) B1710791
theorem B1927273 : Blo 758332 1927273 := bstep (se 2 (by rfl) ⟨722727, by rfl⟩ : syracuseStep 1927273 = 1445455) B1445455
theorem B1141001 : Blo 758332 1141001 := bstep (se 2 (by rfl) ⟨427875, by rfl⟩ : syracuseStep 1141001 = 855751) B855751
theorem B1141103 : Blo 758332 1141103 := bstep (se 1 (by rfl) ⟨855827, by rfl⟩ : syracuseStep 1141103 = 1711655) B1711655
theorem B911935 : Blo 758332 911935 := bstep (se 1 (by rfl) ⟨683951, by rfl⟩ : syracuseStep 911935 = 1367903) B1367903
theorem B1141319 : Blo 758332 1141319 := bstep (se 1 (by rfl) ⟨855989, by rfl⟩ : syracuseStep 1141319 = 1711979) B1711979
theorem B1927759 : Blo 758332 1927759 := bstep (se 1 (by rfl) ⟨1445819, by rfl⟩ : syracuseStep 1927759 = 2891639) B2891639
theorem B1141355 : Blo 758332 1141355 := bstep (se 1 (by rfl) ⟨856016, by rfl⟩ : syracuseStep 1141355 = 1712033) B1712033
theorem B20834995 : Blo 758332 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B568519397 : Blo 758332 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B10414871 : Blo 758332 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B1141583 : Blo 758332 1141583 := bstep (se 1 (by rfl) ⟨856187, by rfl⟩ : syracuseStep 1141583 = 1712375) B1712375
theorem B2747279 : Blo 758332 2747279 := bstep (se 1 (by rfl) ⟨2060459, by rfl⟩ : syracuseStep 2747279 = 4120919) B4120919
theorem B1928407 : Blo 758332 1928407 := bstep (se 1 (by rfl) ⟨1446305, by rfl⟩ : syracuseStep 1928407 = 2892611) B2892611
theorem B1141979 : Blo 758332 1141979 := bstep (se 1 (by rfl) ⟨856484, by rfl⟩ : syracuseStep 1141979 = 1712969) B1712969
theorem B1142153 : Blo 758332 1142153 := bstep (se 2 (by rfl) ⟨428307, by rfl⟩ : syracuseStep 1142153 = 856615) B856615
theorem B2059681 : Blo 758332 2059681 := bstep (se 2 (by rfl) ⟨772380, by rfl⟩ : syracuseStep 2059681 = 1544761) B1544761
theorem B1928711 : Blo 758332 1928711 := bstep (se 1 (by rfl) ⟨1446533, by rfl⟩ : syracuseStep 1928711 = 2893067) B2893067
theorem B3698291 : Blo 758332 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B1142507 : Blo 758332 1142507 := bstep (se 1 (by rfl) ⟨856880, by rfl⟩ : syracuseStep 1142507 = 1713761) B1713761
theorem B3239837 : Blo 758332 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B1142735 : Blo 758332 1142735 := bstep (se 1 (by rfl) ⟨857051, by rfl⟩ : syracuseStep 1142735 = 1714103) B1714103
theorem B1929167 : Blo 758332 1929167 := bstep (se 1 (by rfl) ⟨1446875, by rfl⟩ : syracuseStep 1929167 = 2893751) B2893751
theorem B4681729 : Blo 758332 4681729 := bstep (se 2 (by rfl) ⟨1755648, by rfl⟩ : syracuseStep 4681729 = 3511297) B3511297
theorem B1143131 : Blo 758332 1143131 := bstep (se 1 (by rfl) ⟨857348, by rfl⟩ : syracuseStep 1143131 = 1714697) B1714697
theorem B1143359 : Blo 758332 1143359 := bstep (se 1 (by rfl) ⟨857519, by rfl⟩ : syracuseStep 1143359 = 1715039) B1715039
theorem B1143479 : Blo 758332 1143479 := bstep (se 1 (by rfl) ⟨857609, by rfl⟩ : syracuseStep 1143479 = 1715219) B1715219
theorem B3077065 : Blo 758332 3077065 := bstep (se 2 (by rfl) ⟨1153899, by rfl⟩ : syracuseStep 3077065 = 2307799) B2307799
theorem B14840777 : Blo 758332 14840777 := bstep (se 2 (by rfl) ⟨5565291, by rfl⟩ : syracuseStep 14840777 = 11130583) B11130583
theorem B9893011 : Blo 758332 9893011 := bstep (se 1 (by rfl) ⟨7419758, by rfl⟩ : syracuseStep 9893011 = 14839517) B14839517
theorem B3241255 : Blo 758332 3241255 := bstep (se 1 (by rfl) ⟨2430941, by rfl⟩ : syracuseStep 3241255 = 4861883) B4861883
theorem B3241529 : Blo 758332 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B6486095 : Blo 758332 6486095 := bstep (se 1 (by rfl) ⟨4864571, by rfl⟩ : syracuseStep 6486095 = 9729143) B9729143
theorem B2160893 : Blo 758332 2160893 := bstep (se 3 (by rfl) ⟨405167, by rfl⟩ : syracuseStep 2160893 = 810335) B810335
theorem B14056739 : Blo 758332 14056739 := bstep (se 1 (by rfl) ⟨10542554, by rfl⟩ : syracuseStep 14056739 = 21085109) B21085109
theorem B24969221 : Blo 758332 24969221 := bstep (se 4 (by rfl) ⟨2340864, by rfl⟩ : syracuseStep 24969221 = 4681729) B4681729
theorem B12353543 : Blo 758332 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B3244313 : Blo 758332 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B1081631 : Blo 758332 1081631 := bstep (se 1 (by rfl) ⟨811223, by rfl⟩ : syracuseStep 1081631 = 1622447) B1622447
theorem B1442281 : Blo 758332 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B950887 : Blo 758332 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B3900079 : Blo 758332 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B1442539 : Blo 758332 1442539 := bstep (se 1 (by rfl) ⟨1081904, by rfl⟩ : syracuseStep 1442539 = 2163809) B2163809
theorem B4948715 : Blo 758332 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B1082423 : Blo 758332 1082423 := bstep (se 1 (by rfl) ⟨811817, by rfl⟩ : syracuseStep 1082423 = 1623635) B1623635
theorem B2164391 : Blo 758332 2164391 := bstep (se 1 (by rfl) ⟨1623293, by rfl⟩ : syracuseStep 2164391 = 3246587) B3246587
theorem B1279739 : Blo 758332 1279739 := bstep (se 1 (by rfl) ⟨959804, by rfl⟩ : syracuseStep 1279739 = 1919609) B1919609
theorem B3245903 : Blo 758332 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B3245953 : Blo 758332 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B1279975 : Blo 758332 1279975 := bstep (se 1 (by rfl) ⟨959981, by rfl⟩ : syracuseStep 1279975 = 1919963) B1919963
theorem B1083385 : Blo 758332 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B1280191 : Blo 758332 1280191 := bstep (se 1 (by rfl) ⟨960143, by rfl⟩ : syracuseStep 1280191 = 1920287) B1920287
theorem B2165039 : Blo 758332 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B8653229 : Blo 758332 8653229 := bstep (se 3 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 8653229 = 3244961) B3244961
theorem B1280927 : Blo 758332 1280927 := bstep (se 1 (by rfl) ⟨960695, by rfl⟩ : syracuseStep 1280927 = 1921391) B1921391
theorem B2165723 : Blo 758332 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B5770277 : Blo 758332 5770277 := bstep (se 4 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 5770277 = 1081927) B1081927
theorem B2166041 : Blo 758332 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B1281359 : Blo 758332 1281359 := bstep (se 1 (by rfl) ⟨961019, by rfl⟩ : syracuseStep 1281359 = 1922039) B1922039
theorem B1215913 : Blo 758332 1215913 := bstep (se 2 (by rfl) ⟨455967, by rfl⟩ : syracuseStep 1215913 = 911935) B911935
theorem B1707515 : Blo 758332 1707515 := bstep (se 1 (by rfl) ⟨1280636, by rfl⟩ : syracuseStep 1707515 = 2561273) B2561273
theorem B2559545 : Blo 758332 2559545 := bstep (se 2 (by rfl) ⟨959829, by rfl⟩ : syracuseStep 2559545 = 1919659) B1919659
theorem B9768509 : Blo 758332 9768509 := bstep (se 3 (by rfl) ⟨1831595, by rfl⟩ : syracuseStep 9768509 = 3663191) B3663191
theorem B855643 : Blo 758332 855643 := bstep (se 1 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 855643 = 1283465) B1283465
theorem B7311005 : Blo 758332 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B1707695 : Blo 758332 1707695 := bstep (se 1 (by rfl) ⟨1280771, by rfl⟩ : syracuseStep 1707695 = 2561543) B2561543
theorem B8654687 : Blo 758332 8654687 := bstep (se 1 (by rfl) ⟨6491015, by rfl⟩ : syracuseStep 8654687 = 12982031) B12982031
theorem B855931 : Blo 758332 855931 := bstep (se 1 (by rfl) ⟨641948, by rfl⟩ : syracuseStep 855931 = 1283897) B1283897
theorem B1085339 : Blo 758332 1085339 := bstep (se 1 (by rfl) ⟨814004, by rfl⟩ : syracuseStep 1085339 = 1628009) B1628009
theorem B2166907 : Blo 758332 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B2887933 : Blo 758332 2887933 := bstep (se 3 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 2887933 = 1082975) B1082975
theorem B1708343 : Blo 758332 1708343 := bstep (se 1 (by rfl) ⟨1281257, by rfl⟩ : syracuseStep 1708343 = 2562515) B2562515
theorem B1708415 : Blo 758332 1708415 := bstep (se 1 (by rfl) ⟨1281311, by rfl⟩ : syracuseStep 1708415 = 2562623) B2562623
theorem B5771735 : Blo 758332 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B1282655 : Blo 758332 1282655 := bstep (se 1 (by rfl) ⟨961991, by rfl⟩ : syracuseStep 1282655 = 1923983) B1923983
theorem B758375 : Blo 758332 758375 := bstep (se 1 (by rfl) ⟨568781, by rfl⟩ : syracuseStep 758375 = 1137563) B1137563
theorem B5214881 : Blo 758332 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B758639 : Blo 758332 758639 := bstep (se 1 (by rfl) ⟨568979, by rfl⟩ : syracuseStep 758639 = 1137959) B1137959
theorem B8786819 : Blo 758332 8786819 := bstep (se 1 (by rfl) ⟨6590114, by rfl⟩ : syracuseStep 8786819 = 13180229) B13180229
theorem B758695 : Blo 758332 758695 := bstep (se 1 (by rfl) ⟨569021, by rfl⟩ : syracuseStep 758695 = 1138043) B1138043
theorem B1217531 : Blo 758332 1217531 := bstep (se 1 (by rfl) ⟨913148, by rfl⟩ : syracuseStep 1217531 = 1826297) B1826297
theorem B758779 : Blo 758332 758779 := bstep (se 1 (by rfl) ⟨569084, by rfl⟩ : syracuseStep 758779 = 1138169) B1138169
theorem B857083 : Blo 758332 857083 := bstep (se 1 (by rfl) ⟨642812, by rfl⟩ : syracuseStep 857083 = 1285625) B1285625
theorem B758847 : Blo 758332 758847 := bstep (se 1 (by rfl) ⟨569135, by rfl⟩ : syracuseStep 758847 = 1138271) B1138271
theorem B857263 : Blo 758332 857263 := bstep (se 1 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 857263 = 1285895) B1285895
theorem B758991 : Blo 758332 758991 := bstep (se 1 (by rfl) ⟨569243, by rfl⟩ : syracuseStep 758991 = 1138487) B1138487
theorem B1873307 : Blo 758332 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B2561435 : Blo 758332 2561435 := bstep (se 1 (by rfl) ⟨1921076, by rfl⟩ : syracuseStep 2561435 = 3842153) B3842153
theorem B759195 : Blo 758332 759195 := bstep (se 1 (by rfl) ⟨569396, by rfl⟩ : syracuseStep 759195 = 1138793) B1138793
theorem B1217963 : Blo 758332 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B1709639 : Blo 758332 1709639 := bstep (se 1 (by rfl) ⟨1282229, by rfl⟩ : syracuseStep 1709639 = 2564459) B2564459
theorem B759407 : Blo 758332 759407 := bstep (se 1 (by rfl) ⟨569555, by rfl⟩ : syracuseStep 759407 = 1139111) B1139111
theorem B759463 : Blo 758332 759463 := bstep (se 1 (by rfl) ⟨569597, by rfl⟩ : syracuseStep 759463 = 1139195) B1139195
theorem B2168491 : Blo 758332 2168491 := bstep (se 1 (by rfl) ⟨1626368, by rfl⟩ : syracuseStep 2168491 = 3252737) B3252737
theorem B759547 : Blo 758332 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B1709819 : Blo 758332 1709819 := bstep (se 1 (by rfl) ⟨1282364, by rfl⟩ : syracuseStep 1709819 = 2564729) B2564729
theorem B759583 : Blo 758332 759583 := bstep (se 1 (by rfl) ⟨569687, by rfl⟩ : syracuseStep 759583 = 1139375) B1139375
theorem B759615 : Blo 758332 759615 := bstep (se 1 (by rfl) ⟨569711, by rfl⟩ : syracuseStep 759615 = 1139423) B1139423
theorem B2168639 : Blo 758332 2168639 := bstep (se 1 (by rfl) ⟨1626479, by rfl⟩ : syracuseStep 2168639 = 3252959) B3252959
theorem B32905055 : Blo 758332 32905055 := bstep (se 1 (by rfl) ⟨24678791, by rfl⟩ : syracuseStep 32905055 = 49357583) B49357583
theorem B759791 : Blo 758332 759791 := bstep (se 1 (by rfl) ⟨569843, by rfl⟩ : syracuseStep 759791 = 1139687) B1139687
theorem B1284079 : Blo 758332 1284079 := bstep (se 1 (by rfl) ⟨963059, by rfl⟩ : syracuseStep 1284079 = 1926119) B1926119
theorem B1218655 : Blo 758332 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B2562191 : Blo 758332 2562191 := bstep (se 1 (by rfl) ⟨1921643, by rfl⟩ : syracuseStep 2562191 = 3843287) B3843287
theorem B1317007 : Blo 758332 1317007 := bstep (se 1 (by rfl) ⟨987755, by rfl⟩ : syracuseStep 1317007 = 1975511) B1975511
theorem B759963 : Blo 758332 759963 := bstep (se 1 (by rfl) ⟨569972, by rfl⟩ : syracuseStep 759963 = 1139945) B1139945
theorem B759999 : Blo 758332 759999 := bstep (se 1 (by rfl) ⟨569999, by rfl⟩ : syracuseStep 759999 = 1139999) B1139999
theorem B1284329 : Blo 758332 1284329 := bstep (se 2 (by rfl) ⟨481623, by rfl⟩ : syracuseStep 1284329 = 963247) B963247
theorem B1710377 : Blo 758332 1710377 := bstep (se 2 (by rfl) ⟨641391, by rfl⟩ : syracuseStep 1710377 = 1282783) B1282783
theorem B760111 : Blo 758332 760111 := bstep (se 1 (by rfl) ⟨570083, by rfl⟩ : syracuseStep 760111 = 1140167) B1140167
theorem B760347 : Blo 758332 760347 := bstep (se 1 (by rfl) ⟨570260, by rfl⟩ : syracuseStep 760347 = 1140521) B1140521
theorem B760351 : Blo 758332 760351 := bstep (se 1 (by rfl) ⟨570263, by rfl⟩ : syracuseStep 760351 = 1140527) B1140527
theorem B4102753 : Blo 758332 4102753 := bstep (se 2 (by rfl) ⟨1538532, by rfl⟩ : syracuseStep 4102753 = 3077065) B3077065
theorem B760667 : Blo 758332 760667 := bstep (se 1 (by rfl) ⟨570500, by rfl⟩ : syracuseStep 760667 = 1141001) B1141001
theorem B1710953 : Blo 758332 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B2431903 : Blo 758332 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B1711007 : Blo 758332 1711007 := bstep (se 1 (by rfl) ⟨1283255, by rfl⟩ : syracuseStep 1711007 = 2566511) B2566511
theorem B760735 : Blo 758332 760735 := bstep (se 1 (by rfl) ⟨570551, by rfl⟩ : syracuseStep 760735 = 1141103) B1141103
theorem B760879 : Blo 758332 760879 := bstep (se 1 (by rfl) ⟨570659, by rfl⟩ : syracuseStep 760879 = 1141319) B1141319
theorem B760903 : Blo 758332 760903 := bstep (se 1 (by rfl) ⟨570677, by rfl⟩ : syracuseStep 760903 = 1141355) B1141355
theorem B3087575 : Blo 758332 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B761055 : Blo 758332 761055 := bstep (se 1 (by rfl) ⟨570791, by rfl⟩ : syracuseStep 761055 = 1141583) B1141583
theorem B2563325 : Blo 758332 2563325 := bstep (se 3 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 2563325 = 961247) B961247
theorem B2170223 : Blo 758332 2170223 := bstep (se 1 (by rfl) ⟨1627667, by rfl⟩ : syracuseStep 2170223 = 3255335) B3255335
theorem B23403907 : Blo 758332 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B761319 : Blo 758332 761319 := bstep (se 1 (by rfl) ⟨570989, by rfl⟩ : syracuseStep 761319 = 1141979) B1141979
theorem B761435 : Blo 758332 761435 := bstep (se 1 (by rfl) ⟨571076, by rfl⟩ : syracuseStep 761435 = 1142153) B1142153
theorem B1285807 : Blo 758332 1285807 := bstep (se 1 (by rfl) ⟨964355, by rfl⟩ : syracuseStep 1285807 = 1928711) B1928711
theorem B2465527 : Blo 758332 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B1711943 : Blo 758332 1711943 := bstep (se 1 (by rfl) ⟨1283957, by rfl⟩ : syracuseStep 1711943 = 2567915) B2567915
theorem B761671 : Blo 758332 761671 := bstep (se 1 (by rfl) ⟨571253, by rfl⟩ : syracuseStep 761671 = 1142507) B1142507
theorem B1646507 : Blo 758332 1646507 := bstep (se 1 (by rfl) ⟨1234880, by rfl⟩ : syracuseStep 1646507 = 2469761) B2469761
theorem B761823 : Blo 758332 761823 := bstep (se 1 (by rfl) ⟨571367, by rfl⟩ : syracuseStep 761823 = 1142735) B1142735
theorem B1286111 : Blo 758332 1286111 := bstep (se 1 (by rfl) ⟨964583, by rfl⟩ : syracuseStep 1286111 = 1929167) B1929167
theorem B2564135 : Blo 758332 2564135 := bstep (se 1 (by rfl) ⟨1923101, by rfl⟩ : syracuseStep 2564135 = 3846203) B3846203
theorem B762087 : Blo 758332 762087 := bstep (se 1 (by rfl) ⟨571565, by rfl⟩ : syracuseStep 762087 = 1143131) B1143131
theorem B762239 : Blo 758332 762239 := bstep (se 1 (by rfl) ⟨571679, by rfl⟩ : syracuseStep 762239 = 1143359) B1143359
theorem B1712591 : Blo 758332 1712591 := bstep (se 1 (by rfl) ⟨1284443, by rfl⟩ : syracuseStep 1712591 = 2568887) B2568887
theorem B762319 : Blo 758332 762319 := bstep (se 1 (by rfl) ⟨571739, by rfl⟩ : syracuseStep 762319 = 1143479) B1143479
theorem B2564783 : Blo 758332 2564783 := bstep (se 1 (by rfl) ⟨1923587, by rfl⟩ : syracuseStep 2564783 = 3847175) B3847175
theorem B1581935 : Blo 758332 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B2565107 : Blo 758332 2565107 := bstep (se 1 (by rfl) ⟨1923830, by rfl⟩ : syracuseStep 2565107 = 3847661) B3847661
theorem B1713257 : Blo 758332 1713257 := bstep (se 2 (by rfl) ⟨642471, by rfl⟩ : syracuseStep 1713257 = 1284943) B1284943
theorem B5481701 : Blo 758332 5481701 := bstep (se 4 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 5481701 = 1027819) B1027819
theorem B2565647 : Blo 758332 2565647 := bstep (se 1 (by rfl) ⟨1924235, by rfl⟩ : syracuseStep 2565647 = 3848471) B3848471
theorem B5777081 : Blo 758332 5777081 := bstep (se 2 (by rfl) ⟨2166405, by rfl⟩ : syracuseStep 5777081 = 4332811) B4332811
theorem B13903579 : Blo 758332 13903579 := bstep (se 1 (by rfl) ⟨10427684, by rfl⟩ : syracuseStep 13903579 = 20855369) B20855369
theorem B1713887 : Blo 758332 1713887 := bstep (se 1 (by rfl) ⟨1285415, by rfl⟩ : syracuseStep 1713887 = 2570831) B2570831
theorem B4859651 : Blo 758332 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B1386319 : Blo 758332 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B1321115 : Blo 758332 1321115 := bstep (se 1 (by rfl) ⟨990836, by rfl⟩ : syracuseStep 1321115 = 1981673) B1981673
theorem B6498467 : Blo 758332 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B2894039 : Blo 758332 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B2566457 : Blo 758332 2566457 := bstep (se 2 (by rfl) ⟨962421, by rfl⟩ : syracuseStep 2566457 = 1924843) B1924843
theorem B1714715 : Blo 758332 1714715 := bstep (se 1 (by rfl) ⟨1286036, by rfl⟩ : syracuseStep 1714715 = 2572073) B2572073
theorem B2566727 : Blo 758332 2566727 := bstep (se 1 (by rfl) ⟨1925045, by rfl⟩ : syracuseStep 2566727 = 3850091) B3850091
theorem B9251435 : Blo 758332 9251435 := bstep (se 1 (by rfl) ⟨6938576, by rfl⟩ : syracuseStep 9251435 = 13877153) B13877153
theorem B4337185 : Blo 758332 4337185 := bstep (se 2 (by rfl) ⟨1626444, by rfl⟩ : syracuseStep 4337185 = 3252889) B3252889
theorem B2567753 : Blo 758332 2567753 := bstep (se 2 (by rfl) ⟨962907, by rfl⟩ : syracuseStep 2567753 = 1925815) B1925815
theorem B37007117 : Blo 758332 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B6500857 : Blo 758332 6500857 := bstep (se 2 (by rfl) ⟨2437821, by rfl⟩ : syracuseStep 6500857 = 4875643) B4875643
theorem B2437913 : Blo 758332 2437913 := bstep (se 2 (by rfl) ⟨914217, by rfl⟩ : syracuseStep 2437913 = 1828435) B1828435
theorem B1028975 : Blo 758332 1028975 := bstep (se 1 (by rfl) ⟨771731, by rfl⟩ : syracuseStep 1028975 = 1543463) B1543463
theorem B2569211 : Blo 758332 2569211 := bstep (se 1 (by rfl) ⟨1926908, by rfl⟩ : syracuseStep 2569211 = 3853817) B3853817
theorem B2569427 : Blo 758332 2569427 := bstep (se 1 (by rfl) ⟨1927070, by rfl⟩ : syracuseStep 2569427 = 3854141) B3854141
theorem B2569697 : Blo 758332 2569697 := bstep (se 2 (by rfl) ⟨963636, by rfl⟩ : syracuseStep 2569697 = 1927273) B1927273
theorem B964315 : Blo 758332 964315 := bstep (se 1 (by rfl) ⟨723236, by rfl⟩ : syracuseStep 964315 = 1446473) B1446473
theorem B6567743 : Blo 758332 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B2733887 : Blo 758332 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B2439143 : Blo 758332 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B2111471 : Blo 758332 2111471 := bstep (se 1 (by rfl) ⟨1583603, by rfl⟩ : syracuseStep 2111471 = 3167207) B3167207
theorem B10401851 : Blo 758332 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B2570345 : Blo 758332 2570345 := bstep (se 2 (by rfl) ⟨963879, by rfl⟩ : syracuseStep 2570345 = 1927759) B1927759
theorem B20855141 : Blo 758332 20855141 := bstep (se 4 (by rfl) ⟨1955169, by rfl⟩ : syracuseStep 20855141 = 3910339) B3910339
theorem B4864367 : Blo 758332 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B29637413 : Blo 758332 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B2571209 : Blo 758332 2571209 := bstep (se 2 (by rfl) ⟨964203, by rfl⟩ : syracuseStep 2571209 = 1928407) B1928407
theorem B19446803 : Blo 758332 19446803 := bstep (se 1 (by rfl) ⟨14585102, by rfl⟩ : syracuseStep 19446803 = 29170205) B29170205
theorem B1621063 : Blo 758332 1621063 := bstep (se 1 (by rfl) ⟨1215797, by rfl⟩ : syracuseStep 1621063 = 2431595) B2431595
theorem B2571479 : Blo 758332 2571479 := bstep (se 1 (by rfl) ⟨1928609, by rfl⟩ : syracuseStep 2571479 = 3857219) B3857219
theorem B2440487 : Blo 758332 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B2440783 : Blo 758332 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B2440795 : Blo 758332 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B2440847 : Blo 758332 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B1621729 : Blo 758332 1621729 := bstep (se 2 (by rfl) ⟨608148, by rfl⟩ : syracuseStep 1621729 = 1216297) B1216297
theorem B2572019 : Blo 758332 2572019 := bstep (se 1 (by rfl) ⟨1929014, by rfl⟩ : syracuseStep 2572019 = 3858029) B3858029
theorem B1621883 : Blo 758332 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B1753577 : Blo 758332 1753577 := bstep (se 2 (by rfl) ⟨657591, by rfl⟩ : syracuseStep 1753577 = 1315183) B1315183
theorem B10535669 : Blo 758332 10535669 := bstep (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) B987719
theorem B3654409 : Blo 758332 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B13190681 : Blo 758332 13190681 := bstep (se 2 (by rfl) ⟨4946505, by rfl⟩ : syracuseStep 13190681 = 9893011) B9893011
theorem B379012931 : Blo 758332 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B2738285 : Blo 758332 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B2738387 : Blo 758332 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B9718481 : Blo 758332 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B3656927 : Blo 758332 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B1953193 : Blo 758332 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B1625591 : Blo 758332 1625591 := bstep (se 1 (by rfl) ⟨1219193, by rfl⟩ : syracuseStep 1625591 = 2438387) B2438387
theorem B8670725 : Blo 758332 8670725 := bstep (se 4 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 8670725 = 1625761) B1625761
theorem B3461591 : Blo 758332 3461591 := bstep (se 1 (by rfl) ⟨2596193, by rfl⟩ : syracuseStep 3461591 = 5192387) B5192387
theorem B3854951 : Blo 758332 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B4379417 : Blo 758332 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B1856297 : Blo 758332 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B1823753 : Blo 758332 1823753 := bstep (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) B1367815
theorem B9884753 : Blo 758332 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B19486169 : Blo 758332 19486169 := bstep (se 2 (by rfl) ⟨7307313, by rfl⟩ : syracuseStep 19486169 = 14614627) B14614627
theorem B1922879 : Blo 758332 1922879 := bstep (se 1 (by rfl) ⟨1442159, by rfl⟩ : syracuseStep 1922879 = 2884319) B2884319
theorem B3856409 : Blo 758332 3856409 := bstep (se 2 (by rfl) ⟨1446153, by rfl⟩ : syracuseStep 3856409 = 2892307) B2892307
theorem B6150239 : Blo 758332 6150239 := bstep (se 1 (by rfl) ⟨4612679, by rfl⟩ : syracuseStep 6150239 = 9225359) B9225359
theorem B74111111 : Blo 758332 74111111 := bstep (se 1 (by rfl) ⟨55583333, by rfl⟩ : syracuseStep 74111111 = 111166667) B111166667
theorem B21911795 : Blo 758332 21911795 := bstep (se 1 (by rfl) ⟨16433846, by rfl⟩ : syracuseStep 21911795 = 32867693) B32867693
theorem B1923335 : Blo 758332 1923335 := bstep (se 1 (by rfl) ⟨1442501, by rfl⟩ : syracuseStep 1923335 = 2885003) B2885003
theorem B1137785 : Blo 758332 1137785 := bstep (se 2 (by rfl) ⟨426669, by rfl⟩ : syracuseStep 1137785 = 853339) B853339
theorem B1137887 : Blo 758332 1137887 := bstep (se 1 (by rfl) ⟨853415, by rfl⟩ : syracuseStep 1137887 = 1706831) B1706831
theorem B1137929 : Blo 758332 1137929 := bstep (se 2 (by rfl) ⟨426723, by rfl⟩ : syracuseStep 1137929 = 853447) B853447
theorem B1138031 : Blo 758332 1138031 := bstep (se 1 (by rfl) ⟨853523, by rfl⟩ : syracuseStep 1138031 = 1707047) B1707047
theorem B1924519 : Blo 758332 1924519 := bstep (se 1 (by rfl) ⟨1443389, by rfl⟩ : syracuseStep 1924519 = 2886779) B2886779
theorem B1138151 : Blo 758332 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B1138283 : Blo 758332 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B1138409 : Blo 758332 1138409 := bstep (se 2 (by rfl) ⟨426903, by rfl⟩ : syracuseStep 1138409 = 853807) B853807
theorem B15621983 : Blo 758332 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B39575405 : Blo 758332 39575405 := bstep (se 3 (by rfl) ⟨7420388, by rfl⟩ : syracuseStep 39575405 = 14840777) B14840777
theorem B1138553 : Blo 758332 1138553 := bstep (se 2 (by rfl) ⟨426957, by rfl⟩ : syracuseStep 1138553 = 853915) B853915
theorem B1138655 : Blo 758332 1138655 := bstep (se 1 (by rfl) ⟨853991, by rfl⟩ : syracuseStep 1138655 = 1707983) B1707983
theorem B1138907 : Blo 758332 1138907 := bstep (se 1 (by rfl) ⟨854180, by rfl⟩ : syracuseStep 1138907 = 1708361) B1708361
theorem B1138919 : Blo 758332 1138919 := bstep (se 1 (by rfl) ⟨854189, by rfl⟩ : syracuseStep 1138919 = 1708379) B1708379
theorem B24600833 : Blo 758332 24600833 := bstep (se 2 (by rfl) ⟨9225312, by rfl⟩ : syracuseStep 24600833 = 18450625) B18450625
theorem B6152573 : Blo 758332 6152573 := bstep (se 3 (by rfl) ⟨1153607, by rfl⟩ : syracuseStep 6152573 = 2307215) B2307215
theorem B1139081 : Blo 758332 1139081 := bstep (se 2 (by rfl) ⟨427155, by rfl⟩ : syracuseStep 1139081 = 854311) B854311
theorem B1139177 : Blo 758332 1139177 := bstep (se 2 (by rfl) ⟨427191, by rfl⟩ : syracuseStep 1139177 = 854383) B854383
theorem B1139303 : Blo 758332 1139303 := bstep (se 1 (by rfl) ⟨854477, by rfl⟩ : syracuseStep 1139303 = 1708955) B1708955
theorem B1139435 : Blo 758332 1139435 := bstep (se 1 (by rfl) ⟨854576, by rfl⟩ : syracuseStep 1139435 = 1709153) B1709153
theorem B4875005 : Blo 758332 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B1139465 : Blo 758332 1139465 := bstep (se 2 (by rfl) ⟨427299, by rfl⟩ : syracuseStep 1139465 = 854599) B854599
theorem B1139567 : Blo 758332 1139567 := bstep (se 1 (by rfl) ⟨854675, by rfl⟩ : syracuseStep 1139567 = 1709351) B1709351
theorem B27779993 : Blo 758332 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B1139819 : Blo 758332 1139819 := bstep (se 1 (by rfl) ⟨854864, by rfl⟩ : syracuseStep 1139819 = 1709729) B1709729
theorem B1140059 : Blo 758332 1140059 := bstep (se 1 (by rfl) ⟨855044, by rfl⟩ : syracuseStep 1140059 = 1710089) B1710089
theorem B1926575 : Blo 758332 1926575 := bstep (se 1 (by rfl) ⟨1444931, by rfl⟩ : syracuseStep 1926575 = 2889863) B2889863
theorem B1140335 : Blo 758332 1140335 := bstep (se 1 (by rfl) ⟨855251, by rfl⟩ : syracuseStep 1140335 = 1710503) B1710503
theorem B1926767 : Blo 758332 1926767 := bstep (se 1 (by rfl) ⟨1445075, by rfl⟩ : syracuseStep 1926767 = 2890151) B2890151
theorem B1140407 : Blo 758332 1140407 := bstep (se 1 (by rfl) ⟨855305, by rfl⟩ : syracuseStep 1140407 = 1710611) B1710611
theorem B1730267 : Blo 758332 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B1140443 : Blo 758332 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B4384543 : Blo 758332 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B2746241 : Blo 758332 2746241 := bstep (se 2 (by rfl) ⟨1029840, by rfl⟩ : syracuseStep 2746241 = 2059681) B2059681
theorem B1140617 : Blo 758332 1140617 := bstep (se 2 (by rfl) ⟨427731, by rfl⟩ : syracuseStep 1140617 = 855463) B855463
theorem B1927111 : Blo 758332 1927111 := bstep (se 1 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 1927111 = 2890667) B2890667
theorem B1140719 : Blo 758332 1140719 := bstep (se 1 (by rfl) ⟨855539, by rfl⟩ : syracuseStep 1140719 = 1711079) B1711079
theorem B1140971 : Blo 758332 1140971 := bstep (se 1 (by rfl) ⟨855728, by rfl⟩ : syracuseStep 1140971 = 1711457) B1711457
theorem B1141031 : Blo 758332 1141031 := bstep (se 1 (by rfl) ⟨855773, by rfl⟩ : syracuseStep 1141031 = 1711547) B1711547
theorem B813359 : Blo 758332 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B1141115 : Blo 758332 1141115 := bstep (se 1 (by rfl) ⟨855836, by rfl⟩ : syracuseStep 1141115 = 1711673) B1711673
theorem B2058635 : Blo 758332 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B1141385 : Blo 758332 1141385 := bstep (se 2 (by rfl) ⟨428019, by rfl⟩ : syracuseStep 1141385 = 856039) B856039
theorem B1141559 : Blo 758332 1141559 := bstep (se 1 (by rfl) ⟨856169, by rfl⟩ : syracuseStep 1141559 = 1712339) B1712339
theorem B1141595 : Blo 758332 1141595 := bstep (se 1 (by rfl) ⟨856196, by rfl⟩ : syracuseStep 1141595 = 1712393) B1712393
theorem B1141739 : Blo 758332 1141739 := bstep (se 1 (by rfl) ⟨856304, by rfl⟩ : syracuseStep 1141739 = 1712609) B1712609
theorem B3435527 : Blo 758332 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B1141943 : Blo 758332 1141943 := bstep (se 1 (by rfl) ⟨856457, by rfl⟩ : syracuseStep 1141943 = 1712915) B1712915
theorem B1142183 : Blo 758332 1142183 := bstep (se 1 (by rfl) ⟨856637, by rfl⟩ : syracuseStep 1142183 = 1713275) B1713275
theorem B1142267 : Blo 758332 1142267 := bstep (se 1 (by rfl) ⟨856700, by rfl⟩ : syracuseStep 1142267 = 1713401) B1713401
theorem B3075641 : Blo 758332 3075641 := bstep (se 2 (by rfl) ⟨1153365, by rfl⟩ : syracuseStep 3075641 = 2306731) B2306731
theorem B1142363 : Blo 758332 1142363 := bstep (se 1 (by rfl) ⟨856772, by rfl⟩ : syracuseStep 1142363 = 1713545) B1713545
theorem B21884579 : Blo 758332 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B1142447 : Blo 758332 1142447 := bstep (se 1 (by rfl) ⟨856835, by rfl⟩ : syracuseStep 1142447 = 1713671) B1713671
theorem B1142567 : Blo 758332 1142567 := bstep (se 1 (by rfl) ⟨856925, by rfl⟩ : syracuseStep 1142567 = 1713851) B1713851
theorem B1372025 : Blo 758332 1372025 := bstep (se 2 (by rfl) ⟨514509, by rfl⟩ : syracuseStep 1372025 = 1029019) B1029019
theorem B1142651 : Blo 758332 1142651 := bstep (se 1 (by rfl) ⟨856988, by rfl⟩ : syracuseStep 1142651 = 1713977) B1713977
theorem B1143071 : Blo 758332 1143071 := bstep (se 1 (by rfl) ⟨857303, by rfl⟩ : syracuseStep 1143071 = 1714607) B1714607
theorem B1143095 : Blo 758332 1143095 := bstep (se 1 (by rfl) ⟨857321, by rfl⟩ : syracuseStep 1143095 = 1714643) B1714643
theorem B1143167 : Blo 758332 1143167 := bstep (se 1 (by rfl) ⟨857375, by rfl⟩ : syracuseStep 1143167 = 1714751) B1714751
theorem B4321673 : Blo 758332 4321673 := bstep (se 2 (by rfl) ⟨1620627, by rfl⟩ : syracuseStep 4321673 = 3241255) B3241255
theorem B1143239 : Blo 758332 1143239 := bstep (se 1 (by rfl) ⟨857429, by rfl⟩ : syracuseStep 1143239 = 1714859) B1714859
theorem B6943247 : Blo 758332 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B1831519 : Blo 758332 1831519 := bstep (se 1 (by rfl) ⟨1373639, by rfl⟩ : syracuseStep 1831519 = 2747279) B2747279
theorem B2159891 : Blo 758332 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B2160665 : Blo 758332 2160665 := bstep (se 2 (by rfl) ⟨810249, by rfl⟩ : syracuseStep 2160665 = 1620499) B1620499
theorem B2161019 : Blo 758332 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B4324063 : Blo 758332 4324063 := bstep (se 1 (by rfl) ⟨3243047, by rfl⟩ : syracuseStep 4324063 = 6486095) B6486095
theorem B1440595 : Blo 758332 1440595 := bstep (se 1 (by rfl) ⟨1080446, by rfl⟩ : syracuseStep 1440595 = 2160893) B2160893
theorem B3243527 : Blo 758332 3243527 := bstep (se 1 (by rfl) ⟨2432645, by rfl⟩ : syracuseStep 3243527 = 4865291) B4865291
theorem B9371159 : Blo 758332 9371159 := bstep (se 1 (by rfl) ⟨7028369, by rfl⟩ : syracuseStep 9371159 = 14056739) B14056739
theorem B5472011 : Blo 758332 5472011 := bstep (se 1 (by rfl) ⟨4104008, by rfl⟩ : syracuseStep 5472011 = 8208017) B8208017
theorem B16646147 : Blo 758332 16646147 := bstep (se 1 (by rfl) ⟨12484610, by rfl⟩ : syracuseStep 16646147 = 24969221) B24969221
theorem B2162875 : Blo 758332 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B2884349 : Blo 758332 2884349 := bstep (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) B1081631
theorem B1442927 : Blo 758332 1442927 := bstep (se 1 (by rfl) ⟨1082195, by rfl⟩ : syracuseStep 1442927 = 2164391) B2164391
theorem B853159 : Blo 758332 853159 := bstep (se 1 (by rfl) ⟨639869, by rfl⟩ : syracuseStep 853159 = 1279739) B1279739
theorem B252675287 : Blo 758332 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B2163935 : Blo 758332 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B1443359 : Blo 758332 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B5768819 : Blo 758332 5768819 := bstep (se 1 (by rfl) ⟨4326614, by rfl⟩ : syracuseStep 5768819 = 8653229) B8653229
theorem B853951 : Blo 758332 853951 := bstep (se 1 (by rfl) ⟨640463, by rfl⟩ : syracuseStep 853951 = 1280927) B1280927
theorem B1443815 : Blo 758332 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B854239 : Blo 758332 854239 := bstep (se 1 (by rfl) ⟨640679, by rfl⟩ : syracuseStep 854239 = 1281359) B1281359
theorem B1083727 : Blo 758332 1083727 := bstep (se 1 (by rfl) ⟨812795, by rfl⟩ : syracuseStep 1083727 = 1625591) B1625591
theorem B1706363 : Blo 758332 1706363 := bstep (se 1 (by rfl) ⟨1279772, by rfl⟩ : syracuseStep 1706363 = 2559545) B2559545
theorem B4327937 : Blo 758332 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B5769791 : Blo 758332 5769791 := bstep (se 1 (by rfl) ⟨4327343, by rfl⟩ : syracuseStep 5769791 = 8654687) B8654687
theorem B1706633 : Blo 758332 1706633 := bstep (se 2 (by rfl) ⟨639987, by rfl⟩ : syracuseStep 1706633 = 1279975) B1279975
theorem B2886461 : Blo 758332 2886461 := bstep (se 3 (by rfl) ⟨541211, by rfl⟩ : syracuseStep 2886461 = 1082423) B1082423
theorem B1706921 : Blo 758332 1706921 := bstep (se 2 (by rfl) ⟨640095, by rfl⟩ : syracuseStep 1706921 = 1280191) B1280191
theorem B855103 : Blo 758332 855103 := bstep (se 1 (by rfl) ⟨641327, by rfl⟩ : syracuseStep 855103 = 1282655) B1282655
theorem B2919611 : Blo 758332 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B6589835 : Blo 758332 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B1707623 : Blo 758332 1707623 := bstep (se 1 (by rfl) ⟨1280717, by rfl⟩ : syracuseStep 1707623 = 2561435) B2561435
theorem B1248871 : Blo 758332 1248871 := bstep (se 1 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 1248871 = 1873307) B1873307
theorem B3247901 : Blo 758332 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B1281919 : Blo 758332 1281919 := bstep (se 1 (by rfl) ⟨961439, by rfl⟩ : syracuseStep 1281919 = 1922879) B1922879
theorem B1445759 : Blo 758332 1445759 := bstep (se 1 (by rfl) ⟨1084319, by rfl⟩ : syracuseStep 1445759 = 2168639) B2168639
theorem B4100159 : Blo 758332 4100159 := bstep (se 1 (by rfl) ⟨3075119, by rfl⟩ : syracuseStep 4100159 = 6150239) B6150239
theorem B1708127 : Blo 758332 1708127 := bstep (se 1 (by rfl) ⟨1281095, by rfl⟩ : syracuseStep 1708127 = 2562191) B2562191
theorem B856219 : Blo 758332 856219 := bstep (se 1 (by rfl) ⟨642164, by rfl⟩ : syracuseStep 856219 = 1284329) B1284329
theorem B1282223 : Blo 758332 1282223 := bstep (se 1 (by rfl) ⟨961667, by rfl⟩ : syracuseStep 1282223 = 1923335) B1923335
theorem B758523 : Blo 758332 758523 := bstep (se 1 (by rfl) ⟨568892, by rfl⟩ : syracuseStep 758523 = 1137785) B1137785
theorem B758591 : Blo 758332 758591 := bstep (se 1 (by rfl) ⟨568943, by rfl⟩ : syracuseStep 758591 = 1137887) B1137887
theorem B1708883 : Blo 758332 1708883 := bstep (se 1 (by rfl) ⟨1281662, by rfl⟩ : syracuseStep 1708883 = 2563325) B2563325
theorem B758619 : Blo 758332 758619 := bstep (se 1 (by rfl) ⟨568964, by rfl⟩ : syracuseStep 758619 = 1137929) B1137929
theorem B758687 : Blo 758332 758687 := bstep (se 1 (by rfl) ⟨569015, by rfl⟩ : syracuseStep 758687 = 1138031) B1138031
theorem B1446815 : Blo 758332 1446815 := bstep (se 1 (by rfl) ⟨1085111, by rfl⟩ : syracuseStep 1446815 = 2170223) B2170223
theorem B758767 : Blo 758332 758767 := bstep (se 1 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 758767 = 1138151) B1138151
theorem B758855 : Blo 758332 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B758939 : Blo 758332 758939 := bstep (se 1 (by rfl) ⟨569204, by rfl⟩ : syracuseStep 758939 = 1138409) B1138409
theorem B26383603 : Blo 758332 26383603 := bstep (se 1 (by rfl) ⟨19787702, by rfl⟩ : syracuseStep 26383603 = 39575405) B39575405
theorem B759035 : Blo 758332 759035 := bstep (se 1 (by rfl) ⟨569276, by rfl⟩ : syracuseStep 759035 = 1138553) B1138553
theorem B759103 : Blo 758332 759103 := bstep (se 1 (by rfl) ⟨569327, by rfl⟩ : syracuseStep 759103 = 1138655) B1138655
theorem B857407 : Blo 758332 857407 := bstep (se 1 (by rfl) ⟨643055, by rfl⟩ : syracuseStep 857407 = 1286111) B1286111
theorem B1709423 : Blo 758332 1709423 := bstep (se 1 (by rfl) ⟨1282067, by rfl⟩ : syracuseStep 1709423 = 2564135) B2564135
theorem B759271 : Blo 758332 759271 := bstep (se 1 (by rfl) ⟨569453, by rfl⟩ : syracuseStep 759271 = 1138907) B1138907
theorem B759279 : Blo 758332 759279 := bstep (se 1 (by rfl) ⟨569459, by rfl⟩ : syracuseStep 759279 = 1138919) B1138919
theorem B2889209 : Blo 758332 2889209 := bstep (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) B2166907
theorem B4101715 : Blo 758332 4101715 := bstep (se 1 (by rfl) ⟨3076286, by rfl⟩ : syracuseStep 4101715 = 6152573) B6152573
theorem B759387 : Blo 758332 759387 := bstep (se 1 (by rfl) ⟨569540, by rfl⟩ : syracuseStep 759387 = 1139081) B1139081
theorem B759451 : Blo 758332 759451 := bstep (se 1 (by rfl) ⟨569588, by rfl⟩ : syracuseStep 759451 = 1139177) B1139177
theorem B759535 : Blo 758332 759535 := bstep (se 1 (by rfl) ⟨569651, by rfl⟩ : syracuseStep 759535 = 1139303) B1139303
theorem B1709855 : Blo 758332 1709855 := bstep (se 1 (by rfl) ⟨1282391, by rfl⟩ : syracuseStep 1709855 = 2564783) B2564783
theorem B759623 : Blo 758332 759623 := bstep (se 1 (by rfl) ⟨569717, by rfl⟩ : syracuseStep 759623 = 1139435) B1139435
theorem B3250003 : Blo 758332 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B759643 : Blo 758332 759643 := bstep (se 1 (by rfl) ⟨569732, by rfl⟩ : syracuseStep 759643 = 1139465) B1139465
theorem B759711 : Blo 758332 759711 := bstep (se 1 (by rfl) ⟨569783, by rfl⟩ : syracuseStep 759711 = 1139567) B1139567
theorem B18519995 : Blo 758332 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B1710071 : Blo 758332 1710071 := bstep (se 1 (by rfl) ⟨1282553, by rfl⟩ : syracuseStep 1710071 = 2565107) B2565107
theorem B759879 : Blo 758332 759879 := bstep (se 1 (by rfl) ⟨569909, by rfl⟩ : syracuseStep 759879 = 1139819) B1139819
theorem B2168957 : Blo 758332 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B760039 : Blo 758332 760039 := bstep (se 1 (by rfl) ⟨570029, by rfl⟩ : syracuseStep 760039 = 1140059) B1140059
theorem B1284383 : Blo 758332 1284383 := bstep (se 1 (by rfl) ⟨963287, by rfl⟩ : syracuseStep 1284383 = 1926575) B1926575
theorem B1710431 : Blo 758332 1710431 := bstep (se 1 (by rfl) ⟨1282823, by rfl⟩ : syracuseStep 1710431 = 2565647) B2565647
theorem B760223 : Blo 758332 760223 := bstep (se 1 (by rfl) ⟨570167, by rfl⟩ : syracuseStep 760223 = 1140335) B1140335
theorem B1284511 : Blo 758332 1284511 := bstep (se 1 (by rfl) ⟨963383, by rfl⟩ : syracuseStep 1284511 = 1926767) B1926767
theorem B760271 : Blo 758332 760271 := bstep (se 1 (by rfl) ⟨570203, by rfl⟩ : syracuseStep 760271 = 1140407) B1140407
theorem B1153511 : Blo 758332 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B760295 : Blo 758332 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B760411 : Blo 758332 760411 := bstep (se 1 (by rfl) ⟨570308, by rfl⟩ : syracuseStep 760411 = 1140617) B1140617
theorem B760479 : Blo 758332 760479 := bstep (se 1 (by rfl) ⟨570359, by rfl⟩ : syracuseStep 760479 = 1140719) B1140719
theorem B4332311 : Blo 758332 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B760647 : Blo 758332 760647 := bstep (se 1 (by rfl) ⟨570485, by rfl⟩ : syracuseStep 760647 = 1140971) B1140971
theorem B760687 : Blo 758332 760687 := bstep (se 1 (by rfl) ⟨570515, by rfl⟩ : syracuseStep 760687 = 1141031) B1141031
theorem B1710971 : Blo 758332 1710971 := bstep (se 1 (by rfl) ⟨1283228, by rfl⟩ : syracuseStep 1710971 = 2566457) B2566457
theorem B760743 : Blo 758332 760743 := bstep (se 1 (by rfl) ⟨570557, by rfl⟩ : syracuseStep 760743 = 1141115) B1141115
theorem B1711151 : Blo 758332 1711151 := bstep (se 1 (by rfl) ⟨1283363, by rfl⟩ : syracuseStep 1711151 = 2566727) B2566727
theorem B6167623 : Blo 758332 6167623 := bstep (se 1 (by rfl) ⟨4625717, by rfl⟩ : syracuseStep 6167623 = 9251435) B9251435
theorem B760923 : Blo 758332 760923 := bstep (se 1 (by rfl) ⟨570692, by rfl⟩ : syracuseStep 760923 = 1141385) B1141385
theorem B761039 : Blo 758332 761039 := bstep (se 1 (by rfl) ⟨570779, by rfl⟩ : syracuseStep 761039 = 1141559) B1141559
theorem B761063 : Blo 758332 761063 := bstep (se 1 (by rfl) ⟨570797, by rfl⟩ : syracuseStep 761063 = 1141595) B1141595
theorem B761159 : Blo 758332 761159 := bstep (se 1 (by rfl) ⟨570869, by rfl⟩ : syracuseStep 761159 = 1141739) B1141739
theorem B761295 : Blo 758332 761295 := bstep (se 1 (by rfl) ⟨570971, by rfl⟩ : syracuseStep 761295 = 1141943) B1141943
theorem B2891321 : Blo 758332 2891321 := bstep (se 2 (by rfl) ⟨1084245, by rfl⟩ : syracuseStep 2891321 = 2168491) B2168491
theorem B761455 : Blo 758332 761455 := bstep (se 1 (by rfl) ⟨571091, by rfl⟩ : syracuseStep 761455 = 1142183) B1142183
theorem B1285753 : Blo 758332 1285753 := bstep (se 2 (by rfl) ⟨482157, by rfl⟩ : syracuseStep 1285753 = 964315) B964315
theorem B761511 : Blo 758332 761511 := bstep (se 1 (by rfl) ⟨571133, by rfl⟩ : syracuseStep 761511 = 1142267) B1142267
theorem B1711835 : Blo 758332 1711835 := bstep (se 1 (by rfl) ⟨1283876, by rfl⟩ : syracuseStep 1711835 = 2567753) B2567753
theorem B761575 : Blo 758332 761575 := bstep (se 1 (by rfl) ⟨571181, by rfl⟩ : syracuseStep 761575 = 1142363) B1142363
theorem B14589719 : Blo 758332 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B761631 : Blo 758332 761631 := bstep (se 1 (by rfl) ⟨571223, by rfl⟩ : syracuseStep 761631 = 1142447) B1142447
theorem B761711 : Blo 758332 761711 := bstep (se 1 (by rfl) ⟨571283, by rfl⟩ : syracuseStep 761711 = 1142567) B1142567
theorem B761767 : Blo 758332 761767 := bstep (se 1 (by rfl) ⟨571325, by rfl⟩ : syracuseStep 761767 = 1142651) B1142651
theorem B1712105 : Blo 758332 1712105 := bstep (se 2 (by rfl) ⟨642039, by rfl⟩ : syracuseStep 1712105 = 1284079) B1284079
theorem B762047 : Blo 758332 762047 := bstep (se 1 (by rfl) ⟨571535, by rfl⟩ : syracuseStep 762047 = 1143071) B1143071
theorem B762063 : Blo 758332 762063 := bstep (se 1 (by rfl) ⟨571547, by rfl⟩ : syracuseStep 762063 = 1143095) B1143095
theorem B762111 : Blo 758332 762111 := bstep (se 1 (by rfl) ⟨571583, by rfl⟩ : syracuseStep 762111 = 1143167) B1143167
theorem B762159 : Blo 758332 762159 := bstep (se 1 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 762159 = 1143239) B1143239
theorem B4628831 : Blo 758332 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B1712807 : Blo 758332 1712807 := bstep (se 1 (by rfl) ⟨1284605, by rfl⟩ : syracuseStep 1712807 = 2569211) B2569211
theorem B5776109 : Blo 758332 5776109 := bstep (se 3 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 5776109 = 2166041) B2166041
theorem B1712951 : Blo 758332 1712951 := bstep (se 1 (by rfl) ⟨1284713, by rfl⟩ : syracuseStep 1712951 = 2569427) B2569427
theorem B1713131 : Blo 758332 1713131 := bstep (se 1 (by rfl) ⟨1284848, by rfl⟩ : syracuseStep 1713131 = 2569697) B2569697
theorem B1713563 : Blo 758332 1713563 := bstep (se 1 (by rfl) ⟨1285172, by rfl⟩ : syracuseStep 1713563 = 2570345) B2570345
theorem B13903427 : Blo 758332 13903427 := bstep (se 1 (by rfl) ⟨10427570, by rfl⟩ : syracuseStep 13903427 = 20855141) B20855141
theorem B31205209 : Blo 758332 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B2566025 : Blo 758332 2566025 := bstep (se 2 (by rfl) ⟨962259, by rfl⟩ : syracuseStep 2566025 = 1924519) B1924519
theorem B1714139 : Blo 758332 1714139 := bstep (se 1 (by rfl) ⟨1285604, by rfl⟩ : syracuseStep 1714139 = 2571209) B2571209
theorem B3254377 : Blo 758332 3254377 := bstep (se 2 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 3254377 = 2440783) B2440783
theorem B3254393 : Blo 758332 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B1714319 : Blo 758332 1714319 := bstep (se 1 (by rfl) ⟨1285739, by rfl⟩ : syracuseStep 1714319 = 2571479) B2571479
theorem B1714409 : Blo 758332 1714409 := bstep (se 2 (by rfl) ⟨642903, by rfl⟩ : syracuseStep 1714409 = 1285807) B1285807
theorem B3287369 : Blo 758332 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B2894237 : Blo 758332 2894237 := bstep (se 3 (by rfl) ⟨542669, by rfl⟩ : syracuseStep 2894237 = 1085339) B1085339
theorem B1714679 : Blo 758332 1714679 := bstep (se 1 (by rfl) ⟨1286009, by rfl⟩ : syracuseStep 1714679 = 2572019) B2572019
theorem B3648007 : Blo 758332 3648007 := bstep (se 1 (by rfl) ⟨2736005, by rfl⟩ : syracuseStep 3648007 = 5472011) B5472011
theorem B5778053 : Blo 758332 5778053 := bstep (se 4 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 5778053 = 1083385) B1083385
theorem B8235695 : Blo 758332 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B7023779 : Blo 758332 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B8793787 : Blo 758332 8793787 := bstep (se 1 (by rfl) ⟨6595340, by rfl⟩ : syracuseStep 8793787 = 13190681) B13190681
theorem B13906349 : Blo 758332 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B3846851 : Blo 758332 3846851 := bstep (se 1 (by rfl) ⟨2885138, by rfl⟩ : syracuseStep 3846851 = 5770277) B5770277
theorem B2437951 : Blo 758332 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B5780483 : Blo 758332 5780483 := bstep (se 1 (by rfl) ⟨4335362, by rfl⟩ : syracuseStep 5780483 = 8670725) B8670725
theorem B5846057 : Blo 758332 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B1848425 : Blo 758332 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B2569481 : Blo 758332 2569481 := bstep (se 2 (by rfl) ⟨963555, by rfl⟩ : syracuseStep 2569481 = 1927111) B1927111
theorem B4863341 : Blo 758332 4863341 := bstep (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) B1823753
theorem B2307727 : Blo 758332 2307727 := bstep (se 1 (by rfl) ⟨1730795, by rfl⟩ : syracuseStep 2307727 = 3461591) B3461591
theorem B3847823 : Blo 758332 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B2569967 : Blo 758332 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B12990779 : Blo 758332 12990779 := bstep (se 1 (by rfl) ⟨9743084, by rfl⟩ : syracuseStep 12990779 = 19486169) B19486169
theorem B21936703 : Blo 758332 21936703 := bstep (se 1 (by rfl) ⟨16452527, by rfl⟩ : syracuseStep 21936703 = 32905055) B32905055
theorem B2570939 : Blo 758332 2570939 := bstep (se 1 (by rfl) ⟨1928204, by rfl⟩ : syracuseStep 2570939 = 3856409) B3856409
theorem B1621217 : Blo 758332 1621217 := bstep (se 2 (by rfl) ⟨607956, by rfl⟩ : syracuseStep 1621217 = 1215913) B1215913
theorem B2604257 : Blo 758332 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B5782913 : Blo 758332 5782913 := bstep (se 2 (by rfl) ⟨2168592, by rfl⟩ : syracuseStep 5782913 = 4337185) B4337185
theorem B1097671 : Blo 758332 1097671 := bstep (se 1 (by rfl) ⟨823253, by rfl⟩ : syracuseStep 1097671 = 1646507) B1646507
theorem B16400555 : Blo 758332 16400555 := bstep (se 1 (by rfl) ⟨12300416, by rfl⟩ : syracuseStep 16400555 = 24600833) B24600833
theorem B3850577 : Blo 758332 3850577 := bstep (se 2 (by rfl) ⟨1443966, by rfl⟩ : syracuseStep 3850577 = 2887933) B2887933
theorem B3522973 : Blo 758332 3522973 := bstep (se 3 (by rfl) ⟨660557, by rfl⟩ : syracuseStep 3522973 = 1321115) B1321115
theorem B8667809 : Blo 758332 8667809 := bstep (se 2 (by rfl) ⟨3250428, by rfl⟩ : syracuseStep 8667809 = 6500857) B6500857
theorem B2442025 : Blo 758332 2442025 := bstep (se 2 (by rfl) ⟨915759, by rfl⟩ : syracuseStep 2442025 = 1831519) B1831519
theorem B3654467 : Blo 758332 3654467 := bstep (se 1 (by rfl) ⟨2740850, by rfl⟩ : syracuseStep 3654467 = 5481701) B5481701
theorem B3851387 : Blo 758332 3851387 := bstep (se 1 (by rfl) ⟨2888540, by rfl⟩ : syracuseStep 3851387 = 5777081) B5777081
theorem B2050427 : Blo 758332 2050427 := bstep (se 1 (by rfl) ⟨1537820, by rfl⟩ : syracuseStep 2050427 = 3075641) B3075641
theorem B1624873 : Blo 758332 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B1756009 : Blo 758332 1756009 := bstep (se 2 (by rfl) ⟨658503, by rfl⟩ : syracuseStep 1756009 = 1317007) B1317007
theorem B1625275 : Blo 758332 1625275 := bstep (se 1 (by rfl) ⟨1218956, by rfl⟩ : syracuseStep 1625275 = 2437913) B2437913
theorem B6507965 : Blo 758332 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B1920793 : Blo 758332 1920793 := bstep (se 2 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 1920793 = 1440595) B1440595
theorem B4378495 : Blo 758332 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B1822591 : Blo 758332 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B1626095 : Blo 758332 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B6934567 : Blo 758332 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B12964535 : Blo 758332 12964535 := bstep (se 1 (by rfl) ⟨9723401, by rfl⟩ : syracuseStep 12964535 = 19446803) B19446803
theorem B3658733 : Blo 758332 3658733 := bstep (se 3 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 3658733 = 1372025) B1372025
theorem B6247439 : Blo 758332 6247439 := bstep (se 1 (by rfl) ⟨4685579, by rfl⟩ : syracuseStep 6247439 = 9371159) B9371159
theorem B1627231 : Blo 758332 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B1169051 : Blo 758332 1169051 := bstep (se 1 (by rfl) ⟨876788, by rfl⟩ : syracuseStep 1169051 = 1753577) B1753577
theorem B3299143 : Blo 758332 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B1923041 : Blo 758332 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B1267849 : Blo 758332 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B1923385 : Blo 758332 1923385 := bstep (se 2 (by rfl) ⟨721269, by rfl⟩ : syracuseStep 1923385 = 1442539) B1442539
theorem B4872545 : Blo 758332 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B1825523 : Blo 758332 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B1825591 : Blo 758332 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B6478987 : Blo 758332 6478987 := bstep (se 1 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 6478987 = 9718481) B9718481
theorem B18538105 : Blo 758332 18538105 := bstep (se 2 (by rfl) ⟨6951789, by rfl⟩ : syracuseStep 18538105 = 13903579) B13903579
theorem B4218493 : Blo 758332 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B1138343 : Blo 758332 1138343 := bstep (se 1 (by rfl) ⟨853757, by rfl⟩ : syracuseStep 1138343 = 1707515) B1707515
theorem B6512339 : Blo 758332 6512339 := bstep (se 1 (by rfl) ⟨4884254, by rfl⟩ : syracuseStep 6512339 = 9768509) B9768509
theorem B4874003 : Blo 758332 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B1138463 : Blo 758332 1138463 := bstep (se 1 (by rfl) ⟨853847, by rfl⟩ : syracuseStep 1138463 = 1707695) B1707695
theorem B1138895 : Blo 758332 1138895 := bstep (se 1 (by rfl) ⟨854171, by rfl⟩ : syracuseStep 1138895 = 1708343) B1708343
theorem B1138943 : Blo 758332 1138943 := bstep (se 1 (by rfl) ⟨854207, by rfl⟩ : syracuseStep 1138943 = 1708415) B1708415
theorem B1237531 : Blo 758332 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B5857879 : Blo 758332 5857879 := bstep (se 1 (by rfl) ⟨4393409, by rfl⟩ : syracuseStep 5857879 = 8786819) B8786819
theorem B811687 : Blo 758332 811687 := bstep (se 1 (by rfl) ⟨608765, by rfl⟩ : syracuseStep 811687 = 1217531) B1217531
theorem B20800421 : Blo 758332 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B1139759 : Blo 758332 1139759 := bstep (se 1 (by rfl) ⟨854819, by rfl⟩ : syracuseStep 1139759 = 1709639) B1709639
theorem B1139879 : Blo 758332 1139879 := bstep (se 1 (by rfl) ⟨854909, by rfl⟩ : syracuseStep 1139879 = 1709819) B1709819
theorem B49407407 : Blo 758332 49407407 := bstep (se 1 (by rfl) ⟨37055555, by rfl⟩ : syracuseStep 49407407 = 74111111) B74111111
theorem B14607863 : Blo 758332 14607863 := bstep (se 1 (by rfl) ⟨10955897, by rfl⟩ : syracuseStep 14607863 = 21911795) B21911795
theorem B1140251 : Blo 758332 1140251 := bstep (se 1 (by rfl) ⟨855188, by rfl⟩ : syracuseStep 1140251 = 1710377) B1710377
theorem B1140635 : Blo 758332 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1140671 : Blo 758332 1140671 := bstep (se 1 (by rfl) ⟨855503, by rfl⟩ : syracuseStep 1140671 = 1711007) B1711007
theorem B1140857 : Blo 758332 1140857 := bstep (se 2 (by rfl) ⟨427821, by rfl⟩ : syracuseStep 1140857 = 855643) B855643
theorem B2058383 : Blo 758332 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B1141241 : Blo 758332 1141241 := bstep (se 2 (by rfl) ⟨427965, by rfl⟩ : syracuseStep 1141241 = 855931) B855931
theorem B1141295 : Blo 758332 1141295 := bstep (se 1 (by rfl) ⟨855971, by rfl⟩ : syracuseStep 1141295 = 1711943) B1711943
theorem B10414655 : Blo 758332 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B1141727 : Blo 758332 1141727 := bstep (se 1 (by rfl) ⟨856295, by rfl⟩ : syracuseStep 1141727 = 1712591) B1712591
theorem B1142171 : Blo 758332 1142171 := bstep (se 1 (by rfl) ⟨856628, by rfl⟩ : syracuseStep 1142171 = 1713257) B1713257
theorem B1142591 : Blo 758332 1142591 := bstep (se 1 (by rfl) ⟨856943, by rfl⟩ : syracuseStep 1142591 = 1713887) B1713887
theorem B3239767 : Blo 758332 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B1830827 : Blo 758332 1830827 := bstep (se 1 (by rfl) ⟨1373120, by rfl⟩ : syracuseStep 1830827 = 2746241) B2746241
theorem B1142777 : Blo 758332 1142777 := bstep (se 2 (by rfl) ⟨428541, by rfl⟩ : syracuseStep 1142777 = 857083) B857083
theorem B1929359 : Blo 758332 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B1143017 : Blo 758332 1143017 := bstep (se 2 (by rfl) ⟨428631, by rfl⟩ : syracuseStep 1143017 = 857263) B857263
theorem B1372423 : Blo 758332 1372423 := bstep (se 1 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 1372423 = 2058635) B2058635
theorem B1143143 : Blo 758332 1143143 := bstep (se 1 (by rfl) ⟨857357, by rfl⟩ : syracuseStep 1143143 = 1714715) B1714715
theorem B2290351 : Blo 758332 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B24671411 : Blo 758332 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B2881115 : Blo 758332 2881115 := bstep (se 1 (by rfl) ⟨2160836, by rfl⟩ : syracuseStep 2881115 = 4321673) B4321673
theorem B5470337 : Blo 758332 5470337 := bstep (se 2 (by rfl) ⟨2051376, by rfl⟩ : syracuseStep 5470337 = 4102753) B4102753
theorem B1439927 : Blo 758332 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B5765417 : Blo 758332 5765417 := bstep (se 2 (by rfl) ⟨2162031, by rfl⟩ : syracuseStep 5765417 = 4324063) B4324063
theorem B10975733 : Blo 758332 10975733 := bstep (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) B1028975
theorem B3242537 : Blo 758332 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B1407647 : Blo 758332 1407647 := bstep (se 1 (by rfl) ⟨1055735, by rfl⟩ : syracuseStep 1407647 = 2111471) B2111471
theorem B1440443 : Blo 758332 1440443 := bstep (se 1 (by rfl) ⟨1080332, by rfl⟩ : syracuseStep 1440443 = 2160665) B2160665
theorem B2161417 : Blo 758332 2161417 := bstep (se 2 (by rfl) ⟨810531, by rfl⟩ : syracuseStep 2161417 = 1621063) B1621063
theorem B3242911 : Blo 758332 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B1440679 : Blo 758332 1440679 := bstep (se 1 (by rfl) ⟨1080509, by rfl⟩ : syracuseStep 1440679 = 2161019) B2161019
theorem B19758275 : Blo 758332 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B2162305 : Blo 758332 2162305 := bstep (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) B1621729
theorem B4325021 : Blo 758332 4325021 := bstep (se 3 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 4325021 = 1621883) B1621883
theorem B2162351 : Blo 758332 2162351 := bstep (se 1 (by rfl) ⟨1621763, by rfl⟩ : syracuseStep 2162351 = 3243527) B3243527
theorem B2883833 : Blo 758332 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1442623 : Blo 758332 1442623 := bstep (se 1 (by rfl) ⟨1081967, by rfl⟩ : syracuseStep 1442623 = 2163935) B2163935
theorem B2885291 : Blo 758332 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B4393223 : Blo 758332 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B2165267 : Blo 758332 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B854815 : Blo 758332 854815 := bstep (se 1 (by rfl) ⟨641111, by rfl⟩ : syracuseStep 854815 = 1282223) B1282223
theorem B1444969 : Blo 758332 1444969 := bstep (se 2 (by rfl) ⟨541863, by rfl⟩ : syracuseStep 1444969 = 1083727) B1083727
theorem B4164959 : Blo 758332 4164959 := bstep (se 1 (by rfl) ⟨3123719, by rfl⟩ : syracuseStep 4164959 = 6247439) B6247439
theorem B2166497 : Blo 758332 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1282027 : Blo 758332 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B856255 : Blo 758332 856255 := bstep (se 1 (by rfl) ⟨642191, by rfl⟩ : syracuseStep 856255 = 1284383) B1284383
theorem B3248363 : Blo 758332 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B2167033 : Blo 758332 2167033 := bstep (se 2 (by rfl) ⟨812637, by rfl⟩ : syracuseStep 2167033 = 1625275) B1625275
theorem B3117469 : Blo 758332 3117469 := bstep (se 3 (by rfl) ⟨584525, by rfl⟩ : syracuseStep 3117469 = 1169051) B1169051
theorem B1217015 : Blo 758332 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B2888207 : Blo 758332 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B2561057 : Blo 758332 2561057 := bstep (se 2 (by rfl) ⟨960396, by rfl⟩ : syracuseStep 2561057 = 1920793) B1920793
theorem B758895 : Blo 758332 758895 := bstep (se 1 (by rfl) ⟨569171, by rfl⟩ : syracuseStep 758895 = 1138343) B1138343
theorem B5837993 : Blo 758332 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B1709225 : Blo 758332 1709225 := bstep (se 2 (by rfl) ⟨640959, by rfl⟩ : syracuseStep 1709225 = 1281919) B1281919
theorem B3249335 : Blo 758332 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B758975 : Blo 758332 758975 := bstep (se 1 (by rfl) ⟨569231, by rfl⟩ : syracuseStep 758975 = 1138463) B1138463
theorem B9246089 : Blo 758332 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B759263 : Blo 758332 759263 := bstep (se 1 (by rfl) ⟨569447, by rfl⟩ : syracuseStep 759263 = 1138895) B1138895
theorem B759295 : Blo 758332 759295 := bstep (se 1 (by rfl) ⟨569471, by rfl⟩ : syracuseStep 759295 = 1138943) B1138943
theorem B13866947 : Blo 758332 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B759839 : Blo 758332 759839 := bstep (se 1 (by rfl) ⟨569879, by rfl⟩ : syracuseStep 759839 = 1139759) B1139759
theorem B759919 : Blo 758332 759919 := bstep (se 1 (by rfl) ⟨569939, by rfl⟩ : syracuseStep 759919 = 1139879) B1139879
theorem B3053801 : Blo 758332 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B32938271 : Blo 758332 32938271 := bstep (se 1 (by rfl) ⟨24703703, by rfl⟩ : syracuseStep 32938271 = 49407407) B49407407
theorem B9738575 : Blo 758332 9738575 := bstep (se 1 (by rfl) ⟨7303931, by rfl⟩ : syracuseStep 9738575 = 14607863) B14607863
theorem B760167 : Blo 758332 760167 := bstep (se 1 (by rfl) ⟨570125, by rfl⟩ : syracuseStep 760167 = 1140251) B1140251
theorem B3250601 : Blo 758332 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B1710683 : Blo 758332 1710683 := bstep (se 1 (by rfl) ⟨1283012, by rfl⟩ : syracuseStep 1710683 = 2566025) B2566025
theorem B760423 : Blo 758332 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B760447 : Blo 758332 760447 := bstep (se 1 (by rfl) ⟨570335, by rfl⟩ : syracuseStep 760447 = 1140671) B1140671
theorem B760571 : Blo 758332 760571 := bstep (se 1 (by rfl) ⟨570428, by rfl⟩ : syracuseStep 760571 = 1140857) B1140857
theorem B2169595 : Blo 758332 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B2169641 : Blo 758332 2169641 := bstep (se 2 (by rfl) ⟨813615, by rfl⟩ : syracuseStep 2169641 = 1627231) B1627231
theorem B760827 : Blo 758332 760827 := bstep (se 1 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 760827 = 1141241) B1141241
theorem B760863 : Blo 758332 760863 := bstep (se 1 (by rfl) ⟨570647, by rfl⟩ : syracuseStep 760863 = 1141295) B1141295
theorem B21961853 : Blo 758332 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B3841181 : Blo 758332 3841181 := bstep (se 3 (by rfl) ⟨720221, by rfl⟩ : syracuseStep 3841181 = 1440443) B1440443
theorem B761151 : Blo 758332 761151 := bstep (se 1 (by rfl) ⟨570863, by rfl⟩ : syracuseStep 761151 = 1141727) B1141727
theorem B761447 : Blo 758332 761447 := bstep (se 1 (by rfl) ⟨571085, by rfl⟩ : syracuseStep 761447 = 1142171) B1142171
theorem B4398857 : Blo 758332 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B4333337 : Blo 758332 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B761727 : Blo 758332 761727 := bstep (se 1 (by rfl) ⟨571295, by rfl⟩ : syracuseStep 761727 = 1142591) B1142591
theorem B1220551 : Blo 758332 1220551 := bstep (se 1 (by rfl) ⟨915413, by rfl⟩ : syracuseStep 1220551 = 1830827) B1830827
theorem B761851 : Blo 758332 761851 := bstep (se 1 (by rfl) ⟨571388, by rfl⟩ : syracuseStep 761851 = 1142777) B1142777
theorem B1286239 : Blo 758332 1286239 := bstep (se 1 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 1286239 = 1929359) B1929359
theorem B762011 : Blo 758332 762011 := bstep (se 1 (by rfl) ⟨571508, by rfl⟩ : syracuseStep 762011 = 1143017) B1143017
theorem B762095 : Blo 758332 762095 := bstep (se 1 (by rfl) ⟨571571, by rfl⟩ : syracuseStep 762095 = 1143143) B1143143
theorem B2564513 : Blo 758332 2564513 := bstep (se 2 (by rfl) ⟨961692, by rfl⟩ : syracuseStep 2564513 = 1923385) B1923385
theorem B2564567 : Blo 758332 2564567 := bstep (se 1 (by rfl) ⟨1923425, by rfl⟩ : syracuseStep 2564567 = 3846851) B3846851
theorem B1712681 : Blo 758332 1712681 := bstep (se 2 (by rfl) ⟨642255, by rfl⟩ : syracuseStep 1712681 = 1284511) B1284511
theorem B1712987 : Blo 758332 1712987 := bstep (se 1 (by rfl) ⟨1284740, by rfl⟩ : syracuseStep 1712987 = 2569481) B2569481
theorem B2434121 : Blo 758332 2434121 := bstep (se 2 (by rfl) ⟨912795, by rfl⟩ : syracuseStep 2434121 = 1825591) B1825591
theorem B2565215 : Blo 758332 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B1713311 : Blo 758332 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B3646891 : Blo 758332 3646891 := bstep (se 1 (by rfl) ⟨2735168, by rfl⟩ : syracuseStep 3646891 = 5470337) B5470337
theorem B959951 : Blo 758332 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B3843611 : Blo 758332 3843611 := bstep (se 1 (by rfl) ⟨2882708, by rfl⟩ : syracuseStep 3843611 = 5765417) B5765417
theorem B8660519 : Blo 758332 8660519 := bstep (se 1 (by rfl) ⟨6495389, by rfl⟩ : syracuseStep 8660519 = 12990779) B12990779
theorem B7317155 : Blo 758332 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B1713959 : Blo 758332 1713959 := bstep (se 1 (by rfl) ⟨1285469, by rfl⟩ : syracuseStep 1713959 = 2570939) B2570939
theorem B1714337 : Blo 758332 1714337 := bstep (se 2 (by rfl) ⟨642876, by rfl⟩ : syracuseStep 1714337 = 1285753) B1285753
theorem B24717473 : Blo 758332 24717473 := bstep (se 2 (by rfl) ⟨9269052, by rfl⟩ : syracuseStep 24717473 = 18538105) B18538105
theorem B4336253 : Blo 758332 4336253 := bstep (se 3 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 4336253 = 1626095) B1626095
theorem B2567051 : Blo 758332 2567051 := bstep (se 1 (by rfl) ⟨1925288, by rfl⟩ : syracuseStep 2567051 = 3850577) B3850577
theorem B5778539 : Blo 758332 5778539 := bstep (se 1 (by rfl) ⟨4333904, by rfl⟩ : syracuseStep 5778539 = 8667809) B8667809
theorem B4697297 : Blo 758332 4697297 := bstep (se 2 (by rfl) ⟨1761486, by rfl⟩ : syracuseStep 4697297 = 3522973) B3522973
theorem B2436311 : Blo 758332 2436311 := bstep (se 1 (by rfl) ⟨1827233, by rfl⟩ : syracuseStep 2436311 = 3654467) B3654467
theorem B1650041 : Blo 758332 1650041 := bstep (se 2 (by rfl) ⟨618765, by rfl⟩ : syracuseStep 1650041 = 1237531) B1237531
theorem B6761861 : Blo 758332 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B961951 : Blo 758332 961951 := bstep (se 1 (by rfl) ⟨721463, by rfl⟩ : syracuseStep 961951 = 1442927) B1442927
theorem B2567591 : Blo 758332 2567591 := bstep (se 1 (by rfl) ⟨1925693, by rfl⟩ : syracuseStep 2567591 = 3851387) B3851387
theorem B7810505 : Blo 758332 7810505 := bstep (se 2 (by rfl) ⟨2928939, by rfl⟩ : syracuseStep 7810505 = 5857879) B5857879
theorem B3256033 : Blo 758332 3256033 := bstep (se 2 (by rfl) ⟨1221012, by rfl⟩ : syracuseStep 3256033 = 2442025) B2442025
theorem B3845879 : Blo 758332 3845879 := bstep (se 1 (by rfl) ⟨2884409, by rfl⟩ : syracuseStep 3845879 = 5768819) B5768819
theorem B962543 : Blo 758332 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B3846527 : Blo 758332 3846527 := bstep (se 1 (by rfl) ⟨2884895, by rfl⟩ : syracuseStep 3846527 = 5769791) B5769791
theorem B4338643 : Blo 758332 4338643 := bstep (se 1 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 4338643 = 6507965) B6507965
theorem B963839 : Blo 758332 963839 := bstep (se 1 (by rfl) ⟨722879, by rfl⟩ : syracuseStep 963839 = 1445759) B1445759
theorem B2733439 : Blo 758332 2733439 := bstep (se 1 (by rfl) ⟨2050079, by rfl⟩ : syracuseStep 2733439 = 4100159) B4100159
theorem B4339169 : Blo 758332 4339169 := bstep (se 2 (by rfl) ⟨1627188, by rfl⟩ : syracuseStep 4339169 = 3254377) B3254377
theorem B4929133 : Blo 758332 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B964543 : Blo 758332 964543 := bstep (se 1 (by rfl) ⟨723407, by rfl⟩ : syracuseStep 964543 = 1446815) B1446815
theorem B2439155 : Blo 758332 2439155 := bstep (se 1 (by rfl) ⟨1829366, by rfl⟩ : syracuseStep 2439155 = 3658733) B3658733
theorem B4864009 : Blo 758332 4864009 := bstep (se 2 (by rfl) ⟨1824003, by rfl⟩ : syracuseStep 4864009 = 3648007) B3648007
theorem B17315989 : Blo 758332 17315989 := bstep (se 6 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 17315989 = 811687) B811687
theorem B2341345 : Blo 758332 2341345 := bstep (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) B1756009
theorem B3848957 : Blo 758332 3848957 := bstep (se 3 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 3848957 = 1443359) B1443359
theorem B769007 : Blo 758332 769007 := bstep (se 1 (by rfl) ⟨576755, by rfl⟩ : syracuseStep 769007 = 1153511) B1153511
theorem B4341559 : Blo 758332 4341559 := bstep (se 1 (by rfl) ⟨3256169, by rfl⟩ : syracuseStep 4341559 = 6512339) B6512339
theorem B5783885 : Blo 758332 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B5489021 : Blo 758332 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B3850739 : Blo 758332 3850739 := bstep (se 1 (by rfl) ⟨2888054, by rfl⟩ : syracuseStep 3850739 = 5776109) B5776109
theorem B35178137 : Blo 758332 35178137 := bstep (se 2 (by rfl) ⟨13191801, by rfl⟩ : syracuseStep 35178137 = 26383603) B26383603
theorem B3852035 : Blo 758332 3852035 := bstep (se 1 (by rfl) ⟨2889026, by rfl⟩ : syracuseStep 3852035 = 5778053) B5778053
theorem B7785629 : Blo 758332 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B3853655 : Blo 758332 3853655 := bstep (se 1 (by rfl) ⟨2890241, by rfl⟩ : syracuseStep 3853655 = 5780483) B5780483
theorem B29248937 : Blo 758332 29248937 := bstep (se 2 (by rfl) ⟨10968351, by rfl⟩ : syracuseStep 29248937 = 21936703) B21936703
theorem B1920743 : Blo 758332 1920743 := bstep (se 1 (by rfl) ⟨1440557, by rfl⟩ : syracuseStep 1920743 = 2881115) B2881115
theorem B1920905 : Blo 758332 1920905 := bstep (se 2 (by rfl) ⟨720339, by rfl⟩ : syracuseStep 1920905 = 1440679) B1440679
theorem B8638649 : Blo 758332 8638649 := bstep (se 2 (by rfl) ⟨3239493, by rfl⟩ : syracuseStep 8638649 = 6478987) B6478987
theorem B938431 : Blo 758332 938431 := bstep (se 1 (by rfl) ⟨703823, by rfl⟩ : syracuseStep 938431 = 1407647) B1407647
theorem B9720485 : Blo 758332 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B5624657 : Blo 758332 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B3855275 : Blo 758332 3855275 := bstep (se 1 (by rfl) ⟨2891456, by rfl⟩ : syracuseStep 3855275 = 5782913) B5782913
theorem B1463561 : Blo 758332 1463561 := bstep (se 2 (by rfl) ⟨548835, by rfl⟩ : syracuseStep 1463561 = 1097671) B1097671
theorem B11097431 : Blo 758332 11097431 := bstep (se 1 (by rfl) ⟨8323073, by rfl⟩ : syracuseStep 11097431 = 16646147) B16646147
theorem B10933703 : Blo 758332 10933703 := bstep (se 1 (by rfl) ⟨8200277, by rfl⟩ : syracuseStep 10933703 = 16400555) B16400555
theorem B1922899 : Blo 758332 1922899 := bstep (se 1 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 1922899 = 2884349) B2884349
theorem B168450191 : Blo 758332 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B12343549 : Blo 758332 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B1137545 : Blo 758332 1137545 := bstep (se 2 (by rfl) ⟨426579, by rfl⟩ : syracuseStep 1137545 = 853159) B853159
theorem B1137575 : Blo 758332 1137575 := bstep (se 1 (by rfl) ⟨853181, by rfl⟩ : syracuseStep 1137575 = 1706363) B1706363
theorem B1366951 : Blo 758332 1366951 := bstep (se 1 (by rfl) ⟨1025213, by rfl⟩ : syracuseStep 1366951 = 2050427) B2050427
theorem B1137755 : Blo 758332 1137755 := bstep (se 1 (by rfl) ⟨853316, by rfl⟩ : syracuseStep 1137755 = 1706633) B1706633
theorem B1924307 : Blo 758332 1924307 := bstep (se 1 (by rfl) ⟨1443230, by rfl⟩ : syracuseStep 1924307 = 2886461) B2886461
theorem B1137947 : Blo 758332 1137947 := bstep (se 1 (by rfl) ⟨853460, by rfl⟩ : syracuseStep 1137947 = 1706921) B1706921
theorem B1138415 : Blo 758332 1138415 := bstep (se 1 (by rfl) ⟨853811, by rfl⟩ : syracuseStep 1138415 = 1707623) B1707623
theorem B41606945 : Blo 758332 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B1138601 : Blo 758332 1138601 := bstep (se 2 (by rfl) ⟨426975, by rfl⟩ : syracuseStep 1138601 = 853951) B853951
theorem B1138751 : Blo 758332 1138751 := bstep (se 1 (by rfl) ⟨854063, by rfl⟩ : syracuseStep 1138751 = 1708127) B1708127
theorem B1138985 : Blo 758332 1138985 := bstep (se 2 (by rfl) ⟨427119, by rfl⟩ : syracuseStep 1138985 = 854239) B854239
theorem B8643023 : Blo 758332 8643023 := bstep (se 1 (by rfl) ⟨6482267, by rfl⟩ : syracuseStep 8643023 = 12964535) B12964535
theorem B1139255 : Blo 758332 1139255 := bstep (se 1 (by rfl) ⟨854441, by rfl⟩ : syracuseStep 1139255 = 1708883) B1708883
theorem B1139615 : Blo 758332 1139615 := bstep (se 1 (by rfl) ⟨854711, by rfl⟩ : syracuseStep 1139615 = 1709423) B1709423
theorem B12968909 : Blo 758332 12968909 := bstep (se 3 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 12968909 = 4863341) B4863341
theorem B1926139 : Blo 758332 1926139 := bstep (se 1 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 1926139 = 2889209) B2889209
theorem B1139903 : Blo 758332 1139903 := bstep (se 1 (by rfl) ⟨854927, by rfl⟩ : syracuseStep 1139903 = 1709855) B1709855
theorem B12346663 : Blo 758332 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B1140047 : Blo 758332 1140047 := bstep (se 1 (by rfl) ⟨855035, by rfl⟩ : syracuseStep 1140047 = 1710071) B1710071
theorem B1140137 : Blo 758332 1140137 := bstep (se 2 (by rfl) ⟨427551, by rfl⟩ : syracuseStep 1140137 = 855103) B855103
theorem B1140287 : Blo 758332 1140287 := bstep (se 1 (by rfl) ⟨855215, by rfl⟩ : syracuseStep 1140287 = 1710431) B1710431
theorem B1140647 : Blo 758332 1140647 := bstep (se 1 (by rfl) ⟨855485, by rfl⟩ : syracuseStep 1140647 = 1710971) B1710971
theorem B1140767 : Blo 758332 1140767 := bstep (se 1 (by rfl) ⟨855575, by rfl⟩ : syracuseStep 1140767 = 1711151) B1711151
theorem B1665161 : Blo 758332 1665161 := bstep (se 2 (by rfl) ⟨624435, by rfl⟩ : syracuseStep 1665161 = 1248871) B1248871
theorem B11725049 : Blo 758332 11725049 := bstep (se 2 (by rfl) ⟨4396893, by rfl⟩ : syracuseStep 11725049 = 8793787) B8793787
theorem B1927547 : Blo 758332 1927547 := bstep (se 1 (by rfl) ⟨1445660, by rfl⟩ : syracuseStep 1927547 = 2891321) B2891321
theorem B4319689 : Blo 758332 4319689 := bstep (se 2 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 4319689 = 3239767) B3239767
theorem B1141223 : Blo 758332 1141223 := bstep (se 1 (by rfl) ⟨855917, by rfl⟩ : syracuseStep 1141223 = 1711835) B1711835
theorem B9726479 : Blo 758332 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B1141403 : Blo 758332 1141403 := bstep (se 1 (by rfl) ⟨856052, by rfl⟩ : syracuseStep 1141403 = 1712105) B1712105
theorem B1141625 : Blo 758332 1141625 := bstep (se 2 (by rfl) ⟨428109, by rfl⟩ : syracuseStep 1141625 = 856219) B856219
theorem B1829897 : Blo 758332 1829897 := bstep (se 2 (by rfl) ⟨686211, by rfl⟩ : syracuseStep 1829897 = 1372423) B1372423
theorem B1141871 : Blo 758332 1141871 := bstep (se 1 (by rfl) ⟨856403, by rfl⟩ : syracuseStep 1141871 = 1712807) B1712807
theorem B1141967 : Blo 758332 1141967 := bstep (se 1 (by rfl) ⟨856475, by rfl⟩ : syracuseStep 1141967 = 1712951) B1712951
theorem B1142087 : Blo 758332 1142087 := bstep (se 1 (by rfl) ⟨856565, by rfl⟩ : syracuseStep 1142087 = 1713131) B1713131
theorem B1142375 : Blo 758332 1142375 := bstep (se 1 (by rfl) ⟨856781, by rfl⟩ : syracuseStep 1142375 = 1713563) B1713563
theorem B9268951 : Blo 758332 9268951 := bstep (se 1 (by rfl) ⟨6951713, by rfl⟩ : syracuseStep 9268951 = 13903427) B13903427
theorem B1142759 : Blo 758332 1142759 := bstep (se 1 (by rfl) ⟨857069, by rfl⟩ : syracuseStep 1142759 = 1714139) B1714139
theorem B1142879 : Blo 758332 1142879 := bstep (se 1 (by rfl) ⟨857159, by rfl⟩ : syracuseStep 1142879 = 1714319) B1714319
theorem B1142939 : Blo 758332 1142939 := bstep (se 1 (by rfl) ⟨857204, by rfl⟩ : syracuseStep 1142939 = 1714409) B1714409
theorem B2191579 : Blo 758332 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B1929491 : Blo 758332 1929491 := bstep (se 1 (by rfl) ⟨1447118, by rfl⟩ : syracuseStep 1929491 = 2894237) B2894237
theorem B1143119 : Blo 758332 1143119 := bstep (se 1 (by rfl) ⟨857339, by rfl⟩ : syracuseStep 1143119 = 1714679) B1714679
theorem B6943103 : Blo 758332 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B1143209 : Blo 758332 1143209 := bstep (se 2 (by rfl) ⟨428703, by rfl⟩ : syracuseStep 1143209 = 857407) B857407
theorem B4682519 : Blo 758332 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B5468953 : Blo 758332 5468953 := bstep (se 2 (by rfl) ⟨2050857, by rfl⟩ : syracuseStep 5468953 = 4101715) B4101715
theorem B3076969 : Blo 758332 3076969 := bstep (se 2 (by rfl) ⟨1153863, by rfl⟩ : syracuseStep 3076969 = 2307727) B2307727
theorem B9270899 : Blo 758332 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B3897371 : Blo 758332 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B16447607 : Blo 758332 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B2881889 : Blo 758332 2881889 := bstep (se 2 (by rfl) ⟨1080708, by rfl⟩ : syracuseStep 2881889 = 2161417) B2161417
theorem B4323881 : Blo 758332 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B8223497 : Blo 758332 8223497 := bstep (se 2 (by rfl) ⟨3083811, by rfl⟩ : syracuseStep 8223497 = 6167623) B6167623
theorem B2161691 : Blo 758332 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B13172183 : Blo 758332 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1080811 : Blo 758332 1080811 := bstep (se 1 (by rfl) ⟨810608, by rfl⟩ : syracuseStep 1080811 = 1621217) B1621217
theorem B1736171 : Blo 758332 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B2883073 : Blo 758332 2883073 := bstep (se 2 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 2883073 = 2162305) B2162305
theorem B2883347 : Blo 758332 2883347 := bstep (se 1 (by rfl) ⟨2162510, by rfl⟩ : syracuseStep 2883347 = 4325021) B4325021
theorem B1441567 : Blo 758332 1441567 := bstep (se 1 (by rfl) ⟨1081175, by rfl⟩ : syracuseStep 1441567 = 2162351) B2162351
theorem B1443511 : Blo 758332 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B19499291 : Blo 758332 19499291 := bstep (se 1 (by rfl) ⟨14624468, by rfl⟩ : syracuseStep 19499291 = 29248937) B29248937
theorem B1444331 : Blo 758332 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B1280495 : Blo 758332 1280495 := bstep (se 1 (by rfl) ⟨960371, by rfl⟩ : syracuseStep 1280495 = 1920743) B1920743
theorem B1280603 : Blo 758332 1280603 := bstep (se 1 (by rfl) ⟨960452, by rfl⟩ : syracuseStep 1280603 = 1920905) B1920905
theorem B2165575 : Blo 758332 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B1707371 : Blo 758332 1707371 := bstep (se 1 (by rfl) ⟨1280528, by rfl⟩ : syracuseStep 1707371 = 2561057) B2561057
theorem B2559869 : Blo 758332 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B9244631 : Blo 758332 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B112300127 : Blo 758332 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B2035867 : Blo 758332 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B21958847 : Blo 758332 21958847 := bstep (se 1 (by rfl) ⟨16469135, by rfl⟩ : syracuseStep 21958847 = 32938271) B32938271
theorem B6492383 : Blo 758332 6492383 := bstep (se 1 (by rfl) ⟨4869287, by rfl⟩ : syracuseStep 6492383 = 9738575) B9738575
theorem B2167067 : Blo 758332 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B1446427 : Blo 758332 1446427 := bstep (se 1 (by rfl) ⟨1084820, by rfl⟩ : syracuseStep 1446427 = 2169641) B2169641
theorem B1282601 : Blo 758332 1282601 := bstep (se 2 (by rfl) ⟨480975, by rfl⟩ : syracuseStep 1282601 = 961951) B961951
theorem B758363 : Blo 758332 758363 := bstep (se 1 (by rfl) ⟨568772, by rfl⟩ : syracuseStep 758363 = 1137545) B1137545
theorem B758383 : Blo 758332 758383 := bstep (se 1 (by rfl) ⟨568787, by rfl⟩ : syracuseStep 758383 = 1137575) B1137575
theorem B758503 : Blo 758332 758503 := bstep (se 1 (by rfl) ⟨568877, by rfl⟩ : syracuseStep 758503 = 1137755) B1137755
theorem B2560787 : Blo 758332 2560787 := bstep (se 1 (by rfl) ⟨1920590, by rfl⟩ : syracuseStep 2560787 = 3841181) B3841181
theorem B1282871 : Blo 758332 1282871 := bstep (se 1 (by rfl) ⟨962153, by rfl⟩ : syracuseStep 1282871 = 1924307) B1924307
theorem B758631 : Blo 758332 758631 := bstep (se 1 (by rfl) ⟨568973, by rfl⟩ : syracuseStep 758631 = 1137947) B1137947
theorem B12358601 : Blo 758332 12358601 := bstep (se 2 (by rfl) ⟨4634475, by rfl⟩ : syracuseStep 12358601 = 9268951) B9268951
theorem B758943 : Blo 758332 758943 := bstep (se 1 (by rfl) ⟨569207, by rfl⟩ : syracuseStep 758943 = 1138415) B1138415
theorem B2888891 : Blo 758332 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B759067 : Blo 758332 759067 := bstep (se 1 (by rfl) ⟨569300, by rfl⟩ : syracuseStep 759067 = 1138601) B1138601
theorem B1709369 : Blo 758332 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B759167 : Blo 758332 759167 := bstep (se 1 (by rfl) ⟨569375, by rfl⟩ : syracuseStep 759167 = 1138751) B1138751
theorem B759323 : Blo 758332 759323 := bstep (se 1 (by rfl) ⟨569492, by rfl⟩ : syracuseStep 759323 = 1138985) B1138985
theorem B1709675 : Blo 758332 1709675 := bstep (se 1 (by rfl) ⟨1282256, by rfl⟩ : syracuseStep 1709675 = 2564513) B2564513
theorem B1709711 : Blo 758332 1709711 := bstep (se 1 (by rfl) ⟨1282283, by rfl⟩ : syracuseStep 1709711 = 2564567) B2564567
theorem B2889377 : Blo 758332 2889377 := bstep (se 2 (by rfl) ⟨1083516, by rfl⟩ : syracuseStep 2889377 = 2167033) B2167033
theorem B759503 : Blo 758332 759503 := bstep (se 1 (by rfl) ⟨569627, by rfl⟩ : syracuseStep 759503 = 1139255) B1139255
theorem B759743 : Blo 758332 759743 := bstep (se 1 (by rfl) ⟨569807, by rfl⟩ : syracuseStep 759743 = 1139615) B1139615
theorem B1710143 : Blo 758332 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B759935 : Blo 758332 759935 := bstep (se 1 (by rfl) ⟨569951, by rfl⟩ : syracuseStep 759935 = 1139903) B1139903
theorem B760031 : Blo 758332 760031 := bstep (se 1 (by rfl) ⟨570023, by rfl⟩ : syracuseStep 760031 = 1140047) B1140047
theorem B760091 : Blo 758332 760091 := bstep (se 1 (by rfl) ⟨570068, by rfl⟩ : syracuseStep 760091 = 1140137) B1140137
theorem B2562407 : Blo 758332 2562407 := bstep (se 1 (by rfl) ⟨1921805, by rfl⟩ : syracuseStep 2562407 = 3843611) B3843611
theorem B5773679 : Blo 758332 5773679 := bstep (se 1 (by rfl) ⟨4330259, by rfl⟩ : syracuseStep 5773679 = 8660519) B8660519
theorem B760191 : Blo 758332 760191 := bstep (se 1 (by rfl) ⟨570143, by rfl⟩ : syracuseStep 760191 = 1140287) B1140287
theorem B4102625 : Blo 758332 4102625 := bstep (se 2 (by rfl) ⟨1538484, by rfl⟩ : syracuseStep 4102625 = 3076969) B3076969
theorem B760431 : Blo 758332 760431 := bstep (se 1 (by rfl) ⟨570323, by rfl⟩ : syracuseStep 760431 = 1140647) B1140647
theorem B760511 : Blo 758332 760511 := bstep (se 1 (by rfl) ⟨570383, by rfl⟩ : syracuseStep 760511 = 1140767) B1140767
theorem B1285031 : Blo 758332 1285031 := bstep (se 1 (by rfl) ⟨963773, by rfl⟩ : syracuseStep 1285031 = 1927547) B1927547
theorem B760815 : Blo 758332 760815 := bstep (se 1 (by rfl) ⟨570611, by rfl⟩ : syracuseStep 760815 = 1141223) B1141223
theorem B2890835 : Blo 758332 2890835 := bstep (se 1 (by rfl) ⟨2168126, by rfl⟩ : syracuseStep 2890835 = 4336253) B4336253
theorem B760935 : Blo 758332 760935 := bstep (se 1 (by rfl) ⟨570701, by rfl⟩ : syracuseStep 760935 = 1141403) B1141403
theorem B3644585 : Blo 758332 3644585 := bstep (se 2 (by rfl) ⟨1366719, by rfl⟩ : syracuseStep 3644585 = 2733439) B2733439
theorem B761083 : Blo 758332 761083 := bstep (se 1 (by rfl) ⟨570812, by rfl⟩ : syracuseStep 761083 = 1141625) B1141625
theorem B1711367 : Blo 758332 1711367 := bstep (se 1 (by rfl) ⟨1283525, by rfl⟩ : syracuseStep 1711367 = 2567051) B2567051
theorem B1219931 : Blo 758332 1219931 := bstep (se 1 (by rfl) ⟨914948, by rfl⟩ : syracuseStep 1219931 = 1829897) B1829897
theorem B761247 : Blo 758332 761247 := bstep (se 1 (by rfl) ⟨570935, by rfl⟩ : syracuseStep 761247 = 1141871) B1141871
theorem B761311 : Blo 758332 761311 := bstep (se 1 (by rfl) ⟨570983, by rfl⟩ : syracuseStep 761311 = 1141967) B1141967
theorem B761391 : Blo 758332 761391 := bstep (se 1 (by rfl) ⟨571043, by rfl⟩ : syracuseStep 761391 = 1142087) B1142087
theorem B1711727 : Blo 758332 1711727 := bstep (se 1 (by rfl) ⟨1283795, by rfl⟩ : syracuseStep 1711727 = 2567591) B2567591
theorem B761583 : Blo 758332 761583 := bstep (se 1 (by rfl) ⟨571187, by rfl⟩ : syracuseStep 761583 = 1142375) B1142375
theorem B2563865 : Blo 758332 2563865 := bstep (se 2 (by rfl) ⟨961449, by rfl⟩ : syracuseStep 2563865 = 1922899) B1922899
theorem B2563919 : Blo 758332 2563919 := bstep (se 1 (by rfl) ⟨1922939, by rfl⟩ : syracuseStep 2563919 = 3845879) B3845879
theorem B1286057 : Blo 758332 1286057 := bstep (se 2 (by rfl) ⟨482271, by rfl⟩ : syracuseStep 1286057 = 964543) B964543
theorem B761839 : Blo 758332 761839 := bstep (se 1 (by rfl) ⟨571379, by rfl⟩ : syracuseStep 761839 = 1142759) B1142759
theorem B761919 : Blo 758332 761919 := bstep (se 1 (by rfl) ⟨571439, by rfl⟩ : syracuseStep 761919 = 1142879) B1142879
theorem B761959 : Blo 758332 761959 := bstep (se 1 (by rfl) ⟨571469, by rfl⟩ : syracuseStep 761959 = 1142939) B1142939
theorem B1286327 : Blo 758332 1286327 := bstep (se 1 (by rfl) ⟨964745, by rfl⟩ : syracuseStep 1286327 = 1929491) B1929491
theorem B762079 : Blo 758332 762079 := bstep (se 1 (by rfl) ⟨571559, by rfl⟩ : syracuseStep 762079 = 1143119) B1143119
theorem B2564351 : Blo 758332 2564351 := bstep (se 1 (by rfl) ⟨1923263, by rfl⟩ : syracuseStep 2564351 = 3846527) B3846527
theorem B4628735 : Blo 758332 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B762139 : Blo 758332 762139 := bstep (se 1 (by rfl) ⟨571604, by rfl⟩ : syracuseStep 762139 = 1143209) B1143209
theorem B16458065 : Blo 758332 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B3121679 : Blo 758332 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B3121793 : Blo 758332 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B2892779 : Blo 758332 2892779 := bstep (se 1 (by rfl) ⟨2169584, by rfl⟩ : syracuseStep 2892779 = 4339169) B4339169
theorem B2892793 : Blo 758332 2892793 := bstep (se 2 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 2892793 = 2169595) B2169595
theorem B2598247 : Blo 758332 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B2565971 : Blo 758332 2565971 := bstep (se 1 (by rfl) ⟨1924478, by rfl⟩ : syracuseStep 2565971 = 3848957) B3848957
theorem B5482331 : Blo 758332 5482331 := bstep (se 1 (by rfl) ⟨4111748, by rfl⟩ : syracuseStep 5482331 = 8223497) B8223497
theorem B3844097 : Blo 758332 3844097 := bstep (se 2 (by rfl) ⟨1441536, by rfl⟩ : syracuseStep 3844097 = 2883073) B2883073
theorem B1157447 : Blo 758332 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B2566781 : Blo 758332 2566781 := bstep (se 3 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 2566781 = 962543) B962543
theorem B1714985 : Blo 758332 1714985 := bstep (se 2 (by rfl) ⟨643119, by rfl⟩ : syracuseStep 1714985 = 1286239) B1286239
theorem B2567159 : Blo 758332 2567159 := bstep (se 1 (by rfl) ⟨1925369, by rfl⟩ : syracuseStep 2567159 = 3850739) B3850739
theorem B2568023 : Blo 758332 2568023 := bstep (se 1 (by rfl) ⟨1926017, by rfl⟩ : syracuseStep 2568023 = 3852035) B3852035
theorem B2568185 : Blo 758332 2568185 := bstep (se 2 (by rfl) ⟨963069, by rfl⟩ : syracuseStep 2568185 = 1926139) B1926139
theorem B2928815 : Blo 758332 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B16462217 : Blo 758332 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B4862521 : Blo 758332 4862521 := bstep (se 2 (by rfl) ⟨1823445, by rfl⟩ : syracuseStep 4862521 = 3646891) B3646891
theorem B5190419 : Blo 758332 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B2569103 : Blo 758332 2569103 := bstep (se 1 (by rfl) ⟨1926827, by rfl⟩ : syracuseStep 2569103 = 3853655) B3853655
theorem B369407765 : Blo 758332 369407765 := bstep (se 6 (by rfl) ⟨8657994, by rfl⟩ : syracuseStep 369407765 = 17315989) B17315989
theorem B8664893 : Blo 758332 8664893 := bstep (se 3 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 8664893 = 3249335) B3249335
theorem B3749771 : Blo 758332 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B2570183 : Blo 758332 2570183 := bstep (se 1 (by rfl) ⟨1927637, by rfl⟩ : syracuseStep 2570183 = 3855275) B3855275
theorem B2570237 : Blo 758332 2570237 := bstep (se 3 (by rfl) ⟨481919, by rfl⟩ : syracuseStep 2570237 = 963839) B963839
theorem B7289135 : Blo 758332 7289135 := bstep (se 1 (by rfl) ⟨5466851, by rfl⟩ : syracuseStep 7289135 = 10933703) B10933703
theorem B24656237 : Blo 758332 24656237 := bstep (se 3 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 24656237 = 9246089) B9246089
theorem B19512413 : Blo 758332 19512413 := bstep (se 3 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 19512413 = 7317155) B7317155
theorem B4341377 : Blo 758332 4341377 := bstep (se 2 (by rfl) ⟨1628016, by rfl⟩ : syracuseStep 4341377 = 3256033) B3256033
theorem B2932571 : Blo 758332 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B27737963 : Blo 758332 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B1622747 : Blo 758332 1622747 := bstep (se 1 (by rfl) ⟨1217060, by rfl⟩ : syracuseStep 1622747 = 2434121) B2434121
theorem B7291937 : Blo 758332 7291937 := bstep (se 2 (by rfl) ⟨2734476, by rfl⟩ : syracuseStep 7291937 = 5468953) B5468953
theorem B5784857 : Blo 758332 5784857 := bstep (se 2 (by rfl) ⟨2169321, by rfl⟩ : syracuseStep 5784857 = 4338643) B4338643
theorem B7816699 : Blo 758332 7816699 := bstep (se 1 (by rfl) ⟨5862524, by rfl⟩ : syracuseStep 7816699 = 11725049) B11725049
theorem B3852359 : Blo 758332 3852359 := bstep (se 1 (by rfl) ⟨2889269, by rfl⟩ : syracuseStep 3852359 = 5778539) B5778539
theorem B3131531 : Blo 758332 3131531 := bstep (se 1 (by rfl) ⟨2348648, by rfl⟩ : syracuseStep 3131531 = 4697297) B4697297
theorem B1624207 : Blo 758332 1624207 := bstep (se 1 (by rfl) ⟨1218155, by rfl⟩ : syracuseStep 1624207 = 2436311) B2436311
theorem B6572177 : Blo 758332 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B1100027 : Blo 758332 1100027 := bstep (se 1 (by rfl) ⟨825020, by rfl⟩ : syracuseStep 1100027 = 1650041) B1650041
theorem B4507907 : Blo 758332 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B2050685 : Blo 758332 2050685 := bstep (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) B769007
theorem B6180599 : Blo 758332 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B1822601 : Blo 758332 1822601 := bstep (se 2 (by rfl) ⟨683475, by rfl⟩ : syracuseStep 1822601 = 1366951) B1366951
theorem B1626103 : Blo 758332 1626103 := bstep (se 1 (by rfl) ⟨1219577, by rfl⟩ : syracuseStep 1626103 = 2439155) B2439155
theorem B10965071 : Blo 758332 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B1921259 : Blo 758332 1921259 := bstep (se 1 (by rfl) ⟨1440944, by rfl⟩ : syracuseStep 1921259 = 2881889) B2881889
theorem B6509605 : Blo 758332 6509605 := bstep (se 4 (by rfl) ⟨610275, by rfl⟩ : syracuseStep 6509605 = 1220551) B1220551
theorem B1922089 : Blo 758332 1922089 := bstep (se 2 (by rfl) ⟨720783, by rfl⟩ : syracuseStep 1922089 = 1441567) B1441567
theorem B5788745 : Blo 758332 5788745 := bstep (se 2 (by rfl) ⟨2170779, by rfl⟩ : syracuseStep 5788745 = 4341559) B4341559
theorem B1922231 : Blo 758332 1922231 := bstep (se 1 (by rfl) ⟨1441673, by rfl⟩ : syracuseStep 1922231 = 2883347) B2883347
theorem B1922555 : Blo 758332 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B3855923 : Blo 758332 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B3659347 : Blo 758332 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B1923497 : Blo 758332 1923497 := bstep (se 2 (by rfl) ⟨721311, by rfl⟩ : syracuseStep 1923497 = 1442623) B1442623
theorem B23452091 : Blo 758332 23452091 := bstep (se 1 (by rfl) ⟨17589068, by rfl⟩ : syracuseStep 23452091 = 35178137) B35178137
theorem B1923527 : Blo 758332 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B11688421 : Blo 758332 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B2776639 : Blo 758332 2776639 := bstep (se 1 (by rfl) ⟨2082479, by rfl⟩ : syracuseStep 2776639 = 4164959) B4164959
theorem B5004965 : Blo 758332 5004965 := bstep (se 4 (by rfl) ⟨469215, by rfl⟩ : syracuseStep 5004965 = 938431) B938431
theorem B5759099 : Blo 758332 5759099 := bstep (se 1 (by rfl) ⟨4319324, by rfl⟩ : syracuseStep 5759099 = 8638649) B8638649
theorem B811343 : Blo 758332 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B1925471 : Blo 758332 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B6480323 : Blo 758332 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B5759585 : Blo 758332 5759585 := bstep (se 2 (by rfl) ⟨2159844, by rfl⟩ : syracuseStep 5759585 = 4319689) B4319689
theorem B3891995 : Blo 758332 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B1139483 : Blo 758332 1139483 := bstep (se 1 (by rfl) ⟨854612, by rfl⟩ : syracuseStep 1139483 = 1709225) B1709225
theorem B975707 : Blo 758332 975707 := bstep (se 1 (by rfl) ⟨731780, by rfl⟩ : syracuseStep 975707 = 1463561) B1463561
theorem B7398287 : Blo 758332 7398287 := bstep (se 1 (by rfl) ⟨5548715, by rfl⟩ : syracuseStep 7398287 = 11097431) B11097431
theorem B1139753 : Blo 758332 1139753 := bstep (se 2 (by rfl) ⟨427407, by rfl⟩ : syracuseStep 1139753 = 854815) B854815
theorem B1926625 : Blo 758332 1926625 := bstep (se 2 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 1926625 = 1444969) B1444969
theorem B1140455 : Blo 758332 1140455 := bstep (se 1 (by rfl) ⟨855341, by rfl⟩ : syracuseStep 1140455 = 1710683) B1710683
theorem B14641235 : Blo 758332 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B1141673 : Blo 758332 1141673 := bstep (se 2 (by rfl) ⟨428127, by rfl⟩ : syracuseStep 1141673 = 856255) B856255
theorem B5762015 : Blo 758332 5762015 := bstep (se 1 (by rfl) ⟨4321511, by rfl⟩ : syracuseStep 5762015 = 8643023) B8643023
theorem B1141787 : Blo 758332 1141787 := bstep (se 1 (by rfl) ⟨856340, by rfl⟩ : syracuseStep 1141787 = 1712681) B1712681
theorem B4156625 : Blo 758332 4156625 := bstep (se 2 (by rfl) ⟨1558734, by rfl⟩ : syracuseStep 4156625 = 3117469) B3117469
theorem B1141991 : Blo 758332 1141991 := bstep (se 1 (by rfl) ⟨856493, by rfl⟩ : syracuseStep 1141991 = 1712987) B1712987
theorem B8645939 : Blo 758332 8645939 := bstep (se 1 (by rfl) ⟨6484454, by rfl⟩ : syracuseStep 8645939 = 12968909) B12968909
theorem B1142207 : Blo 758332 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B1142639 : Blo 758332 1142639 := bstep (se 1 (by rfl) ⟨856979, by rfl⟩ : syracuseStep 1142639 = 1713959) B1713959
theorem B1110107 : Blo 758332 1110107 := bstep (se 1 (by rfl) ⟨832580, by rfl⟩ : syracuseStep 1110107 = 1665161) B1665161
theorem B1142891 : Blo 758332 1142891 := bstep (se 1 (by rfl) ⟨857168, by rfl⟩ : syracuseStep 1142891 = 1714337) B1714337
theorem B16478315 : Blo 758332 16478315 := bstep (se 1 (by rfl) ⟨12358736, by rfl⟩ : syracuseStep 16478315 = 24717473) B24717473
theorem B6484319 : Blo 758332 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B5207003 : Blo 758332 5207003 := bstep (se 1 (by rfl) ⟨3905252, by rfl⟩ : syracuseStep 5207003 = 7810505) B7810505
theorem B6485345 : Blo 758332 6485345 := bstep (se 2 (by rfl) ⟨2432004, by rfl⟩ : syracuseStep 6485345 = 4864009) B4864009
theorem B2882587 : Blo 758332 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B1441081 : Blo 758332 1441081 := bstep (se 2 (by rfl) ⟨540405, by rfl⟩ : syracuseStep 1441081 = 1080811) B1080811
theorem B1441127 : Blo 758332 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B8781455 : Blo 758332 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B1081831 : Blo 758332 1081831 := bstep (se 1 (by rfl) ⟨811373, by rfl⟩ : syracuseStep 1081831 = 1622747) B1622747
theorem B2163581 : Blo 758332 2163581 := bstep (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) B811343
theorem B853663 : Blo 758332 853663 := bstep (se 1 (by rfl) ⟨640247, by rfl⟩ : syracuseStep 853663 = 1280495) B1280495
theorem B853735 : Blo 758332 853735 := bstep (se 1 (by rfl) ⟨640301, by rfl⟩ : syracuseStep 853735 = 1280603) B1280603
theorem B10422265 : Blo 758332 10422265 := bstep (se 2 (by rfl) ⟨3908349, by rfl⟩ : syracuseStep 10422265 = 7816699) B7816699
theorem B1706579 : Blo 758332 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B1215067 : Blo 758332 1215067 := bstep (se 1 (by rfl) ⟨911300, by rfl⟩ : syracuseStep 1215067 = 1822601) B1822601
theorem B6163087 : Blo 758332 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B7310047 : Blo 758332 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B4328255 : Blo 758332 4328255 := bstep (se 1 (by rfl) ⟨3246191, by rfl⟩ : syracuseStep 4328255 = 6492383) B6492383
theorem B1280839 : Blo 758332 1280839 := bstep (se 1 (by rfl) ⟨960629, by rfl⟩ : syracuseStep 1280839 = 1921259) B1921259
theorem B1444711 : Blo 758332 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B2165609 : Blo 758332 2165609 := bstep (se 2 (by rfl) ⟨812103, by rfl⟩ : syracuseStep 2165609 = 1624207) B1624207
theorem B855067 : Blo 758332 855067 := bstep (se 1 (by rfl) ⟨641300, by rfl⟩ : syracuseStep 855067 = 1282601) B1282601
theorem B1707191 : Blo 758332 1707191 := bstep (se 1 (by rfl) ⟨1280393, by rfl⟩ : syracuseStep 1707191 = 2560787) B2560787
theorem B855247 : Blo 758332 855247 := bstep (se 1 (by rfl) ⟨641435, by rfl⟩ : syracuseStep 855247 = 1282871) B1282871
theorem B1281487 : Blo 758332 1281487 := bstep (se 1 (by rfl) ⟨961115, by rfl⟩ : syracuseStep 1281487 = 1922231) B1922231
theorem B1281703 : Blo 758332 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B2887433 : Blo 758332 2887433 := bstep (se 2 (by rfl) ⟨1082787, by rfl⟩ : syracuseStep 2887433 = 2165575) B2165575
theorem B1708271 : Blo 758332 1708271 := bstep (se 1 (by rfl) ⟨1281203, by rfl⟩ : syracuseStep 1708271 = 2562407) B2562407
theorem B1282331 : Blo 758332 1282331 := bstep (se 1 (by rfl) ⟨961748, by rfl⟩ : syracuseStep 1282331 = 1923497) B1923497
theorem B15634727 : Blo 758332 15634727 := bstep (se 1 (by rfl) ⟨11726045, by rfl⟩ : syracuseStep 15634727 = 23452091) B23452091
theorem B1282351 : Blo 758332 1282351 := bstep (se 1 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 1282351 = 1923527) B1923527
theorem B856687 : Blo 758332 856687 := bstep (se 1 (by rfl) ⟨642515, by rfl⟩ : syracuseStep 856687 = 1285031) B1285031
theorem B2429723 : Blo 758332 2429723 := bstep (se 1 (by rfl) ⟨1822292, by rfl⟩ : syracuseStep 2429723 = 3644585) B3644585
theorem B9999389 : Blo 758332 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B1709243 : Blo 758332 1709243 := bstep (se 1 (by rfl) ⟨1281932, by rfl⟩ : syracuseStep 1709243 = 2563865) B2563865
theorem B1709279 : Blo 758332 1709279 := bstep (se 1 (by rfl) ⟨1281959, by rfl⟩ : syracuseStep 1709279 = 2563919) B2563919
theorem B857371 : Blo 758332 857371 := bstep (se 1 (by rfl) ⟨643028, by rfl⟩ : syracuseStep 857371 = 1286057) B1286057
theorem B2168137 : Blo 758332 2168137 := bstep (se 2 (by rfl) ⟨813051, by rfl⟩ : syracuseStep 2168137 = 1626103) B1626103
theorem B3839399 : Blo 758332 3839399 := bstep (se 1 (by rfl) ⟨2879549, by rfl⟩ : syracuseStep 3839399 = 5759099) B5759099
theorem B857551 : Blo 758332 857551 := bstep (se 1 (by rfl) ⟨643163, by rfl⟩ : syracuseStep 857551 = 1286327) B1286327
theorem B1709567 : Blo 758332 1709567 := bstep (se 1 (by rfl) ⟨1282175, by rfl⟩ : syracuseStep 1709567 = 2564351) B2564351
theorem B3085823 : Blo 758332 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B1283647 : Blo 758332 1283647 := bstep (se 1 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 1283647 = 1925471) B1925471
theorem B3839723 : Blo 758332 3839723 := bstep (se 1 (by rfl) ⟨2879792, by rfl⟩ : syracuseStep 3839723 = 5759585) B5759585
theorem B2594663 : Blo 758332 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B759655 : Blo 758332 759655 := bstep (se 1 (by rfl) ⟨569741, by rfl⟩ : syracuseStep 759655 = 1139483) B1139483
theorem B759835 : Blo 758332 759835 := bstep (se 1 (by rfl) ⟨569876, by rfl⟩ : syracuseStep 759835 = 1139753) B1139753
theorem B3086525 : Blo 758332 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B760303 : Blo 758332 760303 := bstep (se 1 (by rfl) ⟨570227, by rfl⟩ : syracuseStep 760303 = 1140455) B1140455
theorem B1710647 : Blo 758332 1710647 := bstep (se 1 (by rfl) ⟨1282985, by rfl⟩ : syracuseStep 1710647 = 2565971) B2565971
theorem B2562731 : Blo 758332 2562731 := bstep (se 1 (by rfl) ⟨1922048, by rfl⟩ : syracuseStep 2562731 = 3844097) B3844097
theorem B2562785 : Blo 758332 2562785 := bstep (se 2 (by rfl) ⟨961044, by rfl⟩ : syracuseStep 2562785 = 1922089) B1922089
theorem B1711187 : Blo 758332 1711187 := bstep (se 1 (by rfl) ⟨1283390, by rfl⟩ : syracuseStep 1711187 = 2566781) B2566781
theorem B761115 : Blo 758332 761115 := bstep (se 1 (by rfl) ⟨570836, by rfl⟩ : syracuseStep 761115 = 1141673) B1141673
theorem B3841343 : Blo 758332 3841343 := bstep (se 1 (by rfl) ⟨2881007, by rfl⟩ : syracuseStep 3841343 = 5762015) B5762015
theorem B1711439 : Blo 758332 1711439 := bstep (se 1 (by rfl) ⟨1283579, by rfl⟩ : syracuseStep 1711439 = 2567159) B2567159
theorem B761191 : Blo 758332 761191 := bstep (se 1 (by rfl) ⟨570893, by rfl⟩ : syracuseStep 761191 = 1141787) B1141787
theorem B761327 : Blo 758332 761327 := bstep (se 1 (by rfl) ⟨570995, by rfl⟩ : syracuseStep 761327 = 1141991) B1141991
theorem B761471 : Blo 758332 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B1712015 : Blo 758332 1712015 := bstep (se 1 (by rfl) ⟨1284011, by rfl⟩ : syracuseStep 1712015 = 2568023) B2568023
theorem B761759 : Blo 758332 761759 := bstep (se 1 (by rfl) ⟨571319, by rfl⟩ : syracuseStep 761759 = 1142639) B1142639
theorem B1712123 : Blo 758332 1712123 := bstep (se 1 (by rfl) ⟨1284092, by rfl⟩ : syracuseStep 1712123 = 2568185) B2568185
theorem B761927 : Blo 758332 761927 := bstep (se 1 (by rfl) ⟨571445, by rfl⟩ : syracuseStep 761927 = 1142891) B1142891
theorem B10985543 : Blo 758332 10985543 := bstep (se 1 (by rfl) ⟨8239157, by rfl⟩ : syracuseStep 10985543 = 16478315) B16478315
theorem B1712735 : Blo 758332 1712735 := bstep (se 1 (by rfl) ⟨1284551, by rfl⟩ : syracuseStep 1712735 = 2569103) B2569103
theorem B5776595 : Blo 758332 5776595 := bstep (se 1 (by rfl) ⟨4332446, by rfl⟩ : syracuseStep 5776595 = 8664893) B8664893
theorem B1713455 : Blo 758332 1713455 := bstep (se 1 (by rfl) ⟨1285091, by rfl⟩ : syracuseStep 1713455 = 2570183) B2570183
theorem B1713491 : Blo 758332 1713491 := bstep (se 1 (by rfl) ⟨1285118, by rfl⟩ : syracuseStep 1713491 = 2570237) B2570237
theorem B3843449 : Blo 758332 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B4859423 : Blo 758332 4859423 := bstep (se 1 (by rfl) ⟨3644567, by rfl⟩ : syracuseStep 4859423 = 7289135) B7289135
theorem B960751 : Blo 758332 960751 := bstep (se 1 (by rfl) ⟨720563, by rfl⟩ : syracuseStep 960751 = 1441127) B1441127
theorem B2894251 : Blo 758332 2894251 := bstep (se 1 (by rfl) ⟨2170688, by rfl⟩ : syracuseStep 2894251 = 4341377) B4341377
theorem B18491975 : Blo 758332 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B2960285 : Blo 758332 2960285 := bstep (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) B1110107
theorem B4861291 : Blo 758332 4861291 := bstep (se 1 (by rfl) ⟨3645968, by rfl⟩ : syracuseStep 4861291 = 7291937) B7291937
theorem B2568239 : Blo 758332 2568239 := bstep (se 1 (by rfl) ⟨1926179, by rfl⟩ : syracuseStep 2568239 = 3852359) B3852359
theorem B2568833 : Blo 758332 2568833 := bstep (se 2 (by rfl) ⟨963312, by rfl⟩ : syracuseStep 2568833 = 1926625) B1926625
theorem B8239067 : Blo 758332 8239067 := bstep (se 1 (by rfl) ⟨6179300, by rfl⟩ : syracuseStep 8239067 = 12358601) B12358601
theorem B2570615 : Blo 758332 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B3849119 : Blo 758332 3849119 := bstep (se 1 (by rfl) ⟨2886839, by rfl⟩ : syracuseStep 3849119 = 5773679) B5773679
theorem B2735083 : Blo 758332 2735083 := bstep (se 1 (by rfl) ⟨2051312, by rfl⟩ : syracuseStep 2735083 = 4102625) B4102625
theorem B2081119 : Blo 758332 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B4932191 : Blo 758332 4932191 := bstep (se 1 (by rfl) ⟨3699143, by rfl⟩ : syracuseStep 4932191 = 7398287) B7398287
theorem B2933405 : Blo 758332 2933405 := bstep (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) B1100027
theorem B3654887 : Blo 758332 3654887 := bstep (se 1 (by rfl) ⟨2741165, by rfl⟩ : syracuseStep 3654887 = 5482331) B5482331
theorem B3851549 : Blo 758332 3851549 := bstep (se 3 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 3851549 = 1444331) B1444331
theorem B2771083 : Blo 758332 2771083 := bstep (se 1 (by rfl) ⟨2078312, by rfl⟩ : syracuseStep 2771083 = 4156625) B4156625
theorem B1952543 : Blo 758332 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B3460279 : Blo 758332 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B15584561 : Blo 758332 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B10407541 : Blo 758332 10407541 := bstep (se 5 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 10407541 = 975707) B975707
theorem B246271843 : Blo 758332 246271843 := bstep (se 1 (by rfl) ⟨184703882, by rfl⟩ : syracuseStep 246271843 = 369407765) B369407765
theorem B16437491 : Blo 758332 16437491 := bstep (se 1 (by rfl) ⟨12328118, by rfl⟩ : syracuseStep 16437491 = 24656237) B24656237
theorem B1921441 : Blo 758332 1921441 := bstep (se 2 (by rfl) ⟨720540, by rfl⟩ : syracuseStep 1921441 = 1441081) B1441081
theorem B7820189 : Blo 758332 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B5854303 : Blo 758332 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B3856571 : Blo 758332 3856571 := bstep (se 1 (by rfl) ⟨2892428, by rfl⟩ : syracuseStep 3856571 = 5784857) B5784857
theorem B3857057 : Blo 758332 3857057 := bstep (se 2 (by rfl) ⟨1446396, by rfl⟩ : syracuseStep 3857057 = 2892793) B2892793
theorem B2087687 : Blo 758332 2087687 := bstep (se 1 (by rfl) ⟨1565765, by rfl⟩ : syracuseStep 2087687 = 3131531) B3131531
theorem B4381451 : Blo 758332 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B12999527 : Blo 758332 12999527 := bstep (se 1 (by rfl) ⟨9749645, by rfl⟩ : syracuseStep 12999527 = 19499291) B19499291
theorem B1367123 : Blo 758332 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B3464329 : Blo 758332 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B1138247 : Blo 758332 1138247 := bstep (se 1 (by rfl) ⟨853685, by rfl⟩ : syracuseStep 1138247 = 1707371) B1707371
theorem B1924681 : Blo 758332 1924681 := bstep (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) B1443511
theorem B4120399 : Blo 758332 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B74866751 : Blo 758332 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B14639231 : Blo 758332 14639231 := bstep (se 1 (by rfl) ⟨10979423, by rfl⟩ : syracuseStep 14639231 = 21958847) B21958847
theorem B3859163 : Blo 758332 3859163 := bstep (se 1 (by rfl) ⟨2894372, by rfl⟩ : syracuseStep 3859163 = 5788745) B5788745
theorem B1925927 : Blo 758332 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B1139579 : Blo 758332 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B1139783 : Blo 758332 1139783 := bstep (se 1 (by rfl) ⟨854837, by rfl⟩ : syracuseStep 1139783 = 1709675) B1709675
theorem B1139807 : Blo 758332 1139807 := bstep (se 1 (by rfl) ⟨854855, by rfl⟩ : syracuseStep 1139807 = 1709711) B1709711
theorem B1926251 : Blo 758332 1926251 := bstep (se 1 (by rfl) ⟨1444688, by rfl⟩ : syracuseStep 1926251 = 2889377) B2889377
theorem B1140095 : Blo 758332 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B1927223 : Blo 758332 1927223 := bstep (se 1 (by rfl) ⟨1445417, by rfl⟩ : syracuseStep 1927223 = 2890835) B2890835
theorem B1140911 : Blo 758332 1140911 := bstep (se 1 (by rfl) ⟨855683, by rfl⟩ : syracuseStep 1140911 = 1711367) B1711367
theorem B813287 : Blo 758332 813287 := bstep (se 1 (by rfl) ⟨609965, by rfl⟩ : syracuseStep 813287 = 1219931) B1219931
theorem B1141151 : Blo 758332 1141151 := bstep (se 1 (by rfl) ⟨855863, by rfl⟩ : syracuseStep 1141151 = 1711727) B1711727
theorem B3336643 : Blo 758332 3336643 := bstep (se 1 (by rfl) ⟨2502482, by rfl⟩ : syracuseStep 3336643 = 5004965) B5004965
theorem B133196501 : Blo 758332 133196501 := bstep (se 7 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 133196501 = 3121793) B3121793
theorem B2714489 : Blo 758332 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B10972043 : Blo 758332 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B4320215 : Blo 758332 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B1928519 : Blo 758332 1928519 := bstep (se 1 (by rfl) ⟨1446389, by rfl⟩ : syracuseStep 1928519 = 2892779) B2892779
theorem B12021085 : Blo 758332 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B1928569 : Blo 758332 1928569 := bstep (se 2 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 1928569 = 1446427) B1446427
theorem B6483361 : Blo 758332 6483361 := bstep (se 2 (by rfl) ⟨2431260, by rfl⟩ : syracuseStep 6483361 = 4862521) B4862521
theorem B8679473 : Blo 758332 8679473 := bstep (se 2 (by rfl) ⟨3254802, by rfl⟩ : syracuseStep 8679473 = 6509605) B6509605
theorem B9760823 : Blo 758332 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B1143323 : Blo 758332 1143323 := bstep (se 1 (by rfl) ⟨857492, by rfl⟩ : syracuseStep 1143323 = 1714985) B1714985
theorem B4879129 : Blo 758332 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B5763959 : Blo 758332 5763959 := bstep (se 1 (by rfl) ⟨4322969, by rfl⟩ : syracuseStep 5763959 = 8645939) B8645939
theorem B4322879 : Blo 758332 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B10974811 : Blo 758332 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B3471335 : Blo 758332 3471335 := bstep (se 1 (by rfl) ⟨2603501, by rfl⟩ : syracuseStep 3471335 = 5207003) B5207003
theorem B4323563 : Blo 758332 4323563 := bstep (se 1 (by rfl) ⟨3242672, by rfl⟩ : syracuseStep 4323563 = 6485345) B6485345
theorem B13008275 : Blo 758332 13008275 := bstep (se 1 (by rfl) ⟨9756206, by rfl⟩ : syracuseStep 13008275 = 19512413) B19512413
theorem B3702185 : Blo 758332 3702185 := bstep (se 2 (by rfl) ⟨1388319, by rfl⟩ : syracuseStep 3702185 = 2776639) B2776639
theorem B1442387 : Blo 758332 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B1442441 : Blo 758332 1442441 := bstep (se 2 (by rfl) ⟨540915, by rfl⟩ : syracuseStep 1442441 = 1081831) B1081831
theorem B2885503 : Blo 758332 2885503 := bstep (se 1 (by rfl) ⟨2164127, by rfl⟩ : syracuseStep 2885503 = 4328255) B4328255
theorem B1443739 : Blo 758332 1443739 := bstep (se 1 (by rfl) ⟨1082804, by rfl⟩ : syracuseStep 1443739 = 2165609) B2165609
theorem B10389707 : Blo 758332 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B13896353 : Blo 758332 13896353 := bstep (se 2 (by rfl) ⟨5211132, by rfl⟩ : syracuseStep 13896353 = 10422265) B10422265
theorem B854887 : Blo 758332 854887 := bstep (se 1 (by rfl) ⟨641165, by rfl⟩ : syracuseStep 854887 = 1282331) B1282331
theorem B10423151 : Blo 758332 10423151 := bstep (se 1 (by rfl) ⟨7817363, by rfl⟩ : syracuseStep 10423151 = 15634727) B15634727
theorem B1281001 : Blo 758332 1281001 := bstep (se 2 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 1281001 = 960751) B960751
theorem B5213459 : Blo 758332 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B2559599 : Blo 758332 2559599 := bstep (se 1 (by rfl) ⟨1919699, by rfl⟩ : syracuseStep 2559599 = 3839399) B3839399
theorem B1707785 : Blo 758332 1707785 := bstep (se 2 (by rfl) ⟨640419, by rfl⟩ : syracuseStep 1707785 = 1280839) B1280839
theorem B2559815 : Blo 758332 2559815 := bstep (se 1 (by rfl) ⟨1919861, by rfl⟩ : syracuseStep 2559815 = 3839723) B3839723
theorem B8228861 : Blo 758332 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B1708487 : Blo 758332 1708487 := bstep (se 1 (by rfl) ⟨1281365, by rfl⟩ : syracuseStep 1708487 = 2562731) B2562731
theorem B16028113 : Blo 758332 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B1708523 : Blo 758332 1708523 := bstep (se 1 (by rfl) ⟨1281392, by rfl⟩ : syracuseStep 1708523 = 2562785) B2562785
theorem B2920967 : Blo 758332 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B1708649 : Blo 758332 1708649 := bstep (se 2 (by rfl) ⟨640743, by rfl⟩ : syracuseStep 1708649 = 1281487) B1281487
theorem B2560895 : Blo 758332 2560895 := bstep (se 1 (by rfl) ⟨1920671, by rfl⟩ : syracuseStep 2560895 = 3841343) B3841343
theorem B1708937 : Blo 758332 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B758831 : Blo 758332 758831 := bstep (se 1 (by rfl) ⟨569123, by rfl⟩ : syracuseStep 758831 = 1138247) B1138247
theorem B49911167 : Blo 758332 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B1709801 : Blo 758332 1709801 := bstep (se 2 (by rfl) ⟨641175, by rfl⟩ : syracuseStep 1709801 = 1282351) B1282351
theorem B1283951 : Blo 758332 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B2561921 : Blo 758332 2561921 := bstep (se 2 (by rfl) ⟨960720, by rfl⟩ : syracuseStep 2561921 = 1921441) B1921441
theorem B759719 : Blo 758332 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B2168765 : Blo 758332 2168765 := bstep (se 3 (by rfl) ⟨406643, by rfl⟩ : syracuseStep 2168765 = 813287) B813287
theorem B759855 : Blo 758332 759855 := bstep (se 1 (by rfl) ⟨569891, by rfl⟩ : syracuseStep 759855 = 1139783) B1139783
theorem B759871 : Blo 758332 759871 := bstep (se 1 (by rfl) ⟨569903, by rfl⟩ : syracuseStep 759871 = 1139807) B1139807
theorem B1284167 : Blo 758332 1284167 := bstep (se 1 (by rfl) ⟨963125, by rfl⟩ : syracuseStep 1284167 = 1926251) B1926251
theorem B2562299 : Blo 758332 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B760063 : Blo 758332 760063 := bstep (se 1 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 760063 = 1140095) B1140095
theorem B1284815 : Blo 758332 1284815 := bstep (se 1 (by rfl) ⟨963611, by rfl⟩ : syracuseStep 1284815 = 1927223) B1927223
theorem B760607 : Blo 758332 760607 := bstep (se 1 (by rfl) ⟨570455, by rfl⟩ : syracuseStep 760607 = 1140911) B1140911
theorem B7805737 : Blo 758332 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B760767 : Blo 758332 760767 := bstep (se 1 (by rfl) ⟨570575, by rfl⟩ : syracuseStep 760767 = 1141151) B1141151
theorem B12327983 : Blo 758332 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B2890849 : Blo 758332 2890849 := bstep (se 2 (by rfl) ⟨1084068, by rfl⟩ : syracuseStep 2890849 = 2168137) B2168137
theorem B1809659 : Blo 758332 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B7314695 : Blo 758332 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B1711529 : Blo 758332 1711529 := bstep (se 2 (by rfl) ⟨641823, by rfl⟩ : syracuseStep 1711529 = 1283647) B1283647
theorem B1285679 : Blo 758332 1285679 := bstep (se 1 (by rfl) ⟨964259, by rfl⟩ : syracuseStep 1285679 = 1928519) B1928519
theorem B1712159 : Blo 758332 1712159 := bstep (se 1 (by rfl) ⟨1284119, by rfl⟩ : syracuseStep 1712159 = 2568239) B2568239
theorem B3645661 : Blo 758332 3645661 := bstep (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) B1367123
theorem B762215 : Blo 758332 762215 := bstep (se 1 (by rfl) ⟨571661, by rfl⟩ : syracuseStep 762215 = 1143323) B1143323
theorem B1712555 : Blo 758332 1712555 := bstep (se 1 (by rfl) ⟨1284416, by rfl⟩ : syracuseStep 1712555 = 2568833) B2568833
theorem B3842639 : Blo 758332 3842639 := bstep (se 1 (by rfl) ⟨2881979, by rfl⟩ : syracuseStep 3842639 = 5763959) B5763959
theorem B3646777 : Blo 758332 3646777 := bstep (se 2 (by rfl) ⟨1367541, by rfl⟩ : syracuseStep 3646777 = 2735083) B2735083
theorem B1713743 : Blo 758332 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B2566079 : Blo 758332 2566079 := bstep (se 1 (by rfl) ⟨1924559, by rfl⟩ : syracuseStep 2566079 = 3849119) B3849119
theorem B2566241 : Blo 758332 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B2468123 : Blo 758332 2468123 := bstep (se 1 (by rfl) ⟨1851092, by rfl⟩ : syracuseStep 2468123 = 3702185) B3702185
theorem B3288127 : Blo 758332 3288127 := bstep (se 1 (by rfl) ⟨2466095, by rfl⟩ : syracuseStep 3288127 = 4932191) B4932191
theorem B2567699 : Blo 758332 2567699 := bstep (se 1 (by rfl) ⟨1925774, by rfl⟩ : syracuseStep 2567699 = 3851549) B3851549
theorem B10958327 : Blo 758332 10958327 := bstep (se 1 (by rfl) ⟨8218745, by rfl⟩ : syracuseStep 10958327 = 16437491) B16437491
theorem B9746365 : Blo 758332 9746365 := bstep (se 3 (by rfl) ⟨1827443, by rfl⟩ : syracuseStep 9746365 = 3654887) B3654887
theorem B6666259 : Blo 758332 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B1620089 : Blo 758332 1620089 := bstep (se 2 (by rfl) ⟨607533, by rfl⟩ : syracuseStep 1620089 = 1215067) B1215067
theorem B9746729 : Blo 758332 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B2571047 : Blo 758332 2571047 := bstep (se 1 (by rfl) ⟨1928285, by rfl⟩ : syracuseStep 2571047 = 3856571) B3856571
theorem B2571371 : Blo 758332 2571371 := bstep (se 1 (by rfl) ⟨1928528, by rfl⟩ : syracuseStep 2571371 = 3857057) B3857057
theorem B2571425 : Blo 758332 2571425 := bstep (se 2 (by rfl) ⟨964284, by rfl⟩ : syracuseStep 2571425 = 1928569) B1928569
theorem B1391791 : Blo 758332 1391791 := bstep (se 1 (by rfl) ⟨1043843, by rfl⟩ : syracuseStep 1391791 = 2087687) B2087687
theorem B8666351 : Blo 758332 8666351 := bstep (se 1 (by rfl) ⟨6499763, by rfl⟩ : syracuseStep 8666351 = 12999527) B12999527
theorem B13876721 : Blo 758332 13876721 := bstep (se 2 (by rfl) ⟨5203770, by rfl⟩ : syracuseStep 13876721 = 10407541) B10407541
theorem B7323695 : Blo 758332 7323695 := bstep (se 1 (by rfl) ⟨5492771, by rfl⟩ : syracuseStep 7323695 = 10985543) B10985543
theorem B2572775 : Blo 758332 2572775 := bstep (se 1 (by rfl) ⟨1929581, by rfl⟩ : syracuseStep 2572775 = 3859163) B3859163
theorem B3851063 : Blo 758332 3851063 := bstep (se 1 (by rfl) ⟨2888297, by rfl⟩ : syracuseStep 3851063 = 5776595) B5776595
theorem B6505505 : Blo 758332 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B14633081 : Blo 758332 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B5786315 : Blo 758332 5786315 := bstep (se 1 (by rfl) ⟨4339736, by rfl⟩ : syracuseStep 5786315 = 8679473) B8679473
theorem B6507215 : Blo 758332 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B5492711 : Blo 758332 5492711 := bstep (se 1 (by rfl) ⟨4119533, by rfl⟩ : syracuseStep 5492711 = 8239067) B8239067
theorem B2314223 : Blo 758332 2314223 := bstep (se 1 (by rfl) ⟨1735667, by rfl⟩ : syracuseStep 2314223 = 3471335) B3471335
theorem B8672183 : Blo 758332 8672183 := bstep (se 1 (by rfl) ⟨6504137, by rfl⟩ : syracuseStep 8672183 = 13008275) B13008275
theorem B5493865 : Blo 758332 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B1955603 : Blo 758332 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B2774825 : Blo 758332 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B1137719 : Blo 758332 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B6479261 : Blo 758332 6479261 := bstep (se 3 (by rfl) ⟨1214861, by rfl⟩ : syracuseStep 6479261 = 2429723) B2429723
theorem B1138127 : Blo 758332 1138127 := bstep (se 1 (by rfl) ⟨853595, by rfl⟩ : syracuseStep 1138127 = 1707191) B1707191
theorem B1138217 : Blo 758332 1138217 := bstep (se 2 (by rfl) ⟨426831, by rfl⟩ : syracuseStep 1138217 = 853663) B853663
theorem B1138313 : Blo 758332 1138313 := bstep (se 2 (by rfl) ⟨426867, by rfl⟩ : syracuseStep 1138313 = 853735) B853735
theorem B1924955 : Blo 758332 1924955 := bstep (se 1 (by rfl) ⟨1443716, by rfl⟩ : syracuseStep 1924955 = 2887433) B2887433
theorem B1138847 : Blo 758332 1138847 := bstep (se 1 (by rfl) ⟨854135, by rfl⟩ : syracuseStep 1138847 = 1708271) B1708271
theorem B3694777 : Blo 758332 3694777 := bstep (se 2 (by rfl) ⟨1385541, by rfl⟩ : syracuseStep 3694777 = 2771083) B2771083
theorem B3859001 : Blo 758332 3859001 := bstep (se 2 (by rfl) ⟨1447125, by rfl⟩ : syracuseStep 3859001 = 2894251) B2894251
theorem B4448857 : Blo 758332 4448857 := bstep (se 2 (by rfl) ⟨1668321, by rfl⟩ : syracuseStep 4448857 = 3336643) B3336643
theorem B1139495 : Blo 758332 1139495 := bstep (se 1 (by rfl) ⟨854621, by rfl⟩ : syracuseStep 1139495 = 1709243) B1709243
theorem B1139519 : Blo 758332 1139519 := bstep (se 1 (by rfl) ⟨854639, by rfl⟩ : syracuseStep 1139519 = 1709279) B1709279
theorem B8217449 : Blo 758332 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B1139711 : Blo 758332 1139711 := bstep (se 1 (by rfl) ⟨854783, by rfl⟩ : syracuseStep 1139711 = 1709567) B1709567
theorem B1926281 : Blo 758332 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B1729775 : Blo 758332 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B1140089 : Blo 758332 1140089 := bstep (se 2 (by rfl) ⟨427533, by rfl⟩ : syracuseStep 1140089 = 855067) B855067
theorem B2057683 : Blo 758332 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B4613705 : Blo 758332 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B1140329 : Blo 758332 1140329 := bstep (se 2 (by rfl) ⟨427623, by rfl⟩ : syracuseStep 1140329 = 855247) B855247
theorem B1140431 : Blo 758332 1140431 := bstep (se 1 (by rfl) ⟨855323, by rfl⟩ : syracuseStep 1140431 = 1710647) B1710647
theorem B6481721 : Blo 758332 6481721 := bstep (se 2 (by rfl) ⟨2430645, by rfl⟩ : syracuseStep 6481721 = 4861291) B4861291
theorem B8644481 : Blo 758332 8644481 := bstep (se 2 (by rfl) ⟨3241680, by rfl⟩ : syracuseStep 8644481 = 6483361) B6483361
theorem B1140791 : Blo 758332 1140791 := bstep (se 1 (by rfl) ⟨855593, by rfl⟩ : syracuseStep 1140791 = 1711187) B1711187
theorem B1140959 : Blo 758332 1140959 := bstep (se 1 (by rfl) ⟨855719, by rfl⟩ : syracuseStep 1140959 = 1711439) B1711439
theorem B328362457 : Blo 758332 328362457 := bstep (se 2 (by rfl) ⟨123135921, by rfl⟩ : syracuseStep 328362457 = 246271843) B246271843
theorem B1141343 : Blo 758332 1141343 := bstep (se 1 (by rfl) ⟨856007, by rfl⟩ : syracuseStep 1141343 = 1712015) B1712015
theorem B1141415 : Blo 758332 1141415 := bstep (se 1 (by rfl) ⟨856061, by rfl⟩ : syracuseStep 1141415 = 1712123) B1712123
theorem B9759487 : Blo 758332 9759487 := bstep (se 1 (by rfl) ⟨7319615, by rfl⟩ : syracuseStep 9759487 = 14639231) B14639231
theorem B1141823 : Blo 758332 1141823 := bstep (se 1 (by rfl) ⟨856367, by rfl⟩ : syracuseStep 1141823 = 1712735) B1712735
theorem B1142249 : Blo 758332 1142249 := bstep (se 2 (by rfl) ⟨428343, by rfl⟩ : syracuseStep 1142249 = 856687) B856687
theorem B1142303 : Blo 758332 1142303 := bstep (se 1 (by rfl) ⟨856727, by rfl⟩ : syracuseStep 1142303 = 1713455) B1713455
theorem B1142327 : Blo 758332 1142327 := bstep (se 1 (by rfl) ⟨856745, by rfl⟩ : syracuseStep 1142327 = 1713491) B1713491
theorem B3239615 : Blo 758332 3239615 := bstep (se 1 (by rfl) ⟨2429711, by rfl⟩ : syracuseStep 3239615 = 4859423) B4859423
theorem B1143161 : Blo 758332 1143161 := bstep (se 2 (by rfl) ⟨428685, by rfl⟩ : syracuseStep 1143161 = 857371) B857371
theorem B88797667 : Blo 758332 88797667 := bstep (se 1 (by rfl) ⟨66598250, by rfl⟩ : syracuseStep 88797667 = 133196501) B133196501
theorem B1143401 : Blo 758332 1143401 := bstep (se 2 (by rfl) ⟨428775, by rfl⟩ : syracuseStep 1143401 = 857551) B857551
theorem B2880143 : Blo 758332 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B5206781 : Blo 758332 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B7894093 : Blo 758332 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B2881919 : Blo 758332 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B2882375 : Blo 758332 2882375 := bstep (se 1 (by rfl) ⟨2161781, by rfl⟩ : syracuseStep 2882375 = 4323563) B4323563
theorem B4619105 : Blo 758332 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B4882463 : Blo 758332 4882463 := bstep (se 1 (by rfl) ⟨3661847, by rfl⟩ : syracuseStep 4882463 = 7323695) B7323695
theorem B5931809 : Blo 758332 5931809 := bstep (se 2 (by rfl) ⟨2224428, by rfl⟩ : syracuseStep 5931809 = 4448857) B4448857
theorem B6948767 : Blo 758332 6948767 := bstep (se 1 (by rfl) ⟨5211575, by rfl⟩ : syracuseStep 6948767 = 10423151) B10423151
theorem B3475639 : Blo 758332 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B1706399 : Blo 758332 1706399 := bstep (se 1 (by rfl) ⟨1279799, by rfl⟩ : syracuseStep 1706399 = 2559599) B2559599
theorem B1706543 : Blo 758332 1706543 := bstep (se 1 (by rfl) ⟨1279907, by rfl⟩ : syracuseStep 1706543 = 2559815) B2559815
theorem B1542815 : Blo 758332 1542815 := bstep (se 1 (by rfl) ⟨1157111, by rfl⟩ : syracuseStep 1542815 = 2314223) B2314223
theorem B1707263 : Blo 758332 1707263 := bstep (se 1 (by rfl) ⟨1280447, by rfl⟩ : syracuseStep 1707263 = 2560895) B2560895
theorem B437816609 : Blo 758332 437816609 := bstep (se 2 (by rfl) ⟨164181228, by rfl⟩ : syracuseStep 437816609 = 328362457) B328362457
theorem B13012649 : Blo 758332 13012649 := bstep (se 2 (by rfl) ⟨4879743, by rfl⟩ : syracuseStep 13012649 = 9759487) B9759487
theorem B855967 : Blo 758332 855967 := bstep (se 1 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 855967 = 1283951) B1283951
theorem B1707947 : Blo 758332 1707947 := bstep (se 1 (by rfl) ⟨1280960, by rfl⟩ : syracuseStep 1707947 = 2561921) B2561921
theorem B1445843 : Blo 758332 1445843 := bstep (se 1 (by rfl) ⟨1084382, by rfl⟩ : syracuseStep 1445843 = 2168765) B2168765
theorem B1708001 : Blo 758332 1708001 := bstep (se 2 (by rfl) ⟨640500, by rfl⟩ : syracuseStep 1708001 = 1281001) B1281001
theorem B856111 : Blo 758332 856111 := bstep (se 1 (by rfl) ⟨642083, by rfl⟩ : syracuseStep 856111 = 1284167) B1284167
theorem B1708199 : Blo 758332 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B856543 : Blo 758332 856543 := bstep (se 1 (by rfl) ⟨642407, by rfl⟩ : syracuseStep 856543 = 1284815) B1284815
theorem B758479 : Blo 758332 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B5214941 : Blo 758332 5214941 := bstep (se 3 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 5214941 = 1955603) B1955603
theorem B758751 : Blo 758332 758751 := bstep (se 1 (by rfl) ⟨569063, by rfl⟩ : syracuseStep 758751 = 1138127) B1138127
theorem B758811 : Blo 758332 758811 := bstep (se 1 (by rfl) ⟨569108, by rfl⟩ : syracuseStep 758811 = 1138217) B1138217
theorem B857119 : Blo 758332 857119 := bstep (se 1 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 857119 = 1285679) B1285679
theorem B758875 : Blo 758332 758875 := bstep (se 1 (by rfl) ⟨569156, by rfl⟩ : syracuseStep 758875 = 1138313) B1138313
theorem B1283303 : Blo 758332 1283303 := bstep (se 1 (by rfl) ⟨962477, by rfl⟩ : syracuseStep 1283303 = 1924955) B1924955
theorem B759231 : Blo 758332 759231 := bstep (se 1 (by rfl) ⟨569423, by rfl⟩ : syracuseStep 759231 = 1138847) B1138847
theorem B2561759 : Blo 758332 2561759 := bstep (se 1 (by rfl) ⟨1921319, by rfl⟩ : syracuseStep 2561759 = 3842639) B3842639
theorem B759663 : Blo 758332 759663 := bstep (se 1 (by rfl) ⟨569747, by rfl⟩ : syracuseStep 759663 = 1139495) B1139495
theorem B759679 : Blo 758332 759679 := bstep (se 1 (by rfl) ⟨569759, by rfl⟩ : syracuseStep 759679 = 1139519) B1139519
theorem B5478299 : Blo 758332 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B21370817 : Blo 758332 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B118396889 : Blo 758332 118396889 := bstep (se 2 (by rfl) ⟨44398833, by rfl⟩ : syracuseStep 118396889 = 88797667) B88797667
theorem B759807 : Blo 758332 759807 := bstep (se 1 (by rfl) ⟨569855, by rfl⟩ : syracuseStep 759807 = 1139711) B1139711
theorem B1284187 : Blo 758332 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B760059 : Blo 758332 760059 := bstep (se 1 (by rfl) ⟨570044, by rfl⟩ : syracuseStep 760059 = 1140089) B1140089
theorem B760219 : Blo 758332 760219 := bstep (se 1 (by rfl) ⟨570164, by rfl⟩ : syracuseStep 760219 = 1140329) B1140329
theorem B760287 : Blo 758332 760287 := bstep (se 1 (by rfl) ⟨570215, by rfl⟩ : syracuseStep 760287 = 1140431) B1140431
theorem B1710719 : Blo 758332 1710719 := bstep (se 1 (by rfl) ⟨1283039, by rfl⟩ : syracuseStep 1710719 = 2566079) B2566079
theorem B760527 : Blo 758332 760527 := bstep (se 1 (by rfl) ⟨570395, by rfl⟩ : syracuseStep 760527 = 1140791) B1140791
theorem B1710827 : Blo 758332 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B10525457 : Blo 758332 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B760639 : Blo 758332 760639 := bstep (se 1 (by rfl) ⟨570479, by rfl⟩ : syracuseStep 760639 = 1140959) B1140959
theorem B1645415 : Blo 758332 1645415 := bstep (se 1 (by rfl) ⟨1234061, by rfl⟩ : syracuseStep 1645415 = 2468123) B2468123
theorem B760895 : Blo 758332 760895 := bstep (se 1 (by rfl) ⟨570671, by rfl⟩ : syracuseStep 760895 = 1141343) B1141343
theorem B760943 : Blo 758332 760943 := bstep (se 1 (by rfl) ⟨570707, by rfl⟩ : syracuseStep 760943 = 1141415) B1141415
theorem B761215 : Blo 758332 761215 := bstep (se 1 (by rfl) ⟨570911, by rfl⟩ : syracuseStep 761215 = 1141823) B1141823
theorem B761499 : Blo 758332 761499 := bstep (se 1 (by rfl) ⟨571124, by rfl⟩ : syracuseStep 761499 = 1142249) B1142249
theorem B1711799 : Blo 758332 1711799 := bstep (se 1 (by rfl) ⟨1283849, by rfl⟩ : syracuseStep 1711799 = 2567699) B2567699
theorem B761535 : Blo 758332 761535 := bstep (se 1 (by rfl) ⟨571151, by rfl⟩ : syracuseStep 761535 = 1142303) B1142303
theorem B761551 : Blo 758332 761551 := bstep (se 1 (by rfl) ⟨571163, by rfl⟩ : syracuseStep 761551 = 1142327) B1142327
theorem B8888345 : Blo 758332 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B762107 : Blo 758332 762107 := bstep (se 1 (by rfl) ⟨571580, by rfl⟩ : syracuseStep 762107 = 1143161) B1143161
theorem B762267 : Blo 758332 762267 := bstep (se 1 (by rfl) ⟨571700, by rfl⟩ : syracuseStep 762267 = 1143401) B1143401
theorem B4825757 : Blo 758332 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B6497819 : Blo 758332 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B1714031 : Blo 758332 1714031 := bstep (se 1 (by rfl) ⟨1285523, by rfl⟩ : syracuseStep 1714031 = 2571047) B2571047
theorem B1714247 : Blo 758332 1714247 := bstep (se 1 (by rfl) ⟨1285685, by rfl⟩ : syracuseStep 1714247 = 2571371) B2571371
theorem B1714283 : Blo 758332 1714283 := bstep (se 1 (by rfl) ⟨1285712, by rfl⟩ : syracuseStep 1714283 = 2571425) B2571425
theorem B5777567 : Blo 758332 5777567 := bstep (se 1 (by rfl) ⟨4333175, by rfl⟩ : syracuseStep 5777567 = 8666351) B8666351
theorem B9251147 : Blo 758332 9251147 := bstep (se 1 (by rfl) ⟨6938360, by rfl⟩ : syracuseStep 9251147 = 13876721) B13876721
theorem B4860881 : Blo 758332 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B1715183 : Blo 758332 1715183 := bstep (se 1 (by rfl) ⟨1286387, by rfl⟩ : syracuseStep 1715183 = 2572775) B2572775
theorem B961627 : Blo 758332 961627 := bstep (se 1 (by rfl) ⟨721220, by rfl⟩ : syracuseStep 961627 = 1442441) B1442441
theorem B2567375 : Blo 758332 2567375 := bstep (se 1 (by rfl) ⟨1925531, by rfl⟩ : syracuseStep 2567375 = 3851063) B3851063
theorem B4337003 : Blo 758332 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B6926471 : Blo 758332 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B3846365 : Blo 758332 3846365 := bstep (se 3 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 3846365 = 1442387) B1442387
theorem B4862369 : Blo 758332 4862369 := bstep (se 2 (by rfl) ⟨1823388, by rfl⟩ : syracuseStep 4862369 = 3646777) B3646777
theorem B4338143 : Blo 758332 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B3847337 : Blo 758332 3847337 := bstep (se 2 (by rfl) ⟨1442751, by rfl⟩ : syracuseStep 3847337 = 2885503) B2885503
theorem B5485907 : Blo 758332 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B1947311 : Blo 758332 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B5781455 : Blo 758332 5781455 := bstep (se 1 (by rfl) ⟨4336091, by rfl⟩ : syracuseStep 5781455 = 8672183) B8672183
theorem B33274111 : Blo 758332 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B78821909 : Blo 758332 78821909 := bstep (se 6 (by rfl) ⟨1847388, by rfl⟩ : syracuseStep 78821909 = 3694777) B3694777
theorem B1849883 : Blo 758332 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B2572667 : Blo 758332 2572667 := bstep (se 1 (by rfl) ⟨1929500, by rfl⟩ : syracuseStep 2572667 = 3859001) B3859001
theorem B7325153 : Blo 758332 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B12995153 : Blo 758332 12995153 := bstep (se 2 (by rfl) ⟨4873182, by rfl⟩ : syracuseStep 12995153 = 9746365) B9746365
theorem B1920095 : Blo 758332 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B10407649 : Blo 758332 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B3854465 : Blo 758332 3854465 := bstep (se 2 (by rfl) ⟨1445424, by rfl⟩ : syracuseStep 3854465 = 2890849) B2890849
theorem B1855721 : Blo 758332 1855721 := bstep (se 2 (by rfl) ⟨695895, by rfl⟩ : syracuseStep 1855721 = 1391791) B1391791
theorem B1921279 : Blo 758332 1921279 := bstep (se 1 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 1921279 = 2881919) B2881919
theorem B1921583 : Blo 758332 1921583 := bstep (se 1 (by rfl) ⟨1441187, by rfl⟩ : syracuseStep 1921583 = 2882375) B2882375
theorem B9755387 : Blo 758332 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B9264235 : Blo 758332 9264235 := bstep (se 1 (by rfl) ⟨6948176, by rfl⟩ : syracuseStep 9264235 = 13896353) B13896353
theorem B3857543 : Blo 758332 3857543 := bstep (se 1 (by rfl) ⟨2893157, by rfl⟩ : syracuseStep 3857543 = 5786315) B5786315
theorem B2743577 : Blo 758332 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B1138523 : Blo 758332 1138523 := bstep (se 1 (by rfl) ⟨853892, by rfl⟩ : syracuseStep 1138523 = 1707785) B1707785
theorem B1924985 : Blo 758332 1924985 := bstep (se 2 (by rfl) ⟨721869, by rfl⟩ : syracuseStep 1924985 = 1443739) B1443739
theorem B1138991 : Blo 758332 1138991 := bstep (se 1 (by rfl) ⟨854243, by rfl⟩ : syracuseStep 1138991 = 1708487) B1708487
theorem B1139015 : Blo 758332 1139015 := bstep (se 1 (by rfl) ⟨854261, by rfl⟩ : syracuseStep 1139015 = 1708523) B1708523
theorem B1139099 : Blo 758332 1139099 := bstep (se 1 (by rfl) ⟨854324, by rfl⟩ : syracuseStep 1139099 = 1708649) B1708649
theorem B1139291 : Blo 758332 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B4612733 : Blo 758332 4612733 := bstep (se 3 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 4612733 = 1729775) B1729775
theorem B1139849 : Blo 758332 1139849 := bstep (se 2 (by rfl) ⟨427443, by rfl⟩ : syracuseStep 1139849 = 854887) B854887
theorem B1139867 : Blo 758332 1139867 := bstep (se 1 (by rfl) ⟨854900, by rfl⟩ : syracuseStep 1139867 = 1709801) B1709801
theorem B4384169 : Blo 758332 4384169 := bstep (se 2 (by rfl) ⟨1644063, by rfl⟩ : syracuseStep 4384169 = 3288127) B3288127
theorem B8218655 : Blo 758332 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B4876463 : Blo 758332 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B4319507 : Blo 758332 4319507 := bstep (se 1 (by rfl) ⟨3239630, by rfl⟩ : syracuseStep 4319507 = 6479261) B6479261
theorem B1141019 : Blo 758332 1141019 := bstep (se 1 (by rfl) ⟨855764, by rfl⟩ : syracuseStep 1141019 = 1711529) B1711529
theorem B1141439 : Blo 758332 1141439 := bstep (se 1 (by rfl) ⟨856079, by rfl⟩ : syracuseStep 1141439 = 1712159) B1712159
theorem B1141703 : Blo 758332 1141703 := bstep (se 1 (by rfl) ⟨856277, by rfl⟩ : syracuseStep 1141703 = 1712555) B1712555
theorem B3075803 : Blo 758332 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B1142495 : Blo 758332 1142495 := bstep (se 1 (by rfl) ⟨856871, by rfl⟩ : syracuseStep 1142495 = 1713743) B1713743
theorem B4321147 : Blo 758332 4321147 := bstep (se 1 (by rfl) ⟨3240860, by rfl⟩ : syracuseStep 4321147 = 6481721) B6481721
theorem B5762987 : Blo 758332 5762987 := bstep (se 1 (by rfl) ⟨4322240, by rfl⟩ : syracuseStep 5762987 = 8644481) B8644481
theorem B2159743 : Blo 758332 2159743 := bstep (se 1 (by rfl) ⟨1619807, by rfl⟩ : syracuseStep 2159743 = 3239615) B3239615
theorem B3471187 : Blo 758332 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B7305551 : Blo 758332 7305551 := bstep (se 1 (by rfl) ⟨5479163, by rfl⟩ : syracuseStep 7305551 = 10958327) B10958327
theorem B1080059 : Blo 758332 1080059 := bstep (se 1 (by rfl) ⟨810044, by rfl⟩ : syracuseStep 1080059 = 1620089) B1620089
theorem B3079403 : Blo 758332 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B14647229 : Blo 758332 14647229 := bstep (se 3 (by rfl) ⟨2746355, by rfl⟩ : syracuseStep 14647229 = 5492711) B5492711
theorem B4948589 : Blo 758332 4948589 := bstep (se 3 (by rfl) ⟨927860, by rfl⟩ : syracuseStep 4948589 = 1855721) B1855721
theorem B4883435 : Blo 758332 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B1280063 : Blo 758332 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B1281055 : Blo 758332 1281055 := bstep (se 1 (by rfl) ⟨960791, by rfl⟩ : syracuseStep 1281055 = 1921583) B1921583
theorem B3476627 : Blo 758332 3476627 := bstep (se 1 (by rfl) ⟨2607470, by rfl⟩ : syracuseStep 3476627 = 5214941) B5214941
theorem B855535 : Blo 758332 855535 := bstep (se 1 (by rfl) ⟨641651, by rfl⟩ : syracuseStep 855535 = 1283303) B1283303
theorem B1707839 : Blo 758332 1707839 := bstep (se 1 (by rfl) ⟨1280879, by rfl⟩ : syracuseStep 1707839 = 2561759) B2561759
theorem B1282169 : Blo 758332 1282169 := bstep (se 2 (by rfl) ⟨480813, by rfl⟩ : syracuseStep 1282169 = 961627) B961627
theorem B7016971 : Blo 758332 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B56988845 : Blo 758332 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B759015 : Blo 758332 759015 := bstep (se 1 (by rfl) ⟨569261, by rfl⟩ : syracuseStep 759015 = 1138523) B1138523
theorem B1283323 : Blo 758332 1283323 := bstep (se 1 (by rfl) ⟨962492, by rfl⟩ : syracuseStep 1283323 = 1924985) B1924985
theorem B759327 : Blo 758332 759327 := bstep (se 1 (by rfl) ⟨569495, by rfl⟩ : syracuseStep 759327 = 1138991) B1138991
theorem B759343 : Blo 758332 759343 := bstep (se 1 (by rfl) ⟨569507, by rfl⟩ : syracuseStep 759343 = 1139015) B1139015
theorem B759399 : Blo 758332 759399 := bstep (se 1 (by rfl) ⟨569549, by rfl⟩ : syracuseStep 759399 = 1139099) B1139099
theorem B19732085 : Blo 758332 19732085 := bstep (se 5 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 19732085 = 1849883) B1849883
theorem B2561705 : Blo 758332 2561705 := bstep (se 2 (by rfl) ⟨960639, by rfl⟩ : syracuseStep 2561705 = 1921279) B1921279
theorem B759527 : Blo 758332 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B3217171 : Blo 758332 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B759899 : Blo 758332 759899 := bstep (se 1 (by rfl) ⟨569924, by rfl⟩ : syracuseStep 759899 = 1139849) B1139849
theorem B759911 : Blo 758332 759911 := bstep (se 1 (by rfl) ⟨569933, by rfl⟩ : syracuseStep 759911 = 1139867) B1139867
theorem B2922779 : Blo 758332 2922779 := bstep (se 1 (by rfl) ⟨2192084, by rfl⟩ : syracuseStep 2922779 = 4384169) B4384169
theorem B4331879 : Blo 758332 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B5479103 : Blo 758332 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B760679 : Blo 758332 760679 := bstep (se 1 (by rfl) ⟨570509, by rfl⟩ : syracuseStep 760679 = 1141019) B1141019
theorem B6167431 : Blo 758332 6167431 := bstep (se 1 (by rfl) ⟨4625573, by rfl⟩ : syracuseStep 6167431 = 9251147) B9251147
theorem B760959 : Blo 758332 760959 := bstep (se 1 (by rfl) ⟨570719, by rfl⟩ : syracuseStep 760959 = 1141439) B1141439
theorem B761135 : Blo 758332 761135 := bstep (se 1 (by rfl) ⟨570851, by rfl⟩ : syracuseStep 761135 = 1141703) B1141703
theorem B1711583 : Blo 758332 1711583 := bstep (se 1 (by rfl) ⟨1283687, by rfl⟩ : syracuseStep 1711583 = 2567375) B2567375
theorem B2891335 : Blo 758332 2891335 := bstep (se 1 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 2891335 = 4337003) B4337003
theorem B4628249 : Blo 758332 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B761663 : Blo 758332 761663 := bstep (se 1 (by rfl) ⟨571247, by rfl⟩ : syracuseStep 761663 = 1142495) B1142495
theorem B3841991 : Blo 758332 3841991 := bstep (se 1 (by rfl) ⟨2881493, by rfl⟩ : syracuseStep 3841991 = 5762987) B5762987
theorem B1712249 : Blo 758332 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B2564243 : Blo 758332 2564243 := bstep (se 1 (by rfl) ⟨1923182, by rfl⟩ : syracuseStep 2564243 = 3846365) B3846365
theorem B2892095 : Blo 758332 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B2564891 : Blo 758332 2564891 := bstep (se 1 (by rfl) ⟨1923668, by rfl⟩ : syracuseStep 2564891 = 3847337) B3847337
theorem B3254975 : Blo 758332 3254975 := bstep (se 1 (by rfl) ⟨2441231, by rfl⟩ : syracuseStep 3254975 = 4882463) B4882463
theorem B1715111 : Blo 758332 1715111 := bstep (se 1 (by rfl) ⟨1286333, by rfl⟩ : syracuseStep 1715111 = 2572667) B2572667
theorem B4632511 : Blo 758332 4632511 := bstep (se 1 (by rfl) ⟨3474383, by rfl⟩ : syracuseStep 4632511 = 6948767) B6948767
theorem B8663435 : Blo 758332 8663435 := bstep (se 1 (by rfl) ⟨6497576, by rfl⟩ : syracuseStep 8663435 = 12995153) B12995153
theorem B1028543 : Blo 758332 1028543 := bstep (se 1 (by rfl) ⟨771407, by rfl⟩ : syracuseStep 1028543 = 1542815) B1542815
theorem B291877739 : Blo 758332 291877739 := bstep (se 1 (by rfl) ⟨218908304, by rfl⟩ : syracuseStep 291877739 = 437816609) B437816609
theorem B963895 : Blo 758332 963895 := bstep (se 1 (by rfl) ⟨722921, by rfl⟩ : syracuseStep 963895 = 1445843) B1445843
theorem B2569643 : Blo 758332 2569643 := bstep (se 1 (by rfl) ⟨1927232, by rfl⟩ : syracuseStep 2569643 = 3854465) B3854465
theorem B4634185 : Blo 758332 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B14629085 : Blo 758332 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B3652199 : Blo 758332 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B6503591 : Blo 758332 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B1096943 : Blo 758332 1096943 := bstep (se 1 (by rfl) ⟨822707, by rfl⟩ : syracuseStep 1096943 = 1645415) B1645415
theorem B2571695 : Blo 758332 2571695 := bstep (se 1 (by rfl) ⟨1928771, by rfl⟩ : syracuseStep 2571695 = 3857543) B3857543
theorem B13876865 : Blo 758332 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B3851711 : Blo 758332 3851711 := bstep (se 1 (by rfl) ⟨2888783, by rfl⟩ : syracuseStep 3851711 = 5777567) B5777567
theorem B2050535 : Blo 758332 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B1298207 : Blo 758332 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B3854303 : Blo 758332 3854303 := bstep (se 1 (by rfl) ⟨2890727, by rfl⟩ : syracuseStep 3854303 = 5781455) B5781455
theorem B4870367 : Blo 758332 4870367 := bstep (se 1 (by rfl) ⟨3652775, by rfl⟩ : syracuseStep 4870367 = 7305551) B7305551
theorem B52547939 : Blo 758332 52547939 := bstep (se 1 (by rfl) ⟨39410954, by rfl⟩ : syracuseStep 52547939 = 78821909) B78821909
theorem B2052935 : Blo 758332 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B3954539 : Blo 758332 3954539 := bstep (se 1 (by rfl) ⟨2965904, by rfl⟩ : syracuseStep 3954539 = 5931809) B5931809
theorem B1137599 : Blo 758332 1137599 := bstep (se 1 (by rfl) ⟨853199, by rfl⟩ : syracuseStep 1137599 = 1706399) B1706399
theorem B1137695 : Blo 758332 1137695 := bstep (se 1 (by rfl) ⟨853271, by rfl⟩ : syracuseStep 1137695 = 1706543) B1706543
theorem B1138175 : Blo 758332 1138175 := bstep (se 1 (by rfl) ⟨853631, by rfl⟩ : syracuseStep 1138175 = 1707263) B1707263
theorem B8675099 : Blo 758332 8675099 := bstep (se 1 (by rfl) ⟨6506324, by rfl⟩ : syracuseStep 8675099 = 13012649) B13012649
theorem B1138631 : Blo 758332 1138631 := bstep (se 1 (by rfl) ⟨853973, by rfl⟩ : syracuseStep 1138631 = 1707947) B1707947
theorem B1138667 : Blo 758332 1138667 := bstep (se 1 (by rfl) ⟨854000, by rfl⟩ : syracuseStep 1138667 = 1708001) B1708001
theorem B1138799 : Blo 758332 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B78931259 : Blo 758332 78931259 := bstep (se 1 (by rfl) ⟨59198444, by rfl⟩ : syracuseStep 78931259 = 118396889) B118396889
theorem B1140479 : Blo 758332 1140479 := bstep (se 1 (by rfl) ⟨855359, by rfl⟩ : syracuseStep 1140479 = 1710719) B1710719
theorem B1140551 : Blo 758332 1140551 := bstep (se 1 (by rfl) ⟨855413, by rfl⟩ : syracuseStep 1140551 = 1710827) B1710827
theorem B1829051 : Blo 758332 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B1141199 : Blo 758332 1141199 := bstep (se 1 (by rfl) ⟨855899, by rfl⟩ : syracuseStep 1141199 = 1711799) B1711799
theorem B5761529 : Blo 758332 5761529 := bstep (se 2 (by rfl) ⟨2160573, by rfl⟩ : syracuseStep 5761529 = 4321147) B4321147
theorem B1141289 : Blo 758332 1141289 := bstep (se 2 (by rfl) ⟨427983, by rfl⟩ : syracuseStep 1141289 = 855967) B855967
theorem B5925563 : Blo 758332 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B1141481 : Blo 758332 1141481 := bstep (se 2 (by rfl) ⟨428055, by rfl⟩ : syracuseStep 1141481 = 856111) B856111
theorem B3075155 : Blo 758332 3075155 := bstep (se 1 (by rfl) ⟨2306366, by rfl⟩ : syracuseStep 3075155 = 4612733) B4612733
theorem B13003901 : Blo 758332 13003901 := bstep (se 3 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 13003901 = 4876463) B4876463
theorem B1142057 : Blo 758332 1142057 := bstep (se 2 (by rfl) ⟨428271, by rfl⟩ : syracuseStep 1142057 = 856543) B856543
theorem B1142687 : Blo 758332 1142687 := bstep (se 1 (by rfl) ⟨857015, by rfl⟩ : syracuseStep 1142687 = 1714031) B1714031
theorem B1142825 : Blo 758332 1142825 := bstep (se 2 (by rfl) ⟨428559, by rfl⟩ : syracuseStep 1142825 = 857119) B857119
theorem B1142831 : Blo 758332 1142831 := bstep (se 1 (by rfl) ⟨857123, by rfl⟩ : syracuseStep 1142831 = 1714247) B1714247
theorem B1142855 : Blo 758332 1142855 := bstep (se 1 (by rfl) ⟨857141, by rfl⟩ : syracuseStep 1142855 = 1714283) B1714283
theorem B2879657 : Blo 758332 2879657 := bstep (se 2 (by rfl) ⟨1079871, by rfl⟩ : syracuseStep 2879657 = 2159743) B2159743
theorem B2879671 : Blo 758332 2879671 := bstep (se 1 (by rfl) ⟨2159753, by rfl⟩ : syracuseStep 2879671 = 4319507) B4319507
theorem B3240587 : Blo 758332 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B2880157 : Blo 758332 2880157 := bstep (se 3 (by rfl) ⟨540029, by rfl⟩ : syracuseStep 2880157 = 1080059) B1080059
theorem B1143455 : Blo 758332 1143455 := bstep (se 1 (by rfl) ⟨857591, by rfl⟩ : syracuseStep 1143455 = 1715183) B1715183
theorem B4617647 : Blo 758332 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B3241579 : Blo 758332 3241579 := bstep (se 1 (by rfl) ⟨2431184, by rfl⟩ : syracuseStep 3241579 = 4862369) B4862369
theorem B44365481 : Blo 758332 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B12352313 : Blo 758332 12352313 := bstep (se 2 (by rfl) ⟨4632117, by rfl⟩ : syracuseStep 12352313 = 9264235) B9264235
theorem B9764819 : Blo 758332 9764819 := bstep (se 1 (by rfl) ⟨7323614, by rfl⟩ : syracuseStep 9764819 = 14647229) B14647229
theorem B853375 : Blo 758332 853375 := bstep (se 1 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 853375 = 1280063) B1280063
theorem B854779 : Blo 758332 854779 := bstep (se 1 (by rfl) ⟨641084, by rfl⟩ : syracuseStep 854779 = 1282169) B1282169
theorem B3246911 : Blo 758332 3246911 := bstep (se 1 (by rfl) ⟨2435183, by rfl⟩ : syracuseStep 3246911 = 4870367) B4870367
theorem B35031959 : Blo 758332 35031959 := bstep (se 1 (by rfl) ⟨26273969, by rfl⟩ : syracuseStep 35031959 = 52547939) B52547939
theorem B1707803 : Blo 758332 1707803 := bstep (se 1 (by rfl) ⟨1280852, by rfl⟩ : syracuseStep 1707803 = 2561705) B2561705
theorem B1708073 : Blo 758332 1708073 := bstep (se 2 (by rfl) ⟨640527, by rfl⟩ : syracuseStep 1708073 = 1281055) B1281055
theorem B2887919 : Blo 758332 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B758399 : Blo 758332 758399 := bstep (se 1 (by rfl) ⟨568799, by rfl⟩ : syracuseStep 758399 = 1137599) B1137599
theorem B758463 : Blo 758332 758463 := bstep (se 1 (by rfl) ⟨568847, by rfl⟩ : syracuseStep 758463 = 1137695) B1137695
theorem B758783 : Blo 758332 758783 := bstep (se 1 (by rfl) ⟨569087, by rfl⟩ : syracuseStep 758783 = 1138175) B1138175
theorem B3085499 : Blo 758332 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B2561327 : Blo 758332 2561327 := bstep (se 1 (by rfl) ⟨1920995, by rfl⟩ : syracuseStep 2561327 = 3841991) B3841991
theorem B759087 : Blo 758332 759087 := bstep (se 1 (by rfl) ⟨569315, by rfl⟩ : syracuseStep 759087 = 1138631) B1138631
theorem B759111 : Blo 758332 759111 := bstep (se 1 (by rfl) ⟨569333, by rfl⟩ : syracuseStep 759111 = 1138667) B1138667
theorem B759199 : Blo 758332 759199 := bstep (se 1 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 759199 = 1138799) B1138799
theorem B1709495 : Blo 758332 1709495 := bstep (se 1 (by rfl) ⟨1282121, by rfl⟩ : syracuseStep 1709495 = 2564243) B2564243
theorem B3839561 : Blo 758332 3839561 := bstep (se 2 (by rfl) ⟨1439835, by rfl⟩ : syracuseStep 3839561 = 2879671) B2879671
theorem B1709927 : Blo 758332 1709927 := bstep (se 1 (by rfl) ⟨1282445, by rfl⟩ : syracuseStep 1709927 = 2564891) B2564891
theorem B3840209 : Blo 758332 3840209 := bstep (se 2 (by rfl) ⟨1440078, by rfl⟩ : syracuseStep 3840209 = 2880157) B2880157
theorem B760319 : Blo 758332 760319 := bstep (se 1 (by rfl) ⟨570239, by rfl⟩ : syracuseStep 760319 = 1140479) B1140479
theorem B760367 : Blo 758332 760367 := bstep (se 1 (by rfl) ⟨570275, by rfl⟩ : syracuseStep 760367 = 1140551) B1140551
theorem B1219367 : Blo 758332 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B760799 : Blo 758332 760799 := bstep (se 1 (by rfl) ⟨570599, by rfl⟩ : syracuseStep 760799 = 1141199) B1141199
theorem B1711097 : Blo 758332 1711097 := bstep (se 2 (by rfl) ⟨641661, by rfl⟩ : syracuseStep 1711097 = 1283323) B1283323
theorem B3841019 : Blo 758332 3841019 := bstep (se 1 (by rfl) ⟨2880764, by rfl⟩ : syracuseStep 3841019 = 5761529) B5761529
theorem B760859 : Blo 758332 760859 := bstep (se 1 (by rfl) ⟨570644, by rfl⟩ : syracuseStep 760859 = 1141289) B1141289
theorem B1285193 : Blo 758332 1285193 := bstep (se 2 (by rfl) ⟨481947, by rfl⟩ : syracuseStep 1285193 = 963895) B963895
theorem B2169983 : Blo 758332 2169983 := bstep (se 1 (by rfl) ⟨1627487, by rfl⟩ : syracuseStep 2169983 = 3254975) B3254975
theorem B760987 : Blo 758332 760987 := bstep (se 1 (by rfl) ⟨570740, by rfl⟩ : syracuseStep 760987 = 1141481) B1141481
theorem B761371 : Blo 758332 761371 := bstep (se 1 (by rfl) ⟨571028, by rfl⟩ : syracuseStep 761371 = 1142057) B1142057
theorem B761791 : Blo 758332 761791 := bstep (se 1 (by rfl) ⟨571343, by rfl⟩ : syracuseStep 761791 = 1142687) B1142687
theorem B761883 : Blo 758332 761883 := bstep (se 1 (by rfl) ⟨571412, by rfl⟩ : syracuseStep 761883 = 1142825) B1142825
theorem B761887 : Blo 758332 761887 := bstep (se 1 (by rfl) ⟨571415, by rfl⟩ : syracuseStep 761887 = 1142831) B1142831
theorem B761903 : Blo 758332 761903 := bstep (se 1 (by rfl) ⟨571427, by rfl⟩ : syracuseStep 761903 = 1142855) B1142855
theorem B5775623 : Blo 758332 5775623 := bstep (se 1 (by rfl) ⟨4331717, by rfl⟩ : syracuseStep 5775623 = 8663435) B8663435
theorem B762303 : Blo 758332 762303 := bstep (se 1 (by rfl) ⟨571727, by rfl⟩ : syracuseStep 762303 = 1143455) B1143455
theorem B194585159 : Blo 758332 194585159 := bstep (se 1 (by rfl) ⟨145938869, by rfl⟩ : syracuseStep 194585159 = 291877739) B291877739
theorem B2925181 : Blo 758332 2925181 := bstep (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) B1096943
theorem B1713095 : Blo 758332 1713095 := bstep (se 1 (by rfl) ⟨1284821, by rfl⟩ : syracuseStep 1713095 = 2569643) B2569643
theorem B2434799 : Blo 758332 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B8234875 : Blo 758332 8234875 := bstep (se 1 (by rfl) ⟨6176156, by rfl⟩ : syracuseStep 8234875 = 12352313) B12352313
theorem B4335727 : Blo 758332 4335727 := bstep (se 1 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 4335727 = 6503591) B6503591
theorem B1714463 : Blo 758332 1714463 := bstep (se 1 (by rfl) ⟨1285847, by rfl⟩ : syracuseStep 1714463 = 2571695) B2571695
theorem B9251243 : Blo 758332 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B3255623 : Blo 758332 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B2567807 : Blo 758332 2567807 := bstep (se 1 (by rfl) ⟨1925855, by rfl⟩ : syracuseStep 2567807 = 3851711) B3851711
theorem B2569535 : Blo 758332 2569535 := bstep (se 1 (by rfl) ⟨1927151, by rfl⟩ : syracuseStep 2569535 = 3854303) B3854303
theorem B37992563 : Blo 758332 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B13154723 : Blo 758332 13154723 := bstep (se 1 (by rfl) ⟨9866042, by rfl⟩ : syracuseStep 13154723 = 19732085) B19732085
theorem B1948519 : Blo 758332 1948519 := bstep (se 1 (by rfl) ⟨1461389, by rfl⟩ : syracuseStep 1948519 = 2922779) B2922779
theorem B3652735 : Blo 758332 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B5783399 : Blo 758332 5783399 := bstep (se 1 (by rfl) ⟨4337549, by rfl⟩ : syracuseStep 5783399 = 8675099) B8675099
theorem B6176681 : Blo 758332 6176681 := bstep (se 2 (by rfl) ⟨2316255, by rfl⟩ : syracuseStep 6176681 = 4632511) B4632511
theorem B9355961 : Blo 758332 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B3950375 : Blo 758332 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B2050103 : Blo 758332 2050103 := bstep (se 1 (by rfl) ⟨1537577, by rfl⟩ : syracuseStep 2050103 = 3075155) B3075155
theorem B8669267 : Blo 758332 8669267 := bstep (se 1 (by rfl) ⟨6501950, by rfl⟩ : syracuseStep 8669267 = 13003901) B13003901
theorem B6178913 : Blo 758332 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B1919771 : Blo 758332 1919771 := bstep (se 1 (by rfl) ⟨1439828, by rfl⟩ : syracuseStep 1919771 = 2879657) B2879657
theorem B29576987 : Blo 758332 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B9752723 : Blo 758332 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B3461885 : Blo 758332 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B3855113 : Blo 758332 3855113 := bstep (se 2 (by rfl) ⟨1445667, by rfl⟩ : syracuseStep 3855113 = 2891335) B2891335
theorem B6509879 : Blo 758332 6509879 := bstep (se 1 (by rfl) ⟨4882409, by rfl⟩ : syracuseStep 6509879 = 9764819) B9764819
theorem B3299059 : Blo 758332 3299059 := bstep (se 1 (by rfl) ⟨2474294, by rfl⟩ : syracuseStep 3299059 = 4948589) B4948589
theorem B2742781 : Blo 758332 2742781 := bstep (se 3 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 2742781 = 1028543) B1028543
theorem B8641565 : Blo 758332 8641565 := bstep (se 3 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 8641565 = 3240587) B3240587
theorem B2317751 : Blo 758332 2317751 := bstep (se 1 (by rfl) ⟨1738313, by rfl⟩ : syracuseStep 2317751 = 3476627) B3476627
theorem B1138559 : Blo 758332 1138559 := bstep (se 1 (by rfl) ⟨853919, by rfl⟩ : syracuseStep 1138559 = 1707839) B1707839
theorem B1368623 : Blo 758332 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B1140713 : Blo 758332 1140713 := bstep (se 2 (by rfl) ⟨427767, by rfl⟩ : syracuseStep 1140713 = 855535) B855535
theorem B10545437 : Blo 758332 10545437 := bstep (se 3 (by rfl) ⟨1977269, by rfl⟩ : syracuseStep 10545437 = 3954539) B3954539
theorem B1141055 : Blo 758332 1141055 := bstep (se 1 (by rfl) ⟨855791, by rfl⟩ : syracuseStep 1141055 = 1711583) B1711583
theorem B1141499 : Blo 758332 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B1928063 : Blo 758332 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B52620839 : Blo 758332 52620839 := bstep (se 1 (by rfl) ⟨39465629, by rfl⟩ : syracuseStep 52620839 = 78931259) B78931259
theorem B5468093 : Blo 758332 5468093 := bstep (se 3 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 5468093 = 2050535) B2050535
theorem B1143407 : Blo 758332 1143407 := bstep (se 1 (by rfl) ⟨857555, by rfl⟩ : syracuseStep 1143407 = 1715111) B1715111
theorem B4322105 : Blo 758332 4322105 := bstep (se 2 (by rfl) ⟨1620789, by rfl⟩ : syracuseStep 4322105 = 3241579) B3241579
theorem B4289561 : Blo 758332 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B3078431 : Blo 758332 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B8223241 : Blo 758332 8223241 := bstep (se 2 (by rfl) ⟨3083715, by rfl⟩ : syracuseStep 8223241 = 6167431) B6167431
theorem B3900241 : Blo 758332 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B1279847 : Blo 758332 1279847 := bstep (se 1 (by rfl) ⟨959885, by rfl⟩ : syracuseStep 1279847 = 1919771) B1919771
theorem B2164607 : Blo 758332 2164607 := bstep (se 1 (by rfl) ⟨1623455, by rfl⟩ : syracuseStep 2164607 = 3246911) B3246911
theorem B10979833 : Blo 758332 10979833 := bstep (se 2 (by rfl) ⟨4117437, by rfl⟩ : syracuseStep 10979833 = 8234875) B8234875
theorem B1707551 : Blo 758332 1707551 := bstep (se 1 (by rfl) ⟨1280663, by rfl⟩ : syracuseStep 1707551 = 2561327) B2561327
theorem B2559707 : Blo 758332 2559707 := bstep (se 1 (by rfl) ⟨1919780, by rfl⟩ : syracuseStep 2559707 = 3839561) B3839561
theorem B2560139 : Blo 758332 2560139 := bstep (se 1 (by rfl) ⟨1920104, by rfl⟩ : syracuseStep 2560139 = 3840209) B3840209
theorem B10392101 : Blo 758332 10392101 := bstep (se 4 (by rfl) ⟨974259, by rfl⟩ : syracuseStep 10392101 = 1948519) B1948519
theorem B2560679 : Blo 758332 2560679 := bstep (se 1 (by rfl) ⟨1920509, by rfl⟩ : syracuseStep 2560679 = 3841019) B3841019
theorem B856795 : Blo 758332 856795 := bstep (se 1 (by rfl) ⟨642596, by rfl⟩ : syracuseStep 856795 = 1285193) B1285193
theorem B1446655 : Blo 758332 1446655 := bstep (se 1 (by rfl) ⟨1084991, by rfl⟩ : syracuseStep 1446655 = 2169983) B2169983
theorem B1545167 : Blo 758332 1545167 := bstep (se 1 (by rfl) ⟨1158875, by rfl⟩ : syracuseStep 1545167 = 2317751) B2317751
theorem B759039 : Blo 758332 759039 := bstep (se 1 (by rfl) ⟨569279, by rfl⟩ : syracuseStep 759039 = 1138559) B1138559
theorem B28121165 : Blo 758332 28121165 := bstep (se 3 (by rfl) ⟨5272718, by rfl⟩ : syracuseStep 28121165 = 10545437) B10545437
theorem B760475 : Blo 758332 760475 := bstep (se 1 (by rfl) ⟨570356, by rfl⟩ : syracuseStep 760475 = 1140713) B1140713
theorem B760703 : Blo 758332 760703 := bstep (se 1 (by rfl) ⟨570527, by rfl⟩ : syracuseStep 760703 = 1141055) B1141055
theorem B6167495 : Blo 758332 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B760999 : Blo 758332 760999 := bstep (se 1 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 760999 = 1141499) B1141499
theorem B1285375 : Blo 758332 1285375 := bstep (se 1 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 1285375 = 1928063) B1928063
theorem B2170415 : Blo 758332 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B4398745 : Blo 758332 4398745 := bstep (se 2 (by rfl) ⟨1649529, by rfl⟩ : syracuseStep 4398745 = 3299059) B3299059
theorem B1711871 : Blo 758332 1711871 := bstep (se 1 (by rfl) ⟨1283903, by rfl⟩ : syracuseStep 1711871 = 2567807) B2567807
theorem B3645395 : Blo 758332 3645395 := bstep (se 1 (by rfl) ⟨2734046, by rfl⟩ : syracuseStep 3645395 = 5468093) B5468093
theorem B762271 : Blo 758332 762271 := bstep (se 1 (by rfl) ⟨571703, by rfl⟩ : syracuseStep 762271 = 1143407) B1143407
theorem B2859707 : Blo 758332 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B1713023 : Blo 758332 1713023 := bstep (se 1 (by rfl) ⟨1284767, by rfl⟩ : syracuseStep 1713023 = 2569535) B2569535
theorem B6237307 : Blo 758332 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B5779511 : Blo 758332 5779511 := bstep (se 1 (by rfl) ⟨4334633, by rfl⟩ : syracuseStep 5779511 = 8669267) B8669267
theorem B6501815 : Blo 758332 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B5780969 : Blo 758332 5780969 := bstep (se 2 (by rfl) ⟨2167863, by rfl⟩ : syracuseStep 5780969 = 4335727) B4335727
theorem B2307923 : Blo 758332 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B2570075 : Blo 758332 2570075 := bstep (se 1 (by rfl) ⟨1927556, by rfl⟩ : syracuseStep 2570075 = 3855113) B3855113
theorem B4339919 : Blo 758332 4339919 := bstep (se 1 (by rfl) ⟨3254939, by rfl⟩ : syracuseStep 4339919 = 6509879) B6509879
theorem B3850415 : Blo 758332 3850415 := bstep (se 1 (by rfl) ⟨2887811, by rfl⟩ : syracuseStep 3850415 = 5775623) B5775623
theorem B1623199 : Blo 758332 1623199 := bstep (se 1 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 1623199 = 2434799) B2434799
theorem B35080559 : Blo 758332 35080559 := bstep (se 1 (by rfl) ⟨26310419, by rfl⟩ : syracuseStep 35080559 = 52620839) B52620839
theorem B3657041 : Blo 758332 3657041 := bstep (se 2 (by rfl) ⟨1371390, by rfl⟩ : syracuseStep 3657041 = 2742781) B2742781
theorem B10964321 : Blo 758332 10964321 := bstep (se 2 (by rfl) ⟨4111620, by rfl⟩ : syracuseStep 10964321 = 8223241) B8223241
theorem B4870313 : Blo 758332 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B2052287 : Blo 758332 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B8769815 : Blo 758332 8769815 := bstep (se 1 (by rfl) ⟨6577361, by rfl⟩ : syracuseStep 8769815 = 13154723) B13154723
theorem B3855599 : Blo 758332 3855599 := bstep (se 1 (by rfl) ⟨2891699, by rfl⟩ : syracuseStep 3855599 = 5783399) B5783399
theorem B4117787 : Blo 758332 4117787 := bstep (se 1 (by rfl) ⟨3088340, by rfl⟩ : syracuseStep 4117787 = 6176681) B6176681
theorem B1366735 : Blo 758332 1366735 := bstep (se 1 (by rfl) ⟨1025051, by rfl⟩ : syracuseStep 1366735 = 2050103) B2050103
theorem B4119275 : Blo 758332 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B1137833 : Blo 758332 1137833 := bstep (se 2 (by rfl) ⟨426687, by rfl⟩ : syracuseStep 1137833 = 853375) B853375
theorem B23354639 : Blo 758332 23354639 := bstep (se 1 (by rfl) ⟨17515979, by rfl⟩ : syracuseStep 23354639 = 35031959) B35031959
theorem B19717991 : Blo 758332 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B1138535 : Blo 758332 1138535 := bstep (se 1 (by rfl) ⟨853901, by rfl⟩ : syracuseStep 1138535 = 1707803) B1707803
theorem B1138715 : Blo 758332 1138715 := bstep (se 1 (by rfl) ⟨854036, by rfl⟩ : syracuseStep 1138715 = 1708073) B1708073
theorem B1925279 : Blo 758332 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B2056999 : Blo 758332 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B1139663 : Blo 758332 1139663 := bstep (se 1 (by rfl) ⟨854747, by rfl⟩ : syracuseStep 1139663 = 1709495) B1709495
theorem B1139705 : Blo 758332 1139705 := bstep (se 2 (by rfl) ⟨427389, by rfl⟩ : syracuseStep 1139705 = 854779) B854779
theorem B1139951 : Blo 758332 1139951 := bstep (se 1 (by rfl) ⟨854963, by rfl⟩ : syracuseStep 1139951 = 1709927) B1709927
theorem B812911 : Blo 758332 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B1140731 : Blo 758332 1140731 := bstep (se 1 (by rfl) ⟨855548, by rfl⟩ : syracuseStep 1140731 = 1711097) B1711097
theorem B5761043 : Blo 758332 5761043 := bstep (se 1 (by rfl) ⟨4320782, by rfl⟩ : syracuseStep 5761043 = 8641565) B8641565
theorem B912415 : Blo 758332 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B129723439 : Blo 758332 129723439 := bstep (se 1 (by rfl) ⟨97292579, by rfl⟩ : syracuseStep 129723439 = 194585159) B194585159
theorem B1142063 : Blo 758332 1142063 := bstep (se 1 (by rfl) ⟨856547, by rfl⟩ : syracuseStep 1142063 = 1713095) B1713095
theorem B1142975 : Blo 758332 1142975 := bstep (se 1 (by rfl) ⟨857231, by rfl⟩ : syracuseStep 1142975 = 1714463) B1714463
theorem B42137333 : Blo 758332 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B2881403 : Blo 758332 2881403 := bstep (se 1 (by rfl) ⟨2161052, by rfl⟩ : syracuseStep 2881403 = 4322105) B4322105
theorem B25328375 : Blo 758332 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B853231 : Blo 758332 853231 := bstep (se 1 (by rfl) ⟨639923, by rfl⟩ : syracuseStep 853231 = 1279847) B1279847
theorem B1443071 : Blo 758332 1443071 := bstep (se 1 (by rfl) ⟨1082303, by rfl⟩ : syracuseStep 1443071 = 2164607) B2164607
theorem B2164265 : Blo 758332 2164265 := bstep (se 2 (by rfl) ⟨811599, by rfl⟩ : syracuseStep 2164265 = 1623199) B1623199
theorem B7309547 : Blo 758332 7309547 := bstep (se 1 (by rfl) ⟨5482160, by rfl⟩ : syracuseStep 7309547 = 10964321) B10964321
theorem B1706471 : Blo 758332 1706471 := bstep (se 1 (by rfl) ⟨1279853, by rfl⟩ : syracuseStep 1706471 = 2559707) B2559707
theorem B1083881 : Blo 758332 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B1706759 : Blo 758332 1706759 := bstep (se 1 (by rfl) ⟨1280069, by rfl⟩ : syracuseStep 1706759 = 2560139) B2560139
theorem B3246875 : Blo 758332 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B1707119 : Blo 758332 1707119 := bstep (se 1 (by rfl) ⟨1280339, by rfl⟩ : syracuseStep 1707119 = 2560679) B2560679
theorem B1216553 : Blo 758332 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B18747443 : Blo 758332 18747443 := bstep (se 1 (by rfl) ⟨14060582, by rfl⟩ : syracuseStep 18747443 = 28121165) B28121165
theorem B758555 : Blo 758332 758555 := bstep (se 1 (by rfl) ⟨568916, by rfl⟩ : syracuseStep 758555 = 1137833) B1137833
theorem B15569759 : Blo 758332 15569759 := bstep (se 1 (by rfl) ⟨11677319, by rfl⟩ : syracuseStep 15569759 = 23354639) B23354639
theorem B13145327 : Blo 758332 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B759023 : Blo 758332 759023 := bstep (se 1 (by rfl) ⟨569267, by rfl⟩ : syracuseStep 759023 = 1138535) B1138535
theorem B2430263 : Blo 758332 2430263 := bstep (se 1 (by rfl) ⟨1822697, by rfl⟩ : syracuseStep 2430263 = 3645395) B3645395
theorem B759143 : Blo 758332 759143 := bstep (se 1 (by rfl) ⟨569357, by rfl⟩ : syracuseStep 759143 = 1138715) B1138715
theorem B1283519 : Blo 758332 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B1906471 : Blo 758332 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B759775 : Blo 758332 759775 := bstep (se 1 (by rfl) ⟨569831, by rfl⟩ : syracuseStep 759775 = 1139663) B1139663
theorem B33265637 : Blo 758332 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B759803 : Blo 758332 759803 := bstep (se 1 (by rfl) ⟨569852, by rfl⟩ : syracuseStep 759803 = 1139705) B1139705
theorem B759967 : Blo 758332 759967 := bstep (se 1 (by rfl) ⟨569975, by rfl⟩ : syracuseStep 759967 = 1139951) B1139951
theorem B760487 : Blo 758332 760487 := bstep (se 1 (by rfl) ⟨570365, by rfl⟩ : syracuseStep 760487 = 1140731) B1140731
theorem B3840695 : Blo 758332 3840695 := bstep (se 1 (by rfl) ⟨2880521, by rfl⟩ : syracuseStep 3840695 = 5761043) B5761043
theorem B10984733 : Blo 758332 10984733 := bstep (se 3 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 10984733 = 4119275) B4119275
theorem B761375 : Blo 758332 761375 := bstep (se 1 (by rfl) ⟨571031, by rfl⟩ : syracuseStep 761375 = 1142063) B1142063
theorem B761983 : Blo 758332 761983 := bstep (se 1 (by rfl) ⟨571487, by rfl⟩ : syracuseStep 761983 = 1142975) B1142975
theorem B4334543 : Blo 758332 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B28091555 : Blo 758332 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B1713383 : Blo 758332 1713383 := bstep (se 1 (by rfl) ⟨1285037, by rfl⟩ : syracuseStep 1713383 = 2570075) B2570075
theorem B2893279 : Blo 758332 2893279 := bstep (se 1 (by rfl) ⟨2169959, by rfl⟩ : syracuseStep 2893279 = 4339919) B4339919
theorem B1713833 : Blo 758332 1713833 := bstep (se 2 (by rfl) ⟨642687, by rfl⟩ : syracuseStep 1713833 = 1285375) B1285375
theorem B16885583 : Blo 758332 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B2566943 : Blo 758332 2566943 := bstep (se 1 (by rfl) ⟨1925207, by rfl⟩ : syracuseStep 2566943 = 3850415) B3850415
theorem B2438027 : Blo 758332 2438027 := bstep (se 1 (by rfl) ⟨1828520, by rfl⟩ : syracuseStep 2438027 = 3657041) B3657041
theorem B5846543 : Blo 758332 5846543 := bstep (se 1 (by rfl) ⟨4384907, by rfl⟩ : syracuseStep 5846543 = 8769815) B8769815
theorem B6928067 : Blo 758332 6928067 := bstep (se 1 (by rfl) ⟨5196050, by rfl⟩ : syracuseStep 6928067 = 10392101) B10392101
theorem B2570399 : Blo 758332 2570399 := bstep (se 1 (by rfl) ⟨1927799, by rfl⟩ : syracuseStep 2570399 = 3855599) B3855599
theorem B172964585 : Blo 758332 172964585 := bstep (se 2 (by rfl) ⟨64861719, by rfl⟩ : syracuseStep 172964585 = 129723439) B129723439
theorem B4111663 : Blo 758332 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B3853007 : Blo 758332 3853007 := bstep (se 1 (by rfl) ⟨2889755, by rfl⟩ : syracuseStep 3853007 = 5779511) B5779511
theorem B1822313 : Blo 758332 1822313 := bstep (se 2 (by rfl) ⟨683367, by rfl⟩ : syracuseStep 1822313 = 1366735) B1366735
theorem B3853979 : Blo 758332 3853979 := bstep (se 1 (by rfl) ⟨2890484, by rfl⟩ : syracuseStep 3853979 = 5780969) B5780969
theorem B1920935 : Blo 758332 1920935 := bstep (se 1 (by rfl) ⟨1440701, by rfl⟩ : syracuseStep 1920935 = 2881403) B2881403
theorem B5787773 : Blo 758332 5787773 := bstep (se 3 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 5787773 = 2170415) B2170415
theorem B2742665 : Blo 758332 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B23387039 : Blo 758332 23387039 := bstep (se 1 (by rfl) ⟨17540279, by rfl⟩ : syracuseStep 23387039 = 35080559) B35080559
theorem B1138367 : Blo 758332 1138367 := bstep (se 1 (by rfl) ⟨853775, by rfl⟩ : syracuseStep 1138367 = 1707551) B1707551
theorem B4120445 : Blo 758332 4120445 := bstep (se 3 (by rfl) ⟨772583, by rfl⟩ : syracuseStep 4120445 = 1545167) B1545167
theorem B1368191 : Blo 758332 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B14639777 : Blo 758332 14639777 := bstep (se 2 (by rfl) ⟨5489916, by rfl⟩ : syracuseStep 14639777 = 10979833) B10979833
theorem B2745191 : Blo 758332 2745191 := bstep (se 1 (by rfl) ⟨2058893, by rfl⟩ : syracuseStep 2745191 = 4117787) B4117787
theorem B20801285 : Blo 758332 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B1141247 : Blo 758332 1141247 := bstep (se 1 (by rfl) ⟨855935, by rfl⟩ : syracuseStep 1141247 = 1711871) B1711871
theorem B1142015 : Blo 758332 1142015 := bstep (se 1 (by rfl) ⟨856511, by rfl⟩ : syracuseStep 1142015 = 1713023) B1713023
theorem B1142393 : Blo 758332 1142393 := bstep (se 2 (by rfl) ⟨428397, by rfl⟩ : syracuseStep 1142393 = 856795) B856795
theorem B1928873 : Blo 758332 1928873 := bstep (se 2 (by rfl) ⟨723327, by rfl⟩ : syracuseStep 1928873 = 1446655) B1446655
theorem B1538615 : Blo 758332 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B5864993 : Blo 758332 5864993 := bstep (se 2 (by rfl) ⟨2199372, by rfl⟩ : syracuseStep 5864993 = 4398745) B4398745
theorem B3244141 : Blo 758332 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B1442843 : Blo 758332 1442843 := bstep (se 1 (by rfl) ⟨1082132, by rfl⟩ : syracuseStep 1442843 = 2164265) B2164265
theorem B2164583 : Blo 758332 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B1214875 : Blo 758332 1214875 := bstep (se 1 (by rfl) ⟨911156, by rfl⟩ : syracuseStep 1214875 = 1822313) B1822313
theorem B1280623 : Blo 758332 1280623 := bstep (se 1 (by rfl) ⟨960467, by rfl⟩ : syracuseStep 1280623 = 1920935) B1920935
theorem B855679 : Blo 758332 855679 := bstep (se 1 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 855679 = 1283519) B1283519
theorem B2560463 : Blo 758332 2560463 := bstep (se 1 (by rfl) ⟨1920347, by rfl⟩ : syracuseStep 2560463 = 3840695) B3840695
theorem B758911 : Blo 758332 758911 := bstep (se 1 (by rfl) ⟨569183, by rfl⟩ : syracuseStep 758911 = 1138367) B1138367
theorem B2889695 : Blo 758332 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B7313773 : Blo 758332 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B13867523 : Blo 758332 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B2890349 : Blo 758332 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B4102973 : Blo 758332 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B760831 : Blo 758332 760831 := bstep (se 1 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 760831 = 1141247) B1141247
theorem B1711295 : Blo 758332 1711295 := bstep (se 1 (by rfl) ⟨1283471, by rfl⟩ : syracuseStep 1711295 = 2566943) B2566943
theorem B761343 : Blo 758332 761343 := bstep (se 1 (by rfl) ⟨571007, by rfl⟩ : syracuseStep 761343 = 1142015) B1142015
theorem B761595 : Blo 758332 761595 := bstep (se 1 (by rfl) ⟨571196, by rfl⟩ : syracuseStep 761595 = 1142393) B1142393
theorem B1285915 : Blo 758332 1285915 := bstep (se 1 (by rfl) ⟨964436, by rfl⟩ : syracuseStep 1285915 = 1928873) B1928873
theorem B1713599 : Blo 758332 1713599 := bstep (se 1 (by rfl) ⟨1285199, by rfl⟩ : syracuseStep 1713599 = 2570399) B2570399
theorem B5482217 : Blo 758332 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B3909995 : Blo 758332 3909995 := bstep (se 1 (by rfl) ⟨2932496, by rfl⟩ : syracuseStep 3909995 = 5864993) B5864993
theorem B3648509 : Blo 758332 3648509 := bstep (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) B1368191
theorem B962047 : Blo 758332 962047 := bstep (se 1 (by rfl) ⟨721535, by rfl⟩ : syracuseStep 962047 = 1443071) B1443071
theorem B2568671 : Blo 758332 2568671 := bstep (se 1 (by rfl) ⟨1926503, by rfl⟩ : syracuseStep 2568671 = 3853007) B3853007
theorem B2569319 : Blo 758332 2569319 := bstep (se 1 (by rfl) ⟨1926989, by rfl⟩ : syracuseStep 2569319 = 3853979) B3853979
theorem B12498295 : Blo 758332 12498295 := bstep (se 1 (by rfl) ⟨9373721, by rfl⟩ : syracuseStep 12498295 = 18747443) B18747443
theorem B8763551 : Blo 758332 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B1620175 : Blo 758332 1620175 := bstep (se 1 (by rfl) ⟨1215131, by rfl⟩ : syracuseStep 1620175 = 2430263) B2430263
theorem B7323155 : Blo 758332 7323155 := bstep (se 1 (by rfl) ⟨5492366, by rfl⟩ : syracuseStep 7323155 = 10984733) B10984733
theorem B18727703 : Blo 758332 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B11257055 : Blo 758332 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B2541961 : Blo 758332 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B1625351 : Blo 758332 1625351 := bstep (se 1 (by rfl) ⟨1219013, by rfl⟩ : syracuseStep 1625351 = 2438027) B2438027
theorem B4873031 : Blo 758332 4873031 := bstep (se 1 (by rfl) ⟨3654773, by rfl⟩ : syracuseStep 4873031 = 7309547) B7309547
theorem B1137641 : Blo 758332 1137641 := bstep (se 2 (by rfl) ⟨426615, by rfl⟩ : syracuseStep 1137641 = 853231) B853231
theorem B1137647 : Blo 758332 1137647 := bstep (se 1 (by rfl) ⟨853235, by rfl⟩ : syracuseStep 1137647 = 1706471) B1706471
theorem B1137839 : Blo 758332 1137839 := bstep (se 1 (by rfl) ⟨853379, by rfl⟩ : syracuseStep 1137839 = 1706759) B1706759
theorem B3857705 : Blo 758332 3857705 := bstep (se 2 (by rfl) ⟨1446639, by rfl⟩ : syracuseStep 3857705 = 2893279) B2893279
theorem B1138079 : Blo 758332 1138079 := bstep (se 1 (by rfl) ⟨853559, by rfl⟩ : syracuseStep 1138079 = 1707119) B1707119
theorem B3858515 : Blo 758332 3858515 := bstep (se 1 (by rfl) ⟨2893886, by rfl⟩ : syracuseStep 3858515 = 5787773) B5787773
theorem B10379839 : Blo 758332 10379839 := bstep (se 1 (by rfl) ⟨7784879, by rfl⟩ : syracuseStep 10379839 = 15569759) B15569759
theorem B22177091 : Blo 758332 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B15591359 : Blo 758332 15591359 := bstep (se 1 (by rfl) ⟨11693519, by rfl⟩ : syracuseStep 15591359 = 23387039) B23387039
theorem B2746963 : Blo 758332 2746963 := bstep (se 1 (by rfl) ⟨2060222, by rfl⟩ : syracuseStep 2746963 = 4120445) B4120445
theorem B9759851 : Blo 758332 9759851 := bstep (se 1 (by rfl) ⟨7319888, by rfl⟩ : syracuseStep 9759851 = 14639777) B14639777
theorem B1830127 : Blo 758332 1830127 := bstep (se 1 (by rfl) ⟨1372595, by rfl⟩ : syracuseStep 1830127 = 2745191) B2745191
theorem B1142255 : Blo 758332 1142255 := bstep (se 1 (by rfl) ⟨856691, by rfl⟩ : syracuseStep 1142255 = 1713383) B1713383
theorem B1142555 : Blo 758332 1142555 := bstep (se 1 (by rfl) ⟨856916, by rfl⟩ : syracuseStep 1142555 = 1713833) B1713833
theorem B461238893 : Blo 758332 461238893 := bstep (se 3 (by rfl) ⟨86482292, by rfl⟩ : syracuseStep 461238893 = 172964585) B172964585
theorem B3897695 : Blo 758332 3897695 := bstep (se 1 (by rfl) ⟨2923271, by rfl⟩ : syracuseStep 3897695 = 5846543) B5846543
theorem B4618711 : Blo 758332 4618711 := bstep (se 1 (by rfl) ⟨3464033, by rfl⟩ : syracuseStep 4618711 = 6928067) B6928067
theorem B4325521 : Blo 758332 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B12485135 : Blo 758332 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B7504703 : Blo 758332 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B1706975 : Blo 758332 1706975 := bstep (se 1 (by rfl) ⟨1280231, by rfl⟩ : syracuseStep 1706975 = 2560463) B2560463
theorem B1707497 : Blo 758332 1707497 := bstep (se 2 (by rfl) ⟨640311, by rfl⟩ : syracuseStep 1707497 = 1280623) B1280623
theorem B9245015 : Blo 758332 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B3248687 : Blo 758332 3248687 := bstep (se 1 (by rfl) ⟨2436515, by rfl⟩ : syracuseStep 3248687 = 4873031) B4873031
theorem B758427 : Blo 758332 758427 := bstep (se 1 (by rfl) ⟨568820, by rfl⟩ : syracuseStep 758427 = 1137641) B1137641
theorem B758431 : Blo 758332 758431 := bstep (se 1 (by rfl) ⟨568823, by rfl⟩ : syracuseStep 758431 = 1137647) B1137647
theorem B1282729 : Blo 758332 1282729 := bstep (se 2 (by rfl) ⟨481023, by rfl⟩ : syracuseStep 1282729 = 962047) B962047
theorem B758559 : Blo 758332 758559 := bstep (se 1 (by rfl) ⟨568919, by rfl⟩ : syracuseStep 758559 = 1137839) B1137839
theorem B5772221 : Blo 758332 5772221 := bstep (se 3 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 5772221 = 2164583) B2164583
theorem B758719 : Blo 758332 758719 := bstep (se 1 (by rfl) ⟨569039, by rfl⟩ : syracuseStep 758719 = 1138079) B1138079
theorem B10394239 : Blo 758332 10394239 := bstep (se 1 (by rfl) ⟨7795679, by rfl⟩ : syracuseStep 10394239 = 15591359) B15591359
theorem B2432339 : Blo 758332 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B761503 : Blo 758332 761503 := bstep (se 1 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 761503 = 1142255) B1142255
theorem B761703 : Blo 758332 761703 := bstep (se 1 (by rfl) ⟨571277, by rfl⟩ : syracuseStep 761703 = 1142555) B1142555
theorem B1712447 : Blo 758332 1712447 := bstep (se 1 (by rfl) ⟨1284335, by rfl⟩ : syracuseStep 1712447 = 2568671) B2568671
theorem B4334269 : Blo 758332 4334269 := bstep (se 3 (by rfl) ⟨812675, by rfl⟩ : syracuseStep 4334269 = 1625351) B1625351
theorem B1712879 : Blo 758332 1712879 := bstep (se 1 (by rfl) ⟨1284659, by rfl⟩ : syracuseStep 1712879 = 2569319) B2569319
theorem B5842367 : Blo 758332 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B2598463 : Blo 758332 2598463 := bstep (se 1 (by rfl) ⟨1948847, by rfl⟩ : syracuseStep 2598463 = 3897695) B3897695
theorem B1714553 : Blo 758332 1714553 := bstep (se 2 (by rfl) ⟨642957, by rfl⟩ : syracuseStep 1714553 = 1285915) B1285915
theorem B961895 : Blo 758332 961895 := bstep (se 1 (by rfl) ⟨721421, by rfl⟩ : syracuseStep 961895 = 1442843) B1442843
theorem B13839785 : Blo 758332 13839785 := bstep (se 2 (by rfl) ⟨5189919, by rfl⟩ : syracuseStep 13839785 = 10379839) B10379839
theorem B1619833 : Blo 758332 1619833 := bstep (se 2 (by rfl) ⟨607437, by rfl⟩ : syracuseStep 1619833 = 1214875) B1214875
theorem B2440169 : Blo 758332 2440169 := bstep (se 2 (by rfl) ⟨915063, by rfl⟩ : syracuseStep 2440169 = 1830127) B1830127
theorem B2735315 : Blo 758332 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B2571803 : Blo 758332 2571803 := bstep (se 1 (by rfl) ⟨1928852, by rfl⟩ : syracuseStep 2571803 = 3857705) B3857705
theorem B2572343 : Blo 758332 2572343 := bstep (se 1 (by rfl) ⟨1929257, by rfl⟩ : syracuseStep 2572343 = 3858515) B3858515
theorem B3654811 : Blo 758332 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B2606663 : Blo 758332 2606663 := bstep (se 1 (by rfl) ⟨1954997, by rfl⟩ : syracuseStep 2606663 = 3909995) B3909995
theorem B16664393 : Blo 758332 16664393 := bstep (se 2 (by rfl) ⟨6249147, by rfl⟩ : syracuseStep 16664393 = 12498295) B12498295
theorem B6506567 : Blo 758332 6506567 := bstep (se 1 (by rfl) ⟨4879925, by rfl⟩ : syracuseStep 6506567 = 9759851) B9759851
theorem B9751697 : Blo 758332 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B13557125 : Blo 758332 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B3662617 : Blo 758332 3662617 := bstep (se 2 (by rfl) ⟨1373481, by rfl⟩ : syracuseStep 3662617 = 2746963) B2746963
theorem B59138909 : Blo 758332 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B1926463 : Blo 758332 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B1926899 : Blo 758332 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B1140863 : Blo 758332 1140863 := bstep (se 1 (by rfl) ⟨855647, by rfl⟩ : syracuseStep 1140863 = 1711295) B1711295
theorem B1140905 : Blo 758332 1140905 := bstep (se 2 (by rfl) ⟨427839, by rfl⟩ : syracuseStep 1140905 = 855679) B855679
theorem B1142399 : Blo 758332 1142399 := bstep (se 1 (by rfl) ⟨856799, by rfl⟩ : syracuseStep 1142399 = 1713599) B1713599
theorem B2160233 : Blo 758332 2160233 := bstep (se 2 (by rfl) ⟨810087, by rfl⟩ : syracuseStep 2160233 = 1620175) B1620175
theorem B307492595 : Blo 758332 307492595 := bstep (se 1 (by rfl) ⟨230619446, by rfl⟩ : syracuseStep 307492595 = 461238893) B461238893
theorem B6158281 : Blo 758332 6158281 := bstep (se 2 (by rfl) ⟨2309355, by rfl⟩ : syracuseStep 6158281 = 4618711) B4618711
theorem B4882103 : Blo 758332 4882103 := bstep (se 1 (by rfl) ⟨3661577, by rfl⟩ : syracuseStep 4882103 = 7323155) B7323155
theorem B5767361 : Blo 758332 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B4883489 : Blo 758332 4883489 := bstep (se 2 (by rfl) ⟨1831308, by rfl⟩ : syracuseStep 4883489 = 3662617) B3662617
theorem B1737775 : Blo 758332 1737775 := bstep (se 1 (by rfl) ⟨1303331, by rfl⟩ : syracuseStep 1737775 = 2606663) B2606663
theorem B11109595 : Blo 758332 11109595 := bstep (se 1 (by rfl) ⟨8332196, by rfl⟩ : syracuseStep 11109595 = 16664393) B16664393
theorem B33293693 : Blo 758332 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B6163343 : Blo 758332 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B2165791 : Blo 758332 2165791 := bstep (se 1 (by rfl) ⟨1624343, by rfl⟩ : syracuseStep 2165791 = 3248687) B3248687
theorem B39425939 : Blo 758332 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B1710305 : Blo 758332 1710305 := bstep (se 2 (by rfl) ⟨641364, by rfl⟩ : syracuseStep 1710305 = 1282729) B1282729
theorem B1284599 : Blo 758332 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B760575 : Blo 758332 760575 := bstep (se 1 (by rfl) ⟨570431, by rfl⟩ : syracuseStep 760575 = 1140863) B1140863
theorem B760603 : Blo 758332 760603 := bstep (se 1 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 760603 = 1140905) B1140905
theorem B761599 : Blo 758332 761599 := bstep (se 1 (by rfl) ⟨571199, by rfl⟩ : syracuseStep 761599 = 1142399) B1142399
theorem B2565053 : Blo 758332 2565053 := bstep (se 3 (by rfl) ⟨480947, by rfl⟩ : syracuseStep 2565053 = 961895) B961895
theorem B1714535 : Blo 758332 1714535 := bstep (se 1 (by rfl) ⟨1285901, by rfl⟩ : syracuseStep 1714535 = 2571803) B2571803
theorem B3254735 : Blo 758332 3254735 := bstep (se 1 (by rfl) ⟨2441051, by rfl⟩ : syracuseStep 3254735 = 4882103) B4882103
theorem B1714895 : Blo 758332 1714895 := bstep (se 1 (by rfl) ⟨1286171, by rfl⟩ : syracuseStep 1714895 = 2572343) B2572343
theorem B5779025 : Blo 758332 5779025 := bstep (se 2 (by rfl) ⟨2167134, by rfl⟩ : syracuseStep 5779025 = 4334269) B4334269
theorem B4337711 : Blo 758332 4337711 := bstep (se 1 (by rfl) ⟨3253283, by rfl⟩ : syracuseStep 4337711 = 6506567) B6506567
theorem B2568617 : Blo 758332 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B6501131 : Blo 758332 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B3848147 : Blo 758332 3848147 := bstep (se 1 (by rfl) ⟨2886110, by rfl⟩ : syracuseStep 3848147 = 5772221) B5772221
theorem B1621559 : Blo 758332 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B9226523 : Blo 758332 9226523 := bstep (se 1 (by rfl) ⟨6919892, by rfl⟩ : syracuseStep 9226523 = 13839785) B13839785
theorem B8211041 : Blo 758332 8211041 := bstep (se 2 (by rfl) ⟨3079140, by rfl⟩ : syracuseStep 8211041 = 6158281) B6158281
theorem B1626779 : Blo 758332 1626779 := bstep (se 1 (by rfl) ⟨1220084, by rfl⟩ : syracuseStep 1626779 = 2440169) B2440169
theorem B1823543 : Blo 758332 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B5003135 : Blo 758332 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B4873081 : Blo 758332 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B1137983 : Blo 758332 1137983 := bstep (se 1 (by rfl) ⟨853487, by rfl⟩ : syracuseStep 1137983 = 1706975) B1706975
theorem B3464617 : Blo 758332 3464617 := bstep (se 2 (by rfl) ⟨1299231, by rfl⟩ : syracuseStep 3464617 = 2598463) B2598463
theorem B1138331 : Blo 758332 1138331 := bstep (se 1 (by rfl) ⟨853748, by rfl⟩ : syracuseStep 1138331 = 1707497) B1707497
theorem B9038083 : Blo 758332 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B1141631 : Blo 758332 1141631 := bstep (se 1 (by rfl) ⟨856223, by rfl⟩ : syracuseStep 1141631 = 1712447) B1712447
theorem B1141919 : Blo 758332 1141919 := bstep (se 1 (by rfl) ⟨856439, by rfl⟩ : syracuseStep 1141919 = 1712879) B1712879
theorem B3894911 : Blo 758332 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B1143035 : Blo 758332 1143035 := bstep (se 1 (by rfl) ⟨857276, by rfl⟩ : syracuseStep 1143035 = 1714553) B1714553
theorem B2159777 : Blo 758332 2159777 := bstep (se 2 (by rfl) ⟨809916, by rfl⟩ : syracuseStep 2159777 = 1619833) B1619833
theorem B13858985 : Blo 758332 13858985 := bstep (se 2 (by rfl) ⟨5197119, by rfl⟩ : syracuseStep 13858985 = 10394239) B10394239
theorem B1440155 : Blo 758332 1440155 := bstep (se 1 (by rfl) ⟨1080116, by rfl⟩ : syracuseStep 1440155 = 2160233) B2160233
theorem B204995063 : Blo 758332 204995063 := bstep (se 1 (by rfl) ⟨153746297, by rfl⟩ : syracuseStep 204995063 = 307492595) B307492595
theorem B14812793 : Blo 758332 14812793 := bstep (se 2 (by rfl) ⟨5554797, by rfl⟩ : syracuseStep 14812793 = 11109595) B11109595
theorem B5474027 : Blo 758332 5474027 := bstep (se 1 (by rfl) ⟨4105520, by rfl⟩ : syracuseStep 5474027 = 8211041) B8211041
theorem B1084519 : Blo 758332 1084519 := bstep (se 1 (by rfl) ⟨813389, by rfl⟩ : syracuseStep 1084519 = 1626779) B1626779
theorem B1215695 : Blo 758332 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B26283959 : Blo 758332 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B2887721 : Blo 758332 2887721 := bstep (se 2 (by rfl) ⟨1082895, by rfl⟩ : syracuseStep 2887721 = 2165791) B2165791
theorem B856399 : Blo 758332 856399 := bstep (se 1 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 856399 = 1284599) B1284599
theorem B758655 : Blo 758332 758655 := bstep (se 1 (by rfl) ⟨568991, by rfl⟩ : syracuseStep 758655 = 1137983) B1137983
theorem B758887 : Blo 758332 758887 := bstep (se 1 (by rfl) ⟨569165, by rfl⟩ : syracuseStep 758887 = 1138331) B1138331
theorem B1710035 : Blo 758332 1710035 := bstep (se 1 (by rfl) ⟨1282526, by rfl⟩ : syracuseStep 1710035 = 2565053) B2565053
theorem B2169823 : Blo 758332 2169823 := bstep (se 1 (by rfl) ⟨1627367, by rfl⟩ : syracuseStep 2169823 = 3254735) B3254735
theorem B761087 : Blo 758332 761087 := bstep (se 1 (by rfl) ⟨570815, by rfl⟩ : syracuseStep 761087 = 1141631) B1141631
theorem B761279 : Blo 758332 761279 := bstep (se 1 (by rfl) ⟨570959, by rfl⟩ : syracuseStep 761279 = 1141919) B1141919
theorem B2596607 : Blo 758332 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B2891807 : Blo 758332 2891807 := bstep (se 1 (by rfl) ⟨2168855, by rfl⟩ : syracuseStep 2891807 = 4337711) B4337711
theorem B762023 : Blo 758332 762023 := bstep (se 1 (by rfl) ⟨571517, by rfl⟩ : syracuseStep 762023 = 1143035) B1143035
theorem B1712411 : Blo 758332 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B4334087 : Blo 758332 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B6497441 : Blo 758332 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B2565431 : Blo 758332 2565431 := bstep (se 1 (by rfl) ⟨1924073, by rfl⟩ : syracuseStep 2565431 = 3848147) B3848147
theorem B960103 : Blo 758332 960103 := bstep (se 1 (by rfl) ⟨720077, by rfl⟩ : syracuseStep 960103 = 1440155) B1440155
theorem B3844907 : Blo 758332 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B3255659 : Blo 758332 3255659 := bstep (se 1 (by rfl) ⟨2441744, by rfl⟩ : syracuseStep 3255659 = 4883489) B4883489
theorem B22195795 : Blo 758332 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B4108895 : Blo 758332 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B3852683 : Blo 758332 3852683 := bstep (se 1 (by rfl) ⟨2889512, by rfl⟩ : syracuseStep 3852683 = 5779025) B5779025
theorem B136663375 : Blo 758332 136663375 := bstep (se 1 (by rfl) ⟨102497531, by rfl⟩ : syracuseStep 136663375 = 204995063) B204995063
theorem B2317033 : Blo 758332 2317033 := bstep (se 2 (by rfl) ⟨868887, by rfl⟩ : syracuseStep 2317033 = 1737775) B1737775
theorem B6151015 : Blo 758332 6151015 := bstep (se 1 (by rfl) ⟨4613261, by rfl⟩ : syracuseStep 6151015 = 9226523) B9226523
theorem B12050777 : Blo 758332 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B3335423 : Blo 758332 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B1140203 : Blo 758332 1140203 := bstep (se 1 (by rfl) ⟨855152, by rfl⟩ : syracuseStep 1140203 = 1710305) B1710305
theorem B36957293 : Blo 758332 36957293 := bstep (se 3 (by rfl) ⟨6929492, by rfl⟩ : syracuseStep 36957293 = 13858985) B13858985
theorem B1143023 : Blo 758332 1143023 := bstep (se 1 (by rfl) ⟨857267, by rfl⟩ : syracuseStep 1143023 = 1714535) B1714535
theorem B1143263 : Blo 758332 1143263 := bstep (se 1 (by rfl) ⟨857447, by rfl⟩ : syracuseStep 1143263 = 1714895) B1714895
theorem B1439851 : Blo 758332 1439851 := bstep (se 1 (by rfl) ⟨1079888, by rfl⟩ : syracuseStep 1439851 = 2159777) B2159777
theorem B4619489 : Blo 758332 4619489 := bstep (se 2 (by rfl) ⟨1732308, by rfl⟩ : syracuseStep 4619489 = 3464617) B3464617
theorem B1081039 : Blo 758332 1081039 := bstep (se 1 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 1081039 = 1621559) B1621559
theorem B1280137 : Blo 758332 1280137 := bstep (se 2 (by rfl) ⟨480051, by rfl⟩ : syracuseStep 1280137 = 960103) B960103
theorem B1446025 : Blo 758332 1446025 := bstep (se 2 (by rfl) ⟨542259, by rfl⟩ : syracuseStep 1446025 = 1084519) B1084519
theorem B29594393 : Blo 758332 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B8033851 : Blo 758332 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B2889391 : Blo 758332 2889391 := bstep (se 1 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 2889391 = 4334087) B4334087
theorem B4331627 : Blo 758332 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B1710287 : Blo 758332 1710287 := bstep (se 1 (by rfl) ⟨1282715, by rfl⟩ : syracuseStep 1710287 = 2565431) B2565431
theorem B760135 : Blo 758332 760135 := bstep (se 1 (by rfl) ⟨570101, by rfl⟩ : syracuseStep 760135 = 1140203) B1140203
theorem B2563271 : Blo 758332 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B2170439 : Blo 758332 2170439 := bstep (se 1 (by rfl) ⟨1627829, by rfl⟩ : syracuseStep 2170439 = 3255659) B3255659
theorem B762015 : Blo 758332 762015 := bstep (se 1 (by rfl) ⟨571511, by rfl⟩ : syracuseStep 762015 = 1143023) B1143023
theorem B762175 : Blo 758332 762175 := bstep (se 1 (by rfl) ⟨571631, by rfl⟩ : syracuseStep 762175 = 1143263) B1143263
theorem B3089377 : Blo 758332 3089377 := bstep (se 2 (by rfl) ⟨1158516, by rfl⟩ : syracuseStep 3089377 = 2317033) B2317033
theorem B8201353 : Blo 758332 8201353 := bstep (se 2 (by rfl) ⟨3075507, by rfl⟩ : syracuseStep 8201353 = 6151015) B6151015
theorem B2893097 : Blo 758332 2893097 := bstep (se 2 (by rfl) ⟨1084911, by rfl⟩ : syracuseStep 2893097 = 2169823) B2169823
theorem B9875195 : Blo 758332 9875195 := bstep (se 1 (by rfl) ⟨7406396, by rfl⟩ : syracuseStep 9875195 = 14812793) B14812793
theorem B2568455 : Blo 758332 2568455 := bstep (se 1 (by rfl) ⟨1926341, by rfl⟩ : syracuseStep 2568455 = 3852683) B3852683
theorem B8894461 : Blo 758332 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B14597405 : Blo 758332 14597405 := bstep (se 3 (by rfl) ⟨2737013, by rfl⟩ : syracuseStep 14597405 = 5474027) B5474027
theorem B1919801 : Blo 758332 1919801 := bstep (se 2 (by rfl) ⟨719925, by rfl⟩ : syracuseStep 1919801 = 1439851) B1439851
theorem B2739263 : Blo 758332 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B17522639 : Blo 758332 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B1925147 : Blo 758332 1925147 := bstep (se 1 (by rfl) ⟨1443860, by rfl⟩ : syracuseStep 1925147 = 2887721) B2887721
theorem B1140023 : Blo 758332 1140023 := bstep (se 1 (by rfl) ⟨855017, by rfl⟩ : syracuseStep 1140023 = 1710035) B1710035
theorem B1731071 : Blo 758332 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B1927871 : Blo 758332 1927871 := bstep (se 1 (by rfl) ⟨1445903, by rfl⟩ : syracuseStep 1927871 = 2891807) B2891807
theorem B1141607 : Blo 758332 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B182217833 : Blo 758332 182217833 := bstep (se 2 (by rfl) ⟨68331687, by rfl⟩ : syracuseStep 182217833 = 136663375) B136663375
theorem B1141865 : Blo 758332 1141865 := bstep (se 2 (by rfl) ⟨428199, by rfl⟩ : syracuseStep 1141865 = 856399) B856399
theorem B24638195 : Blo 758332 24638195 := bstep (se 1 (by rfl) ⟨18478646, by rfl⟩ : syracuseStep 24638195 = 36957293) B36957293
theorem B3241853 : Blo 758332 3241853 := bstep (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) B1215695
theorem B12318637 : Blo 758332 12318637 := bstep (se 3 (by rfl) ⟨2309744, by rfl⟩ : syracuseStep 12318637 = 4619489) B4619489
theorem B1441385 : Blo 758332 1441385 := bstep (se 2 (by rfl) ⟨540519, by rfl⟩ : syracuseStep 1441385 = 1081039) B1081039
theorem B1279867 : Blo 758332 1279867 := bstep (se 1 (by rfl) ⟨959900, by rfl⟩ : syracuseStep 1279867 = 1919801) B1919801
theorem B1706849 : Blo 758332 1706849 := bstep (se 2 (by rfl) ⟨640068, by rfl⟩ : syracuseStep 1706849 = 1280137) B1280137
theorem B19729595 : Blo 758332 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B2887751 : Blo 758332 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B1708847 : Blo 758332 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B1446959 : Blo 758332 1446959 := bstep (se 1 (by rfl) ⟨1085219, by rfl⟩ : syracuseStep 1446959 = 2170439) B2170439
theorem B1283431 : Blo 758332 1283431 := bstep (se 1 (by rfl) ⟨962573, by rfl⟩ : syracuseStep 1283431 = 1925147) B1925147
theorem B760015 : Blo 758332 760015 := bstep (se 1 (by rfl) ⟨570011, by rfl⟩ : syracuseStep 760015 = 1140023) B1140023
theorem B1285247 : Blo 758332 1285247 := bstep (se 1 (by rfl) ⟨963935, by rfl⟩ : syracuseStep 1285247 = 1927871) B1927871
theorem B761071 : Blo 758332 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B121478555 : Blo 758332 121478555 := bstep (se 1 (by rfl) ⟨91108916, by rfl⟩ : syracuseStep 121478555 = 182217833) B182217833
theorem B761243 : Blo 758332 761243 := bstep (se 1 (by rfl) ⟨570932, by rfl⟩ : syracuseStep 761243 = 1141865) B1141865
theorem B16424849 : Blo 758332 16424849 := bstep (se 2 (by rfl) ⟨6159318, by rfl⟩ : syracuseStep 16424849 = 12318637) B12318637
theorem B1712303 : Blo 758332 1712303 := bstep (se 1 (by rfl) ⟨1284227, by rfl⟩ : syracuseStep 1712303 = 2568455) B2568455
theorem B16425463 : Blo 758332 16425463 := bstep (se 1 (by rfl) ⟨12319097, by rfl⟩ : syracuseStep 16425463 = 24638195) B24638195
theorem B960923 : Blo 758332 960923 := bstep (se 1 (by rfl) ⟨720692, by rfl⟩ : syracuseStep 960923 = 1441385) B1441385
theorem B11681759 : Blo 758332 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B3852521 : Blo 758332 3852521 := bstep (se 2 (by rfl) ⟨1444695, by rfl⟩ : syracuseStep 3852521 = 2889391) B2889391
theorem B4119169 : Blo 758332 4119169 := bstep (se 2 (by rfl) ⟨1544688, by rfl⟩ : syracuseStep 4119169 = 3089377) B3089377
theorem B10935137 : Blo 758332 10935137 := bstep (se 2 (by rfl) ⟨4100676, by rfl⟩ : syracuseStep 10935137 = 8201353) B8201353
theorem B1140191 : Blo 758332 1140191 := bstep (se 1 (by rfl) ⟨855143, by rfl⟩ : syracuseStep 1140191 = 1710287) B1710287
theorem B1928033 : Blo 758332 1928033 := bstep (se 2 (by rfl) ⟨723012, by rfl⟩ : syracuseStep 1928033 = 1446025) B1446025
theorem B1928731 : Blo 758332 1928731 := bstep (se 1 (by rfl) ⟨1446548, by rfl⟩ : syracuseStep 1928731 = 2893097) B2893097
theorem B4616189 : Blo 758332 4616189 := bstep (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) B1731071
theorem B10711801 : Blo 758332 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B6583463 : Blo 758332 6583463 := bstep (se 1 (by rfl) ⟨4937597, by rfl⟩ : syracuseStep 6583463 = 9875195) B9875195
theorem B11859281 : Blo 758332 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B7304701 : Blo 758332 7304701 := bstep (se 3 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 7304701 = 2739263) B2739263
theorem B2161235 : Blo 758332 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B9731603 : Blo 758332 9731603 := bstep (se 1 (by rfl) ⟨7298702, by rfl⟩ : syracuseStep 9731603 = 14597405) B14597405
theorem B1706489 : Blo 758332 1706489 := bstep (se 2 (by rfl) ⟨639933, by rfl⟩ : syracuseStep 1706489 = 1279867) B1279867
theorem B856831 : Blo 758332 856831 := bstep (se 1 (by rfl) ⟨642623, by rfl⟩ : syracuseStep 856831 = 1285247) B1285247
theorem B10949899 : Blo 758332 10949899 := bstep (se 1 (by rfl) ⟨8212424, by rfl⟩ : syracuseStep 10949899 = 16424849) B16424849
theorem B760127 : Blo 758332 760127 := bstep (se 1 (by rfl) ⟨570095, by rfl⟩ : syracuseStep 760127 = 1140191) B1140191
theorem B2562461 : Blo 758332 2562461 := bstep (se 3 (by rfl) ⟨480461, by rfl⟩ : syracuseStep 2562461 = 960923) B960923
theorem B1711241 : Blo 758332 1711241 := bstep (se 2 (by rfl) ⟨641715, by rfl⟩ : syracuseStep 1711241 = 1283431) B1283431
theorem B1285355 : Blo 758332 1285355 := bstep (se 1 (by rfl) ⟨964016, by rfl⟩ : syracuseStep 1285355 = 1928033) B1928033
theorem B9739601 : Blo 758332 9739601 := bstep (se 2 (by rfl) ⟨3652350, by rfl⟩ : syracuseStep 9739601 = 7304701) B7304701
theorem B7906187 : Blo 758332 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B21900617 : Blo 758332 21900617 := bstep (se 2 (by rfl) ⟨8212731, by rfl⟩ : syracuseStep 21900617 = 16425463) B16425463
theorem B2568347 : Blo 758332 2568347 := bstep (se 1 (by rfl) ⟨1926260, by rfl⟩ : syracuseStep 2568347 = 3852521) B3852521
theorem B13153063 : Blo 758332 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B964639 : Blo 758332 964639 := bstep (se 1 (by rfl) ⟨723479, by rfl⟩ : syracuseStep 964639 = 1446959) B1446959
theorem B7290091 : Blo 758332 7290091 := bstep (se 1 (by rfl) ⟨5467568, by rfl⟩ : syracuseStep 7290091 = 10935137) B10935137
theorem B2571641 : Blo 758332 2571641 := bstep (se 2 (by rfl) ⟨964365, by rfl⟩ : syracuseStep 2571641 = 1928731) B1928731
theorem B80985703 : Blo 758332 80985703 := bstep (se 1 (by rfl) ⟨60739277, by rfl⟩ : syracuseStep 80985703 = 121478555) B121478555
theorem B5492225 : Blo 758332 5492225 := bstep (se 2 (by rfl) ⟨2059584, by rfl⟩ : syracuseStep 5492225 = 4119169) B4119169
theorem B7787839 : Blo 758332 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B1137899 : Blo 758332 1137899 := bstep (se 1 (by rfl) ⟨853424, by rfl⟩ : syracuseStep 1137899 = 1706849) B1706849
theorem B1925167 : Blo 758332 1925167 := bstep (se 1 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 1925167 = 2887751) B2887751
theorem B1139231 : Blo 758332 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B1141535 : Blo 758332 1141535 := bstep (se 1 (by rfl) ⟨856151, by rfl⟩ : syracuseStep 1141535 = 1712303) B1712303
theorem B14282401 : Blo 758332 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B3077459 : Blo 758332 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B4388975 : Blo 758332 4388975 := bstep (se 1 (by rfl) ⟨3291731, by rfl⟩ : syracuseStep 4388975 = 6583463) B6583463
theorem B1440823 : Blo 758332 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B6487735 : Blo 758332 6487735 := bstep (se 1 (by rfl) ⟨4865801, by rfl⟩ : syracuseStep 6487735 = 9731603) B9731603
theorem B1708307 : Blo 758332 1708307 := bstep (se 1 (by rfl) ⟨1281230, by rfl⟩ : syracuseStep 1708307 = 2562461) B2562461
theorem B758599 : Blo 758332 758599 := bstep (se 1 (by rfl) ⟨568949, by rfl⟩ : syracuseStep 758599 = 1137899) B1137899
theorem B856903 : Blo 758332 856903 := bstep (se 1 (by rfl) ⟨642677, by rfl⟩ : syracuseStep 856903 = 1285355) B1285355
theorem B19043201 : Blo 758332 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B6493067 : Blo 758332 6493067 := bstep (se 1 (by rfl) ⟨4869800, by rfl⟩ : syracuseStep 6493067 = 9739601) B9739601
theorem B759487 : Blo 758332 759487 := bstep (se 1 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 759487 = 1139231) B1139231
theorem B17537417 : Blo 758332 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B761023 : Blo 758332 761023 := bstep (se 1 (by rfl) ⟨570767, by rfl⟩ : syracuseStep 761023 = 1141535) B1141535
theorem B1286185 : Blo 758332 1286185 := bstep (se 2 (by rfl) ⟨482319, by rfl⟩ : syracuseStep 1286185 = 964639) B964639
theorem B1712231 : Blo 758332 1712231 := bstep (se 1 (by rfl) ⟨1284173, by rfl⟩ : syracuseStep 1712231 = 2568347) B2568347
theorem B2925983 : Blo 758332 2925983 := bstep (se 1 (by rfl) ⟨2194487, by rfl⟩ : syracuseStep 2925983 = 4388975) B4388975
theorem B107980937 : Blo 758332 107980937 := bstep (se 2 (by rfl) ⟨40492851, by rfl⟩ : syracuseStep 107980937 = 80985703) B80985703
theorem B1714427 : Blo 758332 1714427 := bstep (se 1 (by rfl) ⟨1285820, by rfl⟩ : syracuseStep 1714427 = 2571641) B2571641
theorem B2566889 : Blo 758332 2566889 := bstep (se 2 (by rfl) ⟨962583, by rfl⟩ : syracuseStep 2566889 = 1925167) B1925167
theorem B14599865 : Blo 758332 14599865 := bstep (se 2 (by rfl) ⟨5474949, by rfl⟩ : syracuseStep 14599865 = 10949899) B10949899
theorem B14600411 : Blo 758332 14600411 := bstep (se 1 (by rfl) ⟨10950308, by rfl⟩ : syracuseStep 14600411 = 21900617) B21900617
theorem B2051639 : Blo 758332 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B1921097 : Blo 758332 1921097 := bstep (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) B1440823
theorem B9720121 : Blo 758332 9720121 := bstep (se 2 (by rfl) ⟨3645045, by rfl⟩ : syracuseStep 9720121 = 7290091) B7290091
theorem B1137659 : Blo 758332 1137659 := bstep (se 1 (by rfl) ⟨853244, by rfl⟩ : syracuseStep 1137659 = 1706489) B1706489
theorem B3661483 : Blo 758332 3661483 := bstep (se 1 (by rfl) ⟨2746112, by rfl⟩ : syracuseStep 3661483 = 5492225) B5492225
theorem B1140827 : Blo 758332 1140827 := bstep (se 1 (by rfl) ⟨855620, by rfl⟩ : syracuseStep 1140827 = 1711241) B1711241
theorem B5270791 : Blo 758332 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B1142441 : Blo 758332 1142441 := bstep (se 2 (by rfl) ⟨428415, by rfl⟩ : syracuseStep 1142441 = 856831) B856831
theorem B10383785 : Blo 758332 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B8650313 : Blo 758332 8650313 := bstep (se 2 (by rfl) ⟨3243867, by rfl⟩ : syracuseStep 8650313 = 6487735) B6487735
theorem B9733243 : Blo 758332 9733243 := bstep (se 1 (by rfl) ⟨7299932, by rfl⟩ : syracuseStep 9733243 = 14599865) B14599865
theorem B9733607 : Blo 758332 9733607 := bstep (se 1 (by rfl) ⟨7300205, by rfl⟩ : syracuseStep 9733607 = 14600411) B14600411
theorem B1280731 : Blo 758332 1280731 := bstep (se 1 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 1280731 = 1921097) B1921097
theorem B4328711 : Blo 758332 4328711 := bstep (se 1 (by rfl) ⟨3246533, by rfl⟩ : syracuseStep 4328711 = 6493067) B6493067
theorem B758439 : Blo 758332 758439 := bstep (se 1 (by rfl) ⟨568829, by rfl⟩ : syracuseStep 758439 = 1137659) B1137659
theorem B760551 : Blo 758332 760551 := bstep (se 1 (by rfl) ⟨570413, by rfl⟩ : syracuseStep 760551 = 1140827) B1140827
theorem B1711259 : Blo 758332 1711259 := bstep (se 1 (by rfl) ⟨1283444, by rfl⟩ : syracuseStep 1711259 = 2566889) B2566889
theorem B761627 : Blo 758332 761627 := bstep (se 1 (by rfl) ⟨571220, by rfl⟩ : syracuseStep 761627 = 1142441) B1142441
theorem B6922523 : Blo 758332 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B1714913 : Blo 758332 1714913 := bstep (se 2 (by rfl) ⟨643092, by rfl⟩ : syracuseStep 1714913 = 1286185) B1286185
theorem B12695467 : Blo 758332 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B7027721 : Blo 758332 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B12960161 : Blo 758332 12960161 := bstep (se 2 (by rfl) ⟨4860060, by rfl⟩ : syracuseStep 12960161 = 9720121) B9720121
theorem B1950655 : Blo 758332 1950655 := bstep (se 1 (by rfl) ⟨1462991, by rfl⟩ : syracuseStep 1950655 = 2925983) B2925983
theorem B1367759 : Blo 758332 1367759 := bstep (se 1 (by rfl) ⟨1025819, by rfl⟩ : syracuseStep 1367759 = 2051639) B2051639
theorem B1138871 : Blo 758332 1138871 := bstep (se 1 (by rfl) ⟨854153, by rfl⟩ : syracuseStep 1138871 = 1708307) B1708307
theorem B11691611 : Blo 758332 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B1141487 : Blo 758332 1141487 := bstep (se 1 (by rfl) ⟨856115, by rfl⟩ : syracuseStep 1141487 = 1712231) B1712231
theorem B1142537 : Blo 758332 1142537 := bstep (se 2 (by rfl) ⟨428451, by rfl⟩ : syracuseStep 1142537 = 856903) B856903
theorem B71987291 : Blo 758332 71987291 := bstep (se 1 (by rfl) ⟨53990468, by rfl⟩ : syracuseStep 71987291 = 107980937) B107980937
theorem B1142951 : Blo 758332 1142951 := bstep (se 1 (by rfl) ⟨857213, by rfl⟩ : syracuseStep 1142951 = 1714427) B1714427
theorem B4881977 : Blo 758332 4881977 := bstep (se 2 (by rfl) ⟨1830741, by rfl⟩ : syracuseStep 4881977 = 3661483) B3661483
theorem B5766875 : Blo 758332 5766875 := bstep (se 1 (by rfl) ⟨4325156, by rfl⟩ : syracuseStep 5766875 = 8650313) B8650313
theorem B6489071 : Blo 758332 6489071 := bstep (se 1 (by rfl) ⟨4866803, by rfl⟩ : syracuseStep 6489071 = 9733607) B9733607
theorem B12977657 : Blo 758332 12977657 := bstep (se 2 (by rfl) ⟨4866621, by rfl⟩ : syracuseStep 12977657 = 9733243) B9733243
theorem B2885807 : Blo 758332 2885807 := bstep (se 1 (by rfl) ⟨2164355, by rfl⟩ : syracuseStep 2885807 = 4328711) B4328711
theorem B1707641 : Blo 758332 1707641 := bstep (se 2 (by rfl) ⟨640365, by rfl⟩ : syracuseStep 1707641 = 1280731) B1280731
theorem B759247 : Blo 758332 759247 := bstep (se 1 (by rfl) ⟨569435, by rfl⟩ : syracuseStep 759247 = 1138871) B1138871
theorem B760991 : Blo 758332 760991 := bstep (se 1 (by rfl) ⟨570743, by rfl⟩ : syracuseStep 760991 = 1141487) B1141487
theorem B761691 : Blo 758332 761691 := bstep (se 1 (by rfl) ⟨571268, by rfl⟩ : syracuseStep 761691 = 1142537) B1142537
theorem B761967 : Blo 758332 761967 := bstep (se 1 (by rfl) ⟨571475, by rfl⟩ : syracuseStep 761967 = 1142951) B1142951
theorem B3254651 : Blo 758332 3254651 := bstep (se 1 (by rfl) ⟨2440988, by rfl⟩ : syracuseStep 3254651 = 4881977) B4881977
theorem B3844583 : Blo 758332 3844583 := bstep (se 1 (by rfl) ⟨2883437, by rfl⟩ : syracuseStep 3844583 = 5766875) B5766875
theorem B2600873 : Blo 758332 2600873 := bstep (se 2 (by rfl) ⟨975327, by rfl⟩ : syracuseStep 2600873 = 1950655) B1950655
theorem B16927289 : Blo 758332 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B47991527 : Blo 758332 47991527 := bstep (se 1 (by rfl) ⟨35993645, by rfl⟩ : syracuseStep 47991527 = 71987291) B71987291
theorem B8640107 : Blo 758332 8640107 := bstep (se 1 (by rfl) ⟨6480080, by rfl⟩ : syracuseStep 8640107 = 12960161) B12960161
theorem B1140839 : Blo 758332 1140839 := bstep (se 1 (by rfl) ⟨855629, by rfl⟩ : syracuseStep 1140839 = 1711259) B1711259
theorem B911839 : Blo 758332 911839 := bstep (se 1 (by rfl) ⟨683879, by rfl⟩ : syracuseStep 911839 = 1367759) B1367759
theorem B4615015 : Blo 758332 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B7794407 : Blo 758332 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B1143275 : Blo 758332 1143275 := bstep (se 1 (by rfl) ⟨857456, by rfl⟩ : syracuseStep 1143275 = 1714913) B1714913
theorem B4685147 : Blo 758332 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B4326047 : Blo 758332 4326047 := bstep (se 1 (by rfl) ⟨3244535, by rfl⟩ : syracuseStep 4326047 = 6489071) B6489071
theorem B8651771 : Blo 758332 8651771 := bstep (se 1 (by rfl) ⟨6488828, by rfl⟩ : syracuseStep 8651771 = 12977657) B12977657
theorem B1215785 : Blo 758332 1215785 := bstep (se 2 (by rfl) ⟨455919, by rfl⟩ : syracuseStep 1215785 = 911839) B911839
theorem B760559 : Blo 758332 760559 := bstep (se 1 (by rfl) ⟨570419, by rfl⟩ : syracuseStep 760559 = 1140839) B1140839
theorem B2169767 : Blo 758332 2169767 := bstep (se 1 (by rfl) ⟨1627325, by rfl⟩ : syracuseStep 2169767 = 3254651) B3254651
theorem B2563055 : Blo 758332 2563055 := bstep (se 1 (by rfl) ⟨1922291, by rfl⟩ : syracuseStep 2563055 = 3844583) B3844583
theorem B762183 : Blo 758332 762183 := bstep (se 1 (by rfl) ⟨571637, by rfl⟩ : syracuseStep 762183 = 1143275) B1143275
theorem B3123431 : Blo 758332 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B11284859 : Blo 758332 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B31994351 : Blo 758332 31994351 := bstep (se 1 (by rfl) ⟨23995763, by rfl⟩ : syracuseStep 31994351 = 47991527) B47991527
theorem B5196271 : Blo 758332 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B1923871 : Blo 758332 1923871 := bstep (se 1 (by rfl) ⟨1442903, by rfl⟩ : syracuseStep 1923871 = 2885807) B2885807
theorem B1138427 : Blo 758332 1138427 := bstep (se 1 (by rfl) ⟨853820, by rfl⟩ : syracuseStep 1138427 = 1707641) B1707641
theorem B5760071 : Blo 758332 5760071 := bstep (se 1 (by rfl) ⟨4320053, by rfl⟩ : syracuseStep 5760071 = 8640107) B8640107
theorem B6153353 : Blo 758332 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B1733915 : Blo 758332 1733915 := bstep (se 1 (by rfl) ⟨1300436, by rfl⟩ : syracuseStep 1733915 = 2600873) B2600873
theorem B2884031 : Blo 758332 2884031 := bstep (se 1 (by rfl) ⟨2163023, by rfl⟩ : syracuseStep 2884031 = 4326047) B4326047
theorem B5767847 : Blo 758332 5767847 := bstep (se 1 (by rfl) ⟨4325885, by rfl⟩ : syracuseStep 5767847 = 8651771) B8651771
theorem B1446511 : Blo 758332 1446511 := bstep (se 1 (by rfl) ⟨1084883, by rfl⟩ : syracuseStep 1446511 = 2169767) B2169767
theorem B1708703 : Blo 758332 1708703 := bstep (se 1 (by rfl) ⟨1281527, by rfl⟩ : syracuseStep 1708703 = 2563055) B2563055
theorem B758951 : Blo 758332 758951 := bstep (se 1 (by rfl) ⟨569213, by rfl⟩ : syracuseStep 758951 = 1138427) B1138427
theorem B3840047 : Blo 758332 3840047 := bstep (se 1 (by rfl) ⟨2880035, by rfl⟩ : syracuseStep 3840047 = 5760071) B5760071
theorem B4102235 : Blo 758332 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B1155943 : Blo 758332 1155943 := bstep (se 1 (by rfl) ⟨866957, by rfl⟩ : syracuseStep 1155943 = 1733915) B1733915
theorem B2565161 : Blo 758332 2565161 := bstep (se 2 (by rfl) ⟨961935, by rfl⟩ : syracuseStep 2565161 = 1923871) B1923871
theorem B6928361 : Blo 758332 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B2082287 : Blo 758332 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B7523239 : Blo 758332 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B810523 : Blo 758332 810523 := bstep (se 1 (by rfl) ⟨607892, by rfl⟩ : syracuseStep 810523 = 1215785) B1215785
theorem B21329567 : Blo 758332 21329567 := bstep (se 1 (by rfl) ⟨15997175, by rfl⟩ : syracuseStep 21329567 = 31994351) B31994351
theorem B1541257 : Blo 758332 1541257 := bstep (se 2 (by rfl) ⟨577971, by rfl⟩ : syracuseStep 1541257 = 1155943) B1155943
theorem B10030985 : Blo 758332 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B2560031 : Blo 758332 2560031 := bstep (se 1 (by rfl) ⟨1920023, by rfl⟩ : syracuseStep 2560031 = 3840047) B3840047
theorem B1710107 : Blo 758332 1710107 := bstep (se 1 (by rfl) ⟨1282580, by rfl⟩ : syracuseStep 1710107 = 2565161) B2565161
theorem B3845231 : Blo 758332 3845231 := bstep (se 1 (by rfl) ⟨2883923, by rfl⟩ : syracuseStep 3845231 = 5767847) B5767847
theorem B1388191 : Blo 758332 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B2734823 : Blo 758332 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B1922687 : Blo 758332 1922687 := bstep (se 1 (by rfl) ⟨1442015, by rfl⟩ : syracuseStep 1922687 = 2884031) B2884031
theorem B1139135 : Blo 758332 1139135 := bstep (se 1 (by rfl) ⟨854351, by rfl⟩ : syracuseStep 1139135 = 1708703) B1708703
theorem B1928681 : Blo 758332 1928681 := bstep (se 2 (by rfl) ⟨723255, by rfl⟩ : syracuseStep 1928681 = 1446511) B1446511
theorem B14219711 : Blo 758332 14219711 := bstep (se 1 (by rfl) ⟨10664783, by rfl⟩ : syracuseStep 14219711 = 21329567) B21329567
theorem B4618907 : Blo 758332 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B1080697 : Blo 758332 1080697 := bstep (se 2 (by rfl) ⟨405261, by rfl⟩ : syracuseStep 1080697 = 810523) B810523
theorem B6687323 : Blo 758332 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B1706687 : Blo 758332 1706687 := bstep (se 1 (by rfl) ⟨1280015, by rfl⟩ : syracuseStep 1706687 = 2560031) B2560031
theorem B1281791 : Blo 758332 1281791 := bstep (se 1 (by rfl) ⟨961343, by rfl⟩ : syracuseStep 1281791 = 1922687) B1922687
theorem B759423 : Blo 758332 759423 := bstep (se 1 (by rfl) ⟨569567, by rfl⟩ : syracuseStep 759423 = 1139135) B1139135
theorem B2563487 : Blo 758332 2563487 := bstep (se 1 (by rfl) ⟨1922615, by rfl⟩ : syracuseStep 2563487 = 3845231) B3845231
theorem B1285787 : Blo 758332 1285787 := bstep (se 1 (by rfl) ⟨964340, by rfl⟩ : syracuseStep 1285787 = 1928681) B1928681
theorem B9479807 : Blo 758332 9479807 := bstep (se 1 (by rfl) ⟨7109855, by rfl⟩ : syracuseStep 9479807 = 14219711) B14219711
theorem B1850921 : Blo 758332 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B7292861 : Blo 758332 7292861 := bstep (se 3 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 7292861 = 2734823) B2734823
theorem B1140071 : Blo 758332 1140071 := bstep (se 1 (by rfl) ⟨855053, by rfl⟩ : syracuseStep 1140071 = 1710107) B1710107
theorem B8220037 : Blo 758332 8220037 := bstep (se 4 (by rfl) ⟨770628, by rfl⟩ : syracuseStep 8220037 = 1541257) B1541257
theorem B3079271 : Blo 758332 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B1440929 : Blo 758332 1440929 := bstep (se 2 (by rfl) ⟨540348, by rfl⟩ : syracuseStep 1440929 = 1080697) B1080697
theorem B4458215 : Blo 758332 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B854527 : Blo 758332 854527 := bstep (se 1 (by rfl) ⟨640895, by rfl⟩ : syracuseStep 854527 = 1281791) B1281791
theorem B1708991 : Blo 758332 1708991 := bstep (se 1 (by rfl) ⟨1281743, by rfl⟩ : syracuseStep 1708991 = 2563487) B2563487
theorem B857191 : Blo 758332 857191 := bstep (se 1 (by rfl) ⟨642893, by rfl⟩ : syracuseStep 857191 = 1285787) B1285787
theorem B760047 : Blo 758332 760047 := bstep (se 1 (by rfl) ⟨570035, by rfl⟩ : syracuseStep 760047 = 1140071) B1140071
theorem B3842477 : Blo 758332 3842477 := bstep (se 3 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 3842477 = 1440929) B1440929
theorem B4861907 : Blo 758332 4861907 := bstep (se 1 (by rfl) ⟨3646430, by rfl⟩ : syracuseStep 4861907 = 7292861) B7292861
theorem B10960049 : Blo 758332 10960049 := bstep (se 2 (by rfl) ⟨4110018, by rfl⟩ : syracuseStep 10960049 = 8220037) B8220037
theorem B2052847 : Blo 758332 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B1233947 : Blo 758332 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B1137791 : Blo 758332 1137791 := bstep (se 1 (by rfl) ⟨853343, by rfl⟩ : syracuseStep 1137791 = 1706687) B1706687
theorem B6319871 : Blo 758332 6319871 := bstep (se 1 (by rfl) ⟨4739903, by rfl⟩ : syracuseStep 6319871 = 9479807) B9479807
theorem B822631 : Blo 758332 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B10948517 : Blo 758332 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B758527 : Blo 758332 758527 := bstep (se 1 (by rfl) ⟨568895, by rfl⟩ : syracuseStep 758527 = 1137791) B1137791
theorem B2561651 : Blo 758332 2561651 := bstep (se 1 (by rfl) ⟨1921238, by rfl⟩ : syracuseStep 2561651 = 3842477) B3842477
theorem B4213247 : Blo 758332 4213247 := bstep (se 1 (by rfl) ⟨3159935, by rfl⟩ : syracuseStep 4213247 = 6319871) B6319871
theorem B2972143 : Blo 758332 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B1139327 : Blo 758332 1139327 := bstep (se 1 (by rfl) ⟨854495, by rfl⟩ : syracuseStep 1139327 = 1708991) B1708991
theorem B1139369 : Blo 758332 1139369 := bstep (se 2 (by rfl) ⟨427263, by rfl⟩ : syracuseStep 1139369 = 854527) B854527
theorem B1142921 : Blo 758332 1142921 := bstep (se 2 (by rfl) ⟨428595, by rfl⟩ : syracuseStep 1142921 = 857191) B857191
theorem B3241271 : Blo 758332 3241271 := bstep (se 1 (by rfl) ⟨2430953, by rfl⟩ : syracuseStep 3241271 = 4861907) B4861907
theorem B7306699 : Blo 758332 7306699 := bstep (se 1 (by rfl) ⟨5480024, by rfl⟩ : syracuseStep 7306699 = 10960049) B10960049
theorem B1707767 : Blo 758332 1707767 := bstep (se 1 (by rfl) ⟨1280825, by rfl⟩ : syracuseStep 1707767 = 2561651) B2561651
theorem B759551 : Blo 758332 759551 := bstep (se 1 (by rfl) ⟨569663, by rfl⟩ : syracuseStep 759551 = 1139327) B1139327
theorem B759579 : Blo 758332 759579 := bstep (se 1 (by rfl) ⟨569684, by rfl⟩ : syracuseStep 759579 = 1139369) B1139369
theorem B761947 : Blo 758332 761947 := bstep (se 1 (by rfl) ⟨571460, by rfl⟩ : syracuseStep 761947 = 1142921) B1142921
theorem B9742265 : Blo 758332 9742265 := bstep (se 2 (by rfl) ⟨3653349, by rfl⟩ : syracuseStep 9742265 = 7306699) B7306699
theorem B1096841 : Blo 758332 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B44941301 : Blo 758332 44941301 := bstep (se 5 (by rfl) ⟨2106623, by rfl⟩ : syracuseStep 44941301 = 4213247) B4213247
theorem B7299011 : Blo 758332 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B3962857 : Blo 758332 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B2160847 : Blo 758332 2160847 := bstep (se 1 (by rfl) ⟨1620635, by rfl⟩ : syracuseStep 2160847 = 3241271) B3241271
theorem B6494843 : Blo 758332 6494843 := bstep (se 1 (by rfl) ⟨4871132, by rfl⟩ : syracuseStep 6494843 = 9742265) B9742265
theorem B5283809 : Blo 758332 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B2924909 : Blo 758332 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B29960867 : Blo 758332 29960867 := bstep (se 1 (by rfl) ⟨22470650, by rfl⟩ : syracuseStep 29960867 = 44941301) B44941301
theorem B4866007 : Blo 758332 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B1138511 : Blo 758332 1138511 := bstep (se 1 (by rfl) ⟨853883, by rfl⟩ : syracuseStep 1138511 = 1707767) B1707767
theorem B2881129 : Blo 758332 2881129 := bstep (se 2 (by rfl) ⟨1080423, by rfl⟩ : syracuseStep 2881129 = 2160847) B2160847
theorem B4329895 : Blo 758332 4329895 := bstep (se 1 (by rfl) ⟨3247421, by rfl⟩ : syracuseStep 4329895 = 6494843) B6494843
theorem B759007 : Blo 758332 759007 := bstep (se 1 (by rfl) ⟨569255, by rfl⟩ : syracuseStep 759007 = 1138511) B1138511
theorem B79895645 : Blo 758332 79895645 := bstep (se 3 (by rfl) ⟨14980433, by rfl⟩ : syracuseStep 79895645 = 29960867) B29960867
theorem B3841505 : Blo 758332 3841505 := bstep (se 2 (by rfl) ⟨1440564, by rfl⟩ : syracuseStep 3841505 = 2881129) B2881129
theorem B3522539 : Blo 758332 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B1949939 : Blo 758332 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B6488009 : Blo 758332 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B2561003 : Blo 758332 2561003 := bstep (se 1 (by rfl) ⟨1920752, by rfl⟩ : syracuseStep 2561003 = 3841505) B3841505
theorem B5773193 : Blo 758332 5773193 := bstep (se 2 (by rfl) ⟨2164947, by rfl⟩ : syracuseStep 5773193 = 4329895) B4329895
theorem B53263763 : Blo 758332 53263763 := bstep (se 1 (by rfl) ⟨39947822, by rfl⟩ : syracuseStep 53263763 = 79895645) B79895645
theorem B2348359 : Blo 758332 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B1299959 : Blo 758332 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B4325339 : Blo 758332 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B1707335 : Blo 758332 1707335 := bstep (se 1 (by rfl) ⟨1280501, by rfl⟩ : syracuseStep 1707335 = 2561003) B2561003
theorem B12524581 : Blo 758332 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B866639 : Blo 758332 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B3848795 : Blo 758332 3848795 := bstep (se 1 (by rfl) ⟨2886596, by rfl⟩ : syracuseStep 3848795 = 5773193) B5773193
theorem B35509175 : Blo 758332 35509175 := bstep (se 1 (by rfl) ⟨26631881, by rfl⟩ : syracuseStep 35509175 = 53263763) B53263763
theorem B2883559 : Blo 758332 2883559 := bstep (se 1 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 2883559 = 4325339) B4325339
theorem B2565863 : Blo 758332 2565863 := bstep (se 1 (by rfl) ⟨1924397, by rfl⟩ : syracuseStep 2565863 = 3848795) B3848795
theorem B3844745 : Blo 758332 3844745 := bstep (se 2 (by rfl) ⟨1441779, by rfl⟩ : syracuseStep 3844745 = 2883559) B2883559
theorem B23672783 : Blo 758332 23672783 := bstep (se 1 (by rfl) ⟨17754587, by rfl⟩ : syracuseStep 23672783 = 35509175) B35509175
theorem B2311037 : Blo 758332 2311037 := bstep (se 3 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 2311037 = 866639) B866639
theorem B16699441 : Blo 758332 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B1138223 : Blo 758332 1138223 := bstep (se 1 (by rfl) ⟨853667, by rfl⟩ : syracuseStep 1138223 = 1707335) B1707335
theorem B1540691 : Blo 758332 1540691 := bstep (se 1 (by rfl) ⟨1155518, by rfl⟩ : syracuseStep 1540691 = 2311037) B2311037
theorem B758815 : Blo 758332 758815 := bstep (se 1 (by rfl) ⟨569111, by rfl⟩ : syracuseStep 758815 = 1138223) B1138223
theorem B1710575 : Blo 758332 1710575 := bstep (se 1 (by rfl) ⟨1282931, by rfl⟩ : syracuseStep 1710575 = 2565863) B2565863
theorem B2563163 : Blo 758332 2563163 := bstep (se 1 (by rfl) ⟨1922372, by rfl⟩ : syracuseStep 2563163 = 3844745) B3844745
theorem B63127421 : Blo 758332 63127421 := bstep (se 3 (by rfl) ⟨11836391, by rfl⟩ : syracuseStep 63127421 = 23672783) B23672783
theorem B22265921 : Blo 758332 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B14843947 : Blo 758332 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B1708775 : Blo 758332 1708775 := bstep (se 1 (by rfl) ⟨1281581, by rfl⟩ : syracuseStep 1708775 = 2563163) B2563163
theorem B42084947 : Blo 758332 42084947 := bstep (se 1 (by rfl) ⟨31563710, by rfl⟩ : syracuseStep 42084947 = 63127421) B63127421
theorem B1027127 : Blo 758332 1027127 := bstep (se 1 (by rfl) ⟨770345, by rfl⟩ : syracuseStep 1027127 = 1540691) B1540691
theorem B1140383 : Blo 758332 1140383 := bstep (se 1 (by rfl) ⟨855287, by rfl⟩ : syracuseStep 1140383 = 1710575) B1710575
theorem B19791929 : Blo 758332 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B760255 : Blo 758332 760255 := bstep (se 1 (by rfl) ⟨570191, by rfl⟩ : syracuseStep 760255 = 1140383) B1140383
theorem B28056631 : Blo 758332 28056631 := bstep (se 1 (by rfl) ⟨21042473, by rfl⟩ : syracuseStep 28056631 = 42084947) B42084947
theorem B2739005 : Blo 758332 2739005 := bstep (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) B1027127
theorem B1139183 : Blo 758332 1139183 := bstep (se 1 (by rfl) ⟨854387, by rfl⟩ : syracuseStep 1139183 = 1708775) B1708775
theorem B759455 : Blo 758332 759455 := bstep (se 1 (by rfl) ⟨569591, by rfl⟩ : syracuseStep 759455 = 1139183) B1139183
theorem B37408841 : Blo 758332 37408841 := bstep (se 2 (by rfl) ⟨14028315, by rfl⟩ : syracuseStep 37408841 = 28056631) B28056631
theorem B13194619 : Blo 758332 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B1826003 : Blo 758332 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B24939227 : Blo 758332 24939227 := bstep (se 1 (by rfl) ⟨18704420, by rfl⟩ : syracuseStep 24939227 = 37408841) B37408841
theorem B70371301 : Blo 758332 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B4869341 : Blo 758332 4869341 := bstep (se 3 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 4869341 = 1826003) B1826003
theorem B3246227 : Blo 758332 3246227 := bstep (se 1 (by rfl) ⟨2434670, by rfl⟩ : syracuseStep 3246227 = 4869341) B4869341
theorem B16626151 : Blo 758332 16626151 := bstep (se 1 (by rfl) ⟨12469613, by rfl⟩ : syracuseStep 16626151 = 24939227) B24939227
theorem B93828401 : Blo 758332 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B2164151 : Blo 758332 2164151 := bstep (se 1 (by rfl) ⟨1623113, by rfl⟩ : syracuseStep 2164151 = 3246227) B3246227
theorem B88672805 : Blo 758332 88672805 := bstep (se 4 (by rfl) ⟨8313075, by rfl⟩ : syracuseStep 88672805 = 16626151) B16626151
theorem B62552267 : Blo 758332 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B1442767 : Blo 758332 1442767 := bstep (se 1 (by rfl) ⟨1082075, by rfl⟩ : syracuseStep 1442767 = 2164151) B2164151
theorem B59115203 : Blo 758332 59115203 := bstep (se 1 (by rfl) ⟨44336402, by rfl⟩ : syracuseStep 59115203 = 88672805) B88672805
theorem B41701511 : Blo 758332 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B111204029 : Blo 758332 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B39410135 : Blo 758332 39410135 := bstep (se 1 (by rfl) ⟨29557601, by rfl⟩ : syracuseStep 39410135 = 59115203) B59115203
theorem B1923689 : Blo 758332 1923689 := bstep (se 2 (by rfl) ⟨721383, by rfl⟩ : syracuseStep 1923689 = 1442767) B1442767
theorem B1282459 : Blo 758332 1282459 := bstep (se 1 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 1282459 = 1923689) B1923689
theorem B74136019 : Blo 758332 74136019 := bstep (se 1 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 74136019 = 111204029) B111204029
theorem B26273423 : Blo 758332 26273423 := bstep (se 1 (by rfl) ⟨19705067, by rfl⟩ : syracuseStep 26273423 = 39410135) B39410135
theorem B1709945 : Blo 758332 1709945 := bstep (se 2 (by rfl) ⟨641229, by rfl⟩ : syracuseStep 1709945 = 1282459) B1282459
theorem B17515615 : Blo 758332 17515615 := bstep (se 1 (by rfl) ⟨13136711, by rfl⟩ : syracuseStep 17515615 = 26273423) B26273423
theorem B98848025 : Blo 758332 98848025 := bstep (se 2 (by rfl) ⟨37068009, by rfl⟩ : syracuseStep 98848025 = 74136019) B74136019
theorem B65898683 : Blo 758332 65898683 := bstep (se 1 (by rfl) ⟨49424012, by rfl⟩ : syracuseStep 65898683 = 98848025) B98848025
theorem B23354153 : Blo 758332 23354153 := bstep (se 2 (by rfl) ⟨8757807, by rfl⟩ : syracuseStep 23354153 = 17515615) B17515615
theorem B1139963 : Blo 758332 1139963 := bstep (se 1 (by rfl) ⟨854972, by rfl⟩ : syracuseStep 1139963 = 1709945) B1709945
theorem B15569435 : Blo 758332 15569435 := bstep (se 1 (by rfl) ⟨11677076, by rfl⟩ : syracuseStep 15569435 = 23354153) B23354153
theorem B759975 : Blo 758332 759975 := bstep (se 1 (by rfl) ⟨569981, by rfl⟩ : syracuseStep 759975 = 1139963) B1139963
theorem B43932455 : Blo 758332 43932455 := bstep (se 1 (by rfl) ⟨32949341, by rfl⟩ : syracuseStep 43932455 = 65898683) B65898683
theorem B10379623 : Blo 758332 10379623 := bstep (se 1 (by rfl) ⟨7784717, by rfl⟩ : syracuseStep 10379623 = 15569435) B15569435
theorem B29288303 : Blo 758332 29288303 := bstep (se 1 (by rfl) ⟨21966227, by rfl⟩ : syracuseStep 29288303 = 43932455) B43932455
theorem B13839497 : Blo 758332 13839497 := bstep (se 2 (by rfl) ⟨5189811, by rfl⟩ : syracuseStep 13839497 = 10379623) B10379623
theorem B19525535 : Blo 758332 19525535 := bstep (se 1 (by rfl) ⟨14644151, by rfl⟩ : syracuseStep 19525535 = 29288303) B29288303
theorem B13017023 : Blo 758332 13017023 := bstep (se 1 (by rfl) ⟨9762767, by rfl⟩ : syracuseStep 13017023 = 19525535) B19525535
theorem B9226331 : Blo 758332 9226331 := bstep (se 1 (by rfl) ⟨6919748, by rfl⟩ : syracuseStep 9226331 = 13839497) B13839497
theorem B6150887 : Blo 758332 6150887 := bstep (se 1 (by rfl) ⟨4613165, by rfl⟩ : syracuseStep 6150887 = 9226331) B9226331
theorem B8678015 : Blo 758332 8678015 := bstep (se 1 (by rfl) ⟨6508511, by rfl⟩ : syracuseStep 8678015 = 13017023) B13017023
theorem B4100591 : Blo 758332 4100591 := bstep (se 1 (by rfl) ⟨3075443, by rfl⟩ : syracuseStep 4100591 = 6150887) B6150887
theorem B5785343 : Blo 758332 5785343 := bstep (se 1 (by rfl) ⟨4339007, by rfl⟩ : syracuseStep 5785343 = 8678015) B8678015
theorem B3856895 : Blo 758332 3856895 := bstep (se 1 (by rfl) ⟨2892671, by rfl⟩ : syracuseStep 3856895 = 5785343) B5785343
theorem B10934909 : Blo 758332 10934909 := bstep (se 3 (by rfl) ⟨2050295, by rfl⟩ : syracuseStep 10934909 = 4100591) B4100591
theorem B2571263 : Blo 758332 2571263 := bstep (se 1 (by rfl) ⟨1928447, by rfl⟩ : syracuseStep 2571263 = 3856895) B3856895
theorem B7289939 : Blo 758332 7289939 := bstep (se 1 (by rfl) ⟨5467454, by rfl⟩ : syracuseStep 7289939 = 10934909) B10934909
theorem B1714175 : Blo 758332 1714175 := bstep (se 1 (by rfl) ⟨1285631, by rfl⟩ : syracuseStep 1714175 = 2571263) B2571263
theorem B4859959 : Blo 758332 4859959 := bstep (se 1 (by rfl) ⟨3644969, by rfl⟩ : syracuseStep 4859959 = 7289939) B7289939
theorem B6479945 : Blo 758332 6479945 := bstep (se 2 (by rfl) ⟨2429979, by rfl⟩ : syracuseStep 6479945 = 4859959) B4859959
theorem B1142783 : Blo 758332 1142783 := bstep (se 1 (by rfl) ⟨857087, by rfl⟩ : syracuseStep 1142783 = 1714175) B1714175
theorem B761855 : Blo 758332 761855 := bstep (se 1 (by rfl) ⟨571391, by rfl⟩ : syracuseStep 761855 = 1142783) B1142783
theorem B4319963 : Blo 758332 4319963 := bstep (se 1 (by rfl) ⟨3239972, by rfl⟩ : syracuseStep 4319963 = 6479945) B6479945
theorem B2879975 : Blo 758332 2879975 := bstep (se 1 (by rfl) ⟨2159981, by rfl⟩ : syracuseStep 2879975 = 4319963) B4319963
theorem B1919983 : Blo 758332 1919983 := bstep (se 1 (by rfl) ⟨1439987, by rfl⟩ : syracuseStep 1919983 = 2879975) B2879975
theorem B2559977 : Blo 758332 2559977 := bstep (se 2 (by rfl) ⟨959991, by rfl⟩ : syracuseStep 2559977 = 1919983) B1919983
theorem B1706651 : Blo 758332 1706651 := bstep (se 1 (by rfl) ⟨1279988, by rfl⟩ : syracuseStep 1706651 = 2559977) B2559977
theorem B1137767 : Blo 758332 1137767 := bstep (se 1 (by rfl) ⟨853325, by rfl⟩ : syracuseStep 1137767 = 1706651) B1706651
theorem B758511 : Blo 758332 758511 := bstep (se 1 (by rfl) ⟨568883, by rfl⟩ : syracuseStep 758511 = 1137767) B1137767

theorem C0 (j : ℕ) (h1 : 189583 ≤ j) (h2 : j ≤ 190282) : Blo 758332 (4 * j + 3) := by
  interval_cases j
  · exact B758335
  · exact B758339
  · exact B758343
  · exact B758347
  · exact B758351
  · exact B758355
  · exact B758359
  · exact B758363
  · exact B758367
  · exact B758371
  · exact B758375
  · exact B758379
  · exact B758383
  · exact B758387
  · exact B758391
  · exact B758395
  · exact B758399
  · exact B758403
  · exact B758407
  · exact B758411
  · exact B758415
  · exact B758419
  · exact B758423
  · exact B758427
  · exact B758431
  · exact B758435
  · exact B758439
  · exact B758443
  · exact B758447
  · exact B758451
  · exact B758455
  · exact B758459
  · exact B758463
  · exact B758467
  · exact B758471
  · exact B758475
  · exact B758479
  · exact B758483
  · exact B758487
  · exact B758491
  · exact B758495
  · exact B758499
  · exact B758503
  · exact B758507
  · exact B758511
  · exact B758515
  · exact B758519
  · exact B758523
  · exact B758527
  · exact B758531
  · exact B758535
  · exact B758539
  · exact B758543
  · exact B758547
  · exact B758551
  · exact B758555
  · exact B758559
  · exact B758563
  · exact B758567
  · exact B758571
  · exact B758575
  · exact B758579
  · exact B758583
  · exact B758587
  · exact B758591
  · exact B758595
  · exact B758599
  · exact B758603
  · exact B758607
  · exact B758611
  · exact B758615
  · exact B758619
  · exact B758623
  · exact B758627
  · exact B758631
  · exact B758635
  · exact B758639
  · exact B758643
  · exact B758647
  · exact B758651
  · exact B758655
  · exact B758659
  · exact B758663
  · exact B758667
  · exact B758671
  · exact B758675
  · exact B758679
  · exact B758683
  · exact B758687
  · exact B758691
  · exact B758695
  · exact B758699
  · exact B758703
  · exact B758707
  · exact B758711
  · exact B758715
  · exact B758719
  · exact B758723
  · exact B758727
  · exact B758731
  · exact B758735
  · exact B758739
  · exact B758743
  · exact B758747
  · exact B758751
  · exact B758755
  · exact B758759
  · exact B758763
  · exact B758767
  · exact B758771
  · exact B758775
  · exact B758779
  · exact B758783
  · exact B758787
  · exact B758791
  · exact B758795
  · exact B758799
  · exact B758803
  · exact B758807
  · exact B758811
  · exact B758815
  · exact B758819
  · exact B758823
  · exact B758827
  · exact B758831
  · exact B758835
  · exact B758839
  · exact B758843
  · exact B758847
  · exact B758851
  · exact B758855
  · exact B758859
  · exact B758863
  · exact B758867
  · exact B758871
  · exact B758875
  · exact B758879
  · exact B758883
  · exact B758887
  · exact B758891
  · exact B758895
  · exact B758899
  · exact B758903
  · exact B758907
  · exact B758911
  · exact B758915
  · exact B758919
  · exact B758923
  · exact B758927
  · exact B758931
  · exact B758935
  · exact B758939
  · exact B758943
  · exact B758947
  · exact B758951
  · exact B758955
  · exact B758959
  · exact B758963
  · exact B758967
  · exact B758971
  · exact B758975
  · exact B758979
  · exact B758983
  · exact B758987
  · exact B758991
  · exact B758995
  · exact B758999
  · exact B759003
  · exact B759007
  · exact B759011
  · exact B759015
  · exact B759019
  · exact B759023
  · exact B759027
  · exact B759031
  · exact B759035
  · exact B759039
  · exact B759043
  · exact B759047
  · exact B759051
  · exact B759055
  · exact B759059
  · exact B759063
  · exact B759067
  · exact B759071
  · exact B759075
  · exact B759079
  · exact B759083
  · exact B759087
  · exact B759091
  · exact B759095
  · exact B759099
  · exact B759103
  · exact B759107
  · exact B759111
  · exact B759115
  · exact B759119
  · exact B759123
  · exact B759127
  · exact B759131
  · exact B759135
  · exact B759139
  · exact B759143
  · exact B759147
  · exact B759151
  · exact B759155
  · exact B759159
  · exact B759163
  · exact B759167
  · exact B759171
  · exact B759175
  · exact B759179
  · exact B759183
  · exact B759187
  · exact B759191
  · exact B759195
  · exact B759199
  · exact B759203
  · exact B759207
  · exact B759211
  · exact B759215
  · exact B759219
  · exact B759223
  · exact B759227
  · exact B759231
  · exact B759235
  · exact B759239
  · exact B759243
  · exact B759247
  · exact B759251
  · exact B759255
  · exact B759259
  · exact B759263
  · exact B759267
  · exact B759271
  · exact B759275
  · exact B759279
  · exact B759283
  · exact B759287
  · exact B759291
  · exact B759295
  · exact B759299
  · exact B759303
  · exact B759307
  · exact B759311
  · exact B759315
  · exact B759319
  · exact B759323
  · exact B759327
  · exact B759331
  · exact B759335
  · exact B759339
  · exact B759343
  · exact B759347
  · exact B759351
  · exact B759355
  · exact B759359
  · exact B759363
  · exact B759367
  · exact B759371
  · exact B759375
  · exact B759379
  · exact B759383
  · exact B759387
  · exact B759391
  · exact B759395
  · exact B759399
  · exact B759403
  · exact B759407
  · exact B759411
  · exact B759415
  · exact B759419
  · exact B759423
  · exact B759427
  · exact B759431
  · exact B759435
  · exact B759439
  · exact B759443
  · exact B759447
  · exact B759451
  · exact B759455
  · exact B759459
  · exact B759463
  · exact B759467
  · exact B759471
  · exact B759475
  · exact B759479
  · exact B759483
  · exact B759487
  · exact B759491
  · exact B759495
  · exact B759499
  · exact B759503
  · exact B759507
  · exact B759511
  · exact B759515
  · exact B759519
  · exact B759523
  · exact B759527
  · exact B759531
  · exact B759535
  · exact B759539
  · exact B759543
  · exact B759547
  · exact B759551
  · exact B759555
  · exact B759559
  · exact B759563
  · exact B759567
  · exact B759571
  · exact B759575
  · exact B759579
  · exact B759583
  · exact B759587
  · exact B759591
  · exact B759595
  · exact B759599
  · exact B759603
  · exact B759607
  · exact B759611
  · exact B759615
  · exact B759619
  · exact B759623
  · exact B759627
  · exact B759631
  · exact B759635
  · exact B759639
  · exact B759643
  · exact B759647
  · exact B759651
  · exact B759655
  · exact B759659
  · exact B759663
  · exact B759667
  · exact B759671
  · exact B759675
  · exact B759679
  · exact B759683
  · exact B759687
  · exact B759691
  · exact B759695
  · exact B759699
  · exact B759703
  · exact B759707
  · exact B759711
  · exact B759715
  · exact B759719
  · exact B759723
  · exact B759727
  · exact B759731
  · exact B759735
  · exact B759739
  · exact B759743
  · exact B759747
  · exact B759751
  · exact B759755
  · exact B759759
  · exact B759763
  · exact B759767
  · exact B759771
  · exact B759775
  · exact B759779
  · exact B759783
  · exact B759787
  · exact B759791
  · exact B759795
  · exact B759799
  · exact B759803
  · exact B759807
  · exact B759811
  · exact B759815
  · exact B759819
  · exact B759823
  · exact B759827
  · exact B759831
  · exact B759835
  · exact B759839
  · exact B759843
  · exact B759847
  · exact B759851
  · exact B759855
  · exact B759859
  · exact B759863
  · exact B759867
  · exact B759871
  · exact B759875
  · exact B759879
  · exact B759883
  · exact B759887
  · exact B759891
  · exact B759895
  · exact B759899
  · exact B759903
  · exact B759907
  · exact B759911
  · exact B759915
  · exact B759919
  · exact B759923
  · exact B759927
  · exact B759931
  · exact B759935
  · exact B759939
  · exact B759943
  · exact B759947
  · exact B759951
  · exact B759955
  · exact B759959
  · exact B759963
  · exact B759967
  · exact B759971
  · exact B759975
  · exact B759979
  · exact B759983
  · exact B759987
  · exact B759991
  · exact B759995
  · exact B759999
  · exact B760003
  · exact B760007
  · exact B760011
  · exact B760015
  · exact B760019
  · exact B760023
  · exact B760027
  · exact B760031
  · exact B760035
  · exact B760039
  · exact B760043
  · exact B760047
  · exact B760051
  · exact B760055
  · exact B760059
  · exact B760063
  · exact B760067
  · exact B760071
  · exact B760075
  · exact B760079
  · exact B760083
  · exact B760087
  · exact B760091
  · exact B760095
  · exact B760099
  · exact B760103
  · exact B760107
  · exact B760111
  · exact B760115
  · exact B760119
  · exact B760123
  · exact B760127
  · exact B760131
  · exact B760135
  · exact B760139
  · exact B760143
  · exact B760147
  · exact B760151
  · exact B760155
  · exact B760159
  · exact B760163
  · exact B760167
  · exact B760171
  · exact B760175
  · exact B760179
  · exact B760183
  · exact B760187
  · exact B760191
  · exact B760195
  · exact B760199
  · exact B760203
  · exact B760207
  · exact B760211
  · exact B760215
  · exact B760219
  · exact B760223
  · exact B760227
  · exact B760231
  · exact B760235
  · exact B760239
  · exact B760243
  · exact B760247
  · exact B760251
  · exact B760255
  · exact B760259
  · exact B760263
  · exact B760267
  · exact B760271
  · exact B760275
  · exact B760279
  · exact B760283
  · exact B760287
  · exact B760291
  · exact B760295
  · exact B760299
  · exact B760303
  · exact B760307
  · exact B760311
  · exact B760315
  · exact B760319
  · exact B760323
  · exact B760327
  · exact B760331
  · exact B760335
  · exact B760339
  · exact B760343
  · exact B760347
  · exact B760351
  · exact B760355
  · exact B760359
  · exact B760363
  · exact B760367
  · exact B760371
  · exact B760375
  · exact B760379
  · exact B760383
  · exact B760387
  · exact B760391
  · exact B760395
  · exact B760399
  · exact B760403
  · exact B760407
  · exact B760411
  · exact B760415
  · exact B760419
  · exact B760423
  · exact B760427
  · exact B760431
  · exact B760435
  · exact B760439
  · exact B760443
  · exact B760447
  · exact B760451
  · exact B760455
  · exact B760459
  · exact B760463
  · exact B760467
  · exact B760471
  · exact B760475
  · exact B760479
  · exact B760483
  · exact B760487
  · exact B760491
  · exact B760495
  · exact B760499
  · exact B760503
  · exact B760507
  · exact B760511
  · exact B760515
  · exact B760519
  · exact B760523
  · exact B760527
  · exact B760531
  · exact B760535
  · exact B760539
  · exact B760543
  · exact B760547
  · exact B760551
  · exact B760555
  · exact B760559
  · exact B760563
  · exact B760567
  · exact B760571
  · exact B760575
  · exact B760579
  · exact B760583
  · exact B760587
  · exact B760591
  · exact B760595
  · exact B760599
  · exact B760603
  · exact B760607
  · exact B760611
  · exact B760615
  · exact B760619
  · exact B760623
  · exact B760627
  · exact B760631
  · exact B760635
  · exact B760639
  · exact B760643
  · exact B760647
  · exact B760651
  · exact B760655
  · exact B760659
  · exact B760663
  · exact B760667
  · exact B760671
  · exact B760675
  · exact B760679
  · exact B760683
  · exact B760687
  · exact B760691
  · exact B760695
  · exact B760699
  · exact B760703
  · exact B760707
  · exact B760711
  · exact B760715
  · exact B760719
  · exact B760723
  · exact B760727
  · exact B760731
  · exact B760735
  · exact B760739
  · exact B760743
  · exact B760747
  · exact B760751
  · exact B760755
  · exact B760759
  · exact B760763
  · exact B760767
  · exact B760771
  · exact B760775
  · exact B760779
  · exact B760783
  · exact B760787
  · exact B760791
  · exact B760795
  · exact B760799
  · exact B760803
  · exact B760807
  · exact B760811
  · exact B760815
  · exact B760819
  · exact B760823
  · exact B760827
  · exact B760831
  · exact B760835
  · exact B760839
  · exact B760843
  · exact B760847
  · exact B760851
  · exact B760855
  · exact B760859
  · exact B760863
  · exact B760867
  · exact B760871
  · exact B760875
  · exact B760879
  · exact B760883
  · exact B760887
  · exact B760891
  · exact B760895
  · exact B760899
  · exact B760903
  · exact B760907
  · exact B760911
  · exact B760915
  · exact B760919
  · exact B760923
  · exact B760927
  · exact B760931
  · exact B760935
  · exact B760939
  · exact B760943
  · exact B760947
  · exact B760951
  · exact B760955
  · exact B760959
  · exact B760963
  · exact B760967
  · exact B760971
  · exact B760975
  · exact B760979
  · exact B760983
  · exact B760987
  · exact B760991
  · exact B760995
  · exact B760999
  · exact B761003
  · exact B761007
  · exact B761011
  · exact B761015
  · exact B761019
  · exact B761023
  · exact B761027
  · exact B761031
  · exact B761035
  · exact B761039
  · exact B761043
  · exact B761047
  · exact B761051
  · exact B761055
  · exact B761059
  · exact B761063
  · exact B761067
  · exact B761071
  · exact B761075
  · exact B761079
  · exact B761083
  · exact B761087
  · exact B761091
  · exact B761095
  · exact B761099
  · exact B761103
  · exact B761107
  · exact B761111
  · exact B761115
  · exact B761119
  · exact B761123
  · exact B761127
  · exact B761131

theorem C1 (j : ℕ) (h1 : 190283 ≤ j) (h2 : j ≤ 190582) : Blo 758332 (4 * j + 3) := by
  interval_cases j
  · exact B761135
  · exact B761139
  · exact B761143
  · exact B761147
  · exact B761151
  · exact B761155
  · exact B761159
  · exact B761163
  · exact B761167
  · exact B761171
  · exact B761175
  · exact B761179
  · exact B761183
  · exact B761187
  · exact B761191
  · exact B761195
  · exact B761199
  · exact B761203
  · exact B761207
  · exact B761211
  · exact B761215
  · exact B761219
  · exact B761223
  · exact B761227
  · exact B761231
  · exact B761235
  · exact B761239
  · exact B761243
  · exact B761247
  · exact B761251
  · exact B761255
  · exact B761259
  · exact B761263
  · exact B761267
  · exact B761271
  · exact B761275
  · exact B761279
  · exact B761283
  · exact B761287
  · exact B761291
  · exact B761295
  · exact B761299
  · exact B761303
  · exact B761307
  · exact B761311
  · exact B761315
  · exact B761319
  · exact B761323
  · exact B761327
  · exact B761331
  · exact B761335
  · exact B761339
  · exact B761343
  · exact B761347
  · exact B761351
  · exact B761355
  · exact B761359
  · exact B761363
  · exact B761367
  · exact B761371
  · exact B761375
  · exact B761379
  · exact B761383
  · exact B761387
  · exact B761391
  · exact B761395
  · exact B761399
  · exact B761403
  · exact B761407
  · exact B761411
  · exact B761415
  · exact B761419
  · exact B761423
  · exact B761427
  · exact B761431
  · exact B761435
  · exact B761439
  · exact B761443
  · exact B761447
  · exact B761451
  · exact B761455
  · exact B761459
  · exact B761463
  · exact B761467
  · exact B761471
  · exact B761475
  · exact B761479
  · exact B761483
  · exact B761487
  · exact B761491
  · exact B761495
  · exact B761499
  · exact B761503
  · exact B761507
  · exact B761511
  · exact B761515
  · exact B761519
  · exact B761523
  · exact B761527
  · exact B761531
  · exact B761535
  · exact B761539
  · exact B761543
  · exact B761547
  · exact B761551
  · exact B761555
  · exact B761559
  · exact B761563
  · exact B761567
  · exact B761571
  · exact B761575
  · exact B761579
  · exact B761583
  · exact B761587
  · exact B761591
  · exact B761595
  · exact B761599
  · exact B761603
  · exact B761607
  · exact B761611
  · exact B761615
  · exact B761619
  · exact B761623
  · exact B761627
  · exact B761631
  · exact B761635
  · exact B761639
  · exact B761643
  · exact B761647
  · exact B761651
  · exact B761655
  · exact B761659
  · exact B761663
  · exact B761667
  · exact B761671
  · exact B761675
  · exact B761679
  · exact B761683
  · exact B761687
  · exact B761691
  · exact B761695
  · exact B761699
  · exact B761703
  · exact B761707
  · exact B761711
  · exact B761715
  · exact B761719
  · exact B761723
  · exact B761727
  · exact B761731
  · exact B761735
  · exact B761739
  · exact B761743
  · exact B761747
  · exact B761751
  · exact B761755
  · exact B761759
  · exact B761763
  · exact B761767
  · exact B761771
  · exact B761775
  · exact B761779
  · exact B761783
  · exact B761787
  · exact B761791
  · exact B761795
  · exact B761799
  · exact B761803
  · exact B761807
  · exact B761811
  · exact B761815
  · exact B761819
  · exact B761823
  · exact B761827
  · exact B761831
  · exact B761835
  · exact B761839
  · exact B761843
  · exact B761847
  · exact B761851
  · exact B761855
  · exact B761859
  · exact B761863
  · exact B761867
  · exact B761871
  · exact B761875
  · exact B761879
  · exact B761883
  · exact B761887
  · exact B761891
  · exact B761895
  · exact B761899
  · exact B761903
  · exact B761907
  · exact B761911
  · exact B761915
  · exact B761919
  · exact B761923
  · exact B761927
  · exact B761931
  · exact B761935
  · exact B761939
  · exact B761943
  · exact B761947
  · exact B761951
  · exact B761955
  · exact B761959
  · exact B761963
  · exact B761967
  · exact B761971
  · exact B761975
  · exact B761979
  · exact B761983
  · exact B761987
  · exact B761991
  · exact B761995
  · exact B761999
  · exact B762003
  · exact B762007
  · exact B762011
  · exact B762015
  · exact B762019
  · exact B762023
  · exact B762027
  · exact B762031
  · exact B762035
  · exact B762039
  · exact B762043
  · exact B762047
  · exact B762051
  · exact B762055
  · exact B762059
  · exact B762063
  · exact B762067
  · exact B762071
  · exact B762075
  · exact B762079
  · exact B762083
  · exact B762087
  · exact B762091
  · exact B762095
  · exact B762099
  · exact B762103
  · exact B762107
  · exact B762111
  · exact B762115
  · exact B762119
  · exact B762123
  · exact B762127
  · exact B762131
  · exact B762135
  · exact B762139
  · exact B762143
  · exact B762147
  · exact B762151
  · exact B762155
  · exact B762159
  · exact B762163
  · exact B762167
  · exact B762171
  · exact B762175
  · exact B762179
  · exact B762183
  · exact B762187
  · exact B762191
  · exact B762195
  · exact B762199
  · exact B762203
  · exact B762207
  · exact B762211
  · exact B762215
  · exact B762219
  · exact B762223
  · exact B762227
  · exact B762231
  · exact B762235
  · exact B762239
  · exact B762243
  · exact B762247
  · exact B762251
  · exact B762255
  · exact B762259
  · exact B762263
  · exact B762267
  · exact B762271
  · exact B762275
  · exact B762279
  · exact B762283
  · exact B762287
  · exact B762291
  · exact B762295
  · exact B762299
  · exact B762303
  · exact B762307
  · exact B762311
  · exact B762315
  · exact B762319
  · exact B762323
  · exact B762327
  · exact B762331

theorem solution (m : ℕ) (hlo : 758332 ≤ m) (hhi : m ≤ 762332) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 189583 ≤ j := by omega
    have hj2 : j ≤ 190582 := by omega
    have hb : Blo 758332 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 190283 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
