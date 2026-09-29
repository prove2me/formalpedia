-- Prove2me | solution 1 for syracuse_descends_range_1853628_1855628
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:07:59.032292+00:00
-- url     : https://prove2.me/submissions/703ed684-3b4f-425b-822e-0081014e1307

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


theorem B4694021 : Blo 1853628 4694021 := bbase (se 4 (by rfl) ⟨440064, by rfl⟩ : syracuseStep 4694021 = 880129) (by norm_num)
theorem B10027061 : Blo 1853628 10027061 := bbase (se 5 (by rfl) ⟨470018, by rfl⟩ : syracuseStep 10027061 = 940037) (by norm_num)
theorem B3342397 : Blo 1853628 3342397 := bbase (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) (by norm_num)
theorem B3129421 : Blo 1853628 3129421 := bbase (se 3 (by rfl) ⟨586766, by rfl⟩ : syracuseStep 3129421 = 1173533) (by norm_num)
theorem B3129509 : Blo 1853628 3129509 := bbase (se 4 (by rfl) ⟨293391, by rfl⟩ : syracuseStep 3129509 = 586783) (by norm_num)
theorem B6258869 : Blo 1853628 6258869 := bbase (se 5 (by rfl) ⟨293384, by rfl⟩ : syracuseStep 6258869 = 586769) (by norm_num)
theorem B4694213 : Blo 1853628 4694213 := bbase (se 4 (by rfl) ⟨440082, by rfl⟩ : syracuseStep 4694213 = 880165) (by norm_num)
theorem B2859205 : Blo 1853628 2859205 := bbase (se 4 (by rfl) ⟨268050, by rfl⟩ : syracuseStep 2859205 = 536101) (by norm_num)
theorem B2859229 : Blo 1853628 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B3129637 : Blo 1853628 3129637 := bbase (se 4 (by rfl) ⟨293403, by rfl⟩ : syracuseStep 3129637 = 586807) (by norm_num)
theorem B3129725 : Blo 1853628 3129725 := bbase (se 3 (by rfl) ⟨586823, by rfl⟩ : syracuseStep 3129725 = 1173647) (by norm_num)
theorem B6685109 : Blo 1853628 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B2228677 : Blo 1853628 2228677 := bbase (se 4 (by rfl) ⟨208938, by rfl⟩ : syracuseStep 2228677 = 417877) (by norm_num)
theorem B3129853 : Blo 1853628 3129853 := bbase (se 3 (by rfl) ⟨586847, by rfl⟩ : syracuseStep 3129853 = 1173695) (by norm_num)
theorem B4694557 : Blo 1853628 4694557 := bbase (se 3 (by rfl) ⟨880229, by rfl⟩ : syracuseStep 4694557 = 1760459) (by norm_num)
theorem B3129941 : Blo 1853628 3129941 := bbase (se 8 (by rfl) ⟨18339, by rfl⟩ : syracuseStep 3129941 = 36679) (by norm_num)
theorem B6259301 : Blo 1853628 6259301 := bbase (se 4 (by rfl) ⟨586809, by rfl⟩ : syracuseStep 6259301 = 1173619) (by norm_num)
theorem B4694669 : Blo 1853628 4694669 := bbase (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) (by norm_num)
theorem B2712229 : Blo 1853628 2712229 := bbase (se 4 (by rfl) ⟨254271, by rfl⟩ : syracuseStep 2712229 = 508543) (by norm_num)
theorem B9388709 : Blo 1853628 9388709 := bbase (se 4 (by rfl) ⟨880191, by rfl⟩ : syracuseStep 9388709 = 1760383) (by norm_num)
theorem B3130069 : Blo 1853628 3130069 := bbase (se 7 (by rfl) ⟨36680, by rfl⟩ : syracuseStep 3130069 = 73361) (by norm_num)
theorem B3130157 : Blo 1853628 3130157 := bbase (se 3 (by rfl) ⟨586904, by rfl⟩ : syracuseStep 3130157 = 1173809) (by norm_num)
theorem B4694861 : Blo 1853628 4694861 := bbase (se 3 (by rfl) ⟨880286, by rfl⟩ : syracuseStep 4694861 = 1760573) (by norm_num)
theorem B3130285 : Blo 1853628 3130285 := bbase (se 3 (by rfl) ⟨586928, by rfl⟩ : syracuseStep 3130285 = 1173857) (by norm_num)
theorem B15852469 : Blo 1853628 15852469 := bbase (se 5 (by rfl) ⟨743084, by rfl⟩ : syracuseStep 15852469 = 1486169) (by norm_num)
theorem B12862421 : Blo 1853628 12862421 := bbase (se 7 (by rfl) ⟨150731, by rfl⟩ : syracuseStep 12862421 = 301463) (by norm_num)
theorem B4170725 : Blo 1853628 4170725 := bbase (se 4 (by rfl) ⟨391005, by rfl⟩ : syracuseStep 4170725 = 782011) (by norm_num)
theorem B3130373 : Blo 1853628 3130373 := bbase (se 4 (by rfl) ⟨293472, by rfl⟩ : syracuseStep 3130373 = 586945) (by norm_num)
theorem B6259733 : Blo 1853628 6259733 := bbase (se 6 (by rfl) ⟨146712, by rfl⟩ : syracuseStep 6259733 = 293425) (by norm_num)
theorem B4170797 : Blo 1853628 4170797 := bbase (se 3 (by rfl) ⟨782024, by rfl⟩ : syracuseStep 4170797 = 1564049) (by norm_num)
theorem B4760621 : Blo 1853628 4760621 := bbase (se 3 (by rfl) ⟨892616, by rfl⟩ : syracuseStep 4760621 = 1785233) (by norm_num)
theorem B3171421 : Blo 1853628 3171421 := bbase (se 3 (by rfl) ⟨594641, by rfl⟩ : syracuseStep 3171421 = 1189283) (by norm_num)
theorem B4170869 : Blo 1853628 4170869 := bbase (se 5 (by rfl) ⟨195509, by rfl⟩ : syracuseStep 4170869 = 391019) (by norm_num)
theorem B3130501 : Blo 1853628 3130501 := bbase (se 4 (by rfl) ⟨293484, by rfl⟩ : syracuseStep 3130501 = 586969) (by norm_num)
theorem B3343493 : Blo 1853628 3343493 := bbase (se 4 (by rfl) ⟨313452, by rfl⟩ : syracuseStep 3343493 = 626905) (by norm_num)
theorem B15836309 : Blo 1853628 15836309 := bbase (se 6 (by rfl) ⟨371163, by rfl⟩ : syracuseStep 15836309 = 742327) (by norm_num)
theorem B11437205 : Blo 1853628 11437205 := bbase (se 6 (by rfl) ⟨268059, by rfl⟩ : syracuseStep 11437205 = 536119) (by norm_num)
theorem B4695205 : Blo 1853628 4695205 := bbase (se 4 (by rfl) ⟨440175, by rfl⟩ : syracuseStep 4695205 = 880351) (by norm_num)
theorem B4170941 : Blo 1853628 4170941 := bbase (se 3 (by rfl) ⟨782051, by rfl⟩ : syracuseStep 4170941 = 1564103) (by norm_num)
theorem B3130589 : Blo 1853628 3130589 := bbase (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) (by norm_num)
theorem B4171013 : Blo 1853628 4171013 := bbase (se 4 (by rfl) ⟨391032, by rfl⟩ : syracuseStep 4171013 = 782065) (by norm_num)
theorem B4695317 : Blo 1853628 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B2819357 : Blo 1853628 2819357 := bbase (se 3 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 2819357 = 1057259) (by norm_num)
theorem B9520421 : Blo 1853628 9520421 := bbase (se 4 (by rfl) ⟨892539, by rfl⟩ : syracuseStep 9520421 = 1785079) (by norm_num)
theorem B4171085 : Blo 1853628 4171085 := bbase (se 3 (by rfl) ⟨782078, by rfl⟩ : syracuseStep 4171085 = 1564157) (by norm_num)
theorem B3130717 : Blo 1853628 3130717 := bbase (se 3 (by rfl) ⟨587009, by rfl⟩ : syracuseStep 3130717 = 1174019) (by norm_num)
theorem B4171157 : Blo 1853628 4171157 := bbase (se 6 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 4171157 = 195523) (by norm_num)
theorem B7038373 : Blo 1853628 7038373 := bbase (se 4 (by rfl) ⟨659847, by rfl⟩ : syracuseStep 7038373 = 1319695) (by norm_num)
theorem B3343781 : Blo 1853628 3343781 := bbase (se 4 (by rfl) ⟨313479, by rfl⟩ : syracuseStep 3343781 = 626959) (by norm_num)
theorem B3130805 : Blo 1853628 3130805 := bbase (se 5 (by rfl) ⟨146756, by rfl⟩ : syracuseStep 3130805 = 293513) (by norm_num)
theorem B6260165 : Blo 1853628 6260165 := bbase (se 4 (by rfl) ⟨586890, by rfl⟩ : syracuseStep 6260165 = 1173781) (by norm_num)
theorem B4695509 : Blo 1853628 4695509 := bbase (se 7 (by rfl) ⟨55025, by rfl⟩ : syracuseStep 4695509 = 110051) (by norm_num)
theorem B4171229 : Blo 1853628 4171229 := bbase (se 3 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 4171229 = 1564211) (by norm_num)
theorem B3171845 : Blo 1853628 3171845 := bbase (se 4 (by rfl) ⟨297360, by rfl⟩ : syracuseStep 3171845 = 594721) (by norm_num)
theorem B4171301 : Blo 1853628 4171301 := bbase (se 4 (by rfl) ⟨391059, by rfl⟩ : syracuseStep 4171301 = 782119) (by norm_num)
theorem B2639413 : Blo 1853628 2639413 := bbase (se 5 (by rfl) ⟨123722, by rfl⟩ : syracuseStep 2639413 = 247445) (by norm_num)
theorem B3130933 : Blo 1853628 3130933 := bbase (se 5 (by rfl) ⟨146762, by rfl⟩ : syracuseStep 3130933 = 293525) (by norm_num)
theorem B4171373 : Blo 1853628 4171373 := bbase (se 3 (by rfl) ⟨782132, by rfl⟩ : syracuseStep 4171373 = 1564265) (by norm_num)
theorem B3131021 : Blo 1853628 3131021 := bbase (se 3 (by rfl) ⟨587066, by rfl⟩ : syracuseStep 3131021 = 1174133) (by norm_num)
theorem B7923365 : Blo 1853628 7923365 := bbase (se 4 (by rfl) ⟨742815, by rfl⟩ : syracuseStep 7923365 = 1485631) (by norm_num)
theorem B4171445 : Blo 1853628 4171445 := bbase (se 5 (by rfl) ⟨195536, by rfl⟩ : syracuseStep 4171445 = 391073) (by norm_num)
theorem B10561205 : Blo 1853628 10561205 := bbase (se 5 (by rfl) ⟨495056, by rfl⟩ : syracuseStep 10561205 = 990113) (by norm_num)
theorem B7038677 : Blo 1853628 7038677 := bbase (se 7 (by rfl) ⟨82484, by rfl⟩ : syracuseStep 7038677 = 164969) (by norm_num)
theorem B4171517 : Blo 1853628 4171517 := bbase (se 3 (by rfl) ⟨782159, by rfl⟩ : syracuseStep 4171517 = 1564319) (by norm_num)
theorem B3131149 : Blo 1853628 3131149 := bbase (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) (by norm_num)
theorem B2115353 : Blo 1853628 2115353 := bbase (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) (by norm_num)
theorem B4458277 : Blo 1853628 4458277 := bbase (se 4 (by rfl) ⟨417963, by rfl⟩ : syracuseStep 4458277 = 835927) (by norm_num)
theorem B4695853 : Blo 1853628 4695853 := bbase (se 3 (by rfl) ⟨880472, by rfl⟩ : syracuseStep 4695853 = 1760945) (by norm_num)
theorem B4171589 : Blo 1853628 4171589 := bbase (se 4 (by rfl) ⟨391086, by rfl⟩ : syracuseStep 4171589 = 782173) (by norm_num)
theorem B3131237 : Blo 1853628 3131237 := bbase (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) (by norm_num)
theorem B6260597 : Blo 1853628 6260597 := bbase (se 5 (by rfl) ⟨293465, by rfl⟩ : syracuseStep 6260597 = 586931) (by norm_num)
theorem B4171661 : Blo 1853628 4171661 := bbase (se 3 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 4171661 = 1564373) (by norm_num)
theorem B4695965 : Blo 1853628 4695965 := bbase (se 3 (by rfl) ⟨880493, by rfl⟩ : syracuseStep 4695965 = 1760987) (by norm_num)
theorem B9390005 : Blo 1853628 9390005 := bbase (se 5 (by rfl) ⟨440156, by rfl⟩ : syracuseStep 9390005 = 880313) (by norm_num)
theorem B6432709 : Blo 1853628 6432709 := bbase (se 4 (by rfl) ⟨603066, by rfl⟩ : syracuseStep 6432709 = 1206133) (by norm_num)
theorem B4171733 : Blo 1853628 4171733 := bbase (se 7 (by rfl) ⟨48887, by rfl⟩ : syracuseStep 4171733 = 97775) (by norm_num)
theorem B3131365 : Blo 1853628 3131365 := bbase (se 4 (by rfl) ⟨293565, by rfl⟩ : syracuseStep 3131365 = 587131) (by norm_num)
theorem B4171805 : Blo 1853628 4171805 := bbase (se 3 (by rfl) ⟨782213, by rfl⟩ : syracuseStep 4171805 = 1564427) (by norm_num)
theorem B4696157 : Blo 1853628 4696157 := bbase (se 3 (by rfl) ⟨880529, by rfl⟩ : syracuseStep 4696157 = 1761059) (by norm_num)
theorem B4171877 : Blo 1853628 4171877 := bbase (se 4 (by rfl) ⟨391113, by rfl⟩ : syracuseStep 4171877 = 782227) (by norm_num)
theorem B8915093 : Blo 1853628 8915093 := bbase (se 6 (by rfl) ⟨208947, by rfl⟩ : syracuseStep 8915093 = 417895) (by norm_num)
theorem B3958949 : Blo 1853628 3958949 := bbase (se 4 (by rfl) ⟨371151, by rfl⟩ : syracuseStep 3958949 = 742303) (by norm_num)
theorem B4171949 : Blo 1853628 4171949 := bbase (se 3 (by rfl) ⟨782240, by rfl⟩ : syracuseStep 4171949 = 1564481) (by norm_num)
theorem B4172021 : Blo 1853628 4172021 := bbase (se 5 (by rfl) ⟨195563, by rfl⟩ : syracuseStep 4172021 = 391127) (by norm_num)
theorem B5941525 : Blo 1853628 5941525 := bbase (se 6 (by rfl) ⟨139254, by rfl⟩ : syracuseStep 5941525 = 278509) (by norm_num)
theorem B6261029 : Blo 1853628 6261029 := bbase (se 4 (by rfl) ⟨586971, by rfl⟩ : syracuseStep 6261029 = 1173943) (by norm_num)
theorem B4172093 : Blo 1853628 4172093 := bbase (se 3 (by rfl) ⟨782267, by rfl⟩ : syracuseStep 4172093 = 1564535) (by norm_num)
theorem B2640205 : Blo 1853628 2640205 := bbase (se 3 (by rfl) ⟨495038, by rfl⟩ : syracuseStep 2640205 = 990077) (by norm_num)
theorem B4172165 : Blo 1853628 4172165 := bbase (se 4 (by rfl) ⟨391140, by rfl⟩ : syracuseStep 4172165 = 782281) (by norm_num)
theorem B4696501 : Blo 1853628 4696501 := bbase (se 5 (by rfl) ⟨220148, by rfl⟩ : syracuseStep 4696501 = 440297) (by norm_num)
theorem B4172237 : Blo 1853628 4172237 := bbase (se 3 (by rfl) ⟨782294, by rfl⟩ : syracuseStep 4172237 = 1564589) (by norm_num)
theorem B2288101 : Blo 1853628 2288101 := bbase (se 4 (by rfl) ⟨214509, by rfl⟩ : syracuseStep 2288101 = 429019) (by norm_num)
theorem B4172309 : Blo 1853628 4172309 := bbase (se 6 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 4172309 = 195577) (by norm_num)
theorem B4696613 : Blo 1853628 4696613 := bbase (se 4 (by rfl) ⟨440307, by rfl⟩ : syracuseStep 4696613 = 880615) (by norm_num)
theorem B4172381 : Blo 1853628 4172381 := bbase (se 3 (by rfl) ⟨782321, by rfl⟩ : syracuseStep 4172381 = 1564643) (by norm_num)
theorem B9513605 : Blo 1853628 9513605 := bbase (se 4 (by rfl) ⟨891900, by rfl⟩ : syracuseStep 9513605 = 1783801) (by norm_num)
theorem B2640541 : Blo 1853628 2640541 := bbase (se 3 (by rfl) ⟨495101, by rfl⟩ : syracuseStep 2640541 = 990203) (by norm_num)
theorem B4172453 : Blo 1853628 4172453 := bbase (se 4 (by rfl) ⟨391167, by rfl⟩ : syracuseStep 4172453 = 782335) (by norm_num)
theorem B6261461 : Blo 1853628 6261461 := bbase (se 7 (by rfl) ⟨73376, by rfl⟩ : syracuseStep 6261461 = 146753) (by norm_num)
theorem B4696805 : Blo 1853628 4696805 := bbase (se 4 (by rfl) ⟨440325, by rfl⟩ : syracuseStep 4696805 = 880651) (by norm_num)
theorem B4172525 : Blo 1853628 4172525 := bbase (se 3 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 4172525 = 1564697) (by norm_num)
theorem B6343429 : Blo 1853628 6343429 := bbase (se 4 (by rfl) ⟨594696, by rfl⟩ : syracuseStep 6343429 = 1189393) (by norm_num)
theorem B4172597 : Blo 1853628 4172597 := bbase (se 5 (by rfl) ⟨195590, by rfl⟩ : syracuseStep 4172597 = 391181) (by norm_num)
theorem B2640757 : Blo 1853628 2640757 := bbase (se 5 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 2640757 = 247571) (by norm_num)
theorem B4172669 : Blo 1853628 4172669 := bbase (se 3 (by rfl) ⟨782375, by rfl⟩ : syracuseStep 4172669 = 1564751) (by norm_num)
theorem B4172741 : Blo 1853628 4172741 := bbase (se 4 (by rfl) ⟨391194, by rfl⟩ : syracuseStep 4172741 = 782389) (by norm_num)
theorem B4172813 : Blo 1853628 4172813 := bbase (se 3 (by rfl) ⟨782402, by rfl⟩ : syracuseStep 4172813 = 1564805) (by norm_num)
theorem B2346013 : Blo 1853628 2346013 := bbase (se 3 (by rfl) ⟨439877, by rfl⟩ : syracuseStep 2346013 = 879755) (by norm_num)
theorem B4172885 : Blo 1853628 4172885 := bbase (se 8 (by rfl) ⟨24450, by rfl⟩ : syracuseStep 4172885 = 48901) (by norm_num)
theorem B6261893 : Blo 1853628 6261893 := bbase (se 4 (by rfl) ⟨587052, by rfl⟩ : syracuseStep 6261893 = 1174105) (by norm_num)
theorem B4172957 : Blo 1853628 4172957 := bbase (se 3 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 4172957 = 1564859) (by norm_num)
theorem B5500069 : Blo 1853628 5500069 := bbase (se 4 (by rfl) ⟨515631, by rfl⟩ : syracuseStep 5500069 = 1031263) (by norm_num)
theorem B4345013 : Blo 1853628 4345013 := bbase (se 5 (by rfl) ⟨203672, by rfl⟩ : syracuseStep 4345013 = 407345) (by norm_num)
theorem B9391301 : Blo 1853628 9391301 := bbase (se 4 (by rfl) ⟨880434, by rfl⟩ : syracuseStep 9391301 = 1760869) (by norm_num)
theorem B2346185 : Blo 1853628 2346185 := bbase (se 2 (by rfl) ⟨879819, by rfl⟩ : syracuseStep 2346185 = 1759639) (by norm_num)
theorem B4173029 : Blo 1853628 4173029 := bbase (se 4 (by rfl) ⟨391221, by rfl⟩ : syracuseStep 4173029 = 782443) (by norm_num)
theorem B2641133 : Blo 1853628 2641133 := bbase (se 3 (by rfl) ⟨495212, by rfl⟩ : syracuseStep 2641133 = 990425) (by norm_num)
theorem B2346241 : Blo 1853628 2346241 := bbase (se 2 (by rfl) ⟨879840, by rfl⟩ : syracuseStep 2346241 = 1759681) (by norm_num)
theorem B2780453 : Blo 1853628 2780453 := bbase (se 4 (by rfl) ⟨260667, by rfl⟩ : syracuseStep 2780453 = 521335) (by norm_num)
theorem B4173101 : Blo 1853628 4173101 := bbase (se 3 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 4173101 = 1564913) (by norm_num)
theorem B2780477 : Blo 1853628 2780477 := bbase (se 3 (by rfl) ⟨521339, by rfl⟩ : syracuseStep 2780477 = 1042679) (by norm_num)
theorem B2780501 : Blo 1853628 2780501 := bbase (se 11 (by rfl) ⟨2036, by rfl⟩ : syracuseStep 2780501 = 4073) (by norm_num)
theorem B2346337 : Blo 1853628 2346337 := bbase (se 2 (by rfl) ⟨879876, by rfl⟩ : syracuseStep 2346337 = 1759753) (by norm_num)
theorem B2780525 : Blo 1853628 2780525 := bbase (se 3 (by rfl) ⟨521348, by rfl⟩ : syracuseStep 2780525 = 1042697) (by norm_num)
theorem B1879409 : Blo 1853628 1879409 := bbase (se 2 (by rfl) ⟨704778, by rfl⟩ : syracuseStep 1879409 = 1409557) (by norm_num)
theorem B4173173 : Blo 1853628 4173173 := bbase (se 5 (by rfl) ⟨195617, by rfl⟩ : syracuseStep 4173173 = 391235) (by norm_num)
theorem B2780549 : Blo 1853628 2780549 := bbase (se 4 (by rfl) ⟨260676, by rfl⟩ : syracuseStep 2780549 = 521353) (by norm_num)
theorem B7925141 : Blo 1853628 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B2780573 : Blo 1853628 2780573 := bbase (se 3 (by rfl) ⟨521357, by rfl⟩ : syracuseStep 2780573 = 1042715) (by norm_num)
theorem B2780597 : Blo 1853628 2780597 := bbase (se 5 (by rfl) ⟨130340, by rfl⟩ : syracuseStep 2780597 = 260681) (by norm_num)
theorem B4173245 : Blo 1853628 4173245 := bbase (se 3 (by rfl) ⟨782483, by rfl⟩ : syracuseStep 4173245 = 1564967) (by norm_num)
theorem B2780621 : Blo 1853628 2780621 := bbase (se 3 (by rfl) ⟨521366, by rfl⟩ : syracuseStep 2780621 = 1042733) (by norm_num)
theorem B2780645 : Blo 1853628 2780645 := bbase (se 4 (by rfl) ⟨260685, by rfl⟩ : syracuseStep 2780645 = 521371) (by norm_num)
theorem B2780669 : Blo 1853628 2780669 := bbase (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) (by norm_num)
theorem B4173317 : Blo 1853628 4173317 := bbase (se 4 (by rfl) ⟨391248, by rfl⟩ : syracuseStep 4173317 = 782497) (by norm_num)
theorem B2346509 : Blo 1853628 2346509 := bbase (se 3 (by rfl) ⟨439970, by rfl⟩ : syracuseStep 2346509 = 879941) (by norm_num)
theorem B2780693 : Blo 1853628 2780693 := bbase (se 6 (by rfl) ⟨65172, by rfl⟩ : syracuseStep 2780693 = 130345) (by norm_num)
theorem B2780717 : Blo 1853628 2780717 := bbase (se 3 (by rfl) ⟨521384, by rfl⟩ : syracuseStep 2780717 = 1042769) (by norm_num)
theorem B6262325 : Blo 1853628 6262325 := bbase (se 5 (by rfl) ⟨293546, by rfl⟩ : syracuseStep 6262325 = 587093) (by norm_num)
theorem B2780741 : Blo 1853628 2780741 := bbase (se 4 (by rfl) ⟨260694, by rfl⟩ : syracuseStep 2780741 = 521389) (by norm_num)
theorem B2346565 : Blo 1853628 2346565 := bbase (se 4 (by rfl) ⟨219990, by rfl⟩ : syracuseStep 2346565 = 439981) (by norm_num)
theorem B4173389 : Blo 1853628 4173389 := bbase (se 3 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 4173389 = 1565021) (by norm_num)
theorem B2780765 : Blo 1853628 2780765 := bbase (se 3 (by rfl) ⟨521393, by rfl⟩ : syracuseStep 2780765 = 1042787) (by norm_num)
theorem B2780789 : Blo 1853628 2780789 := bbase (se 5 (by rfl) ⟨130349, by rfl⟩ : syracuseStep 2780789 = 260699) (by norm_num)
theorem B2780813 : Blo 1853628 2780813 := bbase (se 3 (by rfl) ⟨521402, by rfl⟩ : syracuseStep 2780813 = 1042805) (by norm_num)
theorem B4173461 : Blo 1853628 4173461 := bbase (se 6 (by rfl) ⟨97815, by rfl⟩ : syracuseStep 4173461 = 195631) (by norm_num)
theorem B2780837 : Blo 1853628 2780837 := bbase (se 4 (by rfl) ⟨260703, by rfl⟩ : syracuseStep 2780837 = 521407) (by norm_num)
theorem B2346661 : Blo 1853628 2346661 := bbase (se 4 (by rfl) ⟨219999, by rfl⟩ : syracuseStep 2346661 = 439999) (by norm_num)
theorem B2780861 : Blo 1853628 2780861 := bbase (se 3 (by rfl) ⟨521411, by rfl⟩ : syracuseStep 2780861 = 1042823) (by norm_num)
theorem B2780885 : Blo 1853628 2780885 := bbase (se 7 (by rfl) ⟨32588, by rfl⟩ : syracuseStep 2780885 = 65177) (by norm_num)
theorem B1879765 : Blo 1853628 1879765 := bbase (se 7 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 1879765 = 44057) (by norm_num)
theorem B4173533 : Blo 1853628 4173533 := bbase (se 3 (by rfl) ⟨782537, by rfl⟩ : syracuseStep 4173533 = 1565075) (by norm_num)
theorem B3567341 : Blo 1853628 3567341 := bbase (se 3 (by rfl) ⟨668876, by rfl⟩ : syracuseStep 3567341 = 1337753) (by norm_num)
theorem B2780909 : Blo 1853628 2780909 := bbase (se 3 (by rfl) ⟨521420, by rfl⟩ : syracuseStep 2780909 = 1042841) (by norm_num)
theorem B2780933 : Blo 1853628 2780933 := bbase (se 4 (by rfl) ⟨260712, by rfl⟩ : syracuseStep 2780933 = 521425) (by norm_num)
theorem B3960589 : Blo 1853628 3960589 := bbase (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) (by norm_num)
theorem B5279509 : Blo 1853628 5279509 := bbase (se 6 (by rfl) ⟨123738, by rfl⟩ : syracuseStep 5279509 = 247477) (by norm_num)
theorem B23760661 : Blo 1853628 23760661 := bbase (se 6 (by rfl) ⟨556890, by rfl⟩ : syracuseStep 23760661 = 1113781) (by norm_num)
theorem B7040789 : Blo 1853628 7040789 := bbase (se 6 (by rfl) ⟨165018, by rfl⟩ : syracuseStep 7040789 = 330037) (by norm_num)
theorem B2780957 : Blo 1853628 2780957 := bbase (se 3 (by rfl) ⟨521429, by rfl⟩ : syracuseStep 2780957 = 1042859) (by norm_num)
theorem B5353253 : Blo 1853628 5353253 := bbase (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) (by norm_num)
theorem B4173605 : Blo 1853628 4173605 := bbase (se 4 (by rfl) ⟨391275, by rfl⟩ : syracuseStep 4173605 = 782551) (by norm_num)
theorem B2780981 : Blo 1853628 2780981 := bbase (se 5 (by rfl) ⟨130358, by rfl⟩ : syracuseStep 2780981 = 260717) (by norm_num)
theorem B2781005 : Blo 1853628 2781005 := bbase (se 3 (by rfl) ⟨521438, by rfl⟩ : syracuseStep 2781005 = 1042877) (by norm_num)
theorem B2346833 : Blo 1853628 2346833 := bbase (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) (by norm_num)
theorem B76156757 : Blo 1853628 76156757 := bbase (se 9 (by rfl) ⟨223115, by rfl⟩ : syracuseStep 76156757 = 446231) (by norm_num)
theorem B5082965 : Blo 1853628 5082965 := bbase (se 9 (by rfl) ⟨14891, by rfl⟩ : syracuseStep 5082965 = 29783) (by norm_num)
theorem B2781029 : Blo 1853628 2781029 := bbase (se 4 (by rfl) ⟨260721, by rfl⟩ : syracuseStep 2781029 = 521443) (by norm_num)
theorem B4173677 : Blo 1853628 4173677 := bbase (se 3 (by rfl) ⟨782564, by rfl⟩ : syracuseStep 4173677 = 1565129) (by norm_num)
theorem B2781053 : Blo 1853628 2781053 := bbase (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) (by norm_num)
theorem B2346889 : Blo 1853628 2346889 := bbase (se 2 (by rfl) ⟨880083, by rfl⟩ : syracuseStep 2346889 = 1760167) (by norm_num)
theorem B2781077 : Blo 1853628 2781077 := bbase (se 6 (by rfl) ⟨65181, by rfl⟩ : syracuseStep 2781077 = 130363) (by norm_num)
theorem B2781101 : Blo 1853628 2781101 := bbase (se 3 (by rfl) ⟨521456, by rfl⟩ : syracuseStep 2781101 = 1042913) (by norm_num)
theorem B4173749 : Blo 1853628 4173749 := bbase (se 5 (by rfl) ⟨195644, by rfl⟩ : syracuseStep 4173749 = 391289) (by norm_num)
theorem B5713861 : Blo 1853628 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B2781125 : Blo 1853628 2781125 := bbase (se 4 (by rfl) ⟨260730, by rfl⟩ : syracuseStep 2781125 = 521461) (by norm_num)
theorem B2781149 : Blo 1853628 2781149 := bbase (se 3 (by rfl) ⟨521465, by rfl⟩ : syracuseStep 2781149 = 1042931) (by norm_num)
theorem B2346985 : Blo 1853628 2346985 := bbase (se 2 (by rfl) ⟨880119, by rfl⟩ : syracuseStep 2346985 = 1760239) (by norm_num)
theorem B2781173 : Blo 1853628 2781173 := bbase (se 5 (by rfl) ⟨130367, by rfl⟩ : syracuseStep 2781173 = 260735) (by norm_num)
theorem B2969597 : Blo 1853628 2969597 := bbase (se 3 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 2969597 = 1113599) (by norm_num)
theorem B4173821 : Blo 1853628 4173821 := bbase (se 3 (by rfl) ⟨782591, by rfl⟩ : syracuseStep 4173821 = 1565183) (by norm_num)
theorem B2781197 : Blo 1853628 2781197 := bbase (se 3 (by rfl) ⟨521474, by rfl⟩ : syracuseStep 2781197 = 1042949) (by norm_num)
theorem B2781221 : Blo 1853628 2781221 := bbase (se 4 (by rfl) ⟨260739, by rfl⟩ : syracuseStep 2781221 = 521479) (by norm_num)
theorem B7041077 : Blo 1853628 7041077 := bbase (se 5 (by rfl) ⟨330050, by rfl⟩ : syracuseStep 7041077 = 660101) (by norm_num)
theorem B2781245 : Blo 1853628 2781245 := bbase (se 3 (by rfl) ⟨521483, by rfl⟩ : syracuseStep 2781245 = 1042967) (by norm_num)
theorem B4173893 : Blo 1853628 4173893 := bbase (se 4 (by rfl) ⟨391302, by rfl⟩ : syracuseStep 4173893 = 782605) (by norm_num)
theorem B2781269 : Blo 1853628 2781269 := bbase (se 8 (by rfl) ⟨16296, by rfl⟩ : syracuseStep 2781269 = 32593) (by norm_num)
theorem B2781293 : Blo 1853628 2781293 := bbase (se 3 (by rfl) ⟨521492, by rfl⟩ : syracuseStep 2781293 = 1042985) (by norm_num)
theorem B2781317 : Blo 1853628 2781317 := bbase (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) (by norm_num)
theorem B4173965 : Blo 1853628 4173965 := bbase (se 3 (by rfl) ⟨782618, by rfl⟩ : syracuseStep 4173965 = 1565237) (by norm_num)
theorem B2347157 : Blo 1853628 2347157 := bbase (se 6 (by rfl) ⟨55011, by rfl⟩ : syracuseStep 2347157 = 110023) (by norm_num)
theorem B2781341 : Blo 1853628 2781341 := bbase (se 3 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 2781341 = 1043003) (by norm_num)
theorem B2379937 : Blo 1853628 2379937 := bbase (se 2 (by rfl) ⟨892476, by rfl⟩ : syracuseStep 2379937 = 1784953) (by norm_num)
theorem B2781365 : Blo 1853628 2781365 := bbase (se 5 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 2781365 = 260753) (by norm_num)
theorem B3387589 : Blo 1853628 3387589 := bbase (se 4 (by rfl) ⟨317586, by rfl⟩ : syracuseStep 3387589 = 635173) (by norm_num)
theorem B2781389 : Blo 1853628 2781389 := bbase (se 3 (by rfl) ⟨521510, by rfl⟩ : syracuseStep 2781389 = 1043021) (by norm_num)
theorem B2347213 : Blo 1853628 2347213 := bbase (se 3 (by rfl) ⟨440102, by rfl⟩ : syracuseStep 2347213 = 880205) (by norm_num)
theorem B4174037 : Blo 1853628 4174037 := bbase (se 7 (by rfl) ⟨48914, by rfl⟩ : syracuseStep 4174037 = 97829) (by norm_num)
theorem B2969821 : Blo 1853628 2969821 := bbase (se 3 (by rfl) ⟨556841, by rfl⟩ : syracuseStep 2969821 = 1113683) (by norm_num)
theorem B2781413 : Blo 1853628 2781413 := bbase (se 4 (by rfl) ⟨260757, by rfl⟩ : syracuseStep 2781413 = 521515) (by norm_num)
theorem B2781437 : Blo 1853628 2781437 := bbase (se 3 (by rfl) ⟨521519, by rfl⟩ : syracuseStep 2781437 = 1043039) (by norm_num)
theorem B1880317 : Blo 1853628 1880317 := bbase (se 3 (by rfl) ⟨352559, by rfl⟩ : syracuseStep 1880317 = 705119) (by norm_num)
theorem B2781461 : Blo 1853628 2781461 := bbase (se 6 (by rfl) ⟨65190, by rfl⟩ : syracuseStep 2781461 = 130381) (by norm_num)
theorem B4174109 : Blo 1853628 4174109 := bbase (se 3 (by rfl) ⟨782645, by rfl⟩ : syracuseStep 4174109 = 1565291) (by norm_num)
theorem B3387685 : Blo 1853628 3387685 := bbase (se 4 (by rfl) ⟨317595, by rfl⟩ : syracuseStep 3387685 = 635191) (by norm_num)
theorem B2781485 : Blo 1853628 2781485 := bbase (se 3 (by rfl) ⟨521528, by rfl⟩ : syracuseStep 2781485 = 1043057) (by norm_num)
theorem B2347309 : Blo 1853628 2347309 := bbase (se 3 (by rfl) ⟨440120, by rfl⟩ : syracuseStep 2347309 = 880241) (by norm_num)
theorem B2781509 : Blo 1853628 2781509 := bbase (se 4 (by rfl) ⟨260766, by rfl⟩ : syracuseStep 2781509 = 521533) (by norm_num)
theorem B2781533 : Blo 1853628 2781533 := bbase (se 3 (by rfl) ⟨521537, by rfl⟩ : syracuseStep 2781533 = 1043075) (by norm_num)
theorem B4174181 : Blo 1853628 4174181 := bbase (se 4 (by rfl) ⟨391329, by rfl⟩ : syracuseStep 4174181 = 782659) (by norm_num)
theorem B3051893 : Blo 1853628 3051893 := bbase (se 5 (by rfl) ⟨143057, by rfl⟩ : syracuseStep 3051893 = 286115) (by norm_num)
theorem B2781557 : Blo 1853628 2781557 := bbase (se 5 (by rfl) ⟨130385, by rfl⟩ : syracuseStep 2781557 = 260771) (by norm_num)
theorem B7926133 : Blo 1853628 7926133 := bbase (se 5 (by rfl) ⟨371537, by rfl⟩ : syracuseStep 7926133 = 743075) (by norm_num)
theorem B2781581 : Blo 1853628 2781581 := bbase (se 3 (by rfl) ⟨521546, by rfl⟩ : syracuseStep 2781581 = 1043093) (by norm_num)
theorem B2781605 : Blo 1853628 2781605 := bbase (se 4 (by rfl) ⟨260775, by rfl⟩ : syracuseStep 2781605 = 521551) (by norm_num)
theorem B4174253 : Blo 1853628 4174253 := bbase (se 3 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 4174253 = 1565345) (by norm_num)
theorem B7516597 : Blo 1853628 7516597 := bbase (se 5 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 7516597 = 704681) (by norm_num)
theorem B2781629 : Blo 1853628 2781629 := bbase (se 3 (by rfl) ⟨521555, by rfl⟩ : syracuseStep 2781629 = 1043111) (by norm_num)
theorem B2781653 : Blo 1853628 2781653 := bbase (se 7 (by rfl) ⟨32597, by rfl⟩ : syracuseStep 2781653 = 65195) (by norm_num)
theorem B9392597 : Blo 1853628 9392597 := bbase (se 7 (by rfl) ⟨110069, by rfl⟩ : syracuseStep 9392597 = 220139) (by norm_num)
theorem B13373909 : Blo 1853628 13373909 := bbase (se 7 (by rfl) ⟨156725, by rfl⟩ : syracuseStep 13373909 = 313451) (by norm_num)
theorem B2347481 : Blo 1853628 2347481 := bbase (se 2 (by rfl) ⟨880305, by rfl⟩ : syracuseStep 2347481 = 1760611) (by norm_num)
theorem B2085349 : Blo 1853628 2085349 := bbase (se 4 (by rfl) ⟨195501, by rfl⟩ : syracuseStep 2085349 = 391003) (by norm_num)
theorem B2781677 : Blo 1853628 2781677 := bbase (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) (by norm_num)
theorem B4174325 : Blo 1853628 4174325 := bbase (se 5 (by rfl) ⟨195671, by rfl⟩ : syracuseStep 4174325 = 391343) (by norm_num)
theorem B2781701 : Blo 1853628 2781701 := bbase (se 4 (by rfl) ⟨260784, by rfl⟩ : syracuseStep 2781701 = 521569) (by norm_num)
theorem B2085385 : Blo 1853628 2085385 := bbase (se 2 (by rfl) ⟨782019, by rfl⟩ : syracuseStep 2085385 = 1564039) (by norm_num)
theorem B2347537 : Blo 1853628 2347537 := bbase (se 2 (by rfl) ⟨880326, by rfl⟩ : syracuseStep 2347537 = 1760653) (by norm_num)
theorem B2781725 : Blo 1853628 2781725 := bbase (se 3 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 2781725 = 1043147) (by norm_num)
theorem B2085421 : Blo 1853628 2085421 := bbase (se 3 (by rfl) ⟨391016, by rfl⟩ : syracuseStep 2085421 = 782033) (by norm_num)
theorem B2781749 : Blo 1853628 2781749 := bbase (se 5 (by rfl) ⟨130394, by rfl⟩ : syracuseStep 2781749 = 260789) (by norm_num)
theorem B14086709 : Blo 1853628 14086709 := bbase (se 5 (by rfl) ⟨660314, by rfl⟩ : syracuseStep 14086709 = 1320629) (by norm_num)
theorem B4174397 : Blo 1853628 4174397 := bbase (se 3 (by rfl) ⟨782699, by rfl⟩ : syracuseStep 4174397 = 1565399) (by norm_num)
theorem B2781773 : Blo 1853628 2781773 := bbase (se 3 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 2781773 = 1043165) (by norm_num)
theorem B2085457 : Blo 1853628 2085457 := bbase (se 2 (by rfl) ⟨782046, by rfl⟩ : syracuseStep 2085457 = 1564093) (by norm_num)
theorem B2781797 : Blo 1853628 2781797 := bbase (se 4 (by rfl) ⟨260793, by rfl⟩ : syracuseStep 2781797 = 521587) (by norm_num)
theorem B2347633 : Blo 1853628 2347633 := bbase (se 2 (by rfl) ⟨880362, by rfl⟩ : syracuseStep 2347633 = 1760725) (by norm_num)
theorem B2085493 : Blo 1853628 2085493 := bbase (se 5 (by rfl) ⟨97757, by rfl⟩ : syracuseStep 2085493 = 195515) (by norm_num)
theorem B2781821 : Blo 1853628 2781821 := bbase (se 3 (by rfl) ⟨521591, by rfl⟩ : syracuseStep 2781821 = 1043183) (by norm_num)
theorem B3961477 : Blo 1853628 3961477 := bbase (se 4 (by rfl) ⟨371388, by rfl⟩ : syracuseStep 3961477 = 742777) (by norm_num)
theorem B4174469 : Blo 1853628 4174469 := bbase (se 4 (by rfl) ⟨391356, by rfl⟩ : syracuseStep 4174469 = 782713) (by norm_num)
theorem B2781845 : Blo 1853628 2781845 := bbase (se 6 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 2781845 = 130399) (by norm_num)
theorem B19075733 : Blo 1853628 19075733 := bbase (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) (by norm_num)
theorem B5640853 : Blo 1853628 5640853 := bbase (se 6 (by rfl) ⟨132207, by rfl⟩ : syracuseStep 5640853 = 264415) (by norm_num)
theorem B2085529 : Blo 1853628 2085529 := bbase (se 2 (by rfl) ⟨782073, by rfl⟩ : syracuseStep 2085529 = 1564147) (by norm_num)
theorem B2257565 : Blo 1853628 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B2781869 : Blo 1853628 2781869 := bbase (se 3 (by rfl) ⟨521600, by rfl⟩ : syracuseStep 2781869 = 1043201) (by norm_num)
theorem B2085565 : Blo 1853628 2085565 := bbase (se 3 (by rfl) ⟨391043, by rfl⟩ : syracuseStep 2085565 = 782087) (by norm_num)
theorem B4289213 : Blo 1853628 4289213 := bbase (se 3 (by rfl) ⟨804227, by rfl⟩ : syracuseStep 4289213 = 1608455) (by norm_num)
theorem B2781893 : Blo 1853628 2781893 := bbase (se 4 (by rfl) ⟨260802, by rfl⟩ : syracuseStep 2781893 = 521605) (by norm_num)
theorem B4174541 : Blo 1853628 4174541 := bbase (se 3 (by rfl) ⟨782726, by rfl⟩ : syracuseStep 4174541 = 1565453) (by norm_num)
theorem B2781917 : Blo 1853628 2781917 := bbase (se 3 (by rfl) ⟨521609, by rfl⟩ : syracuseStep 2781917 = 1043219) (by norm_num)
theorem B2085601 : Blo 1853628 2085601 := bbase (se 2 (by rfl) ⟨782100, by rfl⟩ : syracuseStep 2085601 = 1564201) (by norm_num)
theorem B4518629 : Blo 1853628 4518629 := bbase (se 4 (by rfl) ⟨423621, by rfl⟩ : syracuseStep 4518629 = 847243) (by norm_num)
theorem B2781941 : Blo 1853628 2781941 := bbase (se 5 (by rfl) ⟨130403, by rfl⟩ : syracuseStep 2781941 = 260807) (by norm_num)
theorem B2085637 : Blo 1853628 2085637 := bbase (se 4 (by rfl) ⟨195528, by rfl⟩ : syracuseStep 2085637 = 391057) (by norm_num)
theorem B2781965 : Blo 1853628 2781965 := bbase (se 3 (by rfl) ⟨521618, by rfl⟩ : syracuseStep 2781965 = 1043237) (by norm_num)
theorem B3863317 : Blo 1853628 3863317 := bbase (se 6 (by rfl) ⟨90546, by rfl⟩ : syracuseStep 3863317 = 181093) (by norm_num)
theorem B4174613 : Blo 1853628 4174613 := bbase (se 6 (by rfl) ⟨97842, by rfl⟩ : syracuseStep 4174613 = 195685) (by norm_num)
theorem B2347805 : Blo 1853628 2347805 := bbase (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) (by norm_num)
theorem B2781989 : Blo 1853628 2781989 := bbase (se 4 (by rfl) ⟨260811, by rfl⟩ : syracuseStep 2781989 = 521623) (by norm_num)
theorem B2085673 : Blo 1853628 2085673 := bbase (se 2 (by rfl) ⟨782127, by rfl⟩ : syracuseStep 2085673 = 1564255) (by norm_num)
theorem B2782013 : Blo 1853628 2782013 := bbase (se 3 (by rfl) ⟨521627, by rfl⟩ : syracuseStep 2782013 = 1043255) (by norm_num)
theorem B3519301 : Blo 1853628 3519301 := bbase (se 4 (by rfl) ⟨329934, by rfl⟩ : syracuseStep 3519301 = 659869) (by norm_num)
theorem B2085709 : Blo 1853628 2085709 := bbase (se 3 (by rfl) ⟨391070, by rfl⟩ : syracuseStep 2085709 = 782141) (by norm_num)
theorem B2782037 : Blo 1853628 2782037 := bbase (se 9 (by rfl) ⟨8150, by rfl⟩ : syracuseStep 2782037 = 16301) (by norm_num)
theorem B2347861 : Blo 1853628 2347861 := bbase (se 9 (by rfl) ⟨6878, by rfl⟩ : syracuseStep 2347861 = 13757) (by norm_num)
theorem B4174685 : Blo 1853628 4174685 := bbase (se 3 (by rfl) ⟨782753, by rfl⟩ : syracuseStep 4174685 = 1565507) (by norm_num)
theorem B2782061 : Blo 1853628 2782061 := bbase (se 3 (by rfl) ⟨521636, by rfl⟩ : syracuseStep 2782061 = 1043273) (by norm_num)
theorem B2085745 : Blo 1853628 2085745 := bbase (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) (by norm_num)
theorem B9384821 : Blo 1853628 9384821 := bbase (se 5 (by rfl) ⟨439913, by rfl⟩ : syracuseStep 9384821 = 879827) (by norm_num)
theorem B2675581 : Blo 1853628 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B2782085 : Blo 1853628 2782085 := bbase (se 4 (by rfl) ⟨260820, by rfl⟩ : syracuseStep 2782085 = 521641) (by norm_num)
theorem B4756373 : Blo 1853628 4756373 := bbase (se 6 (by rfl) ⟨111477, by rfl⟩ : syracuseStep 4756373 = 222955) (by norm_num)
theorem B2085781 : Blo 1853628 2085781 := bbase (se 6 (by rfl) ⟨48885, by rfl⟩ : syracuseStep 2085781 = 97771) (by norm_num)
theorem B2782109 : Blo 1853628 2782109 := bbase (se 3 (by rfl) ⟨521645, by rfl⟩ : syracuseStep 2782109 = 1043291) (by norm_num)
theorem B4174757 : Blo 1853628 4174757 := bbase (se 4 (by rfl) ⟨391383, by rfl⟩ : syracuseStep 4174757 = 782767) (by norm_num)
theorem B2782133 : Blo 1853628 2782133 := bbase (se 5 (by rfl) ⟨130412, by rfl⟩ : syracuseStep 2782133 = 260825) (by norm_num)
theorem B2347957 : Blo 1853628 2347957 := bbase (se 5 (by rfl) ⟨110060, by rfl⟩ : syracuseStep 2347957 = 220121) (by norm_num)
theorem B2085817 : Blo 1853628 2085817 := bbase (se 2 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 2085817 = 1564363) (by norm_num)
theorem B2782157 : Blo 1853628 2782157 := bbase (se 3 (by rfl) ⟨521654, by rfl⟩ : syracuseStep 2782157 = 1043309) (by norm_num)
theorem B3519445 : Blo 1853628 3519445 := bbase (se 7 (by rfl) ⟨41243, by rfl⟩ : syracuseStep 3519445 = 82487) (by norm_num)
theorem B14078933 : Blo 1853628 14078933 := bbase (se 7 (by rfl) ⟨164987, by rfl⟩ : syracuseStep 14078933 = 329975) (by norm_num)
theorem B2085853 : Blo 1853628 2085853 := bbase (se 3 (by rfl) ⟨391097, by rfl⟩ : syracuseStep 2085853 = 782195) (by norm_num)
theorem B2782181 : Blo 1853628 2782181 := bbase (se 4 (by rfl) ⟨260829, by rfl⟩ : syracuseStep 2782181 = 521659) (by norm_num)
theorem B4174829 : Blo 1853628 4174829 := bbase (se 3 (by rfl) ⟨782780, by rfl⟩ : syracuseStep 4174829 = 1565561) (by norm_num)
theorem B2782205 : Blo 1853628 2782205 := bbase (se 3 (by rfl) ⟨521663, by rfl⟩ : syracuseStep 2782205 = 1043327) (by norm_num)
theorem B2085889 : Blo 1853628 2085889 := bbase (se 2 (by rfl) ⟨782208, by rfl⟩ : syracuseStep 2085889 = 1564417) (by norm_num)
theorem B2782229 : Blo 1853628 2782229 := bbase (se 6 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 2782229 = 130417) (by norm_num)
theorem B2085925 : Blo 1853628 2085925 := bbase (se 4 (by rfl) ⟨195555, by rfl⟩ : syracuseStep 2085925 = 391111) (by norm_num)
theorem B5944357 : Blo 1853628 5944357 := bbase (se 4 (by rfl) ⟨557283, by rfl⟩ : syracuseStep 5944357 = 1114567) (by norm_num)
theorem B2782253 : Blo 1853628 2782253 := bbase (se 3 (by rfl) ⟨521672, by rfl⟩ : syracuseStep 2782253 = 1043345) (by norm_num)
theorem B4174901 : Blo 1853628 4174901 := bbase (se 5 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 4174901 = 391397) (by norm_num)
theorem B2782277 : Blo 1853628 2782277 := bbase (se 4 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 2782277 = 521677) (by norm_num)
theorem B2085961 : Blo 1853628 2085961 := bbase (se 2 (by rfl) ⟨782235, by rfl⟩ : syracuseStep 2085961 = 1564471) (by norm_num)
theorem B2782301 : Blo 1853628 2782301 := bbase (se 3 (by rfl) ⟨521681, by rfl⟩ : syracuseStep 2782301 = 1043363) (by norm_num)
theorem B2348129 : Blo 1853628 2348129 := bbase (se 2 (by rfl) ⟨880548, by rfl⟩ : syracuseStep 2348129 = 1761097) (by norm_num)
theorem B5944421 : Blo 1853628 5944421 := bbase (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) (by norm_num)
theorem B2085997 : Blo 1853628 2085997 := bbase (se 3 (by rfl) ⟨391124, by rfl⟩ : syracuseStep 2085997 = 782249) (by norm_num)
theorem B3519605 : Blo 1853628 3519605 := bbase (se 5 (by rfl) ⟨164981, by rfl⟩ : syracuseStep 3519605 = 329963) (by norm_num)
theorem B8909941 : Blo 1853628 8909941 := bbase (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) (by norm_num)
theorem B2782325 : Blo 1853628 2782325 := bbase (se 5 (by rfl) ⟨130421, by rfl⟩ : syracuseStep 2782325 = 260843) (by norm_num)
theorem B3961973 : Blo 1853628 3961973 := bbase (se 5 (by rfl) ⟨185717, by rfl⟩ : syracuseStep 3961973 = 371435) (by norm_num)
theorem B4174973 : Blo 1853628 4174973 := bbase (se 3 (by rfl) ⟨782807, by rfl⟩ : syracuseStep 4174973 = 1565615) (by norm_num)
theorem B2782349 : Blo 1853628 2782349 := bbase (se 3 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 2782349 = 1043381) (by norm_num)
theorem B2086033 : Blo 1853628 2086033 := bbase (se 2 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 2086033 = 1564525) (by norm_num)
theorem B2348185 : Blo 1853628 2348185 := bbase (se 2 (by rfl) ⟨880569, by rfl⟩ : syracuseStep 2348185 = 1761139) (by norm_num)
theorem B2782373 : Blo 1853628 2782373 := bbase (se 4 (by rfl) ⟨260847, by rfl⟩ : syracuseStep 2782373 = 521695) (by norm_num)
theorem B2086069 : Blo 1853628 2086069 := bbase (se 5 (by rfl) ⟨97784, by rfl⟩ : syracuseStep 2086069 = 195569) (by norm_num)
theorem B2782397 : Blo 1853628 2782397 := bbase (se 3 (by rfl) ⟨521699, by rfl⟩ : syracuseStep 2782397 = 1043399) (by norm_num)
theorem B4175045 : Blo 1853628 4175045 := bbase (se 4 (by rfl) ⟨391410, by rfl⟩ : syracuseStep 4175045 = 782821) (by norm_num)
theorem B7042261 : Blo 1853628 7042261 := bbase (se 7 (by rfl) ⟨82526, by rfl⟩ : syracuseStep 7042261 = 165053) (by norm_num)
theorem B2782421 : Blo 1853628 2782421 := bbase (se 7 (by rfl) ⟨32606, by rfl⟩ : syracuseStep 2782421 = 65213) (by norm_num)
theorem B2086105 : Blo 1853628 2086105 := bbase (se 2 (by rfl) ⟨782289, by rfl⟩ : syracuseStep 2086105 = 1564579) (by norm_num)
theorem B2782445 : Blo 1853628 2782445 := bbase (se 3 (by rfl) ⟨521708, by rfl⟩ : syracuseStep 2782445 = 1043417) (by norm_num)
theorem B5281013 : Blo 1853628 5281013 := bbase (se 5 (by rfl) ⟨247547, by rfl⟩ : syracuseStep 5281013 = 495095) (by norm_num)
theorem B2348281 : Blo 1853628 2348281 := bbase (se 2 (by rfl) ⟨880605, by rfl⟩ : syracuseStep 2348281 = 1761211) (by norm_num)
theorem B1979645 : Blo 1853628 1979645 := bbase (se 3 (by rfl) ⟨371183, by rfl⟩ : syracuseStep 1979645 = 742367) (by norm_num)
theorem B2086141 : Blo 1853628 2086141 := bbase (se 3 (by rfl) ⟨391151, by rfl⟩ : syracuseStep 2086141 = 782303) (by norm_num)
theorem B3519749 : Blo 1853628 3519749 := bbase (se 4 (by rfl) ⟨329976, by rfl⟩ : syracuseStep 3519749 = 659953) (by norm_num)
theorem B2782469 : Blo 1853628 2782469 := bbase (se 4 (by rfl) ⟨260856, by rfl⟩ : syracuseStep 2782469 = 521713) (by norm_num)
theorem B4175117 : Blo 1853628 4175117 := bbase (se 3 (by rfl) ⟨782834, by rfl⟩ : syracuseStep 4175117 = 1565669) (by norm_num)
theorem B2782493 : Blo 1853628 2782493 := bbase (se 3 (by rfl) ⟨521717, by rfl⟩ : syracuseStep 2782493 = 1043435) (by norm_num)
theorem B2086177 : Blo 1853628 2086177 := bbase (se 2 (by rfl) ⟨782316, by rfl⟩ : syracuseStep 2086177 = 1564633) (by norm_num)
theorem B2782517 : Blo 1853628 2782517 := bbase (se 5 (by rfl) ⟨130430, by rfl⟩ : syracuseStep 2782517 = 260861) (by norm_num)
theorem B2086213 : Blo 1853628 2086213 := bbase (se 4 (by rfl) ⟨195582, by rfl⟩ : syracuseStep 2086213 = 391165) (by norm_num)
theorem B2782541 : Blo 1853628 2782541 := bbase (se 3 (by rfl) ⟨521726, by rfl⟩ : syracuseStep 2782541 = 1043453) (by norm_num)
theorem B2782565 : Blo 1853628 2782565 := bbase (se 4 (by rfl) ⟨260865, by rfl⟩ : syracuseStep 2782565 = 521731) (by norm_num)
theorem B2086249 : Blo 1853628 2086249 := bbase (se 2 (by rfl) ⟨782343, by rfl⟩ : syracuseStep 2086249 = 1564687) (by norm_num)
theorem B16921973 : Blo 1853628 16921973 := bbase (se 5 (by rfl) ⟨793217, by rfl⟩ : syracuseStep 16921973 = 1586435) (by norm_num)
theorem B2782589 : Blo 1853628 2782589 := bbase (se 3 (by rfl) ⟨521735, by rfl⟩ : syracuseStep 2782589 = 1043471) (by norm_num)
theorem B2086285 : Blo 1853628 2086285 := bbase (se 3 (by rfl) ⟨391178, by rfl⟩ : syracuseStep 2086285 = 782357) (by norm_num)
theorem B2782613 : Blo 1853628 2782613 := bbase (se 6 (by rfl) ⟨65217, by rfl⟩ : syracuseStep 2782613 = 130435) (by norm_num)
theorem B2348453 : Blo 1853628 2348453 := bbase (se 4 (by rfl) ⟨220167, by rfl⟩ : syracuseStep 2348453 = 440335) (by norm_num)
theorem B2782637 : Blo 1853628 2782637 := bbase (se 3 (by rfl) ⟨521744, by rfl⟩ : syracuseStep 2782637 = 1043489) (by norm_num)
theorem B2086321 : Blo 1853628 2086321 := bbase (se 2 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 2086321 = 1564741) (by norm_num)
theorem B2782661 : Blo 1853628 2782661 := bbase (se 4 (by rfl) ⟨260874, by rfl⟩ : syracuseStep 2782661 = 521749) (by norm_num)
theorem B2086357 : Blo 1853628 2086357 := bbase (se 7 (by rfl) ⟨24449, by rfl⟩ : syracuseStep 2086357 = 48899) (by norm_num)
theorem B2782685 : Blo 1853628 2782685 := bbase (se 3 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 2782685 = 1043507) (by norm_num)
theorem B2348509 : Blo 1853628 2348509 := bbase (se 3 (by rfl) ⟨440345, by rfl⟩ : syracuseStep 2348509 = 880691) (by norm_num)
theorem B1979893 : Blo 1853628 1979893 := bbase (se 5 (by rfl) ⟨92807, by rfl⟩ : syracuseStep 1979893 = 185615) (by norm_num)
theorem B2782709 : Blo 1853628 2782709 := bbase (se 5 (by rfl) ⟨130439, by rfl⟩ : syracuseStep 2782709 = 260879) (by norm_num)
theorem B2086393 : Blo 1853628 2086393 := bbase (se 2 (by rfl) ⟨782397, by rfl⟩ : syracuseStep 2086393 = 1564795) (by norm_num)
theorem B7042565 : Blo 1853628 7042565 := bbase (se 4 (by rfl) ⟨660240, by rfl⟩ : syracuseStep 7042565 = 1320481) (by norm_num)
theorem B2782733 : Blo 1853628 2782733 := bbase (se 3 (by rfl) ⟨521762, by rfl⟩ : syracuseStep 2782733 = 1043525) (by norm_num)
theorem B2086429 : Blo 1853628 2086429 := bbase (se 3 (by rfl) ⟨391205, by rfl⟩ : syracuseStep 2086429 = 782411) (by norm_num)
theorem B3520037 : Blo 1853628 3520037 := bbase (se 4 (by rfl) ⟨330003, by rfl⟩ : syracuseStep 3520037 = 660007) (by norm_num)
theorem B2782757 : Blo 1853628 2782757 := bbase (se 4 (by rfl) ⟨260883, by rfl⟩ : syracuseStep 2782757 = 521767) (by norm_num)
theorem B2782781 : Blo 1853628 2782781 := bbase (se 3 (by rfl) ⟨521771, by rfl⟩ : syracuseStep 2782781 = 1043543) (by norm_num)
theorem B2086465 : Blo 1853628 2086465 := bbase (se 2 (by rfl) ⟨782424, by rfl⟩ : syracuseStep 2086465 = 1564849) (by norm_num)
theorem B10557013 : Blo 1853628 10557013 := bbase (se 8 (by rfl) ⟨61857, by rfl⟩ : syracuseStep 10557013 = 123715) (by norm_num)
theorem B2782805 : Blo 1853628 2782805 := bbase (se 8 (by rfl) ⟨16305, by rfl⟩ : syracuseStep 2782805 = 32611) (by norm_num)
theorem B2086501 : Blo 1853628 2086501 := bbase (se 4 (by rfl) ⟨195609, by rfl⟩ : syracuseStep 2086501 = 391219) (by norm_num)
theorem B2971237 : Blo 1853628 2971237 := bbase (se 4 (by rfl) ⟨278553, by rfl⟩ : syracuseStep 2971237 = 557107) (by norm_num)
theorem B2782829 : Blo 1853628 2782829 := bbase (se 3 (by rfl) ⟨521780, by rfl⟩ : syracuseStep 2782829 = 1043561) (by norm_num)
theorem B2782853 : Blo 1853628 2782853 := bbase (se 4 (by rfl) ⟨260892, by rfl⟩ : syracuseStep 2782853 = 521785) (by norm_num)
theorem B2086537 : Blo 1853628 2086537 := bbase (se 2 (by rfl) ⟨782451, by rfl⟩ : syracuseStep 2086537 = 1564903) (by norm_num)
theorem B6256277 : Blo 1853628 6256277 := bbase (se 6 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 6256277 = 293263) (by norm_num)
theorem B2782877 : Blo 1853628 2782877 := bbase (se 3 (by rfl) ⟨521789, by rfl⟩ : syracuseStep 2782877 = 1043579) (by norm_num)
theorem B2086573 : Blo 1853628 2086573 := bbase (se 3 (by rfl) ⟨391232, by rfl⟩ : syracuseStep 2086573 = 782465) (by norm_num)
theorem B2782901 : Blo 1853628 2782901 := bbase (se 5 (by rfl) ⟨130448, by rfl⟩ : syracuseStep 2782901 = 260897) (by norm_num)
theorem B3520189 : Blo 1853628 3520189 := bbase (se 3 (by rfl) ⟨660035, by rfl⟩ : syracuseStep 3520189 = 1320071) (by norm_num)
theorem B2782925 : Blo 1853628 2782925 := bbase (se 3 (by rfl) ⟨521798, by rfl⟩ : syracuseStep 2782925 = 1043597) (by norm_num)
theorem B2086609 : Blo 1853628 2086609 := bbase (se 2 (by rfl) ⟨782478, by rfl⟩ : syracuseStep 2086609 = 1564957) (by norm_num)
theorem B7919333 : Blo 1853628 7919333 := bbase (se 4 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 7919333 = 1484875) (by norm_num)
theorem B2782949 : Blo 1853628 2782949 := bbase (se 4 (by rfl) ⟨260901, by rfl⟩ : syracuseStep 2782949 = 521803) (by norm_num)
theorem B9393893 : Blo 1853628 9393893 := bbase (se 4 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 9393893 = 1761355) (by norm_num)
theorem B2086645 : Blo 1853628 2086645 := bbase (se 5 (by rfl) ⟨97811, by rfl⟩ : syracuseStep 2086645 = 195623) (by norm_num)
theorem B2782973 : Blo 1853628 2782973 := bbase (se 3 (by rfl) ⟨521807, by rfl⟩ : syracuseStep 2782973 = 1043615) (by norm_num)
theorem B2258705 : Blo 1853628 2258705 := bbase (se 2 (by rfl) ⟨847014, by rfl⟩ : syracuseStep 2258705 = 1694029) (by norm_num)
theorem B2782997 : Blo 1853628 2782997 := bbase (se 6 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 2782997 = 130453) (by norm_num)
theorem B2086681 : Blo 1853628 2086681 := bbase (se 2 (by rfl) ⟨782505, by rfl⟩ : syracuseStep 2086681 = 1565011) (by norm_num)
theorem B5011237 : Blo 1853628 5011237 := bbase (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) (by norm_num)
theorem B2783021 : Blo 1853628 2783021 := bbase (se 3 (by rfl) ⟨521816, by rfl⟩ : syracuseStep 2783021 = 1043633) (by norm_num)
theorem B2086717 : Blo 1853628 2086717 := bbase (se 3 (by rfl) ⟨391259, by rfl⟩ : syracuseStep 2086717 = 782519) (by norm_num)
theorem B2783045 : Blo 1853628 2783045 := bbase (se 4 (by rfl) ⟨260910, by rfl⟩ : syracuseStep 2783045 = 521821) (by norm_num)
theorem B3012437 : Blo 1853628 3012437 := bbase (se 9 (by rfl) ⟨8825, by rfl⟩ : syracuseStep 3012437 = 17651) (by norm_num)
theorem B2783069 : Blo 1853628 2783069 := bbase (se 3 (by rfl) ⟨521825, by rfl⟩ : syracuseStep 2783069 = 1043651) (by norm_num)
theorem B2086753 : Blo 1853628 2086753 := bbase (se 2 (by rfl) ⟨782532, by rfl⟩ : syracuseStep 2086753 = 1565065) (by norm_num)
theorem B2971493 : Blo 1853628 2971493 := bbase (se 4 (by rfl) ⟨278577, by rfl⟩ : syracuseStep 2971493 = 557155) (by norm_num)
theorem B2783093 : Blo 1853628 2783093 := bbase (se 5 (by rfl) ⟨130457, by rfl⟩ : syracuseStep 2783093 = 260915) (by norm_num)
theorem B2086789 : Blo 1853628 2086789 := bbase (se 4 (by rfl) ⟨195636, by rfl⟩ : syracuseStep 2086789 = 391273) (by norm_num)
theorem B2783117 : Blo 1853628 2783117 := bbase (se 3 (by rfl) ⟨521834, by rfl⟩ : syracuseStep 2783117 = 1043669) (by norm_num)
theorem B1980325 : Blo 1853628 1980325 := bbase (se 4 (by rfl) ⟨185655, by rfl⟩ : syracuseStep 1980325 = 371311) (by norm_num)
theorem B2783141 : Blo 1853628 2783141 := bbase (se 4 (by rfl) ⟨260919, by rfl⟩ : syracuseStep 2783141 = 521839) (by norm_num)
theorem B2086825 : Blo 1853628 2086825 := bbase (se 2 (by rfl) ⟨782559, by rfl⟩ : syracuseStep 2086825 = 1565119) (by norm_num)
theorem B2783165 : Blo 1853628 2783165 := bbase (se 3 (by rfl) ⟨521843, by rfl⟩ : syracuseStep 2783165 = 1043687) (by norm_num)
theorem B2086861 : Blo 1853628 2086861 := bbase (se 3 (by rfl) ⟨391286, by rfl⟩ : syracuseStep 2086861 = 782573) (by norm_num)
theorem B22566869 : Blo 1853628 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2783189 : Blo 1853628 2783189 := bbase (se 7 (by rfl) ⟨32615, by rfl⟩ : syracuseStep 2783189 = 65231) (by norm_num)
theorem B3962837 : Blo 1853628 3962837 := bbase (se 7 (by rfl) ⟨46439, by rfl⟩ : syracuseStep 3962837 = 92879) (by norm_num)
theorem B3520493 : Blo 1853628 3520493 := bbase (se 3 (by rfl) ⟨660092, by rfl⟩ : syracuseStep 3520493 = 1320185) (by norm_num)
theorem B1980397 : Blo 1853628 1980397 := bbase (se 3 (by rfl) ⟨371324, by rfl⟩ : syracuseStep 1980397 = 742649) (by norm_num)
theorem B2783213 : Blo 1853628 2783213 := bbase (se 3 (by rfl) ⟨521852, by rfl⟩ : syracuseStep 2783213 = 1043705) (by norm_num)
theorem B2086897 : Blo 1853628 2086897 := bbase (se 2 (by rfl) ⟨782586, by rfl⟩ : syracuseStep 2086897 = 1565173) (by norm_num)
theorem B2783237 : Blo 1853628 2783237 := bbase (se 4 (by rfl) ⟨260928, by rfl⟩ : syracuseStep 2783237 = 521857) (by norm_num)
theorem B2086933 : Blo 1853628 2086933 := bbase (se 6 (by rfl) ⟨48912, by rfl⟩ : syracuseStep 2086933 = 97825) (by norm_num)
theorem B2783261 : Blo 1853628 2783261 := bbase (se 3 (by rfl) ⟨521861, by rfl⟩ : syracuseStep 2783261 = 1043723) (by norm_num)
theorem B2971685 : Blo 1853628 2971685 := bbase (se 4 (by rfl) ⟨278595, by rfl⟩ : syracuseStep 2971685 = 557191) (by norm_num)
theorem B4454453 : Blo 1853628 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B2783285 : Blo 1853628 2783285 := bbase (se 5 (by rfl) ⟨130466, by rfl⟩ : syracuseStep 2783285 = 260933) (by norm_num)
theorem B2086969 : Blo 1853628 2086969 := bbase (se 2 (by rfl) ⟨782613, by rfl⟩ : syracuseStep 2086969 = 1565227) (by norm_num)
theorem B6256709 : Blo 1853628 6256709 := bbase (se 4 (by rfl) ⟨586566, by rfl⟩ : syracuseStep 6256709 = 1173133) (by norm_num)
theorem B2783309 : Blo 1853628 2783309 := bbase (se 3 (by rfl) ⟨521870, by rfl⟩ : syracuseStep 2783309 = 1043741) (by norm_num)
theorem B2087005 : Blo 1853628 2087005 := bbase (se 3 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 2087005 = 782627) (by norm_num)
theorem B3962981 : Blo 1853628 3962981 := bbase (se 4 (by rfl) ⟨371529, by rfl⟩ : syracuseStep 3962981 = 743059) (by norm_num)
theorem B2783333 : Blo 1853628 2783333 := bbase (se 4 (by rfl) ⟨260937, by rfl⟩ : syracuseStep 2783333 = 521875) (by norm_num)
theorem B4692077 : Blo 1853628 4692077 := bbase (se 3 (by rfl) ⟨879764, by rfl⟩ : syracuseStep 4692077 = 1759529) (by norm_num)
theorem B2783357 : Blo 1853628 2783357 := bbase (se 3 (by rfl) ⟨521879, by rfl⟩ : syracuseStep 2783357 = 1043759) (by norm_num)
theorem B2087041 : Blo 1853628 2087041 := bbase (se 2 (by rfl) ⟨782640, by rfl⟩ : syracuseStep 2087041 = 1565281) (by norm_num)
theorem B3340421 : Blo 1853628 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B9386117 : Blo 1853628 9386117 := bbase (se 4 (by rfl) ⟨879948, by rfl⟩ : syracuseStep 9386117 = 1759897) (by norm_num)
theorem B2783381 : Blo 1853628 2783381 := bbase (se 6 (by rfl) ⟨65235, by rfl⟩ : syracuseStep 2783381 = 130471) (by norm_num)
theorem B2087077 : Blo 1853628 2087077 := bbase (se 4 (by rfl) ⟨195663, by rfl⟩ : syracuseStep 2087077 = 391327) (by norm_num)
theorem B2783405 : Blo 1853628 2783405 := bbase (se 3 (by rfl) ⟨521888, by rfl⟩ : syracuseStep 2783405 = 1043777) (by norm_num)
theorem B2783429 : Blo 1853628 2783429 := bbase (se 4 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 2783429 = 521893) (by norm_num)
theorem B2087113 : Blo 1853628 2087113 := bbase (se 2 (by rfl) ⟨782667, by rfl⟩ : syracuseStep 2087113 = 1565335) (by norm_num)
theorem B5011669 : Blo 1853628 5011669 := bbase (se 7 (by rfl) ⟨58730, by rfl⟩ : syracuseStep 5011669 = 117461) (by norm_num)
theorem B2087149 : Blo 1853628 2087149 := bbase (se 3 (by rfl) ⟨391340, by rfl⟩ : syracuseStep 2087149 = 782681) (by norm_num)
theorem B9517301 : Blo 1853628 9517301 := bbase (se 5 (by rfl) ⟨446123, by rfl⟩ : syracuseStep 9517301 = 892247) (by norm_num)
theorem B2087185 : Blo 1853628 2087185 := bbase (se 2 (by rfl) ⟨782694, by rfl⟩ : syracuseStep 2087185 = 1565389) (by norm_num)
theorem B4692269 : Blo 1853628 4692269 := bbase (se 3 (by rfl) ⟨879800, by rfl⟩ : syracuseStep 4692269 = 1759601) (by norm_num)
theorem B2087221 : Blo 1853628 2087221 := bbase (se 5 (by rfl) ⟨97838, by rfl⟩ : syracuseStep 2087221 = 195677) (by norm_num)
theorem B6682949 : Blo 1853628 6682949 := bbase (se 4 (by rfl) ⟨626526, by rfl⟩ : syracuseStep 6682949 = 1253053) (by norm_num)
theorem B2087257 : Blo 1853628 2087257 := bbase (se 2 (by rfl) ⟨782721, by rfl⟩ : syracuseStep 2087257 = 1565443) (by norm_num)
theorem B1980769 : Blo 1853628 1980769 := bbase (se 2 (by rfl) ⟨742788, by rfl⟩ : syracuseStep 1980769 = 1485577) (by norm_num)
theorem B2087293 : Blo 1853628 2087293 := bbase (se 3 (by rfl) ⟨391367, by rfl⟩ : syracuseStep 2087293 = 782735) (by norm_num)
theorem B2087329 : Blo 1853628 2087329 := bbase (se 2 (by rfl) ⟨782748, by rfl⟩ : syracuseStep 2087329 = 1565497) (by norm_num)
theorem B2087365 : Blo 1853628 2087365 := bbase (se 4 (by rfl) ⟨195690, by rfl⟩ : syracuseStep 2087365 = 391381) (by norm_num)
theorem B5642693 : Blo 1853628 5642693 := bbase (se 4 (by rfl) ⟨529002, by rfl⟩ : syracuseStep 5642693 = 1058005) (by norm_num)
theorem B6683093 : Blo 1853628 6683093 := bbase (se 7 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 6683093 = 156635) (by norm_num)
theorem B4454885 : Blo 1853628 4454885 := bbase (se 4 (by rfl) ⟨417645, by rfl⟩ : syracuseStep 4454885 = 835291) (by norm_num)
theorem B9157093 : Blo 1853628 9157093 := bbase (se 4 (by rfl) ⟨858477, by rfl⟩ : syracuseStep 9157093 = 1716955) (by norm_num)
theorem B2087401 : Blo 1853628 2087401 := bbase (se 2 (by rfl) ⟨782775, by rfl⟩ : syracuseStep 2087401 = 1565551) (by norm_num)
theorem B6257141 : Blo 1853628 6257141 := bbase (se 5 (by rfl) ⟨293303, by rfl⟩ : syracuseStep 6257141 = 586607) (by norm_num)
theorem B5011973 : Blo 1853628 5011973 := bbase (se 4 (by rfl) ⟨469872, by rfl⟩ : syracuseStep 5011973 = 939745) (by norm_num)
theorem B2087437 : Blo 1853628 2087437 := bbase (se 3 (by rfl) ⟨391394, by rfl⟩ : syracuseStep 2087437 = 782789) (by norm_num)
theorem B2087473 : Blo 1853628 2087473 := bbase (se 2 (by rfl) ⟨782802, by rfl⟩ : syracuseStep 2087473 = 1565605) (by norm_num)
theorem B2087509 : Blo 1853628 2087509 := bbase (se 8 (by rfl) ⟨12231, by rfl⟩ : syracuseStep 2087509 = 24463) (by norm_num)
theorem B2087545 : Blo 1853628 2087545 := bbase (se 2 (by rfl) ⟨782829, by rfl⟩ : syracuseStep 2087545 = 1565659) (by norm_num)
theorem B4692613 : Blo 1853628 4692613 := bbase (se 4 (by rfl) ⟨439932, by rfl⟩ : syracuseStep 4692613 = 879865) (by norm_num)
theorem B2087581 : Blo 1853628 2087581 := bbase (se 3 (by rfl) ⟨391421, by rfl⟩ : syracuseStep 2087581 = 782843) (by norm_num)
theorem B1981145 : Blo 1853628 1981145 := bbase (se 2 (by rfl) ⟨742929, by rfl⟩ : syracuseStep 1981145 = 1485859) (by norm_num)
theorem B3521245 : Blo 1853628 3521245 := bbase (se 3 (by rfl) ⟨660233, by rfl⟩ : syracuseStep 3521245 = 1320467) (by norm_num)
theorem B4692725 : Blo 1853628 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B7518997 : Blo 1853628 7518997 := bbase (se 6 (by rfl) ⟨176226, by rfl⟩ : syracuseStep 7518997 = 352453) (by norm_num)
theorem B1981217 : Blo 1853628 1981217 := bbase (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) (by norm_num)
theorem B5282597 : Blo 1853628 5282597 := bbase (se 4 (by rfl) ⟨495243, by rfl⟩ : syracuseStep 5282597 = 990487) (by norm_num)
theorem B3128125 : Blo 1853628 3128125 := bbase (se 3 (by rfl) ⟨586523, by rfl⟩ : syracuseStep 3128125 = 1173047) (by norm_num)
theorem B3521389 : Blo 1853628 3521389 := bbase (se 3 (by rfl) ⟨660260, by rfl⟩ : syracuseStep 3521389 = 1320521) (by norm_num)
theorem B3128213 : Blo 1853628 3128213 := bbase (se 6 (by rfl) ⟨73317, by rfl⟩ : syracuseStep 3128213 = 146635) (by norm_num)
theorem B3759005 : Blo 1853628 3759005 := bbase (se 3 (by rfl) ⟨704813, by rfl⟩ : syracuseStep 3759005 = 1409627) (by norm_num)
theorem B6257573 : Blo 1853628 6257573 := bbase (se 4 (by rfl) ⟨586647, by rfl⟩ : syracuseStep 6257573 = 1173295) (by norm_num)
theorem B4692917 : Blo 1853628 4692917 := bbase (se 5 (by rfl) ⟨219980, by rfl⟩ : syracuseStep 4692917 = 439961) (by norm_num)
theorem B1981405 : Blo 1853628 1981405 := bbase (se 3 (by rfl) ⟨371513, by rfl⟩ : syracuseStep 1981405 = 743027) (by norm_num)
theorem B3521549 : Blo 1853628 3521549 := bbase (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) (by norm_num)
theorem B3128341 : Blo 1853628 3128341 := bbase (se 6 (by rfl) ⟨73320, by rfl⟩ : syracuseStep 3128341 = 146641) (by norm_num)
theorem B2858021 : Blo 1853628 2858021 := bbase (se 4 (by rfl) ⟨267939, by rfl⟩ : syracuseStep 2858021 = 535879) (by norm_num)
theorem B11877461 : Blo 1853628 11877461 := bbase (se 8 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 11877461 = 139189) (by norm_num)
theorem B3128429 : Blo 1853628 3128429 := bbase (se 3 (by rfl) ⟨586580, by rfl⟩ : syracuseStep 3128429 = 1173161) (by norm_num)
theorem B3521693 : Blo 1853628 3521693 := bbase (se 3 (by rfl) ⟨660317, by rfl⟩ : syracuseStep 3521693 = 1320635) (by norm_num)
theorem B5938373 : Blo 1853628 5938373 := bbase (se 4 (by rfl) ⟨556722, by rfl⟩ : syracuseStep 5938373 = 1113445) (by norm_num)
theorem B3128557 : Blo 1853628 3128557 := bbase (se 3 (by rfl) ⟨586604, by rfl⟩ : syracuseStep 3128557 = 1173209) (by norm_num)
theorem B2227457 : Blo 1853628 2227457 := bbase (se 2 (by rfl) ⟨835296, by rfl⟩ : syracuseStep 2227457 = 1670593) (by norm_num)
theorem B4693261 : Blo 1853628 4693261 := bbase (se 3 (by rfl) ⟨879986, by rfl⟩ : syracuseStep 4693261 = 1759973) (by norm_num)
theorem B2227505 : Blo 1853628 2227505 := bbase (se 2 (by rfl) ⟨835314, by rfl⟩ : syracuseStep 2227505 = 1670629) (by norm_num)
theorem B3128645 : Blo 1853628 3128645 := bbase (se 4 (by rfl) ⟨293310, by rfl⟩ : syracuseStep 3128645 = 586621) (by norm_num)
theorem B6258005 : Blo 1853628 6258005 := bbase (se 11 (by rfl) ⟨4583, by rfl⟩ : syracuseStep 6258005 = 9167) (by norm_num)
theorem B57105749 : Blo 1853628 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B13557077 : Blo 1853628 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B4693373 : Blo 1853628 4693373 := bbase (se 3 (by rfl) ⟨880007, by rfl⟩ : syracuseStep 4693373 = 1760015) (by norm_num)
theorem B2227601 : Blo 1853628 2227601 := bbase (se 2 (by rfl) ⟨835350, by rfl⟩ : syracuseStep 2227601 = 1670701) (by norm_num)
theorem B9387413 : Blo 1853628 9387413 := bbase (se 6 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 9387413 = 440035) (by norm_num)
theorem B3521981 : Blo 1853628 3521981 := bbase (se 3 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 3521981 = 1320743) (by norm_num)
theorem B3128773 : Blo 1853628 3128773 := bbase (se 4 (by rfl) ⟨293322, by rfl⟩ : syracuseStep 3128773 = 586645) (by norm_num)
theorem B5283269 : Blo 1853628 5283269 := bbase (se 4 (by rfl) ⟨495306, by rfl⟩ : syracuseStep 5283269 = 990613) (by norm_num)
theorem B10558997 : Blo 1853628 10558997 := bbase (se 6 (by rfl) ⟨247476, by rfl⟩ : syracuseStep 10558997 = 494953) (by norm_num)
theorem B19037717 : Blo 1853628 19037717 := bbase (se 6 (by rfl) ⟨446196, by rfl⟩ : syracuseStep 19037717 = 892393) (by norm_num)
theorem B3128861 : Blo 1853628 3128861 := bbase (se 3 (by rfl) ⟨586661, by rfl⟩ : syracuseStep 3128861 = 1173323) (by norm_num)
theorem B2227765 : Blo 1853628 2227765 := bbase (se 5 (by rfl) ⟨104426, by rfl⟩ : syracuseStep 2227765 = 208853) (by norm_num)
theorem B4693565 : Blo 1853628 4693565 := bbase (se 3 (by rfl) ⟨880043, by rfl⟩ : syracuseStep 4693565 = 1760087) (by norm_num)
theorem B7044677 : Blo 1853628 7044677 := bbase (se 4 (by rfl) ⟨660438, by rfl⟩ : syracuseStep 7044677 = 1320877) (by norm_num)
theorem B3522133 : Blo 1853628 3522133 := bbase (se 8 (by rfl) ⟨20637, by rfl⟩ : syracuseStep 3522133 = 41275) (by norm_num)
theorem B3128989 : Blo 1853628 3128989 := bbase (se 3 (by rfl) ⟨586685, by rfl⟩ : syracuseStep 3128989 = 1173371) (by norm_num)
theorem B2506397 : Blo 1853628 2506397 := bbase (se 3 (by rfl) ⟨469949, by rfl⟩ : syracuseStep 2506397 = 939899) (by norm_num)
theorem B3129077 : Blo 1853628 3129077 := bbase (se 5 (by rfl) ⟨146675, by rfl⟩ : syracuseStep 3129077 = 293351) (by norm_num)
theorem B6258437 : Blo 1853628 6258437 := bbase (se 4 (by rfl) ⟨586728, by rfl⟩ : syracuseStep 6258437 = 1173457) (by norm_num)
theorem B2227981 : Blo 1853628 2227981 := bbase (se 3 (by rfl) ⟨417746, by rfl⟩ : syracuseStep 2227981 = 835493) (by norm_num)
theorem B11427637 : Blo 1853628 11427637 := bbase (se 5 (by rfl) ⟨535670, by rfl⟩ : syracuseStep 11427637 = 1071341) (by norm_num)
theorem B8912693 : Blo 1853628 8912693 := bbase (se 5 (by rfl) ⟨417782, by rfl⟩ : syracuseStep 8912693 = 835565) (by norm_num)
theorem B3342181 : Blo 1853628 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B7044965 : Blo 1853628 7044965 := bbase (se 4 (by rfl) ⟨660465, by rfl⟩ : syracuseStep 7044965 = 1320931) (by norm_num)
theorem B3129205 : Blo 1853628 3129205 := bbase (se 5 (by rfl) ⟨146681, by rfl⟩ : syracuseStep 3129205 = 293363) (by norm_num)
theorem B5283701 : Blo 1853628 5283701 := bbase (se 5 (by rfl) ⟨247673, by rfl⟩ : syracuseStep 5283701 = 495347) (by norm_num)
theorem B3522437 : Blo 1853628 3522437 := bbase (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) (by norm_num)
theorem B4693909 : Blo 1853628 4693909 := bbase (se 6 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 4693909 = 220027) (by norm_num)
theorem B17833877 : Blo 1853628 17833877 := bbase (se 6 (by rfl) ⟨417981, by rfl⟩ : syracuseStep 17833877 = 835963) (by norm_num)
theorem B2228149 : Blo 1853628 2228149 := bbase (se 5 (by rfl) ⟨104444, by rfl⟩ : syracuseStep 2228149 = 208889) (by norm_num)
theorem B3129293 : Blo 1853628 3129293 := bbase (se 3 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 3129293 = 1173485) (by norm_num)
theorem B3342317 : Blo 1853628 3342317 := bbase (se 3 (by rfl) ⟨626684, by rfl⟩ : syracuseStep 3342317 = 1253369) (by norm_num)
theorem B3129347 : Blo 1853628 3129347 := bstep (se 1 (by rfl) ⟨2347010, by rfl⟩ : syracuseStep 3129347 = 4694021) B4694021
theorem B4694051 : Blo 1853628 4694051 := bstep (se 1 (by rfl) ⟨3520538, by rfl⟩ : syracuseStep 4694051 = 7041077) B7041077
theorem B6684707 : Blo 1853628 6684707 := bstep (se 1 (by rfl) ⟨5013530, by rfl⟩ : syracuseStep 6684707 = 10027061) B10027061
theorem B4456529 : Blo 1853628 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B3129475 : Blo 1853628 3129475 := bstep (se 1 (by rfl) ⟨2347106, by rfl⟩ : syracuseStep 3129475 = 4694213) B4694213
theorem B3129617 : Blo 1853628 3129617 := bstep (se 2 (by rfl) ⟨1173606, by rfl⟩ : syracuseStep 3129617 = 2347213) B2347213
theorem B4456739 : Blo 1853628 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B7922033 : Blo 1853628 7922033 := bstep (se 2 (by rfl) ⟨2970762, by rfl⟩ : syracuseStep 7922033 = 5941525) B5941525
theorem B6259085 : Blo 1853628 6259085 := bstep (se 3 (by rfl) ⟨1173578, by rfl⟩ : syracuseStep 6259085 = 2347157) B2347157
theorem B3129745 : Blo 1853628 3129745 := bstep (se 2 (by rfl) ⟨1173654, by rfl⟩ : syracuseStep 3129745 = 2347309) B2347309
theorem B3129779 : Blo 1853628 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B6259139 : Blo 1853628 6259139 := bstep (se 1 (by rfl) ⟨4694354, by rfl⟩ : syracuseStep 6259139 = 9388709) B9388709
theorem B2859475 : Blo 1853628 2859475 := bstep (se 1 (by rfl) ⟨2144606, by rfl⟩ : syracuseStep 2859475 = 4289213) B4289213
theorem B10568177 : Blo 1853628 10568177 := bstep (se 2 (by rfl) ⟨3963066, by rfl⟩ : syracuseStep 10568177 = 7926133) B7926133
theorem B3129907 : Blo 1853628 3129907 := bstep (se 1 (by rfl) ⟨2347430, by rfl⟩ : syracuseStep 3129907 = 4694861) B4694861
theorem B3170915 : Blo 1853628 3170915 := bstep (se 1 (by rfl) ⟨2378186, by rfl⟩ : syracuseStep 3170915 = 4756373) B4756373
theorem B5939885 : Blo 1853628 5939885 := bstep (se 3 (by rfl) ⟨1113728, by rfl⟩ : syracuseStep 5939885 = 2227457) B2227457
theorem B3130049 : Blo 1853628 3130049 := bstep (se 2 (by rfl) ⟨1173768, by rfl⟩ : syracuseStep 3130049 = 2347537) B2347537
theorem B21127877 : Blo 1853628 21127877 := bstep (se 4 (by rfl) ⟨1980738, by rfl⟩ : syracuseStep 21127877 = 3961477) B3961477
theorem B6259409 : Blo 1853628 6259409 := bstep (se 2 (by rfl) ⟨2347278, by rfl⟩ : syracuseStep 6259409 = 4694557) B4694557
theorem B2228995 : Blo 1853628 2228995 := bstep (se 1 (by rfl) ⟨1671746, by rfl⟩ : syracuseStep 2228995 = 3343493) B3343493
theorem B25387789 : Blo 1853628 25387789 := bstep (se 3 (by rfl) ⟨4760210, by rfl⟩ : syracuseStep 25387789 = 9520421) B9520421
theorem B5940013 : Blo 1853628 5940013 := bstep (se 3 (by rfl) ⟨1113752, by rfl⟩ : syracuseStep 5940013 = 2227505) B2227505
theorem B3130177 : Blo 1853628 3130177 := bstep (se 2 (by rfl) ⟨1173816, by rfl⟩ : syracuseStep 3130177 = 2347633) B2347633
theorem B3130211 : Blo 1853628 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B7521137 : Blo 1853628 7521137 := bstep (se 2 (by rfl) ⟨2820426, by rfl⟩ : syracuseStep 7521137 = 5640853) B5640853
theorem B4694993 : Blo 1853628 4694993 := bstep (se 2 (by rfl) ⟨1760622, by rfl⟩ : syracuseStep 4694993 = 3521245) B3521245
theorem B3130339 : Blo 1853628 3130339 := bstep (se 1 (by rfl) ⟨2347754, by rfl⟩ : syracuseStep 3130339 = 4695509) B4695509
theorem B4695043 : Blo 1853628 4695043 := bstep (se 1 (by rfl) ⟨3521282, by rfl⟩ : syracuseStep 4695043 = 7042565) B7042565
theorem B5940269 : Blo 1853628 5940269 := bstep (se 3 (by rfl) ⟨1113800, by rfl⟩ : syracuseStep 5940269 = 2227601) B2227601
theorem B4170833 : Blo 1853628 4170833 := bstep (se 2 (by rfl) ⟨1564062, by rfl⟩ : syracuseStep 4170833 = 3128125) B3128125
theorem B4170851 : Blo 1853628 4170851 := bstep (se 1 (by rfl) ⟨3128138, by rfl⟩ : syracuseStep 4170851 = 6256277) B6256277
theorem B3130481 : Blo 1853628 3130481 := bstep (se 2 (by rfl) ⟨1173930, by rfl⟩ : syracuseStep 3130481 = 2347861) B2347861
theorem B4695185 : Blo 1853628 4695185 := bstep (se 2 (by rfl) ⟨1760694, by rfl⟩ : syracuseStep 4695185 = 3521389) B3521389
theorem B6259949 : Blo 1853628 6259949 := bstep (se 3 (by rfl) ⟨1173740, by rfl⟩ : syracuseStep 6259949 = 2347481) B2347481
theorem B3130609 : Blo 1853628 3130609 := bstep (se 2 (by rfl) ⟨1173978, by rfl⟩ : syracuseStep 3130609 = 2347957) B2347957
theorem B21136625 : Blo 1853628 21136625 := bstep (se 2 (by rfl) ⟨7926234, by rfl⟩ : syracuseStep 21136625 = 15852469) B15852469
theorem B11879693 : Blo 1853628 11879693 := bstep (se 3 (by rfl) ⟨2227442, by rfl⟩ : syracuseStep 11879693 = 4454885) B4454885
theorem B3130643 : Blo 1853628 3130643 := bstep (se 1 (by rfl) ⟨2347982, by rfl⟩ : syracuseStep 3130643 = 4695965) B4695965
theorem B6260003 : Blo 1853628 6260003 := bstep (se 1 (by rfl) ⟨4695002, by rfl⟩ : syracuseStep 6260003 = 9390005) B9390005
theorem B10028357 : Blo 1853628 10028357 := bstep (se 4 (by rfl) ⟨940158, by rfl⟩ : syracuseStep 10028357 = 1880317) B1880317
theorem B4171121 : Blo 1853628 4171121 := bstep (se 2 (by rfl) ⟨1564170, by rfl⟩ : syracuseStep 4171121 = 3128341) B3128341
theorem B4171139 : Blo 1853628 4171139 := bstep (se 1 (by rfl) ⟨3128354, by rfl⟩ : syracuseStep 4171139 = 6256709) B6256709
theorem B3130771 : Blo 1853628 3130771 := bstep (se 1 (by rfl) ⟨2348078, by rfl⟩ : syracuseStep 3130771 = 4696157) B4696157
theorem B2639299 : Blo 1853628 2639299 := bstep (se 1 (by rfl) ⟨1979474, by rfl⟩ : syracuseStep 2639299 = 3958949) B3958949
theorem B4228561 : Blo 1853628 4228561 := bstep (se 2 (by rfl) ⟨1585710, by rfl⟩ : syracuseStep 4228561 = 3171421) B3171421
theorem B11879921 : Blo 1853628 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B3130913 : Blo 1853628 3130913 := bstep (se 2 (by rfl) ⟨1174092, by rfl⟩ : syracuseStep 3130913 = 2348185) B2348185
theorem B6260273 : Blo 1853628 6260273 := bstep (se 2 (by rfl) ⟨2347602, by rfl⟩ : syracuseStep 6260273 = 4695205) B4695205
theorem B121996853 : Blo 1853628 121996853 := bstep (se 5 (by rfl) ⟨5718602, by rfl⟩ : syracuseStep 121996853 = 11437205) B11437205
theorem B9389681 : Blo 1853628 9389681 := bstep (se 2 (by rfl) ⟨3521130, by rfl⟩ : syracuseStep 9389681 = 7042261) B7042261
theorem B3761795 : Blo 1853628 3761795 := bstep (se 1 (by rfl) ⟨2821346, by rfl⟩ : syracuseStep 3761795 = 5642693) B5642693
theorem B4171409 : Blo 1853628 4171409 := bstep (se 2 (by rfl) ⟨1564278, by rfl⟩ : syracuseStep 4171409 = 3128557) B3128557
theorem B3131041 : Blo 1853628 3131041 := bstep (se 2 (by rfl) ⟨1174140, by rfl⟩ : syracuseStep 3131041 = 2348281) B2348281
theorem B4171427 : Blo 1853628 4171427 := bstep (se 1 (by rfl) ⟨3128570, by rfl⟩ : syracuseStep 4171427 = 6257141) B6257141
theorem B3131075 : Blo 1853628 3131075 := bstep (se 1 (by rfl) ⟨2348306, by rfl⟩ : syracuseStep 3131075 = 4696613) B4696613
theorem B6342403 : Blo 1853628 6342403 := bstep (se 1 (by rfl) ⟨4756802, by rfl⟩ : syracuseStep 6342403 = 9513605) B9513605
theorem B3131203 : Blo 1853628 3131203 := bstep (se 1 (by rfl) ⟨2348402, by rfl⟩ : syracuseStep 3131203 = 4696805) B4696805
theorem B4171697 : Blo 1853628 4171697 := bstep (se 2 (by rfl) ⟨1564386, by rfl⟩ : syracuseStep 4171697 = 3128773) B3128773
theorem B4171715 : Blo 1853628 4171715 := bstep (se 1 (by rfl) ⟨3128786, by rfl⟩ : syracuseStep 4171715 = 6257573) B6257573
theorem B9512909 : Blo 1853628 9512909 := bstep (se 3 (by rfl) ⟨1783670, by rfl⟩ : syracuseStep 9512909 = 3567341) B3567341
theorem B3131345 : Blo 1853628 3131345 := bstep (se 2 (by rfl) ⟨1174254, by rfl⟩ : syracuseStep 3131345 = 2348509) B2348509
theorem B6023213 : Blo 1853628 6023213 := bstep (se 3 (by rfl) ⟨1129352, by rfl⟩ : syracuseStep 6023213 = 2258705) B2258705
theorem B6260813 : Blo 1853628 6260813 := bstep (se 3 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 6260813 = 2347805) B2347805
theorem B14076017 : Blo 1853628 14076017 := bstep (se 2 (by rfl) ⟨5278506, by rfl⟩ : syracuseStep 14076017 = 10557013) B10557013
theorem B4696177 : Blo 1853628 4696177 := bstep (se 2 (by rfl) ⟨1761066, by rfl⟩ : syracuseStep 4696177 = 3522133) B3522133
theorem B3958915 : Blo 1853628 3958915 := bstep (se 1 (by rfl) ⟨2969186, by rfl⟩ : syracuseStep 3958915 = 5938373) B5938373
theorem B6260867 : Blo 1853628 6260867 := bstep (se 1 (by rfl) ⟨4695650, by rfl⟩ : syracuseStep 6260867 = 9391301) B9391301
theorem B1853635 : Blo 1853628 1853635 := bstep (se 1 (by rfl) ⟨1390226, by rfl⟩ : syracuseStep 1853635 = 2780453) B2780453
theorem B4171985 : Blo 1853628 4171985 := bstep (se 2 (by rfl) ⟨1564494, by rfl⟩ : syracuseStep 4171985 = 3128989) B3128989
theorem B1853651 : Blo 1853628 1853651 := bstep (se 1 (by rfl) ⟨1390238, by rfl⟩ : syracuseStep 1853651 = 2780477) B2780477
theorem B1853667 : Blo 1853628 1853667 := bstep (se 1 (by rfl) ⟨1390250, by rfl⟩ : syracuseStep 1853667 = 2780501) B2780501
theorem B4172003 : Blo 1853628 4172003 := bstep (se 1 (by rfl) ⟨3129002, by rfl⟩ : syracuseStep 4172003 = 6258005) B6258005
theorem B38070499 : Blo 1853628 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B9038051 : Blo 1853628 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B1853683 : Blo 1853628 1853683 := bstep (se 1 (by rfl) ⟨1390262, by rfl⟩ : syracuseStep 1853683 = 2780525) B2780525
theorem B1853699 : Blo 1853628 1853699 := bstep (se 1 (by rfl) ⟨1390274, by rfl⟩ : syracuseStep 1853699 = 2780549) B2780549
theorem B1853715 : Blo 1853628 1853715 := bstep (se 1 (by rfl) ⟨1390286, by rfl⟩ : syracuseStep 1853715 = 2780573) B2780573
theorem B1853731 : Blo 1853628 1853731 := bstep (se 1 (by rfl) ⟨1390298, by rfl⟩ : syracuseStep 1853731 = 2780597) B2780597
theorem B1853747 : Blo 1853628 1853747 := bstep (se 1 (by rfl) ⟨1390310, by rfl⟩ : syracuseStep 1853747 = 2780621) B2780621
theorem B1853763 : Blo 1853628 1853763 := bstep (se 1 (by rfl) ⟨1390322, by rfl⟩ : syracuseStep 1853763 = 2780645) B2780645
theorem B1853779 : Blo 1853628 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B1853795 : Blo 1853628 1853795 := bstep (se 1 (by rfl) ⟨1390346, by rfl⟩ : syracuseStep 1853795 = 2780693) B2780693
theorem B7039331 : Blo 1853628 7039331 := bstep (se 1 (by rfl) ⟨5279498, by rfl⟩ : syracuseStep 7039331 = 10558997) B10558997
theorem B12691811 : Blo 1853628 12691811 := bstep (se 1 (by rfl) ⟨9518858, by rfl⟩ : syracuseStep 12691811 = 19037717) B19037717
theorem B7039345 : Blo 1853628 7039345 := bstep (se 2 (by rfl) ⟨2639754, by rfl⟩ : syracuseStep 7039345 = 5279509) B5279509
theorem B31680881 : Blo 1853628 31680881 := bstep (se 2 (by rfl) ⟨11880330, by rfl⟩ : syracuseStep 31680881 = 23760661) B23760661
theorem B1853811 : Blo 1853628 1853811 := bstep (se 1 (by rfl) ⟨1390358, by rfl⟩ : syracuseStep 1853811 = 2780717) B2780717
theorem B1853827 : Blo 1853628 1853827 := bstep (se 1 (by rfl) ⟨1390370, by rfl⟩ : syracuseStep 1853827 = 2780741) B2780741
theorem B4696451 : Blo 1853628 4696451 := bstep (se 1 (by rfl) ⟨3522338, by rfl⟩ : syracuseStep 4696451 = 7044677) B7044677
theorem B6261137 : Blo 1853628 6261137 := bstep (se 2 (by rfl) ⟨2347926, by rfl⟩ : syracuseStep 6261137 = 4695853) B4695853
theorem B1853843 : Blo 1853628 1853843 := bstep (se 1 (by rfl) ⟨1390382, by rfl⟩ : syracuseStep 1853843 = 2780765) B2780765
theorem B1853859 : Blo 1853628 1853859 := bstep (se 1 (by rfl) ⟨1390394, by rfl⟩ : syracuseStep 1853859 = 2780789) B2780789
theorem B1853875 : Blo 1853628 1853875 := bstep (se 1 (by rfl) ⟨1390406, by rfl⟩ : syracuseStep 1853875 = 2780813) B2780813
theorem B1853891 : Blo 1853628 1853891 := bstep (se 1 (by rfl) ⟨1390418, by rfl⟩ : syracuseStep 1853891 = 2780837) B2780837
theorem B1853907 : Blo 1853628 1853907 := bstep (se 1 (by rfl) ⟨1390430, by rfl⟩ : syracuseStep 1853907 = 2780861) B2780861
theorem B1853923 : Blo 1853628 1853923 := bstep (se 1 (by rfl) ⟨1390442, by rfl⟩ : syracuseStep 1853923 = 2780885) B2780885
theorem B4172273 : Blo 1853628 4172273 := bstep (se 2 (by rfl) ⟨1564602, by rfl⟩ : syracuseStep 4172273 = 3129205) B3129205
theorem B1853939 : Blo 1853628 1853939 := bstep (se 1 (by rfl) ⟨1390454, by rfl⟩ : syracuseStep 1853939 = 2780909) B2780909
theorem B1853955 : Blo 1853628 1853955 := bstep (se 1 (by rfl) ⟨1390466, by rfl⟩ : syracuseStep 1853955 = 2780933) B2780933
theorem B4172291 : Blo 1853628 4172291 := bstep (se 1 (by rfl) ⟨3129218, by rfl⟩ : syracuseStep 4172291 = 6258437) B6258437
theorem B1853971 : Blo 1853628 1853971 := bstep (se 1 (by rfl) ⟨1390478, by rfl⟩ : syracuseStep 1853971 = 2780957) B2780957
theorem B1853987 : Blo 1853628 1853987 := bstep (se 1 (by rfl) ⟨1390490, by rfl⟩ : syracuseStep 1853987 = 2780981) B2780981
theorem B5941795 : Blo 1853628 5941795 := bstep (se 1 (by rfl) ⟨4456346, by rfl⟩ : syracuseStep 5941795 = 8912693) B8912693
theorem B2640433 : Blo 1853628 2640433 := bstep (se 2 (by rfl) ⟨990162, by rfl⟩ : syracuseStep 2640433 = 1980325) B1980325
theorem B1854003 : Blo 1853628 1854003 := bstep (se 1 (by rfl) ⟨1390502, by rfl⟩ : syracuseStep 1854003 = 2781005) B2781005
theorem B1854019 : Blo 1853628 1854019 := bstep (se 1 (by rfl) ⟨1390514, by rfl⟩ : syracuseStep 1854019 = 2781029) B2781029
theorem B4696643 : Blo 1853628 4696643 := bstep (se 1 (by rfl) ⟨3522482, by rfl⟩ : syracuseStep 4696643 = 7044965) B7044965
theorem B1854035 : Blo 1853628 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B1854051 : Blo 1853628 1854051 := bstep (se 1 (by rfl) ⟨1390538, by rfl⟩ : syracuseStep 1854051 = 2781077) B2781077
theorem B11889251 : Blo 1853628 11889251 := bstep (se 1 (by rfl) ⟨8916938, by rfl⟩ : syracuseStep 11889251 = 17833877) B17833877
theorem B1854067 : Blo 1853628 1854067 := bstep (se 1 (by rfl) ⟨1390550, by rfl⟩ : syracuseStep 1854067 = 2781101) B2781101
theorem B1854083 : Blo 1853628 1854083 := bstep (se 1 (by rfl) ⟨1390562, by rfl⟩ : syracuseStep 1854083 = 2781125) B2781125
theorem B2640529 : Blo 1853628 2640529 := bstep (se 2 (by rfl) ⟨990198, by rfl⟩ : syracuseStep 2640529 = 1980397) B1980397
theorem B1854099 : Blo 1853628 1854099 := bstep (se 1 (by rfl) ⟨1390574, by rfl⟩ : syracuseStep 1854099 = 2781149) B2781149
theorem B1854115 : Blo 1853628 1854115 := bstep (se 1 (by rfl) ⟨1390586, by rfl⟩ : syracuseStep 1854115 = 2781173) B2781173
theorem B1854131 : Blo 1853628 1854131 := bstep (se 1 (by rfl) ⟨1390598, by rfl⟩ : syracuseStep 1854131 = 2781197) B2781197
theorem B1854147 : Blo 1853628 1854147 := bstep (se 1 (by rfl) ⟨1390610, by rfl⟩ : syracuseStep 1854147 = 2781221) B2781221
theorem B1854163 : Blo 1853628 1854163 := bstep (se 1 (by rfl) ⟨1390622, by rfl⟩ : syracuseStep 1854163 = 2781245) B2781245
theorem B1854179 : Blo 1853628 1854179 := bstep (se 1 (by rfl) ⟨1390634, by rfl⟩ : syracuseStep 1854179 = 2781269) B2781269
theorem B1854195 : Blo 1853628 1854195 := bstep (se 1 (by rfl) ⟨1390646, by rfl⟩ : syracuseStep 1854195 = 2781293) B2781293
theorem B1854211 : Blo 1853628 1854211 := bstep (se 1 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 1854211 = 2781317) B2781317
theorem B7924493 : Blo 1853628 7924493 := bstep (se 3 (by rfl) ⟨1485842, by rfl⟩ : syracuseStep 7924493 = 2971685) B2971685
theorem B4172561 : Blo 1853628 4172561 := bstep (se 2 (by rfl) ⟨1564710, by rfl⟩ : syracuseStep 4172561 = 3129421) B3129421
theorem B1854227 : Blo 1853628 1854227 := bstep (se 1 (by rfl) ⟨1390670, by rfl⟩ : syracuseStep 1854227 = 2781341) B2781341
theorem B1854243 : Blo 1853628 1854243 := bstep (se 1 (by rfl) ⟨1390682, by rfl⟩ : syracuseStep 1854243 = 2781365) B2781365
theorem B4172579 : Blo 1853628 4172579 := bstep (se 1 (by rfl) ⟨3129434, by rfl⟩ : syracuseStep 4172579 = 6258869) B6258869
theorem B1854259 : Blo 1853628 1854259 := bstep (se 1 (by rfl) ⟨1390694, by rfl⟩ : syracuseStep 1854259 = 2781389) B2781389
theorem B1854275 : Blo 1853628 1854275 := bstep (se 1 (by rfl) ⟨1390706, by rfl⟩ : syracuseStep 1854275 = 2781413) B2781413
theorem B1854291 : Blo 1853628 1854291 := bstep (se 1 (by rfl) ⟨1390718, by rfl⟩ : syracuseStep 1854291 = 2781437) B2781437
theorem B1854307 : Blo 1853628 1854307 := bstep (se 1 (by rfl) ⟨1390730, by rfl⟩ : syracuseStep 1854307 = 2781461) B2781461
theorem B1854323 : Blo 1853628 1854323 := bstep (se 1 (by rfl) ⟨1390742, by rfl⟩ : syracuseStep 1854323 = 2781485) B2781485
theorem B3173249 : Blo 1853628 3173249 := bstep (se 2 (by rfl) ⟨1189968, by rfl⟩ : syracuseStep 3173249 = 2379937) B2379937
theorem B1854339 : Blo 1853628 1854339 := bstep (se 1 (by rfl) ⟨1390754, by rfl⟩ : syracuseStep 1854339 = 2781509) B2781509
theorem B1854355 : Blo 1853628 1854355 := bstep (se 1 (by rfl) ⟨1390766, by rfl⟩ : syracuseStep 1854355 = 2781533) B2781533
theorem B2034595 : Blo 1853628 2034595 := bstep (se 1 (by rfl) ⟨1525946, by rfl⟩ : syracuseStep 2034595 = 3051893) B3051893
theorem B1854371 : Blo 1853628 1854371 := bstep (se 1 (by rfl) ⟨1390778, by rfl⟩ : syracuseStep 1854371 = 2781557) B2781557
theorem B6261677 : Blo 1853628 6261677 := bstep (se 3 (by rfl) ⟨1174064, by rfl⟩ : syracuseStep 6261677 = 2348129) B2348129
theorem B3812273 : Blo 1853628 3812273 := bstep (se 2 (by rfl) ⟨1429602, by rfl⟩ : syracuseStep 3812273 = 2859205) B2859205
theorem B1854387 : Blo 1853628 1854387 := bstep (se 1 (by rfl) ⟨1390790, by rfl⟩ : syracuseStep 1854387 = 2781581) B2781581
theorem B1854403 : Blo 1853628 1854403 := bstep (se 1 (by rfl) ⟨1390802, by rfl⟩ : syracuseStep 1854403 = 2781605) B2781605
theorem B3959761 : Blo 1853628 3959761 := bstep (se 2 (by rfl) ⟨1484910, by rfl⟩ : syracuseStep 3959761 = 2969821) B2969821
theorem B1854419 : Blo 1853628 1854419 := bstep (se 1 (by rfl) ⟨1390814, by rfl⟩ : syracuseStep 1854419 = 2781629) B2781629
theorem B1854435 : Blo 1853628 1854435 := bstep (se 1 (by rfl) ⟨1390826, by rfl⟩ : syracuseStep 1854435 = 2781653) B2781653
theorem B6261731 : Blo 1853628 6261731 := bstep (se 1 (by rfl) ⟨4696298, by rfl⟩ : syracuseStep 6261731 = 9392597) B9392597
theorem B8915939 : Blo 1853628 8915939 := bstep (se 1 (by rfl) ⟨6686954, by rfl⟩ : syracuseStep 8915939 = 13373909) B13373909
theorem B1854451 : Blo 1853628 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B1854467 : Blo 1853628 1854467 := bstep (se 1 (by rfl) ⟨1390850, by rfl⟩ : syracuseStep 1854467 = 2781701) B2781701
theorem B1854483 : Blo 1853628 1854483 := bstep (se 1 (by rfl) ⟨1390862, by rfl⟩ : syracuseStep 1854483 = 2781725) B2781725
theorem B1854499 : Blo 1853628 1854499 := bstep (se 1 (by rfl) ⟨1390874, by rfl⟩ : syracuseStep 1854499 = 2781749) B2781749
theorem B9391139 : Blo 1853628 9391139 := bstep (se 1 (by rfl) ⟨7043354, by rfl⟩ : syracuseStep 9391139 = 14086709) B14086709
theorem B4172849 : Blo 1853628 4172849 := bstep (se 2 (by rfl) ⟨1564818, by rfl⟩ : syracuseStep 4172849 = 3129637) B3129637
theorem B4516913 : Blo 1853628 4516913 := bstep (se 2 (by rfl) ⟨1693842, by rfl⟩ : syracuseStep 4516913 = 3387685) B3387685
theorem B1854515 : Blo 1853628 1854515 := bstep (se 1 (by rfl) ⟨1390886, by rfl⟩ : syracuseStep 1854515 = 2781773) B2781773
theorem B1854531 : Blo 1853628 1854531 := bstep (se 1 (by rfl) ⟨1390898, by rfl⟩ : syracuseStep 1854531 = 2781797) B2781797
theorem B4172867 : Blo 1853628 4172867 := bstep (se 1 (by rfl) ⟨3129650, by rfl⟩ : syracuseStep 4172867 = 6259301) B6259301
theorem B1854547 : Blo 1853628 1854547 := bstep (se 1 (by rfl) ⟨1390910, by rfl⟩ : syracuseStep 1854547 = 2781821) B2781821
theorem B1854563 : Blo 1853628 1854563 := bstep (se 1 (by rfl) ⟨1390922, by rfl⟩ : syracuseStep 1854563 = 2781845) B2781845
theorem B12717155 : Blo 1853628 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B1854579 : Blo 1853628 1854579 := bstep (se 1 (by rfl) ⟨1390934, by rfl⟩ : syracuseStep 1854579 = 2781869) B2781869
theorem B2641025 : Blo 1853628 2641025 := bstep (se 2 (by rfl) ⟨990384, by rfl⟩ : syracuseStep 2641025 = 1980769) B1980769
theorem B1854595 : Blo 1853628 1854595 := bstep (se 1 (by rfl) ⟨1390946, by rfl⟩ : syracuseStep 1854595 = 2781893) B2781893
theorem B11586701 : Blo 1853628 11586701 := bstep (se 3 (by rfl) ⟨2172506, by rfl⟩ : syracuseStep 11586701 = 4345013) B4345013
theorem B1854611 : Blo 1853628 1854611 := bstep (se 1 (by rfl) ⟨1390958, by rfl⟩ : syracuseStep 1854611 = 2781917) B2781917
theorem B1854627 : Blo 1853628 1854627 := bstep (se 1 (by rfl) ⟨1390970, by rfl⟩ : syracuseStep 1854627 = 2781941) B2781941
theorem B1854643 : Blo 1853628 1854643 := bstep (se 1 (by rfl) ⟨1390982, by rfl⟩ : syracuseStep 1854643 = 2781965) B2781965
theorem B1854659 : Blo 1853628 1854659 := bstep (se 1 (by rfl) ⟨1390994, by rfl⟩ : syracuseStep 1854659 = 2781989) B2781989
theorem B1854675 : Blo 1853628 1854675 := bstep (se 1 (by rfl) ⟨1391006, by rfl⟩ : syracuseStep 1854675 = 2782013) B2782013
theorem B1854691 : Blo 1853628 1854691 := bstep (se 1 (by rfl) ⟨1391018, by rfl⟩ : syracuseStep 1854691 = 2782037) B2782037
theorem B10022129 : Blo 1853628 10022129 := bstep (se 2 (by rfl) ⟨3758298, by rfl⟩ : syracuseStep 10022129 = 7516597) B7516597
theorem B6262001 : Blo 1853628 6262001 := bstep (se 2 (by rfl) ⟨2348250, by rfl⟩ : syracuseStep 6262001 = 4696501) B4696501
theorem B1854707 : Blo 1853628 1854707 := bstep (se 1 (by rfl) ⟨1391030, by rfl⟩ : syracuseStep 1854707 = 2782061) B2782061
theorem B1854723 : Blo 1853628 1854723 := bstep (se 1 (by rfl) ⟨1391042, by rfl⟩ : syracuseStep 1854723 = 2782085) B2782085
theorem B1854739 : Blo 1853628 1854739 := bstep (se 1 (by rfl) ⟨1391054, by rfl⟩ : syracuseStep 1854739 = 2782109) B2782109
theorem B1854755 : Blo 1853628 1854755 := bstep (se 1 (by rfl) ⟨1391066, by rfl⟩ : syracuseStep 1854755 = 2782133) B2782133
theorem B2780465 : Blo 1853628 2780465 := bstep (se 2 (by rfl) ⟨1042674, by rfl⟩ : syracuseStep 2780465 = 2085349) B2085349
theorem B3050801 : Blo 1853628 3050801 := bstep (se 2 (by rfl) ⟨1144050, by rfl⟩ : syracuseStep 3050801 = 2288101) B2288101
theorem B1854771 : Blo 1853628 1854771 := bstep (se 1 (by rfl) ⟨1391078, by rfl⟩ : syracuseStep 1854771 = 2782157) B2782157
theorem B2780483 : Blo 1853628 2780483 := bstep (se 1 (by rfl) ⟨2085362, by rfl⟩ : syracuseStep 2780483 = 4170725) B4170725
theorem B1854787 : Blo 1853628 1854787 := bstep (se 1 (by rfl) ⟨1391090, by rfl⟩ : syracuseStep 1854787 = 2782181) B2782181
theorem B4173137 : Blo 1853628 4173137 := bstep (se 2 (by rfl) ⟨1564926, by rfl⟩ : syracuseStep 4173137 = 3129853) B3129853
theorem B1854803 : Blo 1853628 1854803 := bstep (se 1 (by rfl) ⟨1391102, by rfl⟩ : syracuseStep 1854803 = 2782205) B2782205
theorem B2780513 : Blo 1853628 2780513 := bstep (se 2 (by rfl) ⟨1042692, by rfl⟩ : syracuseStep 2780513 = 2085385) B2085385
theorem B4173155 : Blo 1853628 4173155 := bstep (se 1 (by rfl) ⟨3129866, by rfl⟩ : syracuseStep 4173155 = 6259733) B6259733
theorem B1854819 : Blo 1853628 1854819 := bstep (se 1 (by rfl) ⟨1391114, by rfl⟩ : syracuseStep 1854819 = 2782229) B2782229
theorem B2780531 : Blo 1853628 2780531 := bstep (se 1 (by rfl) ⟨2085398, by rfl⟩ : syracuseStep 2780531 = 4170797) B4170797
theorem B1854835 : Blo 1853628 1854835 := bstep (se 1 (by rfl) ⟨1391126, by rfl⟩ : syracuseStep 1854835 = 2782253) B2782253
theorem B3173747 : Blo 1853628 3173747 := bstep (se 1 (by rfl) ⟨2380310, by rfl⟩ : syracuseStep 3173747 = 4760621) B4760621
theorem B1854851 : Blo 1853628 1854851 := bstep (se 1 (by rfl) ⟨1391138, by rfl⟩ : syracuseStep 1854851 = 2782277) B2782277
theorem B2780561 : Blo 1853628 2780561 := bstep (se 2 (by rfl) ⟨1042710, by rfl⟩ : syracuseStep 2780561 = 2085421) B2085421
theorem B1854867 : Blo 1853628 1854867 := bstep (se 1 (by rfl) ⟨1391150, by rfl⟩ : syracuseStep 1854867 = 2782301) B2782301
theorem B2780579 : Blo 1853628 2780579 := bstep (se 1 (by rfl) ⟨2085434, by rfl⟩ : syracuseStep 2780579 = 4170869) B4170869
theorem B2346403 : Blo 1853628 2346403 := bstep (se 1 (by rfl) ⟨1759802, by rfl⟩ : syracuseStep 2346403 = 3519605) B3519605
theorem B1854883 : Blo 1853628 1854883 := bstep (se 1 (by rfl) ⟨1391162, by rfl⟩ : syracuseStep 1854883 = 2782325) B2782325
theorem B1854899 : Blo 1853628 1854899 := bstep (se 1 (by rfl) ⟨1391174, by rfl⟩ : syracuseStep 1854899 = 2782349) B2782349
theorem B2780609 : Blo 1853628 2780609 := bstep (se 2 (by rfl) ⟨1042728, by rfl⟩ : syracuseStep 2780609 = 2085457) B2085457
theorem B1854915 : Blo 1853628 1854915 := bstep (se 1 (by rfl) ⟨1391186, by rfl⟩ : syracuseStep 1854915 = 2782373) B2782373
theorem B2780627 : Blo 1853628 2780627 := bstep (se 1 (by rfl) ⟨2085470, by rfl⟩ : syracuseStep 2780627 = 4170941) B4170941
theorem B1854931 : Blo 1853628 1854931 := bstep (se 1 (by rfl) ⟨1391198, by rfl⟩ : syracuseStep 1854931 = 2782397) B2782397
theorem B1854947 : Blo 1853628 1854947 := bstep (se 1 (by rfl) ⟨1391210, by rfl⟩ : syracuseStep 1854947 = 2782421) B2782421
theorem B2780657 : Blo 1853628 2780657 := bstep (se 2 (by rfl) ⟨1042746, by rfl⟩ : syracuseStep 2780657 = 2085493) B2085493
theorem B1854963 : Blo 1853628 1854963 := bstep (se 1 (by rfl) ⟨1391222, by rfl⟩ : syracuseStep 1854963 = 2782445) B2782445
theorem B2780675 : Blo 1853628 2780675 := bstep (se 1 (by rfl) ⟨2085506, by rfl⟩ : syracuseStep 2780675 = 4171013) B4171013
theorem B2346499 : Blo 1853628 2346499 := bstep (se 1 (by rfl) ⟨1759874, by rfl⟩ : syracuseStep 2346499 = 3519749) B3519749
theorem B1854979 : Blo 1853628 1854979 := bstep (se 1 (by rfl) ⟨1391234, by rfl⟩ : syracuseStep 1854979 = 2782469) B2782469
theorem B1879571 : Blo 1853628 1879571 := bstep (se 1 (by rfl) ⟨1409678, by rfl⟩ : syracuseStep 1879571 = 2819357) B2819357
theorem B1854995 : Blo 1853628 1854995 := bstep (se 1 (by rfl) ⟨1391246, by rfl⟩ : syracuseStep 1854995 = 2782493) B2782493
theorem B2780705 : Blo 1853628 2780705 := bstep (se 2 (by rfl) ⟨1042764, by rfl⟩ : syracuseStep 2780705 = 2085529) B2085529
theorem B1855011 : Blo 1853628 1855011 := bstep (se 1 (by rfl) ⟨1391258, by rfl⟩ : syracuseStep 1855011 = 2782517) B2782517
theorem B2780723 : Blo 1853628 2780723 := bstep (se 1 (by rfl) ⟨2085542, by rfl⟩ : syracuseStep 2780723 = 4171085) B4171085
theorem B1855027 : Blo 1853628 1855027 := bstep (se 1 (by rfl) ⟨1391270, by rfl⟩ : syracuseStep 1855027 = 2782541) B2782541
theorem B1855043 : Blo 1853628 1855043 := bstep (se 1 (by rfl) ⟨1391282, by rfl⟩ : syracuseStep 1855043 = 2782565) B2782565
theorem B2780753 : Blo 1853628 2780753 := bstep (se 2 (by rfl) ⟨1042782, by rfl⟩ : syracuseStep 2780753 = 2085565) B2085565
theorem B1855059 : Blo 1853628 1855059 := bstep (se 1 (by rfl) ⟨1391294, by rfl⟩ : syracuseStep 1855059 = 2782589) B2782589
theorem B2780771 : Blo 1853628 2780771 := bstep (se 1 (by rfl) ⟨2085578, by rfl⟩ : syracuseStep 2780771 = 4171157) B4171157
theorem B1855075 : Blo 1853628 1855075 := bstep (se 1 (by rfl) ⟨1391306, by rfl⟩ : syracuseStep 1855075 = 2782613) B2782613
theorem B4173425 : Blo 1853628 4173425 := bstep (se 2 (by rfl) ⟨1565034, by rfl⟩ : syracuseStep 4173425 = 3130069) B3130069
theorem B1855091 : Blo 1853628 1855091 := bstep (se 1 (by rfl) ⟨1391318, by rfl⟩ : syracuseStep 1855091 = 2782637) B2782637
theorem B2780801 : Blo 1853628 2780801 := bstep (se 2 (by rfl) ⟨1042800, by rfl⟩ : syracuseStep 2780801 = 2085601) B2085601
theorem B4173443 : Blo 1853628 4173443 := bstep (se 1 (by rfl) ⟨3130082, by rfl⟩ : syracuseStep 4173443 = 6260165) B6260165
theorem B1855107 : Blo 1853628 1855107 := bstep (se 1 (by rfl) ⟨1391330, by rfl⟩ : syracuseStep 1855107 = 2782661) B2782661
theorem B45125261 : Blo 1853628 45125261 := bstep (se 3 (by rfl) ⟨8460986, by rfl⟩ : syracuseStep 45125261 = 16921973) B16921973
theorem B2780819 : Blo 1853628 2780819 := bstep (se 1 (by rfl) ⟨2085614, by rfl⟩ : syracuseStep 2780819 = 4171229) B4171229
theorem B1855123 : Blo 1853628 1855123 := bstep (se 1 (by rfl) ⟨1391342, by rfl⟩ : syracuseStep 1855123 = 2782685) B2782685
theorem B1855139 : Blo 1853628 1855139 := bstep (se 1 (by rfl) ⟨1391354, by rfl⟩ : syracuseStep 1855139 = 2782709) B2782709
theorem B2780849 : Blo 1853628 2780849 := bstep (se 2 (by rfl) ⟨1042818, by rfl⟩ : syracuseStep 2780849 = 2085637) B2085637
theorem B8457905 : Blo 1853628 8457905 := bstep (se 2 (by rfl) ⟨3171714, by rfl⟩ : syracuseStep 8457905 = 6343429) B6343429
theorem B1855155 : Blo 1853628 1855155 := bstep (se 1 (by rfl) ⟨1391366, by rfl⟩ : syracuseStep 1855155 = 2782733) B2782733
theorem B2780867 : Blo 1853628 2780867 := bstep (se 1 (by rfl) ⟨2085650, by rfl⟩ : syracuseStep 2780867 = 4171301) B4171301
theorem B1855171 : Blo 1853628 1855171 := bstep (se 1 (by rfl) ⟨1391378, by rfl⟩ : syracuseStep 1855171 = 2782757) B2782757
theorem B18067141 : Blo 1853628 18067141 := bstep (se 4 (by rfl) ⟨1693794, by rfl⟩ : syracuseStep 18067141 = 3387589) B3387589
theorem B1855187 : Blo 1853628 1855187 := bstep (se 1 (by rfl) ⟨1391390, by rfl⟩ : syracuseStep 1855187 = 2782781) B2782781
theorem B2780897 : Blo 1853628 2780897 := bstep (se 2 (by rfl) ⟨1042836, by rfl⟩ : syracuseStep 2780897 = 2085673) B2085673
theorem B1855203 : Blo 1853628 1855203 := bstep (se 1 (by rfl) ⟨1391402, by rfl⟩ : syracuseStep 1855203 = 2782805) B2782805
theorem B2780915 : Blo 1853628 2780915 := bstep (se 1 (by rfl) ⟨2085686, by rfl⟩ : syracuseStep 2780915 = 4171373) B4171373
theorem B1855219 : Blo 1853628 1855219 := bstep (se 1 (by rfl) ⟨1391414, by rfl⟩ : syracuseStep 1855219 = 2782829) B2782829
theorem B1855235 : Blo 1853628 1855235 := bstep (se 1 (by rfl) ⟨1391426, by rfl⟩ : syracuseStep 1855235 = 2782853) B2782853
theorem B8916749 : Blo 1853628 8916749 := bstep (se 3 (by rfl) ⟨1671890, by rfl⟩ : syracuseStep 8916749 = 3343781) B3343781
theorem B2780945 : Blo 1853628 2780945 := bstep (se 2 (by rfl) ⟨1042854, by rfl⟩ : syracuseStep 2780945 = 2085709) B2085709
theorem B6262541 : Blo 1853628 6262541 := bstep (se 3 (by rfl) ⟨1174226, by rfl⟩ : syracuseStep 6262541 = 2348453) B2348453
theorem B1855251 : Blo 1853628 1855251 := bstep (se 1 (by rfl) ⟨1391438, by rfl⟩ : syracuseStep 1855251 = 2782877) B2782877
theorem B2780963 : Blo 1853628 2780963 := bstep (se 1 (by rfl) ⟨2085722, by rfl⟩ : syracuseStep 2780963 = 4171445) B4171445
theorem B7040803 : Blo 1853628 7040803 := bstep (se 1 (by rfl) ⟨5280602, by rfl⟩ : syracuseStep 7040803 = 10561205) B10561205
theorem B1855267 : Blo 1853628 1855267 := bstep (se 1 (by rfl) ⟨1391450, by rfl⟩ : syracuseStep 1855267 = 2782901) B2782901
theorem B1855283 : Blo 1853628 1855283 := bstep (se 1 (by rfl) ⟨1391462, by rfl⟩ : syracuseStep 1855283 = 2782925) B2782925
theorem B2780993 : Blo 1853628 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B5279555 : Blo 1853628 5279555 := bstep (se 1 (by rfl) ⟨3959666, by rfl⟩ : syracuseStep 5279555 = 7919333) B7919333
theorem B15249221 : Blo 1853628 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B1855299 : Blo 1853628 1855299 := bstep (se 1 (by rfl) ⟨1391474, by rfl⟩ : syracuseStep 1855299 = 2782949) B2782949
theorem B6262595 : Blo 1853628 6262595 := bstep (se 1 (by rfl) ⟨4696946, by rfl⟩ : syracuseStep 6262595 = 9393893) B9393893
theorem B9391949 : Blo 1853628 9391949 := bstep (se 3 (by rfl) ⟨1760990, by rfl⟩ : syracuseStep 9391949 = 3521981) B3521981
theorem B2781011 : Blo 1853628 2781011 := bstep (se 1 (by rfl) ⟨2085758, by rfl⟩ : syracuseStep 2781011 = 4171517) B4171517
theorem B1855315 : Blo 1853628 1855315 := bstep (se 1 (by rfl) ⟨1391486, by rfl⟩ : syracuseStep 1855315 = 2782973) B2782973
theorem B1855331 : Blo 1853628 1855331 := bstep (se 1 (by rfl) ⟨1391498, by rfl⟩ : syracuseStep 1855331 = 2782997) B2782997
theorem B2781041 : Blo 1853628 2781041 := bstep (se 2 (by rfl) ⟨1042890, by rfl⟩ : syracuseStep 2781041 = 2085781) B2085781
theorem B1855347 : Blo 1853628 1855347 := bstep (se 1 (by rfl) ⟨1391510, by rfl⟩ : syracuseStep 1855347 = 2783021) B2783021
theorem B2781059 : Blo 1853628 2781059 := bstep (se 1 (by rfl) ⟨2085794, by rfl⟩ : syracuseStep 2781059 = 4171589) B4171589
theorem B1855363 : Blo 1853628 1855363 := bstep (se 1 (by rfl) ⟨1391522, by rfl⟩ : syracuseStep 1855363 = 2783045) B2783045
theorem B4173713 : Blo 1853628 4173713 := bstep (se 2 (by rfl) ⟨1565142, by rfl⟩ : syracuseStep 4173713 = 3130285) B3130285
theorem B1855379 : Blo 1853628 1855379 := bstep (se 1 (by rfl) ⟨1391534, by rfl⟩ : syracuseStep 1855379 = 2783069) B2783069
theorem B2781089 : Blo 1853628 2781089 := bstep (se 2 (by rfl) ⟨1042908, by rfl⟩ : syracuseStep 2781089 = 2085817) B2085817
theorem B4173731 : Blo 1853628 4173731 := bstep (se 1 (by rfl) ⟨3130298, by rfl⟩ : syracuseStep 4173731 = 6260597) B6260597
theorem B1855395 : Blo 1853628 1855395 := bstep (se 1 (by rfl) ⟨1391546, by rfl⟩ : syracuseStep 1855395 = 2783093) B2783093
theorem B2781107 : Blo 1853628 2781107 := bstep (se 1 (by rfl) ⟨2085830, by rfl⟩ : syracuseStep 2781107 = 4171661) B4171661
theorem B1855411 : Blo 1853628 1855411 := bstep (se 1 (by rfl) ⟨1391558, by rfl⟩ : syracuseStep 1855411 = 2783117) B2783117
theorem B1855427 : Blo 1853628 1855427 := bstep (se 1 (by rfl) ⟨1391570, by rfl⟩ : syracuseStep 1855427 = 2783141) B2783141
theorem B2781137 : Blo 1853628 2781137 := bstep (se 2 (by rfl) ⟨1042926, by rfl⟩ : syracuseStep 2781137 = 2085853) B2085853
theorem B1855443 : Blo 1853628 1855443 := bstep (se 1 (by rfl) ⟨1391582, by rfl⟩ : syracuseStep 1855443 = 2783165) B2783165
theorem B2781155 : Blo 1853628 2781155 := bstep (se 1 (by rfl) ⟨2085866, by rfl⟩ : syracuseStep 2781155 = 4171733) B4171733
theorem B15044579 : Blo 1853628 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B1855459 : Blo 1853628 1855459 := bstep (se 1 (by rfl) ⟨1391594, by rfl⟩ : syracuseStep 1855459 = 2783189) B2783189
theorem B2641891 : Blo 1853628 2641891 := bstep (se 1 (by rfl) ⟨1981418, by rfl⟩ : syracuseStep 2641891 = 3962837) B3962837
theorem B2346995 : Blo 1853628 2346995 := bstep (se 1 (by rfl) ⟨1760246, by rfl⟩ : syracuseStep 2346995 = 3520493) B3520493
theorem B1855475 : Blo 1853628 1855475 := bstep (se 1 (by rfl) ⟨1391606, by rfl⟩ : syracuseStep 1855475 = 2783213) B2783213
theorem B2781185 : Blo 1853628 2781185 := bstep (se 2 (by rfl) ⟨1042944, by rfl⟩ : syracuseStep 2781185 = 2085889) B2085889
theorem B1855491 : Blo 1853628 1855491 := bstep (se 1 (by rfl) ⟨1391618, by rfl⟩ : syracuseStep 1855491 = 2783237) B2783237
theorem B8458253 : Blo 1853628 8458253 := bstep (se 3 (by rfl) ⟨1585922, by rfl⟩ : syracuseStep 8458253 = 3171845) B3171845
theorem B2781203 : Blo 1853628 2781203 := bstep (se 1 (by rfl) ⟨2085902, by rfl⟩ : syracuseStep 2781203 = 4171805) B4171805
theorem B1855507 : Blo 1853628 1855507 := bstep (se 1 (by rfl) ⟨1391630, by rfl⟩ : syracuseStep 1855507 = 2783261) B2783261
theorem B2969635 : Blo 1853628 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B1855523 : Blo 1853628 1855523 := bstep (se 1 (by rfl) ⟨1391642, by rfl⟩ : syracuseStep 1855523 = 2783285) B2783285
theorem B2781233 : Blo 1853628 2781233 := bstep (se 2 (by rfl) ⟨1042962, by rfl⟩ : syracuseStep 2781233 = 2085925) B2085925
theorem B7925809 : Blo 1853628 7925809 := bstep (se 2 (by rfl) ⟨2972178, by rfl⟩ : syracuseStep 7925809 = 5944357) B5944357
theorem B1855539 : Blo 1853628 1855539 := bstep (se 1 (by rfl) ⟨1391654, by rfl⟩ : syracuseStep 1855539 = 2783309) B2783309
theorem B2781251 : Blo 1853628 2781251 := bstep (se 1 (by rfl) ⟨2085938, by rfl⟩ : syracuseStep 2781251 = 4171877) B4171877
theorem B2641987 : Blo 1853628 2641987 := bstep (se 1 (by rfl) ⟨1981490, by rfl⟩ : syracuseStep 2641987 = 3962981) B3962981
theorem B1855555 : Blo 1853628 1855555 := bstep (se 1 (by rfl) ⟨1391666, by rfl⟩ : syracuseStep 1855555 = 2783333) B2783333
theorem B1855571 : Blo 1853628 1855571 := bstep (se 1 (by rfl) ⟨1391678, by rfl⟩ : syracuseStep 1855571 = 2783357) B2783357
theorem B2781281 : Blo 1853628 2781281 := bstep (se 2 (by rfl) ⟨1042980, by rfl⟩ : syracuseStep 2781281 = 2085961) B2085961
theorem B5943395 : Blo 1853628 5943395 := bstep (se 1 (by rfl) ⟨4457546, by rfl⟩ : syracuseStep 5943395 = 8915093) B8915093
theorem B1855587 : Blo 1853628 1855587 := bstep (se 1 (by rfl) ⟨1391690, by rfl⟩ : syracuseStep 1855587 = 2783381) B2783381
theorem B2781299 : Blo 1853628 2781299 := bstep (se 1 (by rfl) ⟨2085974, by rfl⟩ : syracuseStep 2781299 = 4171949) B4171949
theorem B1855603 : Blo 1853628 1855603 := bstep (se 1 (by rfl) ⟨1391702, by rfl⟩ : syracuseStep 1855603 = 2783405) B2783405
theorem B1855619 : Blo 1853628 1855619 := bstep (se 1 (by rfl) ⟨1391714, by rfl⟩ : syracuseStep 1855619 = 2783429) B2783429
theorem B2781329 : Blo 1853628 2781329 := bstep (se 2 (by rfl) ⟨1042998, by rfl⟩ : syracuseStep 2781329 = 2085997) B2085997
theorem B2781347 : Blo 1853628 2781347 := bstep (se 1 (by rfl) ⟨2086010, by rfl⟩ : syracuseStep 2781347 = 4172021) B4172021
theorem B6344867 : Blo 1853628 6344867 := bstep (se 1 (by rfl) ⟨4758650, by rfl⟩ : syracuseStep 6344867 = 9517301) B9517301
theorem B4174001 : Blo 1853628 4174001 := bstep (se 2 (by rfl) ⟨1565250, by rfl⟩ : syracuseStep 4174001 = 3130501) B3130501
theorem B2781377 : Blo 1853628 2781377 := bstep (se 2 (by rfl) ⟨1043016, by rfl⟩ : syracuseStep 2781377 = 2086033) B2086033
theorem B4174019 : Blo 1853628 4174019 := bstep (se 1 (by rfl) ⟨3130514, by rfl⟩ : syracuseStep 4174019 = 6261029) B6261029
theorem B26726597 : Blo 1853628 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B2781395 : Blo 1853628 2781395 := bstep (se 1 (by rfl) ⟨2086046, by rfl⟩ : syracuseStep 2781395 = 4172093) B4172093
theorem B2781425 : Blo 1853628 2781425 := bstep (se 2 (by rfl) ⟨1043034, by rfl⟩ : syracuseStep 2781425 = 2086069) B2086069
theorem B2781443 : Blo 1853628 2781443 := bstep (se 1 (by rfl) ⟨2086082, by rfl⟩ : syracuseStep 2781443 = 4172165) B4172165
theorem B2781473 : Blo 1853628 2781473 := bstep (se 2 (by rfl) ⟨1043052, by rfl⟩ : syracuseStep 2781473 = 2086105) B2086105
theorem B2781491 : Blo 1853628 2781491 := bstep (se 1 (by rfl) ⟨2086118, by rfl⟩ : syracuseStep 2781491 = 4172237) B4172237
theorem B2781521 : Blo 1853628 2781521 := bstep (se 2 (by rfl) ⟨1043070, by rfl⟩ : syracuseStep 2781521 = 2086141) B2086141
theorem B2781539 : Blo 1853628 2781539 := bstep (se 1 (by rfl) ⟨2086154, by rfl⟩ : syracuseStep 2781539 = 4172309) B4172309
theorem B2781569 : Blo 1853628 2781569 := bstep (se 2 (by rfl) ⟨1043088, by rfl⟩ : syracuseStep 2781569 = 2086177) B2086177
theorem B2781587 : Blo 1853628 2781587 := bstep (se 1 (by rfl) ⟨2086190, by rfl⟩ : syracuseStep 2781587 = 4172381) B4172381
theorem B2781617 : Blo 1853628 2781617 := bstep (se 2 (by rfl) ⟨1043106, by rfl⟩ : syracuseStep 2781617 = 2086213) B2086213
theorem B2781635 : Blo 1853628 2781635 := bstep (se 1 (by rfl) ⟨2086226, by rfl⟩ : syracuseStep 2781635 = 4172453) B4172453
theorem B4174289 : Blo 1853628 4174289 := bstep (se 2 (by rfl) ⟨1565358, by rfl⟩ : syracuseStep 4174289 = 3130717) B3130717
theorem B2781665 : Blo 1853628 2781665 := bstep (se 2 (by rfl) ⟨1043124, by rfl⟩ : syracuseStep 2781665 = 2086249) B2086249
theorem B4174307 : Blo 1853628 4174307 := bstep (se 1 (by rfl) ⟨3130730, by rfl⟩ : syracuseStep 4174307 = 6261461) B6261461
theorem B2781683 : Blo 1853628 2781683 := bstep (se 1 (by rfl) ⟨2086262, by rfl⟩ : syracuseStep 2781683 = 4172525) B4172525
theorem B2781713 : Blo 1853628 2781713 := bstep (se 2 (by rfl) ⟨1043142, by rfl⟩ : syracuseStep 2781713 = 2086285) B2086285
theorem B2781731 : Blo 1853628 2781731 := bstep (se 1 (by rfl) ⟨2086298, by rfl⟩ : syracuseStep 2781731 = 4172597) B4172597
theorem B9384497 : Blo 1853628 9384497 := bstep (se 2 (by rfl) ⟨3519186, by rfl⟩ : syracuseStep 9384497 = 7038373) B7038373
theorem B2781761 : Blo 1853628 2781761 := bstep (se 2 (by rfl) ⟨1043160, by rfl⟩ : syracuseStep 2781761 = 2086321) B2086321
theorem B2781779 : Blo 1853628 2781779 := bstep (se 1 (by rfl) ⟨2086334, by rfl⟩ : syracuseStep 2781779 = 4172669) B4172669
theorem B2085475 : Blo 1853628 2085475 := bstep (se 1 (by rfl) ⟨1564106, by rfl⟩ : syracuseStep 2085475 = 3128213) B3128213
theorem B2781809 : Blo 1853628 2781809 := bstep (se 2 (by rfl) ⟨1043178, by rfl⟩ : syracuseStep 2781809 = 2086357) B2086357
theorem B2781827 : Blo 1853628 2781827 := bstep (se 1 (by rfl) ⟨2086370, by rfl⟩ : syracuseStep 2781827 = 4172741) B4172741
theorem B2781857 : Blo 1853628 2781857 := bstep (se 2 (by rfl) ⟨1043196, by rfl⟩ : syracuseStep 2781857 = 2086393) B2086393
theorem B2781875 : Blo 1853628 2781875 := bstep (se 1 (by rfl) ⟨2086406, by rfl⟩ : syracuseStep 2781875 = 4172813) B4172813
theorem B2347699 : Blo 1853628 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B1905347 : Blo 1853628 1905347 := bstep (se 1 (by rfl) ⟨1429010, by rfl⟩ : syracuseStep 1905347 = 2858021) B2858021
theorem B2781905 : Blo 1853628 2781905 := bstep (se 2 (by rfl) ⟨1043214, by rfl⟩ : syracuseStep 2781905 = 2086429) B2086429
theorem B7918307 : Blo 1853628 7918307 := bstep (se 1 (by rfl) ⟨5938730, by rfl⟩ : syracuseStep 7918307 = 11877461) B11877461
theorem B2781923 : Blo 1853628 2781923 := bstep (se 1 (by rfl) ⟨2086442, by rfl⟩ : syracuseStep 2781923 = 4172885) B4172885
theorem B5640941 : Blo 1853628 5640941 := bstep (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) B2115353
theorem B3519217 : Blo 1853628 3519217 := bstep (se 2 (by rfl) ⟨1319706, by rfl⟩ : syracuseStep 3519217 = 2639413) B2639413
theorem B2970353 : Blo 1853628 2970353 := bstep (se 2 (by rfl) ⟨1113882, by rfl⟩ : syracuseStep 2970353 = 2227765) B2227765
theorem B2085619 : Blo 1853628 2085619 := bstep (se 1 (by rfl) ⟨1564214, by rfl⟩ : syracuseStep 2085619 = 3128429) B3128429
theorem B4174577 : Blo 1853628 4174577 := bstep (se 2 (by rfl) ⟨1565466, by rfl⟩ : syracuseStep 4174577 = 3130933) B3130933
theorem B2781953 : Blo 1853628 2781953 := bstep (se 2 (by rfl) ⟨1043232, by rfl⟩ : syracuseStep 2781953 = 2086465) B2086465
theorem B4174595 : Blo 1853628 4174595 := bstep (se 1 (by rfl) ⟨3130946, by rfl⟩ : syracuseStep 4174595 = 6261893) B6261893
theorem B2781971 : Blo 1853628 2781971 := bstep (se 1 (by rfl) ⟨2086478, by rfl⟩ : syracuseStep 2781971 = 4172957) B4172957
theorem B2347795 : Blo 1853628 2347795 := bstep (se 1 (by rfl) ⟨1760846, by rfl⟩ : syracuseStep 2347795 = 3521693) B3521693
theorem B2782001 : Blo 1853628 2782001 := bstep (se 2 (by rfl) ⟨1043250, by rfl⟩ : syracuseStep 2782001 = 2086501) B2086501
theorem B3961649 : Blo 1853628 3961649 := bstep (se 2 (by rfl) ⟨1485618, by rfl⟩ : syracuseStep 3961649 = 2971237) B2971237
theorem B2782019 : Blo 1853628 2782019 := bstep (se 1 (by rfl) ⟨2086514, by rfl⟩ : syracuseStep 2782019 = 4173029) B4173029
theorem B2782049 : Blo 1853628 2782049 := bstep (se 2 (by rfl) ⟨1043268, by rfl⟩ : syracuseStep 2782049 = 2086537) B2086537
theorem B2782067 : Blo 1853628 2782067 := bstep (se 1 (by rfl) ⟨2086550, by rfl⟩ : syracuseStep 2782067 = 4173101) B4173101
theorem B2085763 : Blo 1853628 2085763 := bstep (se 1 (by rfl) ⟨1564322, by rfl⟩ : syracuseStep 2085763 = 3128645) B3128645
theorem B8033165 : Blo 1853628 8033165 := bstep (se 3 (by rfl) ⟨1506218, by rfl⟩ : syracuseStep 8033165 = 3012437) B3012437
theorem B2782097 : Blo 1853628 2782097 := bstep (se 2 (by rfl) ⟨1043286, by rfl⟩ : syracuseStep 2782097 = 2086573) B2086573
theorem B2782115 : Blo 1853628 2782115 := bstep (se 1 (by rfl) ⟨2086586, by rfl⟩ : syracuseStep 2782115 = 4173173) B4173173
theorem B2782145 : Blo 1853628 2782145 := bstep (se 2 (by rfl) ⟨1043304, by rfl⟩ : syracuseStep 2782145 = 2086609) B2086609
theorem B2782163 : Blo 1853628 2782163 := bstep (se 1 (by rfl) ⟨2086622, by rfl⟩ : syracuseStep 2782163 = 4173245) B4173245
theorem B2782193 : Blo 1853628 2782193 := bstep (se 2 (by rfl) ⟨1043322, by rfl⟩ : syracuseStep 2782193 = 2086645) B2086645
theorem B2782211 : Blo 1853628 2782211 := bstep (se 1 (by rfl) ⟨2086658, by rfl⟩ : syracuseStep 2782211 = 4173317) B4173317
theorem B5280785 : Blo 1853628 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B2970641 : Blo 1853628 2970641 := bstep (se 2 (by rfl) ⟨1113990, by rfl⟩ : syracuseStep 2970641 = 2227981) B2227981
theorem B2085907 : Blo 1853628 2085907 := bstep (se 1 (by rfl) ⟨1564430, by rfl⟩ : syracuseStep 2085907 = 3128861) B3128861
theorem B4174865 : Blo 1853628 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B2782241 : Blo 1853628 2782241 := bstep (se 2 (by rfl) ⟨1043340, by rfl⟩ : syracuseStep 2782241 = 2086681) B2086681
theorem B4174883 : Blo 1853628 4174883 := bstep (se 1 (by rfl) ⟨3131162, by rfl⟩ : syracuseStep 4174883 = 6262325) B6262325
theorem B2782259 : Blo 1853628 2782259 := bstep (se 1 (by rfl) ⟨2086694, by rfl⟩ : syracuseStep 2782259 = 4173389) B4173389
theorem B5944369 : Blo 1853628 5944369 := bstep (se 2 (by rfl) ⟨2229138, by rfl⟩ : syracuseStep 5944369 = 4458277) B4458277
theorem B10024013 : Blo 1853628 10024013 := bstep (se 3 (by rfl) ⟨1879502, by rfl⟩ : syracuseStep 10024013 = 3759005) B3759005
theorem B2782289 : Blo 1853628 2782289 := bstep (se 2 (by rfl) ⟨1043358, by rfl⟩ : syracuseStep 2782289 = 2086717) B2086717
theorem B2782307 : Blo 1853628 2782307 := bstep (se 1 (by rfl) ⟨2086730, by rfl⟩ : syracuseStep 2782307 = 4173461) B4173461
theorem B2782337 : Blo 1853628 2782337 := bstep (se 2 (by rfl) ⟨1043376, by rfl⟩ : syracuseStep 2782337 = 2086753) B2086753
theorem B2782355 : Blo 1853628 2782355 := bstep (se 1 (by rfl) ⟨2086766, by rfl⟩ : syracuseStep 2782355 = 4173533) B4173533
theorem B2086051 : Blo 1853628 2086051 := bstep (se 1 (by rfl) ⟨1564538, by rfl⟩ : syracuseStep 2086051 = 3129077) B3129077
theorem B2782385 : Blo 1853628 2782385 := bstep (se 2 (by rfl) ⟨1043394, by rfl⟩ : syracuseStep 2782385 = 2086789) B2086789
theorem B3568835 : Blo 1853628 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B2782403 : Blo 1853628 2782403 := bstep (se 1 (by rfl) ⟨2086802, by rfl⟩ : syracuseStep 2782403 = 4173605) B4173605
theorem B48837829 : Blo 1853628 48837829 := bstep (se 4 (by rfl) ⟨4578546, by rfl⟩ : syracuseStep 48837829 = 9157093) B9157093
theorem B2782433 : Blo 1853628 2782433 := bstep (se 2 (by rfl) ⟨1043412, by rfl⟩ : syracuseStep 2782433 = 2086825) B2086825
theorem B50771171 : Blo 1853628 50771171 := bstep (se 1 (by rfl) ⟨38078378, by rfl⟩ : syracuseStep 50771171 = 76156757) B76156757
theorem B3388643 : Blo 1853628 3388643 := bstep (se 1 (by rfl) ⟨2541482, by rfl⟩ : syracuseStep 3388643 = 5082965) B5082965
theorem B2970865 : Blo 1853628 2970865 := bstep (se 2 (by rfl) ⟨1114074, by rfl⟩ : syracuseStep 2970865 = 2228149) B2228149
theorem B2782451 : Blo 1853628 2782451 := bstep (se 1 (by rfl) ⟨2086838, by rfl⟩ : syracuseStep 2782451 = 4173677) B4173677
theorem B2348291 : Blo 1853628 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B2782481 : Blo 1853628 2782481 := bstep (se 2 (by rfl) ⟨1043430, by rfl⟩ : syracuseStep 2782481 = 2086861) B2086861
theorem B2782499 : Blo 1853628 2782499 := bstep (se 1 (by rfl) ⟨2086874, by rfl⟩ : syracuseStep 2782499 = 4173749) B4173749
theorem B4175153 : Blo 1853628 4175153 := bstep (se 2 (by rfl) ⟨1565682, by rfl⟩ : syracuseStep 4175153 = 3131365) B3131365
theorem B2086195 : Blo 1853628 2086195 := bstep (se 1 (by rfl) ⟨1564646, by rfl⟩ : syracuseStep 2086195 = 3129293) B3129293
theorem B21116213 : Blo 1853628 21116213 := bstep (se 5 (by rfl) ⟨989822, by rfl⟩ : syracuseStep 21116213 = 1979645) B1979645
theorem B2782529 : Blo 1853628 2782529 := bstep (se 2 (by rfl) ⟨1043448, by rfl⟩ : syracuseStep 2782529 = 2086897) B2086897
theorem B1979731 : Blo 1853628 1979731 := bstep (se 1 (by rfl) ⟨1484798, by rfl⟩ : syracuseStep 1979731 = 2969597) B2969597
theorem B2782547 : Blo 1853628 2782547 := bstep (se 1 (by rfl) ⟨2086910, by rfl⟩ : syracuseStep 2782547 = 4173821) B4173821
theorem B2782577 : Blo 1853628 2782577 := bstep (se 2 (by rfl) ⟨1043466, by rfl⟩ : syracuseStep 2782577 = 2086933) B2086933
theorem B2782595 : Blo 1853628 2782595 := bstep (se 1 (by rfl) ⟨2086946, by rfl⟩ : syracuseStep 2782595 = 4173893) B4173893
theorem B2782625 : Blo 1853628 2782625 := bstep (se 2 (by rfl) ⟨1043484, by rfl⟩ : syracuseStep 2782625 = 2086969) B2086969
theorem B2782643 : Blo 1853628 2782643 := bstep (se 1 (by rfl) ⟨2086982, by rfl⟩ : syracuseStep 2782643 = 4173965) B4173965
theorem B2086339 : Blo 1853628 2086339 := bstep (se 1 (by rfl) ⟨1564754, by rfl⟩ : syracuseStep 2086339 = 3129509) B3129509
theorem B2782673 : Blo 1853628 2782673 := bstep (se 2 (by rfl) ⟨1043502, by rfl⟩ : syracuseStep 2782673 = 2087005) B2087005
theorem B2782691 : Blo 1853628 2782691 := bstep (se 1 (by rfl) ⟨2087018, by rfl⟩ : syracuseStep 2782691 = 4174037) B4174037
theorem B2782721 : Blo 1853628 2782721 := bstep (se 2 (by rfl) ⟨1043520, by rfl⟩ : syracuseStep 2782721 = 2087041) B2087041
theorem B2782739 : Blo 1853628 2782739 := bstep (se 1 (by rfl) ⟨2087054, by rfl⟩ : syracuseStep 2782739 = 4174109) B4174109
theorem B2782769 : Blo 1853628 2782769 := bstep (se 2 (by rfl) ⟨1043538, by rfl⟩ : syracuseStep 2782769 = 2087077) B2087077
theorem B2782787 : Blo 1853628 2782787 := bstep (se 1 (by rfl) ⟨2087090, by rfl⟩ : syracuseStep 2782787 = 4174181) B4174181
theorem B2086483 : Blo 1853628 2086483 := bstep (se 1 (by rfl) ⟨1564862, by rfl⟩ : syracuseStep 2086483 = 3129725) B3129725
theorem B2782817 : Blo 1853628 2782817 := bstep (se 2 (by rfl) ⟨1043556, by rfl⟩ : syracuseStep 2782817 = 2087113) B2087113
theorem B6682225 : Blo 1853628 6682225 := bstep (se 2 (by rfl) ⟨2505834, by rfl⟩ : syracuseStep 6682225 = 5011669) B5011669
theorem B2782835 : Blo 1853628 2782835 := bstep (se 1 (by rfl) ⟨2087126, by rfl⟩ : syracuseStep 2782835 = 4174253) B4174253
theorem B10565261 : Blo 1853628 10565261 := bstep (se 3 (by rfl) ⟨1980986, by rfl⟩ : syracuseStep 10565261 = 3961973) B3961973
theorem B2782865 : Blo 1853628 2782865 := bstep (se 2 (by rfl) ⟨1043574, by rfl⟩ : syracuseStep 2782865 = 2087149) B2087149
theorem B2782883 : Blo 1853628 2782883 := bstep (se 1 (by rfl) ⟨2087162, by rfl⟩ : syracuseStep 2782883 = 4174325) B4174325
theorem B2782913 : Blo 1853628 2782913 := bstep (se 2 (by rfl) ⟨1043592, by rfl⟩ : syracuseStep 2782913 = 2087185) B2087185
theorem B2782931 : Blo 1853628 2782931 := bstep (se 1 (by rfl) ⟨2087198, by rfl⟩ : syracuseStep 2782931 = 4174397) B4174397
theorem B2086627 : Blo 1853628 2086627 := bstep (se 1 (by rfl) ⟨1564970, by rfl⟩ : syracuseStep 2086627 = 3129941) B3129941
theorem B2782961 : Blo 1853628 2782961 := bstep (se 2 (by rfl) ⟨1043610, by rfl⟩ : syracuseStep 2782961 = 2087221) B2087221
theorem B2782979 : Blo 1853628 2782979 := bstep (se 1 (by rfl) ⟨2087234, by rfl⟩ : syracuseStep 2782979 = 4174469) B4174469
theorem B3520273 : Blo 1853628 3520273 := bstep (se 2 (by rfl) ⟨1320102, by rfl⟩ : syracuseStep 3520273 = 2640205) B2640205
theorem B2783009 : Blo 1853628 2783009 := bstep (se 2 (by rfl) ⟨1043628, by rfl⟩ : syracuseStep 2783009 = 2087257) B2087257
theorem B2783027 : Blo 1853628 2783027 := bstep (se 1 (by rfl) ⟨2087270, by rfl⟩ : syracuseStep 2783027 = 4174541) B4174541
theorem B3012419 : Blo 1853628 3012419 := bstep (se 1 (by rfl) ⟨2259314, by rfl⟩ : syracuseStep 3012419 = 4518629) B4518629
theorem B2783057 : Blo 1853628 2783057 := bstep (se 2 (by rfl) ⟨1043646, by rfl⟩ : syracuseStep 2783057 = 2087293) B2087293
theorem B2783075 : Blo 1853628 2783075 := bstep (se 1 (by rfl) ⟨2087306, by rfl⟩ : syracuseStep 2783075 = 4174613) B4174613
theorem B6256493 : Blo 1853628 6256493 := bstep (se 3 (by rfl) ⟨1173092, by rfl⟩ : syracuseStep 6256493 = 2346185) B2346185
theorem B2086771 : Blo 1853628 2086771 := bstep (se 1 (by rfl) ⟨1565078, by rfl⟩ : syracuseStep 2086771 = 3130157) B3130157
theorem B2783105 : Blo 1853628 2783105 := bstep (se 2 (by rfl) ⟨1043664, by rfl⟩ : syracuseStep 2783105 = 2087329) B2087329
theorem B2783123 : Blo 1853628 2783123 := bstep (se 1 (by rfl) ⟨2087342, by rfl⟩ : syracuseStep 2783123 = 4174685) B4174685
theorem B6256547 : Blo 1853628 6256547 := bstep (se 1 (by rfl) ⟨4692410, by rfl⟩ : syracuseStep 6256547 = 9384821) B9384821
theorem B2783153 : Blo 1853628 2783153 := bstep (se 2 (by rfl) ⟨1043682, by rfl⟩ : syracuseStep 2783153 = 2087365) B2087365
theorem B2783171 : Blo 1853628 2783171 := bstep (se 1 (by rfl) ⟨2087378, by rfl⟩ : syracuseStep 2783171 = 4174757) B4174757
theorem B7043021 : Blo 1853628 7043021 := bstep (se 3 (by rfl) ⟨1320566, by rfl⟩ : syracuseStep 7043021 = 2641133) B2641133
theorem B2783201 : Blo 1853628 2783201 := bstep (se 2 (by rfl) ⟨1043700, by rfl⟩ : syracuseStep 2783201 = 2087401) B2087401
theorem B9385955 : Blo 1853628 9385955 := bstep (se 1 (by rfl) ⟨7039466, by rfl⟩ : syracuseStep 9385955 = 14078933) B14078933
theorem B8574947 : Blo 1853628 8574947 := bstep (se 1 (by rfl) ⟨6431210, by rfl⟩ : syracuseStep 8574947 = 12862421) B12862421
theorem B2783219 : Blo 1853628 2783219 := bstep (se 1 (by rfl) ⟨2087414, by rfl⟩ : syracuseStep 2783219 = 4174829) B4174829
theorem B2086915 : Blo 1853628 2086915 := bstep (se 1 (by rfl) ⟨1565186, by rfl⟩ : syracuseStep 2086915 = 3130373) B3130373
theorem B2783249 : Blo 1853628 2783249 := bstep (se 2 (by rfl) ⟨1043718, by rfl⟩ : syracuseStep 2783249 = 2087437) B2087437
theorem B2783267 : Blo 1853628 2783267 := bstep (se 1 (by rfl) ⟨2087450, by rfl⟩ : syracuseStep 2783267 = 4174901) B4174901
theorem B2783297 : Blo 1853628 2783297 := bstep (se 2 (by rfl) ⟨1043736, by rfl⟩ : syracuseStep 2783297 = 2087473) B2087473
theorem B3962947 : Blo 1853628 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B2783315 : Blo 1853628 2783315 := bstep (se 1 (by rfl) ⟨2087486, by rfl⟩ : syracuseStep 2783315 = 4174973) B4174973
theorem B10557539 : Blo 1853628 10557539 := bstep (se 1 (by rfl) ⟨7918154, by rfl⟩ : syracuseStep 10557539 = 15836309) B15836309
theorem B2783345 : Blo 1853628 2783345 := bstep (se 2 (by rfl) ⟨1043754, by rfl⟩ : syracuseStep 2783345 = 2087509) B2087509
theorem B2783363 : Blo 1853628 2783363 := bstep (se 1 (by rfl) ⟨2087522, by rfl⟩ : syracuseStep 2783363 = 4175045) B4175045
theorem B2087059 : Blo 1853628 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B2783393 : Blo 1853628 2783393 := bstep (se 2 (by rfl) ⟨1043772, by rfl⟩ : syracuseStep 2783393 = 2087545) B2087545
theorem B3520675 : Blo 1853628 3520675 := bstep (se 1 (by rfl) ⟨2640506, by rfl⟩ : syracuseStep 3520675 = 5281013) B5281013
theorem B6256817 : Blo 1853628 6256817 := bstep (se 2 (by rfl) ⟨2346306, by rfl⟩ : syracuseStep 6256817 = 4692613) B4692613
theorem B2783411 : Blo 1853628 2783411 := bstep (se 1 (by rfl) ⟨2087558, by rfl⟩ : syracuseStep 2783411 = 4175117) B4175117
theorem B14465221 : Blo 1853628 14465221 := bstep (se 4 (by rfl) ⟨1356114, by rfl⟩ : syracuseStep 14465221 = 2712229) B2712229
theorem B29333701 : Blo 1853628 29333701 := bstep (se 4 (by rfl) ⟨2750034, by rfl⟩ : syracuseStep 29333701 = 5500069) B5500069
theorem B3520721 : Blo 1853628 3520721 := bstep (se 2 (by rfl) ⟨1320270, by rfl⟩ : syracuseStep 3520721 = 2640541) B2640541
theorem B2783441 : Blo 1853628 2783441 := bstep (se 2 (by rfl) ⟨1043790, by rfl⟩ : syracuseStep 2783441 = 2087581) B2087581
theorem B2087203 : Blo 1853628 2087203 := bstep (se 1 (by rfl) ⟨1565402, by rfl⟩ : syracuseStep 2087203 = 3130805) B3130805
theorem B5011757 : Blo 1853628 5011757 := bstep (se 3 (by rfl) ⟨939704, by rfl⟩ : syracuseStep 5011757 = 1879409) B1879409
theorem B10025329 : Blo 1853628 10025329 := bstep (se 2 (by rfl) ⟨3759498, by rfl⟩ : syracuseStep 10025329 = 7518997) B7518997
theorem B5151089 : Blo 1853628 5151089 := bstep (se 2 (by rfl) ⟨1931658, by rfl⟩ : syracuseStep 5151089 = 3863317) B3863317
theorem B21133709 : Blo 1853628 21133709 := bstep (se 3 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 21133709 = 7925141) B7925141
theorem B4692401 : Blo 1853628 4692401 := bstep (se 2 (by rfl) ⟨1759650, by rfl⟩ : syracuseStep 4692401 = 3519301) B3519301
theorem B2087347 : Blo 1853628 2087347 := bstep (se 1 (by rfl) ⟨1565510, by rfl⟩ : syracuseStep 2087347 = 3131021) B3131021
theorem B5282243 : Blo 1853628 5282243 := bstep (se 1 (by rfl) ⟨3961682, by rfl⟩ : syracuseStep 5282243 = 7923365) B7923365
theorem B10025413 : Blo 1853628 10025413 := bstep (se 4 (by rfl) ⟨939882, by rfl⟩ : syracuseStep 10025413 = 1879765) B1879765
theorem B4692451 : Blo 1853628 4692451 := bstep (se 1 (by rfl) ⟨3519338, by rfl⟩ : syracuseStep 4692451 = 7038677) B7038677
theorem B3521009 : Blo 1853628 3521009 := bstep (se 2 (by rfl) ⟨1320378, by rfl⟩ : syracuseStep 3521009 = 2640757) B2640757
theorem B1980995 : Blo 1853628 1980995 := bstep (se 1 (by rfl) ⟨1485746, by rfl⟩ : syracuseStep 1980995 = 2971493) B2971493
theorem B2087491 : Blo 1853628 2087491 := bstep (se 1 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 2087491 = 3131237) B3131237
theorem B4692593 : Blo 1853628 4692593 := bstep (se 2 (by rfl) ⟨1759722, by rfl⟩ : syracuseStep 4692593 = 3519445) B3519445
theorem B6257357 : Blo 1853628 6257357 := bstep (se 3 (by rfl) ⟨1173254, by rfl⟩ : syracuseStep 6257357 = 2346509) B2346509
theorem B3128017 : Blo 1853628 3128017 := bstep (se 2 (by rfl) ⟨1173006, by rfl⟩ : syracuseStep 3128017 = 2346013) B2346013
theorem B3128051 : Blo 1853628 3128051 := bstep (se 1 (by rfl) ⟨2346038, by rfl⟩ : syracuseStep 3128051 = 4692077) B4692077
theorem B2226947 : Blo 1853628 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B6257411 : Blo 1853628 6257411 := bstep (se 1 (by rfl) ⟨4693058, by rfl⟩ : syracuseStep 6257411 = 9386117) B9386117
theorem B9386765 : Blo 1853628 9386765 := bstep (se 3 (by rfl) ⟨1760018, by rfl⟩ : syracuseStep 9386765 = 3520037) B3520037
theorem B3128179 : Blo 1853628 3128179 := bstep (se 1 (by rfl) ⟨2346134, by rfl⟩ : syracuseStep 3128179 = 4692269) B4692269
theorem B4455299 : Blo 1853628 4455299 := bstep (se 1 (by rfl) ⟨3341474, by rfl⟩ : syracuseStep 4455299 = 6682949) B6682949
theorem B4455395 : Blo 1853628 4455395 := bstep (se 1 (by rfl) ⟨3341546, by rfl⟩ : syracuseStep 4455395 = 6683093) B6683093
theorem B3128321 : Blo 1853628 3128321 := bstep (se 2 (by rfl) ⟨1173120, by rfl⟩ : syracuseStep 3128321 = 2346241) B2346241
theorem B3341315 : Blo 1853628 3341315 := bstep (se 1 (by rfl) ⟨2505986, by rfl⟩ : syracuseStep 3341315 = 5011973) B5011973
theorem B6257681 : Blo 1853628 6257681 := bstep (se 2 (by rfl) ⟨2346630, by rfl⟩ : syracuseStep 6257681 = 4693261) B4693261
theorem B6020173 : Blo 1853628 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B6683725 : Blo 1853628 6683725 := bstep (se 3 (by rfl) ⟨1253198, by rfl⟩ : syracuseStep 6683725 = 2506397) B2506397
theorem B3128449 : Blo 1853628 3128449 := bstep (se 2 (by rfl) ⟨1173168, by rfl⟩ : syracuseStep 3128449 = 2346337) B2346337
theorem B3128483 : Blo 1853628 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B3521731 : Blo 1853628 3521731 := bstep (se 1 (by rfl) ⟨2641298, by rfl⟩ : syracuseStep 3521731 = 5282597) B5282597
theorem B5283053 : Blo 1853628 5283053 := bstep (se 3 (by rfl) ⟨990572, by rfl⟩ : syracuseStep 5283053 = 1981145) B1981145
theorem B3128611 : Blo 1853628 3128611 := bstep (se 1 (by rfl) ⟨2346458, by rfl⟩ : syracuseStep 3128611 = 4692917) B4692917
theorem B14269765 : Blo 1853628 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B5283245 : Blo 1853628 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B3128753 : Blo 1853628 3128753 := bstep (se 2 (by rfl) ⟨1173282, by rfl⟩ : syracuseStep 3128753 = 2346565) B2346565
theorem B6258221 : Blo 1853628 6258221 := bstep (se 3 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 6258221 = 2346833) B2346833
theorem B3128881 : Blo 1853628 3128881 := bstep (se 2 (by rfl) ⟨1173330, by rfl⟩ : syracuseStep 3128881 = 2346661) B2346661
theorem B4693585 : Blo 1853628 4693585 := bstep (se 2 (by rfl) ⟨1760094, by rfl⟩ : syracuseStep 4693585 = 3520189) B3520189
theorem B3128915 : Blo 1853628 3128915 := bstep (se 1 (by rfl) ⟨2346686, by rfl⟩ : syracuseStep 3128915 = 4693373) B4693373
theorem B6258275 : Blo 1853628 6258275 := bstep (se 1 (by rfl) ⟨4693706, by rfl⟩ : syracuseStep 6258275 = 9387413) B9387413
theorem B3522179 : Blo 1853628 3522179 := bstep (se 1 (by rfl) ⟨2641634, by rfl⟩ : syracuseStep 3522179 = 5283269) B5283269
theorem B11886277 : Blo 1853628 11886277 := bstep (se 4 (by rfl) ⟨1114338, by rfl⟩ : syracuseStep 11886277 = 2228677) B2228677
theorem B3129043 : Blo 1853628 3129043 := bstep (se 1 (by rfl) ⟨2346782, by rfl⟩ : syracuseStep 3129043 = 4693565) B4693565
theorem B15236849 : Blo 1853628 15236849 := bstep (se 2 (by rfl) ⟨5713818, by rfl⟩ : syracuseStep 15236849 = 11427637) B11427637
theorem B4456241 : Blo 1853628 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B10567493 : Blo 1853628 10567493 := bstep (se 4 (by rfl) ⟨990702, by rfl⟩ : syracuseStep 10567493 = 1981405) B1981405
theorem B3129185 : Blo 1853628 3129185 := bstep (se 2 (by rfl) ⟨1173444, by rfl⟩ : syracuseStep 3129185 = 2346889) B2346889
theorem B4693859 : Blo 1853628 4693859 := bstep (se 1 (by rfl) ⟨3520394, by rfl⟩ : syracuseStep 4693859 = 7040789) B7040789
theorem B6258545 : Blo 1853628 6258545 := bstep (se 2 (by rfl) ⟨2346954, by rfl⟩ : syracuseStep 6258545 = 4693909) B4693909
theorem B3522467 : Blo 1853628 3522467 := bstep (se 1 (by rfl) ⟨2641850, by rfl⟩ : syracuseStep 3522467 = 5283701) B5283701
theorem B7618481 : Blo 1853628 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B8576945 : Blo 1853628 8576945 := bstep (se 2 (by rfl) ⟨3216354, by rfl⟩ : syracuseStep 8576945 = 6432709) B6432709
theorem B10559429 : Blo 1853628 10559429 := bstep (se 4 (by rfl) ⟨989946, by rfl⟩ : syracuseStep 10559429 = 1979893) B1979893
theorem B8912845 : Blo 1853628 8912845 := bstep (se 3 (by rfl) ⟨1671158, by rfl⟩ : syracuseStep 8912845 = 3342317) B3342317
theorem B3129313 : Blo 1853628 3129313 := bstep (se 2 (by rfl) ⟨1173492, by rfl⟩ : syracuseStep 3129313 = 2346985) B2346985
theorem B3129367 : Blo 1853628 3129367 := bstep (se 1 (by rfl) ⟨2347025, by rfl⟩ : syracuseStep 3129367 = 4694051) B4694051
theorem B4456471 : Blo 1853628 4456471 := bstep (se 1 (by rfl) ⟨3342353, by rfl⟩ : syracuseStep 4456471 = 6684707) B6684707
theorem B7921709 : Blo 1853628 7921709 := bstep (se 3 (by rfl) ⟨1485320, by rfl⟩ : syracuseStep 7921709 = 2970641) B2970641
theorem B10567745 : Blo 1853628 10567745 := bstep (se 2 (by rfl) ⟨3962904, by rfl⟩ : syracuseStep 10567745 = 7925809) B7925809
theorem B5283929 : Blo 1853628 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B17817731 : Blo 1853628 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B4694233 : Blo 1853628 4694233 := bstep (se 2 (by rfl) ⟨1760337, by rfl⟩ : syracuseStep 4694233 = 3520675) B3520675
theorem B7045451 : Blo 1853628 7045451 := bstep (se 1 (by rfl) ⟨5284088, by rfl⟩ : syracuseStep 7045451 = 10568177) B10568177
theorem B14090597 : Blo 1853628 14090597 := bstep (se 4 (by rfl) ⟨1320993, by rfl⟩ : syracuseStep 14090597 = 2641987) B2641987
theorem B2113943 : Blo 1853628 2113943 := bstep (se 1 (by rfl) ⟨1585457, by rfl⟩ : syracuseStep 2113943 = 3170915) B3170915
theorem B3760627 : Blo 1853628 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B5014091 : Blo 1853628 5014091 := bstep (se 1 (by rfl) ⟨3760568, by rfl⟩ : syracuseStep 5014091 = 7521137) B7521137
theorem B135389789 : Blo 1853628 135389789 := bstep (se 3 (by rfl) ⟨25385585, by rfl⟩ : syracuseStep 135389789 = 50771171) B50771171
theorem B3129995 : Blo 1853628 3129995 := bstep (se 1 (by rfl) ⟨2347496, by rfl⟩ : syracuseStep 3129995 = 4694993) B4694993
theorem B7922393 : Blo 1853628 7922393 := bstep (se 2 (by rfl) ⟨2970897, by rfl⟩ : syracuseStep 7922393 = 5941795) B5941795
theorem B14082821 : Blo 1853628 14082821 := bstep (se 4 (by rfl) ⟨1320264, by rfl⟩ : syracuseStep 14082821 = 2640529) B2640529
theorem B3130123 : Blo 1853628 3130123 := bstep (se 1 (by rfl) ⟨2347592, by rfl⟩ : syracuseStep 3130123 = 4695185) B4695185
theorem B14091083 : Blo 1853628 14091083 := bstep (se 1 (by rfl) ⟨10568312, by rfl⟩ : syracuseStep 14091083 = 21136625) B21136625
theorem B6685571 : Blo 1853628 6685571 := bstep (se 1 (by rfl) ⟨5014178, by rfl⟩ : syracuseStep 6685571 = 10028357) B10028357
theorem B3130265 : Blo 1853628 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B4170689 : Blo 1853628 4170689 := bstep (se 2 (by rfl) ⟨1564008, by rfl⟩ : syracuseStep 4170689 = 3128017) B3128017
theorem B8463325 : Blo 1853628 8463325 := bstep (se 3 (by rfl) ⟨1586873, by rfl⟩ : syracuseStep 8463325 = 3173747) B3173747
theorem B33850385 : Blo 1853628 33850385 := bstep (se 2 (by rfl) ⟨12693894, by rfl⟩ : syracuseStep 33850385 = 25387789) B25387789
theorem B3130393 : Blo 1853628 3130393 := bstep (se 2 (by rfl) ⟨1173897, by rfl⟩ : syracuseStep 3130393 = 2347795) B2347795
theorem B81331235 : Blo 1853628 81331235 := bstep (se 1 (by rfl) ⟨60998426, by rfl⟩ : syracuseStep 81331235 = 121996853) B121996853
theorem B6259787 : Blo 1853628 6259787 := bstep (se 1 (by rfl) ⟨4694840, by rfl⟩ : syracuseStep 6259787 = 9389681) B9389681
theorem B2507863 : Blo 1853628 2507863 := bstep (se 1 (by rfl) ⟨1880897, by rfl⟩ : syracuseStep 2507863 = 3761795) B3761795
theorem B4170905 : Blo 1853628 4170905 := bstep (se 2 (by rfl) ⟨1564089, by rfl⟩ : syracuseStep 4170905 = 3128179) B3128179
theorem B2008279 : Blo 1853628 2008279 := bstep (se 1 (by rfl) ⟨1506209, by rfl⟩ : syracuseStep 2008279 = 3012419) B3012419
theorem B2712793 : Blo 1853628 2712793 := bstep (se 2 (by rfl) ⟨1017297, by rfl⟩ : syracuseStep 2712793 = 2034595) B2034595
theorem B4170995 : Blo 1853628 4170995 := bstep (se 1 (by rfl) ⟨3128246, by rfl⟩ : syracuseStep 4170995 = 6256493) B6256493
theorem B4171031 : Blo 1853628 4171031 := bstep (se 1 (by rfl) ⟨3128273, by rfl⟩ : syracuseStep 4171031 = 6256547) B6256547
theorem B9389357 : Blo 1853628 9389357 := bstep (se 3 (by rfl) ⟨1760504, by rfl⟩ : syracuseStep 9389357 = 3521009) B3521009
theorem B6341939 : Blo 1853628 6341939 := bstep (se 1 (by rfl) ⟨4756454, by rfl⟩ : syracuseStep 6341939 = 9512909) B9512909
theorem B4695347 : Blo 1853628 4695347 := bstep (se 1 (by rfl) ⟨3521510, by rfl⟩ : syracuseStep 4695347 = 7043021) B7043021
theorem B6260057 : Blo 1853628 6260057 := bstep (se 2 (by rfl) ⟨2347521, by rfl⟩ : syracuseStep 6260057 = 4695043) B4695043
theorem B4015475 : Blo 1853628 4015475 := bstep (se 1 (by rfl) ⟨3011606, by rfl⟩ : syracuseStep 4015475 = 6023213) B6023213
theorem B7038359 : Blo 1853628 7038359 := bstep (se 1 (by rfl) ⟨5278769, by rfl⟩ : syracuseStep 7038359 = 10557539) B10557539
theorem B4171211 : Blo 1853628 4171211 := bstep (se 1 (by rfl) ⟨3128408, by rfl⟩ : syracuseStep 4171211 = 6256817) B6256817
theorem B4171265 : Blo 1853628 4171265 := bstep (se 2 (by rfl) ⟨1564224, by rfl⟩ : syracuseStep 4171265 = 3128449) B3128449
theorem B21120587 : Blo 1853628 21120587 := bstep (se 1 (by rfl) ⟨15840440, by rfl⟩ : syracuseStep 21120587 = 31680881) B31680881
theorem B3434059 : Blo 1853628 3434059 := bstep (se 1 (by rfl) ⟨2575544, by rfl⟩ : syracuseStep 3434059 = 5151089) B5151089
theorem B3130967 : Blo 1853628 3130967 := bstep (se 1 (by rfl) ⟨2348225, by rfl⟩ : syracuseStep 3130967 = 4696451) B4696451
theorem B4695641 : Blo 1853628 4695641 := bstep (se 2 (by rfl) ⟨1760865, by rfl⟩ : syracuseStep 4695641 = 3521731) B3521731
theorem B3131095 : Blo 1853628 3131095 := bstep (se 1 (by rfl) ⟨2348321, by rfl⟩ : syracuseStep 3131095 = 4696643) B4696643
theorem B4171481 : Blo 1853628 4171481 := bstep (se 2 (by rfl) ⟨1564305, by rfl⟩ : syracuseStep 4171481 = 3128611) B3128611
theorem B2639641 : Blo 1853628 2639641 := bstep (se 2 (by rfl) ⟨989865, by rfl⟩ : syracuseStep 2639641 = 1979731) B1979731
theorem B22554413 : Blo 1853628 22554413 := bstep (se 3 (by rfl) ⟨4228952, by rfl⟩ : syracuseStep 22554413 = 8457905) B8457905
theorem B4171571 : Blo 1853628 4171571 := bstep (se 1 (by rfl) ⟨3128678, by rfl⟩ : syracuseStep 4171571 = 6257357) B6257357
theorem B4171607 : Blo 1853628 4171607 := bstep (se 1 (by rfl) ⟨3128705, by rfl⟩ : syracuseStep 4171607 = 6257411) B6257411
theorem B5080925 : Blo 1853628 5080925 := bstep (se 3 (by rfl) ⟨952673, by rfl⟩ : syracuseStep 5080925 = 1905347) B1905347
theorem B2115499 : Blo 1853628 2115499 := bstep (se 1 (by rfl) ⟨1586624, by rfl⟩ : syracuseStep 2115499 = 3173249) B3173249
theorem B5638081 : Blo 1853628 5638081 := bstep (se 2 (by rfl) ⟨2114280, by rfl⟩ : syracuseStep 5638081 = 4228561) B4228561
theorem B2541515 : Blo 1853628 2541515 := bstep (se 1 (by rfl) ⟨1906136, by rfl⟩ : syracuseStep 2541515 = 3812273) B3812273
theorem B4171787 : Blo 1853628 4171787 := bstep (se 1 (by rfl) ⟨3128840, by rfl⟩ : syracuseStep 4171787 = 6257681) B6257681
theorem B6260759 : Blo 1853628 6260759 := bstep (se 1 (by rfl) ⟨4695569, by rfl⟩ : syracuseStep 6260759 = 9391139) B9391139
theorem B4171841 : Blo 1853628 4171841 := bstep (se 2 (by rfl) ⟨1564440, by rfl⟩ : syracuseStep 4171841 = 3128881) B3128881
theorem B1853643 : Blo 1853628 1853643 := bstep (se 1 (by rfl) ⟨1390232, by rfl⟩ : syracuseStep 1853643 = 2780465) B2780465
theorem B2033867 : Blo 1853628 2033867 := bstep (se 1 (by rfl) ⟨1525400, by rfl⟩ : syracuseStep 2033867 = 3050801) B3050801
theorem B1853655 : Blo 1853628 1853655 := bstep (se 1 (by rfl) ⟨1390241, by rfl⟩ : syracuseStep 1853655 = 2780483) B2780483
theorem B1853675 : Blo 1853628 1853675 := bstep (se 1 (by rfl) ⟨1390256, by rfl⟩ : syracuseStep 1853675 = 2780513) B2780513
theorem B1853687 : Blo 1853628 1853687 := bstep (se 1 (by rfl) ⟨1390265, by rfl⟩ : syracuseStep 1853687 = 2780531) B2780531
theorem B1853707 : Blo 1853628 1853707 := bstep (se 1 (by rfl) ⟨1390280, by rfl⟩ : syracuseStep 1853707 = 2780561) B2780561
theorem B1853719 : Blo 1853628 1853719 := bstep (se 1 (by rfl) ⟨1390289, by rfl⟩ : syracuseStep 1853719 = 2780579) B2780579
theorem B4172057 : Blo 1853628 4172057 := bstep (se 2 (by rfl) ⟨1564521, by rfl⟩ : syracuseStep 4172057 = 3129043) B3129043
theorem B1853739 : Blo 1853628 1853739 := bstep (se 1 (by rfl) ⟨1390304, by rfl⟩ : syracuseStep 1853739 = 2780609) B2780609
theorem B1853751 : Blo 1853628 1853751 := bstep (se 1 (by rfl) ⟨1390313, by rfl⟩ : syracuseStep 1853751 = 2780627) B2780627
theorem B1853771 : Blo 1853628 1853771 := bstep (se 1 (by rfl) ⟨1390328, by rfl⟩ : syracuseStep 1853771 = 2780657) B2780657
theorem B1853783 : Blo 1853628 1853783 := bstep (se 1 (by rfl) ⟨1390337, by rfl⟩ : syracuseStep 1853783 = 2780675) B2780675
theorem B8456537 : Blo 1853628 8456537 := bstep (se 2 (by rfl) ⟨3171201, by rfl⟩ : syracuseStep 8456537 = 6342403) B6342403
theorem B1853803 : Blo 1853628 1853803 := bstep (se 1 (by rfl) ⟨1390352, by rfl⟩ : syracuseStep 1853803 = 2780705) B2780705
theorem B4172147 : Blo 1853628 4172147 := bstep (se 1 (by rfl) ⟨3129110, by rfl⟩ : syracuseStep 4172147 = 6258221) B6258221
theorem B1853815 : Blo 1853628 1853815 := bstep (se 1 (by rfl) ⟨1390361, by rfl⟩ : syracuseStep 1853815 = 2780723) B2780723
theorem B1853835 : Blo 1853628 1853835 := bstep (se 1 (by rfl) ⟨1390376, by rfl⟩ : syracuseStep 1853835 = 2780753) B2780753
theorem B1853847 : Blo 1853628 1853847 := bstep (se 1 (by rfl) ⟨1390385, by rfl⟩ : syracuseStep 1853847 = 2780771) B2780771
theorem B4172183 : Blo 1853628 4172183 := bstep (se 1 (by rfl) ⟨3129137, by rfl⟩ : syracuseStep 4172183 = 6258275) B6258275
theorem B1853867 : Blo 1853628 1853867 := bstep (se 1 (by rfl) ⟨1390400, by rfl⟩ : syracuseStep 1853867 = 2780801) B2780801
theorem B30083507 : Blo 1853628 30083507 := bstep (se 1 (by rfl) ⟨22562630, by rfl⟩ : syracuseStep 30083507 = 45125261) B45125261
theorem B1853879 : Blo 1853628 1853879 := bstep (se 1 (by rfl) ⟨1390409, by rfl⟩ : syracuseStep 1853879 = 2780819) B2780819
theorem B1853899 : Blo 1853628 1853899 := bstep (se 1 (by rfl) ⟨1390424, by rfl⟩ : syracuseStep 1853899 = 2780849) B2780849
theorem B1853911 : Blo 1853628 1853911 := bstep (se 1 (by rfl) ⟨1390433, by rfl⟩ : syracuseStep 1853911 = 2780867) B2780867
theorem B1853931 : Blo 1853628 1853931 := bstep (se 1 (by rfl) ⟨1390448, by rfl⟩ : syracuseStep 1853931 = 2780897) B2780897
theorem B1853943 : Blo 1853628 1853943 := bstep (se 1 (by rfl) ⟨1390457, by rfl⟩ : syracuseStep 1853943 = 2780915) B2780915
theorem B1853963 : Blo 1853628 1853963 := bstep (se 1 (by rfl) ⟨1390472, by rfl⟩ : syracuseStep 1853963 = 2780945) B2780945
theorem B1853975 : Blo 1853628 1853975 := bstep (se 1 (by rfl) ⟨1390481, by rfl⟩ : syracuseStep 1853975 = 2780963) B2780963
theorem B1853995 : Blo 1853628 1853995 := bstep (se 1 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 1853995 = 2780993) B2780993
theorem B6261299 : Blo 1853628 6261299 := bstep (se 1 (by rfl) ⟨4695974, by rfl⟩ : syracuseStep 6261299 = 9391949) B9391949
theorem B1854007 : Blo 1853628 1854007 := bstep (se 1 (by rfl) ⟨1390505, by rfl⟩ : syracuseStep 1854007 = 2781011) B2781011
theorem B1854027 : Blo 1853628 1854027 := bstep (se 1 (by rfl) ⟨1390520, by rfl⟩ : syracuseStep 1854027 = 2781041) B2781041
theorem B4172363 : Blo 1853628 4172363 := bstep (se 1 (by rfl) ⟨3129272, by rfl⟩ : syracuseStep 4172363 = 6258545) B6258545
theorem B1854039 : Blo 1853628 1854039 := bstep (se 1 (by rfl) ⟨1390529, by rfl⟩ : syracuseStep 1854039 = 2781059) B2781059
theorem B1854059 : Blo 1853628 1854059 := bstep (se 1 (by rfl) ⟨1390544, by rfl⟩ : syracuseStep 1854059 = 2781089) B2781089
theorem B1854071 : Blo 1853628 1854071 := bstep (se 1 (by rfl) ⟨1390553, by rfl⟩ : syracuseStep 1854071 = 2781107) B2781107
theorem B4172417 : Blo 1853628 4172417 := bstep (se 2 (by rfl) ⟨1564656, by rfl⟩ : syracuseStep 4172417 = 3129313) B3129313
theorem B7039619 : Blo 1853628 7039619 := bstep (se 1 (by rfl) ⟨5279714, by rfl⟩ : syracuseStep 7039619 = 10559429) B10559429
theorem B1854091 : Blo 1853628 1854091 := bstep (se 1 (by rfl) ⟨1390568, by rfl⟩ : syracuseStep 1854091 = 2781137) B2781137
theorem B1854103 : Blo 1853628 1854103 := bstep (se 1 (by rfl) ⟨1390577, by rfl⟩ : syracuseStep 1854103 = 2781155) B2781155
theorem B10029719 : Blo 1853628 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B1854123 : Blo 1853628 1854123 := bstep (se 1 (by rfl) ⟨1390592, by rfl⟩ : syracuseStep 1854123 = 2781185) B2781185
theorem B5638835 : Blo 1853628 5638835 := bstep (se 1 (by rfl) ⟨4229126, by rfl⟩ : syracuseStep 5638835 = 8458253) B8458253
theorem B1854135 : Blo 1853628 1854135 := bstep (se 1 (by rfl) ⟨1390601, by rfl⟩ : syracuseStep 1854135 = 2781203) B2781203
theorem B1854155 : Blo 1853628 1854155 := bstep (se 1 (by rfl) ⟨1390616, by rfl⟩ : syracuseStep 1854155 = 2781233) B2781233
theorem B1854167 : Blo 1853628 1854167 := bstep (se 1 (by rfl) ⟨1390625, by rfl⟩ : syracuseStep 1854167 = 2781251) B2781251
theorem B3959513 : Blo 1853628 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B1854187 : Blo 1853628 1854187 := bstep (se 1 (by rfl) ⟨1390640, by rfl⟩ : syracuseStep 1854187 = 2781281) B2781281
theorem B1854199 : Blo 1853628 1854199 := bstep (se 1 (by rfl) ⟨1390649, by rfl⟩ : syracuseStep 1854199 = 2781299) B2781299
theorem B1854219 : Blo 1853628 1854219 := bstep (se 1 (by rfl) ⟨1390664, by rfl⟩ : syracuseStep 1854219 = 2781329) B2781329
theorem B1854231 : Blo 1853628 1854231 := bstep (se 1 (by rfl) ⟨1390673, by rfl⟩ : syracuseStep 1854231 = 2781347) B2781347
theorem B4229911 : Blo 1853628 4229911 := bstep (se 1 (by rfl) ⟨3172433, by rfl⟩ : syracuseStep 4229911 = 6344867) B6344867
theorem B1854251 : Blo 1853628 1854251 := bstep (se 1 (by rfl) ⟨1390688, by rfl⟩ : syracuseStep 1854251 = 2781377) B2781377
theorem B1854263 : Blo 1853628 1854263 := bstep (se 1 (by rfl) ⟨1390697, by rfl⟩ : syracuseStep 1854263 = 2781395) B2781395
theorem B6261569 : Blo 1853628 6261569 := bstep (se 2 (by rfl) ⟨2348088, by rfl⟩ : syracuseStep 6261569 = 4696177) B4696177
theorem B1854283 : Blo 1853628 1854283 := bstep (se 1 (by rfl) ⟨1390712, by rfl⟩ : syracuseStep 1854283 = 2781425) B2781425
theorem B1854295 : Blo 1853628 1854295 := bstep (se 1 (by rfl) ⟨1390721, by rfl⟩ : syracuseStep 1854295 = 2781443) B2781443
theorem B5278553 : Blo 1853628 5278553 := bstep (se 2 (by rfl) ⟨1979457, by rfl⟩ : syracuseStep 5278553 = 3958915) B3958915
theorem B4172633 : Blo 1853628 4172633 := bstep (se 2 (by rfl) ⟨1564737, by rfl⟩ : syracuseStep 4172633 = 3129475) B3129475
theorem B1854315 : Blo 1853628 1854315 := bstep (se 1 (by rfl) ⟨1390736, by rfl⟩ : syracuseStep 1854315 = 2781473) B2781473
theorem B1854327 : Blo 1853628 1854327 := bstep (se 1 (by rfl) ⟨1390745, by rfl⟩ : syracuseStep 1854327 = 2781491) B2781491
theorem B1854347 : Blo 1853628 1854347 := bstep (se 1 (by rfl) ⟨1390760, by rfl⟩ : syracuseStep 1854347 = 2781521) B2781521
theorem B1854359 : Blo 1853628 1854359 := bstep (se 1 (by rfl) ⟨1390769, by rfl⟩ : syracuseStep 1854359 = 2781539) B2781539
theorem B1854379 : Blo 1853628 1854379 := bstep (se 1 (by rfl) ⟨1390784, by rfl⟩ : syracuseStep 1854379 = 2781569) B2781569
theorem B4172723 : Blo 1853628 4172723 := bstep (se 1 (by rfl) ⟨3129542, by rfl⟩ : syracuseStep 4172723 = 6259085) B6259085
theorem B1854391 : Blo 1853628 1854391 := bstep (se 1 (by rfl) ⟨1390793, by rfl⟩ : syracuseStep 1854391 = 2781587) B2781587
theorem B1854411 : Blo 1853628 1854411 := bstep (se 1 (by rfl) ⟨1390808, by rfl⟩ : syracuseStep 1854411 = 2781617) B2781617
theorem B1854423 : Blo 1853628 1854423 := bstep (se 1 (by rfl) ⟨1390817, by rfl⟩ : syracuseStep 1854423 = 2781635) B2781635
theorem B4172759 : Blo 1853628 4172759 := bstep (se 1 (by rfl) ⟨3129569, by rfl⟩ : syracuseStep 4172759 = 6259139) B6259139
theorem B50760665 : Blo 1853628 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B1854443 : Blo 1853628 1854443 := bstep (se 1 (by rfl) ⟨1390832, by rfl⟩ : syracuseStep 1854443 = 2781665) B2781665
theorem B1854455 : Blo 1853628 1854455 := bstep (se 1 (by rfl) ⟨1390841, by rfl⟩ : syracuseStep 1854455 = 2781683) B2781683
theorem B1854475 : Blo 1853628 1854475 := bstep (se 1 (by rfl) ⟨1390856, by rfl⟩ : syracuseStep 1854475 = 2781713) B2781713
theorem B1854487 : Blo 1853628 1854487 := bstep (se 1 (by rfl) ⟨1390865, by rfl⟩ : syracuseStep 1854487 = 2781731) B2781731
theorem B1854507 : Blo 1853628 1854507 := bstep (se 1 (by rfl) ⟨1390880, by rfl⟩ : syracuseStep 1854507 = 2781761) B2781761
theorem B1854519 : Blo 1853628 1854519 := bstep (se 1 (by rfl) ⟨1390889, by rfl⟩ : syracuseStep 1854519 = 2781779) B2781779
theorem B32107589 : Blo 1853628 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B1854539 : Blo 1853628 1854539 := bstep (se 1 (by rfl) ⟨1390904, by rfl⟩ : syracuseStep 1854539 = 2781809) B2781809
theorem B1854551 : Blo 1853628 1854551 := bstep (se 1 (by rfl) ⟨1390913, by rfl⟩ : syracuseStep 1854551 = 2781827) B2781827
theorem B1854571 : Blo 1853628 1854571 := bstep (se 1 (by rfl) ⟨1390928, by rfl⟩ : syracuseStep 1854571 = 2781857) B2781857
theorem B3959923 : Blo 1853628 3959923 := bstep (se 1 (by rfl) ⟨2969942, by rfl⟩ : syracuseStep 3959923 = 5939885) B5939885
theorem B1854583 : Blo 1853628 1854583 := bstep (se 1 (by rfl) ⟨1390937, by rfl⟩ : syracuseStep 1854583 = 2781875) B2781875
theorem B14085251 : Blo 1853628 14085251 := bstep (se 1 (by rfl) ⟨10563938, by rfl⟩ : syracuseStep 14085251 = 21127877) B21127877
theorem B1854603 : Blo 1853628 1854603 := bstep (se 1 (by rfl) ⟨1390952, by rfl⟩ : syracuseStep 1854603 = 2781905) B2781905
theorem B4172939 : Blo 1853628 4172939 := bstep (se 1 (by rfl) ⟨3129704, by rfl⟩ : syracuseStep 4172939 = 6259409) B6259409
theorem B5278871 : Blo 1853628 5278871 := bstep (se 1 (by rfl) ⟨3959153, by rfl⟩ : syracuseStep 5278871 = 7918307) B7918307
theorem B1854615 : Blo 1853628 1854615 := bstep (se 1 (by rfl) ⟨1390961, by rfl⟩ : syracuseStep 1854615 = 2781923) B2781923
theorem B1854635 : Blo 1853628 1854635 := bstep (se 1 (by rfl) ⟨1390976, by rfl⟩ : syracuseStep 1854635 = 2781953) B2781953
theorem B1854647 : Blo 1853628 1854647 := bstep (se 1 (by rfl) ⟨1390985, by rfl⟩ : syracuseStep 1854647 = 2781971) B2781971
theorem B4172993 : Blo 1853628 4172993 := bstep (se 2 (by rfl) ⟨1564872, by rfl⟩ : syracuseStep 4172993 = 3129745) B3129745
theorem B1854667 : Blo 1853628 1854667 := bstep (se 1 (by rfl) ⟨1391000, by rfl⟩ : syracuseStep 1854667 = 2782001) B2782001
theorem B2641099 : Blo 1853628 2641099 := bstep (se 1 (by rfl) ⟨1980824, by rfl⟩ : syracuseStep 2641099 = 3961649) B3961649
theorem B1854679 : Blo 1853628 1854679 := bstep (se 1 (by rfl) ⟨1391009, by rfl⟩ : syracuseStep 1854679 = 2782019) B2782019
theorem B1854699 : Blo 1853628 1854699 := bstep (se 1 (by rfl) ⟨1391024, by rfl⟩ : syracuseStep 1854699 = 2782049) B2782049
theorem B1854711 : Blo 1853628 1854711 := bstep (se 1 (by rfl) ⟨1391033, by rfl⟩ : syracuseStep 1854711 = 2782067) B2782067
theorem B1854731 : Blo 1853628 1854731 := bstep (se 1 (by rfl) ⟨1391048, by rfl⟩ : syracuseStep 1854731 = 2782097) B2782097
theorem B1854743 : Blo 1853628 1854743 := bstep (se 1 (by rfl) ⟨1391057, by rfl⟩ : syracuseStep 1854743 = 2782115) B2782115
theorem B3812633 : Blo 1853628 3812633 := bstep (se 2 (by rfl) ⟨1429737, by rfl⟩ : syracuseStep 3812633 = 2859475) B2859475
theorem B1854763 : Blo 1853628 1854763 := bstep (se 1 (by rfl) ⟨1391072, by rfl⟩ : syracuseStep 1854763 = 2782145) B2782145
theorem B1854775 : Blo 1853628 1854775 := bstep (se 1 (by rfl) ⟨1391081, by rfl⟩ : syracuseStep 1854775 = 2782163) B2782163
theorem B1854795 : Blo 1853628 1854795 := bstep (se 1 (by rfl) ⟨1391096, by rfl⟩ : syracuseStep 1854795 = 2782193) B2782193
theorem B1854807 : Blo 1853628 1854807 := bstep (se 1 (by rfl) ⟨1391105, by rfl⟩ : syracuseStep 1854807 = 2782211) B2782211
theorem B6262109 : Blo 1853628 6262109 := bstep (se 3 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 6262109 = 2348291) B2348291
theorem B1854827 : Blo 1853628 1854827 := bstep (se 1 (by rfl) ⟨1391120, by rfl⟩ : syracuseStep 1854827 = 2782241) B2782241
theorem B3960179 : Blo 1853628 3960179 := bstep (se 1 (by rfl) ⟨2970134, by rfl⟩ : syracuseStep 3960179 = 5940269) B5940269
theorem B1854839 : Blo 1853628 1854839 := bstep (se 1 (by rfl) ⟨1391129, by rfl⟩ : syracuseStep 1854839 = 2782259) B2782259
theorem B2780555 : Blo 1853628 2780555 := bstep (se 1 (by rfl) ⟨2085416, by rfl⟩ : syracuseStep 2780555 = 4170833) B4170833
theorem B1854859 : Blo 1853628 1854859 := bstep (se 1 (by rfl) ⟨1391144, by rfl⟩ : syracuseStep 1854859 = 2782289) B2782289
theorem B2780567 : Blo 1853628 2780567 := bstep (se 1 (by rfl) ⟨2085425, by rfl⟩ : syracuseStep 2780567 = 4170851) B4170851
theorem B1854871 : Blo 1853628 1854871 := bstep (se 1 (by rfl) ⟨1391153, by rfl⟩ : syracuseStep 1854871 = 2782307) B2782307
theorem B4173209 : Blo 1853628 4173209 := bstep (se 2 (by rfl) ⟨1564953, by rfl⟩ : syracuseStep 4173209 = 3129907) B3129907
theorem B1854891 : Blo 1853628 1854891 := bstep (se 1 (by rfl) ⟨1391168, by rfl⟩ : syracuseStep 1854891 = 2782337) B2782337
theorem B1854903 : Blo 1853628 1854903 := bstep (se 1 (by rfl) ⟨1391177, by rfl⟩ : syracuseStep 1854903 = 2782355) B2782355
theorem B1854923 : Blo 1853628 1854923 := bstep (se 1 (by rfl) ⟨1391192, by rfl⟩ : syracuseStep 1854923 = 2782385) B2782385
theorem B2379223 : Blo 1853628 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B1854935 : Blo 1853628 1854935 := bstep (se 1 (by rfl) ⟨1391201, by rfl⟩ : syracuseStep 1854935 = 2782403) B2782403
theorem B2780633 : Blo 1853628 2780633 := bstep (se 2 (by rfl) ⟨1042737, by rfl⟩ : syracuseStep 2780633 = 2085475) B2085475
theorem B1854955 : Blo 1853628 1854955 := bstep (se 1 (by rfl) ⟨1391216, by rfl⟩ : syracuseStep 1854955 = 2782433) B2782433
theorem B4173299 : Blo 1853628 4173299 := bstep (se 1 (by rfl) ⟨3129974, by rfl⟩ : syracuseStep 4173299 = 6259949) B6259949
theorem B1854967 : Blo 1853628 1854967 := bstep (se 1 (by rfl) ⟨1391225, by rfl⟩ : syracuseStep 1854967 = 2782451) B2782451
theorem B1854987 : Blo 1853628 1854987 := bstep (se 1 (by rfl) ⟨1391240, by rfl⟩ : syracuseStep 1854987 = 2782481) B2782481
theorem B4173335 : Blo 1853628 4173335 := bstep (se 1 (by rfl) ⟨3130001, by rfl⟩ : syracuseStep 4173335 = 6260003) B6260003
theorem B1854999 : Blo 1853628 1854999 := bstep (se 1 (by rfl) ⟨1391249, by rfl⟩ : syracuseStep 1854999 = 2782499) B2782499
theorem B14077475 : Blo 1853628 14077475 := bstep (se 1 (by rfl) ⟨10558106, by rfl⟩ : syracuseStep 14077475 = 21116213) B21116213
theorem B1855019 : Blo 1853628 1855019 := bstep (se 1 (by rfl) ⟨1391264, by rfl⟩ : syracuseStep 1855019 = 2782529) B2782529
theorem B1855031 : Blo 1853628 1855031 := bstep (se 1 (by rfl) ⟨1391273, by rfl⟩ : syracuseStep 1855031 = 2782547) B2782547
theorem B2780747 : Blo 1853628 2780747 := bstep (se 1 (by rfl) ⟨2085560, by rfl⟩ : syracuseStep 2780747 = 4171121) B4171121
theorem B1855051 : Blo 1853628 1855051 := bstep (se 1 (by rfl) ⟨1391288, by rfl⟩ : syracuseStep 1855051 = 2782577) B2782577
theorem B2780759 : Blo 1853628 2780759 := bstep (se 1 (by rfl) ⟨2085569, by rfl⟩ : syracuseStep 2780759 = 4171139) B4171139
theorem B1855063 : Blo 1853628 1855063 := bstep (se 1 (by rfl) ⟨1391297, by rfl⟩ : syracuseStep 1855063 = 2782595) B2782595
theorem B1855083 : Blo 1853628 1855083 := bstep (se 1 (by rfl) ⟨1391312, by rfl⟩ : syracuseStep 1855083 = 2782625) B2782625
theorem B1855095 : Blo 1853628 1855095 := bstep (se 1 (by rfl) ⟨1391321, by rfl⟩ : syracuseStep 1855095 = 2782643) B2782643
theorem B1855115 : Blo 1853628 1855115 := bstep (se 1 (by rfl) ⟨1391336, by rfl⟩ : syracuseStep 1855115 = 2782673) B2782673
theorem B1855127 : Blo 1853628 1855127 := bstep (se 1 (by rfl) ⟨1391345, by rfl⟩ : syracuseStep 1855127 = 2782691) B2782691
theorem B2780825 : Blo 1853628 2780825 := bstep (se 2 (by rfl) ⟨1042809, by rfl⟩ : syracuseStep 2780825 = 2085619) B2085619
theorem B1855147 : Blo 1853628 1855147 := bstep (se 1 (by rfl) ⟨1391360, by rfl⟩ : syracuseStep 1855147 = 2782721) B2782721
theorem B1855159 : Blo 1853628 1855159 := bstep (se 1 (by rfl) ⟨1391369, by rfl⟩ : syracuseStep 1855159 = 2782739) B2782739
theorem B77147845 : Blo 1853628 77147845 := bstep (se 4 (by rfl) ⟨7232610, by rfl⟩ : syracuseStep 77147845 = 14465221) B14465221
theorem B156446405 : Blo 1853628 156446405 := bstep (se 4 (by rfl) ⟨14666850, by rfl⟩ : syracuseStep 156446405 = 29333701) B29333701
theorem B4173515 : Blo 1853628 4173515 := bstep (se 1 (by rfl) ⟨3130136, by rfl⟩ : syracuseStep 4173515 = 6260273) B6260273
theorem B1855179 : Blo 1853628 1855179 := bstep (se 1 (by rfl) ⟨1391384, by rfl⟩ : syracuseStep 1855179 = 2782769) B2782769
theorem B1855191 : Blo 1853628 1855191 := bstep (se 1 (by rfl) ⟨1391393, by rfl⟩ : syracuseStep 1855191 = 2782787) B2782787
theorem B1855211 : Blo 1853628 1855211 := bstep (se 1 (by rfl) ⟨1391408, by rfl⟩ : syracuseStep 1855211 = 2782817) B2782817
theorem B1855223 : Blo 1853628 1855223 := bstep (se 1 (by rfl) ⟨1391417, by rfl⟩ : syracuseStep 1855223 = 2782835) B2782835
theorem B4173569 : Blo 1853628 4173569 := bstep (se 2 (by rfl) ⟨1565088, by rfl⟩ : syracuseStep 4173569 = 3130177) B3130177
theorem B2780939 : Blo 1853628 2780939 := bstep (se 1 (by rfl) ⟨2085704, by rfl⟩ : syracuseStep 2780939 = 4171409) B4171409
theorem B1855243 : Blo 1853628 1855243 := bstep (se 1 (by rfl) ⟨1391432, by rfl⟩ : syracuseStep 1855243 = 2782865) B2782865
theorem B2780951 : Blo 1853628 2780951 := bstep (se 1 (by rfl) ⟨2085713, by rfl⟩ : syracuseStep 2780951 = 4171427) B4171427
theorem B1855255 : Blo 1853628 1855255 := bstep (se 1 (by rfl) ⟨1391441, by rfl⟩ : syracuseStep 1855255 = 2782883) B2782883
theorem B1855275 : Blo 1853628 1855275 := bstep (se 1 (by rfl) ⟨1391456, by rfl⟩ : syracuseStep 1855275 = 2782913) B2782913
theorem B1855287 : Blo 1853628 1855287 := bstep (se 1 (by rfl) ⟨1391465, by rfl⟩ : syracuseStep 1855287 = 2782931) B2782931
theorem B1855307 : Blo 1853628 1855307 := bstep (se 1 (by rfl) ⟨1391480, by rfl⟩ : syracuseStep 1855307 = 2782961) B2782961
theorem B2781017 : Blo 1853628 2781017 := bstep (se 2 (by rfl) ⟨1042881, by rfl⟩ : syracuseStep 2781017 = 2085763) B2085763
theorem B1855319 : Blo 1853628 1855319 := bstep (se 1 (by rfl) ⟨1391489, by rfl⟩ : syracuseStep 1855319 = 2782979) B2782979
theorem B1855339 : Blo 1853628 1855339 := bstep (se 1 (by rfl) ⟨1391504, by rfl⟩ : syracuseStep 1855339 = 2783009) B2783009
theorem B1855351 : Blo 1853628 1855351 := bstep (se 1 (by rfl) ⟨1391513, by rfl⟩ : syracuseStep 1855351 = 2783027) B2783027
theorem B1855371 : Blo 1853628 1855371 := bstep (se 1 (by rfl) ⟨1391528, by rfl⟩ : syracuseStep 1855371 = 2783057) B2783057
theorem B1855383 : Blo 1853628 1855383 := bstep (se 1 (by rfl) ⟨1391537, by rfl⟩ : syracuseStep 1855383 = 2783075) B2783075
theorem B1855403 : Blo 1853628 1855403 := bstep (se 1 (by rfl) ⟨1391552, by rfl⟩ : syracuseStep 1855403 = 2783105) B2783105
theorem B1855415 : Blo 1853628 1855415 := bstep (se 1 (by rfl) ⟨1391561, by rfl⟩ : syracuseStep 1855415 = 2783123) B2783123
theorem B5279681 : Blo 1853628 5279681 := bstep (se 2 (by rfl) ⟨1979880, by rfl⟩ : syracuseStep 5279681 = 3959761) B3959761
theorem B2781131 : Blo 1853628 2781131 := bstep (se 1 (by rfl) ⟨2085848, by rfl⟩ : syracuseStep 2781131 = 4171697) B4171697
theorem B1855435 : Blo 1853628 1855435 := bstep (se 1 (by rfl) ⟨1391576, by rfl⟩ : syracuseStep 1855435 = 2783153) B2783153
theorem B2781143 : Blo 1853628 2781143 := bstep (se 1 (by rfl) ⟨2085857, by rfl⟩ : syracuseStep 2781143 = 4171715) B4171715
theorem B1855447 : Blo 1853628 1855447 := bstep (se 1 (by rfl) ⟨1391585, by rfl⟩ : syracuseStep 1855447 = 2783171) B2783171
theorem B4173785 : Blo 1853628 4173785 := bstep (se 2 (by rfl) ⟨1565169, by rfl⟩ : syracuseStep 4173785 = 3130339) B3130339
theorem B1855467 : Blo 1853628 1855467 := bstep (se 1 (by rfl) ⟨1391600, by rfl⟩ : syracuseStep 1855467 = 2783201) B2783201
theorem B1855479 : Blo 1853628 1855479 := bstep (se 1 (by rfl) ⟨1391609, by rfl⟩ : syracuseStep 1855479 = 2783219) B2783219
theorem B1855499 : Blo 1853628 1855499 := bstep (se 1 (by rfl) ⟨1391624, by rfl⟩ : syracuseStep 1855499 = 2783249) B2783249
theorem B1855511 : Blo 1853628 1855511 := bstep (se 1 (by rfl) ⟨1391633, by rfl⟩ : syracuseStep 1855511 = 2783267) B2783267
theorem B2781209 : Blo 1853628 2781209 := bstep (se 2 (by rfl) ⟨1042953, by rfl⟩ : syracuseStep 2781209 = 2085907) B2085907
theorem B1855531 : Blo 1853628 1855531 := bstep (se 1 (by rfl) ⟨1391648, by rfl⟩ : syracuseStep 1855531 = 2783297) B2783297
theorem B4173875 : Blo 1853628 4173875 := bstep (se 1 (by rfl) ⟨3130406, by rfl⟩ : syracuseStep 4173875 = 6260813) B6260813
theorem B1855543 : Blo 1853628 1855543 := bstep (se 1 (by rfl) ⟨1391657, by rfl⟩ : syracuseStep 1855543 = 2783315) B2783315
theorem B7925825 : Blo 1853628 7925825 := bstep (se 2 (by rfl) ⟨2972184, by rfl⟩ : syracuseStep 7925825 = 5944369) B5944369
theorem B9384011 : Blo 1853628 9384011 := bstep (se 1 (by rfl) ⟨7038008, by rfl⟩ : syracuseStep 9384011 = 14076017) B14076017
theorem B1855563 : Blo 1853628 1855563 := bstep (se 1 (by rfl) ⟨1391672, by rfl⟩ : syracuseStep 1855563 = 2783345) B2783345
theorem B4173911 : Blo 1853628 4173911 := bstep (se 1 (by rfl) ⟨3130433, by rfl⟩ : syracuseStep 4173911 = 6260867) B6260867
theorem B1855575 : Blo 1853628 1855575 := bstep (se 1 (by rfl) ⟨1391681, by rfl⟩ : syracuseStep 1855575 = 2783363) B2783363
theorem B1855595 : Blo 1853628 1855595 := bstep (se 1 (by rfl) ⟨1391696, by rfl⟩ : syracuseStep 1855595 = 2783393) B2783393
theorem B1855607 : Blo 1853628 1855607 := bstep (se 1 (by rfl) ⟨1391705, by rfl⟩ : syracuseStep 1855607 = 2783411) B2783411
theorem B2781323 : Blo 1853628 2781323 := bstep (se 1 (by rfl) ⟨2085992, by rfl⟩ : syracuseStep 2781323 = 4171985) B4171985
theorem B2347147 : Blo 1853628 2347147 := bstep (se 1 (by rfl) ⟨1760360, by rfl⟩ : syracuseStep 2347147 = 3520721) B3520721
theorem B1855627 : Blo 1853628 1855627 := bstep (se 1 (by rfl) ⟨1391720, by rfl⟩ : syracuseStep 1855627 = 2783441) B2783441
theorem B2781335 : Blo 1853628 2781335 := bstep (se 1 (by rfl) ⟨2086001, by rfl⟩ : syracuseStep 2781335 = 4172003) B4172003
theorem B6025367 : Blo 1853628 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B2781401 : Blo 1853628 2781401 := bstep (se 2 (by rfl) ⟨1043025, by rfl⟩ : syracuseStep 2781401 = 2086051) B2086051
theorem B4174091 : Blo 1853628 4174091 := bstep (se 1 (by rfl) ⟨3130568, by rfl⟩ : syracuseStep 4174091 = 6261137) B6261137
theorem B3961153 : Blo 1853628 3961153 := bstep (se 2 (by rfl) ⟨1485432, by rfl⟩ : syracuseStep 3961153 = 2970865) B2970865
theorem B4174145 : Blo 1853628 4174145 := bstep (se 2 (by rfl) ⟨1565304, by rfl⟩ : syracuseStep 4174145 = 3130609) B3130609
theorem B2781515 : Blo 1853628 2781515 := bstep (se 1 (by rfl) ⟨2086136, by rfl⟩ : syracuseStep 2781515 = 4172273) B4172273
theorem B2781527 : Blo 1853628 2781527 := bstep (se 1 (by rfl) ⟨2086145, by rfl⟩ : syracuseStep 2781527 = 4172291) B4172291
theorem B7926167 : Blo 1853628 7926167 := bstep (se 1 (by rfl) ⟨5944625, by rfl⟩ : syracuseStep 7926167 = 11889251) B11889251
theorem B2781593 : Blo 1853628 2781593 := bstep (se 2 (by rfl) ⟨1043097, by rfl⟩ : syracuseStep 2781593 = 2086195) B2086195
theorem B19026353 : Blo 1853628 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B2085367 : Blo 1853628 2085367 := bstep (se 1 (by rfl) ⟨1564025, by rfl⟩ : syracuseStep 2085367 = 3128051) B3128051
theorem B2781707 : Blo 1853628 2781707 := bstep (se 1 (by rfl) ⟨2086280, by rfl⟩ : syracuseStep 2781707 = 4172561) B4172561
theorem B2781719 : Blo 1853628 2781719 := bstep (se 1 (by rfl) ⟨2086289, by rfl⟩ : syracuseStep 2781719 = 4172579) B4172579
theorem B4174361 : Blo 1853628 4174361 := bstep (se 2 (by rfl) ⟨1565385, by rfl⟩ : syracuseStep 4174361 = 3130771) B3130771
theorem B2970199 : Blo 1853628 2970199 := bstep (se 1 (by rfl) ⟨2227649, by rfl⟩ : syracuseStep 2970199 = 4455299) B4455299
theorem B3519065 : Blo 1853628 3519065 := bstep (se 2 (by rfl) ⟨1319649, by rfl⟩ : syracuseStep 3519065 = 2639299) B2639299
theorem B2781785 : Blo 1853628 2781785 := bstep (se 2 (by rfl) ⟨1043169, by rfl⟩ : syracuseStep 2781785 = 2086339) B2086339
theorem B4174451 : Blo 1853628 4174451 := bstep (se 1 (by rfl) ⟨3130838, by rfl⟩ : syracuseStep 4174451 = 6261677) B6261677
theorem B2970263 : Blo 1853628 2970263 := bstep (se 1 (by rfl) ⟨2227697, by rfl⟩ : syracuseStep 2970263 = 4455395) B4455395
theorem B4174487 : Blo 1853628 4174487 := bstep (se 1 (by rfl) ⟨3130865, by rfl⟩ : syracuseStep 4174487 = 6261731) B6261731
theorem B5943959 : Blo 1853628 5943959 := bstep (se 1 (by rfl) ⟨4457969, by rfl⟩ : syracuseStep 5943959 = 8915939) B8915939
theorem B2085547 : Blo 1853628 2085547 := bstep (se 1 (by rfl) ⟨1564160, by rfl⟩ : syracuseStep 2085547 = 3128321) B3128321
theorem B2781899 : Blo 1853628 2781899 := bstep (se 1 (by rfl) ⟨2086424, by rfl⟩ : syracuseStep 2781899 = 4172849) B4172849
theorem B3011275 : Blo 1853628 3011275 := bstep (se 1 (by rfl) ⟨2258456, by rfl⟩ : syracuseStep 3011275 = 4516913) B4516913
theorem B2781911 : Blo 1853628 2781911 := bstep (se 1 (by rfl) ⟨2086433, by rfl⟩ : syracuseStep 2781911 = 4172867) B4172867
theorem B2085655 : Blo 1853628 2085655 := bstep (se 1 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 2085655 = 3128483) B3128483
theorem B2781977 : Blo 1853628 2781977 := bstep (se 2 (by rfl) ⟨1043241, by rfl⟩ : syracuseStep 2781977 = 2086483) B2086483
theorem B8909633 : Blo 1853628 8909633 := bstep (se 2 (by rfl) ⟨3341112, by rfl⟩ : syracuseStep 8909633 = 6682225) B6682225
theorem B6681419 : Blo 1853628 6681419 := bstep (se 1 (by rfl) ⟨5011064, by rfl⟩ : syracuseStep 6681419 = 10022129) B10022129
theorem B4174667 : Blo 1853628 4174667 := bstep (se 1 (by rfl) ⟨3131000, by rfl⟩ : syracuseStep 4174667 = 6262001) B6262001
theorem B4174721 : Blo 1853628 4174721 := bstep (se 2 (by rfl) ⟨1565520, by rfl⟩ : syracuseStep 4174721 = 3131041) B3131041
theorem B2782091 : Blo 1853628 2782091 := bstep (se 1 (by rfl) ⟨2086568, by rfl⟩ : syracuseStep 2782091 = 4173137) B4173137
theorem B2782103 : Blo 1853628 2782103 := bstep (se 1 (by rfl) ⟨2086577, by rfl⟩ : syracuseStep 2782103 = 4173155) B4173155
theorem B24089521 : Blo 1853628 24089521 := bstep (se 2 (by rfl) ⟨9033570, by rfl⟩ : syracuseStep 24089521 = 18067141) B18067141
theorem B15848369 : Blo 1853628 15848369 := bstep (se 2 (by rfl) ⟨5943138, by rfl⟩ : syracuseStep 15848369 = 11886277) B11886277
theorem B2085835 : Blo 1853628 2085835 := bstep (se 1 (by rfl) ⟨1564376, by rfl⟩ : syracuseStep 2085835 = 3128753) B3128753
theorem B2782169 : Blo 1853628 2782169 := bstep (se 2 (by rfl) ⟨1043313, by rfl⟩ : syracuseStep 2782169 = 2086627) B2086627
theorem B2085943 : Blo 1853628 2085943 := bstep (se 1 (by rfl) ⟨1564457, by rfl⟩ : syracuseStep 2085943 = 3128915) B3128915
theorem B2782283 : Blo 1853628 2782283 := bstep (se 1 (by rfl) ⟨2086712, by rfl⟩ : syracuseStep 2782283 = 4173425) B4173425
theorem B2782295 : Blo 1853628 2782295 := bstep (se 1 (by rfl) ⟨2086721, by rfl⟩ : syracuseStep 2782295 = 4173443) B4173443
theorem B2348119 : Blo 1853628 2348119 := bstep (se 1 (by rfl) ⟨1761089, by rfl⟩ : syracuseStep 2348119 = 3522179) B3522179
theorem B4174937 : Blo 1853628 4174937 := bstep (se 2 (by rfl) ⟨1565601, by rfl⟩ : syracuseStep 4174937 = 3131203) B3131203
theorem B9393245 : Blo 1853628 9393245 := bstep (se 3 (by rfl) ⟨1761233, by rfl⟩ : syracuseStep 9393245 = 3522467) B3522467
theorem B2782361 : Blo 1853628 2782361 := bstep (se 2 (by rfl) ⟨1043385, by rfl⟩ : syracuseStep 2782361 = 2086771) B2086771
theorem B5944499 : Blo 1853628 5944499 := bstep (se 1 (by rfl) ⟨4458374, by rfl⟩ : syracuseStep 5944499 = 8916749) B8916749
theorem B4175027 : Blo 1853628 4175027 := bstep (se 1 (by rfl) ⟨3131270, by rfl⟩ : syracuseStep 4175027 = 6262541) B6262541
theorem B2970827 : Blo 1853628 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B3519703 : Blo 1853628 3519703 := bstep (se 1 (by rfl) ⟨2639777, by rfl⟩ : syracuseStep 3519703 = 5279555) B5279555
theorem B4175063 : Blo 1853628 4175063 := bstep (se 1 (by rfl) ⟨3131297, by rfl⟩ : syracuseStep 4175063 = 6262595) B6262595
theorem B2086123 : Blo 1853628 2086123 := bstep (se 1 (by rfl) ⟨1564592, by rfl⟩ : syracuseStep 2086123 = 3129185) B3129185
theorem B2782475 : Blo 1853628 2782475 := bstep (se 1 (by rfl) ⟨2086856, by rfl⟩ : syracuseStep 2782475 = 4173713) B4173713
theorem B11883793 : Blo 1853628 11883793 := bstep (se 2 (by rfl) ⟨4456422, by rfl⟩ : syracuseStep 11883793 = 8912845) B8912845
theorem B2782487 : Blo 1853628 2782487 := bstep (se 1 (by rfl) ⟨2086865, by rfl⟩ : syracuseStep 2782487 = 4173731) B4173731
theorem B2086231 : Blo 1853628 2086231 := bstep (se 1 (by rfl) ⟨1564673, by rfl⟩ : syracuseStep 2086231 = 3129347) B3129347
theorem B2782553 : Blo 1853628 2782553 := bstep (se 2 (by rfl) ⟨1043457, by rfl⟩ : syracuseStep 2782553 = 2086915) B2086915
theorem B2971019 : Blo 1853628 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B2782667 : Blo 1853628 2782667 := bstep (se 1 (by rfl) ⟨2087000, by rfl⟩ : syracuseStep 2782667 = 4174001) B4174001
theorem B2782679 : Blo 1853628 2782679 := bstep (se 1 (by rfl) ⟨2087009, by rfl⟩ : syracuseStep 2782679 = 4174019) B4174019
theorem B2086411 : Blo 1853628 2086411 := bstep (se 1 (by rfl) ⟨1564808, by rfl⟩ : syracuseStep 2086411 = 3129617) B3129617
theorem B2782745 : Blo 1853628 2782745 := bstep (se 2 (by rfl) ⟨1043529, by rfl⟩ : syracuseStep 2782745 = 2087059) B2087059
theorem B5281355 : Blo 1853628 5281355 := bstep (se 1 (by rfl) ⟨3961016, by rfl⟩ : syracuseStep 5281355 = 7922033) B7922033
theorem B15849053 : Blo 1853628 15849053 := bstep (se 3 (by rfl) ⟨2971697, by rfl⟩ : syracuseStep 15849053 = 5943395) B5943395
theorem B2086519 : Blo 1853628 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B2782859 : Blo 1853628 2782859 := bstep (se 1 (by rfl) ⟨2087144, by rfl⟩ : syracuseStep 2782859 = 4174289) B4174289
theorem B2782871 : Blo 1853628 2782871 := bstep (se 1 (by rfl) ⟨2087153, by rfl⟩ : syracuseStep 2782871 = 4174307) B4174307
theorem B7042733 : Blo 1853628 7042733 := bstep (se 3 (by rfl) ⟨1320512, by rfl⟩ : syracuseStep 7042733 = 2641025) B2641025
theorem B6256331 : Blo 1853628 6256331 := bstep (se 1 (by rfl) ⟨4692248, by rfl⟩ : syracuseStep 6256331 = 9384497) B9384497
theorem B2782937 : Blo 1853628 2782937 := bstep (se 2 (by rfl) ⟨1043601, by rfl⟩ : syracuseStep 2782937 = 2087203) B2087203
theorem B2086699 : Blo 1853628 2086699 := bstep (se 1 (by rfl) ⟨1565024, by rfl⟩ : syracuseStep 2086699 = 3130049) B3130049
theorem B9385793 : Blo 1853628 9385793 := bstep (se 2 (by rfl) ⟨3519672, by rfl⟩ : syracuseStep 9385793 = 7039345) B7039345
theorem B13367105 : Blo 1853628 13367105 := bstep (se 2 (by rfl) ⟨5012664, by rfl⟩ : syracuseStep 13367105 = 10025329) B10025329
theorem B1980235 : Blo 1853628 1980235 := bstep (se 1 (by rfl) ⟨1485176, by rfl⟩ : syracuseStep 1980235 = 2970353) B2970353
theorem B2783051 : Blo 1853628 2783051 := bstep (se 1 (by rfl) ⟨2087288, by rfl⟩ : syracuseStep 2783051 = 4174577) B4174577
theorem B2783063 : Blo 1853628 2783063 := bstep (se 1 (by rfl) ⟨2087297, by rfl⟩ : syracuseStep 2783063 = 4174595) B4174595
theorem B2086807 : Blo 1853628 2086807 := bstep (se 1 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 2086807 = 3130211) B3130211
theorem B2783129 : Blo 1853628 2783129 := bstep (se 2 (by rfl) ⟨1043673, by rfl⟩ : syracuseStep 2783129 = 2087347) B2087347
theorem B5355443 : Blo 1853628 5355443 := bstep (se 1 (by rfl) ⟨4016582, by rfl⟩ : syracuseStep 5355443 = 8033165) B8033165
theorem B6256601 : Blo 1853628 6256601 := bstep (se 2 (by rfl) ⟨2346225, by rfl⟩ : syracuseStep 6256601 = 4692451) B4692451
theorem B3520523 : Blo 1853628 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B2783243 : Blo 1853628 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B2783255 : Blo 1853628 2783255 := bstep (se 1 (by rfl) ⟨2087441, by rfl⟩ : syracuseStep 2783255 = 4174883) B4174883
theorem B6682675 : Blo 1853628 6682675 := bstep (se 1 (by rfl) ⟨5012006, by rfl⟩ : syracuseStep 6682675 = 10024013) B10024013
theorem B3520577 : Blo 1853628 3520577 := bstep (se 2 (by rfl) ⟨1320216, by rfl⟩ : syracuseStep 3520577 = 2640433) B2640433
theorem B2086987 : Blo 1853628 2086987 := bstep (se 1 (by rfl) ⟨1565240, by rfl⟩ : syracuseStep 2086987 = 3130481) B3130481
theorem B2783321 : Blo 1853628 2783321 := bstep (se 2 (by rfl) ⟨1043745, by rfl⟩ : syracuseStep 2783321 = 2087491) B2087491
theorem B11884637 : Blo 1853628 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B2259095 : Blo 1853628 2259095 := bstep (se 1 (by rfl) ⟨1694321, by rfl⟩ : syracuseStep 2259095 = 3388643) B3388643
theorem B7919795 : Blo 1853628 7919795 := bstep (se 1 (by rfl) ⟨5939846, by rfl⟩ : syracuseStep 7919795 = 11879693) B11879693
theorem B2087095 : Blo 1853628 2087095 := bstep (se 1 (by rfl) ⟨1565321, by rfl⟩ : syracuseStep 2087095 = 3130643) B3130643
theorem B2783435 : Blo 1853628 2783435 := bstep (se 1 (by rfl) ⟨2087576, by rfl⟩ : syracuseStep 2783435 = 4175153) B4175153
theorem B4692289 : Blo 1853628 4692289 := bstep (se 2 (by rfl) ⟨1759608, by rfl⟩ : syracuseStep 4692289 = 3519217) B3519217
theorem B7919947 : Blo 1853628 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B2971993 : Blo 1853628 2971993 := bstep (se 2 (by rfl) ⟨1114497, by rfl⟩ : syracuseStep 2971993 = 2228995) B2228995
theorem B2087275 : Blo 1853628 2087275 := bstep (se 1 (by rfl) ⟨1565456, by rfl⟩ : syracuseStep 2087275 = 3130913) B3130913
theorem B7920017 : Blo 1853628 7920017 := bstep (se 2 (by rfl) ⟨2970006, by rfl⟩ : syracuseStep 7920017 = 5940013) B5940013
theorem B7043507 : Blo 1853628 7043507 := bstep (se 1 (by rfl) ⟨5282630, by rfl⟩ : syracuseStep 7043507 = 10565261) B10565261
theorem B14088653 : Blo 1853628 14088653 := bstep (se 3 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 14088653 = 5283245) B5283245
theorem B2087383 : Blo 1853628 2087383 := bstep (se 1 (by rfl) ⟨1565537, by rfl⟩ : syracuseStep 2087383 = 3131075) B3131075
theorem B2087563 : Blo 1853628 2087563 := bstep (se 1 (by rfl) ⟨1565672, by rfl⟩ : syracuseStep 2087563 = 3131345) B3131345
theorem B6257303 : Blo 1853628 6257303 := bstep (se 1 (by rfl) ⟨4692977, by rfl⟩ : syracuseStep 6257303 = 9385955) B9385955
theorem B5716631 : Blo 1853628 5716631 := bstep (se 1 (by rfl) ⟨4287473, by rfl⟩ : syracuseStep 5716631 = 8574947) B8574947
theorem B5012189 : Blo 1853628 5012189 := bstep (se 3 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 5012189 = 1879571) B1879571
theorem B8911633 : Blo 1853628 8911633 := bstep (se 2 (by rfl) ⟨3341862, by rfl⟩ : syracuseStep 8911633 = 6683725) B6683725
theorem B5282653 : Blo 1853628 5282653 := bstep (se 3 (by rfl) ⟨990497, by rfl⟩ : syracuseStep 5282653 = 1980995) B1980995
theorem B3341171 : Blo 1853628 3341171 := bstep (se 1 (by rfl) ⟨2505878, by rfl⟩ : syracuseStep 3341171 = 5011757) B5011757
theorem B4692887 : Blo 1853628 4692887 := bstep (se 1 (by rfl) ⟨3519665, by rfl⟩ : syracuseStep 4692887 = 7039331) B7039331
theorem B8461207 : Blo 1853628 8461207 := bstep (se 1 (by rfl) ⟨6345905, by rfl⟩ : syracuseStep 8461207 = 12691811) B12691811
theorem B65117105 : Blo 1853628 65117105 := bstep (se 2 (by rfl) ⟨24418914, by rfl⟩ : syracuseStep 65117105 = 48837829) B48837829
theorem B14089139 : Blo 1853628 14089139 := bstep (se 1 (by rfl) ⟨10566854, by rfl⟩ : syracuseStep 14089139 = 21133709) B21133709
theorem B3128267 : Blo 1853628 3128267 := bstep (se 1 (by rfl) ⟨2346200, by rfl⟩ : syracuseStep 3128267 = 4692401) B4692401
theorem B3521495 : Blo 1853628 3521495 := bstep (se 1 (by rfl) ⟨2641121, by rfl⟩ : syracuseStep 3521495 = 5282243) B5282243
theorem B3128395 : Blo 1853628 3128395 := bstep (se 1 (by rfl) ⟨2346296, by rfl⟩ : syracuseStep 3128395 = 4692593) B4692593
theorem B6257843 : Blo 1853628 6257843 := bstep (se 1 (by rfl) ⟨4693382, by rfl⟩ : syracuseStep 6257843 = 9386765) B9386765
theorem B5282995 : Blo 1853628 5282995 := bstep (se 1 (by rfl) ⟨3962246, by rfl⟩ : syracuseStep 5282995 = 7924493) B7924493
theorem B3128537 : Blo 1853628 3128537 := bstep (se 2 (by rfl) ⟨1173201, by rfl⟩ : syracuseStep 3128537 = 2346403) B2346403
theorem B2227543 : Blo 1853628 2227543 := bstep (se 1 (by rfl) ⟨1670657, by rfl⟩ : syracuseStep 2227543 = 3341315) B3341315
theorem B3128665 : Blo 1853628 3128665 := bstep (se 2 (by rfl) ⟨1173249, by rfl⟩ : syracuseStep 3128665 = 2346499) B2346499
theorem B5938525 : Blo 1853628 5938525 := bstep (se 3 (by rfl) ⟨1113473, by rfl⟩ : syracuseStep 5938525 = 2226947) B2226947
theorem B8478103 : Blo 1853628 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B7724467 : Blo 1853628 7724467 := bstep (se 1 (by rfl) ⟨5793350, by rfl⟩ : syracuseStep 7724467 = 11586701) B11586701
theorem B6258113 : Blo 1853628 6258113 := bstep (se 2 (by rfl) ⟨2346792, by rfl⟩ : syracuseStep 6258113 = 4693585) B4693585
theorem B3522035 : Blo 1853628 3522035 := bstep (se 1 (by rfl) ⟨2641526, by rfl⟩ : syracuseStep 3522035 = 5283053) B5283053
theorem B4693697 : Blo 1853628 4693697 := bstep (se 2 (by rfl) ⟨1760136, by rfl⟩ : syracuseStep 4693697 = 3520273) B3520273
theorem B53468869 : Blo 1853628 53468869 := bstep (se 4 (by rfl) ⟨5012706, by rfl⟩ : syracuseStep 53468869 = 10025413) B10025413
theorem B9387737 : Blo 1853628 9387737 := bstep (se 2 (by rfl) ⟨3520401, by rfl⟩ : syracuseStep 9387737 = 7040803) B7040803
theorem B10157899 : Blo 1853628 10157899 := bstep (se 1 (by rfl) ⟨7618424, by rfl⟩ : syracuseStep 10157899 = 15236849) B15236849
theorem B10166147 : Blo 1853628 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B7044995 : Blo 1853628 7044995 := bstep (se 1 (by rfl) ⟨5283746, by rfl⟩ : syracuseStep 7044995 = 10567493) B10567493
theorem B3129239 : Blo 1853628 3129239 := bstep (se 1 (by rfl) ⟨2346929, by rfl⟩ : syracuseStep 3129239 = 4693859) B4693859
theorem B5078987 : Blo 1853628 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B5717963 : Blo 1853628 5717963 := bstep (se 1 (by rfl) ⟨4288472, by rfl⟩ : syracuseStep 5717963 = 8576945) B8576945
theorem B3522521 : Blo 1853628 3522521 := bstep (se 2 (by rfl) ⟨1320945, by rfl⟩ : syracuseStep 3522521 = 2641891) B2641891
theorem B6258653 : Blo 1853628 6258653 := bstep (se 3 (by rfl) ⟨1173497, by rfl⟩ : syracuseStep 6258653 = 2346995) B2346995
theorem B9388061 : Blo 1853628 9388061 := bstep (se 3 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 9388061 = 3520523) B3520523
theorem B7045163 : Blo 1853628 7045163 := bstep (se 1 (by rfl) ⟨5283872, by rfl⟩ : syracuseStep 7045163 = 10567745) B10567745
theorem B5283883 : Blo 1853628 5283883 := bstep (se 1 (by rfl) ⟨3962912, by rfl⟩ : syracuseStep 5283883 = 7925825) B7925825
theorem B3522619 : Blo 1853628 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B11878487 : Blo 1853628 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B3129529 : Blo 1853628 3129529 := bstep (se 2 (by rfl) ⟨1173573, by rfl⟩ : syracuseStep 3129529 = 2347147) B2347147
theorem B5284111 : Blo 1853628 5284111 := bstep (se 1 (by rfl) ⟨3963083, by rfl⟩ : syracuseStep 5284111 = 7926167) B7926167
theorem B6258977 : Blo 1853628 6258977 := bstep (se 2 (by rfl) ⟨2347116, by rfl⟩ : syracuseStep 6258977 = 4694233) B4694233
theorem B3342727 : Blo 1853628 3342727 := bstep (se 1 (by rfl) ⟨2507045, by rfl⟩ : syracuseStep 3342727 = 5014091) B5014091
theorem B90259859 : Blo 1853628 90259859 := bstep (se 1 (by rfl) ⟨67694894, by rfl⟩ : syracuseStep 90259859 = 135389789) B135389789
theorem B10559929 : Blo 1853628 10559929 := bstep (se 2 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 10559929 = 7919947) B7919947
theorem B9388547 : Blo 1853628 9388547 := bstep (se 1 (by rfl) ⟨7041410, by rfl⟩ : syracuseStep 9388547 = 14082821) B14082821
theorem B5423645 : Blo 1853628 5423645 := bstep (se 3 (by rfl) ⟨1016933, by rfl⟩ : syracuseStep 5423645 = 2033867) B2033867
theorem B4457047 : Blo 1853628 4457047 := bstep (se 1 (by rfl) ⟨3342785, by rfl⟩ : syracuseStep 4457047 = 6685571) B6685571
theorem B5014169 : Blo 1853628 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B6259571 : Blo 1853628 6259571 := bstep (se 1 (by rfl) ⟨4694678, by rfl⟩ : syracuseStep 6259571 = 9389357) B9389357
theorem B4227959 : Blo 1853628 4227959 := bstep (se 1 (by rfl) ⟨3170969, by rfl⟩ : syracuseStep 4227959 = 6341939) B6341939
theorem B3130231 : Blo 1853628 3130231 := bstep (se 1 (by rfl) ⟨2347673, by rfl⟩ : syracuseStep 3130231 = 4695347) B4695347
theorem B4015033 : Blo 1853628 4015033 := bstep (se 2 (by rfl) ⟨1505637, by rfl⟩ : syracuseStep 4015033 = 3011275) B3011275
theorem B7922717 : Blo 1853628 7922717 := bstep (se 3 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 7922717 = 2971019) B2971019
theorem B3130427 : Blo 1853628 3130427 := bstep (se 1 (by rfl) ⟨2347820, by rfl⟩ : syracuseStep 3130427 = 4695641) B4695641
theorem B5637181 : Blo 1853628 5637181 := bstep (se 3 (by rfl) ⟨1056971, by rfl⟩ : syracuseStep 5637181 = 2113943) B2113943
theorem B4695155 : Blo 1853628 4695155 := bstep (se 1 (by rfl) ⟨3521366, by rfl⟩ : syracuseStep 4695155 = 7042733) B7042733
theorem B4170887 : Blo 1853628 4170887 := bstep (se 1 (by rfl) ⟨3128165, by rfl⟩ : syracuseStep 4170887 = 6256331) B6256331
theorem B11281609 : Blo 1853628 11281609 := bstep (se 2 (by rfl) ⟨4230603, by rfl⟩ : syracuseStep 11281609 = 8461207) B8461207
theorem B4171067 : Blo 1853628 4171067 := bstep (se 1 (by rfl) ⟨3128300, by rfl⟩ : syracuseStep 4171067 = 6256601) B6256601
theorem B7923091 : Blo 1853628 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B4171193 : Blo 1853628 4171193 := bstep (se 2 (by rfl) ⟨1564197, by rfl⟩ : syracuseStep 4171193 = 3128395) B3128395
theorem B3130825 : Blo 1853628 3130825 := bstep (se 2 (by rfl) ⟨1174059, by rfl⟩ : syracuseStep 3130825 = 2348119) B2348119
theorem B3343817 : Blo 1853628 3343817 := bstep (se 2 (by rfl) ⟨1253931, by rfl⟩ : syracuseStep 3343817 = 2507863) B2507863
theorem B5637691 : Blo 1853628 5637691 := bstep (se 1 (by rfl) ⟨4228268, by rfl⟩ : syracuseStep 5637691 = 8456537) B8456537
theorem B20055671 : Blo 1853628 20055671 := bstep (se 1 (by rfl) ⟨15041753, by rfl⟩ : syracuseStep 20055671 = 30083507) B30083507
theorem B4695671 : Blo 1853628 4695671 := bstep (se 1 (by rfl) ⟨3521753, by rfl⟩ : syracuseStep 4695671 = 7043507) B7043507
theorem B15845057 : Blo 1853628 15845057 := bstep (se 2 (by rfl) ⟨5941896, by rfl⟩ : syracuseStep 15845057 = 11883793) B11883793
theorem B4171535 : Blo 1853628 4171535 := bstep (se 1 (by rfl) ⟨3128651, by rfl⟩ : syracuseStep 4171535 = 6257303) B6257303
theorem B3811087 : Blo 1853628 3811087 := bstep (se 1 (by rfl) ⟨2858315, by rfl⟩ : syracuseStep 3811087 = 5716631) B5716631
theorem B6686479 : Blo 1853628 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B4171553 : Blo 1853628 4171553 := bstep (se 2 (by rfl) ⟨1564332, by rfl⟩ : syracuseStep 4171553 = 3128665) B3128665
theorem B11880229 : Blo 1853628 11880229 := bstep (se 4 (by rfl) ⟨1113771, by rfl⟩ : syracuseStep 11880229 = 2227543) B2227543
theorem B2639675 : Blo 1853628 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B31672133 : Blo 1853628 31672133 := bstep (se 4 (by rfl) ⟨2969262, by rfl⟩ : syracuseStep 31672133 = 5938525) B5938525
theorem B3172297 : Blo 1853628 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B43411403 : Blo 1853628 43411403 := bstep (se 1 (by rfl) ⟨32558552, by rfl⟩ : syracuseStep 43411403 = 65117105) B65117105
theorem B9390167 : Blo 1853628 9390167 := bstep (se 1 (by rfl) ⟨7042625, by rfl⟩ : syracuseStep 9390167 = 14085251) B14085251
theorem B4171895 : Blo 1853628 4171895 := bstep (se 1 (by rfl) ⟨3128921, by rfl⟩ : syracuseStep 4171895 = 6257843) B6257843
theorem B23759021 : Blo 1853628 23759021 := bstep (se 3 (by rfl) ⟨4454816, by rfl⟩ : syracuseStep 23759021 = 8909633) B8909633
theorem B2640119 : Blo 1853628 2640119 := bstep (se 1 (by rfl) ⟨1980089, by rfl⟩ : syracuseStep 2640119 = 3960179) B3960179
theorem B1853703 : Blo 1853628 1853703 := bstep (se 1 (by rfl) ⟨1390277, by rfl⟩ : syracuseStep 1853703 = 2780555) B2780555
theorem B1853711 : Blo 1853628 1853711 := bstep (se 1 (by rfl) ⟨1390283, by rfl⟩ : syracuseStep 1853711 = 2780567) B2780567
theorem B4172075 : Blo 1853628 4172075 := bstep (se 1 (by rfl) ⟨3129056, by rfl⟩ : syracuseStep 4172075 = 6258113) B6258113
theorem B1853755 : Blo 1853628 1853755 := bstep (se 1 (by rfl) ⟨1390316, by rfl⟩ : syracuseStep 1853755 = 2780633) B2780633
theorem B1853831 : Blo 1853628 1853831 := bstep (se 1 (by rfl) ⟨1390373, by rfl⟩ : syracuseStep 1853831 = 2780747) B2780747
theorem B1853839 : Blo 1853628 1853839 := bstep (se 1 (by rfl) ⟨1390379, by rfl⟩ : syracuseStep 1853839 = 2780759) B2780759
theorem B13543865 : Blo 1853628 13543865 := bstep (se 2 (by rfl) ⟨5078949, by rfl⟩ : syracuseStep 13543865 = 10157899) B10157899
theorem B2640313 : Blo 1853628 2640313 := bstep (se 2 (by rfl) ⟨990117, by rfl⟩ : syracuseStep 2640313 = 1980235) B1980235
theorem B1853883 : Blo 1853628 1853883 := bstep (se 1 (by rfl) ⟨1390412, by rfl⟩ : syracuseStep 1853883 = 2780825) B2780825
theorem B14281181 : Blo 1853628 14281181 := bstep (se 3 (by rfl) ⟨2677721, by rfl⟩ : syracuseStep 14281181 = 5355443) B5355443
theorem B1853959 : Blo 1853628 1853959 := bstep (se 1 (by rfl) ⟨1390469, by rfl⟩ : syracuseStep 1853959 = 2780939) B2780939
theorem B1853967 : Blo 1853628 1853967 := bstep (se 1 (by rfl) ⟨1390475, by rfl⟩ : syracuseStep 1853967 = 2780951) B2780951
theorem B15247901 : Blo 1853628 15247901 := bstep (se 3 (by rfl) ⟨2858981, by rfl⟩ : syracuseStep 15247901 = 5717963) B5717963
theorem B6777373 : Blo 1853628 6777373 := bstep (se 3 (by rfl) ⟨1270757, by rfl⟩ : syracuseStep 6777373 = 2541515) B2541515
theorem B2820665 : Blo 1853628 2820665 := bstep (se 2 (by rfl) ⟨1057749, by rfl⟩ : syracuseStep 2820665 = 2115499) B2115499
theorem B1854011 : Blo 1853628 1854011 := bstep (se 1 (by rfl) ⟨1390508, by rfl⟩ : syracuseStep 1854011 = 2781017) B2781017
theorem B9390653 : Blo 1853628 9390653 := bstep (se 3 (by rfl) ⟨1760747, by rfl⟩ : syracuseStep 9390653 = 3521495) B3521495
theorem B6777431 : Blo 1853628 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B4696663 : Blo 1853628 4696663 := bstep (se 1 (by rfl) ⟨3522497, by rfl⟩ : syracuseStep 4696663 = 7044995) B7044995
theorem B3385991 : Blo 1853628 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B1854087 : Blo 1853628 1854087 := bstep (se 1 (by rfl) ⟨1390565, by rfl⟩ : syracuseStep 1854087 = 2781131) B2781131
theorem B1854095 : Blo 1853628 1854095 := bstep (se 1 (by rfl) ⟨1390571, by rfl⟩ : syracuseStep 1854095 = 2781143) B2781143
theorem B4172435 : Blo 1853628 4172435 := bstep (se 1 (by rfl) ⟨3129326, by rfl⟩ : syracuseStep 4172435 = 6258653) B6258653
theorem B1854139 : Blo 1853628 1854139 := bstep (se 1 (by rfl) ⟨1390604, by rfl⟩ : syracuseStep 1854139 = 2781209) B2781209
theorem B4172489 : Blo 1853628 4172489 := bstep (se 2 (by rfl) ⟨1564683, by rfl⟩ : syracuseStep 4172489 = 3129367) B3129367
theorem B5941961 : Blo 1853628 5941961 := bstep (se 2 (by rfl) ⟨2228235, by rfl⟩ : syracuseStep 5941961 = 4456471) B4456471
theorem B1854215 : Blo 1853628 1854215 := bstep (se 1 (by rfl) ⟨1390661, by rfl⟩ : syracuseStep 1854215 = 2781323) B2781323
theorem B1854223 : Blo 1853628 1854223 := bstep (se 1 (by rfl) ⟨1390667, by rfl⟩ : syracuseStep 1854223 = 2781335) B2781335
theorem B1854267 : Blo 1853628 1854267 := bstep (se 1 (by rfl) ⟨1390700, by rfl⟩ : syracuseStep 1854267 = 2781401) B2781401
theorem B1854343 : Blo 1853628 1854343 := bstep (se 1 (by rfl) ⟨1390757, by rfl⟩ : syracuseStep 1854343 = 2781515) B2781515
theorem B4696967 : Blo 1853628 4696967 := bstep (se 1 (by rfl) ⟨3522725, by rfl⟩ : syracuseStep 4696967 = 7045451) B7045451
theorem B1854351 : Blo 1853628 1854351 := bstep (se 1 (by rfl) ⟨1390763, by rfl⟩ : syracuseStep 1854351 = 2781527) B2781527
theorem B40668085 : Blo 1853628 40668085 := bstep (se 5 (by rfl) ⟨1906316, by rfl⟩ : syracuseStep 40668085 = 3812633) B3812633
theorem B1854395 : Blo 1853628 1854395 := bstep (se 1 (by rfl) ⟨1390796, by rfl⟩ : syracuseStep 1854395 = 2781593) B2781593
theorem B12684235 : Blo 1853628 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B1854471 : Blo 1853628 1854471 := bstep (se 1 (by rfl) ⟨1390853, by rfl⟩ : syracuseStep 1854471 = 2781707) B2781707
theorem B1854479 : Blo 1853628 1854479 := bstep (se 1 (by rfl) ⟨1390859, by rfl⟩ : syracuseStep 1854479 = 2781719) B2781719
theorem B1854523 : Blo 1853628 1854523 := bstep (se 1 (by rfl) ⟨1390892, by rfl⟩ : syracuseStep 1854523 = 2781785) B2781785
theorem B14076989 : Blo 1853628 14076989 := bstep (se 3 (by rfl) ⟨2639435, by rfl⟩ : syracuseStep 14076989 = 5278871) B5278871
theorem B16067645 : Blo 1853628 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B1854599 : Blo 1853628 1854599 := bstep (se 1 (by rfl) ⟨1390949, by rfl⟩ : syracuseStep 1854599 = 2781899) B2781899
theorem B1854607 : Blo 1853628 1854607 := bstep (se 1 (by rfl) ⟨1390955, by rfl⟩ : syracuseStep 1854607 = 2781911) B2781911
theorem B1854651 : Blo 1853628 1854651 := bstep (se 1 (by rfl) ⟨1390988, by rfl⟩ : syracuseStep 1854651 = 2781977) B2781977
theorem B1854727 : Blo 1853628 1854727 := bstep (se 1 (by rfl) ⟨1391045, by rfl⟩ : syracuseStep 1854727 = 2782091) B2782091
theorem B1854735 : Blo 1853628 1854735 := bstep (se 1 (by rfl) ⟨1391051, by rfl⟩ : syracuseStep 1854735 = 2782103) B2782103
theorem B2780459 : Blo 1853628 2780459 := bstep (se 1 (by rfl) ⟨2085344, by rfl⟩ : syracuseStep 2780459 = 4170689) B4170689
theorem B1854779 : Blo 1853628 1854779 := bstep (se 1 (by rfl) ⟨1391084, by rfl⟩ : syracuseStep 1854779 = 2782169) B2782169
theorem B2780489 : Blo 1853628 2780489 := bstep (se 2 (by rfl) ⟨1042683, by rfl⟩ : syracuseStep 2780489 = 2085367) B2085367
theorem B4173191 : Blo 1853628 4173191 := bstep (se 1 (by rfl) ⟨3129893, by rfl⟩ : syracuseStep 4173191 = 6259787) B6259787
theorem B1854855 : Blo 1853628 1854855 := bstep (se 1 (by rfl) ⟨1391141, by rfl⟩ : syracuseStep 1854855 = 2782283) B2782283
theorem B1854863 : Blo 1853628 1854863 := bstep (se 1 (by rfl) ⟨1391147, by rfl⟩ : syracuseStep 1854863 = 2782295) B2782295
theorem B6262163 : Blo 1853628 6262163 := bstep (se 1 (by rfl) ⟨4696622, by rfl⟩ : syracuseStep 6262163 = 9393245) B9393245
theorem B2780603 : Blo 1853628 2780603 := bstep (se 1 (by rfl) ⟨2085452, by rfl⟩ : syracuseStep 2780603 = 4170905) B4170905
theorem B1854907 : Blo 1853628 1854907 := bstep (se 1 (by rfl) ⟨1391180, by rfl⟩ : syracuseStep 1854907 = 2782361) B2782361
theorem B3960265 : Blo 1853628 3960265 := bstep (se 2 (by rfl) ⟨1485099, by rfl⟩ : syracuseStep 3960265 = 2970199) B2970199
theorem B2780663 : Blo 1853628 2780663 := bstep (se 1 (by rfl) ⟨2085497, by rfl⟩ : syracuseStep 2780663 = 4170995) B4170995
theorem B1854983 : Blo 1853628 1854983 := bstep (se 1 (by rfl) ⟨1391237, by rfl⟩ : syracuseStep 1854983 = 2782475) B2782475
theorem B2780687 : Blo 1853628 2780687 := bstep (se 1 (by rfl) ⟨2085515, by rfl⟩ : syracuseStep 2780687 = 4171031) B4171031
theorem B1854991 : Blo 1853628 1854991 := bstep (se 1 (by rfl) ⟨1391243, by rfl⟩ : syracuseStep 1854991 = 2782487) B2782487
theorem B2780729 : Blo 1853628 2780729 := bstep (se 2 (by rfl) ⟨1042773, by rfl⟩ : syracuseStep 2780729 = 2085547) B2085547
theorem B4173371 : Blo 1853628 4173371 := bstep (se 1 (by rfl) ⟨3130028, by rfl⟩ : syracuseStep 4173371 = 6260057) B6260057
theorem B1855035 : Blo 1853628 1855035 := bstep (se 1 (by rfl) ⟨1391276, by rfl⟩ : syracuseStep 1855035 = 2782553) B2782553
theorem B2780807 : Blo 1853628 2780807 := bstep (se 1 (by rfl) ⟨2085605, by rfl⟩ : syracuseStep 2780807 = 4171211) B4171211
theorem B1855111 : Blo 1853628 1855111 := bstep (se 1 (by rfl) ⟨1391333, by rfl⟩ : syracuseStep 1855111 = 2782667) B2782667
theorem B1855119 : Blo 1853628 1855119 := bstep (se 1 (by rfl) ⟨1391339, by rfl⟩ : syracuseStep 1855119 = 2782679) B2782679
theorem B2780843 : Blo 1853628 2780843 := bstep (se 1 (by rfl) ⟨2085632, by rfl⟩ : syracuseStep 2780843 = 4171265) B4171265
theorem B4173497 : Blo 1853628 4173497 := bstep (se 2 (by rfl) ⟨1565061, by rfl⟩ : syracuseStep 4173497 = 3130123) B3130123
theorem B1855163 : Blo 1853628 1855163 := bstep (se 1 (by rfl) ⟨1391372, by rfl⟩ : syracuseStep 1855163 = 2782745) B2782745
theorem B11882177 : Blo 1853628 11882177 := bstep (se 2 (by rfl) ⟨4455816, by rfl⟩ : syracuseStep 11882177 = 8911633) B8911633
theorem B411455173 : Blo 1853628 411455173 := bstep (se 4 (by rfl) ⟨38573922, by rfl⟩ : syracuseStep 411455173 = 77147845) B77147845
theorem B2780873 : Blo 1853628 2780873 := bstep (se 2 (by rfl) ⟨1042827, by rfl⟩ : syracuseStep 2780873 = 2085655) B2085655
theorem B5639881 : Blo 1853628 5639881 := bstep (se 2 (by rfl) ⟨2114955, by rfl⟩ : syracuseStep 5639881 = 4229911) B4229911
theorem B1855239 : Blo 1853628 1855239 := bstep (se 1 (by rfl) ⟨1391429, by rfl⟩ : syracuseStep 1855239 = 2782859) B2782859
theorem B1855247 : Blo 1853628 1855247 := bstep (se 1 (by rfl) ⟨1391435, by rfl⟩ : syracuseStep 1855247 = 2782871) B2782871
theorem B2780987 : Blo 1853628 2780987 := bstep (se 1 (by rfl) ⟨2085740, by rfl⟩ : syracuseStep 2780987 = 4171481) B4171481
theorem B1855291 : Blo 1853628 1855291 := bstep (se 1 (by rfl) ⟨1391468, by rfl⟩ : syracuseStep 1855291 = 2782937) B2782937
theorem B15036275 : Blo 1853628 15036275 := bstep (se 1 (by rfl) ⟨11277206, by rfl⟩ : syracuseStep 15036275 = 22554413) B22554413
theorem B2781047 : Blo 1853628 2781047 := bstep (se 1 (by rfl) ⟨2085785, by rfl⟩ : syracuseStep 2781047 = 4171571) B4171571
theorem B1855367 : Blo 1853628 1855367 := bstep (se 1 (by rfl) ⟨1391525, by rfl⟩ : syracuseStep 1855367 = 2783051) B2783051
theorem B2781071 : Blo 1853628 2781071 := bstep (se 1 (by rfl) ⟨2085803, by rfl⟩ : syracuseStep 2781071 = 4171607) B4171607
theorem B1855375 : Blo 1853628 1855375 := bstep (se 1 (by rfl) ⟨1391531, by rfl⟩ : syracuseStep 1855375 = 2783063) B2783063
theorem B2781113 : Blo 1853628 2781113 := bstep (se 2 (by rfl) ⟨1042917, by rfl⟩ : syracuseStep 2781113 = 2085835) B2085835
theorem B1855419 : Blo 1853628 1855419 := bstep (se 1 (by rfl) ⟨1391564, by rfl⟩ : syracuseStep 1855419 = 2783129) B2783129
theorem B11284433 : Blo 1853628 11284433 := bstep (se 2 (by rfl) ⟨4231662, by rfl⟩ : syracuseStep 11284433 = 8463325) B8463325
theorem B2781191 : Blo 1853628 2781191 := bstep (se 1 (by rfl) ⟨2085893, by rfl⟩ : syracuseStep 2781191 = 4171787) B4171787
theorem B1855495 : Blo 1853628 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B4173839 : Blo 1853628 4173839 := bstep (se 1 (by rfl) ⟨3130379, by rfl⟩ : syracuseStep 4173839 = 6260759) B6260759
theorem B1855503 : Blo 1853628 1855503 := bstep (se 1 (by rfl) ⟨1391627, by rfl⟩ : syracuseStep 1855503 = 2783255) B2783255
theorem B4173857 : Blo 1853628 4173857 := bstep (se 2 (by rfl) ⟨1565196, by rfl⟩ : syracuseStep 4173857 = 3130393) B3130393
theorem B2781227 : Blo 1853628 2781227 := bstep (se 1 (by rfl) ⟨2085920, by rfl⟩ : syracuseStep 2781227 = 4171841) B4171841
theorem B2347051 : Blo 1853628 2347051 := bstep (se 1 (by rfl) ⟨1760288, by rfl⟩ : syracuseStep 2347051 = 3520577) B3520577
theorem B1855547 : Blo 1853628 1855547 := bstep (se 1 (by rfl) ⟨1391660, by rfl⟩ : syracuseStep 1855547 = 2783321) B2783321
theorem B2781257 : Blo 1853628 2781257 := bstep (se 2 (by rfl) ⟨1042971, by rfl⟩ : syracuseStep 2781257 = 2085943) B2085943
theorem B5279863 : Blo 1853628 5279863 := bstep (se 1 (by rfl) ⟨3959897, by rfl⟩ : syracuseStep 5279863 = 7919795) B7919795
theorem B1855623 : Blo 1853628 1855623 := bstep (se 1 (by rfl) ⟨1391717, by rfl⟩ : syracuseStep 1855623 = 2783435) B2783435
theorem B5279897 : Blo 1853628 5279897 := bstep (se 2 (by rfl) ⟨1979961, by rfl⟩ : syracuseStep 5279897 = 3959923) B3959923
theorem B2781371 : Blo 1853628 2781371 := bstep (se 1 (by rfl) ⟨2086028, by rfl⟩ : syracuseStep 2781371 = 4172057) B4172057
theorem B9384173 : Blo 1853628 9384173 := bstep (se 3 (by rfl) ⟨1759532, by rfl⟩ : syracuseStep 9384173 = 3519065) B3519065
theorem B24097013 : Blo 1853628 24097013 := bstep (se 5 (by rfl) ⟨1129547, by rfl⟩ : syracuseStep 24097013 = 2259095) B2259095
theorem B2781431 : Blo 1853628 2781431 := bstep (se 1 (by rfl) ⟨2086073, by rfl⟩ : syracuseStep 2781431 = 4172147) B4172147
theorem B5280011 : Blo 1853628 5280011 := bstep (se 1 (by rfl) ⟨3960008, by rfl⟩ : syracuseStep 5280011 = 7920017) B7920017
theorem B2781455 : Blo 1853628 2781455 := bstep (se 1 (by rfl) ⟨2086091, by rfl⟩ : syracuseStep 2781455 = 4172183) B4172183
theorem B3617057 : Blo 1853628 3617057 := bstep (se 2 (by rfl) ⟨1356396, by rfl⟩ : syracuseStep 3617057 = 2712793) B2712793
theorem B9392435 : Blo 1853628 9392435 := bstep (se 1 (by rfl) ⟨7044326, by rfl⟩ : syracuseStep 9392435 = 14088653) B14088653
theorem B2781497 : Blo 1853628 2781497 := bstep (se 2 (by rfl) ⟨1043061, by rfl⟩ : syracuseStep 2781497 = 2086123) B2086123
theorem B4174199 : Blo 1853628 4174199 := bstep (se 1 (by rfl) ⟨3130649, by rfl⟩ : syracuseStep 4174199 = 6261299) B6261299
theorem B2781575 : Blo 1853628 2781575 := bstep (se 1 (by rfl) ⟨2086181, by rfl⟩ : syracuseStep 2781575 = 4172363) B4172363
theorem B2781611 : Blo 1853628 2781611 := bstep (se 1 (by rfl) ⟨2086208, by rfl⟩ : syracuseStep 2781611 = 4172417) B4172417
theorem B2781641 : Blo 1853628 2781641 := bstep (se 2 (by rfl) ⟨1043115, by rfl⟩ : syracuseStep 2781641 = 2086231) B2086231
theorem B4174379 : Blo 1853628 4174379 := bstep (se 1 (by rfl) ⟨3130784, by rfl⟩ : syracuseStep 4174379 = 6261569) B6261569
theorem B3519035 : Blo 1853628 3519035 := bstep (se 1 (by rfl) ⟨2639276, by rfl⟩ : syracuseStep 3519035 = 5278553) B5278553
theorem B2781755 : Blo 1853628 2781755 := bstep (se 1 (by rfl) ⟨2086316, by rfl⟩ : syracuseStep 2781755 = 4172633) B4172633
theorem B2781815 : Blo 1853628 2781815 := bstep (se 1 (by rfl) ⟨2086361, by rfl⟩ : syracuseStep 2781815 = 4172723) B4172723
theorem B9392759 : Blo 1853628 9392759 := bstep (se 1 (by rfl) ⟨7044569, by rfl⟩ : syracuseStep 9392759 = 14089139) B14089139
theorem B2085511 : Blo 1853628 2085511 := bstep (se 1 (by rfl) ⟨1564133, by rfl⟩ : syracuseStep 2085511 = 3128267) B3128267
theorem B2781839 : Blo 1853628 2781839 := bstep (se 1 (by rfl) ⟨2086379, by rfl⟩ : syracuseStep 2781839 = 4172759) B4172759
theorem B2781881 : Blo 1853628 2781881 := bstep (se 2 (by rfl) ⟨1043205, by rfl⟩ : syracuseStep 2781881 = 2086411) B2086411
theorem B2781959 : Blo 1853628 2781959 := bstep (se 1 (by rfl) ⟨2086469, by rfl⟩ : syracuseStep 2781959 = 4172939) B4172939
theorem B2781995 : Blo 1853628 2781995 := bstep (se 1 (by rfl) ⟨2086496, by rfl⟩ : syracuseStep 2781995 = 4172993) B4172993
theorem B2085691 : Blo 1853628 2085691 := bstep (se 1 (by rfl) ⟨1564268, by rfl⟩ : syracuseStep 2085691 = 3128537) B3128537
theorem B2782025 : Blo 1853628 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B4174739 : Blo 1853628 4174739 := bstep (se 1 (by rfl) ⟨3131054, by rfl⟩ : syracuseStep 4174739 = 6262109) B6262109
theorem B71291825 : Blo 1853628 71291825 := bstep (se 2 (by rfl) ⟨26734434, by rfl⟩ : syracuseStep 71291825 = 53468869) B53468869
theorem B2782139 : Blo 1853628 2782139 := bstep (se 1 (by rfl) ⟨2086604, by rfl⟩ : syracuseStep 2782139 = 4173209) B4173209
theorem B4174793 : Blo 1853628 4174793 := bstep (se 2 (by rfl) ⟨1565547, by rfl⟩ : syracuseStep 4174793 = 3131095) B3131095
theorem B2782199 : Blo 1853628 2782199 := bstep (se 1 (by rfl) ⟨2086649, by rfl⟩ : syracuseStep 2782199 = 4173299) B4173299
theorem B2348023 : Blo 1853628 2348023 := bstep (se 1 (by rfl) ⟨1761017, by rfl⟩ : syracuseStep 2348023 = 3522035) B3522035
theorem B2782223 : Blo 1853628 2782223 := bstep (se 1 (by rfl) ⟨2086667, by rfl⟩ : syracuseStep 2782223 = 4173335) B4173335
theorem B9384983 : Blo 1853628 9384983 := bstep (se 1 (by rfl) ⟨7038737, by rfl⟩ : syracuseStep 9384983 = 14077475) B14077475
theorem B3519521 : Blo 1853628 3519521 := bstep (se 2 (by rfl) ⟨1319820, by rfl⟩ : syracuseStep 3519521 = 2639641) B2639641
theorem B2782265 : Blo 1853628 2782265 := bstep (se 2 (by rfl) ⟨1043349, by rfl⟩ : syracuseStep 2782265 = 2086699) B2086699
theorem B104297603 : Blo 1853628 104297603 := bstep (se 1 (by rfl) ⟨78223202, by rfl⟩ : syracuseStep 104297603 = 156446405) B156446405
theorem B2782343 : Blo 1853628 2782343 := bstep (se 1 (by rfl) ⟨2086757, by rfl⟩ : syracuseStep 2782343 = 4173515) B4173515
theorem B2782379 : Blo 1853628 2782379 := bstep (se 1 (by rfl) ⟨2086784, by rfl⟩ : syracuseStep 2782379 = 4173569) B4173569
theorem B2782409 : Blo 1853628 2782409 := bstep (se 2 (by rfl) ⟨1043403, by rfl⟩ : syracuseStep 2782409 = 2086807) B2086807
theorem B7517441 : Blo 1853628 7517441 := bstep (se 2 (by rfl) ⟨2819040, by rfl⟩ : syracuseStep 7517441 = 5638081) B5638081
theorem B2086159 : Blo 1853628 2086159 := bstep (se 1 (by rfl) ⟨1564619, by rfl⟩ : syracuseStep 2086159 = 3129239) B3129239
theorem B3519787 : Blo 1853628 3519787 := bstep (se 1 (by rfl) ⟨2639840, by rfl⟩ : syracuseStep 3519787 = 5279681) B5279681
theorem B2782523 : Blo 1853628 2782523 := bstep (se 1 (by rfl) ⟨2086892, by rfl⟩ : syracuseStep 2782523 = 4173785) B4173785
theorem B2348347 : Blo 1853628 2348347 := bstep (se 1 (by rfl) ⟨1761260, by rfl⟩ : syracuseStep 2348347 = 3522521) B3522521
theorem B5281139 : Blo 1853628 5281139 := bstep (se 1 (by rfl) ⟨3960854, by rfl⟩ : syracuseStep 5281139 = 7921709) B7921709
theorem B2782583 : Blo 1853628 2782583 := bstep (se 1 (by rfl) ⟨2086937, by rfl⟩ : syracuseStep 2782583 = 4173875) B4173875
theorem B6256007 : Blo 1853628 6256007 := bstep (se 1 (by rfl) ⟨4692005, by rfl⟩ : syracuseStep 6256007 = 9384011) B9384011
theorem B2782607 : Blo 1853628 2782607 := bstep (se 1 (by rfl) ⟨2086955, by rfl⟩ : syracuseStep 2782607 = 4173911) B4173911
theorem B8910233 : Blo 1853628 8910233 := bstep (se 2 (by rfl) ⟨3341337, by rfl⟩ : syracuseStep 8910233 = 6682675) B6682675
theorem B2782649 : Blo 1853628 2782649 := bstep (se 2 (by rfl) ⟨1043493, by rfl⟩ : syracuseStep 2782649 = 2086987) B2086987
theorem B2782727 : Blo 1853628 2782727 := bstep (se 1 (by rfl) ⟨2087045, by rfl⟩ : syracuseStep 2782727 = 4174091) B4174091
theorem B2782763 : Blo 1853628 2782763 := bstep (se 1 (by rfl) ⟨2087072, by rfl⟩ : syracuseStep 2782763 = 4174145) B4174145
theorem B9393731 : Blo 1853628 9393731 := bstep (se 1 (by rfl) ⟨7045298, by rfl⟩ : syracuseStep 9393731 = 14090597) B14090597
theorem B2782793 : Blo 1853628 2782793 := bstep (se 2 (by rfl) ⟨1043547, by rfl⟩ : syracuseStep 2782793 = 2087095) B2087095
theorem B2782907 : Blo 1853628 2782907 := bstep (se 1 (by rfl) ⟨2087180, by rfl⟩ : syracuseStep 2782907 = 4174361) B4174361
theorem B18314981 : Blo 1853628 18314981 := bstep (se 4 (by rfl) ⟨1717029, by rfl⟩ : syracuseStep 18314981 = 3434059) B3434059
theorem B2782967 : Blo 1853628 2782967 := bstep (se 1 (by rfl) ⟨2087225, by rfl⟩ : syracuseStep 2782967 = 4174451) B4174451
theorem B6256385 : Blo 1853628 6256385 := bstep (se 2 (by rfl) ⟨2346144, by rfl⟩ : syracuseStep 6256385 = 4692289) B4692289
theorem B5281537 : Blo 1853628 5281537 := bstep (se 2 (by rfl) ⟨1980576, by rfl⟩ : syracuseStep 5281537 = 3961153) B3961153
theorem B2086663 : Blo 1853628 2086663 := bstep (se 1 (by rfl) ⟨1564997, by rfl⟩ : syracuseStep 2086663 = 3129995) B3129995
theorem B1980175 : Blo 1853628 1980175 := bstep (se 1 (by rfl) ⟨1485131, by rfl⟩ : syracuseStep 1980175 = 2970263) B2970263
theorem B2782991 : Blo 1853628 2782991 := bstep (se 1 (by rfl) ⟨2087243, by rfl⟩ : syracuseStep 2782991 = 4174487) B4174487
theorem B3962639 : Blo 1853628 3962639 := bstep (se 1 (by rfl) ⟨2971979, by rfl⟩ : syracuseStep 3962639 = 5943959) B5943959
theorem B3962657 : Blo 1853628 3962657 := bstep (se 2 (by rfl) ⟨1485996, by rfl⟩ : syracuseStep 3962657 = 2971993) B2971993
theorem B2783033 : Blo 1853628 2783033 := bstep (se 2 (by rfl) ⟨1043637, by rfl⟩ : syracuseStep 2783033 = 2087275) B2087275
theorem B5281595 : Blo 1853628 5281595 := bstep (se 1 (by rfl) ⟨3961196, by rfl⟩ : syracuseStep 5281595 = 7922393) B7922393
theorem B4454279 : Blo 1853628 4454279 := bstep (se 1 (by rfl) ⟨3340709, by rfl⟩ : syracuseStep 4454279 = 6681419) B6681419
theorem B2783111 : Blo 1853628 2783111 := bstep (se 1 (by rfl) ⟨2087333, by rfl⟩ : syracuseStep 2783111 = 4174667) B4174667
theorem B9394055 : Blo 1853628 9394055 := bstep (se 1 (by rfl) ⟨7045541, by rfl⟩ : syracuseStep 9394055 = 14091083) B14091083
theorem B2783147 : Blo 1853628 2783147 := bstep (se 1 (by rfl) ⟨2087360, by rfl⟩ : syracuseStep 2783147 = 4174721) B4174721
theorem B2086843 : Blo 1853628 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B2783177 : Blo 1853628 2783177 := bstep (se 2 (by rfl) ⟨1043691, by rfl⟩ : syracuseStep 2783177 = 2087383) B2087383
theorem B10565579 : Blo 1853628 10565579 := bstep (se 1 (by rfl) ⟨7924184, by rfl⟩ : syracuseStep 10565579 = 15848369) B15848369
theorem B22566923 : Blo 1853628 22566923 := bstep (se 1 (by rfl) ⟨16925192, by rfl⟩ : syracuseStep 22566923 = 33850385) B33850385
theorem B54220823 : Blo 1853628 54220823 := bstep (se 1 (by rfl) ⟨40665617, by rfl⟩ : syracuseStep 54220823 = 81331235) B81331235
theorem B2783291 : Blo 1853628 2783291 := bstep (se 1 (by rfl) ⟨2087468, by rfl⟩ : syracuseStep 2783291 = 4174937) B4174937
theorem B3962999 : Blo 1853628 3962999 := bstep (se 1 (by rfl) ⟨2972249, by rfl⟩ : syracuseStep 3962999 = 5944499) B5944499
theorem B2783351 : Blo 1853628 2783351 := bstep (se 1 (by rfl) ⟨2087513, by rfl⟩ : syracuseStep 2783351 = 4175027) B4175027
theorem B1980551 : Blo 1853628 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B2783375 : Blo 1853628 2783375 := bstep (se 1 (by rfl) ⟨2087531, by rfl⟩ : syracuseStep 2783375 = 4175063) B4175063
theorem B2783417 : Blo 1853628 2783417 := bstep (se 2 (by rfl) ⟨1043781, by rfl⟩ : syracuseStep 2783417 = 2087563) B2087563
theorem B2676983 : Blo 1853628 2676983 := bstep (se 1 (by rfl) ⟨2007737, by rfl⟩ : syracuseStep 2676983 = 4015475) B4015475
theorem B4692239 : Blo 1853628 4692239 := bstep (se 1 (by rfl) ⟨3519179, by rfl⟩ : syracuseStep 4692239 = 7038359) B7038359
theorem B14080391 : Blo 1853628 14080391 := bstep (se 1 (by rfl) ⟨10560293, by rfl⟩ : syracuseStep 14080391 = 21120587) B21120587
theorem B3520903 : Blo 1853628 3520903 := bstep (se 1 (by rfl) ⟨2640677, by rfl⟩ : syracuseStep 3520903 = 5281355) B5281355
theorem B2087311 : Blo 1853628 2087311 := bstep (se 1 (by rfl) ⟨1565483, by rfl⟩ : syracuseStep 2087311 = 3130967) B3130967
theorem B10566035 : Blo 1853628 10566035 := bstep (se 1 (by rfl) ⟨7924526, by rfl⟩ : syracuseStep 10566035 = 15849053) B15849053
theorem B7043537 : Blo 1853628 7043537 := bstep (se 2 (by rfl) ⟨2641326, by rfl⟩ : syracuseStep 7043537 = 5282653) B5282653
theorem B6257195 : Blo 1853628 6257195 := bstep (se 1 (by rfl) ⟨4692896, by rfl⟩ : syracuseStep 6257195 = 9385793) B9385793
theorem B8911403 : Blo 1853628 8911403 := bstep (se 1 (by rfl) ⟨6683552, by rfl⟩ : syracuseStep 8911403 = 13367105) B13367105
theorem B32119361 : Blo 1853628 32119361 := bstep (se 2 (by rfl) ⟨12044760, by rfl⟩ : syracuseStep 32119361 = 24089521) B24089521
theorem B7043993 : Blo 1853628 7043993 := bstep (se 2 (by rfl) ⟨2641497, by rfl⟩ : syracuseStep 7043993 = 5282995) B5282995
theorem B3521465 : Blo 1853628 3521465 := bstep (se 2 (by rfl) ⟨1320549, by rfl⟩ : syracuseStep 3521465 = 2641099) B2641099
theorem B4692937 : Blo 1853628 4692937 := bstep (se 2 (by rfl) ⟨1759851, by rfl⟩ : syracuseStep 4692937 = 3519703) B3519703
theorem B2677705 : Blo 1853628 2677705 := bstep (se 2 (by rfl) ⟨1004139, by rfl⟩ : syracuseStep 2677705 = 2008279) B2008279
theorem B4693079 : Blo 1853628 4693079 := bstep (se 1 (by rfl) ⟨3519809, by rfl⟩ : syracuseStep 4693079 = 7039619) B7039619
theorem B3759223 : Blo 1853628 3759223 := bstep (se 1 (by rfl) ⟨2819417, by rfl⟩ : syracuseStep 3759223 = 5638835) B5638835
theorem B3341459 : Blo 1853628 3341459 := bstep (se 1 (by rfl) ⟨2506094, by rfl⟩ : syracuseStep 3341459 = 5012189) B5012189
theorem B11304137 : Blo 1853628 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B2227447 : Blo 1853628 2227447 := bstep (se 1 (by rfl) ⟨1670585, by rfl⟩ : syracuseStep 2227447 = 3341171) B3341171
theorem B3128591 : Blo 1853628 3128591 := bstep (se 1 (by rfl) ⟨2346443, by rfl⟩ : syracuseStep 3128591 = 4692887) B4692887
theorem B33840443 : Blo 1853628 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B21405059 : Blo 1853628 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B13549133 : Blo 1853628 13549133 := bstep (se 3 (by rfl) ⟨2540462, by rfl⟩ : syracuseStep 13549133 = 5080925) B5080925
theorem B41197157 : Blo 1853628 41197157 := bstep (se 4 (by rfl) ⟨3862233, by rfl⟩ : syracuseStep 41197157 = 7724467) B7724467
theorem B3129131 : Blo 1853628 3129131 := bstep (se 1 (by rfl) ⟨2346848, by rfl⟩ : syracuseStep 3129131 = 4693697) B4693697
theorem B6258491 : Blo 1853628 6258491 := bstep (se 1 (by rfl) ⟨4693868, by rfl⟩ : syracuseStep 6258491 = 9387737) B9387737
theorem B6258707 : Blo 1853628 6258707 := bstep (se 1 (by rfl) ⟨4694030, by rfl⟩ : syracuseStep 6258707 = 9388061) B9388061
theorem B3129401 : Blo 1853628 3129401 := bstep (se 2 (by rfl) ⟨1173525, by rfl⟩ : syracuseStep 3129401 = 2347051) B2347051
theorem B7045177 : Blo 1853628 7045177 := bstep (se 2 (by rfl) ⟨2641941, by rfl⟩ : syracuseStep 7045177 = 5283883) B5283883
theorem B16064675 : Blo 1853628 16064675 := bstep (se 1 (by rfl) ⟨12048506, by rfl⟩ : syracuseStep 16064675 = 24097013) B24097013
theorem B6259031 : Blo 1853628 6259031 := bstep (se 1 (by rfl) ⟨4694273, by rfl⟩ : syracuseStep 6259031 = 9388547) B9388547
theorem B278126941 : Blo 1853628 278126941 := bstep (se 3 (by rfl) ⟨52148801, by rfl⟩ : syracuseStep 278126941 = 104297603) B104297603
theorem B7045481 : Blo 1853628 7045481 := bstep (se 2 (by rfl) ⟨2642055, by rfl⟩ : syracuseStep 7045481 = 5284111) B5284111
theorem B3342779 : Blo 1853628 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B4694537 : Blo 1853628 4694537 := bstep (se 2 (by rfl) ⟨1760451, by rfl⟩ : syracuseStep 4694537 = 3520903) B3520903
theorem B2818639 : Blo 1853628 2818639 := bstep (se 1 (by rfl) ⟨2113979, by rfl⟩ : syracuseStep 2818639 = 4227959) B4227959
theorem B9036497 : Blo 1853628 9036497 := bstep (se 2 (by rfl) ⟨3388686, by rfl⟩ : syracuseStep 9036497 = 6777373) B6777373
theorem B3130103 : Blo 1853628 3130103 := bstep (se 1 (by rfl) ⟨2347577, by rfl⟩ : syracuseStep 3130103 = 4695155) B4695155
theorem B4170671 : Blo 1853628 4170671 := bstep (se 1 (by rfl) ⟨3128003, by rfl⟩ : syracuseStep 4170671 = 6256007) B6256007
theorem B5940155 : Blo 1853628 5940155 := bstep (se 1 (by rfl) ⟨4455116, by rfl⟩ : syracuseStep 5940155 = 8910233) B8910233
theorem B2229211 : Blo 1853628 2229211 := bstep (se 1 (by rfl) ⟨1671908, by rfl⟩ : syracuseStep 2229211 = 3343817) B3343817
theorem B13370447 : Blo 1853628 13370447 := bstep (se 1 (by rfl) ⟨10027835, by rfl⟩ : syracuseStep 13370447 = 20055671) B20055671
theorem B3130447 : Blo 1853628 3130447 := bstep (se 1 (by rfl) ⟨2347835, by rfl⟩ : syracuseStep 3130447 = 4695671) B4695671
theorem B4170923 : Blo 1853628 4170923 := bstep (se 1 (by rfl) ⟨3128192, by rfl⟩ : syracuseStep 4170923 = 6256385) B6256385
theorem B54224113 : Blo 1853628 54224113 := bstep (se 2 (by rfl) ⟨20334042, by rfl⟩ : syracuseStep 54224113 = 40668085) B40668085
theorem B3130697 : Blo 1853628 3130697 := bstep (se 2 (by rfl) ⟨1174011, by rfl⟩ : syracuseStep 3130697 = 2348023) B2348023
theorem B6260111 : Blo 1853628 6260111 := bstep (se 1 (by rfl) ⟨4695083, by rfl⟩ : syracuseStep 6260111 = 9390167) B9390167
theorem B35661221 : Blo 1853628 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B15042145 : Blo 1853628 15042145 := bstep (se 2 (by rfl) ⟨5640804, by rfl⟩ : syracuseStep 15042145 = 11281609) B11281609
theorem B9029243 : Blo 1853628 9029243 := bstep (se 1 (by rfl) ⟨6771932, by rfl⟩ : syracuseStep 9029243 = 13543865) B13543865
theorem B4695691 : Blo 1853628 4695691 := bstep (se 1 (by rfl) ⟨3521768, by rfl⟩ : syracuseStep 4695691 = 7043537) B7043537
theorem B9520787 : Blo 1853628 9520787 := bstep (se 1 (by rfl) ⟨7140590, by rfl⟩ : syracuseStep 9520787 = 14281181) B14281181
theorem B4171463 : Blo 1853628 4171463 := bstep (se 1 (by rfl) ⟨3128597, by rfl⟩ : syracuseStep 4171463 = 6257195) B6257195
theorem B5940935 : Blo 1853628 5940935 := bstep (se 1 (by rfl) ⟨4455701, by rfl⟩ : syracuseStep 5940935 = 8911403) B8911403
theorem B6260435 : Blo 1853628 6260435 := bstep (se 1 (by rfl) ⟨4695326, by rfl⟩ : syracuseStep 6260435 = 9390653) B9390653
theorem B3131129 : Blo 1853628 3131129 := bstep (se 2 (by rfl) ⟨1174173, by rfl⟩ : syracuseStep 3131129 = 2348347) B2348347
theorem B3131311 : Blo 1853628 3131311 := bstep (se 1 (by rfl) ⟨2348483, by rfl⟩ : syracuseStep 3131311 = 4696967) B4696967
theorem B4695995 : Blo 1853628 4695995 := bstep (se 1 (by rfl) ⟨3521996, by rfl⟩ : syracuseStep 4695995 = 7043993) B7043993
theorem B17827877 : Blo 1853628 17827877 := bstep (se 4 (by rfl) ⟨1671363, by rfl⟩ : syracuseStep 17827877 = 3342727) B3342727
theorem B7039133 : Blo 1853628 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B1853639 : Blo 1853628 1853639 := bstep (se 1 (by rfl) ⟨1390229, by rfl⟩ : syracuseStep 1853639 = 2780459) B2780459
theorem B1853659 : Blo 1853628 1853659 := bstep (se 1 (by rfl) ⟨1390244, by rfl⟩ : syracuseStep 1853659 = 2780489) B2780489
theorem B1853735 : Blo 1853628 1853735 := bstep (se 1 (by rfl) ⟨1390301, by rfl⟩ : syracuseStep 1853735 = 2780603) B2780603
theorem B1853775 : Blo 1853628 1853775 := bstep (se 1 (by rfl) ⟨1390331, by rfl⟩ : syracuseStep 1853775 = 2780663) B2780663
theorem B1853791 : Blo 1853628 1853791 := bstep (se 1 (by rfl) ⟨1390343, by rfl⟩ : syracuseStep 1853791 = 2780687) B2780687
theorem B2640233 : Blo 1853628 2640233 := bstep (se 2 (by rfl) ⟨990087, by rfl⟩ : syracuseStep 2640233 = 1980175) B1980175
theorem B5081449 : Blo 1853628 5081449 := bstep (se 2 (by rfl) ⟨1905543, by rfl⟩ : syracuseStep 5081449 = 3811087) B3811087
theorem B1853819 : Blo 1853628 1853819 := bstep (se 1 (by rfl) ⟨1390364, by rfl⟩ : syracuseStep 1853819 = 2780729) B2780729
theorem B14281093 : Blo 1853628 14281093 := bstep (se 4 (by rfl) ⟨1338852, by rfl⟩ : syracuseStep 14281093 = 2677705) B2677705
theorem B1853871 : Blo 1853628 1853871 := bstep (se 1 (by rfl) ⟨1390403, by rfl⟩ : syracuseStep 1853871 = 2780807) B2780807
theorem B1853895 : Blo 1853628 1853895 := bstep (se 1 (by rfl) ⟨1390421, by rfl⟩ : syracuseStep 1853895 = 2780843) B2780843
theorem B1853915 : Blo 1853628 1853915 := bstep (se 1 (by rfl) ⟨1390436, by rfl⟩ : syracuseStep 1853915 = 2780873) B2780873
theorem B115763741 : Blo 1853628 115763741 := bstep (se 3 (by rfl) ⟨21705701, by rfl⟩ : syracuseStep 115763741 = 43411403) B43411403
theorem B1853991 : Blo 1853628 1853991 := bstep (se 1 (by rfl) ⟨1390493, by rfl⟩ : syracuseStep 1853991 = 2780987) B2780987
theorem B4172327 : Blo 1853628 4172327 := bstep (se 1 (by rfl) ⟨3129245, by rfl⟩ : syracuseStep 4172327 = 6258491) B6258491
theorem B1854031 : Blo 1853628 1854031 := bstep (se 1 (by rfl) ⟨1390523, by rfl⟩ : syracuseStep 1854031 = 2781047) B2781047
theorem B1854047 : Blo 1853628 1854047 := bstep (se 1 (by rfl) ⟨1390535, by rfl⟩ : syracuseStep 1854047 = 2781071) B2781071
theorem B4229729 : Blo 1853628 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B1854075 : Blo 1853628 1854075 := bstep (se 1 (by rfl) ⟨1390556, by rfl⟩ : syracuseStep 1854075 = 2781113) B2781113
theorem B7522955 : Blo 1853628 7522955 := bstep (se 1 (by rfl) ⟨5642216, by rfl⟩ : syracuseStep 7522955 = 11284433) B11284433
theorem B1854127 : Blo 1853628 1854127 := bstep (se 1 (by rfl) ⟨1390595, by rfl⟩ : syracuseStep 1854127 = 2781191) B2781191
theorem B1854151 : Blo 1853628 1854151 := bstep (se 1 (by rfl) ⟨1390613, by rfl⟩ : syracuseStep 1854151 = 2781227) B2781227
theorem B4696775 : Blo 1853628 4696775 := bstep (se 1 (by rfl) ⟨3522581, by rfl⟩ : syracuseStep 4696775 = 7045163) B7045163
theorem B1854171 : Blo 1853628 1854171 := bstep (se 1 (by rfl) ⟨1390628, by rfl⟩ : syracuseStep 1854171 = 2781257) B2781257
theorem B4696825 : Blo 1853628 4696825 := bstep (se 2 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 4696825 = 3522619) B3522619
theorem B1854247 : Blo 1853628 1854247 := bstep (se 1 (by rfl) ⟨1390685, by rfl⟩ : syracuseStep 1854247 = 2781371) B2781371
theorem B7039817 : Blo 1853628 7039817 := bstep (se 2 (by rfl) ⟨2639931, by rfl⟩ : syracuseStep 7039817 = 5279863) B5279863
theorem B1854287 : Blo 1853628 1854287 := bstep (se 1 (by rfl) ⟨1390715, by rfl⟩ : syracuseStep 1854287 = 2781431) B2781431
theorem B1854303 : Blo 1853628 1854303 := bstep (se 1 (by rfl) ⟨1390727, by rfl⟩ : syracuseStep 1854303 = 2781455) B2781455
theorem B2411371 : Blo 1853628 2411371 := bstep (se 1 (by rfl) ⟨1808528, by rfl⟩ : syracuseStep 2411371 = 3617057) B3617057
theorem B4172651 : Blo 1853628 4172651 := bstep (se 1 (by rfl) ⟨3129488, by rfl⟩ : syracuseStep 4172651 = 6258977) B6258977
theorem B6261623 : Blo 1853628 6261623 := bstep (se 1 (by rfl) ⟨4696217, by rfl⟩ : syracuseStep 6261623 = 9392435) B9392435
theorem B1854331 : Blo 1853628 1854331 := bstep (se 1 (by rfl) ⟨1390748, by rfl⟩ : syracuseStep 1854331 = 2781497) B2781497
theorem B4172705 : Blo 1853628 4172705 := bstep (se 2 (by rfl) ⟨1564764, by rfl⟩ : syracuseStep 4172705 = 3129529) B3129529
theorem B1854383 : Blo 1853628 1854383 := bstep (se 1 (by rfl) ⟨1390787, by rfl⟩ : syracuseStep 1854383 = 2781575) B2781575
theorem B60173239 : Blo 1853628 60173239 := bstep (se 1 (by rfl) ⟨45129929, by rfl⟩ : syracuseStep 60173239 = 90259859) B90259859
theorem B1854407 : Blo 1853628 1854407 := bstep (se 1 (by rfl) ⟨1390805, by rfl⟩ : syracuseStep 1854407 = 2781611) B2781611
theorem B1854427 : Blo 1853628 1854427 := bstep (se 1 (by rfl) ⟨1390820, by rfl⟩ : syracuseStep 1854427 = 2781641) B2781641
theorem B2346023 : Blo 1853628 2346023 := bstep (se 1 (by rfl) ⟨1759517, by rfl⟩ : syracuseStep 2346023 = 3519035) B3519035
theorem B1854503 : Blo 1853628 1854503 := bstep (se 1 (by rfl) ⟨1390877, by rfl⟩ : syracuseStep 1854503 = 2781755) B2781755
theorem B1854543 : Blo 1853628 1854543 := bstep (se 1 (by rfl) ⟨1390907, by rfl⟩ : syracuseStep 1854543 = 2781815) B2781815
theorem B6261839 : Blo 1853628 6261839 := bstep (se 1 (by rfl) ⟨4696379, by rfl⟩ : syracuseStep 6261839 = 9392759) B9392759
theorem B1854559 : Blo 1853628 1854559 := bstep (se 1 (by rfl) ⟨1390919, by rfl⟩ : syracuseStep 1854559 = 2781839) B2781839
theorem B1854587 : Blo 1853628 1854587 := bstep (se 1 (by rfl) ⟨1390940, by rfl⟩ : syracuseStep 1854587 = 2781881) B2781881
theorem B1854639 : Blo 1853628 1854639 := bstep (se 1 (by rfl) ⟨1390979, by rfl⟩ : syracuseStep 1854639 = 2781959) B2781959
theorem B1854663 : Blo 1853628 1854663 := bstep (se 1 (by rfl) ⟨1390997, by rfl⟩ : syracuseStep 1854663 = 2781995) B2781995
theorem B1854683 : Blo 1853628 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B4173047 : Blo 1853628 4173047 := bstep (se 1 (by rfl) ⟨3129785, by rfl⟩ : syracuseStep 4173047 = 6259571) B6259571
theorem B1854759 : Blo 1853628 1854759 := bstep (se 1 (by rfl) ⟨1391069, by rfl⟩ : syracuseStep 1854759 = 2782139) B2782139
theorem B7040317 : Blo 1853628 7040317 := bstep (se 3 (by rfl) ⟨1320059, by rfl⟩ : syracuseStep 7040317 = 2640119) B2640119
theorem B7138621 : Blo 1853628 7138621 := bstep (se 3 (by rfl) ⟨1338491, by rfl⟩ : syracuseStep 7138621 = 2676983) B2676983
theorem B1854799 : Blo 1853628 1854799 := bstep (se 1 (by rfl) ⟨1391099, by rfl⟩ : syracuseStep 1854799 = 2782199) B2782199
theorem B1854815 : Blo 1853628 1854815 := bstep (se 1 (by rfl) ⟨1391111, by rfl⟩ : syracuseStep 1854815 = 2782223) B2782223
theorem B2346347 : Blo 1853628 2346347 := bstep (se 1 (by rfl) ⟨1759760, by rfl⟩ : syracuseStep 2346347 = 3519521) B3519521
theorem B1854843 : Blo 1853628 1854843 := bstep (se 1 (by rfl) ⟨1391132, by rfl⟩ : syracuseStep 1854843 = 2782265) B2782265
theorem B2780591 : Blo 1853628 2780591 := bstep (se 1 (by rfl) ⟨2085443, by rfl⟩ : syracuseStep 2780591 = 4170887) B4170887
theorem B1854895 : Blo 1853628 1854895 := bstep (se 1 (by rfl) ⟨1391171, by rfl⟩ : syracuseStep 1854895 = 2782343) B2782343
theorem B1854919 : Blo 1853628 1854919 := bstep (se 1 (by rfl) ⟨1391189, by rfl⟩ : syracuseStep 1854919 = 2782379) B2782379
theorem B5942729 : Blo 1853628 5942729 := bstep (se 2 (by rfl) ⟨2228523, by rfl⟩ : syracuseStep 5942729 = 4457047) B4457047
theorem B6262217 : Blo 1853628 6262217 := bstep (se 2 (by rfl) ⟨2348331, by rfl⟩ : syracuseStep 6262217 = 4696663) B4696663
theorem B1854939 : Blo 1853628 1854939 := bstep (se 1 (by rfl) ⟨1391204, by rfl⟩ : syracuseStep 1854939 = 2782409) B2782409
theorem B2780681 : Blo 1853628 2780681 := bstep (se 2 (by rfl) ⟨1042755, by rfl⟩ : syracuseStep 2780681 = 2085511) B2085511
theorem B2780711 : Blo 1853628 2780711 := bstep (se 1 (by rfl) ⟨2085533, by rfl⟩ : syracuseStep 2780711 = 4171067) B4171067
theorem B1855015 : Blo 1853628 1855015 := bstep (se 1 (by rfl) ⟨1391261, by rfl⟩ : syracuseStep 1855015 = 2782523) B2782523
theorem B1855055 : Blo 1853628 1855055 := bstep (se 1 (by rfl) ⟨1391291, by rfl⟩ : syracuseStep 1855055 = 2782583) B2782583
theorem B1855071 : Blo 1853628 1855071 := bstep (se 1 (by rfl) ⟨1391303, by rfl⟩ : syracuseStep 1855071 = 2782607) B2782607
theorem B2780795 : Blo 1853628 2780795 := bstep (se 1 (by rfl) ⟨2085596, by rfl⟩ : syracuseStep 2780795 = 4171193) B4171193
theorem B1855099 : Blo 1853628 1855099 := bstep (se 1 (by rfl) ⟨1391324, by rfl⟩ : syracuseStep 1855099 = 2782649) B2782649
theorem B1855151 : Blo 1853628 1855151 := bstep (se 1 (by rfl) ⟨1391363, by rfl⟩ : syracuseStep 1855151 = 2782727) B2782727
theorem B1855175 : Blo 1853628 1855175 := bstep (se 1 (by rfl) ⟨1391381, by rfl⟩ : syracuseStep 1855175 = 2782763) B2782763
theorem B6262487 : Blo 1853628 6262487 := bstep (se 1 (by rfl) ⟨4696865, by rfl⟩ : syracuseStep 6262487 = 9393731) B9393731
theorem B1855195 : Blo 1853628 1855195 := bstep (se 1 (by rfl) ⟨1391396, by rfl⟩ : syracuseStep 1855195 = 2782793) B2782793
theorem B2780921 : Blo 1853628 2780921 := bstep (se 2 (by rfl) ⟨1042845, by rfl⟩ : syracuseStep 2780921 = 2085691) B2085691
theorem B1855271 : Blo 1853628 1855271 := bstep (se 1 (by rfl) ⟨1391453, by rfl⟩ : syracuseStep 1855271 = 2782907) B2782907
theorem B10563371 : Blo 1853628 10563371 := bstep (se 1 (by rfl) ⟨7922528, by rfl⟩ : syracuseStep 10563371 = 15845057) B15845057
theorem B12209987 : Blo 1853628 12209987 := bstep (se 1 (by rfl) ⟨9157490, by rfl⟩ : syracuseStep 12209987 = 18314981) B18314981
theorem B4173641 : Blo 1853628 4173641 := bstep (se 2 (by rfl) ⟨1565115, by rfl⟩ : syracuseStep 4173641 = 3130231) B3130231
theorem B1855311 : Blo 1853628 1855311 := bstep (se 1 (by rfl) ⟨1391483, by rfl⟩ : syracuseStep 1855311 = 2782967) B2782967
theorem B2781023 : Blo 1853628 2781023 := bstep (se 1 (by rfl) ⟨2085767, by rfl⟩ : syracuseStep 2781023 = 4171535) B4171535
theorem B1855327 : Blo 1853628 1855327 := bstep (se 1 (by rfl) ⟨1391495, by rfl⟩ : syracuseStep 1855327 = 2782991) B2782991
theorem B2781035 : Blo 1853628 2781035 := bstep (se 1 (by rfl) ⟨2085776, by rfl⟩ : syracuseStep 2781035 = 4171553) B4171553
theorem B2641771 : Blo 1853628 2641771 := bstep (se 1 (by rfl) ⟨1981328, by rfl⟩ : syracuseStep 2641771 = 3962657) B3962657
theorem B1855355 : Blo 1853628 1855355 := bstep (se 1 (by rfl) ⟨1391516, by rfl⟩ : syracuseStep 1855355 = 2783033) B2783033
theorem B21114755 : Blo 1853628 21114755 := bstep (se 1 (by rfl) ⟨15836066, by rfl⟩ : syracuseStep 21114755 = 31672133) B31672133
theorem B2969519 : Blo 1853628 2969519 := bstep (se 1 (by rfl) ⟨2227139, by rfl⟩ : syracuseStep 2969519 = 4454279) B4454279
theorem B1855407 : Blo 1853628 1855407 := bstep (se 1 (by rfl) ⟨1391555, by rfl⟩ : syracuseStep 1855407 = 2783111) B2783111
theorem B6262703 : Blo 1853628 6262703 := bstep (se 1 (by rfl) ⟨4697027, by rfl⟩ : syracuseStep 6262703 = 9394055) B9394055
theorem B16912313 : Blo 1853628 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B1855431 : Blo 1853628 1855431 := bstep (se 1 (by rfl) ⟨1391573, by rfl⟩ : syracuseStep 1855431 = 2783147) B2783147
theorem B1855451 : Blo 1853628 1855451 := bstep (se 1 (by rfl) ⟨1391588, by rfl⟩ : syracuseStep 1855451 = 2783177) B2783177
theorem B15044615 : Blo 1853628 15044615 := bstep (se 1 (by rfl) ⟨11283461, by rfl⟩ : syracuseStep 15044615 = 22566923) B22566923
theorem B36147215 : Blo 1853628 36147215 := bstep (se 1 (by rfl) ⟨27110411, by rfl⟩ : syracuseStep 36147215 = 54220823) B54220823
theorem B1855527 : Blo 1853628 1855527 := bstep (se 1 (by rfl) ⟨1391645, by rfl⟩ : syracuseStep 1855527 = 2783291) B2783291
theorem B14463053 : Blo 1853628 14463053 := bstep (se 3 (by rfl) ⟨2711822, by rfl⟩ : syracuseStep 14463053 = 5423645) B5423645
theorem B2781263 : Blo 1853628 2781263 := bstep (se 1 (by rfl) ⟨2085947, by rfl⟩ : syracuseStep 2781263 = 4171895) B4171895
theorem B7516241 : Blo 1853628 7516241 := bstep (se 2 (by rfl) ⟨2818590, by rfl⟩ : syracuseStep 7516241 = 5637181) B5637181
theorem B2641999 : Blo 1853628 2641999 := bstep (se 1 (by rfl) ⟨1981499, by rfl⟩ : syracuseStep 2641999 = 3962999) B3962999
theorem B1855567 : Blo 1853628 1855567 := bstep (se 1 (by rfl) ⟨1391675, by rfl⟩ : syracuseStep 1855567 = 2783351) B2783351
theorem B1855583 : Blo 1853628 1855583 := bstep (se 1 (by rfl) ⟨1391687, by rfl⟩ : syracuseStep 1855583 = 2783375) B2783375
theorem B15839347 : Blo 1853628 15839347 := bstep (se 1 (by rfl) ⟨11879510, by rfl⟩ : syracuseStep 15839347 = 23759021) B23759021
theorem B1855611 : Blo 1853628 1855611 := bstep (se 1 (by rfl) ⟨1391708, by rfl⟩ : syracuseStep 1855611 = 2783417) B2783417
theorem B2781383 : Blo 1853628 2781383 := bstep (se 1 (by rfl) ⟨2086037, by rfl⟩ : syracuseStep 2781383 = 4172075) B4172075
theorem B2969929 : Blo 1853628 2969929 := bstep (se 2 (by rfl) ⟨1113723, by rfl⟩ : syracuseStep 2969929 = 2227447) B2227447
theorem B2781545 : Blo 1853628 2781545 := bstep (se 2 (by rfl) ⟨1043079, by rfl⟩ : syracuseStep 2781545 = 2086159) B2086159
theorem B1880443 : Blo 1853628 1880443 := bstep (se 1 (by rfl) ⟨1410332, by rfl⟩ : syracuseStep 1880443 = 2820665) B2820665
theorem B4518287 : Blo 1853628 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B2257327 : Blo 1853628 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B2781623 : Blo 1853628 2781623 := bstep (se 1 (by rfl) ⟨2086217, by rfl⟩ : syracuseStep 2781623 = 4172435) B4172435
theorem B2781659 : Blo 1853628 2781659 := bstep (se 1 (by rfl) ⟨2086244, by rfl⟩ : syracuseStep 2781659 = 4172489) B4172489
theorem B3961307 : Blo 1853628 3961307 := bstep (se 1 (by rfl) ⟨2970980, by rfl⟩ : syracuseStep 3961307 = 5941961) B5941961
theorem B10564121 : Blo 1853628 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B5280353 : Blo 1853628 5280353 := bstep (se 2 (by rfl) ⟨1980132, by rfl⟩ : syracuseStep 5280353 = 3960265) B3960265
theorem B4174433 : Blo 1853628 4174433 := bstep (se 2 (by rfl) ⟨1565412, by rfl⟩ : syracuseStep 4174433 = 3130825) B3130825
theorem B2347643 : Blo 1853628 2347643 := bstep (se 1 (by rfl) ⟨1760732, by rfl⟩ : syracuseStep 2347643 = 3521465) B3521465
theorem B9384659 : Blo 1853628 9384659 := bstep (se 1 (by rfl) ⟨7038494, by rfl⟩ : syracuseStep 9384659 = 14076989) B14076989
theorem B10711763 : Blo 1853628 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B7516921 : Blo 1853628 7516921 := bstep (se 2 (by rfl) ⟨2818845, by rfl⟩ : syracuseStep 7516921 = 5637691) B5637691
theorem B2085727 : Blo 1853628 2085727 := bstep (se 1 (by rfl) ⟨1564295, by rfl⟩ : syracuseStep 2085727 = 3128591) B3128591
theorem B2782127 : Blo 1853628 2782127 := bstep (se 1 (by rfl) ⟨2086595, by rfl⟩ : syracuseStep 2782127 = 4173191) B4173191
theorem B548606897 : Blo 1853628 548606897 := bstep (se 2 (by rfl) ⟨205727586, by rfl⟩ : syracuseStep 548606897 = 411455173) B411455173
theorem B4174775 : Blo 1853628 4174775 := bstep (se 1 (by rfl) ⟨3131081, by rfl⟩ : syracuseStep 4174775 = 6262163) B6262163
theorem B7042049 : Blo 1853628 7042049 := bstep (se 2 (by rfl) ⟨2640768, by rfl⟩ : syracuseStep 7042049 = 5281537) B5281537
theorem B2782217 : Blo 1853628 2782217 := bstep (se 2 (by rfl) ⟨1043331, by rfl⟩ : syracuseStep 2782217 = 2086663) B2086663
theorem B2782247 : Blo 1853628 2782247 := bstep (se 1 (by rfl) ⟨2086685, by rfl⟩ : syracuseStep 2782247 = 4173371) B4173371
theorem B15840305 : Blo 1853628 15840305 := bstep (se 2 (by rfl) ⟨5940114, by rfl⟩ : syracuseStep 15840305 = 11880229) B11880229
theorem B9032755 : Blo 1853628 9032755 := bstep (se 1 (by rfl) ⟨6774566, by rfl⟩ : syracuseStep 9032755 = 13549133) B13549133
theorem B27464771 : Blo 1853628 27464771 := bstep (se 1 (by rfl) ⟨20598578, by rfl⟩ : syracuseStep 27464771 = 41197157) B41197157
theorem B2782331 : Blo 1853628 2782331 := bstep (se 1 (by rfl) ⟨2086748, by rfl⟩ : syracuseStep 2782331 = 4173497) B4173497
theorem B2086087 : Blo 1853628 2086087 := bstep (se 1 (by rfl) ⟨1564565, by rfl⟩ : syracuseStep 2086087 = 3129131) B3129131
theorem B10024183 : Blo 1853628 10024183 := bstep (se 1 (by rfl) ⟨7518137, by rfl⟩ : syracuseStep 10024183 = 15036275) B15036275
theorem B2782457 : Blo 1853628 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B2782559 : Blo 1853628 2782559 := bstep (se 1 (by rfl) ⟨2086919, by rfl⟩ : syracuseStep 2782559 = 4173839) B4173839
theorem B2782571 : Blo 1853628 2782571 := bstep (se 1 (by rfl) ⟨2086928, by rfl⟩ : syracuseStep 2782571 = 4173857) B4173857
theorem B7918991 : Blo 1853628 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B3519931 : Blo 1853628 3519931 := bstep (se 1 (by rfl) ⟨2639948, by rfl⟩ : syracuseStep 3519931 = 5279897) B5279897
theorem B6256115 : Blo 1853628 6256115 := bstep (se 1 (by rfl) ⟨4692086, by rfl⟩ : syracuseStep 6256115 = 9384173) B9384173
theorem B3520007 : Blo 1853628 3520007 := bstep (se 1 (by rfl) ⟨2640005, by rfl⟩ : syracuseStep 3520007 = 5280011) B5280011
theorem B2782799 : Blo 1853628 2782799 := bstep (se 1 (by rfl) ⟨2087099, by rfl⟩ : syracuseStep 2782799 = 4174199) B4174199
theorem B5281469 : Blo 1853628 5281469 := bstep (se 3 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 5281469 = 1980551) B1980551
theorem B2782919 : Blo 1853628 2782919 := bstep (se 1 (by rfl) ⟨2087189, by rfl⟩ : syracuseStep 2782919 = 4174379) B4174379
theorem B8910557 : Blo 1853628 8910557 := bstep (se 3 (by rfl) ⟨1670729, by rfl⟩ : syracuseStep 8910557 = 3341459) B3341459
theorem B2783081 : Blo 1853628 2783081 := bstep (se 2 (by rfl) ⟨1043655, by rfl⟩ : syracuseStep 2783081 = 2087311) B2087311
theorem B14079905 : Blo 1853628 14079905 := bstep (se 2 (by rfl) ⟨5279964, by rfl⟩ : syracuseStep 14079905 = 10559929) B10559929
theorem B3520417 : Blo 1853628 3520417 := bstep (se 2 (by rfl) ⟨1320156, by rfl⟩ : syracuseStep 3520417 = 2640313) B2640313
theorem B2783159 : Blo 1853628 2783159 := bstep (se 1 (by rfl) ⟨2087369, by rfl⟩ : syracuseStep 2783159 = 4174739) B4174739
theorem B47527883 : Blo 1853628 47527883 := bstep (se 1 (by rfl) ⟨35645912, by rfl⟩ : syracuseStep 47527883 = 71291825) B71291825
theorem B2783195 : Blo 1853628 2783195 := bstep (se 1 (by rfl) ⟨2087396, by rfl⟩ : syracuseStep 2783195 = 4174793) B4174793
theorem B6256655 : Blo 1853628 6256655 := bstep (se 1 (by rfl) ⟨4692491, by rfl⟩ : syracuseStep 6256655 = 9384983) B9384983
theorem B5281811 : Blo 1853628 5281811 := bstep (se 1 (by rfl) ⟨3961358, by rfl⟩ : syracuseStep 5281811 = 7922717) B7922717
theorem B2086951 : Blo 1853628 2086951 := bstep (se 1 (by rfl) ⟨1565213, by rfl⟩ : syracuseStep 2086951 = 3130427) B3130427
theorem B5011627 : Blo 1853628 5011627 := bstep (se 1 (by rfl) ⟨3758720, by rfl⟩ : syracuseStep 5011627 = 7517441) B7517441
theorem B3520759 : Blo 1853628 3520759 := bstep (se 1 (by rfl) ⟨2640569, by rfl⟩ : syracuseStep 3520759 = 5281139) B5281139
theorem B85654037 : Blo 1853628 85654037 := bstep (se 6 (by rfl) ⟨2007516, by rfl⟩ : syracuseStep 85654037 = 4015033) B4015033
theorem B3521063 : Blo 1853628 3521063 := bstep (se 1 (by rfl) ⟨2640797, by rfl⟩ : syracuseStep 3521063 = 5281595) B5281595
theorem B6257249 : Blo 1853628 6257249 := bstep (se 2 (by rfl) ⟨2346468, by rfl⟩ : syracuseStep 6257249 = 4692937) B4692937
theorem B7043719 : Blo 1853628 7043719 := bstep (se 1 (by rfl) ⟨5282789, by rfl⟩ : syracuseStep 7043719 = 10565579) B10565579
theorem B5012297 : Blo 1853628 5012297 := bstep (se 2 (by rfl) ⟨1879611, by rfl⟩ : syracuseStep 5012297 = 3759223) B3759223
theorem B3128159 : Blo 1853628 3128159 := bstep (se 1 (by rfl) ⟨2346119, by rfl⟩ : syracuseStep 3128159 = 4692239) B4692239
theorem B9386927 : Blo 1853628 9386927 := bstep (se 1 (by rfl) ⟨7040195, by rfl⟩ : syracuseStep 9386927 = 14080391) B14080391
theorem B7044023 : Blo 1853628 7044023 := bstep (se 1 (by rfl) ⟨5283017, by rfl⟩ : syracuseStep 7044023 = 10566035) B10566035
theorem B10165267 : Blo 1853628 10165267 := bstep (se 1 (by rfl) ⟨7623950, by rfl⟩ : syracuseStep 10165267 = 15247901) B15247901
theorem B21412907 : Blo 1853628 21412907 := bstep (se 1 (by rfl) ⟨16059680, by rfl⟩ : syracuseStep 21412907 = 32119361) B32119361
theorem B4693049 : Blo 1853628 4693049 := bstep (se 2 (by rfl) ⟨1759893, by rfl⟩ : syracuseStep 4693049 = 3519787) B3519787
theorem B10567037 : Blo 1853628 10567037 := bstep (se 3 (by rfl) ⟨1981319, by rfl⟩ : syracuseStep 10567037 = 3962639) B3962639
theorem B3128719 : Blo 1853628 3128719 := bstep (se 1 (by rfl) ⟨2346539, by rfl⟩ : syracuseStep 3128719 = 4693079) B4693079
theorem B7536091 : Blo 1853628 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B22560295 : Blo 1853628 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B14270039 : Blo 1853628 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B7519841 : Blo 1853628 7519841 := bstep (se 2 (by rfl) ⟨2819940, by rfl⟩ : syracuseStep 7519841 = 5639881) B5639881
theorem B7921451 : Blo 1853628 7921451 := bstep (se 1 (by rfl) ⟨5941088, by rfl⟩ : syracuseStep 7921451 = 11882177) B11882177
theorem B9642035 : Blo 1853628 9642035 := bstep (se 1 (by rfl) ⟨7231526, by rfl⟩ : syracuseStep 9642035 = 14463053) B14463053
theorem B3522665 : Blo 1853628 3522665 := bstep (se 2 (by rfl) ⟨1320999, by rfl⟩ : syracuseStep 3522665 = 2641999) B2641999
theorem B21119129 : Blo 1853628 21119129 := bstep (se 2 (by rfl) ⟨7919673, by rfl⟩ : syracuseStep 21119129 = 15839347) B15839347
theorem B2228519 : Blo 1853628 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B4694345 : Blo 1853628 4694345 := bstep (se 2 (by rfl) ⟨1760379, by rfl⟩ : syracuseStep 4694345 = 3520759) B3520759
theorem B3129691 : Blo 1853628 3129691 := bstep (se 1 (by rfl) ⟨2347268, by rfl⟩ : syracuseStep 3129691 = 4694537) B4694537
theorem B370835921 : Blo 1853628 370835921 := bstep (se 2 (by rfl) ⟨139063470, by rfl⟩ : syracuseStep 370835921 = 278126941) B278126941
theorem B6775265 : Blo 1853628 6775265 := bstep (se 2 (by rfl) ⟨2540724, by rfl⟩ : syracuseStep 6775265 = 5081449) B5081449
theorem B2507257 : Blo 1853628 2507257 := bstep (se 2 (by rfl) ⟨940221, by rfl⟩ : syracuseStep 2507257 = 1880443) B1880443
theorem B4694699 : Blo 1853628 4694699 := bstep (se 1 (by rfl) ⟨3521024, by rfl⟩ : syracuseStep 4694699 = 7042049) B7042049
theorem B10560203 : Blo 1853628 10560203 := bstep (se 1 (by rfl) ⟨7920152, by rfl⟩ : syracuseStep 10560203 = 15840305) B15840305
theorem B23774147 : Blo 1853628 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B4170743 : Blo 1853628 4170743 := bstep (se 1 (by rfl) ⟨3128057, by rfl⟩ : syracuseStep 4170743 = 6256115) B6256115
theorem B5940371 : Blo 1853628 5940371 := bstep (se 1 (by rfl) ⟨4455278, by rfl⟩ : syracuseStep 5940371 = 8910557) B8910557
theorem B3130663 : Blo 1853628 3130663 := bstep (se 1 (by rfl) ⟨2347997, by rfl⟩ : syracuseStep 3130663 = 4695995) B4695995
theorem B4171103 : Blo 1853628 4171103 := bstep (se 1 (by rfl) ⟨3128327, by rfl⟩ : syracuseStep 4171103 = 6256655) B6256655
theorem B12043673 : Blo 1853628 12043673 := bstep (se 2 (by rfl) ⟨4516377, by rfl⟩ : syracuseStep 12043673 = 9032755) B9032755
theorem B6260381 : Blo 1853628 6260381 := bstep (se 3 (by rfl) ⟨1173821, by rfl⟩ : syracuseStep 6260381 = 2347643) B2347643
theorem B25388765 : Blo 1853628 25388765 := bstep (se 3 (by rfl) ⟨4760393, by rfl⟩ : syracuseStep 25388765 = 9520787) B9520787
theorem B4171499 : Blo 1853628 4171499 := bstep (se 1 (by rfl) ⟨3128624, by rfl⟩ : syracuseStep 4171499 = 6257249) B6257249
theorem B2819819 : Blo 1853628 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B5015303 : Blo 1853628 5015303 := bstep (se 1 (by rfl) ⟨3761477, by rfl⟩ : syracuseStep 5015303 = 7522955) B7522955
theorem B3131183 : Blo 1853628 3131183 := bstep (se 1 (by rfl) ⟨2348387, by rfl⟩ : syracuseStep 3131183 = 4696775) B4696775
theorem B4171625 : Blo 1853628 4171625 := bstep (se 2 (by rfl) ⟨1564359, by rfl⟩ : syracuseStep 4171625 = 3128719) B3128719
theorem B4696015 : Blo 1853628 4696015 := bstep (se 1 (by rfl) ⟨3522011, by rfl⟩ : syracuseStep 4696015 = 7044023) B7044023
theorem B20056193 : Blo 1853628 20056193 := bstep (se 2 (by rfl) ⟨7521072, by rfl⟩ : syracuseStep 20056193 = 15042145) B15042145
theorem B6260921 : Blo 1853628 6260921 := bstep (se 2 (by rfl) ⟨2347845, by rfl⟩ : syracuseStep 6260921 = 4695691) B4695691
theorem B1853727 : Blo 1853628 1853727 := bstep (se 1 (by rfl) ⟨1390295, by rfl⟩ : syracuseStep 1853727 = 2780591) B2780591
theorem B1853787 : Blo 1853628 1853787 := bstep (se 1 (by rfl) ⟨1390340, by rfl⟩ : syracuseStep 1853787 = 2780681) B2780681
theorem B1853807 : Blo 1853628 1853807 := bstep (se 1 (by rfl) ⟨1390355, by rfl⟩ : syracuseStep 1853807 = 2780711) B2780711
theorem B9513359 : Blo 1853628 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B1853863 : Blo 1853628 1853863 := bstep (se 1 (by rfl) ⟨1390397, by rfl⟩ : syracuseStep 1853863 = 2780795) B2780795
theorem B11889125 : Blo 1853628 11889125 := bstep (se 4 (by rfl) ⟨1114605, by rfl⟩ : syracuseStep 11889125 = 2229211) B2229211
theorem B1853947 : Blo 1853628 1853947 := bstep (se 1 (by rfl) ⟨1390460, by rfl⟩ : syracuseStep 1853947 = 2780921) B2780921
theorem B1854015 : Blo 1853628 1854015 := bstep (se 1 (by rfl) ⟨1390511, by rfl⟩ : syracuseStep 1854015 = 2781023) B2781023
theorem B1854023 : Blo 1853628 1854023 := bstep (se 1 (by rfl) ⟨1390517, by rfl⟩ : syracuseStep 1854023 = 2781035) B2781035
theorem B14076503 : Blo 1853628 14076503 := bstep (se 1 (by rfl) ⟨10557377, by rfl⟩ : syracuseStep 14076503 = 21114755) B21114755
theorem B11274875 : Blo 1853628 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B10029743 : Blo 1853628 10029743 := bstep (se 1 (by rfl) ⟨7522307, by rfl⟩ : syracuseStep 10029743 = 15044615) B15044615
theorem B4172471 : Blo 1853628 4172471 := bstep (se 1 (by rfl) ⟨3129353, by rfl⟩ : syracuseStep 4172471 = 6258707) B6258707
theorem B1854175 : Blo 1853628 1854175 := bstep (se 1 (by rfl) ⟨1390631, by rfl⟩ : syracuseStep 1854175 = 2781263) B2781263
theorem B47541005 : Blo 1853628 47541005 := bstep (se 3 (by rfl) ⟨8913938, by rfl⟩ : syracuseStep 47541005 = 17827877) B17827877
theorem B10709783 : Blo 1853628 10709783 := bstep (se 1 (by rfl) ⟨8032337, by rfl⟩ : syracuseStep 10709783 = 16064675) B16064675
theorem B1854255 : Blo 1853628 1854255 := bstep (se 1 (by rfl) ⟨1390691, by rfl⟩ : syracuseStep 1854255 = 2781383) B2781383
theorem B73239389 : Blo 1853628 73239389 := bstep (se 3 (by rfl) ⟨13732385, by rfl⟩ : syracuseStep 73239389 = 27464771) B27464771
theorem B35654525 : Blo 1853628 35654525 := bstep (se 3 (by rfl) ⟨6685223, by rfl⟩ : syracuseStep 35654525 = 13370447) B13370447
theorem B4172687 : Blo 1853628 4172687 := bstep (se 1 (by rfl) ⟨3129515, by rfl⟩ : syracuseStep 4172687 = 6259031) B6259031
theorem B1854363 : Blo 1853628 1854363 := bstep (se 1 (by rfl) ⟨1390772, by rfl⟩ : syracuseStep 1854363 = 2781545) B2781545
theorem B4696987 : Blo 1853628 4696987 := bstep (se 1 (by rfl) ⟨3522740, by rfl⟩ : syracuseStep 4696987 = 7045481) B7045481
theorem B1854415 : Blo 1853628 1854415 := bstep (se 1 (by rfl) ⟨1390811, by rfl⟩ : syracuseStep 1854415 = 2781623) B2781623
theorem B1854439 : Blo 1853628 1854439 := bstep (se 1 (by rfl) ⟨1390829, by rfl⟩ : syracuseStep 1854439 = 2781659) B2781659
theorem B2640871 : Blo 1853628 2640871 := bstep (se 1 (by rfl) ⟨1980653, by rfl⟩ : syracuseStep 2640871 = 3961307) B3961307
theorem B6024331 : Blo 1853628 6024331 := bstep (se 1 (by rfl) ⟨4518248, by rfl⟩ : syracuseStep 6024331 = 9036497) B9036497
theorem B2780447 : Blo 1853628 2780447 := bstep (se 1 (by rfl) ⟨2085335, by rfl⟩ : syracuseStep 2780447 = 4170671) B4170671
theorem B1854751 : Blo 1853628 1854751 := bstep (se 1 (by rfl) ⟨1391063, by rfl⟩ : syracuseStep 1854751 = 2782127) B2782127
theorem B3960103 : Blo 1853628 3960103 := bstep (se 1 (by rfl) ⟨2970077, by rfl⟩ : syracuseStep 3960103 = 5940155) B5940155
theorem B1854811 : Blo 1853628 1854811 := bstep (se 1 (by rfl) ⟨1391108, by rfl⟩ : syracuseStep 1854811 = 2782217) B2782217
theorem B1854831 : Blo 1853628 1854831 := bstep (se 1 (by rfl) ⟨1391123, by rfl⟩ : syracuseStep 1854831 = 2782247) B2782247
theorem B1854887 : Blo 1853628 1854887 := bstep (se 1 (by rfl) ⟨1391165, by rfl⟩ : syracuseStep 1854887 = 2782331) B2782331
theorem B2780615 : Blo 1853628 2780615 := bstep (se 1 (by rfl) ⟨2085461, by rfl⟩ : syracuseStep 2780615 = 4170923) B4170923
theorem B1854971 : Blo 1853628 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B9391625 : Blo 1853628 9391625 := bstep (se 2 (by rfl) ⟨3521859, by rfl⟩ : syracuseStep 9391625 = 7043719) B7043719
theorem B1855039 : Blo 1853628 1855039 := bstep (se 1 (by rfl) ⟨1391279, by rfl⟩ : syracuseStep 1855039 = 2782559) B2782559
theorem B1855047 : Blo 1853628 1855047 := bstep (se 1 (by rfl) ⟨1391285, by rfl⟩ : syracuseStep 1855047 = 2782571) B2782571
theorem B5279327 : Blo 1853628 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B4173407 : Blo 1853628 4173407 := bstep (se 1 (by rfl) ⟨3130055, by rfl⟩ : syracuseStep 4173407 = 6260111) B6260111
theorem B7040621 : Blo 1853628 7040621 := bstep (se 3 (by rfl) ⟨1320116, by rfl⟩ : syracuseStep 7040621 = 2640233) B2640233
theorem B10022561 : Blo 1853628 10022561 := bstep (se 2 (by rfl) ⟨3758460, by rfl⟩ : syracuseStep 10022561 = 7516921) B7516921
theorem B6262433 : Blo 1853628 6262433 := bstep (se 2 (by rfl) ⟨2348412, by rfl⟩ : syracuseStep 6262433 = 4696825) B4696825
theorem B2346671 : Blo 1853628 2346671 := bstep (se 1 (by rfl) ⟨1760003, by rfl⟩ : syracuseStep 2346671 = 3520007) B3520007
theorem B1855199 : Blo 1853628 1855199 := bstep (se 1 (by rfl) ⟨1391399, by rfl⟩ : syracuseStep 1855199 = 2782799) B2782799
theorem B2780969 : Blo 1853628 2780969 := bstep (se 2 (by rfl) ⟨1042863, by rfl⟩ : syracuseStep 2780969 = 2085727) B2085727
theorem B2780975 : Blo 1853628 2780975 := bstep (se 1 (by rfl) ⟨2085731, by rfl⟩ : syracuseStep 2780975 = 4171463) B4171463
theorem B3960623 : Blo 1853628 3960623 := bstep (se 1 (by rfl) ⟨2970467, by rfl⟩ : syracuseStep 3960623 = 5940935) B5940935
theorem B1855279 : Blo 1853628 1855279 := bstep (se 1 (by rfl) ⟨1391459, by rfl⟩ : syracuseStep 1855279 = 2782919) B2782919
theorem B4173623 : Blo 1853628 4173623 := bstep (se 1 (by rfl) ⟨3130217, by rfl⟩ : syracuseStep 4173623 = 6260435) B6260435
theorem B3215161 : Blo 1853628 3215161 := bstep (se 2 (by rfl) ⟨1205685, by rfl⟩ : syracuseStep 3215161 = 2411371) B2411371
theorem B1855387 : Blo 1853628 1855387 := bstep (se 1 (by rfl) ⟨1391540, by rfl⟩ : syracuseStep 1855387 = 2783081) B2783081
theorem B1855439 : Blo 1853628 1855439 := bstep (se 1 (by rfl) ⟨1391579, by rfl⟩ : syracuseStep 1855439 = 2783159) B2783159
theorem B1855463 : Blo 1853628 1855463 := bstep (se 1 (by rfl) ⟨1391597, by rfl⟩ : syracuseStep 1855463 = 2783195) B2783195
theorem B13553689 : Blo 1853628 13553689 := bstep (se 2 (by rfl) ⟨5082633, by rfl⟩ : syracuseStep 13553689 = 10165267) B10165267
theorem B4173929 : Blo 1853628 4173929 := bstep (se 2 (by rfl) ⟨1565223, by rfl⟩ : syracuseStep 4173929 = 3130447) B3130447
theorem B2781449 : Blo 1853628 2781449 := bstep (se 2 (by rfl) ⟨1043043, by rfl⟩ : syracuseStep 2781449 = 2086087) B2086087
theorem B72298817 : Blo 1853628 72298817 := bstep (se 2 (by rfl) ⟨27112056, by rfl⟩ : syracuseStep 72298817 = 54224113) B54224113
theorem B13365577 : Blo 1853628 13365577 := bstep (se 2 (by rfl) ⟨5012091, by rfl⟩ : syracuseStep 13365577 = 10024183) B10024183
theorem B57102691 : Blo 1853628 57102691 := bstep (se 1 (by rfl) ⟨42827018, by rfl⟩ : syracuseStep 57102691 = 85654037) B85654037
theorem B2781551 : Blo 1853628 2781551 := bstep (se 1 (by rfl) ⟨2086163, by rfl⟩ : syracuseStep 2781551 = 4172327) B4172327
theorem B2347375 : Blo 1853628 2347375 := bstep (se 1 (by rfl) ⟨1760531, by rfl⟩ : syracuseStep 2347375 = 3521063) B3521063
theorem B15839621 : Blo 1853628 15839621 := bstep (se 4 (by rfl) ⟨1484964, by rfl⟩ : syracuseStep 15839621 = 2969929) B2969929
theorem B2085439 : Blo 1853628 2085439 := bstep (se 1 (by rfl) ⟨1564079, by rfl⟩ : syracuseStep 2085439 = 3128159) B3128159
theorem B2781767 : Blo 1853628 2781767 := bstep (se 1 (by rfl) ⟨2086325, by rfl⟩ : syracuseStep 2781767 = 4172651) B4172651
theorem B4174415 : Blo 1853628 4174415 := bstep (se 1 (by rfl) ⟨3130811, by rfl⟩ : syracuseStep 4174415 = 6261623) B6261623
theorem B2781803 : Blo 1853628 2781803 := bstep (se 1 (by rfl) ⟨2086352, by rfl⟩ : syracuseStep 2781803 = 4172705) B4172705
theorem B10048121 : Blo 1853628 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B76165829 : Blo 1853628 76165829 := bstep (se 4 (by rfl) ⟨7140546, by rfl⟩ : syracuseStep 76165829 = 14281093) B14281093
theorem B14275271 : Blo 1853628 14275271 := bstep (se 1 (by rfl) ⟨10706453, by rfl⟩ : syracuseStep 14275271 = 21412907) B21412907
theorem B4174559 : Blo 1853628 4174559 := bstep (se 1 (by rfl) ⟨3130919, by rfl⟩ : syracuseStep 4174559 = 6261839) B6261839
theorem B2782031 : Blo 1853628 2782031 := bstep (se 1 (by rfl) ⟨2086523, by rfl⟩ : syracuseStep 2782031 = 4173047) B4173047
theorem B32559965 : Blo 1853628 32559965 := bstep (se 3 (by rfl) ⟨6104993, by rfl⟩ : syracuseStep 32559965 = 12209987) B12209987
theorem B12039077 : Blo 1853628 12039077 := bstep (se 4 (by rfl) ⟨1128663, by rfl⟩ : syracuseStep 12039077 = 2257327) B2257327
theorem B3961819 : Blo 1853628 3961819 := bstep (se 1 (by rfl) ⟨2971364, by rfl⟩ : syracuseStep 3961819 = 5942729) B5942729
theorem B4174811 : Blo 1853628 4174811 := bstep (se 1 (by rfl) ⟨3131108, by rfl⟩ : syracuseStep 4174811 = 6262217) B6262217
theorem B7918717 : Blo 1853628 7918717 := bstep (se 3 (by rfl) ⟨1484759, by rfl⟩ : syracuseStep 7918717 = 2969519) B2969519
theorem B4174991 : Blo 1853628 4174991 := bstep (se 1 (by rfl) ⟨3131243, by rfl⟩ : syracuseStep 4174991 = 6262487) B6262487
theorem B5280967 : Blo 1853628 5280967 := bstep (se 1 (by rfl) ⟨3960725, by rfl⟩ : syracuseStep 5280967 = 7921451) B7921451
theorem B7042247 : Blo 1853628 7042247 := bstep (se 1 (by rfl) ⟨5281685, by rfl⟩ : syracuseStep 7042247 = 10563371) B10563371
theorem B2782427 : Blo 1853628 2782427 := bstep (se 1 (by rfl) ⟨2086820, by rfl⟩ : syracuseStep 2782427 = 4173641) B4173641
theorem B4175081 : Blo 1853628 4175081 := bstep (se 2 (by rfl) ⟨1565655, by rfl⟩ : syracuseStep 4175081 = 3131311) B3131311
theorem B4175135 : Blo 1853628 4175135 := bstep (se 1 (by rfl) ⟨3131351, by rfl⟩ : syracuseStep 4175135 = 6262703) B6262703
theorem B24098143 : Blo 1853628 24098143 := bstep (se 1 (by rfl) ⟨18073607, by rfl⟩ : syracuseStep 24098143 = 36147215) B36147215
theorem B2086267 : Blo 1853628 2086267 := bstep (se 1 (by rfl) ⟨1564700, by rfl⟩ : syracuseStep 2086267 = 3129401) B3129401
theorem B2782601 : Blo 1853628 2782601 := bstep (se 2 (by rfl) ⟨1043475, by rfl⟩ : syracuseStep 2782601 = 2086951) B2086951
theorem B5010827 : Blo 1853628 5010827 := bstep (se 1 (by rfl) ⟨3758120, by rfl⟩ : syracuseStep 5010827 = 7516241) B7516241
theorem B9393569 : Blo 1853628 9393569 := bstep (se 2 (by rfl) ⟨3522588, by rfl⟩ : syracuseStep 9393569 = 7045177) B7045177
theorem B6256061 : Blo 1853628 6256061 := bstep (se 3 (by rfl) ⟨1173011, by rfl⟩ : syracuseStep 6256061 = 2346023) B2346023
theorem B6682169 : Blo 1853628 6682169 := bstep (se 2 (by rfl) ⟨2505813, by rfl⟩ : syracuseStep 6682169 = 5011627) B5011627
theorem B3012191 : Blo 1853628 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B7042747 : Blo 1853628 7042747 := bstep (se 1 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 7042747 = 10564121) B10564121
theorem B3520235 : Blo 1853628 3520235 := bstep (se 1 (by rfl) ⟨2640176, by rfl⟩ : syracuseStep 3520235 = 5280353) B5280353
theorem B2782955 : Blo 1853628 2782955 := bstep (se 1 (by rfl) ⟨2087216, by rfl⟩ : syracuseStep 2782955 = 4174433) B4174433
theorem B6256439 : Blo 1853628 6256439 := bstep (se 1 (by rfl) ⟨4692329, by rfl⟩ : syracuseStep 6256439 = 9384659) B9384659
theorem B7141175 : Blo 1853628 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B2086735 : Blo 1853628 2086735 := bstep (se 1 (by rfl) ⟨1565051, by rfl⟩ : syracuseStep 2086735 = 3130103) B3130103
theorem B365737931 : Blo 1853628 365737931 := bstep (se 1 (by rfl) ⟨274303448, by rfl⟩ : syracuseStep 365737931 = 548606897) B548606897
theorem B2783183 : Blo 1853628 2783183 := bstep (se 1 (by rfl) ⟨2087387, by rfl⟩ : syracuseStep 2783183 = 4174775) B4174775
theorem B3758185 : Blo 1853628 3758185 := bstep (se 2 (by rfl) ⟨1409319, by rfl⟩ : syracuseStep 3758185 = 2818639) B2818639
theorem B2087131 : Blo 1853628 2087131 := bstep (se 1 (by rfl) ⟨1565348, by rfl⟩ : syracuseStep 2087131 = 3130697) B3130697
theorem B6256925 : Blo 1853628 6256925 := bstep (se 3 (by rfl) ⟨1173173, by rfl⟩ : syracuseStep 6256925 = 2346347) B2346347
theorem B6019495 : Blo 1853628 6019495 := bstep (se 1 (by rfl) ⟨4514621, by rfl⟩ : syracuseStep 6019495 = 9029243) B9029243
theorem B3520979 : Blo 1853628 3520979 := bstep (se 1 (by rfl) ⟨2640734, by rfl⟩ : syracuseStep 3520979 = 5281469) B5281469
theorem B2087419 : Blo 1853628 2087419 := bstep (se 1 (by rfl) ⟨1565564, by rfl⟩ : syracuseStep 2087419 = 3131129) B3131129
theorem B80230985 : Blo 1853628 80230985 := bstep (se 2 (by rfl) ⟨30086619, by rfl⟩ : syracuseStep 80230985 = 60173239) B60173239
theorem B9386603 : Blo 1853628 9386603 := bstep (se 1 (by rfl) ⟨7039952, by rfl⟩ : syracuseStep 9386603 = 14079905) B14079905
theorem B31685255 : Blo 1853628 31685255 := bstep (se 1 (by rfl) ⟨23763941, by rfl⟩ : syracuseStep 31685255 = 47527883) B47527883
theorem B3521207 : Blo 1853628 3521207 := bstep (se 1 (by rfl) ⟨2640905, by rfl⟩ : syracuseStep 3521207 = 5281811) B5281811
theorem B4692755 : Blo 1853628 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B77175827 : Blo 1853628 77175827 := bstep (se 1 (by rfl) ⟨57881870, by rfl⟩ : syracuseStep 77175827 = 115763741) B115763741
theorem B9387089 : Blo 1853628 9387089 := bstep (se 2 (by rfl) ⟨3520158, by rfl⟩ : syracuseStep 9387089 = 7040317) B7040317
theorem B9518161 : Blo 1853628 9518161 := bstep (se 2 (by rfl) ⟨3569310, by rfl⟩ : syracuseStep 9518161 = 7138621) B7138621
theorem B4693211 : Blo 1853628 4693211 := bstep (se 1 (by rfl) ⟨3519908, by rfl⟩ : syracuseStep 4693211 = 7039817) B7039817
theorem B3341531 : Blo 1853628 3341531 := bstep (se 1 (by rfl) ⟨2506148, by rfl⟩ : syracuseStep 3341531 = 5012297) B5012297
theorem B4693241 : Blo 1853628 4693241 := bstep (se 2 (by rfl) ⟨1759965, by rfl⟩ : syracuseStep 4693241 = 3519931) B3519931
theorem B6257951 : Blo 1853628 6257951 := bstep (se 1 (by rfl) ⟨4693463, by rfl⟩ : syracuseStep 6257951 = 9386927) B9386927
theorem B3128699 : Blo 1853628 3128699 := bstep (se 1 (by rfl) ⟨2346524, by rfl⟩ : syracuseStep 3128699 = 4693049) B4693049
theorem B30080393 : Blo 1853628 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B7044691 : Blo 1853628 7044691 := bstep (se 1 (by rfl) ⟨5283518, by rfl⟩ : syracuseStep 7044691 = 10567037) B10567037
theorem B5013227 : Blo 1853628 5013227 := bstep (se 1 (by rfl) ⟨3759920, by rfl⟩ : syracuseStep 5013227 = 7519841) B7519841
theorem B3522361 : Blo 1853628 3522361 := bstep (se 2 (by rfl) ⟨1320885, by rfl⟩ : syracuseStep 3522361 = 2641771) B2641771
theorem B4693889 : Blo 1853628 4693889 := bstep (se 2 (by rfl) ⟨1760208, by rfl⟩ : syracuseStep 4693889 = 3520417) B3520417
theorem B18071585 : Blo 1853628 18071585 := bstep (se 2 (by rfl) ⟨6776844, by rfl⟩ : syracuseStep 18071585 = 13553689) B13553689
theorem B3129563 : Blo 1853628 3129563 := bstep (se 1 (by rfl) ⟨2347172, by rfl⟩ : syracuseStep 3129563 = 4694345) B4694345
theorem B10559747 : Blo 1853628 10559747 := bstep (se 1 (by rfl) ⟨7919810, by rfl⟩ : syracuseStep 10559747 = 15839621) B15839621
theorem B3129799 : Blo 1853628 3129799 := bstep (se 1 (by rfl) ⟨2347349, by rfl⟩ : syracuseStep 3129799 = 4694699) B4694699
theorem B76136921 : Blo 1853628 76136921 := bstep (se 2 (by rfl) ⟨28551345, by rfl⟩ : syracuseStep 76136921 = 57102691) B57102691
theorem B3129833 : Blo 1853628 3129833 := bstep (se 2 (by rfl) ⟨1173687, by rfl⟩ : syracuseStep 3129833 = 2347375) B2347375
theorem B4694831 : Blo 1853628 4694831 := bstep (se 1 (by rfl) ⟨3521123, by rfl⟩ : syracuseStep 4694831 = 7042247) B7042247
theorem B8029115 : Blo 1853628 8029115 := bstep (se 1 (by rfl) ⟨6021836, by rfl⟩ : syracuseStep 8029115 = 12043673) B12043673
theorem B4170707 : Blo 1853628 4170707 := bstep (se 1 (by rfl) ⟨3128030, by rfl⟩ : syracuseStep 4170707 = 6256061) B6256061
theorem B13362205 : Blo 1853628 13362205 := bstep (se 3 (by rfl) ⟨2505413, by rfl⟩ : syracuseStep 13362205 = 5010827) B5010827
theorem B2008127 : Blo 1853628 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B16925843 : Blo 1853628 16925843 := bstep (se 1 (by rfl) ⟨12694382, by rfl⟩ : syracuseStep 16925843 = 25388765) B25388765
theorem B3343535 : Blo 1853628 3343535 := bstep (se 1 (by rfl) ⟨2507651, by rfl⟩ : syracuseStep 3343535 = 5015303) B5015303
theorem B4170959 : Blo 1853628 4170959 := bstep (se 1 (by rfl) ⟨3128219, by rfl⟩ : syracuseStep 4170959 = 6256439) B6256439
theorem B4760783 : Blo 1853628 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B13370795 : Blo 1853628 13370795 := bstep (se 1 (by rfl) ⟨10028096, by rfl⟩ : syracuseStep 13370795 = 20056193) B20056193
theorem B12690881 : Blo 1853628 12690881 := bstep (se 2 (by rfl) ⟨4759080, by rfl⟩ : syracuseStep 12690881 = 9518161) B9518161
theorem B4171283 : Blo 1853628 4171283 := bstep (se 1 (by rfl) ⟨3128462, by rfl⟩ : syracuseStep 4171283 = 6256925) B6256925
theorem B6342239 : Blo 1853628 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B53487323 : Blo 1853628 53487323 := bstep (se 1 (by rfl) ⟨40115492, by rfl⟩ : syracuseStep 53487323 = 80230985) B80230985
theorem B6686495 : Blo 1853628 6686495 := bstep (se 1 (by rfl) ⟨5014871, by rfl⟩ : syracuseStep 6686495 = 10029743) B10029743
theorem B32130857 : Blo 1853628 32130857 := bstep (se 2 (by rfl) ⟨12049071, by rfl⟩ : syracuseStep 32130857 = 24098143) B24098143
theorem B48826259 : Blo 1853628 48826259 := bstep (se 1 (by rfl) ⟨36619694, by rfl⟩ : syracuseStep 48826259 = 73239389) B73239389
theorem B10561661 : Blo 1853628 10561661 := bstep (se 3 (by rfl) ⟨1980311, by rfl⟩ : syracuseStep 10561661 = 3960623) B3960623
theorem B1853631 : Blo 1853628 1853631 := bstep (se 1 (by rfl) ⟨1390223, by rfl⟩ : syracuseStep 1853631 = 2780447) B2780447
theorem B4171967 : Blo 1853628 4171967 := bstep (se 1 (by rfl) ⟨3128975, by rfl⟩ : syracuseStep 4171967 = 6257951) B6257951
theorem B9390329 : Blo 1853628 9390329 := bstep (se 2 (by rfl) ⟨3521373, by rfl⟩ : syracuseStep 9390329 = 7042747) B7042747
theorem B1853743 : Blo 1853628 1853743 := bstep (se 1 (by rfl) ⟨1390307, by rfl⟩ : syracuseStep 1853743 = 2780615) B2780615
theorem B6261083 : Blo 1853628 6261083 := bstep (se 1 (by rfl) ⟨4695812, by rfl⟩ : syracuseStep 6261083 = 9391625) B9391625
theorem B4286881 : Blo 1853628 4286881 := bstep (se 2 (by rfl) ⟨1607580, by rfl⟩ : syracuseStep 4286881 = 3215161) B3215161
theorem B4696481 : Blo 1853628 4696481 := bstep (se 2 (by rfl) ⟨1761180, by rfl⟩ : syracuseStep 4696481 = 3522361) B3522361
theorem B1853979 : Blo 1853628 1853979 := bstep (se 1 (by rfl) ⟨1390484, by rfl⟩ : syracuseStep 1853979 = 2780969) B2780969
theorem B1853983 : Blo 1853628 1853983 := bstep (se 1 (by rfl) ⟨1390487, by rfl⟩ : syracuseStep 1853983 = 2780975) B2780975
theorem B6261353 : Blo 1853628 6261353 := bstep (se 2 (by rfl) ⟨2348007, by rfl⟩ : syracuseStep 6261353 = 4696015) B4696015
theorem B13372037 : Blo 1853628 13372037 := bstep (se 4 (by rfl) ⟨1253628, by rfl⟩ : syracuseStep 13372037 = 2507257) B2507257
theorem B1854299 : Blo 1853628 1854299 := bstep (se 1 (by rfl) ⟨1390724, by rfl⟩ : syracuseStep 1854299 = 2781449) B2781449
theorem B1854367 : Blo 1853628 1854367 := bstep (se 1 (by rfl) ⟨1390775, by rfl⟩ : syracuseStep 1854367 = 2781551) B2781551
theorem B1854511 : Blo 1853628 1854511 := bstep (se 1 (by rfl) ⟨1390883, by rfl⟩ : syracuseStep 1854511 = 2781767) B2781767
theorem B1854535 : Blo 1853628 1854535 := bstep (se 1 (by rfl) ⟨1390901, by rfl⟩ : syracuseStep 1854535 = 2781803) B2781803
theorem B17820769 : Blo 1853628 17820769 := bstep (se 2 (by rfl) ⟨6682788, by rfl⟩ : syracuseStep 17820769 = 13365577) B13365577
theorem B4172921 : Blo 1853628 4172921 := bstep (se 2 (by rfl) ⟨1564845, by rfl⟩ : syracuseStep 4172921 = 3129691) B3129691
theorem B50777219 : Blo 1853628 50777219 := bstep (se 1 (by rfl) ⟨38082914, by rfl⟩ : syracuseStep 50777219 = 76165829) B76165829
theorem B7040135 : Blo 1853628 7040135 := bstep (se 1 (by rfl) ⟨5280101, by rfl⟩ : syracuseStep 7040135 = 10560203) B10560203
theorem B1854687 : Blo 1853628 1854687 := bstep (se 1 (by rfl) ⟨1391015, by rfl⟩ : syracuseStep 1854687 = 2782031) B2782031
theorem B2780495 : Blo 1853628 2780495 := bstep (se 1 (by rfl) ⟨2085371, by rfl⟩ : syracuseStep 2780495 = 4170743) B4170743
theorem B2780585 : Blo 1853628 2780585 := bstep (se 2 (by rfl) ⟨1042719, by rfl⟩ : syracuseStep 2780585 = 2085439) B2085439
theorem B3960247 : Blo 1853628 3960247 := bstep (se 1 (by rfl) ⟨2970185, by rfl⟩ : syracuseStep 3960247 = 5940371) B5940371
theorem B5942717 : Blo 1853628 5942717 := bstep (se 3 (by rfl) ⟨1114259, by rfl⟩ : syracuseStep 5942717 = 2228519) B2228519
theorem B1854951 : Blo 1853628 1854951 := bstep (se 1 (by rfl) ⟨1391213, by rfl⟩ : syracuseStep 1854951 = 2782427) B2782427
theorem B2780735 : Blo 1853628 2780735 := bstep (se 1 (by rfl) ⟨2085551, by rfl⟩ : syracuseStep 2780735 = 4171103) B4171103
theorem B1855067 : Blo 1853628 1855067 := bstep (se 1 (by rfl) ⟨1391300, by rfl⟩ : syracuseStep 1855067 = 2782601) B2782601
theorem B6262379 : Blo 1853628 6262379 := bstep (se 1 (by rfl) ⟨4696784, by rfl⟩ : syracuseStep 6262379 = 9393569) B9393569
theorem B4173587 : Blo 1853628 4173587 := bstep (se 1 (by rfl) ⟨3130190, by rfl⟩ : syracuseStep 4173587 = 6260381) B6260381
theorem B2780999 : Blo 1853628 2780999 := bstep (se 1 (by rfl) ⟨2085749, by rfl⟩ : syracuseStep 2780999 = 4171499) B4171499
theorem B2346823 : Blo 1853628 2346823 := bstep (se 1 (by rfl) ⟨1760117, by rfl⟩ : syracuseStep 2346823 = 3520235) B3520235
theorem B1855303 : Blo 1853628 1855303 := bstep (se 1 (by rfl) ⟨1391477, by rfl⟩ : syracuseStep 1855303 = 2782955) B2782955
theorem B6262649 : Blo 1853628 6262649 := bstep (se 2 (by rfl) ⟨2348493, by rfl⟩ : syracuseStep 6262649 = 4696987) B4696987
theorem B2781083 : Blo 1853628 2781083 := bstep (se 1 (by rfl) ⟨2085812, by rfl⟩ : syracuseStep 2781083 = 4171625) B4171625
theorem B18067373 : Blo 1853628 18067373 := bstep (se 3 (by rfl) ⟨3387632, by rfl⟩ : syracuseStep 18067373 = 6775265) B6775265
theorem B1855455 : Blo 1853628 1855455 := bstep (se 1 (by rfl) ⟨1391591, by rfl⟩ : syracuseStep 1855455 = 2783183) B2783183
theorem B4173947 : Blo 1853628 4173947 := bstep (se 1 (by rfl) ⟨3130460, by rfl⟩ : syracuseStep 4173947 = 6260921) B6260921
theorem B8032441 : Blo 1853628 8032441 := bstep (se 2 (by rfl) ⟨3012165, by rfl⟩ : syracuseStep 8032441 = 6024331) B6024331
theorem B7041289 : Blo 1853628 7041289 := bstep (se 2 (by rfl) ⟨2640483, by rfl⟩ : syracuseStep 7041289 = 5280967) B5280967
theorem B2347319 : Blo 1853628 2347319 := bstep (se 1 (by rfl) ⟨1760489, by rfl⟩ : syracuseStep 2347319 = 3520979) B3520979
theorem B7926083 : Blo 1853628 7926083 := bstep (se 1 (by rfl) ⟨5944562, by rfl⟩ : syracuseStep 7926083 = 11889125) B11889125
theorem B5280137 : Blo 1853628 5280137 := bstep (se 2 (by rfl) ⟨1980051, by rfl⟩ : syracuseStep 5280137 = 3960103) B3960103
theorem B4174217 : Blo 1853628 4174217 := bstep (se 2 (by rfl) ⟨1565331, by rfl⟩ : syracuseStep 4174217 = 3130663) B3130663
theorem B9384335 : Blo 1853628 9384335 := bstep (se 1 (by rfl) ⟨7038251, by rfl⟩ : syracuseStep 9384335 = 14076503) B14076503
theorem B7516583 : Blo 1853628 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B21123503 : Blo 1853628 21123503 := bstep (se 1 (by rfl) ⟨15842627, by rfl⟩ : syracuseStep 21123503 = 31685255) B31685255
theorem B2781647 : Blo 1853628 2781647 := bstep (se 1 (by rfl) ⟨2086235, by rfl⟩ : syracuseStep 2781647 = 4172471) B4172471
theorem B2347471 : Blo 1853628 2347471 := bstep (se 1 (by rfl) ⟨1760603, by rfl⟩ : syracuseStep 2347471 = 3521207) B3521207
theorem B2781689 : Blo 1853628 2781689 := bstep (se 2 (by rfl) ⟨1043133, by rfl⟩ : syracuseStep 2781689 = 2086267) B2086267
theorem B7139855 : Blo 1853628 7139855 := bstep (se 1 (by rfl) ⟨5354891, by rfl⟩ : syracuseStep 7139855 = 10709783) B10709783
theorem B23769683 : Blo 1853628 23769683 := bstep (se 1 (by rfl) ⟨17827262, by rfl⟩ : syracuseStep 23769683 = 35654525) B35654525
theorem B2781791 : Blo 1853628 2781791 := bstep (se 1 (by rfl) ⟨2086343, by rfl⟩ : syracuseStep 2781791 = 4172687) B4172687
theorem B51450551 : Blo 1853628 51450551 := bstep (se 1 (by rfl) ⟨38587913, by rfl⟩ : syracuseStep 51450551 = 77175827) B77175827
theorem B9392921 : Blo 1853628 9392921 := bstep (se 2 (by rfl) ⟨3522345, by rfl⟩ : syracuseStep 9392921 = 7044691) B7044691
theorem B2085799 : Blo 1853628 2085799 := bstep (se 1 (by rfl) ⟨1564349, by rfl⟩ : syracuseStep 2085799 = 3128699) B3128699
theorem B3519551 : Blo 1853628 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B2782271 : Blo 1853628 2782271 := bstep (se 1 (by rfl) ⟨2086703, by rfl⟩ : syracuseStep 2782271 = 4173407) B4173407
theorem B2782313 : Blo 1853628 2782313 := bstep (se 2 (by rfl) ⟨1043367, by rfl⟩ : syracuseStep 2782313 = 2086735) B2086735
theorem B6681707 : Blo 1853628 6681707 := bstep (se 1 (by rfl) ⟨5011280, by rfl⟩ : syracuseStep 6681707 = 10022561) B10022561
theorem B4174955 : Blo 1853628 4174955 := bstep (se 1 (by rfl) ⟨3131216, by rfl⟩ : syracuseStep 4174955 = 6262433) B6262433
theorem B2782415 : Blo 1853628 2782415 := bstep (se 1 (by rfl) ⟨2086811, by rfl⟩ : syracuseStep 2782415 = 4173623) B4173623
theorem B2782619 : Blo 1853628 2782619 := bstep (se 1 (by rfl) ⟨2086964, by rfl⟩ : syracuseStep 2782619 = 4173929) B4173929
theorem B2348443 : Blo 1853628 2348443 := bstep (se 1 (by rfl) ⟨1761332, by rfl⟩ : syracuseStep 2348443 = 3522665) B3522665
theorem B14079419 : Blo 1853628 14079419 := bstep (se 1 (by rfl) ⟨10559564, by rfl⟩ : syracuseStep 14079419 = 21119129) B21119129
theorem B25712093 : Blo 1853628 25712093 := bstep (se 3 (by rfl) ⟨4821017, by rfl⟩ : syracuseStep 25712093 = 9642035) B9642035
theorem B5010913 : Blo 1853628 5010913 := bstep (se 2 (by rfl) ⟨1879092, by rfl⟩ : syracuseStep 5010913 = 3758185) B3758185
theorem B48199211 : Blo 1853628 48199211 := bstep (se 1 (by rfl) ⟨36149408, by rfl⟩ : syracuseStep 48199211 = 72298817) B72298817
theorem B2782841 : Blo 1853628 2782841 := bstep (se 2 (by rfl) ⟨1043565, by rfl⟩ : syracuseStep 2782841 = 2087131) B2087131
theorem B2782943 : Blo 1853628 2782943 := bstep (se 1 (by rfl) ⟨2087207, by rfl⟩ : syracuseStep 2782943 = 4174415) B4174415
theorem B6698747 : Blo 1853628 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B9516847 : Blo 1853628 9516847 := bstep (se 1 (by rfl) ⟨7137635, by rfl⟩ : syracuseStep 9516847 = 14275271) B14275271
theorem B2783039 : Blo 1853628 2783039 := bstep (se 1 (by rfl) ⟨2087279, by rfl⟩ : syracuseStep 2783039 = 4174559) B4174559
theorem B21706643 : Blo 1853628 21706643 := bstep (se 1 (by rfl) ⟨16279982, by rfl⟩ : syracuseStep 21706643 = 32559965) B32559965
theorem B8910749 : Blo 1853628 8910749 := bstep (se 3 (by rfl) ⟨1670765, by rfl⟩ : syracuseStep 8910749 = 3341531) B3341531
theorem B8026051 : Blo 1853628 8026051 := bstep (se 1 (by rfl) ⟨6019538, by rfl⟩ : syracuseStep 8026051 = 12039077) B12039077
theorem B15849431 : Blo 1853628 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B2783207 : Blo 1853628 2783207 := bstep (se 1 (by rfl) ⟨2087405, by rfl⟩ : syracuseStep 2783207 = 4174811) B4174811
theorem B2783225 : Blo 1853628 2783225 := bstep (se 2 (by rfl) ⟨1043709, by rfl⟩ : syracuseStep 2783225 = 2087419) B2087419
theorem B2783327 : Blo 1853628 2783327 := bstep (se 1 (by rfl) ⟨2087495, by rfl⟩ : syracuseStep 2783327 = 4174991) B4174991
theorem B2783387 : Blo 1853628 2783387 := bstep (se 1 (by rfl) ⟨2087540, by rfl⟩ : syracuseStep 2783387 = 4175081) B4175081
theorem B2783423 : Blo 1853628 2783423 := bstep (se 1 (by rfl) ⟨2087567, by rfl⟩ : syracuseStep 2783423 = 4175135) B4175135
theorem B4454779 : Blo 1853628 4454779 := bstep (se 1 (by rfl) ⟨3341084, by rfl⟩ : syracuseStep 4454779 = 6682169) B6682169
theorem B2087455 : Blo 1853628 2087455 := bstep (se 1 (by rfl) ⟨1565591, by rfl⟩ : syracuseStep 2087455 = 3131183) B3131183
theorem B988895789 : Blo 1853628 988895789 := bstep (se 3 (by rfl) ⟨185417960, by rfl⟩ : syracuseStep 988895789 = 370835921) B370835921
theorem B5282425 : Blo 1853628 5282425 := bstep (se 2 (by rfl) ⟨1980909, by rfl⟩ : syracuseStep 5282425 = 3961819) B3961819
theorem B243825287 : Blo 1853628 243825287 := bstep (se 1 (by rfl) ⟨182868965, by rfl⟩ : syracuseStep 243825287 = 365737931) B365737931
theorem B3521161 : Blo 1853628 3521161 := bstep (se 2 (by rfl) ⟨1320435, by rfl⟩ : syracuseStep 3521161 = 2640871) B2640871
theorem B10558289 : Blo 1853628 10558289 := bstep (se 2 (by rfl) ⟨3959358, by rfl⟩ : syracuseStep 10558289 = 7918717) B7918717
theorem B6257735 : Blo 1853628 6257735 := bstep (se 1 (by rfl) ⟨4693301, by rfl⟩ : syracuseStep 6257735 = 9386603) B9386603
theorem B6257789 : Blo 1853628 6257789 := bstep (se 3 (by rfl) ⟨1173335, by rfl⟩ : syracuseStep 6257789 = 2346671) B2346671
theorem B31694003 : Blo 1853628 31694003 := bstep (se 1 (by rfl) ⟨23770502, by rfl⟩ : syracuseStep 31694003 = 47541005) B47541005
theorem B3128503 : Blo 1853628 3128503 := bstep (se 1 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 3128503 = 4692755) B4692755
theorem B7519517 : Blo 1853628 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B6258059 : Blo 1853628 6258059 := bstep (se 1 (by rfl) ⟨4693544, by rfl⟩ : syracuseStep 6258059 = 9387089) B9387089
theorem B3128807 : Blo 1853628 3128807 := bstep (se 1 (by rfl) ⟨2346605, by rfl⟩ : syracuseStep 3128807 = 4693211) B4693211
theorem B3128827 : Blo 1853628 3128827 := bstep (se 1 (by rfl) ⟨2346620, by rfl⟩ : syracuseStep 3128827 = 4693241) B4693241
theorem B32103973 : Blo 1853628 32103973 := bstep (se 4 (by rfl) ⟨3009747, by rfl⟩ : syracuseStep 32103973 = 6019495) B6019495
theorem B20053595 : Blo 1853628 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B4693747 : Blo 1853628 4693747 := bstep (se 1 (by rfl) ⟨3520310, by rfl⟩ : syracuseStep 4693747 = 7040621) B7040621
theorem B3342151 : Blo 1853628 3342151 := bstep (se 1 (by rfl) ⟨2506613, by rfl⟩ : syracuseStep 3342151 = 5013227) B5013227
theorem B3129259 : Blo 1853628 3129259 := bstep (se 1 (by rfl) ⟨2346944, by rfl⟩ : syracuseStep 3129259 = 4693889) B4693889
theorem B5284055 : Blo 1853628 5284055 := bstep (se 1 (by rfl) ⟨3963041, by rfl⟩ : syracuseStep 5284055 = 7926083) B7926083
theorem B14082335 : Blo 1853628 14082335 := bstep (se 1 (by rfl) ⟨10561751, by rfl⟩ : syracuseStep 14082335 = 21123503) B21123503
theorem B50757947 : Blo 1853628 50757947 := bstep (se 1 (by rfl) ⟨38068460, by rfl⟩ : syracuseStep 50757947 = 76136921) B76136921
theorem B4759903 : Blo 1853628 4759903 := bstep (se 1 (by rfl) ⟨3569927, by rfl⟩ : syracuseStep 4759903 = 7139855) B7139855
theorem B9388385 : Blo 1853628 9388385 := bstep (se 2 (by rfl) ⟨3520644, by rfl⟩ : syracuseStep 9388385 = 7041289) B7041289
theorem B34300367 : Blo 1853628 34300367 := bstep (se 1 (by rfl) ⟨25725275, by rfl⟩ : syracuseStep 34300367 = 51450551) B51450551
theorem B5939705 : Blo 1853628 5939705 := bstep (se 2 (by rfl) ⟨2227389, by rfl⟩ : syracuseStep 5939705 = 4454779) B4454779
theorem B3129887 : Blo 1853628 3129887 := bstep (se 1 (by rfl) ⟨2347415, by rfl⟩ : syracuseStep 3129887 = 4694831) B4694831
theorem B3129961 : Blo 1853628 3129961 := bstep (se 2 (by rfl) ⟨1173735, by rfl⟩ : syracuseStep 3129961 = 2347471) B2347471
theorem B2229023 : Blo 1853628 2229023 := bstep (se 1 (by rfl) ⟨1671767, by rfl⟩ : syracuseStep 2229023 = 3343535) B3343535
theorem B6259517 : Blo 1853628 6259517 := bstep (se 3 (by rfl) ⟨1173659, by rfl⟩ : syracuseStep 6259517 = 2347319) B2347319
theorem B4694881 : Blo 1853628 4694881 := bstep (se 2 (by rfl) ⟨1760580, by rfl⟩ : syracuseStep 4694881 = 3521161) B3521161
theorem B8913863 : Blo 1853628 8913863 := bstep (se 1 (by rfl) ⟨6685397, by rfl⟩ : syracuseStep 8913863 = 13370795) B13370795
theorem B4228159 : Blo 1853628 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B4457663 : Blo 1853628 4457663 := bstep (se 1 (by rfl) ⟨3343247, by rfl⟩ : syracuseStep 4457663 = 6686495) B6686495
theorem B6260219 : Blo 1853628 6260219 := bstep (se 1 (by rfl) ⟨4695164, by rfl⟩ : syracuseStep 6260219 = 9390329) B9390329
theorem B4171337 : Blo 1853628 4171337 := bstep (se 2 (by rfl) ⟨1564251, by rfl⟩ : syracuseStep 4171337 = 3128503) B3128503
theorem B3130987 : Blo 1853628 3130987 := bstep (se 1 (by rfl) ⟨2348240, by rfl⟩ : syracuseStep 3130987 = 4696481) B4696481
theorem B650200765 : Blo 1853628 650200765 := bstep (se 3 (by rfl) ⟨121912643, by rfl⟩ : syracuseStep 650200765 = 243825287) B243825287
theorem B8914691 : Blo 1853628 8914691 := bstep (se 1 (by rfl) ⟨6686018, by rfl⟩ : syracuseStep 8914691 = 13372037) B13372037
theorem B3131257 : Blo 1853628 3131257 := bstep (se 2 (by rfl) ⟨1174221, by rfl⟩ : syracuseStep 3131257 = 2348443) B2348443
theorem B7038859 : Blo 1853628 7038859 := bstep (se 1 (by rfl) ⟨5279144, by rfl⟩ : syracuseStep 7038859 = 10558289) B10558289
theorem B4171769 : Blo 1853628 4171769 := bstep (se 2 (by rfl) ⟨1564413, by rfl⟩ : syracuseStep 4171769 = 3128827) B3128827
theorem B4171823 : Blo 1853628 4171823 := bstep (se 1 (by rfl) ⟨3128867, by rfl⟩ : syracuseStep 4171823 = 6257735) B6257735
theorem B42805297 : Blo 1853628 42805297 := bstep (se 2 (by rfl) ⟨16051986, by rfl⟩ : syracuseStep 42805297 = 32103973) B32103973
theorem B4171859 : Blo 1853628 4171859 := bstep (se 1 (by rfl) ⟨3128894, by rfl⟩ : syracuseStep 4171859 = 6257789) B6257789
theorem B33851479 : Blo 1853628 33851479 := bstep (se 1 (by rfl) ⟨25388609, by rfl⟩ : syracuseStep 33851479 = 50777219) B50777219
theorem B21129335 : Blo 1853628 21129335 := bstep (se 1 (by rfl) ⟨15847001, by rfl⟩ : syracuseStep 21129335 = 31694003) B31694003
theorem B1853663 : Blo 1853628 1853663 := bstep (se 1 (by rfl) ⟨1390247, by rfl⟩ : syracuseStep 1853663 = 2780495) B2780495
theorem B4172039 : Blo 1853628 4172039 := bstep (se 1 (by rfl) ⟨3129029, by rfl⟩ : syracuseStep 4172039 = 6258059) B6258059
theorem B1853723 : Blo 1853628 1853723 := bstep (se 1 (by rfl) ⟨1390292, by rfl⟩ : syracuseStep 1853723 = 2780585) B2780585
theorem B1853823 : Blo 1853628 1853823 := bstep (se 1 (by rfl) ⟨1390367, by rfl⟩ : syracuseStep 1853823 = 2780735) B2780735
theorem B1853999 : Blo 1853628 1853999 := bstep (se 1 (by rfl) ⟨1390499, by rfl⟩ : syracuseStep 1853999 = 2780999) B2780999
theorem B4172345 : Blo 1853628 4172345 := bstep (se 2 (by rfl) ⟨1564629, by rfl⟩ : syracuseStep 4172345 = 3129259) B3129259
theorem B10701401 : Blo 1853628 10701401 := bstep (se 2 (by rfl) ⟨4013025, by rfl⟩ : syracuseStep 10701401 = 8026051) B8026051
theorem B1854055 : Blo 1853628 1854055 := bstep (se 1 (by rfl) ⟨1390541, by rfl⟩ : syracuseStep 1854055 = 2781083) B2781083
theorem B12044915 : Blo 1853628 12044915 := bstep (se 1 (by rfl) ⟨9033686, by rfl⟩ : syracuseStep 12044915 = 18067373) B18067373
theorem B7039831 : Blo 1853628 7039831 := bstep (se 1 (by rfl) ⟨5279873, by rfl⟩ : syracuseStep 7039831 = 10559747) B10559747
theorem B10709921 : Blo 1853628 10709921 := bstep (se 2 (by rfl) ⟨4016220, by rfl⟩ : syracuseStep 10709921 = 8032441) B8032441
theorem B1854431 : Blo 1853628 1854431 := bstep (se 1 (by rfl) ⟨1390823, by rfl⟩ : syracuseStep 1854431 = 2781647) B2781647
theorem B1854459 : Blo 1853628 1854459 := bstep (se 1 (by rfl) ⟨1390844, by rfl⟩ : syracuseStep 1854459 = 2781689) B2781689
theorem B15846455 : Blo 1853628 15846455 := bstep (se 1 (by rfl) ⟨11884841, by rfl⟩ : syracuseStep 15846455 = 23769683) B23769683
theorem B1854527 : Blo 1853628 1854527 := bstep (se 1 (by rfl) ⟨1390895, by rfl⟩ : syracuseStep 1854527 = 2781791) B2781791
theorem B6261947 : Blo 1853628 6261947 := bstep (se 1 (by rfl) ⟨4696460, by rfl⟩ : syracuseStep 6261947 = 9392921) B9392921
theorem B4173065 : Blo 1853628 4173065 := bstep (se 2 (by rfl) ⟨1564899, by rfl⟩ : syracuseStep 4173065 = 3129799) B3129799
theorem B5352743 : Blo 1853628 5352743 := bstep (se 1 (by rfl) ⟨4014557, by rfl⟩ : syracuseStep 5352743 = 8029115) B8029115
theorem B2780471 : Blo 1853628 2780471 := bstep (se 1 (by rfl) ⟨2085353, by rfl⟩ : syracuseStep 2780471 = 4170707) B4170707
theorem B1854847 : Blo 1853628 1854847 := bstep (se 1 (by rfl) ⟨1391135, by rfl⟩ : syracuseStep 1854847 = 2782271) B2782271
theorem B1854875 : Blo 1853628 1854875 := bstep (se 1 (by rfl) ⟨1391156, by rfl⟩ : syracuseStep 1854875 = 2782313) B2782313
theorem B11283895 : Blo 1853628 11283895 := bstep (se 1 (by rfl) ⟨8462921, by rfl⟩ : syracuseStep 11283895 = 16925843) B16925843
theorem B2780639 : Blo 1853628 2780639 := bstep (se 1 (by rfl) ⟨2085479, by rfl⟩ : syracuseStep 2780639 = 4170959) B4170959
theorem B1854943 : Blo 1853628 1854943 := bstep (se 1 (by rfl) ⟨1391207, by rfl⟩ : syracuseStep 1854943 = 2782415) B2782415
theorem B3173855 : Blo 1853628 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B1855079 : Blo 1853628 1855079 := bstep (se 1 (by rfl) ⟨1391309, by rfl⟩ : syracuseStep 1855079 = 2782619) B2782619
theorem B17141395 : Blo 1853628 17141395 := bstep (se 1 (by rfl) ⟨12856046, by rfl⟩ : syracuseStep 17141395 = 25712093) B25712093
theorem B2780855 : Blo 1853628 2780855 := bstep (se 1 (by rfl) ⟨2085641, by rfl⟩ : syracuseStep 2780855 = 4171283) B4171283
theorem B32132807 : Blo 1853628 32132807 := bstep (se 1 (by rfl) ⟨24099605, by rfl⟩ : syracuseStep 32132807 = 48199211) B48199211
theorem B1855227 : Blo 1853628 1855227 := bstep (se 1 (by rfl) ⟨1391420, by rfl⟩ : syracuseStep 1855227 = 2782841) B2782841
theorem B1855295 : Blo 1853628 1855295 := bstep (se 1 (by rfl) ⟨1391471, by rfl⟩ : syracuseStep 1855295 = 2782943) B2782943
theorem B1855359 : Blo 1853628 1855359 := bstep (se 1 (by rfl) ⟨1391519, by rfl⟩ : syracuseStep 1855359 = 2783039) B2783039
theorem B2781065 : Blo 1853628 2781065 := bstep (se 2 (by rfl) ⟨1042899, by rfl⟩ : syracuseStep 2781065 = 2085799) B2085799
theorem B32550839 : Blo 1853628 32550839 := bstep (se 1 (by rfl) ⟨24413129, by rfl⟩ : syracuseStep 32550839 = 48826259) B48826259
theorem B14471095 : Blo 1853628 14471095 := bstep (se 1 (by rfl) ⟨10853321, by rfl⟩ : syracuseStep 14471095 = 21706643) B21706643
theorem B1855471 : Blo 1853628 1855471 := bstep (se 1 (by rfl) ⟨1391603, by rfl⟩ : syracuseStep 1855471 = 2783207) B2783207
theorem B1855483 : Blo 1853628 1855483 := bstep (se 1 (by rfl) ⟨1391612, by rfl⟩ : syracuseStep 1855483 = 2783225) B2783225
theorem B1855551 : Blo 1853628 1855551 := bstep (se 1 (by rfl) ⟨1391663, by rfl⟩ : syracuseStep 1855551 = 2783327) B2783327
theorem B7041107 : Blo 1853628 7041107 := bstep (se 1 (by rfl) ⟨5280830, by rfl⟩ : syracuseStep 7041107 = 10561661) B10561661
theorem B1855591 : Blo 1853628 1855591 := bstep (se 1 (by rfl) ⟨1391693, by rfl⟩ : syracuseStep 1855591 = 2783387) B2783387
theorem B2781311 : Blo 1853628 2781311 := bstep (se 1 (by rfl) ⟨2085983, by rfl⟩ : syracuseStep 2781311 = 4171967) B4171967
theorem B1855615 : Blo 1853628 1855615 := bstep (se 1 (by rfl) ⟨1391711, by rfl⟩ : syracuseStep 1855615 = 2783423) B2783423
theorem B23761025 : Blo 1853628 23761025 := bstep (se 2 (by rfl) ⟨8910384, by rfl⟩ : syracuseStep 23761025 = 17820769) B17820769
theorem B4174055 : Blo 1853628 4174055 := bstep (se 1 (by rfl) ⟨3130541, by rfl⟩ : syracuseStep 4174055 = 6261083) B6261083
theorem B659263859 : Blo 1853628 659263859 := bstep (se 1 (by rfl) ⟨494447894, by rfl⟩ : syracuseStep 659263859 = 988895789) B988895789
theorem B4174235 : Blo 1853628 4174235 := bstep (se 1 (by rfl) ⟨3130676, by rfl⟩ : syracuseStep 4174235 = 6261353) B6261353
theorem B5280329 : Blo 1853628 5280329 := bstep (se 2 (by rfl) ⟨1980123, by rfl⟩ : syracuseStep 5280329 = 3960247) B3960247
theorem B6681217 : Blo 1853628 6681217 := bstep (se 2 (by rfl) ⟨2505456, by rfl⟩ : syracuseStep 6681217 = 5010913) B5010913
theorem B17863325 : Blo 1853628 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B2781947 : Blo 1853628 2781947 := bstep (se 1 (by rfl) ⟨2086460, by rfl⟩ : syracuseStep 2781947 = 4172921) B4172921
theorem B3961811 : Blo 1853628 3961811 := bstep (se 1 (by rfl) ⟨2971358, by rfl⟩ : syracuseStep 3961811 = 5942717) B5942717
theorem B2085871 : Blo 1853628 2085871 := bstep (se 1 (by rfl) ⟨1564403, by rfl⟩ : syracuseStep 2085871 = 3128807) B3128807
theorem B4174919 : Blo 1853628 4174919 := bstep (se 1 (by rfl) ⟨3131189, by rfl⟩ : syracuseStep 4174919 = 6262379) B6262379
theorem B23761997 : Blo 1853628 23761997 := bstep (se 3 (by rfl) ⟨4455374, by rfl⟩ : syracuseStep 23761997 = 8910749) B8910749
theorem B2782391 : Blo 1853628 2782391 := bstep (se 1 (by rfl) ⟨2086793, by rfl⟩ : syracuseStep 2782391 = 4173587) B4173587
theorem B4175099 : Blo 1853628 4175099 := bstep (se 1 (by rfl) ⟨3131324, by rfl⟩ : syracuseStep 4175099 = 6262649) B6262649
theorem B12047723 : Blo 1853628 12047723 := bstep (se 1 (by rfl) ⟨9035792, by rfl⟩ : syracuseStep 12047723 = 18071585) B18071585
theorem B2782631 : Blo 1853628 2782631 := bstep (se 1 (by rfl) ⟨2086973, by rfl⟩ : syracuseStep 2782631 = 4173947) B4173947
theorem B2086375 : Blo 1853628 2086375 := bstep (se 1 (by rfl) ⟨1564781, by rfl⟩ : syracuseStep 2086375 = 3129563) B3129563
theorem B9385469 : Blo 1853628 9385469 := bstep (se 3 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 9385469 = 3519551) B3519551
theorem B5355005 : Blo 1853628 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B3520091 : Blo 1853628 3520091 := bstep (se 1 (by rfl) ⟨2640068, by rfl⟩ : syracuseStep 3520091 = 5280137) B5280137
theorem B2782811 : Blo 1853628 2782811 := bstep (se 1 (by rfl) ⟨2087108, by rfl⟩ : syracuseStep 2782811 = 4174217) B4174217
theorem B6256223 : Blo 1853628 6256223 := bstep (se 1 (by rfl) ⟨4692167, by rfl⟩ : syracuseStep 6256223 = 9384335) B9384335
theorem B5011055 : Blo 1853628 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B2086555 : Blo 1853628 2086555 := bstep (se 1 (by rfl) ⟨1564916, by rfl⟩ : syracuseStep 2086555 = 3129833) B3129833
theorem B5715841 : Blo 1853628 5715841 := bstep (se 2 (by rfl) ⟨2143440, by rfl⟩ : syracuseStep 5715841 = 4286881) B4286881
theorem B2783273 : Blo 1853628 2783273 := bstep (se 2 (by rfl) ⟨1043727, by rfl⟩ : syracuseStep 2783273 = 2087455) B2087455
theorem B4454471 : Blo 1853628 4454471 := bstep (se 1 (by rfl) ⟨3340853, by rfl⟩ : syracuseStep 4454471 = 6681707) B6681707
theorem B2783303 : Blo 1853628 2783303 := bstep (se 1 (by rfl) ⟨2087477, by rfl⟩ : syracuseStep 2783303 = 4174955) B4174955
theorem B7043233 : Blo 1853628 7043233 := bstep (se 2 (by rfl) ⟨2641212, by rfl⟩ : syracuseStep 7043233 = 5282425) B5282425
theorem B9386279 : Blo 1853628 9386279 := bstep (se 1 (by rfl) ⟨7039709, by rfl⟩ : syracuseStep 9386279 = 14079419) B14079419
theorem B8460587 : Blo 1853628 8460587 := bstep (se 1 (by rfl) ⟨6345440, by rfl⟩ : syracuseStep 8460587 = 12690881) B12690881
theorem B35658215 : Blo 1853628 35658215 := bstep (se 1 (by rfl) ⟨26743661, by rfl⟩ : syracuseStep 35658215 = 53487323) B53487323
theorem B21420571 : Blo 1853628 21420571 := bstep (se 1 (by rfl) ⟨16065428, by rfl⟩ : syracuseStep 21420571 = 32130857) B32130857
theorem B10566287 : Blo 1853628 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B17816273 : Blo 1853628 17816273 := bstep (se 2 (by rfl) ⟨6681102, by rfl⟩ : syracuseStep 17816273 = 13362205) B13362205
theorem B4693423 : Blo 1853628 4693423 := bstep (se 1 (by rfl) ⟨3520067, by rfl⟩ : syracuseStep 4693423 = 7040135) B7040135
theorem B5013011 : Blo 1853628 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B6258329 : Blo 1853628 6258329 := bstep (se 2 (by rfl) ⟨2346873, by rfl⟩ : syracuseStep 6258329 = 4693747) B4693747
theorem B13369063 : Blo 1853628 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B12689129 : Blo 1853628 12689129 := bstep (se 2 (by rfl) ⟨4758423, by rfl⟩ : syracuseStep 12689129 = 9516847) B9516847
theorem B3129097 : Blo 1853628 3129097 := bstep (se 2 (by rfl) ⟨1173411, by rfl⟩ : syracuseStep 3129097 = 2346823) B2346823
theorem B4456201 : Blo 1853628 4456201 := bstep (se 2 (by rfl) ⟨1671075, by rfl⟩ : syracuseStep 4456201 = 3342151) B3342151
theorem B4694071 : Blo 1853628 4694071 := bstep (se 1 (by rfl) ⟨3520553, by rfl⟩ : syracuseStep 4694071 = 7041107) B7041107
theorem B57073729 : Blo 1853628 57073729 := bstep (se 2 (by rfl) ⟨21402648, by rfl⟩ : syracuseStep 57073729 = 42805297) B42805297
theorem B3522703 : Blo 1853628 3522703 := bstep (se 1 (by rfl) ⟨2642027, by rfl⟩ : syracuseStep 3522703 = 5284055) B5284055
theorem B11878589 : Blo 1853628 11878589 := bstep (se 3 (by rfl) ⟨2227235, by rfl⟩ : syracuseStep 11878589 = 4454471) B4454471
theorem B9388223 : Blo 1853628 9388223 := bstep (se 1 (by rfl) ⟨7041167, by rfl⟩ : syracuseStep 9388223 = 14082335) B14082335
theorem B6258923 : Blo 1853628 6258923 := bstep (se 1 (by rfl) ⟨4694192, by rfl⟩ : syracuseStep 6258923 = 9388385) B9388385
theorem B439509239 : Blo 1853628 439509239 := bstep (se 1 (by rfl) ⟨329631929, by rfl⟩ : syracuseStep 439509239 = 659263859) B659263859
theorem B4170815 : Blo 1853628 4170815 := bstep (se 1 (by rfl) ⟨3128111, by rfl⟩ : syracuseStep 4170815 = 6256223) B6256223
theorem B6259841 : Blo 1853628 6259841 := bstep (se 2 (by rfl) ⟨2347440, by rfl⟩ : syracuseStep 6259841 = 4694881) B4694881
theorem B14280013 : Blo 1853628 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B5637545 : Blo 1853628 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B8029943 : Blo 1853628 8029943 := bstep (se 1 (by rfl) ⟨6022457, by rfl⟩ : syracuseStep 8029943 = 12044915) B12044915
theorem B1853647 : Blo 1853628 1853647 := bstep (se 1 (by rfl) ⟨1390235, by rfl⟩ : syracuseStep 1853647 = 2780471) B2780471
theorem B1853759 : Blo 1853628 1853759 := bstep (se 1 (by rfl) ⟨1390319, by rfl⟩ : syracuseStep 1853759 = 2780639) B2780639
theorem B4172129 : Blo 1853628 4172129 := bstep (se 2 (by rfl) ⟨1564548, by rfl⟩ : syracuseStep 4172129 = 3129097) B3129097
theorem B5941601 : Blo 1853628 5941601 := bstep (se 2 (by rfl) ⟨2228100, by rfl⟩ : syracuseStep 5941601 = 4456201) B4456201
theorem B4172219 : Blo 1853628 4172219 := bstep (se 1 (by rfl) ⟨3129164, by rfl⟩ : syracuseStep 4172219 = 6258329) B6258329
theorem B1853903 : Blo 1853628 1853903 := bstep (se 1 (by rfl) ⟨1390427, by rfl⟩ : syracuseStep 1853903 = 2780855) B2780855
theorem B7621121 : Blo 1853628 7621121 := bstep (se 2 (by rfl) ⟨2857920, by rfl⟩ : syracuseStep 7621121 = 5715841) B5715841
theorem B19294793 : Blo 1853628 19294793 := bstep (se 2 (by rfl) ⟨7235547, by rfl⟩ : syracuseStep 19294793 = 14471095) B14471095
theorem B1854043 : Blo 1853628 1854043 := bstep (se 1 (by rfl) ⟨1390532, by rfl⟩ : syracuseStep 1854043 = 2781065) B2781065
theorem B1854207 : Blo 1853628 1854207 := bstep (se 1 (by rfl) ⟨1390655, by rfl⟩ : syracuseStep 1854207 = 2781311) B2781311
theorem B9390977 : Blo 1853628 9390977 := bstep (se 2 (by rfl) ⟨3521616, by rfl⟩ : syracuseStep 9390977 = 7043233) B7043233
theorem B22866911 : Blo 1853628 22866911 := bstep (se 1 (by rfl) ⟨17150183, by rfl⟩ : syracuseStep 22866911 = 34300367) B34300367
theorem B3959803 : Blo 1853628 3959803 := bstep (se 1 (by rfl) ⟨2969852, by rfl⟩ : syracuseStep 3959803 = 5939705) B5939705
theorem B1854631 : Blo 1853628 1854631 := bstep (se 1 (by rfl) ⟨1390973, by rfl⟩ : syracuseStep 1854631 = 2781947) B2781947
theorem B4173011 : Blo 1853628 4173011 := bstep (se 1 (by rfl) ⟨3129758, by rfl⟩ : syracuseStep 4173011 = 6259517) B6259517
theorem B5942575 : Blo 1853628 5942575 := bstep (se 1 (by rfl) ⟨4456931, by rfl⟩ : syracuseStep 5942575 = 8913863) B8913863
theorem B28560761 : Blo 1853628 28560761 := bstep (se 2 (by rfl) ⟨10710285, by rfl⟩ : syracuseStep 28560761 = 21420571) B21420571
theorem B14273981 : Blo 1853628 14273981 := bstep (se 3 (by rfl) ⟨2676371, by rfl⟩ : syracuseStep 14273981 = 5352743) B5352743
theorem B1854927 : Blo 1853628 1854927 := bstep (se 1 (by rfl) ⟨1391195, by rfl⟩ : syracuseStep 1854927 = 2782391) B2782391
theorem B4173281 : Blo 1853628 4173281 := bstep (se 2 (by rfl) ⟨1564980, by rfl⟩ : syracuseStep 4173281 = 3129961) B3129961
theorem B8908289 : Blo 1853628 8908289 := bstep (se 2 (by rfl) ⟨3340608, by rfl⟩ : syracuseStep 8908289 = 6681217) B6681217
theorem B8031815 : Blo 1853628 8031815 := bstep (se 1 (by rfl) ⟨6023861, by rfl⟩ : syracuseStep 8031815 = 12047723) B12047723
theorem B1855087 : Blo 1853628 1855087 := bstep (se 1 (by rfl) ⟨1391315, by rfl⟩ : syracuseStep 1855087 = 2782631) B2782631
theorem B4173479 : Blo 1853628 4173479 := bstep (se 1 (by rfl) ⟨3130109, by rfl⟩ : syracuseStep 4173479 = 6260219) B6260219
theorem B2780891 : Blo 1853628 2780891 := bstep (se 1 (by rfl) ⟨2085668, by rfl⟩ : syracuseStep 2780891 = 4171337) B4171337
theorem B2346727 : Blo 1853628 2346727 := bstep (se 1 (by rfl) ⟨1760045, by rfl⟩ : syracuseStep 2346727 = 3520091) B3520091
theorem B1855207 : Blo 1853628 1855207 := bstep (se 1 (by rfl) ⟨1391405, by rfl⟩ : syracuseStep 1855207 = 2782811) B2782811
theorem B5943127 : Blo 1853628 5943127 := bstep (se 1 (by rfl) ⟨4457345, by rfl⟩ : syracuseStep 5943127 = 8914691) B8914691
theorem B2781161 : Blo 1853628 2781161 := bstep (se 2 (by rfl) ⟨1042935, by rfl⟩ : syracuseStep 2781161 = 2085871) B2085871
theorem B2781179 : Blo 1853628 2781179 := bstep (se 1 (by rfl) ⟨2085884, by rfl⟩ : syracuseStep 2781179 = 4171769) B4171769
theorem B1855515 : Blo 1853628 1855515 := bstep (se 1 (by rfl) ⟨1391636, by rfl⟩ : syracuseStep 1855515 = 2783273) B2783273
theorem B2781215 : Blo 1853628 2781215 := bstep (se 1 (by rfl) ⟨2085911, by rfl⟩ : syracuseStep 2781215 = 4171823) B4171823
theorem B1855535 : Blo 1853628 1855535 := bstep (se 1 (by rfl) ⟨1391651, by rfl⟩ : syracuseStep 1855535 = 2783303) B2783303
theorem B2781239 : Blo 1853628 2781239 := bstep (se 1 (by rfl) ⟨2085929, by rfl⟩ : syracuseStep 2781239 = 4171859) B4171859
theorem B14086223 : Blo 1853628 14086223 := bstep (se 1 (by rfl) ⟨10564667, by rfl⟩ : syracuseStep 14086223 = 21129335) B21129335
theorem B2781359 : Blo 1853628 2781359 := bstep (se 1 (by rfl) ⟨2086019, by rfl⟩ : syracuseStep 2781359 = 4172039) B4172039
theorem B5640391 : Blo 1853628 5640391 := bstep (se 1 (by rfl) ⟨4230293, by rfl⟩ : syracuseStep 5640391 = 8460587) B8460587
theorem B28537069 : Blo 1853628 28537069 := bstep (se 3 (by rfl) ⟨5350700, by rfl⟩ : syracuseStep 28537069 = 10701401) B10701401
theorem B2781563 : Blo 1853628 2781563 := bstep (se 1 (by rfl) ⟨2086172, by rfl⟩ : syracuseStep 2781563 = 4172345) B4172345
theorem B15045193 : Blo 1853628 15045193 := bstep (se 2 (by rfl) ⟨5641947, by rfl⟩ : syracuseStep 15045193 = 11283895) B11283895
theorem B7139947 : Blo 1853628 7139947 := bstep (se 1 (by rfl) ⟨5354960, by rfl⟩ : syracuseStep 7139947 = 10709921) B10709921
theorem B2781833 : Blo 1853628 2781833 := bstep (se 2 (by rfl) ⟨1043187, by rfl⟩ : syracuseStep 2781833 = 2086375) B2086375
theorem B10564303 : Blo 1853628 10564303 := bstep (se 1 (by rfl) ⟨7923227, by rfl⟩ : syracuseStep 10564303 = 15846455) B15846455
theorem B5944061 : Blo 1853628 5944061 := bstep (se 3 (by rfl) ⟨1114511, by rfl⟩ : syracuseStep 5944061 = 2229023) B2229023
theorem B4174631 : Blo 1853628 4174631 := bstep (se 1 (by rfl) ⟨3130973, by rfl⟩ : syracuseStep 4174631 = 6261947) B6261947
theorem B4174649 : Blo 1853628 4174649 := bstep (se 2 (by rfl) ⟨1565493, by rfl⟩ : syracuseStep 4174649 = 3130987) B3130987
theorem B2782043 : Blo 1853628 2782043 := bstep (se 1 (by rfl) ⟨2086532, by rfl⟩ : syracuseStep 2782043 = 4173065) B4173065
theorem B2782073 : Blo 1853628 2782073 := bstep (se 2 (by rfl) ⟨1043277, by rfl⟩ : syracuseStep 2782073 = 2086555) B2086555
theorem B33854453 : Blo 1853628 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B8459419 : Blo 1853628 8459419 := bstep (se 1 (by rfl) ⟨6344564, by rfl⟩ : syracuseStep 8459419 = 12689129) B12689129
theorem B4175009 : Blo 1853628 4175009 := bstep (se 2 (by rfl) ⟨1565628, by rfl⟩ : syracuseStep 4175009 = 3131257) B3131257
theorem B9385145 : Blo 1853628 9385145 := bstep (se 2 (by rfl) ⟨3519429, by rfl⟩ : syracuseStep 9385145 = 7038859) B7038859
theorem B10564829 : Blo 1853628 10564829 := bstep (se 3 (by rfl) ⟨1980905, by rfl⟩ : syracuseStep 10564829 = 3961811) B3961811
theorem B15840683 : Blo 1853628 15840683 := bstep (se 1 (by rfl) ⟨11880512, by rfl⟩ : syracuseStep 15840683 = 23761025) B23761025
theorem B45135305 : Blo 1853628 45135305 := bstep (se 2 (by rfl) ⟨16925739, by rfl⟩ : syracuseStep 45135305 = 33851479) B33851479
theorem B2782703 : Blo 1853628 2782703 := bstep (se 1 (by rfl) ⟨2087027, by rfl⟩ : syracuseStep 2782703 = 4174055) B4174055
theorem B33838631 : Blo 1853628 33838631 := bstep (se 1 (by rfl) ⟨25378973, by rfl⟩ : syracuseStep 33838631 = 50757947) B50757947
theorem B2782823 : Blo 1853628 2782823 := bstep (se 1 (by rfl) ⟨2087117, by rfl⟩ : syracuseStep 2782823 = 4174235) B4174235
theorem B2086591 : Blo 1853628 2086591 := bstep (se 1 (by rfl) ⟨1564943, by rfl⟩ : syracuseStep 2086591 = 3129887) B3129887
theorem B11908883 : Blo 1853628 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B2783279 : Blo 1853628 2783279 := bstep (se 1 (by rfl) ⟨2087459, by rfl⟩ : syracuseStep 2783279 = 4174919) B4174919
theorem B15841331 : Blo 1853628 15841331 := bstep (se 1 (by rfl) ⟨11880998, by rfl⟩ : syracuseStep 15841331 = 23761997) B23761997
theorem B2971775 : Blo 1853628 2971775 := bstep (se 1 (by rfl) ⟨2228831, by rfl⟩ : syracuseStep 2971775 = 4457663) B4457663
theorem B2783399 : Blo 1853628 2783399 := bstep (se 1 (by rfl) ⟨2087549, by rfl⟩ : syracuseStep 2783399 = 4175099) B4175099
theorem B6256979 : Blo 1853628 6256979 := bstep (se 1 (by rfl) ⟨4692734, by rfl⟩ : syracuseStep 6256979 = 9385469) B9385469
theorem B3340703 : Blo 1853628 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B9386441 : Blo 1853628 9386441 := bstep (se 2 (by rfl) ⟨3519915, by rfl⟩ : syracuseStep 9386441 = 7039831) B7039831
theorem B14080877 : Blo 1853628 14080877 := bstep (se 3 (by rfl) ⟨2640164, by rfl⟩ : syracuseStep 14080877 = 5280329) B5280329
theorem B6257519 : Blo 1853628 6257519 := bstep (se 1 (by rfl) ⟨4693139, by rfl⟩ : syracuseStep 6257519 = 9386279) B9386279
theorem B23772143 : Blo 1853628 23772143 := bstep (se 1 (by rfl) ⟨17829107, by rfl⟩ : syracuseStep 23772143 = 35658215) B35658215
theorem B7044191 : Blo 1853628 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B11877515 : Blo 1853628 11877515 := bstep (se 1 (by rfl) ⟨8908136, by rfl⟩ : syracuseStep 11877515 = 17816273) B17816273
theorem B25386149 : Blo 1853628 25386149 := bstep (se 4 (by rfl) ⟨2379951, by rfl⟩ : syracuseStep 25386149 = 4759903) B4759903
theorem B6257897 : Blo 1853628 6257897 := bstep (se 2 (by rfl) ⟨2346711, by rfl⟩ : syracuseStep 6257897 = 4693423) B4693423
theorem B22855193 : Blo 1853628 22855193 := bstep (se 2 (by rfl) ⟨8570697, by rfl⟩ : syracuseStep 22855193 = 17141395) B17141395
theorem B866934353 : Blo 1853628 866934353 := bstep (se 2 (by rfl) ⟨325100382, by rfl⟩ : syracuseStep 866934353 = 650200765) B650200765
theorem B17825417 : Blo 1853628 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B3342007 : Blo 1853628 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B21421871 : Blo 1853628 21421871 := bstep (se 1 (by rfl) ⟨16066403, by rfl⟩ : syracuseStep 21421871 = 32132807) B32132807
theorem B21700559 : Blo 1853628 21700559 := bstep (se 1 (by rfl) ⟨16275419, by rfl⟩ : syracuseStep 21700559 = 32550839) B32550839
theorem B6258761 : Blo 1853628 6258761 := bstep (se 2 (by rfl) ⟨2347035, by rfl⟩ : syracuseStep 6258761 = 4694071) B4694071
theorem B6258815 : Blo 1853628 6258815 := bstep (se 1 (by rfl) ⟨4694111, by rfl⟩ : syracuseStep 6258815 = 9388223) B9388223
theorem B7520521 : Blo 1853628 7520521 := bstep (se 2 (by rfl) ⟨2820195, by rfl⟩ : syracuseStep 7520521 = 5640391) B5640391
theorem B80241029 : Blo 1853628 80241029 := bstep (se 4 (by rfl) ⟨7522596, by rfl⟩ : syracuseStep 80241029 = 15045193) B15045193
theorem B22569635 : Blo 1853628 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B9519929 : Blo 1853628 9519929 := bstep (se 2 (by rfl) ⟨3569973, by rfl⟩ : syracuseStep 9519929 = 7139947) B7139947
theorem B10560455 : Blo 1853628 10560455 := bstep (se 1 (by rfl) ⟨7920341, by rfl⟩ : syracuseStep 10560455 = 15840683) B15840683
theorem B30090203 : Blo 1853628 30090203 := bstep (se 1 (by rfl) ⟨22567652, by rfl⟩ : syracuseStep 30090203 = 45135305) B45135305
theorem B7939255 : Blo 1853628 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B10560887 : Blo 1853628 10560887 := bstep (se 1 (by rfl) ⟨7920665, by rfl⟩ : syracuseStep 10560887 = 15841331) B15841331
theorem B4171319 : Blo 1853628 4171319 := bstep (se 1 (by rfl) ⟨3128489, by rfl⟩ : syracuseStep 4171319 = 6256979) B6256979
theorem B5080747 : Blo 1853628 5080747 := bstep (se 1 (by rfl) ⟨3810560, by rfl⟩ : syracuseStep 5080747 = 7621121) B7621121
theorem B12863195 : Blo 1853628 12863195 := bstep (se 1 (by rfl) ⟨9647396, by rfl⟩ : syracuseStep 12863195 = 19294793) B19294793
theorem B7923433 : Blo 1853628 7923433 := bstep (se 2 (by rfl) ⟨2971287, by rfl⟩ : syracuseStep 7923433 = 5942575) B5942575
theorem B19040017 : Blo 1853628 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B4171679 : Blo 1853628 4171679 := bstep (se 1 (by rfl) ⟨3128759, by rfl⟩ : syracuseStep 4171679 = 6257519) B6257519
theorem B6260651 : Blo 1853628 6260651 := bstep (se 1 (by rfl) ⟨4695488, by rfl⟩ : syracuseStep 6260651 = 9390977) B9390977
theorem B4696127 : Blo 1853628 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B4171931 : Blo 1853628 4171931 := bstep (se 1 (by rfl) ⟨3128948, by rfl⟩ : syracuseStep 4171931 = 6257897) B6257897
theorem B19040507 : Blo 1853628 19040507 := bstep (se 1 (by rfl) ⟨14280380, by rfl⟩ : syracuseStep 19040507 = 28560761) B28560761
theorem B577956235 : Blo 1853628 577956235 := bstep (se 1 (by rfl) ⟨433467176, by rfl⟩ : syracuseStep 577956235 = 866934353) B866934353
theorem B7924169 : Blo 1853628 7924169 := bstep (se 2 (by rfl) ⟨2971563, by rfl⟩ : syracuseStep 7924169 = 5943127) B5943127
theorem B1853927 : Blo 1853628 1853927 := bstep (se 1 (by rfl) ⟨1390445, by rfl⟩ : syracuseStep 1853927 = 2780891) B2780891
theorem B14281247 : Blo 1853628 14281247 := bstep (se 1 (by rfl) ⟨10710935, by rfl⟩ : syracuseStep 14281247 = 21421871) B21421871
theorem B1854107 : Blo 1853628 1854107 := bstep (se 1 (by rfl) ⟨1390580, by rfl⟩ : syracuseStep 1854107 = 2781161) B2781161
theorem B1854119 : Blo 1853628 1854119 := bstep (se 1 (by rfl) ⟨1390589, by rfl⟩ : syracuseStep 1854119 = 2781179) B2781179
theorem B1854143 : Blo 1853628 1854143 := bstep (se 1 (by rfl) ⟨1390607, by rfl⟩ : syracuseStep 1854143 = 2781215) B2781215
theorem B1854159 : Blo 1853628 1854159 := bstep (se 1 (by rfl) ⟨1390619, by rfl⟩ : syracuseStep 1854159 = 2781239) B2781239
theorem B9390815 : Blo 1853628 9390815 := bstep (se 1 (by rfl) ⟨7043111, by rfl⟩ : syracuseStep 9390815 = 14086223) B14086223
theorem B76098305 : Blo 1853628 76098305 := bstep (se 2 (by rfl) ⟨28536864, by rfl⟩ : syracuseStep 76098305 = 57073729) B57073729
theorem B1854239 : Blo 1853628 1854239 := bstep (se 1 (by rfl) ⟨1390679, by rfl⟩ : syracuseStep 1854239 = 2781359) B2781359
theorem B4172615 : Blo 1853628 4172615 := bstep (se 1 (by rfl) ⟨3129461, by rfl⟩ : syracuseStep 4172615 = 6258923) B6258923
theorem B293006159 : Blo 1853628 293006159 := bstep (se 1 (by rfl) ⟨219754619, by rfl⟩ : syracuseStep 293006159 = 439509239) B439509239
theorem B4696937 : Blo 1853628 4696937 := bstep (se 2 (by rfl) ⟨1761351, by rfl⟩ : syracuseStep 4696937 = 3522703) B3522703
theorem B1854375 : Blo 1853628 1854375 := bstep (se 1 (by rfl) ⟨1390781, by rfl⟩ : syracuseStep 1854375 = 2781563) B2781563
theorem B1854555 : Blo 1853628 1854555 := bstep (se 1 (by rfl) ⟨1390916, by rfl⟩ : syracuseStep 1854555 = 2781833) B2781833
theorem B1854695 : Blo 1853628 1854695 := bstep (se 1 (by rfl) ⟨1391021, by rfl⟩ : syracuseStep 1854695 = 2782043) B2782043
theorem B1854715 : Blo 1853628 1854715 := bstep (se 1 (by rfl) ⟨1391036, by rfl⟩ : syracuseStep 1854715 = 2782073) B2782073
theorem B2780543 : Blo 1853628 2780543 := bstep (se 1 (by rfl) ⟨2085407, by rfl⟩ : syracuseStep 2780543 = 4170815) B4170815
theorem B4173227 : Blo 1853628 4173227 := bstep (se 1 (by rfl) ⟨3129920, by rfl⟩ : syracuseStep 4173227 = 6259841) B6259841
theorem B14085737 : Blo 1853628 14085737 := bstep (se 2 (by rfl) ⟨5282151, by rfl⟩ : syracuseStep 14085737 = 10564303) B10564303
theorem B1855135 : Blo 1853628 1855135 := bstep (se 1 (by rfl) ⟨1391351, by rfl⟩ : syracuseStep 1855135 = 2782703) B2782703
theorem B1855215 : Blo 1853628 1855215 := bstep (se 1 (by rfl) ⟨1391411, by rfl⟩ : syracuseStep 1855215 = 2782823) B2782823
theorem B8908541 : Blo 1853628 8908541 := bstep (se 3 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 8908541 = 3340703) B3340703
theorem B5353295 : Blo 1853628 5353295 := bstep (se 1 (by rfl) ⟨4014971, by rfl⟩ : syracuseStep 5353295 = 8029943) B8029943
theorem B5279737 : Blo 1853628 5279737 := bstep (se 2 (by rfl) ⟨1979901, by rfl⟩ : syracuseStep 5279737 = 3959803) B3959803
theorem B1855519 : Blo 1853628 1855519 := bstep (se 1 (by rfl) ⟨1391639, by rfl⟩ : syracuseStep 1855519 = 2783279) B2783279
theorem B1855599 : Blo 1853628 1855599 := bstep (se 1 (by rfl) ⟨1391699, by rfl⟩ : syracuseStep 1855599 = 2783399) B2783399
theorem B2781419 : Blo 1853628 2781419 := bstep (se 1 (by rfl) ⟨2086064, by rfl⟩ : syracuseStep 2781419 = 4172129) B4172129
theorem B3961067 : Blo 1853628 3961067 := bstep (se 1 (by rfl) ⟨2970800, by rfl⟩ : syracuseStep 3961067 = 5941601) B5941601
theorem B2781479 : Blo 1853628 2781479 := bstep (se 1 (by rfl) ⟨2086109, by rfl⟩ : syracuseStep 2781479 = 4172219) B4172219
theorem B15848095 : Blo 1853628 15848095 := bstep (se 1 (by rfl) ⟨11886071, by rfl⟩ : syracuseStep 15848095 = 23772143) B23772143
theorem B7918343 : Blo 1853628 7918343 := bstep (se 1 (by rfl) ⟨5938757, by rfl⟩ : syracuseStep 7918343 = 11877515) B11877515
theorem B2782007 : Blo 1853628 2782007 := bstep (se 1 (by rfl) ⟨2086505, by rfl⟩ : syracuseStep 2782007 = 4173011) B4173011
theorem B2782121 : Blo 1853628 2782121 := bstep (se 2 (by rfl) ⟨1043295, by rfl⟩ : syracuseStep 2782121 = 2086591) B2086591
theorem B9515987 : Blo 1853628 9515987 := bstep (se 1 (by rfl) ⟨7136990, by rfl⟩ : syracuseStep 9515987 = 14273981) B14273981
theorem B2782187 : Blo 1853628 2782187 := bstep (se 1 (by rfl) ⟨2086640, by rfl⟩ : syracuseStep 2782187 = 4173281) B4173281
theorem B5354543 : Blo 1853628 5354543 := bstep (se 1 (by rfl) ⟨4015907, by rfl⟩ : syracuseStep 5354543 = 8031815) B8031815
theorem B11883611 : Blo 1853628 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B2782319 : Blo 1853628 2782319 := bstep (se 1 (by rfl) ⟨2086739, by rfl⟩ : syracuseStep 2782319 = 4173479) B4173479
theorem B7919059 : Blo 1853628 7919059 := bstep (se 1 (by rfl) ⟨5939294, by rfl⟩ : syracuseStep 7919059 = 11878589) B11878589
theorem B38049425 : Blo 1853628 38049425 := bstep (se 2 (by rfl) ⟨14268534, by rfl⟩ : syracuseStep 38049425 = 28537069) B28537069
theorem B2783087 : Blo 1853628 2783087 := bstep (se 1 (by rfl) ⟨2087315, by rfl⟩ : syracuseStep 2783087 = 4174631) B4174631
theorem B2783099 : Blo 1853628 2783099 := bstep (se 1 (by rfl) ⟨2087324, by rfl⟩ : syracuseStep 2783099 = 4174649) B4174649
theorem B2783339 : Blo 1853628 2783339 := bstep (se 1 (by rfl) ⟨2087504, by rfl⟩ : syracuseStep 2783339 = 4175009) B4175009
theorem B6256763 : Blo 1853628 6256763 := bstep (se 1 (by rfl) ⟨4692572, by rfl⟩ : syracuseStep 6256763 = 9385145) B9385145
theorem B7043219 : Blo 1853628 7043219 := bstep (se 1 (by rfl) ⟨5282414, by rfl⟩ : syracuseStep 7043219 = 10564829) B10564829
theorem B3758363 : Blo 1853628 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B22559087 : Blo 1853628 22559087 := bstep (se 1 (by rfl) ⟨16919315, by rfl⟩ : syracuseStep 22559087 = 33838631) B33838631
theorem B1981183 : Blo 1853628 1981183 := bstep (se 1 (by rfl) ⟨1485887, by rfl⟩ : syracuseStep 1981183 = 2971775) B2971775
theorem B11279225 : Blo 1853628 11279225 := bstep (se 2 (by rfl) ⟨4229709, by rfl⟩ : syracuseStep 11279225 = 8459419) B8459419
theorem B6257627 : Blo 1853628 6257627 := bstep (se 1 (by rfl) ⟨4693220, by rfl⟩ : syracuseStep 6257627 = 9386441) B9386441
theorem B9387251 : Blo 1853628 9387251 := bstep (se 1 (by rfl) ⟨7040438, by rfl⟩ : syracuseStep 9387251 = 14080877) B14080877
theorem B15244607 : Blo 1853628 15244607 := bstep (se 1 (by rfl) ⟨11433455, by rfl⟩ : syracuseStep 15244607 = 22866911) B22866911
theorem B15850829 : Blo 1853628 15850829 := bstep (se 3 (by rfl) ⟨2972030, by rfl⟩ : syracuseStep 15850829 = 5944061) B5944061
theorem B16924099 : Blo 1853628 16924099 := bstep (se 1 (by rfl) ⟨12693074, by rfl⟩ : syracuseStep 16924099 = 25386149) B25386149
theorem B4456009 : Blo 1853628 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B3128969 : Blo 1853628 3128969 := bstep (se 2 (by rfl) ⟨1173363, by rfl⟩ : syracuseStep 3128969 = 2346727) B2346727
theorem B5938859 : Blo 1853628 5938859 := bstep (se 1 (by rfl) ⟨4454144, by rfl⟩ : syracuseStep 5938859 = 8908289) B8908289
theorem B15236795 : Blo 1853628 15236795 := bstep (se 1 (by rfl) ⟨11427596, by rfl⟩ : syracuseStep 15236795 = 22855193) B22855193
theorem B57868157 : Blo 1853628 57868157 := bstep (se 3 (by rfl) ⟨10850279, by rfl⟩ : syracuseStep 57868157 = 21700559) B21700559
theorem B14278781 : Blo 1853628 14278781 := bstep (se 3 (by rfl) ⟨2677271, by rfl⟩ : syracuseStep 14278781 = 5354543) B5354543
theorem B53494019 : Blo 1853628 53494019 := bstep (se 1 (by rfl) ⟨40120514, by rfl⟩ : syracuseStep 53494019 = 80241029) B80241029
theorem B10027361 : Blo 1853628 10027361 := bstep (se 2 (by rfl) ⟨3760260, by rfl⟩ : syracuseStep 10027361 = 7520521) B7520521
theorem B3130751 : Blo 1853628 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B4171175 : Blo 1853628 4171175 := bstep (se 1 (by rfl) ⟨3128381, by rfl⟩ : syracuseStep 4171175 = 6256763) B6256763
theorem B4695479 : Blo 1853628 4695479 := bstep (se 1 (by rfl) ⟨3521609, by rfl⟩ : syracuseStep 4695479 = 7043219) B7043219
theorem B10585673 : Blo 1853628 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B9520831 : Blo 1853628 9520831 := bstep (se 1 (by rfl) ⟨7140623, by rfl⟩ : syracuseStep 9520831 = 14281247) B14281247
theorem B15836957 : Blo 1853628 15836957 := bstep (se 3 (by rfl) ⟨2969429, by rfl⟩ : syracuseStep 15836957 = 5938859) B5938859
theorem B6260543 : Blo 1853628 6260543 := bstep (se 1 (by rfl) ⟨4695407, by rfl⟩ : syracuseStep 6260543 = 9390815) B9390815
theorem B3131291 : Blo 1853628 3131291 := bstep (se 1 (by rfl) ⟨2348468, by rfl⟩ : syracuseStep 3131291 = 4696937) B4696937
theorem B4171751 : Blo 1853628 4171751 := bstep (se 1 (by rfl) ⟨3128813, by rfl⟩ : syracuseStep 4171751 = 6257627) B6257627
theorem B5941345 : Blo 1853628 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B1853695 : Blo 1853628 1853695 := bstep (se 1 (by rfl) ⟨1390271, by rfl⟩ : syracuseStep 1853695 = 2780543) B2780543
theorem B9390491 : Blo 1853628 9390491 := bstep (se 1 (by rfl) ⟨7042868, by rfl⟩ : syracuseStep 9390491 = 14085737) B14085737
theorem B38578771 : Blo 1853628 38578771 := bstep (se 1 (by rfl) ⟨28934078, by rfl⟩ : syracuseStep 38578771 = 57868157) B57868157
theorem B7039649 : Blo 1853628 7039649 := bstep (se 2 (by rfl) ⟨2639868, by rfl⟩ : syracuseStep 7039649 = 5279737) B5279737
theorem B4172507 : Blo 1853628 4172507 := bstep (se 1 (by rfl) ⟨3129380, by rfl⟩ : syracuseStep 4172507 = 6258761) B6258761
theorem B4172543 : Blo 1853628 4172543 := bstep (se 1 (by rfl) ⟨3129407, by rfl⟩ : syracuseStep 4172543 = 6258815) B6258815
theorem B1854279 : Blo 1853628 1854279 := bstep (se 1 (by rfl) ⟨1390709, by rfl⟩ : syracuseStep 1854279 = 2781419) B2781419
theorem B1854319 : Blo 1853628 1854319 := bstep (se 1 (by rfl) ⟨1390739, by rfl⟩ : syracuseStep 1854319 = 2781479) B2781479
theorem B31689629 : Blo 1853628 31689629 := bstep (se 3 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 31689629 = 11883611) B11883611
theorem B5278895 : Blo 1853628 5278895 := bstep (se 1 (by rfl) ⟨3959171, by rfl⟩ : syracuseStep 5278895 = 7918343) B7918343
theorem B770608313 : Blo 1853628 770608313 := bstep (se 2 (by rfl) ⟨288978117, by rfl⟩ : syracuseStep 770608313 = 577956235) B577956235
theorem B1854671 : Blo 1853628 1854671 := bstep (se 1 (by rfl) ⟨1391003, by rfl⟩ : syracuseStep 1854671 = 2782007) B2782007
theorem B1854747 : Blo 1853628 1854747 := bstep (se 1 (by rfl) ⟨1391060, by rfl⟩ : syracuseStep 1854747 = 2782121) B2782121
theorem B10562845 : Blo 1853628 10562845 := bstep (se 3 (by rfl) ⟨1980533, by rfl⟩ : syracuseStep 10562845 = 3961067) B3961067
theorem B7040303 : Blo 1853628 7040303 := bstep (se 1 (by rfl) ⟨5280227, by rfl⟩ : syracuseStep 7040303 = 10560455) B10560455
theorem B6343991 : Blo 1853628 6343991 := bstep (se 1 (by rfl) ⟨4757993, by rfl⟩ : syracuseStep 6343991 = 9515987) B9515987
theorem B1854791 : Blo 1853628 1854791 := bstep (se 1 (by rfl) ⟨1391093, by rfl⟩ : syracuseStep 1854791 = 2782187) B2782187
theorem B1854879 : Blo 1853628 1854879 := bstep (se 1 (by rfl) ⟨1391159, by rfl⟩ : syracuseStep 1854879 = 2782319) B2782319
theorem B21130793 : Blo 1853628 21130793 := bstep (se 2 (by rfl) ⟨7924047, by rfl⟩ : syracuseStep 21130793 = 15848095) B15848095
theorem B7040591 : Blo 1853628 7040591 := bstep (se 1 (by rfl) ⟨5280443, by rfl⟩ : syracuseStep 7040591 = 10560887) B10560887
theorem B2641577 : Blo 1853628 2641577 := bstep (se 2 (by rfl) ⟨990591, by rfl⟩ : syracuseStep 2641577 = 1981183) B1981183
theorem B2780879 : Blo 1853628 2780879 := bstep (se 1 (by rfl) ⟨2085659, by rfl⟩ : syracuseStep 2780879 = 4171319) B4171319
theorem B25366283 : Blo 1853628 25366283 := bstep (se 1 (by rfl) ⟨19024712, by rfl⟩ : syracuseStep 25366283 = 38049425) B38049425
theorem B1855391 : Blo 1853628 1855391 := bstep (se 1 (by rfl) ⟨1391543, by rfl⟩ : syracuseStep 1855391 = 2783087) B2783087
theorem B1855399 : Blo 1853628 1855399 := bstep (se 1 (by rfl) ⟨1391549, by rfl⟩ : syracuseStep 1855399 = 2783099) B2783099
theorem B2781119 : Blo 1853628 2781119 := bstep (se 1 (by rfl) ⟨2085839, by rfl⟩ : syracuseStep 2781119 = 4171679) B4171679
theorem B4173767 : Blo 1853628 4173767 := bstep (se 1 (by rfl) ⟨3130325, by rfl⟩ : syracuseStep 4173767 = 6260651) B6260651
theorem B1855559 : Blo 1853628 1855559 := bstep (se 1 (by rfl) ⟨1391669, by rfl⟩ : syracuseStep 1855559 = 2783339) B2783339
theorem B2781287 : Blo 1853628 2781287 := bstep (se 1 (by rfl) ⟨2085965, by rfl⟩ : syracuseStep 2781287 = 4171931) B4171931
theorem B12693671 : Blo 1853628 12693671 := bstep (se 1 (by rfl) ⟨9520253, by rfl⟩ : syracuseStep 12693671 = 19040507) B19040507
theorem B2781743 : Blo 1853628 2781743 := bstep (se 1 (by rfl) ⟨2086307, by rfl⟩ : syracuseStep 2781743 = 4172615) B4172615
theorem B22565465 : Blo 1853628 22565465 := bstep (se 2 (by rfl) ⟨8462049, by rfl⟩ : syracuseStep 22565465 = 16924099) B16924099
theorem B202928813 : Blo 1853628 202928813 := bstep (se 3 (by rfl) ⟨38049152, by rfl⟩ : syracuseStep 202928813 = 76098305) B76098305
theorem B14275453 : Blo 1853628 14275453 := bstep (se 3 (by rfl) ⟨2676647, by rfl⟩ : syracuseStep 14275453 = 5353295) B5353295
theorem B10163071 : Blo 1853628 10163071 := bstep (se 1 (by rfl) ⟨7622303, by rfl⟩ : syracuseStep 10163071 = 15244607) B15244607
theorem B2782151 : Blo 1853628 2782151 := bstep (se 1 (by rfl) ⟨2086613, by rfl⟩ : syracuseStep 2782151 = 4173227) B4173227
theorem B10564577 : Blo 1853628 10564577 := bstep (se 2 (by rfl) ⟨3961716, by rfl⟩ : syracuseStep 10564577 = 7923433) B7923433
theorem B2085979 : Blo 1853628 2085979 := bstep (se 1 (by rfl) ⟨1564484, by rfl⟩ : syracuseStep 2085979 = 3128969) B3128969
theorem B6346619 : Blo 1853628 6346619 := bstep (se 1 (by rfl) ⟨4759964, by rfl⟩ : syracuseStep 6346619 = 9519929) B9519929
theorem B20060135 : Blo 1853628 20060135 := bstep (se 1 (by rfl) ⟨15045101, by rfl⟩ : syracuseStep 20060135 = 30090203) B30090203
theorem B8575463 : Blo 1853628 8575463 := bstep (se 1 (by rfl) ⟨6431597, by rfl⟩ : syracuseStep 8575463 = 12863195) B12863195
theorem B2505575 : Blo 1853628 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B15039391 : Blo 1853628 15039391 := bstep (se 1 (by rfl) ⟨11279543, by rfl⟩ : syracuseStep 15039391 = 22559087) B22559087
theorem B5282779 : Blo 1853628 5282779 := bstep (se 1 (by rfl) ⟨3962084, by rfl⟩ : syracuseStep 5282779 = 7924169) B7924169
theorem B60185693 : Blo 1853628 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B40631453 : Blo 1853628 40631453 := bstep (se 3 (by rfl) ⟨7618397, by rfl⟩ : syracuseStep 40631453 = 15236795) B15236795
theorem B195337439 : Blo 1853628 195337439 := bstep (se 1 (by rfl) ⟨146503079, by rfl⟩ : syracuseStep 195337439 = 293006159) B293006159
theorem B7519483 : Blo 1853628 7519483 := bstep (se 1 (by rfl) ⟨5639612, by rfl⟩ : syracuseStep 7519483 = 11279225) B11279225
theorem B10558745 : Blo 1853628 10558745 := bstep (se 2 (by rfl) ⟨3959529, by rfl⟩ : syracuseStep 10558745 = 7919059) B7919059
theorem B6258167 : Blo 1853628 6258167 := bstep (se 1 (by rfl) ⟨4693625, by rfl⟩ : syracuseStep 6258167 = 9387251) B9387251
theorem B10567219 : Blo 1853628 10567219 := bstep (se 1 (by rfl) ⟨7925414, by rfl⟩ : syracuseStep 10567219 = 15850829) B15850829
theorem B6774329 : Blo 1853628 6774329 := bstep (se 2 (by rfl) ⟨2540373, by rfl⟩ : syracuseStep 6774329 = 5080747) B5080747
theorem B25386689 : Blo 1853628 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B5939027 : Blo 1853628 5939027 := bstep (se 1 (by rfl) ⟨4454270, by rfl⟩ : syracuseStep 5939027 = 8908541) B8908541
theorem B8462447 : Blo 1853628 8462447 := bstep (se 1 (by rfl) ⟨6346835, by rfl⟩ : syracuseStep 8462447 = 12693671) B12693671
theorem B7921793 : Blo 1853628 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B38076749 : Blo 1853628 38076749 := bstep (se 3 (by rfl) ⟨7139390, by rfl⟩ : syracuseStep 38076749 = 14278781) B14278781
theorem B51438361 : Blo 1853628 51438361 := bstep (se 2 (by rfl) ⟨19289385, by rfl⟩ : syracuseStep 51438361 = 38578771) B38578771
theorem B26739629 : Blo 1853628 26739629 := bstep (se 3 (by rfl) ⟨5013680, by rfl⟩ : syracuseStep 26739629 = 10027361) B10027361
theorem B3130319 : Blo 1853628 3130319 := bstep (se 1 (by rfl) ⟨2347739, by rfl⟩ : syracuseStep 3130319 = 4695479) B4695479
theorem B13550761 : Blo 1853628 13550761 := bstep (se 2 (by rfl) ⟨5081535, by rfl⟩ : syracuseStep 13550761 = 10163071) B10163071
theorem B6260327 : Blo 1853628 6260327 := bstep (se 1 (by rfl) ⟨4695245, by rfl⟩ : syracuseStep 6260327 = 9390491) B9390491
theorem B14083793 : Blo 1853628 14083793 := bstep (se 2 (by rfl) ⟨5281422, by rfl⟩ : syracuseStep 14083793 = 10562845) B10562845
theorem B513738875 : Blo 1853628 513738875 := bstep (se 1 (by rfl) ⟨385304156, by rfl⟩ : syracuseStep 513738875 = 770608313) B770608313
theorem B7039163 : Blo 1853628 7039163 := bstep (se 1 (by rfl) ⟨5279372, by rfl⟩ : syracuseStep 7039163 = 10558745) B10558745
theorem B4229327 : Blo 1853628 4229327 := bstep (se 1 (by rfl) ⟨3171995, by rfl⟩ : syracuseStep 4229327 = 6343991) B6343991
theorem B4172111 : Blo 1853628 4172111 := bstep (se 1 (by rfl) ⟨3129083, by rfl⟩ : syracuseStep 4172111 = 6258167) B6258167
theorem B4516219 : Blo 1853628 4516219 := bstep (se 1 (by rfl) ⟨3387164, by rfl⟩ : syracuseStep 4516219 = 6774329) B6774329
theorem B1853919 : Blo 1853628 1853919 := bstep (se 1 (by rfl) ⟨1390439, by rfl⟩ : syracuseStep 1853919 = 2780879) B2780879
theorem B16910855 : Blo 1853628 16910855 := bstep (se 1 (by rfl) ⟨12683141, by rfl⟩ : syracuseStep 16910855 = 25366283) B25366283
theorem B3959351 : Blo 1853628 3959351 := bstep (se 1 (by rfl) ⟨2969513, by rfl⟩ : syracuseStep 3959351 = 5939027) B5939027
theorem B1854079 : Blo 1853628 1854079 := bstep (se 1 (by rfl) ⟨1390559, by rfl⟩ : syracuseStep 1854079 = 2781119) B2781119
theorem B1854191 : Blo 1853628 1854191 := bstep (se 1 (by rfl) ⟨1390643, by rfl⟩ : syracuseStep 1854191 = 2781287) B2781287
theorem B35662679 : Blo 1853628 35662679 := bstep (se 1 (by rfl) ⟨26747009, by rfl⟩ : syracuseStep 35662679 = 53494019) B53494019
theorem B1854495 : Blo 1853628 1854495 := bstep (se 1 (by rfl) ⟨1390871, by rfl⟩ : syracuseStep 1854495 = 2781743) B2781743
theorem B15043643 : Blo 1853628 15043643 := bstep (se 1 (by rfl) ⟨11282732, by rfl⟩ : syracuseStep 15043643 = 22565465) B22565465
theorem B135285875 : Blo 1853628 135285875 := bstep (se 1 (by rfl) ⟨101464406, by rfl⟩ : syracuseStep 135285875 = 202928813) B202928813
theorem B1854767 : Blo 1853628 1854767 := bstep (se 1 (by rfl) ⟨1391075, by rfl⟩ : syracuseStep 1854767 = 2782151) B2782151
theorem B2780783 : Blo 1853628 2780783 := bstep (se 1 (by rfl) ⟨2085587, by rfl⟩ : syracuseStep 2780783 = 4171175) B4171175
theorem B50777765 : Blo 1853628 50777765 := bstep (se 4 (by rfl) ⟨4760415, by rfl⟩ : syracuseStep 50777765 = 9520831) B9520831
theorem B7057115 : Blo 1853628 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B19033937 : Blo 1853628 19033937 := bstep (se 2 (by rfl) ⟨7137726, by rfl⟩ : syracuseStep 19033937 = 14275453) B14275453
theorem B4173695 : Blo 1853628 4173695 := bstep (se 1 (by rfl) ⟨3130271, by rfl⟩ : syracuseStep 4173695 = 6260543) B6260543
theorem B4231079 : Blo 1853628 4231079 := bstep (se 1 (by rfl) ⟨3173309, by rfl⟩ : syracuseStep 4231079 = 6346619) B6346619
theorem B40103909 : Blo 1853628 40103909 := bstep (se 4 (by rfl) ⟨3759741, by rfl⟩ : syracuseStep 40103909 = 7519483) B7519483
theorem B2781167 : Blo 1853628 2781167 := bstep (se 1 (by rfl) ⟨2085875, by rfl⟩ : syracuseStep 2781167 = 4171751) B4171751
theorem B13373423 : Blo 1853628 13373423 := bstep (se 1 (by rfl) ⟨10030067, by rfl⟩ : syracuseStep 13373423 = 20060135) B20060135
theorem B2781305 : Blo 1853628 2781305 := bstep (se 2 (by rfl) ⟨1042989, by rfl⟩ : syracuseStep 2781305 = 2085979) B2085979
theorem B2781671 : Blo 1853628 2781671 := bstep (se 1 (by rfl) ⟨2086253, by rfl⟩ : syracuseStep 2781671 = 4172507) B4172507
theorem B2781695 : Blo 1853628 2781695 := bstep (se 1 (by rfl) ⟨2086271, by rfl⟩ : syracuseStep 2781695 = 4172543) B4172543
theorem B27087635 : Blo 1853628 27087635 := bstep (se 1 (by rfl) ⟨20315726, by rfl⟩ : syracuseStep 27087635 = 40631453) B40631453
theorem B3519263 : Blo 1853628 3519263 := bstep (se 1 (by rfl) ⟨2639447, by rfl⟩ : syracuseStep 3519263 = 5278895) B5278895
theorem B130224959 : Blo 1853628 130224959 := bstep (se 1 (by rfl) ⟨97668719, by rfl⟩ : syracuseStep 130224959 = 195337439) B195337439
theorem B6681533 : Blo 1853628 6681533 := bstep (se 3 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 6681533 = 2505575) B2505575
theorem B14087195 : Blo 1853628 14087195 := bstep (se 1 (by rfl) ⟨10565396, by rfl⟩ : syracuseStep 14087195 = 21130793) B21130793
theorem B2782511 : Blo 1853628 2782511 := bstep (se 1 (by rfl) ⟨2086883, by rfl⟩ : syracuseStep 2782511 = 4173767) B4173767
theorem B160495181 : Blo 1853628 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B7043051 : Blo 1853628 7043051 := bstep (se 1 (by rfl) ⟨5282288, by rfl⟩ : syracuseStep 7043051 = 10564577) B10564577
theorem B2087167 : Blo 1853628 2087167 := bstep (se 1 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 2087167 = 3130751) B3130751
theorem B10557971 : Blo 1853628 10557971 := bstep (se 1 (by rfl) ⟨7918478, by rfl⟩ : syracuseStep 10557971 = 15836957) B15836957
theorem B20052521 : Blo 1853628 20052521 := bstep (se 2 (by rfl) ⟨7519695, by rfl⟩ : syracuseStep 20052521 = 15039391) B15039391
theorem B2087527 : Blo 1853628 2087527 := bstep (se 1 (by rfl) ⟨1565645, by rfl⟩ : syracuseStep 2087527 = 3131291) B3131291
theorem B7043705 : Blo 1853628 7043705 := bstep (se 2 (by rfl) ⟨2641389, by rfl⟩ : syracuseStep 7043705 = 5282779) B5282779
theorem B5716975 : Blo 1853628 5716975 := bstep (se 1 (by rfl) ⟨4287731, by rfl⟩ : syracuseStep 5716975 = 8575463) B8575463
theorem B4693099 : Blo 1853628 4693099 := bstep (se 1 (by rfl) ⟨3519824, by rfl⟩ : syracuseStep 4693099 = 7039649) B7039649
theorem B7044205 : Blo 1853628 7044205 := bstep (se 3 (by rfl) ⟨1320788, by rfl⟩ : syracuseStep 7044205 = 2641577) B2641577
theorem B21126419 : Blo 1853628 21126419 := bstep (se 1 (by rfl) ⟨15844814, by rfl⟩ : syracuseStep 21126419 = 31689629) B31689629
theorem B14089625 : Blo 1853628 14089625 := bstep (se 2 (by rfl) ⟨5283609, by rfl⟩ : syracuseStep 14089625 = 10567219) B10567219
theorem B4693535 : Blo 1853628 4693535 := bstep (se 1 (by rfl) ⟨3520151, by rfl⟩ : syracuseStep 4693535 = 7040303) B7040303
theorem B4693727 : Blo 1853628 4693727 := bstep (se 1 (by rfl) ⟨3520295, by rfl⟩ : syracuseStep 4693727 = 7040591) B7040591
theorem B16924459 : Blo 1853628 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B17826419 : Blo 1853628 17826419 := bstep (se 1 (by rfl) ⟨13369814, by rfl⟩ : syracuseStep 17826419 = 26739629) B26739629
theorem B68584481 : Blo 1853628 68584481 := bstep (se 2 (by rfl) ⟨25719180, by rfl⟩ : syracuseStep 68584481 = 51438361) B51438361
theorem B106996787 : Blo 1853628 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B9389195 : Blo 1853628 9389195 := bstep (se 1 (by rfl) ⟨7041896, by rfl⟩ : syracuseStep 9389195 = 14083793) B14083793
theorem B4695367 : Blo 1853628 4695367 := bstep (se 1 (by rfl) ⟨3521525, by rfl⟩ : syracuseStep 4695367 = 7043051) B7043051
theorem B342492583 : Blo 1853628 342492583 := bstep (se 1 (by rfl) ⟨256869437, by rfl⟩ : syracuseStep 342492583 = 513738875) B513738875
theorem B2819551 : Blo 1853628 2819551 := bstep (se 1 (by rfl) ⟨2114663, by rfl⟩ : syracuseStep 2819551 = 4229327) B4229327
theorem B11273903 : Blo 1853628 11273903 := bstep (se 1 (by rfl) ⟨8455427, by rfl⟩ : syracuseStep 11273903 = 16910855) B16910855
theorem B7038647 : Blo 1853628 7038647 := bstep (se 1 (by rfl) ⟨5278985, by rfl⟩ : syracuseStep 7038647 = 10557971) B10557971
theorem B2639567 : Blo 1853628 2639567 := bstep (se 1 (by rfl) ⟨1979675, by rfl⟩ : syracuseStep 2639567 = 3959351) B3959351
theorem B4695803 : Blo 1853628 4695803 := bstep (se 1 (by rfl) ⟨3521852, by rfl⟩ : syracuseStep 4695803 = 7043705) B7043705
theorem B23775119 : Blo 1853628 23775119 := bstep (se 1 (by rfl) ⟨17831339, by rfl⟩ : syracuseStep 23775119 = 35662679) B35662679
theorem B24086501 : Blo 1853628 24086501 := bstep (se 4 (by rfl) ⟨2258109, by rfl⟩ : syracuseStep 24086501 = 4516219) B4516219
theorem B10029095 : Blo 1853628 10029095 := bstep (se 1 (by rfl) ⟨7521821, by rfl⟩ : syracuseStep 10029095 = 15043643) B15043643
theorem B14084279 : Blo 1853628 14084279 := bstep (se 1 (by rfl) ⟨10563209, by rfl⟩ : syracuseStep 14084279 = 21126419) B21126419
theorem B1853855 : Blo 1853628 1853855 := bstep (se 1 (by rfl) ⟨1390391, by rfl⟩ : syracuseStep 1853855 = 2780783) B2780783
theorem B33851843 : Blo 1853628 33851843 := bstep (se 1 (by rfl) ⟨25388882, by rfl⟩ : syracuseStep 33851843 = 50777765) B50777765
theorem B4704743 : Blo 1853628 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B2820719 : Blo 1853628 2820719 := bstep (se 1 (by rfl) ⟨2115539, by rfl⟩ : syracuseStep 2820719 = 4231079) B4231079
theorem B1854111 : Blo 1853628 1854111 := bstep (se 1 (by rfl) ⟨1390583, by rfl⟩ : syracuseStep 1854111 = 2781167) B2781167
theorem B8915615 : Blo 1853628 8915615 := bstep (se 1 (by rfl) ⟨6686711, by rfl⟩ : syracuseStep 8915615 = 13373423) B13373423
theorem B1854203 : Blo 1853628 1854203 := bstep (se 1 (by rfl) ⟨1390652, by rfl⟩ : syracuseStep 1854203 = 2781305) B2781305
theorem B1854447 : Blo 1853628 1854447 := bstep (se 1 (by rfl) ⟨1390835, by rfl⟩ : syracuseStep 1854447 = 2781671) B2781671
theorem B1854463 : Blo 1853628 1854463 := bstep (se 1 (by rfl) ⟨1390847, by rfl⟩ : syracuseStep 1854463 = 2781695) B2781695
theorem B2346175 : Blo 1853628 2346175 := bstep (se 1 (by rfl) ⟨1759631, by rfl⟩ : syracuseStep 2346175 = 3519263) B3519263
theorem B9391463 : Blo 1853628 9391463 := bstep (se 1 (by rfl) ⟨7043597, by rfl⟩ : syracuseStep 9391463 = 14087195) B14087195
theorem B1855007 : Blo 1853628 1855007 := bstep (se 1 (by rfl) ⟨1391255, by rfl⟩ : syracuseStep 1855007 = 2782511) B2782511
theorem B4173551 : Blo 1853628 4173551 := bstep (se 1 (by rfl) ⟨3130163, by rfl⟩ : syracuseStep 4173551 = 6260327) B6260327
theorem B7622633 : Blo 1853628 7622633 := bstep (se 2 (by rfl) ⟨2858487, by rfl⟩ : syracuseStep 7622633 = 5716975) B5716975
theorem B9392273 : Blo 1853628 9392273 := bstep (se 2 (by rfl) ⟨3522102, by rfl⟩ : syracuseStep 9392273 = 7044205) B7044205
theorem B2781407 : Blo 1853628 2781407 := bstep (se 1 (by rfl) ⟨2086055, by rfl⟩ : syracuseStep 2781407 = 4172111) B4172111
theorem B18067681 : Blo 1853628 18067681 := bstep (se 2 (by rfl) ⟨6775380, by rfl⟩ : syracuseStep 18067681 = 13550761) B13550761
theorem B72233693 : Blo 1853628 72233693 := bstep (se 3 (by rfl) ⟨13543817, by rfl⟩ : syracuseStep 72233693 = 27087635) B27087635
theorem B90190583 : Blo 1853628 90190583 := bstep (se 1 (by rfl) ⟨67642937, by rfl⟩ : syracuseStep 90190583 = 135285875) B135285875
theorem B9393083 : Blo 1853628 9393083 := bstep (se 1 (by rfl) ⟨7044812, by rfl⟩ : syracuseStep 9393083 = 14089625) B14089625
theorem B22565945 : Blo 1853628 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B2782463 : Blo 1853628 2782463 := bstep (se 1 (by rfl) ⟨2086847, by rfl⟩ : syracuseStep 2782463 = 4173695) B4173695
theorem B26735939 : Blo 1853628 26735939 := bstep (se 1 (by rfl) ⟨20051954, by rfl⟩ : syracuseStep 26735939 = 40103909) B40103909
theorem B5641631 : Blo 1853628 5641631 := bstep (se 1 (by rfl) ⟨4231223, by rfl⟩ : syracuseStep 5641631 = 8462447) B8462447
theorem B5281195 : Blo 1853628 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B25384499 : Blo 1853628 25384499 := bstep (se 1 (by rfl) ⟨19038374, by rfl⟩ : syracuseStep 25384499 = 38076749) B38076749
theorem B2782889 : Blo 1853628 2782889 := bstep (se 2 (by rfl) ⟨1043583, by rfl⟩ : syracuseStep 2782889 = 2087167) B2087167
theorem B86816639 : Blo 1853628 86816639 := bstep (se 1 (by rfl) ⟨65112479, by rfl⟩ : syracuseStep 86816639 = 130224959) B130224959
theorem B2086879 : Blo 1853628 2086879 := bstep (se 1 (by rfl) ⟨1565159, by rfl⟩ : syracuseStep 2086879 = 3130319) B3130319
theorem B2783369 : Blo 1853628 2783369 := bstep (se 2 (by rfl) ⟨1043763, by rfl⟩ : syracuseStep 2783369 = 2087527) B2087527
theorem B4692775 : Blo 1853628 4692775 := bstep (se 1 (by rfl) ⟨3519581, by rfl⟩ : syracuseStep 4692775 = 7039163) B7039163
theorem B6257465 : Blo 1853628 6257465 := bstep (se 2 (by rfl) ⟨2346549, by rfl⟩ : syracuseStep 6257465 = 4693099) B4693099
theorem B13368347 : Blo 1853628 13368347 := bstep (se 1 (by rfl) ⟨10026260, by rfl⟩ : syracuseStep 13368347 = 20052521) B20052521
theorem B3129023 : Blo 1853628 3129023 := bstep (se 1 (by rfl) ⟨2346767, by rfl⟩ : syracuseStep 3129023 = 4693535) B4693535
theorem B3129151 : Blo 1853628 3129151 := bstep (se 1 (by rfl) ⟨2346863, by rfl⟩ : syracuseStep 3129151 = 4693727) B4693727
theorem B17817421 : Blo 1853628 17817421 := bstep (se 3 (by rfl) ⟨3340766, by rfl⟩ : syracuseStep 17817421 = 6681533) B6681533
theorem B12689291 : Blo 1853628 12689291 := bstep (se 1 (by rfl) ⟨9516968, by rfl⟩ : syracuseStep 12689291 = 19033937) B19033937
theorem B6259463 : Blo 1853628 6259463 := bstep (se 1 (by rfl) ⟨4694597, by rfl⟩ : syracuseStep 6259463 = 9389195) B9389195
theorem B3761087 : Blo 1853628 3761087 := bstep (se 1 (by rfl) ⟨2820815, by rfl⟩ : syracuseStep 3761087 = 5641631) B5641631
theorem B3130535 : Blo 1853628 3130535 := bstep (se 1 (by rfl) ⟨2347901, by rfl⟩ : syracuseStep 3130535 = 4695803) B4695803
theorem B57877759 : Blo 1853628 57877759 := bstep (se 1 (by rfl) ⟨43408319, by rfl⟩ : syracuseStep 57877759 = 86816639) B86816639
theorem B16057667 : Blo 1853628 16057667 := bstep (se 1 (by rfl) ⟨12043250, by rfl⟩ : syracuseStep 16057667 = 24086501) B24086501
theorem B6686063 : Blo 1853628 6686063 := bstep (se 1 (by rfl) ⟨5014547, by rfl⟩ : syracuseStep 6686063 = 10029095) B10029095
theorem B9389519 : Blo 1853628 9389519 := bstep (se 1 (by rfl) ⟨7042139, by rfl⟩ : syracuseStep 9389519 = 14084279) B14084279
theorem B6260489 : Blo 1853628 6260489 := bstep (se 2 (by rfl) ⟨2347683, by rfl⟩ : syracuseStep 6260489 = 4695367) B4695367
theorem B4171643 : Blo 1853628 4171643 := bstep (se 1 (by rfl) ⟨3128732, by rfl⟩ : syracuseStep 4171643 = 6257465) B6257465
theorem B7038845 : Blo 1853628 7038845 := bstep (se 3 (by rfl) ⟨1319783, by rfl⟩ : syracuseStep 7038845 = 2639567) B2639567
theorem B456656777 : Blo 1853628 456656777 := bstep (se 2 (by rfl) ⟨171246291, by rfl⟩ : syracuseStep 456656777 = 342492583) B342492583
theorem B6260975 : Blo 1853628 6260975 := bstep (se 1 (by rfl) ⟨4695731, by rfl⟩ : syracuseStep 6260975 = 9391463) B9391463
theorem B4172201 : Blo 1853628 4172201 := bstep (se 2 (by rfl) ⟨1564575, by rfl⟩ : syracuseStep 4172201 = 3129151) B3129151
theorem B20327021 : Blo 1853628 20327021 := bstep (se 3 (by rfl) ⟨3811316, by rfl⟩ : syracuseStep 20327021 = 7622633) B7622633
theorem B6261515 : Blo 1853628 6261515 := bstep (se 1 (by rfl) ⟨4696136, by rfl⟩ : syracuseStep 6261515 = 9392273) B9392273
theorem B1854271 : Blo 1853628 1854271 := bstep (se 1 (by rfl) ⟨1390703, by rfl⟩ : syracuseStep 1854271 = 2781407) B2781407
theorem B48155795 : Blo 1853628 48155795 := bstep (se 1 (by rfl) ⟨36116846, by rfl⟩ : syracuseStep 48155795 = 72233693) B72233693
theorem B6262055 : Blo 1853628 6262055 := bstep (se 1 (by rfl) ⟨4696541, by rfl⟩ : syracuseStep 6262055 = 9393083) B9393083
theorem B45722987 : Blo 1853628 45722987 := bstep (se 1 (by rfl) ⟨34292240, by rfl⟩ : syracuseStep 45722987 = 68584481) B68584481
theorem B15043963 : Blo 1853628 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B71331191 : Blo 1853628 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B1854975 : Blo 1853628 1854975 := bstep (se 1 (by rfl) ⟨1391231, by rfl⟩ : syracuseStep 1854975 = 2782463) B2782463
theorem B1855259 : Blo 1853628 1855259 := bstep (se 1 (by rfl) ⟨1391444, by rfl⟩ : syracuseStep 1855259 = 2782889) B2782889
theorem B7515935 : Blo 1853628 7515935 := bstep (se 1 (by rfl) ⟨5636951, by rfl⟩ : syracuseStep 7515935 = 11273903) B11273903
theorem B1855579 : Blo 1853628 1855579 := bstep (se 1 (by rfl) ⟨1391684, by rfl⟩ : syracuseStep 1855579 = 2783369) B2783369
theorem B1880479 : Blo 1853628 1880479 := bstep (se 1 (by rfl) ⟨1410359, by rfl⟩ : syracuseStep 1880479 = 2820719) B2820719
theorem B5943743 : Blo 1853628 5943743 := bstep (se 1 (by rfl) ⟨4457807, by rfl⟩ : syracuseStep 5943743 = 8915615) B8915615
theorem B7041593 : Blo 1853628 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B2086015 : Blo 1853628 2086015 := bstep (se 1 (by rfl) ⟨1564511, by rfl⟩ : syracuseStep 2086015 = 3129023) B3129023
theorem B2782367 : Blo 1853628 2782367 := bstep (se 1 (by rfl) ⟨2086775, by rfl⟩ : syracuseStep 2782367 = 4173551) B4173551
theorem B8459527 : Blo 1853628 8459527 := bstep (se 1 (by rfl) ⟨6344645, by rfl⟩ : syracuseStep 8459527 = 12689291) B12689291
theorem B2782505 : Blo 1853628 2782505 := bstep (se 2 (by rfl) ⟨1043439, by rfl⟩ : syracuseStep 2782505 = 2086879) B2086879
theorem B24090241 : Blo 1853628 24090241 := bstep (se 2 (by rfl) ⟨9033840, by rfl⟩ : syracuseStep 24090241 = 18067681) B18067681
theorem B11884279 : Blo 1853628 11884279 := bstep (se 1 (by rfl) ⟨8913209, by rfl⟩ : syracuseStep 11884279 = 17826419) B17826419
theorem B60127055 : Blo 1853628 60127055 := bstep (se 1 (by rfl) ⟨45095291, by rfl⟩ : syracuseStep 60127055 = 90190583) B90190583
theorem B17823959 : Blo 1853628 17823959 := bstep (se 1 (by rfl) ⟨13367969, by rfl⟩ : syracuseStep 17823959 = 26735939) B26735939
theorem B16922999 : Blo 1853628 16922999 := bstep (se 1 (by rfl) ⟨12692249, by rfl⟩ : syracuseStep 16922999 = 25384499) B25384499
theorem B6257033 : Blo 1853628 6257033 := bstep (se 2 (by rfl) ⟨2346387, by rfl⟩ : syracuseStep 6257033 = 4692775) B4692775
theorem B4692431 : Blo 1853628 4692431 := bstep (se 1 (by rfl) ⟨3519323, by rfl⟩ : syracuseStep 4692431 = 7038647) B7038647
theorem B15850079 : Blo 1853628 15850079 := bstep (se 1 (by rfl) ⟨11887559, by rfl⟩ : syracuseStep 15850079 = 23775119) B23775119
theorem B3128233 : Blo 1853628 3128233 := bstep (se 2 (by rfl) ⟨1173087, by rfl⟩ : syracuseStep 3128233 = 2346175) B2346175
theorem B22567895 : Blo 1853628 22567895 := bstep (se 1 (by rfl) ⟨16925921, by rfl⟩ : syracuseStep 22567895 = 33851843) B33851843
theorem B3136495 : Blo 1853628 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B3759401 : Blo 1853628 3759401 := bstep (se 2 (by rfl) ⟨1409775, by rfl⟩ : syracuseStep 3759401 = 2819551) B2819551
theorem B8912231 : Blo 1853628 8912231 := bstep (se 1 (by rfl) ⟨6684173, by rfl⟩ : syracuseStep 8912231 = 13368347) B13368347
theorem B23756561 : Blo 1853628 23756561 := bstep (se 2 (by rfl) ⟨8908710, by rfl⟩ : syracuseStep 23756561 = 17817421) B17817421
theorem B4694395 : Blo 1853628 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B4457375 : Blo 1853628 4457375 := bstep (se 1 (by rfl) ⟨3343031, by rfl⟩ : syracuseStep 4457375 = 6686063) B6686063
theorem B6259679 : Blo 1853628 6259679 := bstep (se 1 (by rfl) ⟨4694759, by rfl⟩ : syracuseStep 6259679 = 9389519) B9389519
theorem B40084703 : Blo 1853628 40084703 := bstep (se 1 (by rfl) ⟨30063527, by rfl⟩ : syracuseStep 40084703 = 60127055) B60127055
theorem B4170977 : Blo 1853628 4170977 := bstep (se 2 (by rfl) ⟨1564116, by rfl⟩ : syracuseStep 4170977 = 3128233) B3128233
theorem B11281999 : Blo 1853628 11281999 := bstep (se 1 (by rfl) ⟨8461499, by rfl⟩ : syracuseStep 11281999 = 16922999) B16922999
theorem B4171355 : Blo 1853628 4171355 := bstep (se 1 (by rfl) ⟨3128516, by rfl⟩ : syracuseStep 4171355 = 6257033) B6257033
theorem B13551347 : Blo 1853628 13551347 := bstep (se 1 (by rfl) ⟨10163510, by rfl⟩ : syracuseStep 13551347 = 20327021) B20327021
theorem B10029221 : Blo 1853628 10029221 := bstep (se 4 (by rfl) ⟨940239, by rfl⟩ : syracuseStep 10029221 = 1880479) B1880479
theorem B5941487 : Blo 1853628 5941487 := bstep (se 1 (by rfl) ⟨4456115, by rfl⟩ : syracuseStep 5941487 = 8912231) B8912231
theorem B15845705 : Blo 1853628 15845705 := bstep (se 2 (by rfl) ⟨5942139, by rfl⟩ : syracuseStep 15845705 = 11884279) B11884279
theorem B10029565 : Blo 1853628 10029565 := bstep (se 3 (by rfl) ⟨1880543, by rfl⟩ : syracuseStep 10029565 = 3761087) B3761087
theorem B15837707 : Blo 1853628 15837707 := bstep (se 1 (by rfl) ⟨11878280, by rfl⟩ : syracuseStep 15837707 = 23756561) B23756561
theorem B4172975 : Blo 1853628 4172975 := bstep (se 1 (by rfl) ⟨3129731, by rfl⟩ : syracuseStep 4172975 = 6259463) B6259463
theorem B1854911 : Blo 1853628 1854911 := bstep (se 1 (by rfl) ⟨1391183, by rfl⟩ : syracuseStep 1854911 = 2782367) B2782367
theorem B1855003 : Blo 1853628 1855003 := bstep (se 1 (by rfl) ⟨1391252, by rfl⟩ : syracuseStep 1855003 = 2782505) B2782505
theorem B4173659 : Blo 1853628 4173659 := bstep (se 1 (by rfl) ⟨3130244, by rfl⟩ : syracuseStep 4173659 = 6260489) B6260489
theorem B2781095 : Blo 1853628 2781095 := bstep (se 1 (by rfl) ⟨2085821, by rfl⟩ : syracuseStep 2781095 = 4171643) B4171643
theorem B4181993 : Blo 1853628 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B11882639 : Blo 1853628 11882639 := bstep (se 1 (by rfl) ⟨8911979, by rfl⟩ : syracuseStep 11882639 = 17823959) B17823959
theorem B4173983 : Blo 1853628 4173983 := bstep (se 1 (by rfl) ⟨3130487, by rfl⟩ : syracuseStep 4173983 = 6260975) B6260975
theorem B2781353 : Blo 1853628 2781353 := bstep (se 2 (by rfl) ⟨1043007, by rfl⟩ : syracuseStep 2781353 = 2086015) B2086015
theorem B2781467 : Blo 1853628 2781467 := bstep (se 1 (by rfl) ⟨2086100, by rfl⟩ : syracuseStep 2781467 = 4172201) B4172201
theorem B20058617 : Blo 1853628 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B4174343 : Blo 1853628 4174343 := bstep (se 1 (by rfl) ⟨3130757, by rfl⟩ : syracuseStep 4174343 = 6261515) B6261515
theorem B15045263 : Blo 1853628 15045263 := bstep (se 1 (by rfl) ⟨11283947, by rfl⟩ : syracuseStep 15045263 = 22567895) B22567895
theorem B4174703 : Blo 1853628 4174703 := bstep (se 1 (by rfl) ⟨3131027, by rfl⟩ : syracuseStep 4174703 = 6262055) B6262055
theorem B5010623 : Blo 1853628 5010623 := bstep (se 1 (by rfl) ⟨3757967, by rfl⟩ : syracuseStep 5010623 = 7515935) B7515935
theorem B3962495 : Blo 1853628 3962495 := bstep (se 1 (by rfl) ⟨2971871, by rfl⟩ : syracuseStep 3962495 = 5943743) B5943743
theorem B2087023 : Blo 1853628 2087023 := bstep (se 1 (by rfl) ⟨1565267, by rfl⟩ : syracuseStep 2087023 = 3130535) B3130535
theorem B10705111 : Blo 1853628 10705111 := bstep (se 1 (by rfl) ⟨8028833, by rfl⟩ : syracuseStep 10705111 = 16057667) B16057667
theorem B4692563 : Blo 1853628 4692563 := bstep (se 1 (by rfl) ⟨3519422, by rfl⟩ : syracuseStep 4692563 = 7038845) B7038845
theorem B304437851 : Blo 1853628 304437851 := bstep (se 1 (by rfl) ⟨228328388, by rfl⟩ : syracuseStep 304437851 = 456656777) B456656777
theorem B308681381 : Blo 1853628 308681381 := bstep (se 4 (by rfl) ⟨28938879, by rfl⟩ : syracuseStep 308681381 = 57877759) B57877759
theorem B3128287 : Blo 1853628 3128287 := bstep (se 1 (by rfl) ⟨2346215, by rfl⟩ : syracuseStep 3128287 = 4692431) B4692431
theorem B11279369 : Blo 1853628 11279369 := bstep (se 2 (by rfl) ⟨4229763, by rfl⟩ : syracuseStep 11279369 = 8459527) B8459527
theorem B10566719 : Blo 1853628 10566719 := bstep (se 1 (by rfl) ⟨7925039, by rfl⟩ : syracuseStep 10566719 = 15850079) B15850079
theorem B32103863 : Blo 1853628 32103863 := bstep (se 1 (by rfl) ⟨24077897, by rfl⟩ : syracuseStep 32103863 = 48155795) B48155795
theorem B32120321 : Blo 1853628 32120321 := bstep (se 2 (by rfl) ⟨12045120, by rfl⟩ : syracuseStep 32120321 = 24090241) B24090241
theorem B2506267 : Blo 1853628 2506267 := bstep (se 1 (by rfl) ⟨1879700, by rfl⟩ : syracuseStep 2506267 = 3759401) B3759401
theorem B30481991 : Blo 1853628 30481991 := bstep (se 1 (by rfl) ⟨22861493, by rfl⟩ : syracuseStep 30481991 = 45722987) B45722987
theorem B47554127 : Blo 1853628 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B7921759 : Blo 1853628 7921759 := bstep (se 1 (by rfl) ⟨5941319, by rfl⟩ : syracuseStep 7921759 = 11882639) B11882639
theorem B6259193 : Blo 1853628 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B26723135 : Blo 1853628 26723135 := bstep (se 1 (by rfl) ⟨20042351, by rfl⟩ : syracuseStep 26723135 = 40084703) B40084703
theorem B4171049 : Blo 1853628 4171049 := bstep (se 2 (by rfl) ⟨1564143, by rfl⟩ : syracuseStep 4171049 = 3128287) B3128287
theorem B6686147 : Blo 1853628 6686147 := bstep (se 1 (by rfl) ⟨5014610, by rfl⟩ : syracuseStep 6686147 = 10029221) B10029221
theorem B202958567 : Blo 1853628 202958567 := bstep (se 1 (by rfl) ⟨152218925, by rfl⟩ : syracuseStep 202958567 = 304437851) B304437851
theorem B36136925 : Blo 1853628 36136925 := bstep (se 3 (by rfl) ⟨6775673, by rfl⟩ : syracuseStep 36136925 = 13551347) B13551347
theorem B15042665 : Blo 1853628 15042665 := bstep (se 2 (by rfl) ⟨5640999, by rfl⟩ : syracuseStep 15042665 = 11281999) B11281999
theorem B1854063 : Blo 1853628 1854063 := bstep (se 1 (by rfl) ⟨1390547, by rfl⟩ : syracuseStep 1854063 = 2781095) B2781095
theorem B2787995 : Blo 1853628 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B1854235 : Blo 1853628 1854235 := bstep (se 1 (by rfl) ⟨1390676, by rfl⟩ : syracuseStep 1854235 = 2781353) B2781353
theorem B1854311 : Blo 1853628 1854311 := bstep (se 1 (by rfl) ⟨1390733, by rfl⟩ : syracuseStep 1854311 = 2781467) B2781467
theorem B13372411 : Blo 1853628 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B10030175 : Blo 1853628 10030175 := bstep (se 1 (by rfl) ⟨7522631, by rfl⟩ : syracuseStep 10030175 = 15045263) B15045263
theorem B4173119 : Blo 1853628 4173119 := bstep (se 1 (by rfl) ⟨3129839, by rfl⟩ : syracuseStep 4173119 = 6259679) B6259679
theorem B2780651 : Blo 1853628 2780651 := bstep (se 1 (by rfl) ⟨2085488, by rfl⟩ : syracuseStep 2780651 = 4170977) B4170977
theorem B2780903 : Blo 1853628 2780903 := bstep (se 1 (by rfl) ⟨2085677, by rfl⟩ : syracuseStep 2780903 = 4171355) B4171355
theorem B2641663 : Blo 1853628 2641663 := bstep (se 1 (by rfl) ⟨1981247, by rfl⟩ : syracuseStep 2641663 = 3962495) B3962495
theorem B57093925 : Blo 1853628 57093925 := bstep (se 4 (by rfl) ⟨5352555, by rfl⟩ : syracuseStep 57093925 = 10705111) B10705111
theorem B3960991 : Blo 1853628 3960991 := bstep (se 1 (by rfl) ⟨2970743, by rfl⟩ : syracuseStep 3960991 = 5941487) B5941487
theorem B10563803 : Blo 1853628 10563803 := bstep (se 1 (by rfl) ⟨7922852, by rfl⟩ : syracuseStep 10563803 = 15845705) B15845705
theorem B205787587 : Blo 1853628 205787587 := bstep (se 1 (by rfl) ⟨154340690, by rfl⟩ : syracuseStep 205787587 = 308681381) B308681381
theorem B2781983 : Blo 1853628 2781983 := bstep (se 1 (by rfl) ⟨2086487, by rfl⟩ : syracuseStep 2781983 = 4172975) B4172975
theorem B21402575 : Blo 1853628 21402575 := bstep (se 1 (by rfl) ⟨16051931, by rfl⟩ : syracuseStep 21402575 = 32103863) B32103863
theorem B20321327 : Blo 1853628 20321327 := bstep (se 1 (by rfl) ⟨15240995, by rfl⟩ : syracuseStep 20321327 = 30481991) B30481991
theorem B2782439 : Blo 1853628 2782439 := bstep (se 1 (by rfl) ⟨2086829, by rfl⟩ : syracuseStep 2782439 = 4173659) B4173659
theorem B53491013 : Blo 1853628 53491013 := bstep (se 4 (by rfl) ⟨5014782, by rfl⟩ : syracuseStep 53491013 = 10029565) B10029565
theorem B30078317 : Blo 1853628 30078317 := bstep (se 3 (by rfl) ⟨5639684, by rfl⟩ : syracuseStep 30078317 = 11279369) B11279369
theorem B2782655 : Blo 1853628 2782655 := bstep (se 1 (by rfl) ⟨2086991, by rfl⟩ : syracuseStep 2782655 = 4173983) B4173983
theorem B13366757 : Blo 1853628 13366757 := bstep (se 4 (by rfl) ⟨1253133, by rfl⟩ : syracuseStep 13366757 = 2506267) B2506267
theorem B2782697 : Blo 1853628 2782697 := bstep (se 2 (by rfl) ⟨1043511, by rfl⟩ : syracuseStep 2782697 = 2087023) B2087023
theorem B2782895 : Blo 1853628 2782895 := bstep (se 1 (by rfl) ⟨2087171, by rfl⟩ : syracuseStep 2782895 = 4174343) B4174343
theorem B2783135 : Blo 1853628 2783135 := bstep (se 1 (by rfl) ⟨2087351, by rfl⟩ : syracuseStep 2783135 = 4174703) B4174703
theorem B2971583 : Blo 1853628 2971583 := bstep (se 1 (by rfl) ⟨2228687, by rfl⟩ : syracuseStep 2971583 = 4457375) B4457375
theorem B3340415 : Blo 1853628 3340415 := bstep (se 1 (by rfl) ⟨2505311, by rfl⟩ : syracuseStep 3340415 = 5010623) B5010623
theorem B85654189 : Blo 1853628 85654189 := bstep (se 3 (by rfl) ⟨16060160, by rfl⟩ : syracuseStep 85654189 = 32120321) B32120321
theorem B10558471 : Blo 1853628 10558471 := bstep (se 1 (by rfl) ⟨7918853, by rfl⟩ : syracuseStep 10558471 = 15837707) B15837707
theorem B3128375 : Blo 1853628 3128375 := bstep (se 1 (by rfl) ⟨2346281, by rfl⟩ : syracuseStep 3128375 = 4692563) B4692563
theorem B7044479 : Blo 1853628 7044479 := bstep (se 1 (by rfl) ⟨5283359, by rfl⟩ : syracuseStep 7044479 = 10566719) B10566719
theorem B31702751 : Blo 1853628 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B54190205 : Blo 1853628 54190205 := bstep (se 3 (by rfl) ⟨10160663, by rfl⟩ : syracuseStep 54190205 = 20321327) B20321327
theorem B274383449 : Blo 1853628 274383449 := bstep (se 2 (by rfl) ⟨102893793, by rfl⟩ : syracuseStep 274383449 = 205787587) B205787587
theorem B35660675 : Blo 1853628 35660675 := bstep (se 1 (by rfl) ⟨26745506, by rfl⟩ : syracuseStep 35660675 = 53491013) B53491013
theorem B114205585 : Blo 1853628 114205585 := bstep (se 2 (by rfl) ⟨42827094, by rfl⟩ : syracuseStep 114205585 = 85654189) B85654189
theorem B4457431 : Blo 1853628 4457431 := bstep (se 1 (by rfl) ⟨3343073, by rfl⟩ : syracuseStep 4457431 = 6686147) B6686147
theorem B10028443 : Blo 1853628 10028443 := bstep (se 1 (by rfl) ⟨7521332, by rfl⟩ : syracuseStep 10028443 = 15042665) B15042665
theorem B6686783 : Blo 1853628 6686783 := bstep (se 1 (by rfl) ⟨5015087, by rfl⟩ : syracuseStep 6686783 = 10030175) B10030175
theorem B4696319 : Blo 1853628 4696319 := bstep (se 1 (by rfl) ⟨3522239, by rfl⟩ : syracuseStep 4696319 = 7044479) B7044479
theorem B1853767 : Blo 1853628 1853767 := bstep (se 1 (by rfl) ⟨1390325, by rfl⟩ : syracuseStep 1853767 = 2780651) B2780651
theorem B1853935 : Blo 1853628 1853935 := bstep (se 1 (by rfl) ⟨1390451, by rfl⟩ : syracuseStep 1853935 = 2780903) B2780903
theorem B10562345 : Blo 1853628 10562345 := bstep (se 2 (by rfl) ⟨3960879, by rfl⟩ : syracuseStep 10562345 = 7921759) B7921759
theorem B4172795 : Blo 1853628 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B1854655 : Blo 1853628 1854655 := bstep (se 1 (by rfl) ⟨1390991, by rfl⟩ : syracuseStep 1854655 = 2781983) B2781983
theorem B1854959 : Blo 1853628 1854959 := bstep (se 1 (by rfl) ⟨1391219, by rfl⟩ : syracuseStep 1854959 = 2782439) B2782439
theorem B2780699 : Blo 1853628 2780699 := bstep (se 1 (by rfl) ⟨2085524, by rfl⟩ : syracuseStep 2780699 = 4171049) B4171049
theorem B1855103 : Blo 1853628 1855103 := bstep (se 1 (by rfl) ⟨1391327, by rfl⟩ : syracuseStep 1855103 = 2782655) B2782655
theorem B1855131 : Blo 1853628 1855131 := bstep (se 1 (by rfl) ⟨1391348, by rfl⟩ : syracuseStep 1855131 = 2782697) B2782697
theorem B1855263 : Blo 1853628 1855263 := bstep (se 1 (by rfl) ⟨1391447, by rfl⟩ : syracuseStep 1855263 = 2782895) B2782895
theorem B1855423 : Blo 1853628 1855423 := bstep (se 1 (by rfl) ⟨1391567, by rfl⟩ : syracuseStep 1855423 = 2783135) B2783135
theorem B17829881 : Blo 1853628 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B14077961 : Blo 1853628 14077961 := bstep (se 2 (by rfl) ⟨5279235, by rfl⟩ : syracuseStep 14077961 = 10558471) B10558471
theorem B2085583 : Blo 1853628 2085583 := bstep (se 1 (by rfl) ⟨1564187, by rfl⟩ : syracuseStep 2085583 = 3128375) B3128375
theorem B2782079 : Blo 1853628 2782079 := bstep (se 1 (by rfl) ⟨2086559, by rfl⟩ : syracuseStep 2782079 = 4173119) B4173119
theorem B76125233 : Blo 1853628 76125233 := bstep (se 2 (by rfl) ⟨28546962, by rfl⟩ : syracuseStep 76125233 = 57093925) B57093925
theorem B7042535 : Blo 1853628 7042535 := bstep (se 1 (by rfl) ⟨5281901, by rfl⟩ : syracuseStep 7042535 = 10563803) B10563803
theorem B5281321 : Blo 1853628 5281321 := bstep (se 2 (by rfl) ⟨1980495, by rfl⟩ : syracuseStep 5281321 = 3960991) B3960991
theorem B17815423 : Blo 1853628 17815423 := bstep (se 1 (by rfl) ⟨13361567, by rfl⟩ : syracuseStep 17815423 = 26723135) B26723135
theorem B14268383 : Blo 1853628 14268383 := bstep (se 1 (by rfl) ⟨10701287, by rfl⟩ : syracuseStep 14268383 = 21402575) B21402575
theorem B20052211 : Blo 1853628 20052211 := bstep (se 1 (by rfl) ⟨15039158, by rfl⟩ : syracuseStep 20052211 = 30078317) B30078317
theorem B8911171 : Blo 1853628 8911171 := bstep (se 1 (by rfl) ⟨6683378, by rfl⟩ : syracuseStep 8911171 = 13366757) B13366757
theorem B135305711 : Blo 1853628 135305711 := bstep (se 1 (by rfl) ⟨101479283, by rfl⟩ : syracuseStep 135305711 = 202958567) B202958567
theorem B1981055 : Blo 1853628 1981055 := bstep (se 1 (by rfl) ⟨1485791, by rfl⟩ : syracuseStep 1981055 = 2971583) B2971583
theorem B24091283 : Blo 1853628 24091283 := bstep (se 1 (by rfl) ⟨18068462, by rfl⟩ : syracuseStep 24091283 = 36136925) B36136925
theorem B2226943 : Blo 1853628 2226943 := bstep (se 1 (by rfl) ⟨1670207, by rfl⟩ : syracuseStep 2226943 = 3340415) B3340415
theorem B1858663 : Blo 1853628 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B3522217 : Blo 1853628 3522217 := bstep (se 2 (by rfl) ⟨1320831, by rfl⟩ : syracuseStep 3522217 = 2641663) B2641663
theorem B21135167 : Blo 1853628 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B36126803 : Blo 1853628 36126803 := bstep (se 1 (by rfl) ⟨27095102, by rfl⟩ : syracuseStep 36126803 = 54190205) B54190205
theorem B23773783 : Blo 1853628 23773783 := bstep (se 1 (by rfl) ⟨17830337, by rfl⟩ : syracuseStep 23773783 = 35660675) B35660675
theorem B50750155 : Blo 1853628 50750155 := bstep (se 1 (by rfl) ⟨38062616, by rfl⟩ : syracuseStep 50750155 = 76125233) B76125233
theorem B4695023 : Blo 1853628 4695023 := bstep (se 1 (by rfl) ⟨3521267, by rfl⟩ : syracuseStep 4695023 = 7042535) B7042535
theorem B152274113 : Blo 1853628 152274113 := bstep (se 2 (by rfl) ⟨57102792, by rfl⟩ : syracuseStep 152274113 = 114205585) B114205585
theorem B9512255 : Blo 1853628 9512255 := bstep (se 1 (by rfl) ⟨7134191, by rfl⟩ : syracuseStep 9512255 = 14268383) B14268383
theorem B4457855 : Blo 1853628 4457855 := bstep (se 1 (by rfl) ⟨3343391, by rfl⟩ : syracuseStep 4457855 = 6686783) B6686783
theorem B3130879 : Blo 1853628 3130879 := bstep (se 1 (by rfl) ⟨2348159, by rfl⟩ : syracuseStep 3130879 = 4696319) B4696319
theorem B90203807 : Blo 1853628 90203807 := bstep (se 1 (by rfl) ⟨67652855, by rfl⟩ : syracuseStep 90203807 = 135305711) B135305711
theorem B13371257 : Blo 1853628 13371257 := bstep (se 2 (by rfl) ⟨5014221, by rfl⟩ : syracuseStep 13371257 = 10028443) B10028443
theorem B4696289 : Blo 1853628 4696289 := bstep (se 2 (by rfl) ⟨1761108, by rfl⟩ : syracuseStep 4696289 = 3522217) B3522217
theorem B1853799 : Blo 1853628 1853799 := bstep (se 1 (by rfl) ⟨1390349, by rfl⟩ : syracuseStep 1853799 = 2780699) B2780699
theorem B182922299 : Blo 1853628 182922299 := bstep (se 1 (by rfl) ⟨137191724, by rfl⟩ : syracuseStep 182922299 = 274383449) B274383449
theorem B11881561 : Blo 1853628 11881561 := bstep (se 2 (by rfl) ⟨4455585, by rfl⟩ : syracuseStep 11881561 = 8911171) B8911171
theorem B1854719 : Blo 1853628 1854719 := bstep (se 1 (by rfl) ⟨1391039, by rfl⟩ : syracuseStep 1854719 = 2782079) B2782079
theorem B2780777 : Blo 1853628 2780777 := bstep (se 2 (by rfl) ⟨1042791, by rfl⟩ : syracuseStep 2780777 = 2085583) B2085583
theorem B5943241 : Blo 1853628 5943241 := bstep (se 2 (by rfl) ⟨2228715, by rfl⟩ : syracuseStep 5943241 = 4457431) B4457431
theorem B2478217 : Blo 1853628 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B16060855 : Blo 1853628 16060855 := bstep (se 1 (by rfl) ⟨12045641, by rfl⟩ : syracuseStep 16060855 = 24091283) B24091283
theorem B7041563 : Blo 1853628 7041563 := bstep (se 1 (by rfl) ⟨5281172, by rfl⟩ : syracuseStep 7041563 = 10562345) B10562345
theorem B2781863 : Blo 1853628 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B7041761 : Blo 1853628 7041761 := bstep (se 2 (by rfl) ⟨2640660, by rfl⟩ : syracuseStep 7041761 = 5281321) B5281321
theorem B23753897 : Blo 1853628 23753897 := bstep (se 2 (by rfl) ⟨8907711, by rfl⟩ : syracuseStep 23753897 = 17815423) B17815423
theorem B9385307 : Blo 1853628 9385307 := bstep (se 1 (by rfl) ⟨7038980, by rfl⟩ : syracuseStep 9385307 = 14077961) B14077961
theorem B26736281 : Blo 1853628 26736281 := bstep (se 2 (by rfl) ⟨10026105, by rfl⟩ : syracuseStep 26736281 = 20052211) B20052211
theorem B11877029 : Blo 1853628 11877029 := bstep (se 4 (by rfl) ⟨1113471, by rfl⟩ : syracuseStep 11877029 = 2226943) B2226943
theorem B5282813 : Blo 1853628 5282813 := bstep (se 3 (by rfl) ⟨990527, by rfl⟩ : syracuseStep 5282813 = 1981055) B1981055
theorem B14090111 : Blo 1853628 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B11886587 : Blo 1853628 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B24084535 : Blo 1853628 24084535 := bstep (se 1 (by rfl) ⟨18063401, by rfl⟩ : syracuseStep 24084535 = 36126803) B36126803
theorem B4694375 : Blo 1853628 4694375 := bstep (se 1 (by rfl) ⟨3520781, by rfl⟩ : syracuseStep 4694375 = 7041563) B7041563
theorem B4694507 : Blo 1853628 4694507 := bstep (se 1 (by rfl) ⟨3520880, by rfl⟩ : syracuseStep 4694507 = 7041761) B7041761
theorem B21414473 : Blo 1853628 21414473 := bstep (se 2 (by rfl) ⟨8030427, by rfl⟩ : syracuseStep 21414473 = 16060855) B16060855
theorem B3130015 : Blo 1853628 3130015 := bstep (se 1 (by rfl) ⟨2347511, by rfl⟩ : syracuseStep 3130015 = 4695023) B4695023
theorem B15835931 : Blo 1853628 15835931 := bstep (se 1 (by rfl) ⟨11876948, by rfl⟩ : syracuseStep 15835931 = 23753897) B23753897
theorem B101516075 : Blo 1853628 101516075 := bstep (se 1 (by rfl) ⟨76137056, by rfl⟩ : syracuseStep 101516075 = 152274113) B152274113
theorem B6341503 : Blo 1853628 6341503 := bstep (se 1 (by rfl) ⟨4756127, by rfl⟩ : syracuseStep 6341503 = 9512255) B9512255
theorem B67666873 : Blo 1853628 67666873 := bstep (se 2 (by rfl) ⟨25375077, by rfl⟩ : syracuseStep 67666873 = 50750155) B50750155
theorem B8914171 : Blo 1853628 8914171 := bstep (se 1 (by rfl) ⟨6685628, by rfl⟩ : syracuseStep 8914171 = 13371257) B13371257
theorem B3130859 : Blo 1853628 3130859 := bstep (se 1 (by rfl) ⟨2348144, by rfl⟩ : syracuseStep 3130859 = 4696289) B4696289
theorem B121948199 : Blo 1853628 121948199 := bstep (se 1 (by rfl) ⟨91461149, by rfl⟩ : syracuseStep 121948199 = 182922299) B182922299
theorem B1853851 : Blo 1853628 1853851 := bstep (se 1 (by rfl) ⟨1390388, by rfl⟩ : syracuseStep 1853851 = 2780777) B2780777
theorem B7924321 : Blo 1853628 7924321 := bstep (se 2 (by rfl) ⟨2971620, by rfl⟩ : syracuseStep 7924321 = 5943241) B5943241
theorem B7924391 : Blo 1853628 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B1854575 : Blo 1853628 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B31698377 : Blo 1853628 31698377 := bstep (se 2 (by rfl) ⟨11886891, by rfl⟩ : syracuseStep 31698377 = 23773783) B23773783
theorem B7918019 : Blo 1853628 7918019 := bstep (se 1 (by rfl) ⟨5938514, by rfl⟩ : syracuseStep 7918019 = 11877029) B11877029
theorem B4174505 : Blo 1853628 4174505 := bstep (se 2 (by rfl) ⟨1565439, by rfl⟩ : syracuseStep 4174505 = 3130879) B3130879
theorem B9393407 : Blo 1853628 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B52868629 : Blo 1853628 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B6256871 : Blo 1853628 6256871 := bstep (se 1 (by rfl) ⟨4692653, by rfl⟩ : syracuseStep 6256871 = 9385307) B9385307
theorem B2971903 : Blo 1853628 2971903 := bstep (se 1 (by rfl) ⟨2228927, by rfl⟩ : syracuseStep 2971903 = 4457855) B4457855
theorem B17824187 : Blo 1853628 17824187 := bstep (se 1 (by rfl) ⟨13368140, by rfl⟩ : syracuseStep 17824187 = 26736281) B26736281
theorem B60135871 : Blo 1853628 60135871 := bstep (se 1 (by rfl) ⟨45101903, by rfl⟩ : syracuseStep 60135871 = 90203807) B90203807
theorem B15842081 : Blo 1853628 15842081 := bstep (se 2 (by rfl) ⟨5940780, by rfl⟩ : syracuseStep 15842081 = 11881561) B11881561
theorem B3521875 : Blo 1853628 3521875 := bstep (se 1 (by rfl) ⟨2641406, by rfl⟩ : syracuseStep 3521875 = 5282813) B5282813
theorem B32112713 : Blo 1853628 32112713 := bstep (se 2 (by rfl) ⟨12042267, by rfl⟩ : syracuseStep 32112713 = 24084535) B24084535
theorem B3129583 : Blo 1853628 3129583 := bstep (se 1 (by rfl) ⟨2347187, by rfl⟩ : syracuseStep 3129583 = 4694375) B4694375
theorem B3129671 : Blo 1853628 3129671 := bstep (se 1 (by rfl) ⟨2347253, by rfl⟩ : syracuseStep 3129671 = 4694507) B4694507
theorem B8455337 : Blo 1853628 8455337 := bstep (se 2 (by rfl) ⟨3170751, by rfl⟩ : syracuseStep 8455337 = 6341503) B6341503
theorem B81298799 : Blo 1853628 81298799 := bstep (se 1 (by rfl) ⟨60974099, by rfl⟩ : syracuseStep 81298799 = 121948199) B121948199
theorem B4171247 : Blo 1853628 4171247 := bstep (se 1 (by rfl) ⟨3128435, by rfl⟩ : syracuseStep 4171247 = 6256871) B6256871
theorem B4695833 : Blo 1853628 4695833 := bstep (se 2 (by rfl) ⟨1760937, by rfl⟩ : syracuseStep 4695833 = 3521875) B3521875
theorem B10561387 : Blo 1853628 10561387 := bstep (se 1 (by rfl) ⟨7921040, by rfl⟩ : syracuseStep 10561387 = 15842081) B15842081
theorem B5278679 : Blo 1853628 5278679 := bstep (se 1 (by rfl) ⟨3959009, by rfl⟩ : syracuseStep 5278679 = 7918019) B7918019
theorem B67677383 : Blo 1853628 67677383 := bstep (se 1 (by rfl) ⟨50758037, by rfl⟩ : syracuseStep 67677383 = 101516075) B101516075
theorem B6262271 : Blo 1853628 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B4173353 : Blo 1853628 4173353 := bstep (se 2 (by rfl) ⟨1565007, by rfl⟩ : syracuseStep 4173353 = 3130015) B3130015
theorem B90222497 : Blo 1853628 90222497 := bstep (se 2 (by rfl) ⟨33833436, by rfl⟩ : syracuseStep 90222497 = 67666873) B67666873
theorem B11882791 : Blo 1853628 11882791 := bstep (se 1 (by rfl) ⟨8912093, by rfl⟩ : syracuseStep 11882791 = 17824187) B17824187
theorem B21132251 : Blo 1853628 21132251 := bstep (se 1 (by rfl) ⟨15849188, by rfl⟩ : syracuseStep 21132251 = 31698377) B31698377
theorem B3962537 : Blo 1853628 3962537 := bstep (se 2 (by rfl) ⟨1485951, by rfl⟩ : syracuseStep 3962537 = 2971903) B2971903
theorem B14276315 : Blo 1853628 14276315 := bstep (se 1 (by rfl) ⟨10707236, by rfl⟩ : syracuseStep 14276315 = 21414473) B21414473
theorem B2783003 : Blo 1853628 2783003 := bstep (se 1 (by rfl) ⟨2087252, by rfl⟩ : syracuseStep 2783003 = 4174505) B4174505
theorem B10557287 : Blo 1853628 10557287 := bstep (se 1 (by rfl) ⟨7917965, by rfl⟩ : syracuseStep 10557287 = 15835931) B15835931
theorem B80181161 : Blo 1853628 80181161 := bstep (se 2 (by rfl) ⟨30067935, by rfl⟩ : syracuseStep 80181161 = 60135871) B60135871
theorem B10565761 : Blo 1853628 10565761 := bstep (se 2 (by rfl) ⟨3962160, by rfl⟩ : syracuseStep 10565761 = 7924321) B7924321
theorem B2087239 : Blo 1853628 2087239 := bstep (se 1 (by rfl) ⟨1565429, by rfl⟩ : syracuseStep 2087239 = 3130859) B3130859
theorem B11885561 : Blo 1853628 11885561 := bstep (se 2 (by rfl) ⟨4457085, by rfl⟩ : syracuseStep 11885561 = 8914171) B8914171
theorem B5282927 : Blo 1853628 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B70491505 : Blo 1853628 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B15843721 : Blo 1853628 15843721 := bstep (se 2 (by rfl) ⟨5941395, by rfl⟩ : syracuseStep 15843721 = 11882791) B11882791
theorem B5636891 : Blo 1853628 5636891 := bstep (se 1 (by rfl) ⟨4227668, by rfl⟩ : syracuseStep 5636891 = 8455337) B8455337
theorem B54199199 : Blo 1853628 54199199 := bstep (se 1 (by rfl) ⟨40649399, by rfl⟩ : syracuseStep 54199199 = 81298799) B81298799
theorem B3130555 : Blo 1853628 3130555 := bstep (se 1 (by rfl) ⟨2347916, by rfl⟩ : syracuseStep 3130555 = 4695833) B4695833
theorem B7038191 : Blo 1853628 7038191 := bstep (se 1 (by rfl) ⟨5278643, by rfl⟩ : syracuseStep 7038191 = 10557287) B10557287
theorem B53454107 : Blo 1853628 53454107 := bstep (se 1 (by rfl) ⟨40090580, by rfl⟩ : syracuseStep 53454107 = 80181161) B80181161
theorem B93988673 : Blo 1853628 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B7923707 : Blo 1853628 7923707 := bstep (se 1 (by rfl) ⟨5942780, by rfl⟩ : syracuseStep 7923707 = 11885561) B11885561
theorem B60148331 : Blo 1853628 60148331 := bstep (se 1 (by rfl) ⟨45111248, by rfl⟩ : syracuseStep 60148331 = 90222497) B90222497
theorem B21408475 : Blo 1853628 21408475 := bstep (se 1 (by rfl) ⟨16056356, by rfl⟩ : syracuseStep 21408475 = 32112713) B32112713
theorem B4172777 : Blo 1853628 4172777 := bstep (se 2 (by rfl) ⟨1564791, by rfl⟩ : syracuseStep 4172777 = 3129583) B3129583
theorem B2780831 : Blo 1853628 2780831 := bstep (se 1 (by rfl) ⟨2085623, by rfl⟩ : syracuseStep 2780831 = 4171247) B4171247
theorem B2641691 : Blo 1853628 2641691 := bstep (se 1 (by rfl) ⟨1981268, by rfl⟩ : syracuseStep 2641691 = 3962537) B3962537
theorem B1855335 : Blo 1853628 1855335 := bstep (se 1 (by rfl) ⟨1391501, by rfl⟩ : syracuseStep 1855335 = 2783003) B2783003
theorem B3519119 : Blo 1853628 3519119 := bstep (se 1 (by rfl) ⟨2639339, by rfl⟩ : syracuseStep 3519119 = 5278679) B5278679
theorem B45118255 : Blo 1853628 45118255 := bstep (se 1 (by rfl) ⟨33838691, by rfl⟩ : syracuseStep 45118255 = 67677383) B67677383
theorem B4174847 : Blo 1853628 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B2782235 : Blo 1853628 2782235 := bstep (se 1 (by rfl) ⟨2086676, by rfl⟩ : syracuseStep 2782235 = 4173353) B4173353
theorem B14087681 : Blo 1853628 14087681 := bstep (se 2 (by rfl) ⟨5282880, by rfl⟩ : syracuseStep 14087681 = 10565761) B10565761
theorem B2086447 : Blo 1853628 2086447 := bstep (se 1 (by rfl) ⟨1564835, by rfl⟩ : syracuseStep 2086447 = 3129671) B3129671
theorem B2782985 : Blo 1853628 2782985 := bstep (se 2 (by rfl) ⟨1043619, by rfl⟩ : syracuseStep 2782985 = 2087239) B2087239
theorem B14088167 : Blo 1853628 14088167 := bstep (se 1 (by rfl) ⟨10566125, by rfl⟩ : syracuseStep 14088167 = 21132251) B21132251
theorem B9517543 : Blo 1853628 9517543 := bstep (se 1 (by rfl) ⟨7138157, by rfl⟩ : syracuseStep 9517543 = 14276315) B14276315
theorem B3521951 : Blo 1853628 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B14081849 : Blo 1853628 14081849 := bstep (se 2 (by rfl) ⟨5280693, by rfl⟩ : syracuseStep 14081849 = 10561387) B10561387
theorem B35636071 : Blo 1853628 35636071 := bstep (se 1 (by rfl) ⟨26727053, by rfl⟩ : syracuseStep 35636071 = 53454107) B53454107
theorem B1853887 : Blo 1853628 1853887 := bstep (se 1 (by rfl) ⟨1390415, by rfl⟩ : syracuseStep 1853887 = 2780831) B2780831
theorem B50760229 : Blo 1853628 50760229 := bstep (se 4 (by rfl) ⟨4758771, by rfl⟩ : syracuseStep 50760229 = 9517543) B9517543
theorem B2346079 : Blo 1853628 2346079 := bstep (se 1 (by rfl) ⟨1759559, by rfl⟩ : syracuseStep 2346079 = 3519119) B3519119
theorem B1854823 : Blo 1853628 1854823 := bstep (se 1 (by rfl) ⟨1391117, by rfl⟩ : syracuseStep 1854823 = 2782235) B2782235
theorem B28544633 : Blo 1853628 28544633 := bstep (se 2 (by rfl) ⟨10704237, by rfl⟩ : syracuseStep 28544633 = 21408475) B21408475
theorem B9391787 : Blo 1853628 9391787 := bstep (se 1 (by rfl) ⟨7043840, by rfl⟩ : syracuseStep 9391787 = 14087681) B14087681
theorem B60157673 : Blo 1853628 60157673 := bstep (se 2 (by rfl) ⟨22559127, by rfl⟩ : syracuseStep 60157673 = 45118255) B45118255
theorem B1855323 : Blo 1853628 1855323 := bstep (se 1 (by rfl) ⟨1391492, by rfl⟩ : syracuseStep 1855323 = 2782985) B2782985
theorem B9392111 : Blo 1853628 9392111 := bstep (se 1 (by rfl) ⟨7044083, by rfl⟩ : syracuseStep 9392111 = 14088167) B14088167
theorem B4174073 : Blo 1853628 4174073 := bstep (se 2 (by rfl) ⟨1565277, by rfl⟩ : syracuseStep 4174073 = 3130555) B3130555
theorem B2781851 : Blo 1853628 2781851 := bstep (se 1 (by rfl) ⟨2086388, by rfl⟩ : syracuseStep 2781851 = 4172777) B4172777
theorem B2781929 : Blo 1853628 2781929 := bstep (se 2 (by rfl) ⟨1043223, by rfl⟩ : syracuseStep 2781929 = 2086447) B2086447
theorem B2347967 : Blo 1853628 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B21124961 : Blo 1853628 21124961 := bstep (se 2 (by rfl) ⟨7921860, by rfl⟩ : syracuseStep 21124961 = 15843721) B15843721
theorem B3757927 : Blo 1853628 3757927 := bstep (se 1 (by rfl) ⟨2818445, by rfl⟩ : syracuseStep 3757927 = 5636891) B5636891
theorem B36132799 : Blo 1853628 36132799 := bstep (se 1 (by rfl) ⟨27099599, by rfl⟩ : syracuseStep 36132799 = 54199199) B54199199
theorem B2783231 : Blo 1853628 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B4692127 : Blo 1853628 4692127 := bstep (se 1 (by rfl) ⟨3519095, by rfl⟩ : syracuseStep 4692127 = 7038191) B7038191
theorem B62659115 : Blo 1853628 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B5282471 : Blo 1853628 5282471 := bstep (se 1 (by rfl) ⟨3961853, by rfl⟩ : syracuseStep 5282471 = 7923707) B7923707
theorem B40098887 : Blo 1853628 40098887 := bstep (se 1 (by rfl) ⟨30074165, by rfl⟩ : syracuseStep 40098887 = 60148331) B60148331
theorem B7044509 : Blo 1853628 7044509 := bstep (se 3 (by rfl) ⟨1320845, by rfl⟩ : syracuseStep 7044509 = 2641691) B2641691
theorem B9387899 : Blo 1853628 9387899 := bstep (se 1 (by rfl) ⟨7040924, by rfl⟩ : syracuseStep 9387899 = 14081849) B14081849
theorem B47514761 : Blo 1853628 47514761 := bstep (se 2 (by rfl) ⟨17818035, by rfl⟩ : syracuseStep 47514761 = 35636071) B35636071
theorem B14083307 : Blo 1853628 14083307 := bstep (se 1 (by rfl) ⟨10562480, by rfl⟩ : syracuseStep 14083307 = 21124961) B21124961
theorem B41772743 : Blo 1853628 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B26732591 : Blo 1853628 26732591 := bstep (se 1 (by rfl) ⟨20049443, by rfl⟩ : syracuseStep 26732591 = 40098887) B40098887
theorem B4696339 : Blo 1853628 4696339 := bstep (se 1 (by rfl) ⟨3522254, by rfl⟩ : syracuseStep 4696339 = 7044509) B7044509
theorem B6261191 : Blo 1853628 6261191 := bstep (se 1 (by rfl) ⟨4695893, by rfl⟩ : syracuseStep 6261191 = 9391787) B9391787
theorem B6261245 : Blo 1853628 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B6261407 : Blo 1853628 6261407 := bstep (se 1 (by rfl) ⟨4696055, by rfl⟩ : syracuseStep 6261407 = 9392111) B9392111
theorem B1854567 : Blo 1853628 1854567 := bstep (se 1 (by rfl) ⟨1390925, by rfl⟩ : syracuseStep 1854567 = 2781851) B2781851
theorem B1854619 : Blo 1853628 1854619 := bstep (se 1 (by rfl) ⟨1390964, by rfl⟩ : syracuseStep 1854619 = 2781929) B2781929
theorem B1855487 : Blo 1853628 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B5010569 : Blo 1853628 5010569 := bstep (se 2 (by rfl) ⟨1878963, by rfl⟩ : syracuseStep 5010569 = 3757927) B3757927
theorem B40105115 : Blo 1853628 40105115 := bstep (se 1 (by rfl) ⟨30078836, by rfl⟩ : syracuseStep 40105115 = 60157673) B60157673
theorem B2782715 : Blo 1853628 2782715 := bstep (se 1 (by rfl) ⟨2087036, by rfl⟩ : syracuseStep 2782715 = 4174073) B4174073
theorem B6256169 : Blo 1853628 6256169 := bstep (se 2 (by rfl) ⟨2346063, by rfl⟩ : syracuseStep 6256169 = 4692127) B4692127
theorem B67680305 : Blo 1853628 67680305 := bstep (se 2 (by rfl) ⟨25380114, by rfl⟩ : syracuseStep 67680305 = 50760229) B50760229
theorem B3128105 : Blo 1853628 3128105 := bstep (se 2 (by rfl) ⟨1173039, by rfl⟩ : syracuseStep 3128105 = 2346079) B2346079
theorem B3521647 : Blo 1853628 3521647 := bstep (se 1 (by rfl) ⟨2641235, by rfl⟩ : syracuseStep 3521647 = 5282471) B5282471
theorem B19029755 : Blo 1853628 19029755 := bstep (se 1 (by rfl) ⟨14272316, by rfl⟩ : syracuseStep 19029755 = 28544633) B28544633
theorem B6258599 : Blo 1853628 6258599 := bstep (se 1 (by rfl) ⟨4693949, by rfl⟩ : syracuseStep 6258599 = 9387899) B9387899
theorem B48177065 : Blo 1853628 48177065 := bstep (se 2 (by rfl) ⟨18066399, by rfl⟩ : syracuseStep 48177065 = 36132799) B36132799
theorem B9388871 : Blo 1853628 9388871 := bstep (se 1 (by rfl) ⟨7041653, by rfl⟩ : syracuseStep 9388871 = 14083307) B14083307
theorem B4170779 : Blo 1853628 4170779 := bstep (se 1 (by rfl) ⟨3128084, by rfl⟩ : syracuseStep 4170779 = 6256169) B6256169
theorem B4695529 : Blo 1853628 4695529 := bstep (se 2 (by rfl) ⟨1760823, by rfl⟩ : syracuseStep 4695529 = 3521647) B3521647
theorem B4172399 : Blo 1853628 4172399 := bstep (se 1 (by rfl) ⟨3129299, by rfl⟩ : syracuseStep 4172399 = 6258599) B6258599
theorem B6261785 : Blo 1853628 6261785 := bstep (se 2 (by rfl) ⟨2348169, by rfl⟩ : syracuseStep 6261785 = 4696339) B4696339
theorem B1855143 : Blo 1853628 1855143 := bstep (se 1 (by rfl) ⟨1391357, by rfl⟩ : syracuseStep 1855143 = 2782715) B2782715
theorem B27848495 : Blo 1853628 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B17821727 : Blo 1853628 17821727 := bstep (se 1 (by rfl) ⟨13366295, by rfl⟩ : syracuseStep 17821727 = 26732591) B26732591
theorem B4174127 : Blo 1853628 4174127 := bstep (se 1 (by rfl) ⟨3130595, by rfl⟩ : syracuseStep 4174127 = 6261191) B6261191
theorem B4174163 : Blo 1853628 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B4174271 : Blo 1853628 4174271 := bstep (se 1 (by rfl) ⟨3130703, by rfl⟩ : syracuseStep 4174271 = 6261407) B6261407
theorem B2085403 : Blo 1853628 2085403 := bstep (se 1 (by rfl) ⟨1564052, by rfl⟩ : syracuseStep 2085403 = 3128105) B3128105
theorem B12686503 : Blo 1853628 12686503 := bstep (se 1 (by rfl) ⟨9514877, by rfl⟩ : syracuseStep 12686503 = 19029755) B19029755
theorem B32118043 : Blo 1853628 32118043 := bstep (se 1 (by rfl) ⟨24088532, by rfl⟩ : syracuseStep 32118043 = 48177065) B48177065
theorem B3340379 : Blo 1853628 3340379 := bstep (se 1 (by rfl) ⟨2505284, by rfl⟩ : syracuseStep 3340379 = 5010569) B5010569
theorem B31676507 : Blo 1853628 31676507 := bstep (se 1 (by rfl) ⟨23757380, by rfl⟩ : syracuseStep 31676507 = 47514761) B47514761
theorem B26736743 : Blo 1853628 26736743 := bstep (se 1 (by rfl) ⟨20052557, by rfl⟩ : syracuseStep 26736743 = 40105115) B40105115
theorem B45120203 : Blo 1853628 45120203 := bstep (se 1 (by rfl) ⟨33840152, by rfl⟩ : syracuseStep 45120203 = 67680305) B67680305
theorem B6259247 : Blo 1853628 6259247 := bstep (se 1 (by rfl) ⟨4694435, by rfl⟩ : syracuseStep 6259247 = 9388871) B9388871
theorem B6260705 : Blo 1853628 6260705 := bstep (se 2 (by rfl) ⟨2347764, by rfl⟩ : syracuseStep 6260705 = 4695529) B4695529
theorem B74262653 : Blo 1853628 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B11881151 : Blo 1853628 11881151 := bstep (se 1 (by rfl) ⟨8910863, by rfl⟩ : syracuseStep 11881151 = 17821727) B17821727
theorem B2780519 : Blo 1853628 2780519 := bstep (se 1 (by rfl) ⟨2085389, by rfl⟩ : syracuseStep 2780519 = 4170779) B4170779
theorem B2780537 : Blo 1853628 2780537 := bstep (se 2 (by rfl) ⟨1042701, by rfl⟩ : syracuseStep 2780537 = 2085403) B2085403
theorem B42824057 : Blo 1853628 42824057 := bstep (se 2 (by rfl) ⟨16059021, by rfl⟩ : syracuseStep 42824057 = 32118043) B32118043
theorem B2781599 : Blo 1853628 2781599 := bstep (se 1 (by rfl) ⟨2086199, by rfl⟩ : syracuseStep 2781599 = 4172399) B4172399
theorem B4174523 : Blo 1853628 4174523 := bstep (se 1 (by rfl) ⟨3130892, by rfl⟩ : syracuseStep 4174523 = 6261785) B6261785
theorem B2782751 : Blo 1853628 2782751 := bstep (se 1 (by rfl) ⟨2087063, by rfl⟩ : syracuseStep 2782751 = 4174127) B4174127
theorem B2782775 : Blo 1853628 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B2782847 : Blo 1853628 2782847 := bstep (se 1 (by rfl) ⟨2087135, by rfl⟩ : syracuseStep 2782847 = 4174271) B4174271
theorem B2226919 : Blo 1853628 2226919 := bstep (se 1 (by rfl) ⟨1670189, by rfl⟩ : syracuseStep 2226919 = 3340379) B3340379
theorem B21117671 : Blo 1853628 21117671 := bstep (se 1 (by rfl) ⟨15838253, by rfl⟩ : syracuseStep 21117671 = 31676507) B31676507
theorem B17824495 : Blo 1853628 17824495 := bstep (se 1 (by rfl) ⟨13368371, by rfl⟩ : syracuseStep 17824495 = 26736743) B26736743
theorem B16915337 : Blo 1853628 16915337 := bstep (se 2 (by rfl) ⟨6343251, by rfl⟩ : syracuseStep 16915337 = 12686503) B12686503
theorem B30080135 : Blo 1853628 30080135 := bstep (se 1 (by rfl) ⟨22560101, by rfl⟩ : syracuseStep 30080135 = 45120203) B45120203
theorem B23765993 : Blo 1853628 23765993 := bstep (se 2 (by rfl) ⟨8912247, by rfl⟩ : syracuseStep 23765993 = 17824495) B17824495
theorem B114197485 : Blo 1853628 114197485 := bstep (se 3 (by rfl) ⟨21412028, by rfl⟩ : syracuseStep 114197485 = 42824057) B42824057
theorem B1853679 : Blo 1853628 1853679 := bstep (se 1 (by rfl) ⟨1390259, by rfl⟩ : syracuseStep 1853679 = 2780519) B2780519
theorem B1853691 : Blo 1853628 1853691 := bstep (se 1 (by rfl) ⟨1390268, by rfl⟩ : syracuseStep 1853691 = 2780537) B2780537
theorem B1854399 : Blo 1853628 1854399 := bstep (se 1 (by rfl) ⟨1390799, by rfl⟩ : syracuseStep 1854399 = 2781599) B2781599
theorem B4172831 : Blo 1853628 4172831 := bstep (se 1 (by rfl) ⟨3129623, by rfl⟩ : syracuseStep 4172831 = 6259247) B6259247
theorem B2969225 : Blo 1853628 2969225 := bstep (se 2 (by rfl) ⟨1113459, by rfl⟩ : syracuseStep 2969225 = 2226919) B2226919
theorem B1855167 : Blo 1853628 1855167 := bstep (se 1 (by rfl) ⟨1391375, by rfl⟩ : syracuseStep 1855167 = 2782751) B2782751
theorem B1855183 : Blo 1853628 1855183 := bstep (se 1 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 1855183 = 2782775) B2782775
theorem B1855231 : Blo 1853628 1855231 := bstep (se 1 (by rfl) ⟨1391423, by rfl⟩ : syracuseStep 1855231 = 2782847) B2782847
theorem B4173803 : Blo 1853628 4173803 := bstep (se 1 (by rfl) ⟨3130352, by rfl⟩ : syracuseStep 4173803 = 6260705) B6260705
theorem B49508435 : Blo 1853628 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B14078447 : Blo 1853628 14078447 := bstep (se 1 (by rfl) ⟨10558835, by rfl⟩ : syracuseStep 14078447 = 21117671) B21117671
theorem B11276891 : Blo 1853628 11276891 := bstep (se 1 (by rfl) ⟨8457668, by rfl⟩ : syracuseStep 11276891 = 16915337) B16915337
theorem B2783015 : Blo 1853628 2783015 := bstep (se 1 (by rfl) ⟨2087261, by rfl⟩ : syracuseStep 2783015 = 4174523) B4174523
theorem B7920767 : Blo 1853628 7920767 := bstep (se 1 (by rfl) ⟨5940575, by rfl⟩ : syracuseStep 7920767 = 11881151) B11881151
theorem B20053423 : Blo 1853628 20053423 := bstep (se 1 (by rfl) ⟨15040067, by rfl⟩ : syracuseStep 20053423 = 30080135) B30080135
theorem B132022493 : Blo 1853628 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B15843995 : Blo 1853628 15843995 := bstep (se 1 (by rfl) ⟨11882996, by rfl⟩ : syracuseStep 15843995 = 23765993) B23765993
theorem B21122045 : Blo 1853628 21122045 := bstep (se 3 (by rfl) ⟨3960383, by rfl⟩ : syracuseStep 21122045 = 7920767) B7920767
theorem B1855343 : Blo 1853628 1855343 := bstep (se 1 (by rfl) ⟨1391507, by rfl⟩ : syracuseStep 1855343 = 2783015) B2783015
theorem B2781887 : Blo 1853628 2781887 := bstep (se 1 (by rfl) ⟨2086415, by rfl⟩ : syracuseStep 2781887 = 4172831) B4172831
theorem B1979483 : Blo 1853628 1979483 := bstep (se 1 (by rfl) ⟨1484612, by rfl⟩ : syracuseStep 1979483 = 2969225) B2969225
theorem B2782535 : Blo 1853628 2782535 := bstep (se 1 (by rfl) ⟨2086901, by rfl⟩ : syracuseStep 2782535 = 4173803) B4173803
theorem B9385631 : Blo 1853628 9385631 := bstep (se 1 (by rfl) ⟨7039223, by rfl⟩ : syracuseStep 9385631 = 14078447) B14078447
theorem B7517927 : Blo 1853628 7517927 := bstep (se 1 (by rfl) ⟨5638445, by rfl⟩ : syracuseStep 7517927 = 11276891) B11276891
theorem B152263313 : Blo 1853628 152263313 := bstep (se 2 (by rfl) ⟨57098742, by rfl⟩ : syracuseStep 152263313 = 114197485) B114197485
theorem B26737897 : Blo 1853628 26737897 := bstep (se 2 (by rfl) ⟨10026711, by rfl⟩ : syracuseStep 26737897 = 20053423) B20053423
theorem B88014995 : Blo 1853628 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B101508875 : Blo 1853628 101508875 := bstep (se 1 (by rfl) ⟨76131656, by rfl⟩ : syracuseStep 101508875 = 152263313) B152263313
theorem B5278621 : Blo 1853628 5278621 := bstep (se 3 (by rfl) ⟨989741, by rfl⟩ : syracuseStep 5278621 = 1979483) B1979483
theorem B10562663 : Blo 1853628 10562663 := bstep (se 1 (by rfl) ⟨7921997, by rfl⟩ : syracuseStep 10562663 = 15843995) B15843995
theorem B1854591 : Blo 1853628 1854591 := bstep (se 1 (by rfl) ⟨1390943, by rfl⟩ : syracuseStep 1854591 = 2781887) B2781887
theorem B1855023 : Blo 1853628 1855023 := bstep (se 1 (by rfl) ⟨1391267, by rfl⟩ : syracuseStep 1855023 = 2782535) B2782535
theorem B6257087 : Blo 1853628 6257087 := bstep (se 1 (by rfl) ⟨4692815, by rfl⟩ : syracuseStep 6257087 = 9385631) B9385631
theorem B5011951 : Blo 1853628 5011951 := bstep (se 1 (by rfl) ⟨3758963, by rfl⟩ : syracuseStep 5011951 = 7517927) B7517927
theorem B35650529 : Blo 1853628 35650529 := bstep (se 2 (by rfl) ⟨13368948, by rfl⟩ : syracuseStep 35650529 = 26737897) B26737897
theorem B14081363 : Blo 1853628 14081363 := bstep (se 1 (by rfl) ⟨10561022, by rfl⟩ : syracuseStep 14081363 = 21122045) B21122045
theorem B7038161 : Blo 1853628 7038161 := bstep (se 2 (by rfl) ⟨2639310, by rfl⟩ : syracuseStep 7038161 = 5278621) B5278621
theorem B4171391 : Blo 1853628 4171391 := bstep (se 1 (by rfl) ⟨3128543, by rfl⟩ : syracuseStep 4171391 = 6257087) B6257087
theorem B23767019 : Blo 1853628 23767019 := bstep (se 1 (by rfl) ⟨17825264, by rfl⟩ : syracuseStep 23767019 = 35650529) B35650529
theorem B7041775 : Blo 1853628 7041775 := bstep (se 1 (by rfl) ⟨5281331, by rfl⟩ : syracuseStep 7041775 = 10562663) B10562663
theorem B58676663 : Blo 1853628 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B6682601 : Blo 1853628 6682601 := bstep (se 2 (by rfl) ⟨2505975, by rfl⟩ : syracuseStep 6682601 = 5011951) B5011951
theorem B67672583 : Blo 1853628 67672583 := bstep (se 1 (by rfl) ⟨50754437, by rfl⟩ : syracuseStep 67672583 = 101508875) B101508875
theorem B9387575 : Blo 1853628 9387575 := bstep (se 1 (by rfl) ⟨7040681, by rfl⟩ : syracuseStep 9387575 = 14081363) B14081363
theorem B39117775 : Blo 1853628 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B9389033 : Blo 1853628 9389033 := bstep (se 2 (by rfl) ⟨3520887, by rfl⟩ : syracuseStep 9389033 = 7041775) B7041775
theorem B15844679 : Blo 1853628 15844679 := bstep (se 1 (by rfl) ⟨11883509, by rfl⟩ : syracuseStep 15844679 = 23767019) B23767019
theorem B45115055 : Blo 1853628 45115055 := bstep (se 1 (by rfl) ⟨33836291, by rfl⟩ : syracuseStep 45115055 = 67672583) B67672583
theorem B17820269 : Blo 1853628 17820269 := bstep (se 3 (by rfl) ⟨3341300, by rfl⟩ : syracuseStep 17820269 = 6682601) B6682601
theorem B2780927 : Blo 1853628 2780927 := bstep (se 1 (by rfl) ⟨2085695, by rfl⟩ : syracuseStep 2780927 = 4171391) B4171391
theorem B4692107 : Blo 1853628 4692107 := bstep (se 1 (by rfl) ⟨3519080, by rfl⟩ : syracuseStep 4692107 = 7038161) B7038161
theorem B6258383 : Blo 1853628 6258383 := bstep (se 1 (by rfl) ⟨4693787, by rfl⟩ : syracuseStep 6258383 = 9387575) B9387575
theorem B6259355 : Blo 1853628 6259355 := bstep (se 1 (by rfl) ⟨4694516, by rfl⟩ : syracuseStep 6259355 = 9389033) B9389033
theorem B11880179 : Blo 1853628 11880179 := bstep (se 1 (by rfl) ⟨8910134, by rfl⟩ : syracuseStep 11880179 = 17820269) B17820269
theorem B4172255 : Blo 1853628 4172255 := bstep (se 1 (by rfl) ⟨3129191, by rfl⟩ : syracuseStep 4172255 = 6258383) B6258383
theorem B1853951 : Blo 1853628 1853951 := bstep (se 1 (by rfl) ⟨1390463, by rfl⟩ : syracuseStep 1853951 = 2780927) B2780927
theorem B10563119 : Blo 1853628 10563119 := bstep (se 1 (by rfl) ⟨7922339, by rfl⟩ : syracuseStep 10563119 = 15844679) B15844679
theorem B30076703 : Blo 1853628 30076703 := bstep (se 1 (by rfl) ⟨22557527, by rfl⟩ : syracuseStep 30076703 = 45115055) B45115055
theorem B52157033 : Blo 1853628 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B3128071 : Blo 1853628 3128071 := bstep (se 1 (by rfl) ⟨2346053, by rfl⟩ : syracuseStep 3128071 = 4692107) B4692107
theorem B4170761 : Blo 1853628 4170761 := bstep (se 2 (by rfl) ⟨1564035, by rfl⟩ : syracuseStep 4170761 = 3128071) B3128071
theorem B4172903 : Blo 1853628 4172903 := bstep (se 1 (by rfl) ⟨3129677, by rfl⟩ : syracuseStep 4172903 = 6259355) B6259355
theorem B2781503 : Blo 1853628 2781503 := bstep (se 1 (by rfl) ⟨2086127, by rfl⟩ : syracuseStep 2781503 = 4172255) B4172255
theorem B34771355 : Blo 1853628 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B7042079 : Blo 1853628 7042079 := bstep (se 1 (by rfl) ⟨5281559, by rfl⟩ : syracuseStep 7042079 = 10563119) B10563119
theorem B20051135 : Blo 1853628 20051135 := bstep (se 1 (by rfl) ⟨15038351, by rfl⟩ : syracuseStep 20051135 = 30076703) B30076703
theorem B7920119 : Blo 1853628 7920119 := bstep (se 1 (by rfl) ⟨5940089, by rfl⟩ : syracuseStep 7920119 = 11880179) B11880179
theorem B4694719 : Blo 1853628 4694719 := bstep (se 1 (by rfl) ⟨3521039, by rfl⟩ : syracuseStep 4694719 = 7042079) B7042079
theorem B1854335 : Blo 1853628 1854335 := bstep (se 1 (by rfl) ⟨1390751, by rfl⟩ : syracuseStep 1854335 = 2781503) B2781503
theorem B2780507 : Blo 1853628 2780507 := bstep (se 1 (by rfl) ⟨2085380, by rfl⟩ : syracuseStep 2780507 = 4170761) B4170761
theorem B5280079 : Blo 1853628 5280079 := bstep (se 1 (by rfl) ⟨3960059, by rfl⟩ : syracuseStep 5280079 = 7920119) B7920119
theorem B2781935 : Blo 1853628 2781935 := bstep (se 1 (by rfl) ⟨2086451, by rfl⟩ : syracuseStep 2781935 = 4172903) B4172903
theorem B23180903 : Blo 1853628 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B13367423 : Blo 1853628 13367423 := bstep (se 1 (by rfl) ⟨10025567, by rfl⟩ : syracuseStep 13367423 = 20051135) B20051135
theorem B6259625 : Blo 1853628 6259625 := bstep (se 2 (by rfl) ⟨2347359, by rfl⟩ : syracuseStep 6259625 = 4694719) B4694719
theorem B1853671 : Blo 1853628 1853671 := bstep (se 1 (by rfl) ⟨1390253, by rfl⟩ : syracuseStep 1853671 = 2780507) B2780507
theorem B7040105 : Blo 1853628 7040105 := bstep (se 2 (by rfl) ⟨2640039, by rfl⟩ : syracuseStep 7040105 = 5280079) B5280079
theorem B1854623 : Blo 1853628 1854623 := bstep (se 1 (by rfl) ⟨1390967, by rfl⟩ : syracuseStep 1854623 = 2781935) B2781935
theorem B15453935 : Blo 1853628 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B8911615 : Blo 1853628 8911615 := bstep (se 1 (by rfl) ⟨6683711, by rfl⟩ : syracuseStep 8911615 = 13367423) B13367423
theorem B4173083 : Blo 1853628 4173083 := bstep (se 1 (by rfl) ⟨3129812, by rfl⟩ : syracuseStep 4173083 = 6259625) B6259625
theorem B11882153 : Blo 1853628 11882153 := bstep (se 2 (by rfl) ⟨4455807, by rfl⟩ : syracuseStep 11882153 = 8911615) B8911615
theorem B10302623 : Blo 1853628 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B4693403 : Blo 1853628 4693403 := bstep (se 1 (by rfl) ⟨3520052, by rfl⟩ : syracuseStep 4693403 = 7040105) B7040105
theorem B6868415 : Blo 1853628 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B2782055 : Blo 1853628 2782055 := bstep (se 1 (by rfl) ⟨2086541, by rfl⟩ : syracuseStep 2782055 = 4173083) B4173083
theorem B3128935 : Blo 1853628 3128935 := bstep (se 1 (by rfl) ⟨2346701, by rfl⟩ : syracuseStep 3128935 = 4693403) B4693403
theorem B7921435 : Blo 1853628 7921435 := bstep (se 1 (by rfl) ⟨5941076, by rfl⟩ : syracuseStep 7921435 = 11882153) B11882153
theorem B4171913 : Blo 1853628 4171913 := bstep (se 2 (by rfl) ⟨1564467, by rfl⟩ : syracuseStep 4171913 = 3128935) B3128935
theorem B10561913 : Blo 1853628 10561913 := bstep (se 2 (by rfl) ⟨3960717, by rfl⟩ : syracuseStep 10561913 = 7921435) B7921435
theorem B1854703 : Blo 1853628 1854703 := bstep (se 1 (by rfl) ⟨1391027, by rfl⟩ : syracuseStep 1854703 = 2782055) B2782055
theorem B18315773 : Blo 1853628 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B2781275 : Blo 1853628 2781275 := bstep (se 1 (by rfl) ⟨2085956, by rfl⟩ : syracuseStep 2781275 = 4171913) B4171913
theorem B7041275 : Blo 1853628 7041275 := bstep (se 1 (by rfl) ⟨5280956, by rfl⟩ : syracuseStep 7041275 = 10561913) B10561913
theorem B12210515 : Blo 1853628 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B4694183 : Blo 1853628 4694183 := bstep (se 1 (by rfl) ⟨3520637, by rfl⟩ : syracuseStep 4694183 = 7041275) B7041275
theorem B1854183 : Blo 1853628 1854183 := bstep (se 1 (by rfl) ⟨1390637, by rfl⟩ : syracuseStep 1854183 = 2781275) B2781275
theorem B8140343 : Blo 1853628 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B3129455 : Blo 1853628 3129455 := bstep (se 1 (by rfl) ⟨2347091, by rfl⟩ : syracuseStep 3129455 = 4694183) B4694183
theorem B86830325 : Blo 1853628 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B57886883 : Blo 1853628 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B2086303 : Blo 1853628 2086303 := bstep (se 1 (by rfl) ⟨1564727, by rfl⟩ : syracuseStep 2086303 = 3129455) B3129455
theorem B2781737 : Blo 1853628 2781737 := bstep (se 2 (by rfl) ⟨1043151, by rfl⟩ : syracuseStep 2781737 = 2086303) B2086303
theorem B38591255 : Blo 1853628 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B1854491 : Blo 1853628 1854491 := bstep (se 1 (by rfl) ⟨1390868, by rfl⟩ : syracuseStep 1854491 = 2781737) B2781737
theorem B25727503 : Blo 1853628 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B34303337 : Blo 1853628 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B22868891 : Blo 1853628 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B15245927 : Blo 1853628 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B10163951 : Blo 1853628 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B6775967 : Blo 1853628 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B18069245 : Blo 1853628 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B12046163 : Blo 1853628 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B32123101 : Blo 1853628 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B42830801 : Blo 1853628 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B28553867 : Blo 1853628 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B19035911 : Blo 1853628 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B12690607 : Blo 1853628 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B16920809 : Blo 1853628 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B11280539 : Blo 1853628 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B7520359 : Blo 1853628 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B10027145 : Blo 1853628 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B6684763 : Blo 1853628 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B8913017 : Blo 1853628 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B5942011 : Blo 1853628 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B7922681 : Blo 1853628 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B5281787 : Blo 1853628 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B14084765 : Blo 1853628 14084765 := bstep (se 3 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 14084765 = 5281787) B5281787
theorem B9389843 : Blo 1853628 9389843 := bstep (se 1 (by rfl) ⟨7042382, by rfl⟩ : syracuseStep 9389843 = 14084765) B14084765
theorem B6259895 : Blo 1853628 6259895 := bstep (se 1 (by rfl) ⟨4694921, by rfl⟩ : syracuseStep 6259895 = 9389843) B9389843
theorem B4173263 : Blo 1853628 4173263 := bstep (se 1 (by rfl) ⟨3129947, by rfl⟩ : syracuseStep 4173263 = 6259895) B6259895
theorem B2782175 : Blo 1853628 2782175 := bstep (se 1 (by rfl) ⟨2086631, by rfl⟩ : syracuseStep 2782175 = 4173263) B4173263
theorem B1854783 : Blo 1853628 1854783 := bstep (se 1 (by rfl) ⟨1391087, by rfl⟩ : syracuseStep 1854783 = 2782175) B2782175

theorem C0 (j : ℕ) (h1 : 463407 ≤ j) (h2 : j ≤ 463906) : Blo 1853628 (4 * j + 3) := by
  interval_cases j
  · exact B1853631
  · exact B1853635
  · exact B1853639
  · exact B1853643
  · exact B1853647
  · exact B1853651
  · exact B1853655
  · exact B1853659
  · exact B1853663
  · exact B1853667
  · exact B1853671
  · exact B1853675
  · exact B1853679
  · exact B1853683
  · exact B1853687
  · exact B1853691
  · exact B1853695
  · exact B1853699
  · exact B1853703
  · exact B1853707
  · exact B1853711
  · exact B1853715
  · exact B1853719
  · exact B1853723
  · exact B1853727
  · exact B1853731
  · exact B1853735
  · exact B1853739
  · exact B1853743
  · exact B1853747
  · exact B1853751
  · exact B1853755
  · exact B1853759
  · exact B1853763
  · exact B1853767
  · exact B1853771
  · exact B1853775
  · exact B1853779
  · exact B1853783
  · exact B1853787
  · exact B1853791
  · exact B1853795
  · exact B1853799
  · exact B1853803
  · exact B1853807
  · exact B1853811
  · exact B1853815
  · exact B1853819
  · exact B1853823
  · exact B1853827
  · exact B1853831
  · exact B1853835
  · exact B1853839
  · exact B1853843
  · exact B1853847
  · exact B1853851
  · exact B1853855
  · exact B1853859
  · exact B1853863
  · exact B1853867
  · exact B1853871
  · exact B1853875
  · exact B1853879
  · exact B1853883
  · exact B1853887
  · exact B1853891
  · exact B1853895
  · exact B1853899
  · exact B1853903
  · exact B1853907
  · exact B1853911
  · exact B1853915
  · exact B1853919
  · exact B1853923
  · exact B1853927
  · exact B1853931
  · exact B1853935
  · exact B1853939
  · exact B1853943
  · exact B1853947
  · exact B1853951
  · exact B1853955
  · exact B1853959
  · exact B1853963
  · exact B1853967
  · exact B1853971
  · exact B1853975
  · exact B1853979
  · exact B1853983
  · exact B1853987
  · exact B1853991
  · exact B1853995
  · exact B1853999
  · exact B1854003
  · exact B1854007
  · exact B1854011
  · exact B1854015
  · exact B1854019
  · exact B1854023
  · exact B1854027
  · exact B1854031
  · exact B1854035
  · exact B1854039
  · exact B1854043
  · exact B1854047
  · exact B1854051
  · exact B1854055
  · exact B1854059
  · exact B1854063
  · exact B1854067
  · exact B1854071
  · exact B1854075
  · exact B1854079
  · exact B1854083
  · exact B1854087
  · exact B1854091
  · exact B1854095
  · exact B1854099
  · exact B1854103
  · exact B1854107
  · exact B1854111
  · exact B1854115
  · exact B1854119
  · exact B1854123
  · exact B1854127
  · exact B1854131
  · exact B1854135
  · exact B1854139
  · exact B1854143
  · exact B1854147
  · exact B1854151
  · exact B1854155
  · exact B1854159
  · exact B1854163
  · exact B1854167
  · exact B1854171
  · exact B1854175
  · exact B1854179
  · exact B1854183
  · exact B1854187
  · exact B1854191
  · exact B1854195
  · exact B1854199
  · exact B1854203
  · exact B1854207
  · exact B1854211
  · exact B1854215
  · exact B1854219
  · exact B1854223
  · exact B1854227
  · exact B1854231
  · exact B1854235
  · exact B1854239
  · exact B1854243
  · exact B1854247
  · exact B1854251
  · exact B1854255
  · exact B1854259
  · exact B1854263
  · exact B1854267
  · exact B1854271
  · exact B1854275
  · exact B1854279
  · exact B1854283
  · exact B1854287
  · exact B1854291
  · exact B1854295
  · exact B1854299
  · exact B1854303
  · exact B1854307
  · exact B1854311
  · exact B1854315
  · exact B1854319
  · exact B1854323
  · exact B1854327
  · exact B1854331
  · exact B1854335
  · exact B1854339
  · exact B1854343
  · exact B1854347
  · exact B1854351
  · exact B1854355
  · exact B1854359
  · exact B1854363
  · exact B1854367
  · exact B1854371
  · exact B1854375
  · exact B1854379
  · exact B1854383
  · exact B1854387
  · exact B1854391
  · exact B1854395
  · exact B1854399
  · exact B1854403
  · exact B1854407
  · exact B1854411
  · exact B1854415
  · exact B1854419
  · exact B1854423
  · exact B1854427
  · exact B1854431
  · exact B1854435
  · exact B1854439
  · exact B1854443
  · exact B1854447
  · exact B1854451
  · exact B1854455
  · exact B1854459
  · exact B1854463
  · exact B1854467
  · exact B1854471
  · exact B1854475
  · exact B1854479
  · exact B1854483
  · exact B1854487
  · exact B1854491
  · exact B1854495
  · exact B1854499
  · exact B1854503
  · exact B1854507
  · exact B1854511
  · exact B1854515
  · exact B1854519
  · exact B1854523
  · exact B1854527
  · exact B1854531
  · exact B1854535
  · exact B1854539
  · exact B1854543
  · exact B1854547
  · exact B1854551
  · exact B1854555
  · exact B1854559
  · exact B1854563
  · exact B1854567
  · exact B1854571
  · exact B1854575
  · exact B1854579
  · exact B1854583
  · exact B1854587
  · exact B1854591
  · exact B1854595
  · exact B1854599
  · exact B1854603
  · exact B1854607
  · exact B1854611
  · exact B1854615
  · exact B1854619
  · exact B1854623
  · exact B1854627
  · exact B1854631
  · exact B1854635
  · exact B1854639
  · exact B1854643
  · exact B1854647
  · exact B1854651
  · exact B1854655
  · exact B1854659
  · exact B1854663
  · exact B1854667
  · exact B1854671
  · exact B1854675
  · exact B1854679
  · exact B1854683
  · exact B1854687
  · exact B1854691
  · exact B1854695
  · exact B1854699
  · exact B1854703
  · exact B1854707
  · exact B1854711
  · exact B1854715
  · exact B1854719
  · exact B1854723
  · exact B1854727
  · exact B1854731
  · exact B1854735
  · exact B1854739
  · exact B1854743
  · exact B1854747
  · exact B1854751
  · exact B1854755
  · exact B1854759
  · exact B1854763
  · exact B1854767
  · exact B1854771
  · exact B1854775
  · exact B1854779
  · exact B1854783
  · exact B1854787
  · exact B1854791
  · exact B1854795
  · exact B1854799
  · exact B1854803
  · exact B1854807
  · exact B1854811
  · exact B1854815
  · exact B1854819
  · exact B1854823
  · exact B1854827
  · exact B1854831
  · exact B1854835
  · exact B1854839
  · exact B1854843
  · exact B1854847
  · exact B1854851
  · exact B1854855
  · exact B1854859
  · exact B1854863
  · exact B1854867
  · exact B1854871
  · exact B1854875
  · exact B1854879
  · exact B1854883
  · exact B1854887
  · exact B1854891
  · exact B1854895
  · exact B1854899
  · exact B1854903
  · exact B1854907
  · exact B1854911
  · exact B1854915
  · exact B1854919
  · exact B1854923
  · exact B1854927
  · exact B1854931
  · exact B1854935
  · exact B1854939
  · exact B1854943
  · exact B1854947
  · exact B1854951
  · exact B1854955
  · exact B1854959
  · exact B1854963
  · exact B1854967
  · exact B1854971
  · exact B1854975
  · exact B1854979
  · exact B1854983
  · exact B1854987
  · exact B1854991
  · exact B1854995
  · exact B1854999
  · exact B1855003
  · exact B1855007
  · exact B1855011
  · exact B1855015
  · exact B1855019
  · exact B1855023
  · exact B1855027
  · exact B1855031
  · exact B1855035
  · exact B1855039
  · exact B1855043
  · exact B1855047
  · exact B1855051
  · exact B1855055
  · exact B1855059
  · exact B1855063
  · exact B1855067
  · exact B1855071
  · exact B1855075
  · exact B1855079
  · exact B1855083
  · exact B1855087
  · exact B1855091
  · exact B1855095
  · exact B1855099
  · exact B1855103
  · exact B1855107
  · exact B1855111
  · exact B1855115
  · exact B1855119
  · exact B1855123
  · exact B1855127
  · exact B1855131
  · exact B1855135
  · exact B1855139
  · exact B1855143
  · exact B1855147
  · exact B1855151
  · exact B1855155
  · exact B1855159
  · exact B1855163
  · exact B1855167
  · exact B1855171
  · exact B1855175
  · exact B1855179
  · exact B1855183
  · exact B1855187
  · exact B1855191
  · exact B1855195
  · exact B1855199
  · exact B1855203
  · exact B1855207
  · exact B1855211
  · exact B1855215
  · exact B1855219
  · exact B1855223
  · exact B1855227
  · exact B1855231
  · exact B1855235
  · exact B1855239
  · exact B1855243
  · exact B1855247
  · exact B1855251
  · exact B1855255
  · exact B1855259
  · exact B1855263
  · exact B1855267
  · exact B1855271
  · exact B1855275
  · exact B1855279
  · exact B1855283
  · exact B1855287
  · exact B1855291
  · exact B1855295
  · exact B1855299
  · exact B1855303
  · exact B1855307
  · exact B1855311
  · exact B1855315
  · exact B1855319
  · exact B1855323
  · exact B1855327
  · exact B1855331
  · exact B1855335
  · exact B1855339
  · exact B1855343
  · exact B1855347
  · exact B1855351
  · exact B1855355
  · exact B1855359
  · exact B1855363
  · exact B1855367
  · exact B1855371
  · exact B1855375
  · exact B1855379
  · exact B1855383
  · exact B1855387
  · exact B1855391
  · exact B1855395
  · exact B1855399
  · exact B1855403
  · exact B1855407
  · exact B1855411
  · exact B1855415
  · exact B1855419
  · exact B1855423
  · exact B1855427
  · exact B1855431
  · exact B1855435
  · exact B1855439
  · exact B1855443
  · exact B1855447
  · exact B1855451
  · exact B1855455
  · exact B1855459
  · exact B1855463
  · exact B1855467
  · exact B1855471
  · exact B1855475
  · exact B1855479
  · exact B1855483
  · exact B1855487
  · exact B1855491
  · exact B1855495
  · exact B1855499
  · exact B1855503
  · exact B1855507
  · exact B1855511
  · exact B1855515
  · exact B1855519
  · exact B1855523
  · exact B1855527
  · exact B1855531
  · exact B1855535
  · exact B1855539
  · exact B1855543
  · exact B1855547
  · exact B1855551
  · exact B1855555
  · exact B1855559
  · exact B1855563
  · exact B1855567
  · exact B1855571
  · exact B1855575
  · exact B1855579
  · exact B1855583
  · exact B1855587
  · exact B1855591
  · exact B1855595
  · exact B1855599
  · exact B1855603
  · exact B1855607
  · exact B1855611
  · exact B1855615
  · exact B1855619
  · exact B1855623
  · exact B1855627

theorem solution (m : ℕ) (hlo : 1853628 ≤ m) (hhi : m ≤ 1855628) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 463407 ≤ j := by omega
    have hj2 : j ≤ 463906 := by omega
    have hb : Blo 1853628 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
