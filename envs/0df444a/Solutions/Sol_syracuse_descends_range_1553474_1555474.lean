-- Prove2me | solution 1 for syracuse_descends_range_1553474_1555474
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:52.018085+00:00
-- url     : https://prove2.me/submissions/b6ff1250-0b24-4eb4-aff8-63d3a030f5d8

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


theorem B3498029 : Blo 1553474 3498029 := bbase (se 3 (by rfl) ⟨655880, by rfl⟩ : syracuseStep 3498029 = 1311761) (by norm_num)
theorem B1966133 : Blo 1553474 1966133 := bbase (se 5 (by rfl) ⟨92162, by rfl⟩ : syracuseStep 1966133 = 184325) (by norm_num)
theorem B1966189 : Blo 1553474 1966189 := bbase (se 3 (by rfl) ⟨368660, by rfl⟩ : syracuseStep 1966189 = 737321) (by norm_num)
theorem B3498101 : Blo 1553474 3498101 := bbase (se 5 (by rfl) ⟨163973, by rfl⟩ : syracuseStep 3498101 = 327947) (by norm_num)
theorem B7471237 : Blo 1553474 7471237 := bbase (se 4 (by rfl) ⟨700428, by rfl⟩ : syracuseStep 7471237 = 1400857) (by norm_num)
theorem B2621605 : Blo 1553474 2621605 := bbase (se 4 (by rfl) ⟨245775, by rfl⟩ : syracuseStep 2621605 = 491551) (by norm_num)
theorem B3498173 : Blo 1553474 3498173 := bbase (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) (by norm_num)
theorem B1966285 : Blo 1553474 1966285 := bbase (se 3 (by rfl) ⟨368678, by rfl⟩ : syracuseStep 1966285 = 737357) (by norm_num)
theorem B3735773 : Blo 1553474 3735773 := bbase (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) (by norm_num)
theorem B5603573 : Blo 1553474 5603573 := bbase (se 5 (by rfl) ⟨262667, by rfl⟩ : syracuseStep 5603573 = 525335) (by norm_num)
theorem B3318013 : Blo 1553474 3318013 := bbase (se 3 (by rfl) ⟨622127, by rfl⟩ : syracuseStep 3318013 = 1244255) (by norm_num)
theorem B2621693 : Blo 1553474 2621693 := bbase (se 3 (by rfl) ⟨491567, by rfl⟩ : syracuseStep 2621693 = 983135) (by norm_num)
theorem B3498245 : Blo 1553474 3498245 := bbase (se 4 (by rfl) ⟨327960, by rfl⟩ : syracuseStep 3498245 = 655921) (by norm_num)
theorem B7864613 : Blo 1553474 7864613 := bbase (se 4 (by rfl) ⟨737307, by rfl⟩ : syracuseStep 7864613 = 1474615) (by norm_num)
theorem B3498317 : Blo 1553474 3498317 := bbase (se 3 (by rfl) ⟨655934, by rfl⟩ : syracuseStep 3498317 = 1311869) (by norm_num)
theorem B3932509 : Blo 1553474 3932509 := bbase (se 3 (by rfl) ⟨737345, by rfl⟩ : syracuseStep 3932509 = 1474691) (by norm_num)
theorem B5243237 : Blo 1553474 5243237 := bbase (se 4 (by rfl) ⟨491553, by rfl⟩ : syracuseStep 5243237 = 983107) (by norm_num)
theorem B1966457 : Blo 1553474 1966457 := bbase (se 2 (by rfl) ⟨737421, by rfl⟩ : syracuseStep 1966457 = 1474843) (by norm_num)
theorem B2621821 : Blo 1553474 2621821 := bbase (se 3 (by rfl) ⟨491591, by rfl⟩ : syracuseStep 2621821 = 983183) (by norm_num)
theorem B3547525 : Blo 1553474 3547525 := bbase (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) (by norm_num)
theorem B3498389 : Blo 1553474 3498389 := bbase (se 6 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 3498389 = 163987) (by norm_num)
theorem B2490797 : Blo 1553474 2490797 := bbase (se 3 (by rfl) ⟨467024, by rfl⟩ : syracuseStep 2490797 = 934049) (by norm_num)
theorem B1966513 : Blo 1553474 1966513 := bbase (se 2 (by rfl) ⟨737442, by rfl⟩ : syracuseStep 1966513 = 1474885) (by norm_num)
theorem B3932621 : Blo 1553474 3932621 := bbase (se 3 (by rfl) ⟨737366, by rfl⟩ : syracuseStep 3932621 = 1474733) (by norm_num)
theorem B2621909 : Blo 1553474 2621909 := bbase (se 7 (by rfl) ⟨30725, by rfl⟩ : syracuseStep 2621909 = 61451) (by norm_num)
theorem B3498461 : Blo 1553474 3498461 := bbase (se 3 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 3498461 = 1311923) (by norm_num)
theorem B4424165 : Blo 1553474 4424165 := bbase (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) (by norm_num)
theorem B8856053 : Blo 1553474 8856053 := bbase (se 5 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 8856053 = 830255) (by norm_num)
theorem B1966609 : Blo 1553474 1966609 := bbase (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) (by norm_num)
theorem B2212373 : Blo 1553474 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B3498533 : Blo 1553474 3498533 := bbase (se 4 (by rfl) ⟨327987, by rfl⟩ : syracuseStep 3498533 = 655975) (by norm_num)
theorem B2949709 : Blo 1553474 2949709 := bbase (se 3 (by rfl) ⟨553070, by rfl⟩ : syracuseStep 2949709 = 1106141) (by norm_num)
theorem B2622037 : Blo 1553474 2622037 := bbase (se 8 (by rfl) ⟨15363, by rfl⟩ : syracuseStep 2622037 = 30727) (by norm_num)
theorem B3498605 : Blo 1553474 3498605 := bbase (se 3 (by rfl) ⟨655988, by rfl⟩ : syracuseStep 3498605 = 1311977) (by norm_num)
theorem B3932813 : Blo 1553474 3932813 := bbase (se 3 (by rfl) ⟨737402, by rfl⟩ : syracuseStep 3932813 = 1474805) (by norm_num)
theorem B5604005 : Blo 1553474 5604005 := bbase (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) (by norm_num)
theorem B2622125 : Blo 1553474 2622125 := bbase (se 3 (by rfl) ⟨491648, by rfl⟩ : syracuseStep 2622125 = 983297) (by norm_num)
theorem B3498677 : Blo 1553474 3498677 := bbase (se 5 (by rfl) ⟨164000, by rfl⟩ : syracuseStep 3498677 = 328001) (by norm_num)
theorem B1966781 : Blo 1553474 1966781 := bbase (se 3 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 1966781 = 737543) (by norm_num)
theorem B2949853 : Blo 1553474 2949853 := bbase (se 3 (by rfl) ⟨553097, by rfl⟩ : syracuseStep 2949853 = 1106195) (by norm_num)
theorem B1966837 : Blo 1553474 1966837 := bbase (se 5 (by rfl) ⟨92195, by rfl⟩ : syracuseStep 1966837 = 184391) (by norm_num)
theorem B3498749 : Blo 1553474 3498749 := bbase (se 3 (by rfl) ⟨656015, by rfl⟩ : syracuseStep 3498749 = 1312031) (by norm_num)
theorem B3990269 : Blo 1553474 3990269 := bbase (se 3 (by rfl) ⟨748175, by rfl⟩ : syracuseStep 3990269 = 1496351) (by norm_num)
theorem B5243669 : Blo 1553474 5243669 := bbase (se 6 (by rfl) ⟨122898, by rfl⟩ : syracuseStep 5243669 = 245797) (by norm_num)
theorem B2622253 : Blo 1553474 2622253 := bbase (se 3 (by rfl) ⟨491672, by rfl⟩ : syracuseStep 2622253 = 983345) (by norm_num)
theorem B5055301 : Blo 1553474 5055301 := bbase (se 4 (by rfl) ⟨473934, by rfl⟩ : syracuseStep 5055301 = 947869) (by norm_num)
theorem B3498821 : Blo 1553474 3498821 := bbase (se 4 (by rfl) ⟨328014, by rfl⟩ : syracuseStep 3498821 = 656029) (by norm_num)
theorem B1868617 : Blo 1553474 1868617 := bbase (se 2 (by rfl) ⟨700731, by rfl⟩ : syracuseStep 1868617 = 1401463) (by norm_num)
theorem B1966933 : Blo 1553474 1966933 := bbase (se 9 (by rfl) ⟨5762, by rfl⟩ : syracuseStep 1966933 = 11525) (by norm_num)
theorem B2950013 : Blo 1553474 2950013 := bbase (se 3 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 2950013 = 1106255) (by norm_num)
theorem B2622341 : Blo 1553474 2622341 := bbase (se 4 (by rfl) ⟨245844, by rfl⟩ : syracuseStep 2622341 = 491689) (by norm_num)
theorem B3498893 : Blo 1553474 3498893 := bbase (se 3 (by rfl) ⟨656042, by rfl⟩ : syracuseStep 3498893 = 1312085) (by norm_num)
theorem B6636437 : Blo 1553474 6636437 := bbase (se 6 (by rfl) ⟨155541, by rfl⟩ : syracuseStep 6636437 = 311083) (by norm_num)
theorem B5899189 : Blo 1553474 5899189 := bbase (se 5 (by rfl) ⟨276524, by rfl⟩ : syracuseStep 5899189 = 553049) (by norm_num)
theorem B2802637 : Blo 1553474 2802637 := bbase (se 3 (by rfl) ⟨525494, by rfl⟩ : syracuseStep 2802637 = 1050989) (by norm_num)
theorem B3498965 : Blo 1553474 3498965 := bbase (se 7 (by rfl) ⟨41003, by rfl⟩ : syracuseStep 3498965 = 82007) (by norm_num)
theorem B3736541 : Blo 1553474 3736541 := bbase (se 3 (by rfl) ⟨700601, by rfl⟩ : syracuseStep 3736541 = 1401203) (by norm_num)
theorem B3933157 : Blo 1553474 3933157 := bbase (se 4 (by rfl) ⟨368733, by rfl⟩ : syracuseStep 3933157 = 737467) (by norm_num)
theorem B1967105 : Blo 1553474 1967105 := bbase (se 2 (by rfl) ⟨737664, by rfl⟩ : syracuseStep 1967105 = 1475329) (by norm_num)
theorem B2622469 : Blo 1553474 2622469 := bbase (se 4 (by rfl) ⟨245856, by rfl⟩ : syracuseStep 2622469 = 491713) (by norm_num)
theorem B2950157 : Blo 1553474 2950157 := bbase (se 3 (by rfl) ⟨553154, by rfl⟩ : syracuseStep 2950157 = 1106309) (by norm_num)
theorem B2802709 : Blo 1553474 2802709 := bbase (se 6 (by rfl) ⟨65688, by rfl⟩ : syracuseStep 2802709 = 131377) (by norm_num)
theorem B3499037 : Blo 1553474 3499037 := bbase (se 3 (by rfl) ⟨656069, by rfl⟩ : syracuseStep 3499037 = 1312139) (by norm_num)
theorem B1967161 : Blo 1553474 1967161 := bbase (se 2 (by rfl) ⟨737685, by rfl⟩ : syracuseStep 1967161 = 1475371) (by norm_num)
theorem B2212925 : Blo 1553474 2212925 := bbase (se 3 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 2212925 = 829847) (by norm_num)
theorem B3933269 : Blo 1553474 3933269 := bbase (se 8 (by rfl) ⟨23046, by rfl⟩ : syracuseStep 3933269 = 46093) (by norm_num)
theorem B2622557 : Blo 1553474 2622557 := bbase (se 3 (by rfl) ⟨491729, by rfl⟩ : syracuseStep 2622557 = 983459) (by norm_num)
theorem B3499109 : Blo 1553474 3499109 := bbase (se 4 (by rfl) ⟨328041, by rfl⟩ : syracuseStep 3499109 = 656083) (by norm_num)
theorem B7873685 : Blo 1553474 7873685 := bbase (se 6 (by rfl) ⟨184539, by rfl⟩ : syracuseStep 7873685 = 369079) (by norm_num)
theorem B1967257 : Blo 1553474 1967257 := bbase (se 2 (by rfl) ⟨737721, by rfl⟩ : syracuseStep 1967257 = 1475443) (by norm_num)
theorem B3499181 : Blo 1553474 3499181 := bbase (se 3 (by rfl) ⟨656096, by rfl⟩ : syracuseStep 3499181 = 1312193) (by norm_num)
theorem B6636725 : Blo 1553474 6636725 := bbase (se 5 (by rfl) ⟨311096, by rfl⟩ : syracuseStep 6636725 = 622193) (by norm_num)
theorem B5244101 : Blo 1553474 5244101 := bbase (se 4 (by rfl) ⟨491634, by rfl⟩ : syracuseStep 5244101 = 983269) (by norm_num)
theorem B2622685 : Blo 1553474 2622685 := bbase (se 3 (by rfl) ⟨491753, by rfl⟩ : syracuseStep 2622685 = 983507) (by norm_num)
theorem B5899493 : Blo 1553474 5899493 := bbase (se 4 (by rfl) ⟨553077, by rfl⟩ : syracuseStep 5899493 = 1106155) (by norm_num)
theorem B5604581 : Blo 1553474 5604581 := bbase (se 4 (by rfl) ⟨525429, by rfl⟩ : syracuseStep 5604581 = 1050859) (by norm_num)
theorem B3499253 : Blo 1553474 3499253 := bbase (se 5 (by rfl) ⟨164027, by rfl⟩ : syracuseStep 3499253 = 328055) (by norm_num)
theorem B3933461 : Blo 1553474 3933461 := bbase (se 6 (by rfl) ⟨92190, by rfl⟩ : syracuseStep 3933461 = 184381) (by norm_num)
theorem B1893665 : Blo 1553474 1893665 := bbase (se 2 (by rfl) ⟨710124, by rfl⟩ : syracuseStep 1893665 = 1420249) (by norm_num)
theorem B2950445 : Blo 1553474 2950445 := bbase (se 3 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 2950445 = 1106417) (by norm_num)
theorem B2622773 : Blo 1553474 2622773 := bbase (se 5 (by rfl) ⟨122942, by rfl⟩ : syracuseStep 2622773 = 245885) (by norm_num)
theorem B3499325 : Blo 1553474 3499325 := bbase (se 3 (by rfl) ⟨656123, by rfl⟩ : syracuseStep 3499325 = 1312247) (by norm_num)
theorem B1967429 : Blo 1553474 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B9954677 : Blo 1553474 9954677 := bbase (se 5 (by rfl) ⟨466625, by rfl⟩ : syracuseStep 9954677 = 933251) (by norm_num)
theorem B1967485 : Blo 1553474 1967485 := bbase (se 3 (by rfl) ⟨368903, by rfl⟩ : syracuseStep 1967485 = 737807) (by norm_num)
theorem B3499397 : Blo 1553474 3499397 := bbase (se 4 (by rfl) ⟨328068, by rfl⟩ : syracuseStep 3499397 = 656137) (by norm_num)
theorem B2336141 : Blo 1553474 2336141 := bbase (se 3 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 2336141 = 876053) (by norm_num)
theorem B7185829 : Blo 1553474 7185829 := bbase (se 4 (by rfl) ⟨673671, by rfl⟩ : syracuseStep 7185829 = 1347343) (by norm_num)
theorem B2622901 : Blo 1553474 2622901 := bbase (se 5 (by rfl) ⟨122948, by rfl⟩ : syracuseStep 2622901 = 245897) (by norm_num)
theorem B2950597 : Blo 1553474 2950597 := bbase (se 4 (by rfl) ⟨276618, by rfl⟩ : syracuseStep 2950597 = 553237) (by norm_num)
theorem B3499469 : Blo 1553474 3499469 := bbase (se 3 (by rfl) ⟨656150, by rfl⟩ : syracuseStep 3499469 = 1312301) (by norm_num)
theorem B1967581 : Blo 1553474 1967581 := bbase (se 3 (by rfl) ⟨368921, by rfl⟩ : syracuseStep 1967581 = 737843) (by norm_num)
theorem B2622989 : Blo 1553474 2622989 := bbase (se 3 (by rfl) ⟨491810, by rfl⟩ : syracuseStep 2622989 = 983621) (by norm_num)
theorem B3499541 : Blo 1553474 3499541 := bbase (se 6 (by rfl) ⟨82020, by rfl⟩ : syracuseStep 3499541 = 164041) (by norm_num)
theorem B7865909 : Blo 1553474 7865909 := bbase (se 5 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 7865909 = 737429) (by norm_num)
theorem B3499613 : Blo 1553474 3499613 := bbase (se 3 (by rfl) ⟨656177, by rfl⟩ : syracuseStep 3499613 = 1312355) (by norm_num)
theorem B3933805 : Blo 1553474 3933805 := bbase (se 3 (by rfl) ⟨737588, by rfl⟩ : syracuseStep 3933805 = 1475177) (by norm_num)
theorem B5244533 : Blo 1553474 5244533 := bbase (se 5 (by rfl) ⟨245837, by rfl⟩ : syracuseStep 5244533 = 491675) (by norm_num)
theorem B4425349 : Blo 1553474 4425349 := bbase (se 4 (by rfl) ⟨414876, by rfl⟩ : syracuseStep 4425349 = 829753) (by norm_num)
theorem B1967753 : Blo 1553474 1967753 := bbase (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) (by norm_num)
theorem B2623117 : Blo 1553474 2623117 := bbase (se 3 (by rfl) ⟨491834, by rfl⟩ : syracuseStep 2623117 = 983669) (by norm_num)
theorem B3499685 : Blo 1553474 3499685 := bbase (se 4 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 3499685 = 656191) (by norm_num)
theorem B1967809 : Blo 1553474 1967809 := bbase (se 2 (by rfl) ⟨737928, by rfl⟩ : syracuseStep 1967809 = 1475857) (by norm_num)
theorem B3933917 : Blo 1553474 3933917 := bbase (se 3 (by rfl) ⟨737609, by rfl⟩ : syracuseStep 3933917 = 1475219) (by norm_num)
theorem B3319517 : Blo 1553474 3319517 := bbase (se 3 (by rfl) ⟨622409, by rfl⟩ : syracuseStep 3319517 = 1244819) (by norm_num)
theorem B2623205 : Blo 1553474 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B3499757 : Blo 1553474 3499757 := bbase (se 3 (by rfl) ⟨656204, by rfl⟩ : syracuseStep 3499757 = 1312409) (by norm_num)
theorem B2950901 : Blo 1553474 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B1967905 : Blo 1553474 1967905 := bbase (se 2 (by rfl) ⟨737964, by rfl⟩ : syracuseStep 1967905 = 1475929) (by norm_num)
theorem B4425509 : Blo 1553474 4425509 := bbase (se 4 (by rfl) ⟨414891, by rfl⟩ : syracuseStep 4425509 = 829783) (by norm_num)
theorem B2213677 : Blo 1553474 2213677 := bbase (se 3 (by rfl) ⟨415064, by rfl⟩ : syracuseStep 2213677 = 830129) (by norm_num)
theorem B2623333 : Blo 1553474 2623333 := bbase (se 4 (by rfl) ⟨245937, by rfl⟩ : syracuseStep 2623333 = 491875) (by norm_num)
theorem B3319661 : Blo 1553474 3319661 := bbase (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) (by norm_num)
theorem B1574797 : Blo 1553474 1574797 := bbase (se 3 (by rfl) ⟨295274, by rfl⟩ : syracuseStep 1574797 = 590549) (by norm_num)
theorem B8398741 : Blo 1553474 8398741 := bbase (se 6 (by rfl) ⟨196845, by rfl⟩ : syracuseStep 8398741 = 393691) (by norm_num)
theorem B3934109 : Blo 1553474 3934109 := bbase (se 3 (by rfl) ⟨737645, by rfl⟩ : syracuseStep 3934109 = 1475291) (by norm_num)
theorem B6637477 : Blo 1553474 6637477 := bbase (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) (by norm_num)
theorem B2623421 : Blo 1553474 2623421 := bbase (se 3 (by rfl) ⟨491891, by rfl⟩ : syracuseStep 2623421 = 983783) (by norm_num)
theorem B5048261 : Blo 1553474 5048261 := bbase (se 4 (by rfl) ⟨473274, by rfl⟩ : syracuseStep 5048261 = 946549) (by norm_num)
theorem B1968077 : Blo 1553474 1968077 := bbase (se 3 (by rfl) ⟨369014, by rfl⟩ : syracuseStep 1968077 = 738029) (by norm_num)
theorem B1968133 : Blo 1553474 1968133 := bbase (se 4 (by rfl) ⟨184512, by rfl⟩ : syracuseStep 1968133 = 369025) (by norm_num)
theorem B4425749 : Blo 1553474 4425749 := bbase (se 6 (by rfl) ⟨103728, by rfl⟩ : syracuseStep 4425749 = 207457) (by norm_num)
theorem B5244965 : Blo 1553474 5244965 := bbase (se 4 (by rfl) ⟨491715, by rfl⟩ : syracuseStep 5244965 = 983431) (by norm_num)
theorem B2623549 : Blo 1553474 2623549 := bbase (se 3 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 2623549 = 983831) (by norm_num)
theorem B1968229 : Blo 1553474 1968229 := bbase (se 4 (by rfl) ⟨184521, by rfl⟩ : syracuseStep 1968229 = 369043) (by norm_num)
theorem B2623637 : Blo 1553474 2623637 := bbase (se 6 (by rfl) ⟨61491, by rfl⟩ : syracuseStep 2623637 = 122983) (by norm_num)
theorem B1575073 : Blo 1553474 1575073 := bbase (se 2 (by rfl) ⟨590652, by rfl⟩ : syracuseStep 1575073 = 1181305) (by norm_num)
theorem B1575121 : Blo 1553474 1575121 := bbase (se 2 (by rfl) ⟨590670, by rfl⟩ : syracuseStep 1575121 = 1181341) (by norm_num)
theorem B4425941 : Blo 1553474 4425941 := bbase (se 7 (by rfl) ⟨51866, by rfl⟩ : syracuseStep 4425941 = 103733) (by norm_num)
theorem B3320021 : Blo 1553474 3320021 := bbase (se 7 (by rfl) ⟨38906, by rfl⟩ : syracuseStep 3320021 = 77813) (by norm_num)
theorem B3934453 : Blo 1553474 3934453 := bbase (se 5 (by rfl) ⟨184427, by rfl⟩ : syracuseStep 3934453 = 368855) (by norm_num)
theorem B4983029 : Blo 1553474 4983029 := bbase (se 5 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 4983029 = 467159) (by norm_num)
theorem B1968401 : Blo 1553474 1968401 := bbase (se 2 (by rfl) ⟨738150, by rfl⟩ : syracuseStep 1968401 = 1476301) (by norm_num)
theorem B2623765 : Blo 1553474 2623765 := bbase (se 6 (by rfl) ⟨61494, by rfl⟩ : syracuseStep 2623765 = 122989) (by norm_num)
theorem B1968457 : Blo 1553474 1968457 := bbase (se 2 (by rfl) ⟨738171, by rfl⟩ : syracuseStep 1968457 = 1476343) (by norm_num)
theorem B3934565 : Blo 1553474 3934565 := bbase (se 4 (by rfl) ⟨368865, by rfl⟩ : syracuseStep 3934565 = 737731) (by norm_num)
theorem B2623853 : Blo 1553474 2623853 := bbase (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) (by norm_num)
theorem B2099621 : Blo 1553474 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B1968553 : Blo 1553474 1968553 := bbase (se 2 (by rfl) ⟨738207, by rfl⟩ : syracuseStep 1968553 = 1476415) (by norm_num)
theorem B2992565 : Blo 1553474 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B5245397 : Blo 1553474 5245397 := bbase (se 7 (by rfl) ⟨61469, by rfl⟩ : syracuseStep 5245397 = 122939) (by norm_num)
theorem B2951653 : Blo 1553474 2951653 := bbase (se 4 (by rfl) ⟨276717, by rfl⟩ : syracuseStep 2951653 = 553435) (by norm_num)
theorem B2623981 : Blo 1553474 2623981 := bbase (se 3 (by rfl) ⟨491996, by rfl⟩ : syracuseStep 2623981 = 983993) (by norm_num)
theorem B28355093 : Blo 1553474 28355093 := bbase (se 6 (by rfl) ⟨664572, by rfl⟩ : syracuseStep 28355093 = 1329145) (by norm_num)
theorem B1681957 : Blo 1553474 1681957 := bbase (se 4 (by rfl) ⟨157683, by rfl⟩ : syracuseStep 1681957 = 315367) (by norm_num)
theorem B3934757 : Blo 1553474 3934757 := bbase (se 4 (by rfl) ⟨368883, by rfl⟩ : syracuseStep 3934757 = 737767) (by norm_num)
theorem B8399413 : Blo 1553474 8399413 := bbase (se 5 (by rfl) ⟨393722, by rfl⟩ : syracuseStep 8399413 = 787445) (by norm_num)
theorem B2099773 : Blo 1553474 2099773 := bbase (se 3 (by rfl) ⟨393707, by rfl⟩ : syracuseStep 2099773 = 787415) (by norm_num)
theorem B2624069 : Blo 1553474 2624069 := bbase (se 4 (by rfl) ⟨246006, by rfl⟩ : syracuseStep 2624069 = 492013) (by norm_num)
theorem B2214469 : Blo 1553474 2214469 := bbase (se 4 (by rfl) ⟨207606, by rfl⟩ : syracuseStep 2214469 = 415213) (by norm_num)
theorem B1681993 : Blo 1553474 1681993 := bbase (se 2 (by rfl) ⟨630747, by rfl⟩ : syracuseStep 1681993 = 1261495) (by norm_num)
theorem B2951797 : Blo 1553474 2951797 := bbase (se 5 (by rfl) ⟨138365, by rfl⟩ : syracuseStep 2951797 = 276731) (by norm_num)
theorem B6638213 : Blo 1553474 6638213 := bbase (se 4 (by rfl) ⟨622332, by rfl⟩ : syracuseStep 6638213 = 1244665) (by norm_num)
theorem B5319317 : Blo 1553474 5319317 := bbase (se 6 (by rfl) ⟨124671, by rfl⟩ : syracuseStep 5319317 = 249343) (by norm_num)
theorem B8858261 : Blo 1553474 8858261 := bbase (se 6 (by rfl) ⟨207615, by rfl⟩ : syracuseStep 8858261 = 415231) (by norm_num)
theorem B2624197 : Blo 1553474 2624197 := bbase (se 4 (by rfl) ⟨246018, by rfl⟩ : syracuseStep 2624197 = 492037) (by norm_num)
theorem B1747669 : Blo 1553474 1747669 := bbase (se 7 (by rfl) ⟨20480, by rfl⟩ : syracuseStep 1747669 = 40961) (by norm_num)
theorem B1747705 : Blo 1553474 1747705 := bbase (se 2 (by rfl) ⟨655389, by rfl⟩ : syracuseStep 1747705 = 1310779) (by norm_num)
theorem B2951957 : Blo 1553474 2951957 := bbase (se 6 (by rfl) ⟨69186, by rfl⟩ : syracuseStep 2951957 = 138373) (by norm_num)
theorem B1747741 : Blo 1553474 1747741 := bbase (se 3 (by rfl) ⟨327701, by rfl⟩ : syracuseStep 1747741 = 655403) (by norm_num)
theorem B2624285 : Blo 1553474 2624285 := bbase (se 3 (by rfl) ⟨492053, by rfl⟩ : syracuseStep 2624285 = 984107) (by norm_num)
theorem B1747777 : Blo 1553474 1747777 := bbase (se 2 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 1747777 = 1310833) (by norm_num)
theorem B7867205 : Blo 1553474 7867205 := bbase (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) (by norm_num)
theorem B1747813 : Blo 1553474 1747813 := bbase (se 4 (by rfl) ⟨163857, by rfl⟩ : syracuseStep 1747813 = 327715) (by norm_num)
theorem B3935101 : Blo 1553474 3935101 := bbase (se 3 (by rfl) ⟨737831, by rfl⟩ : syracuseStep 3935101 = 1475663) (by norm_num)
theorem B5245829 : Blo 1553474 5245829 := bbase (se 4 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 5245829 = 983593) (by norm_num)
theorem B1747849 : Blo 1553474 1747849 := bbase (se 2 (by rfl) ⟨655443, by rfl⟩ : syracuseStep 1747849 = 1310887) (by norm_num)
theorem B2624413 : Blo 1553474 2624413 := bbase (se 3 (by rfl) ⟨492077, by rfl⟩ : syracuseStep 2624413 = 984155) (by norm_num)
theorem B2952101 : Blo 1553474 2952101 := bbase (se 4 (by rfl) ⟨276759, by rfl⟩ : syracuseStep 2952101 = 553519) (by norm_num)
theorem B1747885 : Blo 1553474 1747885 := bbase (se 3 (by rfl) ⟨327728, by rfl⟩ : syracuseStep 1747885 = 655457) (by norm_num)
theorem B1747921 : Blo 1553474 1747921 := bbase (se 2 (by rfl) ⟨655470, by rfl⟩ : syracuseStep 1747921 = 1310941) (by norm_num)
theorem B2100205 : Blo 1553474 2100205 := bbase (se 3 (by rfl) ⟨393788, by rfl⟩ : syracuseStep 2100205 = 787577) (by norm_num)
theorem B3935213 : Blo 1553474 3935213 := bbase (se 3 (by rfl) ⟨737852, by rfl⟩ : syracuseStep 3935213 = 1475705) (by norm_num)
theorem B1747957 : Blo 1553474 1747957 := bbase (se 5 (by rfl) ⟨81935, by rfl⟩ : syracuseStep 1747957 = 163871) (by norm_num)
theorem B2624501 : Blo 1553474 2624501 := bbase (se 5 (by rfl) ⟨123023, by rfl⟩ : syracuseStep 2624501 = 246047) (by norm_num)
theorem B1747993 : Blo 1553474 1747993 := bbase (se 2 (by rfl) ⟨655497, by rfl⟩ : syracuseStep 1747993 = 1310995) (by norm_num)
theorem B1748029 : Blo 1553474 1748029 := bbase (se 3 (by rfl) ⟨327755, by rfl⟩ : syracuseStep 1748029 = 655511) (by norm_num)
theorem B3320909 : Blo 1553474 3320909 := bbase (se 3 (by rfl) ⟨622670, by rfl⟩ : syracuseStep 3320909 = 1245341) (by norm_num)
theorem B1748065 : Blo 1553474 1748065 := bbase (se 2 (by rfl) ⟨655524, by rfl⟩ : syracuseStep 1748065 = 1311049) (by norm_num)
theorem B15961205 : Blo 1553474 15961205 := bbase (se 5 (by rfl) ⟨748181, by rfl⟩ : syracuseStep 15961205 = 1496363) (by norm_num)
theorem B2624629 : Blo 1553474 2624629 := bbase (se 5 (by rfl) ⟨123029, by rfl⟩ : syracuseStep 2624629 = 246059) (by norm_num)
theorem B1748101 : Blo 1553474 1748101 := bbase (se 4 (by rfl) ⟨163884, by rfl⟩ : syracuseStep 1748101 = 327769) (by norm_num)
theorem B1993877 : Blo 1553474 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B1748137 : Blo 1553474 1748137 := bbase (se 2 (by rfl) ⟨655551, by rfl⟩ : syracuseStep 1748137 = 1311103) (by norm_num)
theorem B3935405 : Blo 1553474 3935405 := bbase (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) (by norm_num)
theorem B4426933 : Blo 1553474 4426933 := bbase (se 5 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 4426933 = 415025) (by norm_num)
theorem B2100421 : Blo 1553474 2100421 := bbase (se 4 (by rfl) ⟨196914, by rfl⟩ : syracuseStep 2100421 = 393829) (by norm_num)
theorem B2952389 : Blo 1553474 2952389 := bbase (se 4 (by rfl) ⟨276786, by rfl⟩ : syracuseStep 2952389 = 553573) (by norm_num)
theorem B1748173 : Blo 1553474 1748173 := bbase (se 3 (by rfl) ⟨327782, by rfl⟩ : syracuseStep 1748173 = 655565) (by norm_num)
theorem B2624717 : Blo 1553474 2624717 := bbase (se 3 (by rfl) ⟨492134, by rfl⟩ : syracuseStep 2624717 = 984269) (by norm_num)
theorem B1748209 : Blo 1553474 1748209 := bbase (se 2 (by rfl) ⟨655578, by rfl⟩ : syracuseStep 1748209 = 1311157) (by norm_num)
theorem B1748245 : Blo 1553474 1748245 := bbase (se 6 (by rfl) ⟨40974, by rfl⟩ : syracuseStep 1748245 = 81949) (by norm_num)
theorem B5901605 : Blo 1553474 5901605 := bbase (se 4 (by rfl) ⟨553275, by rfl⟩ : syracuseStep 5901605 = 1106551) (by norm_num)
theorem B5246261 : Blo 1553474 5246261 := bbase (se 5 (by rfl) ⟨245918, by rfl⟩ : syracuseStep 5246261 = 491837) (by norm_num)
theorem B1748281 : Blo 1553474 1748281 := bbase (se 2 (by rfl) ⟨655605, by rfl⟩ : syracuseStep 1748281 = 1311211) (by norm_num)
theorem B3321157 : Blo 1553474 3321157 := bbase (se 4 (by rfl) ⟨311358, by rfl⟩ : syracuseStep 3321157 = 622717) (by norm_num)
theorem B1576265 : Blo 1553474 1576265 := bbase (se 2 (by rfl) ⟨591099, by rfl⟩ : syracuseStep 1576265 = 1182199) (by norm_num)
theorem B2624845 : Blo 1553474 2624845 := bbase (se 3 (by rfl) ⟨492158, by rfl⟩ : syracuseStep 2624845 = 984317) (by norm_num)
theorem B1748317 : Blo 1553474 1748317 := bbase (se 3 (by rfl) ⟨327809, by rfl⟩ : syracuseStep 1748317 = 655619) (by norm_num)
theorem B2952541 : Blo 1553474 2952541 := bbase (se 3 (by rfl) ⟨553601, by rfl⟩ : syracuseStep 2952541 = 1107203) (by norm_num)
theorem B7466357 : Blo 1553474 7466357 := bbase (se 5 (by rfl) ⟨349985, by rfl⟩ : syracuseStep 7466357 = 699971) (by norm_num)
theorem B1748353 : Blo 1553474 1748353 := bbase (se 2 (by rfl) ⟨655632, by rfl⟩ : syracuseStep 1748353 = 1311265) (by norm_num)
theorem B2837909 : Blo 1553474 2837909 := bbase (se 6 (by rfl) ⟨66513, by rfl⟩ : syracuseStep 2837909 = 133027) (by norm_num)
theorem B1748389 : Blo 1553474 1748389 := bbase (se 4 (by rfl) ⟨163911, by rfl⟩ : syracuseStep 1748389 = 327823) (by norm_num)
theorem B1748425 : Blo 1553474 1748425 := bbase (se 2 (by rfl) ⟨655659, by rfl⟩ : syracuseStep 1748425 = 1311319) (by norm_num)
theorem B1748461 : Blo 1553474 1748461 := bbase (se 3 (by rfl) ⟨327836, by rfl⟩ : syracuseStep 1748461 = 655673) (by norm_num)
theorem B1994233 : Blo 1553474 1994233 := bbase (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) (by norm_num)
theorem B3935749 : Blo 1553474 3935749 := bbase (se 4 (by rfl) ⟨368976, by rfl⟩ : syracuseStep 3935749 = 737953) (by norm_num)
theorem B1748497 : Blo 1553474 1748497 := bbase (se 2 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 1748497 = 1311373) (by norm_num)
theorem B1748533 : Blo 1553474 1748533 := bbase (se 5 (by rfl) ⟨81962, by rfl⟩ : syracuseStep 1748533 = 163925) (by norm_num)
theorem B5901893 : Blo 1553474 5901893 := bbase (se 4 (by rfl) ⟨553302, by rfl⟩ : syracuseStep 5901893 = 1106605) (by norm_num)
theorem B6475349 : Blo 1553474 6475349 := bbase (se 8 (by rfl) ⟨37941, by rfl⟩ : syracuseStep 6475349 = 75883) (by norm_num)
theorem B11808341 : Blo 1553474 11808341 := bbase (se 8 (by rfl) ⟨69189, by rfl⟩ : syracuseStep 11808341 = 138379) (by norm_num)
theorem B1748569 : Blo 1553474 1748569 := bbase (se 2 (by rfl) ⟨655713, by rfl⟩ : syracuseStep 1748569 = 1311427) (by norm_num)
theorem B2330213 : Blo 1553474 2330213 := bbase (se 4 (by rfl) ⟨218457, by rfl⟩ : syracuseStep 2330213 = 436915) (by norm_num)
theorem B3935861 : Blo 1553474 3935861 := bbase (se 5 (by rfl) ⟨184493, by rfl⟩ : syracuseStep 3935861 = 368987) (by norm_num)
theorem B2330237 : Blo 1553474 2330237 := bbase (se 3 (by rfl) ⟨436919, by rfl⟩ : syracuseStep 2330237 = 873839) (by norm_num)
theorem B1748605 : Blo 1553474 1748605 := bbase (se 3 (by rfl) ⟨327863, by rfl⟩ : syracuseStep 1748605 = 655727) (by norm_num)
theorem B2952845 : Blo 1553474 2952845 := bbase (se 3 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 2952845 = 1107317) (by norm_num)
theorem B2330261 : Blo 1553474 2330261 := bbase (se 6 (by rfl) ⟨54615, by rfl⟩ : syracuseStep 2330261 = 109231) (by norm_num)
theorem B1748641 : Blo 1553474 1748641 := bbase (se 2 (by rfl) ⟨655740, by rfl⟩ : syracuseStep 1748641 = 1311481) (by norm_num)
theorem B2330285 : Blo 1553474 2330285 := bbase (se 3 (by rfl) ⟨436928, by rfl⟩ : syracuseStep 2330285 = 873857) (by norm_num)
theorem B2330309 : Blo 1553474 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B1748677 : Blo 1553474 1748677 := bbase (se 4 (by rfl) ⟨163938, by rfl⟩ : syracuseStep 1748677 = 327877) (by norm_num)
theorem B2330333 : Blo 1553474 2330333 := bbase (se 3 (by rfl) ⟨436937, by rfl⟩ : syracuseStep 2330333 = 873875) (by norm_num)
theorem B2838245 : Blo 1553474 2838245 := bbase (se 4 (by rfl) ⟨266085, by rfl⟩ : syracuseStep 2838245 = 532171) (by norm_num)
theorem B5246693 : Blo 1553474 5246693 := bbase (se 4 (by rfl) ⟨491877, by rfl⟩ : syracuseStep 5246693 = 983755) (by norm_num)
theorem B1748713 : Blo 1553474 1748713 := bbase (se 2 (by rfl) ⟨655767, by rfl⟩ : syracuseStep 1748713 = 1311535) (by norm_num)
theorem B2330357 : Blo 1553474 2330357 := bbase (se 5 (by rfl) ⟨109235, by rfl⟩ : syracuseStep 2330357 = 218471) (by norm_num)
theorem B3837685 : Blo 1553474 3837685 := bbase (se 5 (by rfl) ⟨179891, by rfl⟩ : syracuseStep 3837685 = 359783) (by norm_num)
theorem B2330381 : Blo 1553474 2330381 := bbase (se 3 (by rfl) ⟨436946, by rfl⟩ : syracuseStep 2330381 = 873893) (by norm_num)
theorem B1748749 : Blo 1553474 1748749 := bbase (se 3 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 1748749 = 655781) (by norm_num)
theorem B2330405 : Blo 1553474 2330405 := bbase (se 4 (by rfl) ⟨218475, by rfl⟩ : syracuseStep 2330405 = 436951) (by norm_num)
theorem B2305837 : Blo 1553474 2305837 := bbase (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) (by norm_num)
theorem B1748785 : Blo 1553474 1748785 := bbase (se 2 (by rfl) ⟨655794, by rfl⟩ : syracuseStep 1748785 = 1311589) (by norm_num)
theorem B3936053 : Blo 1553474 3936053 := bbase (se 5 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 3936053 = 369005) (by norm_num)
theorem B2330429 : Blo 1553474 2330429 := bbase (se 3 (by rfl) ⟨436955, by rfl⟩ : syracuseStep 2330429 = 873911) (by norm_num)
theorem B3321661 : Blo 1553474 3321661 := bbase (se 3 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 3321661 = 1245623) (by norm_num)
theorem B5599045 : Blo 1553474 5599045 := bbase (se 4 (by rfl) ⟨524910, by rfl⟩ : syracuseStep 5599045 = 1049821) (by norm_num)
theorem B2330453 : Blo 1553474 2330453 := bbase (se 9 (by rfl) ⟨6827, by rfl⟩ : syracuseStep 2330453 = 13655) (by norm_num)
theorem B1748821 : Blo 1553474 1748821 := bbase (se 9 (by rfl) ⟨5123, by rfl⟩ : syracuseStep 1748821 = 10247) (by norm_num)
theorem B2330477 : Blo 1553474 2330477 := bbase (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) (by norm_num)
theorem B1748857 : Blo 1553474 1748857 := bbase (se 2 (by rfl) ⟨655821, by rfl⟩ : syracuseStep 1748857 = 1311643) (by norm_num)
theorem B2330501 : Blo 1553474 2330501 := bbase (se 4 (by rfl) ⟨218484, by rfl⟩ : syracuseStep 2330501 = 436969) (by norm_num)
theorem B2658197 : Blo 1553474 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2330525 : Blo 1553474 2330525 := bbase (se 3 (by rfl) ⟨436973, by rfl⟩ : syracuseStep 2330525 = 873947) (by norm_num)
theorem B1748893 : Blo 1553474 1748893 := bbase (se 3 (by rfl) ⟨327917, by rfl⟩ : syracuseStep 1748893 = 655835) (by norm_num)
theorem B2330549 : Blo 1553474 2330549 := bbase (se 5 (by rfl) ⟨109244, by rfl⟩ : syracuseStep 2330549 = 218489) (by norm_num)
theorem B1748929 : Blo 1553474 1748929 := bbase (se 2 (by rfl) ⟨655848, by rfl⟩ : syracuseStep 1748929 = 1311697) (by norm_num)
theorem B2330573 : Blo 1553474 2330573 := bbase (se 3 (by rfl) ⟨436982, by rfl⟩ : syracuseStep 2330573 = 873965) (by norm_num)
theorem B2330597 : Blo 1553474 2330597 := bbase (se 4 (by rfl) ⟨218493, by rfl⟩ : syracuseStep 2330597 = 436987) (by norm_num)
theorem B1748965 : Blo 1553474 1748965 := bbase (se 4 (by rfl) ⟨163965, by rfl⟩ : syracuseStep 1748965 = 327931) (by norm_num)
theorem B11800565 : Blo 1553474 11800565 := bbase (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) (by norm_num)
theorem B2330621 : Blo 1553474 2330621 := bbase (se 3 (by rfl) ⟨436991, by rfl⟩ : syracuseStep 2330621 = 873983) (by norm_num)
theorem B1749001 : Blo 1553474 1749001 := bbase (se 2 (by rfl) ⟨655875, by rfl⟩ : syracuseStep 1749001 = 1311751) (by norm_num)
theorem B2330645 : Blo 1553474 2330645 := bbase (se 6 (by rfl) ⟨54624, by rfl⟩ : syracuseStep 2330645 = 109249) (by norm_num)
theorem B2363413 : Blo 1553474 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B1658917 : Blo 1553474 1658917 := bbase (se 4 (by rfl) ⟨155523, by rfl⟩ : syracuseStep 1658917 = 311047) (by norm_num)
theorem B2330669 : Blo 1553474 2330669 := bbase (se 3 (by rfl) ⟨437000, by rfl⟩ : syracuseStep 2330669 = 874001) (by norm_num)
theorem B1749037 : Blo 1553474 1749037 := bbase (se 3 (by rfl) ⟨327944, by rfl⟩ : syracuseStep 1749037 = 655889) (by norm_num)
theorem B2330693 : Blo 1553474 2330693 := bbase (se 4 (by rfl) ⟨218502, by rfl⟩ : syracuseStep 2330693 = 437005) (by norm_num)
theorem B1749073 : Blo 1553474 1749073 := bbase (se 2 (by rfl) ⟨655902, by rfl⟩ : syracuseStep 1749073 = 1311805) (by norm_num)
theorem B7868501 : Blo 1553474 7868501 := bbase (se 8 (by rfl) ⟨46104, by rfl⟩ : syracuseStep 7868501 = 92209) (by norm_num)
theorem B2330717 : Blo 1553474 2330717 := bbase (se 3 (by rfl) ⟨437009, by rfl⟩ : syracuseStep 2330717 = 874019) (by norm_num)
theorem B2330741 : Blo 1553474 2330741 := bbase (se 5 (by rfl) ⟨109253, by rfl⟩ : syracuseStep 2330741 = 218507) (by norm_num)
theorem B2363509 : Blo 1553474 2363509 := bbase (se 5 (by rfl) ⟨110789, by rfl⟩ : syracuseStep 2363509 = 221579) (by norm_num)
theorem B1749109 : Blo 1553474 1749109 := bbase (se 5 (by rfl) ⟨81989, by rfl⟩ : syracuseStep 1749109 = 163979) (by norm_num)
theorem B2330765 : Blo 1553474 2330765 := bbase (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) (by norm_num)
theorem B3936397 : Blo 1553474 3936397 := bbase (se 3 (by rfl) ⟨738074, by rfl⟩ : syracuseStep 3936397 = 1476149) (by norm_num)
theorem B5247125 : Blo 1553474 5247125 := bbase (se 6 (by rfl) ⟨122979, by rfl⟩ : syracuseStep 5247125 = 245959) (by norm_num)
theorem B1749145 : Blo 1553474 1749145 := bbase (se 2 (by rfl) ⟨655929, by rfl⟩ : syracuseStep 1749145 = 1311859) (by norm_num)
theorem B2330789 : Blo 1553474 2330789 := bbase (se 4 (by rfl) ⟨218511, by rfl⟩ : syracuseStep 2330789 = 437023) (by norm_num)
theorem B9965749 : Blo 1553474 9965749 := bbase (se 5 (by rfl) ⟨467144, by rfl⟩ : syracuseStep 9965749 = 934289) (by norm_num)
theorem B2330813 : Blo 1553474 2330813 := bbase (se 3 (by rfl) ⟨437027, by rfl⟩ : syracuseStep 2330813 = 874055) (by norm_num)
theorem B1749181 : Blo 1553474 1749181 := bbase (se 3 (by rfl) ⟨327971, by rfl⟩ : syracuseStep 1749181 = 655943) (by norm_num)
theorem B2330837 : Blo 1553474 2330837 := bbase (se 7 (by rfl) ⟨27314, by rfl⟩ : syracuseStep 2330837 = 54629) (by norm_num)
theorem B1749217 : Blo 1553474 1749217 := bbase (se 2 (by rfl) ⟨655956, by rfl⟩ : syracuseStep 1749217 = 1311913) (by norm_num)
theorem B2330861 : Blo 1553474 2330861 := bbase (se 3 (by rfl) ⟨437036, by rfl⟩ : syracuseStep 2330861 = 874073) (by norm_num)
theorem B3936509 : Blo 1553474 3936509 := bbase (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) (by norm_num)
theorem B2330885 : Blo 1553474 2330885 := bbase (se 4 (by rfl) ⟨218520, by rfl⟩ : syracuseStep 2330885 = 437041) (by norm_num)
theorem B1749253 : Blo 1553474 1749253 := bbase (se 4 (by rfl) ⟨163992, by rfl⟩ : syracuseStep 1749253 = 327985) (by norm_num)
theorem B4428037 : Blo 1553474 4428037 := bbase (se 4 (by rfl) ⟨415128, by rfl⟩ : syracuseStep 4428037 = 830257) (by norm_num)
theorem B9957653 : Blo 1553474 9957653 := bbase (se 6 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 9957653 = 466765) (by norm_num)
theorem B2330909 : Blo 1553474 2330909 := bbase (se 3 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 2330909 = 874091) (by norm_num)
theorem B1749289 : Blo 1553474 1749289 := bbase (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) (by norm_num)
theorem B2330933 : Blo 1553474 2330933 := bbase (se 5 (by rfl) ⟨109262, by rfl⟩ : syracuseStep 2330933 = 218525) (by norm_num)
theorem B2363717 : Blo 1553474 2363717 := bbase (se 4 (by rfl) ⟨221598, by rfl⟩ : syracuseStep 2363717 = 443197) (by norm_num)
theorem B2330957 : Blo 1553474 2330957 := bbase (se 3 (by rfl) ⟨437054, by rfl⟩ : syracuseStep 2330957 = 874109) (by norm_num)
theorem B1749325 : Blo 1553474 1749325 := bbase (se 3 (by rfl) ⟨327998, by rfl⟩ : syracuseStep 1749325 = 655997) (by norm_num)
theorem B2330981 : Blo 1553474 2330981 := bbase (se 4 (by rfl) ⟨218529, by rfl⟩ : syracuseStep 2330981 = 437059) (by norm_num)
theorem B1749361 : Blo 1553474 1749361 := bbase (se 2 (by rfl) ⟨656010, by rfl⟩ : syracuseStep 1749361 = 1312021) (by norm_num)
theorem B2331005 : Blo 1553474 2331005 := bbase (se 3 (by rfl) ⟨437063, by rfl⟩ : syracuseStep 2331005 = 874127) (by norm_num)
theorem B2331029 : Blo 1553474 2331029 := bbase (se 6 (by rfl) ⟨54633, by rfl⟩ : syracuseStep 2331029 = 109267) (by norm_num)
theorem B10097045 : Blo 1553474 10097045 := bbase (se 6 (by rfl) ⟨236649, by rfl⟩ : syracuseStep 10097045 = 473299) (by norm_num)
theorem B1749397 : Blo 1553474 1749397 := bbase (se 6 (by rfl) ⟨41001, by rfl⟩ : syracuseStep 1749397 = 82003) (by norm_num)
theorem B2331053 : Blo 1553474 2331053 := bbase (se 3 (by rfl) ⟨437072, by rfl⟩ : syracuseStep 2331053 = 874145) (by norm_num)
theorem B1749433 : Blo 1553474 1749433 := bbase (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) (by norm_num)
theorem B3936701 : Blo 1553474 3936701 := bbase (se 3 (by rfl) ⟨738131, by rfl⟩ : syracuseStep 3936701 = 1476263) (by norm_num)
theorem B2331077 : Blo 1553474 2331077 := bbase (se 4 (by rfl) ⟨218538, by rfl⟩ : syracuseStep 2331077 = 437077) (by norm_num)
theorem B2331101 : Blo 1553474 2331101 := bbase (se 3 (by rfl) ⟨437081, by rfl⟩ : syracuseStep 2331101 = 874163) (by norm_num)
theorem B1749469 : Blo 1553474 1749469 := bbase (se 3 (by rfl) ⟨328025, by rfl⟩ : syracuseStep 1749469 = 656051) (by norm_num)
theorem B1659361 : Blo 1553474 1659361 := bbase (se 2 (by rfl) ⟨622260, by rfl⟩ : syracuseStep 1659361 = 1244521) (by norm_num)
theorem B2331125 : Blo 1553474 2331125 := bbase (se 5 (by rfl) ⟨109271, by rfl⟩ : syracuseStep 2331125 = 218543) (by norm_num)
theorem B1749505 : Blo 1553474 1749505 := bbase (se 2 (by rfl) ⟨656064, by rfl⟩ : syracuseStep 1749505 = 1312129) (by norm_num)
theorem B2331149 : Blo 1553474 2331149 := bbase (se 3 (by rfl) ⟨437090, by rfl⟩ : syracuseStep 2331149 = 874181) (by norm_num)
theorem B3985949 : Blo 1553474 3985949 := bbase (se 3 (by rfl) ⟨747365, by rfl⟩ : syracuseStep 3985949 = 1494731) (by norm_num)
theorem B2331173 : Blo 1553474 2331173 := bbase (se 4 (by rfl) ⟨218547, by rfl⟩ : syracuseStep 2331173 = 437095) (by norm_num)
theorem B1749541 : Blo 1553474 1749541 := bbase (se 4 (by rfl) ⟨164019, by rfl⟩ : syracuseStep 1749541 = 328039) (by norm_num)
theorem B2331197 : Blo 1553474 2331197 := bbase (se 3 (by rfl) ⟨437099, by rfl⟩ : syracuseStep 2331197 = 874199) (by norm_num)
theorem B5247557 : Blo 1553474 5247557 := bbase (se 4 (by rfl) ⟨491958, by rfl⟩ : syracuseStep 5247557 = 983917) (by norm_num)
theorem B1749577 : Blo 1553474 1749577 := bbase (se 2 (by rfl) ⟨656091, by rfl⟩ : syracuseStep 1749577 = 1312183) (by norm_num)
theorem B2331221 : Blo 1553474 2331221 := bbase (se 8 (by rfl) ⟨13659, by rfl⟩ : syracuseStep 2331221 = 27319) (by norm_num)
theorem B1659485 : Blo 1553474 1659485 := bbase (se 3 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 1659485 = 622307) (by norm_num)
theorem B2331245 : Blo 1553474 2331245 := bbase (se 3 (by rfl) ⟨437108, by rfl⟩ : syracuseStep 2331245 = 874217) (by norm_num)
theorem B1749613 : Blo 1553474 1749613 := bbase (se 3 (by rfl) ⟨328052, by rfl⟩ : syracuseStep 1749613 = 656105) (by norm_num)
theorem B2331269 : Blo 1553474 2331269 := bbase (se 4 (by rfl) ⟨218556, by rfl⟩ : syracuseStep 2331269 = 437113) (by norm_num)
theorem B1749649 : Blo 1553474 1749649 := bbase (se 2 (by rfl) ⟨656118, by rfl⟩ : syracuseStep 1749649 = 1312237) (by norm_num)
theorem B2331293 : Blo 1553474 2331293 := bbase (se 3 (by rfl) ⟨437117, by rfl⟩ : syracuseStep 2331293 = 874235) (by norm_num)
theorem B2331317 : Blo 1553474 2331317 := bbase (se 5 (by rfl) ⟨109280, by rfl⟩ : syracuseStep 2331317 = 218561) (by norm_num)
theorem B1749685 : Blo 1553474 1749685 := bbase (se 5 (by rfl) ⟨82016, by rfl⟩ : syracuseStep 1749685 = 164033) (by norm_num)
theorem B2331341 : Blo 1553474 2331341 := bbase (se 3 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 2331341 = 874253) (by norm_num)
theorem B1749721 : Blo 1553474 1749721 := bbase (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) (by norm_num)
theorem B2331365 : Blo 1553474 2331365 := bbase (se 4 (by rfl) ⟨218565, by rfl⟩ : syracuseStep 2331365 = 437131) (by norm_num)
theorem B5903077 : Blo 1553474 5903077 := bbase (se 4 (by rfl) ⟨553413, by rfl⟩ : syracuseStep 5903077 = 1106827) (by norm_num)
theorem B2331389 : Blo 1553474 2331389 := bbase (se 3 (by rfl) ⟨437135, by rfl⟩ : syracuseStep 2331389 = 874271) (by norm_num)
theorem B1749757 : Blo 1553474 1749757 := bbase (se 3 (by rfl) ⟨328079, by rfl⟩ : syracuseStep 1749757 = 656159) (by norm_num)
theorem B2659085 : Blo 1553474 2659085 := bbase (se 3 (by rfl) ⟨498578, by rfl⟩ : syracuseStep 2659085 = 997157) (by norm_num)
theorem B2331413 : Blo 1553474 2331413 := bbase (se 6 (by rfl) ⟨54642, by rfl⟩ : syracuseStep 2331413 = 109285) (by norm_num)
theorem B3937045 : Blo 1553474 3937045 := bbase (se 6 (by rfl) ⟨92274, by rfl⟩ : syracuseStep 3937045 = 184549) (by norm_num)
theorem B1749793 : Blo 1553474 1749793 := bbase (se 2 (by rfl) ⟨656172, by rfl⟩ : syracuseStep 1749793 = 1312345) (by norm_num)
theorem B2331437 : Blo 1553474 2331437 := bbase (se 3 (by rfl) ⟨437144, by rfl⟩ : syracuseStep 2331437 = 874289) (by norm_num)
theorem B2331461 : Blo 1553474 2331461 := bbase (se 4 (by rfl) ⟨218574, by rfl⟩ : syracuseStep 2331461 = 437149) (by norm_num)
theorem B1749829 : Blo 1553474 1749829 := bbase (se 4 (by rfl) ⟨164046, by rfl⟩ : syracuseStep 1749829 = 328093) (by norm_num)
theorem B1659737 : Blo 1553474 1659737 := bbase (se 2 (by rfl) ⟨622401, by rfl⟩ : syracuseStep 1659737 = 1244803) (by norm_num)
theorem B2331485 : Blo 1553474 2331485 := bbase (se 3 (by rfl) ⟨437153, by rfl⟩ : syracuseStep 2331485 = 874307) (by norm_num)
theorem B1749865 : Blo 1553474 1749865 := bbase (se 2 (by rfl) ⟨656199, by rfl⟩ : syracuseStep 1749865 = 1312399) (by norm_num)
theorem B2331509 : Blo 1553474 2331509 := bbase (se 5 (by rfl) ⟨109289, by rfl⟩ : syracuseStep 2331509 = 218579) (by norm_num)
theorem B3937157 : Blo 1553474 3937157 := bbase (se 4 (by rfl) ⟨369108, by rfl⟩ : syracuseStep 3937157 = 738217) (by norm_num)
theorem B2331533 : Blo 1553474 2331533 := bbase (se 3 (by rfl) ⟨437162, by rfl⟩ : syracuseStep 2331533 = 874325) (by norm_num)
theorem B1749901 : Blo 1553474 1749901 := bbase (se 3 (by rfl) ⟨328106, by rfl⟩ : syracuseStep 1749901 = 656213) (by norm_num)
theorem B2331557 : Blo 1553474 2331557 := bbase (se 4 (by rfl) ⟨218583, by rfl⟩ : syracuseStep 2331557 = 437167) (by norm_num)
theorem B2331581 : Blo 1553474 2331581 := bbase (se 3 (by rfl) ⟨437171, by rfl⟩ : syracuseStep 2331581 = 874343) (by norm_num)
theorem B2331605 : Blo 1553474 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B2331629 : Blo 1553474 2331629 := bbase (se 3 (by rfl) ⟨437180, by rfl⟩ : syracuseStep 2331629 = 874361) (by norm_num)
theorem B5247989 : Blo 1553474 5247989 := bbase (se 5 (by rfl) ⟨245999, by rfl⟩ : syracuseStep 5247989 = 491999) (by norm_num)
theorem B2331653 : Blo 1553474 2331653 := bbase (se 4 (by rfl) ⟨218592, by rfl⟩ : syracuseStep 2331653 = 437185) (by norm_num)
theorem B5903381 : Blo 1553474 5903381 := bbase (se 6 (by rfl) ⟨138360, by rfl⟩ : syracuseStep 5903381 = 276721) (by norm_num)
theorem B2331677 : Blo 1553474 2331677 := bbase (se 3 (by rfl) ⟨437189, by rfl⟩ : syracuseStep 2331677 = 874379) (by norm_num)
theorem B2331701 : Blo 1553474 2331701 := bbase (se 5 (by rfl) ⟨109298, by rfl⟩ : syracuseStep 2331701 = 218597) (by norm_num)
theorem B2331725 : Blo 1553474 2331725 := bbase (se 3 (by rfl) ⟨437198, by rfl⟩ : syracuseStep 2331725 = 874397) (by norm_num)
theorem B4977749 : Blo 1553474 4977749 := bbase (se 8 (by rfl) ⟨29166, by rfl⟩ : syracuseStep 4977749 = 58333) (by norm_num)
theorem B2331749 : Blo 1553474 2331749 := bbase (se 4 (by rfl) ⟨218601, by rfl⟩ : syracuseStep 2331749 = 437203) (by norm_num)
theorem B2331773 : Blo 1553474 2331773 := bbase (se 3 (by rfl) ⟨437207, by rfl⟩ : syracuseStep 2331773 = 874415) (by norm_num)
theorem B7091333 : Blo 1553474 7091333 := bbase (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) (by norm_num)
theorem B3150989 : Blo 1553474 3150989 := bbase (se 3 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 3150989 = 1181621) (by norm_num)
theorem B2331797 : Blo 1553474 2331797 := bbase (se 6 (by rfl) ⟨54651, by rfl⟩ : syracuseStep 2331797 = 109303) (by norm_num)
theorem B3151021 : Blo 1553474 3151021 := bbase (se 3 (by rfl) ⟨590816, by rfl⟩ : syracuseStep 3151021 = 1181633) (by norm_num)
theorem B2331821 : Blo 1553474 2331821 := bbase (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) (by norm_num)
theorem B2331845 : Blo 1553474 2331845 := bbase (se 4 (by rfl) ⟨218610, by rfl⟩ : syracuseStep 2331845 = 437221) (by norm_num)
theorem B2331869 : Blo 1553474 2331869 := bbase (se 3 (by rfl) ⟨437225, by rfl⟩ : syracuseStep 2331869 = 874451) (by norm_num)
theorem B2331893 : Blo 1553474 2331893 := bbase (se 5 (by rfl) ⟨109307, by rfl⟩ : syracuseStep 2331893 = 218615) (by norm_num)
theorem B2331917 : Blo 1553474 2331917 := bbase (se 3 (by rfl) ⟨437234, by rfl⟩ : syracuseStep 2331917 = 874469) (by norm_num)
theorem B1660181 : Blo 1553474 1660181 := bbase (se 6 (by rfl) ⟨38910, by rfl⟩ : syracuseStep 1660181 = 77821) (by norm_num)
theorem B2331941 : Blo 1553474 2331941 := bbase (se 4 (by rfl) ⟨218619, by rfl⟩ : syracuseStep 2331941 = 437239) (by norm_num)
theorem B5985589 : Blo 1553474 5985589 := bbase (se 5 (by rfl) ⟨280574, by rfl⟩ : syracuseStep 5985589 = 561149) (by norm_num)
theorem B2331965 : Blo 1553474 2331965 := bbase (se 3 (by rfl) ⟨437243, by rfl⟩ : syracuseStep 2331965 = 874487) (by norm_num)
theorem B2331989 : Blo 1553474 2331989 := bbase (se 14 (by rfl) ⟨213, by rfl⟩ : syracuseStep 2331989 = 427) (by norm_num)
theorem B7869797 : Blo 1553474 7869797 := bbase (se 4 (by rfl) ⟨737793, by rfl⟩ : syracuseStep 7869797 = 1475587) (by norm_num)
theorem B2332013 : Blo 1553474 2332013 := bbase (se 3 (by rfl) ⟨437252, by rfl⟩ : syracuseStep 2332013 = 874505) (by norm_num)
theorem B2332037 : Blo 1553474 2332037 := bbase (se 4 (by rfl) ⟨218628, by rfl⟩ : syracuseStep 2332037 = 437257) (by norm_num)
theorem B3691925 : Blo 1553474 3691925 := bbase (se 6 (by rfl) ⟨86529, by rfl⟩ : syracuseStep 3691925 = 173059) (by norm_num)
theorem B8852885 : Blo 1553474 8852885 := bbase (se 6 (by rfl) ⟨207489, by rfl⟩ : syracuseStep 8852885 = 414979) (by norm_num)
theorem B2332061 : Blo 1553474 2332061 := bbase (se 3 (by rfl) ⟨437261, by rfl⟩ : syracuseStep 2332061 = 874523) (by norm_num)
theorem B5248421 : Blo 1553474 5248421 := bbase (se 4 (by rfl) ⟨492039, by rfl⟩ : syracuseStep 5248421 = 984079) (by norm_num)
theorem B2332085 : Blo 1553474 2332085 := bbase (se 5 (by rfl) ⟨109316, by rfl⟩ : syracuseStep 2332085 = 218633) (by norm_num)
theorem B14382517 : Blo 1553474 14382517 := bbase (se 5 (by rfl) ⟨674180, by rfl⟩ : syracuseStep 14382517 = 1348361) (by norm_num)
theorem B3495365 : Blo 1553474 3495365 := bbase (se 4 (by rfl) ⟨327690, by rfl⟩ : syracuseStep 3495365 = 655381) (by norm_num)
theorem B2332109 : Blo 1553474 2332109 := bbase (se 3 (by rfl) ⟨437270, by rfl⟩ : syracuseStep 2332109 = 874541) (by norm_num)
theorem B2332133 : Blo 1553474 2332133 := bbase (se 4 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 2332133 = 437275) (by norm_num)
theorem B2332157 : Blo 1553474 2332157 := bbase (se 3 (by rfl) ⟨437279, by rfl⟩ : syracuseStep 2332157 = 874559) (by norm_num)
theorem B3495437 : Blo 1553474 3495437 := bbase (se 3 (by rfl) ⟨655394, by rfl⟩ : syracuseStep 3495437 = 1310789) (by norm_num)
theorem B1660429 : Blo 1553474 1660429 := bbase (se 3 (by rfl) ⟨311330, by rfl⟩ : syracuseStep 1660429 = 622661) (by norm_num)
theorem B2332181 : Blo 1553474 2332181 := bbase (se 6 (by rfl) ⟨54660, by rfl⟩ : syracuseStep 2332181 = 109321) (by norm_num)
theorem B2332205 : Blo 1553474 2332205 := bbase (se 3 (by rfl) ⟨437288, by rfl⟩ : syracuseStep 2332205 = 874577) (by norm_num)
theorem B2332229 : Blo 1553474 2332229 := bbase (se 4 (by rfl) ⟨218646, by rfl⟩ : syracuseStep 2332229 = 437293) (by norm_num)
theorem B3495509 : Blo 1553474 3495509 := bbase (se 8 (by rfl) ⟨20481, by rfl⟩ : syracuseStep 3495509 = 40963) (by norm_num)
theorem B2365013 : Blo 1553474 2365013 := bbase (se 8 (by rfl) ⟨13857, by rfl⟩ : syracuseStep 2365013 = 27715) (by norm_num)
theorem B2332253 : Blo 1553474 2332253 := bbase (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) (by norm_num)
theorem B2332277 : Blo 1553474 2332277 := bbase (se 5 (by rfl) ⟨109325, by rfl⟩ : syracuseStep 2332277 = 218651) (by norm_num)
theorem B10638965 : Blo 1553474 10638965 := bbase (se 5 (by rfl) ⟨498701, by rfl⟩ : syracuseStep 10638965 = 997403) (by norm_num)
theorem B2332301 : Blo 1553474 2332301 := bbase (se 3 (by rfl) ⟨437306, by rfl⟩ : syracuseStep 2332301 = 874613) (by norm_num)
theorem B3495581 : Blo 1553474 3495581 := bbase (se 3 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 3495581 = 1310843) (by norm_num)
theorem B2332325 : Blo 1553474 2332325 := bbase (se 4 (by rfl) ⟨218655, by rfl⟩ : syracuseStep 2332325 = 437311) (by norm_num)
theorem B2332349 : Blo 1553474 2332349 := bbase (se 3 (by rfl) ⟨437315, by rfl⟩ : syracuseStep 2332349 = 874631) (by norm_num)
theorem B3987149 : Blo 1553474 3987149 := bbase (se 3 (by rfl) ⟨747590, by rfl⟩ : syracuseStep 3987149 = 1495181) (by norm_num)
theorem B2332373 : Blo 1553474 2332373 := bbase (se 7 (by rfl) ⟨27332, by rfl⟩ : syracuseStep 2332373 = 54665) (by norm_num)
theorem B3495653 : Blo 1553474 3495653 := bbase (se 4 (by rfl) ⟨327717, by rfl⟩ : syracuseStep 3495653 = 655435) (by norm_num)
theorem B2332397 : Blo 1553474 2332397 := bbase (se 3 (by rfl) ⟨437324, by rfl⟩ : syracuseStep 2332397 = 874649) (by norm_num)
theorem B2332421 : Blo 1553474 2332421 := bbase (se 4 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 2332421 = 437329) (by norm_num)
theorem B2332445 : Blo 1553474 2332445 := bbase (se 3 (by rfl) ⟨437333, by rfl⟩ : syracuseStep 2332445 = 874667) (by norm_num)
theorem B2660125 : Blo 1553474 2660125 := bbase (se 3 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 2660125 = 997547) (by norm_num)
theorem B3495725 : Blo 1553474 3495725 := bbase (se 3 (by rfl) ⟨655448, by rfl⟩ : syracuseStep 3495725 = 1310897) (by norm_num)
theorem B2332469 : Blo 1553474 2332469 := bbase (se 5 (by rfl) ⟨109334, by rfl⟩ : syracuseStep 2332469 = 218669) (by norm_num)
theorem B2332493 : Blo 1553474 2332493 := bbase (se 3 (by rfl) ⟨437342, by rfl⟩ : syracuseStep 2332493 = 874685) (by norm_num)
theorem B13285205 : Blo 1553474 13285205 := bbase (se 9 (by rfl) ⟨38921, by rfl⟩ : syracuseStep 13285205 = 77843) (by norm_num)
theorem B5248853 : Blo 1553474 5248853 := bbase (se 9 (by rfl) ⟨15377, by rfl⟩ : syracuseStep 5248853 = 30755) (by norm_num)
theorem B6641509 : Blo 1553474 6641509 := bbase (se 4 (by rfl) ⟨622641, by rfl⟩ : syracuseStep 6641509 = 1245283) (by norm_num)
theorem B2332517 : Blo 1553474 2332517 := bbase (se 4 (by rfl) ⟨218673, by rfl⟩ : syracuseStep 2332517 = 437347) (by norm_num)
theorem B3495797 : Blo 1553474 3495797 := bbase (se 5 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 3495797 = 327731) (by norm_num)
theorem B2332541 : Blo 1553474 2332541 := bbase (se 3 (by rfl) ⟨437351, by rfl⟩ : syracuseStep 2332541 = 874703) (by norm_num)
theorem B2332565 : Blo 1553474 2332565 := bbase (se 6 (by rfl) ⟨54669, by rfl⟩ : syracuseStep 2332565 = 109339) (by norm_num)
theorem B2332589 : Blo 1553474 2332589 := bbase (se 3 (by rfl) ⟨437360, by rfl⟩ : syracuseStep 2332589 = 874721) (by norm_num)
theorem B3495869 : Blo 1553474 3495869 := bbase (se 3 (by rfl) ⟨655475, by rfl⟩ : syracuseStep 3495869 = 1310951) (by norm_num)
theorem B2332613 : Blo 1553474 2332613 := bbase (se 4 (by rfl) ⟨218682, by rfl⟩ : syracuseStep 2332613 = 437365) (by norm_num)
theorem B1660873 : Blo 1553474 1660873 := bbase (se 2 (by rfl) ⟨622827, by rfl⟩ : syracuseStep 1660873 = 1245655) (by norm_num)
theorem B13277141 : Blo 1553474 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B25221077 : Blo 1553474 25221077 := bbase (se 7 (by rfl) ⟨295559, by rfl⟩ : syracuseStep 25221077 = 591119) (by norm_num)
theorem B2332637 : Blo 1553474 2332637 := bbase (se 3 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 2332637 = 874739) (by norm_num)
theorem B2332661 : Blo 1553474 2332661 := bbase (se 5 (by rfl) ⟨109343, by rfl⟩ : syracuseStep 2332661 = 218687) (by norm_num)
theorem B3495941 : Blo 1553474 3495941 := bbase (se 4 (by rfl) ⟨327744, by rfl⟩ : syracuseStep 3495941 = 655489) (by norm_num)
theorem B1660933 : Blo 1553474 1660933 := bbase (se 4 (by rfl) ⟨155712, by rfl⟩ : syracuseStep 1660933 = 311425) (by norm_num)
theorem B2332685 : Blo 1553474 2332685 := bbase (se 3 (by rfl) ⟨437378, by rfl⟩ : syracuseStep 2332685 = 874757) (by norm_num)
theorem B2332709 : Blo 1553474 2332709 := bbase (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) (by norm_num)
theorem B2332733 : Blo 1553474 2332733 := bbase (se 3 (by rfl) ⟨437387, by rfl⟩ : syracuseStep 2332733 = 874775) (by norm_num)
theorem B3496013 : Blo 1553474 3496013 := bbase (se 3 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 3496013 = 1311005) (by norm_num)
theorem B2332757 : Blo 1553474 2332757 := bbase (se 8 (by rfl) ⟨13668, by rfl⟩ : syracuseStep 2332757 = 27337) (by norm_num)
theorem B3545189 : Blo 1553474 3545189 := bbase (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) (by norm_num)
theorem B2332781 : Blo 1553474 2332781 := bbase (se 3 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 2332781 = 874793) (by norm_num)
theorem B2332805 : Blo 1553474 2332805 := bbase (se 4 (by rfl) ⟨218700, by rfl⟩ : syracuseStep 2332805 = 437401) (by norm_num)
theorem B3496085 : Blo 1553474 3496085 := bbase (se 6 (by rfl) ⟨81939, by rfl⟩ : syracuseStep 3496085 = 163879) (by norm_num)
theorem B2332829 : Blo 1553474 2332829 := bbase (se 3 (by rfl) ⟨437405, by rfl⟩ : syracuseStep 2332829 = 874811) (by norm_num)
theorem B2332853 : Blo 1553474 2332853 := bbase (se 5 (by rfl) ⟨109352, by rfl⟩ : syracuseStep 2332853 = 218705) (by norm_num)
theorem B2332877 : Blo 1553474 2332877 := bbase (se 3 (by rfl) ⟨437414, by rfl⟩ : syracuseStep 2332877 = 874829) (by norm_num)
theorem B3496157 : Blo 1553474 3496157 := bbase (se 3 (by rfl) ⟨655529, by rfl⟩ : syracuseStep 3496157 = 1311059) (by norm_num)
theorem B2332901 : Blo 1553474 2332901 := bbase (se 4 (by rfl) ⟨218709, by rfl⟩ : syracuseStep 2332901 = 437419) (by norm_num)
theorem B3152117 : Blo 1553474 3152117 := bbase (se 5 (by rfl) ⟨147755, by rfl⟩ : syracuseStep 3152117 = 295511) (by norm_num)
theorem B2332925 : Blo 1553474 2332925 := bbase (se 3 (by rfl) ⟨437423, by rfl⟩ : syracuseStep 2332925 = 874847) (by norm_num)
theorem B5249285 : Blo 1553474 5249285 := bbase (se 4 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 5249285 = 984241) (by norm_num)
theorem B2332949 : Blo 1553474 2332949 := bbase (se 6 (by rfl) ⟨54678, by rfl⟩ : syracuseStep 2332949 = 109357) (by norm_num)
theorem B3496229 : Blo 1553474 3496229 := bbase (se 4 (by rfl) ⟨327771, by rfl⟩ : syracuseStep 3496229 = 655543) (by norm_num)
theorem B2332973 : Blo 1553474 2332973 := bbase (se 3 (by rfl) ⟨437432, by rfl⟩ : syracuseStep 2332973 = 874865) (by norm_num)
theorem B2799941 : Blo 1553474 2799941 := bbase (se 4 (by rfl) ⟨262494, by rfl⟩ : syracuseStep 2799941 = 524989) (by norm_num)
theorem B2332997 : Blo 1553474 2332997 := bbase (se 4 (by rfl) ⟨218718, by rfl⟩ : syracuseStep 2332997 = 437437) (by norm_num)
theorem B2333021 : Blo 1553474 2333021 := bbase (se 3 (by rfl) ⟨437441, by rfl⟩ : syracuseStep 2333021 = 874883) (by norm_num)
theorem B3496301 : Blo 1553474 3496301 := bbase (se 3 (by rfl) ⟨655556, by rfl⟩ : syracuseStep 3496301 = 1311113) (by norm_num)
theorem B2333045 : Blo 1553474 2333045 := bbase (se 5 (by rfl) ⟨109361, by rfl⟩ : syracuseStep 2333045 = 218723) (by norm_num)
theorem B2333069 : Blo 1553474 2333069 := bbase (se 3 (by rfl) ⟨437450, by rfl⟩ : syracuseStep 2333069 = 874901) (by norm_num)
theorem B2333093 : Blo 1553474 2333093 := bbase (se 4 (by rfl) ⟨218727, by rfl⟩ : syracuseStep 2333093 = 437455) (by norm_num)
theorem B3496373 : Blo 1553474 3496373 := bbase (se 5 (by rfl) ⟨163892, by rfl⟩ : syracuseStep 3496373 = 327785) (by norm_num)
theorem B2333117 : Blo 1553474 2333117 := bbase (se 3 (by rfl) ⟨437459, by rfl⟩ : syracuseStep 2333117 = 874919) (by norm_num)
theorem B2333141 : Blo 1553474 2333141 := bbase (se 7 (by rfl) ⟨27341, by rfl⟩ : syracuseStep 2333141 = 54683) (by norm_num)
theorem B2333165 : Blo 1553474 2333165 := bbase (se 3 (by rfl) ⟨437468, by rfl⟩ : syracuseStep 2333165 = 874937) (by norm_num)
theorem B3496445 : Blo 1553474 3496445 := bbase (se 3 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 3496445 = 1311167) (by norm_num)
theorem B2333189 : Blo 1553474 2333189 := bbase (se 4 (by rfl) ⟨218736, by rfl⟩ : syracuseStep 2333189 = 437473) (by norm_num)
theorem B8854069 : Blo 1553474 8854069 := bbase (se 5 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 8854069 = 830069) (by norm_num)
theorem B3496517 : Blo 1553474 3496517 := bbase (se 4 (by rfl) ⟨327798, by rfl⟩ : syracuseStep 3496517 = 655597) (by norm_num)
theorem B7871093 : Blo 1553474 7871093 := bbase (se 5 (by rfl) ⟨368957, by rfl⟩ : syracuseStep 7871093 = 737915) (by norm_num)
theorem B3496589 : Blo 1553474 3496589 := bbase (se 3 (by rfl) ⟨655610, by rfl⟩ : syracuseStep 3496589 = 1311221) (by norm_num)
theorem B28367509 : Blo 1553474 28367509 := bbase (se 6 (by rfl) ⟨664863, by rfl⟩ : syracuseStep 28367509 = 1329727) (by norm_num)
theorem B1866397 : Blo 1553474 1866397 := bbase (se 3 (by rfl) ⟨349949, by rfl⟩ : syracuseStep 1866397 = 699899) (by norm_num)
theorem B5249717 : Blo 1553474 5249717 := bbase (se 5 (by rfl) ⟨246080, by rfl⟩ : syracuseStep 5249717 = 492161) (by norm_num)
theorem B3496661 : Blo 1553474 3496661 := bbase (se 7 (by rfl) ⟨40976, by rfl⟩ : syracuseStep 3496661 = 81953) (by norm_num)
theorem B3496733 : Blo 1553474 3496733 := bbase (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) (by norm_num)
theorem B2489125 : Blo 1553474 2489125 := bbase (se 4 (by rfl) ⟨233355, by rfl⟩ : syracuseStep 2489125 = 466711) (by norm_num)
theorem B2800445 : Blo 1553474 2800445 := bbase (se 3 (by rfl) ⟨525083, by rfl⟩ : syracuseStep 2800445 = 1050167) (by norm_num)
theorem B3496805 : Blo 1553474 3496805 := bbase (se 4 (by rfl) ⟨327825, by rfl⟩ : syracuseStep 3496805 = 655651) (by norm_num)
theorem B3496877 : Blo 1553474 3496877 := bbase (se 3 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 3496877 = 1311329) (by norm_num)
theorem B3152837 : Blo 1553474 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B3496949 : Blo 1553474 3496949 := bbase (se 5 (by rfl) ⟨163919, by rfl⟩ : syracuseStep 3496949 = 327839) (by norm_num)
theorem B2022413 : Blo 1553474 2022413 := bbase (se 3 (by rfl) ⟨379202, by rfl⟩ : syracuseStep 2022413 = 758405) (by norm_num)
theorem B8969237 : Blo 1553474 8969237 := bbase (se 6 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 8969237 = 420433) (by norm_num)
theorem B3497021 : Blo 1553474 3497021 := bbase (se 3 (by rfl) ⟨655691, by rfl⟩ : syracuseStep 3497021 = 1311383) (by norm_num)
theorem B5905493 : Blo 1553474 5905493 := bbase (se 8 (by rfl) ⟨34602, by rfl⟩ : syracuseStep 5905493 = 69205) (by norm_num)
theorem B3497093 : Blo 1553474 3497093 := bbase (se 4 (by rfl) ⟨327852, by rfl⟩ : syracuseStep 3497093 = 655705) (by norm_num)
theorem B3497165 : Blo 1553474 3497165 := bbase (se 3 (by rfl) ⟨655718, by rfl⟩ : syracuseStep 3497165 = 1311437) (by norm_num)
theorem B3497237 : Blo 1553474 3497237 := bbase (se 6 (by rfl) ⟨81966, by rfl⟩ : syracuseStep 3497237 = 163933) (by norm_num)
theorem B4980005 : Blo 1553474 4980005 := bbase (se 4 (by rfl) ⟨466875, by rfl⟩ : syracuseStep 4980005 = 933751) (by norm_num)
theorem B3497309 : Blo 1553474 3497309 := bbase (se 3 (by rfl) ⟨655745, by rfl⟩ : syracuseStep 3497309 = 1311491) (by norm_num)
theorem B5905781 : Blo 1553474 5905781 := bbase (se 5 (by rfl) ⟨276833, by rfl⟩ : syracuseStep 5905781 = 553667) (by norm_num)
theorem B3497381 : Blo 1553474 3497381 := bbase (se 4 (by rfl) ⟨327879, by rfl⟩ : syracuseStep 3497381 = 655759) (by norm_num)
theorem B4980133 : Blo 1553474 4980133 := bbase (se 4 (by rfl) ⟨466887, by rfl⟩ : syracuseStep 4980133 = 933775) (by norm_num)
theorem B2489797 : Blo 1553474 2489797 := bbase (se 4 (by rfl) ⟨233418, by rfl⟩ : syracuseStep 2489797 = 466837) (by norm_num)
theorem B3497453 : Blo 1553474 3497453 := bbase (se 3 (by rfl) ⟨655772, by rfl⟩ : syracuseStep 3497453 = 1311545) (by norm_num)
theorem B3988997 : Blo 1553474 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B2801189 : Blo 1553474 2801189 := bbase (se 4 (by rfl) ⟨262611, by rfl⟩ : syracuseStep 2801189 = 525223) (by norm_num)
theorem B3497525 : Blo 1553474 3497525 := bbase (se 5 (by rfl) ⟨163946, by rfl⟩ : syracuseStep 3497525 = 327893) (by norm_num)
theorem B3735157 : Blo 1553474 3735157 := bbase (se 5 (by rfl) ⟨175085, by rfl⟩ : syracuseStep 3735157 = 350171) (by norm_num)
theorem B3497597 : Blo 1553474 3497597 := bbase (se 3 (by rfl) ⟨655799, by rfl⟩ : syracuseStep 3497597 = 1311599) (by norm_num)
theorem B1867421 : Blo 1553474 1867421 := bbase (se 3 (by rfl) ⟨350141, by rfl⟩ : syracuseStep 1867421 = 700283) (by norm_num)
theorem B2916013 : Blo 1553474 2916013 := bbase (se 3 (by rfl) ⟨546752, by rfl⟩ : syracuseStep 2916013 = 1093505) (by norm_num)
theorem B3497669 : Blo 1553474 3497669 := bbase (se 4 (by rfl) ⟨327906, by rfl⟩ : syracuseStep 3497669 = 655813) (by norm_num)
theorem B3497741 : Blo 1553474 3497741 := bbase (se 3 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 3497741 = 1311653) (by norm_num)
theorem B3497813 : Blo 1553474 3497813 := bbase (se 9 (by rfl) ⟨10247, by rfl⟩ : syracuseStep 3497813 = 20495) (by norm_num)
theorem B3735389 : Blo 1553474 3735389 := bbase (se 3 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 3735389 = 1400771) (by norm_num)
theorem B3366773 : Blo 1553474 3366773 := bbase (se 5 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 3366773 = 315635) (by norm_num)
theorem B7872389 : Blo 1553474 7872389 := bbase (se 4 (by rfl) ⟨738036, by rfl⟩ : syracuseStep 7872389 = 1476073) (by norm_num)
theorem B4202389 : Blo 1553474 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B3497885 : Blo 1553474 3497885 := bbase (se 3 (by rfl) ⟨655853, by rfl⟩ : syracuseStep 3497885 = 1311707) (by norm_num)
theorem B3497957 : Blo 1553474 3497957 := bbase (se 4 (by rfl) ⟨327933, by rfl⟩ : syracuseStep 3497957 = 655867) (by norm_num)
theorem B3735533 : Blo 1553474 3735533 := bbase (se 3 (by rfl) ⟨700412, by rfl⟩ : syracuseStep 3735533 = 1400825) (by norm_num)
theorem B2211889 : Blo 1553474 2211889 := bstep (se 2 (by rfl) ⟨829458, by rfl⟩ : syracuseStep 2211889 = 1658917) B1658917
theorem B3498065 : Blo 1553474 3498065 := bstep (se 2 (by rfl) ⟨1311774, by rfl⟩ : syracuseStep 3498065 = 2623549) B2623549
theorem B3498083 : Blo 1553474 3498083 := bstep (se 1 (by rfl) ⟨2623562, by rfl⟩ : syracuseStep 3498083 = 5247125) B5247125
theorem B5243021 : Blo 1553474 5243021 := bstep (se 3 (by rfl) ⟨983066, by rfl⟩ : syracuseStep 5243021 = 1966133) B1966133
theorem B2621585 : Blo 1553474 2621585 := bstep (se 2 (by rfl) ⟨983094, by rfl⟩ : syracuseStep 2621585 = 1966189) B1966189
theorem B2490515 : Blo 1553474 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B3735715 : Blo 1553474 3735715 := bstep (se 1 (by rfl) ⟨2801786, by rfl⟩ : syracuseStep 3735715 = 5603573) B5603573
theorem B9961649 : Blo 1553474 9961649 := bstep (se 2 (by rfl) ⟨3735618, by rfl⟩ : syracuseStep 9961649 = 7471237) B7471237
theorem B5243075 : Blo 1553474 5243075 := bstep (se 1 (by rfl) ⟨3932306, by rfl⟩ : syracuseStep 5243075 = 7864613) B7864613
theorem B13287665 : Blo 1553474 13287665 := bstep (se 2 (by rfl) ⟨4982874, by rfl⟩ : syracuseStep 13287665 = 9965749) B9965749
theorem B2621713 : Blo 1553474 2621713 := bstep (se 2 (by rfl) ⟨983142, by rfl⟩ : syracuseStep 2621713 = 1966285) B1966285
theorem B2621747 : Blo 1553474 2621747 := bstep (se 1 (by rfl) ⟨1966310, by rfl⟩ : syracuseStep 2621747 = 3932621) B3932621
theorem B2949443 : Blo 1553474 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B4424017 : Blo 1553474 4424017 := bstep (se 2 (by rfl) ⟨1659006, by rfl⟩ : syracuseStep 4424017 = 3318013) B3318013
theorem B3498353 : Blo 1553474 3498353 := bstep (se 2 (by rfl) ⟨1311882, by rfl⟩ : syracuseStep 3498353 = 2623765) B2623765
theorem B3498371 : Blo 1553474 3498371 := bstep (se 1 (by rfl) ⟨2623778, by rfl⟩ : syracuseStep 3498371 = 5247557) B5247557
theorem B2621875 : Blo 1553474 2621875 := bstep (se 1 (by rfl) ⟨1966406, by rfl⟩ : syracuseStep 2621875 = 3932813) B3932813
theorem B5243345 : Blo 1553474 5243345 := bstep (se 2 (by rfl) ⟨1966254, by rfl⟩ : syracuseStep 5243345 = 3932509) B3932509
theorem B7873037 : Blo 1553474 7873037 := bstep (se 3 (by rfl) ⟨1476194, by rfl⟩ : syracuseStep 7873037 = 2952389) B2952389
theorem B2622017 : Blo 1553474 2622017 := bstep (se 2 (by rfl) ⟨983256, by rfl⟩ : syracuseStep 2622017 = 1966513) B1966513
theorem B1966675 : Blo 1553474 1966675 := bstep (se 1 (by rfl) ⟨1475006, by rfl⟩ : syracuseStep 1966675 = 2950013) B2950013
theorem B4424291 : Blo 1553474 4424291 := bstep (se 1 (by rfl) ⟨3318218, by rfl⟩ : syracuseStep 4424291 = 6636437) B6636437
theorem B2212481 : Blo 1553474 2212481 := bstep (se 2 (by rfl) ⟨829680, by rfl⟩ : syracuseStep 2212481 = 1659361) B1659361
theorem B3498641 : Blo 1553474 3498641 := bstep (se 2 (by rfl) ⟨1311990, by rfl⟩ : syracuseStep 3498641 = 2623981) B2623981
theorem B3498659 : Blo 1553474 3498659 := bstep (se 1 (by rfl) ⟨2623994, by rfl⟩ : syracuseStep 3498659 = 5247989) B5247989
theorem B1966771 : Blo 1553474 1966771 := bstep (se 1 (by rfl) ⟨1475078, by rfl⟩ : syracuseStep 1966771 = 2950157) B2950157
theorem B2622145 : Blo 1553474 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B3318499 : Blo 1553474 3318499 := bstep (se 1 (by rfl) ⟨2488874, by rfl⟩ : syracuseStep 3318499 = 4977749) B4977749
theorem B2622179 : Blo 1553474 2622179 := bstep (se 1 (by rfl) ⟨1966634, by rfl⟩ : syracuseStep 2622179 = 3933269) B3933269
theorem B11199217 : Blo 1553474 11199217 := bstep (se 2 (by rfl) ⟨4199706, by rfl⟩ : syracuseStep 11199217 = 8399413) B8399413
theorem B11805425 : Blo 1553474 11805425 := bstep (se 2 (by rfl) ⟨4427034, by rfl⟩ : syracuseStep 11805425 = 8854069) B8854069
theorem B4727555 : Blo 1553474 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B3932945 : Blo 1553474 3932945 := bstep (se 2 (by rfl) ⟨1474854, by rfl⟩ : syracuseStep 3932945 = 2949709) B2949709
theorem B4424483 : Blo 1553474 4424483 := bstep (se 1 (by rfl) ⟨3318362, by rfl⟩ : syracuseStep 4424483 = 6636725) B6636725
theorem B3932995 : Blo 1553474 3932995 := bstep (se 1 (by rfl) ⟨2949746, by rfl⟩ : syracuseStep 3932995 = 5899493) B5899493
theorem B3736387 : Blo 1553474 3736387 := bstep (se 1 (by rfl) ⟨2802290, by rfl⟩ : syracuseStep 3736387 = 5604581) B5604581
theorem B2622307 : Blo 1553474 2622307 := bstep (se 1 (by rfl) ⟨1966730, by rfl⟩ : syracuseStep 2622307 = 3933461) B3933461
theorem B4203373 : Blo 1553474 4203373 := bstep (se 3 (by rfl) ⟨788132, by rfl⟩ : syracuseStep 4203373 = 1576265) B1576265
theorem B37823345 : Blo 1553474 37823345 := bstep (se 2 (by rfl) ⟨14183754, by rfl⟩ : syracuseStep 37823345 = 28367509) B28367509
theorem B3498929 : Blo 1553474 3498929 := bstep (se 2 (by rfl) ⟨1312098, by rfl⟩ : syracuseStep 3498929 = 2624197) B2624197
theorem B3498947 : Blo 1553474 3498947 := bstep (se 1 (by rfl) ⟨2624210, by rfl⟩ : syracuseStep 3498947 = 5248421) B5248421
theorem B3933137 : Blo 1553474 3933137 := bstep (se 2 (by rfl) ⟨1474926, by rfl⟩ : syracuseStep 3933137 = 2949853) B2949853
theorem B5243885 : Blo 1553474 5243885 := bstep (se 3 (by rfl) ⟨983228, by rfl⟩ : syracuseStep 5243885 = 1966457) B1966457
theorem B2622449 : Blo 1553474 2622449 := bstep (se 2 (by rfl) ⟨983418, by rfl⟩ : syracuseStep 2622449 = 1966837) B1966837
theorem B5243939 : Blo 1553474 5243939 := bstep (se 1 (by rfl) ⟨3932954, by rfl⟩ : syracuseStep 5243939 = 7865909) B7865909
theorem B3318833 : Blo 1553474 3318833 := bstep (se 2 (by rfl) ⟨1244562, by rfl⟩ : syracuseStep 3318833 = 2489125) B2489125
theorem B37815349 : Blo 1553474 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B2491489 : Blo 1553474 2491489 := bstep (se 2 (by rfl) ⟨934308, by rfl⟩ : syracuseStep 2491489 = 1868617) B1868617
theorem B2622577 : Blo 1553474 2622577 := bstep (se 2 (by rfl) ⟨983466, by rfl⟩ : syracuseStep 2622577 = 1966933) B1966933
theorem B2622611 : Blo 1553474 2622611 := bstep (se 1 (by rfl) ⟨1966958, by rfl⟩ : syracuseStep 2622611 = 3933917) B3933917
theorem B2213011 : Blo 1553474 2213011 := bstep (se 1 (by rfl) ⟨1659758, by rfl⟩ : syracuseStep 2213011 = 3319517) B3319517
theorem B1967267 : Blo 1553474 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B2950339 : Blo 1553474 2950339 := bstep (se 1 (by rfl) ⟨2212754, by rfl⟩ : syracuseStep 2950339 = 4425509) B4425509
theorem B3499217 : Blo 1553474 3499217 := bstep (se 2 (by rfl) ⟨1312206, by rfl⟩ : syracuseStep 3499217 = 2624413) B2624413
theorem B8856803 : Blo 1553474 8856803 := bstep (se 1 (by rfl) ⟨6642602, by rfl⟩ : syracuseStep 8856803 = 13285205) B13285205
theorem B3499235 : Blo 1553474 3499235 := bstep (se 1 (by rfl) ⟨2624426, by rfl⟩ : syracuseStep 3499235 = 5248853) B5248853
theorem B7865585 : Blo 1553474 7865585 := bstep (se 2 (by rfl) ⟨2949594, by rfl⟩ : syracuseStep 7865585 = 5899189) B5899189
theorem B3736849 : Blo 1553474 3736849 := bstep (se 2 (by rfl) ⟨1401318, by rfl⟩ : syracuseStep 3736849 = 2802637) B2802637
theorem B2622739 : Blo 1553474 2622739 := bstep (se 1 (by rfl) ⟨1967054, by rfl⟩ : syracuseStep 2622739 = 3934109) B3934109
theorem B5244209 : Blo 1553474 5244209 := bstep (se 2 (by rfl) ⟨1966578, by rfl⟩ : syracuseStep 5244209 = 3933157) B3933157
theorem B2950499 : Blo 1553474 2950499 := bstep (se 1 (by rfl) ⟨2212874, by rfl⟩ : syracuseStep 2950499 = 4425749) B4425749
theorem B3736945 : Blo 1553474 3736945 := bstep (se 2 (by rfl) ⟨1401354, by rfl⟩ : syracuseStep 3736945 = 2802709) B2802709
theorem B5899661 : Blo 1553474 5899661 := bstep (se 3 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 5899661 = 2212373) B2212373
theorem B2622881 : Blo 1553474 2622881 := bstep (se 2 (by rfl) ⟨983580, by rfl⟩ : syracuseStep 2622881 = 1967161) B1967161
theorem B2213347 : Blo 1553474 2213347 := bstep (se 1 (by rfl) ⟨1660010, by rfl⟩ : syracuseStep 2213347 = 3320021) B3320021
theorem B3499505 : Blo 1553474 3499505 := bstep (se 2 (by rfl) ⟨1312314, by rfl⟩ : syracuseStep 3499505 = 2624629) B2624629
theorem B3499523 : Blo 1553474 3499523 := bstep (se 1 (by rfl) ⟨2624642, by rfl⟩ : syracuseStep 3499523 = 5249285) B5249285
theorem B2623009 : Blo 1553474 2623009 := bstep (se 2 (by rfl) ⟨983628, by rfl⟩ : syracuseStep 2623009 = 1967257) B1967257
theorem B21268021 : Blo 1553474 21268021 := bstep (se 5 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 21268021 = 1993877) B1993877
theorem B2623043 : Blo 1553474 2623043 := bstep (se 1 (by rfl) ⟨1967282, by rfl⟩ : syracuseStep 2623043 = 3934565) B3934565
theorem B4425293 : Blo 1553474 4425293 := bstep (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) B1659485
theorem B2623171 : Blo 1553474 2623171 := bstep (se 1 (by rfl) ⟨1967378, by rfl⟩ : syracuseStep 2623171 = 3934757) B3934757
theorem B26961605 : Blo 1553474 26961605 := bstep (se 4 (by rfl) ⟨2527650, by rfl⟩ : syracuseStep 26961605 = 5055301) B5055301
theorem B7980785 : Blo 1553474 7980785 := bstep (se 2 (by rfl) ⟨2992794, by rfl⟩ : syracuseStep 7980785 = 5985589) B5985589
theorem B4425475 : Blo 1553474 4425475 := bstep (se 1 (by rfl) ⟨3319106, by rfl⟩ : syracuseStep 4425475 = 6638213) B6638213
theorem B14944013 : Blo 1553474 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B3499793 : Blo 1553474 3499793 := bstep (se 2 (by rfl) ⟨1312422, by rfl⟩ : syracuseStep 3499793 = 2624845) B2624845
theorem B3499811 : Blo 1553474 3499811 := bstep (se 1 (by rfl) ⟨2624858, by rfl⟩ : syracuseStep 3499811 = 5249717) B5249717
theorem B5244749 : Blo 1553474 5244749 := bstep (se 3 (by rfl) ⟨983390, by rfl⟩ : syracuseStep 5244749 = 1966781) B1966781
theorem B2623313 : Blo 1553474 2623313 := bstep (se 2 (by rfl) ⟨983742, by rfl⟩ : syracuseStep 2623313 = 1967485) B1967485
theorem B1967971 : Blo 1553474 1967971 := bstep (se 1 (by rfl) ⟨1475978, by rfl⟩ : syracuseStep 1967971 = 2951957) B2951957
theorem B5244803 : Blo 1553474 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B3934129 : Blo 1553474 3934129 := bstep (se 2 (by rfl) ⟨1475298, by rfl⟩ : syracuseStep 3934129 = 2950597) B2950597
theorem B1968067 : Blo 1553474 1968067 := bstep (se 1 (by rfl) ⟨1476050, by rfl⟩ : syracuseStep 1968067 = 2952101) B2952101
theorem B2623441 : Blo 1553474 2623441 := bstep (se 2 (by rfl) ⟨983790, by rfl⟩ : syracuseStep 2623441 = 1967581) B1967581
theorem B2623475 : Blo 1553474 2623475 := bstep (se 1 (by rfl) ⟨1967606, by rfl⟩ : syracuseStep 2623475 = 3935213) B3935213
theorem B2213905 : Blo 1553474 2213905 := bstep (se 2 (by rfl) ⟨830214, by rfl⟩ : syracuseStep 2213905 = 1660429) B1660429
theorem B2213939 : Blo 1553474 2213939 := bstep (se 1 (by rfl) ⟨1660454, by rfl⟩ : syracuseStep 2213939 = 3320909) B3320909
theorem B2623603 : Blo 1553474 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B5245073 : Blo 1553474 5245073 := bstep (se 2 (by rfl) ⟨1966902, by rfl⟩ : syracuseStep 5245073 = 3933805) B3933805
theorem B5900465 : Blo 1553474 5900465 := bstep (se 2 (by rfl) ⟨2212674, by rfl⟩ : syracuseStep 5900465 = 4425349) B4425349
theorem B3934403 : Blo 1553474 3934403 := bstep (se 1 (by rfl) ⟨2950802, by rfl⟩ : syracuseStep 3934403 = 5901605) B5901605
theorem B3320003 : Blo 1553474 3320003 := bstep (se 1 (by rfl) ⟨2490002, by rfl⟩ : syracuseStep 3320003 = 4980005) B4980005
theorem B4425965 : Blo 1553474 4425965 := bstep (se 3 (by rfl) ⟨829868, by rfl⟩ : syracuseStep 4425965 = 1659737) B1659737
theorem B2623745 : Blo 1553474 2623745 := bstep (se 2 (by rfl) ⟨983904, by rfl⟩ : syracuseStep 2623745 = 1967809) B1967809
theorem B2623873 : Blo 1553474 2623873 := bstep (se 2 (by rfl) ⟨983952, by rfl⟩ : syracuseStep 2623873 = 1967905) B1967905
theorem B3934595 : Blo 1553474 3934595 := bstep (se 1 (by rfl) ⟨2950946, by rfl⟩ : syracuseStep 3934595 = 5901893) B5901893
theorem B2951569 : Blo 1553474 2951569 := bstep (se 2 (by rfl) ⟨1106838, by rfl⟩ : syracuseStep 2951569 = 2213677) B2213677
theorem B3074449 : Blo 1553474 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B2623907 : Blo 1553474 2623907 := bstep (se 1 (by rfl) ⟨1967930, by rfl⟩ : syracuseStep 2623907 = 3935861) B3935861
theorem B7465393 : Blo 1553474 7465393 := bstep (se 2 (by rfl) ⟨2799522, by rfl⟩ : syracuseStep 7465393 = 5599045) B5599045
theorem B1968563 : Blo 1553474 1968563 := bstep (se 1 (by rfl) ⟨1476422, by rfl⟩ : syracuseStep 1968563 = 2952845) B2952845
theorem B2099729 : Blo 1553474 2099729 := bstep (se 2 (by rfl) ⟨787398, by rfl⟩ : syracuseStep 2099729 = 1574797) B1574797
theorem B2624035 : Blo 1553474 2624035 := bstep (se 1 (by rfl) ⟨1968026, by rfl⟩ : syracuseStep 2624035 = 3936053) B3936053
theorem B8849969 : Blo 1553474 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B9964109 : Blo 1553474 9964109 := bstep (se 3 (by rfl) ⟨1868270, by rfl⟩ : syracuseStep 9964109 = 3736541) B3736541
theorem B2214497 : Blo 1553474 2214497 := bstep (se 2 (by rfl) ⟨830436, by rfl⟩ : syracuseStep 2214497 = 1660873) B1660873
theorem B1772131 : Blo 1553474 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B7867043 : Blo 1553474 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B5245613 : Blo 1553474 5245613 := bstep (se 3 (by rfl) ⟨983552, by rfl⟩ : syracuseStep 5245613 = 1967105) B1967105
theorem B2624177 : Blo 1553474 2624177 := bstep (se 2 (by rfl) ⟨984066, by rfl⟩ : syracuseStep 2624177 = 1968133) B1968133
theorem B2214577 : Blo 1553474 2214577 := bstep (se 2 (by rfl) ⟨830466, by rfl⟩ : syracuseStep 2214577 = 1660933) B1660933
theorem B5393101 : Blo 1553474 5393101 := bstep (se 3 (by rfl) ⟨1011206, by rfl⟩ : syracuseStep 5393101 = 2022413) B2022413
theorem B5245667 : Blo 1553474 5245667 := bstep (se 1 (by rfl) ⟨3934250, by rfl⟩ : syracuseStep 5245667 = 7868501) B7868501
theorem B2624305 : Blo 1553474 2624305 := bstep (se 2 (by rfl) ⟨984114, by rfl⟩ : syracuseStep 2624305 = 1968229) B1968229
theorem B5901133 : Blo 1553474 5901133 := bstep (se 3 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 5901133 = 2212925) B2212925
theorem B1747795 : Blo 1553474 1747795 := bstep (se 1 (by rfl) ⟨1310846, by rfl⟩ : syracuseStep 1747795 = 2621693) B2621693
theorem B2624339 : Blo 1553474 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B6638435 : Blo 1553474 6638435 := bstep (se 1 (by rfl) ⟨4978826, by rfl⟩ : syracuseStep 6638435 = 9957653) B9957653
theorem B2100097 : Blo 1553474 2100097 := bstep (se 2 (by rfl) ⟨787536, by rfl⟩ : syracuseStep 2100097 = 1575073) B1575073
theorem B1575811 : Blo 1553474 1575811 := bstep (se 1 (by rfl) ⟨1181858, by rfl⟩ : syracuseStep 1575811 = 2363717) B2363717
theorem B2100161 : Blo 1553474 2100161 := bstep (se 2 (by rfl) ⟨787560, by rfl⟩ : syracuseStep 2100161 = 1575121) B1575121
theorem B2624467 : Blo 1553474 2624467 := bstep (se 1 (by rfl) ⟨1968350, by rfl⟩ : syracuseStep 2624467 = 3936701) B3936701
theorem B1747939 : Blo 1553474 1747939 := bstep (se 1 (by rfl) ⟨1310954, by rfl⟩ : syracuseStep 1747939 = 2621909) B2621909
theorem B5245937 : Blo 1553474 5245937 := bstep (se 2 (by rfl) ⟨1967226, by rfl⟩ : syracuseStep 5245937 = 3934453) B3934453
theorem B2624609 : Blo 1553474 2624609 := bstep (se 2 (by rfl) ⟨984228, by rfl⟩ : syracuseStep 2624609 = 1968457) B1968457
theorem B1748083 : Blo 1553474 1748083 := bstep (se 1 (by rfl) ⟨1311062, by rfl⟩ : syracuseStep 1748083 = 2622125) B2622125
theorem B4730033 : Blo 1553474 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B1772723 : Blo 1553474 1772723 := bstep (se 1 (by rfl) ⟨1329542, by rfl⟩ : syracuseStep 1772723 = 2659085) B2659085
theorem B2624737 : Blo 1553474 2624737 := bstep (se 2 (by rfl) ⟨984276, by rfl⟩ : syracuseStep 2624737 = 1968553) B1968553
theorem B1748227 : Blo 1553474 1748227 := bstep (se 1 (by rfl) ⟨1311170, by rfl⟩ : syracuseStep 1748227 = 2622341) B2622341
theorem B2624771 : Blo 1553474 2624771 := bstep (se 1 (by rfl) ⟨1968578, by rfl⟩ : syracuseStep 2624771 = 3937157) B3937157
theorem B3935537 : Blo 1553474 3935537 := bstep (se 2 (by rfl) ⟨1475826, by rfl⟩ : syracuseStep 3935537 = 2951653) B2951653
theorem B29871413 : Blo 1553474 29871413 := bstep (se 5 (by rfl) ⟨1400222, by rfl⟩ : syracuseStep 29871413 = 2800445) B2800445
theorem B3935587 : Blo 1553474 3935587 := bstep (se 1 (by rfl) ⟨2951690, by rfl⟩ : syracuseStep 3935587 = 5903381) B5903381
theorem B4427149 : Blo 1553474 4427149 := bstep (se 3 (by rfl) ⟨830090, by rfl⟩ : syracuseStep 4427149 = 1660181) B1660181
theorem B1748371 : Blo 1553474 1748371 := bstep (se 1 (by rfl) ⟨1311278, by rfl⟩ : syracuseStep 1748371 = 2622557) B2622557
theorem B5049773 : Blo 1553474 5049773 := bstep (se 3 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 5049773 = 1893665) B1893665
theorem B2952625 : Blo 1553474 2952625 := bstep (se 2 (by rfl) ⟨1107234, by rfl⟩ : syracuseStep 2952625 = 2214469) B2214469
theorem B2100659 : Blo 1553474 2100659 := bstep (se 1 (by rfl) ⟨1575494, by rfl⟩ : syracuseStep 2100659 = 3150989) B3150989
theorem B7867853 : Blo 1553474 7867853 := bstep (se 3 (by rfl) ⟨1475222, by rfl⟩ : syracuseStep 7867853 = 2950445) B2950445
theorem B3935729 : Blo 1553474 3935729 := bstep (se 2 (by rfl) ⟨1475898, by rfl⟩ : syracuseStep 3935729 = 2951797) B2951797
theorem B7466509 : Blo 1553474 7466509 := bstep (se 3 (by rfl) ⟨1399970, by rfl⟩ : syracuseStep 7466509 = 2799941) B2799941
theorem B5246477 : Blo 1553474 5246477 := bstep (se 3 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 5246477 = 1967429) B1967429
theorem B1748515 : Blo 1553474 1748515 := bstep (se 1 (by rfl) ⟨1311386, by rfl⟩ : syracuseStep 1748515 = 2622773) B2622773
theorem B5246531 : Blo 1553474 5246531 := bstep (se 1 (by rfl) ⟨3934898, by rfl⟩ : syracuseStep 5246531 = 7869797) B7869797
theorem B2461283 : Blo 1553474 2461283 := bstep (se 1 (by rfl) ⟨1845962, by rfl⟩ : syracuseStep 2461283 = 3691925) B3691925
theorem B5901923 : Blo 1553474 5901923 := bstep (se 1 (by rfl) ⟨4426442, by rfl⟩ : syracuseStep 5901923 = 8852885) B8852885
theorem B2330225 : Blo 1553474 2330225 := bstep (se 2 (by rfl) ⟨873834, by rfl⟩ : syracuseStep 2330225 = 1747669) B1747669
theorem B2330243 : Blo 1553474 2330243 := bstep (se 1 (by rfl) ⟨1747682, by rfl⟩ : syracuseStep 2330243 = 3495365) B3495365
theorem B26545805 : Blo 1553474 26545805 := bstep (se 3 (by rfl) ⟨4977338, by rfl⟩ : syracuseStep 26545805 = 9954677) B9954677
theorem B2330273 : Blo 1553474 2330273 := bstep (se 2 (by rfl) ⟨873852, by rfl⟩ : syracuseStep 2330273 = 1747705) B1747705
theorem B2330291 : Blo 1553474 2330291 := bstep (se 1 (by rfl) ⟨1747718, by rfl⟩ : syracuseStep 2330291 = 3495437) B3495437
theorem B1748659 : Blo 1553474 1748659 := bstep (se 1 (by rfl) ⟨1311494, by rfl⟩ : syracuseStep 1748659 = 2622989) B2622989
theorem B6229709 : Blo 1553474 6229709 := bstep (se 3 (by rfl) ⟨1168070, by rfl⟩ : syracuseStep 6229709 = 2336141) B2336141
theorem B2330321 : Blo 1553474 2330321 := bstep (se 2 (by rfl) ⟨873870, by rfl⟩ : syracuseStep 2330321 = 1747741) B1747741
theorem B2330339 : Blo 1553474 2330339 := bstep (se 1 (by rfl) ⟨1747754, by rfl⟩ : syracuseStep 2330339 = 3495509) B3495509
theorem B1576675 : Blo 1553474 1576675 := bstep (se 1 (by rfl) ⟨1182506, by rfl⟩ : syracuseStep 1576675 = 2365013) B2365013
theorem B2330369 : Blo 1553474 2330369 := bstep (se 2 (by rfl) ⟨873888, by rfl⟩ : syracuseStep 2330369 = 1747777) B1747777
theorem B5598989 : Blo 1553474 5598989 := bstep (se 3 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 5598989 = 2099621) B2099621
theorem B2330387 : Blo 1553474 2330387 := bstep (se 1 (by rfl) ⟨1747790, by rfl⟩ : syracuseStep 2330387 = 3495581) B3495581
theorem B2330417 : Blo 1553474 2330417 := bstep (se 2 (by rfl) ⟨873906, by rfl⟩ : syracuseStep 2330417 = 1747813) B1747813
theorem B2330435 : Blo 1553474 2330435 := bstep (se 1 (by rfl) ⟨1747826, by rfl⟩ : syracuseStep 2330435 = 3495653) B3495653
theorem B1748803 : Blo 1553474 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B5246801 : Blo 1553474 5246801 := bstep (se 2 (by rfl) ⟨1967550, by rfl⟩ : syracuseStep 5246801 = 3935101) B3935101
theorem B2330465 : Blo 1553474 2330465 := bstep (se 2 (by rfl) ⟨873924, by rfl⟩ : syracuseStep 2330465 = 1747849) B1747849
theorem B2330483 : Blo 1553474 2330483 := bstep (se 1 (by rfl) ⟨1747862, by rfl⟩ : syracuseStep 2330483 = 3495725) B3495725
theorem B2330513 : Blo 1553474 2330513 := bstep (se 2 (by rfl) ⟨873942, by rfl⟩ : syracuseStep 2330513 = 1747885) B1747885
theorem B2330531 : Blo 1553474 2330531 := bstep (se 1 (by rfl) ⟨1747898, by rfl⟩ : syracuseStep 2330531 = 3495797) B3495797
theorem B2330561 : Blo 1553474 2330561 := bstep (se 2 (by rfl) ⟨873960, by rfl⟩ : syracuseStep 2330561 = 1747921) B1747921
theorem B2330579 : Blo 1553474 2330579 := bstep (se 1 (by rfl) ⟨1747934, by rfl⟩ : syracuseStep 2330579 = 3495869) B3495869
theorem B1748947 : Blo 1553474 1748947 := bstep (se 1 (by rfl) ⟨1311710, by rfl⟩ : syracuseStep 1748947 = 2623421) B2623421
theorem B8851427 : Blo 1553474 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B16814051 : Blo 1553474 16814051 := bstep (se 1 (by rfl) ⟨12610538, by rfl⟩ : syracuseStep 16814051 = 25221077) B25221077
theorem B2330609 : Blo 1553474 2330609 := bstep (se 2 (by rfl) ⟨873978, by rfl⟩ : syracuseStep 2330609 = 1747957) B1747957
theorem B2330627 : Blo 1553474 2330627 := bstep (se 1 (by rfl) ⟨1747970, by rfl⟩ : syracuseStep 2330627 = 3495941) B3495941
theorem B2330657 : Blo 1553474 2330657 := bstep (se 2 (by rfl) ⟨873996, by rfl⟩ : syracuseStep 2330657 = 1747993) B1747993
theorem B2330675 : Blo 1553474 2330675 := bstep (se 1 (by rfl) ⟨1748006, by rfl⟩ : syracuseStep 2330675 = 3496013) B3496013
theorem B10629197 : Blo 1553474 10629197 := bstep (se 3 (by rfl) ⟨1992974, by rfl⟩ : syracuseStep 10629197 = 3985949) B3985949
theorem B2330705 : Blo 1553474 2330705 := bstep (se 2 (by rfl) ⟨874014, by rfl⟩ : syracuseStep 2330705 = 1748029) B1748029
theorem B2330723 : Blo 1553474 2330723 := bstep (se 1 (by rfl) ⟨1748042, by rfl⟩ : syracuseStep 2330723 = 3496085) B3496085
theorem B1749091 : Blo 1553474 1749091 := bstep (se 1 (by rfl) ⟨1311818, by rfl⟩ : syracuseStep 1749091 = 2623637) B2623637
theorem B2330753 : Blo 1553474 2330753 := bstep (se 2 (by rfl) ⟨874032, by rfl⟩ : syracuseStep 2330753 = 1748065) B1748065
theorem B2330771 : Blo 1553474 2330771 := bstep (se 1 (by rfl) ⟨1748078, by rfl⟩ : syracuseStep 2330771 = 3496157) B3496157
theorem B2101411 : Blo 1553474 2101411 := bstep (se 1 (by rfl) ⟨1576058, by rfl⟩ : syracuseStep 2101411 = 3152117) B3152117
theorem B3322019 : Blo 1553474 3322019 := bstep (se 1 (by rfl) ⟨2491514, by rfl⟩ : syracuseStep 3322019 = 4983029) B4983029
theorem B2330801 : Blo 1553474 2330801 := bstep (se 2 (by rfl) ⟨874050, by rfl⟩ : syracuseStep 2330801 = 1748101) B1748101
theorem B2330819 : Blo 1553474 2330819 := bstep (se 1 (by rfl) ⟨1748114, by rfl⟩ : syracuseStep 2330819 = 3496229) B3496229
theorem B2330849 : Blo 1553474 2330849 := bstep (se 2 (by rfl) ⟨874068, by rfl⟩ : syracuseStep 2330849 = 1748137) B1748137
theorem B5902577 : Blo 1553474 5902577 := bstep (se 2 (by rfl) ⟨2213466, by rfl⟩ : syracuseStep 5902577 = 4426933) B4426933
theorem B2330867 : Blo 1553474 2330867 := bstep (se 1 (by rfl) ⟨1748150, by rfl⟩ : syracuseStep 2330867 = 3496301) B3496301
theorem B1749235 : Blo 1553474 1749235 := bstep (se 1 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 1749235 = 2623853) B2623853
theorem B2330897 : Blo 1553474 2330897 := bstep (se 2 (by rfl) ⟨874086, by rfl⟩ : syracuseStep 2330897 = 1748173) B1748173
theorem B2330915 : Blo 1553474 2330915 := bstep (se 1 (by rfl) ⟨1748186, by rfl⟩ : syracuseStep 2330915 = 3496373) B3496373
theorem B1995043 : Blo 1553474 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B2330945 : Blo 1553474 2330945 := bstep (se 2 (by rfl) ⟨874104, by rfl⟩ : syracuseStep 2330945 = 1748209) B1748209
theorem B2330963 : Blo 1553474 2330963 := bstep (se 1 (by rfl) ⟨1748222, by rfl⟩ : syracuseStep 2330963 = 3496445) B3496445
theorem B18903395 : Blo 1553474 18903395 := bstep (se 1 (by rfl) ⟨14177546, by rfl⟩ : syracuseStep 18903395 = 28355093) B28355093
theorem B5247341 : Blo 1553474 5247341 := bstep (se 3 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 5247341 = 1967753) B1967753
theorem B2330993 : Blo 1553474 2330993 := bstep (se 2 (by rfl) ⟨874122, by rfl⟩ : syracuseStep 2330993 = 1748245) B1748245
theorem B2331011 : Blo 1553474 2331011 := bstep (se 1 (by rfl) ⟨1748258, by rfl⟩ : syracuseStep 2331011 = 3496517) B3496517
theorem B1749379 : Blo 1553474 1749379 := bstep (se 1 (by rfl) ⟨1312034, by rfl⟩ : syracuseStep 1749379 = 2624069) B2624069
theorem B14184845 : Blo 1553474 14184845 := bstep (se 3 (by rfl) ⟨2659658, by rfl⟩ : syracuseStep 14184845 = 5319317) B5319317
theorem B2331041 : Blo 1553474 2331041 := bstep (se 2 (by rfl) ⟨874140, by rfl⟩ : syracuseStep 2331041 = 1748281) B1748281
theorem B5247395 : Blo 1553474 5247395 := bstep (se 1 (by rfl) ⟨3935546, by rfl⟩ : syracuseStep 5247395 = 7871093) B7871093
theorem B4428209 : Blo 1553474 4428209 := bstep (se 2 (by rfl) ⟨1660578, by rfl⟩ : syracuseStep 4428209 = 3321157) B3321157
theorem B2331059 : Blo 1553474 2331059 := bstep (se 1 (by rfl) ⟨1748294, by rfl⟩ : syracuseStep 2331059 = 3496589) B3496589
theorem B2331089 : Blo 1553474 2331089 := bstep (se 2 (by rfl) ⟨874158, by rfl⟩ : syracuseStep 2331089 = 1748317) B1748317
theorem B3936721 : Blo 1553474 3936721 := bstep (se 2 (by rfl) ⟨1476270, by rfl⟩ : syracuseStep 3936721 = 2952541) B2952541
theorem B2331107 : Blo 1553474 2331107 := bstep (se 1 (by rfl) ⟨1748330, by rfl⟩ : syracuseStep 2331107 = 3496661) B3496661
theorem B2331137 : Blo 1553474 2331137 := bstep (se 2 (by rfl) ⟨874176, by rfl⟩ : syracuseStep 2331137 = 1748353) B1748353
theorem B2331155 : Blo 1553474 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B1749523 : Blo 1553474 1749523 := bstep (se 1 (by rfl) ⟨1312142, by rfl⟩ : syracuseStep 1749523 = 2624285) B2624285
theorem B2331185 : Blo 1553474 2331185 := bstep (se 2 (by rfl) ⟨874194, by rfl⟩ : syracuseStep 2331185 = 1748389) B1748389
theorem B9581105 : Blo 1553474 9581105 := bstep (se 2 (by rfl) ⟨3592914, by rfl⟩ : syracuseStep 9581105 = 7185829) B7185829
theorem B6640177 : Blo 1553474 6640177 := bstep (se 2 (by rfl) ⟨2490066, by rfl⟩ : syracuseStep 6640177 = 4980133) B4980133
theorem B2331203 : Blo 1553474 2331203 := bstep (se 1 (by rfl) ⟨1748402, by rfl⟩ : syracuseStep 2331203 = 3496805) B3496805
theorem B2331233 : Blo 1553474 2331233 := bstep (se 2 (by rfl) ⟨874212, by rfl⟩ : syracuseStep 2331233 = 1748425) B1748425
theorem B2331251 : Blo 1553474 2331251 := bstep (se 1 (by rfl) ⟨1748438, by rfl⟩ : syracuseStep 2331251 = 3496877) B3496877
theorem B2101891 : Blo 1553474 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B2331281 : Blo 1553474 2331281 := bstep (se 2 (by rfl) ⟨874230, by rfl⟩ : syracuseStep 2331281 = 1748461) B1748461
theorem B2658977 : Blo 1553474 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B2331299 : Blo 1553474 2331299 := bstep (se 1 (by rfl) ⟨1748474, by rfl⟩ : syracuseStep 2331299 = 3496949) B3496949
theorem B1749667 : Blo 1553474 1749667 := bstep (se 1 (by rfl) ⟨1312250, by rfl⟩ : syracuseStep 1749667 = 2624501) B2624501
theorem B5247665 : Blo 1553474 5247665 := bstep (se 2 (by rfl) ⟨1967874, by rfl⟩ : syracuseStep 5247665 = 3935749) B3935749
theorem B2331329 : Blo 1553474 2331329 := bstep (se 2 (by rfl) ⟨874248, by rfl⟩ : syracuseStep 2331329 = 1748497) B1748497
theorem B2331347 : Blo 1553474 2331347 := bstep (se 1 (by rfl) ⟨1748510, by rfl⟩ : syracuseStep 2331347 = 3497021) B3497021
theorem B3936995 : Blo 1553474 3936995 := bstep (se 1 (by rfl) ⟨2952746, by rfl⟩ : syracuseStep 3936995 = 5905493) B5905493
theorem B2331377 : Blo 1553474 2331377 := bstep (se 2 (by rfl) ⟨874266, by rfl⟩ : syracuseStep 2331377 = 1748533) B1748533
theorem B2331395 : Blo 1553474 2331395 := bstep (se 1 (by rfl) ⟨1748546, by rfl⟩ : syracuseStep 2331395 = 3497093) B3497093
theorem B2331425 : Blo 1553474 2331425 := bstep (se 2 (by rfl) ⟨874284, by rfl⟩ : syracuseStep 2331425 = 1748569) B1748569
theorem B2331443 : Blo 1553474 2331443 := bstep (se 1 (by rfl) ⟨1748582, by rfl⟩ : syracuseStep 2331443 = 3497165) B3497165
theorem B1749811 : Blo 1553474 1749811 := bstep (se 1 (by rfl) ⟨1312358, by rfl⟩ : syracuseStep 1749811 = 2624717) B2624717
theorem B2331473 : Blo 1553474 2331473 := bstep (se 2 (by rfl) ⟨874302, by rfl⟩ : syracuseStep 2331473 = 1748605) B1748605
theorem B2331491 : Blo 1553474 2331491 := bstep (se 1 (by rfl) ⟨1748618, by rfl⟩ : syracuseStep 2331491 = 3497237) B3497237
theorem B2331521 : Blo 1553474 2331521 := bstep (se 2 (by rfl) ⟨874320, by rfl⟩ : syracuseStep 2331521 = 1748641) B1748641
theorem B3888017 : Blo 1553474 3888017 := bstep (se 2 (by rfl) ⟨1458006, by rfl⟩ : syracuseStep 3888017 = 2916013) B2916013
theorem B2331539 : Blo 1553474 2331539 := bstep (se 1 (by rfl) ⟨1748654, by rfl⟩ : syracuseStep 2331539 = 3497309) B3497309
theorem B4977571 : Blo 1553474 4977571 := bstep (se 1 (by rfl) ⟨3733178, by rfl⟩ : syracuseStep 4977571 = 7466357) B7466357
theorem B3937187 : Blo 1553474 3937187 := bstep (se 1 (by rfl) ⟨2952890, by rfl⟩ : syracuseStep 3937187 = 5905781) B5905781
theorem B2331569 : Blo 1553474 2331569 := bstep (se 2 (by rfl) ⟨874338, by rfl⟩ : syracuseStep 2331569 = 1748677) B1748677
theorem B2331587 : Blo 1553474 2331587 := bstep (se 1 (by rfl) ⟨1748690, by rfl⟩ : syracuseStep 2331587 = 3497381) B3497381
theorem B8852429 : Blo 1553474 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B2331617 : Blo 1553474 2331617 := bstep (se 2 (by rfl) ⟨874356, by rfl⟩ : syracuseStep 2331617 = 1748713) B1748713
theorem B5116913 : Blo 1553474 5116913 := bstep (se 2 (by rfl) ⟨1918842, by rfl⟩ : syracuseStep 5116913 = 3837685) B3837685
theorem B2331635 : Blo 1553474 2331635 := bstep (se 1 (by rfl) ⟨1748726, by rfl⟩ : syracuseStep 2331635 = 3497453) B3497453
theorem B2659331 : Blo 1553474 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B2331665 : Blo 1553474 2331665 := bstep (se 2 (by rfl) ⟨874374, by rfl⟩ : syracuseStep 2331665 = 1748749) B1748749
theorem B2331683 : Blo 1553474 2331683 := bstep (se 1 (by rfl) ⟨1748762, by rfl⟩ : syracuseStep 2331683 = 3497525) B3497525
theorem B2331713 : Blo 1553474 2331713 := bstep (se 2 (by rfl) ⟨874392, by rfl⟩ : syracuseStep 2331713 = 1748785) B1748785
theorem B1553475 : Blo 1553474 1553475 := bstep (se 1 (by rfl) ⟨1165106, by rfl⟩ : syracuseStep 1553475 = 2330213) B2330213
theorem B4428881 : Blo 1553474 4428881 := bstep (se 2 (by rfl) ⟨1660830, by rfl⟩ : syracuseStep 4428881 = 3321661) B3321661
theorem B1553491 : Blo 1553474 1553491 := bstep (se 1 (by rfl) ⟨1165118, by rfl⟩ : syracuseStep 1553491 = 2330237) B2330237
theorem B2331731 : Blo 1553474 2331731 := bstep (se 1 (by rfl) ⟨1748798, by rfl⟩ : syracuseStep 2331731 = 3497597) B3497597
theorem B1553507 : Blo 1553474 1553507 := bstep (se 1 (by rfl) ⟨1165130, by rfl⟩ : syracuseStep 1553507 = 2330261) B2330261
theorem B2331761 : Blo 1553474 2331761 := bstep (se 2 (by rfl) ⟨874410, by rfl⟩ : syracuseStep 2331761 = 1748821) B1748821
theorem B1553523 : Blo 1553474 1553523 := bstep (se 1 (by rfl) ⟨1165142, by rfl⟩ : syracuseStep 1553523 = 2330285) B2330285
theorem B1553539 : Blo 1553474 1553539 := bstep (se 1 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 1553539 = 2330309) B2330309
theorem B2331779 : Blo 1553474 2331779 := bstep (se 1 (by rfl) ⟨1748834, by rfl⟩ : syracuseStep 2331779 = 3497669) B3497669
theorem B1553555 : Blo 1553474 1553555 := bstep (se 1 (by rfl) ⟨1165166, by rfl⟩ : syracuseStep 1553555 = 2330333) B2330333
theorem B2331809 : Blo 1553474 2331809 := bstep (se 2 (by rfl) ⟨874428, by rfl⟩ : syracuseStep 2331809 = 1748857) B1748857
theorem B1553571 : Blo 1553474 1553571 := bstep (se 1 (by rfl) ⟨1165178, by rfl⟩ : syracuseStep 1553571 = 2330357) B2330357
theorem B1553587 : Blo 1553474 1553587 := bstep (se 1 (by rfl) ⟨1165190, by rfl⟩ : syracuseStep 1553587 = 2330381) B2330381
theorem B2331827 : Blo 1553474 2331827 := bstep (se 1 (by rfl) ⟨1748870, by rfl⟩ : syracuseStep 2331827 = 3497741) B3497741
theorem B1553603 : Blo 1553474 1553603 := bstep (se 1 (by rfl) ⟨1165202, by rfl⟩ : syracuseStep 1553603 = 2330405) B2330405
theorem B5248205 : Blo 1553474 5248205 := bstep (se 3 (by rfl) ⟨984038, by rfl⟩ : syracuseStep 5248205 = 1968077) B1968077
theorem B2331857 : Blo 1553474 2331857 := bstep (se 2 (by rfl) ⟨874446, by rfl⟩ : syracuseStep 2331857 = 1748893) B1748893
theorem B1553619 : Blo 1553474 1553619 := bstep (se 1 (by rfl) ⟨1165214, by rfl⟩ : syracuseStep 1553619 = 2330429) B2330429
theorem B1553635 : Blo 1553474 1553635 := bstep (se 1 (by rfl) ⟨1165226, by rfl⟩ : syracuseStep 1553635 = 2330453) B2330453
theorem B2331875 : Blo 1553474 2331875 := bstep (se 1 (by rfl) ⟨1748906, by rfl⟩ : syracuseStep 2331875 = 3497813) B3497813
theorem B1553651 : Blo 1553474 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B2331905 : Blo 1553474 2331905 := bstep (se 2 (by rfl) ⟨874464, by rfl⟩ : syracuseStep 2331905 = 1748929) B1748929
theorem B1553667 : Blo 1553474 1553667 := bstep (se 1 (by rfl) ⟨1165250, by rfl⟩ : syracuseStep 1553667 = 2330501) B2330501
theorem B5248259 : Blo 1553474 5248259 := bstep (se 1 (by rfl) ⟨3936194, by rfl⟩ : syracuseStep 5248259 = 7872389) B7872389
theorem B1553683 : Blo 1553474 1553683 := bstep (se 1 (by rfl) ⟨1165262, by rfl⟩ : syracuseStep 1553683 = 2330525) B2330525
theorem B2331923 : Blo 1553474 2331923 := bstep (se 1 (by rfl) ⟨1748942, by rfl⟩ : syracuseStep 2331923 = 3497885) B3497885
theorem B1553699 : Blo 1553474 1553699 := bstep (se 1 (by rfl) ⟨1165274, by rfl⟩ : syracuseStep 1553699 = 2330549) B2330549
theorem B2331953 : Blo 1553474 2331953 := bstep (se 2 (by rfl) ⟨874482, by rfl⟩ : syracuseStep 2331953 = 1748965) B1748965
theorem B1553715 : Blo 1553474 1553715 := bstep (se 1 (by rfl) ⟨1165286, by rfl⟩ : syracuseStep 1553715 = 2330573) B2330573
theorem B1553731 : Blo 1553474 1553731 := bstep (se 1 (by rfl) ⟨1165298, by rfl⟩ : syracuseStep 1553731 = 2330597) B2330597
theorem B2331971 : Blo 1553474 2331971 := bstep (se 1 (by rfl) ⟨1748978, by rfl⟩ : syracuseStep 2331971 = 3497957) B3497957
theorem B1553747 : Blo 1553474 1553747 := bstep (se 1 (by rfl) ⟨1165310, by rfl⟩ : syracuseStep 1553747 = 2330621) B2330621
theorem B2332001 : Blo 1553474 2332001 := bstep (se 2 (by rfl) ⟨874500, by rfl⟩ : syracuseStep 2332001 = 1749001) B1749001
theorem B1553763 : Blo 1553474 1553763 := bstep (se 1 (by rfl) ⟨1165322, by rfl⟩ : syracuseStep 1553763 = 2330645) B2330645
theorem B3151217 : Blo 1553474 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B1553779 : Blo 1553474 1553779 := bstep (se 1 (by rfl) ⟨1165334, by rfl⟩ : syracuseStep 1553779 = 2330669) B2330669
theorem B2332019 : Blo 1553474 2332019 := bstep (se 1 (by rfl) ⟨1749014, by rfl⟩ : syracuseStep 2332019 = 3498029) B3498029
theorem B1553795 : Blo 1553474 1553795 := bstep (se 1 (by rfl) ⟨1165346, by rfl⟩ : syracuseStep 1553795 = 2330693) B2330693
theorem B2332049 : Blo 1553474 2332049 := bstep (se 2 (by rfl) ⟨874518, by rfl⟩ : syracuseStep 2332049 = 1749037) B1749037
theorem B1553811 : Blo 1553474 1553811 := bstep (se 1 (by rfl) ⟨1165358, by rfl⟩ : syracuseStep 1553811 = 2330717) B2330717
theorem B1553827 : Blo 1553474 1553827 := bstep (se 1 (by rfl) ⟨1165370, by rfl⟩ : syracuseStep 1553827 = 2330741) B2330741
theorem B2332067 : Blo 1553474 2332067 := bstep (se 1 (by rfl) ⟨1749050, by rfl⟩ : syracuseStep 2332067 = 3498101) B3498101
theorem B1553843 : Blo 1553474 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B2332097 : Blo 1553474 2332097 := bstep (se 2 (by rfl) ⟨874536, by rfl⟩ : syracuseStep 2332097 = 1749073) B1749073
theorem B1553859 : Blo 1553474 1553859 := bstep (se 1 (by rfl) ⟨1165394, by rfl⟩ : syracuseStep 1553859 = 2330789) B2330789
theorem B1553875 : Blo 1553474 1553875 := bstep (se 1 (by rfl) ⟨1165406, by rfl⟩ : syracuseStep 1553875 = 2330813) B2330813
theorem B2332115 : Blo 1553474 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B1553891 : Blo 1553474 1553891 := bstep (se 1 (by rfl) ⟨1165418, by rfl⟩ : syracuseStep 1553891 = 2330837) B2330837
theorem B2332145 : Blo 1553474 2332145 := bstep (se 2 (by rfl) ⟨874554, by rfl⟩ : syracuseStep 2332145 = 1749109) B1749109
theorem B1553907 : Blo 1553474 1553907 := bstep (se 1 (by rfl) ⟨1165430, by rfl⟩ : syracuseStep 1553907 = 2330861) B2330861
theorem B1553923 : Blo 1553474 1553923 := bstep (se 1 (by rfl) ⟨1165442, by rfl⟩ : syracuseStep 1553923 = 2330885) B2330885
theorem B2332163 : Blo 1553474 2332163 := bstep (se 1 (by rfl) ⟨1749122, by rfl⟩ : syracuseStep 2332163 = 3498245) B3498245
theorem B5248529 : Blo 1553474 5248529 := bstep (se 2 (by rfl) ⟨1968198, by rfl⟩ : syracuseStep 5248529 = 3936397) B3936397
theorem B1553939 : Blo 1553474 1553939 := bstep (se 1 (by rfl) ⟨1165454, by rfl⟩ : syracuseStep 1553939 = 2330909) B2330909
theorem B2332193 : Blo 1553474 2332193 := bstep (se 2 (by rfl) ⟨874572, by rfl⟩ : syracuseStep 2332193 = 1749145) B1749145
theorem B1553955 : Blo 1553474 1553955 := bstep (se 1 (by rfl) ⟨1165466, by rfl⟩ : syracuseStep 1553955 = 2330933) B2330933
theorem B3495473 : Blo 1553474 3495473 := bstep (se 2 (by rfl) ⟨1310802, by rfl⟩ : syracuseStep 3495473 = 2621605) B2621605
theorem B1553971 : Blo 1553474 1553971 := bstep (se 1 (by rfl) ⟨1165478, by rfl⟩ : syracuseStep 1553971 = 2330957) B2330957
theorem B2332211 : Blo 1553474 2332211 := bstep (se 1 (by rfl) ⟨1749158, by rfl⟩ : syracuseStep 2332211 = 3498317) B3498317
theorem B3495491 : Blo 1553474 3495491 := bstep (se 1 (by rfl) ⟨2621618, by rfl⟩ : syracuseStep 3495491 = 5243237) B5243237
theorem B1553987 : Blo 1553474 1553987 := bstep (se 1 (by rfl) ⟨1165490, by rfl⟩ : syracuseStep 1553987 = 2330981) B2330981
theorem B2332241 : Blo 1553474 2332241 := bstep (se 2 (by rfl) ⟨874590, by rfl⟩ : syracuseStep 2332241 = 1749181) B1749181
theorem B1554003 : Blo 1553474 1554003 := bstep (se 1 (by rfl) ⟨1165502, by rfl⟩ : syracuseStep 1554003 = 2331005) B2331005
theorem B1554019 : Blo 1553474 1554019 := bstep (se 1 (by rfl) ⟨1165514, by rfl⟩ : syracuseStep 1554019 = 2331029) B2331029
theorem B6731363 : Blo 1553474 6731363 := bstep (se 1 (by rfl) ⟨5048522, by rfl⟩ : syracuseStep 6731363 = 10097045) B10097045
theorem B2332259 : Blo 1553474 2332259 := bstep (se 1 (by rfl) ⟨1749194, by rfl⟩ : syracuseStep 2332259 = 3498389) B3498389
theorem B1554035 : Blo 1553474 1554035 := bstep (se 1 (by rfl) ⟨1165526, by rfl⟩ : syracuseStep 1554035 = 2331053) B2331053
theorem B2332289 : Blo 1553474 2332289 := bstep (se 2 (by rfl) ⟨874608, by rfl⟩ : syracuseStep 2332289 = 1749217) B1749217
theorem B1554051 : Blo 1553474 1554051 := bstep (se 1 (by rfl) ⟨1165538, by rfl⟩ : syracuseStep 1554051 = 2331077) B2331077
theorem B1554067 : Blo 1553474 1554067 := bstep (se 1 (by rfl) ⟨1165550, by rfl⟩ : syracuseStep 1554067 = 2331101) B2331101
theorem B2332307 : Blo 1553474 2332307 := bstep (se 1 (by rfl) ⟨1749230, by rfl⟩ : syracuseStep 2332307 = 3498461) B3498461
theorem B1554083 : Blo 1553474 1554083 := bstep (se 1 (by rfl) ⟨1165562, by rfl⟩ : syracuseStep 1554083 = 2331125) B2331125
theorem B5904035 : Blo 1553474 5904035 := bstep (se 1 (by rfl) ⟨4428026, by rfl⟩ : syracuseStep 5904035 = 8856053) B8856053
theorem B2332337 : Blo 1553474 2332337 := bstep (se 2 (by rfl) ⟨874626, by rfl⟩ : syracuseStep 2332337 = 1749253) B1749253
theorem B5904049 : Blo 1553474 5904049 := bstep (se 2 (by rfl) ⟨2214018, by rfl⟩ : syracuseStep 5904049 = 4428037) B4428037
theorem B1554099 : Blo 1553474 1554099 := bstep (se 1 (by rfl) ⟨1165574, by rfl⟩ : syracuseStep 1554099 = 2331149) B2331149
theorem B1554115 : Blo 1553474 1554115 := bstep (se 1 (by rfl) ⟨1165586, by rfl⟩ : syracuseStep 1554115 = 2331173) B2331173
theorem B2332355 : Blo 1553474 2332355 := bstep (se 1 (by rfl) ⟨1749266, by rfl⟩ : syracuseStep 2332355 = 3498533) B3498533
theorem B1554131 : Blo 1553474 1554131 := bstep (se 1 (by rfl) ⟨1165598, by rfl⟩ : syracuseStep 1554131 = 2331197) B2331197
theorem B2332385 : Blo 1553474 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B1554147 : Blo 1553474 1554147 := bstep (se 1 (by rfl) ⟨1165610, by rfl⟩ : syracuseStep 1554147 = 2331221) B2331221
theorem B1554163 : Blo 1553474 1554163 := bstep (se 1 (by rfl) ⟨1165622, by rfl⟩ : syracuseStep 1554163 = 2331245) B2331245
theorem B2332403 : Blo 1553474 2332403 := bstep (se 1 (by rfl) ⟨1749302, by rfl⟩ : syracuseStep 2332403 = 3498605) B3498605
theorem B1554179 : Blo 1553474 1554179 := bstep (se 1 (by rfl) ⟨1165634, by rfl⟩ : syracuseStep 1554179 = 2331269) B2331269
theorem B2332433 : Blo 1553474 2332433 := bstep (se 2 (by rfl) ⟨874662, by rfl⟩ : syracuseStep 2332433 = 1749325) B1749325
theorem B1554195 : Blo 1553474 1554195 := bstep (se 1 (by rfl) ⟨1165646, by rfl⟩ : syracuseStep 1554195 = 2331293) B2331293
theorem B1554211 : Blo 1553474 1554211 := bstep (se 1 (by rfl) ⟨1165658, by rfl⟩ : syracuseStep 1554211 = 2331317) B2331317
theorem B2332451 : Blo 1553474 2332451 := bstep (se 1 (by rfl) ⟨1749338, by rfl⟩ : syracuseStep 2332451 = 3498677) B3498677
theorem B1554227 : Blo 1553474 1554227 := bstep (se 1 (by rfl) ⟨1165670, by rfl⟩ : syracuseStep 1554227 = 2331341) B2331341
theorem B2332481 : Blo 1553474 2332481 := bstep (se 2 (by rfl) ⟨874680, by rfl⟩ : syracuseStep 2332481 = 1749361) B1749361
theorem B1554243 : Blo 1553474 1554243 := bstep (se 1 (by rfl) ⟨1165682, by rfl⟩ : syracuseStep 1554243 = 2331365) B2331365
theorem B3495761 : Blo 1553474 3495761 := bstep (se 2 (by rfl) ⟨1310910, by rfl⟩ : syracuseStep 3495761 = 2621821) B2621821
theorem B1554259 : Blo 1553474 1554259 := bstep (se 1 (by rfl) ⟨1165694, by rfl⟩ : syracuseStep 1554259 = 2331389) B2331389
theorem B2332499 : Blo 1553474 2332499 := bstep (se 1 (by rfl) ⟨1749374, by rfl⟩ : syracuseStep 2332499 = 3498749) B3498749
theorem B3495779 : Blo 1553474 3495779 := bstep (se 1 (by rfl) ⟨2621834, by rfl⟩ : syracuseStep 3495779 = 5243669) B5243669
theorem B1554275 : Blo 1553474 1554275 := bstep (se 1 (by rfl) ⟨1165706, by rfl⟩ : syracuseStep 1554275 = 2331413) B2331413
theorem B2332529 : Blo 1553474 2332529 := bstep (se 2 (by rfl) ⟨874698, by rfl⟩ : syracuseStep 2332529 = 1749397) B1749397
theorem B1554291 : Blo 1553474 1554291 := bstep (se 1 (by rfl) ⟨1165718, by rfl⟩ : syracuseStep 1554291 = 2331437) B2331437
theorem B1554307 : Blo 1553474 1554307 := bstep (se 1 (by rfl) ⟨1165730, by rfl⟩ : syracuseStep 1554307 = 2331461) B2331461
theorem B2332547 : Blo 1553474 2332547 := bstep (se 1 (by rfl) ⟨1749410, by rfl⟩ : syracuseStep 2332547 = 3498821) B3498821
theorem B11802509 : Blo 1553474 11802509 := bstep (se 3 (by rfl) ⟨2212970, by rfl⟩ : syracuseStep 11802509 = 4425941) B4425941
theorem B1554323 : Blo 1553474 1554323 := bstep (se 1 (by rfl) ⟨1165742, by rfl⟩ : syracuseStep 1554323 = 2331485) B2331485
theorem B2332577 : Blo 1553474 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B1554339 : Blo 1553474 1554339 := bstep (se 1 (by rfl) ⟨1165754, by rfl⟩ : syracuseStep 1554339 = 2331509) B2331509
theorem B1554355 : Blo 1553474 1554355 := bstep (se 1 (by rfl) ⟨1165766, by rfl⟩ : syracuseStep 1554355 = 2331533) B2331533
theorem B2332595 : Blo 1553474 2332595 := bstep (se 1 (by rfl) ⟨1749446, by rfl⟩ : syracuseStep 2332595 = 3498893) B3498893
theorem B1554371 : Blo 1553474 1554371 := bstep (se 1 (by rfl) ⟨1165778, by rfl⟩ : syracuseStep 1554371 = 2331557) B2331557
theorem B12605381 : Blo 1553474 12605381 := bstep (se 4 (by rfl) ⟨1181754, by rfl⟩ : syracuseStep 12605381 = 2363509) B2363509
theorem B1554387 : Blo 1553474 1554387 := bstep (se 1 (by rfl) ⟨1165790, by rfl⟩ : syracuseStep 1554387 = 2331581) B2331581
theorem B2332625 : Blo 1553474 2332625 := bstep (se 2 (by rfl) ⟨874734, by rfl⟩ : syracuseStep 2332625 = 1749469) B1749469
theorem B1554403 : Blo 1553474 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B2332643 : Blo 1553474 2332643 := bstep (se 1 (by rfl) ⟨1749482, by rfl⟩ : syracuseStep 2332643 = 3498965) B3498965
theorem B1554419 : Blo 1553474 1554419 := bstep (se 1 (by rfl) ⟨1165814, by rfl⟩ : syracuseStep 1554419 = 2331629) B2331629
theorem B2332673 : Blo 1553474 2332673 := bstep (se 2 (by rfl) ⟨874752, by rfl⟩ : syracuseStep 2332673 = 1749505) B1749505
theorem B1554435 : Blo 1553474 1554435 := bstep (se 1 (by rfl) ⟨1165826, by rfl⟩ : syracuseStep 1554435 = 2331653) B2331653
theorem B1554451 : Blo 1553474 1554451 := bstep (se 1 (by rfl) ⟨1165838, by rfl⟩ : syracuseStep 1554451 = 2331677) B2331677
theorem B2332691 : Blo 1553474 2332691 := bstep (se 1 (by rfl) ⟨1749518, by rfl⟩ : syracuseStep 2332691 = 3499037) B3499037
theorem B1554467 : Blo 1553474 1554467 := bstep (se 1 (by rfl) ⟨1165850, by rfl⟩ : syracuseStep 1554467 = 2331701) B2331701
theorem B5249069 : Blo 1553474 5249069 := bstep (se 3 (by rfl) ⟨984200, by rfl⟩ : syracuseStep 5249069 = 1968401) B1968401
theorem B2242609 : Blo 1553474 2242609 := bstep (se 2 (by rfl) ⟨840978, by rfl⟩ : syracuseStep 2242609 = 1681957) B1681957
theorem B2332721 : Blo 1553474 2332721 := bstep (se 2 (by rfl) ⟨874770, by rfl⟩ : syracuseStep 2332721 = 1749541) B1749541
theorem B1554483 : Blo 1553474 1554483 := bstep (se 1 (by rfl) ⟨1165862, by rfl⟩ : syracuseStep 1554483 = 2331725) B2331725
theorem B1554499 : Blo 1553474 1554499 := bstep (se 1 (by rfl) ⟨1165874, by rfl⟩ : syracuseStep 1554499 = 2331749) B2331749
theorem B2332739 : Blo 1553474 2332739 := bstep (se 1 (by rfl) ⟨1749554, by rfl⟩ : syracuseStep 2332739 = 3499109) B3499109
theorem B2799697 : Blo 1553474 2799697 := bstep (se 2 (by rfl) ⟨1049886, by rfl⟩ : syracuseStep 2799697 = 2099773) B2099773
theorem B1554515 : Blo 1553474 1554515 := bstep (se 1 (by rfl) ⟨1165886, by rfl⟩ : syracuseStep 1554515 = 2331773) B2331773
theorem B2242657 : Blo 1553474 2242657 := bstep (se 2 (by rfl) ⟨840996, by rfl⟩ : syracuseStep 2242657 = 1681993) B1681993
theorem B2332769 : Blo 1553474 2332769 := bstep (se 2 (by rfl) ⟨874788, by rfl⟩ : syracuseStep 2332769 = 1749577) B1749577
theorem B1554531 : Blo 1553474 1554531 := bstep (se 1 (by rfl) ⟨1165898, by rfl⟩ : syracuseStep 1554531 = 2331797) B2331797
theorem B5249123 : Blo 1553474 5249123 := bstep (se 1 (by rfl) ⟨3936842, by rfl⟩ : syracuseStep 5249123 = 7873685) B7873685
theorem B3496049 : Blo 1553474 3496049 := bstep (se 2 (by rfl) ⟨1311018, by rfl⟩ : syracuseStep 3496049 = 2622037) B2622037
theorem B1554547 : Blo 1553474 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B2332787 : Blo 1553474 2332787 := bstep (se 1 (by rfl) ⟨1749590, by rfl⟩ : syracuseStep 2332787 = 3499181) B3499181
theorem B3496067 : Blo 1553474 3496067 := bstep (se 1 (by rfl) ⟨2622050, by rfl⟩ : syracuseStep 3496067 = 5244101) B5244101
theorem B1554563 : Blo 1553474 1554563 := bstep (se 1 (by rfl) ⟨1165922, by rfl⟩ : syracuseStep 1554563 = 2331845) B2331845
theorem B2332817 : Blo 1553474 2332817 := bstep (se 2 (by rfl) ⟨874806, by rfl⟩ : syracuseStep 2332817 = 1749613) B1749613
theorem B1554579 : Blo 1553474 1554579 := bstep (se 1 (by rfl) ⟨1165934, by rfl⟩ : syracuseStep 1554579 = 2331869) B2331869
theorem B1554595 : Blo 1553474 1554595 := bstep (se 1 (by rfl) ⟨1165946, by rfl⟩ : syracuseStep 1554595 = 2331893) B2331893
theorem B2332835 : Blo 1553474 2332835 := bstep (se 1 (by rfl) ⟨1749626, by rfl⟩ : syracuseStep 2332835 = 3499253) B3499253
theorem B1554611 : Blo 1553474 1554611 := bstep (se 1 (by rfl) ⟨1165958, by rfl⟩ : syracuseStep 1554611 = 2331917) B2331917
theorem B2332865 : Blo 1553474 2332865 := bstep (se 2 (by rfl) ⟨874824, by rfl⟩ : syracuseStep 2332865 = 1749649) B1749649
theorem B1554627 : Blo 1553474 1554627 := bstep (se 1 (by rfl) ⟨1165970, by rfl⟩ : syracuseStep 1554627 = 2331941) B2331941
theorem B2488529 : Blo 1553474 2488529 := bstep (se 2 (by rfl) ⟨933198, by rfl⟩ : syracuseStep 2488529 = 1866397) B1866397
theorem B1554643 : Blo 1553474 1554643 := bstep (se 1 (by rfl) ⟨1165982, by rfl⟩ : syracuseStep 1554643 = 2331965) B2331965
theorem B2332883 : Blo 1553474 2332883 := bstep (se 1 (by rfl) ⟨1749662, by rfl⟩ : syracuseStep 2332883 = 3499325) B3499325
theorem B1554659 : Blo 1553474 1554659 := bstep (se 1 (by rfl) ⟨1165994, by rfl⟩ : syracuseStep 1554659 = 2331989) B2331989
theorem B2332913 : Blo 1553474 2332913 := bstep (se 2 (by rfl) ⟨874842, by rfl⟩ : syracuseStep 2332913 = 1749685) B1749685
theorem B1554675 : Blo 1553474 1554675 := bstep (se 1 (by rfl) ⟨1166006, by rfl⟩ : syracuseStep 1554675 = 2332013) B2332013
theorem B1554691 : Blo 1553474 1554691 := bstep (se 1 (by rfl) ⟨1166018, by rfl⟩ : syracuseStep 1554691 = 2332037) B2332037
theorem B2332931 : Blo 1553474 2332931 := bstep (se 1 (by rfl) ⟨1749698, by rfl⟩ : syracuseStep 2332931 = 3499397) B3499397
theorem B1554707 : Blo 1553474 1554707 := bstep (se 1 (by rfl) ⟨1166030, by rfl⟩ : syracuseStep 1554707 = 2332061) B2332061
theorem B2332961 : Blo 1553474 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B1554723 : Blo 1553474 1554723 := bstep (se 1 (by rfl) ⟨1166042, by rfl⟩ : syracuseStep 1554723 = 2332085) B2332085
theorem B7870769 : Blo 1553474 7870769 := bstep (se 2 (by rfl) ⟨2951538, by rfl⟩ : syracuseStep 7870769 = 5903077) B5903077
theorem B1554739 : Blo 1553474 1554739 := bstep (se 1 (by rfl) ⟨1166054, by rfl⟩ : syracuseStep 1554739 = 2332109) B2332109
theorem B2332979 : Blo 1553474 2332979 := bstep (se 1 (by rfl) ⟨1749734, by rfl⟩ : syracuseStep 2332979 = 3499469) B3499469
theorem B1554755 : Blo 1553474 1554755 := bstep (se 1 (by rfl) ⟨1166066, by rfl⟩ : syracuseStep 1554755 = 2332133) B2332133
theorem B2333009 : Blo 1553474 2333009 := bstep (se 2 (by rfl) ⟨874878, by rfl⟩ : syracuseStep 2333009 = 1749757) B1749757
theorem B1554771 : Blo 1553474 1554771 := bstep (se 1 (by rfl) ⟨1166078, by rfl⟩ : syracuseStep 1554771 = 2332157) B2332157
theorem B1554787 : Blo 1553474 1554787 := bstep (se 1 (by rfl) ⟨1166090, by rfl⟩ : syracuseStep 1554787 = 2332181) B2332181
theorem B2333027 : Blo 1553474 2333027 := bstep (se 1 (by rfl) ⟨1749770, by rfl⟩ : syracuseStep 2333027 = 3499541) B3499541
theorem B5249393 : Blo 1553474 5249393 := bstep (se 2 (by rfl) ⟨1968522, by rfl⟩ : syracuseStep 5249393 = 3937045) B3937045
theorem B1554803 : Blo 1553474 1554803 := bstep (se 1 (by rfl) ⟨1166102, by rfl⟩ : syracuseStep 1554803 = 2332205) B2332205
theorem B1554819 : Blo 1553474 1554819 := bstep (se 1 (by rfl) ⟨1166114, by rfl⟩ : syracuseStep 1554819 = 2332229) B2332229
theorem B2333057 : Blo 1553474 2333057 := bstep (se 2 (by rfl) ⟨874896, by rfl⟩ : syracuseStep 2333057 = 1749793) B1749793
theorem B7567757 : Blo 1553474 7567757 := bstep (se 3 (by rfl) ⟨1418954, by rfl⟩ : syracuseStep 7567757 = 2837909) B2837909
theorem B3496337 : Blo 1553474 3496337 := bstep (se 2 (by rfl) ⟨1311126, by rfl⟩ : syracuseStep 3496337 = 2622253) B2622253
theorem B1554835 : Blo 1553474 1554835 := bstep (se 1 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 1554835 = 2332253) B2332253
theorem B2333075 : Blo 1553474 2333075 := bstep (se 1 (by rfl) ⟨1749806, by rfl⟩ : syracuseStep 2333075 = 3499613) B3499613
theorem B3496355 : Blo 1553474 3496355 := bstep (se 1 (by rfl) ⟨2622266, by rfl⟩ : syracuseStep 3496355 = 5244533) B5244533
theorem B1554851 : Blo 1553474 1554851 := bstep (se 1 (by rfl) ⟨1166138, by rfl⟩ : syracuseStep 1554851 = 2332277) B2332277
theorem B7092643 : Blo 1553474 7092643 := bstep (se 1 (by rfl) ⟨5319482, by rfl⟩ : syracuseStep 7092643 = 10638965) B10638965
theorem B2333105 : Blo 1553474 2333105 := bstep (se 2 (by rfl) ⟨874914, by rfl⟩ : syracuseStep 2333105 = 1749829) B1749829
theorem B1554867 : Blo 1553474 1554867 := bstep (se 1 (by rfl) ⟨1166150, by rfl⟩ : syracuseStep 1554867 = 2332301) B2332301
theorem B1554883 : Blo 1553474 1554883 := bstep (se 1 (by rfl) ⟨1166162, by rfl⟩ : syracuseStep 1554883 = 2332325) B2332325
theorem B2333123 : Blo 1553474 2333123 := bstep (se 1 (by rfl) ⟨1749842, by rfl⟩ : syracuseStep 2333123 = 3499685) B3499685
theorem B6642125 : Blo 1553474 6642125 := bstep (se 3 (by rfl) ⟨1245398, by rfl⟩ : syracuseStep 6642125 = 2490797) B2490797
theorem B1554899 : Blo 1553474 1554899 := bstep (se 1 (by rfl) ⟨1166174, by rfl⟩ : syracuseStep 1554899 = 2332349) B2332349
theorem B2333153 : Blo 1553474 2333153 := bstep (se 2 (by rfl) ⟨874932, by rfl⟩ : syracuseStep 2333153 = 1749865) B1749865
theorem B1554915 : Blo 1553474 1554915 := bstep (se 1 (by rfl) ⟨1166186, by rfl⟩ : syracuseStep 1554915 = 2332373) B2332373
theorem B1554931 : Blo 1553474 1554931 := bstep (se 1 (by rfl) ⟨1166198, by rfl⟩ : syracuseStep 1554931 = 2332397) B2332397
theorem B2333171 : Blo 1553474 2333171 := bstep (se 1 (by rfl) ⟨1749878, by rfl⟩ : syracuseStep 2333171 = 3499757) B3499757
theorem B1554947 : Blo 1553474 1554947 := bstep (se 1 (by rfl) ⟨1166210, by rfl⟩ : syracuseStep 1554947 = 2332421) B2332421
theorem B2333201 : Blo 1553474 2333201 := bstep (se 2 (by rfl) ⟨874950, by rfl⟩ : syracuseStep 2333201 = 1749901) B1749901
theorem B1554963 : Blo 1553474 1554963 := bstep (se 1 (by rfl) ⟨1166222, by rfl⟩ : syracuseStep 1554963 = 2332445) B2332445
theorem B1554979 : Blo 1553474 1554979 := bstep (se 1 (by rfl) ⟨1166234, by rfl⟩ : syracuseStep 1554979 = 2332469) B2332469
theorem B1554995 : Blo 1553474 1554995 := bstep (se 1 (by rfl) ⟨1166246, by rfl⟩ : syracuseStep 1554995 = 2332493) B2332493
theorem B1555011 : Blo 1553474 1555011 := bstep (se 1 (by rfl) ⟨1166258, by rfl⟩ : syracuseStep 1555011 = 2332517) B2332517
theorem B1555027 : Blo 1553474 1555027 := bstep (se 1 (by rfl) ⟨1166270, by rfl⟩ : syracuseStep 1555027 = 2332541) B2332541
theorem B1555043 : Blo 1553474 1555043 := bstep (se 1 (by rfl) ⟨1166282, by rfl⟩ : syracuseStep 1555043 = 2332565) B2332565
theorem B1555059 : Blo 1553474 1555059 := bstep (se 1 (by rfl) ⟨1166294, by rfl⟩ : syracuseStep 1555059 = 2332589) B2332589
theorem B3365507 : Blo 1553474 3365507 := bstep (se 1 (by rfl) ⟨2524130, by rfl⟩ : syracuseStep 3365507 = 5048261) B5048261
theorem B1555075 : Blo 1553474 1555075 := bstep (se 1 (by rfl) ⟨1166306, by rfl⟩ : syracuseStep 1555075 = 2332613) B2332613
theorem B2800273 : Blo 1553474 2800273 := bstep (se 2 (by rfl) ⟨1050102, by rfl⟩ : syracuseStep 2800273 = 2100205) B2100205
theorem B1555091 : Blo 1553474 1555091 := bstep (se 1 (by rfl) ⟨1166318, by rfl⟩ : syracuseStep 1555091 = 2332637) B2332637
theorem B1555107 : Blo 1553474 1555107 := bstep (se 1 (by rfl) ⟨1166330, by rfl⟩ : syracuseStep 1555107 = 2332661) B2332661
theorem B3496625 : Blo 1553474 3496625 := bstep (se 2 (by rfl) ⟨1311234, by rfl⟩ : syracuseStep 3496625 = 2622469) B2622469
theorem B1555123 : Blo 1553474 1555123 := bstep (se 1 (by rfl) ⟨1166342, by rfl⟩ : syracuseStep 1555123 = 2332685) B2332685
theorem B3496643 : Blo 1553474 3496643 := bstep (se 1 (by rfl) ⟨2622482, by rfl⟩ : syracuseStep 3496643 = 5244965) B5244965
theorem B1555139 : Blo 1553474 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B1555155 : Blo 1553474 1555155 := bstep (se 1 (by rfl) ⟨1166366, by rfl⟩ : syracuseStep 1555155 = 2332733) B2332733
theorem B1555171 : Blo 1553474 1555171 := bstep (se 1 (by rfl) ⟨1166378, by rfl⟩ : syracuseStep 1555171 = 2332757) B2332757
theorem B1555187 : Blo 1553474 1555187 := bstep (se 1 (by rfl) ⟨1166390, by rfl⟩ : syracuseStep 1555187 = 2332781) B2332781
theorem B1555203 : Blo 1553474 1555203 := bstep (se 1 (by rfl) ⟨1166402, by rfl⟩ : syracuseStep 1555203 = 2332805) B2332805
theorem B1555219 : Blo 1553474 1555219 := bstep (se 1 (by rfl) ⟨1166414, by rfl⟩ : syracuseStep 1555219 = 2332829) B2332829
theorem B1555235 : Blo 1553474 1555235 := bstep (se 1 (by rfl) ⟨1166426, by rfl⟩ : syracuseStep 1555235 = 2332853) B2332853
theorem B1555251 : Blo 1553474 1555251 := bstep (se 1 (by rfl) ⟨1166438, by rfl⟩ : syracuseStep 1555251 = 2332877) B2332877
theorem B1555267 : Blo 1553474 1555267 := bstep (se 1 (by rfl) ⟨1166450, by rfl⟩ : syracuseStep 1555267 = 2332901) B2332901
theorem B1555283 : Blo 1553474 1555283 := bstep (se 1 (by rfl) ⟨1166462, by rfl⟩ : syracuseStep 1555283 = 2332925) B2332925
theorem B1555299 : Blo 1553474 1555299 := bstep (se 1 (by rfl) ⟨1166474, by rfl⟩ : syracuseStep 1555299 = 2332949) B2332949
theorem B1555315 : Blo 1553474 1555315 := bstep (se 1 (by rfl) ⟨1166486, by rfl⟩ : syracuseStep 1555315 = 2332973) B2332973
theorem B1555331 : Blo 1553474 1555331 := bstep (se 1 (by rfl) ⟨1166498, by rfl⟩ : syracuseStep 1555331 = 2332997) B2332997
theorem B4201361 : Blo 1553474 4201361 := bstep (se 2 (by rfl) ⟨1575510, by rfl⟩ : syracuseStep 4201361 = 3151021) B3151021
theorem B1555347 : Blo 1553474 1555347 := bstep (se 1 (by rfl) ⟨1166510, by rfl⟩ : syracuseStep 1555347 = 2333021) B2333021
theorem B1555363 : Blo 1553474 1555363 := bstep (se 1 (by rfl) ⟨1166522, by rfl⟩ : syracuseStep 1555363 = 2333045) B2333045
theorem B2800561 : Blo 1553474 2800561 := bstep (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) B2100421
theorem B1555379 : Blo 1553474 1555379 := bstep (se 1 (by rfl) ⟨1166534, by rfl⟩ : syracuseStep 1555379 = 2333069) B2333069
theorem B1555395 : Blo 1553474 1555395 := bstep (se 1 (by rfl) ⟨1166546, by rfl⟩ : syracuseStep 1555395 = 2333093) B2333093
theorem B3496913 : Blo 1553474 3496913 := bstep (se 2 (by rfl) ⟨1311342, by rfl⟩ : syracuseStep 3496913 = 2622685) B2622685
theorem B1555411 : Blo 1553474 1555411 := bstep (se 1 (by rfl) ⟨1166558, by rfl⟩ : syracuseStep 1555411 = 2333117) B2333117
theorem B3496931 : Blo 1553474 3496931 := bstep (se 1 (by rfl) ⟨2622698, by rfl⟩ : syracuseStep 3496931 = 5245397) B5245397
theorem B1555427 : Blo 1553474 1555427 := bstep (se 1 (by rfl) ⟨1166570, by rfl⟩ : syracuseStep 1555427 = 2333141) B2333141
theorem B1555443 : Blo 1553474 1555443 := bstep (se 1 (by rfl) ⟨1166582, by rfl⟩ : syracuseStep 1555443 = 2333165) B2333165
theorem B1555459 : Blo 1553474 1555459 := bstep (se 1 (by rfl) ⟨1166594, by rfl⟩ : syracuseStep 1555459 = 2333189) B2333189
theorem B4979789 : Blo 1553474 4979789 := bstep (se 3 (by rfl) ⟨933710, by rfl⟩ : syracuseStep 4979789 = 1867421) B1867421
theorem B5905507 : Blo 1553474 5905507 := bstep (se 1 (by rfl) ⟨4429130, by rfl⟩ : syracuseStep 5905507 = 8858261) B8858261
theorem B10632397 : Blo 1553474 10632397 := bstep (se 3 (by rfl) ⟨1993574, by rfl⟩ : syracuseStep 10632397 = 3987149) B3987149
theorem B3497201 : Blo 1553474 3497201 := bstep (se 2 (by rfl) ⟨1311450, by rfl⟩ : syracuseStep 3497201 = 2622901) B2622901
theorem B19176689 : Blo 1553474 19176689 := bstep (se 2 (by rfl) ⟨7191258, by rfl⟩ : syracuseStep 19176689 = 14382517) B14382517
theorem B3497219 : Blo 1553474 3497219 := bstep (se 1 (by rfl) ⟨2622914, by rfl⟩ : syracuseStep 3497219 = 5245829) B5245829
theorem B7568653 : Blo 1553474 7568653 := bstep (se 3 (by rfl) ⟨1419122, by rfl⟩ : syracuseStep 7568653 = 2838245) B2838245
theorem B10640717 : Blo 1553474 10640717 := bstep (se 3 (by rfl) ⟨1995134, by rfl⟩ : syracuseStep 10640717 = 3990269) B3990269
theorem B5979491 : Blo 1553474 5979491 := bstep (se 1 (by rfl) ⟨4484618, by rfl⟩ : syracuseStep 5979491 = 8969237) B8969237
theorem B10640803 : Blo 1553474 10640803 := bstep (se 1 (by rfl) ⟨7980602, by rfl⟩ : syracuseStep 10640803 = 15961205) B15961205
theorem B4980209 : Blo 1553474 4980209 := bstep (se 2 (by rfl) ⟨1867578, by rfl⟩ : syracuseStep 4980209 = 3735157) B3735157
theorem B3497489 : Blo 1553474 3497489 := bstep (se 2 (by rfl) ⟨1311558, by rfl⟩ : syracuseStep 3497489 = 2623117) B2623117
theorem B3497507 : Blo 1553474 3497507 := bstep (se 1 (by rfl) ⟨2623130, by rfl⟩ : syracuseStep 3497507 = 5246261) B5246261
theorem B1867459 : Blo 1553474 1867459 := bstep (se 1 (by rfl) ⟨1400594, by rfl⟩ : syracuseStep 1867459 = 2801189) B2801189
theorem B13278917 : Blo 1553474 13278917 := bstep (se 4 (by rfl) ⟨1244898, by rfl⟩ : syracuseStep 13278917 = 2489797) B2489797
theorem B3546833 : Blo 1553474 3546833 := bstep (se 2 (by rfl) ⟨1330062, by rfl⟩ : syracuseStep 3546833 = 2660125) B2660125
theorem B4316899 : Blo 1553474 4316899 := bstep (se 1 (by rfl) ⟨3237674, by rfl⟩ : syracuseStep 4316899 = 6475349) B6475349
theorem B7872227 : Blo 1553474 7872227 := bstep (se 1 (by rfl) ⟨5904170, by rfl⟩ : syracuseStep 7872227 = 11808341) B11808341
theorem B3497777 : Blo 1553474 3497777 := bstep (se 2 (by rfl) ⟨1311666, by rfl⟩ : syracuseStep 3497777 = 2623333) B2623333
theorem B8855345 : Blo 1553474 8855345 := bstep (se 2 (by rfl) ⟨3320754, by rfl⟩ : syracuseStep 8855345 = 6641509) B6641509
theorem B3497795 : Blo 1553474 3497795 := bstep (se 1 (by rfl) ⟨2623346, by rfl⟩ : syracuseStep 3497795 = 5246693) B5246693
theorem B11198321 : Blo 1553474 11198321 := bstep (se 2 (by rfl) ⟨4199370, by rfl⟩ : syracuseStep 11198321 = 8398741) B8398741
theorem B5603185 : Blo 1553474 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B2490259 : Blo 1553474 2490259 := bstep (se 1 (by rfl) ⟨1867694, by rfl⟩ : syracuseStep 2490259 = 3735389) B3735389
theorem B2244515 : Blo 1553474 2244515 := bstep (se 1 (by rfl) ⟨1683386, by rfl⟩ : syracuseStep 2244515 = 3366773) B3366773
theorem B2490355 : Blo 1553474 2490355 := bstep (se 1 (by rfl) ⟨1867766, by rfl⟩ : syracuseStep 2490355 = 3735533) B3735533
theorem B7086131 : Blo 1553474 7086131 := bstep (se 1 (by rfl) ⟨5314598, by rfl⟩ : syracuseStep 7086131 = 10629197) B10629197
theorem B2949185 : Blo 1553474 2949185 := bstep (se 2 (by rfl) ⟨1105944, by rfl⟩ : syracuseStep 2949185 = 2211889) B2211889
theorem B2990209 : Blo 1553474 2990209 := bstep (se 2 (by rfl) ⟨1121328, by rfl⟩ : syracuseStep 2990209 = 2242657) B2242657
theorem B3498137 : Blo 1553474 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B1966295 : Blo 1553474 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B4980953 : Blo 1553474 4980953 := bstep (se 2 (by rfl) ⟨1867857, by rfl⟩ : syracuseStep 4980953 = 3735715) B3735715
theorem B2801881 : Blo 1553474 2801881 := bstep (se 2 (by rfl) ⟨1050705, by rfl⟩ : syracuseStep 2801881 = 2101411) B2101411
theorem B3498227 : Blo 1553474 3498227 := bstep (se 1 (by rfl) ⟨2623670, by rfl⟩ : syracuseStep 3498227 = 5247341) B5247341
theorem B3498263 : Blo 1553474 3498263 := bstep (se 1 (by rfl) ⟨2623697, by rfl⟩ : syracuseStep 3498263 = 5247395) B5247395
theorem B2949527 : Blo 1553474 2949527 := bstep (se 1 (by rfl) ⟨2212145, by rfl⟩ : syracuseStep 2949527 = 4424291) B4424291
theorem B5898689 : Blo 1553474 5898689 := bstep (se 2 (by rfl) ⟨2212008, by rfl⟩ : syracuseStep 5898689 = 4424017) B4424017
theorem B3498443 : Blo 1553474 3498443 := bstep (se 1 (by rfl) ⟨2623832, by rfl⟩ : syracuseStep 3498443 = 5247665) B5247665
theorem B4727261 : Blo 1553474 4727261 := bstep (se 3 (by rfl) ⟨886361, by rfl⟩ : syracuseStep 4727261 = 1772723) B1772723
theorem B3498497 : Blo 1553474 3498497 := bstep (se 2 (by rfl) ⟨1311936, by rfl⟩ : syracuseStep 3498497 = 2623873) B2623873
theorem B2621963 : Blo 1553474 2621963 := bstep (se 1 (by rfl) ⟨1966472, by rfl⟩ : syracuseStep 2621963 = 3932945) B3932945
theorem B6636077 : Blo 1553474 6636077 := bstep (se 3 (by rfl) ⟨1244264, by rfl⟩ : syracuseStep 6636077 = 2488529) B2488529
theorem B9953857 : Blo 1553474 9953857 := bstep (se 2 (by rfl) ⟨3732696, by rfl⟩ : syracuseStep 9953857 = 7465393) B7465393
theorem B25215563 : Blo 1553474 25215563 := bstep (se 1 (by rfl) ⟨18911672, by rfl⟩ : syracuseStep 25215563 = 37823345) B37823345
theorem B2622091 : Blo 1553474 2622091 := bstep (se 1 (by rfl) ⟨1966568, by rfl⟩ : syracuseStep 2622091 = 3933137) B3933137
theorem B3498713 : Blo 1553474 3498713 := bstep (se 2 (by rfl) ⟨1312017, by rfl⟩ : syracuseStep 3498713 = 2624035) B2624035
theorem B2622233 : Blo 1553474 2622233 := bstep (se 2 (by rfl) ⟨983337, by rfl⟩ : syracuseStep 2622233 = 1966675) B1966675
theorem B3498803 : Blo 1553474 3498803 := bstep (se 1 (by rfl) ⟨2624102, by rfl⟩ : syracuseStep 3498803 = 5248205) B5248205
theorem B5243723 : Blo 1553474 5243723 := bstep (se 1 (by rfl) ⟨3932792, by rfl⟩ : syracuseStep 5243723 = 7865585) B7865585
theorem B3498839 : Blo 1553474 3498839 := bstep (se 1 (by rfl) ⟨2624129, by rfl⟩ : syracuseStep 3498839 = 5248259) B5248259
theorem B2802521 : Blo 1553474 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B1966999 : Blo 1553474 1966999 := bstep (se 1 (by rfl) ⟨1475249, by rfl⟩ : syracuseStep 1966999 = 2950499) B2950499
theorem B2622361 : Blo 1553474 2622361 := bstep (se 2 (by rfl) ⟨983385, by rfl⟩ : syracuseStep 2622361 = 1966771) B1966771
theorem B3933107 : Blo 1553474 3933107 := bstep (se 1 (by rfl) ⟨2949830, by rfl⟩ : syracuseStep 3933107 = 5899661) B5899661
theorem B3499019 : Blo 1553474 3499019 := bstep (se 1 (by rfl) ⟨2624264, by rfl⟩ : syracuseStep 3499019 = 5248529) B5248529
theorem B47842325 : Blo 1553474 47842325 := bstep (se 6 (by rfl) ⟨1121304, by rfl⟩ : syracuseStep 47842325 = 2242609) B2242609
theorem B2950195 : Blo 1553474 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B3499073 : Blo 1553474 3499073 := bstep (se 2 (by rfl) ⟨1312152, by rfl⟩ : syracuseStep 3499073 = 2624305) B2624305
theorem B5243993 : Blo 1553474 5243993 := bstep (se 2 (by rfl) ⟨1966497, by rfl⟩ : syracuseStep 5243993 = 3932995) B3932995
theorem B17974403 : Blo 1553474 17974403 := bstep (se 1 (by rfl) ⟨13480802, by rfl⟩ : syracuseStep 17974403 = 26961605) B26961605
theorem B5604497 : Blo 1553474 5604497 := bstep (se 2 (by rfl) ⟨2101686, by rfl⟩ : syracuseStep 5604497 = 4203373) B4203373
theorem B9962675 : Blo 1553474 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B6636761 : Blo 1553474 6636761 := bstep (se 2 (by rfl) ⟨2488785, by rfl⟩ : syracuseStep 6636761 = 4977571) B4977571
theorem B3499289 : Blo 1553474 3499289 := bstep (se 2 (by rfl) ⟨1312233, by rfl⟩ : syracuseStep 3499289 = 2624467) B2624467
theorem B13280557 : Blo 1553474 13280557 := bstep (se 3 (by rfl) ⟨2490104, by rfl⟩ : syracuseStep 13280557 = 4980209) B4980209
theorem B3499379 : Blo 1553474 3499379 := bstep (se 1 (by rfl) ⟨2624534, by rfl⟩ : syracuseStep 3499379 = 5249069) B5249069
theorem B3499415 : Blo 1553474 3499415 := bstep (se 1 (by rfl) ⟨2624561, by rfl⟩ : syracuseStep 3499415 = 5249123) B5249123
theorem B3933643 : Blo 1553474 3933643 := bstep (se 1 (by rfl) ⟨2950232, by rfl⟩ : syracuseStep 3933643 = 5900465) B5900465
theorem B2622935 : Blo 1553474 2622935 := bstep (se 1 (by rfl) ⟨1967201, by rfl⟩ : syracuseStep 2622935 = 3934403) B3934403
theorem B2213335 : Blo 1553474 2213335 := bstep (se 1 (by rfl) ⟨1660001, by rfl⟩ : syracuseStep 2213335 = 3320003) B3320003
theorem B7874009 : Blo 1553474 7874009 := bstep (se 2 (by rfl) ⟨2952753, by rfl⟩ : syracuseStep 7874009 = 5905507) B5905507
theorem B2950643 : Blo 1553474 2950643 := bstep (se 1 (by rfl) ⟨2212982, by rfl⟩ : syracuseStep 2950643 = 4425965) B4425965
theorem B2950681 : Blo 1553474 2950681 := bstep (se 2 (by rfl) ⟨1106505, by rfl⟩ : syracuseStep 2950681 = 2213011) B2213011
theorem B3499595 : Blo 1553474 3499595 := bstep (se 1 (by rfl) ⟨2624696, by rfl⟩ : syracuseStep 3499595 = 5249393) B5249393
theorem B2623063 : Blo 1553474 2623063 := bstep (se 1 (by rfl) ⟨1967297, by rfl⟩ : syracuseStep 2623063 = 3934595) B3934595
theorem B3933785 : Blo 1553474 3933785 := bstep (se 2 (by rfl) ⟨1475169, by rfl⟩ : syracuseStep 3933785 = 2950339) B2950339
theorem B3499649 : Blo 1553474 3499649 := bstep (se 2 (by rfl) ⟨1312368, by rfl⟩ : syracuseStep 3499649 = 2624737) B2624737
theorem B5899949 : Blo 1553474 5899949 := bstep (se 3 (by rfl) ⟨1106240, by rfl⟩ : syracuseStep 5899949 = 2212481) B2212481
theorem B4982465 : Blo 1553474 4982465 := bstep (se 2 (by rfl) ⟨1868424, by rfl⟩ : syracuseStep 4982465 = 3736849) B3736849
theorem B5899979 : Blo 1553474 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B5244695 : Blo 1553474 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B4425623 : Blo 1553474 4425623 := bstep (se 1 (by rfl) ⟨3319217, by rfl⟩ : syracuseStep 4425623 = 6638435) B6638435
theorem B2951129 : Blo 1553474 2951129 := bstep (se 2 (by rfl) ⟨1106673, by rfl⟩ : syracuseStep 2951129 = 2213347) B2213347
theorem B11200517 : Blo 1553474 11200517 := bstep (se 4 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 11200517 = 2100097) B2100097
theorem B9955345 : Blo 1553474 9955345 := bstep (se 2 (by rfl) ⟨3733254, by rfl⟩ : syracuseStep 9955345 = 7466509) B7466509
theorem B3319859 : Blo 1553474 3319859 := bstep (se 1 (by rfl) ⟨2489894, by rfl⟩ : syracuseStep 3319859 = 4979789) B4979789
theorem B11798621 : Blo 1553474 11798621 := bstep (se 3 (by rfl) ⟨2212241, by rfl⟩ : syracuseStep 11798621 = 4424483) B4424483
theorem B2623691 : Blo 1553474 2623691 := bstep (se 1 (by rfl) ⟨1967768, by rfl⟩ : syracuseStep 2623691 = 3935537) B3935537
theorem B5245235 : Blo 1553474 5245235 := bstep (se 1 (by rfl) ⟨3933926, by rfl⟩ : syracuseStep 5245235 = 7867853) B7867853
theorem B2623819 : Blo 1553474 2623819 := bstep (se 1 (by rfl) ⟨1967864, by rfl⟩ : syracuseStep 2623819 = 3935729) B3935729
theorem B5900633 : Blo 1553474 5900633 := bstep (se 2 (by rfl) ⟨2212737, by rfl⟩ : syracuseStep 5900633 = 4425475) B4425475
theorem B1640855 : Blo 1553474 1640855 := bstep (se 1 (by rfl) ⟨1230641, by rfl⟩ : syracuseStep 1640855 = 2461283) B2461283
theorem B3934615 : Blo 1553474 3934615 := bstep (se 1 (by rfl) ⟨2950961, by rfl⟩ : syracuseStep 3934615 = 5901923) B5901923
theorem B17697203 : Blo 1553474 17697203 := bstep (se 1 (by rfl) ⟨13272902, by rfl⟩ : syracuseStep 17697203 = 26545805) B26545805
theorem B2623961 : Blo 1553474 2623961 := bstep (se 2 (by rfl) ⟨983985, by rfl⟩ : syracuseStep 2623961 = 1967971) B1967971
theorem B3320345 : Blo 1553474 3320345 := bstep (se 2 (by rfl) ⟨1245129, by rfl⟩ : syracuseStep 3320345 = 2490259) B2490259
theorem B5245505 : Blo 1553474 5245505 := bstep (se 2 (by rfl) ⟨1967064, by rfl⟩ : syracuseStep 5245505 = 3934129) B3934129
theorem B7465547 : Blo 1553474 7465547 := bstep (se 1 (by rfl) ⟨5599160, by rfl⟩ : syracuseStep 7465547 = 11198321) B11198321
theorem B2624089 : Blo 1553474 2624089 := bstep (se 2 (by rfl) ⟨984033, by rfl⟩ : syracuseStep 2624089 = 1968067) B1968067
theorem B13281893 : Blo 1553474 13281893 := bstep (se 4 (by rfl) ⟨1245177, by rfl⟩ : syracuseStep 13281893 = 2490355) B2490355
theorem B5900951 : Blo 1553474 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B11209367 : Blo 1553474 11209367 := bstep (se 1 (by rfl) ⟨8407025, by rfl⟩ : syracuseStep 11209367 = 16814051) B16814051
theorem B2951873 : Blo 1553474 2951873 := bstep (se 2 (by rfl) ⟨1106952, by rfl⟩ : syracuseStep 2951873 = 2213905) B2213905
theorem B1747723 : Blo 1553474 1747723 := bstep (se 1 (by rfl) ⟨1310792, by rfl⟩ : syracuseStep 1747723 = 2621585) B2621585
theorem B8850221 : Blo 1553474 8850221 := bstep (se 3 (by rfl) ⟨1659416, by rfl⟩ : syracuseStep 8850221 = 3318833) B3318833
theorem B3935051 : Blo 1553474 3935051 := bstep (se 1 (by rfl) ⟨2951288, by rfl⟩ : syracuseStep 3935051 = 5902577) B5902577
theorem B8858443 : Blo 1553474 8858443 := bstep (se 1 (by rfl) ⟨6643832, by rfl⟩ : syracuseStep 8858443 = 13287665) B13287665
theorem B1747831 : Blo 1553474 1747831 := bstep (se 1 (by rfl) ⟨1310873, by rfl⟩ : syracuseStep 1747831 = 2621747) B2621747
theorem B9456563 : Blo 1553474 9456563 := bstep (se 1 (by rfl) ⟨7092422, by rfl⟩ : syracuseStep 9456563 = 14184845) B14184845
theorem B2952139 : Blo 1553474 2952139 := bstep (se 1 (by rfl) ⟨2214104, by rfl⟩ : syracuseStep 2952139 = 4428209) B4428209
theorem B1748011 : Blo 1553474 1748011 := bstep (se 1 (by rfl) ⟨1311008, by rfl⟩ : syracuseStep 1748011 = 2622017) B2622017
theorem B5246045 : Blo 1553474 5246045 := bstep (se 3 (by rfl) ⟨983633, by rfl⟩ : syracuseStep 5246045 = 1967267) B1967267
theorem B8858717 : Blo 1553474 8858717 := bstep (se 3 (by rfl) ⟨1661009, by rfl⟩ : syracuseStep 8858717 = 3322019) B3322019
theorem B1772651 : Blo 1553474 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B1748119 : Blo 1553474 1748119 := bstep (se 1 (by rfl) ⟨1311089, by rfl⟩ : syracuseStep 1748119 = 2622179) B2622179
theorem B2624663 : Blo 1553474 2624663 := bstep (se 1 (by rfl) ⟨1968497, by rfl⟩ : syracuseStep 2624663 = 3936995) B3936995
theorem B3935425 : Blo 1553474 3935425 := bstep (se 2 (by rfl) ⟨1475784, by rfl⟩ : syracuseStep 3935425 = 2951569) B2951569
theorem B4099265 : Blo 1553474 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B9456857 : Blo 1553474 9456857 := bstep (se 2 (by rfl) ⟨3546321, by rfl⟩ : syracuseStep 9456857 = 7092643) B7092643
theorem B2592011 : Blo 1553474 2592011 := bstep (se 1 (by rfl) ⟨1944008, by rfl⟩ : syracuseStep 2592011 = 3888017) B3888017
theorem B2624791 : Blo 1553474 2624791 := bstep (se 1 (by rfl) ⟨1968593, by rfl⟩ : syracuseStep 2624791 = 3937187) B3937187
theorem B51137837 : Blo 1553474 51137837 := bstep (se 3 (by rfl) ⟨9588344, by rfl⟩ : syracuseStep 51137837 = 19176689) B19176689
theorem B5901619 : Blo 1553474 5901619 := bstep (se 1 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 5901619 = 8852429) B8852429
theorem B1748299 : Blo 1553474 1748299 := bstep (se 1 (by rfl) ⟨1311224, by rfl⟩ : syracuseStep 1748299 = 2622449) B2622449
theorem B2952587 : Blo 1553474 2952587 := bstep (se 1 (by rfl) ⟨2214440, by rfl⟩ : syracuseStep 2952587 = 4428881) B4428881
theorem B1748407 : Blo 1553474 1748407 := bstep (se 1 (by rfl) ⟨1311305, by rfl⟩ : syracuseStep 1748407 = 2622611) B2622611
theorem B2362841 : Blo 1553474 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B2952769 : Blo 1553474 2952769 := bstep (se 2 (by rfl) ⟨1107288, by rfl⟩ : syracuseStep 2952769 = 2214577) B2214577
theorem B2100811 : Blo 1553474 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B50409053 : Blo 1553474 50409053 := bstep (se 3 (by rfl) ⟨9451697, by rfl⟩ : syracuseStep 50409053 = 18903395) B18903395
theorem B1748587 : Blo 1553474 1748587 := bstep (se 1 (by rfl) ⟨1311440, by rfl⟩ : syracuseStep 1748587 = 2622881) B2622881
theorem B2330315 : Blo 1553474 2330315 := bstep (se 1 (by rfl) ⟨1747736, by rfl⟩ : syracuseStep 2330315 = 3495473) B3495473
theorem B2330327 : Blo 1553474 2330327 := bstep (se 1 (by rfl) ⟨1747745, by rfl⟩ : syracuseStep 2330327 = 3495491) B3495491
theorem B1748695 : Blo 1553474 1748695 := bstep (se 1 (by rfl) ⟨1311521, by rfl⟩ : syracuseStep 1748695 = 2623043) B2623043
theorem B7868177 : Blo 1553474 7868177 := bstep (se 2 (by rfl) ⟨2950566, by rfl⟩ : syracuseStep 7868177 = 5901133) B5901133
theorem B3936023 : Blo 1553474 3936023 := bstep (se 1 (by rfl) ⟨2952017, by rfl⟩ : syracuseStep 3936023 = 5904035) B5904035
theorem B2330393 : Blo 1553474 2330393 := bstep (se 2 (by rfl) ⟨873897, by rfl⟩ : syracuseStep 2330393 = 1747795) B1747795
theorem B5320523 : Blo 1553474 5320523 := bstep (se 1 (by rfl) ⟨3990392, by rfl⟩ : syracuseStep 5320523 = 7980785) B7980785
theorem B2101081 : Blo 1553474 2101081 := bstep (se 2 (by rfl) ⟨787905, by rfl⟩ : syracuseStep 2101081 = 1575811) B1575811
theorem B17698661 : Blo 1553474 17698661 := bstep (se 4 (by rfl) ⟨1659249, by rfl⟩ : syracuseStep 17698661 = 3318499) B3318499
theorem B8408933 : Blo 1553474 8408933 := bstep (se 4 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 8408933 = 1576675) B1576675
theorem B2330507 : Blo 1553474 2330507 := bstep (se 1 (by rfl) ⟨1747880, by rfl⟩ : syracuseStep 2330507 = 3495761) B3495761
theorem B1748875 : Blo 1553474 1748875 := bstep (se 1 (by rfl) ⟨1311656, by rfl⟩ : syracuseStep 1748875 = 2623313) B2623313
theorem B2330519 : Blo 1553474 2330519 := bstep (se 1 (by rfl) ⟨1747889, by rfl⟩ : syracuseStep 2330519 = 3495779) B3495779
theorem B7868339 : Blo 1553474 7868339 := bstep (se 1 (by rfl) ⟨5901254, by rfl⟩ : syracuseStep 7868339 = 11802509) B11802509
theorem B2330585 : Blo 1553474 2330585 := bstep (se 2 (by rfl) ⟨873969, by rfl⟩ : syracuseStep 2330585 = 1747939) B1747939
theorem B1748983 : Blo 1553474 1748983 := bstep (se 1 (by rfl) ⟨1311737, by rfl⟩ : syracuseStep 1748983 = 2623475) B2623475
theorem B5599277 : Blo 1553474 5599277 := bstep (se 3 (by rfl) ⟨1049864, by rfl⟩ : syracuseStep 5599277 = 2099729) B2099729
theorem B2330699 : Blo 1553474 2330699 := bstep (se 1 (by rfl) ⟨1748024, by rfl⟩ : syracuseStep 2330699 = 3496049) B3496049
theorem B2330711 : Blo 1553474 2330711 := bstep (se 1 (by rfl) ⟨1748033, by rfl⟩ : syracuseStep 2330711 = 3496067) B3496067
theorem B3321985 : Blo 1553474 3321985 := bstep (se 2 (by rfl) ⟨1245744, by rfl⟩ : syracuseStep 3321985 = 2491489) B2491489
theorem B2330777 : Blo 1553474 2330777 := bstep (se 2 (by rfl) ⟨874041, by rfl⟩ : syracuseStep 2330777 = 1748083) B1748083
theorem B1749163 : Blo 1553474 1749163 := bstep (se 1 (by rfl) ⟨1311872, by rfl⟩ : syracuseStep 1749163 = 2623745) B2623745
theorem B5247179 : Blo 1553474 5247179 := bstep (se 1 (by rfl) ⟨3935384, by rfl⟩ : syracuseStep 5247179 = 7870769) B7870769
theorem B2330891 : Blo 1553474 2330891 := bstep (se 1 (by rfl) ⟨1748168, by rfl⟩ : syracuseStep 2330891 = 3496337) B3496337
theorem B14176529 : Blo 1553474 14176529 := bstep (se 2 (by rfl) ⟨5316198, by rfl⟩ : syracuseStep 14176529 = 10632397) B10632397
theorem B2330903 : Blo 1553474 2330903 := bstep (se 1 (by rfl) ⟨1748177, by rfl⟩ : syracuseStep 2330903 = 3496355) B3496355
theorem B1749271 : Blo 1553474 1749271 := bstep (se 1 (by rfl) ⟨1311953, by rfl⟩ : syracuseStep 1749271 = 2623907) B2623907
theorem B4428083 : Blo 1553474 4428083 := bstep (se 1 (by rfl) ⟨3321062, by rfl⟩ : syracuseStep 4428083 = 6642125) B6642125
theorem B2330969 : Blo 1553474 2330969 := bstep (se 2 (by rfl) ⟨874113, by rfl⟩ : syracuseStep 2330969 = 1748227) B1748227
theorem B8974685 : Blo 1553474 8974685 := bstep (se 3 (by rfl) ⟨1682753, by rfl⟩ : syracuseStep 8974685 = 3365507) B3365507
theorem B19927397 : Blo 1553474 19927397 := bstep (se 4 (by rfl) ⟨1868193, by rfl⟩ : syracuseStep 19927397 = 3736387) B3736387
theorem B2331083 : Blo 1553474 2331083 := bstep (se 1 (by rfl) ⟨1748312, by rfl⟩ : syracuseStep 2331083 = 3496625) B3496625
theorem B1749451 : Blo 1553474 1749451 := bstep (se 1 (by rfl) ⟨1312088, by rfl⟩ : syracuseStep 1749451 = 2624177) B2624177
theorem B2331095 : Blo 1553474 2331095 := bstep (se 1 (by rfl) ⟨1748321, by rfl⟩ : syracuseStep 2331095 = 3496643) B3496643
theorem B5247449 : Blo 1553474 5247449 := bstep (se 2 (by rfl) ⟨1967793, by rfl⟩ : syracuseStep 5247449 = 3935587) B3935587
theorem B5902865 : Blo 1553474 5902865 := bstep (se 2 (by rfl) ⟨2213574, by rfl⟩ : syracuseStep 5902865 = 4427149) B4427149
theorem B2331161 : Blo 1553474 2331161 := bstep (se 2 (by rfl) ⟨874185, by rfl⟩ : syracuseStep 2331161 = 1748371) B1748371
theorem B9458221 : Blo 1553474 9458221 := bstep (se 3 (by rfl) ⟨1773416, by rfl⟩ : syracuseStep 9458221 = 3546833) B3546833
theorem B1749559 : Blo 1553474 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B3936833 : Blo 1553474 3936833 := bstep (se 2 (by rfl) ⟨1476312, by rfl⟩ : syracuseStep 3936833 = 2952625) B2952625
theorem B2331275 : Blo 1553474 2331275 := bstep (se 1 (by rfl) ⟨1748456, by rfl⟩ : syracuseStep 2331275 = 3496913) B3496913
theorem B2331287 : Blo 1553474 2331287 := bstep (se 1 (by rfl) ⟨1748465, by rfl⟩ : syracuseStep 2331287 = 3496931) B3496931
theorem B2331353 : Blo 1553474 2331353 := bstep (se 2 (by rfl) ⟨874257, by rfl⟩ : syracuseStep 2331353 = 1748515) B1748515
theorem B1749739 : Blo 1553474 1749739 := bstep (se 1 (by rfl) ⟨1312304, by rfl⟩ : syracuseStep 1749739 = 2624609) B2624609
theorem B28357361 : Blo 1553474 28357361 := bstep (se 2 (by rfl) ⟨10634010, by rfl⟩ : syracuseStep 28357361 = 21268021) B21268021
theorem B2331467 : Blo 1553474 2331467 := bstep (se 1 (by rfl) ⟨1748600, by rfl⟩ : syracuseStep 2331467 = 3497201) B3497201
theorem B2331479 : Blo 1553474 2331479 := bstep (se 1 (by rfl) ⟨1748609, by rfl⟩ : syracuseStep 2331479 = 3497219) B3497219
theorem B1749847 : Blo 1553474 1749847 := bstep (se 1 (by rfl) ⟨1312385, by rfl⟩ : syracuseStep 1749847 = 2624771) B2624771
theorem B3986327 : Blo 1553474 3986327 := bstep (se 1 (by rfl) ⟨2989745, by rfl⟩ : syracuseStep 3986327 = 5979491) B5979491
theorem B2331545 : Blo 1553474 2331545 := bstep (se 2 (by rfl) ⟨874329, by rfl⟩ : syracuseStep 2331545 = 1748659) B1748659
theorem B5755865 : Blo 1553474 5755865 := bstep (se 2 (by rfl) ⟨2158449, by rfl⟩ : syracuseStep 5755865 = 4316899) B4316899
theorem B2331659 : Blo 1553474 2331659 := bstep (se 1 (by rfl) ⟨1748744, by rfl⟩ : syracuseStep 2331659 = 3497489) B3497489
theorem B2331671 : Blo 1553474 2331671 := bstep (se 1 (by rfl) ⟨1748753, by rfl⟩ : syracuseStep 2331671 = 3497507) B3497507
theorem B1553483 : Blo 1553474 1553483 := bstep (se 1 (by rfl) ⟨1165112, by rfl⟩ : syracuseStep 1553483 = 2330225) B2330225
theorem B1553495 : Blo 1553474 1553495 := bstep (se 1 (by rfl) ⟨1165121, by rfl⟩ : syracuseStep 1553495 = 2330243) B2330243
theorem B2331737 : Blo 1553474 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B5985373 : Blo 1553474 5985373 := bstep (se 3 (by rfl) ⟨1122257, by rfl⟩ : syracuseStep 5985373 = 2244515) B2244515
theorem B1553515 : Blo 1553474 1553515 := bstep (se 1 (by rfl) ⟨1165136, by rfl⟩ : syracuseStep 1553515 = 2330273) B2330273
theorem B1553527 : Blo 1553474 1553527 := bstep (se 1 (by rfl) ⟨1165145, by rfl⟩ : syracuseStep 1553527 = 2330291) B2330291
theorem B8852611 : Blo 1553474 8852611 := bstep (se 1 (by rfl) ⟨6639458, by rfl⟩ : syracuseStep 8852611 = 13278917) B13278917
theorem B1553547 : Blo 1553474 1553547 := bstep (se 1 (by rfl) ⟨1165160, by rfl⟩ : syracuseStep 1553547 = 2330321) B2330321
theorem B1553559 : Blo 1553474 1553559 := bstep (se 1 (by rfl) ⟨1165169, by rfl⟩ : syracuseStep 1553559 = 2330339) B2330339
theorem B5248151 : Blo 1553474 5248151 := bstep (se 1 (by rfl) ⟨3936113, by rfl⟩ : syracuseStep 5248151 = 7872227) B7872227
theorem B1553579 : Blo 1553474 1553579 := bstep (se 1 (by rfl) ⟨1165184, by rfl⟩ : syracuseStep 1553579 = 2330369) B2330369
theorem B5600429 : Blo 1553474 5600429 := bstep (se 3 (by rfl) ⟨1050080, by rfl⟩ : syracuseStep 5600429 = 2100161) B2100161
theorem B3732659 : Blo 1553474 3732659 := bstep (se 1 (by rfl) ⟨2799494, by rfl⟩ : syracuseStep 3732659 = 5598989) B5598989
theorem B54580405 : Blo 1553474 54580405 := bstep (se 5 (by rfl) ⟨2558456, by rfl⟩ : syracuseStep 54580405 = 5116913) B5116913
theorem B1553591 : Blo 1553474 1553591 := bstep (se 1 (by rfl) ⟨1165193, by rfl⟩ : syracuseStep 1553591 = 2330387) B2330387
theorem B1553611 : Blo 1553474 1553611 := bstep (se 1 (by rfl) ⟨1165208, by rfl⟩ : syracuseStep 1553611 = 2330417) B2330417
theorem B2331851 : Blo 1553474 2331851 := bstep (se 1 (by rfl) ⟨1748888, by rfl⟩ : syracuseStep 2331851 = 3497777) B3497777
theorem B5903563 : Blo 1553474 5903563 := bstep (se 1 (by rfl) ⟨4427672, by rfl⟩ : syracuseStep 5903563 = 8855345) B8855345
theorem B1553623 : Blo 1553474 1553623 := bstep (se 1 (by rfl) ⟨1165217, by rfl⟩ : syracuseStep 1553623 = 2330435) B2330435
theorem B2331863 : Blo 1553474 2331863 := bstep (se 1 (by rfl) ⟨1748897, by rfl⟩ : syracuseStep 2331863 = 3497795) B3497795
theorem B1553643 : Blo 1553474 1553643 := bstep (se 1 (by rfl) ⟨1165232, by rfl⟩ : syracuseStep 1553643 = 2330465) B2330465
theorem B1553655 : Blo 1553474 1553655 := bstep (se 1 (by rfl) ⟨1165241, by rfl⟩ : syracuseStep 1553655 = 2330483) B2330483
theorem B1553675 : Blo 1553474 1553675 := bstep (se 1 (by rfl) ⟨1165256, by rfl⟩ : syracuseStep 1553675 = 2330513) B2330513
theorem B1553687 : Blo 1553474 1553687 := bstep (se 1 (by rfl) ⟨1165265, by rfl⟩ : syracuseStep 1553687 = 2330531) B2330531
theorem B2331929 : Blo 1553474 2331929 := bstep (se 2 (by rfl) ⟨874473, by rfl⟩ : syracuseStep 2331929 = 1748947) B1748947
theorem B1553707 : Blo 1553474 1553707 := bstep (se 1 (by rfl) ⟨1165280, by rfl⟩ : syracuseStep 1553707 = 2330561) B2330561
theorem B1553719 : Blo 1553474 1553719 := bstep (se 1 (by rfl) ⟨1165289, by rfl⟩ : syracuseStep 1553719 = 2330579) B2330579
theorem B1553739 : Blo 1553474 1553739 := bstep (se 1 (by rfl) ⟨1165304, by rfl⟩ : syracuseStep 1553739 = 2330609) B2330609
theorem B1553751 : Blo 1553474 1553751 := bstep (se 1 (by rfl) ⟨1165313, by rfl⟩ : syracuseStep 1553751 = 2330627) B2330627
theorem B7091549 : Blo 1553474 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B1553771 : Blo 1553474 1553771 := bstep (se 1 (by rfl) ⟨1165328, by rfl⟩ : syracuseStep 1553771 = 2330657) B2330657
theorem B1553783 : Blo 1553474 1553783 := bstep (se 1 (by rfl) ⟨1165337, by rfl⟩ : syracuseStep 1553783 = 2330675) B2330675
theorem B1553803 : Blo 1553474 1553803 := bstep (se 1 (by rfl) ⟨1165352, by rfl⟩ : syracuseStep 1553803 = 2330705) B2330705
theorem B2332043 : Blo 1553474 2332043 := bstep (se 1 (by rfl) ⟨1749032, by rfl⟩ : syracuseStep 2332043 = 3498065) B3498065
theorem B1553815 : Blo 1553474 1553815 := bstep (se 1 (by rfl) ⟨1165361, by rfl⟩ : syracuseStep 1553815 = 2330723) B2330723
theorem B2332055 : Blo 1553474 2332055 := bstep (se 1 (by rfl) ⟨1749041, by rfl⟩ : syracuseStep 2332055 = 3498083) B3498083
theorem B1553835 : Blo 1553474 1553835 := bstep (se 1 (by rfl) ⟨1165376, by rfl⟩ : syracuseStep 1553835 = 2330753) B2330753
theorem B3495347 : Blo 1553474 3495347 := bstep (se 1 (by rfl) ⟨2621510, by rfl⟩ : syracuseStep 3495347 = 5243021) B5243021
theorem B1553847 : Blo 1553474 1553847 := bstep (se 1 (by rfl) ⟨1165385, by rfl⟩ : syracuseStep 1553847 = 2330771) B2330771
theorem B1660343 : Blo 1553474 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B3732929 : Blo 1553474 3732929 := bstep (se 2 (by rfl) ⟨1399848, by rfl⟩ : syracuseStep 3732929 = 2799697) B2799697
theorem B1553867 : Blo 1553474 1553867 := bstep (se 1 (by rfl) ⟨1165400, by rfl⟩ : syracuseStep 1553867 = 2330801) B2330801
theorem B6641099 : Blo 1553474 6641099 := bstep (se 1 (by rfl) ⟨4980824, by rfl⟩ : syracuseStep 6641099 = 9961649) B9961649
theorem B3495383 : Blo 1553474 3495383 := bstep (se 1 (by rfl) ⟨2621537, by rfl⟩ : syracuseStep 3495383 = 5243075) B5243075
theorem B1553879 : Blo 1553474 1553879 := bstep (se 1 (by rfl) ⟨1165409, by rfl⟩ : syracuseStep 1553879 = 2330819) B2330819
theorem B2332121 : Blo 1553474 2332121 := bstep (se 2 (by rfl) ⟨874545, by rfl⟩ : syracuseStep 2332121 = 1749091) B1749091
theorem B5903837 : Blo 1553474 5903837 := bstep (se 3 (by rfl) ⟨1106969, by rfl⟩ : syracuseStep 5903837 = 2213939) B2213939
theorem B1553899 : Blo 1553474 1553899 := bstep (se 1 (by rfl) ⟨1165424, by rfl⟩ : syracuseStep 1553899 = 2330849) B2330849
theorem B1553911 : Blo 1553474 1553911 := bstep (se 1 (by rfl) ⟨1165433, by rfl⟩ : syracuseStep 1553911 = 2330867) B2330867
theorem B1553931 : Blo 1553474 1553931 := bstep (se 1 (by rfl) ⟨1165448, by rfl⟩ : syracuseStep 1553931 = 2330897) B2330897
theorem B1553943 : Blo 1553474 1553943 := bstep (se 1 (by rfl) ⟨1165457, by rfl⟩ : syracuseStep 1553943 = 2330915) B2330915
theorem B1553963 : Blo 1553474 1553963 := bstep (se 1 (by rfl) ⟨1165472, by rfl⟩ : syracuseStep 1553963 = 2330945) B2330945
theorem B1553975 : Blo 1553474 1553975 := bstep (se 1 (by rfl) ⟨1165481, by rfl⟩ : syracuseStep 1553975 = 2330963) B2330963
theorem B1553995 : Blo 1553474 1553995 := bstep (se 1 (by rfl) ⟨1165496, by rfl⟩ : syracuseStep 1553995 = 2330993) B2330993
theorem B2332235 : Blo 1553474 2332235 := bstep (se 1 (by rfl) ⟨1749176, by rfl⟩ : syracuseStep 2332235 = 3498353) B3498353
theorem B1554007 : Blo 1553474 1554007 := bstep (se 1 (by rfl) ⟨1165505, by rfl⟩ : syracuseStep 1554007 = 2331011) B2331011
theorem B2332247 : Blo 1553474 2332247 := bstep (se 1 (by rfl) ⟨1749185, by rfl⟩ : syracuseStep 2332247 = 3498371) B3498371
theorem B1554027 : Blo 1553474 1554027 := bstep (se 1 (by rfl) ⟨1165520, by rfl⟩ : syracuseStep 1554027 = 2331041) B2331041
theorem B1554039 : Blo 1553474 1554039 := bstep (se 1 (by rfl) ⟨1165529, by rfl⟩ : syracuseStep 1554039 = 2331059) B2331059
theorem B3495563 : Blo 1553474 3495563 := bstep (se 1 (by rfl) ⟨2621672, by rfl⟩ : syracuseStep 3495563 = 5243345) B5243345
theorem B1554059 : Blo 1553474 1554059 := bstep (se 1 (by rfl) ⟨1165544, by rfl⟩ : syracuseStep 1554059 = 2331089) B2331089
theorem B1554071 : Blo 1553474 1554071 := bstep (se 1 (by rfl) ⟨1165553, by rfl⟩ : syracuseStep 1554071 = 2331107) B2331107
theorem B2332313 : Blo 1553474 2332313 := bstep (se 2 (by rfl) ⟨874617, by rfl⟩ : syracuseStep 2332313 = 1749235) B1749235
theorem B1554091 : Blo 1553474 1554091 := bstep (se 1 (by rfl) ⟨1165568, by rfl⟩ : syracuseStep 1554091 = 2331137) B2331137
theorem B5248691 : Blo 1553474 5248691 := bstep (se 1 (by rfl) ⟨3936518, by rfl⟩ : syracuseStep 5248691 = 7873037) B7873037
theorem B1554103 : Blo 1553474 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B3495617 : Blo 1553474 3495617 := bstep (se 2 (by rfl) ⟨1310856, by rfl⟩ : syracuseStep 3495617 = 2621713) B2621713
theorem B1554123 : Blo 1553474 1554123 := bstep (se 1 (by rfl) ⟨1165592, by rfl⟩ : syracuseStep 1554123 = 2331185) B2331185
theorem B1554135 : Blo 1553474 1554135 := bstep (se 1 (by rfl) ⟨1165601, by rfl⟩ : syracuseStep 1554135 = 2331203) B2331203
theorem B2660057 : Blo 1553474 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B1554155 : Blo 1553474 1554155 := bstep (se 1 (by rfl) ⟨1165616, by rfl⟩ : syracuseStep 1554155 = 2331233) B2331233
theorem B1554167 : Blo 1553474 1554167 := bstep (se 1 (by rfl) ⟨1165625, by rfl⟩ : syracuseStep 1554167 = 2331251) B2331251
theorem B1554187 : Blo 1553474 1554187 := bstep (se 1 (by rfl) ⟨1165640, by rfl⟩ : syracuseStep 1554187 = 2331281) B2331281
theorem B2332427 : Blo 1553474 2332427 := bstep (se 1 (by rfl) ⟨1749320, by rfl⟩ : syracuseStep 2332427 = 3498641) B3498641
theorem B1554199 : Blo 1553474 1554199 := bstep (se 1 (by rfl) ⟨1165649, by rfl⟩ : syracuseStep 1554199 = 2331299) B2331299
theorem B2332439 : Blo 1553474 2332439 := bstep (se 1 (by rfl) ⟨1749329, by rfl⟩ : syracuseStep 2332439 = 3498659) B3498659
theorem B1554219 : Blo 1553474 1554219 := bstep (se 1 (by rfl) ⟨1165664, by rfl⟩ : syracuseStep 1554219 = 2331329) B2331329
theorem B1554231 : Blo 1553474 1554231 := bstep (se 1 (by rfl) ⟨1165673, by rfl⟩ : syracuseStep 1554231 = 2331347) B2331347
theorem B1554251 : Blo 1553474 1554251 := bstep (se 1 (by rfl) ⟨1165688, by rfl⟩ : syracuseStep 1554251 = 2331377) B2331377
theorem B7870283 : Blo 1553474 7870283 := bstep (se 1 (by rfl) ⟨5902712, by rfl⟩ : syracuseStep 7870283 = 11805425) B11805425
theorem B1554263 : Blo 1553474 1554263 := bstep (se 1 (by rfl) ⟨1165697, by rfl⟩ : syracuseStep 1554263 = 2331395) B2331395
theorem B3151703 : Blo 1553474 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B2332505 : Blo 1553474 2332505 := bstep (se 2 (by rfl) ⟨874689, by rfl⟩ : syracuseStep 2332505 = 1749379) B1749379
theorem B1554283 : Blo 1553474 1554283 := bstep (se 1 (by rfl) ⟨1165712, by rfl⟩ : syracuseStep 1554283 = 2331425) B2331425
theorem B1554295 : Blo 1553474 1554295 := bstep (se 1 (by rfl) ⟨1165721, by rfl⟩ : syracuseStep 1554295 = 2331443) B2331443
theorem B1554315 : Blo 1553474 1554315 := bstep (se 1 (by rfl) ⟨1165736, by rfl⟩ : syracuseStep 1554315 = 2331473) B2331473
theorem B1554327 : Blo 1553474 1554327 := bstep (se 1 (by rfl) ⟨1165745, by rfl⟩ : syracuseStep 1554327 = 2331491) B2331491
theorem B3495833 : Blo 1553474 3495833 := bstep (se 2 (by rfl) ⟨1310937, by rfl⟩ : syracuseStep 3495833 = 2621875) B2621875
theorem B1554347 : Blo 1553474 1554347 := bstep (se 1 (by rfl) ⟨1165760, by rfl⟩ : syracuseStep 1554347 = 2331521) B2331521
theorem B1554359 : Blo 1553474 1554359 := bstep (se 1 (by rfl) ⟨1165769, by rfl⟩ : syracuseStep 1554359 = 2331539) B2331539
theorem B5248961 : Blo 1553474 5248961 := bstep (se 2 (by rfl) ⟨1968360, by rfl⟩ : syracuseStep 5248961 = 3936721) B3936721
theorem B1554379 : Blo 1553474 1554379 := bstep (se 1 (by rfl) ⟨1165784, by rfl⟩ : syracuseStep 1554379 = 2331569) B2331569
theorem B2332619 : Blo 1553474 2332619 := bstep (se 1 (by rfl) ⟨1749464, by rfl⟩ : syracuseStep 2332619 = 3498929) B3498929
theorem B1554391 : Blo 1553474 1554391 := bstep (se 1 (by rfl) ⟨1165793, by rfl⟩ : syracuseStep 1554391 = 2331587) B2331587
theorem B2332631 : Blo 1553474 2332631 := bstep (se 1 (by rfl) ⟨1749473, by rfl⟩ : syracuseStep 2332631 = 3498947) B3498947
theorem B1554411 : Blo 1553474 1554411 := bstep (se 1 (by rfl) ⟨1165808, by rfl⟩ : syracuseStep 1554411 = 2331617) B2331617
theorem B3495923 : Blo 1553474 3495923 := bstep (se 1 (by rfl) ⟨2621942, by rfl⟩ : syracuseStep 3495923 = 5243885) B5243885
theorem B1554423 : Blo 1553474 1554423 := bstep (se 1 (by rfl) ⟨1165817, by rfl⟩ : syracuseStep 1554423 = 2331635) B2331635
theorem B1554443 : Blo 1553474 1554443 := bstep (se 1 (by rfl) ⟨1165832, by rfl⟩ : syracuseStep 1554443 = 2331665) B2331665
theorem B3495959 : Blo 1553474 3495959 := bstep (se 1 (by rfl) ⟨2621969, by rfl⟩ : syracuseStep 3495959 = 5243939) B5243939
theorem B1554455 : Blo 1553474 1554455 := bstep (se 1 (by rfl) ⟨1165841, by rfl⟩ : syracuseStep 1554455 = 2331683) B2331683
theorem B2332697 : Blo 1553474 2332697 := bstep (se 2 (by rfl) ⟨874761, by rfl⟩ : syracuseStep 2332697 = 1749523) B1749523
theorem B1554475 : Blo 1553474 1554475 := bstep (se 1 (by rfl) ⟨1165856, by rfl⟩ : syracuseStep 1554475 = 2331713) B2331713
theorem B1554487 : Blo 1553474 1554487 := bstep (se 1 (by rfl) ⟨1165865, by rfl⟩ : syracuseStep 1554487 = 2331731) B2331731
theorem B8853569 : Blo 1553474 8853569 := bstep (se 2 (by rfl) ⟨3320088, by rfl⟩ : syracuseStep 8853569 = 6640177) B6640177
theorem B1554507 : Blo 1553474 1554507 := bstep (se 1 (by rfl) ⟨1165880, by rfl⟩ : syracuseStep 1554507 = 2331761) B2331761
theorem B1554519 : Blo 1553474 1554519 := bstep (se 1 (by rfl) ⟨1165889, by rfl⟩ : syracuseStep 1554519 = 2331779) B2331779
theorem B1554539 : Blo 1553474 1554539 := bstep (se 1 (by rfl) ⟨1165904, by rfl⟩ : syracuseStep 1554539 = 2331809) B2331809
theorem B1554551 : Blo 1553474 1554551 := bstep (se 1 (by rfl) ⟨1165913, by rfl⟩ : syracuseStep 1554551 = 2331827) B2331827
theorem B1554571 : Blo 1553474 1554571 := bstep (se 1 (by rfl) ⟨1165928, by rfl⟩ : syracuseStep 1554571 = 2331857) B2331857
theorem B2332811 : Blo 1553474 2332811 := bstep (se 1 (by rfl) ⟨1749608, by rfl⟩ : syracuseStep 2332811 = 3499217) B3499217
theorem B1554583 : Blo 1553474 1554583 := bstep (se 1 (by rfl) ⟨1165937, by rfl⟩ : syracuseStep 1554583 = 2331875) B2331875
theorem B5904535 : Blo 1553474 5904535 := bstep (se 1 (by rfl) ⟨4428401, by rfl⟩ : syracuseStep 5904535 = 8856803) B8856803
theorem B2332823 : Blo 1553474 2332823 := bstep (se 1 (by rfl) ⟨1749617, by rfl⟩ : syracuseStep 2332823 = 3499235) B3499235
theorem B1554603 : Blo 1553474 1554603 := bstep (se 1 (by rfl) ⟨1165952, by rfl⟩ : syracuseStep 1554603 = 2331905) B2331905
theorem B1554615 : Blo 1553474 1554615 := bstep (se 1 (by rfl) ⟨1165961, by rfl⟩ : syracuseStep 1554615 = 2331923) B2331923
theorem B3733697 : Blo 1553474 3733697 := bstep (se 2 (by rfl) ⟨1400136, by rfl⟩ : syracuseStep 3733697 = 2800273) B2800273
theorem B3496139 : Blo 1553474 3496139 := bstep (se 1 (by rfl) ⟨2622104, by rfl⟩ : syracuseStep 3496139 = 5244209) B5244209
theorem B1554635 : Blo 1553474 1554635 := bstep (se 1 (by rfl) ⟨1165976, by rfl⟩ : syracuseStep 1554635 = 2331953) B2331953
theorem B1554647 : Blo 1553474 1554647 := bstep (se 1 (by rfl) ⟨1165985, by rfl⟩ : syracuseStep 1554647 = 2331971) B2331971
theorem B2332889 : Blo 1553474 2332889 := bstep (se 2 (by rfl) ⟨874833, by rfl⟩ : syracuseStep 2332889 = 1749667) B1749667
theorem B1554667 : Blo 1553474 1554667 := bstep (se 1 (by rfl) ⟨1166000, by rfl⟩ : syracuseStep 1554667 = 2332001) B2332001
theorem B1554679 : Blo 1553474 1554679 := bstep (se 1 (by rfl) ⟨1166009, by rfl⟩ : syracuseStep 1554679 = 2332019) B2332019
theorem B3496193 : Blo 1553474 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B1554699 : Blo 1553474 1554699 := bstep (se 1 (by rfl) ⟨1166024, by rfl⟩ : syracuseStep 1554699 = 2332049) B2332049
theorem B7190801 : Blo 1553474 7190801 := bstep (se 2 (by rfl) ⟨2696550, by rfl⟩ : syracuseStep 7190801 = 5393101) B5393101
theorem B1554711 : Blo 1553474 1554711 := bstep (se 1 (by rfl) ⟨1166033, by rfl⟩ : syracuseStep 1554711 = 2332067) B2332067
theorem B1554731 : Blo 1553474 1554731 := bstep (se 1 (by rfl) ⟨1166048, by rfl⟩ : syracuseStep 1554731 = 2332097) B2332097
theorem B1554743 : Blo 1553474 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B14932289 : Blo 1553474 14932289 := bstep (se 2 (by rfl) ⟨5599608, by rfl⟩ : syracuseStep 14932289 = 11199217) B11199217
theorem B1554763 : Blo 1553474 1554763 := bstep (se 1 (by rfl) ⟨1166072, by rfl⟩ : syracuseStep 1554763 = 2332145) B2332145
theorem B2333003 : Blo 1553474 2333003 := bstep (se 1 (by rfl) ⟨1749752, by rfl⟩ : syracuseStep 2333003 = 3499505) B3499505
theorem B1554775 : Blo 1553474 1554775 := bstep (se 1 (by rfl) ⟨1166081, by rfl⟩ : syracuseStep 1554775 = 2332163) B2332163
theorem B2333015 : Blo 1553474 2333015 := bstep (se 1 (by rfl) ⟨1749761, by rfl⟩ : syracuseStep 2333015 = 3499523) B3499523
theorem B1554795 : Blo 1553474 1554795 := bstep (se 1 (by rfl) ⟨1166096, by rfl⟩ : syracuseStep 1554795 = 2332193) B2332193
theorem B1554807 : Blo 1553474 1554807 := bstep (se 1 (by rfl) ⟨1166105, by rfl⟩ : syracuseStep 1554807 = 2332211) B2332211
theorem B1554827 : Blo 1553474 1554827 := bstep (se 1 (by rfl) ⟨1166120, by rfl⟩ : syracuseStep 1554827 = 2332241) B2332241
theorem B4487575 : Blo 1553474 4487575 := bstep (se 1 (by rfl) ⟨3365681, by rfl⟩ : syracuseStep 4487575 = 6731363) B6731363
theorem B1554839 : Blo 1553474 1554839 := bstep (se 1 (by rfl) ⟨1166129, by rfl⟩ : syracuseStep 1554839 = 2332259) B2332259
theorem B2333081 : Blo 1553474 2333081 := bstep (se 2 (by rfl) ⟨874905, by rfl⟩ : syracuseStep 2333081 = 1749811) B1749811
theorem B1554859 : Blo 1553474 1554859 := bstep (se 1 (by rfl) ⟨1166144, by rfl⟩ : syracuseStep 1554859 = 2332289) B2332289
theorem B1554871 : Blo 1553474 1554871 := bstep (se 1 (by rfl) ⟨1166153, by rfl⟩ : syracuseStep 1554871 = 2332307) B2332307
theorem B1554891 : Blo 1553474 1554891 := bstep (se 1 (by rfl) ⟨1166168, by rfl⟩ : syracuseStep 1554891 = 2332337) B2332337
theorem B1554903 : Blo 1553474 1554903 := bstep (se 1 (by rfl) ⟨1166177, by rfl⟩ : syracuseStep 1554903 = 2332355) B2332355
theorem B3496409 : Blo 1553474 3496409 := bstep (se 2 (by rfl) ⟨1311153, by rfl⟩ : syracuseStep 3496409 = 2622307) B2622307
theorem B5601757 : Blo 1553474 5601757 := bstep (se 3 (by rfl) ⟨1050329, by rfl⟩ : syracuseStep 5601757 = 2100659) B2100659
theorem B5249501 : Blo 1553474 5249501 := bstep (se 3 (by rfl) ⟨984281, by rfl⟩ : syracuseStep 5249501 = 1968563) B1968563
theorem B1554923 : Blo 1553474 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B1554935 : Blo 1553474 1554935 := bstep (se 1 (by rfl) ⟨1166201, by rfl⟩ : syracuseStep 1554935 = 2332403) B2332403
theorem B1554955 : Blo 1553474 1554955 := bstep (se 1 (by rfl) ⟨1166216, by rfl⟩ : syracuseStep 1554955 = 2332433) B2332433
theorem B2333195 : Blo 1553474 2333195 := bstep (se 1 (by rfl) ⟨1749896, by rfl⟩ : syracuseStep 2333195 = 3499793) B3499793
theorem B1554967 : Blo 1553474 1554967 := bstep (se 1 (by rfl) ⟨1166225, by rfl⟩ : syracuseStep 1554967 = 2332451) B2332451
theorem B2333207 : Blo 1553474 2333207 := bstep (se 1 (by rfl) ⟨1749905, by rfl⟩ : syracuseStep 2333207 = 3499811) B3499811
theorem B1554987 : Blo 1553474 1554987 := bstep (se 1 (by rfl) ⟨1166240, by rfl⟩ : syracuseStep 1554987 = 2332481) B2332481
theorem B3496499 : Blo 1553474 3496499 := bstep (se 1 (by rfl) ⟨2622374, by rfl⟩ : syracuseStep 3496499 = 5244749) B5244749
theorem B1554999 : Blo 1553474 1554999 := bstep (se 1 (by rfl) ⟨1166249, by rfl⟩ : syracuseStep 1554999 = 2332499) B2332499
theorem B3734081 : Blo 1553474 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B1555019 : Blo 1553474 1555019 := bstep (se 1 (by rfl) ⟨1166264, by rfl⟩ : syracuseStep 1555019 = 2332529) B2332529
theorem B3496535 : Blo 1553474 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B1555031 : Blo 1553474 1555031 := bstep (se 1 (by rfl) ⟨1166273, by rfl⟩ : syracuseStep 1555031 = 2332547) B2332547
theorem B1555051 : Blo 1553474 1555051 := bstep (se 1 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 1555051 = 2332577) B2332577
theorem B1555063 : Blo 1553474 1555063 := bstep (se 1 (by rfl) ⟨1166297, by rfl⟩ : syracuseStep 1555063 = 2332595) B2332595
theorem B8403587 : Blo 1553474 8403587 := bstep (se 1 (by rfl) ⟨6302690, by rfl⟩ : syracuseStep 8403587 = 12605381) B12605381
theorem B1555083 : Blo 1553474 1555083 := bstep (se 1 (by rfl) ⟨1166312, by rfl⟩ : syracuseStep 1555083 = 2332625) B2332625
theorem B1555095 : Blo 1553474 1555095 := bstep (se 1 (by rfl) ⟨1166321, by rfl⟩ : syracuseStep 1555095 = 2332643) B2332643
theorem B1555115 : Blo 1553474 1555115 := bstep (se 1 (by rfl) ⟨1166336, by rfl⟩ : syracuseStep 1555115 = 2332673) B2332673
theorem B1555127 : Blo 1553474 1555127 := bstep (se 1 (by rfl) ⟨1166345, by rfl⟩ : syracuseStep 1555127 = 2332691) B2332691
theorem B1555147 : Blo 1553474 1555147 := bstep (se 1 (by rfl) ⟨1166360, by rfl⟩ : syracuseStep 1555147 = 2332721) B2332721
theorem B1555159 : Blo 1553474 1555159 := bstep (se 1 (by rfl) ⟨1166369, by rfl⟩ : syracuseStep 1555159 = 2332739) B2332739
theorem B1555179 : Blo 1553474 1555179 := bstep (se 1 (by rfl) ⟨1166384, by rfl⟩ : syracuseStep 1555179 = 2332769) B2332769
theorem B50420465 : Blo 1553474 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B1555191 : Blo 1553474 1555191 := bstep (se 1 (by rfl) ⟨1166393, by rfl⟩ : syracuseStep 1555191 = 2332787) B2332787
theorem B3496715 : Blo 1553474 3496715 := bstep (se 1 (by rfl) ⟨2622536, by rfl⟩ : syracuseStep 3496715 = 5245073) B5245073
theorem B1555211 : Blo 1553474 1555211 := bstep (se 1 (by rfl) ⟨1166408, by rfl⟩ : syracuseStep 1555211 = 2332817) B2332817
theorem B1555223 : Blo 1553474 1555223 := bstep (se 1 (by rfl) ⟨1166417, by rfl⟩ : syracuseStep 1555223 = 2332835) B2332835
theorem B1555243 : Blo 1553474 1555243 := bstep (se 1 (by rfl) ⟨1166432, by rfl⟩ : syracuseStep 1555243 = 2332865) B2332865
theorem B25549613 : Blo 1553474 25549613 := bstep (se 3 (by rfl) ⟨4790552, by rfl⟩ : syracuseStep 25549613 = 9581105) B9581105
theorem B1555255 : Blo 1553474 1555255 := bstep (se 1 (by rfl) ⟨1166441, by rfl⟩ : syracuseStep 1555255 = 2332883) B2332883
theorem B3496769 : Blo 1553474 3496769 := bstep (se 2 (by rfl) ⟨1311288, by rfl⟩ : syracuseStep 3496769 = 2622577) B2622577
theorem B1555275 : Blo 1553474 1555275 := bstep (se 1 (by rfl) ⟨1166456, by rfl⟩ : syracuseStep 1555275 = 2332913) B2332913
theorem B1555287 : Blo 1553474 1555287 := bstep (se 1 (by rfl) ⟨1166465, by rfl⟩ : syracuseStep 1555287 = 2332931) B2332931
theorem B1555307 : Blo 1553474 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B1555319 : Blo 1553474 1555319 := bstep (se 1 (by rfl) ⟨1166489, by rfl⟩ : syracuseStep 1555319 = 2332979) B2332979
theorem B1555339 : Blo 1553474 1555339 := bstep (se 1 (by rfl) ⟨1166504, by rfl⟩ : syracuseStep 1555339 = 2333009) B2333009
theorem B1555351 : Blo 1553474 1555351 := bstep (se 1 (by rfl) ⟨1166513, by rfl⟩ : syracuseStep 1555351 = 2333027) B2333027
theorem B1555371 : Blo 1553474 1555371 := bstep (se 1 (by rfl) ⟨1166528, by rfl⟩ : syracuseStep 1555371 = 2333057) B2333057
theorem B5905325 : Blo 1553474 5905325 := bstep (se 3 (by rfl) ⟨1107248, by rfl⟩ : syracuseStep 5905325 = 2214497) B2214497
theorem B5045171 : Blo 1553474 5045171 := bstep (se 1 (by rfl) ⟨3783878, by rfl⟩ : syracuseStep 5045171 = 7567757) B7567757
theorem B1555383 : Blo 1553474 1555383 := bstep (se 1 (by rfl) ⟨1166537, by rfl⟩ : syracuseStep 1555383 = 2333075) B2333075
theorem B1555403 : Blo 1553474 1555403 := bstep (se 1 (by rfl) ⟨1166552, by rfl⟩ : syracuseStep 1555403 = 2333105) B2333105
theorem B1555415 : Blo 1553474 1555415 := bstep (se 1 (by rfl) ⟨1166561, by rfl⟩ : syracuseStep 1555415 = 2333123) B2333123
theorem B1555435 : Blo 1553474 1555435 := bstep (se 1 (by rfl) ⟨1166576, by rfl⟩ : syracuseStep 1555435 = 2333153) B2333153
theorem B1555447 : Blo 1553474 1555447 := bstep (se 1 (by rfl) ⟨1166585, by rfl⟩ : syracuseStep 1555447 = 2333171) B2333171
theorem B1555467 : Blo 1553474 1555467 := bstep (se 1 (by rfl) ⟨1166600, by rfl⟩ : syracuseStep 1555467 = 2333201) B2333201
theorem B10091537 : Blo 1553474 10091537 := bstep (se 2 (by rfl) ⟨3784326, by rfl⟩ : syracuseStep 10091537 = 7568653) B7568653
theorem B3496985 : Blo 1553474 3496985 := bstep (se 2 (by rfl) ⟨1311369, by rfl⟩ : syracuseStep 3496985 = 2622739) B2622739
theorem B6642739 : Blo 1553474 6642739 := bstep (se 1 (by rfl) ⟨4982054, by rfl⟩ : syracuseStep 6642739 = 9964109) B9964109
theorem B3497075 : Blo 1553474 3497075 := bstep (se 1 (by rfl) ⟨2622806, by rfl⟩ : syracuseStep 3497075 = 5245613) B5245613
theorem B3497111 : Blo 1553474 3497111 := bstep (se 1 (by rfl) ⟨2622833, by rfl⟩ : syracuseStep 3497111 = 5245667) B5245667
theorem B14187737 : Blo 1553474 14187737 := bstep (se 2 (by rfl) ⟨5320401, by rfl⟩ : syracuseStep 14187737 = 10640803) B10640803
theorem B19930373 : Blo 1553474 19930373 := bstep (se 4 (by rfl) ⟨1868472, by rfl⟩ : syracuseStep 19930373 = 3736945) B3736945
theorem B2800907 : Blo 1553474 2800907 := bstep (se 1 (by rfl) ⟨2100680, by rfl⟩ : syracuseStep 2800907 = 4201361) B4201361
theorem B3497291 : Blo 1553474 3497291 := bstep (se 1 (by rfl) ⟨2622968, by rfl⟩ : syracuseStep 3497291 = 5245937) B5245937
theorem B3497345 : Blo 1553474 3497345 := bstep (se 2 (by rfl) ⟨1311504, by rfl⟩ : syracuseStep 3497345 = 2623009) B2623009
theorem B3153355 : Blo 1553474 3153355 := bstep (se 1 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 3153355 = 4730033) B4730033
theorem B19914275 : Blo 1553474 19914275 := bstep (se 1 (by rfl) ⟨14935706, by rfl⟩ : syracuseStep 19914275 = 29871413) B29871413
theorem B7093811 : Blo 1553474 7093811 := bstep (se 1 (by rfl) ⟨5320358, by rfl⟩ : syracuseStep 7093811 = 10640717) B10640717
theorem B7872065 : Blo 1553474 7872065 := bstep (se 2 (by rfl) ⟨2952024, by rfl⟩ : syracuseStep 7872065 = 5904049) B5904049
theorem B2489945 : Blo 1553474 2489945 := bstep (se 2 (by rfl) ⟨933729, by rfl⟩ : syracuseStep 2489945 = 1867459) B1867459
theorem B3497561 : Blo 1553474 3497561 := bstep (se 2 (by rfl) ⟨1311585, by rfl⟩ : syracuseStep 3497561 = 2623171) B2623171
theorem B3366515 : Blo 1553474 3366515 := bstep (se 1 (by rfl) ⟨2524886, by rfl⟩ : syracuseStep 3366515 = 5049773) B5049773
theorem B3497651 : Blo 1553474 3497651 := bstep (se 1 (by rfl) ⟨2623238, by rfl⟩ : syracuseStep 3497651 = 5246477) B5246477
theorem B3497687 : Blo 1553474 3497687 := bstep (se 1 (by rfl) ⟨2623265, by rfl⟩ : syracuseStep 3497687 = 5246531) B5246531
theorem B4153139 : Blo 1553474 4153139 := bstep (se 1 (by rfl) ⟨3114854, by rfl⟩ : syracuseStep 4153139 = 6229709) B6229709
theorem B7470913 : Blo 1553474 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B3497867 : Blo 1553474 3497867 := bstep (se 1 (by rfl) ⟨2623400, by rfl⟩ : syracuseStep 3497867 = 5246801) B5246801
theorem B3497921 : Blo 1553474 3497921 := bstep (se 2 (by rfl) ⟨1311720, by rfl⟩ : syracuseStep 3497921 = 2623441) B2623441
theorem B1966123 : Blo 1553474 1966123 := bstep (se 1 (by rfl) ⟨1474592, by rfl⟩ : syracuseStep 1966123 = 2949185) B2949185
theorem B3498119 : Blo 1553474 3498119 := bstep (se 1 (by rfl) ⟨2623589, by rfl⟩ : syracuseStep 3498119 = 5247179) B5247179
theorem B7872713 : Blo 1553474 7872713 := bstep (se 2 (by rfl) ⟨2952267, by rfl⟩ : syracuseStep 7872713 = 5904535) B5904535
theorem B1966351 : Blo 1553474 1966351 := bstep (se 1 (by rfl) ⟨1474763, by rfl⟩ : syracuseStep 1966351 = 2949527) B2949527
theorem B4727069 : Blo 1553474 4727069 := bstep (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) B1772651
theorem B3735841 : Blo 1553474 3735841 := bstep (se 2 (by rfl) ⟨1400940, by rfl⟩ : syracuseStep 3735841 = 2801881) B2801881
theorem B3932459 : Blo 1553474 3932459 := bstep (se 1 (by rfl) ⟨2949344, by rfl⟩ : syracuseStep 3932459 = 5898689) B5898689
theorem B3498299 : Blo 1553474 3498299 := bstep (se 1 (by rfl) ⟨2623724, by rfl⟩ : syracuseStep 3498299 = 5247449) B5247449
theorem B4424051 : Blo 1553474 4424051 := bstep (se 1 (by rfl) ⟨3318038, by rfl⟩ : syracuseStep 4424051 = 6636077) B6636077
theorem B16810375 : Blo 1553474 16810375 := bstep (se 1 (by rfl) ⟨12607781, by rfl⟩ : syracuseStep 16810375 = 25215563) B25215563
theorem B3498425 : Blo 1553474 3498425 := bstep (se 2 (by rfl) ⟨1311909, by rfl⟩ : syracuseStep 3498425 = 2623819) B2623819
theorem B5243453 : Blo 1553474 5243453 := bstep (se 3 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 5243453 = 1966295) B1966295
theorem B2622071 : Blo 1553474 2622071 := bstep (se 1 (by rfl) ⟨1966553, by rfl⟩ : syracuseStep 2622071 = 3933107) B3933107
theorem B13271809 : Blo 1553474 13271809 := bstep (se 2 (by rfl) ⟨4976928, by rfl⟩ : syracuseStep 13271809 = 9953857) B9953857
theorem B3736331 : Blo 1553474 3736331 := bstep (se 1 (by rfl) ⟨2802248, by rfl⟩ : syracuseStep 3736331 = 5604497) B5604497
theorem B3498767 : Blo 1553474 3498767 := bstep (se 1 (by rfl) ⟨2624075, by rfl⟩ : syracuseStep 3498767 = 5248151) B5248151
theorem B3498785 : Blo 1553474 3498785 := bstep (se 2 (by rfl) ⟨1312044, by rfl⟩ : syracuseStep 3498785 = 2624089) B2624089
theorem B4424507 : Blo 1553474 4424507 := bstep (se 1 (by rfl) ⟨3318380, by rfl⟩ : syracuseStep 4424507 = 6636761) B6636761
theorem B4727699 : Blo 1553474 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B1967095 : Blo 1553474 1967095 := bstep (se 1 (by rfl) ⟨1475321, by rfl⟩ : syracuseStep 1967095 = 2950643) B2950643
theorem B2622523 : Blo 1553474 2622523 := bstep (se 1 (by rfl) ⟨1966892, by rfl⟩ : syracuseStep 2622523 = 3933785) B3933785
theorem B4375613 : Blo 1553474 4375613 := bstep (se 3 (by rfl) ⟨820427, by rfl⟩ : syracuseStep 4375613 = 1640855) B1640855
theorem B3933299 : Blo 1553474 3933299 := bstep (se 1 (by rfl) ⟨2949974, by rfl⟩ : syracuseStep 3933299 = 5899949) B5899949
theorem B3499127 : Blo 1553474 3499127 := bstep (se 1 (by rfl) ⟨2624345, by rfl⟩ : syracuseStep 3499127 = 5248691) B5248691
theorem B3933319 : Blo 1553474 3933319 := bstep (se 1 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 3933319 = 5899979) B5899979
theorem B2622665 : Blo 1553474 2622665 := bstep (se 2 (by rfl) ⟨983499, by rfl⟩ : syracuseStep 2622665 = 1966999) B1966999
theorem B2950415 : Blo 1553474 2950415 := bstep (se 1 (by rfl) ⟨2212811, by rfl⟩ : syracuseStep 2950415 = 4425623) B4425623
theorem B3499307 : Blo 1553474 3499307 := bstep (se 1 (by rfl) ⟨2624480, by rfl⟩ : syracuseStep 3499307 = 5248961) B5248961
theorem B1967419 : Blo 1553474 1967419 := bstep (se 1 (by rfl) ⟨1475564, by rfl⟩ : syracuseStep 1967419 = 2951129) B2951129
theorem B2213239 : Blo 1553474 2213239 := bstep (se 1 (by rfl) ⟨1659929, by rfl⟩ : syracuseStep 2213239 = 3319859) B3319859
theorem B7865747 : Blo 1553474 7865747 := bstep (se 1 (by rfl) ⟨5899310, by rfl⟩ : syracuseStep 7865747 = 11798621) B11798621
theorem B3933593 : Blo 1553474 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B8856985 : Blo 1553474 8856985 := bstep (se 2 (by rfl) ⟨3321369, by rfl⟩ : syracuseStep 8856985 = 6642739) B6642739
theorem B7980497 : Blo 1553474 7980497 := bstep (se 2 (by rfl) ⟨2992686, by rfl⟩ : syracuseStep 7980497 = 5985373) B5985373
theorem B4793867 : Blo 1553474 4793867 := bstep (se 1 (by rfl) ⟨3595400, by rfl⟩ : syracuseStep 4793867 = 7190801) B7190801
theorem B19908125 : Blo 1553474 19908125 := bstep (se 3 (by rfl) ⟨3732773, by rfl⟩ : syracuseStep 19908125 = 7465547) B7465547
theorem B9954859 : Blo 1553474 9954859 := bstep (se 1 (by rfl) ⟨7466144, by rfl⟩ : syracuseStep 9954859 = 14932289) B14932289
theorem B3933755 : Blo 1553474 3933755 := bstep (se 1 (by rfl) ⟨2950316, by rfl⟩ : syracuseStep 3933755 = 5900633) B5900633
theorem B11798135 : Blo 1553474 11798135 := bstep (se 1 (by rfl) ⟨8848601, by rfl⟩ : syracuseStep 11798135 = 17697203) B17697203
theorem B3499667 : Blo 1553474 3499667 := bstep (se 1 (by rfl) ⟨2624750, by rfl⟩ : syracuseStep 3499667 = 5249501) B5249501
theorem B2213563 : Blo 1553474 2213563 := bstep (se 1 (by rfl) ⟨1660172, by rfl⟩ : syracuseStep 2213563 = 3320345) B3320345
theorem B3499721 : Blo 1553474 3499721 := bstep (se 2 (by rfl) ⟨1312395, by rfl⟩ : syracuseStep 3499721 = 2624791) B2624791
theorem B3933967 : Blo 1553474 3933967 := bstep (se 1 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 3933967 = 5900951) B5900951
theorem B7472911 : Blo 1553474 7472911 := bstep (se 1 (by rfl) ⟨5604683, by rfl⟩ : syracuseStep 7472911 = 11209367) B11209367
theorem B1967915 : Blo 1553474 1967915 := bstep (se 1 (by rfl) ⟨1475936, by rfl⟩ : syracuseStep 1967915 = 2951873) B2951873
theorem B33613643 : Blo 1553474 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B5900147 : Blo 1553474 5900147 := bstep (se 1 (by rfl) ⟨4425110, by rfl⟩ : syracuseStep 5900147 = 8850221) B8850221
theorem B17033075 : Blo 1553474 17033075 := bstep (se 1 (by rfl) ⟨12774806, by rfl⟩ : syracuseStep 17033075 = 25549613) B25549613
theorem B2623367 : Blo 1553474 2623367 := bstep (se 1 (by rfl) ⟨1967525, by rfl⟩ : syracuseStep 2623367 = 3935051) B3935051
theorem B5244857 : Blo 1553474 5244857 := bstep (se 2 (by rfl) ⟨1966821, by rfl⟩ : syracuseStep 5244857 = 3933643) B3933643
theorem B6727691 : Blo 1553474 6727691 := bstep (se 1 (by rfl) ⟨5045768, by rfl⟩ : syracuseStep 6727691 = 10091537) B10091537
theorem B3934241 : Blo 1553474 3934241 := bstep (se 2 (by rfl) ⟨1475340, by rfl⟩ : syracuseStep 3934241 = 2950681) B2950681
theorem B7473389 : Blo 1553474 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B1968391 : Blo 1553474 1968391 := bstep (se 1 (by rfl) ⟨1476293, by rfl⟩ : syracuseStep 1968391 = 2952587) B2952587
theorem B1575227 : Blo 1553474 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B4729207 : Blo 1553474 4729207 := bstep (se 1 (by rfl) ⟨3546905, by rfl⟩ : syracuseStep 4729207 = 7093811) B7093811
theorem B33606035 : Blo 1553474 33606035 := bstep (se 1 (by rfl) ⟨25204526, by rfl⟩ : syracuseStep 33606035 = 50409053) B50409053
theorem B13453789 : Blo 1553474 13453789 := bstep (se 3 (by rfl) ⟨2522585, by rfl⟩ : syracuseStep 13453789 = 5045171) B5045171
theorem B5245451 : Blo 1553474 5245451 := bstep (se 1 (by rfl) ⟨3934088, by rfl⟩ : syracuseStep 5245451 = 7868177) B7868177
theorem B2624015 : Blo 1553474 2624015 := bstep (se 1 (by rfl) ⟨1968011, by rfl⟩ : syracuseStep 2624015 = 3936023) B3936023
theorem B11799107 : Blo 1553474 11799107 := bstep (se 1 (by rfl) ⟨8849330, by rfl⟩ : syracuseStep 11799107 = 17698661) B17698661
theorem B5605955 : Blo 1553474 5605955 := bstep (se 1 (by rfl) ⟨4204466, by rfl⟩ : syracuseStep 5605955 = 8408933) B8408933
theorem B5245559 : Blo 1553474 5245559 := bstep (se 1 (by rfl) ⟨3934169, by rfl⟩ : syracuseStep 5245559 = 7868339) B7868339
theorem B13273793 : Blo 1553474 13273793 := bstep (se 2 (by rfl) ⟨4977672, by rfl⟩ : syracuseStep 13273793 = 9955345) B9955345
theorem B2952055 : Blo 1553474 2952055 := bstep (se 1 (by rfl) ⟨2214041, by rfl⟩ : syracuseStep 2952055 = 4428083) B4428083
theorem B1747975 : Blo 1553474 1747975 := bstep (se 1 (by rfl) ⟨1310981, by rfl⟩ : syracuseStep 1747975 = 2621963) B2621963
theorem B3935243 : Blo 1553474 3935243 := bstep (se 1 (by rfl) ⟨2951432, by rfl⟩ : syracuseStep 3935243 = 5902865) B5902865
theorem B2624555 : Blo 1553474 2624555 := bstep (se 1 (by rfl) ⟨1968416, by rfl⟩ : syracuseStep 2624555 = 3936833) B3936833
theorem B1748155 : Blo 1553474 1748155 := bstep (se 1 (by rfl) ⟨1311116, by rfl⟩ : syracuseStep 1748155 = 2622233) B2622233
theorem B5246153 : Blo 1553474 5246153 := bstep (se 2 (by rfl) ⟨1967307, by rfl⟩ : syracuseStep 5246153 = 3934615) B3934615
theorem B5983433 : Blo 1553474 5983433 := bstep (se 2 (by rfl) ⟨2243787, by rfl⟩ : syracuseStep 5983433 = 4487575) B4487575
theorem B13282541 : Blo 1553474 13282541 := bstep (se 3 (by rfl) ⟨2490476, by rfl⟩ : syracuseStep 13282541 = 4980953) B4980953
theorem B2657551 : Blo 1553474 2657551 := bstep (se 1 (by rfl) ⟨1993163, by rfl⟩ : syracuseStep 2657551 = 3986327) B3986327
theorem B31894883 : Blo 1553474 31894883 := bstep (se 1 (by rfl) ⟨23921162, by rfl⟩ : syracuseStep 31894883 = 47842325) B47842325
theorem B12610961 : Blo 1553474 12610961 := bstep (se 2 (by rfl) ⟨4729110, by rfl⟩ : syracuseStep 12610961 = 9458221) B9458221
theorem B23932493 : Blo 1553474 23932493 := bstep (se 3 (by rfl) ⟨4487342, by rfl⟩ : syracuseStep 23932493 = 8974685) B8974685
theorem B2330231 : Blo 1553474 2330231 := bstep (se 1 (by rfl) ⟨1747673, by rfl⟩ : syracuseStep 2330231 = 3495347) B3495347
theorem B4427399 : Blo 1553474 4427399 := bstep (se 1 (by rfl) ⟨3320549, by rfl⟩ : syracuseStep 4427399 = 6641099) B6641099
theorem B2330255 : Blo 1553474 2330255 := bstep (se 1 (by rfl) ⟨1747691, by rfl⟩ : syracuseStep 2330255 = 3495383) B3495383
theorem B1748623 : Blo 1553474 1748623 := bstep (se 1 (by rfl) ⟨1311467, by rfl⟩ : syracuseStep 1748623 = 2622935) B2622935
theorem B3935891 : Blo 1553474 3935891 := bstep (se 1 (by rfl) ⟨2951918, by rfl⟩ : syracuseStep 3935891 = 5903837) B5903837
theorem B2330297 : Blo 1553474 2330297 := bstep (se 2 (by rfl) ⟨873861, by rfl⟩ : syracuseStep 2330297 = 1747723) B1747723
theorem B2330375 : Blo 1553474 2330375 := bstep (se 1 (by rfl) ⟨1747781, by rfl⟩ : syracuseStep 2330375 = 3495563) B3495563
theorem B2330411 : Blo 1553474 2330411 := bstep (se 1 (by rfl) ⟨1747808, by rfl⟩ : syracuseStep 2330411 = 3495617) B3495617
theorem B3321643 : Blo 1553474 3321643 := bstep (se 1 (by rfl) ⟨2491232, by rfl⟩ : syracuseStep 3321643 = 4982465) B4982465
theorem B1773371 : Blo 1553474 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B2330441 : Blo 1553474 2330441 := bstep (se 2 (by rfl) ⟨873915, by rfl⟩ : syracuseStep 2330441 = 1747831) B1747831
theorem B5246855 : Blo 1553474 5246855 := bstep (se 1 (by rfl) ⟨3935141, by rfl⟩ : syracuseStep 5246855 = 7870283) B7870283
theorem B2101135 : Blo 1553474 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B3936185 : Blo 1553474 3936185 := bstep (se 2 (by rfl) ⟨1476069, by rfl⟩ : syracuseStep 3936185 = 2952139) B2952139
theorem B2330555 : Blo 1553474 2330555 := bstep (se 1 (by rfl) ⟨1747916, by rfl⟩ : syracuseStep 2330555 = 3495833) B3495833
theorem B2330615 : Blo 1553474 2330615 := bstep (se 1 (by rfl) ⟨1747961, by rfl⟩ : syracuseStep 2330615 = 3495923) B3495923
theorem B7467011 : Blo 1553474 7467011 := bstep (se 1 (by rfl) ⟨5600258, by rfl⟩ : syracuseStep 7467011 = 11200517) B11200517
theorem B2330639 : Blo 1553474 2330639 := bstep (se 1 (by rfl) ⟨1747979, by rfl⟩ : syracuseStep 2330639 = 3495959) B3495959
theorem B5902379 : Blo 1553474 5902379 := bstep (se 1 (by rfl) ⟨4426784, by rfl⟩ : syracuseStep 5902379 = 8853569) B8853569
theorem B2330681 : Blo 1553474 2330681 := bstep (se 2 (by rfl) ⟨874005, by rfl⟩ : syracuseStep 2330681 = 1748011) B1748011
theorem B2330759 : Blo 1553474 2330759 := bstep (se 1 (by rfl) ⟨1748069, by rfl⟩ : syracuseStep 2330759 = 3496139) B3496139
theorem B1749127 : Blo 1553474 1749127 := bstep (se 1 (by rfl) ⟨1311845, by rfl⟩ : syracuseStep 1749127 = 2623691) B2623691
theorem B2330795 : Blo 1553474 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B2330825 : Blo 1553474 2330825 := bstep (se 2 (by rfl) ⟨874059, by rfl⟩ : syracuseStep 2330825 = 1748119) B1748119
theorem B6639853 : Blo 1553474 6639853 := bstep (se 3 (by rfl) ⟨1244972, by rfl⟩ : syracuseStep 6639853 = 2489945) B2489945
theorem B72773873 : Blo 1553474 72773873 := bstep (se 2 (by rfl) ⟨27290202, by rfl⟩ : syracuseStep 72773873 = 54580405) B54580405
theorem B5247233 : Blo 1553474 5247233 := bstep (se 2 (by rfl) ⟨1967712, by rfl⟩ : syracuseStep 5247233 = 3935425) B3935425
theorem B2330939 : Blo 1553474 2330939 := bstep (se 1 (by rfl) ⟨1748204, by rfl⟩ : syracuseStep 2330939 = 3496409) B3496409
theorem B1749307 : Blo 1553474 1749307 := bstep (se 1 (by rfl) ⟨1311980, by rfl⟩ : syracuseStep 1749307 = 2623961) B2623961
theorem B2330999 : Blo 1553474 2330999 := bstep (se 1 (by rfl) ⟨1748249, by rfl⟩ : syracuseStep 2330999 = 3496499) B3496499
theorem B2331023 : Blo 1553474 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B17707409 : Blo 1553474 17707409 := bstep (se 2 (by rfl) ⟨6640278, by rfl⟩ : syracuseStep 17707409 = 13280557) B13280557
theorem B7868825 : Blo 1553474 7868825 := bstep (se 2 (by rfl) ⟨2950809, by rfl⟩ : syracuseStep 7868825 = 5901619) B5901619
theorem B2331065 : Blo 1553474 2331065 := bstep (se 2 (by rfl) ⟨874149, by rfl⟩ : syracuseStep 2331065 = 1748299) B1748299
theorem B2331143 : Blo 1553474 2331143 := bstep (se 1 (by rfl) ⟨1748357, by rfl⟩ : syracuseStep 2331143 = 3496715) B3496715
theorem B2331179 : Blo 1553474 2331179 := bstep (se 1 (by rfl) ⟨1748384, by rfl⟩ : syracuseStep 2331179 = 3496769) B3496769
theorem B2331209 : Blo 1553474 2331209 := bstep (se 2 (by rfl) ⟨874203, by rfl⟩ : syracuseStep 2331209 = 1748407) B1748407
theorem B3936883 : Blo 1553474 3936883 := bstep (se 1 (by rfl) ⟨2952662, by rfl⟩ : syracuseStep 3936883 = 5905325) B5905325
theorem B6304375 : Blo 1553474 6304375 := bstep (se 1 (by rfl) ⟨4728281, by rfl⟩ : syracuseStep 6304375 = 9456563) B9456563
theorem B2331323 : Blo 1553474 2331323 := bstep (se 1 (by rfl) ⟨1748492, by rfl⟩ : syracuseStep 2331323 = 3496985) B3496985
theorem B2331383 : Blo 1553474 2331383 := bstep (se 1 (by rfl) ⟨1748537, by rfl⟩ : syracuseStep 2331383 = 3497075) B3497075
theorem B3937025 : Blo 1553474 3937025 := bstep (se 2 (by rfl) ⟨1476384, by rfl⟩ : syracuseStep 3937025 = 2952769) B2952769
theorem B2331407 : Blo 1553474 2331407 := bstep (se 1 (by rfl) ⟨1748555, by rfl⟩ : syracuseStep 2331407 = 3497111) B3497111
theorem B1749775 : Blo 1553474 1749775 := bstep (se 1 (by rfl) ⟨1312331, by rfl⟩ : syracuseStep 1749775 = 2624663) B2624663
theorem B2732843 : Blo 1553474 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B2331449 : Blo 1553474 2331449 := bstep (se 2 (by rfl) ⟨874293, by rfl⟩ : syracuseStep 2331449 = 1748587) B1748587
theorem B6304571 : Blo 1553474 6304571 := bstep (se 1 (by rfl) ⟨4728428, by rfl⟩ : syracuseStep 6304571 = 9456857) B9456857
theorem B9458491 : Blo 1553474 9458491 := bstep (se 1 (by rfl) ⟨7093868, by rfl⟩ : syracuseStep 9458491 = 14187737) B14187737
theorem B34091891 : Blo 1553474 34091891 := bstep (se 1 (by rfl) ⟨25568918, by rfl⟩ : syracuseStep 34091891 = 51137837) B51137837
theorem B2331527 : Blo 1553474 2331527 := bstep (se 1 (by rfl) ⟨1748645, by rfl⟩ : syracuseStep 2331527 = 3497291) B3497291
theorem B2331563 : Blo 1553474 2331563 := bstep (se 1 (by rfl) ⟨1748672, by rfl⟩ : syracuseStep 2331563 = 3497345) B3497345
theorem B61395893 : Blo 1553474 61395893 := bstep (se 5 (by rfl) ⟨2877932, by rfl⟩ : syracuseStep 61395893 = 5755865) B5755865
theorem B2331593 : Blo 1553474 2331593 := bstep (se 2 (by rfl) ⟨874347, by rfl⟩ : syracuseStep 2331593 = 1748695) B1748695
theorem B13276183 : Blo 1553474 13276183 := bstep (se 1 (by rfl) ⟨9957137, by rfl⟩ : syracuseStep 13276183 = 19914275) B19914275
theorem B5248043 : Blo 1553474 5248043 := bstep (se 1 (by rfl) ⟨3936032, by rfl⟩ : syracuseStep 5248043 = 7872065) B7872065
theorem B2331707 : Blo 1553474 2331707 := bstep (se 1 (by rfl) ⟨1748780, by rfl⟩ : syracuseStep 2331707 = 3497561) B3497561
theorem B2331767 : Blo 1553474 2331767 := bstep (se 1 (by rfl) ⟨1748825, by rfl⟩ : syracuseStep 2331767 = 3497651) B3497651
theorem B1553543 : Blo 1553474 1553543 := bstep (se 1 (by rfl) ⟨1165157, by rfl⟩ : syracuseStep 1553543 = 2330315) B2330315
theorem B1553551 : Blo 1553474 1553551 := bstep (se 1 (by rfl) ⟨1165163, by rfl⟩ : syracuseStep 1553551 = 2330327) B2330327
theorem B2331791 : Blo 1553474 2331791 := bstep (se 1 (by rfl) ⟨1748843, by rfl⟩ : syracuseStep 2331791 = 3497687) B3497687
theorem B2331833 : Blo 1553474 2331833 := bstep (se 2 (by rfl) ⟨874437, by rfl⟩ : syracuseStep 2331833 = 1748875) B1748875
theorem B1553595 : Blo 1553474 1553595 := bstep (se 1 (by rfl) ⟨1165196, by rfl⟩ : syracuseStep 1553595 = 2330393) B2330393
theorem B1553671 : Blo 1553474 1553671 := bstep (se 1 (by rfl) ⟨1165253, by rfl⟩ : syracuseStep 1553671 = 2330507) B2330507
theorem B2331911 : Blo 1553474 2331911 := bstep (se 1 (by rfl) ⟨1748933, by rfl⟩ : syracuseStep 2331911 = 3497867) B3497867
theorem B1553679 : Blo 1553474 1553679 := bstep (se 1 (by rfl) ⟨1165259, by rfl⟩ : syracuseStep 1553679 = 2330519) B2330519
theorem B2331947 : Blo 1553474 2331947 := bstep (se 1 (by rfl) ⟨1748960, by rfl⟩ : syracuseStep 2331947 = 3497921) B3497921
theorem B1553723 : Blo 1553474 1553723 := bstep (se 1 (by rfl) ⟨1165292, by rfl⟩ : syracuseStep 1553723 = 2330585) B2330585
theorem B2331977 : Blo 1553474 2331977 := bstep (se 2 (by rfl) ⟨874491, by rfl⟩ : syracuseStep 2331977 = 1748983) B1748983
theorem B3732851 : Blo 1553474 3732851 := bstep (se 1 (by rfl) ⟨2799638, by rfl⟩ : syracuseStep 3732851 = 5599277) B5599277
theorem B4724087 : Blo 1553474 4724087 := bstep (se 1 (by rfl) ⟨3543065, by rfl⟩ : syracuseStep 4724087 = 7086131) B7086131
theorem B1553799 : Blo 1553474 1553799 := bstep (se 1 (by rfl) ⟨1165349, by rfl⟩ : syracuseStep 1553799 = 2330699) B2330699
theorem B1553807 : Blo 1553474 1553807 := bstep (se 1 (by rfl) ⟨1165355, by rfl⟩ : syracuseStep 1553807 = 2330711) B2330711
theorem B1553851 : Blo 1553474 1553851 := bstep (se 1 (by rfl) ⟨1165388, by rfl⟩ : syracuseStep 1553851 = 2330777) B2330777
theorem B2332091 : Blo 1553474 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B2332151 : Blo 1553474 2332151 := bstep (se 1 (by rfl) ⟨1749113, by rfl⟩ : syracuseStep 2332151 = 3498227) B3498227
theorem B3986945 : Blo 1553474 3986945 := bstep (se 2 (by rfl) ⟨1495104, by rfl⟩ : syracuseStep 3986945 = 2990209) B2990209
theorem B4429313 : Blo 1553474 4429313 := bstep (se 2 (by rfl) ⟨1660992, by rfl⟩ : syracuseStep 4429313 = 3321985) B3321985
theorem B1553927 : Blo 1553474 1553927 := bstep (se 1 (by rfl) ⟨1165445, by rfl⟩ : syracuseStep 1553927 = 2330891) B2330891
theorem B9451019 : Blo 1553474 9451019 := bstep (se 1 (by rfl) ⟨7088264, by rfl⟩ : syracuseStep 9451019 = 14176529) B14176529
theorem B1553935 : Blo 1553474 1553935 := bstep (se 1 (by rfl) ⟨1165451, by rfl⟩ : syracuseStep 1553935 = 2330903) B2330903
theorem B2332175 : Blo 1553474 2332175 := bstep (se 1 (by rfl) ⟨1749131, by rfl⟩ : syracuseStep 2332175 = 3498263) B3498263
theorem B2332217 : Blo 1553474 2332217 := bstep (se 2 (by rfl) ⟨874581, by rfl⟩ : syracuseStep 2332217 = 1749163) B1749163
theorem B1553979 : Blo 1553474 1553979 := bstep (se 1 (by rfl) ⟨1165484, by rfl⟩ : syracuseStep 1553979 = 2330969) B2330969
theorem B13284931 : Blo 1553474 13284931 := bstep (se 1 (by rfl) ⟨9963698, by rfl⟩ : syracuseStep 13284931 = 19927397) B19927397
theorem B1554055 : Blo 1553474 1554055 := bstep (se 1 (by rfl) ⟨1165541, by rfl⟩ : syracuseStep 1554055 = 2331083) B2331083
theorem B2332295 : Blo 1553474 2332295 := bstep (se 1 (by rfl) ⟨1749221, by rfl⟩ : syracuseStep 2332295 = 3498443) B3498443
theorem B1554063 : Blo 1553474 1554063 := bstep (se 1 (by rfl) ⟨1165547, by rfl⟩ : syracuseStep 1554063 = 2331095) B2331095
theorem B2332331 : Blo 1553474 2332331 := bstep (se 1 (by rfl) ⟨1749248, by rfl⟩ : syracuseStep 2332331 = 3498497) B3498497
theorem B1554107 : Blo 1553474 1554107 := bstep (se 1 (by rfl) ⟨1165580, by rfl⟩ : syracuseStep 1554107 = 2331161) B2331161
theorem B2332361 : Blo 1553474 2332361 := bstep (se 2 (by rfl) ⟨874635, by rfl⟩ : syracuseStep 2332361 = 1749271) B1749271
theorem B1554183 : Blo 1553474 1554183 := bstep (se 1 (by rfl) ⟨1165637, by rfl⟩ : syracuseStep 1554183 = 2331275) B2331275
theorem B1554191 : Blo 1553474 1554191 := bstep (se 1 (by rfl) ⟨1165643, by rfl⟩ : syracuseStep 1554191 = 2331287) B2331287
theorem B1554235 : Blo 1553474 1554235 := bstep (se 1 (by rfl) ⟨1165676, by rfl⟩ : syracuseStep 1554235 = 2331353) B2331353
theorem B2332475 : Blo 1553474 2332475 := bstep (se 1 (by rfl) ⟨1749356, by rfl⟩ : syracuseStep 2332475 = 3498713) B3498713
theorem B18904907 : Blo 1553474 18904907 := bstep (se 1 (by rfl) ⟨14178680, by rfl⟩ : syracuseStep 18904907 = 28357361) B28357361
theorem B2332535 : Blo 1553474 2332535 := bstep (se 1 (by rfl) ⟨1749401, by rfl⟩ : syracuseStep 2332535 = 3498803) B3498803
theorem B3495815 : Blo 1553474 3495815 := bstep (se 1 (by rfl) ⟨2621861, by rfl⟩ : syracuseStep 3495815 = 5243723) B5243723
theorem B1554311 : Blo 1553474 1554311 := bstep (se 1 (by rfl) ⟨1165733, by rfl⟩ : syracuseStep 1554311 = 2331467) B2331467
theorem B1554319 : Blo 1553474 1554319 := bstep (se 1 (by rfl) ⟨1165739, by rfl⟩ : syracuseStep 1554319 = 2331479) B2331479
theorem B2332559 : Blo 1553474 2332559 := bstep (se 1 (by rfl) ⟨1749419, by rfl⟩ : syracuseStep 2332559 = 3498839) B3498839
theorem B2332601 : Blo 1553474 2332601 := bstep (se 2 (by rfl) ⟨874725, by rfl⟩ : syracuseStep 2332601 = 1749451) B1749451
theorem B1554363 : Blo 1553474 1554363 := bstep (se 1 (by rfl) ⟨1165772, by rfl⟩ : syracuseStep 1554363 = 2331545) B2331545
theorem B7469009 : Blo 1553474 7469009 := bstep (se 2 (by rfl) ⟨2800878, by rfl⟩ : syracuseStep 7469009 = 5601757) B5601757
theorem B1554439 : Blo 1553474 1554439 := bstep (se 1 (by rfl) ⟨1165829, by rfl⟩ : syracuseStep 1554439 = 2331659) B2331659
theorem B2332679 : Blo 1553474 2332679 := bstep (se 1 (by rfl) ⟨1749509, by rfl⟩ : syracuseStep 2332679 = 3499019) B3499019
theorem B1554447 : Blo 1553474 1554447 := bstep (se 1 (by rfl) ⟨1165835, by rfl⟩ : syracuseStep 1554447 = 2331671) B2331671
theorem B6912029 : Blo 1553474 6912029 := bstep (se 3 (by rfl) ⟨1296005, by rfl⟩ : syracuseStep 6912029 = 2592011) B2592011
theorem B2332715 : Blo 1553474 2332715 := bstep (se 1 (by rfl) ⟨1749536, by rfl⟩ : syracuseStep 2332715 = 3499073) B3499073
theorem B3495995 : Blo 1553474 3495995 := bstep (se 1 (by rfl) ⟨2621996, by rfl⟩ : syracuseStep 3495995 = 5243993) B5243993
theorem B1554491 : Blo 1553474 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B2332745 : Blo 1553474 2332745 := bstep (se 2 (by rfl) ⟨874779, by rfl⟩ : syracuseStep 2332745 = 1749559) B1749559
theorem B11982935 : Blo 1553474 11982935 := bstep (se 1 (by rfl) ⟨8987201, by rfl⟩ : syracuseStep 11982935 = 17974403) B17974403
theorem B3733619 : Blo 1553474 3733619 := bstep (se 1 (by rfl) ⟨2800214, by rfl⟩ : syracuseStep 3733619 = 5600429) B5600429
theorem B2488439 : Blo 1553474 2488439 := bstep (se 1 (by rfl) ⟨1866329, by rfl⟩ : syracuseStep 2488439 = 3732659) B3732659
theorem B6641783 : Blo 1553474 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B1554567 : Blo 1553474 1554567 := bstep (se 1 (by rfl) ⟨1165925, by rfl⟩ : syracuseStep 1554567 = 2331851) B2331851
theorem B1554575 : Blo 1553474 1554575 := bstep (se 1 (by rfl) ⟨1165931, by rfl⟩ : syracuseStep 1554575 = 2331863) B2331863
theorem B3496121 : Blo 1553474 3496121 := bstep (se 2 (by rfl) ⟨1311045, by rfl⟩ : syracuseStep 3496121 = 2622091) B2622091
theorem B1554619 : Blo 1553474 1554619 := bstep (se 1 (by rfl) ⟨1165964, by rfl⟩ : syracuseStep 1554619 = 2331929) B2331929
theorem B2332859 : Blo 1553474 2332859 := bstep (se 1 (by rfl) ⟨1749644, by rfl⟩ : syracuseStep 2332859 = 3499289) B3499289
theorem B2332919 : Blo 1553474 2332919 := bstep (se 1 (by rfl) ⟨1749689, by rfl⟩ : syracuseStep 2332919 = 3499379) B3499379
theorem B1554695 : Blo 1553474 1554695 := bstep (se 1 (by rfl) ⟨1166021, by rfl⟩ : syracuseStep 1554695 = 2332043) B2332043
theorem B1554703 : Blo 1553474 1554703 := bstep (se 1 (by rfl) ⟨1166027, by rfl⟩ : syracuseStep 1554703 = 2332055) B2332055
theorem B2332943 : Blo 1553474 2332943 := bstep (se 1 (by rfl) ⟨1749707, by rfl⟩ : syracuseStep 2332943 = 3499415) B3499415
theorem B2488619 : Blo 1553474 2488619 := bstep (se 1 (by rfl) ⟨1866464, by rfl⟩ : syracuseStep 2488619 = 3732929) B3732929
theorem B2332985 : Blo 1553474 2332985 := bstep (se 2 (by rfl) ⟨874869, by rfl⟩ : syracuseStep 2332985 = 1749739) B1749739
theorem B1554747 : Blo 1553474 1554747 := bstep (se 1 (by rfl) ⟨1166060, by rfl⟩ : syracuseStep 1554747 = 2332121) B2332121
theorem B5249339 : Blo 1553474 5249339 := bstep (se 1 (by rfl) ⟨3937004, by rfl⟩ : syracuseStep 5249339 = 7874009) B7874009
theorem B1554823 : Blo 1553474 1554823 := bstep (se 1 (by rfl) ⟨1166117, by rfl⟩ : syracuseStep 1554823 = 2332235) B2332235
theorem B2333063 : Blo 1553474 2333063 := bstep (se 1 (by rfl) ⟨1749797, by rfl⟩ : syracuseStep 2333063 = 3499595) B3499595
theorem B1554831 : Blo 1553474 1554831 := bstep (se 1 (by rfl) ⟨1166123, by rfl⟩ : syracuseStep 1554831 = 2332247) B2332247
theorem B2333099 : Blo 1553474 2333099 := bstep (se 1 (by rfl) ⟨1749824, by rfl⟩ : syracuseStep 2333099 = 3499649) B3499649
theorem B11811257 : Blo 1553474 11811257 := bstep (se 2 (by rfl) ⟨4429221, by rfl⟩ : syracuseStep 11811257 = 8858443) B8858443
theorem B1554875 : Blo 1553474 1554875 := bstep (se 1 (by rfl) ⟨1166156, by rfl⟩ : syracuseStep 1554875 = 2332313) B2332313
theorem B2333129 : Blo 1553474 2333129 := bstep (se 2 (by rfl) ⟨874923, by rfl⟩ : syracuseStep 2333129 = 1749847) B1749847
theorem B1554951 : Blo 1553474 1554951 := bstep (se 1 (by rfl) ⟨1166213, by rfl⟩ : syracuseStep 1554951 = 2332427) B2332427
theorem B3496463 : Blo 1553474 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B1554959 : Blo 1553474 1554959 := bstep (se 1 (by rfl) ⟨1166219, by rfl⟩ : syracuseStep 1554959 = 2332439) B2332439
theorem B3496481 : Blo 1553474 3496481 := bstep (se 2 (by rfl) ⟨1311180, by rfl⟩ : syracuseStep 3496481 = 2622361) B2622361
theorem B1555003 : Blo 1553474 1555003 := bstep (se 1 (by rfl) ⟨1166252, by rfl⟩ : syracuseStep 1555003 = 2332505) B2332505
theorem B12606029 : Blo 1553474 12606029 := bstep (se 3 (by rfl) ⟨2363630, by rfl⟩ : syracuseStep 12606029 = 4727261) B4727261
theorem B1555079 : Blo 1553474 1555079 := bstep (se 1 (by rfl) ⟨1166309, by rfl⟩ : syracuseStep 1555079 = 2332619) B2332619
theorem B1555087 : Blo 1553474 1555087 := bstep (se 1 (by rfl) ⟨1166315, by rfl⟩ : syracuseStep 1555087 = 2332631) B2332631
theorem B1555131 : Blo 1553474 1555131 := bstep (se 1 (by rfl) ⟨1166348, by rfl⟩ : syracuseStep 1555131 = 2332697) B2332697
theorem B1555207 : Blo 1553474 1555207 := bstep (se 1 (by rfl) ⟨1166405, by rfl⟩ : syracuseStep 1555207 = 2332811) B2332811
theorem B1555215 : Blo 1553474 1555215 := bstep (se 1 (by rfl) ⟨1166411, by rfl⟩ : syracuseStep 1555215 = 2332823) B2332823
theorem B2489131 : Blo 1553474 2489131 := bstep (se 1 (by rfl) ⟨1866848, by rfl⟩ : syracuseStep 2489131 = 3733697) B3733697
theorem B1555259 : Blo 1553474 1555259 := bstep (se 1 (by rfl) ⟨1166444, by rfl⟩ : syracuseStep 1555259 = 2332889) B2332889
theorem B11803481 : Blo 1553474 11803481 := bstep (se 2 (by rfl) ⟨4426305, by rfl⟩ : syracuseStep 11803481 = 8852611) B8852611
theorem B3496823 : Blo 1553474 3496823 := bstep (se 1 (by rfl) ⟨2622617, by rfl⟩ : syracuseStep 3496823 = 5245235) B5245235
theorem B1555335 : Blo 1553474 1555335 := bstep (se 1 (by rfl) ⟨1166501, by rfl⟩ : syracuseStep 1555335 = 2333003) B2333003
theorem B1555343 : Blo 1553474 1555343 := bstep (se 1 (by rfl) ⟨1166507, by rfl⟩ : syracuseStep 1555343 = 2333015) B2333015
theorem B67271573 : Blo 1553474 67271573 := bstep (se 6 (by rfl) ⟨1576677, by rfl⟩ : syracuseStep 67271573 = 3153355) B3153355
theorem B7871417 : Blo 1553474 7871417 := bstep (se 2 (by rfl) ⟨2951781, by rfl⟩ : syracuseStep 7871417 = 5903563) B5903563
theorem B1555387 : Blo 1553474 1555387 := bstep (se 1 (by rfl) ⟨1166540, by rfl⟩ : syracuseStep 1555387 = 2333081) B2333081
theorem B1555463 : Blo 1553474 1555463 := bstep (se 1 (by rfl) ⟨1166597, by rfl⟩ : syracuseStep 1555463 = 2333195) B2333195
theorem B1555471 : Blo 1553474 1555471 := bstep (se 1 (by rfl) ⟨1166603, by rfl⟩ : syracuseStep 1555471 = 2333207) B2333207
theorem B2489387 : Blo 1553474 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B3497003 : Blo 1553474 3497003 := bstep (se 1 (by rfl) ⟨2622752, by rfl⟩ : syracuseStep 3497003 = 5245505) B5245505
theorem B8854595 : Blo 1553474 8854595 := bstep (se 1 (by rfl) ⟨6640946, by rfl⟩ : syracuseStep 8854595 = 13281893) B13281893
theorem B5602391 : Blo 1553474 5602391 := bstep (se 1 (by rfl) ⟨4201793, by rfl⟩ : syracuseStep 5602391 = 8403587) B8403587
theorem B17710325 : Blo 1553474 17710325 := bstep (se 5 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 17710325 = 1660343) B1660343
theorem B3497363 : Blo 1553474 3497363 := bstep (se 1 (by rfl) ⟨2623022, by rfl⟩ : syracuseStep 3497363 = 5246045) B5246045
theorem B5905811 : Blo 1553474 5905811 := bstep (se 1 (by rfl) ⟨4429358, by rfl⟩ : syracuseStep 5905811 = 8858717) B8858717
theorem B2801081 : Blo 1553474 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B3497417 : Blo 1553474 3497417 := bstep (se 2 (by rfl) ⟨1311531, by rfl⟩ : syracuseStep 3497417 = 2623063) B2623063
theorem B13286915 : Blo 1553474 13286915 := bstep (se 1 (by rfl) ⟨9965186, by rfl⟩ : syracuseStep 13286915 = 19930373) B19930373
theorem B1867271 : Blo 1553474 1867271 := bstep (se 1 (by rfl) ⟨1400453, by rfl⟩ : syracuseStep 1867271 = 2800907) B2800907
theorem B14188061 : Blo 1553474 14188061 := bstep (se 3 (by rfl) ⟨2660261, by rfl⟩ : syracuseStep 14188061 = 5320523) B5320523
theorem B2244343 : Blo 1553474 2244343 := bstep (se 1 (by rfl) ⟨1683257, by rfl⟩ : syracuseStep 2244343 = 3366515) B3366515
theorem B9961217 : Blo 1553474 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B2801441 : Blo 1553474 2801441 := bstep (se 2 (by rfl) ⟨1050540, by rfl⟩ : syracuseStep 2801441 = 2101081) B2101081
theorem B11804453 : Blo 1553474 11804453 := bstep (se 4 (by rfl) ⟨1106667, by rfl⟩ : syracuseStep 11804453 = 2213335) B2213335
theorem B2768759 : Blo 1553474 2768759 := bstep (se 1 (by rfl) ⟨2076569, by rfl⟩ : syracuseStep 2768759 = 4153139) B4153139
theorem B2621497 : Blo 1553474 2621497 := bstep (se 2 (by rfl) ⟨983061, by rfl⟩ : syracuseStep 2621497 = 1966123) B1966123
theorem B3498155 : Blo 1553474 3498155 := bstep (se 1 (by rfl) ⟨2623616, by rfl⟩ : syracuseStep 3498155 = 5247233) B5247233
theorem B2621639 : Blo 1553474 2621639 := bstep (se 1 (by rfl) ⟨1966229, by rfl⟩ : syracuseStep 2621639 = 3932459) B3932459
theorem B2949367 : Blo 1553474 2949367 := bstep (se 1 (by rfl) ⟨2212025, by rfl⟩ : syracuseStep 2949367 = 4424051) B4424051
theorem B11804939 : Blo 1553474 11804939 := bstep (se 1 (by rfl) ⟨8853704, by rfl⟩ : syracuseStep 11804939 = 17707409) B17707409
theorem B6635837 : Blo 1553474 6635837 := bstep (se 3 (by rfl) ⟨1244219, by rfl⟩ : syracuseStep 6635837 = 2488439) B2488439
theorem B2621801 : Blo 1553474 2621801 := bstep (se 2 (by rfl) ⟨983175, by rfl⟩ : syracuseStep 2621801 = 1966351) B1966351
theorem B4981121 : Blo 1553474 4981121 := bstep (se 2 (by rfl) ⟨1867920, by rfl⟩ : syracuseStep 4981121 = 3735841) B3735841
theorem B2490887 : Blo 1553474 2490887 := bstep (se 1 (by rfl) ⟨1868165, by rfl⟩ : syracuseStep 2490887 = 3736331) B3736331
theorem B22413833 : Blo 1553474 22413833 := bstep (se 2 (by rfl) ⟨8405187, by rfl⟩ : syracuseStep 22413833 = 16810375) B16810375
theorem B2949671 : Blo 1553474 2949671 := bstep (se 1 (by rfl) ⟨2212253, by rfl⟩ : syracuseStep 2949671 = 4424507) B4424507
theorem B4203047 : Blo 1553474 4203047 := bstep (se 1 (by rfl) ⟨3152285, by rfl⟩ : syracuseStep 4203047 = 6304571) B6304571
theorem B3498695 : Blo 1553474 3498695 := bstep (se 1 (by rfl) ⟨2624021, by rfl⟩ : syracuseStep 3498695 = 5248043) B5248043
theorem B2917075 : Blo 1553474 2917075 := bstep (se 1 (by rfl) ⟨2187806, by rfl⟩ : syracuseStep 2917075 = 4375613) B4375613
theorem B2622199 : Blo 1553474 2622199 := bstep (se 1 (by rfl) ⟨1966649, by rfl⟩ : syracuseStep 2622199 = 3933299) B3933299
theorem B1966943 : Blo 1553474 1966943 := bstep (se 1 (by rfl) ⟨1475207, by rfl⟩ : syracuseStep 1966943 = 2950415) B2950415
theorem B5243831 : Blo 1553474 5243831 := bstep (se 1 (by rfl) ⟨3932873, by rfl⟩ : syracuseStep 5243831 = 7865747) B7865747
theorem B2622395 : Blo 1553474 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B17695745 : Blo 1553474 17695745 := bstep (se 2 (by rfl) ⟨6635904, by rfl⟩ : syracuseStep 17695745 = 13271809) B13271809
theorem B6300679 : Blo 1553474 6300679 := bstep (se 1 (by rfl) ⟨4725509, by rfl⟩ : syracuseStep 6300679 = 9451019) B9451019
theorem B3195911 : Blo 1553474 3195911 := bstep (se 1 (by rfl) ⟨2396933, by rfl⟩ : syracuseStep 3195911 = 4793867) B4793867
theorem B13272083 : Blo 1553474 13272083 := bstep (se 1 (by rfl) ⟨9954062, by rfl⟩ : syracuseStep 13272083 = 19908125) B19908125
theorem B2622503 : Blo 1553474 2622503 := bstep (se 1 (by rfl) ⟨1966877, by rfl⟩ : syracuseStep 2622503 = 3933755) B3933755
theorem B3318841 : Blo 1553474 3318841 := bstep (se 2 (by rfl) ⟨1244565, by rfl⟩ : syracuseStep 3318841 = 2489131) B2489131
theorem B7865423 : Blo 1553474 7865423 := bstep (se 1 (by rfl) ⟨5899067, by rfl⟩ : syracuseStep 7865423 = 11798135) B11798135
theorem B3933431 : Blo 1553474 3933431 := bstep (se 1 (by rfl) ⟨2950073, by rfl⟩ : syracuseStep 3933431 = 5900147) B5900147
theorem B11355383 : Blo 1553474 11355383 := bstep (se 1 (by rfl) ⟨8516537, by rfl⟩ : syracuseStep 11355383 = 17033075) B17033075
theorem B2622793 : Blo 1553474 2622793 := bstep (se 2 (by rfl) ⟨983547, by rfl⟩ : syracuseStep 2622793 = 1967095) B1967095
theorem B2622827 : Blo 1553474 2622827 := bstep (se 1 (by rfl) ⟨1967120, by rfl⟩ : syracuseStep 2622827 = 3934241) B3934241
theorem B5244425 : Blo 1553474 5244425 := bstep (se 2 (by rfl) ⟨1966659, by rfl⟩ : syracuseStep 5244425 = 3933319) B3933319
theorem B3499559 : Blo 1553474 3499559 := bstep (se 1 (by rfl) ⟨2624669, by rfl⟩ : syracuseStep 3499559 = 5249339) B5249339
theorem B7874171 : Blo 1553474 7874171 := bstep (se 1 (by rfl) ⟨5905628, by rfl⟩ : syracuseStep 7874171 = 11811257) B11811257
theorem B11806397 : Blo 1553474 11806397 := bstep (se 3 (by rfl) ⟨2213699, by rfl⟩ : syracuseStep 11806397 = 4427399) B4427399
theorem B7866071 : Blo 1553474 7866071 := bstep (se 1 (by rfl) ⟨5899553, by rfl⟩ : syracuseStep 7866071 = 11799107) B11799107
theorem B3737303 : Blo 1553474 3737303 := bstep (se 1 (by rfl) ⟨2802977, by rfl⟩ : syracuseStep 3737303 = 5605955) B5605955
theorem B2623225 : Blo 1553474 2623225 := bstep (se 2 (by rfl) ⟨983709, by rfl⟩ : syracuseStep 2623225 = 1967419) B1967419
theorem B8849195 : Blo 1553474 8849195 := bstep (se 1 (by rfl) ⟨6636896, by rfl⟩ : syracuseStep 8849195 = 13273793) B13273793
theorem B2950985 : Blo 1553474 2950985 := bstep (se 2 (by rfl) ⟨1106619, by rfl⟩ : syracuseStep 2950985 = 2213239) B2213239
theorem B2623495 : Blo 1553474 2623495 := bstep (se 1 (by rfl) ⟨1967621, by rfl⟩ : syracuseStep 2623495 = 3935243) B3935243
theorem B13273145 : Blo 1553474 13273145 := bstep (se 2 (by rfl) ⟨4977429, by rfl⟩ : syracuseStep 13273145 = 9954859) B9954859
theorem B17713241 : Blo 1553474 17713241 := bstep (se 2 (by rfl) ⟨6642465, by rfl⟩ : syracuseStep 17713241 = 13284931) B13284931
theorem B4728989 : Blo 1553474 4728989 := bstep (se 3 (by rfl) ⟨886685, by rfl⟩ : syracuseStep 4728989 = 1773371) B1773371
theorem B11806883 : Blo 1553474 11806883 := bstep (se 1 (by rfl) ⟨8855162, by rfl⟩ : syracuseStep 11806883 = 17710325) B17710325
theorem B2951417 : Blo 1553474 2951417 := bstep (se 2 (by rfl) ⟨1106781, by rfl⟩ : syracuseStep 2951417 = 2213563) B2213563
theorem B8407307 : Blo 1553474 8407307 := bstep (se 1 (by rfl) ⟨6305480, by rfl⟩ : syracuseStep 8407307 = 12610961) B12610961
theorem B2992457 : Blo 1553474 2992457 := bstep (se 2 (by rfl) ⟨1122171, by rfl⟩ : syracuseStep 2992457 = 2244343) B2244343
theorem B8857943 : Blo 1553474 8857943 := bstep (se 1 (by rfl) ⟨6643457, by rfl⟩ : syracuseStep 8857943 = 13286915) B13286915
theorem B5245289 : Blo 1553474 5245289 := bstep (se 2 (by rfl) ⟨1966983, by rfl⟩ : syracuseStep 5245289 = 3933967) B3933967
theorem B9963881 : Blo 1553474 9963881 := bstep (se 2 (by rfl) ⟨3736455, by rfl⟩ : syracuseStep 9963881 = 7472911) B7472911
theorem B2623927 : Blo 1553474 2623927 := bstep (se 1 (by rfl) ⟨1967945, by rfl⟩ : syracuseStep 2623927 = 3935891) B3935891
theorem B1845839 : Blo 1553474 1845839 := bstep (se 1 (by rfl) ⟨1384379, by rfl⟩ : syracuseStep 1845839 = 2768759) B2768759
theorem B2624123 : Blo 1553474 2624123 := bstep (se 1 (by rfl) ⟨1968092, by rfl⟩ : syracuseStep 2624123 = 3936185) B3936185
theorem B3934919 : Blo 1553474 3934919 := bstep (se 1 (by rfl) ⟨2951189, by rfl⟩ : syracuseStep 3934919 = 5902379) B5902379
theorem B6638365 : Blo 1553474 6638365 := bstep (se 3 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 6638365 = 2489387) B2489387
theorem B48515915 : Blo 1553474 48515915 := bstep (se 1 (by rfl) ⟨36386936, by rfl⟩ : syracuseStep 48515915 = 72773873) B72773873
theorem B5245883 : Blo 1553474 5245883 := bstep (se 1 (by rfl) ⟨3934412, by rfl⟩ : syracuseStep 5245883 = 7868825) B7868825
theorem B2624521 : Blo 1553474 2624521 := bstep (se 2 (by rfl) ⟨984195, by rfl⟩ : syracuseStep 2624521 = 1968391) B1968391
theorem B1748047 : Blo 1553474 1748047 := bstep (se 1 (by rfl) ⟨1311035, by rfl⟩ : syracuseStep 1748047 = 2622071) B2622071
theorem B2624683 : Blo 1553474 2624683 := bstep (se 1 (by rfl) ⟨1968512, by rfl⟩ : syracuseStep 2624683 = 3937025) B3937025
theorem B1821895 : Blo 1553474 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B22727927 : Blo 1553474 22727927 := bstep (se 1 (by rfl) ⟨17045945, by rfl⟩ : syracuseStep 22727927 = 34091891) B34091891
theorem B40930595 : Blo 1553474 40930595 := bstep (se 1 (by rfl) ⟨30697946, by rfl⟩ : syracuseStep 40930595 = 61395893) B61395893
theorem B33623333 : Blo 1553474 33623333 := bstep (se 4 (by rfl) ⟨3152187, by rfl⟩ : syracuseStep 33623333 = 6304375) B6304375
theorem B1748443 : Blo 1553474 1748443 := bstep (se 1 (by rfl) ⟨1311332, by rfl⟩ : syracuseStep 1748443 = 2622665) B2622665
theorem B5320331 : Blo 1553474 5320331 := bstep (se 1 (by rfl) ⟨3990248, by rfl⟩ : syracuseStep 5320331 = 7980497) B7980497
theorem B2657963 : Blo 1553474 2657963 := bstep (se 1 (by rfl) ⟨1993472, by rfl⟩ : syracuseStep 2657963 = 3986945) B3986945
theorem B2952875 : Blo 1553474 2952875 := bstep (se 1 (by rfl) ⟨2214656, by rfl⟩ : syracuseStep 2952875 = 4429313) B4429313
theorem B12611321 : Blo 1553474 12611321 := bstep (se 2 (by rfl) ⟨4729245, by rfl⟩ : syracuseStep 12611321 = 9458491) B9458491
theorem B3936073 : Blo 1553474 3936073 := bstep (se 2 (by rfl) ⟨1476027, by rfl⟩ : syracuseStep 3936073 = 2952055) B2952055
theorem B39825269 : Blo 1553474 39825269 := bstep (se 5 (by rfl) ⟨1866809, by rfl⟩ : syracuseStep 39825269 = 3733619) B3733619
theorem B12603271 : Blo 1553474 12603271 := bstep (se 1 (by rfl) ⟨9452453, by rfl⟩ : syracuseStep 12603271 = 18904907) B18904907
theorem B2330543 : Blo 1553474 2330543 := bstep (se 1 (by rfl) ⟨1747907, by rfl⟩ : syracuseStep 2330543 = 3495815) B3495815
theorem B1748911 : Blo 1553474 1748911 := bstep (se 1 (by rfl) ⟨1311683, by rfl⟩ : syracuseStep 1748911 = 2623367) B2623367
theorem B4485127 : Blo 1553474 4485127 := bstep (se 1 (by rfl) ⟨3363845, by rfl⟩ : syracuseStep 4485127 = 6727691) B6727691
theorem B2330633 : Blo 1553474 2330633 := bstep (se 2 (by rfl) ⟨873987, by rfl⟩ : syracuseStep 2330633 = 1747975) B1747975
theorem B4608019 : Blo 1553474 4608019 := bstep (se 1 (by rfl) ⟨3456014, by rfl⟩ : syracuseStep 4608019 = 6912029) B6912029
theorem B2330663 : Blo 1553474 2330663 := bstep (se 1 (by rfl) ⟨1747997, by rfl⟩ : syracuseStep 2330663 = 3495995) B3495995
theorem B4427855 : Blo 1553474 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B2330747 : Blo 1553474 2330747 := bstep (se 1 (by rfl) ⟨1748060, by rfl⟩ : syracuseStep 2330747 = 3496121) B3496121
theorem B1659079 : Blo 1553474 1659079 := bstep (se 1 (by rfl) ⟨1244309, by rfl⟩ : syracuseStep 1659079 = 2488619) B2488619
theorem B2330873 : Blo 1553474 2330873 := bstep (se 2 (by rfl) ⟨874077, by rfl⟩ : syracuseStep 2330873 = 1748155) B1748155
theorem B2330975 : Blo 1553474 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B1749343 : Blo 1553474 1749343 := bstep (se 1 (by rfl) ⟨1312007, by rfl⟩ : syracuseStep 1749343 = 2624015) B2624015
theorem B2330987 : Blo 1553474 2330987 := bstep (se 1 (by rfl) ⟨1748240, by rfl⟩ : syracuseStep 2330987 = 3496481) B3496481
theorem B11809313 : Blo 1553474 11809313 := bstep (se 2 (by rfl) ⟨4428492, by rfl⟩ : syracuseStep 11809313 = 8856985) B8856985
theorem B7868987 : Blo 1553474 7868987 := bstep (se 1 (by rfl) ⟨5901740, by rfl⟩ : syracuseStep 7868987 = 11803481) B11803481
theorem B2331215 : Blo 1553474 2331215 := bstep (se 1 (by rfl) ⟨1748411, by rfl⟩ : syracuseStep 2331215 = 3496823) B3496823
theorem B44847715 : Blo 1553474 44847715 := bstep (se 1 (by rfl) ⟨33635786, by rfl⟩ : syracuseStep 44847715 = 67271573) B67271573
theorem B5247611 : Blo 1553474 5247611 := bstep (se 1 (by rfl) ⟨3935708, by rfl⟩ : syracuseStep 5247611 = 7871417) B7871417
theorem B2331335 : Blo 1553474 2331335 := bstep (se 1 (by rfl) ⟨1748501, by rfl⟩ : syracuseStep 2331335 = 3497003) B3497003
theorem B1749703 : Blo 1553474 1749703 := bstep (se 1 (by rfl) ⟨1312277, by rfl⟩ : syracuseStep 1749703 = 2624555) B2624555
theorem B5903063 : Blo 1553474 5903063 := bstep (se 1 (by rfl) ⟨4427297, by rfl⟩ : syracuseStep 5903063 = 8854595) B8854595
theorem B5247773 : Blo 1553474 5247773 := bstep (se 3 (by rfl) ⟨983957, by rfl⟩ : syracuseStep 5247773 = 1967915) B1967915
theorem B2331497 : Blo 1553474 2331497 := bstep (se 2 (by rfl) ⟨874311, by rfl⟩ : syracuseStep 2331497 = 1748623) B1748623
theorem B21263255 : Blo 1553474 21263255 := bstep (se 1 (by rfl) ⟨15947441, by rfl⟩ : syracuseStep 21263255 = 31894883) B31894883
theorem B2331575 : Blo 1553474 2331575 := bstep (se 1 (by rfl) ⟨1748681, by rfl⟩ : syracuseStep 2331575 = 3497363) B3497363
theorem B3937207 : Blo 1553474 3937207 := bstep (se 1 (by rfl) ⟨2952905, by rfl⟩ : syracuseStep 3937207 = 5905811) B5905811
theorem B2331611 : Blo 1553474 2331611 := bstep (se 1 (by rfl) ⟨1748708, by rfl⟩ : syracuseStep 2331611 = 3497417) B3497417
theorem B9458707 : Blo 1553474 9458707 := bstep (se 1 (by rfl) ⟨7094030, by rfl⟩ : syracuseStep 9458707 = 14188061) B14188061
theorem B15954995 : Blo 1553474 15954995 := bstep (se 1 (by rfl) ⟨11966246, by rfl⟩ : syracuseStep 15954995 = 23932493) B23932493
theorem B4428857 : Blo 1553474 4428857 := bstep (se 2 (by rfl) ⟨1660821, by rfl⟩ : syracuseStep 4428857 = 3321643) B3321643
theorem B1553487 : Blo 1553474 1553487 := bstep (se 1 (by rfl) ⟨1165115, by rfl⟩ : syracuseStep 1553487 = 2330231) B2330231
theorem B1553503 : Blo 1553474 1553503 := bstep (se 1 (by rfl) ⟨1165127, by rfl⟩ : syracuseStep 1553503 = 2330255) B2330255
theorem B1553531 : Blo 1553474 1553531 := bstep (se 1 (by rfl) ⟨1165148, by rfl⟩ : syracuseStep 1553531 = 2330297) B2330297
theorem B6640811 : Blo 1553474 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B1553583 : Blo 1553474 1553583 := bstep (se 1 (by rfl) ⟨1165187, by rfl⟩ : syracuseStep 1553583 = 2330375) B2330375
theorem B7869635 : Blo 1553474 7869635 := bstep (se 1 (by rfl) ⟨5902226, by rfl⟩ : syracuseStep 7869635 = 11804453) B11804453
theorem B1553607 : Blo 1553474 1553607 := bstep (se 1 (by rfl) ⟨1165205, by rfl⟩ : syracuseStep 1553607 = 2330411) B2330411
theorem B1553627 : Blo 1553474 1553627 := bstep (se 1 (by rfl) ⟨1165220, by rfl⟩ : syracuseStep 1553627 = 2330441) B2330441
theorem B1553703 : Blo 1553474 1553703 := bstep (se 1 (by rfl) ⟨1165277, by rfl⟩ : syracuseStep 1553703 = 2330555) B2330555
theorem B1553743 : Blo 1553474 1553743 := bstep (se 1 (by rfl) ⟨1165307, by rfl⟩ : syracuseStep 1553743 = 2330615) B2330615
theorem B4978007 : Blo 1553474 4978007 := bstep (se 1 (by rfl) ⟨3733505, by rfl⟩ : syracuseStep 4978007 = 7467011) B7467011
theorem B1553759 : Blo 1553474 1553759 := bstep (se 1 (by rfl) ⟨1165319, by rfl⟩ : syracuseStep 1553759 = 2330639) B2330639
theorem B1553787 : Blo 1553474 1553787 := bstep (se 1 (by rfl) ⟨1165340, by rfl⟩ : syracuseStep 1553787 = 2330681) B2330681
theorem B1553839 : Blo 1553474 1553839 := bstep (se 1 (by rfl) ⟨1165379, by rfl⟩ : syracuseStep 1553839 = 2330759) B2330759
theorem B2332079 : Blo 1553474 2332079 := bstep (se 1 (by rfl) ⟨1749059, by rfl⟩ : syracuseStep 2332079 = 3498119) B3498119
theorem B1553863 : Blo 1553474 1553863 := bstep (se 1 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 1553863 = 2330795) B2330795
theorem B1553883 : Blo 1553474 1553883 := bstep (se 1 (by rfl) ⟨1165412, by rfl⟩ : syracuseStep 1553883 = 2330825) B2330825
theorem B5248475 : Blo 1553474 5248475 := bstep (se 1 (by rfl) ⟨3936356, by rfl⟩ : syracuseStep 5248475 = 7872713) B7872713
theorem B2332169 : Blo 1553474 2332169 := bstep (se 2 (by rfl) ⟨874563, by rfl⟩ : syracuseStep 2332169 = 1749127) B1749127
theorem B3151379 : Blo 1553474 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B1553959 : Blo 1553474 1553959 := bstep (se 1 (by rfl) ⟨1165469, by rfl⟩ : syracuseStep 1553959 = 2330939) B2330939
theorem B2332199 : Blo 1553474 2332199 := bstep (se 1 (by rfl) ⟨1749149, by rfl⟩ : syracuseStep 2332199 = 3498299) B3498299
theorem B31954493 : Blo 1553474 31954493 := bstep (se 3 (by rfl) ⟨5991467, by rfl⟩ : syracuseStep 31954493 = 11982935) B11982935
theorem B1553999 : Blo 1553474 1553999 := bstep (se 1 (by rfl) ⟨1165499, by rfl⟩ : syracuseStep 1553999 = 2330999) B2330999
theorem B1554015 : Blo 1553474 1554015 := bstep (se 1 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 1554015 = 2331023) B2331023
theorem B1554043 : Blo 1553474 1554043 := bstep (se 1 (by rfl) ⟨1165532, by rfl⟩ : syracuseStep 1554043 = 2331065) B2331065
theorem B2332283 : Blo 1553474 2332283 := bstep (se 1 (by rfl) ⟨1749212, by rfl⟩ : syracuseStep 2332283 = 3498425) B3498425
theorem B8853137 : Blo 1553474 8853137 := bstep (se 2 (by rfl) ⟨3319926, by rfl⟩ : syracuseStep 8853137 = 6639853) B6639853
theorem B56694421 : Blo 1553474 56694421 := bstep (se 6 (by rfl) ⟨1328775, by rfl⟩ : syracuseStep 56694421 = 2657551) B2657551
theorem B1554095 : Blo 1553474 1554095 := bstep (se 1 (by rfl) ⟨1165571, by rfl⟩ : syracuseStep 1554095 = 2331143) B2331143
theorem B1554119 : Blo 1553474 1554119 := bstep (se 1 (by rfl) ⟨1165589, by rfl⟩ : syracuseStep 1554119 = 2331179) B2331179
theorem B3495635 : Blo 1553474 3495635 := bstep (se 1 (by rfl) ⟨2621726, by rfl⟩ : syracuseStep 3495635 = 5243453) B5243453
theorem B1554139 : Blo 1553474 1554139 := bstep (se 1 (by rfl) ⟨1165604, by rfl⟩ : syracuseStep 1554139 = 2331209) B2331209
theorem B2332409 : Blo 1553474 2332409 := bstep (se 2 (by rfl) ⟨874653, by rfl⟩ : syracuseStep 2332409 = 1749307) B1749307
theorem B1554215 : Blo 1553474 1554215 := bstep (se 1 (by rfl) ⟨1165661, by rfl⟩ : syracuseStep 1554215 = 2331323) B2331323
theorem B6305609 : Blo 1553474 6305609 := bstep (se 2 (by rfl) ⟨2364603, by rfl⟩ : syracuseStep 6305609 = 4729207) B4729207
theorem B1554255 : Blo 1553474 1554255 := bstep (se 1 (by rfl) ⟨1165691, by rfl⟩ : syracuseStep 1554255 = 2331383) B2331383
theorem B1554271 : Blo 1553474 1554271 := bstep (se 1 (by rfl) ⟨1165703, by rfl⟩ : syracuseStep 1554271 = 2331407) B2331407
theorem B2332511 : Blo 1553474 2332511 := bstep (se 1 (by rfl) ⟨1749383, by rfl⟩ : syracuseStep 2332511 = 3498767) B3498767
theorem B2332523 : Blo 1553474 2332523 := bstep (se 1 (by rfl) ⟨1749392, by rfl⟩ : syracuseStep 2332523 = 3498785) B3498785
theorem B1554299 : Blo 1553474 1554299 := bstep (se 1 (by rfl) ⟨1165724, by rfl⟩ : syracuseStep 1554299 = 2331449) B2331449
theorem B1554351 : Blo 1553474 1554351 := bstep (se 1 (by rfl) ⟨1165763, by rfl⟩ : syracuseStep 1554351 = 2331527) B2331527
theorem B3151799 : Blo 1553474 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B1554375 : Blo 1553474 1554375 := bstep (se 1 (by rfl) ⟨1165781, by rfl⟩ : syracuseStep 1554375 = 2331563) B2331563
theorem B19929037 : Blo 1553474 19929037 := bstep (se 3 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 19929037 = 7473389) B7473389
theorem B17938385 : Blo 1553474 17938385 := bstep (se 2 (by rfl) ⟨6726894, by rfl⟩ : syracuseStep 17938385 = 13453789) B13453789
theorem B1554395 : Blo 1553474 1554395 := bstep (se 1 (by rfl) ⟨1165796, by rfl⟩ : syracuseStep 1554395 = 2331593) B2331593
theorem B1554471 : Blo 1553474 1554471 := bstep (se 1 (by rfl) ⟨1165853, by rfl⟩ : syracuseStep 1554471 = 2331707) B2331707
theorem B1554511 : Blo 1553474 1554511 := bstep (se 1 (by rfl) ⟨1165883, by rfl⟩ : syracuseStep 1554511 = 2331767) B2331767
theorem B2332751 : Blo 1553474 2332751 := bstep (se 1 (by rfl) ⟨1749563, by rfl⟩ : syracuseStep 2332751 = 3499127) B3499127
theorem B1554527 : Blo 1553474 1554527 := bstep (se 1 (by rfl) ⟨1165895, by rfl⟩ : syracuseStep 1554527 = 2331791) B2331791
theorem B1554555 : Blo 1553474 1554555 := bstep (se 1 (by rfl) ⟨1165916, by rfl⟩ : syracuseStep 1554555 = 2331833) B2331833
theorem B5249177 : Blo 1553474 5249177 := bstep (se 2 (by rfl) ⟨1968441, by rfl⟩ : syracuseStep 5249177 = 3936883) B3936883
theorem B4200605 : Blo 1553474 4200605 := bstep (se 3 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 4200605 = 1575227) B1575227
theorem B1554607 : Blo 1553474 1554607 := bstep (se 1 (by rfl) ⟨1165955, by rfl⟩ : syracuseStep 1554607 = 2331911) B2331911
theorem B1554631 : Blo 1553474 1554631 := bstep (se 1 (by rfl) ⟨1165973, by rfl⟩ : syracuseStep 1554631 = 2331947) B2331947
theorem B2332871 : Blo 1553474 2332871 := bstep (se 1 (by rfl) ⟨1749653, by rfl⟩ : syracuseStep 2332871 = 3499307) B3499307
theorem B1554651 : Blo 1553474 1554651 := bstep (se 1 (by rfl) ⟨1165988, by rfl⟩ : syracuseStep 1554651 = 2331977) B2331977
theorem B2488567 : Blo 1553474 2488567 := bstep (se 1 (by rfl) ⟨1866425, by rfl⟩ : syracuseStep 2488567 = 3732851) B3732851
theorem B1554727 : Blo 1553474 1554727 := bstep (se 1 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 1554727 = 2332091) B2332091
theorem B12597565 : Blo 1553474 12597565 := bstep (se 3 (by rfl) ⟨2362043, by rfl⟩ : syracuseStep 12597565 = 4724087) B4724087
theorem B1554767 : Blo 1553474 1554767 := bstep (se 1 (by rfl) ⟨1166075, by rfl⟩ : syracuseStep 1554767 = 2332151) B2332151
theorem B1554783 : Blo 1553474 1554783 := bstep (se 1 (by rfl) ⟨1166087, by rfl⟩ : syracuseStep 1554783 = 2332175) B2332175
theorem B2333033 : Blo 1553474 2333033 := bstep (se 2 (by rfl) ⟨874887, by rfl⟩ : syracuseStep 2333033 = 1749775) B1749775
theorem B1554811 : Blo 1553474 1554811 := bstep (se 1 (by rfl) ⟨1166108, by rfl⟩ : syracuseStep 1554811 = 2332217) B2332217
theorem B1554863 : Blo 1553474 1554863 := bstep (se 1 (by rfl) ⟨1166147, by rfl⟩ : syracuseStep 1554863 = 2332295) B2332295
theorem B2333111 : Blo 1553474 2333111 := bstep (se 1 (by rfl) ⟨1749833, by rfl⟩ : syracuseStep 2333111 = 3499667) B3499667
theorem B1554887 : Blo 1553474 1554887 := bstep (se 1 (by rfl) ⟨1166165, by rfl⟩ : syracuseStep 1554887 = 2332331) B2332331
theorem B1554907 : Blo 1553474 1554907 := bstep (se 1 (by rfl) ⟨1166180, by rfl⟩ : syracuseStep 1554907 = 2332361) B2332361
theorem B2333147 : Blo 1553474 2333147 := bstep (se 1 (by rfl) ⟨1749860, by rfl⟩ : syracuseStep 2333147 = 3499721) B3499721
theorem B1554983 : Blo 1553474 1554983 := bstep (se 1 (by rfl) ⟨1166237, by rfl⟩ : syracuseStep 1554983 = 2332475) B2332475
theorem B1555023 : Blo 1553474 1555023 := bstep (se 1 (by rfl) ⟨1166267, by rfl⟩ : syracuseStep 1555023 = 2332535) B2332535
theorem B1555039 : Blo 1553474 1555039 := bstep (se 1 (by rfl) ⟨1166279, by rfl⟩ : syracuseStep 1555039 = 2332559) B2332559
theorem B3496571 : Blo 1553474 3496571 := bstep (se 1 (by rfl) ⟨2622428, by rfl⟩ : syracuseStep 3496571 = 5244857) B5244857
theorem B1555067 : Blo 1553474 1555067 := bstep (se 1 (by rfl) ⟨1166300, by rfl⟩ : syracuseStep 1555067 = 2332601) B2332601
theorem B4979339 : Blo 1553474 4979339 := bstep (se 1 (by rfl) ⟨3734504, by rfl⟩ : syracuseStep 4979339 = 7469009) B7469009
theorem B1555119 : Blo 1553474 1555119 := bstep (se 1 (by rfl) ⟨1166339, by rfl⟩ : syracuseStep 1555119 = 2332679) B2332679
theorem B4979389 : Blo 1553474 4979389 := bstep (se 3 (by rfl) ⟨933635, by rfl⟩ : syracuseStep 4979389 = 1867271) B1867271
theorem B1555143 : Blo 1553474 1555143 := bstep (se 1 (by rfl) ⟨1166357, by rfl⟩ : syracuseStep 1555143 = 2332715) B2332715
theorem B17701577 : Blo 1553474 17701577 := bstep (se 2 (by rfl) ⟨6638091, by rfl⟩ : syracuseStep 17701577 = 13276183) B13276183
theorem B1555163 : Blo 1553474 1555163 := bstep (se 1 (by rfl) ⟨1166372, by rfl⟩ : syracuseStep 1555163 = 2332745) B2332745
theorem B3496697 : Blo 1553474 3496697 := bstep (se 2 (by rfl) ⟨1311261, by rfl⟩ : syracuseStep 3496697 = 2622523) B2622523
theorem B1555239 : Blo 1553474 1555239 := bstep (se 1 (by rfl) ⟨1166429, by rfl⟩ : syracuseStep 1555239 = 2332859) B2332859
theorem B1555279 : Blo 1553474 1555279 := bstep (se 1 (by rfl) ⟨1166459, by rfl⟩ : syracuseStep 1555279 = 2332919) B2332919
theorem B1555295 : Blo 1553474 1555295 := bstep (se 1 (by rfl) ⟨1166471, by rfl⟩ : syracuseStep 1555295 = 2332943) B2332943
theorem B1555323 : Blo 1553474 1555323 := bstep (se 1 (by rfl) ⟨1166492, by rfl⟩ : syracuseStep 1555323 = 2332985) B2332985
theorem B1555375 : Blo 1553474 1555375 := bstep (se 1 (by rfl) ⟨1166531, by rfl⟩ : syracuseStep 1555375 = 2333063) B2333063
theorem B22404023 : Blo 1553474 22404023 := bstep (se 1 (by rfl) ⟨16803017, by rfl⟩ : syracuseStep 22404023 = 33606035) B33606035
theorem B1555399 : Blo 1553474 1555399 := bstep (se 1 (by rfl) ⟨1166549, by rfl⟩ : syracuseStep 1555399 = 2333099) B2333099
theorem B1555419 : Blo 1553474 1555419 := bstep (se 1 (by rfl) ⟨1166564, by rfl⟩ : syracuseStep 1555419 = 2333129) B2333129
theorem B3496967 : Blo 1553474 3496967 := bstep (se 1 (by rfl) ⟨2622725, by rfl⟩ : syracuseStep 3496967 = 5245451) B5245451
theorem B8404019 : Blo 1553474 8404019 := bstep (se 1 (by rfl) ⟨6303014, by rfl⟩ : syracuseStep 8404019 = 12606029) B12606029
theorem B3497039 : Blo 1553474 3497039 := bstep (se 1 (by rfl) ⟨2622779, by rfl⟩ : syracuseStep 3497039 = 5245559) B5245559
theorem B3734927 : Blo 1553474 3734927 := bstep (se 1 (by rfl) ⟨2801195, by rfl⟩ : syracuseStep 3734927 = 5602391) B5602391
theorem B3497435 : Blo 1553474 3497435 := bstep (se 1 (by rfl) ⟨2623076, by rfl⟩ : syracuseStep 3497435 = 5246153) B5246153
theorem B3988955 : Blo 1553474 3988955 := bstep (se 1 (by rfl) ⟨2991716, by rfl⟩ : syracuseStep 3988955 = 5983433) B5983433
theorem B8855027 : Blo 1553474 8855027 := bstep (se 1 (by rfl) ⟨6641270, by rfl⟩ : syracuseStep 8855027 = 13282541) B13282541
theorem B89636381 : Blo 1553474 89636381 := bstep (se 3 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 89636381 = 33613643) B33613643
theorem B1867387 : Blo 1553474 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B2801513 : Blo 1553474 2801513 := bstep (se 2 (by rfl) ⟨1050567, by rfl⟩ : syracuseStep 2801513 = 2101135) B2101135
theorem B1867627 : Blo 1553474 1867627 := bstep (se 1 (by rfl) ⟨1400720, by rfl⟩ : syracuseStep 1867627 = 2801441) B2801441
theorem B3497903 : Blo 1553474 3497903 := bstep (se 1 (by rfl) ⟨2623427, by rfl⟩ : syracuseStep 3497903 = 5246855) B5246855
theorem B5980169 : Blo 1553474 5980169 := bstep (se 2 (by rfl) ⟨2242563, by rfl⟩ : syracuseStep 5980169 = 4485127) B4485127
theorem B3497993 : Blo 1553474 3497993 := bstep (se 2 (by rfl) ⟨1311747, by rfl⟩ : syracuseStep 3497993 = 2623495) B2623495
theorem B6144025 : Blo 1553474 6144025 := bstep (se 2 (by rfl) ⟨2304009, by rfl⟩ : syracuseStep 6144025 = 4608019) B4608019
theorem B4423891 : Blo 1553474 4423891 := bstep (se 1 (by rfl) ⟨3317918, by rfl⟩ : syracuseStep 4423891 = 6635837) B6635837
theorem B2212105 : Blo 1553474 2212105 := bstep (se 2 (by rfl) ⟨829539, by rfl⟩ : syracuseStep 2212105 = 1659079) B1659079
theorem B3932489 : Blo 1553474 3932489 := bstep (se 2 (by rfl) ⟨1474683, by rfl⟩ : syracuseStep 3932489 = 2949367) B2949367
theorem B3318089 : Blo 1553474 3318089 := bstep (se 2 (by rfl) ⟨1244283, by rfl⟩ : syracuseStep 3318089 = 2488567) B2488567
theorem B14942555 : Blo 1553474 14942555 := bstep (se 1 (by rfl) ⟨11206916, by rfl⟩ : syracuseStep 14942555 = 22413833) B22413833
theorem B7872875 : Blo 1553474 7872875 := bstep (se 1 (by rfl) ⟨5904656, by rfl⟩ : syracuseStep 7872875 = 11809313) B11809313
theorem B1966447 : Blo 1553474 1966447 := bstep (se 1 (by rfl) ⟨1474835, by rfl⟩ : syracuseStep 1966447 = 2949671) B2949671
theorem B3498407 : Blo 1553474 3498407 := bstep (se 1 (by rfl) ⟨2623805, by rfl⟩ : syracuseStep 3498407 = 5247611) B5247611
theorem B3498515 : Blo 1553474 3498515 := bstep (se 1 (by rfl) ⟨2623886, by rfl⟩ : syracuseStep 3498515 = 5247773) B5247773
theorem B3498569 : Blo 1553474 3498569 := bstep (se 2 (by rfl) ⟨1311963, by rfl⟩ : syracuseStep 3498569 = 2623927) B2623927
theorem B11797163 : Blo 1553474 11797163 := bstep (se 1 (by rfl) ⟨8847872, by rfl⟩ : syracuseStep 11797163 = 17695745) B17695745
theorem B2130607 : Blo 1553474 2130607 := bstep (se 1 (by rfl) ⟨1597955, by rfl⟩ : syracuseStep 2130607 = 3195911) B3195911
theorem B8848055 : Blo 1553474 8848055 := bstep (se 1 (by rfl) ⟨6636041, by rfl⟩ : syracuseStep 8848055 = 13272083) B13272083
theorem B5243615 : Blo 1553474 5243615 := bstep (se 1 (by rfl) ⟨3932711, by rfl⟩ : syracuseStep 5243615 = 7865423) B7865423
theorem B2622287 : Blo 1553474 2622287 := bstep (se 1 (by rfl) ⟨1966715, by rfl⟩ : syracuseStep 2622287 = 3933431) B3933431
theorem B7570255 : Blo 1553474 7570255 := bstep (se 1 (by rfl) ⟨5677691, by rfl⟩ : syracuseStep 7570255 = 11355383) B11355383
theorem B3318671 : Blo 1553474 3318671 := bstep (se 1 (by rfl) ⟨2489003, by rfl⟩ : syracuseStep 3318671 = 4978007) B4978007
theorem B3498983 : Blo 1553474 3498983 := bstep (se 1 (by rfl) ⟨2624237, by rfl⟩ : syracuseStep 3498983 = 5248475) B5248475
theorem B9716773 : Blo 1553474 9716773 := bstep (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) B1821895
theorem B5244047 : Blo 1553474 5244047 := bstep (se 1 (by rfl) ⟨3933035, by rfl⟩ : syracuseStep 5244047 = 7866071) B7866071
theorem B2491535 : Blo 1553474 2491535 := bstep (se 1 (by rfl) ⟨1868651, by rfl⟩ : syracuseStep 2491535 = 3737303) B3737303
theorem B5899463 : Blo 1553474 5899463 := bstep (se 1 (by rfl) ⟨4424597, by rfl⟩ : syracuseStep 5899463 = 8849195) B8849195
theorem B1967323 : Blo 1553474 1967323 := bstep (se 1 (by rfl) ⟨1475492, by rfl⟩ : syracuseStep 1967323 = 2950985) B2950985
theorem B4203739 : Blo 1553474 4203739 := bstep (se 1 (by rfl) ⟨3152804, by rfl⟩ : syracuseStep 4203739 = 6305609) B6305609
theorem B3499361 : Blo 1553474 3499361 := bstep (se 2 (by rfl) ⟨1312260, by rfl⟩ : syracuseStep 3499361 = 2624521) B2624521
theorem B8848763 : Blo 1553474 8848763 := bstep (se 1 (by rfl) ⟨6636572, by rfl⟩ : syracuseStep 8848763 = 13273145) B13273145
theorem B4425121 : Blo 1553474 4425121 := bstep (se 2 (by rfl) ⟨1659420, by rfl⟩ : syracuseStep 4425121 = 3318841) B3318841
theorem B3499451 : Blo 1553474 3499451 := bstep (se 1 (by rfl) ⟨2624588, by rfl⟩ : syracuseStep 3499451 = 5249177) B5249177
theorem B11208125 : Blo 1553474 11208125 := bstep (se 3 (by rfl) ⟨2101523, by rfl⟩ : syracuseStep 11208125 = 4203047) B4203047
theorem B5604871 : Blo 1553474 5604871 := bstep (se 1 (by rfl) ⟨4203653, by rfl⟩ : syracuseStep 5604871 = 8407307) B8407307
theorem B3499577 : Blo 1553474 3499577 := bstep (se 2 (by rfl) ⟨1312341, by rfl⟩ : syracuseStep 3499577 = 2624683) B2624683
theorem B3319559 : Blo 1553474 3319559 := bstep (se 1 (by rfl) ⟨2489669, by rfl⟩ : syracuseStep 3319559 = 4979339) B4979339
theorem B7874333 : Blo 1553474 7874333 := bstep (se 3 (by rfl) ⟨1476437, by rfl⟩ : syracuseStep 7874333 = 2952875) B2952875
theorem B2623279 : Blo 1553474 2623279 := bstep (se 1 (by rfl) ⟨1967459, by rfl⟩ : syracuseStep 2623279 = 3934919) B3934919
theorem B32343943 : Blo 1553474 32343943 := bstep (se 1 (by rfl) ⟨24257957, by rfl⟩ : syracuseStep 32343943 = 48515915) B48515915
theorem B14936015 : Blo 1553474 14936015 := bstep (se 1 (by rfl) ⟨11202011, by rfl⟩ : syracuseStep 14936015 = 22404023) B22404023
theorem B22415555 : Blo 1553474 22415555 := bstep (se 1 (by rfl) ⟨16811666, by rfl⟩ : syracuseStep 22415555 = 33623333) B33623333
theorem B5245181 : Blo 1553474 5245181 := bstep (se 3 (by rfl) ⟨983471, by rfl⟩ : syracuseStep 5245181 = 1966943) B1966943
theorem B1771975 : Blo 1553474 1771975 := bstep (se 1 (by rfl) ⟨1328981, by rfl⟩ : syracuseStep 1771975 = 2657963) B2657963
theorem B8407547 : Blo 1553474 8407547 := bstep (se 1 (by rfl) ⟨6305660, by rfl⟩ : syracuseStep 8407547 = 12611321) B12611321
theorem B16804361 : Blo 1553474 16804361 := bstep (se 2 (by rfl) ⟨6301635, by rfl⟩ : syracuseStep 16804361 = 12603271) B12603271
theorem B2951903 : Blo 1553474 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B1747759 : Blo 1553474 1747759 := bstep (se 1 (by rfl) ⟨1310819, by rfl⟩ : syracuseStep 1747759 = 2621639) B2621639
theorem B1747867 : Blo 1553474 1747867 := bstep (se 1 (by rfl) ⟨1310900, by rfl⟩ : syracuseStep 1747867 = 2621801) B2621801
theorem B3320747 : Blo 1553474 3320747 := bstep (se 1 (by rfl) ⟨2490560, by rfl⟩ : syracuseStep 3320747 = 4981121) B4981121
theorem B5245991 : Blo 1553474 5245991 := bstep (se 1 (by rfl) ⟨3934493, by rfl⟩ : syracuseStep 5245991 = 7868987) B7868987
theorem B12610637 : Blo 1553474 12610637 := bstep (se 3 (by rfl) ⟨2364494, by rfl⟩ : syracuseStep 12610637 = 4728989) B4728989
theorem B16796753 : Blo 1553474 16796753 := bstep (se 2 (by rfl) ⟨6298782, by rfl⟩ : syracuseStep 16796753 = 12597565) B12597565
theorem B3935375 : Blo 1553474 3935375 := bstep (se 1 (by rfl) ⟨2951531, by rfl⟩ : syracuseStep 3935375 = 5903063) B5903063
theorem B14175503 : Blo 1553474 14175503 := bstep (se 1 (by rfl) ⟨10631627, by rfl⟩ : syracuseStep 14175503 = 21263255) B21263255
theorem B1748263 : Blo 1553474 1748263 := bstep (se 1 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 1748263 = 2622395) B2622395
theorem B1748335 : Blo 1553474 1748335 := bstep (se 1 (by rfl) ⟨1311251, by rfl⟩ : syracuseStep 1748335 = 2622503) B2622503
theorem B10636663 : Blo 1553474 10636663 := bstep (se 1 (by rfl) ⟨7977497, by rfl⟩ : syracuseStep 10636663 = 15954995) B15954995
theorem B4427207 : Blo 1553474 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B5246423 : Blo 1553474 5246423 := bstep (se 1 (by rfl) ⟨3934817, by rfl⟩ : syracuseStep 5246423 = 7869635) B7869635
theorem B59796953 : Blo 1553474 59796953 := bstep (se 2 (by rfl) ⟨22423857, by rfl⟩ : syracuseStep 59796953 = 44847715) B44847715
theorem B1748551 : Blo 1553474 1748551 := bstep (se 1 (by rfl) ⟨1311413, by rfl⟩ : syracuseStep 1748551 = 2622827) B2622827
theorem B6639185 : Blo 1553474 6639185 := bstep (se 2 (by rfl) ⟨2489694, by rfl⟩ : syracuseStep 6639185 = 4979389) B4979389
theorem B2100919 : Blo 1553474 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B8851153 : Blo 1553474 8851153 := bstep (se 2 (by rfl) ⟨3319182, by rfl⟩ : syracuseStep 8851153 = 6638365) B6638365
theorem B21302995 : Blo 1553474 21302995 := bstep (se 1 (by rfl) ⟨15977246, by rfl⟩ : syracuseStep 21302995 = 31954493) B31954493
theorem B5902091 : Blo 1553474 5902091 := bstep (se 1 (by rfl) ⟨4426568, by rfl⟩ : syracuseStep 5902091 = 8853137) B8853137
theorem B2330423 : Blo 1553474 2330423 := bstep (se 1 (by rfl) ⟨1747817, by rfl⟩ : syracuseStep 2330423 = 3495635) B3495635
theorem B2101199 : Blo 1553474 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B8400905 : Blo 1553474 8400905 := bstep (se 2 (by rfl) ⟨3150339, by rfl⟩ : syracuseStep 8400905 = 6300679) B6300679
theorem B12611609 : Blo 1553474 12611609 := bstep (se 2 (by rfl) ⟨4729353, by rfl⟩ : syracuseStep 12611609 = 9458707) B9458707
theorem B11808827 : Blo 1553474 11808827 := bstep (se 1 (by rfl) ⟨8856620, by rfl⟩ : syracuseStep 11808827 = 17713241) B17713241
theorem B2330729 : Blo 1553474 2330729 := bstep (se 2 (by rfl) ⟨874023, by rfl⟩ : syracuseStep 2330729 = 1748047) B1748047
theorem B1994971 : Blo 1553474 1994971 := bstep (se 1 (by rfl) ⟨1496228, by rfl⟩ : syracuseStep 1994971 = 2992457) B2992457
theorem B2331047 : Blo 1553474 2331047 := bstep (se 1 (by rfl) ⟨1748285, by rfl⟩ : syracuseStep 2331047 = 3496571) B3496571
theorem B1749415 : Blo 1553474 1749415 := bstep (se 1 (by rfl) ⟨1312061, by rfl⟩ : syracuseStep 1749415 = 2624123) B2624123
theorem B11801051 : Blo 1553474 11801051 := bstep (se 1 (by rfl) ⟨8850788, by rfl⟩ : syracuseStep 11801051 = 17701577) B17701577
theorem B2331131 : Blo 1553474 2331131 := bstep (se 1 (by rfl) ⟨1748348, by rfl⟩ : syracuseStep 2331131 = 3496697) B3496697
theorem B2331257 : Blo 1553474 2331257 := bstep (se 2 (by rfl) ⟨874221, by rfl⟩ : syracuseStep 2331257 = 1748443) B1748443
theorem B2331311 : Blo 1553474 2331311 := bstep (se 1 (by rfl) ⟨1748483, by rfl⟩ : syracuseStep 2331311 = 3496967) B3496967
theorem B2331359 : Blo 1553474 2331359 := bstep (se 1 (by rfl) ⟨1748519, by rfl⟩ : syracuseStep 2331359 = 3497039) B3497039
theorem B15151951 : Blo 1553474 15151951 := bstep (se 1 (by rfl) ⟨11363963, by rfl⟩ : syracuseStep 15151951 = 22727927) B22727927
theorem B75592561 : Blo 1553474 75592561 := bstep (se 2 (by rfl) ⟨28347210, by rfl⟩ : syracuseStep 75592561 = 56694421) B56694421
theorem B2331623 : Blo 1553474 2331623 := bstep (se 1 (by rfl) ⟨1748717, by rfl⟩ : syracuseStep 2331623 = 3497435) B3497435
theorem B2659303 : Blo 1553474 2659303 := bstep (se 1 (by rfl) ⟨1994477, by rfl⟩ : syracuseStep 2659303 = 3988955) B3988955
theorem B5903351 : Blo 1553474 5903351 := bstep (se 1 (by rfl) ⟨4427513, by rfl⟩ : syracuseStep 5903351 = 8855027) B8855027
theorem B59757587 : Blo 1553474 59757587 := bstep (se 1 (by rfl) ⟨44818190, by rfl⟩ : syracuseStep 59757587 = 89636381) B89636381
theorem B5248097 : Blo 1553474 5248097 := bstep (se 2 (by rfl) ⟨1968036, by rfl⟩ : syracuseStep 5248097 = 3936073) B3936073
theorem B2331881 : Blo 1553474 2331881 := bstep (se 2 (by rfl) ⟨874455, by rfl⟩ : syracuseStep 2331881 = 1748911) B1748911
theorem B26572049 : Blo 1553474 26572049 := bstep (se 2 (by rfl) ⟨9964518, by rfl⟩ : syracuseStep 26572049 = 19929037) B19929037
theorem B1553695 : Blo 1553474 1553695 := bstep (se 1 (by rfl) ⟨1165271, by rfl⟩ : syracuseStep 1553695 = 2330543) B2330543
theorem B2331935 : Blo 1553474 2331935 := bstep (se 1 (by rfl) ⟨1748951, by rfl⟩ : syracuseStep 2331935 = 3497903) B3497903
theorem B1553755 : Blo 1553474 1553755 := bstep (se 1 (by rfl) ⟨1165316, by rfl⟩ : syracuseStep 1553755 = 2330633) B2330633
theorem B1553775 : Blo 1553474 1553775 := bstep (se 1 (by rfl) ⟨1165331, by rfl⟩ : syracuseStep 1553775 = 2330663) B2330663
theorem B3495329 : Blo 1553474 3495329 := bstep (se 2 (by rfl) ⟨1310748, by rfl⟩ : syracuseStep 3495329 = 2621497) B2621497
theorem B1553831 : Blo 1553474 1553831 := bstep (se 1 (by rfl) ⟨1165373, by rfl⟩ : syracuseStep 1553831 = 2330747) B2330747
theorem B2332103 : Blo 1553474 2332103 := bstep (se 1 (by rfl) ⟨1749077, by rfl⟩ : syracuseStep 2332103 = 3498155) B3498155
theorem B11810285 : Blo 1553474 11810285 := bstep (se 3 (by rfl) ⟨2214428, by rfl⟩ : syracuseStep 11810285 = 4428857) B4428857
theorem B1553915 : Blo 1553474 1553915 := bstep (se 1 (by rfl) ⟨1165436, by rfl⟩ : syracuseStep 1553915 = 2330873) B2330873
theorem B7869959 : Blo 1553474 7869959 := bstep (se 1 (by rfl) ⟨5902469, by rfl⟩ : syracuseStep 7869959 = 11804939) B11804939
theorem B1553983 : Blo 1553474 1553983 := bstep (se 1 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 1553983 = 2330975) B2330975
theorem B1553991 : Blo 1553474 1553991 := bstep (se 1 (by rfl) ⟨1165493, by rfl⟩ : syracuseStep 1553991 = 2330987) B2330987
theorem B1660591 : Blo 1553474 1660591 := bstep (se 1 (by rfl) ⟨1245443, by rfl⟩ : syracuseStep 1660591 = 2490887) B2490887
theorem B1554143 : Blo 1553474 1554143 := bstep (se 1 (by rfl) ⟨1165607, by rfl⟩ : syracuseStep 1554143 = 2331215) B2331215
theorem B2332457 : Blo 1553474 2332457 := bstep (se 2 (by rfl) ⟨874671, by rfl⟩ : syracuseStep 2332457 = 1749343) B1749343
theorem B1554223 : Blo 1553474 1554223 := bstep (se 1 (by rfl) ⟨1165667, by rfl⟩ : syracuseStep 1554223 = 2331335) B2331335
theorem B2332463 : Blo 1553474 2332463 := bstep (se 1 (by rfl) ⟨1749347, by rfl⟩ : syracuseStep 2332463 = 3498695) B3498695
theorem B1554331 : Blo 1553474 1554331 := bstep (se 1 (by rfl) ⟨1165748, by rfl⟩ : syracuseStep 1554331 = 2331497) B2331497
theorem B3495887 : Blo 1553474 3495887 := bstep (se 1 (by rfl) ⟨2621915, by rfl⟩ : syracuseStep 3495887 = 5243831) B5243831
theorem B1554383 : Blo 1553474 1554383 := bstep (se 1 (by rfl) ⟨1165787, by rfl⟩ : syracuseStep 1554383 = 2331575) B2331575
theorem B1554407 : Blo 1553474 1554407 := bstep (se 1 (by rfl) ⟨1165805, by rfl⟩ : syracuseStep 1554407 = 2331611) B2331611
theorem B7870445 : Blo 1553474 7870445 := bstep (se 3 (by rfl) ⟨1475708, by rfl⟩ : syracuseStep 7870445 = 2951417) B2951417
theorem B2332937 : Blo 1553474 2332937 := bstep (se 2 (by rfl) ⟨874851, by rfl⟩ : syracuseStep 2332937 = 1749703) B1749703
theorem B3889433 : Blo 1553474 3889433 := bstep (se 2 (by rfl) ⟨1458537, by rfl⟩ : syracuseStep 3889433 = 2917075) B2917075
theorem B1554719 : Blo 1553474 1554719 := bstep (se 1 (by rfl) ⟨1166039, by rfl⟩ : syracuseStep 1554719 = 2332079) B2332079
theorem B3496265 : Blo 1553474 3496265 := bstep (se 2 (by rfl) ⟨1311099, by rfl⟩ : syracuseStep 3496265 = 2622199) B2622199
theorem B3496283 : Blo 1553474 3496283 := bstep (se 1 (by rfl) ⟨2622212, by rfl⟩ : syracuseStep 3496283 = 5244425) B5244425
theorem B1554779 : Blo 1553474 1554779 := bstep (se 1 (by rfl) ⟨1166084, by rfl⟩ : syracuseStep 1554779 = 2332169) B2332169
theorem B1554799 : Blo 1553474 1554799 := bstep (se 1 (by rfl) ⟨1166099, by rfl⟩ : syracuseStep 1554799 = 2332199) B2332199
theorem B2333039 : Blo 1553474 2333039 := bstep (se 1 (by rfl) ⟨1749779, by rfl⟩ : syracuseStep 2333039 = 3499559) B3499559
theorem B1554855 : Blo 1553474 1554855 := bstep (se 1 (by rfl) ⟨1166141, by rfl⟩ : syracuseStep 1554855 = 2332283) B2332283
theorem B5249447 : Blo 1553474 5249447 := bstep (se 1 (by rfl) ⟨3937085, by rfl⟩ : syracuseStep 5249447 = 7874171) B7874171
theorem B7870931 : Blo 1553474 7870931 := bstep (se 1 (by rfl) ⟨5903198, by rfl⟩ : syracuseStep 7870931 = 11806397) B11806397
theorem B1554939 : Blo 1553474 1554939 := bstep (se 1 (by rfl) ⟨1166204, by rfl⟩ : syracuseStep 1554939 = 2332409) B2332409
theorem B1555007 : Blo 1553474 1555007 := bstep (se 1 (by rfl) ⟨1166255, by rfl⟩ : syracuseStep 1555007 = 2332511) B2332511
theorem B1555015 : Blo 1553474 1555015 := bstep (se 1 (by rfl) ⟨1166261, by rfl⟩ : syracuseStep 1555015 = 2332523) B2332523
theorem B5249609 : Blo 1553474 5249609 := bstep (se 2 (by rfl) ⟨1968603, by rfl⟩ : syracuseStep 5249609 = 3937207) B3937207
theorem B11958923 : Blo 1553474 11958923 := bstep (se 1 (by rfl) ⟨8969192, by rfl⟩ : syracuseStep 11958923 = 17938385) B17938385
theorem B1555167 : Blo 1553474 1555167 := bstep (se 1 (by rfl) ⟨1166375, by rfl⟩ : syracuseStep 1555167 = 2332751) B2332751
theorem B2800403 : Blo 1553474 2800403 := bstep (se 1 (by rfl) ⟨2100302, by rfl⟩ : syracuseStep 2800403 = 4200605) B4200605
theorem B7871255 : Blo 1553474 7871255 := bstep (se 1 (by rfl) ⟨5903441, by rfl⟩ : syracuseStep 7871255 = 11806883) B11806883
theorem B1555247 : Blo 1553474 1555247 := bstep (se 1 (by rfl) ⟨1166435, by rfl⟩ : syracuseStep 1555247 = 2332871) B2332871
theorem B4922237 : Blo 1553474 4922237 := bstep (se 3 (by rfl) ⟨922919, by rfl⟩ : syracuseStep 4922237 = 1845839) B1845839
theorem B5905295 : Blo 1553474 5905295 := bstep (se 1 (by rfl) ⟨4428971, by rfl⟩ : syracuseStep 5905295 = 8857943) B8857943
theorem B3496859 : Blo 1553474 3496859 := bstep (se 1 (by rfl) ⟨2622644, by rfl⟩ : syracuseStep 3496859 = 5245289) B5245289
theorem B6642587 : Blo 1553474 6642587 := bstep (se 1 (by rfl) ⟨4981940, by rfl⟩ : syracuseStep 6642587 = 9963881) B9963881
theorem B1555355 : Blo 1553474 1555355 := bstep (se 1 (by rfl) ⟨1166516, by rfl⟩ : syracuseStep 1555355 = 2333033) B2333033
theorem B1555407 : Blo 1553474 1555407 := bstep (se 1 (by rfl) ⟨1166555, by rfl⟩ : syracuseStep 1555407 = 2333111) B2333111
theorem B1555431 : Blo 1553474 1555431 := bstep (se 1 (by rfl) ⟨1166573, by rfl⟩ : syracuseStep 1555431 = 2333147) B2333147
theorem B3497057 : Blo 1553474 3497057 := bstep (se 2 (by rfl) ⟨1311396, by rfl⟩ : syracuseStep 3497057 = 2622793) B2622793
theorem B9960677 : Blo 1553474 9960677 := bstep (se 4 (by rfl) ⟨933813, by rfl⟩ : syracuseStep 9960677 = 1867627) B1867627
theorem B3497255 : Blo 1553474 3497255 := bstep (se 1 (by rfl) ⟨2622941, by rfl⟩ : syracuseStep 3497255 = 5245883) B5245883
theorem B5602679 : Blo 1553474 5602679 := bstep (se 1 (by rfl) ⟨4202009, by rfl⟩ : syracuseStep 5602679 = 8404019) B8404019
theorem B2489849 : Blo 1553474 2489849 := bstep (se 2 (by rfl) ⟨933693, by rfl⟩ : syracuseStep 2489849 = 1867387) B1867387
theorem B27287063 : Blo 1553474 27287063 := bstep (se 1 (by rfl) ⟨20465297, by rfl⟩ : syracuseStep 27287063 = 40930595) B40930595
theorem B2489951 : Blo 1553474 2489951 := bstep (se 1 (by rfl) ⟨1867463, by rfl⟩ : syracuseStep 2489951 = 3734927) B3734927
theorem B7470701 : Blo 1553474 7470701 := bstep (se 3 (by rfl) ⟨1400756, by rfl⟩ : syracuseStep 7470701 = 2801513) B2801513
theorem B3497633 : Blo 1553474 3497633 := bstep (se 2 (by rfl) ⟨1311612, by rfl⟩ : syracuseStep 3497633 = 2623225) B2623225
theorem B3546887 : Blo 1553474 3546887 := bstep (se 1 (by rfl) ⟨2660165, by rfl⟩ : syracuseStep 3546887 = 5320331) B5320331
theorem B26550179 : Blo 1553474 26550179 := bstep (se 1 (by rfl) ⟨19912634, by rfl⟩ : syracuseStep 26550179 = 39825269) B39825269
theorem B8192033 : Blo 1553474 8192033 := bstep (se 2 (by rfl) ⟨3072012, by rfl⟩ : syracuseStep 8192033 = 6144025) B6144025
theorem B7872551 : Blo 1553474 7872551 := bstep (se 1 (by rfl) ⟨5904413, by rfl⟩ : syracuseStep 7872551 = 11808827) B11808827
theorem B2621659 : Blo 1553474 2621659 := bstep (se 1 (by rfl) ⟨1966244, by rfl⟩ : syracuseStep 2621659 = 3932489) B3932489
theorem B9961703 : Blo 1553474 9961703 := bstep (se 1 (by rfl) ⟨7471277, by rfl⟩ : syracuseStep 9961703 = 14942555) B14942555
theorem B5898521 : Blo 1553474 5898521 := bstep (se 2 (by rfl) ⟨2211945, by rfl⟩ : syracuseStep 5898521 = 4423891) B4423891
theorem B2949473 : Blo 1553474 2949473 := bstep (se 2 (by rfl) ⟨1106052, by rfl⟩ : syracuseStep 2949473 = 2212105) B2212105
theorem B7864775 : Blo 1553474 7864775 := bstep (se 1 (by rfl) ⟨5898581, by rfl⟩ : syracuseStep 7864775 = 11797163) B11797163
theorem B5898703 : Blo 1553474 5898703 := bstep (se 1 (by rfl) ⟨4424027, by rfl⟩ : syracuseStep 5898703 = 8848055) B8848055
theorem B2621929 : Blo 1553474 2621929 := bstep (se 2 (by rfl) ⟨983223, by rfl⟩ : syracuseStep 2621929 = 1966447) B1966447
theorem B2212447 : Blo 1553474 2212447 := bstep (se 1 (by rfl) ⟨1659335, by rfl⟩ : syracuseStep 2212447 = 3318671) B3318671
theorem B39838391 : Blo 1553474 39838391 := bstep (se 1 (by rfl) ⟨29878793, by rfl⟩ : syracuseStep 39838391 = 59757587) B59757587
theorem B3498731 : Blo 1553474 3498731 := bstep (se 1 (by rfl) ⟨2624048, by rfl⟩ : syracuseStep 3498731 = 5248097) B5248097
theorem B3932975 : Blo 1553474 3932975 := bstep (se 1 (by rfl) ⟨2949731, by rfl⟩ : syracuseStep 3932975 = 5899463) B5899463
theorem B8848237 : Blo 1553474 8848237 := bstep (se 3 (by rfl) ⟨1659044, by rfl⟩ : syracuseStep 8848237 = 3318089) B3318089
theorem B8856485 : Blo 1553474 8856485 := bstep (se 4 (by rfl) ⟨830295, by rfl⟩ : syracuseStep 8856485 = 1660591) B1660591
theorem B11363237 : Blo 1553474 11363237 := bstep (se 4 (by rfl) ⟨1065303, by rfl⟩ : syracuseStep 11363237 = 2130607) B2130607
theorem B5899175 : Blo 1553474 5899175 := bstep (se 1 (by rfl) ⟨4424381, by rfl⟩ : syracuseStep 5899175 = 8848763) B8848763
theorem B7472083 : Blo 1553474 7472083 := bstep (se 1 (by rfl) ⟨5604062, by rfl⟩ : syracuseStep 7472083 = 11208125) B11208125
theorem B7873523 : Blo 1553474 7873523 := bstep (se 1 (by rfl) ⟨5905142, by rfl⟩ : syracuseStep 7873523 = 11810285) B11810285
theorem B10093673 : Blo 1553474 10093673 := bstep (se 2 (by rfl) ⟨3785127, by rfl⟩ : syracuseStep 10093673 = 7570255) B7570255
theorem B20202601 : Blo 1553474 20202601 := bstep (se 2 (by rfl) ⟨7575975, by rfl⟩ : syracuseStep 20202601 = 15151951) B15151951
theorem B2213039 : Blo 1553474 2213039 := bstep (se 1 (by rfl) ⟨1659779, by rfl⟩ : syracuseStep 2213039 = 3319559) B3319559
theorem B44811629 : Blo 1553474 44811629 := bstep (se 3 (by rfl) ⟨8402180, by rfl⟩ : syracuseStep 44811629 = 16804361) B16804361
theorem B14943703 : Blo 1553474 14943703 := bstep (se 1 (by rfl) ⟨11207777, by rfl⟩ : syracuseStep 14943703 = 22415555) B22415555
theorem B17704493 : Blo 1553474 17704493 := bstep (se 3 (by rfl) ⟨3319592, by rfl⟩ : syracuseStep 17704493 = 6639185) B6639185
theorem B3499631 : Blo 1553474 3499631 := bstep (se 1 (by rfl) ⟨2624723, by rfl⟩ : syracuseStep 3499631 = 5249447) B5249447
theorem B2623097 : Blo 1553474 2623097 := bstep (se 2 (by rfl) ⟨983661, by rfl⟩ : syracuseStep 2623097 = 1967323) B1967323
theorem B5604985 : Blo 1553474 5604985 := bstep (se 2 (by rfl) ⟨2101869, by rfl⟩ : syracuseStep 5604985 = 4203739) B4203739
theorem B5605031 : Blo 1553474 5605031 := bstep (se 1 (by rfl) ⟨4203773, by rfl⟩ : syracuseStep 5605031 = 8407547) B8407547
theorem B3499739 : Blo 1553474 3499739 := bstep (se 1 (by rfl) ⟨2624804, by rfl⟩ : syracuseStep 3499739 = 5249609) B5249609
theorem B7972615 : Blo 1553474 7972615 := bstep (se 1 (by rfl) ⟨5979461, by rfl⟩ : syracuseStep 7972615 = 11958923) B11958923
theorem B14182217 : Blo 1553474 14182217 := bstep (se 2 (by rfl) ⟨5318331, by rfl⟩ : syracuseStep 14182217 = 10636663) B10636663
theorem B5900161 : Blo 1553474 5900161 := bstep (se 2 (by rfl) ⟨2212560, by rfl⟩ : syracuseStep 5900161 = 4425121) B4425121
theorem B2213831 : Blo 1553474 2213831 := bstep (se 1 (by rfl) ⟨1660373, by rfl⟩ : syracuseStep 2213831 = 3320747) B3320747
theorem B7473161 : Blo 1553474 7473161 := bstep (se 2 (by rfl) ⟨2802435, by rfl⟩ : syracuseStep 7473161 = 5604871) B5604871
theorem B8407091 : Blo 1553474 8407091 := bstep (se 1 (by rfl) ⟨6305318, by rfl⟩ : syracuseStep 8407091 = 12610637) B12610637
theorem B2623583 : Blo 1553474 2623583 := bstep (se 1 (by rfl) ⟨1967687, by rfl⟩ : syracuseStep 2623583 = 3935375) B3935375
theorem B28403993 : Blo 1553474 28403993 := bstep (se 2 (by rfl) ⟨10651497, by rfl⟩ : syracuseStep 28403993 = 21302995) B21302995
theorem B2951471 : Blo 1553474 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B39864635 : Blo 1553474 39864635 := bstep (se 1 (by rfl) ⟨29898476, by rfl⟩ : syracuseStep 39864635 = 59796953) B59796953
theorem B3934727 : Blo 1553474 3934727 := bstep (se 1 (by rfl) ⟨2951045, by rfl⟩ : syracuseStep 3934727 = 5902091) B5902091
theorem B43125257 : Blo 1553474 43125257 := bstep (se 2 (by rfl) ⟨16171971, by rfl⟩ : syracuseStep 43125257 = 32343943) B32343943
theorem B8407739 : Blo 1553474 8407739 := bstep (se 1 (by rfl) ⟨6305804, by rfl⟩ : syracuseStep 8407739 = 12611609) B12611609
theorem B7867367 : Blo 1553474 7867367 := bstep (se 1 (by rfl) ⟨5900525, by rfl⟩ : syracuseStep 7867367 = 11801051) B11801051
theorem B1748191 : Blo 1553474 1748191 := bstep (se 1 (by rfl) ⟨1311143, by rfl⟩ : syracuseStep 1748191 = 2622287) B2622287
theorem B3935567 : Blo 1553474 3935567 := bstep (se 1 (by rfl) ⟨2951675, by rfl⟩ : syracuseStep 3935567 = 5903351) B5903351
theorem B17714699 : Blo 1553474 17714699 := bstep (se 1 (by rfl) ⟨13286024, by rfl⟩ : syracuseStep 17714699 = 26572049) B26572049
theorem B2330219 : Blo 1553474 2330219 := bstep (se 1 (by rfl) ⟨1747664, by rfl⟩ : syracuseStep 2330219 = 3495329) B3495329
theorem B5246639 : Blo 1553474 5246639 := bstep (se 1 (by rfl) ⟨3934979, by rfl⟩ : syracuseStep 5246639 = 7869959) B7869959
theorem B2330345 : Blo 1553474 2330345 := bstep (se 2 (by rfl) ⟨873879, by rfl⟩ : syracuseStep 2330345 = 1747759) B1747759
theorem B100790081 : Blo 1553474 100790081 := bstep (se 2 (by rfl) ⟨37796280, by rfl⟩ : syracuseStep 100790081 = 75592561) B75592561
theorem B2330489 : Blo 1553474 2330489 := bstep (se 2 (by rfl) ⟨873933, by rfl⟩ : syracuseStep 2330489 = 1747867) B1747867
theorem B2330591 : Blo 1553474 2330591 := bstep (se 1 (by rfl) ⟨1747943, by rfl⟩ : syracuseStep 2330591 = 3495887) B3495887
theorem B9957343 : Blo 1553474 9957343 := bstep (se 1 (by rfl) ⟨7468007, by rfl⟩ : syracuseStep 9957343 = 14936015) B14936015
theorem B5246963 : Blo 1553474 5246963 := bstep (se 1 (by rfl) ⟨3935222, by rfl⟩ : syracuseStep 5246963 = 7870445) B7870445
theorem B12955697 : Blo 1553474 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B2592955 : Blo 1553474 2592955 := bstep (se 1 (by rfl) ⟨1944716, by rfl⟩ : syracuseStep 2592955 = 3889433) B3889433
theorem B2330843 : Blo 1553474 2330843 := bstep (se 1 (by rfl) ⟨1748132, by rfl⟩ : syracuseStep 2330843 = 3496265) B3496265
theorem B2330855 : Blo 1553474 2330855 := bstep (se 1 (by rfl) ⟨1748141, by rfl⟩ : syracuseStep 2330855 = 3496283) B3496283
theorem B6639869 : Blo 1553474 6639869 := bstep (se 3 (by rfl) ⟨1244975, by rfl⟩ : syracuseStep 6639869 = 2489951) B2489951
theorem B5247287 : Blo 1553474 5247287 := bstep (se 1 (by rfl) ⟨3935465, by rfl⟩ : syracuseStep 5247287 = 7870931) B7870931
theorem B2331017 : Blo 1553474 2331017 := bstep (se 2 (by rfl) ⟨874131, by rfl⟩ : syracuseStep 2331017 = 1748263) B1748263
theorem B2331113 : Blo 1553474 2331113 := bstep (se 2 (by rfl) ⟨874167, by rfl⟩ : syracuseStep 2331113 = 1748335) B1748335
theorem B5247503 : Blo 1553474 5247503 := bstep (se 1 (by rfl) ⟨3935627, by rfl⟩ : syracuseStep 5247503 = 7871255) B7871255
theorem B3281491 : Blo 1553474 3281491 := bstep (se 1 (by rfl) ⟨2461118, by rfl⟩ : syracuseStep 3281491 = 4922237) B4922237
theorem B3936863 : Blo 1553474 3936863 := bstep (se 1 (by rfl) ⟨2952647, by rfl⟩ : syracuseStep 3936863 = 5905295) B5905295
theorem B2331239 : Blo 1553474 2331239 := bstep (se 1 (by rfl) ⟨1748429, by rfl⟩ : syracuseStep 2331239 = 3496859) B3496859
theorem B4428391 : Blo 1553474 4428391 := bstep (se 1 (by rfl) ⟨3321293, by rfl⟩ : syracuseStep 4428391 = 6642587) B6642587
theorem B9458365 : Blo 1553474 9458365 := bstep (se 3 (by rfl) ⟨1773443, by rfl⟩ : syracuseStep 9458365 = 3546887) B3546887
theorem B2331371 : Blo 1553474 2331371 := bstep (se 1 (by rfl) ⟨1748528, by rfl⟩ : syracuseStep 2331371 = 3497057) B3497057
theorem B2331401 : Blo 1553474 2331401 := bstep (se 2 (by rfl) ⟨874275, by rfl⟩ : syracuseStep 2331401 = 1748551) B1748551
theorem B6640451 : Blo 1553474 6640451 := bstep (se 1 (by rfl) ⟨4980338, by rfl⟩ : syracuseStep 6640451 = 9960677) B9960677
theorem B9450335 : Blo 1553474 9450335 := bstep (se 1 (by rfl) ⟨7087751, by rfl⟩ : syracuseStep 9450335 = 14175503) B14175503
theorem B2331503 : Blo 1553474 2331503 := bstep (se 1 (by rfl) ⟨1748627, by rfl⟩ : syracuseStep 2331503 = 3497255) B3497255
theorem B11801537 : Blo 1553474 11801537 := bstep (se 2 (by rfl) ⟨4425576, by rfl⟩ : syracuseStep 11801537 = 8851153) B8851153
theorem B1659899 : Blo 1553474 1659899 := bstep (se 1 (by rfl) ⟨1244924, by rfl⟩ : syracuseStep 1659899 = 2489849) B2489849
theorem B18191375 : Blo 1553474 18191375 := bstep (se 1 (by rfl) ⟨13643531, by rfl⟩ : syracuseStep 18191375 = 27287063) B27287063
theorem B9450533 : Blo 1553474 9450533 := bstep (se 4 (by rfl) ⟨885987, by rfl⟩ : syracuseStep 9450533 = 1771975) B1771975
theorem B2331755 : Blo 1553474 2331755 := bstep (se 1 (by rfl) ⟨1748816, by rfl⟩ : syracuseStep 2331755 = 3497633) B3497633
theorem B1553615 : Blo 1553474 1553615 := bstep (se 1 (by rfl) ⟨1165211, by rfl⟩ : syracuseStep 1553615 = 2330423) B2330423
theorem B17700119 : Blo 1553474 17700119 := bstep (se 1 (by rfl) ⟨13275089, by rfl⟩ : syracuseStep 17700119 = 26550179) B26550179
theorem B5600603 : Blo 1553474 5600603 := bstep (se 1 (by rfl) ⟨4200452, by rfl⟩ : syracuseStep 5600603 = 8400905) B8400905
theorem B2331995 : Blo 1553474 2331995 := bstep (se 1 (by rfl) ⟨1748996, by rfl⟩ : syracuseStep 2331995 = 3497993) B3497993
theorem B15947117 : Blo 1553474 15947117 := bstep (se 3 (by rfl) ⟨2990084, by rfl⟩ : syracuseStep 15947117 = 5980169) B5980169
theorem B1553819 : Blo 1553474 1553819 := bstep (se 1 (by rfl) ⟨1165364, by rfl⟩ : syracuseStep 1553819 = 2330729) B2330729
theorem B5248583 : Blo 1553474 5248583 := bstep (se 1 (by rfl) ⟨3936437, by rfl⟩ : syracuseStep 5248583 = 7872875) B7872875
theorem B1554031 : Blo 1553474 1554031 := bstep (se 1 (by rfl) ⟨1165523, by rfl⟩ : syracuseStep 1554031 = 2331047) B2331047
theorem B2332271 : Blo 1553474 2332271 := bstep (se 1 (by rfl) ⟨1749203, by rfl⟩ : syracuseStep 2332271 = 3498407) B3498407
theorem B2659961 : Blo 1553474 2659961 := bstep (se 2 (by rfl) ⟨997485, by rfl⟩ : syracuseStep 2659961 = 1994971) B1994971
theorem B1554087 : Blo 1553474 1554087 := bstep (se 1 (by rfl) ⟨1165565, by rfl⟩ : syracuseStep 1554087 = 2331131) B2331131
theorem B2332343 : Blo 1553474 2332343 := bstep (se 1 (by rfl) ⟨1749257, by rfl⟩ : syracuseStep 2332343 = 3498515) B3498515
theorem B2332379 : Blo 1553474 2332379 := bstep (se 1 (by rfl) ⟨1749284, by rfl⟩ : syracuseStep 2332379 = 3498569) B3498569
theorem B1554171 : Blo 1553474 1554171 := bstep (se 1 (by rfl) ⟨1165628, by rfl⟩ : syracuseStep 1554171 = 2331257) B2331257
theorem B1554207 : Blo 1553474 1554207 := bstep (se 1 (by rfl) ⟨1165655, by rfl⟩ : syracuseStep 1554207 = 2331311) B2331311
theorem B3495743 : Blo 1553474 3495743 := bstep (se 1 (by rfl) ⟨2621807, by rfl⟩ : syracuseStep 3495743 = 5243615) B5243615
theorem B1554239 : Blo 1553474 1554239 := bstep (se 1 (by rfl) ⟨1165679, by rfl⟩ : syracuseStep 1554239 = 2331359) B2331359
theorem B2332553 : Blo 1553474 2332553 := bstep (se 2 (by rfl) ⟨874707, by rfl⟩ : syracuseStep 2332553 = 1749415) B1749415
theorem B1554415 : Blo 1553474 1554415 := bstep (se 1 (by rfl) ⟨1165811, by rfl⟩ : syracuseStep 1554415 = 2331623) B2331623
theorem B2332655 : Blo 1553474 2332655 := bstep (se 1 (by rfl) ⟨1749491, by rfl⟩ : syracuseStep 2332655 = 3498983) B3498983
theorem B3496031 : Blo 1553474 3496031 := bstep (se 1 (by rfl) ⟨2622023, by rfl⟩ : syracuseStep 3496031 = 5244047) B5244047
theorem B1661023 : Blo 1553474 1661023 := bstep (se 1 (by rfl) ⟨1245767, by rfl⟩ : syracuseStep 1661023 = 2491535) B2491535
theorem B1554587 : Blo 1553474 1554587 := bstep (se 1 (by rfl) ⟨1165940, by rfl⟩ : syracuseStep 1554587 = 2331881) B2331881
theorem B1554623 : Blo 1553474 1554623 := bstep (se 1 (by rfl) ⟨1165967, by rfl⟩ : syracuseStep 1554623 = 2331935) B2331935
theorem B2332907 : Blo 1553474 2332907 := bstep (se 1 (by rfl) ⟨1749680, by rfl⟩ : syracuseStep 2332907 = 3499361) B3499361
theorem B2332967 : Blo 1553474 2332967 := bstep (se 1 (by rfl) ⟨1749725, by rfl⟩ : syracuseStep 2332967 = 3499451) B3499451
theorem B1554735 : Blo 1553474 1554735 := bstep (se 1 (by rfl) ⟨1166051, by rfl⟩ : syracuseStep 1554735 = 2332103) B2332103
theorem B2333051 : Blo 1553474 2333051 := bstep (se 1 (by rfl) ⟨1749788, by rfl⟩ : syracuseStep 2333051 = 3499577) B3499577
theorem B5249555 : Blo 1553474 5249555 := bstep (se 1 (by rfl) ⟨3937166, by rfl⟩ : syracuseStep 5249555 = 7874333) B7874333
theorem B1554971 : Blo 1553474 1554971 := bstep (se 1 (by rfl) ⟨1166228, by rfl⟩ : syracuseStep 1554971 = 2332457) B2332457
theorem B1554975 : Blo 1553474 1554975 := bstep (se 1 (by rfl) ⟨1166231, by rfl⟩ : syracuseStep 1554975 = 2332463) B2332463
theorem B3545737 : Blo 1553474 3545737 := bstep (se 2 (by rfl) ⟨1329651, by rfl⟩ : syracuseStep 3545737 = 2659303) B2659303
theorem B3496787 : Blo 1553474 3496787 := bstep (se 1 (by rfl) ⟨2622590, by rfl⟩ : syracuseStep 3496787 = 5245181) B5245181
theorem B1555291 : Blo 1553474 1555291 := bstep (se 1 (by rfl) ⟨1166468, by rfl⟩ : syracuseStep 1555291 = 2332937) B2332937
theorem B1555359 : Blo 1553474 1555359 := bstep (se 1 (by rfl) ⟨1166519, by rfl⟩ : syracuseStep 1555359 = 2333039) B2333039
theorem B1866935 : Blo 1553474 1866935 := bstep (se 1 (by rfl) ⟨1400201, by rfl⟩ : syracuseStep 1866935 = 2800403) B2800403
theorem B7871741 : Blo 1553474 7871741 := bstep (se 3 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 7871741 = 2951903) B2951903
theorem B3497327 : Blo 1553474 3497327 := bstep (se 1 (by rfl) ⟨2622995, by rfl⟩ : syracuseStep 3497327 = 5245991) B5245991
theorem B11197835 : Blo 1553474 11197835 := bstep (se 1 (by rfl) ⟨8398376, by rfl⟩ : syracuseStep 11197835 = 16796753) B16796753
theorem B2801225 : Blo 1553474 2801225 := bstep (se 2 (by rfl) ⟨1050459, by rfl⟩ : syracuseStep 2801225 = 2100919) B2100919
theorem B3735119 : Blo 1553474 3735119 := bstep (se 1 (by rfl) ⟨2801339, by rfl⟩ : syracuseStep 3735119 = 5602679) B5602679
theorem B3497615 : Blo 1553474 3497615 := bstep (se 1 (by rfl) ⟨2623211, by rfl⟩ : syracuseStep 3497615 = 5246423) B5246423
theorem B3497705 : Blo 1553474 3497705 := bstep (se 2 (by rfl) ⟨1311639, by rfl⟩ : syracuseStep 3497705 = 2623279) B2623279
theorem B4980467 : Blo 1553474 4980467 := bstep (se 1 (by rfl) ⟨3735350, by rfl⟩ : syracuseStep 4980467 = 7470701) B7470701
theorem B5603197 : Blo 1553474 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B3932347 : Blo 1553474 3932347 := bstep (se 1 (by rfl) ⟨2949260, by rfl⟩ : syracuseStep 3932347 = 5898521) B5898521
theorem B3498191 : Blo 1553474 3498191 := bstep (se 1 (by rfl) ⟨2623643, by rfl⟩ : syracuseStep 3498191 = 5247287) B5247287
theorem B3457273 : Blo 1553474 3457273 := bstep (se 2 (by rfl) ⟨1296477, by rfl⟩ : syracuseStep 3457273 = 2592955) B2592955
theorem B5243183 : Blo 1553474 5243183 := bstep (se 1 (by rfl) ⟨3932387, by rfl⟩ : syracuseStep 5243183 = 7864775) B7864775
theorem B3498335 : Blo 1553474 3498335 := bstep (se 1 (by rfl) ⟨2623751, by rfl⟩ : syracuseStep 3498335 = 5247503) B5247503
theorem B26558927 : Blo 1553474 26558927 := bstep (se 1 (by rfl) ⟨19919195, by rfl⟩ : syracuseStep 26558927 = 39838391) B39838391
theorem B2621983 : Blo 1553474 2621983 := bstep (se 1 (by rfl) ⟨1966487, by rfl⟩ : syracuseStep 2621983 = 3932975) B3932975
theorem B6300223 : Blo 1553474 6300223 := bstep (se 1 (by rfl) ⟨4725167, by rfl⟩ : syracuseStep 6300223 = 9450335) B9450335
theorem B7864937 : Blo 1553474 7864937 := bstep (se 2 (by rfl) ⟨2949351, by rfl⟩ : syracuseStep 7864937 = 5898703) B5898703
theorem B3932783 : Blo 1553474 3932783 := bstep (se 1 (by rfl) ⟨2949587, by rfl⟩ : syracuseStep 3932783 = 5899175) B5899175
theorem B6300355 : Blo 1553474 6300355 := bstep (se 1 (by rfl) ⟨4725266, by rfl⟩ : syracuseStep 6300355 = 9450533) B9450533
theorem B2949929 : Blo 1553474 2949929 := bstep (se 2 (by rfl) ⟨1106223, by rfl⟩ : syracuseStep 2949929 = 2212447) B2212447
theorem B14934941 : Blo 1553474 14934941 := bstep (se 3 (by rfl) ⟨2800301, by rfl⟩ : syracuseStep 14934941 = 5600603) B5600603
theorem B7865261 : Blo 1553474 7865261 := bstep (se 3 (by rfl) ⟨1474736, by rfl⟩ : syracuseStep 7865261 = 2949473) B2949473
theorem B3499055 : Blo 1553474 3499055 := bstep (se 1 (by rfl) ⟨2624291, by rfl⟩ : syracuseStep 3499055 = 5248583) B5248583
theorem B3736687 : Blo 1553474 3736687 := bstep (se 1 (by rfl) ⟨2802515, by rfl⟩ : syracuseStep 3736687 = 5605031) B5605031
theorem B11797649 : Blo 1553474 11797649 := bstep (se 2 (by rfl) ⟨4424118, by rfl⟩ : syracuseStep 11797649 = 8848237) B8848237
theorem B9454811 : Blo 1553474 9454811 := bstep (se 1 (by rfl) ⟨7091108, by rfl⟩ : syracuseStep 9454811 = 14182217) B14182217
theorem B9962777 : Blo 1553474 9962777 := bstep (se 2 (by rfl) ⟨3736041, by rfl⟩ : syracuseStep 9962777 = 7472083) B7472083
theorem B4982107 : Blo 1553474 4982107 := bstep (se 1 (by rfl) ⟨3736580, by rfl⟩ : syracuseStep 4982107 = 7473161) B7473161
theorem B115000685 : Blo 1553474 115000685 := bstep (se 3 (by rfl) ⟨21562628, by rfl⟩ : syracuseStep 115000685 = 43125257) B43125257
theorem B5604727 : Blo 1553474 5604727 := bstep (se 1 (by rfl) ⟨4203545, by rfl⟩ : syracuseStep 5604727 = 8407091) B8407091
theorem B26936801 : Blo 1553474 26936801 := bstep (se 2 (by rfl) ⟨10101300, by rfl⟩ : syracuseStep 26936801 = 20202601) B20202601
theorem B1967647 : Blo 1553474 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B26576423 : Blo 1553474 26576423 := bstep (se 1 (by rfl) ⟨19932317, by rfl⟩ : syracuseStep 26576423 = 39864635) B39864635
theorem B2623151 : Blo 1553474 2623151 := bstep (se 1 (by rfl) ⟨1967363, by rfl⟩ : syracuseStep 2623151 = 3934727) B3934727
theorem B3499703 : Blo 1553474 3499703 := bstep (se 1 (by rfl) ⟨2624777, by rfl⟩ : syracuseStep 3499703 = 5249555) B5249555
theorem B5605159 : Blo 1553474 5605159 := bstep (se 1 (by rfl) ⟨4203869, by rfl⟩ : syracuseStep 5605159 = 8407739) B8407739
theorem B19924937 : Blo 1553474 19924937 := bstep (se 2 (by rfl) ⟨7471851, by rfl⟩ : syracuseStep 19924937 = 14943703) B14943703
theorem B5244911 : Blo 1553474 5244911 := bstep (se 1 (by rfl) ⟨3933683, by rfl⟩ : syracuseStep 5244911 = 7867367) B7867367
theorem B7473313 : Blo 1553474 7473313 := bstep (se 2 (by rfl) ⟨2802492, by rfl⟩ : syracuseStep 7473313 = 5604985) B5604985
theorem B2623711 : Blo 1553474 2623711 := bstep (se 1 (by rfl) ⟨1967783, by rfl⟩ : syracuseStep 2623711 = 3935567) B3935567
theorem B7465223 : Blo 1553474 7465223 := bstep (se 1 (by rfl) ⟨5598917, by rfl⟩ : syracuseStep 7465223 = 11197835) B11197835
theorem B3320311 : Blo 1553474 3320311 := bstep (se 1 (by rfl) ⟨2490233, by rfl⟩ : syracuseStep 3320311 = 4980467) B4980467
theorem B7866881 : Blo 1553474 7866881 := bstep (se 2 (by rfl) ⟨2950080, by rfl⟩ : syracuseStep 7866881 = 5900161) B5900161
theorem B67193387 : Blo 1553474 67193387 := bstep (se 1 (by rfl) ⟨50395040, by rfl⟩ : syracuseStep 67193387 = 100790081) B100790081
theorem B4426397 : Blo 1553474 4426397 := bstep (se 3 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 4426397 = 1659899) B1659899
theorem B8637131 : Blo 1553474 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B2214697 : Blo 1553474 2214697 := bstep (se 2 (by rfl) ⟨830511, by rfl⟩ : syracuseStep 2214697 = 1661023) B1661023
theorem B4426579 : Blo 1553474 4426579 := bstep (se 1 (by rfl) ⟨3319934, by rfl⟩ : syracuseStep 4426579 = 6639869) B6639869
theorem B2624575 : Blo 1553474 2624575 := bstep (se 1 (by rfl) ⟨1968431, by rfl⟩ : syracuseStep 2624575 = 3936863) B3936863
theorem B17501285 : Blo 1553474 17501285 := bstep (se 4 (by rfl) ⟨1640745, by rfl⟩ : syracuseStep 17501285 = 3281491) B3281491
theorem B5901437 : Blo 1553474 5901437 := bstep (se 3 (by rfl) ⟨1106519, by rfl⟩ : syracuseStep 5901437 = 2213039) B2213039
theorem B4426967 : Blo 1553474 4426967 := bstep (se 1 (by rfl) ⟨3320225, by rfl⟩ : syracuseStep 4426967 = 6640451) B6640451
theorem B7867691 : Blo 1553474 7867691 := bstep (se 1 (by rfl) ⟨5900768, by rfl⟩ : syracuseStep 7867691 = 11801537) B11801537
theorem B12127583 : Blo 1553474 12127583 := bstep (se 1 (by rfl) ⟨9095687, by rfl⟩ : syracuseStep 12127583 = 18191375) B18191375
theorem B18910597 : Blo 1553474 18910597 := bstep (se 4 (by rfl) ⟨1772868, by rfl⟩ : syracuseStep 18910597 = 3545737) B3545737
theorem B6729115 : Blo 1553474 6729115 := bstep (se 1 (by rfl) ⟨5046836, by rfl⟩ : syracuseStep 6729115 = 10093673) B10093673
theorem B11800079 : Blo 1553474 11800079 := bstep (se 1 (by rfl) ⟨8850059, by rfl⟩ : syracuseStep 11800079 = 17700119) B17700119
theorem B12611153 : Blo 1553474 12611153 := bstep (se 2 (by rfl) ⟨4729182, by rfl⟩ : syracuseStep 12611153 = 9458365) B9458365
theorem B1748731 : Blo 1553474 1748731 := bstep (se 1 (by rfl) ⟨1311548, by rfl⟩ : syracuseStep 1748731 = 2623097) B2623097
theorem B1773307 : Blo 1553474 1773307 := bstep (se 1 (by rfl) ⟨1329980, by rfl⟩ : syracuseStep 1773307 = 2659961) B2659961
theorem B2330495 : Blo 1553474 2330495 := bstep (se 1 (by rfl) ⟨1747871, by rfl⟩ : syracuseStep 2330495 = 3495743) B3495743
theorem B2330687 : Blo 1553474 2330687 := bstep (se 1 (by rfl) ⟨1748015, by rfl⟩ : syracuseStep 2330687 = 3496031) B3496031
theorem B1749055 : Blo 1553474 1749055 := bstep (se 1 (by rfl) ⟨1311791, by rfl⟩ : syracuseStep 1749055 = 2623583) B2623583
theorem B18935995 : Blo 1553474 18935995 := bstep (se 1 (by rfl) ⟨14201996, by rfl⟩ : syracuseStep 18935995 = 28403993) B28403993
theorem B2330921 : Blo 1553474 2330921 := bstep (se 2 (by rfl) ⟨874095, by rfl⟩ : syracuseStep 2330921 = 1748191) B1748191
theorem B2331191 : Blo 1553474 2331191 := bstep (se 1 (by rfl) ⟨1748393, by rfl⟩ : syracuseStep 2331191 = 3496787) B3496787
theorem B5247827 : Blo 1553474 5247827 := bstep (se 1 (by rfl) ⟨3935870, by rfl⟩ : syracuseStep 5247827 = 7871741) B7871741
theorem B2331551 : Blo 1553474 2331551 := bstep (se 1 (by rfl) ⟨1748663, by rfl⟩ : syracuseStep 2331551 = 3497327) B3497327
theorem B11809799 : Blo 1553474 11809799 := bstep (se 1 (by rfl) ⟨8857349, by rfl⟩ : syracuseStep 11809799 = 17714699) B17714699
theorem B10630153 : Blo 1553474 10630153 := bstep (se 2 (by rfl) ⟨3986307, by rfl⟩ : syracuseStep 10630153 = 7972615) B7972615
theorem B1553479 : Blo 1553474 1553479 := bstep (se 1 (by rfl) ⟨1165109, by rfl⟩ : syracuseStep 1553479 = 2330219) B2330219
theorem B2331743 : Blo 1553474 2331743 := bstep (se 1 (by rfl) ⟨1748807, by rfl⟩ : syracuseStep 2331743 = 3497615) B3497615
theorem B1553563 : Blo 1553474 1553563 := bstep (se 1 (by rfl) ⟨1165172, by rfl⟩ : syracuseStep 1553563 = 2330345) B2330345
theorem B2331803 : Blo 1553474 2331803 := bstep (se 1 (by rfl) ⟨1748852, by rfl⟩ : syracuseStep 2331803 = 3497705) B3497705
theorem B5903549 : Blo 1553474 5903549 := bstep (se 3 (by rfl) ⟨1106915, by rfl⟩ : syracuseStep 5903549 = 2213831) B2213831
theorem B1553659 : Blo 1553474 1553659 := bstep (se 1 (by rfl) ⟨1165244, by rfl⟩ : syracuseStep 1553659 = 2330489) B2330489
theorem B13276457 : Blo 1553474 13276457 := bstep (se 2 (by rfl) ⟨4978671, by rfl⟩ : syracuseStep 13276457 = 9957343) B9957343
theorem B1553727 : Blo 1553474 1553727 := bstep (se 1 (by rfl) ⟨1165295, by rfl⟩ : syracuseStep 1553727 = 2330591) B2330591
theorem B5461355 : Blo 1553474 5461355 := bstep (se 1 (by rfl) ⟨4096016, by rfl⟩ : syracuseStep 5461355 = 8192033) B8192033
theorem B5248367 : Blo 1553474 5248367 := bstep (se 1 (by rfl) ⟨3936275, by rfl⟩ : syracuseStep 5248367 = 7872551) B7872551
theorem B1553895 : Blo 1553474 1553895 := bstep (se 1 (by rfl) ⟨1165421, by rfl⟩ : syracuseStep 1553895 = 2330843) B2330843
theorem B1553903 : Blo 1553474 1553903 := bstep (se 1 (by rfl) ⟨1165427, by rfl⟩ : syracuseStep 1553903 = 2330855) B2330855
theorem B6641135 : Blo 1553474 6641135 := bstep (se 1 (by rfl) ⟨4980851, by rfl⟩ : syracuseStep 6641135 = 9961703) B9961703
theorem B1554011 : Blo 1553474 1554011 := bstep (se 1 (by rfl) ⟨1165508, by rfl⟩ : syracuseStep 1554011 = 2331017) B2331017
theorem B3495545 : Blo 1553474 3495545 := bstep (se 2 (by rfl) ⟨1310829, by rfl⟩ : syracuseStep 3495545 = 2621659) B2621659
theorem B1554075 : Blo 1553474 1554075 := bstep (se 1 (by rfl) ⟨1165556, by rfl⟩ : syracuseStep 1554075 = 2331113) B2331113
theorem B1554159 : Blo 1553474 1554159 := bstep (se 1 (by rfl) ⟨1165619, by rfl⟩ : syracuseStep 1554159 = 2331239) B2331239
theorem B4978493 : Blo 1553474 4978493 := bstep (se 3 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 4978493 = 1866935) B1866935
theorem B1554247 : Blo 1553474 1554247 := bstep (se 1 (by rfl) ⟨1165685, by rfl⟩ : syracuseStep 1554247 = 2331371) B2331371
theorem B2332487 : Blo 1553474 2332487 := bstep (se 1 (by rfl) ⟨1749365, by rfl⟩ : syracuseStep 2332487 = 3498731) B3498731
theorem B1554267 : Blo 1553474 1554267 := bstep (se 1 (by rfl) ⟨1165700, by rfl⟩ : syracuseStep 1554267 = 2331401) B2331401
theorem B1554335 : Blo 1553474 1554335 := bstep (se 1 (by rfl) ⟨1165751, by rfl⟩ : syracuseStep 1554335 = 2331503) B2331503
theorem B5904323 : Blo 1553474 5904323 := bstep (se 1 (by rfl) ⟨4428242, by rfl⟩ : syracuseStep 5904323 = 8856485) B8856485
theorem B7575491 : Blo 1553474 7575491 := bstep (se 1 (by rfl) ⟨5681618, by rfl⟩ : syracuseStep 7575491 = 11363237) B11363237
theorem B3495905 : Blo 1553474 3495905 := bstep (se 2 (by rfl) ⟨1310964, by rfl⟩ : syracuseStep 3495905 = 2621929) B2621929
theorem B5249015 : Blo 1553474 5249015 := bstep (se 1 (by rfl) ⟨3936761, by rfl⟩ : syracuseStep 5249015 = 7873523) B7873523
theorem B1554503 : Blo 1553474 1554503 := bstep (se 1 (by rfl) ⟨1165877, by rfl⟩ : syracuseStep 1554503 = 2331755) B2331755
theorem B5904521 : Blo 1553474 5904521 := bstep (se 2 (by rfl) ⟨2214195, by rfl⟩ : syracuseStep 5904521 = 4428391) B4428391
theorem B1554663 : Blo 1553474 1554663 := bstep (se 1 (by rfl) ⟨1165997, by rfl⟩ : syracuseStep 1554663 = 2331995) B2331995
theorem B10631411 : Blo 1553474 10631411 := bstep (se 1 (by rfl) ⟨7973558, by rfl⟩ : syracuseStep 10631411 = 15947117) B15947117
theorem B29874419 : Blo 1553474 29874419 := bstep (se 1 (by rfl) ⟨22405814, by rfl⟩ : syracuseStep 29874419 = 44811629) B44811629
theorem B11802995 : Blo 1553474 11802995 := bstep (se 1 (by rfl) ⟨8852246, by rfl⟩ : syracuseStep 11802995 = 17704493) B17704493
theorem B1554847 : Blo 1553474 1554847 := bstep (se 1 (by rfl) ⟨1166135, by rfl⟩ : syracuseStep 1554847 = 2332271) B2332271
theorem B2333087 : Blo 1553474 2333087 := bstep (se 1 (by rfl) ⟨1749815, by rfl⟩ : syracuseStep 2333087 = 3499631) B3499631
theorem B1554895 : Blo 1553474 1554895 := bstep (se 1 (by rfl) ⟨1166171, by rfl⟩ : syracuseStep 1554895 = 2332343) B2332343
theorem B1554919 : Blo 1553474 1554919 := bstep (se 1 (by rfl) ⟨1166189, by rfl⟩ : syracuseStep 1554919 = 2332379) B2332379
theorem B2333159 : Blo 1553474 2333159 := bstep (se 1 (by rfl) ⟨1749869, by rfl⟩ : syracuseStep 2333159 = 3499739) B3499739
theorem B1555035 : Blo 1553474 1555035 := bstep (se 1 (by rfl) ⟨1166276, by rfl⟩ : syracuseStep 1555035 = 2332553) B2332553
theorem B1555103 : Blo 1553474 1555103 := bstep (se 1 (by rfl) ⟨1166327, by rfl⟩ : syracuseStep 1555103 = 2332655) B2332655
theorem B1555271 : Blo 1553474 1555271 := bstep (se 1 (by rfl) ⟨1166453, by rfl⟩ : syracuseStep 1555271 = 2332907) B2332907
theorem B1555311 : Blo 1553474 1555311 := bstep (se 1 (by rfl) ⟨1166483, by rfl⟩ : syracuseStep 1555311 = 2332967) B2332967
theorem B9960317 : Blo 1553474 9960317 := bstep (se 3 (by rfl) ⟨1867559, by rfl⟩ : syracuseStep 9960317 = 3735119) B3735119
theorem B1555367 : Blo 1553474 1555367 := bstep (se 1 (by rfl) ⟨1166525, by rfl⟩ : syracuseStep 1555367 = 2333051) B2333051
theorem B1867483 : Blo 1553474 1867483 := bstep (se 1 (by rfl) ⟨1400612, by rfl⟩ : syracuseStep 1867483 = 2801225) B2801225
theorem B3497759 : Blo 1553474 3497759 := bstep (se 1 (by rfl) ⟨2623319, by rfl⟩ : syracuseStep 3497759 = 5246639) B5246639
theorem B7470929 : Blo 1553474 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B3497975 : Blo 1553474 3497975 := bstep (se 1 (by rfl) ⟨2623481, by rfl⟩ : syracuseStep 3497975 = 5246963) B5246963
theorem B5243129 : Blo 1553474 5243129 := bstep (se 2 (by rfl) ⟨1966173, by rfl⟩ : syracuseStep 5243129 = 3932347) B3932347
theorem B3498281 : Blo 1553474 3498281 := bstep (se 2 (by rfl) ⟨1311855, by rfl⟩ : syracuseStep 3498281 = 2623711) B2623711
theorem B5243291 : Blo 1553474 5243291 := bstep (se 1 (by rfl) ⟨3932468, by rfl⟩ : syracuseStep 5243291 = 7864937) B7864937
theorem B2621855 : Blo 1553474 2621855 := bstep (se 1 (by rfl) ⟨1966391, by rfl⟩ : syracuseStep 2621855 = 3932783) B3932783
theorem B1966619 : Blo 1553474 1966619 := bstep (se 1 (by rfl) ⟨1474964, by rfl⟩ : syracuseStep 1966619 = 2949929) B2949929
theorem B3498551 : Blo 1553474 3498551 := bstep (se 1 (by rfl) ⟨2623913, by rfl⟩ : syracuseStep 3498551 = 5247827) B5247827
theorem B5243507 : Blo 1553474 5243507 := bstep (se 1 (by rfl) ⟨3932630, by rfl⟩ : syracuseStep 5243507 = 7865261) B7865261
theorem B7873199 : Blo 1553474 7873199 := bstep (se 1 (by rfl) ⟨5904899, by rfl⟩ : syracuseStep 7873199 = 11809799) B11809799
theorem B7865099 : Blo 1553474 7865099 := bstep (se 1 (by rfl) ⟨5898824, by rfl⟩ : syracuseStep 7865099 = 11797649) B11797649
theorem B3498911 : Blo 1553474 3498911 := bstep (se 1 (by rfl) ⟨2624183, by rfl⟩ : syracuseStep 3498911 = 5248367) B5248367
theorem B17957867 : Blo 1553474 17957867 := bstep (se 1 (by rfl) ⟨13468400, by rfl⟩ : syracuseStep 17957867 = 26936801) B26936801
theorem B3318995 : Blo 1553474 3318995 := bstep (se 1 (by rfl) ⟨2489246, by rfl⟩ : syracuseStep 3318995 = 4978493) B4978493
theorem B3499343 : Blo 1553474 3499343 := bstep (se 1 (by rfl) ⟨2624507, by rfl⟩ : syracuseStep 3499343 = 5249015) B5249015
theorem B14173537 : Blo 1553474 14173537 := bstep (se 2 (by rfl) ⟨5315076, by rfl⟩ : syracuseStep 14173537 = 10630153) B10630153
theorem B3499433 : Blo 1553474 3499433 := bstep (se 2 (by rfl) ⟨1312287, by rfl⟩ : syracuseStep 3499433 = 2624575) B2624575
theorem B4982249 : Blo 1553474 4982249 := bstep (se 2 (by rfl) ⟨1868343, by rfl⟩ : syracuseStep 4982249 = 3736687) B3736687
theorem B7087607 : Blo 1553474 7087607 := bstep (se 1 (by rfl) ⟨5315705, by rfl⟩ : syracuseStep 7087607 = 10631411) B10631411
theorem B19916279 : Blo 1553474 19916279 := bstep (se 1 (by rfl) ⟨14937209, by rfl⟩ : syracuseStep 19916279 = 29874419) B29874419
theorem B33629741 : Blo 1553474 33629741 := bstep (se 3 (by rfl) ⟨6305576, by rfl⟩ : syracuseStep 33629741 = 12611153) B12611153
theorem B5244587 : Blo 1553474 5244587 := bstep (se 1 (by rfl) ⟨3933440, by rfl⟩ : syracuseStep 5244587 = 7866881) B7866881
theorem B44795591 : Blo 1553474 44795591 := bstep (se 1 (by rfl) ⟨33596693, by rfl⟩ : syracuseStep 44795591 = 67193387) B67193387
theorem B2950931 : Blo 1553474 2950931 := bstep (se 1 (by rfl) ⟨2213198, by rfl⟩ : syracuseStep 2950931 = 4426397) B4426397
theorem B7472969 : Blo 1553474 7472969 := bstep (se 2 (by rfl) ⟨2802363, by rfl⟩ : syracuseStep 7472969 = 5604727) B5604727
theorem B8972153 : Blo 1553474 8972153 := bstep (se 2 (by rfl) ⟨3364557, by rfl⟩ : syracuseStep 8972153 = 6729115) B6729115
theorem B2623529 : Blo 1553474 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B11667523 : Blo 1553474 11667523 := bstep (se 1 (by rfl) ⟨8750642, by rfl⟩ : syracuseStep 11667523 = 17501285) B17501285
theorem B3934291 : Blo 1553474 3934291 := bstep (se 1 (by rfl) ⟨2950718, by rfl⟩ : syracuseStep 3934291 = 5901437) B5901437
theorem B295020629 : Blo 1553474 295020629 := bstep (se 8 (by rfl) ⟨1728636, by rfl⟩ : syracuseStep 295020629 = 3457273) B3457273
theorem B2951311 : Blo 1553474 2951311 := bstep (se 1 (by rfl) ⟨2213483, by rfl⟩ : syracuseStep 2951311 = 4426967) B4426967
theorem B5245127 : Blo 1553474 5245127 := bstep (se 1 (by rfl) ⟨3933845, by rfl⟩ : syracuseStep 5245127 = 7867691) B7867691
theorem B7866719 : Blo 1553474 7866719 := bstep (se 1 (by rfl) ⟨5900039, by rfl⟩ : syracuseStep 7866719 = 11800079) B11800079
theorem B7473545 : Blo 1553474 7473545 := bstep (se 2 (by rfl) ⟨2802579, by rfl⟩ : syracuseStep 7473545 = 5605159) B5605159
theorem B9964417 : Blo 1553474 9964417 := bstep (se 2 (by rfl) ⟨3736656, by rfl⟩ : syracuseStep 9964417 = 7473313) B7473313
theorem B17705951 : Blo 1553474 17705951 := bstep (se 1 (by rfl) ⟨13279463, by rfl⟩ : syracuseStep 17705951 = 26558927) B26558927
theorem B9956627 : Blo 1553474 9956627 := bstep (se 1 (by rfl) ⟨7467470, by rfl⟩ : syracuseStep 9956627 = 14934941) B14934941
theorem B4427081 : Blo 1553474 4427081 := bstep (se 2 (by rfl) ⟨1660155, by rfl⟩ : syracuseStep 4427081 = 3320311) B3320311
theorem B3935699 : Blo 1553474 3935699 := bstep (se 1 (by rfl) ⟨2951774, by rfl⟩ : syracuseStep 3935699 = 5903549) B5903549
theorem B8850971 : Blo 1553474 8850971 := bstep (se 1 (by rfl) ⟨6638228, by rfl⟩ : syracuseStep 8850971 = 13276457) B13276457
theorem B8400473 : Blo 1553474 8400473 := bstep (se 2 (by rfl) ⟨3150177, by rfl⟩ : syracuseStep 8400473 = 6300355) B6300355
theorem B4427423 : Blo 1553474 4427423 := bstep (se 1 (by rfl) ⟨3320567, by rfl⟩ : syracuseStep 4427423 = 6641135) B6641135
theorem B2952929 : Blo 1553474 2952929 := bstep (se 2 (by rfl) ⟨1107348, by rfl⟩ : syracuseStep 2952929 = 2214697) B2214697
theorem B2330363 : Blo 1553474 2330363 := bstep (se 1 (by rfl) ⟨1747772, by rfl⟩ : syracuseStep 2330363 = 3495545) B3495545
theorem B5902105 : Blo 1553474 5902105 := bstep (se 2 (by rfl) ⟨2213289, by rfl⟩ : syracuseStep 5902105 = 4426579) B4426579
theorem B1748767 : Blo 1553474 1748767 := bstep (se 1 (by rfl) ⟨1311575, by rfl⟩ : syracuseStep 1748767 = 2623151) B2623151
theorem B403967893 : Blo 1553474 403967893 := bstep (se 6 (by rfl) ⟨9467997, by rfl⟩ : syracuseStep 403967893 = 18935995) B18935995
theorem B3936215 : Blo 1553474 3936215 := bstep (se 1 (by rfl) ⟨2952161, by rfl⟩ : syracuseStep 3936215 = 5904323) B5904323
theorem B13283291 : Blo 1553474 13283291 := bstep (se 1 (by rfl) ⟨9962468, by rfl⟩ : syracuseStep 13283291 = 19924937) B19924937
theorem B2330603 : Blo 1553474 2330603 := bstep (se 1 (by rfl) ⟨1747952, by rfl⟩ : syracuseStep 2330603 = 3495905) B3495905
theorem B3936347 : Blo 1553474 3936347 := bstep (se 1 (by rfl) ⟨2952260, by rfl⟩ : syracuseStep 3936347 = 5904521) B5904521
theorem B4976815 : Blo 1553474 4976815 := bstep (se 1 (by rfl) ⟨3732611, by rfl⟩ : syracuseStep 4976815 = 7465223) B7465223
theorem B7868663 : Blo 1553474 7868663 := bstep (se 1 (by rfl) ⟨5901497, by rfl⟩ : syracuseStep 7868663 = 11802995) B11802995
theorem B6640211 : Blo 1553474 6640211 := bstep (se 1 (by rfl) ⟨4980158, by rfl⟩ : syracuseStep 6640211 = 9960317) B9960317
theorem B2331641 : Blo 1553474 2331641 := bstep (se 2 (by rfl) ⟨874365, by rfl⟩ : syracuseStep 2331641 = 1748731) B1748731
theorem B2364409 : Blo 1553474 2364409 := bstep (se 2 (by rfl) ⟨886653, by rfl⟩ : syracuseStep 2364409 = 1773307) B1773307
theorem B2331839 : Blo 1553474 2331839 := bstep (se 1 (by rfl) ⟨1748879, by rfl⟩ : syracuseStep 2331839 = 3497759) B3497759
theorem B1553663 : Blo 1553474 1553663 := bstep (se 1 (by rfl) ⟨1165247, by rfl⟩ : syracuseStep 1553663 = 2330495) B2330495
theorem B2331983 : Blo 1553474 2331983 := bstep (se 1 (by rfl) ⟨1748987, by rfl⟩ : syracuseStep 2331983 = 3497975) B3497975
theorem B1553791 : Blo 1553474 1553791 := bstep (se 1 (by rfl) ⟨1165343, by rfl⟩ : syracuseStep 1553791 = 2330687) B2330687
theorem B2332073 : Blo 1553474 2332073 := bstep (se 2 (by rfl) ⟨874527, by rfl⟩ : syracuseStep 2332073 = 1749055) B1749055
theorem B2332127 : Blo 1553474 2332127 := bstep (se 1 (by rfl) ⟨1749095, by rfl⟩ : syracuseStep 2332127 = 3498191) B3498191
theorem B1553947 : Blo 1553474 1553947 := bstep (se 1 (by rfl) ⟨1165460, by rfl⟩ : syracuseStep 1553947 = 2330921) B2330921
theorem B3495455 : Blo 1553474 3495455 := bstep (se 1 (by rfl) ⟨2621591, by rfl⟩ : syracuseStep 3495455 = 5243183) B5243183
theorem B2332223 : Blo 1553474 2332223 := bstep (se 1 (by rfl) ⟨1749167, by rfl⟩ : syracuseStep 2332223 = 3498335) B3498335
theorem B33601189 : Blo 1553474 33601189 := bstep (se 4 (by rfl) ⟨3150111, by rfl⟩ : syracuseStep 33601189 = 6300223) B6300223
theorem B1554127 : Blo 1553474 1554127 := bstep (se 1 (by rfl) ⟨1165595, by rfl⟩ : syracuseStep 1554127 = 2331191) B2331191
theorem B1554367 : Blo 1553474 1554367 := bstep (se 1 (by rfl) ⟨1165775, by rfl⟩ : syracuseStep 1554367 = 2331551) B2331551
theorem B2332703 : Blo 1553474 2332703 := bstep (se 1 (by rfl) ⟨1749527, by rfl⟩ : syracuseStep 2332703 = 3499055) B3499055
theorem B3495977 : Blo 1553474 3495977 := bstep (se 2 (by rfl) ⟨1310991, by rfl⟩ : syracuseStep 3495977 = 2621983) B2621983
theorem B1554495 : Blo 1553474 1554495 := bstep (se 1 (by rfl) ⟨1165871, by rfl⟩ : syracuseStep 1554495 = 2331743) B2331743
theorem B1554535 : Blo 1553474 1554535 := bstep (se 1 (by rfl) ⟨1165901, by rfl⟩ : syracuseStep 1554535 = 2331803) B2331803
theorem B6641851 : Blo 1553474 6641851 := bstep (se 1 (by rfl) ⟨4981388, by rfl⟩ : syracuseStep 6641851 = 9962777) B9962777
theorem B76667123 : Blo 1553474 76667123 := bstep (se 1 (by rfl) ⟨57500342, by rfl⟩ : syracuseStep 76667123 = 115000685) B115000685
theorem B14563613 : Blo 1553474 14563613 := bstep (se 3 (by rfl) ⟨2730677, by rfl⟩ : syracuseStep 14563613 = 5461355) B5461355
theorem B17717615 : Blo 1553474 17717615 := bstep (se 1 (by rfl) ⟨13288211, by rfl⟩ : syracuseStep 17717615 = 26576423) B26576423
theorem B2333135 : Blo 1553474 2333135 := bstep (se 1 (by rfl) ⟨1749851, by rfl⟩ : syracuseStep 2333135 = 3499703) B3499703
theorem B1554991 : Blo 1553474 1554991 := bstep (se 1 (by rfl) ⟨1166243, by rfl⟩ : syracuseStep 1554991 = 2332487) B2332487
theorem B3496607 : Blo 1553474 3496607 := bstep (se 1 (by rfl) ⟨2622455, by rfl⟩ : syracuseStep 3496607 = 5244911) B5244911
theorem B1555391 : Blo 1553474 1555391 := bstep (se 1 (by rfl) ⟨1166543, by rfl⟩ : syracuseStep 1555391 = 2333087) B2333087
theorem B1555439 : Blo 1553474 1555439 := bstep (se 1 (by rfl) ⟨1166579, by rfl⟩ : syracuseStep 1555439 = 2333159) B2333159
theorem B6642809 : Blo 1553474 6642809 := bstep (se 2 (by rfl) ⟨2491053, by rfl⟩ : syracuseStep 6642809 = 4982107) B4982107
theorem B5758087 : Blo 1553474 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B25214129 : Blo 1553474 25214129 := bstep (se 2 (by rfl) ⟨9455298, by rfl⟩ : syracuseStep 25214129 = 18910597) B18910597
theorem B8085055 : Blo 1553474 8085055 := bstep (se 1 (by rfl) ⟨6063791, by rfl⟩ : syracuseStep 8085055 = 12127583) B12127583
theorem B100851317 : Blo 1553474 100851317 := bstep (se 5 (by rfl) ⟨4727405, by rfl⟩ : syracuseStep 100851317 = 9454811) B9454811
theorem B2489977 : Blo 1553474 2489977 := bstep (se 2 (by rfl) ⟨933741, by rfl⟩ : syracuseStep 2489977 = 1867483) B1867483
theorem B20201309 : Blo 1553474 20201309 := bstep (se 3 (by rfl) ⟨3787745, by rfl⟩ : syracuseStep 20201309 = 7575491) B7575491
theorem B4980619 : Blo 1553474 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B15556697 : Blo 1553474 15556697 := bstep (se 2 (by rfl) ⟨5833761, by rfl⟩ : syracuseStep 15556697 = 11667523) B11667523
theorem B6635753 : Blo 1553474 6635753 := bstep (se 2 (by rfl) ⟨2488407, by rfl⟩ : syracuseStep 6635753 = 4976815) B4976815
theorem B8855801 : Blo 1553474 8855801 := bstep (se 2 (by rfl) ⟨3320925, by rfl⟩ : syracuseStep 8855801 = 6641851) B6641851
theorem B5243399 : Blo 1553474 5243399 := bstep (se 1 (by rfl) ⟨3932549, by rfl⟩ : syracuseStep 5243399 = 7865099) B7865099
theorem B4981979 : Blo 1553474 4981979 := bstep (se 1 (by rfl) ⟨3736484, by rfl⟩ : syracuseStep 4981979 = 7472969) B7472969
theorem B5981435 : Blo 1553474 5981435 := bstep (se 1 (by rfl) ⟨4486076, by rfl⟩ : syracuseStep 5981435 = 8972153) B8972153
theorem B5244317 : Blo 1553474 5244317 := bstep (se 3 (by rfl) ⟨983309, by rfl⟩ : syracuseStep 5244317 = 1966619) B1966619
theorem B51111415 : Blo 1553474 51111415 := bstep (se 1 (by rfl) ⟨38333561, by rfl⟩ : syracuseStep 51111415 = 76667123) B76667123
theorem B7677449 : Blo 1553474 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B9709075 : Blo 1553474 9709075 := bstep (se 1 (by rfl) ⟨7281806, by rfl⟩ : syracuseStep 9709075 = 14563613) B14563613
theorem B5244479 : Blo 1553474 5244479 := bstep (se 1 (by rfl) ⟨3933359, by rfl⟩ : syracuseStep 5244479 = 7866719) B7866719
theorem B4982363 : Blo 1553474 4982363 := bstep (se 1 (by rfl) ⟨3736772, by rfl⟩ : syracuseStep 4982363 = 7473545) B7473545
theorem B3319969 : Blo 1553474 3319969 := bstep (se 2 (by rfl) ⟨1244988, by rfl⟩ : syracuseStep 3319969 = 2489977) B2489977
theorem B6637751 : Blo 1553474 6637751 := bstep (se 1 (by rfl) ⟨4978313, by rfl⟩ : syracuseStep 6637751 = 9956627) B9956627
theorem B2951387 : Blo 1553474 2951387 := bstep (se 1 (by rfl) ⟨2213540, by rfl⟩ : syracuseStep 2951387 = 4427081) B4427081
theorem B2623799 : Blo 1553474 2623799 := bstep (se 1 (by rfl) ⟨1967849, by rfl⟩ : syracuseStep 2623799 = 3935699) B3935699
theorem B5900647 : Blo 1553474 5900647 := bstep (se 1 (by rfl) ⟨4425485, by rfl⟩ : syracuseStep 5900647 = 8850971) B8850971
theorem B67234211 : Blo 1553474 67234211 := bstep (se 1 (by rfl) ⟨50425658, by rfl⟩ : syracuseStep 67234211 = 100851317) B100851317
theorem B2951615 : Blo 1553474 2951615 := bstep (se 1 (by rfl) ⟨2213711, by rfl⟩ : syracuseStep 2951615 = 4427423) B4427423
theorem B1968619 : Blo 1553474 1968619 := bstep (se 1 (by rfl) ⟨1476464, by rfl⟩ : syracuseStep 1968619 = 2952929) B2952929
theorem B12610181 : Blo 1553474 12610181 := bstep (se 4 (by rfl) ⟨1182204, by rfl⟩ : syracuseStep 12610181 = 2364409) B2364409
theorem B2624143 : Blo 1553474 2624143 := bstep (se 1 (by rfl) ⟨1968107, by rfl⟩ : syracuseStep 2624143 = 3936215) B3936215
theorem B2624231 : Blo 1553474 2624231 := bstep (se 1 (by rfl) ⟨1968173, by rfl⟩ : syracuseStep 2624231 = 3936347) B3936347
theorem B5245721 : Blo 1553474 5245721 := bstep (se 2 (by rfl) ⟨1967145, by rfl⟩ : syracuseStep 5245721 = 3934291) B3934291
theorem B5245775 : Blo 1553474 5245775 := bstep (se 1 (by rfl) ⟨3934331, by rfl⟩ : syracuseStep 5245775 = 7868663) B7868663
theorem B3935081 : Blo 1553474 3935081 := bstep (se 2 (by rfl) ⟨1475655, by rfl⟩ : syracuseStep 3935081 = 2951311) B2951311
theorem B1747903 : Blo 1553474 1747903 := bstep (se 1 (by rfl) ⟨1310927, by rfl⟩ : syracuseStep 1747903 = 2621855) B2621855
theorem B4426807 : Blo 1553474 4426807 := bstep (se 1 (by rfl) ⟨3320105, by rfl⟩ : syracuseStep 4426807 = 6640211) B6640211
theorem B8850653 : Blo 1553474 8850653 := bstep (se 3 (by rfl) ⟨1659497, by rfl⟩ : syracuseStep 8850653 = 3318995) B3318995
theorem B3321499 : Blo 1553474 3321499 := bstep (se 1 (by rfl) ⟨2491124, by rfl⟩ : syracuseStep 3321499 = 4982249) B4982249
theorem B2330303 : Blo 1553474 2330303 := bstep (se 1 (by rfl) ⟨1747727, by rfl⟩ : syracuseStep 2330303 = 3495455) B3495455
theorem B29863727 : Blo 1553474 29863727 := bstep (se 1 (by rfl) ⟨22397795, by rfl⟩ : syracuseStep 29863727 = 44795591) B44795591
theorem B2330651 : Blo 1553474 2330651 := bstep (se 1 (by rfl) ⟨1747988, by rfl⟩ : syracuseStep 2330651 = 3495977) B3495977
theorem B1749019 : Blo 1553474 1749019 := bstep (se 1 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 1749019 = 2623529) B2623529
theorem B2331071 : Blo 1553474 2331071 := bstep (se 1 (by rfl) ⟨1748303, by rfl⟩ : syracuseStep 2331071 = 3496607) B3496607
theorem B7869149 : Blo 1553474 7869149 := bstep (se 3 (by rfl) ⟨1475465, by rfl⟩ : syracuseStep 7869149 = 2950931) B2950931
theorem B26563301 : Blo 1553474 26563301 := bstep (se 4 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 26563301 = 4980619) B4980619
theorem B4428539 : Blo 1553474 4428539 := bstep (se 1 (by rfl) ⟨3321404, by rfl⟩ : syracuseStep 4428539 = 6642809) B6642809
theorem B7869473 : Blo 1553474 7869473 := bstep (se 2 (by rfl) ⟨2951052, by rfl⟩ : syracuseStep 7869473 = 5902105) B5902105
theorem B2331689 : Blo 1553474 2331689 := bstep (se 2 (by rfl) ⟨874383, by rfl⟩ : syracuseStep 2331689 = 1748767) B1748767
theorem B5600315 : Blo 1553474 5600315 := bstep (se 1 (by rfl) ⟨4200236, by rfl⟩ : syracuseStep 5600315 = 8400473) B8400473
theorem B191550581 : Blo 1553474 191550581 := bstep (se 5 (by rfl) ⟨8978933, by rfl⟩ : syracuseStep 191550581 = 17957867) B17957867
theorem B1553575 : Blo 1553474 1553575 := bstep (se 1 (by rfl) ⟨1165181, by rfl⟩ : syracuseStep 1553575 = 2330363) B2330363
theorem B1553735 : Blo 1553474 1553735 := bstep (se 1 (by rfl) ⟨1165301, by rfl⟩ : syracuseStep 1553735 = 2330603) B2330603
theorem B3495419 : Blo 1553474 3495419 := bstep (se 1 (by rfl) ⟨2621564, by rfl⟩ : syracuseStep 3495419 = 5243129) B5243129
theorem B2332187 : Blo 1553474 2332187 := bstep (se 1 (by rfl) ⟨1749140, by rfl⟩ : syracuseStep 2332187 = 3498281) B3498281
theorem B3495527 : Blo 1553474 3495527 := bstep (se 1 (by rfl) ⟨2621645, by rfl⟩ : syracuseStep 3495527 = 5243291) B5243291
theorem B2332367 : Blo 1553474 2332367 := bstep (se 1 (by rfl) ⟨1749275, by rfl⟩ : syracuseStep 2332367 = 3498551) B3498551
theorem B3495671 : Blo 1553474 3495671 := bstep (se 1 (by rfl) ⟨2621753, by rfl⟩ : syracuseStep 3495671 = 5243507) B5243507
theorem B5248799 : Blo 1553474 5248799 := bstep (se 1 (by rfl) ⟨3936599, by rfl⟩ : syracuseStep 5248799 = 7873199) B7873199
theorem B2332607 : Blo 1553474 2332607 := bstep (se 1 (by rfl) ⟨1749455, by rfl⟩ : syracuseStep 2332607 = 3498911) B3498911
theorem B1554427 : Blo 1553474 1554427 := bstep (se 1 (by rfl) ⟨1165820, by rfl⟩ : syracuseStep 1554427 = 2331641) B2331641
theorem B1554559 : Blo 1553474 1554559 := bstep (se 1 (by rfl) ⟨1165919, by rfl⟩ : syracuseStep 1554559 = 2331839) B2331839
theorem B1554655 : Blo 1553474 1554655 := bstep (se 1 (by rfl) ⟨1165991, by rfl⟩ : syracuseStep 1554655 = 2331983) B2331983
theorem B2332895 : Blo 1553474 2332895 := bstep (se 1 (by rfl) ⟨1749671, by rfl⟩ : syracuseStep 2332895 = 3499343) B3499343
theorem B1554715 : Blo 1553474 1554715 := bstep (se 1 (by rfl) ⟨1166036, by rfl⟩ : syracuseStep 1554715 = 2332073) B2332073
theorem B2332955 : Blo 1553474 2332955 := bstep (se 1 (by rfl) ⟨1749716, by rfl⟩ : syracuseStep 2332955 = 3499433) B3499433
theorem B1554751 : Blo 1553474 1554751 := bstep (se 1 (by rfl) ⟨1166063, by rfl⟩ : syracuseStep 1554751 = 2332127) B2332127
theorem B4725071 : Blo 1553474 4725071 := bstep (se 1 (by rfl) ⟨3543803, by rfl⟩ : syracuseStep 4725071 = 7087607) B7087607
theorem B13277519 : Blo 1553474 13277519 := bstep (se 1 (by rfl) ⟨9958139, by rfl⟩ : syracuseStep 13277519 = 19916279) B19916279
theorem B22419827 : Blo 1553474 22419827 := bstep (se 1 (by rfl) ⟨16814870, by rfl⟩ : syracuseStep 22419827 = 33629741) B33629741
theorem B1554815 : Blo 1553474 1554815 := bstep (se 1 (by rfl) ⟨1166111, by rfl⟩ : syracuseStep 1554815 = 2332223) B2332223
theorem B3496391 : Blo 1553474 3496391 := bstep (se 1 (by rfl) ⟨2622293, by rfl⟩ : syracuseStep 3496391 = 5244587) B5244587
theorem B13285889 : Blo 1553474 13285889 := bstep (se 2 (by rfl) ⟨4982208, by rfl⟩ : syracuseStep 13285889 = 9964417) B9964417
theorem B1555135 : Blo 1553474 1555135 := bstep (se 1 (by rfl) ⟨1166351, by rfl⟩ : syracuseStep 1555135 = 2332703) B2332703
theorem B196680419 : Blo 1553474 196680419 := bstep (se 1 (by rfl) ⟨147510314, by rfl⟩ : syracuseStep 196680419 = 295020629) B295020629
theorem B3496751 : Blo 1553474 3496751 := bstep (se 1 (by rfl) ⟨2622563, by rfl⟩ : syracuseStep 3496751 = 5245127) B5245127
theorem B11811743 : Blo 1553474 11811743 := bstep (se 1 (by rfl) ⟨8858807, by rfl⟩ : syracuseStep 11811743 = 17717615) B17717615
theorem B1555423 : Blo 1553474 1555423 := bstep (se 1 (by rfl) ⟨1166567, by rfl⟩ : syracuseStep 1555423 = 2333135) B2333135
theorem B18898049 : Blo 1553474 18898049 := bstep (se 2 (by rfl) ⟨7086768, by rfl⟩ : syracuseStep 18898049 = 14173537) B14173537
theorem B11803967 : Blo 1553474 11803967 := bstep (se 1 (by rfl) ⟨8852975, by rfl⟩ : syracuseStep 11803967 = 17705951) B17705951
theorem B10780073 : Blo 1553474 10780073 := bstep (se 2 (by rfl) ⟨4042527, by rfl⟩ : syracuseStep 10780073 = 8085055) B8085055
theorem B16809419 : Blo 1553474 16809419 := bstep (se 1 (by rfl) ⟨12607064, by rfl⟩ : syracuseStep 16809419 = 25214129) B25214129
theorem B44801585 : Blo 1553474 44801585 := bstep (se 2 (by rfl) ⟨16800594, by rfl⟩ : syracuseStep 44801585 = 33601189) B33601189
theorem B538623857 : Blo 1553474 538623857 := bstep (se 2 (by rfl) ⟨201983946, by rfl⟩ : syracuseStep 538623857 = 403967893) B403967893
theorem B13467539 : Blo 1553474 13467539 := bstep (se 1 (by rfl) ⟨10100654, by rfl⟩ : syracuseStep 13467539 = 20201309) B20201309
theorem B8855527 : Blo 1553474 8855527 := bstep (se 1 (by rfl) ⟨6641645, by rfl⟩ : syracuseStep 8855527 = 13283291) B13283291
theorem B10371131 : Blo 1553474 10371131 := bstep (se 1 (by rfl) ⟨7778348, by rfl⟩ : syracuseStep 10371131 = 15556697) B15556697
theorem B51781733 : Blo 1553474 51781733 := bstep (se 4 (by rfl) ⟨4854537, by rfl⟩ : syracuseStep 51781733 = 9709075) B9709075
theorem B4423835 : Blo 1553474 4423835 := bstep (se 1 (by rfl) ⟨3317876, by rfl⟩ : syracuseStep 4423835 = 6635753) B6635753
theorem B3498857 : Blo 1553474 3498857 := bstep (se 2 (by rfl) ⟨1312071, by rfl⟩ : syracuseStep 3498857 = 2624143) B2624143
theorem B3499199 : Blo 1553474 3499199 := bstep (se 1 (by rfl) ⟨2624399, by rfl⟩ : syracuseStep 3499199 = 5248799) B5248799
theorem B4425167 : Blo 1553474 4425167 := bstep (se 1 (by rfl) ⟨3318875, by rfl⟩ : syracuseStep 4425167 = 6637751) B6637751
theorem B1967591 : Blo 1553474 1967591 := bstep (se 1 (by rfl) ⟨1475693, by rfl⟩ : syracuseStep 1967591 = 2951387) B2951387
theorem B1967743 : Blo 1553474 1967743 := bstep (se 1 (by rfl) ⟨1475807, by rfl⟩ : syracuseStep 1967743 = 2951615) B2951615
theorem B8857259 : Blo 1553474 8857259 := bstep (se 1 (by rfl) ⟨6642944, by rfl⟩ : syracuseStep 8857259 = 13285889) B13285889
theorem B8406787 : Blo 1553474 8406787 := bstep (se 1 (by rfl) ⟨6305090, by rfl⟩ : syracuseStep 8406787 = 12610181) B12610181
theorem B2623387 : Blo 1553474 2623387 := bstep (se 1 (by rfl) ⟨1967540, by rfl⟩ : syracuseStep 2623387 = 3935081) B3935081
theorem B7874495 : Blo 1553474 7874495 := bstep (se 1 (by rfl) ⟨5905871, by rfl⟩ : syracuseStep 7874495 = 11811743) B11811743
theorem B5900435 : Blo 1553474 5900435 := bstep (se 1 (by rfl) ⟨4425326, by rfl⟩ : syracuseStep 5900435 = 8850653) B8850653
theorem B7186715 : Blo 1553474 7186715 := bstep (se 1 (by rfl) ⟨5390036, by rfl⟩ : syracuseStep 7186715 = 10780073) B10780073
theorem B19909151 : Blo 1553474 19909151 := bstep (se 1 (by rfl) ⟨14931863, by rfl⟩ : syracuseStep 19909151 = 29863727) B29863727
theorem B359082571 : Blo 1553474 359082571 := bstep (se 1 (by rfl) ⟨269311928, by rfl⟩ : syracuseStep 359082571 = 538623857) B538623857
theorem B11807369 : Blo 1553474 11807369 := bstep (se 2 (by rfl) ⟨4427763, by rfl⟩ : syracuseStep 11807369 = 8855527) B8855527
theorem B4426625 : Blo 1553474 4426625 := bstep (se 2 (by rfl) ⟨1659984, by rfl⟩ : syracuseStep 4426625 = 3319969) B3319969
theorem B7867529 : Blo 1553474 7867529 := bstep (se 2 (by rfl) ⟨2950323, by rfl⟩ : syracuseStep 7867529 = 5900647) B5900647
theorem B5246099 : Blo 1553474 5246099 := bstep (se 1 (by rfl) ⟨3934574, by rfl⟩ : syracuseStep 5246099 = 7869149) B7869149
theorem B2952359 : Blo 1553474 2952359 := bstep (se 1 (by rfl) ⟨2214269, by rfl⟩ : syracuseStep 2952359 = 4428539) B4428539
theorem B2624825 : Blo 1553474 2624825 := bstep (se 2 (by rfl) ⟨984309, by rfl⟩ : syracuseStep 2624825 = 1968619) B1968619
theorem B5246315 : Blo 1553474 5246315 := bstep (se 1 (by rfl) ⟨3934736, by rfl⟩ : syracuseStep 5246315 = 7869473) B7869473
theorem B127700387 : Blo 1553474 127700387 := bstep (se 1 (by rfl) ⟨95775290, by rfl⟩ : syracuseStep 127700387 = 191550581) B191550581
theorem B3321319 : Blo 1553474 3321319 := bstep (se 1 (by rfl) ⟨2490989, by rfl⟩ : syracuseStep 3321319 = 4981979) B4981979
theorem B2330279 : Blo 1553474 2330279 := bstep (se 1 (by rfl) ⟨1747709, by rfl⟩ : syracuseStep 2330279 = 3495419) B3495419
theorem B3321575 : Blo 1553474 3321575 := bstep (se 1 (by rfl) ⟨2491181, by rfl⟩ : syracuseStep 3321575 = 4982363) B4982363
theorem B2330351 : Blo 1553474 2330351 := bstep (se 1 (by rfl) ⟨1747763, by rfl⟩ : syracuseStep 2330351 = 3495527) B3495527
theorem B2330447 : Blo 1553474 2330447 := bstep (se 1 (by rfl) ⟨1747835, by rfl⟩ : syracuseStep 2330447 = 3495671) B3495671
theorem B2330537 : Blo 1553474 2330537 := bstep (se 2 (by rfl) ⟨873951, by rfl⟩ : syracuseStep 2330537 = 1747903) B1747903
theorem B5902409 : Blo 1553474 5902409 := bstep (se 2 (by rfl) ⟨2213403, by rfl⟩ : syracuseStep 5902409 = 4426807) B4426807
theorem B1749199 : Blo 1553474 1749199 := bstep (se 1 (by rfl) ⟨1311899, by rfl⟩ : syracuseStep 1749199 = 2623799) B2623799
theorem B3150047 : Blo 1553474 3150047 := bstep (se 1 (by rfl) ⟨2362535, by rfl⟩ : syracuseStep 3150047 = 4725071) B4725071
theorem B8851679 : Blo 1553474 8851679 := bstep (se 1 (by rfl) ⟨6638759, by rfl⟩ : syracuseStep 8851679 = 13277519) B13277519
theorem B14946551 : Blo 1553474 14946551 := bstep (se 1 (by rfl) ⟨11209913, by rfl⟩ : syracuseStep 14946551 = 22419827) B22419827
theorem B44822807 : Blo 1553474 44822807 := bstep (se 1 (by rfl) ⟨33617105, by rfl⟩ : syracuseStep 44822807 = 67234211) B67234211
theorem B2330927 : Blo 1553474 2330927 := bstep (se 1 (by rfl) ⟨1748195, by rfl⟩ : syracuseStep 2330927 = 3496391) B3496391
theorem B1749487 : Blo 1553474 1749487 := bstep (se 1 (by rfl) ⟨1312115, by rfl⟩ : syracuseStep 1749487 = 2624231) B2624231
theorem B2331167 : Blo 1553474 2331167 := bstep (se 1 (by rfl) ⟨1748375, by rfl⟩ : syracuseStep 2331167 = 3496751) B3496751
theorem B4428665 : Blo 1553474 4428665 := bstep (se 2 (by rfl) ⟨1660749, by rfl⟩ : syracuseStep 4428665 = 3321499) B3321499
theorem B7869311 : Blo 1553474 7869311 := bstep (se 1 (by rfl) ⟨5901983, by rfl⟩ : syracuseStep 7869311 = 11803967) B11803967
theorem B1553535 : Blo 1553474 1553535 := bstep (se 1 (by rfl) ⟨1165151, by rfl⟩ : syracuseStep 1553535 = 2330303) B2330303
theorem B1553767 : Blo 1553474 1553767 := bstep (se 1 (by rfl) ⟨1165325, by rfl⟩ : syracuseStep 1553767 = 2330651) B2330651
theorem B2332025 : Blo 1553474 2332025 := bstep (se 2 (by rfl) ⟨874509, by rfl⟩ : syracuseStep 2332025 = 1749019) B1749019
theorem B5903867 : Blo 1553474 5903867 := bstep (se 1 (by rfl) ⟨4427900, by rfl⟩ : syracuseStep 5903867 = 8855801) B8855801
theorem B1554047 : Blo 1553474 1554047 := bstep (se 1 (by rfl) ⟨1165535, by rfl⟩ : syracuseStep 1554047 = 2331071) B2331071
theorem B3495599 : Blo 1553474 3495599 := bstep (se 1 (by rfl) ⟨2621699, by rfl⟩ : syracuseStep 3495599 = 5243399) B5243399
theorem B17708867 : Blo 1553474 17708867 := bstep (se 1 (by rfl) ⟨13281650, by rfl⟩ : syracuseStep 17708867 = 26563301) B26563301
theorem B1554459 : Blo 1553474 1554459 := bstep (se 1 (by rfl) ⟨1165844, by rfl⟩ : syracuseStep 1554459 = 2331689) B2331689
theorem B3733543 : Blo 1553474 3733543 := bstep (se 1 (by rfl) ⟨2800157, by rfl⟩ : syracuseStep 3733543 = 5600315) B5600315
theorem B3987623 : Blo 1553474 3987623 := bstep (se 1 (by rfl) ⟨2990717, by rfl⟩ : syracuseStep 3987623 = 5981435) B5981435
theorem B3496211 : Blo 1553474 3496211 := bstep (se 1 (by rfl) ⟨2622158, by rfl⟩ : syracuseStep 3496211 = 5244317) B5244317
theorem B5118299 : Blo 1553474 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B1554791 : Blo 1553474 1554791 := bstep (se 1 (by rfl) ⟨1166093, by rfl⟩ : syracuseStep 1554791 = 2332187) B2332187
theorem B3496319 : Blo 1553474 3496319 := bstep (se 1 (by rfl) ⟨2622239, by rfl⟩ : syracuseStep 3496319 = 5244479) B5244479
theorem B1554911 : Blo 1553474 1554911 := bstep (se 1 (by rfl) ⟨1166183, by rfl⟩ : syracuseStep 1554911 = 2332367) B2332367
theorem B1555071 : Blo 1553474 1555071 := bstep (se 1 (by rfl) ⟨1166303, by rfl⟩ : syracuseStep 1555071 = 2332607) B2332607
theorem B1555263 : Blo 1553474 1555263 := bstep (se 1 (by rfl) ⟨1166447, by rfl⟩ : syracuseStep 1555263 = 2332895) B2332895
theorem B1555303 : Blo 1553474 1555303 := bstep (se 1 (by rfl) ⟨1166477, by rfl⟩ : syracuseStep 1555303 = 2332955) B2332955
theorem B131120279 : Blo 1553474 131120279 := bstep (se 1 (by rfl) ⟨98340209, by rfl⟩ : syracuseStep 131120279 = 196680419) B196680419
theorem B3497147 : Blo 1553474 3497147 := bstep (se 1 (by rfl) ⟨2622860, by rfl⟩ : syracuseStep 3497147 = 5245721) B5245721
theorem B3497183 : Blo 1553474 3497183 := bstep (se 1 (by rfl) ⟨2622887, by rfl⟩ : syracuseStep 3497183 = 5245775) B5245775
theorem B68148553 : Blo 1553474 68148553 := bstep (se 2 (by rfl) ⟨25555707, by rfl⟩ : syracuseStep 68148553 = 51111415) B51111415
theorem B12598699 : Blo 1553474 12598699 := bstep (se 1 (by rfl) ⟨9449024, by rfl⟩ : syracuseStep 12598699 = 18898049) B18898049
theorem B11206279 : Blo 1553474 11206279 := bstep (se 1 (by rfl) ⟨8404709, by rfl⟩ : syracuseStep 11206279 = 16809419) B16809419
theorem B29867723 : Blo 1553474 29867723 := bstep (se 1 (by rfl) ⟨22400792, by rfl⟩ : syracuseStep 29867723 = 44801585) B44801585
theorem B8978359 : Blo 1553474 8978359 := bstep (se 1 (by rfl) ⟨6733769, by rfl⟩ : syracuseStep 8978359 = 13467539) B13467539
theorem B6914087 : Blo 1553474 6914087 := bstep (se 1 (by rfl) ⟨5185565, by rfl⟩ : syracuseStep 6914087 = 10371131) B10371131
theorem B34521155 : Blo 1553474 34521155 := bstep (se 1 (by rfl) ⟨25890866, by rfl⟩ : syracuseStep 34521155 = 51781733) B51781733
theorem B2949223 : Blo 1553474 2949223 := bstep (se 1 (by rfl) ⟨2211917, by rfl⟩ : syracuseStep 2949223 = 4423835) B4423835
theorem B2950111 : Blo 1553474 2950111 := bstep (se 1 (by rfl) ⟨2212583, by rfl⟩ : syracuseStep 2950111 = 4425167) B4425167
theorem B11805911 : Blo 1553474 11805911 := bstep (se 1 (by rfl) ⟨8854433, by rfl⟩ : syracuseStep 11805911 = 17708867) B17708867
theorem B3933623 : Blo 1553474 3933623 := bstep (se 1 (by rfl) ⟨2950217, by rfl⟩ : syracuseStep 3933623 = 5900435) B5900435
theorem B13272767 : Blo 1553474 13272767 := bstep (se 1 (by rfl) ⟨9954575, by rfl⟩ : syracuseStep 13272767 = 19909151) B19909151
theorem B2951083 : Blo 1553474 2951083 := bstep (se 1 (by rfl) ⟨2213312, by rfl⟩ : syracuseStep 2951083 = 4426625) B4426625
theorem B5245019 : Blo 1553474 5245019 := bstep (se 1 (by rfl) ⟨3933764, by rfl⟩ : syracuseStep 5245019 = 7867529) B7867529
theorem B1968239 : Blo 1553474 1968239 := bstep (se 1 (by rfl) ⟨1476179, by rfl⟩ : syracuseStep 1968239 = 2952359) B2952359
theorem B2623657 : Blo 1553474 2623657 := bstep (se 2 (by rfl) ⟨983871, by rfl⟩ : syracuseStep 2623657 = 1967743) B1967743
theorem B85133591 : Blo 1553474 85133591 := bstep (se 1 (by rfl) ⟨63850193, by rfl⟩ : syracuseStep 85133591 = 127700387) B127700387
theorem B11209049 : Blo 1553474 11209049 := bstep (se 2 (by rfl) ⟨4203393, by rfl⟩ : syracuseStep 11209049 = 8406787) B8406787
theorem B2214383 : Blo 1553474 2214383 := bstep (se 1 (by rfl) ⟨1660787, by rfl⟩ : syracuseStep 2214383 = 3321575) B3321575
theorem B11971145 : Blo 1553474 11971145 := bstep (se 2 (by rfl) ⟨4489179, by rfl⟩ : syracuseStep 11971145 = 8978359) B8978359
theorem B3934939 : Blo 1553474 3934939 := bstep (se 1 (by rfl) ⟨2951204, by rfl⟩ : syracuseStep 3934939 = 5902409) B5902409
theorem B5901119 : Blo 1553474 5901119 := bstep (se 1 (by rfl) ⟨4425839, by rfl⟩ : syracuseStep 5901119 = 8851679) B8851679
theorem B9964367 : Blo 1553474 9964367 := bstep (se 1 (by rfl) ⟨7473275, by rfl⟩ : syracuseStep 9964367 = 14946551) B14946551
theorem B2952443 : Blo 1553474 2952443 := bstep (se 1 (by rfl) ⟨2214332, by rfl⟩ : syracuseStep 2952443 = 4428665) B4428665
theorem B8400125 : Blo 1553474 8400125 := bstep (se 3 (by rfl) ⟨1575023, by rfl⟩ : syracuseStep 8400125 = 3150047) B3150047
theorem B5246207 : Blo 1553474 5246207 := bstep (se 1 (by rfl) ⟨3934655, by rfl⟩ : syracuseStep 5246207 = 7869311) B7869311
theorem B478776761 : Blo 1553474 478776761 := bstep (se 2 (by rfl) ⟨179541285, by rfl⟩ : syracuseStep 478776761 = 359082571) B359082571
theorem B3935911 : Blo 1553474 3935911 := bstep (se 1 (by rfl) ⟨2951933, by rfl⟩ : syracuseStep 3935911 = 5903867) B5903867
theorem B2330399 : Blo 1553474 2330399 := bstep (se 1 (by rfl) ⟨1747799, by rfl⟩ : syracuseStep 2330399 = 3495599) B3495599
theorem B5246909 : Blo 1553474 5246909 := bstep (se 3 (by rfl) ⟨983795, by rfl⟩ : syracuseStep 5246909 = 1967591) B1967591
theorem B2658415 : Blo 1553474 2658415 := bstep (se 1 (by rfl) ⟨1993811, by rfl⟩ : syracuseStep 2658415 = 3987623) B3987623
theorem B2330807 : Blo 1553474 2330807 := bstep (se 1 (by rfl) ⟨1748105, by rfl⟩ : syracuseStep 2330807 = 3496211) B3496211
theorem B3412199 : Blo 1553474 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B2330879 : Blo 1553474 2330879 := bstep (se 1 (by rfl) ⟨1748159, by rfl⟩ : syracuseStep 2330879 = 3496319) B3496319
theorem B16798265 : Blo 1553474 16798265 := bstep (se 2 (by rfl) ⟨6299349, by rfl⟩ : syracuseStep 16798265 = 12598699) B12598699
theorem B4428425 : Blo 1553474 4428425 := bstep (se 2 (by rfl) ⟨1660659, by rfl⟩ : syracuseStep 4428425 = 3321319) B3321319
theorem B87413519 : Blo 1553474 87413519 := bstep (se 1 (by rfl) ⟨65560139, by rfl⟩ : syracuseStep 87413519 = 131120279) B131120279
theorem B2331431 : Blo 1553474 2331431 := bstep (se 1 (by rfl) ⟨1748573, by rfl⟩ : syracuseStep 2331431 = 3497147) B3497147
theorem B2331455 : Blo 1553474 2331455 := bstep (se 1 (by rfl) ⟨1748591, by rfl⟩ : syracuseStep 2331455 = 3497183) B3497183
theorem B1749883 : Blo 1553474 1749883 := bstep (se 1 (by rfl) ⟨1312412, by rfl⟩ : syracuseStep 1749883 = 2624825) B2624825
theorem B1553519 : Blo 1553474 1553519 := bstep (se 1 (by rfl) ⟨1165139, by rfl⟩ : syracuseStep 1553519 = 2330279) B2330279
theorem B19911815 : Blo 1553474 19911815 := bstep (se 1 (by rfl) ⟨14933861, by rfl⟩ : syracuseStep 19911815 = 29867723) B29867723
theorem B1553567 : Blo 1553474 1553567 := bstep (se 1 (by rfl) ⟨1165175, by rfl⟩ : syracuseStep 1553567 = 2330351) B2330351
theorem B1553631 : Blo 1553474 1553631 := bstep (se 1 (by rfl) ⟨1165223, by rfl⟩ : syracuseStep 1553631 = 2330447) B2330447
theorem B1553691 : Blo 1553474 1553691 := bstep (se 1 (by rfl) ⟨1165268, by rfl⟩ : syracuseStep 1553691 = 2330537) B2330537
theorem B4978057 : Blo 1553474 4978057 := bstep (se 2 (by rfl) ⟨1866771, by rfl⟩ : syracuseStep 4978057 = 3733543) B3733543
theorem B29881871 : Blo 1553474 29881871 := bstep (se 1 (by rfl) ⟨22411403, by rfl⟩ : syracuseStep 29881871 = 44822807) B44822807
theorem B1553951 : Blo 1553474 1553951 := bstep (se 1 (by rfl) ⟨1165463, by rfl⟩ : syracuseStep 1553951 = 2330927) B2330927
theorem B2332265 : Blo 1553474 2332265 := bstep (se 2 (by rfl) ⟨874599, by rfl⟩ : syracuseStep 2332265 = 1749199) B1749199
theorem B1554111 : Blo 1553474 1554111 := bstep (se 1 (by rfl) ⟨1165583, by rfl⟩ : syracuseStep 1554111 = 2331167) B2331167
theorem B2332571 : Blo 1553474 2332571 := bstep (se 1 (by rfl) ⟨1749428, by rfl⟩ : syracuseStep 2332571 = 3498857) B3498857
theorem B2332649 : Blo 1553474 2332649 := bstep (se 2 (by rfl) ⟨874743, by rfl⟩ : syracuseStep 2332649 = 1749487) B1749487
theorem B2332799 : Blo 1553474 2332799 := bstep (se 1 (by rfl) ⟨1749599, by rfl⟩ : syracuseStep 2332799 = 3499199) B3499199
theorem B1554683 : Blo 1553474 1554683 := bstep (se 1 (by rfl) ⟨1166012, by rfl⟩ : syracuseStep 1554683 = 2332025) B2332025
theorem B5904839 : Blo 1553474 5904839 := bstep (se 1 (by rfl) ⟨4428629, by rfl⟩ : syracuseStep 5904839 = 8857259) B8857259
theorem B5249663 : Blo 1553474 5249663 := bstep (se 1 (by rfl) ⟨3937247, by rfl⟩ : syracuseStep 5249663 = 7874495) B7874495
theorem B4791143 : Blo 1553474 4791143 := bstep (se 1 (by rfl) ⟨3593357, by rfl⟩ : syracuseStep 4791143 = 7186715) B7186715
theorem B7871579 : Blo 1553474 7871579 := bstep (se 1 (by rfl) ⟨5903684, by rfl⟩ : syracuseStep 7871579 = 11807369) B11807369
theorem B90864737 : Blo 1553474 90864737 := bstep (se 2 (by rfl) ⟨34074276, by rfl⟩ : syracuseStep 90864737 = 68148553) B68148553
theorem B3497399 : Blo 1553474 3497399 := bstep (se 1 (by rfl) ⟨2623049, by rfl⟩ : syracuseStep 3497399 = 5246099) B5246099
theorem B14941705 : Blo 1553474 14941705 := bstep (se 2 (by rfl) ⟨5603139, by rfl⟩ : syracuseStep 14941705 = 11206279) B11206279
theorem B3497543 : Blo 1553474 3497543 := bstep (se 1 (by rfl) ⟨2623157, by rfl⟩ : syracuseStep 3497543 = 5246315) B5246315
theorem B3497849 : Blo 1553474 3497849 := bstep (se 2 (by rfl) ⟨1311693, by rfl⟩ : syracuseStep 3497849 = 2623387) B2623387
theorem B3932297 : Blo 1553474 3932297 := bstep (se 2 (by rfl) ⟨1474611, by rfl⟩ : syracuseStep 3932297 = 2949223) B2949223
theorem B3498209 : Blo 1553474 3498209 := bstep (se 2 (by rfl) ⟨1311828, by rfl⟩ : syracuseStep 3498209 = 2623657) B2623657
theorem B11198843 : Blo 1553474 11198843 := bstep (se 1 (by rfl) ⟨8399132, by rfl⟩ : syracuseStep 11198843 = 16798265) B16798265
theorem B2622415 : Blo 1553474 2622415 := bstep (se 1 (by rfl) ⟨1966811, by rfl⟩ : syracuseStep 2622415 = 3933623) B3933623
theorem B8848511 : Blo 1553474 8848511 := bstep (se 1 (by rfl) ⟨6636383, by rfl⟩ : syracuseStep 8848511 = 13272767) B13272767
theorem B3933481 : Blo 1553474 3933481 := bstep (se 2 (by rfl) ⟨1475055, by rfl⟩ : syracuseStep 3933481 = 2950111) B2950111
theorem B56755727 : Blo 1553474 56755727 := bstep (se 1 (by rfl) ⟨42566795, by rfl⟩ : syracuseStep 56755727 = 85133591) B85133591
theorem B7472699 : Blo 1553474 7472699 := bstep (se 1 (by rfl) ⟨5604524, by rfl⟩ : syracuseStep 7472699 = 11209049) B11209049
theorem B7980763 : Blo 1553474 7980763 := bstep (se 1 (by rfl) ⟨5985572, by rfl⟩ : syracuseStep 7980763 = 11971145) B11971145
theorem B3499775 : Blo 1553474 3499775 := bstep (se 1 (by rfl) ⟨2624831, by rfl⟩ : syracuseStep 3499775 = 5249663) B5249663
theorem B6637409 : Blo 1553474 6637409 := bstep (se 2 (by rfl) ⟨2489028, by rfl⟩ : syracuseStep 6637409 = 4978057) B4978057
theorem B3934079 : Blo 1553474 3934079 := bstep (se 1 (by rfl) ⟨2950559, by rfl⟩ : syracuseStep 3934079 = 5901119) B5901119
theorem B1968295 : Blo 1553474 1968295 := bstep (se 1 (by rfl) ⟨1476221, by rfl⟩ : syracuseStep 1968295 = 2952443) B2952443
theorem B3934777 : Blo 1553474 3934777 := bstep (se 2 (by rfl) ⟨1475541, by rfl⟩ : syracuseStep 3934777 = 2951083) B2951083
theorem B23014103 : Blo 1553474 23014103 := bstep (se 1 (by rfl) ⟨17260577, by rfl⟩ : syracuseStep 23014103 = 34521155) B34521155
theorem B2952283 : Blo 1553474 2952283 := bstep (se 1 (by rfl) ⟨2214212, by rfl⟩ : syracuseStep 2952283 = 4428425) B4428425
theorem B22400333 : Blo 1553474 22400333 := bstep (se 3 (by rfl) ⟨4200062, by rfl⟩ : syracuseStep 22400333 = 8400125) B8400125
theorem B13274543 : Blo 1553474 13274543 := bstep (se 1 (by rfl) ⟨9955907, by rfl⟩ : syracuseStep 13274543 = 19911815) B19911815
theorem B5246585 : Blo 1553474 5246585 := bstep (se 2 (by rfl) ⟨1967469, by rfl⟩ : syracuseStep 5246585 = 3934939) B3934939
theorem B3936559 : Blo 1553474 3936559 := bstep (se 1 (by rfl) ⟨2952419, by rfl⟩ : syracuseStep 3936559 = 5904839) B5904839
theorem B5247719 : Blo 1553474 5247719 := bstep (se 1 (by rfl) ⟨3935789, by rfl⟩ : syracuseStep 5247719 = 7871579) B7871579
theorem B60576491 : Blo 1553474 60576491 := bstep (se 1 (by rfl) ⟨45432368, by rfl⟩ : syracuseStep 60576491 = 90864737) B90864737
theorem B5247881 : Blo 1553474 5247881 := bstep (se 2 (by rfl) ⟨1967955, by rfl⟩ : syracuseStep 5247881 = 3935911) B3935911
theorem B2331599 : Blo 1553474 2331599 := bstep (se 1 (by rfl) ⟨1748699, by rfl⟩ : syracuseStep 2331599 = 3497399) B3497399
theorem B2331695 : Blo 1553474 2331695 := bstep (se 1 (by rfl) ⟨1748771, by rfl⟩ : syracuseStep 2331695 = 3497543) B3497543
theorem B1553599 : Blo 1553474 1553599 := bstep (se 1 (by rfl) ⟨1165199, by rfl⟩ : syracuseStep 1553599 = 2330399) B2330399
theorem B2331899 : Blo 1553474 2331899 := bstep (se 1 (by rfl) ⟨1748924, by rfl⟩ : syracuseStep 2331899 = 3497849) B3497849
theorem B4609391 : Blo 1553474 4609391 := bstep (se 1 (by rfl) ⟨3457043, by rfl⟩ : syracuseStep 4609391 = 6914087) B6914087
theorem B1553871 : Blo 1553474 1553871 := bstep (se 1 (by rfl) ⟨1165403, by rfl⟩ : syracuseStep 1553871 = 2330807) B2330807
theorem B3544553 : Blo 1553474 3544553 := bstep (se 2 (by rfl) ⟨1329207, by rfl⟩ : syracuseStep 3544553 = 2658415) B2658415
theorem B2274799 : Blo 1553474 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B1553919 : Blo 1553474 1553919 := bstep (se 1 (by rfl) ⟨1165439, by rfl⟩ : syracuseStep 1553919 = 2330879) B2330879
theorem B5248637 : Blo 1553474 5248637 := bstep (se 3 (by rfl) ⟨984119, by rfl⟩ : syracuseStep 5248637 = 1968239) B1968239
theorem B1554287 : Blo 1553474 1554287 := bstep (se 1 (by rfl) ⟨1165715, by rfl⟩ : syracuseStep 1554287 = 2331431) B2331431
theorem B1554303 : Blo 1553474 1554303 := bstep (se 1 (by rfl) ⟨1165727, by rfl⟩ : syracuseStep 1554303 = 2331455) B2331455
theorem B7870607 : Blo 1553474 7870607 := bstep (se 1 (by rfl) ⟨5902955, by rfl⟩ : syracuseStep 7870607 = 11805911) B11805911
theorem B19921247 : Blo 1553474 19921247 := bstep (se 1 (by rfl) ⟨14940935, by rfl⟩ : syracuseStep 19921247 = 29881871) B29881871
theorem B1554843 : Blo 1553474 1554843 := bstep (se 1 (by rfl) ⟨1166132, by rfl⟩ : syracuseStep 1554843 = 2332265) B2332265
theorem B2333177 : Blo 1553474 2333177 := bstep (se 2 (by rfl) ⟨874941, by rfl⟩ : syracuseStep 2333177 = 1749883) B1749883
theorem B1555047 : Blo 1553474 1555047 := bstep (se 1 (by rfl) ⟨1166285, by rfl⟩ : syracuseStep 1555047 = 2332571) B2332571
theorem B5905021 : Blo 1553474 5905021 := bstep (se 3 (by rfl) ⟨1107191, by rfl⟩ : syracuseStep 5905021 = 2214383) B2214383
theorem B1555099 : Blo 1553474 1555099 := bstep (se 1 (by rfl) ⟨1166324, by rfl⟩ : syracuseStep 1555099 = 2332649) B2332649
theorem B3496679 : Blo 1553474 3496679 := bstep (se 1 (by rfl) ⟨2622509, by rfl⟩ : syracuseStep 3496679 = 5245019) B5245019
theorem B1555199 : Blo 1553474 1555199 := bstep (se 1 (by rfl) ⟨1166399, by rfl⟩ : syracuseStep 1555199 = 2332799) B2332799
theorem B6642911 : Blo 1553474 6642911 := bstep (se 1 (by rfl) ⟨4982183, by rfl⟩ : syracuseStep 6642911 = 9964367) B9964367
theorem B3194095 : Blo 1553474 3194095 := bstep (se 1 (by rfl) ⟨2395571, by rfl⟩ : syracuseStep 3194095 = 4791143) B4791143
theorem B19922273 : Blo 1553474 19922273 := bstep (se 2 (by rfl) ⟨7470852, by rfl⟩ : syracuseStep 19922273 = 14941705) B14941705
theorem B233102717 : Blo 1553474 233102717 := bstep (se 3 (by rfl) ⟨43706759, by rfl⟩ : syracuseStep 233102717 = 87413519) B87413519
theorem B3497471 : Blo 1553474 3497471 := bstep (se 1 (by rfl) ⟨2623103, by rfl⟩ : syracuseStep 3497471 = 5246207) B5246207
theorem B319184507 : Blo 1553474 319184507 := bstep (se 1 (by rfl) ⟨239388380, by rfl⟩ : syracuseStep 319184507 = 478776761) B478776761
theorem B3497939 : Blo 1553474 3497939 := bstep (se 1 (by rfl) ⟨2623454, by rfl⟩ : syracuseStep 3497939 = 5246909) B5246909
theorem B2621531 : Blo 1553474 2621531 := bstep (se 1 (by rfl) ⟨1966148, by rfl⟩ : syracuseStep 2621531 = 3932297) B3932297
theorem B3498479 : Blo 1553474 3498479 := bstep (se 1 (by rfl) ⟨2623859, by rfl⟩ : syracuseStep 3498479 = 5247719) B5247719
theorem B3498587 : Blo 1553474 3498587 := bstep (se 1 (by rfl) ⟨2623940, by rfl⟩ : syracuseStep 3498587 = 5247881) B5247881
theorem B5899007 : Blo 1553474 5899007 := bstep (se 1 (by rfl) ⟨4424255, by rfl⟩ : syracuseStep 5899007 = 8848511) B8848511
theorem B7873361 : Blo 1553474 7873361 := bstep (se 2 (by rfl) ⟨2952510, by rfl⟩ : syracuseStep 7873361 = 5905021) B5905021
theorem B4981799 : Blo 1553474 4981799 := bstep (se 1 (by rfl) ⟨3736349, by rfl⟩ : syracuseStep 4981799 = 7472699) B7472699
theorem B3499091 : Blo 1553474 3499091 := bstep (se 1 (by rfl) ⟨2624318, by rfl⟩ : syracuseStep 3499091 = 5248637) B5248637
theorem B4424939 : Blo 1553474 4424939 := bstep (se 1 (by rfl) ⟨3318704, by rfl⟩ : syracuseStep 4424939 = 6637409) B6637409
theorem B2622719 : Blo 1553474 2622719 := bstep (se 1 (by rfl) ⟨1967039, by rfl⟩ : syracuseStep 2622719 = 3934079) B3934079
theorem B13280831 : Blo 1553474 13280831 := bstep (se 1 (by rfl) ⟨9960623, by rfl⟩ : syracuseStep 13280831 = 19921247) B19921247
theorem B851158685 : Blo 1553474 851158685 := bstep (se 3 (by rfl) ⟨159592253, by rfl⟩ : syracuseStep 851158685 = 319184507) B319184507
theorem B5244641 : Blo 1553474 5244641 := bstep (se 2 (by rfl) ⟨1966740, by rfl⟩ : syracuseStep 5244641 = 3933481) B3933481
theorem B3033065 : Blo 1553474 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B13281515 : Blo 1553474 13281515 := bstep (se 1 (by rfl) ⟨9961136, by rfl⟩ : syracuseStep 13281515 = 19922273) B19922273
theorem B8849695 : Blo 1553474 8849695 := bstep (se 1 (by rfl) ⟨6637271, by rfl⟩ : syracuseStep 8849695 = 13274543) B13274543
theorem B2624393 : Blo 1553474 2624393 := bstep (se 2 (by rfl) ⟨984147, by rfl⟩ : syracuseStep 2624393 = 1968295) B1968295
theorem B7465895 : Blo 1553474 7465895 := bstep (se 1 (by rfl) ⟨5599421, by rfl⟩ : syracuseStep 7465895 = 11198843) B11198843
theorem B5246369 : Blo 1553474 5246369 := bstep (se 2 (by rfl) ⟨1967388, by rfl⟩ : syracuseStep 5246369 = 3934777) B3934777
theorem B2363035 : Blo 1553474 2363035 := bstep (se 1 (by rfl) ⟨1772276, by rfl⟩ : syracuseStep 2363035 = 3544553) B3544553
theorem B5247071 : Blo 1553474 5247071 := bstep (se 1 (by rfl) ⟨3935303, by rfl⟩ : syracuseStep 5247071 = 7870607) B7870607
theorem B3936377 : Blo 1553474 3936377 := bstep (se 2 (by rfl) ⟨1476141, by rfl⟩ : syracuseStep 3936377 = 2952283) B2952283
theorem B2331119 : Blo 1553474 2331119 := bstep (se 1 (by rfl) ⟨1748339, by rfl⟩ : syracuseStep 2331119 = 3496679) B3496679
theorem B61370941 : Blo 1553474 61370941 := bstep (se 3 (by rfl) ⟨11507051, by rfl⟩ : syracuseStep 61370941 = 23014103) B23014103
theorem B4428607 : Blo 1553474 4428607 := bstep (se 1 (by rfl) ⟨3321455, by rfl⟩ : syracuseStep 4428607 = 6642911) B6642911
theorem B2331647 : Blo 1553474 2331647 := bstep (se 1 (by rfl) ⟨1748735, by rfl⟩ : syracuseStep 2331647 = 3497471) B3497471
theorem B2331959 : Blo 1553474 2331959 := bstep (se 1 (by rfl) ⟨1748969, by rfl⟩ : syracuseStep 2331959 = 3497939) B3497939
theorem B2332139 : Blo 1553474 2332139 := bstep (se 1 (by rfl) ⟨1749104, by rfl⟩ : syracuseStep 2332139 = 3498209) B3498209
theorem B5248745 : Blo 1553474 5248745 := bstep (se 2 (by rfl) ⟨1968279, by rfl⟩ : syracuseStep 5248745 = 3936559) B3936559
theorem B40384327 : Blo 1553474 40384327 := bstep (se 1 (by rfl) ⟨30288245, by rfl⟩ : syracuseStep 40384327 = 60576491) B60576491
theorem B1554399 : Blo 1553474 1554399 := bstep (se 1 (by rfl) ⟨1165799, by rfl⟩ : syracuseStep 1554399 = 2331599) B2331599
theorem B1554463 : Blo 1553474 1554463 := bstep (se 1 (by rfl) ⟨1165847, by rfl⟩ : syracuseStep 1554463 = 2331695) B2331695
theorem B1554599 : Blo 1553474 1554599 := bstep (se 1 (by rfl) ⟨1165949, by rfl⟩ : syracuseStep 1554599 = 2331899) B2331899
theorem B37837151 : Blo 1553474 37837151 := bstep (se 1 (by rfl) ⟨28377863, by rfl⟩ : syracuseStep 37837151 = 56755727) B56755727
theorem B49166837 : Blo 1553474 49166837 := bstep (se 5 (by rfl) ⟨2304695, by rfl⟩ : syracuseStep 49166837 = 4609391) B4609391
theorem B2333183 : Blo 1553474 2333183 := bstep (se 1 (by rfl) ⟨1749887, by rfl⟩ : syracuseStep 2333183 = 3499775) B3499775
theorem B3496553 : Blo 1553474 3496553 := bstep (se 2 (by rfl) ⟨1311207, by rfl⟩ : syracuseStep 3496553 = 2622415) B2622415
theorem B4258793 : Blo 1553474 4258793 := bstep (se 2 (by rfl) ⟨1597047, by rfl⟩ : syracuseStep 4258793 = 3194095) B3194095
theorem B1555451 : Blo 1553474 1555451 := bstep (se 1 (by rfl) ⟨1166588, by rfl⟩ : syracuseStep 1555451 = 2333177) B2333177
theorem B14933555 : Blo 1553474 14933555 := bstep (se 1 (by rfl) ⟨11200166, by rfl⟩ : syracuseStep 14933555 = 22400333) B22400333
theorem B155401811 : Blo 1553474 155401811 := bstep (se 1 (by rfl) ⟨116551358, by rfl⟩ : syracuseStep 155401811 = 233102717) B233102717
theorem B10641017 : Blo 1553474 10641017 := bstep (se 2 (by rfl) ⟨3990381, by rfl⟩ : syracuseStep 10641017 = 7980763) B7980763
theorem B3497723 : Blo 1553474 3497723 := bstep (se 1 (by rfl) ⟨2623292, by rfl⟩ : syracuseStep 3497723 = 5246585) B5246585
theorem B3498047 : Blo 1553474 3498047 := bstep (se 1 (by rfl) ⟨2623535, by rfl⟩ : syracuseStep 3498047 = 5247071) B5247071
theorem B3932671 : Blo 1553474 3932671 := bstep (se 1 (by rfl) ⟨2949503, by rfl⟩ : syracuseStep 3932671 = 5899007) B5899007
theorem B2949959 : Blo 1553474 2949959 := bstep (se 1 (by rfl) ⟨2212469, by rfl⟩ : syracuseStep 2949959 = 4424939) B4424939
theorem B3499163 : Blo 1553474 3499163 := bstep (se 1 (by rfl) ⟨2624372, by rfl⟩ : syracuseStep 3499163 = 5248745) B5248745
theorem B25224767 : Blo 1553474 25224767 := bstep (se 1 (by rfl) ⟨18918575, by rfl⟩ : syracuseStep 25224767 = 37837151) B37837151
theorem B32777891 : Blo 1553474 32777891 := bstep (se 1 (by rfl) ⟨24583418, by rfl⟩ : syracuseStep 32777891 = 49166837) B49166837
theorem B9955703 : Blo 1553474 9955703 := bstep (se 1 (by rfl) ⟨7466777, by rfl⟩ : syracuseStep 9955703 = 14933555) B14933555
theorem B8088173 : Blo 1553474 8088173 := bstep (se 3 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 8088173 = 3033065) B3033065
theorem B1747687 : Blo 1553474 1747687 := bstep (se 1 (by rfl) ⟨1310765, by rfl⟩ : syracuseStep 1747687 = 2621531) B2621531
theorem B2624251 : Blo 1553474 2624251 := bstep (se 1 (by rfl) ⟨1968188, by rfl⟩ : syracuseStep 2624251 = 3936377) B3936377
theorem B11799593 : Blo 1553474 11799593 := bstep (se 2 (by rfl) ⟨4424847, by rfl⟩ : syracuseStep 11799593 = 8849695) B8849695
theorem B3321199 : Blo 1553474 3321199 := bstep (se 1 (by rfl) ⟨2490899, by rfl⟩ : syracuseStep 3321199 = 4981799) B4981799
theorem B1748479 : Blo 1553474 1748479 := bstep (se 1 (by rfl) ⟨1311359, by rfl⟩ : syracuseStep 1748479 = 2622719) B2622719
theorem B567439123 : Blo 1553474 567439123 := bstep (se 1 (by rfl) ⟨425579342, by rfl⟩ : syracuseStep 567439123 = 851158685) B851158685
theorem B2331035 : Blo 1553474 2331035 := bstep (se 1 (by rfl) ⟨1748276, by rfl⟩ : syracuseStep 2331035 = 3496553) B3496553
theorem B1749595 : Blo 1553474 1749595 := bstep (se 1 (by rfl) ⟨1312196, by rfl⟩ : syracuseStep 1749595 = 2624393) B2624393
theorem B4977263 : Blo 1553474 4977263 := bstep (se 1 (by rfl) ⟨3732947, by rfl⟩ : syracuseStep 4977263 = 7465895) B7465895
theorem B2839195 : Blo 1553474 2839195 := bstep (se 1 (by rfl) ⟨2129396, by rfl⟩ : syracuseStep 2839195 = 4258793) B4258793
theorem B3150713 : Blo 1553474 3150713 := bstep (se 2 (by rfl) ⟨1181517, by rfl⟩ : syracuseStep 3150713 = 2363035) B2363035
theorem B103601207 : Blo 1553474 103601207 := bstep (se 1 (by rfl) ⟨77700905, by rfl⟩ : syracuseStep 103601207 = 155401811) B155401811
theorem B2331815 : Blo 1553474 2331815 := bstep (se 1 (by rfl) ⟨1748861, by rfl⟩ : syracuseStep 2331815 = 3497723) B3497723
theorem B1554079 : Blo 1553474 1554079 := bstep (se 1 (by rfl) ⟨1165559, by rfl⟩ : syracuseStep 1554079 = 2331119) B2331119
theorem B2332319 : Blo 1553474 2332319 := bstep (se 1 (by rfl) ⟨1749239, by rfl⟩ : syracuseStep 2332319 = 3498479) B3498479
theorem B2332391 : Blo 1553474 2332391 := bstep (se 1 (by rfl) ⟨1749293, by rfl⟩ : syracuseStep 2332391 = 3498587) B3498587
theorem B5248907 : Blo 1553474 5248907 := bstep (se 1 (by rfl) ⟨3936680, by rfl⟩ : syracuseStep 5248907 = 7873361) B7873361
theorem B1554431 : Blo 1553474 1554431 := bstep (se 1 (by rfl) ⟨1165823, by rfl⟩ : syracuseStep 1554431 = 2331647) B2331647
theorem B2332727 : Blo 1553474 2332727 := bstep (se 1 (by rfl) ⟨1749545, by rfl⟩ : syracuseStep 2332727 = 3499091) B3499091
theorem B81827921 : Blo 1553474 81827921 := bstep (se 2 (by rfl) ⟨30685470, by rfl⟩ : syracuseStep 81827921 = 61370941) B61370941
theorem B1554639 : Blo 1553474 1554639 := bstep (se 1 (by rfl) ⟨1165979, by rfl⟩ : syracuseStep 1554639 = 2331959) B2331959
theorem B1554759 : Blo 1553474 1554759 := bstep (se 1 (by rfl) ⟨1166069, by rfl⟩ : syracuseStep 1554759 = 2332139) B2332139
theorem B8853887 : Blo 1553474 8853887 := bstep (se 1 (by rfl) ⟨6640415, by rfl⟩ : syracuseStep 8853887 = 13280831) B13280831
theorem B5904809 : Blo 1553474 5904809 := bstep (se 2 (by rfl) ⟨2214303, by rfl⟩ : syracuseStep 5904809 = 4428607) B4428607
theorem B3496427 : Blo 1553474 3496427 := bstep (se 1 (by rfl) ⟨2622320, by rfl⟩ : syracuseStep 3496427 = 5244641) B5244641
theorem B8854343 : Blo 1553474 8854343 := bstep (se 1 (by rfl) ⟨6640757, by rfl⟩ : syracuseStep 8854343 = 13281515) B13281515
theorem B28376045 : Blo 1553474 28376045 := bstep (se 3 (by rfl) ⟨5320508, by rfl⟩ : syracuseStep 28376045 = 10641017) B10641017
theorem B1555455 : Blo 1553474 1555455 := bstep (se 1 (by rfl) ⟨1166591, by rfl⟩ : syracuseStep 1555455 = 2333183) B2333183
theorem B3497579 : Blo 1553474 3497579 := bstep (se 1 (by rfl) ⟨2623184, by rfl⟩ : syracuseStep 3497579 = 5246369) B5246369
theorem B53845769 : Blo 1553474 53845769 := bstep (se 2 (by rfl) ⟨20192163, by rfl⟩ : syracuseStep 53845769 = 40384327) B40384327
theorem B3318175 : Blo 1553474 3318175 := bstep (se 1 (by rfl) ⟨2488631, by rfl⟩ : syracuseStep 3318175 = 4977263) B4977263
theorem B5243561 : Blo 1553474 5243561 := bstep (se 2 (by rfl) ⟨1966335, by rfl⟩ : syracuseStep 5243561 = 3932671) B3932671
theorem B3499001 : Blo 1553474 3499001 := bstep (se 2 (by rfl) ⟨1312125, by rfl⟩ : syracuseStep 3499001 = 2624251) B2624251
theorem B3499271 : Blo 1553474 3499271 := bstep (se 1 (by rfl) ⟨2624453, by rfl⟩ : syracuseStep 3499271 = 5248907) B5248907
theorem B6637135 : Blo 1553474 6637135 := bstep (se 1 (by rfl) ⟨4977851, by rfl⟩ : syracuseStep 6637135 = 9955703) B9955703
theorem B5392115 : Blo 1553474 5392115 := bstep (se 1 (by rfl) ⟨4044086, by rfl⟩ : syracuseStep 5392115 = 8088173) B8088173
theorem B18917363 : Blo 1553474 18917363 := bstep (se 1 (by rfl) ⟨14188022, by rfl⟩ : syracuseStep 18917363 = 28376045) B28376045
theorem B7866395 : Blo 1553474 7866395 := bstep (se 1 (by rfl) ⟨5899796, by rfl⟩ : syracuseStep 7866395 = 11799593) B11799593
theorem B7866557 : Blo 1553474 7866557 := bstep (se 3 (by rfl) ⟨1474979, by rfl⟩ : syracuseStep 7866557 = 2949959) B2949959
theorem B276269885 : Blo 1553474 276269885 := bstep (se 3 (by rfl) ⟨51800603, by rfl⟩ : syracuseStep 276269885 = 103601207) B103601207
theorem B2100475 : Blo 1553474 2100475 := bstep (se 1 (by rfl) ⟨1575356, by rfl⟩ : syracuseStep 2100475 = 3150713) B3150713
theorem B15142373 : Blo 1553474 15142373 := bstep (se 4 (by rfl) ⟨1419597, by rfl⟩ : syracuseStep 15142373 = 2839195) B2839195
theorem B2330249 : Blo 1553474 2330249 := bstep (se 2 (by rfl) ⟨873843, by rfl⟩ : syracuseStep 2330249 = 1747687) B1747687
theorem B21851927 : Blo 1553474 21851927 := bstep (se 1 (by rfl) ⟨16388945, by rfl⟩ : syracuseStep 21851927 = 32777891) B32777891
theorem B5902591 : Blo 1553474 5902591 := bstep (se 1 (by rfl) ⟨4426943, by rfl⟩ : syracuseStep 5902591 = 8853887) B8853887
theorem B3936539 : Blo 1553474 3936539 := bstep (se 1 (by rfl) ⟨2952404, by rfl⟩ : syracuseStep 3936539 = 5904809) B5904809
theorem B2330951 : Blo 1553474 2330951 := bstep (se 1 (by rfl) ⟨1748213, by rfl⟩ : syracuseStep 2330951 = 3496427) B3496427
theorem B4428265 : Blo 1553474 4428265 := bstep (se 2 (by rfl) ⟨1660599, by rfl⟩ : syracuseStep 4428265 = 3321199) B3321199
theorem B5902895 : Blo 1553474 5902895 := bstep (se 1 (by rfl) ⟨4427171, by rfl⟩ : syracuseStep 5902895 = 8854343) B8854343
theorem B2331305 : Blo 1553474 2331305 := bstep (se 2 (by rfl) ⟨874239, by rfl⟩ : syracuseStep 2331305 = 1748479) B1748479
theorem B756585497 : Blo 1553474 756585497 := bstep (se 2 (by rfl) ⟨283719561, by rfl⟩ : syracuseStep 756585497 = 567439123) B567439123
theorem B2331719 : Blo 1553474 2331719 := bstep (se 1 (by rfl) ⟨1748789, by rfl⟩ : syracuseStep 2331719 = 3497579) B3497579
theorem B2332031 : Blo 1553474 2332031 := bstep (se 1 (by rfl) ⟨1749023, by rfl⟩ : syracuseStep 2332031 = 3498047) B3498047
theorem B218207789 : Blo 1553474 218207789 := bstep (se 3 (by rfl) ⟨40913960, by rfl⟩ : syracuseStep 218207789 = 81827921) B81827921
theorem B1554023 : Blo 1553474 1554023 := bstep (se 1 (by rfl) ⟨1165517, by rfl⟩ : syracuseStep 1554023 = 2331035) B2331035
theorem B2332775 : Blo 1553474 2332775 := bstep (se 1 (by rfl) ⟨1749581, by rfl⟩ : syracuseStep 2332775 = 3499163) B3499163
theorem B1554543 : Blo 1553474 1554543 := bstep (se 1 (by rfl) ⟨1165907, by rfl⟩ : syracuseStep 1554543 = 2331815) B2331815
theorem B2332793 : Blo 1553474 2332793 := bstep (se 2 (by rfl) ⟨874797, by rfl⟩ : syracuseStep 2332793 = 1749595) B1749595
theorem B16816511 : Blo 1553474 16816511 := bstep (se 1 (by rfl) ⟨12612383, by rfl⟩ : syracuseStep 16816511 = 25224767) B25224767
theorem B1554879 : Blo 1553474 1554879 := bstep (se 1 (by rfl) ⟨1166159, by rfl⟩ : syracuseStep 1554879 = 2332319) B2332319
theorem B1554927 : Blo 1553474 1554927 := bstep (se 1 (by rfl) ⟨1166195, by rfl⟩ : syracuseStep 1554927 = 2332391) B2332391
theorem B1555151 : Blo 1553474 1555151 := bstep (se 1 (by rfl) ⟨1166363, by rfl⟩ : syracuseStep 1555151 = 2332727) B2332727
theorem B35897179 : Blo 1553474 35897179 := bstep (se 1 (by rfl) ⟨26922884, by rfl⟩ : syracuseStep 35897179 = 53845769) B53845769
theorem B4424233 : Blo 1553474 4424233 := bstep (se 2 (by rfl) ⟨1659087, by rfl⟩ : syracuseStep 4424233 = 3318175) B3318175
theorem B504390331 : Blo 1553474 504390331 := bstep (se 1 (by rfl) ⟨378292748, by rfl⟩ : syracuseStep 504390331 = 756585497) B756585497
theorem B5244263 : Blo 1553474 5244263 := bstep (se 1 (by rfl) ⟨3933197, by rfl⟩ : syracuseStep 5244263 = 7866395) B7866395
theorem B5244371 : Blo 1553474 5244371 := bstep (se 1 (by rfl) ⟨3933278, by rfl⟩ : syracuseStep 5244371 = 7866557) B7866557
theorem B8849513 : Blo 1553474 8849513 := bstep (se 2 (by rfl) ⟨3318567, by rfl⟩ : syracuseStep 8849513 = 6637135) B6637135
theorem B10094915 : Blo 1553474 10094915 := bstep (se 1 (by rfl) ⟨7571186, by rfl⟩ : syracuseStep 10094915 = 15142373) B15142373
theorem B14567951 : Blo 1553474 14567951 := bstep (se 1 (by rfl) ⟨10925963, by rfl⟩ : syracuseStep 14567951 = 21851927) B21851927
theorem B2624359 : Blo 1553474 2624359 := bstep (se 1 (by rfl) ⟨1968269, by rfl⟩ : syracuseStep 2624359 = 3936539) B3936539
theorem B3935263 : Blo 1553474 3935263 := bstep (se 1 (by rfl) ⟨2951447, by rfl⟩ : syracuseStep 3935263 = 5902895) B5902895
theorem B11202533 : Blo 1553474 11202533 := bstep (se 4 (by rfl) ⟨1050237, by rfl⟩ : syracuseStep 11202533 = 2100475) B2100475
theorem B12611575 : Blo 1553474 12611575 := bstep (se 1 (by rfl) ⟨9458681, by rfl⟩ : syracuseStep 12611575 = 18917363) B18917363
theorem B11211007 : Blo 1553474 11211007 := bstep (se 1 (by rfl) ⟨8408255, by rfl⟩ : syracuseStep 11211007 = 16816511) B16816511
theorem B1553499 : Blo 1553474 1553499 := bstep (se 1 (by rfl) ⟨1165124, by rfl⟩ : syracuseStep 1553499 = 2330249) B2330249
theorem B47862905 : Blo 1553474 47862905 := bstep (se 2 (by rfl) ⟨17948589, by rfl⟩ : syracuseStep 47862905 = 35897179) B35897179
theorem B1553967 : Blo 1553474 1553967 := bstep (se 1 (by rfl) ⟨1165475, by rfl⟩ : syracuseStep 1553967 = 2330951) B2330951
theorem B7870121 : Blo 1553474 7870121 := bstep (se 2 (by rfl) ⟨2951295, by rfl⟩ : syracuseStep 7870121 = 5902591) B5902591
theorem B3495707 : Blo 1553474 3495707 := bstep (se 1 (by rfl) ⟨2621780, by rfl⟩ : syracuseStep 3495707 = 5243561) B5243561
theorem B1554203 : Blo 1553474 1554203 := bstep (se 1 (by rfl) ⟨1165652, by rfl⟩ : syracuseStep 1554203 = 2331305) B2331305
theorem B5904353 : Blo 1553474 5904353 := bstep (se 2 (by rfl) ⟨2214132, by rfl⟩ : syracuseStep 5904353 = 4428265) B4428265
theorem B2332667 : Blo 1553474 2332667 := bstep (se 1 (by rfl) ⟨1749500, by rfl⟩ : syracuseStep 2332667 = 3499001) B3499001
theorem B1554479 : Blo 1553474 1554479 := bstep (se 1 (by rfl) ⟨1165859, by rfl⟩ : syracuseStep 1554479 = 2331719) B2331719
theorem B2332847 : Blo 1553474 2332847 := bstep (se 1 (by rfl) ⟨1749635, by rfl⟩ : syracuseStep 2332847 = 3499271) B3499271
theorem B1554687 : Blo 1553474 1554687 := bstep (se 1 (by rfl) ⟨1166015, by rfl⟩ : syracuseStep 1554687 = 2332031) B2332031
theorem B145471859 : Blo 1553474 145471859 := bstep (se 1 (by rfl) ⟨109103894, by rfl⟩ : syracuseStep 145471859 = 218207789) B218207789
theorem B3594743 : Blo 1553474 3594743 := bstep (se 1 (by rfl) ⟨2696057, by rfl⟩ : syracuseStep 3594743 = 5392115) B5392115
theorem B1555183 : Blo 1553474 1555183 := bstep (se 1 (by rfl) ⟨1166387, by rfl⟩ : syracuseStep 1555183 = 2332775) B2332775
theorem B1555195 : Blo 1553474 1555195 := bstep (se 1 (by rfl) ⟨1166396, by rfl⟩ : syracuseStep 1555195 = 2332793) B2332793
theorem B184179923 : Blo 1553474 184179923 := bstep (se 1 (by rfl) ⟨138134942, by rfl⟩ : syracuseStep 184179923 = 276269885) B276269885
theorem B5898977 : Blo 1553474 5898977 := bstep (se 2 (by rfl) ⟨2212116, by rfl⟩ : syracuseStep 5898977 = 4424233) B4424233
theorem B26919773 : Blo 1553474 26919773 := bstep (se 3 (by rfl) ⟨5047457, by rfl⟩ : syracuseStep 26919773 = 10094915) B10094915
theorem B3499145 : Blo 1553474 3499145 := bstep (se 2 (by rfl) ⟨1312179, by rfl⟩ : syracuseStep 3499145 = 2624359) B2624359
theorem B5899675 : Blo 1553474 5899675 := bstep (se 1 (by rfl) ⟨4424756, by rfl⟩ : syracuseStep 5899675 = 8849513) B8849513
theorem B127634413 : Blo 1553474 127634413 := bstep (se 3 (by rfl) ⟨23931452, by rfl⟩ : syracuseStep 127634413 = 47862905) B47862905
theorem B5246747 : Blo 1553474 5246747 := bstep (se 1 (by rfl) ⟨3935060, by rfl⟩ : syracuseStep 5246747 = 7870121) B7870121
theorem B2330471 : Blo 1553474 2330471 := bstep (se 1 (by rfl) ⟨1747853, by rfl⟩ : syracuseStep 2330471 = 3495707) B3495707
theorem B3936235 : Blo 1553474 3936235 := bstep (se 1 (by rfl) ⟨2952176, by rfl⟩ : syracuseStep 3936235 = 5904353) B5904353
theorem B5247017 : Blo 1553474 5247017 := bstep (se 2 (by rfl) ⟨1967631, by rfl⟩ : syracuseStep 5247017 = 3935263) B3935263
theorem B96981239 : Blo 1553474 96981239 := bstep (se 1 (by rfl) ⟨72735929, by rfl⟩ : syracuseStep 96981239 = 145471859) B145471859
theorem B2396495 : Blo 1553474 2396495 := bstep (se 1 (by rfl) ⟨1797371, by rfl⟩ : syracuseStep 2396495 = 3594743) B3594743
theorem B9711967 : Blo 1553474 9711967 := bstep (se 1 (by rfl) ⟨7283975, by rfl⟩ : syracuseStep 9711967 = 14567951) B14567951
theorem B122786615 : Blo 1553474 122786615 := bstep (se 1 (by rfl) ⟨92089961, by rfl⟩ : syracuseStep 122786615 = 184179923) B184179923
theorem B7468355 : Blo 1553474 7468355 := bstep (se 1 (by rfl) ⟨5601266, by rfl⟩ : syracuseStep 7468355 = 11202533) B11202533
theorem B16815433 : Blo 1553474 16815433 := bstep (se 2 (by rfl) ⟨6305787, by rfl⟩ : syracuseStep 16815433 = 12611575) B12611575
theorem B14948009 : Blo 1553474 14948009 := bstep (se 2 (by rfl) ⟨5605503, by rfl⟩ : syracuseStep 14948009 = 11211007) B11211007
theorem B3496175 : Blo 1553474 3496175 := bstep (se 1 (by rfl) ⟨2622131, by rfl⟩ : syracuseStep 3496175 = 5244263) B5244263
theorem B672520441 : Blo 1553474 672520441 := bstep (se 2 (by rfl) ⟨252195165, by rfl⟩ : syracuseStep 672520441 = 504390331) B504390331
theorem B3496247 : Blo 1553474 3496247 := bstep (se 1 (by rfl) ⟨2622185, by rfl⟩ : syracuseStep 3496247 = 5244371) B5244371
theorem B1555111 : Blo 1553474 1555111 := bstep (se 1 (by rfl) ⟨1166333, by rfl⟩ : syracuseStep 1555111 = 2332667) B2332667
theorem B1555231 : Blo 1553474 1555231 := bstep (se 1 (by rfl) ⟨1166423, by rfl⟩ : syracuseStep 1555231 = 2332847) B2332847
theorem B3498011 : Blo 1553474 3498011 := bstep (se 1 (by rfl) ⟨2623508, by rfl⟩ : syracuseStep 3498011 = 5247017) B5247017
theorem B1597663 : Blo 1553474 1597663 := bstep (se 1 (by rfl) ⟨1198247, by rfl⟩ : syracuseStep 1597663 = 2396495) B2396495
theorem B3932651 : Blo 1553474 3932651 := bstep (se 1 (by rfl) ⟨2949488, by rfl⟩ : syracuseStep 3932651 = 5898977) B5898977
theorem B7866233 : Blo 1553474 7866233 := bstep (se 2 (by rfl) ⟨2949837, by rfl⟩ : syracuseStep 7866233 = 5899675) B5899675
theorem B64654159 : Blo 1553474 64654159 := bstep (se 1 (by rfl) ⟨48490619, by rfl⟩ : syracuseStep 64654159 = 96981239) B96981239
theorem B9965339 : Blo 1553474 9965339 := bstep (se 1 (by rfl) ⟨7474004, by rfl⟩ : syracuseStep 9965339 = 14948009) B14948009
theorem B2330783 : Blo 1553474 2330783 := bstep (se 1 (by rfl) ⟨1748087, by rfl⟩ : syracuseStep 2330783 = 3496175) B3496175
theorem B2330831 : Blo 1553474 2330831 := bstep (se 1 (by rfl) ⟨1748123, by rfl⟩ : syracuseStep 2330831 = 3496247) B3496247
theorem B327430973 : Blo 1553474 327430973 := bstep (se 3 (by rfl) ⟨61393307, by rfl⟩ : syracuseStep 327430973 = 122786615) B122786615
theorem B1553647 : Blo 1553474 1553647 := bstep (se 1 (by rfl) ⟨1165235, by rfl⟩ : syracuseStep 1553647 = 2330471) B2330471
theorem B5248313 : Blo 1553474 5248313 := bstep (se 2 (by rfl) ⟨1968117, by rfl⟩ : syracuseStep 5248313 = 3936235) B3936235
theorem B896693921 : Blo 1553474 896693921 := bstep (se 2 (by rfl) ⟨336260220, by rfl⟩ : syracuseStep 896693921 = 672520441) B672520441
theorem B12949289 : Blo 1553474 12949289 := bstep (se 2 (by rfl) ⟨4855983, by rfl⟩ : syracuseStep 12949289 = 9711967) B9711967
theorem B17946515 : Blo 1553474 17946515 := bstep (se 1 (by rfl) ⟨13459886, by rfl⟩ : syracuseStep 17946515 = 26919773) B26919773
theorem B2332763 : Blo 1553474 2332763 := bstep (se 1 (by rfl) ⟨1749572, by rfl⟩ : syracuseStep 2332763 = 3499145) B3499145
theorem B4978903 : Blo 1553474 4978903 := bstep (se 1 (by rfl) ⟨3734177, by rfl⟩ : syracuseStep 4978903 = 7468355) B7468355
theorem B170179217 : Blo 1553474 170179217 := bstep (se 2 (by rfl) ⟨63817206, by rfl⟩ : syracuseStep 170179217 = 127634413) B127634413
theorem B22420577 : Blo 1553474 22420577 := bstep (se 2 (by rfl) ⟨8407716, by rfl⟩ : syracuseStep 22420577 = 16815433) B16815433
theorem B3497831 : Blo 1553474 3497831 := bstep (se 1 (by rfl) ⟨2623373, by rfl⟩ : syracuseStep 3497831 = 5246747) B5246747
theorem B2621767 : Blo 1553474 2621767 := bstep (se 1 (by rfl) ⟨1966325, by rfl⟩ : syracuseStep 2621767 = 3932651) B3932651
theorem B138125749 : Blo 1553474 138125749 := bstep (se 5 (by rfl) ⟨6474644, by rfl⟩ : syracuseStep 138125749 = 12949289) B12949289
theorem B3498875 : Blo 1553474 3498875 := bstep (se 1 (by rfl) ⟨2624156, by rfl⟩ : syracuseStep 3498875 = 5248313) B5248313
theorem B86205545 : Blo 1553474 86205545 := bstep (se 2 (by rfl) ⟨32327079, by rfl⟩ : syracuseStep 86205545 = 64654159) B64654159
theorem B597795947 : Blo 1553474 597795947 := bstep (se 1 (by rfl) ⟨448346960, by rfl⟩ : syracuseStep 597795947 = 896693921) B896693921
theorem B8520869 : Blo 1553474 8520869 := bstep (se 4 (by rfl) ⟨798831, by rfl⟩ : syracuseStep 8520869 = 1597663) B1597663
theorem B5244155 : Blo 1553474 5244155 := bstep (se 1 (by rfl) ⟨3933116, by rfl⟩ : syracuseStep 5244155 = 7866233) B7866233
theorem B113452811 : Blo 1553474 113452811 := bstep (se 1 (by rfl) ⟨85089608, by rfl⟩ : syracuseStep 113452811 = 170179217) B170179217
theorem B6638537 : Blo 1553474 6638537 := bstep (se 2 (by rfl) ⟨2489451, by rfl⟩ : syracuseStep 6638537 = 4978903) B4978903
theorem B218287315 : Blo 1553474 218287315 := bstep (se 1 (by rfl) ⟨163715486, by rfl⟩ : syracuseStep 218287315 = 327430973) B327430973
theorem B11964343 : Blo 1553474 11964343 := bstep (se 1 (by rfl) ⟨8973257, by rfl⟩ : syracuseStep 11964343 = 17946515) B17946515
theorem B14947051 : Blo 1553474 14947051 := bstep (se 1 (by rfl) ⟨11210288, by rfl⟩ : syracuseStep 14947051 = 22420577) B22420577
theorem B2331887 : Blo 1553474 2331887 := bstep (se 1 (by rfl) ⟨1748915, by rfl⟩ : syracuseStep 2331887 = 3497831) B3497831
theorem B2332007 : Blo 1553474 2332007 := bstep (se 1 (by rfl) ⟨1749005, by rfl⟩ : syracuseStep 2332007 = 3498011) B3498011
theorem B1553855 : Blo 1553474 1553855 := bstep (se 1 (by rfl) ⟨1165391, by rfl⟩ : syracuseStep 1553855 = 2330783) B2330783
theorem B1553887 : Blo 1553474 1553887 := bstep (se 1 (by rfl) ⟨1165415, by rfl⟩ : syracuseStep 1553887 = 2330831) B2330831
theorem B1555175 : Blo 1553474 1555175 := bstep (se 1 (by rfl) ⟨1166381, by rfl⟩ : syracuseStep 1555175 = 2332763) B2332763
theorem B6643559 : Blo 1553474 6643559 := bstep (se 1 (by rfl) ⟨4982669, by rfl⟩ : syracuseStep 6643559 = 9965339) B9965339
theorem B1164199013 : Blo 1553474 1164199013 := bstep (se 4 (by rfl) ⟨109143657, by rfl⟩ : syracuseStep 1164199013 = 218287315) B218287315
theorem B4425691 : Blo 1553474 4425691 := bstep (se 1 (by rfl) ⟨3319268, by rfl⟩ : syracuseStep 4425691 = 6638537) B6638537
theorem B15952457 : Blo 1553474 15952457 := bstep (se 2 (by rfl) ⟨5982171, by rfl⟩ : syracuseStep 15952457 = 11964343) B11964343
theorem B184167665 : Blo 1553474 184167665 := bstep (se 2 (by rfl) ⟨69062874, by rfl⟩ : syracuseStep 184167665 = 138125749) B138125749
theorem B57470363 : Blo 1553474 57470363 := bstep (se 1 (by rfl) ⟨43102772, by rfl⟩ : syracuseStep 57470363 = 86205545) B86205545
theorem B5680579 : Blo 1553474 5680579 := bstep (se 1 (by rfl) ⟨4260434, by rfl⟩ : syracuseStep 5680579 = 8520869) B8520869
theorem B17716157 : Blo 1553474 17716157 := bstep (se 3 (by rfl) ⟨3321779, by rfl⟩ : syracuseStep 17716157 = 6643559) B6643559
theorem B3495689 : Blo 1553474 3495689 := bstep (se 2 (by rfl) ⟨1310883, by rfl⟩ : syracuseStep 3495689 = 2621767) B2621767
theorem B2332583 : Blo 1553474 2332583 := bstep (se 1 (by rfl) ⟨1749437, by rfl⟩ : syracuseStep 2332583 = 3498875) B3498875
theorem B398530631 : Blo 1553474 398530631 := bstep (se 1 (by rfl) ⟨298897973, by rfl⟩ : syracuseStep 398530631 = 597795947) B597795947
theorem B1554591 : Blo 1553474 1554591 := bstep (se 1 (by rfl) ⟨1165943, by rfl⟩ : syracuseStep 1554591 = 2331887) B2331887
theorem B3496103 : Blo 1553474 3496103 := bstep (se 1 (by rfl) ⟨2622077, by rfl⟩ : syracuseStep 3496103 = 5244155) B5244155
theorem B1554671 : Blo 1553474 1554671 := bstep (se 1 (by rfl) ⟨1166003, by rfl⟩ : syracuseStep 1554671 = 2332007) B2332007
theorem B19929401 : Blo 1553474 19929401 := bstep (se 2 (by rfl) ⟨7473525, by rfl⟩ : syracuseStep 19929401 = 14947051) B14947051
theorem B75635207 : Blo 1553474 75635207 := bstep (se 1 (by rfl) ⟨56726405, by rfl⟩ : syracuseStep 75635207 = 113452811) B113452811
theorem B50423471 : Blo 1553474 50423471 := bstep (se 1 (by rfl) ⟨37817603, by rfl⟩ : syracuseStep 50423471 = 75635207) B75635207
theorem B10634971 : Blo 1553474 10634971 := bstep (se 1 (by rfl) ⟨7976228, by rfl⟩ : syracuseStep 10634971 = 15952457) B15952457
theorem B5900921 : Blo 1553474 5900921 := bstep (se 2 (by rfl) ⟨2212845, by rfl⟩ : syracuseStep 5900921 = 4425691) B4425691
theorem B2330459 : Blo 1553474 2330459 := bstep (se 1 (by rfl) ⟨1747844, by rfl⟩ : syracuseStep 2330459 = 3495689) B3495689
theorem B265687087 : Blo 1553474 265687087 := bstep (se 1 (by rfl) ⟨199265315, by rfl⟩ : syracuseStep 265687087 = 398530631) B398530631
theorem B2330735 : Blo 1553474 2330735 := bstep (se 1 (by rfl) ⟨1748051, by rfl⟩ : syracuseStep 2330735 = 3496103) B3496103
theorem B7574105 : Blo 1553474 7574105 := bstep (se 2 (by rfl) ⟨2840289, by rfl⟩ : syracuseStep 7574105 = 5680579) B5680579
theorem B122778443 : Blo 1553474 122778443 := bstep (se 1 (by rfl) ⟨92083832, by rfl⟩ : syracuseStep 122778443 = 184167665) B184167665
theorem B11810771 : Blo 1553474 11810771 := bstep (se 1 (by rfl) ⟨8858078, by rfl⟩ : syracuseStep 11810771 = 17716157) B17716157
theorem B776132675 : Blo 1553474 776132675 := bstep (se 1 (by rfl) ⟨582099506, by rfl⟩ : syracuseStep 776132675 = 1164199013) B1164199013
theorem B1555055 : Blo 1553474 1555055 := bstep (se 1 (by rfl) ⟨1166291, by rfl⟩ : syracuseStep 1555055 = 2332583) B2332583
theorem B13286267 : Blo 1553474 13286267 := bstep (se 1 (by rfl) ⟨9964700, by rfl⟩ : syracuseStep 13286267 = 19929401) B19929401
theorem B38313575 : Blo 1553474 38313575 := bstep (se 1 (by rfl) ⟨28735181, by rfl⟩ : syracuseStep 38313575 = 57470363) B57470363
theorem B7873847 : Blo 1553474 7873847 := bstep (se 1 (by rfl) ⟨5905385, by rfl⟩ : syracuseStep 7873847 = 11810771) B11810771
theorem B3933947 : Blo 1553474 3933947 := bstep (se 1 (by rfl) ⟨2950460, by rfl⟩ : syracuseStep 3933947 = 5900921) B5900921
theorem B8857511 : Blo 1553474 8857511 := bstep (se 1 (by rfl) ⟨6643133, by rfl⟩ : syracuseStep 8857511 = 13286267) B13286267
theorem B354249449 : Blo 1553474 354249449 := bstep (se 2 (by rfl) ⟨132843543, by rfl⟩ : syracuseStep 354249449 = 265687087) B265687087
theorem B33615647 : Blo 1553474 33615647 := bstep (se 1 (by rfl) ⟨25211735, by rfl⟩ : syracuseStep 33615647 = 50423471) B50423471
theorem B20197613 : Blo 1553474 20197613 := bstep (se 3 (by rfl) ⟨3787052, by rfl⟩ : syracuseStep 20197613 = 7574105) B7574105
theorem B1553639 : Blo 1553474 1553639 := bstep (se 1 (by rfl) ⟨1165229, by rfl⟩ : syracuseStep 1553639 = 2330459) B2330459
theorem B1553823 : Blo 1553474 1553823 := bstep (se 1 (by rfl) ⟨1165367, by rfl⟩ : syracuseStep 1553823 = 2330735) B2330735
theorem B81852295 : Blo 1553474 81852295 := bstep (se 1 (by rfl) ⟨61389221, by rfl⟩ : syracuseStep 81852295 = 122778443) B122778443
theorem B517421783 : Blo 1553474 517421783 := bstep (se 1 (by rfl) ⟨388066337, by rfl⟩ : syracuseStep 517421783 = 776132675) B776132675
theorem B14179961 : Blo 1553474 14179961 := bstep (se 2 (by rfl) ⟨5317485, by rfl⟩ : syracuseStep 14179961 = 10634971) B10634971
theorem B25542383 : Blo 1553474 25542383 := bstep (se 1 (by rfl) ⟨19156787, by rfl⟩ : syracuseStep 25542383 = 38313575) B38313575
theorem B2622631 : Blo 1553474 2622631 := bstep (se 1 (by rfl) ⟨1966973, by rfl⟩ : syracuseStep 2622631 = 3933947) B3933947
theorem B109136393 : Blo 1553474 109136393 := bstep (se 2 (by rfl) ⟨40926147, by rfl⟩ : syracuseStep 109136393 = 81852295) B81852295
theorem B1379791421 : Blo 1553474 1379791421 := bstep (se 3 (by rfl) ⟨258710891, by rfl⟩ : syracuseStep 1379791421 = 517421783) B517421783
theorem B68113021 : Blo 1553474 68113021 := bstep (se 3 (by rfl) ⟨12771191, by rfl⟩ : syracuseStep 68113021 = 25542383) B25542383
theorem B22410431 : Blo 1553474 22410431 := bstep (se 1 (by rfl) ⟨16807823, by rfl⟩ : syracuseStep 22410431 = 33615647) B33615647
theorem B13465075 : Blo 1553474 13465075 := bstep (se 1 (by rfl) ⟨10098806, by rfl⟩ : syracuseStep 13465075 = 20197613) B20197613
theorem B5249231 : Blo 1553474 5249231 := bstep (se 1 (by rfl) ⟨3936923, by rfl⟩ : syracuseStep 5249231 = 7873847) B7873847
theorem B5905007 : Blo 1553474 5905007 := bstep (se 1 (by rfl) ⟨4428755, by rfl⟩ : syracuseStep 5905007 = 8857511) B8857511
theorem B37813229 : Blo 1553474 37813229 := bstep (se 3 (by rfl) ⟨7089980, by rfl⟩ : syracuseStep 37813229 = 14179961) B14179961
theorem B236166299 : Blo 1553474 236166299 := bstep (se 1 (by rfl) ⟨177124724, by rfl⟩ : syracuseStep 236166299 = 354249449) B354249449
theorem B90817361 : Blo 1553474 90817361 := bstep (se 2 (by rfl) ⟨34056510, by rfl⟩ : syracuseStep 90817361 = 68113021) B68113021
theorem B3499487 : Blo 1553474 3499487 := bstep (se 1 (by rfl) ⟨2624615, by rfl⟩ : syracuseStep 3499487 = 5249231) B5249231
theorem B25208819 : Blo 1553474 25208819 := bstep (se 1 (by rfl) ⟨18906614, by rfl⟩ : syracuseStep 25208819 = 37813229) B37813229
theorem B157444199 : Blo 1553474 157444199 := bstep (se 1 (by rfl) ⟨118083149, by rfl⟩ : syracuseStep 157444199 = 236166299) B236166299
theorem B72757595 : Blo 1553474 72757595 := bstep (se 1 (by rfl) ⟨54568196, by rfl⟩ : syracuseStep 72757595 = 109136393) B109136393
theorem B3936671 : Blo 1553474 3936671 := bstep (se 1 (by rfl) ⟨2952503, by rfl⟩ : syracuseStep 3936671 = 5905007) B5905007
theorem B17953433 : Blo 1553474 17953433 := bstep (se 2 (by rfl) ⟨6732537, by rfl⟩ : syracuseStep 17953433 = 13465075) B13465075
theorem B919860947 : Blo 1553474 919860947 := bstep (se 1 (by rfl) ⟨689895710, by rfl⟩ : syracuseStep 919860947 = 1379791421) B1379791421
theorem B14940287 : Blo 1553474 14940287 := bstep (se 1 (by rfl) ⟨11205215, by rfl⟩ : syracuseStep 14940287 = 22410431) B22410431
theorem B3496841 : Blo 1553474 3496841 := bstep (se 2 (by rfl) ⟨1311315, by rfl⟩ : syracuseStep 3496841 = 2622631) B2622631
theorem B48505063 : Blo 1553474 48505063 := bstep (se 1 (by rfl) ⟨36378797, by rfl⟩ : syracuseStep 48505063 = 72757595) B72757595
theorem B11968955 : Blo 1553474 11968955 := bstep (se 1 (by rfl) ⟨8976716, by rfl⟩ : syracuseStep 11968955 = 17953433) B17953433
theorem B2624447 : Blo 1553474 2624447 := bstep (se 1 (by rfl) ⟨1968335, by rfl⟩ : syracuseStep 2624447 = 3936671) B3936671
theorem B613240631 : Blo 1553474 613240631 := bstep (se 1 (by rfl) ⟨459930473, by rfl⟩ : syracuseStep 613240631 = 919860947) B919860947
theorem B16805879 : Blo 1553474 16805879 := bstep (se 1 (by rfl) ⟨12604409, by rfl⟩ : syracuseStep 16805879 = 25208819) B25208819
theorem B2331227 : Blo 1553474 2331227 := bstep (se 1 (by rfl) ⟨1748420, by rfl⟩ : syracuseStep 2331227 = 3496841) B3496841
theorem B60544907 : Blo 1553474 60544907 := bstep (se 1 (by rfl) ⟨45408680, by rfl⟩ : syracuseStep 60544907 = 90817361) B90817361
theorem B2332991 : Blo 1553474 2332991 := bstep (se 1 (by rfl) ⟨1749743, by rfl⟩ : syracuseStep 2332991 = 3499487) B3499487
theorem B104962799 : Blo 1553474 104962799 := bstep (se 1 (by rfl) ⟨78722099, by rfl⟩ : syracuseStep 104962799 = 157444199) B157444199
theorem B9960191 : Blo 1553474 9960191 := bstep (se 1 (by rfl) ⟨7470143, by rfl⟩ : syracuseStep 9960191 = 14940287) B14940287
theorem B7979303 : Blo 1553474 7979303 := bstep (se 1 (by rfl) ⟨5984477, by rfl⟩ : syracuseStep 7979303 = 11968955) B11968955
theorem B40363271 : Blo 1553474 40363271 := bstep (se 1 (by rfl) ⟨30272453, by rfl⟩ : syracuseStep 40363271 = 60544907) B60544907
theorem B6640127 : Blo 1553474 6640127 := bstep (se 1 (by rfl) ⟨4980095, by rfl⟩ : syracuseStep 6640127 = 9960191) B9960191
theorem B1749631 : Blo 1553474 1749631 := bstep (se 1 (by rfl) ⟨1312223, by rfl⟩ : syracuseStep 1749631 = 2624447) B2624447
theorem B408827087 : Blo 1553474 408827087 := bstep (se 1 (by rfl) ⟨306620315, by rfl⟩ : syracuseStep 408827087 = 613240631) B613240631
theorem B11203919 : Blo 1553474 11203919 := bstep (se 1 (by rfl) ⟨8402939, by rfl⟩ : syracuseStep 11203919 = 16805879) B16805879
theorem B64673417 : Blo 1553474 64673417 := bstep (se 2 (by rfl) ⟨24252531, by rfl⟩ : syracuseStep 64673417 = 48505063) B48505063
theorem B1554151 : Blo 1553474 1554151 := bstep (se 1 (by rfl) ⟨1165613, by rfl⟩ : syracuseStep 1554151 = 2331227) B2331227
theorem B1555327 : Blo 1553474 1555327 := bstep (se 1 (by rfl) ⟨1166495, by rfl⟩ : syracuseStep 1555327 = 2332991) B2332991
theorem B69975199 : Blo 1553474 69975199 := bstep (se 1 (by rfl) ⟨52481399, by rfl⟩ : syracuseStep 69975199 = 104962799) B104962799
theorem B43115611 : Blo 1553474 43115611 := bstep (se 1 (by rfl) ⟨32336708, by rfl⟩ : syracuseStep 43115611 = 64673417) B64673417
theorem B93300265 : Blo 1553474 93300265 := bstep (se 2 (by rfl) ⟨34987599, by rfl⟩ : syracuseStep 93300265 = 69975199) B69975199
theorem B4426751 : Blo 1553474 4426751 := bstep (se 1 (by rfl) ⟨3320063, by rfl⟩ : syracuseStep 4426751 = 6640127) B6640127
theorem B21278141 : Blo 1553474 21278141 := bstep (se 3 (by rfl) ⟨3989651, by rfl⟩ : syracuseStep 21278141 = 7979303) B7979303
theorem B272551391 : Blo 1553474 272551391 := bstep (se 1 (by rfl) ⟨204413543, by rfl⟩ : syracuseStep 272551391 = 408827087) B408827087
theorem B2332841 : Blo 1553474 2332841 := bstep (se 2 (by rfl) ⟨874815, by rfl⟩ : syracuseStep 2332841 = 1749631) B1749631
theorem B26908847 : Blo 1553474 26908847 := bstep (se 1 (by rfl) ⟨20181635, by rfl⟩ : syracuseStep 26908847 = 40363271) B40363271
theorem B7469279 : Blo 1553474 7469279 := bstep (se 1 (by rfl) ⟨5601959, by rfl⟩ : syracuseStep 7469279 = 11203919) B11203919
theorem B2951167 : Blo 1553474 2951167 := bstep (se 1 (by rfl) ⟨2213375, by rfl⟩ : syracuseStep 2951167 = 4426751) B4426751
theorem B181700927 : Blo 1553474 181700927 := bstep (se 1 (by rfl) ⟨136275695, by rfl⟩ : syracuseStep 181700927 = 272551391) B272551391
theorem B497601413 : Blo 1553474 497601413 := bstep (se 4 (by rfl) ⟨46650132, by rfl⟩ : syracuseStep 497601413 = 93300265) B93300265
theorem B57487481 : Blo 1553474 57487481 := bstep (se 2 (by rfl) ⟨21557805, by rfl⟩ : syracuseStep 57487481 = 43115611) B43115611
theorem B14185427 : Blo 1553474 14185427 := bstep (se 1 (by rfl) ⟨10639070, by rfl⟩ : syracuseStep 14185427 = 21278141) B21278141
theorem B1555227 : Blo 1553474 1555227 := bstep (se 1 (by rfl) ⟨1166420, by rfl⟩ : syracuseStep 1555227 = 2332841) B2332841
theorem B17939231 : Blo 1553474 17939231 := bstep (se 1 (by rfl) ⟨13454423, by rfl⟩ : syracuseStep 17939231 = 26908847) B26908847
theorem B4979519 : Blo 1553474 4979519 := bstep (se 1 (by rfl) ⟨3734639, by rfl⟩ : syracuseStep 4979519 = 7469279) B7469279
theorem B3319679 : Blo 1553474 3319679 := bstep (se 1 (by rfl) ⟨2489759, by rfl⟩ : syracuseStep 3319679 = 4979519) B4979519
theorem B3934889 : Blo 1553474 3934889 := bstep (se 2 (by rfl) ⟨1475583, by rfl⟩ : syracuseStep 3934889 = 2951167) B2951167
theorem B38324987 : Blo 1553474 38324987 := bstep (se 1 (by rfl) ⟨28743740, by rfl⟩ : syracuseStep 38324987 = 57487481) B57487481
theorem B37827805 : Blo 1553474 37827805 := bstep (se 3 (by rfl) ⟨7092713, by rfl⟩ : syracuseStep 37827805 = 14185427) B14185427
theorem B121133951 : Blo 1553474 121133951 := bstep (se 1 (by rfl) ⟨90850463, by rfl⟩ : syracuseStep 121133951 = 181700927) B181700927
theorem B11959487 : Blo 1553474 11959487 := bstep (se 1 (by rfl) ⟨8969615, by rfl⟩ : syracuseStep 11959487 = 17939231) B17939231
theorem B331734275 : Blo 1553474 331734275 := bstep (se 1 (by rfl) ⟨248800706, by rfl⟩ : syracuseStep 331734275 = 497601413) B497601413
theorem B2213119 : Blo 1553474 2213119 := bstep (se 1 (by rfl) ⟨1659839, by rfl⟩ : syracuseStep 2213119 = 3319679) B3319679
theorem B2623259 : Blo 1553474 2623259 := bstep (se 1 (by rfl) ⟨1967444, by rfl⟩ : syracuseStep 2623259 = 3934889) B3934889
theorem B7972991 : Blo 1553474 7972991 := bstep (se 1 (by rfl) ⟨5979743, by rfl⟩ : syracuseStep 7972991 = 11959487) B11959487
theorem B221156183 : Blo 1553474 221156183 := bstep (se 1 (by rfl) ⟨165867137, by rfl⟩ : syracuseStep 221156183 = 331734275) B331734275
theorem B50437073 : Blo 1553474 50437073 := bstep (se 2 (by rfl) ⟨18913902, by rfl⟩ : syracuseStep 50437073 = 37827805) B37827805
theorem B25549991 : Blo 1553474 25549991 := bstep (se 1 (by rfl) ⟨19162493, by rfl⟩ : syracuseStep 25549991 = 38324987) B38324987
theorem B80755967 : Blo 1553474 80755967 := bstep (se 1 (by rfl) ⟨60566975, by rfl⟩ : syracuseStep 80755967 = 121133951) B121133951
theorem B2950825 : Blo 1553474 2950825 := bstep (se 2 (by rfl) ⟨1106559, by rfl⟩ : syracuseStep 2950825 = 2213119) B2213119
theorem B17033327 : Blo 1553474 17033327 := bstep (se 1 (by rfl) ⟨12774995, by rfl⟩ : syracuseStep 17033327 = 25549991) B25549991
theorem B1748839 : Blo 1553474 1748839 := bstep (se 1 (by rfl) ⟨1311629, by rfl⟩ : syracuseStep 1748839 = 2623259) B2623259
theorem B33624715 : Blo 1553474 33624715 := bstep (se 1 (by rfl) ⟨25218536, by rfl⟩ : syracuseStep 33624715 = 50437073) B50437073
theorem B147437455 : Blo 1553474 147437455 := bstep (se 1 (by rfl) ⟨110578091, by rfl⟩ : syracuseStep 147437455 = 221156183) B221156183
theorem B5315327 : Blo 1553474 5315327 := bstep (se 1 (by rfl) ⟨3986495, by rfl⟩ : syracuseStep 5315327 = 7972991) B7972991
theorem B53837311 : Blo 1553474 53837311 := bstep (se 1 (by rfl) ⟨40377983, by rfl⟩ : syracuseStep 53837311 = 80755967) B80755967
theorem B11355551 : Blo 1553474 11355551 := bstep (se 1 (by rfl) ⟨8516663, by rfl⟩ : syracuseStep 11355551 = 17033327) B17033327
theorem B3934433 : Blo 1553474 3934433 := bstep (se 2 (by rfl) ⟨1475412, by rfl⟩ : syracuseStep 3934433 = 2950825) B2950825
theorem B3543551 : Blo 1553474 3543551 := bstep (se 1 (by rfl) ⟨2657663, by rfl⟩ : syracuseStep 3543551 = 5315327) B5315327
theorem B71783081 : Blo 1553474 71783081 := bstep (se 2 (by rfl) ⟨26918655, by rfl⟩ : syracuseStep 71783081 = 53837311) B53837311
theorem B2331785 : Blo 1553474 2331785 := bstep (se 2 (by rfl) ⟨874419, by rfl⟩ : syracuseStep 2331785 = 1748839) B1748839
theorem B44832953 : Blo 1553474 44832953 := bstep (se 2 (by rfl) ⟨16812357, by rfl⟩ : syracuseStep 44832953 = 33624715) B33624715
theorem B196583273 : Blo 1553474 196583273 := bstep (se 2 (by rfl) ⟨73718727, by rfl⟩ : syracuseStep 196583273 = 147437455) B147437455
theorem B7570367 : Blo 1553474 7570367 := bstep (se 1 (by rfl) ⟨5677775, by rfl⟩ : syracuseStep 7570367 = 11355551) B11355551
theorem B2622955 : Blo 1553474 2622955 := bstep (se 1 (by rfl) ⟨1967216, by rfl⟩ : syracuseStep 2622955 = 3934433) B3934433
theorem B2362367 : Blo 1553474 2362367 := bstep (se 1 (by rfl) ⟨1771775, by rfl⟩ : syracuseStep 2362367 = 3543551) B3543551
theorem B29888635 : Blo 1553474 29888635 := bstep (se 1 (by rfl) ⟨22416476, by rfl⟩ : syracuseStep 29888635 = 44832953) B44832953
theorem B47855387 : Blo 1553474 47855387 := bstep (se 1 (by rfl) ⟨35891540, by rfl⟩ : syracuseStep 47855387 = 71783081) B71783081
theorem B1554523 : Blo 1553474 1554523 := bstep (se 1 (by rfl) ⟨1165892, by rfl⟩ : syracuseStep 1554523 = 2331785) B2331785
theorem B131055515 : Blo 1553474 131055515 := bstep (se 1 (by rfl) ⟨98291636, by rfl⟩ : syracuseStep 131055515 = 196583273) B196583273
theorem B5046911 : Blo 1553474 5046911 := bstep (se 1 (by rfl) ⟨3785183, by rfl⟩ : syracuseStep 5046911 = 7570367) B7570367
theorem B1574911 : Blo 1553474 1574911 := bstep (se 1 (by rfl) ⟨1181183, by rfl⟩ : syracuseStep 1574911 = 2362367) B2362367
theorem B87370343 : Blo 1553474 87370343 := bstep (se 1 (by rfl) ⟨65527757, by rfl⟩ : syracuseStep 87370343 = 131055515) B131055515
theorem B31903591 : Blo 1553474 31903591 := bstep (se 1 (by rfl) ⟨23927693, by rfl⟩ : syracuseStep 31903591 = 47855387) B47855387
theorem B39851513 : Blo 1553474 39851513 := bstep (se 2 (by rfl) ⟨14944317, by rfl⟩ : syracuseStep 39851513 = 29888635) B29888635
theorem B3497273 : Blo 1553474 3497273 := bstep (se 2 (by rfl) ⟨1311477, by rfl⟩ : syracuseStep 3497273 = 2622955) B2622955
theorem B26567675 : Blo 1553474 26567675 := bstep (se 1 (by rfl) ⟨19925756, by rfl⟩ : syracuseStep 26567675 = 39851513) B39851513
theorem B58246895 : Blo 1553474 58246895 := bstep (se 1 (by rfl) ⟨43685171, by rfl⟩ : syracuseStep 58246895 = 87370343) B87370343
theorem B2099881 : Blo 1553474 2099881 := bstep (se 2 (by rfl) ⟨787455, by rfl⟩ : syracuseStep 2099881 = 1574911) B1574911
theorem B2331515 : Blo 1553474 2331515 := bstep (se 1 (by rfl) ⟨1748636, by rfl⟩ : syracuseStep 2331515 = 3497273) B3497273
theorem B42538121 : Blo 1553474 42538121 := bstep (se 2 (by rfl) ⟨15951795, by rfl⟩ : syracuseStep 42538121 = 31903591) B31903591
theorem B3364607 : Blo 1553474 3364607 := bstep (se 1 (by rfl) ⟨2523455, by rfl⟩ : syracuseStep 3364607 = 5046911) B5046911
theorem B17711783 : Blo 1553474 17711783 := bstep (se 1 (by rfl) ⟨13283837, by rfl⟩ : syracuseStep 17711783 = 26567675) B26567675
theorem B155325053 : Blo 1553474 155325053 := bstep (se 3 (by rfl) ⟨29123447, by rfl⟩ : syracuseStep 155325053 = 58246895) B58246895
theorem B1554343 : Blo 1553474 1554343 := bstep (se 1 (by rfl) ⟨1165757, by rfl⟩ : syracuseStep 1554343 = 2331515) B2331515
theorem B28358747 : Blo 1553474 28358747 := bstep (se 1 (by rfl) ⟨21269060, by rfl⟩ : syracuseStep 28358747 = 42538121) B42538121
theorem B2799841 : Blo 1553474 2799841 := bstep (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) B2099881
theorem B2243071 : Blo 1553474 2243071 := bstep (se 1 (by rfl) ⟨1682303, by rfl⟩ : syracuseStep 2243071 = 3364607) B3364607
theorem B11963045 : Blo 1553474 11963045 := bstep (se 4 (by rfl) ⟨1121535, by rfl⟩ : syracuseStep 11963045 = 2243071) B2243071
theorem B103550035 : Blo 1553474 103550035 := bstep (se 1 (by rfl) ⟨77662526, by rfl⟩ : syracuseStep 103550035 = 155325053) B155325053
theorem B11807855 : Blo 1553474 11807855 := bstep (se 1 (by rfl) ⟨8855891, by rfl⟩ : syracuseStep 11807855 = 17711783) B17711783
theorem B3733121 : Blo 1553474 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B18905831 : Blo 1553474 18905831 := bstep (se 1 (by rfl) ⟨14179373, by rfl⟩ : syracuseStep 18905831 = 28358747) B28358747
theorem B7975363 : Blo 1553474 7975363 := bstep (se 1 (by rfl) ⟨5981522, by rfl⟩ : syracuseStep 7975363 = 11963045) B11963045
theorem B12603887 : Blo 1553474 12603887 := bstep (se 1 (by rfl) ⟨9452915, by rfl⟩ : syracuseStep 12603887 = 18905831) B18905831
theorem B2488747 : Blo 1553474 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B138066713 : Blo 1553474 138066713 := bstep (se 2 (by rfl) ⟨51775017, by rfl⟩ : syracuseStep 138066713 = 103550035) B103550035
theorem B7871903 : Blo 1553474 7871903 := bstep (se 1 (by rfl) ⟨5903927, by rfl⟩ : syracuseStep 7871903 = 11807855) B11807855
theorem B3318329 : Blo 1553474 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B10633817 : Blo 1553474 10633817 := bstep (se 2 (by rfl) ⟨3987681, by rfl⟩ : syracuseStep 10633817 = 7975363) B7975363
theorem B5247935 : Blo 1553474 5247935 := bstep (se 1 (by rfl) ⟨3935951, by rfl⟩ : syracuseStep 5247935 = 7871903) B7871903
theorem B8402591 : Blo 1553474 8402591 := bstep (se 1 (by rfl) ⟨6301943, by rfl⟩ : syracuseStep 8402591 = 12603887) B12603887
theorem B92044475 : Blo 1553474 92044475 := bstep (se 1 (by rfl) ⟨69033356, by rfl⟩ : syracuseStep 92044475 = 138066713) B138066713
theorem B2212219 : Blo 1553474 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B3498623 : Blo 1553474 3498623 := bstep (se 1 (by rfl) ⟨2623967, by rfl⟩ : syracuseStep 3498623 = 5247935) B5247935
theorem B7089211 : Blo 1553474 7089211 := bstep (se 1 (by rfl) ⟨5316908, by rfl⟩ : syracuseStep 7089211 = 10633817) B10633817
theorem B61362983 : Blo 1553474 61362983 := bstep (se 1 (by rfl) ⟨46022237, by rfl⟩ : syracuseStep 61362983 = 92044475) B92044475
theorem B5601727 : Blo 1553474 5601727 := bstep (se 1 (by rfl) ⟨4201295, by rfl⟩ : syracuseStep 5601727 = 8402591) B8402591
theorem B2949625 : Blo 1553474 2949625 := bstep (se 2 (by rfl) ⟨1106109, by rfl⟩ : syracuseStep 2949625 = 2212219) B2212219
theorem B2332415 : Blo 1553474 2332415 := bstep (se 1 (by rfl) ⟨1749311, by rfl⟩ : syracuseStep 2332415 = 3498623) B3498623
theorem B40908655 : Blo 1553474 40908655 := bstep (se 1 (by rfl) ⟨30681491, by rfl⟩ : syracuseStep 40908655 = 61362983) B61362983
theorem B9452281 : Blo 1553474 9452281 := bstep (se 2 (by rfl) ⟨3544605, by rfl⟩ : syracuseStep 9452281 = 7089211) B7089211
theorem B29875877 : Blo 1553474 29875877 := bstep (se 4 (by rfl) ⟨2800863, by rfl⟩ : syracuseStep 29875877 = 5601727) B5601727
theorem B3932833 : Blo 1553474 3932833 := bstep (se 2 (by rfl) ⟨1474812, by rfl⟩ : syracuseStep 3932833 = 2949625) B2949625
theorem B218179493 : Blo 1553474 218179493 := bstep (se 4 (by rfl) ⟨20454327, by rfl⟩ : syracuseStep 218179493 = 40908655) B40908655
theorem B19917251 : Blo 1553474 19917251 := bstep (se 1 (by rfl) ⟨14937938, by rfl⟩ : syracuseStep 19917251 = 29875877) B29875877
theorem B12603041 : Blo 1553474 12603041 := bstep (se 2 (by rfl) ⟨4726140, by rfl⟩ : syracuseStep 12603041 = 9452281) B9452281
theorem B1554943 : Blo 1553474 1554943 := bstep (se 1 (by rfl) ⟨1166207, by rfl⟩ : syracuseStep 1554943 = 2332415) B2332415
theorem B5243777 : Blo 1553474 5243777 := bstep (se 2 (by rfl) ⟨1966416, by rfl⟩ : syracuseStep 5243777 = 3932833) B3932833
theorem B145452995 : Blo 1553474 145452995 := bstep (se 1 (by rfl) ⟨109089746, by rfl⟩ : syracuseStep 145452995 = 218179493) B218179493
theorem B8402027 : Blo 1553474 8402027 := bstep (se 1 (by rfl) ⟨6301520, by rfl⟩ : syracuseStep 8402027 = 12603041) B12603041
theorem B13278167 : Blo 1553474 13278167 := bstep (se 1 (by rfl) ⟨9958625, by rfl⟩ : syracuseStep 13278167 = 19917251) B19917251
theorem B22405405 : Blo 1553474 22405405 := bstep (se 3 (by rfl) ⟨4201013, by rfl⟩ : syracuseStep 22405405 = 8402027) B8402027
theorem B8852111 : Blo 1553474 8852111 := bstep (se 1 (by rfl) ⟨6639083, by rfl⟩ : syracuseStep 8852111 = 13278167) B13278167
theorem B3495851 : Blo 1553474 3495851 := bstep (se 1 (by rfl) ⟨2621888, by rfl⟩ : syracuseStep 3495851 = 5243777) B5243777
theorem B96968663 : Blo 1553474 96968663 := bstep (se 1 (by rfl) ⟨72726497, by rfl⟩ : syracuseStep 96968663 = 145452995) B145452995
theorem B64645775 : Blo 1553474 64645775 := bstep (se 1 (by rfl) ⟨48484331, by rfl⟩ : syracuseStep 64645775 = 96968663) B96968663
theorem B5901407 : Blo 1553474 5901407 := bstep (se 1 (by rfl) ⟨4426055, by rfl⟩ : syracuseStep 5901407 = 8852111) B8852111
theorem B2330567 : Blo 1553474 2330567 := bstep (se 1 (by rfl) ⟨1747925, by rfl⟩ : syracuseStep 2330567 = 3495851) B3495851
theorem B29873873 : Blo 1553474 29873873 := bstep (se 2 (by rfl) ⟨11202702, by rfl⟩ : syracuseStep 29873873 = 22405405) B22405405
theorem B19915915 : Blo 1553474 19915915 := bstep (se 1 (by rfl) ⟨14936936, by rfl⟩ : syracuseStep 19915915 = 29873873) B29873873
theorem B3934271 : Blo 1553474 3934271 := bstep (se 1 (by rfl) ⟨2950703, by rfl⟩ : syracuseStep 3934271 = 5901407) B5901407
theorem B1553711 : Blo 1553474 1553711 := bstep (se 1 (by rfl) ⟨1165283, by rfl⟩ : syracuseStep 1553711 = 2330567) B2330567
theorem B43097183 : Blo 1553474 43097183 := bstep (se 1 (by rfl) ⟨32322887, by rfl⟩ : syracuseStep 43097183 = 64645775) B64645775
theorem B2622847 : Blo 1553474 2622847 := bstep (se 1 (by rfl) ⟨1967135, by rfl⟩ : syracuseStep 2622847 = 3934271) B3934271
theorem B28731455 : Blo 1553474 28731455 := bstep (se 1 (by rfl) ⟨21548591, by rfl⟩ : syracuseStep 28731455 = 43097183) B43097183
theorem B26554553 : Blo 1553474 26554553 := bstep (se 2 (by rfl) ⟨9957957, by rfl⟩ : syracuseStep 26554553 = 19915915) B19915915
theorem B17703035 : Blo 1553474 17703035 := bstep (se 1 (by rfl) ⟨13277276, by rfl⟩ : syracuseStep 17703035 = 26554553) B26554553
theorem B19154303 : Blo 1553474 19154303 := bstep (se 1 (by rfl) ⟨14365727, by rfl⟩ : syracuseStep 19154303 = 28731455) B28731455
theorem B3497129 : Blo 1553474 3497129 := bstep (se 2 (by rfl) ⟨1311423, by rfl⟩ : syracuseStep 3497129 = 2622847) B2622847
theorem B2331419 : Blo 1553474 2331419 := bstep (se 1 (by rfl) ⟨1748564, by rfl⟩ : syracuseStep 2331419 = 3497129) B3497129
theorem B11802023 : Blo 1553474 11802023 := bstep (se 1 (by rfl) ⟨8851517, by rfl⟩ : syracuseStep 11802023 = 17703035) B17703035
theorem B12769535 : Blo 1553474 12769535 := bstep (se 1 (by rfl) ⟨9577151, by rfl⟩ : syracuseStep 12769535 = 19154303) B19154303
theorem B8513023 : Blo 1553474 8513023 := bstep (se 1 (by rfl) ⟨6384767, by rfl⟩ : syracuseStep 8513023 = 12769535) B12769535
theorem B7868015 : Blo 1553474 7868015 := bstep (se 1 (by rfl) ⟨5901011, by rfl⟩ : syracuseStep 7868015 = 11802023) B11802023
theorem B1554279 : Blo 1553474 1554279 := bstep (se 1 (by rfl) ⟨1165709, by rfl⟩ : syracuseStep 1554279 = 2331419) B2331419
theorem B5245343 : Blo 1553474 5245343 := bstep (se 1 (by rfl) ⟨3934007, by rfl⟩ : syracuseStep 5245343 = 7868015) B7868015
theorem B11350697 : Blo 1553474 11350697 := bstep (se 2 (by rfl) ⟨4256511, by rfl⟩ : syracuseStep 11350697 = 8513023) B8513023
theorem B3496895 : Blo 1553474 3496895 := bstep (se 1 (by rfl) ⟨2622671, by rfl⟩ : syracuseStep 3496895 = 5245343) B5245343
theorem B30268525 : Blo 1553474 30268525 := bstep (se 3 (by rfl) ⟨5675348, by rfl⟩ : syracuseStep 30268525 = 11350697) B11350697
theorem B40358033 : Blo 1553474 40358033 := bstep (se 2 (by rfl) ⟨15134262, by rfl⟩ : syracuseStep 40358033 = 30268525) B30268525
theorem B2331263 : Blo 1553474 2331263 := bstep (se 1 (by rfl) ⟨1748447, by rfl⟩ : syracuseStep 2331263 = 3496895) B3496895
theorem B26905355 : Blo 1553474 26905355 := bstep (se 1 (by rfl) ⟨20179016, by rfl⟩ : syracuseStep 26905355 = 40358033) B40358033
theorem B1554175 : Blo 1553474 1554175 := bstep (se 1 (by rfl) ⟨1165631, by rfl⟩ : syracuseStep 1554175 = 2331263) B2331263
theorem B17936903 : Blo 1553474 17936903 := bstep (se 1 (by rfl) ⟨13452677, by rfl⟩ : syracuseStep 17936903 = 26905355) B26905355
theorem B47831741 : Blo 1553474 47831741 := bstep (se 3 (by rfl) ⟨8968451, by rfl⟩ : syracuseStep 47831741 = 17936903) B17936903
theorem B31887827 : Blo 1553474 31887827 := bstep (se 1 (by rfl) ⟨23915870, by rfl⟩ : syracuseStep 31887827 = 47831741) B47831741
theorem B21258551 : Blo 1553474 21258551 := bstep (se 1 (by rfl) ⟨15943913, by rfl⟩ : syracuseStep 21258551 = 31887827) B31887827
theorem B56689469 : Blo 1553474 56689469 := bstep (se 3 (by rfl) ⟨10629275, by rfl⟩ : syracuseStep 56689469 = 21258551) B21258551
theorem B37792979 : Blo 1553474 37792979 := bstep (se 1 (by rfl) ⟨28344734, by rfl⟩ : syracuseStep 37792979 = 56689469) B56689469
theorem B25195319 : Blo 1553474 25195319 := bstep (se 1 (by rfl) ⟨18896489, by rfl⟩ : syracuseStep 25195319 = 37792979) B37792979
theorem B16796879 : Blo 1553474 16796879 := bstep (se 1 (by rfl) ⟨12597659, by rfl⟩ : syracuseStep 16796879 = 25195319) B25195319
theorem B11197919 : Blo 1553474 11197919 := bstep (se 1 (by rfl) ⟨8398439, by rfl⟩ : syracuseStep 11197919 = 16796879) B16796879
theorem B7465279 : Blo 1553474 7465279 := bstep (se 1 (by rfl) ⟨5598959, by rfl⟩ : syracuseStep 7465279 = 11197919) B11197919
theorem B9953705 : Blo 1553474 9953705 := bstep (se 2 (by rfl) ⟨3732639, by rfl⟩ : syracuseStep 9953705 = 7465279) B7465279
theorem B6635803 : Blo 1553474 6635803 := bstep (se 1 (by rfl) ⟨4976852, by rfl⟩ : syracuseStep 6635803 = 9953705) B9953705
theorem B8847737 : Blo 1553474 8847737 := bstep (se 2 (by rfl) ⟨3317901, by rfl⟩ : syracuseStep 8847737 = 6635803) B6635803
theorem B5898491 : Blo 1553474 5898491 := bstep (se 1 (by rfl) ⟨4423868, by rfl⟩ : syracuseStep 5898491 = 8847737) B8847737
theorem B3932327 : Blo 1553474 3932327 := bstep (se 1 (by rfl) ⟨2949245, by rfl⟩ : syracuseStep 3932327 = 5898491) B5898491
theorem B2621551 : Blo 1553474 2621551 := bstep (se 1 (by rfl) ⟨1966163, by rfl⟩ : syracuseStep 2621551 = 3932327) B3932327
theorem B3495401 : Blo 1553474 3495401 := bstep (se 2 (by rfl) ⟨1310775, by rfl⟩ : syracuseStep 3495401 = 2621551) B2621551
theorem B2330267 : Blo 1553474 2330267 := bstep (se 1 (by rfl) ⟨1747700, by rfl⟩ : syracuseStep 2330267 = 3495401) B3495401
theorem B1553511 : Blo 1553474 1553511 := bstep (se 1 (by rfl) ⟨1165133, by rfl⟩ : syracuseStep 1553511 = 2330267) B2330267

theorem C0 (j : ℕ) (h1 : 388368 ≤ j) (h2 : j ≤ 388867) : Blo 1553474 (4 * j + 3) := by
  interval_cases j
  · exact B1553475
  · exact B1553479
  · exact B1553483
  · exact B1553487
  · exact B1553491
  · exact B1553495
  · exact B1553499
  · exact B1553503
  · exact B1553507
  · exact B1553511
  · exact B1553515
  · exact B1553519
  · exact B1553523
  · exact B1553527
  · exact B1553531
  · exact B1553535
  · exact B1553539
  · exact B1553543
  · exact B1553547
  · exact B1553551
  · exact B1553555
  · exact B1553559
  · exact B1553563
  · exact B1553567
  · exact B1553571
  · exact B1553575
  · exact B1553579
  · exact B1553583
  · exact B1553587
  · exact B1553591
  · exact B1553595
  · exact B1553599
  · exact B1553603
  · exact B1553607
  · exact B1553611
  · exact B1553615
  · exact B1553619
  · exact B1553623
  · exact B1553627
  · exact B1553631
  · exact B1553635
  · exact B1553639
  · exact B1553643
  · exact B1553647
  · exact B1553651
  · exact B1553655
  · exact B1553659
  · exact B1553663
  · exact B1553667
  · exact B1553671
  · exact B1553675
  · exact B1553679
  · exact B1553683
  · exact B1553687
  · exact B1553691
  · exact B1553695
  · exact B1553699
  · exact B1553703
  · exact B1553707
  · exact B1553711
  · exact B1553715
  · exact B1553719
  · exact B1553723
  · exact B1553727
  · exact B1553731
  · exact B1553735
  · exact B1553739
  · exact B1553743
  · exact B1553747
  · exact B1553751
  · exact B1553755
  · exact B1553759
  · exact B1553763
  · exact B1553767
  · exact B1553771
  · exact B1553775
  · exact B1553779
  · exact B1553783
  · exact B1553787
  · exact B1553791
  · exact B1553795
  · exact B1553799
  · exact B1553803
  · exact B1553807
  · exact B1553811
  · exact B1553815
  · exact B1553819
  · exact B1553823
  · exact B1553827
  · exact B1553831
  · exact B1553835
  · exact B1553839
  · exact B1553843
  · exact B1553847
  · exact B1553851
  · exact B1553855
  · exact B1553859
  · exact B1553863
  · exact B1553867
  · exact B1553871
  · exact B1553875
  · exact B1553879
  · exact B1553883
  · exact B1553887
  · exact B1553891
  · exact B1553895
  · exact B1553899
  · exact B1553903
  · exact B1553907
  · exact B1553911
  · exact B1553915
  · exact B1553919
  · exact B1553923
  · exact B1553927
  · exact B1553931
  · exact B1553935
  · exact B1553939
  · exact B1553943
  · exact B1553947
  · exact B1553951
  · exact B1553955
  · exact B1553959
  · exact B1553963
  · exact B1553967
  · exact B1553971
  · exact B1553975
  · exact B1553979
  · exact B1553983
  · exact B1553987
  · exact B1553991
  · exact B1553995
  · exact B1553999
  · exact B1554003
  · exact B1554007
  · exact B1554011
  · exact B1554015
  · exact B1554019
  · exact B1554023
  · exact B1554027
  · exact B1554031
  · exact B1554035
  · exact B1554039
  · exact B1554043
  · exact B1554047
  · exact B1554051
  · exact B1554055
  · exact B1554059
  · exact B1554063
  · exact B1554067
  · exact B1554071
  · exact B1554075
  · exact B1554079
  · exact B1554083
  · exact B1554087
  · exact B1554091
  · exact B1554095
  · exact B1554099
  · exact B1554103
  · exact B1554107
  · exact B1554111
  · exact B1554115
  · exact B1554119
  · exact B1554123
  · exact B1554127
  · exact B1554131
  · exact B1554135
  · exact B1554139
  · exact B1554143
  · exact B1554147
  · exact B1554151
  · exact B1554155
  · exact B1554159
  · exact B1554163
  · exact B1554167
  · exact B1554171
  · exact B1554175
  · exact B1554179
  · exact B1554183
  · exact B1554187
  · exact B1554191
  · exact B1554195
  · exact B1554199
  · exact B1554203
  · exact B1554207
  · exact B1554211
  · exact B1554215
  · exact B1554219
  · exact B1554223
  · exact B1554227
  · exact B1554231
  · exact B1554235
  · exact B1554239
  · exact B1554243
  · exact B1554247
  · exact B1554251
  · exact B1554255
  · exact B1554259
  · exact B1554263
  · exact B1554267
  · exact B1554271
  · exact B1554275
  · exact B1554279
  · exact B1554283
  · exact B1554287
  · exact B1554291
  · exact B1554295
  · exact B1554299
  · exact B1554303
  · exact B1554307
  · exact B1554311
  · exact B1554315
  · exact B1554319
  · exact B1554323
  · exact B1554327
  · exact B1554331
  · exact B1554335
  · exact B1554339
  · exact B1554343
  · exact B1554347
  · exact B1554351
  · exact B1554355
  · exact B1554359
  · exact B1554363
  · exact B1554367
  · exact B1554371
  · exact B1554375
  · exact B1554379
  · exact B1554383
  · exact B1554387
  · exact B1554391
  · exact B1554395
  · exact B1554399
  · exact B1554403
  · exact B1554407
  · exact B1554411
  · exact B1554415
  · exact B1554419
  · exact B1554423
  · exact B1554427
  · exact B1554431
  · exact B1554435
  · exact B1554439
  · exact B1554443
  · exact B1554447
  · exact B1554451
  · exact B1554455
  · exact B1554459
  · exact B1554463
  · exact B1554467
  · exact B1554471
  · exact B1554475
  · exact B1554479
  · exact B1554483
  · exact B1554487
  · exact B1554491
  · exact B1554495
  · exact B1554499
  · exact B1554503
  · exact B1554507
  · exact B1554511
  · exact B1554515
  · exact B1554519
  · exact B1554523
  · exact B1554527
  · exact B1554531
  · exact B1554535
  · exact B1554539
  · exact B1554543
  · exact B1554547
  · exact B1554551
  · exact B1554555
  · exact B1554559
  · exact B1554563
  · exact B1554567
  · exact B1554571
  · exact B1554575
  · exact B1554579
  · exact B1554583
  · exact B1554587
  · exact B1554591
  · exact B1554595
  · exact B1554599
  · exact B1554603
  · exact B1554607
  · exact B1554611
  · exact B1554615
  · exact B1554619
  · exact B1554623
  · exact B1554627
  · exact B1554631
  · exact B1554635
  · exact B1554639
  · exact B1554643
  · exact B1554647
  · exact B1554651
  · exact B1554655
  · exact B1554659
  · exact B1554663
  · exact B1554667
  · exact B1554671
  · exact B1554675
  · exact B1554679
  · exact B1554683
  · exact B1554687
  · exact B1554691
  · exact B1554695
  · exact B1554699
  · exact B1554703
  · exact B1554707
  · exact B1554711
  · exact B1554715
  · exact B1554719
  · exact B1554723
  · exact B1554727
  · exact B1554731
  · exact B1554735
  · exact B1554739
  · exact B1554743
  · exact B1554747
  · exact B1554751
  · exact B1554755
  · exact B1554759
  · exact B1554763
  · exact B1554767
  · exact B1554771
  · exact B1554775
  · exact B1554779
  · exact B1554783
  · exact B1554787
  · exact B1554791
  · exact B1554795
  · exact B1554799
  · exact B1554803
  · exact B1554807
  · exact B1554811
  · exact B1554815
  · exact B1554819
  · exact B1554823
  · exact B1554827
  · exact B1554831
  · exact B1554835
  · exact B1554839
  · exact B1554843
  · exact B1554847
  · exact B1554851
  · exact B1554855
  · exact B1554859
  · exact B1554863
  · exact B1554867
  · exact B1554871
  · exact B1554875
  · exact B1554879
  · exact B1554883
  · exact B1554887
  · exact B1554891
  · exact B1554895
  · exact B1554899
  · exact B1554903
  · exact B1554907
  · exact B1554911
  · exact B1554915
  · exact B1554919
  · exact B1554923
  · exact B1554927
  · exact B1554931
  · exact B1554935
  · exact B1554939
  · exact B1554943
  · exact B1554947
  · exact B1554951
  · exact B1554955
  · exact B1554959
  · exact B1554963
  · exact B1554967
  · exact B1554971
  · exact B1554975
  · exact B1554979
  · exact B1554983
  · exact B1554987
  · exact B1554991
  · exact B1554995
  · exact B1554999
  · exact B1555003
  · exact B1555007
  · exact B1555011
  · exact B1555015
  · exact B1555019
  · exact B1555023
  · exact B1555027
  · exact B1555031
  · exact B1555035
  · exact B1555039
  · exact B1555043
  · exact B1555047
  · exact B1555051
  · exact B1555055
  · exact B1555059
  · exact B1555063
  · exact B1555067
  · exact B1555071
  · exact B1555075
  · exact B1555079
  · exact B1555083
  · exact B1555087
  · exact B1555091
  · exact B1555095
  · exact B1555099
  · exact B1555103
  · exact B1555107
  · exact B1555111
  · exact B1555115
  · exact B1555119
  · exact B1555123
  · exact B1555127
  · exact B1555131
  · exact B1555135
  · exact B1555139
  · exact B1555143
  · exact B1555147
  · exact B1555151
  · exact B1555155
  · exact B1555159
  · exact B1555163
  · exact B1555167
  · exact B1555171
  · exact B1555175
  · exact B1555179
  · exact B1555183
  · exact B1555187
  · exact B1555191
  · exact B1555195
  · exact B1555199
  · exact B1555203
  · exact B1555207
  · exact B1555211
  · exact B1555215
  · exact B1555219
  · exact B1555223
  · exact B1555227
  · exact B1555231
  · exact B1555235
  · exact B1555239
  · exact B1555243
  · exact B1555247
  · exact B1555251
  · exact B1555255
  · exact B1555259
  · exact B1555263
  · exact B1555267
  · exact B1555271
  · exact B1555275
  · exact B1555279
  · exact B1555283
  · exact B1555287
  · exact B1555291
  · exact B1555295
  · exact B1555299
  · exact B1555303
  · exact B1555307
  · exact B1555311
  · exact B1555315
  · exact B1555319
  · exact B1555323
  · exact B1555327
  · exact B1555331
  · exact B1555335
  · exact B1555339
  · exact B1555343
  · exact B1555347
  · exact B1555351
  · exact B1555355
  · exact B1555359
  · exact B1555363
  · exact B1555367
  · exact B1555371
  · exact B1555375
  · exact B1555379
  · exact B1555383
  · exact B1555387
  · exact B1555391
  · exact B1555395
  · exact B1555399
  · exact B1555403
  · exact B1555407
  · exact B1555411
  · exact B1555415
  · exact B1555419
  · exact B1555423
  · exact B1555427
  · exact B1555431
  · exact B1555435
  · exact B1555439
  · exact B1555443
  · exact B1555447
  · exact B1555451
  · exact B1555455
  · exact B1555459
  · exact B1555463
  · exact B1555467
  · exact B1555471

theorem solution (m : ℕ) (hlo : 1553474 ≤ m) (hhi : m ≤ 1555474) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 388368 ≤ j := by omega
    have hj2 : j ≤ 388867 := by omega
    have hb : Blo 1553474 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
