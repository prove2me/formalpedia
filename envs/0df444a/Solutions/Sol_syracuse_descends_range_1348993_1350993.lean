-- Prove2me | solution 1 for syracuse_descends_range_1348993_1350993
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:49.240148+00:00
-- url     : https://prove2.me/submissions/354c7c08-30a0-4cf3-a1c0-1f44307c4d06

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


theorem B2277389 : Blo 1348993 2277389 := bbase (se 3 (by rfl) ⟨427010, by rfl⟩ : syracuseStep 2277389 = 854021) (by norm_num)
theorem B3039245 : Blo 1348993 3039245 := bbase (se 3 (by rfl) ⟨569858, by rfl⟩ : syracuseStep 3039245 = 1139717) (by norm_num)
theorem B2023493 : Blo 1348993 2023493 := bbase (se 4 (by rfl) ⟨189702, by rfl⟩ : syracuseStep 2023493 = 379405) (by norm_num)
theorem B2310221 : Blo 1348993 2310221 := bbase (se 3 (by rfl) ⟨433166, by rfl⟩ : syracuseStep 2310221 = 866333) (by norm_num)
theorem B23371861 : Blo 1348993 23371861 := bbase (se 8 (by rfl) ⟨136944, by rfl⟩ : syracuseStep 23371861 = 273889) (by norm_num)
theorem B3039317 : Blo 1348993 3039317 := bbase (se 8 (by rfl) ⟨17808, by rfl⟩ : syracuseStep 3039317 = 35617) (by norm_num)
theorem B2023517 : Blo 1348993 2023517 := bbase (se 3 (by rfl) ⟨379409, by rfl⟩ : syracuseStep 2023517 = 758819) (by norm_num)
theorem B3842149 : Blo 1348993 3842149 := bbase (se 4 (by rfl) ⟨360201, by rfl⟩ : syracuseStep 3842149 = 720403) (by norm_num)
theorem B3416165 : Blo 1348993 3416165 := bbase (se 4 (by rfl) ⟨320265, by rfl⟩ : syracuseStep 3416165 = 640531) (by norm_num)
theorem B2023541 : Blo 1348993 2023541 := bbase (se 5 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 2023541 = 189707) (by norm_num)
theorem B2023565 : Blo 1348993 2023565 := bbase (se 3 (by rfl) ⟨379418, by rfl⟩ : syracuseStep 2023565 = 758837) (by norm_num)
theorem B2277517 : Blo 1348993 2277517 := bbase (se 3 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 2277517 = 854069) (by norm_num)
theorem B2162837 : Blo 1348993 2162837 := bbase (se 6 (by rfl) ⟨50691, by rfl⟩ : syracuseStep 2162837 = 101383) (by norm_num)
theorem B3039389 : Blo 1348993 3039389 := bbase (se 3 (by rfl) ⟨569885, by rfl⟩ : syracuseStep 3039389 = 1139771) (by norm_num)
theorem B2023589 : Blo 1348993 2023589 := bbase (se 4 (by rfl) ⟨189711, by rfl⟩ : syracuseStep 2023589 = 379423) (by norm_num)
theorem B2883757 : Blo 1348993 2883757 := bbase (se 3 (by rfl) ⟨540704, by rfl⟩ : syracuseStep 2883757 = 1081409) (by norm_num)
theorem B2023613 : Blo 1348993 2023613 := bbase (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) (by norm_num)
theorem B1368257 : Blo 1348993 1368257 := bbase (se 2 (by rfl) ⟨513096, by rfl⟩ : syracuseStep 1368257 = 1026193) (by norm_num)
theorem B2023637 : Blo 1348993 2023637 := bbase (se 7 (by rfl) ⟨23714, by rfl⟩ : syracuseStep 2023637 = 47429) (by norm_num)
theorem B1622233 : Blo 1348993 1622233 := bbase (se 2 (by rfl) ⟨608337, by rfl⟩ : syracuseStep 1622233 = 1216675) (by norm_num)
theorem B1368289 : Blo 1348993 1368289 := bbase (se 2 (by rfl) ⟨513108, by rfl⟩ : syracuseStep 1368289 = 1026217) (by norm_num)
theorem B2277605 : Blo 1348993 2277605 := bbase (se 4 (by rfl) ⟨213525, by rfl⟩ : syracuseStep 2277605 = 427051) (by norm_num)
theorem B3039461 : Blo 1348993 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B2023661 : Blo 1348993 2023661 := bbase (se 3 (by rfl) ⟨379436, by rfl⟩ : syracuseStep 2023661 = 758873) (by norm_num)
theorem B2023685 : Blo 1348993 2023685 := bbase (se 4 (by rfl) ⟨189720, by rfl⟩ : syracuseStep 2023685 = 379441) (by norm_num)
theorem B3842309 : Blo 1348993 3842309 := bbase (se 4 (by rfl) ⟨360216, by rfl⟩ : syracuseStep 3842309 = 720433) (by norm_num)
theorem B2023709 : Blo 1348993 2023709 := bbase (se 3 (by rfl) ⟨379445, by rfl⟩ : syracuseStep 2023709 = 758891) (by norm_num)
theorem B3416357 : Blo 1348993 3416357 := bbase (se 4 (by rfl) ⟨320283, by rfl⟩ : syracuseStep 3416357 = 640567) (by norm_num)
theorem B3039533 : Blo 1348993 3039533 := bbase (se 3 (by rfl) ⟨569912, by rfl⟩ : syracuseStep 3039533 = 1139825) (by norm_num)
theorem B2023733 : Blo 1348993 2023733 := bbase (se 5 (by rfl) ⟨94862, by rfl⟩ : syracuseStep 2023733 = 189725) (by norm_num)
theorem B4555061 : Blo 1348993 4555061 := bbase (se 5 (by rfl) ⟨213518, by rfl⟩ : syracuseStep 4555061 = 427037) (by norm_num)
theorem B2023757 : Blo 1348993 2023757 := bbase (se 3 (by rfl) ⟨379454, by rfl⟩ : syracuseStep 2023757 = 758909) (by norm_num)
theorem B2023781 : Blo 1348993 2023781 := bbase (se 4 (by rfl) ⟨189729, by rfl⟩ : syracuseStep 2023781 = 379459) (by norm_num)
theorem B2277733 : Blo 1348993 2277733 := bbase (se 4 (by rfl) ⟨213537, by rfl⟩ : syracuseStep 2277733 = 427075) (by norm_num)
theorem B3039605 : Blo 1348993 3039605 := bbase (se 5 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 3039605 = 284963) (by norm_num)
theorem B2023805 : Blo 1348993 2023805 := bbase (se 3 (by rfl) ⟨379463, by rfl⟩ : syracuseStep 2023805 = 758927) (by norm_num)
theorem B1442173 : Blo 1348993 1442173 := bbase (se 3 (by rfl) ⟨270407, by rfl⟩ : syracuseStep 1442173 = 540815) (by norm_num)
theorem B2023829 : Blo 1348993 2023829 := bbase (se 6 (by rfl) ⟨47433, by rfl⟩ : syracuseStep 2023829 = 94867) (by norm_num)
theorem B2023853 : Blo 1348993 2023853 := bbase (se 3 (by rfl) ⟨379472, by rfl⟩ : syracuseStep 2023853 = 758945) (by norm_num)
theorem B1442233 : Blo 1348993 1442233 := bbase (se 2 (by rfl) ⟨540837, by rfl⟩ : syracuseStep 1442233 = 1081675) (by norm_num)
theorem B2277821 : Blo 1348993 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B3465661 : Blo 1348993 3465661 := bbase (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) (by norm_num)
theorem B3039677 : Blo 1348993 3039677 := bbase (se 3 (by rfl) ⟨569939, by rfl⟩ : syracuseStep 3039677 = 1139879) (by norm_num)
theorem B2023877 : Blo 1348993 2023877 := bbase (se 4 (by rfl) ⟨189738, by rfl⟩ : syracuseStep 2023877 = 379477) (by norm_num)
theorem B2023901 : Blo 1348993 2023901 := bbase (se 3 (by rfl) ⟨379481, by rfl⟩ : syracuseStep 2023901 = 758963) (by norm_num)
theorem B6488549 : Blo 1348993 6488549 := bbase (se 4 (by rfl) ⟨608301, by rfl⟩ : syracuseStep 6488549 = 1216603) (by norm_num)
theorem B2023925 : Blo 1348993 2023925 := bbase (se 5 (by rfl) ⟨94871, by rfl⟩ : syracuseStep 2023925 = 189743) (by norm_num)
theorem B3842549 : Blo 1348993 3842549 := bbase (se 5 (by rfl) ⟨180119, by rfl⟩ : syracuseStep 3842549 = 360239) (by norm_num)
theorem B2023949 : Blo 1348993 2023949 := bbase (se 3 (by rfl) ⟨379490, by rfl⟩ : syracuseStep 2023949 = 758981) (by norm_num)
theorem B2023973 : Blo 1348993 2023973 := bbase (se 4 (by rfl) ⟨189747, by rfl⟩ : syracuseStep 2023973 = 379495) (by norm_num)
theorem B2433581 : Blo 1348993 2433581 := bbase (se 3 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 2433581 = 912593) (by norm_num)
theorem B2023997 : Blo 1348993 2023997 := bbase (se 3 (by rfl) ⟨379499, by rfl⟩ : syracuseStep 2023997 = 758999) (by norm_num)
theorem B2277949 : Blo 1348993 2277949 := bbase (se 3 (by rfl) ⟨427115, by rfl⟩ : syracuseStep 2277949 = 854231) (by norm_num)
theorem B2024021 : Blo 1348993 2024021 := bbase (se 8 (by rfl) ⟨11859, by rfl⟩ : syracuseStep 2024021 = 23719) (by norm_num)
theorem B2024045 : Blo 1348993 2024045 := bbase (se 3 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 2024045 = 759017) (by norm_num)
theorem B2433653 : Blo 1348993 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B3416701 : Blo 1348993 3416701 := bbase (se 3 (by rfl) ⟨640631, by rfl⟩ : syracuseStep 3416701 = 1281263) (by norm_num)
theorem B2024069 : Blo 1348993 2024069 := bbase (se 4 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 2024069 = 379513) (by norm_num)
theorem B2278037 : Blo 1348993 2278037 := bbase (se 6 (by rfl) ⟨53391, by rfl⟩ : syracuseStep 2278037 = 106783) (by norm_num)
theorem B2024093 : Blo 1348993 2024093 := bbase (se 3 (by rfl) ⟨379517, by rfl⟩ : syracuseStep 2024093 = 759035) (by norm_num)
theorem B2884261 : Blo 1348993 2884261 := bbase (se 4 (by rfl) ⟨270399, by rfl⟩ : syracuseStep 2884261 = 540799) (by norm_num)
theorem B2024117 : Blo 1348993 2024117 := bbase (se 5 (by rfl) ⟨94880, by rfl⟩ : syracuseStep 2024117 = 189761) (by norm_num)
theorem B3842741 : Blo 1348993 3842741 := bbase (se 5 (by rfl) ⟨180128, by rfl⟩ : syracuseStep 3842741 = 360257) (by norm_num)
theorem B2024141 : Blo 1348993 2024141 := bbase (se 3 (by rfl) ⟨379526, by rfl⟩ : syracuseStep 2024141 = 759053) (by norm_num)
theorem B2024165 : Blo 1348993 2024165 := bbase (se 4 (by rfl) ⟨189765, by rfl⟩ : syracuseStep 2024165 = 379531) (by norm_num)
theorem B4555493 : Blo 1348993 4555493 := bbase (se 4 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 4555493 = 854155) (by norm_num)
theorem B3416813 : Blo 1348993 3416813 := bbase (se 3 (by rfl) ⟨640652, by rfl⟩ : syracuseStep 3416813 = 1281305) (by norm_num)
theorem B1442549 : Blo 1348993 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B2024189 : Blo 1348993 2024189 := bbase (se 3 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 2024189 = 759071) (by norm_num)
theorem B4326149 : Blo 1348993 4326149 := bbase (se 4 (by rfl) ⟨405576, by rfl⟩ : syracuseStep 4326149 = 811153) (by norm_num)
theorem B2024213 : Blo 1348993 2024213 := bbase (se 6 (by rfl) ⟨47442, by rfl⟩ : syracuseStep 2024213 = 94885) (by norm_num)
theorem B2278165 : Blo 1348993 2278165 := bbase (se 6 (by rfl) ⟨53394, by rfl⟩ : syracuseStep 2278165 = 106789) (by norm_num)
theorem B1368857 : Blo 1348993 1368857 := bbase (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) (by norm_num)
theorem B2163485 : Blo 1348993 2163485 := bbase (se 3 (by rfl) ⟨405653, by rfl⟩ : syracuseStep 2163485 = 811307) (by norm_num)
theorem B2024237 : Blo 1348993 2024237 := bbase (se 3 (by rfl) ⟨379544, by rfl⟩ : syracuseStep 2024237 = 759089) (by norm_num)
theorem B2024261 : Blo 1348993 2024261 := bbase (se 4 (by rfl) ⟨189774, by rfl⟩ : syracuseStep 2024261 = 379549) (by norm_num)
theorem B2024285 : Blo 1348993 2024285 := bbase (se 3 (by rfl) ⟨379553, by rfl⟩ : syracuseStep 2024285 = 759107) (by norm_num)
theorem B6832997 : Blo 1348993 6832997 := bbase (se 4 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 6832997 = 1281187) (by norm_num)
theorem B2278253 : Blo 1348993 2278253 := bbase (se 3 (by rfl) ⟨427172, by rfl⟩ : syracuseStep 2278253 = 854345) (by norm_num)
theorem B2024309 : Blo 1348993 2024309 := bbase (se 5 (by rfl) ⟨94889, by rfl⟩ : syracuseStep 2024309 = 189779) (by norm_num)
theorem B3466109 : Blo 1348993 3466109 := bbase (se 3 (by rfl) ⟨649895, by rfl⟩ : syracuseStep 3466109 = 1299791) (by norm_num)
theorem B1622921 : Blo 1348993 1622921 := bbase (se 2 (by rfl) ⟨608595, by rfl⟩ : syracuseStep 1622921 = 1217191) (by norm_num)
theorem B2024333 : Blo 1348993 2024333 := bbase (se 3 (by rfl) ⟨379562, by rfl⟩ : syracuseStep 2024333 = 759125) (by norm_num)
theorem B2024357 : Blo 1348993 2024357 := bbase (se 4 (by rfl) ⟨189783, by rfl⟩ : syracuseStep 2024357 = 379567) (by norm_num)
theorem B3417005 : Blo 1348993 3417005 := bbase (se 3 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 3417005 = 1281377) (by norm_num)
theorem B2024381 : Blo 1348993 2024381 := bbase (se 3 (by rfl) ⟨379571, by rfl⟩ : syracuseStep 2024381 = 759143) (by norm_num)
theorem B2024405 : Blo 1348993 2024405 := bbase (se 7 (by rfl) ⟨23723, by rfl⟩ : syracuseStep 2024405 = 47447) (by norm_num)
theorem B2024429 : Blo 1348993 2024429 := bbase (se 3 (by rfl) ⟨379580, by rfl⟩ : syracuseStep 2024429 = 759161) (by norm_num)
theorem B2278381 : Blo 1348993 2278381 := bbase (se 3 (by rfl) ⟨427196, by rfl⟩ : syracuseStep 2278381 = 854393) (by norm_num)
theorem B1713145 : Blo 1348993 1713145 := bbase (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) (by norm_num)
theorem B2024453 : Blo 1348993 2024453 := bbase (se 4 (by rfl) ⟨189792, by rfl⟩ : syracuseStep 2024453 = 379585) (by norm_num)
theorem B2024477 : Blo 1348993 2024477 := bbase (se 3 (by rfl) ⟨379589, by rfl⟩ : syracuseStep 2024477 = 759179) (by norm_num)
theorem B3466277 : Blo 1348993 3466277 := bbase (se 4 (by rfl) ⟨324963, by rfl⟩ : syracuseStep 3466277 = 649927) (by norm_num)
theorem B9724981 : Blo 1348993 9724981 := bbase (se 5 (by rfl) ⟨455858, by rfl⟩ : syracuseStep 9724981 = 911717) (by norm_num)
theorem B2024501 : Blo 1348993 2024501 := bbase (se 5 (by rfl) ⟨94898, by rfl⟩ : syracuseStep 2024501 = 189797) (by norm_num)
theorem B2278469 : Blo 1348993 2278469 := bbase (se 4 (by rfl) ⟨213606, by rfl⟩ : syracuseStep 2278469 = 427213) (by norm_num)
theorem B2024525 : Blo 1348993 2024525 := bbase (se 3 (by rfl) ⟨379598, by rfl⟩ : syracuseStep 2024525 = 759197) (by norm_num)
theorem B2024549 : Blo 1348993 2024549 := bbase (se 4 (by rfl) ⟨189801, by rfl⟩ : syracuseStep 2024549 = 379603) (by norm_num)
theorem B2024573 : Blo 1348993 2024573 := bbase (se 3 (by rfl) ⟨379607, by rfl⟩ : syracuseStep 2024573 = 759215) (by norm_num)
theorem B3245197 : Blo 1348993 3245197 := bbase (se 3 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 3245197 = 1216949) (by norm_num)
theorem B2024597 : Blo 1348993 2024597 := bbase (se 6 (by rfl) ⟨47451, by rfl⟩ : syracuseStep 2024597 = 94903) (by norm_num)
theorem B4555925 : Blo 1348993 4555925 := bbase (se 6 (by rfl) ⟨106779, by rfl⟩ : syracuseStep 4555925 = 213559) (by norm_num)
theorem B5129365 : Blo 1348993 5129365 := bbase (se 6 (by rfl) ⟨120219, by rfl⟩ : syracuseStep 5129365 = 240439) (by norm_num)
theorem B2024621 : Blo 1348993 2024621 := bbase (se 3 (by rfl) ⟨379616, by rfl⟩ : syracuseStep 2024621 = 759233) (by norm_num)
theorem B2024645 : Blo 1348993 2024645 := bbase (se 4 (by rfl) ⟨189810, by rfl⟩ : syracuseStep 2024645 = 379621) (by norm_num)
theorem B2278597 : Blo 1348993 2278597 := bbase (se 4 (by rfl) ⟨213618, by rfl⟩ : syracuseStep 2278597 = 427237) (by norm_num)
theorem B7300309 : Blo 1348993 7300309 := bbase (se 7 (by rfl) ⟨85550, by rfl⟩ : syracuseStep 7300309 = 171101) (by norm_num)
theorem B2024669 : Blo 1348993 2024669 := bbase (se 3 (by rfl) ⟨379625, by rfl⟩ : syracuseStep 2024669 = 759251) (by norm_num)
theorem B2024693 : Blo 1348993 2024693 := bbase (se 5 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 2024693 = 189815) (by norm_num)
theorem B11535605 : Blo 1348993 11535605 := bbase (se 5 (by rfl) ⟨540731, by rfl⟩ : syracuseStep 11535605 = 1081463) (by norm_num)
theorem B3417349 : Blo 1348993 3417349 := bbase (se 4 (by rfl) ⟨320376, by rfl⟩ : syracuseStep 3417349 = 640753) (by norm_num)
theorem B2024717 : Blo 1348993 2024717 := bbase (se 3 (by rfl) ⟨379634, by rfl⟩ : syracuseStep 2024717 = 759269) (by norm_num)
theorem B2278685 : Blo 1348993 2278685 := bbase (se 3 (by rfl) ⟨427253, by rfl⟩ : syracuseStep 2278685 = 854507) (by norm_num)
theorem B2024741 : Blo 1348993 2024741 := bbase (se 4 (by rfl) ⟨189819, by rfl⟩ : syracuseStep 2024741 = 379639) (by norm_num)
theorem B2024765 : Blo 1348993 2024765 := bbase (se 3 (by rfl) ⟨379643, by rfl⟩ : syracuseStep 2024765 = 759287) (by norm_num)
theorem B2024789 : Blo 1348993 2024789 := bbase (se 12 (by rfl) ⟨741, by rfl⟩ : syracuseStep 2024789 = 1483) (by norm_num)
theorem B2024813 : Blo 1348993 2024813 := bbase (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) (by norm_num)
theorem B11527541 : Blo 1348993 11527541 := bbase (se 5 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 11527541 = 1080707) (by norm_num)
theorem B3417461 : Blo 1348993 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B2024837 : Blo 1348993 2024837 := bbase (se 4 (by rfl) ⟨189828, by rfl⟩ : syracuseStep 2024837 = 379657) (by norm_num)
theorem B2024861 : Blo 1348993 2024861 := bbase (se 3 (by rfl) ⟨379661, by rfl⟩ : syracuseStep 2024861 = 759323) (by norm_num)
theorem B2278813 : Blo 1348993 2278813 := bbase (se 3 (by rfl) ⟨427277, by rfl⟩ : syracuseStep 2278813 = 854555) (by norm_num)
theorem B2024885 : Blo 1348993 2024885 := bbase (se 5 (by rfl) ⟨94916, by rfl⟩ : syracuseStep 2024885 = 189833) (by norm_num)
theorem B2024909 : Blo 1348993 2024909 := bbase (se 3 (by rfl) ⟨379670, by rfl⟩ : syracuseStep 2024909 = 759341) (by norm_num)
theorem B17302997 : Blo 1348993 17302997 := bbase (se 7 (by rfl) ⟨202769, by rfl⟩ : syracuseStep 17302997 = 405539) (by norm_num)
theorem B2024933 : Blo 1348993 2024933 := bbase (se 4 (by rfl) ⟨189837, by rfl⟩ : syracuseStep 2024933 = 379675) (by norm_num)
theorem B2278901 : Blo 1348993 2278901 := bbase (se 5 (by rfl) ⟨106823, by rfl⟩ : syracuseStep 2278901 = 213647) (by norm_num)
theorem B2024957 : Blo 1348993 2024957 := bbase (se 3 (by rfl) ⟨379679, by rfl⟩ : syracuseStep 2024957 = 759359) (by norm_num)
theorem B2024981 : Blo 1348993 2024981 := bbase (se 6 (by rfl) ⟨47460, by rfl⟩ : syracuseStep 2024981 = 94921) (by norm_num)
theorem B2885149 : Blo 1348993 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B2025005 : Blo 1348993 2025005 := bbase (se 3 (by rfl) ⟨379688, by rfl⟩ : syracuseStep 2025005 = 759377) (by norm_num)
theorem B3417653 : Blo 1348993 3417653 := bbase (se 5 (by rfl) ⟨160202, by rfl⟩ : syracuseStep 3417653 = 320405) (by norm_num)
theorem B2025029 : Blo 1348993 2025029 := bbase (se 4 (by rfl) ⟨189846, by rfl⟩ : syracuseStep 2025029 = 379693) (by norm_num)
theorem B4556357 : Blo 1348993 4556357 := bbase (se 4 (by rfl) ⟨427158, by rfl⟩ : syracuseStep 4556357 = 854317) (by norm_num)
theorem B26297941 : Blo 1348993 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B2025053 : Blo 1348993 2025053 := bbase (se 3 (by rfl) ⟨379697, by rfl⟩ : syracuseStep 2025053 = 759395) (by norm_num)
theorem B2025077 : Blo 1348993 2025077 := bbase (se 5 (by rfl) ⟨94925, by rfl⟩ : syracuseStep 2025077 = 189851) (by norm_num)
theorem B2279029 : Blo 1348993 2279029 := bbase (se 5 (by rfl) ⟨106829, by rfl⟩ : syracuseStep 2279029 = 213659) (by norm_num)
theorem B2025101 : Blo 1348993 2025101 := bbase (se 3 (by rfl) ⟨379706, by rfl⟩ : syracuseStep 2025101 = 759413) (by norm_num)
theorem B3843733 : Blo 1348993 3843733 := bbase (se 6 (by rfl) ⟨90087, by rfl⟩ : syracuseStep 3843733 = 180175) (by norm_num)
theorem B2025125 : Blo 1348993 2025125 := bbase (se 4 (by rfl) ⟨189855, by rfl⟩ : syracuseStep 2025125 = 379711) (by norm_num)
theorem B2025149 : Blo 1348993 2025149 := bbase (se 3 (by rfl) ⟨379715, by rfl⟩ : syracuseStep 2025149 = 759431) (by norm_num)
theorem B2279117 : Blo 1348993 2279117 := bbase (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) (by norm_num)
theorem B2025173 : Blo 1348993 2025173 := bbase (se 7 (by rfl) ⟨23732, by rfl⟩ : syracuseStep 2025173 = 47465) (by norm_num)
theorem B2025197 : Blo 1348993 2025197 := bbase (se 3 (by rfl) ⟨379724, by rfl⟩ : syracuseStep 2025197 = 759449) (by norm_num)
theorem B2025221 : Blo 1348993 2025221 := bbase (se 4 (by rfl) ⟨189864, by rfl⟩ : syracuseStep 2025221 = 379729) (by norm_num)
theorem B2025245 : Blo 1348993 2025245 := bbase (se 3 (by rfl) ⟨379733, by rfl⟩ : syracuseStep 2025245 = 759467) (by norm_num)
theorem B2025269 : Blo 1348993 2025269 := bbase (se 5 (by rfl) ⟨94934, by rfl⟩ : syracuseStep 2025269 = 189869) (by norm_num)
theorem B2025293 : Blo 1348993 2025293 := bbase (se 3 (by rfl) ⟨379742, by rfl⟩ : syracuseStep 2025293 = 759485) (by norm_num)
theorem B2279245 : Blo 1348993 2279245 := bbase (se 3 (by rfl) ⟨427358, by rfl⟩ : syracuseStep 2279245 = 854717) (by norm_num)
theorem B2025317 : Blo 1348993 2025317 := bbase (se 4 (by rfl) ⟨189873, by rfl⟩ : syracuseStep 2025317 = 379747) (by norm_num)
theorem B2025341 : Blo 1348993 2025341 := bbase (se 3 (by rfl) ⟨379751, by rfl⟩ : syracuseStep 2025341 = 759503) (by norm_num)
theorem B3417997 : Blo 1348993 3417997 := bbase (se 3 (by rfl) ⟨640874, by rfl⟩ : syracuseStep 3417997 = 1281749) (by norm_num)
theorem B2025365 : Blo 1348993 2025365 := bbase (se 6 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 2025365 = 94939) (by norm_num)
theorem B2279333 : Blo 1348993 2279333 := bbase (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) (by norm_num)
theorem B2025389 : Blo 1348993 2025389 := bbase (se 3 (by rfl) ⟨379760, by rfl⟩ : syracuseStep 2025389 = 759521) (by norm_num)
theorem B2025413 : Blo 1348993 2025413 := bbase (se 4 (by rfl) ⟨189882, by rfl⟩ : syracuseStep 2025413 = 379765) (by norm_num)
theorem B2025437 : Blo 1348993 2025437 := bbase (se 3 (by rfl) ⟨379769, by rfl⟩ : syracuseStep 2025437 = 759539) (by norm_num)
theorem B4556789 : Blo 1348993 4556789 := bbase (se 5 (by rfl) ⟨213599, by rfl⟩ : syracuseStep 4556789 = 427199) (by norm_num)
theorem B2025461 : Blo 1348993 2025461 := bbase (se 5 (by rfl) ⟨94943, by rfl⟩ : syracuseStep 2025461 = 189887) (by norm_num)
theorem B3418109 : Blo 1348993 3418109 := bbase (se 3 (by rfl) ⟨640895, by rfl⟩ : syracuseStep 3418109 = 1281791) (by norm_num)
theorem B2025485 : Blo 1348993 2025485 := bbase (se 3 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 2025485 = 759557) (by norm_num)
theorem B2025509 : Blo 1348993 2025509 := bbase (se 4 (by rfl) ⟨189891, by rfl⟩ : syracuseStep 2025509 = 379783) (by norm_num)
theorem B2279461 : Blo 1348993 2279461 := bbase (se 4 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 2279461 = 427399) (by norm_num)
theorem B1517629 : Blo 1348993 1517629 := bbase (se 3 (by rfl) ⟨284555, by rfl⟩ : syracuseStep 1517629 = 569111) (by norm_num)
theorem B2025533 : Blo 1348993 2025533 := bbase (se 3 (by rfl) ⟨379787, by rfl⟩ : syracuseStep 2025533 = 759575) (by norm_num)
theorem B2025557 : Blo 1348993 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B1517665 : Blo 1348993 1517665 := bbase (se 2 (by rfl) ⟨569124, by rfl⟩ : syracuseStep 1517665 = 1138249) (by norm_num)
theorem B2025581 : Blo 1348993 2025581 := bbase (se 3 (by rfl) ⟨379796, by rfl⟩ : syracuseStep 2025581 = 759593) (by norm_num)
theorem B6834293 : Blo 1348993 6834293 := bbase (se 5 (by rfl) ⟨320357, by rfl⟩ : syracuseStep 6834293 = 640715) (by norm_num)
theorem B2279549 : Blo 1348993 2279549 := bbase (se 3 (by rfl) ⟨427415, by rfl⟩ : syracuseStep 2279549 = 854831) (by norm_num)
theorem B1755265 : Blo 1348993 1755265 := bbase (se 2 (by rfl) ⟨658224, by rfl⟩ : syracuseStep 1755265 = 1316449) (by norm_num)
theorem B1517701 : Blo 1348993 1517701 := bbase (se 4 (by rfl) ⟨142284, by rfl⟩ : syracuseStep 1517701 = 284569) (by norm_num)
theorem B4384901 : Blo 1348993 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B2025605 : Blo 1348993 2025605 := bbase (se 4 (by rfl) ⟨189900, by rfl⟩ : syracuseStep 2025605 = 379801) (by norm_num)
theorem B2025629 : Blo 1348993 2025629 := bbase (se 3 (by rfl) ⟨379805, by rfl⟩ : syracuseStep 2025629 = 759611) (by norm_num)
theorem B1517737 : Blo 1348993 1517737 := bbase (se 2 (by rfl) ⟨569151, by rfl⟩ : syracuseStep 1517737 = 1138303) (by norm_num)
theorem B2025653 : Blo 1348993 2025653 := bbase (se 5 (by rfl) ⟨94952, by rfl⟩ : syracuseStep 2025653 = 189905) (by norm_num)
theorem B3418301 : Blo 1348993 3418301 := bbase (se 3 (by rfl) ⟨640931, by rfl⟩ : syracuseStep 3418301 = 1281863) (by norm_num)
theorem B1517773 : Blo 1348993 1517773 := bbase (se 3 (by rfl) ⟨284582, by rfl⟩ : syracuseStep 1517773 = 569165) (by norm_num)
theorem B2025677 : Blo 1348993 2025677 := bbase (se 3 (by rfl) ⟨379814, by rfl⟩ : syracuseStep 2025677 = 759629) (by norm_num)
theorem B2025701 : Blo 1348993 2025701 := bbase (se 4 (by rfl) ⟨189909, by rfl⟩ : syracuseStep 2025701 = 379819) (by norm_num)
theorem B1517809 : Blo 1348993 1517809 := bbase (se 2 (by rfl) ⟨569178, by rfl⟩ : syracuseStep 1517809 = 1138357) (by norm_num)
theorem B2025725 : Blo 1348993 2025725 := bbase (se 3 (by rfl) ⟨379823, by rfl⟩ : syracuseStep 2025725 = 759647) (by norm_num)
theorem B2279677 : Blo 1348993 2279677 := bbase (se 3 (by rfl) ⟨427439, by rfl⟩ : syracuseStep 2279677 = 854879) (by norm_num)
theorem B1517845 : Blo 1348993 1517845 := bbase (se 6 (by rfl) ⟨35574, by rfl⟩ : syracuseStep 1517845 = 71149) (by norm_num)
theorem B2025749 : Blo 1348993 2025749 := bbase (se 6 (by rfl) ⟨47478, by rfl⟩ : syracuseStep 2025749 = 94957) (by norm_num)
theorem B2025773 : Blo 1348993 2025773 := bbase (se 3 (by rfl) ⟨379832, by rfl⟩ : syracuseStep 2025773 = 759665) (by norm_num)
theorem B2738485 : Blo 1348993 2738485 := bbase (se 5 (by rfl) ⟨128366, by rfl⟩ : syracuseStep 2738485 = 256733) (by norm_num)
theorem B1517881 : Blo 1348993 1517881 := bbase (se 2 (by rfl) ⟨569205, by rfl⟩ : syracuseStep 1517881 = 1138411) (by norm_num)
theorem B2025797 : Blo 1348993 2025797 := bbase (se 4 (by rfl) ⟨189918, by rfl⟩ : syracuseStep 2025797 = 379837) (by norm_num)
theorem B7686485 : Blo 1348993 7686485 := bbase (se 10 (by rfl) ⟨11259, by rfl⟩ : syracuseStep 7686485 = 22519) (by norm_num)
theorem B14600533 : Blo 1348993 14600533 := bbase (se 10 (by rfl) ⟨21387, by rfl⟩ : syracuseStep 14600533 = 42775) (by norm_num)
theorem B2279765 : Blo 1348993 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B1517917 : Blo 1348993 1517917 := bbase (se 3 (by rfl) ⟨284609, by rfl⟩ : syracuseStep 1517917 = 569219) (by norm_num)
theorem B2025821 : Blo 1348993 2025821 := bbase (se 3 (by rfl) ⟨379841, by rfl⟩ : syracuseStep 2025821 = 759683) (by norm_num)
theorem B5196149 : Blo 1348993 5196149 := bbase (se 5 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 5196149 = 487139) (by norm_num)
theorem B2025845 : Blo 1348993 2025845 := bbase (se 5 (by rfl) ⟨94961, by rfl⟩ : syracuseStep 2025845 = 189923) (by norm_num)
theorem B2738557 : Blo 1348993 2738557 := bbase (se 3 (by rfl) ⟨513479, by rfl⟩ : syracuseStep 2738557 = 1026959) (by norm_num)
theorem B1517953 : Blo 1348993 1517953 := bbase (se 2 (by rfl) ⟨569232, by rfl⟩ : syracuseStep 1517953 = 1138465) (by norm_num)
theorem B2025869 : Blo 1348993 2025869 := bbase (se 3 (by rfl) ⟨379850, by rfl⟩ : syracuseStep 2025869 = 759701) (by norm_num)
theorem B1517989 : Blo 1348993 1517989 := bbase (se 4 (by rfl) ⟨142311, by rfl⟩ : syracuseStep 1517989 = 284623) (by norm_num)
theorem B4557221 : Blo 1348993 4557221 := bbase (se 4 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 4557221 = 854479) (by norm_num)
theorem B2025893 : Blo 1348993 2025893 := bbase (se 4 (by rfl) ⟨189927, by rfl⟩ : syracuseStep 2025893 = 379855) (by norm_num)
theorem B6244789 : Blo 1348993 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B2025917 : Blo 1348993 2025917 := bbase (se 3 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 2025917 = 759719) (by norm_num)
theorem B1518025 : Blo 1348993 1518025 := bbase (se 2 (by rfl) ⟨569259, by rfl⟩ : syracuseStep 1518025 = 1138519) (by norm_num)
theorem B2025941 : Blo 1348993 2025941 := bbase (se 7 (by rfl) ⟨23741, by rfl⟩ : syracuseStep 2025941 = 47483) (by norm_num)
theorem B5769701 : Blo 1348993 5769701 := bbase (se 4 (by rfl) ⟨540909, by rfl⟩ : syracuseStep 5769701 = 1081819) (by norm_num)
theorem B1518061 : Blo 1348993 1518061 := bbase (se 3 (by rfl) ⟨284636, by rfl⟩ : syracuseStep 1518061 = 569273) (by norm_num)
theorem B2025965 : Blo 1348993 2025965 := bbase (se 3 (by rfl) ⟨379868, by rfl⟩ : syracuseStep 2025965 = 759737) (by norm_num)
theorem B2025989 : Blo 1348993 2025989 := bbase (se 4 (by rfl) ⟨189936, by rfl⟩ : syracuseStep 2025989 = 379873) (by norm_num)
theorem B1518097 : Blo 1348993 1518097 := bbase (se 2 (by rfl) ⟨569286, by rfl⟩ : syracuseStep 1518097 = 1138573) (by norm_num)
theorem B3418645 : Blo 1348993 3418645 := bbase (se 6 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 3418645 = 160249) (by norm_num)
theorem B2599445 : Blo 1348993 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B2026013 : Blo 1348993 2026013 := bbase (se 3 (by rfl) ⟨379877, by rfl⟩ : syracuseStep 2026013 = 759755) (by norm_num)
theorem B3648037 : Blo 1348993 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B1518133 : Blo 1348993 1518133 := bbase (se 5 (by rfl) ⟨71162, by rfl⟩ : syracuseStep 1518133 = 142325) (by norm_num)
theorem B2026037 : Blo 1348993 2026037 := bbase (se 5 (by rfl) ⟨94970, by rfl⟩ : syracuseStep 2026037 = 189941) (by norm_num)
theorem B6244933 : Blo 1348993 6244933 := bbase (se 4 (by rfl) ⟨585462, by rfl⟩ : syracuseStep 6244933 = 1170925) (by norm_num)
theorem B4328005 : Blo 1348993 4328005 := bbase (se 4 (by rfl) ⟨405750, by rfl⟩ : syracuseStep 4328005 = 811501) (by norm_num)
theorem B2026061 : Blo 1348993 2026061 := bbase (se 3 (by rfl) ⟨379886, by rfl⟩ : syracuseStep 2026061 = 759773) (by norm_num)
theorem B14600789 : Blo 1348993 14600789 := bbase (se 8 (by rfl) ⟨85551, by rfl⟩ : syracuseStep 14600789 = 171103) (by norm_num)
theorem B1518169 : Blo 1348993 1518169 := bbase (se 2 (by rfl) ⟨569313, by rfl⟩ : syracuseStep 1518169 = 1138627) (by norm_num)
theorem B2026085 : Blo 1348993 2026085 := bbase (se 4 (by rfl) ⟨189945, by rfl⟩ : syracuseStep 2026085 = 379891) (by norm_num)
theorem B1518205 : Blo 1348993 1518205 := bbase (se 3 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 1518205 = 569327) (by norm_num)
theorem B2026109 : Blo 1348993 2026109 := bbase (se 3 (by rfl) ⟨379895, by rfl⟩ : syracuseStep 2026109 = 759791) (by norm_num)
theorem B3418757 : Blo 1348993 3418757 := bbase (se 4 (by rfl) ⟨320508, by rfl⟩ : syracuseStep 3418757 = 641017) (by norm_num)
theorem B2026133 : Blo 1348993 2026133 := bbase (se 6 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 2026133 = 94975) (by norm_num)
theorem B1518241 : Blo 1348993 1518241 := bbase (se 2 (by rfl) ⟨569340, by rfl⟩ : syracuseStep 1518241 = 1138681) (by norm_num)
theorem B2026157 : Blo 1348993 2026157 := bbase (se 3 (by rfl) ⟨379904, by rfl⟩ : syracuseStep 2026157 = 759809) (by norm_num)
theorem B1518277 : Blo 1348993 1518277 := bbase (se 4 (by rfl) ⟨142338, by rfl⟩ : syracuseStep 1518277 = 284677) (by norm_num)
theorem B2026181 : Blo 1348993 2026181 := bbase (se 4 (by rfl) ⟨189954, by rfl⟩ : syracuseStep 2026181 = 379909) (by norm_num)
theorem B2026205 : Blo 1348993 2026205 := bbase (se 3 (by rfl) ⟨379913, by rfl⟩ : syracuseStep 2026205 = 759827) (by norm_num)
theorem B3844837 : Blo 1348993 3844837 := bbase (se 4 (by rfl) ⟨360453, by rfl⟩ : syracuseStep 3844837 = 720907) (by norm_num)
theorem B1518313 : Blo 1348993 1518313 := bbase (se 2 (by rfl) ⟨569367, by rfl⟩ : syracuseStep 1518313 = 1138735) (by norm_num)
theorem B2026229 : Blo 1348993 2026229 := bbase (se 5 (by rfl) ⟨94979, by rfl⟩ : syracuseStep 2026229 = 189959) (by norm_num)
theorem B1518349 : Blo 1348993 1518349 := bbase (se 3 (by rfl) ⟨284690, by rfl⟩ : syracuseStep 1518349 = 569381) (by norm_num)
theorem B2026253 : Blo 1348993 2026253 := bbase (se 3 (by rfl) ⟨379922, by rfl⟩ : syracuseStep 2026253 = 759845) (by norm_num)
theorem B2026277 : Blo 1348993 2026277 := bbase (se 4 (by rfl) ⟨189963, by rfl⟩ : syracuseStep 2026277 = 379927) (by norm_num)
theorem B1518385 : Blo 1348993 1518385 := bbase (se 2 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 1518385 = 1138789) (by norm_num)
theorem B2026301 : Blo 1348993 2026301 := bbase (se 3 (by rfl) ⟨379931, by rfl⟩ : syracuseStep 2026301 = 759863) (by norm_num)
theorem B3418949 : Blo 1348993 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B1518421 : Blo 1348993 1518421 := bbase (se 9 (by rfl) ⟨4448, by rfl⟩ : syracuseStep 1518421 = 8897) (by norm_num)
theorem B4557653 : Blo 1348993 4557653 := bbase (se 9 (by rfl) ⟨13352, by rfl⟩ : syracuseStep 4557653 = 26705) (by norm_num)
theorem B2026325 : Blo 1348993 2026325 := bbase (se 9 (by rfl) ⟨5936, by rfl⟩ : syracuseStep 2026325 = 11873) (by norm_num)
theorem B2026349 : Blo 1348993 2026349 := bbase (se 3 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 2026349 = 759881) (by norm_num)
theorem B1518457 : Blo 1348993 1518457 := bbase (se 2 (by rfl) ⟨569421, by rfl⟩ : syracuseStep 1518457 = 1138843) (by norm_num)
theorem B2026373 : Blo 1348993 2026373 := bbase (se 4 (by rfl) ⟨189972, by rfl⟩ : syracuseStep 2026373 = 379945) (by norm_num)
theorem B1518493 : Blo 1348993 1518493 := bbase (se 3 (by rfl) ⟨284717, by rfl⟩ : syracuseStep 1518493 = 569435) (by norm_num)
theorem B2026397 : Blo 1348993 2026397 := bbase (se 3 (by rfl) ⟨379949, by rfl⟩ : syracuseStep 2026397 = 759899) (by norm_num)
theorem B2026421 : Blo 1348993 2026421 := bbase (se 5 (by rfl) ⟨94988, by rfl⟩ : syracuseStep 2026421 = 189977) (by norm_num)
theorem B1518529 : Blo 1348993 1518529 := bbase (se 2 (by rfl) ⟨569448, by rfl⟩ : syracuseStep 1518529 = 1138897) (by norm_num)
theorem B2026445 : Blo 1348993 2026445 := bbase (se 3 (by rfl) ⟨379958, by rfl⟩ : syracuseStep 2026445 = 759917) (by norm_num)
theorem B1518565 : Blo 1348993 1518565 := bbase (se 4 (by rfl) ⟨142365, by rfl⟩ : syracuseStep 1518565 = 284731) (by norm_num)
theorem B2026469 : Blo 1348993 2026469 := bbase (se 4 (by rfl) ⟨189981, by rfl⟩ : syracuseStep 2026469 = 379963) (by norm_num)
theorem B1518601 : Blo 1348993 1518601 := bbase (se 2 (by rfl) ⟨569475, by rfl⟩ : syracuseStep 1518601 = 1138951) (by norm_num)
theorem B1518637 : Blo 1348993 1518637 := bbase (se 3 (by rfl) ⟨284744, by rfl⟩ : syracuseStep 1518637 = 569489) (by norm_num)
theorem B1518673 : Blo 1348993 1518673 := bbase (se 2 (by rfl) ⟨569502, by rfl⟩ : syracuseStep 1518673 = 1139005) (by norm_num)
theorem B1518709 : Blo 1348993 1518709 := bbase (se 5 (by rfl) ⟨71189, by rfl⟩ : syracuseStep 1518709 = 142379) (by norm_num)
theorem B1518745 : Blo 1348993 1518745 := bbase (se 2 (by rfl) ⟨569529, by rfl⟩ : syracuseStep 1518745 = 1139059) (by norm_num)
theorem B3419293 : Blo 1348993 3419293 := bbase (se 3 (by rfl) ⟨641117, by rfl⟩ : syracuseStep 3419293 = 1282235) (by norm_num)
theorem B1518781 : Blo 1348993 1518781 := bbase (se 3 (by rfl) ⟨284771, by rfl⟩ : syracuseStep 1518781 = 569543) (by norm_num)
theorem B1518817 : Blo 1348993 1518817 := bbase (se 2 (by rfl) ⟨569556, by rfl⟩ : syracuseStep 1518817 = 1139113) (by norm_num)
theorem B1518853 : Blo 1348993 1518853 := bbase (se 4 (by rfl) ⟨142392, by rfl⟩ : syracuseStep 1518853 = 284785) (by norm_num)
theorem B4558085 : Blo 1348993 4558085 := bbase (se 4 (by rfl) ⟨427320, by rfl⟩ : syracuseStep 4558085 = 854641) (by norm_num)
theorem B3419405 : Blo 1348993 3419405 := bbase (se 3 (by rfl) ⟨641138, by rfl⟩ : syracuseStep 3419405 = 1282277) (by norm_num)
theorem B1518889 : Blo 1348993 1518889 := bbase (se 2 (by rfl) ⟨569583, by rfl⟩ : syracuseStep 1518889 = 1139167) (by norm_num)
theorem B1518925 : Blo 1348993 1518925 := bbase (se 3 (by rfl) ⟨284798, by rfl⟩ : syracuseStep 1518925 = 569597) (by norm_num)
theorem B8654165 : Blo 1348993 8654165 := bbase (se 11 (by rfl) ⟨6338, by rfl⟩ : syracuseStep 8654165 = 12677) (by norm_num)
theorem B1518961 : Blo 1348993 1518961 := bbase (se 2 (by rfl) ⟨569610, by rfl⟩ : syracuseStep 1518961 = 1139221) (by norm_num)
theorem B6835589 : Blo 1348993 6835589 := bbase (se 4 (by rfl) ⟨640836, by rfl⟩ : syracuseStep 6835589 = 1281673) (by norm_num)
theorem B1707409 : Blo 1348993 1707409 := bbase (se 2 (by rfl) ⟨640278, by rfl⟩ : syracuseStep 1707409 = 1280557) (by norm_num)
theorem B1518997 : Blo 1348993 1518997 := bbase (se 6 (by rfl) ⟨35601, by rfl⟩ : syracuseStep 1518997 = 71203) (by norm_num)
theorem B6925733 : Blo 1348993 6925733 := bbase (se 4 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 6925733 = 1298575) (by norm_num)
theorem B1519033 : Blo 1348993 1519033 := bbase (se 2 (by rfl) ⟨569637, by rfl⟩ : syracuseStep 1519033 = 1139275) (by norm_num)
theorem B3419597 : Blo 1348993 3419597 := bbase (se 3 (by rfl) ⟨641174, by rfl⟩ : syracuseStep 3419597 = 1282349) (by norm_num)
theorem B42118613 : Blo 1348993 42118613 := bbase (se 7 (by rfl) ⟨493577, by rfl⟩ : syracuseStep 42118613 = 987155) (by norm_num)
theorem B5770709 : Blo 1348993 5770709 := bbase (se 7 (by rfl) ⟨67625, by rfl⟩ : syracuseStep 5770709 = 135251) (by norm_num)
theorem B1519069 : Blo 1348993 1519069 := bbase (se 3 (by rfl) ⟨284825, by rfl⟩ : syracuseStep 1519069 = 569651) (by norm_num)
theorem B7687669 : Blo 1348993 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B1519105 : Blo 1348993 1519105 := bbase (se 2 (by rfl) ⟨569664, by rfl⟩ : syracuseStep 1519105 = 1139329) (by norm_num)
theorem B1519141 : Blo 1348993 1519141 := bbase (se 4 (by rfl) ⟨142419, by rfl⟩ : syracuseStep 1519141 = 284839) (by norm_num)
theorem B1707581 : Blo 1348993 1707581 := bbase (se 3 (by rfl) ⟨320171, by rfl⟩ : syracuseStep 1707581 = 640343) (by norm_num)
theorem B1519177 : Blo 1348993 1519177 := bbase (se 2 (by rfl) ⟨569691, by rfl⟩ : syracuseStep 1519177 = 1139383) (by norm_num)
theorem B1519213 : Blo 1348993 1519213 := bbase (se 3 (by rfl) ⟨284852, by rfl⟩ : syracuseStep 1519213 = 569705) (by norm_num)
theorem B5762677 : Blo 1348993 5762677 := bbase (se 5 (by rfl) ⟨270125, by rfl⟩ : syracuseStep 5762677 = 540251) (by norm_num)
theorem B1707637 : Blo 1348993 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1519249 : Blo 1348993 1519249 := bbase (se 2 (by rfl) ⟨569718, by rfl⟩ : syracuseStep 1519249 = 1139437) (by norm_num)
theorem B1519285 : Blo 1348993 1519285 := bbase (se 5 (by rfl) ⟨71216, by rfl⟩ : syracuseStep 1519285 = 142433) (by norm_num)
theorem B4558517 : Blo 1348993 4558517 := bbase (se 5 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 4558517 = 427361) (by norm_num)
theorem B1707733 : Blo 1348993 1707733 := bbase (se 7 (by rfl) ⟨20012, by rfl⟩ : syracuseStep 1707733 = 40025) (by norm_num)
theorem B1519321 : Blo 1348993 1519321 := bbase (se 2 (by rfl) ⟨569745, by rfl⟩ : syracuseStep 1519321 = 1139491) (by norm_num)
theorem B1519357 : Blo 1348993 1519357 := bbase (se 3 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 1519357 = 569759) (by norm_num)
theorem B1920773 : Blo 1348993 1920773 := bbase (se 4 (by rfl) ⟨180072, by rfl⟩ : syracuseStep 1920773 = 360145) (by norm_num)
theorem B1519393 : Blo 1348993 1519393 := bbase (se 2 (by rfl) ⟨569772, by rfl⟩ : syracuseStep 1519393 = 1139545) (by norm_num)
theorem B1519429 : Blo 1348993 1519429 := bbase (se 4 (by rfl) ⟨142446, by rfl⟩ : syracuseStep 1519429 = 284893) (by norm_num)
theorem B4108117 : Blo 1348993 4108117 := bbase (se 9 (by rfl) ⟨12035, by rfl⟩ : syracuseStep 4108117 = 24071) (by norm_num)
theorem B1560421 : Blo 1348993 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B1519465 : Blo 1348993 1519465 := bbase (se 2 (by rfl) ⟨569799, by rfl⟩ : syracuseStep 1519465 = 1139599) (by norm_num)
theorem B1707905 : Blo 1348993 1707905 := bbase (se 2 (by rfl) ⟨640464, by rfl⟩ : syracuseStep 1707905 = 1280929) (by norm_num)
theorem B1519501 : Blo 1348993 1519501 := bbase (se 3 (by rfl) ⟨284906, by rfl⟩ : syracuseStep 1519501 = 569813) (by norm_num)
theorem B5124005 : Blo 1348993 5124005 := bbase (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) (by norm_num)
theorem B3698597 : Blo 1348993 3698597 := bbase (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) (by norm_num)
theorem B1519537 : Blo 1348993 1519537 := bbase (se 2 (by rfl) ⟨569826, by rfl⟩ : syracuseStep 1519537 = 1139653) (by norm_num)
theorem B1707961 : Blo 1348993 1707961 := bbase (se 2 (by rfl) ⟨640485, by rfl⟩ : syracuseStep 1707961 = 1280971) (by norm_num)
theorem B1519573 : Blo 1348993 1519573 := bbase (se 7 (by rfl) ⟨17807, by rfl⟩ : syracuseStep 1519573 = 35615) (by norm_num)
theorem B1519609 : Blo 1348993 1519609 := bbase (se 2 (by rfl) ⟨569853, by rfl⟩ : syracuseStep 1519609 = 1139707) (by norm_num)
theorem B1708057 : Blo 1348993 1708057 := bbase (se 2 (by rfl) ⟨640521, by rfl⟩ : syracuseStep 1708057 = 1281043) (by norm_num)
theorem B1519645 : Blo 1348993 1519645 := bbase (se 3 (by rfl) ⟨284933, by rfl⟩ : syracuseStep 1519645 = 569867) (by norm_num)
theorem B1519681 : Blo 1348993 1519681 := bbase (se 2 (by rfl) ⟨569880, by rfl⟩ : syracuseStep 1519681 = 1139761) (by norm_num)
theorem B3649637 : Blo 1348993 3649637 := bbase (se 4 (by rfl) ⟨342153, by rfl⟩ : syracuseStep 3649637 = 684307) (by norm_num)
theorem B4558949 : Blo 1348993 4558949 := bbase (se 4 (by rfl) ⟨427401, by rfl⟩ : syracuseStep 4558949 = 854803) (by norm_num)
theorem B1519717 : Blo 1348993 1519717 := bbase (se 4 (by rfl) ⟨142473, by rfl⟩ : syracuseStep 1519717 = 284947) (by norm_num)
theorem B1519753 : Blo 1348993 1519753 := bbase (se 2 (by rfl) ⟨569907, by rfl⟩ : syracuseStep 1519753 = 1139815) (by norm_num)
theorem B3035285 : Blo 1348993 3035285 := bbase (se 6 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 3035285 = 142279) (by norm_num)
theorem B1519789 : Blo 1348993 1519789 := bbase (se 3 (by rfl) ⟨284960, by rfl⟩ : syracuseStep 1519789 = 569921) (by norm_num)
theorem B5124293 : Blo 1348993 5124293 := bbase (se 4 (by rfl) ⟨480402, by rfl⟩ : syracuseStep 5124293 = 960805) (by norm_num)
theorem B6574277 : Blo 1348993 6574277 := bbase (se 4 (by rfl) ⟨616338, by rfl⟩ : syracuseStep 6574277 = 1232677) (by norm_num)
theorem B1708229 : Blo 1348993 1708229 := bbase (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) (by norm_num)
theorem B3846341 : Blo 1348993 3846341 := bbase (se 4 (by rfl) ⟨360594, by rfl⟩ : syracuseStep 3846341 = 721189) (by norm_num)
theorem B1519825 : Blo 1348993 1519825 := bbase (se 2 (by rfl) ⟨569934, by rfl⟩ : syracuseStep 1519825 = 1139869) (by norm_num)
theorem B3035357 : Blo 1348993 3035357 := bbase (se 3 (by rfl) ⟨569129, by rfl⟩ : syracuseStep 3035357 = 1138259) (by norm_num)
theorem B2052325 : Blo 1348993 2052325 := bbase (se 4 (by rfl) ⟨192405, by rfl⟩ : syracuseStep 2052325 = 384811) (by norm_num)
theorem B1519861 : Blo 1348993 1519861 := bbase (se 5 (by rfl) ⟨71243, by rfl⟩ : syracuseStep 1519861 = 142487) (by norm_num)
theorem B1708285 : Blo 1348993 1708285 := bbase (se 3 (by rfl) ⟨320303, by rfl⟩ : syracuseStep 1708285 = 640607) (by norm_num)
theorem B2887949 : Blo 1348993 2887949 := bbase (se 3 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 2887949 = 1082981) (by norm_num)
theorem B3035429 : Blo 1348993 3035429 := bbase (se 4 (by rfl) ⟨284571, by rfl⟩ : syracuseStep 3035429 = 569143) (by norm_num)
theorem B1921325 : Blo 1348993 1921325 := bbase (se 3 (by rfl) ⟨360248, by rfl⟩ : syracuseStep 1921325 = 720497) (by norm_num)
theorem B5763413 : Blo 1348993 5763413 := bbase (se 10 (by rfl) ⟨8442, by rfl⟩ : syracuseStep 5763413 = 16885) (by norm_num)
theorem B1708381 : Blo 1348993 1708381 := bbase (se 3 (by rfl) ⟨320321, by rfl⟩ : syracuseStep 1708381 = 640643) (by norm_num)
theorem B3035501 : Blo 1348993 3035501 := bbase (se 3 (by rfl) ⟨569156, by rfl⟩ : syracuseStep 3035501 = 1138313) (by norm_num)
theorem B3035573 : Blo 1348993 3035573 := bbase (se 5 (by rfl) ⟨142292, by rfl⟩ : syracuseStep 3035573 = 284585) (by norm_num)
theorem B5476853 : Blo 1348993 5476853 := bbase (se 5 (by rfl) ⟨256727, by rfl⟩ : syracuseStep 5476853 = 513455) (by norm_num)
theorem B3035645 : Blo 1348993 3035645 := bbase (se 3 (by rfl) ⟨569183, by rfl⟩ : syracuseStep 3035645 = 1138367) (by norm_num)
theorem B1708553 : Blo 1348993 1708553 := bbase (se 2 (by rfl) ⟨640707, by rfl⟩ : syracuseStep 1708553 = 1281415) (by norm_num)
theorem B3650069 : Blo 1348993 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B4559381 : Blo 1348993 4559381 := bbase (se 6 (by rfl) ⟨106860, by rfl⟩ : syracuseStep 4559381 = 213721) (by norm_num)
theorem B1708609 : Blo 1348993 1708609 := bbase (se 2 (by rfl) ⟨640728, by rfl⟩ : syracuseStep 1708609 = 1281457) (by norm_num)
theorem B3035717 : Blo 1348993 3035717 := bbase (se 4 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 3035717 = 569197) (by norm_num)
theorem B3035789 : Blo 1348993 3035789 := bbase (se 3 (by rfl) ⟨569210, by rfl⟩ : syracuseStep 3035789 = 1138421) (by norm_num)
theorem B6836885 : Blo 1348993 6836885 := bbase (se 6 (by rfl) ⟨160239, by rfl⟩ : syracuseStep 6836885 = 320479) (by norm_num)
theorem B1708705 : Blo 1348993 1708705 := bbase (se 2 (by rfl) ⟨640764, by rfl⟩ : syracuseStep 1708705 = 1281529) (by norm_num)
theorem B4321957 : Blo 1348993 4321957 := bbase (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) (by norm_num)
theorem B3076789 : Blo 1348993 3076789 := bbase (se 5 (by rfl) ⟨144224, by rfl⟩ : syracuseStep 3076789 = 288449) (by norm_num)
theorem B1823413 : Blo 1348993 1823413 := bbase (se 5 (by rfl) ⟨85472, by rfl⟩ : syracuseStep 1823413 = 170945) (by norm_num)
theorem B6927029 : Blo 1348993 6927029 := bbase (se 5 (by rfl) ⟨324704, by rfl⟩ : syracuseStep 6927029 = 649409) (by norm_num)
theorem B3003061 : Blo 1348993 3003061 := bbase (se 5 (by rfl) ⟨140768, by rfl⟩ : syracuseStep 3003061 = 281537) (by norm_num)
theorem B3035861 : Blo 1348993 3035861 := bbase (se 7 (by rfl) ⟨35576, by rfl⟩ : syracuseStep 3035861 = 71153) (by norm_num)
theorem B3076829 : Blo 1348993 3076829 := bbase (se 3 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 3076829 = 1153811) (by norm_num)
theorem B4862693 : Blo 1348993 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B3035933 : Blo 1348993 3035933 := bbase (se 3 (by rfl) ⟨569237, by rfl⟩ : syracuseStep 3035933 = 1138475) (by norm_num)
theorem B1708877 : Blo 1348993 1708877 := bbase (se 3 (by rfl) ⟨320414, by rfl⟩ : syracuseStep 1708877 = 640829) (by norm_num)
theorem B10253141 : Blo 1348993 10253141 := bbase (se 9 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 10253141 = 60077) (by norm_num)
theorem B3036005 : Blo 1348993 3036005 := bbase (se 4 (by rfl) ⟨284625, by rfl⟩ : syracuseStep 3036005 = 569251) (by norm_num)
theorem B1708933 : Blo 1348993 1708933 := bbase (se 4 (by rfl) ⟨160212, by rfl⟩ : syracuseStep 1708933 = 320425) (by norm_num)
theorem B1823629 : Blo 1348993 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B3036077 : Blo 1348993 3036077 := bbase (se 3 (by rfl) ⟨569264, by rfl⟩ : syracuseStep 3036077 = 1138529) (by norm_num)
theorem B1561529 : Blo 1348993 1561529 := bbase (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) (by norm_num)
theorem B2053085 : Blo 1348993 2053085 := bbase (se 3 (by rfl) ⟨384953, by rfl⟩ : syracuseStep 2053085 = 769907) (by norm_num)
theorem B2339813 : Blo 1348993 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B1709029 : Blo 1348993 1709029 := bbase (se 4 (by rfl) ⟨160221, by rfl⟩ : syracuseStep 1709029 = 320443) (by norm_num)
theorem B3036149 : Blo 1348993 3036149 := bbase (se 5 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 3036149 = 284639) (by norm_num)
theorem B2561053 : Blo 1348993 2561053 := bbase (se 3 (by rfl) ⟨480197, by rfl⟩ : syracuseStep 2561053 = 960395) (by norm_num)
theorem B1922077 : Blo 1348993 1922077 := bbase (se 3 (by rfl) ⟨360389, by rfl⟩ : syracuseStep 1922077 = 720779) (by norm_num)
theorem B4617253 : Blo 1348993 4617253 := bbase (se 4 (by rfl) ⟨432867, by rfl⟩ : syracuseStep 4617253 = 865735) (by norm_num)
theorem B3036221 : Blo 1348993 3036221 := bbase (se 3 (by rfl) ⟨569291, by rfl⟩ : syracuseStep 3036221 = 1138583) (by norm_num)
theorem B3036293 : Blo 1348993 3036293 := bbase (se 4 (by rfl) ⟨284652, by rfl⟩ : syracuseStep 3036293 = 569305) (by norm_num)
theorem B1709201 : Blo 1348993 1709201 := bbase (se 2 (by rfl) ⟨640950, by rfl⟩ : syracuseStep 1709201 = 1281901) (by norm_num)
theorem B2561213 : Blo 1348993 2561213 := bbase (se 3 (by rfl) ⟨480227, by rfl⟩ : syracuseStep 2561213 = 960455) (by norm_num)
theorem B1709257 : Blo 1348993 1709257 := bbase (se 2 (by rfl) ⟨640971, by rfl⟩ : syracuseStep 1709257 = 1281943) (by norm_num)
theorem B3036365 : Blo 1348993 3036365 := bbase (se 3 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 3036365 = 1138637) (by norm_num)
theorem B10245365 : Blo 1348993 10245365 := bbase (se 5 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 10245365 = 960503) (by norm_num)
theorem B3036437 : Blo 1348993 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B1709353 : Blo 1348993 1709353 := bbase (se 2 (by rfl) ⟨641007, by rfl⟩ : syracuseStep 1709353 = 1282015) (by norm_num)
theorem B2561357 : Blo 1348993 2561357 := bbase (se 3 (by rfl) ⟨480254, by rfl⟩ : syracuseStep 2561357 = 960509) (by norm_num)
theorem B3036509 : Blo 1348993 3036509 := bbase (se 3 (by rfl) ⟨569345, by rfl⟩ : syracuseStep 3036509 = 1138691) (by norm_num)
theorem B5125477 : Blo 1348993 5125477 := bbase (se 4 (by rfl) ⟨480513, by rfl⟩ : syracuseStep 5125477 = 961027) (by norm_num)
theorem B3036581 : Blo 1348993 3036581 := bbase (se 4 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 3036581 = 569359) (by norm_num)
theorem B8648117 : Blo 1348993 8648117 := bbase (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) (by norm_num)
theorem B7689653 : Blo 1348993 7689653 := bbase (se 5 (by rfl) ⟨360452, by rfl⟩ : syracuseStep 7689653 = 720905) (by norm_num)
theorem B1709525 : Blo 1348993 1709525 := bbase (se 7 (by rfl) ⟨20033, by rfl⟩ : syracuseStep 1709525 = 40067) (by norm_num)
theorem B3036653 : Blo 1348993 3036653 := bbase (se 3 (by rfl) ⟨569372, by rfl⟩ : syracuseStep 3036653 = 1138745) (by norm_num)
theorem B1709581 : Blo 1348993 1709581 := bbase (se 3 (by rfl) ⟨320546, by rfl⟩ : syracuseStep 1709581 = 641093) (by norm_num)
theorem B2053669 : Blo 1348993 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B3036725 : Blo 1348993 3036725 := bbase (se 5 (by rfl) ⟨142346, by rfl⟩ : syracuseStep 3036725 = 284693) (by norm_num)
theorem B2561645 : Blo 1348993 2561645 := bbase (se 3 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 2561645 = 960617) (by norm_num)
theorem B1709677 : Blo 1348993 1709677 := bbase (se 3 (by rfl) ⟨320564, by rfl⟩ : syracuseStep 1709677 = 641129) (by norm_num)
theorem B3036797 : Blo 1348993 3036797 := bbase (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) (by norm_num)
theorem B3241613 : Blo 1348993 3241613 := bbase (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) (by norm_num)
theorem B5125781 : Blo 1348993 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B12981941 : Blo 1348993 12981941 := bbase (se 5 (by rfl) ⟨608528, by rfl⟩ : syracuseStep 12981941 = 1217057) (by norm_num)
theorem B3036869 : Blo 1348993 3036869 := bbase (se 4 (by rfl) ⟨284706, by rfl⟩ : syracuseStep 3036869 = 569413) (by norm_num)
theorem B4863701 : Blo 1348993 4863701 := bbase (se 7 (by rfl) ⟨56996, by rfl⟩ : syracuseStep 4863701 = 113993) (by norm_num)
theorem B2561797 : Blo 1348993 2561797 := bbase (se 4 (by rfl) ⟨240168, by rfl⟩ : syracuseStep 2561797 = 480337) (by norm_num)
theorem B3036941 : Blo 1348993 3036941 := bbase (se 3 (by rfl) ⟨569426, by rfl⟩ : syracuseStep 3036941 = 1138853) (by norm_num)
theorem B1709849 : Blo 1348993 1709849 := bbase (se 2 (by rfl) ⟨641193, by rfl⟩ : syracuseStep 1709849 = 1282387) (by norm_num)
theorem B1922869 : Blo 1348993 1922869 := bbase (se 5 (by rfl) ⟨90134, by rfl⟩ : syracuseStep 1922869 = 180269) (by norm_num)
theorem B3037013 : Blo 1348993 3037013 := bbase (se 9 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 3037013 = 17795) (by norm_num)
theorem B3037085 : Blo 1348993 3037085 := bbase (se 3 (by rfl) ⟨569453, by rfl⟩ : syracuseStep 3037085 = 1138907) (by norm_num)
theorem B6838181 : Blo 1348993 6838181 := bbase (se 4 (by rfl) ⟨641079, by rfl⟩ : syracuseStep 6838181 = 1282159) (by norm_num)
theorem B3037157 : Blo 1348993 3037157 := bbase (se 4 (by rfl) ⟨284733, by rfl⟩ : syracuseStep 3037157 = 569467) (by norm_num)
theorem B3037229 : Blo 1348993 3037229 := bbase (se 3 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 3037229 = 1138961) (by norm_num)
theorem B2562101 : Blo 1348993 2562101 := bbase (se 5 (by rfl) ⟨120098, by rfl⟩ : syracuseStep 2562101 = 240197) (by norm_num)
theorem B3242045 : Blo 1348993 3242045 := bbase (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) (by norm_num)
theorem B21878869 : Blo 1348993 21878869 := bbase (se 8 (by rfl) ⟨128196, by rfl⟩ : syracuseStep 21878869 = 256393) (by norm_num)
theorem B34576469 : Blo 1348993 34576469 := bbase (se 8 (by rfl) ⟨202596, by rfl⟩ : syracuseStep 34576469 = 405193) (by norm_num)
theorem B3037301 : Blo 1348993 3037301 := bbase (se 5 (by rfl) ⟨142373, by rfl⟩ : syracuseStep 3037301 = 284747) (by norm_num)
theorem B1923205 : Blo 1348993 1923205 := bbase (se 4 (by rfl) ⟨180300, by rfl⟩ : syracuseStep 1923205 = 360601) (by norm_num)
theorem B3037373 : Blo 1348993 3037373 := bbase (se 3 (by rfl) ⟨569507, by rfl⟩ : syracuseStep 3037373 = 1139015) (by norm_num)
theorem B4552901 : Blo 1348993 4552901 := bbase (se 4 (by rfl) ⟨426834, by rfl⟩ : syracuseStep 4552901 = 853669) (by norm_num)
theorem B3037445 : Blo 1348993 3037445 := bbase (se 4 (by rfl) ⟨284760, by rfl⟩ : syracuseStep 3037445 = 569521) (by norm_num)
theorem B6830405 : Blo 1348993 6830405 := bbase (se 4 (by rfl) ⟨640350, by rfl⟩ : syracuseStep 6830405 = 1280701) (by norm_num)
theorem B3037517 : Blo 1348993 3037517 := bbase (se 3 (by rfl) ⟨569534, by rfl⟩ : syracuseStep 3037517 = 1139069) (by norm_num)
theorem B41564501 : Blo 1348993 41564501 := bbase (se 10 (by rfl) ⟨60885, by rfl⟩ : syracuseStep 41564501 = 121771) (by norm_num)
theorem B1923421 : Blo 1348993 1923421 := bbase (se 3 (by rfl) ⟨360641, by rfl⟩ : syracuseStep 1923421 = 721283) (by norm_num)
theorem B3037589 : Blo 1348993 3037589 := bbase (se 6 (by rfl) ⟨71193, by rfl⟩ : syracuseStep 3037589 = 142387) (by norm_num)
theorem B3037661 : Blo 1348993 3037661 := bbase (se 3 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 3037661 = 1139123) (by norm_num)
theorem B3037733 : Blo 1348993 3037733 := bbase (se 4 (by rfl) ⟨284787, by rfl⟩ : syracuseStep 3037733 = 569575) (by norm_num)
theorem B2882117 : Blo 1348993 2882117 := bbase (se 4 (by rfl) ⟨270198, by rfl⟩ : syracuseStep 2882117 = 540397) (by norm_num)
theorem B4618853 : Blo 1348993 4618853 := bbase (se 4 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 4618853 = 866035) (by norm_num)
theorem B3037805 : Blo 1348993 3037805 := bbase (se 3 (by rfl) ⟨569588, by rfl⟩ : syracuseStep 3037805 = 1139177) (by norm_num)
theorem B4553333 : Blo 1348993 4553333 := bbase (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) (by norm_num)
theorem B3242621 : Blo 1348993 3242621 := bbase (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) (by norm_num)
theorem B3037877 : Blo 1348993 3037877 := bbase (se 5 (by rfl) ⟨142400, by rfl⟩ : syracuseStep 3037877 = 284801) (by norm_num)
theorem B2882261 : Blo 1348993 2882261 := bbase (se 7 (by rfl) ⟨33776, by rfl⟩ : syracuseStep 2882261 = 67553) (by norm_num)
theorem B3414757 : Blo 1348993 3414757 := bbase (se 4 (by rfl) ⟨320133, by rfl⟩ : syracuseStep 3414757 = 640267) (by norm_num)
theorem B3037949 : Blo 1348993 3037949 := bbase (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) (by norm_num)
theorem B4381445 : Blo 1348993 4381445 := bbase (se 4 (by rfl) ⟨410760, by rfl⟩ : syracuseStep 4381445 = 821521) (by norm_num)
theorem B2562853 : Blo 1348993 2562853 := bbase (se 4 (by rfl) ⟨240267, by rfl⟩ : syracuseStep 2562853 = 480535) (by norm_num)
theorem B3038021 : Blo 1348993 3038021 := bbase (se 4 (by rfl) ⟨284814, by rfl⟩ : syracuseStep 3038021 = 569629) (by norm_num)
theorem B3414869 : Blo 1348993 3414869 := bbase (se 9 (by rfl) ⟨10004, by rfl⟩ : syracuseStep 3414869 = 20009) (by norm_num)
theorem B1825661 : Blo 1348993 1825661 := bbase (se 3 (by rfl) ⟨342311, by rfl⟩ : syracuseStep 1825661 = 684623) (by norm_num)
theorem B3038093 : Blo 1348993 3038093 := bbase (se 3 (by rfl) ⟨569642, by rfl⟩ : syracuseStep 3038093 = 1139285) (by norm_num)
theorem B1440661 : Blo 1348993 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B2562997 : Blo 1348993 2562997 := bbase (se 5 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 2562997 = 240281) (by norm_num)
theorem B3038165 : Blo 1348993 3038165 := bbase (se 7 (by rfl) ⟨35603, by rfl⟩ : syracuseStep 3038165 = 71207) (by norm_num)
theorem B1440785 : Blo 1348993 1440785 := bbase (se 2 (by rfl) ⟨540294, by rfl⟩ : syracuseStep 1440785 = 1080589) (by norm_num)
theorem B3415061 : Blo 1348993 3415061 := bbase (se 6 (by rfl) ⟨80040, by rfl⟩ : syracuseStep 3415061 = 160081) (by norm_num)
theorem B3038237 : Blo 1348993 3038237 := bbase (se 3 (by rfl) ⟨569669, by rfl⟩ : syracuseStep 3038237 = 1139339) (by norm_num)
theorem B4553765 : Blo 1348993 4553765 := bbase (se 4 (by rfl) ⟨426915, by rfl⟩ : syracuseStep 4553765 = 853831) (by norm_num)
theorem B2882621 : Blo 1348993 2882621 := bbase (se 3 (by rfl) ⟨540491, by rfl⟩ : syracuseStep 2882621 = 1080983) (by norm_num)
theorem B2276437 : Blo 1348993 2276437 := bbase (se 8 (by rfl) ⟨13338, by rfl⟩ : syracuseStep 2276437 = 26677) (by norm_num)
theorem B2563157 : Blo 1348993 2563157 := bbase (se 8 (by rfl) ⟨15018, by rfl⟩ : syracuseStep 2563157 = 30037) (by norm_num)
theorem B3038309 : Blo 1348993 3038309 := bbase (se 4 (by rfl) ⟨284841, by rfl⟩ : syracuseStep 3038309 = 569683) (by norm_num)
theorem B2309285 : Blo 1348993 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B2276525 : Blo 1348993 2276525 := bbase (se 3 (by rfl) ⟨426848, by rfl⟩ : syracuseStep 2276525 = 853697) (by norm_num)
theorem B3038381 : Blo 1348993 3038381 := bbase (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) (by norm_num)
theorem B2432197 : Blo 1348993 2432197 := bbase (se 4 (by rfl) ⟨228018, by rfl⟩ : syracuseStep 2432197 = 456037) (by norm_num)
theorem B2923733 : Blo 1348993 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B2563301 : Blo 1348993 2563301 := bbase (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) (by norm_num)
theorem B2161901 : Blo 1348993 2161901 := bbase (se 3 (by rfl) ⟨405356, by rfl⟩ : syracuseStep 2161901 = 810713) (by norm_num)
theorem B3038453 : Blo 1348993 3038453 := bbase (se 5 (by rfl) ⟨142427, by rfl⟩ : syracuseStep 3038453 = 284855) (by norm_num)
theorem B1441037 : Blo 1348993 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B2432269 : Blo 1348993 2432269 := bbase (se 3 (by rfl) ⟨456050, by rfl⟩ : syracuseStep 2432269 = 912101) (by norm_num)
theorem B2276653 : Blo 1348993 2276653 := bbase (se 3 (by rfl) ⟨426872, by rfl⟩ : syracuseStep 2276653 = 853745) (by norm_num)
theorem B3038525 : Blo 1348993 3038525 := bbase (se 3 (by rfl) ⟨569723, by rfl⟩ : syracuseStep 3038525 = 1139447) (by norm_num)
theorem B3415405 : Blo 1348993 3415405 := bbase (se 3 (by rfl) ⟨640388, by rfl⟩ : syracuseStep 3415405 = 1280777) (by norm_num)
theorem B2276741 : Blo 1348993 2276741 := bbase (se 4 (by rfl) ⟨213444, by rfl⟩ : syracuseStep 2276741 = 426889) (by norm_num)
theorem B3038597 : Blo 1348993 3038597 := bbase (se 4 (by rfl) ⟨284868, by rfl⟩ : syracuseStep 3038597 = 569737) (by norm_num)
theorem B2735525 : Blo 1348993 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B3038669 : Blo 1348993 3038669 := bbase (se 3 (by rfl) ⟨569750, by rfl⟩ : syracuseStep 3038669 = 1139501) (by norm_num)
theorem B4554197 : Blo 1348993 4554197 := bbase (se 7 (by rfl) ⟨53369, by rfl⟩ : syracuseStep 4554197 = 106739) (by norm_num)
theorem B3415517 : Blo 1348993 3415517 := bbase (se 3 (by rfl) ⟨640409, by rfl⟩ : syracuseStep 3415517 = 1280819) (by norm_num)
theorem B4324853 : Blo 1348993 4324853 := bbase (se 5 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 4324853 = 405455) (by norm_num)
theorem B2276869 : Blo 1348993 2276869 := bbase (se 4 (by rfl) ⟨213456, by rfl⟩ : syracuseStep 2276869 = 426913) (by norm_num)
theorem B2563589 : Blo 1348993 2563589 := bbase (se 4 (by rfl) ⟨240336, by rfl⟩ : syracuseStep 2563589 = 480673) (by norm_num)
theorem B3038741 : Blo 1348993 3038741 := bbase (se 6 (by rfl) ⟨71220, by rfl⟩ : syracuseStep 3038741 = 142441) (by norm_num)
theorem B1621541 : Blo 1348993 1621541 := bbase (se 4 (by rfl) ⟨152019, by rfl⟩ : syracuseStep 1621541 = 304039) (by norm_num)
theorem B5766709 : Blo 1348993 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B6831701 : Blo 1348993 6831701 := bbase (se 8 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 6831701 = 80059) (by norm_num)
theorem B7691861 : Blo 1348993 7691861 := bbase (se 8 (by rfl) ⟨45069, by rfl⟩ : syracuseStep 7691861 = 90139) (by norm_num)
theorem B2276957 : Blo 1348993 2276957 := bbase (se 3 (by rfl) ⟨426929, by rfl⟩ : syracuseStep 2276957 = 853859) (by norm_num)
theorem B3038813 : Blo 1348993 3038813 := bbase (se 3 (by rfl) ⟨569777, by rfl⟩ : syracuseStep 3038813 = 1139555) (by norm_num)
theorem B2252405 : Blo 1348993 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1367689 : Blo 1348993 1367689 := bbase (se 2 (by rfl) ⟨512883, by rfl⟩ : syracuseStep 1367689 = 1025767) (by norm_num)
theorem B1621657 : Blo 1348993 1621657 := bbase (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) (by norm_num)
theorem B3415709 : Blo 1348993 3415709 := bbase (se 3 (by rfl) ⟨640445, by rfl⟩ : syracuseStep 3415709 = 1280891) (by norm_num)
theorem B2563741 : Blo 1348993 2563741 := bbase (se 3 (by rfl) ⟨480701, by rfl⟩ : syracuseStep 2563741 = 961403) (by norm_num)
theorem B3038885 : Blo 1348993 3038885 := bbase (se 4 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 3038885 = 569791) (by norm_num)
theorem B1441481 : Blo 1348993 1441481 := bbase (se 2 (by rfl) ⟨540555, by rfl⟩ : syracuseStep 1441481 = 1081111) (by norm_num)
theorem B3464909 : Blo 1348993 3464909 := bbase (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) (by norm_num)
theorem B5127893 : Blo 1348993 5127893 := bbase (se 7 (by rfl) ⟨60092, by rfl⟩ : syracuseStep 5127893 = 120185) (by norm_num)
theorem B2277085 : Blo 1348993 2277085 := bbase (se 3 (by rfl) ⟨426953, by rfl⟩ : syracuseStep 2277085 = 853907) (by norm_num)
theorem B1621729 : Blo 1348993 1621729 := bbase (se 2 (by rfl) ⟨608148, by rfl⟩ : syracuseStep 1621729 = 1216297) (by norm_num)
theorem B3038957 : Blo 1348993 3038957 := bbase (se 3 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 3038957 = 1139609) (by norm_num)
theorem B16637717 : Blo 1348993 16637717 := bbase (se 6 (by rfl) ⟨389946, by rfl⟩ : syracuseStep 16637717 = 779893) (by norm_num)
theorem B2277173 : Blo 1348993 2277173 := bbase (se 5 (by rfl) ⟨106742, by rfl⟩ : syracuseStep 2277173 = 213485) (by norm_num)
theorem B3039029 : Blo 1348993 3039029 := bbase (se 5 (by rfl) ⟨142454, by rfl⟩ : syracuseStep 3039029 = 284909) (by norm_num)
theorem B10944341 : Blo 1348993 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B1621849 : Blo 1348993 1621849 := bbase (se 2 (by rfl) ⟨608193, by rfl⟩ : syracuseStep 1621849 = 1216387) (by norm_num)
theorem B3039101 : Blo 1348993 3039101 := bbase (se 3 (by rfl) ⟨569831, by rfl⟩ : syracuseStep 3039101 = 1139663) (by norm_num)
theorem B4554629 : Blo 1348993 4554629 := bbase (se 4 (by rfl) ⟨426996, by rfl⟩ : syracuseStep 4554629 = 853993) (by norm_num)
theorem B2277301 : Blo 1348993 2277301 := bbase (se 5 (by rfl) ⟨106748, by rfl⟩ : syracuseStep 2277301 = 213497) (by norm_num)
theorem B2883509 : Blo 1348993 2883509 := bbase (se 5 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 2883509 = 270329) (by norm_num)
theorem B1441729 : Blo 1348993 1441729 := bbase (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) (by norm_num)
theorem B3039173 : Blo 1348993 3039173 := bbase (se 4 (by rfl) ⟨284922, by rfl⟩ : syracuseStep 3039173 = 569845) (by norm_num)
theorem B2564045 : Blo 1348993 2564045 := bbase (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) (by norm_num)
theorem B3416053 : Blo 1348993 3416053 := bbase (se 5 (by rfl) ⟨160127, by rfl⟩ : syracuseStep 3416053 = 320255) (by norm_num)
theorem B5128181 : Blo 1348993 5128181 := bbase (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) (by norm_num)
theorem B2277409 : Blo 1348993 2277409 := bstep (se 2 (by rfl) ⟨854028, by rfl⟩ : syracuseStep 2277409 = 1708057) B1708057
theorem B3842093 : Blo 1348993 3842093 := bstep (se 3 (by rfl) ⟨720392, by rfl⟩ : syracuseStep 3842093 = 1440785) B1440785
theorem B3039281 : Blo 1348993 3039281 := bstep (se 2 (by rfl) ⟨1139730, by rfl⟩ : syracuseStep 3039281 = 2279461) B2279461
theorem B1540147 : Blo 1348993 1540147 := bstep (se 1 (by rfl) ⟨1155110, by rfl⟩ : syracuseStep 1540147 = 2310221) B2310221
theorem B2277443 : Blo 1348993 2277443 := bstep (se 1 (by rfl) ⟨1708082, by rfl⟩ : syracuseStep 2277443 = 3416165) B3416165
theorem B2433091 : Blo 1348993 2433091 := bstep (se 1 (by rfl) ⟨1824818, by rfl⟩ : syracuseStep 2433091 = 3649637) B3649637
theorem B3039299 : Blo 1348993 3039299 := bstep (se 1 (by rfl) ⟨2279474, by rfl⟩ : syracuseStep 3039299 = 4558949) B4558949
theorem B2023505 : Blo 1348993 2023505 := bstep (se 2 (by rfl) ⟨758814, by rfl⟩ : syracuseStep 2023505 = 1517629) B1517629
theorem B2023523 : Blo 1348993 2023523 := bstep (se 1 (by rfl) ⟨1517642, by rfl⟩ : syracuseStep 2023523 = 3035285) B3035285
theorem B1441891 : Blo 1348993 1441891 := bstep (se 1 (by rfl) ⟨1081418, by rfl⟩ : syracuseStep 1441891 = 2162837) B2162837
theorem B29171825 : Blo 1348993 29171825 := bstep (se 2 (by rfl) ⟨10939434, by rfl⟩ : syracuseStep 29171825 = 21878869) B21878869
theorem B31162481 : Blo 1348993 31162481 := bstep (se 2 (by rfl) ⟨11685930, by rfl⟩ : syracuseStep 31162481 = 23371861) B23371861
theorem B2023553 : Blo 1348993 2023553 := bstep (se 2 (by rfl) ⟨758832, by rfl⟩ : syracuseStep 2023553 = 1517665) B1517665
theorem B3416195 : Blo 1348993 3416195 := bstep (se 1 (by rfl) ⟨2562146, by rfl⟩ : syracuseStep 3416195 = 5124293) B5124293
theorem B4382851 : Blo 1348993 4382851 := bstep (se 1 (by rfl) ⟨3287138, by rfl⟩ : syracuseStep 4382851 = 6574277) B6574277
theorem B2564227 : Blo 1348993 2564227 := bstep (se 1 (by rfl) ⟨1923170, by rfl⟩ : syracuseStep 2564227 = 3846341) B3846341
theorem B2023571 : Blo 1348993 2023571 := bstep (se 1 (by rfl) ⟨1517678, by rfl⟩ : syracuseStep 2023571 = 3035357) B3035357
theorem B2023601 : Blo 1348993 2023601 := bstep (se 2 (by rfl) ⟨758850, by rfl⟩ : syracuseStep 2023601 = 1517701) B1517701
theorem B2564273 : Blo 1348993 2564273 := bstep (se 2 (by rfl) ⟨961602, by rfl⟩ : syracuseStep 2564273 = 1923205) B1923205
theorem B1925299 : Blo 1348993 1925299 := bstep (se 1 (by rfl) ⟨1443974, by rfl⟩ : syracuseStep 1925299 = 2887949) B2887949
theorem B2023619 : Blo 1348993 2023619 := bstep (se 1 (by rfl) ⟨1517714, by rfl⟩ : syracuseStep 2023619 = 3035429) B3035429
theorem B2277571 : Blo 1348993 2277571 := bstep (se 1 (by rfl) ⟨1708178, by rfl⟩ : syracuseStep 2277571 = 3416357) B3416357
theorem B2023649 : Blo 1348993 2023649 := bstep (se 2 (by rfl) ⟨758868, by rfl⟩ : syracuseStep 2023649 = 1517737) B1517737
theorem B3842275 : Blo 1348993 3842275 := bstep (se 1 (by rfl) ⟨2881706, by rfl⟩ : syracuseStep 3842275 = 5763413) B5763413
theorem B2023667 : Blo 1348993 2023667 := bstep (se 1 (by rfl) ⟨1517750, by rfl⟩ : syracuseStep 2023667 = 3035501) B3035501
theorem B2023697 : Blo 1348993 2023697 := bstep (se 2 (by rfl) ⟨758886, by rfl⟩ : syracuseStep 2023697 = 1517773) B1517773
theorem B2023715 : Blo 1348993 2023715 := bstep (se 1 (by rfl) ⟨1517786, by rfl⟩ : syracuseStep 2023715 = 3035573) B3035573
theorem B2736433 : Blo 1348993 2736433 := bstep (se 2 (by rfl) ⟨1026162, by rfl⟩ : syracuseStep 2736433 = 2052325) B2052325
theorem B2023745 : Blo 1348993 2023745 := bstep (se 2 (by rfl) ⟨758904, by rfl⟩ : syracuseStep 2023745 = 1517809) B1517809
theorem B4325699 : Blo 1348993 4325699 := bstep (se 1 (by rfl) ⟨3244274, by rfl⟩ : syracuseStep 4325699 = 6488549) B6488549
theorem B2277713 : Blo 1348993 2277713 := bstep (se 2 (by rfl) ⟨854142, by rfl⟩ : syracuseStep 2277713 = 1708285) B1708285
theorem B3039569 : Blo 1348993 3039569 := bstep (se 2 (by rfl) ⟨1139838, by rfl⟩ : syracuseStep 3039569 = 2279677) B2279677
theorem B2023763 : Blo 1348993 2023763 := bstep (se 1 (by rfl) ⟨1517822, by rfl⟩ : syracuseStep 2023763 = 3035645) B3035645
theorem B3039587 : Blo 1348993 3039587 := bstep (se 1 (by rfl) ⟨2279690, by rfl⟩ : syracuseStep 3039587 = 4559381) B4559381
theorem B2023793 : Blo 1348993 2023793 := bstep (se 2 (by rfl) ⟨758922, by rfl⟩ : syracuseStep 2023793 = 1517845) B1517845
theorem B1622387 : Blo 1348993 1622387 := bstep (se 1 (by rfl) ⟨1216790, by rfl⟩ : syracuseStep 1622387 = 2433581) B2433581
theorem B2023811 : Blo 1348993 2023811 := bstep (se 1 (by rfl) ⟨1517858, by rfl⟩ : syracuseStep 2023811 = 3035717) B3035717
theorem B2023841 : Blo 1348993 2023841 := bstep (se 2 (by rfl) ⟨758940, by rfl⟩ : syracuseStep 2023841 = 1517881) B1517881
theorem B1622435 : Blo 1348993 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B2023859 : Blo 1348993 2023859 := bstep (se 1 (by rfl) ⟨1517894, by rfl⟩ : syracuseStep 2023859 = 3035789) B3035789
theorem B2023889 : Blo 1348993 2023889 := bstep (se 2 (by rfl) ⟨758958, by rfl⟩ : syracuseStep 2023889 = 1517917) B1517917
theorem B2277841 : Blo 1348993 2277841 := bstep (se 2 (by rfl) ⟨854190, by rfl⟩ : syracuseStep 2277841 = 1708381) B1708381
theorem B2564561 : Blo 1348993 2564561 := bstep (se 2 (by rfl) ⟨961710, by rfl⟩ : syracuseStep 2564561 = 1923421) B1923421
theorem B2023907 : Blo 1348993 2023907 := bstep (se 1 (by rfl) ⟨1517930, by rfl⟩ : syracuseStep 2023907 = 3035861) B3035861
theorem B2277875 : Blo 1348993 2277875 := bstep (se 1 (by rfl) ⟨1708406, by rfl⟩ : syracuseStep 2277875 = 3416813) B3416813
theorem B2023937 : Blo 1348993 2023937 := bstep (se 2 (by rfl) ⟨758976, by rfl⟩ : syracuseStep 2023937 = 1517953) B1517953
theorem B2884099 : Blo 1348993 2884099 := bstep (se 1 (by rfl) ⟨2163074, by rfl⟩ : syracuseStep 2884099 = 4326149) B4326149
theorem B4555277 : Blo 1348993 4555277 := bstep (se 3 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 4555277 = 1708229) B1708229
theorem B2023955 : Blo 1348993 2023955 := bstep (se 1 (by rfl) ⟨1517966, by rfl⟩ : syracuseStep 2023955 = 3035933) B3035933
theorem B1442323 : Blo 1348993 1442323 := bstep (se 1 (by rfl) ⟨1081742, by rfl⟩ : syracuseStep 1442323 = 2163485) B2163485
theorem B2023985 : Blo 1348993 2023985 := bstep (se 2 (by rfl) ⟨758994, by rfl⟩ : syracuseStep 2023985 = 1517989) B1517989
theorem B2024003 : Blo 1348993 2024003 := bstep (se 1 (by rfl) ⟨1518002, by rfl⟩ : syracuseStep 2024003 = 3036005) B3036005
theorem B4555331 : Blo 1348993 4555331 := bstep (se 1 (by rfl) ⟨3416498, by rfl⟩ : syracuseStep 4555331 = 6832997) B6832997
theorem B4620881 : Blo 1348993 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B2024033 : Blo 1348993 2024033 := bstep (se 2 (by rfl) ⟨759012, by rfl⟩ : syracuseStep 2024033 = 1518025) B1518025
theorem B2024051 : Blo 1348993 2024051 := bstep (se 1 (by rfl) ⟨1518038, by rfl⟩ : syracuseStep 2024051 = 3036077) B3036077
theorem B2278003 : Blo 1348993 2278003 := bstep (se 1 (by rfl) ⟨1708502, by rfl⟩ : syracuseStep 2278003 = 3417005) B3417005
theorem B2024081 : Blo 1348993 2024081 := bstep (se 2 (by rfl) ⟨759030, by rfl⟩ : syracuseStep 2024081 = 1518061) B1518061
theorem B2024099 : Blo 1348993 2024099 := bstep (se 1 (by rfl) ⟨1518074, by rfl⟩ : syracuseStep 2024099 = 3036149) B3036149
theorem B2024129 : Blo 1348993 2024129 := bstep (se 2 (by rfl) ⟨759048, by rfl⟩ : syracuseStep 2024129 = 1518097) B1518097
theorem B2310851 : Blo 1348993 2310851 := bstep (se 1 (by rfl) ⟨1733138, by rfl⟩ : syracuseStep 2310851 = 3466277) B3466277
theorem B3842765 : Blo 1348993 3842765 := bstep (se 3 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 3842765 = 1441037) B1441037
theorem B2024147 : Blo 1348993 2024147 := bstep (se 1 (by rfl) ⟨1518110, by rfl⟩ : syracuseStep 2024147 = 3036221) B3036221
theorem B2024177 : Blo 1348993 2024177 := bstep (se 2 (by rfl) ⟨759066, by rfl⟩ : syracuseStep 2024177 = 1518133) B1518133
theorem B2278145 : Blo 1348993 2278145 := bstep (se 2 (by rfl) ⟨854304, by rfl⟩ : syracuseStep 2278145 = 1708609) B1708609
theorem B2024195 : Blo 1348993 2024195 := bstep (se 1 (by rfl) ⟨1518146, by rfl⟩ : syracuseStep 2024195 = 3036293) B3036293
theorem B2024225 : Blo 1348993 2024225 := bstep (se 2 (by rfl) ⟨759084, by rfl⟩ : syracuseStep 2024225 = 1518169) B1518169
theorem B2024243 : Blo 1348993 2024243 := bstep (se 1 (by rfl) ⟨1518182, by rfl⟩ : syracuseStep 2024243 = 3036365) B3036365
theorem B2024273 : Blo 1348993 2024273 := bstep (se 2 (by rfl) ⟨759102, by rfl⟩ : syracuseStep 2024273 = 1518205) B1518205
theorem B4555601 : Blo 1348993 4555601 := bstep (se 2 (by rfl) ⟨1708350, by rfl⟩ : syracuseStep 4555601 = 3416701) B3416701
theorem B2024291 : Blo 1348993 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B2024321 : Blo 1348993 2024321 := bstep (se 2 (by rfl) ⟨759120, by rfl⟩ : syracuseStep 2024321 = 1518241) B1518241
theorem B2278273 : Blo 1348993 2278273 := bstep (se 2 (by rfl) ⟨854352, by rfl⟩ : syracuseStep 2278273 = 1708705) B1708705
theorem B2024339 : Blo 1348993 2024339 := bstep (se 1 (by rfl) ⟨1518254, by rfl⟩ : syracuseStep 2024339 = 3036509) B3036509
theorem B7685027 : Blo 1348993 7685027 := bstep (se 1 (by rfl) ⟨5763770, by rfl⟩ : syracuseStep 7685027 = 11527541) B11527541
theorem B2278307 : Blo 1348993 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B2024369 : Blo 1348993 2024369 := bstep (se 2 (by rfl) ⟨759138, by rfl⟩ : syracuseStep 2024369 = 1518277) B1518277
theorem B2024387 : Blo 1348993 2024387 := bstep (se 1 (by rfl) ⟨1518290, by rfl⟩ : syracuseStep 2024387 = 3036581) B3036581
theorem B2024417 : Blo 1348993 2024417 := bstep (se 2 (by rfl) ⟨759156, by rfl⟩ : syracuseStep 2024417 = 1518313) B1518313
theorem B11535331 : Blo 1348993 11535331 := bstep (se 1 (by rfl) ⟨8651498, by rfl⟩ : syracuseStep 11535331 = 17302997) B17302997
theorem B2024435 : Blo 1348993 2024435 := bstep (se 1 (by rfl) ⟨1518326, by rfl⟩ : syracuseStep 2024435 = 3036653) B3036653
theorem B2024465 : Blo 1348993 2024465 := bstep (se 2 (by rfl) ⟨759174, by rfl⟩ : syracuseStep 2024465 = 1518349) B1518349
theorem B2024483 : Blo 1348993 2024483 := bstep (se 1 (by rfl) ⟨1518362, by rfl⟩ : syracuseStep 2024483 = 3036725) B3036725
theorem B2278435 : Blo 1348993 2278435 := bstep (se 1 (by rfl) ⟨1708826, by rfl⟩ : syracuseStep 2278435 = 3417653) B3417653
theorem B3417137 : Blo 1348993 3417137 := bstep (se 2 (by rfl) ⟨1281426, by rfl⟩ : syracuseStep 3417137 = 2562853) B2562853
theorem B2024513 : Blo 1348993 2024513 := bstep (se 2 (by rfl) ⟨759192, by rfl⟩ : syracuseStep 2024513 = 1518385) B1518385
theorem B2024531 : Blo 1348993 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B3417187 : Blo 1348993 3417187 := bstep (se 1 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 3417187 = 5125781) B5125781
theorem B2024561 : Blo 1348993 2024561 := bstep (se 2 (by rfl) ⟨759210, by rfl⟩ : syracuseStep 2024561 = 1518421) B1518421
theorem B2024579 : Blo 1348993 2024579 := bstep (se 1 (by rfl) ⟨1518434, by rfl⟩ : syracuseStep 2024579 = 3036869) B3036869
theorem B8651909 : Blo 1348993 8651909 := bstep (se 4 (by rfl) ⟨811116, by rfl⟩ : syracuseStep 8651909 = 1622233) B1622233
theorem B2024609 : Blo 1348993 2024609 := bstep (se 2 (by rfl) ⟨759228, by rfl⟩ : syracuseStep 2024609 = 1518457) B1518457
theorem B2278577 : Blo 1348993 2278577 := bstep (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) B1708933
theorem B2024627 : Blo 1348993 2024627 := bstep (se 1 (by rfl) ⟨1518470, by rfl⟩ : syracuseStep 2024627 = 3036941) B3036941
theorem B2024657 : Blo 1348993 2024657 := bstep (se 2 (by rfl) ⟨759246, by rfl⟩ : syracuseStep 2024657 = 1518493) B1518493
theorem B2024675 : Blo 1348993 2024675 := bstep (se 1 (by rfl) ⟨1518506, by rfl⟩ : syracuseStep 2024675 = 3037013) B3037013
theorem B3417329 : Blo 1348993 3417329 := bstep (se 2 (by rfl) ⟨1281498, by rfl⟩ : syracuseStep 3417329 = 2562997) B2562997
theorem B2024705 : Blo 1348993 2024705 := bstep (se 2 (by rfl) ⟨759264, by rfl⟩ : syracuseStep 2024705 = 1518529) B1518529
theorem B2024723 : Blo 1348993 2024723 := bstep (se 1 (by rfl) ⟨1518542, by rfl⟩ : syracuseStep 2024723 = 3037085) B3037085
theorem B2024753 : Blo 1348993 2024753 := bstep (se 2 (by rfl) ⟨759282, by rfl⟩ : syracuseStep 2024753 = 1518565) B1518565
theorem B2278705 : Blo 1348993 2278705 := bstep (se 2 (by rfl) ⟨854514, by rfl⟩ : syracuseStep 2278705 = 1709029) B1709029
theorem B2024771 : Blo 1348993 2024771 := bstep (se 1 (by rfl) ⟨1518578, by rfl⟩ : syracuseStep 2024771 = 3037157) B3037157
theorem B2278739 : Blo 1348993 2278739 := bstep (se 1 (by rfl) ⟨1709054, by rfl⟩ : syracuseStep 2278739 = 3418109) B3418109
theorem B2024801 : Blo 1348993 2024801 := bstep (se 2 (by rfl) ⟨759300, by rfl⟩ : syracuseStep 2024801 = 1518601) B1518601
theorem B4556141 : Blo 1348993 4556141 := bstep (se 3 (by rfl) ⟨854276, by rfl⟩ : syracuseStep 4556141 = 1708553) B1708553
theorem B2024819 : Blo 1348993 2024819 := bstep (se 1 (by rfl) ⟨1518614, by rfl⟩ : syracuseStep 2024819 = 3037229) B3037229
theorem B9733517 : Blo 1348993 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B2024849 : Blo 1348993 2024849 := bstep (se 2 (by rfl) ⟨759318, by rfl⟩ : syracuseStep 2024849 = 1518637) B1518637
theorem B2024867 : Blo 1348993 2024867 := bstep (se 1 (by rfl) ⟨1518650, by rfl⟩ : syracuseStep 2024867 = 3037301) B3037301
theorem B4556195 : Blo 1348993 4556195 := bstep (se 1 (by rfl) ⟨3417146, by rfl⟩ : syracuseStep 4556195 = 6834293) B6834293
theorem B2024897 : Blo 1348993 2024897 := bstep (se 2 (by rfl) ⟨759336, by rfl⟩ : syracuseStep 2024897 = 1518673) B1518673
theorem B2024915 : Blo 1348993 2024915 := bstep (se 1 (by rfl) ⟨1518686, by rfl⟩ : syracuseStep 2024915 = 3037373) B3037373
theorem B2278867 : Blo 1348993 2278867 := bstep (se 1 (by rfl) ⟨1709150, by rfl⟩ : syracuseStep 2278867 = 3418301) B3418301
theorem B2024945 : Blo 1348993 2024945 := bstep (se 2 (by rfl) ⟨759354, by rfl⟩ : syracuseStep 2024945 = 1518709) B1518709
theorem B2024963 : Blo 1348993 2024963 := bstep (se 1 (by rfl) ⟨1518722, by rfl⟩ : syracuseStep 2024963 = 3037445) B3037445
theorem B4326929 : Blo 1348993 4326929 := bstep (se 2 (by rfl) ⟨1622598, by rfl⟩ : syracuseStep 4326929 = 3245197) B3245197
theorem B2024993 : Blo 1348993 2024993 := bstep (se 2 (by rfl) ⟨759372, by rfl⟩ : syracuseStep 2024993 = 1518745) B1518745
theorem B2025011 : Blo 1348993 2025011 := bstep (se 1 (by rfl) ⟨1518758, by rfl⟩ : syracuseStep 2025011 = 3037517) B3037517
theorem B2025041 : Blo 1348993 2025041 := bstep (se 2 (by rfl) ⟨759390, by rfl⟩ : syracuseStep 2025041 = 1518781) B1518781
theorem B2279009 : Blo 1348993 2279009 := bstep (se 2 (by rfl) ⟨854628, by rfl⟩ : syracuseStep 2279009 = 1709257) B1709257
theorem B2025059 : Blo 1348993 2025059 := bstep (se 1 (by rfl) ⟨1518794, by rfl⟩ : syracuseStep 2025059 = 3037589) B3037589
theorem B9733745 : Blo 1348993 9733745 := bstep (se 2 (by rfl) ⟨3650154, by rfl⟩ : syracuseStep 9733745 = 7300309) B7300309
theorem B2025089 : Blo 1348993 2025089 := bstep (se 2 (by rfl) ⟨759408, by rfl⟩ : syracuseStep 2025089 = 1518817) B1518817
theorem B6006413 : Blo 1348993 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B2025107 : Blo 1348993 2025107 := bstep (se 1 (by rfl) ⟨1518830, by rfl⟩ : syracuseStep 2025107 = 3037661) B3037661
theorem B4556465 : Blo 1348993 4556465 := bstep (se 2 (by rfl) ⟨1708674, by rfl⟩ : syracuseStep 4556465 = 3417349) B3417349
theorem B2025137 : Blo 1348993 2025137 := bstep (se 2 (by rfl) ⟨759426, by rfl⟩ : syracuseStep 2025137 = 1518853) B1518853
theorem B2025155 : Blo 1348993 2025155 := bstep (se 1 (by rfl) ⟨1518866, by rfl⟩ : syracuseStep 2025155 = 3037733) B3037733
theorem B2025185 : Blo 1348993 2025185 := bstep (se 2 (by rfl) ⟨759444, by rfl⟩ : syracuseStep 2025185 = 1518889) B1518889
theorem B2279137 : Blo 1348993 2279137 := bstep (se 2 (by rfl) ⟨854676, by rfl⟩ : syracuseStep 2279137 = 1709353) B1709353
theorem B9733859 : Blo 1348993 9733859 := bstep (se 1 (by rfl) ⟨7300394, by rfl⟩ : syracuseStep 9733859 = 14600789) B14600789
theorem B2025203 : Blo 1348993 2025203 := bstep (se 1 (by rfl) ⟨1518902, by rfl⟩ : syracuseStep 2025203 = 3037805) B3037805
theorem B2279171 : Blo 1348993 2279171 := bstep (se 1 (by rfl) ⟨1709378, by rfl⟩ : syracuseStep 2279171 = 3418757) B3418757
theorem B2025233 : Blo 1348993 2025233 := bstep (se 2 (by rfl) ⟨759462, by rfl⟩ : syracuseStep 2025233 = 1518925) B1518925
theorem B2025251 : Blo 1348993 2025251 := bstep (se 1 (by rfl) ⟨1518938, by rfl⟩ : syracuseStep 2025251 = 3037877) B3037877
theorem B6833969 : Blo 1348993 6833969 := bstep (se 2 (by rfl) ⟨2562738, by rfl⟩ : syracuseStep 6833969 = 5125477) B5125477
theorem B2025281 : Blo 1348993 2025281 := bstep (se 2 (by rfl) ⟨759480, by rfl⟩ : syracuseStep 2025281 = 1518961) B1518961
theorem B2025299 : Blo 1348993 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B3843949 : Blo 1348993 3843949 := bstep (se 3 (by rfl) ⟨720740, by rfl⟩ : syracuseStep 3843949 = 1441481) B1441481
theorem B2025329 : Blo 1348993 2025329 := bstep (se 2 (by rfl) ⟨759498, by rfl⟩ : syracuseStep 2025329 = 1518997) B1518997
theorem B2025347 : Blo 1348993 2025347 := bstep (se 1 (by rfl) ⟨1519010, by rfl⟩ : syracuseStep 2025347 = 3038021) B3038021
theorem B2279299 : Blo 1348993 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B7686029 : Blo 1348993 7686029 := bstep (se 3 (by rfl) ⟨1441130, by rfl⟩ : syracuseStep 7686029 = 2882261) B2882261
theorem B2025377 : Blo 1348993 2025377 := bstep (se 2 (by rfl) ⟨759516, by rfl⟩ : syracuseStep 2025377 = 1519033) B1519033
theorem B2025395 : Blo 1348993 2025395 := bstep (se 1 (by rfl) ⟨1519046, by rfl⟩ : syracuseStep 2025395 = 3038093) B3038093
theorem B2025425 : Blo 1348993 2025425 := bstep (se 2 (by rfl) ⟨759534, by rfl⟩ : syracuseStep 2025425 = 1519069) B1519069
theorem B2025443 : Blo 1348993 2025443 := bstep (se 1 (by rfl) ⟨1519082, by rfl⟩ : syracuseStep 2025443 = 3038165) B3038165
theorem B10250225 : Blo 1348993 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B2025473 : Blo 1348993 2025473 := bstep (se 2 (by rfl) ⟨759552, by rfl⟩ : syracuseStep 2025473 = 1519105) B1519105
theorem B5122061 : Blo 1348993 5122061 := bstep (se 3 (by rfl) ⟨960386, by rfl⟩ : syracuseStep 5122061 = 1920773) B1920773
theorem B2279441 : Blo 1348993 2279441 := bstep (se 2 (by rfl) ⟨854790, by rfl⟩ : syracuseStep 2279441 = 1709581) B1709581
theorem B2025491 : Blo 1348993 2025491 := bstep (se 1 (by rfl) ⟨1519118, by rfl⟩ : syracuseStep 2025491 = 3038237) B3038237
theorem B2025521 : Blo 1348993 2025521 := bstep (se 2 (by rfl) ⟨759570, by rfl⟩ : syracuseStep 2025521 = 1519141) B1519141
theorem B2738225 : Blo 1348993 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B2025539 : Blo 1348993 2025539 := bstep (se 1 (by rfl) ⟨1519154, by rfl⟩ : syracuseStep 2025539 = 3038309) B3038309
theorem B2025569 : Blo 1348993 2025569 := bstep (se 2 (by rfl) ⟨759588, by rfl⟩ : syracuseStep 2025569 = 1519177) B1519177
theorem B35063921 : Blo 1348993 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B1517683 : Blo 1348993 1517683 := bstep (se 1 (by rfl) ⟨1138262, by rfl⟩ : syracuseStep 1517683 = 2276525) B2276525
theorem B2025587 : Blo 1348993 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B2025617 : Blo 1348993 2025617 := bstep (se 2 (by rfl) ⟨759606, by rfl⟩ : syracuseStep 2025617 = 1519213) B1519213
theorem B2279569 : Blo 1348993 2279569 := bstep (se 2 (by rfl) ⟨854838, by rfl⟩ : syracuseStep 2279569 = 1709677) B1709677
theorem B2025635 : Blo 1348993 2025635 := bstep (se 1 (by rfl) ⟨1519226, by rfl⟩ : syracuseStep 2025635 = 3038453) B3038453
theorem B2279603 : Blo 1348993 2279603 := bstep (se 1 (by rfl) ⟨1709702, by rfl⟩ : syracuseStep 2279603 = 3419405) B3419405
theorem B2025665 : Blo 1348993 2025665 := bstep (se 2 (by rfl) ⟨759624, by rfl⟩ : syracuseStep 2025665 = 1519249) B1519249
theorem B4557005 : Blo 1348993 4557005 := bstep (se 3 (by rfl) ⟨854438, by rfl⟩ : syracuseStep 4557005 = 1708877) B1708877
theorem B3418321 : Blo 1348993 3418321 := bstep (se 2 (by rfl) ⟨1281870, by rfl⟩ : syracuseStep 3418321 = 2563741) B2563741
theorem B2025683 : Blo 1348993 2025683 := bstep (se 1 (by rfl) ⟨1519262, by rfl⟩ : syracuseStep 2025683 = 3038525) B3038525
theorem B5769443 : Blo 1348993 5769443 := bstep (se 1 (by rfl) ⟨4327082, by rfl⟩ : syracuseStep 5769443 = 8654165) B8654165
theorem B2025713 : Blo 1348993 2025713 := bstep (se 2 (by rfl) ⟨759642, by rfl⟩ : syracuseStep 2025713 = 1519285) B1519285
theorem B1517827 : Blo 1348993 1517827 := bstep (se 1 (by rfl) ⟨1138370, by rfl⟩ : syracuseStep 1517827 = 2276741) B2276741
theorem B4557059 : Blo 1348993 4557059 := bstep (se 1 (by rfl) ⟨3417794, by rfl⟩ : syracuseStep 4557059 = 6835589) B6835589
theorem B2025731 : Blo 1348993 2025731 := bstep (se 1 (by rfl) ⟨1519298, by rfl⟩ : syracuseStep 2025731 = 3038597) B3038597
theorem B2025761 : Blo 1348993 2025761 := bstep (se 2 (by rfl) ⟨759660, by rfl⟩ : syracuseStep 2025761 = 1519321) B1519321
theorem B2025779 : Blo 1348993 2025779 := bstep (se 1 (by rfl) ⟨1519334, by rfl⟩ : syracuseStep 2025779 = 3038669) B3038669
theorem B2279731 : Blo 1348993 2279731 := bstep (se 1 (by rfl) ⟨1709798, by rfl⟩ : syracuseStep 2279731 = 3419597) B3419597
theorem B4868429 : Blo 1348993 4868429 := bstep (se 3 (by rfl) ⟨912830, by rfl⟩ : syracuseStep 4868429 = 1825661) B1825661
theorem B9242957 : Blo 1348993 9242957 := bstep (se 3 (by rfl) ⟨1733054, by rfl⟩ : syracuseStep 9242957 = 3466109) B3466109
theorem B2025809 : Blo 1348993 2025809 := bstep (se 2 (by rfl) ⟨759678, by rfl⟩ : syracuseStep 2025809 = 1519357) B1519357
theorem B2025827 : Blo 1348993 2025827 := bstep (se 1 (by rfl) ⟨1519370, by rfl⟩ : syracuseStep 2025827 = 3038741) B3038741
theorem B4327789 : Blo 1348993 4327789 := bstep (se 3 (by rfl) ⟨811460, by rfl⟩ : syracuseStep 4327789 = 1622921) B1622921
theorem B2025857 : Blo 1348993 2025857 := bstep (se 2 (by rfl) ⟨759696, by rfl⟩ : syracuseStep 2025857 = 1519393) B1519393
theorem B1517971 : Blo 1348993 1517971 := bstep (se 1 (by rfl) ⟨1138478, by rfl⟩ : syracuseStep 1517971 = 2276957) B2276957
theorem B2025875 : Blo 1348993 2025875 := bstep (se 1 (by rfl) ⟨1519406, by rfl⟩ : syracuseStep 2025875 = 3038813) B3038813
theorem B2025905 : Blo 1348993 2025905 := bstep (se 2 (by rfl) ⟨759714, by rfl⟩ : syracuseStep 2025905 = 1519429) B1519429
theorem B2025923 : Blo 1348993 2025923 := bstep (se 1 (by rfl) ⟨1519442, by rfl⟩ : syracuseStep 2025923 = 3038885) B3038885
theorem B2025953 : Blo 1348993 2025953 := bstep (se 2 (by rfl) ⟨759732, by rfl⟩ : syracuseStep 2025953 = 1519465) B1519465
theorem B3418595 : Blo 1348993 3418595 := bstep (se 1 (by rfl) ⟨2563946, by rfl⟩ : syracuseStep 3418595 = 5127893) B5127893
theorem B4164077 : Blo 1348993 4164077 := bstep (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) B1561529
theorem B2025971 : Blo 1348993 2025971 := bstep (se 1 (by rfl) ⟨1519478, by rfl⟩ : syracuseStep 2025971 = 3038957) B3038957
theorem B4557329 : Blo 1348993 4557329 := bstep (se 2 (by rfl) ⟨1708998, by rfl⟩ : syracuseStep 4557329 = 3417997) B3417997
theorem B2026001 : Blo 1348993 2026001 := bstep (se 2 (by rfl) ⟨759750, by rfl⟩ : syracuseStep 2026001 = 1519501) B1519501
theorem B1518115 : Blo 1348993 1518115 := bstep (se 1 (by rfl) ⟨1138586, by rfl⟩ : syracuseStep 1518115 = 2277173) B2277173
theorem B2026019 : Blo 1348993 2026019 := bstep (se 1 (by rfl) ⟨1519514, by rfl⟩ : syracuseStep 2026019 = 3039029) B3039029
theorem B2026049 : Blo 1348993 2026049 := bstep (se 2 (by rfl) ⟨759768, by rfl⟩ : syracuseStep 2026049 = 1519537) B1519537
theorem B5474893 : Blo 1348993 5474893 := bstep (se 3 (by rfl) ⟨1026542, by rfl⟩ : syracuseStep 5474893 = 2053085) B2053085
theorem B2026067 : Blo 1348993 2026067 := bstep (se 1 (by rfl) ⟨1519550, by rfl⟩ : syracuseStep 2026067 = 3039101) B3039101
theorem B2026097 : Blo 1348993 2026097 := bstep (se 2 (by rfl) ⟨759786, by rfl⟩ : syracuseStep 2026097 = 1519573) B1519573
theorem B2026115 : Blo 1348993 2026115 := bstep (se 1 (by rfl) ⟨1519586, by rfl⟩ : syracuseStep 2026115 = 3039173) B3039173
theorem B2026145 : Blo 1348993 2026145 := bstep (se 2 (by rfl) ⟨759804, by rfl⟩ : syracuseStep 2026145 = 1519609) B1519609
theorem B3418787 : Blo 1348993 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B1518259 : Blo 1348993 1518259 := bstep (se 1 (by rfl) ⟨1138694, by rfl⟩ : syracuseStep 1518259 = 2277389) B2277389
theorem B2026163 : Blo 1348993 2026163 := bstep (se 1 (by rfl) ⟨1519622, by rfl⟩ : syracuseStep 2026163 = 3039245) B3039245
theorem B2026193 : Blo 1348993 2026193 := bstep (se 2 (by rfl) ⟨759822, by rfl⟩ : syracuseStep 2026193 = 1519645) B1519645
theorem B2026211 : Blo 1348993 2026211 := bstep (se 1 (by rfl) ⟨1519658, by rfl⟩ : syracuseStep 2026211 = 3039317) B3039317
theorem B2026241 : Blo 1348993 2026241 := bstep (se 2 (by rfl) ⟨759840, by rfl⟩ : syracuseStep 2026241 = 1519681) B1519681
theorem B2026259 : Blo 1348993 2026259 := bstep (se 1 (by rfl) ⟨1519694, by rfl⟩ : syracuseStep 2026259 = 3039389) B3039389
theorem B5122865 : Blo 1348993 5122865 := bstep (se 2 (by rfl) ⟨1921074, by rfl⟩ : syracuseStep 5122865 = 3842149) B3842149
theorem B2026289 : Blo 1348993 2026289 := bstep (se 2 (by rfl) ⟨759858, by rfl⟩ : syracuseStep 2026289 = 1519717) B1519717
theorem B1518403 : Blo 1348993 1518403 := bstep (se 1 (by rfl) ⟨1138802, by rfl⟩ : syracuseStep 1518403 = 2277605) B2277605
theorem B2026307 : Blo 1348993 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B8645453 : Blo 1348993 8645453 := bstep (se 3 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 8645453 = 3242045) B3242045
theorem B2026337 : Blo 1348993 2026337 := bstep (se 2 (by rfl) ⟨759876, by rfl⟩ : syracuseStep 2026337 = 1519753) B1519753
theorem B2026355 : Blo 1348993 2026355 := bstep (se 1 (by rfl) ⟨1519766, by rfl⟩ : syracuseStep 2026355 = 3039533) B3039533
theorem B3845009 : Blo 1348993 3845009 := bstep (se 2 (by rfl) ⟨1441878, by rfl⟩ : syracuseStep 3845009 = 2883757) B2883757
theorem B2026385 : Blo 1348993 2026385 := bstep (se 2 (by rfl) ⟨759894, by rfl⟩ : syracuseStep 2026385 = 1519789) B1519789
theorem B2026403 : Blo 1348993 2026403 := bstep (se 1 (by rfl) ⟨1519802, by rfl⟩ : syracuseStep 2026403 = 3039605) B3039605
theorem B2026433 : Blo 1348993 2026433 := bstep (se 2 (by rfl) ⟨759912, by rfl⟩ : syracuseStep 2026433 = 1519825) B1519825
theorem B1518547 : Blo 1348993 1518547 := bstep (se 1 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 1518547 = 2277821) B2277821
theorem B2026451 : Blo 1348993 2026451 := bstep (se 1 (by rfl) ⟨1519838, by rfl⟩ : syracuseStep 2026451 = 3039677) B3039677
theorem B2026481 : Blo 1348993 2026481 := bstep (se 2 (by rfl) ⟨759930, by rfl⟩ : syracuseStep 2026481 = 1519861) B1519861
theorem B11693069 : Blo 1348993 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B4557869 : Blo 1348993 4557869 := bstep (se 3 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 4557869 = 1709201) B1709201
theorem B1518691 : Blo 1348993 1518691 := bstep (se 1 (by rfl) ⟨1139018, by rfl⟩ : syracuseStep 1518691 = 2278037) B2278037
theorem B4557923 : Blo 1348993 4557923 := bstep (se 1 (by rfl) ⟨3418442, by rfl⟩ : syracuseStep 4557923 = 6836885) B6836885
theorem B19467377 : Blo 1348993 19467377 := bstep (se 2 (by rfl) ⟨7300266, by rfl⟩ : syracuseStep 19467377 = 14600533) B14600533
theorem B2051219 : Blo 1348993 2051219 := bstep (se 1 (by rfl) ⟨1538414, by rfl⟩ : syracuseStep 2051219 = 3076829) B3076829
theorem B6835427 : Blo 1348993 6835427 := bstep (se 1 (by rfl) ⟨5126570, by rfl⟩ : syracuseStep 6835427 = 10253141) B10253141
theorem B8326385 : Blo 1348993 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B1518835 : Blo 1348993 1518835 := bstep (se 1 (by rfl) ⟨1139126, by rfl⟩ : syracuseStep 1518835 = 2278253) B2278253
theorem B4558193 : Blo 1348993 4558193 := bstep (se 2 (by rfl) ⟨1709322, by rfl⟩ : syracuseStep 4558193 = 3418645) B3418645
theorem B1518979 : Blo 1348993 1518979 := bstep (se 1 (by rfl) ⟨1139234, by rfl⟩ : syracuseStep 1518979 = 2278469) B2278469
theorem B8326577 : Blo 1348993 8326577 := bstep (se 2 (by rfl) ⟨3122466, by rfl⟩ : syracuseStep 8326577 = 6244933) B6244933
theorem B5770673 : Blo 1348993 5770673 := bstep (se 2 (by rfl) ⟨2164002, by rfl⟩ : syracuseStep 5770673 = 4328005) B4328005
theorem B5123533 : Blo 1348993 5123533 := bstep (se 3 (by rfl) ⟨960662, by rfl⟩ : syracuseStep 5123533 = 1921325) B1921325
theorem B1707475 : Blo 1348993 1707475 := bstep (se 1 (by rfl) ⟨1280606, by rfl⟩ : syracuseStep 1707475 = 2561213) B2561213
theorem B1519123 : Blo 1348993 1519123 := bstep (se 1 (by rfl) ⟨1139342, by rfl⟩ : syracuseStep 1519123 = 2278685) B2278685
theorem B5762609 : Blo 1348993 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B3845681 : Blo 1348993 3845681 := bstep (se 2 (by rfl) ⟨1442130, by rfl⟩ : syracuseStep 3845681 = 2884261) B2884261
theorem B1707571 : Blo 1348993 1707571 := bstep (se 1 (by rfl) ⟨1280678, by rfl⟩ : syracuseStep 1707571 = 2561357) B2561357
theorem B1519267 : Blo 1348993 1519267 := bstep (se 1 (by rfl) ⟨1139450, by rfl⟩ : syracuseStep 1519267 = 2278901) B2278901
theorem B8654627 : Blo 1348993 8654627 := bstep (se 1 (by rfl) ⟨6490970, by rfl⟩ : syracuseStep 8654627 = 12981941) B12981941
theorem B1519411 : Blo 1348993 1519411 := bstep (se 1 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 1519411 = 2279117) B2279117
theorem B1920881 : Blo 1348993 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B4558733 : Blo 1348993 4558733 := bstep (se 3 (by rfl) ⟨854762, by rfl⟩ : syracuseStep 4558733 = 1709525) B1709525
theorem B1519555 : Blo 1348993 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B4558787 : Blo 1348993 4558787 := bstep (se 1 (by rfl) ⟨3419090, by rfl⟩ : syracuseStep 4558787 = 6838181) B6838181
theorem B6836237 : Blo 1348993 6836237 := bstep (se 3 (by rfl) ⟨1281794, by rfl⟩ : syracuseStep 6836237 = 2563589) B2563589
theorem B1708067 : Blo 1348993 1708067 := bstep (se 1 (by rfl) ⟨1281050, by rfl⟩ : syracuseStep 1708067 = 2562101) B2562101
theorem B6156337 : Blo 1348993 6156337 := bstep (se 2 (by rfl) ⟨2308626, by rfl⟩ : syracuseStep 6156337 = 4617253) B4617253
theorem B1519699 : Blo 1348993 1519699 := bstep (se 1 (by rfl) ⟨1139774, by rfl⟩ : syracuseStep 1519699 = 2279549) B2279549
theorem B3035249 : Blo 1348993 3035249 := bstep (se 2 (by rfl) ⟨1138218, by rfl⟩ : syracuseStep 3035249 = 2276437) B2276437
theorem B3035267 : Blo 1348993 3035267 := bstep (se 1 (by rfl) ⟨2276450, by rfl⟩ : syracuseStep 3035267 = 4552901) B4552901
theorem B4559057 : Blo 1348993 4559057 := bstep (se 2 (by rfl) ⟨1709646, by rfl⟩ : syracuseStep 4559057 = 3419293) B3419293
theorem B5124323 : Blo 1348993 5124323 := bstep (se 1 (by rfl) ⟨3843242, by rfl⟩ : syracuseStep 5124323 = 7686485) B7686485
theorem B27709667 : Blo 1348993 27709667 := bstep (se 1 (by rfl) ⟨20782250, by rfl⟩ : syracuseStep 27709667 = 41564501) B41564501
theorem B1519843 : Blo 1348993 1519843 := bstep (se 1 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 1519843 = 2279765) B2279765
theorem B3846467 : Blo 1348993 3846467 := bstep (se 1 (by rfl) ⟨2884850, by rfl⟩ : syracuseStep 3846467 = 5769701) B5769701
theorem B1732963 : Blo 1348993 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B1921411 : Blo 1348993 1921411 := bstep (se 1 (by rfl) ⟨1441058, by rfl⟩ : syracuseStep 1921411 = 2882117) B2882117
theorem B3035537 : Blo 1348993 3035537 := bstep (se 2 (by rfl) ⟨1138326, by rfl⟩ : syracuseStep 3035537 = 2276653) B2276653
theorem B3035555 : Blo 1348993 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B2920963 : Blo 1348993 2920963 := bstep (se 1 (by rfl) ⟨2190722, by rfl⟩ : syracuseStep 2920963 = 4381445) B4381445
theorem B3846797 : Blo 1348993 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B3035825 : Blo 1348993 3035825 := bstep (se 2 (by rfl) ⟨1138434, by rfl⟩ : syracuseStep 3035825 = 2276869) B2276869
theorem B14594741 : Blo 1348993 14594741 := bstep (se 5 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 14594741 = 1368257) B1368257
theorem B3035843 : Blo 1348993 3035843 := bstep (se 1 (by rfl) ⟨2276882, by rfl⟩ : syracuseStep 3035843 = 4553765) B4553765
theorem B3846865 : Blo 1348993 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1921747 : Blo 1348993 1921747 := bstep (se 1 (by rfl) ⟨1441310, by rfl⟩ : syracuseStep 1921747 = 2882621) B2882621
theorem B1708771 : Blo 1348993 1708771 := bstep (se 1 (by rfl) ⟨1281578, by rfl⟩ : syracuseStep 1708771 = 2563157) B2563157
theorem B3650285 : Blo 1348993 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B4559597 : Blo 1348993 4559597 := bstep (se 3 (by rfl) ⟨854924, by rfl⟩ : syracuseStep 4559597 = 1709849) B1709849
theorem B7688945 : Blo 1348993 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1708867 : Blo 1348993 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B1823585 : Blo 1348993 1823585 := bstep (se 2 (by rfl) ⟨683844, by rfl⟩ : syracuseStep 1823585 = 1367689) B1367689
theorem B5124977 : Blo 1348993 5124977 := bstep (se 2 (by rfl) ⟨1921866, by rfl⟩ : syracuseStep 5124977 = 3843733) B3843733
theorem B1823683 : Blo 1348993 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B4617155 : Blo 1348993 4617155 := bstep (se 1 (by rfl) ⟨3462866, by rfl⟩ : syracuseStep 4617155 = 6925733) B6925733
theorem B3036113 : Blo 1348993 3036113 := bstep (se 2 (by rfl) ⟨1138542, by rfl⟩ : syracuseStep 3036113 = 2277085) B2277085
theorem B3036131 : Blo 1348993 3036131 := bstep (se 1 (by rfl) ⟨2277098, by rfl⟩ : syracuseStep 3036131 = 4554197) B4554197
theorem B28079075 : Blo 1348993 28079075 := bstep (se 1 (by rfl) ⟨21059306, by rfl⟩ : syracuseStep 28079075 = 42118613) B42118613
theorem B3847139 : Blo 1348993 3847139 := bstep (se 1 (by rfl) ⟨2885354, by rfl⟩ : syracuseStep 3847139 = 5770709) B5770709
theorem B5477489 : Blo 1348993 5477489 := bstep (se 2 (by rfl) ⟨2054058, by rfl⟩ : syracuseStep 5477489 = 4108117) B4108117
theorem B7296227 : Blo 1348993 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B3036401 : Blo 1348993 3036401 := bstep (se 2 (by rfl) ⟨1138650, by rfl⟩ : syracuseStep 3036401 = 2277301) B2277301
theorem B1922305 : Blo 1348993 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B3036419 : Blo 1348993 3036419 := bstep (se 1 (by rfl) ⟨2277314, by rfl⟩ : syracuseStep 3036419 = 4554629) B4554629
theorem B6239501 : Blo 1348993 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B1922339 : Blo 1348993 1922339 := bstep (se 1 (by rfl) ⟨1441754, by rfl⟩ : syracuseStep 1922339 = 2883509) B2883509
theorem B1709363 : Blo 1348993 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B1348995 : Blo 1348993 1348995 := bstep (se 1 (by rfl) ⟨1011746, by rfl⟩ : syracuseStep 1348995 = 2023493) B2023493
theorem B1349011 : Blo 1348993 1349011 := bstep (se 1 (by rfl) ⟨1011758, by rfl⟩ : syracuseStep 1349011 = 2023517) B2023517
theorem B1349027 : Blo 1348993 1349027 := bstep (se 1 (by rfl) ⟨1011770, by rfl⟩ : syracuseStep 1349027 = 2023541) B2023541
theorem B1349043 : Blo 1348993 1349043 := bstep (se 1 (by rfl) ⟨1011782, by rfl⟩ : syracuseStep 1349043 = 2023565) B2023565
theorem B1349059 : Blo 1348993 1349059 := bstep (se 1 (by rfl) ⟨1011794, by rfl⟩ : syracuseStep 1349059 = 2023589) B2023589
theorem B1349075 : Blo 1348993 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B1349091 : Blo 1348993 1349091 := bstep (se 1 (by rfl) ⟨1011818, by rfl⟩ : syracuseStep 1349091 = 2023637) B2023637
theorem B1349107 : Blo 1348993 1349107 := bstep (se 1 (by rfl) ⟨1011830, by rfl⟩ : syracuseStep 1349107 = 2023661) B2023661
theorem B2340353 : Blo 1348993 2340353 := bstep (se 2 (by rfl) ⟨877632, by rfl⟩ : syracuseStep 2340353 = 1755265) B1755265
theorem B1349123 : Blo 1348993 1349123 := bstep (se 1 (by rfl) ⟨1011842, by rfl⟩ : syracuseStep 1349123 = 2023685) B2023685
theorem B2561539 : Blo 1348993 2561539 := bstep (se 1 (by rfl) ⟨1921154, by rfl⟩ : syracuseStep 2561539 = 3842309) B3842309
theorem B3036689 : Blo 1348993 3036689 := bstep (se 2 (by rfl) ⟨1138758, by rfl⟩ : syracuseStep 3036689 = 2277517) B2277517
theorem B1349139 : Blo 1348993 1349139 := bstep (se 1 (by rfl) ⟨1011854, by rfl⟩ : syracuseStep 1349139 = 2023709) B2023709
theorem B1349155 : Blo 1348993 1349155 := bstep (se 1 (by rfl) ⟨1011866, by rfl⟩ : syracuseStep 1349155 = 2023733) B2023733
theorem B3036707 : Blo 1348993 3036707 := bstep (se 1 (by rfl) ⟨2277530, by rfl⟩ : syracuseStep 3036707 = 4555061) B4555061
theorem B1349171 : Blo 1348993 1349171 := bstep (se 1 (by rfl) ⟨1011878, by rfl⟩ : syracuseStep 1349171 = 2023757) B2023757
theorem B1349187 : Blo 1348993 1349187 := bstep (se 1 (by rfl) ⟨1011890, by rfl⟩ : syracuseStep 1349187 = 2023781) B2023781
theorem B1349203 : Blo 1348993 1349203 := bstep (se 1 (by rfl) ⟨1011902, by rfl⟩ : syracuseStep 1349203 = 2023805) B2023805
theorem B1349219 : Blo 1348993 1349219 := bstep (se 1 (by rfl) ⟨1011914, by rfl⟩ : syracuseStep 1349219 = 2023829) B2023829
theorem B1349235 : Blo 1348993 1349235 := bstep (se 1 (by rfl) ⟨1011926, by rfl⟩ : syracuseStep 1349235 = 2023853) B2023853
theorem B1349251 : Blo 1348993 1349251 := bstep (se 1 (by rfl) ⟨1011938, by rfl⟩ : syracuseStep 1349251 = 2023877) B2023877
theorem B1349267 : Blo 1348993 1349267 := bstep (se 1 (by rfl) ⟨1011950, by rfl⟩ : syracuseStep 1349267 = 2023901) B2023901
theorem B1349283 : Blo 1348993 1349283 := bstep (se 1 (by rfl) ⟨1011962, by rfl⟩ : syracuseStep 1349283 = 2023925) B2023925
theorem B2561699 : Blo 1348993 2561699 := bstep (se 1 (by rfl) ⟨1921274, by rfl⟩ : syracuseStep 2561699 = 3842549) B3842549
theorem B1349299 : Blo 1348993 1349299 := bstep (se 1 (by rfl) ⟨1011974, by rfl⟩ : syracuseStep 1349299 = 2023949) B2023949
theorem B1349315 : Blo 1348993 1349315 := bstep (se 1 (by rfl) ⟨1011986, by rfl⟩ : syracuseStep 1349315 = 2023973) B2023973
theorem B1349331 : Blo 1348993 1349331 := bstep (se 1 (by rfl) ⟨1011998, by rfl⟩ : syracuseStep 1349331 = 2023997) B2023997
theorem B1349347 : Blo 1348993 1349347 := bstep (se 1 (by rfl) ⟨1012010, by rfl⟩ : syracuseStep 1349347 = 2024021) B2024021
theorem B3651313 : Blo 1348993 3651313 := bstep (se 2 (by rfl) ⟨1369242, by rfl⟩ : syracuseStep 3651313 = 2738485) B2738485
theorem B1349363 : Blo 1348993 1349363 := bstep (se 1 (by rfl) ⟨1012022, by rfl⟩ : syracuseStep 1349363 = 2024045) B2024045
theorem B1349379 : Blo 1348993 1349379 := bstep (se 1 (by rfl) ⟨1012034, by rfl⟩ : syracuseStep 1349379 = 2024069) B2024069
theorem B1349395 : Blo 1348993 1349395 := bstep (se 1 (by rfl) ⟨1012046, by rfl⟩ : syracuseStep 1349395 = 2024093) B2024093
theorem B1349411 : Blo 1348993 1349411 := bstep (se 1 (by rfl) ⟨1012058, by rfl⟩ : syracuseStep 1349411 = 2024117) B2024117
theorem B4618019 : Blo 1348993 4618019 := bstep (se 1 (by rfl) ⟨3463514, by rfl⟩ : syracuseStep 4618019 = 6927029) B6927029
theorem B3036977 : Blo 1348993 3036977 := bstep (se 2 (by rfl) ⟨1138866, by rfl⟩ : syracuseStep 3036977 = 2277733) B2277733
theorem B1349427 : Blo 1348993 1349427 := bstep (se 1 (by rfl) ⟨1012070, by rfl⟩ : syracuseStep 1349427 = 2024141) B2024141
theorem B3241795 : Blo 1348993 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B1349443 : Blo 1348993 1349443 := bstep (se 1 (by rfl) ⟨1012082, by rfl⟩ : syracuseStep 1349443 = 2024165) B2024165
theorem B3036995 : Blo 1348993 3036995 := bstep (se 1 (by rfl) ⟨2277746, by rfl⟩ : syracuseStep 3036995 = 4555493) B4555493
theorem B1922897 : Blo 1348993 1922897 := bstep (se 2 (by rfl) ⟨721086, by rfl⟩ : syracuseStep 1922897 = 1442173) B1442173
theorem B3651409 : Blo 1348993 3651409 := bstep (se 2 (by rfl) ⟨1369278, by rfl⟩ : syracuseStep 3651409 = 2738557) B2738557
theorem B1349459 : Blo 1348993 1349459 := bstep (se 1 (by rfl) ⟨1012094, by rfl⟩ : syracuseStep 1349459 = 2024189) B2024189
theorem B1349475 : Blo 1348993 1349475 := bstep (se 1 (by rfl) ⟨1012106, by rfl⟩ : syracuseStep 1349475 = 2024213) B2024213
theorem B1349491 : Blo 1348993 1349491 := bstep (se 1 (by rfl) ⟨1012118, by rfl⟩ : syracuseStep 1349491 = 2024237) B2024237
theorem B1349507 : Blo 1348993 1349507 := bstep (se 1 (by rfl) ⟨1012130, by rfl⟩ : syracuseStep 1349507 = 2024261) B2024261
theorem B7796621 : Blo 1348993 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B1349523 : Blo 1348993 1349523 := bstep (se 1 (by rfl) ⟨1012142, by rfl⟩ : syracuseStep 1349523 = 2024285) B2024285
theorem B1922977 : Blo 1348993 1922977 := bstep (se 2 (by rfl) ⟨721116, by rfl⟩ : syracuseStep 1922977 = 1442233) B1442233
theorem B1349539 : Blo 1348993 1349539 := bstep (se 1 (by rfl) ⟨1012154, by rfl⟩ : syracuseStep 1349539 = 2024309) B2024309
theorem B1349555 : Blo 1348993 1349555 := bstep (se 1 (by rfl) ⟨1012166, by rfl⟩ : syracuseStep 1349555 = 2024333) B2024333
theorem B1349571 : Blo 1348993 1349571 := bstep (se 1 (by rfl) ⟨1012178, by rfl⟩ : syracuseStep 1349571 = 2024357) B2024357
theorem B5765069 : Blo 1348993 5765069 := bstep (se 3 (by rfl) ⟨1080950, by rfl⟩ : syracuseStep 5765069 = 2161901) B2161901
theorem B1349587 : Blo 1348993 1349587 := bstep (se 1 (by rfl) ⟨1012190, by rfl⟩ : syracuseStep 1349587 = 2024381) B2024381
theorem B1349603 : Blo 1348993 1349603 := bstep (se 1 (by rfl) ⟨1012202, by rfl⟩ : syracuseStep 1349603 = 2024405) B2024405
theorem B1349619 : Blo 1348993 1349619 := bstep (se 1 (by rfl) ⟨1012214, by rfl⟩ : syracuseStep 1349619 = 2024429) B2024429
theorem B1349635 : Blo 1348993 1349635 := bstep (se 1 (by rfl) ⟨1012226, by rfl⟩ : syracuseStep 1349635 = 2024453) B2024453
theorem B1349651 : Blo 1348993 1349651 := bstep (se 1 (by rfl) ⟨1012238, by rfl⟩ : syracuseStep 1349651 = 2024477) B2024477
theorem B1349667 : Blo 1348993 1349667 := bstep (se 1 (by rfl) ⟨1012250, by rfl⟩ : syracuseStep 1349667 = 2024501) B2024501
theorem B4864049 : Blo 1348993 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B1349683 : Blo 1348993 1349683 := bstep (se 1 (by rfl) ⟨1012262, by rfl⟩ : syracuseStep 1349683 = 2024525) B2024525
theorem B1349699 : Blo 1348993 1349699 := bstep (se 1 (by rfl) ⟨1012274, by rfl⟩ : syracuseStep 1349699 = 2024549) B2024549
theorem B3037265 : Blo 1348993 3037265 := bstep (se 2 (by rfl) ⟨1138974, by rfl⟩ : syracuseStep 3037265 = 2277949) B2277949
theorem B1349715 : Blo 1348993 1349715 := bstep (se 1 (by rfl) ⟨1012286, by rfl⟩ : syracuseStep 1349715 = 2024573) B2024573
theorem B1349731 : Blo 1348993 1349731 := bstep (se 1 (by rfl) ⟨1012298, by rfl⟩ : syracuseStep 1349731 = 2024597) B2024597
theorem B3037283 : Blo 1348993 3037283 := bstep (se 1 (by rfl) ⟨2277962, by rfl⟩ : syracuseStep 3037283 = 4555925) B4555925
theorem B1349747 : Blo 1348993 1349747 := bstep (se 1 (by rfl) ⟨1012310, by rfl⟩ : syracuseStep 1349747 = 2024621) B2024621
theorem B1349763 : Blo 1348993 1349763 := bstep (se 1 (by rfl) ⟨1012322, by rfl⟩ : syracuseStep 1349763 = 2024645) B2024645
theorem B1349779 : Blo 1348993 1349779 := bstep (se 1 (by rfl) ⟨1012334, by rfl⟩ : syracuseStep 1349779 = 2024669) B2024669
theorem B6830243 : Blo 1348993 6830243 := bstep (se 1 (by rfl) ⟨5122682, by rfl⟩ : syracuseStep 6830243 = 10245365) B10245365
theorem B1349795 : Blo 1348993 1349795 := bstep (se 1 (by rfl) ⟨1012346, by rfl⟩ : syracuseStep 1349795 = 2024693) B2024693
theorem B7690403 : Blo 1348993 7690403 := bstep (se 1 (by rfl) ⟨5767802, by rfl⟩ : syracuseStep 7690403 = 11535605) B11535605
theorem B1349811 : Blo 1348993 1349811 := bstep (se 1 (by rfl) ⟨1012358, by rfl⟩ : syracuseStep 1349811 = 2024717) B2024717
theorem B1349827 : Blo 1348993 1349827 := bstep (se 1 (by rfl) ⟨1012370, by rfl⟩ : syracuseStep 1349827 = 2024741) B2024741
theorem B1349843 : Blo 1348993 1349843 := bstep (se 1 (by rfl) ⟨1012382, by rfl⟩ : syracuseStep 1349843 = 2024765) B2024765
theorem B1349859 : Blo 1348993 1349859 := bstep (se 1 (by rfl) ⟨1012394, by rfl⟩ : syracuseStep 1349859 = 2024789) B2024789
theorem B4102385 : Blo 1348993 4102385 := bstep (se 2 (by rfl) ⟨1538394, by rfl⟩ : syracuseStep 4102385 = 3076789) B3076789
theorem B2431217 : Blo 1348993 2431217 := bstep (se 2 (by rfl) ⟨911706, by rfl⟩ : syracuseStep 2431217 = 1823413) B1823413
theorem B1349875 : Blo 1348993 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B4004081 : Blo 1348993 4004081 := bstep (se 2 (by rfl) ⟨1501530, by rfl⟩ : syracuseStep 4004081 = 3003061) B3003061
theorem B1349891 : Blo 1348993 1349891 := bstep (se 1 (by rfl) ⟨1012418, by rfl⟩ : syracuseStep 1349891 = 2024837) B2024837
theorem B1349907 : Blo 1348993 1349907 := bstep (se 1 (by rfl) ⟨1012430, by rfl⟩ : syracuseStep 1349907 = 2024861) B2024861
theorem B5765411 : Blo 1348993 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B1349923 : Blo 1348993 1349923 := bstep (se 1 (by rfl) ⟨1012442, by rfl⟩ : syracuseStep 1349923 = 2024885) B2024885
theorem B5126435 : Blo 1348993 5126435 := bstep (se 1 (by rfl) ⟨3844826, by rfl⟩ : syracuseStep 5126435 = 7689653) B7689653
theorem B4553009 : Blo 1348993 4553009 := bstep (se 2 (by rfl) ⟨1707378, by rfl⟩ : syracuseStep 4553009 = 3414757) B3414757
theorem B5126449 : Blo 1348993 5126449 := bstep (se 2 (by rfl) ⟨1922418, by rfl⟩ : syracuseStep 5126449 = 3844837) B3844837
theorem B1349939 : Blo 1348993 1349939 := bstep (se 1 (by rfl) ⟨1012454, by rfl⟩ : syracuseStep 1349939 = 2024909) B2024909
theorem B1349955 : Blo 1348993 1349955 := bstep (se 1 (by rfl) ⟨1012466, by rfl⟩ : syracuseStep 1349955 = 2024933) B2024933
theorem B1349971 : Blo 1348993 1349971 := bstep (se 1 (by rfl) ⟨1012478, by rfl⟩ : syracuseStep 1349971 = 2024957) B2024957
theorem B1349987 : Blo 1348993 1349987 := bstep (se 1 (by rfl) ⟨1012490, by rfl⟩ : syracuseStep 1349987 = 2024981) B2024981
theorem B3037553 : Blo 1348993 3037553 := bstep (se 2 (by rfl) ⟨1139082, by rfl⟩ : syracuseStep 3037553 = 2278165) B2278165
theorem B1350003 : Blo 1348993 1350003 := bstep (se 1 (by rfl) ⟨1012502, by rfl⟩ : syracuseStep 1350003 = 2025005) B2025005
theorem B1350019 : Blo 1348993 1350019 := bstep (se 1 (by rfl) ⟨1012514, by rfl⟩ : syracuseStep 1350019 = 2025029) B2025029
theorem B3037571 : Blo 1348993 3037571 := bstep (se 1 (by rfl) ⟨2278178, by rfl⟩ : syracuseStep 3037571 = 4556357) B4556357
theorem B1350035 : Blo 1348993 1350035 := bstep (se 1 (by rfl) ⟨1012526, by rfl⟩ : syracuseStep 1350035 = 2025053) B2025053
theorem B1350051 : Blo 1348993 1350051 := bstep (se 1 (by rfl) ⟨1012538, by rfl⟩ : syracuseStep 1350051 = 2025077) B2025077
theorem B2161075 : Blo 1348993 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B1350067 : Blo 1348993 1350067 := bstep (se 1 (by rfl) ⟨1012550, by rfl⟩ : syracuseStep 1350067 = 2025101) B2025101
theorem B1350083 : Blo 1348993 1350083 := bstep (se 1 (by rfl) ⟨1012562, by rfl⟩ : syracuseStep 1350083 = 2025125) B2025125
theorem B1350099 : Blo 1348993 1350099 := bstep (se 1 (by rfl) ⟨1012574, by rfl⟩ : syracuseStep 1350099 = 2025149) B2025149
theorem B3242467 : Blo 1348993 3242467 := bstep (se 1 (by rfl) ⟨2431850, by rfl⟩ : syracuseStep 3242467 = 4863701) B4863701
theorem B1350115 : Blo 1348993 1350115 := bstep (se 1 (by rfl) ⟨1012586, by rfl⟩ : syracuseStep 1350115 = 2025173) B2025173
theorem B1350131 : Blo 1348993 1350131 := bstep (se 1 (by rfl) ⟨1012598, by rfl⟩ : syracuseStep 1350131 = 2025197) B2025197
theorem B1350147 : Blo 1348993 1350147 := bstep (se 1 (by rfl) ⟨1012610, by rfl⟩ : syracuseStep 1350147 = 2025221) B2025221
theorem B7297541 : Blo 1348993 7297541 := bstep (se 4 (by rfl) ⟨684144, by rfl⟩ : syracuseStep 7297541 = 1368289) B1368289
theorem B2431505 : Blo 1348993 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B1350163 : Blo 1348993 1350163 := bstep (se 1 (by rfl) ⟨1012622, by rfl⟩ : syracuseStep 1350163 = 2025245) B2025245
theorem B1350179 : Blo 1348993 1350179 := bstep (se 1 (by rfl) ⟨1012634, by rfl⟩ : syracuseStep 1350179 = 2025269) B2025269
theorem B1350195 : Blo 1348993 1350195 := bstep (se 1 (by rfl) ⟨1012646, by rfl⟩ : syracuseStep 1350195 = 2025293) B2025293
theorem B1350211 : Blo 1348993 1350211 := bstep (se 1 (by rfl) ⟨1012658, by rfl⟩ : syracuseStep 1350211 = 2025317) B2025317
theorem B1350227 : Blo 1348993 1350227 := bstep (se 1 (by rfl) ⟨1012670, by rfl⟩ : syracuseStep 1350227 = 2025341) B2025341
theorem B1350243 : Blo 1348993 1350243 := bstep (se 1 (by rfl) ⟨1012682, by rfl⟩ : syracuseStep 1350243 = 2025365) B2025365
theorem B1350259 : Blo 1348993 1350259 := bstep (se 1 (by rfl) ⟨1012694, by rfl⟩ : syracuseStep 1350259 = 2025389) B2025389
theorem B1350275 : Blo 1348993 1350275 := bstep (se 1 (by rfl) ⟨1012706, by rfl⟩ : syracuseStep 1350275 = 2025413) B2025413
theorem B11532941 : Blo 1348993 11532941 := bstep (se 3 (by rfl) ⟨2162426, by rfl⟩ : syracuseStep 11532941 = 4324853) B4324853
theorem B14604941 : Blo 1348993 14604941 := bstep (se 3 (by rfl) ⟨2738426, by rfl⟩ : syracuseStep 14604941 = 5476853) B5476853
theorem B3037841 : Blo 1348993 3037841 := bstep (se 2 (by rfl) ⟨1139190, by rfl⟩ : syracuseStep 3037841 = 2278381) B2278381
theorem B1350291 : Blo 1348993 1350291 := bstep (se 1 (by rfl) ⟨1012718, by rfl⟩ : syracuseStep 1350291 = 2025437) B2025437
theorem B2284193 : Blo 1348993 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B3037859 : Blo 1348993 3037859 := bstep (se 1 (by rfl) ⟨2278394, by rfl⟩ : syracuseStep 3037859 = 4556789) B4556789
theorem B1350307 : Blo 1348993 1350307 := bstep (se 1 (by rfl) ⟨1012730, by rfl⟩ : syracuseStep 1350307 = 2025461) B2025461
theorem B1350323 : Blo 1348993 1350323 := bstep (se 1 (by rfl) ⟨1012742, by rfl⟩ : syracuseStep 1350323 = 2025485) B2025485
theorem B1350339 : Blo 1348993 1350339 := bstep (se 1 (by rfl) ⟨1012754, by rfl⟩ : syracuseStep 1350339 = 2025509) B2025509
theorem B3414737 : Blo 1348993 3414737 := bstep (se 2 (by rfl) ⟨1280526, by rfl⟩ : syracuseStep 3414737 = 2561053) B2561053
theorem B2562769 : Blo 1348993 2562769 := bstep (se 2 (by rfl) ⟨961038, by rfl⟩ : syracuseStep 2562769 = 1922077) B1922077
theorem B1350355 : Blo 1348993 1350355 := bstep (se 1 (by rfl) ⟨1012766, by rfl⟩ : syracuseStep 1350355 = 2025533) B2025533
theorem B23050979 : Blo 1348993 23050979 := bstep (se 1 (by rfl) ⟨17288234, by rfl⟩ : syracuseStep 23050979 = 34576469) B34576469
theorem B1350371 : Blo 1348993 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B12966641 : Blo 1348993 12966641 := bstep (se 2 (by rfl) ⟨4862490, by rfl⟩ : syracuseStep 12966641 = 9724981) B9724981
theorem B1350387 : Blo 1348993 1350387 := bstep (se 1 (by rfl) ⟨1012790, by rfl⟩ : syracuseStep 1350387 = 2025581) B2025581
theorem B1350403 : Blo 1348993 1350403 := bstep (se 1 (by rfl) ⟨1012802, by rfl⟩ : syracuseStep 1350403 = 2025605) B2025605
theorem B4324109 : Blo 1348993 4324109 := bstep (se 3 (by rfl) ⟨810770, by rfl⟩ : syracuseStep 4324109 = 1621541) B1621541
theorem B1350419 : Blo 1348993 1350419 := bstep (se 1 (by rfl) ⟨1012814, by rfl⟩ : syracuseStep 1350419 = 2025629) B2025629
theorem B1350435 : Blo 1348993 1350435 := bstep (se 1 (by rfl) ⟨1012826, by rfl⟩ : syracuseStep 1350435 = 2025653) B2025653
theorem B1350451 : Blo 1348993 1350451 := bstep (se 1 (by rfl) ⟨1012838, by rfl⟩ : syracuseStep 1350451 = 2025677) B2025677
theorem B1350467 : Blo 1348993 1350467 := bstep (se 1 (by rfl) ⟨1012850, by rfl⟩ : syracuseStep 1350467 = 2025701) B2025701
theorem B4553549 : Blo 1348993 4553549 := bstep (se 3 (by rfl) ⟨853790, by rfl⟩ : syracuseStep 4553549 = 1707581) B1707581
theorem B1350483 : Blo 1348993 1350483 := bstep (se 1 (by rfl) ⟨1012862, by rfl⟩ : syracuseStep 1350483 = 2025725) B2025725
theorem B1350499 : Blo 1348993 1350499 := bstep (se 1 (by rfl) ⟨1012874, by rfl⟩ : syracuseStep 1350499 = 2025749) B2025749
theorem B6839153 : Blo 1348993 6839153 := bstep (se 2 (by rfl) ⟨2564682, by rfl⟩ : syracuseStep 6839153 = 5129365) B5129365
theorem B1350515 : Blo 1348993 1350515 := bstep (se 1 (by rfl) ⟨1012886, by rfl⟩ : syracuseStep 1350515 = 2025773) B2025773
theorem B4553603 : Blo 1348993 4553603 := bstep (se 1 (by rfl) ⟨3415202, by rfl⟩ : syracuseStep 4553603 = 6830405) B6830405
theorem B1350531 : Blo 1348993 1350531 := bstep (se 1 (by rfl) ⟨1012898, by rfl⟩ : syracuseStep 1350531 = 2025797) B2025797
theorem B1350547 : Blo 1348993 1350547 := bstep (se 1 (by rfl) ⟨1012910, by rfl⟩ : syracuseStep 1350547 = 2025821) B2025821
theorem B3464099 : Blo 1348993 3464099 := bstep (se 1 (by rfl) ⟨2598074, by rfl⟩ : syracuseStep 3464099 = 5196149) B5196149
theorem B1350563 : Blo 1348993 1350563 := bstep (se 1 (by rfl) ⟨1012922, by rfl⟩ : syracuseStep 1350563 = 2025845) B2025845
theorem B3242929 : Blo 1348993 3242929 := bstep (se 2 (by rfl) ⟨1216098, by rfl⟩ : syracuseStep 3242929 = 2432197) B2432197
theorem B3038129 : Blo 1348993 3038129 := bstep (se 2 (by rfl) ⟨1139298, by rfl⟩ : syracuseStep 3038129 = 2278597) B2278597
theorem B1350579 : Blo 1348993 1350579 := bstep (se 1 (by rfl) ⟨1012934, by rfl⟩ : syracuseStep 1350579 = 2025869) B2025869
theorem B3038147 : Blo 1348993 3038147 := bstep (se 1 (by rfl) ⟨2278610, by rfl⟩ : syracuseStep 3038147 = 4557221) B4557221
theorem B1350595 : Blo 1348993 1350595 := bstep (se 1 (by rfl) ⟨1012946, by rfl⟩ : syracuseStep 1350595 = 2025893) B2025893
theorem B6831053 : Blo 1348993 6831053 := bstep (se 3 (by rfl) ⟨1280822, by rfl⟩ : syracuseStep 6831053 = 2561645) B2561645
theorem B1350611 : Blo 1348993 1350611 := bstep (se 1 (by rfl) ⟨1012958, by rfl⟩ : syracuseStep 1350611 = 2025917) B2025917
theorem B1350627 : Blo 1348993 1350627 := bstep (se 1 (by rfl) ⟨1012970, by rfl⟩ : syracuseStep 1350627 = 2025941) B2025941
theorem B1350643 : Blo 1348993 1350643 := bstep (se 1 (by rfl) ⟨1012982, by rfl⟩ : syracuseStep 1350643 = 2025965) B2025965
theorem B1350659 : Blo 1348993 1350659 := bstep (se 1 (by rfl) ⟨1012994, by rfl⟩ : syracuseStep 1350659 = 2025989) B2025989
theorem B3243025 : Blo 1348993 3243025 := bstep (se 2 (by rfl) ⟨1216134, by rfl⟩ : syracuseStep 3243025 = 2432269) B2432269
theorem B1350675 : Blo 1348993 1350675 := bstep (se 1 (by rfl) ⟨1013006, by rfl⟩ : syracuseStep 1350675 = 2026013) B2026013
theorem B1350691 : Blo 1348993 1350691 := bstep (se 1 (by rfl) ⟨1013018, by rfl⟩ : syracuseStep 1350691 = 2026037) B2026037
theorem B1350707 : Blo 1348993 1350707 := bstep (se 1 (by rfl) ⟨1013030, by rfl⟩ : syracuseStep 1350707 = 2026061) B2026061
theorem B3079235 : Blo 1348993 3079235 := bstep (se 1 (by rfl) ⟨2309426, by rfl⟩ : syracuseStep 3079235 = 4618853) B4618853
theorem B1350723 : Blo 1348993 1350723 := bstep (se 1 (by rfl) ⟨1013042, by rfl⟩ : syracuseStep 1350723 = 2026085) B2026085
theorem B2161747 : Blo 1348993 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B1350739 : Blo 1348993 1350739 := bstep (se 1 (by rfl) ⟨1013054, by rfl⟩ : syracuseStep 1350739 = 2026109) B2026109
theorem B1350755 : Blo 1348993 1350755 := bstep (se 1 (by rfl) ⟨1013066, by rfl⟩ : syracuseStep 1350755 = 2026133) B2026133
theorem B1350771 : Blo 1348993 1350771 := bstep (se 1 (by rfl) ⟨1013078, by rfl⟩ : syracuseStep 1350771 = 2026157) B2026157
theorem B1350787 : Blo 1348993 1350787 := bstep (se 1 (by rfl) ⟨1013090, by rfl⟩ : syracuseStep 1350787 = 2026181) B2026181
theorem B10247309 : Blo 1348993 10247309 := bstep (se 3 (by rfl) ⟨1921370, by rfl⟩ : syracuseStep 10247309 = 3842741) B3842741
theorem B4553873 : Blo 1348993 4553873 := bstep (se 2 (by rfl) ⟨1707702, by rfl⟩ : syracuseStep 4553873 = 3415405) B3415405
theorem B1350803 : Blo 1348993 1350803 := bstep (se 1 (by rfl) ⟨1013102, by rfl⟩ : syracuseStep 1350803 = 2026205) B2026205
theorem B1350819 : Blo 1348993 1350819 := bstep (se 1 (by rfl) ⟨1013114, by rfl⟩ : syracuseStep 1350819 = 2026229) B2026229
theorem B1350835 : Blo 1348993 1350835 := bstep (se 1 (by rfl) ⟨1013126, by rfl⟩ : syracuseStep 1350835 = 2026253) B2026253
theorem B2276545 : Blo 1348993 2276545 := bstep (se 2 (by rfl) ⟨853704, by rfl⟩ : syracuseStep 2276545 = 1707409) B1707409
theorem B1350851 : Blo 1348993 1350851 := bstep (se 1 (by rfl) ⟨1013138, by rfl⟩ : syracuseStep 1350851 = 2026277) B2026277
theorem B3038417 : Blo 1348993 3038417 := bstep (se 2 (by rfl) ⟨1139406, by rfl⟩ : syracuseStep 3038417 = 2278813) B2278813
theorem B1350867 : Blo 1348993 1350867 := bstep (se 1 (by rfl) ⟨1013150, by rfl⟩ : syracuseStep 1350867 = 2026301) B2026301
theorem B2276579 : Blo 1348993 2276579 := bstep (se 1 (by rfl) ⟨1707434, by rfl⟩ : syracuseStep 2276579 = 3414869) B3414869
theorem B3038435 : Blo 1348993 3038435 := bstep (se 1 (by rfl) ⟨2278826, by rfl⟩ : syracuseStep 3038435 = 4557653) B4557653
theorem B1350883 : Blo 1348993 1350883 := bstep (se 1 (by rfl) ⟨1013162, by rfl⟩ : syracuseStep 1350883 = 2026325) B2026325
theorem B1350899 : Blo 1348993 1350899 := bstep (se 1 (by rfl) ⟨1013174, by rfl⟩ : syracuseStep 1350899 = 2026349) B2026349
theorem B1350915 : Blo 1348993 1350915 := bstep (se 1 (by rfl) ⟨1013186, by rfl⟩ : syracuseStep 1350915 = 2026373) B2026373
theorem B1350931 : Blo 1348993 1350931 := bstep (se 1 (by rfl) ⟨1013198, by rfl⟩ : syracuseStep 1350931 = 2026397) B2026397
theorem B1350947 : Blo 1348993 1350947 := bstep (se 1 (by rfl) ⟨1013210, by rfl⟩ : syracuseStep 1350947 = 2026421) B2026421
theorem B1350963 : Blo 1348993 1350963 := bstep (se 1 (by rfl) ⟨1013222, by rfl⟩ : syracuseStep 1350963 = 2026445) B2026445
theorem B1350979 : Blo 1348993 1350979 := bstep (se 1 (by rfl) ⟨1013234, by rfl⟩ : syracuseStep 1350979 = 2026469) B2026469
theorem B2276707 : Blo 1348993 2276707 := bstep (se 1 (by rfl) ⟨1707530, by rfl⟩ : syracuseStep 2276707 = 3415061) B3415061
theorem B1539523 : Blo 1348993 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B7683569 : Blo 1348993 7683569 := bstep (se 2 (by rfl) ⟨2881338, by rfl⟩ : syracuseStep 7683569 = 5762677) B5762677
theorem B2276849 : Blo 1348993 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B3038705 : Blo 1348993 3038705 := bstep (se 2 (by rfl) ⟨1139514, by rfl⟩ : syracuseStep 3038705 = 2279029) B2279029
theorem B3038723 : Blo 1348993 3038723 := bstep (se 1 (by rfl) ⟨2279042, by rfl⟩ : syracuseStep 3038723 = 4558085) B4558085
theorem B2162209 : Blo 1348993 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B2276977 : Blo 1348993 2276977 := bstep (se 2 (by rfl) ⟨853866, by rfl⟩ : syracuseStep 2276977 = 1707733) B1707733
theorem B2162305 : Blo 1348993 2162305 := bstep (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) B1621729
theorem B2277011 : Blo 1348993 2277011 := bstep (se 1 (by rfl) ⟨1707758, by rfl⟩ : syracuseStep 2277011 = 3415517) B3415517
theorem B4554413 : Blo 1348993 4554413 := bstep (se 3 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 4554413 = 1707905) B1707905
theorem B3415729 : Blo 1348993 3415729 := bstep (se 2 (by rfl) ⟨1280898, by rfl⟩ : syracuseStep 3415729 = 2561797) B2561797
theorem B4554467 : Blo 1348993 4554467 := bstep (se 1 (by rfl) ⟨3415850, by rfl⟩ : syracuseStep 4554467 = 6831701) B6831701
theorem B5127907 : Blo 1348993 5127907 := bstep (se 1 (by rfl) ⟨3845930, by rfl⟩ : syracuseStep 5127907 = 7691861) B7691861
theorem B2563825 : Blo 1348993 2563825 := bstep (se 2 (by rfl) ⟨961434, by rfl⟩ : syracuseStep 2563825 = 1922869) B1922869
theorem B3038993 : Blo 1348993 3038993 := bstep (se 2 (by rfl) ⟨1139622, by rfl⟩ : syracuseStep 3038993 = 2279245) B2279245
theorem B2277139 : Blo 1348993 2277139 := bstep (se 1 (by rfl) ⟨1707854, by rfl⟩ : syracuseStep 2277139 = 3415709) B3415709
theorem B2162465 : Blo 1348993 2162465 := bstep (se 2 (by rfl) ⟨810924, by rfl⟩ : syracuseStep 2162465 = 1621849) B1621849
theorem B3039011 : Blo 1348993 3039011 := bstep (se 1 (by rfl) ⟨2279258, by rfl⟩ : syracuseStep 3039011 = 4558517) B4558517
theorem B2080561 : Blo 1348993 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B2309939 : Blo 1348993 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B11091811 : Blo 1348993 11091811 := bstep (se 1 (by rfl) ⟨8318858, by rfl⟩ : syracuseStep 11091811 = 16637717) B16637717
theorem B2277281 : Blo 1348993 2277281 := bstep (se 2 (by rfl) ⟨853980, by rfl⟩ : syracuseStep 2277281 = 1707961) B1707961
theorem B3416003 : Blo 1348993 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B2465731 : Blo 1348993 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B4554737 : Blo 1348993 4554737 := bstep (se 2 (by rfl) ⟨1708026, by rfl⟩ : syracuseStep 4554737 = 3416053) B3416053
theorem B8208449 : Blo 1348993 8208449 := bstep (se 2 (by rfl) ⟨3078168, by rfl⟩ : syracuseStep 8208449 = 6156337) B6156337
theorem B2023499 : Blo 1348993 2023499 := bstep (se 1 (by rfl) ⟨1517624, by rfl⟩ : syracuseStep 2023499 = 3035249) B3035249
theorem B19447883 : Blo 1348993 19447883 := bstep (se 1 (by rfl) ⟨14585912, by rfl⟩ : syracuseStep 19447883 = 29171825) B29171825
theorem B20774987 : Blo 1348993 20774987 := bstep (se 1 (by rfl) ⟨15581240, by rfl⟩ : syracuseStep 20774987 = 31162481) B31162481
theorem B2023511 : Blo 1348993 2023511 := bstep (se 1 (by rfl) ⟨1517633, by rfl⟩ : syracuseStep 2023511 = 3035267) B3035267
theorem B2277463 : Blo 1348993 2277463 := bstep (se 1 (by rfl) ⟨1708097, by rfl⟩ : syracuseStep 2277463 = 3416195) B3416195
theorem B3244121 : Blo 1348993 3244121 := bstep (se 2 (by rfl) ⟨1216545, by rfl⟩ : syracuseStep 3244121 = 2433091) B2433091
theorem B4554845 : Blo 1348993 4554845 := bstep (se 3 (by rfl) ⟨854033, by rfl⟩ : syracuseStep 4554845 = 1708067) B1708067
theorem B3039371 : Blo 1348993 3039371 := bstep (se 1 (by rfl) ⟨2279528, by rfl⟩ : syracuseStep 3039371 = 4559057) B4559057
theorem B3416215 : Blo 1348993 3416215 := bstep (se 1 (by rfl) ⟨2562161, by rfl⟩ : syracuseStep 3416215 = 5124323) B5124323
theorem B18473111 : Blo 1348993 18473111 := bstep (se 1 (by rfl) ⟨13854833, by rfl⟩ : syracuseStep 18473111 = 27709667) B27709667
theorem B2023577 : Blo 1348993 2023577 := bstep (se 2 (by rfl) ⟨758841, by rfl⟩ : syracuseStep 2023577 = 1517683) B1517683
theorem B3039425 : Blo 1348993 3039425 := bstep (se 2 (by rfl) ⟨1139784, by rfl⟩ : syracuseStep 3039425 = 2279569) B2279569
theorem B2883799 : Blo 1348993 2883799 := bstep (se 1 (by rfl) ⟨2162849, by rfl⟩ : syracuseStep 2883799 = 4325699) B4325699
theorem B2564311 : Blo 1348993 2564311 := bstep (se 1 (by rfl) ⟨1923233, by rfl⟩ : syracuseStep 2564311 = 3846467) B3846467
theorem B2023691 : Blo 1348993 2023691 := bstep (se 1 (by rfl) ⟨1517768, by rfl⟩ : syracuseStep 2023691 = 3035537) B3035537
theorem B2023703 : Blo 1348993 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B2023769 : Blo 1348993 2023769 := bstep (se 2 (by rfl) ⟨758913, by rfl⟩ : syracuseStep 2023769 = 1517827) B1517827
theorem B3080587 : Blo 1348993 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B3039641 : Blo 1348993 3039641 := bstep (se 2 (by rfl) ⟨1139865, by rfl⟩ : syracuseStep 3039641 = 2279731) B2279731
theorem B2564531 : Blo 1348993 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B2023883 : Blo 1348993 2023883 := bstep (se 1 (by rfl) ⟨1517912, by rfl⟩ : syracuseStep 2023883 = 3035825) B3035825
theorem B2023895 : Blo 1348993 2023895 := bstep (se 1 (by rfl) ⟨1517921, by rfl⟩ : syracuseStep 2023895 = 3035843) B3035843
theorem B2310617 : Blo 1348993 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B1540567 : Blo 1348993 1540567 := bstep (se 1 (by rfl) ⟨1155425, by rfl⟩ : syracuseStep 1540567 = 2310851) B2310851
theorem B3039731 : Blo 1348993 3039731 := bstep (se 1 (by rfl) ⟨2279798, by rfl⟩ : syracuseStep 3039731 = 4559597) B4559597
theorem B2023961 : Blo 1348993 2023961 := bstep (se 2 (by rfl) ⟨758985, by rfl⟩ : syracuseStep 2023961 = 1517971) B1517971
theorem B3416651 : Blo 1348993 3416651 := bstep (se 1 (by rfl) ⟨2562488, by rfl⟩ : syracuseStep 3416651 = 5124977) B5124977
theorem B2024075 : Blo 1348993 2024075 := bstep (se 1 (by rfl) ⟨1518056, by rfl⟩ : syracuseStep 2024075 = 3036113) B3036113
theorem B2024087 : Blo 1348993 2024087 := bstep (se 1 (by rfl) ⟨1518065, by rfl⟩ : syracuseStep 2024087 = 3036131) B3036131
theorem B18719383 : Blo 1348993 18719383 := bstep (se 1 (by rfl) ⟨14039537, by rfl⟩ : syracuseStep 18719383 = 28079075) B28079075
theorem B2564759 : Blo 1348993 2564759 := bstep (se 1 (by rfl) ⟨1923569, by rfl⟩ : syracuseStep 2564759 = 3847139) B3847139
theorem B2278091 : Blo 1348993 2278091 := bstep (se 1 (by rfl) ⟨1708568, by rfl⟩ : syracuseStep 2278091 = 3417137) B3417137
theorem B2024153 : Blo 1348993 2024153 := bstep (se 2 (by rfl) ⟨759057, by rfl⟩ : syracuseStep 2024153 = 1518115) B1518115
theorem B5767939 : Blo 1348993 5767939 := bstep (se 1 (by rfl) ⟨4325954, by rfl⟩ : syracuseStep 5767939 = 8651909) B8651909
theorem B7299857 : Blo 1348993 7299857 := bstep (se 2 (by rfl) ⟨2737446, by rfl⟩ : syracuseStep 7299857 = 5474893) B5474893
theorem B2024267 : Blo 1348993 2024267 := bstep (se 1 (by rfl) ⟨1518200, by rfl⟩ : syracuseStep 2024267 = 3036401) B3036401
theorem B2278219 : Blo 1348993 2278219 := bstep (se 1 (by rfl) ⟨1708664, by rfl⟩ : syracuseStep 2278219 = 3417329) B3417329
theorem B2024279 : Blo 1348993 2024279 := bstep (se 1 (by rfl) ⟨1518209, by rfl⟩ : syracuseStep 2024279 = 3036419) B3036419
theorem B2024345 : Blo 1348993 2024345 := bstep (se 2 (by rfl) ⟨759129, by rfl⟩ : syracuseStep 2024345 = 1518259) B1518259
theorem B6489011 : Blo 1348993 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B3417025 : Blo 1348993 3417025 := bstep (se 2 (by rfl) ⟨1281384, by rfl⟩ : syracuseStep 3417025 = 2562769) B2562769
theorem B5129153 : Blo 1348993 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B2278361 : Blo 1348993 2278361 := bstep (se 2 (by rfl) ⟨854385, by rfl⟩ : syracuseStep 2278361 = 1708771) B1708771
theorem B4326365 : Blo 1348993 4326365 := bstep (se 3 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 4326365 = 1622387) B1622387
theorem B2024459 : Blo 1348993 2024459 := bstep (se 1 (by rfl) ⟨1518344, by rfl⟩ : syracuseStep 2024459 = 3036689) B3036689
theorem B2884619 : Blo 1348993 2884619 := bstep (se 1 (by rfl) ⟨2163464, by rfl⟩ : syracuseStep 2884619 = 4326929) B4326929
theorem B2024471 : Blo 1348993 2024471 := bstep (se 1 (by rfl) ⟨1518353, by rfl⟩ : syracuseStep 2024471 = 3036707) B3036707
theorem B6489163 : Blo 1348993 6489163 := bstep (se 1 (by rfl) ⟨4866872, by rfl⟩ : syracuseStep 6489163 = 9733745) B9733745
theorem B2024537 : Blo 1348993 2024537 := bstep (se 2 (by rfl) ⟨759201, by rfl⟩ : syracuseStep 2024537 = 1518403) B1518403
theorem B2278489 : Blo 1348993 2278489 := bstep (se 2 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 2278489 = 1708867) B1708867
theorem B6489239 : Blo 1348993 6489239 := bstep (se 1 (by rfl) ⟨4866929, by rfl⟩ : syracuseStep 6489239 = 9733859) B9733859
theorem B2024651 : Blo 1348993 2024651 := bstep (se 1 (by rfl) ⟨1518488, by rfl⟩ : syracuseStep 2024651 = 3036977) B3036977
theorem B4555979 : Blo 1348993 4555979 := bstep (se 1 (by rfl) ⟨3416984, by rfl⟩ : syracuseStep 4555979 = 6833969) B6833969
theorem B2024663 : Blo 1348993 2024663 := bstep (se 1 (by rfl) ⟨1518497, by rfl⟩ : syracuseStep 2024663 = 3036995) B3036995
theorem B2024729 : Blo 1348993 2024729 := bstep (se 2 (by rfl) ⟨759273, by rfl⟩ : syracuseStep 2024729 = 1518547) B1518547
theorem B3843379 : Blo 1348993 3843379 := bstep (se 1 (by rfl) ⟨2882534, by rfl⟩ : syracuseStep 3843379 = 5765069) B5765069
theorem B6833483 : Blo 1348993 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B2024843 : Blo 1348993 2024843 := bstep (se 1 (by rfl) ⟨1518632, by rfl⟩ : syracuseStep 2024843 = 3037265) B3037265
theorem B2024855 : Blo 1348993 2024855 := bstep (se 1 (by rfl) ⟨1518641, by rfl⟩ : syracuseStep 2024855 = 3037283) B3037283
theorem B2024921 : Blo 1348993 2024921 := bstep (se 2 (by rfl) ⟨759345, by rfl⟩ : syracuseStep 2024921 = 1518691) B1518691
theorem B4556249 : Blo 1348993 4556249 := bstep (se 2 (by rfl) ⟨1708593, by rfl⟩ : syracuseStep 4556249 = 3417187) B3417187
theorem B3843607 : Blo 1348993 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B3417623 : Blo 1348993 3417623 := bstep (se 1 (by rfl) ⟨2563217, by rfl⟩ : syracuseStep 3417623 = 5126435) B5126435
theorem B2025035 : Blo 1348993 2025035 := bstep (se 1 (by rfl) ⟨1518776, by rfl⟩ : syracuseStep 2025035 = 3037553) B3037553
theorem B2025047 : Blo 1348993 2025047 := bstep (se 1 (by rfl) ⟨1518785, by rfl⟩ : syracuseStep 2025047 = 3037571) B3037571
theorem B2279063 : Blo 1348993 2279063 := bstep (se 1 (by rfl) ⟨1709297, by rfl⟩ : syracuseStep 2279063 = 3418595) B3418595
theorem B2025113 : Blo 1348993 2025113 := bstep (se 2 (by rfl) ⟨759417, by rfl⟩ : syracuseStep 2025113 = 1518835) B1518835
theorem B2025227 : Blo 1348993 2025227 := bstep (se 1 (by rfl) ⟨1518920, by rfl⟩ : syracuseStep 2025227 = 3037841) B3037841
theorem B2025239 : Blo 1348993 2025239 := bstep (se 1 (by rfl) ⟨1518929, by rfl⟩ : syracuseStep 2025239 = 3037859) B3037859
theorem B2279191 : Blo 1348993 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B8644427 : Blo 1348993 8644427 := bstep (se 1 (by rfl) ⟨6483320, by rfl⟩ : syracuseStep 8644427 = 12966641) B12966641
theorem B2025305 : Blo 1348993 2025305 := bstep (se 2 (by rfl) ⟨759489, by rfl⟩ : syracuseStep 2025305 = 1518979) B1518979
theorem B2025419 : Blo 1348993 2025419 := bstep (se 1 (by rfl) ⟨1519064, by rfl⟩ : syracuseStep 2025419 = 3038129) B3038129
theorem B9734093 : Blo 1348993 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B2025431 : Blo 1348993 2025431 := bstep (se 1 (by rfl) ⟨1519073, by rfl⟩ : syracuseStep 2025431 = 3038147) B3038147
theorem B2025497 : Blo 1348993 2025497 := bstep (se 2 (by rfl) ⟨759561, by rfl⟩ : syracuseStep 2025497 = 1519123) B1519123
theorem B12978251 : Blo 1348993 12978251 := bstep (se 1 (by rfl) ⟨9733688, by rfl⟩ : syracuseStep 12978251 = 19467377) B19467377
theorem B12314717 : Blo 1348993 12314717 := bstep (se 3 (by rfl) ⟨2309009, by rfl⟩ : syracuseStep 12314717 = 4618019) B4618019
theorem B2025611 : Blo 1348993 2025611 := bstep (se 1 (by rfl) ⟨1519208, by rfl⟩ : syracuseStep 2025611 = 3038417) B3038417
theorem B1517719 : Blo 1348993 1517719 := bstep (se 1 (by rfl) ⟨1138289, by rfl⟩ : syracuseStep 1517719 = 2276579) B2276579
theorem B4556951 : Blo 1348993 4556951 := bstep (se 1 (by rfl) ⟨3417713, by rfl⟩ : syracuseStep 4556951 = 6835427) B6835427
theorem B2025623 : Blo 1348993 2025623 := bstep (se 1 (by rfl) ⟨1519217, by rfl⟩ : syracuseStep 2025623 = 3038435) B3038435
theorem B2025689 : Blo 1348993 2025689 := bstep (se 2 (by rfl) ⟨759633, by rfl⟩ : syracuseStep 2025689 = 1519267) B1519267
theorem B5122349 : Blo 1348993 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B3418433 : Blo 1348993 3418433 := bstep (se 2 (by rfl) ⟨1281912, by rfl⟩ : syracuseStep 3418433 = 2563825) B2563825
theorem B4868417 : Blo 1348993 4868417 := bstep (se 2 (by rfl) ⟨1825656, by rfl⟩ : syracuseStep 4868417 = 3651313) B3651313
theorem B5122379 : Blo 1348993 5122379 := bstep (se 1 (by rfl) ⟨3841784, by rfl⟩ : syracuseStep 5122379 = 7683569) B7683569
theorem B1517899 : Blo 1348993 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B2025803 : Blo 1348993 2025803 := bstep (se 1 (by rfl) ⟨1519352, by rfl⟩ : syracuseStep 2025803 = 3038705) B3038705
theorem B2025815 : Blo 1348993 2025815 := bstep (se 1 (by rfl) ⟨1519361, by rfl⟩ : syracuseStep 2025815 = 3038723) B3038723
theorem B13150565 : Blo 1348993 13150565 := bstep (se 4 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 13150565 = 2465731) B2465731
theorem B2025881 : Blo 1348993 2025881 := bstep (se 2 (by rfl) ⟨759705, by rfl⟩ : syracuseStep 2025881 = 1519411) B1519411
theorem B1518007 : Blo 1348993 1518007 := bstep (se 1 (by rfl) ⟨1138505, by rfl⟩ : syracuseStep 1518007 = 2277011) B2277011
theorem B4868545 : Blo 1348993 4868545 := bstep (se 2 (by rfl) ⟨1825704, by rfl⟩ : syracuseStep 4868545 = 3651409) B3651409
theorem B14789081 : Blo 1348993 14789081 := bstep (se 2 (by rfl) ⟨5545905, by rfl⟩ : syracuseStep 14789081 = 11091811) B11091811
theorem B2025995 : Blo 1348993 2025995 := bstep (se 1 (by rfl) ⟨1519496, by rfl⟩ : syracuseStep 2025995 = 3038993) B3038993
theorem B2026007 : Blo 1348993 2026007 := bstep (se 1 (by rfl) ⟨1519505, by rfl⟩ : syracuseStep 2026007 = 3039011) B3039011
theorem B5769751 : Blo 1348993 5769751 := bstep (se 1 (by rfl) ⟨4327313, by rfl⟩ : syracuseStep 5769751 = 8654627) B8654627
theorem B2026073 : Blo 1348993 2026073 := bstep (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) B1519555
theorem B1518187 : Blo 1348993 1518187 := bstep (se 1 (by rfl) ⟨1138640, by rfl⟩ : syracuseStep 1518187 = 2277281) B2277281
theorem B4557491 : Blo 1348993 4557491 := bstep (se 1 (by rfl) ⟨3418118, by rfl⟩ : syracuseStep 4557491 = 6836237) B6836237
theorem B2026187 : Blo 1348993 2026187 := bstep (se 1 (by rfl) ⟨1519640, by rfl⟩ : syracuseStep 2026187 = 3039281) B3039281
theorem B1518295 : Blo 1348993 1518295 := bstep (se 1 (by rfl) ⟨1138721, by rfl⟩ : syracuseStep 1518295 = 2277443) B2277443
theorem B2026199 : Blo 1348993 2026199 := bstep (se 1 (by rfl) ⟨1519649, by rfl⟩ : syracuseStep 2026199 = 3039299) B3039299
theorem B2026265 : Blo 1348993 2026265 := bstep (se 2 (by rfl) ⟨759849, by rfl⟩ : syracuseStep 2026265 = 1519699) B1519699
theorem B7301933 : Blo 1348993 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B5843801 : Blo 1348993 5843801 := bstep (se 2 (by rfl) ⟨2191425, by rfl⟩ : syracuseStep 5843801 = 4382851) B4382851
theorem B3418969 : Blo 1348993 3418969 := bstep (se 2 (by rfl) ⟨1282113, by rfl⟩ : syracuseStep 3418969 = 2564227) B2564227
theorem B8211293 : Blo 1348993 8211293 := bstep (se 3 (by rfl) ⟨1539617, by rfl⟩ : syracuseStep 8211293 = 3079235) B3079235
theorem B1518475 : Blo 1348993 1518475 := bstep (se 1 (by rfl) ⟨1138856, by rfl⟩ : syracuseStep 1518475 = 2277713) B2277713
theorem B2026379 : Blo 1348993 2026379 := bstep (se 1 (by rfl) ⟨1519784, by rfl⟩ : syracuseStep 2026379 = 3039569) B3039569
theorem B2026391 : Blo 1348993 2026391 := bstep (se 1 (by rfl) ⟨1519793, by rfl⟩ : syracuseStep 2026391 = 3039587) B3039587
theorem B2567065 : Blo 1348993 2567065 := bstep (se 2 (by rfl) ⟨962649, by rfl⟩ : syracuseStep 2567065 = 1925299) B1925299
theorem B4557761 : Blo 1348993 4557761 := bstep (se 2 (by rfl) ⟨1709160, by rfl⟩ : syracuseStep 4557761 = 3418321) B3418321
theorem B5123033 : Blo 1348993 5123033 := bstep (se 2 (by rfl) ⟨1921137, by rfl⟩ : syracuseStep 5123033 = 3842275) B3842275
theorem B2026457 : Blo 1348993 2026457 := bstep (se 2 (by rfl) ⟨759921, by rfl⟩ : syracuseStep 2026457 = 1519843) B1519843
theorem B1518583 : Blo 1348993 1518583 := bstep (se 1 (by rfl) ⟨1138937, by rfl⟩ : syracuseStep 1518583 = 2277875) B2277875
theorem B3648577 : Blo 1348993 3648577 := bstep (se 2 (by rfl) ⟨1368216, by rfl⟩ : syracuseStep 3648577 = 2736433) B2736433
theorem B6835265 : Blo 1348993 6835265 := bstep (se 2 (by rfl) ⟨2563224, by rfl⟩ : syracuseStep 6835265 = 5126449) B5126449
theorem B11529317 : Blo 1348993 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B5770385 : Blo 1348993 5770385 := bstep (se 2 (by rfl) ⟨2163894, by rfl⟩ : syracuseStep 5770385 = 4327789) B4327789
theorem B1518763 : Blo 1348993 1518763 := bstep (se 1 (by rfl) ⟨1139072, by rfl⟩ : syracuseStep 1518763 = 2278145) B2278145
theorem B5123351 : Blo 1348993 5123351 := bstep (se 1 (by rfl) ⟨3842513, by rfl⟩ : syracuseStep 5123351 = 7685027) B7685027
theorem B1518871 : Blo 1348993 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B10939693 : Blo 1348993 10939693 := bstep (se 3 (by rfl) ⟨2051192, by rfl⟩ : syracuseStep 10939693 = 4102385) B4102385
theorem B3894617 : Blo 1348993 3894617 := bstep (se 2 (by rfl) ⟨1460481, by rfl⟩ : syracuseStep 3894617 = 2920963) B2920963
theorem B3845465 : Blo 1348993 3845465 := bstep (se 2 (by rfl) ⟨1442049, by rfl⟩ : syracuseStep 3845465 = 2884099) B2884099
theorem B1519051 : Blo 1348993 1519051 := bstep (se 1 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 1519051 = 2278577) B2278577
theorem B4558301 : Blo 1348993 4558301 := bstep (se 3 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 4558301 = 1709363) B1709363
theorem B1519159 : Blo 1348993 1519159 := bstep (se 1 (by rfl) ⟨1139369, by rfl⟩ : syracuseStep 1519159 = 2278739) B2278739
theorem B1560235 : Blo 1348993 1560235 := bstep (se 1 (by rfl) ⟨1170176, by rfl⟩ : syracuseStep 1560235 = 2340353) B2340353
theorem B19451573 : Blo 1348993 19451573 := bstep (se 5 (by rfl) ⟨911792, by rfl⟩ : syracuseStep 19451573 = 1823585) B1823585
theorem B1519339 : Blo 1348993 1519339 := bstep (se 1 (by rfl) ⟨1139504, by rfl⟩ : syracuseStep 1519339 = 2279009) B2279009
theorem B1707799 : Blo 1348993 1707799 := bstep (se 1 (by rfl) ⟨1280849, by rfl⟩ : syracuseStep 1707799 = 2561699) B2561699
theorem B1519447 : Blo 1348993 1519447 := bstep (se 1 (by rfl) ⟨1139585, by rfl⟩ : syracuseStep 1519447 = 2279171) B2279171
theorem B5124019 : Blo 1348993 5124019 := bstep (se 1 (by rfl) ⟨3843014, by rfl⟩ : syracuseStep 5124019 = 7686029) B7686029
theorem B15380441 : Blo 1348993 15380441 := bstep (se 2 (by rfl) ⟨5767665, by rfl⟩ : syracuseStep 15380441 = 11535331) B11535331
theorem B1519627 : Blo 1348993 1519627 := bstep (se 1 (by rfl) ⟨1139720, by rfl⟩ : syracuseStep 1519627 = 2279441) B2279441
theorem B23375947 : Blo 1348993 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B1519735 : Blo 1348993 1519735 := bstep (se 1 (by rfl) ⟨1139801, by rfl⟩ : syracuseStep 1519735 = 2279603) B2279603
theorem B3846295 : Blo 1348993 3846295 := bstep (se 1 (by rfl) ⟨2884721, by rfl⟩ : syracuseStep 3846295 = 5769443) B5769443
theorem B3035339 : Blo 1348993 3035339 := bstep (se 1 (by rfl) ⟨2276504, by rfl⟩ : syracuseStep 3035339 = 4553009) B4553009
theorem B3035393 : Blo 1348993 3035393 := bstep (se 2 (by rfl) ⟨1138272, by rfl⟩ : syracuseStep 3035393 = 2276545) B2276545
theorem B17305973 : Blo 1348993 17305973 := bstep (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) B1622435
theorem B7688627 : Blo 1348993 7688627 := bstep (se 1 (by rfl) ⟨5766470, by rfl⟩ : syracuseStep 7688627 = 11532941) B11532941
theorem B9736627 : Blo 1348993 9736627 := bstep (se 1 (by rfl) ⟨7302470, by rfl⟩ : syracuseStep 9736627 = 14604941) B14604941
theorem B3035609 : Blo 1348993 3035609 := bstep (se 2 (by rfl) ⟨1138353, by rfl⟩ : syracuseStep 3035609 = 2276707) B2276707
theorem B3035699 : Blo 1348993 3035699 := bstep (se 1 (by rfl) ⟨2276774, by rfl⟩ : syracuseStep 3035699 = 4553549) B4553549
theorem B5763635 : Blo 1348993 5763635 := bstep (se 1 (by rfl) ⟨4322726, by rfl⟩ : syracuseStep 5763635 = 8645453) B8645453
theorem B4559435 : Blo 1348993 4559435 := bstep (se 1 (by rfl) ⟨3419576, by rfl⟩ : syracuseStep 4559435 = 6839153) B6839153
theorem B3035735 : Blo 1348993 3035735 := bstep (se 1 (by rfl) ⟨2276801, by rfl⟩ : syracuseStep 3035735 = 4553603) B4553603
theorem B2052697 : Blo 1348993 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B7795379 : Blo 1348993 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B11530957 : Blo 1348993 11530957 := bstep (se 3 (by rfl) ⟨2162054, by rfl⟩ : syracuseStep 11530957 = 4324109) B4324109
theorem B3035915 : Blo 1348993 3035915 := bstep (se 1 (by rfl) ⟨2276936, by rfl⟩ : syracuseStep 3035915 = 4553873) B4553873
theorem B3035969 : Blo 1348993 3035969 := bstep (se 2 (by rfl) ⟨1138488, by rfl⟩ : syracuseStep 3035969 = 2276977) B2276977
theorem B5550923 : Blo 1348993 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B5551051 : Blo 1348993 5551051 := bstep (se 1 (by rfl) ⟨4163288, by rfl⟩ : syracuseStep 5551051 = 8326577) B8326577
theorem B3847115 : Blo 1348993 3847115 := bstep (se 1 (by rfl) ⟨2885336, by rfl⟩ : syracuseStep 3847115 = 5770673) B5770673
theorem B6837209 : Blo 1348993 6837209 := bstep (se 2 (by rfl) ⟨2563953, by rfl⟩ : syracuseStep 6837209 = 5127907) B5127907
theorem B3036185 : Blo 1348993 3036185 := bstep (se 2 (by rfl) ⟨1138569, by rfl⟩ : syracuseStep 3036185 = 2277139) B2277139
theorem B2774081 : Blo 1348993 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B4322393 : Blo 1348993 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B3036275 : Blo 1348993 3036275 := bstep (se 1 (by rfl) ⟨2277206, by rfl⟩ : syracuseStep 3036275 = 4554413) B4554413
theorem B5125265 : Blo 1348993 5125265 := bstep (se 2 (by rfl) ⟨1921974, by rfl⟩ : syracuseStep 5125265 = 3843949) B3843949
theorem B3036311 : Blo 1348993 3036311 := bstep (se 1 (by rfl) ⟨2277233, by rfl⟩ : syracuseStep 3036311 = 4554467) B4554467
theorem B3036491 : Blo 1348993 3036491 := bstep (se 1 (by rfl) ⟨2277368, by rfl⟩ : syracuseStep 3036491 = 4554737) B4554737
theorem B2561395 : Blo 1348993 2561395 := bstep (se 1 (by rfl) ⟨1921046, by rfl⟩ : syracuseStep 2561395 = 3842093) B3842093
theorem B3036545 : Blo 1348993 3036545 := bstep (se 2 (by rfl) ⟨1138704, by rfl⟩ : syracuseStep 3036545 = 2277409) B2277409
theorem B1349003 : Blo 1348993 1349003 := bstep (se 1 (by rfl) ⟨1011752, by rfl⟩ : syracuseStep 1349003 = 2023505) B2023505
theorem B1349015 : Blo 1348993 1349015 := bstep (se 1 (by rfl) ⟨1011761, by rfl⟩ : syracuseStep 1349015 = 2023523) B2023523
theorem B2053529 : Blo 1348993 2053529 := bstep (se 2 (by rfl) ⟨770073, by rfl⟩ : syracuseStep 2053529 = 1540147) B1540147
theorem B1349035 : Blo 1348993 1349035 := bstep (se 1 (by rfl) ⟨1011776, by rfl⟩ : syracuseStep 1349035 = 2023553) B2023553
theorem B1349047 : Blo 1348993 1349047 := bstep (se 1 (by rfl) ⟨1011785, by rfl⟩ : syracuseStep 1349047 = 2023571) B2023571
theorem B1349067 : Blo 1348993 1349067 := bstep (se 1 (by rfl) ⟨1011800, by rfl⟩ : syracuseStep 1349067 = 2023601) B2023601
theorem B1709515 : Blo 1348993 1709515 := bstep (se 1 (by rfl) ⟨1282136, by rfl⟩ : syracuseStep 1709515 = 2564273) B2564273
theorem B1349079 : Blo 1348993 1349079 := bstep (se 1 (by rfl) ⟨1011809, by rfl⟩ : syracuseStep 1349079 = 2023619) B2023619
theorem B1349099 : Blo 1348993 1349099 := bstep (se 1 (by rfl) ⟨1011824, by rfl⟩ : syracuseStep 1349099 = 2023649) B2023649
theorem B1349111 : Blo 1348993 1349111 := bstep (se 1 (by rfl) ⟨1011833, by rfl⟩ : syracuseStep 1349111 = 2023667) B2023667
theorem B1349131 : Blo 1348993 1349131 := bstep (se 1 (by rfl) ⟨1011848, by rfl⟩ : syracuseStep 1349131 = 2023697) B2023697
theorem B1349143 : Blo 1348993 1349143 := bstep (se 1 (by rfl) ⟨1011857, by rfl⟩ : syracuseStep 1349143 = 2023715) B2023715
theorem B1349163 : Blo 1348993 1349163 := bstep (se 1 (by rfl) ⟨1011872, by rfl⟩ : syracuseStep 1349163 = 2023745) B2023745
theorem B1349175 : Blo 1348993 1349175 := bstep (se 1 (by rfl) ⟨1011881, by rfl⟩ : syracuseStep 1349175 = 2023763) B2023763
theorem B1349195 : Blo 1348993 1349195 := bstep (se 1 (by rfl) ⟨1011896, by rfl⟩ : syracuseStep 1349195 = 2023793) B2023793
theorem B1349207 : Blo 1348993 1349207 := bstep (se 1 (by rfl) ⟨1011905, by rfl⟩ : syracuseStep 1349207 = 2023811) B2023811
theorem B3036761 : Blo 1348993 3036761 := bstep (se 2 (by rfl) ⟨1138785, by rfl⟩ : syracuseStep 3036761 = 2277571) B2277571
theorem B1349227 : Blo 1348993 1349227 := bstep (se 1 (by rfl) ⟨1011920, by rfl⟩ : syracuseStep 1349227 = 2023841) B2023841
theorem B1349239 : Blo 1348993 1349239 := bstep (se 1 (by rfl) ⟨1011929, by rfl⟩ : syracuseStep 1349239 = 2023859) B2023859
theorem B1349259 : Blo 1348993 1349259 := bstep (se 1 (by rfl) ⟨1011944, by rfl⟩ : syracuseStep 1349259 = 2023889) B2023889
theorem B1349271 : Blo 1348993 1349271 := bstep (se 1 (by rfl) ⟨1011953, by rfl⟩ : syracuseStep 1349271 = 2023907) B2023907
theorem B1349291 : Blo 1348993 1349291 := bstep (se 1 (by rfl) ⟨1011968, by rfl⟩ : syracuseStep 1349291 = 2023937) B2023937
theorem B3036851 : Blo 1348993 3036851 := bstep (se 1 (by rfl) ⟨2277638, by rfl⟩ : syracuseStep 3036851 = 4555277) B4555277
theorem B1349303 : Blo 1348993 1349303 := bstep (se 1 (by rfl) ⟨1011977, by rfl⟩ : syracuseStep 1349303 = 2023955) B2023955
theorem B1349323 : Blo 1348993 1349323 := bstep (se 1 (by rfl) ⟨1011992, by rfl⟩ : syracuseStep 1349323 = 2023985) B2023985
theorem B1349335 : Blo 1348993 1349335 := bstep (se 1 (by rfl) ⟨1012001, by rfl⟩ : syracuseStep 1349335 = 2024003) B2024003
theorem B3036887 : Blo 1348993 3036887 := bstep (se 1 (by rfl) ⟨2277665, by rfl⟩ : syracuseStep 3036887 = 4555331) B4555331
theorem B1349355 : Blo 1348993 1349355 := bstep (se 1 (by rfl) ⟨1012016, by rfl⟩ : syracuseStep 1349355 = 2024033) B2024033
theorem B1349367 : Blo 1348993 1349367 := bstep (se 1 (by rfl) ⟨1012025, by rfl⟩ : syracuseStep 1349367 = 2024051) B2024051
theorem B1349387 : Blo 1348993 1349387 := bstep (se 1 (by rfl) ⟨1012040, by rfl⟩ : syracuseStep 1349387 = 2024081) B2024081
theorem B1349399 : Blo 1348993 1349399 := bstep (se 1 (by rfl) ⟨1012049, by rfl⟩ : syracuseStep 1349399 = 2024099) B2024099
theorem B9729827 : Blo 1348993 9729827 := bstep (se 1 (by rfl) ⟨7297370, by rfl⟩ : syracuseStep 9729827 = 14594741) B14594741
theorem B1349419 : Blo 1348993 1349419 := bstep (se 1 (by rfl) ⟨1012064, by rfl⟩ : syracuseStep 1349419 = 2024129) B2024129
theorem B2561843 : Blo 1348993 2561843 := bstep (se 1 (by rfl) ⟨1921382, by rfl⟩ : syracuseStep 2561843 = 3842765) B3842765
theorem B1349431 : Blo 1348993 1349431 := bstep (se 1 (by rfl) ⟨1012073, by rfl⟩ : syracuseStep 1349431 = 2024147) B2024147
theorem B1349451 : Blo 1348993 1349451 := bstep (se 1 (by rfl) ⟨1012088, by rfl⟩ : syracuseStep 1349451 = 2024177) B2024177
theorem B5125963 : Blo 1348993 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B1349463 : Blo 1348993 1349463 := bstep (se 1 (by rfl) ⟨1012097, by rfl⟩ : syracuseStep 1349463 = 2024195) B2024195
theorem B2561881 : Blo 1348993 2561881 := bstep (se 2 (by rfl) ⟨960705, by rfl⟩ : syracuseStep 2561881 = 1921411) B1921411
theorem B7690085 : Blo 1348993 7690085 := bstep (se 4 (by rfl) ⟨720945, by rfl⟩ : syracuseStep 7690085 = 1441891) B1441891
theorem B1349483 : Blo 1348993 1349483 := bstep (se 1 (by rfl) ⟨1012112, by rfl⟩ : syracuseStep 1349483 = 2024225) B2024225
theorem B1349495 : Blo 1348993 1349495 := bstep (se 1 (by rfl) ⟨1012121, by rfl⟩ : syracuseStep 1349495 = 2024243) B2024243
theorem B1349515 : Blo 1348993 1349515 := bstep (se 1 (by rfl) ⟨1012136, by rfl⟩ : syracuseStep 1349515 = 2024273) B2024273
theorem B3037067 : Blo 1348993 3037067 := bstep (se 1 (by rfl) ⟨2277800, by rfl⟩ : syracuseStep 3037067 = 4555601) B4555601
theorem B1349527 : Blo 1348993 1349527 := bstep (se 1 (by rfl) ⟨1012145, by rfl⟩ : syracuseStep 1349527 = 2024291) B2024291
theorem B2881433 : Blo 1348993 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B1349547 : Blo 1348993 1349547 := bstep (se 1 (by rfl) ⟨1012160, by rfl⟩ : syracuseStep 1349547 = 2024321) B2024321
theorem B1349559 : Blo 1348993 1349559 := bstep (se 1 (by rfl) ⟨1012169, by rfl⟩ : syracuseStep 1349559 = 2024339) B2024339
theorem B3037121 : Blo 1348993 3037121 := bstep (se 2 (by rfl) ⟨1138920, by rfl⟩ : syracuseStep 3037121 = 2277841) B2277841
theorem B1349579 : Blo 1348993 1349579 := bstep (se 1 (by rfl) ⟨1012184, by rfl⟩ : syracuseStep 1349579 = 2024369) B2024369
theorem B1349591 : Blo 1348993 1349591 := bstep (se 1 (by rfl) ⟨1012193, by rfl⟩ : syracuseStep 1349591 = 2024387) B2024387
theorem B3078103 : Blo 1348993 3078103 := bstep (se 1 (by rfl) ⟨2308577, by rfl⟩ : syracuseStep 3078103 = 4617155) B4617155
theorem B4323289 : Blo 1348993 4323289 := bstep (se 2 (by rfl) ⟨1621233, by rfl⟩ : syracuseStep 4323289 = 3242467) B3242467
theorem B1349611 : Blo 1348993 1349611 := bstep (se 1 (by rfl) ⟨1012208, by rfl⟩ : syracuseStep 1349611 = 2024417) B2024417
theorem B1349623 : Blo 1348993 1349623 := bstep (se 1 (by rfl) ⟨1012217, by rfl⟩ : syracuseStep 1349623 = 2024435) B2024435
theorem B11532293 : Blo 1348993 11532293 := bstep (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) B2162305
theorem B1349643 : Blo 1348993 1349643 := bstep (se 1 (by rfl) ⟨1012232, by rfl⟩ : syracuseStep 1349643 = 2024465) B2024465
theorem B1349655 : Blo 1348993 1349655 := bstep (se 1 (by rfl) ⟨1012241, by rfl⟩ : syracuseStep 1349655 = 2024483) B2024483
theorem B1923097 : Blo 1348993 1923097 := bstep (se 2 (by rfl) ⟨721161, by rfl⟩ : syracuseStep 1923097 = 1442323) B1442323
theorem B1349675 : Blo 1348993 1349675 := bstep (se 1 (by rfl) ⟨1012256, by rfl⟩ : syracuseStep 1349675 = 2024513) B2024513
theorem B1349687 : Blo 1348993 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B1349707 : Blo 1348993 1349707 := bstep (se 1 (by rfl) ⟨1012280, by rfl⟩ : syracuseStep 1349707 = 2024561) B2024561
theorem B3651659 : Blo 1348993 3651659 := bstep (se 1 (by rfl) ⟨2738744, by rfl⟩ : syracuseStep 3651659 = 5477489) B5477489
theorem B1349719 : Blo 1348993 1349719 := bstep (se 1 (by rfl) ⟨1012289, by rfl⟩ : syracuseStep 1349719 = 2024579) B2024579
theorem B5126237 : Blo 1348993 5126237 := bstep (se 3 (by rfl) ⟨961169, by rfl⟩ : syracuseStep 5126237 = 1922339) B1922339
theorem B1349739 : Blo 1348993 1349739 := bstep (se 1 (by rfl) ⟨1012304, by rfl⟩ : syracuseStep 1349739 = 2024609) B2024609
theorem B1349751 : Blo 1348993 1349751 := bstep (se 1 (by rfl) ⟨1012313, by rfl⟩ : syracuseStep 1349751 = 2024627) B2024627
theorem B1349771 : Blo 1348993 1349771 := bstep (se 1 (by rfl) ⟨1012328, by rfl⟩ : syracuseStep 1349771 = 2024657) B2024657
theorem B4864151 : Blo 1348993 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B1349783 : Blo 1348993 1349783 := bstep (se 1 (by rfl) ⟨1012337, by rfl⟩ : syracuseStep 1349783 = 2024675) B2024675
theorem B3037337 : Blo 1348993 3037337 := bstep (se 2 (by rfl) ⟨1139001, by rfl⟩ : syracuseStep 3037337 = 2278003) B2278003
theorem B1349803 : Blo 1348993 1349803 := bstep (se 1 (by rfl) ⟨1012352, by rfl⟩ : syracuseStep 1349803 = 2024705) B2024705
theorem B4159667 : Blo 1348993 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B1349815 : Blo 1348993 1349815 := bstep (se 1 (by rfl) ⟨1012361, by rfl⟩ : syracuseStep 1349815 = 2024723) B2024723
theorem B1349835 : Blo 1348993 1349835 := bstep (se 1 (by rfl) ⟨1012376, by rfl⟩ : syracuseStep 1349835 = 2024753) B2024753
theorem B12982477 : Blo 1348993 12982477 := bstep (se 3 (by rfl) ⟨2434214, by rfl⟩ : syracuseStep 12982477 = 4868429) B4868429
theorem B24647885 : Blo 1348993 24647885 := bstep (se 3 (by rfl) ⟨4621478, by rfl⟩ : syracuseStep 24647885 = 9242957) B9242957
theorem B1349847 : Blo 1348993 1349847 := bstep (se 1 (by rfl) ⟨1012385, by rfl⟩ : syracuseStep 1349847 = 2024771) B2024771
theorem B1349867 : Blo 1348993 1349867 := bstep (se 1 (by rfl) ⟨1012400, by rfl⟩ : syracuseStep 1349867 = 2024801) B2024801
theorem B3037427 : Blo 1348993 3037427 := bstep (se 1 (by rfl) ⟨2278070, by rfl⟩ : syracuseStep 3037427 = 4556141) B4556141
theorem B1349879 : Blo 1348993 1349879 := bstep (se 1 (by rfl) ⟨1012409, by rfl⟩ : syracuseStep 1349879 = 2024819) B2024819
theorem B1349899 : Blo 1348993 1349899 := bstep (se 1 (by rfl) ⟨1012424, by rfl⟩ : syracuseStep 1349899 = 2024849) B2024849
theorem B1349911 : Blo 1348993 1349911 := bstep (se 1 (by rfl) ⟨1012433, by rfl⟩ : syracuseStep 1349911 = 2024867) B2024867
theorem B3037463 : Blo 1348993 3037463 := bstep (se 1 (by rfl) ⟨2278097, by rfl⟩ : syracuseStep 3037463 = 4556195) B4556195
theorem B2562329 : Blo 1348993 2562329 := bstep (se 2 (by rfl) ⟨960873, by rfl⟩ : syracuseStep 2562329 = 1921747) B1921747
theorem B1349931 : Blo 1348993 1349931 := bstep (se 1 (by rfl) ⟨1012448, by rfl⟩ : syracuseStep 1349931 = 2024897) B2024897
theorem B1349943 : Blo 1348993 1349943 := bstep (se 1 (by rfl) ⟨1012457, by rfl⟩ : syracuseStep 1349943 = 2024915) B2024915
theorem B1349963 : Blo 1348993 1349963 := bstep (se 1 (by rfl) ⟨1012472, by rfl⟩ : syracuseStep 1349963 = 2024945) B2024945
theorem B1349975 : Blo 1348993 1349975 := bstep (se 1 (by rfl) ⟨1012481, by rfl⟩ : syracuseStep 1349975 = 2024963) B2024963
theorem B1349995 : Blo 1348993 1349995 := bstep (se 1 (by rfl) ⟨1012496, by rfl⟩ : syracuseStep 1349995 = 2024993) B2024993
theorem B1350007 : Blo 1348993 1350007 := bstep (se 1 (by rfl) ⟨1012505, by rfl⟩ : syracuseStep 1350007 = 2025011) B2025011
theorem B1350027 : Blo 1348993 1350027 := bstep (se 1 (by rfl) ⟨1012520, by rfl⟩ : syracuseStep 1350027 = 2025041) B2025041
theorem B1350039 : Blo 1348993 1350039 := bstep (se 1 (by rfl) ⟨1012529, by rfl⟩ : syracuseStep 1350039 = 2025059) B2025059
theorem B1350059 : Blo 1348993 1350059 := bstep (se 1 (by rfl) ⟨1012544, by rfl⟩ : syracuseStep 1350059 = 2025089) B2025089
theorem B4004275 : Blo 1348993 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B1350071 : Blo 1348993 1350071 := bstep (se 1 (by rfl) ⟨1012553, by rfl⟩ : syracuseStep 1350071 = 2025107) B2025107
theorem B3037643 : Blo 1348993 3037643 := bstep (se 1 (by rfl) ⟨2278232, by rfl⟩ : syracuseStep 3037643 = 4556465) B4556465
theorem B1350091 : Blo 1348993 1350091 := bstep (se 1 (by rfl) ⟨1012568, by rfl⟩ : syracuseStep 1350091 = 2025137) B2025137
theorem B1350103 : Blo 1348993 1350103 := bstep (se 1 (by rfl) ⟨1012577, by rfl⟩ : syracuseStep 1350103 = 2025155) B2025155
theorem B1350123 : Blo 1348993 1350123 := bstep (se 1 (by rfl) ⟨1012592, by rfl⟩ : syracuseStep 1350123 = 2025185) B2025185
theorem B1350135 : Blo 1348993 1350135 := bstep (se 1 (by rfl) ⟨1012601, by rfl⟩ : syracuseStep 1350135 = 2025203) B2025203
theorem B3037697 : Blo 1348993 3037697 := bstep (se 2 (by rfl) ⟨1139136, by rfl⟩ : syracuseStep 3037697 = 2278273) B2278273
theorem B1350155 : Blo 1348993 1350155 := bstep (se 1 (by rfl) ⟨1012616, by rfl⟩ : syracuseStep 1350155 = 2025233) B2025233
theorem B1350167 : Blo 1348993 1350167 := bstep (se 1 (by rfl) ⟨1012625, by rfl⟩ : syracuseStep 1350167 = 2025251) B2025251
theorem B1350187 : Blo 1348993 1350187 := bstep (se 1 (by rfl) ⟨1012640, by rfl⟩ : syracuseStep 1350187 = 2025281) B2025281
theorem B6838829 : Blo 1348993 6838829 := bstep (se 3 (by rfl) ⟨1282280, by rfl⟩ : syracuseStep 6838829 = 2564561) B2564561
theorem B1350199 : Blo 1348993 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B4323905 : Blo 1348993 4323905 := bstep (se 2 (by rfl) ⟨1621464, by rfl⟩ : syracuseStep 4323905 = 3242929) B3242929
theorem B1350219 : Blo 1348993 1350219 := bstep (se 1 (by rfl) ⟨1012664, by rfl⟩ : syracuseStep 1350219 = 2025329) B2025329
theorem B1350231 : Blo 1348993 1350231 := bstep (se 1 (by rfl) ⟨1012673, by rfl⟩ : syracuseStep 1350231 = 2025347) B2025347
theorem B2431577 : Blo 1348993 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B1350251 : Blo 1348993 1350251 := bstep (se 1 (by rfl) ⟨1012688, by rfl⟩ : syracuseStep 1350251 = 2025377) B2025377
theorem B1350263 : Blo 1348993 1350263 := bstep (se 1 (by rfl) ⟨1012697, by rfl⟩ : syracuseStep 1350263 = 2025395) B2025395
theorem B1350283 : Blo 1348993 1350283 := bstep (se 1 (by rfl) ⟨1012712, by rfl⟩ : syracuseStep 1350283 = 2025425) B2025425
theorem B1350295 : Blo 1348993 1350295 := bstep (se 1 (by rfl) ⟨1012721, by rfl⟩ : syracuseStep 1350295 = 2025443) B2025443
theorem B1350315 : Blo 1348993 1350315 := bstep (se 1 (by rfl) ⟨1012736, by rfl⟩ : syracuseStep 1350315 = 2025473) B2025473
theorem B3414707 : Blo 1348993 3414707 := bstep (se 1 (by rfl) ⟨2561030, by rfl⟩ : syracuseStep 3414707 = 5122061) B5122061
theorem B1350327 : Blo 1348993 1350327 := bstep (se 1 (by rfl) ⟨1012745, by rfl⟩ : syracuseStep 1350327 = 2025491) B2025491
theorem B4324033 : Blo 1348993 4324033 := bstep (se 2 (by rfl) ⟨1621512, by rfl⟩ : syracuseStep 4324033 = 3243025) B3243025
theorem B3242699 : Blo 1348993 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B1350347 : Blo 1348993 1350347 := bstep (se 1 (by rfl) ⟨1012760, by rfl⟩ : syracuseStep 1350347 = 2025521) B2025521
theorem B1350359 : Blo 1348993 1350359 := bstep (se 1 (by rfl) ⟨1012769, by rfl⟩ : syracuseStep 1350359 = 2025539) B2025539
theorem B3037913 : Blo 1348993 3037913 := bstep (se 2 (by rfl) ⟨1139217, by rfl⟩ : syracuseStep 3037913 = 2278435) B2278435
theorem B1350379 : Blo 1348993 1350379 := bstep (se 1 (by rfl) ⟨1012784, by rfl⟩ : syracuseStep 1350379 = 2025569) B2025569
theorem B1350391 : Blo 1348993 1350391 := bstep (se 1 (by rfl) ⟨1012793, by rfl⟩ : syracuseStep 1350391 = 2025587) B2025587
theorem B1350411 : Blo 1348993 1350411 := bstep (se 1 (by rfl) ⟨1012808, by rfl⟩ : syracuseStep 1350411 = 2025617) B2025617
theorem B4553495 : Blo 1348993 4553495 := bstep (se 1 (by rfl) ⟨3415121, by rfl⟩ : syracuseStep 4553495 = 6830243) B6830243
theorem B5126935 : Blo 1348993 5126935 := bstep (se 1 (by rfl) ⟨3845201, by rfl⟩ : syracuseStep 5126935 = 7690403) B7690403
theorem B1350423 : Blo 1348993 1350423 := bstep (se 1 (by rfl) ⟨1012817, by rfl⟩ : syracuseStep 1350423 = 2025635) B2025635
theorem B1350443 : Blo 1348993 1350443 := bstep (se 1 (by rfl) ⟨1012832, by rfl⟩ : syracuseStep 1350443 = 2025665) B2025665
theorem B3038003 : Blo 1348993 3038003 := bstep (se 1 (by rfl) ⟨2278502, by rfl⟩ : syracuseStep 3038003 = 4557005) B4557005
theorem B1350455 : Blo 1348993 1350455 := bstep (se 1 (by rfl) ⟨1012841, by rfl⟩ : syracuseStep 1350455 = 2025683) B2025683
theorem B1620811 : Blo 1348993 1620811 := bstep (se 1 (by rfl) ⟨1215608, by rfl⟩ : syracuseStep 1620811 = 2431217) B2431217
theorem B2669387 : Blo 1348993 2669387 := bstep (se 1 (by rfl) ⟨2002040, by rfl⟩ : syracuseStep 2669387 = 4004081) B4004081
theorem B1350475 : Blo 1348993 1350475 := bstep (se 1 (by rfl) ⟨1012856, by rfl⟩ : syracuseStep 1350475 = 2025713) B2025713
theorem B3038039 : Blo 1348993 3038039 := bstep (se 1 (by rfl) ⟨2278529, by rfl⟩ : syracuseStep 3038039 = 4557059) B4557059
theorem B1350487 : Blo 1348993 1350487 := bstep (se 1 (by rfl) ⟨1012865, by rfl⟩ : syracuseStep 1350487 = 2025731) B2025731
theorem B1350507 : Blo 1348993 1350507 := bstep (se 1 (by rfl) ⟨1012880, by rfl⟩ : syracuseStep 1350507 = 2025761) B2025761
theorem B1350519 : Blo 1348993 1350519 := bstep (se 1 (by rfl) ⟨1012889, by rfl⟩ : syracuseStep 1350519 = 2025779) B2025779
theorem B1350539 : Blo 1348993 1350539 := bstep (se 1 (by rfl) ⟨1012904, by rfl⟩ : syracuseStep 1350539 = 2025809) B2025809
theorem B1350551 : Blo 1348993 1350551 := bstep (se 1 (by rfl) ⟨1012913, by rfl⟩ : syracuseStep 1350551 = 2025827) B2025827
theorem B1350571 : Blo 1348993 1350571 := bstep (se 1 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 1350571 = 2025857) B2025857
theorem B1350583 : Blo 1348993 1350583 := bstep (se 1 (by rfl) ⟨1012937, by rfl⟩ : syracuseStep 1350583 = 2025875) B2025875
theorem B1350603 : Blo 1348993 1350603 := bstep (se 1 (by rfl) ⟨1012952, by rfl⟩ : syracuseStep 1350603 = 2025905) B2025905
theorem B1350615 : Blo 1348993 1350615 := bstep (se 1 (by rfl) ⟨1012961, by rfl⟩ : syracuseStep 1350615 = 2025923) B2025923
theorem B1350635 : Blo 1348993 1350635 := bstep (se 1 (by rfl) ⟨1012976, by rfl⟩ : syracuseStep 1350635 = 2025953) B2025953
theorem B2776051 : Blo 1348993 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B1350647 : Blo 1348993 1350647 := bstep (se 1 (by rfl) ⟨1012985, by rfl⟩ : syracuseStep 1350647 = 2025971) B2025971
theorem B2563073 : Blo 1348993 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B4865027 : Blo 1348993 4865027 := bstep (se 1 (by rfl) ⟨3648770, by rfl⟩ : syracuseStep 4865027 = 7297541) B7297541
theorem B1621003 : Blo 1348993 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B3038219 : Blo 1348993 3038219 := bstep (se 1 (by rfl) ⟨2278664, by rfl⟩ : syracuseStep 3038219 = 4557329) B4557329
theorem B1350667 : Blo 1348993 1350667 := bstep (se 1 (by rfl) ⟨1013000, by rfl⟩ : syracuseStep 1350667 = 2026001) B2026001
theorem B1350679 : Blo 1348993 1350679 := bstep (se 1 (by rfl) ⟨1013009, by rfl⟩ : syracuseStep 1350679 = 2026019) B2026019
theorem B1350699 : Blo 1348993 1350699 := bstep (se 1 (by rfl) ⟨1013024, by rfl⟩ : syracuseStep 1350699 = 2026049) B2026049
theorem B1350711 : Blo 1348993 1350711 := bstep (se 1 (by rfl) ⟨1013033, by rfl⟩ : syracuseStep 1350711 = 2026067) B2026067
theorem B3038273 : Blo 1348993 3038273 := bstep (se 2 (by rfl) ⟨1139352, by rfl⟩ : syracuseStep 3038273 = 2278705) B2278705
theorem B1350731 : Blo 1348993 1350731 := bstep (se 1 (by rfl) ⟨1013048, by rfl⟩ : syracuseStep 1350731 = 2026097) B2026097
theorem B1350743 : Blo 1348993 1350743 := bstep (se 1 (by rfl) ⟨1013057, by rfl⟩ : syracuseStep 1350743 = 2026115) B2026115
theorem B1350763 : Blo 1348993 1350763 := bstep (se 1 (by rfl) ⟨1013072, by rfl⟩ : syracuseStep 1350763 = 2026145) B2026145
theorem B1522795 : Blo 1348993 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B1350775 : Blo 1348993 1350775 := bstep (se 1 (by rfl) ⟨1013081, by rfl⟩ : syracuseStep 1350775 = 2026163) B2026163
theorem B2276491 : Blo 1348993 2276491 := bstep (se 1 (by rfl) ⟨1707368, by rfl⟩ : syracuseStep 2276491 = 3414737) B3414737
theorem B1350795 : Blo 1348993 1350795 := bstep (se 1 (by rfl) ⟨1013096, by rfl⟩ : syracuseStep 1350795 = 2026193) B2026193
theorem B15367319 : Blo 1348993 15367319 := bstep (se 1 (by rfl) ⟨11525489, by rfl⟩ : syracuseStep 15367319 = 23050979) B23050979
theorem B1350807 : Blo 1348993 1350807 := bstep (se 1 (by rfl) ⟨1013105, by rfl⟩ : syracuseStep 1350807 = 2026211) B2026211
theorem B1350827 : Blo 1348993 1350827 := bstep (se 1 (by rfl) ⟨1013120, by rfl⟩ : syracuseStep 1350827 = 2026241) B2026241
theorem B1350839 : Blo 1348993 1350839 := bstep (se 1 (by rfl) ⟨1013129, by rfl⟩ : syracuseStep 1350839 = 2026259) B2026259
theorem B3415243 : Blo 1348993 3415243 := bstep (se 1 (by rfl) ⟨2561432, by rfl⟩ : syracuseStep 3415243 = 5122865) B5122865
theorem B1350859 : Blo 1348993 1350859 := bstep (se 1 (by rfl) ⟨1013144, by rfl⟩ : syracuseStep 1350859 = 2026289) B2026289
theorem B1350871 : Blo 1348993 1350871 := bstep (se 1 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 1350871 = 2026307) B2026307
theorem B1350891 : Blo 1348993 1350891 := bstep (se 1 (by rfl) ⟨1013168, by rfl⟩ : syracuseStep 1350891 = 2026337) B2026337
theorem B1350903 : Blo 1348993 1350903 := bstep (se 1 (by rfl) ⟨1013177, by rfl⟩ : syracuseStep 1350903 = 2026355) B2026355
theorem B2563339 : Blo 1348993 2563339 := bstep (se 1 (by rfl) ⟨1922504, by rfl⟩ : syracuseStep 2563339 = 3845009) B3845009
theorem B1350923 : Blo 1348993 1350923 := bstep (se 1 (by rfl) ⟨1013192, by rfl⟩ : syracuseStep 1350923 = 2026385) B2026385
theorem B6831377 : Blo 1348993 6831377 := bstep (se 2 (by rfl) ⟨2561766, by rfl⟩ : syracuseStep 6831377 = 5123533) B5123533
theorem B2309399 : Blo 1348993 2309399 := bstep (se 1 (by rfl) ⟨1732049, by rfl⟩ : syracuseStep 2309399 = 3464099) B3464099
theorem B2276633 : Blo 1348993 2276633 := bstep (se 2 (by rfl) ⟨853737, by rfl⟩ : syracuseStep 2276633 = 1707475) B1707475
theorem B3038489 : Blo 1348993 3038489 := bstep (se 2 (by rfl) ⟨1139433, by rfl⟩ : syracuseStep 3038489 = 2278867) B2278867
theorem B1350935 : Blo 1348993 1350935 := bstep (se 1 (by rfl) ⟨1013201, by rfl⟩ : syracuseStep 1350935 = 2026403) B2026403
theorem B1350955 : Blo 1348993 1350955 := bstep (se 1 (by rfl) ⟨1013216, by rfl⟩ : syracuseStep 1350955 = 2026433) B2026433
theorem B4554035 : Blo 1348993 4554035 := bstep (se 1 (by rfl) ⟨3415526, by rfl⟩ : syracuseStep 4554035 = 6831053) B6831053
theorem B1350967 : Blo 1348993 1350967 := bstep (se 1 (by rfl) ⟨1013225, by rfl⟩ : syracuseStep 1350967 = 2026451) B2026451
theorem B1350987 : Blo 1348993 1350987 := bstep (se 1 (by rfl) ⟨1013240, by rfl⟩ : syracuseStep 1350987 = 2026481) B2026481
theorem B3415385 : Blo 1348993 3415385 := bstep (se 2 (by rfl) ⟨1280769, by rfl⟩ : syracuseStep 3415385 = 2561539) B2561539
theorem B3038579 : Blo 1348993 3038579 := bstep (se 1 (by rfl) ⟨2278934, by rfl⟩ : syracuseStep 3038579 = 4557869) B4557869
theorem B2882945 : Blo 1348993 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B3038615 : Blo 1348993 3038615 := bstep (se 1 (by rfl) ⟨2278961, by rfl⟩ : syracuseStep 3038615 = 4557923) B4557923
theorem B2276761 : Blo 1348993 2276761 := bstep (se 2 (by rfl) ⟨853785, by rfl⟩ : syracuseStep 2276761 = 1707571) B1707571
theorem B6831539 : Blo 1348993 6831539 := bstep (se 1 (by rfl) ⟨5123654, by rfl⟩ : syracuseStep 6831539 = 10247309) B10247309
theorem B1367479 : Blo 1348993 1367479 := bstep (se 1 (by rfl) ⟨1025609, by rfl⟩ : syracuseStep 1367479 = 2051219) B2051219
theorem B98557397 : Blo 1348993 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B5127725 : Blo 1348993 5127725 := bstep (se 3 (by rfl) ⟨961448, by rfl⟩ : syracuseStep 5127725 = 1922897) B1922897
theorem B4554305 : Blo 1348993 4554305 := bstep (se 2 (by rfl) ⟨1707864, by rfl⟩ : syracuseStep 4554305 = 3415729) B3415729
theorem B3038795 : Blo 1348993 3038795 := bstep (se 1 (by rfl) ⟨2279096, by rfl⟩ : syracuseStep 3038795 = 4558193) B4558193
theorem B3038849 : Blo 1348993 3038849 := bstep (se 2 (by rfl) ⟨1139568, by rfl⟩ : syracuseStep 3038849 = 2279137) B2279137
theorem B3841739 : Blo 1348993 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B2563787 : Blo 1348993 2563787 := bstep (se 1 (by rfl) ⟨1922840, by rfl⟩ : syracuseStep 2563787 = 3845681) B3845681
theorem B20790989 : Blo 1348993 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B3039065 : Blo 1348993 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B1441643 : Blo 1348993 1441643 := bstep (se 1 (by rfl) ⟨1081232, by rfl⟩ : syracuseStep 1441643 = 2162465) B2162465
theorem B2563969 : Blo 1348993 2563969 := bstep (se 2 (by rfl) ⟨961488, by rfl⟩ : syracuseStep 2563969 = 1922977) B1922977
theorem B3039155 : Blo 1348993 3039155 := bstep (se 1 (by rfl) ⟨2279366, by rfl⟩ : syracuseStep 3039155 = 4558733) B4558733
theorem B2277335 : Blo 1348993 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B3039191 : Blo 1348993 3039191 := bstep (se 1 (by rfl) ⟨2279393, by rfl⟩ : syracuseStep 3039191 = 4558787) B4558787
theorem B7692317 : Blo 1348993 7692317 := bstep (se 3 (by rfl) ⟨1442309, by rfl⟩ : syracuseStep 7692317 = 2884619) B2884619
theorem B2564129 : Blo 1348993 2564129 := bstep (se 2 (by rfl) ⟨961548, by rfl⟩ : syracuseStep 2564129 = 1923097) B1923097
theorem B5472299 : Blo 1348993 5472299 := bstep (se 1 (by rfl) ⟨4104224, by rfl⟩ : syracuseStep 5472299 = 8208449) B8208449
theorem B2162747 : Blo 1348993 2162747 := bstep (se 1 (by rfl) ⟨1622060, by rfl⟩ : syracuseStep 2162747 = 3244121) B3244121
theorem B2023559 : Blo 1348993 2023559 := bstep (se 1 (by rfl) ⟨1517669, by rfl⟩ : syracuseStep 2023559 = 3035339) B3035339
theorem B2023595 : Blo 1348993 2023595 := bstep (se 1 (by rfl) ⟨1517696, by rfl⟩ : syracuseStep 2023595 = 3035393) B3035393
theorem B2023625 : Blo 1348993 2023625 := bstep (se 2 (by rfl) ⟨758859, by rfl⟩ : syracuseStep 2023625 = 1517719) B1517719
theorem B4554953 : Blo 1348993 4554953 := bstep (se 2 (by rfl) ⟨1708107, by rfl⟩ : syracuseStep 4554953 = 3416215) B3416215
theorem B5128393 : Blo 1348993 5128393 := bstep (se 2 (by rfl) ⟨1923147, by rfl⟩ : syracuseStep 5128393 = 3846295) B3846295
theorem B17309969 : Blo 1348993 17309969 := bstep (se 2 (by rfl) ⟨6491238, by rfl⟩ : syracuseStep 17309969 = 12982477) B12982477
theorem B2023739 : Blo 1348993 2023739 := bstep (se 1 (by rfl) ⟨1517804, by rfl⟩ : syracuseStep 2023739 = 3035609) B3035609
theorem B2023799 : Blo 1348993 2023799 := bstep (se 1 (by rfl) ⟨1517849, by rfl⟩ : syracuseStep 2023799 = 3035699) B3035699
theorem B3842423 : Blo 1348993 3842423 := bstep (se 1 (by rfl) ⟨2881817, by rfl⟩ : syracuseStep 3842423 = 5763635) B5763635
theorem B2277767 : Blo 1348993 2277767 := bstep (se 1 (by rfl) ⟨1708325, by rfl⟩ : syracuseStep 2277767 = 3416651) B3416651
theorem B3039623 : Blo 1348993 3039623 := bstep (se 1 (by rfl) ⟨2279717, by rfl⟩ : syracuseStep 3039623 = 4559435) B4559435
theorem B2023823 : Blo 1348993 2023823 := bstep (se 1 (by rfl) ⟨1517867, by rfl⟩ : syracuseStep 2023823 = 3035735) B3035735
theorem B2023865 : Blo 1348993 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B2023943 : Blo 1348993 2023943 := bstep (se 1 (by rfl) ⟨1517957, by rfl⟩ : syracuseStep 2023943 = 3035915) B3035915
theorem B4866571 : Blo 1348993 4866571 := bstep (se 1 (by rfl) ⟨3649928, by rfl⟩ : syracuseStep 4866571 = 7299857) B7299857
theorem B2023979 : Blo 1348993 2023979 := bstep (se 1 (by rfl) ⟨1517984, by rfl⟩ : syracuseStep 2023979 = 3035969) B3035969
theorem B2024009 : Blo 1348993 2024009 := bstep (se 2 (by rfl) ⟨759003, by rfl⟩ : syracuseStep 2024009 = 1518007) B1518007
theorem B4326007 : Blo 1348993 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B2884243 : Blo 1348993 2884243 := bstep (se 1 (by rfl) ⟨2163182, by rfl⟩ : syracuseStep 2884243 = 4326365) B4326365
theorem B2024123 : Blo 1348993 2024123 := bstep (se 1 (by rfl) ⟨1518092, by rfl⟩ : syracuseStep 2024123 = 3036185) B3036185
theorem B7693001 : Blo 1348993 7693001 := bstep (se 2 (by rfl) ⟨2884875, by rfl⟩ : syracuseStep 7693001 = 5769751) B5769751
theorem B2024183 : Blo 1348993 2024183 := bstep (se 1 (by rfl) ⟨1518137, by rfl⟩ : syracuseStep 2024183 = 3036275) B3036275
theorem B3416843 : Blo 1348993 3416843 := bstep (se 1 (by rfl) ⟨2562632, by rfl⟩ : syracuseStep 3416843 = 5125265) B5125265
theorem B2024207 : Blo 1348993 2024207 := bstep (se 1 (by rfl) ⟨1518155, by rfl⟩ : syracuseStep 2024207 = 3036311) B3036311
theorem B2736929 : Blo 1348993 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B2024249 : Blo 1348993 2024249 := bstep (se 2 (by rfl) ⟨759093, by rfl⟩ : syracuseStep 2024249 = 1518187) B1518187
theorem B2024327 : Blo 1348993 2024327 := bstep (se 1 (by rfl) ⟨1518245, by rfl⟩ : syracuseStep 2024327 = 3036491) B3036491
theorem B4555655 : Blo 1348993 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B2024363 : Blo 1348993 2024363 := bstep (se 1 (by rfl) ⟨1518272, by rfl⟩ : syracuseStep 2024363 = 3036545) B3036545
theorem B1369019 : Blo 1348993 1369019 := bstep (se 1 (by rfl) ⟨1026764, by rfl⟩ : syracuseStep 1369019 = 2053529) B2053529
theorem B2024393 : Blo 1348993 2024393 := bstep (se 2 (by rfl) ⟨759147, by rfl⟩ : syracuseStep 2024393 = 1518295) B1518295
theorem B2278415 : Blo 1348993 2278415 := bstep (se 1 (by rfl) ⟨1708811, by rfl⟩ : syracuseStep 2278415 = 3417623) B3417623
theorem B2024507 : Blo 1348993 2024507 := bstep (se 1 (by rfl) ⟨1518380, by rfl⟩ : syracuseStep 2024507 = 3036761) B3036761
theorem B15377525 : Blo 1348993 15377525 := bstep (se 5 (by rfl) ⟨720821, by rfl⟩ : syracuseStep 15377525 = 1441643) B1441643
theorem B2024567 : Blo 1348993 2024567 := bstep (se 1 (by rfl) ⟨1518425, by rfl⟩ : syracuseStep 2024567 = 3036851) B3036851
theorem B2024591 : Blo 1348993 2024591 := bstep (se 1 (by rfl) ⟨1518443, by rfl⟩ : syracuseStep 2024591 = 3036887) B3036887
theorem B2024633 : Blo 1348993 2024633 := bstep (se 2 (by rfl) ⟨759237, by rfl⟩ : syracuseStep 2024633 = 1518475) B1518475
theorem B39437549 : Blo 1348993 39437549 := bstep (se 3 (by rfl) ⟨7394540, by rfl⟩ : syracuseStep 39437549 = 14789081) B14789081
theorem B6161645 : Blo 1348993 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B4556033 : Blo 1348993 4556033 := bstep (se 2 (by rfl) ⟨1708512, by rfl⟩ : syracuseStep 4556033 = 3417025) B3417025
theorem B2024711 : Blo 1348993 2024711 := bstep (se 1 (by rfl) ⟨1518533, by rfl⟩ : syracuseStep 2024711 = 3037067) B3037067
theorem B2024747 : Blo 1348993 2024747 := bstep (se 1 (by rfl) ⟨1518560, by rfl⟩ : syracuseStep 2024747 = 3037121) B3037121
theorem B6489395 : Blo 1348993 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B2024777 : Blo 1348993 2024777 := bstep (se 2 (by rfl) ⟨759291, by rfl⟩ : syracuseStep 2024777 = 1518583) B1518583
theorem B8652167 : Blo 1348993 8652167 := bstep (se 1 (by rfl) ⟨6489125, by rfl⟩ : syracuseStep 8652167 = 12978251) B12978251
theorem B2434439 : Blo 1348993 2434439 := bstep (se 1 (by rfl) ⟨1825829, by rfl⟩ : syracuseStep 2434439 = 3651659) B3651659
theorem B8209811 : Blo 1348993 8209811 := bstep (se 1 (by rfl) ⟨6157358, by rfl⟩ : syracuseStep 8209811 = 12314717) B12314717
theorem B3417491 : Blo 1348993 3417491 := bstep (se 1 (by rfl) ⟨2563118, by rfl⟩ : syracuseStep 3417491 = 5126237) B5126237
theorem B8652217 : Blo 1348993 8652217 := bstep (se 2 (by rfl) ⟨3244581, by rfl⟩ : syracuseStep 8652217 = 6489163) B6489163
theorem B2024891 : Blo 1348993 2024891 := bstep (se 1 (by rfl) ⟨1518668, by rfl⟩ : syracuseStep 2024891 = 3037337) B3037337
theorem B2024951 : Blo 1348993 2024951 := bstep (se 1 (by rfl) ⟨1518713, by rfl⟩ : syracuseStep 2024951 = 3037427) B3037427
theorem B2024975 : Blo 1348993 2024975 := bstep (se 1 (by rfl) ⟨1518731, by rfl⟩ : syracuseStep 2024975 = 3037463) B3037463
theorem B2278955 : Blo 1348993 2278955 := bstep (se 1 (by rfl) ⟨1709216, by rfl⟩ : syracuseStep 2278955 = 3418433) B3418433
theorem B3245611 : Blo 1348993 3245611 := bstep (se 1 (by rfl) ⟨2434208, by rfl⟩ : syracuseStep 3245611 = 4868417) B4868417
theorem B2025017 : Blo 1348993 2025017 := bstep (se 2 (by rfl) ⟨759381, by rfl⟩ : syracuseStep 2025017 = 1518763) B1518763
theorem B8767043 : Blo 1348993 8767043 := bstep (se 1 (by rfl) ⟨6575282, by rfl⟩ : syracuseStep 8767043 = 13150565) B13150565
theorem B2025095 : Blo 1348993 2025095 := bstep (se 1 (by rfl) ⟨1518821, by rfl⟩ : syracuseStep 2025095 = 3037643) B3037643
theorem B2025131 : Blo 1348993 2025131 := bstep (se 1 (by rfl) ⟨1518848, by rfl⟩ : syracuseStep 2025131 = 3037697) B3037697
theorem B3417785 : Blo 1348993 3417785 := bstep (se 2 (by rfl) ⟨1281669, by rfl⟩ : syracuseStep 3417785 = 2563339) B2563339
theorem B2025161 : Blo 1348993 2025161 := bstep (se 2 (by rfl) ⟨759435, by rfl⟩ : syracuseStep 2025161 = 1518871) B1518871
theorem B2025275 : Blo 1348993 2025275 := bstep (se 1 (by rfl) ⟨1518956, by rfl⟩ : syracuseStep 2025275 = 3037913) B3037913
theorem B4867955 : Blo 1348993 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B2025335 : Blo 1348993 2025335 := bstep (se 1 (by rfl) ⟨1519001, by rfl⟩ : syracuseStep 2025335 = 3038003) B3038003
theorem B2025359 : Blo 1348993 2025359 := bstep (se 1 (by rfl) ⟨1519019, by rfl⟩ : syracuseStep 2025359 = 3038039) B3038039
theorem B5474195 : Blo 1348993 5474195 := bstep (se 1 (by rfl) ⟨4105646, by rfl⟩ : syracuseStep 5474195 = 8211293) B8211293
theorem B2025401 : Blo 1348993 2025401 := bstep (se 2 (by rfl) ⟨759525, by rfl⟩ : syracuseStep 2025401 = 1519051) B1519051
theorem B2279353 : Blo 1348993 2279353 := bstep (se 2 (by rfl) ⟨854757, by rfl⟩ : syracuseStep 2279353 = 1709515) B1709515
theorem B2025479 : Blo 1348993 2025479 := bstep (se 1 (by rfl) ⟨1519109, by rfl⟩ : syracuseStep 2025479 = 3038219) B3038219
theorem B4556843 : Blo 1348993 4556843 := bstep (se 1 (by rfl) ⟨3417632, by rfl⟩ : syracuseStep 4556843 = 6835265) B6835265
theorem B2025515 : Blo 1348993 2025515 := bstep (se 1 (by rfl) ⟨1519136, by rfl⟩ : syracuseStep 2025515 = 3038273) B3038273
theorem B7686211 : Blo 1348993 7686211 := bstep (se 1 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 7686211 = 11529317) B11529317
theorem B2025545 : Blo 1348993 2025545 := bstep (se 2 (by rfl) ⟨759579, by rfl⟩ : syracuseStep 2025545 = 1519159) B1519159
theorem B1517755 : Blo 1348993 1517755 := bstep (se 1 (by rfl) ⟨1138316, by rfl⟩ : syracuseStep 1517755 = 2276633) B2276633
theorem B2025659 : Blo 1348993 2025659 := bstep (se 1 (by rfl) ⟨1519244, by rfl⟩ : syracuseStep 2025659 = 3038489) B3038489
theorem B2025719 : Blo 1348993 2025719 := bstep (se 1 (by rfl) ⟨1519289, by rfl⟩ : syracuseStep 2025719 = 3038579) B3038579
theorem B2025743 : Blo 1348993 2025743 := bstep (se 1 (by rfl) ⟨1519307, by rfl⟩ : syracuseStep 2025743 = 3038615) B3038615
theorem B2025785 : Blo 1348993 2025785 := bstep (se 2 (by rfl) ⟨759669, by rfl⟩ : syracuseStep 2025785 = 1519339) B1519339
theorem B3418483 : Blo 1348993 3418483 := bstep (se 1 (by rfl) ⟨2563862, by rfl⟩ : syracuseStep 3418483 = 5127725) B5127725
theorem B2025863 : Blo 1348993 2025863 := bstep (se 1 (by rfl) ⟨1519397, by rfl⟩ : syracuseStep 2025863 = 3038795) B3038795
theorem B2025899 : Blo 1348993 2025899 := bstep (se 1 (by rfl) ⟨1519424, by rfl⟩ : syracuseStep 2025899 = 3038849) B3038849
theorem B6834617 : Blo 1348993 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B2025929 : Blo 1348993 2025929 := bstep (se 2 (by rfl) ⟨759723, by rfl⟩ : syracuseStep 2025929 = 1519447) B1519447
theorem B3418625 : Blo 1348993 3418625 := bstep (se 2 (by rfl) ⟨1281984, by rfl⟩ : syracuseStep 3418625 = 2563969) B2563969
theorem B10258973 : Blo 1348993 10258973 := bstep (se 3 (by rfl) ⟨1923557, by rfl⟩ : syracuseStep 10258973 = 3847115) B3847115
theorem B2026043 : Blo 1348993 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B14805605 : Blo 1348993 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B2026103 : Blo 1348993 2026103 := bstep (se 1 (by rfl) ⟨1519577, by rfl⟩ : syracuseStep 2026103 = 3039155) B3039155
theorem B1518223 : Blo 1348993 1518223 := bstep (se 1 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 1518223 = 2277335) B2277335
theorem B2026127 : Blo 1348993 2026127 := bstep (se 1 (by rfl) ⟨1519595, by rfl⟩ : syracuseStep 2026127 = 3039191) B3039191
theorem B2026169 : Blo 1348993 2026169 := bstep (se 2 (by rfl) ⟨759813, by rfl⟩ : syracuseStep 2026169 = 1519627) B1519627
theorem B2026247 : Blo 1348993 2026247 := bstep (se 1 (by rfl) ⟨1519685, by rfl⟩ : syracuseStep 2026247 = 3039371) B3039371
theorem B12315407 : Blo 1348993 12315407 := bstep (se 1 (by rfl) ⟨9236555, by rfl⟩ : syracuseStep 12315407 = 18473111) B18473111
theorem B2026283 : Blo 1348993 2026283 := bstep (se 1 (by rfl) ⟨1519712, by rfl⟩ : syracuseStep 2026283 = 3039425) B3039425
theorem B2026313 : Blo 1348993 2026313 := bstep (se 2 (by rfl) ⟨759867, by rfl⟩ : syracuseStep 2026313 = 1519735) B1519735
theorem B11537315 : Blo 1348993 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B2026427 : Blo 1348993 2026427 := bstep (se 1 (by rfl) ⟨1519820, by rfl⟩ : syracuseStep 2026427 = 3039641) B3039641
theorem B3845065 : Blo 1348993 3845065 := bstep (se 2 (by rfl) ⟨1441899, by rfl⟩ : syracuseStep 3845065 = 2883799) B2883799
theorem B3419081 : Blo 1348993 3419081 := bstep (se 2 (by rfl) ⟨1282155, by rfl⟩ : syracuseStep 3419081 = 2564311) B2564311
theorem B2026487 : Blo 1348993 2026487 := bstep (se 1 (by rfl) ⟨1519865, by rfl⟩ : syracuseStep 2026487 = 3039731) B3039731
theorem B17304637 : Blo 1348993 17304637 := bstep (se 3 (by rfl) ⟨3244619, by rfl⟩ : syracuseStep 17304637 = 6489239) B6489239
theorem B1518727 : Blo 1348993 1518727 := bstep (se 1 (by rfl) ⟨1139045, by rfl⟩ : syracuseStep 1518727 = 2278091) B2278091
theorem B4107449 : Blo 1348993 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B6491393 : Blo 1348993 6491393 := bstep (se 2 (by rfl) ⟨2434272, by rfl⟩ : syracuseStep 6491393 = 4868545) B4868545
theorem B3419435 : Blo 1348993 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B1518907 : Blo 1348993 1518907 := bstep (se 1 (by rfl) ⟨1139180, by rfl⟩ : syracuseStep 1518907 = 2278361) B2278361
theorem B4558139 : Blo 1348993 4558139 := bstep (se 1 (by rfl) ⟨3418604, by rfl⟩ : syracuseStep 4558139 = 6837209) B6837209
theorem B6835913 : Blo 1348993 6835913 := bstep (se 2 (by rfl) ⟨2563467, by rfl⟩ : syracuseStep 6835913 = 5126935) B5126935
theorem B1519375 : Blo 1348993 1519375 := bstep (se 1 (by rfl) ⟨1139531, by rfl⟩ : syracuseStep 1519375 = 2279063) B2279063
theorem B4558625 : Blo 1348993 4558625 := bstep (se 2 (by rfl) ⟨1709484, by rfl⟩ : syracuseStep 4558625 = 3418969) B3418969
theorem B1707895 : Blo 1348993 1707895 := bstep (se 1 (by rfl) ⟨1280921, by rfl⟩ : syracuseStep 1707895 = 2561843) B2561843
theorem B5762951 : Blo 1348993 5762951 := bstep (se 1 (by rfl) ⟨4322213, by rfl⟩ : syracuseStep 5762951 = 8644427) B8644427
theorem B7401401 : Blo 1348993 7401401 := bstep (se 2 (by rfl) ⟨2775525, by rfl⟩ : syracuseStep 7401401 = 5551051) B5551051
theorem B7688195 : Blo 1348993 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B2773111 : Blo 1348993 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B3035321 : Blo 1348993 3035321 := bstep (se 2 (by rfl) ⟨1138245, by rfl⟩ : syracuseStep 3035321 = 2276491) B2276491
theorem B1708219 : Blo 1348993 1708219 := bstep (se 1 (by rfl) ⟨1281164, by rfl⟩ : syracuseStep 1708219 = 2562329) B2562329
theorem B6484205 : Blo 1348993 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B4559219 : Blo 1348993 4559219 := bstep (se 1 (by rfl) ⟨3419414, by rfl⟩ : syracuseStep 4559219 = 6838829) B6838829
theorem B14586257 : Blo 1348993 14586257 := bstep (se 2 (by rfl) ⟨5469846, by rfl⟩ : syracuseStep 14586257 = 10939693) B10939693
theorem B5124505 : Blo 1348993 5124505 := bstep (se 2 (by rfl) ⟨1921689, by rfl⟩ : syracuseStep 5124505 = 3843379) B3843379
theorem B20787677 : Blo 1348993 20787677 := bstep (se 3 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 20787677 = 7795379) B7795379
theorem B3035663 : Blo 1348993 3035663 := bstep (se 1 (by rfl) ⟨2276747, by rfl⟩ : syracuseStep 3035663 = 4553495) B4553495
theorem B3035681 : Blo 1348993 3035681 := bstep (se 2 (by rfl) ⟨1138380, by rfl⟩ : syracuseStep 3035681 = 2276761) B2276761
theorem B3895867 : Blo 1348993 3895867 := bstep (se 1 (by rfl) ⟨2921900, by rfl⟩ : syracuseStep 3895867 = 5843801) B5843801
theorem B1823305 : Blo 1348993 1823305 := bstep (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) B1367479
theorem B1708715 : Blo 1348993 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B5124809 : Blo 1348993 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B3846923 : Blo 1348993 3846923 := bstep (se 1 (by rfl) ⟨2885192, by rfl⟩ : syracuseStep 3846923 = 5770385) B5770385
theorem B10244879 : Blo 1348993 10244879 := bstep (se 1 (by rfl) ⟨7683659, by rfl⟩ : syracuseStep 10244879 = 15367319) B15367319
theorem B3036023 : Blo 1348993 3036023 := bstep (se 1 (by rfl) ⟨2277017, by rfl⟩ : syracuseStep 3036023 = 4554035) B4554035
theorem B1921963 : Blo 1348993 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B65704931 : Blo 1348993 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B3036203 : Blo 1348993 3036203 := bstep (se 1 (by rfl) ⟨2277152, by rfl⟩ : syracuseStep 3036203 = 4554305) B4554305
theorem B2561159 : Blo 1348993 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B1709191 : Blo 1348993 1709191 := bstep (se 1 (by rfl) ⟨1281893, by rfl⟩ : syracuseStep 1709191 = 2563787) B2563787
theorem B5764385 : Blo 1348993 5764385 := bstep (se 2 (by rfl) ⟨2161644, by rfl⟩ : syracuseStep 5764385 = 4323289) B4323289
theorem B10253627 : Blo 1348993 10253627 := bstep (se 1 (by rfl) ⟨7690220, by rfl⟩ : syracuseStep 10253627 = 15380441) B15380441
theorem B12973405 : Blo 1348993 12973405 := bstep (se 3 (by rfl) ⟨2432513, by rfl⟩ : syracuseStep 12973405 = 4865027) B4865027
theorem B1348999 : Blo 1348993 1348999 := bstep (se 1 (by rfl) ⟨1011749, by rfl⟩ : syracuseStep 1348999 = 2023499) B2023499
theorem B12965255 : Blo 1348993 12965255 := bstep (se 1 (by rfl) ⟨9723941, by rfl⟩ : syracuseStep 12965255 = 19447883) B19447883
theorem B13849991 : Blo 1348993 13849991 := bstep (se 1 (by rfl) ⟨10387493, by rfl⟩ : syracuseStep 13849991 = 20774987) B20774987
theorem B1349007 : Blo 1348993 1349007 := bstep (se 1 (by rfl) ⟨1011755, by rfl⟩ : syracuseStep 1349007 = 2023511) B2023511
theorem B3036563 : Blo 1348993 3036563 := bstep (se 1 (by rfl) ⟨2277422, by rfl⟩ : syracuseStep 3036563 = 4554845) B4554845
theorem B31167929 : Blo 1348993 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B1349051 : Blo 1348993 1349051 := bstep (se 1 (by rfl) ⟨1011788, by rfl⟩ : syracuseStep 1349051 = 2023577) B2023577
theorem B3036617 : Blo 1348993 3036617 := bstep (se 2 (by rfl) ⟨1138731, by rfl⟩ : syracuseStep 3036617 = 2277463) B2277463
theorem B1349127 : Blo 1348993 1349127 := bstep (se 1 (by rfl) ⟨1011845, by rfl⟩ : syracuseStep 1349127 = 2023691) B2023691
theorem B1349135 : Blo 1348993 1349135 := bstep (se 1 (by rfl) ⟨1011851, by rfl⟩ : syracuseStep 1349135 = 2023703) B2023703
theorem B1349179 : Blo 1348993 1349179 := bstep (se 1 (by rfl) ⟨1011884, by rfl⟩ : syracuseStep 1349179 = 2023769) B2023769
theorem B5125751 : Blo 1348993 5125751 := bstep (se 1 (by rfl) ⟨3844313, by rfl⟩ : syracuseStep 5125751 = 7688627) B7688627
theorem B1709687 : Blo 1348993 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B1349255 : Blo 1348993 1349255 := bstep (se 1 (by rfl) ⟨1011941, by rfl⟩ : syracuseStep 1349255 = 2023883) B2023883
theorem B1349263 : Blo 1348993 1349263 := bstep (se 1 (by rfl) ⟨1011947, by rfl⟩ : syracuseStep 1349263 = 2023895) B2023895
theorem B1349307 : Blo 1348993 1349307 := bstep (se 1 (by rfl) ⟨1011980, by rfl⟩ : syracuseStep 1349307 = 2023961) B2023961
theorem B1349383 : Blo 1348993 1349383 := bstep (se 1 (by rfl) ⟨1012037, by rfl⟩ : syracuseStep 1349383 = 2024075) B2024075
theorem B1349391 : Blo 1348993 1349391 := bstep (se 1 (by rfl) ⟨1012043, by rfl⟩ : syracuseStep 1349391 = 2024087) B2024087
theorem B1709839 : Blo 1348993 1709839 := bstep (se 1 (by rfl) ⟨1282379, by rfl⟩ : syracuseStep 1709839 = 2564759) B2564759
theorem B1349435 : Blo 1348993 1349435 := bstep (se 1 (by rfl) ⟨1012076, by rfl⟩ : syracuseStep 1349435 = 2024153) B2024153
theorem B1349511 : Blo 1348993 1349511 := bstep (se 1 (by rfl) ⟨1012133, by rfl⟩ : syracuseStep 1349511 = 2024267) B2024267
theorem B3700615 : Blo 1348993 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B1349519 : Blo 1348993 1349519 := bstep (se 1 (by rfl) ⟨1012139, by rfl⟩ : syracuseStep 1349519 = 2024279) B2024279
theorem B5339033 : Blo 1348993 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B12982169 : Blo 1348993 12982169 := bstep (se 2 (by rfl) ⟨4868313, by rfl⟩ : syracuseStep 12982169 = 9736627) B9736627
theorem B1349563 : Blo 1348993 1349563 := bstep (se 1 (by rfl) ⟨1012172, by rfl⟩ : syracuseStep 1349563 = 2024345) B2024345
theorem B2054089 : Blo 1348993 2054089 := bstep (se 2 (by rfl) ⟨770283, by rfl⟩ : syracuseStep 2054089 = 1540567) B1540567
theorem B1349639 : Blo 1348993 1349639 := bstep (se 1 (by rfl) ⟨1012229, by rfl⟩ : syracuseStep 1349639 = 2024459) B2024459
theorem B1349647 : Blo 1348993 1349647 := bstep (se 1 (by rfl) ⟨1012235, by rfl⟩ : syracuseStep 1349647 = 2024471) B2024471
theorem B1849387 : Blo 1348993 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B2881595 : Blo 1348993 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B1349691 : Blo 1348993 1349691 := bstep (se 1 (by rfl) ⟨1012268, by rfl⟩ : syracuseStep 1349691 = 2024537) B2024537
theorem B1349767 : Blo 1348993 1349767 := bstep (se 1 (by rfl) ⟨1012325, by rfl⟩ : syracuseStep 1349767 = 2024651) B2024651
theorem B3037319 : Blo 1348993 3037319 := bstep (se 1 (by rfl) ⟨2277989, by rfl⟩ : syracuseStep 3037319 = 4555979) B4555979
theorem B1349775 : Blo 1348993 1349775 := bstep (se 1 (by rfl) ⟨1012331, by rfl⟩ : syracuseStep 1349775 = 2024663) B2024663
theorem B1349819 : Blo 1348993 1349819 := bstep (se 1 (by rfl) ⟨1012364, by rfl⟩ : syracuseStep 1349819 = 2024729) B2024729
theorem B24959177 : Blo 1348993 24959177 := bstep (se 2 (by rfl) ⟨9359691, by rfl⟩ : syracuseStep 24959177 = 18719383) B18719383
theorem B5765377 : Blo 1348993 5765377 := bstep (se 2 (by rfl) ⟨2162016, by rfl⟩ : syracuseStep 5765377 = 4324033) B4324033
theorem B1349895 : Blo 1348993 1349895 := bstep (se 1 (by rfl) ⟨1012421, by rfl⟩ : syracuseStep 1349895 = 2024843) B2024843
theorem B1349903 : Blo 1348993 1349903 := bstep (se 1 (by rfl) ⟨1012427, by rfl⟩ : syracuseStep 1349903 = 2024855) B2024855
theorem B15374609 : Blo 1348993 15374609 := bstep (se 2 (by rfl) ⟨5765478, by rfl⟩ : syracuseStep 15374609 = 11530957) B11530957
theorem B1349947 : Blo 1348993 1349947 := bstep (se 1 (by rfl) ⟨1012460, by rfl⟩ : syracuseStep 1349947 = 2024921) B2024921
theorem B3037499 : Blo 1348993 3037499 := bstep (se 1 (by rfl) ⟨2278124, by rfl⟩ : syracuseStep 3037499 = 4556249) B4556249
theorem B7690585 : Blo 1348993 7690585 := bstep (se 2 (by rfl) ⟨2883969, by rfl⟩ : syracuseStep 7690585 = 5767939) B5767939
theorem B1350023 : Blo 1348993 1350023 := bstep (se 1 (by rfl) ⟨1012517, by rfl⟩ : syracuseStep 1350023 = 2025035) B2025035
theorem B1350031 : Blo 1348993 1350031 := bstep (se 1 (by rfl) ⟨1012523, by rfl⟩ : syracuseStep 1350031 = 2025047) B2025047
theorem B2161081 : Blo 1348993 2161081 := bstep (se 2 (by rfl) ⟨810405, by rfl⟩ : syracuseStep 2161081 = 1620811) B1620811
theorem B3037625 : Blo 1348993 3037625 := bstep (se 2 (by rfl) ⟨1139109, by rfl⟩ : syracuseStep 3037625 = 2278219) B2278219
theorem B1350075 : Blo 1348993 1350075 := bstep (se 1 (by rfl) ⟨1012556, by rfl⟩ : syracuseStep 1350075 = 2025113) B2025113
theorem B1350151 : Blo 1348993 1350151 := bstep (se 1 (by rfl) ⟨1012613, by rfl⟩ : syracuseStep 1350151 = 2025227) B2025227
theorem B1350159 : Blo 1348993 1350159 := bstep (se 1 (by rfl) ⟨1012619, by rfl⟩ : syracuseStep 1350159 = 2025239) B2025239
theorem B6486551 : Blo 1348993 6486551 := bstep (se 1 (by rfl) ⟨4864913, by rfl⟩ : syracuseStep 6486551 = 9729827) B9729827
theorem B3422753 : Blo 1348993 3422753 := bstep (se 2 (by rfl) ⟨1283532, by rfl⟩ : syracuseStep 3422753 = 2567065) B2567065
theorem B1350203 : Blo 1348993 1350203 := bstep (se 1 (by rfl) ⟨1012652, by rfl⟩ : syracuseStep 1350203 = 2025305) B2025305
theorem B5126723 : Blo 1348993 5126723 := bstep (se 1 (by rfl) ⟨3845042, by rfl⟩ : syracuseStep 5126723 = 7690085) B7690085
theorem B1350279 : Blo 1348993 1350279 := bstep (se 1 (by rfl) ⟨1012709, by rfl⟩ : syracuseStep 1350279 = 2025419) B2025419
theorem B1350287 : Blo 1348993 1350287 := bstep (se 1 (by rfl) ⟨1012715, by rfl⟩ : syracuseStep 1350287 = 2025431) B2025431
theorem B2161337 : Blo 1348993 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B1350331 : Blo 1348993 1350331 := bstep (se 1 (by rfl) ⟨1012748, by rfl⟩ : syracuseStep 1350331 = 2025497) B2025497
theorem B4864769 : Blo 1348993 4864769 := bstep (se 2 (by rfl) ⟨1824288, by rfl⟩ : syracuseStep 4864769 = 3648577) B3648577
theorem B1350407 : Blo 1348993 1350407 := bstep (se 1 (by rfl) ⟨1012805, by rfl⟩ : syracuseStep 1350407 = 2025611) B2025611
theorem B3242767 : Blo 1348993 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B3037967 : Blo 1348993 3037967 := bstep (se 1 (by rfl) ⟨2278475, by rfl⟩ : syracuseStep 3037967 = 4556951) B4556951
theorem B1350415 : Blo 1348993 1350415 := bstep (se 1 (by rfl) ⟨1012811, by rfl⟩ : syracuseStep 1350415 = 2025623) B2025623
theorem B3037985 : Blo 1348993 3037985 := bstep (se 2 (by rfl) ⟨1139244, by rfl⟩ : syracuseStep 3037985 = 2278489) B2278489
theorem B16431923 : Blo 1348993 16431923 := bstep (se 1 (by rfl) ⟨12323942, by rfl⟩ : syracuseStep 16431923 = 24647885) B24647885
theorem B2030393 : Blo 1348993 2030393 := bstep (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) B1522795
theorem B1350459 : Blo 1348993 1350459 := bstep (se 1 (by rfl) ⟨1012844, by rfl⟩ : syracuseStep 1350459 = 2025689) B2025689
theorem B3414899 : Blo 1348993 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B3414919 : Blo 1348993 3414919 := bstep (se 1 (by rfl) ⟨2561189, by rfl⟩ : syracuseStep 3414919 = 5122379) B5122379
theorem B1350535 : Blo 1348993 1350535 := bstep (se 1 (by rfl) ⟨1012901, by rfl⟩ : syracuseStep 1350535 = 2025803) B2025803
theorem B1350543 : Blo 1348993 1350543 := bstep (se 1 (by rfl) ⟨1012907, by rfl⟩ : syracuseStep 1350543 = 2025815) B2025815
theorem B4553657 : Blo 1348993 4553657 := bstep (se 2 (by rfl) ⟨1707621, by rfl⟩ : syracuseStep 4553657 = 3415243) B3415243
theorem B1350587 : Blo 1348993 1350587 := bstep (se 1 (by rfl) ⟨1012940, by rfl⟩ : syracuseStep 1350587 = 2025881) B2025881
theorem B1350663 : Blo 1348993 1350663 := bstep (se 1 (by rfl) ⟨1012997, by rfl⟩ : syracuseStep 1350663 = 2025995) B2025995
theorem B1350671 : Blo 1348993 1350671 := bstep (se 1 (by rfl) ⟨1013003, by rfl⟩ : syracuseStep 1350671 = 2026007) B2026007
theorem B2882603 : Blo 1348993 2882603 := bstep (se 1 (by rfl) ⟨2161952, by rfl⟩ : syracuseStep 2882603 = 4323905) B4323905
theorem B1350715 : Blo 1348993 1350715 := bstep (se 1 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 1350715 = 2026073) B2026073
theorem B2276471 : Blo 1348993 2276471 := bstep (se 1 (by rfl) ⟨1707353, by rfl⟩ : syracuseStep 2276471 = 3414707) B3414707
theorem B3038327 : Blo 1348993 3038327 := bstep (se 1 (by rfl) ⟨2278745, by rfl⟩ : syracuseStep 3038327 = 4557491) B4557491
theorem B2161799 : Blo 1348993 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B1350791 : Blo 1348993 1350791 := bstep (se 1 (by rfl) ⟨1013093, by rfl⟩ : syracuseStep 1350791 = 2026187) B2026187
theorem B1350799 : Blo 1348993 1350799 := bstep (se 1 (by rfl) ⟨1013099, by rfl⟩ : syracuseStep 1350799 = 2026199) B2026199
theorem B3415193 : Blo 1348993 3415193 := bstep (se 2 (by rfl) ⟨1280697, by rfl⟩ : syracuseStep 3415193 = 2561395) B2561395
theorem B1350843 : Blo 1348993 1350843 := bstep (se 1 (by rfl) ⟨1013132, by rfl⟩ : syracuseStep 1350843 = 2026265) B2026265
theorem B1350919 : Blo 1348993 1350919 := bstep (se 1 (by rfl) ⟨1013189, by rfl⟩ : syracuseStep 1350919 = 2026379) B2026379
theorem B1350927 : Blo 1348993 1350927 := bstep (se 1 (by rfl) ⟨1013195, by rfl⟩ : syracuseStep 1350927 = 2026391) B2026391
theorem B3038507 : Blo 1348993 3038507 := bstep (se 1 (by rfl) ⟨2278880, by rfl⟩ : syracuseStep 3038507 = 4557761) B4557761
theorem B3415355 : Blo 1348993 3415355 := bstep (se 1 (by rfl) ⟨2561516, by rfl⟩ : syracuseStep 3415355 = 5123033) B5123033
theorem B1350971 : Blo 1348993 1350971 := bstep (se 1 (by rfl) ⟨1013228, by rfl⟩ : syracuseStep 1350971 = 2026457) B2026457
theorem B4554251 : Blo 1348993 4554251 := bstep (se 1 (by rfl) ⟨3415688, by rfl⟩ : syracuseStep 4554251 = 6831377) B6831377
theorem B3415567 : Blo 1348993 3415567 := bstep (se 1 (by rfl) ⟨2561675, by rfl⟩ : syracuseStep 3415567 = 5123351) B5123351
theorem B1539599 : Blo 1348993 1539599 := bstep (se 1 (by rfl) ⟨1154699, by rfl⟩ : syracuseStep 1539599 = 2309399) B2309399
theorem B7118365 : Blo 1348993 7118365 := bstep (se 3 (by rfl) ⟨1334693, by rfl⟩ : syracuseStep 7118365 = 2669387) B2669387
theorem B2080313 : Blo 1348993 2080313 := bstep (se 2 (by rfl) ⟨780117, by rfl⟩ : syracuseStep 2080313 = 1560235) B1560235
theorem B2596411 : Blo 1348993 2596411 := bstep (se 1 (by rfl) ⟨1947308, by rfl⟩ : syracuseStep 2596411 = 3894617) B3894617
theorem B2276923 : Blo 1348993 2276923 := bstep (se 1 (by rfl) ⟨1707692, by rfl⟩ : syracuseStep 2276923 = 3415385) B3415385
theorem B2563643 : Blo 1348993 2563643 := bstep (se 1 (by rfl) ⟨1922732, by rfl⟩ : syracuseStep 2563643 = 3845465) B3845465
theorem B4554359 : Blo 1348993 4554359 := bstep (se 1 (by rfl) ⟨3415769, by rfl⟩ : syracuseStep 4554359 = 6831539) B6831539
theorem B3038867 : Blo 1348993 3038867 := bstep (se 1 (by rfl) ⟨2279150, by rfl⟩ : syracuseStep 3038867 = 4558301) B4558301
theorem B2277065 : Blo 1348993 2277065 := bstep (se 2 (by rfl) ⟨853899, by rfl⟩ : syracuseStep 2277065 = 1707799) B1707799
theorem B3038921 : Blo 1348993 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B7683821 : Blo 1348993 7683821 := bstep (se 3 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 7683821 = 2881433) B2881433
theorem B3415841 : Blo 1348993 3415841 := bstep (se 2 (by rfl) ⟨1280940, by rfl⟩ : syracuseStep 3415841 = 2561881) B2561881
theorem B12967715 : Blo 1348993 12967715 := bstep (se 1 (by rfl) ⟨9725786, by rfl⟩ : syracuseStep 12967715 = 19451573) B19451573
theorem B13860659 : Blo 1348993 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B6832025 : Blo 1348993 6832025 := bstep (se 2 (by rfl) ⟨2562009, by rfl⟩ : syracuseStep 6832025 = 5124019) B5124019
theorem B4104137 : Blo 1348993 4104137 := bstep (se 2 (by rfl) ⟨1539051, by rfl⟩ : syracuseStep 4104137 = 3078103) B3078103
theorem B5128211 : Blo 1348993 5128211 := bstep (se 1 (by rfl) ⟨3846158, by rfl⟩ : syracuseStep 5128211 = 7692317) B7692317
theorem B2465849 : Blo 1348993 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B10248281 : Blo 1348993 10248281 := bstep (se 2 (by rfl) ⟨3843105, by rfl⟩ : syracuseStep 10248281 = 7686211) B7686211
theorem B2023547 : Blo 1348993 2023547 := bstep (se 1 (by rfl) ⟨1517660, by rfl⟩ : syracuseStep 2023547 = 3035321) B3035321
theorem B7684253 : Blo 1348993 7684253 := bstep (se 3 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 7684253 = 2881595) B2881595
theorem B5767325 : Blo 1348993 5767325 := bstep (se 3 (by rfl) ⟨1081373, by rfl⟩ : syracuseStep 5767325 = 2162747) B2162747
theorem B3039479 : Blo 1348993 3039479 := bstep (se 1 (by rfl) ⟨2279609, by rfl⟩ : syracuseStep 3039479 = 4559219) B4559219
theorem B2023673 : Blo 1348993 2023673 := bstep (se 2 (by rfl) ⟨758877, by rfl⟩ : syracuseStep 2023673 = 1517755) B1517755
theorem B2277625 : Blo 1348993 2277625 := bstep (se 2 (by rfl) ⟨854109, by rfl⟩ : syracuseStep 2277625 = 1708219) B1708219
theorem B2023775 : Blo 1348993 2023775 := bstep (se 1 (by rfl) ⟨1517831, by rfl⟩ : syracuseStep 2023775 = 3035663) B3035663
theorem B2023787 : Blo 1348993 2023787 := bstep (se 1 (by rfl) ⟨1517840, by rfl⟩ : syracuseStep 2023787 = 3035681) B3035681
theorem B3416539 : Blo 1348993 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B5128667 : Blo 1348993 5128667 := bstep (se 1 (by rfl) ⟨3846500, by rfl⟩ : syracuseStep 5128667 = 7693001) B7693001
theorem B2277895 : Blo 1348993 2277895 := bstep (se 1 (by rfl) ⟨1708421, by rfl⟩ : syracuseStep 2277895 = 3416843) B3416843
theorem B2564615 : Blo 1348993 2564615 := bstep (se 1 (by rfl) ⟨1923461, by rfl⟩ : syracuseStep 2564615 = 3846923) B3846923
theorem B6832673 : Blo 1348993 6832673 := bstep (se 2 (by rfl) ⟨2562252, by rfl⟩ : syracuseStep 6832673 = 5124505) B5124505
theorem B2024015 : Blo 1348993 2024015 := bstep (se 1 (by rfl) ⟨1518011, by rfl⟩ : syracuseStep 2024015 = 3036023) B3036023
theorem B43803287 : Blo 1348993 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B6488761 : Blo 1348993 6488761 := bstep (se 2 (by rfl) ⟨2433285, by rfl⟩ : syracuseStep 6488761 = 4866571) B4866571
theorem B2024135 : Blo 1348993 2024135 := bstep (se 1 (by rfl) ⟨1518101, by rfl⟩ : syracuseStep 2024135 = 3036203) B3036203
theorem B5194489 : Blo 1348993 5194489 := bstep (se 2 (by rfl) ⟨1947933, by rfl⟩ : syracuseStep 5194489 = 3895867) B3895867
theorem B5768009 : Blo 1348993 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B2024297 : Blo 1348993 2024297 := bstep (se 2 (by rfl) ⟨759111, by rfl⟩ : syracuseStep 2024297 = 1518223) B1518223
theorem B4326263 : Blo 1348993 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B8643503 : Blo 1348993 8643503 := bstep (se 1 (by rfl) ⟨6482627, by rfl⟩ : syracuseStep 8643503 = 12965255) B12965255
theorem B9233327 : Blo 1348993 9233327 := bstep (se 1 (by rfl) ⟨6924995, by rfl⟩ : syracuseStep 9233327 = 13849991) B13849991
theorem B5768111 : Blo 1348993 5768111 := bstep (se 1 (by rfl) ⟨4326083, by rfl⟩ : syracuseStep 5768111 = 8652167) B8652167
theorem B1622959 : Blo 1348993 1622959 := bstep (se 1 (by rfl) ⟨1217219, by rfl⟩ : syracuseStep 1622959 = 2434439) B2434439
theorem B2024375 : Blo 1348993 2024375 := bstep (se 1 (by rfl) ⟨1518281, by rfl⟩ : syracuseStep 2024375 = 3036563) B3036563
theorem B5473207 : Blo 1348993 5473207 := bstep (se 1 (by rfl) ⟨4104905, by rfl⟩ : syracuseStep 5473207 = 8209811) B8209811
theorem B2278327 : Blo 1348993 2278327 := bstep (se 1 (by rfl) ⟨1708745, by rfl⟩ : syracuseStep 2278327 = 3417491) B3417491
theorem B2024411 : Blo 1348993 2024411 := bstep (se 1 (by rfl) ⟨1518308, by rfl⟩ : syracuseStep 2024411 = 3036617) B3036617
theorem B38896685 : Blo 1348993 38896685 := bstep (se 3 (by rfl) ⟨7293128, by rfl⟩ : syracuseStep 38896685 = 14586257) B14586257
theorem B3417167 : Blo 1348993 3417167 := bstep (se 1 (by rfl) ⟨2562875, by rfl⟩ : syracuseStep 3417167 = 5125751) B5125751
theorem B2278523 : Blo 1348993 2278523 := bstep (se 1 (by rfl) ⟨1708892, by rfl⟩ : syracuseStep 2278523 = 3417785) B3417785
theorem B3245303 : Blo 1348993 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B2024879 : Blo 1348993 2024879 := bstep (se 1 (by rfl) ⟨1518659, by rfl⟩ : syracuseStep 2024879 = 3037319) B3037319
theorem B16639451 : Blo 1348993 16639451 := bstep (se 1 (by rfl) ⟨12479588, by rfl⟩ : syracuseStep 16639451 = 24959177) B24959177
theorem B2024969 : Blo 1348993 2024969 := bstep (se 2 (by rfl) ⟨759363, by rfl⟩ : syracuseStep 2024969 = 1518727) B1518727
theorem B2278921 : Blo 1348993 2278921 := bstep (se 2 (by rfl) ⟨854595, by rfl⟩ : syracuseStep 2278921 = 1709191) B1709191
theorem B10249739 : Blo 1348993 10249739 := bstep (se 1 (by rfl) ⟨7687304, by rfl⟩ : syracuseStep 10249739 = 15374609) B15374609
theorem B2024999 : Blo 1348993 2024999 := bstep (se 1 (by rfl) ⟨1518749, by rfl⟩ : syracuseStep 2024999 = 3037499) B3037499
theorem B4556411 : Blo 1348993 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B2025083 : Blo 1348993 2025083 := bstep (se 1 (by rfl) ⟨1518812, by rfl⟩ : syracuseStep 2025083 = 3037625) B3037625
theorem B2279083 : Blo 1348993 2279083 := bstep (se 1 (by rfl) ⟨1709312, by rfl⟩ : syracuseStep 2279083 = 3418625) B3418625
theorem B3417815 : Blo 1348993 3417815 := bstep (se 1 (by rfl) ⟨2563361, by rfl⟩ : syracuseStep 3417815 = 5126723) B5126723
theorem B2025209 : Blo 1348993 2025209 := bstep (se 2 (by rfl) ⟨759453, by rfl⟩ : syracuseStep 2025209 = 1518907) B1518907
theorem B4556573 : Blo 1348993 4556573 := bstep (se 3 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 4556573 = 1708715) B1708715
theorem B2025311 : Blo 1348993 2025311 := bstep (se 1 (by rfl) ⟨1518983, by rfl⟩ : syracuseStep 2025311 = 3037967) B3037967
theorem B2025323 : Blo 1348993 2025323 := bstep (se 1 (by rfl) ⟨1518992, by rfl⟩ : syracuseStep 2025323 = 3037985) B3037985
theorem B10954615 : Blo 1348993 10954615 := bstep (se 1 (by rfl) ⟨8215961, by rfl⟩ : syracuseStep 10954615 = 16431923) B16431923
theorem B11536289 : Blo 1348993 11536289 := bstep (se 2 (by rfl) ⟨4326108, by rfl⟩ : syracuseStep 11536289 = 8652217) B8652217
theorem B2279387 : Blo 1348993 2279387 := bstep (se 1 (by rfl) ⟨1709540, by rfl⟩ : syracuseStep 2279387 = 3419081) B3419081
theorem B4327481 : Blo 1348993 4327481 := bstep (se 2 (by rfl) ⟨1622805, by rfl⟩ : syracuseStep 4327481 = 3245611) B3245611
theorem B1517647 : Blo 1348993 1517647 := bstep (se 1 (by rfl) ⟨1138235, by rfl⟩ : syracuseStep 1517647 = 2276471) B2276471
theorem B2025551 : Blo 1348993 2025551 := bstep (se 1 (by rfl) ⟨1519163, by rfl⟩ : syracuseStep 2025551 = 3038327) B3038327
theorem B2738299 : Blo 1348993 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B4327595 : Blo 1348993 4327595 := bstep (se 1 (by rfl) ⟨3245696, by rfl⟩ : syracuseStep 4327595 = 6491393) B6491393
theorem B2025671 : Blo 1348993 2025671 := bstep (se 1 (by rfl) ⟨1519253, by rfl⟩ : syracuseStep 2025671 = 3038507) B3038507
theorem B2279623 : Blo 1348993 2279623 := bstep (se 1 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 2279623 = 3419435) B3419435
theorem B2025833 : Blo 1348993 2025833 := bstep (se 2 (by rfl) ⟨759687, by rfl⟩ : syracuseStep 2025833 = 1519375) B1519375
theorem B2279785 : Blo 1348993 2279785 := bstep (se 2 (by rfl) ⟨854919, by rfl⟩ : syracuseStep 2279785 = 1709839) B1709839
theorem B1386875 : Blo 1348993 1386875 := bstep (se 1 (by rfl) ⟨1040156, by rfl⟩ : syracuseStep 1386875 = 2080313) B2080313
theorem B2025911 : Blo 1348993 2025911 := bstep (se 1 (by rfl) ⟨1519433, by rfl⟩ : syracuseStep 2025911 = 3038867) B3038867
theorem B1518043 : Blo 1348993 1518043 := bstep (se 1 (by rfl) ⟨1138532, by rfl⟩ : syracuseStep 1518043 = 2277065) B2277065
theorem B4557275 : Blo 1348993 4557275 := bstep (se 1 (by rfl) ⟨3417956, by rfl⟩ : syracuseStep 4557275 = 6835913) B6835913
theorem B2025947 : Blo 1348993 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B5122547 : Blo 1348993 5122547 := bstep (se 1 (by rfl) ⟨3841910, by rfl⟩ : syracuseStep 5122547 = 7683821) B7683821
theorem B4934153 : Blo 1348993 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B8645143 : Blo 1348993 8645143 := bstep (se 1 (by rfl) ⟨6483857, by rfl⟩ : syracuseStep 8645143 = 12967715) B12967715
theorem B2738785 : Blo 1348993 2738785 := bstep (se 2 (by rfl) ⟨1027044, by rfl⟩ : syracuseStep 2738785 = 2054089) B2054089
theorem B4934267 : Blo 1348993 4934267 := bstep (se 1 (by rfl) ⟨3700700, by rfl⟩ : syracuseStep 4934267 = 7401401) B7401401
theorem B3648199 : Blo 1348993 3648199 := bstep (se 1 (by rfl) ⟨2736149, by rfl⟩ : syracuseStep 3648199 = 5472299) B5472299
theorem B3697481 : Blo 1348993 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B1518511 : Blo 1348993 1518511 := bstep (se 1 (by rfl) ⟨1138883, by rfl⟩ : syracuseStep 1518511 = 2277767) B2277767
theorem B2026415 : Blo 1348993 2026415 := bstep (se 1 (by rfl) ⟨1519811, by rfl⟩ : syracuseStep 2026415 = 3039623) B3039623
theorem B7687169 : Blo 1348993 7687169 := bstep (se 2 (by rfl) ⟨2882688, by rfl⟩ : syracuseStep 7687169 = 5765377) B5765377
theorem B4557977 : Blo 1348993 4557977 := bstep (se 2 (by rfl) ⟨1709241, by rfl⟩ : syracuseStep 4557977 = 3418483) B3418483
theorem B1518943 : Blo 1348993 1518943 := bstep (se 1 (by rfl) ⟨1139207, by rfl⟩ : syracuseStep 1518943 = 2278415) B2278415
theorem B10251683 : Blo 1348993 10251683 := bstep (se 1 (by rfl) ⟨7688762, by rfl⟩ : syracuseStep 10251683 = 15377525) B15377525
theorem B15371693 : Blo 1348993 15371693 := bstep (se 3 (by rfl) ⟨2882192, by rfl⟩ : syracuseStep 15371693 = 5764385) B5764385
theorem B26291699 : Blo 1348993 26291699 := bstep (se 1 (by rfl) ⟨19718774, by rfl⟩ : syracuseStep 26291699 = 39437549) B39437549
theorem B4107763 : Blo 1348993 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B3845657 : Blo 1348993 3845657 := bstep (se 2 (by rfl) ⟨1442121, by rfl⟩ : syracuseStep 3845657 = 2884243) B2884243
theorem B6835751 : Blo 1348993 6835751 := bstep (se 1 (by rfl) ⟨5126813, by rfl⟩ : syracuseStep 6835751 = 10253627) B10253627
theorem B20778619 : Blo 1348993 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B1519303 : Blo 1348993 1519303 := bstep (se 1 (by rfl) ⟨1139477, by rfl⟩ : syracuseStep 1519303 = 2278955) B2278955
theorem B5844695 : Blo 1348993 5844695 := bstep (se 1 (by rfl) ⟨4383521, by rfl⟩ : syracuseStep 5844695 = 8767043) B8767043
theorem B3649463 : Blo 1348993 3649463 := bstep (se 1 (by rfl) ⟨2737097, by rfl⟩ : syracuseStep 3649463 = 5474195) B5474195
theorem B3559355 : Blo 1348993 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B8654779 : Blo 1348993 8654779 := bstep (se 1 (by rfl) ⟨6491084, by rfl⟩ : syracuseStep 8654779 = 12982169) B12982169
theorem B23072849 : Blo 1348993 23072849 := bstep (se 2 (by rfl) ⟨8652318, by rfl⟩ : syracuseStep 23072849 = 17304637) B17304637
theorem B4559165 : Blo 1348993 4559165 := bstep (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) B1709687
theorem B2281835 : Blo 1348993 2281835 := bstep (se 1 (by rfl) ⟨1711376, by rfl⟩ : syracuseStep 2281835 = 3422753) B3422753
theorem B17297873 : Blo 1348993 17297873 := bstep (se 2 (by rfl) ⟨6486702, by rfl⟩ : syracuseStep 17297873 = 12973405) B12973405
theorem B5763565 : Blo 1348993 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B3035771 : Blo 1348993 3035771 := bstep (se 1 (by rfl) ⟨2276828, by rfl⟩ : syracuseStep 3035771 = 4553657) B4553657
theorem B1921735 : Blo 1348993 1921735 := bstep (se 1 (by rfl) ⟨1441301, by rfl⟩ : syracuseStep 1921735 = 2882603) B2882603
theorem B9491153 : Blo 1348993 9491153 := bstep (se 2 (by rfl) ⟨3559182, by rfl⟩ : syracuseStep 9491153 = 7118365) B7118365
theorem B3461881 : Blo 1348993 3461881 := bstep (se 2 (by rfl) ⟨1298205, by rfl⟩ : syracuseStep 3461881 = 2596411) B2596411
theorem B3035897 : Blo 1348993 3035897 := bstep (se 2 (by rfl) ⟨1138461, by rfl⟩ : syracuseStep 3035897 = 2276923) B2276923
theorem B3036167 : Blo 1348993 3036167 := bstep (se 1 (by rfl) ⟨2277125, by rfl⟩ : syracuseStep 3036167 = 4554251) B4554251
theorem B1709095 : Blo 1348993 1709095 := bstep (se 1 (by rfl) ⟨1281821, by rfl⟩ : syracuseStep 1709095 = 2563643) B2563643
theorem B3036239 : Blo 1348993 3036239 := bstep (se 1 (by rfl) ⟨2277179, by rfl⟩ : syracuseStep 3036239 = 4554359) B4554359
theorem B3650717 : Blo 1348993 3650717 := bstep (se 3 (by rfl) ⟨684509, by rfl⟩ : syracuseStep 3650717 = 1369019) B1369019
theorem B5125463 : Blo 1348993 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B1709419 : Blo 1348993 1709419 := bstep (se 1 (by rfl) ⟨1282064, by rfl⟩ : syracuseStep 1709419 = 2564129) B2564129
theorem B1349039 : Blo 1348993 1349039 := bstep (se 1 (by rfl) ⟨1011779, by rfl⟩ : syracuseStep 1349039 = 2023559) B2023559
theorem B1349063 : Blo 1348993 1349063 := bstep (se 1 (by rfl) ⟨1011797, by rfl⟩ : syracuseStep 1349063 = 2023595) B2023595
theorem B1349083 : Blo 1348993 1349083 := bstep (se 1 (by rfl) ⟨1011812, by rfl⟩ : syracuseStep 1349083 = 2023625) B2023625
theorem B3036635 : Blo 1348993 3036635 := bstep (se 1 (by rfl) ⟨2277476, by rfl⟩ : syracuseStep 3036635 = 4554953) B4554953
theorem B4322803 : Blo 1348993 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B16422389 : Blo 1348993 16422389 := bstep (se 5 (by rfl) ⟨769799, by rfl⟩ : syracuseStep 16422389 = 1539599) B1539599
theorem B11539979 : Blo 1348993 11539979 := bstep (se 1 (by rfl) ⟨8654984, by rfl⟩ : syracuseStep 11539979 = 17309969) B17309969
theorem B1349159 : Blo 1348993 1349159 := bstep (se 1 (by rfl) ⟨1011869, by rfl⟩ : syracuseStep 1349159 = 2023739) B2023739
theorem B1349199 : Blo 1348993 1349199 := bstep (se 1 (by rfl) ⟨1011899, by rfl⟩ : syracuseStep 1349199 = 2023799) B2023799
theorem B2561615 : Blo 1348993 2561615 := bstep (se 1 (by rfl) ⟨1921211, by rfl⟩ : syracuseStep 2561615 = 3842423) B3842423
theorem B1349215 : Blo 1348993 1349215 := bstep (se 1 (by rfl) ⟨1011911, by rfl⟩ : syracuseStep 1349215 = 2023823) B2023823
theorem B6837857 : Blo 1348993 6837857 := bstep (se 2 (by rfl) ⟨2564196, by rfl⟩ : syracuseStep 6837857 = 5128393) B5128393
theorem B1349243 : Blo 1348993 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B13858451 : Blo 1348993 13858451 := bstep (se 1 (by rfl) ⟨10393838, by rfl⟩ : syracuseStep 13858451 = 20787677) B20787677
theorem B1349295 : Blo 1348993 1349295 := bstep (se 1 (by rfl) ⟨1011971, by rfl⟩ : syracuseStep 1349295 = 2023943) B2023943
theorem B6829757 : Blo 1348993 6829757 := bstep (se 3 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 6829757 = 2561159) B2561159
theorem B1349319 : Blo 1348993 1349319 := bstep (se 1 (by rfl) ⟨1011989, by rfl⟩ : syracuseStep 1349319 = 2023979) B2023979
theorem B1349339 : Blo 1348993 1349339 := bstep (se 1 (by rfl) ⟨1012004, by rfl⟩ : syracuseStep 1349339 = 2024009) B2024009
theorem B10254113 : Blo 1348993 10254113 := bstep (se 2 (by rfl) ⟨3845292, by rfl⟩ : syracuseStep 10254113 = 7690585) B7690585
theorem B1349415 : Blo 1348993 1349415 := bstep (se 1 (by rfl) ⟨1012061, by rfl⟩ : syracuseStep 1349415 = 2024123) B2024123
theorem B1349455 : Blo 1348993 1349455 := bstep (se 1 (by rfl) ⟨1012091, by rfl⟩ : syracuseStep 1349455 = 2024183) B2024183
theorem B6829919 : Blo 1348993 6829919 := bstep (se 1 (by rfl) ⟨5122439, by rfl⟩ : syracuseStep 6829919 = 10244879) B10244879
theorem B1349471 : Blo 1348993 1349471 := bstep (se 1 (by rfl) ⟨1012103, by rfl⟩ : syracuseStep 1349471 = 2024207) B2024207
theorem B1824619 : Blo 1348993 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B1349499 : Blo 1348993 1349499 := bstep (se 1 (by rfl) ⟨1012124, by rfl⟩ : syracuseStep 1349499 = 2024249) B2024249
theorem B2881441 : Blo 1348993 2881441 := bstep (se 2 (by rfl) ⟨1080540, by rfl⟩ : syracuseStep 2881441 = 2161081) B2161081
theorem B1349551 : Blo 1348993 1349551 := bstep (se 1 (by rfl) ⟨1012163, by rfl⟩ : syracuseStep 1349551 = 2024327) B2024327
theorem B3037103 : Blo 1348993 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B1349575 : Blo 1348993 1349575 := bstep (se 1 (by rfl) ⟨1012181, by rfl⟩ : syracuseStep 1349575 = 2024363) B2024363
theorem B1349595 : Blo 1348993 1349595 := bstep (se 1 (by rfl) ⟨1012196, by rfl⟩ : syracuseStep 1349595 = 2024393) B2024393
theorem B1349671 : Blo 1348993 1349671 := bstep (se 1 (by rfl) ⟨1012253, by rfl⟩ : syracuseStep 1349671 = 2024507) B2024507
theorem B1349711 : Blo 1348993 1349711 := bstep (se 1 (by rfl) ⟨1012283, by rfl⟩ : syracuseStep 1349711 = 2024567) B2024567
theorem B1349727 : Blo 1348993 1349727 := bstep (se 1 (by rfl) ⟨1012295, by rfl⟩ : syracuseStep 1349727 = 2024591) B2024591
theorem B2431073 : Blo 1348993 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B1349755 : Blo 1348993 1349755 := bstep (se 1 (by rfl) ⟨1012316, by rfl⟩ : syracuseStep 1349755 = 2024633) B2024633
theorem B3037355 : Blo 1348993 3037355 := bstep (se 1 (by rfl) ⟨2278016, by rfl⟩ : syracuseStep 3037355 = 4556033) B4556033
theorem B1349807 : Blo 1348993 1349807 := bstep (se 1 (by rfl) ⟨1012355, by rfl⟩ : syracuseStep 1349807 = 2024711) B2024711
theorem B1349831 : Blo 1348993 1349831 := bstep (se 1 (by rfl) ⟨1012373, by rfl⟩ : syracuseStep 1349831 = 2024747) B2024747
theorem B1349851 : Blo 1348993 1349851 := bstep (se 1 (by rfl) ⟨1012388, by rfl⟩ : syracuseStep 1349851 = 2024777) B2024777
theorem B1349927 : Blo 1348993 1349927 := bstep (se 1 (by rfl) ⟨1012445, by rfl⟩ : syracuseStep 1349927 = 2024891) B2024891
theorem B1349967 : Blo 1348993 1349967 := bstep (se 1 (by rfl) ⟨1012475, by rfl⟩ : syracuseStep 1349967 = 2024951) B2024951
theorem B1349983 : Blo 1348993 1349983 := bstep (se 1 (by rfl) ⟨1012487, by rfl⟩ : syracuseStep 1349983 = 2024975) B2024975
theorem B4323689 : Blo 1348993 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B1350011 : Blo 1348993 1350011 := bstep (se 1 (by rfl) ⟨1012508, by rfl⟩ : syracuseStep 1350011 = 2025017) B2025017
theorem B1350063 : Blo 1348993 1350063 := bstep (se 1 (by rfl) ⟨1012547, by rfl⟩ : syracuseStep 1350063 = 2025095) B2025095
theorem B1350087 : Blo 1348993 1350087 := bstep (se 1 (by rfl) ⟨1012565, by rfl⟩ : syracuseStep 1350087 = 2025131) B2025131
theorem B1350107 : Blo 1348993 1350107 := bstep (se 1 (by rfl) ⟨1012580, by rfl⟩ : syracuseStep 1350107 = 2025161) B2025161
theorem B4553225 : Blo 1348993 4553225 := bstep (se 2 (by rfl) ⟨1707459, by rfl⟩ : syracuseStep 4553225 = 3414919) B3414919
theorem B1350183 : Blo 1348993 1350183 := bstep (se 1 (by rfl) ⟨1012637, by rfl⟩ : syracuseStep 1350183 = 2025275) B2025275
theorem B2562617 : Blo 1348993 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B1350223 : Blo 1348993 1350223 := bstep (se 1 (by rfl) ⟨1012667, by rfl⟩ : syracuseStep 1350223 = 2025335) B2025335
theorem B1350239 : Blo 1348993 1350239 := bstep (se 1 (by rfl) ⟨1012679, by rfl⟩ : syracuseStep 1350239 = 2025359) B2025359
theorem B5126753 : Blo 1348993 5126753 := bstep (se 2 (by rfl) ⟨1922532, by rfl⟩ : syracuseStep 5126753 = 3845065) B3845065
theorem B1350267 : Blo 1348993 1350267 := bstep (se 1 (by rfl) ⟨1012700, by rfl⟩ : syracuseStep 1350267 = 2025401) B2025401
theorem B1350319 : Blo 1348993 1350319 := bstep (se 1 (by rfl) ⟨1012739, by rfl⟩ : syracuseStep 1350319 = 2025479) B2025479
theorem B3037895 : Blo 1348993 3037895 := bstep (se 1 (by rfl) ⟨2278421, by rfl⟩ : syracuseStep 3037895 = 4556843) B4556843
theorem B1350343 : Blo 1348993 1350343 := bstep (se 1 (by rfl) ⟨1012757, by rfl⟩ : syracuseStep 1350343 = 2025515) B2025515
theorem B1350363 : Blo 1348993 1350363 := bstep (se 1 (by rfl) ⟨1012772, by rfl⟩ : syracuseStep 1350363 = 2025545) B2025545
theorem B1350439 : Blo 1348993 1350439 := bstep (se 1 (by rfl) ⟨1012829, by rfl⟩ : syracuseStep 1350439 = 2025659) B2025659
theorem B1350479 : Blo 1348993 1350479 := bstep (se 1 (by rfl) ⟨1012859, by rfl⟩ : syracuseStep 1350479 = 2025719) B2025719
theorem B1350495 : Blo 1348993 1350495 := bstep (se 1 (by rfl) ⟨1012871, by rfl⟩ : syracuseStep 1350495 = 2025743) B2025743
theorem B1350523 : Blo 1348993 1350523 := bstep (se 1 (by rfl) ⟨1012892, by rfl⟩ : syracuseStep 1350523 = 2025785) B2025785
theorem B1350575 : Blo 1348993 1350575 := bstep (se 1 (by rfl) ⟨1012931, by rfl⟩ : syracuseStep 1350575 = 2025863) B2025863
theorem B1350599 : Blo 1348993 1350599 := bstep (se 1 (by rfl) ⟨1012949, by rfl⟩ : syracuseStep 1350599 = 2025899) B2025899
theorem B1350619 : Blo 1348993 1350619 := bstep (se 1 (by rfl) ⟨1012964, by rfl⟩ : syracuseStep 1350619 = 2025929) B2025929
theorem B4324367 : Blo 1348993 4324367 := bstep (se 1 (by rfl) ⟨3243275, by rfl⟩ : syracuseStep 4324367 = 6486551) B6486551
theorem B6839315 : Blo 1348993 6839315 := bstep (se 1 (by rfl) ⟨5129486, by rfl⟩ : syracuseStep 6839315 = 10258973) B10258973
theorem B1350695 : Blo 1348993 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B9870403 : Blo 1348993 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B1350735 : Blo 1348993 1350735 := bstep (se 1 (by rfl) ⟨1013051, by rfl⟩ : syracuseStep 1350735 = 2026103) B2026103
theorem B1350751 : Blo 1348993 1350751 := bstep (se 1 (by rfl) ⟨1013063, by rfl⟩ : syracuseStep 1350751 = 2026127) B2026127
theorem B1350779 : Blo 1348993 1350779 := bstep (se 1 (by rfl) ⟨1013084, by rfl⟩ : syracuseStep 1350779 = 2026169) B2026169
theorem B3243179 : Blo 1348993 3243179 := bstep (se 1 (by rfl) ⟨2432384, by rfl⟩ : syracuseStep 3243179 = 4864769) B4864769
theorem B1350831 : Blo 1348993 1350831 := bstep (se 1 (by rfl) ⟨1013123, by rfl⟩ : syracuseStep 1350831 = 2026247) B2026247
theorem B1350855 : Blo 1348993 1350855 := bstep (se 1 (by rfl) ⟨1013141, by rfl⟩ : syracuseStep 1350855 = 2026283) B2026283
theorem B1350875 : Blo 1348993 1350875 := bstep (se 1 (by rfl) ⟨1013156, by rfl⟩ : syracuseStep 1350875 = 2026313) B2026313
theorem B2276599 : Blo 1348993 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B7691543 : Blo 1348993 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B1350951 : Blo 1348993 1350951 := bstep (se 1 (by rfl) ⟨1013213, by rfl⟩ : syracuseStep 1350951 = 2026427) B2026427
theorem B1350991 : Blo 1348993 1350991 := bstep (se 1 (by rfl) ⟨1013243, by rfl⟩ : syracuseStep 1350991 = 2026487) B2026487
theorem B4554089 : Blo 1348993 4554089 := bstep (se 2 (by rfl) ⟨1707783, by rfl⟩ : syracuseStep 4554089 = 3415567) B3415567
theorem B32841085 : Blo 1348993 32841085 := bstep (se 3 (by rfl) ⟨6157703, by rfl⟩ : syracuseStep 32841085 = 12315407) B12315407
theorem B1441199 : Blo 1348993 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B2276795 : Blo 1348993 2276795 := bstep (se 1 (by rfl) ⟨1707596, by rfl⟩ : syracuseStep 2276795 = 3415193) B3415193
theorem B36961757 : Blo 1348993 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B5414381 : Blo 1348993 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B2276903 : Blo 1348993 2276903 := bstep (se 1 (by rfl) ⟨1707677, by rfl⟩ : syracuseStep 2276903 = 3415355) B3415355
theorem B3038759 : Blo 1348993 3038759 := bstep (se 1 (by rfl) ⟨2279069, by rfl⟩ : syracuseStep 3038759 = 4558139) B4558139
theorem B2277193 : Blo 1348993 2277193 := bstep (se 2 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 2277193 = 1707895) B1707895
theorem B2277227 : Blo 1348993 2277227 := bstep (se 1 (by rfl) ⟨1707920, by rfl⟩ : syracuseStep 2277227 = 3415841) B3415841
theorem B3039083 : Blo 1348993 3039083 := bstep (se 1 (by rfl) ⟨2279312, by rfl⟩ : syracuseStep 3039083 = 4558625) B4558625
theorem B3039137 : Blo 1348993 3039137 := bstep (se 2 (by rfl) ⟨1139676, by rfl⟩ : syracuseStep 3039137 = 2279353) B2279353
theorem B3841967 : Blo 1348993 3841967 := bstep (se 1 (by rfl) ⟨2881475, by rfl⟩ : syracuseStep 3841967 = 5762951) B5762951
theorem B4554683 : Blo 1348993 4554683 := bstep (se 1 (by rfl) ⟨3416012, by rfl⟩ : syracuseStep 4554683 = 6832025) B6832025
theorem B2736091 : Blo 1348993 2736091 := bstep (se 1 (by rfl) ⟨2052068, by rfl⟩ : syracuseStep 2736091 = 4104137) B4104137
theorem B6832187 : Blo 1348993 6832187 := bstep (se 1 (by rfl) ⟨5124140, by rfl⟩ : syracuseStep 6832187 = 10248281) B10248281
theorem B2023529 : Blo 1348993 2023529 := bstep (se 2 (by rfl) ⟨758823, by rfl⟩ : syracuseStep 2023529 = 1517647) B1517647
theorem B3039443 : Blo 1348993 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B3039497 : Blo 1348993 3039497 := bstep (se 2 (by rfl) ⟨1139811, by rfl⟩ : syracuseStep 3039497 = 2279623) B2279623
theorem B4555115 : Blo 1348993 4555115 := bstep (se 1 (by rfl) ⟨3416336, by rfl⟩ : syracuseStep 4555115 = 6832673) B6832673
theorem B2023847 : Blo 1348993 2023847 := bstep (se 1 (by rfl) ⟨1517885, by rfl⟩ : syracuseStep 2023847 = 3035771) B3035771
theorem B3039713 : Blo 1348993 3039713 := bstep (se 2 (by rfl) ⟨1139892, by rfl⟩ : syracuseStep 3039713 = 2279785) B2279785
theorem B2023931 : Blo 1348993 2023931 := bstep (se 1 (by rfl) ⟨1517948, by rfl⟩ : syracuseStep 2023931 = 3035897) B3035897
theorem B2884175 : Blo 1348993 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B2024057 : Blo 1348993 2024057 := bstep (se 2 (by rfl) ⟨759021, by rfl⟩ : syracuseStep 2024057 = 1518043) B1518043
theorem B4555385 : Blo 1348993 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B7684753 : Blo 1348993 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B2024111 : Blo 1348993 2024111 := bstep (se 1 (by rfl) ⟨1518083, by rfl⟩ : syracuseStep 2024111 = 3036167) B3036167
theorem B11526857 : Blo 1348993 11526857 := bstep (se 2 (by rfl) ⟨4322571, by rfl⟩ : syracuseStep 11526857 = 8645143) B8645143
theorem B2024159 : Blo 1348993 2024159 := bstep (se 1 (by rfl) ⟨1518119, by rfl⟩ : syracuseStep 2024159 = 3036239) B3036239
theorem B2278111 : Blo 1348993 2278111 := bstep (se 1 (by rfl) ⟨1708583, by rfl⟩ : syracuseStep 2278111 = 3417167) B3417167
theorem B2433811 : Blo 1348993 2433811 := bstep (se 1 (by rfl) ⟨1825358, by rfl⟩ : syracuseStep 2433811 = 3650717) B3650717
theorem B3416975 : Blo 1348993 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B8651681 : Blo 1348993 8651681 := bstep (se 2 (by rfl) ⟨3244380, by rfl⟩ : syracuseStep 8651681 = 6488761) B6488761
theorem B11092967 : Blo 1348993 11092967 := bstep (se 1 (by rfl) ⟨8319725, by rfl⟩ : syracuseStep 11092967 = 16639451) B16639451
theorem B2024423 : Blo 1348993 2024423 := bstep (se 1 (by rfl) ⟨1518317, by rfl⟩ : syracuseStep 2024423 = 3036635) B3036635
theorem B6833159 : Blo 1348993 6833159 := bstep (se 1 (by rfl) ⟨5124869, by rfl⟩ : syracuseStep 6833159 = 10249739) B10249739
theorem B7693319 : Blo 1348993 7693319 := bstep (se 1 (by rfl) ⟨5769989, by rfl⟩ : syracuseStep 7693319 = 11539979) B11539979
theorem B10249253 : Blo 1348993 10249253 := bstep (se 4 (by rfl) ⟨960867, by rfl⟩ : syracuseStep 10249253 = 1921735) B1921735
theorem B3843197 : Blo 1348993 3843197 := bstep (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) B1441199
theorem B2278543 : Blo 1348993 2278543 := bstep (se 1 (by rfl) ⟨1708907, by rfl⟩ : syracuseStep 2278543 = 3417815) B3417815
theorem B2024681 : Blo 1348993 2024681 := bstep (se 2 (by rfl) ⟨759255, by rfl⟩ : syracuseStep 2024681 = 1518511) B1518511
theorem B2024735 : Blo 1348993 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B13157741 : Blo 1348993 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B2884987 : Blo 1348993 2884987 := bstep (se 1 (by rfl) ⟨2163740, by rfl⟩ : syracuseStep 2884987 = 4327481) B4327481
theorem B2278793 : Blo 1348993 2278793 := bstep (se 2 (by rfl) ⟨854547, by rfl⟩ : syracuseStep 2278793 = 1709095) B1709095
theorem B2024903 : Blo 1348993 2024903 := bstep (se 1 (by rfl) ⟨1518677, by rfl⟩ : syracuseStep 2024903 = 3037355) B3037355
theorem B2885063 : Blo 1348993 2885063 := bstep (se 1 (by rfl) ⟨2163797, by rfl⟩ : syracuseStep 2885063 = 4327595) B4327595
theorem B6833645 : Blo 1348993 6833645 := bstep (se 3 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 6833645 = 2562617) B2562617
theorem B3417835 : Blo 1348993 3417835 := bstep (se 1 (by rfl) ⟨2563376, by rfl⟩ : syracuseStep 3417835 = 5126753) B5126753
theorem B2025257 : Blo 1348993 2025257 := bstep (se 2 (by rfl) ⟨759471, by rfl⟩ : syracuseStep 2025257 = 1518943) B1518943
theorem B2025263 : Blo 1348993 2025263 := bstep (se 1 (by rfl) ⟨1518947, by rfl⟩ : syracuseStep 2025263 = 3037895) B3037895
theorem B2279225 : Blo 1348993 2279225 := bstep (se 2 (by rfl) ⟨854709, by rfl⟩ : syracuseStep 2279225 = 1709419) B1709419
theorem B43788113 : Blo 1348993 43788113 := bstep (se 2 (by rfl) ⟨16420542, by rfl⟩ : syracuseStep 43788113 = 32841085) B32841085
theorem B2025737 : Blo 1348993 2025737 := bstep (se 2 (by rfl) ⟨759651, by rfl⟩ : syracuseStep 2025737 = 1519303) B1519303
theorem B6834455 : Blo 1348993 6834455 := bstep (se 1 (by rfl) ⟨5125841, by rfl⟩ : syracuseStep 6834455 = 10251683) B10251683
theorem B1517863 : Blo 1348993 1517863 := bstep (se 1 (by rfl) ⟨1138397, by rfl⟩ : syracuseStep 1517863 = 2276795) B2276795
theorem B1517935 : Blo 1348993 1517935 := bstep (se 1 (by rfl) ⟨1138451, by rfl⟩ : syracuseStep 1517935 = 2276903) B2276903
theorem B4557167 : Blo 1348993 4557167 := bstep (se 1 (by rfl) ⟨3417875, by rfl⟩ : syracuseStep 4557167 = 6835751) B6835751
theorem B2025839 : Blo 1348993 2025839 := bstep (se 1 (by rfl) ⟨1519379, by rfl⟩ : syracuseStep 2025839 = 3038759) B3038759
theorem B1518151 : Blo 1348993 1518151 := bstep (se 1 (by rfl) ⟨1138613, by rfl⟩ : syracuseStep 1518151 = 2277227) B2277227
theorem B2026055 : Blo 1348993 2026055 := bstep (se 1 (by rfl) ⟨1519541, by rfl⟩ : syracuseStep 2026055 = 3039083) B3039083
theorem B21908069 : Blo 1348993 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B2026091 : Blo 1348993 2026091 := bstep (se 1 (by rfl) ⟨1519568, by rfl⟩ : syracuseStep 2026091 = 3039137) B3039137
theorem B3648121 : Blo 1348993 3648121 := bstep (se 2 (by rfl) ⟨1368045, by rfl⟩ : syracuseStep 3648121 = 2736091) B2736091
theorem B3418807 : Blo 1348993 3418807 := bstep (se 1 (by rfl) ⟨2564105, by rfl⟩ : syracuseStep 3418807 = 5128211) B5128211
theorem B5122835 : Blo 1348993 5122835 := bstep (se 1 (by rfl) ⟨3842126, by rfl⟩ : syracuseStep 5122835 = 7684253) B7684253
theorem B3844883 : Blo 1348993 3844883 := bstep (se 1 (by rfl) ⟨2883662, by rfl⟩ : syracuseStep 3844883 = 5767325) B5767325
theorem B2026319 : Blo 1348993 2026319 := bstep (se 1 (by rfl) ⟨1519739, by rfl⟩ : syracuseStep 2026319 = 3039479) B3039479
theorem B6482861 : Blo 1348993 6482861 := bstep (se 3 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 6482861 = 2431073) B2431073
theorem B3419111 : Blo 1348993 3419111 := bstep (se 1 (by rfl) ⟨2564333, by rfl⟩ : syracuseStep 3419111 = 5128667) B5128667
theorem B3845339 : Blo 1348993 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B5762335 : Blo 1348993 5762335 := bstep (se 1 (by rfl) ⟨4321751, by rfl⟩ : syracuseStep 5762335 = 8643503) B8643503
theorem B6155551 : Blo 1348993 6155551 := bstep (se 1 (by rfl) ⟨4616663, by rfl⟩ : syracuseStep 6155551 = 9233327) B9233327
theorem B3845407 : Blo 1348993 3845407 := bstep (se 1 (by rfl) ⟨2884055, by rfl⟩ : syracuseStep 3845407 = 5768111) B5768111
theorem B8654141 : Blo 1348993 8654141 := bstep (se 3 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 8654141 = 3245303) B3245303
theorem B25931123 : Blo 1348993 25931123 := bstep (se 1 (by rfl) ⟨19448342, by rfl⟩ : syracuseStep 25931123 = 38896685) B38896685
theorem B1519015 : Blo 1348993 1519015 := bstep (se 1 (by rfl) ⟨1139261, by rfl⟩ : syracuseStep 1519015 = 2278523) B2278523
theorem B3698333 : Blo 1348993 3698333 := bstep (se 3 (by rfl) ⟨693437, by rfl⟩ : syracuseStep 3698333 = 1386875) B1386875
theorem B4615841 : Blo 1348993 4615841 := bstep (se 2 (by rfl) ⟨1730940, by rfl⟩ : syracuseStep 4615841 = 3461881) B3461881
theorem B6925985 : Blo 1348993 6925985 := bstep (se 2 (by rfl) ⟨2597244, by rfl⟩ : syracuseStep 6925985 = 5194489) B5194489
theorem B10948259 : Blo 1348993 10948259 := bstep (se 1 (by rfl) ⟨8211194, by rfl⟩ : syracuseStep 10948259 = 16422389) B16422389
theorem B1707743 : Blo 1348993 1707743 := bstep (se 1 (by rfl) ⟨1280807, by rfl⟩ : syracuseStep 1707743 = 2561615) B2561615
theorem B4558571 : Blo 1348993 4558571 := bstep (se 1 (by rfl) ⟨3418928, by rfl⟩ : syracuseStep 4558571 = 6837857) B6837857
theorem B6836075 : Blo 1348993 6836075 := bstep (se 1 (by rfl) ⟨5127056, by rfl⟩ : syracuseStep 6836075 = 10254113) B10254113
theorem B1519591 : Blo 1348993 1519591 := bstep (se 1 (by rfl) ⟨1139693, by rfl⟩ : syracuseStep 1519591 = 2279387) B2279387
theorem B13160537 : Blo 1348993 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B3035465 : Blo 1348993 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B3035483 : Blo 1348993 3035483 := bstep (se 1 (by rfl) ⟨2276612, by rfl⟩ : syracuseStep 3035483 = 4553225) B4553225
theorem B3289511 : Blo 1348993 3289511 := bstep (se 1 (by rfl) ⟨2467133, by rfl⟩ : syracuseStep 3289511 = 4934267) B4934267
theorem B25309741 : Blo 1348993 25309741 := bstep (se 3 (by rfl) ⟨4745576, by rfl⟩ : syracuseStep 25309741 = 9491153) B9491153
theorem B15585853 : Blo 1348993 15585853 := bstep (se 3 (by rfl) ⟨2922347, by rfl⟩ : syracuseStep 15585853 = 5844695) B5844695
theorem B5763737 : Blo 1348993 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B5124779 : Blo 1348993 5124779 := bstep (se 1 (by rfl) ⟨3843584, by rfl⟩ : syracuseStep 5124779 = 7687169) B7687169
theorem B4559543 : Blo 1348993 4559543 := bstep (se 1 (by rfl) ⟨3419657, by rfl⟩ : syracuseStep 4559543 = 6839315) B6839315
theorem B3036059 : Blo 1348993 3036059 := bstep (se 1 (by rfl) ⟨2277044, by rfl⟩ : syracuseStep 3036059 = 4554089) B4554089
theorem B8655781 : Blo 1348993 8655781 := bstep (se 4 (by rfl) ⟨811479, by rfl⟩ : syracuseStep 8655781 = 1622959) B1622959
theorem B3609587 : Blo 1348993 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B17527799 : Blo 1348993 17527799 := bstep (se 1 (by rfl) ⟨13145849, by rfl⟩ : syracuseStep 17527799 = 26291699) B26291699
theorem B3036257 : Blo 1348993 3036257 := bstep (se 2 (by rfl) ⟨1138596, by rfl⟩ : syracuseStep 3036257 = 2277193) B2277193
theorem B11539705 : Blo 1348993 11539705 := bstep (se 2 (by rfl) ⟨4327389, by rfl⟩ : syracuseStep 11539705 = 8654779) B8654779
theorem B2561311 : Blo 1348993 2561311 := bstep (se 1 (by rfl) ⟨1920983, by rfl⟩ : syracuseStep 2561311 = 3841967) B3841967
theorem B3036455 : Blo 1348993 3036455 := bstep (se 1 (by rfl) ⟨2277341, by rfl⟩ : syracuseStep 3036455 = 4554683) B4554683
theorem B2372903 : Blo 1348993 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B1643899 : Blo 1348993 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B15381899 : Blo 1348993 15381899 := bstep (se 1 (by rfl) ⟨11536424, by rfl⟩ : syracuseStep 15381899 = 23072849) B23072849
theorem B1349031 : Blo 1348993 1349031 := bstep (se 1 (by rfl) ⟨1011773, by rfl⟩ : syracuseStep 1349031 = 2023547) B2023547
theorem B3651065 : Blo 1348993 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B1349115 : Blo 1348993 1349115 := bstep (se 1 (by rfl) ⟨1011836, by rfl⟩ : syracuseStep 1349115 = 2023673) B2023673
theorem B1349183 : Blo 1348993 1349183 := bstep (se 1 (by rfl) ⟨1011887, by rfl⟩ : syracuseStep 1349183 = 2023775) B2023775
theorem B1349191 : Blo 1348993 1349191 := bstep (se 1 (by rfl) ⟨1011893, by rfl⟩ : syracuseStep 1349191 = 2023787) B2023787
theorem B1521223 : Blo 1348993 1521223 := bstep (se 1 (by rfl) ⟨1140917, by rfl⟩ : syracuseStep 1521223 = 2281835) B2281835
theorem B11531915 : Blo 1348993 11531915 := bstep (se 1 (by rfl) ⟨8648936, by rfl⟩ : syracuseStep 11531915 = 17297873) B17297873
theorem B3036833 : Blo 1348993 3036833 := bstep (se 2 (by rfl) ⟨1138812, by rfl⟩ : syracuseStep 3036833 = 2277625) B2277625
theorem B1709743 : Blo 1348993 1709743 := bstep (se 1 (by rfl) ⟨1282307, by rfl⟩ : syracuseStep 1709743 = 2564615) B2564615
theorem B1349343 : Blo 1348993 1349343 := bstep (se 1 (by rfl) ⟨1012007, by rfl⟩ : syracuseStep 1349343 = 2024015) B2024015
theorem B29202191 : Blo 1348993 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B8648477 : Blo 1348993 8648477 := bstep (se 3 (by rfl) ⟨1621589, by rfl⟩ : syracuseStep 8648477 = 3243179) B3243179
theorem B1349423 : Blo 1348993 1349423 := bstep (se 1 (by rfl) ⟨1012067, by rfl⟩ : syracuseStep 1349423 = 2024135) B2024135
theorem B1349531 : Blo 1348993 1349531 := bstep (se 1 (by rfl) ⟨1012148, by rfl⟩ : syracuseStep 1349531 = 2024297) B2024297
theorem B1349583 : Blo 1348993 1349583 := bstep (se 1 (by rfl) ⟨1012187, by rfl⟩ : syracuseStep 1349583 = 2024375) B2024375
theorem B1349607 : Blo 1348993 1349607 := bstep (se 1 (by rfl) ⟨1012205, by rfl⟩ : syracuseStep 1349607 = 2024411) B2024411
theorem B3037193 : Blo 1348993 3037193 := bstep (se 2 (by rfl) ⟨1138947, by rfl⟩ : syracuseStep 3037193 = 2277895) B2277895
theorem B3651713 : Blo 1348993 3651713 := bstep (se 2 (by rfl) ⟨1369392, by rfl⟩ : syracuseStep 3651713 = 2738785) B2738785
theorem B4864265 : Blo 1348993 4864265 := bstep (se 2 (by rfl) ⟨1824099, by rfl⟩ : syracuseStep 4864265 = 3648199) B3648199
theorem B1349919 : Blo 1348993 1349919 := bstep (se 1 (by rfl) ⟨1012439, by rfl⟩ : syracuseStep 1349919 = 2024879) B2024879
theorem B1349979 : Blo 1348993 1349979 := bstep (se 1 (by rfl) ⟨1012484, by rfl⟩ : syracuseStep 1349979 = 2024969) B2024969
theorem B1349999 : Blo 1348993 1349999 := bstep (se 1 (by rfl) ⟨1012499, by rfl⟩ : syracuseStep 1349999 = 2024999) B2024999
theorem B3037607 : Blo 1348993 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B1350055 : Blo 1348993 1350055 := bstep (se 1 (by rfl) ⟨1012541, by rfl⟩ : syracuseStep 1350055 = 2025083) B2025083
theorem B9238967 : Blo 1348993 9238967 := bstep (se 1 (by rfl) ⟨6929225, by rfl⟩ : syracuseStep 9238967 = 13858451) B13858451
theorem B4553171 : Blo 1348993 4553171 := bstep (se 1 (by rfl) ⟨3414878, by rfl⟩ : syracuseStep 4553171 = 6829757) B6829757
theorem B1350139 : Blo 1348993 1350139 := bstep (se 1 (by rfl) ⟨1012604, by rfl⟩ : syracuseStep 1350139 = 2025209) B2025209
theorem B3037715 : Blo 1348993 3037715 := bstep (se 1 (by rfl) ⟨2278286, by rfl⟩ : syracuseStep 3037715 = 4556573) B4556573
theorem B4553279 : Blo 1348993 4553279 := bstep (se 1 (by rfl) ⟨3414959, by rfl⟩ : syracuseStep 4553279 = 6829919) B6829919
theorem B1350207 : Blo 1348993 1350207 := bstep (se 1 (by rfl) ⟨1012655, by rfl⟩ : syracuseStep 1350207 = 2025311) B2025311
theorem B1350215 : Blo 1348993 1350215 := bstep (se 1 (by rfl) ⟨1012661, by rfl⟩ : syracuseStep 1350215 = 2025323) B2025323
theorem B7297609 : Blo 1348993 7297609 := bstep (se 2 (by rfl) ⟨2736603, by rfl⟩ : syracuseStep 7297609 = 5473207) B5473207
theorem B3037769 : Blo 1348993 3037769 := bstep (se 2 (by rfl) ⟨1139163, by rfl⟩ : syracuseStep 3037769 = 2278327) B2278327
theorem B7690859 : Blo 1348993 7690859 := bstep (se 1 (by rfl) ⟨5768144, by rfl⟩ : syracuseStep 7690859 = 11536289) B11536289
theorem B1350367 : Blo 1348993 1350367 := bstep (se 1 (by rfl) ⟨1012775, by rfl⟩ : syracuseStep 1350367 = 2025551) B2025551
theorem B10255085 : Blo 1348993 10255085 := bstep (se 3 (by rfl) ⟨1922828, by rfl⟩ : syracuseStep 10255085 = 3845657) B3845657
theorem B1350447 : Blo 1348993 1350447 := bstep (se 1 (by rfl) ⟨1012835, by rfl⟩ : syracuseStep 1350447 = 2025671) B2025671
theorem B2882459 : Blo 1348993 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B1350555 : Blo 1348993 1350555 := bstep (se 1 (by rfl) ⟨1012916, by rfl⟩ : syracuseStep 1350555 = 2025833) B2025833
theorem B1350607 : Blo 1348993 1350607 := bstep (se 1 (by rfl) ⟨1012955, by rfl⟩ : syracuseStep 1350607 = 2025911) B2025911
theorem B3038183 : Blo 1348993 3038183 := bstep (se 1 (by rfl) ⟨2278637, by rfl⟩ : syracuseStep 3038183 = 4557275) B4557275
theorem B1350631 : Blo 1348993 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B3415031 : Blo 1348993 3415031 := bstep (se 1 (by rfl) ⟨2561273, by rfl⟩ : syracuseStep 3415031 = 5122547) B5122547
theorem B2464987 : Blo 1348993 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B1350943 : Blo 1348993 1350943 := bstep (se 1 (by rfl) ⟨1013207, by rfl⟩ : syracuseStep 1350943 = 2026415) B2026415
theorem B2882911 : Blo 1348993 2882911 := bstep (se 1 (by rfl) ⟨2162183, by rfl⟩ : syracuseStep 2882911 = 4324367) B4324367
theorem B3038561 : Blo 1348993 3038561 := bstep (se 2 (by rfl) ⟨1139460, by rfl⟩ : syracuseStep 3038561 = 2278921) B2278921
theorem B3038651 : Blo 1348993 3038651 := bstep (se 1 (by rfl) ⟨2278988, by rfl⟩ : syracuseStep 3038651 = 4557977) B4557977
theorem B27704825 : Blo 1348993 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B5127695 : Blo 1348993 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B3038777 : Blo 1348993 3038777 := bstep (se 2 (by rfl) ⟨1139541, by rfl⟩ : syracuseStep 3038777 = 2279083) B2279083
theorem B10247795 : Blo 1348993 10247795 := bstep (se 1 (by rfl) ⟨7685846, by rfl⟩ : syracuseStep 10247795 = 15371693) B15371693
theorem B24641171 : Blo 1348993 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B2432825 : Blo 1348993 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B14606153 : Blo 1348993 14606153 := bstep (se 2 (by rfl) ⟨5477307, by rfl⟩ : syracuseStep 14606153 = 10954615) B10954615
theorem B3841921 : Blo 1348993 3841921 := bstep (se 2 (by rfl) ⟨1440720, by rfl⟩ : syracuseStep 3841921 = 2881441) B2881441
theorem B2432975 : Blo 1348993 2432975 := bstep (se 1 (by rfl) ⟨1824731, by rfl⟩ : syracuseStep 2432975 = 3649463) B3649463
theorem B4554791 : Blo 1348993 4554791 := bstep (se 1 (by rfl) ⟨3416093, by rfl⟩ : syracuseStep 4554791 = 6832187) B6832187
theorem B8773691 : Blo 1348993 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B2023643 : Blo 1348993 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B2023655 : Blo 1348993 2023655 := bstep (se 1 (by rfl) ⟨1517741, by rfl⟩ : syracuseStep 2023655 = 3035483) B3035483
theorem B2023817 : Blo 1348993 2023817 := bstep (se 2 (by rfl) ⟨758931, by rfl⟩ : syracuseStep 2023817 = 1517863) B1517863
theorem B3842491 : Blo 1348993 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B3416519 : Blo 1348993 3416519 := bstep (se 1 (by rfl) ⟨2562389, by rfl⟩ : syracuseStep 3416519 = 5124779) B5124779
theorem B3039695 : Blo 1348993 3039695 := bstep (se 1 (by rfl) ⟨2279771, by rfl⟩ : syracuseStep 3039695 = 4559543) B4559543
theorem B7684571 : Blo 1348993 7684571 := bstep (se 1 (by rfl) ⟨5763428, by rfl⟩ : syracuseStep 7684571 = 11526857) B11526857
theorem B2023913 : Blo 1348993 2023913 := bstep (se 2 (by rfl) ⟨758967, by rfl⟩ : syracuseStep 2023913 = 1517935) B1517935
theorem B2277983 : Blo 1348993 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B2024039 : Blo 1348993 2024039 := bstep (se 1 (by rfl) ⟨1518029, by rfl⟩ : syracuseStep 2024039 = 3036059) B3036059
theorem B5767787 : Blo 1348993 5767787 := bstep (se 1 (by rfl) ⟨4325840, by rfl⟩ : syracuseStep 5767787 = 8651681) B8651681
theorem B4555439 : Blo 1348993 4555439 := bstep (se 1 (by rfl) ⟨3416579, by rfl⟩ : syracuseStep 4555439 = 6833159) B6833159
theorem B5128879 : Blo 1348993 5128879 := bstep (se 1 (by rfl) ⟨3846659, by rfl⟩ : syracuseStep 5128879 = 7693319) B7693319
theorem B6832835 : Blo 1348993 6832835 := bstep (se 1 (by rfl) ⟨5124626, by rfl⟩ : syracuseStep 6832835 = 10249253) B10249253
theorem B2024171 : Blo 1348993 2024171 := bstep (se 1 (by rfl) ⟨1518128, by rfl⟩ : syracuseStep 2024171 = 3036257) B3036257
theorem B2024201 : Blo 1348993 2024201 := bstep (se 2 (by rfl) ⟨759075, by rfl⟩ : syracuseStep 2024201 = 1518151) B1518151
theorem B2024303 : Blo 1348993 2024303 := bstep (se 1 (by rfl) ⟨1518227, by rfl⟩ : syracuseStep 2024303 = 3036455) B3036455
theorem B1581935 : Blo 1348993 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B4555763 : Blo 1348993 4555763 := bstep (se 1 (by rfl) ⟨3416822, by rfl⟩ : syracuseStep 4555763 = 6833645) B6833645
theorem B2434043 : Blo 1348993 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B3245081 : Blo 1348993 3245081 := bstep (se 2 (by rfl) ⟨1216905, by rfl⟩ : syracuseStep 3245081 = 2433811) B2433811
theorem B2024555 : Blo 1348993 2024555 := bstep (se 1 (by rfl) ⟨1518416, by rfl⟩ : syracuseStep 2024555 = 3036833) B3036833
theorem B7693501 : Blo 1348993 7693501 := bstep (se 3 (by rfl) ⟨1442531, by rfl⟩ : syracuseStep 7693501 = 2885063) B2885063
theorem B2024795 : Blo 1348993 2024795 := bstep (se 1 (by rfl) ⟨1518596, by rfl⟩ : syracuseStep 2024795 = 3037193) B3037193
theorem B2434475 : Blo 1348993 2434475 := bstep (se 1 (by rfl) ⟨1825856, by rfl⟩ : syracuseStep 2434475 = 3651713) B3651713
theorem B4556303 : Blo 1348993 4556303 := bstep (se 1 (by rfl) ⟨3417227, by rfl⟩ : syracuseStep 4556303 = 6834455) B6834455
theorem B2025071 : Blo 1348993 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B3286649 : Blo 1348993 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B15386273 : Blo 1348993 15386273 := bstep (se 2 (by rfl) ⟨5769852, by rfl⟩ : syracuseStep 15386273 = 11539705) B11539705
theorem B2025143 : Blo 1348993 2025143 := bstep (se 1 (by rfl) ⟨1518857, by rfl⟩ : syracuseStep 2025143 = 3037715) B3037715
theorem B2025179 : Blo 1348993 2025179 := bstep (se 1 (by rfl) ⟨1518884, by rfl⟩ : syracuseStep 2025179 = 3037769) B3037769
theorem B3843881 : Blo 1348993 3843881 := bstep (se 2 (by rfl) ⟨1441455, by rfl⟩ : syracuseStep 3843881 = 2882911) B2882911
theorem B2025353 : Blo 1348993 2025353 := bstep (se 2 (by rfl) ⟨759507, by rfl⟩ : syracuseStep 2025353 = 1519015) B1519015
theorem B2025455 : Blo 1348993 2025455 := bstep (se 1 (by rfl) ⟨1519091, by rfl⟩ : syracuseStep 2025455 = 3038183) B3038183
theorem B2279407 : Blo 1348993 2279407 := bstep (se 1 (by rfl) ⟨1709555, by rfl⟩ : syracuseStep 2279407 = 3419111) B3419111
theorem B5769427 : Blo 1348993 5769427 := bstep (se 1 (by rfl) ⟨4327070, by rfl⟩ : syracuseStep 5769427 = 8654141) B8654141
theorem B2279657 : Blo 1348993 2279657 := bstep (se 2 (by rfl) ⟨854871, by rfl⟩ : syracuseStep 2279657 = 1709743) B1709743
theorem B2025707 : Blo 1348993 2025707 := bstep (se 1 (by rfl) ⟨1519280, by rfl⟩ : syracuseStep 2025707 = 3038561) B3038561
theorem B17287415 : Blo 1348993 17287415 := bstep (se 1 (by rfl) ⟨12965561, by rfl⟩ : syracuseStep 17287415 = 25931123) B25931123
theorem B2025767 : Blo 1348993 2025767 := bstep (se 1 (by rfl) ⟨1519325, by rfl⟩ : syracuseStep 2025767 = 3038651) B3038651
theorem B4557113 : Blo 1348993 4557113 := bstep (se 2 (by rfl) ⟨1708917, by rfl⟩ : syracuseStep 4557113 = 3417835) B3417835
theorem B3418463 : Blo 1348993 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B2025851 : Blo 1348993 2025851 := bstep (se 1 (by rfl) ⟨1519388, by rfl⟩ : syracuseStep 2025851 = 3038777) B3038777
theorem B16427447 : Blo 1348993 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B5122561 : Blo 1348993 5122561 := bstep (se 2 (by rfl) ⟨1920960, by rfl⟩ : syracuseStep 5122561 = 3841921) B3841921
theorem B77826581 : Blo 1348993 77826581 := bstep (se 6 (by rfl) ⟨1824060, by rfl⟩ : syracuseStep 77826581 = 3648121) B3648121
theorem B4557383 : Blo 1348993 4557383 := bstep (se 1 (by rfl) ⟨3418037, by rfl⟩ : syracuseStep 4557383 = 6836075) B6836075
theorem B2026121 : Blo 1348993 2026121 := bstep (se 2 (by rfl) ⟨759795, by rfl⟩ : syracuseStep 2026121 = 1519591) B1519591
theorem B2026295 : Blo 1348993 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B2026331 : Blo 1348993 2026331 := bstep (se 1 (by rfl) ⟨1519748, by rfl⟩ : syracuseStep 2026331 = 3039497) B3039497
theorem B2026475 : Blo 1348993 2026475 := bstep (se 1 (by rfl) ⟨1519856, by rfl⟩ : syracuseStep 2026475 = 3039713) B3039713
theorem B33746321 : Blo 1348993 33746321 := bstep (se 2 (by rfl) ⟨12654870, by rfl⟩ : syracuseStep 33746321 = 25309741) B25309741
theorem B4558409 : Blo 1348993 4558409 := bstep (se 2 (by rfl) ⟨1709403, by rfl⟩ : syracuseStep 4558409 = 3418807) B3418807
theorem B1519195 : Blo 1348993 1519195 := bstep (se 1 (by rfl) ⟨1139396, by rfl⟩ : syracuseStep 1519195 = 2278793) B2278793
theorem B7687943 : Blo 1348993 7687943 := bstep (se 1 (by rfl) ⟨5765957, by rfl⟩ : syracuseStep 7687943 = 11531915) B11531915
theorem B19468127 : Blo 1348993 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B1519483 : Blo 1348993 1519483 := bstep (se 1 (by rfl) ⟨1139612, by rfl⟩ : syracuseStep 1519483 = 2279225) B2279225
theorem B29192075 : Blo 1348993 29192075 := bstep (se 1 (by rfl) ⟨21894056, by rfl⟩ : syracuseStep 29192075 = 43788113) B43788113
theorem B32452757 : Blo 1348993 32452757 := bstep (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) B1521223
theorem B3035447 : Blo 1348993 3035447 := bstep (se 1 (by rfl) ⟨2276585, by rfl⟩ : syracuseStep 3035447 = 4553171) B4553171
theorem B3035519 : Blo 1348993 3035519 := bstep (se 1 (by rfl) ⟨2276639, by rfl⟩ : syracuseStep 3035519 = 4553279) B4553279
theorem B6836723 : Blo 1348993 6836723 := bstep (se 1 (by rfl) ⟨5127542, by rfl⟩ : syracuseStep 6836723 = 10255085) B10255085
theorem B2191865 : Blo 1348993 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B3846649 : Blo 1348993 3846649 := bstep (se 2 (by rfl) ⟨1442493, by rfl⟩ : syracuseStep 3846649 = 2884987) B2884987
theorem B1921639 : Blo 1348993 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B4321907 : Blo 1348993 4321907 := bstep (se 1 (by rfl) ⟨3241430, by rfl⟩ : syracuseStep 4321907 = 6482861) B6482861
theorem B18469883 : Blo 1348993 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B3077227 : Blo 1348993 3077227 := bstep (se 1 (by rfl) ⟨2307920, by rfl⟩ : syracuseStep 3077227 = 4615841) B4615841
theorem B4617323 : Blo 1348993 4617323 := bstep (se 1 (by rfl) ⟨3462992, by rfl⟩ : syracuseStep 4617323 = 6925985) B6925985
theorem B9737435 : Blo 1348993 9737435 := bstep (se 1 (by rfl) ⟨7303076, by rfl⟩ : syracuseStep 9737435 = 14606153) B14606153
theorem B46740797 : Blo 1348993 46740797 := bstep (se 3 (by rfl) ⟨8763899, by rfl⟩ : syracuseStep 46740797 = 17527799) B17527799
theorem B1349019 : Blo 1348993 1349019 := bstep (se 1 (by rfl) ⟨1011764, by rfl⟩ : syracuseStep 1349019 = 2023529) B2023529
theorem B3036743 : Blo 1348993 3036743 := bstep (se 1 (by rfl) ⟨2277557, by rfl⟩ : syracuseStep 3036743 = 4555115) B4555115
theorem B1349231 : Blo 1348993 1349231 := bstep (se 1 (by rfl) ⟨1011923, by rfl⟩ : syracuseStep 1349231 = 2023847) B2023847
theorem B1349287 : Blo 1348993 1349287 := bstep (se 1 (by rfl) ⟨1011965, by rfl⟩ : syracuseStep 1349287 = 2023931) B2023931
theorem B1922783 : Blo 1348993 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B1349371 : Blo 1348993 1349371 := bstep (se 1 (by rfl) ⟨1012028, by rfl⟩ : syracuseStep 1349371 = 2024057) B2024057
theorem B3036923 : Blo 1348993 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B1349407 : Blo 1348993 1349407 := bstep (se 1 (by rfl) ⟨1012055, by rfl⟩ : syracuseStep 1349407 = 2024111) B2024111
theorem B1349439 : Blo 1348993 1349439 := bstep (se 1 (by rfl) ⟨1012079, by rfl⟩ : syracuseStep 1349439 = 2024159) B2024159
theorem B7395311 : Blo 1348993 7395311 := bstep (se 1 (by rfl) ⟨5546483, by rfl⟩ : syracuseStep 7395311 = 11092967) B11092967
theorem B1349615 : Blo 1348993 1349615 := bstep (se 1 (by rfl) ⟨1012211, by rfl⟩ : syracuseStep 1349615 = 2024423) B2024423
theorem B2406391 : Blo 1348993 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B20781137 : Blo 1348993 20781137 := bstep (se 2 (by rfl) ⟨7792926, by rfl⟩ : syracuseStep 20781137 = 15585853) B15585853
theorem B2562131 : Blo 1348993 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B9730145 : Blo 1348993 9730145 := bstep (se 2 (by rfl) ⟨3648804, by rfl⟩ : syracuseStep 9730145 = 7297609) B7297609
theorem B1349787 : Blo 1348993 1349787 := bstep (se 1 (by rfl) ⟨1012340, by rfl⟩ : syracuseStep 1349787 = 2024681) B2024681
theorem B1349823 : Blo 1348993 1349823 := bstep (se 1 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 1349823 = 2024735) B2024735
theorem B10246337 : Blo 1348993 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B8771827 : Blo 1348993 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B10254599 : Blo 1348993 10254599 := bstep (se 1 (by rfl) ⟨7690949, by rfl⟩ : syracuseStep 10254599 = 15381899) B15381899
theorem B3037481 : Blo 1348993 3037481 := bstep (se 2 (by rfl) ⟨1139055, by rfl⟩ : syracuseStep 3037481 = 2278111) B2278111
theorem B1349935 : Blo 1348993 1349935 := bstep (se 1 (by rfl) ⟨1012451, by rfl⟩ : syracuseStep 1349935 = 2024903) B2024903
theorem B8772029 : Blo 1348993 8772029 := bstep (se 3 (by rfl) ⟨1644755, by rfl⟩ : syracuseStep 8772029 = 3289511) B3289511
theorem B5765651 : Blo 1348993 5765651 := bstep (se 1 (by rfl) ⟨4324238, by rfl⟩ : syracuseStep 5765651 = 8648477) B8648477
theorem B1350171 : Blo 1348993 1350171 := bstep (se 1 (by rfl) ⟨1012628, by rfl⟩ : syracuseStep 1350171 = 2025257) B2025257
theorem B1350175 : Blo 1348993 1350175 := bstep (se 1 (by rfl) ⟨1012631, by rfl⟩ : syracuseStep 1350175 = 2025263) B2025263
theorem B11541041 : Blo 1348993 11541041 := bstep (se 2 (by rfl) ⟨4327890, by rfl⟩ : syracuseStep 11541041 = 8655781) B8655781
theorem B3242843 : Blo 1348993 3242843 := bstep (se 1 (by rfl) ⟨2432132, by rfl⟩ : syracuseStep 3242843 = 4864265) B4864265
theorem B1350491 : Blo 1348993 1350491 := bstep (se 1 (by rfl) ⟨1012868, by rfl⟩ : syracuseStep 1350491 = 2025737) B2025737
theorem B3038057 : Blo 1348993 3038057 := bstep (se 2 (by rfl) ⟨1139271, by rfl⟩ : syracuseStep 3038057 = 2278543) B2278543
theorem B3038111 : Blo 1348993 3038111 := bstep (se 1 (by rfl) ⟨2278583, by rfl⟩ : syracuseStep 3038111 = 4557167) B4557167
theorem B1350559 : Blo 1348993 1350559 := bstep (se 1 (by rfl) ⟨1012919, by rfl⟩ : syracuseStep 1350559 = 2025839) B2025839
theorem B6159311 : Blo 1348993 6159311 := bstep (se 1 (by rfl) ⟨4619483, by rfl⟩ : syracuseStep 6159311 = 9238967) B9238967
theorem B7683113 : Blo 1348993 7683113 := bstep (se 2 (by rfl) ⟨2881167, by rfl⟩ : syracuseStep 7683113 = 5762335) B5762335
theorem B3415081 : Blo 1348993 3415081 := bstep (se 2 (by rfl) ⟨1280655, by rfl⟩ : syracuseStep 3415081 = 2561311) B2561311
theorem B8207401 : Blo 1348993 8207401 := bstep (se 2 (by rfl) ⟨3077775, by rfl⟩ : syracuseStep 8207401 = 6155551) B6155551
theorem B5127209 : Blo 1348993 5127209 := bstep (se 2 (by rfl) ⟨1922703, by rfl⟩ : syracuseStep 5127209 = 3845407) B3845407
theorem B1350703 : Blo 1348993 1350703 := bstep (se 1 (by rfl) ⟨1013027, by rfl⟩ : syracuseStep 1350703 = 2026055) B2026055
theorem B14605379 : Blo 1348993 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B5127239 : Blo 1348993 5127239 := bstep (se 1 (by rfl) ⟨3845429, by rfl⟩ : syracuseStep 5127239 = 7690859) B7690859
theorem B1350727 : Blo 1348993 1350727 := bstep (se 1 (by rfl) ⟨1013045, by rfl⟩ : syracuseStep 1350727 = 2026091) B2026091
theorem B3415223 : Blo 1348993 3415223 := bstep (se 1 (by rfl) ⟨2561417, by rfl⟩ : syracuseStep 3415223 = 5122835) B5122835
theorem B2563255 : Blo 1348993 2563255 := bstep (se 1 (by rfl) ⟨1922441, by rfl⟩ : syracuseStep 2563255 = 3844883) B3844883
theorem B1350879 : Blo 1348993 1350879 := bstep (se 1 (by rfl) ⟨1013159, by rfl⟩ : syracuseStep 1350879 = 2026319) B2026319
theorem B4553981 : Blo 1348993 4553981 := bstep (se 3 (by rfl) ⟨853871, by rfl⟩ : syracuseStep 4553981 = 1707743) B1707743
theorem B2276687 : Blo 1348993 2276687 := bstep (se 1 (by rfl) ⟨1707515, by rfl⟩ : syracuseStep 2276687 = 3415031) B3415031
theorem B2563559 : Blo 1348993 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B6831863 : Blo 1348993 6831863 := bstep (se 1 (by rfl) ⟨5123897, by rfl⟩ : syracuseStep 6831863 = 10247795) B10247795
theorem B2465555 : Blo 1348993 2465555 := bstep (se 1 (by rfl) ⟨1849166, by rfl⟩ : syracuseStep 2465555 = 3698333) B3698333
theorem B7298839 : Blo 1348993 7298839 := bstep (se 1 (by rfl) ⟨5474129, by rfl⟩ : syracuseStep 7298839 = 10948259) B10948259
theorem B3039047 : Blo 1348993 3039047 := bstep (se 1 (by rfl) ⟨2279285, by rfl⟩ : syracuseStep 3039047 = 4558571) B4558571
theorem B1621883 : Blo 1348993 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B6487933 : Blo 1348993 6487933 := bstep (se 3 (by rfl) ⟨1216487, by rfl⟩ : syracuseStep 6487933 = 2432975) B2432975
theorem B21635171 : Blo 1348993 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B23396509 : Blo 1348993 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B2023631 : Blo 1348993 2023631 := bstep (se 1 (by rfl) ⟨1517723, by rfl⟩ : syracuseStep 2023631 = 3035447) B3035447
theorem B6832349 : Blo 1348993 6832349 := bstep (se 3 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 6832349 = 2562131) B2562131
theorem B2023679 : Blo 1348993 2023679 := bstep (se 1 (by rfl) ⟨1517759, by rfl⟩ : syracuseStep 2023679 = 3035519) B3035519
theorem B7692569 : Blo 1348993 7692569 := bstep (se 2 (by rfl) ⟨2884713, by rfl⟩ : syracuseStep 7692569 = 5769427) B5769427
theorem B2277679 : Blo 1348993 2277679 := bstep (se 1 (by rfl) ⟨1708259, by rfl⟩ : syracuseStep 2277679 = 3416519) B3416519
theorem B4555223 : Blo 1348993 4555223 := bstep (se 1 (by rfl) ⟨3416417, by rfl⟩ : syracuseStep 4555223 = 6832835) B6832835
theorem B5128865 : Blo 1348993 5128865 := bstep (se 2 (by rfl) ⟨1923324, by rfl⟩ : syracuseStep 5128865 = 3846649) B3846649
theorem B12313255 : Blo 1348993 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B1622695 : Blo 1348993 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B2024495 : Blo 1348993 2024495 := bstep (se 1 (by rfl) ⟨1518371, by rfl⟩ : syracuseStep 2024495 = 3036743) B3036743
theorem B10257515 : Blo 1348993 10257515 := bstep (se 1 (by rfl) ⟨7693136, by rfl⟩ : syracuseStep 10257515 = 15386273) B15386273
theorem B2024615 : Blo 1348993 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B13854091 : Blo 1348993 13854091 := bstep (se 1 (by rfl) ⟨10390568, by rfl⟩ : syracuseStep 13854091 = 20781137) B20781137
theorem B2024987 : Blo 1348993 2024987 := bstep (se 1 (by rfl) ⟨1518740, by rfl⟩ : syracuseStep 2024987 = 3037481) B3037481
theorem B2278975 : Blo 1348993 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B3417673 : Blo 1348993 3417673 := bstep (se 2 (by rfl) ⟨1281627, by rfl⟩ : syracuseStep 3417673 = 2563255) B2563255
theorem B10258001 : Blo 1348993 10258001 := bstep (se 2 (by rfl) ⟨3846750, by rfl⟩ : syracuseStep 10258001 = 7693501) B7693501
theorem B3843767 : Blo 1348993 3843767 := bstep (se 1 (by rfl) ⟨2882825, by rfl⟩ : syracuseStep 3843767 = 5765651) B5765651
theorem B7694027 : Blo 1348993 7694027 := bstep (se 1 (by rfl) ⟨5770520, by rfl⟩ : syracuseStep 7694027 = 11541041) B11541041
theorem B2025371 : Blo 1348993 2025371 := bstep (se 1 (by rfl) ⟨1519028, by rfl⟩ : syracuseStep 2025371 = 3038057) B3038057
theorem B2025407 : Blo 1348993 2025407 := bstep (se 1 (by rfl) ⟨1519055, by rfl⟩ : syracuseStep 2025407 = 3038111) B3038111
theorem B4106207 : Blo 1348993 4106207 := bstep (se 1 (by rfl) ⟨3079655, by rfl⟩ : syracuseStep 4106207 = 6159311) B6159311
theorem B5122075 : Blo 1348993 5122075 := bstep (se 1 (by rfl) ⟨3841556, by rfl⟩ : syracuseStep 5122075 = 7683113) B7683113
theorem B3418139 : Blo 1348993 3418139 := bstep (se 1 (by rfl) ⟨2563604, by rfl⟩ : syracuseStep 3418139 = 5127209) B5127209
theorem B3418159 : Blo 1348993 3418159 := bstep (se 1 (by rfl) ⟨2563619, by rfl⟩ : syracuseStep 3418159 = 5127239) B5127239
theorem B2025593 : Blo 1348993 2025593 := bstep (se 2 (by rfl) ⟨759597, by rfl⟩ : syracuseStep 2025593 = 1519195) B1519195
theorem B1517791 : Blo 1348993 1517791 := bstep (se 1 (by rfl) ⟨1138343, by rfl⟩ : syracuseStep 1517791 = 2276687) B2276687
theorem B22497547 : Blo 1348993 22497547 := bstep (se 1 (by rfl) ⟨16873160, by rfl⟩ : syracuseStep 22497547 = 33746321) B33746321
theorem B2025977 : Blo 1348993 2025977 := bstep (se 2 (by rfl) ⟨759741, by rfl⟩ : syracuseStep 2025977 = 1519483) B1519483
theorem B2026031 : Blo 1348993 2026031 := bstep (se 1 (by rfl) ⟨1519523, by rfl⟩ : syracuseStep 2026031 = 3039047) B3039047
theorem B12978751 : Blo 1348993 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B19720829 : Blo 1348993 19720829 := bstep (se 3 (by rfl) ⟨3697655, by rfl⟩ : syracuseStep 19720829 = 7395311) B7395311
theorem B8653549 : Blo 1348993 8653549 := bstep (se 3 (by rfl) ⟨1622540, by rfl⟩ : syracuseStep 8653549 = 3245081) B3245081
theorem B2026463 : Blo 1348993 2026463 := bstep (se 1 (by rfl) ⟨1519847, by rfl⟩ : syracuseStep 2026463 = 3039695) B3039695
theorem B5123047 : Blo 1348993 5123047 := bstep (se 1 (by rfl) ⟨3842285, by rfl⟩ : syracuseStep 5123047 = 7684571) B7684571
theorem B4557815 : Blo 1348993 4557815 := bstep (se 1 (by rfl) ⟨3418361, by rfl⟩ : syracuseStep 4557815 = 6836723) B6836723
theorem B1518655 : Blo 1348993 1518655 := bstep (se 1 (by rfl) ⟨1138991, by rfl⟩ : syracuseStep 1518655 = 2277983) B2277983
theorem B3845191 : Blo 1348993 3845191 := bstep (se 1 (by rfl) ⟨2883893, by rfl⟩ : syracuseStep 3845191 = 5767787) B5767787
theorem B5123321 : Blo 1348993 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B2191099 : Blo 1348993 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B6491933 : Blo 1348993 6491933 := bstep (se 3 (by rfl) ⟨1217237, by rfl⟩ : syracuseStep 6491933 = 2434475) B2434475
theorem B5844973 : Blo 1348993 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B1519771 : Blo 1348993 1519771 := bstep (se 1 (by rfl) ⟨1139828, by rfl⟩ : syracuseStep 1519771 = 2279657) B2279657
theorem B6836399 : Blo 1348993 6836399 := bstep (se 1 (by rfl) ⟨5127299, by rfl⟩ : syracuseStep 6836399 = 10254599) B10254599
theorem B51884387 : Blo 1348993 51884387 := bstep (se 1 (by rfl) ⟨38913290, by rfl⟩ : syracuseStep 51884387 = 77826581) B77826581
theorem B9736919 : Blo 1348993 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B6574813 : Blo 1348993 6574813 := bstep (se 3 (by rfl) ⟨1232777, by rfl⟩ : syracuseStep 6574813 = 2465555) B2465555
theorem B3035987 : Blo 1348993 3035987 := bstep (se 1 (by rfl) ⟨2276990, by rfl⟩ : syracuseStep 3035987 = 4553981) B4553981
theorem B1709039 : Blo 1348993 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B51336341 : Blo 1348993 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B5125295 : Blo 1348993 5125295 := bstep (se 1 (by rfl) ⟨3843971, by rfl⟩ : syracuseStep 5125295 = 7687943) B7687943
theorem B19461383 : Blo 1348993 19461383 := bstep (se 1 (by rfl) ⟨14596037, by rfl⟩ : syracuseStep 19461383 = 29192075) B29192075
theorem B3036527 : Blo 1348993 3036527 := bstep (se 1 (by rfl) ⟨2277395, by rfl⟩ : syracuseStep 3036527 = 4554791) B4554791
theorem B1349095 : Blo 1348993 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B1349103 : Blo 1348993 1349103 := bstep (se 1 (by rfl) ⟨1011827, by rfl⟩ : syracuseStep 1349103 = 2023655) B2023655
theorem B1349211 : Blo 1348993 1349211 := bstep (se 1 (by rfl) ⟨1011908, by rfl⟩ : syracuseStep 1349211 = 2023817) B2023817
theorem B11695769 : Blo 1348993 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B1349275 : Blo 1348993 1349275 := bstep (se 1 (by rfl) ⟨1011956, by rfl⟩ : syracuseStep 1349275 = 2023913) B2023913
theorem B1349359 : Blo 1348993 1349359 := bstep (se 1 (by rfl) ⟨1012019, by rfl⟩ : syracuseStep 1349359 = 2024039) B2024039
theorem B2881271 : Blo 1348993 2881271 := bstep (se 1 (by rfl) ⟨2160953, by rfl⟩ : syracuseStep 2881271 = 4321907) B4321907
theorem B3036959 : Blo 1348993 3036959 := bstep (se 1 (by rfl) ⟨2277719, by rfl⟩ : syracuseStep 3036959 = 4555439) B4555439
theorem B1349447 : Blo 1348993 1349447 := bstep (se 1 (by rfl) ⟨1012085, by rfl⟩ : syracuseStep 1349447 = 2024171) B2024171
theorem B1349467 : Blo 1348993 1349467 := bstep (se 1 (by rfl) ⟨1012100, by rfl⟩ : syracuseStep 1349467 = 2024201) B2024201
theorem B25966493 : Blo 1348993 25966493 := bstep (se 3 (by rfl) ⟨4868717, by rfl⟩ : syracuseStep 25966493 = 9737435) B9737435
theorem B1349535 : Blo 1348993 1349535 := bstep (se 1 (by rfl) ⟨1012151, by rfl⟩ : syracuseStep 1349535 = 2024303) B2024303
theorem B3037175 : Blo 1348993 3037175 := bstep (se 1 (by rfl) ⟨2277881, by rfl⟩ : syracuseStep 3037175 = 4555763) B4555763
theorem B6830081 : Blo 1348993 6830081 := bstep (se 2 (by rfl) ⟨2561280, by rfl⟩ : syracuseStep 6830081 = 5122561) B5122561
theorem B3078215 : Blo 1348993 3078215 := bstep (se 1 (by rfl) ⟨2308661, by rfl⟩ : syracuseStep 3078215 = 4617323) B4617323
theorem B1349703 : Blo 1348993 1349703 := bstep (se 1 (by rfl) ⟨1012277, by rfl⟩ : syracuseStep 1349703 = 2024555) B2024555
theorem B2562185 : Blo 1348993 2562185 := bstep (se 2 (by rfl) ⟨960819, by rfl⟩ : syracuseStep 2562185 = 1921639) B1921639
theorem B31160531 : Blo 1348993 31160531 := bstep (se 1 (by rfl) ⟨23370398, by rfl⟩ : syracuseStep 31160531 = 46740797) B46740797
theorem B1349863 : Blo 1348993 1349863 := bstep (se 1 (by rfl) ⟨1012397, by rfl⟩ : syracuseStep 1349863 = 2024795) B2024795
theorem B6838505 : Blo 1348993 6838505 := bstep (se 2 (by rfl) ⟨2564439, by rfl⟩ : syracuseStep 6838505 = 5128879) B5128879
theorem B3037535 : Blo 1348993 3037535 := bstep (se 1 (by rfl) ⟨2278151, by rfl⟩ : syracuseStep 3037535 = 4556303) B4556303
theorem B1350047 : Blo 1348993 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B1350095 : Blo 1348993 1350095 := bstep (se 1 (by rfl) ⟨1012571, by rfl⟩ : syracuseStep 1350095 = 2025143) B2025143
theorem B1350119 : Blo 1348993 1350119 := bstep (se 1 (by rfl) ⟨1012589, by rfl⟩ : syracuseStep 1350119 = 2025179) B2025179
theorem B2562587 : Blo 1348993 2562587 := bstep (se 1 (by rfl) ⟨1921940, by rfl⟩ : syracuseStep 2562587 = 3843881) B3843881
theorem B1350235 : Blo 1348993 1350235 := bstep (se 1 (by rfl) ⟨1012676, by rfl⟩ : syracuseStep 1350235 = 2025353) B2025353
theorem B1350303 : Blo 1348993 1350303 := bstep (se 1 (by rfl) ⟨1012727, by rfl⟩ : syracuseStep 1350303 = 2025455) B2025455
theorem B4553441 : Blo 1348993 4553441 := bstep (se 2 (by rfl) ⟨1707540, by rfl⟩ : syracuseStep 4553441 = 3415081) B3415081
theorem B10943201 : Blo 1348993 10943201 := bstep (se 2 (by rfl) ⟨4103700, by rfl⟩ : syracuseStep 10943201 = 8207401) B8207401
theorem B6486763 : Blo 1348993 6486763 := bstep (se 1 (by rfl) ⟨4865072, by rfl⟩ : syracuseStep 6486763 = 9730145) B9730145
theorem B6830891 : Blo 1348993 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B4102969 : Blo 1348993 4102969 := bstep (se 2 (by rfl) ⟨1538613, by rfl⟩ : syracuseStep 4102969 = 3077227) B3077227
theorem B1350471 : Blo 1348993 1350471 := bstep (se 1 (by rfl) ⟨1012853, by rfl⟩ : syracuseStep 1350471 = 2025707) B2025707
theorem B11524943 : Blo 1348993 11524943 := bstep (se 1 (by rfl) ⟨8643707, by rfl⟩ : syracuseStep 11524943 = 17287415) B17287415
theorem B1350511 : Blo 1348993 1350511 := bstep (se 1 (by rfl) ⟨1012883, by rfl⟩ : syracuseStep 1350511 = 2025767) B2025767
theorem B3038075 : Blo 1348993 3038075 := bstep (se 1 (by rfl) ⟨2278556, by rfl⟩ : syracuseStep 3038075 = 4557113) B4557113
theorem B1350567 : Blo 1348993 1350567 := bstep (se 1 (by rfl) ⟨1012925, by rfl⟩ : syracuseStep 1350567 = 2025851) B2025851
theorem B10951631 : Blo 1348993 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B5848019 : Blo 1348993 5848019 := bstep (se 1 (by rfl) ⟨4386014, by rfl⟩ : syracuseStep 5848019 = 8772029) B8772029
theorem B3038255 : Blo 1348993 3038255 := bstep (se 1 (by rfl) ⟨2278691, by rfl⟩ : syracuseStep 3038255 = 4557383) B4557383
theorem B1350747 : Blo 1348993 1350747 := bstep (se 1 (by rfl) ⟨1013060, by rfl⟩ : syracuseStep 1350747 = 2026121) B2026121
theorem B1350863 : Blo 1348993 1350863 := bstep (se 1 (by rfl) ⟨1013147, by rfl⟩ : syracuseStep 1350863 = 2026295) B2026295
theorem B2161895 : Blo 1348993 2161895 := bstep (se 1 (by rfl) ⟨1621421, by rfl⟩ : syracuseStep 2161895 = 3242843) B3242843
theorem B1350887 : Blo 1348993 1350887 := bstep (se 1 (by rfl) ⟨1013165, by rfl⟩ : syracuseStep 1350887 = 2026331) B2026331
theorem B5127421 : Blo 1348993 5127421 := bstep (se 3 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 5127421 = 1922783) B1922783
theorem B1350983 : Blo 1348993 1350983 := bstep (se 1 (by rfl) ⟨1013237, by rfl⟩ : syracuseStep 1350983 = 2026475) B2026475
theorem B2276815 : Blo 1348993 2276815 := bstep (se 1 (by rfl) ⟨1707611, by rfl⟩ : syracuseStep 2276815 = 3415223) B3415223
theorem B4218493 : Blo 1348993 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B4325021 : Blo 1348993 4325021 := bstep (se 3 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 4325021 = 1621883) B1621883
theorem B9731785 : Blo 1348993 9731785 := bstep (se 2 (by rfl) ⟨3649419, by rfl⟩ : syracuseStep 9731785 = 7298839) B7298839
theorem B3038939 : Blo 1348993 3038939 := bstep (se 1 (by rfl) ⟨2279204, by rfl⟩ : syracuseStep 3038939 = 4558409) B4558409
theorem B4554575 : Blo 1348993 4554575 := bstep (se 1 (by rfl) ⟨3415931, by rfl⟩ : syracuseStep 4554575 = 6831863) B6831863
theorem B8650577 : Blo 1348993 8650577 := bstep (se 2 (by rfl) ⟨3243966, by rfl⟩ : syracuseStep 8650577 = 6487933) B6487933
theorem B3039209 : Blo 1348993 3039209 := bstep (se 2 (by rfl) ⟨1139703, by rfl⟩ : syracuseStep 3039209 = 2279407) B2279407
theorem B4554899 : Blo 1348993 4554899 := bstep (se 1 (by rfl) ⟨3416174, by rfl⟩ : syracuseStep 4554899 = 6832349) B6832349
theorem B5128379 : Blo 1348993 5128379 := bstep (se 1 (by rfl) ⟨3846284, by rfl⟩ : syracuseStep 5128379 = 7692569) B7692569
theorem B2023721 : Blo 1348993 2023721 := bstep (se 2 (by rfl) ⟨758895, by rfl⟩ : syracuseStep 2023721 = 1517791) B1517791
theorem B2023991 : Blo 1348993 2023991 := bstep (se 1 (by rfl) ⟨1517993, by rfl⟩ : syracuseStep 2023991 = 3035987) B3035987
theorem B3416863 : Blo 1348993 3416863 := bstep (se 1 (by rfl) ⟨2562647, by rfl⟩ : syracuseStep 3416863 = 5125295) B5125295
theorem B124781381 : Blo 1348993 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B16417673 : Blo 1348993 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B2163593 : Blo 1348993 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B2024351 : Blo 1348993 2024351 := bstep (se 1 (by rfl) ⟨1518263, by rfl⟩ : syracuseStep 2024351 = 3036527) B3036527
theorem B5129351 : Blo 1348993 5129351 := bstep (se 1 (by rfl) ⟨3847013, by rfl⟩ : syracuseStep 5129351 = 7694027) B7694027
theorem B2024639 : Blo 1348993 2024639 := bstep (se 1 (by rfl) ⟨1518479, by rfl⟩ : syracuseStep 2024639 = 3036959) B3036959
theorem B17310995 : Blo 1348993 17310995 := bstep (se 1 (by rfl) ⟨12983246, by rfl⟩ : syracuseStep 17310995 = 25966493) B25966493
theorem B2737471 : Blo 1348993 2737471 := bstep (se 1 (by rfl) ⟨2053103, by rfl⟩ : syracuseStep 2737471 = 4106207) B4106207
theorem B2024783 : Blo 1348993 2024783 := bstep (se 1 (by rfl) ⟨1518587, by rfl⟩ : syracuseStep 2024783 = 3037175) B3037175
theorem B2278759 : Blo 1348993 2278759 := bstep (se 1 (by rfl) ⟨1709069, by rfl⟩ : syracuseStep 2278759 = 3418139) B3418139
theorem B2024873 : Blo 1348993 2024873 := bstep (se 2 (by rfl) ⟨759327, by rfl⟩ : syracuseStep 2024873 = 1518655) B1518655
theorem B2025023 : Blo 1348993 2025023 := bstep (se 1 (by rfl) ⟨1518767, by rfl⟩ : syracuseStep 2025023 = 3037535) B3037535
theorem B2025383 : Blo 1348993 2025383 := bstep (se 1 (by rfl) ⟨1519037, by rfl⟩ : syracuseStep 2025383 = 3038075) B3038075
theorem B7301087 : Blo 1348993 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B2025503 : Blo 1348993 2025503 := bstep (se 1 (by rfl) ⟨1519127, by rfl⟩ : syracuseStep 2025503 = 3038255) B3038255
theorem B4556897 : Blo 1348993 4556897 := bstep (se 2 (by rfl) ⟨1708836, by rfl⟩ : syracuseStep 4556897 = 3417673) B3417673
theorem B2025959 : Blo 1348993 2025959 := bstep (se 1 (by rfl) ⟨1519469, by rfl⟩ : syracuseStep 2025959 = 3038939) B3038939
theorem B4327955 : Blo 1348993 4327955 := bstep (se 1 (by rfl) ⟨3245966, by rfl⟩ : syracuseStep 4327955 = 6491933) B6491933
theorem B4557437 : Blo 1348993 4557437 := bstep (se 3 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 4557437 = 1709039) B1709039
theorem B7793297 : Blo 1348993 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B2026139 : Blo 1348993 2026139 := bstep (se 1 (by rfl) ⟨1519604, by rfl⟩ : syracuseStep 2026139 = 3039209) B3039209
theorem B4557545 : Blo 1348993 4557545 := bstep (se 2 (by rfl) ⟨1709079, by rfl⟩ : syracuseStep 4557545 = 3418159) B3418159
theorem B4557599 : Blo 1348993 4557599 := bstep (se 1 (by rfl) ⟨3418199, by rfl⟩ : syracuseStep 4557599 = 6836399) B6836399
theorem B2026361 : Blo 1348993 2026361 := bstep (se 2 (by rfl) ⟨759885, by rfl⟩ : syracuseStep 2026361 = 1519771) B1519771
theorem B34589591 : Blo 1348993 34589591 := bstep (se 1 (by rfl) ⟨25942193, by rfl⟩ : syracuseStep 34589591 = 51884387) B51884387
theorem B3419243 : Blo 1348993 3419243 := bstep (se 1 (by rfl) ⟨2564432, by rfl⟩ : syracuseStep 3419243 = 5128865) B5128865
theorem B6491279 : Blo 1348993 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B17305001 : Blo 1348993 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B11538065 : Blo 1348993 11538065 := bstep (se 2 (by rfl) ⟨4326774, by rfl⟩ : syracuseStep 11538065 = 8653549) B8653549
theorem B1920847 : Blo 1348993 1920847 := bstep (se 1 (by rfl) ⟨1440635, by rfl⟩ : syracuseStep 1920847 = 2881271) B2881271
theorem B2052143 : Blo 1348993 2052143 := bstep (se 1 (by rfl) ⟨1539107, by rfl⟩ : syracuseStep 2052143 = 3078215) B3078215
theorem B1708123 : Blo 1348993 1708123 := bstep (se 1 (by rfl) ⟨1281092, by rfl⟩ : syracuseStep 1708123 = 2562185) B2562185
theorem B4559003 : Blo 1348993 4559003 := bstep (se 1 (by rfl) ⟨3419252, by rfl⟩ : syracuseStep 4559003 = 6838505) B6838505
theorem B6836561 : Blo 1348993 6836561 := bstep (se 2 (by rfl) ⟨2563710, by rfl⟩ : syracuseStep 6836561 = 5127421) B5127421
theorem B1708391 : Blo 1348993 1708391 := bstep (se 1 (by rfl) ⟨1281293, by rfl⟩ : syracuseStep 1708391 = 2562587) B2562587
theorem B3035627 : Blo 1348993 3035627 := bstep (se 1 (by rfl) ⟨2276720, by rfl⟩ : syracuseStep 3035627 = 4553441) B4553441
theorem B7295467 : Blo 1348993 7295467 := bstep (se 1 (by rfl) ⟨5471600, by rfl⟩ : syracuseStep 7295467 = 10943201) B10943201
theorem B3035753 : Blo 1348993 3035753 := bstep (se 2 (by rfl) ⟨1138407, by rfl⟩ : syracuseStep 3035753 = 2276815) B2276815
theorem B5624657 : Blo 1348993 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B2921465 : Blo 1348993 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B3036383 : Blo 1348993 3036383 := bstep (se 1 (by rfl) ⟨2277287, by rfl⟩ : syracuseStep 3036383 = 4554575) B4554575
theorem B6829433 : Blo 1348993 6829433 := bstep (se 2 (by rfl) ⟨2561037, by rfl⟩ : syracuseStep 6829433 = 5122075) B5122075
theorem B14423447 : Blo 1348993 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B1349087 : Blo 1348993 1349087 := bstep (se 1 (by rfl) ⟨1011815, by rfl⟩ : syracuseStep 1349087 = 2023631) B2023631
theorem B1349119 : Blo 1348993 1349119 := bstep (se 1 (by rfl) ⟨1011839, by rfl⟩ : syracuseStep 1349119 = 2023679) B2023679
theorem B3036815 : Blo 1348993 3036815 := bstep (se 1 (by rfl) ⟨2277611, by rfl⟩ : syracuseStep 3036815 = 4555223) B4555223
theorem B29996729 : Blo 1348993 29996729 := bstep (se 2 (by rfl) ⟨11248773, by rfl⟩ : syracuseStep 29996729 = 22497547) B22497547
theorem B3036905 : Blo 1348993 3036905 := bstep (se 2 (by rfl) ⟨1138839, by rfl⟩ : syracuseStep 3036905 = 2277679) B2277679
theorem B5765053 : Blo 1348993 5765053 := bstep (se 3 (by rfl) ⟨1080947, by rfl⟩ : syracuseStep 5765053 = 2161895) B2161895
theorem B1349663 : Blo 1348993 1349663 := bstep (se 1 (by rfl) ⟨1012247, by rfl⟩ : syracuseStep 1349663 = 2024495) B2024495
theorem B6838343 : Blo 1348993 6838343 := bstep (se 1 (by rfl) ⟨5128757, by rfl⟩ : syracuseStep 6838343 = 10257515) B10257515
theorem B34224227 : Blo 1348993 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B1349743 : Blo 1348993 1349743 := bstep (se 1 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 1349743 = 2024615) B2024615
theorem B12974255 : Blo 1348993 12974255 := bstep (se 1 (by rfl) ⟨9730691, by rfl⟩ : syracuseStep 12974255 = 19461383) B19461383
theorem B8649017 : Blo 1348993 8649017 := bstep (se 2 (by rfl) ⟨3243381, by rfl⟩ : syracuseStep 8649017 = 6486763) B6486763
theorem B1349991 : Blo 1348993 1349991 := bstep (se 1 (by rfl) ⟨1012493, by rfl⟩ : syracuseStep 1349991 = 2024987) B2024987
theorem B6838667 : Blo 1348993 6838667 := bstep (se 1 (by rfl) ⟨5129000, by rfl⟩ : syracuseStep 6838667 = 10258001) B10258001
theorem B5470625 : Blo 1348993 5470625 := bstep (se 2 (by rfl) ⟨2051484, by rfl⟩ : syracuseStep 5470625 = 4102969) B4102969
theorem B7797179 : Blo 1348993 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B2562511 : Blo 1348993 2562511 := bstep (se 1 (by rfl) ⟨1921883, by rfl⟩ : syracuseStep 2562511 = 3843767) B3843767
theorem B1350247 : Blo 1348993 1350247 := bstep (se 1 (by rfl) ⟨1012685, by rfl⟩ : syracuseStep 1350247 = 2025371) B2025371
theorem B1350271 : Blo 1348993 1350271 := bstep (se 1 (by rfl) ⟨1012703, by rfl⟩ : syracuseStep 1350271 = 2025407) B2025407
theorem B6830729 : Blo 1348993 6830729 := bstep (se 2 (by rfl) ⟨2561523, by rfl⟩ : syracuseStep 6830729 = 5123047) B5123047
theorem B4553387 : Blo 1348993 4553387 := bstep (se 1 (by rfl) ⟨3415040, by rfl⟩ : syracuseStep 4553387 = 6830081) B6830081
theorem B1350395 : Blo 1348993 1350395 := bstep (se 1 (by rfl) ⟨1012796, by rfl⟩ : syracuseStep 1350395 = 2025593) B2025593
theorem B5126921 : Blo 1348993 5126921 := bstep (se 2 (by rfl) ⟨1922595, by rfl⟩ : syracuseStep 5126921 = 3845191) B3845191
theorem B20773687 : Blo 1348993 20773687 := bstep (se 1 (by rfl) ⟨15580265, by rfl⟩ : syracuseStep 20773687 = 31160531) B31160531
theorem B1350651 : Blo 1348993 1350651 := bstep (se 1 (by rfl) ⟨1012988, by rfl⟩ : syracuseStep 1350651 = 2025977) B2025977
theorem B1350687 : Blo 1348993 1350687 := bstep (se 1 (by rfl) ⟨1013015, by rfl⟩ : syracuseStep 1350687 = 2026031) B2026031
theorem B13147219 : Blo 1348993 13147219 := bstep (se 1 (by rfl) ⟨9860414, by rfl⟩ : syracuseStep 13147219 = 19720829) B19720829
theorem B18472121 : Blo 1348993 18472121 := bstep (se 2 (by rfl) ⟨6927045, by rfl⟩ : syracuseStep 18472121 = 13854091) B13854091
theorem B4553927 : Blo 1348993 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B7683295 : Blo 1348993 7683295 := bstep (se 1 (by rfl) ⟨5762471, by rfl⟩ : syracuseStep 7683295 = 11524943) B11524943
theorem B140262677 : Blo 1348993 140262677 := bstep (se 6 (by rfl) ⟨3287406, by rfl⟩ : syracuseStep 140262677 = 6574813) B6574813
theorem B3898679 : Blo 1348993 3898679 := bstep (se 1 (by rfl) ⟨2924009, by rfl⟩ : syracuseStep 3898679 = 5848019) B5848019
theorem B1350975 : Blo 1348993 1350975 := bstep (se 1 (by rfl) ⟨1013231, by rfl⟩ : syracuseStep 1350975 = 2026463) B2026463
theorem B3038543 : Blo 1348993 3038543 := bstep (se 1 (by rfl) ⟨2278907, by rfl⟩ : syracuseStep 3038543 = 4557815) B4557815
theorem B3038633 : Blo 1348993 3038633 := bstep (se 2 (by rfl) ⟨1139487, by rfl⟩ : syracuseStep 3038633 = 2278975) B2278975
theorem B3415547 : Blo 1348993 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B12975713 : Blo 1348993 12975713 := bstep (se 2 (by rfl) ⟨4865892, by rfl⟩ : syracuseStep 12975713 = 9731785) B9731785
theorem B2883347 : Blo 1348993 2883347 := bstep (se 1 (by rfl) ⟨2162510, by rfl⟩ : syracuseStep 2883347 = 4325021) B4325021
theorem B5767051 : Blo 1348993 5767051 := bstep (se 1 (by rfl) ⟨4325288, by rfl⟩ : syracuseStep 5767051 = 8650577) B8650577
theorem B1368095 : Blo 1348993 1368095 := bstep (se 1 (by rfl) ⟨1026071, by rfl⟩ : syracuseStep 1368095 = 2052143) B2052143
theorem B3039335 : Blo 1348993 3039335 := bstep (se 1 (by rfl) ⟨2279501, by rfl⟩ : syracuseStep 3039335 = 4559003) B4559003
theorem B2277497 : Blo 1348993 2277497 := bstep (se 2 (by rfl) ⟨854061, by rfl⟩ : syracuseStep 2277497 = 1708123) B1708123
theorem B2023751 : Blo 1348993 2023751 := bstep (se 1 (by rfl) ⟨1517813, by rfl⟩ : syracuseStep 2023751 = 3035627) B3035627
theorem B2023835 : Blo 1348993 2023835 := bstep (se 1 (by rfl) ⟨1517876, by rfl⟩ : syracuseStep 2023835 = 3035753) B3035753
theorem B10945115 : Blo 1348993 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B1442395 : Blo 1348993 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B3416681 : Blo 1348993 3416681 := bstep (se 2 (by rfl) ⟨1281255, by rfl⟩ : syracuseStep 3416681 = 2562511) B2562511
theorem B10396477 : Blo 1348993 10396477 := bstep (se 3 (by rfl) ⟨1949339, by rfl⟩ : syracuseStep 10396477 = 3898679) B3898679
theorem B2024255 : Blo 1348993 2024255 := bstep (se 1 (by rfl) ⟨1518191, by rfl⟩ : syracuseStep 2024255 = 3036383) B3036383
theorem B4555709 : Blo 1348993 4555709 := bstep (se 3 (by rfl) ⟨854195, by rfl⟩ : syracuseStep 4555709 = 1708391) B1708391
theorem B4555817 : Blo 1348993 4555817 := bstep (se 2 (by rfl) ⟨1708431, by rfl⟩ : syracuseStep 4555817 = 3416863) B3416863
theorem B27698249 : Blo 1348993 27698249 := bstep (se 2 (by rfl) ⟨10386843, by rfl⟩ : syracuseStep 27698249 = 20773687) B20773687
theorem B2024543 : Blo 1348993 2024543 := bstep (se 1 (by rfl) ⟨1518407, by rfl⟩ : syracuseStep 2024543 = 3036815) B3036815
theorem B19997819 : Blo 1348993 19997819 := bstep (se 1 (by rfl) ⟨14998364, by rfl⟩ : syracuseStep 19997819 = 29996729) B29996729
theorem B2024603 : Blo 1348993 2024603 := bstep (se 1 (by rfl) ⟨1518452, by rfl⟩ : syracuseStep 2024603 = 3036905) B3036905
theorem B20792477 : Blo 1348993 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B4867391 : Blo 1348993 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B22816151 : Blo 1348993 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B2885303 : Blo 1348993 2885303 := bstep (se 1 (by rfl) ⟨2163977, by rfl⟩ : syracuseStep 2885303 = 4327955) B4327955
theorem B5195531 : Blo 1348993 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B3417947 : Blo 1348993 3417947 := bstep (se 1 (by rfl) ⟨2563460, by rfl⟩ : syracuseStep 3417947 = 5126921) B5126921
theorem B2279495 : Blo 1348993 2279495 := bstep (se 1 (by rfl) ⟨1709621, by rfl⟩ : syracuseStep 2279495 = 3419243) B3419243
theorem B4327519 : Blo 1348993 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B12314747 : Blo 1348993 12314747 := bstep (se 1 (by rfl) ⟨9236060, by rfl⟩ : syracuseStep 12314747 = 18472121) B18472121
theorem B2025695 : Blo 1348993 2025695 := bstep (se 1 (by rfl) ⟨1519271, by rfl⟩ : syracuseStep 2025695 = 3038543) B3038543
theorem B11536667 : Blo 1348993 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B2025755 : Blo 1348993 2025755 := bstep (se 1 (by rfl) ⟨1519316, by rfl⟩ : syracuseStep 2025755 = 3038633) B3038633
theorem B7686737 : Blo 1348993 7686737 := bstep (se 2 (by rfl) ⟨2882526, by rfl⟩ : syracuseStep 7686737 = 5765053) B5765053
theorem B3418919 : Blo 1348993 3418919 := bstep (se 1 (by rfl) ⟨2564189, by rfl⟩ : syracuseStep 3418919 = 5128379) B5128379
theorem B4557707 : Blo 1348993 4557707 := bstep (se 1 (by rfl) ⟨3418280, by rfl⟩ : syracuseStep 4557707 = 6836561) B6836561
theorem B9727289 : Blo 1348993 9727289 := bstep (se 2 (by rfl) ⟨3647733, by rfl⟩ : syracuseStep 9727289 = 7295467) B7295467
theorem B3419567 : Blo 1348993 3419567 := bstep (se 1 (by rfl) ⟨2564675, by rfl⟩ : syracuseStep 3419567 = 5129351) B5129351
theorem B4558895 : Blo 1348993 4558895 := bstep (se 1 (by rfl) ⟨3419171, by rfl⟩ : syracuseStep 4558895 = 6838343) B6838343
theorem B4559111 : Blo 1348993 4559111 := bstep (se 1 (by rfl) ⟨3419333, by rfl⟩ : syracuseStep 4559111 = 6838667) B6838667
theorem B10244393 : Blo 1348993 10244393 := bstep (se 2 (by rfl) ⟨3841647, by rfl⟩ : syracuseStep 10244393 = 7683295) B7683295
theorem B3649961 : Blo 1348993 3649961 := bstep (se 2 (by rfl) ⟨1368735, by rfl⟩ : syracuseStep 3649961 = 2737471) B2737471
theorem B3035591 : Blo 1348993 3035591 := bstep (se 1 (by rfl) ⟨2276693, by rfl⟩ : syracuseStep 3035591 = 4553387) B4553387
theorem B3035951 : Blo 1348993 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B93508451 : Blo 1348993 93508451 := bstep (se 1 (by rfl) ⟨70131338, by rfl⟩ : syracuseStep 93508451 = 140262677) B140262677
theorem B2561129 : Blo 1348993 2561129 := bstep (se 2 (by rfl) ⟨960423, by rfl⟩ : syracuseStep 2561129 = 1920847) B1920847
theorem B1922231 : Blo 1348993 1922231 := bstep (se 1 (by rfl) ⟨1441673, by rfl⟩ : syracuseStep 1922231 = 2883347) B2883347
theorem B7689401 : Blo 1348993 7689401 := bstep (se 2 (by rfl) ⟨2883525, by rfl⟩ : syracuseStep 7689401 = 5767051) B5767051
theorem B3036599 : Blo 1348993 3036599 := bstep (se 1 (by rfl) ⟨2277449, by rfl⟩ : syracuseStep 3036599 = 4554899) B4554899
theorem B1349147 : Blo 1348993 1349147 := bstep (se 1 (by rfl) ⟨1011860, by rfl⟩ : syracuseStep 1349147 = 2023721) B2023721
theorem B1349327 : Blo 1348993 1349327 := bstep (se 1 (by rfl) ⟨1011995, by rfl⟩ : syracuseStep 1349327 = 2023991) B2023991
theorem B83187587 : Blo 1348993 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B3749771 : Blo 1348993 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B1349567 : Blo 1348993 1349567 := bstep (se 1 (by rfl) ⟨1012175, by rfl⟩ : syracuseStep 1349567 = 2024351) B2024351
theorem B1349759 : Blo 1348993 1349759 := bstep (se 1 (by rfl) ⟨1012319, by rfl⟩ : syracuseStep 1349759 = 2024639) B2024639
theorem B11540663 : Blo 1348993 11540663 := bstep (se 1 (by rfl) ⟨8655497, by rfl⟩ : syracuseStep 11540663 = 17310995) B17310995
theorem B1349855 : Blo 1348993 1349855 := bstep (se 1 (by rfl) ⟨1012391, by rfl⟩ : syracuseStep 1349855 = 2024783) B2024783
theorem B4552955 : Blo 1348993 4552955 := bstep (se 1 (by rfl) ⟨3414716, by rfl⟩ : syracuseStep 4552955 = 6829433) B6829433
theorem B9615631 : Blo 1348993 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B1349915 : Blo 1348993 1349915 := bstep (se 1 (by rfl) ⟨1012436, by rfl⟩ : syracuseStep 1349915 = 2024873) B2024873
theorem B1350015 : Blo 1348993 1350015 := bstep (se 1 (by rfl) ⟨1012511, by rfl⟩ : syracuseStep 1350015 = 2025023) B2025023
theorem B14588333 : Blo 1348993 14588333 := bstep (se 3 (by rfl) ⟨2735312, by rfl⟩ : syracuseStep 14588333 = 5470625) B5470625
theorem B1350255 : Blo 1348993 1350255 := bstep (se 1 (by rfl) ⟨1012691, by rfl⟩ : syracuseStep 1350255 = 2025383) B2025383
theorem B1350335 : Blo 1348993 1350335 := bstep (se 1 (by rfl) ⟨1012751, by rfl⟩ : syracuseStep 1350335 = 2025503) B2025503
theorem B3037931 : Blo 1348993 3037931 := bstep (se 1 (by rfl) ⟨2278448, by rfl⟩ : syracuseStep 3037931 = 4556897) B4556897
theorem B17529625 : Blo 1348993 17529625 := bstep (se 2 (by rfl) ⟨6573609, by rfl⟩ : syracuseStep 17529625 = 13147219) B13147219
theorem B8649503 : Blo 1348993 8649503 := bstep (se 1 (by rfl) ⟨6487127, by rfl⟩ : syracuseStep 8649503 = 12974255) B12974255
theorem B5766011 : Blo 1348993 5766011 := bstep (se 1 (by rfl) ⟨4324508, by rfl⟩ : syracuseStep 5766011 = 8649017) B8649017
theorem B1350639 : Blo 1348993 1350639 := bstep (se 1 (by rfl) ⟨1012979, by rfl⟩ : syracuseStep 1350639 = 2025959) B2025959
theorem B3038291 : Blo 1348993 3038291 := bstep (se 1 (by rfl) ⟨2278718, by rfl⟩ : syracuseStep 3038291 = 4557437) B4557437
theorem B4553819 : Blo 1348993 4553819 := bstep (se 1 (by rfl) ⟨3415364, by rfl⟩ : syracuseStep 4553819 = 6830729) B6830729
theorem B1350759 : Blo 1348993 1350759 := bstep (se 1 (by rfl) ⟨1013069, by rfl⟩ : syracuseStep 1350759 = 2026139) B2026139
theorem B3038345 : Blo 1348993 3038345 := bstep (se 2 (by rfl) ⟨1139379, by rfl⟩ : syracuseStep 3038345 = 2278759) B2278759
theorem B3038363 : Blo 1348993 3038363 := bstep (se 1 (by rfl) ⟨2278772, by rfl⟩ : syracuseStep 3038363 = 4557545) B4557545
theorem B3038399 : Blo 1348993 3038399 := bstep (se 1 (by rfl) ⟨2278799, by rfl⟩ : syracuseStep 3038399 = 4557599) B4557599
theorem B1350907 : Blo 1348993 1350907 := bstep (se 1 (by rfl) ⟨1013180, by rfl⟩ : syracuseStep 1350907 = 2026361) B2026361
theorem B23059727 : Blo 1348993 23059727 := bstep (se 1 (by rfl) ⟨17294795, by rfl⟩ : syracuseStep 23059727 = 34589591) B34589591
theorem B2277031 : Blo 1348993 2277031 := bstep (se 1 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 2277031 = 3415547) B3415547
theorem B8650475 : Blo 1348993 8650475 := bstep (se 1 (by rfl) ⟨6487856, by rfl⟩ : syracuseStep 8650475 = 12975713) B12975713
theorem B7692043 : Blo 1348993 7692043 := bstep (se 1 (by rfl) ⟨5769032, by rfl⟩ : syracuseStep 7692043 = 11538065) B11538065
theorem B7790573 : Blo 1348993 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B3039263 : Blo 1348993 3039263 := bstep (se 1 (by rfl) ⟨2279447, by rfl⟩ : syracuseStep 3039263 = 4558895) B4558895
theorem B3039407 : Blo 1348993 3039407 := bstep (se 1 (by rfl) ⟨2279555, by rfl⟩ : syracuseStep 3039407 = 4559111) B4559111
theorem B2023727 : Blo 1348993 2023727 := bstep (se 1 (by rfl) ⟨1517795, by rfl⟩ : syracuseStep 2023727 = 3035591) B3035591
theorem B12820841 : Blo 1348993 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B2277787 : Blo 1348993 2277787 := bstep (se 1 (by rfl) ⟨1708340, by rfl⟩ : syracuseStep 2277787 = 3416681) B3416681
theorem B2023967 : Blo 1348993 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B18465499 : Blo 1348993 18465499 := bstep (se 1 (by rfl) ⟨13849124, by rfl⟩ : syracuseStep 18465499 = 27698249) B27698249
theorem B13861651 : Blo 1348993 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B2024399 : Blo 1348993 2024399 := bstep (se 1 (by rfl) ⟨1518299, by rfl⟩ : syracuseStep 2024399 = 3036599) B3036599
theorem B9733229 : Blo 1348993 9733229 := bstep (se 3 (by rfl) ⟨1824980, by rfl⟩ : syracuseStep 9733229 = 3649961) B3649961
theorem B2278631 : Blo 1348993 2278631 := bstep (se 1 (by rfl) ⟨1708973, by rfl⟩ : syracuseStep 2278631 = 3417947) B3417947
theorem B8209831 : Blo 1348993 8209831 := bstep (se 1 (by rfl) ⟨6157373, by rfl⟩ : syracuseStep 8209831 = 12314747) B12314747
theorem B7693775 : Blo 1348993 7693775 := bstep (se 1 (by rfl) ⟨5770331, by rfl⟩ : syracuseStep 7693775 = 11540663) B11540663
theorem B9725555 : Blo 1348993 9725555 := bstep (se 1 (by rfl) ⟨7294166, by rfl⟩ : syracuseStep 9725555 = 14588333) B14588333
theorem B2025287 : Blo 1348993 2025287 := bstep (se 1 (by rfl) ⟨1518965, by rfl⟩ : syracuseStep 2025287 = 3037931) B3037931
theorem B2279279 : Blo 1348993 2279279 := bstep (se 1 (by rfl) ⟨1709459, by rfl⟩ : syracuseStep 2279279 = 3418919) B3418919
theorem B3844007 : Blo 1348993 3844007 := bstep (se 1 (by rfl) ⟨2883005, by rfl⟩ : syracuseStep 3844007 = 5766011) B5766011
theorem B2025527 : Blo 1348993 2025527 := bstep (se 1 (by rfl) ⟨1519145, by rfl⟩ : syracuseStep 2025527 = 3038291) B3038291
theorem B2025563 : Blo 1348993 2025563 := bstep (se 1 (by rfl) ⟨1519172, by rfl⟩ : syracuseStep 2025563 = 3038345) B3038345
theorem B2025575 : Blo 1348993 2025575 := bstep (se 1 (by rfl) ⟨1519181, by rfl⟩ : syracuseStep 2025575 = 3038363) B3038363
theorem B2025599 : Blo 1348993 2025599 := bstep (se 1 (by rfl) ⟨1519199, by rfl⟩ : syracuseStep 2025599 = 3038399) B3038399
theorem B2279711 : Blo 1348993 2279711 := bstep (se 1 (by rfl) ⟨1709783, by rfl⟩ : syracuseStep 2279711 = 3419567) B3419567
theorem B2026223 : Blo 1348993 2026223 := bstep (se 1 (by rfl) ⟨1519667, by rfl⟩ : syracuseStep 2026223 = 3039335) B3039335
theorem B1518331 : Blo 1348993 1518331 := bstep (se 1 (by rfl) ⟨1138748, by rfl⟩ : syracuseStep 1518331 = 2277497) B2277497
theorem B3648253 : Blo 1348993 3648253 := bstep (se 3 (by rfl) ⟨684047, by rfl⟩ : syracuseStep 3648253 = 1368095) B1368095
theorem B5770025 : Blo 1348993 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B1707419 : Blo 1348993 1707419 := bstep (se 1 (by rfl) ⟨1280564, by rfl⟩ : syracuseStep 1707419 = 2561129) B2561129
theorem B13331879 : Blo 1348993 13331879 := bstep (se 1 (by rfl) ⟨9998909, by rfl⟩ : syracuseStep 13331879 = 19997819) B19997819
theorem B12979709 : Blo 1348993 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B1519663 : Blo 1348993 1519663 := bstep (se 1 (by rfl) ⟨1139747, by rfl⟩ : syracuseStep 1519663 = 2279495) B2279495
theorem B93491333 : Blo 1348993 93491333 := bstep (se 4 (by rfl) ⟨8764812, by rfl⟩ : syracuseStep 93491333 = 17529625) B17529625
theorem B3035303 : Blo 1348993 3035303 := bstep (se 1 (by rfl) ⟨2276477, by rfl⟩ : syracuseStep 3035303 = 4552955) B4552955
theorem B55447877 : Blo 1348993 55447877 := bstep (se 4 (by rfl) ⟨5198238, by rfl⟩ : syracuseStep 55447877 = 10396477) B10396477
theorem B5124491 : Blo 1348993 5124491 := bstep (se 1 (by rfl) ⟨3843368, by rfl⟩ : syracuseStep 5124491 = 7686737) B7686737
theorem B3035879 : Blo 1348993 3035879 := bstep (se 1 (by rfl) ⟨2276909, by rfl⟩ : syracuseStep 3035879 = 4553819) B4553819
theorem B15373151 : Blo 1348993 15373151 := bstep (se 1 (by rfl) ⟨11529863, by rfl⟩ : syracuseStep 15373151 = 23059727) B23059727
theorem B6484859 : Blo 1348993 6484859 := bstep (se 1 (by rfl) ⟨4863644, by rfl⟩ : syracuseStep 6484859 = 9727289) B9727289
theorem B3036041 : Blo 1348993 3036041 := bstep (se 2 (by rfl) ⟨1138515, by rfl⟩ : syracuseStep 3036041 = 2277031) B2277031
theorem B9999389 : Blo 1348993 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B6829595 : Blo 1348993 6829595 := bstep (se 1 (by rfl) ⟨5122196, by rfl⟩ : syracuseStep 6829595 = 10244393) B10244393
theorem B1349167 : Blo 1348993 1349167 := bstep (se 1 (by rfl) ⟨1011875, by rfl⟩ : syracuseStep 1349167 = 2023751) B2023751
theorem B1349223 : Blo 1348993 1349223 := bstep (se 1 (by rfl) ⟨1011917, by rfl⟩ : syracuseStep 1349223 = 2023835) B2023835
theorem B7296743 : Blo 1348993 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B5125949 : Blo 1348993 5125949 := bstep (se 3 (by rfl) ⟨961115, by rfl⟩ : syracuseStep 5125949 = 1922231) B1922231
theorem B1349503 : Blo 1348993 1349503 := bstep (se 1 (by rfl) ⟨1012127, by rfl⟩ : syracuseStep 1349503 = 2024255) B2024255
theorem B62338967 : Blo 1348993 62338967 := bstep (se 1 (by rfl) ⟨46754225, by rfl⟩ : syracuseStep 62338967 = 93508451) B93508451
theorem B3037139 : Blo 1348993 3037139 := bstep (se 1 (by rfl) ⟨2277854, by rfl⟩ : syracuseStep 3037139 = 4555709) B4555709
theorem B3037211 : Blo 1348993 3037211 := bstep (se 1 (by rfl) ⟨2277908, by rfl⟩ : syracuseStep 3037211 = 4555817) B4555817
theorem B1349695 : Blo 1348993 1349695 := bstep (se 1 (by rfl) ⟨1012271, by rfl⟩ : syracuseStep 1349695 = 2024543) B2024543
theorem B1349735 : Blo 1348993 1349735 := bstep (se 1 (by rfl) ⟨1012301, by rfl⟩ : syracuseStep 1349735 = 2024603) B2024603
theorem B1923193 : Blo 1348993 1923193 := bstep (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) B1442395
theorem B5126267 : Blo 1348993 5126267 := bstep (se 1 (by rfl) ⟨3844700, by rfl⟩ : syracuseStep 5126267 = 7689401) B7689401
theorem B15210767 : Blo 1348993 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B1923535 : Blo 1348993 1923535 := bstep (se 1 (by rfl) ⟨1442651, by rfl⟩ : syracuseStep 1923535 = 2885303) B2885303
theorem B3463687 : Blo 1348993 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B55458391 : Blo 1348993 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B1350463 : Blo 1348993 1350463 := bstep (se 1 (by rfl) ⟨1012847, by rfl⟩ : syracuseStep 1350463 = 2025695) B2025695
theorem B7691111 : Blo 1348993 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B1350503 : Blo 1348993 1350503 := bstep (se 1 (by rfl) ⟨1012877, by rfl⟩ : syracuseStep 1350503 = 2025755) B2025755
theorem B5766335 : Blo 1348993 5766335 := bstep (se 1 (by rfl) ⟨4324751, by rfl⟩ : syracuseStep 5766335 = 8649503) B8649503
theorem B3038471 : Blo 1348993 3038471 := bstep (se 1 (by rfl) ⟨2278853, by rfl⟩ : syracuseStep 3038471 = 4557707) B4557707
theorem B10256057 : Blo 1348993 10256057 := bstep (se 2 (by rfl) ⟨3846021, by rfl⟩ : syracuseStep 10256057 = 7692043) B7692043
theorem B5766983 : Blo 1348993 5766983 := bstep (se 1 (by rfl) ⟨4325237, by rfl⟩ : syracuseStep 5766983 = 8650475) B8650475
theorem B5193715 : Blo 1348993 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B18472997 : Blo 1348993 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B2023535 : Blo 1348993 2023535 := bstep (se 1 (by rfl) ⟨1517651, by rfl⟩ : syracuseStep 2023535 = 3035303) B3035303
theorem B3416327 : Blo 1348993 3416327 := bstep (se 1 (by rfl) ⟨2562245, by rfl⟩ : syracuseStep 3416327 = 5124491) B5124491
theorem B2023919 : Blo 1348993 2023919 := bstep (se 1 (by rfl) ⟨1517939, by rfl⟩ : syracuseStep 2023919 = 3035879) B3035879
theorem B10248767 : Blo 1348993 10248767 := bstep (se 1 (by rfl) ⟨7686575, by rfl⟩ : syracuseStep 10248767 = 15373151) B15373151
theorem B2024027 : Blo 1348993 2024027 := bstep (se 1 (by rfl) ⟨1518020, by rfl⟩ : syracuseStep 2024027 = 3036041) B3036041
theorem B2564713 : Blo 1348993 2564713 := bstep (se 2 (by rfl) ⟨961767, by rfl⟩ : syracuseStep 2564713 = 1923535) B1923535
theorem B10257029 : Blo 1348993 10257029 := bstep (se 4 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 10257029 = 1923193) B1923193
theorem B6488819 : Blo 1348993 6488819 := bstep (se 1 (by rfl) ⟨4866614, by rfl⟩ : syracuseStep 6488819 = 9733229) B9733229
theorem B5129183 : Blo 1348993 5129183 := bstep (se 1 (by rfl) ⟨3846887, by rfl⟩ : syracuseStep 5129183 = 7693775) B7693775
theorem B2024441 : Blo 1348993 2024441 := bstep (se 2 (by rfl) ⟨759165, by rfl⟩ : syracuseStep 2024441 = 1518331) B1518331
theorem B18482201 : Blo 1348993 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B3417299 : Blo 1348993 3417299 := bstep (se 1 (by rfl) ⟨2562974, by rfl⟩ : syracuseStep 3417299 = 5125949) B5125949
theorem B41559311 : Blo 1348993 41559311 := bstep (se 1 (by rfl) ⟨31169483, by rfl⟩ : syracuseStep 41559311 = 62338967) B62338967
theorem B2024759 : Blo 1348993 2024759 := bstep (se 1 (by rfl) ⟨1518569, by rfl⟩ : syracuseStep 2024759 = 3037139) B3037139
theorem B2024807 : Blo 1348993 2024807 := bstep (se 1 (by rfl) ⟨1518605, by rfl⟩ : syracuseStep 2024807 = 3037211) B3037211
theorem B3417511 : Blo 1348993 3417511 := bstep (se 1 (by rfl) ⟨2563133, by rfl⟩ : syracuseStep 3417511 = 5126267) B5126267
theorem B10946441 : Blo 1348993 10946441 := bstep (se 2 (by rfl) ⟨4104915, by rfl⟩ : syracuseStep 10946441 = 8209831) B8209831
theorem B19457981 : Blo 1348993 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B3844223 : Blo 1348993 3844223 := bstep (se 1 (by rfl) ⟨2883167, by rfl⟩ : syracuseStep 3844223 = 5766335) B5766335
theorem B2025647 : Blo 1348993 2025647 := bstep (se 1 (by rfl) ⟨1519235, by rfl⟩ : syracuseStep 2025647 = 3038471) B3038471
theorem B8653139 : Blo 1348993 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B3844655 : Blo 1348993 3844655 := bstep (se 1 (by rfl) ⟨2883491, by rfl⟩ : syracuseStep 3844655 = 5766983) B5766983
theorem B6924953 : Blo 1348993 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B2026175 : Blo 1348993 2026175 := bstep (se 1 (by rfl) ⟨1519631, by rfl⟩ : syracuseStep 2026175 = 3039263) B3039263
theorem B2026217 : Blo 1348993 2026217 := bstep (se 2 (by rfl) ⟨759831, by rfl⟩ : syracuseStep 2026217 = 1519663) B1519663
theorem B62327555 : Blo 1348993 62327555 := bstep (se 1 (by rfl) ⟨46745666, by rfl⟩ : syracuseStep 62327555 = 93491333) B93491333
theorem B2026271 : Blo 1348993 2026271 := bstep (se 1 (by rfl) ⟨1519703, by rfl⟩ : syracuseStep 2026271 = 3039407) B3039407
theorem B36965251 : Blo 1348993 36965251 := bstep (se 1 (by rfl) ⟨27723938, by rfl⟩ : syracuseStep 36965251 = 55447877) B55447877
theorem B8547227 : Blo 1348993 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B40562045 : Blo 1348993 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B73944521 : Blo 1348993 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B1519087 : Blo 1348993 1519087 := bstep (se 1 (by rfl) ⟨1139315, by rfl⟩ : syracuseStep 1519087 = 2278631) B2278631
theorem B1519519 : Blo 1348993 1519519 := bstep (se 1 (by rfl) ⟨1139639, by rfl⟩ : syracuseStep 1519519 = 2279279) B2279279
theorem B1519807 : Blo 1348993 1519807 := bstep (se 1 (by rfl) ⟨1139855, by rfl⟩ : syracuseStep 1519807 = 2279711) B2279711
theorem B3846683 : Blo 1348993 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B6837371 : Blo 1348993 6837371 := bstep (se 1 (by rfl) ⟨5128028, by rfl⟩ : syracuseStep 6837371 = 10256057) B10256057
theorem B1349151 : Blo 1348993 1349151 := bstep (se 1 (by rfl) ⟨1011863, by rfl⟩ : syracuseStep 1349151 = 2023727) B2023727
theorem B1349311 : Blo 1348993 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B3037049 : Blo 1348993 3037049 := bstep (se 2 (by rfl) ⟨1138893, by rfl⟩ : syracuseStep 3037049 = 2277787) B2277787
theorem B4323239 : Blo 1348993 4323239 := bstep (se 1 (by rfl) ⟨3242429, by rfl⟩ : syracuseStep 4323239 = 6484859) B6484859
theorem B1349599 : Blo 1348993 1349599 := bstep (se 1 (by rfl) ⟨1012199, by rfl⟩ : syracuseStep 1349599 = 2024399) B2024399
theorem B6666259 : Blo 1348993 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B4864337 : Blo 1348993 4864337 := bstep (se 2 (by rfl) ⟨1824126, by rfl⟩ : syracuseStep 4864337 = 3648253) B3648253
theorem B4553063 : Blo 1348993 4553063 := bstep (se 1 (by rfl) ⟨3414797, by rfl⟩ : syracuseStep 4553063 = 6829595) B6829595
theorem B4553117 : Blo 1348993 4553117 := bstep (se 3 (by rfl) ⟨853709, by rfl⟩ : syracuseStep 4553117 = 1707419) B1707419
theorem B98482661 : Blo 1348993 98482661 := bstep (se 4 (by rfl) ⟨9232749, by rfl⟩ : syracuseStep 98482661 = 18465499) B18465499
theorem B1350191 : Blo 1348993 1350191 := bstep (se 1 (by rfl) ⟨1012643, by rfl⟩ : syracuseStep 1350191 = 2025287) B2025287
theorem B2562671 : Blo 1348993 2562671 := bstep (se 1 (by rfl) ⟨1922003, by rfl⟩ : syracuseStep 2562671 = 3844007) B3844007
theorem B1350351 : Blo 1348993 1350351 := bstep (se 1 (by rfl) ⟨1012763, by rfl⟩ : syracuseStep 1350351 = 2025527) B2025527
theorem B1350375 : Blo 1348993 1350375 := bstep (se 1 (by rfl) ⟨1012781, by rfl⟩ : syracuseStep 1350375 = 2025563) B2025563
theorem B1350383 : Blo 1348993 1350383 := bstep (se 1 (by rfl) ⟨1012787, by rfl⟩ : syracuseStep 1350383 = 2025575) B2025575
theorem B1350399 : Blo 1348993 1350399 := bstep (se 1 (by rfl) ⟨1012799, by rfl⟩ : syracuseStep 1350399 = 2025599) B2025599
theorem B25934813 : Blo 1348993 25934813 := bstep (se 3 (by rfl) ⟨4862777, by rfl⟩ : syracuseStep 25934813 = 9725555) B9725555
theorem B1350815 : Blo 1348993 1350815 := bstep (se 1 (by rfl) ⟨1013111, by rfl⟩ : syracuseStep 1350815 = 2026223) B2026223
theorem B5127407 : Blo 1348993 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B8887919 : Blo 1348993 8887919 := bstep (se 1 (by rfl) ⟨6665939, by rfl⟩ : syracuseStep 8887919 = 13331879) B13331879
theorem B8888345 : Blo 1348993 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B2277551 : Blo 1348993 2277551 := bstep (se 1 (by rfl) ⟨1708163, by rfl⟩ : syracuseStep 2277551 = 3416327) B3416327
theorem B2564455 : Blo 1348993 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B6832511 : Blo 1348993 6832511 := bstep (se 1 (by rfl) ⟨5124383, by rfl⟩ : syracuseStep 6832511 = 10248767) B10248767
theorem B4325879 : Blo 1348993 4325879 := bstep (se 1 (by rfl) ⟨3244409, by rfl⟩ : syracuseStep 4325879 = 6488819) B6488819
theorem B12321467 : Blo 1348993 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B2278199 : Blo 1348993 2278199 := bstep (se 1 (by rfl) ⟨1708649, by rfl⟩ : syracuseStep 2278199 = 3417299) B3417299
theorem B27706207 : Blo 1348993 27706207 := bstep (se 1 (by rfl) ⟨20779655, by rfl⟩ : syracuseStep 27706207 = 41559311) B41559311
theorem B2024699 : Blo 1348993 2024699 := bstep (se 1 (by rfl) ⟨1518524, by rfl⟩ : syracuseStep 2024699 = 3037049) B3037049
theorem B5768759 : Blo 1348993 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B18466541 : Blo 1348993 18466541 := bstep (se 3 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 18466541 = 6924953) B6924953
theorem B41551703 : Blo 1348993 41551703 := bstep (se 1 (by rfl) ⟨31163777, by rfl⟩ : syracuseStep 41551703 = 62327555) B62327555
theorem B4556681 : Blo 1348993 4556681 := bstep (se 2 (by rfl) ⟨1708755, by rfl⟩ : syracuseStep 4556681 = 3417511) B3417511
theorem B2025449 : Blo 1348993 2025449 := bstep (se 2 (by rfl) ⟨759543, by rfl⟩ : syracuseStep 2025449 = 1519087) B1519087
theorem B3418271 : Blo 1348993 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B2026025 : Blo 1348993 2026025 := bstep (se 2 (by rfl) ⟨759759, by rfl⟩ : syracuseStep 2026025 = 1519519) B1519519
theorem B12315331 : Blo 1348993 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B2026409 : Blo 1348993 2026409 := bstep (se 2 (by rfl) ⟨759903, by rfl⟩ : syracuseStep 2026409 = 1519807) B1519807
theorem B3419455 : Blo 1348993 3419455 := bstep (se 1 (by rfl) ⟨2564591, by rfl⟩ : syracuseStep 3419455 = 5129183) B5129183
theorem B4558247 : Blo 1348993 4558247 := bstep (se 1 (by rfl) ⟨3418685, by rfl⟩ : syracuseStep 4558247 = 6837371) B6837371
theorem B3419617 : Blo 1348993 3419617 := bstep (se 2 (by rfl) ⟨1282356, by rfl⟩ : syracuseStep 3419617 = 2564713) B2564713
theorem B12971987 : Blo 1348993 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B3035375 : Blo 1348993 3035375 := bstep (se 1 (by rfl) ⟨2276531, by rfl⟩ : syracuseStep 3035375 = 4553063) B4553063
theorem B3035411 : Blo 1348993 3035411 := bstep (se 1 (by rfl) ⟨2276558, by rfl⟩ : syracuseStep 3035411 = 4553117) B4553117
theorem B65655107 : Blo 1348993 65655107 := bstep (se 1 (by rfl) ⟨49241330, by rfl⟩ : syracuseStep 65655107 = 98482661) B98482661
theorem B1708447 : Blo 1348993 1708447 := bstep (se 1 (by rfl) ⟨1281335, by rfl⟩ : syracuseStep 1708447 = 2562671) B2562671
theorem B5698151 : Blo 1348993 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B17289875 : Blo 1348993 17289875 := bstep (se 1 (by rfl) ⟨12967406, by rfl⟩ : syracuseStep 17289875 = 25934813) B25934813
theorem B49296347 : Blo 1348993 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B1349023 : Blo 1348993 1349023 := bstep (se 1 (by rfl) ⟨1011767, by rfl⟩ : syracuseStep 1349023 = 2023535) B2023535
theorem B1349279 : Blo 1348993 1349279 := bstep (se 1 (by rfl) ⟨1011959, by rfl⟩ : syracuseStep 1349279 = 2023919) B2023919
theorem B1349351 : Blo 1348993 1349351 := bstep (se 1 (by rfl) ⟨1012013, by rfl⟩ : syracuseStep 1349351 = 2024027) B2024027
theorem B6838019 : Blo 1348993 6838019 := bstep (se 1 (by rfl) ⟨5128514, by rfl⟩ : syracuseStep 6838019 = 10257029) B10257029
theorem B1349627 : Blo 1348993 1349627 := bstep (se 1 (by rfl) ⟨1012220, by rfl⟩ : syracuseStep 1349627 = 2024441) B2024441
theorem B1349839 : Blo 1348993 1349839 := bstep (se 1 (by rfl) ⟨1012379, by rfl⟩ : syracuseStep 1349839 = 2024759) B2024759
theorem B1349871 : Blo 1348993 1349871 := bstep (se 1 (by rfl) ⟨1012403, by rfl⟩ : syracuseStep 1349871 = 2024807) B2024807
theorem B94804469 : Blo 1348993 94804469 := bstep (se 5 (by rfl) ⟨4443959, by rfl⟩ : syracuseStep 94804469 = 8887919) B8887919
theorem B7297627 : Blo 1348993 7297627 := bstep (se 1 (by rfl) ⟨5473220, by rfl⟩ : syracuseStep 7297627 = 10946441) B10946441
theorem B2882159 : Blo 1348993 2882159 := bstep (se 1 (by rfl) ⟨2161619, by rfl⟩ : syracuseStep 2882159 = 4323239) B4323239
theorem B2562815 : Blo 1348993 2562815 := bstep (se 1 (by rfl) ⟨1922111, by rfl⟩ : syracuseStep 2562815 = 3844223) B3844223
theorem B1350431 : Blo 1348993 1350431 := bstep (se 1 (by rfl) ⟨1012823, by rfl⟩ : syracuseStep 1350431 = 2025647) B2025647
theorem B3242891 : Blo 1348993 3242891 := bstep (se 1 (by rfl) ⟨2432168, by rfl⟩ : syracuseStep 3242891 = 4864337) B4864337
theorem B2563103 : Blo 1348993 2563103 := bstep (se 1 (by rfl) ⟨1922327, by rfl⟩ : syracuseStep 2563103 = 3844655) B3844655
theorem B1350783 : Blo 1348993 1350783 := bstep (se 1 (by rfl) ⟨1013087, by rfl⟩ : syracuseStep 1350783 = 2026175) B2026175
theorem B1350811 : Blo 1348993 1350811 := bstep (se 1 (by rfl) ⟨1013108, by rfl⟩ : syracuseStep 1350811 = 2026217) B2026217
theorem B1350847 : Blo 1348993 1350847 := bstep (se 1 (by rfl) ⟨1013135, by rfl⟩ : syracuseStep 1350847 = 2026271) B2026271
theorem B197148005 : Blo 1348993 197148005 := bstep (se 4 (by rfl) ⟨18482625, by rfl⟩ : syracuseStep 197148005 = 36965251) B36965251
theorem B27041363 : Blo 1348993 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B2023583 : Blo 1348993 2023583 := bstep (se 1 (by rfl) ⟨1517687, by rfl⟩ : syracuseStep 2023583 = 3035375) B3035375
theorem B2023607 : Blo 1348993 2023607 := bstep (se 1 (by rfl) ⟨1517705, by rfl⟩ : syracuseStep 2023607 = 3035411) B3035411
theorem B43770071 : Blo 1348993 43770071 := bstep (se 1 (by rfl) ⟨32827553, by rfl⟩ : syracuseStep 43770071 = 65655107) B65655107
theorem B4555007 : Blo 1348993 4555007 := bstep (se 1 (by rfl) ⟨3416255, by rfl⟩ : syracuseStep 4555007 = 6832511) B6832511
theorem B2883919 : Blo 1348993 2883919 := bstep (se 1 (by rfl) ⟨2162939, by rfl⟩ : syracuseStep 2883919 = 4325879) B4325879
theorem B11526583 : Blo 1348993 11526583 := bstep (se 1 (by rfl) ⟨8644937, by rfl⟩ : syracuseStep 11526583 = 17289875) B17289875
theorem B2277929 : Blo 1348993 2277929 := bstep (se 2 (by rfl) ⟨854223, by rfl⟩ : syracuseStep 2277929 = 1708447) B1708447
theorem B2278847 : Blo 1348993 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B63202979 : Blo 1348993 63202979 := bstep (se 1 (by rfl) ⟨47402234, by rfl⟩ : syracuseStep 63202979 = 94804469) B94804469
theorem B5925563 : Blo 1348993 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B6834941 : Blo 1348993 6834941 := bstep (se 3 (by rfl) ⟨1281551, by rfl⟩ : syracuseStep 6834941 = 2563103) B2563103
theorem B1518367 : Blo 1348993 1518367 := bstep (se 1 (by rfl) ⟨1138775, by rfl⟩ : syracuseStep 1518367 = 2277551) B2277551
theorem B3419273 : Blo 1348993 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B1518799 : Blo 1348993 1518799 := bstep (se 1 (by rfl) ⟨1139099, by rfl⟩ : syracuseStep 1518799 = 2278199) B2278199
theorem B16420441 : Blo 1348993 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B36941609 : Blo 1348993 36941609 := bstep (se 2 (by rfl) ⟨13853103, by rfl⟩ : syracuseStep 36941609 = 27706207) B27706207
theorem B4558679 : Blo 1348993 4558679 := bstep (se 1 (by rfl) ⟨3419009, by rfl⟩ : syracuseStep 4558679 = 6838019) B6838019
theorem B27701135 : Blo 1348993 27701135 := bstep (se 1 (by rfl) ⟨20775851, by rfl⟩ : syracuseStep 27701135 = 41551703) B41551703
theorem B1921439 : Blo 1348993 1921439 := bstep (se 1 (by rfl) ⟨1441079, by rfl⟩ : syracuseStep 1921439 = 2882159) B2882159
theorem B4559273 : Blo 1348993 4559273 := bstep (se 2 (by rfl) ⟨1709727, by rfl⟩ : syracuseStep 4559273 = 3419455) B3419455
theorem B1708543 : Blo 1348993 1708543 := bstep (se 1 (by rfl) ⟨1281407, by rfl⟩ : syracuseStep 1708543 = 2562815) B2562815
theorem B4559489 : Blo 1348993 4559489 := bstep (se 2 (by rfl) ⟨1709808, by rfl⟩ : syracuseStep 4559489 = 3419617) B3419617
theorem B18027575 : Blo 1348993 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B8647991 : Blo 1348993 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B3798767 : Blo 1348993 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B8214311 : Blo 1348993 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B32864231 : Blo 1348993 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B9730169 : Blo 1348993 9730169 := bstep (se 2 (by rfl) ⟨3648813, by rfl⟩ : syracuseStep 9730169 = 7297627) B7297627
theorem B1349799 : Blo 1348993 1349799 := bstep (se 1 (by rfl) ⟨1012349, by rfl⟩ : syracuseStep 1349799 = 2024699) B2024699
theorem B12311027 : Blo 1348993 12311027 := bstep (se 1 (by rfl) ⟨9233270, by rfl⟩ : syracuseStep 12311027 = 18466541) B18466541
theorem B3037787 : Blo 1348993 3037787 := bstep (se 1 (by rfl) ⟨2278340, by rfl⟩ : syracuseStep 3037787 = 4556681) B4556681
theorem B1350299 : Blo 1348993 1350299 := bstep (se 1 (by rfl) ⟨1012724, by rfl⟩ : syracuseStep 1350299 = 2025449) B2025449
theorem B15383357 : Blo 1348993 15383357 := bstep (se 3 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 15383357 = 5768759) B5768759
theorem B1350683 : Blo 1348993 1350683 := bstep (se 1 (by rfl) ⟨1013012, by rfl⟩ : syracuseStep 1350683 = 2026025) B2026025
theorem B2161927 : Blo 1348993 2161927 := bstep (se 1 (by rfl) ⟨1621445, by rfl⟩ : syracuseStep 2161927 = 3242891) B3242891
theorem B1350939 : Blo 1348993 1350939 := bstep (se 1 (by rfl) ⟨1013204, by rfl⟩ : syracuseStep 1350939 = 2026409) B2026409
theorem B131432003 : Blo 1348993 131432003 := bstep (se 1 (by rfl) ⟨98574002, by rfl⟩ : syracuseStep 131432003 = 197148005) B197148005
theorem B3038831 : Blo 1348993 3038831 := bstep (se 1 (by rfl) ⟨2279123, by rfl⟩ : syracuseStep 3038831 = 4558247) B4558247
theorem B29180047 : Blo 1348993 29180047 := bstep (se 1 (by rfl) ⟨21885035, by rfl⟩ : syracuseStep 29180047 = 43770071) B43770071
theorem B3039515 : Blo 1348993 3039515 := bstep (se 1 (by rfl) ⟨2279636, by rfl⟩ : syracuseStep 3039515 = 4559273) B4559273
theorem B3039659 : Blo 1348993 3039659 := bstep (se 1 (by rfl) ⟨2279744, by rfl⟩ : syracuseStep 3039659 = 4559489) B4559489
theorem B15368777 : Blo 1348993 15368777 := bstep (se 2 (by rfl) ⟨5763291, by rfl⟩ : syracuseStep 15368777 = 11526583) B11526583
theorem B2278057 : Blo 1348993 2278057 := bstep (se 2 (by rfl) ⟨854271, by rfl⟩ : syracuseStep 2278057 = 1708543) B1708543
theorem B12018383 : Blo 1348993 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B2024489 : Blo 1348993 2024489 := bstep (se 2 (by rfl) ⟨759183, by rfl⟩ : syracuseStep 2024489 = 1518367) B1518367
theorem B2532511 : Blo 1348993 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B2025065 : Blo 1348993 2025065 := bstep (se 2 (by rfl) ⟨759399, by rfl⟩ : syracuseStep 2025065 = 1518799) B1518799
theorem B2025191 : Blo 1348993 2025191 := bstep (se 1 (by rfl) ⟨1518893, by rfl⟩ : syracuseStep 2025191 = 3037787) B3037787
theorem B3950375 : Blo 1348993 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B4556627 : Blo 1348993 4556627 := bstep (se 1 (by rfl) ⟨3417470, by rfl⟩ : syracuseStep 4556627 = 6834941) B6834941
theorem B2279515 : Blo 1348993 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B2025887 : Blo 1348993 2025887 := bstep (se 1 (by rfl) ⟨1519415, by rfl⟩ : syracuseStep 2025887 = 3038831) B3038831
theorem B24627739 : Blo 1348993 24627739 := bstep (se 1 (by rfl) ⟨18470804, by rfl⟩ : syracuseStep 24627739 = 36941609) B36941609
theorem B18467423 : Blo 1348993 18467423 := bstep (se 1 (by rfl) ⟨13850567, by rfl⟩ : syracuseStep 18467423 = 27701135) B27701135
theorem B1518619 : Blo 1348993 1518619 := bstep (se 1 (by rfl) ⟨1138964, by rfl⟩ : syracuseStep 1518619 = 2277929) B2277929
theorem B3845225 : Blo 1348993 3845225 := bstep (se 2 (by rfl) ⟨1441959, by rfl⟩ : syracuseStep 3845225 = 2883919) B2883919
theorem B1519231 : Blo 1348993 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B5123837 : Blo 1348993 5123837 := bstep (se 3 (by rfl) ⟨960719, by rfl⟩ : syracuseStep 5123837 = 1921439) B1921439
theorem B42135319 : Blo 1348993 42135319 := bstep (se 1 (by rfl) ⟨31601489, by rfl⟩ : syracuseStep 42135319 = 63202979) B63202979
theorem B5476207 : Blo 1348993 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B21909487 : Blo 1348993 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B21893921 : Blo 1348993 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B1349055 : Blo 1348993 1349055 := bstep (se 1 (by rfl) ⟨1011791, by rfl⟩ : syracuseStep 1349055 = 2023583) B2023583
theorem B1349071 : Blo 1348993 1349071 := bstep (se 1 (by rfl) ⟨1011803, by rfl⟩ : syracuseStep 1349071 = 2023607) B2023607
theorem B3036671 : Blo 1348993 3036671 := bstep (se 1 (by rfl) ⟨2277503, by rfl⟩ : syracuseStep 3036671 = 4555007) B4555007
theorem B5765327 : Blo 1348993 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B6486779 : Blo 1348993 6486779 := bstep (se 1 (by rfl) ⟨4865084, by rfl⟩ : syracuseStep 6486779 = 9730169) B9730169
theorem B8207351 : Blo 1348993 8207351 := bstep (se 1 (by rfl) ⟨6155513, by rfl⟩ : syracuseStep 8207351 = 12311027) B12311027
theorem B2882569 : Blo 1348993 2882569 := bstep (se 2 (by rfl) ⟨1080963, by rfl⟩ : syracuseStep 2882569 = 2161927) B2161927
theorem B10255571 : Blo 1348993 10255571 := bstep (se 1 (by rfl) ⟨7691678, by rfl⟩ : syracuseStep 10255571 = 15383357) B15383357
theorem B87621335 : Blo 1348993 87621335 := bstep (se 1 (by rfl) ⟨65716001, by rfl⟩ : syracuseStep 87621335 = 131432003) B131432003
theorem B3039119 : Blo 1348993 3039119 := bstep (se 1 (by rfl) ⟨2279339, by rfl⟩ : syracuseStep 3039119 = 4558679) B4558679
theorem B3039353 : Blo 1348993 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B8012255 : Blo 1348993 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B2024447 : Blo 1348993 2024447 := bstep (se 1 (by rfl) ⟨1518335, by rfl⟩ : syracuseStep 2024447 = 3036671) B3036671
theorem B3843425 : Blo 1348993 3843425 := bstep (se 2 (by rfl) ⟨1441284, by rfl⟩ : syracuseStep 3843425 = 2882569) B2882569
theorem B2024825 : Blo 1348993 2024825 := bstep (se 2 (by rfl) ⟨759309, by rfl⟩ : syracuseStep 2024825 = 1518619) B1518619
theorem B3843551 : Blo 1348993 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B2025641 : Blo 1348993 2025641 := bstep (se 2 (by rfl) ⟨759615, by rfl⟩ : syracuseStep 2025641 = 1519231) B1519231
theorem B7301609 : Blo 1348993 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B2026079 : Blo 1348993 2026079 := bstep (se 1 (by rfl) ⟨1519559, by rfl⟩ : syracuseStep 2026079 = 3039119) B3039119
theorem B2026343 : Blo 1348993 2026343 := bstep (se 1 (by rfl) ⟨1519757, by rfl⟩ : syracuseStep 2026343 = 3039515) B3039515
theorem B38906729 : Blo 1348993 38906729 := bstep (se 2 (by rfl) ⟨14590023, by rfl⟩ : syracuseStep 38906729 = 29180047) B29180047
theorem B2026439 : Blo 1348993 2026439 := bstep (se 1 (by rfl) ⟨1519829, by rfl⟩ : syracuseStep 2026439 = 3039659) B3039659
theorem B32836985 : Blo 1348993 32836985 := bstep (se 2 (by rfl) ⟨12313869, by rfl⟩ : syracuseStep 32836985 = 24627739) B24627739
theorem B6837047 : Blo 1348993 6837047 := bstep (se 1 (by rfl) ⟨5127785, by rfl⟩ : syracuseStep 6837047 = 10255571) B10255571
theorem B58414223 : Blo 1348993 58414223 := bstep (se 1 (by rfl) ⟨43810667, by rfl⟩ : syracuseStep 58414223 = 87621335) B87621335
theorem B10245851 : Blo 1348993 10245851 := bstep (se 1 (by rfl) ⟨7684388, by rfl⟩ : syracuseStep 10245851 = 15368777) B15368777
theorem B42137333 : Blo 1348993 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B14595947 : Blo 1348993 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B1349659 : Blo 1348993 1349659 := bstep (se 1 (by rfl) ⟨1012244, by rfl⟩ : syracuseStep 1349659 = 2024489) B2024489
theorem B13506725 : Blo 1348993 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B3037409 : Blo 1348993 3037409 := bstep (se 2 (by rfl) ⟨1139028, by rfl⟩ : syracuseStep 3037409 = 2278057) B2278057
theorem B1350043 : Blo 1348993 1350043 := bstep (se 1 (by rfl) ⟨1012532, by rfl⟩ : syracuseStep 1350043 = 2025065) B2025065
theorem B1350127 : Blo 1348993 1350127 := bstep (se 1 (by rfl) ⟨1012595, by rfl⟩ : syracuseStep 1350127 = 2025191) B2025191
theorem B3037751 : Blo 1348993 3037751 := bstep (se 1 (by rfl) ⟨2278313, by rfl⟩ : syracuseStep 3037751 = 4556627) B4556627
theorem B224721701 : Blo 1348993 224721701 := bstep (se 4 (by rfl) ⟨21067659, by rfl⟩ : syracuseStep 224721701 = 42135319) B42135319
theorem B1350591 : Blo 1348993 1350591 := bstep (se 1 (by rfl) ⟨1012943, by rfl⟩ : syracuseStep 1350591 = 2025887) B2025887
theorem B12311615 : Blo 1348993 12311615 := bstep (se 1 (by rfl) ⟨9233711, by rfl⟩ : syracuseStep 12311615 = 18467423) B18467423
theorem B4324519 : Blo 1348993 4324519 := bstep (se 1 (by rfl) ⟨3243389, by rfl⟩ : syracuseStep 4324519 = 6486779) B6486779
theorem B5471567 : Blo 1348993 5471567 := bstep (se 1 (by rfl) ⟨4103675, by rfl⟩ : syracuseStep 5471567 = 8207351) B8207351
theorem B2563483 : Blo 1348993 2563483 := bstep (se 1 (by rfl) ⟨1922612, by rfl⟩ : syracuseStep 2563483 = 3845225) B3845225
theorem B3415891 : Blo 1348993 3415891 := bstep (se 1 (by rfl) ⟨2561918, by rfl⟩ : syracuseStep 3415891 = 5123837) B5123837
theorem B29212649 : Blo 1348993 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B28091555 : Blo 1348993 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B21366013 : Blo 1348993 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B9004483 : Blo 1348993 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B2024939 : Blo 1348993 2024939 := bstep (se 1 (by rfl) ⟨1518704, by rfl⟩ : syracuseStep 2024939 = 3037409) B3037409
theorem B4867739 : Blo 1348993 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B2025167 : Blo 1348993 2025167 := bstep (se 1 (by rfl) ⟨1518875, by rfl⟩ : syracuseStep 2025167 = 3037751) B3037751
theorem B3417977 : Blo 1348993 3417977 := bstep (se 2 (by rfl) ⟨1281741, by rfl⟩ : syracuseStep 3417977 = 2563483) B2563483
theorem B25937819 : Blo 1348993 25937819 := bstep (se 1 (by rfl) ⟨19453364, by rfl⟩ : syracuseStep 25937819 = 38906729) B38906729
theorem B3647711 : Blo 1348993 3647711 := bstep (se 1 (by rfl) ⟨2735783, by rfl⟩ : syracuseStep 3647711 = 5471567) B5471567
theorem B21891323 : Blo 1348993 21891323 := bstep (se 1 (by rfl) ⟨16418492, by rfl⟩ : syracuseStep 21891323 = 32836985) B32836985
theorem B19475099 : Blo 1348993 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B2026235 : Blo 1348993 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B4558031 : Blo 1348993 4558031 := bstep (se 1 (by rfl) ⟨3418523, by rfl⟩ : syracuseStep 4558031 = 6837047) B6837047
theorem B23064101 : Blo 1348993 23064101 := bstep (se 4 (by rfl) ⟨2162259, by rfl⟩ : syracuseStep 23064101 = 4324519) B4324519
theorem B1349631 : Blo 1348993 1349631 := bstep (se 1 (by rfl) ⟨1012223, by rfl⟩ : syracuseStep 1349631 = 2024447) B2024447
theorem B38942815 : Blo 1348993 38942815 := bstep (se 1 (by rfl) ⟨29207111, by rfl⟩ : syracuseStep 38942815 = 58414223) B58414223
theorem B2562283 : Blo 1348993 2562283 := bstep (se 1 (by rfl) ⟨1921712, by rfl⟩ : syracuseStep 2562283 = 3843425) B3843425
theorem B1349883 : Blo 1348993 1349883 := bstep (se 1 (by rfl) ⟨1012412, by rfl⟩ : syracuseStep 1349883 = 2024825) B2024825
theorem B2562367 : Blo 1348993 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B6830567 : Blo 1348993 6830567 := bstep (se 1 (by rfl) ⟨5122925, by rfl⟩ : syracuseStep 6830567 = 10245851) B10245851
theorem B9730631 : Blo 1348993 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B1350427 : Blo 1348993 1350427 := bstep (se 1 (by rfl) ⟨1012820, by rfl⟩ : syracuseStep 1350427 = 2025641) B2025641
theorem B1350719 : Blo 1348993 1350719 := bstep (se 1 (by rfl) ⟨1013039, by rfl⟩ : syracuseStep 1350719 = 2026079) B2026079
theorem B149814467 : Blo 1348993 149814467 := bstep (se 1 (by rfl) ⟨112360850, by rfl⟩ : syracuseStep 149814467 = 224721701) B224721701
theorem B1350895 : Blo 1348993 1350895 := bstep (se 1 (by rfl) ⟨1013171, by rfl⟩ : syracuseStep 1350895 = 2026343) B2026343
theorem B1350959 : Blo 1348993 1350959 := bstep (se 1 (by rfl) ⟨1013219, by rfl⟩ : syracuseStep 1350959 = 2026439) B2026439
theorem B8207743 : Blo 1348993 8207743 := bstep (se 1 (by rfl) ⟨6155807, by rfl⟩ : syracuseStep 8207743 = 12311615) B12311615
theorem B4554521 : Blo 1348993 4554521 := bstep (se 2 (by rfl) ⟨1707945, by rfl⟩ : syracuseStep 4554521 = 3415891) B3415891
theorem B3416377 : Blo 1348993 3416377 := bstep (se 2 (by rfl) ⟨1281141, by rfl⟩ : syracuseStep 3416377 = 2562283) B2562283
theorem B3416489 : Blo 1348993 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B58376861 : Blo 1348993 58376861 := bstep (se 3 (by rfl) ⟨10945661, by rfl⟩ : syracuseStep 58376861 = 21891323) B21891323
theorem B18727703 : Blo 1348993 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B3245159 : Blo 1348993 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B2278651 : Blo 1348993 2278651 := bstep (se 1 (by rfl) ⟨1708988, by rfl⟩ : syracuseStep 2278651 = 3417977) B3417977
theorem B51923753 : Blo 1348993 51923753 := bstep (se 2 (by rfl) ⟨19471407, by rfl⟩ : syracuseStep 51923753 = 38942815) B38942815
theorem B9727229 : Blo 1348993 9727229 := bstep (se 3 (by rfl) ⟨1823855, by rfl⟩ : syracuseStep 9727229 = 3647711) B3647711
theorem B28488017 : Blo 1348993 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B12005977 : Blo 1348993 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B3036347 : Blo 1348993 3036347 := bstep (se 1 (by rfl) ⟨2277260, by rfl⟩ : syracuseStep 3036347 = 4554521) B4554521
theorem B1349959 : Blo 1348993 1349959 := bstep (se 1 (by rfl) ⟨1012469, by rfl⟩ : syracuseStep 1349959 = 2024939) B2024939
theorem B1350111 : Blo 1348993 1350111 := bstep (se 1 (by rfl) ⟨1012583, by rfl⟩ : syracuseStep 1350111 = 2025167) B2025167
theorem B17291879 : Blo 1348993 17291879 := bstep (se 1 (by rfl) ⟨12968909, by rfl⟩ : syracuseStep 17291879 = 25937819) B25937819
theorem B4553711 : Blo 1348993 4553711 := bstep (se 1 (by rfl) ⟨3415283, by rfl⟩ : syracuseStep 4553711 = 6830567) B6830567
theorem B6487087 : Blo 1348993 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B12983399 : Blo 1348993 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B1350823 : Blo 1348993 1350823 := bstep (se 1 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 1350823 = 2026235) B2026235
theorem B10943657 : Blo 1348993 10943657 := bstep (se 2 (by rfl) ⟨4103871, by rfl⟩ : syracuseStep 10943657 = 8207743) B8207743
theorem B99876311 : Blo 1348993 99876311 := bstep (se 1 (by rfl) ⟨74907233, by rfl⟩ : syracuseStep 99876311 = 149814467) B149814467
theorem B3038687 : Blo 1348993 3038687 := bstep (se 1 (by rfl) ⟨2279015, by rfl⟩ : syracuseStep 3038687 = 4558031) B4558031
theorem B15376067 : Blo 1348993 15376067 := bstep (se 1 (by rfl) ⟨11532050, by rfl⟩ : syracuseStep 15376067 = 23064101) B23064101
theorem B2277659 : Blo 1348993 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B4555169 : Blo 1348993 4555169 := bstep (se 2 (by rfl) ⟨1708188, by rfl⟩ : syracuseStep 4555169 = 3416377) B3416377
theorem B12485135 : Blo 1348993 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B2163439 : Blo 1348993 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B16007969 : Blo 1348993 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B2024231 : Blo 1348993 2024231 := bstep (se 1 (by rfl) ⟨1518173, by rfl⟩ : syracuseStep 2024231 = 3036347) B3036347
theorem B11527919 : Blo 1348993 11527919 := bstep (se 1 (by rfl) ⟨8645939, by rfl⟩ : syracuseStep 11527919 = 17291879) B17291879
theorem B2025791 : Blo 1348993 2025791 := bstep (se 1 (by rfl) ⟨1519343, by rfl⟩ : syracuseStep 2025791 = 3038687) B3038687
theorem B10250711 : Blo 1348993 10250711 := bstep (se 1 (by rfl) ⟨7688033, by rfl⟩ : syracuseStep 10250711 = 15376067) B15376067
theorem B18992011 : Blo 1348993 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B25939277 : Blo 1348993 25939277 := bstep (se 3 (by rfl) ⟨4863614, by rfl⟩ : syracuseStep 25939277 = 9727229) B9727229
theorem B34615835 : Blo 1348993 34615835 := bstep (se 1 (by rfl) ⟨25961876, by rfl⟩ : syracuseStep 34615835 = 51923753) B51923753
theorem B3035807 : Blo 1348993 3035807 := bstep (se 1 (by rfl) ⟨2276855, by rfl⟩ : syracuseStep 3035807 = 4553711) B4553711
theorem B8655599 : Blo 1348993 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B7295771 : Blo 1348993 7295771 := bstep (se 1 (by rfl) ⟨5471828, by rfl⟩ : syracuseStep 7295771 = 10943657) B10943657
theorem B38917907 : Blo 1348993 38917907 := bstep (se 1 (by rfl) ⟨29188430, by rfl⟩ : syracuseStep 38917907 = 58376861) B58376861
theorem B8649449 : Blo 1348993 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B3038201 : Blo 1348993 3038201 := bstep (se 2 (by rfl) ⟨1139325, by rfl⟩ : syracuseStep 3038201 = 2278651) B2278651
theorem B66584207 : Blo 1348993 66584207 := bstep (se 1 (by rfl) ⟨49938155, by rfl⟩ : syracuseStep 66584207 = 99876311) B99876311
theorem B23077223 : Blo 1348993 23077223 := bstep (se 1 (by rfl) ⟨17307917, by rfl⟩ : syracuseStep 23077223 = 34615835) B34615835
theorem B2023871 : Blo 1348993 2023871 := bstep (se 1 (by rfl) ⟨1517903, by rfl⟩ : syracuseStep 2023871 = 3035807) B3035807
theorem B2884585 : Blo 1348993 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B7685279 : Blo 1348993 7685279 := bstep (se 1 (by rfl) ⟨5763959, by rfl⟩ : syracuseStep 7685279 = 11527919) B11527919
theorem B25945271 : Blo 1348993 25945271 := bstep (se 1 (by rfl) ⟨19458953, by rfl⟩ : syracuseStep 25945271 = 38917907) B38917907
theorem B25322681 : Blo 1348993 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B33293693 : Blo 1348993 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B6833807 : Blo 1348993 6833807 := bstep (se 1 (by rfl) ⟨5125355, by rfl⟩ : syracuseStep 6833807 = 10250711) B10250711
theorem B2025467 : Blo 1348993 2025467 := bstep (se 1 (by rfl) ⟨1519100, by rfl⟩ : syracuseStep 2025467 = 3038201) B3038201
theorem B1518439 : Blo 1348993 1518439 := bstep (se 1 (by rfl) ⟨1138829, by rfl⟩ : syracuseStep 1518439 = 2277659) B2277659
theorem B23081597 : Blo 1348993 23081597 := bstep (se 3 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 23081597 = 8655599) B8655599
theorem B44389471 : Blo 1348993 44389471 := bstep (se 1 (by rfl) ⟨33292103, by rfl⟩ : syracuseStep 44389471 = 66584207) B66584207
theorem B3036779 : Blo 1348993 3036779 := bstep (se 1 (by rfl) ⟨2277584, by rfl⟩ : syracuseStep 3036779 = 4555169) B4555169
theorem B4863847 : Blo 1348993 4863847 := bstep (se 1 (by rfl) ⟨3647885, by rfl⟩ : syracuseStep 4863847 = 7295771) B7295771
theorem B1349487 : Blo 1348993 1349487 := bstep (se 1 (by rfl) ⟨1012115, by rfl⟩ : syracuseStep 1349487 = 2024231) B2024231
theorem B1350527 : Blo 1348993 1350527 := bstep (se 1 (by rfl) ⟨1012895, by rfl⟩ : syracuseStep 1350527 = 2025791) B2025791
theorem B5766299 : Blo 1348993 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B42687917 : Blo 1348993 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B17292851 : Blo 1348993 17292851 := bstep (se 1 (by rfl) ⟨12969638, by rfl⟩ : syracuseStep 17292851 = 25939277) B25939277
theorem B15384815 : Blo 1348993 15384815 := bstep (se 1 (by rfl) ⟨11538611, by rfl⟩ : syracuseStep 15384815 = 23077223) B23077223
theorem B2024519 : Blo 1348993 2024519 := bstep (se 1 (by rfl) ⟨1518389, by rfl⟩ : syracuseStep 2024519 = 3036779) B3036779
theorem B4555871 : Blo 1348993 4555871 := bstep (se 1 (by rfl) ⟨3416903, by rfl⟩ : syracuseStep 4555871 = 6833807) B6833807
theorem B2024585 : Blo 1348993 2024585 := bstep (se 2 (by rfl) ⟨759219, by rfl⟩ : syracuseStep 2024585 = 1518439) B1518439
theorem B3844199 : Blo 1348993 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B11528567 : Blo 1348993 11528567 := bstep (se 1 (by rfl) ⟨8646425, by rfl⟩ : syracuseStep 11528567 = 17292851) B17292851
theorem B15387731 : Blo 1348993 15387731 := bstep (se 1 (by rfl) ⟨11540798, by rfl⟩ : syracuseStep 15387731 = 23081597) B23081597
theorem B5123519 : Blo 1348993 5123519 := bstep (se 1 (by rfl) ⟨3842639, by rfl⟩ : syracuseStep 5123519 = 7685279) B7685279
theorem B17296847 : Blo 1348993 17296847 := bstep (se 1 (by rfl) ⟨12972635, by rfl⟩ : syracuseStep 17296847 = 25945271) B25945271
theorem B22195795 : Blo 1348993 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B3846113 : Blo 1348993 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B6485129 : Blo 1348993 6485129 := bstep (se 2 (by rfl) ⟨2431923, by rfl⟩ : syracuseStep 6485129 = 4863847) B4863847
theorem B1349247 : Blo 1348993 1349247 := bstep (se 1 (by rfl) ⟨1011935, by rfl⟩ : syracuseStep 1349247 = 2023871) B2023871
theorem B16881787 : Blo 1348993 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B1350311 : Blo 1348993 1350311 := bstep (se 1 (by rfl) ⟨1012733, by rfl⟩ : syracuseStep 1350311 = 2025467) B2025467
theorem B59185961 : Blo 1348993 59185961 := bstep (se 2 (by rfl) ⟨22194735, by rfl⟩ : syracuseStep 59185961 = 44389471) B44389471
theorem B28458611 : Blo 1348993 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B10256543 : Blo 1348993 10256543 := bstep (se 1 (by rfl) ⟨7692407, by rfl⟩ : syracuseStep 10256543 = 15384815) B15384815
theorem B7685711 : Blo 1348993 7685711 := bstep (se 1 (by rfl) ⟨5764283, by rfl⟩ : syracuseStep 7685711 = 11528567) B11528567
theorem B10258487 : Blo 1348993 10258487 := bstep (se 1 (by rfl) ⟨7693865, by rfl⟩ : syracuseStep 10258487 = 15387731) B15387731
theorem B10251197 : Blo 1348993 10251197 := bstep (se 3 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 10251197 = 3844199) B3844199
theorem B39457307 : Blo 1348993 39457307 := bstep (se 1 (by rfl) ⟨29592980, by rfl⟩ : syracuseStep 39457307 = 59185961) B59185961
theorem B29594393 : Blo 1348993 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B11531231 : Blo 1348993 11531231 := bstep (se 1 (by rfl) ⟨8648423, by rfl⟩ : syracuseStep 11531231 = 17296847) B17296847
theorem B22509049 : Blo 1348993 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B1349679 : Blo 1348993 1349679 := bstep (se 1 (by rfl) ⟨1012259, by rfl⟩ : syracuseStep 1349679 = 2024519) B2024519
theorem B3037247 : Blo 1348993 3037247 := bstep (se 1 (by rfl) ⟨2277935, by rfl⟩ : syracuseStep 3037247 = 4555871) B4555871
theorem B4323419 : Blo 1348993 4323419 := bstep (se 1 (by rfl) ⟨3242564, by rfl⟩ : syracuseStep 4323419 = 6485129) B6485129
theorem B1349723 : Blo 1348993 1349723 := bstep (se 1 (by rfl) ⟨1012292, by rfl⟩ : syracuseStep 1349723 = 2024585) B2024585
theorem B3415679 : Blo 1348993 3415679 := bstep (se 1 (by rfl) ⟨2561759, by rfl⟩ : syracuseStep 3415679 = 5123519) B5123519
theorem B18972407 : Blo 1348993 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B2564075 : Blo 1348993 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B26304871 : Blo 1348993 26304871 := bstep (se 1 (by rfl) ⟨19728653, by rfl⟩ : syracuseStep 26304871 = 39457307) B39457307
theorem B2024831 : Blo 1348993 2024831 := bstep (se 1 (by rfl) ⟨1518623, by rfl⟩ : syracuseStep 2024831 = 3037247) B3037247
theorem B6834131 : Blo 1348993 6834131 := bstep (se 1 (by rfl) ⟨5125598, by rfl⟩ : syracuseStep 6834131 = 10251197) B10251197
theorem B19729595 : Blo 1348993 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B7687487 : Blo 1348993 7687487 := bstep (se 1 (by rfl) ⟨5765615, by rfl⟩ : syracuseStep 7687487 = 11531231) B11531231
theorem B5123807 : Blo 1348993 5123807 := bstep (se 1 (by rfl) ⟨3842855, by rfl⟩ : syracuseStep 5123807 = 7685711) B7685711
theorem B30012065 : Blo 1348993 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B6837533 : Blo 1348993 6837533 := bstep (se 3 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 6837533 = 2564075) B2564075
theorem B6837695 : Blo 1348993 6837695 := bstep (se 1 (by rfl) ⟨5128271, by rfl⟩ : syracuseStep 6837695 = 10256543) B10256543
theorem B6838991 : Blo 1348993 6838991 := bstep (se 1 (by rfl) ⟨5129243, by rfl⟩ : syracuseStep 6838991 = 10258487) B10258487
theorem B2882279 : Blo 1348993 2882279 := bstep (se 1 (by rfl) ⟨2161709, by rfl⟩ : syracuseStep 2882279 = 4323419) B4323419
theorem B2277119 : Blo 1348993 2277119 := bstep (se 1 (by rfl) ⟨1707839, by rfl⟩ : syracuseStep 2277119 = 3415679) B3415679
theorem B12648271 : Blo 1348993 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B4556087 : Blo 1348993 4556087 := bstep (se 1 (by rfl) ⟨3417065, by rfl⟩ : syracuseStep 4556087 = 6834131) B6834131
theorem B1518079 : Blo 1348993 1518079 := bstep (se 1 (by rfl) ⟨1138559, by rfl⟩ : syracuseStep 1518079 = 2277119) B2277119
theorem B20008043 : Blo 1348993 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B35073161 : Blo 1348993 35073161 := bstep (se 2 (by rfl) ⟨13152435, by rfl⟩ : syracuseStep 35073161 = 26304871) B26304871
theorem B4558355 : Blo 1348993 4558355 := bstep (se 1 (by rfl) ⟨3418766, by rfl⟩ : syracuseStep 4558355 = 6837533) B6837533
theorem B4558463 : Blo 1348993 4558463 := bstep (se 1 (by rfl) ⟨3418847, by rfl⟩ : syracuseStep 4558463 = 6837695) B6837695
theorem B4559327 : Blo 1348993 4559327 := bstep (se 1 (by rfl) ⟨3419495, by rfl⟩ : syracuseStep 4559327 = 6838991) B6838991
theorem B1921519 : Blo 1348993 1921519 := bstep (se 1 (by rfl) ⟨1441139, by rfl⟩ : syracuseStep 1921519 = 2882279) B2882279
theorem B13153063 : Blo 1348993 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B5124991 : Blo 1348993 5124991 := bstep (se 1 (by rfl) ⟨3843743, by rfl⟩ : syracuseStep 5124991 = 7687487) B7687487
theorem B16864361 : Blo 1348993 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B1349887 : Blo 1348993 1349887 := bstep (se 1 (by rfl) ⟨1012415, by rfl⟩ : syracuseStep 1349887 = 2024831) B2024831
theorem B3415871 : Blo 1348993 3415871 := bstep (se 1 (by rfl) ⟨2561903, by rfl⟩ : syracuseStep 3415871 = 5123807) B5123807
theorem B3039551 : Blo 1348993 3039551 := bstep (se 1 (by rfl) ⟨2279663, by rfl⟩ : syracuseStep 3039551 = 4559327) B4559327
theorem B2024105 : Blo 1348993 2024105 := bstep (se 2 (by rfl) ⟨759039, by rfl⟩ : syracuseStep 2024105 = 1518079) B1518079
theorem B6833321 : Blo 1348993 6833321 := bstep (se 2 (by rfl) ⟨2562495, by rfl⟩ : syracuseStep 6833321 = 5124991) B5124991
theorem B13338695 : Blo 1348993 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B23382107 : Blo 1348993 23382107 := bstep (se 1 (by rfl) ⟨17536580, by rfl⟩ : syracuseStep 23382107 = 35073161) B35073161
theorem B11242907 : Blo 1348993 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B2562025 : Blo 1348993 2562025 := bstep (se 2 (by rfl) ⟨960759, by rfl⟩ : syracuseStep 2562025 = 1921519) B1921519
theorem B3037391 : Blo 1348993 3037391 := bstep (se 1 (by rfl) ⟨2278043, by rfl⟩ : syracuseStep 3037391 = 4556087) B4556087
theorem B17537417 : Blo 1348993 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B3038903 : Blo 1348993 3038903 := bstep (se 1 (by rfl) ⟨2279177, by rfl⟩ : syracuseStep 3038903 = 4558355) B4558355
theorem B3038975 : Blo 1348993 3038975 := bstep (se 1 (by rfl) ⟨2279231, by rfl⟩ : syracuseStep 3038975 = 4558463) B4558463
theorem B2277247 : Blo 1348993 2277247 := bstep (se 1 (by rfl) ⟨1707935, by rfl⟩ : syracuseStep 2277247 = 3415871) B3415871
theorem B4555547 : Blo 1348993 4555547 := bstep (se 1 (by rfl) ⟨3416660, by rfl⟩ : syracuseStep 4555547 = 6833321) B6833321
theorem B2024927 : Blo 1348993 2024927 := bstep (se 1 (by rfl) ⟨1518695, by rfl⟩ : syracuseStep 2024927 = 3037391) B3037391
theorem B11691611 : Blo 1348993 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B2025935 : Blo 1348993 2025935 := bstep (se 1 (by rfl) ⟨1519451, by rfl⟩ : syracuseStep 2025935 = 3038903) B3038903
theorem B2025983 : Blo 1348993 2025983 := bstep (se 1 (by rfl) ⟨1519487, by rfl⟩ : syracuseStep 2025983 = 3038975) B3038975
theorem B2026367 : Blo 1348993 2026367 := bstep (se 1 (by rfl) ⟨1519775, by rfl⟩ : syracuseStep 2026367 = 3039551) B3039551
theorem B8892463 : Blo 1348993 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B3036329 : Blo 1348993 3036329 := bstep (se 2 (by rfl) ⟨1138623, by rfl⟩ : syracuseStep 3036329 = 2277247) B2277247
theorem B1349403 : Blo 1348993 1349403 := bstep (se 1 (by rfl) ⟨1012052, by rfl⟩ : syracuseStep 1349403 = 2024105) B2024105
theorem B15588071 : Blo 1348993 15588071 := bstep (se 1 (by rfl) ⟨11691053, by rfl⟩ : syracuseStep 15588071 = 23382107) B23382107
theorem B7495271 : Blo 1348993 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B3416033 : Blo 1348993 3416033 := bstep (se 2 (by rfl) ⟨1281012, by rfl⟩ : syracuseStep 3416033 = 2562025) B2562025
theorem B2024219 : Blo 1348993 2024219 := bstep (se 1 (by rfl) ⟨1518164, by rfl⟩ : syracuseStep 2024219 = 3036329) B3036329
theorem B11856617 : Blo 1348993 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B7794407 : Blo 1348993 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B10392047 : Blo 1348993 10392047 := bstep (se 1 (by rfl) ⟨7794035, by rfl⟩ : syracuseStep 10392047 = 15588071) B15588071
theorem B3037031 : Blo 1348993 3037031 := bstep (se 1 (by rfl) ⟨2277773, by rfl⟩ : syracuseStep 3037031 = 4555547) B4555547
theorem B1349951 : Blo 1348993 1349951 := bstep (se 1 (by rfl) ⟨1012463, by rfl⟩ : syracuseStep 1349951 = 2024927) B2024927
theorem B1350623 : Blo 1348993 1350623 := bstep (se 1 (by rfl) ⟨1012967, by rfl⟩ : syracuseStep 1350623 = 2025935) B2025935
theorem B1350655 : Blo 1348993 1350655 := bstep (se 1 (by rfl) ⟨1012991, by rfl⟩ : syracuseStep 1350655 = 2025983) B2025983
theorem B1350911 : Blo 1348993 1350911 := bstep (se 1 (by rfl) ⟨1013183, by rfl⟩ : syracuseStep 1350911 = 2026367) B2026367
theorem B4996847 : Blo 1348993 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B2277355 : Blo 1348993 2277355 := bstep (se 1 (by rfl) ⟨1708016, by rfl⟩ : syracuseStep 2277355 = 3416033) B3416033
theorem B2024687 : Blo 1348993 2024687 := bstep (se 1 (by rfl) ⟨1518515, by rfl⟩ : syracuseStep 2024687 = 3037031) B3037031
theorem B5196271 : Blo 1348993 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B13324925 : Blo 1348993 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B3036473 : Blo 1348993 3036473 := bstep (se 2 (by rfl) ⟨1138677, by rfl⟩ : syracuseStep 3036473 = 2277355) B2277355
theorem B6928031 : Blo 1348993 6928031 := bstep (se 1 (by rfl) ⟨5196023, by rfl⟩ : syracuseStep 6928031 = 10392047) B10392047
theorem B1349479 : Blo 1348993 1349479 := bstep (se 1 (by rfl) ⟨1012109, by rfl⟩ : syracuseStep 1349479 = 2024219) B2024219
theorem B7904411 : Blo 1348993 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B2024315 : Blo 1348993 2024315 := bstep (se 1 (by rfl) ⟨1518236, by rfl⟩ : syracuseStep 2024315 = 3036473) B3036473
theorem B5269607 : Blo 1348993 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B8883283 : Blo 1348993 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B6928361 : Blo 1348993 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B1349791 : Blo 1348993 1349791 := bstep (se 1 (by rfl) ⟨1012343, by rfl⟩ : syracuseStep 1349791 = 2024687) B2024687
theorem B4618687 : Blo 1348993 4618687 := bstep (se 1 (by rfl) ⟨3464015, by rfl⟩ : syracuseStep 4618687 = 6928031) B6928031
theorem B1349543 : Blo 1348993 1349543 := bstep (se 1 (by rfl) ⟨1012157, by rfl⟩ : syracuseStep 1349543 = 2024315) B2024315
theorem B6158249 : Blo 1348993 6158249 := bstep (se 2 (by rfl) ⟨2309343, by rfl⟩ : syracuseStep 6158249 = 4618687) B4618687
theorem B4618907 : Blo 1348993 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B3513071 : Blo 1348993 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B11844377 : Blo 1348993 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B4105499 : Blo 1348993 4105499 := bstep (se 1 (by rfl) ⟨3079124, by rfl⟩ : syracuseStep 4105499 = 6158249) B6158249
theorem B3079271 : Blo 1348993 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B2342047 : Blo 1348993 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B7896251 : Blo 1348993 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B3122729 : Blo 1348993 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B21056669 : Blo 1348993 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B10947997 : Blo 1348993 10947997 := bstep (se 3 (by rfl) ⟨2052749, by rfl⟩ : syracuseStep 10947997 = 4105499) B4105499
theorem B2052847 : Blo 1348993 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B2737129 : Blo 1348993 2737129 := bstep (se 2 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 2737129 = 2052847) B2052847
theorem B2081819 : Blo 1348993 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B14037779 : Blo 1348993 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B14597329 : Blo 1348993 14597329 := bstep (se 2 (by rfl) ⟨5473998, by rfl⟩ : syracuseStep 14597329 = 10947997) B10947997
theorem B9358519 : Blo 1348993 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B3649505 : Blo 1348993 3649505 := bstep (se 2 (by rfl) ⟨1368564, by rfl⟩ : syracuseStep 3649505 = 2737129) B2737129
theorem B5551517 : Blo 1348993 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B19463105 : Blo 1348993 19463105 := bstep (se 2 (by rfl) ⟨7298664, by rfl⟩ : syracuseStep 19463105 = 14597329) B14597329
theorem B14804045 : Blo 1348993 14804045 := bstep (se 3 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 14804045 = 5551517) B5551517
theorem B12478025 : Blo 1348993 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B12975403 : Blo 1348993 12975403 := bstep (se 1 (by rfl) ⟨9731552, by rfl⟩ : syracuseStep 12975403 = 19463105) B19463105
theorem B38928053 : Blo 1348993 38928053 := bstep (se 5 (by rfl) ⟨1824752, by rfl⟩ : syracuseStep 38928053 = 3649505) B3649505
theorem B8318683 : Blo 1348993 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B9869363 : Blo 1348993 9869363 := bstep (se 1 (by rfl) ⟨7402022, by rfl⟩ : syracuseStep 9869363 = 14804045) B14804045
theorem B17300537 : Blo 1348993 17300537 := bstep (se 2 (by rfl) ⟨6487701, by rfl⟩ : syracuseStep 17300537 = 12975403) B12975403
theorem B25952035 : Blo 1348993 25952035 := bstep (se 1 (by rfl) ⟨19464026, by rfl⟩ : syracuseStep 25952035 = 38928053) B38928053
theorem B6579575 : Blo 1348993 6579575 := bstep (se 1 (by rfl) ⟨4934681, by rfl⟩ : syracuseStep 6579575 = 9869363) B9869363
theorem B11533691 : Blo 1348993 11533691 := bstep (se 1 (by rfl) ⟨8650268, by rfl⟩ : syracuseStep 11533691 = 17300537) B17300537
theorem B11091577 : Blo 1348993 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B34602713 : Blo 1348993 34602713 := bstep (se 2 (by rfl) ⟨12976017, by rfl⟩ : syracuseStep 34602713 = 25952035) B25952035
theorem B14788769 : Blo 1348993 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B4386383 : Blo 1348993 4386383 := bstep (se 1 (by rfl) ⟨3289787, by rfl⟩ : syracuseStep 4386383 = 6579575) B6579575
theorem B7689127 : Blo 1348993 7689127 := bstep (se 1 (by rfl) ⟨5766845, by rfl⟩ : syracuseStep 7689127 = 11533691) B11533691
theorem B23068475 : Blo 1348993 23068475 := bstep (se 1 (by rfl) ⟨17301356, by rfl⟩ : syracuseStep 23068475 = 34602713) B34602713
theorem B39436717 : Blo 1348993 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B15378983 : Blo 1348993 15378983 := bstep (se 1 (by rfl) ⟨11534237, by rfl⟩ : syracuseStep 15378983 = 23068475) B23068475
theorem B10252169 : Blo 1348993 10252169 := bstep (se 2 (by rfl) ⟨3844563, by rfl⟩ : syracuseStep 10252169 = 7689127) B7689127
theorem B2924255 : Blo 1348993 2924255 := bstep (se 1 (by rfl) ⟨2193191, by rfl⟩ : syracuseStep 2924255 = 4386383) B4386383
theorem B6834779 : Blo 1348993 6834779 := bstep (se 1 (by rfl) ⟨5126084, by rfl⟩ : syracuseStep 6834779 = 10252169) B10252169
theorem B10252655 : Blo 1348993 10252655 := bstep (se 1 (by rfl) ⟨7689491, by rfl⟩ : syracuseStep 10252655 = 15378983) B15378983
theorem B52582289 : Blo 1348993 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B1949503 : Blo 1348993 1949503 := bstep (se 1 (by rfl) ⟨1462127, by rfl⟩ : syracuseStep 1949503 = 2924255) B2924255
theorem B4556519 : Blo 1348993 4556519 := bstep (se 1 (by rfl) ⟨3417389, by rfl⟩ : syracuseStep 4556519 = 6834779) B6834779
theorem B2599337 : Blo 1348993 2599337 := bstep (se 2 (by rfl) ⟨974751, by rfl⟩ : syracuseStep 2599337 = 1949503) B1949503
theorem B6835103 : Blo 1348993 6835103 := bstep (se 1 (by rfl) ⟨5126327, by rfl⟩ : syracuseStep 6835103 = 10252655) B10252655
theorem B140219437 : Blo 1348993 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B6931565 : Blo 1348993 6931565 := bstep (se 3 (by rfl) ⟨1299668, by rfl⟩ : syracuseStep 6931565 = 2599337) B2599337
theorem B186959249 : Blo 1348993 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B4556735 : Blo 1348993 4556735 := bstep (se 1 (by rfl) ⟨3417551, by rfl⟩ : syracuseStep 4556735 = 6835103) B6835103
theorem B3037679 : Blo 1348993 3037679 := bstep (se 1 (by rfl) ⟨2278259, by rfl⟩ : syracuseStep 3037679 = 4556519) B4556519
theorem B4621043 : Blo 1348993 4621043 := bstep (se 1 (by rfl) ⟨3465782, by rfl⟩ : syracuseStep 4621043 = 6931565) B6931565
theorem B2025119 : Blo 1348993 2025119 := bstep (se 1 (by rfl) ⟨1518839, by rfl⟩ : syracuseStep 2025119 = 3037679) B3037679
theorem B124639499 : Blo 1348993 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B3037823 : Blo 1348993 3037823 := bstep (se 1 (by rfl) ⟨2278367, by rfl⟩ : syracuseStep 3037823 = 4556735) B4556735
theorem B3080695 : Blo 1348993 3080695 := bstep (se 1 (by rfl) ⟨2310521, by rfl⟩ : syracuseStep 3080695 = 4621043) B4621043
theorem B83092999 : Blo 1348993 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B2025215 : Blo 1348993 2025215 := bstep (se 1 (by rfl) ⟨1518911, by rfl⟩ : syracuseStep 2025215 = 3037823) B3037823
theorem B1350079 : Blo 1348993 1350079 := bstep (se 1 (by rfl) ⟨1012559, by rfl⟩ : syracuseStep 1350079 = 2025119) B2025119
theorem B110790665 : Blo 1348993 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B4107593 : Blo 1348993 4107593 := bstep (se 2 (by rfl) ⟨1540347, by rfl⟩ : syracuseStep 4107593 = 3080695) B3080695
theorem B1350143 : Blo 1348993 1350143 := bstep (se 1 (by rfl) ⟨1012607, by rfl⟩ : syracuseStep 1350143 = 2025215) B2025215
theorem B73860443 : Blo 1348993 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B2738395 : Blo 1348993 2738395 := bstep (se 1 (by rfl) ⟨2053796, by rfl⟩ : syracuseStep 2738395 = 4107593) B4107593
theorem B3651193 : Blo 1348993 3651193 := bstep (se 2 (by rfl) ⟨1369197, by rfl⟩ : syracuseStep 3651193 = 2738395) B2738395
theorem B49240295 : Blo 1348993 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B32826863 : Blo 1348993 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B4868257 : Blo 1348993 4868257 := bstep (se 2 (by rfl) ⟨1825596, by rfl⟩ : syracuseStep 4868257 = 3651193) B3651193
theorem B6491009 : Blo 1348993 6491009 := bstep (se 2 (by rfl) ⟨2434128, by rfl⟩ : syracuseStep 6491009 = 4868257) B4868257
theorem B21884575 : Blo 1348993 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B4327339 : Blo 1348993 4327339 := bstep (se 1 (by rfl) ⟨3245504, by rfl⟩ : syracuseStep 4327339 = 6491009) B6491009
theorem B29179433 : Blo 1348993 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B5769785 : Blo 1348993 5769785 := bstep (se 2 (by rfl) ⟨2163669, by rfl⟩ : syracuseStep 5769785 = 4327339) B4327339
theorem B19452955 : Blo 1348993 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B25937273 : Blo 1348993 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B3846523 : Blo 1348993 3846523 := bstep (se 1 (by rfl) ⟨2884892, by rfl⟩ : syracuseStep 3846523 = 5769785) B5769785
theorem B5128697 : Blo 1348993 5128697 := bstep (se 2 (by rfl) ⟨1923261, by rfl⟩ : syracuseStep 5128697 = 3846523) B3846523
theorem B17291515 : Blo 1348993 17291515 := bstep (se 1 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 17291515 = 25937273) B25937273
theorem B23055353 : Blo 1348993 23055353 := bstep (se 2 (by rfl) ⟨8645757, by rfl⟩ : syracuseStep 23055353 = 17291515) B17291515
theorem B3419131 : Blo 1348993 3419131 := bstep (se 1 (by rfl) ⟨2564348, by rfl⟩ : syracuseStep 3419131 = 5128697) B5128697
theorem B15370235 : Blo 1348993 15370235 := bstep (se 1 (by rfl) ⟨11527676, by rfl⟩ : syracuseStep 15370235 = 23055353) B23055353
theorem B4558841 : Blo 1348993 4558841 := bstep (se 2 (by rfl) ⟨1709565, by rfl⟩ : syracuseStep 4558841 = 3419131) B3419131
theorem B10246823 : Blo 1348993 10246823 := bstep (se 1 (by rfl) ⟨7685117, by rfl⟩ : syracuseStep 10246823 = 15370235) B15370235
theorem B3039227 : Blo 1348993 3039227 := bstep (se 1 (by rfl) ⟨2279420, by rfl⟩ : syracuseStep 3039227 = 4558841) B4558841
theorem B2026151 : Blo 1348993 2026151 := bstep (se 1 (by rfl) ⟨1519613, by rfl⟩ : syracuseStep 2026151 = 3039227) B3039227
theorem B6831215 : Blo 1348993 6831215 := bstep (se 1 (by rfl) ⟨5123411, by rfl⟩ : syracuseStep 6831215 = 10246823) B10246823
theorem B1350767 : Blo 1348993 1350767 := bstep (se 1 (by rfl) ⟨1013075, by rfl⟩ : syracuseStep 1350767 = 2026151) B2026151
theorem B4554143 : Blo 1348993 4554143 := bstep (se 1 (by rfl) ⟨3415607, by rfl⟩ : syracuseStep 4554143 = 6831215) B6831215
theorem B3036095 : Blo 1348993 3036095 := bstep (se 1 (by rfl) ⟨2277071, by rfl⟩ : syracuseStep 3036095 = 4554143) B4554143
theorem B2024063 : Blo 1348993 2024063 := bstep (se 1 (by rfl) ⟨1518047, by rfl⟩ : syracuseStep 2024063 = 3036095) B3036095
theorem B1349375 : Blo 1348993 1349375 := bstep (se 1 (by rfl) ⟨1012031, by rfl⟩ : syracuseStep 1349375 = 2024063) B2024063

theorem C0 (j : ℕ) (h1 : 337248 ≤ j) (h2 : j ≤ 337747) : Blo 1348993 (4 * j + 3) := by
  interval_cases j
  · exact B1348995
  · exact B1348999
  · exact B1349003
  · exact B1349007
  · exact B1349011
  · exact B1349015
  · exact B1349019
  · exact B1349023
  · exact B1349027
  · exact B1349031
  · exact B1349035
  · exact B1349039
  · exact B1349043
  · exact B1349047
  · exact B1349051
  · exact B1349055
  · exact B1349059
  · exact B1349063
  · exact B1349067
  · exact B1349071
  · exact B1349075
  · exact B1349079
  · exact B1349083
  · exact B1349087
  · exact B1349091
  · exact B1349095
  · exact B1349099
  · exact B1349103
  · exact B1349107
  · exact B1349111
  · exact B1349115
  · exact B1349119
  · exact B1349123
  · exact B1349127
  · exact B1349131
  · exact B1349135
  · exact B1349139
  · exact B1349143
  · exact B1349147
  · exact B1349151
  · exact B1349155
  · exact B1349159
  · exact B1349163
  · exact B1349167
  · exact B1349171
  · exact B1349175
  · exact B1349179
  · exact B1349183
  · exact B1349187
  · exact B1349191
  · exact B1349195
  · exact B1349199
  · exact B1349203
  · exact B1349207
  · exact B1349211
  · exact B1349215
  · exact B1349219
  · exact B1349223
  · exact B1349227
  · exact B1349231
  · exact B1349235
  · exact B1349239
  · exact B1349243
  · exact B1349247
  · exact B1349251
  · exact B1349255
  · exact B1349259
  · exact B1349263
  · exact B1349267
  · exact B1349271
  · exact B1349275
  · exact B1349279
  · exact B1349283
  · exact B1349287
  · exact B1349291
  · exact B1349295
  · exact B1349299
  · exact B1349303
  · exact B1349307
  · exact B1349311
  · exact B1349315
  · exact B1349319
  · exact B1349323
  · exact B1349327
  · exact B1349331
  · exact B1349335
  · exact B1349339
  · exact B1349343
  · exact B1349347
  · exact B1349351
  · exact B1349355
  · exact B1349359
  · exact B1349363
  · exact B1349367
  · exact B1349371
  · exact B1349375
  · exact B1349379
  · exact B1349383
  · exact B1349387
  · exact B1349391
  · exact B1349395
  · exact B1349399
  · exact B1349403
  · exact B1349407
  · exact B1349411
  · exact B1349415
  · exact B1349419
  · exact B1349423
  · exact B1349427
  · exact B1349431
  · exact B1349435
  · exact B1349439
  · exact B1349443
  · exact B1349447
  · exact B1349451
  · exact B1349455
  · exact B1349459
  · exact B1349463
  · exact B1349467
  · exact B1349471
  · exact B1349475
  · exact B1349479
  · exact B1349483
  · exact B1349487
  · exact B1349491
  · exact B1349495
  · exact B1349499
  · exact B1349503
  · exact B1349507
  · exact B1349511
  · exact B1349515
  · exact B1349519
  · exact B1349523
  · exact B1349527
  · exact B1349531
  · exact B1349535
  · exact B1349539
  · exact B1349543
  · exact B1349547
  · exact B1349551
  · exact B1349555
  · exact B1349559
  · exact B1349563
  · exact B1349567
  · exact B1349571
  · exact B1349575
  · exact B1349579
  · exact B1349583
  · exact B1349587
  · exact B1349591
  · exact B1349595
  · exact B1349599
  · exact B1349603
  · exact B1349607
  · exact B1349611
  · exact B1349615
  · exact B1349619
  · exact B1349623
  · exact B1349627
  · exact B1349631
  · exact B1349635
  · exact B1349639
  · exact B1349643
  · exact B1349647
  · exact B1349651
  · exact B1349655
  · exact B1349659
  · exact B1349663
  · exact B1349667
  · exact B1349671
  · exact B1349675
  · exact B1349679
  · exact B1349683
  · exact B1349687
  · exact B1349691
  · exact B1349695
  · exact B1349699
  · exact B1349703
  · exact B1349707
  · exact B1349711
  · exact B1349715
  · exact B1349719
  · exact B1349723
  · exact B1349727
  · exact B1349731
  · exact B1349735
  · exact B1349739
  · exact B1349743
  · exact B1349747
  · exact B1349751
  · exact B1349755
  · exact B1349759
  · exact B1349763
  · exact B1349767
  · exact B1349771
  · exact B1349775
  · exact B1349779
  · exact B1349783
  · exact B1349787
  · exact B1349791
  · exact B1349795
  · exact B1349799
  · exact B1349803
  · exact B1349807
  · exact B1349811
  · exact B1349815
  · exact B1349819
  · exact B1349823
  · exact B1349827
  · exact B1349831
  · exact B1349835
  · exact B1349839
  · exact B1349843
  · exact B1349847
  · exact B1349851
  · exact B1349855
  · exact B1349859
  · exact B1349863
  · exact B1349867
  · exact B1349871
  · exact B1349875
  · exact B1349879
  · exact B1349883
  · exact B1349887
  · exact B1349891
  · exact B1349895
  · exact B1349899
  · exact B1349903
  · exact B1349907
  · exact B1349911
  · exact B1349915
  · exact B1349919
  · exact B1349923
  · exact B1349927
  · exact B1349931
  · exact B1349935
  · exact B1349939
  · exact B1349943
  · exact B1349947
  · exact B1349951
  · exact B1349955
  · exact B1349959
  · exact B1349963
  · exact B1349967
  · exact B1349971
  · exact B1349975
  · exact B1349979
  · exact B1349983
  · exact B1349987
  · exact B1349991
  · exact B1349995
  · exact B1349999
  · exact B1350003
  · exact B1350007
  · exact B1350011
  · exact B1350015
  · exact B1350019
  · exact B1350023
  · exact B1350027
  · exact B1350031
  · exact B1350035
  · exact B1350039
  · exact B1350043
  · exact B1350047
  · exact B1350051
  · exact B1350055
  · exact B1350059
  · exact B1350063
  · exact B1350067
  · exact B1350071
  · exact B1350075
  · exact B1350079
  · exact B1350083
  · exact B1350087
  · exact B1350091
  · exact B1350095
  · exact B1350099
  · exact B1350103
  · exact B1350107
  · exact B1350111
  · exact B1350115
  · exact B1350119
  · exact B1350123
  · exact B1350127
  · exact B1350131
  · exact B1350135
  · exact B1350139
  · exact B1350143
  · exact B1350147
  · exact B1350151
  · exact B1350155
  · exact B1350159
  · exact B1350163
  · exact B1350167
  · exact B1350171
  · exact B1350175
  · exact B1350179
  · exact B1350183
  · exact B1350187
  · exact B1350191
  · exact B1350195
  · exact B1350199
  · exact B1350203
  · exact B1350207
  · exact B1350211
  · exact B1350215
  · exact B1350219
  · exact B1350223
  · exact B1350227
  · exact B1350231
  · exact B1350235
  · exact B1350239
  · exact B1350243
  · exact B1350247
  · exact B1350251
  · exact B1350255
  · exact B1350259
  · exact B1350263
  · exact B1350267
  · exact B1350271
  · exact B1350275
  · exact B1350279
  · exact B1350283
  · exact B1350287
  · exact B1350291
  · exact B1350295
  · exact B1350299
  · exact B1350303
  · exact B1350307
  · exact B1350311
  · exact B1350315
  · exact B1350319
  · exact B1350323
  · exact B1350327
  · exact B1350331
  · exact B1350335
  · exact B1350339
  · exact B1350343
  · exact B1350347
  · exact B1350351
  · exact B1350355
  · exact B1350359
  · exact B1350363
  · exact B1350367
  · exact B1350371
  · exact B1350375
  · exact B1350379
  · exact B1350383
  · exact B1350387
  · exact B1350391
  · exact B1350395
  · exact B1350399
  · exact B1350403
  · exact B1350407
  · exact B1350411
  · exact B1350415
  · exact B1350419
  · exact B1350423
  · exact B1350427
  · exact B1350431
  · exact B1350435
  · exact B1350439
  · exact B1350443
  · exact B1350447
  · exact B1350451
  · exact B1350455
  · exact B1350459
  · exact B1350463
  · exact B1350467
  · exact B1350471
  · exact B1350475
  · exact B1350479
  · exact B1350483
  · exact B1350487
  · exact B1350491
  · exact B1350495
  · exact B1350499
  · exact B1350503
  · exact B1350507
  · exact B1350511
  · exact B1350515
  · exact B1350519
  · exact B1350523
  · exact B1350527
  · exact B1350531
  · exact B1350535
  · exact B1350539
  · exact B1350543
  · exact B1350547
  · exact B1350551
  · exact B1350555
  · exact B1350559
  · exact B1350563
  · exact B1350567
  · exact B1350571
  · exact B1350575
  · exact B1350579
  · exact B1350583
  · exact B1350587
  · exact B1350591
  · exact B1350595
  · exact B1350599
  · exact B1350603
  · exact B1350607
  · exact B1350611
  · exact B1350615
  · exact B1350619
  · exact B1350623
  · exact B1350627
  · exact B1350631
  · exact B1350635
  · exact B1350639
  · exact B1350643
  · exact B1350647
  · exact B1350651
  · exact B1350655
  · exact B1350659
  · exact B1350663
  · exact B1350667
  · exact B1350671
  · exact B1350675
  · exact B1350679
  · exact B1350683
  · exact B1350687
  · exact B1350691
  · exact B1350695
  · exact B1350699
  · exact B1350703
  · exact B1350707
  · exact B1350711
  · exact B1350715
  · exact B1350719
  · exact B1350723
  · exact B1350727
  · exact B1350731
  · exact B1350735
  · exact B1350739
  · exact B1350743
  · exact B1350747
  · exact B1350751
  · exact B1350755
  · exact B1350759
  · exact B1350763
  · exact B1350767
  · exact B1350771
  · exact B1350775
  · exact B1350779
  · exact B1350783
  · exact B1350787
  · exact B1350791
  · exact B1350795
  · exact B1350799
  · exact B1350803
  · exact B1350807
  · exact B1350811
  · exact B1350815
  · exact B1350819
  · exact B1350823
  · exact B1350827
  · exact B1350831
  · exact B1350835
  · exact B1350839
  · exact B1350843
  · exact B1350847
  · exact B1350851
  · exact B1350855
  · exact B1350859
  · exact B1350863
  · exact B1350867
  · exact B1350871
  · exact B1350875
  · exact B1350879
  · exact B1350883
  · exact B1350887
  · exact B1350891
  · exact B1350895
  · exact B1350899
  · exact B1350903
  · exact B1350907
  · exact B1350911
  · exact B1350915
  · exact B1350919
  · exact B1350923
  · exact B1350927
  · exact B1350931
  · exact B1350935
  · exact B1350939
  · exact B1350943
  · exact B1350947
  · exact B1350951
  · exact B1350955
  · exact B1350959
  · exact B1350963
  · exact B1350967
  · exact B1350971
  · exact B1350975
  · exact B1350979
  · exact B1350983
  · exact B1350987
  · exact B1350991

theorem solution (m : ℕ) (hlo : 1348993 ≤ m) (hhi : m ≤ 1350993) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 337248 ≤ j := by omega
    have hj2 : j ≤ 337747 := by omega
    have hb : Blo 1348993 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
