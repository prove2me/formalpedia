-- Prove2me | solution 1 for syracuse_descends_range_397767_401767
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:47.915375+00:00
-- url     : https://prove2.me/submissions/065c317f-bab3-47c4-95fa-7a148c6c6709

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


theorem B426017 : Blo 397767 426017 := bbase (se 2 (by rfl) ⟨159756, by rfl⟩ : syracuseStep 426017 = 319513) (by norm_num)
theorem B1015861 : Blo 397767 1015861 := bbase (se 5 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 1015861 = 95237) (by norm_num)
theorem B1343573 : Blo 397767 1343573 := bbase (se 8 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 1343573 = 15745) (by norm_num)
theorem B1015973 : Blo 397767 1015973 := bbase (se 4 (by rfl) ⟨95247, by rfl⟩ : syracuseStep 1015973 = 190495) (by norm_num)
theorem B426269 : Blo 397767 426269 := bbase (se 3 (by rfl) ⟨79925, by rfl⟩ : syracuseStep 426269 = 159851) (by norm_num)
theorem B1016165 : Blo 397767 1016165 := bbase (se 4 (by rfl) ⟨95265, by rfl⟩ : syracuseStep 1016165 = 190531) (by norm_num)
theorem B1704341 : Blo 397767 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B1344005 : Blo 397767 1344005 := bbase (se 4 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 1344005 = 252001) (by norm_num)
theorem B721477 : Blo 397767 721477 := bbase (se 4 (by rfl) ⟨67638, by rfl⟩ : syracuseStep 721477 = 135277) (by norm_num)
theorem B21955157 : Blo 397767 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B852581 : Blo 397767 852581 := bbase (se 4 (by rfl) ⟨79929, by rfl⟩ : syracuseStep 852581 = 159859) (by norm_num)
theorem B1016509 : Blo 397767 1016509 := bbase (se 3 (by rfl) ⟨190595, by rfl⟩ : syracuseStep 1016509 = 381191) (by norm_num)
theorem B426713 : Blo 397767 426713 := bbase (se 2 (by rfl) ⟨160017, by rfl⟩ : syracuseStep 426713 = 320035) (by norm_num)
theorem B852725 : Blo 397767 852725 := bbase (se 5 (by rfl) ⟨39971, by rfl⟩ : syracuseStep 852725 = 79943) (by norm_num)
theorem B1442549 : Blo 397767 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B721693 : Blo 397767 721693 := bbase (se 3 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 721693 = 270635) (by norm_num)
theorem B1016621 : Blo 397767 1016621 := bbase (se 3 (by rfl) ⟨190616, by rfl⟩ : syracuseStep 1016621 = 381233) (by norm_num)
theorem B1540949 : Blo 397767 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B1344437 : Blo 397767 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B426961 : Blo 397767 426961 := bbase (se 2 (by rfl) ⟨160110, by rfl⟩ : syracuseStep 426961 = 320221) (by norm_num)
theorem B2032613 : Blo 397767 2032613 := bbase (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) (by norm_num)
theorem B1016813 : Blo 397767 1016813 := bbase (se 3 (by rfl) ⟨190652, by rfl⟩ : syracuseStep 1016813 = 381305) (by norm_num)
theorem B853085 : Blo 397767 853085 := bbase (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) (by norm_num)
theorem B1344869 : Blo 397767 1344869 := bbase (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) (by norm_num)
theorem B427405 : Blo 397767 427405 := bbase (se 3 (by rfl) ⟨80138, by rfl⟩ : syracuseStep 427405 = 160277) (by norm_num)
theorem B427465 : Blo 397767 427465 := bbase (se 2 (by rfl) ⟨160299, by rfl⟩ : syracuseStep 427465 = 320599) (by norm_num)
theorem B3409397 : Blo 397767 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B755237 : Blo 397767 755237 := bbase (se 4 (by rfl) ⟨70803, by rfl⟩ : syracuseStep 755237 = 141607) (by norm_num)
theorem B755381 : Blo 397767 755381 := bbase (se 5 (by rfl) ⟨35408, by rfl⟩ : syracuseStep 755381 = 70817) (by norm_num)
theorem B427781 : Blo 397767 427781 := bbase (se 4 (by rfl) ⟨40104, by rfl⟩ : syracuseStep 427781 = 80209) (by norm_num)
theorem B1345301 : Blo 397767 1345301 := bbase (se 6 (by rfl) ⟨31530, by rfl⟩ : syracuseStep 1345301 = 63061) (by norm_num)
theorem B722861 : Blo 397767 722861 := bbase (se 3 (by rfl) ⟨135536, by rfl⟩ : syracuseStep 722861 = 271073) (by norm_num)
theorem B755669 : Blo 397767 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B853973 : Blo 397767 853973 := bbase (se 7 (by rfl) ⟨10007, by rfl⟩ : syracuseStep 853973 = 20015) (by norm_num)
theorem B755821 : Blo 397767 755821 := bbase (se 3 (by rfl) ⟨141716, by rfl⟩ : syracuseStep 755821 = 283433) (by norm_num)
theorem B1083557 : Blo 397767 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B428225 : Blo 397767 428225 := bbase (se 2 (by rfl) ⟨160584, by rfl⟩ : syracuseStep 428225 = 321169) (by norm_num)
theorem B1345733 : Blo 397767 1345733 := bbase (se 4 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 1345733 = 252325) (by norm_num)
theorem B854221 : Blo 397767 854221 := bbase (se 3 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 854221 = 320333) (by norm_num)
theorem B2033909 : Blo 397767 2033909 := bbase (se 5 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 2033909 = 190679) (by norm_num)
theorem B428285 : Blo 397767 428285 := bbase (se 3 (by rfl) ⟨80303, by rfl⟩ : syracuseStep 428285 = 160607) (by norm_num)
theorem B5146901 : Blo 397767 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B428413 : Blo 397767 428413 := bbase (se 3 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 428413 = 160655) (by norm_num)
theorem B756125 : Blo 397767 756125 := bbase (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) (by norm_num)
theorem B1280549 : Blo 397767 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B1346165 : Blo 397767 1346165 := bbase (se 5 (by rfl) ⟨63101, by rfl⟩ : syracuseStep 1346165 = 126203) (by norm_num)
theorem B1215157 : Blo 397767 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B854725 : Blo 397767 854725 := bbase (se 4 (by rfl) ⟨80130, by rfl⟩ : syracuseStep 854725 = 160261) (by norm_num)
theorem B428857 : Blo 397767 428857 := bbase (se 2 (by rfl) ⟨160821, by rfl⟩ : syracuseStep 428857 = 321643) (by norm_num)
theorem B461657 : Blo 397767 461657 := bbase (se 2 (by rfl) ⟨173121, by rfl⟩ : syracuseStep 461657 = 346243) (by norm_num)
theorem B428977 : Blo 397767 428977 := bbase (se 2 (by rfl) ⟨160866, by rfl⟩ : syracuseStep 428977 = 321733) (by norm_num)
theorem B1346597 : Blo 397767 1346597 := bbase (se 4 (by rfl) ⟨126243, by rfl⟩ : syracuseStep 1346597 = 252487) (by norm_num)
theorem B756877 : Blo 397767 756877 := bbase (se 3 (by rfl) ⟨141914, by rfl⟩ : syracuseStep 756877 = 283829) (by norm_num)
theorem B757021 : Blo 397767 757021 := bbase (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) (by norm_num)
theorem B1084853 : Blo 397767 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B757181 : Blo 397767 757181 := bbase (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) (by norm_num)
theorem B1347029 : Blo 397767 1347029 := bbase (se 7 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 1347029 = 31571) (by norm_num)
theorem B2559509 : Blo 397767 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B1248821 : Blo 397767 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B855613 : Blo 397767 855613 := bbase (se 3 (by rfl) ⟨160427, by rfl⟩ : syracuseStep 855613 = 320855) (by norm_num)
theorem B757325 : Blo 397767 757325 := bbase (se 3 (by rfl) ⟨141998, by rfl⟩ : syracuseStep 757325 = 283997) (by norm_num)
theorem B1707637 : Blo 397767 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1281845 : Blo 397767 1281845 := bbase (se 5 (by rfl) ⟨60086, by rfl⟩ : syracuseStep 1281845 = 120173) (by norm_num)
theorem B757613 : Blo 397767 757613 := bbase (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) (by norm_num)
theorem B2723701 : Blo 397767 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1347461 : Blo 397767 1347461 := bbase (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) (by norm_num)
theorem B692173 : Blo 397767 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B757765 : Blo 397767 757765 := bbase (se 4 (by rfl) ⟨71040, by rfl⟩ : syracuseStep 757765 = 142081) (by norm_num)
theorem B856109 : Blo 397767 856109 := bbase (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) (by norm_num)
theorem B758069 : Blo 397767 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B1347893 : Blo 397767 1347893 := bbase (se 5 (by rfl) ⟨63182, by rfl⟩ : syracuseStep 1347893 = 126365) (by norm_num)
theorem B2298293 : Blo 397767 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B1512053 : Blo 397767 1512053 := bbase (se 5 (by rfl) ⟨70877, by rfl⟩ : syracuseStep 1512053 = 141755) (by norm_num)
theorem B1348325 : Blo 397767 1348325 := bbase (se 4 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 1348325 = 252811) (by norm_num)
theorem B1512341 : Blo 397767 1512341 := bbase (se 6 (by rfl) ⟨35445, by rfl⟩ : syracuseStep 1512341 = 70891) (by norm_num)
theorem B856997 : Blo 397767 856997 := bbase (se 4 (by rfl) ⟨80343, by rfl⟩ : syracuseStep 856997 = 160687) (by norm_num)
theorem B857117 : Blo 397767 857117 := bbase (se 3 (by rfl) ⟨160709, by rfl⟩ : syracuseStep 857117 = 321419) (by norm_num)
theorem B758821 : Blo 397767 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B1348757 : Blo 397767 1348757 := bbase (se 6 (by rfl) ⟨31611, by rfl⟩ : syracuseStep 1348757 = 63223) (by norm_num)
theorem B758965 : Blo 397767 758965 := bbase (se 5 (by rfl) ⟨35576, by rfl⟩ : syracuseStep 758965 = 71153) (by norm_num)
theorem B1021133 : Blo 397767 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B2266325 : Blo 397767 2266325 := bbase (se 7 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 2266325 = 53117) (by norm_num)
theorem B759125 : Blo 397767 759125 := bbase (se 14 (by rfl) ⟨69, by rfl⟩ : syracuseStep 759125 = 139) (by norm_num)
theorem B2168149 : Blo 397767 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B1021349 : Blo 397767 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B759269 : Blo 397767 759269 := bbase (se 4 (by rfl) ⟨71181, by rfl⟩ : syracuseStep 759269 = 142363) (by norm_num)
theorem B1218053 : Blo 397767 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B955925 : Blo 397767 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B1349189 : Blo 397767 1349189 := bbase (se 4 (by rfl) ⟨126486, by rfl⟩ : syracuseStep 1349189 = 252973) (by norm_num)
theorem B1283701 : Blo 397767 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B857749 : Blo 397767 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B759557 : Blo 397767 759557 := bbase (se 4 (by rfl) ⟨71208, by rfl⟩ : syracuseStep 759557 = 142417) (by norm_num)
theorem B956261 : Blo 397767 956261 := bbase (se 4 (by rfl) ⟨89649, by rfl⟩ : syracuseStep 956261 = 179299) (by norm_num)
theorem B759709 : Blo 397767 759709 := bbase (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) (by norm_num)
theorem B956357 : Blo 397767 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B1349621 : Blo 397767 1349621 := bbase (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) (by norm_num)
theorem B694261 : Blo 397767 694261 := bbase (se 5 (by rfl) ⟨32543, by rfl⟩ : syracuseStep 694261 = 65087) (by norm_num)
theorem B1513525 : Blo 397767 1513525 := bbase (se 5 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 1513525 = 141893) (by norm_num)
theorem B956549 : Blo 397767 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B760013 : Blo 397767 760013 := bbase (se 3 (by rfl) ⟨142502, by rfl⟩ : syracuseStep 760013 = 285005) (by norm_num)
theorem B1513829 : Blo 397767 1513829 := bbase (se 4 (by rfl) ⟨141921, by rfl⟩ : syracuseStep 1513829 = 283843) (by norm_num)
theorem B1350053 : Blo 397767 1350053 := bbase (se 4 (by rfl) ⟨126567, by rfl⟩ : syracuseStep 1350053 = 253135) (by norm_num)
theorem B1710629 : Blo 397767 1710629 := bbase (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) (by norm_num)
theorem B3021461 : Blo 397767 3021461 := bbase (se 6 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 3021461 = 141631) (by norm_num)
theorem B596669 : Blo 397767 596669 := bbase (se 3 (by rfl) ⟨111875, by rfl⟩ : syracuseStep 596669 = 223751) (by norm_num)
theorem B596693 : Blo 397767 596693 := bbase (se 7 (by rfl) ⟨6992, by rfl⟩ : syracuseStep 596693 = 13985) (by norm_num)
theorem B596717 : Blo 397767 596717 := bbase (se 3 (by rfl) ⟨111884, by rfl⟩ : syracuseStep 596717 = 223769) (by norm_num)
theorem B596741 : Blo 397767 596741 := bbase (se 4 (by rfl) ⟨55944, by rfl⟩ : syracuseStep 596741 = 111889) (by norm_num)
theorem B596765 : Blo 397767 596765 := bbase (se 3 (by rfl) ⟨111893, by rfl⟩ : syracuseStep 596765 = 223787) (by norm_num)
theorem B596789 : Blo 397767 596789 := bbase (se 5 (by rfl) ⟨27974, by rfl⟩ : syracuseStep 596789 = 55949) (by norm_num)
theorem B596813 : Blo 397767 596813 := bbase (se 3 (by rfl) ⟨111902, by rfl⟩ : syracuseStep 596813 = 223805) (by norm_num)
theorem B3119957 : Blo 397767 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B1350485 : Blo 397767 1350485 := bbase (se 9 (by rfl) ⟨3956, by rfl⟩ : syracuseStep 1350485 = 7913) (by norm_num)
theorem B596837 : Blo 397767 596837 := bbase (se 4 (by rfl) ⟨55953, by rfl⟩ : syracuseStep 596837 = 111907) (by norm_num)
theorem B596861 : Blo 397767 596861 := bbase (se 3 (by rfl) ⟨111911, by rfl⟩ : syracuseStep 596861 = 223823) (by norm_num)
theorem B596885 : Blo 397767 596885 := bbase (se 6 (by rfl) ⟨13989, by rfl⟩ : syracuseStep 596885 = 27979) (by norm_num)
theorem B596909 : Blo 397767 596909 := bbase (se 3 (by rfl) ⟨111920, by rfl⟩ : syracuseStep 596909 = 223841) (by norm_num)
theorem B760765 : Blo 397767 760765 := bbase (se 3 (by rfl) ⟨142643, by rfl⟩ : syracuseStep 760765 = 285287) (by norm_num)
theorem B596933 : Blo 397767 596933 := bbase (se 4 (by rfl) ⟨55962, by rfl⟩ : syracuseStep 596933 = 111925) (by norm_num)
theorem B596957 : Blo 397767 596957 := bbase (se 3 (by rfl) ⟨111929, by rfl⟩ : syracuseStep 596957 = 223859) (by norm_num)
theorem B596981 : Blo 397767 596981 := bbase (se 5 (by rfl) ⟨27983, by rfl⟩ : syracuseStep 596981 = 55967) (by norm_num)
theorem B597005 : Blo 397767 597005 := bbase (se 3 (by rfl) ⟨111938, by rfl⟩ : syracuseStep 597005 = 223877) (by norm_num)
theorem B597029 : Blo 397767 597029 := bbase (se 4 (by rfl) ⟨55971, by rfl⟩ : syracuseStep 597029 = 111943) (by norm_num)
theorem B597053 : Blo 397767 597053 := bbase (se 3 (by rfl) ⟨111947, by rfl⟩ : syracuseStep 597053 = 223895) (by norm_num)
theorem B760909 : Blo 397767 760909 := bbase (se 3 (by rfl) ⟨142670, by rfl⟩ : syracuseStep 760909 = 285341) (by norm_num)
theorem B597077 : Blo 397767 597077 := bbase (se 8 (by rfl) ⟨3498, by rfl⟩ : syracuseStep 597077 = 6997) (by norm_num)
theorem B597101 : Blo 397767 597101 := bbase (se 3 (by rfl) ⟨111956, by rfl⟩ : syracuseStep 597101 = 223913) (by norm_num)
theorem B597125 : Blo 397767 597125 := bbase (se 4 (by rfl) ⟨55980, by rfl⟩ : syracuseStep 597125 = 111961) (by norm_num)
theorem B597149 : Blo 397767 597149 := bbase (se 3 (by rfl) ⟨111965, by rfl⟩ : syracuseStep 597149 = 223931) (by norm_num)
theorem B597173 : Blo 397767 597173 := bbase (se 5 (by rfl) ⟨27992, by rfl⟩ : syracuseStep 597173 = 55985) (by norm_num)
theorem B597197 : Blo 397767 597197 := bbase (se 3 (by rfl) ⟨111974, by rfl⟩ : syracuseStep 597197 = 223949) (by norm_num)
theorem B2923733 : Blo 397767 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B597221 : Blo 397767 597221 := bbase (se 4 (by rfl) ⟨55989, by rfl⟩ : syracuseStep 597221 = 111979) (by norm_num)
theorem B761069 : Blo 397767 761069 := bbase (se 3 (by rfl) ⟨142700, by rfl⟩ : syracuseStep 761069 = 285401) (by norm_num)
theorem B597245 : Blo 397767 597245 := bbase (se 3 (by rfl) ⟨111983, by rfl⟩ : syracuseStep 597245 = 223967) (by norm_num)
theorem B957701 : Blo 397767 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B1350917 : Blo 397767 1350917 := bbase (se 4 (by rfl) ⟨126648, by rfl⟩ : syracuseStep 1350917 = 253297) (by norm_num)
theorem B597269 : Blo 397767 597269 := bbase (se 6 (by rfl) ⟨13998, by rfl⟩ : syracuseStep 597269 = 27997) (by norm_num)
theorem B597293 : Blo 397767 597293 := bbase (se 3 (by rfl) ⟨111992, by rfl⟩ : syracuseStep 597293 = 223985) (by norm_num)
theorem B597317 : Blo 397767 597317 := bbase (se 4 (by rfl) ⟨55998, by rfl⟩ : syracuseStep 597317 = 111997) (by norm_num)
theorem B1613141 : Blo 397767 1613141 := bbase (se 11 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1613141 = 2363) (by norm_num)
theorem B597341 : Blo 397767 597341 := bbase (se 3 (by rfl) ⟨112001, by rfl⟩ : syracuseStep 597341 = 224003) (by norm_num)
theorem B597365 : Blo 397767 597365 := bbase (se 5 (by rfl) ⟨28001, by rfl⟩ : syracuseStep 597365 = 56003) (by norm_num)
theorem B761213 : Blo 397767 761213 := bbase (se 3 (by rfl) ⟨142727, by rfl⟩ : syracuseStep 761213 = 285455) (by norm_num)
theorem B597389 : Blo 397767 597389 := bbase (se 3 (by rfl) ⟨112010, by rfl⟩ : syracuseStep 597389 = 224021) (by norm_num)
theorem B597413 : Blo 397767 597413 := bbase (se 4 (by rfl) ⟨56007, by rfl⟩ : syracuseStep 597413 = 112015) (by norm_num)
theorem B597437 : Blo 397767 597437 := bbase (se 3 (by rfl) ⟨112019, by rfl⟩ : syracuseStep 597437 = 224039) (by norm_num)
theorem B597461 : Blo 397767 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B597485 : Blo 397767 597485 := bbase (se 3 (by rfl) ⟨112028, by rfl⟩ : syracuseStep 597485 = 224057) (by norm_num)
theorem B597509 : Blo 397767 597509 := bbase (se 4 (by rfl) ⟨56016, by rfl⟩ : syracuseStep 597509 = 112033) (by norm_num)
theorem B1711637 : Blo 397767 1711637 := bbase (se 6 (by rfl) ⟨40116, by rfl⟩ : syracuseStep 1711637 = 80233) (by norm_num)
theorem B597533 : Blo 397767 597533 := bbase (se 3 (by rfl) ⟨112037, by rfl⟩ : syracuseStep 597533 = 224075) (by norm_num)
theorem B597557 : Blo 397767 597557 := bbase (se 5 (by rfl) ⟨28010, by rfl⟩ : syracuseStep 597557 = 56021) (by norm_num)
theorem B597581 : Blo 397767 597581 := bbase (se 3 (by rfl) ⟨112046, by rfl⟩ : syracuseStep 597581 = 224093) (by norm_num)
theorem B597605 : Blo 397767 597605 := bbase (se 4 (by rfl) ⟨56025, by rfl⟩ : syracuseStep 597605 = 112051) (by norm_num)
theorem B597629 : Blo 397767 597629 := bbase (se 3 (by rfl) ⟨112055, by rfl⟩ : syracuseStep 597629 = 224111) (by norm_num)
theorem B597653 : Blo 397767 597653 := bbase (se 6 (by rfl) ⟨14007, by rfl⟩ : syracuseStep 597653 = 28015) (by norm_num)
theorem B761501 : Blo 397767 761501 := bbase (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) (by norm_num)
theorem B597677 : Blo 397767 597677 := bbase (se 3 (by rfl) ⟨112064, by rfl⟩ : syracuseStep 597677 = 224129) (by norm_num)
theorem B1351349 : Blo 397767 1351349 := bbase (se 5 (by rfl) ⟨63344, by rfl⟩ : syracuseStep 1351349 = 126689) (by norm_num)
theorem B597701 : Blo 397767 597701 := bbase (se 4 (by rfl) ⟨56034, by rfl⟩ : syracuseStep 597701 = 112069) (by norm_num)
theorem B597725 : Blo 397767 597725 := bbase (se 3 (by rfl) ⟨112073, by rfl⟩ : syracuseStep 597725 = 224147) (by norm_num)
theorem B597749 : Blo 397767 597749 := bbase (se 5 (by rfl) ⟨28019, by rfl⟩ : syracuseStep 597749 = 56039) (by norm_num)
theorem B597773 : Blo 397767 597773 := bbase (se 3 (by rfl) ⟨112082, by rfl⟩ : syracuseStep 597773 = 224165) (by norm_num)
theorem B1154837 : Blo 397767 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B597797 : Blo 397767 597797 := bbase (se 4 (by rfl) ⟨56043, by rfl⟩ : syracuseStep 597797 = 112087) (by norm_num)
theorem B761653 : Blo 397767 761653 := bbase (se 5 (by rfl) ⟨35702, by rfl⟩ : syracuseStep 761653 = 71405) (by norm_num)
theorem B597821 : Blo 397767 597821 := bbase (se 3 (by rfl) ⟨112091, by rfl⟩ : syracuseStep 597821 = 224183) (by norm_num)
theorem B597845 : Blo 397767 597845 := bbase (se 9 (by rfl) ⟨1751, by rfl⟩ : syracuseStep 597845 = 3503) (by norm_num)
theorem B597869 : Blo 397767 597869 := bbase (se 3 (by rfl) ⟨112100, by rfl⟩ : syracuseStep 597869 = 224201) (by norm_num)
theorem B597893 : Blo 397767 597893 := bbase (se 4 (by rfl) ⟨56052, by rfl⟩ : syracuseStep 597893 = 112105) (by norm_num)
theorem B597917 : Blo 397767 597917 := bbase (se 3 (by rfl) ⟨112109, by rfl⟩ : syracuseStep 597917 = 224219) (by norm_num)
theorem B597941 : Blo 397767 597941 := bbase (se 5 (by rfl) ⟨28028, by rfl⟩ : syracuseStep 597941 = 56057) (by norm_num)
theorem B597965 : Blo 397767 597965 := bbase (se 3 (by rfl) ⟨112118, by rfl⟩ : syracuseStep 597965 = 224237) (by norm_num)
theorem B597989 : Blo 397767 597989 := bbase (se 4 (by rfl) ⟨56061, by rfl⟩ : syracuseStep 597989 = 112123) (by norm_num)
theorem B598013 : Blo 397767 598013 := bbase (se 3 (by rfl) ⟨112127, by rfl⟩ : syracuseStep 598013 = 224255) (by norm_num)
theorem B598037 : Blo 397767 598037 := bbase (se 6 (by rfl) ⟨14016, by rfl⟩ : syracuseStep 598037 = 28033) (by norm_num)
theorem B598061 : Blo 397767 598061 := bbase (se 3 (by rfl) ⟨112136, by rfl⟩ : syracuseStep 598061 = 224273) (by norm_num)
theorem B598085 : Blo 397767 598085 := bbase (se 4 (by rfl) ⟨56070, by rfl⟩ : syracuseStep 598085 = 112141) (by norm_num)
theorem B598109 : Blo 397767 598109 := bbase (se 3 (by rfl) ⟨112145, by rfl⟩ : syracuseStep 598109 = 224291) (by norm_num)
theorem B1351781 : Blo 397767 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B761957 : Blo 397767 761957 := bbase (se 4 (by rfl) ⟨71433, by rfl⟩ : syracuseStep 761957 = 142867) (by norm_num)
theorem B598133 : Blo 397767 598133 := bbase (se 5 (by rfl) ⟨28037, by rfl⟩ : syracuseStep 598133 = 56075) (by norm_num)
theorem B598157 : Blo 397767 598157 := bbase (se 3 (by rfl) ⟨112154, by rfl⟩ : syracuseStep 598157 = 224309) (by norm_num)
theorem B598181 : Blo 397767 598181 := bbase (se 4 (by rfl) ⟨56079, by rfl⟩ : syracuseStep 598181 = 112159) (by norm_num)
theorem B598205 : Blo 397767 598205 := bbase (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) (by norm_num)
theorem B598229 : Blo 397767 598229 := bbase (se 7 (by rfl) ⟨7010, by rfl⟩ : syracuseStep 598229 = 14021) (by norm_num)
theorem B4923605 : Blo 397767 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B598253 : Blo 397767 598253 := bbase (se 3 (by rfl) ⟨112172, by rfl⟩ : syracuseStep 598253 = 224345) (by norm_num)
theorem B598277 : Blo 397767 598277 := bbase (se 4 (by rfl) ⟨56088, by rfl⟩ : syracuseStep 598277 = 112177) (by norm_num)
theorem B598301 : Blo 397767 598301 := bbase (se 3 (by rfl) ⟨112181, by rfl⟩ : syracuseStep 598301 = 224363) (by norm_num)
theorem B598325 : Blo 397767 598325 := bbase (se 5 (by rfl) ⟨28046, by rfl⟩ : syracuseStep 598325 = 56093) (by norm_num)
theorem B598349 : Blo 397767 598349 := bbase (se 3 (by rfl) ⟨112190, by rfl⟩ : syracuseStep 598349 = 224381) (by norm_num)
theorem B598373 : Blo 397767 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B598397 : Blo 397767 598397 := bbase (se 3 (by rfl) ⟨112199, by rfl⟩ : syracuseStep 598397 = 224399) (by norm_num)
theorem B598421 : Blo 397767 598421 := bbase (se 6 (by rfl) ⟨14025, by rfl⟩ : syracuseStep 598421 = 28051) (by norm_num)
theorem B1515941 : Blo 397767 1515941 := bbase (se 4 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 1515941 = 284239) (by norm_num)
theorem B598445 : Blo 397767 598445 := bbase (se 3 (by rfl) ⟨112208, by rfl⟩ : syracuseStep 598445 = 224417) (by norm_num)
theorem B598469 : Blo 397767 598469 := bbase (se 4 (by rfl) ⟨56106, by rfl⟩ : syracuseStep 598469 = 112213) (by norm_num)
theorem B598493 : Blo 397767 598493 := bbase (se 3 (by rfl) ⟨112217, by rfl⟩ : syracuseStep 598493 = 224435) (by norm_num)
theorem B598517 : Blo 397767 598517 := bbase (se 5 (by rfl) ⟨28055, by rfl⟩ : syracuseStep 598517 = 56111) (by norm_num)
theorem B598541 : Blo 397767 598541 := bbase (se 3 (by rfl) ⟨112226, by rfl⟩ : syracuseStep 598541 = 224453) (by norm_num)
theorem B1352213 : Blo 397767 1352213 := bbase (se 6 (by rfl) ⟨31692, by rfl⟩ : syracuseStep 1352213 = 63385) (by norm_num)
theorem B598565 : Blo 397767 598565 := bbase (se 4 (by rfl) ⟨56115, by rfl⟩ : syracuseStep 598565 = 112231) (by norm_num)
theorem B598589 : Blo 397767 598589 := bbase (se 3 (by rfl) ⟨112235, by rfl⟩ : syracuseStep 598589 = 224471) (by norm_num)
theorem B598613 : Blo 397767 598613 := bbase (se 8 (by rfl) ⟨3507, by rfl⟩ : syracuseStep 598613 = 7015) (by norm_num)
theorem B598637 : Blo 397767 598637 := bbase (se 3 (by rfl) ⟨112244, by rfl⟩ : syracuseStep 598637 = 224489) (by norm_num)
theorem B598661 : Blo 397767 598661 := bbase (se 4 (by rfl) ⟨56124, by rfl⟩ : syracuseStep 598661 = 112249) (by norm_num)
theorem B598685 : Blo 397767 598685 := bbase (se 3 (by rfl) ⟨112253, by rfl⟩ : syracuseStep 598685 = 224507) (by norm_num)
theorem B598709 : Blo 397767 598709 := bbase (se 5 (by rfl) ⟨28064, by rfl⟩ : syracuseStep 598709 = 56129) (by norm_num)
theorem B1516229 : Blo 397767 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B598733 : Blo 397767 598733 := bbase (se 3 (by rfl) ⟨112262, by rfl⟩ : syracuseStep 598733 = 224525) (by norm_num)
theorem B598757 : Blo 397767 598757 := bbase (se 4 (by rfl) ⟨56133, by rfl⟩ : syracuseStep 598757 = 112267) (by norm_num)
theorem B598781 : Blo 397767 598781 := bbase (se 3 (by rfl) ⟨112271, by rfl⟩ : syracuseStep 598781 = 224543) (by norm_num)
theorem B598805 : Blo 397767 598805 := bbase (se 6 (by rfl) ⟨14034, by rfl⟩ : syracuseStep 598805 = 28069) (by norm_num)
theorem B598829 : Blo 397767 598829 := bbase (se 3 (by rfl) ⟨112280, by rfl⟩ : syracuseStep 598829 = 224561) (by norm_num)
theorem B598853 : Blo 397767 598853 := bbase (se 4 (by rfl) ⟨56142, by rfl⟩ : syracuseStep 598853 = 112285) (by norm_num)
theorem B762709 : Blo 397767 762709 := bbase (se 9 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 762709 = 4469) (by norm_num)
theorem B598877 : Blo 397767 598877 := bbase (se 3 (by rfl) ⟨112289, by rfl⟩ : syracuseStep 598877 = 224579) (by norm_num)
theorem B598901 : Blo 397767 598901 := bbase (se 5 (by rfl) ⟨28073, by rfl⟩ : syracuseStep 598901 = 56147) (by norm_num)
theorem B598925 : Blo 397767 598925 := bbase (se 3 (by rfl) ⟨112298, by rfl⟩ : syracuseStep 598925 = 224597) (by norm_num)
theorem B598949 : Blo 397767 598949 := bbase (se 4 (by rfl) ⟨56151, by rfl⟩ : syracuseStep 598949 = 112303) (by norm_num)
theorem B598973 : Blo 397767 598973 := bbase (se 3 (by rfl) ⟨112307, by rfl⟩ : syracuseStep 598973 = 224615) (by norm_num)
theorem B1352645 : Blo 397767 1352645 := bbase (se 4 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 1352645 = 253621) (by norm_num)
theorem B598997 : Blo 397767 598997 := bbase (se 7 (by rfl) ⟨7019, by rfl⟩ : syracuseStep 598997 = 14039) (by norm_num)
theorem B599021 : Blo 397767 599021 := bbase (se 3 (by rfl) ⟨112316, by rfl⟩ : syracuseStep 599021 = 224633) (by norm_num)
theorem B599045 : Blo 397767 599045 := bbase (se 4 (by rfl) ⟨56160, by rfl⟩ : syracuseStep 599045 = 112321) (by norm_num)
theorem B599069 : Blo 397767 599069 := bbase (se 3 (by rfl) ⟨112325, by rfl⟩ : syracuseStep 599069 = 224651) (by norm_num)
theorem B599093 : Blo 397767 599093 := bbase (se 5 (by rfl) ⟨28082, by rfl⟩ : syracuseStep 599093 = 56165) (by norm_num)
theorem B599117 : Blo 397767 599117 := bbase (se 3 (by rfl) ⟨112334, by rfl⟩ : syracuseStep 599117 = 224669) (by norm_num)
theorem B566365 : Blo 397767 566365 := bbase (se 3 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 566365 = 212387) (by norm_num)
theorem B599141 : Blo 397767 599141 := bbase (se 4 (by rfl) ⟨56169, by rfl⟩ : syracuseStep 599141 = 112339) (by norm_num)
theorem B599165 : Blo 397767 599165 := bbase (se 3 (by rfl) ⟨112343, by rfl⟩ : syracuseStep 599165 = 224687) (by norm_num)
theorem B599189 : Blo 397767 599189 := bbase (se 6 (by rfl) ⟨14043, by rfl⟩ : syracuseStep 599189 = 28087) (by norm_num)
theorem B599213 : Blo 397767 599213 := bbase (se 3 (by rfl) ⟨112352, by rfl⟩ : syracuseStep 599213 = 224705) (by norm_num)
theorem B828613 : Blo 397767 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B599237 : Blo 397767 599237 := bbase (se 4 (by rfl) ⟨56178, by rfl⟩ : syracuseStep 599237 = 112357) (by norm_num)
theorem B959701 : Blo 397767 959701 := bbase (se 7 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 959701 = 22493) (by norm_num)
theorem B599261 : Blo 397767 599261 := bbase (se 3 (by rfl) ⟨112361, by rfl⟩ : syracuseStep 599261 = 224723) (by norm_num)
theorem B599285 : Blo 397767 599285 := bbase (se 5 (by rfl) ⟨28091, by rfl⟩ : syracuseStep 599285 = 56183) (by norm_num)
theorem B1713413 : Blo 397767 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B599309 : Blo 397767 599309 := bbase (se 3 (by rfl) ⟨112370, by rfl⟩ : syracuseStep 599309 = 224741) (by norm_num)
theorem B599333 : Blo 397767 599333 := bbase (se 4 (by rfl) ⟨56187, by rfl⟩ : syracuseStep 599333 = 112375) (by norm_num)
theorem B959797 : Blo 397767 959797 := bbase (se 5 (by rfl) ⟨44990, by rfl⟩ : syracuseStep 959797 = 89981) (by norm_num)
theorem B599357 : Blo 397767 599357 := bbase (se 3 (by rfl) ⟨112379, by rfl⟩ : syracuseStep 599357 = 224759) (by norm_num)
theorem B599381 : Blo 397767 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B599405 : Blo 397767 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B3417461 : Blo 397767 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B1353077 : Blo 397767 1353077 := bbase (se 5 (by rfl) ⟨63425, by rfl⟩ : syracuseStep 1353077 = 126851) (by norm_num)
theorem B599429 : Blo 397767 599429 := bbase (se 4 (by rfl) ⟨56196, by rfl⟩ : syracuseStep 599429 = 112393) (by norm_num)
theorem B599453 : Blo 397767 599453 := bbase (se 3 (by rfl) ⟨112397, by rfl⟩ : syracuseStep 599453 = 224795) (by norm_num)
theorem B599477 : Blo 397767 599477 := bbase (se 5 (by rfl) ⟨28100, by rfl⟩ : syracuseStep 599477 = 56201) (by norm_num)
theorem B2565557 : Blo 397767 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B599501 : Blo 397767 599501 := bbase (se 3 (by rfl) ⟨112406, by rfl⟩ : syracuseStep 599501 = 224813) (by norm_num)
theorem B2041301 : Blo 397767 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B599525 : Blo 397767 599525 := bbase (se 4 (by rfl) ⟨56205, by rfl⟩ : syracuseStep 599525 = 112411) (by norm_num)
theorem B599549 : Blo 397767 599549 := bbase (se 3 (by rfl) ⟨112415, by rfl⟩ : syracuseStep 599549 = 224831) (by norm_num)
theorem B599573 : Blo 397767 599573 := bbase (se 6 (by rfl) ⟨14052, by rfl⟩ : syracuseStep 599573 = 28105) (by norm_num)
theorem B2041381 : Blo 397767 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B599597 : Blo 397767 599597 := bbase (se 3 (by rfl) ⟨112424, by rfl⟩ : syracuseStep 599597 = 224849) (by norm_num)
theorem B599621 : Blo 397767 599621 := bbase (se 4 (by rfl) ⟨56214, by rfl⟩ : syracuseStep 599621 = 112429) (by norm_num)
theorem B599645 : Blo 397767 599645 := bbase (se 3 (by rfl) ⟨112433, by rfl⟩ : syracuseStep 599645 = 224867) (by norm_num)
theorem B599669 : Blo 397767 599669 := bbase (se 5 (by rfl) ⟨28109, by rfl⟩ : syracuseStep 599669 = 56219) (by norm_num)
theorem B599693 : Blo 397767 599693 := bbase (se 3 (by rfl) ⟨112442, by rfl⟩ : syracuseStep 599693 = 224885) (by norm_num)
theorem B599717 : Blo 397767 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B566957 : Blo 397767 566957 := bbase (se 3 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 566957 = 212609) (by norm_num)
theorem B599741 : Blo 397767 599741 := bbase (se 3 (by rfl) ⟨112451, by rfl⟩ : syracuseStep 599741 = 224903) (by norm_num)
theorem B599765 : Blo 397767 599765 := bbase (se 7 (by rfl) ⟨7028, by rfl⟩ : syracuseStep 599765 = 14057) (by norm_num)
theorem B599789 : Blo 397767 599789 := bbase (se 3 (by rfl) ⟨112460, by rfl⟩ : syracuseStep 599789 = 224921) (by norm_num)
theorem B567037 : Blo 397767 567037 := bbase (se 3 (by rfl) ⟨106319, by rfl⟩ : syracuseStep 567037 = 212639) (by norm_num)
theorem B599813 : Blo 397767 599813 := bbase (se 4 (by rfl) ⟨56232, by rfl⟩ : syracuseStep 599813 = 112465) (by norm_num)
theorem B599837 : Blo 397767 599837 := bbase (se 3 (by rfl) ⟨112469, by rfl⟩ : syracuseStep 599837 = 224939) (by norm_num)
theorem B1353509 : Blo 397767 1353509 := bbase (se 4 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 1353509 = 253783) (by norm_num)
theorem B599861 : Blo 397767 599861 := bbase (se 5 (by rfl) ⟨28118, by rfl⟩ : syracuseStep 599861 = 56237) (by norm_num)
theorem B599885 : Blo 397767 599885 := bbase (se 3 (by rfl) ⟨112478, by rfl⟩ : syracuseStep 599885 = 224957) (by norm_num)
theorem B1517413 : Blo 397767 1517413 := bbase (se 4 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 1517413 = 284515) (by norm_num)
theorem B599909 : Blo 397767 599909 := bbase (se 4 (by rfl) ⟨56241, by rfl⟩ : syracuseStep 599909 = 112483) (by norm_num)
theorem B567157 : Blo 397767 567157 := bbase (se 5 (by rfl) ⟨26585, by rfl⟩ : syracuseStep 567157 = 53171) (by norm_num)
theorem B1615733 : Blo 397767 1615733 := bbase (se 5 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 1615733 = 151475) (by norm_num)
theorem B599933 : Blo 397767 599933 := bbase (se 3 (by rfl) ⟨112487, by rfl⟩ : syracuseStep 599933 = 224975) (by norm_num)
theorem B599957 : Blo 397767 599957 := bbase (se 6 (by rfl) ⟨14061, by rfl⟩ : syracuseStep 599957 = 28123) (by norm_num)
theorem B599981 : Blo 397767 599981 := bbase (se 3 (by rfl) ⟨112496, by rfl⟩ : syracuseStep 599981 = 224993) (by norm_num)
theorem B600005 : Blo 397767 600005 := bbase (se 4 (by rfl) ⟨56250, by rfl⟩ : syracuseStep 600005 = 112501) (by norm_num)
theorem B567253 : Blo 397767 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B600029 : Blo 397767 600029 := bbase (se 3 (by rfl) ⟨112505, by rfl⟩ : syracuseStep 600029 = 225011) (by norm_num)
theorem B600053 : Blo 397767 600053 := bbase (se 5 (by rfl) ⟨28127, by rfl⟩ : syracuseStep 600053 = 56255) (by norm_num)
theorem B600077 : Blo 397767 600077 := bbase (se 3 (by rfl) ⟨112514, by rfl⟩ : syracuseStep 600077 = 225029) (by norm_num)
theorem B895013 : Blo 397767 895013 := bbase (se 4 (by rfl) ⟨83907, by rfl⟩ : syracuseStep 895013 = 167815) (by norm_num)
theorem B600101 : Blo 397767 600101 := bbase (se 4 (by rfl) ⟨56259, by rfl⟩ : syracuseStep 600101 = 112519) (by norm_num)
theorem B600125 : Blo 397767 600125 := bbase (se 3 (by rfl) ⟨112523, by rfl⟩ : syracuseStep 600125 = 225047) (by norm_num)
theorem B600149 : Blo 397767 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B895085 : Blo 397767 895085 := bbase (se 3 (by rfl) ⟨167828, by rfl⟩ : syracuseStep 895085 = 335657) (by norm_num)
theorem B600173 : Blo 397767 600173 := bbase (se 3 (by rfl) ⟨112532, by rfl⟩ : syracuseStep 600173 = 225065) (by norm_num)
theorem B403585 : Blo 397767 403585 := bbase (se 2 (by rfl) ⟨151344, by rfl⟩ : syracuseStep 403585 = 302689) (by norm_num)
theorem B600197 : Blo 397767 600197 := bbase (se 4 (by rfl) ⟨56268, by rfl⟩ : syracuseStep 600197 = 112537) (by norm_num)
theorem B1517717 : Blo 397767 1517717 := bbase (se 6 (by rfl) ⟨35571, by rfl⟩ : syracuseStep 1517717 = 71143) (by norm_num)
theorem B600221 : Blo 397767 600221 := bbase (se 3 (by rfl) ⟨112541, by rfl⟩ : syracuseStep 600221 = 225083) (by norm_num)
theorem B895157 : Blo 397767 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B600245 : Blo 397767 600245 := bbase (se 5 (by rfl) ⟨28136, by rfl⟩ : syracuseStep 600245 = 56273) (by norm_num)
theorem B600269 : Blo 397767 600269 := bbase (se 3 (by rfl) ⟨112550, by rfl⟩ : syracuseStep 600269 = 225101) (by norm_num)
theorem B1353941 : Blo 397767 1353941 := bbase (se 7 (by rfl) ⟨15866, by rfl⟩ : syracuseStep 1353941 = 31733) (by norm_num)
theorem B600293 : Blo 397767 600293 := bbase (se 4 (by rfl) ⟨56277, by rfl⟩ : syracuseStep 600293 = 112555) (by norm_num)
theorem B2894069 : Blo 397767 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B895229 : Blo 397767 895229 := bbase (se 3 (by rfl) ⟨167855, by rfl⟩ : syracuseStep 895229 = 335711) (by norm_num)
theorem B600317 : Blo 397767 600317 := bbase (se 3 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 600317 = 225119) (by norm_num)
theorem B600341 : Blo 397767 600341 := bbase (se 6 (by rfl) ⟨14070, by rfl⟩ : syracuseStep 600341 = 28141) (by norm_num)
theorem B600365 : Blo 397767 600365 := bbase (se 3 (by rfl) ⟨112568, by rfl⟩ : syracuseStep 600365 = 225137) (by norm_num)
theorem B895301 : Blo 397767 895301 := bbase (se 4 (by rfl) ⟨83934, by rfl⟩ : syracuseStep 895301 = 167869) (by norm_num)
theorem B600389 : Blo 397767 600389 := bbase (se 4 (by rfl) ⟨56286, by rfl⟩ : syracuseStep 600389 = 112573) (by norm_num)
theorem B600413 : Blo 397767 600413 := bbase (se 3 (by rfl) ⟨112577, by rfl⟩ : syracuseStep 600413 = 225155) (by norm_num)
theorem B600437 : Blo 397767 600437 := bbase (se 5 (by rfl) ⟨28145, by rfl⟩ : syracuseStep 600437 = 56291) (by norm_num)
theorem B960893 : Blo 397767 960893 := bbase (se 3 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 960893 = 360335) (by norm_num)
theorem B895373 : Blo 397767 895373 := bbase (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) (by norm_num)
theorem B600461 : Blo 397767 600461 := bbase (se 3 (by rfl) ⟨112586, by rfl⟩ : syracuseStep 600461 = 225173) (by norm_num)
theorem B600485 : Blo 397767 600485 := bbase (se 4 (by rfl) ⟨56295, by rfl⟩ : syracuseStep 600485 = 112591) (by norm_num)
theorem B600509 : Blo 397767 600509 := bbase (se 3 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 600509 = 225191) (by norm_num)
theorem B567749 : Blo 397767 567749 := bbase (se 4 (by rfl) ⟨53226, by rfl⟩ : syracuseStep 567749 = 106453) (by norm_num)
theorem B895445 : Blo 397767 895445 := bbase (se 7 (by rfl) ⟨10493, by rfl⟩ : syracuseStep 895445 = 20987) (by norm_num)
theorem B600533 : Blo 397767 600533 := bbase (se 7 (by rfl) ⟨7037, by rfl⟩ : syracuseStep 600533 = 14075) (by norm_num)
theorem B600557 : Blo 397767 600557 := bbase (se 3 (by rfl) ⟨112604, by rfl⟩ : syracuseStep 600557 = 225209) (by norm_num)
theorem B600581 : Blo 397767 600581 := bbase (se 4 (by rfl) ⟨56304, by rfl⟩ : syracuseStep 600581 = 112609) (by norm_num)
theorem B895517 : Blo 397767 895517 := bbase (se 3 (by rfl) ⟨167909, by rfl⟩ : syracuseStep 895517 = 335819) (by norm_num)
theorem B600605 : Blo 397767 600605 := bbase (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) (by norm_num)
theorem B600629 : Blo 397767 600629 := bbase (se 5 (by rfl) ⟨28154, by rfl⟩ : syracuseStep 600629 = 56309) (by norm_num)
theorem B600653 : Blo 397767 600653 := bbase (se 3 (by rfl) ⟨112622, by rfl⟩ : syracuseStep 600653 = 225245) (by norm_num)
theorem B895589 : Blo 397767 895589 := bbase (se 4 (by rfl) ⟨83961, by rfl⟩ : syracuseStep 895589 = 167923) (by norm_num)
theorem B1092197 : Blo 397767 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B600677 : Blo 397767 600677 := bbase (se 4 (by rfl) ⟨56313, by rfl⟩ : syracuseStep 600677 = 112627) (by norm_num)
theorem B600701 : Blo 397767 600701 := bbase (se 3 (by rfl) ⟨112631, by rfl⟩ : syracuseStep 600701 = 225263) (by norm_num)
theorem B1354373 : Blo 397767 1354373 := bbase (se 4 (by rfl) ⟨126972, by rfl⟩ : syracuseStep 1354373 = 253945) (by norm_num)
theorem B600725 : Blo 397767 600725 := bbase (se 6 (by rfl) ⟨14079, by rfl⟩ : syracuseStep 600725 = 28159) (by norm_num)
theorem B895661 : Blo 397767 895661 := bbase (se 3 (by rfl) ⟨167936, by rfl⟩ : syracuseStep 895661 = 335873) (by norm_num)
theorem B600749 : Blo 397767 600749 := bbase (se 3 (by rfl) ⟨112640, by rfl⟩ : syracuseStep 600749 = 225281) (by norm_num)
theorem B600773 : Blo 397767 600773 := bbase (se 4 (by rfl) ⟨56322, by rfl⟩ : syracuseStep 600773 = 112645) (by norm_num)
theorem B600797 : Blo 397767 600797 := bbase (se 3 (by rfl) ⟨112649, by rfl⟩ : syracuseStep 600797 = 225299) (by norm_num)
theorem B895733 : Blo 397767 895733 := bbase (se 5 (by rfl) ⟨41987, by rfl⟩ : syracuseStep 895733 = 83975) (by norm_num)
theorem B600821 : Blo 397767 600821 := bbase (se 5 (by rfl) ⟨28163, by rfl⟩ : syracuseStep 600821 = 56327) (by norm_num)
theorem B600845 : Blo 397767 600845 := bbase (se 3 (by rfl) ⟨112658, by rfl⟩ : syracuseStep 600845 = 225317) (by norm_num)
theorem B600869 : Blo 397767 600869 := bbase (se 4 (by rfl) ⟨56331, by rfl⟩ : syracuseStep 600869 = 112663) (by norm_num)
theorem B895805 : Blo 397767 895805 := bbase (se 3 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 895805 = 335927) (by norm_num)
theorem B600893 : Blo 397767 600893 := bbase (se 3 (by rfl) ⟨112667, by rfl⟩ : syracuseStep 600893 = 225335) (by norm_num)
theorem B600917 : Blo 397767 600917 := bbase (se 9 (by rfl) ⟨1760, by rfl⟩ : syracuseStep 600917 = 3521) (by norm_num)
theorem B600941 : Blo 397767 600941 := bbase (se 3 (by rfl) ⟨112676, by rfl⟩ : syracuseStep 600941 = 225353) (by norm_num)
theorem B895877 : Blo 397767 895877 := bbase (se 4 (by rfl) ⟨83988, by rfl⟩ : syracuseStep 895877 = 167977) (by norm_num)
theorem B600965 : Blo 397767 600965 := bbase (se 4 (by rfl) ⟨56340, by rfl⟩ : syracuseStep 600965 = 112681) (by norm_num)
theorem B600989 : Blo 397767 600989 := bbase (se 3 (by rfl) ⟨112685, by rfl⟩ : syracuseStep 600989 = 225371) (by norm_num)
theorem B601013 : Blo 397767 601013 := bbase (se 5 (by rfl) ⟨28172, by rfl⟩ : syracuseStep 601013 = 56345) (by norm_num)
theorem B895949 : Blo 397767 895949 := bbase (se 3 (by rfl) ⟨167990, by rfl⟩ : syracuseStep 895949 = 335981) (by norm_num)
theorem B601037 : Blo 397767 601037 := bbase (se 3 (by rfl) ⟨112694, by rfl⟩ : syracuseStep 601037 = 225389) (by norm_num)
theorem B601061 : Blo 397767 601061 := bbase (se 4 (by rfl) ⟨56349, by rfl⟩ : syracuseStep 601061 = 112699) (by norm_num)
theorem B568301 : Blo 397767 568301 := bbase (se 3 (by rfl) ⟨106556, by rfl⟩ : syracuseStep 568301 = 213113) (by norm_num)
theorem B601085 : Blo 397767 601085 := bbase (se 3 (by rfl) ⟨112703, by rfl⟩ : syracuseStep 601085 = 225407) (by norm_num)
theorem B896021 : Blo 397767 896021 := bbase (se 6 (by rfl) ⟨21000, by rfl⟩ : syracuseStep 896021 = 42001) (by norm_num)
theorem B601109 : Blo 397767 601109 := bbase (se 6 (by rfl) ⟨14088, by rfl⟩ : syracuseStep 601109 = 28177) (by norm_num)
theorem B601133 : Blo 397767 601133 := bbase (se 3 (by rfl) ⟨112712, by rfl⟩ : syracuseStep 601133 = 225425) (by norm_num)
theorem B1354805 : Blo 397767 1354805 := bbase (se 5 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 1354805 = 127013) (by norm_num)
theorem B601157 : Blo 397767 601157 := bbase (se 4 (by rfl) ⟨56358, by rfl⟩ : syracuseStep 601157 = 112717) (by norm_num)
theorem B896093 : Blo 397767 896093 := bbase (se 3 (by rfl) ⟨168017, by rfl⟩ : syracuseStep 896093 = 336035) (by norm_num)
theorem B601181 : Blo 397767 601181 := bbase (se 3 (by rfl) ⟨112721, by rfl⟩ : syracuseStep 601181 = 225443) (by norm_num)
theorem B601205 : Blo 397767 601205 := bbase (se 5 (by rfl) ⟨28181, by rfl⟩ : syracuseStep 601205 = 56363) (by norm_num)
theorem B601229 : Blo 397767 601229 := bbase (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) (by norm_num)
theorem B896165 : Blo 397767 896165 := bbase (se 4 (by rfl) ⟨84015, by rfl⟩ : syracuseStep 896165 = 168031) (by norm_num)
theorem B601253 : Blo 397767 601253 := bbase (se 4 (by rfl) ⟨56367, by rfl⟩ : syracuseStep 601253 = 112735) (by norm_num)
theorem B601277 : Blo 397767 601277 := bbase (se 3 (by rfl) ⟨112739, by rfl⟩ : syracuseStep 601277 = 225479) (by norm_num)
theorem B601301 : Blo 397767 601301 := bbase (se 7 (by rfl) ⟨7046, by rfl⟩ : syracuseStep 601301 = 14093) (by norm_num)
theorem B896237 : Blo 397767 896237 := bbase (se 3 (by rfl) ⟨168044, by rfl⟩ : syracuseStep 896237 = 336089) (by norm_num)
theorem B601325 : Blo 397767 601325 := bbase (se 3 (by rfl) ⟨112748, by rfl⟩ : syracuseStep 601325 = 225497) (by norm_num)
theorem B601349 : Blo 397767 601349 := bbase (se 4 (by rfl) ⟨56376, by rfl⟩ : syracuseStep 601349 = 112753) (by norm_num)
theorem B601373 : Blo 397767 601373 := bbase (se 3 (by rfl) ⟨112757, by rfl⟩ : syracuseStep 601373 = 225515) (by norm_num)
theorem B896309 : Blo 397767 896309 := bbase (se 5 (by rfl) ⟨42014, by rfl⟩ : syracuseStep 896309 = 84029) (by norm_num)
theorem B601397 : Blo 397767 601397 := bbase (se 5 (by rfl) ⟨28190, by rfl⟩ : syracuseStep 601397 = 56381) (by norm_num)
theorem B961853 : Blo 397767 961853 := bbase (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) (by norm_num)
theorem B601421 : Blo 397767 601421 := bbase (se 3 (by rfl) ⟨112766, by rfl⟩ : syracuseStep 601421 = 225533) (by norm_num)
theorem B601445 : Blo 397767 601445 := bbase (se 4 (by rfl) ⟨56385, by rfl⟩ : syracuseStep 601445 = 112771) (by norm_num)
theorem B896381 : Blo 397767 896381 := bbase (se 3 (by rfl) ⟨168071, by rfl⟩ : syracuseStep 896381 = 336143) (by norm_num)
theorem B601469 : Blo 397767 601469 := bbase (se 3 (by rfl) ⟨112775, by rfl⟩ : syracuseStep 601469 = 225551) (by norm_num)
theorem B601493 : Blo 397767 601493 := bbase (se 6 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 601493 = 28195) (by norm_num)
theorem B601517 : Blo 397767 601517 := bbase (se 3 (by rfl) ⟨112784, by rfl⟩ : syracuseStep 601517 = 225569) (by norm_num)
theorem B896453 : Blo 397767 896453 := bbase (se 4 (by rfl) ⟨84042, by rfl⟩ : syracuseStep 896453 = 168085) (by norm_num)
theorem B601541 : Blo 397767 601541 := bbase (se 4 (by rfl) ⟨56394, by rfl⟩ : syracuseStep 601541 = 112789) (by norm_num)
theorem B601565 : Blo 397767 601565 := bbase (se 3 (by rfl) ⟨112793, by rfl⟩ : syracuseStep 601565 = 225587) (by norm_num)
theorem B1355237 : Blo 397767 1355237 := bbase (se 4 (by rfl) ⟨127053, by rfl⟩ : syracuseStep 1355237 = 254107) (by norm_num)
theorem B601589 : Blo 397767 601589 := bbase (se 5 (by rfl) ⟨28199, by rfl⟩ : syracuseStep 601589 = 56399) (by norm_num)
theorem B896525 : Blo 397767 896525 := bbase (se 3 (by rfl) ⟨168098, by rfl⟩ : syracuseStep 896525 = 336197) (by norm_num)
theorem B601613 : Blo 397767 601613 := bbase (se 3 (by rfl) ⟨112802, by rfl⟩ : syracuseStep 601613 = 225605) (by norm_num)
theorem B601637 : Blo 397767 601637 := bbase (se 4 (by rfl) ⟨56403, by rfl⟩ : syracuseStep 601637 = 112807) (by norm_num)
theorem B405037 : Blo 397767 405037 := bbase (se 3 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 405037 = 151889) (by norm_num)
theorem B601661 : Blo 397767 601661 := bbase (se 3 (by rfl) ⟨112811, by rfl⟩ : syracuseStep 601661 = 225623) (by norm_num)
theorem B405065 : Blo 397767 405065 := bbase (se 2 (by rfl) ⟨151899, by rfl⟩ : syracuseStep 405065 = 303799) (by norm_num)
theorem B896597 : Blo 397767 896597 := bbase (se 8 (by rfl) ⟨5253, by rfl⟩ : syracuseStep 896597 = 10507) (by norm_num)
theorem B831061 : Blo 397767 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B10923605 : Blo 397767 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B601685 : Blo 397767 601685 := bbase (se 8 (by rfl) ⟨3525, by rfl⟩ : syracuseStep 601685 = 7051) (by norm_num)
theorem B601709 : Blo 397767 601709 := bbase (se 3 (by rfl) ⟨112820, by rfl⟩ : syracuseStep 601709 = 225641) (by norm_num)
theorem B503425 : Blo 397767 503425 := bbase (se 2 (by rfl) ⟨188784, by rfl⟩ : syracuseStep 503425 = 377569) (by norm_num)
theorem B601733 : Blo 397767 601733 := bbase (se 4 (by rfl) ⟨56412, by rfl⟩ : syracuseStep 601733 = 112825) (by norm_num)
theorem B896669 : Blo 397767 896669 := bbase (se 3 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 896669 = 336251) (by norm_num)
theorem B601757 : Blo 397767 601757 := bbase (se 3 (by rfl) ⟨112829, by rfl⟩ : syracuseStep 601757 = 225659) (by norm_num)
theorem B601781 : Blo 397767 601781 := bbase (se 5 (by rfl) ⟨28208, by rfl⟩ : syracuseStep 601781 = 56417) (by norm_num)
theorem B601805 : Blo 397767 601805 := bbase (se 3 (by rfl) ⟨112838, by rfl⟩ : syracuseStep 601805 = 225677) (by norm_num)
theorem B569053 : Blo 397767 569053 := bbase (se 3 (by rfl) ⟨106697, by rfl⟩ : syracuseStep 569053 = 213395) (by norm_num)
theorem B896741 : Blo 397767 896741 := bbase (se 4 (by rfl) ⟨84069, by rfl⟩ : syracuseStep 896741 = 168139) (by norm_num)
theorem B601829 : Blo 397767 601829 := bbase (se 4 (by rfl) ⟨56421, by rfl⟩ : syracuseStep 601829 = 112843) (by norm_num)
theorem B601853 : Blo 397767 601853 := bbase (se 3 (by rfl) ⟨112847, by rfl⟩ : syracuseStep 601853 = 225695) (by norm_num)
theorem B601877 : Blo 397767 601877 := bbase (se 6 (by rfl) ⟨14106, by rfl⟩ : syracuseStep 601877 = 28213) (by norm_num)
theorem B503597 : Blo 397767 503597 := bbase (se 3 (by rfl) ⟨94424, by rfl⟩ : syracuseStep 503597 = 188849) (by norm_num)
theorem B896813 : Blo 397767 896813 := bbase (se 3 (by rfl) ⟨168152, by rfl⟩ : syracuseStep 896813 = 336305) (by norm_num)
theorem B601901 : Blo 397767 601901 := bbase (se 3 (by rfl) ⟨112856, by rfl⟩ : syracuseStep 601901 = 225713) (by norm_num)
theorem B601925 : Blo 397767 601925 := bbase (se 4 (by rfl) ⟨56430, by rfl⟩ : syracuseStep 601925 = 112861) (by norm_num)
theorem B601949 : Blo 397767 601949 := bbase (se 3 (by rfl) ⟨112865, by rfl⟩ : syracuseStep 601949 = 225731) (by norm_num)
theorem B503653 : Blo 397767 503653 := bbase (se 4 (by rfl) ⟨47217, by rfl⟩ : syracuseStep 503653 = 94435) (by norm_num)
theorem B896885 : Blo 397767 896885 := bbase (se 5 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 896885 = 84083) (by norm_num)
theorem B1027957 : Blo 397767 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B601973 : Blo 397767 601973 := bbase (se 5 (by rfl) ⟨28217, by rfl⟩ : syracuseStep 601973 = 56435) (by norm_num)
theorem B601997 : Blo 397767 601997 := bbase (se 3 (by rfl) ⟨112874, by rfl⟩ : syracuseStep 601997 = 225749) (by norm_num)
theorem B1355669 : Blo 397767 1355669 := bbase (se 6 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 1355669 = 63547) (by norm_num)
theorem B602021 : Blo 397767 602021 := bbase (se 4 (by rfl) ⟨56439, by rfl⟩ : syracuseStep 602021 = 112879) (by norm_num)
theorem B896957 : Blo 397767 896957 := bbase (se 3 (by rfl) ⟨168179, by rfl⟩ : syracuseStep 896957 = 336359) (by norm_num)
theorem B602045 : Blo 397767 602045 := bbase (se 3 (by rfl) ⟨112883, by rfl⟩ : syracuseStep 602045 = 225767) (by norm_num)
theorem B503749 : Blo 397767 503749 := bbase (se 4 (by rfl) ⟨47226, by rfl⟩ : syracuseStep 503749 = 94453) (by norm_num)
theorem B602069 : Blo 397767 602069 := bbase (se 7 (by rfl) ⟨7055, by rfl⟩ : syracuseStep 602069 = 14111) (by norm_num)
theorem B602093 : Blo 397767 602093 := bbase (se 3 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 602093 = 225785) (by norm_num)
theorem B897029 : Blo 397767 897029 := bbase (se 4 (by rfl) ⟨84096, by rfl⟩ : syracuseStep 897029 = 168193) (by norm_num)
theorem B602117 : Blo 397767 602117 := bbase (se 4 (by rfl) ⟨56448, by rfl⟩ : syracuseStep 602117 = 112897) (by norm_num)
theorem B602141 : Blo 397767 602141 := bbase (se 3 (by rfl) ⟨112901, by rfl⟩ : syracuseStep 602141 = 225803) (by norm_num)
theorem B602165 : Blo 397767 602165 := bbase (se 5 (by rfl) ⟨28226, by rfl⟩ : syracuseStep 602165 = 56453) (by norm_num)
theorem B897101 : Blo 397767 897101 := bbase (se 3 (by rfl) ⟨168206, by rfl⟩ : syracuseStep 897101 = 336413) (by norm_num)
theorem B602189 : Blo 397767 602189 := bbase (se 3 (by rfl) ⟨112910, by rfl⟩ : syracuseStep 602189 = 225821) (by norm_num)
theorem B602213 : Blo 397767 602213 := bbase (se 4 (by rfl) ⟨56457, by rfl⟩ : syracuseStep 602213 = 112915) (by norm_num)
theorem B503921 : Blo 397767 503921 := bbase (se 2 (by rfl) ⟨188970, by rfl⟩ : syracuseStep 503921 = 377941) (by norm_num)
theorem B602237 : Blo 397767 602237 := bbase (se 3 (by rfl) ⟨112919, by rfl⟩ : syracuseStep 602237 = 225839) (by norm_num)
theorem B897173 : Blo 397767 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B602261 : Blo 397767 602261 := bbase (se 6 (by rfl) ⟨14115, by rfl⟩ : syracuseStep 602261 = 28231) (by norm_num)
theorem B503977 : Blo 397767 503977 := bbase (se 2 (by rfl) ⟨188991, by rfl⟩ : syracuseStep 503977 = 377983) (by norm_num)
theorem B602285 : Blo 397767 602285 := bbase (se 3 (by rfl) ⟨112928, by rfl⟩ : syracuseStep 602285 = 225857) (by norm_num)
theorem B602309 : Blo 397767 602309 := bbase (se 4 (by rfl) ⟨56466, by rfl⟩ : syracuseStep 602309 = 112933) (by norm_num)
theorem B1519829 : Blo 397767 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B897245 : Blo 397767 897245 := bbase (se 3 (by rfl) ⟨168233, by rfl⟩ : syracuseStep 897245 = 336467) (by norm_num)
theorem B602333 : Blo 397767 602333 := bbase (se 3 (by rfl) ⟨112937, by rfl⟩ : syracuseStep 602333 = 225875) (by norm_num)
theorem B602357 : Blo 397767 602357 := bbase (se 5 (by rfl) ⟨28235, by rfl⟩ : syracuseStep 602357 = 56471) (by norm_num)
theorem B504073 : Blo 397767 504073 := bbase (se 2 (by rfl) ⟨189027, by rfl⟩ : syracuseStep 504073 = 378055) (by norm_num)
theorem B602381 : Blo 397767 602381 := bbase (se 3 (by rfl) ⟨112946, by rfl⟩ : syracuseStep 602381 = 225893) (by norm_num)
theorem B897317 : Blo 397767 897317 := bbase (se 4 (by rfl) ⟨84123, by rfl⟩ : syracuseStep 897317 = 168247) (by norm_num)
theorem B602405 : Blo 397767 602405 := bbase (se 4 (by rfl) ⟨56475, by rfl⟩ : syracuseStep 602405 = 112951) (by norm_num)
theorem B602429 : Blo 397767 602429 := bbase (se 3 (by rfl) ⟨112955, by rfl⟩ : syracuseStep 602429 = 225911) (by norm_num)
theorem B602453 : Blo 397767 602453 := bbase (se 10 (by rfl) ⟨882, by rfl⟩ : syracuseStep 602453 = 1765) (by norm_num)
theorem B897389 : Blo 397767 897389 := bbase (se 3 (by rfl) ⟨168260, by rfl⟩ : syracuseStep 897389 = 336521) (by norm_num)
theorem B602477 : Blo 397767 602477 := bbase (se 3 (by rfl) ⟨112964, by rfl⟩ : syracuseStep 602477 = 225929) (by norm_num)
theorem B602501 : Blo 397767 602501 := bbase (se 4 (by rfl) ⟨56484, by rfl⟩ : syracuseStep 602501 = 112969) (by norm_num)
theorem B602525 : Blo 397767 602525 := bbase (se 3 (by rfl) ⟨112973, by rfl⟩ : syracuseStep 602525 = 225947) (by norm_num)
theorem B504245 : Blo 397767 504245 := bbase (se 5 (by rfl) ⟨23636, by rfl⟩ : syracuseStep 504245 = 47273) (by norm_num)
theorem B897461 : Blo 397767 897461 := bbase (se 5 (by rfl) ⟨42068, by rfl⟩ : syracuseStep 897461 = 84137) (by norm_num)
theorem B602549 : Blo 397767 602549 := bbase (se 5 (by rfl) ⟨28244, by rfl⟩ : syracuseStep 602549 = 56489) (by norm_num)
theorem B602573 : Blo 397767 602573 := bbase (se 3 (by rfl) ⟨112982, by rfl⟩ : syracuseStep 602573 = 225965) (by norm_num)
theorem B602597 : Blo 397767 602597 := bbase (se 4 (by rfl) ⟨56493, by rfl⟩ : syracuseStep 602597 = 112987) (by norm_num)
theorem B504301 : Blo 397767 504301 := bbase (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) (by norm_num)
theorem B569845 : Blo 397767 569845 := bbase (se 5 (by rfl) ⟨26711, by rfl⟩ : syracuseStep 569845 = 53423) (by norm_num)
theorem B1520117 : Blo 397767 1520117 := bbase (se 5 (by rfl) ⟨71255, by rfl⟩ : syracuseStep 1520117 = 142511) (by norm_num)
theorem B406009 : Blo 397767 406009 := bbase (se 2 (by rfl) ⟨152253, by rfl⟩ : syracuseStep 406009 = 304507) (by norm_num)
theorem B897533 : Blo 397767 897533 := bbase (se 3 (by rfl) ⟨168287, by rfl⟩ : syracuseStep 897533 = 336575) (by norm_num)
theorem B602621 : Blo 397767 602621 := bbase (se 3 (by rfl) ⟨112991, by rfl⟩ : syracuseStep 602621 = 225983) (by norm_num)
theorem B3650069 : Blo 397767 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B602645 : Blo 397767 602645 := bbase (se 6 (by rfl) ⟨14124, by rfl⟩ : syracuseStep 602645 = 28249) (by norm_num)
theorem B897605 : Blo 397767 897605 := bbase (se 4 (by rfl) ⟨84150, by rfl⟩ : syracuseStep 897605 = 168301) (by norm_num)
theorem B504397 : Blo 397767 504397 := bbase (se 3 (by rfl) ⟨94574, by rfl⟩ : syracuseStep 504397 = 189149) (by norm_num)
theorem B766597 : Blo 397767 766597 := bbase (se 4 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 766597 = 143737) (by norm_num)
theorem B897677 : Blo 397767 897677 := bbase (se 3 (by rfl) ⟨168314, by rfl⟩ : syracuseStep 897677 = 336629) (by norm_num)
theorem B1913557 : Blo 397767 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B897749 : Blo 397767 897749 := bbase (se 7 (by rfl) ⟨10520, by rfl⟩ : syracuseStep 897749 = 21041) (by norm_num)
theorem B504569 : Blo 397767 504569 := bbase (se 2 (by rfl) ⟨189213, by rfl⟩ : syracuseStep 504569 = 378427) (by norm_num)
theorem B897821 : Blo 397767 897821 := bbase (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) (by norm_num)
theorem B504625 : Blo 397767 504625 := bbase (se 2 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 504625 = 378469) (by norm_num)
theorem B1815365 : Blo 397767 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B570181 : Blo 397767 570181 := bbase (se 4 (by rfl) ⟨53454, by rfl⟩ : syracuseStep 570181 = 106909) (by norm_num)
theorem B897893 : Blo 397767 897893 := bbase (se 4 (by rfl) ⟨84177, by rfl⟩ : syracuseStep 897893 = 168355) (by norm_num)
theorem B504721 : Blo 397767 504721 := bbase (se 2 (by rfl) ⟨189270, by rfl⟩ : syracuseStep 504721 = 378541) (by norm_num)
theorem B897965 : Blo 397767 897965 := bbase (se 3 (by rfl) ⟨168368, by rfl⟩ : syracuseStep 897965 = 336737) (by norm_num)
theorem B898037 : Blo 397767 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B570397 : Blo 397767 570397 := bbase (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) (by norm_num)
theorem B963613 : Blo 397767 963613 := bbase (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) (by norm_num)
theorem B504893 : Blo 397767 504893 := bbase (se 3 (by rfl) ⟨94667, by rfl⟩ : syracuseStep 504893 = 189335) (by norm_num)
theorem B898109 : Blo 397767 898109 := bbase (se 3 (by rfl) ⟨168395, by rfl⟩ : syracuseStep 898109 = 336791) (by norm_num)
theorem B2274389 : Blo 397767 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B504949 : Blo 397767 504949 := bbase (se 5 (by rfl) ⟨23669, by rfl⟩ : syracuseStep 504949 = 47339) (by norm_num)
theorem B898181 : Blo 397767 898181 := bbase (se 4 (by rfl) ⟨84204, by rfl⟩ : syracuseStep 898181 = 168409) (by norm_num)
theorem B898253 : Blo 397767 898253 := bbase (se 3 (by rfl) ⟨168422, by rfl⟩ : syracuseStep 898253 = 336845) (by norm_num)
theorem B505045 : Blo 397767 505045 := bbase (se 7 (by rfl) ⟨5918, by rfl⟩ : syracuseStep 505045 = 11837) (by norm_num)
theorem B963845 : Blo 397767 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B898325 : Blo 397767 898325 := bbase (se 6 (by rfl) ⟨21054, by rfl⟩ : syracuseStep 898325 = 42109) (by norm_num)
theorem B1029437 : Blo 397767 1029437 := bbase (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) (by norm_num)
theorem B898397 : Blo 397767 898397 := bbase (se 3 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 898397 = 336899) (by norm_num)
theorem B505217 : Blo 397767 505217 := bbase (se 2 (by rfl) ⟨189456, by rfl⟩ : syracuseStep 505217 = 378913) (by norm_num)
theorem B570773 : Blo 397767 570773 := bbase (se 6 (by rfl) ⟨13377, by rfl⟩ : syracuseStep 570773 = 26755) (by norm_num)
theorem B898469 : Blo 397767 898469 := bbase (se 4 (by rfl) ⟨84231, by rfl⟩ : syracuseStep 898469 = 168463) (by norm_num)
theorem B505273 : Blo 397767 505273 := bbase (se 2 (by rfl) ⟨189477, by rfl⟩ : syracuseStep 505273 = 378955) (by norm_num)
theorem B898541 : Blo 397767 898541 := bbase (se 3 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 898541 = 336953) (by norm_num)
theorem B505369 : Blo 397767 505369 := bbase (se 2 (by rfl) ⟨189513, by rfl⟩ : syracuseStep 505369 = 379027) (by norm_num)
theorem B898613 : Blo 397767 898613 := bbase (se 5 (by rfl) ⟨42122, by rfl⟩ : syracuseStep 898613 = 84245) (by norm_num)
theorem B898685 : Blo 397767 898685 := bbase (se 3 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 898685 = 337007) (by norm_num)
theorem B964237 : Blo 397767 964237 := bbase (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) (by norm_num)
theorem B5125781 : Blo 397767 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B1521301 : Blo 397767 1521301 := bbase (se 6 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 1521301 = 71311) (by norm_num)
theorem B505541 : Blo 397767 505541 := bbase (se 4 (by rfl) ⟨47394, by rfl⟩ : syracuseStep 505541 = 94789) (by norm_num)
theorem B898757 : Blo 397767 898757 := bbase (se 4 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 898757 = 168517) (by norm_num)
theorem B505597 : Blo 397767 505597 := bbase (se 3 (by rfl) ⟨94799, by rfl⟩ : syracuseStep 505597 = 189599) (by norm_num)
theorem B898829 : Blo 397767 898829 := bbase (se 3 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 898829 = 337061) (by norm_num)
theorem B898901 : Blo 397767 898901 := bbase (se 9 (by rfl) ⟨2633, by rfl⟩ : syracuseStep 898901 = 5267) (by norm_num)
theorem B505693 : Blo 397767 505693 := bbase (se 3 (by rfl) ⟨94817, by rfl⟩ : syracuseStep 505693 = 189635) (by norm_num)
theorem B898973 : Blo 397767 898973 := bbase (se 3 (by rfl) ⟨168557, by rfl⟩ : syracuseStep 898973 = 337115) (by norm_num)
theorem B1521605 : Blo 397767 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B6862805 : Blo 397767 6862805 := bbase (se 7 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 6862805 = 160847) (by norm_num)
theorem B538589 : Blo 397767 538589 := bbase (se 3 (by rfl) ⟨100985, by rfl⟩ : syracuseStep 538589 = 201971) (by norm_num)
theorem B899045 : Blo 397767 899045 := bbase (se 4 (by rfl) ⟨84285, by rfl⟩ : syracuseStep 899045 = 168571) (by norm_num)
theorem B505865 : Blo 397767 505865 := bbase (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) (by norm_num)
theorem B899117 : Blo 397767 899117 := bbase (se 3 (by rfl) ⟨168584, by rfl⟩ : syracuseStep 899117 = 337169) (by norm_num)
theorem B505921 : Blo 397767 505921 := bbase (se 2 (by rfl) ⟨189720, by rfl⟩ : syracuseStep 505921 = 379441) (by norm_num)
theorem B899189 : Blo 397767 899189 := bbase (se 5 (by rfl) ⟨42149, by rfl⟩ : syracuseStep 899189 = 84299) (by norm_num)
theorem B506017 : Blo 397767 506017 := bbase (se 2 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 506017 = 379513) (by norm_num)
theorem B899261 : Blo 397767 899261 := bbase (se 3 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 899261 = 337223) (by norm_num)
theorem B3029237 : Blo 397767 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B2275573 : Blo 397767 2275573 := bbase (se 5 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 2275573 = 213335) (by norm_num)
theorem B899333 : Blo 397767 899333 := bbase (se 4 (by rfl) ⟨84312, by rfl⟩ : syracuseStep 899333 = 168625) (by norm_num)
theorem B899405 : Blo 397767 899405 := bbase (se 3 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 899405 = 337277) (by norm_num)
theorem B506189 : Blo 397767 506189 := bbase (se 3 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 506189 = 189821) (by norm_num)
theorem B506245 : Blo 397767 506245 := bbase (se 4 (by rfl) ⟨47460, by rfl⟩ : syracuseStep 506245 = 94921) (by norm_num)
theorem B1980805 : Blo 397767 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B899477 : Blo 397767 899477 := bbase (se 6 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 899477 = 42163) (by norm_num)
theorem B899549 : Blo 397767 899549 := bbase (se 3 (by rfl) ⟨168665, by rfl⟩ : syracuseStep 899549 = 337331) (by norm_num)
theorem B506341 : Blo 397767 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B899621 : Blo 397767 899621 := bbase (se 4 (by rfl) ⟨84339, by rfl⟩ : syracuseStep 899621 = 168679) (by norm_num)
theorem B1620533 : Blo 397767 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B899693 : Blo 397767 899693 := bbase (se 3 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 899693 = 337385) (by norm_num)
theorem B1096325 : Blo 397767 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B506513 : Blo 397767 506513 := bbase (se 2 (by rfl) ⟨189942, by rfl⟩ : syracuseStep 506513 = 379885) (by norm_num)
theorem B899765 : Blo 397767 899765 := bbase (se 5 (by rfl) ⟨42176, by rfl⟩ : syracuseStep 899765 = 84353) (by norm_num)
theorem B506569 : Blo 397767 506569 := bbase (se 2 (by rfl) ⟨189963, by rfl⟩ : syracuseStep 506569 = 379927) (by norm_num)
theorem B965333 : Blo 397767 965333 := bbase (se 7 (by rfl) ⟨11312, by rfl⟩ : syracuseStep 965333 = 22625) (by norm_num)
theorem B899837 : Blo 397767 899837 := bbase (se 3 (by rfl) ⟨168719, by rfl⟩ : syracuseStep 899837 = 337439) (by norm_num)
theorem B506665 : Blo 397767 506665 := bbase (se 2 (by rfl) ⟨189999, by rfl⟩ : syracuseStep 506665 = 379999) (by norm_num)
theorem B867125 : Blo 397767 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B899909 : Blo 397767 899909 := bbase (se 4 (by rfl) ⟨84366, by rfl⟩ : syracuseStep 899909 = 168733) (by norm_num)
theorem B899981 : Blo 397767 899981 := bbase (se 3 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 899981 = 337493) (by norm_num)
theorem B900053 : Blo 397767 900053 := bbase (se 7 (by rfl) ⟨10547, by rfl⟩ : syracuseStep 900053 = 21095) (by norm_num)
theorem B506837 : Blo 397767 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B506893 : Blo 397767 506893 := bbase (se 3 (by rfl) ⟨95042, by rfl⟩ : syracuseStep 506893 = 190085) (by norm_num)
theorem B900125 : Blo 397767 900125 := bbase (se 3 (by rfl) ⟨168773, by rfl⟩ : syracuseStep 900125 = 337547) (by norm_num)
theorem B539741 : Blo 397767 539741 := bbase (se 3 (by rfl) ⟨101201, by rfl⟩ : syracuseStep 539741 = 202403) (by norm_num)
theorem B900197 : Blo 397767 900197 := bbase (se 4 (by rfl) ⟨84393, by rfl⟩ : syracuseStep 900197 = 168787) (by norm_num)
theorem B506989 : Blo 397767 506989 := bbase (se 3 (by rfl) ⟨95060, by rfl⟩ : syracuseStep 506989 = 190121) (by norm_num)
theorem B900269 : Blo 397767 900269 := bbase (se 3 (by rfl) ⟨168800, by rfl⟩ : syracuseStep 900269 = 337601) (by norm_num)
theorem B900341 : Blo 397767 900341 := bbase (se 5 (by rfl) ⟨42203, by rfl⟩ : syracuseStep 900341 = 84407) (by norm_num)
theorem B2014469 : Blo 397767 2014469 := bbase (se 4 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 2014469 = 377713) (by norm_num)
theorem B507161 : Blo 397767 507161 := bbase (se 2 (by rfl) ⟨190185, by rfl⟩ : syracuseStep 507161 = 380371) (by norm_num)
theorem B638237 : Blo 397767 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B900413 : Blo 397767 900413 := bbase (se 3 (by rfl) ⟨168827, by rfl⟩ : syracuseStep 900413 = 337655) (by norm_num)
theorem B507217 : Blo 397767 507217 := bbase (se 2 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 507217 = 380413) (by norm_num)
theorem B900485 : Blo 397767 900485 := bbase (se 4 (by rfl) ⟨84420, by rfl⟩ : syracuseStep 900485 = 168841) (by norm_num)
theorem B638365 : Blo 397767 638365 := bbase (se 3 (by rfl) ⟨119693, by rfl⟩ : syracuseStep 638365 = 239387) (by norm_num)
theorem B507313 : Blo 397767 507313 := bbase (se 2 (by rfl) ⟨190242, by rfl⟩ : syracuseStep 507313 = 380485) (by norm_num)
theorem B900557 : Blo 397767 900557 := bbase (se 3 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 900557 = 337709) (by norm_num)
theorem B1916405 : Blo 397767 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B900629 : Blo 397767 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B900701 : Blo 397767 900701 := bbase (se 3 (by rfl) ⟨168881, by rfl⟩ : syracuseStep 900701 = 337763) (by norm_num)
theorem B507485 : Blo 397767 507485 := bbase (se 3 (by rfl) ⟨95153, by rfl⟩ : syracuseStep 507485 = 190307) (by norm_num)
theorem B671341 : Blo 397767 671341 := bbase (se 3 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 671341 = 251753) (by norm_num)
theorem B507541 : Blo 397767 507541 := bbase (se 6 (by rfl) ⟨11895, by rfl⟩ : syracuseStep 507541 = 23791) (by norm_num)
theorem B900773 : Blo 397767 900773 := bbase (se 4 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 900773 = 168895) (by norm_num)
theorem B671429 : Blo 397767 671429 := bbase (se 4 (by rfl) ⟨62946, by rfl⟩ : syracuseStep 671429 = 125893) (by norm_num)
theorem B900845 : Blo 397767 900845 := bbase (se 3 (by rfl) ⟨168908, by rfl⟩ : syracuseStep 900845 = 337817) (by norm_num)
theorem B507637 : Blo 397767 507637 := bbase (se 5 (by rfl) ⟨23795, by rfl⟩ : syracuseStep 507637 = 47591) (by norm_num)
theorem B900917 : Blo 397767 900917 := bbase (se 5 (by rfl) ⟨42230, by rfl⟩ : syracuseStep 900917 = 84461) (by norm_num)
theorem B671557 : Blo 397767 671557 := bbase (se 4 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 671557 = 125917) (by norm_num)
theorem B900989 : Blo 397767 900989 := bbase (se 3 (by rfl) ⟨168935, by rfl⟩ : syracuseStep 900989 = 337871) (by norm_num)
theorem B671645 : Blo 397767 671645 := bbase (se 3 (by rfl) ⟨125933, by rfl⟩ : syracuseStep 671645 = 251867) (by norm_num)
theorem B507809 : Blo 397767 507809 := bbase (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) (by norm_num)
theorem B540589 : Blo 397767 540589 := bbase (se 3 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 540589 = 202721) (by norm_num)
theorem B901061 : Blo 397767 901061 := bbase (se 4 (by rfl) ⟨84474, by rfl⟩ : syracuseStep 901061 = 168949) (by norm_num)
theorem B507865 : Blo 397767 507865 := bbase (se 2 (by rfl) ⟨190449, by rfl⟩ : syracuseStep 507865 = 380899) (by norm_num)
theorem B770045 : Blo 397767 770045 := bbase (se 3 (by rfl) ⟨144383, by rfl⟩ : syracuseStep 770045 = 288767) (by norm_num)
theorem B1523717 : Blo 397767 1523717 := bbase (se 4 (by rfl) ⟨142848, by rfl⟩ : syracuseStep 1523717 = 285697) (by norm_num)
theorem B901133 : Blo 397767 901133 := bbase (se 3 (by rfl) ⟨168962, by rfl⟩ : syracuseStep 901133 = 337925) (by norm_num)
theorem B671773 : Blo 397767 671773 := bbase (se 3 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 671773 = 251915) (by norm_num)
theorem B507961 : Blo 397767 507961 := bbase (se 2 (by rfl) ⟨190485, by rfl⟩ : syracuseStep 507961 = 380971) (by norm_num)
theorem B901205 : Blo 397767 901205 := bbase (se 8 (by rfl) ⟨5280, by rfl⟩ : syracuseStep 901205 = 10561) (by norm_num)
theorem B671861 : Blo 397767 671861 := bbase (se 5 (by rfl) ⟨31493, by rfl⟩ : syracuseStep 671861 = 62987) (by norm_num)
theorem B901277 : Blo 397767 901277 := bbase (se 3 (by rfl) ⟨168989, by rfl⟩ : syracuseStep 901277 = 337979) (by norm_num)
theorem B2277557 : Blo 397767 2277557 := bbase (se 5 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 2277557 = 213521) (by norm_num)
theorem B901349 : Blo 397767 901349 := bbase (se 4 (by rfl) ⟨84501, by rfl⟩ : syracuseStep 901349 = 169003) (by norm_num)
theorem B508133 : Blo 397767 508133 := bbase (se 4 (by rfl) ⟨47637, by rfl⟩ : syracuseStep 508133 = 95275) (by norm_num)
theorem B671989 : Blo 397767 671989 := bbase (se 5 (by rfl) ⟨31499, by rfl⟩ : syracuseStep 671989 = 62999) (by norm_num)
theorem B508189 : Blo 397767 508189 := bbase (se 3 (by rfl) ⟨95285, by rfl⟩ : syracuseStep 508189 = 190571) (by norm_num)
theorem B1524005 : Blo 397767 1524005 := bbase (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) (by norm_num)
theorem B901421 : Blo 397767 901421 := bbase (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) (by norm_num)
theorem B672077 : Blo 397767 672077 := bbase (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) (by norm_num)
theorem B901493 : Blo 397767 901493 := bbase (se 5 (by rfl) ⟨42257, by rfl⟩ : syracuseStep 901493 = 84515) (by norm_num)
theorem B508285 : Blo 397767 508285 := bbase (se 3 (by rfl) ⟨95303, by rfl⟩ : syracuseStep 508285 = 190607) (by norm_num)
theorem B901565 : Blo 397767 901565 := bbase (se 3 (by rfl) ⟨169043, by rfl⟩ : syracuseStep 901565 = 338087) (by norm_num)
theorem B672205 : Blo 397767 672205 := bbase (se 3 (by rfl) ⟨126038, by rfl⟩ : syracuseStep 672205 = 252077) (by norm_num)
theorem B5816789 : Blo 397767 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B10961365 : Blo 397767 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B901637 : Blo 397767 901637 := bbase (se 4 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 901637 = 169057) (by norm_num)
theorem B2015765 : Blo 397767 2015765 := bbase (se 6 (by rfl) ⟨47244, by rfl⟩ : syracuseStep 2015765 = 94489) (by norm_num)
theorem B672293 : Blo 397767 672293 := bbase (se 4 (by rfl) ⟨63027, by rfl⟩ : syracuseStep 672293 = 126055) (by norm_num)
theorem B508457 : Blo 397767 508457 := bbase (se 2 (by rfl) ⟨190671, by rfl⟩ : syracuseStep 508457 = 381343) (by norm_num)
theorem B901709 : Blo 397767 901709 := bbase (se 3 (by rfl) ⟨169070, by rfl⟩ : syracuseStep 901709 = 338141) (by norm_num)
theorem B901781 : Blo 397767 901781 := bbase (se 6 (by rfl) ⟨21135, by rfl⟩ : syracuseStep 901781 = 42271) (by norm_num)
theorem B672421 : Blo 397767 672421 := bbase (se 4 (by rfl) ⟨63039, by rfl⟩ : syracuseStep 672421 = 126079) (by norm_num)
theorem B443053 : Blo 397767 443053 := bbase (se 3 (by rfl) ⟨83072, by rfl⟩ : syracuseStep 443053 = 166145) (by norm_num)
theorem B901853 : Blo 397767 901853 := bbase (se 3 (by rfl) ⟨169097, by rfl⟩ : syracuseStep 901853 = 338195) (by norm_num)
theorem B672509 : Blo 397767 672509 := bbase (se 3 (by rfl) ⟨126095, by rfl⟩ : syracuseStep 672509 = 252191) (by norm_num)
theorem B639749 : Blo 397767 639749 := bbase (se 4 (by rfl) ⟨59976, by rfl⟩ : syracuseStep 639749 = 119953) (by norm_num)
theorem B901925 : Blo 397767 901925 := bbase (se 4 (by rfl) ⟨84555, by rfl⟩ : syracuseStep 901925 = 169111) (by norm_num)
theorem B1917749 : Blo 397767 1917749 := bbase (se 5 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 1917749 = 179789) (by norm_num)
theorem B901997 : Blo 397767 901997 := bbase (se 3 (by rfl) ⟨169124, by rfl⟩ : syracuseStep 901997 = 338249) (by norm_num)
theorem B672637 : Blo 397767 672637 := bbase (se 3 (by rfl) ⟨126119, by rfl⟩ : syracuseStep 672637 = 252239) (by norm_num)
theorem B1819525 : Blo 397767 1819525 := bbase (se 4 (by rfl) ⟨170580, by rfl⟩ : syracuseStep 1819525 = 341161) (by norm_num)
theorem B607117 : Blo 397767 607117 := bbase (se 3 (by rfl) ⟨113834, by rfl⟩ : syracuseStep 607117 = 227669) (by norm_num)
theorem B902069 : Blo 397767 902069 := bbase (se 5 (by rfl) ⟨42284, by rfl⟩ : syracuseStep 902069 = 84569) (by norm_num)
theorem B672725 : Blo 397767 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B607213 : Blo 397767 607213 := bbase (se 3 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 607213 = 227705) (by norm_num)
theorem B902141 : Blo 397767 902141 := bbase (se 3 (by rfl) ⟨169151, by rfl⟩ : syracuseStep 902141 = 338303) (by norm_num)
theorem B902213 : Blo 397767 902213 := bbase (se 4 (by rfl) ⟨84582, by rfl⟩ : syracuseStep 902213 = 169165) (by norm_num)
theorem B672853 : Blo 397767 672853 := bbase (se 8 (by rfl) ⟨3942, by rfl⟩ : syracuseStep 672853 = 7885) (by norm_num)
theorem B410729 : Blo 397767 410729 := bbase (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) (by norm_num)
theorem B902285 : Blo 397767 902285 := bbase (se 3 (by rfl) ⟨169178, by rfl⟩ : syracuseStep 902285 = 338357) (by norm_num)
theorem B672941 : Blo 397767 672941 := bbase (se 3 (by rfl) ⟨126176, by rfl⟩ : syracuseStep 672941 = 252353) (by norm_num)
theorem B2802869 : Blo 397767 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B771277 : Blo 397767 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B902357 : Blo 397767 902357 := bbase (se 7 (by rfl) ⟨10574, by rfl⟩ : syracuseStep 902357 = 21149) (by norm_num)
theorem B902429 : Blo 397767 902429 := bbase (se 3 (by rfl) ⟨169205, by rfl⟩ : syracuseStep 902429 = 338411) (by norm_num)
theorem B673069 : Blo 397767 673069 := bbase (se 3 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 673069 = 252401) (by norm_num)
theorem B902501 : Blo 397767 902501 := bbase (se 4 (by rfl) ⟨84609, by rfl⟩ : syracuseStep 902501 = 169219) (by norm_num)
theorem B673157 : Blo 397767 673157 := bbase (se 4 (by rfl) ⟨63108, by rfl⟩ : syracuseStep 673157 = 126217) (by norm_num)
theorem B771461 : Blo 397767 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B902573 : Blo 397767 902573 := bbase (se 3 (by rfl) ⟨169232, by rfl⟩ : syracuseStep 902573 = 338465) (by norm_num)
theorem B1525189 : Blo 397767 1525189 := bbase (se 4 (by rfl) ⟨142986, by rfl⟩ : syracuseStep 1525189 = 285973) (by norm_num)
theorem B902645 : Blo 397767 902645 := bbase (se 5 (by rfl) ⟨42311, by rfl⟩ : syracuseStep 902645 = 84623) (by norm_num)
theorem B673285 : Blo 397767 673285 := bbase (se 4 (by rfl) ⟨63120, by rfl⟩ : syracuseStep 673285 = 126241) (by norm_num)
theorem B902717 : Blo 397767 902717 := bbase (se 3 (by rfl) ⟨169259, by rfl⟩ : syracuseStep 902717 = 338519) (by norm_num)
theorem B2475605 : Blo 397767 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B673373 : Blo 397767 673373 := bbase (se 3 (by rfl) ⟨126257, by rfl⟩ : syracuseStep 673373 = 252515) (by norm_num)
theorem B902789 : Blo 397767 902789 := bbase (se 4 (by rfl) ⟨84636, by rfl⟩ : syracuseStep 902789 = 169273) (by norm_num)
theorem B640685 : Blo 397767 640685 := bbase (se 3 (by rfl) ⟨120128, by rfl⟩ : syracuseStep 640685 = 240257) (by norm_num)
theorem B902861 : Blo 397767 902861 := bbase (se 3 (by rfl) ⟨169286, by rfl⟩ : syracuseStep 902861 = 338573) (by norm_num)
theorem B673501 : Blo 397767 673501 := bbase (se 3 (by rfl) ⟨126281, by rfl⟩ : syracuseStep 673501 = 252563) (by norm_num)
theorem B902933 : Blo 397767 902933 := bbase (se 6 (by rfl) ⟨21162, by rfl⟩ : syracuseStep 902933 = 42325) (by norm_num)
theorem B2017061 : Blo 397767 2017061 := bbase (se 4 (by rfl) ⟨189099, by rfl⟩ : syracuseStep 2017061 = 378199) (by norm_num)
theorem B673589 : Blo 397767 673589 := bbase (se 5 (by rfl) ⟨31574, by rfl⟩ : syracuseStep 673589 = 63149) (by norm_num)
theorem B903005 : Blo 397767 903005 := bbase (se 3 (by rfl) ⟨169313, by rfl⟩ : syracuseStep 903005 = 338627) (by norm_num)
theorem B903077 : Blo 397767 903077 := bbase (se 4 (by rfl) ⟨84663, by rfl⟩ : syracuseStep 903077 = 169327) (by norm_num)
theorem B673717 : Blo 397767 673717 := bbase (se 5 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 673717 = 63161) (by norm_num)
theorem B903149 : Blo 397767 903149 := bbase (se 3 (by rfl) ⟨169340, by rfl⟩ : syracuseStep 903149 = 338681) (by norm_num)
theorem B673805 : Blo 397767 673805 := bbase (se 3 (by rfl) ⟨126338, by rfl⟩ : syracuseStep 673805 = 252677) (by norm_num)
theorem B608285 : Blo 397767 608285 := bbase (se 3 (by rfl) ⟨114053, by rfl⟩ : syracuseStep 608285 = 228107) (by norm_num)
theorem B903221 : Blo 397767 903221 := bbase (se 5 (by rfl) ⟨42338, by rfl⟩ : syracuseStep 903221 = 84677) (by norm_num)
theorem B608357 : Blo 397767 608357 := bbase (se 4 (by rfl) ⟨57033, by rfl⟩ : syracuseStep 608357 = 114067) (by norm_num)
theorem B1722485 : Blo 397767 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B903293 : Blo 397767 903293 := bbase (se 3 (by rfl) ⟨169367, by rfl⟩ : syracuseStep 903293 = 338735) (by norm_num)
theorem B1099909 : Blo 397767 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B673933 : Blo 397767 673933 := bbase (se 3 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 673933 = 252725) (by norm_num)
theorem B903365 : Blo 397767 903365 := bbase (se 4 (by rfl) ⟨84690, by rfl⟩ : syracuseStep 903365 = 169381) (by norm_num)
theorem B674021 : Blo 397767 674021 := bbase (se 4 (by rfl) ⟨63189, by rfl⟩ : syracuseStep 674021 = 126379) (by norm_num)
theorem B542957 : Blo 397767 542957 := bbase (se 3 (by rfl) ⟨101804, by rfl⟩ : syracuseStep 542957 = 203609) (by norm_num)
theorem B903437 : Blo 397767 903437 := bbase (se 3 (by rfl) ⟨169394, by rfl⟩ : syracuseStep 903437 = 338789) (by norm_num)
theorem B641333 : Blo 397767 641333 := bbase (se 5 (by rfl) ⟨30062, by rfl⟩ : syracuseStep 641333 = 60125) (by norm_num)
theorem B2279765 : Blo 397767 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B903509 : Blo 397767 903509 := bbase (se 10 (by rfl) ⟨1323, by rfl⟩ : syracuseStep 903509 = 2647) (by norm_num)
theorem B772445 : Blo 397767 772445 := bbase (se 3 (by rfl) ⟨144833, by rfl⟩ : syracuseStep 772445 = 289667) (by norm_num)
theorem B674149 : Blo 397767 674149 := bbase (se 4 (by rfl) ⟨63201, by rfl⟩ : syracuseStep 674149 = 126403) (by norm_num)
theorem B903565 : Blo 397767 903565 := bbase (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) (by norm_num)
theorem B903581 : Blo 397767 903581 := bbase (se 3 (by rfl) ⟨169421, by rfl⟩ : syracuseStep 903581 = 338843) (by norm_num)
theorem B674237 : Blo 397767 674237 := bbase (se 3 (by rfl) ⟨126419, by rfl⟩ : syracuseStep 674237 = 252839) (by norm_num)
theorem B3230165 : Blo 397767 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B903653 : Blo 397767 903653 := bbase (se 4 (by rfl) ⟨84717, by rfl⟩ : syracuseStep 903653 = 169435) (by norm_num)
theorem B903725 : Blo 397767 903725 := bbase (se 3 (by rfl) ⟨169448, by rfl⟩ : syracuseStep 903725 = 338897) (by norm_num)
theorem B674365 : Blo 397767 674365 := bbase (se 3 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 674365 = 252887) (by norm_num)
theorem B903797 : Blo 397767 903797 := bbase (se 5 (by rfl) ⟨42365, by rfl⟩ : syracuseStep 903797 = 84731) (by norm_num)
theorem B674453 : Blo 397767 674453 := bbase (se 6 (by rfl) ⟨15807, by rfl⟩ : syracuseStep 674453 = 31615) (by norm_num)
theorem B608941 : Blo 397767 608941 := bbase (se 3 (by rfl) ⟨114176, by rfl⟩ : syracuseStep 608941 = 228353) (by norm_num)
theorem B903869 : Blo 397767 903869 := bbase (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) (by norm_num)
theorem B1034957 : Blo 397767 1034957 := bbase (se 3 (by rfl) ⟨194054, by rfl⟩ : syracuseStep 1034957 = 388109) (by norm_num)
theorem B7785173 : Blo 397767 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B903941 : Blo 397767 903941 := bbase (se 4 (by rfl) ⟨84744, by rfl⟩ : syracuseStep 903941 = 169489) (by norm_num)
theorem B674581 : Blo 397767 674581 := bbase (se 6 (by rfl) ⟨15810, by rfl⟩ : syracuseStep 674581 = 31621) (by norm_num)
theorem B674669 : Blo 397767 674669 := bbase (se 3 (by rfl) ⟨126500, by rfl⟩ : syracuseStep 674669 = 253001) (by norm_num)
theorem B412609 : Blo 397767 412609 := bbase (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) (by norm_num)
theorem B674797 : Blo 397767 674797 := bbase (se 3 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 674797 = 253049) (by norm_num)
theorem B2018357 : Blo 397767 2018357 := bbase (se 5 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 2018357 = 189221) (by norm_num)
theorem B674885 : Blo 397767 674885 := bbase (se 4 (by rfl) ⟨63270, by rfl⟩ : syracuseStep 674885 = 126541) (by norm_num)
theorem B675013 : Blo 397767 675013 := bbase (se 4 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 675013 = 126565) (by norm_num)
theorem B642325 : Blo 397767 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B675101 : Blo 397767 675101 := bbase (se 3 (by rfl) ⟨126581, by rfl⟩ : syracuseStep 675101 = 253163) (by norm_num)
theorem B478505 : Blo 397767 478505 := bbase (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) (by norm_num)
theorem B675229 : Blo 397767 675229 := bbase (se 3 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 675229 = 253211) (by norm_num)
theorem B675317 : Blo 397767 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B478813 : Blo 397767 478813 := bbase (se 3 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 478813 = 179555) (by norm_num)
theorem B675445 : Blo 397767 675445 := bbase (se 5 (by rfl) ⟨31661, by rfl⟩ : syracuseStep 675445 = 63323) (by norm_num)
theorem B478909 : Blo 397767 478909 := bbase (se 3 (by rfl) ⟨89795, by rfl⟩ : syracuseStep 478909 = 179591) (by norm_num)
theorem B675533 : Blo 397767 675533 := bbase (se 3 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 675533 = 253325) (by norm_num)
theorem B642773 : Blo 397767 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B675661 : Blo 397767 675661 := bbase (se 3 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 675661 = 253373) (by norm_num)
theorem B642973 : Blo 397767 642973 := bbase (se 3 (by rfl) ⟨120557, by rfl⟩ : syracuseStep 642973 = 241115) (by norm_num)
theorem B675749 : Blo 397767 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B479197 : Blo 397767 479197 := bbase (se 3 (by rfl) ⟨89849, by rfl⟩ : syracuseStep 479197 = 179699) (by norm_num)
theorem B675877 : Blo 397767 675877 := bbase (se 4 (by rfl) ⟨63363, by rfl⟩ : syracuseStep 675877 = 126727) (by norm_num)
theorem B675965 : Blo 397767 675965 := bbase (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) (by norm_num)
theorem B479389 : Blo 397767 479389 := bbase (se 3 (by rfl) ⟨89885, by rfl⟩ : syracuseStep 479389 = 179771) (by norm_num)
theorem B643229 : Blo 397767 643229 := bbase (se 3 (by rfl) ⟨120605, by rfl⟩ : syracuseStep 643229 = 241211) (by norm_num)
theorem B512173 : Blo 397767 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B676093 : Blo 397767 676093 := bbase (se 3 (by rfl) ⟨126767, by rfl⟩ : syracuseStep 676093 = 253535) (by norm_num)
theorem B1134917 : Blo 397767 1134917 := bbase (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) (by norm_num)
theorem B2019653 : Blo 397767 2019653 := bbase (se 4 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 2019653 = 378685) (by norm_num)
theorem B676181 : Blo 397767 676181 := bbase (se 10 (by rfl) ⟨990, by rfl⟩ : syracuseStep 676181 = 1981) (by norm_num)
theorem B610669 : Blo 397767 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B741773 : Blo 397767 741773 := bbase (se 3 (by rfl) ⟨139082, by rfl⟩ : syracuseStep 741773 = 278165) (by norm_num)
theorem B1921477 : Blo 397767 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B676309 : Blo 397767 676309 := bbase (se 7 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 676309 = 15851) (by norm_num)
theorem B676397 : Blo 397767 676397 := bbase (se 3 (by rfl) ⟨126824, by rfl⟩ : syracuseStep 676397 = 253649) (by norm_num)
theorem B676525 : Blo 397767 676525 := bbase (se 3 (by rfl) ⟨126848, by rfl⟩ : syracuseStep 676525 = 253697) (by norm_num)
theorem B676613 : Blo 397767 676613 := bbase (se 4 (by rfl) ⟨63432, by rfl⟩ : syracuseStep 676613 = 126865) (by norm_num)
theorem B2872181 : Blo 397767 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B676741 : Blo 397767 676741 := bbase (se 4 (by rfl) ⟨63444, by rfl⟩ : syracuseStep 676741 = 126889) (by norm_num)
theorem B676829 : Blo 397767 676829 := bbase (se 3 (by rfl) ⟨126905, by rfl⟩ : syracuseStep 676829 = 253811) (by norm_num)
theorem B447493 : Blo 397767 447493 := bbase (se 4 (by rfl) ⟨41952, by rfl⟩ : syracuseStep 447493 = 83905) (by norm_num)
theorem B480269 : Blo 397767 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B447529 : Blo 397767 447529 := bbase (se 2 (by rfl) ⟨167823, by rfl⟩ : syracuseStep 447529 = 335647) (by norm_num)
theorem B447565 : Blo 397767 447565 := bbase (se 3 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 447565 = 167837) (by norm_num)
theorem B808013 : Blo 397767 808013 := bbase (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) (by norm_num)
theorem B676957 : Blo 397767 676957 := bbase (se 3 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 676957 = 253859) (by norm_num)
theorem B447601 : Blo 397767 447601 := bbase (se 2 (by rfl) ⟨167850, by rfl⟩ : syracuseStep 447601 = 335701) (by norm_num)
theorem B447637 : Blo 397767 447637 := bbase (se 6 (by rfl) ⟨10491, by rfl⟩ : syracuseStep 447637 = 20983) (by norm_num)
theorem B677045 : Blo 397767 677045 := bbase (se 5 (by rfl) ⟨31736, by rfl⟩ : syracuseStep 677045 = 63473) (by norm_num)
theorem B447673 : Blo 397767 447673 := bbase (se 2 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 447673 = 335755) (by norm_num)
theorem B447709 : Blo 397767 447709 := bbase (se 3 (by rfl) ⟨83945, by rfl⟩ : syracuseStep 447709 = 167891) (by norm_num)
theorem B447745 : Blo 397767 447745 := bbase (se 2 (by rfl) ⟨167904, by rfl⟩ : syracuseStep 447745 = 335809) (by norm_num)
theorem B447781 : Blo 397767 447781 := bbase (se 4 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 447781 = 83959) (by norm_num)
theorem B677173 : Blo 397767 677173 := bbase (se 5 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 677173 = 63485) (by norm_num)
theorem B447817 : Blo 397767 447817 := bbase (se 2 (by rfl) ⟨167931, by rfl⟩ : syracuseStep 447817 = 335863) (by norm_num)
theorem B447853 : Blo 397767 447853 := bbase (se 3 (by rfl) ⟨83972, by rfl⟩ : syracuseStep 447853 = 167945) (by norm_num)
theorem B677261 : Blo 397767 677261 := bbase (se 3 (by rfl) ⟨126986, by rfl⟩ : syracuseStep 677261 = 253973) (by norm_num)
theorem B447889 : Blo 397767 447889 := bbase (se 2 (by rfl) ⟨167958, by rfl⟩ : syracuseStep 447889 = 335917) (by norm_num)
theorem B447925 : Blo 397767 447925 := bbase (se 5 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 447925 = 41993) (by norm_num)
theorem B447961 : Blo 397767 447961 := bbase (se 2 (by rfl) ⟨167985, by rfl⟩ : syracuseStep 447961 = 335971) (by norm_num)
theorem B1136101 : Blo 397767 1136101 := bbase (se 4 (by rfl) ⟨106509, by rfl⟩ : syracuseStep 1136101 = 213019) (by norm_num)
theorem B447997 : Blo 397767 447997 := bbase (se 3 (by rfl) ⟨83999, by rfl⟩ : syracuseStep 447997 = 167999) (by norm_num)
theorem B480773 : Blo 397767 480773 := bbase (se 4 (by rfl) ⟨45072, by rfl⟩ : syracuseStep 480773 = 90145) (by norm_num)
theorem B677389 : Blo 397767 677389 := bbase (se 3 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 677389 = 254021) (by norm_num)
theorem B448033 : Blo 397767 448033 := bbase (se 2 (by rfl) ⟨168012, by rfl⟩ : syracuseStep 448033 = 336025) (by norm_num)
theorem B480821 : Blo 397767 480821 := bbase (se 5 (by rfl) ⟨22538, by rfl⟩ : syracuseStep 480821 = 45077) (by norm_num)
theorem B448069 : Blo 397767 448069 := bbase (se 4 (by rfl) ⟨42006, by rfl⟩ : syracuseStep 448069 = 84013) (by norm_num)
theorem B2020949 : Blo 397767 2020949 := bbase (se 8 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 2020949 = 23683) (by norm_num)
theorem B677477 : Blo 397767 677477 := bbase (se 4 (by rfl) ⟨63513, by rfl⟩ : syracuseStep 677477 = 127027) (by norm_num)
theorem B448105 : Blo 397767 448105 := bbase (se 2 (by rfl) ⟨168039, by rfl⟩ : syracuseStep 448105 = 336079) (by norm_num)
theorem B1136261 : Blo 397767 1136261 := bbase (se 4 (by rfl) ⟨106524, by rfl⟩ : syracuseStep 1136261 = 213049) (by norm_num)
theorem B448141 : Blo 397767 448141 := bbase (se 3 (by rfl) ⟨84026, by rfl⟩ : syracuseStep 448141 = 168053) (by norm_num)
theorem B448177 : Blo 397767 448177 := bbase (se 2 (by rfl) ⟨168066, by rfl⟩ : syracuseStep 448177 = 336133) (by norm_num)
theorem B448213 : Blo 397767 448213 := bbase (se 7 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 448213 = 10505) (by norm_num)
theorem B677605 : Blo 397767 677605 := bbase (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) (by norm_num)
theorem B448249 : Blo 397767 448249 := bbase (se 2 (by rfl) ⟨168093, by rfl⟩ : syracuseStep 448249 = 336187) (by norm_num)
theorem B448285 : Blo 397767 448285 := bbase (se 3 (by rfl) ⟨84053, by rfl⟩ : syracuseStep 448285 = 168107) (by norm_num)
theorem B481081 : Blo 397767 481081 := bbase (se 2 (by rfl) ⟨180405, by rfl⟩ : syracuseStep 481081 = 360811) (by norm_num)
theorem B677693 : Blo 397767 677693 := bbase (se 3 (by rfl) ⟨127067, by rfl⟩ : syracuseStep 677693 = 254135) (by norm_num)
theorem B448321 : Blo 397767 448321 := bbase (se 2 (by rfl) ⟨168120, by rfl⟩ : syracuseStep 448321 = 336241) (by norm_num)
theorem B3037013 : Blo 397767 3037013 := bbase (se 9 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 3037013 = 17795) (by norm_num)
theorem B448357 : Blo 397767 448357 := bbase (se 4 (by rfl) ⟨42033, by rfl⟩ : syracuseStep 448357 = 84067) (by norm_num)
theorem B1136501 : Blo 397767 1136501 := bbase (se 5 (by rfl) ⟨53273, by rfl⟩ : syracuseStep 1136501 = 106547) (by norm_num)
theorem B448393 : Blo 397767 448393 := bbase (se 2 (by rfl) ⟨168147, by rfl⟩ : syracuseStep 448393 = 336295) (by norm_num)
theorem B448429 : Blo 397767 448429 := bbase (se 3 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 448429 = 168161) (by norm_num)
theorem B677821 : Blo 397767 677821 := bbase (se 3 (by rfl) ⟨127091, by rfl⟩ : syracuseStep 677821 = 254183) (by norm_num)
theorem B448465 : Blo 397767 448465 := bbase (se 2 (by rfl) ⟨168174, by rfl⟩ : syracuseStep 448465 = 336349) (by norm_num)
theorem B448501 : Blo 397767 448501 := bbase (se 5 (by rfl) ⟨21023, by rfl⟩ : syracuseStep 448501 = 42047) (by norm_num)
theorem B677909 : Blo 397767 677909 := bbase (se 6 (by rfl) ⟨15888, by rfl⟩ : syracuseStep 677909 = 31777) (by norm_num)
theorem B448537 : Blo 397767 448537 := bbase (se 2 (by rfl) ⟨168201, by rfl⟩ : syracuseStep 448537 = 336403) (by norm_num)
theorem B1136693 : Blo 397767 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B448573 : Blo 397767 448573 := bbase (se 3 (by rfl) ⟨84107, by rfl⟩ : syracuseStep 448573 = 168215) (by norm_num)
theorem B481345 : Blo 397767 481345 := bbase (se 2 (by rfl) ⟨180504, by rfl⟩ : syracuseStep 481345 = 361009) (by norm_num)
theorem B448609 : Blo 397767 448609 := bbase (se 2 (by rfl) ⟨168228, by rfl⟩ : syracuseStep 448609 = 336457) (by norm_num)
theorem B448645 : Blo 397767 448645 := bbase (se 4 (by rfl) ⟨42060, by rfl⟩ : syracuseStep 448645 = 84121) (by norm_num)
theorem B448681 : Blo 397767 448681 := bbase (se 2 (by rfl) ⟨168255, by rfl⟩ : syracuseStep 448681 = 336511) (by norm_num)
theorem B514225 : Blo 397767 514225 := bbase (se 2 (by rfl) ⟨192834, by rfl⟩ : syracuseStep 514225 = 385669) (by norm_num)
theorem B481465 : Blo 397767 481465 := bbase (se 2 (by rfl) ⟨180549, by rfl⟩ : syracuseStep 481465 = 361099) (by norm_num)
theorem B448717 : Blo 397767 448717 := bbase (se 3 (by rfl) ⟨84134, by rfl⟩ : syracuseStep 448717 = 168269) (by norm_num)
theorem B448753 : Blo 397767 448753 := bbase (se 2 (by rfl) ⟨168282, by rfl⟩ : syracuseStep 448753 = 336565) (by norm_num)
theorem B448789 : Blo 397767 448789 := bbase (se 6 (by rfl) ⟨10518, by rfl⟩ : syracuseStep 448789 = 21037) (by norm_num)
theorem B448825 : Blo 397767 448825 := bbase (se 2 (by rfl) ⟨168309, by rfl⟩ : syracuseStep 448825 = 336619) (by norm_num)
theorem B448861 : Blo 397767 448861 := bbase (se 3 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 448861 = 168323) (by norm_num)
theorem B448897 : Blo 397767 448897 := bbase (se 2 (by rfl) ⟨168336, by rfl⟩ : syracuseStep 448897 = 336673) (by norm_num)
theorem B448933 : Blo 397767 448933 := bbase (se 4 (by rfl) ⟨42087, by rfl⟩ : syracuseStep 448933 = 84175) (by norm_num)
theorem B448969 : Blo 397767 448969 := bbase (se 2 (by rfl) ⟨168363, by rfl⟩ : syracuseStep 448969 = 336727) (by norm_num)
theorem B449005 : Blo 397767 449005 := bbase (se 3 (by rfl) ⟨84188, by rfl⟩ : syracuseStep 449005 = 168377) (by norm_num)
theorem B449041 : Blo 397767 449041 := bbase (se 2 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 449041 = 336781) (by norm_num)
theorem B1628693 : Blo 397767 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B449077 : Blo 397767 449077 := bbase (se 5 (by rfl) ⟨21050, by rfl⟩ : syracuseStep 449077 = 42101) (by norm_num)
theorem B449113 : Blo 397767 449113 := bbase (se 2 (by rfl) ⟨168417, by rfl⟩ : syracuseStep 449113 = 336835) (by norm_num)
theorem B449149 : Blo 397767 449149 := bbase (se 3 (by rfl) ⟨84215, by rfl⟩ : syracuseStep 449149 = 168431) (by norm_num)
theorem B449185 : Blo 397767 449185 := bbase (se 2 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 449185 = 336889) (by norm_num)
theorem B1628837 : Blo 397767 1628837 := bbase (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) (by norm_num)
theorem B449221 : Blo 397767 449221 := bbase (se 4 (by rfl) ⟨42114, by rfl⟩ : syracuseStep 449221 = 84229) (by norm_num)
theorem B514769 : Blo 397767 514769 := bbase (se 2 (by rfl) ⟨193038, by rfl⟩ : syracuseStep 514769 = 386077) (by norm_num)
theorem B449257 : Blo 397767 449257 := bbase (se 2 (by rfl) ⟨168471, by rfl⟩ : syracuseStep 449257 = 336943) (by norm_num)
theorem B449293 : Blo 397767 449293 := bbase (se 3 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 449293 = 168485) (by norm_num)
theorem B449329 : Blo 397767 449329 := bbase (se 2 (by rfl) ⟨168498, by rfl⟩ : syracuseStep 449329 = 336997) (by norm_num)
theorem B449365 : Blo 397767 449365 := bbase (se 9 (by rfl) ⟨1316, by rfl⟩ : syracuseStep 449365 = 2633) (by norm_num)
theorem B2022245 : Blo 397767 2022245 := bbase (se 4 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 2022245 = 379171) (by norm_num)
theorem B449401 : Blo 397767 449401 := bbase (se 2 (by rfl) ⟨168525, by rfl⟩ : syracuseStep 449401 = 337051) (by norm_num)
theorem B514945 : Blo 397767 514945 := bbase (se 2 (by rfl) ⟨193104, by rfl⟩ : syracuseStep 514945 = 386209) (by norm_num)
theorem B449437 : Blo 397767 449437 := bbase (se 3 (by rfl) ⟨84269, by rfl⟩ : syracuseStep 449437 = 168539) (by norm_num)
theorem B449473 : Blo 397767 449473 := bbase (se 2 (by rfl) ⟨168552, by rfl⟩ : syracuseStep 449473 = 337105) (by norm_num)
theorem B1498085 : Blo 397767 1498085 := bbase (se 4 (by rfl) ⟨140445, by rfl⟩ : syracuseStep 1498085 = 280891) (by norm_num)
theorem B449509 : Blo 397767 449509 := bbase (se 4 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 449509 = 84283) (by norm_num)
theorem B449545 : Blo 397767 449545 := bbase (se 2 (by rfl) ⟨168579, by rfl⟩ : syracuseStep 449545 = 337159) (by norm_num)
theorem B482321 : Blo 397767 482321 := bbase (se 2 (by rfl) ⟨180870, by rfl⟩ : syracuseStep 482321 = 361741) (by norm_num)
theorem B1137685 : Blo 397767 1137685 := bbase (se 6 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 1137685 = 53329) (by norm_num)
theorem B449581 : Blo 397767 449581 := bbase (se 3 (by rfl) ⟨84296, by rfl⟩ : syracuseStep 449581 = 168593) (by norm_num)
theorem B449617 : Blo 397767 449617 := bbase (se 2 (by rfl) ⟨168606, by rfl⟩ : syracuseStep 449617 = 337213) (by norm_num)
theorem B449653 : Blo 397767 449653 := bbase (se 5 (by rfl) ⟨21077, by rfl⟩ : syracuseStep 449653 = 42155) (by norm_num)
theorem B449689 : Blo 397767 449689 := bbase (se 2 (by rfl) ⟨168633, by rfl⟩ : syracuseStep 449689 = 337267) (by norm_num)
theorem B449725 : Blo 397767 449725 := bbase (se 3 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 449725 = 168647) (by norm_num)
theorem B449761 : Blo 397767 449761 := bbase (se 2 (by rfl) ⟨168660, by rfl⟩ : syracuseStep 449761 = 337321) (by norm_num)
theorem B449797 : Blo 397767 449797 := bbase (se 4 (by rfl) ⟨42168, by rfl⟩ : syracuseStep 449797 = 84337) (by norm_num)
theorem B449833 : Blo 397767 449833 := bbase (se 2 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 449833 = 337375) (by norm_num)
theorem B1006901 : Blo 397767 1006901 := bbase (se 5 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 1006901 = 94397) (by norm_num)
theorem B908597 : Blo 397767 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B449869 : Blo 397767 449869 := bbase (se 3 (by rfl) ⟨84350, by rfl⟩ : syracuseStep 449869 = 168701) (by norm_num)
theorem B15621461 : Blo 397767 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B449905 : Blo 397767 449905 := bbase (se 2 (by rfl) ⟨168714, by rfl⟩ : syracuseStep 449905 = 337429) (by norm_num)
theorem B449941 : Blo 397767 449941 := bbase (se 6 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 449941 = 21091) (by norm_num)
theorem B1564085 : Blo 397767 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B449977 : Blo 397767 449977 := bbase (se 2 (by rfl) ⟨168741, by rfl⟩ : syracuseStep 449977 = 337483) (by norm_num)
theorem B450013 : Blo 397767 450013 := bbase (se 3 (by rfl) ⟨84377, by rfl⟩ : syracuseStep 450013 = 168755) (by norm_num)
theorem B1007093 : Blo 397767 1007093 := bbase (se 5 (by rfl) ⟨47207, by rfl⟩ : syracuseStep 1007093 = 94415) (by norm_num)
theorem B450049 : Blo 397767 450049 := bbase (se 2 (by rfl) ⟨168768, by rfl⟩ : syracuseStep 450049 = 337537) (by norm_num)
theorem B450085 : Blo 397767 450085 := bbase (se 4 (by rfl) ⟨42195, by rfl⟩ : syracuseStep 450085 = 84391) (by norm_num)
theorem B450121 : Blo 397767 450121 := bbase (se 2 (by rfl) ⟨168795, by rfl⟩ : syracuseStep 450121 = 337591) (by norm_num)
theorem B450157 : Blo 397767 450157 := bbase (se 3 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 450157 = 168809) (by norm_num)
theorem B3825269 : Blo 397767 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B450193 : Blo 397767 450193 := bbase (se 2 (by rfl) ⟨168822, by rfl⟩ : syracuseStep 450193 = 337645) (by norm_num)
theorem B5758613 : Blo 397767 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B450229 : Blo 397767 450229 := bbase (se 5 (by rfl) ⟨21104, by rfl⟩ : syracuseStep 450229 = 42209) (by norm_num)
theorem B2088629 : Blo 397767 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B450265 : Blo 397767 450265 := bbase (se 2 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 450265 = 337699) (by norm_num)
theorem B450301 : Blo 397767 450301 := bbase (se 3 (by rfl) ⟨84431, by rfl⟩ : syracuseStep 450301 = 168863) (by norm_num)
theorem B450337 : Blo 397767 450337 := bbase (se 2 (by rfl) ⟨168876, by rfl⟩ : syracuseStep 450337 = 337753) (by norm_num)
theorem B450373 : Blo 397767 450373 := bbase (se 4 (by rfl) ⟨42222, by rfl⟩ : syracuseStep 450373 = 84445) (by norm_num)
theorem B1007437 : Blo 397767 1007437 := bbase (se 3 (by rfl) ⟨188894, by rfl⟩ : syracuseStep 1007437 = 377789) (by norm_num)
theorem B450409 : Blo 397767 450409 := bbase (se 2 (by rfl) ⟨168903, by rfl⟩ : syracuseStep 450409 = 337807) (by norm_num)
theorem B450445 : Blo 397767 450445 := bbase (se 3 (by rfl) ⟨84458, by rfl⟩ : syracuseStep 450445 = 168917) (by norm_num)
theorem B450481 : Blo 397767 450481 := bbase (se 2 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 450481 = 337861) (by norm_num)
theorem B1007549 : Blo 397767 1007549 := bbase (se 3 (by rfl) ⟨188915, by rfl⟩ : syracuseStep 1007549 = 377831) (by norm_num)
theorem B450517 : Blo 397767 450517 := bbase (se 7 (by rfl) ⟨5279, by rfl⟩ : syracuseStep 450517 = 10559) (by norm_num)
theorem B810973 : Blo 397767 810973 := bbase (se 3 (by rfl) ⟨152057, by rfl⟩ : syracuseStep 810973 = 304115) (by norm_num)
theorem B450553 : Blo 397767 450553 := bbase (se 2 (by rfl) ⟨168957, by rfl⟩ : syracuseStep 450553 = 337915) (by norm_num)
theorem B450589 : Blo 397767 450589 := bbase (se 3 (by rfl) ⟨84485, by rfl⟩ : syracuseStep 450589 = 168971) (by norm_num)
theorem B450625 : Blo 397767 450625 := bbase (se 2 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 450625 = 337969) (by norm_num)
theorem B1138789 : Blo 397767 1138789 := bbase (se 4 (by rfl) ⟨106761, by rfl⟩ : syracuseStep 1138789 = 213523) (by norm_num)
theorem B450661 : Blo 397767 450661 := bbase (se 4 (by rfl) ⟨42249, by rfl⟩ : syracuseStep 450661 = 84499) (by norm_num)
theorem B2023541 : Blo 397767 2023541 := bbase (se 5 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 2023541 = 189707) (by norm_num)
theorem B1007741 : Blo 397767 1007741 := bbase (se 3 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 1007741 = 377903) (by norm_num)
theorem B450697 : Blo 397767 450697 := bbase (se 2 (by rfl) ⟨169011, by rfl⟩ : syracuseStep 450697 = 338023) (by norm_num)
theorem B450733 : Blo 397767 450733 := bbase (se 3 (by rfl) ⟨84512, by rfl⟩ : syracuseStep 450733 = 169025) (by norm_num)
theorem B1401013 : Blo 397767 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B450769 : Blo 397767 450769 := bbase (se 2 (by rfl) ⟨169038, by rfl⟩ : syracuseStep 450769 = 338077) (by norm_num)
theorem B450805 : Blo 397767 450805 := bbase (se 5 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 450805 = 42263) (by norm_num)
theorem B450841 : Blo 397767 450841 := bbase (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) (by norm_num)
theorem B450877 : Blo 397767 450877 := bbase (se 3 (by rfl) ⟨84539, by rfl⟩ : syracuseStep 450877 = 169079) (by norm_num)
theorem B450913 : Blo 397767 450913 := bbase (se 2 (by rfl) ⟨169092, by rfl⟩ : syracuseStep 450913 = 338185) (by norm_num)
theorem B1925477 : Blo 397767 1925477 := bbase (se 4 (by rfl) ⟨180513, by rfl⟩ : syracuseStep 1925477 = 361027) (by norm_num)
theorem B450949 : Blo 397767 450949 := bbase (se 4 (by rfl) ⟨42276, by rfl⟩ : syracuseStep 450949 = 84553) (by norm_num)
theorem B450985 : Blo 397767 450985 := bbase (se 2 (by rfl) ⟨169119, by rfl⟩ : syracuseStep 450985 = 338239) (by norm_num)
theorem B451021 : Blo 397767 451021 := bbase (se 3 (by rfl) ⟨84566, by rfl⟩ : syracuseStep 451021 = 169133) (by norm_num)
theorem B1008085 : Blo 397767 1008085 := bbase (se 7 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 1008085 = 23627) (by norm_num)
theorem B451057 : Blo 397767 451057 := bbase (se 2 (by rfl) ⟨169146, by rfl⟩ : syracuseStep 451057 = 338293) (by norm_num)
theorem B451093 : Blo 397767 451093 := bbase (se 6 (by rfl) ⟨10572, by rfl⟩ : syracuseStep 451093 = 21145) (by norm_num)
theorem B451129 : Blo 397767 451129 := bbase (se 2 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 451129 = 338347) (by norm_num)
theorem B1008197 : Blo 397767 1008197 := bbase (se 4 (by rfl) ⟨94518, by rfl⟩ : syracuseStep 1008197 = 189037) (by norm_num)
theorem B647765 : Blo 397767 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B451165 : Blo 397767 451165 := bbase (se 3 (by rfl) ⟨84593, by rfl⟩ : syracuseStep 451165 = 169187) (by norm_num)
theorem B451201 : Blo 397767 451201 := bbase (se 2 (by rfl) ⟨169200, by rfl⟩ : syracuseStep 451201 = 338401) (by norm_num)
theorem B1434245 : Blo 397767 1434245 := bbase (se 4 (by rfl) ⟨134460, by rfl⟩ : syracuseStep 1434245 = 268921) (by norm_num)
theorem B1237637 : Blo 397767 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B451237 : Blo 397767 451237 := bbase (se 4 (by rfl) ⟨42303, by rfl⟩ : syracuseStep 451237 = 84607) (by norm_num)
theorem B451273 : Blo 397767 451273 := bbase (se 2 (by rfl) ⟨169227, by rfl⟩ : syracuseStep 451273 = 338455) (by norm_num)
theorem B451309 : Blo 397767 451309 := bbase (se 3 (by rfl) ⟨84620, by rfl⟩ : syracuseStep 451309 = 169241) (by norm_num)
theorem B1008389 : Blo 397767 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B451345 : Blo 397767 451345 := bbase (se 2 (by rfl) ⟨169254, by rfl⟩ : syracuseStep 451345 = 338509) (by norm_num)
theorem B451381 : Blo 397767 451381 := bbase (se 5 (by rfl) ⟨21158, by rfl⟩ : syracuseStep 451381 = 42317) (by norm_num)
theorem B1729349 : Blo 397767 1729349 := bbase (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) (by norm_num)
theorem B451417 : Blo 397767 451417 := bbase (se 2 (by rfl) ⟨169281, by rfl⟩ : syracuseStep 451417 = 338563) (by norm_num)
theorem B451453 : Blo 397767 451453 := bbase (se 3 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 451453 = 169295) (by norm_num)
theorem B3072917 : Blo 397767 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B451489 : Blo 397767 451489 := bbase (se 2 (by rfl) ⟨169308, by rfl⟩ : syracuseStep 451489 = 338617) (by norm_num)
theorem B451525 : Blo 397767 451525 := bbase (se 4 (by rfl) ⟨42330, by rfl⟩ : syracuseStep 451525 = 84661) (by norm_num)
theorem B451561 : Blo 397767 451561 := bbase (se 2 (by rfl) ⟨169335, by rfl⟩ : syracuseStep 451561 = 338671) (by norm_num)
theorem B451597 : Blo 397767 451597 := bbase (se 3 (by rfl) ⟨84674, by rfl⟩ : syracuseStep 451597 = 169349) (by norm_num)
theorem B451633 : Blo 397767 451633 := bbase (se 2 (by rfl) ⟨169362, by rfl⟩ : syracuseStep 451633 = 338725) (by norm_num)
theorem B451669 : Blo 397767 451669 := bbase (se 8 (by rfl) ⟨2646, by rfl⟩ : syracuseStep 451669 = 5293) (by norm_num)
theorem B1008733 : Blo 397767 1008733 := bbase (se 3 (by rfl) ⟨189137, by rfl⟩ : syracuseStep 1008733 = 378275) (by norm_num)
theorem B451705 : Blo 397767 451705 := bbase (se 2 (by rfl) ⟨169389, by rfl⟩ : syracuseStep 451705 = 338779) (by norm_num)
theorem B451741 : Blo 397767 451741 := bbase (se 3 (by rfl) ⟨84701, by rfl⟩ : syracuseStep 451741 = 169403) (by norm_num)
theorem B451777 : Blo 397767 451777 := bbase (se 2 (by rfl) ⟨169416, by rfl⟩ : syracuseStep 451777 = 338833) (by norm_num)
theorem B1008845 : Blo 397767 1008845 := bbase (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) (by norm_num)
theorem B451813 : Blo 397767 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B451849 : Blo 397767 451849 := bbase (se 2 (by rfl) ⟨169443, by rfl⟩ : syracuseStep 451849 = 338887) (by norm_num)
theorem B1729829 : Blo 397767 1729829 := bbase (se 4 (by rfl) ⟨162171, by rfl⟩ : syracuseStep 1729829 = 324343) (by norm_num)
theorem B451885 : Blo 397767 451885 := bbase (se 3 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 451885 = 169457) (by norm_num)
theorem B451921 : Blo 397767 451921 := bbase (se 2 (by rfl) ⟨169470, by rfl⟩ : syracuseStep 451921 = 338941) (by norm_num)
theorem B451957 : Blo 397767 451957 := bbase (se 5 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 451957 = 42371) (by norm_num)
theorem B2024837 : Blo 397767 2024837 := bbase (se 4 (by rfl) ⟨189828, by rfl⟩ : syracuseStep 2024837 = 379657) (by norm_num)
theorem B1009037 : Blo 397767 1009037 := bbase (se 3 (by rfl) ⟨189194, by rfl⟩ : syracuseStep 1009037 = 378389) (by norm_num)
theorem B1926629 : Blo 397767 1926629 := bbase (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) (by norm_num)
theorem B1140293 : Blo 397767 1140293 := bbase (se 4 (by rfl) ⟨106902, by rfl⟩ : syracuseStep 1140293 = 213805) (by norm_num)
theorem B1009381 : Blo 397767 1009381 := bbase (se 4 (by rfl) ⟨94629, by rfl⟩ : syracuseStep 1009381 = 189259) (by norm_num)
theorem B1009493 : Blo 397767 1009493 := bbase (se 9 (by rfl) ⟨2957, by rfl⟩ : syracuseStep 1009493 = 5915) (by norm_num)
theorem B1009685 : Blo 397767 1009685 := bbase (se 6 (by rfl) ⟨23664, by rfl⟩ : syracuseStep 1009685 = 47329) (by norm_num)
theorem B911405 : Blo 397767 911405 := bbase (se 3 (by rfl) ⟨170888, by rfl⟩ : syracuseStep 911405 = 341777) (by norm_num)
theorem B485473 : Blo 397767 485473 := bbase (se 2 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 485473 = 364105) (by norm_num)
theorem B1927397 : Blo 397767 1927397 := bbase (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) (by norm_num)
theorem B1436005 : Blo 397767 1436005 := bbase (se 4 (by rfl) ⟨134625, by rfl⟩ : syracuseStep 1436005 = 269251) (by norm_num)
theorem B1010029 : Blo 397767 1010029 := bbase (se 3 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 1010029 = 378761) (by norm_num)
theorem B1075589 : Blo 397767 1075589 := bbase (se 4 (by rfl) ⟨100836, by rfl⟩ : syracuseStep 1075589 = 201673) (by norm_num)
theorem B1010141 : Blo 397767 1010141 := bbase (se 3 (by rfl) ⟨189401, by rfl⟩ : syracuseStep 1010141 = 378803) (by norm_num)
theorem B1731077 : Blo 397767 1731077 := bbase (se 4 (by rfl) ⟨162288, by rfl⟩ : syracuseStep 1731077 = 324577) (by norm_num)
theorem B2157077 : Blo 397767 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B682597 : Blo 397767 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B2026133 : Blo 397767 2026133 := bbase (se 6 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 2026133 = 94975) (by norm_num)
theorem B1010333 : Blo 397767 1010333 := bbase (se 3 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 1010333 = 378875) (by norm_num)
theorem B813901 : Blo 397767 813901 := bbase (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) (by norm_num)
theorem B813997 : Blo 397767 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B1010677 : Blo 397767 1010677 := bbase (se 5 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 1010677 = 94751) (by norm_num)
theorem B1010789 : Blo 397767 1010789 := bbase (se 4 (by rfl) ⟨94761, by rfl⟩ : syracuseStep 1010789 = 189523) (by norm_num)
theorem B1141877 : Blo 397767 1141877 := bbase (se 5 (by rfl) ⟨53525, by rfl⟩ : syracuseStep 1141877 = 107051) (by norm_num)
theorem B3075317 : Blo 397767 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B650501 : Blo 397767 650501 := bbase (se 4 (by rfl) ⟨60984, by rfl⟩ : syracuseStep 650501 = 121969) (by norm_num)
theorem B1010981 : Blo 397767 1010981 := bbase (se 4 (by rfl) ⟨94779, by rfl⟩ : syracuseStep 1010981 = 189559) (by norm_num)
theorem B1076549 : Blo 397767 1076549 := bbase (se 4 (by rfl) ⟨100926, by rfl⟩ : syracuseStep 1076549 = 201853) (by norm_num)
theorem B716149 : Blo 397767 716149 := bbase (se 5 (by rfl) ⟨33569, by rfl⟩ : syracuseStep 716149 = 67139) (by norm_num)
theorem B1371653 : Blo 397767 1371653 := bbase (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) (by norm_num)
theorem B1011325 : Blo 397767 1011325 := bbase (se 3 (by rfl) ⟨189623, by rfl⟩ : syracuseStep 1011325 = 379247) (by norm_num)
theorem B913085 : Blo 397767 913085 := bbase (se 3 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 913085 = 342407) (by norm_num)
theorem B1011437 : Blo 397767 1011437 := bbase (se 3 (by rfl) ⟨189644, by rfl⟩ : syracuseStep 1011437 = 379289) (by norm_num)
theorem B1142549 : Blo 397767 1142549 := bbase (se 6 (by rfl) ⟨26778, by rfl⟩ : syracuseStep 1142549 = 53557) (by norm_num)
theorem B782237 : Blo 397767 782237 := bbase (se 3 (by rfl) ⟨146669, by rfl⟩ : syracuseStep 782237 = 293339) (by norm_num)
theorem B2027429 : Blo 397767 2027429 := bbase (se 4 (by rfl) ⟨190071, by rfl⟩ : syracuseStep 2027429 = 380143) (by norm_num)
theorem B1011629 : Blo 397767 1011629 := bbase (se 3 (by rfl) ⟨189680, by rfl⟩ : syracuseStep 1011629 = 379361) (by norm_num)
theorem B454681 : Blo 397767 454681 := bbase (se 2 (by rfl) ⟨170505, by rfl⟩ : syracuseStep 454681 = 341011) (by norm_num)
theorem B454717 : Blo 397767 454717 := bbase (se 3 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 454717 = 170519) (by norm_num)
theorem B454753 : Blo 397767 454753 := bbase (se 2 (by rfl) ⟨170532, by rfl⟩ : syracuseStep 454753 = 341065) (by norm_num)
theorem B1142981 : Blo 397767 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B1011973 : Blo 397767 1011973 := bbase (se 4 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 1011973 = 189745) (by norm_num)
theorem B782669 : Blo 397767 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B1012085 : Blo 397767 1012085 := bbase (se 5 (by rfl) ⟨47441, by rfl⟩ : syracuseStep 1012085 = 94883) (by norm_num)
theorem B1012277 : Blo 397767 1012277 := bbase (se 5 (by rfl) ⟨47450, by rfl⟩ : syracuseStep 1012277 = 94901) (by norm_num)
theorem B1536677 : Blo 397767 1536677 := bbase (se 4 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 1536677 = 288127) (by norm_num)
theorem B717541 : Blo 397767 717541 := bbase (se 4 (by rfl) ⟨67269, by rfl⟩ : syracuseStep 717541 = 134539) (by norm_num)
theorem B1274629 : Blo 397767 1274629 := bbase (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) (by norm_num)
theorem B455557 : Blo 397767 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B1012621 : Blo 397767 1012621 := bbase (se 3 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 1012621 = 379733) (by norm_num)
theorem B1143733 : Blo 397767 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B1012733 : Blo 397767 1012733 := bbase (se 3 (by rfl) ⟨189887, by rfl⟩ : syracuseStep 1012733 = 379775) (by norm_num)
theorem B2028725 : Blo 397767 2028725 := bbase (se 5 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 2028725 = 190193) (by norm_num)
theorem B1012925 : Blo 397767 1012925 := bbase (se 3 (by rfl) ⟨189923, by rfl⟩ : syracuseStep 1012925 = 379847) (by norm_num)
theorem B3044789 : Blo 397767 3044789 := bbase (se 5 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 3044789 = 285449) (by norm_num)
theorem B1013269 : Blo 397767 1013269 := bbase (se 6 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 1013269 = 47497) (by norm_num)
theorem B1013381 : Blo 397767 1013381 := bbase (se 4 (by rfl) ⟨95004, by rfl⟩ : syracuseStep 1013381 = 190009) (by norm_num)
theorem B1013573 : Blo 397767 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B1374101 : Blo 397767 1374101 := bbase (se 6 (by rfl) ⟨32205, by rfl⟩ : syracuseStep 1374101 = 64411) (by norm_num)
theorem B718789 : Blo 397767 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B456797 : Blo 397767 456797 := bbase (se 3 (by rfl) ⟨85649, by rfl⟩ : syracuseStep 456797 = 171299) (by norm_num)
theorem B915565 : Blo 397767 915565 := bbase (se 3 (by rfl) ⟨171668, by rfl⟩ : syracuseStep 915565 = 343337) (by norm_num)
theorem B1013917 : Blo 397767 1013917 := bbase (se 3 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 1013917 = 380219) (by norm_num)
theorem B850189 : Blo 397767 850189 := bbase (se 3 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 850189 = 318821) (by norm_num)
theorem B1014029 : Blo 397767 1014029 := bbase (se 3 (by rfl) ⟨190130, by rfl⟩ : syracuseStep 1014029 = 380261) (by norm_num)
theorem B457049 : Blo 397767 457049 := bbase (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) (by norm_num)
theorem B2423189 : Blo 397767 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B850333 : Blo 397767 850333 := bbase (se 3 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 850333 = 318875) (by norm_num)
theorem B2030021 : Blo 397767 2030021 := bbase (se 4 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 2030021 = 380629) (by norm_num)
theorem B1014221 : Blo 397767 1014221 := bbase (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) (by norm_num)
theorem B10222037 : Blo 397767 10222037 := bbase (se 7 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 10222037 = 239579) (by norm_num)
theorem B2882101 : Blo 397767 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B686701 : Blo 397767 686701 := bbase (se 3 (by rfl) ⟨128756, by rfl⟩ : syracuseStep 686701 = 257513) (by norm_num)
theorem B1702565 : Blo 397767 1702565 := bbase (se 4 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 1702565 = 319231) (by norm_num)
theorem B850709 : Blo 397767 850709 := bbase (se 6 (by rfl) ⟨19938, by rfl⟩ : syracuseStep 850709 = 39877) (by norm_num)
theorem B1014565 : Blo 397767 1014565 := bbase (se 4 (by rfl) ⟨95115, by rfl⟩ : syracuseStep 1014565 = 190231) (by norm_num)
theorem B1014677 : Blo 397767 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B1702853 : Blo 397767 1702853 := bbase (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) (by norm_num)
theorem B1014869 : Blo 397767 1014869 := bbase (se 8 (by rfl) ⟨5946, by rfl⟩ : syracuseStep 1014869 = 11893) (by norm_num)
theorem B851077 : Blo 397767 851077 := bbase (se 4 (by rfl) ⟨79788, by rfl⟩ : syracuseStep 851077 = 159577) (by norm_num)
theorem B425197 : Blo 397767 425197 := bbase (se 3 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 425197 = 159449) (by norm_num)
theorem B1342709 : Blo 397767 1342709 := bbase (se 5 (by rfl) ⟨62939, by rfl⟩ : syracuseStep 1342709 = 125879) (by norm_num)
theorem B720173 : Blo 397767 720173 := bbase (se 3 (by rfl) ⟨135032, by rfl⟩ : syracuseStep 720173 = 270065) (by norm_num)
theorem B425269 : Blo 397767 425269 := bbase (se 5 (by rfl) ⟨19934, by rfl⟩ : syracuseStep 425269 = 39869) (by norm_num)
theorem B1015213 : Blo 397767 1015213 := bbase (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) (by norm_num)
theorem B425449 : Blo 397767 425449 := bbase (se 2 (by rfl) ⟨159543, by rfl⟩ : syracuseStep 425449 = 319087) (by norm_num)
theorem B1015325 : Blo 397767 1015325 := bbase (se 3 (by rfl) ⟨190373, by rfl⟩ : syracuseStep 1015325 = 380747) (by norm_num)
theorem B1343141 : Blo 397767 1343141 := bbase (se 4 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 1343141 = 251839) (by norm_num)
theorem B1703605 : Blo 397767 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B1277653 : Blo 397767 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B2031317 : Blo 397767 2031317 := bbase (se 7 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 2031317 = 47609) (by norm_num)
theorem B1015517 : Blo 397767 1015517 := bbase (se 3 (by rfl) ⟨190409, by rfl⟩ : syracuseStep 1015517 = 380819) (by norm_num)
theorem B425893 : Blo 397767 425893 := bbase (se 4 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 425893 = 79855) (by norm_num)
theorem B3243989 : Blo 397767 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B1015811 : Blo 397767 1015811 := bstep (se 1 (by rfl) ⟨761858, by rfl⟩ : syracuseStep 1015811 = 1523717) B1523717
theorem B1016003 : Blo 397767 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B1868017 : Blo 397767 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B1343789 : Blo 397767 1343789 := bstep (se 3 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 1343789 = 503921) B503921
theorem B1343843 : Blo 397767 1343843 := bstep (se 1 (by rfl) ⟨1007882, by rfl⟩ : syracuseStep 1343843 = 2015765) B2015765
theorem B2425349 : Blo 397767 2425349 := bstep (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) B454753
theorem B1278499 : Blo 397767 1278499 := bstep (se 1 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 1278499 = 1917749) B1917749
theorem B1344113 : Blo 397767 1344113 := bstep (se 2 (by rfl) ⟨504042, by rfl⟩ : syracuseStep 1344113 = 1008085) B1008085
theorem B14615153 : Blo 397767 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1868579 : Blo 397767 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1016945 : Blo 397767 1016945 := bstep (se 2 (by rfl) ⟨381354, by rfl⟩ : syracuseStep 1016945 = 762709) B762709
theorem B427123 : Blo 397767 427123 := bstep (se 1 (by rfl) ⟨320342, by rfl⟩ : syracuseStep 427123 = 640685) B640685
theorem B1344653 : Blo 397767 1344653 := bstep (se 3 (by rfl) ⟨252122, by rfl⟩ : syracuseStep 1344653 = 504245) B504245
theorem B2426033 : Blo 397767 2426033 := bstep (se 2 (by rfl) ⟨909762, by rfl⟩ : syracuseStep 2426033 = 1819525) B1819525
theorem B1344707 : Blo 397767 1344707 := bstep (se 1 (by rfl) ⟨1008530, by rfl⟩ : syracuseStep 1344707 = 2017061) B2017061
theorem B9733517 : Blo 397767 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B1148323 : Blo 397767 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B722371 : Blo 397767 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B755153 : Blo 397767 755153 := bstep (se 2 (by rfl) ⟨283182, by rfl⟩ : syracuseStep 755153 = 566365) B566365
theorem B1344977 : Blo 397767 1344977 := bstep (se 2 (by rfl) ⟨504366, by rfl⟩ : syracuseStep 1344977 = 1008733) B1008733
theorem B427555 : Blo 397767 427555 := bstep (se 1 (by rfl) ⟨320666, by rfl⟩ : syracuseStep 427555 = 641333) B641333
theorem B1279601 : Blo 397767 1279601 := bstep (se 2 (by rfl) ⟨479850, by rfl⟩ : syracuseStep 1279601 = 959701) B959701
theorem B1279729 : Blo 397767 1279729 := bstep (se 2 (by rfl) ⟨479898, by rfl⟩ : syracuseStep 1279729 = 959797) B959797
theorem B689971 : Blo 397767 689971 := bstep (se 1 (by rfl) ⟨517478, by rfl⟩ : syracuseStep 689971 = 1034957) B1034957
theorem B2033585 : Blo 397767 2033585 := bstep (se 2 (by rfl) ⟨762594, by rfl⟩ : syracuseStep 2033585 = 1525189) B1525189
theorem B1345517 : Blo 397767 1345517 := bstep (se 3 (by rfl) ⟨252284, by rfl⟩ : syracuseStep 1345517 = 504569) B504569
theorem B1705997 : Blo 397767 1705997 := bstep (se 3 (by rfl) ⟨319874, by rfl⟩ : syracuseStep 1705997 = 639749) B639749
theorem B1345571 : Blo 397767 1345571 := bstep (se 1 (by rfl) ⟨1009178, by rfl⟩ : syracuseStep 1345571 = 2018357) B2018357
theorem B1345841 : Blo 397767 1345841 := bstep (se 2 (by rfl) ⟨504690, by rfl⟩ : syracuseStep 1345841 = 1009381) B1009381
theorem B756049 : Blo 397767 756049 := bstep (se 2 (by rfl) ⟨283518, by rfl⟩ : syracuseStep 756049 = 567037) B567037
theorem B1706339 : Blo 397767 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B756209 : Blo 397767 756209 := bstep (se 2 (by rfl) ⟨283578, by rfl⟩ : syracuseStep 756209 = 567157) B567157
theorem B854563 : Blo 397767 854563 := bstep (se 1 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 854563 = 1281845) B1281845
theorem B2165381 : Blo 397767 2165381 := bstep (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) B406009
theorem B1280717 : Blo 397767 1280717 := bstep (se 3 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 1280717 = 480269) B480269
theorem B428819 : Blo 397767 428819 := bstep (se 1 (by rfl) ⟨321614, by rfl⟩ : syracuseStep 428819 = 643229) B643229
theorem B1346381 : Blo 397767 1346381 := bstep (se 3 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 1346381 = 504893) B504893
theorem B756611 : Blo 397767 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B1346435 : Blo 397767 1346435 := bstep (se 1 (by rfl) ⟨1009826, by rfl⟩ : syracuseStep 1346435 = 2019653) B2019653
theorem B494515 : Blo 397767 494515 := bstep (se 1 (by rfl) ⟨370886, by rfl⟩ : syracuseStep 494515 = 741773) B741773
theorem B1346705 : Blo 397767 1346705 := bstep (se 2 (by rfl) ⟨505014, by rfl⟩ : syracuseStep 1346705 = 1010029) B1010029
theorem B1510883 : Blo 397767 1510883 := bstep (se 1 (by rfl) ⟨1133162, by rfl⟩ : syracuseStep 1510883 = 2266325) B2266325
theorem B2362949 : Blo 397767 2362949 := bstep (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) B443053
theorem B3247685 : Blo 397767 3247685 := bstep (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) B608941
theorem B1347245 : Blo 397767 1347245 := bstep (se 3 (by rfl) ⟨252608, by rfl⟩ : syracuseStep 1347245 = 505217) B505217
theorem B1347299 : Blo 397767 1347299 := bstep (se 1 (by rfl) ⟨1010474, by rfl⟩ : syracuseStep 1347299 = 2020949) B2020949
theorem B757507 : Blo 397767 757507 := bstep (se 1 (by rfl) ⟨568130, by rfl⟩ : syracuseStep 757507 = 1136261) B1136261
theorem B1085201 : Blo 397767 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B1085329 : Blo 397767 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B757667 : Blo 397767 757667 := bstep (se 1 (by rfl) ⟨568250, by rfl⟩ : syracuseStep 757667 = 1136501) B1136501
theorem B1347569 : Blo 397767 1347569 := bstep (se 2 (by rfl) ⟨505338, by rfl⟩ : syracuseStep 1347569 = 1010677) B1010677
theorem B1282061 : Blo 397767 1282061 := bstep (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) B480773
theorem B1085795 : Blo 397767 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B856433 : Blo 397767 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B1085891 : Blo 397767 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B1511885 : Blo 397767 1511885 := bstep (se 3 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 1511885 = 566957) B566957
theorem B397779 : Blo 397767 397779 := bstep (se 1 (by rfl) ⟨298334, by rfl⟩ : syracuseStep 397779 = 596669) B596669
theorem B397795 : Blo 397767 397795 := bstep (se 1 (by rfl) ⟨298346, by rfl⟩ : syracuseStep 397795 = 596693) B596693
theorem B954865 : Blo 397767 954865 := bstep (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) B716149
theorem B397811 : Blo 397767 397811 := bstep (se 1 (by rfl) ⟨298358, by rfl⟩ : syracuseStep 397811 = 596717) B596717
theorem B397827 : Blo 397767 397827 := bstep (se 1 (by rfl) ⟨298370, by rfl⟩ : syracuseStep 397827 = 596741) B596741
theorem B1348109 : Blo 397767 1348109 := bstep (se 3 (by rfl) ⟨252770, by rfl⟩ : syracuseStep 1348109 = 505541) B505541
theorem B397843 : Blo 397767 397843 := bstep (se 1 (by rfl) ⟨298382, by rfl⟩ : syracuseStep 397843 = 596765) B596765
theorem B397859 : Blo 397767 397859 := bstep (se 1 (by rfl) ⟨298394, by rfl⟩ : syracuseStep 397859 = 596789) B596789
theorem B397875 : Blo 397767 397875 := bstep (se 1 (by rfl) ⟨298406, by rfl⟩ : syracuseStep 397875 = 596813) B596813
theorem B397891 : Blo 397767 397891 := bstep (se 1 (by rfl) ⟨298418, by rfl⟩ : syracuseStep 397891 = 596837) B596837
theorem B1348163 : Blo 397767 1348163 := bstep (se 1 (by rfl) ⟨1011122, by rfl⟩ : syracuseStep 1348163 = 2022245) B2022245
theorem B397907 : Blo 397767 397907 := bstep (se 1 (by rfl) ⟨298430, by rfl⟩ : syracuseStep 397907 = 596861) B596861
theorem B397923 : Blo 397767 397923 := bstep (se 1 (by rfl) ⟨298442, by rfl⟩ : syracuseStep 397923 = 596885) B596885
theorem B397939 : Blo 397767 397939 := bstep (se 1 (by rfl) ⟨298454, by rfl⟩ : syracuseStep 397939 = 596909) B596909
theorem B397955 : Blo 397767 397955 := bstep (se 1 (by rfl) ⟨298466, by rfl⟩ : syracuseStep 397955 = 596933) B596933
theorem B397971 : Blo 397767 397971 := bstep (se 1 (by rfl) ⟨298478, by rfl⟩ : syracuseStep 397971 = 596957) B596957
theorem B397987 : Blo 397767 397987 := bstep (se 1 (by rfl) ⟨298490, by rfl⟩ : syracuseStep 397987 = 596981) B596981
theorem B398003 : Blo 397767 398003 := bstep (se 1 (by rfl) ⟨298502, by rfl⟩ : syracuseStep 398003 = 597005) B597005
theorem B398019 : Blo 397767 398019 := bstep (se 1 (by rfl) ⟨298514, by rfl⟩ : syracuseStep 398019 = 597029) B597029
theorem B398035 : Blo 397767 398035 := bstep (se 1 (by rfl) ⟨298526, by rfl⟩ : syracuseStep 398035 = 597053) B597053
theorem B398051 : Blo 397767 398051 := bstep (se 1 (by rfl) ⟨298538, by rfl⟩ : syracuseStep 398051 = 597077) B597077
theorem B398067 : Blo 397767 398067 := bstep (se 1 (by rfl) ⟨298550, by rfl⟩ : syracuseStep 398067 = 597101) B597101
theorem B398083 : Blo 397767 398083 := bstep (se 1 (by rfl) ⟨298562, by rfl⟩ : syracuseStep 398083 = 597125) B597125
theorem B398099 : Blo 397767 398099 := bstep (se 1 (by rfl) ⟨298574, by rfl⟩ : syracuseStep 398099 = 597149) B597149
theorem B398115 : Blo 397767 398115 := bstep (se 1 (by rfl) ⟨298586, by rfl⟩ : syracuseStep 398115 = 597173) B597173
theorem B398131 : Blo 397767 398131 := bstep (se 1 (by rfl) ⟨298598, by rfl⟩ : syracuseStep 398131 = 597197) B597197
theorem B398147 : Blo 397767 398147 := bstep (se 1 (by rfl) ⟨298610, by rfl⟩ : syracuseStep 398147 = 597221) B597221
theorem B1348433 : Blo 397767 1348433 := bstep (se 2 (by rfl) ⟨505662, by rfl⟩ : syracuseStep 1348433 = 1011325) B1011325
theorem B398163 : Blo 397767 398163 := bstep (se 1 (by rfl) ⟨298622, by rfl⟩ : syracuseStep 398163 = 597245) B597245
theorem B398179 : Blo 397767 398179 := bstep (se 1 (by rfl) ⟨298634, by rfl⟩ : syracuseStep 398179 = 597269) B597269
theorem B398195 : Blo 397767 398195 := bstep (se 1 (by rfl) ⟨298646, by rfl⟩ : syracuseStep 398195 = 597293) B597293
theorem B398211 : Blo 397767 398211 := bstep (se 1 (by rfl) ⟨298658, by rfl⟩ : syracuseStep 398211 = 597317) B597317
theorem B398227 : Blo 397767 398227 := bstep (se 1 (by rfl) ⟨298670, by rfl⟩ : syracuseStep 398227 = 597341) B597341
theorem B398243 : Blo 397767 398243 := bstep (se 1 (by rfl) ⟨298682, by rfl⟩ : syracuseStep 398243 = 597365) B597365
theorem B398259 : Blo 397767 398259 := bstep (se 1 (by rfl) ⟨298694, by rfl⟩ : syracuseStep 398259 = 597389) B597389
theorem B398275 : Blo 397767 398275 := bstep (se 1 (by rfl) ⟨298706, by rfl⟩ : syracuseStep 398275 = 597413) B597413
theorem B758737 : Blo 397767 758737 := bstep (se 2 (by rfl) ⟨284526, by rfl⟩ : syracuseStep 758737 = 569053) B569053
theorem B398291 : Blo 397767 398291 := bstep (se 1 (by rfl) ⟨298718, by rfl⟩ : syracuseStep 398291 = 597437) B597437
theorem B398307 : Blo 397767 398307 := bstep (se 1 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 398307 = 597461) B597461
theorem B398323 : Blo 397767 398323 := bstep (se 1 (by rfl) ⟨298742, by rfl⟩ : syracuseStep 398323 = 597485) B597485
theorem B398339 : Blo 397767 398339 := bstep (se 1 (by rfl) ⟨298754, by rfl⟩ : syracuseStep 398339 = 597509) B597509
theorem B398355 : Blo 397767 398355 := bstep (se 1 (by rfl) ⟨298766, by rfl⟩ : syracuseStep 398355 = 597533) B597533
theorem B398371 : Blo 397767 398371 := bstep (se 1 (by rfl) ⟨298778, by rfl⟩ : syracuseStep 398371 = 597557) B597557
theorem B398387 : Blo 397767 398387 := bstep (se 1 (by rfl) ⟨298790, by rfl⟩ : syracuseStep 398387 = 597581) B597581
theorem B398403 : Blo 397767 398403 := bstep (se 1 (by rfl) ⟨298802, by rfl⟩ : syracuseStep 398403 = 597605) B597605
theorem B398419 : Blo 397767 398419 := bstep (se 1 (by rfl) ⟨298814, by rfl⟩ : syracuseStep 398419 = 597629) B597629
theorem B398435 : Blo 397767 398435 := bstep (se 1 (by rfl) ⟨298826, by rfl⟩ : syracuseStep 398435 = 597653) B597653
theorem B3839075 : Blo 397767 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B398451 : Blo 397767 398451 := bstep (se 1 (by rfl) ⟨298838, by rfl⟩ : syracuseStep 398451 = 597677) B597677
theorem B398467 : Blo 397767 398467 := bstep (se 1 (by rfl) ⟨298850, by rfl⟩ : syracuseStep 398467 = 597701) B597701
theorem B398483 : Blo 397767 398483 := bstep (se 1 (by rfl) ⟨298862, by rfl⟩ : syracuseStep 398483 = 597725) B597725
theorem B398499 : Blo 397767 398499 := bstep (se 1 (by rfl) ⟨298874, by rfl⟩ : syracuseStep 398499 = 597749) B597749
theorem B398515 : Blo 397767 398515 := bstep (se 1 (by rfl) ⟨298886, by rfl⟩ : syracuseStep 398515 = 597773) B597773
theorem B398531 : Blo 397767 398531 := bstep (se 1 (by rfl) ⟨298898, by rfl⟩ : syracuseStep 398531 = 597797) B597797
theorem B857297 : Blo 397767 857297 := bstep (se 2 (by rfl) ⟨321486, by rfl⟩ : syracuseStep 857297 = 642973) B642973
theorem B398547 : Blo 397767 398547 := bstep (se 1 (by rfl) ⟨298910, by rfl⟩ : syracuseStep 398547 = 597821) B597821
theorem B398563 : Blo 397767 398563 := bstep (se 1 (by rfl) ⟨298922, by rfl⟩ : syracuseStep 398563 = 597845) B597845
theorem B398579 : Blo 397767 398579 := bstep (se 1 (by rfl) ⟨298934, by rfl⟩ : syracuseStep 398579 = 597869) B597869
theorem B398595 : Blo 397767 398595 := bstep (se 1 (by rfl) ⟨298946, by rfl⟩ : syracuseStep 398595 = 597893) B597893
theorem B922897 : Blo 397767 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B398611 : Blo 397767 398611 := bstep (se 1 (by rfl) ⟨298958, by rfl⟩ : syracuseStep 398611 = 597917) B597917
theorem B398627 : Blo 397767 398627 := bstep (se 1 (by rfl) ⟨298970, by rfl⟩ : syracuseStep 398627 = 597941) B597941
theorem B398643 : Blo 397767 398643 := bstep (se 1 (by rfl) ⟨298982, by rfl⟩ : syracuseStep 398643 = 597965) B597965
theorem B398659 : Blo 397767 398659 := bstep (se 1 (by rfl) ⟨298994, by rfl⟩ : syracuseStep 398659 = 597989) B597989
theorem B398675 : Blo 397767 398675 := bstep (se 1 (by rfl) ⟨299006, by rfl⟩ : syracuseStep 398675 = 598013) B598013
theorem B398691 : Blo 397767 398691 := bstep (se 1 (by rfl) ⟨299018, by rfl⟩ : syracuseStep 398691 = 598037) B598037
theorem B1348973 : Blo 397767 1348973 := bstep (se 3 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 1348973 = 505865) B505865
theorem B398707 : Blo 397767 398707 := bstep (se 1 (by rfl) ⟨299030, by rfl⟩ : syracuseStep 398707 = 598061) B598061
theorem B398723 : Blo 397767 398723 := bstep (se 1 (by rfl) ⟨299042, by rfl⟩ : syracuseStep 398723 = 598085) B598085
theorem B398739 : Blo 397767 398739 := bstep (se 1 (by rfl) ⟨299054, by rfl⟩ : syracuseStep 398739 = 598109) B598109
theorem B398755 : Blo 397767 398755 := bstep (se 1 (by rfl) ⟨299066, by rfl⟩ : syracuseStep 398755 = 598133) B598133
theorem B1349027 : Blo 397767 1349027 := bstep (se 1 (by rfl) ⟨1011770, by rfl⟩ : syracuseStep 1349027 = 2023541) B2023541
theorem B398771 : Blo 397767 398771 := bstep (se 1 (by rfl) ⟨299078, by rfl⟩ : syracuseStep 398771 = 598157) B598157
theorem B398787 : Blo 397767 398787 := bstep (se 1 (by rfl) ⟨299090, by rfl⟩ : syracuseStep 398787 = 598181) B598181
theorem B398803 : Blo 397767 398803 := bstep (se 1 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 398803 = 598205) B598205
theorem B398819 : Blo 397767 398819 := bstep (se 1 (by rfl) ⟨299114, by rfl⟩ : syracuseStep 398819 = 598229) B598229
theorem B3282403 : Blo 397767 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B398835 : Blo 397767 398835 := bstep (se 1 (by rfl) ⟨299126, by rfl⟩ : syracuseStep 398835 = 598253) B598253
theorem B398851 : Blo 397767 398851 := bstep (se 1 (by rfl) ⟨299138, by rfl⟩ : syracuseStep 398851 = 598277) B598277
theorem B398867 : Blo 397767 398867 := bstep (se 1 (by rfl) ⟨299150, by rfl⟩ : syracuseStep 398867 = 598301) B598301
theorem B398883 : Blo 397767 398883 := bstep (se 1 (by rfl) ⟨299162, by rfl⟩ : syracuseStep 398883 = 598325) B598325
theorem B398899 : Blo 397767 398899 := bstep (se 1 (by rfl) ⟨299174, by rfl⟩ : syracuseStep 398899 = 598349) B598349
theorem B398915 : Blo 397767 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B1283651 : Blo 397767 1283651 := bstep (se 1 (by rfl) ⟨962738, by rfl⟩ : syracuseStep 1283651 = 1925477) B1925477
theorem B1218125 : Blo 397767 1218125 := bstep (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) B456797
theorem B398931 : Blo 397767 398931 := bstep (se 1 (by rfl) ⟨299198, by rfl⟩ : syracuseStep 398931 = 598397) B598397
theorem B398947 : Blo 397767 398947 := bstep (se 1 (by rfl) ⟨299210, by rfl⟩ : syracuseStep 398947 = 598421) B598421
theorem B398963 : Blo 397767 398963 := bstep (se 1 (by rfl) ⟨299222, by rfl⟩ : syracuseStep 398963 = 598445) B598445
theorem B398979 : Blo 397767 398979 := bstep (se 1 (by rfl) ⟨299234, by rfl⟩ : syracuseStep 398979 = 598469) B598469
theorem B398995 : Blo 397767 398995 := bstep (se 1 (by rfl) ⟨299246, by rfl⟩ : syracuseStep 398995 = 598493) B598493
theorem B399011 : Blo 397767 399011 := bstep (se 1 (by rfl) ⟨299258, by rfl⟩ : syracuseStep 399011 = 598517) B598517
theorem B1349297 : Blo 397767 1349297 := bstep (se 2 (by rfl) ⟨505986, by rfl⟩ : syracuseStep 1349297 = 1011973) B1011973
theorem B399027 : Blo 397767 399027 := bstep (se 1 (by rfl) ⟨299270, by rfl⟩ : syracuseStep 399027 = 598541) B598541
theorem B399043 : Blo 397767 399043 := bstep (se 1 (by rfl) ⟨299282, by rfl⟩ : syracuseStep 399043 = 598565) B598565
theorem B399059 : Blo 397767 399059 := bstep (se 1 (by rfl) ⟨299294, by rfl⟩ : syracuseStep 399059 = 598589) B598589
theorem B431843 : Blo 397767 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B399075 : Blo 397767 399075 := bstep (se 1 (by rfl) ⟨299306, by rfl⟩ : syracuseStep 399075 = 598613) B598613
theorem B399091 : Blo 397767 399091 := bstep (se 1 (by rfl) ⟨299318, by rfl⟩ : syracuseStep 399091 = 598637) B598637
theorem B399107 : Blo 397767 399107 := bstep (se 1 (by rfl) ⟨299330, by rfl⟩ : syracuseStep 399107 = 598661) B598661
theorem B399123 : Blo 397767 399123 := bstep (se 1 (by rfl) ⟨299342, by rfl⟩ : syracuseStep 399123 = 598685) B598685
theorem B399139 : Blo 397767 399139 := bstep (se 1 (by rfl) ⟨299354, by rfl⟩ : syracuseStep 399139 = 598709) B598709
theorem B399155 : Blo 397767 399155 := bstep (se 1 (by rfl) ⟨299366, by rfl⟩ : syracuseStep 399155 = 598733) B598733
theorem B399171 : Blo 397767 399171 := bstep (se 1 (by rfl) ⟨299378, by rfl⟩ : syracuseStep 399171 = 598757) B598757
theorem B399187 : Blo 397767 399187 := bstep (se 1 (by rfl) ⟨299390, by rfl⟩ : syracuseStep 399187 = 598781) B598781
theorem B399203 : Blo 397767 399203 := bstep (se 1 (by rfl) ⟨299402, by rfl⟩ : syracuseStep 399203 = 598805) B598805
theorem B399219 : Blo 397767 399219 := bstep (se 1 (by rfl) ⟨299414, by rfl⟩ : syracuseStep 399219 = 598829) B598829
theorem B399235 : Blo 397767 399235 := bstep (se 1 (by rfl) ⟨299426, by rfl⟩ : syracuseStep 399235 = 598853) B598853
theorem B1152899 : Blo 397767 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B399251 : Blo 397767 399251 := bstep (se 1 (by rfl) ⟨299438, by rfl⟩ : syracuseStep 399251 = 598877) B598877
theorem B399267 : Blo 397767 399267 := bstep (se 1 (by rfl) ⟨299450, by rfl⟩ : syracuseStep 399267 = 598901) B598901
theorem B2561969 : Blo 397767 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B399283 : Blo 397767 399283 := bstep (se 1 (by rfl) ⟨299462, by rfl⟩ : syracuseStep 399283 = 598925) B598925
theorem B399299 : Blo 397767 399299 := bstep (se 1 (by rfl) ⟨299474, by rfl⟩ : syracuseStep 399299 = 598949) B598949
theorem B1447885 : Blo 397767 1447885 := bstep (se 3 (by rfl) ⟨271478, by rfl⟩ : syracuseStep 1447885 = 542957) B542957
theorem B399315 : Blo 397767 399315 := bstep (se 1 (by rfl) ⟨299486, by rfl⟩ : syracuseStep 399315 = 598973) B598973
theorem B399331 : Blo 397767 399331 := bstep (se 1 (by rfl) ⟨299498, by rfl⟩ : syracuseStep 399331 = 598997) B598997
theorem B759793 : Blo 397767 759793 := bstep (se 2 (by rfl) ⟨284922, by rfl⟩ : syracuseStep 759793 = 569845) B569845
theorem B399347 : Blo 397767 399347 := bstep (se 1 (by rfl) ⟨299510, by rfl⟩ : syracuseStep 399347 = 599021) B599021
theorem B399363 : Blo 397767 399363 := bstep (se 1 (by rfl) ⟨299522, by rfl⟩ : syracuseStep 399363 = 599045) B599045
theorem B399379 : Blo 397767 399379 := bstep (se 1 (by rfl) ⟨299534, by rfl⟩ : syracuseStep 399379 = 599069) B599069
theorem B399395 : Blo 397767 399395 := bstep (se 1 (by rfl) ⟨299546, by rfl⟩ : syracuseStep 399395 = 599093) B599093
theorem B399411 : Blo 397767 399411 := bstep (se 1 (by rfl) ⟨299558, by rfl⟩ : syracuseStep 399411 = 599117) B599117
theorem B399427 : Blo 397767 399427 := bstep (se 1 (by rfl) ⟨299570, by rfl⟩ : syracuseStep 399427 = 599141) B599141
theorem B399443 : Blo 397767 399443 := bstep (se 1 (by rfl) ⟨299582, by rfl⟩ : syracuseStep 399443 = 599165) B599165
theorem B399459 : Blo 397767 399459 := bstep (se 1 (by rfl) ⟨299594, by rfl⟩ : syracuseStep 399459 = 599189) B599189
theorem B399475 : Blo 397767 399475 := bstep (se 1 (by rfl) ⟨299606, by rfl⟩ : syracuseStep 399475 = 599213) B599213
theorem B399491 : Blo 397767 399491 := bstep (se 1 (by rfl) ⟨299618, by rfl⟩ : syracuseStep 399491 = 599237) B599237
theorem B399507 : Blo 397767 399507 := bstep (se 1 (by rfl) ⟨299630, by rfl⟩ : syracuseStep 399507 = 599261) B599261
theorem B399523 : Blo 397767 399523 := bstep (se 1 (by rfl) ⟨299642, by rfl⟩ : syracuseStep 399523 = 599285) B599285
theorem B1022129 : Blo 397767 1022129 := bstep (se 2 (by rfl) ⟨383298, by rfl⟩ : syracuseStep 1022129 = 766597) B766597
theorem B399539 : Blo 397767 399539 := bstep (se 1 (by rfl) ⟨299654, by rfl⟩ : syracuseStep 399539 = 599309) B599309
theorem B1153219 : Blo 397767 1153219 := bstep (se 1 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 1153219 = 1729829) B1729829
theorem B399555 : Blo 397767 399555 := bstep (se 1 (by rfl) ⟨299666, by rfl⟩ : syracuseStep 399555 = 599333) B599333
theorem B1349837 : Blo 397767 1349837 := bstep (se 3 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 1349837 = 506189) B506189
theorem B399571 : Blo 397767 399571 := bstep (se 1 (by rfl) ⟨299678, by rfl⟩ : syracuseStep 399571 = 599357) B599357
theorem B399587 : Blo 397767 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B1218797 : Blo 397767 1218797 := bstep (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) B457049
theorem B399603 : Blo 397767 399603 := bstep (se 1 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 399603 = 599405) B599405
theorem B399619 : Blo 397767 399619 := bstep (se 1 (by rfl) ⟨299714, by rfl⟩ : syracuseStep 399619 = 599429) B599429
theorem B1349891 : Blo 397767 1349891 := bstep (se 1 (by rfl) ⟨1012418, by rfl⟩ : syracuseStep 1349891 = 2024837) B2024837
theorem B399635 : Blo 397767 399635 := bstep (se 1 (by rfl) ⟨299726, by rfl⟩ : syracuseStep 399635 = 599453) B599453
theorem B399651 : Blo 397767 399651 := bstep (se 1 (by rfl) ⟨299738, by rfl⟩ : syracuseStep 399651 = 599477) B599477
theorem B1710371 : Blo 397767 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B399667 : Blo 397767 399667 := bstep (se 1 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 399667 = 599501) B599501
theorem B399683 : Blo 397767 399683 := bstep (se 1 (by rfl) ⟨299762, by rfl⟩ : syracuseStep 399683 = 599525) B599525
theorem B1284419 : Blo 397767 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B399699 : Blo 397767 399699 := bstep (se 1 (by rfl) ⟨299774, by rfl⟩ : syracuseStep 399699 = 599549) B599549
theorem B399715 : Blo 397767 399715 := bstep (se 1 (by rfl) ⟨299786, by rfl⟩ : syracuseStep 399715 = 599573) B599573
theorem B399731 : Blo 397767 399731 := bstep (se 1 (by rfl) ⟨299798, by rfl⟩ : syracuseStep 399731 = 599597) B599597
theorem B399747 : Blo 397767 399747 := bstep (se 1 (by rfl) ⟨299810, by rfl⟩ : syracuseStep 399747 = 599621) B599621
theorem B760195 : Blo 397767 760195 := bstep (se 1 (by rfl) ⟨570146, by rfl⟩ : syracuseStep 760195 = 1140293) B1140293
theorem B399763 : Blo 397767 399763 := bstep (se 1 (by rfl) ⟨299822, by rfl⟩ : syracuseStep 399763 = 599645) B599645
theorem B399779 : Blo 397767 399779 := bstep (se 1 (by rfl) ⟨299834, by rfl⟩ : syracuseStep 399779 = 599669) B599669
theorem B760241 : Blo 397767 760241 := bstep (se 2 (by rfl) ⟨285090, by rfl⟩ : syracuseStep 760241 = 570181) B570181
theorem B399795 : Blo 397767 399795 := bstep (se 1 (by rfl) ⟨299846, by rfl⟩ : syracuseStep 399795 = 599693) B599693
theorem B399811 : Blo 397767 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B399827 : Blo 397767 399827 := bstep (se 1 (by rfl) ⟨299870, by rfl⟩ : syracuseStep 399827 = 599741) B599741
theorem B399843 : Blo 397767 399843 := bstep (se 1 (by rfl) ⟨299882, by rfl⟩ : syracuseStep 399843 = 599765) B599765
theorem B399859 : Blo 397767 399859 := bstep (se 1 (by rfl) ⟨299894, by rfl⟩ : syracuseStep 399859 = 599789) B599789
theorem B399875 : Blo 397767 399875 := bstep (se 1 (by rfl) ⟨299906, by rfl⟩ : syracuseStep 399875 = 599813) B599813
theorem B1513997 : Blo 397767 1513997 := bstep (se 3 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 1513997 = 567749) B567749
theorem B1350161 : Blo 397767 1350161 := bstep (se 2 (by rfl) ⟨506310, by rfl⟩ : syracuseStep 1350161 = 1012621) B1012621
theorem B399891 : Blo 397767 399891 := bstep (se 1 (by rfl) ⟨299918, by rfl⟩ : syracuseStep 399891 = 599837) B599837
theorem B399907 : Blo 397767 399907 := bstep (se 1 (by rfl) ⟨299930, by rfl⟩ : syracuseStep 399907 = 599861) B599861
theorem B399923 : Blo 397767 399923 := bstep (se 1 (by rfl) ⟨299942, by rfl⟩ : syracuseStep 399923 = 599885) B599885
theorem B399939 : Blo 397767 399939 := bstep (se 1 (by rfl) ⟨299954, by rfl⟩ : syracuseStep 399939 = 599909) B599909
theorem B399955 : Blo 397767 399955 := bstep (se 1 (by rfl) ⟨299966, by rfl⟩ : syracuseStep 399955 = 599933) B599933
theorem B399971 : Blo 397767 399971 := bstep (se 1 (by rfl) ⟨299978, by rfl⟩ : syracuseStep 399971 = 599957) B599957
theorem B399987 : Blo 397767 399987 := bstep (se 1 (by rfl) ⟨299990, by rfl⟩ : syracuseStep 399987 = 599981) B599981
theorem B400003 : Blo 397767 400003 := bstep (se 1 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 400003 = 600005) B600005
theorem B400019 : Blo 397767 400019 := bstep (se 1 (by rfl) ⟨300014, by rfl⟩ : syracuseStep 400019 = 600029) B600029
theorem B400035 : Blo 397767 400035 := bstep (se 1 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 400035 = 600053) B600053
theorem B596657 : Blo 397767 596657 := bstep (se 2 (by rfl) ⟨223746, by rfl⟩ : syracuseStep 596657 = 447493) B447493
theorem B400051 : Blo 397767 400051 := bstep (se 1 (by rfl) ⟨300038, by rfl⟩ : syracuseStep 400051 = 600077) B600077
theorem B596675 : Blo 397767 596675 := bstep (se 1 (by rfl) ⟨447506, by rfl⟩ : syracuseStep 596675 = 895013) B895013
theorem B400067 : Blo 397767 400067 := bstep (se 1 (by rfl) ⟨300050, by rfl⟩ : syracuseStep 400067 = 600101) B600101
theorem B760529 : Blo 397767 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B1284817 : Blo 397767 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B400083 : Blo 397767 400083 := bstep (se 1 (by rfl) ⟨300062, by rfl⟩ : syracuseStep 400083 = 600125) B600125
theorem B596705 : Blo 397767 596705 := bstep (se 2 (by rfl) ⟨223764, by rfl⟩ : syracuseStep 596705 = 447529) B447529
theorem B400099 : Blo 397767 400099 := bstep (se 1 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 400099 = 600149) B600149
theorem B596723 : Blo 397767 596723 := bstep (se 1 (by rfl) ⟨447542, by rfl⟩ : syracuseStep 596723 = 895085) B895085
theorem B400115 : Blo 397767 400115 := bstep (se 1 (by rfl) ⟨300086, by rfl⟩ : syracuseStep 400115 = 600173) B600173
theorem B400131 : Blo 397767 400131 := bstep (se 1 (by rfl) ⟨300098, by rfl⟩ : syracuseStep 400131 = 600197) B600197
theorem B3414797 : Blo 397767 3414797 := bstep (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) B1280549
theorem B596753 : Blo 397767 596753 := bstep (se 2 (by rfl) ⟨223782, by rfl⟩ : syracuseStep 596753 = 447565) B447565
theorem B400147 : Blo 397767 400147 := bstep (se 1 (by rfl) ⟨300110, by rfl⟩ : syracuseStep 400147 = 600221) B600221
theorem B596771 : Blo 397767 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B400163 : Blo 397767 400163 := bstep (se 1 (by rfl) ⟨300122, by rfl⟩ : syracuseStep 400163 = 600245) B600245
theorem B400179 : Blo 397767 400179 := bstep (se 1 (by rfl) ⟨300134, by rfl⟩ : syracuseStep 400179 = 600269) B600269
theorem B596801 : Blo 397767 596801 := bstep (se 2 (by rfl) ⟨223800, by rfl⟩ : syracuseStep 596801 = 447601) B447601
theorem B400195 : Blo 397767 400195 := bstep (se 1 (by rfl) ⟨300146, by rfl⟩ : syracuseStep 400195 = 600293) B600293
theorem B1284931 : Blo 397767 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B596819 : Blo 397767 596819 := bstep (se 1 (by rfl) ⟨447614, by rfl⟩ : syracuseStep 596819 = 895229) B895229
theorem B400211 : Blo 397767 400211 := bstep (se 1 (by rfl) ⟨300158, by rfl⟩ : syracuseStep 400211 = 600317) B600317
theorem B400227 : Blo 397767 400227 := bstep (se 1 (by rfl) ⟨300170, by rfl⟩ : syracuseStep 400227 = 600341) B600341
theorem B596849 : Blo 397767 596849 := bstep (se 2 (by rfl) ⟨223818, by rfl⟩ : syracuseStep 596849 = 447637) B447637
theorem B400243 : Blo 397767 400243 := bstep (se 1 (by rfl) ⟨300182, by rfl⟩ : syracuseStep 400243 = 600365) B600365
theorem B596867 : Blo 397767 596867 := bstep (se 1 (by rfl) ⟨447650, by rfl⟩ : syracuseStep 596867 = 895301) B895301
theorem B400259 : Blo 397767 400259 := bstep (se 1 (by rfl) ⟨300194, by rfl⟩ : syracuseStep 400259 = 600389) B600389
theorem B400275 : Blo 397767 400275 := bstep (se 1 (by rfl) ⟨300206, by rfl⟩ : syracuseStep 400275 = 600413) B600413
theorem B596897 : Blo 397767 596897 := bstep (se 2 (by rfl) ⟨223836, by rfl⟩ : syracuseStep 596897 = 447673) B447673
theorem B400291 : Blo 397767 400291 := bstep (se 1 (by rfl) ⟨300218, by rfl⟩ : syracuseStep 400291 = 600437) B600437
theorem B596915 : Blo 397767 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B400307 : Blo 397767 400307 := bstep (se 1 (by rfl) ⟨300230, by rfl⟩ : syracuseStep 400307 = 600461) B600461
theorem B400323 : Blo 397767 400323 := bstep (se 1 (by rfl) ⟨300242, by rfl⟩ : syracuseStep 400323 = 600485) B600485
theorem B2268101 : Blo 397767 2268101 := bstep (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) B425269
theorem B596945 : Blo 397767 596945 := bstep (se 2 (by rfl) ⟨223854, by rfl⟩ : syracuseStep 596945 = 447709) B447709
theorem B400339 : Blo 397767 400339 := bstep (se 1 (by rfl) ⟨300254, by rfl⟩ : syracuseStep 400339 = 600509) B600509
theorem B596963 : Blo 397767 596963 := bstep (se 1 (by rfl) ⟨447722, by rfl⟩ : syracuseStep 596963 = 895445) B895445
theorem B400355 : Blo 397767 400355 := bstep (se 1 (by rfl) ⟨300266, by rfl⟩ : syracuseStep 400355 = 600533) B600533
theorem B400371 : Blo 397767 400371 := bstep (se 1 (by rfl) ⟨300278, by rfl⟩ : syracuseStep 400371 = 600557) B600557
theorem B596993 : Blo 397767 596993 := bstep (se 2 (by rfl) ⟨223872, by rfl⟩ : syracuseStep 596993 = 447745) B447745
theorem B1154051 : Blo 397767 1154051 := bstep (se 1 (by rfl) ⟨865538, by rfl⟩ : syracuseStep 1154051 = 1731077) B1731077
theorem B400387 : Blo 397767 400387 := bstep (se 1 (by rfl) ⟨300290, by rfl⟩ : syracuseStep 400387 = 600581) B600581
theorem B597011 : Blo 397767 597011 := bstep (se 1 (by rfl) ⟨447758, by rfl⟩ : syracuseStep 597011 = 895517) B895517
theorem B400403 : Blo 397767 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B400419 : Blo 397767 400419 := bstep (se 1 (by rfl) ⟨300314, by rfl⟩ : syracuseStep 400419 = 600629) B600629
theorem B1350701 : Blo 397767 1350701 := bstep (se 3 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 1350701 = 506513) B506513
theorem B597041 : Blo 397767 597041 := bstep (se 2 (by rfl) ⟨223890, by rfl⟩ : syracuseStep 597041 = 447781) B447781
theorem B400435 : Blo 397767 400435 := bstep (se 1 (by rfl) ⟨300326, by rfl⟩ : syracuseStep 400435 = 600653) B600653
theorem B597059 : Blo 397767 597059 := bstep (se 1 (by rfl) ⟨447794, by rfl⟩ : syracuseStep 597059 = 895589) B895589
theorem B728131 : Blo 397767 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B400451 : Blo 397767 400451 := bstep (se 1 (by rfl) ⟨300338, by rfl⟩ : syracuseStep 400451 = 600677) B600677
theorem B400467 : Blo 397767 400467 := bstep (se 1 (by rfl) ⟨300350, by rfl⟩ : syracuseStep 400467 = 600701) B600701
theorem B597089 : Blo 397767 597089 := bstep (se 2 (by rfl) ⟨223908, by rfl⟩ : syracuseStep 597089 = 447817) B447817
theorem B1350755 : Blo 397767 1350755 := bstep (se 1 (by rfl) ⟨1013066, by rfl⟩ : syracuseStep 1350755 = 2026133) B2026133
theorem B400483 : Blo 397767 400483 := bstep (se 1 (by rfl) ⟨300362, by rfl⟩ : syracuseStep 400483 = 600725) B600725
theorem B2890865 : Blo 397767 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B597107 : Blo 397767 597107 := bstep (se 1 (by rfl) ⟨447830, by rfl⟩ : syracuseStep 597107 = 895661) B895661
theorem B400499 : Blo 397767 400499 := bstep (se 1 (by rfl) ⟨300374, by rfl⟩ : syracuseStep 400499 = 600749) B600749
theorem B400515 : Blo 397767 400515 := bstep (se 1 (by rfl) ⟨300386, by rfl⟩ : syracuseStep 400515 = 600773) B600773
theorem B597137 : Blo 397767 597137 := bstep (se 2 (by rfl) ⟨223926, by rfl⟩ : syracuseStep 597137 = 447853) B447853
theorem B400531 : Blo 397767 400531 := bstep (se 1 (by rfl) ⟨300398, by rfl⟩ : syracuseStep 400531 = 600797) B600797
theorem B597155 : Blo 397767 597155 := bstep (se 1 (by rfl) ⟨447866, by rfl⟩ : syracuseStep 597155 = 895733) B895733
theorem B400547 : Blo 397767 400547 := bstep (se 1 (by rfl) ⟨300410, by rfl⟩ : syracuseStep 400547 = 600821) B600821
theorem B400563 : Blo 397767 400563 := bstep (se 1 (by rfl) ⟨300422, by rfl⟩ : syracuseStep 400563 = 600845) B600845
theorem B597185 : Blo 397767 597185 := bstep (se 2 (by rfl) ⟨223944, by rfl⟩ : syracuseStep 597185 = 447889) B447889
theorem B400579 : Blo 397767 400579 := bstep (se 1 (by rfl) ⟨300434, by rfl⟩ : syracuseStep 400579 = 600869) B600869
theorem B597203 : Blo 397767 597203 := bstep (se 1 (by rfl) ⟨447902, by rfl⟩ : syracuseStep 597203 = 895805) B895805
theorem B400595 : Blo 397767 400595 := bstep (se 1 (by rfl) ⟨300446, by rfl⟩ : syracuseStep 400595 = 600893) B600893
theorem B400611 : Blo 397767 400611 := bstep (se 1 (by rfl) ⟨300458, by rfl⟩ : syracuseStep 400611 = 600917) B600917
theorem B597233 : Blo 397767 597233 := bstep (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) B447925
theorem B400627 : Blo 397767 400627 := bstep (se 1 (by rfl) ⟨300470, by rfl⟩ : syracuseStep 400627 = 600941) B600941
theorem B597251 : Blo 397767 597251 := bstep (se 1 (by rfl) ⟨447938, by rfl⟩ : syracuseStep 597251 = 895877) B895877
theorem B400643 : Blo 397767 400643 := bstep (se 1 (by rfl) ⟨300482, by rfl⟩ : syracuseStep 400643 = 600965) B600965
theorem B400659 : Blo 397767 400659 := bstep (se 1 (by rfl) ⟨300494, by rfl⟩ : syracuseStep 400659 = 600989) B600989
theorem B597281 : Blo 397767 597281 := bstep (se 2 (by rfl) ⟨223980, by rfl⟩ : syracuseStep 597281 = 447961) B447961
theorem B400675 : Blo 397767 400675 := bstep (se 1 (by rfl) ⟨300506, by rfl⟩ : syracuseStep 400675 = 601013) B601013
theorem B1514801 : Blo 397767 1514801 := bstep (se 2 (by rfl) ⟨568050, by rfl⟩ : syracuseStep 1514801 = 1136101) B1136101
theorem B597299 : Blo 397767 597299 := bstep (se 1 (by rfl) ⟨447974, by rfl⟩ : syracuseStep 597299 = 895949) B895949
theorem B400691 : Blo 397767 400691 := bstep (se 1 (by rfl) ⟨300518, by rfl⟩ : syracuseStep 400691 = 601037) B601037
theorem B400707 : Blo 397767 400707 := bstep (se 1 (by rfl) ⟨300530, by rfl⟩ : syracuseStep 400707 = 601061) B601061
theorem B597329 : Blo 397767 597329 := bstep (se 2 (by rfl) ⟨223998, by rfl⟩ : syracuseStep 597329 = 447997) B447997
theorem B400723 : Blo 397767 400723 := bstep (se 1 (by rfl) ⟨300542, by rfl⟩ : syracuseStep 400723 = 601085) B601085
theorem B597347 : Blo 397767 597347 := bstep (se 1 (by rfl) ⟨448010, by rfl⟩ : syracuseStep 597347 = 896021) B896021
theorem B400739 : Blo 397767 400739 := bstep (se 1 (by rfl) ⟨300554, by rfl⟩ : syracuseStep 400739 = 601109) B601109
theorem B1351025 : Blo 397767 1351025 := bstep (se 2 (by rfl) ⟨506634, by rfl⟩ : syracuseStep 1351025 = 1013269) B1013269
theorem B400755 : Blo 397767 400755 := bstep (se 1 (by rfl) ⟨300566, by rfl⟩ : syracuseStep 400755 = 601133) B601133
theorem B597377 : Blo 397767 597377 := bstep (se 2 (by rfl) ⟨224016, by rfl⟩ : syracuseStep 597377 = 448033) B448033
theorem B400771 : Blo 397767 400771 := bstep (se 1 (by rfl) ⟨300578, by rfl⟩ : syracuseStep 400771 = 601157) B601157
theorem B2268557 : Blo 397767 2268557 := bstep (se 3 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 2268557 = 850709) B850709
theorem B597395 : Blo 397767 597395 := bstep (se 1 (by rfl) ⟨448046, by rfl⟩ : syracuseStep 597395 = 896093) B896093
theorem B400787 : Blo 397767 400787 := bstep (se 1 (by rfl) ⟨300590, by rfl⟩ : syracuseStep 400787 = 601181) B601181
theorem B400803 : Blo 397767 400803 := bstep (se 1 (by rfl) ⟨300602, by rfl⟩ : syracuseStep 400803 = 601205) B601205
theorem B761251 : Blo 397767 761251 := bstep (se 1 (by rfl) ⟨570938, by rfl⟩ : syracuseStep 761251 = 1141877) B1141877
theorem B597425 : Blo 397767 597425 := bstep (se 2 (by rfl) ⟨224034, by rfl⟩ : syracuseStep 597425 = 448069) B448069
theorem B400819 : Blo 397767 400819 := bstep (se 1 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 400819 = 601229) B601229
theorem B597443 : Blo 397767 597443 := bstep (se 1 (by rfl) ⟨448082, by rfl⟩ : syracuseStep 597443 = 896165) B896165
theorem B400835 : Blo 397767 400835 := bstep (se 1 (by rfl) ⟨300626, by rfl⟩ : syracuseStep 400835 = 601253) B601253
theorem B400851 : Blo 397767 400851 := bstep (se 1 (by rfl) ⟨300638, by rfl⟩ : syracuseStep 400851 = 601277) B601277
theorem B597473 : Blo 397767 597473 := bstep (se 2 (by rfl) ⟨224052, by rfl⟩ : syracuseStep 597473 = 448105) B448105
theorem B400867 : Blo 397767 400867 := bstep (se 1 (by rfl) ⟨300650, by rfl⟩ : syracuseStep 400867 = 601301) B601301
theorem B1711601 : Blo 397767 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B597491 : Blo 397767 597491 := bstep (se 1 (by rfl) ⟨448118, by rfl⟩ : syracuseStep 597491 = 896237) B896237
theorem B400883 : Blo 397767 400883 := bstep (se 1 (by rfl) ⟨300662, by rfl⟩ : syracuseStep 400883 = 601325) B601325
theorem B433667 : Blo 397767 433667 := bstep (se 1 (by rfl) ⟨325250, by rfl⟩ : syracuseStep 433667 = 650501) B650501
theorem B400899 : Blo 397767 400899 := bstep (se 1 (by rfl) ⟨300674, by rfl⟩ : syracuseStep 400899 = 601349) B601349
theorem B597521 : Blo 397767 597521 := bstep (se 2 (by rfl) ⟨224070, by rfl⟩ : syracuseStep 597521 = 448141) B448141
theorem B1285649 : Blo 397767 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B400915 : Blo 397767 400915 := bstep (se 1 (by rfl) ⟨300686, by rfl⟩ : syracuseStep 400915 = 601373) B601373
theorem B597539 : Blo 397767 597539 := bstep (se 1 (by rfl) ⟨448154, by rfl⟩ : syracuseStep 597539 = 896309) B896309
theorem B400931 : Blo 397767 400931 := bstep (se 1 (by rfl) ⟨300698, by rfl⟩ : syracuseStep 400931 = 601397) B601397
theorem B400947 : Blo 397767 400947 := bstep (se 1 (by rfl) ⟨300710, by rfl⟩ : syracuseStep 400947 = 601421) B601421
theorem B597569 : Blo 397767 597569 := bstep (se 2 (by rfl) ⟨224088, by rfl⟩ : syracuseStep 597569 = 448177) B448177
theorem B400963 : Blo 397767 400963 := bstep (se 1 (by rfl) ⟨300722, by rfl⟩ : syracuseStep 400963 = 601445) B601445
theorem B597587 : Blo 397767 597587 := bstep (se 1 (by rfl) ⟨448190, by rfl⟩ : syracuseStep 597587 = 896381) B896381
theorem B400979 : Blo 397767 400979 := bstep (se 1 (by rfl) ⟨300734, by rfl⟩ : syracuseStep 400979 = 601469) B601469
theorem B400995 : Blo 397767 400995 := bstep (se 1 (by rfl) ⟨300746, by rfl⟩ : syracuseStep 400995 = 601493) B601493
theorem B597617 : Blo 397767 597617 := bstep (se 2 (by rfl) ⟨224106, by rfl⟩ : syracuseStep 597617 = 448213) B448213
theorem B401011 : Blo 397767 401011 := bstep (se 1 (by rfl) ⟨300758, by rfl⟩ : syracuseStep 401011 = 601517) B601517
theorem B597635 : Blo 397767 597635 := bstep (se 1 (by rfl) ⟨448226, by rfl⟩ : syracuseStep 597635 = 896453) B896453
theorem B401027 : Blo 397767 401027 := bstep (se 1 (by rfl) ⟨300770, by rfl⟩ : syracuseStep 401027 = 601541) B601541
theorem B401043 : Blo 397767 401043 := bstep (se 1 (by rfl) ⟨300782, by rfl⟩ : syracuseStep 401043 = 601565) B601565
theorem B597665 : Blo 397767 597665 := bstep (se 2 (by rfl) ⟨224124, by rfl⟩ : syracuseStep 597665 = 448249) B448249
theorem B401059 : Blo 397767 401059 := bstep (se 1 (by rfl) ⟨300794, by rfl⟩ : syracuseStep 401059 = 601589) B601589
theorem B597683 : Blo 397767 597683 := bstep (se 1 (by rfl) ⟨448262, by rfl⟩ : syracuseStep 597683 = 896525) B896525
theorem B401075 : Blo 397767 401075 := bstep (se 1 (by rfl) ⟨300806, by rfl⟩ : syracuseStep 401075 = 601613) B601613
theorem B401091 : Blo 397767 401091 := bstep (se 1 (by rfl) ⟨300818, by rfl⟩ : syracuseStep 401091 = 601637) B601637
theorem B597713 : Blo 397767 597713 := bstep (se 2 (by rfl) ⟨224142, by rfl⟩ : syracuseStep 597713 = 448285) B448285
theorem B401107 : Blo 397767 401107 := bstep (se 1 (by rfl) ⟨300830, by rfl⟩ : syracuseStep 401107 = 601661) B601661
theorem B597731 : Blo 397767 597731 := bstep (se 1 (by rfl) ⟨448298, by rfl⟩ : syracuseStep 597731 = 896597) B896597
theorem B7282403 : Blo 397767 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B401123 : Blo 397767 401123 := bstep (se 1 (by rfl) ⟨300842, by rfl⟩ : syracuseStep 401123 = 601685) B601685
theorem B401139 : Blo 397767 401139 := bstep (se 1 (by rfl) ⟨300854, by rfl⟩ : syracuseStep 401139 = 601709) B601709
theorem B597761 : Blo 397767 597761 := bstep (se 2 (by rfl) ⟨224160, by rfl⟩ : syracuseStep 597761 = 448321) B448321
theorem B401155 : Blo 397767 401155 := bstep (se 1 (by rfl) ⟨300866, by rfl⟩ : syracuseStep 401155 = 601733) B601733
theorem B597779 : Blo 397767 597779 := bstep (se 1 (by rfl) ⟨448334, by rfl⟩ : syracuseStep 597779 = 896669) B896669
theorem B401171 : Blo 397767 401171 := bstep (se 1 (by rfl) ⟨300878, by rfl⟩ : syracuseStep 401171 = 601757) B601757
theorem B401187 : Blo 397767 401187 := bstep (se 1 (by rfl) ⟨300890, by rfl⟩ : syracuseStep 401187 = 601781) B601781
theorem B597809 : Blo 397767 597809 := bstep (se 2 (by rfl) ⟨224178, by rfl⟩ : syracuseStep 597809 = 448357) B448357
theorem B401203 : Blo 397767 401203 := bstep (se 1 (by rfl) ⟨300902, by rfl⟩ : syracuseStep 401203 = 601805) B601805
theorem B597827 : Blo 397767 597827 := bstep (se 1 (by rfl) ⟨448370, by rfl⟩ : syracuseStep 597827 = 896741) B896741
theorem B401219 : Blo 397767 401219 := bstep (se 1 (by rfl) ⟨300914, by rfl⟩ : syracuseStep 401219 = 601829) B601829
theorem B401235 : Blo 397767 401235 := bstep (se 1 (by rfl) ⟨300926, by rfl⟩ : syracuseStep 401235 = 601853) B601853
theorem B597857 : Blo 397767 597857 := bstep (se 2 (by rfl) ⟨224196, by rfl⟩ : syracuseStep 597857 = 448393) B448393
theorem B761699 : Blo 397767 761699 := bstep (se 1 (by rfl) ⟨571274, by rfl⟩ : syracuseStep 761699 = 1142549) B1142549
theorem B401251 : Blo 397767 401251 := bstep (se 1 (by rfl) ⟨300938, by rfl⟩ : syracuseStep 401251 = 601877) B601877
theorem B597875 : Blo 397767 597875 := bstep (se 1 (by rfl) ⟨448406, by rfl⟩ : syracuseStep 597875 = 896813) B896813
theorem B401267 : Blo 397767 401267 := bstep (se 1 (by rfl) ⟨300950, by rfl⟩ : syracuseStep 401267 = 601901) B601901
theorem B401283 : Blo 397767 401283 := bstep (se 1 (by rfl) ⟨300962, by rfl⟩ : syracuseStep 401283 = 601925) B601925
theorem B1351565 : Blo 397767 1351565 := bstep (se 3 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 1351565 = 506837) B506837
theorem B597905 : Blo 397767 597905 := bstep (se 2 (by rfl) ⟨224214, by rfl⟩ : syracuseStep 597905 = 448429) B448429
theorem B401299 : Blo 397767 401299 := bstep (se 1 (by rfl) ⟨300974, by rfl⟩ : syracuseStep 401299 = 601949) B601949
theorem B597923 : Blo 397767 597923 := bstep (se 1 (by rfl) ⟨448442, by rfl⟩ : syracuseStep 597923 = 896885) B896885
theorem B401315 : Blo 397767 401315 := bstep (se 1 (by rfl) ⟨300986, by rfl⟩ : syracuseStep 401315 = 601973) B601973
theorem B958385 : Blo 397767 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B401331 : Blo 397767 401331 := bstep (se 1 (by rfl) ⟨300998, by rfl⟩ : syracuseStep 401331 = 601997) B601997
theorem B597953 : Blo 397767 597953 := bstep (se 2 (by rfl) ⟨224232, by rfl⟩ : syracuseStep 597953 = 448465) B448465
theorem B1351619 : Blo 397767 1351619 := bstep (se 1 (by rfl) ⟨1013714, by rfl⟩ : syracuseStep 1351619 = 2027429) B2027429
theorem B401347 : Blo 397767 401347 := bstep (se 1 (by rfl) ⟨301010, by rfl⟩ : syracuseStep 401347 = 602021) B602021
theorem B1515469 : Blo 397767 1515469 := bstep (se 3 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 1515469 = 568301) B568301
theorem B597971 : Blo 397767 597971 := bstep (se 1 (by rfl) ⟨448478, by rfl⟩ : syracuseStep 597971 = 896957) B896957
theorem B401363 : Blo 397767 401363 := bstep (se 1 (by rfl) ⟨301022, by rfl⟩ : syracuseStep 401363 = 602045) B602045
theorem B401379 : Blo 397767 401379 := bstep (se 1 (by rfl) ⟨301034, by rfl⟩ : syracuseStep 401379 = 602069) B602069
theorem B598001 : Blo 397767 598001 := bstep (se 2 (by rfl) ⟨224250, by rfl⟩ : syracuseStep 598001 = 448501) B448501
theorem B401395 : Blo 397767 401395 := bstep (se 1 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 401395 = 602093) B602093
theorem B598019 : Blo 397767 598019 := bstep (se 1 (by rfl) ⟨448514, by rfl⟩ : syracuseStep 598019 = 897029) B897029
theorem B401411 : Blo 397767 401411 := bstep (se 1 (by rfl) ⟨301058, by rfl⟩ : syracuseStep 401411 = 602117) B602117
theorem B401427 : Blo 397767 401427 := bstep (se 1 (by rfl) ⟨301070, by rfl⟩ : syracuseStep 401427 = 602141) B602141
theorem B598049 : Blo 397767 598049 := bstep (se 2 (by rfl) ⟨224268, by rfl⟩ : syracuseStep 598049 = 448537) B448537
theorem B401443 : Blo 397767 401443 := bstep (se 1 (by rfl) ⟨301082, by rfl⟩ : syracuseStep 401443 = 602165) B602165
theorem B1286189 : Blo 397767 1286189 := bstep (se 3 (by rfl) ⟨241160, by rfl⟩ : syracuseStep 1286189 = 482321) B482321
theorem B598067 : Blo 397767 598067 := bstep (se 1 (by rfl) ⟨448550, by rfl⟩ : syracuseStep 598067 = 897101) B897101
theorem B401459 : Blo 397767 401459 := bstep (se 1 (by rfl) ⟨301094, by rfl⟩ : syracuseStep 401459 = 602189) B602189
theorem B401475 : Blo 397767 401475 := bstep (se 1 (by rfl) ⟨301106, by rfl⟩ : syracuseStep 401475 = 602213) B602213
theorem B598097 : Blo 397767 598097 := bstep (se 2 (by rfl) ⟨224286, by rfl⟩ : syracuseStep 598097 = 448573) B448573
theorem B401491 : Blo 397767 401491 := bstep (se 1 (by rfl) ⟨301118, by rfl⟩ : syracuseStep 401491 = 602237) B602237
theorem B598115 : Blo 397767 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B401507 : Blo 397767 401507 := bstep (se 1 (by rfl) ⟨301130, by rfl⟩ : syracuseStep 401507 = 602261) B602261
theorem B401523 : Blo 397767 401523 := bstep (se 1 (by rfl) ⟨301142, by rfl⟩ : syracuseStep 401523 = 602285) B602285
theorem B598145 : Blo 397767 598145 := bstep (se 2 (by rfl) ⟨224304, by rfl⟩ : syracuseStep 598145 = 448609) B448609
theorem B761987 : Blo 397767 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B401539 : Blo 397767 401539 := bstep (se 1 (by rfl) ⟨301154, by rfl⟩ : syracuseStep 401539 = 602309) B602309
theorem B1220753 : Blo 397767 1220753 := bstep (se 2 (by rfl) ⟨457782, by rfl⟩ : syracuseStep 1220753 = 915565) B915565
theorem B598163 : Blo 397767 598163 := bstep (se 1 (by rfl) ⟨448622, by rfl⟩ : syracuseStep 598163 = 897245) B897245
theorem B401555 : Blo 397767 401555 := bstep (se 1 (by rfl) ⟨301166, by rfl⟩ : syracuseStep 401555 = 602333) B602333
theorem B401571 : Blo 397767 401571 := bstep (se 1 (by rfl) ⟨301178, by rfl⟩ : syracuseStep 401571 = 602357) B602357
theorem B598193 : Blo 397767 598193 := bstep (se 2 (by rfl) ⟨224322, by rfl⟩ : syracuseStep 598193 = 448645) B448645
theorem B401587 : Blo 397767 401587 := bstep (se 1 (by rfl) ⟨301190, by rfl⟩ : syracuseStep 401587 = 602381) B602381
theorem B598211 : Blo 397767 598211 := bstep (se 1 (by rfl) ⟨448658, by rfl⟩ : syracuseStep 598211 = 897317) B897317
theorem B401603 : Blo 397767 401603 := bstep (se 1 (by rfl) ⟨301202, by rfl⟩ : syracuseStep 401603 = 602405) B602405
theorem B10887365 : Blo 397767 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B1351889 : Blo 397767 1351889 := bstep (se 2 (by rfl) ⟨506958, by rfl⟩ : syracuseStep 1351889 = 1013917) B1013917
theorem B401619 : Blo 397767 401619 := bstep (se 1 (by rfl) ⟨301214, by rfl⟩ : syracuseStep 401619 = 602429) B602429
theorem B598241 : Blo 397767 598241 := bstep (se 2 (by rfl) ⟨224340, by rfl⟩ : syracuseStep 598241 = 448681) B448681
theorem B401635 : Blo 397767 401635 := bstep (se 1 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 401635 = 602453) B602453
theorem B598259 : Blo 397767 598259 := bstep (se 1 (by rfl) ⟨448694, by rfl⟩ : syracuseStep 598259 = 897389) B897389
theorem B401651 : Blo 397767 401651 := bstep (se 1 (by rfl) ⟨301238, by rfl⟩ : syracuseStep 401651 = 602477) B602477
theorem B401667 : Blo 397767 401667 := bstep (se 1 (by rfl) ⟨301250, by rfl⟩ : syracuseStep 401667 = 602501) B602501
theorem B598289 : Blo 397767 598289 := bstep (se 2 (by rfl) ⟨224358, by rfl⟩ : syracuseStep 598289 = 448717) B448717
theorem B401683 : Blo 397767 401683 := bstep (se 1 (by rfl) ⟨301262, by rfl⟩ : syracuseStep 401683 = 602525) B602525
theorem B598307 : Blo 397767 598307 := bstep (se 1 (by rfl) ⟨448730, by rfl⟩ : syracuseStep 598307 = 897461) B897461
theorem B401699 : Blo 397767 401699 := bstep (se 1 (by rfl) ⟨301274, by rfl⟩ : syracuseStep 401699 = 602549) B602549
theorem B401715 : Blo 397767 401715 := bstep (se 1 (by rfl) ⟨301286, by rfl⟩ : syracuseStep 401715 = 602573) B602573
theorem B598337 : Blo 397767 598337 := bstep (se 2 (by rfl) ⟨224376, by rfl⟩ : syracuseStep 598337 = 448753) B448753
theorem B401731 : Blo 397767 401731 := bstep (se 1 (by rfl) ⟨301298, by rfl⟩ : syracuseStep 401731 = 602597) B602597
theorem B598355 : Blo 397767 598355 := bstep (se 1 (by rfl) ⟨448766, by rfl⟩ : syracuseStep 598355 = 897533) B897533
theorem B401747 : Blo 397767 401747 := bstep (se 1 (by rfl) ⟨301310, by rfl⟩ : syracuseStep 401747 = 602621) B602621
theorem B401763 : Blo 397767 401763 := bstep (se 1 (by rfl) ⟨301322, by rfl⟩ : syracuseStep 401763 = 602645) B602645
theorem B598385 : Blo 397767 598385 := bstep (se 2 (by rfl) ⟨224394, by rfl⟩ : syracuseStep 598385 = 448789) B448789
theorem B598403 : Blo 397767 598403 := bstep (se 1 (by rfl) ⟨448802, by rfl⟩ : syracuseStep 598403 = 897605) B897605
theorem B598433 : Blo 397767 598433 := bstep (se 2 (by rfl) ⟨224412, by rfl⟩ : syracuseStep 598433 = 448825) B448825
theorem B598451 : Blo 397767 598451 := bstep (se 1 (by rfl) ⟨448838, by rfl⟩ : syracuseStep 598451 = 897677) B897677
theorem B1024451 : Blo 397767 1024451 := bstep (se 1 (by rfl) ⟨768338, by rfl⟩ : syracuseStep 1024451 = 1536677) B1536677
theorem B598481 : Blo 397767 598481 := bstep (se 2 (by rfl) ⟨224430, by rfl⟩ : syracuseStep 598481 = 448861) B448861
theorem B598499 : Blo 397767 598499 := bstep (se 1 (by rfl) ⟨448874, by rfl⟩ : syracuseStep 598499 = 897749) B897749
theorem B598529 : Blo 397767 598529 := bstep (se 2 (by rfl) ⟨224448, by rfl⟩ : syracuseStep 598529 = 448897) B448897
theorem B598547 : Blo 397767 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B598577 : Blo 397767 598577 := bstep (se 2 (by rfl) ⟨224466, by rfl⟩ : syracuseStep 598577 = 448933) B448933
theorem B598595 : Blo 397767 598595 := bstep (se 1 (by rfl) ⟨448946, by rfl⟩ : syracuseStep 598595 = 897893) B897893
theorem B598625 : Blo 397767 598625 := bstep (se 2 (by rfl) ⟨224484, by rfl⟩ : syracuseStep 598625 = 448969) B448969
theorem B598643 : Blo 397767 598643 := bstep (se 1 (by rfl) ⟨448982, by rfl⟩ : syracuseStep 598643 = 897965) B897965
theorem B598673 : Blo 397767 598673 := bstep (se 2 (by rfl) ⟨224502, by rfl⟩ : syracuseStep 598673 = 449005) B449005
theorem B598691 : Blo 397767 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B598721 : Blo 397767 598721 := bstep (se 2 (by rfl) ⟨224520, by rfl⟩ : syracuseStep 598721 = 449041) B449041
theorem B598739 : Blo 397767 598739 := bstep (se 1 (by rfl) ⟨449054, by rfl⟩ : syracuseStep 598739 = 898109) B898109
theorem B1516259 : Blo 397767 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B1352429 : Blo 397767 1352429 := bstep (se 3 (by rfl) ⟨253580, by rfl⟩ : syracuseStep 1352429 = 507161) B507161
theorem B598769 : Blo 397767 598769 := bstep (se 2 (by rfl) ⟨224538, by rfl⟩ : syracuseStep 598769 = 449077) B449077
theorem B3842801 : Blo 397767 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B598787 : Blo 397767 598787 := bstep (se 1 (by rfl) ⟨449090, by rfl⟩ : syracuseStep 598787 = 898181) B898181
theorem B598817 : Blo 397767 598817 := bstep (se 2 (by rfl) ⟨224556, by rfl⟩ : syracuseStep 598817 = 449113) B449113
theorem B1352483 : Blo 397767 1352483 := bstep (se 1 (by rfl) ⟨1014362, by rfl⟩ : syracuseStep 1352483 = 2028725) B2028725
theorem B598835 : Blo 397767 598835 := bstep (se 1 (by rfl) ⟨449126, by rfl⟩ : syracuseStep 598835 = 898253) B898253
theorem B2564941 : Blo 397767 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B598865 : Blo 397767 598865 := bstep (se 2 (by rfl) ⟨224574, by rfl⟩ : syracuseStep 598865 = 449149) B449149
theorem B598883 : Blo 397767 598883 := bstep (se 1 (by rfl) ⟨449162, by rfl⟩ : syracuseStep 598883 = 898325) B898325
theorem B598913 : Blo 397767 598913 := bstep (se 2 (by rfl) ⟨224592, by rfl⟩ : syracuseStep 598913 = 449185) B449185
theorem B598931 : Blo 397767 598931 := bstep (se 1 (by rfl) ⟨449198, by rfl⟩ : syracuseStep 598931 = 898397) B898397
theorem B598961 : Blo 397767 598961 := bstep (se 2 (by rfl) ⟨224610, by rfl⟩ : syracuseStep 598961 = 449221) B449221
theorem B598979 : Blo 397767 598979 := bstep (se 1 (by rfl) ⟨449234, by rfl⟩ : syracuseStep 598979 = 898469) B898469
theorem B599009 : Blo 397767 599009 := bstep (se 2 (by rfl) ⟨224628, by rfl⟩ : syracuseStep 599009 = 449257) B449257
theorem B599027 : Blo 397767 599027 := bstep (se 1 (by rfl) ⟨449270, by rfl⟩ : syracuseStep 599027 = 898541) B898541
theorem B599057 : Blo 397767 599057 := bstep (se 2 (by rfl) ⟨224646, by rfl⟩ : syracuseStep 599057 = 449293) B449293
theorem B599075 : Blo 397767 599075 := bstep (se 1 (by rfl) ⟨449306, by rfl⟩ : syracuseStep 599075 = 898613) B898613
theorem B1352753 : Blo 397767 1352753 := bstep (se 2 (by rfl) ⟨507282, by rfl⟩ : syracuseStep 1352753 = 1014565) B1014565
theorem B599105 : Blo 397767 599105 := bstep (se 2 (by rfl) ⟨224664, by rfl⟩ : syracuseStep 599105 = 449329) B449329
theorem B599123 : Blo 397767 599123 := bstep (se 1 (by rfl) ⟨449342, by rfl⟩ : syracuseStep 599123 = 898685) B898685
theorem B3417187 : Blo 397767 3417187 := bstep (se 1 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 3417187 = 5125781) B5125781
theorem B599153 : Blo 397767 599153 := bstep (se 2 (by rfl) ⟨224682, by rfl⟩ : syracuseStep 599153 = 449365) B449365
theorem B599171 : Blo 397767 599171 := bstep (se 1 (by rfl) ⟨449378, by rfl⟩ : syracuseStep 599171 = 898757) B898757
theorem B2892941 : Blo 397767 2892941 := bstep (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) B1084853
theorem B599201 : Blo 397767 599201 := bstep (se 2 (by rfl) ⟨224700, by rfl⟩ : syracuseStep 599201 = 449401) B449401
theorem B599219 : Blo 397767 599219 := bstep (se 1 (by rfl) ⟨449414, by rfl⟩ : syracuseStep 599219 = 898829) B898829
theorem B599249 : Blo 397767 599249 := bstep (se 2 (by rfl) ⟨224718, by rfl⟩ : syracuseStep 599249 = 449437) B449437
theorem B599267 : Blo 397767 599267 := bstep (se 1 (by rfl) ⟨449450, by rfl⟩ : syracuseStep 599267 = 898901) B898901
theorem B599297 : Blo 397767 599297 := bstep (se 2 (by rfl) ⟨224736, by rfl⟩ : syracuseStep 599297 = 449473) B449473
theorem B599315 : Blo 397767 599315 := bstep (se 1 (by rfl) ⟨449486, by rfl⟩ : syracuseStep 599315 = 898973) B898973
theorem B599345 : Blo 397767 599345 := bstep (se 2 (by rfl) ⟨224754, by rfl⟩ : syracuseStep 599345 = 449509) B449509
theorem B599363 : Blo 397767 599363 := bstep (se 1 (by rfl) ⟨449522, by rfl⟩ : syracuseStep 599363 = 899045) B899045
theorem B599393 : Blo 397767 599393 := bstep (se 2 (by rfl) ⟨224772, by rfl⟩ : syracuseStep 599393 = 449545) B449545
theorem B1516913 : Blo 397767 1516913 := bstep (se 2 (by rfl) ⟨568842, by rfl⟩ : syracuseStep 1516913 = 1137685) B1137685
theorem B599411 : Blo 397767 599411 := bstep (se 1 (by rfl) ⟨449558, by rfl⟩ : syracuseStep 599411 = 899117) B899117
theorem B599441 : Blo 397767 599441 := bstep (se 2 (by rfl) ⟨224790, by rfl⟩ : syracuseStep 599441 = 449581) B449581
theorem B599459 : Blo 397767 599459 := bstep (se 1 (by rfl) ⟨449594, by rfl⟩ : syracuseStep 599459 = 899189) B899189
theorem B599489 : Blo 397767 599489 := bstep (se 2 (by rfl) ⟨224808, by rfl⟩ : syracuseStep 599489 = 449617) B449617
theorem B599507 : Blo 397767 599507 := bstep (se 1 (by rfl) ⟨449630, by rfl⟩ : syracuseStep 599507 = 899261) B899261
theorem B599537 : Blo 397767 599537 := bstep (se 2 (by rfl) ⟨224826, by rfl⟩ : syracuseStep 599537 = 449653) B449653
theorem B599555 : Blo 397767 599555 := bstep (se 1 (by rfl) ⟨449666, by rfl⟩ : syracuseStep 599555 = 899333) B899333
theorem B599585 : Blo 397767 599585 := bstep (se 2 (by rfl) ⟨224844, by rfl⟩ : syracuseStep 599585 = 449689) B449689
theorem B599603 : Blo 397767 599603 := bstep (se 1 (by rfl) ⟨449702, by rfl⟩ : syracuseStep 599603 = 899405) B899405
theorem B1353293 : Blo 397767 1353293 := bstep (se 3 (by rfl) ⟨253742, by rfl⟩ : syracuseStep 1353293 = 507485) B507485
theorem B599633 : Blo 397767 599633 := bstep (se 2 (by rfl) ⟨224862, by rfl⟩ : syracuseStep 599633 = 449725) B449725
theorem B1615459 : Blo 397767 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B599651 : Blo 397767 599651 := bstep (se 1 (by rfl) ⟨449738, by rfl⟩ : syracuseStep 599651 = 899477) B899477
theorem B599681 : Blo 397767 599681 := bstep (se 2 (by rfl) ⟨224880, by rfl⟩ : syracuseStep 599681 = 449761) B449761
theorem B1353347 : Blo 397767 1353347 := bstep (se 1 (by rfl) ⟨1015010, by rfl⟩ : syracuseStep 1353347 = 2030021) B2030021
theorem B566929 : Blo 397767 566929 := bstep (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) B425197
theorem B599699 : Blo 397767 599699 := bstep (se 1 (by rfl) ⟨449774, by rfl⟩ : syracuseStep 599699 = 899549) B899549
theorem B599729 : Blo 397767 599729 := bstep (se 2 (by rfl) ⟨224898, by rfl⟩ : syracuseStep 599729 = 449797) B449797
theorem B599747 : Blo 397767 599747 := bstep (se 1 (by rfl) ⟨449810, by rfl⟩ : syracuseStep 599747 = 899621) B899621
theorem B599777 : Blo 397767 599777 := bstep (se 2 (by rfl) ⟨224916, by rfl⟩ : syracuseStep 599777 = 449833) B449833
theorem B599795 : Blo 397767 599795 := bstep (se 1 (by rfl) ⟨449846, by rfl⟩ : syracuseStep 599795 = 899693) B899693
theorem B730883 : Blo 397767 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B599825 : Blo 397767 599825 := bstep (se 2 (by rfl) ⟨224934, by rfl⟩ : syracuseStep 599825 = 449869) B449869
theorem B599843 : Blo 397767 599843 := bstep (se 1 (by rfl) ⟨449882, by rfl⟩ : syracuseStep 599843 = 899765) B899765
theorem B599873 : Blo 397767 599873 := bstep (se 2 (by rfl) ⟨224952, by rfl⟩ : syracuseStep 599873 = 449905) B449905
theorem B599891 : Blo 397767 599891 := bstep (se 1 (by rfl) ⟨449918, by rfl⟩ : syracuseStep 599891 = 899837) B899837
theorem B599921 : Blo 397767 599921 := bstep (se 2 (by rfl) ⟨224970, by rfl⟩ : syracuseStep 599921 = 449941) B449941
theorem B599939 : Blo 397767 599939 := bstep (se 1 (by rfl) ⟨449954, by rfl⟩ : syracuseStep 599939 = 899909) B899909
theorem B1714061 : Blo 397767 1714061 := bstep (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) B642773
theorem B1353617 : Blo 397767 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B599969 : Blo 397767 599969 := bstep (se 2 (by rfl) ⟨224988, by rfl⟩ : syracuseStep 599969 = 449977) B449977
theorem B599987 : Blo 397767 599987 := bstep (se 1 (by rfl) ⟨449990, by rfl⟩ : syracuseStep 599987 = 899981) B899981
theorem B600017 : Blo 397767 600017 := bstep (se 2 (by rfl) ⟨225006, by rfl⟩ : syracuseStep 600017 = 450013) B450013
theorem B567265 : Blo 397767 567265 := bstep (se 2 (by rfl) ⟨212724, by rfl⟩ : syracuseStep 567265 = 425449) B425449
theorem B600035 : Blo 397767 600035 := bstep (se 1 (by rfl) ⟨450026, by rfl⟩ : syracuseStep 600035 = 900053) B900053
theorem B600065 : Blo 397767 600065 := bstep (se 2 (by rfl) ⟨225024, by rfl⟩ : syracuseStep 600065 = 450049) B450049
theorem B600083 : Blo 397767 600083 := bstep (se 1 (by rfl) ⟨450062, by rfl⟩ : syracuseStep 600083 = 900125) B900125
theorem B600113 : Blo 397767 600113 := bstep (se 2 (by rfl) ⟨225042, by rfl⟩ : syracuseStep 600113 = 450085) B450085
theorem B600131 : Blo 397767 600131 := bstep (se 1 (by rfl) ⟨450098, by rfl⟩ : syracuseStep 600131 = 900197) B900197
theorem B600161 : Blo 397767 600161 := bstep (se 2 (by rfl) ⟨225060, by rfl⟩ : syracuseStep 600161 = 450121) B450121
theorem B600179 : Blo 397767 600179 := bstep (se 1 (by rfl) ⟨450134, by rfl⟩ : syracuseStep 600179 = 900269) B900269
theorem B895121 : Blo 397767 895121 := bstep (se 2 (by rfl) ⟨335670, by rfl⟩ : syracuseStep 895121 = 671341) B671341
theorem B600209 : Blo 397767 600209 := bstep (se 2 (by rfl) ⟨225078, by rfl⟩ : syracuseStep 600209 = 450157) B450157
theorem B895139 : Blo 397767 895139 := bstep (se 1 (by rfl) ⟨671354, by rfl⟩ : syracuseStep 895139 = 1342709) B1342709
theorem B600227 : Blo 397767 600227 := bstep (se 1 (by rfl) ⟨450170, by rfl⟩ : syracuseStep 600227 = 900341) B900341
theorem B600257 : Blo 397767 600257 := bstep (se 2 (by rfl) ⟨225096, by rfl⟩ : syracuseStep 600257 = 450193) B450193
theorem B600275 : Blo 397767 600275 := bstep (se 1 (by rfl) ⟨450206, by rfl⟩ : syracuseStep 600275 = 900413) B900413
theorem B2271473 : Blo 397767 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B600305 : Blo 397767 600305 := bstep (se 2 (by rfl) ⟨225114, by rfl⟩ : syracuseStep 600305 = 450229) B450229
theorem B600323 : Blo 397767 600323 := bstep (se 1 (by rfl) ⟨450242, by rfl⟩ : syracuseStep 600323 = 900485) B900485
theorem B600353 : Blo 397767 600353 := bstep (se 2 (by rfl) ⟨225132, by rfl⟩ : syracuseStep 600353 = 450265) B450265
theorem B600371 : Blo 397767 600371 := bstep (se 1 (by rfl) ⟨450278, by rfl⟩ : syracuseStep 600371 = 900557) B900557
theorem B600401 : Blo 397767 600401 := bstep (se 2 (by rfl) ⟨225150, by rfl⟩ : syracuseStep 600401 = 450301) B450301
theorem B600419 : Blo 397767 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B600449 : Blo 397767 600449 := bstep (se 2 (by rfl) ⟨225168, by rfl⟩ : syracuseStep 600449 = 450337) B450337
theorem B600467 : Blo 397767 600467 := bstep (se 1 (by rfl) ⟨450350, by rfl⟩ : syracuseStep 600467 = 900701) B900701
theorem B1354157 : Blo 397767 1354157 := bstep (se 3 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 1354157 = 507809) B507809
theorem B895409 : Blo 397767 895409 := bstep (se 2 (by rfl) ⟨335778, by rfl⟩ : syracuseStep 895409 = 671557) B671557
theorem B600497 : Blo 397767 600497 := bstep (se 2 (by rfl) ⟨225186, by rfl⟩ : syracuseStep 600497 = 450373) B450373
theorem B895427 : Blo 397767 895427 := bstep (se 1 (by rfl) ⟨671570, by rfl⟩ : syracuseStep 895427 = 1343141) B1343141
theorem B600515 : Blo 397767 600515 := bstep (se 1 (by rfl) ⟨450386, by rfl⟩ : syracuseStep 600515 = 900773) B900773
theorem B3025349 : Blo 397767 3025349 := bstep (se 4 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 3025349 = 567253) B567253
theorem B600545 : Blo 397767 600545 := bstep (se 2 (by rfl) ⟨225204, by rfl⟩ : syracuseStep 600545 = 450409) B450409
theorem B1354211 : Blo 397767 1354211 := bstep (se 1 (by rfl) ⟨1015658, by rfl⟩ : syracuseStep 1354211 = 2031317) B2031317
theorem B600563 : Blo 397767 600563 := bstep (se 1 (by rfl) ⟨450422, by rfl⟩ : syracuseStep 600563 = 900845) B900845
theorem B600593 : Blo 397767 600593 := bstep (se 2 (by rfl) ⟨225222, by rfl⟩ : syracuseStep 600593 = 450445) B450445
theorem B600611 : Blo 397767 600611 := bstep (se 1 (by rfl) ⟨450458, by rfl⟩ : syracuseStep 600611 = 900917) B900917
theorem B567857 : Blo 397767 567857 := bstep (se 2 (by rfl) ⟨212946, by rfl⟩ : syracuseStep 567857 = 425893) B425893
theorem B600641 : Blo 397767 600641 := bstep (se 2 (by rfl) ⟨225240, by rfl⟩ : syracuseStep 600641 = 450481) B450481
theorem B600659 : Blo 397767 600659 := bstep (se 1 (by rfl) ⟨450494, by rfl⟩ : syracuseStep 600659 = 900989) B900989
theorem B600689 : Blo 397767 600689 := bstep (se 2 (by rfl) ⟨225258, by rfl⟩ : syracuseStep 600689 = 450517) B450517
theorem B600707 : Blo 397767 600707 := bstep (se 1 (by rfl) ⟨450530, by rfl⟩ : syracuseStep 600707 = 901061) B901061
theorem B600737 : Blo 397767 600737 := bstep (se 2 (by rfl) ⟨225276, by rfl⟩ : syracuseStep 600737 = 450553) B450553
theorem B600755 : Blo 397767 600755 := bstep (se 1 (by rfl) ⟨450566, by rfl⟩ : syracuseStep 600755 = 901133) B901133
theorem B895697 : Blo 397767 895697 := bstep (se 2 (by rfl) ⟨335886, by rfl⟩ : syracuseStep 895697 = 671773) B671773
theorem B600785 : Blo 397767 600785 := bstep (se 2 (by rfl) ⟨225294, by rfl⟩ : syracuseStep 600785 = 450589) B450589
theorem B895715 : Blo 397767 895715 := bstep (se 1 (by rfl) ⟨671786, by rfl⟩ : syracuseStep 895715 = 1343573) B1343573
theorem B600803 : Blo 397767 600803 := bstep (se 1 (by rfl) ⟨450602, by rfl⟩ : syracuseStep 600803 = 901205) B901205
theorem B1354481 : Blo 397767 1354481 := bstep (se 2 (by rfl) ⟨507930, by rfl⟩ : syracuseStep 1354481 = 1015861) B1015861
theorem B600833 : Blo 397767 600833 := bstep (se 2 (by rfl) ⟨225312, by rfl⟩ : syracuseStep 600833 = 450625) B450625
theorem B600851 : Blo 397767 600851 := bstep (se 1 (by rfl) ⟨450638, by rfl⟩ : syracuseStep 600851 = 901277) B901277
theorem B1518371 : Blo 397767 1518371 := bstep (se 1 (by rfl) ⟨1138778, by rfl⟩ : syracuseStep 1518371 = 2277557) B2277557
theorem B1518385 : Blo 397767 1518385 := bstep (se 2 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 1518385 = 1138789) B1138789
theorem B600881 : Blo 397767 600881 := bstep (se 2 (by rfl) ⟨225330, by rfl⟩ : syracuseStep 600881 = 450661) B450661
theorem B600899 : Blo 397767 600899 := bstep (se 1 (by rfl) ⟨450674, by rfl⟩ : syracuseStep 600899 = 901349) B901349
theorem B600929 : Blo 397767 600929 := bstep (se 2 (by rfl) ⟨225348, by rfl⟩ : syracuseStep 600929 = 450697) B450697
theorem B600947 : Blo 397767 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B600977 : Blo 397767 600977 := bstep (se 2 (by rfl) ⟨225366, by rfl⟩ : syracuseStep 600977 = 450733) B450733
theorem B600995 : Blo 397767 600995 := bstep (se 1 (by rfl) ⟨450746, by rfl⟩ : syracuseStep 600995 = 901493) B901493
theorem B601025 : Blo 397767 601025 := bstep (se 2 (by rfl) ⟨225384, by rfl⟩ : syracuseStep 601025 = 450769) B450769
theorem B601043 : Blo 397767 601043 := bstep (se 1 (by rfl) ⟨450782, by rfl⟩ : syracuseStep 601043 = 901565) B901565
theorem B3877859 : Blo 397767 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B895985 : Blo 397767 895985 := bstep (se 2 (by rfl) ⟨335994, by rfl⟩ : syracuseStep 895985 = 671989) B671989
theorem B601073 : Blo 397767 601073 := bstep (se 2 (by rfl) ⟨225402, by rfl⟩ : syracuseStep 601073 = 450805) B450805
theorem B896003 : Blo 397767 896003 := bstep (se 1 (by rfl) ⟨672002, by rfl⟩ : syracuseStep 896003 = 1344005) B1344005
theorem B601091 : Blo 397767 601091 := bstep (se 1 (by rfl) ⟨450818, by rfl⟩ : syracuseStep 601091 = 901637) B901637
theorem B2567173 : Blo 397767 2567173 := bstep (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) B481345
theorem B601121 : Blo 397767 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B601139 : Blo 397767 601139 := bstep (se 1 (by rfl) ⟨450854, by rfl⟩ : syracuseStep 601139 = 901709) B901709
theorem B568387 : Blo 397767 568387 := bstep (se 1 (by rfl) ⟨426290, by rfl⟩ : syracuseStep 568387 = 852581) B852581
theorem B601169 : Blo 397767 601169 := bstep (se 2 (by rfl) ⟨225438, by rfl⟩ : syracuseStep 601169 = 450877) B450877
theorem B601187 : Blo 397767 601187 := bstep (se 1 (by rfl) ⟨450890, by rfl⟩ : syracuseStep 601187 = 901781) B901781
theorem B601217 : Blo 397767 601217 := bstep (se 2 (by rfl) ⟨225456, by rfl⟩ : syracuseStep 601217 = 450913) B450913
theorem B601235 : Blo 397767 601235 := bstep (se 1 (by rfl) ⟨450926, by rfl⟩ : syracuseStep 601235 = 901853) B901853
theorem B601265 : Blo 397767 601265 := bstep (se 2 (by rfl) ⟨225474, by rfl⟩ : syracuseStep 601265 = 450949) B450949
theorem B601283 : Blo 397767 601283 := bstep (se 1 (by rfl) ⟨450962, by rfl⟩ : syracuseStep 601283 = 901925) B901925
theorem B601313 : Blo 397767 601313 := bstep (se 2 (by rfl) ⟨225492, by rfl⟩ : syracuseStep 601313 = 450985) B450985
theorem B601331 : Blo 397767 601331 := bstep (se 1 (by rfl) ⟨450998, by rfl⟩ : syracuseStep 601331 = 901997) B901997
theorem B1355021 : Blo 397767 1355021 := bstep (se 3 (by rfl) ⟨254066, by rfl⟩ : syracuseStep 1355021 = 508133) B508133
theorem B896273 : Blo 397767 896273 := bstep (se 2 (by rfl) ⟨336102, by rfl⟩ : syracuseStep 896273 = 672205) B672205
theorem B601361 : Blo 397767 601361 := bstep (se 2 (by rfl) ⟨225510, by rfl⟩ : syracuseStep 601361 = 451021) B451021
theorem B896291 : Blo 397767 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B601379 : Blo 397767 601379 := bstep (se 1 (by rfl) ⟨451034, by rfl⟩ : syracuseStep 601379 = 902069) B902069
theorem B601409 : Blo 397767 601409 := bstep (se 2 (by rfl) ⟨225528, by rfl⟩ : syracuseStep 601409 = 451057) B451057
theorem B1355075 : Blo 397767 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B601427 : Blo 397767 601427 := bstep (se 1 (by rfl) ⟨451070, by rfl⟩ : syracuseStep 601427 = 902141) B902141
theorem B601457 : Blo 397767 601457 := bstep (se 2 (by rfl) ⟨225546, by rfl⟩ : syracuseStep 601457 = 451093) B451093
theorem B601475 : Blo 397767 601475 := bstep (se 1 (by rfl) ⟨451106, by rfl⟩ : syracuseStep 601475 = 902213) B902213
theorem B568723 : Blo 397767 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B601505 : Blo 397767 601505 := bstep (se 2 (by rfl) ⟨225564, by rfl⟩ : syracuseStep 601505 = 451129) B451129
theorem B961969 : Blo 397767 961969 := bstep (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) B721477
theorem B601523 : Blo 397767 601523 := bstep (se 1 (by rfl) ⟨451142, by rfl⟩ : syracuseStep 601523 = 902285) B902285
theorem B601553 : Blo 397767 601553 := bstep (se 2 (by rfl) ⟨225582, by rfl⟩ : syracuseStep 601553 = 451165) B451165
theorem B601571 : Blo 397767 601571 := bstep (se 1 (by rfl) ⟨451178, by rfl⟩ : syracuseStep 601571 = 902357) B902357
theorem B601601 : Blo 397767 601601 := bstep (se 2 (by rfl) ⟨225600, by rfl⟩ : syracuseStep 601601 = 451201) B451201
theorem B601619 : Blo 397767 601619 := bstep (se 1 (by rfl) ⟨451214, by rfl⟩ : syracuseStep 601619 = 902429) B902429
theorem B896561 : Blo 397767 896561 := bstep (se 2 (by rfl) ⟨336210, by rfl⟩ : syracuseStep 896561 = 672421) B672421
theorem B601649 : Blo 397767 601649 := bstep (se 2 (by rfl) ⟨225618, by rfl⟩ : syracuseStep 601649 = 451237) B451237
theorem B896579 : Blo 397767 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B601667 : Blo 397767 601667 := bstep (se 1 (by rfl) ⟨451250, by rfl⟩ : syracuseStep 601667 = 902501) B902501
theorem B1355345 : Blo 397767 1355345 := bstep (se 2 (by rfl) ⟨508254, by rfl⟩ : syracuseStep 1355345 = 1016509) B1016509
theorem B601697 : Blo 397767 601697 := bstep (se 2 (by rfl) ⟨225636, by rfl⟩ : syracuseStep 601697 = 451273) B451273
theorem B601715 : Blo 397767 601715 := bstep (se 1 (by rfl) ⟨451286, by rfl⟩ : syracuseStep 601715 = 902573) B902573
theorem B601745 : Blo 397767 601745 := bstep (se 2 (by rfl) ⟨225654, by rfl⟩ : syracuseStep 601745 = 451309) B451309
theorem B2272931 : Blo 397767 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B601763 : Blo 397767 601763 := bstep (se 1 (by rfl) ⟨451322, by rfl⟩ : syracuseStep 601763 = 902645) B902645
theorem B601793 : Blo 397767 601793 := bstep (se 2 (by rfl) ⟨225672, by rfl⟩ : syracuseStep 601793 = 451345) B451345
theorem B503491 : Blo 397767 503491 := bstep (se 1 (by rfl) ⟨377618, by rfl⟩ : syracuseStep 503491 = 755237) B755237
theorem B601811 : Blo 397767 601811 := bstep (se 1 (by rfl) ⟨451358, by rfl⟩ : syracuseStep 601811 = 902717) B902717
theorem B1650403 : Blo 397767 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B601841 : Blo 397767 601841 := bstep (se 2 (by rfl) ⟨225690, by rfl⟩ : syracuseStep 601841 = 451381) B451381
theorem B601859 : Blo 397767 601859 := bstep (se 1 (by rfl) ⟨451394, by rfl⟩ : syracuseStep 601859 = 902789) B902789
theorem B601889 : Blo 397767 601889 := bstep (se 2 (by rfl) ⟨225708, by rfl⟩ : syracuseStep 601889 = 451417) B451417
theorem B503587 : Blo 397767 503587 := bstep (se 1 (by rfl) ⟨377690, by rfl⟩ : syracuseStep 503587 = 755381) B755381
theorem B601907 : Blo 397767 601907 := bstep (se 1 (by rfl) ⟨451430, by rfl⟩ : syracuseStep 601907 = 902861) B902861
theorem B896849 : Blo 397767 896849 := bstep (se 2 (by rfl) ⟨336318, by rfl⟩ : syracuseStep 896849 = 672637) B672637
theorem B601937 : Blo 397767 601937 := bstep (se 2 (by rfl) ⟨225726, by rfl⟩ : syracuseStep 601937 = 451453) B451453
theorem B896867 : Blo 397767 896867 := bstep (se 1 (by rfl) ⟨672650, by rfl⟩ : syracuseStep 896867 = 1345301) B1345301
theorem B601955 : Blo 397767 601955 := bstep (se 1 (by rfl) ⟨451466, by rfl⟩ : syracuseStep 601955 = 902933) B902933
theorem B601985 : Blo 397767 601985 := bstep (se 2 (by rfl) ⟨225744, by rfl⟩ : syracuseStep 601985 = 451489) B451489
theorem B602003 : Blo 397767 602003 := bstep (se 1 (by rfl) ⟨451502, by rfl⟩ : syracuseStep 602003 = 903005) B903005
theorem B602033 : Blo 397767 602033 := bstep (se 2 (by rfl) ⟨225762, by rfl⟩ : syracuseStep 602033 = 451525) B451525
theorem B569281 : Blo 397767 569281 := bstep (se 2 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 569281 = 426961) B426961
theorem B602051 : Blo 397767 602051 := bstep (se 1 (by rfl) ⟨451538, by rfl⟩ : syracuseStep 602051 = 903077) B903077
theorem B602081 : Blo 397767 602081 := bstep (se 2 (by rfl) ⟨225780, by rfl⟩ : syracuseStep 602081 = 451561) B451561
theorem B569315 : Blo 397767 569315 := bstep (se 1 (by rfl) ⟨426986, by rfl⟩ : syracuseStep 569315 = 853973) B853973
theorem B602099 : Blo 397767 602099 := bstep (se 1 (by rfl) ⟨451574, by rfl⟩ : syracuseStep 602099 = 903149) B903149
theorem B602129 : Blo 397767 602129 := bstep (se 2 (by rfl) ⟨225798, by rfl⟩ : syracuseStep 602129 = 451597) B451597
theorem B405523 : Blo 397767 405523 := bstep (se 1 (by rfl) ⟨304142, by rfl⟩ : syracuseStep 405523 = 608285) B608285
theorem B602147 : Blo 397767 602147 := bstep (se 1 (by rfl) ⟨451610, by rfl⟩ : syracuseStep 602147 = 903221) B903221
theorem B602177 : Blo 397767 602177 := bstep (se 2 (by rfl) ⟨225816, by rfl⟩ : syracuseStep 602177 = 451633) B451633
theorem B602195 : Blo 397767 602195 := bstep (se 1 (by rfl) ⟨451646, by rfl⟩ : syracuseStep 602195 = 903293) B903293
theorem B1355885 : Blo 397767 1355885 := bstep (se 3 (by rfl) ⟨254228, by rfl⟩ : syracuseStep 1355885 = 508457) B508457
theorem B897137 : Blo 397767 897137 := bstep (se 2 (by rfl) ⟨336426, by rfl⟩ : syracuseStep 897137 = 672853) B672853
theorem B602225 : Blo 397767 602225 := bstep (se 2 (by rfl) ⟨225834, by rfl⟩ : syracuseStep 602225 = 451669) B451669
theorem B897155 : Blo 397767 897155 := bstep (se 1 (by rfl) ⟨672866, by rfl⟩ : syracuseStep 897155 = 1345733) B1345733
theorem B602243 : Blo 397767 602243 := bstep (se 1 (by rfl) ⟨451682, by rfl⟩ : syracuseStep 602243 = 903365) B903365
theorem B602273 : Blo 397767 602273 := bstep (se 2 (by rfl) ⟨225852, by rfl⟩ : syracuseStep 602273 = 451705) B451705
theorem B1355939 : Blo 397767 1355939 := bstep (se 1 (by rfl) ⟨1016954, by rfl⟩ : syracuseStep 1355939 = 2033909) B2033909
theorem B602291 : Blo 397767 602291 := bstep (se 1 (by rfl) ⟨451718, by rfl⟩ : syracuseStep 602291 = 903437) B903437
theorem B602321 : Blo 397767 602321 := bstep (se 2 (by rfl) ⟨225870, by rfl⟩ : syracuseStep 602321 = 451741) B451741
theorem B1519843 : Blo 397767 1519843 := bstep (se 1 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 1519843 = 2279765) B2279765
theorem B602339 : Blo 397767 602339 := bstep (se 1 (by rfl) ⟨451754, by rfl⟩ : syracuseStep 602339 = 903509) B903509
theorem B602369 : Blo 397767 602369 := bstep (se 2 (by rfl) ⟨225888, by rfl⟩ : syracuseStep 602369 = 451777) B451777
theorem B1028369 : Blo 397767 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B504083 : Blo 397767 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B602387 : Blo 397767 602387 := bstep (se 1 (by rfl) ⟨451790, by rfl⟩ : syracuseStep 602387 = 903581) B903581
theorem B602417 : Blo 397767 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B602435 : Blo 397767 602435 := bstep (se 1 (by rfl) ⟨451826, by rfl⟩ : syracuseStep 602435 = 903653) B903653
theorem B602465 : Blo 397767 602465 := bstep (se 2 (by rfl) ⟨225924, by rfl⟩ : syracuseStep 602465 = 451849) B451849
theorem B602483 : Blo 397767 602483 := bstep (se 1 (by rfl) ⟨451862, by rfl⟩ : syracuseStep 602483 = 903725) B903725
theorem B897425 : Blo 397767 897425 := bstep (se 2 (by rfl) ⟨336534, by rfl⟩ : syracuseStep 897425 = 673069) B673069
theorem B602513 : Blo 397767 602513 := bstep (se 2 (by rfl) ⟨225942, by rfl⟩ : syracuseStep 602513 = 451885) B451885
theorem B897443 : Blo 397767 897443 := bstep (se 1 (by rfl) ⟨673082, by rfl⟩ : syracuseStep 897443 = 1346165) B1346165
theorem B602531 : Blo 397767 602531 := bstep (se 1 (by rfl) ⟨451898, by rfl⟩ : syracuseStep 602531 = 903797) B903797
theorem B602561 : Blo 397767 602561 := bstep (se 2 (by rfl) ⟨225960, by rfl⟩ : syracuseStep 602561 = 451921) B451921
theorem B602579 : Blo 397767 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B602609 : Blo 397767 602609 := bstep (se 2 (by rfl) ⟨225978, by rfl⟩ : syracuseStep 602609 = 451957) B451957
theorem B602627 : Blo 397767 602627 := bstep (se 1 (by rfl) ⟨451970, by rfl⟩ : syracuseStep 602627 = 903941) B903941
theorem B569873 : Blo 397767 569873 := bstep (se 2 (by rfl) ⟨213702, by rfl⟩ : syracuseStep 569873 = 427405) B427405
theorem B569953 : Blo 397767 569953 := bstep (se 2 (by rfl) ⟨213732, by rfl⟩ : syracuseStep 569953 = 427465) B427465
theorem B2273933 : Blo 397767 2273933 := bstep (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) B852725
theorem B3846797 : Blo 397767 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B897713 : Blo 397767 897713 := bstep (se 2 (by rfl) ⟨336642, by rfl⟩ : syracuseStep 897713 = 673285) B673285
theorem B897731 : Blo 397767 897731 := bstep (se 1 (by rfl) ⟨673298, by rfl⟩ : syracuseStep 897731 = 1346597) B1346597
theorem B4109197 : Blo 397767 4109197 := bstep (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) B1540949
theorem B898001 : Blo 397767 898001 := bstep (se 2 (by rfl) ⟨336750, by rfl⟩ : syracuseStep 898001 = 673501) B673501
theorem B504787 : Blo 397767 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B898019 : Blo 397767 898019 := bstep (se 1 (by rfl) ⟨673514, by rfl⟩ : syracuseStep 898019 = 1347029) B1347029
theorem B832547 : Blo 397767 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B504883 : Blo 397767 504883 := bstep (se 1 (by rfl) ⟨378662, by rfl⟩ : syracuseStep 504883 = 757325) B757325
theorem B898289 : Blo 397767 898289 := bstep (se 2 (by rfl) ⟨336858, by rfl⟩ : syracuseStep 898289 = 673717) B673717
theorem B898307 : Blo 397767 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B570739 : Blo 397767 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B898577 : Blo 397767 898577 := bstep (se 2 (by rfl) ⟨336966, by rfl⟩ : syracuseStep 898577 = 673933) B673933
theorem B505379 : Blo 397767 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B898595 : Blo 397767 898595 := bstep (se 1 (by rfl) ⟨673946, by rfl⟩ : syracuseStep 898595 = 1347893) B1347893
theorem B1095277 : Blo 397767 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B1914673 : Blo 397767 1914673 := bstep (se 2 (by rfl) ⟨718002, by rfl⟩ : syracuseStep 1914673 = 1436005) B1436005
theorem B898865 : Blo 397767 898865 := bstep (se 2 (by rfl) ⟨337074, by rfl⟩ : syracuseStep 898865 = 674149) B674149
theorem B898883 : Blo 397767 898883 := bstep (se 1 (by rfl) ⟨674162, by rfl⟩ : syracuseStep 898883 = 1348325) B1348325
theorem B571217 : Blo 397767 571217 := bstep (se 2 (by rfl) ⟨214206, by rfl⟩ : syracuseStep 571217 = 428413) B428413
theorem B1914787 : Blo 397767 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B571331 : Blo 397767 571331 := bstep (se 1 (by rfl) ⟨428498, by rfl⟩ : syracuseStep 571331 = 856997) B856997
theorem B571411 : Blo 397767 571411 := bstep (se 1 (by rfl) ⟨428558, by rfl⟩ : syracuseStep 571411 = 857117) B857117
theorem B899153 : Blo 397767 899153 := bstep (se 2 (by rfl) ⟨337182, by rfl⟩ : syracuseStep 899153 = 674365) B674365
theorem B899171 : Blo 397767 899171 := bstep (se 1 (by rfl) ⟨674378, by rfl⟩ : syracuseStep 899171 = 1348757) B1348757
theorem B506083 : Blo 397767 506083 := bstep (se 1 (by rfl) ⟨379562, by rfl⟩ : syracuseStep 506083 = 759125) B759125
theorem B1620209 : Blo 397767 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B506179 : Blo 397767 506179 := bstep (se 1 (by rfl) ⟨379634, by rfl⟩ : syracuseStep 506179 = 759269) B759269
theorem B637283 : Blo 397767 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B899441 : Blo 397767 899441 := bstep (se 2 (by rfl) ⟨337290, by rfl⟩ : syracuseStep 899441 = 674581) B674581
theorem B899459 : Blo 397767 899459 := bstep (se 1 (by rfl) ⟨674594, by rfl⟩ : syracuseStep 899459 = 1349189) B1349189
theorem B1522061 : Blo 397767 1522061 := bstep (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) B570773
theorem B571969 : Blo 397767 571969 := bstep (se 2 (by rfl) ⟨214488, by rfl⟩ : syracuseStep 571969 = 428977) B428977
theorem B637507 : Blo 397767 637507 := bstep (se 1 (by rfl) ⟨478130, by rfl⟩ : syracuseStep 637507 = 956261) B956261
theorem B637571 : Blo 397767 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B899729 : Blo 397767 899729 := bstep (se 2 (by rfl) ⟨337398, by rfl⟩ : syracuseStep 899729 = 674797) B674797
theorem B899747 : Blo 397767 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B637699 : Blo 397767 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B506675 : Blo 397767 506675 := bstep (se 1 (by rfl) ⟨380006, by rfl⟩ : syracuseStep 506675 = 760013) B760013
theorem B3849029 : Blo 397767 3849029 := bstep (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) B721693
theorem B900017 : Blo 397767 900017 := bstep (se 2 (by rfl) ⟨337506, by rfl⟩ : syracuseStep 900017 = 675013) B675013
theorem B900035 : Blo 397767 900035 := bstep (se 1 (by rfl) ⟨675026, by rfl⟩ : syracuseStep 900035 = 1350053) B1350053
theorem B2014307 : Blo 397767 2014307 := bstep (se 1 (by rfl) ⟨1510730, by rfl⟩ : syracuseStep 2014307 = 3021461) B3021461
theorem B900305 : Blo 397767 900305 := bstep (se 2 (by rfl) ⟨337614, by rfl⟩ : syracuseStep 900305 = 675229) B675229
theorem B2079971 : Blo 397767 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B900323 : Blo 397767 900323 := bstep (se 1 (by rfl) ⟨675242, by rfl⟩ : syracuseStep 900323 = 1350485) B1350485
theorem B998723 : Blo 397767 998723 := bstep (se 1 (by rfl) ⟨749042, by rfl⟩ : syracuseStep 998723 = 1498085) B1498085
theorem B540049 : Blo 397767 540049 := bstep (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) B405037
theorem B638417 : Blo 397767 638417 := bstep (se 2 (by rfl) ⟨239406, by rfl⟩ : syracuseStep 638417 = 478813) B478813
theorem B2276849 : Blo 397767 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B900593 : Blo 397767 900593 := bstep (se 2 (by rfl) ⟨337722, by rfl⟩ : syracuseStep 900593 = 675445) B675445
theorem B507379 : Blo 397767 507379 := bstep (se 1 (by rfl) ⟨380534, by rfl⟩ : syracuseStep 507379 = 761069) B761069
theorem B671233 : Blo 397767 671233 := bstep (se 2 (by rfl) ⟨251712, by rfl⟩ : syracuseStep 671233 = 503425) B503425
theorem B900611 : Blo 397767 900611 := bstep (se 1 (by rfl) ⟨675458, by rfl⟩ : syracuseStep 900611 = 1350917) B1350917
theorem B671267 : Blo 397767 671267 := bstep (se 1 (by rfl) ⟨503450, by rfl⟩ : syracuseStep 671267 = 1006901) B1006901
theorem B605731 : Blo 397767 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B638545 : Blo 397767 638545 := bstep (se 2 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 638545 = 478909) B478909
theorem B507475 : Blo 397767 507475 := bstep (se 1 (by rfl) ⟨380606, by rfl⟩ : syracuseStep 507475 = 761213) B761213
theorem B671395 : Blo 397767 671395 := bstep (se 1 (by rfl) ⟨503546, by rfl⟩ : syracuseStep 671395 = 1007093) B1007093
theorem B900881 : Blo 397767 900881 := bstep (se 2 (by rfl) ⟨337830, by rfl⟩ : syracuseStep 900881 = 675661) B675661
theorem B900899 : Blo 397767 900899 := bstep (se 1 (by rfl) ⟨675674, by rfl⟩ : syracuseStep 900899 = 1351349) B1351349
theorem B1392419 : Blo 397767 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B671537 : Blo 397767 671537 := bstep (se 2 (by rfl) ⟨251826, by rfl⟩ : syracuseStep 671537 = 503653) B503653
theorem B2015117 : Blo 397767 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B671665 : Blo 397767 671665 := bstep (se 2 (by rfl) ⟨251874, by rfl⟩ : syracuseStep 671665 = 503749) B503749
theorem B638929 : Blo 397767 638929 := bstep (se 2 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 638929 = 479197) B479197
theorem B671699 : Blo 397767 671699 := bstep (se 1 (by rfl) ⟨503774, by rfl⟩ : syracuseStep 671699 = 1007549) B1007549
theorem B606241 : Blo 397767 606241 := bstep (se 2 (by rfl) ⟨227340, by rfl⟩ : syracuseStep 606241 = 454681) B454681
theorem B901169 : Blo 397767 901169 := bstep (se 2 (by rfl) ⟨337938, by rfl⟩ : syracuseStep 901169 = 675877) B675877
theorem B901187 : Blo 397767 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B507971 : Blo 397767 507971 := bstep (se 1 (by rfl) ⟨380978, by rfl⟩ : syracuseStep 507971 = 761957) B761957
theorem B606289 : Blo 397767 606289 := bstep (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) B454717
theorem B671827 : Blo 397767 671827 := bstep (se 1 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 671827 = 1007741) B1007741
theorem B3031181 : Blo 397767 3031181 := bstep (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) B1136693
theorem B639185 : Blo 397767 639185 := bstep (se 2 (by rfl) ⟨239694, by rfl⟩ : syracuseStep 639185 = 479389) B479389
theorem B671969 : Blo 397767 671969 := bstep (se 2 (by rfl) ⟨251988, by rfl⟩ : syracuseStep 671969 = 503977) B503977
theorem B1622285 : Blo 397767 1622285 := bstep (se 3 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 1622285 = 608357) B608357
theorem B901457 : Blo 397767 901457 := bstep (se 2 (by rfl) ⟨338046, by rfl⟩ : syracuseStep 901457 = 676093) B676093
theorem B672097 : Blo 397767 672097 := bstep (se 2 (by rfl) ⟨252036, by rfl⟩ : syracuseStep 672097 = 504073) B504073
theorem B901475 : Blo 397767 901475 := bstep (se 1 (by rfl) ⟨676106, by rfl⟩ : syracuseStep 901475 = 1352213) B1352213
theorem B672131 : Blo 397767 672131 := bstep (se 1 (by rfl) ⟨504098, by rfl⟩ : syracuseStep 672131 = 1008197) B1008197
theorem B672259 : Blo 397767 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B5128757 : Blo 397767 5128757 := bstep (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) B480821
theorem B2048611 : Blo 397767 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B901745 : Blo 397767 901745 := bstep (se 2 (by rfl) ⟨338154, by rfl⟩ : syracuseStep 901745 = 676309) B676309
theorem B901763 : Blo 397767 901763 := bstep (se 1 (by rfl) ⟨676322, by rfl⟩ : syracuseStep 901763 = 1352645) B1352645
theorem B672401 : Blo 397767 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B672529 : Blo 397767 672529 := bstep (se 2 (by rfl) ⟨252198, by rfl⟩ : syracuseStep 672529 = 504397) B504397
theorem B672563 : Blo 397767 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B902033 : Blo 397767 902033 := bstep (se 2 (by rfl) ⟨338262, by rfl⟩ : syracuseStep 902033 = 676525) B676525
theorem B2278307 : Blo 397767 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B902051 : Blo 397767 902051 := bstep (se 1 (by rfl) ⟨676538, by rfl⟩ : syracuseStep 902051 = 1353077) B1353077
theorem B672691 : Blo 397767 672691 := bstep (se 1 (by rfl) ⟨504518, by rfl⟩ : syracuseStep 672691 = 1009037) B1009037
theorem B1360867 : Blo 397767 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B672833 : Blo 397767 672833 := bstep (se 2 (by rfl) ⟨252312, by rfl⟩ : syracuseStep 672833 = 504625) B504625
theorem B607409 : Blo 397767 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B902321 : Blo 397767 902321 := bstep (se 2 (by rfl) ⟨338370, by rfl⟩ : syracuseStep 902321 = 676741) B676741
theorem B672961 : Blo 397767 672961 := bstep (se 2 (by rfl) ⟨252360, by rfl⟩ : syracuseStep 672961 = 504721) B504721
theorem B902339 : Blo 397767 902339 := bstep (se 1 (by rfl) ⟨676754, by rfl⟩ : syracuseStep 902339 = 1353509) B1353509
theorem B672995 : Blo 397767 672995 := bstep (se 1 (by rfl) ⟨504746, by rfl⟩ : syracuseStep 672995 = 1009493) B1009493
theorem B1524977 : Blo 397767 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B673123 : Blo 397767 673123 := bstep (se 1 (by rfl) ⟨504842, by rfl⟩ : syracuseStep 673123 = 1009685) B1009685
theorem B607603 : Blo 397767 607603 := bstep (se 1 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 607603 = 911405) B911405
theorem B5752205 : Blo 397767 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B902609 : Blo 397767 902609 := bstep (se 2 (by rfl) ⟨338478, by rfl⟩ : syracuseStep 902609 = 676957) B676957
theorem B902627 : Blo 397767 902627 := bstep (se 1 (by rfl) ⟨676970, by rfl⟩ : syracuseStep 902627 = 1353941) B1353941
theorem B673265 : Blo 397767 673265 := bstep (se 2 (by rfl) ⟨252474, by rfl⟩ : syracuseStep 673265 = 504949) B504949
theorem B640595 : Blo 397767 640595 := bstep (se 1 (by rfl) ⟨480446, by rfl⟩ : syracuseStep 640595 = 960893) B960893
theorem B673393 : Blo 397767 673393 := bstep (se 2 (by rfl) ⟨252522, by rfl⟩ : syracuseStep 673393 = 505045) B505045
theorem B673427 : Blo 397767 673427 := bstep (se 1 (by rfl) ⟨505070, by rfl⟩ : syracuseStep 673427 = 1010141) B1010141
theorem B902897 : Blo 397767 902897 := bstep (se 2 (by rfl) ⟨338586, by rfl⟩ : syracuseStep 902897 = 677173) B677173
theorem B902915 : Blo 397767 902915 := bstep (se 1 (by rfl) ⟨677186, by rfl⟩ : syracuseStep 902915 = 1354373) B1354373
theorem B673555 : Blo 397767 673555 := bstep (se 1 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 673555 = 1010333) B1010333
theorem B20760461 : Blo 397767 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B673697 : Blo 397767 673697 := bstep (se 2 (by rfl) ⟨252636, by rfl⟩ : syracuseStep 673697 = 505273) B505273
theorem B903185 : Blo 397767 903185 := bstep (se 2 (by rfl) ⟨338694, by rfl⟩ : syracuseStep 903185 = 677389) B677389
theorem B673825 : Blo 397767 673825 := bstep (se 2 (by rfl) ⟨252684, by rfl⟩ : syracuseStep 673825 = 505369) B505369
theorem B903203 : Blo 397767 903203 := bstep (se 1 (by rfl) ⟨677402, by rfl⟩ : syracuseStep 903203 = 1354805) B1354805
theorem B673859 : Blo 397767 673859 := bstep (se 1 (by rfl) ⟨505394, by rfl⟩ : syracuseStep 673859 = 1010789) B1010789
theorem B2312333 : Blo 397767 2312333 := bstep (se 3 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 2312333 = 867125) B867125
theorem B2050211 : Blo 397767 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B673987 : Blo 397767 673987 := bstep (se 1 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 673987 = 1010981) B1010981
theorem B1231085 : Blo 397767 1231085 := bstep (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) B461657
theorem B903473 : Blo 397767 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B903491 : Blo 397767 903491 := bstep (se 1 (by rfl) ⟨677618, by rfl⟩ : syracuseStep 903491 = 1355237) B1355237
theorem B674129 : Blo 397767 674129 := bstep (se 2 (by rfl) ⟨252798, by rfl⟩ : syracuseStep 674129 = 505597) B505597
theorem B641441 : Blo 397767 641441 := bstep (se 2 (by rfl) ⟨240540, by rfl⟩ : syracuseStep 641441 = 481081) B481081
theorem B674257 : Blo 397767 674257 := bstep (se 2 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 674257 = 505693) B505693
theorem B608723 : Blo 397767 608723 := bstep (se 1 (by rfl) ⟨456542, by rfl⟩ : syracuseStep 608723 = 913085) B913085
theorem B674291 : Blo 397767 674291 := bstep (se 1 (by rfl) ⟨505718, by rfl⟩ : syracuseStep 674291 = 1011437) B1011437
theorem B903761 : Blo 397767 903761 := bstep (se 2 (by rfl) ⟨338910, by rfl⟩ : syracuseStep 903761 = 677821) B677821
theorem B903779 : Blo 397767 903779 := bstep (se 1 (by rfl) ⟨677834, by rfl⟩ : syracuseStep 903779 = 1355669) B1355669
theorem B674419 : Blo 397767 674419 := bstep (se 1 (by rfl) ⟨505814, by rfl⟩ : syracuseStep 674419 = 1011629) B1011629
theorem B2018033 : Blo 397767 2018033 := bstep (se 2 (by rfl) ⟨756762, by rfl⟩ : syracuseStep 2018033 = 1513525) B1513525
theorem B674561 : Blo 397767 674561 := bstep (se 2 (by rfl) ⟨252960, by rfl⟩ : syracuseStep 674561 = 505921) B505921
theorem B42257173 : Blo 397767 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B674689 : Blo 397767 674689 := bstep (se 2 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 674689 = 506017) B506017
theorem B641953 : Blo 397767 641953 := bstep (se 2 (by rfl) ⟨240732, by rfl⟩ : syracuseStep 641953 = 481465) B481465
theorem B674723 : Blo 397767 674723 := bstep (se 1 (by rfl) ⟨506042, by rfl⟩ : syracuseStep 674723 = 1012085) B1012085
theorem B3034097 : Blo 397767 3034097 := bstep (se 2 (by rfl) ⟨1137786, by rfl⟩ : syracuseStep 3034097 = 2275573) B2275573
theorem B1133585 : Blo 397767 1133585 := bstep (se 2 (by rfl) ⟨425094, by rfl⟩ : syracuseStep 1133585 = 850189) B850189
theorem B674851 : Blo 397767 674851 := bstep (se 1 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 674851 = 1012277) B1012277
theorem B674993 : Blo 397767 674993 := bstep (se 2 (by rfl) ⟨253122, by rfl⟩ : syracuseStep 674993 = 506245) B506245
theorem B1133777 : Blo 397767 1133777 := bstep (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) B850333
theorem B675121 : Blo 397767 675121 := bstep (se 2 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 675121 = 506341) B506341
theorem B675155 : Blo 397767 675155 := bstep (se 1 (by rfl) ⟨506366, by rfl⟩ : syracuseStep 675155 = 1012733) B1012733
theorem B675283 : Blo 397767 675283 := bstep (se 1 (by rfl) ⟨506462, by rfl⟩ : syracuseStep 675283 = 1012925) B1012925
theorem B642563 : Blo 397767 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B2870797 : Blo 397767 2870797 := bstep (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) B1076549
theorem B675425 : Blo 397767 675425 := bstep (se 2 (by rfl) ⟨253284, by rfl⟩ : syracuseStep 675425 = 506569) B506569
theorem B675553 : Blo 397767 675553 := bstep (se 2 (by rfl) ⟨253332, by rfl⟩ : syracuseStep 675553 = 506665) B506665
theorem B675587 : Blo 397767 675587 := bstep (se 1 (by rfl) ⟨506690, by rfl⟩ : syracuseStep 675587 = 1013381) B1013381
theorem B675715 : Blo 397767 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B4575203 : Blo 397767 4575203 := bstep (se 1 (by rfl) ⟨3431402, by rfl⟩ : syracuseStep 4575203 = 6862805) B6862805
theorem B675857 : Blo 397767 675857 := bstep (se 2 (by rfl) ⟨253446, by rfl⟩ : syracuseStep 675857 = 506893) B506893
theorem B8802325 : Blo 397767 8802325 := bstep (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) B412609
theorem B675985 : Blo 397767 675985 := bstep (se 2 (by rfl) ⟨253494, by rfl⟩ : syracuseStep 675985 = 506989) B506989
theorem B2019491 : Blo 397767 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B1134769 : Blo 397767 1134769 := bstep (se 2 (by rfl) ⟨425538, by rfl⟩ : syracuseStep 1134769 = 851077) B851077
theorem B676019 : Blo 397767 676019 := bstep (se 1 (by rfl) ⟨507014, by rfl⟩ : syracuseStep 676019 = 1014029) B1014029
theorem B676147 : Blo 397767 676147 := bstep (se 1 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 676147 = 1014221) B1014221
theorem B676289 : Blo 397767 676289 := bstep (se 2 (by rfl) ⟨253608, by rfl⟩ : syracuseStep 676289 = 507217) B507217
theorem B1135043 : Blo 397767 1135043 := bstep (se 1 (by rfl) ⟨851282, by rfl⟩ : syracuseStep 1135043 = 1702565) B1702565
theorem B643555 : Blo 397767 643555 := bstep (se 1 (by rfl) ⟨482666, by rfl⟩ : syracuseStep 643555 = 965333) B965333
theorem B676417 : Blo 397767 676417 := bstep (se 2 (by rfl) ⟨253656, by rfl⟩ : syracuseStep 676417 = 507313) B507313
theorem B676451 : Blo 397767 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B1135235 : Blo 397767 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B676579 : Blo 397767 676579 := bstep (se 1 (by rfl) ⟨507434, by rfl⟩ : syracuseStep 676579 = 1014869) B1014869
theorem B676721 : Blo 397767 676721 := bstep (se 2 (by rfl) ⟨253770, by rfl⟩ : syracuseStep 676721 = 507541) B507541
theorem B480115 : Blo 397767 480115 := bstep (se 1 (by rfl) ⟨360086, by rfl⟩ : syracuseStep 480115 = 720173) B720173
theorem B2020301 : Blo 397767 2020301 := bstep (se 3 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 2020301 = 757613) B757613
theorem B676849 : Blo 397767 676849 := bstep (se 2 (by rfl) ⟨253818, by rfl⟩ : syracuseStep 676849 = 507637) B507637
theorem B676883 : Blo 397767 676883 := bstep (se 1 (by rfl) ⟨507662, by rfl⟩ : syracuseStep 676883 = 1015325) B1015325
theorem B447619 : Blo 397767 447619 := bstep (se 1 (by rfl) ⟨335714, by rfl⟩ : syracuseStep 447619 = 671429) B671429
theorem B677011 : Blo 397767 677011 := bstep (se 1 (by rfl) ⟨507758, by rfl⟩ : syracuseStep 677011 = 1015517) B1015517
theorem B447763 : Blo 397767 447763 := bstep (se 1 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 447763 = 671645) B671645
theorem B677153 : Blo 397767 677153 := bstep (se 2 (by rfl) ⟨253932, by rfl⟩ : syracuseStep 677153 = 507865) B507865
theorem B2053453 : Blo 397767 2053453 := bstep (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) B770045
theorem B677281 : Blo 397767 677281 := bstep (se 2 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 677281 = 507961) B507961
theorem B447907 : Blo 397767 447907 := bstep (se 1 (by rfl) ⟨335930, by rfl⟩ : syracuseStep 447907 = 671861) B671861
theorem B1136045 : Blo 397767 1136045 := bstep (se 3 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 1136045 = 426017) B426017
theorem B677315 : Blo 397767 677315 := bstep (se 1 (by rfl) ⟨507986, by rfl⟩ : syracuseStep 677315 = 1015973) B1015973
theorem B448051 : Blo 397767 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B677443 : Blo 397767 677443 := bstep (se 1 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 677443 = 1016165) B1016165
theorem B1136227 : Blo 397767 1136227 := bstep (se 1 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 1136227 = 1704341) B1704341
theorem B448195 : Blo 397767 448195 := bstep (se 1 (by rfl) ⟨336146, by rfl⟩ : syracuseStep 448195 = 672293) B672293
theorem B677585 : Blo 397767 677585 := bstep (se 2 (by rfl) ⟨254094, by rfl⟩ : syracuseStep 677585 = 508189) B508189
theorem B14636771 : Blo 397767 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B677713 : Blo 397767 677713 := bstep (se 2 (by rfl) ⟨254142, by rfl⟩ : syracuseStep 677713 = 508285) B508285
theorem B448339 : Blo 397767 448339 := bstep (se 1 (by rfl) ⟨336254, by rfl⟩ : syracuseStep 448339 = 672509) B672509
theorem B677747 : Blo 397767 677747 := bstep (se 1 (by rfl) ⟨508310, by rfl⟩ : syracuseStep 677747 = 1016621) B1016621
theorem B448483 : Blo 397767 448483 := bstep (se 1 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 448483 = 672725) B672725
theorem B677875 : Blo 397767 677875 := bstep (se 1 (by rfl) ⟨508406, by rfl⟩ : syracuseStep 677875 = 1016813) B1016813
theorem B2152453 : Blo 397767 2152453 := bstep (se 4 (by rfl) ⟨201792, by rfl⟩ : syracuseStep 2152453 = 403585) B403585
theorem B1136717 : Blo 397767 1136717 := bstep (se 3 (by rfl) ⟨213134, by rfl⟩ : syracuseStep 1136717 = 426269) B426269
theorem B448627 : Blo 397767 448627 := bstep (se 1 (by rfl) ⟨336470, by rfl⟩ : syracuseStep 448627 = 672941) B672941
theorem B2087117 : Blo 397767 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B448771 : Blo 397767 448771 := bstep (se 1 (by rfl) ⟨336578, by rfl⟩ : syracuseStep 448771 = 673157) B673157
theorem B514307 : Blo 397767 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B448915 : Blo 397767 448915 := bstep (se 1 (by rfl) ⟨336686, by rfl⟩ : syracuseStep 448915 = 673373) B673373
theorem B809489 : Blo 397767 809489 := bstep (se 2 (by rfl) ⟨303558, by rfl⟩ : syracuseStep 809489 = 607117) B607117
theorem B449059 : Blo 397767 449059 := bstep (se 1 (by rfl) ⟨336794, by rfl⟩ : syracuseStep 449059 = 673589) B673589
theorem B481907 : Blo 397767 481907 := bstep (se 1 (by rfl) ⟨361430, by rfl⟩ : syracuseStep 481907 = 722861) B722861
theorem B449203 : Blo 397767 449203 := bstep (se 1 (by rfl) ⟨336902, by rfl⟩ : syracuseStep 449203 = 673805) B673805
theorem B449347 : Blo 397767 449347 := bstep (se 1 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 449347 = 674021) B674021
theorem B3431267 : Blo 397767 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B449491 : Blo 397767 449491 := bstep (se 1 (by rfl) ⟨337118, by rfl⟩ : syracuseStep 449491 = 674237) B674237
theorem B3824653 : Blo 397767 3824653 := bstep (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) B1434245
theorem B3300365 : Blo 397767 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B449635 : Blo 397767 449635 := bstep (se 1 (by rfl) ⟨337226, by rfl⟩ : syracuseStep 449635 = 674453) B674453
theorem B1137901 : Blo 397767 1137901 := bstep (se 3 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 1137901 = 426713) B426713
theorem B449779 : Blo 397767 449779 := bstep (se 1 (by rfl) ⟨337334, by rfl⟩ : syracuseStep 449779 = 674669) B674669
theorem B449923 : Blo 397767 449923 := bstep (se 1 (by rfl) ⟨337442, by rfl⟩ : syracuseStep 449923 = 674885) B674885
theorem B450067 : Blo 397767 450067 := bstep (se 1 (by rfl) ⟨337550, by rfl⟩ : syracuseStep 450067 = 675101) B675101
theorem B450211 : Blo 397767 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B2023217 : Blo 397767 2023217 := bstep (se 2 (by rfl) ⟨758706, by rfl⟩ : syracuseStep 2023217 = 1517413) B1517413
theorem B450355 : Blo 397767 450355 := bstep (se 1 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 450355 = 675533) B675533
theorem B450499 : Blo 397767 450499 := bstep (se 1 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 450499 = 675749) B675749
theorem B450643 : Blo 397767 450643 := bstep (se 1 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 450643 = 675965) B675965
theorem B647297 : Blo 397767 647297 := bstep (se 2 (by rfl) ⟨242736, by rfl⟩ : syracuseStep 647297 = 485473) B485473
theorem B1007761 : Blo 397767 1007761 := bstep (se 2 (by rfl) ⟨377910, by rfl⟩ : syracuseStep 1007761 = 755821) B755821
theorem B1466545 : Blo 397767 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B2154701 : Blo 397767 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B450787 : Blo 397767 450787 := bstep (se 1 (by rfl) ⟨338090, by rfl⟩ : syracuseStep 450787 = 676181) B676181
theorem B1138961 : Blo 397767 1138961 := bstep (se 2 (by rfl) ⟨427110, by rfl⟩ : syracuseStep 1138961 = 854221) B854221
theorem B1532195 : Blo 397767 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B450931 : Blo 397767 450931 := bstep (se 1 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 450931 = 676397) B676397
theorem B1008035 : Blo 397767 1008035 := bstep (se 1 (by rfl) ⟨756026, by rfl⟩ : syracuseStep 1008035 = 1512053) B1512053
theorem B451075 : Blo 397767 451075 := bstep (se 1 (by rfl) ⟨338306, by rfl⟩ : syracuseStep 451075 = 676613) B676613
theorem B1204753 : Blo 397767 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B3662405 : Blo 397767 3662405 := bstep (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) B686701
theorem B1008227 : Blo 397767 1008227 := bstep (se 1 (by rfl) ⟨756170, by rfl⟩ : syracuseStep 1008227 = 1512341) B1512341
theorem B451219 : Blo 397767 451219 := bstep (se 1 (by rfl) ⟨338414, by rfl⟩ : syracuseStep 451219 = 676829) B676829
theorem B451363 : Blo 397767 451363 := bstep (se 1 (by rfl) ⟨338522, by rfl⟩ : syracuseStep 451363 = 677045) B677045
theorem B910129 : Blo 397767 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B680755 : Blo 397767 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B1139633 : Blo 397767 1139633 := bstep (se 2 (by rfl) ⟨427362, by rfl⟩ : syracuseStep 1139633 = 854725) B854725
theorem B451507 : Blo 397767 451507 := bstep (se 1 (by rfl) ⟨338630, by rfl⟩ : syracuseStep 451507 = 677261) B677261
theorem B680899 : Blo 397767 680899 := bstep (se 1 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 680899 = 1021349) B1021349
theorem B812035 : Blo 397767 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B451651 : Blo 397767 451651 := bstep (se 1 (by rfl) ⟨338738, by rfl⟩ : syracuseStep 451651 = 677477) B677477
theorem B3826885 : Blo 397767 3826885 := bstep (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) B717541
theorem B451795 : Blo 397767 451795 := bstep (se 1 (by rfl) ⟨338846, by rfl⟩ : syracuseStep 451795 = 677693) B677693
theorem B2024675 : Blo 397767 2024675 := bstep (se 1 (by rfl) ⟨1518506, by rfl⟩ : syracuseStep 2024675 = 3037013) B3037013
theorem B451939 : Blo 397767 451939 := bstep (se 1 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 451939 = 677909) B677909
theorem B1009169 : Blo 397767 1009169 := bstep (se 2 (by rfl) ⟨378438, by rfl⟩ : syracuseStep 1009169 = 756877) B756877
theorem B1009219 : Blo 397767 1009219 := bstep (se 1 (by rfl) ⟨756914, by rfl⟩ : syracuseStep 1009219 = 1513829) B1513829
theorem B2287237 : Blo 397767 2287237 := bstep (se 4 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 2287237 = 428857) B428857
theorem B1140419 : Blo 397767 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B1009361 : Blo 397767 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B2025485 : Blo 397767 2025485 := bstep (se 3 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 2025485 = 759557) B759557
theorem B1140749 : Blo 397767 1140749 := bstep (se 3 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 1140749 = 427781) B427781
theorem B1140817 : Blo 397767 1140817 := bstep (se 2 (by rfl) ⟨427806, by rfl⟩ : syracuseStep 1140817 = 855613) B855613
theorem B1108081 : Blo 397767 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B1075427 : Blo 397767 1075427 := bstep (se 1 (by rfl) ⟨806570, by rfl⟩ : syracuseStep 1075427 = 1613141) B1613141
theorem B10414307 : Blo 397767 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B1042723 : Blo 397767 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B1141091 : Blo 397767 1141091 := bstep (se 1 (by rfl) ⟨855818, by rfl⟩ : syracuseStep 1141091 = 1711637) B1711637
theorem B2550179 : Blo 397767 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B3631601 : Blo 397767 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B1370609 : Blo 397767 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B3238469 : Blo 397767 3238469 := bstep (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) B607213
theorem B1436237 : Blo 397767 1436237 := bstep (se 3 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 1436237 = 538589) B538589
theorem B1010353 : Blo 397767 1010353 := bstep (se 2 (by rfl) ⟨378882, by rfl⟩ : syracuseStep 1010353 = 757765) B757765
theorem B682897 : Blo 397767 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B1010627 : Blo 397767 1010627 := bstep (se 1 (by rfl) ⟨757970, by rfl⟩ : syracuseStep 1010627 = 1515941) B1515941
theorem B1010819 : Blo 397767 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B814225 : Blo 397767 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B1141933 : Blo 397767 1141933 := bstep (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) B428225
theorem B1142093 : Blo 397767 1142093 := bstep (se 3 (by rfl) ⟨214142, by rfl⟩ : syracuseStep 1142093 = 428285) B428285
theorem B1142275 : Blo 397767 1142275 := bstep (se 1 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 1142275 = 1713413) B1713413
theorem B2059853 : Blo 397767 2059853 := bstep (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) B772445
theorem B2551409 : Blo 397767 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B1699505 : Blo 397767 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B4419269 : Blo 397767 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B8613773 : Blo 397767 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B1077155 : Blo 397767 1077155 := bstep (se 1 (by rfl) ⟨807866, by rfl⟩ : syracuseStep 1077155 = 1615733) B1615733
theorem B1011761 : Blo 397767 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B1011811 : Blo 397767 1011811 := bstep (se 1 (by rfl) ⟨758858, by rfl⟩ : syracuseStep 1011811 = 1517717) B1517717
theorem B4321421 : Blo 397767 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B1929379 : Blo 397767 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B1011953 : Blo 397767 1011953 := bstep (se 2 (by rfl) ⟨379482, by rfl⟩ : syracuseStep 1011953 = 758965) B758965
theorem B717059 : Blo 397767 717059 := bstep (se 1 (by rfl) ⟨537794, by rfl⟩ : syracuseStep 717059 = 1075589) B1075589
theorem B1372717 : Blo 397767 1372717 := bstep (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) B514769
theorem B2028401 : Blo 397767 2028401 := bstep (se 2 (by rfl) ⟨760650, by rfl⟩ : syracuseStep 2028401 = 1521301) B1521301
theorem B1143665 : Blo 397767 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B914435 : Blo 397767 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B1012945 : Blo 397767 1012945 := bstep (se 2 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 1012945 = 759709) B759709
theorem B521491 : Blo 397767 521491 := bstep (se 1 (by rfl) ⟨391118, by rfl⟩ : syracuseStep 521491 = 782237) B782237
theorem B1013219 : Blo 397767 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B685633 : Blo 397767 685633 := bstep (se 2 (by rfl) ⟨257112, by rfl⟩ : syracuseStep 685633 = 514225) B514225
theorem B1439309 : Blo 397767 1439309 := bstep (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) B539741
theorem B1013411 : Blo 397767 1013411 := bstep (se 1 (by rfl) ⟨760058, by rfl⟩ : syracuseStep 1013411 = 1520117) B1520117
theorem B1210243 : Blo 397767 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B7796621 : Blo 397767 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B2553869 : Blo 397767 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B1701965 : Blo 397767 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B1276013 : Blo 397767 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B686291 : Blo 397767 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B2029859 : Blo 397767 2029859 := bstep (se 1 (by rfl) ⟨1522394, by rfl⟩ : syracuseStep 2029859 = 3044789) B3044789
theorem B686593 : Blo 397767 686593 := bstep (se 2 (by rfl) ⟨257472, by rfl⟩ : syracuseStep 686593 = 514945) B514945
theorem B1014353 : Blo 397767 1014353 := bstep (se 2 (by rfl) ⟨380382, by rfl⟩ : syracuseStep 1014353 = 760765) B760765
theorem B916067 : Blo 397767 916067 := bstep (se 1 (by rfl) ⟨687050, by rfl⟩ : syracuseStep 916067 = 1374101) B1374101
theorem B1014403 : Blo 397767 1014403 := bstep (se 1 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 1014403 = 1521605) B1521605
theorem B1014545 : Blo 397767 1014545 := bstep (se 2 (by rfl) ⟨380454, by rfl⟩ : syracuseStep 1014545 = 760909) B760909
theorem B1080173 : Blo 397767 1080173 := bstep (se 3 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 1080173 = 405065) B405065
theorem B6814691 : Blo 397767 6814691 := bstep (se 1 (by rfl) ⟨5111018, by rfl⟩ : syracuseStep 6814691 = 10222037) B10222037
theorem B2030669 : Blo 397767 2030669 := bstep (se 3 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 2030669 = 761501) B761501
theorem B851153 : Blo 397767 851153 := bstep (se 2 (by rfl) ⟨319182, by rfl⟩ : syracuseStep 851153 = 638365) B638365
theorem B3079565 : Blo 397767 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1342925 : Blo 397767 1342925 := bstep (se 3 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 1342925 = 503597) B503597
theorem B1342979 : Blo 397767 1342979 := bstep (se 1 (by rfl) ⟨1007234, by rfl⟩ : syracuseStep 1342979 = 2014469) B2014469
theorem B1703537 : Blo 397767 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B1277603 : Blo 397767 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B1015537 : Blo 397767 1015537 := bstep (se 2 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 1015537 = 761653) B761653
theorem B1343249 : Blo 397767 1343249 := bstep (se 2 (by rfl) ⟨503718, by rfl⟩ : syracuseStep 1343249 = 1007437) B1007437
theorem B720785 : Blo 397767 720785 := bstep (se 2 (by rfl) ⟨270294, by rfl⟩ : syracuseStep 720785 = 540589) B540589
theorem B3702725 : Blo 397767 3702725 := bstep (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) B694261
theorem B1081297 : Blo 397767 1081297 := bstep (se 2 (by rfl) ⟨405486, by rfl⟩ : syracuseStep 1081297 = 810973) B810973
theorem B2162659 : Blo 397767 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B1081523 : Blo 397767 1081523 := bstep (se 1 (by rfl) ⟨811142, by rfl⟩ : syracuseStep 1081523 = 1622285) B1622285
theorem B1343681 : Blo 397767 1343681 := bstep (se 2 (by rfl) ⟨503880, by rfl⟩ : syracuseStep 1343681 = 1007761) B1007761
theorem B2490689 : Blo 397767 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B2031965 : Blo 397767 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B1245719 : Blo 397767 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1704493 : Blo 397767 1704493 := bstep (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) B639185
theorem B1606337 : Blo 397767 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B1704665 : Blo 397767 1704665 := bstep (se 2 (by rfl) ⟨639249, by rfl⟩ : syracuseStep 1704665 = 1278499) B1278499
theorem B1344221 : Blo 397767 1344221 := bstep (se 3 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 1344221 = 504083) B504083
theorem B1016651 : Blo 397767 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B3834803 : Blo 397767 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B6489011 : Blo 397767 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B1213505 : Blo 397767 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B853067 : Blo 397767 853067 := bstep (se 1 (by rfl) ⟨639800, by rfl⟩ : syracuseStep 853067 = 1279601) B1279601
theorem B1541555 : Blo 397767 1541555 := bstep (se 1 (by rfl) ⟨1156166, by rfl⟩ : syracuseStep 1541555 = 2312333) B2312333
theorem B4556249 : Blo 397767 4556249 := bstep (se 2 (by rfl) ⟨1708593, by rfl⟩ : syracuseStep 4556249 = 3417187) B3417187
theorem B427627 : Blo 397767 427627 := bstep (se 1 (by rfl) ⟨320720, by rfl⟩ : syracuseStep 427627 = 641441) B641441
theorem B1443587 : Blo 397767 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B853811 : Blo 397767 853811 := bstep (se 1 (by rfl) ⟨640358, by rfl⟩ : syracuseStep 853811 = 1280717) B1280717
theorem B1345355 : Blo 397767 1345355 := bstep (se 1 (by rfl) ⟨1009016, by rfl⟩ : syracuseStep 1345355 = 2018033) B2018033
theorem B755723 : Blo 397767 755723 := bstep (se 1 (by rfl) ⟨566792, by rfl⟩ : syracuseStep 755723 = 1133585) B1133585
theorem B1345625 : Blo 397767 1345625 := bstep (se 2 (by rfl) ⟨504609, by rfl⟩ : syracuseStep 1345625 = 1009219) B1009219
theorem B3049649 : Blo 397767 3049649 := bstep (se 2 (by rfl) ⟨1143618, by rfl⟩ : syracuseStep 3049649 = 2287237) B2287237
theorem B755905 : Blo 397767 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B1706305 : Blo 397767 1706305 := bstep (se 2 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 1706305 = 1279729) B1279729
theorem B428375 : Blo 397767 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B1575299 : Blo 397767 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B2165123 : Blo 397767 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B919961 : Blo 397767 919961 := bstep (se 2 (by rfl) ⟨344985, by rfl⟩ : syracuseStep 919961 = 689971) B689971
theorem B723467 : Blo 397767 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B756353 : Blo 397767 756353 := bstep (se 2 (by rfl) ⟨283632, by rfl⟩ : syracuseStep 756353 = 567265) B567265
theorem B3050135 : Blo 397767 3050135 := bstep (se 1 (by rfl) ⟨2287601, by rfl⟩ : syracuseStep 3050135 = 4575203) B4575203
theorem B854707 : Blo 397767 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B1346327 : Blo 397767 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B1477441 : Blo 397767 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B723863 : Blo 397767 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B756695 : Blo 397767 756695 := bstep (se 1 (by rfl) ⟨567521, by rfl⟩ : syracuseStep 756695 = 1135043) B1135043
theorem B1346867 : Blo 397767 1346867 := bstep (se 1 (by rfl) ⟨1010150, by rfl⟩ : syracuseStep 1346867 = 2020301) B2020301
theorem B2559383 : Blo 397767 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B1347137 : Blo 397767 1347137 := bstep (se 2 (by rfl) ⟨505176, by rfl⟩ : syracuseStep 1347137 = 1010353) B1010353
theorem B757363 : Blo 397767 757363 := bstep (se 1 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 757363 = 1136045) B1136045
theorem B855767 : Blo 397767 855767 := bstep (se 1 (by rfl) ⟨641825, by rfl⟩ : syracuseStep 855767 = 1283651) B1283651
theorem B855937 : Blo 397767 855937 := bstep (se 2 (by rfl) ⟨320976, by rfl⟩ : syracuseStep 855937 = 641953) B641953
theorem B1707979 : Blo 397767 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B757811 : Blo 397767 757811 := bstep (se 1 (by rfl) ⟨568358, by rfl⟩ : syracuseStep 757811 = 1136717) B1136717
theorem B757849 : Blo 397767 757849 := bstep (se 2 (by rfl) ⟨284193, by rfl⟩ : syracuseStep 757849 = 568387) B568387
theorem B1347677 : Blo 397767 1347677 := bstep (se 3 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 1347677 = 505379) B505379
theorem B1085633 : Blo 397767 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B3248333 : Blo 397767 3248333 := bstep (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) B1218125
theorem B856279 : Blo 397767 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B1708253 : Blo 397767 1708253 := bstep (se 3 (by rfl) ⟨320297, by rfl⟩ : syracuseStep 1708253 = 640595) B640595
theorem B397771 : Blo 397767 397771 := bstep (se 1 (by rfl) ⟨298328, by rfl⟩ : syracuseStep 397771 = 596657) B596657
theorem B397783 : Blo 397767 397783 := bstep (se 1 (by rfl) ⟨298337, by rfl⟩ : syracuseStep 397783 = 596675) B596675
theorem B397803 : Blo 397767 397803 := bstep (se 1 (by rfl) ⟨298352, by rfl⟩ : syracuseStep 397803 = 596705) B596705
theorem B397815 : Blo 397767 397815 := bstep (se 1 (by rfl) ⟨298361, by rfl⟩ : syracuseStep 397815 = 596723) B596723
theorem B397835 : Blo 397767 397835 := bstep (se 1 (by rfl) ⟨298376, by rfl⟩ : syracuseStep 397835 = 596753) B596753
theorem B397847 : Blo 397767 397847 := bstep (se 1 (by rfl) ⟨298385, by rfl⟩ : syracuseStep 397847 = 596771) B596771
theorem B758297 : Blo 397767 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B397867 : Blo 397767 397867 := bstep (se 1 (by rfl) ⟨298400, by rfl⟩ : syracuseStep 397867 = 596801) B596801
theorem B397879 : Blo 397767 397879 := bstep (se 1 (by rfl) ⟨298409, by rfl⟩ : syracuseStep 397879 = 596819) B596819
theorem B1282625 : Blo 397767 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B397899 : Blo 397767 397899 := bstep (se 1 (by rfl) ⟨298424, by rfl⟩ : syracuseStep 397899 = 596849) B596849
theorem B397911 : Blo 397767 397911 := bstep (se 1 (by rfl) ⟨298433, by rfl⟩ : syracuseStep 397911 = 596867) B596867
theorem B1151581 : Blo 397767 1151581 := bstep (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) B431843
theorem B397931 : Blo 397767 397931 := bstep (se 1 (by rfl) ⟨298448, by rfl⟩ : syracuseStep 397931 = 596897) B596897
theorem B397943 : Blo 397767 397943 := bstep (se 1 (by rfl) ⟨298457, by rfl⟩ : syracuseStep 397943 = 596915) B596915
theorem B1512067 : Blo 397767 1512067 := bstep (se 1 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 1512067 = 2268101) B2268101
theorem B397963 : Blo 397767 397963 := bstep (se 1 (by rfl) ⟨298472, by rfl⟩ : syracuseStep 397963 = 596945) B596945
theorem B397975 : Blo 397767 397975 := bstep (se 1 (by rfl) ⟨298481, by rfl⟩ : syracuseStep 397975 = 596963) B596963
theorem B397995 : Blo 397767 397995 := bstep (se 1 (by rfl) ⟨298496, by rfl⟩ : syracuseStep 397995 = 596993) B596993
theorem B2200243 : Blo 397767 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B398007 : Blo 397767 398007 := bstep (se 1 (by rfl) ⟨298505, by rfl⟩ : syracuseStep 398007 = 597011) B597011
theorem B398027 : Blo 397767 398027 := bstep (se 1 (by rfl) ⟨298520, by rfl⟩ : syracuseStep 398027 = 597041) B597041
theorem B398039 : Blo 397767 398039 := bstep (se 1 (by rfl) ⟨298529, by rfl⟩ : syracuseStep 398039 = 597059) B597059
theorem B398059 : Blo 397767 398059 := bstep (se 1 (by rfl) ⟨298544, by rfl⟩ : syracuseStep 398059 = 597089) B597089
theorem B398071 : Blo 397767 398071 := bstep (se 1 (by rfl) ⟨298553, by rfl⟩ : syracuseStep 398071 = 597107) B597107
theorem B398091 : Blo 397767 398091 := bstep (se 1 (by rfl) ⟨298568, by rfl⟩ : syracuseStep 398091 = 597137) B597137
theorem B398103 : Blo 397767 398103 := bstep (se 1 (by rfl) ⟨298577, by rfl⟩ : syracuseStep 398103 = 597155) B597155
theorem B398123 : Blo 397767 398123 := bstep (se 1 (by rfl) ⟨298592, by rfl⟩ : syracuseStep 398123 = 597185) B597185
theorem B398135 : Blo 397767 398135 := bstep (se 1 (by rfl) ⟨298601, by rfl⟩ : syracuseStep 398135 = 597203) B597203
theorem B398155 : Blo 397767 398155 := bstep (se 1 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 398155 = 597233) B597233
theorem B398167 : Blo 397767 398167 := bstep (se 1 (by rfl) ⟨298625, by rfl⟩ : syracuseStep 398167 = 597251) B597251
theorem B398187 : Blo 397767 398187 := bstep (se 1 (by rfl) ⟨298640, by rfl⟩ : syracuseStep 398187 = 597281) B597281
theorem B398199 : Blo 397767 398199 := bstep (se 1 (by rfl) ⟨298649, by rfl⟩ : syracuseStep 398199 = 597299) B597299
theorem B398219 : Blo 397767 398219 := bstep (se 1 (by rfl) ⟨298664, by rfl⟩ : syracuseStep 398219 = 597329) B597329
theorem B398231 : Blo 397767 398231 := bstep (se 1 (by rfl) ⟨298673, by rfl⟩ : syracuseStep 398231 = 597347) B597347
theorem B398251 : Blo 397767 398251 := bstep (se 1 (by rfl) ⟨298688, by rfl⟩ : syracuseStep 398251 = 597377) B597377
theorem B1512371 : Blo 397767 1512371 := bstep (se 1 (by rfl) ⟨1134278, by rfl⟩ : syracuseStep 1512371 = 2268557) B2268557
theorem B398263 : Blo 397767 398263 := bstep (se 1 (by rfl) ⟨298697, by rfl⟩ : syracuseStep 398263 = 597395) B597395
theorem B398283 : Blo 397767 398283 := bstep (se 1 (by rfl) ⟨298712, by rfl⟩ : syracuseStep 398283 = 597425) B597425
theorem B398295 : Blo 397767 398295 := bstep (se 1 (by rfl) ⟨298721, by rfl⟩ : syracuseStep 398295 = 597443) B597443
theorem B2200537 : Blo 397767 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B398315 : Blo 397767 398315 := bstep (se 1 (by rfl) ⟨298736, by rfl⟩ : syracuseStep 398315 = 597473) B597473
theorem B398327 : Blo 397767 398327 := bstep (se 1 (by rfl) ⟨298745, by rfl⟩ : syracuseStep 398327 = 597491) B597491
theorem B398347 : Blo 397767 398347 := bstep (se 1 (by rfl) ⟨298760, by rfl⟩ : syracuseStep 398347 = 597521) B597521
theorem B857099 : Blo 397767 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B398359 : Blo 397767 398359 := bstep (se 1 (by rfl) ⟨298769, by rfl⟩ : syracuseStep 398359 = 597539) B597539
theorem B398379 : Blo 397767 398379 := bstep (se 1 (by rfl) ⟨298784, by rfl⟩ : syracuseStep 398379 = 597569) B597569
theorem B398391 : Blo 397767 398391 := bstep (se 1 (by rfl) ⟨298793, by rfl⟩ : syracuseStep 398391 = 597587) B597587
theorem B398411 : Blo 397767 398411 := bstep (se 1 (by rfl) ⟨298808, by rfl⟩ : syracuseStep 398411 = 597617) B597617
theorem B398423 : Blo 397767 398423 := bstep (se 1 (by rfl) ⟨298817, by rfl⟩ : syracuseStep 398423 = 597635) B597635
theorem B398443 : Blo 397767 398443 := bstep (se 1 (by rfl) ⟨298832, by rfl⟩ : syracuseStep 398443 = 597665) B597665
theorem B398455 : Blo 397767 398455 := bstep (se 1 (by rfl) ⟨298841, by rfl⟩ : syracuseStep 398455 = 597683) B597683
theorem B398475 : Blo 397767 398475 := bstep (se 1 (by rfl) ⟨298856, by rfl⟩ : syracuseStep 398475 = 597713) B597713
theorem B398487 : Blo 397767 398487 := bstep (se 1 (by rfl) ⟨298865, by rfl⟩ : syracuseStep 398487 = 597731) B597731
theorem B4854935 : Blo 397767 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B398507 : Blo 397767 398507 := bstep (se 1 (by rfl) ⟨298880, by rfl⟩ : syracuseStep 398507 = 597761) B597761
theorem B398519 : Blo 397767 398519 := bstep (se 1 (by rfl) ⟨298889, by rfl⟩ : syracuseStep 398519 = 597779) B597779
theorem B398539 : Blo 397767 398539 := bstep (se 1 (by rfl) ⟨298904, by rfl⟩ : syracuseStep 398539 = 597809) B597809
theorem B1348811 : Blo 397767 1348811 := bstep (se 1 (by rfl) ⟨1011608, by rfl⟩ : syracuseStep 1348811 = 2023217) B2023217
theorem B398551 : Blo 397767 398551 := bstep (se 1 (by rfl) ⟨298913, by rfl⟩ : syracuseStep 398551 = 597827) B597827
theorem B398571 : Blo 397767 398571 := bstep (se 1 (by rfl) ⟨298928, by rfl⟩ : syracuseStep 398571 = 597857) B597857
theorem B398583 : Blo 397767 398583 := bstep (se 1 (by rfl) ⟨298937, by rfl⟩ : syracuseStep 398583 = 597875) B597875
theorem B759041 : Blo 397767 759041 := bstep (se 2 (by rfl) ⟨284640, by rfl⟩ : syracuseStep 759041 = 569281) B569281
theorem B398603 : Blo 397767 398603 := bstep (se 1 (by rfl) ⟨298952, by rfl⟩ : syracuseStep 398603 = 597905) B597905
theorem B398615 : Blo 397767 398615 := bstep (se 1 (by rfl) ⟨298961, by rfl⟩ : syracuseStep 398615 = 597923) B597923
theorem B398635 : Blo 397767 398635 := bstep (se 1 (by rfl) ⟨298976, by rfl⟩ : syracuseStep 398635 = 597953) B597953
theorem B398647 : Blo 397767 398647 := bstep (se 1 (by rfl) ⟨298985, by rfl⟩ : syracuseStep 398647 = 597971) B597971
theorem B398667 : Blo 397767 398667 := bstep (se 1 (by rfl) ⟨299000, by rfl⟩ : syracuseStep 398667 = 598001) B598001
theorem B398679 : Blo 397767 398679 := bstep (se 1 (by rfl) ⟨299009, by rfl⟩ : syracuseStep 398679 = 598019) B598019
theorem B4330853 : Blo 397767 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B398699 : Blo 397767 398699 := bstep (se 1 (by rfl) ⟨299024, by rfl⟩ : syracuseStep 398699 = 598049) B598049
theorem B11736433 : Blo 397767 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B857459 : Blo 397767 857459 := bstep (se 1 (by rfl) ⟨643094, by rfl⟩ : syracuseStep 857459 = 1286189) B1286189
theorem B398711 : Blo 397767 398711 := bstep (se 1 (by rfl) ⟨299033, by rfl⟩ : syracuseStep 398711 = 598067) B598067
theorem B398731 : Blo 397767 398731 := bstep (se 1 (by rfl) ⟨299048, by rfl⟩ : syracuseStep 398731 = 598097) B598097
theorem B398743 : Blo 397767 398743 := bstep (se 1 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 398743 = 598115) B598115
theorem B431531 : Blo 397767 431531 := bstep (se 1 (by rfl) ⟨323648, by rfl⟩ : syracuseStep 431531 = 647297) B647297
theorem B398763 : Blo 397767 398763 := bstep (se 1 (by rfl) ⟨299072, by rfl⟩ : syracuseStep 398763 = 598145) B598145
theorem B398775 : Blo 397767 398775 := bstep (se 1 (by rfl) ⟨299081, by rfl⟩ : syracuseStep 398775 = 598163) B598163
theorem B398795 : Blo 397767 398795 := bstep (se 1 (by rfl) ⟨299096, by rfl⟩ : syracuseStep 398795 = 598193) B598193
theorem B398807 : Blo 397767 398807 := bstep (se 1 (by rfl) ⟨299105, by rfl⟩ : syracuseStep 398807 = 598211) B598211
theorem B1349081 : Blo 397767 1349081 := bstep (se 2 (by rfl) ⟨505905, by rfl⟩ : syracuseStep 1349081 = 1011811) B1011811
theorem B398827 : Blo 397767 398827 := bstep (se 1 (by rfl) ⟨299120, by rfl⟩ : syracuseStep 398827 = 598241) B598241
theorem B398839 : Blo 397767 398839 := bstep (se 1 (by rfl) ⟨299129, by rfl⟩ : syracuseStep 398839 = 598259) B598259
theorem B398859 : Blo 397767 398859 := bstep (se 1 (by rfl) ⟨299144, by rfl⟩ : syracuseStep 398859 = 598289) B598289
theorem B759307 : Blo 397767 759307 := bstep (se 1 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 759307 = 1138961) B1138961
theorem B1021463 : Blo 397767 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B398871 : Blo 397767 398871 := bstep (se 1 (by rfl) ⟨299153, by rfl⟩ : syracuseStep 398871 = 598307) B598307
theorem B398891 : Blo 397767 398891 := bstep (se 1 (by rfl) ⟨299168, by rfl⟩ : syracuseStep 398891 = 598337) B598337
theorem B398903 : Blo 397767 398903 := bstep (se 1 (by rfl) ⟨299177, by rfl⟩ : syracuseStep 398903 = 598355) B598355
theorem B1513025 : Blo 397767 1513025 := bstep (se 2 (by rfl) ⟨567384, by rfl⟩ : syracuseStep 1513025 = 1134769) B1134769
theorem B398923 : Blo 397767 398923 := bstep (se 1 (by rfl) ⟨299192, by rfl⟩ : syracuseStep 398923 = 598385) B598385
theorem B398935 : Blo 397767 398935 := bstep (se 1 (by rfl) ⟨299201, by rfl⟩ : syracuseStep 398935 = 598403) B598403
theorem B398955 : Blo 397767 398955 := bstep (se 1 (by rfl) ⟨299216, by rfl⟩ : syracuseStep 398955 = 598433) B598433
theorem B398967 : Blo 397767 398967 := bstep (se 1 (by rfl) ⟨299225, by rfl⟩ : syracuseStep 398967 = 598451) B598451
theorem B398987 : Blo 397767 398987 := bstep (se 1 (by rfl) ⟨299240, by rfl⟩ : syracuseStep 398987 = 598481) B598481
theorem B398999 : Blo 397767 398999 := bstep (se 1 (by rfl) ⟨299249, by rfl⟩ : syracuseStep 398999 = 598499) B598499
theorem B399019 : Blo 397767 399019 := bstep (se 1 (by rfl) ⟨299264, by rfl⟩ : syracuseStep 399019 = 598529) B598529
theorem B399031 : Blo 397767 399031 := bstep (se 1 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 399031 = 598547) B598547
theorem B399051 : Blo 397767 399051 := bstep (se 1 (by rfl) ⟨299288, by rfl⟩ : syracuseStep 399051 = 598577) B598577
theorem B399063 : Blo 397767 399063 := bstep (se 1 (by rfl) ⟨299297, by rfl⟩ : syracuseStep 399063 = 598595) B598595
theorem B399083 : Blo 397767 399083 := bstep (se 1 (by rfl) ⟨299312, by rfl⟩ : syracuseStep 399083 = 598625) B598625
theorem B399095 : Blo 397767 399095 := bstep (se 1 (by rfl) ⟨299321, by rfl⟩ : syracuseStep 399095 = 598643) B598643
theorem B399115 : Blo 397767 399115 := bstep (se 1 (by rfl) ⟨299336, by rfl⟩ : syracuseStep 399115 = 598673) B598673
theorem B399127 : Blo 397767 399127 := bstep (se 1 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 399127 = 598691) B598691
theorem B399147 : Blo 397767 399147 := bstep (se 1 (by rfl) ⟨299360, by rfl⟩ : syracuseStep 399147 = 598721) B598721
theorem B399159 : Blo 397767 399159 := bstep (se 1 (by rfl) ⟨299369, by rfl⟩ : syracuseStep 399159 = 598739) B598739
theorem B399179 : Blo 397767 399179 := bstep (se 1 (by rfl) ⟨299384, by rfl⟩ : syracuseStep 399179 = 598769) B598769
theorem B2561867 : Blo 397767 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B399191 : Blo 397767 399191 := bstep (se 1 (by rfl) ⟨299393, by rfl⟩ : syracuseStep 399191 = 598787) B598787
theorem B399211 : Blo 397767 399211 := bstep (se 1 (by rfl) ⟨299408, by rfl⟩ : syracuseStep 399211 = 598817) B598817
theorem B399223 : Blo 397767 399223 := bstep (se 1 (by rfl) ⟨299417, by rfl⟩ : syracuseStep 399223 = 598835) B598835
theorem B399243 : Blo 397767 399243 := bstep (se 1 (by rfl) ⟨299432, by rfl⟩ : syracuseStep 399243 = 598865) B598865
theorem B399255 : Blo 397767 399255 := bstep (se 1 (by rfl) ⟨299441, by rfl⟩ : syracuseStep 399255 = 598883) B598883
theorem B399275 : Blo 397767 399275 := bstep (se 1 (by rfl) ⟨299456, by rfl⟩ : syracuseStep 399275 = 598913) B598913
theorem B399287 : Blo 397767 399287 := bstep (se 1 (by rfl) ⟨299465, by rfl⟩ : syracuseStep 399287 = 598931) B598931
theorem B399307 : Blo 397767 399307 := bstep (se 1 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 399307 = 598961) B598961
theorem B759755 : Blo 397767 759755 := bstep (se 1 (by rfl) ⟨569816, by rfl⟩ : syracuseStep 759755 = 1139633) B1139633
theorem B3282893 : Blo 397767 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B399319 : Blo 397767 399319 := bstep (se 1 (by rfl) ⟨299489, by rfl⟩ : syracuseStep 399319 = 598979) B598979
theorem B399339 : Blo 397767 399339 := bstep (se 1 (by rfl) ⟨299504, by rfl⟩ : syracuseStep 399339 = 599009) B599009
theorem B399351 : Blo 397767 399351 := bstep (se 1 (by rfl) ⟨299513, by rfl⟩ : syracuseStep 399351 = 599027) B599027
theorem B399371 : Blo 397767 399371 := bstep (se 1 (by rfl) ⟨299528, by rfl⟩ : syracuseStep 399371 = 599057) B599057
theorem B399383 : Blo 397767 399383 := bstep (se 1 (by rfl) ⟨299537, by rfl⟩ : syracuseStep 399383 = 599075) B599075
theorem B399403 : Blo 397767 399403 := bstep (se 1 (by rfl) ⟨299552, by rfl⟩ : syracuseStep 399403 = 599105) B599105
theorem B399415 : Blo 397767 399415 := bstep (se 1 (by rfl) ⟨299561, by rfl⟩ : syracuseStep 399415 = 599123) B599123
theorem B399435 : Blo 397767 399435 := bstep (se 1 (by rfl) ⟨299576, by rfl⟩ : syracuseStep 399435 = 599153) B599153
theorem B399447 : Blo 397767 399447 := bstep (se 1 (by rfl) ⟨299585, by rfl⟩ : syracuseStep 399447 = 599171) B599171
theorem B399467 : Blo 397767 399467 := bstep (se 1 (by rfl) ⟨299600, by rfl⟩ : syracuseStep 399467 = 599201) B599201
theorem B399479 : Blo 397767 399479 := bstep (se 1 (by rfl) ⟨299609, by rfl⟩ : syracuseStep 399479 = 599219) B599219
theorem B759937 : Blo 397767 759937 := bstep (se 2 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 759937 = 569953) B569953
theorem B399499 : Blo 397767 399499 := bstep (se 1 (by rfl) ⟨299624, by rfl⟩ : syracuseStep 399499 = 599249) B599249
theorem B399511 : Blo 397767 399511 := bstep (se 1 (by rfl) ⟨299633, by rfl⟩ : syracuseStep 399511 = 599267) B599267
theorem B1349783 : Blo 397767 1349783 := bstep (se 1 (by rfl) ⟨1012337, by rfl⟩ : syracuseStep 1349783 = 2024675) B2024675
theorem B399531 : Blo 397767 399531 := bstep (se 1 (by rfl) ⟨299648, by rfl⟩ : syracuseStep 399531 = 599297) B599297
theorem B399543 : Blo 397767 399543 := bstep (se 1 (by rfl) ⟨299657, by rfl⟩ : syracuseStep 399543 = 599315) B599315
theorem B399563 : Blo 397767 399563 := bstep (se 1 (by rfl) ⟨299672, by rfl⟩ : syracuseStep 399563 = 599345) B599345
theorem B399575 : Blo 397767 399575 := bstep (se 1 (by rfl) ⟨299681, by rfl⟩ : syracuseStep 399575 = 599363) B599363
theorem B399595 : Blo 397767 399595 := bstep (se 1 (by rfl) ⟨299696, by rfl⟩ : syracuseStep 399595 = 599393) B599393
theorem B399607 : Blo 397767 399607 := bstep (se 1 (by rfl) ⟨299705, by rfl⟩ : syracuseStep 399607 = 599411) B599411
theorem B399627 : Blo 397767 399627 := bstep (se 1 (by rfl) ⟨299720, by rfl⟩ : syracuseStep 399627 = 599441) B599441
theorem B399639 : Blo 397767 399639 := bstep (se 1 (by rfl) ⟨299729, by rfl⟩ : syracuseStep 399639 = 599459) B599459
theorem B399659 : Blo 397767 399659 := bstep (se 1 (by rfl) ⟨299744, by rfl⟩ : syracuseStep 399659 = 599489) B599489
theorem B399671 : Blo 397767 399671 := bstep (se 1 (by rfl) ⟨299753, by rfl⟩ : syracuseStep 399671 = 599507) B599507
theorem B399691 : Blo 397767 399691 := bstep (se 1 (by rfl) ⟨299768, by rfl⟩ : syracuseStep 399691 = 599537) B599537
theorem B399703 : Blo 397767 399703 := bstep (se 1 (by rfl) ⟨299777, by rfl⟩ : syracuseStep 399703 = 599555) B599555
theorem B399723 : Blo 397767 399723 := bstep (se 1 (by rfl) ⟨299792, by rfl⟩ : syracuseStep 399723 = 599585) B599585
theorem B399735 : Blo 397767 399735 := bstep (se 1 (by rfl) ⟨299801, by rfl⟩ : syracuseStep 399735 = 599603) B599603
theorem B399755 : Blo 397767 399755 := bstep (se 1 (by rfl) ⟨299816, by rfl⟩ : syracuseStep 399755 = 599633) B599633
theorem B14522773 : Blo 397767 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B399767 : Blo 397767 399767 := bstep (se 1 (by rfl) ⟨299825, by rfl⟩ : syracuseStep 399767 = 599651) B599651
theorem B399787 : Blo 397767 399787 := bstep (se 1 (by rfl) ⟨299840, by rfl⟩ : syracuseStep 399787 = 599681) B599681
theorem B399799 : Blo 397767 399799 := bstep (se 1 (by rfl) ⟨299849, by rfl⟩ : syracuseStep 399799 = 599699) B599699
theorem B399819 : Blo 397767 399819 := bstep (se 1 (by rfl) ⟨299864, by rfl⟩ : syracuseStep 399819 = 599729) B599729
theorem B399831 : Blo 397767 399831 := bstep (se 1 (by rfl) ⟨299873, by rfl⟩ : syracuseStep 399831 = 599747) B599747
theorem B760279 : Blo 397767 760279 := bstep (se 1 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 760279 = 1140419) B1140419
theorem B399851 : Blo 397767 399851 := bstep (se 1 (by rfl) ⟨299888, by rfl⟩ : syracuseStep 399851 = 599777) B599777
theorem B399863 : Blo 397767 399863 := bstep (se 1 (by rfl) ⟨299897, by rfl⟩ : syracuseStep 399863 = 599795) B599795
theorem B399883 : Blo 397767 399883 := bstep (se 1 (by rfl) ⟨299912, by rfl⟩ : syracuseStep 399883 = 599825) B599825
theorem B5478929 : Blo 397767 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B399895 : Blo 397767 399895 := bstep (se 1 (by rfl) ⟨299921, by rfl⟩ : syracuseStep 399895 = 599843) B599843
theorem B399915 : Blo 397767 399915 := bstep (se 1 (by rfl) ⟨299936, by rfl⟩ : syracuseStep 399915 = 599873) B599873
theorem B399927 : Blo 397767 399927 := bstep (se 1 (by rfl) ⟨299945, by rfl⟩ : syracuseStep 399927 = 599891) B599891
theorem B399947 : Blo 397767 399947 := bstep (se 1 (by rfl) ⟨299960, by rfl⟩ : syracuseStep 399947 = 599921) B599921
theorem B399959 : Blo 397767 399959 := bstep (se 1 (by rfl) ⟨299969, by rfl⟩ : syracuseStep 399959 = 599939) B599939
theorem B399979 : Blo 397767 399979 := bstep (se 1 (by rfl) ⟨299984, by rfl⟩ : syracuseStep 399979 = 599969) B599969
theorem B399991 : Blo 397767 399991 := bstep (se 1 (by rfl) ⟨299993, by rfl⟩ : syracuseStep 399991 = 599987) B599987
theorem B400011 : Blo 397767 400011 := bstep (se 1 (by rfl) ⟨300008, by rfl⟩ : syracuseStep 400011 = 600017) B600017
theorem B400023 : Blo 397767 400023 := bstep (se 1 (by rfl) ⟨300017, by rfl⟩ : syracuseStep 400023 = 600035) B600035
theorem B400043 : Blo 397767 400043 := bstep (se 1 (by rfl) ⟨300032, by rfl⟩ : syracuseStep 400043 = 600065) B600065
theorem B1350323 : Blo 397767 1350323 := bstep (se 1 (by rfl) ⟨1012742, by rfl⟩ : syracuseStep 1350323 = 2025485) B2025485
theorem B760499 : Blo 397767 760499 := bstep (se 1 (by rfl) ⟨570374, by rfl⟩ : syracuseStep 760499 = 1140749) B1140749
theorem B400055 : Blo 397767 400055 := bstep (se 1 (by rfl) ⟨300041, by rfl⟩ : syracuseStep 400055 = 600083) B600083
theorem B400075 : Blo 397767 400075 := bstep (se 1 (by rfl) ⟨300056, by rfl⟩ : syracuseStep 400075 = 600113) B600113
theorem B400087 : Blo 397767 400087 := bstep (se 1 (by rfl) ⟨300065, by rfl⟩ : syracuseStep 400087 = 600131) B600131
theorem B400107 : Blo 397767 400107 := bstep (se 1 (by rfl) ⟨300080, by rfl⟩ : syracuseStep 400107 = 600161) B600161
theorem B400119 : Blo 397767 400119 := bstep (se 1 (by rfl) ⟨300089, by rfl⟩ : syracuseStep 400119 = 600179) B600179
theorem B4922117 : Blo 397767 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B596747 : Blo 397767 596747 := bstep (se 1 (by rfl) ⟨447560, by rfl⟩ : syracuseStep 596747 = 895121) B895121
theorem B400139 : Blo 397767 400139 := bstep (se 1 (by rfl) ⟨300104, by rfl⟩ : syracuseStep 400139 = 600209) B600209
theorem B596759 : Blo 397767 596759 := bstep (se 1 (by rfl) ⟨447569, by rfl⟩ : syracuseStep 596759 = 895139) B895139
theorem B400151 : Blo 397767 400151 := bstep (se 1 (by rfl) ⟨300113, by rfl⟩ : syracuseStep 400151 = 600227) B600227
theorem B400171 : Blo 397767 400171 := bstep (se 1 (by rfl) ⟨300128, by rfl⟩ : syracuseStep 400171 = 600257) B600257
theorem B1514285 : Blo 397767 1514285 := bstep (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) B567857
theorem B400183 : Blo 397767 400183 := bstep (se 1 (by rfl) ⟨300137, by rfl⟩ : syracuseStep 400183 = 600275) B600275
theorem B1514315 : Blo 397767 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B400203 : Blo 397767 400203 := bstep (se 1 (by rfl) ⟨300152, by rfl⟩ : syracuseStep 400203 = 600305) B600305
theorem B400215 : Blo 397767 400215 := bstep (se 1 (by rfl) ⟨300161, by rfl⟩ : syracuseStep 400215 = 600323) B600323
theorem B596825 : Blo 397767 596825 := bstep (se 2 (by rfl) ⟨223809, by rfl⟩ : syracuseStep 596825 = 447619) B447619
theorem B400235 : Blo 397767 400235 := bstep (se 1 (by rfl) ⟨300176, by rfl⟩ : syracuseStep 400235 = 600353) B600353
theorem B400247 : Blo 397767 400247 := bstep (se 1 (by rfl) ⟨300185, by rfl⟩ : syracuseStep 400247 = 600371) B600371
theorem B400267 : Blo 397767 400267 := bstep (se 1 (by rfl) ⟨300200, by rfl⟩ : syracuseStep 400267 = 600401) B600401
theorem B400279 : Blo 397767 400279 := bstep (se 1 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 400279 = 600419) B600419
theorem B760727 : Blo 397767 760727 := bstep (se 1 (by rfl) ⟨570545, by rfl⟩ : syracuseStep 760727 = 1141091) B1141091
theorem B400299 : Blo 397767 400299 := bstep (se 1 (by rfl) ⟨300224, by rfl⟩ : syracuseStep 400299 = 600449) B600449
theorem B400311 : Blo 397767 400311 := bstep (se 1 (by rfl) ⟨300233, by rfl⟩ : syracuseStep 400311 = 600467) B600467
theorem B1350593 : Blo 397767 1350593 := bstep (se 2 (by rfl) ⟨506472, by rfl⟩ : syracuseStep 1350593 = 1012945) B1012945
theorem B596939 : Blo 397767 596939 := bstep (se 1 (by rfl) ⟨447704, by rfl⟩ : syracuseStep 596939 = 895409) B895409
theorem B400331 : Blo 397767 400331 := bstep (se 1 (by rfl) ⟨300248, by rfl⟩ : syracuseStep 400331 = 600497) B600497
theorem B596951 : Blo 397767 596951 := bstep (se 1 (by rfl) ⟨447713, by rfl⟩ : syracuseStep 596951 = 895427) B895427
theorem B400343 : Blo 397767 400343 := bstep (se 1 (by rfl) ⟨300257, by rfl⟩ : syracuseStep 400343 = 600515) B600515
theorem B1285085 : Blo 397767 1285085 := bstep (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) B481907
theorem B400363 : Blo 397767 400363 := bstep (se 1 (by rfl) ⟨300272, by rfl⟩ : syracuseStep 400363 = 600545) B600545
theorem B400375 : Blo 397767 400375 := bstep (se 1 (by rfl) ⟨300281, by rfl⟩ : syracuseStep 400375 = 600563) B600563
theorem B400395 : Blo 397767 400395 := bstep (se 1 (by rfl) ⟨300296, by rfl⟩ : syracuseStep 400395 = 600593) B600593
theorem B400407 : Blo 397767 400407 := bstep (se 1 (by rfl) ⟨300305, by rfl⟩ : syracuseStep 400407 = 600611) B600611
theorem B597017 : Blo 397767 597017 := bstep (se 2 (by rfl) ⟨223881, by rfl⟩ : syracuseStep 597017 = 447763) B447763
theorem B695321 : Blo 397767 695321 := bstep (se 2 (by rfl) ⟨260745, by rfl⟩ : syracuseStep 695321 = 521491) B521491
theorem B400427 : Blo 397767 400427 := bstep (se 1 (by rfl) ⟨300320, by rfl⟩ : syracuseStep 400427 = 600641) B600641
theorem B957491 : Blo 397767 957491 := bstep (se 1 (by rfl) ⟨718118, by rfl⟩ : syracuseStep 957491 = 1436237) B1436237
theorem B400439 : Blo 397767 400439 := bstep (se 1 (by rfl) ⟨300329, by rfl⟩ : syracuseStep 400439 = 600659) B600659
theorem B400459 : Blo 397767 400459 := bstep (se 1 (by rfl) ⟨300344, by rfl⟩ : syracuseStep 400459 = 600689) B600689
theorem B400471 : Blo 397767 400471 := bstep (se 1 (by rfl) ⟨300353, by rfl⟩ : syracuseStep 400471 = 600707) B600707
theorem B400491 : Blo 397767 400491 := bstep (se 1 (by rfl) ⟨300368, by rfl⟩ : syracuseStep 400491 = 600737) B600737
theorem B400503 : Blo 397767 400503 := bstep (se 1 (by rfl) ⟨300377, by rfl⟩ : syracuseStep 400503 = 600755) B600755
theorem B597131 : Blo 397767 597131 := bstep (se 1 (by rfl) ⟨447848, by rfl⟩ : syracuseStep 597131 = 895697) B895697
theorem B400523 : Blo 397767 400523 := bstep (se 1 (by rfl) ⟨300392, by rfl⟩ : syracuseStep 400523 = 600785) B600785
theorem B597143 : Blo 397767 597143 := bstep (se 1 (by rfl) ⟨447857, by rfl⟩ : syracuseStep 597143 = 895715) B895715
theorem B400535 : Blo 397767 400535 := bstep (se 1 (by rfl) ⟨300401, by rfl⟩ : syracuseStep 400535 = 600803) B600803
theorem B760985 : Blo 397767 760985 := bstep (se 2 (by rfl) ⟨285369, by rfl⟩ : syracuseStep 760985 = 570739) B570739
theorem B400555 : Blo 397767 400555 := bstep (se 1 (by rfl) ⟨300416, by rfl⟩ : syracuseStep 400555 = 600833) B600833
theorem B400567 : Blo 397767 400567 := bstep (se 1 (by rfl) ⟨300425, by rfl⟩ : syracuseStep 400567 = 600851) B600851
theorem B400587 : Blo 397767 400587 := bstep (se 1 (by rfl) ⟨300440, by rfl⟩ : syracuseStep 400587 = 600881) B600881
theorem B400599 : Blo 397767 400599 := bstep (se 1 (by rfl) ⟨300449, by rfl⟩ : syracuseStep 400599 = 600899) B600899
theorem B597209 : Blo 397767 597209 := bstep (se 2 (by rfl) ⟨223953, by rfl⟩ : syracuseStep 597209 = 447907) B447907
theorem B400619 : Blo 397767 400619 := bstep (se 1 (by rfl) ⟨300464, by rfl⟩ : syracuseStep 400619 = 600929) B600929
theorem B400631 : Blo 397767 400631 := bstep (se 1 (by rfl) ⟨300473, by rfl⟩ : syracuseStep 400631 = 600947) B600947
theorem B400651 : Blo 397767 400651 := bstep (se 1 (by rfl) ⟨300488, by rfl⟩ : syracuseStep 400651 = 600977) B600977
theorem B400663 : Blo 397767 400663 := bstep (se 1 (by rfl) ⟨300497, by rfl⟩ : syracuseStep 400663 = 600995) B600995
theorem B400683 : Blo 397767 400683 := bstep (se 1 (by rfl) ⟨300512, by rfl⟩ : syracuseStep 400683 = 601025) B601025
theorem B400695 : Blo 397767 400695 := bstep (se 1 (by rfl) ⟨300521, by rfl⟩ : syracuseStep 400695 = 601043) B601043
theorem B597323 : Blo 397767 597323 := bstep (se 1 (by rfl) ⟨447992, by rfl⟩ : syracuseStep 597323 = 895985) B895985
theorem B400715 : Blo 397767 400715 := bstep (se 1 (by rfl) ⟨300536, by rfl⟩ : syracuseStep 400715 = 601073) B601073
theorem B597335 : Blo 397767 597335 := bstep (se 1 (by rfl) ⟨448001, by rfl⟩ : syracuseStep 597335 = 896003) B896003
theorem B400727 : Blo 397767 400727 := bstep (se 1 (by rfl) ⟨300545, by rfl⟩ : syracuseStep 400727 = 601091) B601091
theorem B400747 : Blo 397767 400747 := bstep (se 1 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 400747 = 601121) B601121
theorem B400759 : Blo 397767 400759 := bstep (se 1 (by rfl) ⟨300569, by rfl⟩ : syracuseStep 400759 = 601139) B601139
theorem B400779 : Blo 397767 400779 := bstep (se 1 (by rfl) ⟨300584, by rfl⟩ : syracuseStep 400779 = 601169) B601169
theorem B400791 : Blo 397767 400791 := bstep (se 1 (by rfl) ⟨300593, by rfl⟩ : syracuseStep 400791 = 601187) B601187
theorem B597401 : Blo 397767 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B400811 : Blo 397767 400811 := bstep (se 1 (by rfl) ⟨300608, by rfl⟩ : syracuseStep 400811 = 601217) B601217
theorem B400823 : Blo 397767 400823 := bstep (se 1 (by rfl) ⟨300617, by rfl⟩ : syracuseStep 400823 = 601235) B601235
theorem B400843 : Blo 397767 400843 := bstep (se 1 (by rfl) ⟨300632, by rfl⟩ : syracuseStep 400843 = 601265) B601265
theorem B400855 : Blo 397767 400855 := bstep (se 1 (by rfl) ⟨300641, by rfl⟩ : syracuseStep 400855 = 601283) B601283
theorem B1514969 : Blo 397767 1514969 := bstep (se 2 (by rfl) ⟨568113, by rfl⟩ : syracuseStep 1514969 = 1136227) B1136227
theorem B1351133 : Blo 397767 1351133 := bstep (se 3 (by rfl) ⟨253337, by rfl⟩ : syracuseStep 1351133 = 506675) B506675
theorem B400875 : Blo 397767 400875 := bstep (se 1 (by rfl) ⟨300656, by rfl⟩ : syracuseStep 400875 = 601313) B601313
theorem B400887 : Blo 397767 400887 := bstep (se 1 (by rfl) ⟨300665, by rfl⟩ : syracuseStep 400887 = 601331) B601331
theorem B597515 : Blo 397767 597515 := bstep (se 1 (by rfl) ⟨448136, by rfl⟩ : syracuseStep 597515 = 896273) B896273
theorem B400907 : Blo 397767 400907 := bstep (se 1 (by rfl) ⟨300680, by rfl⟩ : syracuseStep 400907 = 601361) B601361
theorem B597527 : Blo 397767 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B400919 : Blo 397767 400919 := bstep (se 1 (by rfl) ⟨300689, by rfl⟩ : syracuseStep 400919 = 601379) B601379
theorem B400939 : Blo 397767 400939 := bstep (se 1 (by rfl) ⟨300704, by rfl⟩ : syracuseStep 400939 = 601409) B601409
theorem B761395 : Blo 397767 761395 := bstep (se 1 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 761395 = 1142093) B1142093
theorem B400951 : Blo 397767 400951 := bstep (se 1 (by rfl) ⟨300713, by rfl⟩ : syracuseStep 400951 = 601427) B601427
theorem B400971 : Blo 397767 400971 := bstep (se 1 (by rfl) ⟨300728, by rfl⟩ : syracuseStep 400971 = 601457) B601457
theorem B400983 : Blo 397767 400983 := bstep (se 1 (by rfl) ⟨300737, by rfl⟩ : syracuseStep 400983 = 601475) B601475
theorem B597593 : Blo 397767 597593 := bstep (se 2 (by rfl) ⟨224097, by rfl⟩ : syracuseStep 597593 = 448195) B448195
theorem B401003 : Blo 397767 401003 := bstep (se 1 (by rfl) ⟨300752, by rfl⟩ : syracuseStep 401003 = 601505) B601505
theorem B401015 : Blo 397767 401015 := bstep (se 1 (by rfl) ⟨300761, by rfl⟩ : syracuseStep 401015 = 601523) B601523
theorem B401035 : Blo 397767 401035 := bstep (se 1 (by rfl) ⟨300776, by rfl⟩ : syracuseStep 401035 = 601553) B601553
theorem B401047 : Blo 397767 401047 := bstep (se 1 (by rfl) ⟨300785, by rfl⟩ : syracuseStep 401047 = 601571) B601571
theorem B401067 : Blo 397767 401067 := bstep (se 1 (by rfl) ⟨300800, by rfl⟩ : syracuseStep 401067 = 601601) B601601
theorem B401079 : Blo 397767 401079 := bstep (se 1 (by rfl) ⟨300809, by rfl⟩ : syracuseStep 401079 = 601619) B601619
theorem B597707 : Blo 397767 597707 := bstep (se 1 (by rfl) ⟨448280, by rfl⟩ : syracuseStep 597707 = 896561) B896561
theorem B401099 : Blo 397767 401099 := bstep (se 1 (by rfl) ⟨300824, by rfl⟩ : syracuseStep 401099 = 601649) B601649
theorem B597719 : Blo 397767 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B401111 : Blo 397767 401111 := bstep (se 1 (by rfl) ⟨300833, by rfl⟩ : syracuseStep 401111 = 601667) B601667
theorem B401131 : Blo 397767 401131 := bstep (se 1 (by rfl) ⟨300848, by rfl⟩ : syracuseStep 401131 = 601697) B601697
theorem B401143 : Blo 397767 401143 := bstep (se 1 (by rfl) ⟨300857, by rfl⟩ : syracuseStep 401143 = 601715) B601715
theorem B401163 : Blo 397767 401163 := bstep (se 1 (by rfl) ⟨300872, by rfl⟩ : syracuseStep 401163 = 601745) B601745
theorem B1515287 : Blo 397767 1515287 := bstep (se 1 (by rfl) ⟨1136465, by rfl⟩ : syracuseStep 1515287 = 2272931) B2272931
theorem B401175 : Blo 397767 401175 := bstep (se 1 (by rfl) ⟨300881, by rfl⟩ : syracuseStep 401175 = 601763) B601763
theorem B597785 : Blo 397767 597785 := bstep (se 2 (by rfl) ⟨224169, by rfl⟩ : syracuseStep 597785 = 448339) B448339
theorem B401195 : Blo 397767 401195 := bstep (se 1 (by rfl) ⟨300896, by rfl⟩ : syracuseStep 401195 = 601793) B601793
theorem B401207 : Blo 397767 401207 := bstep (se 1 (by rfl) ⟨300905, by rfl⟩ : syracuseStep 401207 = 601811) B601811
theorem B401227 : Blo 397767 401227 := bstep (se 1 (by rfl) ⟨300920, by rfl⟩ : syracuseStep 401227 = 601841) B601841
theorem B401239 : Blo 397767 401239 := bstep (se 1 (by rfl) ⟨300929, by rfl⟩ : syracuseStep 401239 = 601859) B601859
theorem B1613657 : Blo 397767 1613657 := bstep (se 2 (by rfl) ⟨605121, by rfl⟩ : syracuseStep 1613657 = 1210243) B1210243
theorem B401259 : Blo 397767 401259 := bstep (se 1 (by rfl) ⟨300944, by rfl⟩ : syracuseStep 401259 = 601889) B601889
theorem B401271 : Blo 397767 401271 := bstep (se 1 (by rfl) ⟨300953, by rfl⟩ : syracuseStep 401271 = 601907) B601907
theorem B597899 : Blo 397767 597899 := bstep (se 1 (by rfl) ⟨448424, by rfl⟩ : syracuseStep 597899 = 896849) B896849
theorem B401291 : Blo 397767 401291 := bstep (se 1 (by rfl) ⟨300968, by rfl⟩ : syracuseStep 401291 = 601937) B601937
theorem B597911 : Blo 397767 597911 := bstep (se 1 (by rfl) ⟨448433, by rfl⟩ : syracuseStep 597911 = 896867) B896867
theorem B401303 : Blo 397767 401303 := bstep (se 1 (by rfl) ⟨300977, by rfl⟩ : syracuseStep 401303 = 601955) B601955
theorem B401323 : Blo 397767 401323 := bstep (se 1 (by rfl) ⟨300992, by rfl⟩ : syracuseStep 401323 = 601985) B601985
theorem B5742515 : Blo 397767 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B401335 : Blo 397767 401335 := bstep (se 1 (by rfl) ⟨301001, by rfl⟩ : syracuseStep 401335 = 602003) B602003
theorem B401355 : Blo 397767 401355 := bstep (se 1 (by rfl) ⟨301016, by rfl⟩ : syracuseStep 401355 = 602033) B602033
theorem B401367 : Blo 397767 401367 := bstep (se 1 (by rfl) ⟨301025, by rfl⟩ : syracuseStep 401367 = 602051) B602051
theorem B597977 : Blo 397767 597977 := bstep (se 2 (by rfl) ⟨224241, by rfl⟩ : syracuseStep 597977 = 448483) B448483
theorem B401387 : Blo 397767 401387 := bstep (se 1 (by rfl) ⟨301040, by rfl⟩ : syracuseStep 401387 = 602081) B602081
theorem B401399 : Blo 397767 401399 := bstep (se 1 (by rfl) ⟨301049, by rfl⟩ : syracuseStep 401399 = 602099) B602099
theorem B401419 : Blo 397767 401419 := bstep (se 1 (by rfl) ⟨301064, by rfl⟩ : syracuseStep 401419 = 602129) B602129
theorem B401431 : Blo 397767 401431 := bstep (se 1 (by rfl) ⟨301073, by rfl⟩ : syracuseStep 401431 = 602147) B602147
theorem B761881 : Blo 397767 761881 := bstep (se 2 (by rfl) ⟨285705, by rfl⟩ : syracuseStep 761881 = 571411) B571411
theorem B401451 : Blo 397767 401451 := bstep (se 1 (by rfl) ⟨301088, by rfl⟩ : syracuseStep 401451 = 602177) B602177
theorem B401463 : Blo 397767 401463 := bstep (se 1 (by rfl) ⟨301097, by rfl⟩ : syracuseStep 401463 = 602195) B602195
theorem B598091 : Blo 397767 598091 := bstep (se 1 (by rfl) ⟨448568, by rfl⟩ : syracuseStep 598091 = 897137) B897137
theorem B401483 : Blo 397767 401483 := bstep (se 1 (by rfl) ⟨301112, by rfl⟩ : syracuseStep 401483 = 602225) B602225
theorem B598103 : Blo 397767 598103 := bstep (se 1 (by rfl) ⟨448577, by rfl⟩ : syracuseStep 598103 = 897155) B897155
theorem B401495 : Blo 397767 401495 := bstep (se 1 (by rfl) ⟨301121, by rfl⟩ : syracuseStep 401495 = 602243) B602243
theorem B401515 : Blo 397767 401515 := bstep (se 1 (by rfl) ⟨301136, by rfl⟩ : syracuseStep 401515 = 602273) B602273
theorem B401527 : Blo 397767 401527 := bstep (se 1 (by rfl) ⟨301145, by rfl⟩ : syracuseStep 401527 = 602291) B602291
theorem B401547 : Blo 397767 401547 := bstep (se 1 (by rfl) ⟨301160, by rfl⟩ : syracuseStep 401547 = 602321) B602321
theorem B401559 : Blo 397767 401559 := bstep (se 1 (by rfl) ⟨301169, by rfl⟩ : syracuseStep 401559 = 602339) B602339
theorem B598169 : Blo 397767 598169 := bstep (se 2 (by rfl) ⟨224313, by rfl⟩ : syracuseStep 598169 = 448627) B448627
theorem B401579 : Blo 397767 401579 := bstep (se 1 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 401579 = 602369) B602369
theorem B401591 : Blo 397767 401591 := bstep (se 1 (by rfl) ⟨301193, by rfl⟩ : syracuseStep 401591 = 602387) B602387
theorem B401611 : Blo 397767 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B401623 : Blo 397767 401623 := bstep (se 1 (by rfl) ⟨301217, by rfl⟩ : syracuseStep 401623 = 602435) B602435
theorem B401643 : Blo 397767 401643 := bstep (se 1 (by rfl) ⟨301232, by rfl⟩ : syracuseStep 401643 = 602465) B602465
theorem B401655 : Blo 397767 401655 := bstep (se 1 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 401655 = 602483) B602483
theorem B598283 : Blo 397767 598283 := bstep (se 1 (by rfl) ⟨448712, by rfl⟩ : syracuseStep 598283 = 897425) B897425
theorem B401675 : Blo 397767 401675 := bstep (se 1 (by rfl) ⟨301256, by rfl⟩ : syracuseStep 401675 = 602513) B602513
theorem B598295 : Blo 397767 598295 := bstep (se 1 (by rfl) ⟨448721, by rfl⟩ : syracuseStep 598295 = 897443) B897443
theorem B401687 : Blo 397767 401687 := bstep (se 1 (by rfl) ⟨301265, by rfl⟩ : syracuseStep 401687 = 602531) B602531
theorem B401707 : Blo 397767 401707 := bstep (se 1 (by rfl) ⟨301280, by rfl⟩ : syracuseStep 401707 = 602561) B602561
theorem B401719 : Blo 397767 401719 := bstep (se 1 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 401719 = 602579) B602579
theorem B401739 : Blo 397767 401739 := bstep (se 1 (by rfl) ⟨301304, by rfl⟩ : syracuseStep 401739 = 602609) B602609
theorem B401751 : Blo 397767 401751 := bstep (se 1 (by rfl) ⟨301313, by rfl⟩ : syracuseStep 401751 = 602627) B602627
theorem B598361 : Blo 397767 598361 := bstep (se 2 (by rfl) ⟨224385, by rfl⟩ : syracuseStep 598361 = 448771) B448771
theorem B1515955 : Blo 397767 1515955 := bstep (se 1 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 1515955 = 2273933) B2273933
theorem B2564531 : Blo 397767 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B598475 : Blo 397767 598475 := bstep (se 1 (by rfl) ⟨448856, by rfl⟩ : syracuseStep 598475 = 897713) B897713
theorem B598487 : Blo 397767 598487 := bstep (se 1 (by rfl) ⟨448865, by rfl⟩ : syracuseStep 598487 = 897731) B897731
theorem B598553 : Blo 397767 598553 := bstep (se 2 (by rfl) ⟨224457, by rfl⟩ : syracuseStep 598553 = 448915) B448915
theorem B3023405 : Blo 397767 3023405 := bstep (se 3 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 3023405 = 1133777) B1133777
theorem B2269741 : Blo 397767 2269741 := bstep (se 3 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 2269741 = 851153) B851153
theorem B1352267 : Blo 397767 1352267 := bstep (se 1 (by rfl) ⟨1014200, by rfl⟩ : syracuseStep 1352267 = 2028401) B2028401
theorem B762443 : Blo 397767 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B598667 : Blo 397767 598667 := bstep (se 1 (by rfl) ⟨449000, by rfl⟩ : syracuseStep 598667 = 898001) B898001
theorem B598679 : Blo 397767 598679 := bstep (se 1 (by rfl) ⟨449009, by rfl⟩ : syracuseStep 598679 = 898019) B898019
theorem B598745 : Blo 397767 598745 := bstep (se 2 (by rfl) ⟨224529, by rfl⟩ : syracuseStep 598745 = 449059) B449059
theorem B762625 : Blo 397767 762625 := bstep (se 2 (by rfl) ⟨285984, by rfl⟩ : syracuseStep 762625 = 571969) B571969
theorem B598859 : Blo 397767 598859 := bstep (se 1 (by rfl) ⟨449144, by rfl⟩ : syracuseStep 598859 = 898289) B898289
theorem B598871 : Blo 397767 598871 := bstep (se 1 (by rfl) ⟨449153, by rfl⟩ : syracuseStep 598871 = 898307) B898307
theorem B1352537 : Blo 397767 1352537 := bstep (se 2 (by rfl) ⟨507201, by rfl⟩ : syracuseStep 1352537 = 1014403) B1014403
theorem B598937 : Blo 397767 598937 := bstep (se 2 (by rfl) ⟨224601, by rfl⟩ : syracuseStep 598937 = 449203) B449203
theorem B1713089 : Blo 397767 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B599051 : Blo 397767 599051 := bstep (se 1 (by rfl) ⟨449288, by rfl⟩ : syracuseStep 599051 = 898577) B898577
theorem B599063 : Blo 397767 599063 := bstep (se 1 (by rfl) ⟨449297, by rfl⟩ : syracuseStep 599063 = 898595) B898595
theorem B959539 : Blo 397767 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B599129 : Blo 397767 599129 := bstep (se 2 (by rfl) ⟨224673, by rfl⟩ : syracuseStep 599129 = 449347) B449347
theorem B1713241 : Blo 397767 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B599243 : Blo 397767 599243 := bstep (se 1 (by rfl) ⟨449432, by rfl⟩ : syracuseStep 599243 = 898865) B898865
theorem B599255 : Blo 397767 599255 := bstep (se 1 (by rfl) ⟨449441, by rfl⟩ : syracuseStep 599255 = 898883) B898883
theorem B599321 : Blo 397767 599321 := bstep (se 2 (by rfl) ⟨224745, by rfl⟩ : syracuseStep 599321 = 449491) B449491
theorem B1156445 : Blo 397767 1156445 := bstep (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) B433667
theorem B599435 : Blo 397767 599435 := bstep (se 1 (by rfl) ⟨449576, by rfl⟩ : syracuseStep 599435 = 899153) B899153
theorem B599447 : Blo 397767 599447 := bstep (se 1 (by rfl) ⟨449585, by rfl⟩ : syracuseStep 599447 = 899171) B899171
theorem B599513 : Blo 397767 599513 := bstep (se 2 (by rfl) ⟨224817, by rfl⟩ : syracuseStep 599513 = 449635) B449635
theorem B1353239 : Blo 397767 1353239 := bstep (se 1 (by rfl) ⟨1014929, by rfl⟩ : syracuseStep 1353239 = 2029859) B2029859
theorem B599627 : Blo 397767 599627 := bstep (se 1 (by rfl) ⟨449720, by rfl⟩ : syracuseStep 599627 = 899441) B899441
theorem B599639 : Blo 397767 599639 := bstep (se 1 (by rfl) ⟨449729, by rfl⟩ : syracuseStep 599639 = 899459) B899459
theorem B1517201 : Blo 397767 1517201 := bstep (se 2 (by rfl) ⟨568950, by rfl⟩ : syracuseStep 1517201 = 1137901) B1137901
theorem B599705 : Blo 397767 599705 := bstep (se 2 (by rfl) ⟨224889, by rfl⟩ : syracuseStep 599705 = 449779) B449779
theorem B599819 : Blo 397767 599819 := bstep (se 1 (by rfl) ⟨449864, by rfl⟩ : syracuseStep 599819 = 899729) B899729
theorem B599831 : Blo 397767 599831 := bstep (se 1 (by rfl) ⟨449873, by rfl⟩ : syracuseStep 599831 = 899747) B899747
theorem B599897 : Blo 397767 599897 := bstep (se 2 (by rfl) ⟨224961, by rfl⟩ : syracuseStep 599897 = 449923) B449923
theorem B2566019 : Blo 397767 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B600011 : Blo 397767 600011 := bstep (se 1 (by rfl) ⟨450008, by rfl⟩ : syracuseStep 600011 = 900017) B900017
theorem B600023 : Blo 397767 600023 := bstep (se 1 (by rfl) ⟨450017, by rfl⟩ : syracuseStep 600023 = 900035) B900035
theorem B894977 : Blo 397767 894977 := bstep (se 2 (by rfl) ⟨335616, by rfl⟩ : syracuseStep 894977 = 671233) B671233
theorem B600089 : Blo 397767 600089 := bstep (se 2 (by rfl) ⟨225033, by rfl⟩ : syracuseStep 600089 = 450067) B450067
theorem B1353779 : Blo 397767 1353779 := bstep (se 1 (by rfl) ⟨1015334, by rfl⟩ : syracuseStep 1353779 = 2030669) B2030669
theorem B600203 : Blo 397767 600203 := bstep (se 1 (by rfl) ⟨450152, by rfl⟩ : syracuseStep 600203 = 900305) B900305
theorem B1386647 : Blo 397767 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B600215 : Blo 397767 600215 := bstep (se 1 (by rfl) ⟨450161, by rfl⟩ : syracuseStep 600215 = 900323) B900323
theorem B665815 : Blo 397767 665815 := bstep (se 1 (by rfl) ⟨499361, by rfl⟩ : syracuseStep 665815 = 998723) B998723
theorem B895193 : Blo 397767 895193 := bstep (se 2 (by rfl) ⟨335697, by rfl⟩ : syracuseStep 895193 = 671395) B671395
theorem B600281 : Blo 397767 600281 := bstep (se 2 (by rfl) ⟨225105, by rfl⟩ : syracuseStep 600281 = 450211) B450211
theorem B895283 : Blo 397767 895283 := bstep (se 1 (by rfl) ⟨671462, by rfl⟩ : syracuseStep 895283 = 1342925) B1342925
theorem B1354049 : Blo 397767 1354049 := bstep (se 2 (by rfl) ⟨507768, by rfl⟩ : syracuseStep 1354049 = 1015537) B1015537
theorem B1517899 : Blo 397767 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B600395 : Blo 397767 600395 := bstep (se 1 (by rfl) ⟨450296, by rfl⟩ : syracuseStep 600395 = 900593) B900593
theorem B895319 : Blo 397767 895319 := bstep (se 1 (by rfl) ⟨671489, by rfl⟩ : syracuseStep 895319 = 1342979) B1342979
theorem B600407 : Blo 397767 600407 := bstep (se 1 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 600407 = 900611) B900611
theorem B600473 : Blo 397767 600473 := bstep (se 2 (by rfl) ⟨225177, by rfl⟩ : syracuseStep 600473 = 450355) B450355
theorem B895499 : Blo 397767 895499 := bstep (se 1 (by rfl) ⟨671624, by rfl⟩ : syracuseStep 895499 = 1343249) B1343249
theorem B600587 : Blo 397767 600587 := bstep (se 1 (by rfl) ⟨450440, by rfl⟩ : syracuseStep 600587 = 900881) B900881
theorem B600599 : Blo 397767 600599 := bstep (se 1 (by rfl) ⟨450449, by rfl⟩ : syracuseStep 600599 = 900899) B900899
theorem B928279 : Blo 397767 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B895553 : Blo 397767 895553 := bstep (se 2 (by rfl) ⟨335832, by rfl⟩ : syracuseStep 895553 = 671665) B671665
theorem B600665 : Blo 397767 600665 := bstep (se 2 (by rfl) ⟨225249, by rfl⟩ : syracuseStep 600665 = 450499) B450499
theorem B1518173 : Blo 397767 1518173 := bstep (se 3 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 1518173 = 569315) B569315
theorem B2468483 : Blo 397767 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B600779 : Blo 397767 600779 := bstep (se 1 (by rfl) ⟨450584, by rfl⟩ : syracuseStep 600779 = 901169) B901169
theorem B600791 : Blo 397767 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B895769 : Blo 397767 895769 := bstep (se 2 (by rfl) ⟨335913, by rfl⟩ : syracuseStep 895769 = 671827) B671827
theorem B600857 : Blo 397767 600857 := bstep (se 2 (by rfl) ⟨225321, by rfl⟩ : syracuseStep 600857 = 450643) B450643
theorem B1354589 : Blo 397767 1354589 := bstep (se 3 (by rfl) ⟨253985, by rfl⟩ : syracuseStep 1354589 = 507971) B507971
theorem B895859 : Blo 397767 895859 := bstep (se 1 (by rfl) ⟨671894, by rfl⟩ : syracuseStep 895859 = 1343789) B1343789
theorem B600971 : Blo 397767 600971 := bstep (se 1 (by rfl) ⟨450728, by rfl⟩ : syracuseStep 600971 = 901457) B901457
theorem B895895 : Blo 397767 895895 := bstep (se 1 (by rfl) ⟨671921, by rfl⟩ : syracuseStep 895895 = 1343843) B1343843
theorem B600983 : Blo 397767 600983 := bstep (se 1 (by rfl) ⟨450737, by rfl⟩ : syracuseStep 600983 = 901475) B901475
theorem B601049 : Blo 397767 601049 := bstep (se 2 (by rfl) ⟨225393, by rfl⟩ : syracuseStep 601049 = 450787) B450787
theorem B3419171 : Blo 397767 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B896075 : Blo 397767 896075 := bstep (se 1 (by rfl) ⟨672056, by rfl⟩ : syracuseStep 896075 = 1344113) B1344113
theorem B9743435 : Blo 397767 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B601163 : Blo 397767 601163 := bstep (se 1 (by rfl) ⟨450872, by rfl⟩ : syracuseStep 601163 = 901745) B901745
theorem B601175 : Blo 397767 601175 := bstep (se 1 (by rfl) ⟨450881, by rfl⟩ : syracuseStep 601175 = 901763) B901763
theorem B896129 : Blo 397767 896129 := bstep (se 2 (by rfl) ⟨336048, by rfl⟩ : syracuseStep 896129 = 672097) B672097
theorem B601241 : Blo 397767 601241 := bstep (se 2 (by rfl) ⟨225465, by rfl⟩ : syracuseStep 601241 = 450931) B450931
theorem B601355 : Blo 397767 601355 := bstep (se 1 (by rfl) ⟨451016, by rfl⟩ : syracuseStep 601355 = 902033) B902033
theorem B1518871 : Blo 397767 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B601367 : Blo 397767 601367 := bstep (se 1 (by rfl) ⟨451025, by rfl⟩ : syracuseStep 601367 = 902051) B902051
theorem B896345 : Blo 397767 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B601433 : Blo 397767 601433 := bstep (se 2 (by rfl) ⟨225537, by rfl⟩ : syracuseStep 601433 = 451075) B451075
theorem B1912157 : Blo 397767 1912157 := bstep (se 3 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 1912157 = 717059) B717059
theorem B896435 : Blo 397767 896435 := bstep (se 1 (by rfl) ⟨672326, by rfl⟩ : syracuseStep 896435 = 1344653) B1344653
theorem B1617355 : Blo 397767 1617355 := bstep (se 1 (by rfl) ⟨1213016, by rfl⟩ : syracuseStep 1617355 = 2426033) B2426033
theorem B404939 : Blo 397767 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B601547 : Blo 397767 601547 := bstep (se 1 (by rfl) ⟨451160, by rfl⟩ : syracuseStep 601547 = 902321) B902321
theorem B896471 : Blo 397767 896471 := bstep (se 1 (by rfl) ⟨672353, by rfl⟩ : syracuseStep 896471 = 1344707) B1344707
theorem B2731481 : Blo 397767 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B601559 : Blo 397767 601559 := bstep (se 1 (by rfl) ⟨451169, by rfl⟩ : syracuseStep 601559 = 902339) B902339
theorem B601625 : Blo 397767 601625 := bstep (se 2 (by rfl) ⟨225609, by rfl⟩ : syracuseStep 601625 = 451219) B451219
theorem B503435 : Blo 397767 503435 := bstep (se 1 (by rfl) ⟨377576, by rfl⟩ : syracuseStep 503435 = 755153) B755153
theorem B896651 : Blo 397767 896651 := bstep (se 1 (by rfl) ⟨672488, by rfl⟩ : syracuseStep 896651 = 1344977) B1344977
theorem B601739 : Blo 397767 601739 := bstep (se 1 (by rfl) ⟨451304, by rfl⟩ : syracuseStep 601739 = 902609) B902609
theorem B601751 : Blo 397767 601751 := bstep (se 1 (by rfl) ⟨451313, by rfl⟩ : syracuseStep 601751 = 902627) B902627
theorem B896705 : Blo 397767 896705 := bstep (se 2 (by rfl) ⟨336264, by rfl⟩ : syracuseStep 896705 = 672529) B672529
theorem B601817 : Blo 397767 601817 := bstep (se 2 (by rfl) ⟨225681, by rfl⟩ : syracuseStep 601817 = 451363) B451363
theorem B3419921 : Blo 397767 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B601931 : Blo 397767 601931 := bstep (se 1 (by rfl) ⟨451448, by rfl⟩ : syracuseStep 601931 = 902897) B902897
theorem B601943 : Blo 397767 601943 := bstep (se 1 (by rfl) ⟨451457, by rfl⟩ : syracuseStep 601943 = 902915) B902915
theorem B2895709 : Blo 397767 2895709 := bstep (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) B1085891
theorem B896921 : Blo 397767 896921 := bstep (se 2 (by rfl) ⟨336345, by rfl⟩ : syracuseStep 896921 = 672691) B672691
theorem B602009 : Blo 397767 602009 := bstep (se 2 (by rfl) ⟨225753, by rfl⟩ : syracuseStep 602009 = 451507) B451507
theorem B13840307 : Blo 397767 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B1355723 : Blo 397767 1355723 := bstep (se 1 (by rfl) ⟨1016792, by rfl⟩ : syracuseStep 1355723 = 2033585) B2033585
theorem B1814489 : Blo 397767 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B897011 : Blo 397767 897011 := bstep (se 1 (by rfl) ⟨672758, by rfl⟩ : syracuseStep 897011 = 1345517) B1345517
theorem B602123 : Blo 397767 602123 := bstep (se 1 (by rfl) ⟨451592, by rfl⟩ : syracuseStep 602123 = 903185) B903185
theorem B6467597 : Blo 397767 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B897047 : Blo 397767 897047 := bstep (se 1 (by rfl) ⟨672785, by rfl⟩ : syracuseStep 897047 = 1345571) B1345571
theorem B602135 : Blo 397767 602135 := bstep (se 1 (by rfl) ⟨451601, by rfl⟩ : syracuseStep 602135 = 903203) B903203
theorem B1519661 : Blo 397767 1519661 := bstep (se 3 (by rfl) ⟨284936, by rfl⟩ : syracuseStep 1519661 = 569873) B569873
theorem B602201 : Blo 397767 602201 := bstep (se 2 (by rfl) ⟨225825, by rfl⟩ : syracuseStep 602201 = 451651) B451651
theorem B897227 : Blo 397767 897227 := bstep (se 1 (by rfl) ⟨672920, by rfl⟩ : syracuseStep 897227 = 1345841) B1345841
theorem B602315 : Blo 397767 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B602327 : Blo 397767 602327 := bstep (se 1 (by rfl) ⟨451745, by rfl⟩ : syracuseStep 602327 = 903491) B903491
theorem B897281 : Blo 397767 897281 := bstep (se 2 (by rfl) ⟨336480, by rfl⟩ : syracuseStep 897281 = 672961) B672961
theorem B602393 : Blo 397767 602393 := bstep (se 2 (by rfl) ⟨225897, by rfl⟩ : syracuseStep 602393 = 451795) B451795
theorem B405815 : Blo 397767 405815 := bstep (se 1 (by rfl) ⟨304361, by rfl⟩ : syracuseStep 405815 = 608723) B608723
theorem B504139 : Blo 397767 504139 := bstep (se 1 (by rfl) ⟨378104, by rfl⟩ : syracuseStep 504139 = 756209) B756209
theorem B3027293 : Blo 397767 3027293 := bstep (se 3 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 3027293 = 1135235) B1135235
theorem B602507 : Blo 397767 602507 := bstep (se 1 (by rfl) ⟨451880, by rfl⟩ : syracuseStep 602507 = 903761) B903761
theorem B602519 : Blo 397767 602519 := bstep (se 1 (by rfl) ⟨451889, by rfl⟩ : syracuseStep 602519 = 903779) B903779
theorem B897497 : Blo 397767 897497 := bstep (se 2 (by rfl) ⟨336561, by rfl⟩ : syracuseStep 897497 = 673123) B673123
theorem B602585 : Blo 397767 602585 := bstep (se 2 (by rfl) ⟨225969, by rfl⟩ : syracuseStep 602585 = 451939) B451939
theorem B897587 : Blo 397767 897587 := bstep (se 1 (by rfl) ⟨673190, by rfl⟩ : syracuseStep 897587 = 1346381) B1346381
theorem B504407 : Blo 397767 504407 := bstep (se 1 (by rfl) ⟨378305, by rfl⟩ : syracuseStep 504407 = 756611) B756611
theorem B897623 : Blo 397767 897623 := bstep (se 1 (by rfl) ⟨673217, by rfl⟩ : syracuseStep 897623 = 1346435) B1346435
theorem B963161 : Blo 397767 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B570073 : Blo 397767 570073 := bstep (se 2 (by rfl) ⟨213777, by rfl⟩ : syracuseStep 570073 = 427555) B427555
theorem B897803 : Blo 397767 897803 := bstep (se 1 (by rfl) ⟨673352, by rfl⟩ : syracuseStep 897803 = 1346705) B1346705
theorem B897857 : Blo 397767 897857 := bstep (se 2 (by rfl) ⟨336696, by rfl⟩ : syracuseStep 897857 = 673393) B673393
theorem B898073 : Blo 397767 898073 := bstep (se 2 (by rfl) ⟨336777, by rfl⟩ : syracuseStep 898073 = 673555) B673555
theorem B898163 : Blo 397767 898163 := bstep (se 1 (by rfl) ⟨673622, by rfl⟩ : syracuseStep 898163 = 1347245) B1347245
theorem B898199 : Blo 397767 898199 := bstep (se 1 (by rfl) ⟨673649, by rfl⟩ : syracuseStep 898199 = 1347299) B1347299
theorem B505111 : Blo 397767 505111 := bstep (se 1 (by rfl) ⟨378833, by rfl⟩ : syracuseStep 505111 = 757667) B757667
theorem B898379 : Blo 397767 898379 := bstep (se 1 (by rfl) ⟨673784, by rfl⟩ : syracuseStep 898379 = 1347569) B1347569
theorem B898433 : Blo 397767 898433 := bstep (se 2 (by rfl) ⟨336912, by rfl⟩ : syracuseStep 898433 = 673825) B673825
theorem B1521089 : Blo 397767 1521089 := bstep (se 2 (by rfl) ⟨570408, by rfl⟩ : syracuseStep 1521089 = 1140817) B1140817
theorem B898649 : Blo 397767 898649 := bstep (se 2 (by rfl) ⟨336993, by rfl⟩ : syracuseStep 898649 = 673987) B673987
theorem B898739 : Blo 397767 898739 := bstep (se 1 (by rfl) ⟨674054, by rfl⟩ : syracuseStep 898739 = 1348109) B1348109
theorem B898775 : Blo 397767 898775 := bstep (se 1 (by rfl) ⟨674081, by rfl⟩ : syracuseStep 898775 = 1348163) B1348163
theorem B898955 : Blo 397767 898955 := bstep (se 1 (by rfl) ⟨674216, by rfl⟩ : syracuseStep 898955 = 1348433) B1348433
theorem B899009 : Blo 397767 899009 := bstep (se 2 (by rfl) ⟨337128, by rfl⟩ : syracuseStep 899009 = 674257) B674257
theorem B571531 : Blo 397767 571531 := bstep (se 1 (by rfl) ⟨428648, by rfl⟩ : syracuseStep 571531 = 857297) B857297
theorem B899225 : Blo 397767 899225 := bstep (se 2 (by rfl) ⟨337209, by rfl⟩ : syracuseStep 899225 = 674419) B674419
theorem B899315 : Blo 397767 899315 := bstep (se 1 (by rfl) ⟨674486, by rfl⟩ : syracuseStep 899315 = 1348973) B1348973
theorem B899351 : Blo 397767 899351 := bstep (se 1 (by rfl) ⟨674513, by rfl⟩ : syracuseStep 899351 = 1349027) B1349027
theorem B56342897 : Blo 397767 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B899531 : Blo 397767 899531 := bstep (se 1 (by rfl) ⟨674648, by rfl⟩ : syracuseStep 899531 = 1349297) B1349297
theorem B899585 : Blo 397767 899585 := bstep (se 2 (by rfl) ⟨337344, by rfl⟩ : syracuseStep 899585 = 674689) B674689
theorem B768599 : Blo 397767 768599 := bstep (se 1 (by rfl) ⟨576449, by rfl⟩ : syracuseStep 768599 = 1152899) B1152899
theorem B3422897 : Blo 397767 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B899801 : Blo 397767 899801 := bstep (se 2 (by rfl) ⟨337425, by rfl⟩ : syracuseStep 899801 = 674851) B674851
theorem B899891 : Blo 397767 899891 := bstep (se 1 (by rfl) ⟨674918, by rfl⟩ : syracuseStep 899891 = 1349837) B1349837
theorem B1391411 : Blo 397767 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B899927 : Blo 397767 899927 := bstep (se 1 (by rfl) ⟨674945, by rfl⟩ : syracuseStep 899927 = 1349891) B1349891
theorem B1522577 : Blo 397767 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B506827 : Blo 397767 506827 := bstep (se 1 (by rfl) ⟨380120, by rfl⟩ : syracuseStep 506827 = 760241) B760241
theorem B539659 : Blo 397767 539659 := bstep (se 1 (by rfl) ⟨404744, by rfl⟩ : syracuseStep 539659 = 809489) B809489
theorem B900107 : Blo 397767 900107 := bstep (se 1 (by rfl) ⟨675080, by rfl⟩ : syracuseStep 900107 = 1350161) B1350161
theorem B900161 : Blo 397767 900161 := bstep (se 2 (by rfl) ⟨337560, by rfl⟩ : syracuseStep 900161 = 675121) B675121
theorem B2276531 : Blo 397767 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B900377 : Blo 397767 900377 := bstep (se 2 (by rfl) ⟨337641, by rfl⟩ : syracuseStep 900377 = 675283) B675283
theorem B769367 : Blo 397767 769367 := bstep (se 1 (by rfl) ⟨577025, by rfl⟩ : syracuseStep 769367 = 1154051) B1154051
theorem B1523033 : Blo 397767 1523033 := bstep (se 2 (by rfl) ⟨571137, by rfl⟩ : syracuseStep 1523033 = 1142275) B1142275
theorem B1949021 : Blo 397767 1949021 := bstep (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) B730883
theorem B900467 : Blo 397767 900467 := bstep (se 1 (by rfl) ⟨675350, by rfl⟩ : syracuseStep 900467 = 1350701) B1350701
theorem B900503 : Blo 397767 900503 := bstep (se 1 (by rfl) ⟨675377, by rfl⟩ : syracuseStep 900503 = 1350755) B1350755
theorem B1523245 : Blo 397767 1523245 := bstep (se 3 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 1523245 = 571217) B571217
theorem B900683 : Blo 397767 900683 := bstep (se 1 (by rfl) ⟨675512, by rfl⟩ : syracuseStep 900683 = 1351025) B1351025
theorem B671321 : Blo 397767 671321 := bstep (se 2 (by rfl) ⟨251745, by rfl⟩ : syracuseStep 671321 = 503491) B503491
theorem B2637413 : Blo 397767 2637413 := bstep (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) B494515
theorem B900737 : Blo 397767 900737 := bstep (se 2 (by rfl) ⟨337776, by rfl⟩ : syracuseStep 900737 = 675553) B675553
theorem B20790989 : Blo 397767 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B4570829 : Blo 397767 4570829 := bstep (se 3 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 4570829 = 1714061) B1714061
theorem B671449 : Blo 397767 671449 := bstep (se 2 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 671449 = 503587) B503587
theorem B900953 : Blo 397767 900953 := bstep (se 2 (by rfl) ⟨337857, by rfl⟩ : syracuseStep 900953 = 675715) B675715
theorem B1523549 : Blo 397767 1523549 := bstep (se 3 (by rfl) ⟨285665, by rfl⟩ : syracuseStep 1523549 = 571331) B571331
theorem B507799 : Blo 397767 507799 := bstep (se 1 (by rfl) ⟨380849, by rfl⟩ : syracuseStep 507799 = 761699) B761699
theorem B901043 : Blo 397767 901043 := bstep (se 1 (by rfl) ⟨675782, by rfl⟩ : syracuseStep 901043 = 1351565) B1351565
theorem B638923 : Blo 397767 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B901079 : Blo 397767 901079 := bstep (se 1 (by rfl) ⟨675809, by rfl⟩ : syracuseStep 901079 = 1351619) B1351619
theorem B540697 : Blo 397767 540697 := bstep (se 2 (by rfl) ⟨202761, by rfl⟩ : syracuseStep 540697 = 405523) B405523
theorem B7258243 : Blo 397767 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B901259 : Blo 397767 901259 := bstep (se 1 (by rfl) ⟨675944, by rfl⟩ : syracuseStep 901259 = 1351889) B1351889
theorem B901313 : Blo 397767 901313 := bstep (se 2 (by rfl) ⟨337992, by rfl⟩ : syracuseStep 901313 = 675985) B675985
theorem B2572505 : Blo 397767 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B672023 : Blo 397767 672023 := bstep (se 1 (by rfl) ⟨504017, by rfl⟩ : syracuseStep 672023 = 1008035) B1008035
theorem B2441603 : Blo 397767 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B672151 : Blo 397767 672151 := bstep (se 1 (by rfl) ⟨504113, by rfl⟩ : syracuseStep 672151 = 1008227) B1008227
theorem B901529 : Blo 397767 901529 := bstep (se 2 (by rfl) ⟨338073, by rfl⟩ : syracuseStep 901529 = 676147) B676147
theorem B901619 : Blo 397767 901619 := bstep (se 1 (by rfl) ⟨676214, by rfl⟩ : syracuseStep 901619 = 1352429) B1352429
theorem B901655 : Blo 397767 901655 := bstep (se 1 (by rfl) ⟨676241, by rfl⟩ : syracuseStep 901655 = 1352483) B1352483
theorem B2277989 : Blo 397767 2277989 := bstep (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) B427123
theorem B901835 : Blo 397767 901835 := bstep (se 1 (by rfl) ⟨676376, by rfl⟩ : syracuseStep 901835 = 1352753) B1352753
theorem B901889 : Blo 397767 901889 := bstep (se 2 (by rfl) ⟨338208, by rfl⟩ : syracuseStep 901889 = 676417) B676417
theorem B902105 : Blo 397767 902105 := bstep (se 2 (by rfl) ⟨338289, by rfl⟩ : syracuseStep 902105 = 676579) B676579
theorem B672779 : Blo 397767 672779 := bstep (se 1 (by rfl) ⟨504584, by rfl⟩ : syracuseStep 672779 = 1009169) B1009169
theorem B902195 : Blo 397767 902195 := bstep (se 1 (by rfl) ⟨676646, by rfl⟩ : syracuseStep 902195 = 1353293) B1353293
theorem B902231 : Blo 397767 902231 := bstep (se 1 (by rfl) ⟨676673, by rfl⟩ : syracuseStep 902231 = 1353347) B1353347
theorem B672907 : Blo 397767 672907 := bstep (se 1 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 672907 = 1009361) B1009361
theorem B640153 : Blo 397767 640153 := bstep (se 2 (by rfl) ⟨240057, by rfl⟩ : syracuseStep 640153 = 480115) B480115
theorem B902411 : Blo 397767 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B673049 : Blo 397767 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B9684269 : Blo 397767 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B902465 : Blo 397767 902465 := bstep (se 2 (by rfl) ⟨338424, by rfl⟩ : syracuseStep 902465 = 676849) B676849
theorem B673177 : Blo 397767 673177 := bstep (se 2 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 673177 = 504883) B504883
theorem B902681 : Blo 397767 902681 := bstep (se 2 (by rfl) ⟨338505, by rfl⟩ : syracuseStep 902681 = 677011) B677011
theorem B2442845 : Blo 397767 2442845 := bstep (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) B916067
theorem B902771 : Blo 397767 902771 := bstep (se 1 (by rfl) ⟨677078, by rfl⟩ : syracuseStep 902771 = 1354157) B1354157
theorem B2016899 : Blo 397767 2016899 := bstep (se 1 (by rfl) ⟨1512674, by rfl⟩ : syracuseStep 2016899 = 3025349) B3025349
theorem B902807 : Blo 397767 902807 := bstep (se 1 (by rfl) ⟨677105, by rfl⟩ : syracuseStep 902807 = 1354211) B1354211
theorem B2737937 : Blo 397767 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B902987 : Blo 397767 902987 := bstep (se 1 (by rfl) ⟨677240, by rfl⟩ : syracuseStep 902987 = 1354481) B1354481
theorem B903041 : Blo 397767 903041 := bstep (se 2 (by rfl) ⟨338640, by rfl⟩ : syracuseStep 903041 = 677281) B677281
theorem B673751 : Blo 397767 673751 := bstep (se 1 (by rfl) ⟨505313, by rfl⟩ : syracuseStep 673751 = 1010627) B1010627
theorem B4376537 : Blo 397767 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B673879 : Blo 397767 673879 := bstep (se 1 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 673879 = 1010819) B1010819
theorem B903257 : Blo 397767 903257 := bstep (se 2 (by rfl) ⟨338721, by rfl⟩ : syracuseStep 903257 = 677443) B677443
theorem B1460369 : Blo 397767 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B903347 : Blo 397767 903347 := bstep (se 1 (by rfl) ⟨677510, by rfl⟩ : syracuseStep 903347 = 1355021) B1355021
theorem B903383 : Blo 397767 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B903563 : Blo 397767 903563 := bstep (se 1 (by rfl) ⟨677672, by rfl⟩ : syracuseStep 903563 = 1355345) B1355345
theorem B903617 : Blo 397767 903617 := bstep (se 2 (by rfl) ⟨338856, by rfl⟩ : syracuseStep 903617 = 677713) B677713
theorem B1133003 : Blo 397767 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B903833 : Blo 397767 903833 := bstep (se 2 (by rfl) ⟨338937, by rfl⟩ : syracuseStep 903833 = 677875) B677875
theorem B2869937 : Blo 397767 2869937 := bstep (se 2 (by rfl) ⟨1076226, by rfl⟩ : syracuseStep 2869937 = 2152453) B2152453
theorem B674507 : Blo 397767 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B903923 : Blo 397767 903923 := bstep (se 1 (by rfl) ⟨677942, by rfl⟩ : syracuseStep 903923 = 1355885) B1355885
theorem B903959 : Blo 397767 903959 := bstep (se 1 (by rfl) ⟨677969, by rfl⟩ : syracuseStep 903959 = 1355939) B1355939
theorem B674635 : Blo 397767 674635 := bstep (se 1 (by rfl) ⟨505976, by rfl⟩ : syracuseStep 674635 = 1011953) B1011953
theorem B674777 : Blo 397767 674777 := bstep (se 2 (by rfl) ⟨253041, by rfl⟩ : syracuseStep 674777 = 506083) B506083
theorem B674905 : Blo 397767 674905 := bstep (se 2 (by rfl) ⟨253089, by rfl⟩ : syracuseStep 674905 = 506179) B506179
theorem B609623 : Blo 397767 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B675479 : Blo 397767 675479 := bstep (se 1 (by rfl) ⟨506609, by rfl⟩ : syracuseStep 675479 = 1013219) B1013219
theorem B675607 : Blo 397767 675607 := bstep (se 1 (by rfl) ⟨506705, by rfl⟩ : syracuseStep 675607 = 1013411) B1013411
theorem B5099537 : Blo 397767 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B1134643 : Blo 397767 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B970841 : Blo 397767 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B5492941 : Blo 397767 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B676235 : Blo 397767 676235 := bstep (se 1 (by rfl) ⟨507176, by rfl⟩ : syracuseStep 676235 = 1014353) B1014353
theorem B676363 : Blo 397767 676363 := bstep (se 1 (by rfl) ⟨507272, by rfl⟩ : syracuseStep 676363 = 1014545) B1014545
theorem B4543127 : Blo 397767 4543127 := bstep (se 1 (by rfl) ⟨3407345, by rfl⟩ : syracuseStep 4543127 = 6814691) B6814691
theorem B676505 : Blo 397767 676505 := bstep (se 2 (by rfl) ⟨253689, by rfl⟩ : syracuseStep 676505 = 507379) B507379
theorem B807641 : Blo 397767 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B5788421 : Blo 397767 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B676633 : Blo 397767 676633 := bstep (se 2 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 676633 = 507475) B507475
theorem B2053043 : Blo 397767 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B447511 : Blo 397767 447511 := bstep (se 1 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 447511 = 671267) B671267
theorem B1922093 : Blo 397767 1922093 := bstep (se 3 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 1922093 = 720785) B720785
theorem B1135691 : Blo 397767 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B447691 : Blo 397767 447691 := bstep (se 1 (by rfl) ⟨335768, by rfl⟩ : syracuseStep 447691 = 671537) B671537
theorem B2020625 : Blo 397767 2020625 := bstep (se 2 (by rfl) ⟨757734, by rfl⟩ : syracuseStep 2020625 = 1515469) B1515469
theorem B447799 : Blo 397767 447799 := bstep (se 1 (by rfl) ⟨335849, by rfl⟩ : syracuseStep 447799 = 671699) B671699
theorem B677207 : Blo 397767 677207 := bstep (se 1 (by rfl) ⟨507905, by rfl⟩ : syracuseStep 677207 = 1015811) B1015811
theorem B808321 : Blo 397767 808321 := bstep (se 2 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 808321 = 606241) B606241
theorem B2020787 : Blo 397767 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B808385 : Blo 397767 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B677335 : Blo 397767 677335 := bstep (se 1 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 677335 = 1016003) B1016003
theorem B447979 : Blo 397767 447979 := bstep (se 1 (by rfl) ⟨335984, by rfl⟩ : syracuseStep 447979 = 671969) B671969
theorem B1955393 : Blo 397767 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B448087 : Blo 397767 448087 := bstep (se 1 (by rfl) ⟨336065, by rfl⟩ : syracuseStep 448087 = 672131) B672131
theorem B448267 : Blo 397767 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B448375 : Blo 397767 448375 := bstep (se 1 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 448375 = 672563) B672563
theorem B448555 : Blo 397767 448555 := bstep (se 1 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 448555 = 672833) B672833
theorem B677963 : Blo 397767 677963 := bstep (se 1 (by rfl) ⟨508472, by rfl⟩ : syracuseStep 677963 = 1016945) B1016945
theorem B448663 : Blo 397767 448663 := bstep (se 1 (by rfl) ⟨336497, by rfl⟩ : syracuseStep 448663 = 672995) B672995
theorem B2283821 : Blo 397767 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B448843 : Blo 397767 448843 := bstep (se 1 (by rfl) ⟨336632, by rfl⟩ : syracuseStep 448843 = 673265) B673265
theorem B448951 : Blo 397767 448951 := bstep (se 1 (by rfl) ⟨336713, by rfl⟩ : syracuseStep 448951 = 673427) B673427
theorem B907865 : Blo 397767 907865 := bstep (se 2 (by rfl) ⟨340449, by rfl⟩ : syracuseStep 907865 = 680899) B680899
theorem B449131 : Blo 397767 449131 := bstep (se 1 (by rfl) ⟨336848, by rfl⟩ : syracuseStep 449131 = 673697) B673697
theorem B1137331 : Blo 397767 1137331 := bstep (se 1 (by rfl) ⟨852998, by rfl⟩ : syracuseStep 1137331 = 1705997) B1705997
theorem B449239 : Blo 397767 449239 := bstep (se 1 (by rfl) ⟨336929, by rfl⟩ : syracuseStep 449239 = 673859) B673859
theorem B1366807 : Blo 397767 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B5561189 : Blo 397767 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B449419 : Blo 397767 449419 := bstep (se 1 (by rfl) ⟨337064, by rfl⟩ : syracuseStep 449419 = 674129) B674129
theorem B1137559 : Blo 397767 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B5102513 : Blo 397767 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B449527 : Blo 397767 449527 := bstep (se 1 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 449527 = 674291) B674291
theorem B810137 : Blo 397767 810137 := bstep (se 2 (by rfl) ⟨303801, by rfl⟩ : syracuseStep 810137 = 607603) B607603
theorem B449707 : Blo 397767 449707 := bstep (se 1 (by rfl) ⟨337280, by rfl⟩ : syracuseStep 449707 = 674561) B674561
theorem B1531097 : Blo 397767 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B449815 : Blo 397767 449815 := bstep (se 1 (by rfl) ⟨337361, by rfl⟩ : syracuseStep 449815 = 674723) B674723
theorem B2022731 : Blo 397767 2022731 := bstep (se 1 (by rfl) ⟨1517048, by rfl⟩ : syracuseStep 2022731 = 3034097) B3034097
theorem B449995 : Blo 397767 449995 := bstep (se 1 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 449995 = 674993) B674993
theorem B2153945 : Blo 397767 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B450103 : Blo 397767 450103 := bstep (se 1 (by rfl) ⟨337577, by rfl⟩ : syracuseStep 450103 = 675155) B675155
theorem B1007255 : Blo 397767 1007255 := bstep (se 1 (by rfl) ⟨755441, by rfl⟩ : syracuseStep 1007255 = 1510883) B1510883
theorem B450283 : Blo 397767 450283 := bstep (se 1 (by rfl) ⟨337712, by rfl⟩ : syracuseStep 450283 = 675425) B675425
theorem B450391 : Blo 397767 450391 := bstep (se 1 (by rfl) ⟨337793, by rfl⟩ : syracuseStep 450391 = 675587) B675587
theorem B3432293 : Blo 397767 3432293 := bstep (se 4 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 3432293 = 643555) B643555
theorem B450571 : Blo 397767 450571 := bstep (se 1 (by rfl) ⟨337928, by rfl⟩ : syracuseStep 450571 = 675857) B675857
theorem B450679 : Blo 397767 450679 := bstep (se 1 (by rfl) ⟨338009, by rfl⟩ : syracuseStep 450679 = 676019) B676019
theorem B450859 : Blo 397767 450859 := bstep (se 1 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 450859 = 676289) B676289
theorem B1007923 : Blo 397767 1007923 := bstep (se 1 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 1007923 = 1511885) B1511885
theorem B450967 : Blo 397767 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B1008065 : Blo 397767 1008065 := bstep (se 2 (by rfl) ⟨378024, by rfl⟩ : syracuseStep 1008065 = 756049) B756049
theorem B451147 : Blo 397767 451147 := bstep (se 1 (by rfl) ⟨338360, by rfl⟩ : syracuseStep 451147 = 676721) B676721
theorem B451255 : Blo 397767 451255 := bstep (se 1 (by rfl) ⟨338441, by rfl⟩ : syracuseStep 451255 = 676883) B676883
theorem B1139417 : Blo 397767 1139417 := bstep (se 2 (by rfl) ⟨427281, by rfl⟩ : syracuseStep 1139417 = 854563) B854563
theorem B451435 : Blo 397767 451435 := bstep (se 1 (by rfl) ⟨338576, by rfl⟩ : syracuseStep 451435 = 677153) B677153
theorem B451543 : Blo 397767 451543 := bstep (se 1 (by rfl) ⟨338657, by rfl⟩ : syracuseStep 451543 = 677315) B677315
theorem B2024513 : Blo 397767 2024513 := bstep (se 2 (by rfl) ⟨759192, by rfl⟩ : syracuseStep 2024513 = 1518385) B1518385
theorem B451723 : Blo 397767 451723 := bstep (se 1 (by rfl) ⟨338792, by rfl⟩ : syracuseStep 451723 = 677585) B677585
theorem B9757847 : Blo 397767 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B910529 : Blo 397767 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B451831 : Blo 397767 451831 := bstep (se 1 (by rfl) ⟨338873, by rfl⟩ : syracuseStep 451831 = 677747) B677747
theorem B681419 : Blo 397767 681419 := bstep (se 1 (by rfl) ⟨511064, by rfl⟩ : syracuseStep 681419 = 1022129) B1022129
theorem B812531 : Blo 397767 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B1140247 : Blo 397767 1140247 := bstep (se 1 (by rfl) ⟨855185, by rfl⟩ : syracuseStep 1140247 = 1710371) B1710371
theorem B1009331 : Blo 397767 1009331 := bstep (se 1 (by rfl) ⟨756998, by rfl⟩ : syracuseStep 1009331 = 1513997) B1513997
theorem B2287511 : Blo 397767 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B3827729 : Blo 397767 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B1927243 : Blo 397767 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B1009867 : Blo 397767 1009867 := bstep (se 1 (by rfl) ⟨757400, by rfl⟩ : syracuseStep 1009867 = 1514801) B1514801
theorem B1141067 : Blo 397767 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B1010009 : Blo 397767 1010009 := bstep (se 2 (by rfl) ⟨378753, by rfl⟩ : syracuseStep 1010009 = 757507) B757507
theorem B6810317 : Blo 397767 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B813835 : Blo 397767 813835 := bstep (se 1 (by rfl) ⟨610376, by rfl⟩ : syracuseStep 813835 = 1220753) B1220753
theorem B1436467 : Blo 397767 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B682967 : Blo 397767 682967 := bstep (se 1 (by rfl) ⟨512225, by rfl⟩ : syracuseStep 682967 = 1024451) B1024451
theorem B2026457 : Blo 397767 2026457 := bstep (se 2 (by rfl) ⟨759921, by rfl⟩ : syracuseStep 2026457 = 1519843) B1519843
theorem B1010839 : Blo 397767 1010839 := bstep (se 1 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 1010839 = 1516259) B1516259
theorem B1830109 : Blo 397767 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B1273153 : Blo 397767 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B1371485 : Blo 397767 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B1830289 : Blo 397767 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1928627 : Blo 397767 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B1011275 : Blo 397767 1011275 := bstep (se 1 (by rfl) ⟨758456, by rfl⟩ : syracuseStep 1011275 = 1516913) B1516913
theorem B1011649 : Blo 397767 1011649 := bstep (se 2 (by rfl) ⟨379368, by rfl⟩ : syracuseStep 1011649 = 758737) B758737
theorem B716951 : Blo 397767 716951 := bstep (se 1 (by rfl) ⟨537713, by rfl⟩ : syracuseStep 716951 = 1075427) B1075427
theorem B6942871 : Blo 397767 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B1700119 : Blo 397767 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B913739 : Blo 397767 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B1700189 : Blo 397767 1700189 := bstep (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) B637571
theorem B2158979 : Blo 397767 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1012247 : Blo 397767 1012247 := bstep (se 1 (by rfl) ⟨759185, by rfl⟩ : syracuseStep 1012247 = 1518371) B1518371
theorem B2028077 : Blo 397767 2028077 := bstep (se 3 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 2028077 = 760529) B760529
theorem B2585239 : Blo 397767 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B1143517 : Blo 397767 1143517 := bstep (se 3 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 1143517 = 428819) B428819
theorem B914177 : Blo 397767 914177 := bstep (se 2 (by rfl) ⟨342816, by rfl⟩ : syracuseStep 914177 = 685633) B685633
theorem B2880461 : Blo 397767 2880461 := bstep (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) B1080173
theorem B2552897 : Blo 397767 2552897 := bstep (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) B1914673
theorem B1700939 : Blo 397767 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B2946179 : Blo 397767 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B2553049 : Blo 397767 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B1930513 : Blo 397767 1930513 := bstep (se 2 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 1930513 = 1447885) B1447885
theorem B718103 : Blo 397767 718103 := bstep (se 1 (by rfl) ⟨538577, by rfl⟩ : syracuseStep 718103 = 1077155) B1077155
theorem B1013057 : Blo 397767 1013057 := bstep (se 2 (by rfl) ⟨379896, by rfl⟩ : syracuseStep 1013057 = 759793) B759793
theorem B2880947 : Blo 397767 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B685579 : Blo 397767 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1537625 : Blo 397767 1537625 := bstep (se 2 (by rfl) ⟨576609, by rfl⟩ : syracuseStep 1537625 = 1153219) B1153219
theorem B1013593 : Blo 397767 1013593 := bstep (se 2 (by rfl) ⟨380097, by rfl⟩ : syracuseStep 1013593 = 760195) B760195
theorem B915457 : Blo 397767 915457 := bstep (se 2 (by rfl) ⟨343296, by rfl⟩ : syracuseStep 915457 = 686593) B686593
theorem B555031 : Blo 397767 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B850009 : Blo 397767 850009 := bstep (se 2 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 850009 = 637507) B637507
theorem B850265 : Blo 397767 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B850675 : Blo 397767 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1080139 : Blo 397767 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B424855 : Blo 397767 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B1014707 : Blo 397767 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B720065 : Blo 397767 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B1015001 : Blo 397767 1015001 := bstep (se 2 (by rfl) ⟨380625, by rfl⟩ : syracuseStep 1015001 = 761251) B761251
theorem B1342871 : Blo 397767 1342871 := bstep (se 1 (by rfl) ⟨1007153, by rfl⟩ : syracuseStep 1342871 = 2014307) B2014307
theorem B851393 : Blo 397767 851393 := bstep (se 2 (by rfl) ⟨319272, by rfl⟩ : syracuseStep 851393 = 638545) B638545
theorem B425611 : Blo 397767 425611 := bstep (se 1 (by rfl) ⟨319208, by rfl⟩ : syracuseStep 425611 = 638417) B638417
theorem B851735 : Blo 397767 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B1343411 : Blo 397767 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B851905 : Blo 397767 851905 := bstep (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) B638929
theorem B1441729 : Blo 397767 1441729 := bstep (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) B1081297
theorem B2883545 : Blo 397767 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B720929 : Blo 397767 720929 := bstep (se 2 (by rfl) ⟨270348, by rfl⟩ : syracuseStep 720929 = 540697) B540697
theorem B1015841 : Blo 397767 1015841 := bstep (se 2 (by rfl) ⟨380940, by rfl⟩ : syracuseStep 1015841 = 761881) B761881
theorem B1343897 : Blo 397767 1343897 := bstep (se 2 (by rfl) ⟨503961, by rfl⟩ : syracuseStep 1343897 = 1007923) B1007923
theorem B2884061 : Blo 397767 2884061 := bstep (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) B1081523
theorem B2556535 : Blo 397767 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B4326007 : Blo 397767 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B1082173 : Blo 397767 1082173 := bstep (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) B405815
theorem B6456179 : Blo 397767 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B1016833 : Blo 397767 1016833 := bstep (se 2 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 1016833 = 762625) B762625
theorem B29295685 : Blo 397767 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B1344599 : Blo 397767 1344599 := bstep (se 1 (by rfl) ⟨1008449, by rfl⟩ : syracuseStep 1344599 = 2016899) B2016899
theorem B2917691 : Blo 397767 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B1279385 : Blo 397767 1279385 := bstep (se 2 (by rfl) ⟨479769, by rfl⟩ : syracuseStep 1279385 = 959539) B959539
theorem B2033099 : Blo 397767 2033099 := bstep (se 1 (by rfl) ⟨1524824, by rfl⟩ : syracuseStep 2033099 = 3049649) B3049649
theorem B1345085 : Blo 397767 1345085 := bstep (se 3 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 1345085 = 504407) B504407
theorem B1050199 : Blo 397767 1050199 := bstep (se 1 (by rfl) ⟨787649, by rfl⟩ : syracuseStep 1050199 = 1575299) B1575299
theorem B1443415 : Blo 397767 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B755335 : Blo 397767 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B2033423 : Blo 397767 2033423 := bstep (se 1 (by rfl) ⟨1525067, by rfl⟩ : syracuseStep 2033423 = 3050135) B3050135
theorem B1706255 : Blo 397767 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B4950821 : Blo 397767 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B723755 : Blo 397767 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B2165555 : Blo 397767 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B1346489 : Blo 397767 1346489 := bstep (se 2 (by rfl) ⟨504933, by rfl⟩ : syracuseStep 1346489 = 1009867) B1009867
theorem B887753 : Blo 397767 887753 := bstep (se 2 (by rfl) ⟨332907, by rfl⟩ : syracuseStep 887753 = 665815) B665815
theorem B855083 : Blo 397767 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B12946493 : Blo 397767 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B1281395 : Blo 397767 1281395 := bstep (se 1 (by rfl) ⟨961046, by rfl⟩ : syracuseStep 1281395 = 1922093) B1922093
theorem B757127 : Blo 397767 757127 := bstep (se 1 (by rfl) ⟨567845, by rfl⟩ : syracuseStep 757127 = 1135691) B1135691
theorem B1347083 : Blo 397767 1347083 := bstep (se 1 (by rfl) ⟨1010312, by rfl⟩ : syracuseStep 1347083 = 2020625) B2020625
theorem B2887235 : Blo 397767 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B1347191 : Blo 397767 1347191 := bstep (se 1 (by rfl) ⟨1010393, by rfl⟩ : syracuseStep 1347191 = 2020787) B2020787
theorem B1085113 : Blo 397767 1085113 := bstep (se 2 (by rfl) ⟨406917, by rfl⟩ : syracuseStep 1085113 = 813835) B813835
theorem B1969921 : Blo 397767 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B1707911 : Blo 397767 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B2166749 : Blo 397767 2166749 := bstep (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) B812531
theorem B1347785 : Blo 397767 1347785 := bstep (se 2 (by rfl) ⟨505419, by rfl⟩ : syracuseStep 1347785 = 1010839) B1010839
theorem B3281411 : Blo 397767 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B397831 : Blo 397767 397831 := bstep (se 1 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 397831 = 596747) B596747
theorem B397839 : Blo 397767 397839 := bstep (se 1 (by rfl) ⟨298379, by rfl⟩ : syracuseStep 397839 = 596759) B596759
theorem B397883 : Blo 397767 397883 := bstep (se 1 (by rfl) ⟨298412, by rfl⟩ : syracuseStep 397883 = 596825) B596825
theorem B3707459 : Blo 397767 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B397959 : Blo 397767 397959 := bstep (se 1 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 397959 = 596939) B596939
theorem B397967 : Blo 397767 397967 := bstep (se 1 (by rfl) ⟨298475, by rfl⟩ : syracuseStep 397967 = 596951) B596951
theorem B8622773 : Blo 397767 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B398011 : Blo 397767 398011 := bstep (se 1 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 398011 = 597017) B597017
theorem B463547 : Blo 397767 463547 := bstep (se 1 (by rfl) ⟨347660, by rfl⟩ : syracuseStep 463547 = 695321) B695321
theorem B398087 : Blo 397767 398087 := bstep (se 1 (by rfl) ⟨298565, by rfl⟩ : syracuseStep 398087 = 597131) B597131
theorem B398095 : Blo 397767 398095 := bstep (se 1 (by rfl) ⟨298571, by rfl⟩ : syracuseStep 398095 = 597143) B597143
theorem B2265893 : Blo 397767 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B1020731 : Blo 397767 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B398139 : Blo 397767 398139 := bstep (se 1 (by rfl) ⟨298604, by rfl⟩ : syracuseStep 398139 = 597209) B597209
theorem B398215 : Blo 397767 398215 := bstep (se 1 (by rfl) ⟨298661, by rfl⟩ : syracuseStep 398215 = 597323) B597323
theorem B1348487 : Blo 397767 1348487 := bstep (se 1 (by rfl) ⟨1011365, by rfl⟩ : syracuseStep 1348487 = 2022731) B2022731
theorem B398223 : Blo 397767 398223 := bstep (se 1 (by rfl) ⟨298667, by rfl⟩ : syracuseStep 398223 = 597335) B597335
theorem B398267 : Blo 397767 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B398343 : Blo 397767 398343 := bstep (se 1 (by rfl) ⟨298757, by rfl⟩ : syracuseStep 398343 = 597515) B597515
theorem B398351 : Blo 397767 398351 := bstep (se 1 (by rfl) ⟨298763, by rfl⟩ : syracuseStep 398351 = 597527) B597527
theorem B398395 : Blo 397767 398395 := bstep (se 1 (by rfl) ⟨298796, by rfl⟩ : syracuseStep 398395 = 597593) B597593
theorem B398471 : Blo 397767 398471 := bstep (se 1 (by rfl) ⟨298853, by rfl⟩ : syracuseStep 398471 = 597707) B597707
theorem B398479 : Blo 397767 398479 := bstep (se 1 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 398479 = 597719) B597719
theorem B398523 : Blo 397767 398523 := bstep (se 1 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 398523 = 597785) B597785
theorem B1348865 : Blo 397767 1348865 := bstep (se 2 (by rfl) ⟨505824, by rfl⟩ : syracuseStep 1348865 = 1011649) B1011649
theorem B398599 : Blo 397767 398599 := bstep (se 1 (by rfl) ⟨298949, by rfl⟩ : syracuseStep 398599 = 597899) B597899
theorem B398607 : Blo 397767 398607 := bstep (se 1 (by rfl) ⟨298955, by rfl⟩ : syracuseStep 398607 = 597911) B597911
theorem B398651 : Blo 397767 398651 := bstep (se 1 (by rfl) ⟨298988, by rfl⟩ : syracuseStep 398651 = 597977) B597977
theorem B398727 : Blo 397767 398727 := bstep (se 1 (by rfl) ⟨299045, by rfl⟩ : syracuseStep 398727 = 598091) B598091
theorem B398735 : Blo 397767 398735 := bstep (se 1 (by rfl) ⟨299051, by rfl⟩ : syracuseStep 398735 = 598103) B598103
theorem B1512857 : Blo 397767 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B398779 : Blo 397767 398779 := bstep (se 1 (by rfl) ⟨299084, by rfl⟩ : syracuseStep 398779 = 598169) B598169
theorem B398855 : Blo 397767 398855 := bstep (se 1 (by rfl) ⟨299141, by rfl⟩ : syracuseStep 398855 = 598283) B598283
theorem B398863 : Blo 397767 398863 := bstep (se 1 (by rfl) ⟨299147, by rfl⟩ : syracuseStep 398863 = 598295) B598295
theorem B398907 : Blo 397767 398907 := bstep (se 1 (by rfl) ⟨299180, by rfl⟩ : syracuseStep 398907 = 598361) B598361
theorem B1709687 : Blo 397767 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B398983 : Blo 397767 398983 := bstep (se 1 (by rfl) ⟨299237, by rfl⟩ : syracuseStep 398983 = 598475) B598475
theorem B398991 : Blo 397767 398991 := bstep (se 1 (by rfl) ⟨299243, by rfl⟩ : syracuseStep 398991 = 598487) B598487
theorem B399035 : Blo 397767 399035 := bstep (se 1 (by rfl) ⟨299276, by rfl⟩ : syracuseStep 399035 = 598553) B598553
theorem B2266825 : Blo 397767 2266825 := bstep (se 2 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 2266825 = 1700119) B1700119
theorem B399111 : Blo 397767 399111 := bstep (se 1 (by rfl) ⟨299333, by rfl⟩ : syracuseStep 399111 = 598667) B598667
theorem B399119 : Blo 397767 399119 := bstep (se 1 (by rfl) ⟨299339, by rfl⟩ : syracuseStep 399119 = 598679) B598679
theorem B399163 : Blo 397767 399163 := bstep (se 1 (by rfl) ⟨299372, by rfl⟩ : syracuseStep 399163 = 598745) B598745
theorem B759611 : Blo 397767 759611 := bstep (se 1 (by rfl) ⟨569708, by rfl⟩ : syracuseStep 759611 = 1139417) B1139417
theorem B399239 : Blo 397767 399239 := bstep (se 1 (by rfl) ⟨299429, by rfl⟩ : syracuseStep 399239 = 598859) B598859
theorem B399247 : Blo 397767 399247 := bstep (se 1 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 399247 = 598871) B598871
theorem B399291 : Blo 397767 399291 := bstep (se 1 (by rfl) ⟨299468, by rfl⟩ : syracuseStep 399291 = 598937) B598937
theorem B399367 : Blo 397767 399367 := bstep (se 1 (by rfl) ⟨299525, by rfl⟩ : syracuseStep 399367 = 599051) B599051
theorem B399375 : Blo 397767 399375 := bstep (se 1 (by rfl) ⟨299531, by rfl⟩ : syracuseStep 399375 = 599063) B599063
theorem B1349675 : Blo 397767 1349675 := bstep (se 1 (by rfl) ⟨1012256, by rfl⟩ : syracuseStep 1349675 = 2024513) B2024513
theorem B399419 : Blo 397767 399419 := bstep (se 1 (by rfl) ⟨299564, by rfl⟩ : syracuseStep 399419 = 599129) B599129
theorem B3414149 : Blo 397767 3414149 := bstep (se 4 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 3414149 = 640153) B640153
theorem B399495 : Blo 397767 399495 := bstep (se 1 (by rfl) ⟨299621, by rfl⟩ : syracuseStep 399495 = 599243) B599243
theorem B399503 : Blo 397767 399503 := bstep (se 1 (by rfl) ⟨299627, by rfl⟩ : syracuseStep 399503 = 599255) B599255
theorem B399547 : Blo 397767 399547 := bstep (se 1 (by rfl) ⟨299660, by rfl⟩ : syracuseStep 399547 = 599321) B599321
theorem B399623 : Blo 397767 399623 := bstep (se 1 (by rfl) ⟨299717, by rfl⟩ : syracuseStep 399623 = 599435) B599435
theorem B399631 : Blo 397767 399631 := bstep (se 1 (by rfl) ⟨299723, by rfl⟩ : syracuseStep 399631 = 599447) B599447
theorem B760097 : Blo 397767 760097 := bstep (se 2 (by rfl) ⟨285036, by rfl⟩ : syracuseStep 760097 = 570073) B570073
theorem B399675 : Blo 397767 399675 := bstep (se 1 (by rfl) ⟨299756, by rfl⟩ : syracuseStep 399675 = 599513) B599513
theorem B399751 : Blo 397767 399751 := bstep (se 1 (by rfl) ⟨299813, by rfl⟩ : syracuseStep 399751 = 599627) B599627
theorem B399759 : Blo 397767 399759 := bstep (se 1 (by rfl) ⟨299819, by rfl⟩ : syracuseStep 399759 = 599639) B599639
theorem B399803 : Blo 397767 399803 := bstep (se 1 (by rfl) ⟨299852, by rfl⟩ : syracuseStep 399803 = 599705) B599705
theorem B399879 : Blo 397767 399879 := bstep (se 1 (by rfl) ⟨299909, by rfl⟩ : syracuseStep 399879 = 599819) B599819
theorem B399887 : Blo 397767 399887 := bstep (se 1 (by rfl) ⟨299915, by rfl⟩ : syracuseStep 399887 = 599831) B599831
theorem B399931 : Blo 397767 399931 := bstep (se 1 (by rfl) ⟨299948, by rfl⟩ : syracuseStep 399931 = 599897) B599897
theorem B1710679 : Blo 397767 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B400007 : Blo 397767 400007 := bstep (se 1 (by rfl) ⟨300005, by rfl⟩ : syracuseStep 400007 = 600011) B600011
theorem B400015 : Blo 397767 400015 := bstep (se 1 (by rfl) ⟨300011, by rfl⟩ : syracuseStep 400015 = 600023) B600023
theorem B596651 : Blo 397767 596651 := bstep (se 1 (by rfl) ⟨447488, by rfl⟩ : syracuseStep 596651 = 894977) B894977
theorem B400059 : Blo 397767 400059 := bstep (se 1 (by rfl) ⟨300044, by rfl⟩ : syracuseStep 400059 = 600089) B600089
theorem B596681 : Blo 397767 596681 := bstep (se 2 (by rfl) ⟨223755, by rfl⟩ : syracuseStep 596681 = 447511) B447511
theorem B400135 : Blo 397767 400135 := bstep (se 1 (by rfl) ⟨300101, by rfl⟩ : syracuseStep 400135 = 600203) B600203
theorem B924431 : Blo 397767 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B400143 : Blo 397767 400143 := bstep (se 1 (by rfl) ⟨300107, by rfl⟩ : syracuseStep 400143 = 600215) B600215
theorem B596795 : Blo 397767 596795 := bstep (se 1 (by rfl) ⟨447596, by rfl⟩ : syracuseStep 596795 = 895193) B895193
theorem B400187 : Blo 397767 400187 := bstep (se 1 (by rfl) ⟨300140, by rfl⟩ : syracuseStep 400187 = 600281) B600281
theorem B596855 : Blo 397767 596855 := bstep (se 1 (by rfl) ⟨447641, by rfl⟩ : syracuseStep 596855 = 895283) B895283
theorem B400263 : Blo 397767 400263 := bstep (se 1 (by rfl) ⟨300197, by rfl⟩ : syracuseStep 400263 = 600395) B600395
theorem B596879 : Blo 397767 596879 := bstep (se 1 (by rfl) ⟨447659, by rfl⟩ : syracuseStep 596879 = 895319) B895319
theorem B400271 : Blo 397767 400271 := bstep (se 1 (by rfl) ⟨300203, by rfl⟩ : syracuseStep 400271 = 600407) B600407
theorem B596921 : Blo 397767 596921 := bstep (se 2 (by rfl) ⟨223845, by rfl⟩ : syracuseStep 596921 = 447691) B447691
theorem B400315 : Blo 397767 400315 := bstep (se 1 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 400315 = 600473) B600473
theorem B596999 : Blo 397767 596999 := bstep (se 1 (by rfl) ⟨447749, by rfl⟩ : syracuseStep 596999 = 895499) B895499
theorem B400391 : Blo 397767 400391 := bstep (se 1 (by rfl) ⟨300293, by rfl⟩ : syracuseStep 400391 = 600587) B600587
theorem B400399 : Blo 397767 400399 := bstep (se 1 (by rfl) ⟨300299, by rfl⟩ : syracuseStep 400399 = 600599) B600599
theorem B597035 : Blo 397767 597035 := bstep (se 1 (by rfl) ⟨447776, by rfl⟩ : syracuseStep 597035 = 895553) B895553
theorem B400443 : Blo 397767 400443 := bstep (se 1 (by rfl) ⟨300332, by rfl⟩ : syracuseStep 400443 = 600665) B600665
theorem B597065 : Blo 397767 597065 := bstep (se 2 (by rfl) ⟨223899, by rfl⟩ : syracuseStep 597065 = 447799) B447799
theorem B1645655 : Blo 397767 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B400519 : Blo 397767 400519 := bstep (se 1 (by rfl) ⟨300389, by rfl⟩ : syracuseStep 400519 = 600779) B600779
theorem B400527 : Blo 397767 400527 := bstep (se 1 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 400527 = 600791) B600791
theorem B597179 : Blo 397767 597179 := bstep (se 1 (by rfl) ⟨447884, by rfl⟩ : syracuseStep 597179 = 895769) B895769
theorem B400571 : Blo 397767 400571 := bstep (se 1 (by rfl) ⟨300428, by rfl⟩ : syracuseStep 400571 = 600857) B600857
theorem B597239 : Blo 397767 597239 := bstep (se 1 (by rfl) ⟨447929, by rfl⟩ : syracuseStep 597239 = 895859) B895859
theorem B400647 : Blo 397767 400647 := bstep (se 1 (by rfl) ⟨300485, by rfl⟩ : syracuseStep 400647 = 600971) B600971
theorem B62594309 : Blo 397767 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B597263 : Blo 397767 597263 := bstep (se 1 (by rfl) ⟨447947, by rfl⟩ : syracuseStep 597263 = 895895) B895895
theorem B400655 : Blo 397767 400655 := bstep (se 1 (by rfl) ⟨300491, by rfl⟩ : syracuseStep 400655 = 600983) B600983
theorem B597305 : Blo 397767 597305 := bstep (se 2 (by rfl) ⟨223989, by rfl⟩ : syracuseStep 597305 = 447979) B447979
theorem B1350971 : Blo 397767 1350971 := bstep (se 1 (by rfl) ⟨1013228, by rfl⟩ : syracuseStep 1350971 = 2026457) B2026457
theorem B400699 : Blo 397767 400699 := bstep (se 1 (by rfl) ⟨300524, by rfl⟩ : syracuseStep 400699 = 601049) B601049
theorem B597383 : Blo 397767 597383 := bstep (se 1 (by rfl) ⟨448037, by rfl⟩ : syracuseStep 597383 = 896075) B896075
theorem B6495623 : Blo 397767 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B400775 : Blo 397767 400775 := bstep (se 1 (by rfl) ⟨300581, by rfl⟩ : syracuseStep 400775 = 601163) B601163
theorem B400783 : Blo 397767 400783 := bstep (se 1 (by rfl) ⟨300587, by rfl⟩ : syracuseStep 400783 = 601175) B601175
theorem B597419 : Blo 397767 597419 := bstep (se 1 (by rfl) ⟨448064, by rfl⟩ : syracuseStep 597419 = 896129) B896129
theorem B400827 : Blo 397767 400827 := bstep (se 1 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 400827 = 601241) B601241
theorem B597449 : Blo 397767 597449 := bstep (se 2 (by rfl) ⟨224043, by rfl⟩ : syracuseStep 597449 = 448087) B448087
theorem B400903 : Blo 397767 400903 := bstep (se 1 (by rfl) ⟨300677, by rfl⟩ : syracuseStep 400903 = 601355) B601355
theorem B400911 : Blo 397767 400911 := bstep (se 1 (by rfl) ⟨300683, by rfl⟩ : syracuseStep 400911 = 601367) B601367
theorem B597563 : Blo 397767 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B400955 : Blo 397767 400955 := bstep (se 1 (by rfl) ⟨300716, by rfl⟩ : syracuseStep 400955 = 601433) B601433
theorem B597623 : Blo 397767 597623 := bstep (se 1 (by rfl) ⟨448217, by rfl⟩ : syracuseStep 597623 = 896435) B896435
theorem B1285751 : Blo 397767 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B401031 : Blo 397767 401031 := bstep (se 1 (by rfl) ⟨300773, by rfl⟩ : syracuseStep 401031 = 601547) B601547
theorem B401039 : Blo 397767 401039 := bstep (se 1 (by rfl) ⟨300779, by rfl⟩ : syracuseStep 401039 = 601559) B601559
theorem B597647 : Blo 397767 597647 := bstep (se 1 (by rfl) ⟨448235, by rfl⟩ : syracuseStep 597647 = 896471) B896471
theorem B597689 : Blo 397767 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B401083 : Blo 397767 401083 := bstep (se 1 (by rfl) ⟨300812, by rfl⟩ : syracuseStep 401083 = 601625) B601625
theorem B597767 : Blo 397767 597767 := bstep (se 1 (by rfl) ⟨448325, by rfl⟩ : syracuseStep 597767 = 896651) B896651
theorem B401159 : Blo 397767 401159 := bstep (se 1 (by rfl) ⟨300869, by rfl⟩ : syracuseStep 401159 = 601739) B601739
theorem B401167 : Blo 397767 401167 := bstep (se 1 (by rfl) ⟨300875, by rfl⟩ : syracuseStep 401167 = 601751) B601751
theorem B1351457 : Blo 397767 1351457 := bstep (se 2 (by rfl) ⟨506796, by rfl⟩ : syracuseStep 1351457 = 1013593) B1013593
theorem B597803 : Blo 397767 597803 := bstep (se 1 (by rfl) ⟨448352, by rfl⟩ : syracuseStep 597803 = 896705) B896705
theorem B401211 : Blo 397767 401211 := bstep (se 1 (by rfl) ⟨300908, by rfl⟩ : syracuseStep 401211 = 601817) B601817
theorem B597833 : Blo 397767 597833 := bstep (se 2 (by rfl) ⟨224187, by rfl⟩ : syracuseStep 597833 = 448375) B448375
theorem B401287 : Blo 397767 401287 := bstep (se 1 (by rfl) ⟨300965, by rfl⟩ : syracuseStep 401287 = 601931) B601931
theorem B401295 : Blo 397767 401295 := bstep (se 1 (by rfl) ⟨300971, by rfl⟩ : syracuseStep 401295 = 601943) B601943
theorem B597947 : Blo 397767 597947 := bstep (se 1 (by rfl) ⟨448460, by rfl⟩ : syracuseStep 597947 = 896921) B896921
theorem B401339 : Blo 397767 401339 := bstep (se 1 (by rfl) ⟨301004, by rfl⟩ : syracuseStep 401339 = 602009) B602009
theorem B598007 : Blo 397767 598007 := bstep (se 1 (by rfl) ⟨448505, by rfl⟩ : syracuseStep 598007 = 897011) B897011
theorem B1220609 : Blo 397767 1220609 := bstep (se 2 (by rfl) ⟨457728, by rfl⟩ : syracuseStep 1220609 = 915457) B915457
theorem B401415 : Blo 397767 401415 := bstep (se 1 (by rfl) ⟨301061, by rfl⟩ : syracuseStep 401415 = 602123) B602123
theorem B598031 : Blo 397767 598031 := bstep (se 1 (by rfl) ⟨448523, by rfl⟩ : syracuseStep 598031 = 897047) B897047
theorem B401423 : Blo 397767 401423 := bstep (se 1 (by rfl) ⟨301067, by rfl⟩ : syracuseStep 401423 = 602135) B602135
theorem B598073 : Blo 397767 598073 := bstep (se 2 (by rfl) ⟨224277, by rfl⟩ : syracuseStep 598073 = 448555) B448555
theorem B401467 : Blo 397767 401467 := bstep (se 1 (by rfl) ⟨301100, by rfl⟩ : syracuseStep 401467 = 602201) B602201
theorem B598151 : Blo 397767 598151 := bstep (se 1 (by rfl) ⟨448613, by rfl⟩ : syracuseStep 598151 = 897227) B897227
theorem B401543 : Blo 397767 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B401551 : Blo 397767 401551 := bstep (se 1 (by rfl) ⟨301163, by rfl⟩ : syracuseStep 401551 = 602327) B602327
theorem B598187 : Blo 397767 598187 := bstep (se 1 (by rfl) ⟨448640, by rfl⟩ : syracuseStep 598187 = 897281) B897281
theorem B762041 : Blo 397767 762041 := bstep (se 2 (by rfl) ⟨285765, by rfl⟩ : syracuseStep 762041 = 571531) B571531
theorem B401595 : Blo 397767 401595 := bstep (se 1 (by rfl) ⟨301196, by rfl⟩ : syracuseStep 401595 = 602393) B602393
theorem B598217 : Blo 397767 598217 := bstep (se 2 (by rfl) ⟨224331, by rfl⟩ : syracuseStep 598217 = 448663) B448663
theorem B401671 : Blo 397767 401671 := bstep (se 1 (by rfl) ⟨301253, by rfl⟩ : syracuseStep 401671 = 602507) B602507
theorem B401679 : Blo 397767 401679 := bstep (se 1 (by rfl) ⟨301259, by rfl⟩ : syracuseStep 401679 = 602519) B602519
theorem B598331 : Blo 397767 598331 := bstep (se 1 (by rfl) ⟨448748, by rfl⟩ : syracuseStep 598331 = 897497) B897497
theorem B401723 : Blo 397767 401723 := bstep (se 1 (by rfl) ⟨301292, by rfl⟩ : syracuseStep 401723 = 602585) B602585
theorem B1352051 : Blo 397767 1352051 := bstep (se 1 (by rfl) ⟨1014038, by rfl⟩ : syracuseStep 1352051 = 2028077) B2028077
theorem B598391 : Blo 397767 598391 := bstep (se 1 (by rfl) ⟨448793, by rfl⟩ : syracuseStep 598391 = 897587) B897587
theorem B598415 : Blo 397767 598415 := bstep (se 1 (by rfl) ⟨448811, by rfl⟩ : syracuseStep 598415 = 897623) B897623
theorem B598457 : Blo 397767 598457 := bstep (se 2 (by rfl) ⟨224421, by rfl⟩ : syracuseStep 598457 = 448843) B448843
theorem B598535 : Blo 397767 598535 := bstep (se 1 (by rfl) ⟨448901, by rfl⟩ : syracuseStep 598535 = 897803) B897803
theorem B598571 : Blo 397767 598571 := bstep (se 1 (by rfl) ⟨448928, by rfl⟩ : syracuseStep 598571 = 897857) B897857
theorem B598601 : Blo 397767 598601 := bstep (se 2 (by rfl) ⟨224475, by rfl⟩ : syracuseStep 598601 = 448951) B448951
theorem B598715 : Blo 397767 598715 := bstep (se 1 (by rfl) ⟨449036, by rfl⟩ : syracuseStep 598715 = 898073) B898073
theorem B598775 : Blo 397767 598775 := bstep (se 1 (by rfl) ⟨449081, by rfl⟩ : syracuseStep 598775 = 898163) B898163
theorem B598799 : Blo 397767 598799 := bstep (se 1 (by rfl) ⟨449099, by rfl⟩ : syracuseStep 598799 = 898199) B898199
theorem B598841 : Blo 397767 598841 := bstep (se 2 (by rfl) ⟨224565, by rfl⟩ : syracuseStep 598841 = 449131) B449131
theorem B598919 : Blo 397767 598919 := bstep (se 1 (by rfl) ⟨449189, by rfl⟩ : syracuseStep 598919 = 898379) B898379
theorem B1516441 : Blo 397767 1516441 := bstep (se 2 (by rfl) ⟨568665, by rfl⟩ : syracuseStep 1516441 = 1137331) B1137331
theorem B598955 : Blo 397767 598955 := bstep (se 1 (by rfl) ⟨449216, by rfl⟩ : syracuseStep 598955 = 898433) B898433
theorem B598985 : Blo 397767 598985 := bstep (se 2 (by rfl) ⟨224619, by rfl⟩ : syracuseStep 598985 = 449239) B449239
theorem B599099 : Blo 397767 599099 := bstep (se 1 (by rfl) ⟨449324, by rfl⟩ : syracuseStep 599099 = 898649) B898649
theorem B1025083 : Blo 397767 1025083 := bstep (se 1 (by rfl) ⟨768812, by rfl⟩ : syracuseStep 1025083 = 1537625) B1537625
theorem B599159 : Blo 397767 599159 := bstep (se 1 (by rfl) ⟨449369, by rfl⟩ : syracuseStep 599159 = 898739) B898739
theorem B599183 : Blo 397767 599183 := bstep (se 1 (by rfl) ⟨449387, by rfl⟩ : syracuseStep 599183 = 898775) B898775
theorem B599225 : Blo 397767 599225 := bstep (se 2 (by rfl) ⟨224709, by rfl⟩ : syracuseStep 599225 = 449419) B449419
theorem B1516745 : Blo 397767 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B599303 : Blo 397767 599303 := bstep (se 1 (by rfl) ⟨449477, by rfl⟩ : syracuseStep 599303 = 898955) B898955
theorem B599339 : Blo 397767 599339 := bstep (se 1 (by rfl) ⟨449504, by rfl⟩ : syracuseStep 599339 = 899009) B899009
theorem B599369 : Blo 397767 599369 := bstep (se 2 (by rfl) ⟨224763, by rfl⟩ : syracuseStep 599369 = 449527) B449527
theorem B599483 : Blo 397767 599483 := bstep (se 1 (by rfl) ⟨449612, by rfl⟩ : syracuseStep 599483 = 899225) B899225
theorem B599543 : Blo 397767 599543 := bstep (se 1 (by rfl) ⟨449657, by rfl⟩ : syracuseStep 599543 = 899315) B899315
theorem B599567 : Blo 397767 599567 := bstep (se 1 (by rfl) ⟨449675, by rfl⟩ : syracuseStep 599567 = 899351) B899351
theorem B599609 : Blo 397767 599609 := bstep (se 2 (by rfl) ⟨224853, by rfl⟩ : syracuseStep 599609 = 449707) B449707
theorem B566843 : Blo 397767 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B37561931 : Blo 397767 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B599687 : Blo 397767 599687 := bstep (se 1 (by rfl) ⟨449765, by rfl⟩ : syracuseStep 599687 = 899531) B899531
theorem B599723 : Blo 397767 599723 := bstep (se 1 (by rfl) ⟨449792, by rfl⟩ : syracuseStep 599723 = 899585) B899585
theorem B599753 : Blo 397767 599753 := bstep (se 2 (by rfl) ⟨224907, by rfl⟩ : syracuseStep 599753 = 449815) B449815
theorem B599867 : Blo 397767 599867 := bstep (se 1 (by rfl) ⟨449900, by rfl⟩ : syracuseStep 599867 = 899801) B899801
theorem B599927 : Blo 397767 599927 := bstep (se 1 (by rfl) ⟨449945, by rfl⟩ : syracuseStep 599927 = 899891) B899891
theorem B927607 : Blo 397767 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B599951 : Blo 397767 599951 := bstep (se 1 (by rfl) ⟨449963, by rfl⟩ : syracuseStep 599951 = 899927) B899927
theorem B599993 : Blo 397767 599993 := bstep (se 2 (by rfl) ⟨224997, by rfl⟩ : syracuseStep 599993 = 449995) B449995
theorem B4564997 : Blo 397767 4564997 := bstep (se 4 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 4564997 = 855937) B855937
theorem B600071 : Blo 397767 600071 := bstep (se 1 (by rfl) ⟨450053, by rfl⟩ : syracuseStep 600071 = 900107) B900107
theorem B600107 : Blo 397767 600107 := bstep (se 1 (by rfl) ⟨450080, by rfl⟩ : syracuseStep 600107 = 900161) B900161
theorem B600137 : Blo 397767 600137 := bstep (se 2 (by rfl) ⟨225051, by rfl⟩ : syracuseStep 600137 = 450103) B450103
theorem B1517687 : Blo 397767 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B567481 : Blo 397767 567481 := bstep (se 2 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 567481 = 425611) B425611
theorem B600251 : Blo 397767 600251 := bstep (se 1 (by rfl) ⟨450188, by rfl⟩ : syracuseStep 600251 = 900377) B900377
theorem B600311 : Blo 397767 600311 := bstep (se 1 (by rfl) ⟨450233, by rfl⟩ : syracuseStep 600311 = 900467) B900467
theorem B895247 : Blo 397767 895247 := bstep (se 1 (by rfl) ⟨671435, by rfl⟩ : syracuseStep 895247 = 1342871) B1342871
theorem B600335 : Blo 397767 600335 := bstep (se 1 (by rfl) ⟨450251, by rfl⟩ : syracuseStep 600335 = 900503) B900503
theorem B895265 : Blo 397767 895265 := bstep (se 2 (by rfl) ⟨335724, by rfl⟩ : syracuseStep 895265 = 671449) B671449
theorem B567595 : Blo 397767 567595 := bstep (se 1 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 567595 = 851393) B851393
theorem B600377 : Blo 397767 600377 := bstep (se 2 (by rfl) ⟨225141, by rfl⟩ : syracuseStep 600377 = 450283) B450283
theorem B600455 : Blo 397767 600455 := bstep (se 1 (by rfl) ⟨450341, by rfl⟩ : syracuseStep 600455 = 900683) B900683
theorem B600491 : Blo 397767 600491 := bstep (se 1 (by rfl) ⟨450368, by rfl⟩ : syracuseStep 600491 = 900737) B900737
theorem B600521 : Blo 397767 600521 := bstep (se 2 (by rfl) ⟨225195, by rfl⟩ : syracuseStep 600521 = 450391) B450391
theorem B15313373 : Blo 397767 15313373 := bstep (se 3 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 15313373 = 5742515) B5742515
theorem B567823 : Blo 397767 567823 := bstep (se 1 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 567823 = 851735) B851735
theorem B600635 : Blo 397767 600635 := bstep (se 1 (by rfl) ⟨450476, by rfl⟩ : syracuseStep 600635 = 900953) B900953
theorem B895607 : Blo 397767 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B600695 : Blo 397767 600695 := bstep (se 1 (by rfl) ⟨450521, by rfl⟩ : syracuseStep 600695 = 901043) B901043
theorem B600719 : Blo 397767 600719 := bstep (se 1 (by rfl) ⟨450539, by rfl⟩ : syracuseStep 600719 = 901079) B901079
theorem B600761 : Blo 397767 600761 := bstep (se 2 (by rfl) ⟨225285, by rfl⟩ : syracuseStep 600761 = 450571) B450571
theorem B600839 : Blo 397767 600839 := bstep (se 1 (by rfl) ⟨450629, by rfl⟩ : syracuseStep 600839 = 901259) B901259
theorem B2960165 : Blo 397767 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B895787 : Blo 397767 895787 := bstep (se 1 (by rfl) ⟨671840, by rfl⟩ : syracuseStep 895787 = 1343681) B1343681
theorem B600875 : Blo 397767 600875 := bstep (se 1 (by rfl) ⟨450656, by rfl⟩ : syracuseStep 600875 = 901313) B901313
theorem B1715003 : Blo 397767 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B600905 : Blo 397767 600905 := bstep (se 2 (by rfl) ⟨225339, by rfl⟩ : syracuseStep 600905 = 450679) B450679
theorem B9677657 : Blo 397767 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B1354643 : Blo 397767 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B601019 : Blo 397767 601019 := bstep (se 1 (by rfl) ⟨450764, by rfl⟩ : syracuseStep 601019 = 901529) B901529
theorem B601079 : Blo 397767 601079 := bstep (se 1 (by rfl) ⟨450809, by rfl⟩ : syracuseStep 601079 = 901619) B901619
theorem B601103 : Blo 397767 601103 := bstep (se 1 (by rfl) ⟨450827, by rfl⟩ : syracuseStep 601103 = 901655) B901655
theorem B601145 : Blo 397767 601145 := bstep (se 2 (by rfl) ⟨225429, by rfl⟩ : syracuseStep 601145 = 450859) B450859
theorem B1518659 : Blo 397767 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B601223 : Blo 397767 601223 := bstep (se 1 (by rfl) ⟨450917, by rfl⟩ : syracuseStep 601223 = 901835) B901835
theorem B896147 : Blo 397767 896147 := bstep (se 1 (by rfl) ⟨672110, by rfl⟩ : syracuseStep 896147 = 1344221) B1344221
theorem B601259 : Blo 397767 601259 := bstep (se 1 (by rfl) ⟨450944, by rfl⟩ : syracuseStep 601259 = 901889) B901889
theorem B896201 : Blo 397767 896201 := bstep (se 2 (by rfl) ⟨336075, by rfl⟩ : syracuseStep 896201 = 672151) B672151
theorem B601289 : Blo 397767 601289 := bstep (se 2 (by rfl) ⟨225483, by rfl⟩ : syracuseStep 601289 = 450967) B450967
theorem B601403 : Blo 397767 601403 := bstep (se 1 (by rfl) ⟨451052, by rfl⟩ : syracuseStep 601403 = 902105) B902105
theorem B601463 : Blo 397767 601463 := bstep (se 1 (by rfl) ⟨451097, by rfl⟩ : syracuseStep 601463 = 902195) B902195
theorem B568711 : Blo 397767 568711 := bstep (se 1 (by rfl) ⟨426533, by rfl⟩ : syracuseStep 568711 = 853067) B853067
theorem B601487 : Blo 397767 601487 := bstep (se 1 (by rfl) ⟨451115, by rfl⟩ : syracuseStep 601487 = 902231) B902231
theorem B3026321 : Blo 397767 3026321 := bstep (se 2 (by rfl) ⟨1134870, by rfl⟩ : syracuseStep 3026321 = 2269741) B2269741
theorem B2272657 : Blo 397767 2272657 := bstep (se 2 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 2272657 = 1704493) B1704493
theorem B601529 : Blo 397767 601529 := bstep (se 2 (by rfl) ⟨225573, by rfl⟩ : syracuseStep 601529 = 451147) B451147
theorem B601607 : Blo 397767 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B2436637 : Blo 397767 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B601643 : Blo 397767 601643 := bstep (se 1 (by rfl) ⟨451232, by rfl⟩ : syracuseStep 601643 = 902465) B902465
theorem B601673 : Blo 397767 601673 := bstep (se 2 (by rfl) ⟨225627, by rfl⟩ : syracuseStep 601673 = 451255) B451255
theorem B1027703 : Blo 397767 1027703 := bstep (se 1 (by rfl) ⟨770777, by rfl⟩ : syracuseStep 1027703 = 1541555) B1541555
theorem B601787 : Blo 397767 601787 := bstep (se 1 (by rfl) ⟨451340, by rfl⟩ : syracuseStep 601787 = 902681) B902681
theorem B601847 : Blo 397767 601847 := bstep (se 1 (by rfl) ⟨451385, by rfl⟩ : syracuseStep 601847 = 902771) B902771
theorem B601871 : Blo 397767 601871 := bstep (se 1 (by rfl) ⟨451403, by rfl⟩ : syracuseStep 601871 = 902807) B902807
theorem B601913 : Blo 397767 601913 := bstep (se 2 (by rfl) ⟨225717, by rfl⟩ : syracuseStep 601913 = 451435) B451435
theorem B569207 : Blo 397767 569207 := bstep (se 1 (by rfl) ⟨426905, by rfl⟩ : syracuseStep 569207 = 853811) B853811
theorem B896903 : Blo 397767 896903 := bstep (se 1 (by rfl) ⟨672677, by rfl⟩ : syracuseStep 896903 = 1345355) B1345355
theorem B601991 : Blo 397767 601991 := bstep (se 1 (by rfl) ⟨451493, by rfl⟩ : syracuseStep 601991 = 902987) B902987
theorem B602027 : Blo 397767 602027 := bstep (se 1 (by rfl) ⟨451520, by rfl⟩ : syracuseStep 602027 = 903041) B903041
theorem B602057 : Blo 397767 602057 := bstep (se 2 (by rfl) ⟨225771, by rfl⟩ : syracuseStep 602057 = 451543) B451543
theorem B503815 : Blo 397767 503815 := bstep (se 1 (by rfl) ⟨377861, by rfl⟩ : syracuseStep 503815 = 755723) B755723
theorem B897083 : Blo 397767 897083 := bstep (se 1 (by rfl) ⟨672812, by rfl⟩ : syracuseStep 897083 = 1345625) B1345625
theorem B602171 : Blo 397767 602171 := bstep (se 1 (by rfl) ⟨451628, by rfl⟩ : syracuseStep 602171 = 903257) B903257
theorem B3321917 : Blo 397767 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B602231 : Blo 397767 602231 := bstep (se 1 (by rfl) ⟨451673, by rfl⟩ : syracuseStep 602231 = 903347) B903347
theorem B602255 : Blo 397767 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B897209 : Blo 397767 897209 := bstep (se 2 (by rfl) ⟨336453, by rfl⟩ : syracuseStep 897209 = 672907) B672907
theorem B602297 : Blo 397767 602297 := bstep (se 2 (by rfl) ⟨225861, by rfl⟩ : syracuseStep 602297 = 451723) B451723
theorem B602375 : Blo 397767 602375 := bstep (se 1 (by rfl) ⟨451781, by rfl⟩ : syracuseStep 602375 = 903563) B903563
theorem B602411 : Blo 397767 602411 := bstep (se 1 (by rfl) ⟨451808, by rfl⟩ : syracuseStep 602411 = 903617) B903617
theorem B602441 : Blo 397767 602441 := bstep (se 2 (by rfl) ⟨225915, by rfl⟩ : syracuseStep 602441 = 451831) B451831
theorem B504235 : Blo 397767 504235 := bstep (se 1 (by rfl) ⟨378176, by rfl⟩ : syracuseStep 504235 = 756353) B756353
theorem B602555 : Blo 397767 602555 := bstep (se 1 (by rfl) ⟨451916, by rfl⟩ : syracuseStep 602555 = 903833) B903833
theorem B1913291 : Blo 397767 1913291 := bstep (se 1 (by rfl) ⟨1434968, by rfl⟩ : syracuseStep 1913291 = 2869937) B2869937
theorem B602615 : Blo 397767 602615 := bstep (se 1 (by rfl) ⟨451961, by rfl⟩ : syracuseStep 602615 = 903923) B903923
theorem B897551 : Blo 397767 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B602639 : Blo 397767 602639 := bstep (se 1 (by rfl) ⟨451979, by rfl⟩ : syracuseStep 602639 = 903959) B903959
theorem B897569 : Blo 397767 897569 := bstep (se 2 (by rfl) ⟨336588, by rfl⟩ : syracuseStep 897569 = 673177) B673177
theorem B504463 : Blo 397767 504463 := bstep (se 1 (by rfl) ⟨378347, by rfl⟩ : syracuseStep 504463 = 756695) B756695
theorem B2437805 : Blo 397767 2437805 := bstep (se 3 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 2437805 = 914177) B914177
theorem B1520329 : Blo 397767 1520329 := bstep (se 2 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 1520329 = 1140247) B1140247
theorem B570169 : Blo 397767 570169 := bstep (se 2 (by rfl) ⟨213813, by rfl⟩ : syracuseStep 570169 = 427627) B427627
theorem B897911 : Blo 397767 897911 := bstep (se 1 (by rfl) ⟨673433, by rfl⟩ : syracuseStep 897911 = 1346867) B1346867
theorem B406415 : Blo 397767 406415 := bstep (se 1 (by rfl) ⟨304811, by rfl⟩ : syracuseStep 406415 = 609623) B609623
theorem B898091 : Blo 397767 898091 := bstep (se 1 (by rfl) ⟨673568, by rfl⟩ : syracuseStep 898091 = 1347137) B1347137
theorem B570511 : Blo 397767 570511 := bstep (se 1 (by rfl) ⟨427883, by rfl⟩ : syracuseStep 570511 = 855767) B855767
theorem B505207 : Blo 397767 505207 := bstep (se 1 (by rfl) ⟨378905, by rfl⟩ : syracuseStep 505207 = 757811) B757811
theorem B898451 : Blo 397767 898451 := bstep (se 1 (by rfl) ⟨673838, by rfl⟩ : syracuseStep 898451 = 1347677) B1347677
theorem B2569657 : Blo 397767 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B898505 : Blo 397767 898505 := bstep (se 2 (by rfl) ⟨336939, by rfl⟩ : syracuseStep 898505 = 673879) B673879
theorem B4535837 : Blo 397767 4535837 := bstep (se 3 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 4535837 = 1700939) B1700939
theorem B505531 : Blo 397767 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B2275073 : Blo 397767 2275073 := bstep (se 2 (by rfl) ⟨853152, by rfl⟩ : syracuseStep 2275073 = 1706305) B1706305
theorem B3028751 : Blo 397767 3028751 := bstep (se 1 (by rfl) ⟨2271563, by rfl⟩ : syracuseStep 3028751 = 4543127) B4543127
theorem B538427 : Blo 397767 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B1914941 : Blo 397767 1914941 := bstep (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) B718103
theorem B899207 : Blo 397767 899207 := bstep (se 1 (by rfl) ⟨674405, by rfl⟩ : syracuseStep 899207 = 1348811) B1348811
theorem B506027 : Blo 397767 506027 := bstep (se 1 (by rfl) ⟨379520, by rfl⟩ : syracuseStep 506027 = 759041) B759041
theorem B571639 : Blo 397767 571639 := bstep (se 1 (by rfl) ⟨428729, by rfl⟩ : syracuseStep 571639 = 857459) B857459
theorem B899387 : Blo 397767 899387 := bstep (se 1 (by rfl) ⟨674540, by rfl⟩ : syracuseStep 899387 = 1349081) B1349081
theorem B1915289 : Blo 397767 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B899513 : Blo 397767 899513 := bstep (se 2 (by rfl) ⟨337317, by rfl⟩ : syracuseStep 899513 = 674635) B674635
theorem B1817117 : Blo 397767 1817117 := bstep (se 3 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 1817117 = 681419) B681419
theorem B506503 : Blo 397767 506503 := bstep (se 1 (by rfl) ⟨379877, by rfl⟩ : syracuseStep 506503 = 759755) B759755
theorem B899855 : Blo 397767 899855 := bstep (se 1 (by rfl) ⟨674891, by rfl⟩ : syracuseStep 899855 = 1349783) B1349783
theorem B899873 : Blo 397767 899873 := bstep (se 2 (by rfl) ⟨337452, by rfl⟩ : syracuseStep 899873 = 674905) B674905
theorem B1522547 : Blo 397767 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B2440145 : Blo 397767 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B3652619 : Blo 397767 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B605243 : Blo 397767 605243 := bstep (se 1 (by rfl) ⟨453932, by rfl⟩ : syracuseStep 605243 = 907865) B907865
theorem B4602997 : Blo 397767 4602997 := bstep (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) B431531
theorem B900215 : Blo 397767 900215 := bstep (se 1 (by rfl) ⟨675161, by rfl⟩ : syracuseStep 900215 = 1350323) B1350323
theorem B506999 : Blo 397767 506999 := bstep (se 1 (by rfl) ⟨380249, by rfl⟩ : syracuseStep 506999 = 760499) B760499
theorem B2440385 : Blo 397767 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B507151 : Blo 397767 507151 := bstep (se 1 (by rfl) ⟨380363, by rfl⟩ : syracuseStep 507151 = 760727) B760727
theorem B900395 : Blo 397767 900395 := bstep (se 1 (by rfl) ⟨675296, by rfl⟩ : syracuseStep 900395 = 1350593) B1350593
theorem B3849565 : Blo 397767 3849565 := bstep (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) B1443587
theorem B638327 : Blo 397767 638327 := bstep (se 1 (by rfl) ⟨478745, by rfl⟩ : syracuseStep 638327 = 957491) B957491
theorem B540091 : Blo 397767 540091 := bstep (se 1 (by rfl) ⟨405068, by rfl⟩ : syracuseStep 540091 = 810137) B810137
theorem B507323 : Blo 397767 507323 := bstep (se 1 (by rfl) ⟨380492, by rfl⟩ : syracuseStep 507323 = 760985) B760985
theorem B900755 : Blo 397767 900755 := bstep (se 1 (by rfl) ⟨675566, by rfl⟩ : syracuseStep 900755 = 1351133) B1351133
theorem B900809 : Blo 397767 900809 := bstep (se 2 (by rfl) ⟨337803, by rfl⟩ : syracuseStep 900809 = 675607) B675607
theorem B671503 : Blo 397767 671503 := bstep (se 1 (by rfl) ⟨503627, by rfl⟩ : syracuseStep 671503 = 1007255) B1007255
theorem B2277305 : Blo 397767 2277305 := bstep (se 2 (by rfl) ⟨853989, by rfl⟩ : syracuseStep 2277305 = 1707979) B1707979
theorem B9257161 : Blo 397767 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B672043 : Blo 397767 672043 := bstep (se 1 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 672043 = 1008065) B1008065
theorem B2015603 : Blo 397767 2015603 := bstep (se 1 (by rfl) ⟨1511702, by rfl⟩ : syracuseStep 2015603 = 3023405) B3023405
theorem B901511 : Blo 397767 901511 := bstep (se 1 (by rfl) ⟨676133, by rfl⟩ : syracuseStep 901511 = 1352267) B1352267
theorem B508295 : Blo 397767 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B672185 : Blo 397767 672185 := bstep (se 2 (by rfl) ⟨252069, by rfl⟩ : syracuseStep 672185 = 504139) B504139
theorem B901691 : Blo 397767 901691 := bstep (se 1 (by rfl) ⟨676268, by rfl⟩ : syracuseStep 901691 = 1352537) B1352537
theorem B901817 : Blo 397767 901817 := bstep (se 2 (by rfl) ⟨338181, by rfl⟩ : syracuseStep 901817 = 676363) B676363
theorem B6505231 : Blo 397767 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B607019 : Blo 397767 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B2016089 : Blo 397767 2016089 := bstep (se 2 (by rfl) ⟨756033, by rfl⟩ : syracuseStep 2016089 = 1512067) B1512067
theorem B770963 : Blo 397767 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B2933657 : Blo 397767 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B1524689 : Blo 397767 1524689 := bstep (se 2 (by rfl) ⟨571758, by rfl⟩ : syracuseStep 1524689 = 1143517) B1143517
theorem B902159 : Blo 397767 902159 := bstep (se 1 (by rfl) ⟨676619, by rfl⟩ : syracuseStep 902159 = 1353239) B1353239
theorem B902177 : Blo 397767 902177 := bstep (se 2 (by rfl) ⟨338316, by rfl⟩ : syracuseStep 902177 = 676633) B676633
theorem B672887 : Blo 397767 672887 := bstep (se 1 (by rfl) ⟨504665, by rfl⟩ : syracuseStep 672887 = 1009331) B1009331
theorem B1525007 : Blo 397767 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B2934049 : Blo 397767 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B902519 : Blo 397767 902519 := bstep (se 1 (by rfl) ⟨676889, by rfl⟩ : syracuseStep 902519 = 1353779) B1353779
theorem B902699 : Blo 397767 902699 := bstep (se 1 (by rfl) ⟨677024, by rfl⟩ : syracuseStep 902699 = 1354049) B1354049
theorem B673339 : Blo 397767 673339 := bstep (se 1 (by rfl) ⟨505004, by rfl⟩ : syracuseStep 673339 = 1010009) B1010009
theorem B2574017 : Blo 397767 2574017 := bstep (se 2 (by rfl) ⟨965256, by rfl⟩ : syracuseStep 2574017 = 1930513) B1930513
theorem B673481 : Blo 397767 673481 := bstep (se 2 (by rfl) ⟨252555, by rfl⟩ : syracuseStep 673481 = 505111) B505111
theorem B4540211 : Blo 397767 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B903059 : Blo 397767 903059 := bstep (se 1 (by rfl) ⟨677294, by rfl⟩ : syracuseStep 903059 = 1354589) B1354589
theorem B903113 : Blo 397767 903113 := bstep (se 2 (by rfl) ⟨338667, by rfl⟩ : syracuseStep 903113 = 677335) B677335
theorem B2279447 : Blo 397767 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B1820987 : Blo 397767 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B674183 : Blo 397767 674183 := bstep (se 1 (by rfl) ⟨505637, by rfl⟩ : syracuseStep 674183 = 1011275) B1011275
theorem B2279947 : Blo 397767 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B3426893 : Blo 397767 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B9226871 : Blo 397767 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B903815 : Blo 397767 903815 := bstep (se 1 (by rfl) ⟨677861, by rfl⟩ : syracuseStep 903815 = 1355723) B1355723
theorem B4311731 : Blo 397767 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B477967 : Blo 397767 477967 := bstep (se 1 (by rfl) ⟨358475, by rfl⟩ : syracuseStep 477967 = 716951) B716951
theorem B1133345 : Blo 397767 1133345 := bstep (se 2 (by rfl) ⟨425004, by rfl⟩ : syracuseStep 1133345 = 850009) B850009
theorem B1133459 : Blo 397767 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B2018195 : Blo 397767 2018195 := bstep (se 1 (by rfl) ⟨1513646, by rfl⟩ : syracuseStep 2018195 = 3027293) B3027293
theorem B674831 : Blo 397767 674831 := bstep (se 1 (by rfl) ⟨506123, by rfl⟩ : syracuseStep 674831 = 1012247) B1012247
theorem B642107 : Blo 397767 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B1920307 : Blo 397767 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B675371 : Blo 397767 675371 := bstep (se 1 (by rfl) ⟨506528, by rfl⟩ : syracuseStep 675371 = 1013057) B1013057
theorem B1920631 : Blo 397767 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B1134233 : Blo 397767 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B1822409 : Blo 397767 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B675769 : Blo 397767 675769 := bstep (se 2 (by rfl) ⟨253413, by rfl⟩ : syracuseStep 675769 = 506827) B506827
theorem B512399 : Blo 397767 512399 := bstep (se 1 (by rfl) ⟨384299, by rfl⟩ : syracuseStep 512399 = 768599) B768599
theorem B2281931 : Blo 397767 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B676471 : Blo 397767 676471 := bstep (se 1 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 676471 = 1014707) B1014707
theorem B480043 : Blo 397767 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B676667 : Blo 397767 676667 := bstep (se 1 (by rfl) ⟨507500, by rfl⟩ : syracuseStep 676667 = 1015001) B1015001
theorem B512911 : Blo 397767 512911 := bstep (se 1 (by rfl) ⟨384683, by rfl⟩ : syracuseStep 512911 = 769367) B769367
theorem B1299347 : Blo 397767 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B447547 : Blo 397767 447547 := bstep (se 1 (by rfl) ⟨335660, by rfl⟩ : syracuseStep 447547 = 671321) B671321
theorem B1758275 : Blo 397767 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B677065 : Blo 397767 677065 := bstep (se 2 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 677065 = 507799) B507799
theorem B1135873 : Blo 397767 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B1922305 : Blo 397767 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B1922363 : Blo 397767 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B448015 : Blo 397767 448015 := bstep (se 1 (by rfl) ⟨336011, by rfl⟩ : syracuseStep 448015 = 672023) B672023
theorem B1070891 : Blo 397767 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B1136443 : Blo 397767 1136443 := bstep (se 1 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 1136443 = 1704665) B1704665
theorem B677767 : Blo 397767 677767 := bstep (se 1 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 677767 = 1016651) B1016651
theorem B2021273 : Blo 397767 2021273 := bstep (se 2 (by rfl) ⟨757977, by rfl⟩ : syracuseStep 2021273 = 1515955) B1515955
theorem B448519 : Blo 397767 448519 := bstep (se 1 (by rfl) ⟨336389, by rfl⟩ : syracuseStep 448519 = 672779) B672779
theorem B809003 : Blo 397767 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B6641837 : Blo 397767 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B448699 : Blo 397767 448699 := bstep (se 1 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 448699 = 673049) B673049
theorem B3037499 : Blo 397767 3037499 := bstep (se 1 (by rfl) ⟨2278124, by rfl⟩ : syracuseStep 3037499 = 4556249) B4556249
theorem B6510941 : Blo 397767 6510941 := bstep (se 3 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 6510941 = 2441603) B2441603
theorem B1825291 : Blo 397767 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B449167 : Blo 397767 449167 := bstep (se 1 (by rfl) ⟨336875, by rfl⟩ : syracuseStep 449167 = 673751) B673751
theorem B2284321 : Blo 397767 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B613307 : Blo 397767 613307 := bstep (se 1 (by rfl) ⟨459980, by rfl⟩ : syracuseStep 613307 = 919961) B919961
theorem B482311 : Blo 397767 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B449671 : Blo 397767 449671 := bstep (se 1 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 449671 = 674507) B674507
theorem B449851 : Blo 397767 449851 := bstep (se 1 (by rfl) ⟨337388, by rfl⟩ : syracuseStep 449851 = 674777) B674777
theorem B450319 : Blo 397767 450319 := bstep (se 1 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 450319 = 675479) B675479
theorem B3399691 : Blo 397767 3399691 := bstep (se 1 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 3399691 = 5099537) B5099537
theorem B2285597 : Blo 397767 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B647227 : Blo 397767 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B1138835 : Blo 397767 1138835 := bstep (se 1 (by rfl) ⟨854126, by rfl⟩ : syracuseStep 1138835 = 1708253) B1708253
theorem B1007873 : Blo 397767 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B450823 : Blo 397767 450823 := bstep (se 1 (by rfl) ⟨338117, by rfl⟩ : syracuseStep 450823 = 676235) B676235
theorem B2023865 : Blo 397767 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B451003 : Blo 397767 451003 := bstep (se 1 (by rfl) ⟨338252, by rfl⟩ : syracuseStep 451003 = 676505) B676505
theorem B3858947 : Blo 397767 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B1008247 : Blo 397767 1008247 := bstep (se 1 (by rfl) ⟨756185, by rfl⟩ : syracuseStep 1008247 = 1512371) B1512371
theorem B1368695 : Blo 397767 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B13787941 : Blo 397767 13787941 := bstep (se 4 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 13787941 = 2585239) B2585239
theorem B451471 : Blo 397767 451471 := bstep (se 1 (by rfl) ⟨338603, by rfl⟩ : syracuseStep 451471 = 677207) B677207
theorem B1139609 : Blo 397767 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B680975 : Blo 397767 680975 := bstep (se 1 (by rfl) ⟨510731, by rfl⟩ : syracuseStep 680975 = 1021463) B1021463
theorem B1008683 : Blo 397767 1008683 := bstep (se 1 (by rfl) ⟨756512, by rfl⟩ : syracuseStep 1008683 = 1513025) B1513025
theorem B1303595 : Blo 397767 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B2188595 : Blo 397767 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B23029109 : Blo 397767 23029109 := bstep (se 5 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 23029109 = 2158979) B2158979
theorem B451975 : Blo 397767 451975 := bstep (se 1 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 451975 = 677963) B677963
theorem B6514253 : Blo 397767 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B2025161 : Blo 397767 2025161 := bstep (se 2 (by rfl) ⟨759435, by rfl⟩ : syracuseStep 2025161 = 1518871) B1518871
theorem B1697537 : Blo 397767 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B1009523 : Blo 397767 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B1009543 : Blo 397767 1009543 := bstep (se 1 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 1009543 = 1514315) B1514315
theorem B2156473 : Blo 397767 2156473 := bstep (se 2 (by rfl) ⟨808677, by rfl⟩ : syracuseStep 2156473 = 1617355) B1617355
theorem B3401675 : Blo 397767 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B1009817 : Blo 397767 1009817 := bstep (se 2 (by rfl) ⟨378681, by rfl⟩ : syracuseStep 1009817 = 757363) B757363
theorem B1435963 : Blo 397767 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B1009979 : Blo 397767 1009979 := bstep (se 1 (by rfl) ⟨757484, by rfl⟩ : syracuseStep 1009979 = 1514969) B1514969
theorem B3860945 : Blo 397767 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B1010191 : Blo 397767 1010191 := bstep (se 1 (by rfl) ⟨757643, by rfl⟩ : syracuseStep 1010191 = 1515287) B1515287
theorem B1075771 : Blo 397767 1075771 := bstep (se 1 (by rfl) ⟨806828, by rfl⟩ : syracuseStep 1075771 = 1613657) B1613657
theorem B2288195 : Blo 397767 2288195 := bstep (se 1 (by rfl) ⟨1716146, by rfl⟩ : syracuseStep 2288195 = 3432293) B3432293
theorem B1010465 : Blo 397767 1010465 := bstep (se 2 (by rfl) ⟨378924, by rfl⟩ : syracuseStep 1010465 = 757849) B757849
theorem B1141705 : Blo 397767 1141705 := bstep (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) B856279
theorem B3894317 : Blo 397767 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B1142059 : Blo 397767 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B1535441 : Blo 397767 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B3042845 : Blo 397767 3042845 := bstep (se 3 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 3042845 = 1141067) B1141067
theorem B1142333 : Blo 397767 1142333 := bstep (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) B428375
theorem B1011467 : Blo 397767 1011467 := bstep (se 1 (by rfl) ⟨758600, by rfl⟩ : syracuseStep 1011467 = 1517201) B1517201
theorem B2551819 : Blo 397767 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B3404065 : Blo 397767 3404065 := bstep (se 2 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 3404065 = 2553049) B2553049
theorem B1012115 : Blo 397767 1012115 := bstep (se 1 (by rfl) ⟨759086, by rfl⟩ : syracuseStep 1012115 = 1518173) B1518173
theorem B1077761 : Blo 397767 1077761 := bstep (se 2 (by rfl) ⟨404160, by rfl⟩ : syracuseStep 1077761 = 808321) B808321
theorem B455311 : Blo 397767 455311 := bstep (se 1 (by rfl) ⟨341483, by rfl⟩ : syracuseStep 455311 = 682967) B682967
theorem B1012409 : Blo 397767 1012409 := bstep (se 2 (by rfl) ⟨379653, by rfl⟩ : syracuseStep 1012409 = 759307) B759307
theorem B914105 : Blo 397767 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B1274771 : Blo 397767 1274771 := bstep (se 1 (by rfl) ⟨956078, by rfl⟩ : syracuseStep 1274771 = 1912157) B1912157
theorem B914323 : Blo 397767 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1930301 : Blo 397767 1930301 := bstep (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) B723863
theorem B1209659 : Blo 397767 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B1013107 : Blo 397767 1013107 := bstep (se 1 (by rfl) ⟨759830, by rfl⟩ : syracuseStep 1013107 = 1519661) B1519661
theorem B1013249 : Blo 397767 1013249 := bstep (se 2 (by rfl) ⟨379968, by rfl⟩ : syracuseStep 1013249 = 759937) B759937
theorem B19363697 : Blo 397767 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B1013705 : Blo 397767 1013705 := bstep (se 2 (by rfl) ⟨380139, by rfl⟩ : syracuseStep 1013705 = 760279) B760279
theorem B1701931 : Blo 397767 1701931 := bstep (se 1 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 1701931 = 2552897) B2552897
theorem B1964119 : Blo 397767 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B1014059 : Blo 397767 1014059 := bstep (se 1 (by rfl) ⟨760544, by rfl⟩ : syracuseStep 1014059 = 1521089) B1521089
theorem B1440185 : Blo 397767 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1079837 : Blo 397767 1079837 := bstep (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) B404939
theorem B719545 : Blo 397767 719545 := bstep (se 2 (by rfl) ⟨269829, by rfl⟩ : syracuseStep 719545 = 539659) B539659
theorem B1342493 : Blo 397767 1342493 := bstep (se 3 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 1342493 = 503435) B503435
theorem B1015051 : Blo 397767 1015051 := bstep (se 1 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 1015051 = 1522577) B1522577
theorem B2030993 : Blo 397767 2030993 := bstep (se 2 (by rfl) ⟨761622, by rfl⟩ : syracuseStep 2030993 = 1523245) B1523245
theorem B1015193 : Blo 397767 1015193 := bstep (se 2 (by rfl) ⟨380697, by rfl⟩ : syracuseStep 1015193 = 761395) B761395
theorem B1015355 : Blo 397767 1015355 := bstep (se 1 (by rfl) ⟨761516, by rfl⟩ : syracuseStep 1015355 = 1523033) B1523033
theorem B13860659 : Blo 397767 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B3047219 : Blo 397767 3047219 := bstep (se 1 (by rfl) ⟨2285414, by rfl⟩ : syracuseStep 3047219 = 4570829) B4570829
theorem B1015699 : Blo 397767 1015699 := bstep (se 1 (by rfl) ⟨761774, by rfl⟩ : syracuseStep 1015699 = 1523549) B1523549
theorem B851897 : Blo 397767 851897 := bstep (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) B638923
theorem B38961269 : Blo 397767 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B1343735 : Blo 397767 1343735 := bstep (se 1 (by rfl) ⟨1007801, by rfl⟩ : syracuseStep 1343735 = 2015603) B2015603
theorem B1344059 : Blo 397767 1344059 := bstep (se 1 (by rfl) ⟨1008044, by rfl⟩ : syracuseStep 1344059 = 2016089) B2016089
theorem B1016459 : Blo 397767 1016459 := bstep (se 1 (by rfl) ⟨762344, by rfl⟩ : syracuseStep 1016459 = 1524689) B1524689
theorem B1344329 : Blo 397767 1344329 := bstep (se 2 (by rfl) ⟨504123, by rfl⟩ : syracuseStep 1344329 = 1008247) B1008247
theorem B3408713 : Blo 397767 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B5768009 : Blo 397767 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B1016671 : Blo 397767 1016671 := bstep (se 1 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 1016671 = 1525007) B1525007
theorem B852923 : Blo 397767 852923 := bstep (se 1 (by rfl) ⟨639692, by rfl⟩ : syracuseStep 852923 = 1279385) B1279385
theorem B18383921 : Blo 397767 18383921 := bstep (se 2 (by rfl) ⟨6893970, by rfl⟩ : syracuseStep 18383921 = 13787941) B13787941
theorem B1442897 : Blo 397767 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B8750429 : Blo 397767 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B39060913 : Blo 397767 39060913 := bstep (se 2 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 39060913 = 29295685) B29295685
theorem B1213991 : Blo 397767 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B755563 : Blo 397767 755563 := bstep (se 1 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 755563 = 1133345) B1133345
theorem B1443703 : Blo 397767 1443703 := bstep (se 1 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 1443703 = 2165555) B2165555
theorem B755639 : Blo 397767 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B1345463 : Blo 397767 1345463 := bstep (se 1 (by rfl) ⟨1009097, by rfl⟩ : syracuseStep 1345463 = 2018195) B2018195
theorem B591835 : Blo 397767 591835 := bstep (se 1 (by rfl) ⟨443876, by rfl⟩ : syracuseStep 591835 = 887753) B887753
theorem B854263 : Blo 397767 854263 := bstep (se 1 (by rfl) ⟨640697, by rfl⟩ : syracuseStep 854263 = 1281395) B1281395
theorem B1083773 : Blo 397767 1083773 := bstep (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) B406415
theorem B756155 : Blo 397767 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B1214939 : Blo 397767 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B1346057 : Blo 397767 1346057 := bstep (se 2 (by rfl) ⟨504771, by rfl⟩ : syracuseStep 1346057 = 1009543) B1009543
theorem B1444499 : Blo 397767 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B756641 : Blo 397767 756641 := bstep (se 2 (by rfl) ⟨283740, by rfl⟩ : syracuseStep 756641 = 567481) B567481
theorem B756793 : Blo 397767 756793 := bstep (se 2 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 756793 = 567595) B567595
theorem B1510595 : Blo 397767 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B757097 : Blo 397767 757097 := bstep (se 2 (by rfl) ⟨283911, by rfl⟩ : syracuseStep 757097 = 567823) B567823
theorem B1346921 : Blo 397767 1346921 := bstep (se 2 (by rfl) ⟨505095, by rfl⟩ : syracuseStep 1346921 = 1010191) B1010191
theorem B1281575 : Blo 397767 1281575 := bstep (se 1 (by rfl) ⟨961181, by rfl⟩ : syracuseStep 1281575 = 1922363) B1922363
theorem B1347515 : Blo 397767 1347515 := bstep (se 1 (by rfl) ⟨1010636, by rfl⟩ : syracuseStep 1347515 = 2021273) B2021273
theorem B4427891 : Blo 397767 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B1511581 : Blo 397767 1511581 := bstep (se 3 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 1511581 = 566843) B566843
theorem B4559165 : Blo 397767 4559165 := bstep (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) B1709687
theorem B2560409 : Blo 397767 2560409 := bstep (se 2 (by rfl) ⟨960153, by rfl⟩ : syracuseStep 2560409 = 1920307) B1920307
theorem B397767 : Blo 397767 397767 := bstep (se 1 (by rfl) ⟨298325, by rfl⟩ : syracuseStep 397767 = 596651) B596651
theorem B397787 : Blo 397767 397787 := bstep (se 1 (by rfl) ⟨298340, by rfl⟩ : syracuseStep 397787 = 596681) B596681
theorem B397863 : Blo 397767 397863 := bstep (se 1 (by rfl) ⟨298397, by rfl⟩ : syracuseStep 397863 = 596795) B596795
theorem B397903 : Blo 397767 397903 := bstep (se 1 (by rfl) ⟨298427, by rfl⟩ : syracuseStep 397903 = 596855) B596855
theorem B397919 : Blo 397767 397919 := bstep (se 1 (by rfl) ⟨298439, by rfl⟩ : syracuseStep 397919 = 596879) B596879
theorem B397947 : Blo 397767 397947 := bstep (se 1 (by rfl) ⟨298460, by rfl⟩ : syracuseStep 397947 = 596921) B596921
theorem B4526765 : Blo 397767 4526765 := bstep (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) B1697537
theorem B397999 : Blo 397767 397999 := bstep (se 1 (by rfl) ⟨298499, by rfl⟩ : syracuseStep 397999 = 596999) B596999
theorem B398023 : Blo 397767 398023 := bstep (se 1 (by rfl) ⟨298517, by rfl⟩ : syracuseStep 398023 = 597035) B597035
theorem B3248849 : Blo 397767 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B398043 : Blo 397767 398043 := bstep (se 1 (by rfl) ⟨298532, by rfl⟩ : syracuseStep 398043 = 597065) B597065
theorem B398119 : Blo 397767 398119 := bstep (se 1 (by rfl) ⟨298589, by rfl⟩ : syracuseStep 398119 = 597179) B597179
theorem B2560841 : Blo 397767 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B398159 : Blo 397767 398159 := bstep (se 1 (by rfl) ⟨298619, by rfl⟩ : syracuseStep 398159 = 597239) B597239
theorem B398175 : Blo 397767 398175 := bstep (se 1 (by rfl) ⟨298631, by rfl⟩ : syracuseStep 398175 = 597263) B597263
theorem B398203 : Blo 397767 398203 := bstep (se 1 (by rfl) ⟨298652, by rfl⟩ : syracuseStep 398203 = 597305) B597305
theorem B1446817 : Blo 397767 1446817 := bstep (se 2 (by rfl) ⟨542556, by rfl⟩ : syracuseStep 1446817 = 1085113) B1085113
theorem B398255 : Blo 397767 398255 := bstep (se 1 (by rfl) ⟨298691, by rfl⟩ : syracuseStep 398255 = 597383) B597383
theorem B4330415 : Blo 397767 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B398279 : Blo 397767 398279 := bstep (se 1 (by rfl) ⟨298709, by rfl⟩ : syracuseStep 398279 = 597419) B597419
theorem B398299 : Blo 397767 398299 := bstep (se 1 (by rfl) ⟨298724, by rfl⟩ : syracuseStep 398299 = 597449) B597449
theorem B2626561 : Blo 397767 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B398375 : Blo 397767 398375 := bstep (se 1 (by rfl) ⟨298781, by rfl⟩ : syracuseStep 398375 = 597563) B597563
theorem B398415 : Blo 397767 398415 := bstep (se 1 (by rfl) ⟨298811, by rfl⟩ : syracuseStep 398415 = 597623) B597623
theorem B398431 : Blo 397767 398431 := bstep (se 1 (by rfl) ⟨298823, by rfl⟩ : syracuseStep 398431 = 597647) B597647
theorem B398459 : Blo 397767 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B398511 : Blo 397767 398511 := bstep (se 1 (by rfl) ⟨298883, by rfl⟩ : syracuseStep 398511 = 597767) B597767
theorem B398535 : Blo 397767 398535 := bstep (se 1 (by rfl) ⟨298901, by rfl⟩ : syracuseStep 398535 = 597803) B597803
theorem B398555 : Blo 397767 398555 := bstep (se 1 (by rfl) ⟨298916, by rfl⟩ : syracuseStep 398555 = 597833) B597833
theorem B398631 : Blo 397767 398631 := bstep (se 1 (by rfl) ⟨298973, by rfl⟩ : syracuseStep 398631 = 597947) B597947
theorem B398671 : Blo 397767 398671 := bstep (se 1 (by rfl) ⟨299003, by rfl⟩ : syracuseStep 398671 = 598007) B598007
theorem B398687 : Blo 397767 398687 := bstep (se 1 (by rfl) ⟨299015, by rfl⟩ : syracuseStep 398687 = 598031) B598031
theorem B398715 : Blo 397767 398715 := bstep (se 1 (by rfl) ⟨299036, by rfl⟩ : syracuseStep 398715 = 598073) B598073
theorem B398767 : Blo 397767 398767 := bstep (se 1 (by rfl) ⟨299075, by rfl⟩ : syracuseStep 398767 = 598151) B598151
theorem B759223 : Blo 397767 759223 := bstep (se 1 (by rfl) ⟨569417, by rfl⟩ : syracuseStep 759223 = 1138835) B1138835
theorem B398791 : Blo 397767 398791 := bstep (se 1 (by rfl) ⟨299093, by rfl⟩ : syracuseStep 398791 = 598187) B598187
theorem B398811 : Blo 397767 398811 := bstep (se 1 (by rfl) ⟨299108, by rfl⟩ : syracuseStep 398811 = 598217) B598217
theorem B398887 : Blo 397767 398887 := bstep (se 1 (by rfl) ⟨299165, by rfl⟩ : syracuseStep 398887 = 598331) B598331
theorem B398927 : Blo 397767 398927 := bstep (se 1 (by rfl) ⟨299195, by rfl⟩ : syracuseStep 398927 = 598391) B598391
theorem B398943 : Blo 397767 398943 := bstep (se 1 (by rfl) ⟨299207, by rfl⟩ : syracuseStep 398943 = 598415) B598415
theorem B398971 : Blo 397767 398971 := bstep (se 1 (by rfl) ⟨299228, by rfl⟩ : syracuseStep 398971 = 598457) B598457
theorem B1349243 : Blo 397767 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B399023 : Blo 397767 399023 := bstep (se 1 (by rfl) ⟨299267, by rfl⟩ : syracuseStep 399023 = 598535) B598535
theorem B399047 : Blo 397767 399047 := bstep (se 1 (by rfl) ⟨299285, by rfl⟩ : syracuseStep 399047 = 598571) B598571
theorem B399067 : Blo 397767 399067 := bstep (se 1 (by rfl) ⟨299300, by rfl⟩ : syracuseStep 399067 = 598601) B598601
theorem B1349405 : Blo 397767 1349405 := bstep (se 3 (by rfl) ⟨253013, by rfl⟩ : syracuseStep 1349405 = 506027) B506027
theorem B399143 : Blo 397767 399143 := bstep (se 1 (by rfl) ⟨299357, by rfl⟩ : syracuseStep 399143 = 598715) B598715
theorem B399183 : Blo 397767 399183 := bstep (se 1 (by rfl) ⟨299387, by rfl⟩ : syracuseStep 399183 = 598775) B598775
theorem B399199 : Blo 397767 399199 := bstep (se 1 (by rfl) ⟨299399, by rfl⟩ : syracuseStep 399199 = 598799) B598799
theorem B399227 : Blo 397767 399227 := bstep (se 1 (by rfl) ⟨299420, by rfl⟩ : syracuseStep 399227 = 598841) B598841
theorem B399279 : Blo 397767 399279 := bstep (se 1 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 399279 = 598919) B598919
theorem B24549317 : Blo 397767 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B399303 : Blo 397767 399303 := bstep (se 1 (by rfl) ⟨299477, by rfl⟩ : syracuseStep 399303 = 598955) B598955
theorem B399323 : Blo 397767 399323 := bstep (se 1 (by rfl) ⟨299492, by rfl⟩ : syracuseStep 399323 = 598985) B598985
theorem B399399 : Blo 397767 399399 := bstep (se 1 (by rfl) ⟨299549, by rfl⟩ : syracuseStep 399399 = 599099) B599099
theorem B399439 : Blo 397767 399439 := bstep (se 1 (by rfl) ⟨299579, by rfl⟩ : syracuseStep 399439 = 599159) B599159
theorem B399455 : Blo 397767 399455 := bstep (se 1 (by rfl) ⟨299591, by rfl⟩ : syracuseStep 399455 = 599183) B599183
theorem B399483 : Blo 397767 399483 := bstep (se 1 (by rfl) ⟨299612, by rfl⟩ : syracuseStep 399483 = 599225) B599225
theorem B399535 : Blo 397767 399535 := bstep (se 1 (by rfl) ⟨299651, by rfl⟩ : syracuseStep 399535 = 599303) B599303
theorem B399559 : Blo 397767 399559 := bstep (se 1 (by rfl) ⟨299669, by rfl⟩ : syracuseStep 399559 = 599339) B599339
theorem B399579 : Blo 397767 399579 := bstep (se 1 (by rfl) ⟨299684, by rfl⟩ : syracuseStep 399579 = 599369) B599369
theorem B399655 : Blo 397767 399655 := bstep (se 1 (by rfl) ⟨299741, by rfl⟩ : syracuseStep 399655 = 599483) B599483
theorem B399695 : Blo 397767 399695 := bstep (se 1 (by rfl) ⟨299771, by rfl⟩ : syracuseStep 399695 = 599543) B599543
theorem B399711 : Blo 397767 399711 := bstep (se 1 (by rfl) ⟨299783, by rfl⟩ : syracuseStep 399711 = 599567) B599567
theorem B399739 : Blo 397767 399739 := bstep (se 1 (by rfl) ⟨299804, by rfl⟩ : syracuseStep 399739 = 599609) B599609
theorem B25041287 : Blo 397767 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B399791 : Blo 397767 399791 := bstep (se 1 (by rfl) ⟨299843, by rfl⟩ : syracuseStep 399791 = 599687) B599687
theorem B399815 : Blo 397767 399815 := bstep (se 1 (by rfl) ⟨299861, by rfl⟩ : syracuseStep 399815 = 599723) B599723
theorem B399835 : Blo 397767 399835 := bstep (se 1 (by rfl) ⟨299876, by rfl⟩ : syracuseStep 399835 = 599753) B599753
theorem B1350107 : Blo 397767 1350107 := bstep (se 1 (by rfl) ⟨1012580, by rfl⟩ : syracuseStep 1350107 = 2025161) B2025161
theorem B3840493 : Blo 397767 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B1219097 : Blo 397767 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B399911 : Blo 397767 399911 := bstep (se 1 (by rfl) ⟨299933, by rfl⟩ : syracuseStep 399911 = 599867) B599867
theorem B399951 : Blo 397767 399951 := bstep (se 1 (by rfl) ⟨299963, by rfl⟩ : syracuseStep 399951 = 599927) B599927
theorem B399967 : Blo 397767 399967 := bstep (se 1 (by rfl) ⟨299975, by rfl⟩ : syracuseStep 399967 = 599951) B599951
theorem B399995 : Blo 397767 399995 := bstep (se 1 (by rfl) ⟨299996, by rfl⟩ : syracuseStep 399995 = 599993) B599993
theorem B2267783 : Blo 397767 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B400047 : Blo 397767 400047 := bstep (se 1 (by rfl) ⟨300035, by rfl⟩ : syracuseStep 400047 = 600071) B600071
theorem B400071 : Blo 397767 400071 := bstep (se 1 (by rfl) ⟨300053, by rfl⟩ : syracuseStep 400071 = 600107) B600107
theorem B400091 : Blo 397767 400091 := bstep (se 1 (by rfl) ⟨300068, by rfl⟩ : syracuseStep 400091 = 600137) B600137
theorem B596729 : Blo 397767 596729 := bstep (se 2 (by rfl) ⟨223773, by rfl⟩ : syracuseStep 596729 = 447547) B447547
theorem B400167 : Blo 397767 400167 := bstep (se 1 (by rfl) ⟨300125, by rfl⟩ : syracuseStep 400167 = 600251) B600251
theorem B400207 : Blo 397767 400207 := bstep (se 1 (by rfl) ⟨300155, by rfl⟩ : syracuseStep 400207 = 600311) B600311
theorem B596831 : Blo 397767 596831 := bstep (se 1 (by rfl) ⟨447623, by rfl⟩ : syracuseStep 596831 = 895247) B895247
theorem B400223 : Blo 397767 400223 := bstep (se 1 (by rfl) ⟨300167, by rfl⟩ : syracuseStep 400223 = 600335) B600335
theorem B760681 : Blo 397767 760681 := bstep (se 2 (by rfl) ⟨285255, by rfl⟩ : syracuseStep 760681 = 570511) B570511
theorem B596843 : Blo 397767 596843 := bstep (se 1 (by rfl) ⟨447632, by rfl⟩ : syracuseStep 596843 = 895265) B895265
theorem B400251 : Blo 397767 400251 := bstep (se 1 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 400251 = 600377) B600377
theorem B400303 : Blo 397767 400303 := bstep (se 1 (by rfl) ⟨300227, by rfl⟩ : syracuseStep 400303 = 600455) B600455
theorem B400327 : Blo 397767 400327 := bstep (se 1 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 400327 = 600491) B600491
theorem B400347 : Blo 397767 400347 := bstep (se 1 (by rfl) ⟨300260, by rfl⟩ : syracuseStep 400347 = 600521) B600521
theorem B1514497 : Blo 397767 1514497 := bstep (se 2 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 1514497 = 1135873) B1135873
theorem B2563073 : Blo 397767 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B400423 : Blo 397767 400423 := bstep (se 1 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 400423 = 600635) B600635
theorem B597071 : Blo 397767 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B400463 : Blo 397767 400463 := bstep (se 1 (by rfl) ⟨300347, by rfl⟩ : syracuseStep 400463 = 600695) B600695
theorem B400479 : Blo 397767 400479 := bstep (se 1 (by rfl) ⟨300359, by rfl⟩ : syracuseStep 400479 = 600719) B600719
theorem B400507 : Blo 397767 400507 := bstep (se 1 (by rfl) ⟨300380, by rfl⟩ : syracuseStep 400507 = 600761) B600761
theorem B1350809 : Blo 397767 1350809 := bstep (se 2 (by rfl) ⟨506553, by rfl⟩ : syracuseStep 1350809 = 1013107) B1013107
theorem B400559 : Blo 397767 400559 := bstep (se 1 (by rfl) ⟨300419, by rfl⟩ : syracuseStep 400559 = 600839) B600839
theorem B1973443 : Blo 397767 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B597191 : Blo 397767 597191 := bstep (se 1 (by rfl) ⟨447893, by rfl⟩ : syracuseStep 597191 = 895787) B895787
theorem B400583 : Blo 397767 400583 := bstep (se 1 (by rfl) ⟨300437, by rfl⟩ : syracuseStep 400583 = 600875) B600875
theorem B400603 : Blo 397767 400603 := bstep (se 1 (by rfl) ⟨300452, by rfl⟩ : syracuseStep 400603 = 600905) B600905
theorem B400679 : Blo 397767 400679 := bstep (se 1 (by rfl) ⟨300509, by rfl⟩ : syracuseStep 400679 = 601019) B601019
theorem B400719 : Blo 397767 400719 := bstep (se 1 (by rfl) ⟨300539, by rfl⟩ : syracuseStep 400719 = 601079) B601079
theorem B400735 : Blo 397767 400735 := bstep (se 1 (by rfl) ⟨300551, by rfl⟩ : syracuseStep 400735 = 601103) B601103
theorem B597353 : Blo 397767 597353 := bstep (se 2 (by rfl) ⟨224007, by rfl⟩ : syracuseStep 597353 = 448015) B448015
theorem B2596211 : Blo 397767 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B400763 : Blo 397767 400763 := bstep (se 1 (by rfl) ⟨300572, by rfl⟩ : syracuseStep 400763 = 601145) B601145
theorem B2465149 : Blo 397767 2465149 := bstep (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) B924431
theorem B400815 : Blo 397767 400815 := bstep (se 1 (by rfl) ⟨300611, by rfl⟩ : syracuseStep 400815 = 601223) B601223
theorem B597431 : Blo 397767 597431 := bstep (se 1 (by rfl) ⟨448073, by rfl⟩ : syracuseStep 597431 = 896147) B896147
theorem B400839 : Blo 397767 400839 := bstep (se 1 (by rfl) ⟨300629, by rfl⟩ : syracuseStep 400839 = 601259) B601259
theorem B597467 : Blo 397767 597467 := bstep (se 1 (by rfl) ⟨448100, by rfl⟩ : syracuseStep 597467 = 896201) B896201
theorem B400859 : Blo 397767 400859 := bstep (se 1 (by rfl) ⟨300644, by rfl⟩ : syracuseStep 400859 = 601289) B601289
theorem B400935 : Blo 397767 400935 := bstep (se 1 (by rfl) ⟨300701, by rfl⟩ : syracuseStep 400935 = 601403) B601403
theorem B400975 : Blo 397767 400975 := bstep (se 1 (by rfl) ⟨300731, by rfl⟩ : syracuseStep 400975 = 601463) B601463
theorem B400991 : Blo 397767 400991 := bstep (se 1 (by rfl) ⟨300743, by rfl⟩ : syracuseStep 400991 = 601487) B601487
theorem B3022433 : Blo 397767 3022433 := bstep (se 2 (by rfl) ⟨1133412, by rfl⟩ : syracuseStep 3022433 = 2266825) B2266825
theorem B401019 : Blo 397767 401019 := bstep (se 1 (by rfl) ⟨300764, by rfl⟩ : syracuseStep 401019 = 601529) B601529
theorem B401071 : Blo 397767 401071 := bstep (se 1 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 401071 = 601607) B601607
theorem B401095 : Blo 397767 401095 := bstep (se 1 (by rfl) ⟨300821, by rfl⟩ : syracuseStep 401095 = 601643) B601643
theorem B761555 : Blo 397767 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B401115 : Blo 397767 401115 := bstep (se 1 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 401115 = 601673) B601673
theorem B1515257 : Blo 397767 1515257 := bstep (se 2 (by rfl) ⟨568221, by rfl⟩ : syracuseStep 1515257 = 1136443) B1136443
theorem B401191 : Blo 397767 401191 := bstep (se 1 (by rfl) ⟨300893, by rfl⟩ : syracuseStep 401191 = 601787) B601787
theorem B401231 : Blo 397767 401231 := bstep (se 1 (by rfl) ⟨300923, by rfl⟩ : syracuseStep 401231 = 601847) B601847
theorem B401247 : Blo 397767 401247 := bstep (se 1 (by rfl) ⟨300935, by rfl⟩ : syracuseStep 401247 = 601871) B601871
theorem B401275 : Blo 397767 401275 := bstep (se 1 (by rfl) ⟨300956, by rfl⟩ : syracuseStep 401275 = 601913) B601913
theorem B597935 : Blo 397767 597935 := bstep (se 1 (by rfl) ⟨448451, by rfl⟩ : syracuseStep 597935 = 896903) B896903
theorem B401327 : Blo 397767 401327 := bstep (se 1 (by rfl) ⟨300995, by rfl⟩ : syracuseStep 401327 = 601991) B601991
theorem B401351 : Blo 397767 401351 := bstep (se 1 (by rfl) ⟨301013, by rfl⟩ : syracuseStep 401351 = 602027) B602027
theorem B401371 : Blo 397767 401371 := bstep (se 1 (by rfl) ⟨301028, by rfl⟩ : syracuseStep 401371 = 602057) B602057
theorem B598025 : Blo 397767 598025 := bstep (se 2 (by rfl) ⟨224259, by rfl⟩ : syracuseStep 598025 = 448519) B448519
theorem B598055 : Blo 397767 598055 := bstep (se 1 (by rfl) ⟨448541, by rfl⟩ : syracuseStep 598055 = 897083) B897083
theorem B401447 : Blo 397767 401447 := bstep (se 1 (by rfl) ⟨301085, by rfl⟩ : syracuseStep 401447 = 602171) B602171
theorem B2269241 : Blo 397767 2269241 := bstep (se 2 (by rfl) ⟨850965, by rfl⟩ : syracuseStep 2269241 = 1701931) B1701931
theorem B401487 : Blo 397767 401487 := bstep (se 1 (by rfl) ⟨301115, by rfl⟩ : syracuseStep 401487 = 602231) B602231
theorem B401503 : Blo 397767 401503 := bstep (se 1 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 401503 = 602255) B602255
theorem B598139 : Blo 397767 598139 := bstep (se 1 (by rfl) ⟨448604, by rfl⟩ : syracuseStep 598139 = 897209) B897209
theorem B401531 : Blo 397767 401531 := bstep (se 1 (by rfl) ⟨301148, by rfl⟩ : syracuseStep 401531 = 602297) B602297
theorem B1613981 : Blo 397767 1613981 := bstep (se 3 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 1613981 = 605243) B605243
theorem B1712285 : Blo 397767 1712285 := bstep (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) B642107
theorem B401583 : Blo 397767 401583 := bstep (se 1 (by rfl) ⟨301187, by rfl⟩ : syracuseStep 401583 = 602375) B602375
theorem B401607 : Blo 397767 401607 := bstep (se 1 (by rfl) ⟨301205, by rfl⟩ : syracuseStep 401607 = 602411) B602411
theorem B401627 : Blo 397767 401627 := bstep (se 1 (by rfl) ⟨301220, by rfl⟩ : syracuseStep 401627 = 602441) B602441
theorem B598265 : Blo 397767 598265 := bstep (se 2 (by rfl) ⟨224349, by rfl⟩ : syracuseStep 598265 = 448699) B448699
theorem B401703 : Blo 397767 401703 := bstep (se 1 (by rfl) ⟨301277, by rfl⟩ : syracuseStep 401703 = 602555) B602555
theorem B1351997 : Blo 397767 1351997 := bstep (se 3 (by rfl) ⟨253499, by rfl⟩ : syracuseStep 1351997 = 506999) B506999
theorem B762185 : Blo 397767 762185 := bstep (se 2 (by rfl) ⟨285819, by rfl⟩ : syracuseStep 762185 = 571639) B571639
theorem B401743 : Blo 397767 401743 := bstep (se 1 (by rfl) ⟨301307, by rfl⟩ : syracuseStep 401743 = 602615) B602615
theorem B598367 : Blo 397767 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B401759 : Blo 397767 401759 := bstep (se 1 (by rfl) ⟨301319, by rfl⟩ : syracuseStep 401759 = 602639) B602639
theorem B598379 : Blo 397767 598379 := bstep (se 1 (by rfl) ⟨448784, by rfl⟩ : syracuseStep 598379 = 897569) B897569
theorem B598607 : Blo 397767 598607 := bstep (se 1 (by rfl) ⟨448955, by rfl⟩ : syracuseStep 598607 = 897911) B897911
theorem B10887797 : Blo 397767 10887797 := bstep (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) B1020731
theorem B2433721 : Blo 397767 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B598727 : Blo 397767 598727 := bstep (se 1 (by rfl) ⟨449045, by rfl⟩ : syracuseStep 598727 = 898091) B898091
theorem B1286867 : Blo 397767 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B598889 : Blo 397767 598889 := bstep (se 2 (by rfl) ⟨224583, by rfl⟩ : syracuseStep 598889 = 449167) B449167
theorem B959393 : Blo 397767 959393 := bstep (se 2 (by rfl) ⟨359772, by rfl⟩ : syracuseStep 959393 = 719545) B719545
theorem B598967 : Blo 397767 598967 := bstep (se 1 (by rfl) ⟨449225, by rfl⟩ : syracuseStep 598967 = 898451) B898451
theorem B599003 : Blo 397767 599003 := bstep (se 1 (by rfl) ⟨449252, by rfl⟩ : syracuseStep 599003 = 898505) B898505
theorem B3023891 : Blo 397767 3023891 := bstep (se 1 (by rfl) ⟨2267918, by rfl⟩ : syracuseStep 3023891 = 4535837) B4535837
theorem B1352861 : Blo 397767 1352861 := bstep (se 3 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 1352861 = 507323) B507323
theorem B1516715 : Blo 397767 1516715 := bstep (se 1 (by rfl) ⟨1137536, by rfl⟩ : syracuseStep 1516715 = 2275073) B2275073
theorem B599471 : Blo 397767 599471 := bstep (se 1 (by rfl) ⟨449603, by rfl⟩ : syracuseStep 599471 = 899207) B899207
theorem B599561 : Blo 397767 599561 := bstep (se 2 (by rfl) ⟨224835, by rfl⟩ : syracuseStep 599561 = 449671) B449671
theorem B599591 : Blo 397767 599591 := bstep (se 1 (by rfl) ⟨449693, by rfl⟩ : syracuseStep 599591 = 899387) B899387
theorem B599675 : Blo 397767 599675 := bstep (se 1 (by rfl) ⟨449756, by rfl⟩ : syracuseStep 599675 = 899513) B899513
theorem B1353401 : Blo 397767 1353401 := bstep (se 2 (by rfl) ⟨507525, by rfl⟩ : syracuseStep 1353401 = 1015051) B1015051
theorem B599801 : Blo 397767 599801 := bstep (se 2 (by rfl) ⟨224925, by rfl⟩ : syracuseStep 599801 = 449851) B449851
theorem B599903 : Blo 397767 599903 := bstep (se 1 (by rfl) ⟨449927, by rfl⟩ : syracuseStep 599903 = 899855) B899855
theorem B599915 : Blo 397767 599915 := bstep (se 1 (by rfl) ⟨449936, by rfl⟩ : syracuseStep 599915 = 899873) B899873
theorem B894995 : Blo 397767 894995 := bstep (se 1 (by rfl) ⟨671246, by rfl⟩ : syracuseStep 894995 = 1342493) B1342493
theorem B600143 : Blo 397767 600143 := bstep (se 1 (by rfl) ⟨450107, by rfl⟩ : syracuseStep 600143 = 900215) B900215
theorem B600263 : Blo 397767 600263 := bstep (se 1 (by rfl) ⟨450197, by rfl⟩ : syracuseStep 600263 = 900395) B900395
theorem B1353995 : Blo 397767 1353995 := bstep (se 1 (by rfl) ⟨1015496, by rfl⟩ : syracuseStep 1353995 = 2030993) B2030993
theorem B1517885 : Blo 397767 1517885 := bstep (se 3 (by rfl) ⟨284603, by rfl⟩ : syracuseStep 1517885 = 569207) B569207
theorem B895337 : Blo 397767 895337 := bstep (se 2 (by rfl) ⟨335751, by rfl⟩ : syracuseStep 895337 = 671503) B671503
theorem B600425 : Blo 397767 600425 := bstep (se 2 (by rfl) ⟨225159, by rfl⟩ : syracuseStep 600425 = 450319) B450319
theorem B600503 : Blo 397767 600503 := bstep (se 1 (by rfl) ⟨450377, by rfl⟩ : syracuseStep 600503 = 900755) B900755
theorem B600539 : Blo 397767 600539 := bstep (se 1 (by rfl) ⟨450404, by rfl⟩ : syracuseStep 600539 = 900809) B900809
theorem B2271725 : Blo 397767 2271725 := bstep (se 3 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 2271725 = 851897) B851897
theorem B1354265 : Blo 397767 1354265 := bstep (se 2 (by rfl) ⟨507849, by rfl⟩ : syracuseStep 1354265 = 1015699) B1015699
theorem B1518203 : Blo 397767 1518203 := bstep (se 1 (by rfl) ⟨1138652, by rfl⟩ : syracuseStep 1518203 = 2277305) B2277305
theorem B4532921 : Blo 397767 4532921 := bstep (se 2 (by rfl) ⟨1699845, by rfl⟩ : syracuseStep 4532921 = 3399691) B3399691
theorem B862969 : Blo 397767 862969 := bstep (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) B647227
theorem B601007 : Blo 397767 601007 := bstep (se 1 (by rfl) ⟨450755, by rfl⟩ : syracuseStep 601007 = 901511) B901511
theorem B895931 : Blo 397767 895931 := bstep (se 1 (by rfl) ⟨671948, by rfl⟩ : syracuseStep 895931 = 1343897) B1343897
theorem B601097 : Blo 397767 601097 := bstep (se 2 (by rfl) ⟨225411, by rfl⟩ : syracuseStep 601097 = 450823) B450823
theorem B601127 : Blo 397767 601127 := bstep (se 1 (by rfl) ⟨450845, by rfl⟩ : syracuseStep 601127 = 901691) B901691
theorem B896057 : Blo 397767 896057 := bstep (se 2 (by rfl) ⟨336021, by rfl⟩ : syracuseStep 896057 = 672043) B672043
theorem B601211 : Blo 397767 601211 := bstep (se 1 (by rfl) ⟨450908, by rfl⟩ : syracuseStep 601211 = 901817) B901817
theorem B4304119 : Blo 397767 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B601337 : Blo 397767 601337 := bstep (se 2 (by rfl) ⟨225501, by rfl⟩ : syracuseStep 601337 = 451003) B451003
theorem B601439 : Blo 397767 601439 := bstep (se 1 (by rfl) ⟨451079, by rfl⟩ : syracuseStep 601439 = 902159) B902159
theorem B601451 : Blo 397767 601451 := bstep (se 1 (by rfl) ⟨451088, by rfl⟩ : syracuseStep 601451 = 902177) B902177
theorem B896399 : Blo 397767 896399 := bstep (se 1 (by rfl) ⟨672299, by rfl⟩ : syracuseStep 896399 = 1344599) B1344599
theorem B1945127 : Blo 397767 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B601679 : Blo 397767 601679 := bstep (se 1 (by rfl) ⟨451259, by rfl⟩ : syracuseStep 601679 = 902519) B902519
theorem B1355399 : Blo 397767 1355399 := bstep (se 1 (by rfl) ⟨1016549, by rfl⟩ : syracuseStep 1355399 = 2033099) B2033099
theorem B1355453 : Blo 397767 1355453 := bstep (se 3 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 1355453 = 508295) B508295
theorem B601799 : Blo 397767 601799 := bstep (se 1 (by rfl) ⟨451349, by rfl⟩ : syracuseStep 601799 = 902699) B902699
theorem B896723 : Blo 397767 896723 := bstep (se 1 (by rfl) ⟨672542, by rfl⟩ : syracuseStep 896723 = 1345085) B1345085
theorem B1716011 : Blo 397767 1716011 := bstep (se 1 (by rfl) ⟨1287008, by rfl⟩ : syracuseStep 1716011 = 2574017) B2574017
theorem B1355615 : Blo 397767 1355615 := bstep (se 1 (by rfl) ⟨1016711, by rfl⟩ : syracuseStep 1355615 = 2033423) B2033423
theorem B601961 : Blo 397767 601961 := bstep (se 2 (by rfl) ⟨225735, by rfl⟩ : syracuseStep 601961 = 451471) B451471
theorem B3026807 : Blo 397767 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B602039 : Blo 397767 602039 := bstep (se 1 (by rfl) ⟨451529, by rfl⟩ : syracuseStep 602039 = 903059) B903059
theorem B602075 : Blo 397767 602075 := bstep (se 1 (by rfl) ⟨451556, by rfl⟩ : syracuseStep 602075 = 903113) B903113
theorem B1355777 : Blo 397767 1355777 := bstep (se 2 (by rfl) ⟨508416, by rfl⟩ : syracuseStep 1355777 = 1016833) B1016833
theorem B1519631 : Blo 397767 1519631 := bstep (se 1 (by rfl) ⟨1139723, by rfl⟩ : syracuseStep 1519631 = 2279447) B2279447
theorem B3649853 : Blo 397767 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B3912065 : Blo 397767 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B602543 : Blo 397767 602543 := bstep (se 1 (by rfl) ⟨451907, by rfl⟩ : syracuseStep 602543 = 903815) B903815
theorem B2437613 : Blo 397767 2437613 := bstep (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) B914105
theorem B602633 : Blo 397767 602633 := bstep (se 2 (by rfl) ⟨225987, by rfl⟩ : syracuseStep 602633 = 451975) B451975
theorem B897659 : Blo 397767 897659 := bstep (se 1 (by rfl) ⟨673244, by rfl⟩ : syracuseStep 897659 = 1346489) B1346489
theorem B8630995 : Blo 397767 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B897785 : Blo 397767 897785 := bstep (se 2 (by rfl) ⟨336669, by rfl⟩ : syracuseStep 897785 = 673339) B673339
theorem B1618717 : Blo 397767 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B898055 : Blo 397767 898055 := bstep (se 1 (by rfl) ⟨673541, by rfl⟩ : syracuseStep 898055 = 1347083) B1347083
theorem B898127 : Blo 397767 898127 := bstep (se 1 (by rfl) ⟨673595, by rfl⟩ : syracuseStep 898127 = 1347191) B1347191
theorem B898523 : Blo 397767 898523 := bstep (se 1 (by rfl) ⟨673892, by rfl⟩ : syracuseStep 898523 = 1347785) B1347785
theorem B1521287 : Blo 397767 1521287 := bstep (se 1 (by rfl) ⟨1140965, by rfl⟩ : syracuseStep 1521287 = 2281931) B2281931
theorem B2471639 : Blo 397767 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B1914617 : Blo 397767 1914617 := bstep (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) B1435963
theorem B5748515 : Blo 397767 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B898991 : Blo 397767 898991 := bstep (se 1 (by rfl) ⟨674243, by rfl⟩ : syracuseStep 898991 = 1348487) B1348487
theorem B866231 : Blo 397767 866231 := bstep (se 1 (by rfl) ⟨649673, by rfl⟩ : syracuseStep 866231 = 1299347) B1299347
theorem B3225757 : Blo 397767 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B899243 : Blo 397767 899243 := bstep (se 1 (by rfl) ⟨674432, by rfl⟩ : syracuseStep 899243 = 1348865) B1348865
theorem B637289 : Blo 397767 637289 := bstep (se 2 (by rfl) ⟨238983, by rfl⟩ : syracuseStep 637289 = 477967) B477967
theorem B506407 : Blo 397767 506407 := bstep (se 1 (by rfl) ⟨379805, by rfl⟩ : syracuseStep 506407 = 759611) B759611
theorem B1522273 : Blo 397767 1522273 := bstep (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) B1141705
theorem B539335 : Blo 397767 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B899783 : Blo 397767 899783 := bstep (se 1 (by rfl) ⟨674837, by rfl⟩ : syracuseStep 899783 = 1349675) B1349675
theorem B2276099 : Blo 397767 2276099 := bstep (se 1 (by rfl) ⟨1707074, by rfl⟩ : syracuseStep 2276099 = 3414149) B3414149
theorem B506731 : Blo 397767 506731 := bstep (se 1 (by rfl) ⟨380048, by rfl⟩ : syracuseStep 506731 = 760097) B760097
theorem B4340627 : Blo 397767 4340627 := bstep (se 1 (by rfl) ⟨3255470, by rfl⟩ : syracuseStep 4340627 = 6510941) B6510941
theorem B1522745 : Blo 397767 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B3030209 : Blo 397767 3030209 := bstep (se 2 (by rfl) ⟨1136328, by rfl⟩ : syracuseStep 3030209 = 2272657) B2272657
theorem B408871 : Blo 397767 408871 := bstep (se 1 (by rfl) ⟨306653, by rfl⟩ : syracuseStep 408871 = 613307) B613307
theorem B2735525 : Blo 397767 2735525 := bstep (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) B512911
theorem B41729539 : Blo 397767 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B900647 : Blo 397767 900647 := bstep (se 1 (by rfl) ⟨675485, by rfl⟩ : syracuseStep 900647 = 1350971) B1350971
theorem B900971 : Blo 397767 900971 := bstep (se 1 (by rfl) ⟨675728, by rfl⟩ : syracuseStep 900971 = 1351457) B1351457
theorem B901025 : Blo 397767 901025 := bstep (se 2 (by rfl) ⟨337884, by rfl⟩ : syracuseStep 901025 = 675769) B675769
theorem B671753 : Blo 397767 671753 := bstep (se 2 (by rfl) ⟨251907, by rfl⟩ : syracuseStep 671753 = 503815) B503815
theorem B1523731 : Blo 397767 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B508027 : Blo 397767 508027 := bstep (se 1 (by rfl) ⟨381020, by rfl⟩ : syracuseStep 508027 = 762041) B762041
theorem B671915 : Blo 397767 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B901367 : Blo 397767 901367 := bstep (se 1 (by rfl) ⟨676025, by rfl⟩ : syracuseStep 901367 = 1352051) B1352051
theorem B2572631 : Blo 397767 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B4538753 : Blo 397767 4538753 := bstep (se 2 (by rfl) ⟨1702032, by rfl⟩ : syracuseStep 4538753 = 3404065) B3404065
theorem B672313 : Blo 397767 672313 := bstep (se 2 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 672313 = 504235) B504235
theorem B672455 : Blo 397767 672455 := bstep (se 1 (by rfl) ⟨504341, by rfl⟩ : syracuseStep 672455 = 1008683) B1008683
theorem B869063 : Blo 397767 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B901961 : Blo 397767 901961 := bstep (se 2 (by rfl) ⟨338235, by rfl⟩ : syracuseStep 901961 = 676471) B676471
theorem B672617 : Blo 397767 672617 := bstep (se 2 (by rfl) ⟨252231, by rfl⟩ : syracuseStep 672617 = 504463) B504463
theorem B607081 : Blo 397767 607081 := bstep (se 2 (by rfl) ⟨227655, by rfl⟩ : syracuseStep 607081 = 455311) B455311
theorem B1459063 : Blo 397767 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B15352739 : Blo 397767 15352739 := bstep (se 1 (by rfl) ⟨11514554, by rfl⟩ : syracuseStep 15352739 = 23029109) B23029109
theorem B4342835 : Blo 397767 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B640057 : Blo 397767 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B673015 : Blo 397767 673015 := bstep (se 1 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 673015 = 1009523) B1009523
theorem B673211 : Blo 397767 673211 := bstep (se 1 (by rfl) ⟨504908, by rfl⟩ : syracuseStep 673211 = 1009817) B1009817
theorem B673319 : Blo 397767 673319 := bstep (se 1 (by rfl) ⟨504989, by rfl⟩ : syracuseStep 673319 = 1009979) B1009979
theorem B902753 : Blo 397767 902753 := bstep (se 2 (by rfl) ⟨338532, by rfl⟩ : syracuseStep 902753 = 677065) B677065
theorem B2573963 : Blo 397767 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B10208915 : Blo 397767 10208915 := bstep (se 1 (by rfl) ⟨7656686, by rfl⟩ : syracuseStep 10208915 = 15313373) B15313373
theorem B1525463 : Blo 397767 1525463 := bstep (se 1 (by rfl) ⟨1144097, by rfl⟩ : syracuseStep 1525463 = 2288195) B2288195
theorem B673609 : Blo 397767 673609 := bstep (se 2 (by rfl) ⟨252603, by rfl⟩ : syracuseStep 673609 = 505207) B505207
theorem B673643 : Blo 397767 673643 := bstep (se 1 (by rfl) ⟨505232, by rfl⟩ : syracuseStep 673643 = 1010465) B1010465
theorem B3426209 : Blo 397767 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B903095 : Blo 397767 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B3033125 : Blo 397767 3033125 := bstep (se 4 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 3033125 = 568711) B568711
theorem B674041 : Blo 397767 674041 := bstep (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) B505531
theorem B2017547 : Blo 397767 2017547 := bstep (se 1 (by rfl) ⟨1513160, by rfl⟩ : syracuseStep 2017547 = 3026321) B3026321
theorem B674311 : Blo 397767 674311 := bstep (se 1 (by rfl) ⟨505733, by rfl⟩ : syracuseStep 674311 = 1011467) B1011467
theorem B903689 : Blo 397767 903689 := bstep (se 2 (by rfl) ⟨338883, by rfl⟩ : syracuseStep 903689 = 677767) B677767
theorem B2214611 : Blo 397767 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B2280221 : Blo 397767 2280221 := bstep (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) B855083
theorem B674743 : Blo 397767 674743 := bstep (se 1 (by rfl) ⟨506057, by rfl⟩ : syracuseStep 674743 = 1012115) B1012115
theorem B1625203 : Blo 397767 1625203 := bstep (se 1 (by rfl) ⟨1218902, by rfl⟩ : syracuseStep 1625203 = 2437805) B2437805
theorem B674939 : Blo 397767 674939 := bstep (se 1 (by rfl) ⟨506204, by rfl⟩ : syracuseStep 674939 = 1012409) B1012409
theorem B2280905 : Blo 397767 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B675337 : Blo 397767 675337 := bstep (se 2 (by rfl) ⟨253251, by rfl⟩ : syracuseStep 675337 = 506503) B506503
theorem B675499 : Blo 397767 675499 := bstep (se 1 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 675499 = 1013249) B1013249
theorem B2019005 : Blo 397767 2019005 := bstep (se 3 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 2019005 = 757127) B757127
theorem B2019167 : Blo 397767 2019167 := bstep (se 1 (by rfl) ⟨1514375, by rfl⟩ : syracuseStep 2019167 = 3028751) B3028751
theorem B675803 : Blo 397767 675803 := bstep (se 1 (by rfl) ⟨506852, by rfl⟩ : syracuseStep 675803 = 1013705) B1013705
theorem B643081 : Blo 397767 643081 := bstep (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) B482311
theorem B676039 : Blo 397767 676039 := bstep (se 1 (by rfl) ⟨507029, by rfl⟩ : syracuseStep 676039 = 1014059) B1014059
theorem B3428669 : Blo 397767 3428669 := bstep (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) B1285751
theorem B676201 : Blo 397767 676201 := bstep (se 2 (by rfl) ⟨253575, by rfl⟩ : syracuseStep 676201 = 507151) B507151
theorem B5132753 : Blo 397767 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B1626763 : Blo 397767 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B1626923 : Blo 397767 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B676795 : Blo 397767 676795 := bstep (se 1 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 676795 = 1015193) B1015193
theorem B676903 : Blo 397767 676903 := bstep (se 1 (by rfl) ⟨507677, by rfl⟩ : syracuseStep 676903 = 1015355) B1015355
theorem B480619 : Blo 397767 480619 := bstep (se 1 (by rfl) ⟨360464, by rfl⟩ : syracuseStep 480619 = 720929) B720929
theorem B677227 : Blo 397767 677227 := bstep (se 1 (by rfl) ⟨507920, by rfl⟩ : syracuseStep 677227 = 1015841) B1015841
theorem B12342881 : Blo 397767 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B448123 : Blo 397767 448123 := bstep (se 1 (by rfl) ⟨336092, by rfl⟩ : syracuseStep 448123 = 672185) B672185
theorem B1922707 : Blo 397767 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B1955771 : Blo 397767 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B448591 : Blo 397767 448591 := bstep (se 1 (by rfl) ⟨336443, by rfl⟩ : syracuseStep 448591 = 672887) B672887
theorem B8673641 : Blo 397767 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B1366397 : Blo 397767 1366397 := bstep (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) B512399
theorem B448987 : Blo 397767 448987 := bstep (se 1 (by rfl) ⟨336740, by rfl⟩ : syracuseStep 448987 = 673481) B673481
theorem B2021921 : Blo 397767 2021921 := bstep (se 2 (by rfl) ⟨758220, by rfl⟩ : syracuseStep 2021921 = 1516441) B1516441
theorem B1366777 : Blo 397767 1366777 := bstep (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) B1025083
theorem B1137503 : Blo 397767 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B449455 : Blo 397767 449455 := bstep (se 1 (by rfl) ⟨337091, by rfl⟩ : syracuseStep 449455 = 674183) B674183
theorem B2284595 : Blo 397767 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B6151247 : Blo 397767 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B1236125 : Blo 397767 1236125 := bstep (se 3 (by rfl) ⟨231773, by rfl⟩ : syracuseStep 1236125 = 463547) B463547
theorem B449887 : Blo 397767 449887 := bstep (se 1 (by rfl) ⟨337415, by rfl⟩ : syracuseStep 449887 = 674831) B674831
theorem B1924553 : Blo 397767 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B1007113 : Blo 397767 1007113 := bstep (se 2 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 1007113 = 755335) B755335
theorem B450247 : Blo 397767 450247 := bstep (se 1 (by rfl) ⟨337685, by rfl⟩ : syracuseStep 450247 = 675371) B675371
theorem B1924823 : Blo 397767 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B2055901 : Blo 397767 2055901 := bstep (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) B770963
theorem B3038957 : Blo 397767 3038957 := bstep (se 3 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 3038957 = 1139609) B1139609
theorem B1236809 : Blo 397767 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B2875297 : Blo 397767 2875297 := bstep (se 2 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 2875297 = 2156473) B2156473
theorem B1138607 : Blo 397767 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B451111 : Blo 397767 451111 := bstep (se 1 (by rfl) ⟨338333, by rfl⟩ : syracuseStep 451111 = 676667) B676667
theorem B3039929 : Blo 397767 3039929 := bstep (se 2 (by rfl) ⟨1139973, by rfl⟩ : syracuseStep 3039929 = 2279947) B2279947
theorem B1172183 : Blo 397767 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1434361 : Blo 397767 1434361 := bstep (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) B1075771
theorem B1008571 : Blo 397767 1008571 := bstep (se 1 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 1008571 = 1512857) B1512857
theorem B713927 : Blo 397767 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B2024999 : Blo 397767 2024999 := bstep (se 1 (by rfl) ⟨1518749, by rfl⟩ : syracuseStep 2024999 = 3037499) B3037499
theorem B3040901 : Blo 397767 3040901 := bstep (se 4 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 3040901 = 570169) B570169
theorem B1435805 : Blo 397767 1435805 := bstep (se 3 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 1435805 = 538427) B538427
theorem B813739 : Blo 397767 813739 := bstep (se 1 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 813739 = 1220609) B1220609
theorem B3402425 : Blo 397767 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B5106509 : Blo 397767 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B453983 : Blo 397767 453983 := bstep (se 1 (by rfl) ⟨340487, by rfl⟩ : syracuseStep 453983 = 680975) B680975
theorem B1011163 : Blo 397767 1011163 := bstep (se 1 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 1011163 = 1516745) B1516745
theorem B2027105 : Blo 397767 2027105 := bstep (se 2 (by rfl) ⟨760164, by rfl⟩ : syracuseStep 2027105 = 1520329) B1520329
theorem B3043331 : Blo 397767 3043331 := bstep (se 1 (by rfl) ⟨2282498, by rfl⟩ : syracuseStep 3043331 = 4564997) B4564997
theorem B1011791 : Blo 397767 1011791 := bstep (se 1 (by rfl) ⟨758843, by rfl⟩ : syracuseStep 1011791 = 1517687) B1517687
theorem B11497949 : Blo 397767 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B1143335 : Blo 397767 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B6451771 : Blo 397767 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B1012439 : Blo 397767 1012439 := bstep (se 1 (by rfl) ⟨759329, by rfl⟩ : syracuseStep 1012439 = 1518659) B1518659
theorem B13202189 : Blo 397767 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B1930013 : Blo 397767 1930013 := bstep (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) B723755
theorem B2880485 : Blo 397767 2880485 := bstep (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) B540091
theorem B2028563 : Blo 397767 2028563 := bstep (se 1 (by rfl) ⟨1521422, by rfl⟩ : syracuseStep 2028563 = 3042845) B3042845
theorem B685135 : Blo 397767 685135 := bstep (se 1 (by rfl) ⟨513851, by rfl⟩ : syracuseStep 685135 = 1027703) B1027703
theorem B2618825 : Blo 397767 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B4388413 : Blo 397767 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B1275527 : Blo 397767 1275527 := bstep (se 1 (by rfl) ⟨956645, by rfl⟩ : syracuseStep 1275527 = 1913291) B1913291
theorem B718507 : Blo 397767 718507 := bstep (se 1 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 718507 = 1077761) B1077761
theorem B5601061 : Blo 397767 5601061 := bstep (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) B1050199
theorem B849847 : Blo 397767 849847 := bstep (se 1 (by rfl) ⟨637385, by rfl⟩ : syracuseStep 849847 = 1274771) B1274771
theorem B1702205 : Blo 397767 1702205 := bstep (se 3 (by rfl) ⟨319163, by rfl⟩ : syracuseStep 1702205 = 638327) B638327
theorem B3045761 : Blo 397767 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B4094509 : Blo 397767 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B12909131 : Blo 397767 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B1276859 : Blo 397767 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B1211411 : Blo 397767 1211411 := bstep (se 1 (by rfl) ⟨908558, by rfl⟩ : syracuseStep 1211411 = 1817117) B1817117
theorem B719891 : Blo 397767 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B1015031 : Blo 397767 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B36961757 : Blo 397767 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B2031479 : Blo 397767 2031479 := bstep (se 1 (by rfl) ⟨1523609, by rfl⟩ : syracuseStep 2031479 = 3047219) B3047219
theorem B2031641 : Blo 397767 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B12255947 : Blo 397767 12255947 := bstep (se 1 (by rfl) ⟨9191960, by rfl⟩ : syracuseStep 12255947 = 18383921) B18383921
theorem B5833619 : Blo 397767 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B3244961 : Blo 397767 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B1016975 : Blo 397767 1016975 := bstep (se 1 (by rfl) ⟨762731, by rfl⟩ : syracuseStep 1016975 = 1525463) B1525463
theorem B1344761 : Blo 397767 1344761 := bstep (se 2 (by rfl) ⟨504285, by rfl⟩ : syracuseStep 1344761 = 1008571) B1008571
theorem B853409 : Blo 397767 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B1345031 : Blo 397767 1345031 := bstep (se 1 (by rfl) ⟨1008773, by rfl⟩ : syracuseStep 1345031 = 2017547) B2017547
theorem B722515 : Blo 397767 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B1476407 : Blo 397767 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B854383 : Blo 397767 854383 := bstep (se 1 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 854383 = 1281575) B1281575
theorem B1346003 : Blo 397767 1346003 := bstep (se 1 (by rfl) ⟨1009502, by rfl⟩ : syracuseStep 1346003 = 2019005) B2019005
theorem B1346111 : Blo 397767 1346111 := bstep (se 1 (by rfl) ⟨1009583, by rfl⟩ : syracuseStep 1346111 = 2019167) B2019167
theorem B789113 : Blo 397767 789113 := bstep (se 2 (by rfl) ⟨295917, by rfl⟩ : syracuseStep 789113 = 591835) B591835
theorem B2951927 : Blo 397767 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B1706939 : Blo 397767 1706939 := bstep (se 1 (by rfl) ⟨1280204, by rfl⟩ : syracuseStep 1706939 = 2560409) B2560409
theorem B3017843 : Blo 397767 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B1707227 : Blo 397767 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B2886943 : Blo 397767 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B1084985 : Blo 397767 1084985 := bstep (se 2 (by rfl) ⟨406869, by rfl⟩ : syracuseStep 1084985 = 813739) B813739
theorem B1150625 : Blo 397767 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B8228587 : Blo 397767 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B6983533 : Blo 397767 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B5738825 : Blo 397767 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B1347947 : Blo 397767 1347947 := bstep (se 1 (by rfl) ⟨1010960, by rfl⟩ : syracuseStep 1347947 = 2021921) B2021921
theorem B1511855 : Blo 397767 1511855 := bstep (se 1 (by rfl) ⟨1133891, by rfl⟩ : syracuseStep 1511855 = 2267783) B2267783
theorem B397819 : Blo 397767 397819 := bstep (se 1 (by rfl) ⟨298364, by rfl⟩ : syracuseStep 397819 = 596729) B596729
theorem B397887 : Blo 397767 397887 := bstep (se 1 (by rfl) ⟨298415, by rfl⟩ : syracuseStep 397887 = 596831) B596831
theorem B758335 : Blo 397767 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B397895 : Blo 397767 397895 := bstep (se 1 (by rfl) ⟨298421, by rfl⟩ : syracuseStep 397895 = 596843) B596843
theorem B1348217 : Blo 397767 1348217 := bstep (se 2 (by rfl) ⟨505581, by rfl⟩ : syracuseStep 1348217 = 1011163) B1011163
theorem B1708715 : Blo 397767 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B398047 : Blo 397767 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B4100831 : Blo 397767 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B398127 : Blo 397767 398127 := bstep (se 1 (by rfl) ⟨298595, by rfl⟩ : syracuseStep 398127 = 597191) B597191
theorem B398235 : Blo 397767 398235 := bstep (se 1 (by rfl) ⟨298676, by rfl⟩ : syracuseStep 398235 = 597353) B597353
theorem B398287 : Blo 397767 398287 := bstep (se 1 (by rfl) ⟨298715, by rfl⟩ : syracuseStep 398287 = 597431) B597431
theorem B1283035 : Blo 397767 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B398311 : Blo 397767 398311 := bstep (se 1 (by rfl) ⟨298733, by rfl⟩ : syracuseStep 398311 = 597467) B597467
theorem B1283215 : Blo 397767 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B398623 : Blo 397767 398623 := bstep (se 1 (by rfl) ⟨298967, by rfl⟩ : syracuseStep 398623 = 597935) B597935
theorem B759071 : Blo 397767 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B398683 : Blo 397767 398683 := bstep (se 1 (by rfl) ⟨299012, by rfl⟩ : syracuseStep 398683 = 598025) B598025
theorem B857441 : Blo 397767 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B398703 : Blo 397767 398703 := bstep (se 1 (by rfl) ⟨299027, by rfl⟩ : syracuseStep 398703 = 598055) B598055
theorem B1512827 : Blo 397767 1512827 := bstep (se 1 (by rfl) ⟨1134620, by rfl⟩ : syracuseStep 1512827 = 2269241) B2269241
theorem B398759 : Blo 397767 398759 := bstep (se 1 (by rfl) ⟨299069, by rfl⟩ : syracuseStep 398759 = 598139) B598139
theorem B398843 : Blo 397767 398843 := bstep (se 1 (by rfl) ⟨299132, by rfl⟩ : syracuseStep 398843 = 598265) B598265
theorem B398911 : Blo 397767 398911 := bstep (se 1 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 398911 = 598367) B598367
theorem B398919 : Blo 397767 398919 := bstep (se 1 (by rfl) ⟨299189, by rfl⟩ : syracuseStep 398919 = 598379) B598379
theorem B399071 : Blo 397767 399071 := bstep (se 1 (by rfl) ⟨299303, by rfl⟩ : syracuseStep 399071 = 598607) B598607
theorem B399151 : Blo 397767 399151 := bstep (se 1 (by rfl) ⟨299363, by rfl⟩ : syracuseStep 399151 = 598727) B598727
theorem B399259 : Blo 397767 399259 := bstep (se 1 (by rfl) ⟨299444, by rfl⟩ : syracuseStep 399259 = 598889) B598889
theorem B399311 : Blo 397767 399311 := bstep (se 1 (by rfl) ⟨299483, by rfl⟩ : syracuseStep 399311 = 598967) B598967
theorem B399335 : Blo 397767 399335 := bstep (se 1 (by rfl) ⟨299501, by rfl⟩ : syracuseStep 399335 = 599003) B599003
theorem B2169017 : Blo 397767 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B11507993 : Blo 397767 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B399647 : Blo 397767 399647 := bstep (se 1 (by rfl) ⟨299735, by rfl⟩ : syracuseStep 399647 = 599471) B599471
theorem B399707 : Blo 397767 399707 := bstep (se 1 (by rfl) ⟨299780, by rfl⟩ : syracuseStep 399707 = 599561) B599561
theorem B399727 : Blo 397767 399727 := bstep (se 1 (by rfl) ⟨299795, by rfl⟩ : syracuseStep 399727 = 599591) B599591
theorem B1349999 : Blo 397767 1349999 := bstep (se 1 (by rfl) ⟨1012499, by rfl⟩ : syracuseStep 1349999 = 2024999) B2024999
theorem B399783 : Blo 397767 399783 := bstep (se 1 (by rfl) ⟨299837, by rfl⟩ : syracuseStep 399783 = 599675) B599675
theorem B399867 : Blo 397767 399867 := bstep (se 1 (by rfl) ⟨299900, by rfl⟩ : syracuseStep 399867 = 599801) B599801
theorem B399935 : Blo 397767 399935 := bstep (se 1 (by rfl) ⟨299951, by rfl⟩ : syracuseStep 399935 = 599903) B599903
theorem B399943 : Blo 397767 399943 := bstep (se 1 (by rfl) ⟨299957, by rfl⟩ : syracuseStep 399943 = 599915) B599915
theorem B596663 : Blo 397767 596663 := bstep (se 1 (by rfl) ⟨447497, by rfl⟩ : syracuseStep 596663 = 894995) B894995
theorem B400095 : Blo 397767 400095 := bstep (se 1 (by rfl) ⟨300071, by rfl⟩ : syracuseStep 400095 = 600143) B600143
theorem B3250925 : Blo 397767 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B957203 : Blo 397767 957203 := bstep (se 1 (by rfl) ⟨717902, by rfl⟩ : syracuseStep 957203 = 1435805) B1435805
theorem B400175 : Blo 397767 400175 := bstep (se 1 (by rfl) ⟨300131, by rfl⟩ : syracuseStep 400175 = 600263) B600263
theorem B596891 : Blo 397767 596891 := bstep (se 1 (by rfl) ⟨447668, by rfl⟩ : syracuseStep 596891 = 895337) B895337
theorem B400283 : Blo 397767 400283 := bstep (se 1 (by rfl) ⟨300212, by rfl⟩ : syracuseStep 400283 = 600425) B600425
theorem B400335 : Blo 397767 400335 := bstep (se 1 (by rfl) ⟨300251, by rfl⟩ : syracuseStep 400335 = 600503) B600503
theorem B400359 : Blo 397767 400359 := bstep (se 1 (by rfl) ⟨300269, by rfl⟩ : syracuseStep 400359 = 600539) B600539
theorem B1514483 : Blo 397767 1514483 := bstep (se 1 (by rfl) ⟨1135862, by rfl⟩ : syracuseStep 1514483 = 2271725) B2271725
theorem B3021947 : Blo 397767 3021947 := bstep (se 1 (by rfl) ⟨2266460, by rfl⟩ : syracuseStep 3021947 = 4532921) B4532921
theorem B2268283 : Blo 397767 2268283 := bstep (se 1 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 2268283 = 3402425) B3402425
theorem B2563301 : Blo 397767 2563301 := bstep (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) B480619
theorem B400671 : Blo 397767 400671 := bstep (se 1 (by rfl) ⟨300503, by rfl⟩ : syracuseStep 400671 = 601007) B601007
theorem B597287 : Blo 397767 597287 := bstep (se 1 (by rfl) ⟨447965, by rfl⟩ : syracuseStep 597287 = 895931) B895931
theorem B400731 : Blo 397767 400731 := bstep (se 1 (by rfl) ⟨300548, by rfl⟩ : syracuseStep 400731 = 601097) B601097
theorem B400751 : Blo 397767 400751 := bstep (se 1 (by rfl) ⟨300563, by rfl⟩ : syracuseStep 400751 = 601127) B601127
theorem B597371 : Blo 397767 597371 := bstep (se 1 (by rfl) ⟨448028, by rfl⟩ : syracuseStep 597371 = 896057) B896057
theorem B400807 : Blo 397767 400807 := bstep (se 1 (by rfl) ⟨300605, by rfl⟩ : syracuseStep 400807 = 601211) B601211
theorem B597497 : Blo 397767 597497 := bstep (se 2 (by rfl) ⟨224061, by rfl⟩ : syracuseStep 597497 = 448123) B448123
theorem B400891 : Blo 397767 400891 := bstep (se 1 (by rfl) ⟨300668, by rfl⟩ : syracuseStep 400891 = 601337) B601337
theorem B2563609 : Blo 397767 2563609 := bstep (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) B1922707
theorem B958009 : Blo 397767 958009 := bstep (se 2 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 958009 = 718507) B718507
theorem B400959 : Blo 397767 400959 := bstep (se 1 (by rfl) ⟨300719, by rfl⟩ : syracuseStep 400959 = 601439) B601439
theorem B400967 : Blo 397767 400967 := bstep (se 1 (by rfl) ⟨300725, by rfl⟩ : syracuseStep 400967 = 601451) B601451
theorem B597599 : Blo 397767 597599 := bstep (se 1 (by rfl) ⟨448199, by rfl⟩ : syracuseStep 597599 = 896399) B896399
theorem B401119 : Blo 397767 401119 := bstep (se 1 (by rfl) ⟨300839, by rfl⟩ : syracuseStep 401119 = 601679) B601679
theorem B1351403 : Blo 397767 1351403 := bstep (se 1 (by rfl) ⟨1013552, by rfl⟩ : syracuseStep 1351403 = 2027105) B2027105
theorem B401199 : Blo 397767 401199 := bstep (se 1 (by rfl) ⟨300899, by rfl⟩ : syracuseStep 401199 = 601799) B601799
theorem B597815 : Blo 397767 597815 := bstep (se 1 (by rfl) ⟨448361, by rfl⟩ : syracuseStep 597815 = 896723) B896723
theorem B401307 : Blo 397767 401307 := bstep (se 1 (by rfl) ⟨300980, by rfl⟩ : syracuseStep 401307 = 601961) B601961
theorem B401359 : Blo 397767 401359 := bstep (se 1 (by rfl) ⟨301019, by rfl⟩ : syracuseStep 401359 = 602039) B602039
theorem B401383 : Blo 397767 401383 := bstep (se 1 (by rfl) ⟨301037, by rfl⟩ : syracuseStep 401383 = 602075) B602075
theorem B598121 : Blo 397767 598121 := bstep (se 2 (by rfl) ⟨224295, by rfl⟩ : syracuseStep 598121 = 448591) B448591
theorem B4301009 : Blo 397767 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2433235 : Blo 397767 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B401695 : Blo 397767 401695 := bstep (se 1 (by rfl) ⟨301271, by rfl⟩ : syracuseStep 401695 = 602543) B602543
theorem B401755 : Blo 397767 401755 := bstep (se 1 (by rfl) ⟨301316, by rfl⟩ : syracuseStep 401755 = 602633) B602633
theorem B762223 : Blo 397767 762223 := bstep (se 1 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 762223 = 1143335) B1143335
theorem B598439 : Blo 397767 598439 := bstep (se 1 (by rfl) ⟨448829, by rfl⟩ : syracuseStep 598439 = 897659) B897659
theorem B598523 : Blo 397767 598523 := bstep (se 1 (by rfl) ⟨448892, by rfl⟩ : syracuseStep 598523 = 897785) B897785
theorem B1286675 : Blo 397767 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B598649 : Blo 397767 598649 := bstep (se 2 (by rfl) ⟨224493, by rfl⟩ : syracuseStep 598649 = 448987) B448987
theorem B5120657 : Blo 397767 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B598703 : Blo 397767 598703 := bstep (se 1 (by rfl) ⟨449027, by rfl⟩ : syracuseStep 598703 = 898055) B898055
theorem B1352375 : Blo 397767 1352375 := bstep (se 1 (by rfl) ⟨1014281, by rfl⟩ : syracuseStep 1352375 = 2028563) B2028563
theorem B598751 : Blo 397767 598751 := bstep (se 1 (by rfl) ⟨449063, by rfl⟩ : syracuseStep 598751 = 898127) B898127
theorem B599015 : Blo 397767 599015 := bstep (se 1 (by rfl) ⟨449261, by rfl⟩ : syracuseStep 599015 = 898523) B898523
theorem B599273 : Blo 397767 599273 := bstep (se 2 (by rfl) ⟨224727, by rfl⟩ : syracuseStep 599273 = 449455) B449455
theorem B599327 : Blo 397767 599327 := bstep (se 1 (by rfl) ⟨449495, by rfl⟩ : syracuseStep 599327 = 898991) B898991
theorem B599495 : Blo 397767 599495 := bstep (se 1 (by rfl) ⟨449621, by rfl⟩ : syracuseStep 599495 = 899243) B899243
theorem B2631257 : Blo 397767 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B599849 : Blo 397767 599849 := bstep (se 2 (by rfl) ⟨224943, by rfl⟩ : syracuseStep 599849 = 449887) B449887
theorem B599855 : Blo 397767 599855 := bstep (se 1 (by rfl) ⟨449891, by rfl⟩ : syracuseStep 599855 = 899783) B899783
theorem B3286865 : Blo 397767 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B1517399 : Blo 397767 1517399 := bstep (se 1 (by rfl) ⟨1138049, by rfl⟩ : syracuseStep 1517399 = 2276099) B2276099
theorem B2893751 : Blo 397767 2893751 := bstep (se 1 (by rfl) ⟨2170313, by rfl⟩ : syracuseStep 2893751 = 4340627) B4340627
theorem B600329 : Blo 397767 600329 := bstep (se 2 (by rfl) ⟨225123, by rfl⟩ : syracuseStep 600329 = 450247) B450247
theorem B600431 : Blo 397767 600431 := bstep (se 1 (by rfl) ⟨450323, by rfl⟩ : syracuseStep 600431 = 900647) B900647
theorem B600647 : Blo 397767 600647 := bstep (se 1 (by rfl) ⟨450485, by rfl⟩ : syracuseStep 600647 = 900971) B900971
theorem B1354319 : Blo 397767 1354319 := bstep (se 1 (by rfl) ⟨1015739, by rfl⟩ : syracuseStep 1354319 = 2031479) B2031479
theorem B600683 : Blo 397767 600683 := bstep (se 1 (by rfl) ⟨450512, by rfl⟩ : syracuseStep 600683 = 901025) B901025
theorem B895823 : Blo 397767 895823 := bstep (se 1 (by rfl) ⟨671867, by rfl⟩ : syracuseStep 895823 = 1343735) B1343735
theorem B600911 : Blo 397767 600911 := bstep (se 1 (by rfl) ⟨450683, by rfl⟩ : syracuseStep 600911 = 901367) B901367
theorem B1715087 : Blo 397767 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B3025835 : Blo 397767 3025835 := bstep (se 1 (by rfl) ⟨2269376, by rfl⟩ : syracuseStep 3025835 = 4538753) B4538753
theorem B896039 : Blo 397767 896039 := bstep (se 1 (by rfl) ⟨672029, by rfl⟩ : syracuseStep 896039 = 1344059) B1344059
theorem B896219 : Blo 397767 896219 := bstep (se 1 (by rfl) ⟨672164, by rfl⟩ : syracuseStep 896219 = 1344329) B1344329
theorem B2272475 : Blo 397767 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B3845339 : Blo 397767 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B601307 : Blo 397767 601307 := bstep (se 1 (by rfl) ⟨450980, by rfl⟩ : syracuseStep 601307 = 901961) B901961
theorem B10235159 : Blo 397767 10235159 := bstep (se 1 (by rfl) ⟨7676369, by rfl⟩ : syracuseStep 10235159 = 15352739) B15352739
theorem B568615 : Blo 397767 568615 := bstep (se 1 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 568615 = 852923) B852923
theorem B2895223 : Blo 397767 2895223 := bstep (se 1 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 2895223 = 4342835) B4342835
theorem B601481 : Blo 397767 601481 := bstep (se 2 (by rfl) ⟨225555, by rfl⟩ : syracuseStep 601481 = 451111) B451111
theorem B961931 : Blo 397767 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B896417 : Blo 397767 896417 := bstep (se 2 (by rfl) ⟨336156, by rfl⟩ : syracuseStep 896417 = 672313) B672313
theorem B1912481 : Blo 397767 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B601835 : Blo 397767 601835 := bstep (se 1 (by rfl) ⟨451376, by rfl⟩ : syracuseStep 601835 = 902753) B902753
theorem B1715975 : Blo 397767 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B1355561 : Blo 397767 1355561 := bstep (se 2 (by rfl) ⟨508335, by rfl⟩ : syracuseStep 1355561 = 1016671) B1016671
theorem B503759 : Blo 397767 503759 := bstep (se 1 (by rfl) ⟨377819, by rfl⟩ : syracuseStep 503759 = 755639) B755639
theorem B896975 : Blo 397767 896975 := bstep (se 1 (by rfl) ⟨672731, by rfl⟩ : syracuseStep 896975 = 1345463) B1345463
theorem B602063 : Blo 397767 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B897353 : Blo 397767 897353 := bstep (se 2 (by rfl) ⟨336507, by rfl⟩ : syracuseStep 897353 = 673015) B673015
theorem B897371 : Blo 397767 897371 := bstep (se 1 (by rfl) ⟨673028, by rfl⟩ : syracuseStep 897371 = 1346057) B1346057
theorem B602459 : Blo 397767 602459 := bstep (se 1 (by rfl) ⟨451844, by rfl⟩ : syracuseStep 602459 = 903689) B903689
theorem B962999 : Blo 397767 962999 := bstep (se 1 (by rfl) ⟨722249, by rfl⟩ : syracuseStep 962999 = 1444499) B1444499
theorem B1520147 : Blo 397767 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B8663597 : Blo 397767 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B52081217 : Blo 397767 52081217 := bstep (se 2 (by rfl) ⟨19530456, by rfl⟩ : syracuseStep 52081217 = 39060913) B39060913
theorem B4338461 : Blo 397767 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B504731 : Blo 397767 504731 := bstep (se 1 (by rfl) ⟨378548, by rfl⟩ : syracuseStep 504731 = 757097) B757097
theorem B897947 : Blo 397767 897947 := bstep (se 1 (by rfl) ⟨673460, by rfl⟩ : syracuseStep 897947 = 1346921) B1346921
theorem B1520603 : Blo 397767 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B898145 : Blo 397767 898145 := bstep (se 2 (by rfl) ⟨336804, by rfl⟩ : syracuseStep 898145 = 673609) B673609
theorem B898343 : Blo 397767 898343 := bstep (se 1 (by rfl) ⟨673757, by rfl⟩ : syracuseStep 898343 = 1347515) B1347515
theorem B3421835 : Blo 397767 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B898721 : Blo 397767 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B899081 : Blo 397767 899081 := bstep (se 2 (by rfl) ⟨337155, by rfl⟩ : syracuseStep 899081 = 674311) B674311
theorem B899495 : Blo 397767 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B899603 : Blo 397767 899603 := bstep (se 1 (by rfl) ⟨674702, by rfl⟩ : syracuseStep 899603 = 1349405) B1349405
theorem B899657 : Blo 397767 899657 := bstep (se 2 (by rfl) ⟨337371, by rfl⟩ : syracuseStep 899657 = 674743) B674743
theorem B16366211 : Blo 397767 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B7289477 : Blo 397767 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B5782427 : Blo 397767 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B16694191 : Blo 397767 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B900071 : Blo 397767 900071 := bstep (se 1 (by rfl) ⟨675053, by rfl⟩ : syracuseStep 900071 = 1350107) B1350107
theorem B7781669 : Blo 397767 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B900449 : Blo 397767 900449 := bstep (se 2 (by rfl) ⟨337668, by rfl⟩ : syracuseStep 900449 = 675337) B675337
theorem B1523063 : Blo 397767 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B900539 : Blo 397767 900539 := bstep (se 1 (by rfl) ⟨675404, by rfl⟩ : syracuseStep 900539 = 1350809) B1350809
theorem B900665 : Blo 397767 900665 := bstep (se 2 (by rfl) ⟨337749, by rfl⟩ : syracuseStep 900665 = 675499) B675499
theorem B2014955 : Blo 397767 2014955 := bstep (se 1 (by rfl) ⟨1511216, by rfl⟩ : syracuseStep 2014955 = 3022433) B3022433
theorem B507703 : Blo 397767 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B2015441 : Blo 397767 2015441 := bstep (se 2 (by rfl) ⟨755790, by rfl⟩ : syracuseStep 2015441 = 1511581) B1511581
theorem B901331 : Blo 397767 901331 := bstep (se 1 (by rfl) ⟨675998, by rfl⟩ : syracuseStep 901331 = 1351997) B1351997
theorem B508123 : Blo 397767 508123 := bstep (se 1 (by rfl) ⟨381092, by rfl⟩ : syracuseStep 508123 = 762185) B762185
theorem B901385 : Blo 397767 901385 := bstep (se 2 (by rfl) ⟨338019, by rfl⟩ : syracuseStep 901385 = 676039) B676039
theorem B7258531 : Blo 397767 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B901601 : Blo 397767 901601 := bstep (se 2 (by rfl) ⟨338100, by rfl⟩ : syracuseStep 901601 = 676201) B676201
theorem B8667749 : Blo 397767 8667749 := bstep (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) B1625203
theorem B639595 : Blo 397767 639595 := bstep (se 1 (by rfl) ⟨479696, by rfl⟩ : syracuseStep 639595 = 959393) B959393
theorem B2015927 : Blo 397767 2015927 := bstep (se 1 (by rfl) ⟨1511945, by rfl⟩ : syracuseStep 2015927 = 3023891) B3023891
theorem B8602361 : Blo 397767 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B901907 : Blo 397767 901907 := bstep (se 1 (by rfl) ⟨676430, by rfl⟩ : syracuseStep 901907 = 1352861) B1352861
theorem B475951 : Blo 397767 475951 := bstep (se 1 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 475951 = 713927) B713927
theorem B902267 : Blo 397767 902267 := bstep (se 1 (by rfl) ⟨676700, by rfl⟩ : syracuseStep 902267 = 1353401) B1353401
theorem B2016413 : Blo 397767 2016413 := bstep (se 3 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 2016413 = 756155) B756155
theorem B902393 : Blo 397767 902393 := bstep (se 2 (by rfl) ⟨338397, by rfl⟩ : syracuseStep 902393 = 676795) B676795
theorem B902537 : Blo 397767 902537 := bstep (se 2 (by rfl) ⟨338451, by rfl⟩ : syracuseStep 902537 = 676903) B676903
theorem B902663 : Blo 397767 902663 := bstep (se 1 (by rfl) ⟨676997, by rfl⟩ : syracuseStep 902663 = 1353995) B1353995
theorem B2180645 : Blo 397767 2180645 := bstep (se 4 (by rfl) ⟨204435, by rfl⟩ : syracuseStep 2180645 = 408871) B408871
theorem B902843 : Blo 397767 902843 := bstep (se 1 (by rfl) ⟨677132, by rfl⟩ : syracuseStep 902843 = 1354265) B1354265
theorem B902969 : Blo 397767 902969 := bstep (se 2 (by rfl) ⟨338613, by rfl⟩ : syracuseStep 902969 = 677227) B677227
theorem B5851217 : Blo 397767 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B12503285 : Blo 397767 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B26364149 : Blo 397767 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B1296751 : Blo 397767 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B2017709 : Blo 397767 2017709 := bstep (se 3 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 2017709 = 756641) B756641
theorem B903599 : Blo 397767 903599 := bstep (se 1 (by rfl) ⟨677699, by rfl⟩ : syracuseStep 903599 = 1355399) B1355399
theorem B903635 : Blo 397767 903635 := bstep (se 1 (by rfl) ⟨677726, by rfl⟩ : syracuseStep 903635 = 1355453) B1355453
theorem B903743 : Blo 397767 903743 := bstep (se 1 (by rfl) ⟨677807, by rfl⟩ : syracuseStep 903743 = 1355615) B1355615
theorem B1133129 : Blo 397767 1133129 := bstep (se 2 (by rfl) ⟨424923, by rfl⟩ : syracuseStep 1133129 = 849847) B849847
theorem B2017871 : Blo 397767 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B903851 : Blo 397767 903851 := bstep (se 1 (by rfl) ⟨677888, by rfl⟩ : syracuseStep 903851 = 1355777) B1355777
theorem B674527 : Blo 397767 674527 := bstep (se 1 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 674527 = 1011791) B1011791
theorem B2608043 : Blo 397767 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B1625075 : Blo 397767 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B3296333 : Blo 397767 3296333 := bstep (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) B1236125
theorem B674959 : Blo 397767 674959 := bstep (se 1 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 674959 = 1012439) B1012439
theorem B8801459 : Blo 397767 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B1920323 : Blo 397767 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B675209 : Blo 397767 675209 := bstep (se 2 (by rfl) ⟨253203, by rfl⟩ : syracuseStep 675209 = 506407) B506407
theorem B5459345 : Blo 397767 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B675641 : Blo 397767 675641 := bstep (se 2 (by rfl) ⟨253365, by rfl⟩ : syracuseStep 675641 = 506731) B506731
theorem B577487 : Blo 397767 577487 := bstep (se 1 (by rfl) ⟨433115, by rfl⟩ : syracuseStep 577487 = 866231) B866231
theorem B2019329 : Blo 397767 2019329 := bstep (se 2 (by rfl) ⟨757248, by rfl⟩ : syracuseStep 2019329 = 1514497) B1514497
theorem B1134803 : Blo 397767 1134803 := bstep (se 1 (by rfl) ⟨851102, by rfl⟩ : syracuseStep 1134803 = 1702205) B1702205
theorem B8606087 : Blo 397767 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B807607 : Blo 397767 807607 := bstep (se 1 (by rfl) ⟨605705, by rfl⟩ : syracuseStep 807607 = 1211411) B1211411
theorem B479927 : Blo 397767 479927 := bstep (se 1 (by rfl) ⟨359945, by rfl⟩ : syracuseStep 479927 = 719891) B719891
theorem B2020139 : Blo 397767 2020139 := bstep (se 1 (by rfl) ⟨1515104, by rfl⟩ : syracuseStep 2020139 = 3030209) B3030209
theorem B676687 : Blo 397767 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B3298157 : Blo 397767 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B1823683 : Blo 397767 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B2741201 : Blo 397767 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B447835 : Blo 397767 447835 := bstep (se 1 (by rfl) ⟨335876, by rfl⟩ : syracuseStep 447835 = 671753) B671753
theorem B25974179 : Blo 397767 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B447943 : Blo 397767 447943 := bstep (se 1 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 447943 = 671915) B671915
theorem B677369 : Blo 397767 677369 := bstep (se 2 (by rfl) ⟨254013, by rfl⟩ : syracuseStep 677369 = 508027) B508027
theorem B677639 : Blo 397767 677639 := bstep (se 1 (by rfl) ⟨508229, by rfl⟩ : syracuseStep 677639 = 1016459) B1016459
theorem B448303 : Blo 397767 448303 := bstep (se 1 (by rfl) ⟨336227, by rfl⟩ : syracuseStep 448303 = 672455) B672455
theorem B448411 : Blo 397767 448411 := bstep (se 1 (by rfl) ⟨336308, by rfl⟩ : syracuseStep 448411 = 672617) B672617
theorem B448807 : Blo 397767 448807 := bstep (se 1 (by rfl) ⟨336605, by rfl⟩ : syracuseStep 448807 = 673211) B673211
theorem B448879 : Blo 397767 448879 := bstep (se 1 (by rfl) ⟨336659, by rfl⟩ : syracuseStep 448879 = 673319) B673319
theorem B809327 : Blo 397767 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B6805943 : Blo 397767 6805943 := bstep (se 1 (by rfl) ⟨5104457, by rfl⟩ : syracuseStep 6805943 = 10208915) B10208915
theorem B809441 : Blo 397767 809441 := bstep (se 2 (by rfl) ⟨303540, by rfl⟩ : syracuseStep 809441 = 607081) B607081
theorem B449095 : Blo 397767 449095 := bstep (se 1 (by rfl) ⟨336821, by rfl⟩ : syracuseStep 449095 = 673643) B673643
theorem B2284139 : Blo 397767 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B2022083 : Blo 397767 2022083 := bstep (se 1 (by rfl) ⟨1516562, by rfl⟩ : syracuseStep 2022083 = 3033125) B3033125
theorem B2317501 : Blo 397767 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B3431645 : Blo 397767 3431645 := bstep (se 3 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 3431645 = 1286867) B1286867
theorem B449959 : Blo 397767 449959 := bstep (se 1 (by rfl) ⟨337469, by rfl⟩ : syracuseStep 449959 = 674939) B674939
theorem B1007063 : Blo 397767 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B1007417 : Blo 397767 1007417 := bstep (se 2 (by rfl) ⟨377781, by rfl⟩ : syracuseStep 1007417 = 755563) B755563
theorem B1924937 : Blo 397767 1924937 := bstep (se 2 (by rfl) ⟨721851, by rfl⟩ : syracuseStep 1924937 = 1443703) B1443703
theorem B450535 : Blo 397767 450535 := bstep (se 1 (by rfl) ⟨337901, by rfl⟩ : syracuseStep 450535 = 675803) B675803
theorem B3039443 : Blo 397767 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B2285779 : Blo 397767 2285779 := bstep (se 1 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 2285779 = 3428669) B3428669
theorem B1139017 : Blo 397767 1139017 := bstep (se 2 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 1139017 = 854263) B854263
theorem B1303847 : Blo 397767 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1009057 : Blo 397767 1009057 := bstep (se 2 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 1009057 = 756793) B756793
theorem B910931 : Blo 397767 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B1730807 : Blo 397767 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B2025971 : Blo 397767 2025971 := bstep (se 1 (by rfl) ⟨1519478, by rfl⟩ : syracuseStep 2025971 = 3038957) B3038957
theorem B1010171 : Blo 397767 1010171 := bstep (se 1 (by rfl) ⟨757628, by rfl⟩ : syracuseStep 1010171 = 1515257) B1515257
theorem B1075987 : Blo 397767 1075987 := bstep (se 1 (by rfl) ⟨806990, by rfl⟩ : syracuseStep 1075987 = 1613981) B1613981
theorem B1141523 : Blo 397767 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B2026619 : Blo 397767 2026619 := bstep (se 1 (by rfl) ⟨1519964, by rfl⟩ : syracuseStep 2026619 = 3039929) B3039929
theorem B1011143 : Blo 397767 1011143 := bstep (se 1 (by rfl) ⟨758357, by rfl⟩ : syracuseStep 1011143 = 1516715) B1516715
theorem B2158289 : Blo 397767 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B2027267 : Blo 397767 2027267 := bstep (se 1 (by rfl) ⟨1520450, by rfl⟩ : syracuseStep 2027267 = 3040901) B3040901
theorem B1929089 : Blo 397767 1929089 := bstep (se 2 (by rfl) ⟨723408, by rfl⟩ : syracuseStep 1929089 = 1446817) B1446817
theorem B3239837 : Blo 397767 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B3502081 : Blo 397767 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B913513 : Blo 397767 913513 := bstep (se 2 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 913513 = 685135) B685135
theorem B1011923 : Blo 397767 1011923 := bstep (se 1 (by rfl) ⟨758942, by rfl⟩ : syracuseStep 1011923 = 1517885) B1517885
theorem B1012135 : Blo 397767 1012135 := bstep (se 1 (by rfl) ⟨759101, by rfl⟩ : syracuseStep 1012135 = 1518203) B1518203
theorem B3404339 : Blo 397767 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B1012297 : Blo 397767 1012297 := bstep (se 2 (by rfl) ⟨379611, by rfl⟩ : syracuseStep 1012297 = 759223) B759223
theorem B7468081 : Blo 397767 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B1144007 : Blo 397767 1144007 := bstep (se 1 (by rfl) ⟨858005, by rfl⟩ : syracuseStep 1144007 = 1716011) B1716011
theorem B2028887 : Blo 397767 2028887 := bstep (se 1 (by rfl) ⟨1521665, by rfl⟩ : syracuseStep 2028887 = 3043331) B3043331
theorem B1013087 : Blo 397767 1013087 := bstep (se 1 (by rfl) ⟨759815, by rfl⟩ : syracuseStep 1013087 = 1519631) B1519631
theorem B7665299 : Blo 397767 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B2029697 : Blo 397767 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B1210621 : Blo 397767 1210621 := bstep (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) B453983
theorem B719113 : Blo 397767 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B850351 : Blo 397767 850351 := bstep (se 1 (by rfl) ⟨637763, by rfl⟩ : syracuseStep 850351 = 1275527) B1275527
theorem B1014191 : Blo 397767 1014191 := bstep (se 1 (by rfl) ⟨760643, by rfl⟩ : syracuseStep 1014191 = 1521287) B1521287
theorem B1014241 : Blo 397767 1014241 := bstep (se 2 (by rfl) ⟨380340, by rfl⟩ : syracuseStep 1014241 = 760681) B760681
theorem B1276411 : Blo 397767 1276411 := bstep (se 1 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 1276411 = 1914617) B1914617
theorem B3832343 : Blo 397767 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B424859 : Blo 397767 424859 := bstep (se 1 (by rfl) ⟨318644, by rfl⟩ : syracuseStep 424859 = 637289) B637289
theorem B2030507 : Blo 397767 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B851239 : Blo 397767 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B55639385 : Blo 397767 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B1342817 : Blo 397767 1342817 := bstep (se 2 (by rfl) ⟨503556, by rfl⟩ : syracuseStep 1342817 = 1007113) B1007113
theorem B1015163 : Blo 397767 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B24641171 : Blo 397767 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B3833729 : Blo 397767 3833729 := bstep (se 2 (by rfl) ⟨1437648, by rfl⟩ : syracuseStep 3833729 = 2875297) B2875297
theorem B18677765 : Blo 397767 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B1343627 : Blo 397767 1343627 := bstep (se 1 (by rfl) ⟨1007720, by rfl⟩ : syracuseStep 1343627 = 2015441) B2015441
theorem B3244313 : Blo 397767 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B3047705 : Blo 397767 3047705 := bstep (se 2 (by rfl) ⟨1142889, by rfl⟩ : syracuseStep 3047705 = 2285779) B2285779
theorem B1343951 : Blo 397767 1343951 := bstep (se 1 (by rfl) ⟨1007963, by rfl⟩ : syracuseStep 1343951 = 2015927) B2015927
theorem B1016297 : Blo 397767 1016297 := bstep (se 2 (by rfl) ⟨381111, by rfl⟩ : syracuseStep 1016297 = 762223) B762223
theorem B5734907 : Blo 397767 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B2163307 : Blo 397767 2163307 := bstep (se 1 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 2163307 = 3244961) B3244961
theorem B1344275 : Blo 397767 1344275 := bstep (se 1 (by rfl) ⟨1008206, by rfl⟩ : syracuseStep 1344275 = 2016413) B2016413
theorem B3900811 : Blo 397767 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1345139 : Blo 397767 1345139 := bstep (se 1 (by rfl) ⟨1008854, by rfl⟩ : syracuseStep 1345139 = 2017709) B2017709
theorem B755419 : Blo 397767 755419 := bstep (se 1 (by rfl) ⟨566564, by rfl⟩ : syracuseStep 755419 = 1133129) B1133129
theorem B1345247 : Blo 397767 1345247 := bstep (se 1 (by rfl) ⟨1008935, by rfl⟩ : syracuseStep 1345247 = 2017871) B2017871
theorem B1279805 : Blo 397767 1279805 := bstep (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) B479927
theorem B1967951 : Blo 397767 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B1345409 : Blo 397767 1345409 := bstep (se 2 (by rfl) ⟨504528, by rfl⟩ : syracuseStep 1345409 = 1009057) B1009057
theorem B1083383 : Blo 397767 1083383 := bstep (se 1 (by rfl) ⟨812537, by rfl⟩ : syracuseStep 1083383 = 1625075) B1625075
theorem B11569229 : Blo 397767 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B5867639 : Blo 397767 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1280215 : Blo 397767 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B3639563 : Blo 397767 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B723323 : Blo 397767 723323 := bstep (se 1 (by rfl) ⟨542492, by rfl⟩ : syracuseStep 723323 = 1084985) B1084985
theorem B1345949 : Blo 397767 1345949 := bstep (se 3 (by rfl) ⟨252365, by rfl⟩ : syracuseStep 1345949 = 504731) B504731
theorem B1346219 : Blo 397767 1346219 := bstep (se 1 (by rfl) ⟨1009664, by rfl⟩ : syracuseStep 1346219 = 2019329) B2019329
theorem B756535 : Blo 397767 756535 := bstep (se 1 (by rfl) ⟨567401, by rfl⟩ : syracuseStep 756535 = 1134803) B1134803
theorem B5737391 : Blo 397767 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B1346759 : Blo 397767 1346759 := bstep (se 1 (by rfl) ⟨1010069, by rfl⟩ : syracuseStep 1346759 = 2020139) B2020139
theorem B3411173 : Blo 397767 3411173 := bstep (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) B639595
theorem B2198771 : Blo 397767 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B5738597 : Blo 397767 5738597 := bstep (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) B1075987
theorem B1446011 : Blo 397767 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B7671995 : Blo 397767 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B2429149 : Blo 397767 2429149 := bstep (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) B910931
theorem B758153 : Blo 397767 758153 := bstep (se 2 (by rfl) ⟨284307, by rfl⟩ : syracuseStep 758153 = 568615) B568615
theorem B397775 : Blo 397767 397775 := bstep (se 1 (by rfl) ⟨298331, by rfl⟩ : syracuseStep 397775 = 596663) B596663
theorem B1348055 : Blo 397767 1348055 := bstep (se 1 (by rfl) ⟨1011041, by rfl⟩ : syracuseStep 1348055 = 2022083) B2022083
theorem B2167283 : Blo 397767 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B397927 : Blo 397767 397927 := bstep (se 1 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 397927 = 596891) B596891
theorem B3937085 : Blo 397767 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B1708867 : Blo 397767 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B398191 : Blo 397767 398191 := bstep (se 1 (by rfl) ⟨298643, by rfl⟩ : syracuseStep 398191 = 597287) B597287
theorem B398247 : Blo 397767 398247 := bstep (se 1 (by rfl) ⟨298685, by rfl⟩ : syracuseStep 398247 = 597371) B597371
theorem B398331 : Blo 397767 398331 := bstep (se 1 (by rfl) ⟨298748, by rfl⟩ : syracuseStep 398331 = 597497) B597497
theorem B398399 : Blo 397767 398399 := bstep (se 1 (by rfl) ⟨298799, by rfl⟩ : syracuseStep 398399 = 597599) B597599
theorem B9311377 : Blo 397767 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B398543 : Blo 397767 398543 := bstep (se 1 (by rfl) ⟨298907, by rfl⟩ : syracuseStep 398543 = 597815) B597815
theorem B1283291 : Blo 397767 1283291 := bstep (se 1 (by rfl) ⟨962468, by rfl⟩ : syracuseStep 1283291 = 1924937) B1924937
theorem B398747 : Blo 397767 398747 := bstep (se 1 (by rfl) ⟨299060, by rfl⟩ : syracuseStep 398747 = 598121) B598121
theorem B1218017 : Blo 397767 1218017 := bstep (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) B913513
theorem B398959 : Blo 397767 398959 := bstep (se 1 (by rfl) ⟨299219, by rfl⟩ : syracuseStep 398959 = 598439) B598439
theorem B399015 : Blo 397767 399015 := bstep (se 1 (by rfl) ⟨299261, by rfl⟩ : syracuseStep 399015 = 598523) B598523
theorem B857783 : Blo 397767 857783 := bstep (se 1 (by rfl) ⟨643337, by rfl⟩ : syracuseStep 857783 = 1286675) B1286675
theorem B399099 : Blo 397767 399099 := bstep (se 1 (by rfl) ⟨299324, by rfl⟩ : syracuseStep 399099 = 598649) B598649
theorem B3413771 : Blo 397767 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B399135 : Blo 397767 399135 := bstep (se 1 (by rfl) ⟨299351, by rfl⟩ : syracuseStep 399135 = 598703) B598703
theorem B399167 : Blo 397767 399167 := bstep (se 1 (by rfl) ⟨299375, by rfl⟩ : syracuseStep 399167 = 598751) B598751
theorem B1349513 : Blo 397767 1349513 := bstep (se 2 (by rfl) ⟨506067, by rfl⟩ : syracuseStep 1349513 = 1012135) B1012135
theorem B399343 : Blo 397767 399343 := bstep (se 1 (by rfl) ⟨299507, by rfl⟩ : syracuseStep 399343 = 599015) B599015
theorem B1349729 : Blo 397767 1349729 := bstep (se 2 (by rfl) ⟨506148, by rfl⟩ : syracuseStep 1349729 = 1012297) B1012297
theorem B399515 : Blo 397767 399515 := bstep (se 1 (by rfl) ⟨299636, by rfl⟩ : syracuseStep 399515 = 599273) B599273
theorem B399551 : Blo 397767 399551 := bstep (se 1 (by rfl) ⟨299663, by rfl⟩ : syracuseStep 399551 = 599327) B599327
theorem B399663 : Blo 397767 399663 := bstep (se 1 (by rfl) ⟨299747, by rfl⟩ : syracuseStep 399663 = 599495) B599495
theorem B399899 : Blo 397767 399899 := bstep (se 1 (by rfl) ⟨299924, by rfl⟩ : syracuseStep 399899 = 599849) B599849
theorem B399903 : Blo 397767 399903 := bstep (se 1 (by rfl) ⟨299927, by rfl⟩ : syracuseStep 399903 = 599855) B599855
theorem B2431577 : Blo 397767 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B1710713 : Blo 397767 1710713 := bstep (se 2 (by rfl) ⟨641517, by rfl⟩ : syracuseStep 1710713 = 1283035) B1283035
theorem B1153871 : Blo 397767 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B400219 : Blo 397767 400219 := bstep (se 1 (by rfl) ⟨300164, by rfl⟩ : syracuseStep 400219 = 600329) B600329
theorem B1710953 : Blo 397767 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B400287 : Blo 397767 400287 := bstep (se 1 (by rfl) ⟨300215, by rfl⟩ : syracuseStep 400287 = 600431) B600431
theorem B2104301 : Blo 397767 2104301 := bstep (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) B789113
theorem B1350647 : Blo 397767 1350647 := bstep (se 1 (by rfl) ⟨1012985, by rfl⟩ : syracuseStep 1350647 = 2025971) B2025971
theorem B400431 : Blo 397767 400431 := bstep (se 1 (by rfl) ⟨300323, by rfl⟩ : syracuseStep 400431 = 600647) B600647
theorem B400455 : Blo 397767 400455 := bstep (se 1 (by rfl) ⟨300341, by rfl⟩ : syracuseStep 400455 = 600683) B600683
theorem B597113 : Blo 397767 597113 := bstep (se 2 (by rfl) ⟨223917, by rfl⟩ : syracuseStep 597113 = 447835) B447835
theorem B761015 : Blo 397767 761015 := bstep (se 1 (by rfl) ⟨570761, by rfl⟩ : syracuseStep 761015 = 1141523) B1141523
theorem B597215 : Blo 397767 597215 := bstep (se 1 (by rfl) ⟨447911, by rfl⟩ : syracuseStep 597215 = 895823) B895823
theorem B400607 : Blo 397767 400607 := bstep (se 1 (by rfl) ⟨300455, by rfl⟩ : syracuseStep 400607 = 600911) B600911
theorem B597257 : Blo 397767 597257 := bstep (se 2 (by rfl) ⟨223971, by rfl⟩ : syracuseStep 597257 = 447943) B447943
theorem B597359 : Blo 397767 597359 := bstep (se 1 (by rfl) ⟨448019, by rfl⟩ : syracuseStep 597359 = 896039) B896039
theorem B1351079 : Blo 397767 1351079 := bstep (se 1 (by rfl) ⟨1013309, by rfl⟩ : syracuseStep 1351079 = 2026619) B2026619
theorem B597479 : Blo 397767 597479 := bstep (se 1 (by rfl) ⟨448109, by rfl⟩ : syracuseStep 597479 = 896219) B896219
theorem B1514983 : Blo 397767 1514983 := bstep (se 1 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 1514983 = 2272475) B2272475
theorem B2563559 : Blo 397767 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B400871 : Blo 397767 400871 := bstep (se 1 (by rfl) ⟨300653, by rfl⟩ : syracuseStep 400871 = 601307) B601307
theorem B6823439 : Blo 397767 6823439 := bstep (se 1 (by rfl) ⟨5117579, by rfl⟩ : syracuseStep 6823439 = 10235159) B10235159
theorem B400987 : Blo 397767 400987 := bstep (se 1 (by rfl) ⟨300740, by rfl⟩ : syracuseStep 400987 = 601481) B601481
theorem B597611 : Blo 397767 597611 := bstep (se 1 (by rfl) ⟨448208, by rfl⟩ : syracuseStep 597611 = 896417) B896417
theorem B597737 : Blo 397767 597737 := bstep (se 2 (by rfl) ⟨224151, by rfl⟩ : syracuseStep 597737 = 448303) B448303
theorem B6954781 : Blo 397767 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B401223 : Blo 397767 401223 := bstep (se 1 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 401223 = 601835) B601835
theorem B1351511 : Blo 397767 1351511 := bstep (se 1 (by rfl) ⟨1013633, by rfl⟩ : syracuseStep 1351511 = 2027267) B2027267
theorem B597881 : Blo 397767 597881 := bstep (se 2 (by rfl) ⟨224205, by rfl⟩ : syracuseStep 597881 = 448411) B448411
theorem B1286059 : Blo 397767 1286059 := bstep (se 1 (by rfl) ⟨964544, by rfl⟩ : syracuseStep 1286059 = 1929089) B1929089
theorem B597983 : Blo 397767 597983 := bstep (se 1 (by rfl) ⟨448487, by rfl⟩ : syracuseStep 597983 = 896975) B896975
theorem B401375 : Blo 397767 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B8790221 : Blo 397767 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B598235 : Blo 397767 598235 := bstep (se 1 (by rfl) ⟨448676, by rfl⟩ : syracuseStep 598235 = 897353) B897353
theorem B598247 : Blo 397767 598247 := bstep (se 1 (by rfl) ⟨448685, by rfl⟩ : syracuseStep 598247 = 897371) B897371
theorem B401639 : Blo 397767 401639 := bstep (se 1 (by rfl) ⟨301229, by rfl⟩ : syracuseStep 401639 = 602459) B602459
theorem B1614161 : Blo 397767 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B958817 : Blo 397767 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B5775731 : Blo 397767 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B2269559 : Blo 397767 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B598409 : Blo 397767 598409 := bstep (se 2 (by rfl) ⟨224403, by rfl⟩ : syracuseStep 598409 = 448807) B448807
theorem B598505 : Blo 397767 598505 := bstep (se 2 (by rfl) ⟨224439, by rfl⟩ : syracuseStep 598505 = 448879) B448879
theorem B598631 : Blo 397767 598631 := bstep (se 1 (by rfl) ⟨448973, by rfl⟩ : syracuseStep 598631 = 897947) B897947
theorem B1352321 : Blo 397767 1352321 := bstep (se 2 (by rfl) ⟨507120, by rfl⟩ : syracuseStep 1352321 = 1014241) B1014241
theorem B598763 : Blo 397767 598763 := bstep (se 1 (by rfl) ⟨449072, by rfl⟩ : syracuseStep 598763 = 898145) B898145
theorem B598793 : Blo 397767 598793 := bstep (se 2 (by rfl) ⟨224547, by rfl⟩ : syracuseStep 598793 = 449095) B449095
theorem B762671 : Blo 397767 762671 := bstep (se 1 (by rfl) ⟨572003, by rfl⟩ : syracuseStep 762671 = 1144007) B1144007
theorem B598895 : Blo 397767 598895 := bstep (se 1 (by rfl) ⟨449171, by rfl⟩ : syracuseStep 598895 = 898343) B898343
theorem B1352591 : Blo 397767 1352591 := bstep (se 1 (by rfl) ⟨1014443, by rfl⟩ : syracuseStep 1352591 = 2028887) B2028887
theorem B599147 : Blo 397767 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B22258921 : Blo 397767 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B599387 : Blo 397767 599387 := bstep (se 1 (by rfl) ⟨449540, by rfl⟩ : syracuseStep 599387 = 899081) B899081
theorem B1353131 : Blo 397767 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B3024377 : Blo 397767 3024377 := bstep (se 2 (by rfl) ⟨1134141, by rfl⟩ : syracuseStep 3024377 = 2268283) B2268283
theorem B3090001 : Blo 397767 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B599663 : Blo 397767 599663 := bstep (se 1 (by rfl) ⟨449747, by rfl⟩ : syracuseStep 599663 = 899495) B899495
theorem B599735 : Blo 397767 599735 := bstep (se 1 (by rfl) ⟨449801, by rfl⟩ : syracuseStep 599735 = 899603) B899603
theorem B599771 : Blo 397767 599771 := bstep (se 1 (by rfl) ⟨449828, by rfl⟩ : syracuseStep 599771 = 899657) B899657
theorem B4859651 : Blo 397767 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B599945 : Blo 397767 599945 := bstep (se 2 (by rfl) ⟨224979, by rfl⟩ : syracuseStep 599945 = 449959) B449959
theorem B1353671 : Blo 397767 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B600047 : Blo 397767 600047 := bstep (se 1 (by rfl) ⟨450035, by rfl⟩ : syracuseStep 600047 = 900071) B900071
theorem B3418145 : Blo 397767 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B5187779 : Blo 397767 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B895211 : Blo 397767 895211 := bstep (se 1 (by rfl) ⟨671408, by rfl⟩ : syracuseStep 895211 = 1342817) B1342817
theorem B600299 : Blo 397767 600299 := bstep (se 1 (by rfl) ⟨450224, by rfl⟩ : syracuseStep 600299 = 900449) B900449
theorem B600359 : Blo 397767 600359 := bstep (se 1 (by rfl) ⟨450269, by rfl⟩ : syracuseStep 600359 = 900539) B900539
theorem B600443 : Blo 397767 600443 := bstep (se 1 (by rfl) ⟨450332, by rfl⟩ : syracuseStep 600443 = 900665) B900665
theorem B16427447 : Blo 397767 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B600713 : Blo 397767 600713 := bstep (se 2 (by rfl) ⟨225267, by rfl⟩ : syracuseStep 600713 = 450535) B450535
theorem B1354427 : Blo 397767 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B600887 : Blo 397767 600887 := bstep (se 1 (by rfl) ⟨450665, by rfl⟩ : syracuseStep 600887 = 901331) B901331
theorem B600923 : Blo 397767 600923 := bstep (se 1 (by rfl) ⟨450692, by rfl⟩ : syracuseStep 600923 = 901385) B901385
theorem B601067 : Blo 397767 601067 := bstep (se 1 (by rfl) ⟨450800, by rfl⟩ : syracuseStep 601067 = 901601) B901601
theorem B5778499 : Blo 397767 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B1518689 : Blo 397767 1518689 := bstep (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) B1139017
theorem B8170631 : Blo 397767 8170631 := bstep (se 1 (by rfl) ⟨6127973, by rfl⟩ : syracuseStep 8170631 = 12255947) B12255947
theorem B601271 : Blo 397767 601271 := bstep (se 1 (by rfl) ⟨450953, by rfl⟩ : syracuseStep 601271 = 901907) B901907
theorem B9678041 : Blo 397767 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B601511 : Blo 397767 601511 := bstep (se 1 (by rfl) ⟨451133, by rfl⟩ : syracuseStep 601511 = 902267) B902267
theorem B896507 : Blo 397767 896507 := bstep (se 1 (by rfl) ⟨672380, by rfl⟩ : syracuseStep 896507 = 1344761) B1344761
theorem B601595 : Blo 397767 601595 := bstep (se 1 (by rfl) ⟨451196, by rfl⟩ : syracuseStep 601595 = 902393) B902393
theorem B601691 : Blo 397767 601691 := bstep (se 1 (by rfl) ⟨451268, by rfl⟩ : syracuseStep 601691 = 902537) B902537
theorem B568939 : Blo 397767 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B896687 : Blo 397767 896687 := bstep (se 1 (by rfl) ⟨672515, by rfl⟩ : syracuseStep 896687 = 1345031) B1345031
theorem B601775 : Blo 397767 601775 := bstep (se 1 (by rfl) ⟨451331, by rfl⟩ : syracuseStep 601775 = 902663) B902663
theorem B1453763 : Blo 397767 1453763 := bstep (se 1 (by rfl) ⟨1090322, by rfl⟩ : syracuseStep 1453763 = 2180645) B2180645
theorem B634601 : Blo 397767 634601 := bstep (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) B475951
theorem B601895 : Blo 397767 601895 := bstep (se 1 (by rfl) ⟨451421, by rfl⟩ : syracuseStep 601895 = 902843) B902843
theorem B601979 : Blo 397767 601979 := bstep (se 1 (by rfl) ⟨451484, by rfl⟩ : syracuseStep 601979 = 902969) B902969
theorem B8335523 : Blo 397767 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B17576099 : Blo 397767 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B602399 : Blo 397767 602399 := bstep (se 1 (by rfl) ⟨451799, by rfl⟩ : syracuseStep 602399 = 903599) B903599
theorem B897335 : Blo 397767 897335 := bstep (se 1 (by rfl) ⟨673001, by rfl⟩ : syracuseStep 897335 = 1346003) B1346003
theorem B602423 : Blo 397767 602423 := bstep (se 1 (by rfl) ⟨451817, by rfl⟩ : syracuseStep 602423 = 903635) B903635
theorem B897407 : Blo 397767 897407 := bstep (se 1 (by rfl) ⟨673055, by rfl⟩ : syracuseStep 897407 = 1346111) B1346111
theorem B602495 : Blo 397767 602495 := bstep (se 1 (by rfl) ⟨451871, by rfl⟩ : syracuseStep 602495 = 903743) B903743
theorem B602567 : Blo 397767 602567 := bstep (se 1 (by rfl) ⟨451925, by rfl⟩ : syracuseStep 602567 = 903851) B903851
theorem B2011895 : Blo 397767 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B963353 : Blo 397767 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B767083 : Blo 397767 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B898631 : Blo 397767 898631 := bstep (se 1 (by rfl) ⟨673973, by rfl⟩ : syracuseStep 898631 = 1347947) B1347947
theorem B898811 : Blo 397767 898811 := bstep (se 1 (by rfl) ⟨674108, by rfl⟩ : syracuseStep 898811 = 1348217) B1348217
theorem B2733887 : Blo 397767 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B571627 : Blo 397767 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B17316119 : Blo 397767 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B899369 : Blo 397767 899369 := bstep (se 2 (by rfl) ⟨337263, by rfl⟩ : syracuseStep 899369 = 674527) B674527
theorem B899945 : Blo 397767 899945 := bstep (se 2 (by rfl) ⟨337479, by rfl⟩ : syracuseStep 899945 = 674959) B674959
theorem B539551 : Blo 397767 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B899999 : Blo 397767 899999 := bstep (se 1 (by rfl) ⟨674999, by rfl⟩ : syracuseStep 899999 = 1349999) B1349999
theorem B4537295 : Blo 397767 4537295 := bstep (se 1 (by rfl) ⟨3402971, by rfl⟩ : syracuseStep 4537295 = 6805943) B6805943
theorem B539627 : Blo 397767 539627 := bstep (se 1 (by rfl) ⟨404720, by rfl⟩ : syracuseStep 539627 = 809441) B809441
theorem B3849257 : Blo 397767 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1522759 : Blo 397767 1522759 := bstep (se 1 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 1522759 = 2284139) B2284139
theorem B638135 : Blo 397767 638135 := bstep (se 1 (by rfl) ⟨478601, by rfl⟩ : syracuseStep 638135 = 957203) B957203
theorem B2014631 : Blo 397767 2014631 := bstep (se 1 (by rfl) ⟨1510973, by rfl⟩ : syracuseStep 2014631 = 3021947) B3021947
theorem B8764973 : Blo 397767 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B671375 : Blo 397767 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B900935 : Blo 397767 900935 := bstep (se 1 (by rfl) ⟨675701, by rfl⟩ : syracuseStep 900935 = 1351403) B1351403
theorem B671611 : Blo 397767 671611 := bstep (se 1 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 671611 = 1007417) B1007417
theorem B2867339 : Blo 397767 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B39829765 : Blo 397767 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B901583 : Blo 397767 901583 := bstep (se 1 (by rfl) ⟨676187, by rfl⟩ : syracuseStep 901583 = 1352375) B1352375
theorem B869231 : Blo 397767 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B1754171 : Blo 397767 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B902249 : Blo 397767 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B673447 : Blo 397767 673447 := bstep (se 1 (by rfl) ⟨505085, by rfl⟩ : syracuseStep 673447 = 1010171) B1010171
theorem B902879 : Blo 397767 902879 := bstep (se 1 (by rfl) ⟨677159, by rfl⟩ : syracuseStep 902879 = 1354319) B1354319
theorem B2017223 : Blo 397767 2017223 := bstep (se 1 (by rfl) ⟨1512917, by rfl⟩ : syracuseStep 2017223 = 3025835) B3025835
theorem B641287 : Blo 397767 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B674095 : Blo 397767 674095 := bstep (se 1 (by rfl) ⟨505571, by rfl⟩ : syracuseStep 674095 = 1011143) B1011143
theorem B1132957 : Blo 397767 1132957 := bstep (se 3 (by rfl) ⟨212429, by rfl⟩ : syracuseStep 1132957 = 424859) B424859
theorem B903707 : Blo 397767 903707 := bstep (se 1 (by rfl) ⟨677780, by rfl⟩ : syracuseStep 903707 = 1355561) B1355561
theorem B674615 : Blo 397767 674615 := bstep (se 1 (by rfl) ⟨505961, by rfl⟩ : syracuseStep 674615 = 1011923) B1011923
theorem B641999 : Blo 397767 641999 := bstep (se 1 (by rfl) ⟨481499, by rfl⟩ : syracuseStep 641999 = 962999) B962999
theorem B34720811 : Blo 397767 34720811 := bstep (se 1 (by rfl) ⟨26040608, by rfl⟩ : syracuseStep 34720811 = 52081217) B52081217
theorem B1133801 : Blo 397767 1133801 := bstep (se 2 (by rfl) ⟨425175, by rfl⟩ : syracuseStep 1133801 = 850351) B850351
theorem B675391 : Blo 397767 675391 := bstep (se 1 (by rfl) ⟨506543, by rfl⟩ : syracuseStep 675391 = 1013087) B1013087
theorem B2281223 : Blo 397767 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B676127 : Blo 397767 676127 := bstep (se 1 (by rfl) ⟨507095, by rfl⟩ : syracuseStep 676127 = 1014191) B1014191
theorem B1134985 : Blo 397767 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B3854951 : Blo 397767 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B676775 : Blo 397767 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B676937 : Blo 397767 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B677497 : Blo 397767 677497 := bstep (se 2 (by rfl) ⟨254061, by rfl⟩ : syracuseStep 677497 = 508123) B508123
theorem B3889079 : Blo 397767 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B677983 : Blo 397767 677983 := bstep (se 1 (by rfl) ⟨508487, by rfl⟩ : syracuseStep 677983 = 1016975) B1016975
theorem B1137959 : Blo 397767 1137959 := bstep (se 1 (by rfl) ⟨853469, by rfl⟩ : syracuseStep 1137959 = 1706939) B1706939
theorem B1138151 : Blo 397767 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B450139 : Blo 397767 450139 := bstep (se 1 (by rfl) ⟨337604, by rfl⟩ : syracuseStep 450139 = 675209) B675209
theorem B450427 : Blo 397767 450427 := bstep (se 1 (by rfl) ⟨337820, by rfl⟩ : syracuseStep 450427 = 675641) B675641
theorem B3825883 : Blo 397767 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B1007903 : Blo 397767 1007903 := bstep (se 1 (by rfl) ⟨755927, by rfl⟩ : syracuseStep 1007903 = 1511855) B1511855
theorem B1139143 : Blo 397767 1139143 := bstep (se 1 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 1139143 = 1708715) B1708715
theorem B1729001 : Blo 397767 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B1139177 : Blo 397767 1139177 := bstep (se 2 (by rfl) ⟨427191, by rfl⟩ : syracuseStep 1139177 = 854383) B854383
theorem B1827467 : Blo 397767 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B2024189 : Blo 397767 2024189 := bstep (se 3 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 2024189 = 759071) B759071
theorem B1008551 : Blo 397767 1008551 := bstep (se 1 (by rfl) ⟨756413, by rfl⟩ : syracuseStep 1008551 = 1512827) B1512827
theorem B451579 : Blo 397767 451579 := bstep (se 1 (by rfl) ⟨338684, by rfl⟩ : syracuseStep 451579 = 677369) B677369
theorem B451759 : Blo 397767 451759 := bstep (se 1 (by rfl) ⟨338819, by rfl⟩ : syracuseStep 451759 = 677639) B677639
theorem B3860297 : Blo 397767 3860297 := bstep (se 2 (by rfl) ⟨1447611, by rfl⟩ : syracuseStep 3860297 = 2895223) B2895223
theorem B1009655 : Blo 397767 1009655 := bstep (se 1 (by rfl) ⟨757241, by rfl⟩ : syracuseStep 1009655 = 1514483) B1514483
theorem B2287763 : Blo 397767 2287763 := bstep (se 1 (by rfl) ⟨1715822, by rfl⟩ : syracuseStep 2287763 = 3431645) B3431645
theorem B10971449 : Blo 397767 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B2026295 : Blo 397767 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B1011113 : Blo 397767 1011113 := bstep (se 2 (by rfl) ⟨379167, by rfl⟩ : syracuseStep 1011113 = 758335) B758335
theorem B1076809 : Blo 397767 1076809 := bstep (se 2 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 1076809 = 807607) B807607
theorem B1011599 : Blo 397767 1011599 := bstep (se 1 (by rfl) ⟨758699, by rfl⟩ : syracuseStep 1011599 = 1517399) B1517399
theorem B1929167 : Blo 397767 1929167 := bstep (se 1 (by rfl) ⟨1446875, by rfl⟩ : syracuseStep 1929167 = 2893751) B2893751
theorem B1143391 : Blo 397767 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B1274987 : Blo 397767 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B1438859 : Blo 397767 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B1143983 : Blo 397767 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B2159891 : Blo 397767 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B1013431 : Blo 397767 1013431 := bstep (se 1 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 1013431 = 1520147) B1520147
theorem B1013735 : Blo 397767 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B1701881 : Blo 397767 1701881 := bstep (se 2 (by rfl) ⟨638205, by rfl⟩ : syracuseStep 1701881 = 1276411) B1276411
theorem B5110199 : Blo 397767 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B2554895 : Blo 397767 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B10910807 : Blo 397767 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B1277345 : Blo 397767 1277345 := bstep (se 2 (by rfl) ⟨479004, by rfl⟩ : syracuseStep 1277345 = 958009) B958009
theorem B37092923 : Blo 397767 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B1015375 : Blo 397767 1015375 := bstep (se 1 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 1015375 = 1523063) B1523063
theorem B1343303 : Blo 397767 1343303 := bstep (se 1 (by rfl) ⟨1007477, by rfl⟩ : syracuseStep 1343303 = 2014955) B2014955
theorem B1343357 : Blo 397767 1343357 := bstep (se 3 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 1343357 = 503759) B503759
theorem B1539965 : Blo 397767 1539965 := bstep (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) B577487
theorem B2555819 : Blo 397767 2555819 := bstep (se 1 (by rfl) ⟨1916864, by rfl⟩ : syracuseStep 2555819 = 3833729) B3833729
theorem B12451843 : Blo 397767 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B2162875 : Blo 397767 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B2031803 : Blo 397767 2031803 := bstep (se 1 (by rfl) ⟨1523852, by rfl⟩ : syracuseStep 2031803 = 3047705) B3047705
theorem B2884409 : Blo 397767 2884409 := bstep (se 2 (by rfl) ⟨1081653, by rfl⟩ : syracuseStep 2884409 = 2163307) B2163307
theorem B2556845 : Blo 397767 2556845 := bstep (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) B958817
theorem B1311967 : Blo 397767 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B3048677 : Blo 397767 3048677 := bstep (se 4 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 3048677 = 571627) B571627
theorem B1344815 : Blo 397767 1344815 := bstep (se 1 (by rfl) ⟨1008611, by rfl⟩ : syracuseStep 1344815 = 2017223) B2017223
theorem B722255 : Blo 397767 722255 := bstep (se 1 (by rfl) ⟨541691, by rfl⟩ : syracuseStep 722255 = 1083383) B1083383
theorem B2426375 : Blo 397767 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B427999 : Blo 397767 427999 := bstep (se 1 (by rfl) ⟨320999, by rfl⟩ : syracuseStep 427999 = 641999) B641999
theorem B755867 : Blo 397767 755867 := bstep (se 1 (by rfl) ⟨566900, by rfl⟩ : syracuseStep 755867 = 1133801) B1133801
theorem B5114663 : Blo 397767 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B855049 : Blo 397767 855049 := bstep (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) B641287
theorem B3050621 : Blo 397767 3050621 := bstep (se 3 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 3050621 = 1143983) B1143983
theorem B1510609 : Blo 397767 1510609 := bstep (se 2 (by rfl) ⟨566478, by rfl⟩ : syracuseStep 1510609 = 1132957) B1132957
theorem B2624723 : Blo 397767 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B855527 : Blo 397767 855527 := bstep (se 1 (by rfl) ⟨641645, by rfl⟩ : syracuseStep 855527 = 1283291) B1283291
theorem B3248045 : Blo 397767 3248045 := bstep (se 3 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 3248045 = 1218017) B1218017
theorem B2592719 : Blo 397767 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B7704665 : Blo 397767 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B398075 : Blo 397767 398075 := bstep (se 1 (by rfl) ⟨298556, by rfl⟩ : syracuseStep 398075 = 597113) B597113
theorem B758585 : Blo 397767 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B398143 : Blo 397767 398143 := bstep (se 1 (by rfl) ⟨298607, by rfl⟩ : syracuseStep 398143 = 597215) B597215
theorem B3412813 : Blo 397767 3412813 := bstep (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) B1279805
theorem B398171 : Blo 397767 398171 := bstep (se 1 (by rfl) ⟨298628, by rfl⟩ : syracuseStep 398171 = 597257) B597257
theorem B758639 : Blo 397767 758639 := bstep (se 1 (by rfl) ⟨568979, by rfl⟩ : syracuseStep 758639 = 1137959) B1137959
theorem B398239 : Blo 397767 398239 := bstep (se 1 (by rfl) ⟨298679, by rfl⟩ : syracuseStep 398239 = 597359) B597359
theorem B398319 : Blo 397767 398319 := bstep (se 1 (by rfl) ⟨298739, by rfl⟩ : syracuseStep 398319 = 597479) B597479
theorem B1709039 : Blo 397767 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B398407 : Blo 397767 398407 := bstep (se 1 (by rfl) ⟨298805, by rfl⟩ : syracuseStep 398407 = 597611) B597611
theorem B398491 : Blo 397767 398491 := bstep (se 1 (by rfl) ⟨298868, by rfl⟩ : syracuseStep 398491 = 597737) B597737
theorem B398587 : Blo 397767 398587 := bstep (se 1 (by rfl) ⟨298940, by rfl⟩ : syracuseStep 398587 = 597881) B597881
theorem B398655 : Blo 397767 398655 := bstep (se 1 (by rfl) ⟨298991, by rfl⟩ : syracuseStep 398655 = 597983) B597983
theorem B398823 : Blo 397767 398823 := bstep (se 1 (by rfl) ⟨299117, by rfl⟩ : syracuseStep 398823 = 598235) B598235
theorem B398831 : Blo 397767 398831 := bstep (se 1 (by rfl) ⟨299123, by rfl⟩ : syracuseStep 398831 = 598247) B598247
theorem B1513039 : Blo 397767 1513039 := bstep (se 1 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 1513039 = 2269559) B2269559
theorem B398939 : Blo 397767 398939 := bstep (se 1 (by rfl) ⟨299204, by rfl⟩ : syracuseStep 398939 = 598409) B598409
theorem B399003 : Blo 397767 399003 := bstep (se 1 (by rfl) ⟨299252, by rfl⟩ : syracuseStep 399003 = 598505) B598505
theorem B1152667 : Blo 397767 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B759451 : Blo 397767 759451 := bstep (se 1 (by rfl) ⟨569588, by rfl⟩ : syracuseStep 759451 = 1139177) B1139177
theorem B399087 : Blo 397767 399087 := bstep (se 1 (by rfl) ⟨299315, by rfl⟩ : syracuseStep 399087 = 598631) B598631
theorem B1218311 : Blo 397767 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B399175 : Blo 397767 399175 := bstep (se 1 (by rfl) ⟨299381, by rfl⟩ : syracuseStep 399175 = 598763) B598763
theorem B1349459 : Blo 397767 1349459 := bstep (se 1 (by rfl) ⟨1012094, by rfl⟩ : syracuseStep 1349459 = 2024189) B2024189
theorem B399195 : Blo 397767 399195 := bstep (se 1 (by rfl) ⟨299396, by rfl⟩ : syracuseStep 399195 = 598793) B598793
theorem B1513313 : Blo 397767 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B399263 : Blo 397767 399263 := bstep (se 1 (by rfl) ⟨299447, by rfl⟩ : syracuseStep 399263 = 598895) B598895
theorem B399431 : Blo 397767 399431 := bstep (se 1 (by rfl) ⟨299573, by rfl⟩ : syracuseStep 399431 = 599147) B599147
theorem B399591 : Blo 397767 399591 := bstep (se 1 (by rfl) ⟨299693, by rfl⟩ : syracuseStep 399591 = 599387) B599387
theorem B399775 : Blo 397767 399775 := bstep (se 1 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 399775 = 599663) B599663
theorem B399823 : Blo 397767 399823 := bstep (se 1 (by rfl) ⟨299867, by rfl⟩ : syracuseStep 399823 = 599735) B599735
theorem B399847 : Blo 397767 399847 := bstep (se 1 (by rfl) ⟨299885, by rfl⟩ : syracuseStep 399847 = 599771) B599771
theorem B399963 : Blo 397767 399963 := bstep (se 1 (by rfl) ⟨299972, by rfl⟩ : syracuseStep 399963 = 599945) B599945
theorem B400031 : Blo 397767 400031 := bstep (se 1 (by rfl) ⟨300023, by rfl⟩ : syracuseStep 400031 = 600047) B600047
theorem B1022777 : Blo 397767 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B596807 : Blo 397767 596807 := bstep (se 1 (by rfl) ⟨447605, by rfl⟩ : syracuseStep 596807 = 895211) B895211
theorem B400199 : Blo 397767 400199 := bstep (se 1 (by rfl) ⟨300149, by rfl⟩ : syracuseStep 400199 = 600299) B600299
theorem B400239 : Blo 397767 400239 := bstep (se 1 (by rfl) ⟨300179, by rfl⟩ : syracuseStep 400239 = 600359) B600359
theorem B7314299 : Blo 397767 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B400295 : Blo 397767 400295 := bstep (se 1 (by rfl) ⟨300221, by rfl⟩ : syracuseStep 400295 = 600443) B600443
theorem B10951631 : Blo 397767 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B400475 : Blo 397767 400475 := bstep (se 1 (by rfl) ⟨300356, by rfl⟩ : syracuseStep 400475 = 600713) B600713
theorem B1350863 : Blo 397767 1350863 := bstep (se 1 (by rfl) ⟨1013147, by rfl⟩ : syracuseStep 1350863 = 2026295) B2026295
theorem B400591 : Blo 397767 400591 := bstep (se 1 (by rfl) ⟨300443, by rfl⟩ : syracuseStep 400591 = 600887) B600887
theorem B400615 : Blo 397767 400615 := bstep (se 1 (by rfl) ⟨300461, by rfl⟩ : syracuseStep 400615 = 600923) B600923
theorem B400711 : Blo 397767 400711 := bstep (se 1 (by rfl) ⟨300533, by rfl⟩ : syracuseStep 400711 = 601067) B601067
theorem B5447087 : Blo 397767 5447087 := bstep (se 1 (by rfl) ⟨4085315, by rfl⟩ : syracuseStep 5447087 = 8170631) B8170631
theorem B400847 : Blo 397767 400847 := bstep (se 1 (by rfl) ⟨300635, by rfl⟩ : syracuseStep 400847 = 601271) B601271
theorem B1351241 : Blo 397767 1351241 := bstep (se 2 (by rfl) ⟨506715, by rfl⟩ : syracuseStep 1351241 = 1013431) B1013431
theorem B401007 : Blo 397767 401007 := bstep (se 1 (by rfl) ⟨300755, by rfl⟩ : syracuseStep 401007 = 601511) B601511
theorem B597671 : Blo 397767 597671 := bstep (se 1 (by rfl) ⟨448253, by rfl⟩ : syracuseStep 597671 = 896507) B896507
theorem B401063 : Blo 397767 401063 := bstep (se 1 (by rfl) ⟨300797, by rfl⟩ : syracuseStep 401063 = 601595) B601595
theorem B401127 : Blo 397767 401127 := bstep (se 1 (by rfl) ⟨300845, by rfl⟩ : syracuseStep 401127 = 601691) B601691
theorem B597791 : Blo 397767 597791 := bstep (se 1 (by rfl) ⟨448343, by rfl⟩ : syracuseStep 597791 = 896687) B896687
theorem B401183 : Blo 397767 401183 := bstep (se 1 (by rfl) ⟨300887, by rfl⟩ : syracuseStep 401183 = 601775) B601775
theorem B401263 : Blo 397767 401263 := bstep (se 1 (by rfl) ⟨300947, by rfl⟩ : syracuseStep 401263 = 601895) B601895
theorem B401319 : Blo 397767 401319 := bstep (se 1 (by rfl) ⟨300989, by rfl⟩ : syracuseStep 401319 = 601979) B601979
theorem B1286111 : Blo 397767 1286111 := bstep (se 1 (by rfl) ⟨964583, by rfl⟩ : syracuseStep 1286111 = 1929167) B1929167
theorem B401599 : Blo 397767 401599 := bstep (se 1 (by rfl) ⟨301199, by rfl⟩ : syracuseStep 401599 = 602399) B602399
theorem B598223 : Blo 397767 598223 := bstep (se 1 (by rfl) ⟨448667, by rfl⟩ : syracuseStep 598223 = 897335) B897335
theorem B401615 : Blo 397767 401615 := bstep (se 1 (by rfl) ⟨301211, by rfl⟩ : syracuseStep 401615 = 602423) B602423
theorem B598271 : Blo 397767 598271 := bstep (se 1 (by rfl) ⟨448703, by rfl⟩ : syracuseStep 598271 = 897407) B897407
theorem B401663 : Blo 397767 401663 := bstep (se 1 (by rfl) ⟨301247, by rfl⟩ : syracuseStep 401663 = 602495) B602495
theorem B401711 : Blo 397767 401711 := bstep (se 1 (by rfl) ⟨301283, by rfl⟩ : syracuseStep 401711 = 602567) B602567
theorem B959239 : Blo 397767 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B599087 : Blo 397767 599087 := bstep (se 1 (by rfl) ⟨449315, by rfl⟩ : syracuseStep 599087 = 898631) B898631
theorem B599207 : Blo 397767 599207 := bstep (se 1 (by rfl) ⟨449405, by rfl⟩ : syracuseStep 599207 = 898811) B898811
theorem B11544079 : Blo 397767 11544079 := bstep (se 1 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 11544079 = 17316119) B17316119
theorem B599579 : Blo 397767 599579 := bstep (se 1 (by rfl) ⟨449684, by rfl⟩ : syracuseStep 599579 = 899369) B899369
theorem B599963 : Blo 397767 599963 := bstep (se 1 (by rfl) ⟨449972, by rfl⟩ : syracuseStep 599963 = 899945) B899945
theorem B599999 : Blo 397767 599999 := bstep (se 1 (by rfl) ⟨449999, by rfl⟩ : syracuseStep 599999 = 899999) B899999
theorem B3024863 : Blo 397767 3024863 := bstep (se 1 (by rfl) ⟨2268647, by rfl⟩ : syracuseStep 3024863 = 4537295) B4537295
theorem B2566171 : Blo 397767 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B1353833 : Blo 397767 1353833 := bstep (se 2 (by rfl) ⟨507687, by rfl⟩ : syracuseStep 1353833 = 1015375) B1015375
theorem B600185 : Blo 397767 600185 := bstep (se 2 (by rfl) ⟨225069, by rfl⟩ : syracuseStep 600185 = 450139) B450139
theorem B5843315 : Blo 397767 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B895481 : Blo 397767 895481 := bstep (se 2 (by rfl) ⟨335805, by rfl⟩ : syracuseStep 895481 = 671611) B671611
theorem B600569 : Blo 397767 600569 := bstep (se 2 (by rfl) ⟨225213, by rfl⟩ : syracuseStep 600569 = 450427) B450427
theorem B895535 : Blo 397767 895535 := bstep (se 1 (by rfl) ⟨671651, by rfl⟩ : syracuseStep 895535 = 1343303) B1343303
theorem B600623 : Blo 397767 600623 := bstep (se 1 (by rfl) ⟨450467, by rfl⟩ : syracuseStep 600623 = 900935) B900935
theorem B1714745 : Blo 397767 1714745 := bstep (se 2 (by rfl) ⟨643029, by rfl⟩ : syracuseStep 1714745 = 1286059) B1286059
theorem B895571 : Blo 397767 895571 := bstep (se 1 (by rfl) ⟨671678, by rfl⟩ : syracuseStep 895571 = 1343357) B1343357
theorem B1026643 : Blo 397767 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B1911559 : Blo 397767 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B895751 : Blo 397767 895751 := bstep (se 1 (by rfl) ⟨671813, by rfl⟩ : syracuseStep 895751 = 1343627) B1343627
theorem B895967 : Blo 397767 895967 := bstep (se 1 (by rfl) ⟨671975, by rfl⟩ : syracuseStep 895967 = 1343951) B1343951
theorem B601055 : Blo 397767 601055 := bstep (se 1 (by rfl) ⟨450791, by rfl⟩ : syracuseStep 601055 = 901583) B901583
theorem B896183 : Blo 397767 896183 := bstep (se 1 (by rfl) ⟨672137, by rfl⟩ : syracuseStep 896183 = 1344275) B1344275
theorem B1518857 : Blo 397767 1518857 := bstep (se 2 (by rfl) ⟨569571, by rfl⟩ : syracuseStep 1518857 = 1139143) B1139143
theorem B601499 : Blo 397767 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B896759 : Blo 397767 896759 := bstep (se 1 (by rfl) ⟨672569, by rfl⟩ : syracuseStep 896759 = 1345139) B1345139
theorem B6827813 : Blo 397767 6827813 := bstep (se 4 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 6827813 = 1280215) B1280215
theorem B896831 : Blo 397767 896831 := bstep (se 1 (by rfl) ⟨672623, by rfl⟩ : syracuseStep 896831 = 1345247) B1345247
theorem B601919 : Blo 397767 601919 := bstep (se 1 (by rfl) ⟨451439, by rfl⟩ : syracuseStep 601919 = 902879) B902879
theorem B896939 : Blo 397767 896939 := bstep (se 1 (by rfl) ⟨672704, by rfl⟩ : syracuseStep 896939 = 1345409) B1345409
theorem B5779421 : Blo 397767 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B602105 : Blo 397767 602105 := bstep (se 2 (by rfl) ⟨225789, by rfl⟩ : syracuseStep 602105 = 451579) B451579
theorem B7712819 : Blo 397767 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B3911759 : Blo 397767 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B602345 : Blo 397767 602345 := bstep (se 2 (by rfl) ⟨225879, by rfl⟩ : syracuseStep 602345 = 451759) B451759
theorem B897299 : Blo 397767 897299 := bstep (se 1 (by rfl) ⟨672974, by rfl⟩ : syracuseStep 897299 = 1345949) B1345949
theorem B602471 : Blo 397767 602471 := bstep (se 1 (by rfl) ⟨451853, by rfl⟩ : syracuseStep 602471 = 903707) B903707
theorem B897479 : Blo 397767 897479 := bstep (se 1 (by rfl) ⟨673109, by rfl⟩ : syracuseStep 897479 = 1346219) B1346219
theorem B23147207 : Blo 397767 23147207 := bstep (se 1 (by rfl) ⟨17360405, by rfl⟩ : syracuseStep 23147207 = 34720811) B34720811
theorem B2568941 : Blo 397767 2568941 := bstep (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) B963353
theorem B897839 : Blo 397767 897839 := bstep (se 1 (by rfl) ⟨673379, by rfl⟩ : syracuseStep 897839 = 1346759) B1346759
theorem B2274115 : Blo 397767 2274115 := bstep (se 1 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 2274115 = 3411173) B3411173
theorem B897929 : Blo 397767 897929 := bstep (se 2 (by rfl) ⟨336723, by rfl⟩ : syracuseStep 897929 = 673447) B673447
theorem B1520815 : Blo 397767 1520815 := bstep (se 1 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 1520815 = 2281223) B2281223
theorem B964007 : Blo 397767 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B505435 : Blo 397767 505435 := bstep (se 1 (by rfl) ⟨379076, by rfl⟩ : syracuseStep 505435 = 758153) B758153
theorem B898703 : Blo 397767 898703 := bstep (se 1 (by rfl) ⟨674027, by rfl⟩ : syracuseStep 898703 = 1348055) B1348055
theorem B898793 : Blo 397767 898793 := bstep (se 2 (by rfl) ⟨337047, by rfl⟩ : syracuseStep 898793 = 674095) B674095
theorem B2569967 : Blo 397767 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B571855 : Blo 397767 571855 := bstep (se 1 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 571855 = 857783) B857783
theorem B2275847 : Blo 397767 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B899675 : Blo 397767 899675 := bstep (se 1 (by rfl) ⟨674756, by rfl⟩ : syracuseStep 899675 = 1349513) B1349513
theorem B899819 : Blo 397767 899819 := bstep (se 1 (by rfl) ⟨674864, by rfl⟩ : syracuseStep 899819 = 1349729) B1349729
theorem B769247 : Blo 397767 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B900431 : Blo 397767 900431 := bstep (se 1 (by rfl) ⟨675323, by rfl⟩ : syracuseStep 900431 = 1350647) B1350647
theorem B900521 : Blo 397767 900521 := bstep (se 2 (by rfl) ⟨337695, by rfl⟩ : syracuseStep 900521 = 675391) B675391
theorem B900719 : Blo 397767 900719 := bstep (se 1 (by rfl) ⟨675539, by rfl⟩ : syracuseStep 900719 = 1351079) B1351079
theorem B901007 : Blo 397767 901007 := bstep (se 1 (by rfl) ⟨675755, by rfl⟩ : syracuseStep 901007 = 1351511) B1351511
theorem B671935 : Blo 397767 671935 := bstep (se 1 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 671935 = 1007903) B1007903
theorem B3850487 : Blo 397767 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B901547 : Blo 397767 901547 := bstep (se 1 (by rfl) ⟨676160, by rfl⟩ : syracuseStep 901547 = 1352321) B1352321
theorem B508447 : Blo 397767 508447 := bstep (se 1 (by rfl) ⟨381335, by rfl⟩ : syracuseStep 508447 = 762671) B762671
theorem B901727 : Blo 397767 901727 := bstep (se 1 (by rfl) ⟨676295, by rfl⟩ : syracuseStep 901727 = 1352591) B1352591
theorem B672367 : Blo 397767 672367 := bstep (se 1 (by rfl) ⟨504275, by rfl⟩ : syracuseStep 672367 = 1008551) B1008551
theorem B1524521 : Blo 397767 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B902087 : Blo 397767 902087 := bstep (se 1 (by rfl) ⟨676565, by rfl⟩ : syracuseStep 902087 = 1353131) B1353131
theorem B2016251 : Blo 397767 2016251 := bstep (se 1 (by rfl) ⟨1512188, by rfl⟩ : syracuseStep 2016251 = 3024377) B3024377
theorem B2278489 : Blo 397767 2278489 := bstep (se 2 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 2278489 = 1708867) B1708867
theorem B2573531 : Blo 397767 2573531 := bstep (se 1 (by rfl) ⟨1930148, by rfl⟩ : syracuseStep 2573531 = 3860297) B3860297
theorem B902447 : Blo 397767 902447 := bstep (se 1 (by rfl) ⟨676835, by rfl⟩ : syracuseStep 902447 = 1353671) B1353671
theorem B673103 : Blo 397767 673103 := bstep (se 1 (by rfl) ⟨504827, by rfl⟩ : syracuseStep 673103 = 1009655) B1009655
theorem B2278763 : Blo 397767 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B1525175 : Blo 397767 1525175 := bstep (se 1 (by rfl) ⟨1143881, by rfl⟩ : syracuseStep 1525175 = 2287763) B2287763
theorem B3458519 : Blo 397767 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B902951 : Blo 397767 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B903329 : Blo 397767 903329 := bstep (se 2 (by rfl) ⟨338748, by rfl⟩ : syracuseStep 903329 = 677497) B677497
theorem B674075 : Blo 397767 674075 := bstep (se 1 (by rfl) ⟨505556, by rfl⟩ : syracuseStep 674075 = 1011113) B1011113
theorem B969175 : Blo 397767 969175 := bstep (se 1 (by rfl) ⟨726881, by rfl⟩ : syracuseStep 969175 = 1453763) B1453763
theorem B674399 : Blo 397767 674399 := bstep (se 1 (by rfl) ⟨505799, by rfl⟩ : syracuseStep 674399 = 1011599) B1011599
theorem B5557015 : Blo 397767 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B11717399 : Blo 397767 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B903977 : Blo 397767 903977 := bstep (se 2 (by rfl) ⟨338991, by rfl⟩ : syracuseStep 903977 = 677983) B677983
theorem B1822591 : Blo 397767 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B3035069 : Blo 397767 3035069 := bstep (se 3 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 3035069 = 1138151) B1138151
theorem B675823 : Blo 397767 675823 := bstep (se 1 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 675823 = 1013735) B1013735
theorem B1134587 : Blo 397767 1134587 := bstep (se 1 (by rfl) ⟨850940, by rfl⟩ : syracuseStep 1134587 = 1701881) B1701881
theorem B1692269 : Blo 397767 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B2019977 : Blo 397767 2019977 := bstep (se 2 (by rfl) ⟨757491, by rfl⟩ : syracuseStep 2019977 = 1514983) B1514983
theorem B24728615 : Blo 397767 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B447583 : Blo 397767 447583 := bstep (se 1 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 447583 = 671375) B671375
theorem B5101177 : Blo 397767 5101177 := bstep (se 2 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 5101177 = 3825883) B3825883
theorem B677531 : Blo 397767 677531 := bstep (se 1 (by rfl) ⟨508148, by rfl⟩ : syracuseStep 677531 = 1016297) B1016297
theorem B3823271 : Blo 397767 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B53106353 : Blo 397767 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B579487 : Blo 397767 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B1169447 : Blo 397767 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B482215 : Blo 397767 482215 := bstep (se 1 (by rfl) ⟨361661, by rfl⟩ : syracuseStep 482215 = 723323) B723323
theorem B29678561 : Blo 397767 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B5201081 : Blo 397767 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B449743 : Blo 397767 449743 := bstep (se 1 (by rfl) ⟨337307, by rfl⟩ : syracuseStep 449743 = 674615) B674615
theorem B3824927 : Blo 397767 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B4120001 : Blo 397767 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B1465847 : Blo 397767 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B1007225 : Blo 397767 1007225 := bstep (se 2 (by rfl) ⟨377709, by rfl⟩ : syracuseStep 1007225 = 755419) B755419
theorem B3825731 : Blo 397767 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B450751 : Blo 397767 450751 := bstep (se 1 (by rfl) ⟨338063, by rfl⟩ : syracuseStep 450751 = 676127) B676127
theorem B3399965 : Blo 397767 3399965 := bstep (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) B1274987
theorem B451183 : Blo 397767 451183 := bstep (se 1 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 451183 = 676775) B676775
theorem B451291 : Blo 397767 451291 := bstep (se 1 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 451291 = 676937) B676937
theorem B1008713 : Blo 397767 1008713 := bstep (se 2 (by rfl) ⟨378267, by rfl⟩ : syracuseStep 1008713 = 756535) B756535
theorem B1140475 : Blo 397767 1140475 := bstep (se 1 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 1140475 = 1710713) B1710713
theorem B1140635 : Blo 397767 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1402867 : Blo 397767 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B1435745 : Blo 397767 1435745 := bstep (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) B1076809
theorem B2877605 : Blo 397767 2877605 := bstep (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) B539551
theorem B4548959 : Blo 397767 4548959 := bstep (se 1 (by rfl) ⟨3411719, by rfl⟩ : syracuseStep 4548959 = 6823439) B6823439
theorem B5860147 : Blo 397767 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B1076107 : Blo 397767 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B3238865 : Blo 397767 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B3239767 : Blo 397767 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B12415169 : Blo 397767 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B6484205 : Blo 397767 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B1012459 : Blo 397767 1012459 := bstep (se 1 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 1012459 = 1518689) B1518689
theorem B6452027 : Blo 397767 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B1439005 : Blo 397767 1439005 := bstep (se 3 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 1439005 = 539627) B539627
theorem B2029373 : Blo 397767 2029373 := bstep (se 3 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 2029373 = 761015) B761015
theorem B1341263 : Blo 397767 1341263 := bstep (se 1 (by rfl) ⟨1005947, by rfl⟩ : syracuseStep 1341263 = 2011895) B2011895
theorem B1439927 : Blo 397767 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B2030345 : Blo 397767 2030345 := bstep (se 2 (by rfl) ⟨761379, by rfl⟩ : syracuseStep 2030345 = 1522759) B1522759
theorem B3406799 : Blo 397767 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B1703263 : Blo 397767 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B7273871 : Blo 397767 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B425423 : Blo 397767 425423 := bstep (se 1 (by rfl) ⟨319067, by rfl⟩ : syracuseStep 425423 = 638135) B638135
theorem B851563 : Blo 397767 851563 := bstep (se 1 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 851563 = 1277345) B1277345
theorem B1343087 : Blo 397767 1343087 := bstep (se 1 (by rfl) ⟨1007315, by rfl⟩ : syracuseStep 1343087 = 2014631) B2014631
theorem B9273041 : Blo 397767 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B1703879 : Blo 397767 1703879 := bstep (se 1 (by rfl) ⟨1277909, by rfl⟩ : syracuseStep 1703879 = 2555819) B2555819
theorem B2883833 : Blo 397767 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1016347 : Blo 397767 1016347 := bstep (se 1 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 1016347 = 1524521) B1524521
theorem B1704563 : Blo 397767 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B1344167 : Blo 397767 1344167 := bstep (se 1 (by rfl) ⟨1008125, by rfl⟩ : syracuseStep 1344167 = 2016251) B2016251
theorem B2032451 : Blo 397767 2032451 := bstep (se 1 (by rfl) ⟨1524338, by rfl⟩ : syracuseStep 2032451 = 3048677) B3048677
theorem B1016783 : Blo 397767 1016783 := bstep (se 1 (by rfl) ⟨762587, by rfl⟩ : syracuseStep 1016783 = 1525175) B1525175
theorem B1278985 : Blo 397767 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B3409775 : Blo 397767 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B2033747 : Blo 397767 2033747 := bstep (se 1 (by rfl) ⟨1525310, by rfl⟩ : syracuseStep 2033747 = 3050621) B3050621
theorem B2165363 : Blo 397767 2165363 := bstep (se 1 (by rfl) ⟨1624022, by rfl⟩ : syracuseStep 2165363 = 3248045) B3248045
theorem B1870489 : Blo 397767 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B756391 : Blo 397767 756391 := bstep (se 1 (by rfl) ⟨567293, by rfl⟩ : syracuseStep 756391 = 1134587) B1134587
theorem B1346651 : Blo 397767 1346651 := bstep (se 1 (by rfl) ⟨1009988, by rfl⟩ : syracuseStep 1346651 = 2019977) B2019977
theorem B16485743 : Blo 397767 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B397871 : Blo 397767 397871 := bstep (se 1 (by rfl) ⟨298403, by rfl⟩ : syracuseStep 397871 = 596807) B596807
theorem B398447 : Blo 397767 398447 := bstep (se 1 (by rfl) ⟨298835, by rfl⟩ : syracuseStep 398447 = 597671) B597671
theorem B398527 : Blo 397767 398527 := bstep (se 1 (by rfl) ⟨298895, by rfl⟩ : syracuseStep 398527 = 597791) B597791
theorem B857407 : Blo 397767 857407 := bstep (se 1 (by rfl) ⟨643055, by rfl⟩ : syracuseStep 857407 = 1286111) B1286111
theorem B398815 : Blo 397767 398815 := bstep (se 1 (by rfl) ⟨299111, by rfl⟩ : syracuseStep 398815 = 598223) B598223
theorem B398847 : Blo 397767 398847 := bstep (se 1 (by rfl) ⟨299135, by rfl⟩ : syracuseStep 398847 = 598271) B598271
theorem B2266643 : Blo 397767 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B399391 : Blo 397767 399391 := bstep (se 1 (by rfl) ⟨299543, by rfl⟩ : syracuseStep 399391 = 599087) B599087
theorem B399471 : Blo 397767 399471 := bstep (se 1 (by rfl) ⟨299603, by rfl⟩ : syracuseStep 399471 = 599207) B599207
theorem B1349945 : Blo 397767 1349945 := bstep (se 2 (by rfl) ⟨506229, by rfl⟩ : syracuseStep 1349945 = 1012459) B1012459
theorem B399719 : Blo 397767 399719 := bstep (se 1 (by rfl) ⟨299789, by rfl⟩ : syracuseStep 399719 = 599579) B599579
theorem B399975 : Blo 397767 399975 := bstep (se 1 (by rfl) ⟨299981, by rfl⟩ : syracuseStep 399975 = 599963) B599963
theorem B760423 : Blo 397767 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B399999 : Blo 397767 399999 := bstep (se 1 (by rfl) ⟨299999, by rfl⟩ : syracuseStep 399999 = 599999) B599999
theorem B400123 : Blo 397767 400123 := bstep (se 1 (by rfl) ⟨300092, by rfl⟩ : syracuseStep 400123 = 600185) B600185
theorem B596777 : Blo 397767 596777 := bstep (se 2 (by rfl) ⟨223791, by rfl⟩ : syracuseStep 596777 = 447583) B447583
theorem B596987 : Blo 397767 596987 := bstep (se 1 (by rfl) ⟨447740, by rfl⟩ : syracuseStep 596987 = 895481) B895481
theorem B400379 : Blo 397767 400379 := bstep (se 1 (by rfl) ⟨300284, by rfl⟩ : syracuseStep 400379 = 600569) B600569
theorem B597023 : Blo 397767 597023 := bstep (se 1 (by rfl) ⟨447767, by rfl⟩ : syracuseStep 597023 = 895535) B895535
theorem B400415 : Blo 397767 400415 := bstep (se 1 (by rfl) ⟨300311, by rfl⟩ : syracuseStep 400415 = 600623) B600623
theorem B597047 : Blo 397767 597047 := bstep (se 1 (by rfl) ⟨447785, by rfl⟩ : syracuseStep 597047 = 895571) B895571
theorem B597167 : Blo 397767 597167 := bstep (se 1 (by rfl) ⟨447875, by rfl⟩ : syracuseStep 597167 = 895751) B895751
theorem B597311 : Blo 397767 597311 := bstep (se 1 (by rfl) ⟨447983, by rfl⟩ : syracuseStep 597311 = 895967) B895967
theorem B400703 : Blo 397767 400703 := bstep (se 1 (by rfl) ⟨300527, by rfl⟩ : syracuseStep 400703 = 601055) B601055
theorem B597455 : Blo 397767 597455 := bstep (se 1 (by rfl) ⟨448091, by rfl⟩ : syracuseStep 597455 = 896183) B896183
theorem B400999 : Blo 397767 400999 := bstep (se 1 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 400999 = 601499) B601499
theorem B597839 : Blo 397767 597839 := bstep (se 1 (by rfl) ⟨448379, by rfl⟩ : syracuseStep 597839 = 896759) B896759
theorem B597887 : Blo 397767 597887 := bstep (se 1 (by rfl) ⟨448415, by rfl⟩ : syracuseStep 597887 = 896831) B896831
theorem B401279 : Blo 397767 401279 := bstep (se 1 (by rfl) ⟨300959, by rfl⟩ : syracuseStep 401279 = 601919) B601919
theorem B597959 : Blo 397767 597959 := bstep (se 1 (by rfl) ⟨448469, by rfl⟩ : syracuseStep 597959 = 896939) B896939
theorem B401403 : Blo 397767 401403 := bstep (se 1 (by rfl) ⟨301052, by rfl⟩ : syracuseStep 401403 = 602105) B602105
theorem B401563 : Blo 397767 401563 := bstep (se 1 (by rfl) ⟨301172, by rfl⟩ : syracuseStep 401563 = 602345) B602345
theorem B598199 : Blo 397767 598199 := bstep (se 1 (by rfl) ⟨448649, by rfl⟩ : syracuseStep 598199 = 897299) B897299
theorem B401647 : Blo 397767 401647 := bstep (se 1 (by rfl) ⟨301235, by rfl⟩ : syracuseStep 401647 = 602471) B602471
theorem B598319 : Blo 397767 598319 := bstep (se 1 (by rfl) ⟨448739, by rfl⟩ : syracuseStep 598319 = 897479) B897479
theorem B1712627 : Blo 397767 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B598559 : Blo 397767 598559 := bstep (se 1 (by rfl) ⟨448919, by rfl⟩ : syracuseStep 598559 = 897839) B897839
theorem B4301351 : Blo 397767 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B598619 : Blo 397767 598619 := bstep (se 1 (by rfl) ⟨448964, by rfl⟩ : syracuseStep 598619 = 897929) B897929
theorem B762473 : Blo 397767 762473 := bstep (se 2 (by rfl) ⟨285927, by rfl⟩ : syracuseStep 762473 = 571855) B571855
theorem B599135 : Blo 397767 599135 := bstep (se 1 (by rfl) ⟨449351, by rfl⟩ : syracuseStep 599135 = 898703) B898703
theorem B599195 : Blo 397767 599195 := bstep (se 1 (by rfl) ⟨449396, by rfl⟩ : syracuseStep 599195 = 898793) B898793
theorem B1713311 : Blo 397767 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B1352915 : Blo 397767 1352915 := bstep (se 1 (by rfl) ⟨1014686, by rfl⟩ : syracuseStep 1352915 = 2029373) B2029373
theorem B894175 : Blo 397767 894175 := bstep (se 1 (by rfl) ⟨670631, by rfl⟩ : syracuseStep 894175 = 1341263) B1341263
theorem B959951 : Blo 397767 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B599657 : Blo 397767 599657 := bstep (se 2 (by rfl) ⟨224871, by rfl⟩ : syracuseStep 599657 = 449743) B449743
theorem B1517231 : Blo 397767 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B599783 : Blo 397767 599783 := bstep (se 1 (by rfl) ⟨449837, by rfl⟩ : syracuseStep 599783 = 899675) B899675
theorem B17278757 : Blo 397767 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B2271017 : Blo 397767 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B599879 : Blo 397767 599879 := bstep (se 1 (by rfl) ⟨449909, by rfl⟩ : syracuseStep 599879 = 899819) B899819
theorem B1353563 : Blo 397767 1353563 := bstep (se 1 (by rfl) ⟨1015172, by rfl⟩ : syracuseStep 1353563 = 2030345) B2030345
theorem B2271199 : Blo 397767 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B600287 : Blo 397767 600287 := bstep (se 1 (by rfl) ⟨450215, by rfl⟩ : syracuseStep 600287 = 900431) B900431
theorem B600347 : Blo 397767 600347 := bstep (se 1 (by rfl) ⟨450260, by rfl⟩ : syracuseStep 600347 = 900521) B900521
theorem B895391 : Blo 397767 895391 := bstep (se 1 (by rfl) ⟨671543, by rfl⟩ : syracuseStep 895391 = 1343087) B1343087
theorem B600479 : Blo 397767 600479 := bstep (se 1 (by rfl) ⟨450359, by rfl⟩ : syracuseStep 600479 = 900719) B900719
theorem B600671 : Blo 397767 600671 := bstep (se 1 (by rfl) ⟨450503, by rfl⟩ : syracuseStep 600671 = 901007) B901007
theorem B1354535 : Blo 397767 1354535 := bstep (se 1 (by rfl) ⟨1015901, by rfl⟩ : syracuseStep 1354535 = 2031803) B2031803
theorem B2566991 : Blo 397767 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B895913 : Blo 397767 895913 := bstep (se 2 (by rfl) ⟨335967, by rfl⟩ : syracuseStep 895913 = 671935) B671935
theorem B601001 : Blo 397767 601001 := bstep (se 2 (by rfl) ⟨225375, by rfl⟩ : syracuseStep 601001 = 450751) B450751
theorem B601031 : Blo 397767 601031 := bstep (se 1 (by rfl) ⟨450773, by rfl⟩ : syracuseStep 601031 = 901547) B901547
theorem B601151 : Blo 397767 601151 := bstep (se 1 (by rfl) ⟨450863, by rfl⟩ : syracuseStep 601151 = 901727) B901727
theorem B601391 : Blo 397767 601391 := bstep (se 1 (by rfl) ⟨451043, by rfl⟩ : syracuseStep 601391 = 902087) B902087
theorem B1715687 : Blo 397767 1715687 := bstep (se 1 (by rfl) ⟨1286765, by rfl⟩ : syracuseStep 1715687 = 2573531) B2573531
theorem B896489 : Blo 397767 896489 := bstep (se 2 (by rfl) ⟨336183, by rfl⟩ : syracuseStep 896489 = 672367) B672367
theorem B601577 : Blo 397767 601577 := bstep (se 2 (by rfl) ⟨225591, by rfl⟩ : syracuseStep 601577 = 451183) B451183
theorem B896543 : Blo 397767 896543 := bstep (se 1 (by rfl) ⟨672407, by rfl⟩ : syracuseStep 896543 = 1344815) B1344815
theorem B601631 : Blo 397767 601631 := bstep (se 1 (by rfl) ⟨451223, by rfl⟩ : syracuseStep 601631 = 902447) B902447
theorem B1519175 : Blo 397767 1519175 := bstep (se 1 (by rfl) ⟨1139381, by rfl⟩ : syracuseStep 1519175 = 2278763) B2278763
theorem B601721 : Blo 397767 601721 := bstep (se 2 (by rfl) ⟨225645, by rfl⟩ : syracuseStep 601721 = 451291) B451291
theorem B2305679 : Blo 397767 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B1617583 : Blo 397767 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B601967 : Blo 397767 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B503911 : Blo 397767 503911 := bstep (se 1 (by rfl) ⟨377933, by rfl⟩ : syracuseStep 503911 = 755867) B755867
theorem B602219 : Blo 397767 602219 := bstep (se 1 (by rfl) ⟨451664, by rfl⟩ : syracuseStep 602219 = 903329) B903329
theorem B1749289 : Blo 397767 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B7811599 : Blo 397767 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B602651 : Blo 397767 602651 := bstep (se 1 (by rfl) ⟨451988, by rfl⟩ : syracuseStep 602651 = 903977) B903977
theorem B1749815 : Blo 397767 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B1520633 : Blo 397767 1520633 := bstep (se 2 (by rfl) ⟨570237, by rfl⟩ : syracuseStep 1520633 = 1140475) B1140475
theorem B570665 : Blo 397767 570665 := bstep (se 2 (by rfl) ⟨213999, by rfl⟩ : syracuseStep 570665 = 427999) B427999
theorem B3421561 : Blo 397767 3421561 := bstep (se 2 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 3421561 = 2566171) B2566171
theorem B1128179 : Blo 397767 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B505759 : Blo 397767 505759 := bstep (se 1 (by rfl) ⟨379319, by rfl⟩ : syracuseStep 505759 = 758639) B758639
theorem B1292233 : Blo 397767 1292233 := bstep (se 2 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 1292233 = 969175) B969175
theorem B7813529 : Blo 397767 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B35404235 : Blo 397767 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B899639 : Blo 397767 899639 := bstep (se 1 (by rfl) ⟨674729, by rfl⟩ : syracuseStep 899639 = 1349459) B1349459
theorem B29637413 : Blo 397767 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B2014145 : Blo 397767 2014145 := bstep (se 2 (by rfl) ⟨755304, by rfl⟩ : syracuseStep 2014145 = 1510609) B1510609
theorem B900575 : Blo 397767 900575 := bstep (se 1 (by rfl) ⟨675431, by rfl⟩ : syracuseStep 900575 = 1350863) B1350863
theorem B900827 : Blo 397767 900827 := bstep (se 1 (by rfl) ⟨675620, by rfl⟩ : syracuseStep 900827 = 1351241) B1351241
theorem B671483 : Blo 397767 671483 := bstep (se 1 (by rfl) ⟨503612, by rfl⟩ : syracuseStep 671483 = 1007225) B1007225
theorem B901097 : Blo 397767 901097 := bstep (se 2 (by rfl) ⟨337911, by rfl⟩ : syracuseStep 901097 = 675823) B675823
theorem B672475 : Blo 397767 672475 := bstep (se 1 (by rfl) ⟨504356, by rfl⟩ : syracuseStep 672475 = 1008713) B1008713
theorem B3032153 : Blo 397767 3032153 := bstep (se 2 (by rfl) ⟨1137057, by rfl⟩ : syracuseStep 3032153 = 2274115) B2274115
theorem B2016575 : Blo 397767 2016575 := bstep (se 1 (by rfl) ⟨1512431, by rfl⟩ : syracuseStep 2016575 = 3024863) B3024863
theorem B902555 : Blo 397767 902555 := bstep (se 1 (by rfl) ⟨676916, by rfl⟩ : syracuseStep 902555 = 1353833) B1353833
theorem B1918403 : Blo 397767 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B3032639 : Blo 397767 3032639 := bstep (se 1 (by rfl) ⟨2274479, by rfl⟩ : syracuseStep 3032639 = 4548959) B4548959
theorem B1918673 : Blo 397767 1918673 := bstep (se 2 (by rfl) ⟨719502, by rfl⟩ : syracuseStep 1918673 = 1439005) B1439005
theorem B2017385 : Blo 397767 2017385 := bstep (se 2 (by rfl) ⟨756519, by rfl⟩ : syracuseStep 2017385 = 1513039) B1513039
theorem B673913 : Blo 397767 673913 := bstep (se 2 (by rfl) ⟨252717, by rfl⟩ : syracuseStep 673913 = 505435) B505435
theorem B6801569 : Blo 397767 6801569 := bstep (se 2 (by rfl) ⟨2550588, by rfl⟩ : syracuseStep 6801569 = 5101177) B5101177
theorem B772649 : Blo 397767 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B3852947 : Blo 397767 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B2607839 : Blo 397767 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B8276779 : Blo 397767 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B4541669 : Blo 397767 4541669 := bstep (se 4 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 4541669 = 851563) B851563
theorem B642671 : Blo 397767 642671 := bstep (se 1 (by rfl) ⟨482003, by rfl⟩ : syracuseStep 642671 = 964007) B964007
theorem B1134461 : Blo 397767 1134461 := bstep (se 3 (by rfl) ⟨212711, by rfl⟩ : syracuseStep 1134461 = 425423) B425423
theorem B642953 : Blo 397767 642953 := bstep (se 2 (by rfl) ⟨241107, by rfl⟩ : syracuseStep 642953 = 482215) B482215
theorem B2281405 : Blo 397767 2281405 := bstep (se 3 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 2281405 = 855527) B855527
theorem B9720485 : Blo 397767 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B512831 : Blo 397767 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B6182027 : Blo 397767 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B1135919 : Blo 397767 1135919 := bstep (se 1 (by rfl) ⟨851939, by rfl⟩ : syracuseStep 1135919 = 1703879) B1703879
theorem B16602457 : Blo 397767 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B12474101 : Blo 397767 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B1922939 : Blo 397767 1922939 := bstep (se 1 (by rfl) ⟨1442204, by rfl⟩ : syracuseStep 1922939 = 2884409) B2884409
theorem B677929 : Blo 397767 677929 := bstep (se 2 (by rfl) ⟨254223, by rfl⟩ : syracuseStep 677929 = 508447) B508447
theorem B448735 : Blo 397767 448735 := bstep (se 1 (by rfl) ⟨336551, by rfl⟩ : syracuseStep 448735 = 673103) B673103
theorem B3037985 : Blo 397767 3037985 := bstep (se 2 (by rfl) ⟨1139244, by rfl⟩ : syracuseStep 3037985 = 2278489) B2278489
theorem B449383 : Blo 397767 449383 := bstep (se 1 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 449383 = 674075) B674075
theorem B449599 : Blo 397767 449599 := bstep (se 1 (by rfl) ⟨337199, by rfl⟩ : syracuseStep 449599 = 674399) B674399
theorem B15392105 : Blo 397767 15392105 := bstep (se 2 (by rfl) ⟨5772039, by rfl⟩ : syracuseStep 15392105 = 11544079) B11544079
theorem B2022893 : Blo 397767 2022893 := bstep (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) B758585
theorem B2023379 : Blo 397767 2023379 := bstep (se 1 (by rfl) ⟨1517534, by rfl⟩ : syracuseStep 2023379 = 3035069) B3035069
theorem B1728479 : Blo 397767 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B5136443 : Blo 397767 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B1139359 : Blo 397767 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B1368857 : Blo 397767 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B1926013 : Blo 397767 1926013 := bstep (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) B722255
theorem B2548745 : Blo 397767 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B451687 : Blo 397767 451687 := bstep (se 1 (by rfl) ⟨338765, by rfl⟩ : syracuseStep 451687 = 677531) B677531
theorem B2548847 : Blo 397767 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B812207 : Blo 397767 812207 := bstep (se 1 (by rfl) ⟨609155, by rfl⟩ : syracuseStep 812207 = 1218311) B1218311
theorem B1434809 : Blo 397767 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B1008875 : Blo 397767 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B1140065 : Blo 397767 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B681851 : Blo 397767 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B4876199 : Blo 397767 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B7301087 : Blo 397767 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B19785707 : Blo 397767 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B3467387 : Blo 397767 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B2549951 : Blo 397767 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B3631391 : Blo 397767 3631391 := bstep (se 1 (by rfl) ⟨2723543, by rfl⟩ : syracuseStep 3631391 = 5447087) B5447087
theorem B2746667 : Blo 397767 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B977231 : Blo 397767 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B2550487 : Blo 397767 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B3828653 : Blo 397767 3828653 := bstep (se 3 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 3828653 = 1435745) B1435745
theorem B4550417 : Blo 397767 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B2027753 : Blo 397767 2027753 := bstep (se 2 (by rfl) ⟨760407, by rfl⟩ : syracuseStep 2027753 = 1520815) B1520815
theorem B3895543 : Blo 397767 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B1143163 : Blo 397767 1143163 := bstep (se 1 (by rfl) ⟨857372, by rfl⟩ : syracuseStep 1143163 = 1714745) B1714745
theorem B2159243 : Blo 397767 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B1012571 : Blo 397767 1012571 := bstep (se 1 (by rfl) ⟨759428, by rfl⟩ : syracuseStep 1012571 = 1518857) B1518857
theorem B1536889 : Blo 397767 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B1012601 : Blo 397767 1012601 := bstep (se 2 (by rfl) ⟨379725, by rfl⟩ : syracuseStep 1012601 = 759451) B759451
theorem B4551875 : Blo 397767 4551875 := bstep (se 1 (by rfl) ⟨3413906, by rfl⟩ : syracuseStep 4551875 = 6827813) B6827813
theorem B5141879 : Blo 397767 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B4322803 : Blo 397767 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B15431471 : Blo 397767 15431471 := bstep (se 1 (by rfl) ⟨11573603, by rfl⟩ : syracuseStep 15431471 = 23147207) B23147207
theorem B4849247 : Blo 397767 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B1344383 : Blo 397767 1344383 := bstep (se 1 (by rfl) ⟨1008287, by rfl⟩ : syracuseStep 1344383 = 2016575) B2016575
theorem B1278935 : Blo 397767 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B1279115 : Blo 397767 1279115 := bstep (se 1 (by rfl) ⟨959336, by rfl⟩ : syracuseStep 1279115 = 1918673) B1918673
theorem B1705313 : Blo 397767 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B1344923 : Blo 397767 1344923 := bstep (se 1 (by rfl) ⟨1008692, by rfl⟩ : syracuseStep 1344923 = 2017385) B2017385
theorem B2033261 : Blo 397767 2033261 := bstep (se 3 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 2033261 = 762473) B762473
theorem B1443575 : Blo 397767 1443575 := bstep (se 1 (by rfl) ⟨1082681, by rfl⟩ : syracuseStep 1443575 = 2165363) B2165363
theorem B1738559 : Blo 397767 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B428447 : Blo 397767 428447 := bstep (se 1 (by rfl) ⟨321335, by rfl⟩ : syracuseStep 428447 = 642671) B642671
theorem B756307 : Blo 397767 756307 := bstep (se 1 (by rfl) ⟨567230, by rfl⟩ : syracuseStep 756307 = 1134461) B1134461
theorem B428635 : Blo 397767 428635 := bstep (se 1 (by rfl) ⟨321476, by rfl⟩ : syracuseStep 428635 = 642953) B642953
theorem B757279 : Blo 397767 757279 := bstep (se 1 (by rfl) ⟨567959, by rfl⟩ : syracuseStep 757279 = 1135919) B1135919
theorem B2493985 : Blo 397767 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B1511095 : Blo 397767 1511095 := bstep (se 1 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 1511095 = 2266643) B2266643
theorem B2559869 : Blo 397767 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B1281959 : Blo 397767 1281959 := bstep (se 1 (by rfl) ⟨961469, by rfl⟩ : syracuseStep 1281959 = 1922939) B1922939
theorem B397851 : Blo 397767 397851 := bstep (se 1 (by rfl) ⟨298388, by rfl⟩ : syracuseStep 397851 = 596777) B596777
theorem B19075733 : Blo 397767 19075733 := bstep (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) B894175
theorem B397991 : Blo 397767 397991 := bstep (se 1 (by rfl) ⟨298493, by rfl⟩ : syracuseStep 397991 = 596987) B596987
theorem B398015 : Blo 397767 398015 := bstep (se 1 (by rfl) ⟨298511, by rfl⟩ : syracuseStep 398015 = 597023) B597023
theorem B398031 : Blo 397767 398031 := bstep (se 1 (by rfl) ⟨298523, by rfl⟩ : syracuseStep 398031 = 597047) B597047
theorem B398111 : Blo 397767 398111 := bstep (se 1 (by rfl) ⟨298583, by rfl⟩ : syracuseStep 398111 = 597167) B597167
theorem B398207 : Blo 397767 398207 := bstep (se 1 (by rfl) ⟨298655, by rfl⟩ : syracuseStep 398207 = 597311) B597311
theorem B10261403 : Blo 397767 10261403 := bstep (se 1 (by rfl) ⟨7696052, by rfl⟩ : syracuseStep 10261403 = 15392105) B15392105
theorem B398303 : Blo 397767 398303 := bstep (se 1 (by rfl) ⟨298727, by rfl⟩ : syracuseStep 398303 = 597455) B597455
theorem B1348595 : Blo 397767 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B398559 : Blo 397767 398559 := bstep (se 1 (by rfl) ⟨298919, by rfl⟩ : syracuseStep 398559 = 597839) B597839
theorem B398591 : Blo 397767 398591 := bstep (se 1 (by rfl) ⟨298943, by rfl⟩ : syracuseStep 398591 = 597887) B597887
theorem B398639 : Blo 397767 398639 := bstep (se 1 (by rfl) ⟨298979, by rfl⟩ : syracuseStep 398639 = 597959) B597959
theorem B1348919 : Blo 397767 1348919 := bstep (se 1 (by rfl) ⟨1011689, by rfl⟩ : syracuseStep 1348919 = 2023379) B2023379
theorem B1152319 : Blo 397767 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B398799 : Blo 397767 398799 := bstep (se 1 (by rfl) ⟨299099, by rfl⟩ : syracuseStep 398799 = 598199) B598199
theorem B398879 : Blo 397767 398879 := bstep (se 1 (by rfl) ⟨299159, by rfl⟩ : syracuseStep 398879 = 598319) B598319
theorem B399039 : Blo 397767 399039 := bstep (se 1 (by rfl) ⟨299279, by rfl⟩ : syracuseStep 399039 = 598559) B598559
theorem B2332385 : Blo 397767 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B399079 : Blo 397767 399079 := bstep (se 1 (by rfl) ⟨299309, by rfl⟩ : syracuseStep 399079 = 598619) B598619
theorem B399423 : Blo 397767 399423 := bstep (se 1 (by rfl) ⟨299567, by rfl⟩ : syracuseStep 399423 = 599135) B599135
theorem B399463 : Blo 397767 399463 := bstep (se 1 (by rfl) ⟨299597, by rfl⟩ : syracuseStep 399463 = 599195) B599195
theorem B956539 : Blo 397767 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B760043 : Blo 397767 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B399771 : Blo 397767 399771 := bstep (se 1 (by rfl) ⟨299828, by rfl⟩ : syracuseStep 399771 = 599657) B599657
theorem B399855 : Blo 397767 399855 := bstep (se 1 (by rfl) ⟨299891, by rfl⟩ : syracuseStep 399855 = 599783) B599783
theorem B1514011 : Blo 397767 1514011 := bstep (se 1 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 1514011 = 2271017) B2271017
theorem B399919 : Blo 397767 399919 := bstep (se 1 (by rfl) ⟨299939, by rfl⟩ : syracuseStep 399919 = 599879) B599879
theorem B3250799 : Blo 397767 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B400191 : Blo 397767 400191 := bstep (se 1 (by rfl) ⟨300143, by rfl⟩ : syracuseStep 400191 = 600287) B600287
theorem B400231 : Blo 397767 400231 := bstep (se 1 (by rfl) ⟨300173, by rfl⟩ : syracuseStep 400231 = 600347) B600347
theorem B596927 : Blo 397767 596927 := bstep (se 1 (by rfl) ⟨447695, by rfl⟩ : syracuseStep 596927 = 895391) B895391
theorem B400319 : Blo 397767 400319 := bstep (se 1 (by rfl) ⟨300239, by rfl⟩ : syracuseStep 400319 = 600479) B600479
theorem B400447 : Blo 397767 400447 := bstep (se 1 (by rfl) ⟨300335, by rfl⟩ : syracuseStep 400447 = 600671) B600671
theorem B4562081 : Blo 397767 4562081 := bstep (se 2 (by rfl) ⟨1710780, by rfl⟩ : syracuseStep 4562081 = 3421561) B3421561
theorem B597275 : Blo 397767 597275 := bstep (se 1 (by rfl) ⟨447956, by rfl⟩ : syracuseStep 597275 = 895913) B895913
theorem B400667 : Blo 397767 400667 := bstep (se 1 (by rfl) ⟨300500, by rfl⟩ : syracuseStep 400667 = 601001) B601001
theorem B400687 : Blo 397767 400687 := bstep (se 1 (by rfl) ⟨300515, by rfl⟩ : syracuseStep 400687 = 601031) B601031
theorem B400767 : Blo 397767 400767 := bstep (se 1 (by rfl) ⟨300575, by rfl⟩ : syracuseStep 400767 = 601151) B601151
theorem B400927 : Blo 397767 400927 := bstep (se 1 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 400927 = 601391) B601391
theorem B597659 : Blo 397767 597659 := bstep (se 1 (by rfl) ⟨448244, by rfl⟩ : syracuseStep 597659 = 896489) B896489
theorem B401051 : Blo 397767 401051 := bstep (se 1 (by rfl) ⟨300788, by rfl⟩ : syracuseStep 401051 = 601577) B601577
theorem B597695 : Blo 397767 597695 := bstep (se 1 (by rfl) ⟨448271, by rfl⟩ : syracuseStep 597695 = 896543) B896543
theorem B401087 : Blo 397767 401087 := bstep (se 1 (by rfl) ⟨300815, by rfl⟩ : syracuseStep 401087 = 601631) B601631
theorem B401147 : Blo 397767 401147 := bstep (se 1 (by rfl) ⟨300860, by rfl⟩ : syracuseStep 401147 = 601721) B601721
theorem B401311 : Blo 397767 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B401479 : Blo 397767 401479 := bstep (se 1 (by rfl) ⟨301109, by rfl⟩ : syracuseStep 401479 = 602219) B602219
theorem B1351835 : Blo 397767 1351835 := bstep (se 1 (by rfl) ⟨1013876, by rfl⟩ : syracuseStep 1351835 = 2027753) B2027753
theorem B598313 : Blo 397767 598313 := bstep (se 2 (by rfl) ⟨224367, by rfl⟩ : syracuseStep 598313 = 448735) B448735
theorem B401767 : Blo 397767 401767 := bstep (se 1 (by rfl) ⟨301325, by rfl⟩ : syracuseStep 401767 = 602651) B602651
theorem B599177 : Blo 397767 599177 := bstep (se 2 (by rfl) ⟨224691, by rfl⟩ : syracuseStep 599177 = 449383) B449383
theorem B599465 : Blo 397767 599465 := bstep (se 2 (by rfl) ⟨224799, by rfl⟩ : syracuseStep 599465 = 449599) B449599
theorem B23602823 : Blo 397767 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B599759 : Blo 397767 599759 := bstep (se 1 (by rfl) ⟨449819, by rfl⟩ : syracuseStep 599759 = 899639) B899639
theorem B600383 : Blo 397767 600383 := bstep (se 1 (by rfl) ⟨450287, by rfl⟩ : syracuseStep 600383 = 900575) B900575
theorem B600551 : Blo 397767 600551 := bstep (se 1 (by rfl) ⟨450413, by rfl⟩ : syracuseStep 600551 = 900827) B900827
theorem B600731 : Blo 397767 600731 := bstep (se 1 (by rfl) ⟨450548, by rfl⟩ : syracuseStep 600731 = 901097) B901097
theorem B896111 : Blo 397767 896111 := bstep (se 1 (by rfl) ⟨672083, by rfl⟩ : syracuseStep 896111 = 1344167) B1344167
theorem B1354967 : Blo 397767 1354967 := bstep (se 1 (by rfl) ⟨1016225, by rfl⟩ : syracuseStep 1354967 = 2032451) B2032451
theorem B1355129 : Blo 397767 1355129 := bstep (se 2 (by rfl) ⟨508173, by rfl⟩ : syracuseStep 1355129 = 1016347) B1016347
theorem B1519145 : Blo 397767 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B601703 : Blo 397767 601703 := bstep (se 1 (by rfl) ⟨451277, by rfl⟩ : syracuseStep 601703 = 902555) B902555
theorem B896633 : Blo 397767 896633 := bstep (se 2 (by rfl) ⟨336237, by rfl⟩ : syracuseStep 896633 = 672475) B672475
theorem B2568017 : Blo 397767 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B2273183 : Blo 397767 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B1355831 : Blo 397767 1355831 := bstep (se 1 (by rfl) ⟨1016873, by rfl⟩ : syracuseStep 1355831 = 2033747) B2033747
theorem B4534379 : Blo 397767 4534379 := bstep (se 1 (by rfl) ⟨3400784, by rfl⟩ : syracuseStep 4534379 = 6801569) B6801569
theorem B602249 : Blo 397767 602249 := bstep (se 2 (by rfl) ⟨225843, by rfl⟩ : syracuseStep 602249 = 451687) B451687
theorem B897767 : Blo 397767 897767 := bstep (se 1 (by rfl) ⟨673325, by rfl⟩ : syracuseStep 897767 = 1346651) B1346651
theorem B3650285 : Blo 397767 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B3027779 : Blo 397767 3027779 := bstep (se 1 (by rfl) ⟨2270834, by rfl⟩ : syracuseStep 3027779 = 4541669) B4541669
theorem B10990495 : Blo 397767 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B3028265 : Blo 397767 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B1521773 : Blo 397767 1521773 := bstep (se 3 (by rfl) ⟨285332, by rfl⟩ : syracuseStep 1521773 = 570665) B570665
theorem B899963 : Blo 397767 899963 := bstep (se 1 (by rfl) ⟨674972, by rfl⟩ : syracuseStep 899963 = 1349945) B1349945
theorem B3424295 : Blo 397767 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B671881 : Blo 397767 671881 := bstep (se 2 (by rfl) ⟨251955, by rfl⟩ : syracuseStep 671881 = 503911) B503911
theorem B5194057 : Blo 397767 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B2867567 : Blo 397767 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B1524217 : Blo 397767 1524217 := bstep (se 2 (by rfl) ⟨571581, by rfl⟩ : syracuseStep 1524217 = 1143163) B1143163
theorem B7324445 : Blo 397767 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B541471 : Blo 397767 541471 := bstep (se 1 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 541471 = 812207) B812207
theorem B901943 : Blo 397767 901943 := bstep (se 1 (by rfl) ⟨676457, by rfl⟩ : syracuseStep 901943 = 1352915) B1352915
theorem B672583 : Blo 397767 672583 := bstep (se 1 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 672583 = 1008875) B1008875
theorem B2049185 : Blo 397767 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B11519171 : Blo 397767 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B902375 : Blo 397767 902375 := bstep (se 1 (by rfl) ⟨676781, by rfl⟩ : syracuseStep 902375 = 1353563) B1353563
theorem B4867391 : Blo 397767 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B13190471 : Blo 397767 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B2311591 : Blo 397767 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B10274525 : Blo 397767 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B22136609 : Blo 397767 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B903023 : Blo 397767 903023 := bstep (se 1 (by rfl) ⟨677267, by rfl⟩ : syracuseStep 903023 = 1354535) B1354535
theorem B3033611 : Blo 397767 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B674345 : Blo 397767 674345 := bstep (se 2 (by rfl) ⟨252879, by rfl⟩ : syracuseStep 674345 = 505759) B505759
theorem B1722977 : Blo 397767 1722977 := bstep (se 2 (by rfl) ⟨646116, by rfl⟩ : syracuseStep 1722977 = 1292233) B1292233
theorem B903905 : Blo 397767 903905 := bstep (se 2 (by rfl) ⟨338964, by rfl⟩ : syracuseStep 903905 = 677929) B677929
theorem B1166543 : Blo 397767 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B675047 : Blo 397767 675047 := bstep (se 1 (by rfl) ⟨506285, by rfl⟩ : syracuseStep 675047 = 1012571) B1012571
theorem B675067 : Blo 397767 675067 := bstep (se 1 (by rfl) ⟨506300, by rfl⟩ : syracuseStep 675067 = 1012601) B1012601
theorem B3034583 : Blo 397767 3034583 := bstep (se 1 (by rfl) ⟨2275937, by rfl⟩ : syracuseStep 3034583 = 4551875) B4551875
theorem B3427919 : Blo 397767 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B6148477 : Blo 397767 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B3232831 : Blo 397767 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B447655 : Blo 397767 447655 := bstep (se 1 (by rfl) ⟨335741, by rfl⟩ : syracuseStep 447655 = 671483) B671483
theorem B1922555 : Blo 397767 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1136375 : Blo 397767 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B677855 : Blo 397767 677855 := bstep (se 1 (by rfl) ⟨508391, by rfl⟩ : syracuseStep 677855 = 1016783) B1016783
theorem B2021435 : Blo 397767 2021435 := bstep (se 1 (by rfl) ⟨1516076, by rfl⟩ : syracuseStep 2021435 = 3032153) B3032153
theorem B2021759 : Blo 397767 2021759 := bstep (se 1 (by rfl) ⟨1516319, by rfl⟩ : syracuseStep 2021759 = 3032639) B3032639
theorem B449275 : Blo 397767 449275 := bstep (se 1 (by rfl) ⟨336956, by rfl⟩ : syracuseStep 449275 = 673913) B673913
theorem B515099 : Blo 397767 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B1367549 : Blo 397767 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B6480323 : Blo 397767 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B4121351 : Blo 397767 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1008521 : Blo 397767 1008521 := bstep (se 2 (by rfl) ⟨378195, by rfl⟩ : syracuseStep 1008521 = 756391) B756391
theorem B3400649 : Blo 397767 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B11035705 : Blo 397767 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B8316067 : Blo 397767 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B2025323 : Blo 397767 2025323 := bstep (se 1 (by rfl) ⟨1518992, by rfl⟩ : syracuseStep 2025323 = 3037985) B3037985
theorem B3008477 : Blo 397767 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B2156777 : Blo 397767 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B3041873 : Blo 397767 3041873 := bstep (se 2 (by rfl) ⟨1140702, by rfl⟩ : syracuseStep 3041873 = 2281405) B2281405
theorem B1141751 : Blo 397767 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B1699163 : Blo 397767 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B10415465 : Blo 397767 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B1699231 : Blo 397767 1699231 := bstep (se 1 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 1699231 = 2548847) B2548847
theorem B1142207 : Blo 397767 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B1011487 : Blo 397767 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B454567 : Blo 397767 454567 := bstep (se 1 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 454567 = 681851) B681851
theorem B1699967 : Blo 397767 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B2420927 : Blo 397767 2420927 := bstep (se 1 (by rfl) ⟨1815695, by rfl⟩ : syracuseStep 2420927 = 3631391) B3631391
theorem B651487 : Blo 397767 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B1143209 : Blo 397767 1143209 := bstep (se 2 (by rfl) ⟨428703, by rfl⟩ : syracuseStep 1143209 = 857407) B857407
theorem B2552435 : Blo 397767 2552435 := bstep (se 1 (by rfl) ⟨1914326, by rfl⟩ : syracuseStep 2552435 = 3828653) B3828653
theorem B5763737 : Blo 397767 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B6845309 : Blo 397767 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B1143791 : Blo 397767 1143791 := bstep (se 1 (by rfl) ⟨857843, by rfl⟩ : syracuseStep 1143791 = 1715687) B1715687
theorem B1012783 : Blo 397767 1012783 := bstep (se 1 (by rfl) ⟨759587, by rfl⟩ : syracuseStep 1012783 = 1519175) B1519175
theorem B1439495 : Blo 397767 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B1013755 : Blo 397767 1013755 := bstep (se 1 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 1013755 = 1520633) B1520633
theorem B1013897 : Blo 397767 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B10287647 : Blo 397767 10287647 := bstep (se 1 (by rfl) ⟨7715735, by rfl⟩ : syracuseStep 10287647 = 15431471) B15431471
theorem B5209019 : Blo 397767 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B19758275 : Blo 397767 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1342763 : Blo 397767 1342763 := bstep (se 1 (by rfl) ⟨1007072, by rfl⟩ : syracuseStep 1342763 = 2014145) B2014145
theorem B4882963 : Blo 397767 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B852623 : Blo 397767 852623 := bstep (se 1 (by rfl) ⟨639467, by rfl⟩ : syracuseStep 852623 = 1278935) B1278935
theorem B2032289 : Blo 397767 2032289 := bstep (se 2 (by rfl) ⟨762108, by rfl⟩ : syracuseStep 2032289 = 1524217) B1524217
theorem B852743 : Blo 397767 852743 := bstep (se 1 (by rfl) ⟨639557, by rfl⟩ : syracuseStep 852743 = 1279115) B1279115
theorem B721961 : Blo 397767 721961 := bstep (se 2 (by rfl) ⟨270735, by rfl⟩ : syracuseStep 721961 = 541471) B541471
theorem B6849683 : Blo 397767 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B14714273 : Blo 397767 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B1148651 : Blo 397767 1148651 := bstep (se 1 (by rfl) ⟨861488, by rfl⟩ : syracuseStep 1148651 = 1722977) B1722977
theorem B3082121 : Blo 397767 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B9734093 : Blo 397767 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B1706579 : Blo 397767 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B854639 : Blo 397767 854639 := bstep (se 1 (by rfl) ⟨640979, by rfl⟩ : syracuseStep 854639 = 1281959) B1281959
theorem B12717155 : Blo 397767 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B12979709 : Blo 397767 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B1281703 : Blo 397767 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B757583 : Blo 397767 757583 := bstep (se 1 (by rfl) ⟨568187, by rfl⟩ : syracuseStep 757583 = 1136375) B1136375
theorem B1347623 : Blo 397767 1347623 := bstep (se 1 (by rfl) ⟨1010717, by rfl⟩ : syracuseStep 1347623 = 2021435) B2021435
theorem B1347839 : Blo 397767 1347839 := bstep (se 1 (by rfl) ⟨1010879, by rfl⟩ : syracuseStep 1347839 = 2021759) B2021759
theorem B2167199 : Blo 397767 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B2265641 : Blo 397767 2265641 := bstep (se 2 (by rfl) ⟨849615, by rfl⟩ : syracuseStep 2265641 = 1699231) B1699231
theorem B397951 : Blo 397767 397951 := bstep (se 1 (by rfl) ⟨298463, by rfl⟩ : syracuseStep 397951 = 596927) B596927
theorem B398183 : Blo 397767 398183 := bstep (se 1 (by rfl) ⟨298637, by rfl⟩ : syracuseStep 398183 = 597275) B597275
theorem B1348649 : Blo 397767 1348649 := bstep (se 2 (by rfl) ⟨505743, by rfl⟩ : syracuseStep 1348649 = 1011487) B1011487
theorem B398439 : Blo 397767 398439 := bstep (se 1 (by rfl) ⟨298829, by rfl⟩ : syracuseStep 398439 = 597659) B597659
theorem B398463 : Blo 397767 398463 := bstep (se 1 (by rfl) ⟨298847, by rfl⟩ : syracuseStep 398463 = 597695) B597695
theorem B398875 : Blo 397767 398875 := bstep (se 1 (by rfl) ⟨299156, by rfl⟩ : syracuseStep 398875 = 598313) B598313
theorem B8197969 : Blo 397767 8197969 := bstep (se 2 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 8197969 = 6148477) B6148477
theorem B2267099 : Blo 397767 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B399451 : Blo 397767 399451 := bstep (se 1 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 399451 = 599177) B599177
theorem B399643 : Blo 397767 399643 := bstep (se 1 (by rfl) ⟨299732, by rfl⟩ : syracuseStep 399643 = 599465) B599465
theorem B15735215 : Blo 397767 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B399839 : Blo 397767 399839 := bstep (se 1 (by rfl) ⟨299879, by rfl⟩ : syracuseStep 399839 = 599759) B599759
theorem B14653993 : Blo 397767 14653993 := bstep (se 2 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 14653993 = 10990495) B10990495
theorem B1350215 : Blo 397767 1350215 := bstep (se 1 (by rfl) ⟨1012661, by rfl⟩ : syracuseStep 1350215 = 2025323) B2025323
theorem B2005651 : Blo 397767 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B1350377 : Blo 397767 1350377 := bstep (se 2 (by rfl) ⟨506391, by rfl⟩ : syracuseStep 1350377 = 1012783) B1012783
theorem B400255 : Blo 397767 400255 := bstep (se 1 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 400255 = 600383) B600383
theorem B596873 : Blo 397767 596873 := bstep (se 2 (by rfl) ⟨223827, by rfl⟩ : syracuseStep 596873 = 447655) B447655
theorem B400367 : Blo 397767 400367 := bstep (se 1 (by rfl) ⟨300275, by rfl⟩ : syracuseStep 400367 = 600551) B600551
theorem B400487 : Blo 397767 400487 := bstep (se 1 (by rfl) ⟨300365, by rfl⟩ : syracuseStep 400487 = 600731) B600731
theorem B761167 : Blo 397767 761167 := bstep (se 1 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 761167 = 1141751) B1141751
theorem B597407 : Blo 397767 597407 := bstep (se 1 (by rfl) ⟨448055, by rfl⟩ : syracuseStep 597407 = 896111) B896111
theorem B761471 : Blo 397767 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B401135 : Blo 397767 401135 := bstep (se 1 (by rfl) ⟨300851, by rfl⟩ : syracuseStep 401135 = 601703) B601703
theorem B597755 : Blo 397767 597755 := bstep (se 1 (by rfl) ⟨448316, by rfl⟩ : syracuseStep 597755 = 896633) B896633
theorem B1712011 : Blo 397767 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B1515455 : Blo 397767 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B1351673 : Blo 397767 1351673 := bstep (se 2 (by rfl) ⟨506877, by rfl⟩ : syracuseStep 1351673 = 1013755) B1013755
theorem B3022919 : Blo 397767 3022919 := bstep (se 1 (by rfl) ⟨2267189, by rfl⟩ : syracuseStep 3022919 = 4534379) B4534379
theorem B401499 : Blo 397767 401499 := bstep (se 1 (by rfl) ⟨301124, by rfl⟩ : syracuseStep 401499 = 602249) B602249
theorem B1613951 : Blo 397767 1613951 := bstep (se 1 (by rfl) ⟨1210463, by rfl⟩ : syracuseStep 1613951 = 2420927) B2420927
theorem B762139 : Blo 397767 762139 := bstep (se 1 (by rfl) ⟨571604, by rfl⟩ : syracuseStep 762139 = 1143209) B1143209
theorem B3842491 : Blo 397767 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B598511 : Blo 397767 598511 := bstep (se 1 (by rfl) ⟨448883, by rfl⟩ : syracuseStep 598511 = 897767) B897767
theorem B4563539 : Blo 397767 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B762527 : Blo 397767 762527 := bstep (se 1 (by rfl) ⟨571895, by rfl⟩ : syracuseStep 762527 = 1143791) B1143791
theorem B599033 : Blo 397767 599033 := bstep (se 2 (by rfl) ⟨224637, by rfl⟩ : syracuseStep 599033 = 449275) B449275
theorem B959663 : Blo 397767 959663 := bstep (se 1 (by rfl) ⟨719747, by rfl⟩ : syracuseStep 959663 = 1439495) B1439495
theorem B6858431 : Blo 397767 6858431 := bstep (se 1 (by rfl) ⟨5143823, by rfl⟩ : syracuseStep 6858431 = 10287647) B10287647
theorem B599975 : Blo 397767 599975 := bstep (se 1 (by rfl) ⟨449981, by rfl⟩ : syracuseStep 599975 = 899963) B899963
theorem B895175 : Blo 397767 895175 := bstep (se 1 (by rfl) ⟨671381, by rfl⟩ : syracuseStep 895175 = 1342763) B1342763
theorem B895841 : Blo 397767 895841 := bstep (se 2 (by rfl) ⟨335940, by rfl⟩ : syracuseStep 895841 = 671881) B671881
theorem B6925409 : Blo 397767 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B601295 : Blo 397767 601295 := bstep (se 1 (by rfl) ⟨450971, by rfl⟩ : syracuseStep 601295 = 901943) B901943
theorem B896255 : Blo 397767 896255 := bstep (se 1 (by rfl) ⟨672191, by rfl⟩ : syracuseStep 896255 = 1344383) B1344383
theorem B7679447 : Blo 397767 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B601583 : Blo 397767 601583 := bstep (se 1 (by rfl) ⟨451187, by rfl⟩ : syracuseStep 601583 = 902375) B902375
theorem B8793647 : Blo 397767 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B896615 : Blo 397767 896615 := bstep (se 1 (by rfl) ⟨672461, by rfl⟩ : syracuseStep 896615 = 1344923) B1344923
theorem B7646845 : Blo 397767 7646845 := bstep (se 3 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 7646845 = 2867567) B2867567
theorem B1355507 : Blo 397767 1355507 := bstep (se 1 (by rfl) ⟨1016630, by rfl⟩ : syracuseStep 1355507 = 2033261) B2033261
theorem B896777 : Blo 397767 896777 := bstep (se 2 (by rfl) ⟨336291, by rfl⟩ : syracuseStep 896777 = 672583) B672583
theorem B962383 : Blo 397767 962383 := bstep (se 1 (by rfl) ⟨721787, by rfl⟩ : syracuseStep 962383 = 1443575) B1443575
theorem B1159039 : Blo 397767 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B602015 : Blo 397767 602015 := bstep (se 1 (by rfl) ⟨451511, by rfl⟩ : syracuseStep 602015 = 903023) B903023
theorem B11088089 : Blo 397767 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B602603 : Blo 397767 602603 := bstep (se 1 (by rfl) ⟨451952, by rfl⟩ : syracuseStep 602603 = 903905) B903905
theorem B899063 : Blo 397767 899063 := bstep (se 1 (by rfl) ⟨674297, by rfl⟩ : syracuseStep 899063 = 1348595) B1348595
theorem B899279 : Blo 397767 899279 := bstep (se 1 (by rfl) ⟨674459, by rfl⟩ : syracuseStep 899279 = 1348919) B1348919
theorem B1554923 : Blo 397767 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B900089 : Blo 397767 900089 := bstep (se 2 (by rfl) ⟨337533, by rfl⟩ : syracuseStep 900089 = 675067) B675067
theorem B3325313 : Blo 397767 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B59030957 : Blo 397767 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B2014793 : Blo 397767 2014793 := bstep (se 2 (by rfl) ⟨755547, by rfl⟩ : syracuseStep 2014793 = 1511095) B1511095
theorem B606089 : Blo 397767 606089 := bstep (se 2 (by rfl) ⟨227283, by rfl⟩ : syracuseStep 606089 = 454567) B454567
theorem B901223 : Blo 397767 901223 := bstep (se 1 (by rfl) ⟨675917, by rfl⟩ : syracuseStep 901223 = 1351835) B1351835
theorem B868649 : Blo 397767 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B672347 : Blo 397767 672347 := bstep (se 1 (by rfl) ⟨504260, by rfl⟩ : syracuseStep 672347 = 1008521) B1008521
theorem B4310441 : Blo 397767 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B903311 : Blo 397767 903311 := bstep (se 1 (by rfl) ⟨677483, by rfl⟩ : syracuseStep 903311 = 1354967) B1354967
theorem B1132775 : Blo 397767 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B903419 : Blo 397767 903419 := bstep (se 1 (by rfl) ⟨677564, by rfl⟩ : syracuseStep 903419 = 1355129) B1355129
theorem B903887 : Blo 397767 903887 := bstep (se 1 (by rfl) ⟨677915, by rfl⟩ : syracuseStep 903887 = 1355831) B1355831
theorem B1133311 : Blo 397767 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B2018519 : Blo 397767 2018519 := bstep (se 1 (by rfl) ⟨1513889, by rfl⟩ : syracuseStep 2018519 = 3027779) B3027779
theorem B2018681 : Blo 397767 2018681 := bstep (se 2 (by rfl) ⟨757005, by rfl⟩ : syracuseStep 2018681 = 1514011) B1514011
theorem B2018843 : Blo 397767 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B675931 : Blo 397767 675931 := bstep (se 1 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 675931 = 1013897) B1013897
theorem B2282863 : Blo 397767 2282863 := bstep (se 1 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 2282863 = 3424295) B3424295
theorem B5101541 : Blo 397767 5101541 := bstep (se 4 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 5101541 = 956539) B956539
theorem B2022407 : Blo 397767 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B449563 : Blo 397767 449563 := bstep (se 1 (by rfl) ⟨337172, by rfl⟩ : syracuseStep 449563 = 674345) B674345
theorem B777695 : Blo 397767 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B450031 : Blo 397767 450031 := bstep (se 1 (by rfl) ⟨337523, by rfl⟩ : syracuseStep 450031 = 675047) B675047
theorem B2023055 : Blo 397767 2023055 := bstep (se 1 (by rfl) ⟨1517291, by rfl⟩ : syracuseStep 2023055 = 3034583) B3034583
theorem B2285279 : Blo 397767 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B5464493 : Blo 397767 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B2286053 : Blo 397767 2286053 := bstep (se 4 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 2286053 = 428635) B428635
theorem B6840935 : Blo 397767 6840935 := bstep (se 1 (by rfl) ⟨5130701, by rfl⟩ : syracuseStep 6840935 = 10261403) B10261403
theorem B1008409 : Blo 397767 1008409 := bstep (se 2 (by rfl) ⟨378153, by rfl⟩ : syracuseStep 1008409 = 756307) B756307
theorem B4547501 : Blo 397767 4547501 := bstep (se 3 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 4547501 = 1705313) B1705313
theorem B451903 : Blo 397767 451903 := bstep (se 1 (by rfl) ⟨338927, by rfl⟩ : syracuseStep 451903 = 677855) B677855
theorem B1009705 : Blo 397767 1009705 := bstep (se 2 (by rfl) ⟨378639, by rfl⟩ : syracuseStep 1009705 = 757279) B757279
theorem B3041387 : Blo 397767 3041387 := bstep (se 1 (by rfl) ⟨2281040, by rfl⟩ : syracuseStep 3041387 = 4562081) B4562081
theorem B911699 : Blo 397767 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B4320215 : Blo 397767 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B2747567 : Blo 397767 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B2026781 : Blo 397767 2026781 := bstep (se 3 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 2026781 = 760043) B760043
theorem B1142525 : Blo 397767 1142525 := bstep (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) B428447
theorem B1437851 : Blo 397767 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B2027915 : Blo 397767 2027915 := bstep (se 1 (by rfl) ⟨1520936, by rfl⟩ : syracuseStep 2027915 = 3041873) B3041873
theorem B1536425 : Blo 397767 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B6943643 : Blo 397767 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B1012763 : Blo 397767 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B1373597 : Blo 397767 1373597 := bstep (se 3 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 1373597 = 515099) B515099
theorem B1701623 : Blo 397767 1701623 := bstep (se 1 (by rfl) ⟨1276217, by rfl⟩ : syracuseStep 1701623 = 2552435) B2552435
theorem B1014515 : Blo 397767 1014515 := bstep (se 1 (by rfl) ⟨760886, by rfl⟩ : syracuseStep 1014515 = 1521773) B1521773
theorem B3472679 : Blo 397767 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B13172183 : Blo 397767 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1016185 : Blo 397767 1016185 := bstep (se 2 (by rfl) ⟨381069, by rfl⟩ : syracuseStep 1016185 = 762139) B762139
theorem B1344545 : Blo 397767 1344545 := bstep (se 2 (by rfl) ⟨504204, by rfl⟩ : syracuseStep 1344545 = 1008409) B1008409
theorem B6489395 : Blo 397767 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B755183 : Blo 397767 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B1345679 : Blo 397767 1345679 := bstep (se 1 (by rfl) ⟨1009259, by rfl⟩ : syracuseStep 1345679 = 2018519) B2018519
theorem B1345787 : Blo 397767 1345787 := bstep (se 1 (by rfl) ⟨1009340, by rfl⟩ : syracuseStep 1345787 = 2018681) B2018681
theorem B8653139 : Blo 397767 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B1345895 : Blo 397767 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B1346273 : Blo 397767 1346273 := bstep (se 2 (by rfl) ⟨504852, by rfl⟩ : syracuseStep 1346273 = 1009705) B1009705
theorem B1444799 : Blo 397767 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B1510427 : Blo 397767 1510427 := bstep (se 1 (by rfl) ⟨1132820, by rfl⟩ : syracuseStep 1510427 = 2265641) B2265641
theorem B1511081 : Blo 397767 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B1511399 : Blo 397767 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B10490143 : Blo 397767 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B397915 : Blo 397767 397915 := bstep (se 1 (by rfl) ⟨298436, by rfl⟩ : syracuseStep 397915 = 596873) B596873
theorem B1348271 : Blo 397767 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B10195793 : Blo 397767 10195793 := bstep (se 2 (by rfl) ⟨3823422, by rfl⟩ : syracuseStep 10195793 = 7646845) B7646845
theorem B1708937 : Blo 397767 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B398271 : Blo 397767 398271 := bstep (se 1 (by rfl) ⟨298703, by rfl⟩ : syracuseStep 398271 = 597407) B597407
theorem B1348703 : Blo 397767 1348703 := bstep (se 1 (by rfl) ⟨1011527, by rfl⟩ : syracuseStep 1348703 = 2023055) B2023055
theorem B1283177 : Blo 397767 1283177 := bstep (se 2 (by rfl) ⟨481191, by rfl⟩ : syracuseStep 1283177 = 962383) B962383
theorem B398503 : Blo 397767 398503 := bstep (se 1 (by rfl) ⟨298877, by rfl⟩ : syracuseStep 398503 = 597755) B597755
theorem B3642995 : Blo 397767 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B399007 : Blo 397767 399007 := bstep (se 1 (by rfl) ⟨299255, by rfl⟩ : syracuseStep 399007 = 598511) B598511
theorem B4560623 : Blo 397767 4560623 := bstep (se 1 (by rfl) ⟨3420467, by rfl⟩ : syracuseStep 4560623 = 6840935) B6840935
theorem B399355 : Blo 397767 399355 := bstep (se 1 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 399355 = 599033) B599033
theorem B399983 : Blo 397767 399983 := bstep (se 1 (by rfl) ⟨299987, by rfl⟩ : syracuseStep 399983 = 599975) B599975
theorem B596783 : Blo 397767 596783 := bstep (se 1 (by rfl) ⟨447587, by rfl⟩ : syracuseStep 596783 = 895175) B895175
theorem B597227 : Blo 397767 597227 := bstep (se 1 (by rfl) ⟨447920, by rfl⟩ : syracuseStep 597227 = 895841) B895841
theorem B400863 : Blo 397767 400863 := bstep (se 1 (by rfl) ⟨300647, by rfl⟩ : syracuseStep 400863 = 601295) B601295
theorem B597503 : Blo 397767 597503 := bstep (se 1 (by rfl) ⟨448127, by rfl⟩ : syracuseStep 597503 = 896255) B896255
theorem B1351187 : Blo 397767 1351187 := bstep (se 1 (by rfl) ⟨1013390, by rfl⟩ : syracuseStep 1351187 = 2026781) B2026781
theorem B5119631 : Blo 397767 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B401055 : Blo 397767 401055 := bstep (se 1 (by rfl) ⟨300791, by rfl⟩ : syracuseStep 401055 = 601583) B601583
theorem B597743 : Blo 397767 597743 := bstep (se 1 (by rfl) ⟨448307, by rfl⟩ : syracuseStep 597743 = 896615) B896615
theorem B597851 : Blo 397767 597851 := bstep (se 1 (by rfl) ⟨448388, by rfl⟩ : syracuseStep 597851 = 896777) B896777
theorem B401343 : Blo 397767 401343 := bstep (se 1 (by rfl) ⟨301007, by rfl⟩ : syracuseStep 401343 = 602015) B602015
theorem B958567 : Blo 397767 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B1351943 : Blo 397767 1351943 := bstep (se 1 (by rfl) ⟨1013957, by rfl⟩ : syracuseStep 1351943 = 2027915) B2027915
theorem B1024283 : Blo 397767 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B401735 : Blo 397767 401735 := bstep (se 1 (by rfl) ⟨301301, by rfl⟩ : syracuseStep 401735 = 602603) B602603
theorem B4629095 : Blo 397767 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B19538657 : Blo 397767 19538657 := bstep (se 2 (by rfl) ⟨7326996, by rfl⟩ : syracuseStep 19538657 = 14653993) B14653993
theorem B2073853 : Blo 397767 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B599375 : Blo 397767 599375 := bstep (se 1 (by rfl) ⟨449531, by rfl⟩ : syracuseStep 599375 = 899063) B899063
theorem B599417 : Blo 397767 599417 := bstep (se 2 (by rfl) ⟨224781, by rfl⟩ : syracuseStep 599417 = 449563) B449563
theorem B599519 : Blo 397767 599519 := bstep (se 1 (by rfl) ⟨449639, by rfl⟩ : syracuseStep 599519 = 899279) B899279
theorem B600041 : Blo 397767 600041 := bstep (se 2 (by rfl) ⟨225015, by rfl⟩ : syracuseStep 600041 = 450031) B450031
theorem B600059 : Blo 397767 600059 := bstep (se 1 (by rfl) ⟨450044, by rfl⟩ : syracuseStep 600059 = 900089) B900089
theorem B1616237 : Blo 397767 1616237 := bstep (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) B606089
theorem B600815 : Blo 397767 600815 := bstep (se 1 (by rfl) ⟨450611, by rfl⟩ : syracuseStep 600815 = 901223) B901223
theorem B568415 : Blo 397767 568415 := bstep (se 1 (by rfl) ⟨426311, by rfl⟩ : syracuseStep 568415 = 852623) B852623
theorem B1354859 : Blo 397767 1354859 := bstep (se 1 (by rfl) ⟨1016144, by rfl⟩ : syracuseStep 1354859 = 2032289) B2032289
theorem B568495 : Blo 397767 568495 := bstep (se 1 (by rfl) ⟨426371, by rfl⟩ : syracuseStep 568495 = 852743) B852743
theorem B5123321 : Blo 397767 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B4566455 : Blo 397767 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B9809515 : Blo 397767 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B765767 : Blo 397767 765767 := bstep (se 1 (by rfl) ⟨574325, by rfl⟩ : syracuseStep 765767 = 1148651) B1148651
theorem B602207 : Blo 397767 602207 := bstep (se 1 (by rfl) ⟨451655, by rfl⟩ : syracuseStep 602207 = 903311) B903311
theorem B602279 : Blo 397767 602279 := bstep (se 1 (by rfl) ⟨451709, by rfl⟩ : syracuseStep 602279 = 903419) B903419
theorem B569759 : Blo 397767 569759 := bstep (se 1 (by rfl) ⟨427319, by rfl⟩ : syracuseStep 569759 = 854639) B854639
theorem B602537 : Blo 397767 602537 := bstep (se 2 (by rfl) ⟨225951, by rfl⟩ : syracuseStep 602537 = 451903) B451903
theorem B602591 : Blo 397767 602591 := bstep (se 1 (by rfl) ⟨451943, by rfl⟩ : syracuseStep 602591 = 903887) B903887
theorem B505055 : Blo 397767 505055 := bstep (se 1 (by rfl) ⟨378791, by rfl⟩ : syracuseStep 505055 = 757583) B757583
theorem B898415 : Blo 397767 898415 := bstep (se 1 (by rfl) ⟨673811, by rfl⟩ : syracuseStep 898415 = 1347623) B1347623
theorem B898559 : Blo 397767 898559 := bstep (se 1 (by rfl) ⟨673919, by rfl⟩ : syracuseStep 898559 = 1347839) B1347839
theorem B899099 : Blo 397767 899099 := bstep (se 1 (by rfl) ⟨674324, by rfl⟩ : syracuseStep 899099 = 1348649) B1348649
theorem B900143 : Blo 397767 900143 := bstep (se 1 (by rfl) ⟨675107, by rfl⟩ : syracuseStep 900143 = 1350215) B1350215
theorem B900251 : Blo 397767 900251 := bstep (se 1 (by rfl) ⟨675188, by rfl⟩ : syracuseStep 900251 = 1350377) B1350377
theorem B507647 : Blo 397767 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B1523519 : Blo 397767 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B901115 : Blo 397767 901115 := bstep (se 1 (by rfl) ⟨675836, by rfl⟩ : syracuseStep 901115 = 1351673) B1351673
theorem B2015279 : Blo 397767 2015279 := bstep (se 1 (by rfl) ⟨1511459, by rfl⟩ : syracuseStep 2015279 = 3022919) B3022919
theorem B901241 : Blo 397767 901241 := bstep (se 2 (by rfl) ⟨337965, by rfl⟩ : syracuseStep 901241 = 675931) B675931
theorem B1524035 : Blo 397767 1524035 := bstep (se 1 (by rfl) ⟨1143026, by rfl⟩ : syracuseStep 1524035 = 2286053) B2286053
theorem B508351 : Blo 397767 508351 := bstep (se 1 (by rfl) ⟨381263, by rfl⟩ : syracuseStep 508351 = 762527) B762527
theorem B3031667 : Blo 397767 3031667 := bstep (se 1 (by rfl) ⟨2273750, by rfl⟩ : syracuseStep 3031667 = 4547501) B4547501
theorem B639775 : Blo 397767 639775 := bstep (se 1 (by rfl) ⟨479831, by rfl⟩ : syracuseStep 639775 = 959663) B959663
theorem B4572287 : Blo 397767 4572287 := bstep (se 1 (by rfl) ⟨3429215, by rfl⟩ : syracuseStep 4572287 = 6858431) B6858431
theorem B4146461 : Blo 397767 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B607799 : Blo 397767 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B10930625 : Blo 397767 10930625 := bstep (se 2 (by rfl) ⟨4098984, by rfl⟩ : syracuseStep 10930625 = 8197969) B8197969
theorem B903671 : Blo 397767 903671 := bstep (se 1 (by rfl) ⟨677753, by rfl⟩ : syracuseStep 903671 = 1355507) B1355507
theorem B7392059 : Blo 397767 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B7326845 : Blo 397767 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B675175 : Blo 397767 675175 := bstep (se 1 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 675175 = 1012763) B1012763
theorem B9260477 : Blo 397767 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B2674201 : Blo 397767 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B8867501 : Blo 397767 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B1134415 : Blo 397767 1134415 := bstep (se 1 (by rfl) ⟨850811, by rfl⟩ : syracuseStep 1134415 = 1701623) B1701623
theorem B676343 : Blo 397767 676343 := bstep (se 1 (by rfl) ⟨507257, by rfl⟩ : syracuseStep 676343 = 1014515) B1014515
theorem B6181541 : Blo 397767 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B2282681 : Blo 397767 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B448231 : Blo 397767 448231 := bstep (se 1 (by rfl) ⟨336173, by rfl⟩ : syracuseStep 448231 = 672347) B672347
theorem B6510617 : Blo 397767 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B481307 : Blo 397767 481307 := bstep (se 1 (by rfl) ⟨360980, by rfl⟩ : syracuseStep 481307 = 721961) B721961
theorem B2873627 : Blo 397767 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B2054747 : Blo 397767 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B1137719 : Blo 397767 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B8478103 : Blo 397767 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B9265589 : Blo 397767 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B3401027 : Blo 397767 3401027 := bstep (se 1 (by rfl) ⟨2550770, by rfl⟩ : syracuseStep 3401027 = 5101541) B5101541
theorem B1010303 : Blo 397767 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B1075967 : Blo 397767 1075967 := bstep (se 1 (by rfl) ⟨806975, by rfl⟩ : syracuseStep 1075967 = 1613951) B1613951
theorem B3042359 : Blo 397767 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B2027591 : Blo 397767 2027591 := bstep (se 1 (by rfl) ⟨1520693, by rfl⟩ : syracuseStep 2027591 = 3041387) B3041387
theorem B3043817 : Blo 397767 3043817 := bstep (se 2 (by rfl) ⟨1141431, by rfl⟩ : syracuseStep 3043817 = 2282863) B2282863
theorem B2880143 : Blo 397767 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B4616939 : Blo 397767 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B5862431 : Blo 397767 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B915731 : Blo 397767 915731 := bstep (se 1 (by rfl) ⟨686798, by rfl⟩ : syracuseStep 915731 = 1373597) B1373597
theorem B1014889 : Blo 397767 1014889 := bstep (se 2 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 1014889 = 761167) B761167
theorem B3046733 : Blo 397767 3046733 := bstep (se 3 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 3046733 = 1142525) B1142525
theorem B39353971 : Blo 397767 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B8781455 : Blo 397767 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B1343195 : Blo 397767 1343195 := bstep (se 1 (by rfl) ⟨1007396, by rfl⟩ : syracuseStep 1343195 = 2014793) B2014793
theorem B1343519 : Blo 397767 1343519 := bstep (se 1 (by rfl) ⟨1007639, by rfl⟩ : syracuseStep 1343519 = 2015279) B2015279
theorem B1278089 : Blo 397767 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1016023 : Blo 397767 1016023 := bstep (se 1 (by rfl) ⟨762017, by rfl⟩ : syracuseStep 1016023 = 1524035) B1524035
theorem B3048191 : Blo 397767 3048191 := bstep (se 1 (by rfl) ⟨2286143, by rfl⟩ : syracuseStep 3048191 = 4572287) B4572287
theorem B4326263 : Blo 397767 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B853033 : Blo 397767 853033 := bstep (se 2 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 853033 = 639775) B639775
theorem B5768759 : Blo 397767 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B4884563 : Blo 397767 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B1346813 : Blo 397767 1346813 := bstep (se 3 (by rfl) ⟨252527, by rfl⟩ : syracuseStep 1346813 = 505055) B505055
theorem B855451 : Blo 397767 855451 := bstep (se 1 (by rfl) ⟨641588, by rfl⟩ : syracuseStep 855451 = 1283177) B1283177
theorem B2428663 : Blo 397767 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B757993 : Blo 397767 757993 := bstep (se 2 (by rfl) ⟨284247, by rfl⟩ : syracuseStep 757993 = 568495) B568495
theorem B397855 : Blo 397767 397855 := bstep (se 1 (by rfl) ⟨298391, by rfl⟩ : syracuseStep 397855 = 596783) B596783
theorem B758479 : Blo 397767 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B398151 : Blo 397767 398151 := bstep (se 1 (by rfl) ⟨298613, by rfl⟩ : syracuseStep 398151 = 597227) B597227
theorem B398335 : Blo 397767 398335 := bstep (se 1 (by rfl) ⟨298751, by rfl⟩ : syracuseStep 398335 = 597503) B597503
theorem B3413087 : Blo 397767 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B1512553 : Blo 397767 1512553 := bstep (se 2 (by rfl) ⟨567207, by rfl⟩ : syracuseStep 1512553 = 1134415) B1134415
theorem B398495 : Blo 397767 398495 := bstep (se 1 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 398495 = 597743) B597743
theorem B398567 : Blo 397767 398567 := bstep (se 1 (by rfl) ⟨298925, by rfl⟩ : syracuseStep 398567 = 597851) B597851
theorem B1283485 : Blo 397767 1283485 := bstep (se 3 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 1283485 = 481307) B481307
theorem B3086063 : Blo 397767 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B2267351 : Blo 397767 2267351 := bstep (se 1 (by rfl) ⟨1700513, by rfl⟩ : syracuseStep 2267351 = 3401027) B3401027
theorem B399583 : Blo 397767 399583 := bstep (se 1 (by rfl) ⟨299687, by rfl⟩ : syracuseStep 399583 = 599375) B599375
theorem B399611 : Blo 397767 399611 := bstep (se 1 (by rfl) ⟨299708, by rfl⟩ : syracuseStep 399611 = 599417) B599417
theorem B399679 : Blo 397767 399679 := bstep (se 1 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 399679 = 599519) B599519
theorem B400027 : Blo 397767 400027 := bstep (se 1 (by rfl) ⟨300020, by rfl⟩ : syracuseStep 400027 = 600041) B600041
theorem B400039 : Blo 397767 400039 := bstep (se 1 (by rfl) ⟨300029, by rfl⟩ : syracuseStep 400039 = 600059) B600059
theorem B5479325 : Blo 397767 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B400543 : Blo 397767 400543 := bstep (se 1 (by rfl) ⟨300407, by rfl⟩ : syracuseStep 400543 = 600815) B600815
theorem B3415547 : Blo 397767 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B597641 : Blo 397767 597641 := bstep (se 2 (by rfl) ⟨224115, by rfl⟩ : syracuseStep 597641 = 448231) B448231
theorem B1351727 : Blo 397767 1351727 := bstep (se 1 (by rfl) ⟨1013795, by rfl⟩ : syracuseStep 1351727 = 2027591) B2027591
theorem B401471 : Blo 397767 401471 := bstep (se 1 (by rfl) ⟨301103, by rfl⟩ : syracuseStep 401471 = 602207) B602207
theorem B401519 : Blo 397767 401519 := bstep (se 1 (by rfl) ⟨301139, by rfl⟩ : syracuseStep 401519 = 602279) B602279
theorem B1515773 : Blo 397767 1515773 := bstep (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) B568415
theorem B401691 : Blo 397767 401691 := bstep (se 1 (by rfl) ⟨301268, by rfl⟩ : syracuseStep 401691 = 602537) B602537
theorem B401727 : Blo 397767 401727 := bstep (se 1 (by rfl) ⟨301295, by rfl⟩ : syracuseStep 401727 = 602591) B602591
theorem B3908287 : Blo 397767 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B598943 : Blo 397767 598943 := bstep (se 1 (by rfl) ⟨449207, by rfl⟩ : syracuseStep 598943 = 898415) B898415
theorem B599039 : Blo 397767 599039 := bstep (se 1 (by rfl) ⟨449279, by rfl⟩ : syracuseStep 599039 = 898559) B898559
theorem B599399 : Blo 397767 599399 := bstep (se 1 (by rfl) ⟨449549, by rfl⟩ : syracuseStep 599399 = 899099) B899099
theorem B1353185 : Blo 397767 1353185 := bstep (se 2 (by rfl) ⟨507444, by rfl⟩ : syracuseStep 1353185 = 1014889) B1014889
theorem B1353725 : Blo 397767 1353725 := bstep (se 3 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 1353725 = 507647) B507647
theorem B600095 : Blo 397767 600095 := bstep (se 1 (by rfl) ⟨450071, by rfl⟩ : syracuseStep 600095 = 900143) B900143
theorem B600167 : Blo 397767 600167 := bstep (se 1 (by rfl) ⟨450125, by rfl⟩ : syracuseStep 600167 = 900251) B900251
theorem B52471961 : Blo 397767 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B895463 : Blo 397767 895463 := bstep (se 1 (by rfl) ⟨671597, by rfl⟩ : syracuseStep 895463 = 1343195) B1343195
theorem B600743 : Blo 397767 600743 := bstep (se 1 (by rfl) ⟨450557, by rfl⟩ : syracuseStep 600743 = 901115) B901115
theorem B600827 : Blo 397767 600827 := bstep (se 1 (by rfl) ⟨450620, by rfl⟩ : syracuseStep 600827 = 901241) B901241
theorem B1354913 : Blo 397767 1354913 := bstep (se 2 (by rfl) ⟨508092, by rfl⟩ : syracuseStep 1354913 = 1016185) B1016185
theorem B896363 : Blo 397767 896363 := bstep (se 1 (by rfl) ⟨672272, by rfl⟩ : syracuseStep 896363 = 1344545) B1344545
theorem B2731421 : Blo 397767 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B2764307 : Blo 397767 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B405199 : Blo 397767 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B1519357 : Blo 397767 1519357 := bstep (se 3 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 1519357 = 569759) B569759
theorem B897119 : Blo 397767 897119 := bstep (se 1 (by rfl) ⟨672839, by rfl⟩ : syracuseStep 897119 = 1345679) B1345679
theorem B897191 : Blo 397767 897191 := bstep (se 1 (by rfl) ⟨672893, by rfl⟩ : syracuseStep 897191 = 1345787) B1345787
theorem B897263 : Blo 397767 897263 := bstep (se 1 (by rfl) ⟨672947, by rfl⟩ : syracuseStep 897263 = 1345895) B1345895
theorem B7287083 : Blo 397767 7287083 := bstep (se 1 (by rfl) ⟨5465312, by rfl⟩ : syracuseStep 7287083 = 10930625) B10930625
theorem B602447 : Blo 397767 602447 := bstep (se 1 (by rfl) ⟨451835, by rfl⟩ : syracuseStep 602447 = 903671) B903671
theorem B2765137 : Blo 397767 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B897515 : Blo 397767 897515 := bstep (se 1 (by rfl) ⟨673136, by rfl⟩ : syracuseStep 897515 = 1346273) B1346273
theorem B4928039 : Blo 397767 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B963199 : Blo 397767 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B6173651 : Blo 397767 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B5911667 : Blo 397767 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B898847 : Blo 397767 898847 := bstep (se 1 (by rfl) ⟨674135, by rfl⟩ : syracuseStep 898847 = 1348271) B1348271
theorem B6797195 : Blo 397767 6797195 := bstep (se 1 (by rfl) ⟨5097896, by rfl⟩ : syracuseStep 6797195 = 10195793) B10195793
theorem B899135 : Blo 397767 899135 := bstep (se 1 (by rfl) ⟨674351, by rfl⟩ : syracuseStep 899135 = 1348703) B1348703
theorem B1521787 : Blo 397767 1521787 := bstep (se 1 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 1521787 = 2282681) B2282681
theorem B2013821 : Blo 397767 2013821 := bstep (se 3 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 2013821 = 755183) B755183
theorem B4340411 : Blo 397767 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B1915751 : Blo 397767 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B900233 : Blo 397767 900233 := bstep (se 2 (by rfl) ⟨337587, by rfl⟩ : syracuseStep 900233 = 675175) B675175
theorem B900791 : Blo 397767 900791 := bstep (se 1 (by rfl) ⟨675593, by rfl⟩ : syracuseStep 900791 = 1351187) B1351187
theorem B901295 : Blo 397767 901295 := bstep (se 1 (by rfl) ⟨675971, by rfl⟩ : syracuseStep 901295 = 1351943) B1351943
theorem B6177059 : Blo 397767 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B13025771 : Blo 397767 13025771 := bstep (se 1 (by rfl) ⟨9769328, by rfl⟩ : syracuseStep 13025771 = 19538657) B19538657
theorem B673535 : Blo 397767 673535 := bstep (se 1 (by rfl) ⟨505151, by rfl⟩ : syracuseStep 673535 = 1010303) B1010303
theorem B903239 : Blo 397767 903239 := bstep (se 1 (by rfl) ⟨677429, by rfl⟩ : syracuseStep 903239 = 1354859) B1354859
theorem B510511 : Blo 397767 510511 := bstep (se 1 (by rfl) ⟨382883, by rfl⟩ : syracuseStep 510511 = 765767) B765767
theorem B1920095 : Blo 397767 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B52317413 : Blo 397767 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B610487 : Blo 397767 610487 := bstep (se 1 (by rfl) ⟨457865, by rfl⟩ : syracuseStep 610487 = 915731) B915731
theorem B5854303 : Blo 397767 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B2021111 : Blo 397767 2021111 := bstep (se 1 (by rfl) ⟨1515833, by rfl⟩ : syracuseStep 2021111 = 3031667) B3031667
theorem B677801 : Blo 397767 677801 := bstep (se 2 (by rfl) ⟨254175, by rfl⟩ : syracuseStep 677801 = 508351) B508351
theorem B1006951 : Blo 397767 1006951 := bstep (se 1 (by rfl) ⟨755213, by rfl⟩ : syracuseStep 1006951 = 1510427) B1510427
theorem B1007387 : Blo 397767 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B1007599 : Blo 397767 1007599 := bstep (se 1 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 1007599 = 1511399) B1511399
theorem B450895 : Blo 397767 450895 := bstep (se 1 (by rfl) ⟨338171, by rfl⟩ : syracuseStep 450895 = 676343) B676343
theorem B4121027 : Blo 397767 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B1139291 : Blo 397767 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B3040415 : Blo 397767 3040415 := bstep (se 1 (by rfl) ⟨2280311, by rfl⟩ : syracuseStep 3040415 = 4560623) B4560623
theorem B3565601 : Blo 397767 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B13986857 : Blo 397767 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B1077491 : Blo 397767 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B717311 : Blo 397767 717311 := bstep (se 1 (by rfl) ⟨537983, by rfl⟩ : syracuseStep 717311 = 1075967) B1075967
theorem B2028239 : Blo 397767 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B3044303 : Blo 397767 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B2029211 : Blo 397767 2029211 := bstep (se 1 (by rfl) ⟨1521908, by rfl⟩ : syracuseStep 2029211 = 3043817) B3043817
theorem B3077959 : Blo 397767 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B11304137 : Blo 397767 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B2031155 : Blo 397767 2031155 := bstep (se 1 (by rfl) ⟨1523366, by rfl⟩ : syracuseStep 2031155 = 3046733) B3046733
theorem B1015679 : Blo 397767 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B852059 : Blo 397767 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B8683847 : Blo 397767 8683847 := bstep (se 1 (by rfl) ⟨6512885, by rfl⟩ : syracuseStep 8683847 = 13025771) B13025771
theorem B2032127 : Blo 397767 2032127 := bstep (se 1 (by rfl) ⟨1524095, by rfl⟩ : syracuseStep 2032127 = 3048191) B3048191
theorem B2884175 : Blo 397767 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B5211049 : Blo 397767 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B1280063 : Blo 397767 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B1347407 : Blo 397767 1347407 := bstep (se 1 (by rfl) ⟨1010555, by rfl⟩ : syracuseStep 1347407 = 2021111) B2021111
theorem B1511567 : Blo 397767 1511567 := bstep (se 1 (by rfl) ⟨1133675, by rfl⟩ : syracuseStep 1511567 = 2267351) B2267351
theorem B398427 : Blo 397767 398427 := bstep (se 1 (by rfl) ⟨298820, by rfl⟩ : syracuseStep 398427 = 597641) B597641
theorem B759527 : Blo 397767 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B399295 : Blo 397767 399295 := bstep (se 1 (by rfl) ⟨299471, by rfl⟩ : syracuseStep 399295 = 598943) B598943
theorem B399359 : Blo 397767 399359 := bstep (se 1 (by rfl) ⟨299519, by rfl⟩ : syracuseStep 399359 = 599039) B599039
theorem B1284265 : Blo 397767 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B399599 : Blo 397767 399599 := bstep (se 1 (by rfl) ⟨299699, by rfl⟩ : syracuseStep 399599 = 599399) B599399
theorem B400063 : Blo 397767 400063 := bstep (se 1 (by rfl) ⟨300047, by rfl⟩ : syracuseStep 400063 = 600095) B600095
theorem B400111 : Blo 397767 400111 := bstep (se 1 (by rfl) ⟨300083, by rfl⟩ : syracuseStep 400111 = 600167) B600167
theorem B7805737 : Blo 397767 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B596975 : Blo 397767 596975 := bstep (se 1 (by rfl) ⟨447731, by rfl⟩ : syracuseStep 596975 = 895463) B895463
theorem B400495 : Blo 397767 400495 := bstep (se 1 (by rfl) ⟨300371, by rfl⟩ : syracuseStep 400495 = 600743) B600743
theorem B400551 : Blo 397767 400551 := bstep (se 1 (by rfl) ⟨300413, by rfl⟩ : syracuseStep 400551 = 600827) B600827
theorem B1711313 : Blo 397767 1711313 := bstep (se 2 (by rfl) ⟨641742, by rfl⟩ : syracuseStep 1711313 = 1283485) B1283485
theorem B597575 : Blo 397767 597575 := bstep (se 1 (by rfl) ⟨448181, by rfl⟩ : syracuseStep 597575 = 896363) B896363
theorem B1842871 : Blo 397767 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B4103945 : Blo 397767 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B598079 : Blo 397767 598079 := bstep (se 1 (by rfl) ⟨448559, by rfl⟩ : syracuseStep 598079 = 897119) B897119
theorem B598127 : Blo 397767 598127 := bstep (se 1 (by rfl) ⟨448595, by rfl⟩ : syracuseStep 598127 = 897191) B897191
theorem B598175 : Blo 397767 598175 := bstep (se 1 (by rfl) ⟨448631, by rfl⟩ : syracuseStep 598175 = 897263) B897263
theorem B4858055 : Blo 397767 4858055 := bstep (se 1 (by rfl) ⟨3643541, by rfl⟩ : syracuseStep 4858055 = 7287083) B7287083
theorem B401631 : Blo 397767 401631 := bstep (se 1 (by rfl) ⟨301223, by rfl⟩ : syracuseStep 401631 = 602447) B602447
theorem B598343 : Blo 397767 598343 := bstep (se 1 (by rfl) ⟨448757, by rfl⟩ : syracuseStep 598343 = 897515) B897515
theorem B3285359 : Blo 397767 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B1352159 : Blo 397767 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B3941111 : Blo 397767 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B7283789 : Blo 397767 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B1352807 : Blo 397767 1352807 := bstep (se 1 (by rfl) ⟨1014605, by rfl⟩ : syracuseStep 1352807 = 2029211) B2029211
theorem B599231 : Blo 397767 599231 := bstep (se 1 (by rfl) ⟨449423, by rfl⟩ : syracuseStep 599231 = 898847) B898847
theorem B4531463 : Blo 397767 4531463 := bstep (se 1 (by rfl) ⟨3398597, by rfl⟩ : syracuseStep 4531463 = 6797195) B6797195
theorem B599423 : Blo 397767 599423 := bstep (se 1 (by rfl) ⟨449567, by rfl⟩ : syracuseStep 599423 = 899135) B899135
theorem B2893607 : Blo 397767 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B600155 : Blo 397767 600155 := bstep (se 1 (by rfl) ⟨450116, by rfl⟩ : syracuseStep 600155 = 900233) B900233
theorem B1354103 : Blo 397767 1354103 := bstep (se 1 (by rfl) ⟨1015577, by rfl⟩ : syracuseStep 1354103 = 2031155) B2031155
theorem B600527 : Blo 397767 600527 := bstep (se 1 (by rfl) ⟨450395, by rfl⟩ : syracuseStep 600527 = 900791) B900791
theorem B895679 : Blo 397767 895679 := bstep (se 1 (by rfl) ⟨671759, by rfl⟩ : syracuseStep 895679 = 1343519) B1343519
theorem B600863 : Blo 397767 600863 := bstep (se 1 (by rfl) ⟨450647, by rfl⟩ : syracuseStep 600863 = 901295) B901295
theorem B1354697 : Blo 397767 1354697 := bstep (se 2 (by rfl) ⟨508011, by rfl⟩ : syracuseStep 1354697 = 1016023) B1016023
theorem B601193 : Blo 397767 601193 := bstep (se 2 (by rfl) ⟨225447, by rfl⟩ : syracuseStep 601193 = 450895) B450895
theorem B3845839 : Blo 397767 3845839 := bstep (se 1 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 3845839 = 5768759) B5768759
theorem B602159 : Blo 397767 602159 := bstep (se 1 (by rfl) ⟨451619, by rfl⟩ : syracuseStep 602159 = 903239) B903239
theorem B3256375 : Blo 397767 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B34878275 : Blo 397767 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B897875 : Blo 397767 897875 := bstep (se 1 (by rfl) ⟨673406, by rfl⟩ : syracuseStep 897875 = 1346813) B1346813
theorem B406991 : Blo 397767 406991 := bstep (se 1 (by rfl) ⟨305243, by rfl⟩ : syracuseStep 406991 = 610487) B610487
theorem B2275391 : Blo 397767 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B3652883 : Blo 397767 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B540265 : Blo 397767 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B2277031 : Blo 397767 2277031 := bstep (se 1 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 2277031 = 3415547) B3415547
theorem B671591 : Blo 397767 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B901151 : Blo 397767 901151 := bstep (se 1 (by rfl) ⟨675863, by rfl⟩ : syracuseStep 901151 = 1351727) B1351727
theorem B3686849 : Blo 397767 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B902123 : Blo 397767 902123 := bstep (se 1 (by rfl) ⟨676592, by rfl⟩ : syracuseStep 902123 = 1353185) B1353185
theorem B902483 : Blo 397767 902483 := bstep (se 1 (by rfl) ⟨676862, by rfl⟩ : syracuseStep 902483 = 1353725) B1353725
theorem B2377067 : Blo 397767 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B34981307 : Blo 397767 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B2016737 : Blo 397767 2016737 := bstep (se 2 (by rfl) ⟨756276, by rfl⟩ : syracuseStep 2016737 = 1512553) B1512553
theorem B9324571 : Blo 397767 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B903275 : Blo 397767 903275 := bstep (se 1 (by rfl) ⟨677456, by rfl⟩ : syracuseStep 903275 = 1354913) B1354913
theorem B478207 : Blo 397767 478207 := bstep (se 1 (by rfl) ⟨358655, by rfl⟩ : syracuseStep 478207 = 717311) B717311
theorem B4115767 : Blo 397767 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B677119 : Blo 397767 677119 := bstep (se 1 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 677119 = 1015679) B1015679
theorem B4118039 : Blo 397767 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B449023 : Blo 397767 449023 := bstep (se 1 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 449023 = 673535) B673535
theorem B1137377 : Blo 397767 1137377 := bstep (se 2 (by rfl) ⟨426516, by rfl⟩ : syracuseStep 1137377 = 853033) B853033
theorem B680681 : Blo 397767 680681 := bstep (se 2 (by rfl) ⟨255255, by rfl⟩ : syracuseStep 680681 = 510511) B510511
theorem B2057375 : Blo 397767 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B451867 : Blo 397767 451867 := bstep (se 1 (by rfl) ⟨338900, by rfl⟩ : syracuseStep 451867 = 677801) B677801
theorem B1140601 : Blo 397767 1140601 := bstep (se 2 (by rfl) ⟨427725, by rfl⟩ : syracuseStep 1140601 = 855451) B855451
theorem B3238217 : Blo 397767 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B2025809 : Blo 397767 2025809 := bstep (se 2 (by rfl) ⟨759678, by rfl⟩ : syracuseStep 2025809 = 1519357) B1519357
theorem B1010515 : Blo 397767 1010515 := bstep (se 1 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 1010515 = 1515773) B1515773
theorem B2747351 : Blo 397767 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B1010657 : Blo 397767 1010657 := bstep (se 2 (by rfl) ⟨378996, by rfl⟩ : syracuseStep 1010657 = 757993) B757993
theorem B2026943 : Blo 397767 2026943 := bstep (se 1 (by rfl) ⟨1520207, by rfl⟩ : syracuseStep 2026943 = 3040415) B3040415
theorem B1011305 : Blo 397767 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B718327 : Blo 397767 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B2029049 : Blo 397767 2029049 := bstep (se 2 (by rfl) ⟨760893, by rfl⟩ : syracuseStep 2029049 = 1521787) B1521787
theorem B2029535 : Blo 397767 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B1342547 : Blo 397767 1342547 := bstep (se 1 (by rfl) ⟨1006910, by rfl⟩ : syracuseStep 1342547 = 2013821) B2013821
theorem B1342601 : Blo 397767 1342601 := bstep (se 2 (by rfl) ⟨503475, by rfl⟩ : syracuseStep 1342601 = 1006951) B1006951
theorem B1277167 : Blo 397767 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B7536091 : Blo 397767 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B1343465 : Blo 397767 1343465 := bstep (se 2 (by rfl) ⟨503799, by rfl⟩ : syracuseStep 1343465 = 1007599) B1007599
theorem B2457899 : Blo 397767 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B1344491 : Blo 397767 1344491 := bstep (se 1 (by rfl) ⟨1008368, by rfl⟩ : syracuseStep 1344491 = 2016737) B2016737
theorem B6948065 : Blo 397767 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B853375 : Blo 397767 853375 := bstep (se 1 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 853375 = 1280063) B1280063
theorem B1347353 : Blo 397767 1347353 := bstep (se 2 (by rfl) ⟨505257, by rfl⟩ : syracuseStep 1347353 = 1010515) B1010515
theorem B1085309 : Blo 397767 1085309 := bstep (se 3 (by rfl) ⟨203495, by rfl⟩ : syracuseStep 1085309 = 406991) B406991
theorem B758251 : Blo 397767 758251 := bstep (se 1 (by rfl) ⟨568688, by rfl⟩ : syracuseStep 758251 = 1137377) B1137377
theorem B397983 : Blo 397767 397983 := bstep (se 1 (by rfl) ⟨298487, by rfl⟩ : syracuseStep 397983 = 596975) B596975
theorem B398383 : Blo 397767 398383 := bstep (se 1 (by rfl) ⟨298787, by rfl⟩ : syracuseStep 398383 = 597575) B597575
theorem B398719 : Blo 397767 398719 := bstep (se 1 (by rfl) ⟨299039, by rfl⟩ : syracuseStep 398719 = 598079) B598079
theorem B398751 : Blo 397767 398751 := bstep (se 1 (by rfl) ⟨299063, by rfl⟩ : syracuseStep 398751 = 598127) B598127
theorem B398783 : Blo 397767 398783 := bstep (se 1 (by rfl) ⟨299087, by rfl⟩ : syracuseStep 398783 = 598175) B598175
theorem B398895 : Blo 397767 398895 := bstep (se 1 (by rfl) ⟨299171, by rfl⟩ : syracuseStep 398895 = 598343) B598343
theorem B2627407 : Blo 397767 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B4855859 : Blo 397767 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B399487 : Blo 397767 399487 := bstep (se 1 (by rfl) ⟨299615, by rfl⟩ : syracuseStep 399487 = 599231) B599231
theorem B3020975 : Blo 397767 3020975 := bstep (se 1 (by rfl) ⟨2265731, by rfl⟩ : syracuseStep 3020975 = 4531463) B4531463
theorem B399615 : Blo 397767 399615 := bstep (se 1 (by rfl) ⟨299711, by rfl⟩ : syracuseStep 399615 = 599423) B599423
theorem B400103 : Blo 397767 400103 := bstep (se 1 (by rfl) ⟨300077, by rfl⟩ : syracuseStep 400103 = 600155) B600155
theorem B1350539 : Blo 397767 1350539 := bstep (se 1 (by rfl) ⟨1012904, by rfl⟩ : syracuseStep 1350539 = 2025809) B2025809
theorem B400351 : Blo 397767 400351 := bstep (se 1 (by rfl) ⟨300263, by rfl⟩ : syracuseStep 400351 = 600527) B600527
theorem B597119 : Blo 397767 597119 := bstep (se 1 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 597119 = 895679) B895679
theorem B400575 : Blo 397767 400575 := bstep (se 1 (by rfl) ⟨300431, by rfl⟩ : syracuseStep 400575 = 600863) B600863
theorem B400795 : Blo 397767 400795 := bstep (se 1 (by rfl) ⟨300596, by rfl⟩ : syracuseStep 400795 = 601193) B601193
theorem B1351295 : Blo 397767 1351295 := bstep (se 1 (by rfl) ⟨1013471, by rfl⟩ : syracuseStep 1351295 = 2026943) B2026943
theorem B401439 : Blo 397767 401439 := bstep (se 1 (by rfl) ⟨301079, by rfl⟩ : syracuseStep 401439 = 602159) B602159
theorem B1712353 : Blo 397767 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B598583 : Blo 397767 598583 := bstep (se 1 (by rfl) ⟨448937, by rfl⟩ : syracuseStep 598583 = 897875) B897875
theorem B598697 : Blo 397767 598697 := bstep (se 2 (by rfl) ⟨224511, by rfl⟩ : syracuseStep 598697 = 449023) B449023
theorem B1352699 : Blo 397767 1352699 := bstep (se 1 (by rfl) ⟨1014524, by rfl⟩ : syracuseStep 1352699 = 2029049) B2029049
theorem B1353023 : Blo 397767 1353023 := bstep (se 1 (by rfl) ⟨1014767, by rfl⟩ : syracuseStep 1353023 = 2029535) B2029535
theorem B1516927 : Blo 397767 1516927 := bstep (se 1 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 1516927 = 2275391) B2275391
theorem B895031 : Blo 397767 895031 := bstep (se 1 (by rfl) ⟨671273, by rfl⟩ : syracuseStep 895031 = 1342547) B1342547
theorem B895067 : Blo 397767 895067 := bstep (se 1 (by rfl) ⟨671300, by rfl⟩ : syracuseStep 895067 = 1342601) B1342601
theorem B2435255 : Blo 397767 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B895643 : Blo 397767 895643 := bstep (se 1 (by rfl) ⟨671732, by rfl⟩ : syracuseStep 895643 = 1343465) B1343465
theorem B600767 : Blo 397767 600767 := bstep (se 1 (by rfl) ⟨450575, by rfl⟩ : syracuseStep 600767 = 901151) B901151
theorem B2272157 : Blo 397767 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B1354751 : Blo 397767 1354751 := bstep (se 1 (by rfl) ⟨1016063, by rfl⟩ : syracuseStep 1354751 = 2032127) B2032127
theorem B601415 : Blo 397767 601415 := bstep (se 1 (by rfl) ⟨451061, by rfl⟩ : syracuseStep 601415 = 902123) B902123
theorem B601655 : Blo 397767 601655 := bstep (se 1 (by rfl) ⟨451241, by rfl⟩ : syracuseStep 601655 = 902483) B902483
theorem B602183 : Blo 397767 602183 := bstep (se 1 (by rfl) ⟨451637, by rfl⟩ : syracuseStep 602183 = 903275) B903275
theorem B602489 : Blo 397767 602489 := bstep (se 2 (by rfl) ⟨225933, by rfl⟩ : syracuseStep 602489 = 451867) B451867
theorem B1815149 : Blo 397767 1815149 := bstep (se 3 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 1815149 = 680681) B680681
theorem B1520801 : Blo 397767 1520801 := bstep (se 2 (by rfl) ⟨570300, by rfl⟩ : syracuseStep 1520801 = 1140601) B1140601
theorem B898271 : Blo 397767 898271 := bstep (se 1 (by rfl) ⟨673703, by rfl⟩ : syracuseStep 898271 = 1347407) B1347407
theorem B12432761 : Blo 397767 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B6338845 : Blo 397767 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B506351 : Blo 397767 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B5487689 : Blo 397767 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B5127785 : Blo 397767 5127785 := bstep (se 2 (by rfl) ⟨1922919, by rfl⟩ : syracuseStep 5127785 = 3845839) B3845839
theorem B2735963 : Blo 397767 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B4341833 : Blo 397767 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B901439 : Blo 397767 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B901871 : Blo 397767 901871 := bstep (se 1 (by rfl) ⟨676403, by rfl⟩ : syracuseStep 901871 = 1352807) B1352807
theorem B902735 : Blo 397767 902735 := bstep (se 1 (by rfl) ⟨677051, by rfl⟩ : syracuseStep 902735 = 1354103) B1354103
theorem B902825 : Blo 397767 902825 := bstep (se 2 (by rfl) ⟨338559, by rfl⟩ : syracuseStep 902825 = 677119) B677119
theorem B903131 : Blo 397767 903131 := bstep (se 1 (by rfl) ⟨677348, by rfl⟩ : syracuseStep 903131 = 1354697) B1354697
theorem B673771 : Blo 397767 673771 := bstep (se 1 (by rfl) ⟨505328, by rfl⟩ : syracuseStep 673771 = 1010657) B1010657
theorem B674203 : Blo 397767 674203 := bstep (se 1 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 674203 = 1011305) B1011305
theorem B23252183 : Blo 397767 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B10407649 : Blo 397767 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B10048121 : Blo 397767 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B3036041 : Blo 397767 3036041 := bstep (se 2 (by rfl) ⟨1138515, by rfl⟩ : syracuseStep 3036041 = 2277031) B2277031
theorem B447727 : Blo 397767 447727 := bstep (se 1 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 447727 = 671591) B671591
theorem B5789231 : Blo 397767 5789231 := bstep (se 1 (by rfl) ⟨4341923, by rfl⟩ : syracuseStep 5789231 = 8683847) B8683847
theorem B1922783 : Blo 397767 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B23320871 : Blo 397767 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B1007711 : Blo 397767 1007711 := bstep (se 1 (by rfl) ⟨755783, by rfl⟩ : syracuseStep 1007711 = 1511567) B1511567
theorem B2745359 : Blo 397767 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B1140875 : Blo 397767 1140875 := bstep (se 1 (by rfl) ⟨855656, by rfl⟩ : syracuseStep 1140875 = 1711313) B1711313
theorem B2550437 : Blo 397767 2550437 := bstep (se 4 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 2550437 = 478207) B478207
theorem B3238703 : Blo 397767 3238703 := bstep (se 1 (by rfl) ⟨2429027, by rfl⟩ : syracuseStep 3238703 = 4858055) B4858055
theorem B2190239 : Blo 397767 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B1371583 : Blo 397767 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B1929071 : Blo 397767 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B2158811 : Blo 397767 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B1831567 : Blo 397767 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B3831077 : Blo 397767 3831077 := bstep (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) B718327
theorem B1702889 : Blo 397767 1702889 := bstep (se 2 (by rfl) ⟨638583, by rfl⟩ : syracuseStep 1702889 = 1277167) B1277167
theorem B720353 : Blo 397767 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B2457161 : Blo 397767 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B1638599 : Blo 397767 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B15501455 : Blo 397767 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B723539 : Blo 397767 723539 := bstep (se 1 (by rfl) ⟨542654, by rfl⟩ : syracuseStep 723539 = 1085309) B1085309
theorem B398079 : Blo 397767 398079 := bstep (se 1 (by rfl) ⟨298559, by rfl⟩ : syracuseStep 398079 = 597119) B597119
theorem B399055 : Blo 397767 399055 := bstep (se 1 (by rfl) ⟨299291, by rfl⟩ : syracuseStep 399055 = 598583) B598583
theorem B399131 : Blo 397767 399131 := bstep (se 1 (by rfl) ⟨299348, by rfl⟩ : syracuseStep 399131 = 598697) B598697
theorem B1350269 : Blo 397767 1350269 := bstep (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) B506351
theorem B596687 : Blo 397767 596687 := bstep (se 1 (by rfl) ⟨447515, by rfl⟩ : syracuseStep 596687 = 895031) B895031
theorem B596711 : Blo 397767 596711 := bstep (se 1 (by rfl) ⟨447533, by rfl⟩ : syracuseStep 596711 = 895067) B895067
theorem B760583 : Blo 397767 760583 := bstep (se 1 (by rfl) ⟨570437, by rfl⟩ : syracuseStep 760583 = 1140875) B1140875
theorem B596969 : Blo 397767 596969 := bstep (se 2 (by rfl) ⟨223863, by rfl⟩ : syracuseStep 596969 = 447727) B447727
theorem B597095 : Blo 397767 597095 := bstep (se 1 (by rfl) ⟨447821, by rfl⟩ : syracuseStep 597095 = 895643) B895643
theorem B400511 : Blo 397767 400511 := bstep (se 1 (by rfl) ⟨300383, by rfl⟩ : syracuseStep 400511 = 600767) B600767
theorem B1514771 : Blo 397767 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B400943 : Blo 397767 400943 := bstep (se 1 (by rfl) ⟨300707, by rfl⟩ : syracuseStep 400943 = 601415) B601415
theorem B401103 : Blo 397767 401103 := bstep (se 1 (by rfl) ⟨300827, by rfl⟩ : syracuseStep 401103 = 601655) B601655
theorem B1286047 : Blo 397767 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B401455 : Blo 397767 401455 := bstep (se 1 (by rfl) ⟨301091, by rfl⟩ : syracuseStep 401455 = 602183) B602183
theorem B401659 : Blo 397767 401659 := bstep (se 1 (by rfl) ⟨301244, by rfl⟩ : syracuseStep 401659 = 602489) B602489
theorem B598847 : Blo 397767 598847 := bstep (se 1 (by rfl) ⟨449135, by rfl⟩ : syracuseStep 598847 = 898271) B898271
theorem B3418523 : Blo 397767 3418523 := bstep (se 1 (by rfl) ⟨2563892, by rfl⟩ : syracuseStep 3418523 = 5127785) B5127785
theorem B2894555 : Blo 397767 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B600959 : Blo 397767 600959 := bstep (se 1 (by rfl) ⟨450719, by rfl⟩ : syracuseStep 600959 = 901439) B901439
theorem B601247 : Blo 397767 601247 := bstep (se 1 (by rfl) ⟨450935, by rfl⟩ : syracuseStep 601247 = 901871) B901871
theorem B896327 : Blo 397767 896327 := bstep (se 1 (by rfl) ⟨672245, by rfl⟩ : syracuseStep 896327 = 1344491) B1344491
theorem B601823 : Blo 397767 601823 := bstep (se 1 (by rfl) ⟨451367, by rfl⟩ : syracuseStep 601823 = 902735) B902735
theorem B601883 : Blo 397767 601883 := bstep (se 1 (by rfl) ⟨451412, by rfl⟩ : syracuseStep 601883 = 902825) B902825
theorem B602087 : Blo 397767 602087 := bstep (se 1 (by rfl) ⟨451565, by rfl⟩ : syracuseStep 602087 = 903131) B903131
theorem B898235 : Blo 397767 898235 := bstep (se 1 (by rfl) ⟨673676, by rfl⟩ : syracuseStep 898235 = 1347353) B1347353
theorem B898361 : Blo 397767 898361 := bstep (se 2 (by rfl) ⟨336885, by rfl⟩ : syracuseStep 898361 = 673771) B673771
theorem B6698747 : Blo 397767 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B898937 : Blo 397767 898937 := bstep (se 2 (by rfl) ⟨337101, by rfl⟩ : syracuseStep 898937 = 674203) B674203
theorem B18528173 : Blo 397767 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B2013983 : Blo 397767 2013983 := bstep (se 1 (by rfl) ⟨1510487, by rfl⟩ : syracuseStep 2013983 = 3020975) B3020975
theorem B15547247 : Blo 397767 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B5127421 : Blo 397767 5127421 := bstep (se 3 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 5127421 = 1922783) B1922783
theorem B900359 : Blo 397767 900359 := bstep (se 1 (by rfl) ⟨675269, by rfl⟩ : syracuseStep 900359 = 1350539) B1350539
theorem B13876865 : Blo 397767 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B900863 : Blo 397767 900863 := bstep (se 1 (by rfl) ⟨675647, by rfl⟩ : syracuseStep 900863 = 1351295) B1351295
theorem B671807 : Blo 397767 671807 := bstep (se 1 (by rfl) ⟨503855, by rfl⟩ : syracuseStep 671807 = 1007711) B1007711
theorem B901799 : Blo 397767 901799 := bstep (se 1 (by rfl) ⟨676349, by rfl⟩ : syracuseStep 901799 = 1352699) B1352699
theorem B2442089 : Blo 397767 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B902015 : Blo 397767 902015 := bstep (se 1 (by rfl) ⟨676511, by rfl⟩ : syracuseStep 902015 = 1353023) B1353023
theorem B1623503 : Blo 397767 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B1460159 : Blo 397767 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B903167 : Blo 397767 903167 := bstep (se 1 (by rfl) ⟨677375, by rfl⟩ : syracuseStep 903167 = 1354751) B1354751
theorem B1135259 : Blo 397767 1135259 := bstep (se 1 (by rfl) ⟨851444, by rfl⟩ : syracuseStep 1135259 = 1702889) B1702889
theorem B3658459 : Blo 397767 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B480235 : Blo 397767 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B1823975 : Blo 397767 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B2283137 : Blo 397767 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B2022569 : Blo 397767 2022569 := bstep (se 2 (by rfl) ⟨758463, by rfl⟩ : syracuseStep 2022569 = 1516927) B1516927
theorem B1137833 : Blo 397767 1137833 := bstep (se 2 (by rfl) ⟨426687, by rfl⟩ : syracuseStep 1137833 = 853375) B853375
theorem B2024027 : Blo 397767 2024027 := bstep (se 1 (by rfl) ⟨1518020, by rfl⟩ : syracuseStep 2024027 = 3036041) B3036041
theorem B3859487 : Blo 397767 3859487 := bstep (se 1 (by rfl) ⟨2894615, by rfl⟩ : syracuseStep 3859487 = 5789231) B5789231
theorem B3237239 : Blo 397767 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B1828777 : Blo 397767 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B1011001 : Blo 397767 1011001 := bstep (se 2 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 1011001 = 758251) B758251
theorem B1830239 : Blo 397767 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1700291 : Blo 397767 1700291 := bstep (se 1 (by rfl) ⟨1275218, by rfl⟩ : syracuseStep 1700291 = 2550437) B2550437
theorem B2159135 : Blo 397767 2159135 := bstep (se 1 (by rfl) ⟨1619351, by rfl⟩ : syracuseStep 2159135 = 3238703) B3238703
theorem B3503209 : Blo 397767 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B1439207 : Blo 397767 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B8451793 : Blo 397767 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B1210099 : Blo 397767 1210099 := bstep (se 1 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 1210099 = 1815149) B1815149
theorem B1013867 : Blo 397767 1013867 := bstep (se 1 (by rfl) ⟨760400, by rfl⟩ : syracuseStep 1013867 = 1520801) B1520801
theorem B2554051 : Blo 397767 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B8288507 : Blo 397767 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B1638107 : Blo 397767 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B1082335 : Blo 397767 1082335 := bstep (se 1 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 1082335 = 1623503) B1623503
theorem B756839 : Blo 397767 756839 := bstep (se 1 (by rfl) ⟨567629, by rfl⟩ : syracuseStep 756839 = 1135259) B1135259
theorem B1215983 : Blo 397767 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B1348001 : Blo 397767 1348001 := bstep (se 2 (by rfl) ⟨505500, by rfl⟩ : syracuseStep 1348001 = 1011001) B1011001
theorem B397791 : Blo 397767 397791 := bstep (se 1 (by rfl) ⟨298343, by rfl⟩ : syracuseStep 397791 = 596687) B596687
theorem B397807 : Blo 397767 397807 := bstep (se 1 (by rfl) ⟨298355, by rfl⟩ : syracuseStep 397807 = 596711) B596711
theorem B397979 : Blo 397767 397979 := bstep (se 1 (by rfl) ⟨298484, by rfl⟩ : syracuseStep 397979 = 596969) B596969
theorem B17863325 : Blo 397767 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B398063 : Blo 397767 398063 := bstep (se 1 (by rfl) ⟨298547, by rfl⟩ : syracuseStep 398063 = 597095) B597095
theorem B1348379 : Blo 397767 1348379 := bstep (se 1 (by rfl) ⟨1011284, by rfl⟩ : syracuseStep 1348379 = 2022569) B2022569
theorem B758555 : Blo 397767 758555 := bstep (se 1 (by rfl) ⟨568916, by rfl⟩ : syracuseStep 758555 = 1137833) B1137833
theorem B1349351 : Blo 397767 1349351 := bstep (se 1 (by rfl) ⟨1012013, by rfl⟩ : syracuseStep 1349351 = 2024027) B2024027
theorem B399231 : Blo 397767 399231 := bstep (se 1 (by rfl) ⟨299423, by rfl⟩ : syracuseStep 399231 = 598847) B598847
theorem B400639 : Blo 397767 400639 := bstep (se 1 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 400639 = 600959) B600959
theorem B400831 : Blo 397767 400831 := bstep (se 1 (by rfl) ⟨300623, by rfl⟩ : syracuseStep 400831 = 601247) B601247
theorem B597551 : Blo 397767 597551 := bstep (se 1 (by rfl) ⟨448163, by rfl⟩ : syracuseStep 597551 = 896327) B896327
theorem B1220159 : Blo 397767 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B1613465 : Blo 397767 1613465 := bstep (se 2 (by rfl) ⟨605049, by rfl⟩ : syracuseStep 1613465 = 1210099) B1210099
theorem B401215 : Blo 397767 401215 := bstep (se 1 (by rfl) ⟨300911, by rfl⟩ : syracuseStep 401215 = 601823) B601823
theorem B401255 : Blo 397767 401255 := bstep (se 1 (by rfl) ⟨300941, by rfl⟩ : syracuseStep 401255 = 601883) B601883
theorem B401391 : Blo 397767 401391 := bstep (se 1 (by rfl) ⟨301043, by rfl⟩ : syracuseStep 401391 = 602087) B602087
theorem B598823 : Blo 397767 598823 := bstep (se 1 (by rfl) ⟨449117, by rfl⟩ : syracuseStep 598823 = 898235) B898235
theorem B598907 : Blo 397767 598907 := bstep (se 1 (by rfl) ⟨449180, by rfl⟩ : syracuseStep 598907 = 898361) B898361
theorem B959471 : Blo 397767 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B599291 : Blo 397767 599291 := bstep (se 1 (by rfl) ⟨449468, by rfl⟩ : syracuseStep 599291 = 898937) B898937
theorem B10364831 : Blo 397767 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B600239 : Blo 397767 600239 := bstep (se 1 (by rfl) ⟨450179, by rfl⟩ : syracuseStep 600239 = 900359) B900359
theorem B9251243 : Blo 397767 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B1092071 : Blo 397767 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B600575 : Blo 397767 600575 := bstep (se 1 (by rfl) ⟨450431, by rfl⟩ : syracuseStep 600575 = 900863) B900863
theorem B1714729 : Blo 397767 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B601199 : Blo 397767 601199 := bstep (se 1 (by rfl) ⟨450899, by rfl⟩ : syracuseStep 601199 = 901799) B901799
theorem B601343 : Blo 397767 601343 := bstep (se 1 (by rfl) ⟨451007, by rfl⟩ : syracuseStep 601343 = 902015) B902015
theorem B602111 : Blo 397767 602111 := bstep (se 1 (by rfl) ⟨451583, by rfl⟩ : syracuseStep 602111 = 903167) B903167
theorem B10334303 : Blo 397767 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B17478389 : Blo 397767 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B2438369 : Blo 397767 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B1522091 : Blo 397767 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B900179 : Blo 397767 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B507055 : Blo 397767 507055 := bstep (se 1 (by rfl) ⟨380291, by rfl⟩ : syracuseStep 507055 = 760583) B760583
theorem B2572991 : Blo 397767 2572991 := bstep (se 1 (by rfl) ⟨1929743, by rfl⟩ : syracuseStep 2572991 = 3859487) B3859487
theorem B640313 : Blo 397767 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B4670945 : Blo 397767 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B2279015 : Blo 397767 2279015 := bstep (se 1 (by rfl) ⟨1709261, by rfl⟩ : syracuseStep 2279015 = 3418523) B3418523
theorem B7718813 : Blo 397767 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B1133527 : Blo 397767 1133527 := bstep (se 1 (by rfl) ⟨850145, by rfl⟩ : syracuseStep 1133527 = 1700291) B1700291
theorem B675911 : Blo 397767 675911 := bstep (se 1 (by rfl) ⟨506933, by rfl⟩ : syracuseStep 675911 = 1013867) B1013867
theorem B5525671 : Blo 397767 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B6836561 : Blo 397767 6836561 := bstep (se 2 (by rfl) ⟨2563710, by rfl⟩ : syracuseStep 6836561 = 5127421) B5127421
theorem B447871 : Blo 397767 447871 := bstep (se 1 (by rfl) ⟨335903, by rfl⟩ : syracuseStep 447871 = 671807) B671807
theorem B1628059 : Blo 397767 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B973439 : Blo 397767 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B482359 : Blo 397767 482359 := bstep (se 1 (by rfl) ⟨361769, by rfl⟩ : syracuseStep 482359 = 723539) B723539
theorem B1009847 : Blo 397767 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B2158159 : Blo 397767 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B4877945 : Blo 397767 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B11269057 : Blo 397767 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B3405401 : Blo 397767 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B1439423 : Blo 397767 1439423 := bstep (se 1 (by rfl) ⟨1079567, by rfl⟩ : syracuseStep 1439423 = 2159135) B2159135
theorem B12352115 : Blo 397767 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B1342655 : Blo 397767 1342655 := bstep (se 1 (by rfl) ⟨1006991, by rfl⟩ : syracuseStep 1342655 = 2013983) B2013983
theorem B426875 : Blo 397767 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B3113963 : Blo 397767 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B5145875 : Blo 397767 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B1443113 : Blo 397767 1443113 := bstep (se 2 (by rfl) ⟨541167, by rfl⟩ : syracuseStep 1443113 = 1082335) B1082335
theorem B4557707 : Blo 397767 4557707 := bstep (se 1 (by rfl) ⟨3418280, by rfl⟩ : syracuseStep 4557707 = 6836561) B6836561
theorem B1511369 : Blo 397767 1511369 := bstep (se 2 (by rfl) ⟨566763, by rfl⟩ : syracuseStep 1511369 = 1133527) B1133527
theorem B398367 : Blo 397767 398367 := bstep (se 1 (by rfl) ⟨298775, by rfl⟩ : syracuseStep 398367 = 597551) B597551
theorem B399215 : Blo 397767 399215 := bstep (se 1 (by rfl) ⟨299411, by rfl⟩ : syracuseStep 399215 = 598823) B598823
theorem B399271 : Blo 397767 399271 := bstep (se 1 (by rfl) ⟨299453, by rfl⟩ : syracuseStep 399271 = 598907) B598907
theorem B399527 : Blo 397767 399527 := bstep (se 1 (by rfl) ⟨299645, by rfl⟩ : syracuseStep 399527 = 599291) B599291
theorem B400159 : Blo 397767 400159 := bstep (se 1 (by rfl) ⟨300119, by rfl⟩ : syracuseStep 400159 = 600239) B600239
theorem B6167495 : Blo 397767 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B728047 : Blo 397767 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B400383 : Blo 397767 400383 := bstep (se 1 (by rfl) ⟨300287, by rfl⟩ : syracuseStep 400383 = 600575) B600575
theorem B597161 : Blo 397767 597161 := bstep (se 2 (by rfl) ⟨223935, by rfl⟩ : syracuseStep 597161 = 447871) B447871
theorem B400799 : Blo 397767 400799 := bstep (se 1 (by rfl) ⟨300599, by rfl⟩ : syracuseStep 400799 = 601199) B601199
theorem B400895 : Blo 397767 400895 := bstep (se 1 (by rfl) ⟨300671, by rfl⟩ : syracuseStep 400895 = 601343) B601343
theorem B3251963 : Blo 397767 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B2170745 : Blo 397767 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B401407 : Blo 397767 401407 := bstep (se 1 (by rfl) ⟨301055, by rfl⟩ : syracuseStep 401407 = 602111) B602111
theorem B6889535 : Blo 397767 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B2270267 : Blo 397767 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B959615 : Blo 397767 959615 := bstep (se 1 (by rfl) ⟨719711, by rfl⟩ : syracuseStep 959615 = 1439423) B1439423
theorem B8234743 : Blo 397767 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B600119 : Blo 397767 600119 := bstep (se 1 (by rfl) ⟨450089, by rfl⟩ : syracuseStep 600119 = 900179) B900179
theorem B895103 : Blo 397767 895103 := bstep (se 1 (by rfl) ⟨671327, by rfl⟩ : syracuseStep 895103 = 1342655) B1342655
theorem B1715327 : Blo 397767 1715327 := bstep (se 1 (by rfl) ⟨1286495, by rfl⟩ : syracuseStep 1715327 = 2572991) B2572991
theorem B1519343 : Blo 397767 1519343 := bstep (se 1 (by rfl) ⟨1139507, by rfl⟩ : syracuseStep 1519343 = 2279015) B2279015
theorem B46609037 : Blo 397767 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B504559 : Blo 397767 504559 := bstep (se 1 (by rfl) ⟨378419, by rfl⟩ : syracuseStep 504559 = 756839) B756839
theorem B898667 : Blo 397767 898667 := bstep (se 1 (by rfl) ⟨674000, by rfl⟩ : syracuseStep 898667 = 1348001) B1348001
theorem B11908883 : Blo 397767 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B898919 : Blo 397767 898919 := bstep (se 1 (by rfl) ⟨674189, by rfl⟩ : syracuseStep 898919 = 1348379) B1348379
theorem B505703 : Blo 397767 505703 := bstep (se 1 (by rfl) ⟨379277, by rfl⟩ : syracuseStep 505703 = 758555) B758555
theorem B899567 : Blo 397767 899567 := bstep (se 1 (by rfl) ⟨674675, by rfl⟩ : syracuseStep 899567 = 1349351) B1349351
theorem B639647 : Blo 397767 639647 := bstep (se 1 (by rfl) ⟨479735, by rfl⟩ : syracuseStep 639647 = 959471) B959471
theorem B15025409 : Blo 397767 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B673231 : Blo 397767 673231 := bstep (se 1 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 673231 = 1009847) B1009847
theorem B1625579 : Blo 397767 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B643145 : Blo 397767 643145 := bstep (se 2 (by rfl) ⟨241179, by rfl⟩ : syracuseStep 643145 = 482359) B482359
theorem B676073 : Blo 397767 676073 := bstep (se 2 (by rfl) ⟨253527, by rfl⟩ : syracuseStep 676073 = 507055) B507055
theorem B450607 : Blo 397767 450607 := bstep (se 1 (by rfl) ⟨337955, by rfl⟩ : syracuseStep 450607 = 675911) B675911
theorem B2286305 : Blo 397767 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B648959 : Blo 397767 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B2877545 : Blo 397767 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B813439 : Blo 397767 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B1075643 : Blo 397767 1075643 := bstep (se 1 (by rfl) ⟨806732, by rfl⟩ : syracuseStep 1075643 = 1613465) B1613465
theorem B7367561 : Blo 397767 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B6909887 : Blo 397767 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B3242621 : Blo 397767 3242621 := bstep (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) B1215983
theorem B1014727 : Blo 397767 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B426431 : Blo 397767 426431 := bstep (se 1 (by rfl) ⟨319823, by rfl⟩ : syracuseStep 426431 = 639647) B639647
theorem B1083719 : Blo 397767 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B10979657 : Blo 397767 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B1084585 : Blo 397767 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B398107 : Blo 397767 398107 := bstep (se 1 (by rfl) ⟨298580, by rfl⟩ : syracuseStep 398107 = 597161) B597161
theorem B1348541 : Blo 397767 1348541 := bstep (se 3 (by rfl) ⟨252851, by rfl⟩ : syracuseStep 1348541 = 505703) B505703
theorem B2167975 : Blo 397767 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B1447163 : Blo 397767 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B4593023 : Blo 397767 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B7673453 : Blo 397767 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B1513511 : Blo 397767 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B400079 : Blo 397767 400079 := bstep (se 1 (by rfl) ⟨300059, by rfl⟩ : syracuseStep 400079 = 600119) B600119
theorem B596735 : Blo 397767 596735 := bstep (se 1 (by rfl) ⟨447551, by rfl⟩ : syracuseStep 596735 = 895103) B895103
theorem B31072691 : Blo 397767 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B599111 : Blo 397767 599111 := bstep (se 1 (by rfl) ⟨449333, by rfl⟩ : syracuseStep 599111 = 898667) B898667
theorem B7939255 : Blo 397767 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B599279 : Blo 397767 599279 := bstep (se 1 (by rfl) ⟨449459, by rfl⟩ : syracuseStep 599279 = 898919) B898919
theorem B1352969 : Blo 397767 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B599711 : Blo 397767 599711 := bstep (se 1 (by rfl) ⟨449783, by rfl⟩ : syracuseStep 599711 = 899567) B899567
theorem B18426365 : Blo 397767 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B600809 : Blo 397767 600809 := bstep (se 2 (by rfl) ⟨225303, by rfl⟩ : syracuseStep 600809 = 450607) B450607
theorem B1715053 : Blo 397767 1715053 := bstep (se 3 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 1715053 = 643145) B643145
theorem B2075975 : Blo 397767 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B962075 : Blo 397767 962075 := bstep (se 1 (by rfl) ⟨721556, by rfl⟩ : syracuseStep 962075 = 1443113) B1443113
theorem B897641 : Blo 397767 897641 := bstep (se 2 (by rfl) ⟨336615, by rfl⟩ : syracuseStep 897641 = 673231) B673231
theorem B4111663 : Blo 397767 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B1524203 : Blo 397767 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B639743 : Blo 397767 639743 := bstep (se 1 (by rfl) ⟨479807, by rfl⟩ : syracuseStep 639743 = 959615) B959615
theorem B672745 : Blo 397767 672745 := bstep (se 2 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 672745 = 504559) B504559
theorem B970729 : Blo 397767 970729 := bstep (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) B728047
theorem B10016939 : Blo 397767 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B3430583 : Blo 397767 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B3038471 : Blo 397767 3038471 := bstep (se 1 (by rfl) ⟨2278853, by rfl⟩ : syracuseStep 3038471 = 4557707) B4557707
theorem B1007579 : Blo 397767 1007579 := bstep (se 1 (by rfl) ⟨755684, by rfl⟩ : syracuseStep 1007579 = 1511369) B1511369
theorem B450715 : Blo 397767 450715 := bstep (se 1 (by rfl) ⟨338036, by rfl⟩ : syracuseStep 450715 = 676073) B676073
theorem B1730557 : Blo 397767 1730557 := bstep (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) B648959
theorem B717095 : Blo 397767 717095 := bstep (se 1 (by rfl) ⟨537821, by rfl⟩ : syracuseStep 717095 = 1075643) B1075643
theorem B4911707 : Blo 397767 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B1143551 : Blo 397767 1143551 := bstep (se 1 (by rfl) ⟨857663, by rfl⟩ : syracuseStep 1143551 = 1715327) B1715327
theorem B1012895 : Blo 397767 1012895 := bstep (se 1 (by rfl) ⟨759671, by rfl⟩ : syracuseStep 1012895 = 1519343) B1519343
theorem B4553333 : Blo 397767 4553333 := bstep (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) B426875
theorem B2161747 : Blo 397767 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B1016135 : Blo 397767 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B10585673 : Blo 397767 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B1705981 : Blo 397767 1705981 := bstep (se 3 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 1705981 = 639743) B639743
theorem B5115635 : Blo 397767 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B1446113 : Blo 397767 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B397823 : Blo 397767 397823 := bstep (se 1 (by rfl) ⟨298367, by rfl⟩ : syracuseStep 397823 = 596735) B596735
theorem B399407 : Blo 397767 399407 := bstep (se 1 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 399407 = 599111) B599111
theorem B399519 : Blo 397767 399519 := bstep (se 1 (by rfl) ⟨299639, by rfl⟩ : syracuseStep 399519 = 599279) B599279
theorem B2889917 : Blo 397767 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B399807 : Blo 397767 399807 := bstep (se 1 (by rfl) ⟨299855, by rfl⟩ : syracuseStep 399807 = 599711) B599711
theorem B400539 : Blo 397767 400539 := bstep (se 1 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 400539 = 600809) B600809
theorem B1383983 : Blo 397767 1383983 := bstep (se 1 (by rfl) ⟨1037987, by rfl⟩ : syracuseStep 1383983 = 2075975) B2075975
theorem B598427 : Blo 397767 598427 := bstep (se 1 (by rfl) ⟨448820, by rfl⟩ : syracuseStep 598427 = 897641) B897641
theorem B762367 : Blo 397767 762367 := bstep (se 1 (by rfl) ⟨571775, by rfl⟩ : syracuseStep 762367 = 1143551) B1143551
theorem B2565533 : Blo 397767 2565533 := bstep (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) B962075
theorem B5482217 : Blo 397767 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B600953 : Blo 397767 600953 := bstep (se 2 (by rfl) ⟨225357, by rfl⟩ : syracuseStep 600953 = 450715) B450715
theorem B896993 : Blo 397767 896993 := bstep (se 2 (by rfl) ⟨336372, by rfl⟩ : syracuseStep 896993 = 672745) B672745
theorem B7319771 : Blo 397767 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B2307409 : Blo 397767 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B899027 : Blo 397767 899027 := bstep (se 1 (by rfl) ⟨674270, by rfl⟩ : syracuseStep 899027 = 1348541) B1348541
theorem B964775 : Blo 397767 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B3062015 : Blo 397767 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B671719 : Blo 397767 671719 := bstep (se 1 (by rfl) ⟨503789, by rfl⟩ : syracuseStep 671719 = 1007579) B1007579
theorem B901979 : Blo 397767 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B478063 : Blo 397767 478063 := bstep (se 1 (by rfl) ⟨358547, by rfl⟩ : syracuseStep 478063 = 717095) B717095
theorem B675263 : Blo 397767 675263 := bstep (se 1 (by rfl) ⟨506447, by rfl⟩ : syracuseStep 675263 = 1012895) B1012895
theorem B3035555 : Blo 397767 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B82860509 : Blo 397767 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B1137149 : Blo 397767 1137149 := bstep (se 3 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 1137149 = 426431) B426431
theorem B2286737 : Blo 397767 2286737 := bstep (se 2 (by rfl) ⟨857526, by rfl⟩ : syracuseStep 2286737 = 1715053) B1715053
theorem B1009007 : Blo 397767 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B6677959 : Blo 397767 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B2287055 : Blo 397767 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B2025647 : Blo 397767 2025647 := bstep (se 1 (by rfl) ⟨1519235, by rfl⟩ : syracuseStep 2025647 = 3038471) B3038471
theorem B11529317 : Blo 397767 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B11562533 : Blo 397767 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B12284243 : Blo 397767 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B3274471 : Blo 397767 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B20708885 : Blo 397767 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B1016489 : Blo 397767 1016489 := bstep (se 2 (by rfl) ⟨381183, by rfl⟩ : syracuseStep 1016489 = 762367) B762367
theorem B3410423 : Blo 397767 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B758099 : Blo 397767 758099 := bstep (se 1 (by rfl) ⟨568574, by rfl⟩ : syracuseStep 758099 = 1137149) B1137149
theorem B922655 : Blo 397767 922655 := bstep (se 1 (by rfl) ⟨691991, by rfl⟩ : syracuseStep 922655 = 1383983) B1383983
theorem B398951 : Blo 397767 398951 := bstep (se 1 (by rfl) ⟨299213, by rfl⟩ : syracuseStep 398951 = 598427) B598427
theorem B1710355 : Blo 397767 1710355 := bstep (se 1 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 1710355 = 2565533) B2565533
theorem B1350431 : Blo 397767 1350431 := bstep (se 1 (by rfl) ⟨1012823, by rfl⟩ : syracuseStep 1350431 = 2025647) B2025647
theorem B400635 : Blo 397767 400635 := bstep (se 1 (by rfl) ⟨300476, by rfl⟩ : syracuseStep 400635 = 600953) B600953
theorem B7708355 : Blo 397767 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B597995 : Blo 397767 597995 := bstep (se 1 (by rfl) ⟨448496, by rfl⟩ : syracuseStep 597995 = 896993) B896993
theorem B599351 : Blo 397767 599351 := bstep (se 1 (by rfl) ⟨449513, by rfl⟩ : syracuseStep 599351 = 899027) B899027
theorem B2041343 : Blo 397767 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B13805923 : Blo 397767 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B895625 : Blo 397767 895625 := bstep (se 2 (by rfl) ⟨335859, by rfl⟩ : syracuseStep 895625 = 671719) B671719
theorem B601319 : Blo 397767 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B7057115 : Blo 397767 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B2274641 : Blo 397767 2274641 := bstep (se 2 (by rfl) ⟨852990, by rfl⟩ : syracuseStep 2274641 = 1705981) B1705981
theorem B964075 : Blo 397767 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B637417 : Blo 397767 637417 := bstep (se 2 (by rfl) ⟨239031, by rfl⟩ : syracuseStep 637417 = 478063) B478063
theorem B1524491 : Blo 397767 1524491 := bstep (se 1 (by rfl) ⟨1143368, by rfl⟩ : syracuseStep 1524491 = 2286737) B2286737
theorem B672671 : Blo 397767 672671 := bstep (se 1 (by rfl) ⟨504503, by rfl⟩ : syracuseStep 672671 = 1009007) B1009007
theorem B1524703 : Blo 397767 1524703 := bstep (se 1 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 1524703 = 2287055) B2287055
theorem B3654811 : Blo 397767 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B12306181 : Blo 397767 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B7686211 : Blo 397767 7686211 := bstep (se 1 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 7686211 = 11529317) B11529317
theorem B643183 : Blo 397767 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B677423 : Blo 397767 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B8903945 : Blo 397767 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B450175 : Blo 397767 450175 := bstep (se 1 (by rfl) ⟨337631, by rfl⟩ : syracuseStep 450175 = 675263) B675263
theorem B2023703 : Blo 397767 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B1926611 : Blo 397767 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B55240339 : Blo 397767 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B4879847 : Blo 397767 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B8189495 : Blo 397767 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B17463845 : Blo 397767 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B1016327 : Blo 397767 1016327 := bstep (se 1 (by rfl) ⟨762245, by rfl⟩ : syracuseStep 1016327 = 1524491) B1524491
theorem B2032937 : Blo 397767 2032937 := bstep (se 2 (by rfl) ⟨762351, by rfl⟩ : syracuseStep 2032937 = 1524703) B1524703
theorem B2460413 : Blo 397767 2460413 := bstep (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) B922655
theorem B5935963 : Blo 397767 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B398663 : Blo 397767 398663 := bstep (se 1 (by rfl) ⟨298997, by rfl⟩ : syracuseStep 398663 = 597995) B597995
theorem B1349135 : Blo 397767 1349135 := bstep (se 1 (by rfl) ⟨1011851, by rfl⟩ : syracuseStep 1349135 = 2023703) B2023703
theorem B399567 : Blo 397767 399567 := bstep (se 1 (by rfl) ⟨299675, by rfl⟩ : syracuseStep 399567 = 599351) B599351
theorem B1284407 : Blo 397767 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B597083 : Blo 397767 597083 := bstep (se 1 (by rfl) ⟨447812, by rfl⟩ : syracuseStep 597083 = 895625) B895625
theorem B1285433 : Blo 397767 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B400879 : Blo 397767 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B1516427 : Blo 397767 1516427 := bstep (se 1 (by rfl) ⟨1137320, by rfl⟩ : syracuseStep 1516427 = 2274641) B2274641
theorem B3253231 : Blo 397767 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B11642563 : Blo 397767 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B600233 : Blo 397767 600233 := bstep (se 2 (by rfl) ⟨225087, by rfl⟩ : syracuseStep 600233 = 450175) B450175
theorem B2273615 : Blo 397767 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B900287 : Blo 397767 900287 := bstep (se 1 (by rfl) ⟨675215, by rfl⟩ : syracuseStep 900287 = 1350431) B1350431
theorem B1360895 : Blo 397767 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B4704743 : Blo 397767 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B2280473 : Blo 397767 2280473 := bstep (se 2 (by rfl) ⟨855177, by rfl⟩ : syracuseStep 2280473 = 1710355) B1710355
theorem B5459663 : Blo 397767 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B677659 : Blo 397767 677659 := bstep (se 1 (by rfl) ⟨508244, by rfl⟩ : syracuseStep 677659 = 1016489) B1016489
theorem B3430309 : Blo 397767 3430309 := bstep (se 4 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 3430309 = 643183) B643183
theorem B448447 : Blo 397767 448447 := bstep (se 1 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 448447 = 672671) B672671
theorem B2021597 : Blo 397767 2021597 := bstep (se 3 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 2021597 = 758099) B758099
theorem B4873081 : Blo 397767 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B73653785 : Blo 397767 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B16408241 : Blo 397767 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B10248281 : Blo 397767 10248281 := bstep (se 2 (by rfl) ⟨3843105, by rfl⟩ : syracuseStep 10248281 = 7686211) B7686211
theorem B18407897 : Blo 397767 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B451615 : Blo 397767 451615 := bstep (se 1 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 451615 = 677423) B677423
theorem B5138903 : Blo 397767 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B849889 : Blo 397767 849889 := bstep (se 2 (by rfl) ⟨318708, by rfl⟩ : syracuseStep 849889 = 637417) B637417
theorem B1347731 : Blo 397767 1347731 := bstep (se 1 (by rfl) ⟨1010798, by rfl⟩ : syracuseStep 1347731 = 2021597) B2021597
theorem B856271 : Blo 397767 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B398055 : Blo 397767 398055 := bstep (se 1 (by rfl) ⟨298541, by rfl⟩ : syracuseStep 398055 = 597083) B597083
theorem B856955 : Blo 397767 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B400155 : Blo 397767 400155 := bstep (se 1 (by rfl) ⟨300116, by rfl⟩ : syracuseStep 400155 = 600233) B600233
theorem B6561101 : Blo 397767 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B597929 : Blo 397767 597929 := bstep (se 2 (by rfl) ⟨224223, by rfl⟩ : syracuseStep 597929 = 448447) B448447
theorem B1515743 : Blo 397767 1515743 := bstep (se 1 (by rfl) ⟨1136807, by rfl⟩ : syracuseStep 1515743 = 2273615) B2273615
theorem B6497441 : Blo 397767 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B14559101 : Blo 397767 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B600191 : Blo 397767 600191 := bstep (se 1 (by rfl) ⟨450143, by rfl⟩ : syracuseStep 600191 = 900287) B900287
theorem B1355291 : Blo 397767 1355291 := bstep (se 1 (by rfl) ⟨1016468, by rfl⟩ : syracuseStep 1355291 = 2032937) B2032937
theorem B4337641 : Blo 397767 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B602153 : Blo 397767 602153 := bstep (se 2 (by rfl) ⟨225807, by rfl⟩ : syracuseStep 602153 = 451615) B451615
theorem B1520315 : Blo 397767 1520315 := bstep (se 1 (by rfl) ⟨1140236, by rfl⟩ : syracuseStep 1520315 = 2280473) B2280473
theorem B899423 : Blo 397767 899423 := bstep (se 1 (by rfl) ⟨674567, by rfl⟩ : syracuseStep 899423 = 1349135) B1349135
theorem B49102523 : Blo 397767 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B6832187 : Blo 397767 6832187 := bstep (se 1 (by rfl) ⟨5124140, by rfl⟩ : syracuseStep 6832187 = 10248281) B10248281
theorem B12271931 : Blo 397767 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B7914617 : Blo 397767 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B3425935 : Blo 397767 3425935 := bstep (se 1 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 3425935 = 5138903) B5138903
theorem B903545 : Blo 397767 903545 := bstep (se 2 (by rfl) ⟨338829, by rfl⟩ : syracuseStep 903545 = 677659) B677659
theorem B4573745 : Blo 397767 4573745 := bstep (se 2 (by rfl) ⟨1715154, by rfl⟩ : syracuseStep 4573745 = 3430309) B3430309
theorem B1133185 : Blo 397767 1133185 := bstep (se 2 (by rfl) ⟨424944, by rfl⟩ : syracuseStep 1133185 = 849889) B849889
theorem B677551 : Blo 397767 677551 := bstep (se 1 (by rfl) ⟨508163, by rfl⟩ : syracuseStep 677551 = 1016327) B1016327
theorem B3136495 : Blo 397767 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B15523417 : Blo 397767 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B3629053 : Blo 397767 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B10938827 : Blo 397767 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B1010951 : Blo 397767 1010951 := bstep (se 1 (by rfl) ⟨758213, by rfl⟩ : syracuseStep 1010951 = 1516427) B1516427
theorem B4554791 : Blo 397767 4554791 := bstep (se 1 (by rfl) ⟨3416093, by rfl⟩ : syracuseStep 4554791 = 6832187) B6832187
theorem B5276411 : Blo 397767 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B3049163 : Blo 397767 3049163 := bstep (se 1 (by rfl) ⟨2286872, by rfl⟩ : syracuseStep 3049163 = 4573745) B4573745
theorem B1510913 : Blo 397767 1510913 := bstep (se 2 (by rfl) ⟨566592, by rfl⟩ : syracuseStep 1510913 = 1133185) B1133185
theorem B398619 : Blo 397767 398619 := bstep (se 1 (by rfl) ⟨298964, by rfl⟩ : syracuseStep 398619 = 597929) B597929
theorem B4331627 : Blo 397767 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B29170205 : Blo 397767 29170205 := bstep (se 3 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 29170205 = 10938827) B10938827
theorem B9706067 : Blo 397767 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B400127 : Blo 397767 400127 := bstep (se 1 (by rfl) ⟨300095, by rfl⟩ : syracuseStep 400127 = 600191) B600191
theorem B401435 : Blo 397767 401435 := bstep (se 1 (by rfl) ⟨301076, by rfl⟩ : syracuseStep 401435 = 602153) B602153
theorem B599615 : Blo 397767 599615 := bstep (se 1 (by rfl) ⟨449711, by rfl⟩ : syracuseStep 599615 = 899423) B899423
theorem B602363 : Blo 397767 602363 := bstep (se 1 (by rfl) ⟨451772, by rfl⟩ : syracuseStep 602363 = 903545) B903545
theorem B4567913 : Blo 397767 4567913 := bstep (se 2 (by rfl) ⟨1712967, by rfl⟩ : syracuseStep 4567913 = 3425935) B3425935
theorem B898487 : Blo 397767 898487 := bstep (se 1 (by rfl) ⟨673865, by rfl⟩ : syracuseStep 898487 = 1347731) B1347731
theorem B571303 : Blo 397767 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B4374067 : Blo 397767 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B5783521 : Blo 397767 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B673967 : Blo 397767 673967 := bstep (se 1 (by rfl) ⟨505475, by rfl⟩ : syracuseStep 673967 = 1010951) B1010951
theorem B903401 : Blo 397767 903401 := bstep (se 2 (by rfl) ⟨338775, by rfl⟩ : syracuseStep 903401 = 677551) B677551
theorem B903527 : Blo 397767 903527 := bstep (se 1 (by rfl) ⟨677645, by rfl⟩ : syracuseStep 903527 = 1355291) B1355291
theorem B4181993 : Blo 397767 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B20697889 : Blo 397767 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B4838737 : Blo 397767 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B8181287 : Blo 397767 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B2283389 : Blo 397767 2283389 := bstep (se 3 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 2283389 = 856271) B856271
theorem B1010495 : Blo 397767 1010495 := bstep (se 1 (by rfl) ⟨757871, by rfl⟩ : syracuseStep 1010495 = 1515743) B1515743
theorem B1013543 : Blo 397767 1013543 := bstep (se 1 (by rfl) ⟨760157, by rfl⟩ : syracuseStep 1013543 = 1520315) B1520315
theorem B32735015 : Blo 397767 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B2032775 : Blo 397767 2032775 := bstep (se 1 (by rfl) ⟨1524581, by rfl⟩ : syracuseStep 2032775 = 3049163) B3049163
theorem B2787995 : Blo 397767 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B2887751 : Blo 397767 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B399743 : Blo 397767 399743 := bstep (se 1 (by rfl) ⟨299807, by rfl⟩ : syracuseStep 399743 = 599615) B599615
theorem B27597185 : Blo 397767 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B761737 : Blo 397767 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B401575 : Blo 397767 401575 := bstep (se 1 (by rfl) ⟨301181, by rfl⟩ : syracuseStep 401575 = 602363) B602363
theorem B598991 : Blo 397767 598991 := bstep (se 1 (by rfl) ⟨449243, by rfl⟩ : syracuseStep 598991 = 898487) B898487
theorem B7711361 : Blo 397767 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B3517607 : Blo 397767 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B602267 : Blo 397767 602267 := bstep (se 1 (by rfl) ⟨451700, by rfl⟩ : syracuseStep 602267 = 903401) B903401
theorem B602351 : Blo 397767 602351 := bstep (se 1 (by rfl) ⟨451763, by rfl⟩ : syracuseStep 602351 = 903527) B903527
theorem B5454191 : Blo 397767 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B1522259 : Blo 397767 1522259 := bstep (se 1 (by rfl) ⟨1141694, by rfl⟩ : syracuseStep 1522259 = 2283389) B2283389
theorem B19446803 : Blo 397767 19446803 := bstep (se 1 (by rfl) ⟨14585102, by rfl⟩ : syracuseStep 19446803 = 29170205) B29170205
theorem B6470711 : Blo 397767 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B673663 : Blo 397767 673663 := bstep (se 1 (by rfl) ⟨505247, by rfl⟩ : syracuseStep 673663 = 1010495) B1010495
theorem B675695 : Blo 397767 675695 := bstep (se 1 (by rfl) ⟨506771, by rfl⟩ : syracuseStep 675695 = 1013543) B1013543
theorem B3036527 : Blo 397767 3036527 := bstep (se 1 (by rfl) ⟨2277395, by rfl⟩ : syracuseStep 3036527 = 4554791) B4554791
theorem B449311 : Blo 397767 449311 := bstep (se 1 (by rfl) ⟨336983, by rfl⟩ : syracuseStep 449311 = 673967) B673967
theorem B1007275 : Blo 397767 1007275 := bstep (se 1 (by rfl) ⟨755456, by rfl⟩ : syracuseStep 1007275 = 1510913) B1510913
theorem B6451649 : Blo 397767 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B3045275 : Blo 397767 3045275 := bstep (se 1 (by rfl) ⟨2283956, by rfl⟩ : syracuseStep 3045275 = 4567913) B4567913
theorem B5832089 : Blo 397767 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B21823343 : Blo 397767 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B7700669 : Blo 397767 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B399327 : Blo 397767 399327 := bstep (se 1 (by rfl) ⟨299495, by rfl⟩ : syracuseStep 399327 = 598991) B598991
theorem B401511 : Blo 397767 401511 := bstep (se 1 (by rfl) ⟨301133, by rfl⟩ : syracuseStep 401511 = 602267) B602267
theorem B401567 : Blo 397767 401567 := bstep (se 1 (by rfl) ⟨301175, by rfl⟩ : syracuseStep 401567 = 602351) B602351
theorem B4301099 : Blo 397767 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B599081 : Blo 397767 599081 := bstep (se 2 (by rfl) ⟨224655, by rfl⟩ : syracuseStep 599081 = 449311) B449311
theorem B1355183 : Blo 397767 1355183 := bstep (se 1 (by rfl) ⟨1016387, by rfl⟩ : syracuseStep 1355183 = 2032775) B2032775
theorem B898217 : Blo 397767 898217 := bstep (se 2 (by rfl) ⟨336831, by rfl⟩ : syracuseStep 898217 = 673663) B673663
theorem B18398123 : Blo 397767 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B2345071 : Blo 397767 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B12964535 : Blo 397767 12964535 := bstep (se 1 (by rfl) ⟨9723401, by rfl⟩ : syracuseStep 12964535 = 19446803) B19446803
theorem B4313807 : Blo 397767 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B3888059 : Blo 397767 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B1858663 : Blo 397767 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B450463 : Blo 397767 450463 := bstep (se 1 (by rfl) ⟨337847, by rfl⟩ : syracuseStep 450463 = 675695) B675695
theorem B2024351 : Blo 397767 2024351 := bstep (se 1 (by rfl) ⟨1518263, by rfl⟩ : syracuseStep 2024351 = 3036527) B3036527
theorem B5140907 : Blo 397767 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B2030183 : Blo 397767 2030183 := bstep (se 1 (by rfl) ⟨1522637, by rfl⟩ : syracuseStep 2030183 = 3045275) B3045275
theorem B3636127 : Blo 397767 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1014839 : Blo 397767 1014839 := bstep (se 1 (by rfl) ⟨761129, by rfl⟩ : syracuseStep 1014839 = 1522259) B1522259
theorem B1343033 : Blo 397767 1343033 := bstep (se 2 (by rfl) ⟨503637, by rfl⟩ : syracuseStep 1343033 = 1007275) B1007275
theorem B1015649 : Blo 397767 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B14548895 : Blo 397767 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B1349567 : Blo 397767 1349567 := bstep (se 1 (by rfl) ⟨1012175, by rfl⟩ : syracuseStep 1349567 = 2024351) B2024351
theorem B399387 : Blo 397767 399387 := bstep (se 1 (by rfl) ⟨299540, by rfl⟩ : syracuseStep 399387 = 599081) B599081
theorem B598811 : Blo 397767 598811 := bstep (se 1 (by rfl) ⟨449108, by rfl⟩ : syracuseStep 598811 = 898217) B898217
theorem B1353455 : Blo 397767 1353455 := bstep (se 1 (by rfl) ⟨1015091, by rfl⟩ : syracuseStep 1353455 = 2030183) B2030183
theorem B12265415 : Blo 397767 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B895355 : Blo 397767 895355 := bstep (se 1 (by rfl) ⟨671516, by rfl⟩ : syracuseStep 895355 = 1343033) B1343033
theorem B600617 : Blo 397767 600617 := bstep (se 2 (by rfl) ⟨225231, by rfl⟩ : syracuseStep 600617 = 450463) B450463
theorem B10368157 : Blo 397767 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B3126761 : Blo 397767 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B2867399 : Blo 397767 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B903455 : Blo 397767 903455 := bstep (se 1 (by rfl) ⟨677591, by rfl⟩ : syracuseStep 903455 = 1355183) B1355183
theorem B3427271 : Blo 397767 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B2478217 : Blo 397767 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B676559 : Blo 397767 676559 := bstep (se 1 (by rfl) ⟨507419, by rfl⟩ : syracuseStep 676559 = 1014839) B1014839
theorem B677099 : Blo 397767 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B5133779 : Blo 397767 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B8643023 : Blo 397767 8643023 := bstep (se 1 (by rfl) ⟨6482267, by rfl⟩ : syracuseStep 8643023 = 12964535) B12964535
theorem B2875871 : Blo 397767 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B4848169 : Blo 397767 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B9699263 : Blo 397767 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B7668989 : Blo 397767 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B399207 : Blo 397767 399207 := bstep (se 1 (by rfl) ⟨299405, by rfl⟩ : syracuseStep 399207 = 598811) B598811
theorem B596903 : Blo 397767 596903 := bstep (se 1 (by rfl) ⟨447677, by rfl⟩ : syracuseStep 596903 = 895355) B895355
theorem B400411 : Blo 397767 400411 := bstep (se 1 (by rfl) ⟨300308, by rfl⟩ : syracuseStep 400411 = 600617) B600617
theorem B6464225 : Blo 397767 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B6466175 : Blo 397767 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B1911599 : Blo 397767 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B602303 : Blo 397767 602303 := bstep (se 1 (by rfl) ⟨451727, by rfl⟩ : syracuseStep 602303 = 903455) B903455
theorem B52868629 : Blo 397767 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B3422519 : Blo 397767 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B899711 : Blo 397767 899711 := bstep (se 1 (by rfl) ⟨674783, by rfl⟩ : syracuseStep 899711 = 1349567) B1349567
theorem B902303 : Blo 397767 902303 := bstep (se 1 (by rfl) ⟨676727, by rfl⟩ : syracuseStep 902303 = 1353455) B1353455
theorem B8176943 : Blo 397767 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B2084507 : Blo 397767 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B2284847 : Blo 397767 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B451039 : Blo 397767 451039 := bstep (se 1 (by rfl) ⟨338279, by rfl⟩ : syracuseStep 451039 = 676559) B676559
theorem B451399 : Blo 397767 451399 := bstep (se 1 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 451399 = 677099) B677099
theorem B5762015 : Blo 397767 5762015 := bstep (se 1 (by rfl) ⟨4321511, by rfl⟩ : syracuseStep 5762015 = 8643023) B8643023
theorem B13824209 : Blo 397767 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B5112659 : Blo 397767 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B17237933 : Blo 397767 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B397935 : Blo 397767 397935 := bstep (se 1 (by rfl) ⟨298451, by rfl⟩ : syracuseStep 397935 = 596903) B596903
theorem B3841343 : Blo 397767 3841343 := bstep (se 1 (by rfl) ⟨2881007, by rfl⟩ : syracuseStep 3841343 = 5762015) B5762015
theorem B70491505 : Blo 397767 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B401535 : Blo 397767 401535 := bstep (se 1 (by rfl) ⟨301151, by rfl⟩ : syracuseStep 401535 = 602303) B602303
theorem B9216139 : Blo 397767 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B599807 : Blo 397767 599807 := bstep (se 1 (by rfl) ⟨449855, by rfl⟩ : syracuseStep 599807 = 899711) B899711
theorem B601385 : Blo 397767 601385 := bstep (se 2 (by rfl) ⟨225519, by rfl⟩ : syracuseStep 601385 = 451039) B451039
theorem B601535 : Blo 397767 601535 := bstep (se 1 (by rfl) ⟨451151, by rfl⟩ : syracuseStep 601535 = 902303) B902303
theorem B5451295 : Blo 397767 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B601865 : Blo 397767 601865 := bstep (se 2 (by rfl) ⟨225699, by rfl⟩ : syracuseStep 601865 = 451399) B451399
theorem B1389671 : Blo 397767 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B1523231 : Blo 397767 1523231 := bstep (se 1 (by rfl) ⟨1142423, by rfl⟩ : syracuseStep 1523231 = 2284847) B2284847
theorem B4310783 : Blo 397767 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B2281679 : Blo 397767 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B1274399 : Blo 397767 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B12288185 : Blo 397767 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B3408439 : Blo 397767 3408439 := bstep (se 1 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 3408439 = 5112659) B5112659
theorem B2560895 : Blo 397767 2560895 := bstep (se 1 (by rfl) ⟨1920671, by rfl⟩ : syracuseStep 2560895 = 3841343) B3841343
theorem B399871 : Blo 397767 399871 := bstep (se 1 (by rfl) ⟨299903, by rfl⟩ : syracuseStep 399871 = 599807) B599807
theorem B400923 : Blo 397767 400923 := bstep (se 1 (by rfl) ⟨300692, by rfl⟩ : syracuseStep 400923 = 601385) B601385
theorem B401023 : Blo 397767 401023 := bstep (se 1 (by rfl) ⟨300767, by rfl⟩ : syracuseStep 401023 = 601535) B601535
theorem B401243 : Blo 397767 401243 := bstep (se 1 (by rfl) ⟨300932, by rfl⟩ : syracuseStep 401243 = 601865) B601865
theorem B926447 : Blo 397767 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B93988673 : Blo 397767 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B1521119 : Blo 397767 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B2873855 : Blo 397767 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B11491955 : Blo 397767 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B7268393 : Blo 397767 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B849599 : Blo 397767 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B1015487 : Blo 397767 1015487 := bstep (se 1 (by rfl) ⟨761615, by rfl⟩ : syracuseStep 1015487 = 1523231) B1523231
theorem B8192123 : Blo 397767 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B1707263 : Blo 397767 1707263 := bstep (se 1 (by rfl) ⟨1280447, by rfl⟩ : syracuseStep 1707263 = 2560895) B2560895
theorem B62659115 : Blo 397767 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B566399 : Blo 397767 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B1915903 : Blo 397767 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B9882101 : Blo 397767 9882101 := bstep (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) B926447
theorem B676991 : Blo 397767 676991 := bstep (se 1 (by rfl) ⟨507743, by rfl⟩ : syracuseStep 676991 = 1015487) B1015487
theorem B4544585 : Blo 397767 4544585 := bstep (se 2 (by rfl) ⟨1704219, by rfl⟩ : syracuseStep 4544585 = 3408439) B3408439
theorem B7661303 : Blo 397767 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B4845595 : Blo 397767 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B1014079 : Blo 397767 1014079 := bstep (se 1 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 1014079 = 1521119) B1521119
theorem B6588067 : Blo 397767 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B1510397 : Blo 397767 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B6460793 : Blo 397767 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B1352105 : Blo 397767 1352105 := bstep (se 2 (by rfl) ⟨507039, by rfl⟩ : syracuseStep 1352105 = 1014079) B1014079
theorem B3029723 : Blo 397767 3029723 := bstep (se 1 (by rfl) ⟨2272292, by rfl⟩ : syracuseStep 3029723 = 4544585) B4544585
theorem B5461415 : Blo 397767 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B1138175 : Blo 397767 1138175 := bstep (se 1 (by rfl) ⟨853631, by rfl⟩ : syracuseStep 1138175 = 1707263) B1707263
theorem B451327 : Blo 397767 451327 := bstep (se 1 (by rfl) ⟨338495, by rfl⟩ : syracuseStep 451327 = 676991) B676991
theorem B41772743 : Blo 397767 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B5107535 : Blo 397767 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B2554537 : Blo 397767 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B8784089 : Blo 397767 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B3640943 : Blo 397767 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B758783 : Blo 397767 758783 := bstep (se 1 (by rfl) ⟨569087, by rfl⟩ : syracuseStep 758783 = 1138175) B1138175
theorem B601769 : Blo 397767 601769 := bstep (se 2 (by rfl) ⟨225663, by rfl⟩ : syracuseStep 601769 = 451327) B451327
theorem B4307195 : Blo 397767 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B901403 : Blo 397767 901403 := bstep (se 1 (by rfl) ⟨676052, by rfl⟩ : syracuseStep 901403 = 1352105) B1352105
theorem B2019815 : Blo 397767 2019815 := bstep (se 1 (by rfl) ⟨1514861, by rfl⟩ : syracuseStep 2019815 = 3029723) B3029723
theorem B1006931 : Blo 397767 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B27848495 : Blo 397767 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B3405023 : Blo 397767 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B3406049 : Blo 397767 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B2427295 : Blo 397767 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B1346543 : Blo 397767 1346543 := bstep (se 1 (by rfl) ⟨1009907, by rfl⟩ : syracuseStep 1346543 = 2019815) B2019815
theorem B401179 : Blo 397767 401179 := bstep (se 1 (by rfl) ⟨300884, by rfl⟩ : syracuseStep 401179 = 601769) B601769
theorem B2270015 : Blo 397767 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B2270699 : Blo 397767 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B74262653 : Blo 397767 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B600935 : Blo 397767 600935 := bstep (se 1 (by rfl) ⟨450701, by rfl⟩ : syracuseStep 600935 = 901403) B901403
theorem B505855 : Blo 397767 505855 := bstep (se 1 (by rfl) ⟨379391, by rfl⟩ : syracuseStep 505855 = 758783) B758783
theorem B671287 : Blo 397767 671287 := bstep (se 1 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 671287 = 1006931) B1006931
theorem B2871463 : Blo 397767 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B5856059 : Blo 397767 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B3904039 : Blo 397767 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B1513343 : Blo 397767 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B1513799 : Blo 397767 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B400623 : Blo 397767 400623 := bstep (se 1 (by rfl) ⟨300467, by rfl⟩ : syracuseStep 400623 = 600935) B600935
theorem B895049 : Blo 397767 895049 := bstep (se 2 (by rfl) ⟨335643, by rfl⟩ : syracuseStep 895049 = 671287) B671287
theorem B897695 : Blo 397767 897695 := bstep (se 1 (by rfl) ⟨673271, by rfl⟩ : syracuseStep 897695 = 1346543) B1346543
theorem B674473 : Blo 397767 674473 := bstep (se 2 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 674473 = 505855) B505855
theorem B3236393 : Blo 397767 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B3828617 : Blo 397767 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B49508435 : Blo 397767 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B132022493 : Blo 397767 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B596699 : Blo 397767 596699 := bstep (se 1 (by rfl) ⟨447524, by rfl⟩ : syracuseStep 596699 = 895049) B895049
theorem B598463 : Blo 397767 598463 := bstep (se 1 (by rfl) ⟨448847, by rfl⟩ : syracuseStep 598463 = 897695) B897695
theorem B8630381 : Blo 397767 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B899297 : Blo 397767 899297 := bstep (se 2 (by rfl) ⟨337236, by rfl⟩ : syracuseStep 899297 = 674473) B674473
theorem B1008895 : Blo 397767 1008895 := bstep (se 1 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 1008895 = 1513343) B1513343
theorem B1009199 : Blo 397767 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B5205385 : Blo 397767 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B2552411 : Blo 397767 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B88014995 : Blo 397767 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B1345193 : Blo 397767 1345193 := bstep (se 2 (by rfl) ⟨504447, by rfl⟩ : syracuseStep 1345193 = 1008895) B1008895
theorem B397799 : Blo 397767 397799 := bstep (se 1 (by rfl) ⟨298349, by rfl⟩ : syracuseStep 397799 = 596699) B596699
theorem B398975 : Blo 397767 398975 := bstep (se 1 (by rfl) ⟨299231, by rfl⟩ : syracuseStep 398975 = 598463) B598463
theorem B599531 : Blo 397767 599531 := bstep (se 1 (by rfl) ⟨449648, by rfl⟩ : syracuseStep 599531 = 899297) B899297
theorem B672799 : Blo 397767 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B5753587 : Blo 397767 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B6940513 : Blo 397767 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B1701607 : Blo 397767 1701607 := bstep (se 1 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 1701607 = 2552411) B2552411
theorem B7671449 : Blo 397767 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B399687 : Blo 397767 399687 := bstep (se 1 (by rfl) ⟨299765, by rfl⟩ : syracuseStep 399687 = 599531) B599531
theorem B2268809 : Blo 397767 2268809 := bstep (se 2 (by rfl) ⟨850803, by rfl⟩ : syracuseStep 2268809 = 1701607) B1701607
theorem B896795 : Blo 397767 896795 := bstep (se 1 (by rfl) ⟨672596, by rfl⟩ : syracuseStep 896795 = 1345193) B1345193
theorem B897065 : Blo 397767 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B9254017 : Blo 397767 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B58676663 : Blo 397767 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B5114299 : Blo 397767 5114299 := bstep (se 1 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 5114299 = 7671449) B7671449
theorem B1512539 : Blo 397767 1512539 := bstep (se 1 (by rfl) ⟨1134404, by rfl⟩ : syracuseStep 1512539 = 2268809) B2268809
theorem B597863 : Blo 397767 597863 := bstep (se 1 (by rfl) ⟨448397, by rfl⟩ : syracuseStep 597863 = 896795) B896795
theorem B598043 : Blo 397767 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B12338689 : Blo 397767 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B39117775 : Blo 397767 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B16451585 : Blo 397767 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B6819065 : Blo 397767 6819065 := bstep (se 2 (by rfl) ⟨2557149, by rfl⟩ : syracuseStep 6819065 = 5114299) B5114299
theorem B398575 : Blo 397767 398575 := bstep (se 1 (by rfl) ⟨298931, by rfl⟩ : syracuseStep 398575 = 597863) B597863
theorem B398695 : Blo 397767 398695 := bstep (se 1 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 398695 = 598043) B598043
theorem B52157033 : Blo 397767 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B1008359 : Blo 397767 1008359 := bstep (se 1 (by rfl) ⟨756269, by rfl⟩ : syracuseStep 1008359 = 1512539) B1512539
theorem B34771355 : Blo 397767 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B672239 : Blo 397767 672239 := bstep (se 1 (by rfl) ⟨504179, by rfl⟩ : syracuseStep 672239 = 1008359) B1008359
theorem B10967723 : Blo 397767 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B4546043 : Blo 397767 4546043 := bstep (se 1 (by rfl) ⟨3409532, by rfl⟩ : syracuseStep 4546043 = 6819065) B6819065
theorem B7311815 : Blo 397767 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B23180903 : Blo 397767 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B3030695 : Blo 397767 3030695 := bstep (se 1 (by rfl) ⟨2273021, by rfl⟩ : syracuseStep 3030695 = 4546043) B4546043
theorem B448159 : Blo 397767 448159 := bstep (se 1 (by rfl) ⟨336119, by rfl⟩ : syracuseStep 448159 = 672239) B672239
theorem B597545 : Blo 397767 597545 := bstep (se 2 (by rfl) ⟨224079, by rfl⟩ : syracuseStep 597545 = 448159) B448159
theorem B15453935 : Blo 397767 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B2020463 : Blo 397767 2020463 := bstep (se 1 (by rfl) ⟨1515347, by rfl⟩ : syracuseStep 2020463 = 3030695) B3030695
theorem B4874543 : Blo 397767 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B1346975 : Blo 397767 1346975 := bstep (se 1 (by rfl) ⟨1010231, by rfl⟩ : syracuseStep 1346975 = 2020463) B2020463
theorem B398363 : Blo 397767 398363 := bstep (se 1 (by rfl) ⟨298772, by rfl⟩ : syracuseStep 398363 = 597545) B597545
theorem B3249695 : Blo 397767 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B10302623 : Blo 397767 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B2166463 : Blo 397767 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B897983 : Blo 397767 897983 := bstep (se 1 (by rfl) ⟨673487, by rfl⟩ : syracuseStep 897983 = 1346975) B1346975
theorem B6868415 : Blo 397767 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B2888617 : Blo 397767 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B598655 : Blo 397767 598655 := bstep (se 1 (by rfl) ⟨448991, by rfl⟩ : syracuseStep 598655 = 897983) B897983
theorem B18315773 : Blo 397767 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B399103 : Blo 397767 399103 := bstep (se 1 (by rfl) ⟨299327, by rfl⟩ : syracuseStep 399103 = 598655) B598655
theorem B3851489 : Blo 397767 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B12210515 : Blo 397767 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B2567659 : Blo 397767 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B8140343 : Blo 397767 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B3423545 : Blo 397767 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B86830325 : Blo 397767 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B57886883 : Blo 397767 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B2282363 : Blo 397767 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B1521575 : Blo 397767 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B38591255 : Blo 397767 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B25727503 : Blo 397767 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B1014383 : Blo 397767 1014383 := bstep (se 1 (by rfl) ⟨760787, by rfl⟩ : syracuseStep 1014383 = 1521575) B1521575
theorem B676255 : Blo 397767 676255 := bstep (se 1 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 676255 = 1014383) B1014383
theorem B34303337 : Blo 397767 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B901673 : Blo 397767 901673 := bstep (se 2 (by rfl) ⟨338127, by rfl⟩ : syracuseStep 901673 = 676255) B676255
theorem B22868891 : Blo 397767 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B15245927 : Blo 397767 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B601115 : Blo 397767 601115 := bstep (se 1 (by rfl) ⟨450836, by rfl⟩ : syracuseStep 601115 = 901673) B901673
theorem B10163951 : Blo 397767 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B400743 : Blo 397767 400743 := bstep (se 1 (by rfl) ⟨300557, by rfl⟩ : syracuseStep 400743 = 601115) B601115
theorem B6775967 : Blo 397767 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B18069245 : Blo 397767 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B12046163 : Blo 397767 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B32123101 : Blo 397767 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B42830801 : Blo 397767 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B28553867 : Blo 397767 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B19035911 : Blo 397767 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B12690607 : Blo 397767 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B16920809 : Blo 397767 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B11280539 : Blo 397767 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B7520359 : Blo 397767 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B10027145 : Blo 397767 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B6684763 : Blo 397767 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B8913017 : Blo 397767 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B5942011 : Blo 397767 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B7922681 : Blo 397767 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B5281787 : Blo 397767 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B3521191 : Blo 397767 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B4694921 : Blo 397767 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B3129947 : Blo 397767 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B2086631 : Blo 397767 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B1391087 : Blo 397767 1391087 := bstep (se 1 (by rfl) ⟨1043315, by rfl⟩ : syracuseStep 1391087 = 2086631) B2086631
theorem B927391 : Blo 397767 927391 := bstep (se 1 (by rfl) ⟨695543, by rfl⟩ : syracuseStep 927391 = 1391087) B1391087
theorem B1236521 : Blo 397767 1236521 := bstep (se 2 (by rfl) ⟨463695, by rfl⟩ : syracuseStep 1236521 = 927391) B927391
theorem B824347 : Blo 397767 824347 := bstep (se 1 (by rfl) ⟨618260, by rfl⟩ : syracuseStep 824347 = 1236521) B1236521
theorem B1099129 : Blo 397767 1099129 := bstep (se 2 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 1099129 = 824347) B824347
theorem B1465505 : Blo 397767 1465505 := bstep (se 2 (by rfl) ⟨549564, by rfl⟩ : syracuseStep 1465505 = 1099129) B1099129
theorem B977003 : Blo 397767 977003 := bstep (se 1 (by rfl) ⟨732752, by rfl⟩ : syracuseStep 977003 = 1465505) B1465505
theorem B651335 : Blo 397767 651335 := bstep (se 1 (by rfl) ⟨488501, by rfl⟩ : syracuseStep 651335 = 977003) B977003
theorem B1736893 : Blo 397767 1736893 := bstep (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) B651335
theorem B9263429 : Blo 397767 9263429 := bstep (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) B1736893
theorem B6175619 : Blo 397767 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B4117079 : Blo 397767 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B10978877 : Blo 397767 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B7319251 : Blo 397767 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B39036005 : Blo 397767 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B26024003 : Blo 397767 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B17349335 : Blo 397767 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B11566223 : Blo 397767 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B7710815 : Blo 397767 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B5140543 : Blo 397767 5140543 := bstep (se 1 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 5140543 = 7710815) B7710815
theorem B6854057 : Blo 397767 6854057 := bstep (se 2 (by rfl) ⟨2570271, by rfl⟩ : syracuseStep 6854057 = 5140543) B5140543
theorem B4569371 : Blo 397767 4569371 := bstep (se 1 (by rfl) ⟨3427028, by rfl⟩ : syracuseStep 4569371 = 6854057) B6854057
theorem B3046247 : Blo 397767 3046247 := bstep (se 1 (by rfl) ⟨2284685, by rfl⟩ : syracuseStep 3046247 = 4569371) B4569371
theorem B2030831 : Blo 397767 2030831 := bstep (se 1 (by rfl) ⟨1523123, by rfl⟩ : syracuseStep 2030831 = 3046247) B3046247
theorem B1353887 : Blo 397767 1353887 := bstep (se 1 (by rfl) ⟨1015415, by rfl⟩ : syracuseStep 1353887 = 2030831) B2030831
theorem B902591 : Blo 397767 902591 := bstep (se 1 (by rfl) ⟨676943, by rfl⟩ : syracuseStep 902591 = 1353887) B1353887
theorem B601727 : Blo 397767 601727 := bstep (se 1 (by rfl) ⟨451295, by rfl⟩ : syracuseStep 601727 = 902591) B902591
theorem B401151 : Blo 397767 401151 := bstep (se 1 (by rfl) ⟨300863, by rfl⟩ : syracuseStep 401151 = 601727) B601727

theorem C0 (j : ℕ) (h1 : 99441 ≤ j) (h2 : j ≤ 100140) : Blo 397767 (4 * j + 3) := by
  interval_cases j
  · exact B397767
  · exact B397771
  · exact B397775
  · exact B397779
  · exact B397783
  · exact B397787
  · exact B397791
  · exact B397795
  · exact B397799
  · exact B397803
  · exact B397807
  · exact B397811
  · exact B397815
  · exact B397819
  · exact B397823
  · exact B397827
  · exact B397831
  · exact B397835
  · exact B397839
  · exact B397843
  · exact B397847
  · exact B397851
  · exact B397855
  · exact B397859
  · exact B397863
  · exact B397867
  · exact B397871
  · exact B397875
  · exact B397879
  · exact B397883
  · exact B397887
  · exact B397891
  · exact B397895
  · exact B397899
  · exact B397903
  · exact B397907
  · exact B397911
  · exact B397915
  · exact B397919
  · exact B397923
  · exact B397927
  · exact B397931
  · exact B397935
  · exact B397939
  · exact B397943
  · exact B397947
  · exact B397951
  · exact B397955
  · exact B397959
  · exact B397963
  · exact B397967
  · exact B397971
  · exact B397975
  · exact B397979
  · exact B397983
  · exact B397987
  · exact B397991
  · exact B397995
  · exact B397999
  · exact B398003
  · exact B398007
  · exact B398011
  · exact B398015
  · exact B398019
  · exact B398023
  · exact B398027
  · exact B398031
  · exact B398035
  · exact B398039
  · exact B398043
  · exact B398047
  · exact B398051
  · exact B398055
  · exact B398059
  · exact B398063
  · exact B398067
  · exact B398071
  · exact B398075
  · exact B398079
  · exact B398083
  · exact B398087
  · exact B398091
  · exact B398095
  · exact B398099
  · exact B398103
  · exact B398107
  · exact B398111
  · exact B398115
  · exact B398119
  · exact B398123
  · exact B398127
  · exact B398131
  · exact B398135
  · exact B398139
  · exact B398143
  · exact B398147
  · exact B398151
  · exact B398155
  · exact B398159
  · exact B398163
  · exact B398167
  · exact B398171
  · exact B398175
  · exact B398179
  · exact B398183
  · exact B398187
  · exact B398191
  · exact B398195
  · exact B398199
  · exact B398203
  · exact B398207
  · exact B398211
  · exact B398215
  · exact B398219
  · exact B398223
  · exact B398227
  · exact B398231
  · exact B398235
  · exact B398239
  · exact B398243
  · exact B398247
  · exact B398251
  · exact B398255
  · exact B398259
  · exact B398263
  · exact B398267
  · exact B398271
  · exact B398275
  · exact B398279
  · exact B398283
  · exact B398287
  · exact B398291
  · exact B398295
  · exact B398299
  · exact B398303
  · exact B398307
  · exact B398311
  · exact B398315
  · exact B398319
  · exact B398323
  · exact B398327
  · exact B398331
  · exact B398335
  · exact B398339
  · exact B398343
  · exact B398347
  · exact B398351
  · exact B398355
  · exact B398359
  · exact B398363
  · exact B398367
  · exact B398371
  · exact B398375
  · exact B398379
  · exact B398383
  · exact B398387
  · exact B398391
  · exact B398395
  · exact B398399
  · exact B398403
  · exact B398407
  · exact B398411
  · exact B398415
  · exact B398419
  · exact B398423
  · exact B398427
  · exact B398431
  · exact B398435
  · exact B398439
  · exact B398443
  · exact B398447
  · exact B398451
  · exact B398455
  · exact B398459
  · exact B398463
  · exact B398467
  · exact B398471
  · exact B398475
  · exact B398479
  · exact B398483
  · exact B398487
  · exact B398491
  · exact B398495
  · exact B398499
  · exact B398503
  · exact B398507
  · exact B398511
  · exact B398515
  · exact B398519
  · exact B398523
  · exact B398527
  · exact B398531
  · exact B398535
  · exact B398539
  · exact B398543
  · exact B398547
  · exact B398551
  · exact B398555
  · exact B398559
  · exact B398563
  · exact B398567
  · exact B398571
  · exact B398575
  · exact B398579
  · exact B398583
  · exact B398587
  · exact B398591
  · exact B398595
  · exact B398599
  · exact B398603
  · exact B398607
  · exact B398611
  · exact B398615
  · exact B398619
  · exact B398623
  · exact B398627
  · exact B398631
  · exact B398635
  · exact B398639
  · exact B398643
  · exact B398647
  · exact B398651
  · exact B398655
  · exact B398659
  · exact B398663
  · exact B398667
  · exact B398671
  · exact B398675
  · exact B398679
  · exact B398683
  · exact B398687
  · exact B398691
  · exact B398695
  · exact B398699
  · exact B398703
  · exact B398707
  · exact B398711
  · exact B398715
  · exact B398719
  · exact B398723
  · exact B398727
  · exact B398731
  · exact B398735
  · exact B398739
  · exact B398743
  · exact B398747
  · exact B398751
  · exact B398755
  · exact B398759
  · exact B398763
  · exact B398767
  · exact B398771
  · exact B398775
  · exact B398779
  · exact B398783
  · exact B398787
  · exact B398791
  · exact B398795
  · exact B398799
  · exact B398803
  · exact B398807
  · exact B398811
  · exact B398815
  · exact B398819
  · exact B398823
  · exact B398827
  · exact B398831
  · exact B398835
  · exact B398839
  · exact B398843
  · exact B398847
  · exact B398851
  · exact B398855
  · exact B398859
  · exact B398863
  · exact B398867
  · exact B398871
  · exact B398875
  · exact B398879
  · exact B398883
  · exact B398887
  · exact B398891
  · exact B398895
  · exact B398899
  · exact B398903
  · exact B398907
  · exact B398911
  · exact B398915
  · exact B398919
  · exact B398923
  · exact B398927
  · exact B398931
  · exact B398935
  · exact B398939
  · exact B398943
  · exact B398947
  · exact B398951
  · exact B398955
  · exact B398959
  · exact B398963
  · exact B398967
  · exact B398971
  · exact B398975
  · exact B398979
  · exact B398983
  · exact B398987
  · exact B398991
  · exact B398995
  · exact B398999
  · exact B399003
  · exact B399007
  · exact B399011
  · exact B399015
  · exact B399019
  · exact B399023
  · exact B399027
  · exact B399031
  · exact B399035
  · exact B399039
  · exact B399043
  · exact B399047
  · exact B399051
  · exact B399055
  · exact B399059
  · exact B399063
  · exact B399067
  · exact B399071
  · exact B399075
  · exact B399079
  · exact B399083
  · exact B399087
  · exact B399091
  · exact B399095
  · exact B399099
  · exact B399103
  · exact B399107
  · exact B399111
  · exact B399115
  · exact B399119
  · exact B399123
  · exact B399127
  · exact B399131
  · exact B399135
  · exact B399139
  · exact B399143
  · exact B399147
  · exact B399151
  · exact B399155
  · exact B399159
  · exact B399163
  · exact B399167
  · exact B399171
  · exact B399175
  · exact B399179
  · exact B399183
  · exact B399187
  · exact B399191
  · exact B399195
  · exact B399199
  · exact B399203
  · exact B399207
  · exact B399211
  · exact B399215
  · exact B399219
  · exact B399223
  · exact B399227
  · exact B399231
  · exact B399235
  · exact B399239
  · exact B399243
  · exact B399247
  · exact B399251
  · exact B399255
  · exact B399259
  · exact B399263
  · exact B399267
  · exact B399271
  · exact B399275
  · exact B399279
  · exact B399283
  · exact B399287
  · exact B399291
  · exact B399295
  · exact B399299
  · exact B399303
  · exact B399307
  · exact B399311
  · exact B399315
  · exact B399319
  · exact B399323
  · exact B399327
  · exact B399331
  · exact B399335
  · exact B399339
  · exact B399343
  · exact B399347
  · exact B399351
  · exact B399355
  · exact B399359
  · exact B399363
  · exact B399367
  · exact B399371
  · exact B399375
  · exact B399379
  · exact B399383
  · exact B399387
  · exact B399391
  · exact B399395
  · exact B399399
  · exact B399403
  · exact B399407
  · exact B399411
  · exact B399415
  · exact B399419
  · exact B399423
  · exact B399427
  · exact B399431
  · exact B399435
  · exact B399439
  · exact B399443
  · exact B399447
  · exact B399451
  · exact B399455
  · exact B399459
  · exact B399463
  · exact B399467
  · exact B399471
  · exact B399475
  · exact B399479
  · exact B399483
  · exact B399487
  · exact B399491
  · exact B399495
  · exact B399499
  · exact B399503
  · exact B399507
  · exact B399511
  · exact B399515
  · exact B399519
  · exact B399523
  · exact B399527
  · exact B399531
  · exact B399535
  · exact B399539
  · exact B399543
  · exact B399547
  · exact B399551
  · exact B399555
  · exact B399559
  · exact B399563
  · exact B399567
  · exact B399571
  · exact B399575
  · exact B399579
  · exact B399583
  · exact B399587
  · exact B399591
  · exact B399595
  · exact B399599
  · exact B399603
  · exact B399607
  · exact B399611
  · exact B399615
  · exact B399619
  · exact B399623
  · exact B399627
  · exact B399631
  · exact B399635
  · exact B399639
  · exact B399643
  · exact B399647
  · exact B399651
  · exact B399655
  · exact B399659
  · exact B399663
  · exact B399667
  · exact B399671
  · exact B399675
  · exact B399679
  · exact B399683
  · exact B399687
  · exact B399691
  · exact B399695
  · exact B399699
  · exact B399703
  · exact B399707
  · exact B399711
  · exact B399715
  · exact B399719
  · exact B399723
  · exact B399727
  · exact B399731
  · exact B399735
  · exact B399739
  · exact B399743
  · exact B399747
  · exact B399751
  · exact B399755
  · exact B399759
  · exact B399763
  · exact B399767
  · exact B399771
  · exact B399775
  · exact B399779
  · exact B399783
  · exact B399787
  · exact B399791
  · exact B399795
  · exact B399799
  · exact B399803
  · exact B399807
  · exact B399811
  · exact B399815
  · exact B399819
  · exact B399823
  · exact B399827
  · exact B399831
  · exact B399835
  · exact B399839
  · exact B399843
  · exact B399847
  · exact B399851
  · exact B399855
  · exact B399859
  · exact B399863
  · exact B399867
  · exact B399871
  · exact B399875
  · exact B399879
  · exact B399883
  · exact B399887
  · exact B399891
  · exact B399895
  · exact B399899
  · exact B399903
  · exact B399907
  · exact B399911
  · exact B399915
  · exact B399919
  · exact B399923
  · exact B399927
  · exact B399931
  · exact B399935
  · exact B399939
  · exact B399943
  · exact B399947
  · exact B399951
  · exact B399955
  · exact B399959
  · exact B399963
  · exact B399967
  · exact B399971
  · exact B399975
  · exact B399979
  · exact B399983
  · exact B399987
  · exact B399991
  · exact B399995
  · exact B399999
  · exact B400003
  · exact B400007
  · exact B400011
  · exact B400015
  · exact B400019
  · exact B400023
  · exact B400027
  · exact B400031
  · exact B400035
  · exact B400039
  · exact B400043
  · exact B400047
  · exact B400051
  · exact B400055
  · exact B400059
  · exact B400063
  · exact B400067
  · exact B400071
  · exact B400075
  · exact B400079
  · exact B400083
  · exact B400087
  · exact B400091
  · exact B400095
  · exact B400099
  · exact B400103
  · exact B400107
  · exact B400111
  · exact B400115
  · exact B400119
  · exact B400123
  · exact B400127
  · exact B400131
  · exact B400135
  · exact B400139
  · exact B400143
  · exact B400147
  · exact B400151
  · exact B400155
  · exact B400159
  · exact B400163
  · exact B400167
  · exact B400171
  · exact B400175
  · exact B400179
  · exact B400183
  · exact B400187
  · exact B400191
  · exact B400195
  · exact B400199
  · exact B400203
  · exact B400207
  · exact B400211
  · exact B400215
  · exact B400219
  · exact B400223
  · exact B400227
  · exact B400231
  · exact B400235
  · exact B400239
  · exact B400243
  · exact B400247
  · exact B400251
  · exact B400255
  · exact B400259
  · exact B400263
  · exact B400267
  · exact B400271
  · exact B400275
  · exact B400279
  · exact B400283
  · exact B400287
  · exact B400291
  · exact B400295
  · exact B400299
  · exact B400303
  · exact B400307
  · exact B400311
  · exact B400315
  · exact B400319
  · exact B400323
  · exact B400327
  · exact B400331
  · exact B400335
  · exact B400339
  · exact B400343
  · exact B400347
  · exact B400351
  · exact B400355
  · exact B400359
  · exact B400363
  · exact B400367
  · exact B400371
  · exact B400375
  · exact B400379
  · exact B400383
  · exact B400387
  · exact B400391
  · exact B400395
  · exact B400399
  · exact B400403
  · exact B400407
  · exact B400411
  · exact B400415
  · exact B400419
  · exact B400423
  · exact B400427
  · exact B400431
  · exact B400435
  · exact B400439
  · exact B400443
  · exact B400447
  · exact B400451
  · exact B400455
  · exact B400459
  · exact B400463
  · exact B400467
  · exact B400471
  · exact B400475
  · exact B400479
  · exact B400483
  · exact B400487
  · exact B400491
  · exact B400495
  · exact B400499
  · exact B400503
  · exact B400507
  · exact B400511
  · exact B400515
  · exact B400519
  · exact B400523
  · exact B400527
  · exact B400531
  · exact B400535
  · exact B400539
  · exact B400543
  · exact B400547
  · exact B400551
  · exact B400555
  · exact B400559
  · exact B400563

theorem C1 (j : ℕ) (h1 : 100141 ≤ j) (h2 : j ≤ 100441) : Blo 397767 (4 * j + 3) := by
  interval_cases j
  · exact B400567
  · exact B400571
  · exact B400575
  · exact B400579
  · exact B400583
  · exact B400587
  · exact B400591
  · exact B400595
  · exact B400599
  · exact B400603
  · exact B400607
  · exact B400611
  · exact B400615
  · exact B400619
  · exact B400623
  · exact B400627
  · exact B400631
  · exact B400635
  · exact B400639
  · exact B400643
  · exact B400647
  · exact B400651
  · exact B400655
  · exact B400659
  · exact B400663
  · exact B400667
  · exact B400671
  · exact B400675
  · exact B400679
  · exact B400683
  · exact B400687
  · exact B400691
  · exact B400695
  · exact B400699
  · exact B400703
  · exact B400707
  · exact B400711
  · exact B400715
  · exact B400719
  · exact B400723
  · exact B400727
  · exact B400731
  · exact B400735
  · exact B400739
  · exact B400743
  · exact B400747
  · exact B400751
  · exact B400755
  · exact B400759
  · exact B400763
  · exact B400767
  · exact B400771
  · exact B400775
  · exact B400779
  · exact B400783
  · exact B400787
  · exact B400791
  · exact B400795
  · exact B400799
  · exact B400803
  · exact B400807
  · exact B400811
  · exact B400815
  · exact B400819
  · exact B400823
  · exact B400827
  · exact B400831
  · exact B400835
  · exact B400839
  · exact B400843
  · exact B400847
  · exact B400851
  · exact B400855
  · exact B400859
  · exact B400863
  · exact B400867
  · exact B400871
  · exact B400875
  · exact B400879
  · exact B400883
  · exact B400887
  · exact B400891
  · exact B400895
  · exact B400899
  · exact B400903
  · exact B400907
  · exact B400911
  · exact B400915
  · exact B400919
  · exact B400923
  · exact B400927
  · exact B400931
  · exact B400935
  · exact B400939
  · exact B400943
  · exact B400947
  · exact B400951
  · exact B400955
  · exact B400959
  · exact B400963
  · exact B400967
  · exact B400971
  · exact B400975
  · exact B400979
  · exact B400983
  · exact B400987
  · exact B400991
  · exact B400995
  · exact B400999
  · exact B401003
  · exact B401007
  · exact B401011
  · exact B401015
  · exact B401019
  · exact B401023
  · exact B401027
  · exact B401031
  · exact B401035
  · exact B401039
  · exact B401043
  · exact B401047
  · exact B401051
  · exact B401055
  · exact B401059
  · exact B401063
  · exact B401067
  · exact B401071
  · exact B401075
  · exact B401079
  · exact B401083
  · exact B401087
  · exact B401091
  · exact B401095
  · exact B401099
  · exact B401103
  · exact B401107
  · exact B401111
  · exact B401115
  · exact B401119
  · exact B401123
  · exact B401127
  · exact B401131
  · exact B401135
  · exact B401139
  · exact B401143
  · exact B401147
  · exact B401151
  · exact B401155
  · exact B401159
  · exact B401163
  · exact B401167
  · exact B401171
  · exact B401175
  · exact B401179
  · exact B401183
  · exact B401187
  · exact B401191
  · exact B401195
  · exact B401199
  · exact B401203
  · exact B401207
  · exact B401211
  · exact B401215
  · exact B401219
  · exact B401223
  · exact B401227
  · exact B401231
  · exact B401235
  · exact B401239
  · exact B401243
  · exact B401247
  · exact B401251
  · exact B401255
  · exact B401259
  · exact B401263
  · exact B401267
  · exact B401271
  · exact B401275
  · exact B401279
  · exact B401283
  · exact B401287
  · exact B401291
  · exact B401295
  · exact B401299
  · exact B401303
  · exact B401307
  · exact B401311
  · exact B401315
  · exact B401319
  · exact B401323
  · exact B401327
  · exact B401331
  · exact B401335
  · exact B401339
  · exact B401343
  · exact B401347
  · exact B401351
  · exact B401355
  · exact B401359
  · exact B401363
  · exact B401367
  · exact B401371
  · exact B401375
  · exact B401379
  · exact B401383
  · exact B401387
  · exact B401391
  · exact B401395
  · exact B401399
  · exact B401403
  · exact B401407
  · exact B401411
  · exact B401415
  · exact B401419
  · exact B401423
  · exact B401427
  · exact B401431
  · exact B401435
  · exact B401439
  · exact B401443
  · exact B401447
  · exact B401451
  · exact B401455
  · exact B401459
  · exact B401463
  · exact B401467
  · exact B401471
  · exact B401475
  · exact B401479
  · exact B401483
  · exact B401487
  · exact B401491
  · exact B401495
  · exact B401499
  · exact B401503
  · exact B401507
  · exact B401511
  · exact B401515
  · exact B401519
  · exact B401523
  · exact B401527
  · exact B401531
  · exact B401535
  · exact B401539
  · exact B401543
  · exact B401547
  · exact B401551
  · exact B401555
  · exact B401559
  · exact B401563
  · exact B401567
  · exact B401571
  · exact B401575
  · exact B401579
  · exact B401583
  · exact B401587
  · exact B401591
  · exact B401595
  · exact B401599
  · exact B401603
  · exact B401607
  · exact B401611
  · exact B401615
  · exact B401619
  · exact B401623
  · exact B401627
  · exact B401631
  · exact B401635
  · exact B401639
  · exact B401643
  · exact B401647
  · exact B401651
  · exact B401655
  · exact B401659
  · exact B401663
  · exact B401667
  · exact B401671
  · exact B401675
  · exact B401679
  · exact B401683
  · exact B401687
  · exact B401691
  · exact B401695
  · exact B401699
  · exact B401703
  · exact B401707
  · exact B401711
  · exact B401715
  · exact B401719
  · exact B401723
  · exact B401727
  · exact B401731
  · exact B401735
  · exact B401739
  · exact B401743
  · exact B401747
  · exact B401751
  · exact B401755
  · exact B401759
  · exact B401763
  · exact B401767

theorem solution (m : ℕ) (hlo : 397767 ≤ m) (hhi : m ≤ 401767) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 99441 ≤ j := by omega
    have hj2 : j ≤ 100441 := by omega
    have hb : Blo 397767 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 100141 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
