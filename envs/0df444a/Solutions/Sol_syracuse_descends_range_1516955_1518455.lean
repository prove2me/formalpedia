-- Prove2me | solution 1 for syracuse_descends_range_1516955_1518455
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:18.546807+00:00
-- url     : https://prove2.me/submissions/f33ffe52-d17a-4ebc-a549-dc10310979f3

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


theorem B2277389 : Blo 1516955 2277389 := bbase (se 3 (by rfl) ⟨427010, by rfl⟩ : syracuseStep 2277389 = 854021) (by norm_num)
theorem B3694621 : Blo 1516955 3694621 := bbase (se 3 (by rfl) ⟨692741, by rfl⟩ : syracuseStep 3694621 = 1385483) (by norm_num)
theorem B3416093 : Blo 1516955 3416093 := bbase (se 3 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 3416093 = 1281035) (by norm_num)
theorem B2277413 : Blo 1516955 2277413 := bbase (se 4 (by rfl) ⟨213507, by rfl⟩ : syracuseStep 2277413 = 427015) (by norm_num)
theorem B3842093 : Blo 1516955 3842093 := bbase (se 3 (by rfl) ⟨720392, by rfl⟩ : syracuseStep 3842093 = 1440785) (by norm_num)
theorem B2277437 : Blo 1516955 2277437 := bbase (se 3 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 2277437 = 854039) (by norm_num)
theorem B2277461 : Blo 1516955 2277461 := bbase (se 8 (by rfl) ⟨13344, by rfl⟩ : syracuseStep 2277461 = 26689) (by norm_num)
theorem B3416165 : Blo 1516955 3416165 := bbase (se 4 (by rfl) ⟨320265, by rfl⟩ : syracuseStep 3416165 = 640531) (by norm_num)
theorem B2277485 : Blo 1516955 2277485 := bbase (se 3 (by rfl) ⟨427028, by rfl⟩ : syracuseStep 2277485 = 854057) (by norm_num)
theorem B5120117 : Blo 1516955 5120117 := bbase (se 5 (by rfl) ⟨240005, by rfl⟩ : syracuseStep 5120117 = 480011) (by norm_num)
theorem B2277509 : Blo 1516955 2277509 := bbase (se 4 (by rfl) ⟨213516, by rfl⟩ : syracuseStep 2277509 = 427033) (by norm_num)
theorem B2277533 : Blo 1516955 2277533 := bbase (se 3 (by rfl) ⟨427037, by rfl⟩ : syracuseStep 2277533 = 854075) (by norm_num)
theorem B3416237 : Blo 1516955 3416237 := bbase (se 3 (by rfl) ⟨640544, by rfl⟩ : syracuseStep 3416237 = 1281089) (by norm_num)
theorem B2277557 : Blo 1516955 2277557 := bbase (se 5 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 2277557 = 213521) (by norm_num)
theorem B2597069 : Blo 1516955 2597069 := bbase (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) (by norm_num)
theorem B2277581 : Blo 1516955 2277581 := bbase (se 3 (by rfl) ⟨427046, by rfl⟩ : syracuseStep 2277581 = 854093) (by norm_num)
theorem B7291093 : Blo 1516955 7291093 := bbase (se 7 (by rfl) ⟨85442, by rfl⟩ : syracuseStep 7291093 = 170885) (by norm_num)
theorem B2277605 : Blo 1516955 2277605 := bbase (se 4 (by rfl) ⟨213525, by rfl⟩ : syracuseStep 2277605 = 427051) (by norm_num)
theorem B3416309 : Blo 1516955 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B2277629 : Blo 1516955 2277629 := bbase (se 3 (by rfl) ⟨427055, by rfl⟩ : syracuseStep 2277629 = 854111) (by norm_num)
theorem B2277653 : Blo 1516955 2277653 := bbase (se 6 (by rfl) ⟨53382, by rfl⟩ : syracuseStep 2277653 = 106765) (by norm_num)
theorem B2277677 : Blo 1516955 2277677 := bbase (se 3 (by rfl) ⟨427064, by rfl⟩ : syracuseStep 2277677 = 854129) (by norm_num)
theorem B3416381 : Blo 1516955 3416381 := bbase (se 3 (by rfl) ⟨640571, by rfl⟩ : syracuseStep 3416381 = 1281143) (by norm_num)
theorem B8642933 : Blo 1516955 8642933 := bbase (se 5 (by rfl) ⟨405137, by rfl⟩ : syracuseStep 8642933 = 810275) (by norm_num)
theorem B7684469 : Blo 1516955 7684469 := bbase (se 5 (by rfl) ⟨360209, by rfl⟩ : syracuseStep 7684469 = 720419) (by norm_num)
theorem B3842437 : Blo 1516955 3842437 := bbase (se 4 (by rfl) ⟨360228, by rfl⟩ : syracuseStep 3842437 = 720457) (by norm_num)
theorem B3416453 : Blo 1516955 3416453 := bbase (se 4 (by rfl) ⟨320292, by rfl⟩ : syracuseStep 3416453 = 640585) (by norm_num)
theorem B3416525 : Blo 1516955 3416525 := bbase (se 3 (by rfl) ⟨640598, by rfl⟩ : syracuseStep 3416525 = 1281197) (by norm_num)
theorem B3842549 : Blo 1516955 3842549 := bbase (se 5 (by rfl) ⟨180119, by rfl⟩ : syracuseStep 3842549 = 360239) (by norm_num)
theorem B5120549 : Blo 1516955 5120549 := bbase (se 4 (by rfl) ⟨480051, by rfl⟩ : syracuseStep 5120549 = 960103) (by norm_num)
theorem B3842741 : Blo 1516955 3842741 := bbase (se 5 (by rfl) ⟨180128, by rfl⟩ : syracuseStep 3842741 = 360257) (by norm_num)
theorem B5120981 : Blo 1516955 5120981 := bbase (se 7 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 5120981 = 120023) (by norm_num)
theorem B6480901 : Blo 1516955 6480901 := bbase (se 4 (by rfl) ⟨607584, by rfl⟩ : syracuseStep 6480901 = 1215169) (by norm_num)
theorem B3843085 : Blo 1516955 3843085 := bbase (se 3 (by rfl) ⟨720578, by rfl⟩ : syracuseStep 3843085 = 1441157) (by norm_num)
theorem B3843197 : Blo 1516955 3843197 := bbase (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) (by norm_num)
theorem B3843389 : Blo 1516955 3843389 := bbase (se 3 (by rfl) ⟨720635, by rfl⟩ : syracuseStep 3843389 = 1441271) (by norm_num)
theorem B2630989 : Blo 1516955 2630989 := bbase (se 3 (by rfl) ⟨493310, by rfl⟩ : syracuseStep 2630989 = 986621) (by norm_num)
theorem B5121413 : Blo 1516955 5121413 := bbase (se 4 (by rfl) ⟨480132, by rfl⟩ : syracuseStep 5121413 = 960265) (by norm_num)
theorem B8644117 : Blo 1516955 8644117 := bbase (se 6 (by rfl) ⟨202596, by rfl⟩ : syracuseStep 8644117 = 405193) (by norm_num)
theorem B3647045 : Blo 1516955 3647045 := bbase (se 4 (by rfl) ⟨341910, by rfl⟩ : syracuseStep 3647045 = 683821) (by norm_num)
theorem B26297941 : Blo 1516955 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B7685765 : Blo 1516955 7685765 := bbase (se 4 (by rfl) ⟨720540, by rfl⟩ : syracuseStep 7685765 = 1441081) (by norm_num)
theorem B5121845 : Blo 1516955 5121845 := bbase (se 5 (by rfl) ⟨240086, by rfl⟩ : syracuseStep 5121845 = 480173) (by norm_num)
theorem B4859909 : Blo 1516955 4859909 := bbase (se 4 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 4859909 = 911233) (by norm_num)
theorem B1730641 : Blo 1516955 1730641 := bbase (se 2 (by rfl) ⟨648990, by rfl⟩ : syracuseStep 1730641 = 1297981) (by norm_num)
theorem B11528405 : Blo 1516955 11528405 := bbase (se 7 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 11528405 = 270197) (by norm_num)
theorem B5122277 : Blo 1516955 5122277 := bbase (se 4 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 5122277 = 960427) (by norm_num)
theorem B6482389 : Blo 1516955 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B6482405 : Blo 1516955 6482405 := bbase (se 4 (by rfl) ⟨607725, by rfl⟩ : syracuseStep 6482405 = 1215451) (by norm_num)
theorem B20761109 : Blo 1516955 20761109 := bbase (se 6 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 20761109 = 973177) (by norm_num)
theorem B2189845 : Blo 1516955 2189845 := bbase (se 6 (by rfl) ⟨51324, by rfl⟩ : syracuseStep 2189845 = 102649) (by norm_num)
theorem B1706593 : Blo 1516955 1706593 := bbase (se 2 (by rfl) ⟨639972, by rfl⟩ : syracuseStep 1706593 = 1279945) (by norm_num)
theorem B5761637 : Blo 1516955 5761637 := bbase (se 4 (by rfl) ⟨540153, by rfl⟩ : syracuseStep 5761637 = 1080307) (by norm_num)
theorem B11520629 : Blo 1516955 11520629 := bbase (se 5 (by rfl) ⟨540029, by rfl⟩ : syracuseStep 11520629 = 1080059) (by norm_num)
theorem B9726581 : Blo 1516955 9726581 := bbase (se 5 (by rfl) ⟨455933, by rfl⟩ : syracuseStep 9726581 = 911867) (by norm_num)
theorem B1706629 : Blo 1516955 1706629 := bbase (se 4 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 1706629 = 319993) (by norm_num)
theorem B5122709 : Blo 1516955 5122709 := bbase (se 6 (by rfl) ⟨120063, by rfl⟩ : syracuseStep 5122709 = 240127) (by norm_num)
theorem B1706665 : Blo 1516955 1706665 := bbase (se 2 (by rfl) ⟨639999, by rfl⟩ : syracuseStep 1706665 = 1279999) (by norm_num)
theorem B1706701 : Blo 1516955 1706701 := bbase (se 3 (by rfl) ⟨320006, by rfl⟩ : syracuseStep 1706701 = 640013) (by norm_num)
theorem B1706737 : Blo 1516955 1706737 := bbase (se 2 (by rfl) ⟨640026, by rfl⟩ : syracuseStep 1706737 = 1280053) (by norm_num)
theorem B14592757 : Blo 1516955 14592757 := bbase (se 5 (by rfl) ⟨684035, by rfl⟩ : syracuseStep 14592757 = 1368071) (by norm_num)
theorem B1706773 : Blo 1516955 1706773 := bbase (se 6 (by rfl) ⟨40002, by rfl⟩ : syracuseStep 1706773 = 80005) (by norm_num)
theorem B1706809 : Blo 1516955 1706809 := bbase (se 2 (by rfl) ⟨640053, by rfl⟩ : syracuseStep 1706809 = 1280107) (by norm_num)
theorem B1706845 : Blo 1516955 1706845 := bbase (se 3 (by rfl) ⟨320033, by rfl⟩ : syracuseStep 1706845 = 640067) (by norm_num)
theorem B1706881 : Blo 1516955 1706881 := bbase (se 2 (by rfl) ⟨640080, by rfl⟩ : syracuseStep 1706881 = 1280161) (by norm_num)
theorem B4860805 : Blo 1516955 4860805 := bbase (se 4 (by rfl) ⟨455700, by rfl⟩ : syracuseStep 4860805 = 911401) (by norm_num)
theorem B5761925 : Blo 1516955 5761925 := bbase (se 4 (by rfl) ⟨540180, by rfl⟩ : syracuseStep 5761925 = 1080361) (by norm_num)
theorem B7687061 : Blo 1516955 7687061 := bbase (se 6 (by rfl) ⟨180165, by rfl⟩ : syracuseStep 7687061 = 360331) (by norm_num)
theorem B2960285 : Blo 1516955 2960285 := bbase (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) (by norm_num)
theorem B1706917 : Blo 1516955 1706917 := bbase (se 4 (by rfl) ⟨160023, by rfl⟩ : syracuseStep 1706917 = 320047) (by norm_num)
theorem B1706953 : Blo 1516955 1706953 := bbase (se 2 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 1706953 = 1280215) (by norm_num)
theorem B1919953 : Blo 1516955 1919953 := bbase (se 2 (by rfl) ⟨719982, by rfl⟩ : syracuseStep 1919953 = 1439965) (by norm_num)
theorem B1706989 : Blo 1516955 1706989 := bbase (se 3 (by rfl) ⟨320060, by rfl⟩ : syracuseStep 1706989 = 640121) (by norm_num)
theorem B9358325 : Blo 1516955 9358325 := bbase (se 5 (by rfl) ⟨438671, by rfl⟩ : syracuseStep 9358325 = 877343) (by norm_num)
theorem B1707025 : Blo 1516955 1707025 := bbase (se 2 (by rfl) ⟨640134, by rfl⟩ : syracuseStep 1707025 = 1280269) (by norm_num)
theorem B6925333 : Blo 1516955 6925333 := bbase (se 6 (by rfl) ⟨162312, by rfl⟩ : syracuseStep 6925333 = 324625) (by norm_num)
theorem B1707061 : Blo 1516955 1707061 := bbase (se 5 (by rfl) ⟨80018, by rfl⟩ : syracuseStep 1707061 = 160037) (by norm_num)
theorem B5123141 : Blo 1516955 5123141 := bbase (se 4 (by rfl) ⟨480294, by rfl⟩ : syracuseStep 5123141 = 960589) (by norm_num)
theorem B1707097 : Blo 1516955 1707097 := bbase (se 2 (by rfl) ⟨640161, by rfl⟩ : syracuseStep 1707097 = 1280323) (by norm_num)
theorem B4320373 : Blo 1516955 4320373 := bbase (se 5 (by rfl) ⟨202517, by rfl⟩ : syracuseStep 4320373 = 405035) (by norm_num)
theorem B1920125 : Blo 1516955 1920125 := bbase (se 3 (by rfl) ⟨360023, by rfl⟩ : syracuseStep 1920125 = 720047) (by norm_num)
theorem B1707133 : Blo 1516955 1707133 := bbase (se 3 (by rfl) ⟨320087, by rfl⟩ : syracuseStep 1707133 = 640175) (by norm_num)
theorem B1707169 : Blo 1516955 1707169 := bbase (se 2 (by rfl) ⟨640188, by rfl⟩ : syracuseStep 1707169 = 1280377) (by norm_num)
theorem B1920181 : Blo 1516955 1920181 := bbase (se 5 (by rfl) ⟨90008, by rfl⟩ : syracuseStep 1920181 = 180017) (by norm_num)
theorem B1707205 : Blo 1516955 1707205 := bbase (se 4 (by rfl) ⟨160050, by rfl⟩ : syracuseStep 1707205 = 320101) (by norm_num)
theorem B1707241 : Blo 1516955 1707241 := bbase (se 2 (by rfl) ⟨640215, by rfl⟩ : syracuseStep 1707241 = 1280431) (by norm_num)
theorem B10939637 : Blo 1516955 10939637 := bbase (se 5 (by rfl) ⟨512795, by rfl⟩ : syracuseStep 10939637 = 1025591) (by norm_num)
theorem B1707277 : Blo 1516955 1707277 := bbase (se 3 (by rfl) ⟨320114, by rfl⟩ : syracuseStep 1707277 = 640229) (by norm_num)
theorem B4320533 : Blo 1516955 4320533 := bbase (se 6 (by rfl) ⟨101262, by rfl⟩ : syracuseStep 4320533 = 202525) (by norm_num)
theorem B1920277 : Blo 1516955 1920277 := bbase (se 6 (by rfl) ⟨45006, by rfl⟩ : syracuseStep 1920277 = 90013) (by norm_num)
theorem B1707313 : Blo 1516955 1707313 := bbase (se 2 (by rfl) ⟨640242, by rfl⟩ : syracuseStep 1707313 = 1280485) (by norm_num)
theorem B1707349 : Blo 1516955 1707349 := bbase (se 11 (by rfl) ⟨1250, by rfl⟩ : syracuseStep 1707349 = 2501) (by norm_num)
theorem B1707385 : Blo 1516955 1707385 := bbase (se 2 (by rfl) ⟨640269, by rfl⟩ : syracuseStep 1707385 = 1280539) (by norm_num)
theorem B1707421 : Blo 1516955 1707421 := bbase (se 3 (by rfl) ⟨320141, by rfl⟩ : syracuseStep 1707421 = 640283) (by norm_num)
theorem B6925733 : Blo 1516955 6925733 := bbase (se 4 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 6925733 = 1298575) (by norm_num)
theorem B1920449 : Blo 1516955 1920449 := bbase (se 2 (by rfl) ⟨720168, by rfl⟩ : syracuseStep 1920449 = 1440337) (by norm_num)
theorem B1707457 : Blo 1516955 1707457 := bbase (se 2 (by rfl) ⟨640296, by rfl⟩ : syracuseStep 1707457 = 1280593) (by norm_num)
theorem B8646101 : Blo 1516955 8646101 := bbase (se 7 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 8646101 = 202643) (by norm_num)
theorem B1707493 : Blo 1516955 1707493 := bbase (se 4 (by rfl) ⟨160077, by rfl⟩ : syracuseStep 1707493 = 320155) (by norm_num)
theorem B5123573 : Blo 1516955 5123573 := bbase (se 5 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 5123573 = 480335) (by norm_num)
theorem B1920505 : Blo 1516955 1920505 := bbase (se 2 (by rfl) ⟨720189, by rfl⟩ : syracuseStep 1920505 = 1440379) (by norm_num)
theorem B4320773 : Blo 1516955 4320773 := bbase (se 4 (by rfl) ⟨405072, by rfl⟩ : syracuseStep 4320773 = 810145) (by norm_num)
theorem B1707529 : Blo 1516955 1707529 := bbase (se 2 (by rfl) ⟨640323, by rfl⟩ : syracuseStep 1707529 = 1280647) (by norm_num)
theorem B1707565 : Blo 1516955 1707565 := bbase (se 3 (by rfl) ⟨320168, by rfl⟩ : syracuseStep 1707565 = 640337) (by norm_num)
theorem B1707601 : Blo 1516955 1707601 := bbase (se 2 (by rfl) ⟨640350, by rfl⟩ : syracuseStep 1707601 = 1280701) (by norm_num)
theorem B1920601 : Blo 1516955 1920601 := bbase (se 2 (by rfl) ⟨720225, by rfl⟩ : syracuseStep 1920601 = 1440451) (by norm_num)
theorem B1707637 : Blo 1516955 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1707673 : Blo 1516955 1707673 := bbase (se 2 (by rfl) ⟨640377, by rfl⟩ : syracuseStep 1707673 = 1280755) (by norm_num)
theorem B1707709 : Blo 1516955 1707709 := bbase (se 3 (by rfl) ⟨320195, by rfl⟩ : syracuseStep 1707709 = 640391) (by norm_num)
theorem B4320965 : Blo 1516955 4320965 := bbase (se 4 (by rfl) ⟨405090, by rfl⟩ : syracuseStep 4320965 = 810181) (by norm_num)
theorem B2920133 : Blo 1516955 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B1707745 : Blo 1516955 1707745 := bbase (se 2 (by rfl) ⟨640404, by rfl⟩ : syracuseStep 1707745 = 1280809) (by norm_num)
theorem B1920773 : Blo 1516955 1920773 := bbase (se 4 (by rfl) ⟨180072, by rfl⟩ : syracuseStep 1920773 = 360145) (by norm_num)
theorem B1707781 : Blo 1516955 1707781 := bbase (se 4 (by rfl) ⟨160104, by rfl⟩ : syracuseStep 1707781 = 320209) (by norm_num)
theorem B2772773 : Blo 1516955 2772773 := bbase (se 4 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 2772773 = 519895) (by norm_num)
theorem B1707817 : Blo 1516955 1707817 := bbase (se 2 (by rfl) ⟨640431, by rfl⟩ : syracuseStep 1707817 = 1280863) (by norm_num)
theorem B1920829 : Blo 1516955 1920829 := bbase (se 3 (by rfl) ⟨360155, by rfl⟩ : syracuseStep 1920829 = 720311) (by norm_num)
theorem B1707853 : Blo 1516955 1707853 := bbase (se 3 (by rfl) ⟨320222, by rfl⟩ : syracuseStep 1707853 = 640445) (by norm_num)
theorem B1707889 : Blo 1516955 1707889 := bbase (se 2 (by rfl) ⟨640458, by rfl⟩ : syracuseStep 1707889 = 1280917) (by norm_num)
theorem B1707925 : Blo 1516955 1707925 := bbase (se 6 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 1707925 = 80059) (by norm_num)
theorem B1920925 : Blo 1516955 1920925 := bbase (se 3 (by rfl) ⟨360173, by rfl⟩ : syracuseStep 1920925 = 720347) (by norm_num)
theorem B5124005 : Blo 1516955 5124005 := bbase (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) (by norm_num)
theorem B2559917 : Blo 1516955 2559917 := bbase (se 3 (by rfl) ⟨479984, by rfl⟩ : syracuseStep 2559917 = 959969) (by norm_num)
theorem B1707961 : Blo 1516955 1707961 := bbase (se 2 (by rfl) ⟨640485, by rfl⟩ : syracuseStep 1707961 = 1280971) (by norm_num)
theorem B16404437 : Blo 1516955 16404437 := bbase (se 7 (by rfl) ⟨192239, by rfl⟩ : syracuseStep 16404437 = 384479) (by norm_num)
theorem B1707997 : Blo 1516955 1707997 := bbase (se 3 (by rfl) ⟨320249, by rfl⟩ : syracuseStep 1707997 = 640499) (by norm_num)
theorem B1708033 : Blo 1516955 1708033 := bbase (se 2 (by rfl) ⟨640512, by rfl⟩ : syracuseStep 1708033 = 1281025) (by norm_num)
theorem B5763109 : Blo 1516955 5763109 := bbase (se 4 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 5763109 = 1080583) (by norm_num)
theorem B1708069 : Blo 1516955 1708069 := bbase (se 4 (by rfl) ⟨160131, by rfl⟩ : syracuseStep 1708069 = 320263) (by norm_num)
theorem B2560045 : Blo 1516955 2560045 := bbase (se 3 (by rfl) ⟨480008, by rfl⟩ : syracuseStep 2560045 = 960017) (by norm_num)
theorem B2920517 : Blo 1516955 2920517 := bbase (se 4 (by rfl) ⟨273798, by rfl⟩ : syracuseStep 2920517 = 547597) (by norm_num)
theorem B1921097 : Blo 1516955 1921097 := bbase (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) (by norm_num)
theorem B1708105 : Blo 1516955 1708105 := bbase (se 2 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 1708105 = 1281079) (by norm_num)
theorem B3895397 : Blo 1516955 3895397 := bbase (se 4 (by rfl) ⟨365193, by rfl⟩ : syracuseStep 3895397 = 730387) (by norm_num)
theorem B1708141 : Blo 1516955 1708141 := bbase (se 3 (by rfl) ⟨320276, by rfl⟩ : syracuseStep 1708141 = 640553) (by norm_num)
theorem B1921153 : Blo 1516955 1921153 := bbase (se 2 (by rfl) ⟨720432, by rfl⟩ : syracuseStep 1921153 = 1440865) (by norm_num)
theorem B2560133 : Blo 1516955 2560133 := bbase (se 4 (by rfl) ⟨240012, by rfl⟩ : syracuseStep 2560133 = 480025) (by norm_num)
theorem B1708177 : Blo 1516955 1708177 := bbase (se 2 (by rfl) ⟨640566, by rfl⟩ : syracuseStep 1708177 = 1281133) (by norm_num)
theorem B12963989 : Blo 1516955 12963989 := bbase (se 6 (by rfl) ⟨303843, by rfl⟩ : syracuseStep 12963989 = 607687) (by norm_num)
theorem B3240101 : Blo 1516955 3240101 := bbase (se 4 (by rfl) ⟨303759, by rfl⟩ : syracuseStep 3240101 = 607519) (by norm_num)
theorem B3240109 : Blo 1516955 3240109 := bbase (se 3 (by rfl) ⟨607520, by rfl⟩ : syracuseStep 3240109 = 1215041) (by norm_num)
theorem B1708213 : Blo 1516955 1708213 := bbase (se 5 (by rfl) ⟨80072, by rfl⟩ : syracuseStep 1708213 = 160145) (by norm_num)
theorem B1708249 : Blo 1516955 1708249 := bbase (se 2 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 1708249 = 1281187) (by norm_num)
theorem B1921249 : Blo 1516955 1921249 := bbase (se 2 (by rfl) ⟨720468, by rfl⟩ : syracuseStep 1921249 = 1440937) (by norm_num)
theorem B2560261 : Blo 1516955 2560261 := bbase (se 4 (by rfl) ⟨240024, by rfl⟩ : syracuseStep 2560261 = 480049) (by norm_num)
theorem B1823033 : Blo 1516955 1823033 := bbase (se 2 (by rfl) ⟨683637, by rfl⟩ : syracuseStep 1823033 = 1367275) (by norm_num)
theorem B5763413 : Blo 1516955 5763413 := bbase (se 10 (by rfl) ⟨8442, by rfl⟩ : syracuseStep 5763413 = 16885) (by norm_num)
theorem B5124437 : Blo 1516955 5124437 := bbase (se 10 (by rfl) ⟨7506, by rfl⟩ : syracuseStep 5124437 = 15013) (by norm_num)
theorem B2560349 : Blo 1516955 2560349 := bbase (se 3 (by rfl) ⟨480065, by rfl⟩ : syracuseStep 2560349 = 960131) (by norm_num)
theorem B7786853 : Blo 1516955 7786853 := bbase (se 4 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 7786853 = 1460035) (by norm_num)
theorem B2879869 : Blo 1516955 2879869 := bbase (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) (by norm_num)
theorem B3895685 : Blo 1516955 3895685 := bbase (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) (by norm_num)
theorem B1921421 : Blo 1516955 1921421 := bbase (se 3 (by rfl) ⟨360266, by rfl⟩ : syracuseStep 1921421 = 720533) (by norm_num)
theorem B3117469 : Blo 1516955 3117469 := bbase (se 3 (by rfl) ⟨584525, by rfl⟩ : syracuseStep 3117469 = 1169051) (by norm_num)
theorem B2306485 : Blo 1516955 2306485 := bbase (se 5 (by rfl) ⟨108116, by rfl⟩ : syracuseStep 2306485 = 216233) (by norm_num)
theorem B1921477 : Blo 1516955 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B2560477 : Blo 1516955 2560477 := bbase (se 3 (by rfl) ⟨480089, by rfl⟩ : syracuseStep 2560477 = 960179) (by norm_num)
theorem B18469397 : Blo 1516955 18469397 := bbase (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) (by norm_num)
theorem B2880029 : Blo 1516955 2880029 := bbase (se 3 (by rfl) ⟨540005, by rfl⟩ : syracuseStep 2880029 = 1080011) (by norm_num)
theorem B1921573 : Blo 1516955 1921573 := bbase (se 4 (by rfl) ⟨180147, by rfl⟩ : syracuseStep 1921573 = 360295) (by norm_num)
theorem B2560565 : Blo 1516955 2560565 := bbase (se 5 (by rfl) ⟨120026, by rfl⟩ : syracuseStep 2560565 = 240053) (by norm_num)
theorem B7680581 : Blo 1516955 7680581 := bbase (se 4 (by rfl) ⟨720054, by rfl⟩ : syracuseStep 7680581 = 1440109) (by norm_num)
theorem B4321957 : Blo 1516955 4321957 := bbase (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) (by norm_num)
theorem B2880173 : Blo 1516955 2880173 := bbase (se 3 (by rfl) ⟨540032, by rfl⟩ : syracuseStep 2880173 = 1080065) (by norm_num)
theorem B2560693 : Blo 1516955 2560693 := bbase (se 5 (by rfl) ⟨120032, by rfl⟩ : syracuseStep 2560693 = 240065) (by norm_num)
theorem B6484661 : Blo 1516955 6484661 := bbase (se 5 (by rfl) ⟨303968, by rfl⟩ : syracuseStep 6484661 = 607937) (by norm_num)
theorem B1921745 : Blo 1516955 1921745 := bbase (se 2 (by rfl) ⟨720654, by rfl⟩ : syracuseStep 1921745 = 1441309) (by norm_num)
theorem B2560781 : Blo 1516955 2560781 := bbase (se 3 (by rfl) ⟨480146, by rfl⟩ : syracuseStep 2560781 = 960293) (by norm_num)
theorem B3797885 : Blo 1516955 3797885 := bbase (se 3 (by rfl) ⟨712103, by rfl⟩ : syracuseStep 3797885 = 1424207) (by norm_num)
theorem B2560909 : Blo 1516955 2560909 := bbase (se 3 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 2560909 = 960341) (by norm_num)
theorem B7115701 : Blo 1516955 7115701 := bbase (se 5 (by rfl) ⟨333548, by rfl⟩ : syracuseStep 7115701 = 667097) (by norm_num)
theorem B2880461 : Blo 1516955 2880461 := bbase (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) (by norm_num)
theorem B2560997 : Blo 1516955 2560997 := bbase (se 4 (by rfl) ⟨240093, by rfl⟩ : syracuseStep 2560997 = 480187) (by norm_num)
theorem B1823725 : Blo 1516955 1823725 := bbase (se 3 (by rfl) ⟨341948, by rfl⟩ : syracuseStep 1823725 = 683897) (by norm_num)
theorem B1848305 : Blo 1516955 1848305 := bbase (se 2 (by rfl) ⟨693114, by rfl⟩ : syracuseStep 1848305 = 1386229) (by norm_num)
theorem B4617253 : Blo 1516955 4617253 := bbase (se 4 (by rfl) ⟨432867, by rfl⟩ : syracuseStep 4617253 = 865735) (by norm_num)
theorem B2430005 : Blo 1516955 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B2880613 : Blo 1516955 2880613 := bbase (se 4 (by rfl) ⟨270057, by rfl⟩ : syracuseStep 2880613 = 540115) (by norm_num)
theorem B2561125 : Blo 1516955 2561125 := bbase (se 4 (by rfl) ⟨240105, by rfl⟩ : syracuseStep 2561125 = 480211) (by norm_num)
theorem B1873049 : Blo 1516955 1873049 := bbase (se 2 (by rfl) ⟨702393, by rfl⟩ : syracuseStep 1873049 = 1404787) (by norm_num)
theorem B2561213 : Blo 1516955 2561213 := bbase (se 3 (by rfl) ⟨480227, by rfl⟩ : syracuseStep 2561213 = 960455) (by norm_num)
theorem B1823941 : Blo 1516955 1823941 := bbase (se 4 (by rfl) ⟨170994, by rfl⟩ : syracuseStep 1823941 = 341989) (by norm_num)
theorem B3413213 : Blo 1516955 3413213 := bbase (se 3 (by rfl) ⟨639977, by rfl⟩ : syracuseStep 3413213 = 1279955) (by norm_num)
theorem B1946873 : Blo 1516955 1946873 := bbase (se 2 (by rfl) ⟨730077, by rfl⟩ : syracuseStep 1946873 = 1460155) (by norm_num)
theorem B2159885 : Blo 1516955 2159885 := bbase (se 3 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 2159885 = 809957) (by norm_num)
theorem B3241237 : Blo 1516955 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B3413285 : Blo 1516955 3413285 := bbase (se 4 (by rfl) ⟨319995, by rfl⟩ : syracuseStep 3413285 = 639991) (by norm_num)
theorem B2561341 : Blo 1516955 2561341 := bbase (se 3 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 2561341 = 960503) (by norm_num)
theorem B3413357 : Blo 1516955 3413357 := bbase (se 3 (by rfl) ⟨640004, by rfl⟩ : syracuseStep 3413357 = 1280009) (by norm_num)
theorem B2880917 : Blo 1516955 2880917 := bbase (se 6 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 2880917 = 135043) (by norm_num)
theorem B2561429 : Blo 1516955 2561429 := bbase (se 6 (by rfl) ⟨60033, by rfl⟩ : syracuseStep 2561429 = 120067) (by norm_num)
theorem B2463149 : Blo 1516955 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B3413429 : Blo 1516955 3413429 := bbase (se 5 (by rfl) ⟨160004, by rfl⟩ : syracuseStep 3413429 = 320009) (by norm_num)
theorem B3413501 : Blo 1516955 3413501 := bbase (se 3 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 3413501 = 1280063) (by norm_num)
theorem B2561557 : Blo 1516955 2561557 := bbase (se 6 (by rfl) ⟨60036, by rfl⟩ : syracuseStep 2561557 = 120073) (by norm_num)
theorem B3413573 : Blo 1516955 3413573 := bbase (se 4 (by rfl) ⟨320022, by rfl⟩ : syracuseStep 3413573 = 640045) (by norm_num)
theorem B2307653 : Blo 1516955 2307653 := bbase (se 4 (by rfl) ⟨216342, by rfl⟩ : syracuseStep 2307653 = 432685) (by norm_num)
theorem B2430557 : Blo 1516955 2430557 := bbase (se 3 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 2430557 = 911459) (by norm_num)
theorem B2561645 : Blo 1516955 2561645 := bbase (se 3 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 2561645 = 960617) (by norm_num)
theorem B2430589 : Blo 1516955 2430589 := bbase (se 3 (by rfl) ⟨455735, by rfl⟩ : syracuseStep 2430589 = 911471) (by norm_num)
theorem B3413645 : Blo 1516955 3413645 := bbase (se 3 (by rfl) ⟨640058, by rfl⟩ : syracuseStep 3413645 = 1280117) (by norm_num)
theorem B3241613 : Blo 1516955 3241613 := bbase (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) (by norm_num)
theorem B3413717 : Blo 1516955 3413717 := bbase (se 7 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 3413717 = 80009) (by norm_num)
theorem B4863701 : Blo 1516955 4863701 := bbase (se 7 (by rfl) ⟨56996, by rfl⟩ : syracuseStep 4863701 = 113993) (by norm_num)
theorem B2561773 : Blo 1516955 2561773 := bbase (se 3 (by rfl) ⟨480332, by rfl⟩ : syracuseStep 2561773 = 960665) (by norm_num)
theorem B8206069 : Blo 1516955 8206069 := bbase (se 5 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 8206069 = 769319) (by norm_num)
theorem B4323061 : Blo 1516955 4323061 := bbase (se 5 (by rfl) ⟨202643, by rfl⟩ : syracuseStep 4323061 = 405287) (by norm_num)
theorem B3077909 : Blo 1516955 3077909 := bbase (se 6 (by rfl) ⟨72138, by rfl⟩ : syracuseStep 3077909 = 144277) (by norm_num)
theorem B3413789 : Blo 1516955 3413789 := bbase (se 3 (by rfl) ⟨640085, by rfl⟩ : syracuseStep 3413789 = 1280171) (by norm_num)
theorem B2160437 : Blo 1516955 2160437 := bbase (se 5 (by rfl) ⟨101270, by rfl⟩ : syracuseStep 2160437 = 202541) (by norm_num)
theorem B5470021 : Blo 1516955 5470021 := bbase (se 4 (by rfl) ⟨512814, by rfl⟩ : syracuseStep 5470021 = 1025629) (by norm_num)
theorem B2561861 : Blo 1516955 2561861 := bbase (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) (by norm_num)
theorem B7681877 : Blo 1516955 7681877 := bbase (se 9 (by rfl) ⟨22505, by rfl⟩ : syracuseStep 7681877 = 45011) (by norm_num)
theorem B3839845 : Blo 1516955 3839845 := bbase (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) (by norm_num)
theorem B3413861 : Blo 1516955 3413861 := bbase (se 4 (by rfl) ⟨320049, by rfl⟩ : syracuseStep 3413861 = 640099) (by norm_num)
theorem B1947493 : Blo 1516955 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B1537913 : Blo 1516955 1537913 := bbase (se 2 (by rfl) ⟨576717, by rfl⟩ : syracuseStep 1537913 = 1153435) (by norm_num)
theorem B3413933 : Blo 1516955 3413933 := bbase (se 3 (by rfl) ⟨640112, by rfl⟩ : syracuseStep 3413933 = 1280225) (by norm_num)
theorem B2561989 : Blo 1516955 2561989 := bbase (se 4 (by rfl) ⟨240186, by rfl⟩ : syracuseStep 2561989 = 480373) (by norm_num)
theorem B3839957 : Blo 1516955 3839957 := bbase (se 7 (by rfl) ⟨44999, by rfl⟩ : syracuseStep 3839957 = 89999) (by norm_num)
theorem B3414005 : Blo 1516955 3414005 := bbase (se 5 (by rfl) ⟨160031, by rfl⟩ : syracuseStep 3414005 = 320063) (by norm_num)
theorem B2308117 : Blo 1516955 2308117 := bbase (se 6 (by rfl) ⟨54096, by rfl⟩ : syracuseStep 2308117 = 108193) (by norm_num)
theorem B2562077 : Blo 1516955 2562077 := bbase (se 3 (by rfl) ⟨480389, by rfl⟩ : syracuseStep 2562077 = 960779) (by norm_num)
theorem B7788581 : Blo 1516955 7788581 := bbase (se 4 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 7788581 = 1460359) (by norm_num)
theorem B3414077 : Blo 1516955 3414077 := bbase (se 3 (by rfl) ⟨640139, by rfl⟩ : syracuseStep 3414077 = 1280279) (by norm_num)
theorem B2275445 : Blo 1516955 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B5470325 : Blo 1516955 5470325 := bbase (se 5 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 5470325 = 512843) (by norm_num)
theorem B3414149 : Blo 1516955 3414149 := bbase (se 4 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 3414149 = 640153) (by norm_num)
theorem B2881669 : Blo 1516955 2881669 := bbase (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) (by norm_num)
theorem B2275469 : Blo 1516955 2275469 := bbase (se 3 (by rfl) ⟨426650, by rfl⟩ : syracuseStep 2275469 = 853301) (by norm_num)
theorem B17315989 : Blo 1516955 17315989 := bbase (se 6 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 17315989 = 811687) (by norm_num)
theorem B3840149 : Blo 1516955 3840149 := bbase (se 6 (by rfl) ⟨90003, by rfl⟩ : syracuseStep 3840149 = 180007) (by norm_num)
theorem B2562205 : Blo 1516955 2562205 := bbase (se 3 (by rfl) ⟨480413, by rfl⟩ : syracuseStep 2562205 = 960827) (by norm_num)
theorem B2275493 : Blo 1516955 2275493 := bbase (se 4 (by rfl) ⟨213327, by rfl⟩ : syracuseStep 2275493 = 426655) (by norm_num)
theorem B2275517 : Blo 1516955 2275517 := bbase (se 3 (by rfl) ⟨426659, by rfl⟩ : syracuseStep 2275517 = 853319) (by norm_num)
theorem B3414221 : Blo 1516955 3414221 := bbase (se 3 (by rfl) ⟨640166, by rfl⟩ : syracuseStep 3414221 = 1280333) (by norm_num)
theorem B2275541 : Blo 1516955 2275541 := bbase (se 7 (by rfl) ⟨26666, by rfl⟩ : syracuseStep 2275541 = 53333) (by norm_num)
theorem B2275565 : Blo 1516955 2275565 := bbase (se 3 (by rfl) ⟨426668, by rfl⟩ : syracuseStep 2275565 = 853337) (by norm_num)
theorem B2562293 : Blo 1516955 2562293 := bbase (se 5 (by rfl) ⟨120107, by rfl⟩ : syracuseStep 2562293 = 240215) (by norm_num)
theorem B2275589 : Blo 1516955 2275589 := bbase (se 4 (by rfl) ⟨213336, by rfl⟩ : syracuseStep 2275589 = 426673) (by norm_num)
theorem B6658325 : Blo 1516955 6658325 := bbase (se 6 (by rfl) ⟨156054, by rfl⟩ : syracuseStep 6658325 = 312109) (by norm_num)
theorem B3414293 : Blo 1516955 3414293 := bbase (se 6 (by rfl) ⟨80022, by rfl⟩ : syracuseStep 3414293 = 160045) (by norm_num)
theorem B2881813 : Blo 1516955 2881813 := bbase (se 6 (by rfl) ⟨67542, by rfl⟩ : syracuseStep 2881813 = 135085) (by norm_num)
theorem B2275613 : Blo 1516955 2275613 := bbase (se 3 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 2275613 = 853355) (by norm_num)
theorem B2275637 : Blo 1516955 2275637 := bbase (se 5 (by rfl) ⟨106670, by rfl⟩ : syracuseStep 2275637 = 213341) (by norm_num)
theorem B2275661 : Blo 1516955 2275661 := bbase (se 3 (by rfl) ⟨426686, by rfl⟩ : syracuseStep 2275661 = 853373) (by norm_num)
theorem B3414365 : Blo 1516955 3414365 := bbase (se 3 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 3414365 = 1280387) (by norm_num)
theorem B2275685 : Blo 1516955 2275685 := bbase (se 4 (by rfl) ⟨213345, by rfl⟩ : syracuseStep 2275685 = 426691) (by norm_num)
theorem B2275709 : Blo 1516955 2275709 := bbase (se 3 (by rfl) ⟨426695, by rfl⟩ : syracuseStep 2275709 = 853391) (by norm_num)
theorem B2275733 : Blo 1516955 2275733 := bbase (se 6 (by rfl) ⟨53337, by rfl⟩ : syracuseStep 2275733 = 106675) (by norm_num)
theorem B3414437 : Blo 1516955 3414437 := bbase (se 4 (by rfl) ⟨320103, by rfl⟩ : syracuseStep 3414437 = 640207) (by norm_num)
theorem B2275757 : Blo 1516955 2275757 := bbase (se 3 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 2275757 = 853409) (by norm_num)
theorem B2881973 : Blo 1516955 2881973 := bbase (se 5 (by rfl) ⟨135092, by rfl⟩ : syracuseStep 2881973 = 270185) (by norm_num)
theorem B2308541 : Blo 1516955 2308541 := bbase (se 3 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 2308541 = 865703) (by norm_num)
theorem B2275781 : Blo 1516955 2275781 := bbase (se 4 (by rfl) ⟨213354, by rfl⟩ : syracuseStep 2275781 = 426709) (by norm_num)
theorem B1538509 : Blo 1516955 1538509 := bbase (se 3 (by rfl) ⟨288470, by rfl⟩ : syracuseStep 1538509 = 576941) (by norm_num)
theorem B2275805 : Blo 1516955 2275805 := bbase (se 3 (by rfl) ⟨426713, by rfl⟩ : syracuseStep 2275805 = 853427) (by norm_num)
theorem B3840493 : Blo 1516955 3840493 := bbase (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) (by norm_num)
theorem B3414509 : Blo 1516955 3414509 := bbase (se 3 (by rfl) ⟨640220, by rfl⟩ : syracuseStep 3414509 = 1280441) (by norm_num)
theorem B2275829 : Blo 1516955 2275829 := bbase (se 5 (by rfl) ⟨106679, by rfl⟩ : syracuseStep 2275829 = 213359) (by norm_num)
theorem B2275853 : Blo 1516955 2275853 := bbase (se 3 (by rfl) ⟨426722, by rfl⟩ : syracuseStep 2275853 = 853445) (by norm_num)
theorem B2431517 : Blo 1516955 2431517 := bbase (se 3 (by rfl) ⟨455909, by rfl⟩ : syracuseStep 2431517 = 911819) (by norm_num)
theorem B2275877 : Blo 1516955 2275877 := bbase (se 4 (by rfl) ⟨213363, by rfl⟩ : syracuseStep 2275877 = 426727) (by norm_num)
theorem B2161189 : Blo 1516955 2161189 := bbase (se 4 (by rfl) ⟨202611, by rfl⟩ : syracuseStep 2161189 = 405223) (by norm_num)
theorem B1620533 : Blo 1516955 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B3414581 : Blo 1516955 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B2275901 : Blo 1516955 2275901 := bbase (se 3 (by rfl) ⟨426731, by rfl⟩ : syracuseStep 2275901 = 853463) (by norm_num)
theorem B2882117 : Blo 1516955 2882117 := bbase (se 4 (by rfl) ⟨270198, by rfl⟩ : syracuseStep 2882117 = 540397) (by norm_num)
theorem B2275925 : Blo 1516955 2275925 := bbase (se 8 (by rfl) ⟨13335, by rfl⟩ : syracuseStep 2275925 = 26671) (by norm_num)
theorem B3840605 : Blo 1516955 3840605 := bbase (se 3 (by rfl) ⟨720113, by rfl⟩ : syracuseStep 3840605 = 1440227) (by norm_num)
theorem B2275949 : Blo 1516955 2275949 := bbase (se 3 (by rfl) ⟨426740, by rfl⟩ : syracuseStep 2275949 = 853481) (by norm_num)
theorem B3414653 : Blo 1516955 3414653 := bbase (se 3 (by rfl) ⟨640247, by rfl⟩ : syracuseStep 3414653 = 1280495) (by norm_num)
theorem B2275973 : Blo 1516955 2275973 := bbase (se 4 (by rfl) ⟨213372, by rfl⟩ : syracuseStep 2275973 = 426745) (by norm_num)
theorem B2275997 : Blo 1516955 2275997 := bbase (se 3 (by rfl) ⟨426749, by rfl⟩ : syracuseStep 2275997 = 853499) (by norm_num)
theorem B2276021 : Blo 1516955 2276021 := bbase (se 5 (by rfl) ⟨106688, by rfl⟩ : syracuseStep 2276021 = 213377) (by norm_num)
theorem B3414725 : Blo 1516955 3414725 := bbase (se 4 (by rfl) ⟨320130, by rfl⟩ : syracuseStep 3414725 = 640261) (by norm_num)
theorem B2276045 : Blo 1516955 2276045 := bbase (se 3 (by rfl) ⟨426758, by rfl⟩ : syracuseStep 2276045 = 853517) (by norm_num)
theorem B2276069 : Blo 1516955 2276069 := bbase (se 4 (by rfl) ⟨213381, by rfl⟩ : syracuseStep 2276069 = 426763) (by norm_num)
theorem B2276093 : Blo 1516955 2276093 := bbase (se 3 (by rfl) ⟨426767, by rfl⟩ : syracuseStep 2276093 = 853535) (by norm_num)
theorem B3414797 : Blo 1516955 3414797 := bbase (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) (by norm_num)
theorem B2276117 : Blo 1516955 2276117 := bbase (se 6 (by rfl) ⟨53346, by rfl⟩ : syracuseStep 2276117 = 106693) (by norm_num)
theorem B3840797 : Blo 1516955 3840797 := bbase (se 3 (by rfl) ⟨720149, by rfl⟩ : syracuseStep 3840797 = 1440299) (by norm_num)
theorem B4102949 : Blo 1516955 4102949 := bbase (se 4 (by rfl) ⟨384651, by rfl⟩ : syracuseStep 4102949 = 769303) (by norm_num)
theorem B2276141 : Blo 1516955 2276141 := bbase (se 3 (by rfl) ⟨426776, by rfl⟩ : syracuseStep 2276141 = 853553) (by norm_num)
theorem B2276165 : Blo 1516955 2276165 := bbase (se 4 (by rfl) ⟨213390, by rfl⟩ : syracuseStep 2276165 = 426781) (by norm_num)
theorem B3414869 : Blo 1516955 3414869 := bbase (se 9 (by rfl) ⟨10004, by rfl⟩ : syracuseStep 3414869 = 20009) (by norm_num)
theorem B2276189 : Blo 1516955 2276189 := bbase (se 3 (by rfl) ⟨426785, by rfl⟩ : syracuseStep 2276189 = 853571) (by norm_num)
theorem B5192549 : Blo 1516955 5192549 := bbase (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) (by norm_num)
theorem B2882405 : Blo 1516955 2882405 := bbase (se 4 (by rfl) ⟨270225, by rfl⟩ : syracuseStep 2882405 = 540451) (by norm_num)
theorem B2276213 : Blo 1516955 2276213 := bbase (se 5 (by rfl) ⟨106697, by rfl⟩ : syracuseStep 2276213 = 213395) (by norm_num)
theorem B2276237 : Blo 1516955 2276237 := bbase (se 3 (by rfl) ⟨426794, by rfl⟩ : syracuseStep 2276237 = 853589) (by norm_num)
theorem B3414941 : Blo 1516955 3414941 := bbase (se 3 (by rfl) ⟨640301, by rfl⟩ : syracuseStep 3414941 = 1280603) (by norm_num)
theorem B2276261 : Blo 1516955 2276261 := bbase (se 4 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 2276261 = 426799) (by norm_num)
theorem B2276285 : Blo 1516955 2276285 := bbase (se 3 (by rfl) ⟨426803, by rfl⟩ : syracuseStep 2276285 = 853607) (by norm_num)
theorem B2276309 : Blo 1516955 2276309 := bbase (se 7 (by rfl) ⟨26675, by rfl⟩ : syracuseStep 2276309 = 53351) (by norm_num)
theorem B3415013 : Blo 1516955 3415013 := bbase (se 4 (by rfl) ⟨320157, by rfl⟩ : syracuseStep 3415013 = 640315) (by norm_num)
theorem B2276333 : Blo 1516955 2276333 := bbase (se 3 (by rfl) ⟨426812, by rfl⟩ : syracuseStep 2276333 = 853625) (by norm_num)
theorem B1620977 : Blo 1516955 1620977 := bbase (se 2 (by rfl) ⟨607866, by rfl⟩ : syracuseStep 1620977 = 1215733) (by norm_num)
theorem B4676597 : Blo 1516955 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B2882557 : Blo 1516955 2882557 := bbase (se 3 (by rfl) ⟨540479, by rfl⟩ : syracuseStep 2882557 = 1080959) (by norm_num)
theorem B2276357 : Blo 1516955 2276357 := bbase (se 4 (by rfl) ⟨213408, by rfl⟩ : syracuseStep 2276357 = 426817) (by norm_num)
theorem B2276381 : Blo 1516955 2276381 := bbase (se 3 (by rfl) ⟨426821, by rfl⟩ : syracuseStep 2276381 = 853643) (by norm_num)
theorem B3415085 : Blo 1516955 3415085 := bbase (se 3 (by rfl) ⟨640328, by rfl⟩ : syracuseStep 3415085 = 1280657) (by norm_num)
theorem B2276405 : Blo 1516955 2276405 := bbase (se 5 (by rfl) ⟨106706, by rfl⟩ : syracuseStep 2276405 = 213413) (by norm_num)
theorem B12966965 : Blo 1516955 12966965 := bbase (se 5 (by rfl) ⟨607826, by rfl⟩ : syracuseStep 12966965 = 1215653) (by norm_num)
theorem B2276429 : Blo 1516955 2276429 := bbase (se 3 (by rfl) ⟨426830, by rfl⟩ : syracuseStep 2276429 = 853661) (by norm_num)
theorem B2276453 : Blo 1516955 2276453 := bbase (se 4 (by rfl) ⟨213417, by rfl⟩ : syracuseStep 2276453 = 426835) (by norm_num)
theorem B7683173 : Blo 1516955 7683173 := bbase (se 4 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 7683173 = 1440595) (by norm_num)
theorem B3841141 : Blo 1516955 3841141 := bbase (se 5 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 3841141 = 360107) (by norm_num)
theorem B3415157 : Blo 1516955 3415157 := bbase (se 5 (by rfl) ⟨160085, by rfl⟩ : syracuseStep 3415157 = 320171) (by norm_num)
theorem B2276477 : Blo 1516955 2276477 := bbase (se 3 (by rfl) ⟨426839, by rfl⟩ : syracuseStep 2276477 = 853679) (by norm_num)
theorem B2276501 : Blo 1516955 2276501 := bbase (se 6 (by rfl) ⟨53355, by rfl⟩ : syracuseStep 2276501 = 106711) (by norm_num)
theorem B3161261 : Blo 1516955 3161261 := bbase (se 3 (by rfl) ⟨592736, by rfl⟩ : syracuseStep 3161261 = 1185473) (by norm_num)
theorem B2276525 : Blo 1516955 2276525 := bbase (se 3 (by rfl) ⟨426848, by rfl⟩ : syracuseStep 2276525 = 853697) (by norm_num)
theorem B3415229 : Blo 1516955 3415229 := bbase (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) (by norm_num)
theorem B2276549 : Blo 1516955 2276549 := bbase (se 4 (by rfl) ⟨213426, by rfl⟩ : syracuseStep 2276549 = 426853) (by norm_num)
theorem B2432197 : Blo 1516955 2432197 := bbase (se 4 (by rfl) ⟨228018, by rfl⟩ : syracuseStep 2432197 = 456037) (by norm_num)
theorem B2276573 : Blo 1516955 2276573 := bbase (se 3 (by rfl) ⟨426857, by rfl⟩ : syracuseStep 2276573 = 853715) (by norm_num)
theorem B3841253 : Blo 1516955 3841253 := bbase (se 4 (by rfl) ⟨360117, by rfl⟩ : syracuseStep 3841253 = 720235) (by norm_num)
theorem B1621225 : Blo 1516955 1621225 := bbase (se 2 (by rfl) ⟨607959, by rfl⟩ : syracuseStep 1621225 = 1215919) (by norm_num)
theorem B2276597 : Blo 1516955 2276597 := bbase (se 5 (by rfl) ⟨106715, by rfl⟩ : syracuseStep 2276597 = 213431) (by norm_num)
theorem B3415301 : Blo 1516955 3415301 := bbase (se 4 (by rfl) ⟨320184, by rfl⟩ : syracuseStep 3415301 = 640369) (by norm_num)
theorem B2432261 : Blo 1516955 2432261 := bbase (se 4 (by rfl) ⟨228024, by rfl⟩ : syracuseStep 2432261 = 456049) (by norm_num)
theorem B2276621 : Blo 1516955 2276621 := bbase (se 3 (by rfl) ⟨426866, by rfl⟩ : syracuseStep 2276621 = 853733) (by norm_num)
theorem B2276645 : Blo 1516955 2276645 := bbase (se 4 (by rfl) ⟨213435, by rfl⟩ : syracuseStep 2276645 = 426871) (by norm_num)
theorem B2276669 : Blo 1516955 2276669 := bbase (se 3 (by rfl) ⟨426875, by rfl⟩ : syracuseStep 2276669 = 853751) (by norm_num)
theorem B2161981 : Blo 1516955 2161981 := bbase (se 3 (by rfl) ⟨405371, by rfl⟩ : syracuseStep 2161981 = 810743) (by norm_num)
theorem B3415373 : Blo 1516955 3415373 := bbase (se 3 (by rfl) ⟨640382, by rfl⟩ : syracuseStep 3415373 = 1280765) (by norm_num)
theorem B2276693 : Blo 1516955 2276693 := bbase (se 11 (by rfl) ⟨1667, by rfl⟩ : syracuseStep 2276693 = 3335) (by norm_num)
theorem B2276717 : Blo 1516955 2276717 := bbase (se 3 (by rfl) ⟨426884, by rfl⟩ : syracuseStep 2276717 = 853769) (by norm_num)
theorem B2276741 : Blo 1516955 2276741 := bbase (se 4 (by rfl) ⟨213444, by rfl⟩ : syracuseStep 2276741 = 426889) (by norm_num)
theorem B3415445 : Blo 1516955 3415445 := bbase (se 6 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 3415445 = 160099) (by norm_num)
theorem B2276765 : Blo 1516955 2276765 := bbase (se 3 (by rfl) ⟨426893, by rfl⟩ : syracuseStep 2276765 = 853787) (by norm_num)
theorem B3841445 : Blo 1516955 3841445 := bbase (se 4 (by rfl) ⟨360135, by rfl⟩ : syracuseStep 3841445 = 720271) (by norm_num)
theorem B2276789 : Blo 1516955 2276789 := bbase (se 5 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 2276789 = 213449) (by norm_num)
theorem B2276813 : Blo 1516955 2276813 := bbase (se 3 (by rfl) ⟨426902, by rfl⟩ : syracuseStep 2276813 = 853805) (by norm_num)
theorem B3415517 : Blo 1516955 3415517 := bbase (se 3 (by rfl) ⟨640409, by rfl⟩ : syracuseStep 3415517 = 1280819) (by norm_num)
theorem B2276837 : Blo 1516955 2276837 := bbase (se 4 (by rfl) ⟨213453, by rfl⟩ : syracuseStep 2276837 = 426907) (by norm_num)
theorem B2276861 : Blo 1516955 2276861 := bbase (se 3 (by rfl) ⟨426911, by rfl⟩ : syracuseStep 2276861 = 853823) (by norm_num)
theorem B4439573 : Blo 1516955 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B2276885 : Blo 1516955 2276885 := bbase (se 6 (by rfl) ⟨53364, by rfl⟩ : syracuseStep 2276885 = 106729) (by norm_num)
theorem B3415589 : Blo 1516955 3415589 := bbase (se 4 (by rfl) ⟨320211, by rfl⟩ : syracuseStep 3415589 = 640423) (by norm_num)
theorem B2276909 : Blo 1516955 2276909 := bbase (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) (by norm_num)
theorem B2276933 : Blo 1516955 2276933 := bbase (se 4 (by rfl) ⟨213462, by rfl⟩ : syracuseStep 2276933 = 426925) (by norm_num)
theorem B2276957 : Blo 1516955 2276957 := bbase (se 3 (by rfl) ⟨426929, by rfl⟩ : syracuseStep 2276957 = 853859) (by norm_num)
theorem B3415661 : Blo 1516955 3415661 := bbase (se 3 (by rfl) ⟨640436, by rfl⟩ : syracuseStep 3415661 = 1280873) (by norm_num)
theorem B2276981 : Blo 1516955 2276981 := bbase (se 5 (by rfl) ⟨106733, by rfl⟩ : syracuseStep 2276981 = 213467) (by norm_num)
theorem B2277005 : Blo 1516955 2277005 := bbase (se 3 (by rfl) ⟨426938, by rfl⟩ : syracuseStep 2277005 = 853877) (by norm_num)
theorem B2277029 : Blo 1516955 2277029 := bbase (se 4 (by rfl) ⟨213471, by rfl⟩ : syracuseStep 2277029 = 426943) (by norm_num)
theorem B3415733 : Blo 1516955 3415733 := bbase (se 5 (by rfl) ⟨160112, by rfl⟩ : syracuseStep 3415733 = 320225) (by norm_num)
theorem B2735797 : Blo 1516955 2735797 := bbase (se 5 (by rfl) ⟨128240, by rfl⟩ : syracuseStep 2735797 = 256481) (by norm_num)
theorem B2277053 : Blo 1516955 2277053 := bbase (se 3 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 2277053 = 853895) (by norm_num)
theorem B2277077 : Blo 1516955 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B2277101 : Blo 1516955 2277101 := bbase (se 3 (by rfl) ⟨426956, by rfl⟩ : syracuseStep 2277101 = 853913) (by norm_num)
theorem B5840629 : Blo 1516955 5840629 := bbase (se 5 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 5840629 = 547559) (by norm_num)
theorem B3841789 : Blo 1516955 3841789 := bbase (se 3 (by rfl) ⟨720335, by rfl⟩ : syracuseStep 3841789 = 1440671) (by norm_num)
theorem B3415805 : Blo 1516955 3415805 := bbase (se 3 (by rfl) ⟨640463, by rfl⟩ : syracuseStep 3415805 = 1280927) (by norm_num)
theorem B2277125 : Blo 1516955 2277125 := bbase (se 4 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 2277125 = 426961) (by norm_num)
theorem B16637717 : Blo 1516955 16637717 := bbase (se 6 (by rfl) ⟨389946, by rfl⟩ : syracuseStep 16637717 = 779893) (by norm_num)
theorem B2277149 : Blo 1516955 2277149 := bbase (se 3 (by rfl) ⟨426965, by rfl⟩ : syracuseStep 2277149 = 853931) (by norm_num)
theorem B2277173 : Blo 1516955 2277173 := bbase (se 5 (by rfl) ⟨106742, by rfl⟩ : syracuseStep 2277173 = 213485) (by norm_num)
theorem B3415877 : Blo 1516955 3415877 := bbase (se 4 (by rfl) ⟨320238, by rfl⟩ : syracuseStep 3415877 = 640477) (by norm_num)
theorem B2277197 : Blo 1516955 2277197 := bbase (se 3 (by rfl) ⟨426974, by rfl⟩ : syracuseStep 2277197 = 853949) (by norm_num)
theorem B3645269 : Blo 1516955 3645269 := bbase (se 9 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 3645269 = 21359) (by norm_num)
theorem B10944341 : Blo 1516955 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B2277221 : Blo 1516955 2277221 := bbase (se 4 (by rfl) ⟨213489, by rfl⟩ : syracuseStep 2277221 = 426979) (by norm_num)
theorem B3841901 : Blo 1516955 3841901 := bbase (se 3 (by rfl) ⟨720356, by rfl⟩ : syracuseStep 3841901 = 1440713) (by norm_num)
theorem B6152053 : Blo 1516955 6152053 := bbase (se 5 (by rfl) ⟨288377, by rfl⟩ : syracuseStep 6152053 = 576755) (by norm_num)
theorem B2277245 : Blo 1516955 2277245 := bbase (se 3 (by rfl) ⟨426983, by rfl⟩ : syracuseStep 2277245 = 853967) (by norm_num)
theorem B3415949 : Blo 1516955 3415949 := bbase (se 3 (by rfl) ⟨640490, by rfl⟩ : syracuseStep 3415949 = 1280981) (by norm_num)
theorem B2277269 : Blo 1516955 2277269 := bbase (se 6 (by rfl) ⟨53373, by rfl⟩ : syracuseStep 2277269 = 106747) (by norm_num)
theorem B2277293 : Blo 1516955 2277293 := bbase (se 3 (by rfl) ⟨426992, by rfl⟩ : syracuseStep 2277293 = 853985) (by norm_num)
theorem B2277317 : Blo 1516955 2277317 := bbase (se 4 (by rfl) ⟨213498, by rfl⟩ : syracuseStep 2277317 = 426997) (by norm_num)
theorem B3416021 : Blo 1516955 3416021 := bbase (se 7 (by rfl) ⟨40031, by rfl⟩ : syracuseStep 3416021 = 80063) (by norm_num)
theorem B2277341 : Blo 1516955 2277341 := bbase (se 3 (by rfl) ⟨427001, by rfl⟩ : syracuseStep 2277341 = 854003) (by norm_num)
theorem B2277365 : Blo 1516955 2277365 := bbase (se 5 (by rfl) ⟨106751, by rfl⟩ : syracuseStep 2277365 = 213503) (by norm_num)
theorem B2277377 : Blo 1516955 2277377 := bstep (se 2 (by rfl) ⟨854016, by rfl⟩ : syracuseStep 2277377 = 1708033) B1708033
theorem B2277395 : Blo 1516955 2277395 := bstep (se 1 (by rfl) ⟨1708046, by rfl⟩ : syracuseStep 2277395 = 3416093) B3416093
theorem B7684145 : Blo 1516955 7684145 := bstep (se 2 (by rfl) ⟨2881554, by rfl⟩ : syracuseStep 7684145 = 5763109) B5763109
theorem B2277425 : Blo 1516955 2277425 := bstep (se 2 (by rfl) ⟨854034, by rfl⟩ : syracuseStep 2277425 = 1708069) B1708069
theorem B2596931 : Blo 1516955 2596931 := bstep (se 1 (by rfl) ⟨1947698, by rfl⟩ : syracuseStep 2596931 = 3895397) B3895397
theorem B2277443 : Blo 1516955 2277443 := bstep (se 1 (by rfl) ⟨1708082, by rfl⟩ : syracuseStep 2277443 = 3416165) B3416165
theorem B2277473 : Blo 1516955 2277473 := bstep (se 2 (by rfl) ⟨854052, by rfl⟩ : syracuseStep 2277473 = 1708105) B1708105
theorem B8642659 : Blo 1516955 8642659 := bstep (se 1 (by rfl) ⟨6481994, by rfl⟩ : syracuseStep 8642659 = 12963989) B12963989
theorem B2277491 : Blo 1516955 2277491 := bstep (se 1 (by rfl) ⟨1708118, by rfl⟩ : syracuseStep 2277491 = 3416237) B3416237
theorem B6480013 : Blo 1516955 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B2277521 : Blo 1516955 2277521 := bstep (se 2 (by rfl) ⟨854070, by rfl⟩ : syracuseStep 2277521 = 1708141) B1708141
theorem B2277539 : Blo 1516955 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B3842225 : Blo 1516955 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B2277569 : Blo 1516955 2277569 := bstep (se 2 (by rfl) ⟨854088, by rfl⟩ : syracuseStep 2277569 = 1708177) B1708177
theorem B3416273 : Blo 1516955 3416273 := bstep (se 2 (by rfl) ⟨1281102, by rfl⟩ : syracuseStep 3416273 = 2562205) B2562205
theorem B2277587 : Blo 1516955 2277587 := bstep (se 1 (by rfl) ⟨1708190, by rfl⟩ : syracuseStep 2277587 = 3416381) B3416381
theorem B3842275 : Blo 1516955 3842275 := bstep (se 1 (by rfl) ⟨2881706, by rfl⟩ : syracuseStep 3842275 = 5763413) B5763413
theorem B3416291 : Blo 1516955 3416291 := bstep (se 1 (by rfl) ⟨2562218, by rfl⟩ : syracuseStep 3416291 = 5124437) B5124437
theorem B2277617 : Blo 1516955 2277617 := bstep (se 2 (by rfl) ⟨854106, by rfl⟩ : syracuseStep 2277617 = 1708213) B1708213
theorem B2597123 : Blo 1516955 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B2277635 : Blo 1516955 2277635 := bstep (se 1 (by rfl) ⟨1708226, by rfl⟩ : syracuseStep 2277635 = 3416453) B3416453
theorem B2277665 : Blo 1516955 2277665 := bstep (se 2 (by rfl) ⟨854124, by rfl⟩ : syracuseStep 2277665 = 1708249) B1708249
theorem B2277683 : Blo 1516955 2277683 := bstep (se 1 (by rfl) ⟨1708262, by rfl⟩ : syracuseStep 2277683 = 3416525) B3416525
theorem B5120333 : Blo 1516955 5120333 := bstep (se 3 (by rfl) ⟨960062, by rfl⟩ : syracuseStep 5120333 = 1920125) B1920125
theorem B12312931 : Blo 1516955 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B3842417 : Blo 1516955 3842417 := bstep (se 2 (by rfl) ⟨1440906, by rfl⟩ : syracuseStep 3842417 = 2881813) B2881813
theorem B5120387 : Blo 1516955 5120387 := bstep (se 1 (by rfl) ⟨3840290, by rfl⟩ : syracuseStep 5120387 = 7680581) B7680581
theorem B8643185 : Blo 1516955 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B5120657 : Blo 1516955 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B5759693 : Blo 1516955 5759693 := bstep (se 3 (by rfl) ⟨1079942, by rfl⟩ : syracuseStep 5759693 = 2159885) B2159885
theorem B19457009 : Blo 1516955 19457009 := bstep (se 2 (by rfl) ⟨7296378, by rfl⟩ : syracuseStep 19457009 = 14592757) B14592757
theorem B5121197 : Blo 1516955 5121197 := bstep (se 3 (by rfl) ⟨960224, by rfl⟩ : syracuseStep 5121197 = 1920449) B1920449
theorem B6481073 : Blo 1516955 6481073 := bstep (se 2 (by rfl) ⟨2430402, by rfl⟩ : syracuseStep 6481073 = 4860805) B4860805
theorem B5121251 : Blo 1516955 5121251 := bstep (se 1 (by rfl) ⟨3840938, by rfl⟩ : syracuseStep 5121251 = 7681877) B7681877
theorem B9487601 : Blo 1516955 9487601 := bstep (se 2 (by rfl) ⟨3557850, by rfl⟩ : syracuseStep 9487601 = 7115701) B7115701
theorem B3843409 : Blo 1516955 3843409 := bstep (se 2 (by rfl) ⟨1441278, by rfl⟩ : syracuseStep 3843409 = 2882557) B2882557
theorem B9233777 : Blo 1516955 9233777 := bstep (se 2 (by rfl) ⟨3462666, by rfl⟩ : syracuseStep 9233777 = 6925333) B6925333
theorem B1516963 : Blo 1516955 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B3646883 : Blo 1516955 3646883 := bstep (se 1 (by rfl) ⟨2735162, by rfl⟩ : syracuseStep 3646883 = 5470325) B5470325
theorem B1516979 : Blo 1516955 1516979 := bstep (se 1 (by rfl) ⟨1137734, by rfl⟩ : syracuseStep 1516979 = 2275469) B2275469
theorem B1516995 : Blo 1516955 1516995 := bstep (se 1 (by rfl) ⟨1137746, by rfl⟩ : syracuseStep 1516995 = 2275493) B2275493
theorem B1517011 : Blo 1516955 1517011 := bstep (se 1 (by rfl) ⟨1137758, by rfl⟩ : syracuseStep 1517011 = 2275517) B2275517
theorem B1517027 : Blo 1516955 1517027 := bstep (se 1 (by rfl) ⟨1137770, by rfl⟩ : syracuseStep 1517027 = 2275541) B2275541
theorem B7685603 : Blo 1516955 7685603 := bstep (se 1 (by rfl) ⟨5764202, by rfl⟩ : syracuseStep 7685603 = 11528405) B11528405
theorem B5760497 : Blo 1516955 5760497 := bstep (se 2 (by rfl) ⟨2160186, by rfl⟩ : syracuseStep 5760497 = 4320373) B4320373
theorem B5121521 : Blo 1516955 5121521 := bstep (se 2 (by rfl) ⟨1920570, by rfl⟩ : syracuseStep 5121521 = 3841141) B3841141
theorem B1517043 : Blo 1516955 1517043 := bstep (se 1 (by rfl) ⟨1137782, by rfl⟩ : syracuseStep 1517043 = 2275565) B2275565
theorem B1517059 : Blo 1516955 1517059 := bstep (se 1 (by rfl) ⟨1137794, by rfl⟩ : syracuseStep 1517059 = 2275589) B2275589
theorem B9725453 : Blo 1516955 9725453 := bstep (se 3 (by rfl) ⟨1823522, by rfl⟩ : syracuseStep 9725453 = 3647045) B3647045
theorem B1517075 : Blo 1516955 1517075 := bstep (se 1 (by rfl) ⟨1137806, by rfl⟩ : syracuseStep 1517075 = 2275613) B2275613
theorem B1517091 : Blo 1516955 1517091 := bstep (se 1 (by rfl) ⟨1137818, by rfl⟩ : syracuseStep 1517091 = 2275637) B2275637
theorem B1517107 : Blo 1516955 1517107 := bstep (se 1 (by rfl) ⟨1137830, by rfl⟩ : syracuseStep 1517107 = 2275661) B2275661
theorem B1517123 : Blo 1516955 1517123 := bstep (se 1 (by rfl) ⟨1137842, by rfl⟩ : syracuseStep 1517123 = 2275685) B2275685
theorem B1517139 : Blo 1516955 1517139 := bstep (se 1 (by rfl) ⟨1137854, by rfl⟩ : syracuseStep 1517139 = 2275709) B2275709
theorem B1517155 : Blo 1516955 1517155 := bstep (se 1 (by rfl) ⟨1137866, by rfl⟩ : syracuseStep 1517155 = 2275733) B2275733
theorem B1517171 : Blo 1516955 1517171 := bstep (se 1 (by rfl) ⟨1137878, by rfl⟩ : syracuseStep 1517171 = 2275757) B2275757
theorem B1517187 : Blo 1516955 1517187 := bstep (se 1 (by rfl) ⟨1137890, by rfl⟩ : syracuseStep 1517187 = 2275781) B2275781
theorem B1517203 : Blo 1516955 1517203 := bstep (se 1 (by rfl) ⟨1137902, by rfl⟩ : syracuseStep 1517203 = 2275805) B2275805
theorem B1517219 : Blo 1516955 1517219 := bstep (se 1 (by rfl) ⟨1137914, by rfl⟩ : syracuseStep 1517219 = 2275829) B2275829
theorem B1517235 : Blo 1516955 1517235 := bstep (se 1 (by rfl) ⟨1137926, by rfl⟩ : syracuseStep 1517235 = 2275853) B2275853
theorem B1517251 : Blo 1516955 1517251 := bstep (se 1 (by rfl) ⟨1137938, by rfl⟩ : syracuseStep 1517251 = 2275877) B2275877
theorem B1517267 : Blo 1516955 1517267 := bstep (se 1 (by rfl) ⟨1137950, by rfl⟩ : syracuseStep 1517267 = 2275901) B2275901
theorem B1517283 : Blo 1516955 1517283 := bstep (se 1 (by rfl) ⟨1137962, by rfl⟩ : syracuseStep 1517283 = 2275925) B2275925
theorem B1517299 : Blo 1516955 1517299 := bstep (se 1 (by rfl) ⟨1137974, by rfl⟩ : syracuseStep 1517299 = 2275949) B2275949
theorem B1517315 : Blo 1516955 1517315 := bstep (se 1 (by rfl) ⟨1137986, by rfl⟩ : syracuseStep 1517315 = 2275973) B2275973
theorem B3507985 : Blo 1516955 3507985 := bstep (se 2 (by rfl) ⟨1315494, by rfl⟩ : syracuseStep 3507985 = 2630989) B2630989
theorem B1517331 : Blo 1516955 1517331 := bstep (se 1 (by rfl) ⟨1137998, by rfl⟩ : syracuseStep 1517331 = 2275997) B2275997
theorem B1517347 : Blo 1516955 1517347 := bstep (se 1 (by rfl) ⟨1138010, by rfl⟩ : syracuseStep 1517347 = 2276021) B2276021
theorem B1517363 : Blo 1516955 1517363 := bstep (se 1 (by rfl) ⟨1138022, by rfl⟩ : syracuseStep 1517363 = 2276045) B2276045
theorem B1517379 : Blo 1516955 1517379 := bstep (se 1 (by rfl) ⟨1138034, by rfl⟩ : syracuseStep 1517379 = 2276069) B2276069
theorem B1517395 : Blo 1516955 1517395 := bstep (se 1 (by rfl) ⟨1138046, by rfl⟩ : syracuseStep 1517395 = 2276093) B2276093
theorem B1517411 : Blo 1516955 1517411 := bstep (se 1 (by rfl) ⟨1138058, by rfl⟩ : syracuseStep 1517411 = 2276117) B2276117
theorem B1517427 : Blo 1516955 1517427 := bstep (se 1 (by rfl) ⟨1138070, by rfl⟩ : syracuseStep 1517427 = 2276141) B2276141
theorem B1517443 : Blo 1516955 1517443 := bstep (se 1 (by rfl) ⟨1138082, by rfl⟩ : syracuseStep 1517443 = 2276165) B2276165
theorem B1517459 : Blo 1516955 1517459 := bstep (se 1 (by rfl) ⟨1138094, by rfl⟩ : syracuseStep 1517459 = 2276189) B2276189
theorem B1517475 : Blo 1516955 1517475 := bstep (se 1 (by rfl) ⟨1138106, by rfl⟩ : syracuseStep 1517475 = 2276213) B2276213
theorem B1517491 : Blo 1516955 1517491 := bstep (se 1 (by rfl) ⟨1138118, by rfl⟩ : syracuseStep 1517491 = 2276237) B2276237
theorem B1517507 : Blo 1516955 1517507 := bstep (se 1 (by rfl) ⟨1138130, by rfl⟩ : syracuseStep 1517507 = 2276261) B2276261
theorem B1517523 : Blo 1516955 1517523 := bstep (se 1 (by rfl) ⟨1138142, by rfl⟩ : syracuseStep 1517523 = 2276285) B2276285
theorem B1517539 : Blo 1516955 1517539 := bstep (se 1 (by rfl) ⟨1138154, by rfl⟩ : syracuseStep 1517539 = 2276309) B2276309
theorem B1517555 : Blo 1516955 1517555 := bstep (se 1 (by rfl) ⟨1138166, by rfl⟩ : syracuseStep 1517555 = 2276333) B2276333
theorem B1517571 : Blo 1516955 1517571 := bstep (se 1 (by rfl) ⟨1138178, by rfl⟩ : syracuseStep 1517571 = 2276357) B2276357
theorem B5122061 : Blo 1516955 5122061 := bstep (se 3 (by rfl) ⟨960386, by rfl⟩ : syracuseStep 5122061 = 1920773) B1920773
theorem B1517587 : Blo 1516955 1517587 := bstep (se 1 (by rfl) ⟨1138190, by rfl⟩ : syracuseStep 1517587 = 2276381) B2276381
theorem B1517603 : Blo 1516955 1517603 := bstep (se 1 (by rfl) ⟨1138202, by rfl⟩ : syracuseStep 1517603 = 2276405) B2276405
theorem B8644643 : Blo 1516955 8644643 := bstep (se 1 (by rfl) ⟨6483482, by rfl⟩ : syracuseStep 8644643 = 12966965) B12966965
theorem B1517619 : Blo 1516955 1517619 := bstep (se 1 (by rfl) ⟨1138214, by rfl⟩ : syracuseStep 1517619 = 2276429) B2276429
theorem B1517635 : Blo 1516955 1517635 := bstep (se 1 (by rfl) ⟨1138226, by rfl⟩ : syracuseStep 1517635 = 2276453) B2276453
theorem B5122115 : Blo 1516955 5122115 := bstep (se 1 (by rfl) ⟨3841586, by rfl⟩ : syracuseStep 5122115 = 7683173) B7683173
theorem B1517651 : Blo 1516955 1517651 := bstep (se 1 (by rfl) ⟨1138238, by rfl⟩ : syracuseStep 1517651 = 2276477) B2276477
theorem B1517667 : Blo 1516955 1517667 := bstep (se 1 (by rfl) ⟨1138250, by rfl⟩ : syracuseStep 1517667 = 2276501) B2276501
theorem B35063921 : Blo 1516955 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B2107507 : Blo 1516955 2107507 := bstep (se 1 (by rfl) ⟨1580630, by rfl⟩ : syracuseStep 2107507 = 3161261) B3161261
theorem B1517683 : Blo 1516955 1517683 := bstep (se 1 (by rfl) ⟨1138262, by rfl⟩ : syracuseStep 1517683 = 2276525) B2276525
theorem B1517699 : Blo 1516955 1517699 := bstep (se 1 (by rfl) ⟨1138274, by rfl⟩ : syracuseStep 1517699 = 2276549) B2276549
theorem B5761165 : Blo 1516955 5761165 := bstep (se 3 (by rfl) ⟨1080218, by rfl⟩ : syracuseStep 5761165 = 2160437) B2160437
theorem B1517715 : Blo 1516955 1517715 := bstep (se 1 (by rfl) ⟨1138286, by rfl⟩ : syracuseStep 1517715 = 2276573) B2276573
theorem B7293091 : Blo 1516955 7293091 := bstep (se 1 (by rfl) ⟨5469818, by rfl⟩ : syracuseStep 7293091 = 10939637) B10939637
theorem B1517731 : Blo 1516955 1517731 := bstep (se 1 (by rfl) ⟨1138298, by rfl⟩ : syracuseStep 1517731 = 2276597) B2276597
theorem B1517747 : Blo 1516955 1517747 := bstep (se 1 (by rfl) ⟨1138310, by rfl⟩ : syracuseStep 1517747 = 2276621) B2276621
theorem B1517763 : Blo 1516955 1517763 := bstep (se 1 (by rfl) ⟨1138322, by rfl⟩ : syracuseStep 1517763 = 2276645) B2276645
theorem B1517779 : Blo 1516955 1517779 := bstep (se 1 (by rfl) ⟨1138334, by rfl⟩ : syracuseStep 1517779 = 2276669) B2276669
theorem B1517795 : Blo 1516955 1517795 := bstep (se 1 (by rfl) ⟨1138346, by rfl⟩ : syracuseStep 1517795 = 2276693) B2276693
theorem B1517811 : Blo 1516955 1517811 := bstep (se 1 (by rfl) ⟨1138358, by rfl⟩ : syracuseStep 1517811 = 2276717) B2276717
theorem B3647729 : Blo 1516955 3647729 := bstep (se 2 (by rfl) ⟨1367898, by rfl⟩ : syracuseStep 3647729 = 2735797) B2735797
theorem B1517827 : Blo 1516955 1517827 := bstep (se 1 (by rfl) ⟨1138370, by rfl⟩ : syracuseStep 1517827 = 2276741) B2276741
theorem B7686413 : Blo 1516955 7686413 := bstep (se 3 (by rfl) ⟨1441202, by rfl⟩ : syracuseStep 7686413 = 2882405) B2882405
theorem B1517843 : Blo 1516955 1517843 := bstep (se 1 (by rfl) ⟨1138382, by rfl⟩ : syracuseStep 1517843 = 2276765) B2276765
theorem B1517859 : Blo 1516955 1517859 := bstep (se 1 (by rfl) ⟨1138394, by rfl⟩ : syracuseStep 1517859 = 2276789) B2276789
theorem B1517875 : Blo 1516955 1517875 := bstep (se 1 (by rfl) ⟨1138406, by rfl⟩ : syracuseStep 1517875 = 2276813) B2276813
theorem B1517891 : Blo 1516955 1517891 := bstep (se 1 (by rfl) ⟨1138418, by rfl⟩ : syracuseStep 1517891 = 2276837) B2276837
theorem B10127693 : Blo 1516955 10127693 := bstep (se 3 (by rfl) ⟨1898942, by rfl⟩ : syracuseStep 10127693 = 3797885) B3797885
theorem B5122385 : Blo 1516955 5122385 := bstep (se 2 (by rfl) ⟨1920894, by rfl⟩ : syracuseStep 5122385 = 3841789) B3841789
theorem B1517907 : Blo 1516955 1517907 := bstep (se 1 (by rfl) ⟨1138430, by rfl⟩ : syracuseStep 1517907 = 2276861) B2276861
theorem B2959715 : Blo 1516955 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B1517923 : Blo 1516955 1517923 := bstep (se 1 (by rfl) ⟨1138442, by rfl⟩ : syracuseStep 1517923 = 2276885) B2276885
theorem B1517939 : Blo 1516955 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B1517955 : Blo 1516955 1517955 := bstep (se 1 (by rfl) ⟨1138466, by rfl⟩ : syracuseStep 1517955 = 2276933) B2276933
theorem B1517971 : Blo 1516955 1517971 := bstep (se 1 (by rfl) ⟨1138478, by rfl⟩ : syracuseStep 1517971 = 2276957) B2276957
theorem B1517987 : Blo 1516955 1517987 := bstep (se 1 (by rfl) ⟨1138490, by rfl⟩ : syracuseStep 1517987 = 2276981) B2276981
theorem B7293361 : Blo 1516955 7293361 := bstep (se 2 (by rfl) ⟨2735010, by rfl⟩ : syracuseStep 7293361 = 5470021) B5470021
theorem B1518003 : Blo 1516955 1518003 := bstep (se 1 (by rfl) ⟨1138502, by rfl⟩ : syracuseStep 1518003 = 2277005) B2277005
theorem B1518019 : Blo 1516955 1518019 := bstep (se 1 (by rfl) ⟨1138514, by rfl⟩ : syracuseStep 1518019 = 2277029) B2277029
theorem B1518035 : Blo 1516955 1518035 := bstep (se 1 (by rfl) ⟨1138526, by rfl⟩ : syracuseStep 1518035 = 2277053) B2277053
theorem B1518051 : Blo 1516955 1518051 := bstep (se 1 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 1518051 = 2277077) B2277077
theorem B8202737 : Blo 1516955 8202737 := bstep (se 2 (by rfl) ⟨3076026, by rfl⟩ : syracuseStep 8202737 = 6152053) B6152053
theorem B1518067 : Blo 1516955 1518067 := bstep (se 1 (by rfl) ⟨1138550, by rfl⟩ : syracuseStep 1518067 = 2277101) B2277101
theorem B1518083 : Blo 1516955 1518083 := bstep (se 1 (by rfl) ⟨1138562, by rfl⟩ : syracuseStep 1518083 = 2277125) B2277125
theorem B1518099 : Blo 1516955 1518099 := bstep (se 1 (by rfl) ⟨1138574, by rfl⟩ : syracuseStep 1518099 = 2277149) B2277149
theorem B1518115 : Blo 1516955 1518115 := bstep (se 1 (by rfl) ⟨1138586, by rfl⟩ : syracuseStep 1518115 = 2277173) B2277173
theorem B1518131 : Blo 1516955 1518131 := bstep (se 1 (by rfl) ⟨1138598, by rfl⟩ : syracuseStep 1518131 = 2277197) B2277197
theorem B1518147 : Blo 1516955 1518147 := bstep (se 1 (by rfl) ⟨1138610, by rfl⟩ : syracuseStep 1518147 = 2277221) B2277221
theorem B1518163 : Blo 1516955 1518163 := bstep (se 1 (by rfl) ⟨1138622, by rfl⟩ : syracuseStep 1518163 = 2277245) B2277245
theorem B1518179 : Blo 1516955 1518179 := bstep (se 1 (by rfl) ⟨1138634, by rfl⟩ : syracuseStep 1518179 = 2277269) B2277269
theorem B1706611 : Blo 1516955 1706611 := bstep (se 1 (by rfl) ⟨1279958, by rfl⟩ : syracuseStep 1706611 = 2559917) B2559917
theorem B1518195 : Blo 1516955 1518195 := bstep (se 1 (by rfl) ⟨1138646, by rfl⟩ : syracuseStep 1518195 = 2277293) B2277293
theorem B1518211 : Blo 1516955 1518211 := bstep (se 1 (by rfl) ⟨1138658, by rfl⟩ : syracuseStep 1518211 = 2277317) B2277317
theorem B1518227 : Blo 1516955 1518227 := bstep (se 1 (by rfl) ⟨1138670, by rfl⟩ : syracuseStep 1518227 = 2277341) B2277341
theorem B1518243 : Blo 1516955 1518243 := bstep (se 1 (by rfl) ⟨1138682, by rfl⟩ : syracuseStep 1518243 = 2277365) B2277365
theorem B1518259 : Blo 1516955 1518259 := bstep (se 1 (by rfl) ⟨1138694, by rfl⟩ : syracuseStep 1518259 = 2277389) B2277389
theorem B1518275 : Blo 1516955 1518275 := bstep (se 1 (by rfl) ⟨1138706, by rfl⟩ : syracuseStep 1518275 = 2277413) B2277413
theorem B4926161 : Blo 1516955 4926161 := bstep (se 2 (by rfl) ⟨1847310, by rfl⟩ : syracuseStep 4926161 = 3694621) B3694621
theorem B1518291 : Blo 1516955 1518291 := bstep (se 1 (by rfl) ⟨1138718, by rfl⟩ : syracuseStep 1518291 = 2277437) B2277437
theorem B1518307 : Blo 1516955 1518307 := bstep (se 1 (by rfl) ⟨1138730, by rfl⟩ : syracuseStep 1518307 = 2277461) B2277461
theorem B1518323 : Blo 1516955 1518323 := bstep (se 1 (by rfl) ⟨1138742, by rfl⟩ : syracuseStep 1518323 = 2277485) B2277485
theorem B1706755 : Blo 1516955 1706755 := bstep (se 1 (by rfl) ⟨1280066, by rfl⟩ : syracuseStep 1706755 = 2560133) B2560133
theorem B1518339 : Blo 1516955 1518339 := bstep (se 1 (by rfl) ⟨1138754, by rfl⟩ : syracuseStep 1518339 = 2277509) B2277509
theorem B1518355 : Blo 1516955 1518355 := bstep (se 1 (by rfl) ⟨1138766, by rfl⟩ : syracuseStep 1518355 = 2277533) B2277533
theorem B1518371 : Blo 1516955 1518371 := bstep (se 1 (by rfl) ⟨1138778, by rfl⟩ : syracuseStep 1518371 = 2277557) B2277557
theorem B1731379 : Blo 1516955 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B1518387 : Blo 1516955 1518387 := bstep (se 1 (by rfl) ⟨1138790, by rfl⟩ : syracuseStep 1518387 = 2277581) B2277581
theorem B1518403 : Blo 1516955 1518403 := bstep (se 1 (by rfl) ⟨1138802, by rfl⟩ : syracuseStep 1518403 = 2277605) B2277605
theorem B1518419 : Blo 1516955 1518419 := bstep (se 1 (by rfl) ⟨1138814, by rfl⟩ : syracuseStep 1518419 = 2277629) B2277629
theorem B1518435 : Blo 1516955 1518435 := bstep (se 1 (by rfl) ⟨1138826, by rfl⟩ : syracuseStep 1518435 = 2277653) B2277653
theorem B5122925 : Blo 1516955 5122925 := bstep (se 3 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 5122925 = 1921097) B1921097
theorem B1518451 : Blo 1516955 1518451 := bstep (se 1 (by rfl) ⟨1138838, by rfl⟩ : syracuseStep 1518451 = 2277677) B2277677
theorem B4320145 : Blo 1516955 4320145 := bstep (se 2 (by rfl) ⟨1620054, by rfl⟩ : syracuseStep 4320145 = 3240109) B3240109
theorem B1706899 : Blo 1516955 1706899 := bstep (se 1 (by rfl) ⟨1280174, by rfl⟩ : syracuseStep 1706899 = 2560349) B2560349
theorem B5761955 : Blo 1516955 5761955 := bstep (se 1 (by rfl) ⟨4321466, by rfl⟩ : syracuseStep 5761955 = 8642933) B8642933
theorem B5122979 : Blo 1516955 5122979 := bstep (se 1 (by rfl) ⟨3842234, by rfl⟩ : syracuseStep 5122979 = 7684469) B7684469
theorem B1920019 : Blo 1516955 1920019 := bstep (se 1 (by rfl) ⟨1440014, by rfl⟩ : syracuseStep 1920019 = 2880029) B2880029
theorem B1707043 : Blo 1516955 1707043 := bstep (se 1 (by rfl) ⟨1280282, by rfl⟩ : syracuseStep 1707043 = 2560565) B2560565
theorem B1920115 : Blo 1516955 1920115 := bstep (se 1 (by rfl) ⟨1440086, by rfl⟩ : syracuseStep 1920115 = 2880173) B2880173
theorem B5123249 : Blo 1516955 5123249 := bstep (se 2 (by rfl) ⟨1921218, by rfl⟩ : syracuseStep 5123249 = 3842437) B3842437
theorem B1707187 : Blo 1516955 1707187 := bstep (se 1 (by rfl) ⟨1280390, by rfl⟩ : syracuseStep 1707187 = 2560781) B2560781
theorem B4156625 : Blo 1516955 4156625 := bstep (se 2 (by rfl) ⟨1558734, by rfl⟩ : syracuseStep 4156625 = 3117469) B3117469
theorem B2051345 : Blo 1516955 2051345 := bstep (se 2 (by rfl) ⟨769254, by rfl⟩ : syracuseStep 2051345 = 1538509) B1538509
theorem B1707331 : Blo 1516955 1707331 := bstep (se 1 (by rfl) ⟨1280498, by rfl⟩ : syracuseStep 1707331 = 2560997) B2560997
theorem B1707475 : Blo 1516955 1707475 := bstep (se 1 (by rfl) ⟨1280606, by rfl⟩ : syracuseStep 1707475 = 2561213) B2561213
theorem B4861421 : Blo 1516955 4861421 := bstep (se 3 (by rfl) ⟨911516, by rfl⟩ : syracuseStep 4861421 = 1823033) B1823033
theorem B5762609 : Blo 1516955 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B1920611 : Blo 1516955 1920611 := bstep (se 1 (by rfl) ⟨1440458, by rfl⟩ : syracuseStep 1920611 = 2880917) B2880917
theorem B1707619 : Blo 1516955 1707619 := bstep (se 1 (by rfl) ⟨1280714, by rfl⟩ : syracuseStep 1707619 = 2561429) B2561429
theorem B9727685 : Blo 1516955 9727685 := bstep (se 4 (by rfl) ⟨911970, by rfl⟩ : syracuseStep 9727685 = 1823941) B1823941
theorem B5123789 : Blo 1516955 5123789 := bstep (se 3 (by rfl) ⟨960710, by rfl⟩ : syracuseStep 5123789 = 1921421) B1921421
theorem B1707763 : Blo 1516955 1707763 := bstep (se 1 (by rfl) ⟨1280822, by rfl⟩ : syracuseStep 1707763 = 2561645) B2561645
theorem B5123843 : Blo 1516955 5123843 := bstep (se 1 (by rfl) ⟨3842882, by rfl⟩ : syracuseStep 5123843 = 7685765) B7685765
theorem B6156109 : Blo 1516955 6156109 := bstep (se 3 (by rfl) ⟨1154270, by rfl⟩ : syracuseStep 6156109 = 2308541) B2308541
theorem B2051939 : Blo 1516955 2051939 := bstep (se 1 (by rfl) ⟨1538954, by rfl⟩ : syracuseStep 2051939 = 3077909) B3077909
theorem B1707907 : Blo 1516955 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B8646533 : Blo 1516955 8646533 := bstep (se 4 (by rfl) ⟨810612, by rfl⟩ : syracuseStep 8646533 = 1621225) B1621225
theorem B2559937 : Blo 1516955 2559937 := bstep (se 2 (by rfl) ⟨959976, by rfl⟩ : syracuseStep 2559937 = 1919953) B1919953
theorem B31150021 : Blo 1516955 31150021 := bstep (se 4 (by rfl) ⟨2920314, by rfl⟩ : syracuseStep 31150021 = 5840629) B5840629
theorem B2559971 : Blo 1516955 2559971 := bstep (se 1 (by rfl) ⟨1919978, by rfl⟩ : syracuseStep 2559971 = 3839957) B3839957
theorem B3239939 : Blo 1516955 3239939 := bstep (se 1 (by rfl) ⟨2429954, by rfl⟩ : syracuseStep 3239939 = 4859909) B4859909
theorem B5124113 : Blo 1516955 5124113 := bstep (se 2 (by rfl) ⟨1921542, by rfl⟩ : syracuseStep 5124113 = 3843085) B3843085
theorem B1708051 : Blo 1516955 1708051 := bstep (se 1 (by rfl) ⟨1281038, by rfl⟩ : syracuseStep 1708051 = 2562077) B2562077
theorem B6156337 : Blo 1516955 6156337 := bstep (se 2 (by rfl) ⟨2308626, by rfl⟩ : syracuseStep 6156337 = 4617253) B4617253
theorem B6484045 : Blo 1516955 6484045 := bstep (se 3 (by rfl) ⟨1215758, by rfl⟩ : syracuseStep 6484045 = 2431517) B2431517
theorem B2560099 : Blo 1516955 2560099 := bstep (se 1 (by rfl) ⟨1920074, by rfl⟩ : syracuseStep 2560099 = 3840149) B3840149
theorem B4321421 : Blo 1516955 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B1708195 : Blo 1516955 1708195 := bstep (se 1 (by rfl) ⟨1281146, by rfl⟩ : syracuseStep 1708195 = 2562293) B2562293
theorem B2560241 : Blo 1516955 2560241 := bstep (se 2 (by rfl) ⟨960090, by rfl⟩ : syracuseStep 2560241 = 1920181) B1920181
theorem B1921315 : Blo 1516955 1921315 := bstep (se 1 (by rfl) ⟨1440986, by rfl⟩ : syracuseStep 1921315 = 2881973) B2881973
theorem B4321603 : Blo 1516955 4321603 := bstep (se 1 (by rfl) ⟨3241202, by rfl⟩ : syracuseStep 4321603 = 6482405) B6482405
theorem B13840739 : Blo 1516955 13840739 := bstep (se 1 (by rfl) ⟨10380554, by rfl⟩ : syracuseStep 13840739 = 20761109) B20761109
theorem B2560369 : Blo 1516955 2560369 := bstep (se 2 (by rfl) ⟨960138, by rfl⟩ : syracuseStep 2560369 = 1920277) B1920277
theorem B4321649 : Blo 1516955 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B1921411 : Blo 1516955 1921411 := bstep (se 1 (by rfl) ⟨1441058, by rfl⟩ : syracuseStep 1921411 = 2882117) B2882117
theorem B2560403 : Blo 1516955 2560403 := bstep (se 1 (by rfl) ⟨1920302, by rfl⟩ : syracuseStep 2560403 = 3840605) B3840605
theorem B7680419 : Blo 1516955 7680419 := bstep (se 1 (by rfl) ⟨5760314, by rfl⟩ : syracuseStep 7680419 = 11520629) B11520629
theorem B6484387 : Blo 1516955 6484387 := bstep (se 1 (by rfl) ⟨4863290, by rfl⟩ : syracuseStep 6484387 = 9726581) B9726581
theorem B11522573 : Blo 1516955 11522573 := bstep (se 3 (by rfl) ⟨2160482, by rfl⟩ : syracuseStep 11522573 = 4320965) B4320965
theorem B2560531 : Blo 1516955 2560531 := bstep (se 1 (by rfl) ⟨1920398, by rfl⟩ : syracuseStep 2560531 = 3840797) B3840797
theorem B5124653 : Blo 1516955 5124653 := bstep (se 3 (by rfl) ⟨960872, by rfl⟩ : syracuseStep 5124653 = 1921745) B1921745
theorem B3461699 : Blo 1516955 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B5124707 : Blo 1516955 5124707 := bstep (se 1 (by rfl) ⟨3843530, by rfl⟩ : syracuseStep 5124707 = 7687061) B7687061
theorem B2560673 : Blo 1516955 2560673 := bstep (se 2 (by rfl) ⟨960252, by rfl⟩ : syracuseStep 2560673 = 1920505) B1920505
theorem B3117731 : Blo 1516955 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B6238883 : Blo 1516955 6238883 := bstep (se 1 (by rfl) ⟨4679162, by rfl⟩ : syracuseStep 6238883 = 9358325) B9358325
theorem B2560801 : Blo 1516955 2560801 := bstep (se 2 (by rfl) ⟨960300, by rfl⟩ : syracuseStep 2560801 = 1920601) B1920601
theorem B2560835 : Blo 1516955 2560835 := bstep (se 1 (by rfl) ⟨1920626, by rfl⟩ : syracuseStep 2560835 = 3841253) B3841253
theorem B3240785 : Blo 1516955 3240785 := bstep (se 2 (by rfl) ⟨1215294, by rfl⟩ : syracuseStep 3240785 = 2430589) B2430589
theorem B2880355 : Blo 1516955 2880355 := bstep (se 1 (by rfl) ⟨2160266, by rfl⟩ : syracuseStep 2880355 = 4320533) B4320533
theorem B2560963 : Blo 1516955 2560963 := bstep (se 1 (by rfl) ⟨1920722, by rfl⟩ : syracuseStep 2560963 = 3841445) B3841445
theorem B4617155 : Blo 1516955 4617155 := bstep (se 1 (by rfl) ⟨3462866, by rfl⟩ : syracuseStep 4617155 = 6925733) B6925733
theorem B12301253 : Blo 1516955 12301253 := bstep (se 4 (by rfl) ⟨1153242, by rfl⟩ : syracuseStep 12301253 = 2306485) B2306485
theorem B5764067 : Blo 1516955 5764067 := bstep (se 1 (by rfl) ⟨4323050, by rfl⟩ : syracuseStep 5764067 = 8646101) B8646101
theorem B4101101 : Blo 1516955 4101101 := bstep (se 3 (by rfl) ⟨768956, by rfl⟩ : syracuseStep 4101101 = 1537913) B1537913
theorem B10941425 : Blo 1516955 10941425 := bstep (se 2 (by rfl) ⟨4103034, by rfl⟩ : syracuseStep 10941425 = 8206069) B8206069
theorem B5764081 : Blo 1516955 5764081 := bstep (se 2 (by rfl) ⟨2161530, by rfl⟩ : syracuseStep 5764081 = 4323061) B4323061
theorem B2880515 : Blo 1516955 2880515 := bstep (se 1 (by rfl) ⟨2160386, by rfl⟩ : syracuseStep 2880515 = 4320773) B4320773
theorem B7894093 : Blo 1516955 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B2561105 : Blo 1516955 2561105 := bstep (se 2 (by rfl) ⟨960414, by rfl⟩ : syracuseStep 2561105 = 1920829) B1920829
theorem B1946755 : Blo 1516955 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B17290421 : Blo 1516955 17290421 := bstep (se 5 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 17290421 = 1620977) B1620977
theorem B1848515 : Blo 1516955 1848515 := bstep (se 1 (by rfl) ⟨1386386, by rfl⟩ : syracuseStep 1848515 = 2772773) B2772773
theorem B7681229 : Blo 1516955 7681229 := bstep (se 3 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 7681229 = 2880461) B2880461
theorem B2561233 : Blo 1516955 2561233 := bstep (se 2 (by rfl) ⟨960462, by rfl⟩ : syracuseStep 2561233 = 1920925) B1920925
theorem B2430179 : Blo 1516955 2430179 := bstep (se 1 (by rfl) ⟨1822634, by rfl⟩ : syracuseStep 2430179 = 3645269) B3645269
theorem B7296227 : Blo 1516955 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B2561267 : Blo 1516955 2561267 := bstep (se 1 (by rfl) ⟨1920950, by rfl⟩ : syracuseStep 2561267 = 3841901) B3841901
theorem B4928813 : Blo 1516955 4928813 := bstep (se 3 (by rfl) ⟨924152, by rfl⟩ : syracuseStep 4928813 = 1848305) B1848305
theorem B3077489 : Blo 1516955 3077489 := bstep (se 2 (by rfl) ⟨1154058, by rfl⟩ : syracuseStep 3077489 = 2308117) B2308117
theorem B2561395 : Blo 1516955 2561395 := bstep (se 1 (by rfl) ⟨1921046, by rfl⟩ : syracuseStep 2561395 = 3842093) B3842093
theorem B1947011 : Blo 1516955 1947011 := bstep (se 1 (by rfl) ⟨1460258, by rfl⟩ : syracuseStep 1947011 = 2920517) B2920517
theorem B3413393 : Blo 1516955 3413393 := bstep (se 2 (by rfl) ⟨1280022, by rfl⟩ : syracuseStep 3413393 = 2560045) B2560045
theorem B3413411 : Blo 1516955 3413411 := bstep (se 1 (by rfl) ⟨2560058, by rfl⟩ : syracuseStep 3413411 = 5120117) B5120117
theorem B2307521 : Blo 1516955 2307521 := bstep (se 2 (by rfl) ⟨865320, by rfl⟩ : syracuseStep 2307521 = 1730641) B1730641
theorem B11679173 : Blo 1516955 11679173 := bstep (se 4 (by rfl) ⟨1094922, by rfl⟩ : syracuseStep 11679173 = 2189845) B2189845
theorem B2561537 : Blo 1516955 2561537 := bstep (se 2 (by rfl) ⟨960576, by rfl⟩ : syracuseStep 2561537 = 1921153) B1921153
theorem B5191235 : Blo 1516955 5191235 := bstep (se 1 (by rfl) ⟨3893426, by rfl⟩ : syracuseStep 5191235 = 7786853) B7786853
theorem B9721457 : Blo 1516955 9721457 := bstep (se 2 (by rfl) ⟨3645546, by rfl⟩ : syracuseStep 9721457 = 7291093) B7291093
theorem B2561665 : Blo 1516955 2561665 := bstep (se 2 (by rfl) ⟨960624, by rfl⟩ : syracuseStep 2561665 = 1921249) B1921249
theorem B2561699 : Blo 1516955 2561699 := bstep (se 1 (by rfl) ⟨1921274, by rfl⟩ : syracuseStep 2561699 = 3842549) B3842549
theorem B3413681 : Blo 1516955 3413681 := bstep (se 2 (by rfl) ⟨1280130, by rfl⟩ : syracuseStep 3413681 = 2560261) B2560261
theorem B3413699 : Blo 1516955 3413699 := bstep (se 1 (by rfl) ⟨2560274, by rfl⟩ : syracuseStep 3413699 = 5120549) B5120549
theorem B4994797 : Blo 1516955 4994797 := bstep (se 3 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 4994797 = 1873049) B1873049
theorem B8640269 : Blo 1516955 8640269 := bstep (se 3 (by rfl) ⟨1620050, by rfl⟩ : syracuseStep 8640269 = 3240101) B3240101
theorem B369407765 : Blo 1516955 369407765 := bstep (se 6 (by rfl) ⟨8657994, by rfl⟩ : syracuseStep 369407765 = 17315989) B17315989
theorem B2561827 : Blo 1516955 2561827 := bstep (se 1 (by rfl) ⟨1921370, by rfl⟩ : syracuseStep 2561827 = 3842741) B3842741
theorem B4323107 : Blo 1516955 4323107 := bstep (se 1 (by rfl) ⟨3242330, by rfl⟩ : syracuseStep 4323107 = 6484661) B6484661
theorem B3839825 : Blo 1516955 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B2561969 : Blo 1516955 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B3413969 : Blo 1516955 3413969 := bstep (se 2 (by rfl) ⟨1280238, by rfl⟩ : syracuseStep 3413969 = 2560477) B2560477
theorem B3413987 : Blo 1516955 3413987 := bstep (se 1 (by rfl) ⟨2560490, by rfl⟩ : syracuseStep 3413987 = 5120981) B5120981
theorem B5191661 : Blo 1516955 5191661 := bstep (se 3 (by rfl) ⟨973436, by rfl⟩ : syracuseStep 5191661 = 1946873) B1946873
theorem B2881585 : Blo 1516955 2881585 := bstep (se 2 (by rfl) ⟨1080594, by rfl⟩ : syracuseStep 2881585 = 2161189) B2161189
theorem B2562097 : Blo 1516955 2562097 := bstep (se 2 (by rfl) ⟨960786, by rfl⟩ : syracuseStep 2562097 = 1921573) B1921573
theorem B2562131 : Blo 1516955 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B2275457 : Blo 1516955 2275457 := bstep (se 2 (by rfl) ⟨853296, by rfl⟩ : syracuseStep 2275457 = 1706593) B1706593
theorem B2275475 : Blo 1516955 2275475 := bstep (se 1 (by rfl) ⟨1706606, by rfl⟩ : syracuseStep 2275475 = 3413213) B3413213
theorem B2275505 : Blo 1516955 2275505 := bstep (se 2 (by rfl) ⟨853314, by rfl⟩ : syracuseStep 2275505 = 1706629) B1706629
theorem B2275523 : Blo 1516955 2275523 := bstep (se 1 (by rfl) ⟨1706642, by rfl⟩ : syracuseStep 2275523 = 3413285) B3413285
theorem B2562259 : Blo 1516955 2562259 := bstep (se 1 (by rfl) ⟨1921694, by rfl⟩ : syracuseStep 2562259 = 3843389) B3843389
theorem B2275553 : Blo 1516955 2275553 := bstep (se 2 (by rfl) ⟨853332, by rfl⟩ : syracuseStep 2275553 = 1706665) B1706665
theorem B3414257 : Blo 1516955 3414257 := bstep (se 2 (by rfl) ⟨1280346, by rfl⟩ : syracuseStep 3414257 = 2560693) B2560693
theorem B2275571 : Blo 1516955 2275571 := bstep (se 1 (by rfl) ⟨1706678, by rfl⟩ : syracuseStep 2275571 = 3413357) B3413357
theorem B3414275 : Blo 1516955 3414275 := bstep (se 1 (by rfl) ⟨2560706, by rfl⟩ : syracuseStep 3414275 = 5121413) B5121413
theorem B2275601 : Blo 1516955 2275601 := bstep (se 2 (by rfl) ⟨853350, by rfl⟩ : syracuseStep 2275601 = 1706701) B1706701
theorem B2275619 : Blo 1516955 2275619 := bstep (se 1 (by rfl) ⟨1706714, by rfl⟩ : syracuseStep 2275619 = 3413429) B3413429
theorem B2275649 : Blo 1516955 2275649 := bstep (se 2 (by rfl) ⟨853368, by rfl⟩ : syracuseStep 2275649 = 1706737) B1706737
theorem B2275667 : Blo 1516955 2275667 := bstep (se 1 (by rfl) ⟨1706750, by rfl⟩ : syracuseStep 2275667 = 3413501) B3413501
theorem B2275697 : Blo 1516955 2275697 := bstep (se 2 (by rfl) ⟨853386, by rfl⟩ : syracuseStep 2275697 = 1706773) B1706773
theorem B2275715 : Blo 1516955 2275715 := bstep (se 1 (by rfl) ⟨1706786, by rfl⟩ : syracuseStep 2275715 = 3413573) B3413573
theorem B1538435 : Blo 1516955 1538435 := bstep (se 1 (by rfl) ⟨1153826, by rfl⟩ : syracuseStep 1538435 = 2307653) B2307653
theorem B1620371 : Blo 1516955 1620371 := bstep (se 1 (by rfl) ⟨1215278, by rfl⟩ : syracuseStep 1620371 = 2430557) B2430557
theorem B2275745 : Blo 1516955 2275745 := bstep (se 2 (by rfl) ⟨853404, by rfl⟩ : syracuseStep 2275745 = 1706809) B1706809
theorem B2275763 : Blo 1516955 2275763 := bstep (se 1 (by rfl) ⟨1706822, by rfl⟩ : syracuseStep 2275763 = 3413645) B3413645
theorem B2161075 : Blo 1516955 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B6568397 : Blo 1516955 6568397 := bstep (se 3 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 6568397 = 2463149) B2463149
theorem B2275793 : Blo 1516955 2275793 := bstep (se 2 (by rfl) ⟨853422, by rfl⟩ : syracuseStep 2275793 = 1706845) B1706845
theorem B2275811 : Blo 1516955 2275811 := bstep (se 1 (by rfl) ⟨1706858, by rfl⟩ : syracuseStep 2275811 = 3413717) B3413717
theorem B3242467 : Blo 1516955 3242467 := bstep (se 1 (by rfl) ⟨2431850, by rfl⟩ : syracuseStep 3242467 = 4863701) B4863701
theorem B2275841 : Blo 1516955 2275841 := bstep (se 2 (by rfl) ⟨853440, by rfl⟩ : syracuseStep 2275841 = 1706881) B1706881
theorem B3414545 : Blo 1516955 3414545 := bstep (se 2 (by rfl) ⟨1280454, by rfl⟩ : syracuseStep 3414545 = 2560909) B2560909
theorem B2275859 : Blo 1516955 2275859 := bstep (se 1 (by rfl) ⟨1706894, by rfl⟩ : syracuseStep 2275859 = 3413789) B3413789
theorem B3414563 : Blo 1516955 3414563 := bstep (se 1 (by rfl) ⟨2560922, by rfl⟩ : syracuseStep 3414563 = 5121845) B5121845
theorem B2275889 : Blo 1516955 2275889 := bstep (se 2 (by rfl) ⟨853458, by rfl⟩ : syracuseStep 2275889 = 1706917) B1706917
theorem B2275907 : Blo 1516955 2275907 := bstep (se 1 (by rfl) ⟨1706930, by rfl⟩ : syracuseStep 2275907 = 3413861) B3413861
theorem B2275937 : Blo 1516955 2275937 := bstep (se 2 (by rfl) ⟨853476, by rfl⟩ : syracuseStep 2275937 = 1706953) B1706953
theorem B2275955 : Blo 1516955 2275955 := bstep (se 1 (by rfl) ⟨1706966, by rfl⟩ : syracuseStep 2275955 = 3413933) B3413933
theorem B2275985 : Blo 1516955 2275985 := bstep (se 2 (by rfl) ⟨853494, by rfl⟩ : syracuseStep 2275985 = 1706989) B1706989
theorem B2431633 : Blo 1516955 2431633 := bstep (se 2 (by rfl) ⟨911862, by rfl⟩ : syracuseStep 2431633 = 1823725) B1823725
theorem B2276003 : Blo 1516955 2276003 := bstep (se 1 (by rfl) ⟨1707002, by rfl⟩ : syracuseStep 2276003 = 3414005) B3414005
theorem B8641201 : Blo 1516955 8641201 := bstep (se 2 (by rfl) ⟨3240450, by rfl⟩ : syracuseStep 8641201 = 6480901) B6480901
theorem B2276033 : Blo 1516955 2276033 := bstep (se 2 (by rfl) ⟨853512, by rfl⟩ : syracuseStep 2276033 = 1707025) B1707025
theorem B5192387 : Blo 1516955 5192387 := bstep (se 1 (by rfl) ⟨3894290, by rfl⟩ : syracuseStep 5192387 = 7788581) B7788581
theorem B2276051 : Blo 1516955 2276051 := bstep (se 1 (by rfl) ⟨1707038, by rfl⟩ : syracuseStep 2276051 = 3414077) B3414077
theorem B2276081 : Blo 1516955 2276081 := bstep (se 2 (by rfl) ⟨853530, by rfl⟩ : syracuseStep 2276081 = 1707061) B1707061
theorem B2276099 : Blo 1516955 2276099 := bstep (se 1 (by rfl) ⟨1707074, by rfl⟩ : syracuseStep 2276099 = 3414149) B3414149
theorem B2276129 : Blo 1516955 2276129 := bstep (se 2 (by rfl) ⟨853548, by rfl⟩ : syracuseStep 2276129 = 1707097) B1707097
theorem B3840817 : Blo 1516955 3840817 := bstep (se 2 (by rfl) ⟨1440306, by rfl⟩ : syracuseStep 3840817 = 2880613) B2880613
theorem B3414833 : Blo 1516955 3414833 := bstep (se 2 (by rfl) ⟨1280562, by rfl⟩ : syracuseStep 3414833 = 2561125) B2561125
theorem B2276147 : Blo 1516955 2276147 := bstep (se 1 (by rfl) ⟨1707110, by rfl⟩ : syracuseStep 2276147 = 3414221) B3414221
theorem B3414851 : Blo 1516955 3414851 := bstep (se 1 (by rfl) ⟨2561138, by rfl⟩ : syracuseStep 3414851 = 5122277) B5122277
theorem B2276177 : Blo 1516955 2276177 := bstep (se 2 (by rfl) ⟨853566, by rfl⟩ : syracuseStep 2276177 = 1707133) B1707133
theorem B4438883 : Blo 1516955 4438883 := bstep (se 1 (by rfl) ⟨3329162, by rfl⟩ : syracuseStep 4438883 = 6658325) B6658325
theorem B2276195 : Blo 1516955 2276195 := bstep (se 1 (by rfl) ⟨1707146, by rfl⟩ : syracuseStep 2276195 = 3414293) B3414293
theorem B2276225 : Blo 1516955 2276225 := bstep (se 2 (by rfl) ⟨853584, by rfl⟩ : syracuseStep 2276225 = 1707169) B1707169
theorem B2276243 : Blo 1516955 2276243 := bstep (se 1 (by rfl) ⟨1707182, by rfl⟩ : syracuseStep 2276243 = 3414365) B3414365
theorem B2276273 : Blo 1516955 2276273 := bstep (se 2 (by rfl) ⟨853602, by rfl⟩ : syracuseStep 2276273 = 1707205) B1707205
theorem B3242929 : Blo 1516955 3242929 := bstep (se 2 (by rfl) ⟨1216098, by rfl⟩ : syracuseStep 3242929 = 2432197) B2432197
theorem B2276291 : Blo 1516955 2276291 := bstep (se 1 (by rfl) ⟨1707218, by rfl⟩ : syracuseStep 2276291 = 3414437) B3414437
theorem B2276321 : Blo 1516955 2276321 := bstep (se 2 (by rfl) ⟨853620, by rfl⟩ : syracuseStep 2276321 = 1707241) B1707241
theorem B2276339 : Blo 1516955 2276339 := bstep (se 1 (by rfl) ⟨1707254, by rfl⟩ : syracuseStep 2276339 = 3414509) B3414509
theorem B2276369 : Blo 1516955 2276369 := bstep (se 2 (by rfl) ⟨853638, by rfl⟩ : syracuseStep 2276369 = 1707277) B1707277
theorem B2276387 : Blo 1516955 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B2276417 : Blo 1516955 2276417 := bstep (se 2 (by rfl) ⟨853656, by rfl⟩ : syracuseStep 2276417 = 1707313) B1707313
theorem B3841091 : Blo 1516955 3841091 := bstep (se 1 (by rfl) ⟨2880818, by rfl⟩ : syracuseStep 3841091 = 5761637) B5761637
theorem B3415121 : Blo 1516955 3415121 := bstep (se 2 (by rfl) ⟨1280670, by rfl⟩ : syracuseStep 3415121 = 2561341) B2561341
theorem B2882641 : Blo 1516955 2882641 := bstep (se 2 (by rfl) ⟨1080990, by rfl⟩ : syracuseStep 2882641 = 2161981) B2161981
theorem B2276435 : Blo 1516955 2276435 := bstep (se 1 (by rfl) ⟨1707326, by rfl⟩ : syracuseStep 2276435 = 3414653) B3414653
theorem B3415139 : Blo 1516955 3415139 := bstep (se 1 (by rfl) ⟨2561354, by rfl⟩ : syracuseStep 3415139 = 5122709) B5122709
theorem B2276465 : Blo 1516955 2276465 := bstep (se 2 (by rfl) ⟨853674, by rfl⟩ : syracuseStep 2276465 = 1707349) B1707349
theorem B2276483 : Blo 1516955 2276483 := bstep (se 1 (by rfl) ⟨1707362, by rfl⟩ : syracuseStep 2276483 = 3414725) B3414725
theorem B2276513 : Blo 1516955 2276513 := bstep (se 2 (by rfl) ⟨853692, by rfl⟩ : syracuseStep 2276513 = 1707385) B1707385
theorem B2276531 : Blo 1516955 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B2735299 : Blo 1516955 2735299 := bstep (se 1 (by rfl) ⟨2051474, by rfl⟩ : syracuseStep 2735299 = 4102949) B4102949
theorem B10386629 : Blo 1516955 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B2276561 : Blo 1516955 2276561 := bstep (se 2 (by rfl) ⟨853710, by rfl⟩ : syracuseStep 2276561 = 1707421) B1707421
theorem B2276579 : Blo 1516955 2276579 := bstep (se 1 (by rfl) ⟨1707434, by rfl⟩ : syracuseStep 2276579 = 3414869) B3414869
theorem B2276609 : Blo 1516955 2276609 := bstep (se 2 (by rfl) ⟨853728, by rfl⟩ : syracuseStep 2276609 = 1707457) B1707457
theorem B3841283 : Blo 1516955 3841283 := bstep (se 1 (by rfl) ⟨2880962, by rfl⟩ : syracuseStep 3841283 = 5761925) B5761925
theorem B2276627 : Blo 1516955 2276627 := bstep (se 1 (by rfl) ⟨1707470, by rfl⟩ : syracuseStep 2276627 = 3414941) B3414941
theorem B2276657 : Blo 1516955 2276657 := bstep (se 2 (by rfl) ⟨853746, by rfl⟩ : syracuseStep 2276657 = 1707493) B1707493
theorem B2276675 : Blo 1516955 2276675 := bstep (se 1 (by rfl) ⟨1707506, by rfl⟩ : syracuseStep 2276675 = 3415013) B3415013
theorem B2276705 : Blo 1516955 2276705 := bstep (se 2 (by rfl) ⟨853764, by rfl⟩ : syracuseStep 2276705 = 1707529) B1707529
theorem B11525489 : Blo 1516955 11525489 := bstep (se 2 (by rfl) ⟨4322058, by rfl⟩ : syracuseStep 11525489 = 8644117) B8644117
theorem B3415409 : Blo 1516955 3415409 := bstep (se 2 (by rfl) ⟨1280778, by rfl⟩ : syracuseStep 3415409 = 2561557) B2561557
theorem B2276723 : Blo 1516955 2276723 := bstep (se 1 (by rfl) ⟨1707542, by rfl⟩ : syracuseStep 2276723 = 3415085) B3415085
theorem B3415427 : Blo 1516955 3415427 := bstep (se 1 (by rfl) ⟨2561570, by rfl⟩ : syracuseStep 3415427 = 5123141) B5123141
theorem B2276753 : Blo 1516955 2276753 := bstep (se 2 (by rfl) ⟨853782, by rfl⟩ : syracuseStep 2276753 = 1707565) B1707565
theorem B2276771 : Blo 1516955 2276771 := bstep (se 1 (by rfl) ⟨1707578, by rfl⟩ : syracuseStep 2276771 = 3415157) B3415157
theorem B2276801 : Blo 1516955 2276801 := bstep (se 2 (by rfl) ⟨853800, by rfl⟩ : syracuseStep 2276801 = 1707601) B1707601
theorem B2276819 : Blo 1516955 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B2276849 : Blo 1516955 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B2276867 : Blo 1516955 2276867 := bstep (se 1 (by rfl) ⟨1707650, by rfl⟩ : syracuseStep 2276867 = 3415301) B3415301
theorem B1621507 : Blo 1516955 1621507 := bstep (se 1 (by rfl) ⟨1216130, by rfl⟩ : syracuseStep 1621507 = 2432261) B2432261
theorem B2276897 : Blo 1516955 2276897 := bstep (se 2 (by rfl) ⟨853836, by rfl⟩ : syracuseStep 2276897 = 1707673) B1707673
theorem B2276915 : Blo 1516955 2276915 := bstep (se 1 (by rfl) ⟨1707686, by rfl⟩ : syracuseStep 2276915 = 3415373) B3415373
theorem B2276945 : Blo 1516955 2276945 := bstep (se 2 (by rfl) ⟨853854, by rfl⟩ : syracuseStep 2276945 = 1707709) B1707709
theorem B2276963 : Blo 1516955 2276963 := bstep (se 1 (by rfl) ⟨1707722, by rfl⟩ : syracuseStep 2276963 = 3415445) B3415445
theorem B2276993 : Blo 1516955 2276993 := bstep (se 2 (by rfl) ⟨853872, by rfl⟩ : syracuseStep 2276993 = 1707745) B1707745
theorem B3415697 : Blo 1516955 3415697 := bstep (se 2 (by rfl) ⟨1280886, by rfl⟩ : syracuseStep 3415697 = 2561773) B2561773
theorem B2277011 : Blo 1516955 2277011 := bstep (se 1 (by rfl) ⟨1707758, by rfl⟩ : syracuseStep 2277011 = 3415517) B3415517
theorem B3415715 : Blo 1516955 3415715 := bstep (se 1 (by rfl) ⟨2561786, by rfl⟩ : syracuseStep 3415715 = 5123573) B5123573
theorem B2277041 : Blo 1516955 2277041 := bstep (se 2 (by rfl) ⟨853890, by rfl⟩ : syracuseStep 2277041 = 1707781) B1707781
theorem B2277059 : Blo 1516955 2277059 := bstep (se 1 (by rfl) ⟨1707794, by rfl⟩ : syracuseStep 2277059 = 3415589) B3415589
theorem B2277089 : Blo 1516955 2277089 := bstep (se 2 (by rfl) ⟨853908, by rfl⟩ : syracuseStep 2277089 = 1707817) B1707817
theorem B2277107 : Blo 1516955 2277107 := bstep (se 1 (by rfl) ⟨1707830, by rfl⟩ : syracuseStep 2277107 = 3415661) B3415661
theorem B2277137 : Blo 1516955 2277137 := bstep (se 2 (by rfl) ⟨853926, by rfl⟩ : syracuseStep 2277137 = 1707853) B1707853
theorem B2277155 : Blo 1516955 2277155 := bstep (se 1 (by rfl) ⟨1707866, by rfl⟩ : syracuseStep 2277155 = 3415733) B3415733
theorem B5119793 : Blo 1516955 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B2277185 : Blo 1516955 2277185 := bstep (se 2 (by rfl) ⟨853944, by rfl⟩ : syracuseStep 2277185 = 1707889) B1707889
theorem B2277203 : Blo 1516955 2277203 := bstep (se 1 (by rfl) ⟨1707902, by rfl⟩ : syracuseStep 2277203 = 3415805) B3415805
theorem B11091811 : Blo 1516955 11091811 := bstep (se 1 (by rfl) ⟨8318858, by rfl⟩ : syracuseStep 11091811 = 16637717) B16637717
theorem B2277233 : Blo 1516955 2277233 := bstep (se 2 (by rfl) ⟨853962, by rfl⟩ : syracuseStep 2277233 = 1707925) B1707925
theorem B2277251 : Blo 1516955 2277251 := bstep (se 1 (by rfl) ⟨1707938, by rfl⟩ : syracuseStep 2277251 = 3415877) B3415877
theorem B2277281 : Blo 1516955 2277281 := bstep (se 2 (by rfl) ⟨853980, by rfl⟩ : syracuseStep 2277281 = 1707961) B1707961
theorem B3415985 : Blo 1516955 3415985 := bstep (se 2 (by rfl) ⟨1280994, by rfl⟩ : syracuseStep 3415985 = 2561989) B2561989
theorem B2277299 : Blo 1516955 2277299 := bstep (se 1 (by rfl) ⟨1707974, by rfl⟩ : syracuseStep 2277299 = 3415949) B3415949
theorem B3416003 : Blo 1516955 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B2277329 : Blo 1516955 2277329 := bstep (se 2 (by rfl) ⟨853998, by rfl⟩ : syracuseStep 2277329 = 1707997) B1707997
theorem B10936291 : Blo 1516955 10936291 := bstep (se 1 (by rfl) ⟨8202218, by rfl⟩ : syracuseStep 10936291 = 16404437) B16404437
theorem B2277347 : Blo 1516955 2277347 := bstep (se 1 (by rfl) ⟨1708010, by rfl⟩ : syracuseStep 2277347 = 3416021) B3416021
theorem B3416075 : Blo 1516955 3416075 := bstep (se 1 (by rfl) ⟨2562056, by rfl⟩ : syracuseStep 3416075 = 5124113) B5124113
theorem B2277401 : Blo 1516955 2277401 := bstep (se 2 (by rfl) ⟨854025, by rfl⟩ : syracuseStep 2277401 = 1708051) B1708051
theorem B3842113 : Blo 1516955 3842113 := bstep (se 2 (by rfl) ⟨1440792, by rfl⟩ : syracuseStep 3842113 = 2881585) B2881585
theorem B3416129 : Blo 1516955 3416129 := bstep (se 2 (by rfl) ⟨1281048, by rfl⟩ : syracuseStep 3416129 = 2562097) B2562097
theorem B8208449 : Blo 1516955 8208449 := bstep (se 2 (by rfl) ⟨3078168, by rfl⟩ : syracuseStep 8208449 = 6156337) B6156337
theorem B2277515 : Blo 1516955 2277515 := bstep (se 1 (by rfl) ⟨1708136, by rfl⟩ : syracuseStep 2277515 = 3416273) B3416273
theorem B2277527 : Blo 1516955 2277527 := bstep (se 1 (by rfl) ⟨1708145, by rfl⟩ : syracuseStep 2277527 = 3416291) B3416291
theorem B2810009 : Blo 1516955 2810009 := bstep (se 2 (by rfl) ⟨1053753, by rfl⟩ : syracuseStep 2810009 = 2107507) B2107507
theorem B9724121 : Blo 1516955 9724121 := bstep (se 2 (by rfl) ⟨3646545, by rfl⟩ : syracuseStep 9724121 = 7293091) B7293091
theorem B2277593 : Blo 1516955 2277593 := bstep (se 2 (by rfl) ⟨854097, by rfl⟩ : syracuseStep 2277593 = 1708195) B1708195
theorem B5120279 : Blo 1516955 5120279 := bstep (se 1 (by rfl) ⟨3840209, by rfl⟩ : syracuseStep 5120279 = 7680419) B7680419
theorem B3416345 : Blo 1516955 3416345 := bstep (se 2 (by rfl) ⟨1281129, by rfl⟩ : syracuseStep 3416345 = 2562259) B2562259
theorem B3416435 : Blo 1516955 3416435 := bstep (se 1 (by rfl) ⟨2562326, by rfl⟩ : syracuseStep 3416435 = 5124653) B5124653
theorem B3416471 : Blo 1516955 3416471 := bstep (se 1 (by rfl) ⟨2562353, by rfl⟩ : syracuseStep 3416471 = 5124707) B5124707
theorem B16417241 : Blo 1516955 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B9724481 : Blo 1516955 9724481 := bstep (se 2 (by rfl) ⟨3646680, by rfl⟩ : syracuseStep 9724481 = 7293361) B7293361
theorem B8200835 : Blo 1516955 8200835 := bstep (se 1 (by rfl) ⟨6150626, by rfl⟩ : syracuseStep 8200835 = 12301253) B12301253
theorem B3842711 : Blo 1516955 3842711 := bstep (se 1 (by rfl) ⟨2882033, by rfl⟩ : syracuseStep 3842711 = 5764067) B5764067
theorem B11526947 : Blo 1516955 11526947 := bstep (se 1 (by rfl) ⟨8645210, by rfl⟩ : syracuseStep 11526947 = 17290421) B17290421
theorem B5120819 : Blo 1516955 5120819 := bstep (se 1 (by rfl) ⟨3840614, by rfl⟩ : syracuseStep 5120819 = 7681229) B7681229
theorem B6325067 : Blo 1516955 6325067 := bstep (se 1 (by rfl) ⟨4743800, by rfl⟩ : syracuseStep 6325067 = 9487601) B9487601
theorem B3285875 : Blo 1516955 3285875 := bstep (se 1 (by rfl) ⟨2464406, by rfl⟩ : syracuseStep 3285875 = 4928813) B4928813
theorem B5121089 : Blo 1516955 5121089 := bstep (se 2 (by rfl) ⟨1920408, by rfl⟩ : syracuseStep 5121089 = 3840817) B3840817
theorem B6480971 : Blo 1516955 6480971 := bstep (se 1 (by rfl) ⟨4860728, by rfl⟩ : syracuseStep 6480971 = 9721457) B9721457
theorem B9725021 : Blo 1516955 9725021 := bstep (se 3 (by rfl) ⟨1823441, by rfl⟩ : syracuseStep 9725021 = 3646883) B3646883
theorem B5760179 : Blo 1516955 5760179 := bstep (se 1 (by rfl) ⟨4320134, by rfl⟩ : syracuseStep 5760179 = 8640269) B8640269
theorem B5760193 : Blo 1516955 5760193 := bstep (se 2 (by rfl) ⟨2160072, by rfl⟩ : syracuseStep 5760193 = 4320145) B4320145
theorem B7685441 : Blo 1516955 7685441 := bstep (se 2 (by rfl) ⟨2882040, by rfl⟩ : syracuseStep 7685441 = 5764081) B5764081
theorem B1516971 : Blo 1516955 1516971 := bstep (se 1 (by rfl) ⟨1137728, by rfl⟩ : syracuseStep 1516971 = 2275457) B2275457
theorem B1516983 : Blo 1516955 1516983 := bstep (se 1 (by rfl) ⟨1137737, by rfl⟩ : syracuseStep 1516983 = 2275475) B2275475
theorem B3843521 : Blo 1516955 3843521 := bstep (se 2 (by rfl) ⟨1441320, by rfl⟩ : syracuseStep 3843521 = 2882641) B2882641
theorem B1517003 : Blo 1516955 1517003 := bstep (se 1 (by rfl) ⟨1137752, by rfl⟩ : syracuseStep 1517003 = 2275505) B2275505
theorem B1517015 : Blo 1516955 1517015 := bstep (se 1 (by rfl) ⟨1137761, by rfl⟩ : syracuseStep 1517015 = 2275523) B2275523
theorem B1517035 : Blo 1516955 1517035 := bstep (se 1 (by rfl) ⟨1137776, by rfl⟩ : syracuseStep 1517035 = 2275553) B2275553
theorem B1517047 : Blo 1516955 1517047 := bstep (se 1 (by rfl) ⟨1137785, by rfl⟩ : syracuseStep 1517047 = 2275571) B2275571
theorem B1517067 : Blo 1516955 1517067 := bstep (se 1 (by rfl) ⟨1137800, by rfl⟩ : syracuseStep 1517067 = 2275601) B2275601
theorem B1517079 : Blo 1516955 1517079 := bstep (se 1 (by rfl) ⟨1137809, by rfl⟩ : syracuseStep 1517079 = 2275619) B2275619
theorem B1517099 : Blo 1516955 1517099 := bstep (se 1 (by rfl) ⟨1137824, by rfl⟩ : syracuseStep 1517099 = 2275649) B2275649
theorem B1517111 : Blo 1516955 1517111 := bstep (se 1 (by rfl) ⟨1137833, by rfl⟩ : syracuseStep 1517111 = 2275667) B2275667
theorem B1517131 : Blo 1516955 1517131 := bstep (se 1 (by rfl) ⟨1137848, by rfl⟩ : syracuseStep 1517131 = 2275697) B2275697
theorem B1517143 : Blo 1516955 1517143 := bstep (se 1 (by rfl) ⟨1137857, by rfl⟩ : syracuseStep 1517143 = 2275715) B2275715
theorem B5121629 : Blo 1516955 5121629 := bstep (se 3 (by rfl) ⟨960305, by rfl⟩ : syracuseStep 5121629 = 1920611) B1920611
theorem B1517163 : Blo 1516955 1517163 := bstep (se 1 (by rfl) ⟨1137872, by rfl⟩ : syracuseStep 1517163 = 2275745) B2275745
theorem B1517175 : Blo 1516955 1517175 := bstep (se 1 (by rfl) ⟨1137881, by rfl⟩ : syracuseStep 1517175 = 2275763) B2275763
theorem B1517195 : Blo 1516955 1517195 := bstep (se 1 (by rfl) ⟨1137896, by rfl⟩ : syracuseStep 1517195 = 2275793) B2275793
theorem B1517207 : Blo 1516955 1517207 := bstep (se 1 (by rfl) ⟨1137905, by rfl⟩ : syracuseStep 1517207 = 2275811) B2275811
theorem B1517227 : Blo 1516955 1517227 := bstep (se 1 (by rfl) ⟨1137920, by rfl⟩ : syracuseStep 1517227 = 2275841) B2275841
theorem B1517239 : Blo 1516955 1517239 := bstep (se 1 (by rfl) ⟨1137929, by rfl⟩ : syracuseStep 1517239 = 2275859) B2275859
theorem B1517259 : Blo 1516955 1517259 := bstep (se 1 (by rfl) ⟨1137944, by rfl⟩ : syracuseStep 1517259 = 2275889) B2275889
theorem B1517271 : Blo 1516955 1517271 := bstep (se 1 (by rfl) ⟨1137953, by rfl⟩ : syracuseStep 1517271 = 2275907) B2275907
theorem B1517291 : Blo 1516955 1517291 := bstep (se 1 (by rfl) ⟨1137968, by rfl⟩ : syracuseStep 1517291 = 2275937) B2275937
theorem B1517303 : Blo 1516955 1517303 := bstep (se 1 (by rfl) ⟨1137977, by rfl⟩ : syracuseStep 1517303 = 2275955) B2275955
theorem B1517323 : Blo 1516955 1517323 := bstep (se 1 (by rfl) ⟨1137992, by rfl⟩ : syracuseStep 1517323 = 2275985) B2275985
theorem B1517335 : Blo 1516955 1517335 := bstep (se 1 (by rfl) ⟨1138001, by rfl⟩ : syracuseStep 1517335 = 2276003) B2276003
theorem B1517355 : Blo 1516955 1517355 := bstep (se 1 (by rfl) ⟨1138016, by rfl⟩ : syracuseStep 1517355 = 2276033) B2276033
theorem B1517367 : Blo 1516955 1517367 := bstep (se 1 (by rfl) ⟨1138025, by rfl⟩ : syracuseStep 1517367 = 2276051) B2276051
theorem B1517387 : Blo 1516955 1517387 := bstep (se 1 (by rfl) ⟨1138040, by rfl⟩ : syracuseStep 1517387 = 2276081) B2276081
theorem B1517399 : Blo 1516955 1517399 := bstep (se 1 (by rfl) ⟨1138049, by rfl⟩ : syracuseStep 1517399 = 2276099) B2276099
theorem B1517419 : Blo 1516955 1517419 := bstep (se 1 (by rfl) ⟨1138064, by rfl⟩ : syracuseStep 1517419 = 2276129) B2276129
theorem B1517431 : Blo 1516955 1517431 := bstep (se 1 (by rfl) ⟨1138073, by rfl⟩ : syracuseStep 1517431 = 2276147) B2276147
theorem B1517451 : Blo 1516955 1517451 := bstep (se 1 (by rfl) ⟨1138088, by rfl⟩ : syracuseStep 1517451 = 2276177) B2276177
theorem B2959255 : Blo 1516955 2959255 := bstep (se 1 (by rfl) ⟨2219441, by rfl⟩ : syracuseStep 2959255 = 4438883) B4438883
theorem B1517463 : Blo 1516955 1517463 := bstep (se 1 (by rfl) ⟨1138097, by rfl⟩ : syracuseStep 1517463 = 2276195) B2276195
theorem B1517483 : Blo 1516955 1517483 := bstep (se 1 (by rfl) ⟨1138112, by rfl⟩ : syracuseStep 1517483 = 2276225) B2276225
theorem B1517495 : Blo 1516955 1517495 := bstep (se 1 (by rfl) ⟨1138121, by rfl⟩ : syracuseStep 1517495 = 2276243) B2276243
theorem B1517515 : Blo 1516955 1517515 := bstep (se 1 (by rfl) ⟨1138136, by rfl⟩ : syracuseStep 1517515 = 2276273) B2276273
theorem B1517527 : Blo 1516955 1517527 := bstep (se 1 (by rfl) ⟨1138145, by rfl⟩ : syracuseStep 1517527 = 2276291) B2276291
theorem B1517547 : Blo 1516955 1517547 := bstep (se 1 (by rfl) ⟨1138160, by rfl⟩ : syracuseStep 1517547 = 2276321) B2276321
theorem B1517559 : Blo 1516955 1517559 := bstep (se 1 (by rfl) ⟨1138169, by rfl⟩ : syracuseStep 1517559 = 2276339) B2276339
theorem B1517579 : Blo 1516955 1517579 := bstep (se 1 (by rfl) ⟨1138184, by rfl⟩ : syracuseStep 1517579 = 2276369) B2276369
theorem B1517591 : Blo 1516955 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B1517611 : Blo 1516955 1517611 := bstep (se 1 (by rfl) ⟨1138208, by rfl⟩ : syracuseStep 1517611 = 2276417) B2276417
theorem B1517623 : Blo 1516955 1517623 := bstep (se 1 (by rfl) ⟨1138217, by rfl⟩ : syracuseStep 1517623 = 2276435) B2276435
theorem B1517643 : Blo 1516955 1517643 := bstep (se 1 (by rfl) ⟨1138232, by rfl⟩ : syracuseStep 1517643 = 2276465) B2276465
theorem B1517655 : Blo 1516955 1517655 := bstep (se 1 (by rfl) ⟨1138241, by rfl⟩ : syracuseStep 1517655 = 2276483) B2276483
theorem B1517675 : Blo 1516955 1517675 := bstep (se 1 (by rfl) ⟨1138256, by rfl⟩ : syracuseStep 1517675 = 2276513) B2276513
theorem B1517687 : Blo 1516955 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B6924419 : Blo 1516955 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B2771083 : Blo 1516955 2771083 := bstep (se 1 (by rfl) ⟨2078312, by rfl⟩ : syracuseStep 2771083 = 4156625) B4156625
theorem B1517707 : Blo 1516955 1517707 := bstep (se 1 (by rfl) ⟨1138280, by rfl⟩ : syracuseStep 1517707 = 2276561) B2276561
theorem B1517719 : Blo 1516955 1517719 := bstep (se 1 (by rfl) ⟨1138289, by rfl⟩ : syracuseStep 1517719 = 2276579) B2276579
theorem B1517739 : Blo 1516955 1517739 := bstep (se 1 (by rfl) ⟨1138304, by rfl⟩ : syracuseStep 1517739 = 2276609) B2276609
theorem B1517751 : Blo 1516955 1517751 := bstep (se 1 (by rfl) ⟨1138313, by rfl⟩ : syracuseStep 1517751 = 2276627) B2276627
theorem B1517771 : Blo 1516955 1517771 := bstep (se 1 (by rfl) ⟨1138328, by rfl⟩ : syracuseStep 1517771 = 2276657) B2276657
theorem B1517783 : Blo 1516955 1517783 := bstep (se 1 (by rfl) ⟨1138337, by rfl⟩ : syracuseStep 1517783 = 2276675) B2276675
theorem B1517803 : Blo 1516955 1517803 := bstep (se 1 (by rfl) ⟨1138352, by rfl⟩ : syracuseStep 1517803 = 2276705) B2276705
theorem B1517815 : Blo 1516955 1517815 := bstep (se 1 (by rfl) ⟨1138361, by rfl⟩ : syracuseStep 1517815 = 2276723) B2276723
theorem B1517835 : Blo 1516955 1517835 := bstep (se 1 (by rfl) ⟨1138376, by rfl⟩ : syracuseStep 1517835 = 2276753) B2276753
theorem B1517847 : Blo 1516955 1517847 := bstep (se 1 (by rfl) ⟨1138385, by rfl⟩ : syracuseStep 1517847 = 2276771) B2276771
theorem B1517867 : Blo 1516955 1517867 := bstep (se 1 (by rfl) ⟨1138400, by rfl⟩ : syracuseStep 1517867 = 2276801) B2276801
theorem B1517879 : Blo 1516955 1517879 := bstep (se 1 (by rfl) ⟨1138409, by rfl⟩ : syracuseStep 1517879 = 2276819) B2276819
theorem B1517899 : Blo 1516955 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B1517911 : Blo 1516955 1517911 := bstep (se 1 (by rfl) ⟨1138433, by rfl⟩ : syracuseStep 1517911 = 2276867) B2276867
theorem B1517931 : Blo 1516955 1517931 := bstep (se 1 (by rfl) ⟨1138448, by rfl⟩ : syracuseStep 1517931 = 2276897) B2276897
theorem B1517943 : Blo 1516955 1517943 := bstep (se 1 (by rfl) ⟨1138457, by rfl⟩ : syracuseStep 1517943 = 2276915) B2276915
theorem B1517963 : Blo 1516955 1517963 := bstep (se 1 (by rfl) ⟨1138472, by rfl⟩ : syracuseStep 1517963 = 2276945) B2276945
theorem B1517975 : Blo 1516955 1517975 := bstep (se 1 (by rfl) ⟨1138481, by rfl⟩ : syracuseStep 1517975 = 2276963) B2276963
theorem B1517995 : Blo 1516955 1517995 := bstep (se 1 (by rfl) ⟨1138496, by rfl⟩ : syracuseStep 1517995 = 2276993) B2276993
theorem B1518007 : Blo 1516955 1518007 := bstep (se 1 (by rfl) ⟨1138505, by rfl⟩ : syracuseStep 1518007 = 2277011) B2277011
theorem B1518027 : Blo 1516955 1518027 := bstep (se 1 (by rfl) ⟨1138520, by rfl⟩ : syracuseStep 1518027 = 2277041) B2277041
theorem B1518039 : Blo 1516955 1518039 := bstep (se 1 (by rfl) ⟨1138529, by rfl⟩ : syracuseStep 1518039 = 2277059) B2277059
theorem B14789081 : Blo 1516955 14789081 := bstep (se 2 (by rfl) ⟨5545905, by rfl⟩ : syracuseStep 14789081 = 11091811) B11091811
theorem B1518059 : Blo 1516955 1518059 := bstep (se 1 (by rfl) ⟨1138544, by rfl⟩ : syracuseStep 1518059 = 2277089) B2277089
theorem B1518071 : Blo 1516955 1518071 := bstep (se 1 (by rfl) ⟨1138553, by rfl⟩ : syracuseStep 1518071 = 2277107) B2277107
theorem B1518091 : Blo 1516955 1518091 := bstep (se 1 (by rfl) ⟨1138568, by rfl⟩ : syracuseStep 1518091 = 2277137) B2277137
theorem B1518103 : Blo 1516955 1518103 := bstep (se 1 (by rfl) ⟨1138577, by rfl⟩ : syracuseStep 1518103 = 2277155) B2277155
theorem B1518123 : Blo 1516955 1518123 := bstep (se 1 (by rfl) ⟨1138592, by rfl⟩ : syracuseStep 1518123 = 2277185) B2277185
theorem B1518135 : Blo 1516955 1518135 := bstep (se 1 (by rfl) ⟨1138601, by rfl⟩ : syracuseStep 1518135 = 2277203) B2277203
theorem B1518155 : Blo 1516955 1518155 := bstep (se 1 (by rfl) ⟨1138616, by rfl⟩ : syracuseStep 1518155 = 2277233) B2277233
theorem B1518167 : Blo 1516955 1518167 := bstep (se 1 (by rfl) ⟨1138625, by rfl⟩ : syracuseStep 1518167 = 2277251) B2277251
theorem B1518187 : Blo 1516955 1518187 := bstep (se 1 (by rfl) ⟨1138640, by rfl⟩ : syracuseStep 1518187 = 2277281) B2277281
theorem B1518199 : Blo 1516955 1518199 := bstep (se 1 (by rfl) ⟨1138649, by rfl⟩ : syracuseStep 1518199 = 2277299) B2277299
theorem B1518219 : Blo 1516955 1518219 := bstep (se 1 (by rfl) ⟨1138664, by rfl⟩ : syracuseStep 1518219 = 2277329) B2277329
theorem B1706647 : Blo 1516955 1706647 := bstep (se 1 (by rfl) ⟨1279985, by rfl⟩ : syracuseStep 1706647 = 2559971) B2559971
theorem B1518231 : Blo 1516955 1518231 := bstep (se 1 (by rfl) ⟨1138673, by rfl⟩ : syracuseStep 1518231 = 2277347) B2277347
theorem B1518251 : Blo 1516955 1518251 := bstep (se 1 (by rfl) ⟨1138688, by rfl⟩ : syracuseStep 1518251 = 2277377) B2277377
theorem B1518263 : Blo 1516955 1518263 := bstep (se 1 (by rfl) ⟨1138697, by rfl⟩ : syracuseStep 1518263 = 2277395) B2277395
theorem B5122763 : Blo 1516955 5122763 := bstep (se 1 (by rfl) ⟨3842072, by rfl⟩ : syracuseStep 5122763 = 7684145) B7684145
theorem B1518283 : Blo 1516955 1518283 := bstep (se 1 (by rfl) ⟨1138712, by rfl⟩ : syracuseStep 1518283 = 2277425) B2277425
theorem B1731287 : Blo 1516955 1731287 := bstep (se 1 (by rfl) ⟨1298465, by rfl⟩ : syracuseStep 1731287 = 2596931) B2596931
theorem B1518295 : Blo 1516955 1518295 := bstep (se 1 (by rfl) ⟨1138721, by rfl⟩ : syracuseStep 1518295 = 2277443) B2277443
theorem B1518315 : Blo 1516955 1518315 := bstep (se 1 (by rfl) ⟨1138736, by rfl⟩ : syracuseStep 1518315 = 2277473) B2277473
theorem B1518327 : Blo 1516955 1518327 := bstep (se 1 (by rfl) ⟨1138745, by rfl⟩ : syracuseStep 1518327 = 2277491) B2277491
theorem B1518347 : Blo 1516955 1518347 := bstep (se 1 (by rfl) ⟨1138760, by rfl⟩ : syracuseStep 1518347 = 2277521) B2277521
theorem B8645393 : Blo 1516955 8645393 := bstep (se 2 (by rfl) ⟨3242022, by rfl⟩ : syracuseStep 8645393 = 6484045) B6484045
theorem B1518359 : Blo 1516955 1518359 := bstep (se 1 (by rfl) ⟨1138769, by rfl⟩ : syracuseStep 1518359 = 2277539) B2277539
theorem B1518379 : Blo 1516955 1518379 := bstep (se 1 (by rfl) ⟨1138784, by rfl⟩ : syracuseStep 1518379 = 2277569) B2277569
theorem B1518391 : Blo 1516955 1518391 := bstep (se 1 (by rfl) ⟨1138793, by rfl⟩ : syracuseStep 1518391 = 2277587) B2277587
theorem B1706827 : Blo 1516955 1706827 := bstep (se 1 (by rfl) ⟨1280120, by rfl⟩ : syracuseStep 1706827 = 2560241) B2560241
theorem B1518411 : Blo 1516955 1518411 := bstep (se 1 (by rfl) ⟨1138808, by rfl⟩ : syracuseStep 1518411 = 2277617) B2277617
theorem B1518423 : Blo 1516955 1518423 := bstep (se 1 (by rfl) ⟨1138817, by rfl⟩ : syracuseStep 1518423 = 2277635) B2277635
theorem B1518443 : Blo 1516955 1518443 := bstep (se 1 (by rfl) ⟨1138832, by rfl⟩ : syracuseStep 1518443 = 2277665) B2277665
theorem B1518455 : Blo 1516955 1518455 := bstep (se 1 (by rfl) ⟨1138841, by rfl⟩ : syracuseStep 1518455 = 2277683) B2277683
theorem B9227159 : Blo 1516955 9227159 := bstep (se 1 (by rfl) ⟨6920369, by rfl⟩ : syracuseStep 9227159 = 13840739) B13840739
theorem B1706935 : Blo 1516955 1706935 := bstep (se 1 (by rfl) ⟨1280201, by rfl⟩ : syracuseStep 1706935 = 2560403) B2560403
theorem B5123033 : Blo 1516955 5123033 := bstep (se 2 (by rfl) ⟨1921137, by rfl⟩ : syracuseStep 5123033 = 3842275) B3842275
theorem B5762123 : Blo 1516955 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B5762137 : Blo 1516955 5762137 := bstep (se 2 (by rfl) ⟨2160801, by rfl⟩ : syracuseStep 5762137 = 4321603) B4321603
theorem B1707115 : Blo 1516955 1707115 := bstep (se 1 (by rfl) ⟨1280336, by rfl⟩ : syracuseStep 1707115 = 2560673) B2560673
theorem B1707223 : Blo 1516955 1707223 := bstep (se 1 (by rfl) ⟨1280417, by rfl⟩ : syracuseStep 1707223 = 2560835) B2560835
theorem B8645849 : Blo 1516955 8645849 := bstep (se 2 (by rfl) ⟨3242193, by rfl⟩ : syracuseStep 8645849 = 6484387) B6484387
theorem B7294283 : Blo 1516955 7294283 := bstep (se 1 (by rfl) ⟨5470712, by rfl⟩ : syracuseStep 7294283 = 10941425) B10941425
theorem B12971339 : Blo 1516955 12971339 := bstep (se 1 (by rfl) ⟨9728504, by rfl⟩ : syracuseStep 12971339 = 19457009) B19457009
theorem B1920343 : Blo 1516955 1920343 := bstep (se 1 (by rfl) ⟨1440257, by rfl⟩ : syracuseStep 1920343 = 2880515) B2880515
theorem B6925661 : Blo 1516955 6925661 := bstep (se 3 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 6925661 = 2597123) B2597123
theorem B1707403 : Blo 1516955 1707403 := bstep (se 1 (by rfl) ⟨1280552, by rfl⟩ : syracuseStep 1707403 = 2561105) B2561105
theorem B4320715 : Blo 1516955 4320715 := bstep (se 1 (by rfl) ⟨3240536, by rfl⟩ : syracuseStep 4320715 = 6481073) B6481073
theorem B1707511 : Blo 1516955 1707511 := bstep (se 1 (by rfl) ⟨1280633, by rfl⟩ : syracuseStep 1707511 = 2561267) B2561267
theorem B11521601 : Blo 1516955 11521601 := bstep (se 2 (by rfl) ⟨4320600, by rfl⟩ : syracuseStep 11521601 = 8641201) B8641201
theorem B2051659 : Blo 1516955 2051659 := bstep (se 1 (by rfl) ⟨1538744, by rfl⟩ : syracuseStep 2051659 = 3077489) B3077489
theorem B6155851 : Blo 1516955 6155851 := bstep (se 1 (by rfl) ⟨4616888, by rfl⟩ : syracuseStep 6155851 = 9233777) B9233777
theorem B7786115 : Blo 1516955 7786115 := bstep (se 1 (by rfl) ⟨5839586, by rfl⟩ : syracuseStep 7786115 = 11679173) B11679173
theorem B5123735 : Blo 1516955 5123735 := bstep (se 1 (by rfl) ⟨3842801, by rfl⟩ : syracuseStep 5123735 = 7685603) B7685603
theorem B1707691 : Blo 1516955 1707691 := bstep (se 1 (by rfl) ⟨1280768, by rfl⟩ : syracuseStep 1707691 = 2561537) B2561537
theorem B6483635 : Blo 1516955 6483635 := bstep (se 1 (by rfl) ⟨4862726, by rfl⟩ : syracuseStep 6483635 = 9725453) B9725453
theorem B3460823 : Blo 1516955 3460823 := bstep (se 1 (by rfl) ⟨2595617, by rfl⟩ : syracuseStep 3460823 = 5191235) B5191235
theorem B4320989 : Blo 1516955 4320989 := bstep (se 3 (by rfl) ⟨810185, by rfl⟩ : syracuseStep 4320989 = 1620371) B1620371
theorem B1707799 : Blo 1516955 1707799 := bstep (se 1 (by rfl) ⟨1280849, by rfl⟩ : syracuseStep 1707799 = 2561699) B2561699
theorem B246271843 : Blo 1516955 246271843 := bstep (se 1 (by rfl) ⟨184703882, by rfl⟩ : syracuseStep 246271843 = 369407765) B369407765
theorem B2559883 : Blo 1516955 2559883 := bstep (se 1 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 2559883 = 3839825) B3839825
theorem B1707979 : Blo 1516955 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B5763095 : Blo 1516955 5763095 := bstep (se 1 (by rfl) ⟨4322321, by rfl⟩ : syracuseStep 5763095 = 8644643) B8644643
theorem B2560025 : Blo 1516955 2560025 := bstep (se 2 (by rfl) ⟨960009, by rfl⟩ : syracuseStep 2560025 = 1920019) B1920019
theorem B1708087 : Blo 1516955 1708087 := bstep (se 1 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 1708087 = 2562131) B2562131
theorem B23375947 : Blo 1516955 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B2560153 : Blo 1516955 2560153 := bstep (se 2 (by rfl) ⟨960057, by rfl⟩ : syracuseStep 2560153 = 1920115) B1920115
theorem B5124275 : Blo 1516955 5124275 := bstep (se 1 (by rfl) ⟨3843206, by rfl⟩ : syracuseStep 5124275 = 7686413) B7686413
theorem B4378931 : Blo 1516955 4378931 := bstep (se 1 (by rfl) ⟨3284198, by rfl⟩ : syracuseStep 4378931 = 6568397) B6568397
theorem B5468491 : Blo 1516955 5468491 := bstep (se 1 (by rfl) ⟨4101368, by rfl⟩ : syracuseStep 5468491 = 8202737) B8202737
theorem B5124545 : Blo 1516955 5124545 := bstep (se 2 (by rfl) ⟨1921704, by rfl⟩ : syracuseStep 5124545 = 3843409) B3843409
theorem B3461591 : Blo 1516955 3461591 := bstep (se 1 (by rfl) ⟨2596193, by rfl⟩ : syracuseStep 3461591 = 5192387) B5192387
theorem B2560727 : Blo 1516955 2560727 := bstep (se 1 (by rfl) ⟨1920545, by rfl⟩ : syracuseStep 2560727 = 3841091) B3841091
theorem B2560855 : Blo 1516955 2560855 := bstep (se 1 (by rfl) ⟨1920641, by rfl⟩ : syracuseStep 2560855 = 3841283) B3841283
theorem B3240947 : Blo 1516955 3240947 := bstep (se 1 (by rfl) ⟨2430710, by rfl⟩ : syracuseStep 3240947 = 4861421) B4861421
theorem B6485123 : Blo 1516955 6485123 := bstep (se 1 (by rfl) ⟨4863842, by rfl⟩ : syracuseStep 6485123 = 9727685) B9727685
theorem B3413195 : Blo 1516955 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B3413249 : Blo 1516955 3413249 := bstep (se 2 (by rfl) ⟨1279968, by rfl⟩ : syracuseStep 3413249 = 2559937) B2559937
theorem B5764355 : Blo 1516955 5764355 := bstep (se 1 (by rfl) ⟨4323266, by rfl⟩ : syracuseStep 5764355 = 8646533) B8646533
theorem B2159959 : Blo 1516955 2159959 := bstep (se 1 (by rfl) ⟨1619969, by rfl⟩ : syracuseStep 2159959 = 3239939) B3239939
theorem B2880947 : Blo 1516955 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B2561483 : Blo 1516955 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B3413465 : Blo 1516955 3413465 := bstep (se 2 (by rfl) ⟨1280049, by rfl⟩ : syracuseStep 3413465 = 2560099) B2560099
theorem B11523545 : Blo 1516955 11523545 := bstep (se 2 (by rfl) ⟨4321329, by rfl⟩ : syracuseStep 11523545 = 8642659) B8642659
theorem B8640017 : Blo 1516955 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B7681553 : Blo 1516955 7681553 := bstep (se 2 (by rfl) ⟨2880582, by rfl⟩ : syracuseStep 7681553 = 5761165) B5761165
theorem B3413555 : Blo 1516955 3413555 := bstep (se 1 (by rfl) ⟨2560166, by rfl⟩ : syracuseStep 3413555 = 5120333) B5120333
theorem B2881099 : Blo 1516955 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B2561611 : Blo 1516955 2561611 := bstep (se 1 (by rfl) ⟨1921208, by rfl⟩ : syracuseStep 2561611 = 3842417) B3842417
theorem B3413591 : Blo 1516955 3413591 := bstep (se 1 (by rfl) ⟨2560193, by rfl⟩ : syracuseStep 3413591 = 5120387) B5120387
theorem B7681715 : Blo 1516955 7681715 := bstep (se 1 (by rfl) ⟨5761286, by rfl⟩ : syracuseStep 7681715 = 11522573) B11522573
theorem B2307799 : Blo 1516955 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B2561753 : Blo 1516955 2561753 := bstep (se 2 (by rfl) ⟨960657, by rfl⟩ : syracuseStep 2561753 = 1921315) B1921315
theorem B3413771 : Blo 1516955 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B4159255 : Blo 1516955 4159255 := bstep (se 1 (by rfl) ⟨3119441, by rfl⟩ : syracuseStep 4159255 = 6238883) B6238883
theorem B3839795 : Blo 1516955 3839795 := bstep (se 1 (by rfl) ⟨2879846, by rfl⟩ : syracuseStep 3839795 = 5759693) B5759693
theorem B3413825 : Blo 1516955 3413825 := bstep (se 2 (by rfl) ⟨1280184, by rfl⟩ : syracuseStep 3413825 = 2560369) B2560369
theorem B2561881 : Blo 1516955 2561881 := bstep (se 2 (by rfl) ⟨960705, by rfl⟩ : syracuseStep 2561881 = 1921411) B1921411
theorem B4929373 : Blo 1516955 4929373 := bstep (se 3 (by rfl) ⟨924257, by rfl⟩ : syracuseStep 4929373 = 1848515) B1848515
theorem B2160523 : Blo 1516955 2160523 := bstep (se 1 (by rfl) ⟨1620392, by rfl⟩ : syracuseStep 2160523 = 3240785) B3240785
theorem B2881433 : Blo 1516955 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B3078103 : Blo 1516955 3078103 := bstep (se 1 (by rfl) ⟨2308577, by rfl⟩ : syracuseStep 3078103 = 4617155) B4617155
theorem B4323289 : Blo 1516955 4323289 := bstep (se 2 (by rfl) ⟨1621233, by rfl⟩ : syracuseStep 4323289 = 3242467) B3242467
theorem B2734067 : Blo 1516955 2734067 := bstep (se 1 (by rfl) ⟨2050550, by rfl⟩ : syracuseStep 2734067 = 4101101) B4101101
theorem B3414041 : Blo 1516955 3414041 := bstep (se 2 (by rfl) ⟨1280265, by rfl⟩ : syracuseStep 3414041 = 2560531) B2560531
theorem B5470253 : Blo 1516955 5470253 := bstep (se 3 (by rfl) ⟨1025672, by rfl⟩ : syracuseStep 5470253 = 2051345) B2051345
theorem B3414131 : Blo 1516955 3414131 := bstep (se 1 (by rfl) ⟨2560598, by rfl⟩ : syracuseStep 3414131 = 5121197) B5121197
theorem B1620119 : Blo 1516955 1620119 := bstep (se 1 (by rfl) ⟨1215089, by rfl⟩ : syracuseStep 1620119 = 2430179) B2430179
theorem B3414167 : Blo 1516955 3414167 := bstep (se 1 (by rfl) ⟨2560625, by rfl⟩ : syracuseStep 3414167 = 5121251) B5121251
theorem B2275481 : Blo 1516955 2275481 := bstep (se 2 (by rfl) ⟨853305, by rfl⟩ : syracuseStep 2275481 = 1706611) B1706611
theorem B4864151 : Blo 1516955 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B3242177 : Blo 1516955 3242177 := bstep (se 2 (by rfl) ⟨1215816, by rfl⟩ : syracuseStep 3242177 = 2431633) B2431633
theorem B27007181 : Blo 1516955 27007181 := bstep (se 3 (by rfl) ⟨5063846, by rfl⟩ : syracuseStep 27007181 = 10127693) B10127693
theorem B2275595 : Blo 1516955 2275595 := bstep (se 1 (by rfl) ⟨1706696, by rfl⟩ : syracuseStep 2275595 = 3413393) B3413393
theorem B2275607 : Blo 1516955 2275607 := bstep (se 1 (by rfl) ⟨1706705, by rfl⟩ : syracuseStep 2275607 = 3413411) B3413411
theorem B1538347 : Blo 1516955 1538347 := bstep (se 1 (by rfl) ⟨1153760, by rfl⟩ : syracuseStep 1538347 = 2307521) B2307521
theorem B3840331 : Blo 1516955 3840331 := bstep (se 1 (by rfl) ⟨2880248, by rfl⟩ : syracuseStep 3840331 = 5760497) B5760497
theorem B3414347 : Blo 1516955 3414347 := bstep (se 1 (by rfl) ⟨2560760, by rfl⟩ : syracuseStep 3414347 = 5121521) B5121521
theorem B2275673 : Blo 1516955 2275673 := bstep (se 2 (by rfl) ⟨853377, by rfl⟩ : syracuseStep 2275673 = 1706755) B1706755
theorem B5192029 : Blo 1516955 5192029 := bstep (se 3 (by rfl) ⟨973505, by rfl⟩ : syracuseStep 5192029 = 1947011) B1947011
theorem B4102493 : Blo 1516955 4102493 := bstep (se 3 (by rfl) ⟨769217, by rfl⟩ : syracuseStep 4102493 = 1538435) B1538435
theorem B14588261 : Blo 1516955 14588261 := bstep (se 4 (by rfl) ⟨1367649, by rfl⟩ : syracuseStep 14588261 = 2735299) B2735299
theorem B3414401 : Blo 1516955 3414401 := bstep (se 2 (by rfl) ⟨1280400, by rfl⟩ : syracuseStep 3414401 = 2560801) B2560801
theorem B2308505 : Blo 1516955 2308505 := bstep (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) B1731379
theorem B2275787 : Blo 1516955 2275787 := bstep (se 1 (by rfl) ⟨1706840, by rfl⟩ : syracuseStep 2275787 = 3413681) B3413681
theorem B2275799 : Blo 1516955 2275799 := bstep (se 1 (by rfl) ⟨1706849, by rfl⟩ : syracuseStep 2275799 = 3413699) B3413699
theorem B3840473 : Blo 1516955 3840473 := bstep (se 2 (by rfl) ⟨1440177, by rfl⟩ : syracuseStep 3840473 = 2880355) B2880355
theorem B2882071 : Blo 1516955 2882071 := bstep (se 1 (by rfl) ⟨2161553, by rfl⟩ : syracuseStep 2882071 = 4323107) B4323107
theorem B2275865 : Blo 1516955 2275865 := bstep (se 2 (by rfl) ⟨853449, by rfl⟩ : syracuseStep 2275865 = 1706899) B1706899
theorem B4323905 : Blo 1516955 4323905 := bstep (se 2 (by rfl) ⟨1621464, by rfl⟩ : syracuseStep 4323905 = 3242929) B3242929
theorem B3414617 : Blo 1516955 3414617 := bstep (se 2 (by rfl) ⟨1280481, by rfl⟩ : syracuseStep 3414617 = 2560963) B2560963
theorem B2275979 : Blo 1516955 2275979 := bstep (se 1 (by rfl) ⟨1706984, by rfl⟩ : syracuseStep 2275979 = 3413969) B3413969
theorem B2275991 : Blo 1516955 2275991 := bstep (se 1 (by rfl) ⟨1706993, by rfl⟩ : syracuseStep 2275991 = 3413987) B3413987
theorem B3414707 : Blo 1516955 3414707 := bstep (se 1 (by rfl) ⟨2561030, by rfl⟩ : syracuseStep 3414707 = 5122061) B5122061
theorem B3414743 : Blo 1516955 3414743 := bstep (se 1 (by rfl) ⟨2561057, by rfl⟩ : syracuseStep 3414743 = 5122115) B5122115
theorem B2276057 : Blo 1516955 2276057 := bstep (se 2 (by rfl) ⟨853521, by rfl⟩ : syracuseStep 2276057 = 1707043) B1707043
theorem B10525457 : Blo 1516955 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B2276171 : Blo 1516955 2276171 := bstep (se 1 (by rfl) ⟨1707128, by rfl⟩ : syracuseStep 2276171 = 3414257) B3414257
theorem B2431819 : Blo 1516955 2431819 := bstep (se 1 (by rfl) ⟨1823864, by rfl⟩ : syracuseStep 2431819 = 3647729) B3647729
theorem B2276183 : Blo 1516955 2276183 := bstep (se 1 (by rfl) ⟨1707137, by rfl⟩ : syracuseStep 2276183 = 3414275) B3414275
theorem B2595673 : Blo 1516955 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B3414923 : Blo 1516955 3414923 := bstep (se 1 (by rfl) ⟨2561192, by rfl⟩ : syracuseStep 3414923 = 5122385) B5122385
theorem B1973143 : Blo 1516955 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B2276249 : Blo 1516955 2276249 := bstep (se 2 (by rfl) ⟨853593, by rfl⟩ : syracuseStep 2276249 = 1707187) B1707187
theorem B3414977 : Blo 1516955 3414977 := bstep (se 2 (by rfl) ⟨1280616, by rfl⟩ : syracuseStep 3414977 = 2561233) B2561233
theorem B2276363 : Blo 1516955 2276363 := bstep (se 1 (by rfl) ⟨1707272, by rfl⟩ : syracuseStep 2276363 = 3414545) B3414545
theorem B2276375 : Blo 1516955 2276375 := bstep (se 1 (by rfl) ⟨1707281, by rfl⟩ : syracuseStep 2276375 = 3414563) B3414563
theorem B2276441 : Blo 1516955 2276441 := bstep (se 2 (by rfl) ⟨853665, by rfl⟩ : syracuseStep 2276441 = 1707331) B1707331
theorem B8313949 : Blo 1516955 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B3284107 : Blo 1516955 3284107 := bstep (se 1 (by rfl) ⟨2463080, by rfl⟩ : syracuseStep 3284107 = 4926161) B4926161
theorem B3415193 : Blo 1516955 3415193 := bstep (se 2 (by rfl) ⟨1280697, by rfl⟩ : syracuseStep 3415193 = 2561395) B2561395
theorem B2276555 : Blo 1516955 2276555 := bstep (se 1 (by rfl) ⟨1707416, by rfl⟩ : syracuseStep 2276555 = 3414833) B3414833
theorem B2276567 : Blo 1516955 2276567 := bstep (se 1 (by rfl) ⟨1707425, by rfl⟩ : syracuseStep 2276567 = 3414851) B3414851
theorem B3415283 : Blo 1516955 3415283 := bstep (se 1 (by rfl) ⟨2561462, by rfl⟩ : syracuseStep 3415283 = 5122925) B5122925
theorem B3841303 : Blo 1516955 3841303 := bstep (se 1 (by rfl) ⟨2880977, by rfl⟩ : syracuseStep 3841303 = 5761955) B5761955
theorem B3415319 : Blo 1516955 3415319 := bstep (se 1 (by rfl) ⟨2561489, by rfl⟩ : syracuseStep 3415319 = 5122979) B5122979
theorem B2276633 : Blo 1516955 2276633 := bstep (se 2 (by rfl) ⟨853737, by rfl⟩ : syracuseStep 2276633 = 1707475) B1707475
theorem B2162009 : Blo 1516955 2162009 := bstep (se 2 (by rfl) ⟨810753, by rfl⟩ : syracuseStep 2162009 = 1621507) B1621507
theorem B2276747 : Blo 1516955 2276747 := bstep (se 1 (by rfl) ⟨1707560, by rfl⟩ : syracuseStep 2276747 = 3415121) B3415121
theorem B2276759 : Blo 1516955 2276759 := bstep (se 1 (by rfl) ⟨1707569, by rfl⟩ : syracuseStep 2276759 = 3415139) B3415139
theorem B3415499 : Blo 1516955 3415499 := bstep (se 1 (by rfl) ⟨2561624, by rfl⟩ : syracuseStep 3415499 = 5123249) B5123249
theorem B2276825 : Blo 1516955 2276825 := bstep (se 2 (by rfl) ⟨853809, by rfl⟩ : syracuseStep 2276825 = 1707619) B1707619
theorem B3415553 : Blo 1516955 3415553 := bstep (se 2 (by rfl) ⟨1280832, by rfl⟩ : syracuseStep 3415553 = 2561665) B2561665
theorem B7683659 : Blo 1516955 7683659 := bstep (se 1 (by rfl) ⟨5762744, by rfl⟩ : syracuseStep 7683659 = 11525489) B11525489
theorem B2276939 : Blo 1516955 2276939 := bstep (se 1 (by rfl) ⟨1707704, by rfl⟩ : syracuseStep 2276939 = 3415409) B3415409
theorem B2276951 : Blo 1516955 2276951 := bstep (se 1 (by rfl) ⟨1707713, by rfl⟩ : syracuseStep 2276951 = 3415427) B3415427
theorem B5471837 : Blo 1516955 5471837 := bstep (se 3 (by rfl) ⟨1025969, by rfl⟩ : syracuseStep 5471837 = 2051939) B2051939
theorem B6659729 : Blo 1516955 6659729 := bstep (se 2 (by rfl) ⟨2497398, by rfl⟩ : syracuseStep 6659729 = 4994797) B4994797
theorem B2277017 : Blo 1516955 2277017 := bstep (se 2 (by rfl) ⟨853881, by rfl⟩ : syracuseStep 2277017 = 1707763) B1707763
theorem B4677313 : Blo 1516955 4677313 := bstep (se 2 (by rfl) ⟨1753992, by rfl⟩ : syracuseStep 4677313 = 3507985) B3507985
theorem B3841739 : Blo 1516955 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B3415769 : Blo 1516955 3415769 := bstep (se 2 (by rfl) ⟨1280913, by rfl⟩ : syracuseStep 3415769 = 2561827) B2561827
theorem B2277131 : Blo 1516955 2277131 := bstep (se 1 (by rfl) ⟨1707848, by rfl⟩ : syracuseStep 2277131 = 3415697) B3415697
theorem B8208145 : Blo 1516955 8208145 := bstep (se 2 (by rfl) ⟨3078054, by rfl⟩ : syracuseStep 8208145 = 6156109) B6156109
theorem B2277143 : Blo 1516955 2277143 := bstep (se 1 (by rfl) ⟨1707857, by rfl⟩ : syracuseStep 2277143 = 3415715) B3415715
theorem B3415859 : Blo 1516955 3415859 := bstep (se 1 (by rfl) ⟨2561894, by rfl⟩ : syracuseStep 3415859 = 5123789) B5123789
theorem B3415895 : Blo 1516955 3415895 := bstep (se 1 (by rfl) ⟨2561921, by rfl⟩ : syracuseStep 3415895 = 5123843) B5123843
theorem B2277209 : Blo 1516955 2277209 := bstep (se 2 (by rfl) ⟨853953, by rfl⟩ : syracuseStep 2277209 = 1707907) B1707907
theorem B41533361 : Blo 1516955 41533361 := bstep (se 2 (by rfl) ⟨15575010, by rfl⟩ : syracuseStep 41533361 = 31150021) B31150021
theorem B2277323 : Blo 1516955 2277323 := bstep (se 1 (by rfl) ⟨1707992, by rfl⟩ : syracuseStep 2277323 = 3415985) B3415985
theorem B13844429 : Blo 1516955 13844429 := bstep (se 3 (by rfl) ⟨2595830, by rfl⟩ : syracuseStep 13844429 = 5191661) B5191661
theorem B2277335 : Blo 1516955 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B14581721 : Blo 1516955 14581721 := bstep (se 2 (by rfl) ⟨5468145, by rfl⟩ : syracuseStep 14581721 = 10936291) B10936291
theorem B2277383 : Blo 1516955 2277383 := bstep (se 1 (by rfl) ⟨1708037, by rfl⟩ : syracuseStep 2277383 = 3416075) B3416075
theorem B3842063 : Blo 1516955 3842063 := bstep (se 1 (by rfl) ⟨2881547, by rfl⟩ : syracuseStep 3842063 = 5763095) B5763095
theorem B2277419 : Blo 1516955 2277419 := bstep (se 1 (by rfl) ⟨1708064, by rfl⟩ : syracuseStep 2277419 = 3416129) B3416129
theorem B5472299 : Blo 1516955 5472299 := bstep (se 1 (by rfl) ⟨4104224, by rfl⟩ : syracuseStep 5472299 = 8208449) B8208449
theorem B2277449 : Blo 1516955 2277449 := bstep (se 2 (by rfl) ⟨854043, by rfl⟩ : syracuseStep 2277449 = 1708087) B1708087
theorem B3416183 : Blo 1516955 3416183 := bstep (se 1 (by rfl) ⟨2562137, by rfl⟩ : syracuseStep 3416183 = 5124275) B5124275
theorem B3694777 : Blo 1516955 3694777 := bstep (se 2 (by rfl) ⟨1385541, by rfl⟩ : syracuseStep 3694777 = 2771083) B2771083
theorem B2277563 : Blo 1516955 2277563 := bstep (se 1 (by rfl) ⟨1708172, by rfl⟩ : syracuseStep 2277563 = 3416345) B3416345
theorem B2277623 : Blo 1516955 2277623 := bstep (se 1 (by rfl) ⟨1708217, by rfl⟩ : syracuseStep 2277623 = 3416435) B3416435
theorem B2277647 : Blo 1516955 2277647 := bstep (se 1 (by rfl) ⟨1708235, by rfl⟩ : syracuseStep 2277647 = 3416471) B3416471
theorem B3416363 : Blo 1516955 3416363 := bstep (se 1 (by rfl) ⟨2562272, by rfl⟩ : syracuseStep 3416363 = 5124545) B5124545
theorem B10944827 : Blo 1516955 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B5120441 : Blo 1516955 5120441 := bstep (se 2 (by rfl) ⟨1920165, by rfl⟩ : syracuseStep 5120441 = 3840331) B3840331
theorem B6922705 : Blo 1516955 6922705 := bstep (se 2 (by rfl) ⟨2596014, by rfl⟩ : syracuseStep 6922705 = 5192029) B5192029
theorem B7684631 : Blo 1516955 7684631 := bstep (se 1 (by rfl) ⟨5763473, by rfl⟩ : syracuseStep 7684631 = 11526947) B11526947
theorem B3842761 : Blo 1516955 3842761 := bstep (se 2 (by rfl) ⟨1441035, by rfl⟩ : syracuseStep 3842761 = 2882071) B2882071
theorem B3842903 : Blo 1516955 3842903 := bstep (se 1 (by rfl) ⟨2882177, by rfl⟩ : syracuseStep 3842903 = 5764355) B5764355
theorem B5760011 : Blo 1516955 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B5121035 : Blo 1516955 5121035 := bstep (se 1 (by rfl) ⟨3840776, by rfl⟩ : syracuseStep 5121035 = 7681553) B7681553
theorem B5121143 : Blo 1516955 5121143 := bstep (se 1 (by rfl) ⟨3840857, by rfl⟩ : syracuseStep 5121143 = 7681715) B7681715
theorem B39437549 : Blo 1516955 39437549 := bstep (se 3 (by rfl) ⟨7394540, by rfl⟩ : syracuseStep 39437549 = 14789081) B14789081
theorem B3646835 : Blo 1516955 3646835 := bstep (se 1 (by rfl) ⟨2735126, by rfl⟩ : syracuseStep 3646835 = 5470253) B5470253
theorem B1516987 : Blo 1516955 1516987 := bstep (se 1 (by rfl) ⟨1137740, by rfl⟩ : syracuseStep 1516987 = 2275481) B2275481
theorem B11085265 : Blo 1516955 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B1517063 : Blo 1516955 1517063 := bstep (se 1 (by rfl) ⟨1137797, by rfl⟩ : syracuseStep 1517063 = 2275595) B2275595
theorem B1517071 : Blo 1516955 1517071 := bstep (se 1 (by rfl) ⟨1137803, by rfl⟩ : syracuseStep 1517071 = 2275607) B2275607
theorem B1517115 : Blo 1516955 1517115 := bstep (se 1 (by rfl) ⟨1137836, by rfl⟩ : syracuseStep 1517115 = 2275673) B2275673
theorem B9725507 : Blo 1516955 9725507 := bstep (se 1 (by rfl) ⟨7294130, by rfl⟩ : syracuseStep 9725507 = 14588261) B14588261
theorem B1517191 : Blo 1516955 1517191 := bstep (se 1 (by rfl) ⟨1137893, by rfl⟩ : syracuseStep 1517191 = 2275787) B2275787
theorem B1517199 : Blo 1516955 1517199 := bstep (se 1 (by rfl) ⟨1137899, by rfl⟩ : syracuseStep 1517199 = 2275799) B2275799
theorem B1517243 : Blo 1516955 1517243 := bstep (se 1 (by rfl) ⟨1137932, by rfl⟩ : syracuseStep 1517243 = 2275865) B2275865
theorem B5121737 : Blo 1516955 5121737 := bstep (se 2 (by rfl) ⟨1920651, by rfl⟩ : syracuseStep 5121737 = 3841303) B3841303
theorem B29165285 : Blo 1516955 29165285 := bstep (se 4 (by rfl) ⟨2734245, by rfl⟩ : syracuseStep 29165285 = 5468491) B5468491
theorem B1517319 : Blo 1516955 1517319 := bstep (se 1 (by rfl) ⟨1137989, by rfl⟩ : syracuseStep 1517319 = 2275979) B2275979
theorem B1517327 : Blo 1516955 1517327 := bstep (se 1 (by rfl) ⟨1137995, by rfl⟩ : syracuseStep 1517327 = 2275991) B2275991
theorem B1517371 : Blo 1516955 1517371 := bstep (se 1 (by rfl) ⟨1138028, by rfl⟩ : syracuseStep 1517371 = 2276057) B2276057
theorem B1517447 : Blo 1516955 1517447 := bstep (se 1 (by rfl) ⟨1138085, by rfl⟩ : syracuseStep 1517447 = 2276171) B2276171
theorem B1517455 : Blo 1516955 1517455 := bstep (se 1 (by rfl) ⟨1138091, by rfl⟩ : syracuseStep 1517455 = 2276183) B2276183
theorem B5760953 : Blo 1516955 5760953 := bstep (se 2 (by rfl) ⟨2160357, by rfl⟩ : syracuseStep 5760953 = 4320715) B4320715
theorem B1517499 : Blo 1516955 1517499 := bstep (se 1 (by rfl) ⟨1138124, by rfl⟩ : syracuseStep 1517499 = 2276249) B2276249
theorem B1517575 : Blo 1516955 1517575 := bstep (se 1 (by rfl) ⟨1138181, by rfl⟩ : syracuseStep 1517575 = 2276363) B2276363
theorem B1517583 : Blo 1516955 1517583 := bstep (se 1 (by rfl) ⟨1138187, by rfl⟩ : syracuseStep 1517583 = 2276375) B2276375
theorem B1517627 : Blo 1516955 1517627 := bstep (se 1 (by rfl) ⟨1138220, by rfl⟩ : syracuseStep 1517627 = 2276441) B2276441
theorem B1517703 : Blo 1516955 1517703 := bstep (se 1 (by rfl) ⟨1138277, by rfl⟩ : syracuseStep 1517703 = 2276555) B2276555
theorem B1517711 : Blo 1516955 1517711 := bstep (se 1 (by rfl) ⟨1138283, by rfl⟩ : syracuseStep 1517711 = 2276567) B2276567
theorem B1517755 : Blo 1516955 1517755 := bstep (se 1 (by rfl) ⟨1138316, by rfl⟩ : syracuseStep 1517755 = 2276633) B2276633
theorem B6236417 : Blo 1516955 6236417 := bstep (se 2 (by rfl) ⟨2338656, by rfl⟩ : syracuseStep 6236417 = 4677313) B4677313
theorem B1517831 : Blo 1516955 1517831 := bstep (se 1 (by rfl) ⟨1138373, by rfl⟩ : syracuseStep 1517831 = 2276747) B2276747
theorem B1517839 : Blo 1516955 1517839 := bstep (se 1 (by rfl) ⟨1138379, by rfl⟩ : syracuseStep 1517839 = 2276759) B2276759
theorem B1517883 : Blo 1516955 1517883 := bstep (se 1 (by rfl) ⟨1138412, by rfl⟩ : syracuseStep 1517883 = 2276825) B2276825
theorem B5122439 : Blo 1516955 5122439 := bstep (se 1 (by rfl) ⟨3841829, by rfl⟩ : syracuseStep 5122439 = 7683659) B7683659
theorem B1517959 : Blo 1516955 1517959 := bstep (se 1 (by rfl) ⟨1138469, by rfl⟩ : syracuseStep 1517959 = 2276939) B2276939
theorem B1517967 : Blo 1516955 1517967 := bstep (se 1 (by rfl) ⟨1138475, by rfl⟩ : syracuseStep 1517967 = 2276951) B2276951
theorem B3647891 : Blo 1516955 3647891 := bstep (se 1 (by rfl) ⟨2735918, by rfl⟩ : syracuseStep 3647891 = 5471837) B5471837
theorem B1518011 : Blo 1516955 1518011 := bstep (se 1 (by rfl) ⟨1138508, by rfl⟩ : syracuseStep 1518011 = 2277017) B2277017
theorem B6572497 : Blo 1516955 6572497 := bstep (se 2 (by rfl) ⟨2464686, by rfl⟩ : syracuseStep 6572497 = 4929373) B4929373
theorem B328362457 : Blo 1516955 328362457 := bstep (se 2 (by rfl) ⟨123135921, by rfl⟩ : syracuseStep 328362457 = 246271843) B246271843
theorem B1518087 : Blo 1516955 1518087 := bstep (se 1 (by rfl) ⟨1138565, by rfl⟩ : syracuseStep 1518087 = 2277131) B2277131
theorem B1518095 : Blo 1516955 1518095 := bstep (se 1 (by rfl) ⟨1138571, by rfl⟩ : syracuseStep 1518095 = 2277143) B2277143
theorem B1518139 : Blo 1516955 1518139 := bstep (se 1 (by rfl) ⟨1138604, by rfl⟩ : syracuseStep 1518139 = 2277209) B2277209
theorem B1518215 : Blo 1516955 1518215 := bstep (se 1 (by rfl) ⟨1138661, by rfl⟩ : syracuseStep 1518215 = 2277323) B2277323
theorem B1518223 : Blo 1516955 1518223 := bstep (se 1 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 1518223 = 2277335) B2277335
theorem B1706683 : Blo 1516955 1706683 := bstep (se 1 (by rfl) ⟨1280012, by rfl⟩ : syracuseStep 1706683 = 2560025) B2560025
theorem B1518267 : Blo 1516955 1518267 := bstep (se 1 (by rfl) ⟨1138700, by rfl⟩ : syracuseStep 1518267 = 2277401) B2277401
theorem B5122817 : Blo 1516955 5122817 := bstep (se 2 (by rfl) ⟨1921056, by rfl⟩ : syracuseStep 5122817 = 3842113) B3842113
theorem B1518343 : Blo 1516955 1518343 := bstep (se 1 (by rfl) ⟨1138757, by rfl⟩ : syracuseStep 1518343 = 2277515) B2277515
theorem B1518351 : Blo 1516955 1518351 := bstep (se 1 (by rfl) ⟨1138763, by rfl⟩ : syracuseStep 1518351 = 2277527) B2277527
theorem B6482747 : Blo 1516955 6482747 := bstep (se 1 (by rfl) ⟨4862060, by rfl⟩ : syracuseStep 6482747 = 9724121) B9724121
theorem B1518395 : Blo 1516955 1518395 := bstep (se 1 (by rfl) ⟨1138796, by rfl⟩ : syracuseStep 1518395 = 2277593) B2277593
theorem B2919287 : Blo 1516955 2919287 := bstep (se 1 (by rfl) ⟨2189465, by rfl⟩ : syracuseStep 2919287 = 4378931) B4378931
theorem B70060949 : Blo 1516955 70060949 := bstep (se 6 (by rfl) ⟨1642053, by rfl⟩ : syracuseStep 70060949 = 3284107) B3284107
theorem B6482987 : Blo 1516955 6482987 := bstep (se 1 (by rfl) ⟨4862240, by rfl⟩ : syracuseStep 6482987 = 9724481) B9724481
theorem B2051129 : Blo 1516955 2051129 := bstep (se 2 (by rfl) ⟨769173, by rfl⟩ : syracuseStep 2051129 = 1538347) B1538347
theorem B4320317 : Blo 1516955 4320317 := bstep (se 3 (by rfl) ⟨810059, by rfl⟩ : syracuseStep 4320317 = 1620119) B1620119
theorem B5467223 : Blo 1516955 5467223 := bstep (se 1 (by rfl) ⟨4100417, by rfl⟩ : syracuseStep 5467223 = 8200835) B8200835
theorem B1707151 : Blo 1516955 1707151 := bstep (se 1 (by rfl) ⟨1280363, by rfl⟩ : syracuseStep 1707151 = 2560727) B2560727
theorem B2190583 : Blo 1516955 2190583 := bstep (se 1 (by rfl) ⟨1642937, by rfl⟩ : syracuseStep 2190583 = 3285875) B3285875
theorem B4320647 : Blo 1516955 4320647 := bstep (se 1 (by rfl) ⟨3240485, by rfl⟩ : syracuseStep 4320647 = 6480971) B6480971
theorem B6483347 : Blo 1516955 6483347 := bstep (se 1 (by rfl) ⟨4862510, by rfl⟩ : syracuseStep 6483347 = 9725021) B9725021
theorem B5123627 : Blo 1516955 5123627 := bstep (se 1 (by rfl) ⟨3842720, by rfl⟩ : syracuseStep 5123627 = 7685441) B7685441
theorem B1707655 : Blo 1516955 1707655 := bstep (se 1 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 1707655 = 2561483) B2561483
theorem B6156013 : Blo 1516955 6156013 := bstep (se 3 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 6156013 = 2308505) B2308505
theorem B3460897 : Blo 1516955 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B1707835 : Blo 1516955 1707835 := bstep (se 1 (by rfl) ⟨1280876, by rfl⟩ : syracuseStep 1707835 = 2561753) B2561753
theorem B2559863 : Blo 1516955 2559863 := bstep (se 1 (by rfl) ⟨1919897, by rfl⟩ : syracuseStep 2559863 = 3839795) B3839795
theorem B1822711 : Blo 1516955 1822711 := bstep (se 1 (by rfl) ⟨1367033, by rfl⟩ : syracuseStep 1822711 = 2734067) B2734067
theorem B4616279 : Blo 1516955 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B7680257 : Blo 1516955 7680257 := bstep (se 2 (by rfl) ⟨2880096, by rfl⟩ : syracuseStep 7680257 = 5760193) B5760193
theorem B2560315 : Blo 1516955 2560315 := bstep (se 1 (by rfl) ⟨1920236, by rfl⟩ : syracuseStep 2560315 = 3840473) B3840473
theorem B2879945 : Blo 1516955 2879945 := bstep (se 2 (by rfl) ⟨1079979, by rfl⟩ : syracuseStep 2879945 = 2159959) B2159959
theorem B2560457 : Blo 1516955 2560457 := bstep (se 2 (by rfl) ⟨960171, by rfl⟩ : syracuseStep 2560457 = 1920343) B1920343
theorem B7016971 : Blo 1516955 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B5763595 : Blo 1516955 5763595 := bstep (se 1 (by rfl) ⟨4322696, by rfl⟩ : syracuseStep 5763595 = 8645393) B8645393
theorem B4616765 : Blo 1516955 4616765 := bstep (se 3 (by rfl) ⟨865643, by rfl⟩ : syracuseStep 4616765 = 1731287) B1731287
theorem B10523429 : Blo 1516955 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B5763899 : Blo 1516955 5763899 := bstep (se 1 (by rfl) ⟨4322924, by rfl⟩ : syracuseStep 5763899 = 8645849) B8645849
theorem B4862855 : Blo 1516955 4862855 := bstep (se 1 (by rfl) ⟨3647141, by rfl⟩ : syracuseStep 4862855 = 7294283) B7294283
theorem B8647559 : Blo 1516955 8647559 := bstep (se 1 (by rfl) ⟨6485669, by rfl⟩ : syracuseStep 8647559 = 12971339) B12971339
theorem B4617107 : Blo 1516955 4617107 := bstep (se 1 (by rfl) ⟨3462830, by rfl⟩ : syracuseStep 4617107 = 6925661) B6925661
theorem B3077065 : Blo 1516955 3077065 := bstep (se 2 (by rfl) ⟨1153899, by rfl⟩ : syracuseStep 3077065 = 2307799) B2307799
theorem B7681067 : Blo 1516955 7681067 := bstep (se 1 (by rfl) ⟨5760800, by rfl⟩ : syracuseStep 7681067 = 11521601) B11521601
theorem B5190743 : Blo 1516955 5190743 := bstep (se 1 (by rfl) ⟨3893057, by rfl⟩ : syracuseStep 5190743 = 7786115) B7786115
theorem B4322423 : Blo 1516955 4322423 := bstep (se 1 (by rfl) ⟨3241817, by rfl⟩ : syracuseStep 4322423 = 6483635) B6483635
theorem B2561159 : Blo 1516955 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B2307215 : Blo 1516955 2307215 := bstep (se 1 (by rfl) ⟨1730411, by rfl⟩ : syracuseStep 2307215 = 3460823) B3460823
theorem B2880659 : Blo 1516955 2880659 := bstep (se 1 (by rfl) ⟨2160494, by rfl⟩ : syracuseStep 2880659 = 4320989) B4320989
theorem B3413177 : Blo 1516955 3413177 := bstep (se 2 (by rfl) ⟨1279941, by rfl⟩ : syracuseStep 3413177 = 2559883) B2559883
theorem B2880697 : Blo 1516955 2880697 := bstep (se 2 (by rfl) ⟨1080261, by rfl⟩ : syracuseStep 2880697 = 2160523) B2160523
theorem B3945673 : Blo 1516955 3945673 := bstep (se 2 (by rfl) ⟨1479627, by rfl⟩ : syracuseStep 3945673 = 2959255) B2959255
theorem B5764385 : Blo 1516955 5764385 := bstep (se 2 (by rfl) ⟨2161644, by rfl⟩ : syracuseStep 5764385 = 4323289) B4323289
theorem B9229619 : Blo 1516955 9229619 := bstep (se 1 (by rfl) ⟨6922214, by rfl⟩ : syracuseStep 9229619 = 13844429) B13844429
theorem B9721147 : Blo 1516955 9721147 := bstep (se 1 (by rfl) ⟨7290860, by rfl⟩ : syracuseStep 9721147 = 14581721) B14581721
theorem B31167929 : Blo 1516955 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B3413519 : Blo 1516955 3413519 := bstep (se 1 (by rfl) ⟨2560139, by rfl⟩ : syracuseStep 3413519 = 5120279) B5120279
theorem B3413537 : Blo 1516955 3413537 := bstep (se 2 (by rfl) ⟨1280076, by rfl⟩ : syracuseStep 3413537 = 2560153) B2560153
theorem B2307727 : Blo 1516955 2307727 := bstep (se 1 (by rfl) ⟨1730795, by rfl⟩ : syracuseStep 2307727 = 3461591) B3461591
theorem B7493357 : Blo 1516955 7493357 := bstep (se 3 (by rfl) ⟨1405004, by rfl⟩ : syracuseStep 7493357 = 2810009) B2810009
theorem B2561807 : Blo 1516955 2561807 := bstep (se 1 (by rfl) ⟨1921355, by rfl⟩ : syracuseStep 2561807 = 3842711) B3842711
theorem B3413879 : Blo 1516955 3413879 := bstep (se 1 (by rfl) ⟨2560409, by rfl⟩ : syracuseStep 3413879 = 5120819) B5120819
theorem B2160631 : Blo 1516955 2160631 := bstep (se 1 (by rfl) ⟨1620473, by rfl⟩ : syracuseStep 2160631 = 3240947) B3240947
theorem B3414059 : Blo 1516955 3414059 := bstep (se 1 (by rfl) ⟨2560544, by rfl⟩ : syracuseStep 3414059 = 5121089) B5121089
theorem B4323415 : Blo 1516955 4323415 := bstep (se 1 (by rfl) ⟨3242561, by rfl⟩ : syracuseStep 4323415 = 6485123) B6485123
theorem B3840119 : Blo 1516955 3840119 := bstep (se 1 (by rfl) ⟨2880089, by rfl⟩ : syracuseStep 3840119 = 5760179) B5760179
theorem B2275463 : Blo 1516955 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B2275499 : Blo 1516955 2275499 := bstep (se 1 (by rfl) ⟨1706624, by rfl⟩ : syracuseStep 2275499 = 3413249) B3413249
theorem B2275529 : Blo 1516955 2275529 := bstep (se 2 (by rfl) ⟨853323, by rfl⟩ : syracuseStep 2275529 = 1706647) B1706647
theorem B5765357 : Blo 1516955 5765357 := bstep (se 3 (by rfl) ⟨1081004, by rfl⟩ : syracuseStep 5765357 = 2162009) B2162009
theorem B2562347 : Blo 1516955 2562347 := bstep (se 1 (by rfl) ⟨1921760, by rfl⟩ : syracuseStep 2562347 = 3843521) B3843521
theorem B43759925 : Blo 1516955 43759925 := bstep (se 5 (by rfl) ⟨2051246, by rfl⟩ : syracuseStep 43759925 = 4102493) B4102493
theorem B2275643 : Blo 1516955 2275643 := bstep (se 1 (by rfl) ⟨1706732, by rfl⟩ : syracuseStep 2275643 = 3413465) B3413465
theorem B7682363 : Blo 1516955 7682363 := bstep (se 1 (by rfl) ⟨5761772, by rfl⟩ : syracuseStep 7682363 = 11523545) B11523545
theorem B2275703 : Blo 1516955 2275703 := bstep (se 1 (by rfl) ⟨1706777, by rfl⟩ : syracuseStep 2275703 = 3413555) B3413555
theorem B2275727 : Blo 1516955 2275727 := bstep (se 1 (by rfl) ⟨1706795, by rfl⟩ : syracuseStep 2275727 = 3413591) B3413591
theorem B3414419 : Blo 1516955 3414419 := bstep (se 1 (by rfl) ⟨2560814, by rfl⟩ : syracuseStep 3414419 = 5121629) B5121629
theorem B2275769 : Blo 1516955 2275769 := bstep (se 2 (by rfl) ⟨853413, by rfl⟩ : syracuseStep 2275769 = 1706827) B1706827
theorem B3242425 : Blo 1516955 3242425 := bstep (se 2 (by rfl) ⟨1215909, by rfl⟩ : syracuseStep 3242425 = 2431819) B2431819
theorem B3414473 : Blo 1516955 3414473 := bstep (se 2 (by rfl) ⟨1280427, by rfl⟩ : syracuseStep 3414473 = 2560855) B2560855
theorem B7682525 : Blo 1516955 7682525 := bstep (se 3 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 7682525 = 2880947) B2880947
theorem B2275847 : Blo 1516955 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B2275883 : Blo 1516955 2275883 := bstep (se 1 (by rfl) ⟨1706912, by rfl⟩ : syracuseStep 2275883 = 3413825) B3413825
theorem B2275913 : Blo 1516955 2275913 := bstep (se 2 (by rfl) ⟨853467, by rfl⟩ : syracuseStep 2275913 = 1706935) B1706935
theorem B2276027 : Blo 1516955 2276027 := bstep (se 1 (by rfl) ⟨1707020, by rfl⟩ : syracuseStep 2276027 = 3414041) B3414041
theorem B2276087 : Blo 1516955 2276087 := bstep (se 1 (by rfl) ⟨1707065, by rfl⟩ : syracuseStep 2276087 = 3414131) B3414131
theorem B2276111 : Blo 1516955 2276111 := bstep (se 1 (by rfl) ⟨1707083, by rfl⟩ : syracuseStep 2276111 = 3414167) B3414167
theorem B3242767 : Blo 1516955 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B7682849 : Blo 1516955 7682849 := bstep (se 2 (by rfl) ⟨2881068, by rfl⟩ : syracuseStep 7682849 = 5762137) B5762137
theorem B2161451 : Blo 1516955 2161451 := bstep (se 1 (by rfl) ⟨1621088, by rfl⟩ : syracuseStep 2161451 = 3242177) B3242177
theorem B18004787 : Blo 1516955 18004787 := bstep (se 1 (by rfl) ⟨13503590, by rfl⟩ : syracuseStep 18004787 = 27007181) B27007181
theorem B2276153 : Blo 1516955 2276153 := bstep (se 2 (by rfl) ⟨853557, by rfl⟩ : syracuseStep 2276153 = 1707115) B1707115
theorem B2276231 : Blo 1516955 2276231 := bstep (se 1 (by rfl) ⟨1707173, by rfl⟩ : syracuseStep 2276231 = 3414347) B3414347
theorem B2276267 : Blo 1516955 2276267 := bstep (se 1 (by rfl) ⟨1707200, by rfl⟩ : syracuseStep 2276267 = 3414401) B3414401
theorem B2276297 : Blo 1516955 2276297 := bstep (se 2 (by rfl) ⟨853611, by rfl⟩ : syracuseStep 2276297 = 1707223) B1707223
theorem B2882603 : Blo 1516955 2882603 := bstep (se 1 (by rfl) ⟨2161952, by rfl⟩ : syracuseStep 2882603 = 4323905) B4323905
theorem B2276411 : Blo 1516955 2276411 := bstep (se 1 (by rfl) ⟨1707308, by rfl⟩ : syracuseStep 2276411 = 3414617) B3414617
theorem B2276471 : Blo 1516955 2276471 := bstep (se 1 (by rfl) ⟨1707353, by rfl⟩ : syracuseStep 2276471 = 3414707) B3414707
theorem B3415175 : Blo 1516955 3415175 := bstep (se 1 (by rfl) ⟨2561381, by rfl⟩ : syracuseStep 3415175 = 5122763) B5122763
theorem B2276495 : Blo 1516955 2276495 := bstep (se 1 (by rfl) ⟨1707371, by rfl⟩ : syracuseStep 2276495 = 3414743) B3414743
theorem B2276537 : Blo 1516955 2276537 := bstep (se 2 (by rfl) ⟨853701, by rfl⟩ : syracuseStep 2276537 = 1707403) B1707403
theorem B2276615 : Blo 1516955 2276615 := bstep (se 1 (by rfl) ⟨1707461, by rfl⟩ : syracuseStep 2276615 = 3414923) B3414923
theorem B6151439 : Blo 1516955 6151439 := bstep (se 1 (by rfl) ⟨4613579, by rfl⟩ : syracuseStep 6151439 = 9227159) B9227159
theorem B2276651 : Blo 1516955 2276651 := bstep (se 1 (by rfl) ⟨1707488, by rfl⟩ : syracuseStep 2276651 = 3414977) B3414977
theorem B3415355 : Blo 1516955 3415355 := bstep (se 1 (by rfl) ⟨2561516, by rfl⟩ : syracuseStep 3415355 = 5123033) B5123033
theorem B2276681 : Blo 1516955 2276681 := bstep (se 2 (by rfl) ⟨853755, by rfl⟩ : syracuseStep 2276681 = 1707511) B1707511
theorem B3841415 : Blo 1516955 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B3841465 : Blo 1516955 3841465 := bstep (se 2 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 3841465 = 2881099) B2881099
theorem B3415481 : Blo 1516955 3415481 := bstep (se 2 (by rfl) ⟨1280805, by rfl⟩ : syracuseStep 3415481 = 2561611) B2561611
theorem B2276795 : Blo 1516955 2276795 := bstep (se 1 (by rfl) ⟨1707596, by rfl⟩ : syracuseStep 2276795 = 3415193) B3415193
theorem B2735545 : Blo 1516955 2735545 := bstep (se 2 (by rfl) ⟨1025829, by rfl⟩ : syracuseStep 2735545 = 2051659) B2051659
theorem B8207801 : Blo 1516955 8207801 := bstep (se 2 (by rfl) ⟨3077925, by rfl⟩ : syracuseStep 8207801 = 6155851) B6155851
theorem B2276855 : Blo 1516955 2276855 := bstep (se 1 (by rfl) ⟨1707641, by rfl⟩ : syracuseStep 2276855 = 3415283) B3415283
theorem B2276879 : Blo 1516955 2276879 := bstep (se 1 (by rfl) ⟨1707659, by rfl⟩ : syracuseStep 2276879 = 3415319) B3415319
theorem B16866845 : Blo 1516955 16866845 := bstep (se 3 (by rfl) ⟨3162533, by rfl⟩ : syracuseStep 16866845 = 6325067) B6325067
theorem B2276921 : Blo 1516955 2276921 := bstep (se 2 (by rfl) ⟨853845, by rfl⟩ : syracuseStep 2276921 = 1707691) B1707691
theorem B2276999 : Blo 1516955 2276999 := bstep (se 1 (by rfl) ⟨1707749, by rfl⟩ : syracuseStep 2276999 = 3415499) B3415499
theorem B2277035 : Blo 1516955 2277035 := bstep (se 1 (by rfl) ⟨1707776, by rfl⟩ : syracuseStep 2277035 = 3415553) B3415553
theorem B10944193 : Blo 1516955 10944193 := bstep (se 2 (by rfl) ⟨4104072, by rfl⟩ : syracuseStep 10944193 = 8208145) B8208145
theorem B5545673 : Blo 1516955 5545673 := bstep (se 2 (by rfl) ⟨2079627, by rfl⟩ : syracuseStep 5545673 = 4159255) B4159255
theorem B2277065 : Blo 1516955 2277065 := bstep (se 2 (by rfl) ⟨853899, by rfl⟩ : syracuseStep 2277065 = 1707799) B1707799
theorem B7683821 : Blo 1516955 7683821 := bstep (se 3 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 7683821 = 2881433) B2881433
theorem B4439819 : Blo 1516955 4439819 := bstep (se 1 (by rfl) ⟨3329864, by rfl⟩ : syracuseStep 4439819 = 6659729) B6659729
theorem B3415823 : Blo 1516955 3415823 := bstep (se 1 (by rfl) ⟨2561867, by rfl⟩ : syracuseStep 3415823 = 5123735) B5123735
theorem B3415841 : Blo 1516955 3415841 := bstep (se 2 (by rfl) ⟨1280940, by rfl⟩ : syracuseStep 3415841 = 2561881) B2561881
theorem B2277179 : Blo 1516955 2277179 := bstep (se 1 (by rfl) ⟨1707884, by rfl⟩ : syracuseStep 2277179 = 3415769) B3415769
theorem B2277239 : Blo 1516955 2277239 := bstep (se 1 (by rfl) ⟨1707929, by rfl⟩ : syracuseStep 2277239 = 3415859) B3415859
theorem B2277263 : Blo 1516955 2277263 := bstep (se 1 (by rfl) ⟨1707947, by rfl⟩ : syracuseStep 2277263 = 3415895) B3415895
theorem B2277305 : Blo 1516955 2277305 := bstep (se 2 (by rfl) ⟨853989, by rfl⟩ : syracuseStep 2277305 = 1707979) B1707979
theorem B4104137 : Blo 1516955 4104137 := bstep (se 2 (by rfl) ⟨1539051, by rfl⟩ : syracuseStep 4104137 = 3078103) B3078103
theorem B27688907 : Blo 1516955 27688907 := bstep (se 1 (by rfl) ⟨20766680, by rfl⟩ : syracuseStep 27688907 = 41533361) B41533361
theorem B2277455 : Blo 1516955 2277455 := bstep (se 1 (by rfl) ⟨1708091, by rfl⟩ : syracuseStep 2277455 = 3416183) B3416183
theorem B5120171 : Blo 1516955 5120171 := bstep (se 1 (by rfl) ⟨3840128, by rfl⟩ : syracuseStep 5120171 = 7680257) B7680257
theorem B2277575 : Blo 1516955 2277575 := bstep (se 1 (by rfl) ⟨1708181, by rfl⟩ : syracuseStep 2277575 = 3416363) B3416363
theorem B11526461 : Blo 1516955 11526461 := bstep (se 3 (by rfl) ⟨2161211, by rfl⟩ : syracuseStep 11526461 = 4322423) B4322423
theorem B6152573 : Blo 1516955 6152573 := bstep (se 3 (by rfl) ⟨1153607, by rfl⟩ : syracuseStep 6152573 = 2307215) B2307215
theorem B3842599 : Blo 1516955 3842599 := bstep (se 1 (by rfl) ⟨2881949, by rfl⟩ : syracuseStep 3842599 = 5763899) B5763899
theorem B9355961 : Blo 1516955 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B7684793 : Blo 1516955 7684793 := bstep (se 2 (by rfl) ⟨2881797, by rfl⟩ : syracuseStep 7684793 = 5763595) B5763595
theorem B5120711 : Blo 1516955 5120711 := bstep (se 1 (by rfl) ⟨3840533, by rfl⟩ : syracuseStep 5120711 = 7681067) B7681067
theorem B3842923 : Blo 1516955 3842923 := bstep (se 1 (by rfl) ⟨2882192, by rfl⟩ : syracuseStep 3842923 = 5764385) B5764385
theorem B6153079 : Blo 1516955 6153079 := bstep (se 1 (by rfl) ⟨4614809, by rfl⟩ : syracuseStep 6153079 = 9229619) B9229619
theorem B11683109 : Blo 1516955 11683109 := bstep (se 4 (by rfl) ⟨1095291, by rfl⟩ : syracuseStep 11683109 = 2190583) B2190583
theorem B1516975 : Blo 1516955 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B1516999 : Blo 1516955 1516999 := bstep (se 1 (by rfl) ⟨1137749, by rfl⟩ : syracuseStep 1516999 = 2275499) B2275499
theorem B1517019 : Blo 1516955 1517019 := bstep (se 1 (by rfl) ⟨1137764, by rfl⟩ : syracuseStep 1517019 = 2275529) B2275529
theorem B3843571 : Blo 1516955 3843571 := bstep (se 1 (by rfl) ⟨2882678, by rfl⟩ : syracuseStep 3843571 = 5765357) B5765357
theorem B29173283 : Blo 1516955 29173283 := bstep (se 1 (by rfl) ⟨21879962, by rfl⟩ : syracuseStep 29173283 = 43759925) B43759925
theorem B1517095 : Blo 1516955 1517095 := bstep (se 1 (by rfl) ⟨1137821, by rfl⟩ : syracuseStep 1517095 = 2275643) B2275643
theorem B5121575 : Blo 1516955 5121575 := bstep (se 1 (by rfl) ⟨3841181, by rfl⟩ : syracuseStep 5121575 = 7682363) B7682363
theorem B1517135 : Blo 1516955 1517135 := bstep (se 1 (by rfl) ⟨1137851, by rfl⟩ : syracuseStep 1517135 = 2275703) B2275703
theorem B1517151 : Blo 1516955 1517151 := bstep (se 1 (by rfl) ⟨1137863, by rfl⟩ : syracuseStep 1517151 = 2275727) B2275727
theorem B5260897 : Blo 1516955 5260897 := bstep (se 2 (by rfl) ⟨1972836, by rfl⟩ : syracuseStep 5260897 = 3945673) B3945673
theorem B1517179 : Blo 1516955 1517179 := bstep (se 1 (by rfl) ⟨1137884, by rfl⟩ : syracuseStep 1517179 = 2275769) B2275769
theorem B5121683 : Blo 1516955 5121683 := bstep (se 1 (by rfl) ⟨3841262, by rfl⟩ : syracuseStep 5121683 = 7682525) B7682525
theorem B1517231 : Blo 1516955 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B1517255 : Blo 1516955 1517255 := bstep (se 1 (by rfl) ⟨1137941, by rfl⟩ : syracuseStep 1517255 = 2275883) B2275883
theorem B1517275 : Blo 1516955 1517275 := bstep (se 1 (by rfl) ⟨1137956, by rfl⟩ : syracuseStep 1517275 = 2275913) B2275913
theorem B12961529 : Blo 1516955 12961529 := bstep (se 2 (by rfl) ⟨4860573, by rfl⟩ : syracuseStep 12961529 = 9721147) B9721147
theorem B1517351 : Blo 1516955 1517351 := bstep (se 1 (by rfl) ⟨1138013, by rfl⟩ : syracuseStep 1517351 = 2276027) B2276027
theorem B1517391 : Blo 1516955 1517391 := bstep (se 1 (by rfl) ⟨1138043, by rfl⟩ : syracuseStep 1517391 = 2276087) B2276087
theorem B1517407 : Blo 1516955 1517407 := bstep (se 1 (by rfl) ⟨1138055, by rfl⟩ : syracuseStep 1517407 = 2276111) B2276111
theorem B5121899 : Blo 1516955 5121899 := bstep (se 1 (by rfl) ⟨3841424, by rfl⟩ : syracuseStep 5121899 = 7682849) B7682849
theorem B12003191 : Blo 1516955 12003191 := bstep (se 1 (by rfl) ⟨9002393, by rfl⟩ : syracuseStep 12003191 = 18004787) B18004787
theorem B1517435 : Blo 1516955 1517435 := bstep (se 1 (by rfl) ⟨1138076, by rfl⟩ : syracuseStep 1517435 = 2276153) B2276153
theorem B5121953 : Blo 1516955 5121953 := bstep (se 2 (by rfl) ⟨1920732, by rfl⟩ : syracuseStep 5121953 = 3841465) B3841465
theorem B3647393 : Blo 1516955 3647393 := bstep (se 2 (by rfl) ⟨1367772, by rfl⟩ : syracuseStep 3647393 = 2735545) B2735545
theorem B1517487 : Blo 1516955 1517487 := bstep (se 1 (by rfl) ⟨1138115, by rfl⟩ : syracuseStep 1517487 = 2276231) B2276231
theorem B1517511 : Blo 1516955 1517511 := bstep (se 1 (by rfl) ⟨1138133, by rfl⟩ : syracuseStep 1517511 = 2276267) B2276267
theorem B1517531 : Blo 1516955 1517531 := bstep (se 1 (by rfl) ⟨1138148, by rfl⟩ : syracuseStep 1517531 = 2276297) B2276297
theorem B11839517 : Blo 1516955 11839517 := bstep (se 3 (by rfl) ⟨2219909, by rfl⟩ : syracuseStep 11839517 = 4439819) B4439819
theorem B1517607 : Blo 1516955 1517607 := bstep (se 1 (by rfl) ⟨1138205, by rfl⟩ : syracuseStep 1517607 = 2276411) B2276411
theorem B1517647 : Blo 1516955 1517647 := bstep (se 1 (by rfl) ⟨1138235, by rfl⟩ : syracuseStep 1517647 = 2276471) B2276471
theorem B1517663 : Blo 1516955 1517663 := bstep (se 1 (by rfl) ⟨1138247, by rfl⟩ : syracuseStep 1517663 = 2276495) B2276495
theorem B1517691 : Blo 1516955 1517691 := bstep (se 1 (by rfl) ⟨1138268, by rfl⟩ : syracuseStep 1517691 = 2276537) B2276537
theorem B1517743 : Blo 1516955 1517743 := bstep (se 1 (by rfl) ⟨1138307, by rfl⟩ : syracuseStep 1517743 = 2276615) B2276615
theorem B1517767 : Blo 1516955 1517767 := bstep (se 1 (by rfl) ⟨1138325, by rfl⟩ : syracuseStep 1517767 = 2276651) B2276651
theorem B1517787 : Blo 1516955 1517787 := bstep (se 1 (by rfl) ⟨1138340, by rfl⟩ : syracuseStep 1517787 = 2276681) B2276681
theorem B14592257 : Blo 1516955 14592257 := bstep (se 2 (by rfl) ⟨5472096, by rfl⟩ : syracuseStep 14592257 = 10944193) B10944193
theorem B1517863 : Blo 1516955 1517863 := bstep (se 1 (by rfl) ⟨1138397, by rfl⟩ : syracuseStep 1517863 = 2276795) B2276795
theorem B1517903 : Blo 1516955 1517903 := bstep (se 1 (by rfl) ⟨1138427, by rfl⟩ : syracuseStep 1517903 = 2276855) B2276855
theorem B1517919 : Blo 1516955 1517919 := bstep (se 1 (by rfl) ⟨1138439, by rfl⟩ : syracuseStep 1517919 = 2276879) B2276879
theorem B1517947 : Blo 1516955 1517947 := bstep (se 1 (by rfl) ⟨1138460, by rfl⟩ : syracuseStep 1517947 = 2276921) B2276921
theorem B4614529 : Blo 1516955 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B1517999 : Blo 1516955 1517999 := bstep (se 1 (by rfl) ⟨1138499, by rfl⟩ : syracuseStep 1517999 = 2276999) B2276999
theorem B1518023 : Blo 1516955 1518023 := bstep (se 1 (by rfl) ⟨1138517, by rfl⟩ : syracuseStep 1518023 = 2277035) B2277035
theorem B3697115 : Blo 1516955 3697115 := bstep (se 1 (by rfl) ⟨2772836, by rfl⟩ : syracuseStep 3697115 = 5545673) B5545673
theorem B1518043 : Blo 1516955 1518043 := bstep (se 1 (by rfl) ⟨1138532, by rfl⟩ : syracuseStep 1518043 = 2277065) B2277065
theorem B5122547 : Blo 1516955 5122547 := bstep (se 1 (by rfl) ⟨3841910, by rfl⟩ : syracuseStep 5122547 = 7683821) B7683821
theorem B1518119 : Blo 1516955 1518119 := bstep (se 1 (by rfl) ⟨1138589, by rfl⟩ : syracuseStep 1518119 = 2277179) B2277179
theorem B1706575 : Blo 1516955 1706575 := bstep (se 1 (by rfl) ⟨1279931, by rfl⟩ : syracuseStep 1706575 = 2559863) B2559863
theorem B1518159 : Blo 1516955 1518159 := bstep (se 1 (by rfl) ⟨1138619, by rfl⟩ : syracuseStep 1518159 = 2277239) B2277239
theorem B1518175 : Blo 1516955 1518175 := bstep (se 1 (by rfl) ⟨1138631, by rfl⟩ : syracuseStep 1518175 = 2277263) B2277263
theorem B1518203 : Blo 1516955 1518203 := bstep (se 1 (by rfl) ⟨1138652, by rfl⟩ : syracuseStep 1518203 = 2277305) B2277305
theorem B18459271 : Blo 1516955 18459271 := bstep (se 1 (by rfl) ⟨13844453, by rfl⟩ : syracuseStep 18459271 = 27688907) B27688907
theorem B1518255 : Blo 1516955 1518255 := bstep (se 1 (by rfl) ⟨1138691, by rfl⟩ : syracuseStep 1518255 = 2277383) B2277383
theorem B1518279 : Blo 1516955 1518279 := bstep (se 1 (by rfl) ⟨1138709, by rfl⟩ : syracuseStep 1518279 = 2277419) B2277419
theorem B3648199 : Blo 1516955 3648199 := bstep (se 1 (by rfl) ⟨2736149, by rfl⟩ : syracuseStep 3648199 = 5472299) B5472299
theorem B1518299 : Blo 1516955 1518299 := bstep (se 1 (by rfl) ⟨1138724, by rfl⟩ : syracuseStep 1518299 = 2277449) B2277449
theorem B1518375 : Blo 1516955 1518375 := bstep (se 1 (by rfl) ⟨1138781, by rfl⟩ : syracuseStep 1518375 = 2277563) B2277563
theorem B1518415 : Blo 1516955 1518415 := bstep (se 1 (by rfl) ⟨1138811, by rfl⟩ : syracuseStep 1518415 = 2277623) B2277623
theorem B1518431 : Blo 1516955 1518431 := bstep (se 1 (by rfl) ⟨1138823, by rfl⟩ : syracuseStep 1518431 = 2277647) B2277647
theorem B1919963 : Blo 1516955 1919963 := bstep (se 1 (by rfl) ⟨1439972, by rfl⟩ : syracuseStep 1919963 = 2879945) B2879945
theorem B1706971 : Blo 1516955 1706971 := bstep (se 1 (by rfl) ⟨1280228, by rfl⟩ : syracuseStep 1706971 = 2560457) B2560457
theorem B5123087 : Blo 1516955 5123087 := bstep (se 1 (by rfl) ⟨3842315, by rfl⟩ : syracuseStep 5123087 = 7684631) B7684631
theorem B7015619 : Blo 1516955 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B437816609 : Blo 1516955 437816609 := bstep (se 2 (by rfl) ⟨164181228, by rfl⟩ : syracuseStep 437816609 = 328362457) B328362457
theorem B3460495 : Blo 1516955 3460495 := bstep (se 1 (by rfl) ⟨2595371, by rfl⟩ : syracuseStep 3460495 = 5190743) B5190743
theorem B1707439 : Blo 1516955 1707439 := bstep (se 1 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 1707439 = 2561159) B2561159
theorem B1920439 : Blo 1516955 1920439 := bstep (se 1 (by rfl) ⟨1440329, by rfl⟩ : syracuseStep 1920439 = 2880659) B2880659
theorem B26291699 : Blo 1516955 26291699 := bstep (se 1 (by rfl) ⟨19718774, by rfl⟩ : syracuseStep 26291699 = 39437549) B39437549
theorem B5123681 : Blo 1516955 5123681 := bstep (se 2 (by rfl) ⟨1921380, by rfl⟩ : syracuseStep 5123681 = 3842761) B3842761
theorem B20778619 : Blo 1516955 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B6483671 : Blo 1516955 6483671 := bstep (se 1 (by rfl) ⟨4862753, by rfl⟩ : syracuseStep 6483671 = 9725507) B9725507
theorem B19443523 : Blo 1516955 19443523 := bstep (se 1 (by rfl) ⟨14582642, by rfl⟩ : syracuseStep 19443523 = 29165285) B29165285
theorem B1707871 : Blo 1516955 1707871 := bstep (se 1 (by rfl) ⟨1280903, by rfl⟩ : syracuseStep 1707871 = 2561807) B2561807
theorem B2560079 : Blo 1516955 2560079 := bstep (se 1 (by rfl) ⟨1920059, by rfl⟩ : syracuseStep 2560079 = 3840119) B3840119
theorem B4157611 : Blo 1516955 4157611 := bstep (se 1 (by rfl) ⟨3118208, by rfl⟩ : syracuseStep 4157611 = 6236417) B6236417
theorem B1708231 : Blo 1516955 1708231 := bstep (se 1 (by rfl) ⟨1281173, by rfl⟩ : syracuseStep 1708231 = 2562347) B2562347
theorem B4321831 : Blo 1516955 4321831 := bstep (se 1 (by rfl) ⟨3241373, by rfl⟩ : syracuseStep 4321831 = 6482747) B6482747
theorem B1946191 : Blo 1516955 1946191 := bstep (se 1 (by rfl) ⟨1459643, by rfl⟩ : syracuseStep 1946191 = 2919287) B2919287
theorem B46707299 : Blo 1516955 46707299 := bstep (se 1 (by rfl) ⟨35030474, by rfl⟩ : syracuseStep 46707299 = 70060949) B70060949
theorem B4321991 : Blo 1516955 4321991 := bstep (se 1 (by rfl) ⟨3241493, by rfl⟩ : syracuseStep 4321991 = 6482987) B6482987
theorem B1921735 : Blo 1516955 1921735 := bstep (se 1 (by rfl) ⟨1441301, by rfl⟩ : syracuseStep 1921735 = 2882603) B2882603
theorem B2880211 : Blo 1516955 2880211 := bstep (se 1 (by rfl) ⟨2160158, by rfl⟩ : syracuseStep 2880211 = 4320317) B4320317
theorem B5763869 : Blo 1516955 5763869 := bstep (se 3 (by rfl) ⟨1080725, by rfl⟩ : syracuseStep 5763869 = 2161451) B2161451
theorem B4100959 : Blo 1516955 4100959 := bstep (se 1 (by rfl) ⟨3075719, by rfl⟩ : syracuseStep 4100959 = 6151439) B6151439
theorem B3076969 : Blo 1516955 3076969 := bstep (se 2 (by rfl) ⟨1153863, by rfl⟩ : syracuseStep 3076969 = 2307727) B2307727
theorem B2880431 : Blo 1516955 2880431 := bstep (se 1 (by rfl) ⟨2160323, by rfl⟩ : syracuseStep 2880431 = 4320647) B4320647
theorem B2560943 : Blo 1516955 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B4322231 : Blo 1516955 4322231 := bstep (se 1 (by rfl) ⟨3241673, by rfl⟩ : syracuseStep 4322231 = 6483347) B6483347
theorem B11244563 : Blo 1516955 11244563 := bstep (se 1 (by rfl) ⟨8433422, by rfl⟩ : syracuseStep 11244563 = 16866845) B16866845
theorem B2430281 : Blo 1516955 2430281 := bstep (se 2 (by rfl) ⟨911355, by rfl⟩ : syracuseStep 2430281 = 1822711) B1822711
theorem B2880841 : Blo 1516955 2880841 := bstep (se 2 (by rfl) ⟨1080315, by rfl⟩ : syracuseStep 2880841 = 2160631) B2160631
theorem B2561375 : Blo 1516955 2561375 := bstep (se 1 (by rfl) ⟨1921031, by rfl⟩ : syracuseStep 2561375 = 3842063) B3842063
theorem B3077519 : Blo 1516955 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B5764553 : Blo 1516955 5764553 := bstep (se 2 (by rfl) ⟨2161707, by rfl⟩ : syracuseStep 5764553 = 4323415) B4323415
theorem B5469677 : Blo 1516955 5469677 := bstep (se 3 (by rfl) ⟨1025564, by rfl⟩ : syracuseStep 5469677 = 2051129) B2051129
theorem B7296551 : Blo 1516955 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B14579261 : Blo 1516955 14579261 := bstep (se 3 (by rfl) ⟨2733611, by rfl⟩ : syracuseStep 14579261 = 5467223) B5467223
theorem B3413627 : Blo 1516955 3413627 := bstep (se 1 (by rfl) ⟨2560220, by rfl⟩ : syracuseStep 3413627 = 5120441) B5120441
theorem B3077843 : Blo 1516955 3077843 := bstep (se 1 (by rfl) ⟨2308382, by rfl⟩ : syracuseStep 3077843 = 4616765) B4616765
theorem B3413753 : Blo 1516955 3413753 := bstep (se 2 (by rfl) ⟨1280157, by rfl⟩ : syracuseStep 3413753 = 2560315) B2560315
theorem B2561935 : Blo 1516955 2561935 := bstep (se 1 (by rfl) ⟨1921451, by rfl⟩ : syracuseStep 2561935 = 3842903) B3842903
theorem B4323233 : Blo 1516955 4323233 := bstep (se 2 (by rfl) ⟨1621212, by rfl⟩ : syracuseStep 4323233 = 3242425) B3242425
theorem B5765039 : Blo 1516955 5765039 := bstep (se 1 (by rfl) ⟨4323779, by rfl⟩ : syracuseStep 5765039 = 8647559) B8647559
theorem B3078071 : Blo 1516955 3078071 := bstep (se 1 (by rfl) ⟨2308553, by rfl⟩ : syracuseStep 3078071 = 4617107) B4617107
theorem B9230273 : Blo 1516955 9230273 := bstep (se 2 (by rfl) ⟨3461352, by rfl⟩ : syracuseStep 9230273 = 6922705) B6922705
theorem B8763329 : Blo 1516955 8763329 := bstep (se 2 (by rfl) ⟨3286248, by rfl⟩ : syracuseStep 8763329 = 6572497) B6572497
theorem B3840007 : Blo 1516955 3840007 := bstep (se 1 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 3840007 = 5760011) B5760011
theorem B3414023 : Blo 1516955 3414023 := bstep (se 1 (by rfl) ⟨2560517, by rfl⟩ : syracuseStep 3414023 = 5121035) B5121035
theorem B3414095 : Blo 1516955 3414095 := bstep (se 1 (by rfl) ⟨2560571, by rfl⟩ : syracuseStep 3414095 = 5121143) B5121143
theorem B2275451 : Blo 1516955 2275451 := bstep (se 1 (by rfl) ⟨1706588, by rfl⟩ : syracuseStep 2275451 = 3413177) B3413177
theorem B2431223 : Blo 1516955 2431223 := bstep (se 1 (by rfl) ⟨1823417, by rfl⟩ : syracuseStep 2431223 = 3646835) B3646835
theorem B2275577 : Blo 1516955 2275577 := bstep (se 2 (by rfl) ⟨853341, by rfl⟩ : syracuseStep 2275577 = 1706683) B1706683
theorem B2275679 : Blo 1516955 2275679 := bstep (se 1 (by rfl) ⟨1706759, by rfl⟩ : syracuseStep 2275679 = 3413519) B3413519
theorem B4323689 : Blo 1516955 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B2275691 : Blo 1516955 2275691 := bstep (se 1 (by rfl) ⟨1706768, by rfl⟩ : syracuseStep 2275691 = 3413537) B3413537
theorem B3414491 : Blo 1516955 3414491 := bstep (se 1 (by rfl) ⟨2560868, by rfl⟩ : syracuseStep 3414491 = 5121737) B5121737
theorem B4995571 : Blo 1516955 4995571 := bstep (se 1 (by rfl) ⟨3746678, by rfl⟩ : syracuseStep 4995571 = 7493357) B7493357
theorem B78821909 : Blo 1516955 78821909 := bstep (se 6 (by rfl) ⟨1847388, by rfl⟩ : syracuseStep 78821909 = 3694777) B3694777
theorem B2275919 : Blo 1516955 2275919 := bstep (se 1 (by rfl) ⟨1706939, by rfl⟩ : syracuseStep 2275919 = 3413879) B3413879
theorem B4102753 : Blo 1516955 4102753 := bstep (se 2 (by rfl) ⟨1538532, by rfl⟩ : syracuseStep 4102753 = 3077065) B3077065
theorem B3840635 : Blo 1516955 3840635 := bstep (se 1 (by rfl) ⟨2880476, by rfl⟩ : syracuseStep 3840635 = 5760953) B5760953
theorem B2276039 : Blo 1516955 2276039 := bstep (se 1 (by rfl) ⟨1707029, by rfl⟩ : syracuseStep 2276039 = 3414059) B3414059
theorem B2276201 : Blo 1516955 2276201 := bstep (se 2 (by rfl) ⟨853575, by rfl⟩ : syracuseStep 2276201 = 1707151) B1707151
theorem B3840929 : Blo 1516955 3840929 := bstep (se 2 (by rfl) ⟨1440348, by rfl⟩ : syracuseStep 3840929 = 2880697) B2880697
theorem B3414959 : Blo 1516955 3414959 := bstep (se 1 (by rfl) ⟨2561219, by rfl⟩ : syracuseStep 3414959 = 5122439) B5122439
theorem B2276279 : Blo 1516955 2276279 := bstep (se 1 (by rfl) ⟨1707209, by rfl⟩ : syracuseStep 2276279 = 3414419) B3414419
theorem B2431927 : Blo 1516955 2431927 := bstep (se 1 (by rfl) ⟨1823945, by rfl⟩ : syracuseStep 2431927 = 3647891) B3647891
theorem B2276315 : Blo 1516955 2276315 := bstep (se 1 (by rfl) ⟨1707236, by rfl⟩ : syracuseStep 2276315 = 3414473) B3414473
theorem B3415211 : Blo 1516955 3415211 := bstep (se 1 (by rfl) ⟨2561408, by rfl⟩ : syracuseStep 3415211 = 5122817) B5122817
theorem B2276783 : Blo 1516955 2276783 := bstep (se 1 (by rfl) ⟨1707587, by rfl⟩ : syracuseStep 2276783 = 3415175) B3415175
theorem B2276873 : Blo 1516955 2276873 := bstep (se 2 (by rfl) ⟨853827, by rfl⟩ : syracuseStep 2276873 = 1707655) B1707655
theorem B2276903 : Blo 1516955 2276903 := bstep (se 1 (by rfl) ⟨1707677, by rfl⟩ : syracuseStep 2276903 = 3415355) B3415355
theorem B2276987 : Blo 1516955 2276987 := bstep (se 1 (by rfl) ⟨1707740, by rfl⟩ : syracuseStep 2276987 = 3415481) B3415481
theorem B5471867 : Blo 1516955 5471867 := bstep (se 1 (by rfl) ⟨4103900, by rfl⟩ : syracuseStep 5471867 = 8207801) B8207801
theorem B8208017 : Blo 1516955 8208017 := bstep (se 2 (by rfl) ⟨3078006, by rfl⟩ : syracuseStep 8208017 = 6156013) B6156013
theorem B12967613 : Blo 1516955 12967613 := bstep (se 3 (by rfl) ⟨2431427, by rfl⟩ : syracuseStep 12967613 = 4862855) B4862855
theorem B3415751 : Blo 1516955 3415751 := bstep (se 1 (by rfl) ⟨2561813, by rfl⟩ : syracuseStep 3415751 = 5123627) B5123627
theorem B2277113 : Blo 1516955 2277113 := bstep (se 2 (by rfl) ⟨853917, by rfl⟩ : syracuseStep 2277113 = 1707835) B1707835
theorem B59121413 : Blo 1516955 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B2277215 : Blo 1516955 2277215 := bstep (se 1 (by rfl) ⟨1707911, by rfl⟩ : syracuseStep 2277215 = 3415823) B3415823
theorem B2277227 : Blo 1516955 2277227 := bstep (se 1 (by rfl) ⟨1707920, by rfl⟩ : syracuseStep 2277227 = 3415841) B3415841
theorem B2736091 : Blo 1516955 2736091 := bstep (se 1 (by rfl) ⟨2052068, by rfl⟩ : syracuseStep 2736091 = 4104137) B4104137
theorem B5120009 : Blo 1516955 5120009 := bstep (se 2 (by rfl) ⟨1920003, by rfl⟩ : syracuseStep 5120009 = 3840007) B3840007
theorem B7684307 : Blo 1516955 7684307 := bstep (se 1 (by rfl) ⟨5763230, by rfl⟩ : syracuseStep 7684307 = 11526461) B11526461
theorem B2277641 : Blo 1516955 2277641 := bstep (se 2 (by rfl) ⟨854115, by rfl⟩ : syracuseStep 2277641 = 1708231) B1708231
theorem B31138199 : Blo 1516955 31138199 := bstep (se 1 (by rfl) ⟨23353649, by rfl⟩ : syracuseStep 31138199 = 46707299) B46707299
theorem B6152705 : Blo 1516955 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B3842579 : Blo 1516955 3842579 := bstep (se 1 (by rfl) ⟨2881934, by rfl⟩ : syracuseStep 3842579 = 5763869) B5763869
theorem B6660761 : Blo 1516955 6660761 := bstep (se 2 (by rfl) ⟨2497785, by rfl⟩ : syracuseStep 6660761 = 4995571) B4995571
theorem B6480749 : Blo 1516955 6480749 := bstep (se 3 (by rfl) ⟨1215140, by rfl⟩ : syracuseStep 6480749 = 2430281) B2430281
theorem B3843035 : Blo 1516955 3843035 := bstep (se 1 (by rfl) ⟨2882276, by rfl⟩ : syracuseStep 3843035 = 5764553) B5764553
theorem B3646451 : Blo 1516955 3646451 := bstep (se 1 (by rfl) ⟨2734838, by rfl⟩ : syracuseStep 3646451 = 5469677) B5469677
theorem B19448855 : Blo 1516955 19448855 := bstep (se 1 (by rfl) ⟨14586641, by rfl⟩ : syracuseStep 19448855 = 29173283) B29173283
theorem B3843359 : Blo 1516955 3843359 := bstep (se 1 (by rfl) ⟨2882519, by rfl⟩ : syracuseStep 3843359 = 5765039) B5765039
theorem B6153515 : Blo 1516955 6153515 := bstep (se 1 (by rfl) ⟨4615136, by rfl⟩ : syracuseStep 6153515 = 9230273) B9230273
theorem B5842219 : Blo 1516955 5842219 := bstep (se 1 (by rfl) ⟨4381664, by rfl⟩ : syracuseStep 5842219 = 8763329) B8763329
theorem B1516967 : Blo 1516955 1516967 := bstep (se 1 (by rfl) ⟨1137725, by rfl⟩ : syracuseStep 1516967 = 2275451) B2275451
theorem B32826869 : Blo 1516955 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B1517051 : Blo 1516955 1517051 := bstep (se 1 (by rfl) ⟨1137788, by rfl⟩ : syracuseStep 1517051 = 2275577) B2275577
theorem B1517119 : Blo 1516955 1517119 := bstep (se 1 (by rfl) ⟨1137839, by rfl⟩ : syracuseStep 1517119 = 2275679) B2275679
theorem B1517127 : Blo 1516955 1517127 := bstep (se 1 (by rfl) ⟨1137845, by rfl⟩ : syracuseStep 1517127 = 2275691) B2275691
theorem B1517279 : Blo 1516955 1517279 := bstep (se 1 (by rfl) ⟨1137959, by rfl⟩ : syracuseStep 1517279 = 2275919) B2275919
theorem B1517359 : Blo 1516955 1517359 := bstep (se 1 (by rfl) ⟨1138019, by rfl⟩ : syracuseStep 1517359 = 2276039) B2276039
theorem B4613993 : Blo 1516955 4613993 := bstep (se 2 (by rfl) ⟨1730247, by rfl⟩ : syracuseStep 4613993 = 3460495) B3460495
theorem B1517467 : Blo 1516955 1517467 := bstep (se 1 (by rfl) ⟨1138100, by rfl⟩ : syracuseStep 1517467 = 2276201) B2276201
theorem B1517519 : Blo 1516955 1517519 := bstep (se 1 (by rfl) ⟨1138139, by rfl⟩ : syracuseStep 1517519 = 2276279) B2276279
theorem B1517543 : Blo 1516955 1517543 := bstep (se 1 (by rfl) ⟨1138157, by rfl⟩ : syracuseStep 1517543 = 2276315) B2276315
theorem B7014529 : Blo 1516955 7014529 := bstep (se 2 (by rfl) ⟨2630448, by rfl⟩ : syracuseStep 7014529 = 5260897) B5260897
theorem B1517855 : Blo 1516955 1517855 := bstep (se 1 (by rfl) ⟨1138391, by rfl⟩ : syracuseStep 1517855 = 2276783) B2276783
theorem B12970277 : Blo 1516955 12970277 := bstep (se 4 (by rfl) ⟨1215963, by rfl⟩ : syracuseStep 12970277 = 2431927) B2431927
theorem B1517915 : Blo 1516955 1517915 := bstep (se 1 (by rfl) ⟨1138436, by rfl⟩ : syracuseStep 1517915 = 2276873) B2276873
theorem B1517935 : Blo 1516955 1517935 := bstep (se 1 (by rfl) ⟨1138451, by rfl⟩ : syracuseStep 1517935 = 2276903) B2276903
theorem B1517991 : Blo 1516955 1517991 := bstep (se 1 (by rfl) ⟨1138493, by rfl⟩ : syracuseStep 1517991 = 2276987) B2276987
theorem B3647911 : Blo 1516955 3647911 := bstep (se 1 (by rfl) ⟨2735933, by rfl⟩ : syracuseStep 3647911 = 5471867) B5471867
theorem B8645075 : Blo 1516955 8645075 := bstep (se 1 (by rfl) ⟨6483806, by rfl⟩ : syracuseStep 8645075 = 12967613) B12967613
theorem B1518075 : Blo 1516955 1518075 := bstep (se 1 (by rfl) ⟨1138556, by rfl⟩ : syracuseStep 1518075 = 2277113) B2277113
theorem B39414275 : Blo 1516955 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B1518143 : Blo 1516955 1518143 := bstep (se 1 (by rfl) ⟨1138607, by rfl⟩ : syracuseStep 1518143 = 2277215) B2277215
theorem B1518151 : Blo 1516955 1518151 := bstep (se 1 (by rfl) ⟨1138613, by rfl⟩ : syracuseStep 1518151 = 2277227) B2277227
theorem B3648121 : Blo 1516955 3648121 := bstep (se 2 (by rfl) ⟨1368045, by rfl⟩ : syracuseStep 3648121 = 2736091) B2736091
theorem B1706719 : Blo 1516955 1706719 := bstep (se 1 (by rfl) ⟨1280039, by rfl⟩ : syracuseStep 1706719 = 2560079) B2560079
theorem B1518303 : Blo 1516955 1518303 := bstep (se 1 (by rfl) ⟨1138727, by rfl⟩ : syracuseStep 1518303 = 2277455) B2277455
theorem B1518383 : Blo 1516955 1518383 := bstep (se 1 (by rfl) ⟨1138787, by rfl⟩ : syracuseStep 1518383 = 2277575) B2277575
theorem B6237307 : Blo 1516955 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B5123195 : Blo 1516955 5123195 := bstep (se 1 (by rfl) ⟨3842396, by rfl⟩ : syracuseStep 5123195 = 7684793) B7684793
theorem B1920287 : Blo 1516955 1920287 := bstep (se 1 (by rfl) ⟨1440215, by rfl⟩ : syracuseStep 1920287 = 2880431) B2880431
theorem B1707295 : Blo 1516955 1707295 := bstep (se 1 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 1707295 = 2560943) B2560943
theorem B5762441 : Blo 1516955 5762441 := bstep (se 2 (by rfl) ⟨2160915, by rfl⟩ : syracuseStep 5762441 = 4321831) B4321831
theorem B5123465 : Blo 1516955 5123465 := bstep (se 2 (by rfl) ⟨1921299, by rfl⟩ : syracuseStep 5123465 = 3842599) B3842599
theorem B479768021 : Blo 1516955 479768021 := bstep (se 7 (by rfl) ⟨5622281, by rfl⟩ : syracuseStep 479768021 = 11244563) B11244563
theorem B1707583 : Blo 1516955 1707583 := bstep (se 1 (by rfl) ⟨1280687, by rfl⟩ : syracuseStep 1707583 = 2561375) B2561375
theorem B9719507 : Blo 1516955 9719507 := bstep (se 1 (by rfl) ⟨7289630, by rfl⟩ : syracuseStep 9719507 = 14579261) B14579261
theorem B5467945 : Blo 1516955 5467945 := bstep (se 2 (by rfl) ⟨2050479, by rfl⟩ : syracuseStep 5467945 = 4100959) B4100959
theorem B5123897 : Blo 1516955 5123897 := bstep (se 2 (by rfl) ⟨1921461, by rfl⟩ : syracuseStep 5123897 = 3842923) B3842923
theorem B8204105 : Blo 1516955 8204105 := bstep (se 2 (by rfl) ⟨3076539, by rfl⟩ : syracuseStep 8204105 = 6153079) B6153079
theorem B2052047 : Blo 1516955 2052047 := bstep (se 1 (by rfl) ⟨1539035, by rfl⟩ : syracuseStep 2052047 = 3078071) B3078071
theorem B7893011 : Blo 1516955 7893011 := bstep (se 1 (by rfl) ⟨5919758, by rfl⟩ : syracuseStep 7893011 = 11839517) B11839517
theorem B9728171 : Blo 1516955 9728171 := bstep (se 1 (by rfl) ⟨7296128, by rfl⟩ : syracuseStep 9728171 = 14592257) B14592257
theorem B52547939 : Blo 1516955 52547939 := bstep (se 1 (by rfl) ⟨39410954, by rfl⟩ : syracuseStep 52547939 = 78821909) B78821909
theorem B2560423 : Blo 1516955 2560423 := bstep (se 1 (by rfl) ⟨1920317, by rfl⟩ : syracuseStep 2560423 = 3840635) B3840635
theorem B2560585 : Blo 1516955 2560585 := bstep (se 2 (by rfl) ⟨960219, by rfl⟩ : syracuseStep 2560585 = 1920439) B1920439
theorem B2560619 : Blo 1516955 2560619 := bstep (se 1 (by rfl) ⟨1920464, by rfl⟩ : syracuseStep 2560619 = 3840929) B3840929
theorem B5124761 : Blo 1516955 5124761 := bstep (se 2 (by rfl) ⟨1921785, by rfl⟩ : syracuseStep 5124761 = 3843571) B3843571
theorem B291877739 : Blo 1516955 291877739 := bstep (se 1 (by rfl) ⟨218908304, by rfl⟩ : syracuseStep 291877739 = 437816609) B437816609
theorem B17527799 : Blo 1516955 17527799 := bstep (se 1 (by rfl) ⟨13145849, by rfl⟩ : syracuseStep 17527799 = 26291699) B26291699
theorem B25924697 : Blo 1516955 25924697 := bstep (se 2 (by rfl) ⟨9721761, by rfl⟩ : syracuseStep 25924697 = 19443523) B19443523
theorem B4322447 : Blo 1516955 4322447 := bstep (se 1 (by rfl) ⟨3241835, by rfl⟩ : syracuseStep 4322447 = 6483671) B6483671
theorem B3413447 : Blo 1516955 3413447 := bstep (se 1 (by rfl) ⟨2560085, by rfl⟩ : syracuseStep 3413447 = 5120171) B5120171
theorem B4101715 : Blo 1516955 4101715 := bstep (se 1 (by rfl) ⟨3076286, by rfl⟩ : syracuseStep 4101715 = 6152573) B6152573
theorem B3413807 : Blo 1516955 3413807 := bstep (se 1 (by rfl) ⟨2560355, by rfl⟩ : syracuseStep 3413807 = 5120711) B5120711
theorem B2881327 : Blo 1516955 2881327 := bstep (se 1 (by rfl) ⟨2160995, by rfl⟩ : syracuseStep 2881327 = 4321991) B4321991
theorem B18708317 : Blo 1516955 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B2881487 : Blo 1516955 2881487 := bstep (se 1 (by rfl) ⟨2161115, by rfl⟩ : syracuseStep 2881487 = 4322231) B4322231
theorem B98449445 : Blo 1516955 98449445 := bstep (se 4 (by rfl) ⟨9229635, by rfl⟩ : syracuseStep 98449445 = 18459271) B18459271
theorem B2275433 : Blo 1516955 2275433 := bstep (se 2 (by rfl) ⟨853287, by rfl⟩ : syracuseStep 2275433 = 1706575) B1706575
theorem B2594921 : Blo 1516955 2594921 := bstep (se 2 (by rfl) ⟨973095, by rfl⟩ : syracuseStep 2594921 = 1946191) B1946191
theorem B5470337 : Blo 1516955 5470337 := bstep (se 2 (by rfl) ⟨2051376, by rfl⟩ : syracuseStep 5470337 = 4102753) B4102753
theorem B7788739 : Blo 1516955 7788739 := bstep (se 1 (by rfl) ⟨5841554, by rfl⟩ : syracuseStep 7788739 = 11683109) B11683109
theorem B22173925 : Blo 1516955 22173925 := bstep (se 4 (by rfl) ⟨2078805, by rfl⟩ : syracuseStep 22173925 = 4157611) B4157611
theorem B4864265 : Blo 1516955 4864265 := bstep (se 2 (by rfl) ⟨1824099, by rfl⟩ : syracuseStep 4864265 = 3648199) B3648199
theorem B2562313 : Blo 1516955 2562313 := bstep (se 2 (by rfl) ⟨960867, by rfl⟩ : syracuseStep 2562313 = 1921735) B1921735
theorem B3840281 : Blo 1516955 3840281 := bstep (se 2 (by rfl) ⟨1440105, by rfl⟩ : syracuseStep 3840281 = 2880211) B2880211
theorem B3414383 : Blo 1516955 3414383 := bstep (se 1 (by rfl) ⟨2560787, by rfl⟩ : syracuseStep 3414383 = 5121575) B5121575
theorem B4864367 : Blo 1516955 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B2275751 : Blo 1516955 2275751 := bstep (se 1 (by rfl) ⟨1706813, by rfl⟩ : syracuseStep 2275751 = 3413627) B3413627
theorem B3414455 : Blo 1516955 3414455 := bstep (se 1 (by rfl) ⟨2560841, by rfl⟩ : syracuseStep 3414455 = 5121683) B5121683
theorem B4102625 : Blo 1516955 4102625 := bstep (se 2 (by rfl) ⟨1538484, by rfl⟩ : syracuseStep 4102625 = 3076969) B3076969
theorem B8641019 : Blo 1516955 8641019 := bstep (se 1 (by rfl) ⟨6480764, by rfl⟩ : syracuseStep 8641019 = 12961529) B12961529
theorem B2275835 : Blo 1516955 2275835 := bstep (se 1 (by rfl) ⟨1706876, by rfl⟩ : syracuseStep 2275835 = 3413753) B3413753
theorem B3414599 : Blo 1516955 3414599 := bstep (se 1 (by rfl) ⟨2560949, by rfl⟩ : syracuseStep 3414599 = 5121899) B5121899
theorem B8002127 : Blo 1516955 8002127 := bstep (se 1 (by rfl) ⟨6001595, by rfl⟩ : syracuseStep 8002127 = 12003191) B12003191
theorem B3414635 : Blo 1516955 3414635 := bstep (se 1 (by rfl) ⟨2560976, by rfl⟩ : syracuseStep 3414635 = 5121953) B5121953
theorem B2431595 : Blo 1516955 2431595 := bstep (se 1 (by rfl) ⟨1823696, by rfl⟩ : syracuseStep 2431595 = 3647393) B3647393
theorem B2882155 : Blo 1516955 2882155 := bstep (se 1 (by rfl) ⟨2161616, by rfl⟩ : syracuseStep 2882155 = 4323233) B4323233
theorem B2275961 : Blo 1516955 2275961 := bstep (se 2 (by rfl) ⟨853485, by rfl⟩ : syracuseStep 2275961 = 1706971) B1706971
theorem B2276015 : Blo 1516955 2276015 := bstep (se 1 (by rfl) ⟨1707011, by rfl⟩ : syracuseStep 2276015 = 3414023) B3414023
theorem B2276063 : Blo 1516955 2276063 := bstep (se 1 (by rfl) ⟨1707047, by rfl⟩ : syracuseStep 2276063 = 3414095) B3414095
theorem B1620815 : Blo 1516955 1620815 := bstep (se 1 (by rfl) ⟨1215611, by rfl⟩ : syracuseStep 1620815 = 2431223) B2431223
theorem B2882459 : Blo 1516955 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B2276327 : Blo 1516955 2276327 := bstep (se 1 (by rfl) ⟨1707245, by rfl⟩ : syracuseStep 2276327 = 3414491) B3414491
theorem B3415031 : Blo 1516955 3415031 := bstep (se 1 (by rfl) ⟨2561273, by rfl⟩ : syracuseStep 3415031 = 5122547) B5122547
theorem B3841121 : Blo 1516955 3841121 := bstep (se 2 (by rfl) ⟨1440420, by rfl⟩ : syracuseStep 3841121 = 2880841) B2880841
theorem B8207581 : Blo 1516955 8207581 := bstep (se 3 (by rfl) ⟨1538921, by rfl⟩ : syracuseStep 8207581 = 3077843) B3077843
theorem B2276585 : Blo 1516955 2276585 := bstep (se 2 (by rfl) ⟨853719, by rfl⟩ : syracuseStep 2276585 = 1707439) B1707439
theorem B2276639 : Blo 1516955 2276639 := bstep (se 1 (by rfl) ⟨1707479, by rfl⟩ : syracuseStep 2276639 = 3414959) B3414959
theorem B3415391 : Blo 1516955 3415391 := bstep (se 1 (by rfl) ⟨2561543, by rfl⟩ : syracuseStep 3415391 = 5123087) B5123087
theorem B2276807 : Blo 1516955 2276807 := bstep (se 1 (by rfl) ⟨1707605, by rfl⟩ : syracuseStep 2276807 = 3415211) B3415211
theorem B27704825 : Blo 1516955 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B39435893 : Blo 1516955 39435893 := bstep (se 5 (by rfl) ⟨1848557, by rfl⟩ : syracuseStep 39435893 = 3697115) B3697115
theorem B3415787 : Blo 1516955 3415787 := bstep (se 1 (by rfl) ⟨2561840, by rfl⟩ : syracuseStep 3415787 = 5123681) B5123681
theorem B5472011 : Blo 1516955 5472011 := bstep (se 1 (by rfl) ⟨4104008, by rfl⟩ : syracuseStep 5472011 = 8208017) B8208017
theorem B2277161 : Blo 1516955 2277161 := bstep (se 2 (by rfl) ⟨853935, by rfl⟩ : syracuseStep 2277161 = 1707871) B1707871
theorem B2277167 : Blo 1516955 2277167 := bstep (se 1 (by rfl) ⟨1707875, by rfl⟩ : syracuseStep 2277167 = 3415751) B3415751
theorem B3415913 : Blo 1516955 3415913 := bstep (se 2 (by rfl) ⟨1280967, by rfl⟩ : syracuseStep 3415913 = 2561935) B2561935
theorem B5119901 : Blo 1516955 5119901 := bstep (se 3 (by rfl) ⟨959981, by rfl⟩ : syracuseStep 5119901 = 1919963) B1919963
theorem B20758799 : Blo 1516955 20758799 := bstep (se 1 (by rfl) ⟨15569099, by rfl⟩ : syracuseStep 20758799 = 31138199) B31138199
theorem B29565233 : Blo 1516955 29565233 := bstep (se 2 (by rfl) ⟨11086962, by rfl⟩ : syracuseStep 29565233 = 22173925) B22173925
theorem B3416417 : Blo 1516955 3416417 := bstep (se 2 (by rfl) ⟨1281156, by rfl⟩ : syracuseStep 3416417 = 2562313) B2562313
theorem B3416507 : Blo 1516955 3416507 := bstep (se 1 (by rfl) ⟨2562380, by rfl⟩ : syracuseStep 3416507 = 5124761) B5124761
theorem B194585159 : Blo 1516955 194585159 := bstep (se 1 (by rfl) ⟨145938869, by rfl⟩ : syracuseStep 194585159 = 291877739) B291877739
theorem B19456645 : Blo 1516955 19456645 := bstep (se 4 (by rfl) ⟨1824060, by rfl⟩ : syracuseStep 19456645 = 3648121) B3648121
theorem B5120765 : Blo 1516955 5120765 := bstep (se 3 (by rfl) ⟨960143, by rfl⟩ : syracuseStep 5120765 = 1920287) B1920287
theorem B3842873 : Blo 1516955 3842873 := bstep (se 2 (by rfl) ⟨1441077, by rfl⟩ : syracuseStep 3842873 = 2882155) B2882155
theorem B1516955 : Blo 1516955 1516955 := bstep (se 1 (by rfl) ⟨1137716, by rfl⟩ : syracuseStep 1516955 = 2275433) B2275433
theorem B3646891 : Blo 1516955 3646891 := bstep (se 1 (by rfl) ⟨2735168, by rfl⟩ : syracuseStep 3646891 = 5470337) B5470337
theorem B1517167 : Blo 1516955 1517167 := bstep (se 1 (by rfl) ⟨1137875, by rfl⟩ : syracuseStep 1517167 = 2275751) B2275751
theorem B5760679 : Blo 1516955 5760679 := bstep (se 1 (by rfl) ⟨4320509, by rfl⟩ : syracuseStep 5760679 = 8641019) B8641019
theorem B1517223 : Blo 1516955 1517223 := bstep (se 1 (by rfl) ⟨1137917, by rfl⟩ : syracuseStep 1517223 = 2275835) B2275835
theorem B5334751 : Blo 1516955 5334751 := bstep (se 1 (by rfl) ⟨4001063, by rfl⟩ : syracuseStep 5334751 = 8002127) B8002127
theorem B1517307 : Blo 1516955 1517307 := bstep (se 1 (by rfl) ⟨1137980, by rfl⟩ : syracuseStep 1517307 = 2275961) B2275961
theorem B1517343 : Blo 1516955 1517343 := bstep (se 1 (by rfl) ⟨1138007, by rfl⟩ : syracuseStep 1517343 = 2276015) B2276015
theorem B1517375 : Blo 1516955 1517375 := bstep (se 1 (by rfl) ⟨1138031, by rfl⟩ : syracuseStep 1517375 = 2276063) B2276063
theorem B1517551 : Blo 1516955 1517551 := bstep (se 1 (by rfl) ⟨1138163, by rfl⟩ : syracuseStep 1517551 = 2276327) B2276327
theorem B1517723 : Blo 1516955 1517723 := bstep (se 1 (by rfl) ⟨1138292, by rfl⟩ : syracuseStep 1517723 = 2276585) B2276585
theorem B1517759 : Blo 1516955 1517759 := bstep (se 1 (by rfl) ⟨1138319, by rfl⟩ : syracuseStep 1517759 = 2276639) B2276639
theorem B1517871 : Blo 1516955 1517871 := bstep (se 1 (by rfl) ⟨1138403, by rfl⟩ : syracuseStep 1517871 = 2276807) B2276807
theorem B26290595 : Blo 1516955 26290595 := bstep (se 1 (by rfl) ⟨19717946, by rfl⟩ : syracuseStep 26290595 = 39435893) B39435893
theorem B3648007 : Blo 1516955 3648007 := bstep (se 1 (by rfl) ⟨2736005, by rfl⟩ : syracuseStep 3648007 = 5472011) B5472011
theorem B1518107 : Blo 1516955 1518107 := bstep (se 1 (by rfl) ⟨1138580, by rfl⟩ : syracuseStep 1518107 = 2277161) B2277161
theorem B1518111 : Blo 1516955 1518111 := bstep (se 1 (by rfl) ⟨1138583, by rfl⟩ : syracuseStep 1518111 = 2277167) B2277167
theorem B21048029 : Blo 1516955 21048029 := bstep (se 3 (by rfl) ⟨3946505, by rfl⟩ : syracuseStep 21048029 = 7893011) B7893011
theorem B5122871 : Blo 1516955 5122871 := bstep (se 1 (by rfl) ⟨3842153, by rfl⟩ : syracuseStep 5122871 = 7684307) B7684307
theorem B1518427 : Blo 1516955 1518427 := bstep (se 1 (by rfl) ⟨1138820, by rfl⟩ : syracuseStep 1518427 = 2277641) B2277641
theorem B35031959 : Blo 1516955 35031959 := bstep (se 1 (by rfl) ⟨26273969, by rfl⟩ : syracuseStep 35031959 = 52547939) B52547939
theorem B1707079 : Blo 1516955 1707079 := bstep (se 1 (by rfl) ⟨1280309, by rfl⟩ : syracuseStep 1707079 = 2560619) B2560619
theorem B4320499 : Blo 1516955 4320499 := bstep (se 1 (by rfl) ⟨3240374, by rfl⟩ : syracuseStep 4320499 = 6480749) B6480749
theorem B21884579 : Blo 1516955 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B12472211 : Blo 1516955 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B3075995 : Blo 1516955 3075995 := bstep (se 1 (by rfl) ⟨2306996, by rfl⟩ : syracuseStep 3075995 = 4613993) B4613993
theorem B1920991 : Blo 1516955 1920991 := bstep (se 1 (by rfl) ⟨1440743, by rfl⟩ : syracuseStep 1920991 = 2881487) B2881487
theorem B2560187 : Blo 1516955 2560187 := bstep (se 1 (by rfl) ⟨1920140, by rfl⟩ : syracuseStep 2560187 = 3840281) B3840281
theorem B8646851 : Blo 1516955 8646851 := bstep (se 1 (by rfl) ⟨6485138, by rfl⟩ : syracuseStep 8646851 = 12970277) B12970277
theorem B5763383 : Blo 1516955 5763383 := bstep (se 1 (by rfl) ⟨4322537, by rfl⟩ : syracuseStep 5763383 = 8645075) B8645075
theorem B26276183 : Blo 1516955 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B1921639 : Blo 1516955 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B2560747 : Blo 1516955 2560747 := bstep (se 1 (by rfl) ⟨1920560, by rfl⟩ : syracuseStep 2560747 = 3841121) B3841121
theorem B5468953 : Blo 1516955 5468953 := bstep (se 2 (by rfl) ⟨2050857, by rfl⟩ : syracuseStep 5468953 = 4101715) B4101715
theorem B4322173 : Blo 1516955 4322173 := bstep (se 3 (by rfl) ⟨810407, by rfl⟩ : syracuseStep 4322173 = 1620815) B1620815
theorem B319845347 : Blo 1516955 319845347 := bstep (se 1 (by rfl) ⟨239884010, by rfl⟩ : syracuseStep 319845347 = 479768021) B479768021
theorem B18469883 : Blo 1516955 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B5469403 : Blo 1516955 5469403 := bstep (se 1 (by rfl) ⟨4102052, by rfl⟩ : syracuseStep 5469403 = 8204105) B8204105
theorem B3413267 : Blo 1516955 3413267 := bstep (se 1 (by rfl) ⟨2559950, by rfl⟩ : syracuseStep 3413267 = 5119901) B5119901
theorem B46740797 : Blo 1516955 46740797 := bstep (se 3 (by rfl) ⟨8763899, by rfl⟩ : syracuseStep 46740797 = 17527799) B17527799
theorem B3413339 : Blo 1516955 3413339 := bstep (se 1 (by rfl) ⟨2560004, by rfl⟩ : syracuseStep 3413339 = 5120009) B5120009
theorem B6485447 : Blo 1516955 6485447 := bstep (se 1 (by rfl) ⟨4864085, by rfl⟩ : syracuseStep 6485447 = 9728171) B9728171
theorem B10384985 : Blo 1516955 10384985 := bstep (se 2 (by rfl) ⟨3894369, by rfl⟩ : syracuseStep 10384985 = 7788739) B7788739
theorem B6919789 : Blo 1516955 6919789 := bstep (se 3 (by rfl) ⟨1297460, by rfl⟩ : syracuseStep 6919789 = 2594921) B2594921
theorem B4101803 : Blo 1516955 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B2561719 : Blo 1516955 2561719 := bstep (se 1 (by rfl) ⟨1921289, by rfl⟩ : syracuseStep 2561719 = 3842579) B3842579
theorem B3413897 : Blo 1516955 3413897 := bstep (se 2 (by rfl) ⟨1280211, by rfl⟩ : syracuseStep 3413897 = 2560423) B2560423
theorem B4863881 : Blo 1516955 4863881 := bstep (se 2 (by rfl) ⟨1823955, by rfl⟩ : syracuseStep 4863881 = 3647911) B3647911
theorem B33265637 : Blo 1516955 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B2562023 : Blo 1516955 2562023 := bstep (se 1 (by rfl) ⟨1921517, by rfl⟩ : syracuseStep 2562023 = 3843035) B3843035
theorem B2430967 : Blo 1516955 2430967 := bstep (se 1 (by rfl) ⟨1823225, by rfl⟩ : syracuseStep 2430967 = 3646451) B3646451
theorem B37410821 : Blo 1516955 37410821 := bstep (se 4 (by rfl) ⟨3507264, by rfl⟩ : syracuseStep 37410821 = 7014529) B7014529
theorem B12965903 : Blo 1516955 12965903 := bstep (se 1 (by rfl) ⟨9724427, by rfl⟩ : syracuseStep 12965903 = 19448855) B19448855
theorem B17283131 : Blo 1516955 17283131 := bstep (se 1 (by rfl) ⟨12962348, by rfl⟩ : syracuseStep 17283131 = 25924697) B25924697
theorem B2881631 : Blo 1516955 2881631 := bstep (se 1 (by rfl) ⟨2161223, by rfl⟩ : syracuseStep 2881631 = 4322447) B4322447
theorem B3414113 : Blo 1516955 3414113 := bstep (se 2 (by rfl) ⟨1280292, by rfl⟩ : syracuseStep 3414113 = 2560585) B2560585
theorem B2562239 : Blo 1516955 2562239 := bstep (se 1 (by rfl) ⟨1921679, by rfl⟩ : syracuseStep 2562239 = 3843359) B3843359
theorem B4102343 : Blo 1516955 4102343 := bstep (se 1 (by rfl) ⟨3076757, by rfl⟩ : syracuseStep 4102343 = 6153515) B6153515
theorem B2275625 : Blo 1516955 2275625 := bstep (se 2 (by rfl) ⟨853359, by rfl⟩ : syracuseStep 2275625 = 1706719) B1706719
theorem B2275631 : Blo 1516955 2275631 := bstep (se 1 (by rfl) ⟨1706723, by rfl⟩ : syracuseStep 2275631 = 3413447) B3413447
theorem B2275871 : Blo 1516955 2275871 := bstep (se 1 (by rfl) ⟨1706903, by rfl⟩ : syracuseStep 2275871 = 3413807) B3413807
theorem B65632963 : Blo 1516955 65632963 := bstep (se 1 (by rfl) ⟨49224722, by rfl⟩ : syracuseStep 65632963 = 98449445) B98449445
theorem B3242843 : Blo 1516955 3242843 := bstep (se 1 (by rfl) ⟨2432132, by rfl⟩ : syracuseStep 3242843 = 4864265) B4864265
theorem B2276255 : Blo 1516955 2276255 := bstep (se 1 (by rfl) ⟨1707191, by rfl⟩ : syracuseStep 2276255 = 3414383) B3414383
theorem B3242911 : Blo 1516955 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B71048117 : Blo 1516955 71048117 := bstep (se 5 (by rfl) ⟨3330380, by rfl⟩ : syracuseStep 71048117 = 6660761) B6660761
theorem B2276303 : Blo 1516955 2276303 := bstep (se 1 (by rfl) ⟨1707227, by rfl⟩ : syracuseStep 2276303 = 3414455) B3414455
theorem B10943441 : Blo 1516955 10943441 := bstep (se 2 (by rfl) ⟨4103790, by rfl⟩ : syracuseStep 10943441 = 8207581) B8207581
theorem B2735083 : Blo 1516955 2735083 := bstep (se 1 (by rfl) ⟨2051312, by rfl⟩ : syracuseStep 2735083 = 4102625) B4102625
theorem B2276393 : Blo 1516955 2276393 := bstep (se 2 (by rfl) ⟨853647, by rfl⟩ : syracuseStep 2276393 = 1707295) B1707295
theorem B2276399 : Blo 1516955 2276399 := bstep (se 1 (by rfl) ⟨1707299, by rfl⟩ : syracuseStep 2276399 = 3414599) B3414599
theorem B7789625 : Blo 1516955 7789625 := bstep (se 2 (by rfl) ⟨2921109, by rfl⟩ : syracuseStep 7789625 = 5842219) B5842219
theorem B2276423 : Blo 1516955 2276423 := bstep (se 1 (by rfl) ⟨1707317, by rfl⟩ : syracuseStep 2276423 = 3414635) B3414635
theorem B1621063 : Blo 1516955 1621063 := bstep (se 1 (by rfl) ⟨1215797, by rfl⟩ : syracuseStep 1621063 = 2431595) B2431595
theorem B2276687 : Blo 1516955 2276687 := bstep (se 1 (by rfl) ⟨1707515, by rfl⟩ : syracuseStep 2276687 = 3415031) B3415031
theorem B3415463 : Blo 1516955 3415463 := bstep (se 1 (by rfl) ⟨2561597, by rfl⟩ : syracuseStep 3415463 = 5123195) B5123195
theorem B2276777 : Blo 1516955 2276777 := bstep (se 2 (by rfl) ⟨853791, by rfl⟩ : syracuseStep 2276777 = 1707583) B1707583
theorem B2276927 : Blo 1516955 2276927 := bstep (se 1 (by rfl) ⟨1707695, by rfl⟩ : syracuseStep 2276927 = 3415391) B3415391
theorem B3841627 : Blo 1516955 3841627 := bstep (se 1 (by rfl) ⟨2881220, by rfl⟩ : syracuseStep 3841627 = 5762441) B5762441
theorem B3415643 : Blo 1516955 3415643 := bstep (se 1 (by rfl) ⟨2561732, by rfl⟩ : syracuseStep 3415643 = 5123465) B5123465
theorem B7290593 : Blo 1516955 7290593 := bstep (se 2 (by rfl) ⟨2733972, by rfl⟩ : syracuseStep 7290593 = 5467945) B5467945
theorem B3841769 : Blo 1516955 3841769 := bstep (se 2 (by rfl) ⟨1440663, by rfl⟩ : syracuseStep 3841769 = 2881327) B2881327
theorem B6479671 : Blo 1516955 6479671 := bstep (se 1 (by rfl) ⟨4859753, by rfl⟩ : syracuseStep 6479671 = 9719507) B9719507
theorem B2277191 : Blo 1516955 2277191 := bstep (se 1 (by rfl) ⟨1707893, by rfl⟩ : syracuseStep 2277191 = 3415787) B3415787
theorem B3415931 : Blo 1516955 3415931 := bstep (se 1 (by rfl) ⟨2561948, by rfl⟩ : syracuseStep 3415931 = 5123897) B5123897
theorem B5472125 : Blo 1516955 5472125 := bstep (se 3 (by rfl) ⟨1026023, by rfl⟩ : syracuseStep 5472125 = 2052047) B2052047
theorem B2277275 : Blo 1516955 2277275 := bstep (se 1 (by rfl) ⟨1707956, by rfl⟩ : syracuseStep 2277275 = 3415913) B3415913
theorem B19710155 : Blo 1516955 19710155 := bstep (se 1 (by rfl) ⟨14782616, by rfl⟩ : syracuseStep 19710155 = 29565233) B29565233
theorem B3842255 : Blo 1516955 3842255 := bstep (se 1 (by rfl) ⟨2881691, by rfl⟩ : syracuseStep 3842255 = 5763383) B5763383
theorem B2277611 : Blo 1516955 2277611 := bstep (se 1 (by rfl) ⟨1708208, by rfl⟩ : syracuseStep 2277611 = 3416417) B3416417
theorem B2277671 : Blo 1516955 2277671 := bstep (se 1 (by rfl) ⟨1708253, by rfl⟩ : syracuseStep 2277671 = 3416507) B3416507
theorem B213230231 : Blo 1516955 213230231 := bstep (se 1 (by rfl) ⟨159922673, by rfl⟩ : syracuseStep 213230231 = 319845347) B319845347
theorem B12313255 : Blo 1516955 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B7291937 : Blo 1516955 7291937 := bstep (se 2 (by rfl) ⟨2734476, by rfl⟩ : syracuseStep 7291937 = 5468953) B5468953
theorem B6923323 : Blo 1516955 6923323 := bstep (se 1 (by rfl) ⟨5192492, by rfl⟩ : syracuseStep 6923323 = 10384985) B10384985
theorem B28452005 : Blo 1516955 28452005 := bstep (se 4 (by rfl) ⟨2667375, by rfl⟩ : syracuseStep 28452005 = 5334751) B5334751
theorem B3646777 : Blo 1516955 3646777 := bstep (se 2 (by rfl) ⟨1367541, by rfl⟩ : syracuseStep 3646777 = 2735083) B2735083
theorem B22177091 : Blo 1516955 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B8643935 : Blo 1516955 8643935 := bstep (se 1 (by rfl) ⟨6482951, by rfl⟩ : syracuseStep 8643935 = 12965903) B12965903
theorem B1517083 : Blo 1516955 1517083 := bstep (se 1 (by rfl) ⟨1137812, by rfl⟩ : syracuseStep 1517083 = 2275625) B2275625
theorem B1517087 : Blo 1516955 1517087 := bstep (se 1 (by rfl) ⟨1137815, by rfl⟩ : syracuseStep 1517087 = 2275631) B2275631
theorem B7292537 : Blo 1516955 7292537 := bstep (se 2 (by rfl) ⟨2734701, by rfl⟩ : syracuseStep 7292537 = 5469403) B5469403
theorem B5760665 : Blo 1516955 5760665 := bstep (se 2 (by rfl) ⟨2160249, by rfl⟩ : syracuseStep 5760665 = 4320499) B4320499
theorem B1517247 : Blo 1516955 1517247 := bstep (se 1 (by rfl) ⟨1137935, by rfl⟩ : syracuseStep 1517247 = 2275871) B2275871
theorem B1517503 : Blo 1516955 1517503 := bstep (se 1 (by rfl) ⟨1138127, by rfl⟩ : syracuseStep 1517503 = 2276255) B2276255
theorem B1517535 : Blo 1516955 1517535 := bstep (se 1 (by rfl) ⟨1138151, by rfl⟩ : syracuseStep 1517535 = 2276303) B2276303
theorem B1517595 : Blo 1516955 1517595 := bstep (se 1 (by rfl) ⟨1138196, by rfl⟩ : syracuseStep 1517595 = 2276393) B2276393
theorem B1517599 : Blo 1516955 1517599 := bstep (se 1 (by rfl) ⟨1138199, by rfl⟩ : syracuseStep 1517599 = 2276399) B2276399
theorem B1517615 : Blo 1516955 1517615 := bstep (se 1 (by rfl) ⟨1138211, by rfl⟩ : syracuseStep 1517615 = 2276423) B2276423
theorem B5122169 : Blo 1516955 5122169 := bstep (se 2 (by rfl) ⟨1920813, by rfl⟩ : syracuseStep 5122169 = 3841627) B3841627
theorem B9226385 : Blo 1516955 9226385 := bstep (se 2 (by rfl) ⟨3459894, by rfl⟩ : syracuseStep 9226385 = 6919789) B6919789
theorem B1517791 : Blo 1516955 1517791 := bstep (se 1 (by rfl) ⟨1138343, by rfl⟩ : syracuseStep 1517791 = 2276687) B2276687
theorem B1517851 : Blo 1516955 1517851 := bstep (se 1 (by rfl) ⟨1138388, by rfl⟩ : syracuseStep 1517851 = 2276777) B2276777
theorem B1517951 : Blo 1516955 1517951 := bstep (se 1 (by rfl) ⟨1138463, by rfl⟩ : syracuseStep 1517951 = 2276927) B2276927
theorem B8202653 : Blo 1516955 8202653 := bstep (se 3 (by rfl) ⟨1537997, by rfl⟩ : syracuseStep 8202653 = 3075995) B3075995
theorem B4860395 : Blo 1516955 4860395 := bstep (se 1 (by rfl) ⟨3645296, by rfl⟩ : syracuseStep 4860395 = 7290593) B7290593
theorem B1518127 : Blo 1516955 1518127 := bstep (se 1 (by rfl) ⟨1138595, by rfl⟩ : syracuseStep 1518127 = 2277191) B2277191
theorem B3648083 : Blo 1516955 3648083 := bstep (se 1 (by rfl) ⟨2736062, by rfl⟩ : syracuseStep 3648083 = 5472125) B5472125
theorem B1518183 : Blo 1516955 1518183 := bstep (se 1 (by rfl) ⟨1138637, by rfl⟩ : syracuseStep 1518183 = 2277275) B2277275
theorem B1706791 : Blo 1516955 1706791 := bstep (se 1 (by rfl) ⟨1280093, by rfl⟩ : syracuseStep 1706791 = 2560187) B2560187
theorem B17517455 : Blo 1516955 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B129723439 : Blo 1516955 129723439 := bstep (se 1 (by rfl) ⟨97292579, by rfl⟩ : syracuseStep 129723439 = 194585159) B194585159
theorem B55356797 : Blo 1516955 55356797 := bstep (se 3 (by rfl) ⟨10379399, by rfl⟩ : syracuseStep 55356797 = 20758799) B20758799
theorem B87510617 : Blo 1516955 87510617 := bstep (se 2 (by rfl) ⟨32816481, by rfl⟩ : syracuseStep 87510617 = 65632963) B65632963
theorem B5762897 : Blo 1516955 5762897 := bstep (se 2 (by rfl) ⟨2161086, by rfl⟩ : syracuseStep 5762897 = 4322173) B4322173
theorem B1708015 : Blo 1516955 1708015 := bstep (se 1 (by rfl) ⟨1281011, by rfl⟩ : syracuseStep 1708015 = 2562023) B2562023
theorem B24940547 : Blo 1516955 24940547 := bstep (se 1 (by rfl) ⟨18705410, by rfl⟩ : syracuseStep 24940547 = 37410821) B37410821
theorem B11522087 : Blo 1516955 11522087 := bstep (se 1 (by rfl) ⟨8641565, by rfl⟩ : syracuseStep 11522087 = 17283131) B17283131
theorem B1921087 : Blo 1516955 1921087 := bstep (se 1 (by rfl) ⟨1440815, by rfl⟩ : syracuseStep 1921087 = 2881631) B2881631
theorem B1708159 : Blo 1516955 1708159 := bstep (se 1 (by rfl) ⟨1281119, by rfl⟩ : syracuseStep 1708159 = 2562239) B2562239
theorem B17527063 : Blo 1516955 17527063 := bstep (se 1 (by rfl) ⟨13145297, by rfl⟩ : syracuseStep 17527063 = 26290595) B26290595
theorem B4862521 : Blo 1516955 4862521 := bstep (se 2 (by rfl) ⟨1823445, by rfl⟩ : syracuseStep 4862521 = 3646891) B3646891
theorem B7295627 : Blo 1516955 7295627 := bstep (se 1 (by rfl) ⟨5471720, by rfl⟩ : syracuseStep 7295627 = 10943441) B10943441
theorem B7680905 : Blo 1516955 7680905 := bstep (se 2 (by rfl) ⟨2880339, by rfl⟩ : syracuseStep 7680905 = 5760679) B5760679
theorem B8639561 : Blo 1516955 8639561 := bstep (se 2 (by rfl) ⟨3239835, by rfl⟩ : syracuseStep 8639561 = 6479671) B6479671
theorem B2561179 : Blo 1516955 2561179 := bstep (se 1 (by rfl) ⟨1920884, by rfl⟩ : syracuseStep 2561179 = 3841769) B3841769
theorem B2561321 : Blo 1516955 2561321 := bstep (se 2 (by rfl) ⟨960495, by rfl⟩ : syracuseStep 2561321 = 1920991) B1920991
theorem B3241289 : Blo 1516955 3241289 := bstep (se 2 (by rfl) ⟨1215483, by rfl⟩ : syracuseStep 3241289 = 2430967) B2430967
theorem B5764567 : Blo 1516955 5764567 := bstep (se 1 (by rfl) ⟨4323425, by rfl⟩ : syracuseStep 5764567 = 8646851) B8646851
theorem B3413843 : Blo 1516955 3413843 := bstep (se 1 (by rfl) ⟨2560382, by rfl⟩ : syracuseStep 3413843 = 5120765) B5120765
theorem B2561915 : Blo 1516955 2561915 := bstep (se 1 (by rfl) ⟨1921436, by rfl⟩ : syracuseStep 2561915 = 3842873) B3842873
theorem B4864009 : Blo 1516955 4864009 := bstep (se 2 (by rfl) ⟨1824003, by rfl⟩ : syracuseStep 4864009 = 3648007) B3648007
theorem B2562185 : Blo 1516955 2562185 := bstep (se 2 (by rfl) ⟨960819, by rfl⟩ : syracuseStep 2562185 = 1921639) B1921639
theorem B25942193 : Blo 1516955 25942193 := bstep (se 2 (by rfl) ⟨9728322, by rfl⟩ : syracuseStep 25942193 = 19456645) B19456645
theorem B2275511 : Blo 1516955 2275511 := bstep (se 1 (by rfl) ⟨1706633, by rfl⟩ : syracuseStep 2275511 = 3413267) B3413267
theorem B31160531 : Blo 1516955 31160531 := bstep (se 1 (by rfl) ⟨23370398, by rfl⟩ : syracuseStep 31160531 = 46740797) B46740797
theorem B2275559 : Blo 1516955 2275559 := bstep (se 1 (by rfl) ⟨1706669, by rfl⟩ : syracuseStep 2275559 = 3413339) B3413339
theorem B4323631 : Blo 1516955 4323631 := bstep (se 1 (by rfl) ⟨3242723, by rfl⟩ : syracuseStep 4323631 = 6485447) B6485447
theorem B3414329 : Blo 1516955 3414329 := bstep (se 2 (by rfl) ⟨1280373, by rfl⟩ : syracuseStep 3414329 = 2560747) B2560747
theorem B2734535 : Blo 1516955 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B4323881 : Blo 1516955 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B2275931 : Blo 1516955 2275931 := bstep (se 1 (by rfl) ⟨1706948, by rfl⟩ : syracuseStep 2275931 = 3413897) B3413897
theorem B3242587 : Blo 1516955 3242587 := bstep (se 1 (by rfl) ⟨2431940, by rfl⟩ : syracuseStep 3242587 = 4863881) B4863881
theorem B2276075 : Blo 1516955 2276075 := bstep (se 1 (by rfl) ⟨1707056, by rfl⟩ : syracuseStep 2276075 = 3414113) B3414113
theorem B2276105 : Blo 1516955 2276105 := bstep (se 2 (by rfl) ⟨853539, by rfl⟩ : syracuseStep 2276105 = 1707079) B1707079
theorem B2161417 : Blo 1516955 2161417 := bstep (se 2 (by rfl) ⟨810531, by rfl⟩ : syracuseStep 2161417 = 1621063) B1621063
theorem B2734895 : Blo 1516955 2734895 := bstep (se 1 (by rfl) ⟨2051171, by rfl⟩ : syracuseStep 2734895 = 4102343) B4102343
theorem B14032019 : Blo 1516955 14032019 := bstep (se 1 (by rfl) ⟨10524014, by rfl⟩ : syracuseStep 14032019 = 21048029) B21048029
theorem B3415247 : Blo 1516955 3415247 := bstep (se 1 (by rfl) ⟨2561435, by rfl⟩ : syracuseStep 3415247 = 5122871) B5122871
theorem B2161895 : Blo 1516955 2161895 := bstep (se 1 (by rfl) ⟨1621421, by rfl⟩ : syracuseStep 2161895 = 3242843) B3242843
theorem B23354639 : Blo 1516955 23354639 := bstep (se 1 (by rfl) ⟨17515979, by rfl⟩ : syracuseStep 23354639 = 35031959) B35031959
theorem B47365411 : Blo 1516955 47365411 := bstep (se 1 (by rfl) ⟨35524058, by rfl⟩ : syracuseStep 47365411 = 71048117) B71048117
theorem B5193083 : Blo 1516955 5193083 := bstep (se 1 (by rfl) ⟨3894812, by rfl⟩ : syracuseStep 5193083 = 7789625) B7789625
theorem B3415625 : Blo 1516955 3415625 := bstep (se 2 (by rfl) ⟨1280859, by rfl⟩ : syracuseStep 3415625 = 2561719) B2561719
theorem B2276975 : Blo 1516955 2276975 := bstep (se 1 (by rfl) ⟨1707731, by rfl⟩ : syracuseStep 2276975 = 3415463) B3415463
theorem B2277095 : Blo 1516955 2277095 := bstep (se 1 (by rfl) ⟨1707821, by rfl⟩ : syracuseStep 2277095 = 3415643) B3415643
theorem B14589719 : Blo 1516955 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B2277287 : Blo 1516955 2277287 := bstep (se 1 (by rfl) ⟨1707965, by rfl⟩ : syracuseStep 2277287 = 3415931) B3415931
theorem B8314807 : Blo 1516955 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B2277545 : Blo 1516955 2277545 := bstep (se 2 (by rfl) ⟨854079, by rfl⟩ : syracuseStep 2277545 = 1708159) B1708159
theorem B52560413 : Blo 1516955 52560413 := bstep (se 3 (by rfl) ⟨9855077, by rfl⟩ : syracuseStep 52560413 = 19710155) B19710155
theorem B5120603 : Blo 1516955 5120603 := bstep (se 1 (by rfl) ⟨3840452, by rfl⟩ : syracuseStep 5120603 = 7680905) B7680905
theorem B5759707 : Blo 1516955 5759707 := bstep (se 1 (by rfl) ⟨4319780, by rfl⟩ : syracuseStep 5759707 = 8639561) B8639561
theorem B59138909 : Blo 1516955 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B16417673 : Blo 1516955 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B17294795 : Blo 1516955 17294795 := bstep (se 1 (by rfl) ⟨12971096, by rfl⟩ : syracuseStep 17294795 = 25942193) B25942193
theorem B1517007 : Blo 1516955 1517007 := bstep (se 1 (by rfl) ⟨1137755, by rfl⟩ : syracuseStep 1517007 = 2275511) B2275511
theorem B1517039 : Blo 1516955 1517039 := bstep (se 1 (by rfl) ⟨1137779, by rfl⟩ : syracuseStep 1517039 = 2275559) B2275559
theorem B63153881 : Blo 1516955 63153881 := bstep (se 2 (by rfl) ⟨23682705, by rfl⟩ : syracuseStep 63153881 = 47365411) B47365411
theorem B1517287 : Blo 1516955 1517287 := bstep (se 1 (by rfl) ⟨1137965, by rfl⟩ : syracuseStep 1517287 = 2275931) B2275931
theorem B1517383 : Blo 1516955 1517383 := bstep (se 1 (by rfl) ⟨1138037, by rfl⟩ : syracuseStep 1517383 = 2276075) B2276075
theorem B1517403 : Blo 1516955 1517403 := bstep (se 1 (by rfl) ⟨1138052, by rfl⟩ : syracuseStep 1517403 = 2276105) B2276105
theorem B7686089 : Blo 1516955 7686089 := bstep (se 2 (by rfl) ⟨2882283, by rfl⟩ : syracuseStep 7686089 = 5764567) B5764567
theorem B7293053 : Blo 1516955 7293053 := bstep (se 3 (by rfl) ⟨1367447, by rfl⟩ : syracuseStep 7293053 = 2734895) B2734895
theorem B1517983 : Blo 1516955 1517983 := bstep (se 1 (by rfl) ⟨1138487, by rfl⟩ : syracuseStep 1517983 = 2276975) B2276975
theorem B1518063 : Blo 1516955 1518063 := bstep (se 1 (by rfl) ⟨1138547, by rfl⟩ : syracuseStep 1518063 = 2277095) B2277095
theorem B9726479 : Blo 1516955 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B11086409 : Blo 1516955 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B1518191 : Blo 1516955 1518191 := bstep (se 1 (by rfl) ⟨1138643, by rfl⟩ : syracuseStep 1518191 = 2277287) B2277287
theorem B1518407 : Blo 1516955 1518407 := bstep (se 1 (by rfl) ⟨1138805, by rfl⟩ : syracuseStep 1518407 = 2277611) B2277611
theorem B1518447 : Blo 1516955 1518447 := bstep (se 1 (by rfl) ⟨1138835, by rfl⟩ : syracuseStep 1518447 = 2277671) B2277671
theorem B4861291 : Blo 1516955 4861291 := bstep (se 1 (by rfl) ⟨3645968, by rfl⟩ : syracuseStep 4861291 = 7291937) B7291937
theorem B18968003 : Blo 1516955 18968003 := bstep (se 1 (by rfl) ⟨14226002, by rfl⟩ : syracuseStep 18968003 = 28452005) B28452005
theorem B1707547 : Blo 1516955 1707547 := bstep (se 1 (by rfl) ⟨1280660, by rfl⟩ : syracuseStep 1707547 = 2561321) B2561321
theorem B5762623 : Blo 1516955 5762623 := bstep (se 1 (by rfl) ⟨4321967, by rfl⟩ : syracuseStep 5762623 = 8643935) B8643935
theorem B13848221 : Blo 1516955 13848221 := bstep (se 3 (by rfl) ⟨2596541, by rfl⟩ : syracuseStep 13848221 = 5193083) B5193083
theorem B4861691 : Blo 1516955 4861691 := bstep (se 1 (by rfl) ⟨3646268, by rfl⟩ : syracuseStep 4861691 = 7292537) B7292537
theorem B1707943 : Blo 1516955 1707943 := bstep (se 1 (by rfl) ⟨1280957, by rfl⟩ : syracuseStep 1707943 = 2561915) B2561915
theorem B1708123 : Blo 1516955 1708123 := bstep (se 1 (by rfl) ⟨1281092, by rfl⟩ : syracuseStep 1708123 = 2562185) B2562185
theorem B11530349 : Blo 1516955 11530349 := bstep (se 3 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 11530349 = 4323881) B4323881
theorem B9728221 : Blo 1516955 9728221 := bstep (se 3 (by rfl) ⟨1824041, by rfl⟩ : syracuseStep 9728221 = 3648083) B3648083
theorem B5468435 : Blo 1516955 5468435 := bstep (se 1 (by rfl) ⟨4101326, by rfl⟩ : syracuseStep 5468435 = 8202653) B8202653
theorem B1823023 : Blo 1516955 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B3240263 : Blo 1516955 3240263 := bstep (se 1 (by rfl) ⟨2430197, by rfl⟩ : syracuseStep 3240263 = 4860395) B4860395
theorem B4862369 : Blo 1516955 4862369 := bstep (se 2 (by rfl) ⟨1823388, by rfl⟩ : syracuseStep 4862369 = 3646777) B3646777
theorem B11678303 : Blo 1516955 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B15569759 : Blo 1516955 15569759 := bstep (se 1 (by rfl) ⟨11677319, by rfl⟩ : syracuseStep 15569759 = 23354639) B23354639
theorem B58340411 : Blo 1516955 58340411 := bstep (se 1 (by rfl) ⟨43755308, by rfl⟩ : syracuseStep 58340411 = 87510617) B87510617
theorem B16627031 : Blo 1516955 16627031 := bstep (se 1 (by rfl) ⟨12470273, by rfl⟩ : syracuseStep 16627031 = 24940547) B24940547
theorem B6485345 : Blo 1516955 6485345 := bstep (se 2 (by rfl) ⟨2432004, by rfl⟩ : syracuseStep 6485345 = 4864009) B4864009
theorem B7681391 : Blo 1516955 7681391 := bstep (se 1 (by rfl) ⟨5761043, by rfl⟩ : syracuseStep 7681391 = 11522087) B11522087
theorem B2561449 : Blo 1516955 2561449 := bstep (se 2 (by rfl) ⟨960543, by rfl⟩ : syracuseStep 2561449 = 1921087) B1921087
theorem B2561503 : Blo 1516955 2561503 := bstep (se 1 (by rfl) ⟨1921127, by rfl⟩ : syracuseStep 2561503 = 3842255) B3842255
theorem B25933445 : Blo 1516955 25933445 := bstep (se 4 (by rfl) ⟨2431260, by rfl⟩ : syracuseStep 25933445 = 4862521) B4862521
theorem B23369417 : Blo 1516955 23369417 := bstep (se 2 (by rfl) ⟨8763531, by rfl⟩ : syracuseStep 23369417 = 17527063) B17527063
theorem B5764841 : Blo 1516955 5764841 := bstep (se 2 (by rfl) ⟨2161815, by rfl⟩ : syracuseStep 5764841 = 4323631) B4323631
theorem B142153487 : Blo 1516955 142153487 := bstep (se 1 (by rfl) ⟨106615115, by rfl⟩ : syracuseStep 142153487 = 213230231) B213230231
theorem B5765053 : Blo 1516955 5765053 := bstep (se 3 (by rfl) ⟨1080947, by rfl⟩ : syracuseStep 5765053 = 2161895) B2161895
theorem B4323449 : Blo 1516955 4323449 := bstep (se 2 (by rfl) ⟨1621293, by rfl⟩ : syracuseStep 4323449 = 3242587) B3242587
theorem B2160859 : Blo 1516955 2160859 := bstep (se 1 (by rfl) ⟨1620644, by rfl⟩ : syracuseStep 2160859 = 3241289) B3241289
theorem B147618125 : Blo 1516955 147618125 := bstep (se 3 (by rfl) ⟨27678398, by rfl⟩ : syracuseStep 147618125 = 55356797) B55356797
theorem B2881889 : Blo 1516955 2881889 := bstep (se 2 (by rfl) ⟨1080708, by rfl⟩ : syracuseStep 2881889 = 2161417) B2161417
theorem B2275721 : Blo 1516955 2275721 := bstep (se 2 (by rfl) ⟨853395, by rfl⟩ : syracuseStep 2275721 = 1706791) B1706791
theorem B3840443 : Blo 1516955 3840443 := bstep (se 1 (by rfl) ⟨2880332, by rfl⟩ : syracuseStep 3840443 = 5760665) B5760665
theorem B2275895 : Blo 1516955 2275895 := bstep (se 1 (by rfl) ⟨1706921, by rfl⟩ : syracuseStep 2275895 = 3413843) B3413843
theorem B172964585 : Blo 1516955 172964585 := bstep (se 2 (by rfl) ⟨64861719, by rfl⟩ : syracuseStep 172964585 = 129723439) B129723439
theorem B9231097 : Blo 1516955 9231097 := bstep (se 2 (by rfl) ⟨3461661, by rfl⟩ : syracuseStep 9231097 = 6923323) B6923323
theorem B3414779 : Blo 1516955 3414779 := bstep (se 1 (by rfl) ⟨2561084, by rfl⟩ : syracuseStep 3414779 = 5122169) B5122169
theorem B6150923 : Blo 1516955 6150923 := bstep (se 1 (by rfl) ⟨4613192, by rfl⟩ : syracuseStep 6150923 = 9226385) B9226385
theorem B20773687 : Blo 1516955 20773687 := bstep (se 1 (by rfl) ⟨15580265, by rfl⟩ : syracuseStep 20773687 = 31160531) B31160531
theorem B3414905 : Blo 1516955 3414905 := bstep (se 2 (by rfl) ⟨1280589, by rfl⟩ : syracuseStep 3414905 = 2561179) B2561179
theorem B2276219 : Blo 1516955 2276219 := bstep (se 1 (by rfl) ⟨1707164, by rfl⟩ : syracuseStep 2276219 = 3414329) B3414329
theorem B19455005 : Blo 1516955 19455005 := bstep (se 3 (by rfl) ⟨3647813, by rfl⟩ : syracuseStep 19455005 = 7295627) B7295627
theorem B9354679 : Blo 1516955 9354679 := bstep (se 1 (by rfl) ⟨7016009, by rfl⟩ : syracuseStep 9354679 = 14032019) B14032019
theorem B2276831 : Blo 1516955 2276831 := bstep (se 1 (by rfl) ⟨1707623, by rfl⟩ : syracuseStep 2276831 = 3415247) B3415247
theorem B2277083 : Blo 1516955 2277083 := bstep (se 1 (by rfl) ⟨1707812, by rfl⟩ : syracuseStep 2277083 = 3415625) B3415625
theorem B3841931 : Blo 1516955 3841931 := bstep (se 1 (by rfl) ⟨2881448, by rfl⟩ : syracuseStep 3841931 = 5762897) B5762897
theorem B2277353 : Blo 1516955 2277353 := bstep (se 2 (by rfl) ⟨854007, by rfl⟩ : syracuseStep 2277353 = 1708015) B1708015
theorem B2277497 : Blo 1516955 2277497 := bstep (se 2 (by rfl) ⟨854061, by rfl⟩ : syracuseStep 2277497 = 1708123) B1708123
theorem B3645623 : Blo 1516955 3645623 := bstep (se 1 (by rfl) ⟨2734217, by rfl⟩ : syracuseStep 3645623 = 5468435) B5468435
theorem B10379839 : Blo 1516955 10379839 := bstep (se 1 (by rfl) ⟨7784879, by rfl⟩ : syracuseStep 10379839 = 15569759) B15569759
theorem B10945115 : Blo 1516955 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B11084687 : Blo 1516955 11084687 := bstep (se 1 (by rfl) ⟨8313515, by rfl⟩ : syracuseStep 11084687 = 16627031) B16627031
theorem B5120927 : Blo 1516955 5120927 := bstep (se 1 (by rfl) ⟨3840695, by rfl⟩ : syracuseStep 5120927 = 7681391) B7681391
theorem B27698249 : Blo 1516955 27698249 := bstep (se 2 (by rfl) ⟨10386843, by rfl⟩ : syracuseStep 27698249 = 20773687) B20773687
theorem B3843227 : Blo 1516955 3843227 := bstep (se 1 (by rfl) ⟨2882420, by rfl⟩ : syracuseStep 3843227 = 5764841) B5764841
theorem B98412083 : Blo 1516955 98412083 := bstep (se 1 (by rfl) ⟨73809062, by rfl⟩ : syracuseStep 98412083 = 147618125) B147618125
theorem B1517147 : Blo 1516955 1517147 := bstep (se 1 (by rfl) ⟨1137860, by rfl⟩ : syracuseStep 1517147 = 2275721) B2275721
theorem B1517263 : Blo 1516955 1517263 := bstep (se 1 (by rfl) ⟨1137947, by rfl⟩ : syracuseStep 1517263 = 2275895) B2275895
theorem B7390939 : Blo 1516955 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B6481721 : Blo 1516955 6481721 := bstep (se 2 (by rfl) ⟨2430645, by rfl⟩ : syracuseStep 6481721 = 4861291) B4861291
theorem B1517479 : Blo 1516955 1517479 := bstep (se 1 (by rfl) ⟨1138109, by rfl⟩ : syracuseStep 1517479 = 2276219) B2276219
theorem B12970003 : Blo 1516955 12970003 := bstep (se 1 (by rfl) ⟨9727502, by rfl⟩ : syracuseStep 12970003 = 19455005) B19455005
theorem B49891621 : Blo 1516955 49891621 := bstep (se 4 (by rfl) ⟨4677339, by rfl⟩ : syracuseStep 49891621 = 9354679) B9354679
theorem B1517887 : Blo 1516955 1517887 := bstep (se 1 (by rfl) ⟨1138415, by rfl⟩ : syracuseStep 1517887 = 2276831) B2276831
theorem B1518055 : Blo 1516955 1518055 := bstep (se 1 (by rfl) ⟨1138541, by rfl⟩ : syracuseStep 1518055 = 2277083) B2277083
theorem B7686737 : Blo 1516955 7686737 := bstep (se 2 (by rfl) ⟨2882526, by rfl⟩ : syracuseStep 7686737 = 5765053) B5765053
theorem B1518235 : Blo 1516955 1518235 := bstep (se 1 (by rfl) ⟨1138676, by rfl⟩ : syracuseStep 1518235 = 2277353) B2277353
theorem B7686899 : Blo 1516955 7686899 := bstep (se 1 (by rfl) ⟨5765174, by rfl⟩ : syracuseStep 7686899 = 11530349) B11530349
theorem B1518363 : Blo 1516955 1518363 := bstep (se 1 (by rfl) ⟨1138772, by rfl⟩ : syracuseStep 1518363 = 2277545) B2277545
theorem B12970961 : Blo 1516955 12970961 := bstep (se 2 (by rfl) ⟨4864110, by rfl⟩ : syracuseStep 12970961 = 9728221) B9728221
theorem B35040275 : Blo 1516955 35040275 := bstep (se 1 (by rfl) ⟨26280206, by rfl⟩ : syracuseStep 35040275 = 52560413) B52560413
theorem B7679609 : Blo 1516955 7679609 := bstep (se 2 (by rfl) ⟨2879853, by rfl⟩ : syracuseStep 7679609 = 5759707) B5759707
theorem B11529863 : Blo 1516955 11529863 := bstep (se 1 (by rfl) ⟨8647397, by rfl⟩ : syracuseStep 11529863 = 17294795) B17294795
theorem B12308129 : Blo 1516955 12308129 := bstep (se 2 (by rfl) ⟨4615548, by rfl⟩ : syracuseStep 12308129 = 9231097) B9231097
theorem B17288963 : Blo 1516955 17288963 := bstep (se 1 (by rfl) ⟨12966722, by rfl⟩ : syracuseStep 17288963 = 25933445) B25933445
theorem B42102587 : Blo 1516955 42102587 := bstep (se 1 (by rfl) ⟨31576940, by rfl⟩ : syracuseStep 42102587 = 63153881) B63153881
theorem B94768991 : Blo 1516955 94768991 := bstep (se 1 (by rfl) ⟨71076743, by rfl⟩ : syracuseStep 94768991 = 142153487) B142153487
theorem B5124059 : Blo 1516955 5124059 := bstep (se 1 (by rfl) ⟨3843044, by rfl⟩ : syracuseStep 5124059 = 7686089) B7686089
theorem B4862035 : Blo 1516955 4862035 := bstep (se 1 (by rfl) ⟨3646526, by rfl⟩ : syracuseStep 4862035 = 7293053) B7293053
theorem B1921259 : Blo 1516955 1921259 := bstep (se 1 (by rfl) ⟨1440944, by rfl⟩ : syracuseStep 1921259 = 2881889) B2881889
theorem B31142141 : Blo 1516955 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B2560295 : Blo 1516955 2560295 := bstep (se 1 (by rfl) ⟨1920221, by rfl⟩ : syracuseStep 2560295 = 3840443) B3840443
theorem B6484319 : Blo 1516955 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B4100615 : Blo 1516955 4100615 := bstep (se 1 (by rfl) ⟨3075461, by rfl⟩ : syracuseStep 4100615 = 6150923) B6150923
theorem B461238893 : Blo 1516955 461238893 := bstep (se 3 (by rfl) ⟨86482292, by rfl⟩ : syracuseStep 461238893 = 172964585) B172964585
theorem B12645335 : Blo 1516955 12645335 := bstep (se 1 (by rfl) ⟨9484001, by rfl⟩ : syracuseStep 12645335 = 18968003) B18968003
theorem B3241127 : Blo 1516955 3241127 := bstep (se 1 (by rfl) ⟨2430845, by rfl⟩ : syracuseStep 3241127 = 4861691) B4861691
theorem B2561287 : Blo 1516955 2561287 := bstep (se 1 (by rfl) ⟨1920965, by rfl⟩ : syracuseStep 2561287 = 3841931) B3841931
theorem B3241579 : Blo 1516955 3241579 := bstep (se 1 (by rfl) ⟨2431184, by rfl⟩ : syracuseStep 3241579 = 4862369) B4862369
theorem B2881145 : Blo 1516955 2881145 := bstep (se 2 (by rfl) ⟨1080429, by rfl⟩ : syracuseStep 2881145 = 2160859) B2160859
theorem B3413735 : Blo 1516955 3413735 := bstep (se 1 (by rfl) ⟨2560301, by rfl⟩ : syracuseStep 3413735 = 5120603) B5120603
theorem B2430697 : Blo 1516955 2430697 := bstep (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) B1823023
theorem B39425939 : Blo 1516955 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B38893607 : Blo 1516955 38893607 := bstep (se 1 (by rfl) ⟨29170205, by rfl⟩ : syracuseStep 38893607 = 58340411) B58340411
theorem B8640701 : Blo 1516955 8640701 := bstep (se 3 (by rfl) ⟨1620131, by rfl⟩ : syracuseStep 8640701 = 3240263) B3240263
theorem B4323563 : Blo 1516955 4323563 := bstep (se 1 (by rfl) ⟨3242672, by rfl⟩ : syracuseStep 4323563 = 6485345) B6485345
theorem B15579611 : Blo 1516955 15579611 := bstep (se 1 (by rfl) ⟨11684708, by rfl⟩ : syracuseStep 15579611 = 23369417) B23369417
theorem B2882299 : Blo 1516955 2882299 := bstep (se 1 (by rfl) ⟨2161724, by rfl⟩ : syracuseStep 2882299 = 4323449) B4323449
theorem B2276519 : Blo 1516955 2276519 := bstep (se 1 (by rfl) ⟨1707389, by rfl⟩ : syracuseStep 2276519 = 3414779) B3414779
theorem B3415265 : Blo 1516955 3415265 := bstep (se 2 (by rfl) ⟨1280724, by rfl⟩ : syracuseStep 3415265 = 2561449) B2561449
theorem B2276603 : Blo 1516955 2276603 := bstep (se 1 (by rfl) ⟨1707452, by rfl⟩ : syracuseStep 2276603 = 3414905) B3414905
theorem B3415337 : Blo 1516955 3415337 := bstep (se 2 (by rfl) ⟨1280751, by rfl⟩ : syracuseStep 3415337 = 2561503) B2561503
theorem B2276729 : Blo 1516955 2276729 := bstep (se 2 (by rfl) ⟨853773, by rfl⟩ : syracuseStep 2276729 = 1707547) B1707547
theorem B7683497 : Blo 1516955 7683497 := bstep (se 2 (by rfl) ⟨2881311, by rfl⟩ : syracuseStep 7683497 = 5762623) B5762623
theorem B9232147 : Blo 1516955 9232147 := bstep (se 1 (by rfl) ⟨6924110, by rfl⟩ : syracuseStep 9232147 = 13848221) B13848221
theorem B2277257 : Blo 1516955 2277257 := bstep (se 2 (by rfl) ⟨853971, by rfl⟩ : syracuseStep 2277257 = 1707943) B1707943
theorem B17293337 : Blo 1516955 17293337 := bstep (se 2 (by rfl) ⟨6485001, by rfl⟩ : syracuseStep 17293337 = 12970003) B12970003
theorem B7389791 : Blo 1516955 7389791 := bstep (se 1 (by rfl) ⟨5542343, by rfl⟩ : syracuseStep 7389791 = 11084687) B11084687
theorem B18465499 : Blo 1516955 18465499 := bstep (se 1 (by rfl) ⟨13849124, by rfl⟩ : syracuseStep 18465499 = 27698249) B27698249
theorem B3843065 : Blo 1516955 3843065 := bstep (se 2 (by rfl) ⟨1441149, by rfl⟩ : syracuseStep 3843065 = 2882299) B2882299
theorem B25929071 : Blo 1516955 25929071 := bstep (se 1 (by rfl) ⟨19446803, by rfl⟩ : syracuseStep 25929071 = 38893607) B38893607
theorem B5760467 : Blo 1516955 5760467 := bstep (se 1 (by rfl) ⟨4320350, by rfl⟩ : syracuseStep 5760467 = 8640701) B8640701
theorem B1517679 : Blo 1516955 1517679 := bstep (se 1 (by rfl) ⟨1138259, by rfl⟩ : syracuseStep 1517679 = 2276519) B2276519
theorem B1517735 : Blo 1516955 1517735 := bstep (se 1 (by rfl) ⟨1138301, by rfl⟩ : syracuseStep 1517735 = 2276603) B2276603
theorem B1517819 : Blo 1516955 1517819 := bstep (se 1 (by rfl) ⟨1138364, by rfl⟩ : syracuseStep 1517819 = 2276729) B2276729
theorem B5122331 : Blo 1516955 5122331 := bstep (se 1 (by rfl) ⟨3841748, by rfl⟩ : syracuseStep 5122331 = 7683497) B7683497
theorem B7686575 : Blo 1516955 7686575 := bstep (se 1 (by rfl) ⟨5764931, by rfl⟩ : syracuseStep 7686575 = 11529863) B11529863
theorem B28068391 : Blo 1516955 28068391 := bstep (se 1 (by rfl) ⟨21051293, by rfl⟩ : syracuseStep 28068391 = 42102587) B42102587
theorem B33720893 : Blo 1516955 33720893 := bstep (se 3 (by rfl) ⟨6322667, by rfl⟩ : syracuseStep 33720893 = 12645335) B12645335
theorem B63179327 : Blo 1516955 63179327 := bstep (se 1 (by rfl) ⟨47384495, by rfl⟩ : syracuseStep 63179327 = 94768991) B94768991
theorem B1518171 : Blo 1516955 1518171 := bstep (se 1 (by rfl) ⟨1138628, by rfl⟩ : syracuseStep 1518171 = 2277257) B2277257
theorem B1518331 : Blo 1516955 1518331 := bstep (se 1 (by rfl) ⟨1138748, by rfl⟩ : syracuseStep 1518331 = 2277497) B2277497
theorem B6482713 : Blo 1516955 6482713 := bstep (se 2 (by rfl) ⟨2431017, by rfl⟩ : syracuseStep 6482713 = 4862035) B4862035
theorem B20761427 : Blo 1516955 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B1706863 : Blo 1516955 1706863 := bstep (se 1 (by rfl) ⟨1280147, by rfl⟩ : syracuseStep 1706863 = 2560295) B2560295
theorem B66522161 : Blo 1516955 66522161 := bstep (se 2 (by rfl) ⟨24945810, by rfl⟩ : syracuseStep 66522161 = 49891621) B49891621
theorem B5123357 : Blo 1516955 5123357 := bstep (se 3 (by rfl) ⟨960629, by rfl⟩ : syracuseStep 5123357 = 1921259) B1921259
theorem B13839785 : Blo 1516955 13839785 := bstep (se 2 (by rfl) ⟨5189919, by rfl⟩ : syracuseStep 13839785 = 10379839) B10379839
theorem B1920763 : Blo 1516955 1920763 := bstep (se 1 (by rfl) ⟨1440572, by rfl⟩ : syracuseStep 1920763 = 2881145) B2881145
theorem B26283959 : Blo 1516955 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B5124491 : Blo 1516955 5124491 := bstep (se 1 (by rfl) ⟨3843368, by rfl⟩ : syracuseStep 5124491 = 7686737) B7686737
theorem B5124599 : Blo 1516955 5124599 := bstep (se 1 (by rfl) ⟨3843449, by rfl⟩ : syracuseStep 5124599 = 7686899) B7686899
theorem B8647307 : Blo 1516955 8647307 := bstep (se 1 (by rfl) ⟨6485480, by rfl⟩ : syracuseStep 8647307 = 12970961) B12970961
theorem B23360183 : Blo 1516955 23360183 := bstep (se 1 (by rfl) ⟨17520137, by rfl⟩ : syracuseStep 23360183 = 35040275) B35040275
theorem B4322105 : Blo 1516955 4322105 := bstep (se 2 (by rfl) ⟨1620789, by rfl⟩ : syracuseStep 4322105 = 3241579) B3241579
theorem B3240929 : Blo 1516955 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B12309529 : Blo 1516955 12309529 := bstep (se 2 (by rfl) ⟨4616073, by rfl⟩ : syracuseStep 12309529 = 9232147) B9232147
theorem B8205419 : Blo 1516955 8205419 := bstep (se 1 (by rfl) ⟨6154064, by rfl⟩ : syracuseStep 8205419 = 12308129) B12308129
theorem B2430415 : Blo 1516955 2430415 := bstep (se 1 (by rfl) ⟨1822811, by rfl⟩ : syracuseStep 2430415 = 3645623) B3645623
theorem B4322879 : Blo 1516955 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B2733743 : Blo 1516955 2733743 := bstep (se 1 (by rfl) ⟨2050307, by rfl⟩ : syracuseStep 2733743 = 4100615) B4100615
theorem B7296743 : Blo 1516955 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B307492595 : Blo 1516955 307492595 := bstep (se 1 (by rfl) ⟨230619446, by rfl⟩ : syracuseStep 307492595 = 461238893) B461238893
theorem B3413951 : Blo 1516955 3413951 := bstep (se 1 (by rfl) ⟨2560463, by rfl⟩ : syracuseStep 3413951 = 5120927) B5120927
theorem B2562151 : Blo 1516955 2562151 := bstep (se 1 (by rfl) ⟨1921613, by rfl⟩ : syracuseStep 2562151 = 3843227) B3843227
theorem B2160751 : Blo 1516955 2160751 := bstep (se 1 (by rfl) ⟨1620563, by rfl⟩ : syracuseStep 2160751 = 3241127) B3241127
theorem B65608055 : Blo 1516955 65608055 := bstep (se 1 (by rfl) ⟨49206041, by rfl⟩ : syracuseStep 65608055 = 98412083) B98412083
theorem B2275823 : Blo 1516955 2275823 := bstep (se 1 (by rfl) ⟨1706867, by rfl⟩ : syracuseStep 2275823 = 3413735) B3413735
theorem B2882375 : Blo 1516955 2882375 := bstep (se 1 (by rfl) ⟨2161781, by rfl⟩ : syracuseStep 2882375 = 4323563) B4323563
theorem B10386407 : Blo 1516955 10386407 := bstep (se 1 (by rfl) ⟨7789805, by rfl⟩ : syracuseStep 10386407 = 15579611) B15579611
theorem B3415049 : Blo 1516955 3415049 := bstep (se 2 (by rfl) ⟨1280643, by rfl⟩ : syracuseStep 3415049 = 2561287) B2561287
theorem B2276843 : Blo 1516955 2276843 := bstep (se 1 (by rfl) ⟨1707632, by rfl⟩ : syracuseStep 2276843 = 3415265) B3415265
theorem B17284589 : Blo 1516955 17284589 := bstep (se 3 (by rfl) ⟨3240860, by rfl⟩ : syracuseStep 17284589 = 6481721) B6481721
theorem B2276891 : Blo 1516955 2276891 := bstep (se 1 (by rfl) ⟨1707668, by rfl⟩ : syracuseStep 2276891 = 3415337) B3415337
theorem B9854585 : Blo 1516955 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B5119739 : Blo 1516955 5119739 := bstep (se 1 (by rfl) ⟨3839804, by rfl⟩ : syracuseStep 5119739 = 7679609) B7679609
theorem B11525975 : Blo 1516955 11525975 := bstep (se 1 (by rfl) ⟨8644481, by rfl⟩ : syracuseStep 11525975 = 17288963) B17288963
theorem B3416039 : Blo 1516955 3416039 := bstep (se 1 (by rfl) ⟨2562029, by rfl⟩ : syracuseStep 3416039 = 5124059) B5124059
theorem B3416201 : Blo 1516955 3416201 := bstep (se 2 (by rfl) ⟨1281075, by rfl⟩ : syracuseStep 3416201 = 2562151) B2562151
theorem B3416327 : Blo 1516955 3416327 := bstep (se 1 (by rfl) ⟨2562245, by rfl⟩ : syracuseStep 3416327 = 5124491) B5124491
theorem B21881117 : Blo 1516955 21881117 := bstep (se 3 (by rfl) ⟨4102709, by rfl⟩ : syracuseStep 21881117 = 8205419) B8205419
theorem B3416399 : Blo 1516955 3416399 := bstep (se 1 (by rfl) ⟨2562299, by rfl⟩ : syracuseStep 3416399 = 5124599) B5124599
theorem B15573455 : Blo 1516955 15573455 := bstep (se 1 (by rfl) ⟨11680091, by rfl⟩ : syracuseStep 15573455 = 23360183) B23360183
theorem B17286047 : Blo 1516955 17286047 := bstep (se 1 (by rfl) ⟨12964535, by rfl⟩ : syracuseStep 17286047 = 25929071) B25929071
theorem B8643617 : Blo 1516955 8643617 := bstep (se 2 (by rfl) ⟨3241356, by rfl⟩ : syracuseStep 8643617 = 6482713) B6482713
theorem B43738703 : Blo 1516955 43738703 := bstep (se 1 (by rfl) ⟨32804027, by rfl⟩ : syracuseStep 43738703 = 65608055) B65608055
theorem B1517215 : Blo 1516955 1517215 := bstep (se 1 (by rfl) ⟨1137911, by rfl⟩ : syracuseStep 1517215 = 2275823) B2275823
theorem B22480595 : Blo 1516955 22480595 := bstep (se 1 (by rfl) ⟨16860446, by rfl⟩ : syracuseStep 22480595 = 33720893) B33720893
theorem B19457981 : Blo 1516955 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B9226523 : Blo 1516955 9226523 := bstep (se 1 (by rfl) ⟨6919892, by rfl⟩ : syracuseStep 9226523 = 13839785) B13839785
theorem B1517895 : Blo 1516955 1517895 := bstep (se 1 (by rfl) ⟨1138421, by rfl⟩ : syracuseStep 1517895 = 2276843) B2276843
theorem B1517927 : Blo 1516955 1517927 := bstep (se 1 (by rfl) ⟨1138445, by rfl⟩ : syracuseStep 1517927 = 2276891) B2276891
theorem B12962213 : Blo 1516955 12962213 := bstep (se 4 (by rfl) ⟨1215207, by rfl⟩ : syracuseStep 12962213 = 2430415) B2430415
theorem B11528891 : Blo 1516955 11528891 := bstep (se 1 (by rfl) ⟨8646668, by rfl⟩ : syracuseStep 11528891 = 17293337) B17293337
theorem B4926527 : Blo 1516955 4926527 := bstep (se 1 (by rfl) ⟨3694895, by rfl⟩ : syracuseStep 4926527 = 7389791) B7389791
theorem B37424521 : Blo 1516955 37424521 := bstep (se 2 (by rfl) ⟨14034195, by rfl⟩ : syracuseStep 37424521 = 28068391) B28068391
theorem B1822495 : Blo 1516955 1822495 := bstep (se 1 (by rfl) ⟨1366871, by rfl⟩ : syracuseStep 1822495 = 2733743) B2733743
theorem B16412705 : Blo 1516955 16412705 := bstep (se 2 (by rfl) ⟨6154764, by rfl⟩ : syracuseStep 16412705 = 12309529) B12309529
theorem B5124383 : Blo 1516955 5124383 := bstep (se 1 (by rfl) ⟨3843287, by rfl⟩ : syracuseStep 5124383 = 7686575) B7686575
theorem B42119551 : Blo 1516955 42119551 := bstep (se 1 (by rfl) ⟨31589663, by rfl⟩ : syracuseStep 42119551 = 63179327) B63179327
theorem B1921583 : Blo 1516955 1921583 := bstep (se 1 (by rfl) ⟨1441187, by rfl⟩ : syracuseStep 1921583 = 2882375) B2882375
theorem B13840951 : Blo 1516955 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B44348107 : Blo 1516955 44348107 := bstep (se 1 (by rfl) ⟨33261080, by rfl⟩ : syracuseStep 44348107 = 66522161) B66522161
theorem B11523059 : Blo 1516955 11523059 := bstep (se 1 (by rfl) ⟨8642294, by rfl⟩ : syracuseStep 11523059 = 17284589) B17284589
theorem B2561017 : Blo 1516955 2561017 := bstep (se 2 (by rfl) ⟨960381, by rfl⟩ : syracuseStep 2561017 = 1920763) B1920763
theorem B3413159 : Blo 1516955 3413159 := bstep (se 1 (by rfl) ⟨2559869, by rfl⟩ : syracuseStep 3413159 = 5119739) B5119739
theorem B2881001 : Blo 1516955 2881001 := bstep (se 2 (by rfl) ⟨1080375, by rfl⟩ : syracuseStep 2881001 = 2160751) B2160751
theorem B5764871 : Blo 1516955 5764871 := bstep (se 1 (by rfl) ⟨4323653, by rfl⟩ : syracuseStep 5764871 = 8647307) B8647307
theorem B2881403 : Blo 1516955 2881403 := bstep (se 1 (by rfl) ⟨2161052, by rfl⟩ : syracuseStep 2881403 = 4322105) B4322105
theorem B2562043 : Blo 1516955 2562043 := bstep (se 1 (by rfl) ⟨1921532, by rfl⟩ : syracuseStep 2562043 = 3843065) B3843065
theorem B3840311 : Blo 1516955 3840311 := bstep (se 1 (by rfl) ⟨2880233, by rfl⟩ : syracuseStep 3840311 = 5760467) B5760467
theorem B2881919 : Blo 1516955 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B98482661 : Blo 1516955 98482661 := bstep (se 4 (by rfl) ⟨9232749, by rfl⟩ : syracuseStep 98482661 = 18465499) B18465499
theorem B2275817 : Blo 1516955 2275817 := bstep (se 2 (by rfl) ⟨853431, by rfl⟩ : syracuseStep 2275817 = 1706863) B1706863
theorem B204995063 : Blo 1516955 204995063 := bstep (se 1 (by rfl) ⟨153746297, by rfl⟩ : syracuseStep 204995063 = 307492595) B307492595
theorem B2275967 : Blo 1516955 2275967 := bstep (se 1 (by rfl) ⟨1706975, by rfl⟩ : syracuseStep 2275967 = 3413951) B3413951
theorem B3414887 : Blo 1516955 3414887 := bstep (se 1 (by rfl) ⟨2561165, by rfl⟩ : syracuseStep 3414887 = 5122331) B5122331
theorem B2276699 : Blo 1516955 2276699 := bstep (se 1 (by rfl) ⟨1707524, by rfl⟩ : syracuseStep 2276699 = 3415049) B3415049
theorem B3415571 : Blo 1516955 3415571 := bstep (se 1 (by rfl) ⟨2561678, by rfl⟩ : syracuseStep 3415571 = 5123357) B5123357
theorem B6569723 : Blo 1516955 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B7683983 : Blo 1516955 7683983 := bstep (se 1 (by rfl) ⟨5762987, by rfl⟩ : syracuseStep 7683983 = 11525975) B11525975
theorem B8642477 : Blo 1516955 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B27697085 : Blo 1516955 27697085 := bstep (se 3 (by rfl) ⟨5193203, by rfl⟩ : syracuseStep 27697085 = 10386407) B10386407
theorem B17522639 : Blo 1516955 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B2277359 : Blo 1516955 2277359 := bstep (se 1 (by rfl) ⟨1708019, by rfl⟩ : syracuseStep 2277359 = 3416039) B3416039
theorem B2277467 : Blo 1516955 2277467 := bstep (se 1 (by rfl) ⟨1708100, by rfl⟩ : syracuseStep 2277467 = 3416201) B3416201
theorem B2277551 : Blo 1516955 2277551 := bstep (se 1 (by rfl) ⟨1708163, by rfl⟩ : syracuseStep 2277551 = 3416327) B3416327
theorem B3416255 : Blo 1516955 3416255 := bstep (se 1 (by rfl) ⟨2562191, by rfl⟩ : syracuseStep 3416255 = 5124383) B5124383
theorem B2277599 : Blo 1516955 2277599 := bstep (se 1 (by rfl) ⟨1708199, by rfl⟩ : syracuseStep 2277599 = 3416399) B3416399
theorem B59130809 : Blo 1516955 59130809 := bstep (se 2 (by rfl) ⟨22174053, by rfl⟩ : syracuseStep 59130809 = 44348107) B44348107
theorem B7685117 : Blo 1516955 7685117 := bstep (se 3 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 7685117 = 2881919) B2881919
theorem B3843247 : Blo 1516955 3843247 := bstep (se 1 (by rfl) ⟨2882435, by rfl⟩ : syracuseStep 3843247 = 5764871) B5764871
theorem B1517211 : Blo 1516955 1517211 := bstep (se 1 (by rfl) ⟨1137908, by rfl⟩ : syracuseStep 1517211 = 2275817) B2275817
theorem B1517311 : Blo 1516955 1517311 := bstep (se 1 (by rfl) ⟨1137983, by rfl⟩ : syracuseStep 1517311 = 2275967) B2275967
theorem B7685927 : Blo 1516955 7685927 := bstep (se 1 (by rfl) ⟨5764445, by rfl⟩ : syracuseStep 7685927 = 11528891) B11528891
theorem B1517799 : Blo 1516955 1517799 := bstep (se 1 (by rfl) ⟨1138349, by rfl⟩ : syracuseStep 1517799 = 2276699) B2276699
theorem B5122655 : Blo 1516955 5122655 := bstep (se 1 (by rfl) ⟨3841991, by rfl⟩ : syracuseStep 5122655 = 7683983) B7683983
theorem B5761651 : Blo 1516955 5761651 := bstep (se 1 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 5761651 = 8642477) B8642477
theorem B1518239 : Blo 1516955 1518239 := bstep (se 1 (by rfl) ⟨1138679, by rfl⟩ : syracuseStep 1518239 = 2277359) B2277359
theorem B10382303 : Blo 1516955 10382303 := bstep (se 1 (by rfl) ⟨7786727, by rfl⟩ : syracuseStep 10382303 = 15573455) B15573455
theorem B56159401 : Blo 1516955 56159401 := bstep (se 2 (by rfl) ⟨21059775, by rfl⟩ : syracuseStep 56159401 = 42119551) B42119551
theorem B5762411 : Blo 1516955 5762411 := bstep (se 1 (by rfl) ⟨4321808, by rfl⟩ : syracuseStep 5762411 = 8643617) B8643617
theorem B1920667 : Blo 1516955 1920667 := bstep (se 1 (by rfl) ⟨1440500, by rfl⟩ : syracuseStep 1920667 = 2881001) B2881001
theorem B29159135 : Blo 1516955 29159135 := bstep (se 1 (by rfl) ⟨21869351, by rfl⟩ : syracuseStep 29159135 = 43738703) B43738703
theorem B14987063 : Blo 1516955 14987063 := bstep (se 1 (by rfl) ⟨11240297, by rfl⟩ : syracuseStep 14987063 = 22480595) B22480595
theorem B1920935 : Blo 1516955 1920935 := bstep (se 1 (by rfl) ⟨1440701, by rfl⟩ : syracuseStep 1920935 = 2881403) B2881403
theorem B12971987 : Blo 1516955 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B5124221 : Blo 1516955 5124221 := bstep (se 3 (by rfl) ⟨960791, by rfl⟩ : syracuseStep 5124221 = 1921583) B1921583
theorem B2560207 : Blo 1516955 2560207 := bstep (se 1 (by rfl) ⟨1920155, by rfl⟩ : syracuseStep 2560207 = 3840311) B3840311
theorem B65655107 : Blo 1516955 65655107 := bstep (se 1 (by rfl) ⟨49241330, by rfl⟩ : syracuseStep 65655107 = 98482661) B98482661
theorem B136663375 : Blo 1516955 136663375 := bstep (se 1 (by rfl) ⟨102497531, by rfl⟩ : syracuseStep 136663375 = 204995063) B204995063
theorem B2429993 : Blo 1516955 2429993 := bstep (se 2 (by rfl) ⟨911247, by rfl⟩ : syracuseStep 2429993 = 1822495) B1822495
theorem B4379815 : Blo 1516955 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B10941803 : Blo 1516955 10941803 := bstep (se 1 (by rfl) ⟨8206352, by rfl⟩ : syracuseStep 10941803 = 16412705) B16412705
theorem B14587411 : Blo 1516955 14587411 := bstep (se 1 (by rfl) ⟨10940558, by rfl⟩ : syracuseStep 14587411 = 21881117) B21881117
theorem B11524031 : Blo 1516955 11524031 := bstep (se 1 (by rfl) ⟨8643023, by rfl⟩ : syracuseStep 11524031 = 17286047) B17286047
theorem B7682039 : Blo 1516955 7682039 := bstep (se 1 (by rfl) ⟨5761529, by rfl⟩ : syracuseStep 7682039 = 11523059) B11523059
theorem B18454601 : Blo 1516955 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B2275439 : Blo 1516955 2275439 := bstep (se 1 (by rfl) ⟨1706579, by rfl⟩ : syracuseStep 2275439 = 3413159) B3413159
theorem B3414689 : Blo 1516955 3414689 := bstep (se 2 (by rfl) ⟨1280508, by rfl⟩ : syracuseStep 3414689 = 2561017) B2561017
theorem B6151015 : Blo 1516955 6151015 := bstep (se 1 (by rfl) ⟨4613261, by rfl⟩ : syracuseStep 6151015 = 9226523) B9226523
theorem B8641475 : Blo 1516955 8641475 := bstep (se 1 (by rfl) ⟨6481106, by rfl⟩ : syracuseStep 8641475 = 12962213) B12962213
theorem B2276591 : Blo 1516955 2276591 := bstep (se 1 (by rfl) ⟨1707443, by rfl⟩ : syracuseStep 2276591 = 3414887) B3414887
theorem B3284351 : Blo 1516955 3284351 := bstep (se 1 (by rfl) ⟨2463263, by rfl⟩ : syracuseStep 3284351 = 4926527) B4926527
theorem B199597445 : Blo 1516955 199597445 := bstep (se 4 (by rfl) ⟨18712260, by rfl⟩ : syracuseStep 199597445 = 37424521) B37424521
theorem B2277047 : Blo 1516955 2277047 := bstep (se 1 (by rfl) ⟨1707785, by rfl⟩ : syracuseStep 2277047 = 3415571) B3415571
theorem B18464723 : Blo 1516955 18464723 := bstep (se 1 (by rfl) ⟨13848542, by rfl⟩ : syracuseStep 18464723 = 27697085) B27697085
theorem B11681759 : Blo 1516955 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B3416057 : Blo 1516955 3416057 := bstep (se 2 (by rfl) ⟨1281021, by rfl⟩ : syracuseStep 3416057 = 2562043) B2562043
theorem B3416147 : Blo 1516955 3416147 := bstep (se 1 (by rfl) ⟨2562110, by rfl⟩ : syracuseStep 3416147 = 5124221) B5124221
theorem B2277503 : Blo 1516955 2277503 := bstep (se 1 (by rfl) ⟨1708127, by rfl⟩ : syracuseStep 2277503 = 3416255) B3416255
theorem B43770071 : Blo 1516955 43770071 := bstep (se 1 (by rfl) ⟨32827553, by rfl⟩ : syracuseStep 43770071 = 65655107) B65655107
theorem B39420539 : Blo 1516955 39420539 := bstep (se 1 (by rfl) ⟨29565404, by rfl⟩ : syracuseStep 39420539 = 59130809) B59130809
theorem B8201353 : Blo 1516955 8201353 := bstep (se 2 (by rfl) ⟨3075507, by rfl⟩ : syracuseStep 8201353 = 6151015) B6151015
theorem B5121359 : Blo 1516955 5121359 := bstep (se 1 (by rfl) ⟨3841019, by rfl⟩ : syracuseStep 5121359 = 7682039) B7682039
theorem B1516959 : Blo 1516955 1516959 := bstep (se 1 (by rfl) ⟨1137719, by rfl⟩ : syracuseStep 1516959 = 2275439) B2275439
theorem B5760983 : Blo 1516955 5760983 := bstep (se 1 (by rfl) ⟨4320737, by rfl⟩ : syracuseStep 5760983 = 8641475) B8641475
theorem B19449881 : Blo 1516955 19449881 := bstep (se 2 (by rfl) ⟨7293705, by rfl⟩ : syracuseStep 19449881 = 14587411) B14587411
theorem B1517727 : Blo 1516955 1517727 := bstep (se 1 (by rfl) ⟨1138295, by rfl⟩ : syracuseStep 1517727 = 2276591) B2276591
theorem B2189567 : Blo 1516955 2189567 := bstep (se 1 (by rfl) ⟨1642175, by rfl⟩ : syracuseStep 2189567 = 3284351) B3284351
theorem B133064963 : Blo 1516955 133064963 := bstep (se 1 (by rfl) ⟨99798722, by rfl⟩ : syracuseStep 133064963 = 199597445) B199597445
theorem B5122493 : Blo 1516955 5122493 := bstep (se 3 (by rfl) ⟨960467, by rfl⟩ : syracuseStep 5122493 = 1920935) B1920935
theorem B1518031 : Blo 1516955 1518031 := bstep (se 1 (by rfl) ⟨1138523, by rfl⟩ : syracuseStep 1518031 = 2277047) B2277047
theorem B1518311 : Blo 1516955 1518311 := bstep (se 1 (by rfl) ⟨1138733, by rfl⟩ : syracuseStep 1518311 = 2277467) B2277467
theorem B1518367 : Blo 1516955 1518367 := bstep (se 1 (by rfl) ⟨1138775, by rfl⟩ : syracuseStep 1518367 = 2277551) B2277551
theorem B1518399 : Blo 1516955 1518399 := bstep (se 1 (by rfl) ⟨1138799, by rfl⟩ : syracuseStep 1518399 = 2277599) B2277599
theorem B49212269 : Blo 1516955 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B182217833 : Blo 1516955 182217833 := bstep (se 2 (by rfl) ⟨68331687, by rfl⟩ : syracuseStep 182217833 = 136663375) B136663375
theorem B5123411 : Blo 1516955 5123411 := bstep (se 1 (by rfl) ⟨3842558, by rfl⟩ : syracuseStep 5123411 = 7685117) B7685117
theorem B23359013 : Blo 1516955 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B7294535 : Blo 1516955 7294535 := bstep (se 1 (by rfl) ⟨5470901, by rfl⟩ : syracuseStep 7294535 = 10941803) B10941803
theorem B5123951 : Blo 1516955 5123951 := bstep (se 1 (by rfl) ⟨3842963, by rfl⟩ : syracuseStep 5123951 = 7685927) B7685927
theorem B74879201 : Blo 1516955 74879201 := bstep (se 2 (by rfl) ⟨28079700, by rfl⟩ : syracuseStep 74879201 = 56159401) B56159401
theorem B5124329 : Blo 1516955 5124329 := bstep (se 2 (by rfl) ⟨1921623, by rfl⟩ : syracuseStep 5124329 = 3843247) B3843247
theorem B39965501 : Blo 1516955 39965501 := bstep (se 3 (by rfl) ⟨7493531, by rfl⟩ : syracuseStep 39965501 = 14987063) B14987063
theorem B2560889 : Blo 1516955 2560889 := bstep (se 2 (by rfl) ⟨960333, by rfl⟩ : syracuseStep 2560889 = 1920667) B1920667
theorem B12309815 : Blo 1516955 12309815 := bstep (se 1 (by rfl) ⟨9232361, by rfl⟩ : syracuseStep 12309815 = 18464723) B18464723
theorem B8647991 : Blo 1516955 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B7787839 : Blo 1516955 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B3413609 : Blo 1516955 3413609 := bstep (se 2 (by rfl) ⟨1280103, by rfl⟩ : syracuseStep 3413609 = 2560207) B2560207
theorem B1619995 : Blo 1516955 1619995 := bstep (se 1 (by rfl) ⟨1214996, by rfl⟩ : syracuseStep 1619995 = 2429993) B2429993
theorem B7682201 : Blo 1516955 7682201 := bstep (se 2 (by rfl) ⟨2880825, by rfl⟩ : syracuseStep 7682201 = 5761651) B5761651
theorem B7682687 : Blo 1516955 7682687 := bstep (se 1 (by rfl) ⟨5762015, by rfl⟩ : syracuseStep 7682687 = 11524031) B11524031
theorem B3415103 : Blo 1516955 3415103 := bstep (se 1 (by rfl) ⟨2561327, by rfl⟩ : syracuseStep 3415103 = 5122655) B5122655
theorem B2276459 : Blo 1516955 2276459 := bstep (se 1 (by rfl) ⟨1707344, by rfl⟩ : syracuseStep 2276459 = 3414689) B3414689
theorem B6921535 : Blo 1516955 6921535 := bstep (se 1 (by rfl) ⟨5191151, by rfl⟩ : syracuseStep 6921535 = 10382303) B10382303
theorem B3841607 : Blo 1516955 3841607 := bstep (se 1 (by rfl) ⟨2881205, by rfl⟩ : syracuseStep 3841607 = 5762411) B5762411
theorem B19439423 : Blo 1516955 19439423 := bstep (se 1 (by rfl) ⟨14579567, by rfl⟩ : syracuseStep 19439423 = 29159135) B29159135
theorem B2277371 : Blo 1516955 2277371 := bstep (se 1 (by rfl) ⟨1708028, by rfl⟩ : syracuseStep 2277371 = 3416057) B3416057
theorem B2277431 : Blo 1516955 2277431 := bstep (se 1 (by rfl) ⟨1708073, by rfl⟩ : syracuseStep 2277431 = 3416147) B3416147
theorem B29180047 : Blo 1516955 29180047 := bstep (se 1 (by rfl) ⟨21885035, by rfl⟩ : syracuseStep 29180047 = 43770071) B43770071
theorem B3416219 : Blo 1516955 3416219 := bstep (se 1 (by rfl) ⟨2562164, by rfl⟩ : syracuseStep 3416219 = 5124329) B5124329
theorem B26280359 : Blo 1516955 26280359 := bstep (se 1 (by rfl) ⟨19710269, by rfl⟩ : syracuseStep 26280359 = 39420539) B39420539
theorem B5121467 : Blo 1516955 5121467 := bstep (se 1 (by rfl) ⟨3841100, by rfl⟩ : syracuseStep 5121467 = 7682201) B7682201
theorem B5121791 : Blo 1516955 5121791 := bstep (se 1 (by rfl) ⟨3841343, by rfl⟩ : syracuseStep 5121791 = 7682687) B7682687
theorem B1517639 : Blo 1516955 1517639 := bstep (se 1 (by rfl) ⟨1138229, by rfl⟩ : syracuseStep 1517639 = 2276459) B2276459
theorem B1518247 : Blo 1516955 1518247 := bstep (se 1 (by rfl) ⟨1138685, by rfl⟩ : syracuseStep 1518247 = 2277371) B2277371
theorem B1518335 : Blo 1516955 1518335 := bstep (se 1 (by rfl) ⟨1138751, by rfl⟩ : syracuseStep 1518335 = 2277503) B2277503
theorem B26643667 : Blo 1516955 26643667 := bstep (se 1 (by rfl) ⟨19982750, by rfl⟩ : syracuseStep 26643667 = 39965501) B39965501
theorem B1707259 : Blo 1516955 1707259 := bstep (se 1 (by rfl) ⟨1280444, by rfl⟩ : syracuseStep 1707259 = 2560889) B2560889
theorem B9228713 : Blo 1516955 9228713 := bstep (se 2 (by rfl) ⟨3460767, by rfl⟩ : syracuseStep 9228713 = 6921535) B6921535
theorem B10383785 : Blo 1516955 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B2561071 : Blo 1516955 2561071 := bstep (se 1 (by rfl) ⟨1920803, by rfl⟩ : syracuseStep 2561071 = 3841607) B3841607
theorem B4863023 : Blo 1516955 4863023 := bstep (se 1 (by rfl) ⟨3647267, by rfl⟩ : syracuseStep 4863023 = 7294535) B7294535
theorem B2159993 : Blo 1516955 2159993 := bstep (se 2 (by rfl) ⟨809997, by rfl⟩ : syracuseStep 2159993 = 1619995) B1619995
theorem B199677869 : Blo 1516955 199677869 := bstep (se 3 (by rfl) ⟨37439600, by rfl⟩ : syracuseStep 199677869 = 74879201) B74879201
theorem B5838845 : Blo 1516955 5838845 := bstep (se 3 (by rfl) ⟨1094783, by rfl⟩ : syracuseStep 5838845 = 2189567) B2189567
theorem B8206543 : Blo 1516955 8206543 := bstep (se 1 (by rfl) ⟨6154907, by rfl⟩ : syracuseStep 8206543 = 12309815) B12309815
theorem B5765327 : Blo 1516955 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B3414239 : Blo 1516955 3414239 := bstep (se 1 (by rfl) ⟨2560679, by rfl⟩ : syracuseStep 3414239 = 5121359) B5121359
theorem B2275739 : Blo 1516955 2275739 := bstep (se 1 (by rfl) ⟨1706804, by rfl⟩ : syracuseStep 2275739 = 3413609) B3413609
theorem B3840655 : Blo 1516955 3840655 := bstep (se 1 (by rfl) ⟨2880491, by rfl⟩ : syracuseStep 3840655 = 5760983) B5760983
theorem B12966587 : Blo 1516955 12966587 := bstep (se 1 (by rfl) ⟨9724940, by rfl⟩ : syracuseStep 12966587 = 19449881) B19449881
theorem B88709975 : Blo 1516955 88709975 := bstep (se 1 (by rfl) ⟨66532481, by rfl⟩ : syracuseStep 88709975 = 133064963) B133064963
theorem B10935137 : Blo 1516955 10935137 := bstep (se 2 (by rfl) ⟨4100676, by rfl⟩ : syracuseStep 10935137 = 8201353) B8201353
theorem B3414995 : Blo 1516955 3414995 := bstep (se 1 (by rfl) ⟨2561246, by rfl⟩ : syracuseStep 3414995 = 5122493) B5122493
theorem B32808179 : Blo 1516955 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B2276735 : Blo 1516955 2276735 := bstep (se 1 (by rfl) ⟨1707551, by rfl⟩ : syracuseStep 2276735 = 3415103) B3415103
theorem B121478555 : Blo 1516955 121478555 := bstep (se 1 (by rfl) ⟨91108916, by rfl⟩ : syracuseStep 121478555 = 182217833) B182217833
theorem B3415607 : Blo 1516955 3415607 := bstep (se 1 (by rfl) ⟨2561705, by rfl⟩ : syracuseStep 3415607 = 5123411) B5123411
theorem B15572675 : Blo 1516955 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B12959615 : Blo 1516955 12959615 := bstep (se 1 (by rfl) ⟨9719711, by rfl⟩ : syracuseStep 12959615 = 19439423) B19439423
theorem B3415967 : Blo 1516955 3415967 := bstep (se 1 (by rfl) ⟨2561975, by rfl⟩ : syracuseStep 3415967 = 5123951) B5123951
theorem B2277479 : Blo 1516955 2277479 := bstep (se 1 (by rfl) ⟨1708109, by rfl⟩ : syracuseStep 2277479 = 3416219) B3416219
theorem B6922523 : Blo 1516955 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B5120873 : Blo 1516955 5120873 := bstep (se 2 (by rfl) ⟨1920327, by rfl⟩ : syracuseStep 5120873 = 3840655) B3840655
theorem B5759981 : Blo 1516955 5759981 := bstep (se 3 (by rfl) ⟨1079996, by rfl⟩ : syracuseStep 5759981 = 2159993) B2159993
theorem B24609901 : Blo 1516955 24609901 := bstep (se 3 (by rfl) ⟨4614356, by rfl⟩ : syracuseStep 24609901 = 9228713) B9228713
theorem B3843551 : Blo 1516955 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B1517159 : Blo 1516955 1517159 := bstep (se 1 (by rfl) ⟨1137869, by rfl⟩ : syracuseStep 1517159 = 2275739) B2275739
theorem B8644391 : Blo 1516955 8644391 := bstep (se 1 (by rfl) ⟨6483293, by rfl⟩ : syracuseStep 8644391 = 12966587) B12966587
theorem B41527133 : Blo 1516955 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B59139983 : Blo 1516955 59139983 := bstep (se 1 (by rfl) ⟨44354987, by rfl⟩ : syracuseStep 59139983 = 88709975) B88709975
theorem B1517823 : Blo 1516955 1517823 := bstep (se 1 (by rfl) ⟨1138367, by rfl⟩ : syracuseStep 1517823 = 2276735) B2276735
theorem B1518287 : Blo 1516955 1518287 := bstep (se 1 (by rfl) ⟨1138715, by rfl⟩ : syracuseStep 1518287 = 2277431) B2277431
theorem B38906729 : Blo 1516955 38906729 := bstep (se 2 (by rfl) ⟨14590023, by rfl⟩ : syracuseStep 38906729 = 29180047) B29180047
theorem B35524889 : Blo 1516955 35524889 := bstep (se 2 (by rfl) ⟨13321833, by rfl⟩ : syracuseStep 35524889 = 26643667) B26643667
theorem B8639743 : Blo 1516955 8639743 := bstep (se 1 (by rfl) ⟨6479807, by rfl⟩ : syracuseStep 8639743 = 12959615) B12959615
theorem B15570253 : Blo 1516955 15570253 := bstep (se 3 (by rfl) ⟨2919422, by rfl⟩ : syracuseStep 15570253 = 5838845) B5838845
theorem B10942057 : Blo 1516955 10942057 := bstep (se 2 (by rfl) ⟨4103271, by rfl⟩ : syracuseStep 10942057 = 8206543) B8206543
theorem B17520239 : Blo 1516955 17520239 := bstep (se 1 (by rfl) ⟨13140179, by rfl⟩ : syracuseStep 17520239 = 26280359) B26280359
theorem B3242015 : Blo 1516955 3242015 := bstep (se 1 (by rfl) ⟨2431511, by rfl⟩ : syracuseStep 3242015 = 4863023) B4863023
theorem B3414311 : Blo 1516955 3414311 := bstep (se 1 (by rfl) ⟨2560733, by rfl⟩ : syracuseStep 3414311 = 5121467) B5121467
theorem B3414527 : Blo 1516955 3414527 := bstep (se 1 (by rfl) ⟨2560895, by rfl⟩ : syracuseStep 3414527 = 5121791) B5121791
theorem B133118579 : Blo 1516955 133118579 := bstep (se 1 (by rfl) ⟨99838934, by rfl⟩ : syracuseStep 133118579 = 199677869) B199677869
theorem B3414761 : Blo 1516955 3414761 := bstep (se 2 (by rfl) ⟨1280535, by rfl⟩ : syracuseStep 3414761 = 2561071) B2561071
theorem B2276159 : Blo 1516955 2276159 := bstep (se 1 (by rfl) ⟨1707119, by rfl⟩ : syracuseStep 2276159 = 3414239) B3414239
theorem B2276345 : Blo 1516955 2276345 := bstep (se 2 (by rfl) ⟨853629, by rfl⟩ : syracuseStep 2276345 = 1707259) B1707259
theorem B7290091 : Blo 1516955 7290091 := bstep (se 1 (by rfl) ⟨5467568, by rfl⟩ : syracuseStep 7290091 = 10935137) B10935137
theorem B2276663 : Blo 1516955 2276663 := bstep (se 1 (by rfl) ⟨1707497, by rfl⟩ : syracuseStep 2276663 = 3414995) B3414995
theorem B21872119 : Blo 1516955 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B80985703 : Blo 1516955 80985703 := bstep (se 1 (by rfl) ⟨60739277, by rfl⟩ : syracuseStep 80985703 = 121478555) B121478555
theorem B2277071 : Blo 1516955 2277071 := bstep (se 1 (by rfl) ⟨1707803, by rfl⟩ : syracuseStep 2277071 = 3415607) B3415607
theorem B2277311 : Blo 1516955 2277311 := bstep (se 1 (by rfl) ⟨1707983, by rfl⟩ : syracuseStep 2277311 = 3415967) B3415967
theorem B23683259 : Blo 1516955 23683259 := bstep (se 1 (by rfl) ⟨17762444, by rfl⟩ : syracuseStep 23683259 = 35524889) B35524889
theorem B38880485 : Blo 1516955 38880485 := bstep (se 4 (by rfl) ⟨3645045, by rfl⟩ : syracuseStep 38880485 = 7290091) B7290091
theorem B11519657 : Blo 1516955 11519657 := bstep (se 2 (by rfl) ⟨4319871, by rfl⟩ : syracuseStep 11519657 = 8639743) B8639743
theorem B88745719 : Blo 1516955 88745719 := bstep (se 1 (by rfl) ⟨66559289, by rfl⟩ : syracuseStep 88745719 = 133118579) B133118579
theorem B20760337 : Blo 1516955 20760337 := bstep (se 2 (by rfl) ⟨7785126, by rfl⟩ : syracuseStep 20760337 = 15570253) B15570253
theorem B1517439 : Blo 1516955 1517439 := bstep (se 1 (by rfl) ⟨1138079, by rfl⟩ : syracuseStep 1517439 = 2276159) B2276159
theorem B25937819 : Blo 1516955 25937819 := bstep (se 1 (by rfl) ⟨19453364, by rfl⟩ : syracuseStep 25937819 = 38906729) B38906729
theorem B1517563 : Blo 1516955 1517563 := bstep (se 1 (by rfl) ⟨1138172, by rfl⟩ : syracuseStep 1517563 = 2276345) B2276345
theorem B107980937 : Blo 1516955 107980937 := bstep (se 2 (by rfl) ⟨40492851, by rfl⟩ : syracuseStep 107980937 = 80985703) B80985703
theorem B1517775 : Blo 1516955 1517775 := bstep (se 1 (by rfl) ⟨1138331, by rfl⟩ : syracuseStep 1517775 = 2276663) B2276663
theorem B157706621 : Blo 1516955 157706621 := bstep (se 3 (by rfl) ⟨29569991, by rfl⟩ : syracuseStep 157706621 = 59139983) B59139983
theorem B1518047 : Blo 1516955 1518047 := bstep (se 1 (by rfl) ⟨1138535, by rfl⟩ : syracuseStep 1518047 = 2277071) B2277071
theorem B1518207 : Blo 1516955 1518207 := bstep (se 1 (by rfl) ⟨1138655, by rfl⟩ : syracuseStep 1518207 = 2277311) B2277311
theorem B1518319 : Blo 1516955 1518319 := bstep (se 1 (by rfl) ⟨1138739, by rfl⟩ : syracuseStep 1518319 = 2277479) B2277479
theorem B4615015 : Blo 1516955 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B5762927 : Blo 1516955 5762927 := bstep (se 1 (by rfl) ⟨4322195, by rfl⟩ : syracuseStep 5762927 = 8644391) B8644391
theorem B27684755 : Blo 1516955 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B32813201 : Blo 1516955 32813201 := bstep (se 2 (by rfl) ⟨12304950, by rfl⟩ : syracuseStep 32813201 = 24609901) B24609901
theorem B3413915 : Blo 1516955 3413915 := bstep (se 1 (by rfl) ⟨2560436, by rfl⟩ : syracuseStep 3413915 = 5120873) B5120873
theorem B3839987 : Blo 1516955 3839987 := bstep (se 1 (by rfl) ⟨2879990, by rfl⟩ : syracuseStep 3839987 = 5759981) B5759981
theorem B2562367 : Blo 1516955 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B11680159 : Blo 1516955 11680159 := bstep (se 1 (by rfl) ⟨8760119, by rfl⟩ : syracuseStep 11680159 = 17520239) B17520239
theorem B2161343 : Blo 1516955 2161343 := bstep (se 1 (by rfl) ⟨1621007, by rfl⟩ : syracuseStep 2161343 = 3242015) B3242015
theorem B2276207 : Blo 1516955 2276207 := bstep (se 1 (by rfl) ⟨1707155, by rfl⟩ : syracuseStep 2276207 = 3414311) B3414311
theorem B2276351 : Blo 1516955 2276351 := bstep (se 1 (by rfl) ⟨1707263, by rfl⟩ : syracuseStep 2276351 = 3414527) B3414527
theorem B2276507 : Blo 1516955 2276507 := bstep (se 1 (by rfl) ⟨1707380, by rfl⟩ : syracuseStep 2276507 = 3414761) B3414761
theorem B29162825 : Blo 1516955 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B14589409 : Blo 1516955 14589409 := bstep (se 2 (by rfl) ⟨5471028, by rfl⟩ : syracuseStep 14589409 = 10942057) B10942057
theorem B3416489 : Blo 1516955 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B15573545 : Blo 1516955 15573545 := bstep (se 2 (by rfl) ⟨5840079, by rfl⟩ : syracuseStep 15573545 = 11680159) B11680159
theorem B25920323 : Blo 1516955 25920323 := bstep (se 1 (by rfl) ⟨19440242, by rfl⟩ : syracuseStep 25920323 = 38880485) B38880485
theorem B6153353 : Blo 1516955 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B105137747 : Blo 1516955 105137747 := bstep (se 1 (by rfl) ⟨78853310, by rfl⟩ : syracuseStep 105137747 = 157706621) B157706621
theorem B1517471 : Blo 1516955 1517471 := bstep (se 1 (by rfl) ⟨1138103, by rfl⟩ : syracuseStep 1517471 = 2276207) B2276207
theorem B1517567 : Blo 1516955 1517567 := bstep (se 1 (by rfl) ⟨1138175, by rfl⟩ : syracuseStep 1517567 = 2276351) B2276351
theorem B1517671 : Blo 1516955 1517671 := bstep (se 1 (by rfl) ⟨1138253, by rfl⟩ : syracuseStep 1517671 = 2276507) B2276507
theorem B19441883 : Blo 1516955 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B118327625 : Blo 1516955 118327625 := bstep (se 2 (by rfl) ⟨44372859, by rfl⟩ : syracuseStep 118327625 = 88745719) B88745719
theorem B21875467 : Blo 1516955 21875467 := bstep (se 1 (by rfl) ⟨16406600, by rfl⟩ : syracuseStep 21875467 = 32813201) B32813201
theorem B63155357 : Blo 1516955 63155357 := bstep (se 3 (by rfl) ⟨11841629, by rfl⟩ : syracuseStep 63155357 = 23683259) B23683259
theorem B7679771 : Blo 1516955 7679771 := bstep (se 1 (by rfl) ⟨5759828, by rfl⟩ : syracuseStep 7679771 = 11519657) B11519657
theorem B2559991 : Blo 1516955 2559991 := bstep (se 1 (by rfl) ⟨1919993, by rfl⟩ : syracuseStep 2559991 = 3839987) B3839987
theorem B71987291 : Blo 1516955 71987291 := bstep (se 1 (by rfl) ⟨53990468, by rfl⟩ : syracuseStep 71987291 = 107980937) B107980937
theorem B5763581 : Blo 1516955 5763581 := bstep (se 3 (by rfl) ⟨1080671, by rfl⟩ : syracuseStep 5763581 = 2161343) B2161343
theorem B19452545 : Blo 1516955 19452545 := bstep (se 2 (by rfl) ⟨7294704, by rfl⟩ : syracuseStep 19452545 = 14589409) B14589409
theorem B2275943 : Blo 1516955 2275943 := bstep (se 1 (by rfl) ⟨1706957, by rfl⟩ : syracuseStep 2275943 = 3413915) B3413915
theorem B17291879 : Blo 1516955 17291879 := bstep (se 1 (by rfl) ⟨12968909, by rfl⟩ : syracuseStep 17291879 = 25937819) B25937819
theorem B27680449 : Blo 1516955 27680449 := bstep (se 2 (by rfl) ⟨10380168, by rfl⟩ : syracuseStep 27680449 = 20760337) B20760337
theorem B3841951 : Blo 1516955 3841951 := bstep (se 1 (by rfl) ⟨2881463, by rfl⟩ : syracuseStep 3841951 = 5762927) B5762927
theorem B18456503 : Blo 1516955 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B2277659 : Blo 1516955 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B3842387 : Blo 1516955 3842387 := bstep (se 1 (by rfl) ⟨2881790, by rfl⟩ : syracuseStep 3842387 = 5763581) B5763581
theorem B12968363 : Blo 1516955 12968363 := bstep (se 1 (by rfl) ⟨9726272, by rfl⟩ : syracuseStep 12968363 = 19452545) B19452545
theorem B70091831 : Blo 1516955 70091831 := bstep (se 1 (by rfl) ⟨52568873, by rfl⟩ : syracuseStep 70091831 = 105137747) B105137747
theorem B12961255 : Blo 1516955 12961255 := bstep (se 1 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 12961255 = 19441883) B19441883
theorem B1517295 : Blo 1516955 1517295 := bstep (se 1 (by rfl) ⟨1137971, by rfl⟩ : syracuseStep 1517295 = 2275943) B2275943
theorem B11527919 : Blo 1516955 11527919 := bstep (se 1 (by rfl) ⟨8645939, by rfl⟩ : syracuseStep 11527919 = 17291879) B17291879
theorem B36907265 : Blo 1516955 36907265 := bstep (se 2 (by rfl) ⟨13840224, by rfl⟩ : syracuseStep 36907265 = 27680449) B27680449
theorem B5122601 : Blo 1516955 5122601 := bstep (se 2 (by rfl) ⟨1920975, by rfl⟩ : syracuseStep 5122601 = 3841951) B3841951
theorem B47991527 : Blo 1516955 47991527 := bstep (se 1 (by rfl) ⟨35993645, by rfl⟩ : syracuseStep 47991527 = 71987291) B71987291
theorem B10382363 : Blo 1516955 10382363 := bstep (se 1 (by rfl) ⟨7786772, by rfl⟩ : syracuseStep 10382363 = 15573545) B15573545
theorem B17280215 : Blo 1516955 17280215 := bstep (se 1 (by rfl) ⟨12960161, by rfl⟩ : syracuseStep 17280215 = 25920323) B25920323
theorem B29167289 : Blo 1516955 29167289 := bstep (se 2 (by rfl) ⟨10937733, by rfl⟩ : syracuseStep 29167289 = 21875467) B21875467
theorem B78885083 : Blo 1516955 78885083 := bstep (se 1 (by rfl) ⟨59163812, by rfl⟩ : syracuseStep 78885083 = 118327625) B118327625
theorem B42103571 : Blo 1516955 42103571 := bstep (se 1 (by rfl) ⟨31577678, by rfl⟩ : syracuseStep 42103571 = 63155357) B63155357
theorem B3413321 : Blo 1516955 3413321 := bstep (se 2 (by rfl) ⟨1279995, by rfl⟩ : syracuseStep 3413321 = 2559991) B2559991
theorem B4102235 : Blo 1516955 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B49217341 : Blo 1516955 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B5119847 : Blo 1516955 5119847 := bstep (se 1 (by rfl) ⟨3839885, by rfl⟩ : syracuseStep 5119847 = 7679771) B7679771
theorem B46727887 : Blo 1516955 46727887 := bstep (se 1 (by rfl) ⟨35045915, by rfl⟩ : syracuseStep 46727887 = 70091831) B70091831
theorem B7685279 : Blo 1516955 7685279 := bstep (se 1 (by rfl) ⟨5763959, by rfl⟩ : syracuseStep 7685279 = 11527919) B11527919
theorem B11520143 : Blo 1516955 11520143 := bstep (se 1 (by rfl) ⟨8640107, by rfl⟩ : syracuseStep 11520143 = 17280215) B17280215
theorem B1518439 : Blo 1516955 1518439 := bstep (se 1 (by rfl) ⟨1138829, by rfl⟩ : syracuseStep 1518439 = 2277659) B2277659
theorem B8645575 : Blo 1516955 8645575 := bstep (se 1 (by rfl) ⟨6484181, by rfl⟩ : syracuseStep 8645575 = 12968363) B12968363
theorem B24604843 : Blo 1516955 24604843 := bstep (se 1 (by rfl) ⟨18453632, by rfl⟩ : syracuseStep 24604843 = 36907265) B36907265
theorem B31994351 : Blo 1516955 31994351 := bstep (se 1 (by rfl) ⟨23995763, by rfl⟩ : syracuseStep 31994351 = 47991527) B47991527
theorem B17281673 : Blo 1516955 17281673 := bstep (se 2 (by rfl) ⟨6480627, by rfl⟩ : syracuseStep 17281673 = 12961255) B12961255
theorem B112276189 : Blo 1516955 112276189 := bstep (se 3 (by rfl) ⟨21051785, by rfl⟩ : syracuseStep 112276189 = 42103571) B42103571
theorem B65623121 : Blo 1516955 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B19444859 : Blo 1516955 19444859 := bstep (se 1 (by rfl) ⟨14583644, by rfl⟩ : syracuseStep 19444859 = 29167289) B29167289
theorem B3413231 : Blo 1516955 3413231 := bstep (se 1 (by rfl) ⟨2559923, by rfl⟩ : syracuseStep 3413231 = 5119847) B5119847
theorem B52590055 : Blo 1516955 52590055 := bstep (se 1 (by rfl) ⟨39442541, by rfl⟩ : syracuseStep 52590055 = 78885083) B78885083
theorem B2561591 : Blo 1516955 2561591 := bstep (se 1 (by rfl) ⟨1921193, by rfl⟩ : syracuseStep 2561591 = 3842387) B3842387
theorem B2275547 : Blo 1516955 2275547 := bstep (se 1 (by rfl) ⟨1706660, by rfl⟩ : syracuseStep 2275547 = 3413321) B3413321
theorem B2734823 : Blo 1516955 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B3415067 : Blo 1516955 3415067 := bstep (se 1 (by rfl) ⟨2561300, by rfl⟩ : syracuseStep 3415067 = 5122601) B5122601
theorem B6921575 : Blo 1516955 6921575 := bstep (se 1 (by rfl) ⟨5191181, by rfl⟩ : syracuseStep 6921575 = 10382363) B10382363
theorem B11527433 : Blo 1516955 11527433 := bstep (se 2 (by rfl) ⟨4322787, by rfl⟩ : syracuseStep 11527433 = 8645575) B8645575
theorem B1517031 : Blo 1516955 1517031 := bstep (se 1 (by rfl) ⟨1137773, by rfl⟩ : syracuseStep 1517031 = 2275547) B2275547
theorem B7292861 : Blo 1516955 7292861 := bstep (se 3 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 7292861 = 2734823) B2734823
theorem B4614383 : Blo 1516955 4614383 := bstep (se 1 (by rfl) ⟨3460787, by rfl⟩ : syracuseStep 4614383 = 6921575) B6921575
theorem B11521115 : Blo 1516955 11521115 := bstep (se 1 (by rfl) ⟨8640836, by rfl⟩ : syracuseStep 11521115 = 17281673) B17281673
theorem B43748747 : Blo 1516955 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B12963239 : Blo 1516955 12963239 := bstep (se 1 (by rfl) ⟨9722429, by rfl⟩ : syracuseStep 12963239 = 19444859) B19444859
theorem B5123519 : Blo 1516955 5123519 := bstep (se 1 (by rfl) ⟨3842639, by rfl⟩ : syracuseStep 5123519 = 7685279) B7685279
theorem B62303849 : Blo 1516955 62303849 := bstep (se 2 (by rfl) ⟨23363943, by rfl⟩ : syracuseStep 62303849 = 46727887) B46727887
theorem B1707727 : Blo 1516955 1707727 := bstep (se 1 (by rfl) ⟨1280795, by rfl⟩ : syracuseStep 1707727 = 2561591) B2561591
theorem B598806341 : Blo 1516955 598806341 := bstep (se 4 (by rfl) ⟨56138094, by rfl⟩ : syracuseStep 598806341 = 112276189) B112276189
theorem B7680095 : Blo 1516955 7680095 := bstep (se 1 (by rfl) ⟨5760071, by rfl⟩ : syracuseStep 7680095 = 11520143) B11520143
theorem B70120073 : Blo 1516955 70120073 := bstep (se 2 (by rfl) ⟨26295027, by rfl⟩ : syracuseStep 70120073 = 52590055) B52590055
theorem B32806457 : Blo 1516955 32806457 := bstep (se 2 (by rfl) ⟨12302421, by rfl⟩ : syracuseStep 32806457 = 24604843) B24604843
theorem B21329567 : Blo 1516955 21329567 := bstep (se 1 (by rfl) ⟨15997175, by rfl⟩ : syracuseStep 21329567 = 31994351) B31994351
theorem B2275487 : Blo 1516955 2275487 := bstep (se 1 (by rfl) ⟨1706615, by rfl⟩ : syracuseStep 2275487 = 3413231) B3413231
theorem B2276711 : Blo 1516955 2276711 := bstep (se 1 (by rfl) ⟨1707533, by rfl⟩ : syracuseStep 2276711 = 3415067) B3415067
theorem B5120063 : Blo 1516955 5120063 := bstep (se 1 (by rfl) ⟨3840047, by rfl⟩ : syracuseStep 5120063 = 7680095) B7680095
theorem B7684955 : Blo 1516955 7684955 := bstep (se 1 (by rfl) ⟨5763716, by rfl⟩ : syracuseStep 7684955 = 11527433) B11527433
theorem B1516991 : Blo 1516955 1516991 := bstep (se 1 (by rfl) ⟨1137743, by rfl⟩ : syracuseStep 1516991 = 2275487) B2275487
theorem B1517807 : Blo 1516955 1517807 := bstep (se 1 (by rfl) ⟨1138355, by rfl⟩ : syracuseStep 1517807 = 2276711) B2276711
theorem B29165831 : Blo 1516955 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B41535899 : Blo 1516955 41535899 := bstep (se 1 (by rfl) ⟨31151924, by rfl⟩ : syracuseStep 41535899 = 62303849) B62303849
theorem B46746715 : Blo 1516955 46746715 := bstep (se 1 (by rfl) ⟨35060036, by rfl⟩ : syracuseStep 46746715 = 70120073) B70120073
theorem B4861907 : Blo 1516955 4861907 := bstep (se 1 (by rfl) ⟨3646430, by rfl⟩ : syracuseStep 4861907 = 7292861) B7292861
theorem B3076255 : Blo 1516955 3076255 := bstep (se 1 (by rfl) ⟨2307191, by rfl⟩ : syracuseStep 3076255 = 4614383) B4614383
theorem B7680743 : Blo 1516955 7680743 := bstep (se 1 (by rfl) ⟨5760557, by rfl⟩ : syracuseStep 7680743 = 11521115) B11521115
theorem B21870971 : Blo 1516955 21870971 := bstep (se 1 (by rfl) ⟨16403228, by rfl⟩ : syracuseStep 21870971 = 32806457) B32806457
theorem B14219711 : Blo 1516955 14219711 := bstep (se 1 (by rfl) ⟨10664783, by rfl⟩ : syracuseStep 14219711 = 21329567) B21329567
theorem B2276969 : Blo 1516955 2276969 := bstep (se 2 (by rfl) ⟨853863, by rfl⟩ : syracuseStep 2276969 = 1707727) B1707727
theorem B8642159 : Blo 1516955 8642159 := bstep (se 1 (by rfl) ⟨6481619, by rfl⟩ : syracuseStep 8642159 = 12963239) B12963239
theorem B3415679 : Blo 1516955 3415679 := bstep (se 1 (by rfl) ⟨2561759, by rfl⟩ : syracuseStep 3415679 = 5123519) B5123519
theorem B399204227 : Blo 1516955 399204227 := bstep (se 1 (by rfl) ⟨299403170, by rfl⟩ : syracuseStep 399204227 = 598806341) B598806341
theorem B5120495 : Blo 1516955 5120495 := bstep (se 1 (by rfl) ⟨3840371, by rfl⟩ : syracuseStep 5120495 = 7680743) B7680743
theorem B27690599 : Blo 1516955 27690599 := bstep (se 1 (by rfl) ⟨20767949, by rfl⟩ : syracuseStep 27690599 = 41535899) B41535899
theorem B9479807 : Blo 1516955 9479807 := bstep (se 1 (by rfl) ⟨7109855, by rfl⟩ : syracuseStep 9479807 = 14219711) B14219711
theorem B1517979 : Blo 1516955 1517979 := bstep (se 1 (by rfl) ⟨1138484, by rfl⟩ : syracuseStep 1517979 = 2276969) B2276969
theorem B5761439 : Blo 1516955 5761439 := bstep (se 1 (by rfl) ⟨4321079, by rfl⟩ : syracuseStep 5761439 = 8642159) B8642159
theorem B266136151 : Blo 1516955 266136151 := bstep (se 1 (by rfl) ⟨199602113, by rfl⟩ : syracuseStep 266136151 = 399204227) B399204227
theorem B5123303 : Blo 1516955 5123303 := bstep (se 1 (by rfl) ⟨3842477, by rfl⟩ : syracuseStep 5123303 = 7684955) B7684955
theorem B62328953 : Blo 1516955 62328953 := bstep (se 2 (by rfl) ⟨23373357, by rfl⟩ : syracuseStep 62328953 = 46746715) B46746715
theorem B19443887 : Blo 1516955 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B3241271 : Blo 1516955 3241271 := bstep (se 1 (by rfl) ⟨2430953, by rfl⟩ : syracuseStep 3241271 = 4861907) B4861907
theorem B3413375 : Blo 1516955 3413375 := bstep (se 1 (by rfl) ⟨2560031, by rfl⟩ : syracuseStep 3413375 = 5120063) B5120063
theorem B4101673 : Blo 1516955 4101673 := bstep (se 2 (by rfl) ⟨1538127, by rfl⟩ : syracuseStep 4101673 = 3076255) B3076255
theorem B14580647 : Blo 1516955 14580647 := bstep (se 1 (by rfl) ⟨10935485, by rfl⟩ : syracuseStep 14580647 = 21870971) B21870971
theorem B2277119 : Blo 1516955 2277119 := bstep (se 1 (by rfl) ⟨1707839, by rfl⟩ : syracuseStep 2277119 = 3415679) B3415679
theorem B1518079 : Blo 1516955 1518079 := bstep (se 1 (by rfl) ⟨1138559, by rfl⟩ : syracuseStep 1518079 = 2277119) B2277119
theorem B41552635 : Blo 1516955 41552635 := bstep (se 1 (by rfl) ⟨31164476, by rfl⟩ : syracuseStep 41552635 = 62328953) B62328953
theorem B12962591 : Blo 1516955 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B354848201 : Blo 1516955 354848201 := bstep (se 2 (by rfl) ⟨133068075, by rfl⟩ : syracuseStep 354848201 = 266136151) B266136151
theorem B18460399 : Blo 1516955 18460399 := bstep (se 1 (by rfl) ⟨13845299, by rfl⟩ : syracuseStep 18460399 = 27690599) B27690599
theorem B6319871 : Blo 1516955 6319871 := bstep (se 1 (by rfl) ⟨4739903, by rfl⟩ : syracuseStep 6319871 = 9479807) B9479807
theorem B9720431 : Blo 1516955 9720431 := bstep (se 1 (by rfl) ⟨7290323, by rfl⟩ : syracuseStep 9720431 = 14580647) B14580647
theorem B5468897 : Blo 1516955 5468897 := bstep (se 2 (by rfl) ⟨2050836, by rfl⟩ : syracuseStep 5468897 = 4101673) B4101673
theorem B3413663 : Blo 1516955 3413663 := bstep (se 1 (by rfl) ⟨2560247, by rfl⟩ : syracuseStep 3413663 = 5120495) B5120495
theorem B2160847 : Blo 1516955 2160847 := bstep (se 1 (by rfl) ⟨1620635, by rfl⟩ : syracuseStep 2160847 = 3241271) B3241271
theorem B2275583 : Blo 1516955 2275583 := bstep (se 1 (by rfl) ⟨1706687, by rfl⟩ : syracuseStep 2275583 = 3413375) B3413375
theorem B3840959 : Blo 1516955 3840959 := bstep (se 1 (by rfl) ⟨2880719, by rfl⟩ : syracuseStep 3840959 = 5761439) B5761439
theorem B3415535 : Blo 1516955 3415535 := bstep (se 1 (by rfl) ⟨2561651, by rfl⟩ : syracuseStep 3415535 = 5123303) B5123303
theorem B6480287 : Blo 1516955 6480287 := bstep (se 1 (by rfl) ⟨4860215, by rfl⟩ : syracuseStep 6480287 = 9720431) B9720431
theorem B3645931 : Blo 1516955 3645931 := bstep (se 1 (by rfl) ⟨2734448, by rfl⟩ : syracuseStep 3645931 = 5468897) B5468897
theorem B55403513 : Blo 1516955 55403513 := bstep (se 2 (by rfl) ⟨20776317, by rfl⟩ : syracuseStep 55403513 = 41552635) B41552635
theorem B1517055 : Blo 1516955 1517055 := bstep (se 1 (by rfl) ⟨1137791, by rfl⟩ : syracuseStep 1517055 = 2275583) B2275583
theorem B4213247 : Blo 1516955 4213247 := bstep (se 1 (by rfl) ⟨3159935, by rfl⟩ : syracuseStep 4213247 = 6319871) B6319871
theorem B2560639 : Blo 1516955 2560639 := bstep (se 1 (by rfl) ⟨1920479, by rfl⟩ : syracuseStep 2560639 = 3840959) B3840959
theorem B236565467 : Blo 1516955 236565467 := bstep (se 1 (by rfl) ⟨177424100, by rfl⟩ : syracuseStep 236565467 = 354848201) B354848201
theorem B24613865 : Blo 1516955 24613865 := bstep (se 2 (by rfl) ⟨9230199, by rfl⟩ : syracuseStep 24613865 = 18460399) B18460399
theorem B11524517 : Blo 1516955 11524517 := bstep (se 4 (by rfl) ⟨1080423, by rfl⟩ : syracuseStep 11524517 = 2160847) B2160847
theorem B2275775 : Blo 1516955 2275775 := bstep (se 1 (by rfl) ⟨1706831, by rfl⟩ : syracuseStep 2275775 = 3413663) B3413663
theorem B8641727 : Blo 1516955 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B2277023 : Blo 1516955 2277023 := bstep (se 1 (by rfl) ⟨1707767, by rfl⟩ : syracuseStep 2277023 = 3415535) B3415535
theorem B16409243 : Blo 1516955 16409243 := bstep (se 1 (by rfl) ⟨12306932, by rfl⟩ : syracuseStep 16409243 = 24613865) B24613865
theorem B1517183 : Blo 1516955 1517183 := bstep (se 1 (by rfl) ⟨1137887, by rfl⟩ : syracuseStep 1517183 = 2275775) B2275775
theorem B5761151 : Blo 1516955 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B1518015 : Blo 1516955 1518015 := bstep (se 1 (by rfl) ⟨1138511, by rfl⟩ : syracuseStep 1518015 = 2277023) B2277023
theorem B4320191 : Blo 1516955 4320191 := bstep (se 1 (by rfl) ⟨3240143, by rfl⟩ : syracuseStep 4320191 = 6480287) B6480287
theorem B4861241 : Blo 1516955 4861241 := bstep (se 2 (by rfl) ⟨1822965, by rfl⟩ : syracuseStep 4861241 = 3645931) B3645931
theorem B157710311 : Blo 1516955 157710311 := bstep (se 1 (by rfl) ⟨118282733, by rfl⟩ : syracuseStep 157710311 = 236565467) B236565467
theorem B36935675 : Blo 1516955 36935675 := bstep (se 1 (by rfl) ⟨27701756, by rfl⟩ : syracuseStep 36935675 = 55403513) B55403513
theorem B3414185 : Blo 1516955 3414185 := bstep (se 2 (by rfl) ⟨1280319, by rfl⟩ : syracuseStep 3414185 = 2560639) B2560639
theorem B7683011 : Blo 1516955 7683011 := bstep (se 1 (by rfl) ⟨5762258, by rfl⟩ : syracuseStep 7683011 = 11524517) B11524517
theorem B44941301 : Blo 1516955 44941301 := bstep (se 5 (by rfl) ⟨2106623, by rfl⟩ : syracuseStep 44941301 = 4213247) B4213247
theorem B5122007 : Blo 1516955 5122007 := bstep (se 1 (by rfl) ⟨3841505, by rfl⟩ : syracuseStep 5122007 = 7683011) B7683011
theorem B29960867 : Blo 1516955 29960867 := bstep (se 1 (by rfl) ⟨22470650, by rfl⟩ : syracuseStep 29960867 = 44941301) B44941301
theorem B10939495 : Blo 1516955 10939495 := bstep (se 1 (by rfl) ⟨8204621, by rfl⟩ : syracuseStep 10939495 = 16409243) B16409243
theorem B105140207 : Blo 1516955 105140207 := bstep (se 1 (by rfl) ⟨78855155, by rfl⟩ : syracuseStep 105140207 = 157710311) B157710311
theorem B2880127 : Blo 1516955 2880127 := bstep (se 1 (by rfl) ⟨2160095, by rfl⟩ : syracuseStep 2880127 = 4320191) B4320191
theorem B3240827 : Blo 1516955 3240827 := bstep (se 1 (by rfl) ⟨2430620, by rfl⟩ : syracuseStep 3240827 = 4861241) B4861241
theorem B24623783 : Blo 1516955 24623783 := bstep (se 1 (by rfl) ⟨18467837, by rfl⟩ : syracuseStep 24623783 = 36935675) B36935675
theorem B3840767 : Blo 1516955 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B2276123 : Blo 1516955 2276123 := bstep (se 1 (by rfl) ⟨1707092, by rfl⟩ : syracuseStep 2276123 = 3414185) B3414185
theorem B1517415 : Blo 1516955 1517415 := bstep (se 1 (by rfl) ⟨1138061, by rfl⟩ : syracuseStep 1517415 = 2276123) B2276123
theorem B70093471 : Blo 1516955 70093471 := bstep (se 1 (by rfl) ⟨52570103, by rfl⟩ : syracuseStep 70093471 = 105140207) B105140207
theorem B14585993 : Blo 1516955 14585993 := bstep (se 2 (by rfl) ⟨5469747, by rfl⟩ : syracuseStep 14585993 = 10939495) B10939495
theorem B2560511 : Blo 1516955 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B2160551 : Blo 1516955 2160551 := bstep (se 1 (by rfl) ⟨1620413, by rfl⟩ : syracuseStep 2160551 = 3240827) B3240827
theorem B3840169 : Blo 1516955 3840169 := bstep (se 2 (by rfl) ⟨1440063, by rfl⟩ : syracuseStep 3840169 = 2880127) B2880127
theorem B3414671 : Blo 1516955 3414671 := bstep (se 1 (by rfl) ⟨2561003, by rfl⟩ : syracuseStep 3414671 = 5122007) B5122007
theorem B79895645 : Blo 1516955 79895645 := bstep (se 3 (by rfl) ⟨14980433, by rfl⟩ : syracuseStep 79895645 = 29960867) B29960867
theorem B16415855 : Blo 1516955 16415855 := bstep (se 1 (by rfl) ⟨12311891, by rfl⟩ : syracuseStep 16415855 = 24623783) B24623783
theorem B9723995 : Blo 1516955 9723995 := bstep (se 1 (by rfl) ⟨7292996, by rfl⟩ : syracuseStep 9723995 = 14585993) B14585993
theorem B5120225 : Blo 1516955 5120225 := bstep (se 2 (by rfl) ⟨1920084, by rfl⟩ : syracuseStep 5120225 = 3840169) B3840169
theorem B5761469 : Blo 1516955 5761469 := bstep (se 3 (by rfl) ⟨1080275, by rfl⟩ : syracuseStep 5761469 = 2160551) B2160551
theorem B1707007 : Blo 1516955 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B93457961 : Blo 1516955 93457961 := bstep (se 2 (by rfl) ⟨35046735, by rfl⟩ : syracuseStep 93457961 = 70093471) B70093471
theorem B2276447 : Blo 1516955 2276447 := bstep (se 1 (by rfl) ⟨1707335, by rfl⟩ : syracuseStep 2276447 = 3414671) B3414671
theorem B53263763 : Blo 1516955 53263763 := bstep (se 1 (by rfl) ⟨39947822, by rfl⟩ : syracuseStep 53263763 = 79895645) B79895645
theorem B10943903 : Blo 1516955 10943903 := bstep (se 1 (by rfl) ⟨8207927, by rfl⟩ : syracuseStep 10943903 = 16415855) B16415855
theorem B1517631 : Blo 1516955 1517631 := bstep (se 1 (by rfl) ⟨1138223, by rfl⟩ : syracuseStep 1517631 = 2276447) B2276447
theorem B6482663 : Blo 1516955 6482663 := bstep (se 1 (by rfl) ⟨4861997, by rfl⟩ : syracuseStep 6482663 = 9723995) B9723995
theorem B35509175 : Blo 1516955 35509175 := bstep (se 1 (by rfl) ⟨26631881, by rfl⟩ : syracuseStep 35509175 = 53263763) B53263763
theorem B7295935 : Blo 1516955 7295935 := bstep (se 1 (by rfl) ⟨5471951, by rfl⟩ : syracuseStep 7295935 = 10943903) B10943903
theorem B62305307 : Blo 1516955 62305307 := bstep (se 1 (by rfl) ⟨46728980, by rfl⟩ : syracuseStep 62305307 = 93457961) B93457961
theorem B3413483 : Blo 1516955 3413483 := bstep (se 1 (by rfl) ⟨2560112, by rfl⟩ : syracuseStep 3413483 = 5120225) B5120225
theorem B2276009 : Blo 1516955 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B3840979 : Blo 1516955 3840979 := bstep (se 1 (by rfl) ⟨2880734, by rfl⟩ : syracuseStep 3840979 = 5761469) B5761469
theorem B5121305 : Blo 1516955 5121305 := bstep (se 2 (by rfl) ⟨1920489, by rfl⟩ : syracuseStep 5121305 = 3840979) B3840979
theorem B1517339 : Blo 1516955 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B41536871 : Blo 1516955 41536871 := bstep (se 1 (by rfl) ⟨31152653, by rfl⟩ : syracuseStep 41536871 = 62305307) B62305307
theorem B9727913 : Blo 1516955 9727913 := bstep (se 2 (by rfl) ⟨3647967, by rfl⟩ : syracuseStep 9727913 = 7295935) B7295935
theorem B4321775 : Blo 1516955 4321775 := bstep (se 1 (by rfl) ⟨3241331, by rfl⟩ : syracuseStep 4321775 = 6482663) B6482663
theorem B23672783 : Blo 1516955 23672783 := bstep (se 1 (by rfl) ⟨17754587, by rfl⟩ : syracuseStep 23672783 = 35509175) B35509175
theorem B2275655 : Blo 1516955 2275655 := bstep (se 1 (by rfl) ⟨1706741, by rfl⟩ : syracuseStep 2275655 = 3413483) B3413483
theorem B1517103 : Blo 1516955 1517103 := bstep (se 1 (by rfl) ⟨1137827, by rfl⟩ : syracuseStep 1517103 = 2275655) B2275655
theorem B27691247 : Blo 1516955 27691247 := bstep (se 1 (by rfl) ⟨20768435, by rfl⟩ : syracuseStep 27691247 = 41536871) B41536871
theorem B6485275 : Blo 1516955 6485275 := bstep (se 1 (by rfl) ⟨4863956, by rfl⟩ : syracuseStep 6485275 = 9727913) B9727913
theorem B2881183 : Blo 1516955 2881183 := bstep (se 1 (by rfl) ⟨2160887, by rfl⟩ : syracuseStep 2881183 = 4321775) B4321775
theorem B3414203 : Blo 1516955 3414203 := bstep (se 1 (by rfl) ⟨2560652, by rfl⟩ : syracuseStep 3414203 = 5121305) B5121305
theorem B63127421 : Blo 1516955 63127421 := bstep (se 3 (by rfl) ⟨11836391, by rfl⟩ : syracuseStep 63127421 = 23672783) B23672783
theorem B42084947 : Blo 1516955 42084947 := bstep (se 1 (by rfl) ⟨31563710, by rfl⟩ : syracuseStep 42084947 = 63127421) B63127421
theorem B18460831 : Blo 1516955 18460831 := bstep (se 1 (by rfl) ⟨13845623, by rfl⟩ : syracuseStep 18460831 = 27691247) B27691247
theorem B8647033 : Blo 1516955 8647033 := bstep (se 2 (by rfl) ⟨3242637, by rfl⟩ : syracuseStep 8647033 = 6485275) B6485275
theorem B2276135 : Blo 1516955 2276135 := bstep (se 1 (by rfl) ⟨1707101, by rfl⟩ : syracuseStep 2276135 = 3414203) B3414203
theorem B3841577 : Blo 1516955 3841577 := bstep (se 2 (by rfl) ⟨1440591, by rfl⟩ : syracuseStep 3841577 = 2881183) B2881183
theorem B1517423 : Blo 1516955 1517423 := bstep (se 1 (by rfl) ⟨1138067, by rfl⟩ : syracuseStep 1517423 = 2276135) B2276135
theorem B11529377 : Blo 1516955 11529377 := bstep (se 2 (by rfl) ⟨4323516, by rfl⟩ : syracuseStep 11529377 = 8647033) B8647033
theorem B2561051 : Blo 1516955 2561051 := bstep (se 1 (by rfl) ⟨1920788, by rfl⟩ : syracuseStep 2561051 = 3841577) B3841577
theorem B24614441 : Blo 1516955 24614441 := bstep (se 2 (by rfl) ⟨9230415, by rfl⟩ : syracuseStep 24614441 = 18460831) B18460831
theorem B28056631 : Blo 1516955 28056631 := bstep (se 1 (by rfl) ⟨21042473, by rfl⟩ : syracuseStep 28056631 = 42084947) B42084947
theorem B16409627 : Blo 1516955 16409627 := bstep (se 1 (by rfl) ⟨12307220, by rfl⟩ : syracuseStep 16409627 = 24614441) B24614441
theorem B7686251 : Blo 1516955 7686251 := bstep (se 1 (by rfl) ⟨5764688, by rfl⟩ : syracuseStep 7686251 = 11529377) B11529377
theorem B1707367 : Blo 1516955 1707367 := bstep (se 1 (by rfl) ⟨1280525, by rfl⟩ : syracuseStep 1707367 = 2561051) B2561051
theorem B37408841 : Blo 1516955 37408841 := bstep (se 2 (by rfl) ⟨14028315, by rfl⟩ : syracuseStep 37408841 = 28056631) B28056631
theorem B24939227 : Blo 1516955 24939227 := bstep (se 1 (by rfl) ⟨18704420, by rfl⟩ : syracuseStep 24939227 = 37408841) B37408841
theorem B10939751 : Blo 1516955 10939751 := bstep (se 1 (by rfl) ⟨8204813, by rfl⟩ : syracuseStep 10939751 = 16409627) B16409627
theorem B5124167 : Blo 1516955 5124167 := bstep (se 1 (by rfl) ⟨3843125, by rfl⟩ : syracuseStep 5124167 = 7686251) B7686251
theorem B2276489 : Blo 1516955 2276489 := bstep (se 2 (by rfl) ⟨853683, by rfl⟩ : syracuseStep 2276489 = 1707367) B1707367
theorem B3416111 : Blo 1516955 3416111 := bstep (se 1 (by rfl) ⟨2562083, by rfl⟩ : syracuseStep 3416111 = 5124167) B5124167
theorem B1517659 : Blo 1516955 1517659 := bstep (se 1 (by rfl) ⟨1138244, by rfl⟩ : syracuseStep 1517659 = 2276489) B2276489
theorem B7293167 : Blo 1516955 7293167 := bstep (se 1 (by rfl) ⟨5469875, by rfl⟩ : syracuseStep 7293167 = 10939751) B10939751
theorem B16626151 : Blo 1516955 16626151 := bstep (se 1 (by rfl) ⟨12469613, by rfl⟩ : syracuseStep 16626151 = 24939227) B24939227
theorem B2277407 : Blo 1516955 2277407 := bstep (se 1 (by rfl) ⟨1708055, by rfl⟩ : syracuseStep 2277407 = 3416111) B3416111
theorem B88672805 : Blo 1516955 88672805 := bstep (se 4 (by rfl) ⟨8313075, by rfl⟩ : syracuseStep 88672805 = 16626151) B16626151
theorem B4862111 : Blo 1516955 4862111 := bstep (se 1 (by rfl) ⟨3646583, by rfl⟩ : syracuseStep 4862111 = 7293167) B7293167
theorem B59115203 : Blo 1516955 59115203 := bstep (se 1 (by rfl) ⟨44336402, by rfl⟩ : syracuseStep 59115203 = 88672805) B88672805
theorem B1518271 : Blo 1516955 1518271 := bstep (se 1 (by rfl) ⟨1138703, by rfl⟩ : syracuseStep 1518271 = 2277407) B2277407
theorem B12965629 : Blo 1516955 12965629 := bstep (se 3 (by rfl) ⟨2431055, by rfl⟩ : syracuseStep 12965629 = 4862111) B4862111
theorem B17287505 : Blo 1516955 17287505 := bstep (se 2 (by rfl) ⟨6482814, by rfl⟩ : syracuseStep 17287505 = 12965629) B12965629
theorem B39410135 : Blo 1516955 39410135 := bstep (se 1 (by rfl) ⟨29557601, by rfl⟩ : syracuseStep 39410135 = 59115203) B59115203
theorem B26273423 : Blo 1516955 26273423 := bstep (se 1 (by rfl) ⟨19705067, by rfl⟩ : syracuseStep 26273423 = 39410135) B39410135
theorem B11525003 : Blo 1516955 11525003 := bstep (se 1 (by rfl) ⟨8643752, by rfl⟩ : syracuseStep 11525003 = 17287505) B17287505
theorem B17515615 : Blo 1516955 17515615 := bstep (se 1 (by rfl) ⟨13136711, by rfl⟩ : syracuseStep 17515615 = 26273423) B26273423
theorem B7683335 : Blo 1516955 7683335 := bstep (se 1 (by rfl) ⟨5762501, by rfl⟩ : syracuseStep 7683335 = 11525003) B11525003
theorem B5122223 : Blo 1516955 5122223 := bstep (se 1 (by rfl) ⟨3841667, by rfl⟩ : syracuseStep 5122223 = 7683335) B7683335
theorem B23354153 : Blo 1516955 23354153 := bstep (se 2 (by rfl) ⟨8757807, by rfl⟩ : syracuseStep 23354153 = 17515615) B17515615
theorem B15569435 : Blo 1516955 15569435 := bstep (se 1 (by rfl) ⟨11677076, by rfl⟩ : syracuseStep 15569435 = 23354153) B23354153
theorem B3414815 : Blo 1516955 3414815 := bstep (se 1 (by rfl) ⟨2561111, by rfl⟩ : syracuseStep 3414815 = 5122223) B5122223
theorem B10379623 : Blo 1516955 10379623 := bstep (se 1 (by rfl) ⟨7784717, by rfl⟩ : syracuseStep 10379623 = 15569435) B15569435
theorem B2276543 : Blo 1516955 2276543 := bstep (se 1 (by rfl) ⟨1707407, by rfl⟩ : syracuseStep 2276543 = 3414815) B3414815
theorem B1517695 : Blo 1516955 1517695 := bstep (se 1 (by rfl) ⟨1138271, by rfl⟩ : syracuseStep 1517695 = 2276543) B2276543
theorem B13839497 : Blo 1516955 13839497 := bstep (se 2 (by rfl) ⟨5189811, by rfl⟩ : syracuseStep 13839497 = 10379623) B10379623
theorem B9226331 : Blo 1516955 9226331 := bstep (se 1 (by rfl) ⟨6919748, by rfl⟩ : syracuseStep 9226331 = 13839497) B13839497
theorem B6150887 : Blo 1516955 6150887 := bstep (se 1 (by rfl) ⟨4613165, by rfl⟩ : syracuseStep 6150887 = 9226331) B9226331
theorem B4100591 : Blo 1516955 4100591 := bstep (se 1 (by rfl) ⟨3075443, by rfl⟩ : syracuseStep 4100591 = 6150887) B6150887
theorem B10934909 : Blo 1516955 10934909 := bstep (se 3 (by rfl) ⟨2050295, by rfl⟩ : syracuseStep 10934909 = 4100591) B4100591
theorem B7289939 : Blo 1516955 7289939 := bstep (se 1 (by rfl) ⟨5467454, by rfl⟩ : syracuseStep 7289939 = 10934909) B10934909
theorem B4859959 : Blo 1516955 4859959 := bstep (se 1 (by rfl) ⟨3644969, by rfl⟩ : syracuseStep 4859959 = 7289939) B7289939
theorem B6479945 : Blo 1516955 6479945 := bstep (se 2 (by rfl) ⟨2429979, by rfl⟩ : syracuseStep 6479945 = 4859959) B4859959
theorem B4319963 : Blo 1516955 4319963 := bstep (se 1 (by rfl) ⟨3239972, by rfl⟩ : syracuseStep 4319963 = 6479945) B6479945
theorem B2879975 : Blo 1516955 2879975 := bstep (se 1 (by rfl) ⟨2159981, by rfl⟩ : syracuseStep 2879975 = 4319963) B4319963
theorem B7679933 : Blo 1516955 7679933 := bstep (se 3 (by rfl) ⟨1439987, by rfl⟩ : syracuseStep 7679933 = 2879975) B2879975
theorem B5119955 : Blo 1516955 5119955 := bstep (se 1 (by rfl) ⟨3839966, by rfl⟩ : syracuseStep 5119955 = 7679933) B7679933
theorem B3413303 : Blo 1516955 3413303 := bstep (se 1 (by rfl) ⟨2559977, by rfl⟩ : syracuseStep 3413303 = 5119955) B5119955
theorem B2275535 : Blo 1516955 2275535 := bstep (se 1 (by rfl) ⟨1706651, by rfl⟩ : syracuseStep 2275535 = 3413303) B3413303
theorem B1517023 : Blo 1516955 1517023 := bstep (se 1 (by rfl) ⟨1137767, by rfl⟩ : syracuseStep 1517023 = 2275535) B2275535

theorem C0 (j : ℕ) (h1 : 379238 ≤ j) (h2 : j ≤ 379613) : Blo 1516955 (4 * j + 3) := by
  interval_cases j
  · exact B1516955
  · exact B1516959
  · exact B1516963
  · exact B1516967
  · exact B1516971
  · exact B1516975
  · exact B1516979
  · exact B1516983
  · exact B1516987
  · exact B1516991
  · exact B1516995
  · exact B1516999
  · exact B1517003
  · exact B1517007
  · exact B1517011
  · exact B1517015
  · exact B1517019
  · exact B1517023
  · exact B1517027
  · exact B1517031
  · exact B1517035
  · exact B1517039
  · exact B1517043
  · exact B1517047
  · exact B1517051
  · exact B1517055
  · exact B1517059
  · exact B1517063
  · exact B1517067
  · exact B1517071
  · exact B1517075
  · exact B1517079
  · exact B1517083
  · exact B1517087
  · exact B1517091
  · exact B1517095
  · exact B1517099
  · exact B1517103
  · exact B1517107
  · exact B1517111
  · exact B1517115
  · exact B1517119
  · exact B1517123
  · exact B1517127
  · exact B1517131
  · exact B1517135
  · exact B1517139
  · exact B1517143
  · exact B1517147
  · exact B1517151
  · exact B1517155
  · exact B1517159
  · exact B1517163
  · exact B1517167
  · exact B1517171
  · exact B1517175
  · exact B1517179
  · exact B1517183
  · exact B1517187
  · exact B1517191
  · exact B1517195
  · exact B1517199
  · exact B1517203
  · exact B1517207
  · exact B1517211
  · exact B1517215
  · exact B1517219
  · exact B1517223
  · exact B1517227
  · exact B1517231
  · exact B1517235
  · exact B1517239
  · exact B1517243
  · exact B1517247
  · exact B1517251
  · exact B1517255
  · exact B1517259
  · exact B1517263
  · exact B1517267
  · exact B1517271
  · exact B1517275
  · exact B1517279
  · exact B1517283
  · exact B1517287
  · exact B1517291
  · exact B1517295
  · exact B1517299
  · exact B1517303
  · exact B1517307
  · exact B1517311
  · exact B1517315
  · exact B1517319
  · exact B1517323
  · exact B1517327
  · exact B1517331
  · exact B1517335
  · exact B1517339
  · exact B1517343
  · exact B1517347
  · exact B1517351
  · exact B1517355
  · exact B1517359
  · exact B1517363
  · exact B1517367
  · exact B1517371
  · exact B1517375
  · exact B1517379
  · exact B1517383
  · exact B1517387
  · exact B1517391
  · exact B1517395
  · exact B1517399
  · exact B1517403
  · exact B1517407
  · exact B1517411
  · exact B1517415
  · exact B1517419
  · exact B1517423
  · exact B1517427
  · exact B1517431
  · exact B1517435
  · exact B1517439
  · exact B1517443
  · exact B1517447
  · exact B1517451
  · exact B1517455
  · exact B1517459
  · exact B1517463
  · exact B1517467
  · exact B1517471
  · exact B1517475
  · exact B1517479
  · exact B1517483
  · exact B1517487
  · exact B1517491
  · exact B1517495
  · exact B1517499
  · exact B1517503
  · exact B1517507
  · exact B1517511
  · exact B1517515
  · exact B1517519
  · exact B1517523
  · exact B1517527
  · exact B1517531
  · exact B1517535
  · exact B1517539
  · exact B1517543
  · exact B1517547
  · exact B1517551
  · exact B1517555
  · exact B1517559
  · exact B1517563
  · exact B1517567
  · exact B1517571
  · exact B1517575
  · exact B1517579
  · exact B1517583
  · exact B1517587
  · exact B1517591
  · exact B1517595
  · exact B1517599
  · exact B1517603
  · exact B1517607
  · exact B1517611
  · exact B1517615
  · exact B1517619
  · exact B1517623
  · exact B1517627
  · exact B1517631
  · exact B1517635
  · exact B1517639
  · exact B1517643
  · exact B1517647
  · exact B1517651
  · exact B1517655
  · exact B1517659
  · exact B1517663
  · exact B1517667
  · exact B1517671
  · exact B1517675
  · exact B1517679
  · exact B1517683
  · exact B1517687
  · exact B1517691
  · exact B1517695
  · exact B1517699
  · exact B1517703
  · exact B1517707
  · exact B1517711
  · exact B1517715
  · exact B1517719
  · exact B1517723
  · exact B1517727
  · exact B1517731
  · exact B1517735
  · exact B1517739
  · exact B1517743
  · exact B1517747
  · exact B1517751
  · exact B1517755
  · exact B1517759
  · exact B1517763
  · exact B1517767
  · exact B1517771
  · exact B1517775
  · exact B1517779
  · exact B1517783
  · exact B1517787
  · exact B1517791
  · exact B1517795
  · exact B1517799
  · exact B1517803
  · exact B1517807
  · exact B1517811
  · exact B1517815
  · exact B1517819
  · exact B1517823
  · exact B1517827
  · exact B1517831
  · exact B1517835
  · exact B1517839
  · exact B1517843
  · exact B1517847
  · exact B1517851
  · exact B1517855
  · exact B1517859
  · exact B1517863
  · exact B1517867
  · exact B1517871
  · exact B1517875
  · exact B1517879
  · exact B1517883
  · exact B1517887
  · exact B1517891
  · exact B1517895
  · exact B1517899
  · exact B1517903
  · exact B1517907
  · exact B1517911
  · exact B1517915
  · exact B1517919
  · exact B1517923
  · exact B1517927
  · exact B1517931
  · exact B1517935
  · exact B1517939
  · exact B1517943
  · exact B1517947
  · exact B1517951
  · exact B1517955
  · exact B1517959
  · exact B1517963
  · exact B1517967
  · exact B1517971
  · exact B1517975
  · exact B1517979
  · exact B1517983
  · exact B1517987
  · exact B1517991
  · exact B1517995
  · exact B1517999
  · exact B1518003
  · exact B1518007
  · exact B1518011
  · exact B1518015
  · exact B1518019
  · exact B1518023
  · exact B1518027
  · exact B1518031
  · exact B1518035
  · exact B1518039
  · exact B1518043
  · exact B1518047
  · exact B1518051
  · exact B1518055
  · exact B1518059
  · exact B1518063
  · exact B1518067
  · exact B1518071
  · exact B1518075
  · exact B1518079
  · exact B1518083
  · exact B1518087
  · exact B1518091
  · exact B1518095
  · exact B1518099
  · exact B1518103
  · exact B1518107
  · exact B1518111
  · exact B1518115
  · exact B1518119
  · exact B1518123
  · exact B1518127
  · exact B1518131
  · exact B1518135
  · exact B1518139
  · exact B1518143
  · exact B1518147
  · exact B1518151
  · exact B1518155
  · exact B1518159
  · exact B1518163
  · exact B1518167
  · exact B1518171
  · exact B1518175
  · exact B1518179
  · exact B1518183
  · exact B1518187
  · exact B1518191
  · exact B1518195
  · exact B1518199
  · exact B1518203
  · exact B1518207
  · exact B1518211
  · exact B1518215
  · exact B1518219
  · exact B1518223
  · exact B1518227
  · exact B1518231
  · exact B1518235
  · exact B1518239
  · exact B1518243
  · exact B1518247
  · exact B1518251
  · exact B1518255
  · exact B1518259
  · exact B1518263
  · exact B1518267
  · exact B1518271
  · exact B1518275
  · exact B1518279
  · exact B1518283
  · exact B1518287
  · exact B1518291
  · exact B1518295
  · exact B1518299
  · exact B1518303
  · exact B1518307
  · exact B1518311
  · exact B1518315
  · exact B1518319
  · exact B1518323
  · exact B1518327
  · exact B1518331
  · exact B1518335
  · exact B1518339
  · exact B1518343
  · exact B1518347
  · exact B1518351
  · exact B1518355
  · exact B1518359
  · exact B1518363
  · exact B1518367
  · exact B1518371
  · exact B1518375
  · exact B1518379
  · exact B1518383
  · exact B1518387
  · exact B1518391
  · exact B1518395
  · exact B1518399
  · exact B1518403
  · exact B1518407
  · exact B1518411
  · exact B1518415
  · exact B1518419
  · exact B1518423
  · exact B1518427
  · exact B1518431
  · exact B1518435
  · exact B1518439
  · exact B1518443
  · exact B1518447
  · exact B1518451
  · exact B1518455

theorem solution (m : ℕ) (hlo : 1516955 ≤ m) (hhi : m ≤ 1518455) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 379238 ≤ j := by omega
    have hj2 : j ≤ 379613 := by omega
    have hb : Blo 1516955 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
