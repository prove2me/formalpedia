-- Prove2me | solution 1 for syracuse_descends_range_1566981_1568981
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:06:46.070426+00:00
-- url     : https://prove2.me/submissions/59edc8aa-7ec2-4c7b-87c1-562d33a724a5

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


theorem B2351117 : Blo 1566981 2351117 := bbase (se 3 (by rfl) ⟨440834, by rfl⟩ : syracuseStep 2351117 = 881669) (by norm_num)
theorem B5292053 : Blo 1566981 5292053 := bbase (se 6 (by rfl) ⟨124032, by rfl⟩ : syracuseStep 5292053 = 248065) (by norm_num)
theorem B2351141 : Blo 1566981 2351141 := bbase (se 4 (by rfl) ⟨220419, by rfl⟩ : syracuseStep 2351141 = 440839) (by norm_num)
theorem B2351165 : Blo 1566981 2351165 := bbase (se 3 (by rfl) ⟨440843, by rfl⟩ : syracuseStep 2351165 = 881687) (by norm_num)
theorem B2351189 : Blo 1566981 2351189 := bbase (se 8 (by rfl) ⟨13776, by rfl⟩ : syracuseStep 2351189 = 27553) (by norm_num)
theorem B2646101 : Blo 1566981 2646101 := bbase (se 8 (by rfl) ⟨15504, by rfl⟩ : syracuseStep 2646101 = 31009) (by norm_num)
theorem B101761109 : Blo 1566981 101761109 := bbase (se 8 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 101761109 = 1192513) (by norm_num)
theorem B3350621 : Blo 1566981 3350621 := bbase (se 3 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 3350621 = 1256483) (by norm_num)
theorem B2351213 : Blo 1566981 2351213 := bbase (se 3 (by rfl) ⟨440852, by rfl⟩ : syracuseStep 2351213 = 881705) (by norm_num)
theorem B6791285 : Blo 1566981 6791285 := bbase (se 5 (by rfl) ⟨318341, by rfl⟩ : syracuseStep 6791285 = 636683) (by norm_num)
theorem B2351237 : Blo 1566981 2351237 := bbase (se 4 (by rfl) ⟨220428, by rfl⟩ : syracuseStep 2351237 = 440857) (by norm_num)
theorem B1589393 : Blo 1566981 1589393 := bbase (se 2 (by rfl) ⟨596022, by rfl⟩ : syracuseStep 1589393 = 1192045) (by norm_num)
theorem B2351261 : Blo 1566981 2351261 := bbase (se 3 (by rfl) ⟨440861, by rfl⟩ : syracuseStep 2351261 = 881723) (by norm_num)
theorem B2351285 : Blo 1566981 2351285 := bbase (se 5 (by rfl) ⟨110216, by rfl⟩ : syracuseStep 2351285 = 220433) (by norm_num)
theorem B5652661 : Blo 1566981 5652661 := bbase (se 5 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 5652661 = 529937) (by norm_num)
theorem B2351309 : Blo 1566981 2351309 := bbase (se 3 (by rfl) ⟨440870, by rfl⟩ : syracuseStep 2351309 = 881741) (by norm_num)
theorem B2646229 : Blo 1566981 2646229 := bbase (se 7 (by rfl) ⟨31010, by rfl⟩ : syracuseStep 2646229 = 62021) (by norm_num)
theorem B2351333 : Blo 1566981 2351333 := bbase (se 4 (by rfl) ⟨220437, by rfl⟩ : syracuseStep 2351333 = 440875) (by norm_num)
theorem B2351357 : Blo 1566981 2351357 := bbase (se 3 (by rfl) ⟨440879, by rfl⟩ : syracuseStep 2351357 = 881759) (by norm_num)
theorem B2351381 : Blo 1566981 2351381 := bbase (se 6 (by rfl) ⟨55110, by rfl⟩ : syracuseStep 2351381 = 110221) (by norm_num)
theorem B2351405 : Blo 1566981 2351405 := bbase (se 3 (by rfl) ⟨440888, by rfl⟩ : syracuseStep 2351405 = 881777) (by norm_num)
theorem B2646317 : Blo 1566981 2646317 := bbase (se 3 (by rfl) ⟨496184, by rfl⟩ : syracuseStep 2646317 = 992369) (by norm_num)
theorem B2351429 : Blo 1566981 2351429 := bbase (se 4 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 2351429 = 440893) (by norm_num)
theorem B2351453 : Blo 1566981 2351453 := bbase (se 3 (by rfl) ⟨440897, by rfl⟩ : syracuseStep 2351453 = 881795) (by norm_num)
theorem B6701413 : Blo 1566981 6701413 := bbase (se 4 (by rfl) ⟨628257, by rfl⟩ : syracuseStep 6701413 = 1256515) (by norm_num)
theorem B2351477 : Blo 1566981 2351477 := bbase (se 5 (by rfl) ⟨110225, by rfl⟩ : syracuseStep 2351477 = 220451) (by norm_num)
theorem B3178885 : Blo 1566981 3178885 := bbase (se 4 (by rfl) ⟨298020, by rfl⟩ : syracuseStep 3178885 = 596041) (by norm_num)
theorem B2351501 : Blo 1566981 2351501 := bbase (se 3 (by rfl) ⟨440906, by rfl⟩ : syracuseStep 2351501 = 881813) (by norm_num)
theorem B1909153 : Blo 1566981 1909153 := bbase (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) (by norm_num)
theorem B2351525 : Blo 1566981 2351525 := bbase (se 4 (by rfl) ⟨220455, by rfl⟩ : syracuseStep 2351525 = 440911) (by norm_num)
theorem B2646445 : Blo 1566981 2646445 := bbase (se 3 (by rfl) ⟨496208, by rfl⟩ : syracuseStep 2646445 = 992417) (by norm_num)
theorem B7938485 : Blo 1566981 7938485 := bbase (se 5 (by rfl) ⟨372116, by rfl⟩ : syracuseStep 7938485 = 744233) (by norm_num)
theorem B2826677 : Blo 1566981 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B2351549 : Blo 1566981 2351549 := bbase (se 3 (by rfl) ⟨440915, by rfl⟩ : syracuseStep 2351549 = 881831) (by norm_num)
theorem B5292485 : Blo 1566981 5292485 := bbase (se 4 (by rfl) ⟨496170, by rfl⟩ : syracuseStep 5292485 = 992341) (by norm_num)
theorem B5956037 : Blo 1566981 5956037 := bbase (se 4 (by rfl) ⟨558378, by rfl⟩ : syracuseStep 5956037 = 1116757) (by norm_num)
theorem B2351573 : Blo 1566981 2351573 := bbase (se 7 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 2351573 = 55115) (by norm_num)
theorem B2351597 : Blo 1566981 2351597 := bbase (se 3 (by rfl) ⟨440924, by rfl⟩ : syracuseStep 2351597 = 881849) (by norm_num)
theorem B2351621 : Blo 1566981 2351621 := bbase (se 4 (by rfl) ⟨220464, by rfl⟩ : syracuseStep 2351621 = 440929) (by norm_num)
theorem B2646533 : Blo 1566981 2646533 := bbase (se 4 (by rfl) ⟨248112, by rfl⟩ : syracuseStep 2646533 = 496225) (by norm_num)
theorem B2351645 : Blo 1566981 2351645 := bbase (se 3 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 2351645 = 881867) (by norm_num)
theorem B2351669 : Blo 1566981 2351669 := bbase (se 5 (by rfl) ⟨110234, by rfl⟩ : syracuseStep 2351669 = 220469) (by norm_num)
theorem B2351693 : Blo 1566981 2351693 := bbase (se 3 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 2351693 = 881885) (by norm_num)
theorem B2351717 : Blo 1566981 2351717 := bbase (se 4 (by rfl) ⟨220473, by rfl⟩ : syracuseStep 2351717 = 440947) (by norm_num)
theorem B2351741 : Blo 1566981 2351741 := bbase (se 3 (by rfl) ⟨440951, by rfl⟩ : syracuseStep 2351741 = 881903) (by norm_num)
theorem B2646661 : Blo 1566981 2646661 := bbase (se 4 (by rfl) ⟨248124, by rfl⟩ : syracuseStep 2646661 = 496249) (by norm_num)
theorem B2351765 : Blo 1566981 2351765 := bbase (se 6 (by rfl) ⟨55119, by rfl⟩ : syracuseStep 2351765 = 110239) (by norm_num)
theorem B2351789 : Blo 1566981 2351789 := bbase (se 3 (by rfl) ⟨440960, by rfl⟩ : syracuseStep 2351789 = 881921) (by norm_num)
theorem B2351813 : Blo 1566981 2351813 := bbase (se 4 (by rfl) ⟨220482, by rfl⟩ : syracuseStep 2351813 = 440965) (by norm_num)
theorem B2351837 : Blo 1566981 2351837 := bbase (se 3 (by rfl) ⟨440969, by rfl⟩ : syracuseStep 2351837 = 881939) (by norm_num)
theorem B2646749 : Blo 1566981 2646749 := bbase (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) (by norm_num)
theorem B5956325 : Blo 1566981 5956325 := bbase (se 4 (by rfl) ⟨558405, by rfl⟩ : syracuseStep 5956325 = 1116811) (by norm_num)
theorem B2351861 : Blo 1566981 2351861 := bbase (se 5 (by rfl) ⟨110243, by rfl⟩ : syracuseStep 2351861 = 220487) (by norm_num)
theorem B3769085 : Blo 1566981 3769085 := bbase (se 3 (by rfl) ⟨706703, by rfl⟩ : syracuseStep 3769085 = 1413407) (by norm_num)
theorem B2351885 : Blo 1566981 2351885 := bbase (se 3 (by rfl) ⟨440978, by rfl⟩ : syracuseStep 2351885 = 881957) (by norm_num)
theorem B2351909 : Blo 1566981 2351909 := bbase (se 4 (by rfl) ⟨220491, by rfl⟩ : syracuseStep 2351909 = 440983) (by norm_num)
theorem B3769141 : Blo 1566981 3769141 := bbase (se 5 (by rfl) ⟨176678, by rfl⟩ : syracuseStep 3769141 = 353357) (by norm_num)
theorem B2351933 : Blo 1566981 2351933 := bbase (se 3 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 2351933 = 881975) (by norm_num)
theorem B1983305 : Blo 1566981 1983305 := bbase (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) (by norm_num)
theorem B2351957 : Blo 1566981 2351957 := bbase (se 9 (by rfl) ⟨6890, by rfl⟩ : syracuseStep 2351957 = 13781) (by norm_num)
theorem B2646877 : Blo 1566981 2646877 := bbase (se 3 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 2646877 = 992579) (by norm_num)
theorem B2351981 : Blo 1566981 2351981 := bbase (se 3 (by rfl) ⟨440996, by rfl⟩ : syracuseStep 2351981 = 881993) (by norm_num)
theorem B5292917 : Blo 1566981 5292917 := bbase (se 5 (by rfl) ⟨248105, by rfl⟩ : syracuseStep 5292917 = 496211) (by norm_num)
theorem B1983361 : Blo 1566981 1983361 := bbase (se 2 (by rfl) ⟨743760, by rfl⟩ : syracuseStep 1983361 = 1487521) (by norm_num)
theorem B2352005 : Blo 1566981 2352005 := bbase (se 4 (by rfl) ⟨220500, by rfl⟩ : syracuseStep 2352005 = 441001) (by norm_num)
theorem B13403029 : Blo 1566981 13403029 := bbase (se 6 (by rfl) ⟨314133, by rfl⟩ : syracuseStep 13403029 = 628267) (by norm_num)
theorem B2352029 : Blo 1566981 2352029 := bbase (se 3 (by rfl) ⟨441005, by rfl⟩ : syracuseStep 2352029 = 882011) (by norm_num)
theorem B2352053 : Blo 1566981 2352053 := bbase (se 5 (by rfl) ⟨110252, by rfl⟩ : syracuseStep 2352053 = 220505) (by norm_num)
theorem B2646965 : Blo 1566981 2646965 := bbase (se 5 (by rfl) ⟨124076, by rfl⟩ : syracuseStep 2646965 = 248153) (by norm_num)
theorem B2352077 : Blo 1566981 2352077 := bbase (se 3 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 2352077 = 882029) (by norm_num)
theorem B15074261 : Blo 1566981 15074261 := bbase (se 7 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 15074261 = 353303) (by norm_num)
theorem B1983457 : Blo 1566981 1983457 := bbase (se 2 (by rfl) ⟨743796, by rfl⟩ : syracuseStep 1983457 = 1487593) (by norm_num)
theorem B2352101 : Blo 1566981 2352101 := bbase (se 4 (by rfl) ⟨220509, by rfl⟩ : syracuseStep 2352101 = 441019) (by norm_num)
theorem B2352125 : Blo 1566981 2352125 := bbase (se 3 (by rfl) ⟨441023, by rfl⟩ : syracuseStep 2352125 = 882047) (by norm_num)
theorem B8471573 : Blo 1566981 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B10322965 : Blo 1566981 10322965 := bbase (se 6 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 10322965 = 483889) (by norm_num)
theorem B2352149 : Blo 1566981 2352149 := bbase (se 6 (by rfl) ⟨55128, by rfl⟩ : syracuseStep 2352149 = 110257) (by norm_num)
theorem B2352173 : Blo 1566981 2352173 := bbase (se 3 (by rfl) ⟨441032, by rfl⟩ : syracuseStep 2352173 = 882065) (by norm_num)
theorem B2647093 : Blo 1566981 2647093 := bbase (se 5 (by rfl) ⟨124082, by rfl⟩ : syracuseStep 2647093 = 248165) (by norm_num)
theorem B2352197 : Blo 1566981 2352197 := bbase (se 4 (by rfl) ⟨220518, by rfl⟩ : syracuseStep 2352197 = 441037) (by norm_num)
theorem B5022805 : Blo 1566981 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B2352221 : Blo 1566981 2352221 := bbase (se 3 (by rfl) ⟨441041, by rfl⟩ : syracuseStep 2352221 = 882083) (by norm_num)
theorem B13386869 : Blo 1566981 13386869 := bbase (se 5 (by rfl) ⟨627509, by rfl⟩ : syracuseStep 13386869 = 1255019) (by norm_num)
theorem B2352245 : Blo 1566981 2352245 := bbase (se 5 (by rfl) ⟨110261, by rfl⟩ : syracuseStep 2352245 = 220523) (by norm_num)
theorem B1696897 : Blo 1566981 1696897 := bbase (se 2 (by rfl) ⟨636336, by rfl⟩ : syracuseStep 1696897 = 1272673) (by norm_num)
theorem B1983629 : Blo 1566981 1983629 := bbase (se 3 (by rfl) ⟨371930, by rfl⟩ : syracuseStep 1983629 = 743861) (by norm_num)
theorem B2352269 : Blo 1566981 2352269 := bbase (se 3 (by rfl) ⟨441050, by rfl⟩ : syracuseStep 2352269 = 882101) (by norm_num)
theorem B2647181 : Blo 1566981 2647181 := bbase (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) (by norm_num)
theorem B2352293 : Blo 1566981 2352293 := bbase (se 4 (by rfl) ⟨220527, by rfl⟩ : syracuseStep 2352293 = 441055) (by norm_num)
theorem B3769517 : Blo 1566981 3769517 := bbase (se 3 (by rfl) ⟨706784, by rfl⟩ : syracuseStep 3769517 = 1413569) (by norm_num)
theorem B2352317 : Blo 1566981 2352317 := bbase (se 3 (by rfl) ⟨441059, by rfl⟩ : syracuseStep 2352317 = 882119) (by norm_num)
theorem B1983685 : Blo 1566981 1983685 := bbase (se 4 (by rfl) ⟨185970, by rfl⟩ : syracuseStep 1983685 = 371941) (by norm_num)
theorem B2352341 : Blo 1566981 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B2352365 : Blo 1566981 2352365 := bbase (se 3 (by rfl) ⟨441068, by rfl⟩ : syracuseStep 2352365 = 882137) (by norm_num)
theorem B2974981 : Blo 1566981 2974981 := bbase (se 4 (by rfl) ⟨278904, by rfl⟩ : syracuseStep 2974981 = 557809) (by norm_num)
theorem B2352389 : Blo 1566981 2352389 := bbase (se 4 (by rfl) ⟨220536, by rfl⟩ : syracuseStep 2352389 = 441073) (by norm_num)
theorem B2647309 : Blo 1566981 2647309 := bbase (se 3 (by rfl) ⟨496370, by rfl⟩ : syracuseStep 2647309 = 992741) (by norm_num)
theorem B2352413 : Blo 1566981 2352413 := bbase (se 3 (by rfl) ⟨441077, by rfl⟩ : syracuseStep 2352413 = 882155) (by norm_num)
theorem B1983781 : Blo 1566981 1983781 := bbase (se 4 (by rfl) ⟨185979, by rfl⟩ : syracuseStep 1983781 = 371959) (by norm_num)
theorem B5293349 : Blo 1566981 5293349 := bbase (se 4 (by rfl) ⟨496251, by rfl⟩ : syracuseStep 5293349 = 992503) (by norm_num)
theorem B2352437 : Blo 1566981 2352437 := bbase (se 5 (by rfl) ⟨110270, by rfl⟩ : syracuseStep 2352437 = 220541) (by norm_num)
theorem B2352461 : Blo 1566981 2352461 := bbase (se 3 (by rfl) ⟨441086, by rfl⟩ : syracuseStep 2352461 = 882173) (by norm_num)
theorem B5023061 : Blo 1566981 5023061 := bbase (se 12 (by rfl) ⟨1839, by rfl⟩ : syracuseStep 5023061 = 3679) (by norm_num)
theorem B2352485 : Blo 1566981 2352485 := bbase (se 4 (by rfl) ⟨220545, by rfl⟩ : syracuseStep 2352485 = 441091) (by norm_num)
theorem B2647397 : Blo 1566981 2647397 := bbase (se 4 (by rfl) ⟨248193, by rfl⟩ : syracuseStep 2647397 = 496387) (by norm_num)
theorem B2352509 : Blo 1566981 2352509 := bbase (se 3 (by rfl) ⟨441095, by rfl⟩ : syracuseStep 2352509 = 882191) (by norm_num)
theorem B2975125 : Blo 1566981 2975125 := bbase (se 6 (by rfl) ⟨69729, by rfl⟩ : syracuseStep 2975125 = 139459) (by norm_num)
theorem B11298197 : Blo 1566981 11298197 := bbase (se 6 (by rfl) ⟨264801, by rfl⟩ : syracuseStep 11298197 = 529603) (by norm_num)
theorem B2352533 : Blo 1566981 2352533 := bbase (se 6 (by rfl) ⟨55137, by rfl⟩ : syracuseStep 2352533 = 110275) (by norm_num)
theorem B2385301 : Blo 1566981 2385301 := bbase (se 6 (by rfl) ⟨55905, by rfl⟩ : syracuseStep 2385301 = 111811) (by norm_num)
theorem B3769757 : Blo 1566981 3769757 := bbase (se 3 (by rfl) ⟨706829, by rfl⟩ : syracuseStep 3769757 = 1413659) (by norm_num)
theorem B2352557 : Blo 1566981 2352557 := bbase (se 3 (by rfl) ⟨441104, by rfl⟩ : syracuseStep 2352557 = 882209) (by norm_num)
theorem B4466117 : Blo 1566981 4466117 := bbase (se 4 (by rfl) ⟨418698, by rfl⟩ : syracuseStep 4466117 = 837397) (by norm_num)
theorem B2352581 : Blo 1566981 2352581 := bbase (se 4 (by rfl) ⟨220554, by rfl⟩ : syracuseStep 2352581 = 441109) (by norm_num)
theorem B1983953 : Blo 1566981 1983953 := bbase (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) (by norm_num)
theorem B2352605 : Blo 1566981 2352605 := bbase (se 3 (by rfl) ⟨441113, by rfl⟩ : syracuseStep 2352605 = 882227) (by norm_num)
theorem B2647525 : Blo 1566981 2647525 := bbase (se 4 (by rfl) ⟨248205, by rfl⟩ : syracuseStep 2647525 = 496411) (by norm_num)
theorem B2352629 : Blo 1566981 2352629 := bbase (se 5 (by rfl) ⟨110279, by rfl⟩ : syracuseStep 2352629 = 220559) (by norm_num)
theorem B1984009 : Blo 1566981 1984009 := bbase (se 2 (by rfl) ⟨744003, by rfl⟩ : syracuseStep 1984009 = 1488007) (by norm_num)
theorem B2352653 : Blo 1566981 2352653 := bbase (se 3 (by rfl) ⟨441122, by rfl⟩ : syracuseStep 2352653 = 882245) (by norm_num)
theorem B3180053 : Blo 1566981 3180053 := bbase (se 6 (by rfl) ⟨74532, by rfl⟩ : syracuseStep 3180053 = 149065) (by norm_num)
theorem B2352677 : Blo 1566981 2352677 := bbase (se 4 (by rfl) ⟨220563, by rfl⟩ : syracuseStep 2352677 = 441127) (by norm_num)
theorem B1762861 : Blo 1566981 1762861 := bbase (se 3 (by rfl) ⟨330536, by rfl⟩ : syracuseStep 1762861 = 661073) (by norm_num)
theorem B3966509 : Blo 1566981 3966509 := bbase (se 3 (by rfl) ⟨743720, by rfl⟩ : syracuseStep 3966509 = 1487441) (by norm_num)
theorem B2975285 : Blo 1566981 2975285 := bbase (se 5 (by rfl) ⟨139466, by rfl⟩ : syracuseStep 2975285 = 278933) (by norm_num)
theorem B2352701 : Blo 1566981 2352701 := bbase (se 3 (by rfl) ⟨441131, by rfl⟩ : syracuseStep 2352701 = 882263) (by norm_num)
theorem B2647613 : Blo 1566981 2647613 := bbase (se 3 (by rfl) ⟨496427, by rfl⟩ : syracuseStep 2647613 = 992855) (by norm_num)
theorem B4236869 : Blo 1566981 4236869 := bbase (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) (by norm_num)
theorem B1762897 : Blo 1566981 1762897 := bbase (se 2 (by rfl) ⟨661086, by rfl⟩ : syracuseStep 1762897 = 1322173) (by norm_num)
theorem B14296661 : Blo 1566981 14296661 := bbase (se 8 (by rfl) ⟨83769, by rfl⟩ : syracuseStep 14296661 = 167539) (by norm_num)
theorem B4023893 : Blo 1566981 4023893 := bbase (se 8 (by rfl) ⟨23577, by rfl⟩ : syracuseStep 4023893 = 47155) (by norm_num)
theorem B2352725 : Blo 1566981 2352725 := bbase (se 8 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 2352725 = 27571) (by norm_num)
theorem B5654117 : Blo 1566981 5654117 := bbase (se 4 (by rfl) ⟨530073, by rfl⟩ : syracuseStep 5654117 = 1060147) (by norm_num)
theorem B1984105 : Blo 1566981 1984105 := bbase (se 2 (by rfl) ⟨744039, by rfl⟩ : syracuseStep 1984105 = 1488079) (by norm_num)
theorem B2352749 : Blo 1566981 2352749 := bbase (se 3 (by rfl) ⟨441140, by rfl⟩ : syracuseStep 2352749 = 882281) (by norm_num)
theorem B1762933 : Blo 1566981 1762933 := bbase (se 5 (by rfl) ⟨82637, by rfl⟩ : syracuseStep 1762933 = 165275) (by norm_num)
theorem B3180149 : Blo 1566981 3180149 := bbase (se 5 (by rfl) ⟨149069, by rfl⟩ : syracuseStep 3180149 = 298139) (by norm_num)
theorem B1787521 : Blo 1566981 1787521 := bbase (se 2 (by rfl) ⟨670320, by rfl⟩ : syracuseStep 1787521 = 1340641) (by norm_num)
theorem B2352773 : Blo 1566981 2352773 := bbase (se 4 (by rfl) ⟨220572, by rfl⟩ : syracuseStep 2352773 = 441145) (by norm_num)
theorem B1762969 : Blo 1566981 1762969 := bbase (se 2 (by rfl) ⟨661113, by rfl⟩ : syracuseStep 1762969 = 1322227) (by norm_num)
theorem B2352797 : Blo 1566981 2352797 := bbase (se 3 (by rfl) ⟨441149, by rfl⟩ : syracuseStep 2352797 = 882299) (by norm_num)
theorem B1787557 : Blo 1566981 1787557 := bbase (se 4 (by rfl) ⟨167583, by rfl⟩ : syracuseStep 1787557 = 335167) (by norm_num)
theorem B2352821 : Blo 1566981 2352821 := bbase (se 5 (by rfl) ⟨110288, by rfl⟩ : syracuseStep 2352821 = 220577) (by norm_num)
theorem B1763005 : Blo 1566981 1763005 := bbase (se 3 (by rfl) ⟨330563, by rfl⟩ : syracuseStep 1763005 = 661127) (by norm_num)
theorem B2975429 : Blo 1566981 2975429 := bbase (se 4 (by rfl) ⟨278946, by rfl⟩ : syracuseStep 2975429 = 557893) (by norm_num)
theorem B4236997 : Blo 1566981 4236997 := bbase (se 4 (by rfl) ⟨397218, by rfl⟩ : syracuseStep 4236997 = 794437) (by norm_num)
theorem B7939781 : Blo 1566981 7939781 := bbase (se 4 (by rfl) ⟨744354, by rfl⟩ : syracuseStep 7939781 = 1488709) (by norm_num)
theorem B2352845 : Blo 1566981 2352845 := bbase (se 3 (by rfl) ⟨441158, by rfl⟩ : syracuseStep 2352845 = 882317) (by norm_num)
theorem B6694613 : Blo 1566981 6694613 := bbase (se 7 (by rfl) ⟨78452, by rfl⟩ : syracuseStep 6694613 = 156905) (by norm_num)
theorem B5293781 : Blo 1566981 5293781 := bbase (se 7 (by rfl) ⟨62036, by rfl⟩ : syracuseStep 5293781 = 124073) (by norm_num)
theorem B1763041 : Blo 1566981 1763041 := bbase (se 2 (by rfl) ⟨661140, by rfl⟩ : syracuseStep 1763041 = 1322281) (by norm_num)
theorem B2352869 : Blo 1566981 2352869 := bbase (se 4 (by rfl) ⟨220581, by rfl⟩ : syracuseStep 2352869 = 441163) (by norm_num)
theorem B2352893 : Blo 1566981 2352893 := bbase (se 3 (by rfl) ⟨441167, by rfl⟩ : syracuseStep 2352893 = 882335) (by norm_num)
theorem B1763077 : Blo 1566981 1763077 := bbase (se 4 (by rfl) ⟨165288, by rfl⟩ : syracuseStep 1763077 = 330577) (by norm_num)
theorem B1697545 : Blo 1566981 1697545 := bbase (se 2 (by rfl) ⟨636579, by rfl⟩ : syracuseStep 1697545 = 1273159) (by norm_num)
theorem B1984277 : Blo 1566981 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B2352917 : Blo 1566981 2352917 := bbase (se 6 (by rfl) ⟨55146, by rfl⟩ : syracuseStep 2352917 = 110293) (by norm_num)
theorem B1763113 : Blo 1566981 1763113 := bbase (se 2 (by rfl) ⟨661167, by rfl⟩ : syracuseStep 1763113 = 1322335) (by norm_num)
theorem B2352941 : Blo 1566981 2352941 := bbase (se 3 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 2352941 = 882353) (by norm_num)
theorem B2352965 : Blo 1566981 2352965 := bbase (se 4 (by rfl) ⟨220590, by rfl⟩ : syracuseStep 2352965 = 441181) (by norm_num)
theorem B1763149 : Blo 1566981 1763149 := bbase (se 3 (by rfl) ⟨330590, by rfl⟩ : syracuseStep 1763149 = 661181) (by norm_num)
theorem B1984333 : Blo 1566981 1984333 := bbase (se 3 (by rfl) ⟨372062, by rfl⟩ : syracuseStep 1984333 = 744125) (by norm_num)
theorem B2352989 : Blo 1566981 2352989 := bbase (se 3 (by rfl) ⟨441185, by rfl⟩ : syracuseStep 2352989 = 882371) (by norm_num)
theorem B1632101 : Blo 1566981 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B1763185 : Blo 1566981 1763185 := bbase (se 2 (by rfl) ⟨661194, by rfl⟩ : syracuseStep 1763185 = 1322389) (by norm_num)
theorem B2353013 : Blo 1566981 2353013 := bbase (se 5 (by rfl) ⟨110297, by rfl⟩ : syracuseStep 2353013 = 220595) (by norm_num)
theorem B3966853 : Blo 1566981 3966853 := bbase (se 4 (by rfl) ⟨371892, by rfl⟩ : syracuseStep 3966853 = 743785) (by norm_num)
theorem B2353037 : Blo 1566981 2353037 := bbase (se 3 (by rfl) ⟨441194, by rfl⟩ : syracuseStep 2353037 = 882389) (by norm_num)
theorem B1763221 : Blo 1566981 1763221 := bbase (se 6 (by rfl) ⟨41325, by rfl⟩ : syracuseStep 1763221 = 82651) (by norm_num)
theorem B2353061 : Blo 1566981 2353061 := bbase (se 4 (by rfl) ⟨220599, by rfl⟩ : syracuseStep 2353061 = 441199) (by norm_num)
theorem B1984429 : Blo 1566981 1984429 := bbase (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) (by norm_num)
theorem B1763257 : Blo 1566981 1763257 := bbase (se 2 (by rfl) ⟨661221, by rfl⟩ : syracuseStep 1763257 = 1322443) (by norm_num)
theorem B2353085 : Blo 1566981 2353085 := bbase (se 3 (by rfl) ⟨441203, by rfl⟩ : syracuseStep 2353085 = 882407) (by norm_num)
theorem B2353109 : Blo 1566981 2353109 := bbase (se 7 (by rfl) ⟨27575, by rfl⟩ : syracuseStep 2353109 = 55151) (by norm_num)
theorem B1697753 : Blo 1566981 1697753 := bbase (se 2 (by rfl) ⟨636657, by rfl⟩ : syracuseStep 1697753 = 1273315) (by norm_num)
theorem B1763293 : Blo 1566981 1763293 := bbase (se 3 (by rfl) ⟨330617, by rfl⟩ : syracuseStep 1763293 = 661235) (by norm_num)
theorem B2975717 : Blo 1566981 2975717 := bbase (se 4 (by rfl) ⟨278973, by rfl⟩ : syracuseStep 2975717 = 557947) (by norm_num)
theorem B2353133 : Blo 1566981 2353133 := bbase (se 3 (by rfl) ⟨441212, by rfl⟩ : syracuseStep 2353133 = 882425) (by norm_num)
theorem B3966965 : Blo 1566981 3966965 := bbase (se 5 (by rfl) ⟨185951, by rfl⟩ : syracuseStep 3966965 = 371903) (by norm_num)
theorem B1763329 : Blo 1566981 1763329 := bbase (se 2 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 1763329 = 1322497) (by norm_num)
theorem B2353157 : Blo 1566981 2353157 := bbase (se 4 (by rfl) ⟨220608, by rfl⟩ : syracuseStep 2353157 = 441217) (by norm_num)
theorem B5654549 : Blo 1566981 5654549 := bbase (se 6 (by rfl) ⟨132528, by rfl⟩ : syracuseStep 5654549 = 265057) (by norm_num)
theorem B2353181 : Blo 1566981 2353181 := bbase (se 3 (by rfl) ⟨441221, by rfl⟩ : syracuseStep 2353181 = 882443) (by norm_num)
theorem B1763365 : Blo 1566981 1763365 := bbase (se 4 (by rfl) ⟨165315, by rfl⟩ : syracuseStep 1763365 = 330631) (by norm_num)
theorem B2066485 : Blo 1566981 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B2353205 : Blo 1566981 2353205 := bbase (se 5 (by rfl) ⟨110306, by rfl⟩ : syracuseStep 2353205 = 220613) (by norm_num)
theorem B1763401 : Blo 1566981 1763401 := bbase (se 2 (by rfl) ⟨661275, by rfl⟩ : syracuseStep 1763401 = 1322551) (by norm_num)
theorem B2353229 : Blo 1566981 2353229 := bbase (se 3 (by rfl) ⟨441230, by rfl⟩ : syracuseStep 2353229 = 882461) (by norm_num)
theorem B4294741 : Blo 1566981 4294741 := bbase (se 8 (by rfl) ⟨25164, by rfl⟩ : syracuseStep 4294741 = 50329) (by norm_num)
theorem B8710229 : Blo 1566981 8710229 := bbase (se 8 (by rfl) ⟨51036, by rfl⟩ : syracuseStep 8710229 = 102073) (by norm_num)
theorem B4024405 : Blo 1566981 4024405 := bbase (se 8 (by rfl) ⟨23580, by rfl⟩ : syracuseStep 4024405 = 47161) (by norm_num)
theorem B1984601 : Blo 1566981 1984601 := bbase (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) (by norm_num)
theorem B4466789 : Blo 1566981 4466789 := bbase (se 4 (by rfl) ⟨418761, by rfl⟩ : syracuseStep 4466789 = 837523) (by norm_num)
theorem B2353253 : Blo 1566981 2353253 := bbase (se 4 (by rfl) ⟨220617, by rfl⟩ : syracuseStep 2353253 = 441235) (by norm_num)
theorem B1763437 : Blo 1566981 1763437 := bbase (se 3 (by rfl) ⟨330644, by rfl⟩ : syracuseStep 1763437 = 661289) (by norm_num)
theorem B2975869 : Blo 1566981 2975869 := bbase (se 3 (by rfl) ⟨557975, by rfl⟩ : syracuseStep 2975869 = 1115951) (by norm_num)
theorem B2353277 : Blo 1566981 2353277 := bbase (se 3 (by rfl) ⟨441239, by rfl⟩ : syracuseStep 2353277 = 882479) (by norm_num)
theorem B5294213 : Blo 1566981 5294213 := bbase (se 4 (by rfl) ⟨496332, by rfl⟩ : syracuseStep 5294213 = 992665) (by norm_num)
theorem B1788041 : Blo 1566981 1788041 := bbase (se 2 (by rfl) ⟨670515, by rfl⟩ : syracuseStep 1788041 = 1341031) (by norm_num)
theorem B1763473 : Blo 1566981 1763473 := bbase (se 2 (by rfl) ⟨661302, by rfl⟩ : syracuseStep 1763473 = 1322605) (by norm_num)
theorem B1788049 : Blo 1566981 1788049 := bbase (se 2 (by rfl) ⟨670518, by rfl⟩ : syracuseStep 1788049 = 1341037) (by norm_num)
theorem B1984657 : Blo 1566981 1984657 := bbase (se 2 (by rfl) ⟨744246, by rfl⟩ : syracuseStep 1984657 = 1488493) (by norm_num)
theorem B2353301 : Blo 1566981 2353301 := bbase (se 6 (by rfl) ⟨55155, by rfl⟩ : syracuseStep 2353301 = 110311) (by norm_num)
theorem B2353325 : Blo 1566981 2353325 := bbase (se 3 (by rfl) ⟨441248, by rfl⟩ : syracuseStep 2353325 = 882497) (by norm_num)
theorem B3967157 : Blo 1566981 3967157 := bbase (se 5 (by rfl) ⟨185960, by rfl⟩ : syracuseStep 3967157 = 371921) (by norm_num)
theorem B1763509 : Blo 1566981 1763509 := bbase (se 5 (by rfl) ⟨82664, by rfl⟩ : syracuseStep 1763509 = 165329) (by norm_num)
theorem B2353349 : Blo 1566981 2353349 := bbase (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) (by norm_num)
theorem B3573965 : Blo 1566981 3573965 := bbase (se 3 (by rfl) ⟨670118, by rfl⟩ : syracuseStep 3573965 = 1340237) (by norm_num)
theorem B1763545 : Blo 1566981 1763545 := bbase (se 2 (by rfl) ⟨661329, by rfl⟩ : syracuseStep 1763545 = 1322659) (by norm_num)
theorem B2353373 : Blo 1566981 2353373 := bbase (se 3 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 2353373 = 882515) (by norm_num)
theorem B1984753 : Blo 1566981 1984753 := bbase (se 2 (by rfl) ⟨744282, by rfl⟩ : syracuseStep 1984753 = 1488565) (by norm_num)
theorem B7637237 : Blo 1566981 7637237 := bbase (se 5 (by rfl) ⟨357995, by rfl⟩ : syracuseStep 7637237 = 715991) (by norm_num)
theorem B2353397 : Blo 1566981 2353397 := bbase (se 5 (by rfl) ⟨110315, by rfl⟩ : syracuseStep 2353397 = 220631) (by norm_num)
theorem B1673465 : Blo 1566981 1673465 := bbase (se 2 (by rfl) ⟨627549, by rfl⟩ : syracuseStep 1673465 = 1255099) (by norm_num)
theorem B1763581 : Blo 1566981 1763581 := bbase (se 3 (by rfl) ⟨330671, by rfl⟩ : syracuseStep 1763581 = 661343) (by norm_num)
theorem B2353421 : Blo 1566981 2353421 := bbase (se 3 (by rfl) ⟨441266, by rfl⟩ : syracuseStep 2353421 = 882533) (by norm_num)
theorem B1763617 : Blo 1566981 1763617 := bbase (se 2 (by rfl) ⟨661356, by rfl⟩ : syracuseStep 1763617 = 1322713) (by norm_num)
theorem B5949733 : Blo 1566981 5949733 := bbase (se 4 (by rfl) ⟨557787, by rfl⟩ : syracuseStep 5949733 = 1115575) (by norm_num)
theorem B2353445 : Blo 1566981 2353445 := bbase (se 4 (by rfl) ⟨220635, by rfl⟩ : syracuseStep 2353445 = 441271) (by norm_num)
theorem B2353469 : Blo 1566981 2353469 := bbase (se 3 (by rfl) ⟨441275, by rfl⟩ : syracuseStep 2353469 = 882551) (by norm_num)
theorem B1763653 : Blo 1566981 1763653 := bbase (se 4 (by rfl) ⟨165342, by rfl⟩ : syracuseStep 1763653 = 330685) (by norm_num)
theorem B1763689 : Blo 1566981 1763689 := bbase (se 2 (by rfl) ⟨661383, by rfl⟩ : syracuseStep 1763689 = 1322767) (by norm_num)
theorem B1763725 : Blo 1566981 1763725 := bbase (se 3 (by rfl) ⟨330698, by rfl⟩ : syracuseStep 1763725 = 661397) (by norm_num)
theorem B1984925 : Blo 1566981 1984925 := bbase (se 3 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 1984925 = 744347) (by norm_num)
theorem B2976173 : Blo 1566981 2976173 := bbase (se 3 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 2976173 = 1116065) (by norm_num)
theorem B1763761 : Blo 1566981 1763761 := bbase (se 2 (by rfl) ⟨661410, by rfl⟩ : syracuseStep 1763761 = 1322821) (by norm_num)
theorem B1763797 : Blo 1566981 1763797 := bbase (se 7 (by rfl) ⟨20669, by rfl⟩ : syracuseStep 1763797 = 41339) (by norm_num)
theorem B1984981 : Blo 1566981 1984981 := bbase (se 7 (by rfl) ⟨23261, by rfl⟩ : syracuseStep 1984981 = 46523) (by norm_num)
theorem B1673713 : Blo 1566981 1673713 := bbase (se 2 (by rfl) ⟨627642, by rfl⟩ : syracuseStep 1673713 = 1255285) (by norm_num)
theorem B1763833 : Blo 1566981 1763833 := bbase (se 2 (by rfl) ⟨661437, by rfl⟩ : syracuseStep 1763833 = 1322875) (by norm_num)
theorem B3574277 : Blo 1566981 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B3967501 : Blo 1566981 3967501 := bbase (se 3 (by rfl) ⟨743906, by rfl⟩ : syracuseStep 3967501 = 1487813) (by norm_num)
theorem B4467221 : Blo 1566981 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B1763869 : Blo 1566981 1763869 := bbase (se 3 (by rfl) ⟨330725, by rfl⟩ : syracuseStep 1763869 = 661451) (by norm_num)
theorem B1985077 : Blo 1566981 1985077 := bbase (se 5 (by rfl) ⟨93050, by rfl⟩ : syracuseStep 1985077 = 186101) (by norm_num)
theorem B5294645 : Blo 1566981 5294645 := bbase (se 5 (by rfl) ⟨248186, by rfl⟩ : syracuseStep 5294645 = 496373) (by norm_num)
theorem B1763905 : Blo 1566981 1763905 := bbase (se 2 (by rfl) ⟨661464, by rfl⟩ : syracuseStep 1763905 = 1322929) (by norm_num)
theorem B5950037 : Blo 1566981 5950037 := bbase (se 8 (by rfl) ⟨34863, by rfl⟩ : syracuseStep 5950037 = 69727) (by norm_num)
theorem B1763941 : Blo 1566981 1763941 := bbase (se 4 (by rfl) ⟨165369, by rfl⟩ : syracuseStep 1763941 = 330739) (by norm_num)
theorem B3967613 : Blo 1566981 3967613 := bbase (se 3 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 3967613 = 1487855) (by norm_num)
theorem B1763977 : Blo 1566981 1763977 := bbase (se 2 (by rfl) ⟨661491, by rfl⟩ : syracuseStep 1763977 = 1322983) (by norm_num)
theorem B1764013 : Blo 1566981 1764013 := bbase (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) (by norm_num)
theorem B1764049 : Blo 1566981 1764049 := bbase (se 2 (by rfl) ⟨661518, by rfl⟩ : syracuseStep 1764049 = 1323037) (by norm_num)
theorem B1985249 : Blo 1566981 1985249 := bbase (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) (by norm_num)
theorem B1764085 : Blo 1566981 1764085 := bbase (se 5 (by rfl) ⟨82691, by rfl⟩ : syracuseStep 1764085 = 165383) (by norm_num)
theorem B1788689 : Blo 1566981 1788689 := bbase (se 2 (by rfl) ⟨670758, by rfl⟩ : syracuseStep 1788689 = 1341517) (by norm_num)
theorem B1764121 : Blo 1566981 1764121 := bbase (se 2 (by rfl) ⟨661545, by rfl⟩ : syracuseStep 1764121 = 1323091) (by norm_num)
theorem B1985305 : Blo 1566981 1985305 := bbase (se 2 (by rfl) ⟨744489, by rfl⟩ : syracuseStep 1985305 = 1488979) (by norm_num)
theorem B3967805 : Blo 1566981 3967805 := bbase (se 3 (by rfl) ⟨743963, by rfl⟩ : syracuseStep 3967805 = 1487927) (by norm_num)
theorem B1764157 : Blo 1566981 1764157 := bbase (se 3 (by rfl) ⟨330779, by rfl⟩ : syracuseStep 1764157 = 661559) (by norm_num)
theorem B4524869 : Blo 1566981 4524869 := bbase (se 4 (by rfl) ⟨424206, by rfl⟩ : syracuseStep 4524869 = 848413) (by norm_num)
theorem B1764193 : Blo 1566981 1764193 := bbase (se 2 (by rfl) ⟨661572, by rfl⟩ : syracuseStep 1764193 = 1323145) (by norm_num)
theorem B1985401 : Blo 1566981 1985401 := bbase (se 2 (by rfl) ⟨744525, by rfl⟩ : syracuseStep 1985401 = 1489051) (by norm_num)
theorem B2231173 : Blo 1566981 2231173 := bbase (se 4 (by rfl) ⟨209172, by rfl⟩ : syracuseStep 2231173 = 418345) (by norm_num)
theorem B1764229 : Blo 1566981 1764229 := bbase (se 4 (by rfl) ⟨165396, by rfl⟩ : syracuseStep 1764229 = 330793) (by norm_num)
theorem B1674145 : Blo 1566981 1674145 := bbase (se 2 (by rfl) ⟨627804, by rfl⟩ : syracuseStep 1674145 = 1255609) (by norm_num)
theorem B1764265 : Blo 1566981 1764265 := bbase (se 2 (by rfl) ⟨661599, by rfl⟩ : syracuseStep 1764265 = 1323199) (by norm_num)
theorem B1764301 : Blo 1566981 1764301 := bbase (se 3 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 1764301 = 661613) (by norm_num)
theorem B7941077 : Blo 1566981 7941077 := bbase (se 7 (by rfl) ⟨93059, by rfl⟩ : syracuseStep 7941077 = 186119) (by norm_num)
theorem B5295077 : Blo 1566981 5295077 := bbase (se 4 (by rfl) ⟨496413, by rfl⟩ : syracuseStep 5295077 = 992827) (by norm_num)
theorem B1674217 : Blo 1566981 1674217 := bbase (se 2 (by rfl) ⟨627831, by rfl⟩ : syracuseStep 1674217 = 1255663) (by norm_num)
theorem B1764337 : Blo 1566981 1764337 := bbase (se 2 (by rfl) ⟨661626, by rfl⟩ : syracuseStep 1764337 = 1323253) (by norm_num)
theorem B1764373 : Blo 1566981 1764373 := bbase (se 6 (by rfl) ⟨41352, by rfl⟩ : syracuseStep 1764373 = 82705) (by norm_num)
theorem B1985573 : Blo 1566981 1985573 := bbase (se 4 (by rfl) ⟨186147, by rfl⟩ : syracuseStep 1985573 = 372295) (by norm_num)
theorem B1764409 : Blo 1566981 1764409 := bbase (se 2 (by rfl) ⟨661653, by rfl⟩ : syracuseStep 1764409 = 1323307) (by norm_num)
theorem B1764445 : Blo 1566981 1764445 := bbase (se 3 (by rfl) ⟨330833, by rfl⟩ : syracuseStep 1764445 = 661667) (by norm_num)
theorem B1985629 : Blo 1566981 1985629 := bbase (se 3 (by rfl) ⟨372305, by rfl⟩ : syracuseStep 1985629 = 744611) (by norm_num)
theorem B3525749 : Blo 1566981 3525749 := bbase (se 5 (by rfl) ⟨165269, by rfl⟩ : syracuseStep 3525749 = 330539) (by norm_num)
theorem B1764481 : Blo 1566981 1764481 := bbase (se 2 (by rfl) ⟨661680, by rfl⟩ : syracuseStep 1764481 = 1323361) (by norm_num)
theorem B3968149 : Blo 1566981 3968149 := bbase (se 6 (by rfl) ⟨93003, by rfl⟩ : syracuseStep 3968149 = 186007) (by norm_num)
theorem B2976925 : Blo 1566981 2976925 := bbase (se 3 (by rfl) ⟨558173, by rfl⟩ : syracuseStep 2976925 = 1116347) (by norm_num)
theorem B1764517 : Blo 1566981 1764517 := bbase (se 4 (by rfl) ⟨165423, by rfl⟩ : syracuseStep 1764517 = 330847) (by norm_num)
theorem B3525821 : Blo 1566981 3525821 := bbase (se 3 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 3525821 = 1322183) (by norm_num)
theorem B1985725 : Blo 1566981 1985725 := bbase (se 3 (by rfl) ⟨372323, by rfl⟩ : syracuseStep 1985725 = 744647) (by norm_num)
theorem B1764553 : Blo 1566981 1764553 := bbase (se 2 (by rfl) ⟨661707, by rfl⟩ : syracuseStep 1764553 = 1323415) (by norm_num)
theorem B1764589 : Blo 1566981 1764589 := bbase (se 3 (by rfl) ⟨330860, by rfl⟩ : syracuseStep 1764589 = 661721) (by norm_num)
theorem B3525893 : Blo 1566981 3525893 := bbase (se 4 (by rfl) ⟨330552, by rfl⟩ : syracuseStep 3525893 = 661105) (by norm_num)
theorem B3968261 : Blo 1566981 3968261 := bbase (se 4 (by rfl) ⟨372024, by rfl⟩ : syracuseStep 3968261 = 744049) (by norm_num)
theorem B1764625 : Blo 1566981 1764625 := bbase (se 2 (by rfl) ⟨661734, by rfl⟩ : syracuseStep 1764625 = 1323469) (by norm_num)
theorem B2977069 : Blo 1566981 2977069 := bbase (se 3 (by rfl) ⟨558200, by rfl⟩ : syracuseStep 2977069 = 1116401) (by norm_num)
theorem B1764661 : Blo 1566981 1764661 := bbase (se 5 (by rfl) ⟨82718, by rfl⟩ : syracuseStep 1764661 = 165437) (by norm_num)
theorem B3525965 : Blo 1566981 3525965 := bbase (se 3 (by rfl) ⟨661118, by rfl⟩ : syracuseStep 3525965 = 1322237) (by norm_num)
theorem B1764697 : Blo 1566981 1764697 := bbase (se 2 (by rfl) ⟨661761, by rfl⟩ : syracuseStep 1764697 = 1323523) (by norm_num)
theorem B1674589 : Blo 1566981 1674589 := bbase (se 3 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 1674589 = 627971) (by norm_num)
theorem B7933301 : Blo 1566981 7933301 := bbase (se 5 (by rfl) ⟨371873, by rfl⟩ : syracuseStep 7933301 = 743747) (by norm_num)
theorem B1764733 : Blo 1566981 1764733 := bbase (se 3 (by rfl) ⟨330887, by rfl⟩ : syracuseStep 1764733 = 661775) (by norm_num)
theorem B3526037 : Blo 1566981 3526037 := bbase (se 6 (by rfl) ⟨82641, by rfl⟩ : syracuseStep 3526037 = 165283) (by norm_num)
theorem B1764769 : Blo 1566981 1764769 := bbase (se 2 (by rfl) ⟨661788, by rfl⟩ : syracuseStep 1764769 = 1323577) (by norm_num)
theorem B10177973 : Blo 1566981 10177973 := bbase (se 5 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 10177973 = 954185) (by norm_num)
theorem B3968453 : Blo 1566981 3968453 := bbase (se 4 (by rfl) ⟨372042, by rfl⟩ : syracuseStep 3968453 = 744085) (by norm_num)
theorem B1764805 : Blo 1566981 1764805 := bbase (se 4 (by rfl) ⟨165450, by rfl⟩ : syracuseStep 1764805 = 330901) (by norm_num)
theorem B2977229 : Blo 1566981 2977229 := bbase (se 3 (by rfl) ⟨558230, by rfl⟩ : syracuseStep 2977229 = 1116461) (by norm_num)
theorem B3526109 : Blo 1566981 3526109 := bbase (se 3 (by rfl) ⟨661145, by rfl⟩ : syracuseStep 3526109 = 1322291) (by norm_num)
theorem B1764841 : Blo 1566981 1764841 := bbase (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) (by norm_num)
theorem B1764877 : Blo 1566981 1764877 := bbase (se 3 (by rfl) ⟨330914, by rfl⟩ : syracuseStep 1764877 = 661829) (by norm_num)
theorem B2510365 : Blo 1566981 2510365 := bbase (se 3 (by rfl) ⟨470693, by rfl⟩ : syracuseStep 2510365 = 941387) (by norm_num)
theorem B3526181 : Blo 1566981 3526181 := bbase (se 4 (by rfl) ⟨330579, by rfl⟩ : syracuseStep 3526181 = 661159) (by norm_num)
theorem B1764913 : Blo 1566981 1764913 := bbase (se 2 (by rfl) ⟨661842, by rfl⟩ : syracuseStep 1764913 = 1323685) (by norm_num)
theorem B2944565 : Blo 1566981 2944565 := bbase (se 5 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 2944565 = 276053) (by norm_num)
theorem B16084565 : Blo 1566981 16084565 := bbase (se 8 (by rfl) ⟨94245, by rfl⟩ : syracuseStep 16084565 = 188491) (by norm_num)
theorem B48303701 : Blo 1566981 48303701 := bbase (se 8 (by rfl) ⟨283029, by rfl⟩ : syracuseStep 48303701 = 566059) (by norm_num)
theorem B1764949 : Blo 1566981 1764949 := bbase (se 8 (by rfl) ⟨10341, by rfl⟩ : syracuseStep 1764949 = 20683) (by norm_num)
theorem B2977373 : Blo 1566981 2977373 := bbase (se 3 (by rfl) ⟨558257, by rfl⟩ : syracuseStep 2977373 = 1116515) (by norm_num)
theorem B3526253 : Blo 1566981 3526253 := bbase (se 3 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 3526253 = 1322345) (by norm_num)
theorem B1764985 : Blo 1566981 1764985 := bbase (se 2 (by rfl) ⟨661869, by rfl⟩ : syracuseStep 1764985 = 1323739) (by norm_num)
theorem B11308693 : Blo 1566981 11308693 := bbase (se 6 (by rfl) ⟨265047, by rfl⟩ : syracuseStep 11308693 = 530095) (by norm_num)
theorem B2231965 : Blo 1566981 2231965 := bbase (se 3 (by rfl) ⟨418493, by rfl⟩ : syracuseStep 2231965 = 836987) (by norm_num)
theorem B1765021 : Blo 1566981 1765021 := bbase (se 3 (by rfl) ⟨330941, by rfl⟩ : syracuseStep 1765021 = 661883) (by norm_num)
theorem B3526325 : Blo 1566981 3526325 := bbase (se 5 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 3526325 = 330593) (by norm_num)
theorem B1765057 : Blo 1566981 1765057 := bbase (se 2 (by rfl) ⟨661896, by rfl⟩ : syracuseStep 1765057 = 1323793) (by norm_num)
theorem B1674965 : Blo 1566981 1674965 := bbase (se 7 (by rfl) ⟨19628, by rfl⟩ : syracuseStep 1674965 = 39257) (by norm_num)
theorem B1765093 : Blo 1566981 1765093 := bbase (se 4 (by rfl) ⟨165477, by rfl⟩ : syracuseStep 1765093 = 330955) (by norm_num)
theorem B3526397 : Blo 1566981 3526397 := bbase (se 3 (by rfl) ⟨661199, by rfl⟩ : syracuseStep 3526397 = 1322399) (by norm_num)
theorem B3624725 : Blo 1566981 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B3968797 : Blo 1566981 3968797 := bbase (se 3 (by rfl) ⟨744149, by rfl⟩ : syracuseStep 3968797 = 1488299) (by norm_num)
theorem B1675037 : Blo 1566981 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B3526469 : Blo 1566981 3526469 := bbase (se 4 (by rfl) ⟨330606, by rfl⟩ : syracuseStep 3526469 = 661213) (by norm_num)
theorem B2977661 : Blo 1566981 2977661 := bbase (se 3 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 2977661 = 1116623) (by norm_num)
theorem B3526541 : Blo 1566981 3526541 := bbase (se 3 (by rfl) ⟨661226, by rfl⟩ : syracuseStep 3526541 = 1322453) (by norm_num)
theorem B3968909 : Blo 1566981 3968909 := bbase (se 3 (by rfl) ⟨744170, by rfl⟩ : syracuseStep 3968909 = 1488341) (by norm_num)
theorem B3526613 : Blo 1566981 3526613 := bbase (se 7 (by rfl) ⟨41327, by rfl⟩ : syracuseStep 3526613 = 82655) (by norm_num)
theorem B1675225 : Blo 1566981 1675225 := bbase (se 2 (by rfl) ⟨628209, by rfl⟩ : syracuseStep 1675225 = 1256419) (by norm_num)
theorem B2232301 : Blo 1566981 2232301 := bbase (se 3 (by rfl) ⟨418556, by rfl⟩ : syracuseStep 2232301 = 837113) (by norm_num)
theorem B3575789 : Blo 1566981 3575789 := bbase (se 3 (by rfl) ⟨670460, by rfl⟩ : syracuseStep 3575789 = 1340921) (by norm_num)
theorem B2977813 : Blo 1566981 2977813 := bbase (se 6 (by rfl) ⟨69792, by rfl⟩ : syracuseStep 2977813 = 139585) (by norm_num)
theorem B3526685 : Blo 1566981 3526685 := bbase (se 3 (by rfl) ⟨661253, by rfl⟩ : syracuseStep 3526685 = 1322507) (by norm_num)
theorem B5025829 : Blo 1566981 5025829 := bbase (se 4 (by rfl) ⟨471171, by rfl⟩ : syracuseStep 5025829 = 942343) (by norm_num)
theorem B12718133 : Blo 1566981 12718133 := bbase (se 5 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 12718133 = 1192325) (by norm_num)
theorem B3969101 : Blo 1566981 3969101 := bbase (se 3 (by rfl) ⟨744206, by rfl⟩ : syracuseStep 3969101 = 1488413) (by norm_num)
theorem B3526757 : Blo 1566981 3526757 := bbase (se 4 (by rfl) ⟨330633, by rfl⟩ : syracuseStep 3526757 = 661267) (by norm_num)
theorem B1675409 : Blo 1566981 1675409 := bbase (se 2 (by rfl) ⟨628278, by rfl⟩ : syracuseStep 1675409 = 1256557) (by norm_num)
theorem B3526829 : Blo 1566981 3526829 := bbase (se 3 (by rfl) ⟨661280, by rfl⟩ : syracuseStep 3526829 = 1322561) (by norm_num)
theorem B2232517 : Blo 1566981 2232517 := bbase (se 4 (by rfl) ⟨209298, by rfl⟩ : syracuseStep 2232517 = 418597) (by norm_num)
theorem B7942373 : Blo 1566981 7942373 := bbase (se 4 (by rfl) ⟨744597, by rfl⟩ : syracuseStep 7942373 = 1489195) (by norm_num)
theorem B3526901 : Blo 1566981 3526901 := bbase (se 5 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 3526901 = 330647) (by norm_num)
theorem B3526973 : Blo 1566981 3526973 := bbase (se 3 (by rfl) ⟨661307, by rfl⟩ : syracuseStep 3526973 = 1322615) (by norm_num)
theorem B2978117 : Blo 1566981 2978117 := bbase (se 4 (by rfl) ⟨279198, by rfl⟩ : syracuseStep 2978117 = 558397) (by norm_num)
theorem B5648741 : Blo 1566981 5648741 := bbase (se 4 (by rfl) ⟨529569, by rfl⟩ : syracuseStep 5648741 = 1059139) (by norm_num)
theorem B3527045 : Blo 1566981 3527045 := bbase (se 4 (by rfl) ⟨330660, by rfl⟩ : syracuseStep 3527045 = 661321) (by norm_num)
theorem B3969445 : Blo 1566981 3969445 := bbase (se 4 (by rfl) ⟨372135, by rfl⟩ : syracuseStep 3969445 = 744271) (by norm_num)
theorem B8049077 : Blo 1566981 8049077 := bbase (se 5 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 8049077 = 754601) (by norm_num)
theorem B3527117 : Blo 1566981 3527117 := bbase (se 3 (by rfl) ⟨661334, by rfl⟩ : syracuseStep 3527117 = 1322669) (by norm_num)
theorem B4076045 : Blo 1566981 4076045 := bbase (se 3 (by rfl) ⟨764258, by rfl⟩ : syracuseStep 4076045 = 1528517) (by norm_num)
theorem B3527189 : Blo 1566981 3527189 := bbase (se 6 (by rfl) ⟨82668, by rfl⟩ : syracuseStep 3527189 = 165337) (by norm_num)
theorem B3969557 : Blo 1566981 3969557 := bbase (se 6 (by rfl) ⟨93036, by rfl⟩ : syracuseStep 3969557 = 186073) (by norm_num)
theorem B2232893 : Blo 1566981 2232893 := bbase (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) (by norm_num)
theorem B3527261 : Blo 1566981 3527261 := bbase (se 3 (by rfl) ⟨661361, by rfl⟩ : syracuseStep 3527261 = 1322723) (by norm_num)
theorem B7934597 : Blo 1566981 7934597 := bbase (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) (by norm_num)
theorem B5288597 : Blo 1566981 5288597 := bbase (se 6 (by rfl) ⟨123951, by rfl⟩ : syracuseStep 5288597 = 247903) (by norm_num)
theorem B5952149 : Blo 1566981 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B3527333 : Blo 1566981 3527333 := bbase (se 4 (by rfl) ⟨330687, by rfl⟩ : syracuseStep 3527333 = 661375) (by norm_num)
theorem B2511557 : Blo 1566981 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B3969749 : Blo 1566981 3969749 := bbase (se 7 (by rfl) ⟨46520, by rfl⟩ : syracuseStep 3969749 = 93041) (by norm_num)
theorem B3527405 : Blo 1566981 3527405 := bbase (se 3 (by rfl) ⟨661388, by rfl⟩ : syracuseStep 3527405 = 1322777) (by norm_num)
theorem B3527477 : Blo 1566981 3527477 := bbase (se 5 (by rfl) ⟨165350, by rfl⟩ : syracuseStep 3527477 = 330701) (by norm_num)
theorem B8926037 : Blo 1566981 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B3625813 : Blo 1566981 3625813 := bbase (se 9 (by rfl) ⟨10622, by rfl⟩ : syracuseStep 3625813 = 21245) (by norm_num)
theorem B10179445 : Blo 1566981 10179445 := bbase (se 5 (by rfl) ⟨477161, by rfl⟩ : syracuseStep 10179445 = 954323) (by norm_num)
theorem B3527549 : Blo 1566981 3527549 := bbase (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) (by norm_num)
theorem B2511749 : Blo 1566981 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B5952437 : Blo 1566981 5952437 := bbase (se 5 (by rfl) ⟨279020, by rfl⟩ : syracuseStep 5952437 = 558041) (by norm_num)
theorem B3527621 : Blo 1566981 3527621 := bbase (se 4 (by rfl) ⟨330714, by rfl⟩ : syracuseStep 3527621 = 661429) (by norm_num)
theorem B3527693 : Blo 1566981 3527693 := bbase (se 3 (by rfl) ⟨661442, by rfl⟩ : syracuseStep 3527693 = 1322885) (by norm_num)
theorem B3970093 : Blo 1566981 3970093 := bbase (se 3 (by rfl) ⟨744392, by rfl⟩ : syracuseStep 3970093 = 1488785) (by norm_num)
theorem B12710965 : Blo 1566981 12710965 := bbase (se 5 (by rfl) ⟨595826, by rfl⟩ : syracuseStep 12710965 = 1191653) (by norm_num)
theorem B5289029 : Blo 1566981 5289029 := bbase (se 4 (by rfl) ⟨495846, by rfl⟩ : syracuseStep 5289029 = 991693) (by norm_num)
theorem B3527765 : Blo 1566981 3527765 := bbase (se 8 (by rfl) ⟨20670, by rfl⟩ : syracuseStep 3527765 = 41341) (by norm_num)
theorem B3527837 : Blo 1566981 3527837 := bbase (se 3 (by rfl) ⟨661469, by rfl⟩ : syracuseStep 3527837 = 1322939) (by norm_num)
theorem B3970205 : Blo 1566981 3970205 := bbase (se 3 (by rfl) ⟨744413, by rfl⟩ : syracuseStep 3970205 = 1488827) (by norm_num)
theorem B3527909 : Blo 1566981 3527909 := bbase (se 4 (by rfl) ⟨330741, by rfl⟩ : syracuseStep 3527909 = 661483) (by norm_num)
theorem B3577085 : Blo 1566981 3577085 := bbase (se 3 (by rfl) ⟨670703, by rfl⟩ : syracuseStep 3577085 = 1341407) (by norm_num)
theorem B3527981 : Blo 1566981 3527981 := bbase (se 3 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 3527981 = 1322993) (by norm_num)
theorem B12711221 : Blo 1566981 12711221 := bbase (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) (by norm_num)
theorem B3970397 : Blo 1566981 3970397 := bbase (se 3 (by rfl) ⟨744449, by rfl⟩ : syracuseStep 3970397 = 1488899) (by norm_num)
theorem B3528053 : Blo 1566981 3528053 := bbase (se 5 (by rfl) ⟨165377, by rfl⟩ : syracuseStep 3528053 = 330755) (by norm_num)
theorem B6034837 : Blo 1566981 6034837 := bbase (se 6 (by rfl) ⟨141441, by rfl⟩ : syracuseStep 6034837 = 282883) (by norm_num)
theorem B11302325 : Blo 1566981 11302325 := bbase (se 5 (by rfl) ⟨529796, by rfl⟩ : syracuseStep 11302325 = 1059593) (by norm_num)
theorem B3528125 : Blo 1566981 3528125 := bbase (se 3 (by rfl) ⟨661523, by rfl⟩ : syracuseStep 3528125 = 1323047) (by norm_num)
theorem B5289461 : Blo 1566981 5289461 := bbase (se 5 (by rfl) ⟨247943, by rfl⟩ : syracuseStep 5289461 = 495887) (by norm_num)
theorem B3528197 : Blo 1566981 3528197 := bbase (se 4 (by rfl) ⟨330768, by rfl⟩ : syracuseStep 3528197 = 661537) (by norm_num)
theorem B3528269 : Blo 1566981 3528269 := bbase (se 3 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 3528269 = 1323101) (by norm_num)
theorem B5650021 : Blo 1566981 5650021 := bbase (se 4 (by rfl) ⟨529689, by rfl⟩ : syracuseStep 5650021 = 1059379) (by norm_num)
theorem B2545277 : Blo 1566981 2545277 := bbase (se 3 (by rfl) ⟨477239, by rfl⟩ : syracuseStep 2545277 = 954479) (by norm_num)
theorem B3528341 : Blo 1566981 3528341 := bbase (se 6 (by rfl) ⟨82695, by rfl⟩ : syracuseStep 3528341 = 165391) (by norm_num)
theorem B6698645 : Blo 1566981 6698645 := bbase (se 6 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 6698645 = 313999) (by norm_num)
theorem B3970741 : Blo 1566981 3970741 := bbase (se 5 (by rfl) ⟨186128, by rfl⟩ : syracuseStep 3970741 = 372257) (by norm_num)
theorem B3528413 : Blo 1566981 3528413 := bbase (se 3 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 3528413 = 1323155) (by norm_num)
theorem B3765989 : Blo 1566981 3765989 := bbase (se 4 (by rfl) ⟨353061, by rfl⟩ : syracuseStep 3765989 = 706123) (by norm_num)
theorem B3348229 : Blo 1566981 3348229 := bbase (se 4 (by rfl) ⟨313896, by rfl⟩ : syracuseStep 3348229 = 627793) (by norm_num)
theorem B3528485 : Blo 1566981 3528485 := bbase (se 4 (by rfl) ⟨330795, by rfl⟩ : syracuseStep 3528485 = 661591) (by norm_num)
theorem B3970853 : Blo 1566981 3970853 := bbase (se 4 (by rfl) ⟨372267, by rfl⟩ : syracuseStep 3970853 = 744535) (by norm_num)
theorem B7534421 : Blo 1566981 7534421 := bbase (se 9 (by rfl) ⟨22073, by rfl⟩ : syracuseStep 7534421 = 44147) (by norm_num)
theorem B3528557 : Blo 1566981 3528557 := bbase (se 3 (by rfl) ⟨661604, by rfl⟩ : syracuseStep 3528557 = 1323209) (by norm_num)
theorem B7935893 : Blo 1566981 7935893 := bbase (se 6 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 7935893 = 371995) (by norm_num)
theorem B5289893 : Blo 1566981 5289893 := bbase (se 4 (by rfl) ⟨495927, by rfl⟩ : syracuseStep 5289893 = 991855) (by norm_num)
theorem B3766181 : Blo 1566981 3766181 := bbase (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) (by norm_num)
theorem B3528629 : Blo 1566981 3528629 := bbase (se 5 (by rfl) ⟨165404, by rfl⟩ : syracuseStep 3528629 = 330809) (by norm_num)
theorem B3971045 : Blo 1566981 3971045 := bbase (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) (by norm_num)
theorem B3528701 : Blo 1566981 3528701 := bbase (se 3 (by rfl) ⟨661631, by rfl⟩ : syracuseStep 3528701 = 1323263) (by norm_num)
theorem B5363765 : Blo 1566981 5363765 := bbase (se 5 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 5363765 = 502853) (by norm_num)
theorem B3528773 : Blo 1566981 3528773 := bbase (se 4 (by rfl) ⟨330822, by rfl⟩ : syracuseStep 3528773 = 661645) (by norm_num)
theorem B5953621 : Blo 1566981 5953621 := bbase (se 8 (by rfl) ⟨34884, by rfl⟩ : syracuseStep 5953621 = 69769) (by norm_num)
theorem B2119765 : Blo 1566981 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B4528261 : Blo 1566981 4528261 := bbase (se 4 (by rfl) ⟨424524, by rfl⟩ : syracuseStep 4528261 = 849049) (by norm_num)
theorem B3528845 : Blo 1566981 3528845 := bbase (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) (by norm_num)
theorem B2119861 : Blo 1566981 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B3528917 : Blo 1566981 3528917 := bbase (se 7 (by rfl) ⟨41354, by rfl⟩ : syracuseStep 3528917 = 82709) (by norm_num)
theorem B3528989 : Blo 1566981 3528989 := bbase (se 3 (by rfl) ⟨661685, by rfl⟩ : syracuseStep 3528989 = 1323371) (by norm_num)
theorem B2513197 : Blo 1566981 2513197 := bbase (se 3 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 2513197 = 942449) (by norm_num)
theorem B11909429 : Blo 1566981 11909429 := bbase (se 5 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 11909429 = 1116509) (by norm_num)
theorem B2644285 : Blo 1566981 2644285 := bbase (se 3 (by rfl) ⟨495803, by rfl⟩ : syracuseStep 2644285 = 991607) (by norm_num)
theorem B3971389 : Blo 1566981 3971389 := bbase (se 3 (by rfl) ⟨744635, by rfl⟩ : syracuseStep 3971389 = 1489271) (by norm_num)
theorem B5290325 : Blo 1566981 5290325 := bbase (se 10 (by rfl) ⟨7749, by rfl⟩ : syracuseStep 5290325 = 15499) (by norm_num)
theorem B3529061 : Blo 1566981 3529061 := bbase (se 4 (by rfl) ⟨330849, by rfl⟩ : syracuseStep 3529061 = 661699) (by norm_num)
theorem B5953925 : Blo 1566981 5953925 := bbase (se 4 (by rfl) ⟨558180, by rfl⟩ : syracuseStep 5953925 = 1116361) (by norm_num)
theorem B2644373 : Blo 1566981 2644373 := bbase (se 6 (by rfl) ⟨61977, by rfl⟩ : syracuseStep 2644373 = 123955) (by norm_num)
theorem B3529133 : Blo 1566981 3529133 := bbase (se 3 (by rfl) ⟨661712, by rfl⟩ : syracuseStep 3529133 = 1323425) (by norm_num)
theorem B4463029 : Blo 1566981 4463029 := bbase (se 5 (by rfl) ⟨209204, by rfl⟩ : syracuseStep 4463029 = 418409) (by norm_num)
theorem B3529205 : Blo 1566981 3529205 := bbase (se 5 (by rfl) ⟨165431, by rfl⟩ : syracuseStep 3529205 = 330863) (by norm_num)
theorem B2644501 : Blo 1566981 2644501 := bbase (se 6 (by rfl) ⟨61980, by rfl⟩ : syracuseStep 2644501 = 123961) (by norm_num)
theorem B3529277 : Blo 1566981 3529277 := bbase (se 3 (by rfl) ⟨661739, by rfl⟩ : syracuseStep 3529277 = 1323479) (by norm_num)
theorem B2644589 : Blo 1566981 2644589 := bbase (se 3 (by rfl) ⟨495860, by rfl⟩ : syracuseStep 2644589 = 991721) (by norm_num)
theorem B3349117 : Blo 1566981 3349117 := bbase (se 3 (by rfl) ⟨627959, by rfl⟩ : syracuseStep 3349117 = 1255919) (by norm_num)
theorem B3529349 : Blo 1566981 3529349 := bbase (se 4 (by rfl) ⟨330876, by rfl⟩ : syracuseStep 3529349 = 661753) (by norm_num)
theorem B4766357 : Blo 1566981 4766357 := bbase (se 6 (by rfl) ⟨111711, by rfl⟩ : syracuseStep 4766357 = 223423) (by norm_num)
theorem B3529421 : Blo 1566981 3529421 := bbase (se 3 (by rfl) ⟨661766, by rfl⟩ : syracuseStep 3529421 = 1323533) (by norm_num)
theorem B11901653 : Blo 1566981 11901653 := bbase (se 7 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 11901653 = 278945) (by norm_num)
theorem B2644717 : Blo 1566981 2644717 := bbase (se 3 (by rfl) ⟨495884, by rfl⟩ : syracuseStep 2644717 = 991769) (by norm_num)
theorem B5290757 : Blo 1566981 5290757 := bbase (se 4 (by rfl) ⟨496008, by rfl⟩ : syracuseStep 5290757 = 992017) (by norm_num)
theorem B3529493 : Blo 1566981 3529493 := bbase (se 6 (by rfl) ⟨82722, by rfl⟩ : syracuseStep 3529493 = 165445) (by norm_num)
theorem B1882937 : Blo 1566981 1882937 := bbase (se 2 (by rfl) ⟨706101, by rfl⟩ : syracuseStep 1882937 = 1412203) (by norm_num)
theorem B2644805 : Blo 1566981 2644805 := bbase (se 4 (by rfl) ⟨247950, by rfl⟩ : syracuseStep 2644805 = 495901) (by norm_num)
theorem B32168789 : Blo 1566981 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B3529565 : Blo 1566981 3529565 := bbase (se 3 (by rfl) ⟨661793, by rfl⟩ : syracuseStep 3529565 = 1323587) (by norm_num)
theorem B3529637 : Blo 1566981 3529637 := bbase (se 4 (by rfl) ⟨330903, by rfl⟩ : syracuseStep 3529637 = 661807) (by norm_num)
theorem B2644933 : Blo 1566981 2644933 := bbase (se 4 (by rfl) ⟨247962, by rfl⟩ : syracuseStep 2644933 = 495925) (by norm_num)
theorem B3529709 : Blo 1566981 3529709 := bbase (se 3 (by rfl) ⟨661820, by rfl⟩ : syracuseStep 3529709 = 1323641) (by norm_num)
theorem B8928245 : Blo 1566981 8928245 := bbase (se 5 (by rfl) ⟨418511, by rfl⟩ : syracuseStep 8928245 = 837023) (by norm_num)
theorem B10730485 : Blo 1566981 10730485 := bbase (se 5 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 10730485 = 1005983) (by norm_num)
theorem B2645021 : Blo 1566981 2645021 := bbase (se 3 (by rfl) ⟨495941, by rfl⟩ : syracuseStep 2645021 = 991883) (by norm_num)
theorem B3529781 : Blo 1566981 3529781 := bbase (se 5 (by rfl) ⟨165458, by rfl⟩ : syracuseStep 3529781 = 330917) (by norm_num)
theorem B1883197 : Blo 1566981 1883197 := bbase (se 3 (by rfl) ⟨353099, by rfl⟩ : syracuseStep 1883197 = 706199) (by norm_num)
theorem B2825293 : Blo 1566981 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B1883245 : Blo 1566981 1883245 := bbase (se 3 (by rfl) ⟨353108, by rfl⟩ : syracuseStep 1883245 = 706217) (by norm_num)
theorem B3349613 : Blo 1566981 3349613 := bbase (se 3 (by rfl) ⟨628052, by rfl⟩ : syracuseStep 3349613 = 1256105) (by norm_num)
theorem B3529853 : Blo 1566981 3529853 := bbase (se 3 (by rfl) ⟨661847, by rfl⟩ : syracuseStep 3529853 = 1323695) (by norm_num)
theorem B2645149 : Blo 1566981 2645149 := bbase (se 3 (by rfl) ⟨495965, by rfl⟩ : syracuseStep 2645149 = 991931) (by norm_num)
theorem B7937189 : Blo 1566981 7937189 := bbase (se 4 (by rfl) ⟨744111, by rfl⟩ : syracuseStep 7937189 = 1488223) (by norm_num)
theorem B5291189 : Blo 1566981 5291189 := bbase (se 5 (by rfl) ⟨248024, by rfl⟩ : syracuseStep 5291189 = 496049) (by norm_num)
theorem B5364917 : Blo 1566981 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B3529925 : Blo 1566981 3529925 := bbase (se 4 (by rfl) ⟨330930, by rfl⟩ : syracuseStep 3529925 = 661861) (by norm_num)
theorem B10042613 : Blo 1566981 10042613 := bbase (se 5 (by rfl) ⟨470747, by rfl⟩ : syracuseStep 10042613 = 941495) (by norm_num)
theorem B2645237 : Blo 1566981 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B3529997 : Blo 1566981 3529997 := bbase (se 3 (by rfl) ⟨661874, by rfl⟩ : syracuseStep 3529997 = 1323749) (by norm_num)
theorem B3530069 : Blo 1566981 3530069 := bbase (se 11 (by rfl) ⟨2585, by rfl⟩ : syracuseStep 3530069 = 5171) (by norm_num)
theorem B2645365 : Blo 1566981 2645365 := bbase (se 5 (by rfl) ⟨124001, by rfl⟩ : syracuseStep 2645365 = 248003) (by norm_num)
theorem B6700421 : Blo 1566981 6700421 := bbase (se 4 (by rfl) ⟨628164, by rfl⟩ : syracuseStep 6700421 = 1256329) (by norm_num)
theorem B10722709 : Blo 1566981 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B2350493 : Blo 1566981 2350493 := bbase (se 3 (by rfl) ⟨440717, by rfl⟩ : syracuseStep 2350493 = 881435) (by norm_num)
theorem B3530141 : Blo 1566981 3530141 := bbase (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) (by norm_num)
theorem B2350517 : Blo 1566981 2350517 := bbase (se 5 (by rfl) ⟨110180, by rfl⟩ : syracuseStep 2350517 = 220361) (by norm_num)
theorem B7536053 : Blo 1566981 7536053 := bbase (se 5 (by rfl) ⟨353252, by rfl⟩ : syracuseStep 7536053 = 706505) (by norm_num)
theorem B2350541 : Blo 1566981 2350541 := bbase (se 3 (by rfl) ⟨440726, by rfl⟩ : syracuseStep 2350541 = 881453) (by norm_num)
theorem B2645453 : Blo 1566981 2645453 := bbase (se 3 (by rfl) ⟨496022, by rfl⟩ : syracuseStep 2645453 = 992045) (by norm_num)
theorem B2350565 : Blo 1566981 2350565 := bbase (se 4 (by rfl) ⟨220365, by rfl⟩ : syracuseStep 2350565 = 440731) (by norm_num)
theorem B2350589 : Blo 1566981 2350589 := bbase (se 3 (by rfl) ⟨440735, by rfl⟩ : syracuseStep 2350589 = 881471) (by norm_num)
theorem B2350613 : Blo 1566981 2350613 := bbase (se 6 (by rfl) ⟨55092, by rfl⟩ : syracuseStep 2350613 = 110185) (by norm_num)
theorem B2350637 : Blo 1566981 2350637 := bbase (se 3 (by rfl) ⟨440744, by rfl⟩ : syracuseStep 2350637 = 881489) (by norm_num)
theorem B2350661 : Blo 1566981 2350661 := bbase (se 4 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 2350661 = 440749) (by norm_num)
theorem B2645581 : Blo 1566981 2645581 := bbase (se 3 (by rfl) ⟨496046, by rfl⟩ : syracuseStep 2645581 = 992093) (by norm_num)
theorem B2350685 : Blo 1566981 2350685 := bbase (se 3 (by rfl) ⟨440753, by rfl⟩ : syracuseStep 2350685 = 881507) (by norm_num)
theorem B5291621 : Blo 1566981 5291621 := bbase (se 4 (by rfl) ⟨496089, by rfl⟩ : syracuseStep 5291621 = 992179) (by norm_num)
theorem B2350709 : Blo 1566981 2350709 := bbase (se 5 (by rfl) ⟨110189, by rfl⟩ : syracuseStep 2350709 = 220379) (by norm_num)
theorem B2350733 : Blo 1566981 2350733 := bbase (se 3 (by rfl) ⟨440762, by rfl⟩ : syracuseStep 2350733 = 881525) (by norm_num)
theorem B2350757 : Blo 1566981 2350757 := bbase (se 4 (by rfl) ⟨220383, by rfl⟩ : syracuseStep 2350757 = 440767) (by norm_num)
theorem B2645669 : Blo 1566981 2645669 := bbase (se 4 (by rfl) ⟨248031, by rfl⟩ : syracuseStep 2645669 = 496063) (by norm_num)
theorem B2350781 : Blo 1566981 2350781 := bbase (se 3 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 2350781 = 881543) (by norm_num)
theorem B2825933 : Blo 1566981 2825933 := bbase (se 3 (by rfl) ⟨529862, by rfl⟩ : syracuseStep 2825933 = 1059725) (by norm_num)
theorem B2350805 : Blo 1566981 2350805 := bbase (se 7 (by rfl) ⟨27548, by rfl⟩ : syracuseStep 2350805 = 55097) (by norm_num)
theorem B2350829 : Blo 1566981 2350829 := bbase (se 3 (by rfl) ⟨440780, by rfl⟩ : syracuseStep 2350829 = 881561) (by norm_num)
theorem B2350853 : Blo 1566981 2350853 := bbase (se 4 (by rfl) ⟨220392, by rfl⟩ : syracuseStep 2350853 = 440785) (by norm_num)
theorem B1883917 : Blo 1566981 1883917 := bbase (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) (by norm_num)
theorem B2293525 : Blo 1566981 2293525 := bbase (se 6 (by rfl) ⟨53754, by rfl⟩ : syracuseStep 2293525 = 107509) (by norm_num)
theorem B2350877 : Blo 1566981 2350877 := bbase (se 3 (by rfl) ⟨440789, by rfl⟩ : syracuseStep 2350877 = 881579) (by norm_num)
theorem B2645797 : Blo 1566981 2645797 := bbase (se 4 (by rfl) ⟨248043, by rfl⟩ : syracuseStep 2645797 = 496087) (by norm_num)
theorem B2350901 : Blo 1566981 2350901 := bbase (se 5 (by rfl) ⟨110198, by rfl⟩ : syracuseStep 2350901 = 220397) (by norm_num)
theorem B3768133 : Blo 1566981 3768133 := bbase (se 4 (by rfl) ⟨353262, by rfl⟩ : syracuseStep 3768133 = 706525) (by norm_num)
theorem B2350925 : Blo 1566981 2350925 := bbase (se 3 (by rfl) ⟨440798, by rfl⟩ : syracuseStep 2350925 = 881597) (by norm_num)
theorem B3178325 : Blo 1566981 3178325 := bbase (se 9 (by rfl) ⟨9311, by rfl⟩ : syracuseStep 3178325 = 18623) (by norm_num)
theorem B2350949 : Blo 1566981 2350949 := bbase (se 4 (by rfl) ⟨220401, by rfl⟩ : syracuseStep 2350949 = 440803) (by norm_num)
theorem B2350973 : Blo 1566981 2350973 := bbase (se 3 (by rfl) ⟨440807, by rfl⟩ : syracuseStep 2350973 = 881615) (by norm_num)
theorem B2645885 : Blo 1566981 2645885 := bbase (se 3 (by rfl) ⟨496103, by rfl⟩ : syracuseStep 2645885 = 992207) (by norm_num)
theorem B2350997 : Blo 1566981 2350997 := bbase (se 6 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 2350997 = 110203) (by norm_num)
theorem B4464533 : Blo 1566981 4464533 := bbase (se 6 (by rfl) ⟨104637, by rfl⟩ : syracuseStep 4464533 = 209275) (by norm_num)
theorem B2351021 : Blo 1566981 2351021 := bbase (se 3 (by rfl) ⟨440816, by rfl⟩ : syracuseStep 2351021 = 881633) (by norm_num)
theorem B2351045 : Blo 1566981 2351045 := bbase (se 4 (by rfl) ⟨220410, by rfl⟩ : syracuseStep 2351045 = 440821) (by norm_num)
theorem B3350477 : Blo 1566981 3350477 := bbase (se 3 (by rfl) ⟨628214, by rfl⟩ : syracuseStep 3350477 = 1256429) (by norm_num)
theorem B2351069 : Blo 1566981 2351069 := bbase (se 3 (by rfl) ⟨440825, by rfl⟩ : syracuseStep 2351069 = 881651) (by norm_num)
theorem B2351093 : Blo 1566981 2351093 := bbase (se 5 (by rfl) ⟨110207, by rfl⟩ : syracuseStep 2351093 = 220415) (by norm_num)
theorem B2646013 : Blo 1566981 2646013 := bbase (se 3 (by rfl) ⟨496127, by rfl⟩ : syracuseStep 2646013 = 992255) (by norm_num)
theorem B2351105 : Blo 1566981 2351105 := bstep (se 2 (by rfl) ⟨881664, by rfl⟩ : syracuseStep 2351105 = 1763329) B1763329
theorem B2351123 : Blo 1566981 2351123 := bstep (se 1 (by rfl) ⟨1763342, by rfl⟩ : syracuseStep 2351123 = 3526685) B3526685
theorem B8478755 : Blo 1566981 8478755 := bstep (se 1 (by rfl) ⟨6359066, by rfl⟩ : syracuseStep 8478755 = 12718133) B12718133
theorem B2351153 : Blo 1566981 2351153 := bstep (se 2 (by rfl) ⟨881682, by rfl⟩ : syracuseStep 2351153 = 1763365) B1763365
theorem B6701105 : Blo 1566981 6701105 := bstep (se 2 (by rfl) ⟨2512914, by rfl⟩ : syracuseStep 6701105 = 5025829) B5025829
theorem B2646067 : Blo 1566981 2646067 := bstep (se 1 (by rfl) ⟨1984550, by rfl⟩ : syracuseStep 2646067 = 3969101) B3969101
theorem B2351171 : Blo 1566981 2351171 := bstep (se 1 (by rfl) ⟨1763378, by rfl⟩ : syracuseStep 2351171 = 3526757) B3526757
theorem B2351201 : Blo 1566981 2351201 := bstep (se 2 (by rfl) ⟨881700, by rfl⟩ : syracuseStep 2351201 = 1763401) B1763401
theorem B5726321 : Blo 1566981 5726321 := bstep (se 2 (by rfl) ⟨2147370, by rfl⟩ : syracuseStep 5726321 = 4294741) B4294741
theorem B7938161 : Blo 1566981 7938161 := bstep (se 2 (by rfl) ⟨2976810, by rfl⟩ : syracuseStep 7938161 = 5953621) B5953621
theorem B2351219 : Blo 1566981 2351219 := bstep (se 1 (by rfl) ⟨1763414, by rfl⟩ : syracuseStep 2351219 = 3526829) B3526829
theorem B2826353 : Blo 1566981 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B5365873 : Blo 1566981 5365873 := bstep (se 2 (by rfl) ⟨2012202, by rfl⟩ : syracuseStep 5365873 = 4024405) B4024405
theorem B2351249 : Blo 1566981 2351249 := bstep (se 2 (by rfl) ⟨881718, by rfl⟩ : syracuseStep 2351249 = 1763437) B1763437
theorem B2351267 : Blo 1566981 2351267 := bstep (se 1 (by rfl) ⟨1763450, by rfl⟩ : syracuseStep 2351267 = 3526901) B3526901
theorem B6037681 : Blo 1566981 6037681 := bstep (se 2 (by rfl) ⟨2264130, by rfl⟩ : syracuseStep 6037681 = 4528261) B4528261
theorem B2351297 : Blo 1566981 2351297 := bstep (se 2 (by rfl) ⟨881736, by rfl⟩ : syracuseStep 2351297 = 1763473) B1763473
theorem B2384065 : Blo 1566981 2384065 := bstep (se 2 (by rfl) ⟨894024, by rfl⟩ : syracuseStep 2384065 = 1788049) B1788049
theorem B2646209 : Blo 1566981 2646209 := bstep (se 2 (by rfl) ⟨992328, by rfl⟩ : syracuseStep 2646209 = 1984657) B1984657
theorem B2351315 : Blo 1566981 2351315 := bstep (se 1 (by rfl) ⟨1763486, by rfl⟩ : syracuseStep 2351315 = 3526973) B3526973
theorem B5292269 : Blo 1566981 5292269 := bstep (se 3 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 5292269 = 1984601) B1984601
theorem B2351345 : Blo 1566981 2351345 := bstep (se 2 (by rfl) ⟨881754, by rfl⟩ : syracuseStep 2351345 = 1763509) B1763509
theorem B7536881 : Blo 1566981 7536881 := bstep (se 2 (by rfl) ⟨2826330, by rfl⟩ : syracuseStep 7536881 = 5652661) B5652661
theorem B2351363 : Blo 1566981 2351363 := bstep (se 1 (by rfl) ⟨1763522, by rfl⟩ : syracuseStep 2351363 = 3527045) B3527045
theorem B2351393 : Blo 1566981 2351393 := bstep (se 2 (by rfl) ⟨881772, by rfl⟩ : syracuseStep 2351393 = 1763545) B1763545
theorem B5292323 : Blo 1566981 5292323 := bstep (se 1 (by rfl) ⟨3969242, by rfl⟩ : syracuseStep 5292323 = 7938485) B7938485
theorem B5366051 : Blo 1566981 5366051 := bstep (se 1 (by rfl) ⟨4024538, by rfl⟩ : syracuseStep 5366051 = 8049077) B8049077
theorem B2351411 : Blo 1566981 2351411 := bstep (se 1 (by rfl) ⟨1763558, by rfl⟩ : syracuseStep 2351411 = 3527117) B3527117
theorem B2646337 : Blo 1566981 2646337 := bstep (se 2 (by rfl) ⟨992376, by rfl⟩ : syracuseStep 2646337 = 1984753) B1984753
theorem B2351441 : Blo 1566981 2351441 := bstep (se 2 (by rfl) ⟨881790, by rfl⟩ : syracuseStep 2351441 = 1763581) B1763581
theorem B2351459 : Blo 1566981 2351459 := bstep (se 1 (by rfl) ⟨1763594, by rfl⟩ : syracuseStep 2351459 = 3527189) B3527189
theorem B2646371 : Blo 1566981 2646371 := bstep (se 1 (by rfl) ⟨1984778, by rfl⟩ : syracuseStep 2646371 = 3969557) B3969557
theorem B4768109 : Blo 1566981 4768109 := bstep (se 3 (by rfl) ⟨894020, by rfl⟩ : syracuseStep 4768109 = 1788041) B1788041
theorem B2351489 : Blo 1566981 2351489 := bstep (se 2 (by rfl) ⟨881808, by rfl⟩ : syracuseStep 2351489 = 1763617) B1763617
theorem B3350929 : Blo 1566981 3350929 := bstep (se 2 (by rfl) ⟨1256598, by rfl⟩ : syracuseStep 3350929 = 2513197) B2513197
theorem B2351507 : Blo 1566981 2351507 := bstep (se 1 (by rfl) ⟨1763630, by rfl⟩ : syracuseStep 2351507 = 3527261) B3527261
theorem B2351537 : Blo 1566981 2351537 := bstep (se 2 (by rfl) ⟨881826, by rfl⟩ : syracuseStep 2351537 = 1763653) B1763653
theorem B2351555 : Blo 1566981 2351555 := bstep (se 1 (by rfl) ⟨1763666, by rfl⟩ : syracuseStep 2351555 = 3527333) B3527333
theorem B10052045 : Blo 1566981 10052045 := bstep (se 3 (by rfl) ⟨1884758, by rfl⟩ : syracuseStep 10052045 = 3769517) B3769517
theorem B2351585 : Blo 1566981 2351585 := bstep (se 2 (by rfl) ⟨881844, by rfl⟩ : syracuseStep 2351585 = 1763689) B1763689
theorem B2646499 : Blo 1566981 2646499 := bstep (se 1 (by rfl) ⟨1984874, by rfl⟩ : syracuseStep 2646499 = 3969749) B3969749
theorem B2351603 : Blo 1566981 2351603 := bstep (se 1 (by rfl) ⟨1763702, by rfl⟩ : syracuseStep 2351603 = 3527405) B3527405
theorem B2351633 : Blo 1566981 2351633 := bstep (se 2 (by rfl) ⟨881862, by rfl⟩ : syracuseStep 2351633 = 1763725) B1763725
theorem B2351651 : Blo 1566981 2351651 := bstep (se 1 (by rfl) ⟨1763738, by rfl⟩ : syracuseStep 2351651 = 3527477) B3527477
theorem B5292593 : Blo 1566981 5292593 := bstep (se 2 (by rfl) ⟨1984722, by rfl⟩ : syracuseStep 5292593 = 3969445) B3969445
theorem B2351681 : Blo 1566981 2351681 := bstep (se 2 (by rfl) ⟨881880, by rfl⟩ : syracuseStep 2351681 = 1763761) B1763761
theorem B2351699 : Blo 1566981 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B2351729 : Blo 1566981 2351729 := bstep (se 2 (by rfl) ⟨881898, by rfl⟩ : syracuseStep 2351729 = 1763797) B1763797
theorem B2646641 : Blo 1566981 2646641 := bstep (se 2 (by rfl) ⟨992490, by rfl⟩ : syracuseStep 2646641 = 1984981) B1984981
theorem B2351747 : Blo 1566981 2351747 := bstep (se 1 (by rfl) ⟨1763810, by rfl⟩ : syracuseStep 2351747 = 3527621) B3527621
theorem B2351777 : Blo 1566981 2351777 := bstep (se 2 (by rfl) ⟨881916, by rfl⟩ : syracuseStep 2351777 = 1763833) B1763833
theorem B2351795 : Blo 1566981 2351795 := bstep (se 1 (by rfl) ⟨1763846, by rfl⟩ : syracuseStep 2351795 = 3527693) B3527693
theorem B2351825 : Blo 1566981 2351825 := bstep (se 2 (by rfl) ⟨881934, by rfl⟩ : syracuseStep 2351825 = 1763869) B1763869
theorem B2351843 : Blo 1566981 2351843 := bstep (se 1 (by rfl) ⟨1763882, by rfl⟩ : syracuseStep 2351843 = 3527765) B3527765
theorem B2646769 : Blo 1566981 2646769 := bstep (se 2 (by rfl) ⟨992538, by rfl⟩ : syracuseStep 2646769 = 1985077) B1985077
theorem B2351873 : Blo 1566981 2351873 := bstep (se 2 (by rfl) ⟨881952, by rfl⟩ : syracuseStep 2351873 = 1763905) B1763905
theorem B2351891 : Blo 1566981 2351891 := bstep (se 1 (by rfl) ⟨1763918, by rfl⟩ : syracuseStep 2351891 = 3527837) B3527837
theorem B2646803 : Blo 1566981 2646803 := bstep (se 1 (by rfl) ⟨1985102, by rfl⟩ : syracuseStep 2646803 = 3970205) B3970205
theorem B2351921 : Blo 1566981 2351921 := bstep (se 2 (by rfl) ⟨881970, by rfl⟩ : syracuseStep 2351921 = 1763941) B1763941
theorem B2351939 : Blo 1566981 2351939 := bstep (se 1 (by rfl) ⟨1763954, by rfl⟩ : syracuseStep 2351939 = 3527909) B3527909
theorem B2384723 : Blo 1566981 2384723 := bstep (se 1 (by rfl) ⟨1788542, by rfl⟩ : syracuseStep 2384723 = 3577085) B3577085
theorem B2351969 : Blo 1566981 2351969 := bstep (se 2 (by rfl) ⟨881988, by rfl⟩ : syracuseStep 2351969 = 1763977) B1763977
theorem B2351987 : Blo 1566981 2351987 := bstep (se 1 (by rfl) ⟨1763990, by rfl⟩ : syracuseStep 2351987 = 3527981) B3527981
theorem B2352017 : Blo 1566981 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B2646931 : Blo 1566981 2646931 := bstep (se 1 (by rfl) ⟨1985198, by rfl⟩ : syracuseStep 2646931 = 3970397) B3970397
theorem B2352035 : Blo 1566981 2352035 := bstep (se 1 (by rfl) ⟨1764026, by rfl⟩ : syracuseStep 2352035 = 3528053) B3528053
theorem B2352065 : Blo 1566981 2352065 := bstep (se 2 (by rfl) ⟨882024, by rfl⟩ : syracuseStep 2352065 = 1764049) B1764049
theorem B11305925 : Blo 1566981 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B2352083 : Blo 1566981 2352083 := bstep (se 1 (by rfl) ⟨1764062, by rfl⟩ : syracuseStep 2352083 = 3528125) B3528125
theorem B2352113 : Blo 1566981 2352113 := bstep (se 2 (by rfl) ⟨882042, by rfl⟩ : syracuseStep 2352113 = 1764085) B1764085
theorem B2352131 : Blo 1566981 2352131 := bstep (se 1 (by rfl) ⟨1764098, by rfl⟩ : syracuseStep 2352131 = 3528197) B3528197
theorem B17867789 : Blo 1566981 17867789 := bstep (se 3 (by rfl) ⟨3350210, by rfl⟩ : syracuseStep 17867789 = 6700421) B6700421
theorem B2352161 : Blo 1566981 2352161 := bstep (se 2 (by rfl) ⟨882060, by rfl⟩ : syracuseStep 2352161 = 1764121) B1764121
theorem B2647073 : Blo 1566981 2647073 := bstep (se 2 (by rfl) ⟨992652, by rfl⟩ : syracuseStep 2647073 = 1985305) B1985305
theorem B1983523 : Blo 1566981 1983523 := bstep (se 1 (by rfl) ⟨1487642, by rfl⟩ : syracuseStep 1983523 = 2975285) B2975285
theorem B2352179 : Blo 1566981 2352179 := bstep (se 1 (by rfl) ⟨1764134, by rfl⟩ : syracuseStep 2352179 = 3528269) B3528269
theorem B17409077 : Blo 1566981 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B3769411 : Blo 1566981 3769411 := bstep (se 1 (by rfl) ⟨2827058, by rfl⟩ : syracuseStep 3769411 = 5654117) B5654117
theorem B5293133 : Blo 1566981 5293133 := bstep (se 3 (by rfl) ⟨992462, by rfl⟩ : syracuseStep 5293133 = 1984925) B1984925
theorem B2352209 : Blo 1566981 2352209 := bstep (se 2 (by rfl) ⟨882078, by rfl⟩ : syracuseStep 2352209 = 1764157) B1764157
theorem B2352227 : Blo 1566981 2352227 := bstep (se 1 (by rfl) ⟨1764170, by rfl⟩ : syracuseStep 2352227 = 3528341) B3528341
theorem B4465763 : Blo 1566981 4465763 := bstep (se 1 (by rfl) ⟨3349322, by rfl⟩ : syracuseStep 4465763 = 6698645) B6698645
theorem B4834417 : Blo 1566981 4834417 := bstep (se 2 (by rfl) ⟨1812906, by rfl⟩ : syracuseStep 4834417 = 3625813) B3625813
theorem B2352257 : Blo 1566981 2352257 := bstep (se 2 (by rfl) ⟨882096, by rfl⟩ : syracuseStep 2352257 = 1764193) B1764193
theorem B1983619 : Blo 1566981 1983619 := bstep (se 1 (by rfl) ⟨1487714, by rfl⟩ : syracuseStep 1983619 = 2975429) B2975429
theorem B5293187 : Blo 1566981 5293187 := bstep (se 1 (by rfl) ⟨3969890, by rfl⟩ : syracuseStep 5293187 = 7939781) B7939781
theorem B7537805 : Blo 1566981 7537805 := bstep (se 3 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 7537805 = 2826677) B2826677
theorem B2352275 : Blo 1566981 2352275 := bstep (se 1 (by rfl) ⟨1764206, by rfl⟩ : syracuseStep 2352275 = 3528413) B3528413
theorem B2647201 : Blo 1566981 2647201 := bstep (se 2 (by rfl) ⟨992700, by rfl⟩ : syracuseStep 2647201 = 1985401) B1985401
theorem B2974897 : Blo 1566981 2974897 := bstep (se 2 (by rfl) ⟨1115586, by rfl⟩ : syracuseStep 2974897 = 2231173) B2231173
theorem B2352305 : Blo 1566981 2352305 := bstep (se 2 (by rfl) ⟨882114, by rfl⟩ : syracuseStep 2352305 = 1764229) B1764229
theorem B2352323 : Blo 1566981 2352323 := bstep (se 1 (by rfl) ⟨1764242, by rfl⟩ : syracuseStep 2352323 = 3528485) B3528485
theorem B2647235 : Blo 1566981 2647235 := bstep (se 1 (by rfl) ⟨1985426, by rfl⟩ : syracuseStep 2647235 = 3970853) B3970853
theorem B2352353 : Blo 1566981 2352353 := bstep (se 2 (by rfl) ⟨882132, by rfl⟩ : syracuseStep 2352353 = 1764265) B1764265
theorem B5022947 : Blo 1566981 5022947 := bstep (se 1 (by rfl) ⟨3767210, by rfl⟩ : syracuseStep 5022947 = 7534421) B7534421
theorem B2352371 : Blo 1566981 2352371 := bstep (se 1 (by rfl) ⟨1764278, by rfl⟩ : syracuseStep 2352371 = 3528557) B3528557
theorem B2352401 : Blo 1566981 2352401 := bstep (se 2 (by rfl) ⟨882150, by rfl⟩ : syracuseStep 2352401 = 1764301) B1764301
theorem B2352419 : Blo 1566981 2352419 := bstep (se 1 (by rfl) ⟨1764314, by rfl⟩ : syracuseStep 2352419 = 3528629) B3528629
theorem B2352449 : Blo 1566981 2352449 := bstep (se 2 (by rfl) ⟨882168, by rfl⟩ : syracuseStep 2352449 = 1764337) B1764337
theorem B2647363 : Blo 1566981 2647363 := bstep (se 1 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 2647363 = 3971045) B3971045
theorem B2352467 : Blo 1566981 2352467 := bstep (se 1 (by rfl) ⟨1764350, by rfl⟩ : syracuseStep 2352467 = 3528701) B3528701
theorem B13763953 : Blo 1566981 13763953 := bstep (se 2 (by rfl) ⟨5161482, by rfl⟩ : syracuseStep 13763953 = 10322965) B10322965
theorem B2352497 : Blo 1566981 2352497 := bstep (se 2 (by rfl) ⟨882186, by rfl⟩ : syracuseStep 2352497 = 1764373) B1764373
theorem B2352515 : Blo 1566981 2352515 := bstep (se 1 (by rfl) ⟨1764386, by rfl⟩ : syracuseStep 2352515 = 3528773) B3528773
theorem B5293457 : Blo 1566981 5293457 := bstep (se 2 (by rfl) ⟨1985046, by rfl⟩ : syracuseStep 5293457 = 3970093) B3970093
theorem B2352545 : Blo 1566981 2352545 := bstep (se 2 (by rfl) ⟨882204, by rfl⟩ : syracuseStep 2352545 = 1764409) B1764409
theorem B2352563 : Blo 1566981 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B12232133 : Blo 1566981 12232133 := bstep (se 4 (by rfl) ⟨1146762, by rfl⟩ : syracuseStep 12232133 = 2293525) B2293525
theorem B2352593 : Blo 1566981 2352593 := bstep (se 2 (by rfl) ⟨882222, by rfl⟩ : syracuseStep 2352593 = 1764445) B1764445
theorem B2647505 : Blo 1566981 2647505 := bstep (se 2 (by rfl) ⟨992814, by rfl⟩ : syracuseStep 2647505 = 1985629) B1985629
theorem B2352611 : Blo 1566981 2352611 := bstep (se 1 (by rfl) ⟨1764458, by rfl⟩ : syracuseStep 2352611 = 3528917) B3528917
theorem B2262529 : Blo 1566981 2262529 := bstep (se 2 (by rfl) ⟨848448, by rfl⟩ : syracuseStep 2262529 = 1696897) B1696897
theorem B2352641 : Blo 1566981 2352641 := bstep (se 2 (by rfl) ⟨882240, by rfl⟩ : syracuseStep 2352641 = 1764481) B1764481
theorem B2352659 : Blo 1566981 2352659 := bstep (se 1 (by rfl) ⟨1764494, by rfl⟩ : syracuseStep 2352659 = 3528989) B3528989
theorem B7939619 : Blo 1566981 7939619 := bstep (se 1 (by rfl) ⟨5954714, by rfl⟩ : syracuseStep 7939619 = 11909429) B11909429
theorem B2352689 : Blo 1566981 2352689 := bstep (se 2 (by rfl) ⟨882258, by rfl⟩ : syracuseStep 2352689 = 1764517) B1764517
theorem B2352707 : Blo 1566981 2352707 := bstep (se 1 (by rfl) ⟨1764530, by rfl⟩ : syracuseStep 2352707 = 3529061) B3529061
theorem B2647633 : Blo 1566981 2647633 := bstep (se 2 (by rfl) ⟨992862, by rfl⟩ : syracuseStep 2647633 = 1985725) B1985725
theorem B2352737 : Blo 1566981 2352737 := bstep (se 2 (by rfl) ⟨882276, by rfl⟩ : syracuseStep 2352737 = 1764553) B1764553
theorem B1762915 : Blo 1566981 1762915 := bstep (se 1 (by rfl) ⟨1322186, by rfl⟩ : syracuseStep 1762915 = 2644373) B2644373
theorem B1984115 : Blo 1566981 1984115 := bstep (se 1 (by rfl) ⟨1488086, by rfl⟩ : syracuseStep 1984115 = 2976173) B2976173
theorem B2352755 : Blo 1566981 2352755 := bstep (se 1 (by rfl) ⟨1764566, by rfl⟩ : syracuseStep 2352755 = 3529133) B3529133
theorem B2352785 : Blo 1566981 2352785 := bstep (se 2 (by rfl) ⟨882294, by rfl⟩ : syracuseStep 2352785 = 1764589) B1764589
theorem B2352803 : Blo 1566981 2352803 := bstep (se 1 (by rfl) ⟨1764602, by rfl⟩ : syracuseStep 2352803 = 3529205) B3529205
theorem B3966641 : Blo 1566981 3966641 := bstep (se 2 (by rfl) ⟨1487490, by rfl⟩ : syracuseStep 3966641 = 2974981) B2974981
theorem B2352833 : Blo 1566981 2352833 := bstep (se 2 (by rfl) ⟨882312, by rfl⟩ : syracuseStep 2352833 = 1764625) B1764625
theorem B2352851 : Blo 1566981 2352851 := bstep (se 1 (by rfl) ⟨1764638, by rfl⟩ : syracuseStep 2352851 = 3529277) B3529277
theorem B3966691 : Blo 1566981 3966691 := bstep (se 1 (by rfl) ⟨2975018, by rfl⟩ : syracuseStep 3966691 = 5950037) B5950037
theorem B2352881 : Blo 1566981 2352881 := bstep (se 2 (by rfl) ⟨882330, by rfl⟩ : syracuseStep 2352881 = 1764661) B1764661
theorem B1763059 : Blo 1566981 1763059 := bstep (se 1 (by rfl) ⟨1322294, by rfl⟩ : syracuseStep 1763059 = 2644589) B2644589
theorem B2352899 : Blo 1566981 2352899 := bstep (se 1 (by rfl) ⟨1764674, by rfl⟩ : syracuseStep 2352899 = 3529349) B3529349
theorem B2352929 : Blo 1566981 2352929 := bstep (se 2 (by rfl) ⟨882348, by rfl⟩ : syracuseStep 2352929 = 1764697) B1764697
theorem B2352947 : Blo 1566981 2352947 := bstep (se 1 (by rfl) ⟨1764710, by rfl⟩ : syracuseStep 2352947 = 3529421) B3529421
theorem B2352977 : Blo 1566981 2352977 := bstep (se 2 (by rfl) ⟨882366, by rfl⟩ : syracuseStep 2352977 = 1764733) B1764733
theorem B2352995 : Blo 1566981 2352995 := bstep (se 1 (by rfl) ⟨1764746, by rfl⟩ : syracuseStep 2352995 = 3529493) B3529493
theorem B3966833 : Blo 1566981 3966833 := bstep (se 2 (by rfl) ⟨1487562, by rfl⟩ : syracuseStep 3966833 = 2975125) B2975125
theorem B8046449 : Blo 1566981 8046449 := bstep (se 2 (by rfl) ⟨3017418, by rfl⟩ : syracuseStep 8046449 = 6034837) B6034837
theorem B3180401 : Blo 1566981 3180401 := bstep (se 2 (by rfl) ⟨1192650, by rfl⟩ : syracuseStep 3180401 = 2385301) B2385301
theorem B2353025 : Blo 1566981 2353025 := bstep (se 2 (by rfl) ⟨882384, by rfl⟩ : syracuseStep 2353025 = 1764769) B1764769
theorem B1763203 : Blo 1566981 1763203 := bstep (se 1 (by rfl) ⟨1322402, by rfl⟩ : syracuseStep 1763203 = 2644805) B2644805
theorem B4466573 : Blo 1566981 4466573 := bstep (se 3 (by rfl) ⟨837482, by rfl⟩ : syracuseStep 4466573 = 1674965) B1674965
theorem B2353043 : Blo 1566981 2353043 := bstep (se 1 (by rfl) ⟨1764782, by rfl⟩ : syracuseStep 2353043 = 3529565) B3529565
theorem B5293997 : Blo 1566981 5293997 := bstep (se 3 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 5293997 = 1985249) B1985249
theorem B2353073 : Blo 1566981 2353073 := bstep (se 2 (by rfl) ⟨882402, by rfl⟩ : syracuseStep 2353073 = 1764805) B1764805
theorem B2353091 : Blo 1566981 2353091 := bstep (se 1 (by rfl) ⟨1764818, by rfl⟩ : syracuseStep 2353091 = 3529637) B3529637
theorem B2353121 : Blo 1566981 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B5294051 : Blo 1566981 5294051 := bstep (se 1 (by rfl) ⟨3970538, by rfl⟩ : syracuseStep 5294051 = 7941077) B7941077
theorem B2353139 : Blo 1566981 2353139 := bstep (se 1 (by rfl) ⟨1764854, by rfl⟩ : syracuseStep 2353139 = 3529709) B3529709
theorem B2353169 : Blo 1566981 2353169 := bstep (se 2 (by rfl) ⟨882438, by rfl⟩ : syracuseStep 2353169 = 1764877) B1764877
theorem B1763347 : Blo 1566981 1763347 := bstep (se 1 (by rfl) ⟨1322510, by rfl⟩ : syracuseStep 1763347 = 2645021) B2645021
theorem B2353187 : Blo 1566981 2353187 := bstep (se 1 (by rfl) ⟨1764890, by rfl⟩ : syracuseStep 2353187 = 3529781) B3529781
theorem B4769837 : Blo 1566981 4769837 := bstep (se 3 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 4769837 = 1788689) B1788689
theorem B2353217 : Blo 1566981 2353217 := bstep (se 2 (by rfl) ⟨882456, by rfl⟩ : syracuseStep 2353217 = 1764913) B1764913
theorem B4466765 : Blo 1566981 4466765 := bstep (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) B1675037
theorem B2353235 : Blo 1566981 2353235 := bstep (se 1 (by rfl) ⟨1764926, by rfl⟩ : syracuseStep 2353235 = 3529853) B3529853
theorem B2353265 : Blo 1566981 2353265 := bstep (se 2 (by rfl) ⟨882474, by rfl⟩ : syracuseStep 2353265 = 1764949) B1764949
theorem B2353283 : Blo 1566981 2353283 := bstep (se 1 (by rfl) ⟨1764962, by rfl⟩ : syracuseStep 2353283 = 3529925) B3529925
theorem B2353313 : Blo 1566981 2353313 := bstep (se 2 (by rfl) ⟨882492, by rfl⟩ : syracuseStep 2353313 = 1764985) B1764985
theorem B6695075 : Blo 1566981 6695075 := bstep (se 1 (by rfl) ⟨5021306, by rfl⟩ : syracuseStep 6695075 = 10042613) B10042613
theorem B1763491 : Blo 1566981 1763491 := bstep (se 1 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 1763491 = 2645237) B2645237
theorem B2353331 : Blo 1566981 2353331 := bstep (se 1 (by rfl) ⟨1764998, by rfl⟩ : syracuseStep 2353331 = 3529997) B3529997
theorem B2975953 : Blo 1566981 2975953 := bstep (se 2 (by rfl) ⟨1115982, by rfl⟩ : syracuseStep 2975953 = 2231965) B2231965
theorem B2353361 : Blo 1566981 2353361 := bstep (se 2 (by rfl) ⟨882510, by rfl⟩ : syracuseStep 2353361 = 1765021) B1765021
theorem B125634773 : Blo 1566981 125634773 := bstep (se 7 (by rfl) ⟨1472282, by rfl⟩ : syracuseStep 125634773 = 2944565) B2944565
theorem B2353379 : Blo 1566981 2353379 := bstep (se 1 (by rfl) ⟨1765034, by rfl⟩ : syracuseStep 2353379 = 3530069) B3530069
theorem B5294321 : Blo 1566981 5294321 := bstep (se 2 (by rfl) ⟨1985370, by rfl⟩ : syracuseStep 5294321 = 3970741) B3970741
theorem B2353409 : Blo 1566981 2353409 := bstep (se 2 (by rfl) ⟨882528, by rfl⟩ : syracuseStep 2353409 = 1765057) B1765057
theorem B1566995 : Blo 1566981 1566995 := bstep (se 1 (by rfl) ⟨1175246, by rfl⟩ : syracuseStep 1566995 = 2350493) B2350493
theorem B2353427 : Blo 1566981 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B1567011 : Blo 1566981 1567011 := bstep (se 1 (by rfl) ⟨1175258, by rfl⟩ : syracuseStep 1567011 = 2350517) B2350517
theorem B6785315 : Blo 1566981 6785315 := bstep (se 1 (by rfl) ⟨5088986, by rfl⟩ : syracuseStep 6785315 = 10177973) B10177973
theorem B5024035 : Blo 1566981 5024035 := bstep (se 1 (by rfl) ⟨3768026, by rfl⟩ : syracuseStep 5024035 = 7536053) B7536053
theorem B1567027 : Blo 1566981 1567027 := bstep (se 1 (by rfl) ⟨1175270, by rfl⟩ : syracuseStep 1567027 = 2350541) B2350541
theorem B1763635 : Blo 1566981 1763635 := bstep (se 1 (by rfl) ⟨1322726, by rfl⟩ : syracuseStep 1763635 = 2645453) B2645453
theorem B1984819 : Blo 1566981 1984819 := bstep (se 1 (by rfl) ⟨1488614, by rfl⟩ : syracuseStep 1984819 = 2977229) B2977229
theorem B2353457 : Blo 1566981 2353457 := bstep (se 2 (by rfl) ⟨882546, by rfl⟩ : syracuseStep 2353457 = 1765093) B1765093
theorem B1567043 : Blo 1566981 1567043 := bstep (se 1 (by rfl) ⟨1175282, by rfl⟩ : syracuseStep 1567043 = 2350565) B2350565
theorem B7940429 : Blo 1566981 7940429 := bstep (se 3 (by rfl) ⟨1488830, by rfl⟩ : syracuseStep 7940429 = 2977661) B2977661
theorem B1567059 : Blo 1566981 1567059 := bstep (se 1 (by rfl) ⟨1175294, by rfl⟩ : syracuseStep 1567059 = 2350589) B2350589
theorem B2263393 : Blo 1566981 2263393 := bstep (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) B1697545
theorem B1567075 : Blo 1566981 1567075 := bstep (se 1 (by rfl) ⟨1175306, by rfl⟩ : syracuseStep 1567075 = 2350613) B2350613
theorem B1567091 : Blo 1566981 1567091 := bstep (se 1 (by rfl) ⟨1175318, by rfl⟩ : syracuseStep 1567091 = 2350637) B2350637
theorem B1567107 : Blo 1566981 1567107 := bstep (se 1 (by rfl) ⟨1175330, by rfl⟩ : syracuseStep 1567107 = 2350661) B2350661
theorem B1567123 : Blo 1566981 1567123 := bstep (se 1 (by rfl) ⟨1175342, by rfl⟩ : syracuseStep 1567123 = 2350685) B2350685
theorem B1984915 : Blo 1566981 1984915 := bstep (se 1 (by rfl) ⟨1488686, by rfl⟩ : syracuseStep 1984915 = 2977373) B2977373
theorem B1567139 : Blo 1566981 1567139 := bstep (se 1 (by rfl) ⟨1175354, by rfl⟩ : syracuseStep 1567139 = 2350709) B2350709
theorem B5024177 : Blo 1566981 5024177 := bstep (se 2 (by rfl) ⟨1884066, by rfl⟩ : syracuseStep 5024177 = 3768133) B3768133
theorem B1567155 : Blo 1566981 1567155 := bstep (se 1 (by rfl) ⟨1175366, by rfl⟩ : syracuseStep 1567155 = 2350733) B2350733
theorem B1567171 : Blo 1566981 1567171 := bstep (se 1 (by rfl) ⟨1175378, by rfl⟩ : syracuseStep 1567171 = 2350757) B2350757
theorem B1763779 : Blo 1566981 1763779 := bstep (se 1 (by rfl) ⟨1322834, by rfl⟩ : syracuseStep 1763779 = 2645669) B2645669
theorem B1567187 : Blo 1566981 1567187 := bstep (se 1 (by rfl) ⟨1175390, by rfl⟩ : syracuseStep 1567187 = 2350781) B2350781
theorem B1567203 : Blo 1566981 1567203 := bstep (se 1 (by rfl) ⟨1175402, by rfl⟩ : syracuseStep 1567203 = 2350805) B2350805
theorem B1567219 : Blo 1566981 1567219 := bstep (se 1 (by rfl) ⟨1175414, by rfl⟩ : syracuseStep 1567219 = 2350829) B2350829
theorem B1567235 : Blo 1566981 1567235 := bstep (se 1 (by rfl) ⟨1175426, by rfl⟩ : syracuseStep 1567235 = 2350853) B2350853
theorem B1567251 : Blo 1566981 1567251 := bstep (se 1 (by rfl) ⟨1175438, by rfl⟩ : syracuseStep 1567251 = 2350877) B2350877
theorem B1567267 : Blo 1566981 1567267 := bstep (se 1 (by rfl) ⟨1175450, by rfl⟩ : syracuseStep 1567267 = 2350901) B2350901
theorem B1567283 : Blo 1566981 1567283 := bstep (se 1 (by rfl) ⟨1175462, by rfl⟩ : syracuseStep 1567283 = 2350925) B2350925
theorem B1567299 : Blo 1566981 1567299 := bstep (se 1 (by rfl) ⟨1175474, by rfl⟩ : syracuseStep 1567299 = 2350949) B2350949
theorem B1567315 : Blo 1566981 1567315 := bstep (se 1 (by rfl) ⟨1175486, by rfl⟩ : syracuseStep 1567315 = 2350973) B2350973
theorem B1763923 : Blo 1566981 1763923 := bstep (se 1 (by rfl) ⟨1322942, by rfl⟩ : syracuseStep 1763923 = 2645885) B2645885
theorem B1567331 : Blo 1566981 1567331 := bstep (se 1 (by rfl) ⟨1175498, by rfl⟩ : syracuseStep 1567331 = 2350997) B2350997
theorem B2976355 : Blo 1566981 2976355 := bstep (se 1 (by rfl) ⟨2232266, by rfl⟩ : syracuseStep 2976355 = 4464533) B4464533
theorem B1567347 : Blo 1566981 1567347 := bstep (se 1 (by rfl) ⟨1175510, by rfl⟩ : syracuseStep 1567347 = 2351021) B2351021
theorem B1567363 : Blo 1566981 1567363 := bstep (se 1 (by rfl) ⟨1175522, by rfl⟩ : syracuseStep 1567363 = 2351045) B2351045
theorem B2976401 : Blo 1566981 2976401 := bstep (se 2 (by rfl) ⟨1116150, by rfl⟩ : syracuseStep 2976401 = 2232301) B2232301
theorem B1567379 : Blo 1566981 1567379 := bstep (se 1 (by rfl) ⟨1175534, by rfl⟩ : syracuseStep 1567379 = 2351069) B2351069
theorem B1567395 : Blo 1566981 1567395 := bstep (se 1 (by rfl) ⟨1175546, by rfl⟩ : syracuseStep 1567395 = 2351093) B2351093
theorem B1567411 : Blo 1566981 1567411 := bstep (se 1 (by rfl) ⟨1175558, by rfl⟩ : syracuseStep 1567411 = 2351117) B2351117
theorem B1567427 : Blo 1566981 1567427 := bstep (se 1 (by rfl) ⟨1175570, by rfl⟩ : syracuseStep 1567427 = 2351141) B2351141
theorem B1567443 : Blo 1566981 1567443 := bstep (se 1 (by rfl) ⟨1175582, by rfl⟩ : syracuseStep 1567443 = 2351165) B2351165
theorem B1567459 : Blo 1566981 1567459 := bstep (se 1 (by rfl) ⟨1175594, by rfl⟩ : syracuseStep 1567459 = 2351189) B2351189
theorem B1764067 : Blo 1566981 1764067 := bstep (se 1 (by rfl) ⟨1323050, by rfl⟩ : syracuseStep 1764067 = 2646101) B2646101
theorem B67840739 : Blo 1566981 67840739 := bstep (se 1 (by rfl) ⟨50880554, by rfl⟩ : syracuseStep 67840739 = 101761109) B101761109
theorem B2755313 : Blo 1566981 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B1567475 : Blo 1566981 1567475 := bstep (se 1 (by rfl) ⟨1175606, by rfl⟩ : syracuseStep 1567475 = 2351213) B2351213
theorem B1567491 : Blo 1566981 1567491 := bstep (se 1 (by rfl) ⟨1175618, by rfl⟩ : syracuseStep 1567491 = 2351237) B2351237
theorem B5294861 : Blo 1566981 5294861 := bstep (se 3 (by rfl) ⟨992786, by rfl⟩ : syracuseStep 5294861 = 1985573) B1985573
theorem B1567507 : Blo 1566981 1567507 := bstep (se 1 (by rfl) ⟨1175630, by rfl⟩ : syracuseStep 1567507 = 2351261) B2351261
theorem B1567523 : Blo 1566981 1567523 := bstep (se 1 (by rfl) ⟨1175642, by rfl⟩ : syracuseStep 1567523 = 2351285) B2351285
theorem B1567539 : Blo 1566981 1567539 := bstep (se 1 (by rfl) ⟨1175654, by rfl⟩ : syracuseStep 1567539 = 2351309) B2351309
theorem B1567555 : Blo 1566981 1567555 := bstep (se 1 (by rfl) ⟨1175666, by rfl⟩ : syracuseStep 1567555 = 2351333) B2351333
theorem B5294915 : Blo 1566981 5294915 := bstep (se 1 (by rfl) ⟨3971186, by rfl⟩ : syracuseStep 5294915 = 7942373) B7942373
theorem B3967825 : Blo 1566981 3967825 := bstep (se 2 (by rfl) ⟨1487934, by rfl⟩ : syracuseStep 3967825 = 2975869) B2975869
theorem B1567571 : Blo 1566981 1567571 := bstep (se 1 (by rfl) ⟨1175678, by rfl⟩ : syracuseStep 1567571 = 2351357) B2351357
theorem B1567587 : Blo 1566981 1567587 := bstep (se 1 (by rfl) ⟨1175690, by rfl⟩ : syracuseStep 1567587 = 2351381) B2351381
theorem B1567603 : Blo 1566981 1567603 := bstep (se 1 (by rfl) ⟨1175702, by rfl⟩ : syracuseStep 1567603 = 2351405) B2351405
theorem B1764211 : Blo 1566981 1764211 := bstep (se 1 (by rfl) ⟨1323158, by rfl⟩ : syracuseStep 1764211 = 2646317) B2646317
theorem B1567619 : Blo 1566981 1567619 := bstep (se 1 (by rfl) ⟨1175714, by rfl⟩ : syracuseStep 1567619 = 2351429) B2351429
theorem B1985411 : Blo 1566981 1985411 := bstep (se 1 (by rfl) ⟨1489058, by rfl⟩ : syracuseStep 1985411 = 2978117) B2978117
theorem B1567635 : Blo 1566981 1567635 := bstep (se 1 (by rfl) ⟨1175726, by rfl⟩ : syracuseStep 1567635 = 2351453) B2351453
theorem B1567651 : Blo 1566981 1567651 := bstep (se 1 (by rfl) ⟨1175738, by rfl⟩ : syracuseStep 1567651 = 2351477) B2351477
theorem B2976689 : Blo 1566981 2976689 := bstep (se 2 (by rfl) ⟨1116258, by rfl⟩ : syracuseStep 2976689 = 2232517) B2232517
theorem B1567667 : Blo 1566981 1567667 := bstep (se 1 (by rfl) ⟨1175750, by rfl⟩ : syracuseStep 1567667 = 2351501) B2351501
theorem B1567683 : Blo 1566981 1567683 := bstep (se 1 (by rfl) ⟨1175762, by rfl⟩ : syracuseStep 1567683 = 2351525) B2351525
theorem B8932301 : Blo 1566981 8932301 := bstep (se 3 (by rfl) ⟨1674806, by rfl⟩ : syracuseStep 8932301 = 3349613) B3349613
theorem B1567699 : Blo 1566981 1567699 := bstep (se 1 (by rfl) ⟨1175774, by rfl⟩ : syracuseStep 1567699 = 2351549) B2351549
theorem B1567715 : Blo 1566981 1567715 := bstep (se 1 (by rfl) ⟨1175786, by rfl⟩ : syracuseStep 1567715 = 2351573) B2351573
theorem B1567731 : Blo 1566981 1567731 := bstep (se 1 (by rfl) ⟨1175798, by rfl⟩ : syracuseStep 1567731 = 2351597) B2351597
theorem B1567747 : Blo 1566981 1567747 := bstep (se 1 (by rfl) ⟨1175810, by rfl⟩ : syracuseStep 1567747 = 2351621) B2351621
theorem B1764355 : Blo 1566981 1764355 := bstep (se 1 (by rfl) ⟨1323266, by rfl⟩ : syracuseStep 1764355 = 2646533) B2646533
theorem B1567763 : Blo 1566981 1567763 := bstep (se 1 (by rfl) ⟨1175822, by rfl⟩ : syracuseStep 1567763 = 2351645) B2351645
theorem B1567779 : Blo 1566981 1567779 := bstep (se 1 (by rfl) ⟨1175834, by rfl⟩ : syracuseStep 1567779 = 2351669) B2351669
theorem B4238381 : Blo 1566981 4238381 := bstep (se 3 (by rfl) ⟨794696, by rfl⟩ : syracuseStep 4238381 = 1589393) B1589393
theorem B4467757 : Blo 1566981 4467757 := bstep (se 3 (by rfl) ⟨837704, by rfl⟩ : syracuseStep 4467757 = 1675409) B1675409
theorem B7932977 : Blo 1566981 7932977 := bstep (se 2 (by rfl) ⟨2974866, by rfl⟩ : syracuseStep 7932977 = 5949733) B5949733
theorem B1567795 : Blo 1566981 1567795 := bstep (se 1 (by rfl) ⟨1175846, by rfl⟩ : syracuseStep 1567795 = 2351693) B2351693
theorem B1567811 : Blo 1566981 1567811 := bstep (se 1 (by rfl) ⟨1175858, by rfl⟩ : syracuseStep 1567811 = 2351717) B2351717
theorem B3525713 : Blo 1566981 3525713 := bstep (se 2 (by rfl) ⟨1322142, by rfl⟩ : syracuseStep 3525713 = 2644285) B2644285
theorem B5295185 : Blo 1566981 5295185 := bstep (se 2 (by rfl) ⟨1985694, by rfl⟩ : syracuseStep 5295185 = 3971389) B3971389
theorem B1567827 : Blo 1566981 1567827 := bstep (se 1 (by rfl) ⟨1175870, by rfl⟩ : syracuseStep 1567827 = 2351741) B2351741
theorem B3525731 : Blo 1566981 3525731 := bstep (se 1 (by rfl) ⟨2644298, by rfl⟩ : syracuseStep 3525731 = 5288597) B5288597
theorem B3968099 : Blo 1566981 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B1567843 : Blo 1566981 1567843 := bstep (se 1 (by rfl) ⟨1175882, by rfl⟩ : syracuseStep 1567843 = 2351765) B2351765
theorem B1567859 : Blo 1566981 1567859 := bstep (se 1 (by rfl) ⟨1175894, by rfl⟩ : syracuseStep 1567859 = 2351789) B2351789
theorem B1567875 : Blo 1566981 1567875 := bstep (se 1 (by rfl) ⟨1175906, by rfl⟩ : syracuseStep 1567875 = 2351813) B2351813
theorem B1674371 : Blo 1566981 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B1567891 : Blo 1566981 1567891 := bstep (se 1 (by rfl) ⟨1175918, by rfl⟩ : syracuseStep 1567891 = 2351837) B2351837
theorem B1764499 : Blo 1566981 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B1567907 : Blo 1566981 1567907 := bstep (se 1 (by rfl) ⟨1175930, by rfl⟩ : syracuseStep 1567907 = 2351861) B2351861
theorem B4238513 : Blo 1566981 4238513 := bstep (se 2 (by rfl) ⟨1589442, by rfl⟩ : syracuseStep 4238513 = 3178885) B3178885
theorem B1567923 : Blo 1566981 1567923 := bstep (se 1 (by rfl) ⟨1175942, by rfl⟩ : syracuseStep 1567923 = 2351885) B2351885
theorem B1567939 : Blo 1566981 1567939 := bstep (se 1 (by rfl) ⟨1175954, by rfl⟩ : syracuseStep 1567939 = 2351909) B2351909
theorem B1567955 : Blo 1566981 1567955 := bstep (se 1 (by rfl) ⟨1175966, by rfl⟩ : syracuseStep 1567955 = 2351933) B2351933
theorem B5950691 : Blo 1566981 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B1567971 : Blo 1566981 1567971 := bstep (se 1 (by rfl) ⟨1175978, by rfl⟩ : syracuseStep 1567971 = 2351957) B2351957
theorem B5950705 : Blo 1566981 5950705 := bstep (se 2 (by rfl) ⟨2231514, by rfl⟩ : syracuseStep 5950705 = 4463029) B4463029
theorem B1567987 : Blo 1566981 1567987 := bstep (se 1 (by rfl) ⟨1175990, by rfl⟩ : syracuseStep 1567987 = 2351981) B2351981
theorem B1568003 : Blo 1566981 1568003 := bstep (se 1 (by rfl) ⟨1176002, by rfl⟩ : syracuseStep 1568003 = 2352005) B2352005
theorem B1568019 : Blo 1566981 1568019 := bstep (se 1 (by rfl) ⟨1176014, by rfl⟩ : syracuseStep 1568019 = 2352029) B2352029
theorem B3968291 : Blo 1566981 3968291 := bstep (se 1 (by rfl) ⟨2976218, by rfl⟩ : syracuseStep 3968291 = 5952437) B5952437
theorem B1568035 : Blo 1566981 1568035 := bstep (se 1 (by rfl) ⟨1176026, by rfl⟩ : syracuseStep 1568035 = 2352053) B2352053
theorem B1764643 : Blo 1566981 1764643 := bstep (se 1 (by rfl) ⟨1323482, by rfl⟩ : syracuseStep 1764643 = 2646965) B2646965
theorem B1568051 : Blo 1566981 1568051 := bstep (se 1 (by rfl) ⟨1176038, by rfl⟩ : syracuseStep 1568051 = 2352077) B2352077
theorem B1568067 : Blo 1566981 1568067 := bstep (se 1 (by rfl) ⟨1176050, by rfl⟩ : syracuseStep 1568067 = 2352101) B2352101
theorem B17861957 : Blo 1566981 17861957 := bstep (se 4 (by rfl) ⟨1674558, by rfl⟩ : syracuseStep 17861957 = 3349117) B3349117
theorem B1568083 : Blo 1566981 1568083 := bstep (se 1 (by rfl) ⟨1176062, by rfl⟩ : syracuseStep 1568083 = 2352125) B2352125
theorem B5647715 : Blo 1566981 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B1568099 : Blo 1566981 1568099 := bstep (se 1 (by rfl) ⟨1176074, by rfl⟩ : syracuseStep 1568099 = 2352149) B2352149
theorem B3526001 : Blo 1566981 3526001 := bstep (se 2 (by rfl) ⟨1322250, by rfl⟩ : syracuseStep 3526001 = 2644501) B2644501
theorem B1568115 : Blo 1566981 1568115 := bstep (se 1 (by rfl) ⟨1176086, by rfl⟩ : syracuseStep 1568115 = 2352173) B2352173
theorem B3526019 : Blo 1566981 3526019 := bstep (se 1 (by rfl) ⟨2644514, by rfl⟩ : syracuseStep 3526019 = 5289029) B5289029
theorem B1568131 : Blo 1566981 1568131 := bstep (se 1 (by rfl) ⟨1176098, by rfl⟩ : syracuseStep 1568131 = 2352197) B2352197
theorem B1568147 : Blo 1566981 1568147 := bstep (se 1 (by rfl) ⟨1176110, by rfl⟩ : syracuseStep 1568147 = 2352221) B2352221
theorem B8924579 : Blo 1566981 8924579 := bstep (se 1 (by rfl) ⟨6693434, by rfl⟩ : syracuseStep 8924579 = 13386869) B13386869
theorem B1568163 : Blo 1566981 1568163 := bstep (se 1 (by rfl) ⟨1176122, by rfl⟩ : syracuseStep 1568163 = 2352245) B2352245
theorem B1568179 : Blo 1566981 1568179 := bstep (se 1 (by rfl) ⟨1176134, by rfl⟩ : syracuseStep 1568179 = 2352269) B2352269
theorem B1764787 : Blo 1566981 1764787 := bstep (se 1 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 1764787 = 2647181) B2647181
theorem B1568195 : Blo 1566981 1568195 := bstep (se 1 (by rfl) ⟨1176146, by rfl⟩ : syracuseStep 1568195 = 2352293) B2352293
theorem B1568211 : Blo 1566981 1568211 := bstep (se 1 (by rfl) ⟨1176158, by rfl⟩ : syracuseStep 1568211 = 2352317) B2352317
theorem B1568227 : Blo 1566981 1568227 := bstep (se 1 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 1568227 = 2352341) B2352341
theorem B1568243 : Blo 1566981 1568243 := bstep (se 1 (by rfl) ⟨1176182, by rfl⟩ : syracuseStep 1568243 = 2352365) B2352365
theorem B1568259 : Blo 1566981 1568259 := bstep (se 1 (by rfl) ⟨1176194, by rfl⟩ : syracuseStep 1568259 = 2352389) B2352389
theorem B1568275 : Blo 1566981 1568275 := bstep (se 1 (by rfl) ⟨1176206, by rfl⟩ : syracuseStep 1568275 = 2352413) B2352413
theorem B8474147 : Blo 1566981 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B1568291 : Blo 1566981 1568291 := bstep (se 1 (by rfl) ⟨1176218, by rfl⟩ : syracuseStep 1568291 = 2352437) B2352437
theorem B1568307 : Blo 1566981 1568307 := bstep (se 1 (by rfl) ⟨1176230, by rfl⟩ : syracuseStep 1568307 = 2352461) B2352461
theorem B1568323 : Blo 1566981 1568323 := bstep (se 1 (by rfl) ⟨1176242, by rfl⟩ : syracuseStep 1568323 = 2352485) B2352485
theorem B1764931 : Blo 1566981 1764931 := bstep (se 1 (by rfl) ⟨1323698, by rfl⟩ : syracuseStep 1764931 = 2647397) B2647397
theorem B1568339 : Blo 1566981 1568339 := bstep (se 1 (by rfl) ⟨1176254, by rfl⟩ : syracuseStep 1568339 = 2352509) B2352509
theorem B7532131 : Blo 1566981 7532131 := bstep (se 1 (by rfl) ⟨5649098, by rfl⟩ : syracuseStep 7532131 = 11298197) B11298197
theorem B1568355 : Blo 1566981 1568355 := bstep (se 1 (by rfl) ⟨1176266, by rfl⟩ : syracuseStep 1568355 = 2352533) B2352533
theorem B1568371 : Blo 1566981 1568371 := bstep (se 1 (by rfl) ⟨1176278, by rfl⟩ : syracuseStep 1568371 = 2352557) B2352557
theorem B2977411 : Blo 1566981 2977411 := bstep (se 1 (by rfl) ⟨2233058, by rfl⟩ : syracuseStep 2977411 = 4466117) B4466117
theorem B1568387 : Blo 1566981 1568387 := bstep (se 1 (by rfl) ⟨1176290, by rfl⟩ : syracuseStep 1568387 = 2352581) B2352581
theorem B3526289 : Blo 1566981 3526289 := bstep (se 2 (by rfl) ⟨1322358, by rfl⟩ : syracuseStep 3526289 = 2644717) B2644717
theorem B1568403 : Blo 1566981 1568403 := bstep (se 1 (by rfl) ⟨1176302, by rfl⟩ : syracuseStep 1568403 = 2352605) B2352605
theorem B3526307 : Blo 1566981 3526307 := bstep (se 1 (by rfl) ⟨2644730, by rfl⟩ : syracuseStep 3526307 = 5289461) B5289461
theorem B1568419 : Blo 1566981 1568419 := bstep (se 1 (by rfl) ⟨1176314, by rfl⟩ : syracuseStep 1568419 = 2352629) B2352629
theorem B1568435 : Blo 1566981 1568435 := bstep (se 1 (by rfl) ⟨1176326, by rfl⟩ : syracuseStep 1568435 = 2352653) B2352653
theorem B1568451 : Blo 1566981 1568451 := bstep (se 1 (by rfl) ⟨1176338, by rfl⟩ : syracuseStep 1568451 = 2352677) B2352677
theorem B1568467 : Blo 1566981 1568467 := bstep (se 1 (by rfl) ⟨1176350, by rfl⟩ : syracuseStep 1568467 = 2352701) B2352701
theorem B1765075 : Blo 1566981 1765075 := bstep (se 1 (by rfl) ⟨1323806, by rfl⟩ : syracuseStep 1765075 = 2647613) B2647613
theorem B9531107 : Blo 1566981 9531107 := bstep (se 1 (by rfl) ⟨7148330, by rfl⟩ : syracuseStep 9531107 = 14296661) B14296661
theorem B2682595 : Blo 1566981 2682595 := bstep (se 1 (by rfl) ⟨2011946, by rfl⟩ : syracuseStep 2682595 = 4023893) B4023893
theorem B1568483 : Blo 1566981 1568483 := bstep (se 1 (by rfl) ⟨1176362, by rfl⟩ : syracuseStep 1568483 = 2352725) B2352725
theorem B5025521 : Blo 1566981 5025521 := bstep (se 2 (by rfl) ⟨1884570, by rfl⟩ : syracuseStep 5025521 = 3769141) B3769141
theorem B1568499 : Blo 1566981 1568499 := bstep (se 1 (by rfl) ⟨1176374, by rfl⟩ : syracuseStep 1568499 = 2352749) B2352749
theorem B1568515 : Blo 1566981 1568515 := bstep (se 1 (by rfl) ⟨1176386, by rfl⟩ : syracuseStep 1568515 = 2352773) B2352773
theorem B1568531 : Blo 1566981 1568531 := bstep (se 1 (by rfl) ⟨1176398, by rfl⟩ : syracuseStep 1568531 = 2352797) B2352797
theorem B1568547 : Blo 1566981 1568547 := bstep (se 1 (by rfl) ⟨1176410, by rfl⟩ : syracuseStep 1568547 = 2352821) B2352821
theorem B1568563 : Blo 1566981 1568563 := bstep (se 1 (by rfl) ⟨1176422, by rfl⟩ : syracuseStep 1568563 = 2352845) B2352845
theorem B2510659 : Blo 1566981 2510659 := bstep (se 1 (by rfl) ⟨1882994, by rfl⟩ : syracuseStep 2510659 = 3765989) B3765989
theorem B1568579 : Blo 1566981 1568579 := bstep (se 1 (by rfl) ⟨1176434, by rfl⟩ : syracuseStep 1568579 = 2352869) B2352869
theorem B1568595 : Blo 1566981 1568595 := bstep (se 1 (by rfl) ⟨1176446, by rfl⟩ : syracuseStep 1568595 = 2352893) B2352893
theorem B1568611 : Blo 1566981 1568611 := bstep (se 1 (by rfl) ⟨1176458, by rfl⟩ : syracuseStep 1568611 = 2352917) B2352917
theorem B17870705 : Blo 1566981 17870705 := bstep (se 2 (by rfl) ⟨6701514, by rfl⟩ : syracuseStep 17870705 = 13403029) B13403029
theorem B1568627 : Blo 1566981 1568627 := bstep (se 1 (by rfl) ⟨1176470, by rfl⟩ : syracuseStep 1568627 = 2352941) B2352941
theorem B2232193 : Blo 1566981 2232193 := bstep (se 2 (by rfl) ⟨837072, by rfl⟩ : syracuseStep 2232193 = 1674145) B1674145
theorem B1568643 : Blo 1566981 1568643 := bstep (se 1 (by rfl) ⟨1176482, by rfl⟩ : syracuseStep 1568643 = 2352965) B2352965
theorem B1568659 : Blo 1566981 1568659 := bstep (se 1 (by rfl) ⟨1176494, by rfl⟩ : syracuseStep 1568659 = 2352989) B2352989
theorem B1568675 : Blo 1566981 1568675 := bstep (se 1 (by rfl) ⟨1176506, by rfl⟩ : syracuseStep 1568675 = 2353013) B2353013
theorem B3526577 : Blo 1566981 3526577 := bstep (se 2 (by rfl) ⟨1322466, by rfl⟩ : syracuseStep 3526577 = 2644933) B2644933
theorem B1568691 : Blo 1566981 1568691 := bstep (se 1 (by rfl) ⟨1176518, by rfl⟩ : syracuseStep 1568691 = 2353037) B2353037
theorem B3526595 : Blo 1566981 3526595 := bstep (se 1 (by rfl) ⟨2644946, by rfl⟩ : syracuseStep 3526595 = 5289893) B5289893
theorem B1568707 : Blo 1566981 1568707 := bstep (se 1 (by rfl) ⟨1176530, by rfl⟩ : syracuseStep 1568707 = 2353061) B2353061
theorem B1568723 : Blo 1566981 1568723 := bstep (se 1 (by rfl) ⟨1176542, by rfl⟩ : syracuseStep 1568723 = 2353085) B2353085
theorem B2232289 : Blo 1566981 2232289 := bstep (se 2 (by rfl) ⟨837108, by rfl⟩ : syracuseStep 2232289 = 1674217) B1674217
theorem B1568739 : Blo 1566981 1568739 := bstep (se 1 (by rfl) ⟨1176554, by rfl⟩ : syracuseStep 1568739 = 2353109) B2353109
theorem B14307313 : Blo 1566981 14307313 := bstep (se 2 (by rfl) ⟨5365242, by rfl⟩ : syracuseStep 14307313 = 10730485) B10730485
theorem B1568755 : Blo 1566981 1568755 := bstep (se 1 (by rfl) ⟨1176566, by rfl⟩ : syracuseStep 1568755 = 2353133) B2353133
theorem B1568771 : Blo 1566981 1568771 := bstep (se 1 (by rfl) ⟨1176578, by rfl⟩ : syracuseStep 1568771 = 2353157) B2353157
theorem B1568787 : Blo 1566981 1568787 := bstep (se 1 (by rfl) ⟨1176590, by rfl⟩ : syracuseStep 1568787 = 2353181) B2353181
theorem B3575843 : Blo 1566981 3575843 := bstep (se 1 (by rfl) ⟨2681882, by rfl⟩ : syracuseStep 3575843 = 5363765) B5363765
theorem B1568803 : Blo 1566981 1568803 := bstep (se 1 (by rfl) ⟨1176602, by rfl⟩ : syracuseStep 1568803 = 2353205) B2353205
theorem B1568819 : Blo 1566981 1568819 := bstep (se 1 (by rfl) ⟨1176614, by rfl⟩ : syracuseStep 1568819 = 2353229) B2353229
theorem B2977859 : Blo 1566981 2977859 := bstep (se 1 (by rfl) ⟨2233394, by rfl⟩ : syracuseStep 2977859 = 4466789) B4466789
theorem B10047557 : Blo 1566981 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B1568835 : Blo 1566981 1568835 := bstep (se 1 (by rfl) ⟨1176626, by rfl⟩ : syracuseStep 1568835 = 2353253) B2353253
theorem B2510929 : Blo 1566981 2510929 := bstep (se 2 (by rfl) ⟨941598, by rfl⟩ : syracuseStep 2510929 = 1883197) B1883197
theorem B1568851 : Blo 1566981 1568851 := bstep (se 1 (by rfl) ⟨1176638, by rfl⟩ : syracuseStep 1568851 = 2353277) B2353277
theorem B1568867 : Blo 1566981 1568867 := bstep (se 1 (by rfl) ⟨1176650, by rfl⟩ : syracuseStep 1568867 = 2353301) B2353301
theorem B6697073 : Blo 1566981 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B1568883 : Blo 1566981 1568883 := bstep (se 1 (by rfl) ⟨1176662, by rfl⟩ : syracuseStep 1568883 = 2353325) B2353325
theorem B1568899 : Blo 1566981 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B2510993 : Blo 1566981 2510993 := bstep (se 2 (by rfl) ⟨941622, by rfl⟩ : syracuseStep 2510993 = 1883245) B1883245
theorem B1568915 : Blo 1566981 1568915 := bstep (se 1 (by rfl) ⟨1176686, by rfl⟩ : syracuseStep 1568915 = 2353373) B2353373
theorem B5091491 : Blo 1566981 5091491 := bstep (se 1 (by rfl) ⟨3818618, by rfl⟩ : syracuseStep 5091491 = 7637237) B7637237
theorem B1568931 : Blo 1566981 1568931 := bstep (se 1 (by rfl) ⟨1176698, by rfl⟩ : syracuseStep 1568931 = 2353397) B2353397
theorem B1568947 : Blo 1566981 1568947 := bstep (se 1 (by rfl) ⟨1176710, by rfl⟩ : syracuseStep 1568947 = 2353421) B2353421
theorem B1568963 : Blo 1566981 1568963 := bstep (se 1 (by rfl) ⟨1176722, by rfl⟩ : syracuseStep 1568963 = 2353445) B2353445
theorem B3526865 : Blo 1566981 3526865 := bstep (se 2 (by rfl) ⟨1322574, by rfl⟩ : syracuseStep 3526865 = 2645149) B2645149
theorem B3969233 : Blo 1566981 3969233 := bstep (se 2 (by rfl) ⟨1488462, by rfl⟩ : syracuseStep 3969233 = 2976925) B2976925
theorem B1568979 : Blo 1566981 1568979 := bstep (se 1 (by rfl) ⟨1176734, by rfl⟩ : syracuseStep 1568979 = 2353469) B2353469
theorem B3526883 : Blo 1566981 3526883 := bstep (se 1 (by rfl) ⟨2645162, by rfl⟩ : syracuseStep 3526883 = 5290325) B5290325
theorem B3969283 : Blo 1566981 3969283 := bstep (se 1 (by rfl) ⟨2976962, by rfl⟩ : syracuseStep 3969283 = 5953925) B5953925
theorem B6787405 : Blo 1566981 6787405 := bstep (se 3 (by rfl) ⟨1272638, by rfl⟩ : syracuseStep 6787405 = 2545277) B2545277
theorem B2978147 : Blo 1566981 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B3969425 : Blo 1566981 3969425 := bstep (se 2 (by rfl) ⟨1488534, by rfl⟩ : syracuseStep 3969425 = 2977069) B2977069
theorem B2232785 : Blo 1566981 2232785 := bstep (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) B1674589
theorem B7934435 : Blo 1566981 7934435 := bstep (se 1 (by rfl) ⟨5950826, by rfl⟩ : syracuseStep 7934435 = 11901653) B11901653
theorem B3527153 : Blo 1566981 3527153 := bstep (se 2 (by rfl) ⟨1322682, by rfl⟩ : syracuseStep 3527153 = 2645365) B2645365
theorem B3527171 : Blo 1566981 3527171 := bstep (se 1 (by rfl) ⟨2645378, by rfl⟩ : syracuseStep 3527171 = 5290757) B5290757
theorem B5952163 : Blo 1566981 5952163 := bstep (se 1 (by rfl) ⟨4464122, by rfl⟩ : syracuseStep 5952163 = 8928245) B8928245
theorem B3347153 : Blo 1566981 3347153 := bstep (se 2 (by rfl) ⟨1255182, by rfl⟩ : syracuseStep 3347153 = 2510365) B2510365
theorem B3527441 : Blo 1566981 3527441 := bstep (se 2 (by rfl) ⟨1322790, by rfl⟩ : syracuseStep 3527441 = 2645581) B2645581
theorem B3527459 : Blo 1566981 3527459 := bstep (se 1 (by rfl) ⟨2645594, by rfl⟩ : syracuseStep 3527459 = 5291189) B5291189
theorem B3576611 : Blo 1566981 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B7533361 : Blo 1566981 7533361 := bstep (se 2 (by rfl) ⟨2825010, by rfl⟩ : syracuseStep 7533361 = 5650021) B5650021
theorem B30143285 : Blo 1566981 30143285 := bstep (se 5 (by rfl) ⟨1412966, by rfl⟩ : syracuseStep 30143285 = 2825933) B2825933
theorem B5288813 : Blo 1566981 5288813 := bstep (se 3 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 5288813 = 1983305) B1983305
theorem B15078257 : Blo 1566981 15078257 := bstep (se 2 (by rfl) ⟨5654346, by rfl⟩ : syracuseStep 15078257 = 11308693) B11308693
theorem B5288867 : Blo 1566981 5288867 := bstep (se 1 (by rfl) ⟨3966650, by rfl⟩ : syracuseStep 5288867 = 7933301) B7933301
theorem B5649329 : Blo 1566981 5649329 := bstep (se 2 (by rfl) ⟨2118498, by rfl⟩ : syracuseStep 5649329 = 4236997) B4236997
theorem B6697997 : Blo 1566981 6697997 := bstep (se 3 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 6697997 = 2511749) B2511749
theorem B3527729 : Blo 1566981 3527729 := bstep (se 2 (by rfl) ⟨1322898, by rfl⟩ : syracuseStep 3527729 = 2645797) B2645797
theorem B3527747 : Blo 1566981 3527747 := bstep (se 1 (by rfl) ⟨2645810, by rfl⟩ : syracuseStep 3527747 = 5291621) B5291621
theorem B8934533 : Blo 1566981 8934533 := bstep (se 4 (by rfl) ⟨837612, by rfl⟩ : syracuseStep 8934533 = 1675225) B1675225
theorem B5289137 : Blo 1566981 5289137 := bstep (se 2 (by rfl) ⟨1983426, by rfl⟩ : syracuseStep 5289137 = 3966853) B3966853
theorem B2118883 : Blo 1566981 2118883 := bstep (se 1 (by rfl) ⟨1589162, by rfl⟩ : syracuseStep 2118883 = 3178325) B3178325
theorem B4527341 : Blo 1566981 4527341 := bstep (se 3 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 4527341 = 1697753) B1697753
theorem B8926469 : Blo 1566981 8926469 := bstep (se 4 (by rfl) ⟨836856, by rfl⟩ : syracuseStep 8926469 = 1673713) B1673713
theorem B7935245 : Blo 1566981 7935245 := bstep (se 3 (by rfl) ⟨1487858, by rfl⟩ : syracuseStep 7935245 = 2975717) B2975717
theorem B2233651 : Blo 1566981 2233651 := bstep (se 1 (by rfl) ⟨1675238, by rfl⟩ : syracuseStep 2233651 = 3350477) B3350477
theorem B3528017 : Blo 1566981 3528017 := bstep (se 2 (by rfl) ⟨1323006, by rfl⟩ : syracuseStep 3528017 = 2646013) B2646013
theorem B3528035 : Blo 1566981 3528035 := bstep (se 1 (by rfl) ⟨2646026, by rfl⟩ : syracuseStep 3528035 = 5292053) B5292053
theorem B3970417 : Blo 1566981 3970417 := bstep (se 2 (by rfl) ⟨1488906, by rfl⟩ : syracuseStep 3970417 = 2977813) B2977813
theorem B15078797 : Blo 1566981 15078797 := bstep (se 3 (by rfl) ⟨2827274, by rfl⟩ : syracuseStep 15078797 = 5654549) B5654549
theorem B2233747 : Blo 1566981 2233747 := bstep (se 1 (by rfl) ⟨1675310, by rfl⟩ : syracuseStep 2233747 = 3350621) B3350621
theorem B4527523 : Blo 1566981 4527523 := bstep (se 1 (by rfl) ⟨3395642, by rfl⟩ : syracuseStep 4527523 = 6791285) B6791285
theorem B3765827 : Blo 1566981 3765827 := bstep (se 1 (by rfl) ⟨2824370, by rfl⟩ : syracuseStep 3765827 = 5648741) B5648741
theorem B3528305 : Blo 1566981 3528305 := bstep (se 2 (by rfl) ⟨1323114, by rfl⟩ : syracuseStep 3528305 = 2646229) B2646229
theorem B3528323 : Blo 1566981 3528323 := bstep (se 1 (by rfl) ⟨2646242, by rfl⟩ : syracuseStep 3528323 = 5292485) B5292485
theorem B3970691 : Blo 1566981 3970691 := bstep (se 1 (by rfl) ⟨2978018, by rfl⟩ : syracuseStep 3970691 = 5956037) B5956037
theorem B2717363 : Blo 1566981 2717363 := bstep (se 1 (by rfl) ⟨2038022, by rfl⟩ : syracuseStep 2717363 = 4076045) B4076045
theorem B5289677 : Blo 1566981 5289677 := bstep (se 3 (by rfl) ⟨991814, by rfl⟩ : syracuseStep 5289677 = 1983629) B1983629
theorem B5289731 : Blo 1566981 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B8935217 : Blo 1566981 8935217 := bstep (se 2 (by rfl) ⟨3350706, by rfl⟩ : syracuseStep 8935217 = 6701413) B6701413
theorem B3970883 : Blo 1566981 3970883 := bstep (se 1 (by rfl) ⟨2978162, by rfl⟩ : syracuseStep 3970883 = 5956325) B5956325
theorem B2512723 : Blo 1566981 2512723 := bstep (se 1 (by rfl) ⟨1884542, by rfl⟩ : syracuseStep 2512723 = 3769085) B3769085
theorem B2545537 : Blo 1566981 2545537 := bstep (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) B1909153
theorem B3528593 : Blo 1566981 3528593 := bstep (se 2 (by rfl) ⟨1323222, by rfl⟩ : syracuseStep 3528593 = 2646445) B2646445
theorem B3528611 : Blo 1566981 3528611 := bstep (se 1 (by rfl) ⟨2646458, by rfl⟩ : syracuseStep 3528611 = 5292917) B5292917
theorem B10049507 : Blo 1566981 10049507 := bstep (se 1 (by rfl) ⟨7537130, by rfl⟩ : syracuseStep 10049507 = 15074261) B15074261
theorem B5290001 : Blo 1566981 5290001 := bstep (se 2 (by rfl) ⟨1983750, by rfl⟩ : syracuseStep 5290001 = 3967501) B3967501
theorem B3528881 : Blo 1566981 3528881 := bstep (se 2 (by rfl) ⟨1323330, by rfl⟩ : syracuseStep 3528881 = 2646661) B2646661
theorem B3528899 : Blo 1566981 3528899 := bstep (se 1 (by rfl) ⟨2646674, by rfl⟩ : syracuseStep 3528899 = 5293349) B5293349
theorem B3348707 : Blo 1566981 3348707 := bstep (se 1 (by rfl) ⟨2511530, by rfl⟩ : syracuseStep 3348707 = 5023061) B5023061
theorem B2513171 : Blo 1566981 2513171 := bstep (se 1 (by rfl) ⟨1884878, by rfl⟩ : syracuseStep 2513171 = 3769757) B3769757
theorem B7534883 : Blo 1566981 7534883 := bstep (se 1 (by rfl) ⟨5651162, by rfl⟩ : syracuseStep 7534883 = 11302325) B11302325
theorem B2120035 : Blo 1566981 2120035 := bstep (se 1 (by rfl) ⟨1590026, by rfl⟩ : syracuseStep 2120035 = 3180053) B3180053
theorem B2644339 : Blo 1566981 2644339 := bstep (se 1 (by rfl) ⟨1983254, by rfl⟩ : syracuseStep 2644339 = 3966509) B3966509
theorem B2824579 : Blo 1566981 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B2120099 : Blo 1566981 2120099 := bstep (se 1 (by rfl) ⟨1590074, by rfl⟩ : syracuseStep 2120099 = 3180149) B3180149
theorem B3529169 : Blo 1566981 3529169 := bstep (se 2 (by rfl) ⟨1323438, by rfl⟩ : syracuseStep 3529169 = 2646877) B2646877
theorem B4463075 : Blo 1566981 4463075 := bstep (se 1 (by rfl) ⟨3347306, by rfl⟩ : syracuseStep 4463075 = 6694613) B6694613
theorem B3529187 : Blo 1566981 3529187 := bstep (se 1 (by rfl) ⟨2646890, by rfl⟩ : syracuseStep 3529187 = 5293781) B5293781
theorem B13572593 : Blo 1566981 13572593 := bstep (se 2 (by rfl) ⟨5089722, by rfl⟩ : syracuseStep 13572593 = 10179445) B10179445
theorem B2644481 : Blo 1566981 2644481 := bstep (se 2 (by rfl) ⟨991680, by rfl⟩ : syracuseStep 2644481 = 1983361) B1983361
theorem B5290541 : Blo 1566981 5290541 := bstep (se 3 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 5290541 = 1983953) B1983953
theorem B5290595 : Blo 1566981 5290595 := bstep (se 1 (by rfl) ⟨3967946, by rfl⟩ : syracuseStep 5290595 = 7935893) B7935893
theorem B2644609 : Blo 1566981 2644609 := bstep (se 2 (by rfl) ⟨991728, by rfl⟩ : syracuseStep 2644609 = 1983457) B1983457
theorem B2644643 : Blo 1566981 2644643 := bstep (se 1 (by rfl) ⟨1983482, by rfl⟩ : syracuseStep 2644643 = 3966965) B3966965
theorem B5806819 : Blo 1566981 5806819 := bstep (se 1 (by rfl) ⟨4355114, by rfl⟩ : syracuseStep 5806819 = 8710229) B8710229
theorem B16947953 : Blo 1566981 16947953 := bstep (se 2 (by rfl) ⟨6355482, by rfl⟩ : syracuseStep 16947953 = 12710965) B12710965
theorem B3529457 : Blo 1566981 3529457 := bstep (se 2 (by rfl) ⟨1323546, by rfl⟩ : syracuseStep 3529457 = 2647093) B2647093
theorem B3529475 : Blo 1566981 3529475 := bstep (se 1 (by rfl) ⟨2647106, by rfl⟩ : syracuseStep 3529475 = 5294213) B5294213
theorem B3767057 : Blo 1566981 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2644771 : Blo 1566981 2644771 := bstep (se 1 (by rfl) ⟨1983578, by rfl⟩ : syracuseStep 2644771 = 3967157) B3967157
theorem B2382643 : Blo 1566981 2382643 := bstep (se 1 (by rfl) ⟨1786982, by rfl⟩ : syracuseStep 2382643 = 3573965) B3573965
theorem B5954381 : Blo 1566981 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B5290865 : Blo 1566981 5290865 := bstep (se 2 (by rfl) ⟨1984074, by rfl⟩ : syracuseStep 5290865 = 3968149) B3968149
theorem B2644913 : Blo 1566981 2644913 := bstep (se 2 (by rfl) ⟨991842, by rfl⟩ : syracuseStep 2644913 = 1983685) B1983685
theorem B2382851 : Blo 1566981 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B3529745 : Blo 1566981 3529745 := bstep (se 2 (by rfl) ⟨1323654, by rfl⟩ : syracuseStep 3529745 = 2647309) B2647309
theorem B3529763 : Blo 1566981 3529763 := bstep (se 1 (by rfl) ⟨2647322, by rfl⟩ : syracuseStep 3529763 = 5294645) B5294645
theorem B2645041 : Blo 1566981 2645041 := bstep (se 2 (by rfl) ⟨991890, by rfl⟩ : syracuseStep 2645041 = 1983781) B1983781
theorem B2645075 : Blo 1566981 2645075 := bstep (se 1 (by rfl) ⟨1983806, by rfl⟩ : syracuseStep 2645075 = 3967613) B3967613
theorem B3177571 : Blo 1566981 3177571 := bstep (se 1 (by rfl) ⟨2383178, by rfl⟩ : syracuseStep 3177571 = 4766357) B4766357
theorem B2645203 : Blo 1566981 2645203 := bstep (se 1 (by rfl) ⟨1983902, by rfl⟩ : syracuseStep 2645203 = 3967805) B3967805
theorem B21445859 : Blo 1566981 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B3530033 : Blo 1566981 3530033 := bstep (se 2 (by rfl) ⟨1323762, by rfl⟩ : syracuseStep 3530033 = 2647525) B2647525
theorem B3530051 : Blo 1566981 3530051 := bstep (se 1 (by rfl) ⟨2647538, by rfl⟩ : syracuseStep 3530051 = 5295077) B5295077
theorem B2645345 : Blo 1566981 2645345 := bstep (se 2 (by rfl) ⟨992004, by rfl⟩ : syracuseStep 2645345 = 1984009) B1984009
theorem B5291405 : Blo 1566981 5291405 := bstep (se 3 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 5291405 = 1984277) B1984277
theorem B2350481 : Blo 1566981 2350481 := bstep (se 2 (by rfl) ⟨881430, by rfl⟩ : syracuseStep 2350481 = 1762861) B1762861
theorem B2350499 : Blo 1566981 2350499 := bstep (se 1 (by rfl) ⟨1762874, by rfl⟩ : syracuseStep 2350499 = 3525749) B3525749
theorem B2350529 : Blo 1566981 2350529 := bstep (se 2 (by rfl) ⟨881448, by rfl⟩ : syracuseStep 2350529 = 1762897) B1762897
theorem B5291459 : Blo 1566981 5291459 := bstep (se 1 (by rfl) ⟨3968594, by rfl⟩ : syracuseStep 5291459 = 7937189) B7937189
theorem B57187781 : Blo 1566981 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B2350547 : Blo 1566981 2350547 := bstep (se 1 (by rfl) ⟨1762910, by rfl⟩ : syracuseStep 2350547 = 3525821) B3525821
theorem B2645473 : Blo 1566981 2645473 := bstep (se 2 (by rfl) ⟨992052, by rfl⟩ : syracuseStep 2645473 = 1984105) B1984105
theorem B5021165 : Blo 1566981 5021165 := bstep (se 3 (by rfl) ⟨941468, by rfl⟩ : syracuseStep 5021165 = 1882937) B1882937
theorem B2350577 : Blo 1566981 2350577 := bstep (se 2 (by rfl) ⟨881466, by rfl⟩ : syracuseStep 2350577 = 1762933) B1762933
theorem B2383361 : Blo 1566981 2383361 := bstep (se 2 (by rfl) ⟨893760, by rfl⟩ : syracuseStep 2383361 = 1787521) B1787521
theorem B2350595 : Blo 1566981 2350595 := bstep (se 1 (by rfl) ⟨1762946, by rfl⟩ : syracuseStep 2350595 = 3525893) B3525893
theorem B2645507 : Blo 1566981 2645507 := bstep (se 1 (by rfl) ⟨1984130, by rfl⟩ : syracuseStep 2645507 = 3968261) B3968261
theorem B12066317 : Blo 1566981 12066317 := bstep (se 3 (by rfl) ⟨2262434, by rfl⟩ : syracuseStep 12066317 = 4524869) B4524869
theorem B2350625 : Blo 1566981 2350625 := bstep (se 2 (by rfl) ⟨881484, by rfl⟩ : syracuseStep 2350625 = 1762969) B1762969
theorem B2383409 : Blo 1566981 2383409 := bstep (se 2 (by rfl) ⟨893778, by rfl⟩ : syracuseStep 2383409 = 1787557) B1787557
theorem B2350643 : Blo 1566981 2350643 := bstep (se 1 (by rfl) ⟨1762982, by rfl⟩ : syracuseStep 2350643 = 3525965) B3525965
theorem B2350673 : Blo 1566981 2350673 := bstep (se 2 (by rfl) ⟨881502, by rfl⟩ : syracuseStep 2350673 = 1763005) B1763005
theorem B2350691 : Blo 1566981 2350691 := bstep (se 1 (by rfl) ⟨1763018, by rfl⟩ : syracuseStep 2350691 = 3526037) B3526037
theorem B2350721 : Blo 1566981 2350721 := bstep (se 2 (by rfl) ⟨881520, by rfl⟩ : syracuseStep 2350721 = 1763041) B1763041
theorem B2645635 : Blo 1566981 2645635 := bstep (se 1 (by rfl) ⟨1984226, by rfl⟩ : syracuseStep 2645635 = 3968453) B3968453
theorem B2350739 : Blo 1566981 2350739 := bstep (se 1 (by rfl) ⟨1763054, by rfl⟩ : syracuseStep 2350739 = 3526109) B3526109
theorem B2350769 : Blo 1566981 2350769 := bstep (se 2 (by rfl) ⟨881538, by rfl⟩ : syracuseStep 2350769 = 1763077) B1763077
theorem B4464305 : Blo 1566981 4464305 := bstep (se 2 (by rfl) ⟨1674114, by rfl⟩ : syracuseStep 4464305 = 3348229) B3348229
theorem B2350787 : Blo 1566981 2350787 := bstep (se 1 (by rfl) ⟨1763090, by rfl⟩ : syracuseStep 2350787 = 3526181) B3526181
theorem B5291729 : Blo 1566981 5291729 := bstep (se 2 (by rfl) ⟨1984398, by rfl⟩ : syracuseStep 5291729 = 3968797) B3968797
theorem B2350817 : Blo 1566981 2350817 := bstep (se 2 (by rfl) ⟨881556, by rfl⟩ : syracuseStep 2350817 = 1763113) B1763113
theorem B10723043 : Blo 1566981 10723043 := bstep (se 1 (by rfl) ⟨8042282, by rfl⟩ : syracuseStep 10723043 = 16084565) B16084565
theorem B32202467 : Blo 1566981 32202467 := bstep (se 1 (by rfl) ⟨24151850, by rfl⟩ : syracuseStep 32202467 = 48303701) B48303701
theorem B2350835 : Blo 1566981 2350835 := bstep (se 1 (by rfl) ⟨1763126, by rfl⟩ : syracuseStep 2350835 = 3526253) B3526253
theorem B10043149 : Blo 1566981 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B2350865 : Blo 1566981 2350865 := bstep (se 2 (by rfl) ⟨881574, by rfl⟩ : syracuseStep 2350865 = 1763149) B1763149
theorem B2645777 : Blo 1566981 2645777 := bstep (se 2 (by rfl) ⟨992166, by rfl⟩ : syracuseStep 2645777 = 1984333) B1984333
theorem B2350883 : Blo 1566981 2350883 := bstep (se 1 (by rfl) ⟨1763162, by rfl⟩ : syracuseStep 2350883 = 3526325) B3526325
theorem B2350913 : Blo 1566981 2350913 := bstep (se 2 (by rfl) ⟨881592, by rfl⟩ : syracuseStep 2350913 = 1763185) B1763185
theorem B2350931 : Blo 1566981 2350931 := bstep (se 1 (by rfl) ⟨1763198, by rfl⟩ : syracuseStep 2350931 = 3526397) B3526397
theorem B2416483 : Blo 1566981 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B2350961 : Blo 1566981 2350961 := bstep (se 2 (by rfl) ⟨881610, by rfl⟩ : syracuseStep 2350961 = 1763221) B1763221
theorem B2350979 : Blo 1566981 2350979 := bstep (se 1 (by rfl) ⟨1763234, by rfl⟩ : syracuseStep 2350979 = 3526469) B3526469
theorem B2645905 : Blo 1566981 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B2351009 : Blo 1566981 2351009 := bstep (se 2 (by rfl) ⟨881628, by rfl⟩ : syracuseStep 2351009 = 1763257) B1763257
theorem B2351027 : Blo 1566981 2351027 := bstep (se 1 (by rfl) ⟨1763270, by rfl⟩ : syracuseStep 2351027 = 3526541) B3526541
theorem B2645939 : Blo 1566981 2645939 := bstep (se 1 (by rfl) ⟨1984454, by rfl⟩ : syracuseStep 2645939 = 3968909) B3968909
theorem B17850293 : Blo 1566981 17850293 := bstep (se 5 (by rfl) ⟨836732, by rfl⟩ : syracuseStep 17850293 = 1673465) B1673465
theorem B2351057 : Blo 1566981 2351057 := bstep (se 2 (by rfl) ⟨881646, by rfl⟩ : syracuseStep 2351057 = 1763293) B1763293
theorem B2351075 : Blo 1566981 2351075 := bstep (se 1 (by rfl) ⟨1763306, by rfl⟩ : syracuseStep 2351075 = 3526613) B3526613
theorem B2383859 : Blo 1566981 2383859 := bstep (se 1 (by rfl) ⟨1787894, by rfl⟩ : syracuseStep 2383859 = 3575789) B3575789
theorem B2383895 : Blo 1566981 2383895 := bstep (se 1 (by rfl) ⟨1787921, by rfl⟩ : syracuseStep 2383895 = 3575843) B3575843
theorem B5652503 : Blo 1566981 5652503 := bstep (se 1 (by rfl) ⟨4239377, by rfl⟩ : syracuseStep 5652503 = 8478755) B8478755
theorem B2351129 : Blo 1566981 2351129 := bstep (se 2 (by rfl) ⟨881673, by rfl⟩ : syracuseStep 2351129 = 1763347) B1763347
theorem B3817547 : Blo 1566981 3817547 := bstep (se 1 (by rfl) ⟨2863160, by rfl⟩ : syracuseStep 3817547 = 5726321) B5726321
theorem B4464715 : Blo 1566981 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B5292107 : Blo 1566981 5292107 := bstep (se 1 (by rfl) ⟨3969080, by rfl⟩ : syracuseStep 5292107 = 7938161) B7938161
theorem B1884235 : Blo 1566981 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B2351243 : Blo 1566981 2351243 := bstep (se 1 (by rfl) ⟨1763432, by rfl⟩ : syracuseStep 2351243 = 3526865) B3526865
theorem B2646155 : Blo 1566981 2646155 := bstep (se 1 (by rfl) ⟨1984616, by rfl⟩ : syracuseStep 2646155 = 3969233) B3969233
theorem B2351255 : Blo 1566981 2351255 := bstep (se 1 (by rfl) ⟨1763441, by rfl⟩ : syracuseStep 2351255 = 3526883) B3526883
theorem B11911373 : Blo 1566981 11911373 := bstep (se 3 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 11911373 = 4466765) B4466765
theorem B2351321 : Blo 1566981 2351321 := bstep (se 2 (by rfl) ⟨881745, by rfl⟩ : syracuseStep 2351321 = 1763491) B1763491
theorem B3178739 : Blo 1566981 3178739 := bstep (se 1 (by rfl) ⟨2384054, by rfl⟩ : syracuseStep 3178739 = 4768109) B4768109
theorem B2646283 : Blo 1566981 2646283 := bstep (se 1 (by rfl) ⟨1984712, by rfl⟩ : syracuseStep 2646283 = 3969425) B3969425
theorem B6701363 : Blo 1566981 6701363 := bstep (se 1 (by rfl) ⟨5026022, by rfl⟩ : syracuseStep 6701363 = 10052045) B10052045
theorem B2351435 : Blo 1566981 2351435 := bstep (se 1 (by rfl) ⟨1763576, by rfl⟩ : syracuseStep 2351435 = 3527153) B3527153
theorem B2351447 : Blo 1566981 2351447 := bstep (se 1 (by rfl) ⟨1763585, by rfl⟩ : syracuseStep 2351447 = 3527171) B3527171
theorem B5292377 : Blo 1566981 5292377 := bstep (se 2 (by rfl) ⟨1984641, by rfl⟩ : syracuseStep 5292377 = 3969283) B3969283
theorem B4464989 : Blo 1566981 4464989 := bstep (se 3 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 4464989 = 1674371) B1674371
theorem B2351513 : Blo 1566981 2351513 := bstep (se 2 (by rfl) ⟨881817, by rfl⟩ : syracuseStep 2351513 = 1763635) B1763635
theorem B2646425 : Blo 1566981 2646425 := bstep (se 2 (by rfl) ⟨992409, by rfl⟩ : syracuseStep 2646425 = 1984819) B1984819
theorem B2826713 : Blo 1566981 2826713 := bstep (se 2 (by rfl) ⟨1060017, by rfl⟩ : syracuseStep 2826713 = 2120035) B2120035
theorem B2351627 : Blo 1566981 2351627 := bstep (se 1 (by rfl) ⟨1763720, by rfl⟩ : syracuseStep 2351627 = 3527441) B3527441
theorem B2351639 : Blo 1566981 2351639 := bstep (se 1 (by rfl) ⟨1763729, by rfl⟩ : syracuseStep 2351639 = 3527459) B3527459
theorem B2384407 : Blo 1566981 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B2646553 : Blo 1566981 2646553 := bstep (se 2 (by rfl) ⟨992457, by rfl⟩ : syracuseStep 2646553 = 1984915) B1984915
theorem B20095523 : Blo 1566981 20095523 := bstep (se 1 (by rfl) ⟨15071642, by rfl⟩ : syracuseStep 20095523 = 30143285) B30143285
theorem B1589815 : Blo 1566981 1589815 := bstep (se 1 (by rfl) ⟨1192361, by rfl⟩ : syracuseStep 1589815 = 2384723) B2384723
theorem B10052171 : Blo 1566981 10052171 := bstep (se 1 (by rfl) ⟨7539128, by rfl⟩ : syracuseStep 10052171 = 15078257) B15078257
theorem B2351705 : Blo 1566981 2351705 := bstep (se 2 (by rfl) ⟨881889, by rfl⟩ : syracuseStep 2351705 = 1763779) B1763779
theorem B8929885 : Blo 1566981 8929885 := bstep (se 3 (by rfl) ⟨1674353, by rfl⟩ : syracuseStep 8929885 = 3348707) B3348707
theorem B7537283 : Blo 1566981 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B4465331 : Blo 1566981 4465331 := bstep (se 1 (by rfl) ⟨3348998, by rfl⟩ : syracuseStep 4465331 = 6697997) B6697997
theorem B11911859 : Blo 1566981 11911859 := bstep (se 1 (by rfl) ⟨8933894, by rfl⟩ : syracuseStep 11911859 = 17867789) B17867789
theorem B2351819 : Blo 1566981 2351819 := bstep (se 1 (by rfl) ⟨1763864, by rfl⟩ : syracuseStep 2351819 = 3527729) B3527729
theorem B2351831 : Blo 1566981 2351831 := bstep (se 1 (by rfl) ⟨1763873, by rfl⟩ : syracuseStep 2351831 = 3527747) B3527747
theorem B5956355 : Blo 1566981 5956355 := bstep (se 1 (by rfl) ⟨4467266, by rfl⟩ : syracuseStep 5956355 = 8934533) B8934533
theorem B2351897 : Blo 1566981 2351897 := bstep (se 2 (by rfl) ⟨881961, by rfl⟩ : syracuseStep 2351897 = 1763923) B1763923
theorem B2352011 : Blo 1566981 2352011 := bstep (se 1 (by rfl) ⟨1764008, by rfl⟩ : syracuseStep 2352011 = 3528017) B3528017
theorem B2352023 : Blo 1566981 2352023 := bstep (se 1 (by rfl) ⟨1764017, by rfl⟩ : syracuseStep 2352023 = 3528035) B3528035
theorem B10052531 : Blo 1566981 10052531 := bstep (se 1 (by rfl) ⟨7539398, by rfl⟩ : syracuseStep 10052531 = 15078797) B15078797
theorem B2352089 : Blo 1566981 2352089 := bstep (se 2 (by rfl) ⟨882033, by rfl⟩ : syracuseStep 2352089 = 1764067) B1764067
theorem B7742425 : Blo 1566981 7742425 := bstep (se 2 (by rfl) ⟨2903409, by rfl⟩ : syracuseStep 7742425 = 5806819) B5806819
theorem B12715013 : Blo 1566981 12715013 := bstep (se 4 (by rfl) ⟨1192032, by rfl⟩ : syracuseStep 12715013 = 2384065) B2384065
theorem B5293079 : Blo 1566981 5293079 := bstep (se 1 (by rfl) ⟨3969809, by rfl⟩ : syracuseStep 5293079 = 7939619) B7939619
theorem B128803861 : Blo 1566981 128803861 := bstep (se 6 (by rfl) ⟨3018840, by rfl⟩ : syracuseStep 128803861 = 6037681) B6037681
theorem B10044481 : Blo 1566981 10044481 := bstep (se 2 (by rfl) ⟨3766680, by rfl⟩ : syracuseStep 10044481 = 7533361) B7533361
theorem B2352203 : Blo 1566981 2352203 := bstep (se 1 (by rfl) ⟨1764152, by rfl⟩ : syracuseStep 2352203 = 3528305) B3528305
theorem B2352215 : Blo 1566981 2352215 := bstep (se 1 (by rfl) ⟨1764161, by rfl⟩ : syracuseStep 2352215 = 3528323) B3528323
theorem B2647127 : Blo 1566981 2647127 := bstep (se 1 (by rfl) ⟨1985345, by rfl⟩ : syracuseStep 2647127 = 3970691) B3970691
theorem B5653597 : Blo 1566981 5653597 := bstep (se 3 (by rfl) ⟨1060049, by rfl⟩ : syracuseStep 5653597 = 2120099) B2120099
theorem B1811575 : Blo 1566981 1811575 := bstep (se 1 (by rfl) ⟨1358681, by rfl⟩ : syracuseStep 1811575 = 2717363) B2717363
theorem B2352281 : Blo 1566981 2352281 := bstep (se 2 (by rfl) ⟨882105, by rfl⟩ : syracuseStep 2352281 = 1764211) B1764211
theorem B5956811 : Blo 1566981 5956811 := bstep (se 1 (by rfl) ⟨4467608, by rfl⟩ : syracuseStep 5956811 = 8935217) B8935217
theorem B2647255 : Blo 1566981 2647255 := bstep (se 1 (by rfl) ⟨1985441, by rfl⟩ : syracuseStep 2647255 = 3970883) B3970883
theorem B2352395 : Blo 1566981 2352395 := bstep (se 1 (by rfl) ⟨1764296, by rfl⟩ : syracuseStep 2352395 = 3528593) B3528593
theorem B2352407 : Blo 1566981 2352407 := bstep (se 1 (by rfl) ⟨1764305, by rfl⟩ : syracuseStep 2352407 = 3528611) B3528611
theorem B2352473 : Blo 1566981 2352473 := bstep (se 2 (by rfl) ⟨882177, by rfl⟩ : syracuseStep 2352473 = 1764355) B1764355
theorem B3179891 : Blo 1566981 3179891 := bstep (se 1 (by rfl) ⟨2384918, by rfl⟩ : syracuseStep 3179891 = 4769837) B4769837
theorem B5957009 : Blo 1566981 5957009 := bstep (se 2 (by rfl) ⟨2233878, by rfl⟩ : syracuseStep 5957009 = 4467757) B4467757
theorem B2352587 : Blo 1566981 2352587 := bstep (se 1 (by rfl) ⟨1764440, by rfl⟩ : syracuseStep 2352587 = 3528881) B3528881
theorem B2352599 : Blo 1566981 2352599 := bstep (se 1 (by rfl) ⟨1764449, by rfl⟩ : syracuseStep 2352599 = 3528899) B3528899
theorem B4236761 : Blo 1566981 4236761 := bstep (se 2 (by rfl) ⟨1588785, by rfl⟩ : syracuseStep 4236761 = 3177571) B3177571
theorem B4523543 : Blo 1566981 4523543 := bstep (se 1 (by rfl) ⟨3392657, by rfl⟩ : syracuseStep 4523543 = 6785315) B6785315
theorem B5023255 : Blo 1566981 5023255 := bstep (se 1 (by rfl) ⟨3767441, by rfl⟩ : syracuseStep 5023255 = 7534883) B7534883
theorem B2352665 : Blo 1566981 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B5293619 : Blo 1566981 5293619 := bstep (se 1 (by rfl) ⟨3970214, by rfl⟩ : syracuseStep 5293619 = 7940429) B7940429
theorem B3966529 : Blo 1566981 3966529 := bstep (se 2 (by rfl) ⟨1487448, by rfl⟩ : syracuseStep 3966529 = 2974897) B2974897
theorem B2352779 : Blo 1566981 2352779 := bstep (se 1 (by rfl) ⟨1764584, by rfl⟩ : syracuseStep 2352779 = 3529169) B3529169
theorem B2975383 : Blo 1566981 2975383 := bstep (se 1 (by rfl) ⟨2231537, by rfl⟩ : syracuseStep 2975383 = 4463075) B4463075
theorem B2352791 : Blo 1566981 2352791 := bstep (se 1 (by rfl) ⟨1764593, by rfl⟩ : syracuseStep 2352791 = 3529187) B3529187
theorem B1762987 : Blo 1566981 1762987 := bstep (se 1 (by rfl) ⟨1322240, by rfl⟩ : syracuseStep 1762987 = 2644481) B2644481
theorem B2352857 : Blo 1566981 2352857 := bstep (se 2 (by rfl) ⟨882321, by rfl⟩ : syracuseStep 2352857 = 1764643) B1764643
theorem B1984267 : Blo 1566981 1984267 := bstep (se 1 (by rfl) ⟨1488200, by rfl⟩ : syracuseStep 1984267 = 2976401) B2976401
theorem B1763095 : Blo 1566981 1763095 := bstep (se 1 (by rfl) ⟨1322321, by rfl⟩ : syracuseStep 1763095 = 2644643) B2644643
theorem B18351937 : Blo 1566981 18351937 := bstep (se 2 (by rfl) ⟨6881976, by rfl⟩ : syracuseStep 18351937 = 13763953) B13763953
theorem B5293889 : Blo 1566981 5293889 := bstep (se 2 (by rfl) ⟨1985208, by rfl⟩ : syracuseStep 5293889 = 3970417) B3970417
theorem B11298635 : Blo 1566981 11298635 := bstep (se 1 (by rfl) ⟨8473976, by rfl⟩ : syracuseStep 11298635 = 16947953) B16947953
theorem B1836875 : Blo 1566981 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B2352971 : Blo 1566981 2352971 := bstep (se 1 (by rfl) ⟨1764728, by rfl⟩ : syracuseStep 2352971 = 3529457) B3529457
theorem B2352983 : Blo 1566981 2352983 := bstep (se 1 (by rfl) ⟨1764737, by rfl⟩ : syracuseStep 2352983 = 3529475) B3529475
theorem B2353049 : Blo 1566981 2353049 := bstep (se 2 (by rfl) ⟨882393, by rfl⟩ : syracuseStep 2353049 = 1764787) B1764787
theorem B1763275 : Blo 1566981 1763275 := bstep (se 1 (by rfl) ⟨1322456, by rfl⟩ : syracuseStep 1763275 = 2644913) B2644913
theorem B3016705 : Blo 1566981 3016705 := bstep (se 2 (by rfl) ⟨1131264, by rfl⟩ : syracuseStep 3016705 = 2262529) B2262529
theorem B2353163 : Blo 1566981 2353163 := bstep (se 1 (by rfl) ⟨1764872, by rfl⟩ : syracuseStep 2353163 = 3529745) B3529745
theorem B2353175 : Blo 1566981 2353175 := bstep (se 1 (by rfl) ⟨1764881, by rfl⟩ : syracuseStep 2353175 = 3529763) B3529763
theorem B1763383 : Blo 1566981 1763383 := bstep (se 1 (by rfl) ⟨1322537, by rfl⟩ : syracuseStep 1763383 = 2645075) B2645075
theorem B2353241 : Blo 1566981 2353241 := bstep (se 2 (by rfl) ⟨882465, by rfl⟩ : syracuseStep 2353241 = 1764931) B1764931
theorem B11913317 : Blo 1566981 11913317 := bstep (se 4 (by rfl) ⟨1116873, by rfl⟩ : syracuseStep 11913317 = 2233747) B2233747
theorem B14297239 : Blo 1566981 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B3967127 : Blo 1566981 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B2353355 : Blo 1566981 2353355 := bstep (se 1 (by rfl) ⟨1765016, by rfl⟩ : syracuseStep 2353355 = 3530033) B3530033
theorem B2353367 : Blo 1566981 2353367 := bstep (se 1 (by rfl) ⟨1765025, by rfl⟩ : syracuseStep 2353367 = 3530051) B3530051
theorem B1763563 : Blo 1566981 1763563 := bstep (se 1 (by rfl) ⟨1322672, by rfl⟩ : syracuseStep 1763563 = 2645345) B2645345
theorem B1566987 : Blo 1566981 1566987 := bstep (se 1 (by rfl) ⟨1175240, by rfl⟩ : syracuseStep 1566987 = 2350481) B2350481
theorem B1566999 : Blo 1566981 1566999 := bstep (se 1 (by rfl) ⟨1175249, by rfl⟩ : syracuseStep 1566999 = 2350499) B2350499
theorem B5949719 : Blo 1566981 5949719 := bstep (se 1 (by rfl) ⟨4462289, by rfl⟩ : syracuseStep 5949719 = 8924579) B8924579
theorem B2353433 : Blo 1566981 2353433 := bstep (se 2 (by rfl) ⟨882537, by rfl⟩ : syracuseStep 2353433 = 1765075) B1765075
theorem B1567019 : Blo 1566981 1567019 := bstep (se 1 (by rfl) ⟨1175264, by rfl⟩ : syracuseStep 1567019 = 2350529) B2350529
theorem B1567031 : Blo 1566981 1567031 := bstep (se 1 (by rfl) ⟨1175273, by rfl⟩ : syracuseStep 1567031 = 2350547) B2350547
theorem B1567051 : Blo 1566981 1567051 := bstep (se 1 (by rfl) ⟨1175288, by rfl⟩ : syracuseStep 1567051 = 2350577) B2350577
theorem B1567063 : Blo 1566981 1567063 := bstep (se 1 (by rfl) ⟨1175297, by rfl⟩ : syracuseStep 1567063 = 2350595) B2350595
theorem B1763671 : Blo 1566981 1763671 := bstep (se 1 (by rfl) ⟨1322753, by rfl⟩ : syracuseStep 1763671 = 2645507) B2645507
theorem B5294429 : Blo 1566981 5294429 := bstep (se 3 (by rfl) ⟨992705, by rfl⟩ : syracuseStep 5294429 = 1985411) B1985411
theorem B1567083 : Blo 1566981 1567083 := bstep (se 1 (by rfl) ⟨1175312, by rfl⟩ : syracuseStep 1567083 = 2350625) B2350625
theorem B1567095 : Blo 1566981 1567095 := bstep (se 1 (by rfl) ⟨1175321, by rfl⟩ : syracuseStep 1567095 = 2350643) B2350643
theorem B1567115 : Blo 1566981 1567115 := bstep (se 1 (by rfl) ⟨1175336, by rfl⟩ : syracuseStep 1567115 = 2350673) B2350673
theorem B1567127 : Blo 1566981 1567127 := bstep (se 1 (by rfl) ⟨1175345, by rfl⟩ : syracuseStep 1567127 = 2350691) B2350691
theorem B1567147 : Blo 1566981 1567147 := bstep (se 1 (by rfl) ⟨1175360, by rfl⟩ : syracuseStep 1567147 = 2350721) B2350721
theorem B1567159 : Blo 1566981 1567159 := bstep (se 1 (by rfl) ⟨1175369, by rfl⟩ : syracuseStep 1567159 = 2350739) B2350739
theorem B1567179 : Blo 1566981 1567179 := bstep (se 1 (by rfl) ⟨1175384, by rfl⟩ : syracuseStep 1567179 = 2350769) B2350769
theorem B2976203 : Blo 1566981 2976203 := bstep (se 1 (by rfl) ⟨2232152, by rfl⟩ : syracuseStep 2976203 = 4464305) B4464305
theorem B1567191 : Blo 1566981 1567191 := bstep (se 1 (by rfl) ⟨1175393, by rfl⟩ : syracuseStep 1567191 = 2350787) B2350787
theorem B3221977 : Blo 1566981 3221977 := bstep (se 2 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 3221977 = 2416483) B2416483
theorem B1567211 : Blo 1566981 1567211 := bstep (se 1 (by rfl) ⟨1175408, by rfl⟩ : syracuseStep 1567211 = 2350817) B2350817
theorem B1567223 : Blo 1566981 1567223 := bstep (se 1 (by rfl) ⟨1175417, by rfl⟩ : syracuseStep 1567223 = 2350835) B2350835
theorem B2976257 : Blo 1566981 2976257 := bstep (se 2 (by rfl) ⟨1116096, by rfl⟩ : syracuseStep 2976257 = 2232193) B2232193
theorem B3394049 : Blo 1566981 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B11905541 : Blo 1566981 11905541 := bstep (se 4 (by rfl) ⟨1116144, by rfl⟩ : syracuseStep 11905541 = 2232289) B2232289
theorem B1567243 : Blo 1566981 1567243 := bstep (se 1 (by rfl) ⟨1175432, by rfl⟩ : syracuseStep 1567243 = 2350865) B2350865
theorem B1763851 : Blo 1566981 1763851 := bstep (se 1 (by rfl) ⟨1322888, by rfl⟩ : syracuseStep 1763851 = 2645777) B2645777
theorem B1567255 : Blo 1566981 1567255 := bstep (se 1 (by rfl) ⟨1175441, by rfl⟩ : syracuseStep 1567255 = 2350883) B2350883
theorem B1567275 : Blo 1566981 1567275 := bstep (se 1 (by rfl) ⟨1175456, by rfl⟩ : syracuseStep 1567275 = 2350913) B2350913
theorem B1567287 : Blo 1566981 1567287 := bstep (se 1 (by rfl) ⟨1175465, by rfl⟩ : syracuseStep 1567287 = 2350931) B2350931
theorem B1567307 : Blo 1566981 1567307 := bstep (se 1 (by rfl) ⟨1175480, by rfl⟩ : syracuseStep 1567307 = 2350961) B2350961
theorem B11913803 : Blo 1566981 11913803 := bstep (se 1 (by rfl) ⟨8935352, by rfl⟩ : syracuseStep 11913803 = 17870705) B17870705
theorem B1567319 : Blo 1566981 1567319 := bstep (se 1 (by rfl) ⟨1175489, by rfl⟩ : syracuseStep 1567319 = 2350979) B2350979
theorem B1567339 : Blo 1566981 1567339 := bstep (se 1 (by rfl) ⟨1175504, by rfl⟩ : syracuseStep 1567339 = 2351009) B2351009
theorem B1567351 : Blo 1566981 1567351 := bstep (se 1 (by rfl) ⟨1175513, by rfl⟩ : syracuseStep 1567351 = 2351027) B2351027
theorem B1763959 : Blo 1566981 1763959 := bstep (se 1 (by rfl) ⟨1322969, by rfl⟩ : syracuseStep 1763959 = 2645939) B2645939
theorem B1567371 : Blo 1566981 1567371 := bstep (se 1 (by rfl) ⟨1175528, by rfl⟩ : syracuseStep 1567371 = 2351057) B2351057
theorem B1567383 : Blo 1566981 1567383 := bstep (se 1 (by rfl) ⟨1175537, by rfl⟩ : syracuseStep 1567383 = 2351075) B2351075
theorem B1567403 : Blo 1566981 1567403 := bstep (se 1 (by rfl) ⟨1175552, by rfl⟩ : syracuseStep 1567403 = 2351105) B2351105
theorem B1567415 : Blo 1566981 1567415 := bstep (se 1 (by rfl) ⟨1175561, by rfl⟩ : syracuseStep 1567415 = 2351123) B2351123
theorem B1567435 : Blo 1566981 1567435 := bstep (se 1 (by rfl) ⟨1175576, by rfl⟩ : syracuseStep 1567435 = 2351153) B2351153
theorem B4467403 : Blo 1566981 4467403 := bstep (se 1 (by rfl) ⟨3350552, by rfl⟩ : syracuseStep 4467403 = 6701105) B6701105
theorem B1567447 : Blo 1566981 1567447 := bstep (se 1 (by rfl) ⟨1175585, by rfl⟩ : syracuseStep 1567447 = 2351171) B2351171
theorem B1985239 : Blo 1566981 1985239 := bstep (se 1 (by rfl) ⟨1488929, by rfl⟩ : syracuseStep 1985239 = 2977859) B2977859
theorem B1567467 : Blo 1566981 1567467 := bstep (se 1 (by rfl) ⟨1175600, by rfl⟩ : syracuseStep 1567467 = 2351201) B2351201
theorem B1567479 : Blo 1566981 1567479 := bstep (se 1 (by rfl) ⟨1175609, by rfl⟩ : syracuseStep 1567479 = 2351219) B2351219
theorem B1567499 : Blo 1566981 1567499 := bstep (se 1 (by rfl) ⟨1175624, by rfl⟩ : syracuseStep 1567499 = 2351249) B2351249
theorem B1673995 : Blo 1566981 1673995 := bstep (se 1 (by rfl) ⟨1255496, by rfl⟩ : syracuseStep 1673995 = 2510993) B2510993
theorem B1567511 : Blo 1566981 1567511 := bstep (se 1 (by rfl) ⟨1175633, by rfl⟩ : syracuseStep 1567511 = 2351267) B2351267
theorem B3394327 : Blo 1566981 3394327 := bstep (se 1 (by rfl) ⟨2545745, by rfl⟩ : syracuseStep 3394327 = 5091491) B5091491
theorem B1567531 : Blo 1566981 1567531 := bstep (se 1 (by rfl) ⟨1175648, by rfl⟩ : syracuseStep 1567531 = 2351297) B2351297
theorem B1764139 : Blo 1566981 1764139 := bstep (se 1 (by rfl) ⟨1323104, by rfl⟩ : syracuseStep 1764139 = 2646209) B2646209
theorem B1567543 : Blo 1566981 1567543 := bstep (se 1 (by rfl) ⟨1175657, by rfl⟩ : syracuseStep 1567543 = 2351315) B2351315
theorem B7154497 : Blo 1566981 7154497 := bstep (se 2 (by rfl) ⟨2682936, by rfl⟩ : syracuseStep 7154497 = 5365873) B5365873
theorem B1567563 : Blo 1566981 1567563 := bstep (se 1 (by rfl) ⟨1175672, by rfl⟩ : syracuseStep 1567563 = 2351345) B2351345
theorem B5024587 : Blo 1566981 5024587 := bstep (se 1 (by rfl) ⟨3768440, by rfl⟩ : syracuseStep 5024587 = 7536881) B7536881
theorem B1567575 : Blo 1566981 1567575 := bstep (se 1 (by rfl) ⟨1175681, by rfl⟩ : syracuseStep 1567575 = 2351363) B2351363
theorem B1567595 : Blo 1566981 1567595 := bstep (se 1 (by rfl) ⟨1175696, by rfl⟩ : syracuseStep 1567595 = 2351393) B2351393
theorem B1567607 : Blo 1566981 1567607 := bstep (se 1 (by rfl) ⟨1175705, by rfl⟩ : syracuseStep 1567607 = 2351411) B2351411
theorem B1567627 : Blo 1566981 1567627 := bstep (se 1 (by rfl) ⟨1175720, by rfl⟩ : syracuseStep 1567627 = 2351441) B2351441
theorem B1567639 : Blo 1566981 1567639 := bstep (se 1 (by rfl) ⟨1175729, by rfl⟩ : syracuseStep 1567639 = 2351459) B2351459
theorem B1764247 : Blo 1566981 1764247 := bstep (se 1 (by rfl) ⟨1323185, by rfl⟩ : syracuseStep 1764247 = 2646371) B2646371
theorem B1567659 : Blo 1566981 1567659 := bstep (se 1 (by rfl) ⟨1175744, by rfl⟩ : syracuseStep 1567659 = 2351489) B2351489
theorem B1567671 : Blo 1566981 1567671 := bstep (se 1 (by rfl) ⟨1175753, by rfl⟩ : syracuseStep 1567671 = 2351507) B2351507
theorem B3967937 : Blo 1566981 3967937 := bstep (se 2 (by rfl) ⟨1487976, by rfl⟩ : syracuseStep 3967937 = 2975953) B2975953
theorem B1567691 : Blo 1566981 1567691 := bstep (se 1 (by rfl) ⟨1175768, by rfl⟩ : syracuseStep 1567691 = 2351537) B2351537
theorem B1567703 : Blo 1566981 1567703 := bstep (se 1 (by rfl) ⟨1175777, by rfl⟩ : syracuseStep 1567703 = 2351555) B2351555
theorem B1567723 : Blo 1566981 1567723 := bstep (se 1 (by rfl) ⟨1175792, by rfl⟩ : syracuseStep 1567723 = 2351585) B2351585
theorem B1567735 : Blo 1566981 1567735 := bstep (se 1 (by rfl) ⟨1175801, by rfl⟩ : syracuseStep 1567735 = 2351603) B2351603
theorem B1567755 : Blo 1566981 1567755 := bstep (se 1 (by rfl) ⟨1175816, by rfl⟩ : syracuseStep 1567755 = 2351633) B2351633
theorem B1567767 : Blo 1566981 1567767 := bstep (se 1 (by rfl) ⟨1175825, by rfl⟩ : syracuseStep 1567767 = 2351651) B2351651
theorem B1567787 : Blo 1566981 1567787 := bstep (se 1 (by rfl) ⟨1175840, by rfl⟩ : syracuseStep 1567787 = 2351681) B2351681
theorem B1567799 : Blo 1566981 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B1567819 : Blo 1566981 1567819 := bstep (se 1 (by rfl) ⟨1175864, by rfl⟩ : syracuseStep 1567819 = 2351729) B2351729
theorem B1764427 : Blo 1566981 1764427 := bstep (se 1 (by rfl) ⟨1323320, by rfl⟩ : syracuseStep 1764427 = 2646641) B2646641
theorem B1567831 : Blo 1566981 1567831 := bstep (se 1 (by rfl) ⟨1175873, by rfl⟩ : syracuseStep 1567831 = 2351747) B2351747
theorem B1567851 : Blo 1566981 1567851 := bstep (se 1 (by rfl) ⟨1175888, by rfl⟩ : syracuseStep 1567851 = 2351777) B2351777
theorem B1567863 : Blo 1566981 1567863 := bstep (se 1 (by rfl) ⟨1175897, by rfl⟩ : syracuseStep 1567863 = 2351795) B2351795
theorem B3017857 : Blo 1566981 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B2231435 : Blo 1566981 2231435 := bstep (se 1 (by rfl) ⟨1673576, by rfl⟩ : syracuseStep 2231435 = 3347153) B3347153
theorem B1567883 : Blo 1566981 1567883 := bstep (se 1 (by rfl) ⟨1175912, by rfl⟩ : syracuseStep 1567883 = 2351825) B2351825
theorem B1567895 : Blo 1566981 1567895 := bstep (se 1 (by rfl) ⟨1175921, by rfl⟩ : syracuseStep 1567895 = 2351843) B2351843
theorem B3525785 : Blo 1566981 3525785 := bstep (se 2 (by rfl) ⟨1322169, by rfl⟩ : syracuseStep 3525785 = 2644339) B2644339
theorem B1567915 : Blo 1566981 1567915 := bstep (se 1 (by rfl) ⟨1175936, by rfl⟩ : syracuseStep 1567915 = 2351873) B2351873
theorem B1567927 : Blo 1566981 1567927 := bstep (se 1 (by rfl) ⟨1175945, by rfl⟩ : syracuseStep 1567927 = 2351891) B2351891
theorem B1764535 : Blo 1566981 1764535 := bstep (se 1 (by rfl) ⟨1323401, by rfl⟩ : syracuseStep 1764535 = 2646803) B2646803
theorem B4467905 : Blo 1566981 4467905 := bstep (se 2 (by rfl) ⟨1675464, by rfl⟩ : syracuseStep 4467905 = 3350929) B3350929
theorem B1567947 : Blo 1566981 1567947 := bstep (se 1 (by rfl) ⟨1175960, by rfl⟩ : syracuseStep 1567947 = 2351921) B2351921
theorem B1567959 : Blo 1566981 1567959 := bstep (se 1 (by rfl) ⟨1175969, by rfl⟩ : syracuseStep 1567959 = 2351939) B2351939
theorem B1567979 : Blo 1566981 1567979 := bstep (se 1 (by rfl) ⟨1175984, by rfl⟩ : syracuseStep 1567979 = 2351969) B2351969
theorem B3525875 : Blo 1566981 3525875 := bstep (se 1 (by rfl) ⟨2644406, by rfl⟩ : syracuseStep 3525875 = 5288813) B5288813
theorem B1567991 : Blo 1566981 1567991 := bstep (se 1 (by rfl) ⟨1175993, by rfl⟩ : syracuseStep 1567991 = 2351987) B2351987
theorem B1568011 : Blo 1566981 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B3525911 : Blo 1566981 3525911 := bstep (se 1 (by rfl) ⟨2644433, by rfl⟩ : syracuseStep 3525911 = 5288867) B5288867
theorem B1568023 : Blo 1566981 1568023 := bstep (se 1 (by rfl) ⟨1176017, by rfl⟩ : syracuseStep 1568023 = 2352035) B2352035
theorem B1568043 : Blo 1566981 1568043 := bstep (se 1 (by rfl) ⟨1176032, by rfl⟩ : syracuseStep 1568043 = 2352065) B2352065
theorem B1568055 : Blo 1566981 1568055 := bstep (se 1 (by rfl) ⟨1176041, by rfl⟩ : syracuseStep 1568055 = 2352083) B2352083
theorem B1568075 : Blo 1566981 1568075 := bstep (se 1 (by rfl) ⟨1176056, by rfl⟩ : syracuseStep 1568075 = 2352113) B2352113
theorem B1568087 : Blo 1566981 1568087 := bstep (se 1 (by rfl) ⟨1176065, by rfl⟩ : syracuseStep 1568087 = 2352131) B2352131
theorem B1568107 : Blo 1566981 1568107 := bstep (se 1 (by rfl) ⟨1176080, by rfl⟩ : syracuseStep 1568107 = 2352161) B2352161
theorem B1764715 : Blo 1566981 1764715 := bstep (se 1 (by rfl) ⟨1323536, by rfl⟩ : syracuseStep 1764715 = 2647073) B2647073
theorem B1568119 : Blo 1566981 1568119 := bstep (se 1 (by rfl) ⟨1176089, by rfl⟩ : syracuseStep 1568119 = 2352179) B2352179
theorem B1568139 : Blo 1566981 1568139 := bstep (se 1 (by rfl) ⟨1176104, by rfl⟩ : syracuseStep 1568139 = 2352209) B2352209
theorem B1568151 : Blo 1566981 1568151 := bstep (se 1 (by rfl) ⟨1176113, by rfl⟩ : syracuseStep 1568151 = 2352227) B2352227
theorem B2977175 : Blo 1566981 2977175 := bstep (se 1 (by rfl) ⟨2232881, by rfl⟩ : syracuseStep 2977175 = 4465763) B4465763
theorem B1568171 : Blo 1566981 1568171 := bstep (se 1 (by rfl) ⟨1176128, by rfl⟩ : syracuseStep 1568171 = 2352257) B2352257
theorem B5025203 : Blo 1566981 5025203 := bstep (se 1 (by rfl) ⟨3768902, by rfl⟩ : syracuseStep 5025203 = 7537805) B7537805
theorem B1568183 : Blo 1566981 1568183 := bstep (se 1 (by rfl) ⟨1176137, by rfl⟩ : syracuseStep 1568183 = 2352275) B2352275
theorem B3526091 : Blo 1566981 3526091 := bstep (se 1 (by rfl) ⟨2644568, by rfl⟩ : syracuseStep 3526091 = 5289137) B5289137
theorem B1568203 : Blo 1566981 1568203 := bstep (se 1 (by rfl) ⟨1176152, by rfl⟩ : syracuseStep 1568203 = 2352305) B2352305
theorem B1568215 : Blo 1566981 1568215 := bstep (se 1 (by rfl) ⟨1176161, by rfl⟩ : syracuseStep 1568215 = 2352323) B2352323
theorem B1764823 : Blo 1566981 1764823 := bstep (se 1 (by rfl) ⟨1323617, by rfl⟩ : syracuseStep 1764823 = 2647235) B2647235
theorem B3968473 : Blo 1566981 3968473 := bstep (se 2 (by rfl) ⟨1488177, by rfl⟩ : syracuseStep 3968473 = 2976355) B2976355
theorem B1568235 : Blo 1566981 1568235 := bstep (se 1 (by rfl) ⟨1176176, by rfl⟩ : syracuseStep 1568235 = 2352353) B2352353
theorem B3018227 : Blo 1566981 3018227 := bstep (se 1 (by rfl) ⟨2263670, by rfl⟩ : syracuseStep 3018227 = 4527341) B4527341
theorem B1568247 : Blo 1566981 1568247 := bstep (se 1 (by rfl) ⟨1176185, by rfl⟩ : syracuseStep 1568247 = 2352371) B2352371
theorem B3526145 : Blo 1566981 3526145 := bstep (se 2 (by rfl) ⟨1322304, by rfl⟩ : syracuseStep 3526145 = 2644609) B2644609
theorem B5950979 : Blo 1566981 5950979 := bstep (se 1 (by rfl) ⟨4463234, by rfl⟩ : syracuseStep 5950979 = 8926469) B8926469
theorem B1568267 : Blo 1566981 1568267 := bstep (se 1 (by rfl) ⟨1176200, by rfl⟩ : syracuseStep 1568267 = 2352401) B2352401
theorem B1568279 : Blo 1566981 1568279 := bstep (se 1 (by rfl) ⟨1176209, by rfl⟩ : syracuseStep 1568279 = 2352419) B2352419
theorem B1568299 : Blo 1566981 1568299 := bstep (se 1 (by rfl) ⟨1176224, by rfl⟩ : syracuseStep 1568299 = 2352449) B2352449
theorem B1568311 : Blo 1566981 1568311 := bstep (se 1 (by rfl) ⟨1176233, by rfl⟩ : syracuseStep 1568311 = 2352467) B2352467
theorem B1568331 : Blo 1566981 1568331 := bstep (se 1 (by rfl) ⟨1176248, by rfl⟩ : syracuseStep 1568331 = 2352497) B2352497
theorem B1568343 : Blo 1566981 1568343 := bstep (se 1 (by rfl) ⟨1176257, by rfl⟩ : syracuseStep 1568343 = 2352515) B2352515
theorem B7941725 : Blo 1566981 7941725 := bstep (se 3 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 7941725 = 2978147) B2978147
theorem B1568363 : Blo 1566981 1568363 := bstep (se 1 (by rfl) ⟨1176272, by rfl⟩ : syracuseStep 1568363 = 2352545) B2352545
theorem B1568375 : Blo 1566981 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B8154755 : Blo 1566981 8154755 := bstep (se 1 (by rfl) ⟨6116066, by rfl⟩ : syracuseStep 8154755 = 12232133) B12232133
theorem B1568395 : Blo 1566981 1568395 := bstep (se 1 (by rfl) ⟨1176296, by rfl⟩ : syracuseStep 1568395 = 2352593) B2352593
theorem B1765003 : Blo 1566981 1765003 := bstep (se 1 (by rfl) ⟨1323752, by rfl⟩ : syracuseStep 1765003 = 2647505) B2647505
theorem B1568407 : Blo 1566981 1568407 := bstep (se 1 (by rfl) ⟨1176305, by rfl⟩ : syracuseStep 1568407 = 2352611) B2352611
theorem B1568427 : Blo 1566981 1568427 := bstep (se 1 (by rfl) ⟨1176320, by rfl⟩ : syracuseStep 1568427 = 2352641) B2352641
theorem B1568439 : Blo 1566981 1568439 := bstep (se 1 (by rfl) ⟨1176329, by rfl⟩ : syracuseStep 1568439 = 2352659) B2352659
theorem B1568459 : Blo 1566981 1568459 := bstep (se 1 (by rfl) ⟨1176344, by rfl⟩ : syracuseStep 1568459 = 2352689) B2352689
theorem B2510551 : Blo 1566981 2510551 := bstep (se 1 (by rfl) ⟨1882913, by rfl⟩ : syracuseStep 2510551 = 3765827) B3765827
theorem B3526361 : Blo 1566981 3526361 := bstep (se 2 (by rfl) ⟨1322385, by rfl⟩ : syracuseStep 3526361 = 2644771) B2644771
theorem B1568471 : Blo 1566981 1568471 := bstep (se 1 (by rfl) ⟨1176353, by rfl⟩ : syracuseStep 1568471 = 2352707) B2352707
theorem B1568491 : Blo 1566981 1568491 := bstep (se 1 (by rfl) ⟨1176368, by rfl⟩ : syracuseStep 1568491 = 2352737) B2352737
theorem B1568503 : Blo 1566981 1568503 := bstep (se 1 (by rfl) ⟨1176377, by rfl⟩ : syracuseStep 1568503 = 2352755) B2352755
theorem B1568523 : Blo 1566981 1568523 := bstep (se 1 (by rfl) ⟨1176392, by rfl⟩ : syracuseStep 1568523 = 2352785) B2352785
theorem B1568535 : Blo 1566981 1568535 := bstep (se 1 (by rfl) ⟨1176401, by rfl⟩ : syracuseStep 1568535 = 2352803) B2352803
theorem B1568555 : Blo 1566981 1568555 := bstep (se 1 (by rfl) ⟨1176416, by rfl⟩ : syracuseStep 1568555 = 2352833) B2352833
theorem B3526451 : Blo 1566981 3526451 := bstep (se 1 (by rfl) ⟨2644838, by rfl⟩ : syracuseStep 3526451 = 5289677) B5289677
theorem B1568567 : Blo 1566981 1568567 := bstep (se 1 (by rfl) ⟨1176425, by rfl⟩ : syracuseStep 1568567 = 2352851) B2352851
theorem B1568587 : Blo 1566981 1568587 := bstep (se 1 (by rfl) ⟨1176440, by rfl⟩ : syracuseStep 1568587 = 2352881) B2352881
theorem B3526487 : Blo 1566981 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B1568599 : Blo 1566981 1568599 := bstep (se 1 (by rfl) ⟨1176449, by rfl⟩ : syracuseStep 1568599 = 2352899) B2352899
theorem B1568619 : Blo 1566981 1568619 := bstep (se 1 (by rfl) ⟨1176464, by rfl⟩ : syracuseStep 1568619 = 2352929) B2352929
theorem B1568631 : Blo 1566981 1568631 := bstep (se 1 (by rfl) ⟨1176473, by rfl⟩ : syracuseStep 1568631 = 2352947) B2352947
theorem B1568651 : Blo 1566981 1568651 := bstep (se 1 (by rfl) ⟨1176488, by rfl⟩ : syracuseStep 1568651 = 2352977) B2352977
theorem B1568663 : Blo 1566981 1568663 := bstep (se 1 (by rfl) ⟨1176497, by rfl⟩ : syracuseStep 1568663 = 2352995) B2352995
theorem B1568683 : Blo 1566981 1568683 := bstep (se 1 (by rfl) ⟨1176512, by rfl⟩ : syracuseStep 1568683 = 2353025) B2353025
theorem B2977715 : Blo 1566981 2977715 := bstep (se 1 (by rfl) ⟨2233286, by rfl⟩ : syracuseStep 2977715 = 4466573) B4466573
theorem B1568695 : Blo 1566981 1568695 := bstep (se 1 (by rfl) ⟨1176521, by rfl⟩ : syracuseStep 1568695 = 2353043) B2353043
theorem B1568715 : Blo 1566981 1568715 := bstep (se 1 (by rfl) ⟨1176536, by rfl⟩ : syracuseStep 1568715 = 2353073) B2353073
theorem B1568727 : Blo 1566981 1568727 := bstep (se 1 (by rfl) ⟨1176545, by rfl⟩ : syracuseStep 1568727 = 2353091) B2353091
theorem B1568747 : Blo 1566981 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B1568759 : Blo 1566981 1568759 := bstep (se 1 (by rfl) ⟨1176569, by rfl⟩ : syracuseStep 1568759 = 2353139) B2353139
theorem B3526667 : Blo 1566981 3526667 := bstep (se 1 (by rfl) ⟨2645000, by rfl⟩ : syracuseStep 3526667 = 5290001) B5290001
theorem B1568779 : Blo 1566981 1568779 := bstep (se 1 (by rfl) ⟨1176584, by rfl⟩ : syracuseStep 1568779 = 2353169) B2353169
theorem B1568791 : Blo 1566981 1568791 := bstep (se 1 (by rfl) ⟨1176593, by rfl⟩ : syracuseStep 1568791 = 2353187) B2353187
theorem B1568811 : Blo 1566981 1568811 := bstep (se 1 (by rfl) ⟨1176608, by rfl⟩ : syracuseStep 1568811 = 2353217) B2353217
theorem B1568823 : Blo 1566981 1568823 := bstep (se 1 (by rfl) ⟨1176617, by rfl⟩ : syracuseStep 1568823 = 2353235) B2353235
theorem B3526721 : Blo 1566981 3526721 := bstep (se 2 (by rfl) ⟨1322520, by rfl⟩ : syracuseStep 3526721 = 2645041) B2645041
theorem B1568843 : Blo 1566981 1568843 := bstep (se 1 (by rfl) ⟨1176632, by rfl⟩ : syracuseStep 1568843 = 2353265) B2353265
theorem B1568855 : Blo 1566981 1568855 := bstep (se 1 (by rfl) ⟨1176641, by rfl⟩ : syracuseStep 1568855 = 2353283) B2353283
theorem B5025881 : Blo 1566981 5025881 := bstep (se 2 (by rfl) ⟨1884705, by rfl⟩ : syracuseStep 5025881 = 3769411) B3769411
theorem B1568875 : Blo 1566981 1568875 := bstep (se 1 (by rfl) ⟨1176656, by rfl⟩ : syracuseStep 1568875 = 2353313) B2353313
theorem B1568887 : Blo 1566981 1568887 := bstep (se 1 (by rfl) ⟨1176665, by rfl⟩ : syracuseStep 1568887 = 2353331) B2353331
theorem B1568907 : Blo 1566981 1568907 := bstep (se 1 (by rfl) ⟨1176680, by rfl⟩ : syracuseStep 1568907 = 2353361) B2353361
theorem B1568919 : Blo 1566981 1568919 := bstep (se 1 (by rfl) ⟨1176689, by rfl⟩ : syracuseStep 1568919 = 2353379) B2353379
theorem B1568939 : Blo 1566981 1568939 := bstep (se 1 (by rfl) ⟨1176704, by rfl⟩ : syracuseStep 1568939 = 2353409) B2353409
theorem B1568951 : Blo 1566981 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B1675447 : Blo 1566981 1675447 := bstep (se 1 (by rfl) ⟨1256585, by rfl⟩ : syracuseStep 1675447 = 2513171) B2513171
theorem B1568971 : Blo 1566981 1568971 := bstep (se 1 (by rfl) ⟨1176728, by rfl⟩ : syracuseStep 1568971 = 2353457) B2353457
theorem B3526937 : Blo 1566981 3526937 := bstep (se 2 (by rfl) ⟨1322601, by rfl⟩ : syracuseStep 3526937 = 2645203) B2645203
theorem B7934273 : Blo 1566981 7934273 := bstep (se 2 (by rfl) ⟨2975352, by rfl⟩ : syracuseStep 7934273 = 5950705) B5950705
theorem B9048395 : Blo 1566981 9048395 := bstep (se 1 (by rfl) ⟨6786296, by rfl⟩ : syracuseStep 9048395 = 13572593) B13572593
theorem B13390181 : Blo 1566981 13390181 := bstep (se 4 (by rfl) ⟨1255329, by rfl⟩ : syracuseStep 13390181 = 2510659) B2510659
theorem B3527027 : Blo 1566981 3527027 := bstep (se 1 (by rfl) ⟨2645270, by rfl⟩ : syracuseStep 3527027 = 5290541) B5290541
theorem B3527063 : Blo 1566981 3527063 := bstep (se 1 (by rfl) ⟨2645297, by rfl⟩ : syracuseStep 3527063 = 5290595) B5290595
theorem B2978201 : Blo 1566981 2978201 := bstep (se 2 (by rfl) ⟨1116825, by rfl⟩ : syracuseStep 2978201 = 2233651) B2233651
theorem B2511371 : Blo 1566981 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B3969587 : Blo 1566981 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B3527243 : Blo 1566981 3527243 := bstep (se 1 (by rfl) ⟨2645432, by rfl⟩ : syracuseStep 3527243 = 5290865) B5290865
theorem B3527297 : Blo 1566981 3527297 := bstep (se 2 (by rfl) ⟨1322736, by rfl⟩ : syracuseStep 3527297 = 2645473) B2645473
theorem B5288651 : Blo 1566981 5288651 := bstep (se 1 (by rfl) ⟨3966488, by rfl⟩ : syracuseStep 5288651 = 7932977) B7932977
theorem B3527513 : Blo 1566981 3527513 := bstep (se 2 (by rfl) ⟨1322817, by rfl⟩ : syracuseStep 3527513 = 2645635) B2645635
theorem B3969881 : Blo 1566981 3969881 := bstep (se 2 (by rfl) ⟨1488705, by rfl⟩ : syracuseStep 3969881 = 2977411) B2977411
theorem B11907971 : Blo 1566981 11907971 := bstep (se 1 (by rfl) ⟨8930978, by rfl⟩ : syracuseStep 11907971 = 17861957) B17861957
theorem B3765143 : Blo 1566981 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B3527603 : Blo 1566981 3527603 := bstep (se 1 (by rfl) ⟨2645702, by rfl⟩ : syracuseStep 3527603 = 5291405) B5291405
theorem B3527639 : Blo 1566981 3527639 := bstep (se 1 (by rfl) ⟨2645729, by rfl⟩ : syracuseStep 3527639 = 5291459) B5291459
theorem B5288921 : Blo 1566981 5288921 := bstep (se 2 (by rfl) ⟨1983345, by rfl⟩ : syracuseStep 5288921 = 3966691) B3966691
theorem B3576793 : Blo 1566981 3576793 := bstep (se 2 (by rfl) ⟨1341297, by rfl⟩ : syracuseStep 3576793 = 2682595) B2682595
theorem B3347443 : Blo 1566981 3347443 := bstep (se 1 (by rfl) ⟨2510582, by rfl⟩ : syracuseStep 3347443 = 5021165) B5021165
theorem B13390865 : Blo 1566981 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B5649431 : Blo 1566981 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B3527819 : Blo 1566981 3527819 := bstep (se 1 (by rfl) ⟨2645864, by rfl⟩ : syracuseStep 3527819 = 5291729) B5291729
theorem B6354071 : Blo 1566981 6354071 := bstep (se 1 (by rfl) ⟨4765553, by rfl⟩ : syracuseStep 6354071 = 9531107) B9531107
theorem B7148695 : Blo 1566981 7148695 := bstep (se 1 (by rfl) ⟨5361521, by rfl⟩ : syracuseStep 7148695 = 10723043) B10723043
theorem B21468311 : Blo 1566981 21468311 := bstep (se 1 (by rfl) ⟨16101233, by rfl⟩ : syracuseStep 21468311 = 32202467) B32202467
theorem B3527873 : Blo 1566981 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B11900195 : Blo 1566981 11900195 := bstep (se 1 (by rfl) ⟨8925146, by rfl⟩ : syracuseStep 11900195 = 17850293) B17850293
theorem B19076417 : Blo 1566981 19076417 := bstep (se 2 (by rfl) ⟨7153656, by rfl⟩ : syracuseStep 19076417 = 14307313) B14307313
theorem B6698371 : Blo 1566981 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B3528089 : Blo 1566981 3528089 := bstep (se 2 (by rfl) ⟨1323033, by rfl⟩ : syracuseStep 3528089 = 2646067) B2646067
theorem B3347905 : Blo 1566981 3347905 := bstep (se 2 (by rfl) ⟨1255464, by rfl⟩ : syracuseStep 3347905 = 2510929) B2510929
theorem B3528179 : Blo 1566981 3528179 := bstep (se 1 (by rfl) ⟨2646134, by rfl⟩ : syracuseStep 3528179 = 5292269) B5292269
theorem B3528215 : Blo 1566981 3528215 := bstep (se 1 (by rfl) ⟨2646161, by rfl⟩ : syracuseStep 3528215 = 5292323) B5292323
theorem B3577367 : Blo 1566981 3577367 := bstep (se 1 (by rfl) ⟨2683025, by rfl⟩ : syracuseStep 3577367 = 5366051) B5366051
theorem B5289623 : Blo 1566981 5289623 := bstep (se 1 (by rfl) ⟨3967217, by rfl⟩ : syracuseStep 5289623 = 7934435) B7934435
theorem B3528395 : Blo 1566981 3528395 := bstep (se 1 (by rfl) ⟨2646296, by rfl⟩ : syracuseStep 3528395 = 5292593) B5292593
theorem B6698713 : Blo 1566981 6698713 := bstep (se 2 (by rfl) ⟨2512017, by rfl⟩ : syracuseStep 6698713 = 5024035) B5024035
theorem B3528449 : Blo 1566981 3528449 := bstep (se 2 (by rfl) ⟨1323168, by rfl⟩ : syracuseStep 3528449 = 2646337) B2646337
theorem B9049873 : Blo 1566981 9049873 := bstep (se 2 (by rfl) ⟨3393702, by rfl⟩ : syracuseStep 9049873 = 6787405) B6787405
theorem B3766105 : Blo 1566981 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B335026061 : Blo 1566981 335026061 := bstep (se 3 (by rfl) ⟨62817386, by rfl⟩ : syracuseStep 335026061 = 125634773) B125634773
theorem B3766219 : Blo 1566981 3766219 := bstep (se 1 (by rfl) ⟨2824664, by rfl⟩ : syracuseStep 3766219 = 5649329) B5649329
theorem B3528665 : Blo 1566981 3528665 := bstep (se 2 (by rfl) ⟨1323249, by rfl⟩ : syracuseStep 3528665 = 2646499) B2646499
theorem B11606051 : Blo 1566981 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B3528755 : Blo 1566981 3528755 := bstep (se 1 (by rfl) ⟨2646566, by rfl⟩ : syracuseStep 3528755 = 5293133) B5293133
theorem B3528791 : Blo 1566981 3528791 := bstep (se 1 (by rfl) ⟨2646593, by rfl⟩ : syracuseStep 3528791 = 5293187) B5293187
theorem B3348631 : Blo 1566981 3348631 := bstep (se 1 (by rfl) ⟨2511473, by rfl⟩ : syracuseStep 3348631 = 5022947) B5022947
theorem B5290163 : Blo 1566981 5290163 := bstep (se 1 (by rfl) ⟨3967622, by rfl⟩ : syracuseStep 5290163 = 7935245) B7935245
theorem B7936217 : Blo 1566981 7936217 := bstep (se 2 (by rfl) ⟨2976081, by rfl⟩ : syracuseStep 7936217 = 5952163) B5952163
theorem B3528971 : Blo 1566981 3528971 := bstep (se 1 (by rfl) ⟨2646728, by rfl⟩ : syracuseStep 3528971 = 5293457) B5293457
theorem B3529025 : Blo 1566981 3529025 := bstep (se 2 (by rfl) ⟨1323384, by rfl⟩ : syracuseStep 3529025 = 2646769) B2646769
theorem B3176857 : Blo 1566981 3176857 := bstep (se 2 (by rfl) ⟨1191321, by rfl⟩ : syracuseStep 3176857 = 2382643) B2382643
theorem B5290433 : Blo 1566981 5290433 := bstep (se 2 (by rfl) ⟨1983912, by rfl⟩ : syracuseStep 5290433 = 3967825) B3967825
theorem B2644427 : Blo 1566981 2644427 := bstep (se 1 (by rfl) ⟨1983320, by rfl⟩ : syracuseStep 2644427 = 3966641) B3966641
theorem B3529241 : Blo 1566981 3529241 := bstep (se 2 (by rfl) ⟨1323465, by rfl⟩ : syracuseStep 3529241 = 2646931) B2646931
theorem B5954093 : Blo 1566981 5954093 := bstep (se 3 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 5954093 = 2232785) B2232785
theorem B2644555 : Blo 1566981 2644555 := bstep (se 1 (by rfl) ⟨1983416, by rfl⟩ : syracuseStep 2644555 = 3966833) B3966833
theorem B5364299 : Blo 1566981 5364299 := bstep (se 1 (by rfl) ⟨4023224, by rfl⟩ : syracuseStep 5364299 = 8046449) B8046449
theorem B2120267 : Blo 1566981 2120267 := bstep (se 1 (by rfl) ⟨1590200, by rfl⟩ : syracuseStep 2120267 = 3180401) B3180401
theorem B3529331 : Blo 1566981 3529331 := bstep (se 1 (by rfl) ⟨2646998, by rfl⟩ : syracuseStep 3529331 = 5293997) B5293997
theorem B6699671 : Blo 1566981 6699671 := bstep (se 1 (by rfl) ⟨5024753, by rfl⟩ : syracuseStep 6699671 = 10049507) B10049507
theorem B3529367 : Blo 1566981 3529367 := bstep (se 1 (by rfl) ⟨2647025, by rfl⟩ : syracuseStep 3529367 = 5294051) B5294051
theorem B2644697 : Blo 1566981 2644697 := bstep (se 2 (by rfl) ⟨991761, by rfl⟩ : syracuseStep 2644697 = 1983523) B1983523
theorem B4463383 : Blo 1566981 4463383 := bstep (se 1 (by rfl) ⟨3347537, by rfl⟩ : syracuseStep 4463383 = 6695075) B6695075
theorem B6445889 : Blo 1566981 6445889 := bstep (se 2 (by rfl) ⟨2417208, by rfl⟩ : syracuseStep 6445889 = 4834417) B4834417
theorem B3529547 : Blo 1566981 3529547 := bstep (se 1 (by rfl) ⟨2647160, by rfl⟩ : syracuseStep 3529547 = 5294321) B5294321
theorem B2644825 : Blo 1566981 2644825 := bstep (se 2 (by rfl) ⟨991809, by rfl⟩ : syracuseStep 2644825 = 1983619) B1983619
theorem B3529601 : Blo 1566981 3529601 := bstep (se 2 (by rfl) ⟨1323600, by rfl⟩ : syracuseStep 3529601 = 2647201) B2647201
theorem B3349451 : Blo 1566981 3349451 := bstep (se 1 (by rfl) ⟨2512088, by rfl⟩ : syracuseStep 3349451 = 5024177) B5024177
theorem B2825177 : Blo 1566981 2825177 := bstep (se 2 (by rfl) ⟨1059441, by rfl⟩ : syracuseStep 2825177 = 2118883) B2118883
theorem B5290973 : Blo 1566981 5290973 := bstep (se 3 (by rfl) ⟨992057, by rfl⟩ : syracuseStep 5290973 = 1984115) B1984115
theorem B3529817 : Blo 1566981 3529817 := bstep (se 2 (by rfl) ⟨1323681, by rfl⟩ : syracuseStep 3529817 = 2647363) B2647363
theorem B45227159 : Blo 1566981 45227159 := bstep (se 1 (by rfl) ⟨33920369, by rfl⟩ : syracuseStep 45227159 = 67840739) B67840739
theorem B3529907 : Blo 1566981 3529907 := bstep (se 1 (by rfl) ⟨2647430, by rfl⟩ : syracuseStep 3529907 = 5294861) B5294861
theorem B3529943 : Blo 1566981 3529943 := bstep (se 1 (by rfl) ⟨2647457, by rfl⟩ : syracuseStep 3529943 = 5294915) B5294915
theorem B6036697 : Blo 1566981 6036697 := bstep (se 2 (by rfl) ⟨2263761, by rfl⟩ : syracuseStep 6036697 = 4527523) B4527523
theorem B13401389 : Blo 1566981 13401389 := bstep (se 3 (by rfl) ⟨2512760, by rfl⟩ : syracuseStep 13401389 = 5025521) B5025521
theorem B5954867 : Blo 1566981 5954867 := bstep (se 1 (by rfl) ⟨4466150, by rfl⟩ : syracuseStep 5954867 = 8932301) B8932301
theorem B1588567 : Blo 1566981 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B2825587 : Blo 1566981 2825587 := bstep (se 1 (by rfl) ⟨2119190, by rfl⟩ : syracuseStep 2825587 = 4238381) B4238381
theorem B2350475 : Blo 1566981 2350475 := bstep (se 1 (by rfl) ⟨1762856, by rfl⟩ : syracuseStep 2350475 = 3525713) B3525713
theorem B3530123 : Blo 1566981 3530123 := bstep (se 1 (by rfl) ⟨2647592, by rfl⟩ : syracuseStep 3530123 = 5295185) B5295185
theorem B2350487 : Blo 1566981 2350487 := bstep (se 1 (by rfl) ⟨1762865, by rfl⟩ : syracuseStep 2350487 = 3525731) B3525731
theorem B2645399 : Blo 1566981 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B3530177 : Blo 1566981 3530177 := bstep (se 2 (by rfl) ⟨1323816, by rfl⟩ : syracuseStep 3530177 = 2647633) B2647633
theorem B2825675 : Blo 1566981 2825675 := bstep (se 1 (by rfl) ⟨2119256, by rfl⟩ : syracuseStep 2825675 = 4238513) B4238513
theorem B2350553 : Blo 1566981 2350553 := bstep (se 2 (by rfl) ⟨881457, by rfl⟩ : syracuseStep 2350553 = 1762915) B1762915
theorem B10042841 : Blo 1566981 10042841 := bstep (se 2 (by rfl) ⟨3766065, by rfl⟩ : syracuseStep 10042841 = 7532131) B7532131
theorem B2645527 : Blo 1566981 2645527 := bstep (se 1 (by rfl) ⟨1984145, by rfl⟩ : syracuseStep 2645527 = 3968291) B3968291
theorem B2350667 : Blo 1566981 2350667 := bstep (se 1 (by rfl) ⟨1763000, by rfl⟩ : syracuseStep 2350667 = 3526001) B3526001
theorem B2350679 : Blo 1566981 2350679 := bstep (se 1 (by rfl) ⟨1763009, by rfl⟩ : syracuseStep 2350679 = 3526019) B3526019
theorem B38125187 : Blo 1566981 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B2350745 : Blo 1566981 2350745 := bstep (se 2 (by rfl) ⟨881529, by rfl⟩ : syracuseStep 2350745 = 1763059) B1763059
theorem B1588907 : Blo 1566981 1588907 := bstep (se 1 (by rfl) ⟨1191680, by rfl⟩ : syracuseStep 1588907 = 2383361) B2383361
theorem B8044211 : Blo 1566981 8044211 := bstep (se 1 (by rfl) ⟨6033158, by rfl⟩ : syracuseStep 8044211 = 12066317) B12066317
theorem B1588939 : Blo 1566981 1588939 := bstep (se 1 (by rfl) ⟨1191704, by rfl⟩ : syracuseStep 1588939 = 2383409) B2383409
theorem B2350859 : Blo 1566981 2350859 := bstep (se 1 (by rfl) ⟨1763144, by rfl⟩ : syracuseStep 2350859 = 3526289) B3526289
theorem B2350871 : Blo 1566981 2350871 := bstep (se 1 (by rfl) ⟨1763153, by rfl⟩ : syracuseStep 2350871 = 3526307) B3526307
theorem B3350297 : Blo 1566981 3350297 := bstep (se 2 (by rfl) ⟨1256361, by rfl⟩ : syracuseStep 3350297 = 2512723) B2512723
theorem B7937837 : Blo 1566981 7937837 := bstep (se 3 (by rfl) ⟨1488344, by rfl⟩ : syracuseStep 7937837 = 2976689) B2976689
theorem B2350937 : Blo 1566981 2350937 := bstep (se 2 (by rfl) ⟨881601, by rfl⟩ : syracuseStep 2350937 = 1763203) B1763203
theorem B2351051 : Blo 1566981 2351051 := bstep (se 1 (by rfl) ⟨1763288, by rfl⟩ : syracuseStep 2351051 = 3526577) B3526577
theorem B2351063 : Blo 1566981 2351063 := bstep (se 1 (by rfl) ⟨1763297, by rfl⟩ : syracuseStep 2351063 = 3526595) B3526595
theorem B1589239 : Blo 1566981 1589239 := bstep (se 1 (by rfl) ⟨1191929, by rfl⟩ : syracuseStep 1589239 = 2383859) B2383859
theorem B4022273 : Blo 1566981 4022273 := bstep (se 2 (by rfl) ⟨1508352, by rfl⟩ : syracuseStep 4022273 = 3016705) B3016705
theorem B2351111 : Blo 1566981 2351111 := bstep (se 1 (by rfl) ⟨1763333, by rfl⟩ : syracuseStep 2351111 = 3526667) B3526667
theorem B33906701 : Blo 1566981 33906701 := bstep (se 3 (by rfl) ⟨6357506, by rfl⟩ : syracuseStep 33906701 = 12715013) B12715013
theorem B1589263 : Blo 1566981 1589263 := bstep (se 1 (by rfl) ⟨1191947, by rfl⟩ : syracuseStep 1589263 = 2383895) B2383895
theorem B3768335 : Blo 1566981 3768335 := bstep (se 1 (by rfl) ⟨2826251, by rfl⟩ : syracuseStep 3768335 = 5652503) B5652503
theorem B2351147 : Blo 1566981 2351147 := bstep (se 1 (by rfl) ⟨1763360, by rfl⟩ : syracuseStep 2351147 = 3526721) B3526721
theorem B3350587 : Blo 1566981 3350587 := bstep (se 1 (by rfl) ⟨2512940, by rfl⟩ : syracuseStep 3350587 = 5025881) B5025881
theorem B15065149 : Blo 1566981 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B2351177 : Blo 1566981 2351177 := bstep (se 2 (by rfl) ⟨881691, by rfl⟩ : syracuseStep 2351177 = 1763383) B1763383
theorem B2351291 : Blo 1566981 2351291 := bstep (se 1 (by rfl) ⟨1763468, by rfl⟩ : syracuseStep 2351291 = 3526937) B3526937
theorem B4464841 : Blo 1566981 4464841 := bstep (se 2 (by rfl) ⟨1674315, by rfl⟩ : syracuseStep 4464841 = 3348631) B3348631
theorem B2351351 : Blo 1566981 2351351 := bstep (se 1 (by rfl) ⟨1763513, by rfl⟩ : syracuseStep 2351351 = 3527027) B3527027
theorem B2351375 : Blo 1566981 2351375 := bstep (se 1 (by rfl) ⟨1763531, by rfl⟩ : syracuseStep 2351375 = 3527063) B3527063
theorem B2351417 : Blo 1566981 2351417 := bstep (se 2 (by rfl) ⟨881781, by rfl⟩ : syracuseStep 2351417 = 1763563) B1763563
theorem B1884475 : Blo 1566981 1884475 := bstep (se 1 (by rfl) ⟨1413356, by rfl⟩ : syracuseStep 1884475 = 2826713) B2826713
theorem B2646391 : Blo 1566981 2646391 := bstep (se 1 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 2646391 = 3969587) B3969587
theorem B2351495 : Blo 1566981 2351495 := bstep (se 1 (by rfl) ⟨1763621, by rfl⟩ : syracuseStep 2351495 = 3527243) B3527243
theorem B6701447 : Blo 1566981 6701447 := bstep (se 1 (by rfl) ⟨5026085, by rfl⟩ : syracuseStep 6701447 = 10052171) B10052171
theorem B2351531 : Blo 1566981 2351531 := bstep (se 1 (by rfl) ⟨1763648, by rfl⟩ : syracuseStep 2351531 = 3527297) B3527297
theorem B2351561 : Blo 1566981 2351561 := bstep (se 2 (by rfl) ⟨881835, by rfl⟩ : syracuseStep 2351561 = 1763671) B1763671
theorem B4235809 : Blo 1566981 4235809 := bstep (se 2 (by rfl) ⟨1588428, by rfl⟩ : syracuseStep 4235809 = 3176857) B3176857
theorem B2351675 : Blo 1566981 2351675 := bstep (se 1 (by rfl) ⟨1763756, by rfl⟩ : syracuseStep 2351675 = 3527513) B3527513
theorem B2646587 : Blo 1566981 2646587 := bstep (se 1 (by rfl) ⟨1984940, by rfl⟩ : syracuseStep 2646587 = 3969881) B3969881
theorem B7938647 : Blo 1566981 7938647 := bstep (se 1 (by rfl) ⟨5953985, by rfl⟩ : syracuseStep 7938647 = 11907971) B11907971
theorem B2351735 : Blo 1566981 2351735 := bstep (se 1 (by rfl) ⟨1763801, by rfl⟩ : syracuseStep 2351735 = 3527603) B3527603
theorem B6701687 : Blo 1566981 6701687 := bstep (se 1 (by rfl) ⟨5026265, by rfl⟩ : syracuseStep 6701687 = 10052531) B10052531
theorem B2351759 : Blo 1566981 2351759 := bstep (se 1 (by rfl) ⟨1763819, by rfl⟩ : syracuseStep 2351759 = 3527639) B3527639
theorem B2351801 : Blo 1566981 2351801 := bstep (se 2 (by rfl) ⟨881925, by rfl⟩ : syracuseStep 2351801 = 1763851) B1763851
theorem B2351879 : Blo 1566981 2351879 := bstep (se 1 (by rfl) ⟨1763909, by rfl⟩ : syracuseStep 2351879 = 3527819) B3527819
theorem B4236047 : Blo 1566981 4236047 := bstep (se 1 (by rfl) ⟨3177035, by rfl⟩ : syracuseStep 4236047 = 6354071) B6354071
theorem B14312207 : Blo 1566981 14312207 := bstep (se 1 (by rfl) ⟨10734155, by rfl⟩ : syracuseStep 14312207 = 21468311) B21468311
theorem B76251941 : Blo 1566981 76251941 := bstep (se 4 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 76251941 = 14297239) B14297239
theorem B2351915 : Blo 1566981 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B2351945 : Blo 1566981 2351945 := bstep (se 2 (by rfl) ⟨881979, by rfl⟩ : syracuseStep 2351945 = 1763959) B1763959
theorem B5956537 : Blo 1566981 5956537 := bstep (se 2 (by rfl) ⟨2233701, by rfl⟩ : syracuseStep 5956537 = 4467403) B4467403
theorem B2352059 : Blo 1566981 2352059 := bstep (se 1 (by rfl) ⟨1764044, by rfl⟩ : syracuseStep 2352059 = 3528089) B3528089
theorem B2646985 : Blo 1566981 2646985 := bstep (se 2 (by rfl) ⟨992619, by rfl⟩ : syracuseStep 2646985 = 1985239) B1985239
theorem B2352119 : Blo 1566981 2352119 := bstep (se 1 (by rfl) ⟨1764089, by rfl⟩ : syracuseStep 2352119 = 3528179) B3528179
theorem B3015695 : Blo 1566981 3015695 := bstep (se 1 (by rfl) ⟨2261771, by rfl⟩ : syracuseStep 3015695 = 4523543) B4523543
theorem B2352143 : Blo 1566981 2352143 := bstep (se 1 (by rfl) ⟨1764107, by rfl⟩ : syracuseStep 2352143 = 3528215) B3528215
theorem B2384911 : Blo 1566981 2384911 := bstep (se 1 (by rfl) ⟨1788683, by rfl⟩ : syracuseStep 2384911 = 3577367) B3577367
theorem B2352185 : Blo 1566981 2352185 := bstep (se 2 (by rfl) ⟨882069, by rfl⟩ : syracuseStep 2352185 = 1764139) B1764139
theorem B7939133 : Blo 1566981 7939133 := bstep (se 3 (by rfl) ⟨1488587, by rfl⟩ : syracuseStep 7939133 = 2977175) B2977175
theorem B2352263 : Blo 1566981 2352263 := bstep (se 1 (by rfl) ⟨1764197, by rfl⟩ : syracuseStep 2352263 = 3528395) B3528395
theorem B2352299 : Blo 1566981 2352299 := bstep (se 1 (by rfl) ⟨1764224, by rfl⟩ : syracuseStep 2352299 = 3528449) B3528449
theorem B2352329 : Blo 1566981 2352329 := bstep (se 2 (by rfl) ⟨882123, by rfl⟩ : syracuseStep 2352329 = 1764247) B1764247
theorem B10323233 : Blo 1566981 10323233 := bstep (se 2 (by rfl) ⟨3871212, by rfl⟩ : syracuseStep 10323233 = 7742425) B7742425
theorem B4769057 : Blo 1566981 4769057 := bstep (se 2 (by rfl) ⟨1788396, by rfl⟩ : syracuseStep 4769057 = 3576793) B3576793
theorem B2352443 : Blo 1566981 2352443 := bstep (se 1 (by rfl) ⟨1764332, by rfl⟩ : syracuseStep 2352443 = 3528665) B3528665
theorem B171738481 : Blo 1566981 171738481 := bstep (se 2 (by rfl) ⟨64401930, by rfl⟩ : syracuseStep 171738481 = 128803861) B128803861
theorem B2352503 : Blo 1566981 2352503 := bstep (se 1 (by rfl) ⟨1764377, by rfl⟩ : syracuseStep 2352503 = 3528755) B3528755
theorem B2352527 : Blo 1566981 2352527 := bstep (se 1 (by rfl) ⟨1764395, by rfl⟩ : syracuseStep 2352527 = 3528791) B3528791
theorem B2352569 : Blo 1566981 2352569 := bstep (se 2 (by rfl) ⟨882213, by rfl⟩ : syracuseStep 2352569 = 1764427) B1764427
theorem B7538129 : Blo 1566981 7538129 := bstep (se 2 (by rfl) ⟨2826798, by rfl⟩ : syracuseStep 7538129 = 5653597) B5653597
theorem B4023809 : Blo 1566981 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B2352647 : Blo 1566981 2352647 := bstep (se 1 (by rfl) ⟨1764485, by rfl⟩ : syracuseStep 2352647 = 3528971) B3528971
theorem B3966479 : Blo 1566981 3966479 := bstep (se 1 (by rfl) ⟨2974859, by rfl⟩ : syracuseStep 3966479 = 5949719) B5949719
theorem B5654045 : Blo 1566981 5654045 := bstep (se 3 (by rfl) ⟨1060133, by rfl⟩ : syracuseStep 5654045 = 2120267) B2120267
theorem B2352683 : Blo 1566981 2352683 := bstep (se 1 (by rfl) ⟨1764512, by rfl⟩ : syracuseStep 2352683 = 3529025) B3529025
theorem B2352713 : Blo 1566981 2352713 := bstep (se 2 (by rfl) ⟨882267, by rfl⟩ : syracuseStep 2352713 = 1764535) B1764535
theorem B1762951 : Blo 1566981 1762951 := bstep (se 1 (by rfl) ⟨1322213, by rfl⟩ : syracuseStep 1762951 = 2644427) B2644427
theorem B1984171 : Blo 1566981 1984171 := bstep (se 1 (by rfl) ⟨1488128, by rfl⟩ : syracuseStep 1984171 = 2976257) B2976257
theorem B2352827 : Blo 1566981 2352827 := bstep (se 1 (by rfl) ⟨1764620, by rfl⟩ : syracuseStep 2352827 = 3529241) B3529241
theorem B2352887 : Blo 1566981 2352887 := bstep (se 1 (by rfl) ⟨1764665, by rfl⟩ : syracuseStep 2352887 = 3529331) B3529331
theorem B4466447 : Blo 1566981 4466447 := bstep (se 1 (by rfl) ⟨3349835, by rfl⟩ : syracuseStep 4466447 = 6699671) B6699671
theorem B2352911 : Blo 1566981 2352911 := bstep (se 1 (by rfl) ⟨1764683, by rfl⟩ : syracuseStep 2352911 = 3529367) B3529367
theorem B4237085 : Blo 1566981 4237085 := bstep (se 3 (by rfl) ⟨794453, by rfl⟩ : syracuseStep 4237085 = 1588907) B1588907
theorem B2352953 : Blo 1566981 2352953 := bstep (se 2 (by rfl) ⟨882357, by rfl⟩ : syracuseStep 2352953 = 1764715) B1764715
theorem B1763131 : Blo 1566981 1763131 := bstep (se 1 (by rfl) ⟨1322348, by rfl⟩ : syracuseStep 1763131 = 2644697) B2644697
theorem B8931161 : Blo 1566981 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B2353031 : Blo 1566981 2353031 := bstep (se 1 (by rfl) ⟨1764773, by rfl⟩ : syracuseStep 2353031 = 3529547) B3529547
theorem B2353067 : Blo 1566981 2353067 := bstep (se 1 (by rfl) ⟨1764800, by rfl⟩ : syracuseStep 2353067 = 3529601) B3529601
theorem B2353097 : Blo 1566981 2353097 := bstep (se 2 (by rfl) ⟨882411, by rfl⟩ : syracuseStep 2353097 = 1764823) B1764823
theorem B2353211 : Blo 1566981 2353211 := bstep (se 1 (by rfl) ⟨1764908, by rfl⟩ : syracuseStep 2353211 = 3529817) B3529817
theorem B2353271 : Blo 1566981 2353271 := bstep (se 1 (by rfl) ⟨1764953, by rfl⟩ : syracuseStep 2353271 = 3529907) B3529907
theorem B2353295 : Blo 1566981 2353295 := bstep (se 1 (by rfl) ⟨1764971, by rfl⟩ : syracuseStep 2353295 = 3529943) B3529943
theorem B2353337 : Blo 1566981 2353337 := bstep (se 2 (by rfl) ⟨882501, by rfl⟩ : syracuseStep 2353337 = 1765003) B1765003
theorem B3967177 : Blo 1566981 3967177 := bstep (se 2 (by rfl) ⟨1487691, by rfl⟩ : syracuseStep 3967177 = 2975383) B2975383
theorem B1566983 : Blo 1566981 1566983 := bstep (se 1 (by rfl) ⟨1175237, by rfl⟩ : syracuseStep 1566983 = 2350475) B2350475
theorem B2353415 : Blo 1566981 2353415 := bstep (se 1 (by rfl) ⟨1765061, by rfl⟩ : syracuseStep 2353415 = 3530123) B3530123
theorem B1566991 : Blo 1566981 1566991 := bstep (se 1 (by rfl) ⟨1175243, by rfl⟩ : syracuseStep 1566991 = 2350487) B2350487
theorem B1763599 : Blo 1566981 1763599 := bstep (se 1 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 1763599 = 2645399) B2645399
theorem B8931617 : Blo 1566981 8931617 := bstep (se 2 (by rfl) ⟨3349356, by rfl⟩ : syracuseStep 8931617 = 6698713) B6698713
theorem B2353451 : Blo 1566981 2353451 := bstep (se 1 (by rfl) ⟨1765088, by rfl⟩ : syracuseStep 2353451 = 3530177) B3530177
theorem B1567035 : Blo 1566981 1567035 := bstep (se 1 (by rfl) ⟨1175276, by rfl⟩ : syracuseStep 1567035 = 2350553) B2350553
theorem B6695227 : Blo 1566981 6695227 := bstep (se 1 (by rfl) ⟨5021420, by rfl⟩ : syracuseStep 6695227 = 10042841) B10042841
theorem B3967319 : Blo 1566981 3967319 := bstep (se 1 (by rfl) ⟨2975489, by rfl⟩ : syracuseStep 3967319 = 5950979) B5950979
theorem B1567111 : Blo 1566981 1567111 := bstep (se 1 (by rfl) ⟨1175333, by rfl⟩ : syracuseStep 1567111 = 2350667) B2350667
theorem B1567119 : Blo 1566981 1567119 := bstep (se 1 (by rfl) ⟨1175339, by rfl⟩ : syracuseStep 1567119 = 2350679) B2350679
theorem B5294483 : Blo 1566981 5294483 := bstep (se 1 (by rfl) ⟨3970862, by rfl⟩ : syracuseStep 5294483 = 7941725) B7941725
theorem B1567163 : Blo 1566981 1567163 := bstep (se 1 (by rfl) ⟨1175372, by rfl⟩ : syracuseStep 1567163 = 2350745) B2350745
theorem B1567239 : Blo 1566981 1567239 := bstep (se 1 (by rfl) ⟨1175429, by rfl⟩ : syracuseStep 1567239 = 2350859) B2350859
theorem B1567247 : Blo 1566981 1567247 := bstep (se 1 (by rfl) ⟨1175435, by rfl⟩ : syracuseStep 1567247 = 2350871) B2350871
theorem B8931869 : Blo 1566981 8931869 := bstep (se 3 (by rfl) ⟨1674725, by rfl⟩ : syracuseStep 8931869 = 3349451) B3349451
theorem B1567291 : Blo 1566981 1567291 := bstep (se 1 (by rfl) ⟨1175468, by rfl⟩ : syracuseStep 1567291 = 2350937) B2350937
theorem B1985143 : Blo 1566981 1985143 := bstep (se 1 (by rfl) ⟨1488857, by rfl⟩ : syracuseStep 1985143 = 2977715) B2977715
theorem B1567367 : Blo 1566981 1567367 := bstep (se 1 (by rfl) ⟨1175525, by rfl⟩ : syracuseStep 1567367 = 2351051) B2351051
theorem B1567375 : Blo 1566981 1567375 := bstep (se 1 (by rfl) ⟨1175531, by rfl⟩ : syracuseStep 1567375 = 2351063) B2351063
theorem B1567419 : Blo 1566981 1567419 := bstep (se 1 (by rfl) ⟨1175564, by rfl⟩ : syracuseStep 1567419 = 2351129) B2351129
theorem B1567495 : Blo 1566981 1567495 := bstep (se 1 (by rfl) ⟨1175621, by rfl⟩ : syracuseStep 1567495 = 2351243) B2351243
theorem B1764103 : Blo 1566981 1764103 := bstep (se 1 (by rfl) ⟨1323077, by rfl⟩ : syracuseStep 1764103 = 2646155) B2646155
theorem B1567503 : Blo 1566981 1567503 := bstep (se 1 (by rfl) ⟨1175627, by rfl⟩ : syracuseStep 1567503 = 2351255) B2351255
theorem B12716837 : Blo 1566981 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B7940915 : Blo 1566981 7940915 := bstep (se 1 (by rfl) ⟨5955686, by rfl⟩ : syracuseStep 7940915 = 11911373) B11911373
theorem B1567547 : Blo 1566981 1567547 := bstep (se 1 (by rfl) ⟨1175660, by rfl⟩ : syracuseStep 1567547 = 2351321) B2351321
theorem B4467575 : Blo 1566981 4467575 := bstep (se 1 (by rfl) ⟨3350681, by rfl⟩ : syracuseStep 4467575 = 6701363) B6701363
theorem B1567623 : Blo 1566981 1567623 := bstep (se 1 (by rfl) ⟨1175717, by rfl⟩ : syracuseStep 1567623 = 2351435) B2351435
theorem B1567631 : Blo 1566981 1567631 := bstep (se 1 (by rfl) ⟨1175723, by rfl⟩ : syracuseStep 1567631 = 2351447) B2351447
theorem B2976659 : Blo 1566981 2976659 := bstep (se 1 (by rfl) ⟨2232494, by rfl⟩ : syracuseStep 2976659 = 4464989) B4464989
theorem B1567675 : Blo 1566981 1567675 := bstep (se 1 (by rfl) ⟨1175756, by rfl⟩ : syracuseStep 1567675 = 2351513) B2351513
theorem B1764283 : Blo 1566981 1764283 := bstep (se 1 (by rfl) ⟨1323212, by rfl⟩ : syracuseStep 1764283 = 2646425) B2646425
theorem B1985467 : Blo 1566981 1985467 := bstep (se 1 (by rfl) ⟨1489100, by rfl⟩ : syracuseStep 1985467 = 2978201) B2978201
theorem B1567751 : Blo 1566981 1567751 := bstep (se 1 (by rfl) ⟨1175813, by rfl⟩ : syracuseStep 1567751 = 2351627) B2351627
theorem B1567759 : Blo 1566981 1567759 := bstep (se 1 (by rfl) ⟨1175819, by rfl⟩ : syracuseStep 1567759 = 2351639) B2351639
theorem B13397015 : Blo 1566981 13397015 := bstep (se 1 (by rfl) ⟨10047761, by rfl⟩ : syracuseStep 13397015 = 20095523) B20095523
theorem B5950493 : Blo 1566981 5950493 := bstep (se 3 (by rfl) ⟨1115717, by rfl⟩ : syracuseStep 5950493 = 2231435) B2231435
theorem B1567803 : Blo 1566981 1567803 := bstep (se 1 (by rfl) ⟨1175852, by rfl⟩ : syracuseStep 1567803 = 2351705) B2351705
theorem B5024855 : Blo 1566981 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B2976887 : Blo 1566981 2976887 := bstep (se 1 (by rfl) ⟨2232665, by rfl⟩ : syracuseStep 2976887 = 4465331) B4465331
theorem B7941239 : Blo 1566981 7941239 := bstep (se 1 (by rfl) ⟨5955929, by rfl⟩ : syracuseStep 7941239 = 11911859) B11911859
theorem B3525767 : Blo 1566981 3525767 := bstep (se 1 (by rfl) ⟨2644325, by rfl⟩ : syracuseStep 3525767 = 5288651) B5288651
theorem B1567879 : Blo 1566981 1567879 := bstep (se 1 (by rfl) ⟨1175909, by rfl⟩ : syracuseStep 1567879 = 2351819) B2351819
theorem B1567887 : Blo 1566981 1567887 := bstep (se 1 (by rfl) ⟨1175915, by rfl⟩ : syracuseStep 1567887 = 2351831) B2351831
theorem B1567931 : Blo 1566981 1567931 := bstep (se 1 (by rfl) ⟨1175948, by rfl⟩ : syracuseStep 1567931 = 2351897) B2351897
theorem B1568007 : Blo 1566981 1568007 := bstep (se 1 (by rfl) ⟨1176005, by rfl⟩ : syracuseStep 1568007 = 2352011) B2352011
theorem B1568015 : Blo 1566981 1568015 := bstep (se 1 (by rfl) ⟨1176011, by rfl⟩ : syracuseStep 1568015 = 2352023) B2352023
theorem B4295969 : Blo 1566981 4295969 := bstep (se 2 (by rfl) ⟨1610988, by rfl⟩ : syracuseStep 4295969 = 3221977) B3221977
theorem B3525947 : Blo 1566981 3525947 := bstep (se 1 (by rfl) ⟨2644460, by rfl⟩ : syracuseStep 3525947 = 5288921) B5288921
theorem B1568059 : Blo 1566981 1568059 := bstep (se 1 (by rfl) ⟨1176044, by rfl⟩ : syracuseStep 1568059 = 2352089) B2352089
theorem B1568135 : Blo 1566981 1568135 := bstep (se 1 (by rfl) ⟨1176101, by rfl⟩ : syracuseStep 1568135 = 2352203) B2352203
theorem B1568143 : Blo 1566981 1568143 := bstep (se 1 (by rfl) ⟨1176107, by rfl⟩ : syracuseStep 1568143 = 2352215) B2352215
theorem B1764751 : Blo 1566981 1764751 := bstep (se 1 (by rfl) ⟨1323563, by rfl⟩ : syracuseStep 1764751 = 2647127) B2647127
theorem B3526073 : Blo 1566981 3526073 := bstep (se 2 (by rfl) ⟨1322277, by rfl⟩ : syracuseStep 3526073 = 2644555) B2644555
theorem B1568187 : Blo 1566981 1568187 := bstep (se 1 (by rfl) ⟨1176140, by rfl⟩ : syracuseStep 1568187 = 2352281) B2352281
theorem B11906513 : Blo 1566981 11906513 := bstep (se 2 (by rfl) ⟨4464942, by rfl⟩ : syracuseStep 11906513 = 8929885) B8929885
theorem B1568263 : Blo 1566981 1568263 := bstep (se 1 (by rfl) ⟨1176197, by rfl⟩ : syracuseStep 1568263 = 2352395) B2352395
theorem B1568271 : Blo 1566981 1568271 := bstep (se 1 (by rfl) ⟨1176203, by rfl⟩ : syracuseStep 1568271 = 2352407) B2352407
theorem B7933463 : Blo 1566981 7933463 := bstep (se 1 (by rfl) ⟨5950097, by rfl⟩ : syracuseStep 7933463 = 11900195) B11900195
theorem B24129053 : Blo 1566981 24129053 := bstep (se 3 (by rfl) ⟨4524197, by rfl⟩ : syracuseStep 24129053 = 9048395) B9048395
theorem B12717611 : Blo 1566981 12717611 := bstep (se 1 (by rfl) ⟨9538208, by rfl⟩ : syracuseStep 12717611 = 19076417) B19076417
theorem B1568315 : Blo 1566981 1568315 := bstep (se 1 (by rfl) ⟨1176236, by rfl⟩ : syracuseStep 1568315 = 2352473) B2352473
theorem B1568391 : Blo 1566981 1568391 := bstep (se 1 (by rfl) ⟨1176293, by rfl⟩ : syracuseStep 1568391 = 2352587) B2352587
theorem B1568399 : Blo 1566981 1568399 := bstep (se 1 (by rfl) ⟨1176299, by rfl⟩ : syracuseStep 1568399 = 2352599) B2352599
theorem B2231993 : Blo 1566981 2231993 := bstep (se 2 (by rfl) ⟨836997, by rfl⟩ : syracuseStep 2231993 = 1673995) B1673995
theorem B1568443 : Blo 1566981 1568443 := bstep (se 1 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 1568443 = 2352665) B2352665
theorem B5951177 : Blo 1566981 5951177 := bstep (se 2 (by rfl) ⟨2231691, by rfl⟩ : syracuseStep 5951177 = 4463383) B4463383
theorem B4525769 : Blo 1566981 4525769 := bstep (se 2 (by rfl) ⟨1697163, by rfl⟩ : syracuseStep 4525769 = 3394327) B3394327
theorem B8474341 : Blo 1566981 8474341 := bstep (se 4 (by rfl) ⟨794469, by rfl⟩ : syracuseStep 8474341 = 1588939) B1588939
theorem B9539329 : Blo 1566981 9539329 := bstep (se 2 (by rfl) ⟨3577248, by rfl⟩ : syracuseStep 9539329 = 7154497) B7154497
theorem B1568519 : Blo 1566981 1568519 := bstep (se 1 (by rfl) ⟨1176389, by rfl⟩ : syracuseStep 1568519 = 2352779) B2352779
theorem B3526415 : Blo 1566981 3526415 := bstep (se 1 (by rfl) ⟨2644811, by rfl⟩ : syracuseStep 3526415 = 5289623) B5289623
theorem B1568527 : Blo 1566981 1568527 := bstep (se 1 (by rfl) ⟨1176395, by rfl⟩ : syracuseStep 1568527 = 2352791) B2352791
theorem B3526433 : Blo 1566981 3526433 := bstep (se 2 (by rfl) ⟨1322412, by rfl⟩ : syracuseStep 3526433 = 2644825) B2644825
theorem B1568571 : Blo 1566981 1568571 := bstep (se 1 (by rfl) ⟨1176428, by rfl⟩ : syracuseStep 1568571 = 2352857) B2352857
theorem B7532423 : Blo 1566981 7532423 := bstep (se 1 (by rfl) ⟨5649317, by rfl⟩ : syracuseStep 7532423 = 11298635) B11298635
theorem B1568647 : Blo 1566981 1568647 := bstep (se 1 (by rfl) ⟨1176485, by rfl⟩ : syracuseStep 1568647 = 2352971) B2352971
theorem B1568655 : Blo 1566981 1568655 := bstep (se 1 (by rfl) ⟨1176491, by rfl⟩ : syracuseStep 1568655 = 2352983) B2352983
theorem B223350707 : Blo 1566981 223350707 := bstep (se 1 (by rfl) ⟨167513030, by rfl⟩ : syracuseStep 223350707 = 335026061) B335026061
theorem B1568699 : Blo 1566981 1568699 := bstep (se 1 (by rfl) ⟨1176524, by rfl⟩ : syracuseStep 1568699 = 2353049) B2353049
theorem B8048605 : Blo 1566981 8048605 := bstep (se 3 (by rfl) ⟨1509113, by rfl⟩ : syracuseStep 8048605 = 3018227) B3018227
theorem B1568775 : Blo 1566981 1568775 := bstep (se 1 (by rfl) ⟨1176581, by rfl⟩ : syracuseStep 1568775 = 2353163) B2353163
theorem B1568783 : Blo 1566981 1568783 := bstep (se 1 (by rfl) ⟨1176587, by rfl⟩ : syracuseStep 1568783 = 2353175) B2353175
theorem B7737367 : Blo 1566981 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B6696989 : Blo 1566981 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B1568827 : Blo 1566981 1568827 := bstep (se 1 (by rfl) ⟨1176620, by rfl⟩ : syracuseStep 1568827 = 2353241) B2353241
theorem B7942211 : Blo 1566981 7942211 := bstep (se 1 (by rfl) ⟨5956658, by rfl⟩ : syracuseStep 7942211 = 11913317) B11913317
theorem B3526775 : Blo 1566981 3526775 := bstep (se 1 (by rfl) ⟨2645081, by rfl⟩ : syracuseStep 3526775 = 5290163) B5290163
theorem B1568903 : Blo 1566981 1568903 := bstep (se 1 (by rfl) ⟨1176677, by rfl⟩ : syracuseStep 1568903 = 2353355) B2353355
theorem B1568911 : Blo 1566981 1568911 := bstep (se 1 (by rfl) ⟨1176683, by rfl⟩ : syracuseStep 1568911 = 2353367) B2353367
theorem B1568955 : Blo 1566981 1568955 := bstep (se 1 (by rfl) ⟨1176716, by rfl⟩ : syracuseStep 1568955 = 2353433) B2353433
theorem B9531593 : Blo 1566981 9531593 := bstep (se 2 (by rfl) ⟨3574347, by rfl⟩ : syracuseStep 9531593 = 7148695) B7148695
theorem B8048929 : Blo 1566981 8048929 := bstep (se 2 (by rfl) ⟨3018348, by rfl⟩ : syracuseStep 8048929 = 6036697) B6036697
theorem B3526955 : Blo 1566981 3526955 := bstep (se 1 (by rfl) ⟨2645216, by rfl⟩ : syracuseStep 3526955 = 5290433) B5290433
theorem B3969395 : Blo 1566981 3969395 := bstep (se 1 (by rfl) ⟨2977046, by rfl⟩ : syracuseStep 3969395 = 5954093) B5954093
theorem B3576199 : Blo 1566981 3576199 := bstep (se 1 (by rfl) ⟨2682149, by rfl⟩ : syracuseStep 3576199 = 5364299) B5364299
theorem B7942535 : Blo 1566981 7942535 := bstep (se 1 (by rfl) ⟨5956901, by rfl⟩ : syracuseStep 7942535 = 11913803) B11913803
theorem B2118089 : Blo 1566981 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B4297259 : Blo 1566981 4297259 := bstep (se 1 (by rfl) ⟨3222944, by rfl⟩ : syracuseStep 4297259 = 6445889) B6445889
theorem B15069797 : Blo 1566981 15069797 := bstep (se 4 (by rfl) ⟨1412793, by rfl⟩ : syracuseStep 15069797 = 2825587) B2825587
theorem B3527315 : Blo 1566981 3527315 := bstep (se 1 (by rfl) ⟨2645486, by rfl⟩ : syracuseStep 3527315 = 5290973) B5290973
theorem B3527369 : Blo 1566981 3527369 := bstep (se 2 (by rfl) ⟨1322763, by rfl⟩ : syracuseStep 3527369 = 2645527) B2645527
theorem B6697673 : Blo 1566981 6697673 := bstep (se 2 (by rfl) ⟨2511627, by rfl⟩ : syracuseStep 6697673 = 5023255) B5023255
theorem B5288705 : Blo 1566981 5288705 := bstep (se 2 (by rfl) ⟨1983264, by rfl⟩ : syracuseStep 5288705 = 3966529) B3966529
theorem B30151439 : Blo 1566981 30151439 := bstep (se 1 (by rfl) ⟨22613579, by rfl⟩ : syracuseStep 30151439 = 45227159) B45227159
theorem B2978603 : Blo 1566981 2978603 := bstep (se 1 (by rfl) ⟨2233952, by rfl⟩ : syracuseStep 2978603 = 4467905) B4467905
theorem B8934259 : Blo 1566981 8934259 := bstep (se 1 (by rfl) ⟨6700694, by rfl⟩ : syracuseStep 8934259 = 13401389) B13401389
theorem B3969911 : Blo 1566981 3969911 := bstep (se 1 (by rfl) ⟨2977433, by rfl⟩ : syracuseStep 3969911 = 5954867) B5954867
theorem B3347401 : Blo 1566981 3347401 := bstep (se 2 (by rfl) ⟨1255275, by rfl⟩ : syracuseStep 3347401 = 2510551) B2510551
theorem B10040381 : Blo 1566981 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B25416791 : Blo 1566981 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B5436503 : Blo 1566981 5436503 := bstep (se 1 (by rfl) ⟨4077377, by rfl⟩ : syracuseStep 5436503 = 8154755) B8154755
theorem B5362807 : Blo 1566981 5362807 := bstep (se 1 (by rfl) ⟨4022105, by rfl⟩ : syracuseStep 5362807 = 8044211) B8044211
theorem B2233531 : Blo 1566981 2233531 := bstep (se 1 (by rfl) ⟨1675148, by rfl⟩ : syracuseStep 2233531 = 3350297) B3350297
theorem B7533805 : Blo 1566981 7533805 := bstep (se 3 (by rfl) ⟨1412588, by rfl⟩ : syracuseStep 7533805 = 2825177) B2825177
theorem B8475941 : Blo 1566981 8475941 := bstep (se 4 (by rfl) ⟨794619, by rfl⟩ : syracuseStep 8475941 = 1589239) B1589239
theorem B2545031 : Blo 1566981 2545031 := bstep (se 1 (by rfl) ⟨1908773, by rfl⟩ : syracuseStep 2545031 = 3817547) B3817547
theorem B3528071 : Blo 1566981 3528071 := bstep (se 1 (by rfl) ⟨2646053, by rfl⟩ : syracuseStep 3528071 = 5292107) B5292107
theorem B5952953 : Blo 1566981 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B2512313 : Blo 1566981 2512313 := bstep (se 2 (by rfl) ⟨942117, by rfl⟩ : syracuseStep 2512313 = 1884235) B1884235
theorem B2119159 : Blo 1566981 2119159 := bstep (se 1 (by rfl) ⟨1589369, by rfl⟩ : syracuseStep 2119159 = 3178739) B3178739
theorem B5289515 : Blo 1566981 5289515 := bstep (se 1 (by rfl) ⟨3967136, by rfl⟩ : syracuseStep 5289515 = 7934273) B7934273
theorem B3528251 : Blo 1566981 3528251 := bstep (se 1 (by rfl) ⟨2646188, by rfl⟩ : syracuseStep 3528251 = 5292377) B5292377
theorem B8926787 : Blo 1566981 8926787 := bstep (se 1 (by rfl) ⟨6695090, by rfl⟩ : syracuseStep 8926787 = 13390181) B13390181
theorem B3528377 : Blo 1566981 3528377 := bstep (se 2 (by rfl) ⟨1323141, by rfl⟩ : syracuseStep 3528377 = 2646283) B2646283
theorem B3970903 : Blo 1566981 3970903 := bstep (se 1 (by rfl) ⟨2978177, by rfl⟩ : syracuseStep 3970903 = 5956355) B5956355
theorem B8927243 : Blo 1566981 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B3528719 : Blo 1566981 3528719 := bstep (se 1 (by rfl) ⟨2646539, by rfl⟩ : syracuseStep 3528719 = 5293079) B5293079
theorem B3528737 : Blo 1566981 3528737 := bstep (se 2 (by rfl) ⟨1323276, by rfl⟩ : syracuseStep 3528737 = 2646553) B2646553
theorem B2119753 : Blo 1566981 2119753 := bstep (se 2 (by rfl) ⟨794907, by rfl⟩ : syracuseStep 2119753 = 1589815) B1589815
theorem B3971207 : Blo 1566981 3971207 := bstep (se 1 (by rfl) ⟨2978405, by rfl⟩ : syracuseStep 3971207 = 5956811) B5956811
theorem B2119927 : Blo 1566981 2119927 := bstep (se 1 (by rfl) ⟨1589945, by rfl⟩ : syracuseStep 2119927 = 3179891) B3179891
theorem B3971339 : Blo 1566981 3971339 := bstep (se 1 (by rfl) ⟨2978504, by rfl⟩ : syracuseStep 3971339 = 5957009) B5957009
theorem B8935717 : Blo 1566981 8935717 := bstep (se 4 (by rfl) ⟨837723, by rfl⟩ : syracuseStep 8935717 = 1675447) B1675447
theorem B2824507 : Blo 1566981 2824507 := bstep (se 1 (by rfl) ⟨2118380, by rfl⟩ : syracuseStep 2824507 = 4236761) B4236761
theorem B3529079 : Blo 1566981 3529079 := bstep (se 1 (by rfl) ⟨2646809, by rfl⟩ : syracuseStep 3529079 = 5293619) B5293619
theorem B6699449 : Blo 1566981 6699449 := bstep (se 2 (by rfl) ⟨2512293, by rfl⟩ : syracuseStep 6699449 = 5024587) B5024587
theorem B7936541 : Blo 1566981 7936541 := bstep (se 3 (by rfl) ⟨1488101, by rfl⟩ : syracuseStep 7936541 = 2976203) B2976203
theorem B3529259 : Blo 1566981 3529259 := bstep (se 1 (by rfl) ⟨2646944, by rfl⟩ : syracuseStep 3529259 = 5293889) B5293889
theorem B4463257 : Blo 1566981 4463257 := bstep (se 2 (by rfl) ⟨1673721, by rfl⟩ : syracuseStep 4463257 = 3347443) B3347443
theorem B9050797 : Blo 1566981 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B13392641 : Blo 1566981 13392641 := bstep (se 2 (by rfl) ⟨5022240, by rfl⟩ : syracuseStep 13392641 = 10044481) B10044481
theorem B2644751 : Blo 1566981 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B5290811 : Blo 1566981 5290811 := bstep (se 1 (by rfl) ⟨3968108, by rfl⟩ : syracuseStep 5290811 = 7936217) B7936217
theorem B2415433 : Blo 1566981 2415433 := bstep (se 2 (by rfl) ⟨905787, by rfl⟩ : syracuseStep 2415433 = 1811575) B1811575
theorem B3529619 : Blo 1566981 3529619 := bstep (se 1 (by rfl) ⟨2647214, by rfl⟩ : syracuseStep 3529619 = 5294429) B5294429
theorem B3529673 : Blo 1566981 3529673 := bstep (se 2 (by rfl) ⟨1323627, by rfl⟩ : syracuseStep 3529673 = 2647255) B2647255
theorem B7937027 : Blo 1566981 7937027 := bstep (se 1 (by rfl) ⟨5952770, by rfl⟩ : syracuseStep 7937027 = 11905541) B11905541
theorem B97876997 : Blo 1566981 97876997 := bstep (se 4 (by rfl) ⟨9175968, by rfl⟩ : syracuseStep 97876997 = 18351937) B18351937
theorem B4463873 : Blo 1566981 4463873 := bstep (se 2 (by rfl) ⟨1673952, by rfl⟩ : syracuseStep 4463873 = 3347905) B3347905
theorem B5291297 : Blo 1566981 5291297 := bstep (se 2 (by rfl) ⟨1984236, by rfl⟩ : syracuseStep 5291297 = 3968473) B3968473
theorem B2645291 : Blo 1566981 2645291 := bstep (se 1 (by rfl) ⟨1983968, by rfl⟩ : syracuseStep 2645291 = 3967937) B3967937
theorem B2350523 : Blo 1566981 2350523 := bstep (se 1 (by rfl) ⟨1762892, by rfl⟩ : syracuseStep 2350523 = 3525785) B3525785
theorem B2350583 : Blo 1566981 2350583 := bstep (se 1 (by rfl) ⟨1762937, by rfl⟩ : syracuseStep 2350583 = 3525875) B3525875
theorem B2350607 : Blo 1566981 2350607 := bstep (se 1 (by rfl) ⟨1762955, by rfl⟩ : syracuseStep 2350607 = 3525911) B3525911
theorem B4898333 : Blo 1566981 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B2350649 : Blo 1566981 2350649 := bstep (se 2 (by rfl) ⟨881493, by rfl⟩ : syracuseStep 2350649 = 1762987) B1762987
theorem B3350135 : Blo 1566981 3350135 := bstep (se 1 (by rfl) ⟨2512601, by rfl⟩ : syracuseStep 3350135 = 5025203) B5025203
theorem B2350727 : Blo 1566981 2350727 := bstep (se 1 (by rfl) ⟨1763045, by rfl⟩ : syracuseStep 2350727 = 3526091) B3526091
theorem B1883783 : Blo 1566981 1883783 := bstep (se 1 (by rfl) ⟨1412837, by rfl⟩ : syracuseStep 1883783 = 2825675) B2825675
theorem B2350763 : Blo 1566981 2350763 := bstep (se 1 (by rfl) ⟨1763072, by rfl⟩ : syracuseStep 2350763 = 3526145) B3526145
theorem B2645689 : Blo 1566981 2645689 := bstep (se 2 (by rfl) ⟨992133, by rfl⟩ : syracuseStep 2645689 = 1984267) B1984267
theorem B12066497 : Blo 1566981 12066497 := bstep (se 2 (by rfl) ⟨4524936, by rfl⟩ : syracuseStep 12066497 = 9049873) B9049873
theorem B2350793 : Blo 1566981 2350793 := bstep (se 2 (by rfl) ⟨881547, by rfl⟩ : syracuseStep 2350793 = 1763095) B1763095
theorem B20086501 : Blo 1566981 20086501 := bstep (se 4 (by rfl) ⟨1883109, by rfl⟩ : syracuseStep 20086501 = 3766219) B3766219
theorem B5021473 : Blo 1566981 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B2350907 : Blo 1566981 2350907 := bstep (se 1 (by rfl) ⟨1763180, by rfl⟩ : syracuseStep 2350907 = 3526361) B3526361
theorem B5291891 : Blo 1566981 5291891 := bstep (se 1 (by rfl) ⟨3968918, by rfl⟩ : syracuseStep 5291891 = 7937837) B7937837
theorem B2350967 : Blo 1566981 2350967 := bstep (se 1 (by rfl) ⟨1763225, by rfl⟩ : syracuseStep 2350967 = 3526451) B3526451
theorem B2350991 : Blo 1566981 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B2351033 : Blo 1566981 2351033 := bstep (se 2 (by rfl) ⟨881637, by rfl⟩ : syracuseStep 2351033 = 1763275) B1763275
theorem B4464659 : Blo 1566981 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B2351183 : Blo 1566981 2351183 := bstep (se 1 (by rfl) ⟨1763387, by rfl⟩ : syracuseStep 2351183 = 3526775) B3526775
theorem B20086865 : Blo 1566981 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B2826337 : Blo 1566981 2826337 := bstep (se 2 (by rfl) ⟨1059876, by rfl⟩ : syracuseStep 2826337 = 2119753) B2119753
theorem B2351303 : Blo 1566981 2351303 := bstep (se 1 (by rfl) ⟨1763477, by rfl⟩ : syracuseStep 2351303 = 3526955) B3526955
theorem B2646263 : Blo 1566981 2646263 := bstep (se 1 (by rfl) ⟨1984697, by rfl⟩ : syracuseStep 2646263 = 3969395) B3969395
theorem B2826569 : Blo 1566981 2826569 := bstep (se 2 (by rfl) ⟨1059963, by rfl⟩ : syracuseStep 2826569 = 2119927) B2119927
theorem B2351465 : Blo 1566981 2351465 := bstep (se 2 (by rfl) ⟨881799, by rfl⟩ : syracuseStep 2351465 = 1763599) B1763599
theorem B10731905 : Blo 1566981 10731905 := bstep (se 2 (by rfl) ⟨4024464, by rfl⟩ : syracuseStep 10731905 = 8048929) B8048929
theorem B5292431 : Blo 1566981 5292431 := bstep (se 1 (by rfl) ⟨3969323, by rfl⟩ : syracuseStep 5292431 = 7938647) B7938647
theorem B2351543 : Blo 1566981 2351543 := bstep (se 1 (by rfl) ⟨1763657, by rfl⟩ : syracuseStep 2351543 = 3527315) B3527315
theorem B2351579 : Blo 1566981 2351579 := bstep (se 1 (by rfl) ⟨1763684, by rfl⟩ : syracuseStep 2351579 = 3527369) B3527369
theorem B4465115 : Blo 1566981 4465115 := bstep (se 1 (by rfl) ⟨3348836, by rfl⟩ : syracuseStep 4465115 = 6697673) B6697673
theorem B4768265 : Blo 1566981 4768265 := bstep (se 2 (by rfl) ⟨1788099, by rfl⟩ : syracuseStep 4768265 = 3576199) B3576199
theorem B2646607 : Blo 1566981 2646607 := bstep (se 1 (by rfl) ⟨1984955, by rfl⟩ : syracuseStep 2646607 = 3969911) B3969911
theorem B6693587 : Blo 1566981 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B5292755 : Blo 1566981 5292755 := bstep (se 1 (by rfl) ⟨3969566, by rfl⟩ : syracuseStep 5292755 = 7939133) B7939133
theorem B22602509 : Blo 1566981 22602509 := bstep (se 3 (by rfl) ⟨4237970, by rfl⟩ : syracuseStep 22602509 = 8475941) B8475941
theorem B2646857 : Blo 1566981 2646857 := bstep (se 2 (by rfl) ⟨992571, by rfl⟩ : syracuseStep 2646857 = 1985143) B1985143
theorem B6882155 : Blo 1566981 6882155 := bstep (se 1 (by rfl) ⟨5161616, by rfl⟩ : syracuseStep 6882155 = 10323233) B10323233
theorem B3179371 : Blo 1566981 3179371 := bstep (se 1 (by rfl) ⟨2384528, by rfl⟩ : syracuseStep 3179371 = 4769057) B4769057
theorem B2352047 : Blo 1566981 2352047 := bstep (se 1 (by rfl) ⟨1764035, by rfl⟩ : syracuseStep 2352047 = 3528071) B3528071
theorem B2352137 : Blo 1566981 2352137 := bstep (se 2 (by rfl) ⟨882051, by rfl⟩ : syracuseStep 2352137 = 1764103) B1764103
theorem B3769363 : Blo 1566981 3769363 := bstep (se 1 (by rfl) ⟨2827022, by rfl⟩ : syracuseStep 3769363 = 5654045) B5654045
theorem B2352167 : Blo 1566981 2352167 := bstep (se 1 (by rfl) ⟨1764125, by rfl⟩ : syracuseStep 2352167 = 3528251) B3528251
theorem B3220577 : Blo 1566981 3220577 := bstep (se 2 (by rfl) ⟨1207716, by rfl⟩ : syracuseStep 3220577 = 2415433) B2415433
theorem B2352251 : Blo 1566981 2352251 := bstep (se 1 (by rfl) ⟨1764188, by rfl⟩ : syracuseStep 2352251 = 3528377) B3528377
theorem B11912345 : Blo 1566981 11912345 := bstep (se 2 (by rfl) ⟨4467129, by rfl⟩ : syracuseStep 11912345 = 8934259) B8934259
theorem B2352377 : Blo 1566981 2352377 := bstep (se 2 (by rfl) ⟨882141, by rfl⟩ : syracuseStep 2352377 = 1764283) B1764283
theorem B2647289 : Blo 1566981 2647289 := bstep (se 2 (by rfl) ⟨992733, by rfl⟩ : syracuseStep 2647289 = 1985467) B1985467
theorem B2352479 : Blo 1566981 2352479 := bstep (se 1 (by rfl) ⟨1764359, by rfl⟩ : syracuseStep 2352479 = 3528719) B3528719
theorem B3179881 : Blo 1566981 3179881 := bstep (se 2 (by rfl) ⟨1192455, by rfl⟩ : syracuseStep 3179881 = 2384911) B2384911
theorem B2352491 : Blo 1566981 2352491 := bstep (se 1 (by rfl) ⟨1764368, by rfl⟩ : syracuseStep 2352491 = 3528737) B3528737
theorem B2647471 : Blo 1566981 2647471 := bstep (se 1 (by rfl) ⟨1985603, by rfl⟩ : syracuseStep 2647471 = 3971207) B3971207
theorem B2647559 : Blo 1566981 2647559 := bstep (se 1 (by rfl) ⟨1985669, by rfl⟩ : syracuseStep 2647559 = 3971339) B3971339
theorem B2352719 : Blo 1566981 2352719 := bstep (se 1 (by rfl) ⟨1764539, by rfl⟩ : syracuseStep 2352719 = 3529079) B3529079
theorem B4466299 : Blo 1566981 4466299 := bstep (se 1 (by rfl) ⟨3349724, by rfl⟩ : syracuseStep 4466299 = 6699449) B6699449
theorem B10045073 : Blo 1566981 10045073 := bstep (se 2 (by rfl) ⟨3766902, by rfl⟩ : syracuseStep 10045073 = 7533805) B7533805
theorem B5023421 : Blo 1566981 5023421 := bstep (se 3 (by rfl) ⟨941891, by rfl⟩ : syracuseStep 5023421 = 1883783) B1883783
theorem B2352839 : Blo 1566981 2352839 := bstep (se 1 (by rfl) ⟨1764629, by rfl⟩ : syracuseStep 2352839 = 3529259) B3529259
theorem B228984641 : Blo 1566981 228984641 := bstep (se 2 (by rfl) ⟨85869240, by rfl⟩ : syracuseStep 228984641 = 171738481) B171738481
theorem B1763167 : Blo 1566981 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B2353001 : Blo 1566981 2353001 := bstep (se 2 (by rfl) ⟨882375, by rfl⟩ : syracuseStep 2353001 = 1764751) B1764751
theorem B5293943 : Blo 1566981 5293943 := bstep (se 1 (by rfl) ⟨3970457, by rfl⟩ : syracuseStep 5293943 = 7940915) B7940915
theorem B1984439 : Blo 1566981 1984439 := bstep (se 1 (by rfl) ⟨1488329, by rfl⟩ : syracuseStep 1984439 = 2976659) B2976659
theorem B2353079 : Blo 1566981 2353079 := bstep (se 1 (by rfl) ⟨1764809, by rfl⟩ : syracuseStep 2353079 = 3529619) B3529619
theorem B2353115 : Blo 1566981 2353115 := bstep (se 1 (by rfl) ⟨1764836, by rfl⟩ : syracuseStep 2353115 = 3529673) B3529673
theorem B65251331 : Blo 1566981 65251331 := bstep (se 1 (by rfl) ⟨48938498, by rfl⟩ : syracuseStep 65251331 = 97876997) B97876997
theorem B8931343 : Blo 1566981 8931343 := bstep (se 1 (by rfl) ⟨6698507, by rfl⟩ : syracuseStep 8931343 = 13397015) B13397015
theorem B3966995 : Blo 1566981 3966995 := bstep (se 1 (by rfl) ⟨2975246, by rfl⟩ : syracuseStep 3966995 = 5950493) B5950493
theorem B1984591 : Blo 1566981 1984591 := bstep (se 1 (by rfl) ⟨1488443, by rfl⟩ : syracuseStep 1984591 = 2976887) B2976887
theorem B5294159 : Blo 1566981 5294159 := bstep (se 1 (by rfl) ⟨3970619, by rfl⟩ : syracuseStep 5294159 = 7941239) B7941239
theorem B2975915 : Blo 1566981 2975915 := bstep (se 1 (by rfl) ⟨2231936, by rfl⟩ : syracuseStep 2975915 = 4463873) B4463873
theorem B1763527 : Blo 1566981 1763527 := bstep (se 1 (by rfl) ⟨1322645, by rfl⟩ : syracuseStep 1763527 = 2645291) B2645291
theorem B1567015 : Blo 1566981 1567015 := bstep (se 1 (by rfl) ⟨1175261, by rfl⟩ : syracuseStep 1567015 = 2350523) B2350523
theorem B26782001 : Blo 1566981 26782001 := bstep (se 2 (by rfl) ⟨10043250, by rfl⟩ : syracuseStep 26782001 = 20086501) B20086501
theorem B11299121 : Blo 1566981 11299121 := bstep (se 2 (by rfl) ⟨4237170, by rfl⟩ : syracuseStep 11299121 = 8474341) B8474341
theorem B1567055 : Blo 1566981 1567055 := bstep (se 1 (by rfl) ⟨1175291, by rfl⟩ : syracuseStep 1567055 = 2350583) B2350583
theorem B1567071 : Blo 1566981 1567071 := bstep (se 1 (by rfl) ⟨1175303, by rfl⟩ : syracuseStep 1567071 = 2350607) B2350607
theorem B1567099 : Blo 1566981 1567099 := bstep (se 1 (by rfl) ⟨1175324, by rfl⟩ : syracuseStep 1567099 = 2350649) B2350649
theorem B6695297 : Blo 1566981 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B1567151 : Blo 1566981 1567151 := bstep (se 1 (by rfl) ⟨1175363, by rfl⟩ : syracuseStep 1567151 = 2350727) B2350727
theorem B1567175 : Blo 1566981 1567175 := bstep (se 1 (by rfl) ⟨1175381, by rfl⟩ : syracuseStep 1567175 = 2350763) B2350763
theorem B5294537 : Blo 1566981 5294537 := bstep (se 2 (by rfl) ⟨1985451, by rfl⟩ : syracuseStep 5294537 = 3970903) B3970903
theorem B1567195 : Blo 1566981 1567195 := bstep (se 1 (by rfl) ⟨1175396, by rfl⟩ : syracuseStep 1567195 = 2350793) B2350793
theorem B3967451 : Blo 1566981 3967451 := bstep (se 1 (by rfl) ⟨2975588, by rfl⟩ : syracuseStep 3967451 = 5951177) B5951177
theorem B3017179 : Blo 1566981 3017179 := bstep (se 1 (by rfl) ⟨2262884, by rfl⟩ : syracuseStep 3017179 = 4525769) B4525769
theorem B595601885 : Blo 1566981 595601885 := bstep (se 3 (by rfl) ⟨111675353, by rfl⟩ : syracuseStep 595601885 = 223350707) B223350707
theorem B1567271 : Blo 1566981 1567271 := bstep (se 1 (by rfl) ⟨1175453, by rfl⟩ : syracuseStep 1567271 = 2350907) B2350907
theorem B1567311 : Blo 1566981 1567311 := bstep (se 1 (by rfl) ⟨1175483, by rfl⟩ : syracuseStep 1567311 = 2350967) B2350967
theorem B1567327 : Blo 1566981 1567327 := bstep (se 1 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 1567327 = 2350991) B2350991
theorem B1567355 : Blo 1566981 1567355 := bstep (se 1 (by rfl) ⟨1175516, by rfl⟩ : syracuseStep 1567355 = 2351033) B2351033
theorem B2681515 : Blo 1566981 2681515 := bstep (se 1 (by rfl) ⟨2011136, by rfl⟩ : syracuseStep 2681515 = 4022273) B4022273
theorem B1567407 : Blo 1566981 1567407 := bstep (se 1 (by rfl) ⟨1175555, by rfl⟩ : syracuseStep 1567407 = 2351111) B2351111
theorem B22604467 : Blo 1566981 22604467 := bstep (se 1 (by rfl) ⟨16953350, by rfl⟩ : syracuseStep 22604467 = 33906701) B33906701
theorem B1567431 : Blo 1566981 1567431 := bstep (se 1 (by rfl) ⟨1175573, by rfl⟩ : syracuseStep 1567431 = 2351147) B2351147
theorem B10316489 : Blo 1566981 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B5294807 : Blo 1566981 5294807 := bstep (se 1 (by rfl) ⟨3971105, by rfl⟩ : syracuseStep 5294807 = 7942211) B7942211
theorem B1567451 : Blo 1566981 1567451 := bstep (se 1 (by rfl) ⟨1175588, by rfl⟩ : syracuseStep 1567451 = 2351177) B2351177
theorem B4467449 : Blo 1566981 4467449 := bstep (se 2 (by rfl) ⟨1675293, by rfl⟩ : syracuseStep 4467449 = 3350587) B3350587
theorem B1567527 : Blo 1566981 1567527 := bstep (se 1 (by rfl) ⟨1175645, by rfl⟩ : syracuseStep 1567527 = 2351291) B2351291
theorem B1567567 : Blo 1566981 1567567 := bstep (se 1 (by rfl) ⟨1175675, by rfl⟩ : syracuseStep 1567567 = 2351351) B2351351
theorem B1567583 : Blo 1566981 1567583 := bstep (se 1 (by rfl) ⟨1175687, by rfl⟩ : syracuseStep 1567583 = 2351375) B2351375
theorem B1567611 : Blo 1566981 1567611 := bstep (se 1 (by rfl) ⟨1175708, by rfl⟩ : syracuseStep 1567611 = 2351417) B2351417
theorem B1567663 : Blo 1566981 1567663 := bstep (se 1 (by rfl) ⟨1175747, by rfl⟩ : syracuseStep 1567663 = 2351495) B2351495
theorem B4467631 : Blo 1566981 4467631 := bstep (se 1 (by rfl) ⟨3350723, by rfl⟩ : syracuseStep 4467631 = 6701447) B6701447
theorem B5295023 : Blo 1566981 5295023 := bstep (se 1 (by rfl) ⟨3971267, by rfl⟩ : syracuseStep 5295023 = 7942535) B7942535
theorem B1567687 : Blo 1566981 1567687 := bstep (se 1 (by rfl) ⟨1175765, by rfl⟩ : syracuseStep 1567687 = 2351531) B2351531
theorem B1567707 : Blo 1566981 1567707 := bstep (se 1 (by rfl) ⟨1175780, by rfl⟩ : syracuseStep 1567707 = 2351561) B2351561
theorem B1567783 : Blo 1566981 1567783 := bstep (se 1 (by rfl) ⟨1175837, by rfl⟩ : syracuseStep 1567783 = 2351675) B2351675
theorem B1764391 : Blo 1566981 1764391 := bstep (se 1 (by rfl) ⟨1323293, by rfl⟩ : syracuseStep 1764391 = 2646587) B2646587
theorem B11914289 : Blo 1566981 11914289 := bstep (se 2 (by rfl) ⟨4467858, by rfl⟩ : syracuseStep 11914289 = 8935717) B8935717
theorem B10046531 : Blo 1566981 10046531 := bstep (se 1 (by rfl) ⟨7534898, by rfl⟩ : syracuseStep 10046531 = 15069797) B15069797
theorem B1567823 : Blo 1566981 1567823 := bstep (se 1 (by rfl) ⟨1175867, by rfl⟩ : syracuseStep 1567823 = 2351735) B2351735
theorem B4467791 : Blo 1566981 4467791 := bstep (se 1 (by rfl) ⟨3350843, by rfl⟩ : syracuseStep 4467791 = 6701687) B6701687
theorem B1567839 : Blo 1566981 1567839 := bstep (se 1 (by rfl) ⟨1175879, by rfl⟩ : syracuseStep 1567839 = 2351759) B2351759
theorem B1567867 : Blo 1566981 1567867 := bstep (se 1 (by rfl) ⟨1175900, by rfl⟩ : syracuseStep 1567867 = 2351801) B2351801
theorem B3525803 : Blo 1566981 3525803 := bstep (se 1 (by rfl) ⟨2644352, by rfl⟩ : syracuseStep 3525803 = 5288705) B5288705
theorem B1567919 : Blo 1566981 1567919 := bstep (se 1 (by rfl) ⟨1175939, by rfl⟩ : syracuseStep 1567919 = 2351879) B2351879
theorem B50834627 : Blo 1566981 50834627 := bstep (se 1 (by rfl) ⟨38125970, by rfl⟩ : syracuseStep 50834627 = 76251941) B76251941
theorem B1567943 : Blo 1566981 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B1985735 : Blo 1566981 1985735 := bstep (se 1 (by rfl) ⟨1489301, by rfl⟩ : syracuseStep 1985735 = 2978603) B2978603
theorem B1567963 : Blo 1566981 1567963 := bstep (se 1 (by rfl) ⟨1175972, by rfl⟩ : syracuseStep 1567963 = 2351945) B2351945
theorem B1568039 : Blo 1566981 1568039 := bstep (se 1 (by rfl) ⟨1176029, by rfl⟩ : syracuseStep 1568039 = 2352059) B2352059
theorem B1568079 : Blo 1566981 1568079 := bstep (se 1 (by rfl) ⟨1176059, by rfl⟩ : syracuseStep 1568079 = 2352119) B2352119
theorem B2010463 : Blo 1566981 2010463 := bstep (se 1 (by rfl) ⟨1507847, by rfl⟩ : syracuseStep 2010463 = 3015695) B3015695
theorem B1568095 : Blo 1566981 1568095 := bstep (se 1 (by rfl) ⟨1176071, by rfl⟩ : syracuseStep 1568095 = 2352143) B2352143
theorem B1568123 : Blo 1566981 1568123 := bstep (se 1 (by rfl) ⟨1176092, by rfl⟩ : syracuseStep 1568123 = 2352185) B2352185
theorem B5647745 : Blo 1566981 5647745 := bstep (se 2 (by rfl) ⟨2117904, by rfl⟩ : syracuseStep 5647745 = 4235809) B4235809
theorem B16944527 : Blo 1566981 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B3624335 : Blo 1566981 3624335 := bstep (se 1 (by rfl) ⟨2718251, by rfl⟩ : syracuseStep 3624335 = 5436503) B5436503
theorem B1568175 : Blo 1566981 1568175 := bstep (se 1 (by rfl) ⟨1176131, by rfl⟩ : syracuseStep 1568175 = 2352263) B2352263
theorem B1568199 : Blo 1566981 1568199 := bstep (se 1 (by rfl) ⟨1176149, by rfl⟩ : syracuseStep 1568199 = 2352299) B2352299
theorem B1568219 : Blo 1566981 1568219 := bstep (se 1 (by rfl) ⟨1176164, by rfl⟩ : syracuseStep 1568219 = 2352329) B2352329
theorem B5951009 : Blo 1566981 5951009 := bstep (se 2 (by rfl) ⟨2231628, by rfl⟩ : syracuseStep 5951009 = 4463257) B4463257
theorem B1568295 : Blo 1566981 1568295 := bstep (se 1 (by rfl) ⟨1176221, by rfl⟩ : syracuseStep 1568295 = 2352443) B2352443
theorem B48270917 : Blo 1566981 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B1568335 : Blo 1566981 1568335 := bstep (se 1 (by rfl) ⟨1176251, by rfl⟩ : syracuseStep 1568335 = 2352503) B2352503
theorem B1568351 : Blo 1566981 1568351 := bstep (se 1 (by rfl) ⟨1176263, by rfl⟩ : syracuseStep 1568351 = 2352527) B2352527
theorem B3968635 : Blo 1566981 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1568379 : Blo 1566981 1568379 := bstep (se 1 (by rfl) ⟨1176284, by rfl⟩ : syracuseStep 1568379 = 2352569) B2352569
theorem B1674875 : Blo 1566981 1674875 := bstep (se 1 (by rfl) ⟨1256156, by rfl⟩ : syracuseStep 1674875 = 2512313) B2512313
theorem B5025419 : Blo 1566981 5025419 := bstep (se 1 (by rfl) ⟨3769064, by rfl⟩ : syracuseStep 5025419 = 7538129) B7538129
theorem B2682539 : Blo 1566981 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B1568431 : Blo 1566981 1568431 := bstep (se 1 (by rfl) ⟨1176323, by rfl⟩ : syracuseStep 1568431 = 2352647) B2352647
theorem B6786749 : Blo 1566981 6786749 := bstep (se 3 (by rfl) ⟨1272515, by rfl⟩ : syracuseStep 6786749 = 2545031) B2545031
theorem B3526343 : Blo 1566981 3526343 := bstep (se 1 (by rfl) ⟨2644757, by rfl⟩ : syracuseStep 3526343 = 5289515) B5289515
theorem B1568455 : Blo 1566981 1568455 := bstep (se 1 (by rfl) ⟨1176341, by rfl⟩ : syracuseStep 1568455 = 2352683) B2352683
theorem B5951191 : Blo 1566981 5951191 := bstep (se 1 (by rfl) ⟨4463393, by rfl⟩ : syracuseStep 5951191 = 8926787) B8926787
theorem B1568475 : Blo 1566981 1568475 := bstep (se 1 (by rfl) ⟨1176356, by rfl⟩ : syracuseStep 1568475 = 2352713) B2352713
theorem B1568551 : Blo 1566981 1568551 := bstep (se 1 (by rfl) ⟨1176413, by rfl⟩ : syracuseStep 1568551 = 2352827) B2352827
theorem B1568591 : Blo 1566981 1568591 := bstep (se 1 (by rfl) ⟨1176443, by rfl⟩ : syracuseStep 1568591 = 2352887) B2352887
theorem B2977631 : Blo 1566981 2977631 := bstep (se 1 (by rfl) ⟨2233223, by rfl⟩ : syracuseStep 2977631 = 4466447) B4466447
theorem B1568607 : Blo 1566981 1568607 := bstep (se 1 (by rfl) ⟨1176455, by rfl⟩ : syracuseStep 1568607 = 2352911) B2352911
theorem B5648237 : Blo 1566981 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B1568635 : Blo 1566981 1568635 := bstep (se 1 (by rfl) ⟨1176476, by rfl⟩ : syracuseStep 1568635 = 2352953) B2352953
theorem B7942049 : Blo 1566981 7942049 := bstep (se 2 (by rfl) ⟨2978268, by rfl⟩ : syracuseStep 7942049 = 5956537) B5956537
theorem B1568687 : Blo 1566981 1568687 := bstep (se 1 (by rfl) ⟨1176515, by rfl⟩ : syracuseStep 1568687 = 2353031) B2353031
theorem B1568711 : Blo 1566981 1568711 := bstep (se 1 (by rfl) ⟨1176533, by rfl⟩ : syracuseStep 1568711 = 2353067) B2353067
theorem B1568731 : Blo 1566981 1568731 := bstep (se 1 (by rfl) ⟨1176548, by rfl⟩ : syracuseStep 1568731 = 2353097) B2353097
theorem B5951495 : Blo 1566981 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B1568807 : Blo 1566981 1568807 := bstep (se 1 (by rfl) ⟨1176605, by rfl⟩ : syracuseStep 1568807 = 2353211) B2353211
theorem B13062221 : Blo 1566981 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B1568847 : Blo 1566981 1568847 := bstep (se 1 (by rfl) ⟨1176635, by rfl⟩ : syracuseStep 1568847 = 2353271) B2353271
theorem B1568863 : Blo 1566981 1568863 := bstep (se 1 (by rfl) ⟨1176647, by rfl⟩ : syracuseStep 1568863 = 2353295) B2353295
theorem B1568891 : Blo 1566981 1568891 := bstep (se 1 (by rfl) ⟨1176668, by rfl⟩ : syracuseStep 1568891 = 2353337) B2353337
theorem B1568943 : Blo 1566981 1568943 := bstep (se 1 (by rfl) ⟨1176707, by rfl⟩ : syracuseStep 1568943 = 2353415) B2353415
theorem B1568967 : Blo 1566981 1568967 := bstep (se 1 (by rfl) ⟨1176725, by rfl⟩ : syracuseStep 1568967 = 2353451) B2353451
theorem B2978041 : Blo 1566981 2978041 := bstep (se 2 (by rfl) ⟨1116765, by rfl⟩ : syracuseStep 2978041 = 2233531) B2233531
theorem B5951981 : Blo 1566981 5951981 := bstep (se 3 (by rfl) ⟨1115996, by rfl⟩ : syracuseStep 5951981 = 2231993) B2231993
theorem B3527207 : Blo 1566981 3527207 := bstep (se 1 (by rfl) ⟨2645405, by rfl⟩ : syracuseStep 3527207 = 5290811) B5290811
theorem B2978383 : Blo 1566981 2978383 := bstep (se 1 (by rfl) ⟨2233787, by rfl⟩ : syracuseStep 2978383 = 4467575) B4467575
theorem B3527531 : Blo 1566981 3527531 := bstep (se 1 (by rfl) ⟨2645648, by rfl⟩ : syracuseStep 3527531 = 5291297) B5291297
theorem B2863979 : Blo 1566981 2863979 := bstep (se 1 (by rfl) ⟨2147984, by rfl⟩ : syracuseStep 2863979 = 4295969) B4295969
theorem B3527585 : Blo 1566981 3527585 := bstep (se 2 (by rfl) ⟨1322844, by rfl⟩ : syracuseStep 3527585 = 2645689) B2645689
theorem B12719105 : Blo 1566981 12719105 := bstep (se 2 (by rfl) ⟨4769664, by rfl⟩ : syracuseStep 12719105 = 9539329) B9539329
theorem B5288975 : Blo 1566981 5288975 := bstep (se 1 (by rfl) ⟨3966731, by rfl⟩ : syracuseStep 5288975 = 7933463) B7933463
theorem B16086035 : Blo 1566981 16086035 := bstep (se 1 (by rfl) ⟨12064526, by rfl⟩ : syracuseStep 16086035 = 24129053) B24129053
theorem B2233423 : Blo 1566981 2233423 := bstep (se 1 (by rfl) ⟨1675067, by rfl⟩ : syracuseStep 2233423 = 3350135) B3350135
theorem B3527927 : Blo 1566981 3527927 := bstep (se 1 (by rfl) ⟨2645945, by rfl⟩ : syracuseStep 3527927 = 5291891) B5291891
theorem B2512223 : Blo 1566981 2512223 := bstep (se 1 (by rfl) ⟨1884167, by rfl⟩ : syracuseStep 2512223 = 3768335) B3768335
theorem B6354395 : Blo 1566981 6354395 := bstep (se 1 (by rfl) ⟨4765796, by rfl⟩ : syracuseStep 6354395 = 9531593) B9531593
theorem B13399613 : Blo 1566981 13399613 := bstep (se 3 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 13399613 = 5024855) B5024855
theorem B5289569 : Blo 1566981 5289569 := bstep (se 2 (by rfl) ⟨1983588, by rfl⟩ : syracuseStep 5289569 = 3967177) B3967177
theorem B5953121 : Blo 1566981 5953121 := bstep (se 2 (by rfl) ⟨2232420, by rfl⟩ : syracuseStep 5953121 = 4464841) B4464841
theorem B33904277 : Blo 1566981 33904277 := bstep (se 6 (by rfl) ⟨794631, by rfl⟩ : syracuseStep 33904277 = 1589263) B1589263
theorem B3766009 : Blo 1566981 3766009 := bstep (se 2 (by rfl) ⟨1412253, by rfl⟩ : syracuseStep 3766009 = 2824507) B2824507
theorem B8926969 : Blo 1566981 8926969 := bstep (se 2 (by rfl) ⟨3347613, by rfl⟩ : syracuseStep 8926969 = 6695227) B6695227
theorem B2512633 : Blo 1566981 2512633 := bstep (se 2 (by rfl) ⟨942237, by rfl⟩ : syracuseStep 2512633 = 1884475) B1884475
theorem B3528521 : Blo 1566981 3528521 := bstep (se 2 (by rfl) ⟨1323195, by rfl⟩ : syracuseStep 3528521 = 2646391) B2646391
theorem B2824031 : Blo 1566981 2824031 := bstep (se 1 (by rfl) ⟨2118023, by rfl⟩ : syracuseStep 2824031 = 4236047) B4236047
theorem B20100959 : Blo 1566981 20100959 := bstep (se 1 (by rfl) ⟨15075719, by rfl⟩ : syracuseStep 20100959 = 30151439) B30151439
theorem B9541471 : Blo 1566981 9541471 := bstep (se 1 (by rfl) ⟨7156103, by rfl⟩ : syracuseStep 9541471 = 14312207) B14312207
theorem B2644319 : Blo 1566981 2644319 := bstep (se 1 (by rfl) ⟨1983239, by rfl⟩ : syracuseStep 2644319 = 3966479) B3966479
theorem B2824723 : Blo 1566981 2824723 := bstep (se 1 (by rfl) ⟨2118542, by rfl⟩ : syracuseStep 2824723 = 4237085) B4237085
theorem B5954107 : Blo 1566981 5954107 := bstep (se 1 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 5954107 = 8931161) B8931161
theorem B4463201 : Blo 1566981 4463201 := bstep (se 2 (by rfl) ⟨1673700, by rfl⟩ : syracuseStep 4463201 = 3347401) B3347401
theorem B3529313 : Blo 1566981 3529313 := bstep (se 2 (by rfl) ⟨1323492, by rfl⟩ : syracuseStep 3529313 = 2646985) B2646985
theorem B11459357 : Blo 1566981 11459357 := bstep (se 3 (by rfl) ⟨2148629, by rfl⟩ : syracuseStep 11459357 = 4297259) B4297259
theorem B7150409 : Blo 1566981 7150409 := bstep (se 2 (by rfl) ⟨2681403, by rfl⟩ : syracuseStep 7150409 = 5362807) B5362807
theorem B5954411 : Blo 1566981 5954411 := bstep (se 1 (by rfl) ⟨4465808, by rfl⟩ : syracuseStep 5954411 = 8931617) B8931617
theorem B2644879 : Blo 1566981 2644879 := bstep (se 1 (by rfl) ⟨1983659, by rfl⟩ : syracuseStep 2644879 = 3967319) B3967319
theorem B3529655 : Blo 1566981 3529655 := bstep (se 1 (by rfl) ⟨2647241, by rfl⟩ : syracuseStep 3529655 = 5294483) B5294483
theorem B5291027 : Blo 1566981 5291027 := bstep (se 1 (by rfl) ⟨3968270, by rfl⟩ : syracuseStep 5291027 = 7936541) B7936541
theorem B5954579 : Blo 1566981 5954579 := bstep (se 1 (by rfl) ⟨4465934, by rfl⟩ : syracuseStep 5954579 = 8931869) B8931869
theorem B8928427 : Blo 1566981 8928427 := bstep (se 1 (by rfl) ⟨6696320, by rfl⟩ : syracuseStep 8928427 = 13392641) B13392641
theorem B8477891 : Blo 1566981 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B2825545 : Blo 1566981 2825545 := bstep (se 2 (by rfl) ⟨1059579, by rfl⟩ : syracuseStep 2825545 = 2119159) B2119159
theorem B5291351 : Blo 1566981 5291351 := bstep (se 1 (by rfl) ⟨3968513, by rfl⟩ : syracuseStep 5291351 = 7937027) B7937027
theorem B2350511 : Blo 1566981 2350511 := bstep (se 1 (by rfl) ⟨1762883, by rfl⟩ : syracuseStep 2350511 = 3525767) B3525767
theorem B2350601 : Blo 1566981 2350601 := bstep (se 2 (by rfl) ⟨881475, by rfl⟩ : syracuseStep 2350601 = 1762951) B1762951
theorem B2350631 : Blo 1566981 2350631 := bstep (se 1 (by rfl) ⟨1762973, by rfl⟩ : syracuseStep 2350631 = 3525947) B3525947
theorem B2645561 : Blo 1566981 2645561 := bstep (se 2 (by rfl) ⟨992085, by rfl⟩ : syracuseStep 2645561 = 1984171) B1984171
theorem B2350715 : Blo 1566981 2350715 := bstep (se 1 (by rfl) ⟨1763036, by rfl⟩ : syracuseStep 2350715 = 3526073) B3526073
theorem B7937675 : Blo 1566981 7937675 := bstep (se 1 (by rfl) ⟨5953256, by rfl⟩ : syracuseStep 7937675 = 11906513) B11906513
theorem B8478407 : Blo 1566981 8478407 := bstep (se 1 (by rfl) ⟨6358805, by rfl⟩ : syracuseStep 8478407 = 12717611) B12717611
theorem B2350841 : Blo 1566981 2350841 := bstep (se 2 (by rfl) ⟨881565, by rfl⟩ : syracuseStep 2350841 = 1763131) B1763131
theorem B8044331 : Blo 1566981 8044331 := bstep (se 1 (by rfl) ⟨6033248, by rfl⟩ : syracuseStep 8044331 = 12066497) B12066497
theorem B2350943 : Blo 1566981 2350943 := bstep (se 1 (by rfl) ⟨1763207, by rfl⟩ : syracuseStep 2350943 = 3526415) B3526415
theorem B2350955 : Blo 1566981 2350955 := bstep (se 1 (by rfl) ⟨1763216, by rfl⟩ : syracuseStep 2350955 = 3526433) B3526433
theorem B5021615 : Blo 1566981 5021615 := bstep (se 1 (by rfl) ⟨3766211, by rfl⟩ : syracuseStep 5021615 = 7532423) B7532423
theorem B10731473 : Blo 1566981 10731473 := bstep (se 2 (by rfl) ⟨4024302, by rfl⟩ : syracuseStep 10731473 = 8048605) B8048605
theorem B8708147 : Blo 1566981 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B2646121 : Blo 1566981 2646121 := bstep (se 2 (by rfl) ⟨992295, by rfl⟩ : syracuseStep 2646121 = 1984591) B1984591
theorem B3768449 : Blo 1566981 3768449 := bstep (se 2 (by rfl) ⟨1413168, by rfl⟩ : syracuseStep 3768449 = 2826337) B2826337
theorem B1884379 : Blo 1566981 1884379 := bstep (se 1 (by rfl) ⟨1413284, by rfl⟩ : syracuseStep 1884379 = 2826569) B2826569
theorem B2351369 : Blo 1566981 2351369 := bstep (se 2 (by rfl) ⟨881763, by rfl⟩ : syracuseStep 2351369 = 1763527) B1763527
theorem B2351471 : Blo 1566981 2351471 := bstep (se 1 (by rfl) ⟨1763603, by rfl⟩ : syracuseStep 2351471 = 3527207) B3527207
theorem B2351687 : Blo 1566981 2351687 := bstep (se 1 (by rfl) ⟨1763765, by rfl⟩ : syracuseStep 2351687 = 3527531) B3527531
theorem B4588103 : Blo 1566981 4588103 := bstep (se 1 (by rfl) ⟨3441077, by rfl⟩ : syracuseStep 4588103 = 6882155) B6882155
theorem B2351723 : Blo 1566981 2351723 := bstep (se 1 (by rfl) ⟨1763792, by rfl⟩ : syracuseStep 2351723 = 3527585) B3527585
theorem B8479403 : Blo 1566981 8479403 := bstep (se 1 (by rfl) ⟨6359552, by rfl⟩ : syracuseStep 8479403 = 12719105) B12719105
theorem B10724023 : Blo 1566981 10724023 := bstep (se 1 (by rfl) ⟨8043017, by rfl⟩ : syracuseStep 10724023 = 16086035) B16086035
theorem B2147051 : Blo 1566981 2147051 := bstep (se 1 (by rfl) ⟨1610288, by rfl⟩ : syracuseStep 2147051 = 3220577) B3220577
theorem B7938809 : Blo 1566981 7938809 := bstep (se 2 (by rfl) ⟨2977053, by rfl⟩ : syracuseStep 7938809 = 5954107) B5954107
theorem B2351951 : Blo 1566981 2351951 := bstep (se 1 (by rfl) ⟨1763963, by rfl⟩ : syracuseStep 2351951 = 3527927) B3527927
theorem B30139289 : Blo 1566981 30139289 := bstep (se 2 (by rfl) ⟨11302233, by rfl⟩ : syracuseStep 30139289 = 22604467) B22604467
theorem B4236263 : Blo 1566981 4236263 := bstep (se 1 (by rfl) ⟨3177197, by rfl⟩ : syracuseStep 4236263 = 6354395) B6354395
theorem B22602851 : Blo 1566981 22602851 := bstep (se 1 (by rfl) ⟨16952138, by rfl⟩ : syracuseStep 22602851 = 33904277) B33904277
theorem B30549109 : Blo 1566981 30549109 := bstep (se 5 (by rfl) ⟨1431989, by rfl⟩ : syracuseStep 30549109 = 2863979) B2863979
theorem B2352347 : Blo 1566981 2352347 := bstep (se 1 (by rfl) ⟨1764260, by rfl⟩ : syracuseStep 2352347 = 3528521) B3528521
theorem B5956841 : Blo 1566981 5956841 := bstep (se 2 (by rfl) ⟨2233815, by rfl⟩ : syracuseStep 5956841 = 4467631) B4467631
theorem B43500887 : Blo 1566981 43500887 := bstep (se 1 (by rfl) ⟨32625665, by rfl⟩ : syracuseStep 43500887 = 65251331) B65251331
theorem B12715373 : Blo 1566981 12715373 := bstep (se 3 (by rfl) ⟨2384132, by rfl⟩ : syracuseStep 12715373 = 4768265) B4768265
theorem B2352521 : Blo 1566981 2352521 := bstep (se 2 (by rfl) ⟨882195, by rfl⟩ : syracuseStep 2352521 = 1764391) B1764391
theorem B1983943 : Blo 1566981 1983943 := bstep (se 1 (by rfl) ⟨1487957, by rfl⟩ : syracuseStep 1983943 = 2975915) B2975915
theorem B128722445 : Blo 1566981 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B11904569 : Blo 1566981 11904569 := bstep (se 2 (by rfl) ⟨4464213, by rfl⟩ : syracuseStep 11904569 = 8928427) B8928427
theorem B1762879 : Blo 1566981 1762879 := bstep (se 1 (by rfl) ⟨1322159, by rfl⟩ : syracuseStep 1762879 = 2644319) B2644319
theorem B397067923 : Blo 1566981 397067923 := bstep (se 1 (by rfl) ⟨297800942, by rfl⟩ : syracuseStep 397067923 = 595601885) B595601885
theorem B4466333 : Blo 1566981 4466333 := bstep (se 3 (by rfl) ⟨837437, by rfl⟩ : syracuseStep 4466333 = 1674875) B1674875
theorem B2975467 : Blo 1566981 2975467 := bstep (se 1 (by rfl) ⟨2231600, by rfl⟩ : syracuseStep 2975467 = 4463201) B4463201
theorem B2352875 : Blo 1566981 2352875 := bstep (se 1 (by rfl) ⟨1764656, by rfl⟩ : syracuseStep 2352875 = 3529313) B3529313
theorem B16959365 : Blo 1566981 16959365 := bstep (se 4 (by rfl) ⟨1589940, by rfl⟩ : syracuseStep 16959365 = 3179881) B3179881
theorem B2353103 : Blo 1566981 2353103 := bstep (se 1 (by rfl) ⟨1764827, by rfl⟩ : syracuseStep 2353103 = 3529655) B3529655
theorem B1567007 : Blo 1566981 1567007 := bstep (se 1 (by rfl) ⟨1175255, by rfl⟩ : syracuseStep 1567007 = 2350511) B2350511
theorem B1567067 : Blo 1566981 1567067 := bstep (se 1 (by rfl) ⟨1175300, by rfl⟩ : syracuseStep 1567067 = 2350601) B2350601
theorem B3967339 : Blo 1566981 3967339 := bstep (se 1 (by rfl) ⟨2975504, by rfl⟩ : syracuseStep 3967339 = 5951009) B5951009
theorem B1567087 : Blo 1566981 1567087 := bstep (se 1 (by rfl) ⟨1175315, by rfl⟩ : syracuseStep 1567087 = 2350631) B2350631
theorem B1763707 : Blo 1566981 1763707 := bstep (se 1 (by rfl) ⟨1322780, by rfl⟩ : syracuseStep 1763707 = 2645561) B2645561
theorem B1567143 : Blo 1566981 1567143 := bstep (se 1 (by rfl) ⟨1175357, by rfl⟩ : syracuseStep 1567143 = 2350715) B2350715
theorem B1788359 : Blo 1566981 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B4524499 : Blo 1566981 4524499 := bstep (se 1 (by rfl) ⟨3393374, by rfl⟩ : syracuseStep 4524499 = 6786749) B6786749
theorem B16091621 : Blo 1566981 16091621 := bstep (se 4 (by rfl) ⟨1508589, by rfl⟩ : syracuseStep 16091621 = 3017179) B3017179
theorem B1567227 : Blo 1566981 1567227 := bstep (se 1 (by rfl) ⟨1175420, by rfl⟩ : syracuseStep 1567227 = 2350841) B2350841
theorem B1567295 : Blo 1566981 1567295 := bstep (se 1 (by rfl) ⟨1175471, by rfl⟩ : syracuseStep 1567295 = 2350943) B2350943
theorem B1985087 : Blo 1566981 1985087 := bstep (se 1 (by rfl) ⟨1488815, by rfl⟩ : syracuseStep 1985087 = 2977631) B2977631
theorem B1567303 : Blo 1566981 1567303 := bstep (se 1 (by rfl) ⟨1175477, by rfl⟩ : syracuseStep 1567303 = 2350955) B2350955
theorem B5294699 : Blo 1566981 5294699 := bstep (se 1 (by rfl) ⟨3971024, by rfl⟩ : syracuseStep 5294699 = 7942049) B7942049
theorem B7154315 : Blo 1566981 7154315 := bstep (se 1 (by rfl) ⟨5365736, by rfl⟩ : syracuseStep 7154315 = 10731473) B10731473
theorem B3967663 : Blo 1566981 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B2976439 : Blo 1566981 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B1567455 : Blo 1566981 1567455 := bstep (se 1 (by rfl) ⟨1175591, by rfl⟩ : syracuseStep 1567455 = 2351183) B2351183
theorem B1567535 : Blo 1566981 1567535 := bstep (se 1 (by rfl) ⟨1175651, by rfl⟩ : syracuseStep 1567535 = 2351303) B2351303
theorem B1764175 : Blo 1566981 1764175 := bstep (se 1 (by rfl) ⟨1323131, by rfl⟩ : syracuseStep 1764175 = 2646263) B2646263
theorem B26790749 : Blo 1566981 26790749 := bstep (se 3 (by rfl) ⟨5023265, by rfl⟩ : syracuseStep 26790749 = 10046531) B10046531
theorem B1567643 : Blo 1566981 1567643 := bstep (se 1 (by rfl) ⟨1175732, by rfl⟩ : syracuseStep 1567643 = 2351465) B2351465
theorem B7154603 : Blo 1566981 7154603 := bstep (se 1 (by rfl) ⟨5365952, by rfl⟩ : syracuseStep 7154603 = 10731905) B10731905
theorem B1567695 : Blo 1566981 1567695 := bstep (se 1 (by rfl) ⟨1175771, by rfl⟩ : syracuseStep 1567695 = 2351543) B2351543
theorem B1567719 : Blo 1566981 1567719 := bstep (se 1 (by rfl) ⟨1175789, by rfl⟩ : syracuseStep 1567719 = 2351579) B2351579
theorem B2976743 : Blo 1566981 2976743 := bstep (se 1 (by rfl) ⟨2232557, by rfl⟩ : syracuseStep 2976743 = 4465115) B4465115
theorem B3967987 : Blo 1566981 3967987 := bstep (se 1 (by rfl) ⟨2975990, by rfl⟩ : syracuseStep 3967987 = 5951981) B5951981
theorem B15068339 : Blo 1566981 15068339 := bstep (se 1 (by rfl) ⟨11301254, by rfl⟩ : syracuseStep 15068339 = 22602509) B22602509
theorem B5295293 : Blo 1566981 5295293 := bstep (se 3 (by rfl) ⟨992867, by rfl⟩ : syracuseStep 5295293 = 1985735) B1985735
theorem B1764571 : Blo 1566981 1764571 := bstep (se 1 (by rfl) ⟨1323428, by rfl⟩ : syracuseStep 1764571 = 2646857) B2646857
theorem B1568031 : Blo 1566981 1568031 := bstep (se 1 (by rfl) ⟨1176023, by rfl⟩ : syracuseStep 1568031 = 2352047) B2352047
theorem B1568091 : Blo 1566981 1568091 := bstep (se 1 (by rfl) ⟨1176068, by rfl⟩ : syracuseStep 1568091 = 2352137) B2352137
theorem B3525983 : Blo 1566981 3525983 := bstep (se 1 (by rfl) ⟨2644487, by rfl⟩ : syracuseStep 3525983 = 5288975) B5288975
theorem B1568111 : Blo 1566981 1568111 := bstep (se 1 (by rfl) ⟨1176083, by rfl⟩ : syracuseStep 1568111 = 2352167) B2352167
theorem B1568167 : Blo 1566981 1568167 := bstep (se 1 (by rfl) ⟨1176125, by rfl⟩ : syracuseStep 1568167 = 2352251) B2352251
theorem B7941563 : Blo 1566981 7941563 := bstep (se 1 (by rfl) ⟨5956172, by rfl⟩ : syracuseStep 7941563 = 11912345) B11912345
theorem B1568251 : Blo 1566981 1568251 := bstep (se 1 (by rfl) ⟨1176188, by rfl⟩ : syracuseStep 1568251 = 2352377) B2352377
theorem B1764859 : Blo 1566981 1764859 := bstep (se 1 (by rfl) ⟨1323644, by rfl⟩ : syracuseStep 1764859 = 2647289) B2647289
theorem B3575353 : Blo 1566981 3575353 := bstep (se 2 (by rfl) ⟨1340757, by rfl⟩ : syracuseStep 3575353 = 2681515) B2681515
theorem B1568319 : Blo 1566981 1568319 := bstep (se 1 (by rfl) ⟨1176239, by rfl⟩ : syracuseStep 1568319 = 2352479) B2352479
theorem B1674815 : Blo 1566981 1674815 := bstep (se 1 (by rfl) ⟨1256111, by rfl⟩ : syracuseStep 1674815 = 2512223) B2512223
theorem B1568327 : Blo 1566981 1568327 := bstep (se 1 (by rfl) ⟨1176245, by rfl⟩ : syracuseStep 1568327 = 2352491) B2352491
theorem B15060653 : Blo 1566981 15060653 := bstep (se 3 (by rfl) ⟨2823872, by rfl⟩ : syracuseStep 15060653 = 5647745) B5647745
theorem B1765039 : Blo 1566981 1765039 := bstep (se 1 (by rfl) ⟨1323779, by rfl⟩ : syracuseStep 1765039 = 2647559) B2647559
theorem B8933075 : Blo 1566981 8933075 := bstep (se 1 (by rfl) ⟨6699806, by rfl⟩ : syracuseStep 8933075 = 13399613) B13399613
theorem B1568479 : Blo 1566981 1568479 := bstep (se 1 (by rfl) ⟨1176359, by rfl⟩ : syracuseStep 1568479 = 2352719) B2352719
theorem B3526379 : Blo 1566981 3526379 := bstep (se 1 (by rfl) ⟨2644784, by rfl⟩ : syracuseStep 3526379 = 5289569) B5289569
theorem B3968747 : Blo 1566981 3968747 := bstep (se 1 (by rfl) ⟨2976560, by rfl⟩ : syracuseStep 3968747 = 5953121) B5953121
theorem B6696715 : Blo 1566981 6696715 := bstep (se 1 (by rfl) ⟨5022536, by rfl⟩ : syracuseStep 6696715 = 10045073) B10045073
theorem B1568559 : Blo 1566981 1568559 := bstep (se 1 (by rfl) ⟨1176419, by rfl⟩ : syracuseStep 1568559 = 2352839) B2352839
theorem B4239161 : Blo 1566981 4239161 := bstep (se 2 (by rfl) ⟨1589685, by rfl⟩ : syracuseStep 4239161 = 3179371) B3179371
theorem B3526505 : Blo 1566981 3526505 := bstep (se 2 (by rfl) ⟨1322439, by rfl⟩ : syracuseStep 3526505 = 2644879) B2644879
theorem B1568667 : Blo 1566981 1568667 := bstep (se 1 (by rfl) ⟨1176500, by rfl⟩ : syracuseStep 1568667 = 2353001) B2353001
theorem B1568719 : Blo 1566981 1568719 := bstep (se 1 (by rfl) ⟨1176539, by rfl⟩ : syracuseStep 1568719 = 2353079) B2353079
theorem B1568743 : Blo 1566981 1568743 := bstep (se 1 (by rfl) ⟨1176557, by rfl⟩ : syracuseStep 1568743 = 2353115) B2353115
theorem B5025817 : Blo 1566981 5025817 := bstep (se 2 (by rfl) ⟨1884681, by rfl⟩ : syracuseStep 5025817 = 3769363) B3769363
theorem B2977897 : Blo 1566981 2977897 := bstep (se 2 (by rfl) ⟨1116711, by rfl⟩ : syracuseStep 2977897 = 2233423) B2233423
theorem B17854667 : Blo 1566981 17854667 := bstep (se 1 (by rfl) ⟨13391000, by rfl⟩ : syracuseStep 17854667 = 26782001) B26782001
theorem B7532747 : Blo 1566981 7532747 := bstep (se 1 (by rfl) ⟨5649560, by rfl⟩ : syracuseStep 7532747 = 11299121) B11299121
theorem B2978299 : Blo 1566981 2978299 := bstep (se 1 (by rfl) ⟨2233724, by rfl⟩ : syracuseStep 2978299 = 4467449) B4467449
theorem B7639571 : Blo 1566981 7639571 := bstep (se 1 (by rfl) ⟨5729678, by rfl⟩ : syracuseStep 7639571 = 11459357) B11459357
theorem B3969607 : Blo 1566981 3969607 := bstep (se 1 (by rfl) ⟨2977205, by rfl⟩ : syracuseStep 3969607 = 5954411) B5954411
theorem B3527351 : Blo 1566981 3527351 := bstep (se 1 (by rfl) ⟨2645513, by rfl⟩ : syracuseStep 3527351 = 5291027) B5291027
theorem B3969719 : Blo 1566981 3969719 := bstep (se 1 (by rfl) ⟨2977289, by rfl⟩ : syracuseStep 3969719 = 5954579) B5954579
theorem B7942859 : Blo 1566981 7942859 := bstep (se 1 (by rfl) ⟨5957144, by rfl⟩ : syracuseStep 7942859 = 11914289) B11914289
theorem B2978527 : Blo 1566981 2978527 := bstep (se 1 (by rfl) ⟨2233895, by rfl⟩ : syracuseStep 2978527 = 4467791) B4467791
theorem B21451549 : Blo 1566981 21451549 := bstep (se 3 (by rfl) ⟨4022165, by rfl⟩ : syracuseStep 21451549 = 8044331) B8044331
theorem B3527567 : Blo 1566981 3527567 := bstep (se 1 (by rfl) ⟨2645675, by rfl⟩ : syracuseStep 3527567 = 5291351) B5291351
theorem B7934921 : Blo 1566981 7934921 := bstep (se 2 (by rfl) ⟨2975595, by rfl⟩ : syracuseStep 7934921 = 5951191) B5951191
theorem B3765491 : Blo 1566981 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B3347743 : Blo 1566981 3347743 := bstep (se 1 (by rfl) ⟨2510807, by rfl⟩ : syracuseStep 3347743 = 5021615) B5021615
theorem B11908457 : Blo 1566981 11908457 := bstep (se 2 (by rfl) ⟨4465671, by rfl⟩ : syracuseStep 11908457 = 8931343) B8931343
theorem B13391243 : Blo 1566981 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B3528287 : Blo 1566981 3528287 := bstep (se 1 (by rfl) ⟨2646215, by rfl⟩ : syracuseStep 3528287 = 5292431) B5292431
theorem B3970721 : Blo 1566981 3970721 := bstep (se 2 (by rfl) ⟨1489020, by rfl⟩ : syracuseStep 3970721 = 2978041) B2978041
theorem B4462391 : Blo 1566981 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B3528503 : Blo 1566981 3528503 := bstep (se 1 (by rfl) ⟨2646377, by rfl⟩ : syracuseStep 3528503 = 5292755) B5292755
theorem B3766297 : Blo 1566981 3766297 := bstep (se 2 (by rfl) ⟨1412361, by rfl⟩ : syracuseStep 3766297 = 2824723) B2824723
theorem B3528809 : Blo 1566981 3528809 := bstep (se 2 (by rfl) ⟨1323303, by rfl⟩ : syracuseStep 3528809 = 2646607) B2646607
theorem B3971177 : Blo 1566981 3971177 := bstep (se 2 (by rfl) ⟨1489191, by rfl⟩ : syracuseStep 3971177 = 2978383) B2978383
theorem B3348947 : Blo 1566981 3348947 := bstep (se 1 (by rfl) ⟨2511710, by rfl⟩ : syracuseStep 3348947 = 5023421) B5023421
theorem B152656427 : Blo 1566981 152656427 := bstep (se 1 (by rfl) ⟨114492320, by rfl⟩ : syracuseStep 152656427 = 228984641) B228984641
theorem B1882687 : Blo 1566981 1882687 := bstep (se 1 (by rfl) ⟨1412015, by rfl⟩ : syracuseStep 1882687 = 2824031) B2824031
theorem B13400639 : Blo 1566981 13400639 := bstep (se 1 (by rfl) ⟨10050479, by rfl⟩ : syracuseStep 13400639 = 20100959) B20100959
theorem B3529295 : Blo 1566981 3529295 := bstep (se 1 (by rfl) ⟨2646971, by rfl⟩ : syracuseStep 3529295 = 5293943) B5293943
theorem B2644663 : Blo 1566981 2644663 := bstep (se 1 (by rfl) ⟨1983497, by rfl⟩ : syracuseStep 2644663 = 3966995) B3966995
theorem B3529439 : Blo 1566981 3529439 := bstep (se 1 (by rfl) ⟨2647079, by rfl⟩ : syracuseStep 3529439 = 5294159) B5294159
theorem B4463531 : Blo 1566981 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B3529691 : Blo 1566981 3529691 := bstep (se 1 (by rfl) ⟨2647268, by rfl⟩ : syracuseStep 3529691 = 5294537) B5294537
theorem B2644967 : Blo 1566981 2644967 := bstep (se 1 (by rfl) ⟨1983725, by rfl⟩ : syracuseStep 2644967 = 3967451) B3967451
theorem B3767393 : Blo 1566981 3767393 := bstep (se 2 (by rfl) ⟨1412772, by rfl⟩ : syracuseStep 3767393 = 2825545) B2825545
theorem B3529871 : Blo 1566981 3529871 := bstep (se 1 (by rfl) ⟨2647403, by rfl⟩ : syracuseStep 3529871 = 5294807) B5294807
theorem B10722469 : Blo 1566981 10722469 := bstep (se 4 (by rfl) ⟨1005231, by rfl⟩ : syracuseStep 10722469 = 2010463) B2010463
theorem B4766939 : Blo 1566981 4766939 := bstep (se 1 (by rfl) ⟨3575204, by rfl⟩ : syracuseStep 4766939 = 7150409) B7150409
theorem B3529961 : Blo 1566981 3529961 := bstep (se 2 (by rfl) ⟨1323735, by rfl⟩ : syracuseStep 3529961 = 2647471) B2647471
theorem B3530015 : Blo 1566981 3530015 := bstep (se 1 (by rfl) ⟨2647511, by rfl⟩ : syracuseStep 3530015 = 5295023) B5295023
theorem B110042549 : Blo 1566981 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B2350535 : Blo 1566981 2350535 := bstep (se 1 (by rfl) ⟨1762901, by rfl⟩ : syracuseStep 2350535 = 3525803) B3525803
theorem B33889751 : Blo 1566981 33889751 := bstep (se 1 (by rfl) ⟨25417313, by rfl⟩ : syracuseStep 33889751 = 50834627) B50834627
theorem B5651927 : Blo 1566981 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B5291513 : Blo 1566981 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B5955065 : Blo 1566981 5955065 := bstep (se 2 (by rfl) ⟨2233149, by rfl⟩ : syracuseStep 5955065 = 4466299) B4466299
theorem B11296351 : Blo 1566981 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B2416223 : Blo 1566981 2416223 := bstep (se 1 (by rfl) ⟨1812167, by rfl⟩ : syracuseStep 2416223 = 3624335) B3624335
theorem B5021345 : Blo 1566981 5021345 := bstep (se 2 (by rfl) ⟨1883004, by rfl⟩ : syracuseStep 5021345 = 3766009) B3766009
theorem B11902625 : Blo 1566981 11902625 := bstep (se 2 (by rfl) ⟨4463484, by rfl⟩ : syracuseStep 11902625 = 8926969) B8926969
theorem B3350177 : Blo 1566981 3350177 := bstep (se 2 (by rfl) ⟨1256316, by rfl⟩ : syracuseStep 3350177 = 2512633) B2512633
theorem B5291783 : Blo 1566981 5291783 := bstep (se 1 (by rfl) ⟨3968837, by rfl⟩ : syracuseStep 5291783 = 7937675) B7937675
theorem B3350279 : Blo 1566981 3350279 := bstep (se 1 (by rfl) ⟨2512709, by rfl⟩ : syracuseStep 3350279 = 5025419) B5025419
theorem B2350889 : Blo 1566981 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B12721961 : Blo 1566981 12721961 := bstep (se 2 (by rfl) ⟨4770735, by rfl⟩ : syracuseStep 12721961 = 9541471) B9541471
theorem B2350895 : Blo 1566981 2350895 := bstep (se 1 (by rfl) ⟨1763171, by rfl⟩ : syracuseStep 2350895 = 3526343) B3526343
theorem B5652271 : Blo 1566981 5652271 := bstep (se 1 (by rfl) ⟨4239203, by rfl⟩ : syracuseStep 5652271 = 8478407) B8478407
theorem B5291837 : Blo 1566981 5291837 := bstep (se 3 (by rfl) ⟨992219, by rfl⟩ : syracuseStep 5291837 = 1984439) B1984439
theorem B5021729 : Blo 1566981 5021729 := bstep (se 2 (by rfl) ⟨1883148, by rfl⟩ : syracuseStep 5021729 = 3766297) B3766297
theorem B6701089 : Blo 1566981 6701089 := bstep (se 2 (by rfl) ⟨2512908, by rfl⟩ : syracuseStep 6701089 = 5025817) B5025817
theorem B11903111 : Blo 1566981 11903111 := bstep (se 1 (by rfl) ⟨8927333, by rfl⟩ : syracuseStep 11903111 = 17854667) B17854667
theorem B5021831 : Blo 1566981 5021831 := bstep (se 1 (by rfl) ⟨3766373, by rfl⟩ : syracuseStep 5021831 = 7532747) B7532747
theorem B5652935 : Blo 1566981 5652935 := bstep (se 1 (by rfl) ⟨4239701, by rfl⟩ : syracuseStep 5652935 = 8479403) B8479403
theorem B2351567 : Blo 1566981 2351567 := bstep (se 1 (by rfl) ⟨1763675, by rfl⟩ : syracuseStep 2351567 = 3527351) B3527351
theorem B2646479 : Blo 1566981 2646479 := bstep (se 1 (by rfl) ⟨1984859, by rfl⟩ : syracuseStep 2646479 = 3969719) B3969719
theorem B2351609 : Blo 1566981 2351609 := bstep (se 2 (by rfl) ⟨881853, by rfl⟩ : syracuseStep 2351609 = 1763707) B1763707
theorem B5292539 : Blo 1566981 5292539 := bstep (se 1 (by rfl) ⟨3969404, by rfl⟩ : syracuseStep 5292539 = 7938809) B7938809
theorem B2351711 : Blo 1566981 2351711 := bstep (se 1 (by rfl) ⟨1763783, by rfl⟩ : syracuseStep 2351711 = 3527567) B3527567
theorem B5292809 : Blo 1566981 5292809 := bstep (se 2 (by rfl) ⟨1984803, by rfl⟩ : syracuseStep 5292809 = 3969607) B3969607
theorem B29000591 : Blo 1566981 29000591 := bstep (se 1 (by rfl) ⟨21750443, by rfl⟩ : syracuseStep 29000591 = 43500887) B43500887
theorem B7938971 : Blo 1566981 7938971 := bstep (se 1 (by rfl) ⟨5954228, by rfl⟩ : syracuseStep 7938971 = 11908457) B11908457
theorem B2352191 : Blo 1566981 2352191 := bstep (se 1 (by rfl) ⟨1764143, by rfl⟩ : syracuseStep 2352191 = 3528287) B3528287
theorem B2352233 : Blo 1566981 2352233 := bstep (se 2 (by rfl) ⟨882087, by rfl⟩ : syracuseStep 2352233 = 1764175) B1764175
theorem B2647147 : Blo 1566981 2647147 := bstep (se 1 (by rfl) ⟨1985360, by rfl⟩ : syracuseStep 2647147 = 3970721) B3970721
theorem B4768957 : Blo 1566981 4768957 := bstep (se 3 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 4768957 = 1788359) B1788359
theorem B2352335 : Blo 1566981 2352335 := bstep (se 1 (by rfl) ⟨1764251, by rfl⟩ : syracuseStep 2352335 = 3528503) B3528503
theorem B11306243 : Blo 1566981 11306243 := bstep (se 1 (by rfl) ⟨8479682, by rfl⟩ : syracuseStep 11306243 = 16959365) B16959365
theorem B2352539 : Blo 1566981 2352539 := bstep (se 1 (by rfl) ⟨1764404, by rfl⟩ : syracuseStep 2352539 = 3528809) B3528809
theorem B2647451 : Blo 1566981 2647451 := bstep (se 1 (by rfl) ⟨1985588, by rfl⟩ : syracuseStep 2647451 = 3971177) B3971177
theorem B40732145 : Blo 1566981 40732145 := bstep (se 2 (by rfl) ⟨15274554, by rfl⟩ : syracuseStep 40732145 = 30549109) B30549109
theorem B4466173 : Blo 1566981 4466173 := bstep (se 3 (by rfl) ⟨837407, by rfl⟩ : syracuseStep 4466173 = 1674815) B1674815
theorem B5293565 : Blo 1566981 5293565 := bstep (se 3 (by rfl) ⟨992543, by rfl⟩ : syracuseStep 5293565 = 1985087) B1985087
theorem B14296625 : Blo 1566981 14296625 := bstep (se 2 (by rfl) ⟨5361234, by rfl⟩ : syracuseStep 14296625 = 10722469) B10722469
theorem B2352761 : Blo 1566981 2352761 := bstep (se 2 (by rfl) ⟨882285, by rfl⟩ : syracuseStep 2352761 = 1764571) B1764571
theorem B101770951 : Blo 1566981 101770951 := bstep (se 1 (by rfl) ⟨76328213, by rfl⟩ : syracuseStep 101770951 = 152656427) B152656427
theorem B2352863 : Blo 1566981 2352863 := bstep (se 1 (by rfl) ⟨1764647, by rfl⟩ : syracuseStep 2352863 = 3529295) B3529295
theorem B4769543 : Blo 1566981 4769543 := bstep (se 1 (by rfl) ⟨3577157, by rfl⟩ : syracuseStep 4769543 = 7154315) B7154315
theorem B2352959 : Blo 1566981 2352959 := bstep (se 1 (by rfl) ⟨1764719, by rfl⟩ : syracuseStep 2352959 = 3529439) B3529439
theorem B17860499 : Blo 1566981 17860499 := bstep (se 1 (by rfl) ⟨13395374, by rfl⟩ : syracuseStep 17860499 = 26790749) B26790749
theorem B2975687 : Blo 1566981 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B4769735 : Blo 1566981 4769735 := bstep (se 1 (by rfl) ⟨3577301, by rfl⟩ : syracuseStep 4769735 = 7154603) B7154603
theorem B2353127 : Blo 1566981 2353127 := bstep (se 1 (by rfl) ⟨1764845, by rfl⟩ : syracuseStep 2353127 = 3529691) B3529691
theorem B1763311 : Blo 1566981 1763311 := bstep (se 1 (by rfl) ⟨1322483, by rfl⟩ : syracuseStep 1763311 = 2644967) B2644967
theorem B1984495 : Blo 1566981 1984495 := bstep (se 1 (by rfl) ⟨1488371, by rfl⟩ : syracuseStep 1984495 = 2976743) B2976743
theorem B2353145 : Blo 1566981 2353145 := bstep (se 2 (by rfl) ⟨882429, by rfl⟩ : syracuseStep 2353145 = 1764859) B1764859
theorem B2353247 : Blo 1566981 2353247 := bstep (se 1 (by rfl) ⟨1764935, by rfl⟩ : syracuseStep 2353247 = 3529871) B3529871
theorem B10045559 : Blo 1566981 10045559 := bstep (se 1 (by rfl) ⟨7534169, by rfl⟩ : syracuseStep 10045559 = 15068339) B15068339
theorem B2353307 : Blo 1566981 2353307 := bstep (se 1 (by rfl) ⟨1764980, by rfl⟩ : syracuseStep 2353307 = 3529961) B3529961
theorem B2353343 : Blo 1566981 2353343 := bstep (se 1 (by rfl) ⟨1765007, by rfl⟩ : syracuseStep 2353343 = 3530015) B3530015
theorem B2353385 : Blo 1566981 2353385 := bstep (se 2 (by rfl) ⟨882519, by rfl⟩ : syracuseStep 2353385 = 1765039) B1765039
theorem B73361699 : Blo 1566981 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B5294375 : Blo 1566981 5294375 := bstep (se 1 (by rfl) ⟨3970781, by rfl⟩ : syracuseStep 5294375 = 7941563) B7941563
theorem B1567023 : Blo 1566981 1567023 := bstep (se 1 (by rfl) ⟨1175267, by rfl⟩ : syracuseStep 1567023 = 2350535) B2350535
theorem B3967289 : Blo 1566981 3967289 := bstep (se 2 (by rfl) ⟨1487733, by rfl⟩ : syracuseStep 3967289 = 2975467) B2975467
theorem B1567259 : Blo 1566981 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B8481307 : Blo 1566981 8481307 := bstep (se 1 (by rfl) ⟨6360980, by rfl⟩ : syracuseStep 8481307 = 12721961) B12721961
theorem B1567263 : Blo 1566981 1567263 := bstep (se 1 (by rfl) ⟨1175447, by rfl⟩ : syracuseStep 1567263 = 2350895) B2350895
theorem B1567579 : Blo 1566981 1567579 := bstep (se 1 (by rfl) ⟨1175684, by rfl⟩ : syracuseStep 1567579 = 2351369) B2351369
theorem B1567647 : Blo 1566981 1567647 := bstep (se 1 (by rfl) ⟨1175735, by rfl⟩ : syracuseStep 1567647 = 2351471) B2351471
theorem B1567791 : Blo 1566981 1567791 := bstep (se 1 (by rfl) ⟨1175843, by rfl⟩ : syracuseStep 1567791 = 2351687) B2351687
theorem B3058735 : Blo 1566981 3058735 := bstep (se 1 (by rfl) ⟨2294051, by rfl⟩ : syracuseStep 3058735 = 4588103) B4588103
theorem B1567815 : Blo 1566981 1567815 := bstep (se 1 (by rfl) ⟨1175861, by rfl⟩ : syracuseStep 1567815 = 2351723) B2351723
theorem B5295239 : Blo 1566981 5295239 := bstep (se 1 (by rfl) ⟨3971429, by rfl⟩ : syracuseStep 5295239 = 7942859) B7942859
theorem B1567967 : Blo 1566981 1567967 := bstep (se 1 (by rfl) ⟨1175975, by rfl⟩ : syracuseStep 1567967 = 2351951) B2351951
theorem B6032665 : Blo 1566981 6032665 := bstep (se 2 (by rfl) ⟨2262249, by rfl⟩ : syracuseStep 6032665 = 4524499) B4524499
theorem B15068567 : Blo 1566981 15068567 := bstep (se 1 (by rfl) ⟨11301425, by rfl⟩ : syracuseStep 15068567 = 22602851) B22602851
theorem B2510249 : Blo 1566981 2510249 := bstep (se 2 (by rfl) ⟨941343, by rfl⟩ : syracuseStep 2510249 = 1882687) B1882687
theorem B1568231 : Blo 1566981 1568231 := bstep (se 1 (by rfl) ⟨1176173, by rfl⟩ : syracuseStep 1568231 = 2352347) B2352347
theorem B2510327 : Blo 1566981 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B3526217 : Blo 1566981 3526217 := bstep (se 2 (by rfl) ⟨1322331, by rfl⟩ : syracuseStep 3526217 = 2644663) B2644663
theorem B14298697 : Blo 1566981 14298697 := bstep (se 2 (by rfl) ⟨5362011, by rfl⟩ : syracuseStep 14298697 = 10724023) B10724023
theorem B3968585 : Blo 1566981 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B1568347 : Blo 1566981 1568347 := bstep (se 1 (by rfl) ⟨1176260, by rfl⟩ : syracuseStep 1568347 = 2352521) B2352521
theorem B85814963 : Blo 1566981 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B28602065 : Blo 1566981 28602065 := bstep (se 2 (by rfl) ⟨10725774, by rfl⟩ : syracuseStep 28602065 = 21451549) B21451549
theorem B2977555 : Blo 1566981 2977555 := bstep (se 1 (by rfl) ⟨2233166, by rfl⟩ : syracuseStep 2977555 = 4466333) B4466333
theorem B1568583 : Blo 1566981 1568583 := bstep (se 1 (by rfl) ⟨1176437, by rfl⟩ : syracuseStep 1568583 = 2352875) B2352875
theorem B1568735 : Blo 1566981 1568735 := bstep (se 1 (by rfl) ⟨1176551, by rfl⟩ : syracuseStep 1568735 = 2353103) B2353103
theorem B2232631 : Blo 1566981 2232631 := bstep (se 1 (by rfl) ⟨1674473, by rfl⟩ : syracuseStep 2232631 = 3348947) B3348947
theorem B10727747 : Blo 1566981 10727747 := bstep (se 1 (by rfl) ⟨8045810, by rfl⟩ : syracuseStep 10727747 = 16091621) B16091621
theorem B8933759 : Blo 1566981 8933759 := bstep (se 1 (by rfl) ⟨6700319, by rfl⟩ : syracuseStep 8933759 = 13400639) B13400639
theorem B8934077 : Blo 1566981 8934077 := bstep (se 3 (by rfl) ⟨1675139, by rfl⟩ : syracuseStep 8934077 = 3350279) B3350279
theorem B2511595 : Blo 1566981 2511595 := bstep (se 1 (by rfl) ⟨1883696, by rfl⟩ : syracuseStep 2511595 = 3767393) B3767393
theorem B15061801 : Blo 1566981 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B11899709 : Blo 1566981 11899709 := bstep (se 3 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 11899709 = 4462391) B4462391
theorem B3527675 : Blo 1566981 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B3970043 : Blo 1566981 3970043 := bstep (se 1 (by rfl) ⟨2977532, by rfl⟩ : syracuseStep 3970043 = 5955065) B5955065
theorem B1610815 : Blo 1566981 1610815 := bstep (se 1 (by rfl) ⟨1208111, by rfl⟩ : syracuseStep 1610815 = 2416223) B2416223
theorem B3347563 : Blo 1566981 3347563 := bstep (se 1 (by rfl) ⟨2510672, by rfl⟩ : syracuseStep 3347563 = 5021345) B5021345
theorem B7935083 : Blo 1566981 7935083 := bstep (se 1 (by rfl) ⟨5951312, by rfl⟩ : syracuseStep 7935083 = 11902625) B11902625
theorem B2233451 : Blo 1566981 2233451 := bstep (se 1 (by rfl) ⟨1675088, by rfl⟩ : syracuseStep 2233451 = 3350177) B3350177
theorem B10040435 : Blo 1566981 10040435 := bstep (se 1 (by rfl) ⟨7530326, by rfl⟩ : syracuseStep 10040435 = 15060653) B15060653
theorem B3527855 : Blo 1566981 3527855 := bstep (se 1 (by rfl) ⟨2645891, by rfl⟩ : syracuseStep 3527855 = 5291783) B5291783
theorem B3527891 : Blo 1566981 3527891 := bstep (se 1 (by rfl) ⟨2645918, by rfl⟩ : syracuseStep 3527891 = 5291837) B5291837
theorem B5805431 : Blo 1566981 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B3528161 : Blo 1566981 3528161 := bstep (se 2 (by rfl) ⟨1323060, by rfl⟩ : syracuseStep 3528161 = 2646121) B2646121
theorem B3970529 : Blo 1566981 3970529 := bstep (se 2 (by rfl) ⟨1488948, by rfl⟩ : syracuseStep 3970529 = 2977897) B2977897
theorem B2512505 : Blo 1566981 2512505 := bstep (se 2 (by rfl) ⟨942189, by rfl⟩ : syracuseStep 2512505 = 1884379) B1884379
theorem B10049197 : Blo 1566981 10049197 := bstep (se 3 (by rfl) ⟨1884224, by rfl⟩ : syracuseStep 10049197 = 3768449) B3768449
theorem B5093047 : Blo 1566981 5093047 := bstep (se 1 (by rfl) ⟨3819785, by rfl⟩ : syracuseStep 5093047 = 7639571) B7639571
theorem B5289785 : Blo 1566981 5289785 := bstep (se 2 (by rfl) ⟨1983669, by rfl⟩ : syracuseStep 5289785 = 3967339) B3967339
theorem B20092859 : Blo 1566981 20092859 := bstep (se 1 (by rfl) ⟨15069644, by rfl⟩ : syracuseStep 20092859 = 30139289) B30139289
theorem B5289947 : Blo 1566981 5289947 := bstep (se 1 (by rfl) ⟨3967460, by rfl⟩ : syracuseStep 5289947 = 7934921) B7934921
theorem B2824175 : Blo 1566981 2824175 := bstep (se 1 (by rfl) ⟨2118131, by rfl⟩ : syracuseStep 2824175 = 4236263) B4236263
theorem B3971065 : Blo 1566981 3971065 := bstep (se 2 (by rfl) ⟨1489149, by rfl⟩ : syracuseStep 3971065 = 2978299) B2978299
theorem B2117695589 : Blo 1566981 2117695589 := bstep (se 4 (by rfl) ⟨198533961, by rfl⟩ : syracuseStep 2117695589 = 397067923) B397067923
theorem B3971227 : Blo 1566981 3971227 := bstep (se 1 (by rfl) ⟨2978420, by rfl⟩ : syracuseStep 3971227 = 5956841) B5956841
theorem B5290217 : Blo 1566981 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B8476915 : Blo 1566981 8476915 := bstep (se 1 (by rfl) ⟨6357686, by rfl⟩ : syracuseStep 8476915 = 12715373) B12715373
theorem B8927495 : Blo 1566981 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B3971369 : Blo 1566981 3971369 := bstep (se 2 (by rfl) ⟨1489263, by rfl⟩ : syracuseStep 3971369 = 2978527) B2978527
theorem B7936379 : Blo 1566981 7936379 := bstep (se 1 (by rfl) ⟨5952284, by rfl⟩ : syracuseStep 7936379 = 11904569) B11904569
theorem B5290649 : Blo 1566981 5290649 := bstep (se 2 (by rfl) ⟨1983993, by rfl⟩ : syracuseStep 5290649 = 3967987) B3967987
theorem B4463657 : Blo 1566981 4463657 := bstep (se 2 (by rfl) ⟨1673871, by rfl⟩ : syracuseStep 4463657 = 3347743) B3347743
theorem B3529799 : Blo 1566981 3529799 := bstep (se 1 (by rfl) ⟨2647349, by rfl⟩ : syracuseStep 3529799 = 5294699) B5294699
theorem B2645257 : Blo 1566981 2645257 := bstep (se 2 (by rfl) ⟨991971, by rfl⟩ : syracuseStep 2645257 = 1983943) B1983943
theorem B5725469 : Blo 1566981 5725469 := bstep (se 3 (by rfl) ⟨1073525, by rfl⟩ : syracuseStep 5725469 = 2147051) B2147051
theorem B4767137 : Blo 1566981 4767137 := bstep (se 2 (by rfl) ⟨1787676, by rfl⟩ : syracuseStep 4767137 = 3575353) B3575353
theorem B2350505 : Blo 1566981 2350505 := bstep (se 2 (by rfl) ⟨881439, by rfl⟩ : syracuseStep 2350505 = 1762879) B1762879
theorem B3530195 : Blo 1566981 3530195 := bstep (se 1 (by rfl) ⟨2647646, by rfl⟩ : syracuseStep 3530195 = 5295293) B5295293
theorem B3177959 : Blo 1566981 3177959 := bstep (se 1 (by rfl) ⟨2383469, by rfl⟩ : syracuseStep 3177959 = 4766939) B4766939
theorem B2350655 : Blo 1566981 2350655 := bstep (se 1 (by rfl) ⟨1762991, by rfl⟩ : syracuseStep 2350655 = 3525983) B3525983
theorem B22593167 : Blo 1566981 22593167 := bstep (se 1 (by rfl) ⟨16944875, by rfl⟩ : syracuseStep 22593167 = 33889751) B33889751
theorem B3767951 : Blo 1566981 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B8928953 : Blo 1566981 8928953 := bstep (se 2 (by rfl) ⟨3348357, by rfl⟩ : syracuseStep 8928953 = 6696715) B6696715
theorem B7536361 : Blo 1566981 7536361 := bstep (se 2 (by rfl) ⟨2826135, by rfl⟩ : syracuseStep 7536361 = 5652271) B5652271
theorem B5955383 : Blo 1566981 5955383 := bstep (se 1 (by rfl) ⟨4466537, by rfl⟩ : syracuseStep 5955383 = 8933075) B8933075
theorem B2350919 : Blo 1566981 2350919 := bstep (se 1 (by rfl) ⟨1763189, by rfl⟩ : syracuseStep 2350919 = 3526379) B3526379
theorem B2645831 : Blo 1566981 2645831 := bstep (se 1 (by rfl) ⟨1984373, by rfl⟩ : syracuseStep 2645831 = 3968747) B3968747
theorem B2826107 : Blo 1566981 2826107 := bstep (se 1 (by rfl) ⟨2119580, by rfl⟩ : syracuseStep 2826107 = 4239161) B4239161
theorem B2351003 : Blo 1566981 2351003 := bstep (se 1 (by rfl) ⟨1763252, by rfl⟩ : syracuseStep 2351003 = 3526505) B3526505
theorem B7151831 : Blo 1566981 7151831 := bstep (se 1 (by rfl) ⟨5363873, by rfl⟩ : syracuseStep 7151831 = 10727747) B10727747
theorem B5955839 : Blo 1566981 5955839 := bstep (se 1 (by rfl) ⟨4466879, by rfl⟩ : syracuseStep 5955839 = 8933759) B8933759
theorem B5955869 : Blo 1566981 5955869 := bstep (se 3 (by rfl) ⟨1116725, by rfl⟩ : syracuseStep 5955869 = 2233451) B2233451
theorem B3768623 : Blo 1566981 3768623 := bstep (se 1 (by rfl) ⟨2826467, by rfl⟩ : syracuseStep 3768623 = 5652935) B5652935
theorem B5956051 : Blo 1566981 5956051 := bstep (se 1 (by rfl) ⟨4467038, by rfl⟩ : syracuseStep 5956051 = 8934077) B8934077
theorem B19333727 : Blo 1566981 19333727 := bstep (se 1 (by rfl) ⟨14500295, by rfl⟩ : syracuseStep 19333727 = 29000591) B29000591
theorem B5292647 : Blo 1566981 5292647 := bstep (se 1 (by rfl) ⟨3969485, by rfl⟩ : syracuseStep 5292647 = 7938971) B7938971
theorem B2351783 : Blo 1566981 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B2646695 : Blo 1566981 2646695 := bstep (se 1 (by rfl) ⟨1985021, by rfl⟩ : syracuseStep 2646695 = 3970043) B3970043
theorem B6693623 : Blo 1566981 6693623 := bstep (se 1 (by rfl) ⟨5020217, by rfl⟩ : syracuseStep 6693623 = 10040435) B10040435
theorem B2351903 : Blo 1566981 2351903 := bstep (se 1 (by rfl) ⟨1763927, by rfl⟩ : syracuseStep 2351903 = 3527855) B3527855
theorem B2351927 : Blo 1566981 2351927 := bstep (se 1 (by rfl) ⟨1763945, by rfl⟩ : syracuseStep 2351927 = 3527891) B3527891
theorem B2352107 : Blo 1566981 2352107 := bstep (se 1 (by rfl) ⟨1764080, by rfl⟩ : syracuseStep 2352107 = 3528161) B3528161
theorem B2647019 : Blo 1566981 2647019 := bstep (se 1 (by rfl) ⟨1985264, by rfl⟩ : syracuseStep 2647019 = 3970529) B3970529
theorem B6693997 : Blo 1566981 6693997 := bstep (se 3 (by rfl) ⟨1255124, by rfl⟩ : syracuseStep 6693997 = 2510249) B2510249
theorem B3179695 : Blo 1566981 3179695 := bstep (se 1 (by rfl) ⟨2384771, by rfl⟩ : syracuseStep 3179695 = 4769543) B4769543
theorem B13395239 : Blo 1566981 13395239 := bstep (se 1 (by rfl) ⟨10046429, by rfl⟩ : syracuseStep 13395239 = 20092859) B20092859
theorem B1983791 : Blo 1566981 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B2147753 : Blo 1566981 2147753 := bstep (se 2 (by rfl) ⟨805407, by rfl⟩ : syracuseStep 2147753 = 1610815) B1610815
theorem B48907799 : Blo 1566981 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B2647579 : Blo 1566981 2647579 := bstep (se 1 (by rfl) ⟨1985684, by rfl⟩ : syracuseStep 2647579 = 3971369) B3971369
theorem B6358609 : Blo 1566981 6358609 := bstep (se 2 (by rfl) ⟨2384478, by rfl⟩ : syracuseStep 6358609 = 4768957) B4768957
theorem B2975771 : Blo 1566981 2975771 := bstep (se 1 (by rfl) ⟨2231828, by rfl⟩ : syracuseStep 2975771 = 4463657) B4463657
theorem B2353199 : Blo 1566981 2353199 := bstep (se 1 (by rfl) ⟨1764899, by rfl⟩ : syracuseStep 2353199 = 3529799) B3529799
theorem B19064929 : Blo 1566981 19064929 := bstep (se 2 (by rfl) ⟨7149348, by rfl⟩ : syracuseStep 19064929 = 14298697) B14298697
theorem B135694601 : Blo 1566981 135694601 := bstep (se 2 (by rfl) ⟨50885475, by rfl⟩ : syracuseStep 135694601 = 101770951) B101770951
theorem B10045711 : Blo 1566981 10045711 := bstep (se 1 (by rfl) ⟨7534283, by rfl⟩ : syracuseStep 10045711 = 15068567) B15068567
theorem B1567003 : Blo 1566981 1567003 := bstep (se 1 (by rfl) ⟨1175252, by rfl⟩ : syracuseStep 1567003 = 2350505) B2350505
theorem B2353463 : Blo 1566981 2353463 := bstep (se 1 (by rfl) ⟨1765097, by rfl⟩ : syracuseStep 2353463 = 3530195) B3530195
theorem B1673551 : Blo 1566981 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B1567103 : Blo 1566981 1567103 := bstep (se 1 (by rfl) ⟨1175327, by rfl⟩ : syracuseStep 1567103 = 2350655) B2350655
theorem B1567279 : Blo 1566981 1567279 := bstep (se 1 (by rfl) ⟨1175459, by rfl⟩ : syracuseStep 1567279 = 2350919) B2350919
theorem B1763887 : Blo 1566981 1763887 := bstep (se 1 (by rfl) ⟨1322915, by rfl⟩ : syracuseStep 1763887 = 2645831) B2645831
theorem B1567335 : Blo 1566981 1567335 := bstep (se 1 (by rfl) ⟨1175501, by rfl⟩ : syracuseStep 1567335 = 2351003) B2351003
theorem B5294753 : Blo 1566981 5294753 := bstep (se 2 (by rfl) ⟨1985532, by rfl⟩ : syracuseStep 5294753 = 3971065) B3971065
theorem B5294969 : Blo 1566981 5294969 := bstep (se 2 (by rfl) ⟨1985613, by rfl⟩ : syracuseStep 5294969 = 3971227) B3971227
theorem B1567711 : Blo 1566981 1567711 := bstep (se 1 (by rfl) ⟨1175783, by rfl⟩ : syracuseStep 1567711 = 2351567) B2351567
theorem B1764319 : Blo 1566981 1764319 := bstep (se 1 (by rfl) ⟨1323239, by rfl⟩ : syracuseStep 1764319 = 2646479) B2646479
theorem B1567739 : Blo 1566981 1567739 := bstep (se 1 (by rfl) ⟨1175804, by rfl⟩ : syracuseStep 1567739 = 2351609) B2351609
theorem B1567807 : Blo 1566981 1567807 := bstep (se 1 (by rfl) ⟨1175855, by rfl⟩ : syracuseStep 1567807 = 2351711) B2351711
theorem B2976841 : Blo 1566981 2976841 := bstep (se 2 (by rfl) ⟨1116315, by rfl⟩ : syracuseStep 2976841 = 2232631) B2232631
theorem B7933139 : Blo 1566981 7933139 := bstep (se 1 (by rfl) ⟨5949854, by rfl⟩ : syracuseStep 7933139 = 11899709) B11899709
theorem B30149981 : Blo 1566981 30149981 := bstep (se 3 (by rfl) ⟨5653121, by rfl⟩ : syracuseStep 30149981 = 11306243) B11306243
theorem B11308409 : Blo 1566981 11308409 := bstep (se 2 (by rfl) ⟨4240653, by rfl⟩ : syracuseStep 11308409 = 8481307) B8481307
theorem B1568127 : Blo 1566981 1568127 := bstep (se 1 (by rfl) ⟨1176095, by rfl⟩ : syracuseStep 1568127 = 2352191) B2352191
theorem B1568155 : Blo 1566981 1568155 := bstep (se 1 (by rfl) ⟨1176116, by rfl⟩ : syracuseStep 1568155 = 2352233) B2352233
theorem B1568223 : Blo 1566981 1568223 := bstep (se 1 (by rfl) ⟨1176167, by rfl⟩ : syracuseStep 1568223 = 2352335) B2352335
theorem B3870287 : Blo 1566981 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B1568359 : Blo 1566981 1568359 := bstep (se 1 (by rfl) ⟨1176269, by rfl⟩ : syracuseStep 1568359 = 2352539) B2352539
theorem B1764967 : Blo 1566981 1764967 := bstep (se 1 (by rfl) ⟨1323725, by rfl⟩ : syracuseStep 1764967 = 2647451) B2647451
theorem B9531083 : Blo 1566981 9531083 := bstep (se 1 (by rfl) ⟨7148312, by rfl⟩ : syracuseStep 9531083 = 14296625) B14296625
theorem B20082401 : Blo 1566981 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B1568507 : Blo 1566981 1568507 := bstep (se 1 (by rfl) ⟨1176380, by rfl⟩ : syracuseStep 1568507 = 2352761) B2352761
theorem B1675003 : Blo 1566981 1675003 := bstep (se 1 (by rfl) ⟨1256252, by rfl⟩ : syracuseStep 1675003 = 2512505) B2512505
theorem B1568575 : Blo 1566981 1568575 := bstep (se 1 (by rfl) ⟨1176431, by rfl⟩ : syracuseStep 1568575 = 2352863) B2352863
theorem B3526523 : Blo 1566981 3526523 := bstep (se 1 (by rfl) ⟨2644892, by rfl⟩ : syracuseStep 3526523 = 5289785) B5289785
theorem B1568639 : Blo 1566981 1568639 := bstep (se 1 (by rfl) ⟨1176479, by rfl⟩ : syracuseStep 1568639 = 2352959) B2352959
theorem B11906999 : Blo 1566981 11906999 := bstep (se 1 (by rfl) ⟨8930249, by rfl⟩ : syracuseStep 11906999 = 17860499) B17860499
theorem B8474557 : Blo 1566981 8474557 := bstep (se 3 (by rfl) ⟨1588979, by rfl⟩ : syracuseStep 8474557 = 3177959) B3177959
theorem B3526631 : Blo 1566981 3526631 := bstep (se 1 (by rfl) ⟨2644973, by rfl⟩ : syracuseStep 3526631 = 5289947) B5289947
theorem B1568751 : Blo 1566981 1568751 := bstep (se 1 (by rfl) ⟨1176563, by rfl⟩ : syracuseStep 1568751 = 2353127) B2353127
theorem B1568763 : Blo 1566981 1568763 := bstep (se 1 (by rfl) ⟨1176572, by rfl⟩ : syracuseStep 1568763 = 2353145) B2353145
theorem B1568831 : Blo 1566981 1568831 := bstep (se 1 (by rfl) ⟨1176623, by rfl⟩ : syracuseStep 1568831 = 2353247) B2353247
theorem B1411797059 : Blo 1566981 1411797059 := bstep (se 1 (by rfl) ⟨1058847794, by rfl⟩ : syracuseStep 1411797059 = 2117695589) B2117695589
theorem B6697039 : Blo 1566981 6697039 := bstep (se 1 (by rfl) ⟨5022779, by rfl⟩ : syracuseStep 6697039 = 10045559) B10045559
theorem B1568871 : Blo 1566981 1568871 := bstep (se 1 (by rfl) ⟨1176653, by rfl⟩ : syracuseStep 1568871 = 2353307) B2353307
theorem B1568895 : Blo 1566981 1568895 := bstep (se 1 (by rfl) ⟨1176671, by rfl⟩ : syracuseStep 1568895 = 2353343) B2353343
theorem B3526811 : Blo 1566981 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B1568923 : Blo 1566981 1568923 := bstep (se 1 (by rfl) ⟨1176692, by rfl⟩ : syracuseStep 1568923 = 2353385) B2353385
theorem B5951663 : Blo 1566981 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B3527009 : Blo 1566981 3527009 := bstep (se 2 (by rfl) ⟨1322628, by rfl⟩ : syracuseStep 3527009 = 2645257) B2645257
theorem B3527099 : Blo 1566981 3527099 := bstep (se 1 (by rfl) ⟨2645324, by rfl⟩ : syracuseStep 3527099 = 5290649) B5290649
theorem B50877173 : Blo 1566981 50877173 := bstep (se 5 (by rfl) ⟨2384867, by rfl⟩ : syracuseStep 50877173 = 4769735) B4769735
theorem B13398929 : Blo 1566981 13398929 := bstep (se 2 (by rfl) ⟨5024598, by rfl⟩ : syracuseStep 13398929 = 10049197) B10049197
theorem B10048481 : Blo 1566981 10048481 := bstep (se 2 (by rfl) ⟨3768180, by rfl⟩ : syracuseStep 10048481 = 7536361) B7536361
theorem B3970073 : Blo 1566981 3970073 := bstep (se 2 (by rfl) ⟨1488777, by rfl⟩ : syracuseStep 3970073 = 2977555) B2977555
theorem B15062111 : Blo 1566981 15062111 := bstep (se 1 (by rfl) ⟨11296583, by rfl⟩ : syracuseStep 15062111 = 22593167) B22593167
theorem B2511967 : Blo 1566981 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B57209975 : Blo 1566981 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B5952635 : Blo 1566981 5952635 := bstep (se 1 (by rfl) ⟨4464476, by rfl⟩ : syracuseStep 5952635 = 8928953) B8928953
theorem B19068043 : Blo 1566981 19068043 := bstep (se 1 (by rfl) ⟨14301032, by rfl⟩ : syracuseStep 19068043 = 28602065) B28602065
theorem B3970255 : Blo 1566981 3970255 := bstep (se 1 (by rfl) ⟨2977691, by rfl⟩ : syracuseStep 3970255 = 5955383) B5955383
theorem B3347819 : Blo 1566981 3347819 := bstep (se 1 (by rfl) ⟨2510864, by rfl⟩ : syracuseStep 3347819 = 5021729) B5021729
theorem B8934785 : Blo 1566981 8934785 := bstep (se 2 (by rfl) ⟨3350544, by rfl⟩ : syracuseStep 8934785 = 6701089) B6701089
theorem B7935407 : Blo 1566981 7935407 := bstep (se 1 (by rfl) ⟨5951555, by rfl⟩ : syracuseStep 7935407 = 11903111) B11903111
theorem B3347887 : Blo 1566981 3347887 := bstep (se 1 (by rfl) ⟨2510915, by rfl⟩ : syracuseStep 3347887 = 5021831) B5021831
theorem B11302553 : Blo 1566981 11302553 := bstep (se 2 (by rfl) ⟨4238457, by rfl⟩ : syracuseStep 11302553 = 8476915) B8476915
theorem B3528359 : Blo 1566981 3528359 := bstep (se 1 (by rfl) ⟨2646269, by rfl⟩ : syracuseStep 3528359 = 5292539) B5292539
theorem B3528539 : Blo 1566981 3528539 := bstep (se 1 (by rfl) ⟨2646404, by rfl⟩ : syracuseStep 3528539 = 5292809) B5292809
theorem B5290055 : Blo 1566981 5290055 := bstep (se 1 (by rfl) ⟨3967541, by rfl⟩ : syracuseStep 5290055 = 7935083) B7935083
theorem B15267917 : Blo 1566981 15267917 := bstep (se 3 (by rfl) ⟨2862734, by rfl⟩ : syracuseStep 15267917 = 5725469) B5725469
theorem B3348793 : Blo 1566981 3348793 := bstep (se 2 (by rfl) ⟨1255797, by rfl⟩ : syracuseStep 3348793 = 2511595) B2511595
theorem B27154763 : Blo 1566981 27154763 := bstep (se 1 (by rfl) ⟨20366072, by rfl⟩ : syracuseStep 27154763 = 40732145) B40732145
theorem B3529043 : Blo 1566981 3529043 := bstep (se 1 (by rfl) ⟨2646782, by rfl⟩ : syracuseStep 3529043 = 5293565) B5293565
theorem B1882783 : Blo 1566981 1882783 := bstep (se 1 (by rfl) ⟨1412087, by rfl⟩ : syracuseStep 1882783 = 2824175) B2824175
theorem B4078313 : Blo 1566981 4078313 := bstep (se 2 (by rfl) ⟨1529367, by rfl⟩ : syracuseStep 4078313 = 3058735) B3058735
theorem B4463417 : Blo 1566981 4463417 := bstep (se 2 (by rfl) ⟨1673781, by rfl⟩ : syracuseStep 4463417 = 3347563) B3347563
theorem B3529529 : Blo 1566981 3529529 := bstep (se 2 (by rfl) ⟨1323573, by rfl⟩ : syracuseStep 3529529 = 2647147) B2647147
theorem B3529583 : Blo 1566981 3529583 := bstep (se 1 (by rfl) ⟨2647187, by rfl⟩ : syracuseStep 3529583 = 5294375) B5294375
theorem B2644859 : Blo 1566981 2644859 := bstep (se 1 (by rfl) ⟨1983644, by rfl⟩ : syracuseStep 2644859 = 3967289) B3967289
theorem B5290919 : Blo 1566981 5290919 := bstep (se 1 (by rfl) ⟨3968189, by rfl⟩ : syracuseStep 5290919 = 7936379) B7936379
theorem B8043553 : Blo 1566981 8043553 := bstep (se 2 (by rfl) ⟨3016332, by rfl⟩ : syracuseStep 8043553 = 6032665) B6032665
theorem B5954897 : Blo 1566981 5954897 := bstep (se 2 (by rfl) ⟨2233086, by rfl⟩ : syracuseStep 5954897 = 4466173) B4466173
theorem B3530159 : Blo 1566981 3530159 := bstep (se 1 (by rfl) ⟨2647619, by rfl⟩ : syracuseStep 3530159 = 5295239) B5295239
theorem B6790729 : Blo 1566981 6790729 := bstep (se 2 (by rfl) ⟨2546523, by rfl⟩ : syracuseStep 6790729 = 5093047) B5093047
theorem B3178091 : Blo 1566981 3178091 := bstep (se 1 (by rfl) ⟨2383568, by rfl⟩ : syracuseStep 3178091 = 4767137) B4767137
theorem B2350811 : Blo 1566981 2350811 := bstep (se 1 (by rfl) ⟨1763108, by rfl⟩ : syracuseStep 2350811 = 3526217) B3526217
theorem B2645723 : Blo 1566981 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B1884071 : Blo 1566981 1884071 := bstep (se 1 (by rfl) ⟨1413053, by rfl⟩ : syracuseStep 1884071 = 2826107) B2826107
theorem B2351081 : Blo 1566981 2351081 := bstep (se 2 (by rfl) ⟨881655, by rfl⟩ : syracuseStep 2351081 = 1763311) B1763311
theorem B2645993 : Blo 1566981 2645993 := bstep (se 2 (by rfl) ⟨992247, by rfl⟩ : syracuseStep 2645993 = 1984495) B1984495
theorem B2351207 : Blo 1566981 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B8929385 : Blo 1566981 8929385 := bstep (se 2 (by rfl) ⟨3348519, by rfl⟩ : syracuseStep 8929385 = 6697039) B6697039
theorem B25419905 : Blo 1566981 25419905 := bstep (se 2 (by rfl) ⟨9532464, by rfl⟩ : syracuseStep 25419905 = 19064929) B19064929
theorem B4767887 : Blo 1566981 4767887 := bstep (se 1 (by rfl) ⟨3575915, by rfl⟩ : syracuseStep 4767887 = 7151831) B7151831
theorem B40714445 : Blo 1566981 40714445 := bstep (se 3 (by rfl) ⟨7633958, by rfl⟩ : syracuseStep 40714445 = 15267917) B15267917
theorem B2351339 : Blo 1566981 2351339 := bstep (se 1 (by rfl) ⟨1763504, by rfl⟩ : syracuseStep 2351339 = 3527009) B3527009
theorem B2351399 : Blo 1566981 2351399 := bstep (se 1 (by rfl) ⟨1763549, by rfl⟩ : syracuseStep 2351399 = 3527099) B3527099
theorem B13394281 : Blo 1566981 13394281 := bstep (se 2 (by rfl) ⟨5022855, by rfl⟩ : syracuseStep 13394281 = 10045711) B10045711
theorem B4465057 : Blo 1566981 4465057 := bstep (se 2 (by rfl) ⟨1674396, by rfl⟩ : syracuseStep 4465057 = 3348793) B3348793
theorem B2646715 : Blo 1566981 2646715 := bstep (se 1 (by rfl) ⟨1985036, by rfl⟩ : syracuseStep 2646715 = 3970073) B3970073
theorem B2351849 : Blo 1566981 2351849 := bstep (se 2 (by rfl) ⟨881943, by rfl⟩ : syracuseStep 2351849 = 1763887) B1763887
theorem B8930159 : Blo 1566981 8930159 := bstep (se 1 (by rfl) ⟨6697619, by rfl⟩ : syracuseStep 8930159 = 13395239) B13395239
theorem B5956523 : Blo 1566981 5956523 := bstep (se 1 (by rfl) ⟨4467392, by rfl⟩ : syracuseStep 5956523 = 8934785) B8934785
theorem B32605199 : Blo 1566981 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B5727341 : Blo 1566981 5727341 := bstep (se 3 (by rfl) ⟨1073876, by rfl⟩ : syracuseStep 5727341 = 2147753) B2147753
theorem B2352239 : Blo 1566981 2352239 := bstep (se 1 (by rfl) ⟨1764179, by rfl⟩ : syracuseStep 2352239 = 3528359) B3528359
theorem B2352359 : Blo 1566981 2352359 := bstep (se 1 (by rfl) ⟨1764269, by rfl⟩ : syracuseStep 2352359 = 3528539) B3528539
theorem B2352425 : Blo 1566981 2352425 := bstep (se 2 (by rfl) ⟨882159, by rfl⟩ : syracuseStep 2352425 = 1764319) B1764319
theorem B1983847 : Blo 1566981 1983847 := bstep (se 1 (by rfl) ⟨1487885, by rfl⟩ : syracuseStep 1983847 = 2975771) B2975771
theorem B10724737 : Blo 1566981 10724737 := bstep (se 2 (by rfl) ⟨4021776, by rfl⟩ : syracuseStep 10724737 = 8043553) B8043553
theorem B2352695 : Blo 1566981 2352695 := bstep (se 1 (by rfl) ⟨1764521, by rfl⟩ : syracuseStep 2352695 = 3529043) B3529043
theorem B5293673 : Blo 1566981 5293673 := bstep (se 2 (by rfl) ⟨1985127, by rfl⟩ : syracuseStep 5293673 = 3970255) B3970255
theorem B2975611 : Blo 1566981 2975611 := bstep (se 1 (by rfl) ⟨2231708, by rfl⟩ : syracuseStep 2975611 = 4463417) B4463417
theorem B2353019 : Blo 1566981 2353019 := bstep (se 1 (by rfl) ⟨1764764, by rfl⟩ : syracuseStep 2353019 = 3529529) B3529529
theorem B2353055 : Blo 1566981 2353055 := bstep (se 1 (by rfl) ⟨1764791, by rfl⟩ : syracuseStep 2353055 = 3529583) B3529583
theorem B1763239 : Blo 1566981 1763239 := bstep (se 1 (by rfl) ⟨1322429, by rfl⟩ : syracuseStep 1763239 = 2644859) B2644859
theorem B9054305 : Blo 1566981 9054305 := bstep (se 2 (by rfl) ⟨3395364, by rfl⟩ : syracuseStep 9054305 = 6790729) B6790729
theorem B2353289 : Blo 1566981 2353289 := bstep (se 2 (by rfl) ⟨882483, by rfl⟩ : syracuseStep 2353289 = 1764967) B1764967
theorem B7538939 : Blo 1566981 7538939 := bstep (se 1 (by rfl) ⟨5654204, by rfl⟩ : syracuseStep 7538939 = 11308409) B11308409
theorem B2353439 : Blo 1566981 2353439 := bstep (se 1 (by rfl) ⟨1765079, by rfl⟩ : syracuseStep 2353439 = 3530159) B3530159
theorem B5024189 : Blo 1566981 5024189 := bstep (se 3 (by rfl) ⟨942035, by rfl⟩ : syracuseStep 5024189 = 1884071) B1884071
theorem B1567207 : Blo 1566981 1567207 := bstep (se 1 (by rfl) ⟨1175405, by rfl⟩ : syracuseStep 1567207 = 2350811) B2350811
theorem B1763815 : Blo 1566981 1763815 := bstep (se 1 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 1763815 = 2645723) B2645723
theorem B13388267 : Blo 1566981 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B11299409 : Blo 1566981 11299409 := bstep (se 2 (by rfl) ⟨4237278, by rfl⟩ : syracuseStep 11299409 = 8474557) B8474557
theorem B1567387 : Blo 1566981 1567387 := bstep (se 1 (by rfl) ⟨1175540, by rfl⟩ : syracuseStep 1567387 = 2351081) B2351081
theorem B1763995 : Blo 1566981 1763995 := bstep (se 1 (by rfl) ⟨1322996, by rfl⟩ : syracuseStep 1763995 = 2645993) B2645993
theorem B941198039 : Blo 1566981 941198039 := bstep (se 1 (by rfl) ⟨705898529, by rfl⟩ : syracuseStep 941198039 = 1411797059) B1411797059
theorem B3967775 : Blo 1566981 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B12889151 : Blo 1566981 12889151 := bstep (se 1 (by rfl) ⟨9666863, by rfl⟩ : syracuseStep 12889151 = 19333727) B19333727
theorem B2231401 : Blo 1566981 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B1567855 : Blo 1566981 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1764463 : Blo 1566981 1764463 := bstep (se 1 (by rfl) ⟨1323347, by rfl⟩ : syracuseStep 1764463 = 2646695) B2646695
theorem B33918115 : Blo 1566981 33918115 := bstep (se 1 (by rfl) ⟨25438586, by rfl⟩ : syracuseStep 33918115 = 50877173) B50877173
theorem B1567935 : Blo 1566981 1567935 := bstep (se 1 (by rfl) ⟨1175951, by rfl⟩ : syracuseStep 1567935 = 2351903) B2351903
theorem B1567951 : Blo 1566981 1567951 := bstep (se 1 (by rfl) ⟨1175963, by rfl⟩ : syracuseStep 1567951 = 2351927) B2351927
theorem B8932619 : Blo 1566981 8932619 := bstep (se 1 (by rfl) ⟨6699464, by rfl⟩ : syracuseStep 8932619 = 13398929) B13398929
theorem B7941401 : Blo 1566981 7941401 := bstep (se 2 (by rfl) ⟨2978025, by rfl⟩ : syracuseStep 7941401 = 5956051) B5956051
theorem B1568071 : Blo 1566981 1568071 := bstep (se 1 (by rfl) ⟨1176053, by rfl⟩ : syracuseStep 1568071 = 2352107) B2352107
theorem B1764679 : Blo 1566981 1764679 := bstep (se 1 (by rfl) ⟨1323509, by rfl⟩ : syracuseStep 1764679 = 2647019) B2647019
theorem B3968423 : Blo 1566981 3968423 := bstep (se 1 (by rfl) ⟨2976317, by rfl⟩ : syracuseStep 3968423 = 5952635) B5952635
theorem B2231879 : Blo 1566981 2231879 := bstep (se 1 (by rfl) ⟨1673909, by rfl⟩ : syracuseStep 2231879 = 3347819) B3347819
theorem B1568799 : Blo 1566981 1568799 := bstep (se 1 (by rfl) ⟨1176599, by rfl⟩ : syracuseStep 1568799 = 2353199) B2353199
theorem B3526703 : Blo 1566981 3526703 := bstep (se 1 (by rfl) ⟨2645027, by rfl⟩ : syracuseStep 3526703 = 5290055) B5290055
theorem B3969121 : Blo 1566981 3969121 := bstep (se 2 (by rfl) ⟨1488420, by rfl⟩ : syracuseStep 3969121 = 2976841) B2976841
theorem B8925329 : Blo 1566981 8925329 := bstep (se 2 (by rfl) ⟨3346998, by rfl⟩ : syracuseStep 8925329 = 6693997) B6693997
theorem B25424057 : Blo 1566981 25424057 := bstep (se 2 (by rfl) ⟨9534021, by rfl⟩ : syracuseStep 25424057 = 19068043) B19068043
theorem B1568975 : Blo 1566981 1568975 := bstep (se 1 (by rfl) ⟨1176731, by rfl⟩ : syracuseStep 1568975 = 2353463) B2353463
theorem B4239593 : Blo 1566981 4239593 := bstep (se 2 (by rfl) ⟨1589847, by rfl⟩ : syracuseStep 4239593 = 3179695) B3179695
theorem B3527279 : Blo 1566981 3527279 := bstep (se 1 (by rfl) ⟨2645459, by rfl⟩ : syracuseStep 3527279 = 5290919) B5290919
theorem B5288759 : Blo 1566981 5288759 := bstep (se 1 (by rfl) ⟨3966569, by rfl⟩ : syracuseStep 5288759 = 7933139) B7933139
theorem B3969931 : Blo 1566981 3969931 := bstep (se 1 (by rfl) ⟨2977448, by rfl⟩ : syracuseStep 3969931 = 5954897) B5954897
theorem B20099987 : Blo 1566981 20099987 := bstep (se 1 (by rfl) ⟨15074990, by rfl⟩ : syracuseStep 20099987 = 30149981) B30149981
theorem B2233337 : Blo 1566981 2233337 := bstep (se 2 (by rfl) ⟨837501, by rfl⟩ : syracuseStep 2233337 = 1675003) B1675003
theorem B2118727 : Blo 1566981 2118727 := bstep (se 1 (by rfl) ⟨1589045, by rfl⟩ : syracuseStep 2118727 = 3178091) B3178091
theorem B6354055 : Blo 1566981 6354055 := bstep (se 1 (by rfl) ⟨4765541, by rfl⟩ : syracuseStep 6354055 = 9531083) B9531083
theorem B3970559 : Blo 1566981 3970559 := bstep (se 1 (by rfl) ⟨2977919, by rfl⟩ : syracuseStep 3970559 = 5955839) B5955839
theorem B3970579 : Blo 1566981 3970579 := bstep (se 1 (by rfl) ⟨2977934, by rfl⟩ : syracuseStep 3970579 = 5955869) B5955869
theorem B2512415 : Blo 1566981 2512415 := bstep (se 1 (by rfl) ⟨1884311, by rfl⟩ : syracuseStep 2512415 = 3768623) B3768623
theorem B3528431 : Blo 1566981 3528431 := bstep (se 1 (by rfl) ⟨2646323, by rfl⟩ : syracuseStep 3528431 = 5292647) B5292647
theorem B4462415 : Blo 1566981 4462415 := bstep (se 1 (by rfl) ⟨3346811, by rfl⟩ : syracuseStep 4462415 = 6693623) B6693623
theorem B6698987 : Blo 1566981 6698987 := bstep (se 1 (by rfl) ⟨5024240, by rfl⟩ : syracuseStep 6698987 = 10048481) B10048481
theorem B10041407 : Blo 1566981 10041407 := bstep (se 1 (by rfl) ⟨7531055, by rfl⟩ : syracuseStep 10041407 = 15062111) B15062111
theorem B38139983 : Blo 1566981 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B5290109 : Blo 1566981 5290109 := bstep (se 3 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 5290109 = 1983791) B1983791
theorem B10041509 : Blo 1566981 10041509 := bstep (se 4 (by rfl) ⟨941391, by rfl⟩ : syracuseStep 10041509 = 1882783) B1882783
theorem B5290271 : Blo 1566981 5290271 := bstep (se 1 (by rfl) ⟨3967703, by rfl⟩ : syracuseStep 5290271 = 7935407) B7935407
theorem B7535035 : Blo 1566981 7535035 := bstep (se 1 (by rfl) ⟨5651276, by rfl⟩ : syracuseStep 7535035 = 11302553) B11302553
theorem B3349289 : Blo 1566981 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B90463067 : Blo 1566981 90463067 := bstep (se 1 (by rfl) ⟨67847300, by rfl⟩ : syracuseStep 90463067 = 135694601) B135694601
theorem B18103175 : Blo 1566981 18103175 := bstep (se 1 (by rfl) ⟨13577381, by rfl⟩ : syracuseStep 18103175 = 27154763) B27154763
theorem B3529835 : Blo 1566981 3529835 := bstep (se 1 (by rfl) ⟨2647376, by rfl⟩ : syracuseStep 3529835 = 5294753) B5294753
theorem B2718875 : Blo 1566981 2718875 := bstep (se 1 (by rfl) ⟨2039156, by rfl⟩ : syracuseStep 2718875 = 4078313) B4078313
theorem B4463849 : Blo 1566981 4463849 := bstep (se 2 (by rfl) ⟨1673943, by rfl⟩ : syracuseStep 4463849 = 3347887) B3347887
theorem B3529979 : Blo 1566981 3529979 := bstep (se 1 (by rfl) ⟨2647484, by rfl⟩ : syracuseStep 3529979 = 5294969) B5294969
theorem B3530105 : Blo 1566981 3530105 := bstep (se 2 (by rfl) ⟨1323789, by rfl⟩ : syracuseStep 3530105 = 2647579) B2647579
theorem B8478145 : Blo 1566981 8478145 := bstep (se 2 (by rfl) ⟨3179304, by rfl⟩ : syracuseStep 8478145 = 6358609) B6358609
theorem B2580191 : Blo 1566981 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B2351015 : Blo 1566981 2351015 := bstep (se 1 (by rfl) ⟨1763261, by rfl⟩ : syracuseStep 2351015 = 3526523) B3526523
theorem B7937999 : Blo 1566981 7937999 := bstep (se 1 (by rfl) ⟨5953499, by rfl⟩ : syracuseStep 7937999 = 11906999) B11906999
theorem B2351087 : Blo 1566981 2351087 := bstep (se 1 (by rfl) ⟨1763315, by rfl⟩ : syracuseStep 2351087 = 3526631) B3526631
theorem B2351135 : Blo 1566981 2351135 := bstep (se 1 (by rfl) ⟨1763351, by rfl⟩ : syracuseStep 2351135 = 3526703) B3526703
theorem B3178591 : Blo 1566981 3178591 := bstep (se 1 (by rfl) ⟨2383943, by rfl⟩ : syracuseStep 3178591 = 4767887) B4767887
theorem B16949371 : Blo 1566981 16949371 := bstep (se 1 (by rfl) ⟨12712028, by rfl⟩ : syracuseStep 16949371 = 25424057) B25424057
theorem B5292161 : Blo 1566981 5292161 := bstep (se 2 (by rfl) ⟨1984560, by rfl⟩ : syracuseStep 5292161 = 3969121) B3969121
theorem B2826395 : Blo 1566981 2826395 := bstep (se 1 (by rfl) ⟨2119796, by rfl⟩ : syracuseStep 2826395 = 4239593) B4239593
theorem B2351519 : Blo 1566981 2351519 := bstep (se 1 (by rfl) ⟨1763639, by rfl⟩ : syracuseStep 2351519 = 3527279) B3527279
theorem B17859041 : Blo 1566981 17859041 := bstep (se 2 (by rfl) ⟨6697140, by rfl⟩ : syracuseStep 17859041 = 13394281) B13394281
theorem B11903597 : Blo 1566981 11903597 := bstep (se 3 (by rfl) ⟨2231924, by rfl⟩ : syracuseStep 11903597 = 4463849) B4463849
theorem B2351753 : Blo 1566981 2351753 := bstep (se 2 (by rfl) ⟨881907, by rfl⟩ : syracuseStep 2351753 = 1763815) B1763815
theorem B3818227 : Blo 1566981 3818227 := bstep (se 1 (by rfl) ⟨2863670, by rfl⟩ : syracuseStep 3818227 = 5727341) B5727341
theorem B2351993 : Blo 1566981 2351993 := bstep (se 2 (by rfl) ⟨881997, by rfl⟩ : syracuseStep 2351993 = 1763995) B1763995
theorem B2647039 : Blo 1566981 2647039 := bstep (se 1 (by rfl) ⟨1985279, by rfl⟩ : syracuseStep 2647039 = 3970559) B3970559
theorem B2352287 : Blo 1566981 2352287 := bstep (se 1 (by rfl) ⟨1764215, by rfl⟩ : syracuseStep 2352287 = 3528431) B3528431
theorem B5293241 : Blo 1566981 5293241 := bstep (se 2 (by rfl) ⟨1984965, by rfl⟩ : syracuseStep 5293241 = 3969931) B3969931
theorem B2974943 : Blo 1566981 2974943 := bstep (se 1 (by rfl) ⟨2231207, by rfl⟩ : syracuseStep 2974943 = 4462415) B4462415
theorem B4465991 : Blo 1566981 4465991 := bstep (se 1 (by rfl) ⟨3349493, by rfl⟩ : syracuseStep 4465991 = 6698987) B6698987
theorem B6694271 : Blo 1566981 6694271 := bstep (se 1 (by rfl) ⟨5020703, by rfl⟩ : syracuseStep 6694271 = 10041407) B10041407
theorem B6694339 : Blo 1566981 6694339 := bstep (se 1 (by rfl) ⟨5020754, by rfl⟩ : syracuseStep 6694339 = 10041509) B10041509
theorem B2975201 : Blo 1566981 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B2352617 : Blo 1566981 2352617 := bstep (se 2 (by rfl) ⟨882231, by rfl⟩ : syracuseStep 2352617 = 1764463) B1764463
theorem B8472073 : Blo 1566981 8472073 := bstep (se 2 (by rfl) ⟨3177027, by rfl⟩ : syracuseStep 8472073 = 6354055) B6354055
theorem B2352905 : Blo 1566981 2352905 := bstep (se 2 (by rfl) ⟨882339, by rfl⟩ : syracuseStep 2352905 = 1764679) B1764679
theorem B12068783 : Blo 1566981 12068783 := bstep (se 1 (by rfl) ⟨9051587, by rfl⟩ : syracuseStep 12068783 = 18103175) B18103175
theorem B5294105 : Blo 1566981 5294105 := bstep (se 2 (by rfl) ⟨1985289, by rfl⟩ : syracuseStep 5294105 = 3970579) B3970579
theorem B2353223 : Blo 1566981 2353223 := bstep (se 1 (by rfl) ⟨1764917, by rfl⟩ : syracuseStep 2353223 = 3529835) B3529835
theorem B1812583 : Blo 1566981 1812583 := bstep (se 1 (by rfl) ⟨1359437, by rfl⟩ : syracuseStep 1812583 = 2718875) B2718875
theorem B2353319 : Blo 1566981 2353319 := bstep (se 1 (by rfl) ⟨1764989, by rfl⟩ : syracuseStep 2353319 = 3529979) B3529979
theorem B5294267 : Blo 1566981 5294267 := bstep (se 1 (by rfl) ⟨3970700, by rfl⟩ : syracuseStep 5294267 = 7941401) B7941401
theorem B2353403 : Blo 1566981 2353403 := bstep (se 1 (by rfl) ⟨1765052, by rfl⟩ : syracuseStep 2353403 = 3530105) B3530105
theorem B3967481 : Blo 1566981 3967481 := bstep (se 2 (by rfl) ⟨1487805, by rfl⟩ : syracuseStep 3967481 = 2975611) B2975611
theorem B1567343 : Blo 1566981 1567343 := bstep (se 1 (by rfl) ⟨1175507, by rfl⟩ : syracuseStep 1567343 = 2351015) B2351015
theorem B1567391 : Blo 1566981 1567391 := bstep (se 1 (by rfl) ⟨1175543, by rfl⟩ : syracuseStep 1567391 = 2351087) B2351087
theorem B1567471 : Blo 1566981 1567471 := bstep (se 1 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 1567471 = 2351207) B2351207
theorem B5950219 : Blo 1566981 5950219 := bstep (se 1 (by rfl) ⟨4462664, by rfl⟩ : syracuseStep 5950219 = 8925329) B8925329
theorem B1567559 : Blo 1566981 1567559 := bstep (se 1 (by rfl) ⟨1175669, by rfl⟩ : syracuseStep 1567559 = 2351339) B2351339
theorem B1567599 : Blo 1566981 1567599 := bstep (se 1 (by rfl) ⟨1175699, by rfl⟩ : syracuseStep 1567599 = 2351399) B2351399
theorem B1567899 : Blo 1566981 1567899 := bstep (se 1 (by rfl) ⟨1175924, by rfl⟩ : syracuseStep 1567899 = 2351849) B2351849
theorem B108571853 : Blo 1566981 108571853 := bstep (se 3 (by rfl) ⟨20357222, by rfl⟩ : syracuseStep 108571853 = 40714445) B40714445
theorem B3525839 : Blo 1566981 3525839 := bstep (se 1 (by rfl) ⟨2644379, by rfl⟩ : syracuseStep 3525839 = 5288759) B5288759
theorem B10046713 : Blo 1566981 10046713 := bstep (se 2 (by rfl) ⟨3767517, by rfl⟩ : syracuseStep 10046713 = 7535035) B7535035
theorem B21736799 : Blo 1566981 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B1568159 : Blo 1566981 1568159 := bstep (se 1 (by rfl) ⟨1176119, by rfl⟩ : syracuseStep 1568159 = 2352239) B2352239
theorem B1568239 : Blo 1566981 1568239 := bstep (se 1 (by rfl) ⟨1176179, by rfl⟩ : syracuseStep 1568239 = 2352359) B2352359
theorem B1568283 : Blo 1566981 1568283 := bstep (se 1 (by rfl) ⟨1176212, by rfl⟩ : syracuseStep 1568283 = 2352425) B2352425
theorem B96579253 : Blo 1566981 96579253 := bstep (se 5 (by rfl) ⟨4527152, by rfl⟩ : syracuseStep 96579253 = 9054305) B9054305
theorem B1568463 : Blo 1566981 1568463 := bstep (se 1 (by rfl) ⟨1176347, by rfl⟩ : syracuseStep 1568463 = 2352695) B2352695
theorem B1568679 : Blo 1566981 1568679 := bstep (se 1 (by rfl) ⟨1176509, by rfl⟩ : syracuseStep 1568679 = 2353019) B2353019
theorem B1568703 : Blo 1566981 1568703 := bstep (se 1 (by rfl) ⟨1176527, by rfl⟩ : syracuseStep 1568703 = 2353055) B2353055
theorem B3526739 : Blo 1566981 3526739 := bstep (se 1 (by rfl) ⟨2645054, by rfl⟩ : syracuseStep 3526739 = 5290109) B5290109
theorem B1568859 : Blo 1566981 1568859 := bstep (se 1 (by rfl) ⟨1176644, by rfl⟩ : syracuseStep 1568859 = 2353289) B2353289
theorem B5025959 : Blo 1566981 5025959 := bstep (se 1 (by rfl) ⟨3769469, by rfl⟩ : syracuseStep 5025959 = 7538939) B7538939
theorem B5951677 : Blo 1566981 5951677 := bstep (se 3 (by rfl) ⟨1115939, by rfl⟩ : syracuseStep 5951677 = 2231879) B2231879
theorem B3526847 : Blo 1566981 3526847 := bstep (se 1 (by rfl) ⟨2645135, by rfl⟩ : syracuseStep 3526847 = 5290271) B5290271
theorem B1568959 : Blo 1566981 1568959 := bstep (se 1 (by rfl) ⟨1176719, by rfl⟩ : syracuseStep 1568959 = 2353439) B2353439
theorem B45224153 : Blo 1566981 45224153 := bstep (se 2 (by rfl) ⟨16959057, by rfl⟩ : syracuseStep 45224153 = 33918115) B33918115
theorem B8925511 : Blo 1566981 8925511 := bstep (se 1 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 8925511 = 13388267) B13388267
theorem B7532939 : Blo 1566981 7532939 := bstep (se 1 (by rfl) ⟨5649704, by rfl⟩ : syracuseStep 7532939 = 11299409) B11299409
theorem B14299649 : Blo 1566981 14299649 := bstep (se 2 (by rfl) ⟨5362368, by rfl⟩ : syracuseStep 14299649 = 10724737) B10724737
theorem B2232859 : Blo 1566981 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B5952923 : Blo 1566981 5952923 := bstep (se 1 (by rfl) ⟨4464692, by rfl⟩ : syracuseStep 5952923 = 8929385) B8929385
theorem B16946603 : Blo 1566981 16946603 := bstep (se 1 (by rfl) ⟨12709952, by rfl⟩ : syracuseStep 16946603 = 25419905) B25419905
theorem B5953409 : Blo 1566981 5953409 := bstep (se 2 (by rfl) ⟨2232528, by rfl⟩ : syracuseStep 5953409 = 4465057) B4465057
theorem B5953439 : Blo 1566981 5953439 := bstep (se 1 (by rfl) ⟨4465079, by rfl⟩ : syracuseStep 5953439 = 8930159) B8930159
theorem B13399991 : Blo 1566981 13399991 := bstep (se 1 (by rfl) ⟨10049993, by rfl⟩ : syracuseStep 13399991 = 20099987) B20099987
theorem B3971015 : Blo 1566981 3971015 := bstep (se 1 (by rfl) ⟨2978261, by rfl⟩ : syracuseStep 3971015 = 5956523) B5956523
theorem B3528953 : Blo 1566981 3528953 := bstep (se 2 (by rfl) ⟨1323357, by rfl⟩ : syracuseStep 3528953 = 2646715) B2646715
theorem B3529115 : Blo 1566981 3529115 := bstep (se 1 (by rfl) ⟨2646836, by rfl⟩ : syracuseStep 3529115 = 5293673) B5293673
theorem B25426655 : Blo 1566981 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B6699773 : Blo 1566981 6699773 := bstep (se 3 (by rfl) ⟨1256207, by rfl⟩ : syracuseStep 6699773 = 2512415) B2512415
theorem B2824969 : Blo 1566981 2824969 := bstep (se 2 (by rfl) ⟨1059363, by rfl⟩ : syracuseStep 2824969 = 2118727) B2118727
theorem B3349459 : Blo 1566981 3349459 := bstep (se 1 (by rfl) ⟨2512094, by rfl⟩ : syracuseStep 3349459 = 5024189) B5024189
theorem B2645129 : Blo 1566981 2645129 := bstep (se 2 (by rfl) ⟨991923, by rfl⟩ : syracuseStep 2645129 = 1983847) B1983847
theorem B627465359 : Blo 1566981 627465359 := bstep (se 1 (by rfl) ⟨470599019, by rfl⟩ : syracuseStep 627465359 = 941198039) B941198039
theorem B2645183 : Blo 1566981 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B60308711 : Blo 1566981 60308711 := bstep (se 1 (by rfl) ⟨45231533, by rfl⟩ : syracuseStep 60308711 = 90463067) B90463067
theorem B11304193 : Blo 1566981 11304193 := bstep (se 2 (by rfl) ⟨4239072, by rfl⟩ : syracuseStep 11304193 = 8478145) B8478145
theorem B8592767 : Blo 1566981 8592767 := bstep (se 1 (by rfl) ⟨6444575, by rfl⟩ : syracuseStep 8592767 = 12889151) B12889151
theorem B5955079 : Blo 1566981 5955079 := bstep (se 1 (by rfl) ⟨4466309, by rfl⟩ : syracuseStep 5955079 = 8932619) B8932619
theorem B2645615 : Blo 1566981 2645615 := bstep (se 1 (by rfl) ⟨1984211, by rfl⟩ : syracuseStep 2645615 = 3968423) B3968423
theorem B1720127 : Blo 1566981 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B2350985 : Blo 1566981 2350985 := bstep (se 2 (by rfl) ⟨881619, by rfl⟩ : syracuseStep 2350985 = 1763239) B1763239
theorem B5291999 : Blo 1566981 5291999 := bstep (se 1 (by rfl) ⟨3968999, by rfl⟩ : syracuseStep 5291999 = 7937999) B7937999
theorem B5955565 : Blo 1566981 5955565 := bstep (se 3 (by rfl) ⟨1116668, by rfl⟩ : syracuseStep 5955565 = 2233337) B2233337
theorem B2351159 : Blo 1566981 2351159 := bstep (se 1 (by rfl) ⟨1763369, by rfl⟩ : syracuseStep 2351159 = 3526739) B3526739
theorem B1884263 : Blo 1566981 1884263 := bstep (se 1 (by rfl) ⟨1413197, by rfl⟩ : syracuseStep 1884263 = 2826395) B2826395
theorem B3350639 : Blo 1566981 3350639 := bstep (se 1 (by rfl) ⟨2512979, by rfl⟩ : syracuseStep 3350639 = 5025959) B5025959
theorem B2351231 : Blo 1566981 2351231 := bstep (se 1 (by rfl) ⟨1763423, by rfl⟩ : syracuseStep 2351231 = 3526847) B3526847
theorem B9667109 : Blo 1566981 9667109 := bstep (se 4 (by rfl) ⟨906291, by rfl⟩ : syracuseStep 9667109 = 1812583) B1812583
theorem B1983295 : Blo 1566981 1983295 := bstep (se 1 (by rfl) ⟨1487471, by rfl⟩ : syracuseStep 1983295 = 2974943) B2974943
theorem B11297735 : Blo 1566981 11297735 := bstep (se 1 (by rfl) ⟨8473301, by rfl⟩ : syracuseStep 11297735 = 16946603) B16946603
theorem B1983467 : Blo 1566981 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B20087837 : Blo 1566981 20087837 := bstep (se 3 (by rfl) ⟨3766469, by rfl⟩ : syracuseStep 20087837 = 7532939) B7532939
theorem B4465945 : Blo 1566981 4465945 := bstep (se 2 (by rfl) ⟨1674729, by rfl⟩ : syracuseStep 4465945 = 3349459) B3349459
theorem B8045855 : Blo 1566981 8045855 := bstep (se 1 (by rfl) ⟨6034391, by rfl⟩ : syracuseStep 8045855 = 12068783) B12068783
theorem B2647343 : Blo 1566981 2647343 := bstep (se 1 (by rfl) ⟨1985507, by rfl⟩ : syracuseStep 2647343 = 3971015) B3971015
theorem B2352635 : Blo 1566981 2352635 := bstep (se 1 (by rfl) ⟨1764476, by rfl⟩ : syracuseStep 2352635 = 3528953) B3528953
theorem B2352743 : Blo 1566981 2352743 := bstep (se 1 (by rfl) ⟨1764557, by rfl⟩ : syracuseStep 2352743 = 3529115) B3529115
theorem B13395617 : Blo 1566981 13395617 := bstep (se 2 (by rfl) ⟨5023356, by rfl⟩ : syracuseStep 13395617 = 10046713) B10046713
theorem B16951103 : Blo 1566981 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B4466515 : Blo 1566981 4466515 := bstep (se 1 (by rfl) ⟨3349886, by rfl⟩ : syracuseStep 4466515 = 6699773) B6699773
theorem B7940105 : Blo 1566981 7940105 := bstep (se 2 (by rfl) ⟨2977539, by rfl⟩ : syracuseStep 7940105 = 5955079) B5955079
theorem B1763419 : Blo 1566981 1763419 := bstep (se 1 (by rfl) ⟨1322564, by rfl⟩ : syracuseStep 1763419 = 2645129) B2645129
theorem B418310239 : Blo 1566981 418310239 := bstep (se 1 (by rfl) ⟨313732679, by rfl⟩ : syracuseStep 418310239 = 627465359) B627465359
theorem B1763455 : Blo 1566981 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B128772337 : Blo 1566981 128772337 := bstep (se 2 (by rfl) ⟨48289626, by rfl⟩ : syracuseStep 128772337 = 96579253) B96579253
theorem B5728511 : Blo 1566981 5728511 := bstep (se 1 (by rfl) ⟨4296383, by rfl⟩ : syracuseStep 5728511 = 8592767) B8592767
theorem B1763743 : Blo 1566981 1763743 := bstep (se 1 (by rfl) ⟨1322807, by rfl⟩ : syracuseStep 1763743 = 2645615) B2645615
theorem B1567323 : Blo 1566981 1567323 := bstep (se 1 (by rfl) ⟨1175492, by rfl⟩ : syracuseStep 1567323 = 2350985) B2350985
theorem B7940753 : Blo 1566981 7940753 := bstep (se 2 (by rfl) ⟨2977782, by rfl⟩ : syracuseStep 7940753 = 5955565) B5955565
theorem B1567423 : Blo 1566981 1567423 := bstep (se 1 (by rfl) ⟨1175567, by rfl⟩ : syracuseStep 1567423 = 2351135) B2351135
theorem B30149435 : Blo 1566981 30149435 := bstep (se 1 (by rfl) ⟨22612076, by rfl⟩ : syracuseStep 30149435 = 45224153) B45224153
theorem B1567679 : Blo 1566981 1567679 := bstep (se 1 (by rfl) ⟨1175759, by rfl⟩ : syracuseStep 1567679 = 2351519) B2351519
theorem B11906027 : Blo 1566981 11906027 := bstep (se 1 (by rfl) ⟨8929520, by rfl⟩ : syracuseStep 11906027 = 17859041) B17859041
theorem B1567835 : Blo 1566981 1567835 := bstep (se 1 (by rfl) ⟨1175876, by rfl⟩ : syracuseStep 1567835 = 2351753) B2351753
theorem B16952485 : Blo 1566981 16952485 := bstep (se 4 (by rfl) ⟨1589295, by rfl⟩ : syracuseStep 16952485 = 3178591) B3178591
theorem B1567995 : Blo 1566981 1567995 := bstep (se 1 (by rfl) ⟨1175996, by rfl⟩ : syracuseStep 1567995 = 2351993) B2351993
theorem B2977145 : Blo 1566981 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B1568191 : Blo 1566981 1568191 := bstep (se 1 (by rfl) ⟨1176143, by rfl⟩ : syracuseStep 1568191 = 2352287) B2352287
theorem B2977327 : Blo 1566981 2977327 := bstep (se 1 (by rfl) ⟨2232995, by rfl⟩ : syracuseStep 2977327 = 4465991) B4465991
theorem B3968615 : Blo 1566981 3968615 := bstep (se 1 (by rfl) ⟨2976461, by rfl⟩ : syracuseStep 3968615 = 5952923) B5952923
theorem B5090969 : Blo 1566981 5090969 := bstep (se 2 (by rfl) ⟨1909113, by rfl⟩ : syracuseStep 5090969 = 3818227) B3818227
theorem B1568411 : Blo 1566981 1568411 := bstep (se 1 (by rfl) ⟨1176308, by rfl⟩ : syracuseStep 1568411 = 2352617) B2352617
theorem B7933625 : Blo 1566981 7933625 := bstep (se 2 (by rfl) ⟨2975109, by rfl⟩ : syracuseStep 7933625 = 5950219) B5950219
theorem B1568603 : Blo 1566981 1568603 := bstep (se 1 (by rfl) ⟨1176452, by rfl⟩ : syracuseStep 1568603 = 2352905) B2352905
theorem B3968939 : Blo 1566981 3968939 := bstep (se 1 (by rfl) ⟨2976704, by rfl⟩ : syracuseStep 3968939 = 5953409) B5953409
theorem B3968959 : Blo 1566981 3968959 := bstep (se 1 (by rfl) ⟨2976719, by rfl⟩ : syracuseStep 3968959 = 5953439) B5953439
theorem B8933327 : Blo 1566981 8933327 := bstep (se 1 (by rfl) ⟨6699995, by rfl⟩ : syracuseStep 8933327 = 13399991) B13399991
theorem B1568815 : Blo 1566981 1568815 := bstep (se 1 (by rfl) ⟨1176611, by rfl⟩ : syracuseStep 1568815 = 2353223) B2353223
theorem B1568879 : Blo 1566981 1568879 := bstep (se 1 (by rfl) ⟨1176659, by rfl⟩ : syracuseStep 1568879 = 2353319) B2353319
theorem B1568935 : Blo 1566981 1568935 := bstep (se 1 (by rfl) ⟨1176701, by rfl⟩ : syracuseStep 1568935 = 2353403) B2353403
theorem B8925785 : Blo 1566981 8925785 := bstep (se 2 (by rfl) ⟨3347169, by rfl⟩ : syracuseStep 8925785 = 6694339) B6694339
theorem B72381235 : Blo 1566981 72381235 := bstep (se 1 (by rfl) ⟨54285926, by rfl⟩ : syracuseStep 72381235 = 108571853) B108571853
theorem B3527999 : Blo 1566981 3527999 := bstep (se 1 (by rfl) ⟨2645999, by rfl⟩ : syracuseStep 3527999 = 5291999) B5291999
theorem B3528107 : Blo 1566981 3528107 := bstep (se 1 (by rfl) ⟨2646080, by rfl⟩ : syracuseStep 3528107 = 5292161) B5292161
theorem B22599161 : Blo 1566981 22599161 := bstep (se 2 (by rfl) ⟨8474685, by rfl⟩ : syracuseStep 22599161 = 16949371) B16949371
theorem B7935569 : Blo 1566981 7935569 := bstep (se 2 (by rfl) ⟨2975838, by rfl⟩ : syracuseStep 7935569 = 5951677) B5951677
theorem B9533099 : Blo 1566981 9533099 := bstep (se 1 (by rfl) ⟨7149824, by rfl⟩ : syracuseStep 9533099 = 14299649) B14299649
theorem B7935731 : Blo 1566981 7935731 := bstep (se 1 (by rfl) ⟨5951798, by rfl⟩ : syracuseStep 7935731 = 11903597) B11903597
theorem B11900681 : Blo 1566981 11900681 := bstep (se 2 (by rfl) ⟨4462755, by rfl⟩ : syracuseStep 11900681 = 8925511) B8925511
theorem B3528827 : Blo 1566981 3528827 := bstep (se 1 (by rfl) ⟨2646620, by rfl⟩ : syracuseStep 3528827 = 5293241) B5293241
theorem B4462847 : Blo 1566981 4462847 := bstep (se 1 (by rfl) ⟨3347135, by rfl⟩ : syracuseStep 4462847 = 6694271) B6694271
theorem B3766625 : Blo 1566981 3766625 := bstep (se 2 (by rfl) ⟨1412484, by rfl⟩ : syracuseStep 3766625 = 2824969) B2824969
theorem B3529385 : Blo 1566981 3529385 := bstep (se 2 (by rfl) ⟨1323519, by rfl⟩ : syracuseStep 3529385 = 2647039) B2647039
theorem B3529403 : Blo 1566981 3529403 := bstep (se 1 (by rfl) ⟨2647052, by rfl⟩ : syracuseStep 3529403 = 5294105) B5294105
theorem B3529511 : Blo 1566981 3529511 := bstep (se 1 (by rfl) ⟨2647133, by rfl⟩ : syracuseStep 3529511 = 5294267) B5294267
theorem B2644987 : Blo 1566981 2644987 := bstep (se 1 (by rfl) ⟨1983740, by rfl⟩ : syracuseStep 2644987 = 3967481) B3967481
theorem B15072257 : Blo 1566981 15072257 := bstep (se 2 (by rfl) ⟨5652096, by rfl⟩ : syracuseStep 15072257 = 11304193) B11304193
theorem B11296097 : Blo 1566981 11296097 := bstep (se 2 (by rfl) ⟨4236036, by rfl⟩ : syracuseStep 11296097 = 8472073) B8472073
theorem B2350559 : Blo 1566981 2350559 := bstep (se 1 (by rfl) ⟨1762919, by rfl⟩ : syracuseStep 2350559 = 3525839) B3525839
theorem B40205807 : Blo 1566981 40205807 := bstep (se 1 (by rfl) ⟨30154355, by rfl⟩ : syracuseStep 40205807 = 60308711) B60308711
theorem B4587005 : Blo 1566981 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B14491199 : Blo 1566981 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B2351225 : Blo 1566981 2351225 := bstep (se 2 (by rfl) ⟨881709, by rfl⟩ : syracuseStep 2351225 = 1763419) B1763419
theorem B2351273 : Blo 1566981 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B171696449 : Blo 1566981 171696449 := bstep (se 2 (by rfl) ⟨64386168, by rfl⟩ : syracuseStep 171696449 = 128772337) B128772337
theorem B2351657 : Blo 1566981 2351657 := bstep (se 2 (by rfl) ⟨881871, by rfl⟩ : syracuseStep 2351657 = 1763743) B1763743
theorem B2351999 : Blo 1566981 2351999 := bstep (se 1 (by rfl) ⟨1763999, by rfl⟩ : syracuseStep 2351999 = 3527999) B3527999
theorem B2352071 : Blo 1566981 2352071 := bstep (se 1 (by rfl) ⟨1764053, by rfl⟩ : syracuseStep 2352071 = 3528107) B3528107
theorem B15066107 : Blo 1566981 15066107 := bstep (se 1 (by rfl) ⟨11299580, by rfl⟩ : syracuseStep 15066107 = 22599161) B22599161
theorem B8930411 : Blo 1566981 8930411 := bstep (se 1 (by rfl) ⟨6697808, by rfl⟩ : syracuseStep 8930411 = 13395617) B13395617
theorem B5293403 : Blo 1566981 5293403 := bstep (se 1 (by rfl) ⟨3970052, by rfl⟩ : syracuseStep 5293403 = 7940105) B7940105
theorem B2352551 : Blo 1566981 2352551 := bstep (se 1 (by rfl) ⟨1764413, by rfl⟩ : syracuseStep 2352551 = 3528827) B3528827
theorem B2975231 : Blo 1566981 2975231 := bstep (se 1 (by rfl) ⟨2231423, by rfl⟩ : syracuseStep 2975231 = 4462847) B4462847
theorem B3819007 : Blo 1566981 3819007 := bstep (se 1 (by rfl) ⟨2864255, by rfl⟩ : syracuseStep 3819007 = 5728511) B5728511
theorem B22603313 : Blo 1566981 22603313 := bstep (se 2 (by rfl) ⟨8476242, by rfl⟩ : syracuseStep 22603313 = 16952485) B16952485
theorem B13575917 : Blo 1566981 13575917 := bstep (se 3 (by rfl) ⟨2545484, by rfl⟩ : syracuseStep 13575917 = 5090969) B5090969
theorem B5293835 : Blo 1566981 5293835 := bstep (se 1 (by rfl) ⟨3970376, by rfl⟩ : syracuseStep 5293835 = 7940753) B7940753
theorem B2352923 : Blo 1566981 2352923 := bstep (se 1 (by rfl) ⟨1764692, by rfl⟩ : syracuseStep 2352923 = 3529385) B3529385
theorem B25421597 : Blo 1566981 25421597 := bstep (se 3 (by rfl) ⟨4766549, by rfl⟩ : syracuseStep 25421597 = 9533099) B9533099
theorem B2352935 : Blo 1566981 2352935 := bstep (se 1 (by rfl) ⟨1764701, by rfl⟩ : syracuseStep 2352935 = 3529403) B3529403
theorem B2353007 : Blo 1566981 2353007 := bstep (se 1 (by rfl) ⟨1764755, by rfl⟩ : syracuseStep 2353007 = 3529511) B3529511
theorem B7530731 : Blo 1566981 7530731 := bstep (se 1 (by rfl) ⟨5648048, by rfl⟩ : syracuseStep 7530731 = 11296097) B11296097
theorem B1984763 : Blo 1566981 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B1567039 : Blo 1566981 1567039 := bstep (se 1 (by rfl) ⟨1175279, by rfl⟩ : syracuseStep 1567039 = 2350559) B2350559
theorem B3058003 : Blo 1566981 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B9660799 : Blo 1566981 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B40192685 : Blo 1566981 40192685 := bstep (se 3 (by rfl) ⟨7536128, by rfl⟩ : syracuseStep 40192685 = 15072257) B15072257
theorem B1567439 : Blo 1566981 1567439 := bstep (se 1 (by rfl) ⟨1175579, by rfl⟩ : syracuseStep 1567439 = 2351159) B2351159
theorem B1567487 : Blo 1566981 1567487 := bstep (se 1 (by rfl) ⟨1175615, by rfl⟩ : syracuseStep 1567487 = 2351231) B2351231
theorem B557746985 : Blo 1566981 557746985 := bstep (se 2 (by rfl) ⟨209155119, by rfl⟩ : syracuseStep 557746985 = 418310239) B418310239
theorem B5024701 : Blo 1566981 5024701 := bstep (se 3 (by rfl) ⟨942131, by rfl⟩ : syracuseStep 5024701 = 1884263) B1884263
theorem B5950523 : Blo 1566981 5950523 := bstep (se 1 (by rfl) ⟨4462892, by rfl⟩ : syracuseStep 5950523 = 8925785) B8925785
theorem B7531823 : Blo 1566981 7531823 := bstep (se 1 (by rfl) ⟨5648867, by rfl⟩ : syracuseStep 7531823 = 11297735) B11297735
theorem B1764895 : Blo 1566981 1764895 := bstep (se 1 (by rfl) ⟨1323671, by rfl⟩ : syracuseStep 1764895 = 2647343) B2647343
theorem B1568423 : Blo 1566981 1568423 := bstep (se 1 (by rfl) ⟨1176317, by rfl⟩ : syracuseStep 1568423 = 2352635) B2352635
theorem B1568495 : Blo 1566981 1568495 := bstep (se 1 (by rfl) ⟨1176371, by rfl⟩ : syracuseStep 1568495 = 2352743) B2352743
theorem B7933787 : Blo 1566981 7933787 := bstep (se 1 (by rfl) ⟨5950340, by rfl⟩ : syracuseStep 7933787 = 11900681) B11900681
theorem B11300735 : Blo 1566981 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B3526649 : Blo 1566981 3526649 := bstep (se 2 (by rfl) ⟨1322493, by rfl⟩ : syracuseStep 3526649 = 2644987) B2644987
theorem B2511083 : Blo 1566981 2511083 := bstep (se 1 (by rfl) ⟨1883312, by rfl⟩ : syracuseStep 2511083 = 3766625) B3766625
theorem B20099623 : Blo 1566981 20099623 := bstep (se 1 (by rfl) ⟨15074717, by rfl⟩ : syracuseStep 20099623 = 30149435) B30149435
theorem B3969769 : Blo 1566981 3969769 := bstep (se 2 (by rfl) ⟨1488663, by rfl⟩ : syracuseStep 3969769 = 2977327) B2977327
theorem B5289083 : Blo 1566981 5289083 := bstep (se 1 (by rfl) ⟨3966812, by rfl⟩ : syracuseStep 5289083 = 7933625) B7933625
theorem B5289245 : Blo 1566981 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B2233759 : Blo 1566981 2233759 := bstep (se 1 (by rfl) ⟨1675319, by rfl⟩ : syracuseStep 2233759 = 3350639) B3350639
theorem B6444739 : Blo 1566981 6444739 := bstep (se 1 (by rfl) ⟨4833554, by rfl⟩ : syracuseStep 6444739 = 9667109) B9667109
theorem B13391891 : Blo 1566981 13391891 := bstep (se 1 (by rfl) ⟨10043918, by rfl⟩ : syracuseStep 13391891 = 20087837) B20087837
theorem B5363903 : Blo 1566981 5363903 := bstep (se 1 (by rfl) ⟨4022927, by rfl⟩ : syracuseStep 5363903 = 8045855) B8045855
theorem B5290379 : Blo 1566981 5290379 := bstep (se 1 (by rfl) ⟨3967784, by rfl⟩ : syracuseStep 5290379 = 7935569) B7935569
theorem B96508313 : Blo 1566981 96508313 := bstep (se 2 (by rfl) ⟨36190617, by rfl⟩ : syracuseStep 96508313 = 72381235) B72381235
theorem B2644393 : Blo 1566981 2644393 := bstep (se 2 (by rfl) ⟨991647, by rfl⟩ : syracuseStep 2644393 = 1983295) B1983295
theorem B5290487 : Blo 1566981 5290487 := bstep (se 1 (by rfl) ⟨3967865, by rfl⟩ : syracuseStep 5290487 = 7935731) B7935731
theorem B5954593 : Blo 1566981 5954593 := bstep (se 2 (by rfl) ⟨2232972, by rfl⟩ : syracuseStep 5954593 = 4465945) B4465945
theorem B7937351 : Blo 1566981 7937351 := bstep (se 1 (by rfl) ⟨5953013, by rfl⟩ : syracuseStep 7937351 = 11906027) B11906027
theorem B26803871 : Blo 1566981 26803871 := bstep (se 1 (by rfl) ⟨20102903, by rfl⟩ : syracuseStep 26803871 = 40205807) B40205807
theorem B2645743 : Blo 1566981 2645743 := bstep (se 1 (by rfl) ⟨1984307, by rfl⟩ : syracuseStep 2645743 = 3968615) B3968615
theorem B5955353 : Blo 1566981 5955353 := bstep (se 2 (by rfl) ⟨2233257, by rfl⟩ : syracuseStep 5955353 = 4466515) B4466515
theorem B5291945 : Blo 1566981 5291945 := bstep (se 2 (by rfl) ⟨1984479, by rfl⟩ : syracuseStep 5291945 = 3968959) B3968959
theorem B2645959 : Blo 1566981 2645959 := bstep (se 1 (by rfl) ⟨1984469, by rfl⟩ : syracuseStep 2645959 = 3968939) B3968939
theorem B5955551 : Blo 1566981 5955551 := bstep (se 1 (by rfl) ⟨4466663, by rfl⟩ : syracuseStep 5955551 = 8933327) B8933327
theorem B5292701 : Blo 1566981 5292701 := bstep (se 3 (by rfl) ⟨992381, by rfl⟩ : syracuseStep 5292701 = 1984763) B1984763
theorem B10044071 : Blo 1566981 10044071 := bstep (se 1 (by rfl) ⟨7533053, by rfl⟩ : syracuseStep 10044071 = 15066107) B15066107
theorem B5293025 : Blo 1566981 5293025 := bstep (se 2 (by rfl) ⟨1984884, by rfl⟩ : syracuseStep 5293025 = 3969769) B3969769
theorem B7939457 : Blo 1566981 7939457 := bstep (se 2 (by rfl) ⟨2977296, by rfl⟩ : syracuseStep 7939457 = 5954593) B5954593
theorem B3967015 : Blo 1566981 3967015 := bstep (se 1 (by rfl) ⟨2975261, by rfl⟩ : syracuseStep 3967015 = 5950523) B5950523
theorem B2353193 : Blo 1566981 2353193 := bstep (se 2 (by rfl) ⟨882447, by rfl⟩ : syracuseStep 2353193 = 1764895) B1764895
theorem B17869247 : Blo 1566981 17869247 := bstep (se 1 (by rfl) ⟨13401935, by rfl⟩ : syracuseStep 17869247 = 26803871) B26803871
theorem B20368037 : Blo 1566981 20368037 := bstep (se 4 (by rfl) ⟨1909503, by rfl⟩ : syracuseStep 20368037 = 3819007) B3819007
theorem B1567483 : Blo 1566981 1567483 := bstep (se 1 (by rfl) ⟨1175612, by rfl⟩ : syracuseStep 1567483 = 2351225) B2351225
theorem B1567515 : Blo 1566981 1567515 := bstep (se 1 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 1567515 = 2351273) B2351273
theorem B1674055 : Blo 1566981 1674055 := bstep (se 1 (by rfl) ⟨1255541, by rfl⟩ : syracuseStep 1674055 = 2511083) B2511083
theorem B1567771 : Blo 1566981 1567771 := bstep (se 1 (by rfl) ⟨1175828, by rfl⟩ : syracuseStep 1567771 = 2351657) B2351657
theorem B12881065 : Blo 1566981 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B3525857 : Blo 1566981 3525857 := bstep (se 2 (by rfl) ⟨1322196, by rfl⟩ : syracuseStep 3525857 = 2644393) B2644393
theorem B1567999 : Blo 1566981 1567999 := bstep (se 1 (by rfl) ⟨1175999, by rfl⟩ : syracuseStep 1567999 = 2351999) B2351999
theorem B1568047 : Blo 1566981 1568047 := bstep (se 1 (by rfl) ⟨1176035, by rfl⟩ : syracuseStep 1568047 = 2352071) B2352071
theorem B26799497 : Blo 1566981 26799497 := bstep (se 2 (by rfl) ⟨10049811, by rfl⟩ : syracuseStep 26799497 = 20099623) B20099623
theorem B3526055 : Blo 1566981 3526055 := bstep (se 1 (by rfl) ⟨2644541, by rfl⟩ : syracuseStep 3526055 = 5289083) B5289083
theorem B3526163 : Blo 1566981 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B1568367 : Blo 1566981 1568367 := bstep (se 1 (by rfl) ⟨1176275, by rfl⟩ : syracuseStep 1568367 = 2352551) B2352551
theorem B15068875 : Blo 1566981 15068875 := bstep (se 1 (by rfl) ⟨11301656, by rfl⟩ : syracuseStep 15068875 = 22603313) B22603313
theorem B1568615 : Blo 1566981 1568615 := bstep (se 1 (by rfl) ⟨1176461, by rfl⟩ : syracuseStep 1568615 = 2352923) B2352923
theorem B1568623 : Blo 1566981 1568623 := bstep (se 1 (by rfl) ⟨1176467, by rfl⟩ : syracuseStep 1568623 = 2352935) B2352935
theorem B1568671 : Blo 1566981 1568671 := bstep (se 1 (by rfl) ⟨1176503, by rfl⟩ : syracuseStep 1568671 = 2353007) B2353007
theorem B7933949 : Blo 1566981 7933949 := bstep (se 3 (by rfl) ⟨1487615, by rfl⟩ : syracuseStep 7933949 = 2975231) B2975231
theorem B3575935 : Blo 1566981 3575935 := bstep (se 1 (by rfl) ⟨2681951, by rfl⟩ : syracuseStep 3575935 = 5363903) B5363903
theorem B3526919 : Blo 1566981 3526919 := bstep (se 1 (by rfl) ⟨2645189, by rfl⟩ : syracuseStep 3526919 = 5290379) B5290379
theorem B3526991 : Blo 1566981 3526991 := bstep (se 1 (by rfl) ⟨2645243, by rfl⟩ : syracuseStep 3526991 = 5290487) B5290487
theorem B371831323 : Blo 1566981 371831323 := bstep (se 1 (by rfl) ⟨278873492, by rfl⟩ : syracuseStep 371831323 = 557746985) B557746985
theorem B2978345 : Blo 1566981 2978345 := bstep (se 2 (by rfl) ⟨1116879, by rfl⟩ : syracuseStep 2978345 = 2233759) B2233759
theorem B3527657 : Blo 1566981 3527657 := bstep (se 2 (by rfl) ⟨1322871, by rfl⟩ : syracuseStep 3527657 = 2645743) B2645743
theorem B3970235 : Blo 1566981 3970235 := bstep (se 1 (by rfl) ⟨2977676, by rfl⟩ : syracuseStep 3970235 = 5955353) B5955353
theorem B5289191 : Blo 1566981 5289191 := bstep (se 1 (by rfl) ⟨3966893, by rfl⟩ : syracuseStep 5289191 = 7933787) B7933787
theorem B7533823 : Blo 1566981 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B3527945 : Blo 1566981 3527945 := bstep (se 2 (by rfl) ⟨1322979, by rfl⟩ : syracuseStep 3527945 = 2645959) B2645959
theorem B3527963 : Blo 1566981 3527963 := bstep (se 1 (by rfl) ⟨2645972, by rfl⟩ : syracuseStep 3527963 = 5291945) B5291945
theorem B3970367 : Blo 1566981 3970367 := bstep (se 1 (by rfl) ⟨2977775, by rfl⟩ : syracuseStep 3970367 = 5955551) B5955551
theorem B114464299 : Blo 1566981 114464299 := bstep (se 1 (by rfl) ⟨85848224, by rfl⟩ : syracuseStep 114464299 = 171696449) B171696449
theorem B5953607 : Blo 1566981 5953607 := bstep (se 1 (by rfl) ⟨4465205, by rfl⟩ : syracuseStep 5953607 = 8930411) B8930411
theorem B20084861 : Blo 1566981 20084861 := bstep (se 3 (by rfl) ⟨3765911, by rfl⟩ : syracuseStep 20084861 = 7531823) B7531823
theorem B3528935 : Blo 1566981 3528935 := bstep (se 1 (by rfl) ⟨2646701, by rfl⟩ : syracuseStep 3528935 = 5293403) B5293403
theorem B9050611 : Blo 1566981 9050611 := bstep (se 1 (by rfl) ⟨6787958, by rfl⟩ : syracuseStep 9050611 = 13575917) B13575917
theorem B3529223 : Blo 1566981 3529223 := bstep (se 1 (by rfl) ⟨2646917, by rfl⟩ : syracuseStep 3529223 = 5293835) B5293835
theorem B16947731 : Blo 1566981 16947731 := bstep (se 1 (by rfl) ⟨12710798, by rfl⟩ : syracuseStep 16947731 = 25421597) B25421597
theorem B6699601 : Blo 1566981 6699601 := bstep (se 2 (by rfl) ⟨2512350, by rfl⟩ : syracuseStep 6699601 = 5024701) B5024701
theorem B8927927 : Blo 1566981 8927927 := bstep (se 1 (by rfl) ⟨6695945, by rfl⟩ : syracuseStep 8927927 = 13391891) B13391891
theorem B5020487 : Blo 1566981 5020487 := bstep (se 1 (by rfl) ⟨3765365, by rfl⟩ : syracuseStep 5020487 = 7530731) B7530731
theorem B64338875 : Blo 1566981 64338875 := bstep (se 1 (by rfl) ⟨48254156, by rfl⟩ : syracuseStep 64338875 = 96508313) B96508313
theorem B16309349 : Blo 1566981 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B26795123 : Blo 1566981 26795123 := bstep (se 1 (by rfl) ⟨20096342, by rfl⟩ : syracuseStep 26795123 = 40192685) B40192685
theorem B5291567 : Blo 1566981 5291567 := bstep (se 1 (by rfl) ⟨3968675, by rfl⟩ : syracuseStep 5291567 = 7937351) B7937351
theorem B8592985 : Blo 1566981 8592985 := bstep (se 2 (by rfl) ⟨3222369, by rfl⟩ : syracuseStep 8592985 = 6444739) B6444739
theorem B2351099 : Blo 1566981 2351099 := bstep (se 1 (by rfl) ⟨1763324, by rfl⟩ : syracuseStep 2351099 = 3526649) B3526649
theorem B4767913 : Blo 1566981 4767913 := bstep (se 2 (by rfl) ⟨1787967, by rfl⟩ : syracuseStep 4767913 = 3575935) B3575935
theorem B2351279 : Blo 1566981 2351279 := bstep (se 1 (by rfl) ⟨1763459, by rfl⟩ : syracuseStep 2351279 = 3526919) B3526919
theorem B2351327 : Blo 1566981 2351327 := bstep (se 1 (by rfl) ⟨1763495, by rfl⟩ : syracuseStep 2351327 = 3526991) B3526991
theorem B12067481 : Blo 1566981 12067481 := bstep (se 2 (by rfl) ⟨4525305, by rfl⟩ : syracuseStep 12067481 = 9050611) B9050611
theorem B2351771 : Blo 1566981 2351771 := bstep (se 1 (by rfl) ⟨1763828, by rfl⟩ : syracuseStep 2351771 = 3527657) B3527657
theorem B2646823 : Blo 1566981 2646823 := bstep (se 1 (by rfl) ⟨1985117, by rfl⟩ : syracuseStep 2646823 = 3970235) B3970235
theorem B2351963 : Blo 1566981 2351963 := bstep (se 1 (by rfl) ⟨1763972, by rfl⟩ : syracuseStep 2351963 = 3527945) B3527945
theorem B2351975 : Blo 1566981 2351975 := bstep (se 1 (by rfl) ⟨1763981, by rfl⟩ : syracuseStep 2351975 = 3527963) B3527963
theorem B2646911 : Blo 1566981 2646911 := bstep (se 1 (by rfl) ⟨1985183, by rfl⟩ : syracuseStep 2646911 = 3970367) B3970367
theorem B5292971 : Blo 1566981 5292971 := bstep (se 1 (by rfl) ⟨3969728, by rfl⟩ : syracuseStep 5292971 = 7939457) B7939457
theorem B2352623 : Blo 1566981 2352623 := bstep (se 1 (by rfl) ⟨1764467, by rfl⟩ : syracuseStep 2352623 = 3528935) B3528935
theorem B11912831 : Blo 1566981 11912831 := bstep (se 1 (by rfl) ⟨8934623, by rfl⟩ : syracuseStep 11912831 = 17869247) B17869247
theorem B10045097 : Blo 1566981 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B2352815 : Blo 1566981 2352815 := bstep (se 1 (by rfl) ⟨1764611, by rfl⟩ : syracuseStep 2352815 = 3529223) B3529223
theorem B11298487 : Blo 1566981 11298487 := bstep (se 1 (by rfl) ⟨8473865, by rfl⟩ : syracuseStep 11298487 = 16947731) B16947731
theorem B152619065 : Blo 1566981 152619065 := bstep (se 2 (by rfl) ⟨57232149, by rfl⟩ : syracuseStep 152619065 = 114464299) B114464299
theorem B10872899 : Blo 1566981 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B1567399 : Blo 1566981 1567399 := bstep (se 1 (by rfl) ⟨1175549, by rfl⟩ : syracuseStep 1567399 = 2351099) B2351099
theorem B1985563 : Blo 1566981 1985563 := bstep (se 1 (by rfl) ⟨1489172, by rfl⟩ : syracuseStep 1985563 = 2978345) B2978345
theorem B6696047 : Blo 1566981 6696047 := bstep (se 1 (by rfl) ⟨5022035, by rfl⟩ : syracuseStep 6696047 = 10044071) B10044071
theorem B45829253 : Blo 1566981 45829253 := bstep (se 4 (by rfl) ⟨4296492, by rfl⟩ : syracuseStep 45829253 = 8592985) B8592985
theorem B495775097 : Blo 1566981 495775097 := bstep (se 2 (by rfl) ⟨185915661, by rfl⟩ : syracuseStep 495775097 = 371831323) B371831323
theorem B8932801 : Blo 1566981 8932801 := bstep (se 2 (by rfl) ⟨3349800, by rfl⟩ : syracuseStep 8932801 = 6699601) B6699601
theorem B3526127 : Blo 1566981 3526127 := bstep (se 1 (by rfl) ⟨2644595, by rfl⟩ : syracuseStep 3526127 = 5289191) B5289191
theorem B2232073 : Blo 1566981 2232073 := bstep (se 2 (by rfl) ⟨837027, by rfl⟩ : syracuseStep 2232073 = 1674055) B1674055
theorem B1568795 : Blo 1566981 1568795 := bstep (se 1 (by rfl) ⟨1176596, by rfl⟩ : syracuseStep 1568795 = 2353193) B2353193
theorem B3969071 : Blo 1566981 3969071 := bstep (se 1 (by rfl) ⟨2976803, by rfl⟩ : syracuseStep 3969071 = 5953607) B5953607
theorem B13389907 : Blo 1566981 13389907 := bstep (se 1 (by rfl) ⟨10042430, by rfl⟩ : syracuseStep 13389907 = 20084861) B20084861
theorem B17174753 : Blo 1566981 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B13578691 : Blo 1566981 13578691 := bstep (se 1 (by rfl) ⟨10184018, by rfl⟩ : syracuseStep 13578691 = 20368037) B20368037
theorem B5951951 : Blo 1566981 5951951 := bstep (se 1 (by rfl) ⟨4463963, by rfl⟩ : syracuseStep 5951951 = 8927927) B8927927
theorem B3346991 : Blo 1566981 3346991 := bstep (se 1 (by rfl) ⟨2510243, by rfl⟩ : syracuseStep 3346991 = 5020487) B5020487
theorem B17863415 : Blo 1566981 17863415 := bstep (se 1 (by rfl) ⟨13397561, by rfl⟩ : syracuseStep 17863415 = 26795123) B26795123
theorem B20091833 : Blo 1566981 20091833 := bstep (se 2 (by rfl) ⟨7534437, by rfl⟩ : syracuseStep 20091833 = 15068875) B15068875
theorem B3527711 : Blo 1566981 3527711 := bstep (se 1 (by rfl) ⟨2645783, by rfl⟩ : syracuseStep 3527711 = 5291567) B5291567
theorem B5289299 : Blo 1566981 5289299 := bstep (se 1 (by rfl) ⟨3966974, by rfl⟩ : syracuseStep 5289299 = 7933949) B7933949
theorem B5289353 : Blo 1566981 5289353 := bstep (se 2 (by rfl) ⟨1983507, by rfl⟩ : syracuseStep 5289353 = 3967015) B3967015
theorem B3528467 : Blo 1566981 3528467 := bstep (se 1 (by rfl) ⟨2646350, by rfl⟩ : syracuseStep 3528467 = 5292701) B5292701
theorem B3528683 : Blo 1566981 3528683 := bstep (se 1 (by rfl) ⟨2646512, by rfl⟩ : syracuseStep 3528683 = 5293025) B5293025
theorem B42892583 : Blo 1566981 42892583 := bstep (se 1 (by rfl) ⟨32169437, by rfl⟩ : syracuseStep 42892583 = 64338875) B64338875
theorem B2350571 : Blo 1566981 2350571 := bstep (se 1 (by rfl) ⟨1762928, by rfl⟩ : syracuseStep 2350571 = 3525857) B3525857
theorem B17866331 : Blo 1566981 17866331 := bstep (se 1 (by rfl) ⟨13399748, by rfl⟩ : syracuseStep 17866331 = 26799497) B26799497
theorem B2350703 : Blo 1566981 2350703 := bstep (se 1 (by rfl) ⟨1763027, by rfl⟩ : syracuseStep 2350703 = 3526055) B3526055
theorem B2350775 : Blo 1566981 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B2646047 : Blo 1566981 2646047 := bstep (se 1 (by rfl) ⟨1984535, by rfl⟩ : syracuseStep 2646047 = 3969071) B3969071
theorem B6357217 : Blo 1566981 6357217 := bstep (se 2 (by rfl) ⟨2383956, by rfl⟩ : syracuseStep 6357217 = 4767913) B4767913
theorem B18104921 : Blo 1566981 18104921 := bstep (se 2 (by rfl) ⟨6789345, by rfl⟩ : syracuseStep 18104921 = 13578691) B13578691
theorem B13394555 : Blo 1566981 13394555 := bstep (se 1 (by rfl) ⟨10045916, by rfl⟩ : syracuseStep 13394555 = 20091833) B20091833
theorem B2351807 : Blo 1566981 2351807 := bstep (se 1 (by rfl) ⟨1763855, by rfl⟩ : syracuseStep 2351807 = 3527711) B3527711
theorem B2352311 : Blo 1566981 2352311 := bstep (se 1 (by rfl) ⟨1764233, by rfl⟩ : syracuseStep 2352311 = 3528467) B3528467
theorem B2352455 : Blo 1566981 2352455 := bstep (se 1 (by rfl) ⟨1764341, by rfl⟩ : syracuseStep 2352455 = 3528683) B3528683
theorem B2647417 : Blo 1566981 2647417 := bstep (se 2 (by rfl) ⟨992781, by rfl⟩ : syracuseStep 2647417 = 1985563) B1985563
theorem B101746043 : Blo 1566981 101746043 := bstep (se 1 (by rfl) ⟨76309532, by rfl⟩ : syracuseStep 101746043 = 152619065) B152619065
theorem B32179949 : Blo 1566981 32179949 := bstep (se 3 (by rfl) ⟨6033740, by rfl⟩ : syracuseStep 32179949 = 12067481) B12067481
theorem B330516731 : Blo 1566981 330516731 := bstep (se 1 (by rfl) ⟨247887548, by rfl⟩ : syracuseStep 330516731 = 495775097) B495775097
theorem B1567047 : Blo 1566981 1567047 := bstep (se 1 (by rfl) ⟨1175285, by rfl⟩ : syracuseStep 1567047 = 2350571) B2350571
theorem B2976097 : Blo 1566981 2976097 := bstep (se 2 (by rfl) ⟨1116036, by rfl⟩ : syracuseStep 2976097 = 2232073) B2232073
theorem B1567135 : Blo 1566981 1567135 := bstep (se 1 (by rfl) ⟨1175351, by rfl⟩ : syracuseStep 1567135 = 2350703) B2350703
theorem B1567183 : Blo 1566981 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B17853209 : Blo 1566981 17853209 := bstep (se 2 (by rfl) ⟨6694953, by rfl⟩ : syracuseStep 17853209 = 13389907) B13389907
theorem B1567519 : Blo 1566981 1567519 := bstep (se 1 (by rfl) ⟨1175639, by rfl⟩ : syracuseStep 1567519 = 2351279) B2351279
theorem B1567551 : Blo 1566981 1567551 := bstep (se 1 (by rfl) ⟨1175663, by rfl⟩ : syracuseStep 1567551 = 2351327) B2351327
theorem B3967967 : Blo 1566981 3967967 := bstep (se 1 (by rfl) ⟨2975975, by rfl⟩ : syracuseStep 3967967 = 5951951) B5951951
theorem B2231327 : Blo 1566981 2231327 := bstep (se 1 (by rfl) ⟨1673495, by rfl⟩ : syracuseStep 2231327 = 3346991) B3346991
theorem B1567847 : Blo 1566981 1567847 := bstep (se 1 (by rfl) ⟨1175885, by rfl⟩ : syracuseStep 1567847 = 2351771) B2351771
theorem B1567975 : Blo 1566981 1567975 := bstep (se 1 (by rfl) ⟨1175981, by rfl⟩ : syracuseStep 1567975 = 2351963) B2351963
theorem B1567983 : Blo 1566981 1567983 := bstep (se 1 (by rfl) ⟨1175987, by rfl⟩ : syracuseStep 1567983 = 2351975) B2351975
theorem B1764607 : Blo 1566981 1764607 := bstep (se 1 (by rfl) ⟨1323455, by rfl⟩ : syracuseStep 1764607 = 2646911) B2646911
theorem B114380221 : Blo 1566981 114380221 := bstep (se 3 (by rfl) ⟨21446291, by rfl⟩ : syracuseStep 114380221 = 42892583) B42892583
theorem B3526199 : Blo 1566981 3526199 := bstep (se 1 (by rfl) ⟨2644649, by rfl⟩ : syracuseStep 3526199 = 5289299) B5289299
theorem B3526235 : Blo 1566981 3526235 := bstep (se 1 (by rfl) ⟨2644676, by rfl⟩ : syracuseStep 3526235 = 5289353) B5289353
theorem B1568415 : Blo 1566981 1568415 := bstep (se 1 (by rfl) ⟨1176311, by rfl⟩ : syracuseStep 1568415 = 2352623) B2352623
theorem B7941887 : Blo 1566981 7941887 := bstep (se 1 (by rfl) ⟨5956415, by rfl⟩ : syracuseStep 7941887 = 11912831) B11912831
theorem B6696731 : Blo 1566981 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B1568543 : Blo 1566981 1568543 := bstep (se 1 (by rfl) ⟨1176407, by rfl⟩ : syracuseStep 1568543 = 2352815) B2352815
theorem B30552835 : Blo 1566981 30552835 := bstep (se 1 (by rfl) ⟨22914626, by rfl⟩ : syracuseStep 30552835 = 45829253) B45829253
theorem B11449835 : Blo 1566981 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B17856125 : Blo 1566981 17856125 := bstep (se 3 (by rfl) ⟨3348023, by rfl⟩ : syracuseStep 17856125 = 6696047) B6696047
theorem B11908943 : Blo 1566981 11908943 := bstep (se 1 (by rfl) ⟨8931707, by rfl⟩ : syracuseStep 11908943 = 17863415) B17863415
theorem B3528647 : Blo 1566981 3528647 := bstep (se 1 (by rfl) ⟨2646485, by rfl⟩ : syracuseStep 3528647 = 5292971) B5292971
theorem B3529097 : Blo 1566981 3529097 := bstep (se 2 (by rfl) ⟨1323411, by rfl⟩ : syracuseStep 3529097 = 2646823) B2646823
theorem B7248599 : Blo 1566981 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B11910401 : Blo 1566981 11910401 := bstep (se 2 (by rfl) ⟨4466400, by rfl⟩ : syracuseStep 11910401 = 8932801) B8932801
theorem B15064649 : Blo 1566981 15064649 := bstep (se 2 (by rfl) ⟨5649243, by rfl⟩ : syracuseStep 15064649 = 11298487) B11298487
theorem B2350751 : Blo 1566981 2350751 := bstep (se 1 (by rfl) ⟨1763063, by rfl⟩ : syracuseStep 2350751 = 3526127) B3526127
theorem B11910887 : Blo 1566981 11910887 := bstep (se 1 (by rfl) ⟨8933165, by rfl⟩ : syracuseStep 11910887 = 17866331) B17866331
theorem B8929703 : Blo 1566981 8929703 := bstep (se 1 (by rfl) ⟨6697277, by rfl⟩ : syracuseStep 8929703 = 13394555) B13394555
theorem B881377949 : Blo 1566981 881377949 := bstep (se 3 (by rfl) ⟨165258365, by rfl⟩ : syracuseStep 881377949 = 330516731) B330516731
theorem B67830695 : Blo 1566981 67830695 := bstep (se 1 (by rfl) ⟨50873021, by rfl⟩ : syracuseStep 67830695 = 101746043) B101746043
theorem B11904083 : Blo 1566981 11904083 := bstep (se 1 (by rfl) ⟨8928062, by rfl⟩ : syracuseStep 11904083 = 17856125) B17856125
theorem B7939295 : Blo 1566981 7939295 := bstep (se 1 (by rfl) ⟨5954471, by rfl⟩ : syracuseStep 7939295 = 11908943) B11908943
theorem B2352431 : Blo 1566981 2352431 := bstep (se 1 (by rfl) ⟨1764323, by rfl⟩ : syracuseStep 2352431 = 3528647) B3528647
theorem B2352731 : Blo 1566981 2352731 := bstep (se 1 (by rfl) ⟨1764548, by rfl⟩ : syracuseStep 2352731 = 3529097) B3529097
theorem B2352809 : Blo 1566981 2352809 := bstep (se 2 (by rfl) ⟨882303, by rfl⟩ : syracuseStep 2352809 = 1764607) B1764607
theorem B7940267 : Blo 1566981 7940267 := bstep (se 1 (by rfl) ⟨5955200, by rfl⟩ : syracuseStep 7940267 = 11910401) B11910401
theorem B1567167 : Blo 1566981 1567167 := bstep (se 1 (by rfl) ⟨1175375, by rfl⟩ : syracuseStep 1567167 = 2350751) B2350751
theorem B7940591 : Blo 1566981 7940591 := bstep (se 1 (by rfl) ⟨5955443, by rfl⟩ : syracuseStep 7940591 = 11910887) B11910887
theorem B5294591 : Blo 1566981 5294591 := bstep (se 1 (by rfl) ⟨3970943, by rfl⟩ : syracuseStep 5294591 = 7941887) B7941887
theorem B1764031 : Blo 1566981 1764031 := bstep (se 1 (by rfl) ⟨1323023, by rfl⟩ : syracuseStep 1764031 = 2646047) B2646047
theorem B5950205 : Blo 1566981 5950205 := bstep (se 3 (by rfl) ⟨1115663, by rfl⟩ : syracuseStep 5950205 = 2231327) B2231327
theorem B12069947 : Blo 1566981 12069947 := bstep (se 1 (by rfl) ⟨9052460, by rfl⟩ : syracuseStep 12069947 = 18104921) B18104921
theorem B1567871 : Blo 1566981 1567871 := bstep (se 1 (by rfl) ⟨1175903, by rfl⟩ : syracuseStep 1567871 = 2351807) B2351807
theorem B3968129 : Blo 1566981 3968129 := bstep (se 2 (by rfl) ⟨1488048, by rfl⟩ : syracuseStep 3968129 = 2976097) B2976097
theorem B1568207 : Blo 1566981 1568207 := bstep (se 1 (by rfl) ⟨1176155, by rfl⟩ : syracuseStep 1568207 = 2352311) B2352311
theorem B1568303 : Blo 1566981 1568303 := bstep (se 1 (by rfl) ⟨1176227, by rfl⟩ : syracuseStep 1568303 = 2352455) B2352455
theorem B152506961 : Blo 1566981 152506961 := bstep (se 2 (by rfl) ⟨57190110, by rfl⟩ : syracuseStep 152506961 = 114380221) B114380221
theorem B8476289 : Blo 1566981 8476289 := bstep (se 2 (by rfl) ⟨3178608, by rfl⟩ : syracuseStep 8476289 = 6357217) B6357217
theorem B7633223 : Blo 1566981 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B40737113 : Blo 1566981 40737113 := bstep (se 2 (by rfl) ⟨15276417, by rfl⟩ : syracuseStep 40737113 = 30552835) B30552835
theorem B21453299 : Blo 1566981 21453299 := bstep (se 1 (by rfl) ⟨16089974, by rfl⟩ : syracuseStep 21453299 = 32179949) B32179949
theorem B4832399 : Blo 1566981 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B3529889 : Blo 1566981 3529889 := bstep (se 2 (by rfl) ⟨1323708, by rfl⟩ : syracuseStep 3529889 = 2647417) B2647417
theorem B11902139 : Blo 1566981 11902139 := bstep (se 1 (by rfl) ⟨8926604, by rfl⟩ : syracuseStep 11902139 = 17853209) B17853209
theorem B2645311 : Blo 1566981 2645311 := bstep (se 1 (by rfl) ⟨1983983, by rfl⟩ : syracuseStep 2645311 = 3967967) B3967967
theorem B2350799 : Blo 1566981 2350799 := bstep (se 1 (by rfl) ⟨1763099, by rfl⟩ : syracuseStep 2350799 = 3526199) B3526199
theorem B10043099 : Blo 1566981 10043099 := bstep (se 1 (by rfl) ⟨7532324, by rfl⟩ : syracuseStep 10043099 = 15064649) B15064649
theorem B2350823 : Blo 1566981 2350823 := bstep (se 1 (by rfl) ⟨1763117, by rfl⟩ : syracuseStep 2350823 = 3526235) B3526235
theorem B4464487 : Blo 1566981 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B12886397 : Blo 1566981 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B101671307 : Blo 1566981 101671307 := bstep (se 1 (by rfl) ⟨76253480, by rfl⟩ : syracuseStep 101671307 = 152506961) B152506961
theorem B45220463 : Blo 1566981 45220463 := bstep (se 1 (by rfl) ⟨33915347, by rfl⟩ : syracuseStep 45220463 = 67830695) B67830695
theorem B5292863 : Blo 1566981 5292863 := bstep (se 1 (by rfl) ⟨3969647, by rfl⟩ : syracuseStep 5292863 = 7939295) B7939295
theorem B2352041 : Blo 1566981 2352041 := bstep (se 2 (by rfl) ⟨882015, by rfl⟩ : syracuseStep 2352041 = 1764031) B1764031
theorem B5293511 : Blo 1566981 5293511 := bstep (se 1 (by rfl) ⟨3970133, by rfl⟩ : syracuseStep 5293511 = 7940267) B7940267
theorem B5088815 : Blo 1566981 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B27158075 : Blo 1566981 27158075 := bstep (se 1 (by rfl) ⟨20368556, by rfl⟩ : syracuseStep 27158075 = 40737113) B40737113
theorem B5293727 : Blo 1566981 5293727 := bstep (se 1 (by rfl) ⟨3970295, by rfl⟩ : syracuseStep 5293727 = 7940591) B7940591
theorem B3966803 : Blo 1566981 3966803 := bstep (se 1 (by rfl) ⟨2975102, by rfl⟩ : syracuseStep 3966803 = 5950205) B5950205
theorem B8046631 : Blo 1566981 8046631 := bstep (se 1 (by rfl) ⟨6034973, by rfl⟩ : syracuseStep 8046631 = 12069947) B12069947
theorem B2353259 : Blo 1566981 2353259 := bstep (se 1 (by rfl) ⟨1764944, by rfl⟩ : syracuseStep 2353259 = 3529889) B3529889
theorem B1567199 : Blo 1566981 1567199 := bstep (se 1 (by rfl) ⟨1175399, by rfl⟩ : syracuseStep 1567199 = 2350799) B2350799
theorem B6695399 : Blo 1566981 6695399 := bstep (se 1 (by rfl) ⟨5021549, by rfl⟩ : syracuseStep 6695399 = 10043099) B10043099
theorem B1567215 : Blo 1566981 1567215 := bstep (se 1 (by rfl) ⟨1175411, by rfl⟩ : syracuseStep 1567215 = 2350823) B2350823
theorem B1568287 : Blo 1566981 1568287 := bstep (se 1 (by rfl) ⟨1176215, by rfl⟩ : syracuseStep 1568287 = 2352431) B2352431
theorem B1568487 : Blo 1566981 1568487 := bstep (se 1 (by rfl) ⟨1176365, by rfl⟩ : syracuseStep 1568487 = 2352731) B2352731
theorem B1568539 : Blo 1566981 1568539 := bstep (se 1 (by rfl) ⟨1176404, by rfl⟩ : syracuseStep 1568539 = 2352809) B2352809
theorem B3527081 : Blo 1566981 3527081 := bstep (se 2 (by rfl) ⟨1322655, by rfl⟩ : syracuseStep 3527081 = 2645311) B2645311
theorem B7934759 : Blo 1566981 7934759 := bstep (se 1 (by rfl) ⟨5951069, by rfl⟩ : syracuseStep 7934759 = 11902139) B11902139
theorem B5952649 : Blo 1566981 5952649 := bstep (se 2 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 5952649 = 4464487) B4464487
theorem B5953135 : Blo 1566981 5953135 := bstep (se 1 (by rfl) ⟨4464851, by rfl⟩ : syracuseStep 5953135 = 8929703) B8929703
theorem B587585299 : Blo 1566981 587585299 := bstep (se 1 (by rfl) ⟨440688974, by rfl⟩ : syracuseStep 587585299 = 881377949) B881377949
theorem B7936055 : Blo 1566981 7936055 := bstep (se 1 (by rfl) ⟨5952041, by rfl⟩ : syracuseStep 7936055 = 11904083) B11904083
theorem B5650859 : Blo 1566981 5650859 := bstep (se 1 (by rfl) ⟨4238144, by rfl⟩ : syracuseStep 5650859 = 8476289) B8476289
theorem B14302199 : Blo 1566981 14302199 := bstep (se 1 (by rfl) ⟨10726649, by rfl⟩ : syracuseStep 14302199 = 21453299) B21453299
theorem B3529727 : Blo 1566981 3529727 := bstep (se 1 (by rfl) ⟨2647295, by rfl⟩ : syracuseStep 3529727 = 5294591) B5294591
theorem B2645419 : Blo 1566981 2645419 := bstep (se 1 (by rfl) ⟨1984064, by rfl⟩ : syracuseStep 2645419 = 3968129) B3968129
theorem B67780871 : Blo 1566981 67780871 := bstep (se 1 (by rfl) ⟨50835653, by rfl⟩ : syracuseStep 67780871 = 101671307) B101671307
theorem B2351387 : Blo 1566981 2351387 := bstep (se 1 (by rfl) ⟨1763540, by rfl⟩ : syracuseStep 2351387 = 3527081) B3527081
theorem B30146975 : Blo 1566981 30146975 := bstep (se 1 (by rfl) ⟨22610231, by rfl⟩ : syracuseStep 30146975 = 45220463) B45220463
theorem B3392543 : Blo 1566981 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B18105383 : Blo 1566981 18105383 := bstep (se 1 (by rfl) ⟨13579037, by rfl⟩ : syracuseStep 18105383 = 27158075) B27158075
theorem B2353151 : Blo 1566981 2353151 := bstep (se 1 (by rfl) ⟨1764863, by rfl⟩ : syracuseStep 2353151 = 3529727) B3529727
theorem B1568027 : Blo 1566981 1568027 := bstep (se 1 (by rfl) ⟨1176020, by rfl⟩ : syracuseStep 1568027 = 2352041) B2352041
theorem B1568839 : Blo 1566981 1568839 := bstep (se 1 (by rfl) ⟨1176629, by rfl⟩ : syracuseStep 1568839 = 2353259) B2353259
theorem B3527225 : Blo 1566981 3527225 := bstep (se 2 (by rfl) ⟨1322709, by rfl⟩ : syracuseStep 3527225 = 2645419) B2645419
theorem B783447065 : Blo 1566981 783447065 := bstep (se 2 (by rfl) ⟨293792649, by rfl⟩ : syracuseStep 783447065 = 587585299) B587585299
theorem B42915365 : Blo 1566981 42915365 := bstep (se 4 (by rfl) ⟨4023315, by rfl⟩ : syracuseStep 42915365 = 8046631) B8046631
theorem B8590931 : Blo 1566981 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B5289839 : Blo 1566981 5289839 := bstep (se 1 (by rfl) ⟨3967379, by rfl⟩ : syracuseStep 5289839 = 7934759) B7934759
theorem B3528575 : Blo 1566981 3528575 := bstep (se 1 (by rfl) ⟨2646431, by rfl⟩ : syracuseStep 3528575 = 5292863) B5292863
theorem B3529007 : Blo 1566981 3529007 := bstep (se 1 (by rfl) ⟨2646755, by rfl⟩ : syracuseStep 3529007 = 5293511) B5293511
theorem B3529151 : Blo 1566981 3529151 := bstep (se 1 (by rfl) ⟨2646863, by rfl⟩ : syracuseStep 3529151 = 5293727) B5293727
theorem B2644535 : Blo 1566981 2644535 := bstep (se 1 (by rfl) ⟨1983401, by rfl⟩ : syracuseStep 2644535 = 3966803) B3966803
theorem B5290703 : Blo 1566981 5290703 := bstep (se 1 (by rfl) ⟨3968027, by rfl⟩ : syracuseStep 5290703 = 7936055) B7936055
theorem B7936865 : Blo 1566981 7936865 := bstep (se 2 (by rfl) ⟨2976324, by rfl⟩ : syracuseStep 7936865 = 5952649) B5952649
theorem B3767239 : Blo 1566981 3767239 := bstep (se 1 (by rfl) ⟨2825429, by rfl⟩ : syracuseStep 3767239 = 5650859) B5650859
theorem B4463599 : Blo 1566981 4463599 := bstep (se 1 (by rfl) ⟨3347699, by rfl⟩ : syracuseStep 4463599 = 6695399) B6695399
theorem B9534799 : Blo 1566981 9534799 := bstep (se 1 (by rfl) ⟨7151099, by rfl⟩ : syracuseStep 9534799 = 14302199) B14302199
theorem B7937513 : Blo 1566981 7937513 := bstep (se 2 (by rfl) ⟨2976567, by rfl⟩ : syracuseStep 7937513 = 5953135) B5953135
theorem B45187247 : Blo 1566981 45187247 := bstep (se 1 (by rfl) ⟨33890435, by rfl⟩ : syracuseStep 45187247 = 67780871) B67780871
theorem B2351483 : Blo 1566981 2351483 := bstep (se 1 (by rfl) ⟨1763612, by rfl⟩ : syracuseStep 2351483 = 3527225) B3527225
theorem B522298043 : Blo 1566981 522298043 := bstep (se 1 (by rfl) ⟨391723532, by rfl⟩ : syracuseStep 522298043 = 783447065) B783447065
theorem B5727287 : Blo 1566981 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B2352383 : Blo 1566981 2352383 := bstep (se 1 (by rfl) ⟨1764287, by rfl⟩ : syracuseStep 2352383 = 3528575) B3528575
theorem B5022985 : Blo 1566981 5022985 := bstep (se 2 (by rfl) ⟨1883619, by rfl⟩ : syracuseStep 5022985 = 3767239) B3767239
theorem B2352671 : Blo 1566981 2352671 := bstep (se 1 (by rfl) ⟨1764503, by rfl⟩ : syracuseStep 2352671 = 3529007) B3529007
theorem B2352767 : Blo 1566981 2352767 := bstep (se 1 (by rfl) ⟨1764575, by rfl⟩ : syracuseStep 2352767 = 3529151) B3529151
theorem B1763023 : Blo 1566981 1763023 := bstep (se 1 (by rfl) ⟨1322267, by rfl⟩ : syracuseStep 1763023 = 2644535) B2644535
theorem B9046781 : Blo 1566981 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B1567591 : Blo 1566981 1567591 := bstep (se 1 (by rfl) ⟨1175693, by rfl⟩ : syracuseStep 1567591 = 2351387) B2351387
theorem B20097983 : Blo 1566981 20097983 := bstep (se 1 (by rfl) ⟨15073487, by rfl⟩ : syracuseStep 20097983 = 30146975) B30146975
theorem B12070255 : Blo 1566981 12070255 := bstep (se 1 (by rfl) ⟨9052691, by rfl⟩ : syracuseStep 12070255 = 18105383) B18105383
theorem B28610243 : Blo 1566981 28610243 := bstep (se 1 (by rfl) ⟨21457682, by rfl⟩ : syracuseStep 28610243 = 42915365) B42915365
theorem B3526559 : Blo 1566981 3526559 := bstep (se 1 (by rfl) ⟨2644919, by rfl⟩ : syracuseStep 3526559 = 5289839) B5289839
theorem B5951465 : Blo 1566981 5951465 := bstep (se 2 (by rfl) ⟨2231799, by rfl⟩ : syracuseStep 5951465 = 4463599) B4463599
theorem B1568767 : Blo 1566981 1568767 := bstep (se 1 (by rfl) ⟨1176575, by rfl⟩ : syracuseStep 1568767 = 2353151) B2353151
theorem B50852261 : Blo 1566981 50852261 := bstep (se 4 (by rfl) ⟨4767399, by rfl⟩ : syracuseStep 50852261 = 9534799) B9534799
theorem B3527135 : Blo 1566981 3527135 := bstep (se 1 (by rfl) ⟨2645351, by rfl⟩ : syracuseStep 3527135 = 5290703) B5290703
theorem B5291243 : Blo 1566981 5291243 := bstep (se 1 (by rfl) ⟨3968432, by rfl⟩ : syracuseStep 5291243 = 7936865) B7936865
theorem B5291675 : Blo 1566981 5291675 := bstep (se 1 (by rfl) ⟨3968756, by rfl⟩ : syracuseStep 5291675 = 7937513) B7937513
theorem B2351423 : Blo 1566981 2351423 := bstep (se 1 (by rfl) ⟨1763567, by rfl⟩ : syracuseStep 2351423 = 3527135) B3527135
theorem B3818191 : Blo 1566981 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B6031187 : Blo 1566981 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B19073495 : Blo 1566981 19073495 := bstep (se 1 (by rfl) ⟨14305121, by rfl⟩ : syracuseStep 19073495 = 28610243) B28610243
theorem B3967643 : Blo 1566981 3967643 := bstep (se 1 (by rfl) ⟨2975732, by rfl⟩ : syracuseStep 3967643 = 5951465) B5951465
theorem B30124831 : Blo 1566981 30124831 := bstep (se 1 (by rfl) ⟨22593623, by rfl⟩ : syracuseStep 30124831 = 45187247) B45187247
theorem B1567655 : Blo 1566981 1567655 := bstep (se 1 (by rfl) ⟨1175741, by rfl⟩ : syracuseStep 1567655 = 2351483) B2351483
theorem B33901507 : Blo 1566981 33901507 := bstep (se 1 (by rfl) ⟨25426130, by rfl⟩ : syracuseStep 33901507 = 50852261) B50852261
theorem B1568255 : Blo 1566981 1568255 := bstep (se 1 (by rfl) ⟨1176191, by rfl⟩ : syracuseStep 1568255 = 2352383) B2352383
theorem B1568447 : Blo 1566981 1568447 := bstep (se 1 (by rfl) ⟨1176335, by rfl⟩ : syracuseStep 1568447 = 2352671) B2352671
theorem B1568511 : Blo 1566981 1568511 := bstep (se 1 (by rfl) ⟨1176383, by rfl⟩ : syracuseStep 1568511 = 2352767) B2352767
theorem B6697313 : Blo 1566981 6697313 := bstep (se 2 (by rfl) ⟨2511492, by rfl⟩ : syracuseStep 6697313 = 5022985) B5022985
theorem B16093673 : Blo 1566981 16093673 := bstep (se 2 (by rfl) ⟨6035127, by rfl⟩ : syracuseStep 16093673 = 12070255) B12070255
theorem B13398655 : Blo 1566981 13398655 := bstep (se 1 (by rfl) ⟨10048991, by rfl⟩ : syracuseStep 13398655 = 20097983) B20097983
theorem B3527495 : Blo 1566981 3527495 := bstep (se 1 (by rfl) ⟨2645621, by rfl⟩ : syracuseStep 3527495 = 5291243) B5291243
theorem B3527783 : Blo 1566981 3527783 := bstep (se 1 (by rfl) ⟨2645837, by rfl⟩ : syracuseStep 3527783 = 5291675) B5291675
theorem B348198695 : Blo 1566981 348198695 := bstep (se 1 (by rfl) ⟨261149021, by rfl⟩ : syracuseStep 348198695 = 522298043) B522298043
theorem B2350697 : Blo 1566981 2350697 := bstep (se 2 (by rfl) ⟨881511, by rfl⟩ : syracuseStep 2350697 = 1763023) B1763023
theorem B2351039 : Blo 1566981 2351039 := bstep (se 1 (by rfl) ⟨1763279, by rfl⟩ : syracuseStep 2351039 = 3526559) B3526559
theorem B4464875 : Blo 1566981 4464875 := bstep (se 1 (by rfl) ⟨3348656, by rfl⟩ : syracuseStep 4464875 = 6697313) B6697313
theorem B2351663 : Blo 1566981 2351663 := bstep (se 1 (by rfl) ⟨1763747, by rfl⟩ : syracuseStep 2351663 = 3527495) B3527495
theorem B2351855 : Blo 1566981 2351855 := bstep (se 1 (by rfl) ⟨1763891, by rfl⟩ : syracuseStep 2351855 = 3527783) B3527783
theorem B40166441 : Blo 1566981 40166441 := bstep (se 2 (by rfl) ⟨15062415, by rfl⟩ : syracuseStep 40166441 = 30124831) B30124831
theorem B12715663 : Blo 1566981 12715663 := bstep (se 1 (by rfl) ⟨9536747, by rfl⟩ : syracuseStep 12715663 = 19073495) B19073495
theorem B1567131 : Blo 1566981 1567131 := bstep (se 1 (by rfl) ⟨1175348, by rfl⟩ : syracuseStep 1567131 = 2350697) B2350697
theorem B1567359 : Blo 1566981 1567359 := bstep (se 1 (by rfl) ⟨1175519, by rfl⟩ : syracuseStep 1567359 = 2351039) B2351039
theorem B1567615 : Blo 1566981 1567615 := bstep (se 1 (by rfl) ⟨1175711, by rfl⟩ : syracuseStep 1567615 = 2351423) B2351423
theorem B5090921 : Blo 1566981 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B232132463 : Blo 1566981 232132463 := bstep (se 1 (by rfl) ⟨174099347, by rfl⟩ : syracuseStep 232132463 = 348198695) B348198695
theorem B10729115 : Blo 1566981 10729115 := bstep (se 1 (by rfl) ⟨8046836, by rfl⟩ : syracuseStep 10729115 = 16093673) B16093673
theorem B17864873 : Blo 1566981 17864873 := bstep (se 2 (by rfl) ⟨6699327, by rfl⟩ : syracuseStep 17864873 = 13398655) B13398655
theorem B4020791 : Blo 1566981 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B45202009 : Blo 1566981 45202009 := bstep (se 2 (by rfl) ⟨16950753, by rfl⟩ : syracuseStep 45202009 = 33901507) B33901507
theorem B2645095 : Blo 1566981 2645095 := bstep (se 1 (by rfl) ⟨1983821, by rfl⟩ : syracuseStep 2645095 = 3967643) B3967643
theorem B60269345 : Blo 1566981 60269345 := bstep (se 2 (by rfl) ⟨22601004, by rfl⟩ : syracuseStep 60269345 = 45202009) B45202009
theorem B7152743 : Blo 1566981 7152743 := bstep (se 1 (by rfl) ⟨5364557, by rfl⟩ : syracuseStep 7152743 = 10729115) B10729115
theorem B3393947 : Blo 1566981 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B2976583 : Blo 1566981 2976583 := bstep (se 1 (by rfl) ⟨2232437, by rfl⟩ : syracuseStep 2976583 = 4464875) B4464875
theorem B1567775 : Blo 1566981 1567775 := bstep (se 1 (by rfl) ⟨1175831, by rfl⟩ : syracuseStep 1567775 = 2351663) B2351663
theorem B1567903 : Blo 1566981 1567903 := bstep (se 1 (by rfl) ⟨1175927, by rfl⟩ : syracuseStep 1567903 = 2351855) B2351855
theorem B42888437 : Blo 1566981 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B3526793 : Blo 1566981 3526793 := bstep (se 2 (by rfl) ⟨1322547, by rfl⟩ : syracuseStep 3526793 = 2645095) B2645095
theorem B16954217 : Blo 1566981 16954217 := bstep (se 2 (by rfl) ⟨6357831, by rfl⟩ : syracuseStep 16954217 = 12715663) B12715663
theorem B26777627 : Blo 1566981 26777627 := bstep (se 1 (by rfl) ⟨20083220, by rfl⟩ : syracuseStep 26777627 = 40166441) B40166441
theorem B11909915 : Blo 1566981 11909915 := bstep (se 1 (by rfl) ⟨8932436, by rfl⟩ : syracuseStep 11909915 = 17864873) B17864873
theorem B154754975 : Blo 1566981 154754975 := bstep (se 1 (by rfl) ⟨116066231, by rfl⟩ : syracuseStep 154754975 = 232132463) B232132463
theorem B2351195 : Blo 1566981 2351195 := bstep (se 1 (by rfl) ⟨1763396, by rfl⟩ : syracuseStep 2351195 = 3526793) B3526793
theorem B17851751 : Blo 1566981 17851751 := bstep (se 1 (by rfl) ⟨13388813, by rfl⟩ : syracuseStep 17851751 = 26777627) B26777627
theorem B7939943 : Blo 1566981 7939943 := bstep (se 1 (by rfl) ⟨5954957, by rfl⟩ : syracuseStep 7939943 = 11909915) B11909915
theorem B28592291 : Blo 1566981 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B19073981 : Blo 1566981 19073981 := bstep (se 3 (by rfl) ⟨3576371, by rfl⟩ : syracuseStep 19073981 = 7152743) B7152743
theorem B3968777 : Blo 1566981 3968777 := bstep (se 2 (by rfl) ⟨1488291, by rfl⟩ : syracuseStep 3968777 = 2976583) B2976583
theorem B40179563 : Blo 1566981 40179563 := bstep (se 1 (by rfl) ⟨30134672, by rfl⟩ : syracuseStep 40179563 = 60269345) B60269345
theorem B11302811 : Blo 1566981 11302811 := bstep (se 1 (by rfl) ⟨8477108, by rfl⟩ : syracuseStep 11302811 = 16954217) B16954217
theorem B9050525 : Blo 1566981 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B103169983 : Blo 1566981 103169983 := bstep (se 1 (by rfl) ⟨77377487, by rfl⟩ : syracuseStep 103169983 = 154754975) B154754975
theorem B5293295 : Blo 1566981 5293295 := bstep (se 1 (by rfl) ⟨3969971, by rfl⟩ : syracuseStep 5293295 = 7939943) B7939943
theorem B1567463 : Blo 1566981 1567463 := bstep (se 1 (by rfl) ⟨1175597, by rfl⟩ : syracuseStep 1567463 = 2351195) B2351195
theorem B6033683 : Blo 1566981 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B11901167 : Blo 1566981 11901167 := bstep (se 1 (by rfl) ⟨8925875, by rfl⟩ : syracuseStep 11901167 = 17851751) B17851751
theorem B26786375 : Blo 1566981 26786375 := bstep (se 1 (by rfl) ⟨20089781, by rfl⟩ : syracuseStep 26786375 = 40179563) B40179563
theorem B7535207 : Blo 1566981 7535207 := bstep (se 1 (by rfl) ⟨5651405, by rfl⟩ : syracuseStep 7535207 = 11302811) B11302811
theorem B19061527 : Blo 1566981 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B50863949 : Blo 1566981 50863949 := bstep (se 3 (by rfl) ⟨9536990, by rfl⟩ : syracuseStep 50863949 = 19073981) B19073981
theorem B2645851 : Blo 1566981 2645851 := bstep (se 1 (by rfl) ⟨1984388, by rfl⟩ : syracuseStep 2645851 = 3968777) B3968777
theorem B137559977 : Blo 1566981 137559977 := bstep (se 2 (by rfl) ⟨51584991, by rfl⟩ : syracuseStep 137559977 = 103169983) B103169983
theorem B4022455 : Blo 1566981 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B5023471 : Blo 1566981 5023471 := bstep (se 1 (by rfl) ⟨3767603, by rfl⟩ : syracuseStep 5023471 = 7535207) B7535207
theorem B33909299 : Blo 1566981 33909299 := bstep (se 1 (by rfl) ⟨25431974, by rfl⟩ : syracuseStep 33909299 = 50863949) B50863949
theorem B25415369 : Blo 1566981 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B7934111 : Blo 1566981 7934111 := bstep (se 1 (by rfl) ⟨5950583, by rfl⟩ : syracuseStep 7934111 = 11901167) B11901167
theorem B3527801 : Blo 1566981 3527801 := bstep (se 2 (by rfl) ⟨1322925, by rfl⟩ : syracuseStep 3527801 = 2645851) B2645851
theorem B91706651 : Blo 1566981 91706651 := bstep (se 1 (by rfl) ⟨68779988, by rfl⟩ : syracuseStep 91706651 = 137559977) B137559977
theorem B3528863 : Blo 1566981 3528863 := bstep (se 1 (by rfl) ⟨2646647, by rfl⟩ : syracuseStep 3528863 = 5293295) B5293295
theorem B17857583 : Blo 1566981 17857583 := bstep (se 1 (by rfl) ⟨13393187, by rfl⟩ : syracuseStep 17857583 = 26786375) B26786375
theorem B2351867 : Blo 1566981 2351867 := bstep (se 1 (by rfl) ⟨1763900, by rfl⟩ : syracuseStep 2351867 = 3527801) B3527801
theorem B61137767 : Blo 1566981 61137767 := bstep (se 1 (by rfl) ⟨45853325, by rfl⟩ : syracuseStep 61137767 = 91706651) B91706651
theorem B2352575 : Blo 1566981 2352575 := bstep (se 1 (by rfl) ⟨1764431, by rfl⟩ : syracuseStep 2352575 = 3528863) B3528863
theorem B11905055 : Blo 1566981 11905055 := bstep (se 1 (by rfl) ⟨8928791, by rfl⟩ : syracuseStep 11905055 = 17857583) B17857583
theorem B16943579 : Blo 1566981 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B22606199 : Blo 1566981 22606199 := bstep (se 1 (by rfl) ⟨16954649, by rfl⟩ : syracuseStep 22606199 = 33909299) B33909299
theorem B6697961 : Blo 1566981 6697961 := bstep (se 2 (by rfl) ⟨2511735, by rfl⟩ : syracuseStep 6697961 = 5023471) B5023471
theorem B5289407 : Blo 1566981 5289407 := bstep (se 1 (by rfl) ⟨3967055, by rfl⟩ : syracuseStep 5289407 = 7934111) B7934111
theorem B5363273 : Blo 1566981 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B4465307 : Blo 1566981 4465307 := bstep (se 1 (by rfl) ⟨3348980, by rfl⟩ : syracuseStep 4465307 = 6697961) B6697961
theorem B1567911 : Blo 1566981 1567911 := bstep (se 1 (by rfl) ⟨1175933, by rfl⟩ : syracuseStep 1567911 = 2351867) B2351867
theorem B40758511 : Blo 1566981 40758511 := bstep (se 1 (by rfl) ⟨30568883, by rfl⟩ : syracuseStep 40758511 = 61137767) B61137767
theorem B3526271 : Blo 1566981 3526271 := bstep (se 1 (by rfl) ⟨2644703, by rfl⟩ : syracuseStep 3526271 = 5289407) B5289407
theorem B1568383 : Blo 1566981 1568383 := bstep (se 1 (by rfl) ⟨1176287, by rfl⟩ : syracuseStep 1568383 = 2352575) B2352575
theorem B3575515 : Blo 1566981 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B15070799 : Blo 1566981 15070799 := bstep (se 1 (by rfl) ⟨11303099, by rfl⟩ : syracuseStep 15070799 = 22606199) B22606199
theorem B7936703 : Blo 1566981 7936703 := bstep (se 1 (by rfl) ⟨5952527, by rfl⟩ : syracuseStep 7936703 = 11905055) B11905055
theorem B11295719 : Blo 1566981 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B7530479 : Blo 1566981 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B10047199 : Blo 1566981 10047199 := bstep (se 1 (by rfl) ⟨7535399, by rfl⟩ : syracuseStep 10047199 = 15070799) B15070799
theorem B11907485 : Blo 1566981 11907485 := bstep (se 3 (by rfl) ⟨2232653, by rfl⟩ : syracuseStep 11907485 = 4465307) B4465307
theorem B54344681 : Blo 1566981 54344681 := bstep (se 2 (by rfl) ⟨20379255, by rfl⟩ : syracuseStep 54344681 = 40758511) B40758511
theorem B5291135 : Blo 1566981 5291135 := bstep (se 1 (by rfl) ⟨3968351, by rfl⟩ : syracuseStep 5291135 = 7936703) B7936703
theorem B4767353 : Blo 1566981 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B2350847 : Blo 1566981 2350847 := bstep (se 1 (by rfl) ⟨1763135, by rfl⟩ : syracuseStep 2350847 = 3526271) B3526271
theorem B7938323 : Blo 1566981 7938323 := bstep (se 1 (by rfl) ⟨5953742, by rfl⟩ : syracuseStep 7938323 = 11907485) B11907485
theorem B13396265 : Blo 1566981 13396265 := bstep (se 2 (by rfl) ⟨5023599, by rfl⟩ : syracuseStep 13396265 = 10047199) B10047199
theorem B1567231 : Blo 1566981 1567231 := bstep (se 1 (by rfl) ⟨1175423, by rfl⟩ : syracuseStep 1567231 = 2350847) B2350847
theorem B36229787 : Blo 1566981 36229787 := bstep (se 1 (by rfl) ⟨27172340, by rfl⟩ : syracuseStep 36229787 = 54344681) B54344681
theorem B3527423 : Blo 1566981 3527423 := bstep (se 1 (by rfl) ⟨2645567, by rfl⟩ : syracuseStep 3527423 = 5291135) B5291135
theorem B5020319 : Blo 1566981 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B3178235 : Blo 1566981 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B5292215 : Blo 1566981 5292215 := bstep (se 1 (by rfl) ⟨3969161, by rfl⟩ : syracuseStep 5292215 = 7938323) B7938323
theorem B2351615 : Blo 1566981 2351615 := bstep (se 1 (by rfl) ⟨1763711, by rfl⟩ : syracuseStep 2351615 = 3527423) B3527423
theorem B8930843 : Blo 1566981 8930843 := bstep (se 1 (by rfl) ⟨6698132, by rfl⟩ : syracuseStep 8930843 = 13396265) B13396265
theorem B13387517 : Blo 1566981 13387517 := bstep (se 3 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 13387517 = 5020319) B5020319
theorem B24153191 : Blo 1566981 24153191 := bstep (se 1 (by rfl) ⟨18114893, by rfl⟩ : syracuseStep 24153191 = 36229787) B36229787
theorem B8475293 : Blo 1566981 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B1567743 : Blo 1566981 1567743 := bstep (se 1 (by rfl) ⟨1175807, by rfl⟩ : syracuseStep 1567743 = 2351615) B2351615
theorem B8925011 : Blo 1566981 8925011 := bstep (se 1 (by rfl) ⟨6693758, by rfl⟩ : syracuseStep 8925011 = 13387517) B13387517
theorem B16102127 : Blo 1566981 16102127 := bstep (se 1 (by rfl) ⟨12076595, by rfl⟩ : syracuseStep 16102127 = 24153191) B24153191
theorem B3528143 : Blo 1566981 3528143 := bstep (se 1 (by rfl) ⟨2646107, by rfl⟩ : syracuseStep 3528143 = 5292215) B5292215
theorem B5650195 : Blo 1566981 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B5953895 : Blo 1566981 5953895 := bstep (se 1 (by rfl) ⟨4465421, by rfl⟩ : syracuseStep 5953895 = 8930843) B8930843
theorem B2352095 : Blo 1566981 2352095 := bstep (se 1 (by rfl) ⟨1764071, by rfl⟩ : syracuseStep 2352095 = 3528143) B3528143
theorem B5950007 : Blo 1566981 5950007 := bstep (se 1 (by rfl) ⟨4462505, by rfl⟩ : syracuseStep 5950007 = 8925011) B8925011
theorem B10734751 : Blo 1566981 10734751 := bstep (se 1 (by rfl) ⟨8051063, by rfl⟩ : syracuseStep 10734751 = 16102127) B16102127
theorem B3969263 : Blo 1566981 3969263 := bstep (se 1 (by rfl) ⟨2976947, by rfl⟩ : syracuseStep 3969263 = 5953895) B5953895
theorem B7533593 : Blo 1566981 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B2646175 : Blo 1566981 2646175 := bstep (se 1 (by rfl) ⟨1984631, by rfl⟩ : syracuseStep 2646175 = 3969263) B3969263
theorem B5022395 : Blo 1566981 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B3966671 : Blo 1566981 3966671 := bstep (se 1 (by rfl) ⟨2975003, by rfl⟩ : syracuseStep 3966671 = 5950007) B5950007
theorem B1568063 : Blo 1566981 1568063 := bstep (se 1 (by rfl) ⟨1176047, by rfl⟩ : syracuseStep 1568063 = 2352095) B2352095
theorem B57252005 : Blo 1566981 57252005 := bstep (se 4 (by rfl) ⟨5367375, by rfl⟩ : syracuseStep 57252005 = 10734751) B10734751
theorem B38168003 : Blo 1566981 38168003 := bstep (se 1 (by rfl) ⟨28626002, by rfl⟩ : syracuseStep 38168003 = 57252005) B57252005
theorem B3528233 : Blo 1566981 3528233 := bstep (se 2 (by rfl) ⟨1323087, by rfl⟩ : syracuseStep 3528233 = 2646175) B2646175
theorem B3348263 : Blo 1566981 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B2644447 : Blo 1566981 2644447 := bstep (se 1 (by rfl) ⟨1983335, by rfl⟩ : syracuseStep 2644447 = 3966671) B3966671
theorem B25445335 : Blo 1566981 25445335 := bstep (se 1 (by rfl) ⟨19084001, by rfl⟩ : syracuseStep 25445335 = 38168003) B38168003
theorem B2352155 : Blo 1566981 2352155 := bstep (se 1 (by rfl) ⟨1764116, by rfl⟩ : syracuseStep 2352155 = 3528233) B3528233
theorem B3525929 : Blo 1566981 3525929 := bstep (se 2 (by rfl) ⟨1322223, by rfl⟩ : syracuseStep 3525929 = 2644447) B2644447
theorem B8928701 : Blo 1566981 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B1568103 : Blo 1566981 1568103 := bstep (se 1 (by rfl) ⟨1176077, by rfl⟩ : syracuseStep 1568103 = 2352155) B2352155
theorem B33927113 : Blo 1566981 33927113 := bstep (se 2 (by rfl) ⟨12722667, by rfl⟩ : syracuseStep 33927113 = 25445335) B25445335
theorem B5952467 : Blo 1566981 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B2350619 : Blo 1566981 2350619 := bstep (se 1 (by rfl) ⟨1762964, by rfl⟩ : syracuseStep 2350619 = 3525929) B3525929
theorem B1567079 : Blo 1566981 1567079 := bstep (se 1 (by rfl) ⟨1175309, by rfl⟩ : syracuseStep 1567079 = 2350619) B2350619
theorem B3968311 : Blo 1566981 3968311 := bstep (se 1 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 3968311 = 5952467) B5952467
theorem B22618075 : Blo 1566981 22618075 := bstep (se 1 (by rfl) ⟨16963556, by rfl⟩ : syracuseStep 22618075 = 33927113) B33927113
theorem B30157433 : Blo 1566981 30157433 := bstep (se 2 (by rfl) ⟨11309037, by rfl⟩ : syracuseStep 30157433 = 22618075) B22618075
theorem B5291081 : Blo 1566981 5291081 := bstep (se 2 (by rfl) ⟨1984155, by rfl⟩ : syracuseStep 5291081 = 3968311) B3968311
theorem B20104955 : Blo 1566981 20104955 := bstep (se 1 (by rfl) ⟨15078716, by rfl⟩ : syracuseStep 20104955 = 30157433) B30157433
theorem B3527387 : Blo 1566981 3527387 := bstep (se 1 (by rfl) ⟨2645540, by rfl⟩ : syracuseStep 3527387 = 5291081) B5291081
theorem B2351591 : Blo 1566981 2351591 := bstep (se 1 (by rfl) ⟨1763693, by rfl⟩ : syracuseStep 2351591 = 3527387) B3527387
theorem B13403303 : Blo 1566981 13403303 := bstep (se 1 (by rfl) ⟨10052477, by rfl⟩ : syracuseStep 13403303 = 20104955) B20104955
theorem B1567727 : Blo 1566981 1567727 := bstep (se 1 (by rfl) ⟨1175795, by rfl⟩ : syracuseStep 1567727 = 2351591) B2351591
theorem B8935535 : Blo 1566981 8935535 := bstep (se 1 (by rfl) ⟨6701651, by rfl⟩ : syracuseStep 8935535 = 13403303) B13403303
theorem B5957023 : Blo 1566981 5957023 := bstep (se 1 (by rfl) ⟨4467767, by rfl⟩ : syracuseStep 5957023 = 8935535) B8935535
theorem B7942697 : Blo 1566981 7942697 := bstep (se 2 (by rfl) ⟨2978511, by rfl⟩ : syracuseStep 7942697 = 5957023) B5957023
theorem B5295131 : Blo 1566981 5295131 := bstep (se 1 (by rfl) ⟨3971348, by rfl⟩ : syracuseStep 5295131 = 7942697) B7942697
theorem B3530087 : Blo 1566981 3530087 := bstep (se 1 (by rfl) ⟨2647565, by rfl⟩ : syracuseStep 3530087 = 5295131) B5295131
theorem B2353391 : Blo 1566981 2353391 := bstep (se 1 (by rfl) ⟨1765043, by rfl⟩ : syracuseStep 2353391 = 3530087) B3530087
theorem B1568927 : Blo 1566981 1568927 := bstep (se 1 (by rfl) ⟨1176695, by rfl⟩ : syracuseStep 1568927 = 2353391) B2353391

theorem C0 (j : ℕ) (h1 : 391745 ≤ j) (h2 : j ≤ 392244) : Blo 1566981 (4 * j + 3) := by
  interval_cases j
  · exact B1566983
  · exact B1566987
  · exact B1566991
  · exact B1566995
  · exact B1566999
  · exact B1567003
  · exact B1567007
  · exact B1567011
  · exact B1567015
  · exact B1567019
  · exact B1567023
  · exact B1567027
  · exact B1567031
  · exact B1567035
  · exact B1567039
  · exact B1567043
  · exact B1567047
  · exact B1567051
  · exact B1567055
  · exact B1567059
  · exact B1567063
  · exact B1567067
  · exact B1567071
  · exact B1567075
  · exact B1567079
  · exact B1567083
  · exact B1567087
  · exact B1567091
  · exact B1567095
  · exact B1567099
  · exact B1567103
  · exact B1567107
  · exact B1567111
  · exact B1567115
  · exact B1567119
  · exact B1567123
  · exact B1567127
  · exact B1567131
  · exact B1567135
  · exact B1567139
  · exact B1567143
  · exact B1567147
  · exact B1567151
  · exact B1567155
  · exact B1567159
  · exact B1567163
  · exact B1567167
  · exact B1567171
  · exact B1567175
  · exact B1567179
  · exact B1567183
  · exact B1567187
  · exact B1567191
  · exact B1567195
  · exact B1567199
  · exact B1567203
  · exact B1567207
  · exact B1567211
  · exact B1567215
  · exact B1567219
  · exact B1567223
  · exact B1567227
  · exact B1567231
  · exact B1567235
  · exact B1567239
  · exact B1567243
  · exact B1567247
  · exact B1567251
  · exact B1567255
  · exact B1567259
  · exact B1567263
  · exact B1567267
  · exact B1567271
  · exact B1567275
  · exact B1567279
  · exact B1567283
  · exact B1567287
  · exact B1567291
  · exact B1567295
  · exact B1567299
  · exact B1567303
  · exact B1567307
  · exact B1567311
  · exact B1567315
  · exact B1567319
  · exact B1567323
  · exact B1567327
  · exact B1567331
  · exact B1567335
  · exact B1567339
  · exact B1567343
  · exact B1567347
  · exact B1567351
  · exact B1567355
  · exact B1567359
  · exact B1567363
  · exact B1567367
  · exact B1567371
  · exact B1567375
  · exact B1567379
  · exact B1567383
  · exact B1567387
  · exact B1567391
  · exact B1567395
  · exact B1567399
  · exact B1567403
  · exact B1567407
  · exact B1567411
  · exact B1567415
  · exact B1567419
  · exact B1567423
  · exact B1567427
  · exact B1567431
  · exact B1567435
  · exact B1567439
  · exact B1567443
  · exact B1567447
  · exact B1567451
  · exact B1567455
  · exact B1567459
  · exact B1567463
  · exact B1567467
  · exact B1567471
  · exact B1567475
  · exact B1567479
  · exact B1567483
  · exact B1567487
  · exact B1567491
  · exact B1567495
  · exact B1567499
  · exact B1567503
  · exact B1567507
  · exact B1567511
  · exact B1567515
  · exact B1567519
  · exact B1567523
  · exact B1567527
  · exact B1567531
  · exact B1567535
  · exact B1567539
  · exact B1567543
  · exact B1567547
  · exact B1567551
  · exact B1567555
  · exact B1567559
  · exact B1567563
  · exact B1567567
  · exact B1567571
  · exact B1567575
  · exact B1567579
  · exact B1567583
  · exact B1567587
  · exact B1567591
  · exact B1567595
  · exact B1567599
  · exact B1567603
  · exact B1567607
  · exact B1567611
  · exact B1567615
  · exact B1567619
  · exact B1567623
  · exact B1567627
  · exact B1567631
  · exact B1567635
  · exact B1567639
  · exact B1567643
  · exact B1567647
  · exact B1567651
  · exact B1567655
  · exact B1567659
  · exact B1567663
  · exact B1567667
  · exact B1567671
  · exact B1567675
  · exact B1567679
  · exact B1567683
  · exact B1567687
  · exact B1567691
  · exact B1567695
  · exact B1567699
  · exact B1567703
  · exact B1567707
  · exact B1567711
  · exact B1567715
  · exact B1567719
  · exact B1567723
  · exact B1567727
  · exact B1567731
  · exact B1567735
  · exact B1567739
  · exact B1567743
  · exact B1567747
  · exact B1567751
  · exact B1567755
  · exact B1567759
  · exact B1567763
  · exact B1567767
  · exact B1567771
  · exact B1567775
  · exact B1567779
  · exact B1567783
  · exact B1567787
  · exact B1567791
  · exact B1567795
  · exact B1567799
  · exact B1567803
  · exact B1567807
  · exact B1567811
  · exact B1567815
  · exact B1567819
  · exact B1567823
  · exact B1567827
  · exact B1567831
  · exact B1567835
  · exact B1567839
  · exact B1567843
  · exact B1567847
  · exact B1567851
  · exact B1567855
  · exact B1567859
  · exact B1567863
  · exact B1567867
  · exact B1567871
  · exact B1567875
  · exact B1567879
  · exact B1567883
  · exact B1567887
  · exact B1567891
  · exact B1567895
  · exact B1567899
  · exact B1567903
  · exact B1567907
  · exact B1567911
  · exact B1567915
  · exact B1567919
  · exact B1567923
  · exact B1567927
  · exact B1567931
  · exact B1567935
  · exact B1567939
  · exact B1567943
  · exact B1567947
  · exact B1567951
  · exact B1567955
  · exact B1567959
  · exact B1567963
  · exact B1567967
  · exact B1567971
  · exact B1567975
  · exact B1567979
  · exact B1567983
  · exact B1567987
  · exact B1567991
  · exact B1567995
  · exact B1567999
  · exact B1568003
  · exact B1568007
  · exact B1568011
  · exact B1568015
  · exact B1568019
  · exact B1568023
  · exact B1568027
  · exact B1568031
  · exact B1568035
  · exact B1568039
  · exact B1568043
  · exact B1568047
  · exact B1568051
  · exact B1568055
  · exact B1568059
  · exact B1568063
  · exact B1568067
  · exact B1568071
  · exact B1568075
  · exact B1568079
  · exact B1568083
  · exact B1568087
  · exact B1568091
  · exact B1568095
  · exact B1568099
  · exact B1568103
  · exact B1568107
  · exact B1568111
  · exact B1568115
  · exact B1568119
  · exact B1568123
  · exact B1568127
  · exact B1568131
  · exact B1568135
  · exact B1568139
  · exact B1568143
  · exact B1568147
  · exact B1568151
  · exact B1568155
  · exact B1568159
  · exact B1568163
  · exact B1568167
  · exact B1568171
  · exact B1568175
  · exact B1568179
  · exact B1568183
  · exact B1568187
  · exact B1568191
  · exact B1568195
  · exact B1568199
  · exact B1568203
  · exact B1568207
  · exact B1568211
  · exact B1568215
  · exact B1568219
  · exact B1568223
  · exact B1568227
  · exact B1568231
  · exact B1568235
  · exact B1568239
  · exact B1568243
  · exact B1568247
  · exact B1568251
  · exact B1568255
  · exact B1568259
  · exact B1568263
  · exact B1568267
  · exact B1568271
  · exact B1568275
  · exact B1568279
  · exact B1568283
  · exact B1568287
  · exact B1568291
  · exact B1568295
  · exact B1568299
  · exact B1568303
  · exact B1568307
  · exact B1568311
  · exact B1568315
  · exact B1568319
  · exact B1568323
  · exact B1568327
  · exact B1568331
  · exact B1568335
  · exact B1568339
  · exact B1568343
  · exact B1568347
  · exact B1568351
  · exact B1568355
  · exact B1568359
  · exact B1568363
  · exact B1568367
  · exact B1568371
  · exact B1568375
  · exact B1568379
  · exact B1568383
  · exact B1568387
  · exact B1568391
  · exact B1568395
  · exact B1568399
  · exact B1568403
  · exact B1568407
  · exact B1568411
  · exact B1568415
  · exact B1568419
  · exact B1568423
  · exact B1568427
  · exact B1568431
  · exact B1568435
  · exact B1568439
  · exact B1568443
  · exact B1568447
  · exact B1568451
  · exact B1568455
  · exact B1568459
  · exact B1568463
  · exact B1568467
  · exact B1568471
  · exact B1568475
  · exact B1568479
  · exact B1568483
  · exact B1568487
  · exact B1568491
  · exact B1568495
  · exact B1568499
  · exact B1568503
  · exact B1568507
  · exact B1568511
  · exact B1568515
  · exact B1568519
  · exact B1568523
  · exact B1568527
  · exact B1568531
  · exact B1568535
  · exact B1568539
  · exact B1568543
  · exact B1568547
  · exact B1568551
  · exact B1568555
  · exact B1568559
  · exact B1568563
  · exact B1568567
  · exact B1568571
  · exact B1568575
  · exact B1568579
  · exact B1568583
  · exact B1568587
  · exact B1568591
  · exact B1568595
  · exact B1568599
  · exact B1568603
  · exact B1568607
  · exact B1568611
  · exact B1568615
  · exact B1568619
  · exact B1568623
  · exact B1568627
  · exact B1568631
  · exact B1568635
  · exact B1568639
  · exact B1568643
  · exact B1568647
  · exact B1568651
  · exact B1568655
  · exact B1568659
  · exact B1568663
  · exact B1568667
  · exact B1568671
  · exact B1568675
  · exact B1568679
  · exact B1568683
  · exact B1568687
  · exact B1568691
  · exact B1568695
  · exact B1568699
  · exact B1568703
  · exact B1568707
  · exact B1568711
  · exact B1568715
  · exact B1568719
  · exact B1568723
  · exact B1568727
  · exact B1568731
  · exact B1568735
  · exact B1568739
  · exact B1568743
  · exact B1568747
  · exact B1568751
  · exact B1568755
  · exact B1568759
  · exact B1568763
  · exact B1568767
  · exact B1568771
  · exact B1568775
  · exact B1568779
  · exact B1568783
  · exact B1568787
  · exact B1568791
  · exact B1568795
  · exact B1568799
  · exact B1568803
  · exact B1568807
  · exact B1568811
  · exact B1568815
  · exact B1568819
  · exact B1568823
  · exact B1568827
  · exact B1568831
  · exact B1568835
  · exact B1568839
  · exact B1568843
  · exact B1568847
  · exact B1568851
  · exact B1568855
  · exact B1568859
  · exact B1568863
  · exact B1568867
  · exact B1568871
  · exact B1568875
  · exact B1568879
  · exact B1568883
  · exact B1568887
  · exact B1568891
  · exact B1568895
  · exact B1568899
  · exact B1568903
  · exact B1568907
  · exact B1568911
  · exact B1568915
  · exact B1568919
  · exact B1568923
  · exact B1568927
  · exact B1568931
  · exact B1568935
  · exact B1568939
  · exact B1568943
  · exact B1568947
  · exact B1568951
  · exact B1568955
  · exact B1568959
  · exact B1568963
  · exact B1568967
  · exact B1568971
  · exact B1568975
  · exact B1568979

theorem solution (m : ℕ) (hlo : 1566981 ≤ m) (hhi : m ≤ 1568981) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 391745 ≤ j := by omega
    have hj2 : j ≤ 392244 := by omega
    have hb : Blo 1566981 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
