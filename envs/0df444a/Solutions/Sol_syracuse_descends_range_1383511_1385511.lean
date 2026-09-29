-- Prove2me | solution 1 for syracuse_descends_range_1383511_1385511
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:25.051027+00:00
-- url     : https://prove2.me/submissions/3855bf9a-eabd-49af-86d8-8a68c70e35f1

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


theorem B1753093 : Blo 1383511 1753093 := bbase (se 4 (by rfl) ⟨164352, by rfl⟩ : syracuseStep 1753093 = 328705) (by norm_num)
theorem B3112973 : Blo 1383511 3112973 := bbase (se 3 (by rfl) ⟨583682, by rfl⟩ : syracuseStep 3112973 = 1167365) (by norm_num)
theorem B1556509 : Blo 1383511 1556509 := bbase (se 3 (by rfl) ⟨291845, by rfl⟩ : syracuseStep 1556509 = 583691) (by norm_num)
theorem B2334757 : Blo 1383511 2334757 := bbase (se 4 (by rfl) ⟨218883, by rfl⟩ : syracuseStep 2334757 = 437767) (by norm_num)
theorem B2629685 : Blo 1383511 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B3506237 : Blo 1383511 3506237 := bbase (se 3 (by rfl) ⟨657419, by rfl⟩ : syracuseStep 3506237 = 1314839) (by norm_num)
theorem B1556545 : Blo 1383511 1556545 := bbase (se 2 (by rfl) ⟨583704, by rfl⟩ : syracuseStep 1556545 = 1167409) (by norm_num)
theorem B3113045 : Blo 1383511 3113045 := bbase (se 8 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 3113045 = 36481) (by norm_num)
theorem B4669541 : Blo 1383511 4669541 := bbase (se 4 (by rfl) ⟨437769, by rfl⟩ : syracuseStep 4669541 = 875539) (by norm_num)
theorem B2662501 : Blo 1383511 2662501 := bbase (se 4 (by rfl) ⟨249609, by rfl⟩ : syracuseStep 2662501 = 499219) (by norm_num)
theorem B1556581 : Blo 1383511 1556581 := bbase (se 4 (by rfl) ⟨145929, by rfl⟩ : syracuseStep 1556581 = 291859) (by norm_num)
theorem B2334845 : Blo 1383511 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B1556617 : Blo 1383511 1556617 := bbase (se 2 (by rfl) ⟨583731, by rfl⟩ : syracuseStep 1556617 = 1167463) (by norm_num)
theorem B17744021 : Blo 1383511 17744021 := bbase (se 6 (by rfl) ⟨415875, by rfl⟩ : syracuseStep 17744021 = 831751) (by norm_num)
theorem B3113117 : Blo 1383511 3113117 := bbase (se 3 (by rfl) ⟨583709, by rfl⟩ : syracuseStep 3113117 = 1167419) (by norm_num)
theorem B1556653 : Blo 1383511 1556653 := bbase (se 3 (by rfl) ⟨291872, by rfl⟩ : syracuseStep 1556653 = 583745) (by norm_num)
theorem B1753265 : Blo 1383511 1753265 := bbase (se 2 (by rfl) ⟨657474, by rfl⟩ : syracuseStep 1753265 = 1314949) (by norm_num)
theorem B2629837 : Blo 1383511 2629837 := bbase (se 3 (by rfl) ⟨493094, by rfl⟩ : syracuseStep 2629837 = 986189) (by norm_num)
theorem B1556689 : Blo 1383511 1556689 := bbase (se 2 (by rfl) ⟨583758, by rfl⟩ : syracuseStep 1556689 = 1167517) (by norm_num)
theorem B3113189 : Blo 1383511 3113189 := bbase (se 4 (by rfl) ⟨291861, by rfl⟩ : syracuseStep 3113189 = 583723) (by norm_num)
theorem B1753321 : Blo 1383511 1753321 := bbase (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) (by norm_num)
theorem B1556725 : Blo 1383511 1556725 := bbase (se 5 (by rfl) ⟨72971, by rfl⟩ : syracuseStep 1556725 = 145943) (by norm_num)
theorem B3326197 : Blo 1383511 3326197 := bbase (se 5 (by rfl) ⟨155915, by rfl⟩ : syracuseStep 3326197 = 311831) (by norm_num)
theorem B2334973 : Blo 1383511 2334973 := bbase (se 3 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 2334973 = 875615) (by norm_num)
theorem B3506429 : Blo 1383511 3506429 := bbase (se 3 (by rfl) ⟨657455, by rfl⟩ : syracuseStep 3506429 = 1314911) (by norm_num)
theorem B1556761 : Blo 1383511 1556761 := bbase (se 2 (by rfl) ⟨583785, by rfl⟩ : syracuseStep 1556761 = 1167571) (by norm_num)
theorem B3113261 : Blo 1383511 3113261 := bbase (se 3 (by rfl) ⟨583736, by rfl⟩ : syracuseStep 3113261 = 1167473) (by norm_num)
theorem B1556797 : Blo 1383511 1556797 := bbase (se 3 (by rfl) ⟨291899, by rfl⟩ : syracuseStep 1556797 = 583799) (by norm_num)
theorem B1663301 : Blo 1383511 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B1753417 : Blo 1383511 1753417 := bbase (se 2 (by rfl) ⟨657531, by rfl⟩ : syracuseStep 1753417 = 1315063) (by norm_num)
theorem B2335061 : Blo 1383511 2335061 := bbase (se 10 (by rfl) ⟨3420, by rfl⟩ : syracuseStep 2335061 = 6841) (by norm_num)
theorem B1556833 : Blo 1383511 1556833 := bbase (se 2 (by rfl) ⟨583812, by rfl⟩ : syracuseStep 1556833 = 1167625) (by norm_num)
theorem B3113333 : Blo 1383511 3113333 := bbase (se 5 (by rfl) ⟨145937, by rfl⟩ : syracuseStep 3113333 = 291875) (by norm_num)
theorem B1556869 : Blo 1383511 1556869 := bbase (se 4 (by rfl) ⟨145956, by rfl⟩ : syracuseStep 1556869 = 291913) (by norm_num)
theorem B1556905 : Blo 1383511 1556905 := bbase (se 2 (by rfl) ⟨583839, by rfl⟩ : syracuseStep 1556905 = 1167679) (by norm_num)
theorem B3113405 : Blo 1383511 3113405 := bbase (se 3 (by rfl) ⟨583763, by rfl⟩ : syracuseStep 3113405 = 1167527) (by norm_num)
theorem B1556941 : Blo 1383511 1556941 := bbase (se 3 (by rfl) ⟨291926, by rfl⟩ : syracuseStep 1556941 = 583853) (by norm_num)
theorem B2335189 : Blo 1383511 2335189 := bbase (se 7 (by rfl) ⟨27365, by rfl⟩ : syracuseStep 2335189 = 54731) (by norm_num)
theorem B23658965 : Blo 1383511 23658965 := bbase (se 7 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 23658965 = 554507) (by norm_num)
theorem B1556977 : Blo 1383511 1556977 := bbase (se 2 (by rfl) ⟨583866, by rfl⟩ : syracuseStep 1556977 = 1167733) (by norm_num)
theorem B2630141 : Blo 1383511 2630141 := bbase (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) (by norm_num)
theorem B3113477 : Blo 1383511 3113477 := bbase (se 4 (by rfl) ⟨291888, by rfl⟩ : syracuseStep 3113477 = 583777) (by norm_num)
theorem B4669973 : Blo 1383511 4669973 := bbase (se 6 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 4669973 = 218905) (by norm_num)
theorem B1557013 : Blo 1383511 1557013 := bbase (se 6 (by rfl) ⟨36492, by rfl⟩ : syracuseStep 1557013 = 72985) (by norm_num)
theorem B2335277 : Blo 1383511 2335277 := bbase (se 3 (by rfl) ⟨437864, by rfl⟩ : syracuseStep 2335277 = 875729) (by norm_num)
theorem B1557049 : Blo 1383511 1557049 := bbase (se 2 (by rfl) ⟨583893, by rfl⟩ : syracuseStep 1557049 = 1167787) (by norm_num)
theorem B3113549 : Blo 1383511 3113549 := bbase (se 3 (by rfl) ⟨583790, by rfl⟩ : syracuseStep 3113549 = 1167581) (by norm_num)
theorem B3506773 : Blo 1383511 3506773 := bbase (se 8 (by rfl) ⟨20547, by rfl⟩ : syracuseStep 3506773 = 41095) (by norm_num)
theorem B2024029 : Blo 1383511 2024029 := bbase (se 3 (by rfl) ⟨379505, by rfl⟩ : syracuseStep 2024029 = 759011) (by norm_num)
theorem B1557085 : Blo 1383511 1557085 := bbase (se 3 (by rfl) ⟨291953, by rfl⟩ : syracuseStep 1557085 = 583907) (by norm_num)
theorem B7103077 : Blo 1383511 7103077 := bbase (se 4 (by rfl) ⟨665913, by rfl⟩ : syracuseStep 7103077 = 1331827) (by norm_num)
theorem B4498037 : Blo 1383511 4498037 := bbase (se 5 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 4498037 = 421691) (by norm_num)
theorem B1557121 : Blo 1383511 1557121 := bbase (se 2 (by rfl) ⟨583920, by rfl⟩ : syracuseStep 1557121 = 1167841) (by norm_num)
theorem B3113621 : Blo 1383511 3113621 := bbase (se 6 (by rfl) ⟨72975, by rfl⟩ : syracuseStep 3113621 = 145951) (by norm_num)
theorem B1557157 : Blo 1383511 1557157 := bbase (se 4 (by rfl) ⟨145983, by rfl⟩ : syracuseStep 1557157 = 291967) (by norm_num)
theorem B2335405 : Blo 1383511 2335405 := bbase (se 3 (by rfl) ⟨437888, by rfl⟩ : syracuseStep 2335405 = 875777) (by norm_num)
theorem B3506885 : Blo 1383511 3506885 := bbase (se 4 (by rfl) ⟨328770, by rfl⟩ : syracuseStep 3506885 = 657541) (by norm_num)
theorem B1557193 : Blo 1383511 1557193 := bbase (se 2 (by rfl) ⟨583947, by rfl⟩ : syracuseStep 1557193 = 1167895) (by norm_num)
theorem B3113693 : Blo 1383511 3113693 := bbase (se 3 (by rfl) ⟨583817, by rfl⟩ : syracuseStep 3113693 = 1167635) (by norm_num)
theorem B1557229 : Blo 1383511 1557229 := bbase (se 3 (by rfl) ⟨291980, by rfl⟩ : syracuseStep 1557229 = 583961) (by norm_num)
theorem B2335493 : Blo 1383511 2335493 := bbase (se 4 (by rfl) ⟨218952, by rfl⟩ : syracuseStep 2335493 = 437905) (by norm_num)
theorem B1557265 : Blo 1383511 1557265 := bbase (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) (by norm_num)
theorem B7013141 : Blo 1383511 7013141 := bbase (se 6 (by rfl) ⟨164370, by rfl⟩ : syracuseStep 7013141 = 328741) (by norm_num)
theorem B3113765 : Blo 1383511 3113765 := bbase (se 4 (by rfl) ⟨291915, by rfl⟩ : syracuseStep 3113765 = 583831) (by norm_num)
theorem B1557301 : Blo 1383511 1557301 := bbase (se 5 (by rfl) ⟨72998, by rfl⟩ : syracuseStep 1557301 = 145997) (by norm_num)
theorem B5260085 : Blo 1383511 5260085 := bbase (se 5 (by rfl) ⟨246566, by rfl⟩ : syracuseStep 5260085 = 493133) (by norm_num)
theorem B2106173 : Blo 1383511 2106173 := bbase (se 3 (by rfl) ⟨394907, by rfl⟩ : syracuseStep 2106173 = 789815) (by norm_num)
theorem B2958157 : Blo 1383511 2958157 := bbase (se 3 (by rfl) ⟨554654, by rfl⟩ : syracuseStep 2958157 = 1109309) (by norm_num)
theorem B1557337 : Blo 1383511 1557337 := bbase (se 2 (by rfl) ⟨584001, by rfl⟩ : syracuseStep 1557337 = 1168003) (by norm_num)
theorem B3113837 : Blo 1383511 3113837 := bbase (se 3 (by rfl) ⟨583844, by rfl⟩ : syracuseStep 3113837 = 1167689) (by norm_num)
theorem B3941237 : Blo 1383511 3941237 := bbase (se 5 (by rfl) ⟨184745, by rfl⟩ : syracuseStep 3941237 = 369491) (by norm_num)
theorem B1557373 : Blo 1383511 1557373 := bbase (se 3 (by rfl) ⟨292007, by rfl⟩ : syracuseStep 1557373 = 584015) (by norm_num)
theorem B2335621 : Blo 1383511 2335621 := bbase (se 4 (by rfl) ⟨218964, by rfl⟩ : syracuseStep 2335621 = 437929) (by norm_num)
theorem B3507077 : Blo 1383511 3507077 := bbase (se 4 (by rfl) ⟨328788, by rfl⟩ : syracuseStep 3507077 = 657577) (by norm_num)
theorem B14214037 : Blo 1383511 14214037 := bbase (se 6 (by rfl) ⟨333141, by rfl⟩ : syracuseStep 14214037 = 666283) (by norm_num)
theorem B1557409 : Blo 1383511 1557409 := bbase (se 2 (by rfl) ⟨584028, by rfl⟩ : syracuseStep 1557409 = 1168057) (by norm_num)
theorem B3113909 : Blo 1383511 3113909 := bbase (se 5 (by rfl) ⟨145964, by rfl⟩ : syracuseStep 3113909 = 291929) (by norm_num)
theorem B4670405 : Blo 1383511 4670405 := bbase (se 4 (by rfl) ⟨437850, by rfl⟩ : syracuseStep 4670405 = 875701) (by norm_num)
theorem B1557445 : Blo 1383511 1557445 := bbase (se 4 (by rfl) ⟨146010, by rfl⟩ : syracuseStep 1557445 = 292021) (by norm_num)
theorem B2958277 : Blo 1383511 2958277 := bbase (se 4 (by rfl) ⟨277338, by rfl⟩ : syracuseStep 2958277 = 554677) (by norm_num)
theorem B2335709 : Blo 1383511 2335709 := bbase (se 3 (by rfl) ⟨437945, by rfl⟩ : syracuseStep 2335709 = 875891) (by norm_num)
theorem B1557481 : Blo 1383511 1557481 := bbase (se 2 (by rfl) ⟨584055, by rfl⟩ : syracuseStep 1557481 = 1168111) (by norm_num)
theorem B9470965 : Blo 1383511 9470965 := bbase (se 5 (by rfl) ⟨443951, by rfl⟩ : syracuseStep 9470965 = 887903) (by norm_num)
theorem B3113981 : Blo 1383511 3113981 := bbase (se 3 (by rfl) ⟨583871, by rfl⟩ : syracuseStep 3113981 = 1167743) (by norm_num)
theorem B1557517 : Blo 1383511 1557517 := bbase (se 3 (by rfl) ⟨292034, by rfl⟩ : syracuseStep 1557517 = 584069) (by norm_num)
theorem B1664021 : Blo 1383511 1664021 := bbase (se 6 (by rfl) ⟨39000, by rfl⟩ : syracuseStep 1664021 = 78001) (by norm_num)
theorem B1557553 : Blo 1383511 1557553 := bbase (se 2 (by rfl) ⟨584082, by rfl⟩ : syracuseStep 1557553 = 1168165) (by norm_num)
theorem B3114053 : Blo 1383511 3114053 := bbase (se 4 (by rfl) ⟨291942, by rfl⟩ : syracuseStep 3114053 = 583885) (by norm_num)
theorem B4432981 : Blo 1383511 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B1557589 : Blo 1383511 1557589 := bbase (se 8 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 1557589 = 18253) (by norm_num)
theorem B5260373 : Blo 1383511 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B2335837 : Blo 1383511 2335837 := bbase (se 3 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 2335837 = 875939) (by norm_num)
theorem B1557625 : Blo 1383511 1557625 := bbase (se 2 (by rfl) ⟨584109, by rfl⟩ : syracuseStep 1557625 = 1168219) (by norm_num)
theorem B3114125 : Blo 1383511 3114125 := bbase (se 3 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 3114125 = 1167797) (by norm_num)
theorem B1557661 : Blo 1383511 1557661 := bbase (se 3 (by rfl) ⟨292061, by rfl⟩ : syracuseStep 1557661 = 584123) (by norm_num)
theorem B7005365 : Blo 1383511 7005365 := bbase (se 5 (by rfl) ⟨328376, by rfl⟩ : syracuseStep 7005365 = 656753) (by norm_num)
theorem B2335925 : Blo 1383511 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B2368693 : Blo 1383511 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B1557697 : Blo 1383511 1557697 := bbase (se 2 (by rfl) ⟨584136, by rfl⟩ : syracuseStep 1557697 = 1168273) (by norm_num)
theorem B2958533 : Blo 1383511 2958533 := bbase (se 4 (by rfl) ⟨277362, by rfl⟩ : syracuseStep 2958533 = 554725) (by norm_num)
theorem B3114197 : Blo 1383511 3114197 := bbase (se 7 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 3114197 = 72989) (by norm_num)
theorem B1557733 : Blo 1383511 1557733 := bbase (se 4 (by rfl) ⟨146037, by rfl⟩ : syracuseStep 1557733 = 292075) (by norm_num)
theorem B5686517 : Blo 1383511 5686517 := bbase (se 5 (by rfl) ⟨266555, by rfl⟩ : syracuseStep 5686517 = 533111) (by norm_num)
theorem B1557769 : Blo 1383511 1557769 := bbase (se 2 (by rfl) ⟨584163, by rfl⟩ : syracuseStep 1557769 = 1168327) (by norm_num)
theorem B3114269 : Blo 1383511 3114269 := bbase (se 3 (by rfl) ⟨583925, by rfl⟩ : syracuseStep 3114269 = 1167851) (by norm_num)
theorem B1557805 : Blo 1383511 1557805 := bbase (se 3 (by rfl) ⟨292088, by rfl⟩ : syracuseStep 1557805 = 584177) (by norm_num)
theorem B2336053 : Blo 1383511 2336053 := bbase (se 5 (by rfl) ⟨109502, by rfl⟩ : syracuseStep 2336053 = 219005) (by norm_num)
theorem B3327293 : Blo 1383511 3327293 := bbase (se 3 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 3327293 = 1247735) (by norm_num)
theorem B1664329 : Blo 1383511 1664329 := bbase (se 2 (by rfl) ⟨624123, by rfl⟩ : syracuseStep 1664329 = 1248247) (by norm_num)
theorem B1557841 : Blo 1383511 1557841 := bbase (se 2 (by rfl) ⟨584190, by rfl⟩ : syracuseStep 1557841 = 1168381) (by norm_num)
theorem B3114341 : Blo 1383511 3114341 := bbase (se 4 (by rfl) ⟨291969, by rfl⟩ : syracuseStep 3114341 = 583939) (by norm_num)
theorem B4670837 : Blo 1383511 4670837 := bbase (se 5 (by rfl) ⟨218945, by rfl⟩ : syracuseStep 4670837 = 437891) (by norm_num)
theorem B1557877 : Blo 1383511 1557877 := bbase (se 5 (by rfl) ⟨73025, by rfl⟩ : syracuseStep 1557877 = 146051) (by norm_num)
theorem B2336141 : Blo 1383511 2336141 := bbase (se 3 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 2336141 = 876053) (by norm_num)
theorem B1557913 : Blo 1383511 1557913 := bbase (se 2 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 1557913 = 1168435) (by norm_num)
theorem B1664425 : Blo 1383511 1664425 := bbase (se 2 (by rfl) ⟨624159, by rfl⟩ : syracuseStep 1664425 = 1248319) (by norm_num)
theorem B3114413 : Blo 1383511 3114413 := bbase (se 3 (by rfl) ⟨583952, by rfl⟩ : syracuseStep 3114413 = 1167905) (by norm_num)
theorem B1557949 : Blo 1383511 1557949 := bbase (se 3 (by rfl) ⟨292115, by rfl⟩ : syracuseStep 1557949 = 584231) (by norm_num)
theorem B1557985 : Blo 1383511 1557985 := bbase (se 2 (by rfl) ⟨584244, by rfl⟩ : syracuseStep 1557985 = 1168489) (by norm_num)
theorem B3155429 : Blo 1383511 3155429 := bbase (se 4 (by rfl) ⟨295821, by rfl⟩ : syracuseStep 3155429 = 591643) (by norm_num)
theorem B3114485 : Blo 1383511 3114485 := bbase (se 5 (by rfl) ⟨145991, by rfl⟩ : syracuseStep 3114485 = 291983) (by norm_num)
theorem B1558021 : Blo 1383511 1558021 := bbase (se 4 (by rfl) ⟨146064, by rfl⟩ : syracuseStep 1558021 = 292129) (by norm_num)
theorem B2336269 : Blo 1383511 2336269 := bbase (se 3 (by rfl) ⟨438050, by rfl⟩ : syracuseStep 2336269 = 876101) (by norm_num)
theorem B3941909 : Blo 1383511 3941909 := bbase (se 6 (by rfl) ⟨92388, by rfl⟩ : syracuseStep 3941909 = 184777) (by norm_num)
theorem B1558057 : Blo 1383511 1558057 := bbase (se 2 (by rfl) ⟨584271, by rfl⟩ : syracuseStep 1558057 = 1168543) (by norm_num)
theorem B3114557 : Blo 1383511 3114557 := bbase (se 3 (by rfl) ⟨583979, by rfl⟩ : syracuseStep 3114557 = 1167959) (by norm_num)
theorem B1558093 : Blo 1383511 1558093 := bbase (se 3 (by rfl) ⟨292142, by rfl⟩ : syracuseStep 1558093 = 584285) (by norm_num)
theorem B3327581 : Blo 1383511 3327581 := bbase (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) (by norm_num)
theorem B2336357 : Blo 1383511 2336357 := bbase (se 4 (by rfl) ⟨219033, by rfl⟩ : syracuseStep 2336357 = 438067) (by norm_num)
theorem B1558129 : Blo 1383511 1558129 := bbase (se 2 (by rfl) ⟨584298, by rfl⟩ : syracuseStep 1558129 = 1168597) (by norm_num)
theorem B3114629 : Blo 1383511 3114629 := bbase (se 4 (by rfl) ⟨291996, by rfl⟩ : syracuseStep 3114629 = 583993) (by norm_num)
theorem B1558165 : Blo 1383511 1558165 := bbase (se 6 (by rfl) ⟨36519, by rfl⟩ : syracuseStep 1558165 = 73039) (by norm_num)
theorem B1558201 : Blo 1383511 1558201 := bbase (se 2 (by rfl) ⟨584325, by rfl⟩ : syracuseStep 1558201 = 1168651) (by norm_num)
theorem B3114701 : Blo 1383511 3114701 := bbase (se 3 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 3114701 = 1168013) (by norm_num)
theorem B1558237 : Blo 1383511 1558237 := bbase (se 3 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 1558237 = 584339) (by norm_num)
theorem B2336485 : Blo 1383511 2336485 := bbase (se 4 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 2336485 = 438091) (by norm_num)
theorem B1558273 : Blo 1383511 1558273 := bbase (se 2 (by rfl) ⟨584352, by rfl⟩ : syracuseStep 1558273 = 1168705) (by norm_num)
theorem B3114773 : Blo 1383511 3114773 := bbase (se 6 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 3114773 = 146005) (by norm_num)
theorem B4671269 : Blo 1383511 4671269 := bbase (se 4 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 4671269 = 875863) (by norm_num)
theorem B1558309 : Blo 1383511 1558309 := bbase (se 4 (by rfl) ⟨146091, by rfl⟩ : syracuseStep 1558309 = 292183) (by norm_num)
theorem B2336573 : Blo 1383511 2336573 := bbase (se 3 (by rfl) ⟨438107, by rfl⟩ : syracuseStep 2336573 = 876215) (by norm_num)
theorem B1558345 : Blo 1383511 1558345 := bbase (se 2 (by rfl) ⟨584379, by rfl⟩ : syracuseStep 1558345 = 1168759) (by norm_num)
theorem B3114845 : Blo 1383511 3114845 := bbase (se 3 (by rfl) ⟨584033, by rfl⟩ : syracuseStep 3114845 = 1168067) (by norm_num)
theorem B1558381 : Blo 1383511 1558381 := bbase (se 3 (by rfl) ⟨292196, by rfl⟩ : syracuseStep 1558381 = 584393) (by norm_num)
theorem B1558417 : Blo 1383511 1558417 := bbase (se 2 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 1558417 = 1168813) (by norm_num)
theorem B3114917 : Blo 1383511 3114917 := bbase (se 4 (by rfl) ⟨292023, by rfl⟩ : syracuseStep 3114917 = 584047) (by norm_num)
theorem B1558453 : Blo 1383511 1558453 := bbase (se 5 (by rfl) ⟨73052, by rfl⟩ : syracuseStep 1558453 = 146105) (by norm_num)
theorem B2336701 : Blo 1383511 2336701 := bbase (se 3 (by rfl) ⟨438131, by rfl⟩ : syracuseStep 2336701 = 876263) (by norm_num)
theorem B3942341 : Blo 1383511 3942341 := bbase (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) (by norm_num)
theorem B1558489 : Blo 1383511 1558489 := bbase (se 2 (by rfl) ⟨584433, by rfl⟩ : syracuseStep 1558489 = 1168867) (by norm_num)
theorem B3114989 : Blo 1383511 3114989 := bbase (se 3 (by rfl) ⟨584060, by rfl⟩ : syracuseStep 3114989 = 1168121) (by norm_num)
theorem B1558525 : Blo 1383511 1558525 := bbase (se 3 (by rfl) ⟨292223, by rfl⟩ : syracuseStep 1558525 = 584447) (by norm_num)
theorem B2336789 : Blo 1383511 2336789 := bbase (se 6 (by rfl) ⟨54768, by rfl⟩ : syracuseStep 2336789 = 109537) (by norm_num)
theorem B1558561 : Blo 1383511 1558561 := bbase (se 2 (by rfl) ⟨584460, by rfl⟩ : syracuseStep 1558561 = 1168921) (by norm_num)
theorem B11225141 : Blo 1383511 11225141 := bbase (se 5 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 11225141 = 1052357) (by norm_num)
theorem B3115061 : Blo 1383511 3115061 := bbase (se 5 (by rfl) ⟨146018, by rfl⟩ : syracuseStep 3115061 = 292037) (by norm_num)
theorem B5916725 : Blo 1383511 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B1558597 : Blo 1383511 1558597 := bbase (se 4 (by rfl) ⟨146118, by rfl⟩ : syracuseStep 1558597 = 292237) (by norm_num)
theorem B1558633 : Blo 1383511 1558633 := bbase (se 2 (by rfl) ⟨584487, by rfl⟩ : syracuseStep 1558633 = 1168975) (by norm_num)
theorem B3115133 : Blo 1383511 3115133 := bbase (se 3 (by rfl) ⟨584087, by rfl⟩ : syracuseStep 3115133 = 1168175) (by norm_num)
theorem B1558669 : Blo 1383511 1558669 := bbase (se 3 (by rfl) ⟨292250, by rfl⟩ : syracuseStep 1558669 = 584501) (by norm_num)
theorem B2336917 : Blo 1383511 2336917 := bbase (se 6 (by rfl) ⟨54771, by rfl⟩ : syracuseStep 2336917 = 109543) (by norm_num)
theorem B4991141 : Blo 1383511 4991141 := bbase (se 4 (by rfl) ⟨467919, by rfl⟩ : syracuseStep 4991141 = 935839) (by norm_num)
theorem B3115205 : Blo 1383511 3115205 := bbase (se 4 (by rfl) ⟨292050, by rfl⟩ : syracuseStep 3115205 = 584101) (by norm_num)
theorem B4671701 : Blo 1383511 4671701 := bbase (se 7 (by rfl) ⟨54746, by rfl⟩ : syracuseStep 4671701 = 109493) (by norm_num)
theorem B2337005 : Blo 1383511 2337005 := bbase (se 3 (by rfl) ⟨438188, by rfl⟩ : syracuseStep 2337005 = 876377) (by norm_num)
theorem B2369773 : Blo 1383511 2369773 := bbase (se 3 (by rfl) ⟨444332, by rfl⟩ : syracuseStep 2369773 = 888665) (by norm_num)
theorem B3115277 : Blo 1383511 3115277 := bbase (se 3 (by rfl) ⟨584114, by rfl⟩ : syracuseStep 3115277 = 1168229) (by norm_num)
theorem B3115349 : Blo 1383511 3115349 := bbase (se 10 (by rfl) ⟨4563, by rfl⟩ : syracuseStep 3115349 = 9127) (by norm_num)
theorem B2845037 : Blo 1383511 2845037 := bbase (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) (by norm_num)
theorem B2337133 : Blo 1383511 2337133 := bbase (se 3 (by rfl) ⟨438212, by rfl⟩ : syracuseStep 2337133 = 876425) (by norm_num)
theorem B11225461 : Blo 1383511 11225461 := bbase (se 5 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 11225461 = 1052387) (by norm_num)
theorem B3795349 : Blo 1383511 3795349 := bbase (se 6 (by rfl) ⟨88953, by rfl⟩ : syracuseStep 3795349 = 177907) (by norm_num)
theorem B3115421 : Blo 1383511 3115421 := bbase (se 3 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 3115421 = 1168283) (by norm_num)
theorem B7006661 : Blo 1383511 7006661 := bbase (se 4 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 7006661 = 1313749) (by norm_num)
theorem B4991429 : Blo 1383511 4991429 := bbase (se 4 (by rfl) ⟨467946, by rfl⟩ : syracuseStep 4991429 = 935893) (by norm_num)
theorem B2337221 : Blo 1383511 2337221 := bbase (se 4 (by rfl) ⟨219114, by rfl⟩ : syracuseStep 2337221 = 438229) (by norm_num)
theorem B3115493 : Blo 1383511 3115493 := bbase (se 4 (by rfl) ⟨292077, by rfl⟩ : syracuseStep 3115493 = 584155) (by norm_num)
theorem B1870381 : Blo 1383511 1870381 := bbase (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) (by norm_num)
theorem B3115565 : Blo 1383511 3115565 := bbase (se 3 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 3115565 = 1168337) (by norm_num)
theorem B2337349 : Blo 1383511 2337349 := bbase (se 4 (by rfl) ⟨219126, by rfl⟩ : syracuseStep 2337349 = 438253) (by norm_num)
theorem B3115637 : Blo 1383511 3115637 := bbase (se 5 (by rfl) ⟨146045, by rfl⟩ : syracuseStep 3115637 = 292091) (by norm_num)
theorem B4672133 : Blo 1383511 4672133 := bbase (se 4 (by rfl) ⟨438012, by rfl⟩ : syracuseStep 4672133 = 876025) (by norm_num)
theorem B2075285 : Blo 1383511 2075285 := bbase (se 6 (by rfl) ⟨48639, by rfl⟩ : syracuseStep 2075285 = 97279) (by norm_num)
theorem B5253781 : Blo 1383511 5253781 := bbase (se 6 (by rfl) ⟨123135, by rfl⟩ : syracuseStep 5253781 = 246271) (by norm_num)
theorem B2337437 : Blo 1383511 2337437 := bbase (se 3 (by rfl) ⟨438269, by rfl⟩ : syracuseStep 2337437 = 876539) (by norm_num)
theorem B2075309 : Blo 1383511 2075309 := bbase (se 3 (by rfl) ⟨389120, by rfl⟩ : syracuseStep 2075309 = 778241) (by norm_num)
theorem B3943093 : Blo 1383511 3943093 := bbase (se 5 (by rfl) ⟨184832, by rfl⟩ : syracuseStep 3943093 = 369665) (by norm_num)
theorem B3115709 : Blo 1383511 3115709 := bbase (se 3 (by rfl) ⟨584195, by rfl⟩ : syracuseStep 3115709 = 1168391) (by norm_num)
theorem B2075333 : Blo 1383511 2075333 := bbase (se 4 (by rfl) ⟨194562, by rfl⟩ : syracuseStep 2075333 = 389125) (by norm_num)
theorem B2075357 : Blo 1383511 2075357 := bbase (se 3 (by rfl) ⟨389129, by rfl⟩ : syracuseStep 2075357 = 778259) (by norm_num)
theorem B2075381 : Blo 1383511 2075381 := bbase (se 5 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 2075381 = 194567) (by norm_num)
theorem B3115781 : Blo 1383511 3115781 := bbase (se 4 (by rfl) ⟨292104, by rfl⟩ : syracuseStep 3115781 = 584209) (by norm_num)
theorem B2075405 : Blo 1383511 2075405 := bbase (se 3 (by rfl) ⟨389138, by rfl⟩ : syracuseStep 2075405 = 778277) (by norm_num)
theorem B2337565 : Blo 1383511 2337565 := bbase (se 3 (by rfl) ⟨438293, by rfl⟩ : syracuseStep 2337565 = 876587) (by norm_num)
theorem B2075429 : Blo 1383511 2075429 := bbase (se 4 (by rfl) ⟨194571, by rfl⟩ : syracuseStep 2075429 = 389143) (by norm_num)
theorem B5327669 : Blo 1383511 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B2075453 : Blo 1383511 2075453 := bbase (se 3 (by rfl) ⟨389147, by rfl⟩ : syracuseStep 2075453 = 778295) (by norm_num)
theorem B3115853 : Blo 1383511 3115853 := bbase (se 3 (by rfl) ⟨584222, by rfl⟩ : syracuseStep 3115853 = 1168445) (by norm_num)
theorem B2075477 : Blo 1383511 2075477 := bbase (se 9 (by rfl) ⟨6080, by rfl⟩ : syracuseStep 2075477 = 12161) (by norm_num)
theorem B2075501 : Blo 1383511 2075501 := bbase (se 3 (by rfl) ⟨389156, by rfl⟩ : syracuseStep 2075501 = 778313) (by norm_num)
theorem B2337653 : Blo 1383511 2337653 := bbase (se 5 (by rfl) ⟨109577, by rfl⟩ : syracuseStep 2337653 = 219155) (by norm_num)
theorem B2075525 : Blo 1383511 2075525 := bbase (se 4 (by rfl) ⟨194580, by rfl⟩ : syracuseStep 2075525 = 389161) (by norm_num)
theorem B3115925 : Blo 1383511 3115925 := bbase (se 6 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 3115925 = 146059) (by norm_num)
theorem B2075549 : Blo 1383511 2075549 := bbase (se 3 (by rfl) ⟨389165, by rfl⟩ : syracuseStep 2075549 = 778331) (by norm_num)
theorem B1477541 : Blo 1383511 1477541 := bbase (se 4 (by rfl) ⟨138519, by rfl⟩ : syracuseStep 1477541 = 277039) (by norm_num)
theorem B2075573 : Blo 1383511 2075573 := bbase (se 5 (by rfl) ⟨97292, by rfl⟩ : syracuseStep 2075573 = 194585) (by norm_num)
theorem B5254085 : Blo 1383511 5254085 := bbase (se 4 (by rfl) ⟨492570, by rfl⟩ : syracuseStep 5254085 = 985141) (by norm_num)
theorem B2075597 : Blo 1383511 2075597 := bbase (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) (by norm_num)
theorem B3115997 : Blo 1383511 3115997 := bbase (se 3 (by rfl) ⟨584249, by rfl⟩ : syracuseStep 3115997 = 1168499) (by norm_num)
theorem B2075621 : Blo 1383511 2075621 := bbase (se 4 (by rfl) ⟨194589, by rfl⟩ : syracuseStep 2075621 = 389179) (by norm_num)
theorem B2337781 : Blo 1383511 2337781 := bbase (se 5 (by rfl) ⟨109583, by rfl⟩ : syracuseStep 2337781 = 219167) (by norm_num)
theorem B2075645 : Blo 1383511 2075645 := bbase (se 3 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 2075645 = 778367) (by norm_num)
theorem B2075669 : Blo 1383511 2075669 := bbase (se 6 (by rfl) ⟨48648, by rfl⟩ : syracuseStep 2075669 = 97297) (by norm_num)
theorem B3116069 : Blo 1383511 3116069 := bbase (se 4 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 3116069 = 584263) (by norm_num)
theorem B2075693 : Blo 1383511 2075693 := bbase (se 3 (by rfl) ⟨389192, by rfl⟩ : syracuseStep 2075693 = 778385) (by norm_num)
theorem B4672565 : Blo 1383511 4672565 := bbase (se 5 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 4672565 = 438053) (by norm_num)
theorem B2075717 : Blo 1383511 2075717 := bbase (se 4 (by rfl) ⟨194598, by rfl⟩ : syracuseStep 2075717 = 389197) (by norm_num)
theorem B2337869 : Blo 1383511 2337869 := bbase (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) (by norm_num)
theorem B2075741 : Blo 1383511 2075741 := bbase (se 3 (by rfl) ⟨389201, by rfl⟩ : syracuseStep 2075741 = 778403) (by norm_num)
theorem B3116141 : Blo 1383511 3116141 := bbase (se 3 (by rfl) ⟨584276, by rfl⟩ : syracuseStep 3116141 = 1168553) (by norm_num)
theorem B2075765 : Blo 1383511 2075765 := bbase (se 5 (by rfl) ⟨97301, by rfl⟩ : syracuseStep 2075765 = 194603) (by norm_num)
theorem B2075789 : Blo 1383511 2075789 := bbase (se 3 (by rfl) ⟨389210, by rfl⟩ : syracuseStep 2075789 = 778421) (by norm_num)
theorem B5909669 : Blo 1383511 5909669 := bbase (se 4 (by rfl) ⟨554031, by rfl⟩ : syracuseStep 5909669 = 1108063) (by norm_num)
theorem B2075813 : Blo 1383511 2075813 := bbase (se 4 (by rfl) ⟨194607, by rfl⟩ : syracuseStep 2075813 = 389215) (by norm_num)
theorem B1871029 : Blo 1383511 1871029 := bbase (se 5 (by rfl) ⟨87704, by rfl⟩ : syracuseStep 1871029 = 175409) (by norm_num)
theorem B3116213 : Blo 1383511 3116213 := bbase (se 5 (by rfl) ⟨146072, by rfl⟩ : syracuseStep 3116213 = 292145) (by norm_num)
theorem B2075837 : Blo 1383511 2075837 := bbase (se 3 (by rfl) ⟨389219, by rfl⟩ : syracuseStep 2075837 = 778439) (by norm_num)
theorem B2337997 : Blo 1383511 2337997 := bbase (se 3 (by rfl) ⟨438374, by rfl⟩ : syracuseStep 2337997 = 876749) (by norm_num)
theorem B2075861 : Blo 1383511 2075861 := bbase (se 7 (by rfl) ⟨24326, by rfl⟩ : syracuseStep 2075861 = 48653) (by norm_num)
theorem B2075885 : Blo 1383511 2075885 := bbase (se 3 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 2075885 = 778457) (by norm_num)
theorem B3116285 : Blo 1383511 3116285 := bbase (se 3 (by rfl) ⟨584303, by rfl⟩ : syracuseStep 3116285 = 1168607) (by norm_num)
theorem B2075909 : Blo 1383511 2075909 := bbase (se 4 (by rfl) ⟨194616, by rfl⟩ : syracuseStep 2075909 = 389233) (by norm_num)
theorem B2493725 : Blo 1383511 2493725 := bbase (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) (by norm_num)
theorem B2075933 : Blo 1383511 2075933 := bbase (se 3 (by rfl) ⟨389237, by rfl⟩ : syracuseStep 2075933 = 778475) (by norm_num)
theorem B2075957 : Blo 1383511 2075957 := bbase (se 5 (by rfl) ⟨97310, by rfl⟩ : syracuseStep 2075957 = 194621) (by norm_num)
theorem B3116357 : Blo 1383511 3116357 := bbase (se 4 (by rfl) ⟨292158, by rfl⟩ : syracuseStep 3116357 = 584317) (by norm_num)
theorem B2075981 : Blo 1383511 2075981 := bbase (se 3 (by rfl) ⟨389246, by rfl⟩ : syracuseStep 2075981 = 778493) (by norm_num)
theorem B1477985 : Blo 1383511 1477985 := bbase (se 2 (by rfl) ⟨554244, by rfl⟩ : syracuseStep 1477985 = 1108489) (by norm_num)
theorem B2076005 : Blo 1383511 2076005 := bbase (se 4 (by rfl) ⟨194625, by rfl⟩ : syracuseStep 2076005 = 389251) (by norm_num)
theorem B2076029 : Blo 1383511 2076029 := bbase (se 3 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 2076029 = 778511) (by norm_num)
theorem B3116429 : Blo 1383511 3116429 := bbase (se 3 (by rfl) ⟨584330, by rfl⟩ : syracuseStep 3116429 = 1168661) (by norm_num)
theorem B2076053 : Blo 1383511 2076053 := bbase (se 6 (by rfl) ⟨48657, by rfl⟩ : syracuseStep 2076053 = 97315) (by norm_num)
theorem B1478045 : Blo 1383511 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B5328293 : Blo 1383511 5328293 := bbase (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) (by norm_num)
theorem B2076077 : Blo 1383511 2076077 := bbase (se 3 (by rfl) ⟨389264, by rfl⟩ : syracuseStep 2076077 = 778529) (by norm_num)
theorem B2076101 : Blo 1383511 2076101 := bbase (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) (by norm_num)
theorem B3116501 : Blo 1383511 3116501 := bbase (se 7 (by rfl) ⟨36521, by rfl⟩ : syracuseStep 3116501 = 73043) (by norm_num)
theorem B2076125 : Blo 1383511 2076125 := bbase (se 3 (by rfl) ⟨389273, by rfl⟩ : syracuseStep 2076125 = 778547) (by norm_num)
theorem B4672997 : Blo 1383511 4672997 := bbase (se 4 (by rfl) ⟨438093, by rfl⟩ : syracuseStep 4672997 = 876187) (by norm_num)
theorem B2076149 : Blo 1383511 2076149 := bbase (se 5 (by rfl) ⟨97319, by rfl⟩ : syracuseStep 2076149 = 194639) (by norm_num)
theorem B2076173 : Blo 1383511 2076173 := bbase (se 3 (by rfl) ⟨389282, by rfl⟩ : syracuseStep 2076173 = 778565) (by norm_num)
theorem B1478173 : Blo 1383511 1478173 := bbase (se 3 (by rfl) ⟨277157, by rfl⟩ : syracuseStep 1478173 = 554315) (by norm_num)
theorem B3116573 : Blo 1383511 3116573 := bbase (se 3 (by rfl) ⟨584357, by rfl⟩ : syracuseStep 3116573 = 1168715) (by norm_num)
theorem B2076197 : Blo 1383511 2076197 := bbase (se 4 (by rfl) ⟨194643, by rfl⟩ : syracuseStep 2076197 = 389287) (by norm_num)
theorem B2076221 : Blo 1383511 2076221 := bbase (se 3 (by rfl) ⟨389291, by rfl⟩ : syracuseStep 2076221 = 778583) (by norm_num)
theorem B2076245 : Blo 1383511 2076245 := bbase (se 8 (by rfl) ⟨12165, by rfl⟩ : syracuseStep 2076245 = 24331) (by norm_num)
theorem B2248285 : Blo 1383511 2248285 := bbase (se 3 (by rfl) ⟨421553, by rfl⟩ : syracuseStep 2248285 = 843107) (by norm_num)
theorem B3116645 : Blo 1383511 3116645 := bbase (se 4 (by rfl) ⟨292185, by rfl⟩ : syracuseStep 3116645 = 584371) (by norm_num)
theorem B2076269 : Blo 1383511 2076269 := bbase (se 3 (by rfl) ⟨389300, by rfl⟩ : syracuseStep 2076269 = 778601) (by norm_num)
theorem B2076293 : Blo 1383511 2076293 := bbase (se 4 (by rfl) ⟨194652, by rfl⟩ : syracuseStep 2076293 = 389305) (by norm_num)
theorem B9981589 : Blo 1383511 9981589 := bbase (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) (by norm_num)
theorem B2076317 : Blo 1383511 2076317 := bbase (se 3 (by rfl) ⟨389309, by rfl⟩ : syracuseStep 2076317 = 778619) (by norm_num)
theorem B3116717 : Blo 1383511 3116717 := bbase (se 3 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 3116717 = 1168769) (by norm_num)
theorem B2076341 : Blo 1383511 2076341 := bbase (se 5 (by rfl) ⟨97328, by rfl⟩ : syracuseStep 2076341 = 194657) (by norm_num)
theorem B2076365 : Blo 1383511 2076365 := bbase (se 3 (by rfl) ⟨389318, by rfl⟩ : syracuseStep 2076365 = 778637) (by norm_num)
theorem B7007957 : Blo 1383511 7007957 := bbase (se 7 (by rfl) ⟨82124, by rfl⟩ : syracuseStep 7007957 = 164249) (by norm_num)
theorem B2076389 : Blo 1383511 2076389 := bbase (se 4 (by rfl) ⟨194661, by rfl⟩ : syracuseStep 2076389 = 389323) (by norm_num)
theorem B3116789 : Blo 1383511 3116789 := bbase (se 5 (by rfl) ⟨146099, by rfl⟩ : syracuseStep 3116789 = 292199) (by norm_num)
theorem B2076413 : Blo 1383511 2076413 := bbase (se 3 (by rfl) ⟨389327, by rfl⟩ : syracuseStep 2076413 = 778655) (by norm_num)
theorem B2076437 : Blo 1383511 2076437 := bbase (se 6 (by rfl) ⟨48666, by rfl⟩ : syracuseStep 2076437 = 97333) (by norm_num)
theorem B25620245 : Blo 1383511 25620245 := bbase (se 6 (by rfl) ⟨600474, by rfl⟩ : syracuseStep 25620245 = 1200949) (by norm_num)
theorem B2076461 : Blo 1383511 2076461 := bbase (se 3 (by rfl) ⟨389336, by rfl⟩ : syracuseStep 2076461 = 778673) (by norm_num)
theorem B3116861 : Blo 1383511 3116861 := bbase (se 3 (by rfl) ⟨584411, by rfl⟩ : syracuseStep 3116861 = 1168823) (by norm_num)
theorem B2076485 : Blo 1383511 2076485 := bbase (se 4 (by rfl) ⟨194670, by rfl⟩ : syracuseStep 2076485 = 389341) (by norm_num)
theorem B2076509 : Blo 1383511 2076509 := bbase (se 3 (by rfl) ⟨389345, by rfl⟩ : syracuseStep 2076509 = 778691) (by norm_num)
theorem B2076533 : Blo 1383511 2076533 := bbase (se 5 (by rfl) ⟨97337, by rfl⟩ : syracuseStep 2076533 = 194675) (by norm_num)
theorem B3116933 : Blo 1383511 3116933 := bbase (se 4 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 3116933 = 584425) (by norm_num)
theorem B2076557 : Blo 1383511 2076557 := bbase (se 3 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 2076557 = 778709) (by norm_num)
theorem B4673429 : Blo 1383511 4673429 := bbase (se 6 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 4673429 = 219067) (by norm_num)
theorem B1970077 : Blo 1383511 1970077 := bbase (se 3 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 1970077 = 738779) (by norm_num)
theorem B2076581 : Blo 1383511 2076581 := bbase (se 4 (by rfl) ⟨194679, by rfl⟩ : syracuseStep 2076581 = 389359) (by norm_num)
theorem B2076605 : Blo 1383511 2076605 := bbase (se 3 (by rfl) ⟨389363, by rfl⟩ : syracuseStep 2076605 = 778727) (by norm_num)
theorem B3117005 : Blo 1383511 3117005 := bbase (se 3 (by rfl) ⟨584438, by rfl⟩ : syracuseStep 3117005 = 1168877) (by norm_num)
theorem B29921237 : Blo 1383511 29921237 := bbase (se 7 (by rfl) ⟨350639, by rfl⟩ : syracuseStep 29921237 = 701279) (by norm_num)
theorem B2076629 : Blo 1383511 2076629 := bbase (se 7 (by rfl) ⟨24335, by rfl⟩ : syracuseStep 2076629 = 48671) (by norm_num)
theorem B1478617 : Blo 1383511 1478617 := bbase (se 2 (by rfl) ⟨554481, by rfl⟩ : syracuseStep 1478617 = 1108963) (by norm_num)
theorem B2076653 : Blo 1383511 2076653 := bbase (se 3 (by rfl) ⟨389372, by rfl⟩ : syracuseStep 2076653 = 778745) (by norm_num)
theorem B2076677 : Blo 1383511 2076677 := bbase (se 4 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 2076677 = 389377) (by norm_num)
theorem B3158021 : Blo 1383511 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B3117077 : Blo 1383511 3117077 := bbase (se 6 (by rfl) ⟨73056, by rfl⟩ : syracuseStep 3117077 = 146113) (by norm_num)
theorem B2076701 : Blo 1383511 2076701 := bbase (se 3 (by rfl) ⟨389381, by rfl⟩ : syracuseStep 2076701 = 778763) (by norm_num)
theorem B2076725 : Blo 1383511 2076725 := bbase (se 5 (by rfl) ⟨97346, by rfl⟩ : syracuseStep 2076725 = 194693) (by norm_num)
theorem B2076749 : Blo 1383511 2076749 := bbase (se 3 (by rfl) ⟨389390, by rfl⟩ : syracuseStep 2076749 = 778781) (by norm_num)
theorem B1478737 : Blo 1383511 1478737 := bbase (se 2 (by rfl) ⟨554526, by rfl⟩ : syracuseStep 1478737 = 1109053) (by norm_num)
theorem B3117149 : Blo 1383511 3117149 := bbase (se 3 (by rfl) ⟨584465, by rfl⟩ : syracuseStep 3117149 = 1168931) (by norm_num)
theorem B2076773 : Blo 1383511 2076773 := bbase (se 4 (by rfl) ⟨194697, by rfl⟩ : syracuseStep 2076773 = 389395) (by norm_num)
theorem B2076797 : Blo 1383511 2076797 := bbase (se 3 (by rfl) ⟨389399, by rfl⟩ : syracuseStep 2076797 = 778799) (by norm_num)
theorem B5910677 : Blo 1383511 5910677 := bbase (se 6 (by rfl) ⟨138531, by rfl⟩ : syracuseStep 5910677 = 277063) (by norm_num)
theorem B2076821 : Blo 1383511 2076821 := bbase (se 6 (by rfl) ⟨48675, by rfl⟩ : syracuseStep 2076821 = 97351) (by norm_num)
theorem B3502237 : Blo 1383511 3502237 := bbase (se 3 (by rfl) ⟨656669, by rfl⟩ : syracuseStep 3502237 = 1313339) (by norm_num)
theorem B3117221 : Blo 1383511 3117221 := bbase (se 4 (by rfl) ⟨292239, by rfl⟩ : syracuseStep 3117221 = 584479) (by norm_num)
theorem B2076845 : Blo 1383511 2076845 := bbase (se 3 (by rfl) ⟨389408, by rfl⟩ : syracuseStep 2076845 = 778817) (by norm_num)
theorem B8876213 : Blo 1383511 8876213 := bbase (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) (by norm_num)
theorem B2076869 : Blo 1383511 2076869 := bbase (se 4 (by rfl) ⟨194706, by rfl⟩ : syracuseStep 2076869 = 389413) (by norm_num)
theorem B2076893 : Blo 1383511 2076893 := bbase (se 3 (by rfl) ⟨389417, by rfl⟩ : syracuseStep 2076893 = 778835) (by norm_num)
theorem B3117293 : Blo 1383511 3117293 := bbase (se 3 (by rfl) ⟨584492, by rfl⟩ : syracuseStep 3117293 = 1168985) (by norm_num)
theorem B2076917 : Blo 1383511 2076917 := bbase (se 5 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 2076917 = 194711) (by norm_num)
theorem B3420413 : Blo 1383511 3420413 := bbase (se 3 (by rfl) ⟨641327, by rfl⟩ : syracuseStep 3420413 = 1282655) (by norm_num)
theorem B3502349 : Blo 1383511 3502349 := bbase (se 3 (by rfl) ⟨656690, by rfl⟩ : syracuseStep 3502349 = 1313381) (by norm_num)
theorem B3551501 : Blo 1383511 3551501 := bbase (se 3 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 3551501 = 1331813) (by norm_num)
theorem B2076941 : Blo 1383511 2076941 := bbase (se 3 (by rfl) ⟨389426, by rfl⟩ : syracuseStep 2076941 = 778853) (by norm_num)
theorem B1970453 : Blo 1383511 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B2076965 : Blo 1383511 2076965 := bbase (se 4 (by rfl) ⟨194715, by rfl⟩ : syracuseStep 2076965 = 389431) (by norm_num)
theorem B3117365 : Blo 1383511 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B2076989 : Blo 1383511 2076989 := bbase (se 3 (by rfl) ⟨389435, by rfl⟩ : syracuseStep 2076989 = 778871) (by norm_num)
theorem B4673861 : Blo 1383511 4673861 := bbase (se 4 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 4673861 = 876349) (by norm_num)
theorem B5615941 : Blo 1383511 5615941 := bbase (se 4 (by rfl) ⟨526494, by rfl⟩ : syracuseStep 5615941 = 1052989) (by norm_num)
theorem B1478989 : Blo 1383511 1478989 := bbase (se 3 (by rfl) ⟨277310, by rfl⟩ : syracuseStep 1478989 = 554621) (by norm_num)
theorem B1478993 : Blo 1383511 1478993 := bbase (se 2 (by rfl) ⟨554622, by rfl⟩ : syracuseStep 1478993 = 1109245) (by norm_num)
theorem B2077013 : Blo 1383511 2077013 := bbase (se 10 (by rfl) ⟨3042, by rfl⟩ : syracuseStep 2077013 = 6085) (by norm_num)
theorem B2077037 : Blo 1383511 2077037 := bbase (se 3 (by rfl) ⟨389444, by rfl⟩ : syracuseStep 2077037 = 778889) (by norm_num)
theorem B2077061 : Blo 1383511 2077061 := bbase (se 4 (by rfl) ⟨194724, by rfl⟩ : syracuseStep 2077061 = 389449) (by norm_num)
theorem B15774101 : Blo 1383511 15774101 := bbase (se 6 (by rfl) ⟨369705, by rfl⟩ : syracuseStep 15774101 = 739411) (by norm_num)
theorem B2077085 : Blo 1383511 2077085 := bbase (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) (by norm_num)
theorem B2077109 : Blo 1383511 2077109 := bbase (se 5 (by rfl) ⟨97364, by rfl⟩ : syracuseStep 2077109 = 194729) (by norm_num)
theorem B4493765 : Blo 1383511 4493765 := bbase (se 4 (by rfl) ⟨421290, by rfl⟩ : syracuseStep 4493765 = 842581) (by norm_num)
theorem B3502541 : Blo 1383511 3502541 := bbase (se 3 (by rfl) ⟨656726, by rfl⟩ : syracuseStep 3502541 = 1313453) (by norm_num)
theorem B2077133 : Blo 1383511 2077133 := bbase (se 3 (by rfl) ⟨389462, by rfl⟩ : syracuseStep 2077133 = 778925) (by norm_num)
theorem B51196373 : Blo 1383511 51196373 := bbase (se 7 (by rfl) ⟨599957, by rfl⟩ : syracuseStep 51196373 = 1199915) (by norm_num)
theorem B2077157 : Blo 1383511 2077157 := bbase (se 4 (by rfl) ⟨194733, by rfl⟩ : syracuseStep 2077157 = 389467) (by norm_num)
theorem B1421801 : Blo 1383511 1421801 := bbase (se 2 (by rfl) ⟨533175, by rfl⟩ : syracuseStep 1421801 = 1066351) (by norm_num)
theorem B2077181 : Blo 1383511 2077181 := bbase (se 3 (by rfl) ⟨389471, by rfl⟩ : syracuseStep 2077181 = 778943) (by norm_num)
theorem B2077205 : Blo 1383511 2077205 := bbase (se 6 (by rfl) ⟨48684, by rfl⟩ : syracuseStep 2077205 = 97369) (by norm_num)
theorem B2077229 : Blo 1383511 2077229 := bbase (se 3 (by rfl) ⟨389480, by rfl⟩ : syracuseStep 2077229 = 778961) (by norm_num)
theorem B2077253 : Blo 1383511 2077253 := bbase (se 4 (by rfl) ⟨194742, by rfl⟩ : syracuseStep 2077253 = 389485) (by norm_num)
theorem B11227733 : Blo 1383511 11227733 := bbase (se 8 (by rfl) ⟨65787, by rfl⟩ : syracuseStep 11227733 = 131575) (by norm_num)
theorem B2077277 : Blo 1383511 2077277 := bbase (se 3 (by rfl) ⟨389489, by rfl⟩ : syracuseStep 2077277 = 778979) (by norm_num)
theorem B2077301 : Blo 1383511 2077301 := bbase (se 5 (by rfl) ⟨97373, by rfl⟩ : syracuseStep 2077301 = 194747) (by norm_num)
theorem B2077325 : Blo 1383511 2077325 := bbase (se 3 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 2077325 = 778997) (by norm_num)
theorem B2077349 : Blo 1383511 2077349 := bbase (se 4 (by rfl) ⟨194751, by rfl⟩ : syracuseStep 2077349 = 389503) (by norm_num)
theorem B4207285 : Blo 1383511 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B2077373 : Blo 1383511 2077373 := bbase (se 3 (by rfl) ⟨389507, by rfl⟩ : syracuseStep 2077373 = 779015) (by norm_num)
theorem B2077397 : Blo 1383511 2077397 := bbase (se 7 (by rfl) ⟨24344, by rfl⟩ : syracuseStep 2077397 = 48689) (by norm_num)
theorem B2077421 : Blo 1383511 2077421 := bbase (se 3 (by rfl) ⟨389516, by rfl⟩ : syracuseStep 2077421 = 779033) (by norm_num)
theorem B4674293 : Blo 1383511 4674293 := bbase (se 5 (by rfl) ⟨219107, by rfl⟩ : syracuseStep 4674293 = 438215) (by norm_num)
theorem B2077445 : Blo 1383511 2077445 := bbase (se 4 (by rfl) ⟨194760, by rfl⟩ : syracuseStep 2077445 = 389521) (by norm_num)
theorem B2077469 : Blo 1383511 2077469 := bbase (se 3 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 2077469 = 779051) (by norm_num)
theorem B1577765 : Blo 1383511 1577765 := bbase (se 4 (by rfl) ⟨147915, by rfl⟩ : syracuseStep 1577765 = 295831) (by norm_num)
theorem B3502885 : Blo 1383511 3502885 := bbase (se 4 (by rfl) ⟨328395, by rfl⟩ : syracuseStep 3502885 = 656791) (by norm_num)
theorem B2077493 : Blo 1383511 2077493 := bbase (se 5 (by rfl) ⟨97382, by rfl⟩ : syracuseStep 2077493 = 194765) (by norm_num)
theorem B2077517 : Blo 1383511 2077517 := bbase (se 3 (by rfl) ⟨389534, by rfl⟩ : syracuseStep 2077517 = 779069) (by norm_num)
theorem B2495333 : Blo 1383511 2495333 := bbase (se 4 (by rfl) ⟨233937, by rfl⟩ : syracuseStep 2495333 = 467875) (by norm_num)
theorem B2077541 : Blo 1383511 2077541 := bbase (se 4 (by rfl) ⟨194769, by rfl⟩ : syracuseStep 2077541 = 389539) (by norm_num)
theorem B2077565 : Blo 1383511 2077565 := bbase (se 3 (by rfl) ⟨389543, by rfl⟩ : syracuseStep 2077565 = 779087) (by norm_num)
theorem B3502997 : Blo 1383511 3502997 := bbase (se 6 (by rfl) ⟨82101, by rfl⟩ : syracuseStep 3502997 = 164203) (by norm_num)
theorem B2077589 : Blo 1383511 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B2077613 : Blo 1383511 2077613 := bbase (se 3 (by rfl) ⟨389552, by rfl⟩ : syracuseStep 2077613 = 779105) (by norm_num)
theorem B2077637 : Blo 1383511 2077637 := bbase (se 4 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 2077637 = 389557) (by norm_num)
theorem B2077661 : Blo 1383511 2077661 := bbase (se 3 (by rfl) ⟨389561, by rfl⟩ : syracuseStep 2077661 = 779123) (by norm_num)
theorem B7009253 : Blo 1383511 7009253 := bbase (se 4 (by rfl) ⟨657117, by rfl⟩ : syracuseStep 7009253 = 1314235) (by norm_num)
theorem B2077685 : Blo 1383511 2077685 := bbase (se 5 (by rfl) ⟨97391, by rfl⟩ : syracuseStep 2077685 = 194783) (by norm_num)
theorem B2216965 : Blo 1383511 2216965 := bbase (se 4 (by rfl) ⟨207840, by rfl⟩ : syracuseStep 2216965 = 415681) (by norm_num)
theorem B5256197 : Blo 1383511 5256197 := bbase (se 4 (by rfl) ⟨492768, by rfl⟩ : syracuseStep 5256197 = 985537) (by norm_num)
theorem B3552269 : Blo 1383511 3552269 := bbase (se 3 (by rfl) ⟨666050, by rfl⟩ : syracuseStep 3552269 = 1332101) (by norm_num)
theorem B2077709 : Blo 1383511 2077709 := bbase (se 3 (by rfl) ⟨389570, by rfl⟩ : syracuseStep 2077709 = 779141) (by norm_num)
theorem B2806805 : Blo 1383511 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B2077733 : Blo 1383511 2077733 := bbase (se 4 (by rfl) ⟨194787, by rfl⟩ : syracuseStep 2077733 = 389575) (by norm_num)
theorem B2077757 : Blo 1383511 2077757 := bbase (se 3 (by rfl) ⟨389579, by rfl⟩ : syracuseStep 2077757 = 779159) (by norm_num)
theorem B2806861 : Blo 1383511 2806861 := bbase (se 3 (by rfl) ⟨526286, by rfl⟩ : syracuseStep 2806861 = 1052573) (by norm_num)
theorem B3503189 : Blo 1383511 3503189 := bbase (se 8 (by rfl) ⟨20526, by rfl⟩ : syracuseStep 3503189 = 41053) (by norm_num)
theorem B2077781 : Blo 1383511 2077781 := bbase (se 8 (by rfl) ⟨12174, by rfl⟩ : syracuseStep 2077781 = 24349) (by norm_num)
theorem B3847253 : Blo 1383511 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B2077805 : Blo 1383511 2077805 := bbase (se 3 (by rfl) ⟨389588, by rfl⟩ : syracuseStep 2077805 = 779177) (by norm_num)
theorem B1578097 : Blo 1383511 1578097 := bbase (se 2 (by rfl) ⟨591786, by rfl⟩ : syracuseStep 1578097 = 1183573) (by norm_num)
theorem B2806901 : Blo 1383511 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B2077829 : Blo 1383511 2077829 := bbase (se 4 (by rfl) ⟨194796, by rfl⟩ : syracuseStep 2077829 = 389593) (by norm_num)
theorem B2077853 : Blo 1383511 2077853 := bbase (se 3 (by rfl) ⟨389597, by rfl⟩ : syracuseStep 2077853 = 779195) (by norm_num)
theorem B4674725 : Blo 1383511 4674725 := bbase (se 4 (by rfl) ⟨438255, by rfl⟩ : syracuseStep 4674725 = 876511) (by norm_num)
theorem B3159205 : Blo 1383511 3159205 := bbase (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) (by norm_num)
theorem B4437173 : Blo 1383511 4437173 := bbase (se 5 (by rfl) ⟨207992, by rfl⟩ : syracuseStep 4437173 = 415985) (by norm_num)
theorem B2077877 : Blo 1383511 2077877 := bbase (se 5 (by rfl) ⟨97400, by rfl⟩ : syracuseStep 2077877 = 194801) (by norm_num)
theorem B3372221 : Blo 1383511 3372221 := bbase (se 3 (by rfl) ⟨632291, by rfl⟩ : syracuseStep 3372221 = 1264583) (by norm_num)
theorem B1422533 : Blo 1383511 1422533 := bbase (se 4 (by rfl) ⟨133362, by rfl⟩ : syracuseStep 1422533 = 266725) (by norm_num)
theorem B2077901 : Blo 1383511 2077901 := bbase (se 3 (by rfl) ⟨389606, by rfl⟩ : syracuseStep 2077901 = 779213) (by norm_num)
theorem B2495701 : Blo 1383511 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B3159253 : Blo 1383511 3159253 := bbase (se 7 (by rfl) ⟨37022, by rfl⟩ : syracuseStep 3159253 = 74045) (by norm_num)
theorem B2077925 : Blo 1383511 2077925 := bbase (se 4 (by rfl) ⟨194805, by rfl⟩ : syracuseStep 2077925 = 389611) (by norm_num)
theorem B2077949 : Blo 1383511 2077949 := bbase (se 3 (by rfl) ⟨389615, by rfl⟩ : syracuseStep 2077949 = 779231) (by norm_num)
theorem B2077973 : Blo 1383511 2077973 := bbase (se 6 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 2077973 = 97405) (by norm_num)
theorem B5256485 : Blo 1383511 5256485 := bbase (se 4 (by rfl) ⟨492795, by rfl⟩ : syracuseStep 5256485 = 985591) (by norm_num)
theorem B2077997 : Blo 1383511 2077997 := bbase (se 3 (by rfl) ⟨389624, by rfl⟩ : syracuseStep 2077997 = 779249) (by norm_num)
theorem B2078021 : Blo 1383511 2078021 := bbase (se 4 (by rfl) ⟨194814, by rfl⟩ : syracuseStep 2078021 = 389629) (by norm_num)
theorem B2078045 : Blo 1383511 2078045 := bbase (se 3 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 2078045 = 779267) (by norm_num)
theorem B2078069 : Blo 1383511 2078069 := bbase (se 5 (by rfl) ⟨97409, by rfl⟩ : syracuseStep 2078069 = 194819) (by norm_num)
theorem B2078093 : Blo 1383511 2078093 := bbase (se 3 (by rfl) ⟨389642, by rfl⟩ : syracuseStep 2078093 = 779285) (by norm_num)
theorem B2078117 : Blo 1383511 2078117 := bbase (se 4 (by rfl) ⟨194823, by rfl⟩ : syracuseStep 2078117 = 389647) (by norm_num)
theorem B3503533 : Blo 1383511 3503533 := bbase (se 3 (by rfl) ⟨656912, by rfl⟩ : syracuseStep 3503533 = 1313825) (by norm_num)
theorem B2627005 : Blo 1383511 2627005 := bbase (se 3 (by rfl) ⟨492563, by rfl⟩ : syracuseStep 2627005 = 985127) (by norm_num)
theorem B2078141 : Blo 1383511 2078141 := bbase (se 3 (by rfl) ⟨389651, by rfl⟩ : syracuseStep 2078141 = 779303) (by norm_num)
theorem B2217413 : Blo 1383511 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B2078165 : Blo 1383511 2078165 := bbase (se 7 (by rfl) ⟨24353, by rfl⟩ : syracuseStep 2078165 = 48707) (by norm_num)
theorem B2078189 : Blo 1383511 2078189 := bbase (se 3 (by rfl) ⟨389660, by rfl⟩ : syracuseStep 2078189 = 779321) (by norm_num)
theorem B2078213 : Blo 1383511 2078213 := bbase (se 4 (by rfl) ⟨194832, by rfl⟩ : syracuseStep 2078213 = 389665) (by norm_num)
theorem B3503645 : Blo 1383511 3503645 := bbase (se 3 (by rfl) ⟨656933, by rfl⟩ : syracuseStep 3503645 = 1313867) (by norm_num)
theorem B2078237 : Blo 1383511 2078237 := bbase (se 3 (by rfl) ⟨389669, by rfl⟩ : syracuseStep 2078237 = 779339) (by norm_num)
theorem B6649397 : Blo 1383511 6649397 := bbase (se 5 (by rfl) ⟨311690, by rfl⟩ : syracuseStep 6649397 = 623381) (by norm_num)
theorem B2078261 : Blo 1383511 2078261 := bbase (se 5 (by rfl) ⟨97418, by rfl⟩ : syracuseStep 2078261 = 194837) (by norm_num)
theorem B2627149 : Blo 1383511 2627149 := bbase (se 3 (by rfl) ⟨492590, by rfl⟩ : syracuseStep 2627149 = 985181) (by norm_num)
theorem B4675157 : Blo 1383511 4675157 := bbase (se 8 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 4675157 = 54787) (by norm_num)
theorem B2217613 : Blo 1383511 2217613 := bbase (se 3 (by rfl) ⟨415802, by rfl⟩ : syracuseStep 2217613 = 831605) (by norm_num)
theorem B1971877 : Blo 1383511 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B3503837 : Blo 1383511 3503837 := bbase (se 3 (by rfl) ⟨656969, by rfl⟩ : syracuseStep 3503837 = 1313939) (by norm_num)
theorem B2627309 : Blo 1383511 2627309 := bbase (se 3 (by rfl) ⟨492620, by rfl⟩ : syracuseStep 2627309 = 985241) (by norm_num)
theorem B1578737 : Blo 1383511 1578737 := bbase (se 2 (by rfl) ⟨592026, by rfl⟩ : syracuseStep 1578737 = 1184053) (by norm_num)
theorem B4208453 : Blo 1383511 4208453 := bbase (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) (by norm_num)
theorem B2955133 : Blo 1383511 2955133 := bbase (se 3 (by rfl) ⟨554087, by rfl⟩ : syracuseStep 2955133 = 1108175) (by norm_num)
theorem B2627453 : Blo 1383511 2627453 := bbase (se 3 (by rfl) ⟨492647, by rfl⟩ : syracuseStep 2627453 = 985295) (by norm_num)
theorem B5912453 : Blo 1383511 5912453 := bbase (se 4 (by rfl) ⟨554292, by rfl⟩ : syracuseStep 5912453 = 1108585) (by norm_num)
theorem B2217869 : Blo 1383511 2217869 := bbase (se 3 (by rfl) ⟨415850, by rfl⟩ : syracuseStep 2217869 = 831701) (by norm_num)
theorem B9975797 : Blo 1383511 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B4675589 : Blo 1383511 4675589 := bbase (se 4 (by rfl) ⟨438336, by rfl⟩ : syracuseStep 4675589 = 876673) (by norm_num)
theorem B1751053 : Blo 1383511 1751053 := bbase (se 3 (by rfl) ⟨328322, by rfl⟩ : syracuseStep 1751053 = 656645) (by norm_num)
theorem B3504181 : Blo 1383511 3504181 := bbase (se 5 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 3504181 = 328517) (by norm_num)
theorem B1751149 : Blo 1383511 1751149 := bbase (se 3 (by rfl) ⟨328340, by rfl⟩ : syracuseStep 1751149 = 656681) (by norm_num)
theorem B2627741 : Blo 1383511 2627741 := bbase (se 3 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 2627741 = 985403) (by norm_num)
theorem B3504293 : Blo 1383511 3504293 := bbase (se 4 (by rfl) ⟨328527, by rfl⟩ : syracuseStep 3504293 = 657055) (by norm_num)
theorem B1579225 : Blo 1383511 1579225 := bbase (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) (by norm_num)
theorem B2808029 : Blo 1383511 2808029 := bbase (se 3 (by rfl) ⟨526505, by rfl⟩ : syracuseStep 2808029 = 1053011) (by norm_num)
theorem B7010549 : Blo 1383511 7010549 := bbase (se 5 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 7010549 = 657239) (by norm_num)
theorem B1972469 : Blo 1383511 1972469 := bbase (se 5 (by rfl) ⟨92459, by rfl⟩ : syracuseStep 1972469 = 184919) (by norm_num)
theorem B1751321 : Blo 1383511 1751321 := bbase (se 2 (by rfl) ⟨656745, by rfl⟩ : syracuseStep 1751321 = 1313491) (by norm_num)
theorem B2996509 : Blo 1383511 2996509 := bbase (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) (by norm_num)
theorem B3791141 : Blo 1383511 3791141 := bbase (se 4 (by rfl) ⟨355419, by rfl⟩ : syracuseStep 3791141 = 710839) (by norm_num)
theorem B2627893 : Blo 1383511 2627893 := bbase (se 5 (by rfl) ⟨123182, by rfl⟩ : syracuseStep 2627893 = 246365) (by norm_num)
theorem B1972549 : Blo 1383511 1972549 := bbase (se 4 (by rfl) ⟨184926, by rfl⟩ : syracuseStep 1972549 = 369853) (by norm_num)
theorem B1751377 : Blo 1383511 1751377 := bbase (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) (by norm_num)
theorem B3504485 : Blo 1383511 3504485 := bbase (se 4 (by rfl) ⟨328545, by rfl⟩ : syracuseStep 3504485 = 657091) (by norm_num)
theorem B2955629 : Blo 1383511 2955629 := bbase (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) (by norm_num)
theorem B1579393 : Blo 1383511 1579393 := bbase (se 2 (by rfl) ⟨592272, by rfl⟩ : syracuseStep 1579393 = 1184545) (by norm_num)
theorem B2529677 : Blo 1383511 2529677 := bbase (se 3 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 2529677 = 948629) (by norm_num)
theorem B1751473 : Blo 1383511 1751473 := bbase (se 2 (by rfl) ⟨656802, by rfl⟩ : syracuseStep 1751473 = 1313605) (by norm_num)
theorem B4676021 : Blo 1383511 4676021 := bbase (se 5 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 4676021 = 438377) (by norm_num)
theorem B1972669 : Blo 1383511 1972669 := bbase (se 3 (by rfl) ⟨369875, by rfl⟩ : syracuseStep 1972669 = 739751) (by norm_num)
theorem B5257669 : Blo 1383511 5257669 := bbase (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) (by norm_num)
theorem B1686101 : Blo 1383511 1686101 := bbase (se 8 (by rfl) ⟨9879, by rfl⟩ : syracuseStep 1686101 = 19759) (by norm_num)
theorem B1751645 : Blo 1383511 1751645 := bbase (se 3 (by rfl) ⟨328433, by rfl⟩ : syracuseStep 1751645 = 656867) (by norm_num)
theorem B2628197 : Blo 1383511 2628197 := bbase (se 4 (by rfl) ⟨246393, by rfl⟩ : syracuseStep 2628197 = 492787) (by norm_num)
theorem B1751701 : Blo 1383511 1751701 := bbase (se 6 (by rfl) ⟨41055, by rfl⟩ : syracuseStep 1751701 = 82111) (by norm_num)
theorem B6650549 : Blo 1383511 6650549 := bbase (se 5 (by rfl) ⟨311744, by rfl⟩ : syracuseStep 6650549 = 623489) (by norm_num)
theorem B3504829 : Blo 1383511 3504829 := bbase (se 3 (by rfl) ⟨657155, by rfl⟩ : syracuseStep 3504829 = 1314311) (by norm_num)
theorem B5331653 : Blo 1383511 5331653 := bbase (se 4 (by rfl) ⟨499842, by rfl⟩ : syracuseStep 5331653 = 999685) (by norm_num)
theorem B1751797 : Blo 1383511 1751797 := bbase (se 5 (by rfl) ⟨82115, by rfl⟩ : syracuseStep 1751797 = 164231) (by norm_num)
theorem B5257973 : Blo 1383511 5257973 := bbase (se 5 (by rfl) ⟨246467, by rfl⟩ : syracuseStep 5257973 = 492935) (by norm_num)
theorem B3504941 : Blo 1383511 3504941 := bbase (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) (by norm_num)
theorem B2808685 : Blo 1383511 2808685 := bbase (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) (by norm_num)
theorem B1751969 : Blo 1383511 1751969 := bbase (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) (by norm_num)
theorem B2808749 : Blo 1383511 2808749 := bbase (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) (by norm_num)
theorem B1752025 : Blo 1383511 1752025 := bbase (se 2 (by rfl) ⟨657009, by rfl⟩ : syracuseStep 1752025 = 1314019) (by norm_num)
theorem B2104301 : Blo 1383511 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B3505133 : Blo 1383511 3505133 := bbase (se 3 (by rfl) ⟨657212, by rfl⟩ : syracuseStep 3505133 = 1314425) (by norm_num)
theorem B2218997 : Blo 1383511 2218997 := bbase (se 5 (by rfl) ⟨104015, by rfl⟩ : syracuseStep 2218997 = 208031) (by norm_num)
theorem B10517525 : Blo 1383511 10517525 := bbase (se 6 (by rfl) ⟨246504, by rfl⟩ : syracuseStep 10517525 = 493009) (by norm_num)
theorem B1752121 : Blo 1383511 1752121 := bbase (se 2 (by rfl) ⟨657045, by rfl⟩ : syracuseStep 1752121 = 1314091) (by norm_num)
theorem B2530381 : Blo 1383511 2530381 := bbase (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) (by norm_num)
theorem B2104421 : Blo 1383511 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B2956517 : Blo 1383511 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B1752293 : Blo 1383511 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B7101685 : Blo 1383511 7101685 := bbase (se 5 (by rfl) ⟨332891, by rfl⟩ : syracuseStep 7101685 = 665783) (by norm_num)
theorem B1752349 : Blo 1383511 1752349 := bbase (se 3 (by rfl) ⟨328565, by rfl⟩ : syracuseStep 1752349 = 657131) (by norm_num)
theorem B3505477 : Blo 1383511 3505477 := bbase (se 4 (by rfl) ⟨328638, by rfl⟩ : syracuseStep 3505477 = 657277) (by norm_num)
theorem B2628949 : Blo 1383511 2628949 := bbase (se 11 (by rfl) ⟨1925, by rfl⟩ : syracuseStep 2628949 = 3851) (by norm_num)
theorem B2366813 : Blo 1383511 2366813 := bbase (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) (by norm_num)
theorem B2956637 : Blo 1383511 2956637 := bbase (se 3 (by rfl) ⟨554369, by rfl⟩ : syracuseStep 2956637 = 1108739) (by norm_num)
theorem B1662325 : Blo 1383511 1662325 := bbase (se 5 (by rfl) ⟨77921, by rfl⟩ : syracuseStep 1662325 = 155843) (by norm_num)
theorem B1752445 : Blo 1383511 1752445 := bbase (se 3 (by rfl) ⟨328583, by rfl⟩ : syracuseStep 1752445 = 657167) (by norm_num)
theorem B10509749 : Blo 1383511 10509749 := bbase (se 5 (by rfl) ⟨492644, by rfl⟩ : syracuseStep 10509749 = 985289) (by norm_num)
theorem B6651317 : Blo 1383511 6651317 := bbase (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) (by norm_num)
theorem B3505589 : Blo 1383511 3505589 := bbase (se 5 (by rfl) ⟨164324, by rfl⟩ : syracuseStep 3505589 = 328649) (by norm_num)
theorem B2629093 : Blo 1383511 2629093 := bbase (se 4 (by rfl) ⟨246477, by rfl⟩ : syracuseStep 2629093 = 492955) (by norm_num)
theorem B1662445 : Blo 1383511 1662445 := bbase (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) (by norm_num)
theorem B7888373 : Blo 1383511 7888373 := bbase (se 5 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 7888373 = 739535) (by norm_num)
theorem B4554245 : Blo 1383511 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B7011845 : Blo 1383511 7011845 := bbase (se 4 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 7011845 = 1314721) (by norm_num)
theorem B1752617 : Blo 1383511 1752617 := bbase (se 2 (by rfl) ⟨657231, by rfl⟩ : syracuseStep 1752617 = 1314463) (by norm_num)
theorem B1752673 : Blo 1383511 1752673 := bbase (se 2 (by rfl) ⟨657252, by rfl⟩ : syracuseStep 1752673 = 1314505) (by norm_num)
theorem B3505781 : Blo 1383511 3505781 := bbase (se 5 (by rfl) ⟨164333, by rfl⟩ : syracuseStep 3505781 = 328667) (by norm_num)
theorem B3325573 : Blo 1383511 3325573 := bbase (se 4 (by rfl) ⟨311772, by rfl⟩ : syracuseStep 3325573 = 623545) (by norm_num)
theorem B2629253 : Blo 1383511 2629253 := bbase (se 4 (by rfl) ⟨246492, by rfl⟩ : syracuseStep 2629253 = 492985) (by norm_num)
theorem B1752769 : Blo 1383511 1752769 := bbase (se 2 (by rfl) ⟨657288, by rfl⟩ : syracuseStep 1752769 = 1314577) (by norm_num)
theorem B2629397 : Blo 1383511 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B1777453 : Blo 1383511 1777453 := bbase (se 3 (by rfl) ⟨333272, by rfl⟩ : syracuseStep 1777453 = 666545) (by norm_num)
theorem B2105165 : Blo 1383511 2105165 := bbase (se 3 (by rfl) ⟨394718, by rfl⟩ : syracuseStep 2105165 = 789437) (by norm_num)
theorem B3325805 : Blo 1383511 3325805 := bbase (se 3 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 3325805 = 1247177) (by norm_num)
theorem B1752941 : Blo 1383511 1752941 := bbase (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) (by norm_num)
theorem B7004069 : Blo 1383511 7004069 := bbase (se 4 (by rfl) ⟨656631, by rfl⟩ : syracuseStep 7004069 = 1313263) (by norm_num)
theorem B1752997 : Blo 1383511 1752997 := bbase (se 4 (by rfl) ⟨164343, by rfl⟩ : syracuseStep 1752997 = 328687) (by norm_num)
theorem B3112901 : Blo 1383511 3112901 := bbase (se 4 (by rfl) ⟨291834, by rfl⟩ : syracuseStep 3112901 = 583669) (by norm_num)
theorem B3506125 : Blo 1383511 3506125 := bbase (se 3 (by rfl) ⟨657398, by rfl⟩ : syracuseStep 3506125 = 1314797) (by norm_num)
theorem B2957269 : Blo 1383511 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B1556473 : Blo 1383511 1556473 := bbase (se 2 (by rfl) ⟨583677, by rfl⟩ : syracuseStep 1556473 = 1167355) (by norm_num)
theorem B1384451 : Blo 1383511 1384451 := bstep (se 1 (by rfl) ⟨1038338, by rfl⟩ : syracuseStep 1384451 = 2076677) B2076677
theorem B2105347 : Blo 1383511 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B2334737 : Blo 1383511 2334737 := bstep (se 2 (by rfl) ⟨875526, by rfl⟩ : syracuseStep 2334737 = 1751053) B1751053
theorem B1384467 : Blo 1383511 1384467 := bstep (se 1 (by rfl) ⟨1038350, by rfl⟩ : syracuseStep 1384467 = 2076701) B2076701
theorem B1384483 : Blo 1383511 1384483 := bstep (se 1 (by rfl) ⟨1038362, by rfl⟩ : syracuseStep 1384483 = 2076725) B2076725
theorem B3113009 : Blo 1383511 3113009 := bstep (se 2 (by rfl) ⟨1167378, by rfl⟩ : syracuseStep 3113009 = 2334757) B2334757
theorem B1384499 : Blo 1383511 1384499 := bstep (se 1 (by rfl) ⟨1038374, by rfl⟩ : syracuseStep 1384499 = 2076749) B2076749
theorem B3113027 : Blo 1383511 3113027 := bstep (se 1 (by rfl) ⟨2334770, by rfl⟩ : syracuseStep 3113027 = 4669541) B4669541
theorem B1384515 : Blo 1383511 1384515 := bstep (se 1 (by rfl) ⟨1038386, by rfl⟩ : syracuseStep 1384515 = 2076773) B2076773
theorem B1556563 : Blo 1383511 1556563 := bstep (se 1 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 1556563 = 2334845) B2334845
theorem B1384531 : Blo 1383511 1384531 := bstep (se 1 (by rfl) ⟨1038398, by rfl⟩ : syracuseStep 1384531 = 2076797) B2076797
theorem B3940451 : Blo 1383511 3940451 := bstep (se 1 (by rfl) ⟨2955338, by rfl⟩ : syracuseStep 3940451 = 5910677) B5910677
theorem B1384547 : Blo 1383511 1384547 := bstep (se 1 (by rfl) ⟨1038410, by rfl⟩ : syracuseStep 1384547 = 2076821) B2076821
theorem B11829347 : Blo 1383511 11829347 := bstep (se 1 (by rfl) ⟨8872010, by rfl⟩ : syracuseStep 11829347 = 17744021) B17744021
theorem B1384563 : Blo 1383511 1384563 := bstep (se 1 (by rfl) ⟨1038422, by rfl⟩ : syracuseStep 1384563 = 2076845) B2076845
theorem B1384579 : Blo 1383511 1384579 := bstep (se 1 (by rfl) ⟨1038434, by rfl⟩ : syracuseStep 1384579 = 2076869) B2076869
theorem B7012493 : Blo 1383511 7012493 := bstep (se 3 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 7012493 = 2629685) B2629685
theorem B2334865 : Blo 1383511 2334865 := bstep (se 2 (by rfl) ⟨875574, by rfl⟩ : syracuseStep 2334865 = 1751149) B1751149
theorem B1384595 : Blo 1383511 1384595 := bstep (se 1 (by rfl) ⟨1038446, by rfl⟩ : syracuseStep 1384595 = 2076893) B2076893
theorem B1384611 : Blo 1383511 1384611 := bstep (se 1 (by rfl) ⟨1038458, by rfl⟩ : syracuseStep 1384611 = 2076917) B2076917
theorem B2334899 : Blo 1383511 2334899 := bstep (se 1 (by rfl) ⟨1751174, by rfl⟩ : syracuseStep 2334899 = 3502349) B3502349
theorem B2367667 : Blo 1383511 2367667 := bstep (se 1 (by rfl) ⟨1775750, by rfl⟩ : syracuseStep 2367667 = 3551501) B3551501
theorem B1384627 : Blo 1383511 1384627 := bstep (se 1 (by rfl) ⟨1038470, by rfl⟩ : syracuseStep 1384627 = 2076941) B2076941
theorem B1384643 : Blo 1383511 1384643 := bstep (se 1 (by rfl) ⟨1038482, by rfl⟩ : syracuseStep 1384643 = 2076965) B2076965
theorem B4669649 : Blo 1383511 4669649 := bstep (se 2 (by rfl) ⟨1751118, by rfl⟩ : syracuseStep 4669649 = 3502237) B3502237
theorem B1384659 : Blo 1383511 1384659 := bstep (se 1 (by rfl) ⟨1038494, by rfl⟩ : syracuseStep 1384659 = 2076989) B2076989
theorem B1556707 : Blo 1383511 1556707 := bstep (se 1 (by rfl) ⟨1167530, by rfl⟩ : syracuseStep 1556707 = 2335061) B2335061
theorem B1384675 : Blo 1383511 1384675 := bstep (se 1 (by rfl) ⟨1038506, by rfl⟩ : syracuseStep 1384675 = 2077013) B2077013
theorem B1384691 : Blo 1383511 1384691 := bstep (se 1 (by rfl) ⟨1038518, by rfl⟩ : syracuseStep 1384691 = 2077037) B2077037
theorem B1384707 : Blo 1383511 1384707 := bstep (se 1 (by rfl) ⟨1038530, by rfl⟩ : syracuseStep 1384707 = 2077061) B2077061
theorem B5611789 : Blo 1383511 5611789 := bstep (se 3 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 5611789 = 2104421) B2104421
theorem B3506449 : Blo 1383511 3506449 := bstep (se 2 (by rfl) ⟨1314918, by rfl⟩ : syracuseStep 3506449 = 2629837) B2629837
theorem B1384723 : Blo 1383511 1384723 := bstep (se 1 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 1384723 = 2077085) B2077085
theorem B2105633 : Blo 1383511 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B1384739 : Blo 1383511 1384739 := bstep (se 1 (by rfl) ⟨1038554, by rfl⟩ : syracuseStep 1384739 = 2077109) B2077109
theorem B2335027 : Blo 1383511 2335027 := bstep (se 1 (by rfl) ⟨1751270, by rfl⟩ : syracuseStep 2335027 = 3502541) B3502541
theorem B1384755 : Blo 1383511 1384755 := bstep (se 1 (by rfl) ⟨1038566, by rfl⟩ : syracuseStep 1384755 = 2077133) B2077133
theorem B1384771 : Blo 1383511 1384771 := bstep (se 1 (by rfl) ⟨1038578, by rfl⟩ : syracuseStep 1384771 = 2077157) B2077157
theorem B3113297 : Blo 1383511 3113297 := bstep (se 2 (by rfl) ⟨1167486, by rfl⟩ : syracuseStep 3113297 = 2334973) B2334973
theorem B1384787 : Blo 1383511 1384787 := bstep (se 1 (by rfl) ⟨1038590, by rfl⟩ : syracuseStep 1384787 = 2077181) B2077181
theorem B1753427 : Blo 1383511 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B3113315 : Blo 1383511 3113315 := bstep (se 1 (by rfl) ⟨2334986, by rfl⟩ : syracuseStep 3113315 = 4669973) B4669973
theorem B1384803 : Blo 1383511 1384803 := bstep (se 1 (by rfl) ⟨1038602, by rfl⟩ : syracuseStep 1384803 = 2077205) B2077205
theorem B1556851 : Blo 1383511 1556851 := bstep (se 1 (by rfl) ⟨1167638, by rfl⟩ : syracuseStep 1556851 = 2335277) B2335277
theorem B1384819 : Blo 1383511 1384819 := bstep (se 1 (by rfl) ⟨1038614, by rfl⟩ : syracuseStep 1384819 = 2077229) B2077229
theorem B1384835 : Blo 1383511 1384835 := bstep (se 1 (by rfl) ⟨1038626, by rfl⟩ : syracuseStep 1384835 = 2077253) B2077253
theorem B1384851 : Blo 1383511 1384851 := bstep (se 1 (by rfl) ⟨1038638, by rfl⟩ : syracuseStep 1384851 = 2077277) B2077277
theorem B1384867 : Blo 1383511 1384867 := bstep (se 1 (by rfl) ⟨1038650, by rfl⟩ : syracuseStep 1384867 = 2077301) B2077301
theorem B2998691 : Blo 1383511 2998691 := bstep (se 1 (by rfl) ⟨2249018, by rfl⟩ : syracuseStep 2998691 = 4498037) B4498037
theorem B7487921 : Blo 1383511 7487921 := bstep (se 2 (by rfl) ⟨2807970, by rfl⟩ : syracuseStep 7487921 = 5615941) B5615941
theorem B2630065 : Blo 1383511 2630065 := bstep (se 2 (by rfl) ⟨986274, by rfl⟩ : syracuseStep 2630065 = 1972549) B1972549
theorem B1384883 : Blo 1383511 1384883 := bstep (se 1 (by rfl) ⟨1038662, by rfl⟩ : syracuseStep 1384883 = 2077325) B2077325
theorem B2335169 : Blo 1383511 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B1384899 : Blo 1383511 1384899 := bstep (se 1 (by rfl) ⟨1038674, by rfl⟩ : syracuseStep 1384899 = 2077349) B2077349
theorem B1384915 : Blo 1383511 1384915 := bstep (se 1 (by rfl) ⟨1038686, by rfl⟩ : syracuseStep 1384915 = 2077373) B2077373
theorem B1384931 : Blo 1383511 1384931 := bstep (se 1 (by rfl) ⟨1038698, by rfl⟩ : syracuseStep 1384931 = 2077397) B2077397
theorem B14967281 : Blo 1383511 14967281 := bstep (se 2 (by rfl) ⟨5612730, by rfl⟩ : syracuseStep 14967281 = 11225461) B11225461
theorem B1384947 : Blo 1383511 1384947 := bstep (se 1 (by rfl) ⟨1038710, by rfl⟩ : syracuseStep 1384947 = 2077421) B2077421
theorem B2105857 : Blo 1383511 2105857 := bstep (se 2 (by rfl) ⟨789696, by rfl⟩ : syracuseStep 2105857 = 1579393) B1579393
theorem B1556995 : Blo 1383511 1556995 := bstep (se 1 (by rfl) ⟨1167746, by rfl⟩ : syracuseStep 1556995 = 2335493) B2335493
theorem B1384963 : Blo 1383511 1384963 := bstep (se 1 (by rfl) ⟨1038722, by rfl⟩ : syracuseStep 1384963 = 2077445) B2077445
theorem B3793421 : Blo 1383511 3793421 := bstep (se 3 (by rfl) ⟨711266, by rfl⟩ : syracuseStep 3793421 = 1422533) B1422533
theorem B1384979 : Blo 1383511 1384979 := bstep (se 1 (by rfl) ⟨1038734, by rfl⟩ : syracuseStep 1384979 = 2077469) B2077469
theorem B1384995 : Blo 1383511 1384995 := bstep (se 1 (by rfl) ⟨1038746, by rfl⟩ : syracuseStep 1384995 = 2077493) B2077493
theorem B3506723 : Blo 1383511 3506723 := bstep (se 1 (by rfl) ⟨2630042, by rfl⟩ : syracuseStep 3506723 = 5260085) B5260085
theorem B1385011 : Blo 1383511 1385011 := bstep (se 1 (by rfl) ⟨1038758, by rfl⟩ : syracuseStep 1385011 = 2077517) B2077517
theorem B2335297 : Blo 1383511 2335297 := bstep (se 2 (by rfl) ⟨875736, by rfl⟩ : syracuseStep 2335297 = 1751473) B1751473
theorem B1385027 : Blo 1383511 1385027 := bstep (se 1 (by rfl) ⟨1038770, by rfl⟩ : syracuseStep 1385027 = 2077541) B2077541
theorem B2630225 : Blo 1383511 2630225 := bstep (se 2 (by rfl) ⟨986334, by rfl⟩ : syracuseStep 2630225 = 1972669) B1972669
theorem B1385043 : Blo 1383511 1385043 := bstep (se 1 (by rfl) ⟨1038782, by rfl⟩ : syracuseStep 1385043 = 2077565) B2077565
theorem B2335331 : Blo 1383511 2335331 := bstep (se 1 (by rfl) ⟨1751498, by rfl⟩ : syracuseStep 2335331 = 3502997) B3502997
theorem B1385059 : Blo 1383511 1385059 := bstep (se 1 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 1385059 = 2077589) B2077589
theorem B3113585 : Blo 1383511 3113585 := bstep (se 2 (by rfl) ⟨1167594, by rfl⟩ : syracuseStep 3113585 = 2335189) B2335189
theorem B1385075 : Blo 1383511 1385075 := bstep (se 1 (by rfl) ⟨1038806, by rfl⟩ : syracuseStep 1385075 = 2077613) B2077613
theorem B3113603 : Blo 1383511 3113603 := bstep (se 1 (by rfl) ⟨2335202, by rfl⟩ : syracuseStep 3113603 = 4670405) B4670405
theorem B1385091 : Blo 1383511 1385091 := bstep (se 1 (by rfl) ⟨1038818, by rfl⟩ : syracuseStep 1385091 = 2077637) B2077637
theorem B5259917 : Blo 1383511 5259917 := bstep (se 3 (by rfl) ⟨986234, by rfl⟩ : syracuseStep 5259917 = 1972469) B1972469
theorem B1557139 : Blo 1383511 1557139 := bstep (se 1 (by rfl) ⟨1167854, by rfl⟩ : syracuseStep 1557139 = 2335709) B2335709
theorem B1385107 : Blo 1383511 1385107 := bstep (se 1 (by rfl) ⟨1038830, by rfl⟩ : syracuseStep 1385107 = 2077661) B2077661
theorem B1385123 : Blo 1383511 1385123 := bstep (se 1 (by rfl) ⟨1038842, by rfl⟩ : syracuseStep 1385123 = 2077685) B2077685
theorem B1385139 : Blo 1383511 1385139 := bstep (se 1 (by rfl) ⟨1038854, by rfl⟩ : syracuseStep 1385139 = 2077709) B2077709
theorem B1385155 : Blo 1383511 1385155 := bstep (se 1 (by rfl) ⟨1038866, by rfl⟩ : syracuseStep 1385155 = 2077733) B2077733
theorem B1385171 : Blo 1383511 1385171 := bstep (se 1 (by rfl) ⟨1038878, by rfl⟩ : syracuseStep 1385171 = 2077757) B2077757
theorem B2335459 : Blo 1383511 2335459 := bstep (se 1 (by rfl) ⟨1751594, by rfl⟩ : syracuseStep 2335459 = 3503189) B3503189
theorem B1385187 : Blo 1383511 1385187 := bstep (se 1 (by rfl) ⟨1038890, by rfl⟩ : syracuseStep 1385187 = 2077781) B2077781
theorem B3506915 : Blo 1383511 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B4670189 : Blo 1383511 4670189 := bstep (se 3 (by rfl) ⟨875660, by rfl⟩ : syracuseStep 4670189 = 1751321) B1751321
theorem B1385203 : Blo 1383511 1385203 := bstep (se 1 (by rfl) ⟨1038902, by rfl⟩ : syracuseStep 1385203 = 2077805) B2077805
theorem B1385219 : Blo 1383511 1385219 := bstep (se 1 (by rfl) ⟨1038914, by rfl⟩ : syracuseStep 1385219 = 2077829) B2077829
theorem B1385235 : Blo 1383511 1385235 := bstep (se 1 (by rfl) ⟨1038926, by rfl⟩ : syracuseStep 1385235 = 2077853) B2077853
theorem B4670243 : Blo 1383511 4670243 := bstep (se 1 (by rfl) ⟨3502682, by rfl⟩ : syracuseStep 4670243 = 7005365) B7005365
theorem B1557283 : Blo 1383511 1557283 := bstep (se 1 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 1557283 = 2335925) B2335925
theorem B2958115 : Blo 1383511 2958115 := bstep (se 1 (by rfl) ⟨2218586, by rfl⟩ : syracuseStep 2958115 = 4437173) B4437173
theorem B1385251 : Blo 1383511 1385251 := bstep (se 1 (by rfl) ⟨1038938, by rfl⟩ : syracuseStep 1385251 = 2077877) B2077877
theorem B1385267 : Blo 1383511 1385267 := bstep (se 1 (by rfl) ⟨1038950, by rfl⟩ : syracuseStep 1385267 = 2077901) B2077901
theorem B1385283 : Blo 1383511 1385283 := bstep (se 1 (by rfl) ⟨1038962, by rfl⟩ : syracuseStep 1385283 = 2077925) B2077925
theorem B1385299 : Blo 1383511 1385299 := bstep (se 1 (by rfl) ⟨1038974, by rfl⟩ : syracuseStep 1385299 = 2077949) B2077949
theorem B1385315 : Blo 1383511 1385315 := bstep (se 1 (by rfl) ⟨1038986, by rfl⟩ : syracuseStep 1385315 = 2077973) B2077973
theorem B7005041 : Blo 1383511 7005041 := bstep (se 2 (by rfl) ⟨2626890, by rfl⟩ : syracuseStep 7005041 = 5253781) B5253781
theorem B2335601 : Blo 1383511 2335601 := bstep (se 2 (by rfl) ⟨875850, by rfl⟩ : syracuseStep 2335601 = 1751701) B1751701
theorem B1385331 : Blo 1383511 1385331 := bstep (se 1 (by rfl) ⟨1038998, by rfl⟩ : syracuseStep 1385331 = 2077997) B2077997
theorem B1385347 : Blo 1383511 1385347 := bstep (se 1 (by rfl) ⟨1039010, by rfl⟩ : syracuseStep 1385347 = 2078021) B2078021
theorem B3113873 : Blo 1383511 3113873 := bstep (se 2 (by rfl) ⟨1167702, by rfl⟩ : syracuseStep 3113873 = 2335405) B2335405
theorem B1385363 : Blo 1383511 1385363 := bstep (se 1 (by rfl) ⟨1039022, by rfl⟩ : syracuseStep 1385363 = 2078045) B2078045
theorem B3113891 : Blo 1383511 3113891 := bstep (se 1 (by rfl) ⟨2335418, by rfl⟩ : syracuseStep 3113891 = 4670837) B4670837
theorem B1385379 : Blo 1383511 1385379 := bstep (se 1 (by rfl) ⟨1039034, by rfl⟩ : syracuseStep 1385379 = 2078069) B2078069
theorem B3941293 : Blo 1383511 3941293 := bstep (se 3 (by rfl) ⟨738992, by rfl⟩ : syracuseStep 3941293 = 1477985) B1477985
theorem B1557427 : Blo 1383511 1557427 := bstep (se 1 (by rfl) ⟨1168070, by rfl⟩ : syracuseStep 1557427 = 2336141) B2336141
theorem B1385395 : Blo 1383511 1385395 := bstep (se 1 (by rfl) ⟨1039046, by rfl⟩ : syracuseStep 1385395 = 2078093) B2078093
theorem B1385411 : Blo 1383511 1385411 := bstep (se 1 (by rfl) ⟨1039058, by rfl⟩ : syracuseStep 1385411 = 2078117) B2078117
theorem B22438853 : Blo 1383511 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B9978821 : Blo 1383511 9978821 := bstep (se 4 (by rfl) ⟨935514, by rfl⟩ : syracuseStep 9978821 = 1871029) B1871029
theorem B12633029 : Blo 1383511 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B1385427 : Blo 1383511 1385427 := bstep (se 1 (by rfl) ⟨1039070, by rfl⟩ : syracuseStep 1385427 = 2078141) B2078141
theorem B1385443 : Blo 1383511 1385443 := bstep (se 1 (by rfl) ⟨1039082, by rfl⟩ : syracuseStep 1385443 = 2078165) B2078165
theorem B2335729 : Blo 1383511 2335729 := bstep (se 2 (by rfl) ⟨875898, by rfl⟩ : syracuseStep 2335729 = 1751797) B1751797
theorem B1385459 : Blo 1383511 1385459 := bstep (se 1 (by rfl) ⟨1039094, by rfl⟩ : syracuseStep 1385459 = 2078189) B2078189
theorem B1385475 : Blo 1383511 1385475 := bstep (se 1 (by rfl) ⟨1039106, by rfl⟩ : syracuseStep 1385475 = 2078213) B2078213
theorem B2335763 : Blo 1383511 2335763 := bstep (se 1 (by rfl) ⟨1751822, by rfl⟩ : syracuseStep 2335763 = 3503645) B3503645
theorem B1385491 : Blo 1383511 1385491 := bstep (se 1 (by rfl) ⟨1039118, by rfl⟩ : syracuseStep 1385491 = 2078237) B2078237
theorem B4432931 : Blo 1383511 4432931 := bstep (se 1 (by rfl) ⟨3324698, by rfl⟩ : syracuseStep 4432931 = 6649397) B6649397
theorem B1385507 : Blo 1383511 1385507 := bstep (se 1 (by rfl) ⟨1039130, by rfl⟩ : syracuseStep 1385507 = 2078261) B2078261
theorem B4670513 : Blo 1383511 4670513 := bstep (se 2 (by rfl) ⟨1751442, by rfl⟩ : syracuseStep 4670513 = 3502885) B3502885
theorem B1557571 : Blo 1383511 1557571 := bstep (se 1 (by rfl) ⟨1168178, by rfl⟩ : syracuseStep 1557571 = 2336357) B2336357
theorem B3941453 : Blo 1383511 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B2335891 : Blo 1383511 2335891 := bstep (se 1 (by rfl) ⟨1751918, by rfl⟩ : syracuseStep 2335891 = 3503837) B3503837
theorem B3114161 : Blo 1383511 3114161 := bstep (se 2 (by rfl) ⟨1167810, by rfl⟩ : syracuseStep 3114161 = 2335621) B2335621
theorem B3114179 : Blo 1383511 3114179 := bstep (se 1 (by rfl) ⟨2335634, by rfl⟩ : syracuseStep 3114179 = 4671269) B4671269
theorem B1557715 : Blo 1383511 1557715 := bstep (se 1 (by rfl) ⟨1168286, by rfl⟩ : syracuseStep 1557715 = 2336573) B2336573
theorem B3941635 : Blo 1383511 3941635 := bstep (se 1 (by rfl) ⟨2956226, by rfl⟩ : syracuseStep 3941635 = 5912453) B5912453
theorem B2336033 : Blo 1383511 2336033 := bstep (se 2 (by rfl) ⟨876012, by rfl⟩ : syracuseStep 2336033 = 1752025) B1752025
theorem B1557859 : Blo 1383511 1557859 := bstep (se 1 (by rfl) ⟨1168394, by rfl⟩ : syracuseStep 1557859 = 2336789) B2336789
theorem B2336161 : Blo 1383511 2336161 := bstep (se 2 (by rfl) ⟨876060, by rfl⟩ : syracuseStep 2336161 = 1752121) B1752121
theorem B2336195 : Blo 1383511 2336195 := bstep (se 1 (by rfl) ⟨1752146, by rfl⟩ : syracuseStep 2336195 = 3504293) B3504293
theorem B3327427 : Blo 1383511 3327427 := bstep (se 1 (by rfl) ⟨2495570, by rfl⟩ : syracuseStep 3327427 = 4991141) B4991141
theorem B3114449 : Blo 1383511 3114449 := bstep (se 2 (by rfl) ⟨1167918, by rfl⟩ : syracuseStep 3114449 = 2335837) B2335837
theorem B3114467 : Blo 1383511 3114467 := bstep (se 1 (by rfl) ⟨2335850, by rfl⟩ : syracuseStep 3114467 = 4671701) B4671701
theorem B1558003 : Blo 1383511 1558003 := bstep (se 1 (by rfl) ⟨1168502, by rfl⟩ : syracuseStep 1558003 = 2337005) B2337005
theorem B2336323 : Blo 1383511 2336323 := bstep (se 1 (by rfl) ⟨1752242, by rfl⟩ : syracuseStep 2336323 = 3504485) B3504485
theorem B9479749 : Blo 1383511 9479749 := bstep (se 4 (by rfl) ⟨888726, by rfl⟩ : syracuseStep 9479749 = 1777453) B1777453
theorem B4671053 : Blo 1383511 4671053 := bstep (se 3 (by rfl) ⟨875822, by rfl⟩ : syracuseStep 4671053 = 1751645) B1751645
theorem B8873549 : Blo 1383511 8873549 := bstep (se 3 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 8873549 = 3327581) B3327581
theorem B3327601 : Blo 1383511 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B4212337 : Blo 1383511 4212337 := bstep (se 2 (by rfl) ⟨1579626, by rfl⟩ : syracuseStep 4212337 = 3159253) B3159253
theorem B4671107 : Blo 1383511 4671107 := bstep (se 1 (by rfl) ⟨3503330, by rfl⟩ : syracuseStep 4671107 = 7006661) B7006661
theorem B1558147 : Blo 1383511 1558147 := bstep (se 1 (by rfl) ⟨1168610, by rfl⟩ : syracuseStep 1558147 = 2337221) B2337221
theorem B2336465 : Blo 1383511 2336465 := bstep (se 2 (by rfl) ⟨876174, by rfl⟩ : syracuseStep 2336465 = 1752349) B1752349
theorem B3114737 : Blo 1383511 3114737 := bstep (se 2 (by rfl) ⟨1168026, by rfl⟩ : syracuseStep 3114737 = 2336053) B2336053
theorem B3114755 : Blo 1383511 3114755 := bstep (se 1 (by rfl) ⟨2336066, by rfl⟩ : syracuseStep 3114755 = 4672133) B4672133
theorem B1558291 : Blo 1383511 1558291 := bstep (se 1 (by rfl) ⟨1168718, by rfl⟩ : syracuseStep 1558291 = 2337437) B2337437
theorem B4433699 : Blo 1383511 4433699 := bstep (se 1 (by rfl) ⟨3325274, by rfl⟩ : syracuseStep 4433699 = 6650549) B6650549
theorem B2336593 : Blo 1383511 2336593 := bstep (se 2 (by rfl) ⟨876222, by rfl⟩ : syracuseStep 2336593 = 1752445) B1752445
theorem B2336627 : Blo 1383511 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B4671377 : Blo 1383511 4671377 := bstep (se 2 (by rfl) ⟨1751766, by rfl⟩ : syracuseStep 4671377 = 3503533) B3503533
theorem B1558435 : Blo 1383511 1558435 := bstep (se 1 (by rfl) ⟨1168826, by rfl⟩ : syracuseStep 1558435 = 2337653) B2337653
theorem B8865733 : Blo 1383511 8865733 := bstep (se 4 (by rfl) ⟨831162, by rfl⟩ : syracuseStep 8865733 = 1662325) B1662325
theorem B1402867 : Blo 1383511 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B2336755 : Blo 1383511 2336755 := bstep (se 1 (by rfl) ⟨1752566, by rfl⟩ : syracuseStep 2336755 = 3505133) B3505133
theorem B3115025 : Blo 1383511 3115025 := bstep (se 2 (by rfl) ⟨1168134, by rfl⟩ : syracuseStep 3115025 = 2336269) B2336269
theorem B3115043 : Blo 1383511 3115043 := bstep (se 1 (by rfl) ⟨2336282, by rfl⟩ : syracuseStep 3115043 = 4672565) B4672565
theorem B1558579 : Blo 1383511 1558579 := bstep (se 1 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 1558579 = 2337869) B2337869
theorem B2336897 : Blo 1383511 2336897 := bstep (se 2 (by rfl) ⟨876336, by rfl⟩ : syracuseStep 2336897 = 1752673) B1752673
theorem B4434097 : Blo 1383511 4434097 := bstep (se 2 (by rfl) ⟨1662786, by rfl⟩ : syracuseStep 4434097 = 3325573) B3325573
theorem B2337025 : Blo 1383511 2337025 := bstep (se 2 (by rfl) ⟨876384, by rfl⟩ : syracuseStep 2337025 = 1752769) B1752769
theorem B6654221 : Blo 1383511 6654221 := bstep (se 3 (by rfl) ⟨1247666, by rfl⟩ : syracuseStep 6654221 = 2495333) B2495333
theorem B7006499 : Blo 1383511 7006499 := bstep (se 1 (by rfl) ⟨5254874, by rfl⟩ : syracuseStep 7006499 = 10509749) B10509749
theorem B4434211 : Blo 1383511 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B2337059 : Blo 1383511 2337059 := bstep (se 1 (by rfl) ⟨1752794, by rfl⟩ : syracuseStep 2337059 = 3505589) B3505589
theorem B3115313 : Blo 1383511 3115313 := bstep (se 2 (by rfl) ⟨1168242, by rfl⟩ : syracuseStep 3115313 = 2336485) B2336485
theorem B3115331 : Blo 1383511 3115331 := bstep (se 1 (by rfl) ⟨2336498, by rfl⟩ : syracuseStep 3115331 = 4672997) B4672997
theorem B2337187 : Blo 1383511 2337187 := bstep (se 1 (by rfl) ⟨1752890, by rfl⟩ : syracuseStep 2337187 = 3505781) B3505781
theorem B4671917 : Blo 1383511 4671917 := bstep (se 3 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 4671917 = 1751969) B1751969
theorem B15165877 : Blo 1383511 15165877 := bstep (se 5 (by rfl) ⟨710900, by rfl⟩ : syracuseStep 15165877 = 1421801) B1421801
theorem B7489997 : Blo 1383511 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B4671971 : Blo 1383511 4671971 := bstep (se 1 (by rfl) ⟨3503978, by rfl⟩ : syracuseStep 4671971 = 7007957) B7007957
theorem B2337329 : Blo 1383511 2337329 := bstep (se 2 (by rfl) ⟨876498, by rfl⟩ : syracuseStep 2337329 = 1752997) B1752997
theorem B1403443 : Blo 1383511 1403443 := bstep (se 1 (by rfl) ⟨1052582, by rfl⟩ : syracuseStep 1403443 = 2105165) B2105165
theorem B3115601 : Blo 1383511 3115601 := bstep (se 2 (by rfl) ⟨1168350, by rfl⟩ : syracuseStep 3115601 = 2336701) B2336701
theorem B3115619 : Blo 1383511 3115619 := bstep (se 1 (by rfl) ⟨2336714, by rfl⟩ : syracuseStep 3115619 = 4673429) B4673429
theorem B3943025 : Blo 1383511 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B2075267 : Blo 1383511 2075267 := bstep (se 1 (by rfl) ⟨1556450, by rfl⟩ : syracuseStep 2075267 = 3112901) B3112901
theorem B2075297 : Blo 1383511 2075297 := bstep (se 2 (by rfl) ⟨778236, by rfl⟩ : syracuseStep 2075297 = 1556473) B1556473
theorem B2337457 : Blo 1383511 2337457 := bstep (se 2 (by rfl) ⟨876546, by rfl⟩ : syracuseStep 2337457 = 1753093) B1753093
theorem B2075315 : Blo 1383511 2075315 := bstep (se 1 (by rfl) ⟨1556486, by rfl⟩ : syracuseStep 2075315 = 3112973) B3112973
theorem B9472717 : Blo 1383511 9472717 := bstep (se 3 (by rfl) ⟨1776134, by rfl⟩ : syracuseStep 9472717 = 3552269) B3552269
theorem B2075345 : Blo 1383511 2075345 := bstep (se 2 (by rfl) ⟨778254, by rfl⟩ : syracuseStep 2075345 = 1556509) B1556509
theorem B2337491 : Blo 1383511 2337491 := bstep (se 1 (by rfl) ⟨1753118, by rfl⟩ : syracuseStep 2337491 = 3506237) B3506237
theorem B2075363 : Blo 1383511 2075363 := bstep (se 1 (by rfl) ⟨1556522, by rfl⟩ : syracuseStep 2075363 = 3113045) B3113045
theorem B4672241 : Blo 1383511 4672241 := bstep (se 2 (by rfl) ⟨1752090, by rfl⟩ : syracuseStep 4672241 = 3504181) B3504181
theorem B2075393 : Blo 1383511 2075393 := bstep (se 2 (by rfl) ⟨778272, by rfl⟩ : syracuseStep 2075393 = 1556545) B1556545
theorem B2075411 : Blo 1383511 2075411 := bstep (se 1 (by rfl) ⟨1556558, by rfl⟩ : syracuseStep 2075411 = 3113117) B3113117
theorem B5917475 : Blo 1383511 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B3550001 : Blo 1383511 3550001 := bstep (se 2 (by rfl) ⟨1331250, by rfl⟩ : syracuseStep 3550001 = 2662501) B2662501
theorem B2075441 : Blo 1383511 2075441 := bstep (se 2 (by rfl) ⟨778290, by rfl⟩ : syracuseStep 2075441 = 1556581) B1556581
theorem B2075459 : Blo 1383511 2075459 := bstep (se 1 (by rfl) ⟨1556594, by rfl⟩ : syracuseStep 2075459 = 3113189) B3113189
theorem B2337619 : Blo 1383511 2337619 := bstep (se 1 (by rfl) ⟨1753214, by rfl⟩ : syracuseStep 2337619 = 3506429) B3506429
theorem B2280275 : Blo 1383511 2280275 := bstep (se 1 (by rfl) ⟨1710206, by rfl⟩ : syracuseStep 2280275 = 3420413) B3420413
theorem B2075489 : Blo 1383511 2075489 := bstep (se 2 (by rfl) ⟨778308, by rfl⟩ : syracuseStep 2075489 = 1556617) B1556617
theorem B3115889 : Blo 1383511 3115889 := bstep (se 2 (by rfl) ⟨1168458, by rfl⟩ : syracuseStep 3115889 = 2336917) B2336917
theorem B2075507 : Blo 1383511 2075507 := bstep (se 1 (by rfl) ⟨1556630, by rfl⟩ : syracuseStep 2075507 = 3113261) B3113261
theorem B3115907 : Blo 1383511 3115907 := bstep (se 1 (by rfl) ⟨2336930, by rfl⟩ : syracuseStep 3115907 = 4673861) B4673861
theorem B10259341 : Blo 1383511 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B2075537 : Blo 1383511 2075537 := bstep (se 2 (by rfl) ⟨778326, by rfl⟩ : syracuseStep 2075537 = 1556653) B1556653
theorem B2075555 : Blo 1383511 2075555 := bstep (se 1 (by rfl) ⟨1556666, by rfl⟩ : syracuseStep 2075555 = 3113333) B3113333
theorem B2075585 : Blo 1383511 2075585 := bstep (se 2 (by rfl) ⟨778344, by rfl⟩ : syracuseStep 2075585 = 1556689) B1556689
theorem B2075603 : Blo 1383511 2075603 := bstep (se 1 (by rfl) ⟨1556702, by rfl⟩ : syracuseStep 2075603 = 3113405) B3113405
theorem B2337761 : Blo 1383511 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B34130915 : Blo 1383511 34130915 := bstep (se 1 (by rfl) ⟨25598186, by rfl⟩ : syracuseStep 34130915 = 51196373) B51196373
theorem B15772643 : Blo 1383511 15772643 := bstep (se 1 (by rfl) ⟨11829482, by rfl⟩ : syracuseStep 15772643 = 23658965) B23658965
theorem B2075633 : Blo 1383511 2075633 := bstep (se 2 (by rfl) ⟨778362, by rfl⟩ : syracuseStep 2075633 = 1556725) B1556725
theorem B4434929 : Blo 1383511 4434929 := bstep (se 2 (by rfl) ⟨1663098, by rfl⟩ : syracuseStep 4434929 = 3326197) B3326197
theorem B2075651 : Blo 1383511 2075651 := bstep (se 1 (by rfl) ⟨1556738, by rfl⟩ : syracuseStep 2075651 = 3113477) B3113477
theorem B2075681 : Blo 1383511 2075681 := bstep (se 2 (by rfl) ⟨778380, by rfl⟩ : syracuseStep 2075681 = 1556761) B1556761
theorem B2075699 : Blo 1383511 2075699 := bstep (se 1 (by rfl) ⟨1556774, by rfl⟩ : syracuseStep 2075699 = 3113549) B3113549
theorem B7007309 : Blo 1383511 7007309 := bstep (se 3 (by rfl) ⟨1313870, by rfl⟩ : syracuseStep 7007309 = 2627741) B2627741
theorem B2075729 : Blo 1383511 2075729 := bstep (se 2 (by rfl) ⟨778398, by rfl⟩ : syracuseStep 2075729 = 1556797) B1556797
theorem B2337889 : Blo 1383511 2337889 := bstep (se 2 (by rfl) ⟨876708, by rfl⟩ : syracuseStep 2337889 = 1753417) B1753417
theorem B2075747 : Blo 1383511 2075747 := bstep (se 1 (by rfl) ⟨1556810, by rfl⟩ : syracuseStep 2075747 = 3113621) B3113621
theorem B2075777 : Blo 1383511 2075777 := bstep (se 2 (by rfl) ⟨778416, by rfl⟩ : syracuseStep 2075777 = 1556833) B1556833
theorem B2337923 : Blo 1383511 2337923 := bstep (se 1 (by rfl) ⟨1753442, by rfl⟩ : syracuseStep 2337923 = 3506885) B3506885
theorem B3116177 : Blo 1383511 3116177 := bstep (se 2 (by rfl) ⟨1168566, by rfl⟩ : syracuseStep 3116177 = 2337133) B2337133
theorem B2075795 : Blo 1383511 2075795 := bstep (se 1 (by rfl) ⟨1556846, by rfl⟩ : syracuseStep 2075795 = 3113693) B3113693
theorem B3116195 : Blo 1383511 3116195 := bstep (se 1 (by rfl) ⟨2337146, by rfl⟩ : syracuseStep 3116195 = 4674293) B4674293
theorem B2075825 : Blo 1383511 2075825 := bstep (se 2 (by rfl) ⟨778434, by rfl⟩ : syracuseStep 2075825 = 1556869) B1556869
theorem B2075843 : Blo 1383511 2075843 := bstep (se 1 (by rfl) ⟨1556882, by rfl⟩ : syracuseStep 2075843 = 3113765) B3113765
theorem B1404115 : Blo 1383511 1404115 := bstep (se 1 (by rfl) ⟨1053086, by rfl⟩ : syracuseStep 1404115 = 2106173) B2106173
theorem B2075873 : Blo 1383511 2075873 := bstep (se 2 (by rfl) ⟨778452, by rfl⟩ : syracuseStep 2075873 = 1556905) B1556905
theorem B2075891 : Blo 1383511 2075891 := bstep (se 1 (by rfl) ⟨1556918, by rfl⟩ : syracuseStep 2075891 = 3113837) B3113837
theorem B2338051 : Blo 1383511 2338051 := bstep (se 1 (by rfl) ⟨1753538, by rfl⟩ : syracuseStep 2338051 = 3507077) B3507077
theorem B4672781 : Blo 1383511 4672781 := bstep (se 3 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 4672781 = 1752293) B1752293
theorem B2075921 : Blo 1383511 2075921 := bstep (se 2 (by rfl) ⟨778470, by rfl⟩ : syracuseStep 2075921 = 1556941) B1556941
theorem B2075939 : Blo 1383511 2075939 := bstep (se 1 (by rfl) ⟨1556954, by rfl⟩ : syracuseStep 2075939 = 3113909) B3113909
theorem B2075969 : Blo 1383511 2075969 := bstep (se 2 (by rfl) ⟨778488, by rfl⟩ : syracuseStep 2075969 = 1556977) B1556977
theorem B4672835 : Blo 1383511 4672835 := bstep (se 1 (by rfl) ⟨3504626, by rfl⟩ : syracuseStep 4672835 = 7009253) B7009253
theorem B2075987 : Blo 1383511 2075987 := bstep (se 1 (by rfl) ⟨1556990, by rfl⟩ : syracuseStep 2075987 = 3113981) B3113981
theorem B1871203 : Blo 1383511 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B2076017 : Blo 1383511 2076017 := bstep (se 2 (by rfl) ⟨778506, by rfl⟩ : syracuseStep 2076017 = 1557013) B1557013
theorem B2076035 : Blo 1383511 2076035 := bstep (se 1 (by rfl) ⟨1557026, by rfl⟩ : syracuseStep 2076035 = 3114053) B3114053
theorem B5254541 : Blo 1383511 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B2493841 : Blo 1383511 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B2076065 : Blo 1383511 2076065 := bstep (se 2 (by rfl) ⟨778524, by rfl⟩ : syracuseStep 2076065 = 1557049) B1557049
theorem B1871267 : Blo 1383511 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B3116465 : Blo 1383511 3116465 := bstep (se 2 (by rfl) ⟨1168674, by rfl⟩ : syracuseStep 3116465 = 2337349) B2337349
theorem B2076083 : Blo 1383511 2076083 := bstep (se 1 (by rfl) ⟨1557062, by rfl⟩ : syracuseStep 2076083 = 3114125) B3114125
theorem B3116483 : Blo 1383511 3116483 := bstep (se 1 (by rfl) ⟨2337362, by rfl⟩ : syracuseStep 3116483 = 4674725) B4674725
theorem B2698705 : Blo 1383511 2698705 := bstep (se 2 (by rfl) ⟨1012014, by rfl⟩ : syracuseStep 2698705 = 2024029) B2024029
theorem B2076113 : Blo 1383511 2076113 := bstep (se 2 (by rfl) ⟨778542, by rfl⟩ : syracuseStep 2076113 = 1557085) B1557085
theorem B2076131 : Blo 1383511 2076131 := bstep (se 1 (by rfl) ⟨1557098, by rfl⟩ : syracuseStep 2076131 = 3114197) B3114197
theorem B2076161 : Blo 1383511 2076161 := bstep (se 2 (by rfl) ⟨778560, by rfl⟩ : syracuseStep 2076161 = 1557121) B1557121
theorem B4435469 : Blo 1383511 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B2076179 : Blo 1383511 2076179 := bstep (se 1 (by rfl) ⟨1557134, by rfl⟩ : syracuseStep 2076179 = 3114269) B3114269
theorem B3943981 : Blo 1383511 3943981 := bstep (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) B1478993
theorem B2076209 : Blo 1383511 2076209 := bstep (se 2 (by rfl) ⟨778578, by rfl⟩ : syracuseStep 2076209 = 1557157) B1557157
theorem B17985077 : Blo 1383511 17985077 := bstep (se 5 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 17985077 = 1686101) B1686101
theorem B2076227 : Blo 1383511 2076227 := bstep (se 1 (by rfl) ⟨1557170, by rfl⟩ : syracuseStep 2076227 = 3114341) B3114341
theorem B4673105 : Blo 1383511 4673105 := bstep (se 2 (by rfl) ⟨1752414, by rfl⟩ : syracuseStep 4673105 = 3504829) B3504829
theorem B2076257 : Blo 1383511 2076257 := bstep (se 2 (by rfl) ⟨778596, by rfl⟩ : syracuseStep 2076257 = 1557193) B1557193
theorem B2076275 : Blo 1383511 2076275 := bstep (se 1 (by rfl) ⟨1557206, by rfl⟩ : syracuseStep 2076275 = 3114413) B3114413
theorem B2076305 : Blo 1383511 2076305 := bstep (se 2 (by rfl) ⟨778614, by rfl⟩ : syracuseStep 2076305 = 1557229) B1557229
theorem B2076323 : Blo 1383511 2076323 := bstep (se 1 (by rfl) ⟨1557242, by rfl⟩ : syracuseStep 2076323 = 3114485) B3114485
theorem B2076353 : Blo 1383511 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B6745805 : Blo 1383511 6745805 := bstep (se 3 (by rfl) ⟨1264838, by rfl⟩ : syracuseStep 6745805 = 2529677) B2529677
theorem B3116753 : Blo 1383511 3116753 := bstep (se 2 (by rfl) ⟨1168782, by rfl⟩ : syracuseStep 3116753 = 2337565) B2337565
theorem B2076371 : Blo 1383511 2076371 := bstep (se 1 (by rfl) ⟨1557278, by rfl⟩ : syracuseStep 2076371 = 3114557) B3114557
theorem B3116771 : Blo 1383511 3116771 := bstep (se 1 (by rfl) ⟨2337578, by rfl⟩ : syracuseStep 3116771 = 4675157) B4675157
theorem B2076401 : Blo 1383511 2076401 := bstep (se 2 (by rfl) ⟨778650, by rfl⟩ : syracuseStep 2076401 = 1557301) B1557301
theorem B2076419 : Blo 1383511 2076419 := bstep (se 1 (by rfl) ⟨1557314, by rfl⟩ : syracuseStep 2076419 = 3114629) B3114629
theorem B3944209 : Blo 1383511 3944209 := bstep (se 2 (by rfl) ⟨1479078, by rfl⟩ : syracuseStep 3944209 = 2958157) B2958157
theorem B2076449 : Blo 1383511 2076449 := bstep (se 2 (by rfl) ⟨778668, by rfl⟩ : syracuseStep 2076449 = 1557337) B1557337
theorem B2076467 : Blo 1383511 2076467 := bstep (se 1 (by rfl) ⟨1557350, by rfl⟩ : syracuseStep 2076467 = 3114701) B3114701
theorem B2076497 : Blo 1383511 2076497 := bstep (se 2 (by rfl) ⟨778686, by rfl⟩ : syracuseStep 2076497 = 1557373) B1557373
theorem B2076515 : Blo 1383511 2076515 := bstep (se 1 (by rfl) ⟨1557386, by rfl⟩ : syracuseStep 2076515 = 3114773) B3114773
theorem B18952049 : Blo 1383511 18952049 := bstep (se 2 (by rfl) ⟨7107018, by rfl⟩ : syracuseStep 18952049 = 14214037) B14214037
theorem B2076545 : Blo 1383511 2076545 := bstep (se 2 (by rfl) ⟨778704, by rfl⟩ : syracuseStep 2076545 = 1557409) B1557409
theorem B2805635 : Blo 1383511 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B2076563 : Blo 1383511 2076563 := bstep (se 1 (by rfl) ⟨1557422, by rfl⟩ : syracuseStep 2076563 = 3114845) B3114845
theorem B2076593 : Blo 1383511 2076593 := bstep (se 2 (by rfl) ⟨778722, by rfl⟩ : syracuseStep 2076593 = 1557445) B1557445
theorem B3944369 : Blo 1383511 3944369 := bstep (se 2 (by rfl) ⟨1479138, by rfl⟩ : syracuseStep 3944369 = 2958277) B2958277
theorem B1478579 : Blo 1383511 1478579 := bstep (se 1 (by rfl) ⟨1108934, by rfl⟩ : syracuseStep 1478579 = 2217869) B2217869
theorem B2076611 : Blo 1383511 2076611 := bstep (se 1 (by rfl) ⟨1557458, by rfl⟩ : syracuseStep 2076611 = 3114917) B3114917
theorem B2076641 : Blo 1383511 2076641 := bstep (se 2 (by rfl) ⟨778740, by rfl⟩ : syracuseStep 2076641 = 1557481) B1557481
theorem B12627953 : Blo 1383511 12627953 := bstep (se 2 (by rfl) ⟨4735482, by rfl⟩ : syracuseStep 12627953 = 9470965) B9470965
theorem B3117041 : Blo 1383511 3117041 := bstep (se 2 (by rfl) ⟨1168890, by rfl⟩ : syracuseStep 3117041 = 2337781) B2337781
theorem B2076659 : Blo 1383511 2076659 := bstep (se 1 (by rfl) ⟨1557494, by rfl⟩ : syracuseStep 2076659 = 3114989) B3114989
theorem B3117059 : Blo 1383511 3117059 := bstep (se 1 (by rfl) ⟨2337794, by rfl⟩ : syracuseStep 3117059 = 4675589) B4675589
theorem B12144653 : Blo 1383511 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B2076689 : Blo 1383511 2076689 := bstep (se 2 (by rfl) ⟨778758, by rfl⟩ : syracuseStep 2076689 = 1557517) B1557517
theorem B7483427 : Blo 1383511 7483427 := bstep (se 1 (by rfl) ⟨5612570, by rfl⟩ : syracuseStep 7483427 = 11225141) B11225141
theorem B2076707 : Blo 1383511 2076707 := bstep (se 1 (by rfl) ⟨1557530, by rfl⟩ : syracuseStep 2076707 = 3115061) B3115061
theorem B3944483 : Blo 1383511 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B2076737 : Blo 1383511 2076737 := bstep (se 2 (by rfl) ⟨778776, by rfl⟩ : syracuseStep 2076737 = 1557553) B1557553
theorem B2076755 : Blo 1383511 2076755 := bstep (se 1 (by rfl) ⟨1557566, by rfl⟩ : syracuseStep 2076755 = 3115133) B3115133
theorem B4673645 : Blo 1383511 4673645 := bstep (se 3 (by rfl) ⟨876308, by rfl⟩ : syracuseStep 4673645 = 1752617) B1752617
theorem B5910641 : Blo 1383511 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B2076785 : Blo 1383511 2076785 := bstep (se 2 (by rfl) ⟨778794, by rfl⟩ : syracuseStep 2076785 = 1557589) B1557589
theorem B2076803 : Blo 1383511 2076803 := bstep (se 1 (by rfl) ⟨1557602, by rfl⟩ : syracuseStep 2076803 = 3115205) B3115205
theorem B1872019 : Blo 1383511 1872019 := bstep (se 1 (by rfl) ⟨1404014, by rfl⟩ : syracuseStep 1872019 = 2808029) B2808029
theorem B2076833 : Blo 1383511 2076833 := bstep (se 2 (by rfl) ⟨778812, by rfl⟩ : syracuseStep 2076833 = 1557625) B1557625
theorem B4673699 : Blo 1383511 4673699 := bstep (se 1 (by rfl) ⟨3505274, by rfl⟩ : syracuseStep 4673699 = 7010549) B7010549
theorem B2076851 : Blo 1383511 2076851 := bstep (se 1 (by rfl) ⟨1557638, by rfl⟩ : syracuseStep 2076851 = 3115277) B3115277
theorem B2527427 : Blo 1383511 2527427 := bstep (se 1 (by rfl) ⟨1895570, by rfl⟩ : syracuseStep 2527427 = 3791141) B3791141
theorem B2076881 : Blo 1383511 2076881 := bstep (se 2 (by rfl) ⟨778830, by rfl⟩ : syracuseStep 2076881 = 1557661) B1557661
theorem B2076899 : Blo 1383511 2076899 := bstep (se 1 (by rfl) ⟨1557674, by rfl⟩ : syracuseStep 2076899 = 3115349) B3115349
theorem B1970419 : Blo 1383511 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B1896691 : Blo 1383511 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B2076929 : Blo 1383511 2076929 := bstep (se 2 (by rfl) ⟨778848, by rfl⟩ : syracuseStep 2076929 = 1557697) B1557697
theorem B3117329 : Blo 1383511 3117329 := bstep (se 2 (by rfl) ⟨1168998, by rfl⟩ : syracuseStep 3117329 = 2337997) B2337997
theorem B2076947 : Blo 1383511 2076947 := bstep (se 1 (by rfl) ⟨1557710, by rfl⟩ : syracuseStep 2076947 = 3115421) B3115421
theorem B3117347 : Blo 1383511 3117347 := bstep (se 1 (by rfl) ⟨2338010, by rfl⟩ : syracuseStep 3117347 = 4676021) B4676021
theorem B2076977 : Blo 1383511 2076977 := bstep (se 2 (by rfl) ⟨778866, by rfl⟩ : syracuseStep 2076977 = 1557733) B1557733
theorem B2076995 : Blo 1383511 2076995 := bstep (se 1 (by rfl) ⟨1557746, by rfl⟩ : syracuseStep 2076995 = 3115493) B3115493
theorem B2077025 : Blo 1383511 2077025 := bstep (se 2 (by rfl) ⟨778884, by rfl⟩ : syracuseStep 2077025 = 1557769) B1557769
theorem B2077043 : Blo 1383511 2077043 := bstep (se 1 (by rfl) ⟨1557782, by rfl⟩ : syracuseStep 2077043 = 3115565) B3115565
theorem B2077073 : Blo 1383511 2077073 := bstep (se 2 (by rfl) ⟨778902, by rfl⟩ : syracuseStep 2077073 = 1557805) B1557805
theorem B2077091 : Blo 1383511 2077091 := bstep (se 1 (by rfl) ⟨1557818, by rfl⟩ : syracuseStep 2077091 = 3115637) B3115637
theorem B4673969 : Blo 1383511 4673969 := bstep (se 2 (by rfl) ⟨1752738, by rfl⟩ : syracuseStep 4673969 = 3505477) B3505477
theorem B2077121 : Blo 1383511 2077121 := bstep (se 2 (by rfl) ⟨778920, by rfl⟩ : syracuseStep 2077121 = 1557841) B1557841
theorem B2077139 : Blo 1383511 2077139 := bstep (se 1 (by rfl) ⟨1557854, by rfl⟩ : syracuseStep 2077139 = 3115709) B3115709
theorem B2077169 : Blo 1383511 2077169 := bstep (se 2 (by rfl) ⟨778938, by rfl⟩ : syracuseStep 2077169 = 1557877) B1557877
theorem B2077187 : Blo 1383511 2077187 := bstep (se 1 (by rfl) ⟨1557890, by rfl⟩ : syracuseStep 2077187 = 3115781) B3115781
theorem B2077217 : Blo 1383511 2077217 := bstep (se 2 (by rfl) ⟨778956, by rfl⟩ : syracuseStep 2077217 = 1557913) B1557913
theorem B3551779 : Blo 1383511 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B2077235 : Blo 1383511 2077235 := bstep (se 1 (by rfl) ⟨1557926, by rfl⟩ : syracuseStep 2077235 = 3115853) B3115853
theorem B14979653 : Blo 1383511 14979653 := bstep (se 4 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 14979653 = 2808685) B2808685
theorem B3502673 : Blo 1383511 3502673 := bstep (se 2 (by rfl) ⟨1313502, by rfl⟩ : syracuseStep 3502673 = 2627005) B2627005
theorem B2077265 : Blo 1383511 2077265 := bstep (se 2 (by rfl) ⟨778974, by rfl⟩ : syracuseStep 2077265 = 1557949) B1557949
theorem B2077283 : Blo 1383511 2077283 := bstep (se 1 (by rfl) ⟨1557962, by rfl⟩ : syracuseStep 2077283 = 3115925) B3115925
theorem B2077313 : Blo 1383511 2077313 := bstep (se 2 (by rfl) ⟨778992, by rfl⟩ : syracuseStep 2077313 = 1557985) B1557985
theorem B3502723 : Blo 1383511 3502723 := bstep (se 1 (by rfl) ⟨2627042, by rfl⟩ : syracuseStep 3502723 = 5254085) B5254085
theorem B2216593 : Blo 1383511 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B2077331 : Blo 1383511 2077331 := bstep (se 1 (by rfl) ⟨1557998, by rfl⟩ : syracuseStep 2077331 = 3115997) B3115997
theorem B1479331 : Blo 1383511 1479331 := bstep (se 1 (by rfl) ⟨1109498, by rfl⟩ : syracuseStep 1479331 = 2218997) B2218997
theorem B2077361 : Blo 1383511 2077361 := bstep (se 2 (by rfl) ⟨779010, by rfl⟩ : syracuseStep 2077361 = 1558021) B1558021
theorem B2077379 : Blo 1383511 2077379 := bstep (se 1 (by rfl) ⟨1558034, by rfl⟩ : syracuseStep 2077379 = 3116069) B3116069
theorem B1970897 : Blo 1383511 1970897 := bstep (se 2 (by rfl) ⟨739086, by rfl⟩ : syracuseStep 1970897 = 1478173) B1478173
theorem B2077409 : Blo 1383511 2077409 := bstep (se 2 (by rfl) ⟨779028, by rfl⟩ : syracuseStep 2077409 = 1558057) B1558057
theorem B2077427 : Blo 1383511 2077427 := bstep (se 1 (by rfl) ⟨1558070, by rfl⟩ : syracuseStep 2077427 = 3116141) B3116141
theorem B4207373 : Blo 1383511 4207373 := bstep (se 3 (by rfl) ⟨788882, by rfl⟩ : syracuseStep 4207373 = 1577765) B1577765
theorem B3502865 : Blo 1383511 3502865 := bstep (se 2 (by rfl) ⟨1313574, by rfl⟩ : syracuseStep 3502865 = 2627149) B2627149
theorem B2077457 : Blo 1383511 2077457 := bstep (se 2 (by rfl) ⟨779046, by rfl⟩ : syracuseStep 2077457 = 1558093) B1558093
theorem B151532309 : Blo 1383511 151532309 := bstep (se 6 (by rfl) ⟨3551538, by rfl⟩ : syracuseStep 151532309 = 7103077) B7103077
theorem B2077475 : Blo 1383511 2077475 := bstep (se 1 (by rfl) ⟨1558106, by rfl⟩ : syracuseStep 2077475 = 3116213) B3116213
theorem B2077505 : Blo 1383511 2077505 := bstep (se 2 (by rfl) ⟨779064, by rfl⟩ : syracuseStep 2077505 = 1558129) B1558129
theorem B1971011 : Blo 1383511 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B2077523 : Blo 1383511 2077523 := bstep (se 1 (by rfl) ⟨1558142, by rfl⟩ : syracuseStep 2077523 = 3116285) B3116285
theorem B13308785 : Blo 1383511 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B2077553 : Blo 1383511 2077553 := bstep (se 2 (by rfl) ⟨779082, by rfl⟩ : syracuseStep 2077553 = 1558165) B1558165
theorem B2077571 : Blo 1383511 2077571 := bstep (se 1 (by rfl) ⟨1558178, by rfl⟩ : syracuseStep 2077571 = 3116357) B3116357
theorem B1577875 : Blo 1383511 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B1971091 : Blo 1383511 1971091 := bstep (se 1 (by rfl) ⟨1478318, by rfl⟩ : syracuseStep 1971091 = 2956637) B2956637
theorem B2077601 : Blo 1383511 2077601 := bstep (se 2 (by rfl) ⟨779100, by rfl⟩ : syracuseStep 2077601 = 1558201) B1558201
theorem B2077619 : Blo 1383511 2077619 := bstep (se 1 (by rfl) ⟨1558214, by rfl⟩ : syracuseStep 2077619 = 3116429) B3116429
theorem B4674509 : Blo 1383511 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B2077649 : Blo 1383511 2077649 := bstep (se 2 (by rfl) ⟨779118, by rfl⟩ : syracuseStep 2077649 = 1558237) B1558237
theorem B2077667 : Blo 1383511 2077667 := bstep (se 1 (by rfl) ⟨1558250, by rfl⟩ : syracuseStep 2077667 = 3116501) B3116501
theorem B2077697 : Blo 1383511 2077697 := bstep (se 2 (by rfl) ⟨779136, by rfl⟩ : syracuseStep 2077697 = 1558273) B1558273
theorem B4674563 : Blo 1383511 4674563 := bstep (se 1 (by rfl) ⟨3505922, by rfl⟩ : syracuseStep 4674563 = 7011845) B7011845
theorem B2077715 : Blo 1383511 2077715 := bstep (se 1 (by rfl) ⟨1558286, by rfl⟩ : syracuseStep 2077715 = 3116573) B3116573
theorem B2077745 : Blo 1383511 2077745 := bstep (se 2 (by rfl) ⟨779154, by rfl⟩ : syracuseStep 2077745 = 1558309) B1558309
theorem B2077763 : Blo 1383511 2077763 := bstep (se 1 (by rfl) ⟨1558322, by rfl⟩ : syracuseStep 2077763 = 3116645) B3116645
theorem B2077793 : Blo 1383511 2077793 := bstep (se 2 (by rfl) ⟨779172, by rfl⟩ : syracuseStep 2077793 = 1558345) B1558345
theorem B2077811 : Blo 1383511 2077811 := bstep (se 1 (by rfl) ⟨1558358, by rfl⟩ : syracuseStep 2077811 = 3116717) B3116717
theorem B7885957 : Blo 1383511 7885957 := bstep (se 4 (by rfl) ⟨739308, by rfl⟩ : syracuseStep 7885957 = 1478617) B1478617
theorem B2077841 : Blo 1383511 2077841 := bstep (se 2 (by rfl) ⟨779190, by rfl⟩ : syracuseStep 2077841 = 1558381) B1558381
theorem B2077859 : Blo 1383511 2077859 := bstep (se 1 (by rfl) ⟨1558394, by rfl⟩ : syracuseStep 2077859 = 3116789) B3116789
theorem B2077889 : Blo 1383511 2077889 := bstep (se 2 (by rfl) ⟨779208, by rfl⟩ : syracuseStep 2077889 = 1558417) B1558417
theorem B2626769 : Blo 1383511 2626769 := bstep (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) B1970077
theorem B2077907 : Blo 1383511 2077907 := bstep (se 1 (by rfl) ⟨1558430, by rfl⟩ : syracuseStep 2077907 = 3116861) B3116861
theorem B2077937 : Blo 1383511 2077937 := bstep (se 2 (by rfl) ⟨779226, by rfl⟩ : syracuseStep 2077937 = 1558453) B1558453
theorem B2217203 : Blo 1383511 2217203 := bstep (se 1 (by rfl) ⟨1662902, by rfl⟩ : syracuseStep 2217203 = 3325805) B3325805
theorem B2077955 : Blo 1383511 2077955 := bstep (se 1 (by rfl) ⟨1558466, by rfl⟩ : syracuseStep 2077955 = 3116933) B3116933
theorem B4674833 : Blo 1383511 4674833 := bstep (se 2 (by rfl) ⟨1753062, by rfl⟩ : syracuseStep 4674833 = 3506125) B3506125
theorem B2077985 : Blo 1383511 2077985 := bstep (se 2 (by rfl) ⟨779244, by rfl⟩ : syracuseStep 2077985 = 1558489) B1558489
theorem B2078003 : Blo 1383511 2078003 := bstep (se 1 (by rfl) ⟨1558502, by rfl⟩ : syracuseStep 2078003 = 3117005) B3117005
theorem B2078033 : Blo 1383511 2078033 := bstep (se 2 (by rfl) ⟨779262, by rfl⟩ : syracuseStep 2078033 = 1558525) B1558525
theorem B2078051 : Blo 1383511 2078051 := bstep (se 1 (by rfl) ⟨1558538, by rfl⟩ : syracuseStep 2078051 = 3117077) B3117077
theorem B2078081 : Blo 1383511 2078081 := bstep (se 2 (by rfl) ⟨779280, by rfl⟩ : syracuseStep 2078081 = 1558561) B1558561
theorem B4437389 : Blo 1383511 4437389 := bstep (se 3 (by rfl) ⟨832010, by rfl⟩ : syracuseStep 4437389 = 1664021) B1664021
theorem B2078099 : Blo 1383511 2078099 := bstep (se 1 (by rfl) ⟨1558574, by rfl⟩ : syracuseStep 2078099 = 3117149) B3117149
theorem B2078129 : Blo 1383511 2078129 := bstep (se 2 (by rfl) ⟨779298, by rfl⟩ : syracuseStep 2078129 = 1558597) B1558597
theorem B1971649 : Blo 1383511 1971649 := bstep (se 2 (by rfl) ⟨739368, by rfl⟩ : syracuseStep 1971649 = 1478737) B1478737
theorem B2078147 : Blo 1383511 2078147 := bstep (se 1 (by rfl) ⟨1558610, by rfl⟩ : syracuseStep 2078147 = 3117221) B3117221
theorem B2078177 : Blo 1383511 2078177 := bstep (se 2 (by rfl) ⟨779316, by rfl⟩ : syracuseStep 2078177 = 1558633) B1558633
theorem B2078195 : Blo 1383511 2078195 := bstep (se 1 (by rfl) ⟨1558646, by rfl⟩ : syracuseStep 2078195 = 3117293) B3117293
theorem B2078225 : Blo 1383511 2078225 := bstep (se 2 (by rfl) ⟨779334, by rfl⟩ : syracuseStep 2078225 = 1558669) B1558669
theorem B2078243 : Blo 1383511 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B10516067 : Blo 1383511 10516067 := bstep (se 1 (by rfl) ⟨7887050, by rfl⟩ : syracuseStep 10516067 = 15774101) B15774101
theorem B3159697 : Blo 1383511 3159697 := bstep (se 2 (by rfl) ⟨1184886, by rfl⟩ : syracuseStep 3159697 = 2369773) B2369773
theorem B3995345 : Blo 1383511 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B7485155 : Blo 1383511 7485155 := bstep (se 1 (by rfl) ⟨5613866, by rfl⟩ : syracuseStep 7485155 = 11227733) B11227733
theorem B3503857 : Blo 1383511 3503857 := bstep (se 2 (by rfl) ⟨1313946, by rfl⟩ : syracuseStep 3503857 = 2627893) B2627893
theorem B4675373 : Blo 1383511 4675373 := bstep (se 3 (by rfl) ⟨876632, by rfl⟩ : syracuseStep 4675373 = 1753265) B1753265
theorem B8992589 : Blo 1383511 8992589 := bstep (se 3 (by rfl) ⟨1686110, by rfl⟩ : syracuseStep 8992589 = 3372221) B3372221
theorem B4675427 : Blo 1383511 4675427 := bstep (se 1 (by rfl) ⟨3506570, by rfl⟩ : syracuseStep 4675427 = 7013141) B7013141
theorem B5060465 : Blo 1383511 5060465 := bstep (se 2 (by rfl) ⟨1897674, by rfl⟩ : syracuseStep 5060465 = 3795349) B3795349
theorem B2627491 : Blo 1383511 2627491 := bstep (se 1 (by rfl) ⟨1970618, by rfl⟩ : syracuseStep 2627491 = 3941237) B3941237
theorem B7010225 : Blo 1383511 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B3504131 : Blo 1383511 3504131 := bstep (se 1 (by rfl) ⟨2628098, by rfl⟩ : syracuseStep 3504131 = 5256197) B5256197
theorem B6649933 : Blo 1383511 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B4675697 : Blo 1383511 4675697 := bstep (se 2 (by rfl) ⟨1753386, by rfl⟩ : syracuseStep 4675697 = 3506773) B3506773
theorem B1972355 : Blo 1383511 1972355 := bstep (se 1 (by rfl) ⟨1479266, by rfl⟩ : syracuseStep 1972355 = 2958533) B2958533
theorem B3791011 : Blo 1383511 3791011 := bstep (se 1 (by rfl) ⟨2843258, by rfl⟩ : syracuseStep 3791011 = 5686517) B5686517
theorem B3504323 : Blo 1383511 3504323 := bstep (se 1 (by rfl) ⟨2628242, by rfl⟩ : syracuseStep 3504323 = 5256485) B5256485
theorem B16849093 : Blo 1383511 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B2218195 : Blo 1383511 2218195 := bstep (se 1 (by rfl) ⟨1663646, by rfl⟩ : syracuseStep 2218195 = 3327293) B3327293
theorem B5257457 : Blo 1383511 5257457 := bstep (se 2 (by rfl) ⟨1971546, by rfl⟩ : syracuseStep 5257457 = 3943093) B3943093
theorem B2103619 : Blo 1383511 2103619 := bstep (se 1 (by rfl) ⟨1577714, by rfl⟩ : syracuseStep 2103619 = 3155429) B3155429
theorem B2627939 : Blo 1383511 2627939 := bstep (se 1 (by rfl) ⟨1970954, by rfl⟩ : syracuseStep 2627939 = 3941909) B3941909
theorem B1751539 : Blo 1383511 1751539 := bstep (se 1 (by rfl) ⟨1313654, by rfl⟩ : syracuseStep 1751539 = 2627309) B2627309
theorem B11983373 : Blo 1383511 11983373 := bstep (se 3 (by rfl) ⟨2246882, by rfl⟩ : syracuseStep 11983373 = 4493765) B4493765
theorem B5913101 : Blo 1383511 5913101 := bstep (se 3 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 5913101 = 2217413) B2217413
theorem B13310477 : Blo 1383511 13310477 := bstep (se 3 (by rfl) ⟨2495714, by rfl⟩ : syracuseStep 13310477 = 4991429) B4991429
theorem B1751635 : Blo 1383511 1751635 := bstep (se 1 (by rfl) ⟨1313726, by rfl⟩ : syracuseStep 1751635 = 2627453) B2627453
theorem B2628227 : Blo 1383511 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B6650531 : Blo 1383511 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B2955953 : Blo 1383511 2955953 := bstep (se 2 (by rfl) ⟨1108482, by rfl⟩ : syracuseStep 2955953 = 2216965) B2216965
theorem B3742481 : Blo 1383511 3742481 := bstep (se 2 (by rfl) ⟨1403430, by rfl⟩ : syracuseStep 3742481 = 2806861) B2806861
theorem B3373841 : Blo 1383511 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B2104129 : Blo 1383511 2104129 := bstep (se 2 (by rfl) ⟨789048, by rfl⟩ : syracuseStep 2104129 = 1578097) B1578097
theorem B9468913 : Blo 1383511 9468913 := bstep (se 2 (by rfl) ⟨3550842, by rfl⟩ : syracuseStep 9468913 = 7101685) B7101685
theorem B56835125 : Blo 1383511 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B1752131 : Blo 1383511 1752131 := bstep (se 1 (by rfl) ⟨1314098, by rfl⟩ : syracuseStep 1752131 = 2628197) B2628197
theorem B7887941 : Blo 1383511 7887941 := bstep (se 4 (by rfl) ⟨739494, by rfl⟩ : syracuseStep 7887941 = 1478989) B1478989
theorem B2219105 : Blo 1383511 2219105 := bstep (se 2 (by rfl) ⟨832164, by rfl⟩ : syracuseStep 2219105 = 1664329) B1664329
theorem B1383523 : Blo 1383511 1383523 := bstep (se 1 (by rfl) ⟨1037642, by rfl⟩ : syracuseStep 1383523 = 2075285) B2075285
theorem B3505265 : Blo 1383511 3505265 := bstep (se 2 (by rfl) ⟨1314474, by rfl⟩ : syracuseStep 3505265 = 2628949) B2628949
theorem B1383539 : Blo 1383511 1383539 := bstep (se 1 (by rfl) ⟨1037654, by rfl⟩ : syracuseStep 1383539 = 2075309) B2075309
theorem B1383555 : Blo 1383511 1383555 := bstep (se 1 (by rfl) ⟨1037666, by rfl⟩ : syracuseStep 1383555 = 2075333) B2075333
theorem B3554435 : Blo 1383511 3554435 := bstep (se 1 (by rfl) ⟨2665826, by rfl⟩ : syracuseStep 3554435 = 5331653) B5331653
theorem B1383571 : Blo 1383511 1383571 := bstep (se 1 (by rfl) ⟨1037678, by rfl⟩ : syracuseStep 1383571 = 2075357) B2075357
theorem B1383587 : Blo 1383511 1383587 := bstep (se 1 (by rfl) ⟨1037690, by rfl⟩ : syracuseStep 1383587 = 2075381) B2075381
theorem B3505315 : Blo 1383511 3505315 := bstep (se 1 (by rfl) ⟨2628986, by rfl⟩ : syracuseStep 3505315 = 5257973) B5257973
theorem B1383603 : Blo 1383511 1383603 := bstep (se 1 (by rfl) ⟨1037702, by rfl⟩ : syracuseStep 1383603 = 2075405) B2075405
theorem B1383619 : Blo 1383511 1383619 := bstep (se 1 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 1383619 = 2075429) B2075429
theorem B1383635 : Blo 1383511 1383635 := bstep (se 1 (by rfl) ⟨1037726, by rfl⟩ : syracuseStep 1383635 = 2075453) B2075453
theorem B2219233 : Blo 1383511 2219233 := bstep (se 2 (by rfl) ⟨832212, by rfl⟩ : syracuseStep 2219233 = 1664425) B1664425
theorem B1383651 : Blo 1383511 1383651 := bstep (se 1 (by rfl) ⟨1037738, by rfl⟩ : syracuseStep 1383651 = 2075477) B2075477
theorem B1383667 : Blo 1383511 1383667 := bstep (se 1 (by rfl) ⟨1037750, by rfl⟩ : syracuseStep 1383667 = 2075501) B2075501
theorem B1383683 : Blo 1383511 1383683 := bstep (se 1 (by rfl) ⟨1037762, by rfl⟩ : syracuseStep 1383683 = 2075525) B2075525
theorem B1383699 : Blo 1383511 1383699 := bstep (se 1 (by rfl) ⟨1037774, by rfl⟩ : syracuseStep 1383699 = 2075549) B2075549
theorem B1383715 : Blo 1383511 1383715 := bstep (se 1 (by rfl) ⟨1037786, by rfl⟩ : syracuseStep 1383715 = 2075573) B2075573
theorem B4209965 : Blo 1383511 4209965 := bstep (se 3 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 4209965 = 1578737) B1578737
theorem B3505457 : Blo 1383511 3505457 := bstep (se 2 (by rfl) ⟨1314546, by rfl⟩ : syracuseStep 3505457 = 2629093) B2629093
theorem B1383731 : Blo 1383511 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B1383747 : Blo 1383511 1383747 := bstep (se 1 (by rfl) ⟨1037810, by rfl⟩ : syracuseStep 1383747 = 2075621) B2075621
theorem B1383763 : Blo 1383511 1383763 := bstep (se 1 (by rfl) ⟨1037822, by rfl⟩ : syracuseStep 1383763 = 2075645) B2075645
theorem B1383779 : Blo 1383511 1383779 := bstep (se 1 (by rfl) ⟨1037834, by rfl⟩ : syracuseStep 1383779 = 2075669) B2075669
theorem B7011683 : Blo 1383511 7011683 := bstep (se 1 (by rfl) ⟨5258762, by rfl⟩ : syracuseStep 7011683 = 10517525) B10517525
theorem B1383795 : Blo 1383511 1383795 := bstep (se 1 (by rfl) ⟨1037846, by rfl⟩ : syracuseStep 1383795 = 2075693) B2075693
theorem B1383811 : Blo 1383511 1383811 := bstep (se 1 (by rfl) ⟨1037858, by rfl⟩ : syracuseStep 1383811 = 2075717) B2075717
theorem B1383827 : Blo 1383511 1383827 := bstep (se 1 (by rfl) ⟨1037870, by rfl⟩ : syracuseStep 1383827 = 2075741) B2075741
theorem B1383843 : Blo 1383511 1383843 := bstep (se 1 (by rfl) ⟨1037882, by rfl⟩ : syracuseStep 1383843 = 2075765) B2075765
theorem B1383859 : Blo 1383511 1383859 := bstep (se 1 (by rfl) ⟨1037894, by rfl⟩ : syracuseStep 1383859 = 2075789) B2075789
theorem B3939779 : Blo 1383511 3939779 := bstep (se 1 (by rfl) ⟨2954834, by rfl⟩ : syracuseStep 3939779 = 5909669) B5909669
theorem B1383875 : Blo 1383511 1383875 := bstep (se 1 (by rfl) ⟨1037906, by rfl⟩ : syracuseStep 1383875 = 2075813) B2075813
theorem B2997713 : Blo 1383511 2997713 := bstep (se 2 (by rfl) ⟨1124142, by rfl⟩ : syracuseStep 2997713 = 2248285) B2248285
theorem B1383891 : Blo 1383511 1383891 := bstep (se 1 (by rfl) ⟨1037918, by rfl⟩ : syracuseStep 1383891 = 2075837) B2075837
theorem B1383907 : Blo 1383511 1383907 := bstep (se 1 (by rfl) ⟨1037930, by rfl⟩ : syracuseStep 1383907 = 2075861) B2075861
theorem B1383923 : Blo 1383511 1383923 := bstep (se 1 (by rfl) ⟨1037942, by rfl⟩ : syracuseStep 1383923 = 2075885) B2075885
theorem B1383939 : Blo 1383511 1383939 := bstep (se 1 (by rfl) ⟨1037954, by rfl⟩ : syracuseStep 1383939 = 2075909) B2075909
theorem B2956817 : Blo 1383511 2956817 := bstep (se 2 (by rfl) ⟨1108806, by rfl⟩ : syracuseStep 2956817 = 2217613) B2217613
theorem B1383955 : Blo 1383511 1383955 := bstep (se 1 (by rfl) ⟨1037966, by rfl⟩ : syracuseStep 1383955 = 2075933) B2075933
theorem B1383971 : Blo 1383511 1383971 := bstep (se 1 (by rfl) ⟨1037978, by rfl⟩ : syracuseStep 1383971 = 2075957) B2075957
theorem B2629169 : Blo 1383511 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B1383987 : Blo 1383511 1383987 := bstep (se 1 (by rfl) ⟨1037990, by rfl⟩ : syracuseStep 1383987 = 2075981) B2075981
theorem B1384003 : Blo 1383511 1384003 := bstep (se 1 (by rfl) ⟨1038002, by rfl⟩ : syracuseStep 1384003 = 2076005) B2076005
theorem B1384019 : Blo 1383511 1384019 := bstep (se 1 (by rfl) ⟨1038014, by rfl⟩ : syracuseStep 1384019 = 2076029) B2076029
theorem B1384035 : Blo 1383511 1384035 := bstep (se 1 (by rfl) ⟨1038026, by rfl⟩ : syracuseStep 1384035 = 2076053) B2076053
theorem B1384051 : Blo 1383511 1384051 := bstep (se 1 (by rfl) ⟨1038038, by rfl⟩ : syracuseStep 1384051 = 2076077) B2076077
theorem B1384067 : Blo 1383511 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B1384083 : Blo 1383511 1384083 := bstep (se 1 (by rfl) ⟨1038062, by rfl⟩ : syracuseStep 1384083 = 2076125) B2076125
theorem B1384099 : Blo 1383511 1384099 := bstep (se 1 (by rfl) ⟨1038074, by rfl⟩ : syracuseStep 1384099 = 2076149) B2076149
theorem B5258915 : Blo 1383511 5258915 := bstep (se 1 (by rfl) ⟨3944186, by rfl⟩ : syracuseStep 5258915 = 7888373) B7888373
theorem B1384115 : Blo 1383511 1384115 := bstep (se 1 (by rfl) ⟨1038086, by rfl⟩ : syracuseStep 1384115 = 2076173) B2076173
theorem B1384131 : Blo 1383511 1384131 := bstep (se 1 (by rfl) ⟨1038098, by rfl⟩ : syracuseStep 1384131 = 2076197) B2076197
theorem B1384147 : Blo 1383511 1384147 := bstep (se 1 (by rfl) ⟨1038110, by rfl⟩ : syracuseStep 1384147 = 2076221) B2076221
theorem B1384163 : Blo 1383511 1384163 := bstep (se 1 (by rfl) ⟨1038122, by rfl⟩ : syracuseStep 1384163 = 2076245) B2076245
theorem B1384179 : Blo 1383511 1384179 := bstep (se 1 (by rfl) ⟨1038134, by rfl⟩ : syracuseStep 1384179 = 2076269) B2076269
theorem B1384195 : Blo 1383511 1384195 := bstep (se 1 (by rfl) ⟨1038146, by rfl⟩ : syracuseStep 1384195 = 2076293) B2076293
theorem B1752835 : Blo 1383511 1752835 := bstep (se 1 (by rfl) ⟨1314626, by rfl⟩ : syracuseStep 1752835 = 2629253) B2629253
theorem B3940109 : Blo 1383511 3940109 := bstep (se 3 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 3940109 = 1477541) B1477541
theorem B1384211 : Blo 1383511 1384211 := bstep (se 1 (by rfl) ⟨1038158, by rfl⟩ : syracuseStep 1384211 = 2076317) B2076317
theorem B1384227 : Blo 1383511 1384227 := bstep (se 1 (by rfl) ⟨1038170, by rfl⟩ : syracuseStep 1384227 = 2076341) B2076341
theorem B1384243 : Blo 1383511 1384243 := bstep (se 1 (by rfl) ⟨1038182, by rfl⟩ : syracuseStep 1384243 = 2076365) B2076365
theorem B1384259 : Blo 1383511 1384259 := bstep (se 1 (by rfl) ⟨1038194, by rfl⟩ : syracuseStep 1384259 = 2076389) B2076389
theorem B3940177 : Blo 1383511 3940177 := bstep (se 2 (by rfl) ⟨1477566, by rfl⟩ : syracuseStep 3940177 = 2955133) B2955133
theorem B1384275 : Blo 1383511 1384275 := bstep (se 1 (by rfl) ⟨1038206, by rfl⟩ : syracuseStep 1384275 = 2076413) B2076413
theorem B1384291 : Blo 1383511 1384291 := bstep (se 1 (by rfl) ⟨1038218, by rfl⟩ : syracuseStep 1384291 = 2076437) B2076437
theorem B1752931 : Blo 1383511 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B17080163 : Blo 1383511 17080163 := bstep (se 1 (by rfl) ⟨12810122, by rfl⟩ : syracuseStep 17080163 = 25620245) B25620245
theorem B1384307 : Blo 1383511 1384307 := bstep (se 1 (by rfl) ⟨1038230, by rfl⟩ : syracuseStep 1384307 = 2076461) B2076461
theorem B1384323 : Blo 1383511 1384323 := bstep (se 1 (by rfl) ⟨1038242, by rfl⟩ : syracuseStep 1384323 = 2076485) B2076485
theorem B1384339 : Blo 1383511 1384339 := bstep (se 1 (by rfl) ⟨1038254, by rfl⟩ : syracuseStep 1384339 = 2076509) B2076509
theorem B1384355 : Blo 1383511 1384355 := bstep (se 1 (by rfl) ⟨1038266, by rfl⟩ : syracuseStep 1384355 = 2076533) B2076533
theorem B1384371 : Blo 1383511 1384371 := bstep (se 1 (by rfl) ⟨1038278, by rfl⟩ : syracuseStep 1384371 = 2076557) B2076557
theorem B4669379 : Blo 1383511 4669379 := bstep (se 1 (by rfl) ⟨3502034, by rfl⟩ : syracuseStep 4669379 = 7004069) B7004069
theorem B1384387 : Blo 1383511 1384387 := bstep (se 1 (by rfl) ⟨1038290, by rfl⟩ : syracuseStep 1384387 = 2076581) B2076581
theorem B1384403 : Blo 1383511 1384403 := bstep (se 1 (by rfl) ⟨1038302, by rfl⟩ : syracuseStep 1384403 = 2076605) B2076605
theorem B19947491 : Blo 1383511 19947491 := bstep (se 1 (by rfl) ⟨14960618, by rfl⟩ : syracuseStep 19947491 = 29921237) B29921237
theorem B1384419 : Blo 1383511 1384419 := bstep (se 1 (by rfl) ⟨1038314, by rfl⟩ : syracuseStep 1384419 = 2076629) B2076629
theorem B1384435 : Blo 1383511 1384435 := bstep (se 1 (by rfl) ⟨1038326, by rfl⟩ : syracuseStep 1384435 = 2076653) B2076653
theorem B11231237 : Blo 1383511 11231237 := bstep (se 4 (by rfl) ⟨1052928, by rfl⟩ : syracuseStep 11231237 = 2105857) B2105857
theorem B1556491 : Blo 1383511 1556491 := bstep (se 1 (by rfl) ⟨1167368, by rfl⟩ : syracuseStep 1556491 = 2334737) B2334737
theorem B1384459 : Blo 1383511 1384459 := bstep (se 1 (by rfl) ⟨1038344, by rfl⟩ : syracuseStep 1384459 = 2076689) B2076689
theorem B4988951 : Blo 1383511 4988951 := bstep (se 1 (by rfl) ⟨3741713, by rfl⟩ : syracuseStep 4988951 = 7483427) B7483427
theorem B1384471 : Blo 1383511 1384471 := bstep (se 1 (by rfl) ⟨1038353, by rfl⟩ : syracuseStep 1384471 = 2076707) B2076707
theorem B2629655 : Blo 1383511 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B1384491 : Blo 1383511 1384491 := bstep (se 1 (by rfl) ⟨1038368, by rfl⟩ : syracuseStep 1384491 = 2076737) B2076737
theorem B1384503 : Blo 1383511 1384503 := bstep (se 1 (by rfl) ⟨1038377, by rfl⟩ : syracuseStep 1384503 = 2076755) B2076755
theorem B3940427 : Blo 1383511 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1384523 : Blo 1383511 1384523 := bstep (se 1 (by rfl) ⟨1038392, by rfl⟩ : syracuseStep 1384523 = 2076785) B2076785
theorem B1384535 : Blo 1383511 1384535 := bstep (se 1 (by rfl) ⟨1038401, by rfl⟩ : syracuseStep 1384535 = 2076803) B2076803
theorem B1384555 : Blo 1383511 1384555 := bstep (se 1 (by rfl) ⟨1038416, by rfl⟩ : syracuseStep 1384555 = 2076833) B2076833
theorem B1556599 : Blo 1383511 1556599 := bstep (se 1 (by rfl) ⟨1167449, by rfl⟩ : syracuseStep 1556599 = 2334899) B2334899
theorem B1384567 : Blo 1383511 1384567 := bstep (se 1 (by rfl) ⟨1038425, by rfl⟩ : syracuseStep 1384567 = 2076851) B2076851
theorem B3113099 : Blo 1383511 3113099 := bstep (se 1 (by rfl) ⟨2334824, by rfl⟩ : syracuseStep 3113099 = 4669649) B4669649
theorem B1384587 : Blo 1383511 1384587 := bstep (se 1 (by rfl) ⟨1038440, by rfl⟩ : syracuseStep 1384587 = 2076881) B2076881
theorem B1384599 : Blo 1383511 1384599 := bstep (se 1 (by rfl) ⟨1038449, by rfl⟩ : syracuseStep 1384599 = 2076899) B2076899
theorem B1384619 : Blo 1383511 1384619 := bstep (se 1 (by rfl) ⟨1038464, by rfl⟩ : syracuseStep 1384619 = 2076929) B2076929
theorem B1384631 : Blo 1383511 1384631 := bstep (se 1 (by rfl) ⟨1038473, by rfl⟩ : syracuseStep 1384631 = 2076947) B2076947
theorem B3113153 : Blo 1383511 3113153 := bstep (se 2 (by rfl) ⟨1167432, by rfl⟩ : syracuseStep 3113153 = 2334865) B2334865
theorem B1384651 : Blo 1383511 1384651 := bstep (se 1 (by rfl) ⟨1038488, by rfl⟩ : syracuseStep 1384651 = 2076977) B2076977
theorem B1384663 : Blo 1383511 1384663 := bstep (se 1 (by rfl) ⟨1038497, by rfl⟩ : syracuseStep 1384663 = 2076995) B2076995
theorem B5054681 : Blo 1383511 5054681 := bstep (se 2 (by rfl) ⟨1895505, by rfl⟩ : syracuseStep 5054681 = 3791011) B3791011
theorem B1384683 : Blo 1383511 1384683 := bstep (se 1 (by rfl) ⟨1038512, by rfl⟩ : syracuseStep 1384683 = 2077025) B2077025
theorem B1384695 : Blo 1383511 1384695 := bstep (se 1 (by rfl) ⟨1038521, by rfl⟩ : syracuseStep 1384695 = 2077043) B2077043
theorem B1384715 : Blo 1383511 1384715 := bstep (se 1 (by rfl) ⟨1038536, by rfl⟩ : syracuseStep 1384715 = 2077073) B2077073
theorem B1384727 : Blo 1383511 1384727 := bstep (se 1 (by rfl) ⟨1038545, by rfl⟩ : syracuseStep 1384727 = 2077091) B2077091
theorem B1999127 : Blo 1383511 1999127 := bstep (se 1 (by rfl) ⟨1499345, by rfl⟩ : syracuseStep 1999127 = 2998691) B2998691
theorem B1556779 : Blo 1383511 1556779 := bstep (se 1 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 1556779 = 2335169) B2335169
theorem B1384747 : Blo 1383511 1384747 := bstep (se 1 (by rfl) ⟨1038560, by rfl⟩ : syracuseStep 1384747 = 2077121) B2077121
theorem B1384759 : Blo 1383511 1384759 := bstep (se 1 (by rfl) ⟨1038569, by rfl⟩ : syracuseStep 1384759 = 2077139) B2077139
theorem B1384779 : Blo 1383511 1384779 := bstep (se 1 (by rfl) ⟨1038584, by rfl⟩ : syracuseStep 1384779 = 2077169) B2077169
theorem B1384791 : Blo 1383511 1384791 := bstep (se 1 (by rfl) ⟨1038593, by rfl⟩ : syracuseStep 1384791 = 2077187) B2077187
theorem B5259613 : Blo 1383511 5259613 := bstep (se 3 (by rfl) ⟨986177, by rfl⟩ : syracuseStep 5259613 = 1972355) B1972355
theorem B1384811 : Blo 1383511 1384811 := bstep (se 1 (by rfl) ⟨1038608, by rfl⟩ : syracuseStep 1384811 = 2077217) B2077217
theorem B1384823 : Blo 1383511 1384823 := bstep (se 1 (by rfl) ⟨1038617, by rfl⟩ : syracuseStep 1384823 = 2077235) B2077235
theorem B9986435 : Blo 1383511 9986435 := bstep (se 1 (by rfl) ⟨7489826, by rfl⟩ : syracuseStep 9986435 = 14979653) B14979653
theorem B2335115 : Blo 1383511 2335115 := bstep (se 1 (by rfl) ⟨1751336, by rfl⟩ : syracuseStep 2335115 = 3502673) B3502673
theorem B1384843 : Blo 1383511 1384843 := bstep (se 1 (by rfl) ⟨1038632, by rfl⟩ : syracuseStep 1384843 = 2077265) B2077265
theorem B1753483 : Blo 1383511 1753483 := bstep (se 1 (by rfl) ⟨1315112, by rfl⟩ : syracuseStep 1753483 = 2630225) B2630225
theorem B1556887 : Blo 1383511 1556887 := bstep (se 1 (by rfl) ⟨1167665, by rfl⟩ : syracuseStep 1556887 = 2335331) B2335331
theorem B1384855 : Blo 1383511 1384855 := bstep (se 1 (by rfl) ⟨1038641, by rfl⟩ : syracuseStep 1384855 = 2077283) B2077283
theorem B3113369 : Blo 1383511 3113369 := bstep (se 2 (by rfl) ⟨1167513, by rfl⟩ : syracuseStep 3113369 = 2335027) B2335027
theorem B1384875 : Blo 1383511 1384875 := bstep (se 1 (by rfl) ⟨1038656, by rfl⟩ : syracuseStep 1384875 = 2077313) B2077313
theorem B3506611 : Blo 1383511 3506611 := bstep (se 1 (by rfl) ⟨2629958, by rfl⟩ : syracuseStep 3506611 = 5259917) B5259917
theorem B1384887 : Blo 1383511 1384887 := bstep (se 1 (by rfl) ⟨1038665, by rfl⟩ : syracuseStep 1384887 = 2077331) B2077331
theorem B1384907 : Blo 1383511 1384907 := bstep (se 1 (by rfl) ⟨1038680, by rfl⟩ : syracuseStep 1384907 = 2077361) B2077361
theorem B1384919 : Blo 1383511 1384919 := bstep (se 1 (by rfl) ⟨1038689, by rfl⟩ : syracuseStep 1384919 = 2077379) B2077379
theorem B1384939 : Blo 1383511 1384939 := bstep (se 1 (by rfl) ⟨1038704, by rfl⟩ : syracuseStep 1384939 = 2077409) B2077409
theorem B3113459 : Blo 1383511 3113459 := bstep (se 1 (by rfl) ⟨2335094, by rfl⟩ : syracuseStep 3113459 = 4670189) B4670189
theorem B1384951 : Blo 1383511 1384951 := bstep (se 1 (by rfl) ⟨1038713, by rfl⟩ : syracuseStep 1384951 = 2077427) B2077427
theorem B2335243 : Blo 1383511 2335243 := bstep (se 1 (by rfl) ⟨1751432, by rfl⟩ : syracuseStep 2335243 = 3502865) B3502865
theorem B1384971 : Blo 1383511 1384971 := bstep (se 1 (by rfl) ⟨1038728, by rfl⟩ : syracuseStep 1384971 = 2077457) B2077457
theorem B3113495 : Blo 1383511 3113495 := bstep (se 1 (by rfl) ⟨2335121, by rfl⟩ : syracuseStep 3113495 = 4670243) B4670243
theorem B1384983 : Blo 1383511 1384983 := bstep (se 1 (by rfl) ⟨1038737, by rfl⟩ : syracuseStep 1384983 = 2077475) B2077475
theorem B1385003 : Blo 1383511 1385003 := bstep (se 1 (by rfl) ⟨1038752, by rfl⟩ : syracuseStep 1385003 = 2077505) B2077505
theorem B7004717 : Blo 1383511 7004717 := bstep (se 3 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 7004717 = 2626769) B2626769
theorem B1385015 : Blo 1383511 1385015 := bstep (se 1 (by rfl) ⟨1038761, by rfl⟩ : syracuseStep 1385015 = 2077523) B2077523
theorem B3506753 : Blo 1383511 3506753 := bstep (se 2 (by rfl) ⟨1315032, by rfl⟩ : syracuseStep 3506753 = 2630065) B2630065
theorem B4670027 : Blo 1383511 4670027 := bstep (se 1 (by rfl) ⟨3502520, by rfl⟩ : syracuseStep 4670027 = 7005041) B7005041
theorem B1557067 : Blo 1383511 1557067 := bstep (se 1 (by rfl) ⟨1167800, by rfl⟩ : syracuseStep 1557067 = 2335601) B2335601
theorem B8872523 : Blo 1383511 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B1385035 : Blo 1383511 1385035 := bstep (se 1 (by rfl) ⟨1038776, by rfl⟩ : syracuseStep 1385035 = 2077553) B2077553
theorem B1385047 : Blo 1383511 1385047 := bstep (se 1 (by rfl) ⟨1038785, by rfl⟩ : syracuseStep 1385047 = 2077571) B2077571
theorem B1385067 : Blo 1383511 1385067 := bstep (se 1 (by rfl) ⟨1038800, by rfl⟩ : syracuseStep 1385067 = 2077601) B2077601
theorem B1385079 : Blo 1383511 1385079 := bstep (se 1 (by rfl) ⟨1038809, by rfl⟩ : syracuseStep 1385079 = 2077619) B2077619
theorem B14959235 : Blo 1383511 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B6652547 : Blo 1383511 6652547 := bstep (se 1 (by rfl) ⟨4989410, by rfl⟩ : syracuseStep 6652547 = 9978821) B9978821
theorem B8422019 : Blo 1383511 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B1385099 : Blo 1383511 1385099 := bstep (se 1 (by rfl) ⟨1038824, by rfl⟩ : syracuseStep 1385099 = 2077649) B2077649
theorem B1385111 : Blo 1383511 1385111 := bstep (se 1 (by rfl) ⟨1038833, by rfl⟩ : syracuseStep 1385111 = 2077667) B2077667
theorem B2335385 : Blo 1383511 2335385 := bstep (se 2 (by rfl) ⟨875769, by rfl⟩ : syracuseStep 2335385 = 1751539) B1751539
theorem B1385131 : Blo 1383511 1385131 := bstep (se 1 (by rfl) ⟨1038848, by rfl⟩ : syracuseStep 1385131 = 2077697) B2077697
theorem B1557175 : Blo 1383511 1557175 := bstep (se 1 (by rfl) ⟨1167881, by rfl⟩ : syracuseStep 1557175 = 2335763) B2335763
theorem B1385143 : Blo 1383511 1385143 := bstep (se 1 (by rfl) ⟨1038857, by rfl⟩ : syracuseStep 1385143 = 2077715) B2077715
theorem B3113675 : Blo 1383511 3113675 := bstep (se 1 (by rfl) ⟨2335256, by rfl⟩ : syracuseStep 3113675 = 4670513) B4670513
theorem B1385163 : Blo 1383511 1385163 := bstep (se 1 (by rfl) ⟨1038872, by rfl⟩ : syracuseStep 1385163 = 2077745) B2077745
theorem B1385175 : Blo 1383511 1385175 := bstep (se 1 (by rfl) ⟨1038881, by rfl⟩ : syracuseStep 1385175 = 2077763) B2077763
theorem B4735705 : Blo 1383511 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B1385195 : Blo 1383511 1385195 := bstep (se 1 (by rfl) ⟨1038896, by rfl⟩ : syracuseStep 1385195 = 2077793) B2077793
theorem B1385207 : Blo 1383511 1385207 := bstep (se 1 (by rfl) ⟨1038905, by rfl⟩ : syracuseStep 1385207 = 2077811) B2077811
theorem B3113729 : Blo 1383511 3113729 := bstep (se 2 (by rfl) ⟨1167648, by rfl⟩ : syracuseStep 3113729 = 2335297) B2335297
theorem B1385227 : Blo 1383511 1385227 := bstep (se 1 (by rfl) ⟨1038920, by rfl⟩ : syracuseStep 1385227 = 2077841) B2077841
theorem B1385239 : Blo 1383511 1385239 := bstep (se 1 (by rfl) ⟨1038929, by rfl⟩ : syracuseStep 1385239 = 2077859) B2077859
theorem B2335513 : Blo 1383511 2335513 := bstep (se 2 (by rfl) ⟨875817, by rfl⟩ : syracuseStep 2335513 = 1751635) B1751635
theorem B1385259 : Blo 1383511 1385259 := bstep (se 1 (by rfl) ⟨1038944, by rfl⟩ : syracuseStep 1385259 = 2077889) B2077889
theorem B95920949 : Blo 1383511 95920949 := bstep (se 5 (by rfl) ⟨4496294, by rfl⟩ : syracuseStep 95920949 = 8992589) B8992589
theorem B1385271 : Blo 1383511 1385271 := bstep (se 1 (by rfl) ⟨1038953, by rfl⟩ : syracuseStep 1385271 = 2077907) B2077907
theorem B1385291 : Blo 1383511 1385291 := bstep (se 1 (by rfl) ⟨1038968, by rfl⟩ : syracuseStep 1385291 = 2077937) B2077937
theorem B1385303 : Blo 1383511 1385303 := bstep (se 1 (by rfl) ⟨1038977, by rfl⟩ : syracuseStep 1385303 = 2077955) B2077955
theorem B4670297 : Blo 1383511 4670297 := bstep (se 2 (by rfl) ⟨1751361, by rfl⟩ : syracuseStep 4670297 = 3502723) B3502723
theorem B1557355 : Blo 1383511 1557355 := bstep (se 1 (by rfl) ⟨1168016, by rfl⟩ : syracuseStep 1557355 = 2336033) B2336033
theorem B1385323 : Blo 1383511 1385323 := bstep (se 1 (by rfl) ⟨1038992, by rfl⟩ : syracuseStep 1385323 = 2077985) B2077985
theorem B1385335 : Blo 1383511 1385335 := bstep (se 1 (by rfl) ⟨1039001, by rfl⟩ : syracuseStep 1385335 = 2078003) B2078003
theorem B1385355 : Blo 1383511 1385355 := bstep (se 1 (by rfl) ⟨1039016, by rfl⟩ : syracuseStep 1385355 = 2078033) B2078033
theorem B1385367 : Blo 1383511 1385367 := bstep (se 1 (by rfl) ⟨1039025, by rfl⟩ : syracuseStep 1385367 = 2078051) B2078051
theorem B1385387 : Blo 1383511 1385387 := bstep (se 1 (by rfl) ⟨1039040, by rfl⟩ : syracuseStep 1385387 = 2078081) B2078081
theorem B1385399 : Blo 1383511 1385399 := bstep (se 1 (by rfl) ⟨1039049, by rfl⟩ : syracuseStep 1385399 = 2078099) B2078099
theorem B1385419 : Blo 1383511 1385419 := bstep (se 1 (by rfl) ⟨1039064, by rfl⟩ : syracuseStep 1385419 = 2078129) B2078129
theorem B1557463 : Blo 1383511 1557463 := bstep (se 1 (by rfl) ⟨1168097, by rfl⟩ : syracuseStep 1557463 = 2336195) B2336195
theorem B1385431 : Blo 1383511 1385431 := bstep (se 1 (by rfl) ⟨1039073, by rfl⟩ : syracuseStep 1385431 = 2078147) B2078147
theorem B3113945 : Blo 1383511 3113945 := bstep (se 2 (by rfl) ⟨1167729, by rfl⟩ : syracuseStep 3113945 = 2335459) B2335459
theorem B1385451 : Blo 1383511 1385451 := bstep (se 1 (by rfl) ⟨1039088, by rfl⟩ : syracuseStep 1385451 = 2078177) B2078177
theorem B1385463 : Blo 1383511 1385463 := bstep (se 1 (by rfl) ⟨1039097, by rfl⟩ : syracuseStep 1385463 = 2078195) B2078195
theorem B1385483 : Blo 1383511 1385483 := bstep (se 1 (by rfl) ⟨1039112, by rfl⟩ : syracuseStep 1385483 = 2078225) B2078225
theorem B1385495 : Blo 1383511 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B3114035 : Blo 1383511 3114035 := bstep (se 1 (by rfl) ⟨2335526, by rfl⟩ : syracuseStep 3114035 = 4671053) B4671053
theorem B5915699 : Blo 1383511 5915699 := bstep (se 1 (by rfl) ⟨4436774, by rfl⟩ : syracuseStep 5915699 = 8873549) B8873549
theorem B50521157 : Blo 1383511 50521157 := bstep (se 4 (by rfl) ⟨4736358, by rfl⟩ : syracuseStep 50521157 = 9472717) B9472717
theorem B3114071 : Blo 1383511 3114071 := bstep (se 1 (by rfl) ⟨2335553, by rfl⟩ : syracuseStep 3114071 = 4671107) B4671107
theorem B11830373 : Blo 1383511 11830373 := bstep (se 4 (by rfl) ⟨1109097, by rfl⟩ : syracuseStep 11830373 = 2218195) B2218195
theorem B7488613 : Blo 1383511 7488613 := bstep (se 4 (by rfl) ⟨702057, by rfl⟩ : syracuseStep 7488613 = 1404115) B1404115
theorem B1557643 : Blo 1383511 1557643 := bstep (se 1 (by rfl) ⟨1168232, by rfl⟩ : syracuseStep 1557643 = 2336465) B2336465
theorem B4990103 : Blo 1383511 4990103 := bstep (se 1 (by rfl) ⟨3742577, by rfl⟩ : syracuseStep 4990103 = 7485155) B7485155
theorem B1557751 : Blo 1383511 1557751 := bstep (se 1 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 1557751 = 2336627) B2336627
theorem B3114251 : Blo 1383511 3114251 := bstep (se 1 (by rfl) ⟨2335688, by rfl⟩ : syracuseStep 3114251 = 4671377) B4671377
theorem B39912749 : Blo 1383511 39912749 := bstep (se 3 (by rfl) ⟨7483640, by rfl⟩ : syracuseStep 39912749 = 14967281) B14967281
theorem B12625217 : Blo 1383511 12625217 := bstep (se 2 (by rfl) ⟨4734456, by rfl⟩ : syracuseStep 12625217 = 9468913) B9468913
theorem B3114305 : Blo 1383511 3114305 := bstep (se 2 (by rfl) ⟨1167864, by rfl⟩ : syracuseStep 3114305 = 2335729) B2335729
theorem B2336087 : Blo 1383511 2336087 := bstep (se 1 (by rfl) ⟨1752065, by rfl⟩ : syracuseStep 2336087 = 3504131) B3504131
theorem B1557931 : Blo 1383511 1557931 := bstep (se 1 (by rfl) ⟨1168448, by rfl⟩ : syracuseStep 1557931 = 2336897) B2336897
theorem B2336215 : Blo 1383511 2336215 := bstep (se 1 (by rfl) ⟨1752161, by rfl⟩ : syracuseStep 2336215 = 3504323) B3504323
theorem B4670999 : Blo 1383511 4670999 := bstep (se 1 (by rfl) ⟨3503249, by rfl⟩ : syracuseStep 4670999 = 7006499) B7006499
theorem B1558039 : Blo 1383511 1558039 := bstep (se 1 (by rfl) ⟨1168529, by rfl⟩ : syracuseStep 1558039 = 2337059) B2337059
theorem B3114521 : Blo 1383511 3114521 := bstep (se 2 (by rfl) ⟨1167945, by rfl⟩ : syracuseStep 3114521 = 2335891) B2335891
theorem B3114611 : Blo 1383511 3114611 := bstep (se 1 (by rfl) ⟨2335958, by rfl⟩ : syracuseStep 3114611 = 4671917) B4671917
theorem B2958977 : Blo 1383511 2958977 := bstep (se 2 (by rfl) ⟨1109616, by rfl⟩ : syracuseStep 2958977 = 2219233) B2219233
theorem B3114647 : Blo 1383511 3114647 := bstep (se 1 (by rfl) ⟨2335985, by rfl⟩ : syracuseStep 3114647 = 4671971) B4671971
theorem B7988915 : Blo 1383511 7988915 := bstep (se 1 (by rfl) ⟨5991686, by rfl⟩ : syracuseStep 7988915 = 11983373) B11983373
theorem B8873651 : Blo 1383511 8873651 := bstep (se 1 (by rfl) ⟨6655238, by rfl⟩ : syracuseStep 8873651 = 13310477) B13310477
theorem B1558219 : Blo 1383511 1558219 := bstep (se 1 (by rfl) ⟨1168664, by rfl⟩ : syracuseStep 1558219 = 2337329) B2337329
theorem B4433687 : Blo 1383511 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B7882541 : Blo 1383511 7882541 := bstep (se 3 (by rfl) ⟨1477976, by rfl⟩ : syracuseStep 7882541 = 2955953) B2955953
theorem B1558327 : Blo 1383511 1558327 := bstep (se 1 (by rfl) ⟨1168745, by rfl⟩ : syracuseStep 1558327 = 2337491) B2337491
theorem B3114827 : Blo 1383511 3114827 := bstep (se 1 (by rfl) ⟨2336120, by rfl⟩ : syracuseStep 3114827 = 4672241) B4672241
theorem B3114881 : Blo 1383511 3114881 := bstep (se 2 (by rfl) ⟨1168080, by rfl⟩ : syracuseStep 3114881 = 2336161) B2336161
theorem B3598273 : Blo 1383511 3598273 := bstep (se 2 (by rfl) ⟨1349352, by rfl⟩ : syracuseStep 3598273 = 2698705) B2698705
theorem B1558507 : Blo 1383511 1558507 := bstep (se 1 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 1558507 = 2337761) B2337761
theorem B37890083 : Blo 1383511 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B9979949 : Blo 1383511 9979949 := bstep (se 3 (by rfl) ⟨1871240, by rfl⟩ : syracuseStep 9979949 = 3742481) B3742481
theorem B4671539 : Blo 1383511 4671539 := bstep (se 1 (by rfl) ⟨3503654, by rfl⟩ : syracuseStep 4671539 = 7007309) B7007309
theorem B54716485 : Blo 1383511 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B2336843 : Blo 1383511 2336843 := bstep (se 1 (by rfl) ⟨1752632, by rfl⟩ : syracuseStep 2336843 = 3505265) B3505265
theorem B2369623 : Blo 1383511 2369623 := bstep (se 1 (by rfl) ⟨1777217, by rfl⟩ : syracuseStep 2369623 = 3554435) B3554435
theorem B1558615 : Blo 1383511 1558615 := bstep (se 1 (by rfl) ⟨1168961, by rfl⟩ : syracuseStep 1558615 = 2337923) B2337923
theorem B3115097 : Blo 1383511 3115097 := bstep (se 2 (by rfl) ⟨1168161, by rfl⟩ : syracuseStep 3115097 = 2336323) B2336323
theorem B15779933 : Blo 1383511 15779933 := bstep (se 3 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 15779933 = 5917475) B5917475
theorem B3115187 : Blo 1383511 3115187 := bstep (se 1 (by rfl) ⟨2336390, by rfl⟩ : syracuseStep 3115187 = 4672781) B4672781
theorem B4212929 : Blo 1383511 4212929 := bstep (se 2 (by rfl) ⟨1579848, by rfl⟩ : syracuseStep 4212929 = 3159697) B3159697
theorem B2336971 : Blo 1383511 2336971 := bstep (se 1 (by rfl) ⟨1752728, by rfl⟩ : syracuseStep 2336971 = 3505457) B3505457
theorem B3115223 : Blo 1383511 3115223 := bstep (se 1 (by rfl) ⟨2336417, by rfl⟩ : syracuseStep 3115223 = 4672835) B4672835
theorem B4671809 : Blo 1383511 4671809 := bstep (se 2 (by rfl) ⟨1751928, by rfl⟩ : syracuseStep 4671809 = 3503857) B3503857
theorem B2337113 : Blo 1383511 2337113 := bstep (se 2 (by rfl) ⟨876417, by rfl⟩ : syracuseStep 2337113 = 1752835) B1752835
theorem B7481693 : Blo 1383511 7481693 := bstep (se 3 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 7481693 = 2805635) B2805635
theorem B3115403 : Blo 1383511 3115403 := bstep (se 1 (by rfl) ⟨2336552, by rfl⟩ : syracuseStep 3115403 = 4673105) B4673105
theorem B5253569 : Blo 1383511 5253569 := bstep (se 2 (by rfl) ⟨1970088, by rfl⟩ : syracuseStep 5253569 = 3940177) B3940177
theorem B3115457 : Blo 1383511 3115457 := bstep (se 2 (by rfl) ⟨1168296, by rfl⟩ : syracuseStep 3115457 = 2336593) B2336593
theorem B2337241 : Blo 1383511 2337241 := bstep (se 2 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 2337241 = 1752931) B1752931
theorem B3942877 : Blo 1383511 3942877 := bstep (se 3 (by rfl) ⟨739289, by rfl⟩ : syracuseStep 3942877 = 1478579) B1478579
theorem B12634699 : Blo 1383511 12634699 := bstep (se 1 (by rfl) ⟨9476024, by rfl⟩ : syracuseStep 12634699 = 18952049) B18952049
theorem B13298327 : Blo 1383511 13298327 := bstep (se 1 (by rfl) ⟨9973745, by rfl⟩ : syracuseStep 13298327 = 19947491) B19947491
theorem B1870489 : Blo 1383511 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B3115673 : Blo 1383511 3115673 := bstep (se 2 (by rfl) ⟨1168377, by rfl⟩ : syracuseStep 3115673 = 2336755) B2336755
theorem B8096435 : Blo 1383511 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B2075339 : Blo 1383511 2075339 := bstep (se 1 (by rfl) ⟨1556504, by rfl⟩ : syracuseStep 2075339 = 3113009) B3113009
theorem B2075351 : Blo 1383511 2075351 := bstep (se 1 (by rfl) ⟨1556513, by rfl⟩ : syracuseStep 2075351 = 3113027) B3113027
theorem B3115763 : Blo 1383511 3115763 := bstep (se 1 (by rfl) ⟨2336822, by rfl⟩ : syracuseStep 3115763 = 4673645) B4673645
theorem B8866577 : Blo 1383511 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B3115799 : Blo 1383511 3115799 := bstep (se 1 (by rfl) ⟨2336849, by rfl⟩ : syracuseStep 3115799 = 4673699) B4673699
theorem B2075417 : Blo 1383511 2075417 := bstep (se 2 (by rfl) ⟨778281, by rfl⟩ : syracuseStep 2075417 = 1556563) B1556563
theorem B4672349 : Blo 1383511 4672349 := bstep (se 3 (by rfl) ⟨876065, by rfl⟩ : syracuseStep 4672349 = 1752131) B1752131
theorem B2075531 : Blo 1383511 2075531 := bstep (se 1 (by rfl) ⟨1556648, by rfl⟩ : syracuseStep 2075531 = 3113297) B3113297
theorem B2075543 : Blo 1383511 2075543 := bstep (se 1 (by rfl) ⟨1556657, by rfl⟩ : syracuseStep 2075543 = 3113315) B3113315
theorem B3156889 : Blo 1383511 3156889 := bstep (se 2 (by rfl) ⟨1183833, by rfl⟩ : syracuseStep 3156889 = 2367667) B2367667
theorem B22465457 : Blo 1383511 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B3115979 : Blo 1383511 3115979 := bstep (se 1 (by rfl) ⟨2336984, by rfl⟩ : syracuseStep 3115979 = 4673969) B4673969
theorem B2075609 : Blo 1383511 2075609 := bstep (se 2 (by rfl) ⟨778353, by rfl⟩ : syracuseStep 2075609 = 1556707) B1556707
theorem B3116033 : Blo 1383511 3116033 := bstep (se 2 (by rfl) ⟨1168512, by rfl⟩ : syracuseStep 3116033 = 2337025) B2337025
theorem B7482385 : Blo 1383511 7482385 := bstep (se 2 (by rfl) ⟨2805894, by rfl⟩ : syracuseStep 7482385 = 5611789) B5611789
theorem B2337815 : Blo 1383511 2337815 := bstep (se 1 (by rfl) ⟨1753361, by rfl⟩ : syracuseStep 2337815 = 3506723) B3506723
theorem B2075723 : Blo 1383511 2075723 := bstep (se 1 (by rfl) ⟨1556792, by rfl⟩ : syracuseStep 2075723 = 3113585) B3113585
theorem B2075735 : Blo 1383511 2075735 := bstep (se 1 (by rfl) ⟨1556801, by rfl⟩ : syracuseStep 2075735 = 3113603) B3113603
theorem B2804825 : Blo 1383511 2804825 := bstep (se 2 (by rfl) ⟨1051809, by rfl⟩ : syracuseStep 2804825 = 2103619) B2103619
theorem B2337943 : Blo 1383511 2337943 := bstep (se 1 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 2337943 = 3506915) B3506915
theorem B2075801 : Blo 1383511 2075801 := bstep (se 2 (by rfl) ⟨778425, by rfl⟩ : syracuseStep 2075801 = 1556851) B1556851
theorem B2804915 : Blo 1383511 2804915 := bstep (se 1 (by rfl) ⟨2103686, by rfl⟩ : syracuseStep 2804915 = 4207373) B4207373
theorem B3116249 : Blo 1383511 3116249 := bstep (se 2 (by rfl) ⟨1168593, by rfl⟩ : syracuseStep 3116249 = 2337187) B2337187
theorem B20221169 : Blo 1383511 20221169 := bstep (se 2 (by rfl) ⟨7582938, by rfl⟩ : syracuseStep 20221169 = 15165877) B15165877
theorem B2075915 : Blo 1383511 2075915 := bstep (se 1 (by rfl) ⟨1556936, by rfl⟩ : syracuseStep 2075915 = 3113873) B3113873
theorem B2075927 : Blo 1383511 2075927 := bstep (se 1 (by rfl) ⟨1556945, by rfl⟩ : syracuseStep 2075927 = 3113891) B3113891
theorem B3116339 : Blo 1383511 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B3116375 : Blo 1383511 3116375 := bstep (se 1 (by rfl) ⟨2337281, by rfl⟩ : syracuseStep 3116375 = 4674563) B4674563
theorem B2075993 : Blo 1383511 2075993 := bstep (se 2 (by rfl) ⟨778497, by rfl⟩ : syracuseStep 2075993 = 1556995) B1556995
theorem B1871257 : Blo 1383511 1871257 := bstep (se 2 (by rfl) ⟨701721, by rfl⟩ : syracuseStep 1871257 = 1403443) B1403443
theorem B5615021 : Blo 1383511 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B2076107 : Blo 1383511 2076107 := bstep (se 1 (by rfl) ⟨1557080, by rfl⟩ : syracuseStep 2076107 = 3114161) B3114161
theorem B2076119 : Blo 1383511 2076119 := bstep (se 1 (by rfl) ⟨1557089, by rfl⟩ : syracuseStep 2076119 = 3114179) B3114179
theorem B1478135 : Blo 1383511 1478135 := bstep (se 1 (by rfl) ⟨1108601, by rfl⟩ : syracuseStep 1478135 = 2217203) B2217203
theorem B3116555 : Blo 1383511 3116555 := bstep (se 1 (by rfl) ⟨2337416, by rfl⟩ : syracuseStep 3116555 = 4674833) B4674833
theorem B2076185 : Blo 1383511 2076185 := bstep (se 2 (by rfl) ⟨778569, by rfl⟩ : syracuseStep 2076185 = 1557139) B1557139
theorem B3116609 : Blo 1383511 3116609 := bstep (se 2 (by rfl) ⟨1168728, by rfl⟩ : syracuseStep 3116609 = 2337457) B2337457
theorem B2076299 : Blo 1383511 2076299 := bstep (se 1 (by rfl) ⟨1557224, by rfl⟩ : syracuseStep 2076299 = 3114449) B3114449
theorem B2076311 : Blo 1383511 2076311 := bstep (se 1 (by rfl) ⟨1557233, by rfl⟩ : syracuseStep 2076311 = 3114467) B3114467
theorem B11833037 : Blo 1383511 11833037 := bstep (se 3 (by rfl) ⟨2218694, by rfl⟩ : syracuseStep 11833037 = 4437389) B4437389
theorem B2076377 : Blo 1383511 2076377 := bstep (se 2 (by rfl) ⟨778641, by rfl⟩ : syracuseStep 2076377 = 1557283) B1557283
theorem B3944153 : Blo 1383511 3944153 := bstep (se 2 (by rfl) ⟨1479057, by rfl⟩ : syracuseStep 3944153 = 2958115) B2958115
theorem B3116825 : Blo 1383511 3116825 := bstep (se 2 (by rfl) ⟨1168809, by rfl⟩ : syracuseStep 3116825 = 2337619) B2337619
theorem B19967789 : Blo 1383511 19967789 := bstep (se 3 (by rfl) ⟨3743960, by rfl⟩ : syracuseStep 19967789 = 7487921) B7487921
theorem B2076491 : Blo 1383511 2076491 := bstep (se 1 (by rfl) ⟨1557368, by rfl⟩ : syracuseStep 2076491 = 3114737) B3114737
theorem B2076503 : Blo 1383511 2076503 := bstep (se 1 (by rfl) ⟨1557377, by rfl⟩ : syracuseStep 2076503 = 3114755) B3114755
theorem B3116915 : Blo 1383511 3116915 := bstep (se 1 (by rfl) ⟨2337686, by rfl⟩ : syracuseStep 3116915 = 4675373) B4675373
theorem B5255057 : Blo 1383511 5255057 := bstep (se 2 (by rfl) ⟨1970646, by rfl⟩ : syracuseStep 5255057 = 3941293) B3941293
theorem B3116951 : Blo 1383511 3116951 := bstep (se 1 (by rfl) ⟨2337713, by rfl⟩ : syracuseStep 3116951 = 4675427) B4675427
theorem B2076569 : Blo 1383511 2076569 := bstep (se 2 (by rfl) ⟨778713, by rfl⟩ : syracuseStep 2076569 = 1557427) B1557427
theorem B4673483 : Blo 1383511 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B2076683 : Blo 1383511 2076683 := bstep (se 1 (by rfl) ⟨1557512, by rfl⟩ : syracuseStep 2076683 = 3115025) B3115025
theorem B2076695 : Blo 1383511 2076695 := bstep (se 1 (by rfl) ⟨1557521, by rfl⟩ : syracuseStep 2076695 = 3115043) B3115043
theorem B3117131 : Blo 1383511 3117131 := bstep (se 1 (by rfl) ⟨2337848, by rfl⟩ : syracuseStep 3117131 = 4675697) B4675697
theorem B2076761 : Blo 1383511 2076761 := bstep (se 2 (by rfl) ⟨778785, by rfl⟩ : syracuseStep 2076761 = 1557571) B1557571
theorem B3117185 : Blo 1383511 3117185 := bstep (se 2 (by rfl) ⟨1168944, by rfl⟩ : syracuseStep 3117185 = 2337889) B2337889
theorem B10514609 : Blo 1383511 10514609 := bstep (se 2 (by rfl) ⟨3942978, by rfl⟩ : syracuseStep 10514609 = 7885957) B7885957
theorem B4436147 : Blo 1383511 4436147 := bstep (se 1 (by rfl) ⟨3327110, by rfl⟩ : syracuseStep 4436147 = 6654221) B6654221
theorem B2076875 : Blo 1383511 2076875 := bstep (se 1 (by rfl) ⟨1557656, by rfl⟩ : syracuseStep 2076875 = 3115313) B3115313
theorem B2076887 : Blo 1383511 2076887 := bstep (se 1 (by rfl) ⟨1557665, by rfl⟩ : syracuseStep 2076887 = 3115331) B3115331
theorem B4673753 : Blo 1383511 4673753 := bstep (se 2 (by rfl) ⟨1752657, by rfl⟩ : syracuseStep 4673753 = 3505315) B3505315
theorem B2076953 : Blo 1383511 2076953 := bstep (se 2 (by rfl) ⟨778857, by rfl⟩ : syracuseStep 2076953 = 1557715) B1557715
theorem B4993331 : Blo 1383511 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B5255513 : Blo 1383511 5255513 := bstep (se 2 (by rfl) ⟨1970817, by rfl⟩ : syracuseStep 5255513 = 3941635) B3941635
theorem B3117401 : Blo 1383511 3117401 := bstep (se 2 (by rfl) ⟨1169025, by rfl⟩ : syracuseStep 3117401 = 2338051) B2338051
theorem B7008605 : Blo 1383511 7008605 := bstep (se 3 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 7008605 = 2628227) B2628227
theorem B19960181 : Blo 1383511 19960181 := bstep (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) B1871267
theorem B2077067 : Blo 1383511 2077067 := bstep (se 1 (by rfl) ⟨1557800, by rfl⟩ : syracuseStep 2077067 = 3115601) B3115601
theorem B2077079 : Blo 1383511 2077079 := bstep (se 1 (by rfl) ⟨1557809, by rfl⟩ : syracuseStep 2077079 = 3115619) B3115619
theorem B2494937 : Blo 1383511 2494937 := bstep (se 2 (by rfl) ⟨935601, by rfl⟩ : syracuseStep 2494937 = 1871203) B1871203
theorem B2077145 : Blo 1383511 2077145 := bstep (se 2 (by rfl) ⟨778929, by rfl⟩ : syracuseStep 2077145 = 1557859) B1557859
theorem B2249227 : Blo 1383511 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B10654253 : Blo 1383511 10654253 := bstep (se 3 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 10654253 = 3995345) B3995345
theorem B5255725 : Blo 1383511 5255725 := bstep (se 3 (by rfl) ⟨985448, by rfl⟩ : syracuseStep 5255725 = 1970897) B1970897
theorem B1520183 : Blo 1383511 1520183 := bstep (se 1 (by rfl) ⟨1140137, by rfl⟩ : syracuseStep 1520183 = 2280275) B2280275
theorem B2077259 : Blo 1383511 2077259 := bstep (se 1 (by rfl) ⟨1557944, by rfl⟩ : syracuseStep 2077259 = 3115889) B3115889
theorem B2077271 : Blo 1383511 2077271 := bstep (se 1 (by rfl) ⟨1557953, by rfl⟩ : syracuseStep 2077271 = 3115907) B3115907
theorem B4436569 : Blo 1383511 4436569 := bstep (se 2 (by rfl) ⟨1663713, by rfl⟩ : syracuseStep 4436569 = 3327427) B3327427
theorem B22753943 : Blo 1383511 22753943 := bstep (se 1 (by rfl) ⟨17065457, by rfl⟩ : syracuseStep 22753943 = 34130915) B34130915
theorem B10515095 : Blo 1383511 10515095 := bstep (se 1 (by rfl) ⟨7886321, by rfl⟩ : syracuseStep 10515095 = 15772643) B15772643
theorem B2077337 : Blo 1383511 2077337 := bstep (se 2 (by rfl) ⟨779001, by rfl⟩ : syracuseStep 2077337 = 1558003) B1558003
theorem B1479403 : Blo 1383511 1479403 := bstep (se 1 (by rfl) ⟨1109552, by rfl⟩ : syracuseStep 1479403 = 2219105) B2219105
theorem B2077451 : Blo 1383511 2077451 := bstep (se 1 (by rfl) ⟨1558088, by rfl⟩ : syracuseStep 2077451 = 3116177) B3116177
theorem B2077463 : Blo 1383511 2077463 := bstep (se 1 (by rfl) ⟨1558097, by rfl⟩ : syracuseStep 2077463 = 3116195) B3116195
theorem B9466669 : Blo 1383511 9466669 := bstep (se 3 (by rfl) ⟨1775000, by rfl⟩ : syracuseStep 9466669 = 3550001) B3550001
theorem B4436801 : Blo 1383511 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B5616449 : Blo 1383511 5616449 := bstep (se 2 (by rfl) ⟨2106168, by rfl⟩ : syracuseStep 5616449 = 4212337) B4212337
theorem B2077529 : Blo 1383511 2077529 := bstep (se 2 (by rfl) ⟨779073, by rfl⟩ : syracuseStep 2077529 = 1558147) B1558147
theorem B5256029 : Blo 1383511 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B2806643 : Blo 1383511 2806643 := bstep (se 1 (by rfl) ⟨2104982, by rfl⟩ : syracuseStep 2806643 = 4209965) B4209965
theorem B4674455 : Blo 1383511 4674455 := bstep (se 1 (by rfl) ⟨3505841, by rfl⟩ : syracuseStep 4674455 = 7011683) B7011683
theorem B3503027 : Blo 1383511 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B2077643 : Blo 1383511 2077643 := bstep (se 1 (by rfl) ⟨1558232, by rfl⟩ : syracuseStep 2077643 = 3116465) B3116465
theorem B2626519 : Blo 1383511 2626519 := bstep (se 1 (by rfl) ⟨1969889, by rfl⟩ : syracuseStep 2626519 = 3939779) B3939779
theorem B2077655 : Blo 1383511 2077655 := bstep (se 1 (by rfl) ⟨1558241, by rfl⟩ : syracuseStep 2077655 = 3116483) B3116483
theorem B1971211 : Blo 1383511 1971211 := bstep (se 1 (by rfl) ⟨1478408, by rfl⟩ : syracuseStep 1971211 = 2956817) B2956817
theorem B2077721 : Blo 1383511 2077721 := bstep (se 2 (by rfl) ⟨779145, by rfl⟩ : syracuseStep 2077721 = 1558291) B1558291
theorem B11990051 : Blo 1383511 11990051 := bstep (se 1 (by rfl) ⟨8992538, by rfl⟩ : syracuseStep 11990051 = 17985077) B17985077
theorem B2077835 : Blo 1383511 2077835 := bstep (se 1 (by rfl) ⟨1558376, by rfl⟩ : syracuseStep 2077835 = 3116753) B3116753
theorem B2077847 : Blo 1383511 2077847 := bstep (se 1 (by rfl) ⟨1558385, by rfl⟩ : syracuseStep 2077847 = 3116771) B3116771
theorem B2626739 : Blo 1383511 2626739 := bstep (se 1 (by rfl) ⟨1970054, by rfl⟩ : syracuseStep 2626739 = 3940109) B3940109
theorem B3503321 : Blo 1383511 3503321 := bstep (se 2 (by rfl) ⟨1313745, by rfl⟩ : syracuseStep 3503321 = 2627491) B2627491
theorem B2077913 : Blo 1383511 2077913 := bstep (se 2 (by rfl) ⟨779217, by rfl⟩ : syracuseStep 2077913 = 1558435) B1558435
theorem B8418635 : Blo 1383511 8418635 := bstep (se 1 (by rfl) ⟨6313976, by rfl⟩ : syracuseStep 8418635 = 12627953) B12627953
theorem B2078027 : Blo 1383511 2078027 := bstep (se 1 (by rfl) ⟨1558520, by rfl⟩ : syracuseStep 2078027 = 3117041) B3117041
theorem B2078039 : Blo 1383511 2078039 := bstep (se 1 (by rfl) ⟨1558529, by rfl⟩ : syracuseStep 2078039 = 3117059) B3117059
theorem B2807129 : Blo 1383511 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B2626967 : Blo 1383511 2626967 := bstep (se 1 (by rfl) ⟨1970225, by rfl⟩ : syracuseStep 2626967 = 3940451) B3940451
theorem B7886231 : Blo 1383511 7886231 := bstep (se 1 (by rfl) ⟨5914673, by rfl⟩ : syracuseStep 7886231 = 11829347) B11829347
theorem B2078105 : Blo 1383511 2078105 := bstep (se 2 (by rfl) ⟨779289, by rfl⟩ : syracuseStep 2078105 = 1558579) B1558579
theorem B4674995 : Blo 1383511 4674995 := bstep (se 1 (by rfl) ⟨3506246, by rfl⟩ : syracuseStep 4674995 = 7012493) B7012493
theorem B1684951 : Blo 1383511 1684951 := bstep (se 1 (by rfl) ⟨1263713, by rfl⟩ : syracuseStep 1684951 = 2527427) B2527427
theorem B2078219 : Blo 1383511 2078219 := bstep (se 1 (by rfl) ⟨1558664, by rfl⟩ : syracuseStep 2078219 = 3117329) B3117329
theorem B2078231 : Blo 1383511 2078231 := bstep (se 1 (by rfl) ⟨1558673, by rfl⟩ : syracuseStep 2078231 = 3117347) B3117347
theorem B2496025 : Blo 1383511 2496025 := bstep (se 2 (by rfl) ⟨936009, by rfl⟩ : syracuseStep 2496025 = 1872019) B1872019
theorem B5912129 : Blo 1383511 5912129 := bstep (se 2 (by rfl) ⟨2217048, by rfl⟩ : syracuseStep 5912129 = 4434097) B4434097
theorem B2627225 : Blo 1383511 2627225 := bstep (se 2 (by rfl) ⟨985209, by rfl⟩ : syracuseStep 2627225 = 1970419) B1970419
theorem B2528921 : Blo 1383511 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B2528947 : Blo 1383511 2528947 := bstep (se 1 (by rfl) ⟨1896710, by rfl⟩ : syracuseStep 2528947 = 3793421) B3793421
theorem B4675265 : Blo 1383511 4675265 := bstep (se 2 (by rfl) ⟨1753224, by rfl⟩ : syracuseStep 4675265 = 3506449) B3506449
theorem B5912281 : Blo 1383511 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B101021539 : Blo 1383511 101021539 := bstep (se 1 (by rfl) ⟨75766154, by rfl⟩ : syracuseStep 101021539 = 151532309) B151532309
theorem B2955287 : Blo 1383511 2955287 := bstep (se 1 (by rfl) ⟨2216465, by rfl⟩ : syracuseStep 2955287 = 4432931) B4432931
theorem B2627635 : Blo 1383511 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B2955457 : Blo 1383511 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B1972441 : Blo 1383511 1972441 := bstep (se 2 (by rfl) ⟨739665, by rfl⟩ : syracuseStep 1972441 = 1479331) B1479331
theorem B4675805 : Blo 1383511 4675805 := bstep (se 3 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 4675805 = 1753427) B1753427
theorem B7010711 : Blo 1383511 7010711 := bstep (se 1 (by rfl) ⟨5258033, by rfl⟩ : syracuseStep 7010711 = 10516067) B10516067
theorem B2955799 : Blo 1383511 2955799 := bstep (se 1 (by rfl) ⟨2216849, by rfl⟩ : syracuseStep 2955799 = 4433699) B4433699
theorem B2103833 : Blo 1383511 2103833 := bstep (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) B1577875
theorem B2628121 : Blo 1383511 2628121 := bstep (se 2 (by rfl) ⟨985545, by rfl⟩ : syracuseStep 2628121 = 1971091) B1971091
theorem B3373643 : Blo 1383511 3373643 := bstep (se 1 (by rfl) ⟨2530232, by rfl⟩ : syracuseStep 3373643 = 5060465) B5060465
theorem B15768269 : Blo 1383511 15768269 := bstep (se 3 (by rfl) ⟨2956550, by rfl⟩ : syracuseStep 15768269 = 5913101) B5913101
theorem B3504971 : Blo 1383511 3504971 := bstep (se 1 (by rfl) ⟨2628728, by rfl⟩ : syracuseStep 3504971 = 5257457) B5257457
theorem B1751959 : Blo 1383511 1751959 := bstep (se 1 (by rfl) ⟨1313969, by rfl⟩ : syracuseStep 1751959 = 2627939) B2627939
theorem B11222021 : Blo 1383511 11222021 := bstep (se 4 (by rfl) ⟨1052064, by rfl⟩ : syracuseStep 11222021 = 2104129) B2104129
theorem B2628683 : Blo 1383511 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B1383511 : Blo 1383511 1383511 := bstep (se 1 (by rfl) ⟨1037633, by rfl⟩ : syracuseStep 1383511 = 2075267) B2075267
theorem B1383531 : Blo 1383511 1383531 := bstep (se 1 (by rfl) ⟨1037648, by rfl⟩ : syracuseStep 1383531 = 2075297) B2075297
theorem B1383543 : Blo 1383511 1383543 := bstep (se 1 (by rfl) ⟨1037657, by rfl⟩ : syracuseStep 1383543 = 2075315) B2075315
theorem B1383563 : Blo 1383511 1383563 := bstep (se 1 (by rfl) ⟨1037672, by rfl⟩ : syracuseStep 1383563 = 2075345) B2075345
theorem B1383575 : Blo 1383511 1383575 := bstep (se 1 (by rfl) ⟨1037681, by rfl⟩ : syracuseStep 1383575 = 2075363) B2075363
theorem B1383595 : Blo 1383511 1383595 := bstep (se 1 (by rfl) ⟨1037696, by rfl⟩ : syracuseStep 1383595 = 2075393) B2075393
theorem B1383607 : Blo 1383511 1383607 := bstep (se 1 (by rfl) ⟨1037705, by rfl⟩ : syracuseStep 1383607 = 2075411) B2075411
theorem B3325121 : Blo 1383511 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B1383627 : Blo 1383511 1383627 := bstep (se 1 (by rfl) ⟨1037720, by rfl⟩ : syracuseStep 1383627 = 2075441) B2075441
theorem B1383639 : Blo 1383511 1383639 := bstep (se 1 (by rfl) ⟨1037729, by rfl⟩ : syracuseStep 1383639 = 2075459) B2075459
theorem B1383659 : Blo 1383511 1383659 := bstep (se 1 (by rfl) ⟨1037744, by rfl⟩ : syracuseStep 1383659 = 2075489) B2075489
theorem B1383671 : Blo 1383511 1383671 := bstep (se 1 (by rfl) ⟨1037753, by rfl⟩ : syracuseStep 1383671 = 2075507) B2075507
theorem B2628865 : Blo 1383511 2628865 := bstep (se 2 (by rfl) ⟨985824, by rfl⟩ : syracuseStep 2628865 = 1971649) B1971649
theorem B1383691 : Blo 1383511 1383691 := bstep (se 1 (by rfl) ⟨1037768, by rfl⟩ : syracuseStep 1383691 = 2075537) B2075537
theorem B1383703 : Blo 1383511 1383703 := bstep (se 1 (by rfl) ⟨1037777, by rfl⟩ : syracuseStep 1383703 = 2075555) B2075555
theorem B1383723 : Blo 1383511 1383723 := bstep (se 1 (by rfl) ⟨1037792, by rfl⟩ : syracuseStep 1383723 = 2075585) B2075585
theorem B1383735 : Blo 1383511 1383735 := bstep (se 1 (by rfl) ⟨1037801, by rfl⟩ : syracuseStep 1383735 = 2075603) B2075603
theorem B1383755 : Blo 1383511 1383755 := bstep (se 1 (by rfl) ⟨1037816, by rfl⟩ : syracuseStep 1383755 = 2075633) B2075633
theorem B2956619 : Blo 1383511 2956619 := bstep (se 1 (by rfl) ⟨2217464, by rfl⟩ : syracuseStep 2956619 = 4434929) B4434929
theorem B1383767 : Blo 1383511 1383767 := bstep (se 1 (by rfl) ⟨1037825, by rfl⟩ : syracuseStep 1383767 = 2075651) B2075651
theorem B1383787 : Blo 1383511 1383787 := bstep (se 1 (by rfl) ⟨1037840, by rfl⟩ : syracuseStep 1383787 = 2075681) B2075681
theorem B1383799 : Blo 1383511 1383799 := bstep (se 1 (by rfl) ⟨1037849, by rfl⟩ : syracuseStep 1383799 = 2075699) B2075699
theorem B5258627 : Blo 1383511 5258627 := bstep (se 1 (by rfl) ⟨3943970, by rfl⟩ : syracuseStep 5258627 = 7887941) B7887941
theorem B1383819 : Blo 1383511 1383819 := bstep (se 1 (by rfl) ⟨1037864, by rfl⟩ : syracuseStep 1383819 = 2075729) B2075729
theorem B5258641 : Blo 1383511 5258641 := bstep (se 2 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 5258641 = 3943981) B3943981
theorem B1383831 : Blo 1383511 1383831 := bstep (se 1 (by rfl) ⟨1037873, by rfl⟩ : syracuseStep 1383831 = 2075747) B2075747
theorem B1383851 : Blo 1383511 1383851 := bstep (se 1 (by rfl) ⟨1037888, by rfl⟩ : syracuseStep 1383851 = 2075777) B2075777
theorem B12639665 : Blo 1383511 12639665 := bstep (se 2 (by rfl) ⟨4739874, by rfl⟩ : syracuseStep 12639665 = 9479749) B9479749
theorem B1383863 : Blo 1383511 1383863 := bstep (se 1 (by rfl) ⟨1037897, by rfl⟩ : syracuseStep 1383863 = 2075795) B2075795
theorem B1383883 : Blo 1383511 1383883 := bstep (se 1 (by rfl) ⟨1037912, by rfl⟩ : syracuseStep 1383883 = 2075825) B2075825
theorem B1383895 : Blo 1383511 1383895 := bstep (se 1 (by rfl) ⟨1037921, by rfl⟩ : syracuseStep 1383895 = 2075843) B2075843
theorem B1383915 : Blo 1383511 1383915 := bstep (se 1 (by rfl) ⟨1037936, by rfl⟩ : syracuseStep 1383915 = 2075873) B2075873
theorem B1383927 : Blo 1383511 1383927 := bstep (se 1 (by rfl) ⟨1037945, by rfl⟩ : syracuseStep 1383927 = 2075891) B2075891
theorem B1383947 : Blo 1383511 1383947 := bstep (se 1 (by rfl) ⟨1037960, by rfl⟩ : syracuseStep 1383947 = 2075921) B2075921
theorem B1383959 : Blo 1383511 1383959 := bstep (se 1 (by rfl) ⟨1037969, by rfl⟩ : syracuseStep 1383959 = 2075939) B2075939
theorem B1383979 : Blo 1383511 1383979 := bstep (se 1 (by rfl) ⟨1037984, by rfl⟩ : syracuseStep 1383979 = 2075969) B2075969
theorem B1383991 : Blo 1383511 1383991 := bstep (se 1 (by rfl) ⟨1037993, by rfl⟩ : syracuseStep 1383991 = 2075987) B2075987
theorem B1384011 : Blo 1383511 1384011 := bstep (se 1 (by rfl) ⟨1038008, by rfl⟩ : syracuseStep 1384011 = 2076017) B2076017
theorem B1384023 : Blo 1383511 1384023 := bstep (se 1 (by rfl) ⟨1038017, by rfl⟩ : syracuseStep 1384023 = 2076035) B2076035
theorem B1384043 : Blo 1383511 1384043 := bstep (se 1 (by rfl) ⟨1038032, by rfl⟩ : syracuseStep 1384043 = 2076065) B2076065
theorem B1384055 : Blo 1383511 1384055 := bstep (se 1 (by rfl) ⟨1038041, by rfl⟩ : syracuseStep 1384055 = 2076083) B2076083
theorem B1384075 : Blo 1383511 1384075 := bstep (se 1 (by rfl) ⟨1038056, by rfl⟩ : syracuseStep 1384075 = 2076113) B2076113
theorem B1998475 : Blo 1383511 1998475 := bstep (se 1 (by rfl) ⟨1498856, by rfl⟩ : syracuseStep 1998475 = 2997713) B2997713
theorem B1384087 : Blo 1383511 1384087 := bstep (se 1 (by rfl) ⟨1038065, by rfl⟩ : syracuseStep 1384087 = 2076131) B2076131
theorem B1384107 : Blo 1383511 1384107 := bstep (se 1 (by rfl) ⟨1038080, by rfl⟩ : syracuseStep 1384107 = 2076161) B2076161
theorem B2956979 : Blo 1383511 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B1384119 : Blo 1383511 1384119 := bstep (se 1 (by rfl) ⟨1038089, by rfl⟩ : syracuseStep 1384119 = 2076179) B2076179
theorem B5258945 : Blo 1383511 5258945 := bstep (se 2 (by rfl) ⟨1972104, by rfl⟩ : syracuseStep 5258945 = 3944209) B3944209
theorem B1384139 : Blo 1383511 1384139 := bstep (se 1 (by rfl) ⟨1038104, by rfl⟩ : syracuseStep 1384139 = 2076209) B2076209
theorem B1752779 : Blo 1383511 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1384151 : Blo 1383511 1384151 := bstep (se 1 (by rfl) ⟨1038113, by rfl⟩ : syracuseStep 1384151 = 2076227) B2076227
theorem B1384171 : Blo 1383511 1384171 := bstep (se 1 (by rfl) ⟨1038128, by rfl⟩ : syracuseStep 1384171 = 2076257) B2076257
theorem B1384183 : Blo 1383511 1384183 := bstep (se 1 (by rfl) ⟨1038137, by rfl⟩ : syracuseStep 1384183 = 2076275) B2076275
theorem B1384203 : Blo 1383511 1384203 := bstep (se 1 (by rfl) ⟨1038152, by rfl⟩ : syracuseStep 1384203 = 2076305) B2076305
theorem B1384215 : Blo 1383511 1384215 := bstep (se 1 (by rfl) ⟨1038161, by rfl⟩ : syracuseStep 1384215 = 2076323) B2076323
theorem B3505943 : Blo 1383511 3505943 := bstep (se 1 (by rfl) ⟨2629457, by rfl⟩ : syracuseStep 3505943 = 5258915) B5258915
theorem B1384235 : Blo 1383511 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B4497203 : Blo 1383511 4497203 := bstep (se 1 (by rfl) ⟨3372902, by rfl⟩ : syracuseStep 4497203 = 6745805) B6745805
theorem B1384247 : Blo 1383511 1384247 := bstep (se 1 (by rfl) ⟨1038185, by rfl⟩ : syracuseStep 1384247 = 2076371) B2076371
theorem B1384267 : Blo 1383511 1384267 := bstep (se 1 (by rfl) ⟨1038200, by rfl⟩ : syracuseStep 1384267 = 2076401) B2076401
theorem B1384279 : Blo 1383511 1384279 := bstep (se 1 (by rfl) ⟨1038209, by rfl⟩ : syracuseStep 1384279 = 2076419) B2076419
theorem B1384299 : Blo 1383511 1384299 := bstep (se 1 (by rfl) ⟨1038224, by rfl⟩ : syracuseStep 1384299 = 2076449) B2076449
theorem B1384311 : Blo 1383511 1384311 := bstep (se 1 (by rfl) ⟨1038233, by rfl⟩ : syracuseStep 1384311 = 2076467) B2076467
theorem B1384331 : Blo 1383511 1384331 := bstep (se 1 (by rfl) ⟨1038248, by rfl⟩ : syracuseStep 1384331 = 2076497) B2076497
theorem B1384343 : Blo 1383511 1384343 := bstep (se 1 (by rfl) ⟨1038257, by rfl⟩ : syracuseStep 1384343 = 2076515) B2076515
theorem B11386775 : Blo 1383511 11386775 := bstep (se 1 (by rfl) ⟨8540081, by rfl⟩ : syracuseStep 11386775 = 17080163) B17080163
theorem B1384363 : Blo 1383511 1384363 := bstep (se 1 (by rfl) ⟨1038272, by rfl⟩ : syracuseStep 1384363 = 2076545) B2076545
theorem B11820977 : Blo 1383511 11820977 := bstep (se 2 (by rfl) ⟨4432866, by rfl⟩ : syracuseStep 11820977 = 8865733) B8865733
theorem B1384375 : Blo 1383511 1384375 := bstep (se 1 (by rfl) ⟨1038281, by rfl⟩ : syracuseStep 1384375 = 2076563) B2076563
theorem B1384395 : Blo 1383511 1384395 := bstep (se 1 (by rfl) ⟨1038296, by rfl⟩ : syracuseStep 1384395 = 2076593) B2076593
theorem B2629579 : Blo 1383511 2629579 := bstep (se 1 (by rfl) ⟨1972184, by rfl⟩ : syracuseStep 2629579 = 3944369) B3944369
theorem B3112919 : Blo 1383511 3112919 := bstep (se 1 (by rfl) ⟨2334689, by rfl⟩ : syracuseStep 3112919 = 4669379) B4669379
theorem B1384407 : Blo 1383511 1384407 := bstep (se 1 (by rfl) ⟨1038305, by rfl⟩ : syracuseStep 1384407 = 2076611) B2076611
theorem B1384427 : Blo 1383511 1384427 := bstep (se 1 (by rfl) ⟨1038320, by rfl⟩ : syracuseStep 1384427 = 2076641) B2076641
theorem B1384439 : Blo 1383511 1384439 := bstep (se 1 (by rfl) ⟨1038329, by rfl⟩ : syracuseStep 1384439 = 2076659) B2076659
theorem B7487491 : Blo 1383511 7487491 := bstep (se 1 (by rfl) ⟨5615618, by rfl⟩ : syracuseStep 7487491 = 11231237) B11231237
theorem B1384455 : Blo 1383511 1384455 := bstep (se 1 (by rfl) ⟨1038341, by rfl⟩ : syracuseStep 1384455 = 2076683) B2076683
theorem B29925389 : Blo 1383511 29925389 := bstep (se 3 (by rfl) ⟨5611010, by rfl⟩ : syracuseStep 29925389 = 11222021) B11222021
theorem B3325967 : Blo 1383511 3325967 := bstep (se 1 (by rfl) ⟨2494475, by rfl⟩ : syracuseStep 3325967 = 4988951) B4988951
theorem B1384463 : Blo 1383511 1384463 := bstep (se 1 (by rfl) ⟨1038347, by rfl⟩ : syracuseStep 1384463 = 2076695) B2076695
theorem B1753103 : Blo 1383511 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B1384507 : Blo 1383511 1384507 := bstep (se 1 (by rfl) ⟨1038380, by rfl⟩ : syracuseStep 1384507 = 2076761) B2076761
theorem B13312133 : Blo 1383511 13312133 := bstep (se 4 (by rfl) ⟨1248012, by rfl⟩ : syracuseStep 13312133 = 2496025) B2496025
theorem B1384583 : Blo 1383511 1384583 := bstep (se 1 (by rfl) ⟨1038437, by rfl⟩ : syracuseStep 1384583 = 2076875) B2076875
theorem B1384591 : Blo 1383511 1384591 := bstep (se 1 (by rfl) ⟨1038443, by rfl⟩ : syracuseStep 1384591 = 2076887) B2076887
theorem B1384635 : Blo 1383511 1384635 := bstep (se 1 (by rfl) ⟨1038476, by rfl⟩ : syracuseStep 1384635 = 2076953) B2076953
theorem B7479533 : Blo 1383511 7479533 := bstep (se 3 (by rfl) ⟨1402412, by rfl⟩ : syracuseStep 7479533 = 2804825) B2804825
theorem B1556743 : Blo 1383511 1556743 := bstep (se 1 (by rfl) ⟨1167557, by rfl⟩ : syracuseStep 1556743 = 2335115) B2335115
theorem B1384711 : Blo 1383511 1384711 := bstep (se 1 (by rfl) ⟨1038533, by rfl⟩ : syracuseStep 1384711 = 2077067) B2077067
theorem B1384719 : Blo 1383511 1384719 := bstep (se 1 (by rfl) ⟨1038539, by rfl⟩ : syracuseStep 1384719 = 2077079) B2077079
theorem B2629921 : Blo 1383511 2629921 := bstep (se 2 (by rfl) ⟨986220, by rfl⟩ : syracuseStep 2629921 = 1972441) B1972441
theorem B1663291 : Blo 1383511 1663291 := bstep (se 1 (by rfl) ⟨1247468, by rfl⟩ : syracuseStep 1663291 = 2494937) B2494937
theorem B1384763 : Blo 1383511 1384763 := bstep (se 1 (by rfl) ⟨1038572, by rfl⟩ : syracuseStep 1384763 = 2077145) B2077145
theorem B4669811 : Blo 1383511 4669811 := bstep (se 1 (by rfl) ⟨3502358, by rfl⟩ : syracuseStep 4669811 = 7004717) B7004717
theorem B7102835 : Blo 1383511 7102835 := bstep (se 1 (by rfl) ⟨5327126, by rfl⟩ : syracuseStep 7102835 = 10654253) B10654253
theorem B3113351 : Blo 1383511 3113351 := bstep (se 1 (by rfl) ⟨2335013, by rfl⟩ : syracuseStep 3113351 = 4670027) B4670027
theorem B5915015 : Blo 1383511 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B1384839 : Blo 1383511 1384839 := bstep (se 1 (by rfl) ⟨1038629, by rfl⟩ : syracuseStep 1384839 = 2077259) B2077259
theorem B1384847 : Blo 1383511 1384847 := bstep (se 1 (by rfl) ⟨1038635, by rfl⟩ : syracuseStep 1384847 = 2077271) B2077271
theorem B1556923 : Blo 1383511 1556923 := bstep (se 1 (by rfl) ⟨1167692, by rfl⟩ : syracuseStep 1556923 = 2335385) B2335385
theorem B1384891 : Blo 1383511 1384891 := bstep (se 1 (by rfl) ⟨1038668, by rfl⟩ : syracuseStep 1384891 = 2077337) B2077337
theorem B7012817 : Blo 1383511 7012817 := bstep (se 2 (by rfl) ⟨2629806, by rfl⟩ : syracuseStep 7012817 = 5259613) B5259613
theorem B7479773 : Blo 1383511 7479773 := bstep (se 3 (by rfl) ⟨1402457, by rfl⟩ : syracuseStep 7479773 = 2804915) B2804915
theorem B11829725 : Blo 1383511 11829725 := bstep (se 3 (by rfl) ⟨2218073, by rfl⟩ : syracuseStep 11829725 = 4436147) B4436147
theorem B1384967 : Blo 1383511 1384967 := bstep (se 1 (by rfl) ⟨1038725, by rfl⟩ : syracuseStep 1384967 = 2077451) B2077451
theorem B1384975 : Blo 1383511 1384975 := bstep (se 1 (by rfl) ⟨1038731, by rfl⟩ : syracuseStep 1384975 = 2077463) B2077463
theorem B2957867 : Blo 1383511 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B3744299 : Blo 1383511 3744299 := bstep (se 1 (by rfl) ⟨2808224, by rfl⟩ : syracuseStep 3744299 = 5616449) B5616449
theorem B3113531 : Blo 1383511 3113531 := bstep (se 1 (by rfl) ⟨2335148, by rfl⟩ : syracuseStep 3113531 = 4670297) B4670297
theorem B1385019 : Blo 1383511 1385019 := bstep (se 1 (by rfl) ⟨1038764, by rfl⟩ : syracuseStep 1385019 = 2077529) B2077529
theorem B2335351 : Blo 1383511 2335351 := bstep (se 1 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 2335351 = 3503027) B3503027
theorem B1385095 : Blo 1383511 1385095 := bstep (se 1 (by rfl) ⟨1038821, by rfl⟩ : syracuseStep 1385095 = 2077643) B2077643
theorem B1385103 : Blo 1383511 1385103 := bstep (se 1 (by rfl) ⟨1038827, by rfl⟩ : syracuseStep 1385103 = 2077655) B2077655
theorem B3113657 : Blo 1383511 3113657 := bstep (se 2 (by rfl) ⟨1167621, by rfl⟩ : syracuseStep 3113657 = 2335243) B2335243
theorem B1385147 : Blo 1383511 1385147 := bstep (se 1 (by rfl) ⟨1038860, by rfl⟩ : syracuseStep 1385147 = 2077721) B2077721
theorem B3941065 : Blo 1383511 3941065 := bstep (se 2 (by rfl) ⟨1477899, by rfl⟩ : syracuseStep 3941065 = 2955799) B2955799
theorem B10658533 : Blo 1383511 10658533 := bstep (se 4 (by rfl) ⟨999237, by rfl⟩ : syracuseStep 10658533 = 1998475) B1998475
theorem B1385223 : Blo 1383511 1385223 := bstep (se 1 (by rfl) ⟨1038917, by rfl⟩ : syracuseStep 1385223 = 2077835) B2077835
theorem B3326735 : Blo 1383511 3326735 := bstep (se 1 (by rfl) ⟨2495051, by rfl⟩ : syracuseStep 3326735 = 4990103) B4990103
theorem B1385231 : Blo 1383511 1385231 := bstep (se 1 (by rfl) ⟨1038923, by rfl⟩ : syracuseStep 1385231 = 2077847) B2077847
theorem B5915425 : Blo 1383511 5915425 := bstep (se 2 (by rfl) ⟨2218284, by rfl⟩ : syracuseStep 5915425 = 4436569) B4436569
theorem B2335547 : Blo 1383511 2335547 := bstep (se 1 (by rfl) ⟨1751660, by rfl⟩ : syracuseStep 2335547 = 3503321) B3503321
theorem B1385275 : Blo 1383511 1385275 := bstep (se 1 (by rfl) ⟨1038956, by rfl⟩ : syracuseStep 1385275 = 2077913) B2077913
theorem B26608499 : Blo 1383511 26608499 := bstep (se 1 (by rfl) ⟨19956374, by rfl⟩ : syracuseStep 26608499 = 39912749) B39912749
theorem B5612423 : Blo 1383511 5612423 := bstep (se 1 (by rfl) ⟨4209317, by rfl⟩ : syracuseStep 5612423 = 8418635) B8418635
theorem B1385351 : Blo 1383511 1385351 := bstep (se 1 (by rfl) ⟨1039013, by rfl⟩ : syracuseStep 1385351 = 2078027) B2078027
theorem B1557391 : Blo 1383511 1557391 := bstep (se 1 (by rfl) ⟨1168043, by rfl⟩ : syracuseStep 1557391 = 2336087) B2336087
theorem B1385359 : Blo 1383511 1385359 := bstep (se 1 (by rfl) ⟨1039019, by rfl⟩ : syracuseStep 1385359 = 2078039) B2078039
theorem B1385403 : Blo 1383511 1385403 := bstep (se 1 (by rfl) ⟨1039052, by rfl⟩ : syracuseStep 1385403 = 2078105) B2078105
theorem B15762437 : Blo 1383511 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B1385479 : Blo 1383511 1385479 := bstep (se 1 (by rfl) ⟨1039109, by rfl⟩ : syracuseStep 1385479 = 2078219) B2078219
theorem B3113999 : Blo 1383511 3113999 := bstep (se 1 (by rfl) ⟨2335499, by rfl⟩ : syracuseStep 3113999 = 4670999) B4670999
theorem B1385487 : Blo 1383511 1385487 := bstep (se 1 (by rfl) ⟨1039115, by rfl⟩ : syracuseStep 1385487 = 2078231) B2078231
theorem B3114017 : Blo 1383511 3114017 := bstep (se 2 (by rfl) ⟨1167756, by rfl⟩ : syracuseStep 3114017 = 2335513) B2335513
theorem B3941419 : Blo 1383511 3941419 := bstep (se 1 (by rfl) ⟨2956064, by rfl⟩ : syracuseStep 3941419 = 5912129) B5912129
theorem B5915767 : Blo 1383511 5915767 := bstep (se 1 (by rfl) ⟨4436825, by rfl⟩ : syracuseStep 5915767 = 8873651) B8873651
theorem B2335945 : Blo 1383511 2335945 := bstep (se 2 (by rfl) ⟨875979, by rfl⟩ : syracuseStep 2335945 = 1751959) B1751959
theorem B7890149 : Blo 1383511 7890149 := bstep (se 4 (by rfl) ⟨739701, by rfl⟩ : syracuseStep 7890149 = 1479403) B1479403
theorem B3941693 : Blo 1383511 3941693 := bstep (se 3 (by rfl) ⟨739067, by rfl⟩ : syracuseStep 3941693 = 1478135) B1478135
theorem B6653299 : Blo 1383511 6653299 := bstep (se 1 (by rfl) ⟨4989974, by rfl⟩ : syracuseStep 6653299 = 9979949) B9979949
theorem B3114359 : Blo 1383511 3114359 := bstep (se 1 (by rfl) ⟨2335769, by rfl⟩ : syracuseStep 3114359 = 4671539) B4671539
theorem B1557895 : Blo 1383511 1557895 := bstep (se 1 (by rfl) ⟨1168421, by rfl⟩ : syracuseStep 1557895 = 2336843) B2336843
theorem B10519955 : Blo 1383511 10519955 := bstep (se 1 (by rfl) ⟨7889966, by rfl⟩ : syracuseStep 10519955 = 15779933) B15779933
theorem B8996381 : Blo 1383511 8996381 := bstep (se 3 (by rfl) ⟨1686821, by rfl⟩ : syracuseStep 8996381 = 3373643) B3373643
theorem B3114539 : Blo 1383511 3114539 := bstep (se 1 (by rfl) ⟨2335904, by rfl⟩ : syracuseStep 3114539 = 4671809) B4671809
theorem B1558075 : Blo 1383511 1558075 := bstep (se 1 (by rfl) ⟨1168556, by rfl⟩ : syracuseStep 1558075 = 2337113) B2337113
theorem B7890605 : Blo 1383511 7890605 := bstep (se 3 (by rfl) ⟨1479488, by rfl⟩ : syracuseStep 7890605 = 2958977) B2958977
theorem B8865551 : Blo 1383511 8865551 := bstep (se 1 (by rfl) ⟨6649163, by rfl⟩ : syracuseStep 8865551 = 13298327) B13298327
theorem B10512179 : Blo 1383511 10512179 := bstep (se 1 (by rfl) ⟨7884134, by rfl⟩ : syracuseStep 10512179 = 15768269) B15768269
theorem B2336647 : Blo 1383511 2336647 := bstep (se 1 (by rfl) ⟨1752485, by rfl⟩ : syracuseStep 2336647 = 3504971) B3504971
theorem B3114899 : Blo 1383511 3114899 := bstep (se 1 (by rfl) ⟨2336174, by rfl⟩ : syracuseStep 3114899 = 4672349) B4672349
theorem B3114953 : Blo 1383511 3114953 := bstep (se 2 (by rfl) ⟨1168107, by rfl⟩ : syracuseStep 3114953 = 2336215) B2336215
theorem B14976971 : Blo 1383511 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B1558543 : Blo 1383511 1558543 := bstep (se 1 (by rfl) ⟨1168907, by rfl⟩ : syracuseStep 1558543 = 2337815) B2337815
theorem B255789197 : Blo 1383511 255789197 := bstep (se 3 (by rfl) ⟨47960474, by rfl⟩ : syracuseStep 255789197 = 95920949) B95920949
theorem B7883041 : Blo 1383511 7883041 := bstep (se 2 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 7883041 = 5912281) B5912281
theorem B134695385 : Blo 1383511 134695385 := bstep (se 2 (by rfl) ⟨50510769, by rfl⟩ : syracuseStep 134695385 = 101021539) B101021539
theorem B2337295 : Blo 1383511 2337295 := bstep (se 1 (by rfl) ⟨1752971, by rfl⟩ : syracuseStep 2337295 = 3505943) B3505943
theorem B3115655 : Blo 1383511 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B2075279 : Blo 1383511 2075279 := bstep (se 1 (by rfl) ⟨1556459, by rfl⟩ : syracuseStep 2075279 = 3112919) B3112919
theorem B2075321 : Blo 1383511 2075321 := bstep (se 2 (by rfl) ⟨778245, by rfl⟩ : syracuseStep 2075321 = 1556491) B1556491
theorem B11995877 : Blo 1383511 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B39906053 : Blo 1383511 39906053 := bstep (se 4 (by rfl) ⟨3741192, by rfl⟩ : syracuseStep 39906053 = 7482385) B7482385
theorem B2075399 : Blo 1383511 2075399 := bstep (se 1 (by rfl) ⟨1556549, by rfl⟩ : syracuseStep 2075399 = 3113099) B3113099
theorem B2075435 : Blo 1383511 2075435 := bstep (se 1 (by rfl) ⟨1556576, by rfl⟩ : syracuseStep 2075435 = 3113153) B3113153
theorem B3115835 : Blo 1383511 3115835 := bstep (se 1 (by rfl) ⟨2336876, by rfl⟩ : syracuseStep 3115835 = 4673753) B4673753
theorem B2075465 : Blo 1383511 2075465 := bstep (se 2 (by rfl) ⟨778299, by rfl⟩ : syracuseStep 2075465 = 1556599) B1556599
theorem B4672403 : Blo 1383511 4672403 := bstep (se 1 (by rfl) ⟨3504302, by rfl⟩ : syracuseStep 4672403 = 7008605) B7008605
theorem B13306787 : Blo 1383511 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B3115961 : Blo 1383511 3115961 := bstep (se 2 (by rfl) ⟨1168485, by rfl⟩ : syracuseStep 3115961 = 2336971) B2336971
theorem B2075579 : Blo 1383511 2075579 := bstep (se 1 (by rfl) ⟨1556684, by rfl⟩ : syracuseStep 2075579 = 3113369) B3113369
theorem B2075639 : Blo 1383511 2075639 := bstep (se 1 (by rfl) ⟨1556729, by rfl⟩ : syracuseStep 2075639 = 3113459) B3113459
theorem B2075663 : Blo 1383511 2075663 := bstep (se 1 (by rfl) ⟨1556747, by rfl⟩ : syracuseStep 2075663 = 3113495) B3113495
theorem B2337835 : Blo 1383511 2337835 := bstep (se 1 (by rfl) ⟨1753376, by rfl⟩ : syracuseStep 2337835 = 3506753) B3506753
theorem B2075705 : Blo 1383511 2075705 := bstep (se 2 (by rfl) ⟨778389, by rfl⟩ : syracuseStep 2075705 = 1556779) B1556779
theorem B9972823 : Blo 1383511 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B4435031 : Blo 1383511 4435031 := bstep (se 1 (by rfl) ⟨3326273, by rfl⟩ : syracuseStep 4435031 = 6652547) B6652547
theorem B5614679 : Blo 1383511 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B2075783 : Blo 1383511 2075783 := bstep (se 1 (by rfl) ⟨1556837, by rfl⟩ : syracuseStep 2075783 = 3113675) B3113675
theorem B2075819 : Blo 1383511 2075819 := bstep (se 1 (by rfl) ⟨1556864, by rfl⟩ : syracuseStep 2075819 = 3113729) B3113729
theorem B11234477 : Blo 1383511 11234477 := bstep (se 3 (by rfl) ⟨2106464, by rfl⟩ : syracuseStep 11234477 = 4212929) B4212929
theorem B2337977 : Blo 1383511 2337977 := bstep (se 2 (by rfl) ⟨876741, by rfl⟩ : syracuseStep 2337977 = 1753483) B1753483
theorem B2075849 : Blo 1383511 2075849 := bstep (se 2 (by rfl) ⟨778443, by rfl⟩ : syracuseStep 2075849 = 1556887) B1556887
theorem B13479149 : Blo 1383511 13479149 := bstep (se 3 (by rfl) ⟨2527340, by rfl⟩ : syracuseStep 13479149 = 5054681) B5054681
theorem B1871095 : Blo 1383511 1871095 := bstep (se 1 (by rfl) ⟨1403321, by rfl⟩ : syracuseStep 1871095 = 2806643) B2806643
theorem B3116303 : Blo 1383511 3116303 := bstep (se 1 (by rfl) ⟨2337227, by rfl⟩ : syracuseStep 3116303 = 4674455) B4674455
theorem B3116321 : Blo 1383511 3116321 := bstep (se 2 (by rfl) ⟨1168620, by rfl⟩ : syracuseStep 3116321 = 2337241) B2337241
theorem B53923117 : Blo 1383511 53923117 := bstep (se 3 (by rfl) ⟨10110584, by rfl⟩ : syracuseStep 53923117 = 20221169) B20221169
theorem B2075963 : Blo 1383511 2075963 := bstep (se 1 (by rfl) ⟨1556972, by rfl⟩ : syracuseStep 2075963 = 3113945) B3113945
theorem B2076023 : Blo 1383511 2076023 := bstep (se 1 (by rfl) ⟨1557017, by rfl⟩ : syracuseStep 2076023 = 3114035) B3114035
theorem B3943799 : Blo 1383511 3943799 := bstep (se 1 (by rfl) ⟨2957849, by rfl⟩ : syracuseStep 3943799 = 5915699) B5915699
theorem B33680771 : Blo 1383511 33680771 := bstep (se 1 (by rfl) ⟨25260578, by rfl⟩ : syracuseStep 33680771 = 50521157) B50521157
theorem B2076047 : Blo 1383511 2076047 := bstep (se 1 (by rfl) ⟨1557035, by rfl⟩ : syracuseStep 2076047 = 3114071) B3114071
theorem B7007633 : Blo 1383511 7007633 := bstep (se 2 (by rfl) ⟨2627862, by rfl⟩ : syracuseStep 7007633 = 5255725) B5255725
theorem B2076089 : Blo 1383511 2076089 := bstep (se 2 (by rfl) ⟨778533, by rfl⟩ : syracuseStep 2076089 = 1557067) B1557067
theorem B16846265 : Blo 1383511 16846265 := bstep (se 2 (by rfl) ⟨6317349, by rfl⟩ : syracuseStep 16846265 = 12634699) B12634699
theorem B2076167 : Blo 1383511 2076167 := bstep (se 1 (by rfl) ⟨1557125, by rfl⟩ : syracuseStep 2076167 = 3114251) B3114251
theorem B7884317 : Blo 1383511 7884317 := bstep (se 3 (by rfl) ⟨1478309, by rfl⟩ : syracuseStep 7884317 = 2956619) B2956619
theorem B2493985 : Blo 1383511 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B8416811 : Blo 1383511 8416811 := bstep (se 1 (by rfl) ⟨6312608, by rfl⟩ : syracuseStep 8416811 = 12625217) B12625217
theorem B2076203 : Blo 1383511 2076203 := bstep (se 1 (by rfl) ⟨1557152, by rfl⟩ : syracuseStep 2076203 = 3114305) B3114305
theorem B1871419 : Blo 1383511 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B2076233 : Blo 1383511 2076233 := bstep (se 2 (by rfl) ⟨778587, by rfl⟩ : syracuseStep 2076233 = 1557175) B1557175
theorem B19951181 : Blo 1383511 19951181 := bstep (se 3 (by rfl) ⟨3740846, by rfl⟩ : syracuseStep 19951181 = 7481693) B7481693
theorem B13487717 : Blo 1383511 13487717 := bstep (se 4 (by rfl) ⟨1264473, by rfl⟩ : syracuseStep 13487717 = 2528947) B2528947
theorem B3116663 : Blo 1383511 3116663 := bstep (se 1 (by rfl) ⟨2337497, by rfl⟩ : syracuseStep 3116663 = 4674995) B4674995
theorem B2076347 : Blo 1383511 2076347 := bstep (se 1 (by rfl) ⟨1557260, by rfl⟩ : syracuseStep 2076347 = 3114521) B3114521
theorem B2076407 : Blo 1383511 2076407 := bstep (se 1 (by rfl) ⟨1557305, by rfl⟩ : syracuseStep 2076407 = 3114611) B3114611
theorem B2076431 : Blo 1383511 2076431 := bstep (se 1 (by rfl) ⟨1557323, by rfl⟩ : syracuseStep 2076431 = 3114647) B3114647
theorem B3116843 : Blo 1383511 3116843 := bstep (se 1 (by rfl) ⟨2337632, by rfl⟩ : syracuseStep 3116843 = 4675265) B4675265
theorem B2076473 : Blo 1383511 2076473 := bstep (se 2 (by rfl) ⟨778677, by rfl⟩ : syracuseStep 2076473 = 1557355) B1557355
theorem B5255027 : Blo 1383511 5255027 := bstep (se 1 (by rfl) ⟨3941270, by rfl⟩ : syracuseStep 5255027 = 7882541) B7882541
theorem B2076551 : Blo 1383511 2076551 := bstep (se 1 (by rfl) ⟨1557413, by rfl⟩ : syracuseStep 2076551 = 3114827) B3114827
theorem B2076587 : Blo 1383511 2076587 := bstep (se 1 (by rfl) ⟨1557440, by rfl⟩ : syracuseStep 2076587 = 3114881) B3114881
theorem B3502025 : Blo 1383511 3502025 := bstep (se 2 (by rfl) ⟨1313259, by rfl⟩ : syracuseStep 3502025 = 2626519) B2626519
theorem B2076617 : Blo 1383511 2076617 := bstep (se 2 (by rfl) ⟨778731, by rfl⟩ : syracuseStep 2076617 = 1557463) B1557463
theorem B1970191 : Blo 1383511 1970191 := bstep (se 1 (by rfl) ⟨1477643, by rfl⟩ : syracuseStep 1970191 = 2955287) B2955287
theorem B25260055 : Blo 1383511 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B2076731 : Blo 1383511 2076731 := bstep (se 1 (by rfl) ⟨1557548, by rfl⟩ : syracuseStep 2076731 = 3115097) B3115097
theorem B2076791 : Blo 1383511 2076791 := bstep (se 1 (by rfl) ⟨1557593, by rfl⟩ : syracuseStep 2076791 = 3115187) B3115187
theorem B2076815 : Blo 1383511 2076815 := bstep (se 1 (by rfl) ⟨1557611, by rfl⟩ : syracuseStep 2076815 = 3115223) B3115223
theorem B3117203 : Blo 1383511 3117203 := bstep (se 1 (by rfl) ⟨2337902, by rfl⟩ : syracuseStep 3117203 = 4675805) B4675805
theorem B2076857 : Blo 1383511 2076857 := bstep (se 2 (by rfl) ⟨778821, by rfl⟩ : syracuseStep 2076857 = 1557643) B1557643
theorem B3117257 : Blo 1383511 3117257 := bstep (se 2 (by rfl) ⟨1168971, by rfl⟩ : syracuseStep 3117257 = 2337943) B2337943
theorem B2076935 : Blo 1383511 2076935 := bstep (se 1 (by rfl) ⟨1557701, by rfl⟩ : syracuseStep 2076935 = 3115403) B3115403
theorem B4673807 : Blo 1383511 4673807 := bstep (se 1 (by rfl) ⟨3505355, by rfl⟩ : syracuseStep 4673807 = 7010711) B7010711
theorem B3502379 : Blo 1383511 3502379 := bstep (se 1 (by rfl) ⟨2626784, by rfl⟩ : syracuseStep 3502379 = 5253569) B5253569
theorem B2076971 : Blo 1383511 2076971 := bstep (se 1 (by rfl) ⟨1557728, by rfl⟩ : syracuseStep 2076971 = 3115457) B3115457
theorem B2077001 : Blo 1383511 2077001 := bstep (se 2 (by rfl) ⟨778875, by rfl⟩ : syracuseStep 2077001 = 1557751) B1557751
theorem B2077115 : Blo 1383511 2077115 := bstep (se 1 (by rfl) ⟨1557836, by rfl⟩ : syracuseStep 2077115 = 3115673) B3115673
theorem B21303773 : Blo 1383511 21303773 := bstep (se 3 (by rfl) ⟨3994457, by rfl⟩ : syracuseStep 21303773 = 7988915) B7988915
theorem B2077175 : Blo 1383511 2077175 := bstep (se 1 (by rfl) ⟨1557881, by rfl⟩ : syracuseStep 2077175 = 3115763) B3115763
theorem B5911051 : Blo 1383511 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B2077199 : Blo 1383511 2077199 := bstep (se 1 (by rfl) ⟨1557899, by rfl⟩ : syracuseStep 2077199 = 3115799) B3115799
theorem B4674077 : Blo 1383511 4674077 := bstep (se 3 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 4674077 = 1752779) B1752779
theorem B2495009 : Blo 1383511 2495009 := bstep (se 2 (by rfl) ⟨935628, by rfl⟩ : syracuseStep 2495009 = 1871257) B1871257
theorem B2077241 : Blo 1383511 2077241 := bstep (se 2 (by rfl) ⟨778965, by rfl⟩ : syracuseStep 2077241 = 1557931) B1557931
theorem B2077319 : Blo 1383511 2077319 := bstep (se 1 (by rfl) ⟨1557989, by rfl⟩ : syracuseStep 2077319 = 3115979) B3115979
theorem B2077355 : Blo 1383511 2077355 := bstep (se 1 (by rfl) ⟨1558016, by rfl⟩ : syracuseStep 2077355 = 3116033) B3116033
theorem B2077385 : Blo 1383511 2077385 := bstep (se 2 (by rfl) ⟨779019, by rfl⟩ : syracuseStep 2077385 = 1558039) B1558039
theorem B2216747 : Blo 1383511 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B2077499 : Blo 1383511 2077499 := bstep (se 1 (by rfl) ⟨1558124, by rfl⟩ : syracuseStep 2077499 = 3116249) B3116249
theorem B2077559 : Blo 1383511 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B2077583 : Blo 1383511 2077583 := bstep (se 1 (by rfl) ⟨1558187, by rfl⟩ : syracuseStep 2077583 = 3116375) B3116375
theorem B2077625 : Blo 1383511 2077625 := bstep (se 2 (by rfl) ⟨779109, by rfl⟩ : syracuseStep 2077625 = 1558219) B1558219
theorem B8426443 : Blo 1383511 8426443 := bstep (se 1 (by rfl) ⟨6319832, by rfl⟩ : syracuseStep 8426443 = 12639665) B12639665
theorem B19190789 : Blo 1383511 19190789 := bstep (se 4 (by rfl) ⟨1799136, by rfl⟩ : syracuseStep 19190789 = 3598273) B3598273
theorem B2077703 : Blo 1383511 2077703 := bstep (se 1 (by rfl) ⟨1558277, by rfl⟩ : syracuseStep 2077703 = 3116555) B3116555
theorem B2077739 : Blo 1383511 2077739 := bstep (se 1 (by rfl) ⟨1558304, by rfl⟩ : syracuseStep 2077739 = 3116609) B3116609
theorem B30364733 : Blo 1383511 30364733 := bstep (se 3 (by rfl) ⟨5693387, by rfl⟩ : syracuseStep 30364733 = 11386775) B11386775
theorem B2077769 : Blo 1383511 2077769 := bstep (se 2 (by rfl) ⟨779163, by rfl⟩ : syracuseStep 2077769 = 1558327) B1558327
theorem B1971319 : Blo 1383511 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B2077883 : Blo 1383511 2077883 := bstep (se 1 (by rfl) ⟨1558412, by rfl⟩ : syracuseStep 2077883 = 3116825) B3116825
theorem B2077943 : Blo 1383511 2077943 := bstep (se 1 (by rfl) ⟨1558457, by rfl⟩ : syracuseStep 2077943 = 3116915) B3116915
theorem B3503371 : Blo 1383511 3503371 := bstep (se 1 (by rfl) ⟨2627528, by rfl⟩ : syracuseStep 3503371 = 5255057) B5255057
theorem B2077967 : Blo 1383511 2077967 := bstep (se 1 (by rfl) ⟨1558475, by rfl⟩ : syracuseStep 2077967 = 3116951) B3116951
theorem B2078009 : Blo 1383511 2078009 := bstep (se 2 (by rfl) ⟨779253, by rfl⟩ : syracuseStep 2078009 = 1558507) B1558507
theorem B2078087 : Blo 1383511 2078087 := bstep (se 1 (by rfl) ⟨1558565, by rfl⟩ : syracuseStep 2078087 = 3117131) B3117131
theorem B3503513 : Blo 1383511 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B2078123 : Blo 1383511 2078123 := bstep (se 1 (by rfl) ⟨1558592, by rfl⟩ : syracuseStep 2078123 = 3117185) B3117185
theorem B72955313 : Blo 1383511 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B3159497 : Blo 1383511 3159497 := bstep (se 2 (by rfl) ⟨1184811, by rfl⟩ : syracuseStep 3159497 = 2369623) B2369623
theorem B2078153 : Blo 1383511 2078153 := bstep (se 2 (by rfl) ⟨779307, by rfl⟩ : syracuseStep 2078153 = 1558615) B1558615
theorem B7009739 : Blo 1383511 7009739 := bstep (se 1 (by rfl) ⟨5257304, by rfl⟩ : syracuseStep 7009739 = 10514609) B10514609
theorem B10507805 : Blo 1383511 10507805 := bstep (se 3 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 10507805 = 3940427) B3940427
theorem B3503675 : Blo 1383511 3503675 := bstep (se 1 (by rfl) ⟨2627756, by rfl⟩ : syracuseStep 3503675 = 5255513) B5255513
theorem B2078267 : Blo 1383511 2078267 := bstep (se 1 (by rfl) ⟨1558700, by rfl⟩ : syracuseStep 2078267 = 3117401) B3117401
theorem B6657623 : Blo 1383511 6657623 := bstep (se 1 (by rfl) ⟨4993217, by rfl⟩ : syracuseStep 6657623 = 9986435) B9986435
theorem B15169295 : Blo 1383511 15169295 := bstep (se 1 (by rfl) ⟨11376971, by rfl⟩ : syracuseStep 15169295 = 22753943) B22753943
theorem B7010063 : Blo 1383511 7010063 := bstep (se 1 (by rfl) ⟨5257547, by rfl⟩ : syracuseStep 7010063 = 10515095) B10515095
theorem B53262197 : Blo 1383511 53262197 := bstep (se 5 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 53262197 = 4993331) B4993331
theorem B3504019 : Blo 1383511 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B4675481 : Blo 1383511 4675481 := bstep (se 2 (by rfl) ⟨1753305, by rfl⟩ : syracuseStep 4675481 = 3506611) B3506611
theorem B5257169 : Blo 1383511 5257169 := bstep (se 2 (by rfl) ⟨1971438, by rfl⟩ : syracuseStep 5257169 = 3942877) B3942877
theorem B7993367 : Blo 1383511 7993367 := bstep (se 1 (by rfl) ⟨5995025, by rfl⟩ : syracuseStep 7993367 = 11990051) B11990051
theorem B3504161 : Blo 1383511 3504161 := bstep (se 2 (by rfl) ⟨1314060, by rfl⟩ : syracuseStep 3504161 = 2628121) B2628121
theorem B5331005 : Blo 1383511 5331005 := bstep (se 3 (by rfl) ⟨999563, by rfl⟩ : syracuseStep 5331005 = 1999127) B1999127
theorem B7886915 : Blo 1383511 7886915 := bstep (se 1 (by rfl) ⟨5915186, by rfl⟩ : syracuseStep 7886915 = 11830373) B11830373
theorem B1751159 : Blo 1383511 1751159 := bstep (se 1 (by rfl) ⟨1313369, by rfl⟩ : syracuseStep 1751159 = 2626739) B2626739
theorem B1751311 : Blo 1383511 1751311 := bstep (se 1 (by rfl) ⟨1313483, by rfl⟩ : syracuseStep 1751311 = 2626967) B2626967
theorem B5257487 : Blo 1383511 5257487 := bstep (se 1 (by rfl) ⟨3943115, by rfl⟩ : syracuseStep 5257487 = 7886231) B7886231
theorem B6314273 : Blo 1383511 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B12622225 : Blo 1383511 12622225 := bstep (se 2 (by rfl) ⟨4733334, by rfl⟩ : syracuseStep 12622225 = 9466669) B9466669
theorem B1751483 : Blo 1383511 1751483 := bstep (se 1 (by rfl) ⟨1313612, by rfl⟩ : syracuseStep 1751483 = 2627225) B2627225
theorem B1685947 : Blo 1383511 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B2955791 : Blo 1383511 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B4209185 : Blo 1383511 4209185 := bstep (se 2 (by rfl) ⟨1578444, by rfl⟩ : syracuseStep 4209185 = 3156889) B3156889
theorem B2628281 : Blo 1383511 2628281 := bstep (se 2 (by rfl) ⟨985605, by rfl⟩ : syracuseStep 2628281 = 1971211) B1971211
theorem B5610221 : Blo 1383511 5610221 := bstep (se 3 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 5610221 = 2103833) B2103833
theorem B9984817 : Blo 1383511 9984817 := bstep (se 2 (by rfl) ⟨3744306, by rfl⟩ : syracuseStep 9984817 = 7488613) B7488613
theorem B4053821 : Blo 1383511 4053821 := bstep (se 3 (by rfl) ⟨760091, by rfl⟩ : syracuseStep 4053821 = 1520183) B1520183
theorem B3505153 : Blo 1383511 3505153 := bstep (se 2 (by rfl) ⟨1314432, by rfl⟩ : syracuseStep 3505153 = 2628865) B2628865
theorem B5397623 : Blo 1383511 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B1383559 : Blo 1383511 1383559 := bstep (se 1 (by rfl) ⟨1037669, by rfl⟩ : syracuseStep 1383559 = 2075339) B2075339
theorem B1383567 : Blo 1383511 1383567 := bstep (se 1 (by rfl) ⟨1037675, by rfl⟩ : syracuseStep 1383567 = 2075351) B2075351
theorem B1383611 : Blo 1383511 1383611 := bstep (se 1 (by rfl) ⟨1037708, by rfl⟩ : syracuseStep 1383611 = 2075417) B2075417
theorem B7011521 : Blo 1383511 7011521 := bstep (se 2 (by rfl) ⟨2629320, by rfl⟩ : syracuseStep 7011521 = 5258641) B5258641
theorem B1383687 : Blo 1383511 1383687 := bstep (se 1 (by rfl) ⟨1037765, by rfl⟩ : syracuseStep 1383687 = 2075531) B2075531
theorem B1383695 : Blo 1383511 1383695 := bstep (se 1 (by rfl) ⟨1037771, by rfl⟩ : syracuseStep 1383695 = 2075543) B2075543
theorem B1383739 : Blo 1383511 1383739 := bstep (se 1 (by rfl) ⟨1037804, by rfl⟩ : syracuseStep 1383739 = 2075609) B2075609
theorem B1383815 : Blo 1383511 1383815 := bstep (se 1 (by rfl) ⟨1037861, by rfl⟩ : syracuseStep 1383815 = 2075723) B2075723
theorem B1752455 : Blo 1383511 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B1383823 : Blo 1383511 1383823 := bstep (se 1 (by rfl) ⟨1037867, by rfl⟩ : syracuseStep 1383823 = 2075735) B2075735
theorem B1383867 : Blo 1383511 1383867 := bstep (se 1 (by rfl) ⟨1037900, by rfl⟩ : syracuseStep 1383867 = 2075801) B2075801
theorem B11992541 : Blo 1383511 11992541 := bstep (se 3 (by rfl) ⟨2248601, by rfl⟩ : syracuseStep 11992541 = 4497203) B4497203
theorem B1383943 : Blo 1383511 1383943 := bstep (se 1 (by rfl) ⟨1037957, by rfl⟩ : syracuseStep 1383943 = 2075915) B2075915
theorem B1383951 : Blo 1383511 1383951 := bstep (se 1 (by rfl) ⟨1037963, by rfl⟩ : syracuseStep 1383951 = 2075927) B2075927
theorem B1383995 : Blo 1383511 1383995 := bstep (se 1 (by rfl) ⟨1037996, by rfl⟩ : syracuseStep 1383995 = 2075993) B2075993
theorem B3505751 : Blo 1383511 3505751 := bstep (se 1 (by rfl) ⟨2629313, by rfl⟩ : syracuseStep 3505751 = 5258627) B5258627
theorem B3743347 : Blo 1383511 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1384071 : Blo 1383511 1384071 := bstep (se 1 (by rfl) ⟨1038053, by rfl⟩ : syracuseStep 1384071 = 2076107) B2076107
theorem B1384079 : Blo 1383511 1384079 := bstep (se 1 (by rfl) ⟨1038059, by rfl⟩ : syracuseStep 1384079 = 2076119) B2076119
theorem B1384123 : Blo 1383511 1384123 := bstep (se 1 (by rfl) ⟨1038092, by rfl⟩ : syracuseStep 1384123 = 2076185) B2076185
theorem B1384199 : Blo 1383511 1384199 := bstep (se 1 (by rfl) ⟨1038149, by rfl⟩ : syracuseStep 1384199 = 2076299) B2076299
theorem B1384207 : Blo 1383511 1384207 := bstep (se 1 (by rfl) ⟨1038155, by rfl⟩ : syracuseStep 1384207 = 2076311) B2076311
theorem B8986405 : Blo 1383511 8986405 := bstep (se 4 (by rfl) ⟨842475, by rfl⟩ : syracuseStep 8986405 = 1684951) B1684951
theorem B3505963 : Blo 1383511 3505963 := bstep (se 1 (by rfl) ⟨2629472, by rfl⟩ : syracuseStep 3505963 = 5258945) B5258945
theorem B7888691 : Blo 1383511 7888691 := bstep (se 1 (by rfl) ⟨5916518, by rfl⟩ : syracuseStep 7888691 = 11833037) B11833037
theorem B1384251 : Blo 1383511 1384251 := bstep (se 1 (by rfl) ⟨1038188, by rfl⟩ : syracuseStep 1384251 = 2076377) B2076377
theorem B2629435 : Blo 1383511 2629435 := bstep (se 1 (by rfl) ⟨1972076, by rfl⟩ : syracuseStep 2629435 = 3944153) B3944153
theorem B13311859 : Blo 1383511 13311859 := bstep (se 1 (by rfl) ⟨9983894, by rfl⟩ : syracuseStep 13311859 = 19967789) B19967789
theorem B1384327 : Blo 1383511 1384327 := bstep (se 1 (by rfl) ⟨1038245, by rfl⟩ : syracuseStep 1384327 = 2076491) B2076491
theorem B1384335 : Blo 1383511 1384335 := bstep (se 1 (by rfl) ⟨1038251, by rfl⟩ : syracuseStep 1384335 = 2076503) B2076503
theorem B3506105 : Blo 1383511 3506105 := bstep (se 2 (by rfl) ⟨1314789, by rfl⟩ : syracuseStep 3506105 = 2629579) B2629579
theorem B1384379 : Blo 1383511 1384379 := bstep (se 1 (by rfl) ⟨1038284, by rfl⟩ : syracuseStep 1384379 = 2076569) B2076569
theorem B7880651 : Blo 1383511 7880651 := bstep (se 1 (by rfl) ⟨5910488, by rfl⟩ : syracuseStep 7880651 = 11820977) B11820977
theorem B1384487 : Blo 1383511 1384487 := bstep (se 1 (by rfl) ⟨1038365, by rfl⟩ : syracuseStep 1384487 = 2076731) B2076731
theorem B1384527 : Blo 1383511 1384527 := bstep (se 1 (by rfl) ⟨1038395, by rfl⟩ : syracuseStep 1384527 = 2076791) B2076791
theorem B1384543 : Blo 1383511 1384543 := bstep (se 1 (by rfl) ⟨1038407, by rfl⟩ : syracuseStep 1384543 = 2076815) B2076815
theorem B1384571 : Blo 1383511 1384571 := bstep (se 1 (by rfl) ⟨1038428, by rfl⟩ : syracuseStep 1384571 = 2076857) B2076857
theorem B1384623 : Blo 1383511 1384623 := bstep (se 1 (by rfl) ⟨1038467, by rfl⟩ : syracuseStep 1384623 = 2076935) B2076935
theorem B2334919 : Blo 1383511 2334919 := bstep (se 1 (by rfl) ⟨1751189, by rfl⟩ : syracuseStep 2334919 = 3502379) B3502379
theorem B1384647 : Blo 1383511 1384647 := bstep (se 1 (by rfl) ⟨1038485, by rfl⟩ : syracuseStep 1384647 = 2076971) B2076971
theorem B1384667 : Blo 1383511 1384667 := bstep (se 1 (by rfl) ⟨1038500, by rfl⟩ : syracuseStep 1384667 = 2077001) B2077001
theorem B3113207 : Blo 1383511 3113207 := bstep (se 1 (by rfl) ⟨2334905, by rfl⟩ : syracuseStep 3113207 = 4669811) B4669811
theorem B4735223 : Blo 1383511 4735223 := bstep (se 1 (by rfl) ⟨3551417, by rfl⟩ : syracuseStep 4735223 = 7102835) B7102835
theorem B1384743 : Blo 1383511 1384743 := bstep (se 1 (by rfl) ⟨1038557, by rfl⟩ : syracuseStep 1384743 = 2077115) B2077115
theorem B4669757 : Blo 1383511 4669757 := bstep (se 3 (by rfl) ⟨875579, by rfl⟩ : syracuseStep 4669757 = 1751159) B1751159
theorem B1384783 : Blo 1383511 1384783 := bstep (se 1 (by rfl) ⟨1038587, by rfl⟩ : syracuseStep 1384783 = 2077175) B2077175
theorem B1384799 : Blo 1383511 1384799 := bstep (se 1 (by rfl) ⟨1038599, by rfl⟩ : syracuseStep 1384799 = 2077199) B2077199
theorem B2335081 : Blo 1383511 2335081 := bstep (se 2 (by rfl) ⟨875655, by rfl⟩ : syracuseStep 2335081 = 1751311) B1751311
theorem B1663339 : Blo 1383511 1663339 := bstep (se 1 (by rfl) ⟨1247504, by rfl⟩ : syracuseStep 1663339 = 2495009) B2495009
theorem B1384827 : Blo 1383511 1384827 := bstep (se 1 (by rfl) ⟨1038620, by rfl⟩ : syracuseStep 1384827 = 2077241) B2077241
theorem B10510721 : Blo 1383511 10510721 := bstep (se 2 (by rfl) ⟨3941520, by rfl⟩ : syracuseStep 10510721 = 7883041) B7883041
theorem B3506561 : Blo 1383511 3506561 := bstep (se 2 (by rfl) ⟨1314960, by rfl⟩ : syracuseStep 3506561 = 2629921) B2629921
theorem B1384879 : Blo 1383511 1384879 := bstep (se 1 (by rfl) ⟨1038659, by rfl⟩ : syracuseStep 1384879 = 2077319) B2077319
theorem B1384903 : Blo 1383511 1384903 := bstep (se 1 (by rfl) ⟨1038677, by rfl⟩ : syracuseStep 1384903 = 2077355) B2077355
theorem B29958605 : Blo 1383511 29958605 := bstep (se 3 (by rfl) ⟨5617238, by rfl⟩ : syracuseStep 29958605 = 11234477) B11234477
theorem B1384923 : Blo 1383511 1384923 := bstep (se 1 (by rfl) ⟨1038692, by rfl⟩ : syracuseStep 1384923 = 2077385) B2077385
theorem B1557031 : Blo 1383511 1557031 := bstep (se 1 (by rfl) ⟨1167773, by rfl⟩ : syracuseStep 1557031 = 2335547) B2335547
theorem B1384999 : Blo 1383511 1384999 := bstep (se 1 (by rfl) ⟨1038749, by rfl⟩ : syracuseStep 1384999 = 2077499) B2077499
theorem B1385039 : Blo 1383511 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B1385055 : Blo 1383511 1385055 := bstep (se 1 (by rfl) ⟨1038791, by rfl⟩ : syracuseStep 1385055 = 2077583) B2077583
theorem B1385083 : Blo 1383511 1385083 := bstep (se 1 (by rfl) ⟨1038812, by rfl⟩ : syracuseStep 1385083 = 2077625) B2077625
theorem B1385135 : Blo 1383511 1385135 := bstep (se 1 (by rfl) ⟨1038851, by rfl⟩ : syracuseStep 1385135 = 2077703) B2077703
theorem B7881401 : Blo 1383511 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B1385159 : Blo 1383511 1385159 := bstep (se 1 (by rfl) ⟨1038869, by rfl⟩ : syracuseStep 1385159 = 2077739) B2077739
theorem B20243155 : Blo 1383511 20243155 := bstep (se 1 (by rfl) ⟨15182366, by rfl⟩ : syracuseStep 20243155 = 30364733) B30364733
theorem B1385179 : Blo 1383511 1385179 := bstep (se 1 (by rfl) ⟨1038884, by rfl⟩ : syracuseStep 1385179 = 2077769) B2077769
theorem B1385255 : Blo 1383511 1385255 := bstep (se 1 (by rfl) ⟨1038941, by rfl⟩ : syracuseStep 1385255 = 2077883) B2077883
theorem B5260099 : Blo 1383511 5260099 := bstep (se 1 (by rfl) ⟨3945074, by rfl⟩ : syracuseStep 5260099 = 7890149) B7890149
theorem B3113801 : Blo 1383511 3113801 := bstep (se 2 (by rfl) ⟨1167675, by rfl⟩ : syracuseStep 3113801 = 2335351) B2335351
theorem B1385295 : Blo 1383511 1385295 := bstep (se 1 (by rfl) ⟨1038971, by rfl⟩ : syracuseStep 1385295 = 2077943) B2077943
theorem B1385311 : Blo 1383511 1385311 := bstep (se 1 (by rfl) ⟨1038983, by rfl⟩ : syracuseStep 1385311 = 2077967) B2077967
theorem B1385339 : Blo 1383511 1385339 := bstep (se 1 (by rfl) ⟨1039004, by rfl⟩ : syracuseStep 1385339 = 2078009) B2078009
theorem B1385391 : Blo 1383511 1385391 := bstep (se 1 (by rfl) ⟨1039043, by rfl⟩ : syracuseStep 1385391 = 2078087) B2078087
theorem B7013303 : Blo 1383511 7013303 := bstep (se 1 (by rfl) ⟨5259977, by rfl⟩ : syracuseStep 7013303 = 10519955) B10519955
theorem B2335675 : Blo 1383511 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B48636875 : Blo 1383511 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B1385415 : Blo 1383511 1385415 := bstep (se 1 (by rfl) ⟨1039061, by rfl⟩ : syracuseStep 1385415 = 2078123) B2078123
theorem B2106331 : Blo 1383511 2106331 := bstep (se 1 (by rfl) ⟨1579748, by rfl⟩ : syracuseStep 2106331 = 3159497) B3159497
theorem B1385435 : Blo 1383511 1385435 := bstep (se 1 (by rfl) ⟨1039076, by rfl⟩ : syracuseStep 1385435 = 2078153) B2078153
theorem B7005203 : Blo 1383511 7005203 := bstep (se 1 (by rfl) ⟨5253902, by rfl⟩ : syracuseStep 7005203 = 10507805) B10507805
theorem B5997587 : Blo 1383511 5997587 := bstep (se 1 (by rfl) ⟨4498190, by rfl⟩ : syracuseStep 5997587 = 8996381) B8996381
theorem B2335783 : Blo 1383511 2335783 := bstep (se 1 (by rfl) ⟨1751837, by rfl⟩ : syracuseStep 2335783 = 3503675) B3503675
theorem B1385511 : Blo 1383511 1385511 := bstep (se 1 (by rfl) ⟨1039133, by rfl⟩ : syracuseStep 1385511 = 2078267) B2078267
theorem B13313089 : Blo 1383511 13313089 := bstep (se 2 (by rfl) ⟨4992408, by rfl⟩ : syracuseStep 13313089 = 9984817) B9984817
theorem B5260403 : Blo 1383511 5260403 := bstep (se 1 (by rfl) ⟨3945302, by rfl⟩ : syracuseStep 5260403 = 7890605) B7890605
theorem B4670621 : Blo 1383511 4670621 := bstep (se 3 (by rfl) ⟨875741, by rfl⟩ : syracuseStep 4670621 = 1751483) B1751483
theorem B2336107 : Blo 1383511 2336107 := bstep (se 1 (by rfl) ⟨1752080, by rfl⟩ : syracuseStep 2336107 = 3504161) B3504161
theorem B7882109 : Blo 1383511 7882109 := bstep (se 3 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 7882109 = 2955791) B2955791
theorem B170526131 : Blo 1383511 170526131 := bstep (se 1 (by rfl) ⟨127894598, by rfl⟩ : syracuseStep 170526131 = 255789197) B255789197
theorem B13297097 : Blo 1383511 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B3114593 : Blo 1383511 3114593 := bstep (se 2 (by rfl) ⟨1167972, by rfl⟩ : syracuseStep 3114593 = 2335945) B2335945
theorem B4671161 : Blo 1383511 4671161 := bstep (se 2 (by rfl) ⟨1751685, by rfl⟩ : syracuseStep 4671161 = 3503371) B3503371
theorem B7997251 : Blo 1383511 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B3114935 : Blo 1383511 3114935 := bstep (se 1 (by rfl) ⟨2336201, by rfl⟩ : syracuseStep 3114935 = 4672403) B4672403
theorem B3598415 : Blo 1383511 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B1558651 : Blo 1383511 1558651 := bstep (se 1 (by rfl) ⟨1168988, by rfl⟩ : syracuseStep 1558651 = 2337977) B2337977
theorem B4991129 : Blo 1383511 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B4671755 : Blo 1383511 4671755 := bstep (se 1 (by rfl) ⟨3503816, by rfl⟩ : syracuseStep 4671755 = 7007633) B7007633
theorem B2337167 : Blo 1383511 2337167 := bstep (se 1 (by rfl) ⟨1752875, by rfl⟩ : syracuseStep 2337167 = 3505751) B3505751
theorem B3115529 : Blo 1383511 3115529 := bstep (se 2 (by rfl) ⟨1168323, by rfl⟩ : syracuseStep 3115529 = 2336647) B2336647
theorem B4672025 : Blo 1383511 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B2337403 : Blo 1383511 2337403 := bstep (se 1 (by rfl) ⟨1753052, by rfl⟩ : syracuseStep 2337403 = 3506105) B3506105
theorem B5253767 : Blo 1383511 5253767 := bstep (se 1 (by rfl) ⟨3940325, by rfl⟩ : syracuseStep 5253767 = 7880651) B7880651
theorem B19950259 : Blo 1383511 19950259 := bstep (se 1 (by rfl) ⟨14962694, by rfl⟩ : syracuseStep 19950259 = 29925389) B29925389
theorem B8874755 : Blo 1383511 8874755 := bstep (se 1 (by rfl) ⟨6656066, by rfl⟩ : syracuseStep 8874755 = 13312133) B13312133
theorem B134720293 : Blo 1383511 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B3115871 : Blo 1383511 3115871 := bstep (se 1 (by rfl) ⟨2336903, by rfl⟩ : syracuseStep 3115871 = 4673807) B4673807
theorem B2075567 : Blo 1383511 2075567 := bstep (se 1 (by rfl) ⟨1556675, by rfl⟩ : syracuseStep 2075567 = 3113351) B3113351
theorem B3943343 : Blo 1383511 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B2075657 : Blo 1383511 2075657 := bstep (se 2 (by rfl) ⟨778371, by rfl⟩ : syracuseStep 2075657 = 1556743) B1556743
theorem B3116051 : Blo 1383511 3116051 := bstep (se 1 (by rfl) ⟨2337038, by rfl⟩ : syracuseStep 3116051 = 4674077) B4674077
theorem B2075687 : Blo 1383511 2075687 := bstep (se 1 (by rfl) ⟨1556765, by rfl⟩ : syracuseStep 2075687 = 3113531) B3113531
theorem B2075771 : Blo 1383511 2075771 := bstep (se 1 (by rfl) ⟨1556828, by rfl⟩ : syracuseStep 2075771 = 3113657) B3113657
theorem B16829633 : Blo 1383511 16829633 := bstep (se 2 (by rfl) ⟨6311112, by rfl⟩ : syracuseStep 16829633 = 12622225) B12622225
theorem B17738999 : Blo 1383511 17738999 := bstep (se 1 (by rfl) ⟨13304249, by rfl⟩ : syracuseStep 17738999 = 26608499) B26608499
theorem B2075897 : Blo 1383511 2075897 := bstep (se 2 (by rfl) ⟨778461, by rfl⟩ : syracuseStep 2075897 = 1556923) B1556923
theorem B2247929 : Blo 1383511 2247929 := bstep (se 2 (by rfl) ⟨842973, by rfl⟩ : syracuseStep 2247929 = 1685947) B1685947
theorem B43240757 : Blo 1383511 43240757 := bstep (se 5 (by rfl) ⟨2026910, by rfl⟩ : syracuseStep 43240757 = 4053821) B4053821
theorem B2075999 : Blo 1383511 2075999 := bstep (se 1 (by rfl) ⟨1556999, by rfl⟩ : syracuseStep 2075999 = 3113999) B3113999
theorem B3116393 : Blo 1383511 3116393 := bstep (se 2 (by rfl) ⟨1168647, by rfl⟩ : syracuseStep 3116393 = 2337295) B2337295
theorem B2076011 : Blo 1383511 2076011 := bstep (se 1 (by rfl) ⟨1557008, by rfl⟩ : syracuseStep 2076011 = 3114017) B3114017
theorem B2076239 : Blo 1383511 2076239 := bstep (se 1 (by rfl) ⟨1557179, by rfl⟩ : syracuseStep 2076239 = 3114359) B3114359
theorem B5254753 : Blo 1383511 5254753 := bstep (se 2 (by rfl) ⟨1970532, by rfl⟩ : syracuseStep 5254753 = 3941065) B3941065
theorem B4673159 : Blo 1383511 4673159 := bstep (se 1 (by rfl) ⟨3504869, by rfl⟩ : syracuseStep 4673159 = 7009739) B7009739
theorem B4673213 : Blo 1383511 4673213 := bstep (se 3 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 4673213 = 1752455) B1752455
theorem B2076359 : Blo 1383511 2076359 := bstep (se 1 (by rfl) ⟨1557269, by rfl⟩ : syracuseStep 2076359 = 3114539) B3114539
theorem B10112863 : Blo 1383511 10112863 := bstep (se 1 (by rfl) ⟨7584647, by rfl⟩ : syracuseStep 10112863 = 15169295) B15169295
theorem B4673375 : Blo 1383511 4673375 := bstep (se 1 (by rfl) ⟨3505031, by rfl⟩ : syracuseStep 4673375 = 7010063) B7010063
theorem B2076521 : Blo 1383511 2076521 := bstep (se 2 (by rfl) ⟨778695, by rfl⟩ : syracuseStep 2076521 = 1557391) B1557391
theorem B7008119 : Blo 1383511 7008119 := bstep (se 1 (by rfl) ⟨5256089, by rfl⟩ : syracuseStep 7008119 = 10512179) B10512179
theorem B35508131 : Blo 1383511 35508131 := bstep (se 1 (by rfl) ⟨26631098, by rfl⟩ : syracuseStep 35508131 = 53262197) B53262197
theorem B2076599 : Blo 1383511 2076599 := bstep (se 1 (by rfl) ⟨1557449, by rfl⟩ : syracuseStep 2076599 = 3114899) B3114899
theorem B11235257 : Blo 1383511 11235257 := bstep (se 2 (by rfl) ⟨4213221, by rfl⟩ : syracuseStep 11235257 = 8426443) B8426443
theorem B3116987 : Blo 1383511 3116987 := bstep (se 1 (by rfl) ⟨2337740, by rfl⟩ : syracuseStep 3116987 = 4675481) B4675481
theorem B2076635 : Blo 1383511 2076635 := bstep (se 1 (by rfl) ⟨1557476, by rfl⟩ : syracuseStep 2076635 = 3114953) B3114953
theorem B4673537 : Blo 1383511 4673537 := bstep (se 2 (by rfl) ⟨1752576, by rfl⟩ : syracuseStep 4673537 = 3505153) B3505153
theorem B5328911 : Blo 1383511 5328911 := bstep (se 1 (by rfl) ⟨3996683, by rfl⟩ : syracuseStep 5328911 = 7993367) B7993367
theorem B5255225 : Blo 1383511 5255225 := bstep (se 2 (by rfl) ⟨1970709, by rfl⟩ : syracuseStep 5255225 = 3941419) B3941419
theorem B3117113 : Blo 1383511 3117113 := bstep (se 2 (by rfl) ⟨1168917, by rfl⟩ : syracuseStep 3117113 = 2337835) B2337835
theorem B89796923 : Blo 1383511 89796923 := bstep (se 1 (by rfl) ⟨67347692, by rfl⟩ : syracuseStep 89796923 = 134695385) B134695385
theorem B2494793 : Blo 1383511 2494793 := bstep (se 2 (by rfl) ⟨935547, by rfl⟩ : syracuseStep 2494793 = 1871095) B1871095
theorem B2806123 : Blo 1383511 2806123 := bstep (se 1 (by rfl) ⟨2104592, by rfl⟩ : syracuseStep 2806123 = 4209185) B4209185
theorem B71897489 : Blo 1383511 71897489 := bstep (se 2 (by rfl) ⟨26961558, by rfl⟩ : syracuseStep 71897489 = 53923117) B53923117
theorem B2077103 : Blo 1383511 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B3740147 : Blo 1383511 3740147 := bstep (se 1 (by rfl) ⟨2805110, by rfl⟩ : syracuseStep 3740147 = 5610221) B5610221
theorem B26604035 : Blo 1383511 26604035 := bstep (se 1 (by rfl) ⟨19953026, by rfl⟩ : syracuseStep 26604035 = 39906053) B39906053
theorem B2077193 : Blo 1383511 2077193 := bstep (se 2 (by rfl) ⟨778947, by rfl⟩ : syracuseStep 2077193 = 1557895) B1557895
theorem B2077223 : Blo 1383511 2077223 := bstep (se 1 (by rfl) ⟨1557917, by rfl⟩ : syracuseStep 2077223 = 3115835) B3115835
theorem B2077307 : Blo 1383511 2077307 := bstep (se 1 (by rfl) ⟨1557980, by rfl⟩ : syracuseStep 2077307 = 3115961) B3115961
theorem B2495225 : Blo 1383511 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B2077433 : Blo 1383511 2077433 := bstep (se 2 (by rfl) ⟨779037, by rfl⟩ : syracuseStep 2077433 = 1558075) B1558075
theorem B5911325 : Blo 1383511 5911325 := bstep (se 3 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 5911325 = 2216747) B2216747
theorem B4674347 : Blo 1383511 4674347 := bstep (se 1 (by rfl) ⟨3505760, by rfl⟩ : syracuseStep 4674347 = 7011521) B7011521
theorem B2077535 : Blo 1383511 2077535 := bstep (se 1 (by rfl) ⟨1558151, by rfl⟩ : syracuseStep 2077535 = 3116303) B3116303
theorem B2077547 : Blo 1383511 2077547 := bstep (se 1 (by rfl) ⟨1558160, by rfl⟩ : syracuseStep 2077547 = 3116321) B3116321
theorem B5256211 : Blo 1383511 5256211 := bstep (se 1 (by rfl) ⟨3942158, by rfl⟩ : syracuseStep 5256211 = 7884317) B7884317
theorem B11981873 : Blo 1383511 11981873 := bstep (se 2 (by rfl) ⟨4493202, by rfl⟩ : syracuseStep 11981873 = 8986405) B8986405
theorem B13300787 : Blo 1383511 13300787 := bstep (se 1 (by rfl) ⟨9975590, by rfl⟩ : syracuseStep 13300787 = 19951181) B19951181
theorem B4674617 : Blo 1383511 4674617 := bstep (se 2 (by rfl) ⟨1752981, by rfl⟩ : syracuseStep 4674617 = 3505963) B3505963
theorem B8991811 : Blo 1383511 8991811 := bstep (se 1 (by rfl) ⟨6743858, by rfl⟩ : syracuseStep 8991811 = 13487717) B13487717
theorem B2077775 : Blo 1383511 2077775 := bstep (se 1 (by rfl) ⟨1558331, by rfl⟩ : syracuseStep 2077775 = 3116663) B3116663
theorem B17749145 : Blo 1383511 17749145 := bstep (se 2 (by rfl) ⟨6655929, by rfl⟩ : syracuseStep 17749145 = 13311859) B13311859
theorem B2077895 : Blo 1383511 2077895 := bstep (se 1 (by rfl) ⟨1558421, by rfl⟩ : syracuseStep 2077895 = 3116843) B3116843
theorem B3503351 : Blo 1383511 3503351 := bstep (se 1 (by rfl) ⟨2627513, by rfl⟩ : syracuseStep 3503351 = 5255027) B5255027
theorem B9983321 : Blo 1383511 9983321 := bstep (se 2 (by rfl) ⟨3743745, by rfl⟩ : syracuseStep 9983321 = 7487491) B7487491
theorem B2217311 : Blo 1383511 2217311 := bstep (se 1 (by rfl) ⟨1662983, by rfl⟩ : syracuseStep 2217311 = 3325967) B3325967
theorem B2626921 : Blo 1383511 2626921 := bstep (se 2 (by rfl) ⟨985095, by rfl⟩ : syracuseStep 2626921 = 1970191) B1970191
theorem B2078057 : Blo 1383511 2078057 := bstep (se 2 (by rfl) ⟨779271, by rfl⟩ : syracuseStep 2078057 = 1558543) B1558543
theorem B4674941 : Blo 1383511 4674941 := bstep (se 3 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 4674941 = 1753103) B1753103
theorem B2078135 : Blo 1383511 2078135 := bstep (se 1 (by rfl) ⟨1558601, by rfl⟩ : syracuseStep 2078135 = 3117203) B3117203
theorem B2078171 : Blo 1383511 2078171 := bstep (se 1 (by rfl) ⟨1558628, by rfl⟩ : syracuseStep 2078171 = 3117257) B3117257
theorem B4986355 : Blo 1383511 4986355 := bstep (se 1 (by rfl) ⟨3739766, by rfl⟩ : syracuseStep 4986355 = 7479533) B7479533
theorem B11826749 : Blo 1383511 11826749 := bstep (se 3 (by rfl) ⟨2217515, by rfl⟩ : syracuseStep 11826749 = 4435031) B4435031
theorem B4675211 : Blo 1383511 4675211 := bstep (se 1 (by rfl) ⟨3506408, by rfl⟩ : syracuseStep 4675211 = 7012817) B7012817
theorem B4986515 : Blo 1383511 4986515 := bstep (se 1 (by rfl) ⟨3739886, by rfl⟩ : syracuseStep 4986515 = 7479773) B7479773
theorem B14202515 : Blo 1383511 14202515 := bstep (se 1 (by rfl) ⟨10651886, by rfl⟩ : syracuseStep 14202515 = 21303773) B21303773
theorem B7886483 : Blo 1383511 7886483 := bstep (se 1 (by rfl) ⟨5914862, by rfl⟩ : syracuseStep 7886483 = 11829725) B11829725
theorem B1971911 : Blo 1383511 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B2496199 : Blo 1383511 2496199 := bstep (se 1 (by rfl) ⟨1872149, by rfl⟩ : syracuseStep 2496199 = 3744299) B3744299
theorem B2217721 : Blo 1383511 2217721 := bstep (se 2 (by rfl) ⟨831645, by rfl⟩ : syracuseStep 2217721 = 1663291) B1663291
theorem B2217823 : Blo 1383511 2217823 := bstep (se 1 (by rfl) ⟨1663367, by rfl⟩ : syracuseStep 2217823 = 3326735) B3326735
theorem B12793859 : Blo 1383511 12793859 := bstep (se 1 (by rfl) ⟨9595394, by rfl⟩ : syracuseStep 12793859 = 19190789) B19190789
theorem B10508291 : Blo 1383511 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B2627795 : Blo 1383511 2627795 := bstep (se 1 (by rfl) ⟨1970846, by rfl⟩ : syracuseStep 2627795 = 3941693) B3941693
theorem B14211377 : Blo 1383511 14211377 := bstep (se 2 (by rfl) ⟨5329266, by rfl⟩ : syracuseStep 14211377 = 10658533) B10658533
theorem B7887233 : Blo 1383511 7887233 := bstep (se 2 (by rfl) ⟨2957712, by rfl⟩ : syracuseStep 7887233 = 5915425) B5915425
theorem B4438415 : Blo 1383511 4438415 := bstep (se 1 (by rfl) ⟨3328811, by rfl⟩ : syracuseStep 4438415 = 6657623) B6657623
theorem B44923373 : Blo 1383511 44923373 := bstep (se 3 (by rfl) ⟨8423132, by rfl⟩ : syracuseStep 44923373 = 16846265) B16846265
theorem B31980109 : Blo 1383511 31980109 := bstep (se 3 (by rfl) ⟨5996270, by rfl⟩ : syracuseStep 31980109 = 11992541) B11992541
theorem B9984647 : Blo 1383511 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B3504779 : Blo 1383511 3504779 := bstep (se 1 (by rfl) ⟨2628584, by rfl⟩ : syracuseStep 3504779 = 5257169) B5257169
theorem B3554003 : Blo 1383511 3554003 := bstep (se 1 (by rfl) ⟨2665502, by rfl⟩ : syracuseStep 3554003 = 5331005) B5331005
theorem B5257943 : Blo 1383511 5257943 := bstep (se 1 (by rfl) ⟨3943457, by rfl⟩ : syracuseStep 5257943 = 7886915) B7886915
theorem B2628425 : Blo 1383511 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B7887689 : Blo 1383511 7887689 := bstep (se 2 (by rfl) ⟨2957883, by rfl⟩ : syracuseStep 7887689 = 5915767) B5915767
theorem B3504991 : Blo 1383511 3504991 := bstep (se 1 (by rfl) ⟨2628743, by rfl⟩ : syracuseStep 3504991 = 5257487) B5257487
theorem B4209515 : Blo 1383511 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B1383519 : Blo 1383511 1383519 := bstep (se 1 (by rfl) ⟨1037639, by rfl⟩ : syracuseStep 1383519 = 2075279) B2075279
theorem B1383547 : Blo 1383511 1383547 := bstep (se 1 (by rfl) ⟨1037660, by rfl⟩ : syracuseStep 1383547 = 2075321) B2075321
theorem B1752187 : Blo 1383511 1752187 := bstep (se 1 (by rfl) ⟨1314140, by rfl⟩ : syracuseStep 1752187 = 2628281) B2628281
theorem B8871065 : Blo 1383511 8871065 := bstep (se 2 (by rfl) ⟨3326649, by rfl⟩ : syracuseStep 8871065 = 6653299) B6653299
theorem B1383599 : Blo 1383511 1383599 := bstep (se 1 (by rfl) ⟨1037699, by rfl⟩ : syracuseStep 1383599 = 2075399) B2075399
theorem B1383623 : Blo 1383511 1383623 := bstep (se 1 (by rfl) ⟨1037717, by rfl⟩ : syracuseStep 1383623 = 2075435) B2075435
theorem B1383643 : Blo 1383511 1383643 := bstep (se 1 (by rfl) ⟨1037732, by rfl⟩ : syracuseStep 1383643 = 2075465) B2075465
theorem B8871191 : Blo 1383511 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B1383719 : Blo 1383511 1383719 := bstep (se 1 (by rfl) ⟨1037789, by rfl⟩ : syracuseStep 1383719 = 2075579) B2075579
theorem B1383759 : Blo 1383511 1383759 := bstep (se 1 (by rfl) ⟨1037819, by rfl⟩ : syracuseStep 1383759 = 2075639) B2075639
theorem B1383775 : Blo 1383511 1383775 := bstep (se 1 (by rfl) ⟨1037831, by rfl⟩ : syracuseStep 1383775 = 2075663) B2075663
theorem B1383803 : Blo 1383511 1383803 := bstep (se 1 (by rfl) ⟨1037852, by rfl⟩ : syracuseStep 1383803 = 2075705) B2075705
theorem B23641469 : Blo 1383511 23641469 := bstep (se 3 (by rfl) ⟨4432775, by rfl⟩ : syracuseStep 23641469 = 8865551) B8865551
theorem B3325313 : Blo 1383511 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B3743119 : Blo 1383511 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B1383855 : Blo 1383511 1383855 := bstep (se 1 (by rfl) ⟨1037891, by rfl⟩ : syracuseStep 1383855 = 2075783) B2075783
theorem B1383879 : Blo 1383511 1383879 := bstep (se 1 (by rfl) ⟨1037909, by rfl⟩ : syracuseStep 1383879 = 2075819) B2075819
theorem B1383899 : Blo 1383511 1383899 := bstep (se 1 (by rfl) ⟨1037924, by rfl⟩ : syracuseStep 1383899 = 2075849) B2075849
theorem B8986099 : Blo 1383511 8986099 := bstep (se 1 (by rfl) ⟨6739574, by rfl⟩ : syracuseStep 8986099 = 13479149) B13479149
theorem B1383975 : Blo 1383511 1383975 := bstep (se 1 (by rfl) ⟨1037981, by rfl⟩ : syracuseStep 1383975 = 2075963) B2075963
theorem B1384015 : Blo 1383511 1384015 := bstep (se 1 (by rfl) ⟨1038011, by rfl⟩ : syracuseStep 1384015 = 2076023) B2076023
theorem B2629199 : Blo 1383511 2629199 := bstep (se 1 (by rfl) ⟨1971899, by rfl⟩ : syracuseStep 2629199 = 3943799) B3943799
theorem B22453847 : Blo 1383511 22453847 := bstep (se 1 (by rfl) ⟨16840385, by rfl⟩ : syracuseStep 22453847 = 33680771) B33680771
theorem B1384031 : Blo 1383511 1384031 := bstep (se 1 (by rfl) ⟨1038023, by rfl⟩ : syracuseStep 1384031 = 2076047) B2076047
theorem B1384059 : Blo 1383511 1384059 := bstep (se 1 (by rfl) ⟨1038044, by rfl⟩ : syracuseStep 1384059 = 2076089) B2076089
theorem B1384111 : Blo 1383511 1384111 := bstep (se 1 (by rfl) ⟨1038083, by rfl⟩ : syracuseStep 1384111 = 2076167) B2076167
theorem B14966461 : Blo 1383511 14966461 := bstep (se 3 (by rfl) ⟨2806211, by rfl⟩ : syracuseStep 14966461 = 5612423) B5612423
theorem B5611207 : Blo 1383511 5611207 := bstep (se 1 (by rfl) ⟨4208405, by rfl⟩ : syracuseStep 5611207 = 8416811) B8416811
theorem B1384135 : Blo 1383511 1384135 := bstep (se 1 (by rfl) ⟨1038101, by rfl⟩ : syracuseStep 1384135 = 2076203) B2076203
theorem B1384155 : Blo 1383511 1384155 := bstep (se 1 (by rfl) ⟨1038116, by rfl⟩ : syracuseStep 1384155 = 2076233) B2076233
theorem B3505913 : Blo 1383511 3505913 := bstep (se 2 (by rfl) ⟨1314717, by rfl⟩ : syracuseStep 3505913 = 2629435) B2629435
theorem B1384231 : Blo 1383511 1384231 := bstep (se 1 (by rfl) ⟨1038173, by rfl⟩ : syracuseStep 1384231 = 2076347) B2076347
theorem B1384271 : Blo 1383511 1384271 := bstep (se 1 (by rfl) ⟨1038203, by rfl⟩ : syracuseStep 1384271 = 2076407) B2076407
theorem B1384287 : Blo 1383511 1384287 := bstep (se 1 (by rfl) ⟨1038215, by rfl⟩ : syracuseStep 1384287 = 2076431) B2076431
theorem B5259127 : Blo 1383511 5259127 := bstep (se 1 (by rfl) ⟨3944345, by rfl⟩ : syracuseStep 5259127 = 7888691) B7888691
theorem B1384315 : Blo 1383511 1384315 := bstep (se 1 (by rfl) ⟨1038236, by rfl⟩ : syracuseStep 1384315 = 2076473) B2076473
theorem B1384367 : Blo 1383511 1384367 := bstep (se 1 (by rfl) ⟨1038275, by rfl⟩ : syracuseStep 1384367 = 2076551) B2076551
theorem B1384391 : Blo 1383511 1384391 := bstep (se 1 (by rfl) ⟨1038293, by rfl⟩ : syracuseStep 1384391 = 2076587) B2076587
theorem B2334683 : Blo 1383511 2334683 := bstep (se 1 (by rfl) ⟨1751012, by rfl⟩ : syracuseStep 2334683 = 3502025) B3502025
theorem B1384411 : Blo 1383511 1384411 := bstep (se 1 (by rfl) ⟨1038308, by rfl⟩ : syracuseStep 1384411 = 2076617) B2076617
theorem B3113171 : Blo 1383511 3113171 := bstep (se 1 (by rfl) ⟨2334878, by rfl⟩ : syracuseStep 3113171 = 4669757) B4669757
theorem B1663195 : Blo 1383511 1663195 := bstep (se 1 (by rfl) ⟨1247396, by rfl⟩ : syracuseStep 1663195 = 2494793) B2494793
theorem B3113225 : Blo 1383511 3113225 := bstep (se 2 (by rfl) ⟨1167459, by rfl⟩ : syracuseStep 3113225 = 2334919) B2334919
theorem B47931659 : Blo 1383511 47931659 := bstep (se 1 (by rfl) ⟨35948744, by rfl⟩ : syracuseStep 47931659 = 71897489) B71897489
theorem B1384735 : Blo 1383511 1384735 := bstep (se 1 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 1384735 = 2077103) B2077103
theorem B19972403 : Blo 1383511 19972403 := bstep (se 1 (by rfl) ⟨14979302, by rfl⟩ : syracuseStep 19972403 = 29958605) B29958605
theorem B17736023 : Blo 1383511 17736023 := bstep (se 1 (by rfl) ⟨13302017, by rfl⟩ : syracuseStep 17736023 = 26604035) B26604035
theorem B1384795 : Blo 1383511 1384795 := bstep (se 1 (by rfl) ⟨1038596, by rfl⟩ : syracuseStep 1384795 = 2077193) B2077193
theorem B1384815 : Blo 1383511 1384815 := bstep (se 1 (by rfl) ⟨1038611, by rfl⟩ : syracuseStep 1384815 = 2077223) B2077223
theorem B1384871 : Blo 1383511 1384871 := bstep (se 1 (by rfl) ⟨1038653, by rfl⟩ : syracuseStep 1384871 = 2077307) B2077307
theorem B3113441 : Blo 1383511 3113441 := bstep (se 2 (by rfl) ⟨1167540, by rfl⟩ : syracuseStep 3113441 = 2335081) B2335081
theorem B1384955 : Blo 1383511 1384955 := bstep (se 1 (by rfl) ⟨1038716, by rfl⟩ : syracuseStep 1384955 = 2077433) B2077433
theorem B3940883 : Blo 1383511 3940883 := bstep (se 1 (by rfl) ⟨2955662, by rfl⟩ : syracuseStep 3940883 = 5911325) B5911325
theorem B1385023 : Blo 1383511 1385023 := bstep (se 1 (by rfl) ⟨1038767, by rfl⟩ : syracuseStep 1385023 = 2077535) B2077535
theorem B1385031 : Blo 1383511 1385031 := bstep (se 1 (by rfl) ⟨1038773, by rfl⟩ : syracuseStep 1385031 = 2077547) B2077547
theorem B32424583 : Blo 1383511 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B4670135 : Blo 1383511 4670135 := bstep (se 1 (by rfl) ⟨3502601, by rfl⟩ : syracuseStep 4670135 = 7005203) B7005203
theorem B7987915 : Blo 1383511 7987915 := bstep (se 1 (by rfl) ⟨5990936, by rfl⟩ : syracuseStep 7987915 = 11981873) B11981873
theorem B1385183 : Blo 1383511 1385183 := bstep (se 1 (by rfl) ⟨1038887, by rfl⟩ : syracuseStep 1385183 = 2077775) B2077775
theorem B3506935 : Blo 1383511 3506935 := bstep (se 1 (by rfl) ⟨2630201, by rfl⟩ : syracuseStep 3506935 = 5260403) B5260403
theorem B42640145 : Blo 1383511 42640145 := bstep (se 2 (by rfl) ⟨15990054, by rfl⟩ : syracuseStep 42640145 = 31980109) B31980109
theorem B3113747 : Blo 1383511 3113747 := bstep (se 1 (by rfl) ⟨2335310, by rfl⟩ : syracuseStep 3113747 = 4670621) B4670621
theorem B1385263 : Blo 1383511 1385263 := bstep (se 1 (by rfl) ⟨1038947, by rfl⟩ : syracuseStep 1385263 = 2077895) B2077895
theorem B2335567 : Blo 1383511 2335567 := bstep (se 1 (by rfl) ⟨1751675, by rfl⟩ : syracuseStep 2335567 = 3503351) B3503351
theorem B26600345 : Blo 1383511 26600345 := bstep (se 2 (by rfl) ⟨9975129, by rfl⟩ : syracuseStep 26600345 = 19950259) B19950259
theorem B1385371 : Blo 1383511 1385371 := bstep (se 1 (by rfl) ⟨1039028, by rfl⟩ : syracuseStep 1385371 = 2078057) B2078057
theorem B1385423 : Blo 1383511 1385423 := bstep (se 1 (by rfl) ⟨1039067, by rfl⟩ : syracuseStep 1385423 = 2078135) B2078135
theorem B8864731 : Blo 1383511 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1385447 : Blo 1383511 1385447 := bstep (se 1 (by rfl) ⟨1039085, by rfl⟩ : syracuseStep 1385447 = 2078171) B2078171
theorem B179627057 : Blo 1383511 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B7013465 : Blo 1383511 7013465 := bstep (se 2 (by rfl) ⟨2630049, by rfl⟩ : syracuseStep 7013465 = 5260099) B5260099
theorem B3114107 : Blo 1383511 3114107 := bstep (se 1 (by rfl) ⟨2335580, by rfl⟩ : syracuseStep 3114107 = 4671161) B4671161
theorem B3114233 : Blo 1383511 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B8529239 : Blo 1383511 8529239 := bstep (se 1 (by rfl) ⟨6396929, by rfl⟩ : syracuseStep 8529239 = 12793859) B12793859
theorem B7005527 : Blo 1383511 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B3114377 : Blo 1383511 3114377 := bstep (se 2 (by rfl) ⟨1167891, by rfl⟩ : syracuseStep 3114377 = 2335783) B2335783
theorem B3327419 : Blo 1383511 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B2336249 : Blo 1383511 2336249 := bstep (se 2 (by rfl) ⟨876093, by rfl⟩ : syracuseStep 2336249 = 1752187) B1752187
theorem B3114503 : Blo 1383511 3114503 := bstep (se 1 (by rfl) ⟨2335877, by rfl⟩ : syracuseStep 3114503 = 4671755) B4671755
theorem B1558111 : Blo 1383511 1558111 := bstep (se 1 (by rfl) ⟨1168583, by rfl⟩ : syracuseStep 1558111 = 2337167) B2337167
theorem B2958943 : Blo 1383511 2958943 := bstep (se 1 (by rfl) ⟨2219207, by rfl⟩ : syracuseStep 2958943 = 4438415) B4438415
theorem B3114683 : Blo 1383511 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B2336519 : Blo 1383511 2336519 := bstep (se 1 (by rfl) ⟨1752389, by rfl⟩ : syracuseStep 2336519 = 3504779) B3504779
theorem B2369335 : Blo 1383511 2369335 := bstep (se 1 (by rfl) ⟨1777001, by rfl⟩ : syracuseStep 2369335 = 3554003) B3554003
theorem B3114809 : Blo 1383511 3114809 := bstep (se 2 (by rfl) ⟨1168053, by rfl⟩ : syracuseStep 3114809 = 2336107) B2336107
theorem B5916503 : Blo 1383511 5916503 := bstep (se 1 (by rfl) ⟨4437377, by rfl⟩ : syracuseStep 5916503 = 8874755) B8874755
theorem B4990825 : Blo 1383511 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B6653933 : Blo 1383511 6653933 := bstep (se 3 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 6653933 = 2495225) B2495225
theorem B7006337 : Blo 1383511 7006337 := bstep (se 2 (by rfl) ⟨2627376, by rfl⟩ : syracuseStep 7006337 = 5254753) B5254753
theorem B7481609 : Blo 1383511 7481609 := bstep (se 2 (by rfl) ⟨2805603, by rfl⟩ : syracuseStep 7481609 = 5611207) B5611207
theorem B3328265 : Blo 1383511 3328265 := bstep (se 2 (by rfl) ⟨1248099, by rfl⟩ : syracuseStep 3328265 = 2496199) B2496199
theorem B14969231 : Blo 1383511 14969231 := bstep (se 1 (by rfl) ⟨11226923, by rfl⟩ : syracuseStep 14969231 = 22453847) B22453847
theorem B3115439 : Blo 1383511 3115439 := bstep (se 1 (by rfl) ⟨2336579, by rfl⟩ : syracuseStep 3115439 = 4673159) B4673159
theorem B3115475 : Blo 1383511 3115475 := bstep (se 1 (by rfl) ⟨2336606, by rfl⟩ : syracuseStep 3115475 = 4673213) B4673213
theorem B11233765 : Blo 1383511 11233765 := bstep (se 4 (by rfl) ⟨1053165, by rfl⟩ : syracuseStep 11233765 = 2106331) B2106331
theorem B2337275 : Blo 1383511 2337275 := bstep (se 1 (by rfl) ⟨1752956, by rfl⟩ : syracuseStep 2337275 = 3505913) B3505913
theorem B3115583 : Blo 1383511 3115583 := bstep (se 1 (by rfl) ⟨2336687, by rfl⟩ : syracuseStep 3115583 = 4673375) B4673375
theorem B4672079 : Blo 1383511 4672079 := bstep (se 1 (by rfl) ⟨3504059, by rfl⟩ : syracuseStep 4672079 = 7008119) B7008119
theorem B7490171 : Blo 1383511 7490171 := bstep (se 1 (by rfl) ⟨5617628, by rfl⟩ : syracuseStep 7490171 = 11235257) B11235257
theorem B3115691 : Blo 1383511 3115691 := bstep (se 1 (by rfl) ⟨2336768, by rfl⟩ : syracuseStep 3115691 = 4673537) B4673537
theorem B2075471 : Blo 1383511 2075471 := bstep (se 1 (by rfl) ⟨1556603, by rfl⟩ : syracuseStep 2075471 = 3113207) B3113207
theorem B3156815 : Blo 1383511 3156815 := bstep (se 1 (by rfl) ⟨2367611, by rfl⟩ : syracuseStep 3156815 = 4735223) B4735223
theorem B63974261 : Blo 1383511 63974261 := bstep (se 5 (by rfl) ⟨2998793, by rfl⟩ : syracuseStep 63974261 = 5997587) B5997587
theorem B7007147 : Blo 1383511 7007147 := bstep (se 1 (by rfl) ⟨5255360, by rfl⟩ : syracuseStep 7007147 = 10510721) B10510721
theorem B2337707 : Blo 1383511 2337707 := bstep (se 1 (by rfl) ⟨1753280, by rfl⟩ : syracuseStep 2337707 = 3506561) B3506561
theorem B2493431 : Blo 1383511 2493431 := bstep (se 1 (by rfl) ⟨1870073, by rfl⟩ : syracuseStep 2493431 = 3740147) B3740147
theorem B5254267 : Blo 1383511 5254267 := bstep (se 1 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 5254267 = 7881401) B7881401
theorem B3116231 : Blo 1383511 3116231 := bstep (se 1 (by rfl) ⟨2337173, by rfl⟩ : syracuseStep 3116231 = 4674347) B4674347
theorem B2075867 : Blo 1383511 2075867 := bstep (se 1 (by rfl) ⟨1556900, by rfl⟩ : syracuseStep 2075867 = 3113801) B3113801
theorem B3116411 : Blo 1383511 3116411 := bstep (se 1 (by rfl) ⟨2337308, by rfl⟩ : syracuseStep 3116411 = 4674617) B4674617
theorem B2076041 : Blo 1383511 2076041 := bstep (se 2 (by rfl) ⟨778515, by rfl⟩ : syracuseStep 2076041 = 1557031) B1557031
theorem B11832763 : Blo 1383511 11832763 := bstep (se 1 (by rfl) ⟨8874572, by rfl⟩ : syracuseStep 11832763 = 17749145) B17749145
theorem B3116537 : Blo 1383511 3116537 := bstep (se 2 (by rfl) ⟨1168701, by rfl⟩ : syracuseStep 3116537 = 2337403) B2337403
theorem B6655547 : Blo 1383511 6655547 := bstep (se 1 (by rfl) ⟨4991660, by rfl⟩ : syracuseStep 6655547 = 9983321) B9983321
theorem B1478207 : Blo 1383511 1478207 := bstep (se 1 (by rfl) ⟨1108655, by rfl⟩ : syracuseStep 1478207 = 2217311) B2217311
theorem B5254739 : Blo 1383511 5254739 := bstep (se 1 (by rfl) ⟨3941054, by rfl⟩ : syracuseStep 5254739 = 7882109) B7882109
theorem B3116627 : Blo 1383511 3116627 := bstep (se 1 (by rfl) ⟨2337470, by rfl⟩ : syracuseStep 3116627 = 4674941) B4674941
theorem B113684087 : Blo 1383511 113684087 := bstep (se 1 (by rfl) ⟨85263065, by rfl⟩ : syracuseStep 113684087 = 170526131) B170526131
theorem B8867501 : Blo 1383511 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B7884499 : Blo 1383511 7884499 := bstep (se 1 (by rfl) ⟨5913374, by rfl⟩ : syracuseStep 7884499 = 11826749) B11826749
theorem B2076395 : Blo 1383511 2076395 := bstep (se 1 (by rfl) ⟨1557296, by rfl⟩ : syracuseStep 2076395 = 3114593) B3114593
theorem B3116807 : Blo 1383511 3116807 := bstep (se 1 (by rfl) ⟨2337605, by rfl⟩ : syracuseStep 3116807 = 4675211) B4675211
theorem B4673321 : Blo 1383511 4673321 := bstep (se 2 (by rfl) ⟨1752495, by rfl⟩ : syracuseStep 4673321 = 3504991) B3504991
theorem B2076623 : Blo 1383511 2076623 := bstep (se 1 (by rfl) ⟨1557467, by rfl⟩ : syracuseStep 2076623 = 3114935) B3114935
theorem B7008281 : Blo 1383511 7008281 := bstep (se 2 (by rfl) ⟨2628105, by rfl⟩ : syracuseStep 7008281 = 5256211) B5256211
theorem B11989081 : Blo 1383511 11989081 := bstep (se 2 (by rfl) ⟨4495905, by rfl⟩ : syracuseStep 11989081 = 8991811) B8991811
theorem B9474251 : Blo 1383511 9474251 := bstep (se 1 (by rfl) ⟨7105688, by rfl⟩ : syracuseStep 9474251 = 14211377) B14211377
theorem B2077019 : Blo 1383511 2077019 := bstep (se 1 (by rfl) ⟨1557764, by rfl⟩ : syracuseStep 2077019 = 3115529) B3115529
theorem B3502511 : Blo 1383511 3502511 := bstep (se 1 (by rfl) ⟨2626883, by rfl⟩ : syracuseStep 3502511 = 5253767) B5253767
theorem B6656431 : Blo 1383511 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B3502561 : Blo 1383511 3502561 := bstep (se 2 (by rfl) ⟨1313460, by rfl⟩ : syracuseStep 3502561 = 2626921) B2626921
theorem B2077247 : Blo 1383511 2077247 := bstep (se 1 (by rfl) ⟨1557935, by rfl⟩ : syracuseStep 2077247 = 3115871) B3115871
theorem B2806343 : Blo 1383511 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B6648473 : Blo 1383511 6648473 := bstep (se 2 (by rfl) ⟨2493177, by rfl⟩ : syracuseStep 6648473 = 4986355) B4986355
theorem B11981465 : Blo 1383511 11981465 := bstep (se 2 (by rfl) ⟨4493049, by rfl⟩ : syracuseStep 11981465 = 8986099) B8986099
theorem B2077367 : Blo 1383511 2077367 := bstep (se 1 (by rfl) ⟨1558025, by rfl⟩ : syracuseStep 2077367 = 3116051) B3116051
theorem B11219755 : Blo 1383511 11219755 := bstep (se 1 (by rfl) ⟨8414816, by rfl⟩ : syracuseStep 11219755 = 16829633) B16829633
theorem B11825999 : Blo 1383511 11825999 := bstep (se 1 (by rfl) ⟨8869499, by rfl⟩ : syracuseStep 11825999 = 17738999) B17738999
theorem B2077595 : Blo 1383511 2077595 := bstep (se 1 (by rfl) ⟨1558196, by rfl⟩ : syracuseStep 2077595 = 3116393) B3116393
theorem B10663001 : Blo 1383511 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B10515581 : Blo 1383511 10515581 := bstep (se 3 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 10515581 = 3943343) B3943343
theorem B23672087 : Blo 1383511 23672087 := bstep (se 1 (by rfl) ⟨17754065, by rfl⟩ : syracuseStep 23672087 = 35508131) B35508131
theorem B2077991 : Blo 1383511 2077991 := bstep (se 1 (by rfl) ⟨1558493, by rfl⟩ : syracuseStep 2077991 = 3116987) B3116987
theorem B3552607 : Blo 1383511 3552607 := bstep (se 1 (by rfl) ⟨2664455, by rfl⟩ : syracuseStep 3552607 = 5328911) B5328911
theorem B3503483 : Blo 1383511 3503483 := bstep (se 1 (by rfl) ⟨2627612, by rfl⟩ : syracuseStep 3503483 = 5255225) B5255225
theorem B2078075 : Blo 1383511 2078075 := bstep (se 1 (by rfl) ⟨1558556, by rfl⟩ : syracuseStep 2078075 = 3117113) B3117113
theorem B35468765 : Blo 1383511 35468765 := bstep (se 3 (by rfl) ⟨6650393, by rfl⟩ : syracuseStep 35468765 = 13300787) B13300787
theorem B2078201 : Blo 1383511 2078201 := bstep (se 2 (by rfl) ⟨779325, by rfl⟩ : syracuseStep 2078201 = 1558651) B1558651
theorem B59864615 : Blo 1383511 59864615 := bstep (se 1 (by rfl) ⟨44898461, by rfl⟩ : syracuseStep 59864615 = 89796923) B89796923
theorem B3741497 : Blo 1383511 3741497 := bstep (se 2 (by rfl) ⟨1403061, by rfl⟩ : syracuseStep 3741497 = 2806123) B2806123
theorem B2217785 : Blo 1383511 2217785 := bstep (se 2 (by rfl) ⟨831669, by rfl⟩ : syracuseStep 2217785 = 1663339) B1663339
theorem B4675535 : Blo 1383511 4675535 := bstep (se 1 (by rfl) ⟨3506651, by rfl⟩ : syracuseStep 4675535 = 7013303) B7013303
theorem B115308685 : Blo 1383511 115308685 := bstep (se 3 (by rfl) ⟨21620378, by rfl⟩ : syracuseStep 115308685 = 43240757) B43240757
theorem B26990873 : Blo 1383511 26990873 := bstep (se 2 (by rfl) ⟨10121577, by rfl⟩ : syracuseStep 26990873 = 20243155) B20243155
theorem B3324343 : Blo 1383511 3324343 := bstep (se 1 (by rfl) ⟨2493257, by rfl⟩ : syracuseStep 3324343 = 4986515) B4986515
theorem B9468343 : Blo 1383511 9468343 := bstep (se 1 (by rfl) ⟨7101257, by rfl⟩ : syracuseStep 9468343 = 14202515) B14202515
theorem B5257655 : Blo 1383511 5257655 := bstep (se 1 (by rfl) ⟨3943241, by rfl⟩ : syracuseStep 5257655 = 7886483) B7886483
theorem B2398943 : Blo 1383511 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B17750785 : Blo 1383511 17750785 := bstep (se 2 (by rfl) ⟨6656544, by rfl⟩ : syracuseStep 17750785 = 13313089) B13313089
theorem B1751863 : Blo 1383511 1751863 := bstep (se 1 (by rfl) ⟨1313897, by rfl⟩ : syracuseStep 1751863 = 2627795) B2627795
theorem B7011197 : Blo 1383511 7011197 := bstep (se 3 (by rfl) ⟨1314599, by rfl⟩ : syracuseStep 7011197 = 2629199) B2629199
theorem B5258155 : Blo 1383511 5258155 := bstep (se 1 (by rfl) ⟨3943616, by rfl⟩ : syracuseStep 5258155 = 7887233) B7887233
theorem B29948915 : Blo 1383511 29948915 := bstep (se 1 (by rfl) ⟨22461686, by rfl⟩ : syracuseStep 29948915 = 44923373) B44923373
theorem B3505295 : Blo 1383511 3505295 := bstep (se 1 (by rfl) ⟨2628971, by rfl⟩ : syracuseStep 3505295 = 5257943) B5257943
theorem B11828389 : Blo 1383511 11828389 := bstep (se 4 (by rfl) ⟨1108911, by rfl⟩ : syracuseStep 11828389 = 2217823) B2217823
theorem B5258429 : Blo 1383511 5258429 := bstep (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) B1971911
theorem B1752283 : Blo 1383511 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B5258459 : Blo 1383511 5258459 := bstep (se 1 (by rfl) ⟨3943844, by rfl⟩ : syracuseStep 5258459 = 7887689) B7887689
theorem B1383711 : Blo 1383511 1383711 := bstep (se 1 (by rfl) ⟨1037783, by rfl⟩ : syracuseStep 1383711 = 2075567) B2075567
theorem B1383771 : Blo 1383511 1383771 := bstep (se 1 (by rfl) ⟨1037828, by rfl⟩ : syracuseStep 1383771 = 2075657) B2075657
theorem B1383791 : Blo 1383511 1383791 := bstep (se 1 (by rfl) ⟨1037843, by rfl⟩ : syracuseStep 1383791 = 2075687) B2075687
theorem B1383847 : Blo 1383511 1383847 := bstep (se 1 (by rfl) ⟨1037885, by rfl⟩ : syracuseStep 1383847 = 2075771) B2075771
theorem B5914043 : Blo 1383511 5914043 := bstep (se 1 (by rfl) ⟨4435532, by rfl⟩ : syracuseStep 5914043 = 8871065) B8871065
theorem B1383931 : Blo 1383511 1383931 := bstep (se 1 (by rfl) ⟨1037948, by rfl⟩ : syracuseStep 1383931 = 2075897) B2075897
theorem B1498619 : Blo 1383511 1498619 := bstep (se 1 (by rfl) ⟨1123964, by rfl⟩ : syracuseStep 1498619 = 2247929) B2247929
theorem B5914127 : Blo 1383511 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B1383999 : Blo 1383511 1383999 := bstep (se 1 (by rfl) ⟨1037999, by rfl⟩ : syracuseStep 1383999 = 2075999) B2075999
theorem B1384007 : Blo 1383511 1384007 := bstep (se 1 (by rfl) ⟨1038005, by rfl⟩ : syracuseStep 1384007 = 2076011) B2076011
theorem B19955281 : Blo 1383511 19955281 := bstep (se 2 (by rfl) ⟨7483230, by rfl⟩ : syracuseStep 19955281 = 14966461) B14966461
theorem B15760979 : Blo 1383511 15760979 := bstep (se 1 (by rfl) ⟨11820734, by rfl⟩ : syracuseStep 15760979 = 23641469) B23641469
theorem B2956961 : Blo 1383511 2956961 := bstep (se 2 (by rfl) ⟨1108860, by rfl⟩ : syracuseStep 2956961 = 2217721) B2217721
theorem B1384159 : Blo 1383511 1384159 := bstep (se 1 (by rfl) ⟨1038119, by rfl⟩ : syracuseStep 1384159 = 2076239) B2076239
theorem B13483817 : Blo 1383511 13483817 := bstep (se 2 (by rfl) ⟨5056431, by rfl⟩ : syracuseStep 13483817 = 10112863) B10112863
theorem B1384239 : Blo 1383511 1384239 := bstep (se 1 (by rfl) ⟨1038179, by rfl⟩ : syracuseStep 1384239 = 2076359) B2076359
theorem B7012169 : Blo 1383511 7012169 := bstep (se 2 (by rfl) ⟨2629563, by rfl⟩ : syracuseStep 7012169 = 5259127) B5259127
theorem B1384347 : Blo 1383511 1384347 := bstep (se 1 (by rfl) ⟨1038260, by rfl⟩ : syracuseStep 1384347 = 2076521) B2076521
theorem B1384399 : Blo 1383511 1384399 := bstep (se 1 (by rfl) ⟨1038299, by rfl⟩ : syracuseStep 1384399 = 2076599) B2076599
theorem B1556455 : Blo 1383511 1556455 := bstep (se 1 (by rfl) ⟨1167341, by rfl⟩ : syracuseStep 1556455 = 2334683) B2334683
theorem B1384423 : Blo 1383511 1384423 := bstep (se 1 (by rfl) ⟨1038317, by rfl⟩ : syracuseStep 1384423 = 2076635) B2076635
theorem B1384679 : Blo 1383511 1384679 := bstep (se 1 (by rfl) ⟨1038509, by rfl⟩ : syracuseStep 1384679 = 2077019) B2077019
theorem B2335007 : Blo 1383511 2335007 := bstep (se 1 (by rfl) ⟨1751255, by rfl⟩ : syracuseStep 2335007 = 3502511) B3502511
theorem B1384831 : Blo 1383511 1384831 := bstep (se 1 (by rfl) ⟨1038623, by rfl⟩ : syracuseStep 1384831 = 2077247) B2077247
theorem B4432315 : Blo 1383511 4432315 := bstep (se 1 (by rfl) ⟨3324236, by rfl⟩ : syracuseStep 4432315 = 6648473) B6648473
theorem B7987643 : Blo 1383511 7987643 := bstep (se 1 (by rfl) ⟨5990732, by rfl⟩ : syracuseStep 7987643 = 11981465) B11981465
theorem B3113423 : Blo 1383511 3113423 := bstep (se 1 (by rfl) ⟨2335067, by rfl⟩ : syracuseStep 3113423 = 4670135) B4670135
theorem B1384911 : Blo 1383511 1384911 := bstep (se 1 (by rfl) ⟨1038683, by rfl⟩ : syracuseStep 1384911 = 2077367) B2077367
theorem B28426763 : Blo 1383511 28426763 := bstep (se 1 (by rfl) ⟨21320072, by rfl⟩ : syracuseStep 28426763 = 42640145) B42640145
theorem B25264669 : Blo 1383511 25264669 := bstep (se 3 (by rfl) ⟨4737125, by rfl⟩ : syracuseStep 25264669 = 9474251) B9474251
theorem B4432457 : Blo 1383511 4432457 := bstep (se 2 (by rfl) ⟨1662171, by rfl⟩ : syracuseStep 4432457 = 3324343) B3324343
theorem B12624457 : Blo 1383511 12624457 := bstep (se 2 (by rfl) ⟨4734171, by rfl⟩ : syracuseStep 12624457 = 9468343) B9468343
theorem B1385063 : Blo 1383511 1385063 := bstep (se 1 (by rfl) ⟨1038797, by rfl⟩ : syracuseStep 1385063 = 2077595) B2077595
theorem B4670081 : Blo 1383511 4670081 := bstep (se 2 (by rfl) ⟨1751280, by rfl⟩ : syracuseStep 4670081 = 3502561) B3502561
theorem B119751371 : Blo 1383511 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B1385327 : Blo 1383511 1385327 := bstep (se 1 (by rfl) ⟨1038995, by rfl⟩ : syracuseStep 1385327 = 2077991) B2077991
theorem B5686159 : Blo 1383511 5686159 := bstep (se 1 (by rfl) ⟨4264619, by rfl⟩ : syracuseStep 5686159 = 8529239) B8529239
theorem B4670351 : Blo 1383511 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B2335655 : Blo 1383511 2335655 := bstep (se 1 (by rfl) ⟨1751741, by rfl⟩ : syracuseStep 2335655 = 3503483) B3503483
theorem B1385383 : Blo 1383511 1385383 := bstep (se 1 (by rfl) ⟨1039037, by rfl⟩ : syracuseStep 1385383 = 2078075) B2078075
theorem B1557499 : Blo 1383511 1557499 := bstep (se 1 (by rfl) ⟨1168124, by rfl⟩ : syracuseStep 1557499 = 2336249) B2336249
theorem B1385467 : Blo 1383511 1385467 := bstep (se 1 (by rfl) ⟨1039100, by rfl⟩ : syracuseStep 1385467 = 2078201) B2078201
theorem B23667713 : Blo 1383511 23667713 := bstep (se 2 (by rfl) ⟨8875392, by rfl⟩ : syracuseStep 23667713 = 17750785) B17750785
theorem B14959673 : Blo 1383511 14959673 := bstep (se 2 (by rfl) ⟨5609877, by rfl⟩ : syracuseStep 14959673 = 11219755) B11219755
theorem B2335817 : Blo 1383511 2335817 := bstep (se 2 (by rfl) ⟨875931, by rfl⟩ : syracuseStep 2335817 = 1751863) B1751863
theorem B3114089 : Blo 1383511 3114089 := bstep (se 2 (by rfl) ⟨1167783, by rfl⟩ : syracuseStep 3114089 = 2335567) B2335567
theorem B1557679 : Blo 1383511 1557679 := bstep (se 1 (by rfl) ⟨1168259, by rfl⟩ : syracuseStep 1557679 = 2336519) B2336519
theorem B4670891 : Blo 1383511 4670891 := bstep (se 1 (by rfl) ⟨3503168, by rfl⟩ : syracuseStep 4670891 = 7006337) B7006337
theorem B7005689 : Blo 1383511 7005689 := bstep (se 2 (by rfl) ⟨2627133, by rfl⟩ : syracuseStep 7005689 = 5254267) B5254267
theorem B3941885 : Blo 1383511 3941885 := bstep (se 3 (by rfl) ⟨739103, by rfl⟩ : syracuseStep 3941885 = 1478207) B1478207
theorem B15771185 : Blo 1383511 15771185 := bstep (se 2 (by rfl) ⟨5914194, by rfl⟩ : syracuseStep 15771185 = 11828389) B11828389
theorem B9979487 : Blo 1383511 9979487 := bstep (se 1 (by rfl) ⟨7484615, by rfl⟩ : syracuseStep 9979487 = 14969231) B14969231
theorem B2336377 : Blo 1383511 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B19973789 : Blo 1383511 19973789 := bstep (se 3 (by rfl) ⟨3745085, by rfl⟩ : syracuseStep 19973789 = 7490171) B7490171
theorem B1558183 : Blo 1383511 1558183 := bstep (se 1 (by rfl) ⟨1168637, by rfl⟩ : syracuseStep 1558183 = 2337275) B2337275
theorem B3114719 : Blo 1383511 3114719 := bstep (se 1 (by rfl) ⟨2336039, by rfl⟩ : syracuseStep 3114719 = 4672079) B4672079
theorem B4736809 : Blo 1383511 4736809 := bstep (se 2 (by rfl) ⟨1776303, by rfl⟩ : syracuseStep 4736809 = 3552607) B3552607
theorem B1599295 : Blo 1383511 1599295 := bstep (se 1 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 1599295 = 2398943) B2398943
theorem B42649507 : Blo 1383511 42649507 := bstep (se 1 (by rfl) ⟨31987130, by rfl⟩ : syracuseStep 42649507 = 63974261) B63974261
theorem B4671431 : Blo 1383511 4671431 := bstep (se 1 (by rfl) ⟨3503573, by rfl⟩ : syracuseStep 4671431 = 7007147) B7007147
theorem B1558471 : Blo 1383511 1558471 := bstep (se 1 (by rfl) ⟨1168853, by rfl⟩ : syracuseStep 1558471 = 2337707) B2337707
theorem B19965943 : Blo 1383511 19965943 := bstep (se 1 (by rfl) ⟨14974457, by rfl⟩ : syracuseStep 19965943 = 29948915) B29948915
theorem B2336863 : Blo 1383511 2336863 := bstep (se 1 (by rfl) ⟨1752647, by rfl⟩ : syracuseStep 2336863 = 3505295) B3505295
theorem B10512665 : Blo 1383511 10512665 := bstep (se 2 (by rfl) ⟨3942249, by rfl⟩ : syracuseStep 10512665 = 7884499) B7884499
theorem B3942695 : Blo 1383511 3942695 := bstep (se 1 (by rfl) ⟨2957021, by rfl⟩ : syracuseStep 3942695 = 5914043) B5914043
theorem B3942751 : Blo 1383511 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B6654433 : Blo 1383511 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B8989211 : Blo 1383511 8989211 := bstep (se 1 (by rfl) ⟨6741908, by rfl⟩ : syracuseStep 8989211 = 13483817) B13483817
theorem B3115547 : Blo 1383511 3115547 := bstep (se 1 (by rfl) ⟨2336660, by rfl⟩ : syracuseStep 3115547 = 4673321) B4673321
theorem B2075273 : Blo 1383511 2075273 := bstep (se 2 (by rfl) ⟨778227, by rfl⟩ : syracuseStep 2075273 = 1556455) B1556455
theorem B4672187 : Blo 1383511 4672187 := bstep (se 1 (by rfl) ⟨3504140, by rfl⟩ : syracuseStep 4672187 = 7008281) B7008281
theorem B15985441 : Blo 1383511 15985441 := bstep (se 2 (by rfl) ⟨5994540, by rfl⟩ : syracuseStep 15985441 = 11989081) B11989081
theorem B2075447 : Blo 1383511 2075447 := bstep (se 1 (by rfl) ⟨1556585, by rfl⟩ : syracuseStep 2075447 = 3113171) B3113171
theorem B2075483 : Blo 1383511 2075483 := bstep (se 1 (by rfl) ⟨1556612, by rfl⟩ : syracuseStep 2075483 = 3113225) B3113225
theorem B13314935 : Blo 1383511 13314935 := bstep (se 1 (by rfl) ⟨9986201, by rfl⟩ : syracuseStep 13314935 = 19972403) B19972403
theorem B11824015 : Blo 1383511 11824015 := bstep (se 1 (by rfl) ⟨8868011, by rfl⟩ : syracuseStep 11824015 = 17736023) B17736023
theorem B2075627 : Blo 1383511 2075627 := bstep (se 1 (by rfl) ⟨1556720, by rfl⟩ : syracuseStep 2075627 = 3113441) B3113441
theorem B1870895 : Blo 1383511 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B2075831 : Blo 1383511 2075831 := bstep (se 1 (by rfl) ⟨1556873, by rfl⟩ : syracuseStep 2075831 = 3113747) B3113747
theorem B7883999 : Blo 1383511 7883999 := bstep (se 1 (by rfl) ⟨5912999, by rfl⟩ : syracuseStep 7883999 = 11825999) B11825999
theorem B8875241 : Blo 1383511 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B14978353 : Blo 1383511 14978353 := bstep (se 2 (by rfl) ⟨5616882, by rfl⟩ : syracuseStep 14978353 = 11233765) B11233765
theorem B2076071 : Blo 1383511 2076071 := bstep (se 1 (by rfl) ⟨1557053, by rfl⟩ : syracuseStep 2076071 = 3114107) B3114107
theorem B2076155 : Blo 1383511 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B43232777 : Blo 1383511 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B15781391 : Blo 1383511 15781391 := bstep (se 1 (by rfl) ⟨11836043, by rfl⟩ : syracuseStep 15781391 = 23672087) B23672087
theorem B2076251 : Blo 1383511 2076251 := bstep (se 1 (by rfl) ⟨1557188, by rfl⟩ : syracuseStep 2076251 = 3114377) B3114377
theorem B23645843 : Blo 1383511 23645843 := bstep (se 1 (by rfl) ⟨17734382, by rfl⟩ : syracuseStep 23645843 = 35468765) B35468765
theorem B2076335 : Blo 1383511 2076335 := bstep (se 1 (by rfl) ⟨1557251, by rfl⟩ : syracuseStep 2076335 = 3114503) B3114503
theorem B42602213 : Blo 1383511 42602213 := bstep (se 4 (by rfl) ⟨3993957, by rfl⟩ : syracuseStep 42602213 = 7987915) B7987915
theorem B2076455 : Blo 1383511 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B2494331 : Blo 1383511 2494331 := bstep (se 1 (by rfl) ⟨1870748, by rfl⟩ : syracuseStep 2494331 = 3741497) B3741497
theorem B2076539 : Blo 1383511 2076539 := bstep (se 1 (by rfl) ⟨1557404, by rfl⟩ : syracuseStep 2076539 = 3114809) B3114809
theorem B3944335 : Blo 1383511 3944335 := bstep (se 1 (by rfl) ⟨2958251, by rfl⟩ : syracuseStep 3944335 = 5916503) B5916503
theorem B3117023 : Blo 1383511 3117023 := bstep (se 1 (by rfl) ⟨2337767, by rfl⟩ : syracuseStep 3117023 = 4675535) B4675535
theorem B4435955 : Blo 1383511 4435955 := bstep (se 1 (by rfl) ⟨3326966, by rfl⟩ : syracuseStep 4435955 = 6653933) B6653933
theorem B17993915 : Blo 1383511 17993915 := bstep (se 1 (by rfl) ⟨13495436, by rfl⟩ : syracuseStep 17993915 = 26990873) B26990873
theorem B2076959 : Blo 1383511 2076959 := bstep (se 1 (by rfl) ⟨1557719, by rfl⟩ : syracuseStep 2076959 = 3115439) B3115439
theorem B2076983 : Blo 1383511 2076983 := bstep (se 1 (by rfl) ⟨1557737, by rfl⟩ : syracuseStep 2076983 = 3115475) B3115475
theorem B2077055 : Blo 1383511 2077055 := bstep (se 1 (by rfl) ⟨1557791, by rfl⟩ : syracuseStep 2077055 = 3115583) B3115583
theorem B2077127 : Blo 1383511 2077127 := bstep (se 1 (by rfl) ⟨1557845, by rfl⟩ : syracuseStep 2077127 = 3115691) B3115691
theorem B4674131 : Blo 1383511 4674131 := bstep (se 1 (by rfl) ⟨3505598, by rfl⟩ : syracuseStep 4674131 = 7011197) B7011197
theorem B2077481 : Blo 1383511 2077481 := bstep (se 2 (by rfl) ⟨779055, by rfl⟩ : syracuseStep 2077481 = 1558111) B1558111
theorem B3945257 : Blo 1383511 3945257 := bstep (se 2 (by rfl) ⟨1479471, by rfl⟩ : syracuseStep 3945257 = 2958943) B2958943
theorem B2077487 : Blo 1383511 2077487 := bstep (se 1 (by rfl) ⟨1558115, by rfl⟩ : syracuseStep 2077487 = 3116231) B3116231
theorem B8418173 : Blo 1383511 8418173 := bstep (se 3 (by rfl) ⟨1578407, by rfl⟩ : syracuseStep 8418173 = 3156815) B3156815
theorem B2077607 : Blo 1383511 2077607 := bstep (se 1 (by rfl) ⟨1558205, by rfl⟩ : syracuseStep 2077607 = 3116411) B3116411
theorem B2077691 : Blo 1383511 2077691 := bstep (se 1 (by rfl) ⟨1558268, by rfl⟩ : syracuseStep 2077691 = 3116537) B3116537
theorem B4437031 : Blo 1383511 4437031 := bstep (se 1 (by rfl) ⟨3327773, by rfl⟩ : syracuseStep 4437031 = 6655547) B6655547
theorem B10507319 : Blo 1383511 10507319 := bstep (se 1 (by rfl) ⟨7880489, by rfl⟩ : syracuseStep 10507319 = 15760979) B15760979
theorem B3503159 : Blo 1383511 3503159 := bstep (se 1 (by rfl) ⟨2627369, by rfl⟩ : syracuseStep 3503159 = 5254739) B5254739
theorem B2077751 : Blo 1383511 2077751 := bstep (se 1 (by rfl) ⟨1558313, by rfl⟩ : syracuseStep 2077751 = 3116627) B3116627
theorem B3159113 : Blo 1383511 3159113 := bstep (se 2 (by rfl) ⟨1184667, by rfl⟩ : syracuseStep 3159113 = 2369335) B2369335
theorem B75789391 : Blo 1383511 75789391 := bstep (se 1 (by rfl) ⟨56842043, by rfl⟩ : syracuseStep 75789391 = 113684087) B113684087
theorem B1971307 : Blo 1383511 1971307 := bstep (se 1 (by rfl) ⟨1478480, by rfl⟩ : syracuseStep 1971307 = 2956961) B2956961
theorem B5911667 : Blo 1383511 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B2077871 : Blo 1383511 2077871 := bstep (se 1 (by rfl) ⟨1558403, by rfl⟩ : syracuseStep 2077871 = 3116807) B3116807
theorem B4674779 : Blo 1383511 4674779 := bstep (se 1 (by rfl) ⟨3506084, by rfl⟩ : syracuseStep 4674779 = 7012169) B7012169
theorem B31954439 : Blo 1383511 31954439 := bstep (se 1 (by rfl) ⟨23965829, by rfl⟩ : syracuseStep 31954439 = 47931659) B47931659
theorem B153744913 : Blo 1383511 153744913 := bstep (se 2 (by rfl) ⟨57654342, by rfl⟩ : syracuseStep 153744913 = 115308685) B115308685
theorem B2217593 : Blo 1383511 2217593 := bstep (se 2 (by rfl) ⟨831597, by rfl⟩ : syracuseStep 2217593 = 1663195) B1663195
theorem B2627255 : Blo 1383511 2627255 := bstep (se 1 (by rfl) ⟨1970441, by rfl⟩ : syracuseStep 2627255 = 3940883) B3940883
theorem B17733563 : Blo 1383511 17733563 := bstep (se 1 (by rfl) ⟨13300172, by rfl⟩ : syracuseStep 17733563 = 26600345) B26600345
theorem B7108667 : Blo 1383511 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B4675643 : Blo 1383511 4675643 := bstep (se 1 (by rfl) ⟨3506732, by rfl⟩ : syracuseStep 4675643 = 7013465) B7013465
theorem B7010387 : Blo 1383511 7010387 := bstep (se 1 (by rfl) ⟨5257790, by rfl⟩ : syracuseStep 7010387 = 10515581) B10515581
theorem B2218279 : Blo 1383511 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B4675913 : Blo 1383511 4675913 := bstep (se 2 (by rfl) ⟨1753467, by rfl⟩ : syracuseStep 4675913 = 3506935) B3506935
theorem B39909743 : Blo 1383511 39909743 := bstep (se 1 (by rfl) ⟨29932307, by rfl⟩ : syracuseStep 39909743 = 59864615) B59864615
theorem B7010873 : Blo 1383511 7010873 := bstep (se 2 (by rfl) ⟨2629077, by rfl⟩ : syracuseStep 7010873 = 5258155) B5258155
theorem B11819641 : Blo 1383511 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B3996317 : Blo 1383511 3996317 := bstep (se 3 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 3996317 = 1498619) B1498619
theorem B4987739 : Blo 1383511 4987739 := bstep (se 1 (by rfl) ⟨3740804, by rfl⟩ : syracuseStep 4987739 = 7481609) B7481609
theorem B2218843 : Blo 1383511 2218843 := bstep (se 1 (by rfl) ⟨1664132, by rfl⟩ : syracuseStep 2218843 = 3328265) B3328265
theorem B3505103 : Blo 1383511 3505103 := bstep (se 1 (by rfl) ⟨2628827, by rfl⟩ : syracuseStep 3505103 = 5257655) B5257655
theorem B1383647 : Blo 1383511 1383647 := bstep (se 1 (by rfl) ⟨1037735, by rfl⟩ : syracuseStep 1383647 = 2075471) B2075471
theorem B15777017 : Blo 1383511 15777017 := bstep (se 2 (by rfl) ⟨5916381, by rfl⟩ : syracuseStep 15777017 = 11832763) B11832763
theorem B1662287 : Blo 1383511 1662287 := bstep (se 1 (by rfl) ⟨1246715, by rfl⟩ : syracuseStep 1662287 = 2493431) B2493431
theorem B26607041 : Blo 1383511 26607041 := bstep (se 2 (by rfl) ⟨9977640, by rfl⟩ : syracuseStep 26607041 = 19955281) B19955281
theorem B3505619 : Blo 1383511 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B1383911 : Blo 1383511 1383911 := bstep (se 1 (by rfl) ⟨1037933, by rfl⟩ : syracuseStep 1383911 = 2075867) B2075867
theorem B3505639 : Blo 1383511 3505639 := bstep (se 1 (by rfl) ⟨2629229, by rfl⟩ : syracuseStep 3505639 = 5258459) B5258459
theorem B5914093 : Blo 1383511 5914093 := bstep (se 3 (by rfl) ⟨1108892, by rfl⟩ : syracuseStep 5914093 = 2217785) B2217785
theorem B1384027 : Blo 1383511 1384027 := bstep (se 1 (by rfl) ⟨1038020, by rfl⟩ : syracuseStep 1384027 = 2076041) B2076041
theorem B1384263 : Blo 1383511 1384263 := bstep (se 1 (by rfl) ⟨1038197, by rfl⟩ : syracuseStep 1384263 = 2076395) B2076395
theorem B1384415 : Blo 1383511 1384415 := bstep (se 1 (by rfl) ⟨1038311, by rfl⟩ : syracuseStep 1384415 = 2076623) B2076623
theorem B4989053 : Blo 1383511 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1556671 : Blo 1383511 1556671 := bstep (se 1 (by rfl) ⟨1167503, by rfl⟩ : syracuseStep 1556671 = 2335007) B2335007
theorem B1384639 : Blo 1383511 1384639 := bstep (se 1 (by rfl) ⟨1038479, by rfl⟩ : syracuseStep 1384639 = 2076959) B2076959
theorem B1384655 : Blo 1383511 1384655 := bstep (se 1 (by rfl) ⟨1038491, by rfl⟩ : syracuseStep 1384655 = 2076983) B2076983
theorem B1384703 : Blo 1383511 1384703 := bstep (se 1 (by rfl) ⟨1038527, by rfl⟩ : syracuseStep 1384703 = 2077055) B2077055
theorem B5325095 : Blo 1383511 5325095 := bstep (se 1 (by rfl) ⟨3993821, by rfl⟩ : syracuseStep 5325095 = 7987643) B7987643
theorem B1384751 : Blo 1383511 1384751 := bstep (se 1 (by rfl) ⟨1038563, by rfl⟩ : syracuseStep 1384751 = 2077127) B2077127
theorem B2957705 : Blo 1383511 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B3113387 : Blo 1383511 3113387 := bstep (se 1 (by rfl) ⟨2335040, by rfl⟩ : syracuseStep 3113387 = 4670081) B4670081
theorem B1384987 : Blo 1383511 1384987 := bstep (se 1 (by rfl) ⟨1038740, by rfl⟩ : syracuseStep 1384987 = 2077481) B2077481
theorem B2630171 : Blo 1383511 2630171 := bstep (se 1 (by rfl) ⟨1972628, by rfl⟩ : syracuseStep 2630171 = 3945257) B3945257
theorem B1384991 : Blo 1383511 1384991 := bstep (se 1 (by rfl) ⟨1038743, by rfl⟩ : syracuseStep 1384991 = 2077487) B2077487
theorem B3113567 : Blo 1383511 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B1557103 : Blo 1383511 1557103 := bstep (se 1 (by rfl) ⟨1167827, by rfl⟩ : syracuseStep 1557103 = 2335655) B2335655
theorem B1385071 : Blo 1383511 1385071 := bstep (se 1 (by rfl) ⟨1038803, by rfl⟩ : syracuseStep 1385071 = 2077607) B2077607
theorem B8872577 : Blo 1383511 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B1385127 : Blo 1383511 1385127 := bstep (se 1 (by rfl) ⟨1038845, by rfl⟩ : syracuseStep 1385127 = 2077691) B2077691
theorem B15778475 : Blo 1383511 15778475 := bstep (se 1 (by rfl) ⟨11833856, by rfl⟩ : syracuseStep 15778475 = 23667713) B23667713
theorem B7004879 : Blo 1383511 7004879 := bstep (se 1 (by rfl) ⟨5253659, by rfl⟩ : syracuseStep 7004879 = 10507319) B10507319
theorem B2335439 : Blo 1383511 2335439 := bstep (se 1 (by rfl) ⟨1751579, by rfl⟩ : syracuseStep 2335439 = 3503159) B3503159
theorem B33686225 : Blo 1383511 33686225 := bstep (se 2 (by rfl) ⟨12632334, by rfl⟩ : syracuseStep 33686225 = 25264669) B25264669
theorem B1385167 : Blo 1383511 1385167 := bstep (se 1 (by rfl) ⟨1038875, by rfl⟩ : syracuseStep 1385167 = 2077751) B2077751
theorem B1557211 : Blo 1383511 1557211 := bstep (se 1 (by rfl) ⟨1167908, by rfl⟩ : syracuseStep 1557211 = 2335817) B2335817
theorem B3941111 : Blo 1383511 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B1385247 : Blo 1383511 1385247 := bstep (se 1 (by rfl) ⟨1038935, by rfl⟩ : syracuseStep 1385247 = 2077871) B2077871
theorem B4432765 : Blo 1383511 4432765 := bstep (se 3 (by rfl) ⟨831143, by rfl⟩ : syracuseStep 4432765 = 1662287) B1662287
theorem B3113927 : Blo 1383511 3113927 := bstep (se 1 (by rfl) ⟨2335445, by rfl⟩ : syracuseStep 3113927 = 4670891) B4670891
theorem B4670459 : Blo 1383511 4670459 := bstep (se 1 (by rfl) ⟨3502844, by rfl⟩ : syracuseStep 4670459 = 7005689) B7005689
theorem B6652991 : Blo 1383511 6652991 := bstep (se 1 (by rfl) ⟨4989743, by rfl⟩ : syracuseStep 6652991 = 9979487) B9979487
theorem B2958457 : Blo 1383511 2958457 := bstep (se 2 (by rfl) ⟨1109421, by rfl⟩ : syracuseStep 2958457 = 2218843) B2218843
theorem B11822375 : Blo 1383511 11822375 := bstep (se 1 (by rfl) ⟨8866781, by rfl⟩ : syracuseStep 11822375 = 17733563) B17733563
theorem B3114287 : Blo 1383511 3114287 := bstep (se 1 (by rfl) ⟨2335715, by rfl⟩ : syracuseStep 3114287 = 4671431) B4671431
theorem B10511693 : Blo 1383511 10511693 := bstep (se 3 (by rfl) ⟨1970942, by rfl⟩ : syracuseStep 10511693 = 3941885) B3941885
theorem B5916041 : Blo 1383511 5916041 := bstep (se 2 (by rfl) ⟨2218515, by rfl⟩ : syracuseStep 5916041 = 4437031) B4437031
theorem B23971229 : Blo 1383511 23971229 := bstep (se 3 (by rfl) ⟨4494605, by rfl⟩ : syracuseStep 23971229 = 8989211) B8989211
theorem B85255685 : Blo 1383511 85255685 := bstep (se 4 (by rfl) ⟨7992720, by rfl⟩ : syracuseStep 85255685 = 15985441) B15985441
theorem B2664211 : Blo 1383511 2664211 := bstep (se 1 (by rfl) ⟨1998158, by rfl⟩ : syracuseStep 2664211 = 3996317) B3996317
theorem B3114791 : Blo 1383511 3114791 := bstep (se 1 (by rfl) ⟨2336093, by rfl⟩ : syracuseStep 3114791 = 4672187) B4672187
theorem B7006013 : Blo 1383511 7006013 := bstep (se 3 (by rfl) ⟨1313627, by rfl⟩ : syracuseStep 7006013 = 2627255) B2627255
theorem B2336735 : Blo 1383511 2336735 := bstep (se 1 (by rfl) ⟨1752551, by rfl⟩ : syracuseStep 2336735 = 3505103) B3505103
theorem B5916827 : Blo 1383511 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B3115169 : Blo 1383511 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B2957303 : Blo 1383511 2957303 := bstep (se 1 (by rfl) ⟨2217977, by rfl⟩ : syracuseStep 2957303 = 4435955) B4435955
theorem B17738027 : Blo 1383511 17738027 := bstep (se 1 (by rfl) ⟨13303520, by rfl⟩ : syracuseStep 17738027 = 26607041) B26607041
theorem B2337079 : Blo 1383511 2337079 := bstep (se 1 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 2337079 = 3505619) B3505619
theorem B22448461 : Blo 1383511 22448461 := bstep (se 3 (by rfl) ⟨4209086, by rfl⟩ : syracuseStep 22448461 = 8418173) B8418173
theorem B28821851 : Blo 1383511 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B10520927 : Blo 1383511 10520927 := bstep (se 1 (by rfl) ⟨7890695, by rfl⟩ : syracuseStep 10520927 = 15781391) B15781391
theorem B2132393 : Blo 1383511 2132393 := bstep (se 2 (by rfl) ⟨799647, by rfl⟩ : syracuseStep 2132393 = 1599295) B1599295
theorem B15763895 : Blo 1383511 15763895 := bstep (se 1 (by rfl) ⟨11822921, by rfl⟩ : syracuseStep 15763895 = 23645843) B23645843
theorem B11995943 : Blo 1383511 11995943 := bstep (se 1 (by rfl) ⟨8996957, by rfl⟩ : syracuseStep 11995943 = 17993915) B17993915
theorem B3115817 : Blo 1383511 3115817 := bstep (se 2 (by rfl) ⟨1168431, by rfl⟩ : syracuseStep 3115817 = 2336863) B2336863
theorem B2075615 : Blo 1383511 2075615 := bstep (se 1 (by rfl) ⟨1556711, by rfl⟩ : syracuseStep 2075615 = 3113423) B3113423
theorem B18951175 : Blo 1383511 18951175 := bstep (se 1 (by rfl) ⟨14213381, by rfl⟩ : syracuseStep 18951175 = 28426763) B28426763
theorem B3116087 : Blo 1383511 3116087 := bstep (se 1 (by rfl) ⟨2337065, by rfl⟩ : syracuseStep 3116087 = 4674131) B4674131
theorem B79834247 : Blo 1383511 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B10513637 : Blo 1383511 10513637 := bstep (se 4 (by rfl) ⟨985653, by rfl⟩ : syracuseStep 10513637 = 1971307) B1971307
theorem B5909753 : Blo 1383511 5909753 := bstep (se 2 (by rfl) ⟨2216157, by rfl⟩ : syracuseStep 5909753 = 4432315) B4432315
theorem B9973115 : Blo 1383511 9973115 := bstep (se 1 (by rfl) ⟨7479836, by rfl⟩ : syracuseStep 9973115 = 14959673) B14959673
theorem B2076059 : Blo 1383511 2076059 := bstep (se 1 (by rfl) ⟨1557044, by rfl⟩ : syracuseStep 2076059 = 3114089) B3114089
theorem B33697205 : Blo 1383511 33697205 := bstep (se 5 (by rfl) ⟨1579556, by rfl⟩ : syracuseStep 33697205 = 3159113) B3159113
theorem B3116519 : Blo 1383511 3116519 := bstep (se 1 (by rfl) ⟨2337389, by rfl⟩ : syracuseStep 3116519 = 4674779) B4674779
theorem B21302959 : Blo 1383511 21302959 := bstep (se 1 (by rfl) ⟨15977219, by rfl⟩ : syracuseStep 21302959 = 31954439) B31954439
theorem B10514123 : Blo 1383511 10514123 := bstep (se 1 (by rfl) ⟨7885592, by rfl⟩ : syracuseStep 10514123 = 15771185) B15771185
theorem B1478395 : Blo 1383511 1478395 := bstep (se 1 (by rfl) ⟨1108796, by rfl⟩ : syracuseStep 1478395 = 2217593) B2217593
theorem B13315859 : Blo 1383511 13315859 := bstep (se 1 (by rfl) ⟨9986894, by rfl⟩ : syracuseStep 13315859 = 19973789) B19973789
theorem B2076479 : Blo 1383511 2076479 := bstep (se 1 (by rfl) ⟨1557359, by rfl⟩ : syracuseStep 2076479 = 3114719) B3114719
theorem B7581545 : Blo 1383511 7581545 := bstep (se 2 (by rfl) ⟨2843079, by rfl⟩ : syracuseStep 7581545 = 5686159) B5686159
theorem B15765353 : Blo 1383511 15765353 := bstep (se 2 (by rfl) ⟨5912007, by rfl⟩ : syracuseStep 15765353 = 11824015) B11824015
theorem B2076665 : Blo 1383511 2076665 := bstep (se 2 (by rfl) ⟨778749, by rfl⟩ : syracuseStep 2076665 = 1557499) B1557499
theorem B4739111 : Blo 1383511 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B3117095 : Blo 1383511 3117095 := bstep (se 1 (by rfl) ⟨2337821, by rfl⟩ : syracuseStep 3117095 = 4675643) B4675643
theorem B4673591 : Blo 1383511 4673591 := bstep (se 1 (by rfl) ⟨3505193, by rfl⟩ : syracuseStep 4673591 = 7010387) B7010387
theorem B101052521 : Blo 1383511 101052521 := bstep (se 2 (by rfl) ⟨37894695, by rfl⟩ : syracuseStep 101052521 = 75789391) B75789391
theorem B7008443 : Blo 1383511 7008443 := bstep (se 1 (by rfl) ⟨5256332, by rfl⟩ : syracuseStep 7008443 = 10512665) B10512665
theorem B3117275 : Blo 1383511 3117275 := bstep (se 1 (by rfl) ⟨2337956, by rfl⟩ : syracuseStep 3117275 = 4675913) B4675913
theorem B2076905 : Blo 1383511 2076905 := bstep (se 2 (by rfl) ⟨778839, by rfl⟩ : syracuseStep 2076905 = 1557679) B1557679
theorem B2077031 : Blo 1383511 2077031 := bstep (se 1 (by rfl) ⟨1557773, by rfl⟩ : syracuseStep 2077031 = 3115547) B3115547
theorem B4673915 : Blo 1383511 4673915 := bstep (se 1 (by rfl) ⟨3505436, by rfl⟩ : syracuseStep 4673915 = 7010873) B7010873
theorem B8876623 : Blo 1383511 8876623 := bstep (se 1 (by rfl) ⟨6657467, by rfl⟩ : syracuseStep 8876623 = 13314935) B13314935
theorem B4674185 : Blo 1383511 4674185 := bstep (se 2 (by rfl) ⟨1752819, by rfl⟩ : syracuseStep 4674185 = 3505639) B3505639
theorem B7885457 : Blo 1383511 7885457 := bstep (se 2 (by rfl) ⟨2957046, by rfl⟩ : syracuseStep 7885457 = 5914093) B5914093
theorem B204993217 : Blo 1383511 204993217 := bstep (se 2 (by rfl) ⟨76872456, by rfl⟩ : syracuseStep 204993217 = 153744913) B153744913
theorem B5255999 : Blo 1383511 5255999 := bstep (se 1 (by rfl) ⟨3941999, by rfl⟩ : syracuseStep 5255999 = 7883999) B7883999
theorem B2077577 : Blo 1383511 2077577 := bstep (se 2 (by rfl) ⟨779091, by rfl⟩ : syracuseStep 2077577 = 1558183) B1558183
theorem B56866009 : Blo 1383511 56866009 := bstep (se 2 (by rfl) ⟨21324753, by rfl⟩ : syracuseStep 56866009 = 42649507) B42649507
theorem B2077961 : Blo 1383511 2077961 := bstep (se 2 (by rfl) ⟨779235, by rfl⟩ : syracuseStep 2077961 = 1558471) B1558471
theorem B2078015 : Blo 1383511 2078015 := bstep (se 1 (by rfl) ⟨1558511, by rfl⟩ : syracuseStep 2078015 = 3117023) B3117023
theorem B26621257 : Blo 1383511 26621257 := bstep (se 2 (by rfl) ⟨9982971, by rfl⟩ : syracuseStep 26621257 = 19965943) B19965943
theorem B2954971 : Blo 1383511 2954971 := bstep (se 1 (by rfl) ⟨2216228, by rfl⟩ : syracuseStep 2954971 = 4432457) B4432457
theorem B5257001 : Blo 1383511 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B16832609 : Blo 1383511 16832609 := bstep (se 2 (by rfl) ⟨6312228, by rfl⟩ : syracuseStep 16832609 = 12624457) B12624457
theorem B15759521 : Blo 1383511 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B2628463 : Blo 1383511 2628463 := bstep (se 1 (by rfl) ⟨1971347, by rfl⟩ : syracuseStep 2628463 = 3942695) B3942695
theorem B26606495 : Blo 1383511 26606495 := bstep (se 1 (by rfl) ⟨19954871, by rfl⟩ : syracuseStep 26606495 = 39909743) B39909743
theorem B19971137 : Blo 1383511 19971137 := bstep (se 2 (by rfl) ⟨7489176, by rfl⟩ : syracuseStep 19971137 = 14978353) B14978353
theorem B1383515 : Blo 1383511 1383515 := bstep (se 1 (by rfl) ⟨1037636, by rfl⟩ : syracuseStep 1383515 = 2075273) B2075273
theorem B1383631 : Blo 1383511 1383631 := bstep (se 1 (by rfl) ⟨1037723, by rfl⟩ : syracuseStep 1383631 = 2075447) B2075447
theorem B1383655 : Blo 1383511 1383655 := bstep (se 1 (by rfl) ⟨1037741, by rfl⟩ : syracuseStep 1383655 = 2075483) B2075483
theorem B3325159 : Blo 1383511 3325159 := bstep (se 1 (by rfl) ⟨2493869, by rfl⟩ : syracuseStep 3325159 = 4987739) B4987739
theorem B113605901 : Blo 1383511 113605901 := bstep (se 3 (by rfl) ⟨21301106, by rfl⟩ : syracuseStep 113605901 = 42602213) B42602213
theorem B1383751 : Blo 1383511 1383751 := bstep (se 1 (by rfl) ⟨1037813, by rfl⟩ : syracuseStep 1383751 = 2075627) B2075627
theorem B1383887 : Blo 1383511 1383887 := bstep (se 1 (by rfl) ⟨1037915, by rfl⟩ : syracuseStep 1383887 = 2075831) B2075831
theorem B10518011 : Blo 1383511 10518011 := bstep (se 1 (by rfl) ⟨7888508, by rfl⟩ : syracuseStep 10518011 = 15777017) B15777017
theorem B1384047 : Blo 1383511 1384047 := bstep (se 1 (by rfl) ⟨1038035, by rfl⟩ : syracuseStep 1384047 = 2076071) B2076071
theorem B1384103 : Blo 1383511 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B6315745 : Blo 1383511 6315745 := bstep (se 2 (by rfl) ⟨2368404, by rfl⟩ : syracuseStep 6315745 = 4736809) B4736809
theorem B1384167 : Blo 1383511 1384167 := bstep (se 1 (by rfl) ⟨1038125, by rfl⟩ : syracuseStep 1384167 = 2076251) B2076251
theorem B1384223 : Blo 1383511 1384223 := bstep (se 1 (by rfl) ⟨1038167, by rfl⟩ : syracuseStep 1384223 = 2076335) B2076335
theorem B5259113 : Blo 1383511 5259113 := bstep (se 2 (by rfl) ⟨1972167, by rfl⟩ : syracuseStep 5259113 = 3944335) B3944335
theorem B1384303 : Blo 1383511 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B1662887 : Blo 1383511 1662887 := bstep (se 1 (by rfl) ⟨1247165, by rfl⟩ : syracuseStep 1662887 = 2494331) B2494331
theorem B1384359 : Blo 1383511 1384359 := bstep (se 1 (by rfl) ⟨1038269, by rfl⟩ : syracuseStep 1384359 = 2076539) B2076539
theorem B3326035 : Blo 1383511 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B1384603 : Blo 1383511 1384603 := bstep (se 1 (by rfl) ⟨1038452, by rfl⟩ : syracuseStep 1384603 = 2076905) B2076905
theorem B1384687 : Blo 1383511 1384687 := bstep (se 1 (by rfl) ⟨1038515, by rfl⟩ : syracuseStep 1384687 = 2077031) B2077031
theorem B5915051 : Blo 1383511 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B10518983 : Blo 1383511 10518983 := bstep (se 1 (by rfl) ⟨7889237, by rfl⟩ : syracuseStep 10518983 = 15778475) B15778475
theorem B4669919 : Blo 1383511 4669919 := bstep (se 1 (by rfl) ⟨3502439, by rfl⟩ : syracuseStep 4669919 = 7004879) B7004879
theorem B1556959 : Blo 1383511 1556959 := bstep (se 1 (by rfl) ⟨1167719, by rfl⟩ : syracuseStep 1556959 = 2335439) B2335439
theorem B1385051 : Blo 1383511 1385051 := bstep (se 1 (by rfl) ⟨1038788, by rfl⟩ : syracuseStep 1385051 = 2077577) B2077577
theorem B3113639 : Blo 1383511 3113639 := bstep (se 1 (by rfl) ⟨2335229, by rfl⟩ : syracuseStep 3113639 = 4670459) B4670459
theorem B1385307 : Blo 1383511 1385307 := bstep (se 1 (by rfl) ⟨1038980, by rfl⟩ : syracuseStep 1385307 = 2077961) B2077961
theorem B7881583 : Blo 1383511 7881583 := bstep (se 1 (by rfl) ⟨5911187, by rfl⟩ : syracuseStep 7881583 = 11822375) B11822375
theorem B1385343 : Blo 1383511 1385343 := bstep (se 1 (by rfl) ⟨1039007, by rfl⟩ : syracuseStep 1385343 = 2078015) B2078015
theorem B56837123 : Blo 1383511 56837123 := bstep (se 1 (by rfl) ⟨42627842, by rfl⟩ : syracuseStep 56837123 = 85255685) B85255685
theorem B5686381 : Blo 1383511 5686381 := bstep (se 3 (by rfl) ⟨1066196, by rfl⟩ : syracuseStep 5686381 = 2132393) B2132393
theorem B4670675 : Blo 1383511 4670675 := bstep (se 1 (by rfl) ⟨3503006, by rfl⟩ : syracuseStep 4670675 = 7006013) B7006013
theorem B1557823 : Blo 1383511 1557823 := bstep (se 1 (by rfl) ⟨1168367, by rfl⟩ : syracuseStep 1557823 = 2336735) B2336735
theorem B7013789 : Blo 1383511 7013789 := bstep (se 3 (by rfl) ⟨1315085, by rfl⟩ : syracuseStep 7013789 = 2630171) B2630171
theorem B7013951 : Blo 1383511 7013951 := bstep (se 1 (by rfl) ⟨5260463, by rfl⟩ : syracuseStep 7013951 = 10520927) B10520927
theorem B4433545 : Blo 1383511 4433545 := bstep (se 2 (by rfl) ⟨1662579, by rfl⟩ : syracuseStep 4433545 = 3325159) B3325159
theorem B17737663 : Blo 1383511 17737663 := bstep (se 1 (by rfl) ⟨13303247, by rfl⟩ : syracuseStep 17737663 = 26606495) B26606495
theorem B13314091 : Blo 1383511 13314091 := bstep (se 1 (by rfl) ⟨9985568, by rfl⟩ : syracuseStep 13314091 = 19971137) B19971137
theorem B75737267 : Blo 1383511 75737267 := bstep (se 1 (by rfl) ⟨56802950, by rfl⟩ : syracuseStep 75737267 = 113605901) B113605901
theorem B1384443 : Blo 1383511 1384443 := bstep (se 1 (by rfl) ⟨1038332, by rfl⟩ : syracuseStep 1384443 = 2076665) B2076665
theorem B28403945 : Blo 1383511 28403945 := bstep (se 2 (by rfl) ⟨10651479, by rfl⟩ : syracuseStep 28403945 = 21302959) B21302959
theorem B22464803 : Blo 1383511 22464803 := bstep (se 1 (by rfl) ⟨16848602, by rfl⟩ : syracuseStep 22464803 = 33697205) B33697205
theorem B4434365 : Blo 1383511 4434365 := bstep (se 3 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 4434365 = 1662887) B1662887
theorem B3115727 : Blo 1383511 3115727 := bstep (se 1 (by rfl) ⟨2336795, by rfl⟩ : syracuseStep 3115727 = 4673591) B4673591
theorem B4672295 : Blo 1383511 4672295 := bstep (se 1 (by rfl) ⟨3504221, by rfl⟩ : syracuseStep 4672295 = 7008443) B7008443
theorem B3550063 : Blo 1383511 3550063 := bstep (se 1 (by rfl) ⟨2662547, by rfl⟩ : syracuseStep 3550063 = 5325095) B5325095
theorem B3115943 : Blo 1383511 3115943 := bstep (se 1 (by rfl) ⟨2336957, by rfl⟩ : syracuseStep 3115943 = 4673915) B4673915
theorem B2075561 : Blo 1383511 2075561 := bstep (se 2 (by rfl) ⟨778335, by rfl⟩ : syracuseStep 2075561 = 1556671) B1556671
theorem B2075591 : Blo 1383511 2075591 := bstep (se 1 (by rfl) ⟨1556693, by rfl⟩ : syracuseStep 2075591 = 3113387) B3113387
theorem B2075711 : Blo 1383511 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B3116105 : Blo 1383511 3116105 := bstep (se 2 (by rfl) ⟨1168539, by rfl⟩ : syracuseStep 3116105 = 2337079) B2337079
theorem B3116123 : Blo 1383511 3116123 := bstep (se 1 (by rfl) ⟨2337092, by rfl⟩ : syracuseStep 3116123 = 4674185) B4674185
theorem B22457483 : Blo 1383511 22457483 := bstep (se 1 (by rfl) ⟨16843112, by rfl⟩ : syracuseStep 22457483 = 33686225) B33686225
theorem B2075951 : Blo 1383511 2075951 := bstep (se 1 (by rfl) ⟨1556963, by rfl⟩ : syracuseStep 2075951 = 3113927) B3113927
theorem B4435327 : Blo 1383511 4435327 := bstep (se 1 (by rfl) ⟨3326495, by rfl⟩ : syracuseStep 4435327 = 6652991) B6652991
theorem B2076137 : Blo 1383511 2076137 := bstep (se 2 (by rfl) ⟨778551, by rfl⟩ : syracuseStep 2076137 = 1557103) B1557103
theorem B2076191 : Blo 1383511 2076191 := bstep (se 1 (by rfl) ⟨1557143, by rfl⟩ : syracuseStep 2076191 = 3114287) B3114287
theorem B7007795 : Blo 1383511 7007795 := bstep (se 1 (by rfl) ⟨5255846, by rfl⟩ : syracuseStep 7007795 = 10511693) B10511693
theorem B3944027 : Blo 1383511 3944027 := bstep (se 1 (by rfl) ⟨2958020, by rfl⟩ : syracuseStep 3944027 = 5916041) B5916041
theorem B2076281 : Blo 1383511 2076281 := bstep (se 2 (by rfl) ⟨778605, by rfl⟩ : syracuseStep 2076281 = 1557211) B1557211
theorem B5910353 : Blo 1383511 5910353 := bstep (se 2 (by rfl) ⟨2216382, by rfl⟩ : syracuseStep 5910353 = 4432765) B4432765
theorem B2076527 : Blo 1383511 2076527 := bstep (se 1 (by rfl) ⟨1557395, by rfl⟩ : syracuseStep 2076527 = 3114791) B3114791
theorem B7884773 : Blo 1383511 7884773 := bstep (se 4 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 7884773 = 1478395) B1478395
theorem B25268233 : Blo 1383511 25268233 := bstep (se 2 (by rfl) ⟨9475587, by rfl⟩ : syracuseStep 25268233 = 18951175) B18951175
theorem B3944551 : Blo 1383511 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B10506347 : Blo 1383511 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B2076779 : Blo 1383511 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B3944609 : Blo 1383511 3944609 := bstep (se 2 (by rfl) ⟨1479228, by rfl⟩ : syracuseStep 3944609 = 2958457) B2958457
theorem B11825351 : Blo 1383511 11825351 := bstep (se 1 (by rfl) ⟨8869013, by rfl⟩ : syracuseStep 11825351 = 17738027) B17738027
theorem B19214567 : Blo 1383511 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B75821345 : Blo 1383511 75821345 := bstep (se 2 (by rfl) ⟨28433004, by rfl⟩ : syracuseStep 75821345 = 56866009) B56866009
theorem B2077211 : Blo 1383511 2077211 := bstep (se 1 (by rfl) ⟨1557908, by rfl⟩ : syracuseStep 2077211 = 3115817) B3115817
theorem B2077391 : Blo 1383511 2077391 := bstep (se 1 (by rfl) ⟨1558043, by rfl⟩ : syracuseStep 2077391 = 3116087) B3116087
theorem B7009091 : Blo 1383511 7009091 := bstep (se 1 (by rfl) ⟨5256818, by rfl⟩ : syracuseStep 7009091 = 10513637) B10513637
theorem B6648743 : Blo 1383511 6648743 := bstep (se 1 (by rfl) ⟨4986557, by rfl⟩ : syracuseStep 6648743 = 9973115) B9973115
theorem B2077679 : Blo 1383511 2077679 := bstep (se 1 (by rfl) ⟨1558259, by rfl⟩ : syracuseStep 2077679 = 3116519) B3116519
theorem B3552281 : Blo 1383511 3552281 := bstep (se 2 (by rfl) ⟨1332105, by rfl⟩ : syracuseStep 3552281 = 2664211) B2664211
theorem B7009415 : Blo 1383511 7009415 := bstep (se 1 (by rfl) ⟨5257061, by rfl⟩ : syracuseStep 7009415 = 10514123) B10514123
theorem B8877239 : Blo 1383511 8877239 := bstep (se 1 (by rfl) ⟨6657929, by rfl⟩ : syracuseStep 8877239 = 13315859) B13315859
theorem B1971535 : Blo 1383511 1971535 := bstep (se 1 (by rfl) ⟨1478651, by rfl⟩ : syracuseStep 1971535 = 2957303) B2957303
theorem B3159407 : Blo 1383511 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B2078063 : Blo 1383511 2078063 := bstep (se 1 (by rfl) ⟨1558547, by rfl⟩ : syracuseStep 2078063 = 3117095) B3117095
theorem B67368347 : Blo 1383511 67368347 := bstep (se 1 (by rfl) ⟨50526260, by rfl⟩ : syracuseStep 67368347 = 101052521) B101052521
theorem B2078183 : Blo 1383511 2078183 := bstep (se 1 (by rfl) ⟨1558637, by rfl⟩ : syracuseStep 2078183 = 3117275) B3117275
theorem B1971803 : Blo 1383511 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B5256971 : Blo 1383511 5256971 := bstep (se 1 (by rfl) ⟨3942728, by rfl⟩ : syracuseStep 5256971 = 7885457) B7885457
theorem B29931281 : Blo 1383511 29931281 := bstep (se 2 (by rfl) ⟨11224230, by rfl⟩ : syracuseStep 29931281 = 22448461) B22448461
theorem B2627407 : Blo 1383511 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B3503999 : Blo 1383511 3503999 := bstep (se 1 (by rfl) ⟨2627999, by rfl⟩ : syracuseStep 3503999 = 5255999) B5255999
theorem B11835497 : Blo 1383511 11835497 := bstep (se 2 (by rfl) ⟨4438311, by rfl⟩ : syracuseStep 11835497 = 8876623) B8876623
theorem B273324289 : Blo 1383511 273324289 := bstep (se 2 (by rfl) ⟨102496608, by rfl⟩ : syracuseStep 273324289 = 204993217) B204993217
theorem B15980819 : Blo 1383511 15980819 := bstep (se 1 (by rfl) ⟨11985614, by rfl⟩ : syracuseStep 15980819 = 23971229) B23971229
theorem B3504617 : Blo 1383511 3504617 := bstep (se 2 (by rfl) ⟨1314231, by rfl⟩ : syracuseStep 3504617 = 2628463) B2628463
theorem B3504667 : Blo 1383511 3504667 := bstep (se 1 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 3504667 = 5257001) B5257001
theorem B11221739 : Blo 1383511 11221739 := bstep (se 1 (by rfl) ⟨8416304, by rfl⟩ : syracuseStep 11221739 = 16832609) B16832609
theorem B10509263 : Blo 1383511 10509263 := bstep (se 1 (by rfl) ⟨7881947, by rfl⟩ : syracuseStep 10509263 = 15763895) B15763895
theorem B35495009 : Blo 1383511 35495009 := bstep (se 2 (by rfl) ⟨13310628, by rfl⟩ : syracuseStep 35495009 = 26621257) B26621257
theorem B1383743 : Blo 1383511 1383743 := bstep (se 1 (by rfl) ⟨1037807, by rfl⟩ : syracuseStep 1383743 = 2075615) B2075615
theorem B53222831 : Blo 1383511 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B31989181 : Blo 1383511 31989181 := bstep (se 3 (by rfl) ⟨5997971, by rfl⟩ : syracuseStep 31989181 = 11995943) B11995943
theorem B3939835 : Blo 1383511 3939835 := bstep (se 1 (by rfl) ⟨2954876, by rfl⟩ : syracuseStep 3939835 = 5909753) B5909753
theorem B1384039 : Blo 1383511 1384039 := bstep (se 1 (by rfl) ⟨1038029, by rfl⟩ : syracuseStep 1384039 = 2076059) B2076059
theorem B3939961 : Blo 1383511 3939961 := bstep (se 2 (by rfl) ⟨1477485, by rfl⟩ : syracuseStep 3939961 = 2954971) B2954971
theorem B8420993 : Blo 1383511 8420993 := bstep (se 2 (by rfl) ⟨3157872, by rfl⟩ : syracuseStep 8420993 = 6315745) B6315745
theorem B7012007 : Blo 1383511 7012007 := bstep (se 1 (by rfl) ⟨5259005, by rfl⟩ : syracuseStep 7012007 = 10518011) B10518011
theorem B1384319 : Blo 1383511 1384319 := bstep (se 1 (by rfl) ⟨1038239, by rfl⟩ : syracuseStep 1384319 = 2076479) B2076479
theorem B5054363 : Blo 1383511 5054363 := bstep (se 1 (by rfl) ⟨3790772, by rfl⟩ : syracuseStep 5054363 = 7581545) B7581545
theorem B10510235 : Blo 1383511 10510235 := bstep (se 1 (by rfl) ⟨7882676, by rfl⟩ : syracuseStep 10510235 = 15765353) B15765353
theorem B3506075 : Blo 1383511 3506075 := bstep (se 1 (by rfl) ⟨2629556, by rfl⟩ : syracuseStep 3506075 = 5259113) B5259113
theorem B17752121 : Blo 1383511 17752121 := bstep (se 2 (by rfl) ⟨6657045, by rfl⟩ : syracuseStep 17752121 = 13314091) B13314091
theorem B7004231 : Blo 1383511 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B1384519 : Blo 1383511 1384519 := bstep (se 1 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 1384519 = 2076779) B2076779
theorem B2629739 : Blo 1383511 2629739 := bstep (se 1 (by rfl) ⟨1972304, by rfl⟩ : syracuseStep 2629739 = 3944609) B3944609
theorem B5259401 : Blo 1383511 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B7012655 : Blo 1383511 7012655 := bstep (se 1 (by rfl) ⟨5259491, by rfl⟩ : syracuseStep 7012655 = 10518983) B10518983
theorem B3113279 : Blo 1383511 3113279 := bstep (se 1 (by rfl) ⟨2334959, by rfl⟩ : syracuseStep 3113279 = 4669919) B4669919
theorem B1384807 : Blo 1383511 1384807 := bstep (se 1 (by rfl) ⟨1038605, by rfl⟩ : syracuseStep 1384807 = 2077211) B2077211
theorem B1384927 : Blo 1383511 1384927 := bstep (se 1 (by rfl) ⟨1038695, by rfl⟩ : syracuseStep 1384927 = 2077391) B2077391
theorem B30327365 : Blo 1383511 30327365 := bstep (se 4 (by rfl) ⟨2843190, by rfl⟩ : syracuseStep 30327365 = 5686381) B5686381
theorem B4432495 : Blo 1383511 4432495 := bstep (se 1 (by rfl) ⟨3324371, by rfl⟩ : syracuseStep 4432495 = 6648743) B6648743
theorem B1385119 : Blo 1383511 1385119 := bstep (se 1 (by rfl) ⟨1038839, by rfl⟩ : syracuseStep 1385119 = 2077679) B2077679
theorem B2368187 : Blo 1383511 2368187 := bstep (se 1 (by rfl) ⟨1776140, by rfl⟩ : syracuseStep 2368187 = 3552281) B3552281
theorem B42615517 : Blo 1383511 42615517 := bstep (se 3 (by rfl) ⟨7990409, by rfl⟩ : syracuseStep 42615517 = 15980819) B15980819
theorem B3113783 : Blo 1383511 3113783 := bstep (se 1 (by rfl) ⟨2335337, by rfl⟩ : syracuseStep 3113783 = 4670675) B4670675
theorem B2106271 : Blo 1383511 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B1385375 : Blo 1383511 1385375 := bstep (se 1 (by rfl) ⟨1039031, by rfl⟩ : syracuseStep 1385375 = 2078063) B2078063
theorem B1385455 : Blo 1383511 1385455 := bstep (se 1 (by rfl) ⟨1039091, by rfl⟩ : syracuseStep 1385455 = 2078183) B2078183
theorem B2335999 : Blo 1383511 2335999 := bstep (se 1 (by rfl) ⟨1751999, by rfl⟩ : syracuseStep 2335999 = 3503999) B3503999
theorem B7890331 : Blo 1383511 7890331 := bstep (se 1 (by rfl) ⟨5917748, by rfl⟩ : syracuseStep 7890331 = 11835497) B11835497
theorem B14976535 : Blo 1383511 14976535 := bstep (se 1 (by rfl) ⟨11232401, by rfl⟩ : syracuseStep 14976535 = 22464803) B22464803
theorem B2336411 : Blo 1383511 2336411 := bstep (se 1 (by rfl) ⟨1752308, by rfl⟩ : syracuseStep 2336411 = 3504617) B3504617
theorem B7481159 : Blo 1383511 7481159 := bstep (se 1 (by rfl) ⟨5610869, by rfl⟩ : syracuseStep 7481159 = 11221739) B11221739
theorem B3114863 : Blo 1383511 3114863 := bstep (se 1 (by rfl) ⟨2336147, by rfl⟩ : syracuseStep 3114863 = 4672295) B4672295
theorem B7006175 : Blo 1383511 7006175 := bstep (se 1 (by rfl) ⟨5254631, by rfl⟩ : syracuseStep 7006175 = 10509263) B10509263
theorem B5253113 : Blo 1383511 5253113 := bstep (se 2 (by rfl) ⟨1969917, by rfl⟩ : syracuseStep 5253113 = 3939835) B3939835
theorem B5253281 : Blo 1383511 5253281 := bstep (se 2 (by rfl) ⟨1969980, by rfl⟩ : syracuseStep 5253281 = 3939961) B3939961
theorem B35481887 : Blo 1383511 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B4671863 : Blo 1383511 4671863 := bstep (se 1 (by rfl) ⟨3503897, by rfl⟩ : syracuseStep 4671863 = 7007795) B7007795
theorem B5613995 : Blo 1383511 5613995 := bstep (se 1 (by rfl) ⟨4210496, by rfl⟩ : syracuseStep 5613995 = 8420993) B8420993
theorem B3369575 : Blo 1383511 3369575 := bstep (se 1 (by rfl) ⟨2527181, by rfl⟩ : syracuseStep 3369575 = 5054363) B5054363
theorem B7006823 : Blo 1383511 7006823 := bstep (se 1 (by rfl) ⟨5255117, by rfl⟩ : syracuseStep 7006823 = 10510235) B10510235
theorem B2337383 : Blo 1383511 2337383 := bstep (se 1 (by rfl) ⟨1753037, by rfl⟩ : syracuseStep 2337383 = 3506075) B3506075
theorem B4434713 : Blo 1383511 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B7883567 : Blo 1383511 7883567 := bstep (se 1 (by rfl) ⟨5912675, by rfl⟩ : syracuseStep 7883567 = 11825351) B11825351
theorem B50547563 : Blo 1383511 50547563 := bstep (se 1 (by rfl) ⟨37910672, by rfl⟩ : syracuseStep 50547563 = 75821345) B75821345
theorem B3943367 : Blo 1383511 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B364432385 : Blo 1383511 364432385 := bstep (se 2 (by rfl) ⟨136662144, by rfl⟩ : syracuseStep 364432385 = 273324289) B273324289
theorem B2075759 : Blo 1383511 2075759 := bstep (se 1 (by rfl) ⟨1556819, by rfl⟩ : syracuseStep 2075759 = 3113639) B3113639
theorem B4672727 : Blo 1383511 4672727 := bstep (se 1 (by rfl) ⟨3504545, by rfl⟩ : syracuseStep 4672727 = 7009091) B7009091
theorem B2075945 : Blo 1383511 2075945 := bstep (se 2 (by rfl) ⟨778479, by rfl⟩ : syracuseStep 2075945 = 1556959) B1556959
theorem B37891415 : Blo 1383511 37891415 := bstep (se 1 (by rfl) ⟨28418561, by rfl⟩ : syracuseStep 37891415 = 56837123) B56837123
theorem B4672889 : Blo 1383511 4672889 := bstep (se 2 (by rfl) ⟨1752333, by rfl⟩ : syracuseStep 4672889 = 3504667) B3504667
theorem B4672943 : Blo 1383511 4672943 := bstep (se 1 (by rfl) ⟨3504707, by rfl⟩ : syracuseStep 4672943 = 7009415) B7009415
theorem B5918159 : Blo 1383511 5918159 := bstep (se 1 (by rfl) ⟨4438619, by rfl⟩ : syracuseStep 5918159 = 8877239) B8877239
theorem B44912231 : Blo 1383511 44912231 := bstep (se 1 (by rfl) ⟨33684173, by rfl⟩ : syracuseStep 44912231 = 67368347) B67368347
theorem B11824973 : Blo 1383511 11824973 := bstep (se 3 (by rfl) ⟨2217182, by rfl⟩ : syracuseStep 11824973 = 4434365) B4434365
theorem B50491511 : Blo 1383511 50491511 := bstep (se 1 (by rfl) ⟨37868633, by rfl⟩ : syracuseStep 50491511 = 75737267) B75737267
theorem B18935963 : Blo 1383511 18935963 := bstep (se 1 (by rfl) ⟨14201972, by rfl⟩ : syracuseStep 18935963 = 28403945) B28403945
theorem B2077097 : Blo 1383511 2077097 := bstep (se 2 (by rfl) ⟨778911, by rfl⟩ : syracuseStep 2077097 = 1557823) B1557823
theorem B2077151 : Blo 1383511 2077151 := bstep (se 1 (by rfl) ⟨1557863, by rfl⟩ : syracuseStep 2077151 = 3115727) B3115727
theorem B42652241 : Blo 1383511 42652241 := bstep (se 2 (by rfl) ⟨15994590, by rfl⟩ : syracuseStep 42652241 = 31989181) B31989181
theorem B2077295 : Blo 1383511 2077295 := bstep (se 1 (by rfl) ⟨1557971, by rfl⟩ : syracuseStep 2077295 = 3115943) B3115943
theorem B2077403 : Blo 1383511 2077403 := bstep (se 1 (by rfl) ⟨1558052, by rfl⟩ : syracuseStep 2077403 = 3116105) B3116105
theorem B2077415 : Blo 1383511 2077415 := bstep (se 1 (by rfl) ⟨1558061, by rfl⟩ : syracuseStep 2077415 = 3116123) B3116123
theorem B23663339 : Blo 1383511 23663339 := bstep (se 1 (by rfl) ⟨17747504, by rfl⟩ : syracuseStep 23663339 = 35495009) B35495009
theorem B14971655 : Blo 1383511 14971655 := bstep (se 1 (by rfl) ⟨11228741, by rfl⟩ : syracuseStep 14971655 = 22457483) B22457483
theorem B5911393 : Blo 1383511 5911393 := bstep (se 2 (by rfl) ⟨2216772, by rfl⟩ : syracuseStep 5911393 = 4433545) B4433545
theorem B3503209 : Blo 1383511 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B4674671 : Blo 1383511 4674671 := bstep (se 1 (by rfl) ⟨3506003, by rfl⟩ : syracuseStep 4674671 = 7012007) B7012007
theorem B5256515 : Blo 1383511 5256515 := bstep (se 1 (by rfl) ⟨3942386, by rfl⟩ : syracuseStep 5256515 = 7884773) B7884773
theorem B33690977 : Blo 1383511 33690977 := bstep (se 2 (by rfl) ⟨12634116, by rfl⟩ : syracuseStep 33690977 = 25268233) B25268233
theorem B12809711 : Blo 1383511 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B4675859 : Blo 1383511 4675859 := bstep (se 1 (by rfl) ⟨3506894, by rfl⟩ : syracuseStep 4675859 = 7013789) B7013789
theorem B4675967 : Blo 1383511 4675967 := bstep (se 1 (by rfl) ⟨3506975, by rfl⟩ : syracuseStep 4675967 = 7013951) B7013951
theorem B4733417 : Blo 1383511 4733417 := bstep (se 2 (by rfl) ⟨1775031, by rfl⟩ : syracuseStep 4733417 = 3550063) B3550063
theorem B10508777 : Blo 1383511 10508777 := bstep (se 2 (by rfl) ⟨3940791, by rfl⟩ : syracuseStep 10508777 = 7881583) B7881583
theorem B3504647 : Blo 1383511 3504647 := bstep (se 1 (by rfl) ⟨2628485, by rfl⟩ : syracuseStep 3504647 = 5256971) B5256971
theorem B19954187 : Blo 1383511 19954187 := bstep (se 1 (by rfl) ⟨14965640, by rfl⟩ : syracuseStep 19954187 = 29931281) B29931281
theorem B5258141 : Blo 1383511 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B2628713 : Blo 1383511 2628713 := bstep (se 2 (by rfl) ⟨985767, by rfl⟩ : syracuseStep 2628713 = 1971535) B1971535
theorem B5913769 : Blo 1383511 5913769 := bstep (se 2 (by rfl) ⟨2217663, by rfl⟩ : syracuseStep 5913769 = 4435327) B4435327
theorem B1383707 : Blo 1383511 1383707 := bstep (se 1 (by rfl) ⟨1037780, by rfl⟩ : syracuseStep 1383707 = 2075561) B2075561
theorem B1383727 : Blo 1383511 1383727 := bstep (se 1 (by rfl) ⟨1037795, by rfl⟩ : syracuseStep 1383727 = 2075591) B2075591
theorem B1383807 : Blo 1383511 1383807 := bstep (se 1 (by rfl) ⟨1037855, by rfl⟩ : syracuseStep 1383807 = 2075711) B2075711
theorem B1383967 : Blo 1383511 1383967 := bstep (se 1 (by rfl) ⟨1037975, by rfl⟩ : syracuseStep 1383967 = 2075951) B2075951
theorem B1384091 : Blo 1383511 1384091 := bstep (se 1 (by rfl) ⟨1038068, by rfl⟩ : syracuseStep 1384091 = 2076137) B2076137
theorem B1384127 : Blo 1383511 1384127 := bstep (se 1 (by rfl) ⟨1038095, by rfl⟩ : syracuseStep 1384127 = 2076191) B2076191
theorem B2629351 : Blo 1383511 2629351 := bstep (se 1 (by rfl) ⟨1972013, by rfl⟩ : syracuseStep 2629351 = 3944027) B3944027
theorem B1384187 : Blo 1383511 1384187 := bstep (se 1 (by rfl) ⟨1038140, by rfl⟩ : syracuseStep 1384187 = 2076281) B2076281
theorem B3940235 : Blo 1383511 3940235 := bstep (se 1 (by rfl) ⟨2955176, by rfl⟩ : syracuseStep 3940235 = 5910353) B5910353
theorem B1384351 : Blo 1383511 1384351 := bstep (se 1 (by rfl) ⟨1038263, by rfl⟩ : syracuseStep 1384351 = 2076527) B2076527
theorem B23650217 : Blo 1383511 23650217 := bstep (se 2 (by rfl) ⟨8868831, by rfl⟩ : syracuseStep 23650217 = 17737663) B17737663
theorem B4669487 : Blo 1383511 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B1753159 : Blo 1383511 1753159 := bstep (se 1 (by rfl) ⟨1314869, by rfl⟩ : syracuseStep 1753159 = 2629739) B2629739
theorem B33661007 : Blo 1383511 33661007 := bstep (se 1 (by rfl) ⟨25245755, by rfl⟩ : syracuseStep 33661007 = 50491511) B50491511
theorem B3506267 : Blo 1383511 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B12623975 : Blo 1383511 12623975 := bstep (se 1 (by rfl) ⟨9467981, by rfl⟩ : syracuseStep 12623975 = 18935963) B18935963
theorem B1384731 : Blo 1383511 1384731 := bstep (se 1 (by rfl) ⟨1038548, by rfl⟩ : syracuseStep 1384731 = 2077097) B2077097
theorem B1384767 : Blo 1383511 1384767 := bstep (se 1 (by rfl) ⟨1038575, by rfl⟩ : syracuseStep 1384767 = 2077151) B2077151
theorem B20218243 : Blo 1383511 20218243 := bstep (se 1 (by rfl) ⟨15163682, by rfl⟩ : syracuseStep 20218243 = 30327365) B30327365
theorem B28434827 : Blo 1383511 28434827 := bstep (se 1 (by rfl) ⟨21326120, by rfl⟩ : syracuseStep 28434827 = 42652241) B42652241
theorem B1384863 : Blo 1383511 1384863 := bstep (se 1 (by rfl) ⟨1038647, by rfl⟩ : syracuseStep 1384863 = 2077295) B2077295
theorem B1384935 : Blo 1383511 1384935 := bstep (se 1 (by rfl) ⟨1038701, by rfl⟩ : syracuseStep 1384935 = 2077403) B2077403
theorem B1384943 : Blo 1383511 1384943 := bstep (se 1 (by rfl) ⟨1038707, by rfl⟩ : syracuseStep 1384943 = 2077415) B2077415
theorem B56820689 : Blo 1383511 56820689 := bstep (se 2 (by rfl) ⟨21307758, by rfl⟩ : syracuseStep 56820689 = 42615517) B42615517
theorem B1557607 : Blo 1383511 1557607 := bstep (se 1 (by rfl) ⟨1168205, by rfl⟩ : syracuseStep 1557607 = 2336411) B2336411
theorem B7881857 : Blo 1383511 7881857 := bstep (se 2 (by rfl) ⟨2955696, by rfl⟩ : syracuseStep 7881857 = 5911393) B5911393
theorem B4670783 : Blo 1383511 4670783 := bstep (se 1 (by rfl) ⟨3503087, by rfl⟩ : syracuseStep 4670783 = 7006175) B7006175
theorem B4670945 : Blo 1383511 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B3114575 : Blo 1383511 3114575 := bstep (se 1 (by rfl) ⟨2335931, by rfl⟩ : syracuseStep 3114575 = 4671863) B4671863
theorem B3155611 : Blo 1383511 3155611 := bstep (se 1 (by rfl) ⟨2366708, by rfl⟩ : syracuseStep 3155611 = 4733417) B4733417
theorem B7005851 : Blo 1383511 7005851 := bstep (se 1 (by rfl) ⟨5254388, by rfl⟩ : syracuseStep 7005851 = 10508777) B10508777
theorem B3114665 : Blo 1383511 3114665 := bstep (se 2 (by rfl) ⟨1167999, by rfl⟩ : syracuseStep 3114665 = 2335999) B2335999
theorem B2336431 : Blo 1383511 2336431 := bstep (se 1 (by rfl) ⟨1752323, by rfl⟩ : syracuseStep 2336431 = 3504647) B3504647
theorem B2246383 : Blo 1383511 2246383 := bstep (se 1 (by rfl) ⟨1684787, by rfl⟩ : syracuseStep 2246383 = 3369575) B3369575
theorem B4671215 : Blo 1383511 4671215 := bstep (se 1 (by rfl) ⟨3503411, by rfl⟩ : syracuseStep 4671215 = 7006823) B7006823
theorem B1558255 : Blo 1383511 1558255 := bstep (se 1 (by rfl) ⟨1168691, by rfl⟩ : syracuseStep 1558255 = 2337383) B2337383
theorem B10520441 : Blo 1383511 10520441 := bstep (se 2 (by rfl) ⟨3945165, by rfl⟩ : syracuseStep 10520441 = 7890331) B7890331
theorem B3115151 : Blo 1383511 3115151 := bstep (se 1 (by rfl) ⟨2336363, by rfl⟩ : syracuseStep 3115151 = 4672727) B4672727
theorem B3115259 : Blo 1383511 3115259 := bstep (se 1 (by rfl) ⟨2336444, by rfl⟩ : syracuseStep 3115259 = 4672889) B4672889
theorem B3115295 : Blo 1383511 3115295 := bstep (se 1 (by rfl) ⟨2336471, by rfl⟩ : syracuseStep 3115295 = 4672943) B4672943
theorem B7883315 : Blo 1383511 7883315 := bstep (se 1 (by rfl) ⟨5912486, by rfl⟩ : syracuseStep 7883315 = 11824973) B11824973
theorem B2075519 : Blo 1383511 2075519 := bstep (se 1 (by rfl) ⟨1556639, by rfl⟩ : syracuseStep 2075519 = 3113279) B3113279
theorem B9981103 : Blo 1383511 9981103 := bstep (se 1 (by rfl) ⟨7485827, by rfl⟩ : syracuseStep 9981103 = 14971655) B14971655
theorem B2075855 : Blo 1383511 2075855 := bstep (se 1 (by rfl) ⟨1556891, by rfl⟩ : syracuseStep 2075855 = 3113783) B3113783
theorem B3116447 : Blo 1383511 3116447 := bstep (se 1 (by rfl) ⟨2337335, by rfl⟩ : syracuseStep 3116447 = 4674671) B4674671
theorem B5909993 : Blo 1383511 5909993 := bstep (se 2 (by rfl) ⟨2216247, by rfl⟩ : syracuseStep 5909993 = 4432495) B4432495
theorem B14970653 : Blo 1383511 14970653 := bstep (se 3 (by rfl) ⟨2806997, by rfl⟩ : syracuseStep 14970653 = 5613995) B5613995
theorem B2076575 : Blo 1383511 2076575 := bstep (se 1 (by rfl) ⟨1557431, by rfl⟩ : syracuseStep 2076575 = 3114863) B3114863
theorem B3502075 : Blo 1383511 3502075 := bstep (se 1 (by rfl) ⟨2626556, by rfl⟩ : syracuseStep 3502075 = 5253113) B5253113
theorem B3502187 : Blo 1383511 3502187 := bstep (se 1 (by rfl) ⟨2626640, by rfl⟩ : syracuseStep 3502187 = 5253281) B5253281
theorem B3117239 : Blo 1383511 3117239 := bstep (se 1 (by rfl) ⟨2337929, by rfl⟩ : syracuseStep 3117239 = 4675859) B4675859
theorem B23654591 : Blo 1383511 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B7885025 : Blo 1383511 7885025 := bstep (se 2 (by rfl) ⟨2956884, by rfl⟩ : syracuseStep 7885025 = 5913769) B5913769
theorem B3117311 : Blo 1383511 3117311 := bstep (se 1 (by rfl) ⟨2337983, by rfl⟩ : syracuseStep 3117311 = 4675967) B4675967
theorem B5255711 : Blo 1383511 5255711 := bstep (se 1 (by rfl) ⟨3941783, by rfl⟩ : syracuseStep 5255711 = 7883567) B7883567
theorem B33698375 : Blo 1383511 33698375 := bstep (se 1 (by rfl) ⟨25273781, by rfl⟩ : syracuseStep 33698375 = 50547563) B50547563
theorem B242954923 : Blo 1383511 242954923 := bstep (se 1 (by rfl) ⟨182216192, by rfl⟩ : syracuseStep 242954923 = 364432385) B364432385
theorem B19968713 : Blo 1383511 19968713 := bstep (se 2 (by rfl) ⟨7488267, by rfl⟩ : syracuseStep 19968713 = 14976535) B14976535
theorem B25260943 : Blo 1383511 25260943 := bstep (se 1 (by rfl) ⟨18945707, by rfl⟩ : syracuseStep 25260943 = 37891415) B37891415
theorem B3945439 : Blo 1383511 3945439 := bstep (se 1 (by rfl) ⟨2959079, by rfl⟩ : syracuseStep 3945439 = 5918159) B5918159
theorem B2626823 : Blo 1383511 2626823 := bstep (se 1 (by rfl) ⟨1970117, by rfl⟩ : syracuseStep 2626823 = 3940235) B3940235
theorem B15766811 : Blo 1383511 15766811 := bstep (se 1 (by rfl) ⟨11825108, by rfl⟩ : syracuseStep 15766811 = 23650217) B23650217
theorem B11834747 : Blo 1383511 11834747 := bstep (se 1 (by rfl) ⟨8876060, by rfl⟩ : syracuseStep 11834747 = 17752121) B17752121
theorem B4675103 : Blo 1383511 4675103 := bstep (se 1 (by rfl) ⟨3506327, by rfl⟩ : syracuseStep 4675103 = 7012655) B7012655
theorem B7009901 : Blo 1383511 7009901 := bstep (se 3 (by rfl) ⟨1314356, by rfl⟩ : syracuseStep 7009901 = 2628713) B2628713
theorem B1578791 : Blo 1383511 1578791 := bstep (se 1 (by rfl) ⟨1184093, by rfl⟩ : syracuseStep 1578791 = 2368187) B2368187
theorem B15775559 : Blo 1383511 15775559 := bstep (se 1 (by rfl) ⟨11831669, by rfl⟩ : syracuseStep 15775559 = 23663339) B23663339
theorem B3504343 : Blo 1383511 3504343 := bstep (se 1 (by rfl) ⟨2628257, by rfl⟩ : syracuseStep 3504343 = 5256515) B5256515
theorem B22460651 : Blo 1383511 22460651 := bstep (se 1 (by rfl) ⟨16845488, by rfl⟩ : syracuseStep 22460651 = 33690977) B33690977
theorem B2808361 : Blo 1383511 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B4987439 : Blo 1383511 4987439 := bstep (se 1 (by rfl) ⟨3740579, by rfl⟩ : syracuseStep 4987439 = 7481159) B7481159
theorem B34159229 : Blo 1383511 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B13302791 : Blo 1383511 13302791 := bstep (se 1 (by rfl) ⟨9977093, by rfl⟩ : syracuseStep 13302791 = 19954187) B19954187
theorem B2956475 : Blo 1383511 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B3505427 : Blo 1383511 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B2628911 : Blo 1383511 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B1383839 : Blo 1383511 1383839 := bstep (se 1 (by rfl) ⟨1037879, by rfl⟩ : syracuseStep 1383839 = 2075759) B2075759
theorem B1383963 : Blo 1383511 1383963 := bstep (se 1 (by rfl) ⟨1037972, by rfl⟩ : syracuseStep 1383963 = 2075945) B2075945
theorem B3505801 : Blo 1383511 3505801 := bstep (se 2 (by rfl) ⟨1314675, by rfl⟩ : syracuseStep 3505801 = 2629351) B2629351
theorem B29941487 : Blo 1383511 29941487 := bstep (se 1 (by rfl) ⟨22456115, by rfl⟩ : syracuseStep 29941487 = 44912231) B44912231
theorem B3112991 : Blo 1383511 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B2334791 : Blo 1383511 2334791 := bstep (se 1 (by rfl) ⟨1751093, by rfl⟩ : syracuseStep 2334791 = 3502187) B3502187
theorem B15769727 : Blo 1383511 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B18956551 : Blo 1383511 18956551 := bstep (se 1 (by rfl) ⟨14217413, by rfl⟩ : syracuseStep 18956551 = 28434827) B28434827
theorem B13312475 : Blo 1383511 13312475 := bstep (se 1 (by rfl) ⟨9984356, by rfl⟩ : syracuseStep 13312475 = 19968713) B19968713
theorem B37880459 : Blo 1383511 37880459 := bstep (se 1 (by rfl) ⟨28410344, by rfl⟩ : syracuseStep 37880459 = 56820689) B56820689
theorem B3744481 : Blo 1383511 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B10511207 : Blo 1383511 10511207 := bstep (se 1 (by rfl) ⟨7883405, by rfl⟩ : syracuseStep 10511207 = 15766811) B15766811
theorem B3113855 : Blo 1383511 3113855 := bstep (se 1 (by rfl) ⟨2335391, by rfl⟩ : syracuseStep 3113855 = 4670783) B4670783
theorem B7889831 : Blo 1383511 7889831 := bstep (se 1 (by rfl) ⟨5917373, by rfl⟩ : syracuseStep 7889831 = 11834747) B11834747
theorem B3113963 : Blo 1383511 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B4670567 : Blo 1383511 4670567 := bstep (se 1 (by rfl) ⟨3502925, by rfl⟩ : syracuseStep 4670567 = 7005851) B7005851
theorem B3114143 : Blo 1383511 3114143 := bstep (se 1 (by rfl) ⟨2335607, by rfl⟩ : syracuseStep 3114143 = 4671215) B4671215
theorem B7013627 : Blo 1383511 7013627 := bstep (se 1 (by rfl) ⟨5260220, by rfl⟩ : syracuseStep 7013627 = 10520441) B10520441
theorem B5260585 : Blo 1383511 5260585 := bstep (se 2 (by rfl) ⟨1972719, by rfl⟩ : syracuseStep 5260585 = 3945439) B3945439
theorem B2336951 : Blo 1383511 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B3115241 : Blo 1383511 3115241 := bstep (se 2 (by rfl) ⟨1168215, by rfl⟩ : syracuseStep 3115241 = 2336431) B2336431
theorem B9980435 : Blo 1383511 9980435 := bstep (se 1 (by rfl) ⟨7485326, by rfl⟩ : syracuseStep 9980435 = 14970653) B14970653
theorem B22440671 : Blo 1383511 22440671 := bstep (se 1 (by rfl) ⟨16830503, by rfl⟩ : syracuseStep 22440671 = 33661007) B33661007
theorem B2337511 : Blo 1383511 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B8415983 : Blo 1383511 8415983 := bstep (se 1 (by rfl) ⟨6311987, by rfl⟩ : syracuseStep 8415983 = 12623975) B12623975
theorem B2337545 : Blo 1383511 2337545 := bstep (se 2 (by rfl) ⟨876579, by rfl⟩ : syracuseStep 2337545 = 1753159) B1753159
theorem B4672457 : Blo 1383511 4672457 := bstep (se 2 (by rfl) ⟨1752171, by rfl⟩ : syracuseStep 4672457 = 3504343) B3504343
theorem B22465583 : Blo 1383511 22465583 := bstep (se 1 (by rfl) ⟨16849187, by rfl⟩ : syracuseStep 22465583 = 33698375) B33698375
theorem B5254571 : Blo 1383511 5254571 := bstep (se 1 (by rfl) ⟨3940928, by rfl⟩ : syracuseStep 5254571 = 7881857) B7881857
theorem B323939897 : Blo 1383511 323939897 := bstep (se 2 (by rfl) ⟨121477461, by rfl⟩ : syracuseStep 323939897 = 242954923) B242954923
theorem B3116735 : Blo 1383511 3116735 := bstep (se 1 (by rfl) ⟨2337551, by rfl⟩ : syracuseStep 3116735 = 4675103) B4675103
theorem B2076383 : Blo 1383511 2076383 := bstep (se 1 (by rfl) ⟨1557287, by rfl⟩ : syracuseStep 2076383 = 3114575) B3114575
theorem B4673267 : Blo 1383511 4673267 := bstep (se 1 (by rfl) ⟨3504950, by rfl⟩ : syracuseStep 4673267 = 7009901) B7009901
theorem B2076443 : Blo 1383511 2076443 := bstep (se 1 (by rfl) ⟨1557332, by rfl⟩ : syracuseStep 2076443 = 3114665) B3114665
theorem B33681257 : Blo 1383511 33681257 := bstep (se 2 (by rfl) ⟨12630471, by rfl⟩ : syracuseStep 33681257 = 25260943) B25260943
theorem B2076767 : Blo 1383511 2076767 := bstep (se 1 (by rfl) ⟨1557575, by rfl⟩ : syracuseStep 2076767 = 3115151) B3115151
theorem B2076809 : Blo 1383511 2076809 := bstep (se 2 (by rfl) ⟨778803, by rfl⟩ : syracuseStep 2076809 = 1557607) B1557607
theorem B2076839 : Blo 1383511 2076839 := bstep (se 1 (by rfl) ⟨1557629, by rfl⟩ : syracuseStep 2076839 = 3115259) B3115259
theorem B2076863 : Blo 1383511 2076863 := bstep (se 1 (by rfl) ⟨1557647, by rfl⟩ : syracuseStep 2076863 = 3115295) B3115295
theorem B13308137 : Blo 1383511 13308137 := bstep (se 2 (by rfl) ⟨4990551, by rfl⟩ : syracuseStep 13308137 = 9981103) B9981103
theorem B5255543 : Blo 1383511 5255543 := bstep (se 1 (by rfl) ⟨3941657, by rfl⟩ : syracuseStep 5255543 = 7883315) B7883315
theorem B8868527 : Blo 1383511 8868527 := bstep (se 1 (by rfl) ⟨6651395, by rfl⟩ : syracuseStep 8868527 = 13302791) B13302791
theorem B1970983 : Blo 1383511 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B4674401 : Blo 1383511 4674401 := bstep (se 2 (by rfl) ⟨1752900, by rfl⟩ : syracuseStep 4674401 = 3505801) B3505801
theorem B4207481 : Blo 1383511 4207481 := bstep (se 2 (by rfl) ⟨1577805, by rfl⟩ : syracuseStep 4207481 = 3155611) B3155611
theorem B2077631 : Blo 1383511 2077631 := bstep (se 1 (by rfl) ⟨1558223, by rfl⟩ : syracuseStep 2077631 = 3116447) B3116447
theorem B2995177 : Blo 1383511 2995177 := bstep (se 2 (by rfl) ⟨1123191, by rfl⟩ : syracuseStep 2995177 = 2246383) B2246383
theorem B2077673 : Blo 1383511 2077673 := bstep (se 2 (by rfl) ⟨779127, by rfl⟩ : syracuseStep 2077673 = 1558255) B1558255
theorem B19960991 : Blo 1383511 19960991 := bstep (se 1 (by rfl) ⟨14970743, by rfl⟩ : syracuseStep 19960991 = 29941487) B29941487
theorem B2078159 : Blo 1383511 2078159 := bstep (se 1 (by rfl) ⟨1558619, by rfl⟩ : syracuseStep 2078159 = 3117239) B3117239
theorem B5256683 : Blo 1383511 5256683 := bstep (se 1 (by rfl) ⟨3942512, by rfl⟩ : syracuseStep 5256683 = 7885025) B7885025
theorem B2078207 : Blo 1383511 2078207 := bstep (se 1 (by rfl) ⟨1558655, by rfl⟩ : syracuseStep 2078207 = 3117311) B3117311
theorem B3503807 : Blo 1383511 3503807 := bstep (se 1 (by rfl) ⟨2627855, by rfl⟩ : syracuseStep 3503807 = 5255711) B5255711
theorem B26957657 : Blo 1383511 26957657 := bstep (se 2 (by rfl) ⟨10109121, by rfl⟩ : syracuseStep 26957657 = 20218243) B20218243
theorem B1751215 : Blo 1383511 1751215 := bstep (se 1 (by rfl) ⟨1313411, by rfl⟩ : syracuseStep 1751215 = 2626823) B2626823
theorem B4669433 : Blo 1383511 4669433 := bstep (se 2 (by rfl) ⟨1751037, by rfl⟩ : syracuseStep 4669433 = 3502075) B3502075
theorem B10517039 : Blo 1383511 10517039 := bstep (se 1 (by rfl) ⟨7887779, by rfl⟩ : syracuseStep 10517039 = 15775559) B15775559
theorem B14973767 : Blo 1383511 14973767 := bstep (se 1 (by rfl) ⟨11230325, by rfl⟩ : syracuseStep 14973767 = 22460651) B22460651
theorem B3324959 : Blo 1383511 3324959 := bstep (se 1 (by rfl) ⟨2493719, by rfl⟩ : syracuseStep 3324959 = 4987439) B4987439
theorem B22772819 : Blo 1383511 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B1383679 : Blo 1383511 1383679 := bstep (se 1 (by rfl) ⟨1037759, by rfl⟩ : syracuseStep 1383679 = 2075519) B2075519
theorem B4210109 : Blo 1383511 4210109 := bstep (se 3 (by rfl) ⟨789395, by rfl⟩ : syracuseStep 4210109 = 1578791) B1578791
theorem B1383903 : Blo 1383511 1383903 := bstep (se 1 (by rfl) ⟨1037927, by rfl⟩ : syracuseStep 1383903 = 2075855) B2075855
theorem B1752607 : Blo 1383511 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B3939995 : Blo 1383511 3939995 := bstep (se 1 (by rfl) ⟨2954996, by rfl⟩ : syracuseStep 3939995 = 5909993) B5909993
theorem B1384383 : Blo 1383511 1384383 := bstep (se 1 (by rfl) ⟨1038287, by rfl⟩ : syracuseStep 1384383 = 2076575) B2076575
theorem B1556527 : Blo 1383511 1556527 := bstep (se 1 (by rfl) ⟨1167395, by rfl⟩ : syracuseStep 1556527 = 2334791) B2334791
theorem B1384511 : Blo 1383511 1384511 := bstep (se 1 (by rfl) ⟨1038383, by rfl⟩ : syracuseStep 1384511 = 2076767) B2076767
theorem B1384539 : Blo 1383511 1384539 := bstep (se 1 (by rfl) ⟨1038404, by rfl⟩ : syracuseStep 1384539 = 2076809) B2076809
theorem B1384559 : Blo 1383511 1384559 := bstep (se 1 (by rfl) ⟨1038419, by rfl⟩ : syracuseStep 1384559 = 2076839) B2076839
theorem B1384575 : Blo 1383511 1384575 := bstep (se 1 (by rfl) ⟨1038431, by rfl⟩ : syracuseStep 1384575 = 2076863) B2076863
theorem B8872091 : Blo 1383511 8872091 := bstep (se 1 (by rfl) ⟨6654068, by rfl⟩ : syracuseStep 8872091 = 13308137) B13308137
theorem B2334953 : Blo 1383511 2334953 := bstep (se 2 (by rfl) ⟨875607, by rfl⟩ : syracuseStep 2334953 = 1751215) B1751215
theorem B5259887 : Blo 1383511 5259887 := bstep (se 1 (by rfl) ⟨3944915, by rfl⟩ : syracuseStep 5259887 = 7889831) B7889831
theorem B1385087 : Blo 1383511 1385087 := bstep (se 1 (by rfl) ⟨1038815, by rfl⟩ : syracuseStep 1385087 = 2077631) B2077631
theorem B1385115 : Blo 1383511 1385115 := bstep (se 1 (by rfl) ⟨1038836, by rfl⟩ : syracuseStep 1385115 = 2077673) B2077673
theorem B3113711 : Blo 1383511 3113711 := bstep (se 1 (by rfl) ⟨2335283, by rfl⟩ : syracuseStep 3113711 = 4670567) B4670567
theorem B1385439 : Blo 1383511 1385439 := bstep (se 1 (by rfl) ⟨1039079, by rfl⟩ : syracuseStep 1385439 = 2078159) B2078159
theorem B1385471 : Blo 1383511 1385471 := bstep (se 1 (by rfl) ⟨1039103, by rfl⟩ : syracuseStep 1385471 = 2078207) B2078207
theorem B2335871 : Blo 1383511 2335871 := bstep (se 1 (by rfl) ⟨1751903, by rfl⟩ : syracuseStep 2335871 = 3503807) B3503807
theorem B1557967 : Blo 1383511 1557967 := bstep (se 1 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 1557967 = 2336951) B2336951
theorem B7014113 : Blo 1383511 7014113 := bstep (se 2 (by rfl) ⟨2630292, by rfl⟩ : syracuseStep 7014113 = 5260585) B5260585
theorem B14960447 : Blo 1383511 14960447 := bstep (se 1 (by rfl) ⟨11220335, by rfl⟩ : syracuseStep 14960447 = 22440671) B22440671
theorem B1558363 : Blo 1383511 1558363 := bstep (se 1 (by rfl) ⟨1168772, by rfl⟩ : syracuseStep 1558363 = 2337545) B2337545
theorem B3114971 : Blo 1383511 3114971 := bstep (se 1 (by rfl) ⟨2336228, by rfl⟩ : syracuseStep 3114971 = 4672457) B4672457
theorem B14977055 : Blo 1383511 14977055 := bstep (se 1 (by rfl) ⟨11232791, by rfl⟩ : syracuseStep 14977055 = 22465583) B22465583
theorem B2336809 : Blo 1383511 2336809 := bstep (se 2 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 2336809 = 1752607) B1752607
theorem B15181879 : Blo 1383511 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B71887085 : Blo 1383511 71887085 := bstep (se 3 (by rfl) ⟨13478828, by rfl⟩ : syracuseStep 71887085 = 26957657) B26957657
theorem B215959931 : Blo 1383511 215959931 := bstep (se 1 (by rfl) ⟨161969948, by rfl⟩ : syracuseStep 215959931 = 323939897) B323939897
theorem B3115511 : Blo 1383511 3115511 := bstep (se 1 (by rfl) ⟨2336633, by rfl⟩ : syracuseStep 3115511 = 4673267) B4673267
theorem B2075327 : Blo 1383511 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B10513151 : Blo 1383511 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B8874983 : Blo 1383511 8874983 := bstep (se 1 (by rfl) ⟨6656237, by rfl⟩ : syracuseStep 8874983 = 13312475) B13312475
theorem B25275401 : Blo 1383511 25275401 := bstep (se 2 (by rfl) ⟨9478275, by rfl⟩ : syracuseStep 25275401 = 18956551) B18956551
theorem B3116267 : Blo 1383511 3116267 := bstep (se 1 (by rfl) ⟨2337200, by rfl⟩ : syracuseStep 3116267 = 4674401) B4674401
theorem B7007471 : Blo 1383511 7007471 := bstep (se 1 (by rfl) ⟨5255603, by rfl⟩ : syracuseStep 7007471 = 10511207) B10511207
theorem B2804987 : Blo 1383511 2804987 := bstep (se 1 (by rfl) ⟨2103740, by rfl⟩ : syracuseStep 2804987 = 4207481) B4207481
theorem B2075903 : Blo 1383511 2075903 := bstep (se 1 (by rfl) ⟨1556927, by rfl⟩ : syracuseStep 2075903 = 3113855) B3113855
theorem B2075975 : Blo 1383511 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B2076095 : Blo 1383511 2076095 := bstep (se 1 (by rfl) ⟨1557071, by rfl⟩ : syracuseStep 2076095 = 3114143) B3114143
theorem B13307327 : Blo 1383511 13307327 := bstep (se 1 (by rfl) ⟨9980495, by rfl⟩ : syracuseStep 13307327 = 19960991) B19960991
theorem B4992641 : Blo 1383511 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B3116681 : Blo 1383511 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B3993569 : Blo 1383511 3993569 := bstep (se 2 (by rfl) ⟨1497588, by rfl⟩ : syracuseStep 3993569 = 2995177) B2995177
theorem B2076827 : Blo 1383511 2076827 := bstep (se 1 (by rfl) ⟨1557620, by rfl⟩ : syracuseStep 2076827 = 3115241) B3115241
theorem B9982511 : Blo 1383511 9982511 := bstep (se 1 (by rfl) ⟨7486883, by rfl⟩ : syracuseStep 9982511 = 14973767) B14973767
theorem B2216639 : Blo 1383511 2216639 := bstep (se 1 (by rfl) ⟨1662479, by rfl⟩ : syracuseStep 2216639 = 3324959) B3324959
theorem B3503047 : Blo 1383511 3503047 := bstep (se 1 (by rfl) ⟨2627285, by rfl⟩ : syracuseStep 3503047 = 5254571) B5254571
theorem B2806739 : Blo 1383511 2806739 := bstep (se 1 (by rfl) ⟨2105054, by rfl⟩ : syracuseStep 2806739 = 4210109) B4210109
theorem B2626663 : Blo 1383511 2626663 := bstep (se 1 (by rfl) ⟨1969997, by rfl⟩ : syracuseStep 2626663 = 3939995) B3939995
theorem B2077823 : Blo 1383511 2077823 := bstep (se 1 (by rfl) ⟨1558367, by rfl⟩ : syracuseStep 2077823 = 3116735) B3116735
theorem B3503695 : Blo 1383511 3503695 := bstep (se 1 (by rfl) ⟨2627771, by rfl⟩ : syracuseStep 3503695 = 5255543) B5255543
theorem B25253639 : Blo 1383511 25253639 := bstep (se 1 (by rfl) ⟨18940229, by rfl⟩ : syracuseStep 25253639 = 37880459) B37880459
theorem B5912351 : Blo 1383511 5912351 := bstep (se 1 (by rfl) ⟨4434263, by rfl⟩ : syracuseStep 5912351 = 8868527) B8868527
theorem B4675751 : Blo 1383511 4675751 := bstep (se 1 (by rfl) ⟨3506813, by rfl⟩ : syracuseStep 4675751 = 7013627) B7013627
theorem B3504455 : Blo 1383511 3504455 := bstep (se 1 (by rfl) ⟨2628341, by rfl⟩ : syracuseStep 3504455 = 5256683) B5256683
theorem B2627977 : Blo 1383511 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B26614493 : Blo 1383511 26614493 := bstep (se 3 (by rfl) ⟨4990217, by rfl⟩ : syracuseStep 26614493 = 9980435) B9980435
theorem B7011359 : Blo 1383511 7011359 := bstep (se 1 (by rfl) ⟨5258519, by rfl⟩ : syracuseStep 7011359 = 10517039) B10517039
theorem B5610655 : Blo 1383511 5610655 := bstep (se 1 (by rfl) ⟨4207991, by rfl⟩ : syracuseStep 5610655 = 8415983) B8415983
theorem B1384255 : Blo 1383511 1384255 := bstep (se 1 (by rfl) ⟨1038191, by rfl⟩ : syracuseStep 1384255 = 2076383) B2076383
theorem B1384295 : Blo 1383511 1384295 := bstep (se 1 (by rfl) ⟨1038221, by rfl⟩ : syracuseStep 1384295 = 2076443) B2076443
theorem B22454171 : Blo 1383511 22454171 := bstep (se 1 (by rfl) ⟨16840628, by rfl⟩ : syracuseStep 22454171 = 33681257) B33681257
theorem B3112955 : Blo 1383511 3112955 := bstep (se 1 (by rfl) ⟨2334716, by rfl⟩ : syracuseStep 3112955 = 4669433) B4669433
theorem B20242505 : Blo 1383511 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B1384551 : Blo 1383511 1384551 := bstep (se 1 (by rfl) ⟨1038413, by rfl⟩ : syracuseStep 1384551 = 2076827) B2076827
theorem B5914727 : Blo 1383511 5914727 := bstep (se 1 (by rfl) ⟨4436045, by rfl⟩ : syracuseStep 5914727 = 8872091) B8872091
theorem B1556635 : Blo 1383511 1556635 := bstep (se 1 (by rfl) ⟨1167476, by rfl⟩ : syracuseStep 1556635 = 2334953) B2334953
theorem B3506591 : Blo 1383511 3506591 := bstep (se 1 (by rfl) ⟨2629943, by rfl⟩ : syracuseStep 3506591 = 5259887) B5259887
theorem B7479965 : Blo 1383511 7479965 := bstep (se 3 (by rfl) ⟨1402493, by rfl⟩ : syracuseStep 7479965 = 2804987) B2804987
theorem B1557247 : Blo 1383511 1557247 := bstep (se 1 (by rfl) ⟨1167935, by rfl⟩ : syracuseStep 1557247 = 2335871) B2335871
theorem B1385215 : Blo 1383511 1385215 := bstep (se 1 (by rfl) ⟨1038911, by rfl⟩ : syracuseStep 1385215 = 2077823) B2077823
theorem B16835759 : Blo 1383511 16835759 := bstep (se 1 (by rfl) ⟨12626819, by rfl⟩ : syracuseStep 16835759 = 25253639) B25253639
theorem B3941567 : Blo 1383511 3941567 := bstep (se 1 (by rfl) ⟨2956175, by rfl⟩ : syracuseStep 3941567 = 5912351) B5912351
theorem B4670729 : Blo 1383511 4670729 := bstep (se 2 (by rfl) ⟨1751523, by rfl⟩ : syracuseStep 4670729 = 3503047) B3503047
theorem B47924723 : Blo 1383511 47924723 := bstep (se 1 (by rfl) ⟨35943542, by rfl⟩ : syracuseStep 47924723 = 71887085) B71887085
theorem B7480873 : Blo 1383511 7480873 := bstep (se 2 (by rfl) ⟨2805327, by rfl⟩ : syracuseStep 7480873 = 5610655) B5610655
theorem B2336303 : Blo 1383511 2336303 := bstep (se 1 (by rfl) ⟨1752227, by rfl⟩ : syracuseStep 2336303 = 3504455) B3504455
theorem B5916655 : Blo 1383511 5916655 := bstep (se 1 (by rfl) ⟨4437491, by rfl⟩ : syracuseStep 5916655 = 8874983) B8874983
theorem B4671593 : Blo 1383511 4671593 := bstep (se 2 (by rfl) ⟨1751847, by rfl⟩ : syracuseStep 4671593 = 3503695) B3503695
theorem B4671647 : Blo 1383511 4671647 := bstep (se 1 (by rfl) ⟨3503735, by rfl⟩ : syracuseStep 4671647 = 7007471) B7007471
theorem B3328427 : Blo 1383511 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B14969447 : Blo 1383511 14969447 := bstep (se 1 (by rfl) ⟨11227085, by rfl⟩ : syracuseStep 14969447 = 22454171) B22454171
theorem B2075303 : Blo 1383511 2075303 := bstep (se 1 (by rfl) ⟨1556477, by rfl⟩ : syracuseStep 2075303 = 3112955) B3112955
theorem B3115745 : Blo 1383511 3115745 := bstep (se 2 (by rfl) ⟨1168404, by rfl⟩ : syracuseStep 3115745 = 2336809) B2336809
theorem B2075369 : Blo 1383511 2075369 := bstep (se 2 (by rfl) ⟨778263, by rfl⟩ : syracuseStep 2075369 = 1556527) B1556527
theorem B6655007 : Blo 1383511 6655007 := bstep (se 1 (by rfl) ⟨4991255, by rfl⟩ : syracuseStep 6655007 = 9982511) B9982511
theorem B1477759 : Blo 1383511 1477759 := bstep (se 1 (by rfl) ⟨1108319, by rfl⟩ : syracuseStep 1477759 = 2216639) B2216639
theorem B2075807 : Blo 1383511 2075807 := bstep (se 1 (by rfl) ⟨1556855, by rfl⟩ : syracuseStep 2075807 = 3113711) B3113711
theorem B1871159 : Blo 1383511 1871159 := bstep (se 1 (by rfl) ⟨1403369, by rfl⟩ : syracuseStep 1871159 = 2806739) B2806739
theorem B9973631 : Blo 1383511 9973631 := bstep (se 1 (by rfl) ⟨7480223, by rfl⟩ : syracuseStep 9973631 = 14960447) B14960447
theorem B2076647 : Blo 1383511 2076647 := bstep (se 1 (by rfl) ⟨1557485, by rfl⟩ : syracuseStep 2076647 = 3114971) B3114971
theorem B3117167 : Blo 1383511 3117167 := bstep (se 1 (by rfl) ⟨2337875, by rfl⟩ : syracuseStep 3117167 = 4675751) B4675751
theorem B3502217 : Blo 1383511 3502217 := bstep (se 2 (by rfl) ⟨1313331, by rfl⟩ : syracuseStep 3502217 = 2626663) B2626663
theorem B2077007 : Blo 1383511 2077007 := bstep (se 1 (by rfl) ⟨1557755, by rfl⟩ : syracuseStep 2077007 = 3115511) B3115511
theorem B7008767 : Blo 1383511 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B2077289 : Blo 1383511 2077289 := bstep (se 2 (by rfl) ⟨778983, by rfl⟩ : syracuseStep 2077289 = 1557967) B1557967
theorem B4674239 : Blo 1383511 4674239 := bstep (se 1 (by rfl) ⟨3505679, by rfl⟩ : syracuseStep 4674239 = 7011359) B7011359
theorem B2077511 : Blo 1383511 2077511 := bstep (se 1 (by rfl) ⟨1558133, by rfl⟩ : syracuseStep 2077511 = 3116267) B3116267
theorem B2077787 : Blo 1383511 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B2077817 : Blo 1383511 2077817 := bstep (se 2 (by rfl) ⟨779181, by rfl⟩ : syracuseStep 2077817 = 1558363) B1558363
theorem B3503969 : Blo 1383511 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B4676075 : Blo 1383511 4676075 := bstep (se 1 (by rfl) ⟨3507056, by rfl⟩ : syracuseStep 4676075 = 7014113) B7014113
theorem B9984703 : Blo 1383511 9984703 := bstep (se 1 (by rfl) ⟨7488527, by rfl⟩ : syracuseStep 9984703 = 14977055) B14977055
theorem B143973287 : Blo 1383511 143973287 := bstep (se 1 (by rfl) ⟨107979965, by rfl⟩ : syracuseStep 143973287 = 215959931) B215959931
theorem B1383551 : Blo 1383511 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B17742995 : Blo 1383511 17742995 := bstep (se 1 (by rfl) ⟨13307246, by rfl⟩ : syracuseStep 17742995 = 26614493) B26614493
theorem B16850267 : Blo 1383511 16850267 := bstep (se 1 (by rfl) ⟨12637700, by rfl⟩ : syracuseStep 16850267 = 25275401) B25275401
theorem B1383935 : Blo 1383511 1383935 := bstep (se 1 (by rfl) ⟨1037951, by rfl⟩ : syracuseStep 1383935 = 2075903) B2075903
theorem B1383983 : Blo 1383511 1383983 := bstep (se 1 (by rfl) ⟨1037987, by rfl⟩ : syracuseStep 1383983 = 2075975) B2075975
theorem B1384063 : Blo 1383511 1384063 := bstep (se 1 (by rfl) ⟨1038047, by rfl⟩ : syracuseStep 1384063 = 2076095) B2076095
theorem B8871551 : Blo 1383511 8871551 := bstep (se 1 (by rfl) ⟨6653663, by rfl⟩ : syracuseStep 8871551 = 13307327) B13307327
theorem B2662379 : Blo 1383511 2662379 := bstep (se 1 (by rfl) ⟨1996784, by rfl⟩ : syracuseStep 2662379 = 3993569) B3993569
theorem B2334811 : Blo 1383511 2334811 := bstep (se 1 (by rfl) ⟨1751108, by rfl⟩ : syracuseStep 2334811 = 3502217) B3502217
theorem B1384671 : Blo 1383511 1384671 := bstep (se 1 (by rfl) ⟨1038503, by rfl⟩ : syracuseStep 1384671 = 2077007) B2077007
theorem B1384859 : Blo 1383511 1384859 := bstep (se 1 (by rfl) ⟨1038644, by rfl⟩ : syracuseStep 1384859 = 2077289) B2077289
theorem B1385007 : Blo 1383511 1385007 := bstep (se 1 (by rfl) ⟨1038755, by rfl⟩ : syracuseStep 1385007 = 2077511) B2077511
theorem B1385191 : Blo 1383511 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B1385211 : Blo 1383511 1385211 := bstep (se 1 (by rfl) ⟨1038908, by rfl⟩ : syracuseStep 1385211 = 2077817) B2077817
theorem B11223839 : Blo 1383511 11223839 := bstep (se 1 (by rfl) ⟨8417879, by rfl⟩ : syracuseStep 11223839 = 16835759) B16835759
theorem B4989757 : Blo 1383511 4989757 := bstep (se 3 (by rfl) ⟨935579, by rfl⟩ : syracuseStep 4989757 = 1871159) B1871159
theorem B3113819 : Blo 1383511 3113819 := bstep (se 1 (by rfl) ⟨2335364, by rfl⟩ : syracuseStep 3113819 = 4670729) B4670729
theorem B13312937 : Blo 1383511 13312937 := bstep (se 2 (by rfl) ⟨4992351, by rfl⟩ : syracuseStep 13312937 = 9984703) B9984703
theorem B31949815 : Blo 1383511 31949815 := bstep (se 1 (by rfl) ⟨23962361, by rfl⟩ : syracuseStep 31949815 = 47924723) B47924723
theorem B1557535 : Blo 1383511 1557535 := bstep (se 1 (by rfl) ⟨1168151, by rfl⟩ : syracuseStep 1557535 = 2336303) B2336303
theorem B2335979 : Blo 1383511 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B3114395 : Blo 1383511 3114395 := bstep (se 1 (by rfl) ⟨2335796, by rfl⟩ : syracuseStep 3114395 = 4671593) B4671593
theorem B3114431 : Blo 1383511 3114431 := bstep (se 1 (by rfl) ⟨2335823, by rfl⟩ : syracuseStep 3114431 = 4671647) B4671647
theorem B9979631 : Blo 1383511 9979631 := bstep (se 1 (by rfl) ⟨7484723, by rfl⟩ : syracuseStep 9979631 = 14969447) B14969447
theorem B11233511 : Blo 1383511 11233511 := bstep (se 1 (by rfl) ⟨8425133, by rfl⟩ : syracuseStep 11233511 = 16850267) B16850267
theorem B3943151 : Blo 1383511 3943151 := bstep (se 1 (by rfl) ⟨2957363, by rfl⟩ : syracuseStep 3943151 = 5914727) B5914727
theorem B17746685 : Blo 1383511 17746685 := bstep (se 3 (by rfl) ⟨3327503, by rfl⟩ : syracuseStep 17746685 = 6655007) B6655007
theorem B53980013 : Blo 1383511 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B2075513 : Blo 1383511 2075513 := bstep (se 2 (by rfl) ⟨778317, by rfl⟩ : syracuseStep 2075513 = 1556635) B1556635
theorem B2337727 : Blo 1383511 2337727 := bstep (se 1 (by rfl) ⟨1753295, by rfl⟩ : syracuseStep 2337727 = 3506591) B3506591
theorem B4672511 : Blo 1383511 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B3116159 : Blo 1383511 3116159 := bstep (se 1 (by rfl) ⟨2337119, by rfl⟩ : syracuseStep 3116159 = 4674239) B4674239
theorem B2076329 : Blo 1383511 2076329 := bstep (se 2 (by rfl) ⟨778623, by rfl⟩ : syracuseStep 2076329 = 1557247) B1557247
theorem B1970345 : Blo 1383511 1970345 := bstep (se 2 (by rfl) ⟨738879, by rfl⟩ : syracuseStep 1970345 = 1477759) B1477759
theorem B3117383 : Blo 1383511 3117383 := bstep (se 1 (by rfl) ⟨2338037, by rfl⟩ : syracuseStep 3117383 = 4676075) B4676075
theorem B2077163 : Blo 1383511 2077163 := bstep (se 1 (by rfl) ⟨1557872, by rfl⟩ : syracuseStep 2077163 = 3115745) B3115745
theorem B95982191 : Blo 1383511 95982191 := bstep (se 1 (by rfl) ⟨71986643, by rfl⟩ : syracuseStep 95982191 = 143973287) B143973287
theorem B9974497 : Blo 1383511 9974497 := bstep (se 2 (by rfl) ⟨3740436, by rfl⟩ : syracuseStep 9974497 = 7480873) B7480873
theorem B26596349 : Blo 1383511 26596349 := bstep (se 3 (by rfl) ⟨4986815, by rfl⟩ : syracuseStep 26596349 = 9973631) B9973631
theorem B1774919 : Blo 1383511 1774919 := bstep (se 1 (by rfl) ⟨1331189, by rfl⟩ : syracuseStep 1774919 = 2662379) B2662379
theorem B2078111 : Blo 1383511 2078111 := bstep (se 1 (by rfl) ⟨1558583, by rfl⟩ : syracuseStep 2078111 = 3117167) B3117167
theorem B4986643 : Blo 1383511 4986643 := bstep (se 1 (by rfl) ⟨3739982, by rfl⟩ : syracuseStep 4986643 = 7479965) B7479965
theorem B2627711 : Blo 1383511 2627711 := bstep (se 1 (by rfl) ⟨1970783, by rfl⟩ : syracuseStep 2627711 = 3941567) B3941567
theorem B2218951 : Blo 1383511 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1383535 : Blo 1383511 1383535 := bstep (se 1 (by rfl) ⟨1037651, by rfl⟩ : syracuseStep 1383535 = 2075303) B2075303
theorem B1383579 : Blo 1383511 1383579 := bstep (se 1 (by rfl) ⟨1037684, by rfl⟩ : syracuseStep 1383579 = 2075369) B2075369
theorem B11828663 : Blo 1383511 11828663 := bstep (se 1 (by rfl) ⟨8871497, by rfl⟩ : syracuseStep 11828663 = 17742995) B17742995
theorem B1383871 : Blo 1383511 1383871 := bstep (se 1 (by rfl) ⟨1037903, by rfl⟩ : syracuseStep 1383871 = 2075807) B2075807
theorem B5914367 : Blo 1383511 5914367 := bstep (se 1 (by rfl) ⟨4435775, by rfl⟩ : syracuseStep 5914367 = 8871551) B8871551
theorem B7888873 : Blo 1383511 7888873 := bstep (se 2 (by rfl) ⟨2958327, by rfl⟩ : syracuseStep 7888873 = 5916655) B5916655
theorem B1384431 : Blo 1383511 1384431 := bstep (se 1 (by rfl) ⟨1038323, by rfl⟩ : syracuseStep 1384431 = 2076647) B2076647
theorem B3113081 : Blo 1383511 3113081 := bstep (se 2 (by rfl) ⟨1167405, by rfl⟩ : syracuseStep 3113081 = 2334811) B2334811
theorem B1384775 : Blo 1383511 1384775 := bstep (se 1 (by rfl) ⟨1038581, by rfl⟩ : syracuseStep 1384775 = 2077163) B2077163
theorem B63988127 : Blo 1383511 63988127 := bstep (se 1 (by rfl) ⟨47991095, by rfl⟩ : syracuseStep 63988127 = 95982191) B95982191
theorem B1557319 : Blo 1383511 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B1385407 : Blo 1383511 1385407 := bstep (se 1 (by rfl) ⟨1039055, by rfl⟩ : syracuseStep 1385407 = 2078111) B2078111
theorem B6653009 : Blo 1383511 6653009 := bstep (se 2 (by rfl) ⟨2494878, by rfl⟩ : syracuseStep 6653009 = 4989757) B4989757
theorem B6653087 : Blo 1383511 6653087 := bstep (se 1 (by rfl) ⟨4989815, by rfl⟩ : syracuseStep 6653087 = 9979631) B9979631
theorem B2958601 : Blo 1383511 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B42599753 : Blo 1383511 42599753 := bstep (se 2 (by rfl) ⟨15974907, by rfl⟩ : syracuseStep 42599753 = 31949815) B31949815
theorem B7489007 : Blo 1383511 7489007 := bstep (se 1 (by rfl) ⟨5616755, by rfl⟩ : syracuseStep 7489007 = 11233511) B11233511
theorem B11831123 : Blo 1383511 11831123 := bstep (se 1 (by rfl) ⟨8873342, by rfl⟩ : syracuseStep 11831123 = 17746685) B17746685
theorem B3115007 : Blo 1383511 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B3942911 : Blo 1383511 3942911 := bstep (se 1 (by rfl) ⟨2957183, by rfl⟩ : syracuseStep 3942911 = 5914367) B5914367
theorem B5254253 : Blo 1383511 5254253 := bstep (se 3 (by rfl) ⟨985172, by rfl⟩ : syracuseStep 5254253 = 1970345) B1970345
theorem B7482559 : Blo 1383511 7482559 := bstep (se 1 (by rfl) ⟨5611919, by rfl⟩ : syracuseStep 7482559 = 11223839) B11223839
theorem B2075879 : Blo 1383511 2075879 := bstep (se 1 (by rfl) ⟨1556909, by rfl⟩ : syracuseStep 2075879 = 3113819) B3113819
theorem B8875291 : Blo 1383511 8875291 := bstep (se 1 (by rfl) ⟨6656468, by rfl⟩ : syracuseStep 8875291 = 13312937) B13312937
theorem B17730899 : Blo 1383511 17730899 := bstep (se 1 (by rfl) ⟨13298174, by rfl⟩ : syracuseStep 17730899 = 26596349) B26596349
theorem B2076263 : Blo 1383511 2076263 := bstep (se 1 (by rfl) ⟨1557197, by rfl⟩ : syracuseStep 2076263 = 3114395) B3114395
theorem B2076287 : Blo 1383511 2076287 := bstep (se 1 (by rfl) ⟨1557215, by rfl⟩ : syracuseStep 2076287 = 3114431) B3114431
theorem B13299329 : Blo 1383511 13299329 := bstep (se 2 (by rfl) ⟨4987248, by rfl⟩ : syracuseStep 13299329 = 9974497) B9974497
theorem B3116969 : Blo 1383511 3116969 := bstep (se 2 (by rfl) ⟨1168863, by rfl⟩ : syracuseStep 3116969 = 2337727) B2337727
theorem B2076713 : Blo 1383511 2076713 := bstep (se 2 (by rfl) ⟨778767, by rfl⟩ : syracuseStep 2076713 = 1557535) B1557535
theorem B2077439 : Blo 1383511 2077439 := bstep (se 1 (by rfl) ⟨1558079, by rfl⟩ : syracuseStep 2077439 = 3116159) B3116159
theorem B7885775 : Blo 1383511 7885775 := bstep (se 1 (by rfl) ⟨5914331, by rfl⟩ : syracuseStep 7885775 = 11828663) B11828663
theorem B6648857 : Blo 1383511 6648857 := bstep (se 2 (by rfl) ⟨2493321, by rfl⟩ : syracuseStep 6648857 = 4986643) B4986643
theorem B2078255 : Blo 1383511 2078255 := bstep (se 1 (by rfl) ⟨1558691, by rfl⟩ : syracuseStep 2078255 = 3117383) B3117383
theorem B4733117 : Blo 1383511 4733117 := bstep (se 3 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 4733117 = 1774919) B1774919
theorem B1751807 : Blo 1383511 1751807 := bstep (se 1 (by rfl) ⟨1313855, by rfl⟩ : syracuseStep 1751807 = 2627711) B2627711
theorem B2628767 : Blo 1383511 2628767 := bstep (se 1 (by rfl) ⟨1971575, by rfl⟩ : syracuseStep 2628767 = 3943151) B3943151
theorem B35986675 : Blo 1383511 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B1383675 : Blo 1383511 1383675 := bstep (se 1 (by rfl) ⟨1037756, by rfl⟩ : syracuseStep 1383675 = 2075513) B2075513
theorem B1384219 : Blo 1383511 1384219 := bstep (se 1 (by rfl) ⟨1038164, by rfl⟩ : syracuseStep 1384219 = 2076329) B2076329
theorem B10518497 : Blo 1383511 10518497 := bstep (se 2 (by rfl) ⟨3944436, by rfl⟩ : syracuseStep 10518497 = 7888873) B7888873
theorem B1384475 : Blo 1383511 1384475 := bstep (se 1 (by rfl) ⟨1038356, by rfl⟩ : syracuseStep 1384475 = 2076713) B2076713
theorem B1384959 : Blo 1383511 1384959 := bstep (se 1 (by rfl) ⟨1038719, by rfl⟩ : syracuseStep 1384959 = 2077439) B2077439
theorem B4432571 : Blo 1383511 4432571 := bstep (se 1 (by rfl) ⟨3324428, by rfl⟩ : syracuseStep 4432571 = 6648857) B6648857
theorem B1385503 : Blo 1383511 1385503 := bstep (se 1 (by rfl) ⟨1039127, by rfl⟩ : syracuseStep 1385503 = 2078255) B2078255
theorem B3155411 : Blo 1383511 3155411 := bstep (se 1 (by rfl) ⟨2366558, by rfl⟩ : syracuseStep 3155411 = 4733117) B4733117
theorem B47982233 : Blo 1383511 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B4671485 : Blo 1383511 4671485 := bstep (se 3 (by rfl) ⟨875903, by rfl⟩ : syracuseStep 4671485 = 1751807) B1751807
theorem B8866219 : Blo 1383511 8866219 := bstep (se 1 (by rfl) ⟨6649664, by rfl⟩ : syracuseStep 8866219 = 13299329) B13299329
theorem B2075387 : Blo 1383511 2075387 := bstep (se 1 (by rfl) ⟨1556540, by rfl⟩ : syracuseStep 2075387 = 3113081) B3113081
theorem B42658751 : Blo 1383511 42658751 := bstep (se 1 (by rfl) ⟨31994063, by rfl⟩ : syracuseStep 42658751 = 63988127) B63988127
theorem B4435339 : Blo 1383511 4435339 := bstep (se 1 (by rfl) ⟨3326504, by rfl⟩ : syracuseStep 4435339 = 6653009) B6653009
theorem B4435391 : Blo 1383511 4435391 := bstep (se 1 (by rfl) ⟨3326543, by rfl⟩ : syracuseStep 4435391 = 6653087) B6653087
theorem B4992671 : Blo 1383511 4992671 := bstep (se 1 (by rfl) ⟨3744503, by rfl⟩ : syracuseStep 4992671 = 7489007) B7489007
theorem B2076425 : Blo 1383511 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B2076671 : Blo 1383511 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B3944801 : Blo 1383511 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B11833721 : Blo 1383511 11833721 := bstep (se 2 (by rfl) ⟨4437645, by rfl⟩ : syracuseStep 11833721 = 8875291) B8875291
theorem B3502835 : Blo 1383511 3502835 := bstep (se 1 (by rfl) ⟨2627126, by rfl⟩ : syracuseStep 3502835 = 5254253) B5254253
theorem B2077979 : Blo 1383511 2077979 := bstep (se 1 (by rfl) ⟨1558484, by rfl⟩ : syracuseStep 2077979 = 3116969) B3116969
theorem B5257183 : Blo 1383511 5257183 := bstep (se 1 (by rfl) ⟨3942887, by rfl⟩ : syracuseStep 5257183 = 7885775) B7885775
theorem B28399835 : Blo 1383511 28399835 := bstep (se 1 (by rfl) ⟨21299876, by rfl⟩ : syracuseStep 28399835 = 42599753) B42599753
theorem B7887415 : Blo 1383511 7887415 := bstep (se 1 (by rfl) ⟨5915561, by rfl⟩ : syracuseStep 7887415 = 11831123) B11831123
theorem B9976745 : Blo 1383511 9976745 := bstep (se 2 (by rfl) ⟨3741279, by rfl⟩ : syracuseStep 9976745 = 7482559) B7482559
theorem B2628607 : Blo 1383511 2628607 := bstep (se 1 (by rfl) ⟨1971455, by rfl⟩ : syracuseStep 2628607 = 3942911) B3942911
theorem B1752511 : Blo 1383511 1752511 := bstep (se 1 (by rfl) ⟨1314383, by rfl⟩ : syracuseStep 1752511 = 2628767) B2628767
theorem B1383919 : Blo 1383511 1383919 := bstep (se 1 (by rfl) ⟨1037939, by rfl⟩ : syracuseStep 1383919 = 2075879) B2075879
theorem B11820599 : Blo 1383511 11820599 := bstep (se 1 (by rfl) ⟨8865449, by rfl⟩ : syracuseStep 11820599 = 17730899) B17730899
theorem B1384175 : Blo 1383511 1384175 := bstep (se 1 (by rfl) ⟨1038131, by rfl⟩ : syracuseStep 1384175 = 2076263) B2076263
theorem B1384191 : Blo 1383511 1384191 := bstep (se 1 (by rfl) ⟨1038143, by rfl⟩ : syracuseStep 1384191 = 2076287) B2076287
theorem B7012331 : Blo 1383511 7012331 := bstep (se 1 (by rfl) ⟨5259248, by rfl⟩ : syracuseStep 7012331 = 10518497) B10518497
theorem B7889147 : Blo 1383511 7889147 := bstep (se 1 (by rfl) ⟨5916860, by rfl⟩ : syracuseStep 7889147 = 11833721) B11833721
theorem B2335223 : Blo 1383511 2335223 := bstep (se 1 (by rfl) ⟨1751417, by rfl⟩ : syracuseStep 2335223 = 3502835) B3502835
theorem B11821625 : Blo 1383511 11821625 := bstep (se 2 (by rfl) ⟨4433109, by rfl⟩ : syracuseStep 11821625 = 8866219) B8866219
theorem B1385319 : Blo 1383511 1385319 := bstep (se 1 (by rfl) ⟨1038989, by rfl⟩ : syracuseStep 1385319 = 2077979) B2077979
theorem B10519469 : Blo 1383511 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B3114323 : Blo 1383511 3114323 := bstep (se 1 (by rfl) ⟨2335742, by rfl⟩ : syracuseStep 3114323 = 4671485) B4671485
theorem B18933223 : Blo 1383511 18933223 := bstep (se 1 (by rfl) ⟨14199917, by rfl⟩ : syracuseStep 18933223 = 28399835) B28399835
theorem B127952621 : Blo 1383511 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B2336681 : Blo 1383511 2336681 := bstep (se 2 (by rfl) ⟨876255, by rfl⟩ : syracuseStep 2336681 = 1752511) B1752511
theorem B3328447 : Blo 1383511 3328447 := bstep (se 1 (by rfl) ⟨2496335, by rfl⟩ : syracuseStep 3328447 = 4992671) B4992671
theorem B113756669 : Blo 1383511 113756669 := bstep (se 3 (by rfl) ⟨21329375, by rfl⟩ : syracuseStep 113756669 = 42658751) B42658751
theorem B7009577 : Blo 1383511 7009577 := bstep (se 2 (by rfl) ⟨2628591, by rfl⟩ : syracuseStep 7009577 = 5257183) B5257183
theorem B4674887 : Blo 1383511 4674887 := bstep (se 1 (by rfl) ⟨3506165, by rfl⟩ : syracuseStep 4674887 = 7012331) B7012331
theorem B2955047 : Blo 1383511 2955047 := bstep (se 1 (by rfl) ⟨2216285, by rfl⟩ : syracuseStep 2955047 = 4432571) B4432571
theorem B10516553 : Blo 1383511 10516553 := bstep (se 2 (by rfl) ⟨3943707, by rfl⟩ : syracuseStep 10516553 = 7887415) B7887415
theorem B2103607 : Blo 1383511 2103607 := bstep (se 1 (by rfl) ⟨1577705, by rfl⟩ : syracuseStep 2103607 = 3155411) B3155411
theorem B3504809 : Blo 1383511 3504809 := bstep (se 2 (by rfl) ⟨1314303, by rfl⟩ : syracuseStep 3504809 = 2628607) B2628607
theorem B1383591 : Blo 1383511 1383591 := bstep (se 1 (by rfl) ⟨1037693, by rfl⟩ : syracuseStep 1383591 = 2075387) B2075387
theorem B5913785 : Blo 1383511 5913785 := bstep (se 2 (by rfl) ⟨2217669, by rfl⟩ : syracuseStep 5913785 = 4435339) B4435339
theorem B6651163 : Blo 1383511 6651163 := bstep (se 1 (by rfl) ⟨4988372, by rfl⟩ : syracuseStep 6651163 = 9976745) B9976745
theorem B2956927 : Blo 1383511 2956927 := bstep (se 1 (by rfl) ⟨2217695, by rfl⟩ : syracuseStep 2956927 = 4435391) B4435391
theorem B7880399 : Blo 1383511 7880399 := bstep (se 1 (by rfl) ⟨5910299, by rfl⟩ : syracuseStep 7880399 = 11820599) B11820599
theorem B1384283 : Blo 1383511 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B1384447 : Blo 1383511 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B5259431 : Blo 1383511 5259431 := bstep (se 1 (by rfl) ⟨3944573, by rfl⟩ : syracuseStep 5259431 = 7889147) B7889147
theorem B1556815 : Blo 1383511 1556815 := bstep (se 1 (by rfl) ⟨1167611, by rfl⟩ : syracuseStep 1556815 = 2335223) B2335223
theorem B7881083 : Blo 1383511 7881083 := bstep (se 1 (by rfl) ⟨5910812, by rfl⟩ : syracuseStep 7881083 = 11821625) B11821625
theorem B7012979 : Blo 1383511 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B1557787 : Blo 1383511 1557787 := bstep (se 1 (by rfl) ⟨1168340, by rfl⟩ : syracuseStep 1557787 = 2336681) B2336681
theorem B2336539 : Blo 1383511 2336539 := bstep (se 1 (by rfl) ⟨1752404, by rfl⟩ : syracuseStep 2336539 = 3504809) B3504809
theorem B3942523 : Blo 1383511 3942523 := bstep (se 1 (by rfl) ⟨2956892, by rfl⟩ : syracuseStep 3942523 = 5913785) B5913785
theorem B3942569 : Blo 1383511 3942569 := bstep (se 2 (by rfl) ⟨1478463, by rfl⟩ : syracuseStep 3942569 = 2956927) B2956927
theorem B5253599 : Blo 1383511 5253599 := bstep (se 1 (by rfl) ⟨3940199, by rfl⟩ : syracuseStep 5253599 = 7880399) B7880399
theorem B2804809 : Blo 1383511 2804809 := bstep (se 2 (by rfl) ⟨1051803, by rfl⟩ : syracuseStep 2804809 = 2103607) B2103607
theorem B4673051 : Blo 1383511 4673051 := bstep (se 1 (by rfl) ⟨3504788, by rfl⟩ : syracuseStep 4673051 = 7009577) B7009577
theorem B3116591 : Blo 1383511 3116591 := bstep (se 1 (by rfl) ⟨2337443, by rfl⟩ : syracuseStep 3116591 = 4674887) B4674887
theorem B2076215 : Blo 1383511 2076215 := bstep (se 1 (by rfl) ⟨1557161, by rfl⟩ : syracuseStep 2076215 = 3114323) B3114323
theorem B75837779 : Blo 1383511 75837779 := bstep (se 1 (by rfl) ⟨56878334, by rfl⟩ : syracuseStep 75837779 = 113756669) B113756669
theorem B8868217 : Blo 1383511 8868217 := bstep (se 2 (by rfl) ⟨3325581, by rfl⟩ : syracuseStep 8868217 = 6651163) B6651163
theorem B25244297 : Blo 1383511 25244297 := bstep (se 2 (by rfl) ⟨9466611, by rfl⟩ : syracuseStep 25244297 = 18933223) B18933223
theorem B4437929 : Blo 1383511 4437929 := bstep (se 2 (by rfl) ⟨1664223, by rfl⟩ : syracuseStep 4437929 = 3328447) B3328447
theorem B85301747 : Blo 1383511 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B7011035 : Blo 1383511 7011035 := bstep (se 1 (by rfl) ⟨5258276, by rfl⟩ : syracuseStep 7011035 = 10516553) B10516553
theorem B7880125 : Blo 1383511 7880125 := bstep (se 3 (by rfl) ⟨1477523, by rfl⟩ : syracuseStep 7880125 = 2955047) B2955047
theorem B3506287 : Blo 1383511 3506287 := bstep (se 1 (by rfl) ⟨2629715, by rfl⟩ : syracuseStep 3506287 = 5259431) B5259431
theorem B2958619 : Blo 1383511 2958619 := bstep (se 1 (by rfl) ⟨2218964, by rfl⟩ : syracuseStep 2958619 = 4437929) B4437929
theorem B3115367 : Blo 1383511 3115367 := bstep (se 1 (by rfl) ⟨2336525, by rfl⟩ : syracuseStep 3115367 = 4673051) B4673051
theorem B3115385 : Blo 1383511 3115385 := bstep (se 2 (by rfl) ⟨1168269, by rfl⟩ : syracuseStep 3115385 = 2336539) B2336539
theorem B5254055 : Blo 1383511 5254055 := bstep (se 1 (by rfl) ⟨3940541, by rfl⟩ : syracuseStep 5254055 = 7881083) B7881083
theorem B16829531 : Blo 1383511 16829531 := bstep (se 1 (by rfl) ⟨12622148, by rfl⟩ : syracuseStep 16829531 = 25244297) B25244297
theorem B2075753 : Blo 1383511 2075753 := bstep (se 2 (by rfl) ⟨778407, by rfl⟩ : syracuseStep 2075753 = 1556815) B1556815
theorem B11824289 : Blo 1383511 11824289 := bstep (se 2 (by rfl) ⟨4434108, by rfl⟩ : syracuseStep 11824289 = 8868217) B8868217
theorem B3739745 : Blo 1383511 3739745 := bstep (se 2 (by rfl) ⟨1402404, by rfl⟩ : syracuseStep 3739745 = 2804809) B2804809
theorem B3502399 : Blo 1383511 3502399 := bstep (se 1 (by rfl) ⟨2626799, by rfl⟩ : syracuseStep 3502399 = 5253599) B5253599
theorem B2077049 : Blo 1383511 2077049 := bstep (se 2 (by rfl) ⟨778893, by rfl⟩ : syracuseStep 2077049 = 1557787) B1557787
theorem B4674023 : Blo 1383511 4674023 := bstep (se 1 (by rfl) ⟨3505517, by rfl⟩ : syracuseStep 4674023 = 7011035) B7011035
theorem B10506833 : Blo 1383511 10506833 := bstep (se 2 (by rfl) ⟨3940062, by rfl⟩ : syracuseStep 10506833 = 7880125) B7880125
theorem B2077727 : Blo 1383511 2077727 := bstep (se 1 (by rfl) ⟨1558295, by rfl⟩ : syracuseStep 2077727 = 3116591) B3116591
theorem B5256697 : Blo 1383511 5256697 := bstep (se 2 (by rfl) ⟨1971261, by rfl⟩ : syracuseStep 5256697 = 3942523) B3942523
theorem B50558519 : Blo 1383511 50558519 := bstep (se 1 (by rfl) ⟨37918889, by rfl⟩ : syracuseStep 50558519 = 75837779) B75837779
theorem B4675319 : Blo 1383511 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B2628379 : Blo 1383511 2628379 := bstep (se 1 (by rfl) ⟨1971284, by rfl⟩ : syracuseStep 2628379 = 3942569) B3942569
theorem B56867831 : Blo 1383511 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B1384143 : Blo 1383511 1384143 := bstep (se 1 (by rfl) ⟨1038107, by rfl⟩ : syracuseStep 1384143 = 2076215) B2076215
theorem B1384699 : Blo 1383511 1384699 := bstep (se 1 (by rfl) ⟨1038524, by rfl⟩ : syracuseStep 1384699 = 2077049) B2077049
theorem B7004555 : Blo 1383511 7004555 := bstep (se 1 (by rfl) ⟨5253416, by rfl⟩ : syracuseStep 7004555 = 10506833) B10506833
theorem B4669865 : Blo 1383511 4669865 := bstep (se 2 (by rfl) ⟨1751199, by rfl⟩ : syracuseStep 4669865 = 3502399) B3502399
theorem B1385151 : Blo 1383511 1385151 := bstep (se 1 (by rfl) ⟨1038863, by rfl⟩ : syracuseStep 1385151 = 2077727) B2077727
theorem B7882859 : Blo 1383511 7882859 := bstep (se 1 (by rfl) ⟨5912144, by rfl⟩ : syracuseStep 7882859 = 11824289) B11824289
theorem B2493163 : Blo 1383511 2493163 := bstep (se 1 (by rfl) ⟨1869872, by rfl⟩ : syracuseStep 2493163 = 3739745) B3739745
theorem B3116015 : Blo 1383511 3116015 := bstep (se 1 (by rfl) ⟨2337011, by rfl⟩ : syracuseStep 3116015 = 4674023) B4674023
theorem B33705679 : Blo 1383511 33705679 := bstep (se 1 (by rfl) ⟨25279259, by rfl⟩ : syracuseStep 33705679 = 50558519) B50558519
theorem B3116879 : Blo 1383511 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B2076911 : Blo 1383511 2076911 := bstep (se 1 (by rfl) ⟨1557683, by rfl⟩ : syracuseStep 2076911 = 3115367) B3115367
theorem B2076923 : Blo 1383511 2076923 := bstep (se 1 (by rfl) ⟨1557692, by rfl⟩ : syracuseStep 2076923 = 3115385) B3115385
theorem B3944825 : Blo 1383511 3944825 := bstep (se 2 (by rfl) ⟨1479309, by rfl⟩ : syracuseStep 3944825 = 2958619) B2958619
theorem B3502703 : Blo 1383511 3502703 := bstep (se 1 (by rfl) ⟨2627027, by rfl⟩ : syracuseStep 3502703 = 5254055) B5254055
theorem B7008929 : Blo 1383511 7008929 := bstep (se 2 (by rfl) ⟨2628348, by rfl⟩ : syracuseStep 7008929 = 5256697) B5256697
theorem B11219687 : Blo 1383511 11219687 := bstep (se 1 (by rfl) ⟨8414765, by rfl⟩ : syracuseStep 11219687 = 16829531) B16829531
theorem B4675049 : Blo 1383511 4675049 := bstep (se 2 (by rfl) ⟨1753143, by rfl⟩ : syracuseStep 4675049 = 3506287) B3506287
theorem B3504505 : Blo 1383511 3504505 := bstep (se 2 (by rfl) ⟨1314189, by rfl⟩ : syracuseStep 3504505 = 2628379) B2628379
theorem B37911887 : Blo 1383511 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B1383835 : Blo 1383511 1383835 := bstep (se 1 (by rfl) ⟨1037876, by rfl⟩ : syracuseStep 1383835 = 2075753) B2075753
theorem B1384607 : Blo 1383511 1384607 := bstep (se 1 (by rfl) ⟨1038455, by rfl⟩ : syracuseStep 1384607 = 2076911) B2076911
theorem B1384615 : Blo 1383511 1384615 := bstep (se 1 (by rfl) ⟨1038461, by rfl⟩ : syracuseStep 1384615 = 2076923) B2076923
theorem B2629883 : Blo 1383511 2629883 := bstep (se 1 (by rfl) ⟨1972412, by rfl⟩ : syracuseStep 2629883 = 3944825) B3944825
theorem B4669703 : Blo 1383511 4669703 := bstep (se 1 (by rfl) ⟨3502277, by rfl⟩ : syracuseStep 4669703 = 7004555) B7004555
theorem B3113243 : Blo 1383511 3113243 := bstep (se 1 (by rfl) ⟨2334932, by rfl⟩ : syracuseStep 3113243 = 4669865) B4669865
theorem B2335135 : Blo 1383511 2335135 := bstep (se 1 (by rfl) ⟨1751351, by rfl⟩ : syracuseStep 2335135 = 3502703) B3502703
theorem B7479791 : Blo 1383511 7479791 := bstep (se 1 (by rfl) ⟨5609843, by rfl⟩ : syracuseStep 7479791 = 11219687) B11219687
theorem B13296869 : Blo 1383511 13296869 := bstep (se 4 (by rfl) ⟨1246581, by rfl⟩ : syracuseStep 13296869 = 2493163) B2493163
theorem B25274591 : Blo 1383511 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B4672619 : Blo 1383511 4672619 := bstep (se 1 (by rfl) ⟨3504464, by rfl⟩ : syracuseStep 4672619 = 7008929) B7008929
theorem B4672673 : Blo 1383511 4672673 := bstep (se 2 (by rfl) ⟨1752252, by rfl⟩ : syracuseStep 4672673 = 3504505) B3504505
theorem B3116699 : Blo 1383511 3116699 := bstep (se 1 (by rfl) ⟨2337524, by rfl⟩ : syracuseStep 3116699 = 4675049) B4675049
theorem B5255239 : Blo 1383511 5255239 := bstep (se 1 (by rfl) ⟨3941429, by rfl⟩ : syracuseStep 5255239 = 7882859) B7882859
theorem B2077343 : Blo 1383511 2077343 := bstep (se 1 (by rfl) ⟨1558007, by rfl⟩ : syracuseStep 2077343 = 3116015) B3116015
theorem B2077919 : Blo 1383511 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B44940905 : Blo 1383511 44940905 := bstep (se 2 (by rfl) ⟨16852839, by rfl⟩ : syracuseStep 44940905 = 33705679) B33705679
theorem B1753255 : Blo 1383511 1753255 := bstep (se 1 (by rfl) ⟨1314941, by rfl⟩ : syracuseStep 1753255 = 2629883) B2629883
theorem B3113135 : Blo 1383511 3113135 := bstep (se 1 (by rfl) ⟨2334851, by rfl⟩ : syracuseStep 3113135 = 4669703) B4669703
theorem B1384895 : Blo 1383511 1384895 := bstep (se 1 (by rfl) ⟨1038671, by rfl⟩ : syracuseStep 1384895 = 2077343) B2077343
theorem B3113513 : Blo 1383511 3113513 := bstep (se 2 (by rfl) ⟨1167567, by rfl⟩ : syracuseStep 3113513 = 2335135) B2335135
theorem B1385279 : Blo 1383511 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B8864579 : Blo 1383511 8864579 := bstep (se 1 (by rfl) ⟨6648434, by rfl⟩ : syracuseStep 8864579 = 13296869) B13296869
theorem B3115079 : Blo 1383511 3115079 := bstep (se 1 (by rfl) ⟨2336309, by rfl⟩ : syracuseStep 3115079 = 4672619) B4672619
theorem B3115115 : Blo 1383511 3115115 := bstep (se 1 (by rfl) ⟨2336336, by rfl⟩ : syracuseStep 3115115 = 4672673) B4672673
theorem B29960603 : Blo 1383511 29960603 := bstep (se 1 (by rfl) ⟨22470452, by rfl⟩ : syracuseStep 29960603 = 44940905) B44940905
theorem B7006985 : Blo 1383511 7006985 := bstep (se 2 (by rfl) ⟨2627619, by rfl⟩ : syracuseStep 7006985 = 5255239) B5255239
theorem B2075495 : Blo 1383511 2075495 := bstep (se 1 (by rfl) ⟨1556621, by rfl⟩ : syracuseStep 2075495 = 3113243) B3113243
theorem B2077799 : Blo 1383511 2077799 := bstep (se 1 (by rfl) ⟨1558349, by rfl⟩ : syracuseStep 2077799 = 3116699) B3116699
theorem B4986527 : Blo 1383511 4986527 := bstep (se 1 (by rfl) ⟨3739895, by rfl⟩ : syracuseStep 4986527 = 7479791) B7479791
theorem B16849727 : Blo 1383511 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B1385199 : Blo 1383511 1385199 := bstep (se 1 (by rfl) ⟨1038899, by rfl⟩ : syracuseStep 1385199 = 2077799) B2077799
theorem B19973735 : Blo 1383511 19973735 := bstep (se 1 (by rfl) ⟨14980301, by rfl⟩ : syracuseStep 19973735 = 29960603) B29960603
theorem B13297405 : Blo 1383511 13297405 := bstep (se 3 (by rfl) ⟨2493263, by rfl⟩ : syracuseStep 13297405 = 4986527) B4986527
theorem B4671323 : Blo 1383511 4671323 := bstep (se 1 (by rfl) ⟨3503492, by rfl⟩ : syracuseStep 4671323 = 7006985) B7006985
theorem B11233151 : Blo 1383511 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B2075423 : Blo 1383511 2075423 := bstep (se 1 (by rfl) ⟨1556567, by rfl⟩ : syracuseStep 2075423 = 3113135) B3113135
theorem B2337673 : Blo 1383511 2337673 := bstep (se 2 (by rfl) ⟨876627, by rfl⟩ : syracuseStep 2337673 = 1753255) B1753255
theorem B2075675 : Blo 1383511 2075675 := bstep (se 1 (by rfl) ⟨1556756, by rfl⟩ : syracuseStep 2075675 = 3113513) B3113513
theorem B5909719 : Blo 1383511 5909719 := bstep (se 1 (by rfl) ⟨4432289, by rfl⟩ : syracuseStep 5909719 = 8864579) B8864579
theorem B2076719 : Blo 1383511 2076719 := bstep (se 1 (by rfl) ⟨1557539, by rfl⟩ : syracuseStep 2076719 = 3115079) B3115079
theorem B2076743 : Blo 1383511 2076743 := bstep (se 1 (by rfl) ⟨1557557, by rfl⟩ : syracuseStep 2076743 = 3115115) B3115115
theorem B1383663 : Blo 1383511 1383663 := bstep (se 1 (by rfl) ⟨1037747, by rfl⟩ : syracuseStep 1383663 = 2075495) B2075495
theorem B1384479 : Blo 1383511 1384479 := bstep (se 1 (by rfl) ⟨1038359, by rfl⟩ : syracuseStep 1384479 = 2076719) B2076719
theorem B1384495 : Blo 1383511 1384495 := bstep (se 1 (by rfl) ⟨1038371, by rfl⟩ : syracuseStep 1384495 = 2076743) B2076743
theorem B3114215 : Blo 1383511 3114215 := bstep (se 1 (by rfl) ⟨2335661, by rfl⟩ : syracuseStep 3114215 = 4671323) B4671323
theorem B7488767 : Blo 1383511 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B17729873 : Blo 1383511 17729873 := bstep (se 2 (by rfl) ⟨6648702, by rfl⟩ : syracuseStep 17729873 = 13297405) B13297405
theorem B13315823 : Blo 1383511 13315823 := bstep (se 1 (by rfl) ⟨9986867, by rfl⟩ : syracuseStep 13315823 = 19973735) B19973735
theorem B3116897 : Blo 1383511 3116897 := bstep (se 2 (by rfl) ⟨1168836, by rfl⟩ : syracuseStep 3116897 = 2337673) B2337673
theorem B7879625 : Blo 1383511 7879625 := bstep (se 2 (by rfl) ⟨2954859, by rfl⟩ : syracuseStep 7879625 = 5909719) B5909719
theorem B1383615 : Blo 1383511 1383615 := bstep (se 1 (by rfl) ⟨1037711, by rfl⟩ : syracuseStep 1383615 = 2075423) B2075423
theorem B1383783 : Blo 1383511 1383783 := bstep (se 1 (by rfl) ⟨1037837, by rfl⟩ : syracuseStep 1383783 = 2075675) B2075675
theorem B5253083 : Blo 1383511 5253083 := bstep (se 1 (by rfl) ⟨3939812, by rfl⟩ : syracuseStep 5253083 = 7879625) B7879625
theorem B2076143 : Blo 1383511 2076143 := bstep (se 1 (by rfl) ⟨1557107, by rfl⟩ : syracuseStep 2076143 = 3114215) B3114215
theorem B4992511 : Blo 1383511 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B8877215 : Blo 1383511 8877215 := bstep (se 1 (by rfl) ⟨6657911, by rfl⟩ : syracuseStep 8877215 = 13315823) B13315823
theorem B2077931 : Blo 1383511 2077931 := bstep (se 1 (by rfl) ⟨1558448, by rfl⟩ : syracuseStep 2077931 = 3116897) B3116897
theorem B11819915 : Blo 1383511 11819915 := bstep (se 1 (by rfl) ⟨8864936, by rfl⟩ : syracuseStep 11819915 = 17729873) B17729873
theorem B1385287 : Blo 1383511 1385287 := bstep (se 1 (by rfl) ⟨1038965, by rfl⟩ : syracuseStep 1385287 = 2077931) B2077931
theorem B5918143 : Blo 1383511 5918143 := bstep (se 1 (by rfl) ⟨4438607, by rfl⟩ : syracuseStep 5918143 = 8877215) B8877215
theorem B3502055 : Blo 1383511 3502055 := bstep (se 1 (by rfl) ⟨2626541, by rfl⟩ : syracuseStep 3502055 = 5253083) B5253083
theorem B6656681 : Blo 1383511 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B7879943 : Blo 1383511 7879943 := bstep (se 1 (by rfl) ⟨5909957, by rfl⟩ : syracuseStep 7879943 = 11819915) B11819915
theorem B1384095 : Blo 1383511 1384095 := bstep (se 1 (by rfl) ⟨1038071, by rfl⟩ : syracuseStep 1384095 = 2076143) B2076143
theorem B7890857 : Blo 1383511 7890857 := bstep (se 2 (by rfl) ⟨2959071, by rfl⟩ : syracuseStep 7890857 = 5918143) B5918143
theorem B5253295 : Blo 1383511 5253295 := bstep (se 1 (by rfl) ⟨3939971, by rfl⟩ : syracuseStep 5253295 = 7879943) B7879943
theorem B17751149 : Blo 1383511 17751149 := bstep (se 3 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 17751149 = 6656681) B6656681
theorem B2334703 : Blo 1383511 2334703 := bstep (se 1 (by rfl) ⟨1751027, by rfl⟩ : syracuseStep 2334703 = 3502055) B3502055
theorem B7004393 : Blo 1383511 7004393 := bstep (se 2 (by rfl) ⟨2626647, by rfl⟩ : syracuseStep 7004393 = 5253295) B5253295
theorem B5260571 : Blo 1383511 5260571 := bstep (se 1 (by rfl) ⟨3945428, by rfl⟩ : syracuseStep 5260571 = 7890857) B7890857
theorem B11834099 : Blo 1383511 11834099 := bstep (se 1 (by rfl) ⟨8875574, by rfl⟩ : syracuseStep 11834099 = 17751149) B17751149
theorem B3112937 : Blo 1383511 3112937 := bstep (se 2 (by rfl) ⟨1167351, by rfl⟩ : syracuseStep 3112937 = 2334703) B2334703
theorem B4669595 : Blo 1383511 4669595 := bstep (se 1 (by rfl) ⟨3502196, by rfl⟩ : syracuseStep 4669595 = 7004393) B7004393
theorem B7889399 : Blo 1383511 7889399 := bstep (se 1 (by rfl) ⟨5917049, by rfl⟩ : syracuseStep 7889399 = 11834099) B11834099
theorem B3507047 : Blo 1383511 3507047 := bstep (se 1 (by rfl) ⟨2630285, by rfl⟩ : syracuseStep 3507047 = 5260571) B5260571
theorem B2075291 : Blo 1383511 2075291 := bstep (se 1 (by rfl) ⟨1556468, by rfl⟩ : syracuseStep 2075291 = 3112937) B3112937
theorem B3113063 : Blo 1383511 3113063 := bstep (se 1 (by rfl) ⟨2334797, by rfl⟩ : syracuseStep 3113063 = 4669595) B4669595
theorem B5259599 : Blo 1383511 5259599 := bstep (se 1 (by rfl) ⟨3944699, by rfl⟩ : syracuseStep 5259599 = 7889399) B7889399
theorem B2338031 : Blo 1383511 2338031 := bstep (se 1 (by rfl) ⟨1753523, by rfl⟩ : syracuseStep 2338031 = 3507047) B3507047
theorem B1383527 : Blo 1383511 1383527 := bstep (se 1 (by rfl) ⟨1037645, by rfl⟩ : syracuseStep 1383527 = 2075291) B2075291
theorem B3506399 : Blo 1383511 3506399 := bstep (se 1 (by rfl) ⟨2629799, by rfl⟩ : syracuseStep 3506399 = 5259599) B5259599
theorem B1558687 : Blo 1383511 1558687 := bstep (se 1 (by rfl) ⟨1169015, by rfl⟩ : syracuseStep 1558687 = 2338031) B2338031
theorem B2075375 : Blo 1383511 2075375 := bstep (se 1 (by rfl) ⟨1556531, by rfl⟩ : syracuseStep 2075375 = 3113063) B3113063
theorem B2337599 : Blo 1383511 2337599 := bstep (se 1 (by rfl) ⟨1753199, by rfl⟩ : syracuseStep 2337599 = 3506399) B3506399
theorem B2078249 : Blo 1383511 2078249 := bstep (se 2 (by rfl) ⟨779343, by rfl⟩ : syracuseStep 2078249 = 1558687) B1558687
theorem B1383583 : Blo 1383511 1383583 := bstep (se 1 (by rfl) ⟨1037687, by rfl⟩ : syracuseStep 1383583 = 2075375) B2075375
theorem B1385499 : Blo 1383511 1385499 := bstep (se 1 (by rfl) ⟨1039124, by rfl⟩ : syracuseStep 1385499 = 2078249) B2078249
theorem B1558399 : Blo 1383511 1558399 := bstep (se 1 (by rfl) ⟨1168799, by rfl⟩ : syracuseStep 1558399 = 2337599) B2337599
theorem B2077865 : Blo 1383511 2077865 := bstep (se 2 (by rfl) ⟨779199, by rfl⟩ : syracuseStep 2077865 = 1558399) B1558399
theorem B1385243 : Blo 1383511 1385243 := bstep (se 1 (by rfl) ⟨1038932, by rfl⟩ : syracuseStep 1385243 = 2077865) B2077865

theorem C0 (j : ℕ) (h1 : 345877 ≤ j) (h2 : j ≤ 346377) : Blo 1383511 (4 * j + 3) := by
  interval_cases j
  · exact B1383511
  · exact B1383515
  · exact B1383519
  · exact B1383523
  · exact B1383527
  · exact B1383531
  · exact B1383535
  · exact B1383539
  · exact B1383543
  · exact B1383547
  · exact B1383551
  · exact B1383555
  · exact B1383559
  · exact B1383563
  · exact B1383567
  · exact B1383571
  · exact B1383575
  · exact B1383579
  · exact B1383583
  · exact B1383587
  · exact B1383591
  · exact B1383595
  · exact B1383599
  · exact B1383603
  · exact B1383607
  · exact B1383611
  · exact B1383615
  · exact B1383619
  · exact B1383623
  · exact B1383627
  · exact B1383631
  · exact B1383635
  · exact B1383639
  · exact B1383643
  · exact B1383647
  · exact B1383651
  · exact B1383655
  · exact B1383659
  · exact B1383663
  · exact B1383667
  · exact B1383671
  · exact B1383675
  · exact B1383679
  · exact B1383683
  · exact B1383687
  · exact B1383691
  · exact B1383695
  · exact B1383699
  · exact B1383703
  · exact B1383707
  · exact B1383711
  · exact B1383715
  · exact B1383719
  · exact B1383723
  · exact B1383727
  · exact B1383731
  · exact B1383735
  · exact B1383739
  · exact B1383743
  · exact B1383747
  · exact B1383751
  · exact B1383755
  · exact B1383759
  · exact B1383763
  · exact B1383767
  · exact B1383771
  · exact B1383775
  · exact B1383779
  · exact B1383783
  · exact B1383787
  · exact B1383791
  · exact B1383795
  · exact B1383799
  · exact B1383803
  · exact B1383807
  · exact B1383811
  · exact B1383815
  · exact B1383819
  · exact B1383823
  · exact B1383827
  · exact B1383831
  · exact B1383835
  · exact B1383839
  · exact B1383843
  · exact B1383847
  · exact B1383851
  · exact B1383855
  · exact B1383859
  · exact B1383863
  · exact B1383867
  · exact B1383871
  · exact B1383875
  · exact B1383879
  · exact B1383883
  · exact B1383887
  · exact B1383891
  · exact B1383895
  · exact B1383899
  · exact B1383903
  · exact B1383907
  · exact B1383911
  · exact B1383915
  · exact B1383919
  · exact B1383923
  · exact B1383927
  · exact B1383931
  · exact B1383935
  · exact B1383939
  · exact B1383943
  · exact B1383947
  · exact B1383951
  · exact B1383955
  · exact B1383959
  · exact B1383963
  · exact B1383967
  · exact B1383971
  · exact B1383975
  · exact B1383979
  · exact B1383983
  · exact B1383987
  · exact B1383991
  · exact B1383995
  · exact B1383999
  · exact B1384003
  · exact B1384007
  · exact B1384011
  · exact B1384015
  · exact B1384019
  · exact B1384023
  · exact B1384027
  · exact B1384031
  · exact B1384035
  · exact B1384039
  · exact B1384043
  · exact B1384047
  · exact B1384051
  · exact B1384055
  · exact B1384059
  · exact B1384063
  · exact B1384067
  · exact B1384071
  · exact B1384075
  · exact B1384079
  · exact B1384083
  · exact B1384087
  · exact B1384091
  · exact B1384095
  · exact B1384099
  · exact B1384103
  · exact B1384107
  · exact B1384111
  · exact B1384115
  · exact B1384119
  · exact B1384123
  · exact B1384127
  · exact B1384131
  · exact B1384135
  · exact B1384139
  · exact B1384143
  · exact B1384147
  · exact B1384151
  · exact B1384155
  · exact B1384159
  · exact B1384163
  · exact B1384167
  · exact B1384171
  · exact B1384175
  · exact B1384179
  · exact B1384183
  · exact B1384187
  · exact B1384191
  · exact B1384195
  · exact B1384199
  · exact B1384203
  · exact B1384207
  · exact B1384211
  · exact B1384215
  · exact B1384219
  · exact B1384223
  · exact B1384227
  · exact B1384231
  · exact B1384235
  · exact B1384239
  · exact B1384243
  · exact B1384247
  · exact B1384251
  · exact B1384255
  · exact B1384259
  · exact B1384263
  · exact B1384267
  · exact B1384271
  · exact B1384275
  · exact B1384279
  · exact B1384283
  · exact B1384287
  · exact B1384291
  · exact B1384295
  · exact B1384299
  · exact B1384303
  · exact B1384307
  · exact B1384311
  · exact B1384315
  · exact B1384319
  · exact B1384323
  · exact B1384327
  · exact B1384331
  · exact B1384335
  · exact B1384339
  · exact B1384343
  · exact B1384347
  · exact B1384351
  · exact B1384355
  · exact B1384359
  · exact B1384363
  · exact B1384367
  · exact B1384371
  · exact B1384375
  · exact B1384379
  · exact B1384383
  · exact B1384387
  · exact B1384391
  · exact B1384395
  · exact B1384399
  · exact B1384403
  · exact B1384407
  · exact B1384411
  · exact B1384415
  · exact B1384419
  · exact B1384423
  · exact B1384427
  · exact B1384431
  · exact B1384435
  · exact B1384439
  · exact B1384443
  · exact B1384447
  · exact B1384451
  · exact B1384455
  · exact B1384459
  · exact B1384463
  · exact B1384467
  · exact B1384471
  · exact B1384475
  · exact B1384479
  · exact B1384483
  · exact B1384487
  · exact B1384491
  · exact B1384495
  · exact B1384499
  · exact B1384503
  · exact B1384507
  · exact B1384511
  · exact B1384515
  · exact B1384519
  · exact B1384523
  · exact B1384527
  · exact B1384531
  · exact B1384535
  · exact B1384539
  · exact B1384543
  · exact B1384547
  · exact B1384551
  · exact B1384555
  · exact B1384559
  · exact B1384563
  · exact B1384567
  · exact B1384571
  · exact B1384575
  · exact B1384579
  · exact B1384583
  · exact B1384587
  · exact B1384591
  · exact B1384595
  · exact B1384599
  · exact B1384603
  · exact B1384607
  · exact B1384611
  · exact B1384615
  · exact B1384619
  · exact B1384623
  · exact B1384627
  · exact B1384631
  · exact B1384635
  · exact B1384639
  · exact B1384643
  · exact B1384647
  · exact B1384651
  · exact B1384655
  · exact B1384659
  · exact B1384663
  · exact B1384667
  · exact B1384671
  · exact B1384675
  · exact B1384679
  · exact B1384683
  · exact B1384687
  · exact B1384691
  · exact B1384695
  · exact B1384699
  · exact B1384703
  · exact B1384707
  · exact B1384711
  · exact B1384715
  · exact B1384719
  · exact B1384723
  · exact B1384727
  · exact B1384731
  · exact B1384735
  · exact B1384739
  · exact B1384743
  · exact B1384747
  · exact B1384751
  · exact B1384755
  · exact B1384759
  · exact B1384763
  · exact B1384767
  · exact B1384771
  · exact B1384775
  · exact B1384779
  · exact B1384783
  · exact B1384787
  · exact B1384791
  · exact B1384795
  · exact B1384799
  · exact B1384803
  · exact B1384807
  · exact B1384811
  · exact B1384815
  · exact B1384819
  · exact B1384823
  · exact B1384827
  · exact B1384831
  · exact B1384835
  · exact B1384839
  · exact B1384843
  · exact B1384847
  · exact B1384851
  · exact B1384855
  · exact B1384859
  · exact B1384863
  · exact B1384867
  · exact B1384871
  · exact B1384875
  · exact B1384879
  · exact B1384883
  · exact B1384887
  · exact B1384891
  · exact B1384895
  · exact B1384899
  · exact B1384903
  · exact B1384907
  · exact B1384911
  · exact B1384915
  · exact B1384919
  · exact B1384923
  · exact B1384927
  · exact B1384931
  · exact B1384935
  · exact B1384939
  · exact B1384943
  · exact B1384947
  · exact B1384951
  · exact B1384955
  · exact B1384959
  · exact B1384963
  · exact B1384967
  · exact B1384971
  · exact B1384975
  · exact B1384979
  · exact B1384983
  · exact B1384987
  · exact B1384991
  · exact B1384995
  · exact B1384999
  · exact B1385003
  · exact B1385007
  · exact B1385011
  · exact B1385015
  · exact B1385019
  · exact B1385023
  · exact B1385027
  · exact B1385031
  · exact B1385035
  · exact B1385039
  · exact B1385043
  · exact B1385047
  · exact B1385051
  · exact B1385055
  · exact B1385059
  · exact B1385063
  · exact B1385067
  · exact B1385071
  · exact B1385075
  · exact B1385079
  · exact B1385083
  · exact B1385087
  · exact B1385091
  · exact B1385095
  · exact B1385099
  · exact B1385103
  · exact B1385107
  · exact B1385111
  · exact B1385115
  · exact B1385119
  · exact B1385123
  · exact B1385127
  · exact B1385131
  · exact B1385135
  · exact B1385139
  · exact B1385143
  · exact B1385147
  · exact B1385151
  · exact B1385155
  · exact B1385159
  · exact B1385163
  · exact B1385167
  · exact B1385171
  · exact B1385175
  · exact B1385179
  · exact B1385183
  · exact B1385187
  · exact B1385191
  · exact B1385195
  · exact B1385199
  · exact B1385203
  · exact B1385207
  · exact B1385211
  · exact B1385215
  · exact B1385219
  · exact B1385223
  · exact B1385227
  · exact B1385231
  · exact B1385235
  · exact B1385239
  · exact B1385243
  · exact B1385247
  · exact B1385251
  · exact B1385255
  · exact B1385259
  · exact B1385263
  · exact B1385267
  · exact B1385271
  · exact B1385275
  · exact B1385279
  · exact B1385283
  · exact B1385287
  · exact B1385291
  · exact B1385295
  · exact B1385299
  · exact B1385303
  · exact B1385307
  · exact B1385311
  · exact B1385315
  · exact B1385319
  · exact B1385323
  · exact B1385327
  · exact B1385331
  · exact B1385335
  · exact B1385339
  · exact B1385343
  · exact B1385347
  · exact B1385351
  · exact B1385355
  · exact B1385359
  · exact B1385363
  · exact B1385367
  · exact B1385371
  · exact B1385375
  · exact B1385379
  · exact B1385383
  · exact B1385387
  · exact B1385391
  · exact B1385395
  · exact B1385399
  · exact B1385403
  · exact B1385407
  · exact B1385411
  · exact B1385415
  · exact B1385419
  · exact B1385423
  · exact B1385427
  · exact B1385431
  · exact B1385435
  · exact B1385439
  · exact B1385443
  · exact B1385447
  · exact B1385451
  · exact B1385455
  · exact B1385459
  · exact B1385463
  · exact B1385467
  · exact B1385471
  · exact B1385475
  · exact B1385479
  · exact B1385483
  · exact B1385487
  · exact B1385491
  · exact B1385495
  · exact B1385499
  · exact B1385503
  · exact B1385507
  · exact B1385511

theorem solution (m : ℕ) (hlo : 1383511 ≤ m) (hhi : m ≤ 1385511) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 345877 ≤ j := by omega
    have hj2 : j ≤ 346377 := by omega
    have hb : Blo 1383511 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
