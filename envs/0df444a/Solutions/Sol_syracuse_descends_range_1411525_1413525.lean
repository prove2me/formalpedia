-- Prove2me | solution 1 for syracuse_descends_range_1411525_1413525
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:08.673015+00:00
-- url     : https://prove2.me/submissions/07ed46aa-6431-4ca2-b12a-35fe6ea2c6c8

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


theorem B2383877 : Blo 1411525 2383877 := bbase (se 4 (by rfl) ⟨223488, by rfl⟩ : syracuseStep 2383877 = 446977) (by norm_num)
theorem B1695757 : Blo 1411525 1695757 := bbase (se 3 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 1695757 = 635909) (by norm_num)
theorem B1589269 : Blo 1411525 1589269 := bbase (se 6 (by rfl) ⟨37248, by rfl⟩ : syracuseStep 1589269 = 74497) (by norm_num)
theorem B2293805 : Blo 1411525 2293805 := bbase (se 3 (by rfl) ⟨430088, by rfl⟩ : syracuseStep 2293805 = 860177) (by norm_num)
theorem B1589305 : Blo 1411525 1589305 := bbase (se 2 (by rfl) ⟨595989, by rfl⟩ : syracuseStep 1589305 = 1191979) (by norm_num)
theorem B3178565 : Blo 1411525 3178565 := bbase (se 4 (by rfl) ⟨297990, by rfl⟩ : syracuseStep 3178565 = 595981) (by norm_num)
theorem B7446613 : Blo 1411525 7446613 := bbase (se 8 (by rfl) ⟨43632, by rfl⟩ : syracuseStep 7446613 = 87265) (by norm_num)
theorem B1589341 : Blo 1411525 1589341 := bbase (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) (by norm_num)
theorem B3391589 : Blo 1411525 3391589 := bbase (se 4 (by rfl) ⟨317961, by rfl⟩ : syracuseStep 3391589 = 635923) (by norm_num)
theorem B1589377 : Blo 1411525 1589377 := bbase (se 2 (by rfl) ⟨596016, by rfl⟩ : syracuseStep 1589377 = 1192033) (by norm_num)
theorem B2384005 : Blo 1411525 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B3178637 : Blo 1411525 3178637 := bbase (se 3 (by rfl) ⟨595994, by rfl⟩ : syracuseStep 3178637 = 1191989) (by norm_num)
theorem B1589413 : Blo 1411525 1589413 := bbase (se 4 (by rfl) ⟨149007, by rfl⟩ : syracuseStep 1589413 = 298015) (by norm_num)
theorem B1507501 : Blo 1411525 1507501 := bbase (se 3 (by rfl) ⟨282656, by rfl⟩ : syracuseStep 1507501 = 565313) (by norm_num)
theorem B1695925 : Blo 1411525 1695925 := bbase (se 5 (by rfl) ⟨79496, by rfl⟩ : syracuseStep 1695925 = 158993) (by norm_num)
theorem B7151813 : Blo 1411525 7151813 := bbase (se 4 (by rfl) ⟨670482, by rfl⟩ : syracuseStep 7151813 = 1340965) (by norm_num)
theorem B1589449 : Blo 1411525 1589449 := bbase (se 2 (by rfl) ⟨596043, by rfl⟩ : syracuseStep 1589449 = 1192087) (by norm_num)
theorem B3178709 : Blo 1411525 3178709 := bbase (se 7 (by rfl) ⟨37250, by rfl⟩ : syracuseStep 3178709 = 74501) (by norm_num)
theorem B2384093 : Blo 1411525 2384093 := bbase (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) (by norm_num)
theorem B1589485 : Blo 1411525 1589485 := bbase (se 3 (by rfl) ⟨298028, by rfl⟩ : syracuseStep 1589485 = 596057) (by norm_num)
theorem B1589521 : Blo 1411525 1589521 := bbase (se 2 (by rfl) ⟨596070, by rfl⟩ : syracuseStep 1589521 = 1192141) (by norm_num)
theorem B5726485 : Blo 1411525 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B3178781 : Blo 1411525 3178781 := bbase (se 3 (by rfl) ⟨596021, by rfl⟩ : syracuseStep 3178781 = 1192043) (by norm_num)
theorem B4768037 : Blo 1411525 4768037 := bbase (se 4 (by rfl) ⟨447003, by rfl⟩ : syracuseStep 4768037 = 894007) (by norm_num)
theorem B1909045 : Blo 1411525 1909045 := bbase (se 5 (by rfl) ⟨89486, by rfl⟩ : syracuseStep 1909045 = 178973) (by norm_num)
theorem B1589557 : Blo 1411525 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B12075317 : Blo 1411525 12075317 := bbase (se 5 (by rfl) ⟨566030, by rfl⟩ : syracuseStep 12075317 = 1132061) (by norm_num)
theorem B1589593 : Blo 1411525 1589593 := bbase (se 2 (by rfl) ⟨596097, by rfl⟩ : syracuseStep 1589593 = 1192195) (by norm_num)
theorem B2261341 : Blo 1411525 2261341 := bbase (se 3 (by rfl) ⟨424001, by rfl⟩ : syracuseStep 2261341 = 848003) (by norm_num)
theorem B2384221 : Blo 1411525 2384221 := bbase (se 3 (by rfl) ⟨447041, by rfl⟩ : syracuseStep 2384221 = 894083) (by norm_num)
theorem B3178853 : Blo 1411525 3178853 := bbase (se 4 (by rfl) ⟨298017, by rfl⟩ : syracuseStep 3178853 = 596035) (by norm_num)
theorem B1696121 : Blo 1411525 1696121 := bbase (se 2 (by rfl) ⟨636045, by rfl⟩ : syracuseStep 1696121 = 1272091) (by norm_num)
theorem B1589629 : Blo 1411525 1589629 := bbase (se 3 (by rfl) ⟨298055, by rfl⟩ : syracuseStep 1589629 = 596111) (by norm_num)
theorem B1720705 : Blo 1411525 1720705 := bbase (se 2 (by rfl) ⟨645264, by rfl⟩ : syracuseStep 1720705 = 1290529) (by norm_num)
theorem B1589665 : Blo 1411525 1589665 := bbase (se 2 (by rfl) ⟨596124, by rfl⟩ : syracuseStep 1589665 = 1192249) (by norm_num)
theorem B3178925 : Blo 1411525 3178925 := bbase (se 3 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 3178925 = 1192097) (by norm_num)
theorem B2384309 : Blo 1411525 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B6029765 : Blo 1411525 6029765 := bbase (se 4 (by rfl) ⟨565290, by rfl⟩ : syracuseStep 6029765 = 1130581) (by norm_num)
theorem B1589701 : Blo 1411525 1589701 := bbase (se 4 (by rfl) ⟨149034, by rfl⟩ : syracuseStep 1589701 = 298069) (by norm_num)
theorem B2146765 : Blo 1411525 2146765 := bbase (se 3 (by rfl) ⟨402518, by rfl⟩ : syracuseStep 2146765 = 805037) (by norm_num)
theorem B1589737 : Blo 1411525 1589737 := bbase (se 2 (by rfl) ⟨596151, by rfl⟩ : syracuseStep 1589737 = 1192303) (by norm_num)
theorem B3178997 : Blo 1411525 3178997 := bbase (se 5 (by rfl) ⟨149015, by rfl⟩ : syracuseStep 3178997 = 298031) (by norm_num)
theorem B3310093 : Blo 1411525 3310093 := bbase (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) (by norm_num)
theorem B1589773 : Blo 1411525 1589773 := bbase (se 3 (by rfl) ⟨298082, by rfl⟩ : syracuseStep 1589773 = 596165) (by norm_num)
theorem B1589809 : Blo 1411525 1589809 := bbase (se 2 (by rfl) ⟨596178, by rfl⟩ : syracuseStep 1589809 = 1192357) (by norm_num)
theorem B2384437 : Blo 1411525 2384437 := bbase (se 5 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 2384437 = 223541) (by norm_num)
theorem B3179069 : Blo 1411525 3179069 := bbase (se 3 (by rfl) ⟨596075, by rfl⟩ : syracuseStep 3179069 = 1192151) (by norm_num)
theorem B1589845 : Blo 1411525 1589845 := bbase (se 8 (by rfl) ⟨9315, by rfl⟩ : syracuseStep 1589845 = 18631) (by norm_num)
theorem B1507933 : Blo 1411525 1507933 := bbase (se 3 (by rfl) ⟨282737, by rfl⟩ : syracuseStep 1507933 = 565475) (by norm_num)
theorem B1786465 : Blo 1411525 1786465 := bbase (se 2 (by rfl) ⟨669924, by rfl⟩ : syracuseStep 1786465 = 1339849) (by norm_num)
theorem B4022885 : Blo 1411525 4022885 := bbase (se 4 (by rfl) ⟨377145, by rfl⟩ : syracuseStep 4022885 = 754291) (by norm_num)
theorem B1589881 : Blo 1411525 1589881 := bbase (se 2 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 1589881 = 1192411) (by norm_num)
theorem B3179141 : Blo 1411525 3179141 := bbase (se 4 (by rfl) ⟨298044, by rfl⟩ : syracuseStep 3179141 = 596089) (by norm_num)
theorem B2384525 : Blo 1411525 2384525 := bbase (se 3 (by rfl) ⟨447098, by rfl⟩ : syracuseStep 2384525 = 894197) (by norm_num)
theorem B1589917 : Blo 1411525 1589917 := bbase (se 3 (by rfl) ⟨298109, by rfl⟩ : syracuseStep 1589917 = 596219) (by norm_num)
theorem B1508005 : Blo 1411525 1508005 := bbase (se 4 (by rfl) ⟨141375, by rfl⟩ : syracuseStep 1508005 = 282751) (by norm_num)
theorem B1589953 : Blo 1411525 1589953 := bbase (se 2 (by rfl) ⟨596232, by rfl⟩ : syracuseStep 1589953 = 1192465) (by norm_num)
theorem B3179213 : Blo 1411525 3179213 := bbase (se 3 (by rfl) ⟨596102, by rfl⟩ : syracuseStep 3179213 = 1192205) (by norm_num)
theorem B4522709 : Blo 1411525 4522709 := bbase (se 7 (by rfl) ⟨53000, by rfl⟩ : syracuseStep 4522709 = 106001) (by norm_num)
theorem B4768469 : Blo 1411525 4768469 := bbase (se 7 (by rfl) ⟨55880, by rfl⟩ : syracuseStep 4768469 = 111761) (by norm_num)
theorem B1589989 : Blo 1411525 1589989 := bbase (se 4 (by rfl) ⟨149061, by rfl⟩ : syracuseStep 1589989 = 298123) (by norm_num)
theorem B5088005 : Blo 1411525 5088005 := bbase (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) (by norm_num)
theorem B2261765 : Blo 1411525 2261765 := bbase (se 4 (by rfl) ⟨212040, by rfl⟩ : syracuseStep 2261765 = 424081) (by norm_num)
theorem B5366533 : Blo 1411525 5366533 := bbase (se 4 (by rfl) ⟨503112, by rfl⟩ : syracuseStep 5366533 = 1006225) (by norm_num)
theorem B1590025 : Blo 1411525 1590025 := bbase (se 2 (by rfl) ⟨596259, by rfl⟩ : syracuseStep 1590025 = 1192519) (by norm_num)
theorem B1786637 : Blo 1411525 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B2384653 : Blo 1411525 2384653 := bbase (se 3 (by rfl) ⟨447122, by rfl⟩ : syracuseStep 2384653 = 894245) (by norm_num)
theorem B3179285 : Blo 1411525 3179285 := bbase (se 6 (by rfl) ⟨74514, by rfl⟩ : syracuseStep 3179285 = 149029) (by norm_num)
theorem B1590061 : Blo 1411525 1590061 := bbase (se 3 (by rfl) ⟨298136, by rfl⟩ : syracuseStep 1590061 = 596273) (by norm_num)
theorem B1786693 : Blo 1411525 1786693 := bbase (se 4 (by rfl) ⟨167502, by rfl⟩ : syracuseStep 1786693 = 335005) (by norm_num)
theorem B1590097 : Blo 1411525 1590097 := bbase (se 2 (by rfl) ⟨596286, by rfl⟩ : syracuseStep 1590097 = 1192573) (by norm_num)
theorem B4522837 : Blo 1411525 4522837 := bbase (se 9 (by rfl) ⟨13250, by rfl⟩ : syracuseStep 4522837 = 26501) (by norm_num)
theorem B3179357 : Blo 1411525 3179357 := bbase (se 3 (by rfl) ⟨596129, by rfl⟩ : syracuseStep 3179357 = 1192259) (by norm_num)
theorem B2384741 : Blo 1411525 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B1590133 : Blo 1411525 1590133 := bbase (se 5 (by rfl) ⟨74537, by rfl⟩ : syracuseStep 1590133 = 149075) (by norm_num)
theorem B5088133 : Blo 1411525 5088133 := bbase (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) (by norm_num)
theorem B1590169 : Blo 1411525 1590169 := bbase (se 2 (by rfl) ⟨596313, by rfl⟩ : syracuseStep 1590169 = 1192627) (by norm_num)
theorem B1786789 : Blo 1411525 1786789 := bbase (se 4 (by rfl) ⟨167511, by rfl⟩ : syracuseStep 1786789 = 335023) (by norm_num)
theorem B3179429 : Blo 1411525 3179429 := bbase (se 4 (by rfl) ⟨298071, by rfl⟩ : syracuseStep 3179429 = 596143) (by norm_num)
theorem B2294701 : Blo 1411525 2294701 := bbase (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) (by norm_num)
theorem B1590205 : Blo 1411525 1590205 := bbase (se 3 (by rfl) ⟨298163, by rfl⟩ : syracuseStep 1590205 = 596327) (by norm_num)
theorem B2384869 : Blo 1411525 2384869 := bbase (se 4 (by rfl) ⟨223581, by rfl⟩ : syracuseStep 2384869 = 447163) (by norm_num)
theorem B3179501 : Blo 1411525 3179501 := bbase (se 3 (by rfl) ⟨596156, by rfl⟩ : syracuseStep 3179501 = 1192313) (by norm_num)
theorem B3178493 : Blo 1411525 3178493 := bbase (se 3 (by rfl) ⟨595967, by rfl⟩ : syracuseStep 3178493 = 1191935) (by norm_num)
theorem B2679797 : Blo 1411525 2679797 := bbase (se 5 (by rfl) ⟨125615, by rfl⟩ : syracuseStep 2679797 = 251231) (by norm_num)
theorem B1508377 : Blo 1411525 1508377 := bbase (se 2 (by rfl) ⟨565641, by rfl⟩ : syracuseStep 1508377 = 1131283) (by norm_num)
theorem B2262053 : Blo 1411525 2262053 := bbase (se 4 (by rfl) ⟨212067, by rfl⟩ : syracuseStep 2262053 = 424135) (by norm_num)
theorem B3179573 : Blo 1411525 3179573 := bbase (se 5 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 3179573 = 298085) (by norm_num)
theorem B5366837 : Blo 1411525 5366837 := bbase (se 5 (by rfl) ⟨251570, by rfl⟩ : syracuseStep 5366837 = 503141) (by norm_num)
theorem B2384957 : Blo 1411525 2384957 := bbase (se 3 (by rfl) ⟨447179, by rfl⟩ : syracuseStep 2384957 = 894359) (by norm_num)
theorem B1786961 : Blo 1411525 1786961 := bbase (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) (by norm_num)
theorem B4523093 : Blo 1411525 4523093 := bbase (se 8 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 4523093 = 53005) (by norm_num)
theorem B10183765 : Blo 1411525 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B3015805 : Blo 1411525 3015805 := bbase (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) (by norm_num)
theorem B3179645 : Blo 1411525 3179645 := bbase (se 3 (by rfl) ⟨596183, by rfl⟩ : syracuseStep 3179645 = 1192367) (by norm_num)
theorem B2679941 : Blo 1411525 2679941 := bbase (se 4 (by rfl) ⟨251244, by rfl⟩ : syracuseStep 2679941 = 502489) (by norm_num)
theorem B4768901 : Blo 1411525 4768901 := bbase (se 4 (by rfl) ⟨447084, by rfl⟩ : syracuseStep 4768901 = 894169) (by norm_num)
theorem B1787017 : Blo 1411525 1787017 := bbase (se 2 (by rfl) ⟨670131, by rfl⟩ : syracuseStep 1787017 = 1340263) (by norm_num)
theorem B2385085 : Blo 1411525 2385085 := bbase (se 3 (by rfl) ⟨447203, by rfl⟩ : syracuseStep 2385085 = 894407) (by norm_num)
theorem B3179717 : Blo 1411525 3179717 := bbase (se 4 (by rfl) ⟨298098, by rfl⟩ : syracuseStep 3179717 = 596197) (by norm_num)
theorem B1787113 : Blo 1411525 1787113 := bbase (se 2 (by rfl) ⟨670167, by rfl⟩ : syracuseStep 1787113 = 1340335) (by norm_num)
theorem B1836265 : Blo 1411525 1836265 := bbase (se 2 (by rfl) ⟨688599, by rfl⟩ : syracuseStep 1836265 = 1377199) (by norm_num)
theorem B3572981 : Blo 1411525 3572981 := bbase (se 5 (by rfl) ⟨167483, by rfl⟩ : syracuseStep 3572981 = 334967) (by norm_num)
theorem B2262277 : Blo 1411525 2262277 := bbase (se 4 (by rfl) ⟨212088, by rfl⟩ : syracuseStep 2262277 = 424177) (by norm_num)
theorem B4023557 : Blo 1411525 4023557 := bbase (se 4 (by rfl) ⟨377208, by rfl⟩ : syracuseStep 4023557 = 754417) (by norm_num)
theorem B3179789 : Blo 1411525 3179789 := bbase (se 3 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 3179789 = 1192421) (by norm_num)
theorem B2385173 : Blo 1411525 2385173 := bbase (se 6 (by rfl) ⟨55902, by rfl⟩ : syracuseStep 2385173 = 111805) (by norm_num)
theorem B5432645 : Blo 1411525 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B30532949 : Blo 1411525 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B3179861 : Blo 1411525 3179861 := bbase (se 12 (by rfl) ⟨1164, by rfl⟩ : syracuseStep 3179861 = 2329) (by norm_num)
theorem B1508753 : Blo 1411525 1508753 := bbase (se 2 (by rfl) ⟨565782, by rfl⟩ : syracuseStep 1508753 = 1131565) (by norm_num)
theorem B1787285 : Blo 1411525 1787285 := bbase (se 6 (by rfl) ⟨41889, by rfl⟩ : syracuseStep 1787285 = 83779) (by norm_num)
theorem B2385301 : Blo 1411525 2385301 := bbase (se 6 (by rfl) ⟨55905, by rfl⟩ : syracuseStep 2385301 = 111811) (by norm_num)
theorem B3179933 : Blo 1411525 3179933 := bbase (se 3 (by rfl) ⟨596237, by rfl⟩ : syracuseStep 3179933 = 1192475) (by norm_num)
theorem B2680229 : Blo 1411525 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B3573173 : Blo 1411525 3573173 := bbase (se 5 (by rfl) ⟨167492, by rfl⟩ : syracuseStep 3573173 = 334985) (by norm_num)
theorem B4294085 : Blo 1411525 4294085 := bbase (se 4 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 4294085 = 805141) (by norm_num)
theorem B1787341 : Blo 1411525 1787341 := bbase (se 3 (by rfl) ⟨335126, by rfl⟩ : syracuseStep 1787341 = 670253) (by norm_num)
theorem B6784469 : Blo 1411525 6784469 := bbase (se 7 (by rfl) ⟨79505, by rfl⟩ : syracuseStep 6784469 = 159011) (by norm_num)
theorem B7153109 : Blo 1411525 7153109 := bbase (se 7 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 7153109 = 167651) (by norm_num)
theorem B1508825 : Blo 1411525 1508825 := bbase (se 2 (by rfl) ⟨565809, by rfl⟩ : syracuseStep 1508825 = 1131619) (by norm_num)
theorem B3180005 : Blo 1411525 3180005 := bbase (se 4 (by rfl) ⟨298125, by rfl⟩ : syracuseStep 3180005 = 596251) (by norm_num)
theorem B1787437 : Blo 1411525 1787437 := bbase (se 3 (by rfl) ⟨335144, by rfl⟩ : syracuseStep 1787437 = 670289) (by norm_num)
theorem B3180077 : Blo 1411525 3180077 := bbase (se 3 (by rfl) ⟨596264, by rfl⟩ : syracuseStep 3180077 = 1192529) (by norm_num)
theorem B4769333 : Blo 1411525 4769333 := bbase (se 5 (by rfl) ⟨223562, by rfl⟩ : syracuseStep 4769333 = 447125) (by norm_num)
theorem B2680381 : Blo 1411525 2680381 := bbase (se 3 (by rfl) ⟨502571, by rfl⟩ : syracuseStep 2680381 = 1005143) (by norm_num)
theorem B3180149 : Blo 1411525 3180149 := bbase (se 5 (by rfl) ⟨149069, by rfl⟩ : syracuseStep 3180149 = 298139) (by norm_num)
theorem B1451665 : Blo 1411525 1451665 := bbase (se 2 (by rfl) ⟨544374, by rfl⟩ : syracuseStep 1451665 = 1088749) (by norm_num)
theorem B27158165 : Blo 1411525 27158165 := bbase (se 6 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 27158165 = 1273039) (by norm_num)
theorem B1509013 : Blo 1411525 1509013 := bbase (se 6 (by rfl) ⟨35367, by rfl⟩ : syracuseStep 1509013 = 70735) (by norm_num)
theorem B4023989 : Blo 1411525 4023989 := bbase (se 5 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 4023989 = 377249) (by norm_num)
theorem B3180221 : Blo 1411525 3180221 := bbase (se 3 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 3180221 = 1192583) (by norm_num)
theorem B1787609 : Blo 1411525 1787609 := bbase (se 2 (by rfl) ⟨670353, by rfl⟩ : syracuseStep 1787609 = 1340707) (by norm_num)
theorem B3221213 : Blo 1411525 3221213 := bbase (se 3 (by rfl) ⟨603977, by rfl⟩ : syracuseStep 3221213 = 1207955) (by norm_num)
theorem B3180293 : Blo 1411525 3180293 := bbase (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) (by norm_num)
theorem B3573517 : Blo 1411525 3573517 := bbase (se 3 (by rfl) ⟨670034, by rfl⟩ : syracuseStep 3573517 = 1340069) (by norm_num)
theorem B1787665 : Blo 1411525 1787665 := bbase (se 2 (by rfl) ⟨670374, by rfl⟩ : syracuseStep 1787665 = 1340749) (by norm_num)
theorem B1509197 : Blo 1411525 1509197 := bbase (se 3 (by rfl) ⟨282974, by rfl⟩ : syracuseStep 1509197 = 565949) (by norm_num)
theorem B3180365 : Blo 1411525 3180365 := bbase (se 3 (by rfl) ⟨596318, by rfl⟩ : syracuseStep 3180365 = 1192637) (by norm_num)
theorem B3868517 : Blo 1411525 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B4835173 : Blo 1411525 4835173 := bbase (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) (by norm_num)
theorem B2680685 : Blo 1411525 2680685 := bbase (se 3 (by rfl) ⟨502628, by rfl⟩ : syracuseStep 2680685 = 1005257) (by norm_num)
theorem B1787761 : Blo 1411525 1787761 := bbase (se 2 (by rfl) ⟨670410, by rfl⟩ : syracuseStep 1787761 = 1340821) (by norm_num)
theorem B9045877 : Blo 1411525 9045877 := bbase (se 5 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 9045877 = 848051) (by norm_num)
theorem B3573629 : Blo 1411525 3573629 := bbase (se 3 (by rfl) ⟨670055, by rfl⟩ : syracuseStep 3573629 = 1340111) (by norm_num)
theorem B1697693 : Blo 1411525 1697693 := bbase (se 3 (by rfl) ⟨318317, by rfl⟩ : syracuseStep 1697693 = 636635) (by norm_num)
theorem B1697717 : Blo 1411525 1697717 := bbase (se 5 (by rfl) ⟨79580, by rfl⟩ : syracuseStep 1697717 = 159161) (by norm_num)
theorem B1812425 : Blo 1411525 1812425 := bbase (se 2 (by rfl) ⟨679659, by rfl⟩ : syracuseStep 1812425 = 1359319) (by norm_num)
theorem B4769765 : Blo 1411525 4769765 := bbase (se 4 (by rfl) ⟨447165, by rfl⟩ : syracuseStep 4769765 = 894331) (by norm_num)
theorem B3016693 : Blo 1411525 3016693 := bbase (se 5 (by rfl) ⟨141407, by rfl⟩ : syracuseStep 3016693 = 282815) (by norm_num)
theorem B5801989 : Blo 1411525 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B1787933 : Blo 1411525 1787933 := bbase (se 3 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 1787933 = 670475) (by norm_num)
theorem B3393589 : Blo 1411525 3393589 := bbase (se 5 (by rfl) ⟨159074, by rfl⟩ : syracuseStep 3393589 = 318149) (by norm_num)
theorem B3573821 : Blo 1411525 3573821 := bbase (se 3 (by rfl) ⟨670091, by rfl⟩ : syracuseStep 3573821 = 1340183) (by norm_num)
theorem B1787989 : Blo 1411525 1787989 := bbase (se 8 (by rfl) ⟨10476, by rfl⟩ : syracuseStep 1787989 = 20953) (by norm_num)
theorem B1788085 : Blo 1411525 1788085 := bbase (se 5 (by rfl) ⟨83816, by rfl⟩ : syracuseStep 1788085 = 167633) (by norm_num)
theorem B1698025 : Blo 1411525 1698025 := bbase (se 2 (by rfl) ⟨636759, by rfl⟩ : syracuseStep 1698025 = 1273519) (by norm_num)
theorem B1788257 : Blo 1411525 1788257 := bbase (se 2 (by rfl) ⟨670596, by rfl⟩ : syracuseStep 1788257 = 1341193) (by norm_num)
theorem B2263405 : Blo 1411525 2263405 := bbase (se 3 (by rfl) ⟨424388, by rfl⟩ : syracuseStep 2263405 = 848777) (by norm_num)
theorem B3574165 : Blo 1411525 3574165 := bbase (se 6 (by rfl) ⟨83769, by rfl⟩ : syracuseStep 3574165 = 167539) (by norm_num)
theorem B4770197 : Blo 1411525 4770197 := bbase (se 6 (by rfl) ⟨111801, by rfl⟩ : syracuseStep 4770197 = 223603) (by norm_num)
theorem B1788313 : Blo 1411525 1788313 := bbase (se 2 (by rfl) ⟨670617, by rfl⟩ : syracuseStep 1788313 = 1341235) (by norm_num)
theorem B4024741 : Blo 1411525 4024741 := bbase (se 4 (by rfl) ⟨377319, by rfl⟩ : syracuseStep 4024741 = 754639) (by norm_num)
theorem B1550765 : Blo 1411525 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B11446741 : Blo 1411525 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B3017189 : Blo 1411525 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B1788409 : Blo 1411525 1788409 := bbase (se 2 (by rfl) ⟨670653, by rfl⟩ : syracuseStep 1788409 = 1341307) (by norm_num)
theorem B2206205 : Blo 1411525 2206205 := bbase (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) (by norm_num)
theorem B3574277 : Blo 1411525 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B9054773 : Blo 1411525 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B2681437 : Blo 1411525 2681437 := bbase (se 3 (by rfl) ⟨502769, by rfl⟩ : syracuseStep 2681437 = 1005539) (by norm_num)
theorem B3394165 : Blo 1411525 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B1632901 : Blo 1411525 1632901 := bbase (se 4 (by rfl) ⟨153084, by rfl⟩ : syracuseStep 1632901 = 306169) (by norm_num)
theorem B3820165 : Blo 1411525 3820165 := bbase (se 4 (by rfl) ⟨358140, by rfl⟩ : syracuseStep 3820165 = 716281) (by norm_num)
theorem B1788581 : Blo 1411525 1788581 := bbase (se 4 (by rfl) ⟨167679, by rfl⟩ : syracuseStep 1788581 = 335359) (by norm_num)
theorem B3574469 : Blo 1411525 3574469 := bbase (se 4 (by rfl) ⟨335106, by rfl⟩ : syracuseStep 3574469 = 670213) (by norm_num)
theorem B3623629 : Blo 1411525 3623629 := bbase (se 3 (by rfl) ⟨679430, by rfl⟩ : syracuseStep 3623629 = 1358861) (by norm_num)
theorem B1788637 : Blo 1411525 1788637 := bbase (se 3 (by rfl) ⟨335369, by rfl⟩ : syracuseStep 1788637 = 670739) (by norm_num)
theorem B7154405 : Blo 1411525 7154405 := bbase (se 4 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 7154405 = 1341451) (by norm_num)
theorem B2681581 : Blo 1411525 2681581 := bbase (se 3 (by rfl) ⟨502796, by rfl⟩ : syracuseStep 2681581 = 1005593) (by norm_num)
theorem B2263853 : Blo 1411525 2263853 := bbase (se 3 (by rfl) ⟨424472, by rfl⟩ : syracuseStep 2263853 = 848945) (by norm_num)
theorem B1788733 : Blo 1411525 1788733 := bbase (se 3 (by rfl) ⟨335387, by rfl⟩ : syracuseStep 1788733 = 670775) (by norm_num)
theorem B4770629 : Blo 1411525 4770629 := bbase (se 4 (by rfl) ⟨447246, by rfl⟩ : syracuseStep 4770629 = 894493) (by norm_num)
theorem B2681741 : Blo 1411525 2681741 := bbase (se 3 (by rfl) ⟨502826, by rfl⟩ : syracuseStep 2681741 = 1005653) (by norm_num)
theorem B5090197 : Blo 1411525 5090197 := bbase (se 6 (by rfl) ⟨119301, by rfl⟩ : syracuseStep 5090197 = 238603) (by norm_num)
theorem B3394493 : Blo 1411525 3394493 := bbase (se 3 (by rfl) ⟨636467, by rfl⟩ : syracuseStep 3394493 = 1272935) (by norm_num)
theorem B1788905 : Blo 1411525 1788905 := bbase (se 2 (by rfl) ⟨670839, by rfl⟩ : syracuseStep 1788905 = 1341679) (by norm_num)
theorem B3394549 : Blo 1411525 3394549 := bbase (se 5 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 3394549 = 318239) (by norm_num)
theorem B3574813 : Blo 1411525 3574813 := bbase (se 3 (by rfl) ⟨670277, by rfl⟩ : syracuseStep 3574813 = 1340555) (by norm_num)
theorem B2681885 : Blo 1411525 2681885 := bbase (se 3 (by rfl) ⟨502853, by rfl⟩ : syracuseStep 2681885 = 1005707) (by norm_num)
theorem B1788961 : Blo 1411525 1788961 := bbase (se 2 (by rfl) ⟨670860, by rfl⟩ : syracuseStep 1788961 = 1341721) (by norm_num)
theorem B2862157 : Blo 1411525 2862157 := bbase (se 3 (by rfl) ⟨536654, by rfl⟩ : syracuseStep 2862157 = 1073309) (by norm_num)
theorem B7146629 : Blo 1411525 7146629 := bbase (se 4 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 7146629 = 1339993) (by norm_num)
theorem B3574925 : Blo 1411525 3574925 := bbase (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) (by norm_num)
theorem B8039573 : Blo 1411525 8039573 := bbase (se 6 (by rfl) ⟨188427, by rfl⟩ : syracuseStep 8039573 = 376855) (by norm_num)
theorem B3394781 : Blo 1411525 3394781 := bbase (se 3 (by rfl) ⟨636521, by rfl⟩ : syracuseStep 3394781 = 1273043) (by norm_num)
theorem B2010349 : Blo 1411525 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B2682173 : Blo 1411525 2682173 := bbase (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) (by norm_num)
theorem B3018053 : Blo 1411525 3018053 := bbase (se 4 (by rfl) ⟨282942, by rfl⟩ : syracuseStep 3018053 = 565885) (by norm_num)
theorem B3575117 : Blo 1411525 3575117 := bbase (se 3 (by rfl) ⟨670334, by rfl⟩ : syracuseStep 3575117 = 1340669) (by norm_num)
theorem B16100693 : Blo 1411525 16100693 := bbase (se 11 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 16100693 = 23585) (by norm_num)
theorem B3394973 : Blo 1411525 3394973 := bbase (se 3 (by rfl) ⟨636557, by rfl⟩ : syracuseStep 3394973 = 1273115) (by norm_num)
theorem B1863109 : Blo 1411525 1863109 := bbase (se 4 (by rfl) ⟨174666, by rfl⟩ : syracuseStep 1863109 = 349333) (by norm_num)
theorem B2682325 : Blo 1411525 2682325 := bbase (se 7 (by rfl) ⟨31433, by rfl⟩ : syracuseStep 2682325 = 62867) (by norm_num)
theorem B3018197 : Blo 1411525 3018197 := bbase (se 7 (by rfl) ⟨35369, by rfl⟩ : syracuseStep 3018197 = 70739) (by norm_num)
theorem B4525541 : Blo 1411525 4525541 := bbase (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) (by norm_num)
theorem B5361173 : Blo 1411525 5361173 := bbase (se 6 (by rfl) ⟨125652, by rfl⟩ : syracuseStep 5361173 = 251305) (by norm_num)
theorem B3059237 : Blo 1411525 3059237 := bbase (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) (by norm_num)
theorem B2010685 : Blo 1411525 2010685 := bbase (se 3 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 2010685 = 754007) (by norm_num)
theorem B3575461 : Blo 1411525 3575461 := bbase (se 4 (by rfl) ⟨335199, by rfl⟩ : syracuseStep 3575461 = 670399) (by norm_num)
theorem B2117309 : Blo 1411525 2117309 := bbase (se 3 (by rfl) ⟨396995, by rfl⟩ : syracuseStep 2117309 = 793991) (by norm_num)
theorem B2117333 : Blo 1411525 2117333 := bbase (se 7 (by rfl) ⟨24812, by rfl⟩ : syracuseStep 2117333 = 49625) (by norm_num)
theorem B2117357 : Blo 1411525 2117357 := bbase (se 3 (by rfl) ⟨397004, by rfl⟩ : syracuseStep 2117357 = 794009) (by norm_num)
theorem B2117381 : Blo 1411525 2117381 := bbase (se 4 (by rfl) ⟨198504, by rfl⟩ : syracuseStep 2117381 = 397009) (by norm_num)
theorem B2682629 : Blo 1411525 2682629 := bbase (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) (by norm_num)
theorem B2010901 : Blo 1411525 2010901 := bbase (se 6 (by rfl) ⟨47130, by rfl⟩ : syracuseStep 2010901 = 94261) (by norm_num)
theorem B3575573 : Blo 1411525 3575573 := bbase (se 6 (by rfl) ⟨83802, by rfl⟩ : syracuseStep 3575573 = 167605) (by norm_num)
theorem B2117405 : Blo 1411525 2117405 := bbase (se 3 (by rfl) ⟨397013, by rfl⟩ : syracuseStep 2117405 = 794027) (by norm_num)
theorem B2117429 : Blo 1411525 2117429 := bbase (se 5 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 2117429 = 198509) (by norm_num)
theorem B5361461 : Blo 1411525 5361461 := bbase (se 5 (by rfl) ⟨251318, by rfl⟩ : syracuseStep 5361461 = 502637) (by norm_num)
theorem B2117453 : Blo 1411525 2117453 := bbase (se 3 (by rfl) ⟨397022, by rfl⟩ : syracuseStep 2117453 = 794045) (by norm_num)
theorem B2117477 : Blo 1411525 2117477 := bbase (se 4 (by rfl) ⟨198513, by rfl⟩ : syracuseStep 2117477 = 397027) (by norm_num)
theorem B2117501 : Blo 1411525 2117501 := bbase (se 3 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 2117501 = 794063) (by norm_num)
theorem B2117525 : Blo 1411525 2117525 := bbase (se 6 (by rfl) ⟨49629, by rfl⟩ : syracuseStep 2117525 = 99259) (by norm_num)
theorem B2117549 : Blo 1411525 2117549 := bbase (se 3 (by rfl) ⟨397040, by rfl⟩ : syracuseStep 2117549 = 794081) (by norm_num)
theorem B2117573 : Blo 1411525 2117573 := bbase (se 4 (by rfl) ⟨198522, by rfl⟩ : syracuseStep 2117573 = 397045) (by norm_num)
theorem B3575765 : Blo 1411525 3575765 := bbase (se 7 (by rfl) ⟨41903, by rfl⟩ : syracuseStep 3575765 = 83807) (by norm_num)
theorem B2117597 : Blo 1411525 2117597 := bbase (se 3 (by rfl) ⟨397049, by rfl⟩ : syracuseStep 2117597 = 794099) (by norm_num)
theorem B2117621 : Blo 1411525 2117621 := bbase (se 5 (by rfl) ⟨99263, by rfl⟩ : syracuseStep 2117621 = 198527) (by norm_num)
theorem B7155701 : Blo 1411525 7155701 := bbase (se 5 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 7155701 = 670847) (by norm_num)
theorem B2117645 : Blo 1411525 2117645 := bbase (se 3 (by rfl) ⟨397058, by rfl⟩ : syracuseStep 2117645 = 794117) (by norm_num)
theorem B2117669 : Blo 1411525 2117669 := bbase (se 4 (by rfl) ⟨198531, by rfl⟩ : syracuseStep 2117669 = 397063) (by norm_num)
theorem B10727477 : Blo 1411525 10727477 := bbase (se 5 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 10727477 = 1005701) (by norm_num)
theorem B2117693 : Blo 1411525 2117693 := bbase (se 3 (by rfl) ⟨397067, by rfl⟩ : syracuseStep 2117693 = 794135) (by norm_num)
theorem B2117717 : Blo 1411525 2117717 := bbase (se 8 (by rfl) ⟨12408, by rfl⟩ : syracuseStep 2117717 = 24817) (by norm_num)
theorem B2117741 : Blo 1411525 2117741 := bbase (se 3 (by rfl) ⟨397076, by rfl⟩ : syracuseStep 2117741 = 794153) (by norm_num)
theorem B7245941 : Blo 1411525 7245941 := bbase (se 5 (by rfl) ⟨339653, by rfl⟩ : syracuseStep 7245941 = 679307) (by norm_num)
theorem B2117765 : Blo 1411525 2117765 := bbase (se 4 (by rfl) ⟨198540, by rfl⟩ : syracuseStep 2117765 = 397081) (by norm_num)
theorem B2011277 : Blo 1411525 2011277 := bbase (se 3 (by rfl) ⟨377114, by rfl⟩ : syracuseStep 2011277 = 754229) (by norm_num)
theorem B2117789 : Blo 1411525 2117789 := bbase (se 3 (by rfl) ⟨397085, by rfl⟩ : syracuseStep 2117789 = 794171) (by norm_num)
theorem B2117813 : Blo 1411525 2117813 := bbase (se 5 (by rfl) ⟨99272, by rfl⟩ : syracuseStep 2117813 = 198545) (by norm_num)
theorem B6787253 : Blo 1411525 6787253 := bbase (se 5 (by rfl) ⟨318152, by rfl⟩ : syracuseStep 6787253 = 636305) (by norm_num)
theorem B2117837 : Blo 1411525 2117837 := bbase (se 3 (by rfl) ⟨397094, by rfl⟩ : syracuseStep 2117837 = 794189) (by norm_num)
theorem B2117861 : Blo 1411525 2117861 := bbase (se 4 (by rfl) ⟨198549, by rfl⟩ : syracuseStep 2117861 = 397099) (by norm_num)
theorem B2117885 : Blo 1411525 2117885 := bbase (se 3 (by rfl) ⟨397103, by rfl⟩ : syracuseStep 2117885 = 794207) (by norm_num)
theorem B2117909 : Blo 1411525 2117909 := bbase (se 6 (by rfl) ⟨49638, by rfl⟩ : syracuseStep 2117909 = 99277) (by norm_num)
theorem B2117933 : Blo 1411525 2117933 := bbase (se 3 (by rfl) ⟨397112, by rfl⟩ : syracuseStep 2117933 = 794225) (by norm_num)
theorem B3576109 : Blo 1411525 3576109 := bbase (se 3 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 3576109 = 1341041) (by norm_num)
theorem B2117957 : Blo 1411525 2117957 := bbase (se 4 (by rfl) ⟨198558, by rfl⟩ : syracuseStep 2117957 = 397117) (by norm_num)
theorem B2117981 : Blo 1411525 2117981 := bbase (se 3 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 2117981 = 794243) (by norm_num)
theorem B3395933 : Blo 1411525 3395933 := bbase (se 3 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 3395933 = 1273475) (by norm_num)
theorem B2118005 : Blo 1411525 2118005 := bbase (se 5 (by rfl) ⟨99281, by rfl⟩ : syracuseStep 2118005 = 198563) (by norm_num)
theorem B6033797 : Blo 1411525 6033797 := bbase (se 4 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 6033797 = 1131337) (by norm_num)
theorem B2118029 : Blo 1411525 2118029 := bbase (se 3 (by rfl) ⟨397130, by rfl⟩ : syracuseStep 2118029 = 794261) (by norm_num)
theorem B7147925 : Blo 1411525 7147925 := bbase (se 6 (by rfl) ⟨167529, by rfl⟩ : syracuseStep 7147925 = 335059) (by norm_num)
theorem B3576221 : Blo 1411525 3576221 := bbase (se 3 (by rfl) ⟨670541, by rfl⟩ : syracuseStep 3576221 = 1341083) (by norm_num)
theorem B2118053 : Blo 1411525 2118053 := bbase (se 4 (by rfl) ⟨198567, by rfl⟩ : syracuseStep 2118053 = 397135) (by norm_num)
theorem B2118077 : Blo 1411525 2118077 := bbase (se 3 (by rfl) ⟨397139, by rfl⟩ : syracuseStep 2118077 = 794279) (by norm_num)
theorem B1528265 : Blo 1411525 1528265 := bbase (se 2 (by rfl) ⟨573099, by rfl⟩ : syracuseStep 1528265 = 1146199) (by norm_num)
theorem B10719701 : Blo 1411525 10719701 := bbase (se 7 (by rfl) ⟨125621, by rfl⟩ : syracuseStep 10719701 = 251243) (by norm_num)
theorem B2118101 : Blo 1411525 2118101 := bbase (se 7 (by rfl) ⟨24821, by rfl⟩ : syracuseStep 2118101 = 49643) (by norm_num)
theorem B2118125 : Blo 1411525 2118125 := bbase (se 3 (by rfl) ⟨397148, by rfl⟩ : syracuseStep 2118125 = 794297) (by norm_num)
theorem B4764149 : Blo 1411525 4764149 := bbase (se 5 (by rfl) ⟨223319, by rfl⟩ : syracuseStep 4764149 = 446639) (by norm_num)
theorem B2683381 : Blo 1411525 2683381 := bbase (se 5 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 2683381 = 251567) (by norm_num)
theorem B2118149 : Blo 1411525 2118149 := bbase (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) (by norm_num)
theorem B2118173 : Blo 1411525 2118173 := bbase (se 3 (by rfl) ⟨397157, by rfl⟩ : syracuseStep 2118173 = 794315) (by norm_num)
theorem B2118197 : Blo 1411525 2118197 := bbase (se 5 (by rfl) ⟨99290, by rfl⟩ : syracuseStep 2118197 = 198581) (by norm_num)
theorem B2118221 : Blo 1411525 2118221 := bbase (se 3 (by rfl) ⟨397166, by rfl⟩ : syracuseStep 2118221 = 794333) (by norm_num)
theorem B3576413 : Blo 1411525 3576413 := bbase (se 3 (by rfl) ⟨670577, by rfl⟩ : syracuseStep 3576413 = 1341155) (by norm_num)
theorem B2118245 : Blo 1411525 2118245 := bbase (se 4 (by rfl) ⟨198585, by rfl⟩ : syracuseStep 2118245 = 397171) (by norm_num)
theorem B2118269 : Blo 1411525 2118269 := bbase (se 3 (by rfl) ⟨397175, by rfl⟩ : syracuseStep 2118269 = 794351) (by norm_num)
theorem B2118293 : Blo 1411525 2118293 := bbase (se 6 (by rfl) ⟨49647, by rfl⟩ : syracuseStep 2118293 = 99295) (by norm_num)
theorem B2118317 : Blo 1411525 2118317 := bbase (se 3 (by rfl) ⟨397184, by rfl⟩ : syracuseStep 2118317 = 794369) (by norm_num)
theorem B2118341 : Blo 1411525 2118341 := bbase (se 4 (by rfl) ⟨198594, by rfl⟩ : syracuseStep 2118341 = 397189) (by norm_num)
theorem B2118365 : Blo 1411525 2118365 := bbase (se 3 (by rfl) ⟨397193, by rfl⟩ : syracuseStep 2118365 = 794387) (by norm_num)
theorem B2118389 : Blo 1411525 2118389 := bbase (se 5 (by rfl) ⟨99299, by rfl⟩ : syracuseStep 2118389 = 198599) (by norm_num)
theorem B2118413 : Blo 1411525 2118413 := bbase (se 3 (by rfl) ⟨397202, by rfl⟩ : syracuseStep 2118413 = 794405) (by norm_num)
theorem B2118437 : Blo 1411525 2118437 := bbase (se 4 (by rfl) ⟨198603, by rfl⟩ : syracuseStep 2118437 = 397207) (by norm_num)
theorem B4526885 : Blo 1411525 4526885 := bbase (se 4 (by rfl) ⟨424395, by rfl⟩ : syracuseStep 4526885 = 848791) (by norm_num)
theorem B2118461 : Blo 1411525 2118461 := bbase (se 3 (by rfl) ⟨397211, by rfl⟩ : syracuseStep 2118461 = 794423) (by norm_num)
theorem B2118485 : Blo 1411525 2118485 := bbase (se 9 (by rfl) ⟨6206, by rfl⟩ : syracuseStep 2118485 = 12413) (by norm_num)
theorem B2118509 : Blo 1411525 2118509 := bbase (se 3 (by rfl) ⟨397220, by rfl⟩ : syracuseStep 2118509 = 794441) (by norm_num)
theorem B2118533 : Blo 1411525 2118533 := bbase (se 4 (by rfl) ⟨198612, by rfl⟩ : syracuseStep 2118533 = 397225) (by norm_num)
theorem B2118557 : Blo 1411525 2118557 := bbase (se 3 (by rfl) ⟨397229, by rfl⟩ : syracuseStep 2118557 = 794459) (by norm_num)
theorem B4764581 : Blo 1411525 4764581 := bbase (se 4 (by rfl) ⟨446679, by rfl⟩ : syracuseStep 4764581 = 893359) (by norm_num)
theorem B2118581 : Blo 1411525 2118581 := bbase (se 5 (by rfl) ⟨99308, by rfl⟩ : syracuseStep 2118581 = 198617) (by norm_num)
theorem B3576757 : Blo 1411525 3576757 := bbase (se 5 (by rfl) ⟨167660, by rfl⟩ : syracuseStep 3576757 = 335321) (by norm_num)
theorem B2118605 : Blo 1411525 2118605 := bbase (se 3 (by rfl) ⟨397238, by rfl⟩ : syracuseStep 2118605 = 794477) (by norm_num)
theorem B5362645 : Blo 1411525 5362645 := bbase (se 7 (by rfl) ⟨62843, by rfl⟩ : syracuseStep 5362645 = 125687) (by norm_num)
theorem B2118629 : Blo 1411525 2118629 := bbase (se 4 (by rfl) ⟨198621, by rfl⟩ : syracuseStep 2118629 = 397243) (by norm_num)
theorem B2118653 : Blo 1411525 2118653 := bbase (se 3 (by rfl) ⟨397247, by rfl⟩ : syracuseStep 2118653 = 794495) (by norm_num)
theorem B2118677 : Blo 1411525 2118677 := bbase (se 6 (by rfl) ⟨49656, by rfl⟩ : syracuseStep 2118677 = 99313) (by norm_num)
theorem B3576869 : Blo 1411525 3576869 := bbase (se 4 (by rfl) ⟨335331, by rfl⟩ : syracuseStep 3576869 = 670663) (by norm_num)
theorem B2118701 : Blo 1411525 2118701 := bbase (se 3 (by rfl) ⟨397256, by rfl⟩ : syracuseStep 2118701 = 794513) (by norm_num)
theorem B2544701 : Blo 1411525 2544701 := bbase (se 3 (by rfl) ⟨477131, by rfl⟩ : syracuseStep 2544701 = 954263) (by norm_num)
theorem B1610813 : Blo 1411525 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B2118725 : Blo 1411525 2118725 := bbase (se 4 (by rfl) ⟨198630, by rfl⟩ : syracuseStep 2118725 = 397261) (by norm_num)
theorem B2118749 : Blo 1411525 2118749 := bbase (se 3 (by rfl) ⟨397265, by rfl⟩ : syracuseStep 2118749 = 794531) (by norm_num)
theorem B10179701 : Blo 1411525 10179701 := bbase (se 5 (by rfl) ⟨477173, by rfl⟩ : syracuseStep 10179701 = 954347) (by norm_num)
theorem B2118773 : Blo 1411525 2118773 := bbase (se 5 (by rfl) ⟨99317, by rfl⟩ : syracuseStep 2118773 = 198635) (by norm_num)
theorem B2118797 : Blo 1411525 2118797 := bbase (se 3 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 2118797 = 794549) (by norm_num)
theorem B2118821 : Blo 1411525 2118821 := bbase (se 4 (by rfl) ⟨198639, by rfl⟩ : syracuseStep 2118821 = 397279) (by norm_num)
theorem B2118845 : Blo 1411525 2118845 := bbase (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) (by norm_num)
theorem B2118869 : Blo 1411525 2118869 := bbase (se 7 (by rfl) ⟨24830, by rfl⟩ : syracuseStep 2118869 = 49661) (by norm_num)
theorem B10876117 : Blo 1411525 10876117 := bbase (se 7 (by rfl) ⟨127454, by rfl⟩ : syracuseStep 10876117 = 254909) (by norm_num)
theorem B3577061 : Blo 1411525 3577061 := bbase (se 4 (by rfl) ⟨335349, by rfl⟩ : syracuseStep 3577061 = 670699) (by norm_num)
theorem B2118893 : Blo 1411525 2118893 := bbase (se 3 (by rfl) ⟨397292, by rfl⟩ : syracuseStep 2118893 = 794585) (by norm_num)
theorem B5362949 : Blo 1411525 5362949 := bbase (se 4 (by rfl) ⟨502776, by rfl⟩ : syracuseStep 5362949 = 1005553) (by norm_num)
theorem B2118917 : Blo 1411525 2118917 := bbase (se 4 (by rfl) ⟨198648, by rfl⟩ : syracuseStep 2118917 = 397297) (by norm_num)
theorem B2118941 : Blo 1411525 2118941 := bbase (se 3 (by rfl) ⟨397301, by rfl⟩ : syracuseStep 2118941 = 794603) (by norm_num)
theorem B8041781 : Blo 1411525 8041781 := bbase (se 5 (by rfl) ⟨376958, by rfl⟩ : syracuseStep 8041781 = 753917) (by norm_num)
theorem B2118965 : Blo 1411525 2118965 := bbase (se 5 (by rfl) ⟨99326, by rfl⟩ : syracuseStep 2118965 = 198653) (by norm_num)
theorem B2118989 : Blo 1411525 2118989 := bbase (se 3 (by rfl) ⟨397310, by rfl⟩ : syracuseStep 2118989 = 794621) (by norm_num)
theorem B4765013 : Blo 1411525 4765013 := bbase (se 13 (by rfl) ⟨872, by rfl⟩ : syracuseStep 4765013 = 1745) (by norm_num)
theorem B2119013 : Blo 1411525 2119013 := bbase (se 4 (by rfl) ⟨198657, by rfl⟩ : syracuseStep 2119013 = 397315) (by norm_num)
theorem B2119037 : Blo 1411525 2119037 := bbase (se 3 (by rfl) ⟨397319, by rfl⟩ : syracuseStep 2119037 = 794639) (by norm_num)
theorem B2119061 : Blo 1411525 2119061 := bbase (se 6 (by rfl) ⟨49665, by rfl⟩ : syracuseStep 2119061 = 99331) (by norm_num)
theorem B1430957 : Blo 1411525 1430957 := bbase (se 3 (by rfl) ⟨268304, by rfl⟩ : syracuseStep 1430957 = 536609) (by norm_num)
theorem B2119085 : Blo 1411525 2119085 := bbase (se 3 (by rfl) ⟨397328, by rfl⟩ : syracuseStep 2119085 = 794657) (by norm_num)
theorem B2119109 : Blo 1411525 2119109 := bbase (se 4 (by rfl) ⟨198666, by rfl⟩ : syracuseStep 2119109 = 397333) (by norm_num)
theorem B2119133 : Blo 1411525 2119133 := bbase (se 3 (by rfl) ⟨397337, by rfl⟩ : syracuseStep 2119133 = 794675) (by norm_num)
theorem B2119157 : Blo 1411525 2119157 := bbase (se 5 (by rfl) ⟨99335, by rfl⟩ : syracuseStep 2119157 = 198671) (by norm_num)
theorem B2119181 : Blo 1411525 2119181 := bbase (se 3 (by rfl) ⟨397346, by rfl⟩ : syracuseStep 2119181 = 794693) (by norm_num)
theorem B3175973 : Blo 1411525 3175973 := bbase (se 4 (by rfl) ⟨297747, by rfl⟩ : syracuseStep 3175973 = 595495) (by norm_num)
theorem B2119205 : Blo 1411525 2119205 := bbase (se 4 (by rfl) ⟨198675, by rfl⟩ : syracuseStep 2119205 = 397351) (by norm_num)
theorem B2119229 : Blo 1411525 2119229 := bbase (se 3 (by rfl) ⟨397355, by rfl⟩ : syracuseStep 2119229 = 794711) (by norm_num)
theorem B3577405 : Blo 1411525 3577405 := bbase (se 3 (by rfl) ⟨670763, by rfl⟩ : syracuseStep 3577405 = 1341527) (by norm_num)
theorem B4019797 : Blo 1411525 4019797 := bbase (se 8 (by rfl) ⟨23553, by rfl⟩ : syracuseStep 4019797 = 47107) (by norm_num)
theorem B2119253 : Blo 1411525 2119253 := bbase (se 8 (by rfl) ⟨12417, by rfl⟩ : syracuseStep 2119253 = 24835) (by norm_num)
theorem B3176045 : Blo 1411525 3176045 := bbase (se 3 (by rfl) ⟨595508, by rfl⟩ : syracuseStep 3176045 = 1191017) (by norm_num)
theorem B2119277 : Blo 1411525 2119277 := bbase (se 3 (by rfl) ⟨397364, by rfl⟩ : syracuseStep 2119277 = 794729) (by norm_num)
theorem B2119301 : Blo 1411525 2119301 := bbase (se 4 (by rfl) ⟨198684, by rfl⟩ : syracuseStep 2119301 = 397369) (by norm_num)
theorem B2119325 : Blo 1411525 2119325 := bbase (se 3 (by rfl) ⟨397373, by rfl⟩ : syracuseStep 2119325 = 794747) (by norm_num)
theorem B7149221 : Blo 1411525 7149221 := bbase (se 4 (by rfl) ⟨670239, by rfl⟩ : syracuseStep 7149221 = 1340479) (by norm_num)
theorem B5232293 : Blo 1411525 5232293 := bbase (se 4 (by rfl) ⟨490527, by rfl⟩ : syracuseStep 5232293 = 981055) (by norm_num)
theorem B3577517 : Blo 1411525 3577517 := bbase (se 3 (by rfl) ⟨670784, by rfl⟩ : syracuseStep 3577517 = 1341569) (by norm_num)
theorem B1431217 : Blo 1411525 1431217 := bbase (se 2 (by rfl) ⟨536706, by rfl⟩ : syracuseStep 1431217 = 1073413) (by norm_num)
theorem B3176117 : Blo 1411525 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B2119349 : Blo 1411525 2119349 := bbase (se 5 (by rfl) ⟨99344, by rfl⟩ : syracuseStep 2119349 = 198689) (by norm_num)
theorem B2119373 : Blo 1411525 2119373 := bbase (se 3 (by rfl) ⟨397382, by rfl⟩ : syracuseStep 2119373 = 794765) (by norm_num)
theorem B2119397 : Blo 1411525 2119397 := bbase (se 4 (by rfl) ⟨198693, by rfl⟩ : syracuseStep 2119397 = 397387) (by norm_num)
theorem B5093093 : Blo 1411525 5093093 := bbase (se 4 (by rfl) ⟨477477, by rfl⟩ : syracuseStep 5093093 = 954955) (by norm_num)
theorem B3176189 : Blo 1411525 3176189 := bbase (se 3 (by rfl) ⟨595535, by rfl⟩ : syracuseStep 3176189 = 1191071) (by norm_num)
theorem B2119421 : Blo 1411525 2119421 := bbase (se 3 (by rfl) ⟨397391, by rfl⟩ : syracuseStep 2119421 = 794783) (by norm_num)
theorem B4765445 : Blo 1411525 4765445 := bbase (se 4 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 4765445 = 893521) (by norm_num)
theorem B1611533 : Blo 1411525 1611533 := bbase (se 3 (by rfl) ⟨302162, by rfl⟩ : syracuseStep 1611533 = 604325) (by norm_num)
theorem B2119445 : Blo 1411525 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B2119469 : Blo 1411525 2119469 := bbase (se 3 (by rfl) ⟨397400, by rfl⟩ : syracuseStep 2119469 = 794801) (by norm_num)
theorem B3176261 : Blo 1411525 3176261 := bbase (se 4 (by rfl) ⟨297774, by rfl⟩ : syracuseStep 3176261 = 595549) (by norm_num)
theorem B2119493 : Blo 1411525 2119493 := bbase (se 4 (by rfl) ⟨198702, by rfl⟩ : syracuseStep 2119493 = 397405) (by norm_num)
theorem B2119517 : Blo 1411525 2119517 := bbase (se 3 (by rfl) ⟨397409, by rfl⟩ : syracuseStep 2119517 = 794819) (by norm_num)
theorem B3577709 : Blo 1411525 3577709 := bbase (se 3 (by rfl) ⟨670820, by rfl⟩ : syracuseStep 3577709 = 1341641) (by norm_num)
theorem B2119541 : Blo 1411525 2119541 := bbase (se 5 (by rfl) ⟨99353, by rfl⟩ : syracuseStep 2119541 = 198707) (by norm_num)
theorem B3176333 : Blo 1411525 3176333 := bbase (se 3 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 3176333 = 1191125) (by norm_num)
theorem B2119565 : Blo 1411525 2119565 := bbase (se 3 (by rfl) ⟨397418, by rfl⟩ : syracuseStep 2119565 = 794837) (by norm_num)
theorem B2119589 : Blo 1411525 2119589 := bbase (se 4 (by rfl) ⟨198711, by rfl⟩ : syracuseStep 2119589 = 397423) (by norm_num)
theorem B8591285 : Blo 1411525 8591285 := bbase (se 5 (by rfl) ⟨402716, by rfl⟩ : syracuseStep 8591285 = 805433) (by norm_num)
theorem B2119613 : Blo 1411525 2119613 := bbase (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) (by norm_num)
theorem B3176405 : Blo 1411525 3176405 := bbase (se 7 (by rfl) ⟨37223, by rfl⟩ : syracuseStep 3176405 = 74447) (by norm_num)
theorem B2119637 : Blo 1411525 2119637 := bbase (se 7 (by rfl) ⟨24839, by rfl⟩ : syracuseStep 2119637 = 49679) (by norm_num)
theorem B1431533 : Blo 1411525 1431533 := bbase (se 3 (by rfl) ⟨268412, by rfl⟩ : syracuseStep 1431533 = 536825) (by norm_num)
theorem B2119661 : Blo 1411525 2119661 := bbase (se 3 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 2119661 = 794873) (by norm_num)
theorem B2119685 : Blo 1411525 2119685 := bbase (se 4 (by rfl) ⟨198720, by rfl⟩ : syracuseStep 2119685 = 397441) (by norm_num)
theorem B5093381 : Blo 1411525 5093381 := bbase (se 4 (by rfl) ⟨477504, by rfl⟩ : syracuseStep 5093381 = 955009) (by norm_num)
theorem B3176477 : Blo 1411525 3176477 := bbase (se 3 (by rfl) ⟨595589, by rfl⟩ : syracuseStep 3176477 = 1191179) (by norm_num)
theorem B2119709 : Blo 1411525 2119709 := bbase (se 3 (by rfl) ⟨397445, by rfl⟩ : syracuseStep 2119709 = 794891) (by norm_num)
theorem B4831285 : Blo 1411525 4831285 := bbase (se 5 (by rfl) ⟨226466, by rfl⟩ : syracuseStep 4831285 = 452933) (by norm_num)
theorem B2119733 : Blo 1411525 2119733 := bbase (se 5 (by rfl) ⟨99362, by rfl⟩ : syracuseStep 2119733 = 198725) (by norm_num)
theorem B2119757 : Blo 1411525 2119757 := bbase (se 3 (by rfl) ⟨397454, by rfl⟩ : syracuseStep 2119757 = 794909) (by norm_num)
theorem B3176549 : Blo 1411525 3176549 := bbase (se 4 (by rfl) ⟨297801, by rfl⟩ : syracuseStep 3176549 = 595603) (by norm_num)
theorem B2119781 : Blo 1411525 2119781 := bbase (se 4 (by rfl) ⟨198729, by rfl⟩ : syracuseStep 2119781 = 397459) (by norm_num)
theorem B6035573 : Blo 1411525 6035573 := bbase (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) (by norm_num)
theorem B2119805 : Blo 1411525 2119805 := bbase (se 3 (by rfl) ⟨397463, by rfl⟩ : syracuseStep 2119805 = 794927) (by norm_num)
theorem B2119829 : Blo 1411525 2119829 := bbase (se 6 (by rfl) ⟨49683, by rfl⟩ : syracuseStep 2119829 = 99367) (by norm_num)
theorem B3176621 : Blo 1411525 3176621 := bbase (se 3 (by rfl) ⟨595616, by rfl⟩ : syracuseStep 3176621 = 1191233) (by norm_num)
theorem B2119853 : Blo 1411525 2119853 := bbase (se 3 (by rfl) ⟨397472, by rfl⟩ : syracuseStep 2119853 = 794945) (by norm_num)
theorem B4765877 : Blo 1411525 4765877 := bbase (se 5 (by rfl) ⟨223400, by rfl⟩ : syracuseStep 4765877 = 446801) (by norm_num)
theorem B2119877 : Blo 1411525 2119877 := bbase (se 4 (by rfl) ⟨198738, by rfl⟩ : syracuseStep 2119877 = 397477) (by norm_num)
theorem B7633109 : Blo 1411525 7633109 := bbase (se 7 (by rfl) ⟨89450, by rfl⟩ : syracuseStep 7633109 = 178901) (by norm_num)
theorem B2119901 : Blo 1411525 2119901 := bbase (se 3 (by rfl) ⟨397481, by rfl⟩ : syracuseStep 2119901 = 794963) (by norm_num)
theorem B2382061 : Blo 1411525 2382061 := bbase (se 3 (by rfl) ⟨446636, by rfl⟩ : syracuseStep 2382061 = 893273) (by norm_num)
theorem B3176693 : Blo 1411525 3176693 := bbase (se 5 (by rfl) ⟨148907, by rfl⟩ : syracuseStep 3176693 = 297815) (by norm_num)
theorem B2119925 : Blo 1411525 2119925 := bbase (se 5 (by rfl) ⟨99371, by rfl⟩ : syracuseStep 2119925 = 198743) (by norm_num)
theorem B2119949 : Blo 1411525 2119949 := bbase (se 3 (by rfl) ⟨397490, by rfl⟩ : syracuseStep 2119949 = 794981) (by norm_num)
theorem B2119973 : Blo 1411525 2119973 := bbase (se 4 (by rfl) ⟨198747, by rfl⟩ : syracuseStep 2119973 = 397495) (by norm_num)
theorem B1431865 : Blo 1411525 1431865 := bbase (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) (by norm_num)
theorem B3176765 : Blo 1411525 3176765 := bbase (se 3 (by rfl) ⟨595643, by rfl⟩ : syracuseStep 3176765 = 1191287) (by norm_num)
theorem B2119997 : Blo 1411525 2119997 := bbase (se 3 (by rfl) ⟨397499, by rfl⟩ : syracuseStep 2119997 = 794999) (by norm_num)
theorem B2382149 : Blo 1411525 2382149 := bbase (se 4 (by rfl) ⟨223326, by rfl⟩ : syracuseStep 2382149 = 446653) (by norm_num)
theorem B2120021 : Blo 1411525 2120021 := bbase (se 10 (by rfl) ⟨3105, by rfl⟩ : syracuseStep 2120021 = 6211) (by norm_num)
theorem B2120045 : Blo 1411525 2120045 := bbase (se 3 (by rfl) ⟨397508, by rfl⟩ : syracuseStep 2120045 = 795017) (by norm_num)
theorem B12073333 : Blo 1411525 12073333 := bbase (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) (by norm_num)
theorem B3176837 : Blo 1411525 3176837 := bbase (se 4 (by rfl) ⟨297828, by rfl⟩ : syracuseStep 3176837 = 595657) (by norm_num)
theorem B2120069 : Blo 1411525 2120069 := bbase (se 4 (by rfl) ⟨198756, by rfl⟩ : syracuseStep 2120069 = 397513) (by norm_num)
theorem B2120093 : Blo 1411525 2120093 := bbase (se 3 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 2120093 = 795035) (by norm_num)
theorem B2685349 : Blo 1411525 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B2120117 : Blo 1411525 2120117 := bbase (se 5 (by rfl) ⟨99380, by rfl⟩ : syracuseStep 2120117 = 198761) (by norm_num)
theorem B2382277 : Blo 1411525 2382277 := bbase (se 4 (by rfl) ⟨223338, by rfl⟩ : syracuseStep 2382277 = 446677) (by norm_num)
theorem B3176909 : Blo 1411525 3176909 := bbase (se 3 (by rfl) ⟨595670, by rfl⟩ : syracuseStep 3176909 = 1191341) (by norm_num)
theorem B2120141 : Blo 1411525 2120141 := bbase (se 3 (by rfl) ⟨397526, by rfl⟩ : syracuseStep 2120141 = 795053) (by norm_num)
theorem B2120165 : Blo 1411525 2120165 := bbase (se 4 (by rfl) ⟨198765, by rfl⟩ : syracuseStep 2120165 = 397531) (by norm_num)
theorem B2120189 : Blo 1411525 2120189 := bbase (se 3 (by rfl) ⟨397535, by rfl⟩ : syracuseStep 2120189 = 795071) (by norm_num)
theorem B3176981 : Blo 1411525 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B2120213 : Blo 1411525 2120213 := bbase (se 6 (by rfl) ⟨49692, by rfl⟩ : syracuseStep 2120213 = 99385) (by norm_num)
theorem B2382365 : Blo 1411525 2382365 := bbase (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) (by norm_num)
theorem B2120237 : Blo 1411525 2120237 := bbase (se 3 (by rfl) ⟨397544, by rfl⟩ : syracuseStep 2120237 = 795089) (by norm_num)
theorem B1432117 : Blo 1411525 1432117 := bbase (se 5 (by rfl) ⟨67130, by rfl⟩ : syracuseStep 1432117 = 134261) (by norm_num)
theorem B2120261 : Blo 1411525 2120261 := bbase (se 4 (by rfl) ⟨198774, by rfl⟩ : syracuseStep 2120261 = 397549) (by norm_num)
theorem B3177053 : Blo 1411525 3177053 := bbase (se 3 (by rfl) ⟨595697, by rfl⟩ : syracuseStep 3177053 = 1191395) (by norm_num)
theorem B2120285 : Blo 1411525 2120285 := bbase (se 3 (by rfl) ⟨397553, by rfl⟩ : syracuseStep 2120285 = 795107) (by norm_num)
theorem B4766309 : Blo 1411525 4766309 := bbase (se 4 (by rfl) ⟨446841, by rfl⟩ : syracuseStep 4766309 = 893683) (by norm_num)
theorem B4356709 : Blo 1411525 4356709 := bbase (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) (by norm_num)
theorem B2382493 : Blo 1411525 2382493 := bbase (se 3 (by rfl) ⟨446717, by rfl⟩ : syracuseStep 2382493 = 893435) (by norm_num)
theorem B3177125 : Blo 1411525 3177125 := bbase (se 4 (by rfl) ⟨297855, by rfl⟩ : syracuseStep 3177125 = 595711) (by norm_num)
theorem B3177197 : Blo 1411525 3177197 := bbase (se 3 (by rfl) ⟨595724, by rfl⟩ : syracuseStep 3177197 = 1191449) (by norm_num)
theorem B2382581 : Blo 1411525 2382581 := bbase (se 5 (by rfl) ⟨111683, by rfl⟩ : syracuseStep 2382581 = 223367) (by norm_num)
theorem B11451125 : Blo 1411525 11451125 := bbase (se 5 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 11451125 = 1073543) (by norm_num)
theorem B1587973 : Blo 1411525 1587973 := bbase (se 4 (by rfl) ⟨148872, by rfl⟩ : syracuseStep 1587973 = 297745) (by norm_num)
theorem B1588009 : Blo 1411525 1588009 := bbase (se 2 (by rfl) ⟨595503, by rfl⟩ : syracuseStep 1588009 = 1191007) (by norm_num)
theorem B3177269 : Blo 1411525 3177269 := bbase (se 5 (by rfl) ⟨148934, by rfl⟩ : syracuseStep 3177269 = 297869) (by norm_num)
theorem B1588045 : Blo 1411525 1588045 := bbase (se 3 (by rfl) ⟨297758, by rfl⟩ : syracuseStep 1588045 = 595517) (by norm_num)
theorem B1588081 : Blo 1411525 1588081 := bbase (se 2 (by rfl) ⟨595530, by rfl⟩ : syracuseStep 1588081 = 1191061) (by norm_num)
theorem B2382709 : Blo 1411525 2382709 := bbase (se 5 (by rfl) ⟨111689, by rfl⟩ : syracuseStep 2382709 = 223379) (by norm_num)
theorem B3177341 : Blo 1411525 3177341 := bbase (se 3 (by rfl) ⟨595751, by rfl⟩ : syracuseStep 3177341 = 1191503) (by norm_num)
theorem B1588117 : Blo 1411525 1588117 := bbase (se 6 (by rfl) ⟨37221, by rfl⟩ : syracuseStep 1588117 = 74443) (by norm_num)
theorem B7150517 : Blo 1411525 7150517 := bbase (se 5 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 7150517 = 670361) (by norm_num)
theorem B1588153 : Blo 1411525 1588153 := bbase (se 2 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 1588153 = 1191115) (by norm_num)
theorem B3177413 : Blo 1411525 3177413 := bbase (se 4 (by rfl) ⟨297882, by rfl⟩ : syracuseStep 3177413 = 595765) (by norm_num)
theorem B2382797 : Blo 1411525 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B1588189 : Blo 1411525 1588189 := bbase (se 3 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 1588189 = 595571) (by norm_num)
theorem B1588225 : Blo 1411525 1588225 := bbase (se 2 (by rfl) ⟨595584, by rfl⟩ : syracuseStep 1588225 = 1191169) (by norm_num)
theorem B3177485 : Blo 1411525 3177485 := bbase (se 3 (by rfl) ⟨595778, by rfl⟩ : syracuseStep 3177485 = 1191557) (by norm_num)
theorem B4766741 : Blo 1411525 4766741 := bbase (se 6 (by rfl) ⟨111720, by rfl⟩ : syracuseStep 4766741 = 223441) (by norm_num)
theorem B1588261 : Blo 1411525 1588261 := bbase (se 4 (by rfl) ⟨148899, by rfl⟩ : syracuseStep 1588261 = 297799) (by norm_num)
theorem B4021301 : Blo 1411525 4021301 := bbase (se 5 (by rfl) ⟨188498, by rfl⟩ : syracuseStep 4021301 = 376997) (by norm_num)
theorem B1588297 : Blo 1411525 1588297 := bbase (se 2 (by rfl) ⟨595611, by rfl⟩ : syracuseStep 1588297 = 1191223) (by norm_num)
theorem B2382925 : Blo 1411525 2382925 := bbase (se 3 (by rfl) ⟨446798, by rfl⟩ : syracuseStep 2382925 = 893597) (by norm_num)
theorem B3177557 : Blo 1411525 3177557 := bbase (se 8 (by rfl) ⟨18618, by rfl⟩ : syracuseStep 3177557 = 37237) (by norm_num)
theorem B6036565 : Blo 1411525 6036565 := bbase (se 8 (by rfl) ⟨35370, by rfl⟩ : syracuseStep 6036565 = 70741) (by norm_num)
theorem B1588333 : Blo 1411525 1588333 := bbase (se 3 (by rfl) ⟨297812, by rfl⟩ : syracuseStep 1588333 = 595625) (by norm_num)
theorem B2718829 : Blo 1411525 2718829 := bbase (se 3 (by rfl) ⟨509780, by rfl⟩ : syracuseStep 2718829 = 1019561) (by norm_num)
theorem B1588369 : Blo 1411525 1588369 := bbase (se 2 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 1588369 = 1191277) (by norm_num)
theorem B3177629 : Blo 1411525 3177629 := bbase (se 3 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 3177629 = 1191611) (by norm_num)
theorem B1432733 : Blo 1411525 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B2383013 : Blo 1411525 2383013 := bbase (se 4 (by rfl) ⟨223407, by rfl⟩ : syracuseStep 2383013 = 446815) (by norm_num)
theorem B2415781 : Blo 1411525 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1588405 : Blo 1411525 1588405 := bbase (se 5 (by rfl) ⟨74456, by rfl⟩ : syracuseStep 1588405 = 148913) (by norm_num)
theorem B2579653 : Blo 1411525 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B2546893 : Blo 1411525 2546893 := bbase (se 3 (by rfl) ⟨477542, by rfl⟩ : syracuseStep 2546893 = 955085) (by norm_num)
theorem B1588441 : Blo 1411525 1588441 := bbase (se 2 (by rfl) ⟨595665, by rfl⟩ : syracuseStep 1588441 = 1191331) (by norm_num)
theorem B3177701 : Blo 1411525 3177701 := bbase (se 4 (by rfl) ⟨297909, by rfl⟩ : syracuseStep 3177701 = 595819) (by norm_num)
theorem B1588477 : Blo 1411525 1588477 := bbase (se 3 (by rfl) ⟨297839, by rfl⟩ : syracuseStep 1588477 = 595679) (by norm_num)
theorem B1588513 : Blo 1411525 1588513 := bbase (se 2 (by rfl) ⟨595692, by rfl⟩ : syracuseStep 1588513 = 1191385) (by norm_num)
theorem B2383141 : Blo 1411525 2383141 := bbase (se 4 (by rfl) ⟨223419, by rfl⟩ : syracuseStep 2383141 = 446839) (by norm_num)
theorem B3177773 : Blo 1411525 3177773 := bbase (se 3 (by rfl) ⟨595832, by rfl⟩ : syracuseStep 3177773 = 1191665) (by norm_num)
theorem B1588549 : Blo 1411525 1588549 := bbase (se 4 (by rfl) ⟨148926, by rfl⟩ : syracuseStep 1588549 = 297853) (by norm_num)
theorem B5365061 : Blo 1411525 5365061 := bbase (se 4 (by rfl) ⟨502974, by rfl⟩ : syracuseStep 5365061 = 1005949) (by norm_num)
theorem B3439949 : Blo 1411525 3439949 := bbase (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) (by norm_num)
theorem B1588585 : Blo 1411525 1588585 := bbase (se 2 (by rfl) ⟨595719, by rfl⟩ : syracuseStep 1588585 = 1191439) (by norm_num)
theorem B3177845 : Blo 1411525 3177845 := bbase (se 5 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 3177845 = 297923) (by norm_num)
theorem B2383229 : Blo 1411525 2383229 := bbase (se 3 (by rfl) ⟨446855, by rfl⟩ : syracuseStep 2383229 = 893711) (by norm_num)
theorem B1588621 : Blo 1411525 1588621 := bbase (se 3 (by rfl) ⟨297866, by rfl⟩ : syracuseStep 1588621 = 595733) (by norm_num)
theorem B1588657 : Blo 1411525 1588657 := bbase (se 2 (by rfl) ⟨595746, by rfl⟩ : syracuseStep 1588657 = 1191493) (by norm_num)
theorem B3177917 : Blo 1411525 3177917 := bbase (se 3 (by rfl) ⟨595859, by rfl⟩ : syracuseStep 3177917 = 1191719) (by norm_num)
theorem B4767173 : Blo 1411525 4767173 := bbase (se 4 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 4767173 = 893845) (by norm_num)
theorem B1588693 : Blo 1411525 1588693 := bbase (se 7 (by rfl) ⟨18617, by rfl⟩ : syracuseStep 1588693 = 37235) (by norm_num)
theorem B6618581 : Blo 1411525 6618581 := bbase (se 7 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 6618581 = 155123) (by norm_num)
theorem B1588729 : Blo 1411525 1588729 := bbase (se 2 (by rfl) ⟨595773, by rfl⟩ : syracuseStep 1588729 = 1191547) (by norm_num)
theorem B2383357 : Blo 1411525 2383357 := bbase (se 3 (by rfl) ⟨446879, by rfl⟩ : syracuseStep 2383357 = 893759) (by norm_num)
theorem B3177989 : Blo 1411525 3177989 := bbase (se 4 (by rfl) ⟨297936, by rfl⟩ : syracuseStep 3177989 = 595873) (by norm_num)
theorem B1588765 : Blo 1411525 1588765 := bbase (se 3 (by rfl) ⟨297893, by rfl⟩ : syracuseStep 1588765 = 595787) (by norm_num)
theorem B1588801 : Blo 1411525 1588801 := bbase (se 2 (by rfl) ⟨595800, by rfl⟩ : syracuseStep 1588801 = 1191601) (by norm_num)
theorem B3178061 : Blo 1411525 3178061 := bbase (se 3 (by rfl) ⟨595886, by rfl⟩ : syracuseStep 3178061 = 1191773) (by norm_num)
theorem B2383445 : Blo 1411525 2383445 := bbase (se 8 (by rfl) ⟨13965, by rfl⟩ : syracuseStep 2383445 = 27931) (by norm_num)
theorem B1588837 : Blo 1411525 1588837 := bbase (se 4 (by rfl) ⟨148953, by rfl⟩ : syracuseStep 1588837 = 297907) (by norm_num)
theorem B5365349 : Blo 1411525 5365349 := bbase (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) (by norm_num)
theorem B1588873 : Blo 1411525 1588873 := bbase (se 2 (by rfl) ⟨595827, by rfl⟩ : syracuseStep 1588873 = 1191655) (by norm_num)
theorem B3178133 : Blo 1411525 3178133 := bbase (se 6 (by rfl) ⟨74487, by rfl⟩ : syracuseStep 3178133 = 148975) (by norm_num)
theorem B1588909 : Blo 1411525 1588909 := bbase (se 3 (by rfl) ⟨297920, by rfl⟩ : syracuseStep 1588909 = 595841) (by norm_num)
theorem B1720013 : Blo 1411525 1720013 := bbase (se 3 (by rfl) ⟨322502, by rfl⟩ : syracuseStep 1720013 = 645005) (by norm_num)
theorem B1588945 : Blo 1411525 1588945 := bbase (se 2 (by rfl) ⟨595854, by rfl⟩ : syracuseStep 1588945 = 1191709) (by norm_num)
theorem B2383573 : Blo 1411525 2383573 := bbase (se 7 (by rfl) ⟨27932, by rfl⟩ : syracuseStep 2383573 = 55865) (by norm_num)
theorem B3178205 : Blo 1411525 3178205 := bbase (se 3 (by rfl) ⟨595913, by rfl⟩ : syracuseStep 3178205 = 1191827) (by norm_num)
theorem B1588981 : Blo 1411525 1588981 := bbase (se 5 (by rfl) ⟨74483, by rfl⟩ : syracuseStep 1588981 = 148967) (by norm_num)
theorem B9051925 : Blo 1411525 9051925 := bbase (se 6 (by rfl) ⟨212154, by rfl⟩ : syracuseStep 9051925 = 424309) (by norm_num)
theorem B1589017 : Blo 1411525 1589017 := bbase (se 2 (by rfl) ⟨595881, by rfl⟩ : syracuseStep 1589017 = 1191763) (by norm_num)
theorem B3178277 : Blo 1411525 3178277 := bbase (se 4 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 3178277 = 595927) (by norm_num)
theorem B2383661 : Blo 1411525 2383661 := bbase (se 3 (by rfl) ⟨446936, by rfl⟩ : syracuseStep 2383661 = 893873) (by norm_num)
theorem B1589053 : Blo 1411525 1589053 := bbase (se 3 (by rfl) ⟨297947, by rfl⟩ : syracuseStep 1589053 = 595895) (by norm_num)
theorem B1589089 : Blo 1411525 1589089 := bbase (se 2 (by rfl) ⟨595908, by rfl⟩ : syracuseStep 1589089 = 1191817) (by norm_num)
theorem B3178349 : Blo 1411525 3178349 := bbase (se 3 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 3178349 = 1191881) (by norm_num)
theorem B2416493 : Blo 1411525 2416493 := bbase (se 3 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 2416493 = 906185) (by norm_num)
theorem B4767605 : Blo 1411525 4767605 := bbase (se 5 (by rfl) ⟨223481, by rfl⟩ : syracuseStep 4767605 = 446963) (by norm_num)
theorem B1589125 : Blo 1411525 1589125 := bbase (se 4 (by rfl) ⟨148980, by rfl⟩ : syracuseStep 1589125 = 297961) (by norm_num)
theorem B1589161 : Blo 1411525 1589161 := bbase (se 2 (by rfl) ⟨595935, by rfl⟩ : syracuseStep 1589161 = 1191871) (by norm_num)
theorem B2383789 : Blo 1411525 2383789 := bbase (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) (by norm_num)
theorem B3178421 : Blo 1411525 3178421 := bbase (se 5 (by rfl) ⟨148988, by rfl⟩ : syracuseStep 3178421 = 297977) (by norm_num)
theorem B1589197 : Blo 1411525 1589197 := bbase (se 3 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 1589197 = 595949) (by norm_num)
theorem B6119381 : Blo 1411525 6119381 := bbase (se 7 (by rfl) ⟨71711, by rfl⟩ : syracuseStep 6119381 = 143423) (by norm_num)
theorem B1589233 : Blo 1411525 1589233 := bbase (se 2 (by rfl) ⟨595962, by rfl⟩ : syracuseStep 1589233 = 1191925) (by norm_num)
theorem B1589251 : Blo 1411525 1589251 := bstep (se 1 (by rfl) ⟨1191938, by rfl⟩ : syracuseStep 1589251 = 2383877) B2383877
theorem B13582349 : Blo 1411525 13582349 := bstep (se 3 (by rfl) ⟨2546690, by rfl⟩ : syracuseStep 13582349 = 5093381) B5093381
theorem B2261009 : Blo 1411525 2261009 := bstep (se 2 (by rfl) ⟨847878, by rfl⟩ : syracuseStep 2261009 = 1695757) B1695757
theorem B7151651 : Blo 1411525 7151651 := bstep (se 1 (by rfl) ⟨5363738, by rfl⟩ : syracuseStep 7151651 = 10727477) B10727477
theorem B4767821 : Blo 1411525 4767821 := bstep (se 3 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 4767821 = 1787933) B1787933
theorem B9928817 : Blo 1411525 9928817 := bstep (se 2 (by rfl) ⟨3723306, by rfl⟩ : syracuseStep 9928817 = 7446613) B7446613
theorem B2383985 : Blo 1411525 2383985 := bstep (se 2 (by rfl) ⟨893994, by rfl⟩ : syracuseStep 2383985 = 1787989) B1787989
theorem B4767875 : Blo 1411525 4767875 := bstep (se 1 (by rfl) ⟨3575906, by rfl⟩ : syracuseStep 4767875 = 7151813) B7151813
theorem B1589395 : Blo 1411525 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B3178673 : Blo 1411525 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B3178691 : Blo 1411525 3178691 := bstep (se 1 (by rfl) ⟨2384018, by rfl⟩ : syracuseStep 3178691 = 4768037) B4768037
theorem B2261233 : Blo 1411525 2261233 := bstep (se 2 (by rfl) ⟨847962, by rfl⟩ : syracuseStep 2261233 = 1695925) B1695925
theorem B2384113 : Blo 1411525 2384113 := bstep (se 2 (by rfl) ⟨894042, by rfl⟩ : syracuseStep 2384113 = 1788085) B1788085
theorem B4022531 : Blo 1411525 4022531 := bstep (se 1 (by rfl) ⟨3016898, by rfl⟩ : syracuseStep 4022531 = 6033797) B6033797
theorem B9044237 : Blo 1411525 9044237 := bstep (se 3 (by rfl) ⟨1695794, by rfl⟩ : syracuseStep 9044237 = 3391589) B3391589
theorem B2384147 : Blo 1411525 2384147 := bstep (se 1 (by rfl) ⟨1788110, by rfl⟩ : syracuseStep 2384147 = 3576221) B3576221
theorem B1589539 : Blo 1411525 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B7635313 : Blo 1411525 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B4768145 : Blo 1411525 4768145 := bstep (se 2 (by rfl) ⟨1788054, by rfl⟩ : syracuseStep 4768145 = 3576109) B3576109
theorem B2384275 : Blo 1411525 2384275 := bstep (se 1 (by rfl) ⟨1788206, by rfl⟩ : syracuseStep 2384275 = 3576413) B3576413
theorem B1909153 : Blo 1411525 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B1589683 : Blo 1411525 1589683 := bstep (se 1 (by rfl) ⟨1192262, by rfl⟩ : syracuseStep 1589683 = 2384525) B2384525
theorem B3178961 : Blo 1411525 3178961 := bstep (se 2 (by rfl) ⟨1192110, by rfl⟩ : syracuseStep 3178961 = 2384221) B2384221
theorem B3015139 : Blo 1411525 3015139 := bstep (se 1 (by rfl) ⟨2261354, by rfl⟩ : syracuseStep 3015139 = 4522709) B4522709
theorem B3178979 : Blo 1411525 3178979 := bstep (se 1 (by rfl) ⟨2384234, by rfl⟩ : syracuseStep 3178979 = 4768469) B4768469
theorem B16097777 : Blo 1411525 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B2294273 : Blo 1411525 2294273 := bstep (se 2 (by rfl) ⟨860352, by rfl⟩ : syracuseStep 2294273 = 1720705) B1720705
theorem B3392003 : Blo 1411525 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B1507843 : Blo 1411525 1507843 := bstep (se 1 (by rfl) ⟨1130882, by rfl⟩ : syracuseStep 1507843 = 2261765) B2261765
theorem B2384417 : Blo 1411525 2384417 := bstep (se 2 (by rfl) ⟨894156, by rfl⟩ : syracuseStep 2384417 = 1788313) B1788313
theorem B3580465 : Blo 1411525 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B5366321 : Blo 1411525 5366321 := bstep (se 2 (by rfl) ⟨2012370, by rfl⟩ : syracuseStep 5366321 = 4024741) B4024741
theorem B1589827 : Blo 1411525 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B14500421 : Blo 1411525 14500421 := bstep (se 4 (by rfl) ⟨1359414, by rfl⟩ : syracuseStep 14500421 = 2718829) B2718829
theorem B2384545 : Blo 1411525 2384545 := bstep (se 2 (by rfl) ⟨894204, by rfl⟩ : syracuseStep 2384545 = 1788409) B1788409
theorem B1786531 : Blo 1411525 1786531 := bstep (se 1 (by rfl) ⟨1339898, by rfl⟩ : syracuseStep 1786531 = 2679797) B2679797
theorem B2384579 : Blo 1411525 2384579 := bstep (se 1 (by rfl) ⟨1788434, by rfl⟩ : syracuseStep 2384579 = 3576869) B3576869
theorem B20374213 : Blo 1411525 20374213 := bstep (se 4 (by rfl) ⟨1910082, by rfl⟩ : syracuseStep 20374213 = 3820165) B3820165
theorem B1589971 : Blo 1411525 1589971 := bstep (se 1 (by rfl) ⟨1192478, by rfl⟩ : syracuseStep 1589971 = 2384957) B2384957
theorem B3015395 : Blo 1411525 3015395 := bstep (se 1 (by rfl) ⟨2261546, by rfl⟩ : syracuseStep 3015395 = 4523093) B4523093
theorem B1909489 : Blo 1411525 1909489 := bstep (se 2 (by rfl) ⟨716058, by rfl⟩ : syracuseStep 1909489 = 1432117) B1432117
theorem B3179249 : Blo 1411525 3179249 := bstep (se 2 (by rfl) ⟨1192218, by rfl⟩ : syracuseStep 3179249 = 2384437) B2384437
theorem B1786627 : Blo 1411525 1786627 := bstep (se 1 (by rfl) ⟨1339970, by rfl⟩ : syracuseStep 1786627 = 2679941) B2679941
theorem B3179267 : Blo 1411525 3179267 := bstep (se 1 (by rfl) ⟨2384450, by rfl⟩ : syracuseStep 3179267 = 4768901) B4768901
theorem B7742213 : Blo 1411525 7742213 := bstep (se 4 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 7742213 = 1451665) B1451665
theorem B2384707 : Blo 1411525 2384707 := bstep (se 1 (by rfl) ⟨1788530, by rfl⟩ : syracuseStep 2384707 = 3577061) B3577061
theorem B7152461 : Blo 1411525 7152461 := bstep (se 3 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 7152461 = 2682173) B2682173
theorem B1590115 : Blo 1411525 1590115 := bstep (se 1 (by rfl) ⟨1192586, by rfl⟩ : syracuseStep 1590115 = 2385173) B2385173
theorem B3621763 : Blo 1411525 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B4768685 : Blo 1411525 4768685 := bstep (se 3 (by rfl) ⟨894128, by rfl⟩ : syracuseStep 4768685 = 1788257) B1788257
theorem B2384849 : Blo 1411525 2384849 := bstep (se 2 (by rfl) ⟨894318, by rfl⟩ : syracuseStep 2384849 = 1788637) B1788637
theorem B4522979 : Blo 1411525 4522979 := bstep (se 1 (by rfl) ⟨3392234, by rfl⟩ : syracuseStep 4522979 = 6784469) B6784469
theorem B4768739 : Blo 1411525 4768739 := bstep (se 1 (by rfl) ⟨3576554, by rfl⟩ : syracuseStep 4768739 = 7153109) B7153109
theorem B3179537 : Blo 1411525 3179537 := bstep (se 2 (by rfl) ⟨1192326, by rfl⟩ : syracuseStep 3179537 = 2384653) B2384653
theorem B3179555 : Blo 1411525 3179555 := bstep (se 1 (by rfl) ⟨2384666, by rfl⟩ : syracuseStep 3179555 = 4769333) B4769333
theorem B4023341 : Blo 1411525 4023341 := bstep (se 3 (by rfl) ⟨754376, by rfl⟩ : syracuseStep 4023341 = 1508753) B1508753
theorem B2384977 : Blo 1411525 2384977 := bstep (se 2 (by rfl) ⟨894366, by rfl⟩ : syracuseStep 2384977 = 1788733) B1788733
theorem B18105443 : Blo 1411525 18105443 := bstep (se 1 (by rfl) ⟨13579082, by rfl⟩ : syracuseStep 18105443 = 27158165) B27158165
theorem B6030449 : Blo 1411525 6030449 := bstep (se 2 (by rfl) ⟨2261418, by rfl⟩ : syracuseStep 6030449 = 4522837) B4522837
theorem B2385011 : Blo 1411525 2385011 := bstep (se 1 (by rfl) ⟨1788758, by rfl⟩ : syracuseStep 2385011 = 3577517) B3577517
theorem B6784177 : Blo 1411525 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B4023533 : Blo 1411525 4023533 := bstep (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) B1508825
theorem B4769009 : Blo 1411525 4769009 := bstep (se 2 (by rfl) ⟨1788378, by rfl⟩ : syracuseStep 4769009 = 3576757) B3576757
theorem B1787123 : Blo 1411525 1787123 := bstep (se 1 (by rfl) ⟨1340342, by rfl⟩ : syracuseStep 1787123 = 2680685) B2680685
theorem B2385139 : Blo 1411525 2385139 := bstep (se 1 (by rfl) ⟨1788854, by rfl⟩ : syracuseStep 2385139 = 3577709) B3577709
theorem B8045837 : Blo 1411525 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B5727523 : Blo 1411525 5727523 := bstep (se 1 (by rfl) ⟨4295642, by rfl⟩ : syracuseStep 5727523 = 8591285) B8591285
theorem B3179825 : Blo 1411525 3179825 := bstep (se 2 (by rfl) ⟨1192434, by rfl⟩ : syracuseStep 3179825 = 2384869) B2384869
theorem B3179843 : Blo 1411525 3179843 := bstep (se 1 (by rfl) ⟨2384882, by rfl⟩ : syracuseStep 3179843 = 4769765) B4769765
theorem B2385281 : Blo 1411525 2385281 := bstep (se 2 (by rfl) ⟨894480, by rfl⟩ : syracuseStep 2385281 = 1788961) B1788961
theorem B5088739 : Blo 1411525 5088739 := bstep (se 1 (by rfl) ⟨3816554, by rfl⟩ : syracuseStep 5088739 = 7633109) B7633109
theorem B3221041 : Blo 1411525 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B3180113 : Blo 1411525 3180113 := bstep (se 2 (by rfl) ⟨1192542, by rfl⟩ : syracuseStep 3180113 = 2385085) B2385085
theorem B3180131 : Blo 1411525 3180131 := bstep (se 1 (by rfl) ⟨2385098, by rfl⟩ : syracuseStep 3180131 = 4770197) B4770197
theorem B14501489 : Blo 1411525 14501489 := bstep (se 2 (by rfl) ⟨5438058, by rfl⟩ : syracuseStep 14501489 = 10876117) B10876117
theorem B2680465 : Blo 1411525 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B3016369 : Blo 1411525 3016369 := bstep (se 2 (by rfl) ⟨1131138, by rfl⟩ : syracuseStep 3016369 = 2262277) B2262277
theorem B4769549 : Blo 1411525 4769549 := bstep (se 3 (by rfl) ⟨894290, by rfl⟩ : syracuseStep 4769549 = 1788581) B1788581
theorem B4769603 : Blo 1411525 4769603 := bstep (se 1 (by rfl) ⟨3577202, by rfl⟩ : syracuseStep 4769603 = 7154405) B7154405
theorem B12060485 : Blo 1411525 12060485 := bstep (se 4 (by rfl) ⟨1130670, by rfl⟩ : syracuseStep 12060485 = 2261341) B2261341
theorem B3180401 : Blo 1411525 3180401 := bstep (se 2 (by rfl) ⟨1192650, by rfl⟩ : syracuseStep 3180401 = 2385301) B2385301
theorem B1509235 : Blo 1411525 1509235 := bstep (se 1 (by rfl) ⟨1131926, by rfl⟩ : syracuseStep 1509235 = 2263853) B2263853
theorem B3180419 : Blo 1411525 3180419 := bstep (se 1 (by rfl) ⟨2385314, by rfl⟩ : syracuseStep 3180419 = 4770629) B4770629
theorem B2484145 : Blo 1411525 2484145 := bstep (se 2 (by rfl) ⟨931554, by rfl⟩ : syracuseStep 2484145 = 1863109) B1863109
theorem B1787827 : Blo 1411525 1787827 := bstep (se 1 (by rfl) ⟨1340870, by rfl⟩ : syracuseStep 1787827 = 2681741) B2681741
theorem B2262995 : Blo 1411525 2262995 := bstep (se 1 (by rfl) ⟨1697246, by rfl⟩ : syracuseStep 2262995 = 3394493) B3394493
theorem B1787923 : Blo 1411525 1787923 := bstep (se 1 (by rfl) ⟨1340942, by rfl⟩ : syracuseStep 1787923 = 2681885) B2681885
theorem B2680867 : Blo 1411525 2680867 := bstep (se 1 (by rfl) ⟨2010650, by rfl⟩ : syracuseStep 2680867 = 4021301) B4021301
theorem B3573841 : Blo 1411525 3573841 := bstep (se 2 (by rfl) ⟨1340190, by rfl⟩ : syracuseStep 3573841 = 2680381) B2680381
theorem B2680913 : Blo 1411525 2680913 := bstep (se 2 (by rfl) ⟨1005342, by rfl⟩ : syracuseStep 2680913 = 2010685) B2010685
theorem B4769873 : Blo 1411525 4769873 := bstep (se 2 (by rfl) ⟨1788702, by rfl⟩ : syracuseStep 4769873 = 3577405) B3577405
theorem B5359715 : Blo 1411525 5359715 := bstep (se 1 (by rfl) ⟨4019786, by rfl⟩ : syracuseStep 5359715 = 8039573) B8039573
theorem B5359729 : Blo 1411525 5359729 := bstep (se 2 (by rfl) ⟨2009898, by rfl⟩ : syracuseStep 5359729 = 4019797) B4019797
theorem B2263187 : Blo 1411525 2263187 := bstep (se 1 (by rfl) ⟨1697390, by rfl⟩ : syracuseStep 2263187 = 3394781) B3394781
theorem B4024525 : Blo 1411525 4024525 := bstep (se 3 (by rfl) ⟨754598, by rfl⟩ : syracuseStep 4024525 = 1509197) B1509197
theorem B10733795 : Blo 1411525 10733795 := bstep (se 1 (by rfl) ⟨8050346, by rfl⟩ : syracuseStep 10733795 = 16100693) B16100693
theorem B10316045 : Blo 1411525 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B2263315 : Blo 1411525 2263315 := bstep (se 1 (by rfl) ⟨1697486, by rfl⟩ : syracuseStep 2263315 = 3394973) B3394973
theorem B3017027 : Blo 1411525 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B3574115 : Blo 1411525 3574115 := bstep (se 1 (by rfl) ⟨2680586, by rfl⟩ : syracuseStep 3574115 = 5361173) B5361173
theorem B2681201 : Blo 1411525 2681201 := bstep (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) B2010901
theorem B12069233 : Blo 1411525 12069233 := bstep (se 2 (by rfl) ⟨4525962, by rfl⟩ : syracuseStep 12069233 = 9051925) B9051925
theorem B61049285 : Blo 1411525 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B1411539 : Blo 1411525 1411539 := bstep (se 1 (by rfl) ⟨1058654, by rfl⟩ : syracuseStep 1411539 = 2117309) B2117309
theorem B1411555 : Blo 1411525 1411555 := bstep (se 1 (by rfl) ⟨1058666, by rfl⟩ : syracuseStep 1411555 = 2117333) B2117333
theorem B12061169 : Blo 1411525 12061169 := bstep (se 2 (by rfl) ⟨4522938, by rfl⟩ : syracuseStep 12061169 = 9045877) B9045877
theorem B1411571 : Blo 1411525 1411571 := bstep (se 1 (by rfl) ⟨1058678, by rfl⟩ : syracuseStep 1411571 = 2117357) B2117357
theorem B1411587 : Blo 1411525 1411587 := bstep (se 1 (by rfl) ⟨1058690, by rfl⟩ : syracuseStep 1411587 = 2117381) B2117381
theorem B1788419 : Blo 1411525 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B1411603 : Blo 1411525 1411603 := bstep (se 1 (by rfl) ⟨1058702, by rfl⟩ : syracuseStep 1411603 = 2117405) B2117405
theorem B1411619 : Blo 1411525 1411619 := bstep (se 1 (by rfl) ⟨1058714, by rfl⟩ : syracuseStep 1411619 = 2117429) B2117429
theorem B3574307 : Blo 1411525 3574307 := bstep (se 1 (by rfl) ⟨2680730, by rfl⟩ : syracuseStep 3574307 = 5361461) B5361461
theorem B1411635 : Blo 1411525 1411635 := bstep (se 1 (by rfl) ⟨1058726, by rfl⟩ : syracuseStep 1411635 = 2117453) B2117453
theorem B1411651 : Blo 1411525 1411651 := bstep (se 1 (by rfl) ⟨1058738, by rfl⟩ : syracuseStep 1411651 = 2117477) B2117477
theorem B1411667 : Blo 1411525 1411667 := bstep (se 1 (by rfl) ⟨1058750, by rfl⟩ : syracuseStep 1411667 = 2117501) B2117501
theorem B1411683 : Blo 1411525 1411683 := bstep (se 1 (by rfl) ⟨1058762, by rfl⟩ : syracuseStep 1411683 = 2117525) B2117525
theorem B4770413 : Blo 1411525 4770413 := bstep (se 3 (by rfl) ⟨894452, by rfl⟩ : syracuseStep 4770413 = 1788905) B1788905
theorem B1411699 : Blo 1411525 1411699 := bstep (se 1 (by rfl) ⟨1058774, by rfl⟩ : syracuseStep 1411699 = 2117549) B2117549
theorem B1411715 : Blo 1411525 1411715 := bstep (se 1 (by rfl) ⟨1058786, by rfl⟩ : syracuseStep 1411715 = 2117573) B2117573
theorem B1411731 : Blo 1411525 1411731 := bstep (se 1 (by rfl) ⟨1058798, by rfl⟩ : syracuseStep 1411731 = 2117597) B2117597
theorem B1411747 : Blo 1411525 1411747 := bstep (se 1 (by rfl) ⟨1058810, by rfl⟩ : syracuseStep 1411747 = 2117621) B2117621
theorem B4770467 : Blo 1411525 4770467 := bstep (se 1 (by rfl) ⟨3577850, by rfl⟩ : syracuseStep 4770467 = 7155701) B7155701
theorem B7735985 : Blo 1411525 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B1411763 : Blo 1411525 1411763 := bstep (se 1 (by rfl) ⟨1058822, by rfl⟩ : syracuseStep 1411763 = 2117645) B2117645
theorem B1411779 : Blo 1411525 1411779 := bstep (se 1 (by rfl) ⟨1058834, by rfl⟩ : syracuseStep 1411779 = 2117669) B2117669
theorem B1411795 : Blo 1411525 1411795 := bstep (se 1 (by rfl) ⟨1058846, by rfl⟩ : syracuseStep 1411795 = 2117693) B2117693
theorem B1411811 : Blo 1411525 1411811 := bstep (se 1 (by rfl) ⟨1058858, by rfl⟩ : syracuseStep 1411811 = 2117717) B2117717
theorem B6441713 : Blo 1411525 6441713 := bstep (se 2 (by rfl) ⟨2415642, by rfl⟩ : syracuseStep 6441713 = 4831285) B4831285
theorem B4524785 : Blo 1411525 4524785 := bstep (se 2 (by rfl) ⟨1696794, by rfl⟩ : syracuseStep 4524785 = 3393589) B3393589
theorem B1411827 : Blo 1411525 1411827 := bstep (se 1 (by rfl) ⟨1058870, by rfl⟩ : syracuseStep 1411827 = 2117741) B2117741
theorem B1411843 : Blo 1411525 1411843 := bstep (se 1 (by rfl) ⟨1058882, by rfl⟩ : syracuseStep 1411843 = 2117765) B2117765
theorem B6032141 : Blo 1411525 6032141 := bstep (se 3 (by rfl) ⟨1131026, by rfl⟩ : syracuseStep 6032141 = 2262053) B2262053
theorem B1411859 : Blo 1411525 1411859 := bstep (se 1 (by rfl) ⟨1058894, by rfl⟩ : syracuseStep 1411859 = 2117789) B2117789
theorem B1411875 : Blo 1411525 1411875 := bstep (se 1 (by rfl) ⟨1058906, by rfl⟩ : syracuseStep 1411875 = 2117813) B2117813
theorem B4524835 : Blo 1411525 4524835 := bstep (se 1 (by rfl) ⟨3393626, by rfl⟩ : syracuseStep 4524835 = 6787253) B6787253
theorem B1411891 : Blo 1411525 1411891 := bstep (se 1 (by rfl) ⟨1058918, by rfl⟩ : syracuseStep 1411891 = 2117837) B2117837
theorem B1411907 : Blo 1411525 1411907 := bstep (se 1 (by rfl) ⟨1058930, by rfl⟩ : syracuseStep 1411907 = 2117861) B2117861
theorem B6785869 : Blo 1411525 6785869 := bstep (se 3 (by rfl) ⟨1272350, by rfl⟩ : syracuseStep 6785869 = 2544701) B2544701
theorem B4295501 : Blo 1411525 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B1411923 : Blo 1411525 1411923 := bstep (se 1 (by rfl) ⟨1058942, by rfl⟩ : syracuseStep 1411923 = 2117885) B2117885
theorem B1411939 : Blo 1411525 1411939 := bstep (se 1 (by rfl) ⟨1058954, by rfl⟩ : syracuseStep 1411939 = 2117909) B2117909
theorem B1411955 : Blo 1411525 1411955 := bstep (se 1 (by rfl) ⟨1058966, by rfl⟩ : syracuseStep 1411955 = 2117933) B2117933
theorem B1411971 : Blo 1411525 1411971 := bstep (se 1 (by rfl) ⟨1058978, by rfl⟩ : syracuseStep 1411971 = 2117957) B2117957
theorem B1411987 : Blo 1411525 1411987 := bstep (se 1 (by rfl) ⟨1058990, by rfl⟩ : syracuseStep 1411987 = 2117981) B2117981
theorem B2263955 : Blo 1411525 2263955 := bstep (se 1 (by rfl) ⟨1697966, by rfl⟩ : syracuseStep 2263955 = 3395933) B3395933
theorem B1412003 : Blo 1411525 1412003 := bstep (se 1 (by rfl) ⟨1059002, by rfl⟩ : syracuseStep 1412003 = 2118005) B2118005
theorem B1412019 : Blo 1411525 1412019 := bstep (se 1 (by rfl) ⟨1059014, by rfl⟩ : syracuseStep 1412019 = 2118029) B2118029
theorem B1412035 : Blo 1411525 1412035 := bstep (se 1 (by rfl) ⟨1059026, by rfl⟩ : syracuseStep 1412035 = 2118053) B2118053
theorem B1412051 : Blo 1411525 1412051 := bstep (se 1 (by rfl) ⟨1059038, by rfl⟩ : syracuseStep 1412051 = 2118077) B2118077
theorem B2264033 : Blo 1411525 2264033 := bstep (se 2 (by rfl) ⟨849012, by rfl⟩ : syracuseStep 2264033 = 1698025) B1698025
theorem B7146467 : Blo 1411525 7146467 := bstep (se 1 (by rfl) ⟨5359850, by rfl⟩ : syracuseStep 7146467 = 10719701) B10719701
theorem B1412067 : Blo 1411525 1412067 := bstep (se 1 (by rfl) ⟨1059050, by rfl⟩ : syracuseStep 1412067 = 2118101) B2118101
theorem B1412083 : Blo 1411525 1412083 := bstep (se 1 (by rfl) ⟨1059062, by rfl⟩ : syracuseStep 1412083 = 2118125) B2118125
theorem B1412099 : Blo 1411525 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B1412115 : Blo 1411525 1412115 := bstep (se 1 (by rfl) ⟨1059086, by rfl⟩ : syracuseStep 1412115 = 2118173) B2118173
theorem B1412131 : Blo 1411525 1412131 := bstep (se 1 (by rfl) ⟨1059098, by rfl⟩ : syracuseStep 1412131 = 2118197) B2118197
theorem B1412147 : Blo 1411525 1412147 := bstep (se 1 (by rfl) ⟨1059110, by rfl⟩ : syracuseStep 1412147 = 2118221) B2118221
theorem B1412163 : Blo 1411525 1412163 := bstep (se 1 (by rfl) ⟨1059122, by rfl⟩ : syracuseStep 1412163 = 2118245) B2118245
theorem B2681923 : Blo 1411525 2681923 := bstep (se 1 (by rfl) ⟨2011442, by rfl⟩ : syracuseStep 2681923 = 4022885) B4022885
theorem B3820621 : Blo 1411525 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B1412179 : Blo 1411525 1412179 := bstep (se 1 (by rfl) ⟨1059134, by rfl⟩ : syracuseStep 1412179 = 2118269) B2118269
theorem B1412195 : Blo 1411525 1412195 := bstep (se 1 (by rfl) ⟨1059146, by rfl⟩ : syracuseStep 1412195 = 2118293) B2118293
theorem B1412211 : Blo 1411525 1412211 := bstep (se 1 (by rfl) ⟨1059158, by rfl⟩ : syracuseStep 1412211 = 2118317) B2118317
theorem B1412227 : Blo 1411525 1412227 := bstep (se 1 (by rfl) ⟨1059170, by rfl⟩ : syracuseStep 1412227 = 2118341) B2118341
theorem B3017873 : Blo 1411525 3017873 := bstep (se 2 (by rfl) ⟨1131702, by rfl⟩ : syracuseStep 3017873 = 2263405) B2263405
theorem B1412243 : Blo 1411525 1412243 := bstep (se 1 (by rfl) ⟨1059182, by rfl⟩ : syracuseStep 1412243 = 2118365) B2118365
theorem B1412259 : Blo 1411525 1412259 := bstep (se 1 (by rfl) ⟨1059194, by rfl⟩ : syracuseStep 1412259 = 2118389) B2118389
theorem B1412275 : Blo 1411525 1412275 := bstep (se 1 (by rfl) ⟨1059206, by rfl⟩ : syracuseStep 1412275 = 2118413) B2118413
theorem B1412291 : Blo 1411525 1412291 := bstep (se 1 (by rfl) ⟨1059218, by rfl⟩ : syracuseStep 1412291 = 2118437) B2118437
theorem B1412307 : Blo 1411525 1412307 := bstep (se 1 (by rfl) ⟨1059230, by rfl⟩ : syracuseStep 1412307 = 2118461) B2118461
theorem B1412323 : Blo 1411525 1412323 := bstep (se 1 (by rfl) ⟨1059242, by rfl⟩ : syracuseStep 1412323 = 2118485) B2118485
theorem B1412339 : Blo 1411525 1412339 := bstep (se 1 (by rfl) ⟨1059254, by rfl⟩ : syracuseStep 1412339 = 2118509) B2118509
theorem B1412355 : Blo 1411525 1412355 := bstep (se 1 (by rfl) ⟨1059266, by rfl⟩ : syracuseStep 1412355 = 2118533) B2118533
theorem B2862353 : Blo 1411525 2862353 := bstep (se 2 (by rfl) ⟨1073382, by rfl⟩ : syracuseStep 2862353 = 2146765) B2146765
theorem B1412371 : Blo 1411525 1412371 := bstep (se 1 (by rfl) ⟨1059278, by rfl⟩ : syracuseStep 1412371 = 2118557) B2118557
theorem B1412387 : Blo 1411525 1412387 := bstep (se 1 (by rfl) ⟨1059290, by rfl⟩ : syracuseStep 1412387 = 2118581) B2118581
theorem B1412403 : Blo 1411525 1412403 := bstep (se 1 (by rfl) ⟨1059302, by rfl⟩ : syracuseStep 1412403 = 2118605) B2118605
theorem B1412419 : Blo 1411525 1412419 := bstep (se 1 (by rfl) ⟨1059314, by rfl⟩ : syracuseStep 1412419 = 2118629) B2118629
theorem B1412435 : Blo 1411525 1412435 := bstep (se 1 (by rfl) ⟨1059326, by rfl⟩ : syracuseStep 1412435 = 2118653) B2118653
theorem B1412451 : Blo 1411525 1412451 := bstep (se 1 (by rfl) ⟨1059338, by rfl⟩ : syracuseStep 1412451 = 2118677) B2118677
theorem B1412467 : Blo 1411525 1412467 := bstep (se 1 (by rfl) ⟨1059350, by rfl⟩ : syracuseStep 1412467 = 2118701) B2118701
theorem B1412483 : Blo 1411525 1412483 := bstep (se 1 (by rfl) ⟨1059362, by rfl⟩ : syracuseStep 1412483 = 2118725) B2118725
theorem B1412499 : Blo 1411525 1412499 := bstep (se 1 (by rfl) ⟨1059374, by rfl⟩ : syracuseStep 1412499 = 2118749) B2118749
theorem B6786467 : Blo 1411525 6786467 := bstep (se 1 (by rfl) ⟨5089850, by rfl⟩ : syracuseStep 6786467 = 10179701) B10179701
theorem B1412515 : Blo 1411525 1412515 := bstep (se 1 (by rfl) ⟨1059386, by rfl⟩ : syracuseStep 1412515 = 2118773) B2118773
theorem B1412531 : Blo 1411525 1412531 := bstep (se 1 (by rfl) ⟨1059398, by rfl⟩ : syracuseStep 1412531 = 2118797) B2118797
theorem B1412547 : Blo 1411525 1412547 := bstep (se 1 (by rfl) ⟨1059410, by rfl⟩ : syracuseStep 1412547 = 2118821) B2118821
theorem B8048069 : Blo 1411525 8048069 := bstep (se 4 (by rfl) ⟨754506, by rfl⟩ : syracuseStep 8048069 = 1509013) B1509013
theorem B2010577 : Blo 1411525 2010577 := bstep (se 2 (by rfl) ⟨753966, by rfl⟩ : syracuseStep 2010577 = 1507933) B1507933
theorem B3575249 : Blo 1411525 3575249 := bstep (se 2 (by rfl) ⟨1340718, by rfl⟩ : syracuseStep 3575249 = 2681437) B2681437
theorem B1412563 : Blo 1411525 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B1412579 : Blo 1411525 1412579 := bstep (se 1 (by rfl) ⟨1059434, by rfl⟩ : syracuseStep 1412579 = 2118869) B2118869
theorem B4525553 : Blo 1411525 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B1412595 : Blo 1411525 1412595 := bstep (se 1 (by rfl) ⟨1059446, by rfl⟩ : syracuseStep 1412595 = 2118893) B2118893
theorem B3575299 : Blo 1411525 3575299 := bstep (se 1 (by rfl) ⟨2681474, by rfl⟩ : syracuseStep 3575299 = 5362949) B5362949
theorem B1412611 : Blo 1411525 1412611 := bstep (se 1 (by rfl) ⟨1059458, by rfl⟩ : syracuseStep 1412611 = 2118917) B2118917
theorem B2682371 : Blo 1411525 2682371 := bstep (se 1 (by rfl) ⟨2011778, by rfl⟩ : syracuseStep 2682371 = 4023557) B4023557
theorem B1412627 : Blo 1411525 1412627 := bstep (se 1 (by rfl) ⟨1059470, by rfl⟩ : syracuseStep 1412627 = 2118941) B2118941
theorem B5361187 : Blo 1411525 5361187 := bstep (se 1 (by rfl) ⟨4020890, by rfl⟩ : syracuseStep 5361187 = 8041781) B8041781
theorem B1412643 : Blo 1411525 1412643 := bstep (se 1 (by rfl) ⟨1059482, by rfl⟩ : syracuseStep 1412643 = 2118965) B2118965
theorem B2010673 : Blo 1411525 2010673 := bstep (se 2 (by rfl) ⟨754002, by rfl⟩ : syracuseStep 2010673 = 1508005) B1508005
theorem B1412659 : Blo 1411525 1412659 := bstep (se 1 (by rfl) ⟨1059494, by rfl⟩ : syracuseStep 1412659 = 2118989) B2118989
theorem B1412675 : Blo 1411525 1412675 := bstep (se 1 (by rfl) ⟨1059506, by rfl⟩ : syracuseStep 1412675 = 2119013) B2119013
theorem B8040005 : Blo 1411525 8040005 := bstep (se 4 (by rfl) ⟨753750, by rfl⟩ : syracuseStep 8040005 = 1507501) B1507501
theorem B1412691 : Blo 1411525 1412691 := bstep (se 1 (by rfl) ⟨1059518, by rfl⟩ : syracuseStep 1412691 = 2119037) B2119037
theorem B1412707 : Blo 1411525 1412707 := bstep (se 1 (by rfl) ⟨1059530, by rfl⟩ : syracuseStep 1412707 = 2119061) B2119061
theorem B1412723 : Blo 1411525 1412723 := bstep (se 1 (by rfl) ⟨1059542, by rfl⟩ : syracuseStep 1412723 = 2119085) B2119085
theorem B1412739 : Blo 1411525 1412739 := bstep (se 1 (by rfl) ⟨1059554, by rfl⟩ : syracuseStep 1412739 = 2119109) B2119109
theorem B3575441 : Blo 1411525 3575441 := bstep (se 2 (by rfl) ⟨1340790, by rfl⟩ : syracuseStep 3575441 = 2681581) B2681581
theorem B1412755 : Blo 1411525 1412755 := bstep (se 1 (by rfl) ⟨1059566, by rfl⟩ : syracuseStep 1412755 = 2119133) B2119133
theorem B1412771 : Blo 1411525 1412771 := bstep (se 1 (by rfl) ⟨1059578, by rfl⟩ : syracuseStep 1412771 = 2119157) B2119157
theorem B2117297 : Blo 1411525 2117297 := bstep (se 2 (by rfl) ⟨793986, by rfl⟩ : syracuseStep 2117297 = 1587973) B1587973
theorem B7155377 : Blo 1411525 7155377 := bstep (se 2 (by rfl) ⟨2683266, by rfl⟩ : syracuseStep 7155377 = 5366533) B5366533
theorem B1412787 : Blo 1411525 1412787 := bstep (se 1 (by rfl) ⟨1059590, by rfl⟩ : syracuseStep 1412787 = 2119181) B2119181
theorem B2117315 : Blo 1411525 2117315 := bstep (se 1 (by rfl) ⟨1587986, by rfl⟩ : syracuseStep 2117315 = 3175973) B3175973
theorem B1412803 : Blo 1411525 1412803 := bstep (se 1 (by rfl) ⟨1059602, by rfl⟩ : syracuseStep 1412803 = 2119205) B2119205
theorem B13758149 : Blo 1411525 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B1412819 : Blo 1411525 1412819 := bstep (se 1 (by rfl) ⟨1059614, by rfl⟩ : syracuseStep 1412819 = 2119229) B2119229
theorem B2117345 : Blo 1411525 2117345 := bstep (se 2 (by rfl) ⟨794004, by rfl⟩ : syracuseStep 2117345 = 1588009) B1588009
theorem B1412835 : Blo 1411525 1412835 := bstep (se 1 (by rfl) ⟨1059626, by rfl⟩ : syracuseStep 1412835 = 2119253) B2119253
theorem B2117363 : Blo 1411525 2117363 := bstep (se 1 (by rfl) ⟨1588022, by rfl⟩ : syracuseStep 2117363 = 3176045) B3176045
theorem B1412851 : Blo 1411525 1412851 := bstep (se 1 (by rfl) ⟨1059638, by rfl⟩ : syracuseStep 1412851 = 2119277) B2119277
theorem B1412867 : Blo 1411525 1412867 := bstep (se 1 (by rfl) ⟨1059650, by rfl⟩ : syracuseStep 1412867 = 2119301) B2119301
theorem B7147277 : Blo 1411525 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B2117393 : Blo 1411525 2117393 := bstep (se 2 (by rfl) ⟨794022, by rfl⟩ : syracuseStep 2117393 = 1588045) B1588045
theorem B1412883 : Blo 1411525 1412883 := bstep (se 1 (by rfl) ⟨1059662, by rfl⟩ : syracuseStep 1412883 = 2119325) B2119325
theorem B2117411 : Blo 1411525 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B1412899 : Blo 1411525 1412899 := bstep (se 1 (by rfl) ⟨1059674, by rfl⟩ : syracuseStep 1412899 = 2119349) B2119349
theorem B2682659 : Blo 1411525 2682659 := bstep (se 1 (by rfl) ⟨2011994, by rfl⟩ : syracuseStep 2682659 = 4023989) B4023989
theorem B1412915 : Blo 1411525 1412915 := bstep (se 1 (by rfl) ⟨1059686, by rfl⟩ : syracuseStep 1412915 = 2119373) B2119373
theorem B2117441 : Blo 1411525 2117441 := bstep (se 2 (by rfl) ⟨794040, by rfl⟩ : syracuseStep 2117441 = 1588081) B1588081
theorem B1412931 : Blo 1411525 1412931 := bstep (se 1 (by rfl) ⟨1059698, by rfl⟩ : syracuseStep 1412931 = 2119397) B2119397
theorem B3395395 : Blo 1411525 3395395 := bstep (se 1 (by rfl) ⟨2546546, by rfl⟩ : syracuseStep 3395395 = 5093093) B5093093
theorem B2117459 : Blo 1411525 2117459 := bstep (se 1 (by rfl) ⟨1588094, by rfl⟩ : syracuseStep 2117459 = 3176189) B3176189
theorem B1412947 : Blo 1411525 1412947 := bstep (se 1 (by rfl) ⟨1059710, by rfl⟩ : syracuseStep 1412947 = 2119421) B2119421
theorem B1412963 : Blo 1411525 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B4075373 : Blo 1411525 4075373 := bstep (se 3 (by rfl) ⟨764132, by rfl⟩ : syracuseStep 4075373 = 1528265) B1528265
theorem B2117489 : Blo 1411525 2117489 := bstep (se 2 (by rfl) ⟨794058, by rfl⟩ : syracuseStep 2117489 = 1588117) B1588117
theorem B6786929 : Blo 1411525 6786929 := bstep (se 2 (by rfl) ⟨2545098, by rfl⟩ : syracuseStep 6786929 = 5090197) B5090197
theorem B1412979 : Blo 1411525 1412979 := bstep (se 1 (by rfl) ⟨1059734, by rfl⟩ : syracuseStep 1412979 = 2119469) B2119469
theorem B2117507 : Blo 1411525 2117507 := bstep (se 1 (by rfl) ⟨1588130, by rfl⟩ : syracuseStep 2117507 = 3176261) B3176261
theorem B1412995 : Blo 1411525 1412995 := bstep (se 1 (by rfl) ⟨1059746, by rfl⟩ : syracuseStep 1412995 = 2119493) B2119493
theorem B1413011 : Blo 1411525 1413011 := bstep (se 1 (by rfl) ⟨1059758, by rfl⟩ : syracuseStep 1413011 = 2119517) B2119517
theorem B2117537 : Blo 1411525 2117537 := bstep (se 2 (by rfl) ⟨794076, by rfl⟩ : syracuseStep 2117537 = 1588153) B1588153
theorem B1413027 : Blo 1411525 1413027 := bstep (se 1 (by rfl) ⟨1059770, by rfl⟩ : syracuseStep 1413027 = 2119541) B2119541
theorem B2117555 : Blo 1411525 2117555 := bstep (se 1 (by rfl) ⟨1588166, by rfl⟩ : syracuseStep 2117555 = 3176333) B3176333
theorem B1413043 : Blo 1411525 1413043 := bstep (se 1 (by rfl) ⟨1059782, by rfl⟩ : syracuseStep 1413043 = 2119565) B2119565
theorem B18091957 : Blo 1411525 18091957 := bstep (se 5 (by rfl) ⟨848060, by rfl⟩ : syracuseStep 18091957 = 1696121) B1696121
theorem B1413059 : Blo 1411525 1413059 := bstep (se 1 (by rfl) ⟨1059794, by rfl⟩ : syracuseStep 1413059 = 2119589) B2119589
theorem B2117585 : Blo 1411525 2117585 := bstep (se 2 (by rfl) ⟨794094, by rfl⟩ : syracuseStep 2117585 = 1588189) B1588189
theorem B1413075 : Blo 1411525 1413075 := bstep (se 1 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 1413075 = 2119613) B2119613
theorem B2117603 : Blo 1411525 2117603 := bstep (se 1 (by rfl) ⟨1588202, by rfl⟩ : syracuseStep 2117603 = 3176405) B3176405
theorem B1413091 : Blo 1411525 1413091 := bstep (se 1 (by rfl) ⟨1059818, by rfl⟩ : syracuseStep 1413091 = 2119637) B2119637
theorem B4526065 : Blo 1411525 4526065 := bstep (se 2 (by rfl) ⟨1697274, by rfl⟩ : syracuseStep 4526065 = 3394549) B3394549
theorem B1413107 : Blo 1411525 1413107 := bstep (se 1 (by rfl) ⟨1059830, by rfl⟩ : syracuseStep 1413107 = 2119661) B2119661
theorem B2117633 : Blo 1411525 2117633 := bstep (se 2 (by rfl) ⟨794112, by rfl⟩ : syracuseStep 2117633 = 1588225) B1588225
theorem B1413123 : Blo 1411525 1413123 := bstep (se 1 (by rfl) ⟨1059842, by rfl⟩ : syracuseStep 1413123 = 2119685) B2119685
theorem B2117651 : Blo 1411525 2117651 := bstep (se 1 (by rfl) ⟨1588238, by rfl⟩ : syracuseStep 2117651 = 3176477) B3176477
theorem B1413139 : Blo 1411525 1413139 := bstep (se 1 (by rfl) ⟨1059854, by rfl⟩ : syracuseStep 1413139 = 2119709) B2119709
theorem B2011169 : Blo 1411525 2011169 := bstep (se 2 (by rfl) ⟨754188, by rfl⟩ : syracuseStep 2011169 = 1508377) B1508377
theorem B1413155 : Blo 1411525 1413155 := bstep (se 1 (by rfl) ⟨1059866, by rfl⟩ : syracuseStep 1413155 = 2119733) B2119733
theorem B2117681 : Blo 1411525 2117681 := bstep (se 2 (by rfl) ⟨794130, by rfl⟩ : syracuseStep 2117681 = 1588261) B1588261
theorem B1413171 : Blo 1411525 1413171 := bstep (se 1 (by rfl) ⟨1059878, by rfl⟩ : syracuseStep 1413171 = 2119757) B2119757
theorem B2117699 : Blo 1411525 2117699 := bstep (se 1 (by rfl) ⟨1588274, by rfl⟩ : syracuseStep 2117699 = 3176549) B3176549
theorem B1413187 : Blo 1411525 1413187 := bstep (se 1 (by rfl) ⟨1059890, by rfl⟩ : syracuseStep 1413187 = 2119781) B2119781
theorem B1413203 : Blo 1411525 1413203 := bstep (se 1 (by rfl) ⟨1059902, by rfl⟩ : syracuseStep 1413203 = 2119805) B2119805
theorem B2117729 : Blo 1411525 2117729 := bstep (se 2 (by rfl) ⟨794148, by rfl⟩ : syracuseStep 2117729 = 1588297) B1588297
theorem B1413219 : Blo 1411525 1413219 := bstep (se 1 (by rfl) ⟨1059914, by rfl⟩ : syracuseStep 1413219 = 2119829) B2119829
theorem B13578353 : Blo 1411525 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B8048753 : Blo 1411525 8048753 := bstep (se 2 (by rfl) ⟨3018282, by rfl⟩ : syracuseStep 8048753 = 6036565) B6036565
theorem B2117747 : Blo 1411525 2117747 := bstep (se 1 (by rfl) ⟨1588310, by rfl⟩ : syracuseStep 2117747 = 3176621) B3176621
theorem B1413235 : Blo 1411525 1413235 := bstep (se 1 (by rfl) ⟨1059926, by rfl⟩ : syracuseStep 1413235 = 2119853) B2119853
theorem B1413251 : Blo 1411525 1413251 := bstep (se 1 (by rfl) ⟨1059938, by rfl⟩ : syracuseStep 1413251 = 2119877) B2119877
theorem B2117777 : Blo 1411525 2117777 := bstep (se 2 (by rfl) ⟨794166, by rfl⟩ : syracuseStep 2117777 = 1588333) B1588333
theorem B1413267 : Blo 1411525 1413267 := bstep (se 1 (by rfl) ⟨1059950, by rfl⟩ : syracuseStep 1413267 = 2119901) B2119901
theorem B2117795 : Blo 1411525 2117795 := bstep (se 1 (by rfl) ⟨1588346, by rfl⟩ : syracuseStep 2117795 = 3176693) B3176693
theorem B1413283 : Blo 1411525 1413283 := bstep (se 1 (by rfl) ⟨1059962, by rfl⟩ : syracuseStep 1413283 = 2119925) B2119925
theorem B1413299 : Blo 1411525 1413299 := bstep (se 1 (by rfl) ⟨1059974, by rfl⟩ : syracuseStep 1413299 = 2119949) B2119949
theorem B2117825 : Blo 1411525 2117825 := bstep (se 2 (by rfl) ⟨794184, by rfl⟩ : syracuseStep 2117825 = 1588369) B1588369
theorem B1413315 : Blo 1411525 1413315 := bstep (se 1 (by rfl) ⟨1059986, by rfl⟩ : syracuseStep 1413315 = 2119973) B2119973
theorem B2117843 : Blo 1411525 2117843 := bstep (se 1 (by rfl) ⟨1588382, by rfl⟩ : syracuseStep 2117843 = 3176765) B3176765
theorem B1413331 : Blo 1411525 1413331 := bstep (se 1 (by rfl) ⟨1059998, by rfl⟩ : syracuseStep 1413331 = 2119997) B2119997
theorem B1413347 : Blo 1411525 1413347 := bstep (se 1 (by rfl) ⟨1060010, by rfl⟩ : syracuseStep 1413347 = 2120021) B2120021
theorem B2117873 : Blo 1411525 2117873 := bstep (se 2 (by rfl) ⟨794202, by rfl⟩ : syracuseStep 2117873 = 1588405) B1588405
theorem B1413363 : Blo 1411525 1413363 := bstep (se 1 (by rfl) ⟨1060022, by rfl⟩ : syracuseStep 1413363 = 2120045) B2120045
theorem B2117891 : Blo 1411525 2117891 := bstep (se 1 (by rfl) ⟨1588418, by rfl⟩ : syracuseStep 2117891 = 3176837) B3176837
theorem B1413379 : Blo 1411525 1413379 := bstep (se 1 (by rfl) ⟨1060034, by rfl⟩ : syracuseStep 1413379 = 2120069) B2120069
theorem B3395857 : Blo 1411525 3395857 := bstep (se 2 (by rfl) ⟨1273446, by rfl⟩ : syracuseStep 3395857 = 2546893) B2546893
theorem B1413395 : Blo 1411525 1413395 := bstep (se 1 (by rfl) ⟨1060046, by rfl⟩ : syracuseStep 1413395 = 2120093) B2120093
theorem B2117921 : Blo 1411525 2117921 := bstep (se 2 (by rfl) ⟨794220, by rfl⟩ : syracuseStep 2117921 = 1588441) B1588441
theorem B1413411 : Blo 1411525 1413411 := bstep (se 1 (by rfl) ⟨1060058, by rfl⟩ : syracuseStep 1413411 = 2120117) B2120117
theorem B2117939 : Blo 1411525 2117939 := bstep (se 1 (by rfl) ⟨1588454, by rfl⟩ : syracuseStep 2117939 = 3176909) B3176909
theorem B1413427 : Blo 1411525 1413427 := bstep (se 1 (by rfl) ⟨1060070, by rfl⟩ : syracuseStep 1413427 = 2120141) B2120141
theorem B1413443 : Blo 1411525 1413443 := bstep (se 1 (by rfl) ⟨1060082, by rfl⟩ : syracuseStep 1413443 = 2120165) B2120165
theorem B2117969 : Blo 1411525 2117969 := bstep (se 2 (by rfl) ⟨794238, by rfl⟩ : syracuseStep 2117969 = 1588477) B1588477
theorem B1470803 : Blo 1411525 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B1413459 : Blo 1411525 1413459 := bstep (se 1 (by rfl) ⟨1060094, by rfl⟩ : syracuseStep 1413459 = 2120189) B2120189
theorem B2117987 : Blo 1411525 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B1413475 : Blo 1411525 1413475 := bstep (se 1 (by rfl) ⟨1060106, by rfl⟩ : syracuseStep 1413475 = 2120213) B2120213
theorem B1413491 : Blo 1411525 1413491 := bstep (se 1 (by rfl) ⟨1060118, by rfl⟩ : syracuseStep 1413491 = 2120237) B2120237
theorem B2118017 : Blo 1411525 2118017 := bstep (se 2 (by rfl) ⟨794256, by rfl⟩ : syracuseStep 2118017 = 1588513) B1588513
theorem B1413507 : Blo 1411525 1413507 := bstep (se 1 (by rfl) ⟨1060130, by rfl⟩ : syracuseStep 1413507 = 2120261) B2120261
theorem B2118035 : Blo 1411525 2118035 := bstep (se 1 (by rfl) ⟨1588526, by rfl⟩ : syracuseStep 2118035 = 3177053) B3177053
theorem B1413523 : Blo 1411525 1413523 := bstep (se 1 (by rfl) ⟨1060142, by rfl⟩ : syracuseStep 1413523 = 2120285) B2120285
theorem B2118065 : Blo 1411525 2118065 := bstep (se 2 (by rfl) ⟨794274, by rfl⟩ : syracuseStep 2118065 = 1588549) B1588549
theorem B2118083 : Blo 1411525 2118083 := bstep (se 1 (by rfl) ⟨1588562, by rfl⟩ : syracuseStep 2118083 = 3177125) B3177125
theorem B2118113 : Blo 1411525 2118113 := bstep (se 2 (by rfl) ⟨794292, by rfl⟩ : syracuseStep 2118113 = 1588585) B1588585
theorem B2118131 : Blo 1411525 2118131 := bstep (se 1 (by rfl) ⟨1588598, by rfl⟩ : syracuseStep 2118131 = 3177197) B3177197
theorem B2118161 : Blo 1411525 2118161 := bstep (se 2 (by rfl) ⟨794310, by rfl⟩ : syracuseStep 2118161 = 1588621) B1588621
theorem B2118179 : Blo 1411525 2118179 := bstep (se 1 (by rfl) ⟨1588634, by rfl⟩ : syracuseStep 2118179 = 3177269) B3177269
theorem B2118209 : Blo 1411525 2118209 := bstep (se 2 (by rfl) ⟨794328, by rfl⟩ : syracuseStep 2118209 = 1588657) B1588657
theorem B8589901 : Blo 1411525 8589901 := bstep (se 3 (by rfl) ⟨1610606, by rfl⟩ : syracuseStep 8589901 = 3221213) B3221213
theorem B2118227 : Blo 1411525 2118227 := bstep (se 1 (by rfl) ⟨1588670, by rfl⟩ : syracuseStep 2118227 = 3177341) B3177341
theorem B2118257 : Blo 1411525 2118257 := bstep (se 2 (by rfl) ⟨794346, by rfl⟩ : syracuseStep 2118257 = 1588693) B1588693
theorem B3576433 : Blo 1411525 3576433 := bstep (se 2 (by rfl) ⟨1341162, by rfl⟩ : syracuseStep 3576433 = 2682325) B2682325
theorem B2118275 : Blo 1411525 2118275 := bstep (se 1 (by rfl) ⟨1588706, by rfl⟩ : syracuseStep 2118275 = 3177413) B3177413
theorem B2118305 : Blo 1411525 2118305 := bstep (se 2 (by rfl) ⟨794364, by rfl⟩ : syracuseStep 2118305 = 1588729) B1588729
theorem B2118323 : Blo 1411525 2118323 := bstep (se 1 (by rfl) ⟨1588742, by rfl⟩ : syracuseStep 2118323 = 3177485) B3177485
theorem B4764365 : Blo 1411525 4764365 := bstep (se 3 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 4764365 = 1786637) B1786637
theorem B4297421 : Blo 1411525 4297421 := bstep (se 3 (by rfl) ⟨805766, by rfl⟩ : syracuseStep 4297421 = 1611533) B1611533
theorem B2118353 : Blo 1411525 2118353 := bstep (se 2 (by rfl) ⟨794382, by rfl⟩ : syracuseStep 2118353 = 1588765) B1588765
theorem B2118371 : Blo 1411525 2118371 := bstep (se 1 (by rfl) ⟨1588778, by rfl⟩ : syracuseStep 2118371 = 3177557) B3177557
theorem B2118401 : Blo 1411525 2118401 := bstep (se 2 (by rfl) ⟨794400, by rfl⟩ : syracuseStep 2118401 = 1588801) B1588801
theorem B4764419 : Blo 1411525 4764419 := bstep (se 1 (by rfl) ⟨3573314, by rfl⟩ : syracuseStep 4764419 = 7146629) B7146629
theorem B12071693 : Blo 1411525 12071693 := bstep (se 3 (by rfl) ⟨2263442, by rfl⟩ : syracuseStep 12071693 = 4526885) B4526885
theorem B2118419 : Blo 1411525 2118419 := bstep (se 1 (by rfl) ⟨1588814, by rfl⟩ : syracuseStep 2118419 = 3177629) B3177629
theorem B92943125 : Blo 1411525 92943125 := bstep (se 6 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 92943125 = 4356709) B4356709
theorem B2118449 : Blo 1411525 2118449 := bstep (se 2 (by rfl) ⟨794418, by rfl⟩ : syracuseStep 2118449 = 1588837) B1588837
theorem B2118467 : Blo 1411525 2118467 := bstep (se 1 (by rfl) ⟨1588850, by rfl⟩ : syracuseStep 2118467 = 3177701) B3177701
theorem B2118497 : Blo 1411525 2118497 := bstep (se 2 (by rfl) ⟨794436, by rfl⟩ : syracuseStep 2118497 = 1588873) B1588873
theorem B2118515 : Blo 1411525 2118515 := bstep (se 1 (by rfl) ⟨1588886, by rfl⟩ : syracuseStep 2118515 = 3177773) B3177773
theorem B3576707 : Blo 1411525 3576707 := bstep (se 1 (by rfl) ⟨2682530, by rfl⟩ : syracuseStep 3576707 = 5365061) B5365061
theorem B2012035 : Blo 1411525 2012035 := bstep (se 1 (by rfl) ⟨1509026, by rfl⟩ : syracuseStep 2012035 = 3018053) B3018053
theorem B2118545 : Blo 1411525 2118545 := bstep (se 2 (by rfl) ⟨794454, by rfl⟩ : syracuseStep 2118545 = 1588909) B1588909
theorem B2118563 : Blo 1411525 2118563 := bstep (se 1 (by rfl) ⟨1588922, by rfl⟩ : syracuseStep 2118563 = 3177845) B3177845
theorem B2118593 : Blo 1411525 2118593 := bstep (se 2 (by rfl) ⟨794472, by rfl⟩ : syracuseStep 2118593 = 1588945) B1588945
theorem B6443981 : Blo 1411525 6443981 := bstep (se 3 (by rfl) ⟨1208246, by rfl⟩ : syracuseStep 6443981 = 2416493) B2416493
theorem B2118611 : Blo 1411525 2118611 := bstep (se 1 (by rfl) ⟨1588958, by rfl⟩ : syracuseStep 2118611 = 3177917) B3177917
theorem B4412387 : Blo 1411525 4412387 := bstep (se 1 (by rfl) ⟨3309290, by rfl⟩ : syracuseStep 4412387 = 6618581) B6618581
theorem B2012131 : Blo 1411525 2012131 := bstep (se 1 (by rfl) ⟨1509098, by rfl⟩ : syracuseStep 2012131 = 3018197) B3018197
theorem B2118641 : Blo 1411525 2118641 := bstep (se 2 (by rfl) ⟨794490, by rfl⟩ : syracuseStep 2118641 = 1588981) B1588981
theorem B2118659 : Blo 1411525 2118659 := bstep (se 1 (by rfl) ⟨1588994, by rfl⟩ : syracuseStep 2118659 = 3177989) B3177989
theorem B4764689 : Blo 1411525 4764689 := bstep (se 2 (by rfl) ⟨1786758, by rfl⟩ : syracuseStep 4764689 = 3573517) B3573517
theorem B2118689 : Blo 1411525 2118689 := bstep (se 2 (by rfl) ⟨794508, by rfl⟩ : syracuseStep 2118689 = 1589017) B1589017
theorem B2118707 : Blo 1411525 2118707 := bstep (se 1 (by rfl) ⟨1589030, by rfl⟩ : syracuseStep 2118707 = 3178061) B3178061
theorem B3576899 : Blo 1411525 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B4527181 : Blo 1411525 4527181 := bstep (se 3 (by rfl) ⟨848846, by rfl⟩ : syracuseStep 4527181 = 1697693) B1697693
theorem B2118737 : Blo 1411525 2118737 := bstep (se 2 (by rfl) ⟨794526, by rfl⟩ : syracuseStep 2118737 = 1589053) B1589053
theorem B2118755 : Blo 1411525 2118755 := bstep (se 1 (by rfl) ⟨1589066, by rfl⟩ : syracuseStep 2118755 = 3178133) B3178133
theorem B2118785 : Blo 1411525 2118785 := bstep (se 2 (by rfl) ⟨794544, by rfl⟩ : syracuseStep 2118785 = 1589089) B1589089
theorem B4527245 : Blo 1411525 4527245 := bstep (se 3 (by rfl) ⟨848858, by rfl⟩ : syracuseStep 4527245 = 1697717) B1697717
theorem B2118803 : Blo 1411525 2118803 := bstep (se 1 (by rfl) ⟨1589102, by rfl⟩ : syracuseStep 2118803 = 3178205) B3178205
theorem B2118833 : Blo 1411525 2118833 := bstep (se 2 (by rfl) ⟨794562, by rfl⟩ : syracuseStep 2118833 = 1589125) B1589125
theorem B2118851 : Blo 1411525 2118851 := bstep (se 1 (by rfl) ⟨1589138, by rfl⟩ : syracuseStep 2118851 = 3178277) B3178277
theorem B2118881 : Blo 1411525 2118881 := bstep (se 2 (by rfl) ⟨794580, by rfl⟩ : syracuseStep 2118881 = 1589161) B1589161
theorem B2118899 : Blo 1411525 2118899 := bstep (se 1 (by rfl) ⟨1589174, by rfl⟩ : syracuseStep 2118899 = 3178349) B3178349
theorem B2118929 : Blo 1411525 2118929 := bstep (se 2 (by rfl) ⟨794598, by rfl⟩ : syracuseStep 2118929 = 1589197) B1589197
theorem B2118947 : Blo 1411525 2118947 := bstep (se 1 (by rfl) ⟨1589210, by rfl⟩ : syracuseStep 2118947 = 3178421) B3178421
theorem B2118977 : Blo 1411525 2118977 := bstep (se 2 (by rfl) ⟨794616, by rfl⟩ : syracuseStep 2118977 = 1589233) B1589233
theorem B2118995 : Blo 1411525 2118995 := bstep (se 1 (by rfl) ⟨1589246, by rfl⟩ : syracuseStep 2118995 = 3178493) B3178493
theorem B2119025 : Blo 1411525 2119025 := bstep (se 2 (by rfl) ⟨794634, by rfl⟩ : syracuseStep 2119025 = 1589269) B1589269
theorem B1529203 : Blo 1411525 1529203 := bstep (se 1 (by rfl) ⟨1146902, by rfl⟩ : syracuseStep 1529203 = 2293805) B2293805
theorem B2119043 : Blo 1411525 2119043 := bstep (se 1 (by rfl) ⟨1589282, by rfl⟩ : syracuseStep 2119043 = 3178565) B3178565
theorem B2119073 : Blo 1411525 2119073 := bstep (se 2 (by rfl) ⟨794652, by rfl⟩ : syracuseStep 2119073 = 1589305) B1589305
theorem B2119091 : Blo 1411525 2119091 := bstep (se 1 (by rfl) ⟨1589318, by rfl⟩ : syracuseStep 2119091 = 3178637) B3178637
theorem B2119121 : Blo 1411525 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B2119139 : Blo 1411525 2119139 := bstep (se 1 (by rfl) ⟨1589354, by rfl⟩ : syracuseStep 2119139 = 3178709) B3178709
theorem B2119169 : Blo 1411525 2119169 := bstep (se 2 (by rfl) ⟨794688, by rfl⟩ : syracuseStep 2119169 = 1589377) B1589377
theorem B2119187 : Blo 1411525 2119187 := bstep (se 1 (by rfl) ⟨1589390, by rfl⟩ : syracuseStep 2119187 = 3178781) B3178781
theorem B8050211 : Blo 1411525 8050211 := bstep (se 1 (by rfl) ⟨6037658, by rfl⟩ : syracuseStep 8050211 = 12075317) B12075317
theorem B4765229 : Blo 1411525 4765229 := bstep (se 3 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 4765229 = 1786961) B1786961
theorem B2119217 : Blo 1411525 2119217 := bstep (se 2 (by rfl) ⟨794706, by rfl⟩ : syracuseStep 2119217 = 1589413) B1589413
theorem B2119235 : Blo 1411525 2119235 := bstep (se 1 (by rfl) ⟨1589426, by rfl⟩ : syracuseStep 2119235 = 3178853) B3178853
theorem B2119265 : Blo 1411525 2119265 := bstep (se 2 (by rfl) ⟨794724, by rfl⟩ : syracuseStep 2119265 = 1589449) B1589449
theorem B4765283 : Blo 1411525 4765283 := bstep (se 1 (by rfl) ⟨3573962, by rfl⟩ : syracuseStep 4765283 = 7147925) B7147925
theorem B2119283 : Blo 1411525 2119283 := bstep (se 1 (by rfl) ⟨1589462, by rfl⟩ : syracuseStep 2119283 = 3178925) B3178925
theorem B4019843 : Blo 1411525 4019843 := bstep (se 1 (by rfl) ⟨3014882, by rfl⟩ : syracuseStep 4019843 = 6029765) B6029765
theorem B16094861 : Blo 1411525 16094861 := bstep (se 3 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 16094861 = 6035573) B6035573
theorem B3176081 : Blo 1411525 3176081 := bstep (se 2 (by rfl) ⟨1191030, by rfl⟩ : syracuseStep 3176081 = 2382061) B2382061
theorem B2119313 : Blo 1411525 2119313 := bstep (se 2 (by rfl) ⟨794742, by rfl⟩ : syracuseStep 2119313 = 1589485) B1589485
theorem B3176099 : Blo 1411525 3176099 := bstep (se 1 (by rfl) ⟨2382074, by rfl⟩ : syracuseStep 3176099 = 4764149) B4764149
theorem B2119331 : Blo 1411525 2119331 := bstep (se 1 (by rfl) ⟨1589498, by rfl⟩ : syracuseStep 2119331 = 3178997) B3178997
theorem B2119361 : Blo 1411525 2119361 := bstep (se 2 (by rfl) ⟨794760, by rfl⟩ : syracuseStep 2119361 = 1589521) B1589521
theorem B5363405 : Blo 1411525 5363405 := bstep (se 3 (by rfl) ⟨1005638, by rfl⟩ : syracuseStep 5363405 = 2011277) B2011277
theorem B2119379 : Blo 1411525 2119379 := bstep (se 1 (by rfl) ⟨1589534, by rfl⟩ : syracuseStep 2119379 = 3179069) B3179069
theorem B2545393 : Blo 1411525 2545393 := bstep (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) B1909045
theorem B2119409 : Blo 1411525 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B2119427 : Blo 1411525 2119427 := bstep (se 1 (by rfl) ⟨1589570, by rfl⟩ : syracuseStep 2119427 = 3179141) B3179141
theorem B2119457 : Blo 1411525 2119457 := bstep (se 2 (by rfl) ⟨794796, by rfl⟩ : syracuseStep 2119457 = 1589593) B1589593
theorem B2119475 : Blo 1411525 2119475 := bstep (se 1 (by rfl) ⟨1589606, by rfl⟩ : syracuseStep 2119475 = 3179213) B3179213
theorem B2119505 : Blo 1411525 2119505 := bstep (se 2 (by rfl) ⟨794814, by rfl⟩ : syracuseStep 2119505 = 1589629) B1589629
theorem B2119523 : Blo 1411525 2119523 := bstep (se 1 (by rfl) ⟨1589642, by rfl⟩ : syracuseStep 2119523 = 3179285) B3179285
theorem B4765553 : Blo 1411525 4765553 := bstep (se 2 (by rfl) ⟨1787082, by rfl⟩ : syracuseStep 4765553 = 3574165) B3574165
theorem B2119553 : Blo 1411525 2119553 := bstep (se 2 (by rfl) ⟨794832, by rfl⟩ : syracuseStep 2119553 = 1589665) B1589665
theorem B2119571 : Blo 1411525 2119571 := bstep (se 1 (by rfl) ⟨1589678, by rfl⟩ : syracuseStep 2119571 = 3179357) B3179357
theorem B3176369 : Blo 1411525 3176369 := bstep (se 2 (by rfl) ⟨1191138, by rfl⟩ : syracuseStep 3176369 = 2382277) B2382277
theorem B2119601 : Blo 1411525 2119601 := bstep (se 2 (by rfl) ⟨794850, by rfl⟩ : syracuseStep 2119601 = 1589701) B1589701
theorem B3176387 : Blo 1411525 3176387 := bstep (se 1 (by rfl) ⟨2382290, by rfl⟩ : syracuseStep 3176387 = 4764581) B4764581
theorem B2119619 : Blo 1411525 2119619 := bstep (se 1 (by rfl) ⟨1589714, by rfl⟩ : syracuseStep 2119619 = 3179429) B3179429
theorem B2119649 : Blo 1411525 2119649 := bstep (se 2 (by rfl) ⟨794868, by rfl⟩ : syracuseStep 2119649 = 1589737) B1589737
theorem B3577841 : Blo 1411525 3577841 := bstep (se 2 (by rfl) ⟨1341690, by rfl⟩ : syracuseStep 3577841 = 2683381) B2683381
theorem B2119667 : Blo 1411525 2119667 := bstep (se 1 (by rfl) ⟨1589750, by rfl⟩ : syracuseStep 2119667 = 3179501) B3179501
theorem B4413457 : Blo 1411525 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B2119697 : Blo 1411525 2119697 := bstep (se 2 (by rfl) ⟨794886, by rfl⟩ : syracuseStep 2119697 = 1589773) B1589773
theorem B2119715 : Blo 1411525 2119715 := bstep (se 1 (by rfl) ⟨1589786, by rfl⟩ : syracuseStep 2119715 = 3179573) B3179573
theorem B3577891 : Blo 1411525 3577891 := bstep (se 1 (by rfl) ⟨2683418, by rfl⟩ : syracuseStep 3577891 = 5366837) B5366837
theorem B2119745 : Blo 1411525 2119745 := bstep (se 2 (by rfl) ⟨794904, by rfl⟩ : syracuseStep 2119745 = 1589809) B1589809
theorem B2119763 : Blo 1411525 2119763 := bstep (se 1 (by rfl) ⟨1589822, by rfl⟩ : syracuseStep 2119763 = 3179645) B3179645
theorem B2119793 : Blo 1411525 2119793 := bstep (se 2 (by rfl) ⟨794922, by rfl⟩ : syracuseStep 2119793 = 1589845) B1589845
theorem B2381953 : Blo 1411525 2381953 := bstep (se 2 (by rfl) ⟨893232, by rfl⟩ : syracuseStep 2381953 = 1786465) B1786465
theorem B2119811 : Blo 1411525 2119811 := bstep (se 1 (by rfl) ⟨1589858, by rfl⟩ : syracuseStep 2119811 = 3179717) B3179717
theorem B2119841 : Blo 1411525 2119841 := bstep (se 2 (by rfl) ⟨794940, by rfl⟩ : syracuseStep 2119841 = 1589881) B1589881
theorem B2381987 : Blo 1411525 2381987 := bstep (se 1 (by rfl) ⟨1786490, by rfl⟩ : syracuseStep 2381987 = 3572981) B3572981
theorem B2177201 : Blo 1411525 2177201 := bstep (se 2 (by rfl) ⟨816450, by rfl⟩ : syracuseStep 2177201 = 1632901) B1632901
theorem B2119859 : Blo 1411525 2119859 := bstep (se 1 (by rfl) ⟨1589894, by rfl⟩ : syracuseStep 2119859 = 3179789) B3179789
theorem B9173197 : Blo 1411525 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B3176657 : Blo 1411525 3176657 := bstep (se 2 (by rfl) ⟨1191246, by rfl⟩ : syracuseStep 3176657 = 2382493) B2382493
theorem B2119889 : Blo 1411525 2119889 := bstep (se 2 (by rfl) ⟨794958, by rfl⟩ : syracuseStep 2119889 = 1589917) B1589917
theorem B3176675 : Blo 1411525 3176675 := bstep (se 1 (by rfl) ⟨2382506, by rfl⟩ : syracuseStep 3176675 = 4765013) B4765013
theorem B20355299 : Blo 1411525 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B2119907 : Blo 1411525 2119907 := bstep (se 1 (by rfl) ⟨1589930, by rfl⟩ : syracuseStep 2119907 = 3179861) B3179861
theorem B2119937 : Blo 1411525 2119937 := bstep (se 2 (by rfl) ⟨794976, by rfl⟩ : syracuseStep 2119937 = 1589953) B1589953
theorem B4831505 : Blo 1411525 4831505 := bstep (se 2 (by rfl) ⟨1811814, by rfl⟩ : syracuseStep 4831505 = 3623629) B3623629
theorem B2119955 : Blo 1411525 2119955 := bstep (se 1 (by rfl) ⟨1589966, by rfl⟩ : syracuseStep 2119955 = 3179933) B3179933
theorem B48953621 : Blo 1411525 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B2382115 : Blo 1411525 2382115 := bstep (se 1 (by rfl) ⟨1786586, by rfl⟩ : syracuseStep 2382115 = 3573173) B3573173
theorem B2119985 : Blo 1411525 2119985 := bstep (se 2 (by rfl) ⟨794994, by rfl⟩ : syracuseStep 2119985 = 1589989) B1589989
theorem B2120003 : Blo 1411525 2120003 := bstep (se 1 (by rfl) ⟨1590002, by rfl⟩ : syracuseStep 2120003 = 3180005) B3180005
theorem B2120033 : Blo 1411525 2120033 := bstep (se 2 (by rfl) ⟨795012, by rfl⟩ : syracuseStep 2120033 = 1590025) B1590025
theorem B2120051 : Blo 1411525 2120051 := bstep (se 1 (by rfl) ⟨1590038, by rfl⟩ : syracuseStep 2120051 = 3180077) B3180077
theorem B4766093 : Blo 1411525 4766093 := bstep (se 3 (by rfl) ⟨893642, by rfl⟩ : syracuseStep 4766093 = 1787285) B1787285
theorem B2120081 : Blo 1411525 2120081 := bstep (se 2 (by rfl) ⟨795030, by rfl⟩ : syracuseStep 2120081 = 1590061) B1590061
theorem B2120099 : Blo 1411525 2120099 := bstep (se 1 (by rfl) ⟨1590074, by rfl⟩ : syracuseStep 2120099 = 3180149) B3180149
theorem B2382257 : Blo 1411525 2382257 := bstep (se 2 (by rfl) ⟨893346, by rfl⟩ : syracuseStep 2382257 = 1786693) B1786693
theorem B2120129 : Blo 1411525 2120129 := bstep (se 2 (by rfl) ⟨795048, by rfl⟩ : syracuseStep 2120129 = 1590097) B1590097
theorem B4766147 : Blo 1411525 4766147 := bstep (se 1 (by rfl) ⟨3574610, by rfl⟩ : syracuseStep 4766147 = 7149221) B7149221
theorem B3488195 : Blo 1411525 3488195 := bstep (se 1 (by rfl) ⟨2616146, by rfl⟩ : syracuseStep 3488195 = 5232293) B5232293
theorem B3815885 : Blo 1411525 3815885 := bstep (se 3 (by rfl) ⟨715478, by rfl⟩ : syracuseStep 3815885 = 1430957) B1430957
theorem B4135373 : Blo 1411525 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B2120147 : Blo 1411525 2120147 := bstep (se 1 (by rfl) ⟨1590110, by rfl⟩ : syracuseStep 2120147 = 3180221) B3180221
theorem B3176945 : Blo 1411525 3176945 := bstep (se 2 (by rfl) ⟨1191354, by rfl⟩ : syracuseStep 3176945 = 2382709) B2382709
theorem B2120177 : Blo 1411525 2120177 := bstep (se 2 (by rfl) ⟨795066, by rfl⟩ : syracuseStep 2120177 = 1590133) B1590133
theorem B3176963 : Blo 1411525 3176963 := bstep (se 1 (by rfl) ⟨2382722, by rfl⟩ : syracuseStep 3176963 = 4765445) B4765445
theorem B2120195 : Blo 1411525 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B11450893 : Blo 1411525 11450893 := bstep (se 3 (by rfl) ⟨2147042, by rfl⟩ : syracuseStep 11450893 = 4294085) B4294085
theorem B2120225 : Blo 1411525 2120225 := bstep (se 2 (by rfl) ⟨795084, by rfl⟩ : syracuseStep 2120225 = 1590169) B1590169
theorem B2382385 : Blo 1411525 2382385 := bstep (se 2 (by rfl) ⟨893394, by rfl⟩ : syracuseStep 2382385 = 1786789) B1786789
theorem B2120243 : Blo 1411525 2120243 := bstep (se 1 (by rfl) ⟨1590182, by rfl⟩ : syracuseStep 2120243 = 3180365) B3180365
theorem B77290037 : Blo 1411525 77290037 := bstep (se 5 (by rfl) ⟨3622970, by rfl⟩ : syracuseStep 77290037 = 7245941) B7245941
theorem B2120273 : Blo 1411525 2120273 := bstep (se 2 (by rfl) ⟨795102, by rfl⟩ : syracuseStep 2120273 = 1590205) B1590205
theorem B2382419 : Blo 1411525 2382419 := bstep (se 1 (by rfl) ⟨1786814, by rfl⟩ : syracuseStep 2382419 = 3573629) B3573629
theorem B7150193 : Blo 1411525 7150193 := bstep (se 2 (by rfl) ⟨2681322, by rfl⟩ : syracuseStep 7150193 = 5362645) B5362645
theorem B4766417 : Blo 1411525 4766417 := bstep (se 2 (by rfl) ⟨1787406, by rfl⟩ : syracuseStep 4766417 = 3574813) B3574813
theorem B2382547 : Blo 1411525 2382547 := bstep (se 1 (by rfl) ⟨1786910, by rfl⟩ : syracuseStep 2382547 = 3573821) B3573821
theorem B3816209 : Blo 1411525 3816209 := bstep (se 2 (by rfl) ⟨1431078, by rfl⟩ : syracuseStep 3816209 = 2862157) B2862157
theorem B3177233 : Blo 1411525 3177233 := bstep (se 2 (by rfl) ⟨1191462, by rfl⟩ : syracuseStep 3177233 = 2382925) B2382925
theorem B3177251 : Blo 1411525 3177251 := bstep (se 1 (by rfl) ⟨2382938, by rfl⟩ : syracuseStep 3177251 = 4765877) B4765877
theorem B4021073 : Blo 1411525 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B2382689 : Blo 1411525 2382689 := bstep (se 2 (by rfl) ⟨893508, by rfl⟩ : syracuseStep 2382689 = 1787017) B1787017
theorem B1588099 : Blo 1411525 1588099 := bstep (se 1 (by rfl) ⟨1191074, by rfl⟩ : syracuseStep 1588099 = 2382149) B2382149
theorem B2382817 : Blo 1411525 2382817 := bstep (se 2 (by rfl) ⟨893556, by rfl⟩ : syracuseStep 2382817 = 1787113) B1787113
theorem B2448353 : Blo 1411525 2448353 := bstep (se 2 (by rfl) ⟨918132, by rfl⟩ : syracuseStep 2448353 = 1836265) B1836265
theorem B2382851 : Blo 1411525 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B1588243 : Blo 1411525 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B6036515 : Blo 1411525 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B3177521 : Blo 1411525 3177521 := bstep (se 2 (by rfl) ⟨1191570, by rfl⟩ : syracuseStep 3177521 = 2383141) B2383141
theorem B3177539 : Blo 1411525 3177539 := bstep (se 1 (by rfl) ⟨2383154, by rfl⟩ : syracuseStep 3177539 = 4766309) B4766309
theorem B2382979 : Blo 1411525 2382979 := bstep (se 1 (by rfl) ⟨1787234, by rfl⟩ : syracuseStep 2382979 = 3574469) B3574469
theorem B1588387 : Blo 1411525 1588387 := bstep (se 1 (by rfl) ⟨1191290, by rfl⟩ : syracuseStep 1588387 = 2382581) B2382581
theorem B7634083 : Blo 1411525 7634083 := bstep (se 1 (by rfl) ⟨5725562, by rfl⟩ : syracuseStep 7634083 = 11451125) B11451125
theorem B4586701 : Blo 1411525 4586701 := bstep (se 3 (by rfl) ⟨860006, by rfl⟩ : syracuseStep 4586701 = 1720013) B1720013
theorem B4766957 : Blo 1411525 4766957 := bstep (se 3 (by rfl) ⟨893804, by rfl⟩ : syracuseStep 4766957 = 1787609) B1787609
theorem B2383121 : Blo 1411525 2383121 := bstep (se 2 (by rfl) ⟨893670, by rfl⟩ : syracuseStep 2383121 = 1787341) B1787341
theorem B4767011 : Blo 1411525 4767011 := bstep (se 1 (by rfl) ⟨3575258, by rfl⟩ : syracuseStep 4767011 = 7150517) B7150517
theorem B1588531 : Blo 1411525 1588531 := bstep (se 1 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 1588531 = 2382797) B2382797
theorem B3177809 : Blo 1411525 3177809 := bstep (se 2 (by rfl) ⟨1191678, by rfl⟩ : syracuseStep 3177809 = 2383357) B2383357
theorem B3177827 : Blo 1411525 3177827 := bstep (se 1 (by rfl) ⟨2383370, by rfl⟩ : syracuseStep 3177827 = 4766741) B4766741
theorem B2383249 : Blo 1411525 2383249 := bstep (se 2 (by rfl) ⟨893718, by rfl⟩ : syracuseStep 2383249 = 1787437) B1787437
theorem B2383283 : Blo 1411525 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B19332533 : Blo 1411525 19332533 := bstep (se 5 (by rfl) ⟨906212, by rfl⟩ : syracuseStep 19332533 = 1812425) B1812425
theorem B1588675 : Blo 1411525 1588675 := bstep (se 1 (by rfl) ⟨1191506, by rfl⟩ : syracuseStep 1588675 = 2383013) B2383013
theorem B4767281 : Blo 1411525 4767281 := bstep (se 2 (by rfl) ⟨1787730, by rfl⟩ : syracuseStep 4767281 = 3575461) B3575461
theorem B2383411 : Blo 1411525 2383411 := bstep (se 1 (by rfl) ⟨1787558, by rfl⟩ : syracuseStep 2383411 = 3575117) B3575117
theorem B1908289 : Blo 1411525 1908289 := bstep (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) B1431217
theorem B1588819 : Blo 1411525 1588819 := bstep (se 1 (by rfl) ⟨1191614, by rfl⟩ : syracuseStep 1588819 = 2383229) B2383229
theorem B3178097 : Blo 1411525 3178097 := bstep (se 2 (by rfl) ⟨1191786, by rfl⟩ : syracuseStep 3178097 = 2383573) B2383573
theorem B3178115 : Blo 1411525 3178115 := bstep (se 1 (by rfl) ⟨2383586, by rfl⟩ : syracuseStep 3178115 = 4767173) B4767173
theorem B2383553 : Blo 1411525 2383553 := bstep (se 2 (by rfl) ⟨893832, by rfl⟩ : syracuseStep 2383553 = 1787665) B1787665
theorem B2039491 : Blo 1411525 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B1588963 : Blo 1411525 1588963 := bstep (se 1 (by rfl) ⟨1191722, by rfl⟩ : syracuseStep 1588963 = 2383445) B2383445
theorem B6446897 : Blo 1411525 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B2383681 : Blo 1411525 2383681 := bstep (se 2 (by rfl) ⟨893880, by rfl⟩ : syracuseStep 2383681 = 1787761) B1787761
theorem B2383715 : Blo 1411525 2383715 := bstep (se 1 (by rfl) ⟨1787786, by rfl⟩ : syracuseStep 2383715 = 3575573) B3575573
theorem B1589107 : Blo 1411525 1589107 := bstep (se 1 (by rfl) ⟨1191830, by rfl⟩ : syracuseStep 1589107 = 2383661) B2383661
theorem B3178385 : Blo 1411525 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B3178403 : Blo 1411525 3178403 := bstep (se 1 (by rfl) ⟨2383802, by rfl⟩ : syracuseStep 3178403 = 4767605) B4767605
theorem B16089029 : Blo 1411525 16089029 := bstep (se 4 (by rfl) ⟨1508346, by rfl⟩ : syracuseStep 16089029 = 3016693) B3016693
theorem B3817421 : Blo 1411525 3817421 := bstep (se 3 (by rfl) ⟨715766, by rfl⟩ : syracuseStep 3817421 = 1431533) B1431533
theorem B2383843 : Blo 1411525 2383843 := bstep (se 1 (by rfl) ⟨1787882, by rfl⟩ : syracuseStep 2383843 = 3575765) B3575765
theorem B4079587 : Blo 1411525 4079587 := bstep (se 1 (by rfl) ⟨3059690, by rfl⟩ : syracuseStep 4079587 = 6119381) B6119381
theorem B1507339 : Blo 1411525 1507339 := bstep (se 1 (by rfl) ⟨1130504, by rfl⟩ : syracuseStep 1507339 = 2261009) B2261009
theorem B4767767 : Blo 1411525 4767767 := bstep (se 1 (by rfl) ⟨3575825, by rfl⟩ : syracuseStep 4767767 = 7151651) B7151651
theorem B2383897 : Blo 1411525 2383897 := bstep (se 2 (by rfl) ⟨893961, by rfl⟩ : syracuseStep 2383897 = 1787923) B1787923
theorem B3178547 : Blo 1411525 3178547 := bstep (se 1 (by rfl) ⟨2383910, by rfl⟩ : syracuseStep 3178547 = 4767821) B4767821
theorem B6619211 : Blo 1411525 6619211 := bstep (se 1 (by rfl) ⟨4964408, by rfl⟩ : syracuseStep 6619211 = 9928817) B9928817
theorem B1589323 : Blo 1411525 1589323 := bstep (se 1 (by rfl) ⟨1191992, by rfl⟩ : syracuseStep 1589323 = 2383985) B2383985
theorem B9052235 : Blo 1411525 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B5365835 : Blo 1411525 5365835 := bstep (se 1 (by rfl) ⟨4024376, by rfl⟩ : syracuseStep 5365835 = 8048753) B8048753
theorem B3178583 : Blo 1411525 3178583 := bstep (se 1 (by rfl) ⟨2383937, by rfl⟩ : syracuseStep 3178583 = 4767875) B4767875
theorem B6029491 : Blo 1411525 6029491 := bstep (se 1 (by rfl) ⟨4522118, by rfl⟩ : syracuseStep 6029491 = 9044237) B9044237
theorem B1589431 : Blo 1411525 1589431 := bstep (se 1 (by rfl) ⟨1192073, by rfl⟩ : syracuseStep 1589431 = 2384147) B2384147
theorem B10723589 : Blo 1411525 10723589 := bstep (se 4 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 10723589 = 2010673) B2010673
theorem B3178763 : Blo 1411525 3178763 := bstep (se 1 (by rfl) ⟨2384072, by rfl⟩ : syracuseStep 3178763 = 4768145) B4768145
theorem B12230929 : Blo 1411525 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B5366033 : Blo 1411525 5366033 := bstep (se 2 (by rfl) ⟨2012262, by rfl⟩ : syracuseStep 5366033 = 4024525) B4024525
theorem B3014977 : Blo 1411525 3014977 := bstep (se 2 (by rfl) ⟨1130616, by rfl⟩ : syracuseStep 3014977 = 2261233) B2261233
theorem B3178817 : Blo 1411525 3178817 := bstep (se 2 (by rfl) ⟨1192056, by rfl⟩ : syracuseStep 3178817 = 2384113) B2384113
theorem B10731851 : Blo 1411525 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B1589611 : Blo 1411525 1589611 := bstep (se 1 (by rfl) ⟨1192208, by rfl⟩ : syracuseStep 1589611 = 2384417) B2384417
theorem B9666947 : Blo 1411525 9666947 := bstep (se 1 (by rfl) ⟨7250210, by rfl⟩ : syracuseStep 9666947 = 14500421) B14500421
theorem B1589719 : Blo 1411525 1589719 := bstep (se 1 (by rfl) ⟨1192289, by rfl⟩ : syracuseStep 1589719 = 2384579) B2384579
theorem B5161475 : Blo 1411525 5161475 := bstep (se 1 (by rfl) ⟨3871106, by rfl⟩ : syracuseStep 5161475 = 7742213) B7742213
theorem B3179033 : Blo 1411525 3179033 := bstep (se 2 (by rfl) ⟨1192137, by rfl⟩ : syracuseStep 3179033 = 2384275) B2384275
theorem B4768307 : Blo 1411525 4768307 := bstep (se 1 (by rfl) ⟨3576230, by rfl⟩ : syracuseStep 4768307 = 7152461) B7152461
theorem B2384471 : Blo 1411525 2384471 := bstep (se 1 (by rfl) ⟨1788353, by rfl⟩ : syracuseStep 2384471 = 3576707) B3576707
theorem B3179123 : Blo 1411525 3179123 := bstep (se 1 (by rfl) ⟨2384342, by rfl⟩ : syracuseStep 3179123 = 4768685) B4768685
theorem B1589899 : Blo 1411525 1589899 := bstep (se 1 (by rfl) ⟨1192424, by rfl⟩ : syracuseStep 1589899 = 2384849) B2384849
theorem B3015319 : Blo 1411525 3015319 := bstep (se 1 (by rfl) ⟨2261489, by rfl⟩ : syracuseStep 3015319 = 4522979) B4522979
theorem B2941591 : Blo 1411525 2941591 := bstep (se 1 (by rfl) ⟨2206193, by rfl⟩ : syracuseStep 2941591 = 4412387) B4412387
theorem B3179159 : Blo 1411525 3179159 := bstep (se 1 (by rfl) ⟨2384369, by rfl⟩ : syracuseStep 3179159 = 4768739) B4768739
theorem B27509453 : Blo 1411525 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B2384599 : Blo 1411525 2384599 := bstep (se 1 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 2384599 = 3576899) B3576899
theorem B1590007 : Blo 1411525 1590007 := bstep (se 1 (by rfl) ⟨1192505, by rfl⟩ : syracuseStep 1590007 = 2385011) B2385011
theorem B11453201 : Blo 1411525 11453201 := bstep (se 2 (by rfl) ⟨4294950, by rfl⟩ : syracuseStep 11453201 = 8589901) B8589901
theorem B4768577 : Blo 1411525 4768577 := bstep (se 2 (by rfl) ⟨1788216, by rfl⟩ : syracuseStep 4768577 = 3576433) B3576433
theorem B3179339 : Blo 1411525 3179339 := bstep (se 1 (by rfl) ⟨2384504, by rfl⟩ : syracuseStep 3179339 = 4769009) B4769009
theorem B8045405 : Blo 1411525 8045405 := bstep (se 3 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 8045405 = 3017027) B3017027
theorem B3179393 : Blo 1411525 3179393 := bstep (se 2 (by rfl) ⟨1192272, by rfl⟩ : syracuseStep 3179393 = 2384545) B2384545
theorem B1590187 : Blo 1411525 1590187 := bstep (se 1 (by rfl) ⟨1192640, by rfl⟩ : syracuseStep 1590187 = 2385281) B2385281
theorem B27165617 : Blo 1411525 27165617 := bstep (se 2 (by rfl) ⟨10187106, by rfl⟩ : syracuseStep 27165617 = 20374213) B20374213
theorem B5366807 : Blo 1411525 5366807 := bstep (se 1 (by rfl) ⟨4025105, by rfl⟩ : syracuseStep 5366807 = 8050211) B8050211
theorem B2679895 : Blo 1411525 2679895 := bstep (se 1 (by rfl) ⟨2009921, by rfl⟩ : syracuseStep 2679895 = 4019843) B4019843
theorem B3179609 : Blo 1411525 3179609 := bstep (se 2 (by rfl) ⟨1192353, by rfl⟩ : syracuseStep 3179609 = 2384707) B2384707
theorem B51553421 : Blo 1411525 51553421 := bstep (se 3 (by rfl) ⟨9666266, by rfl⟩ : syracuseStep 51553421 = 19332533) B19332533
theorem B3179699 : Blo 1411525 3179699 := bstep (se 1 (by rfl) ⟨2384774, by rfl⟩ : syracuseStep 3179699 = 4769549) B4769549
theorem B3179735 : Blo 1411525 3179735 := bstep (se 1 (by rfl) ⟨2384801, by rfl⟩ : syracuseStep 3179735 = 4769603) B4769603
theorem B1508663 : Blo 1411525 1508663 := bstep (se 1 (by rfl) ⟨1131497, by rfl⟩ : syracuseStep 1508663 = 2262995) B2262995
theorem B2385227 : Blo 1411525 2385227 := bstep (se 1 (by rfl) ⟨1788920, by rfl⟩ : syracuseStep 2385227 = 3577841) B3577841
theorem B9045341 : Blo 1411525 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B4769117 : Blo 1411525 4769117 := bstep (se 3 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 4769117 = 1788419) B1788419
theorem B1787275 : Blo 1411525 1787275 := bstep (se 1 (by rfl) ⟨1340456, by rfl⟩ : syracuseStep 1787275 = 2680913) B2680913
theorem B3179915 : Blo 1411525 3179915 := bstep (se 1 (by rfl) ⟨2384936, by rfl⟩ : syracuseStep 3179915 = 4769873) B4769873
theorem B3573143 : Blo 1411525 3573143 := bstep (se 1 (by rfl) ⟨2679857, by rfl⟩ : syracuseStep 3573143 = 5359715) B5359715
theorem B1508791 : Blo 1411525 1508791 := bstep (se 1 (by rfl) ⟨1131593, by rfl⟩ : syracuseStep 1508791 = 2263187) B2263187
theorem B3179969 : Blo 1411525 3179969 := bstep (se 2 (by rfl) ⟨1192488, by rfl⟩ : syracuseStep 3179969 = 2384977) B2384977
theorem B1451467 : Blo 1411525 1451467 := bstep (se 1 (by rfl) ⟨1088600, by rfl⟩ : syracuseStep 1451467 = 2177201) B2177201
theorem B3221003 : Blo 1411525 3221003 := bstep (se 1 (by rfl) ⟨2415752, by rfl⟩ : syracuseStep 3221003 = 4831505) B4831505
theorem B9045569 : Blo 1411525 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B8046155 : Blo 1411525 8046155 := bstep (se 1 (by rfl) ⟨6034616, by rfl⟩ : syracuseStep 8046155 = 12069233) B12069233
theorem B40699523 : Blo 1411525 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B3180185 : Blo 1411525 3180185 := bstep (se 2 (by rfl) ⟨1192569, by rfl⟩ : syracuseStep 3180185 = 2385139) B2385139
theorem B7636697 : Blo 1411525 7636697 := bstep (se 2 (by rfl) ⟨2863761, by rfl⟩ : syracuseStep 7636697 = 5727523) B5727523
theorem B3180275 : Blo 1411525 3180275 := bstep (se 1 (by rfl) ⟨2385206, by rfl⟩ : syracuseStep 3180275 = 4770413) B4770413
theorem B3180311 : Blo 1411525 3180311 := bstep (se 1 (by rfl) ⟨2385233, by rfl⟩ : syracuseStep 3180311 = 4770467) B4770467
theorem B4294475 : Blo 1411525 4294475 := bstep (se 1 (by rfl) ⟨3220856, by rfl⟩ : syracuseStep 4294475 = 6441713) B6441713
theorem B3016523 : Blo 1411525 3016523 := bstep (se 1 (by rfl) ⟨2262392, by rfl⟩ : syracuseStep 3016523 = 4524785) B4524785
theorem B2680715 : Blo 1411525 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B2680769 : Blo 1411525 2680769 := bstep (se 2 (by rfl) ⟨1005288, by rfl⟩ : syracuseStep 2680769 = 2010577) B2010577
theorem B6784985 : Blo 1411525 6784985 := bstep (se 2 (by rfl) ⟨2544369, by rfl⟩ : syracuseStep 6784985 = 5088739) B5088739
theorem B1632235 : Blo 1411525 1632235 := bstep (se 1 (by rfl) ⟨1224176, by rfl⟩ : syracuseStep 1632235 = 2448353) B2448353
theorem B1509355 : Blo 1411525 1509355 := bstep (se 1 (by rfl) ⟨1132016, by rfl⟩ : syracuseStep 1509355 = 2264033) B2264033
theorem B4024343 : Blo 1411525 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B4294721 : Blo 1411525 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B7153757 : Blo 1411525 7153757 := bstep (se 3 (by rfl) ⟨1341329, by rfl⟩ : syracuseStep 7153757 = 2682659) B2682659
theorem B3573953 : Blo 1411525 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B4524311 : Blo 1411525 4524311 := bstep (se 1 (by rfl) ⟨3393233, by rfl⟩ : syracuseStep 4524311 = 6786467) B6786467
theorem B3393857 : Blo 1411525 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B3017035 : Blo 1411525 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B1788247 : Blo 1411525 1788247 := bstep (se 1 (by rfl) ⟨1341185, by rfl⟩ : syracuseStep 1788247 = 2682371) B2682371
theorem B5360003 : Blo 1411525 5360003 := bstep (se 1 (by rfl) ⟨4020002, by rfl⟩ : syracuseStep 5360003 = 8040005) B8040005
theorem B1411531 : Blo 1411525 1411531 := bstep (se 1 (by rfl) ⟨1058648, by rfl⟩ : syracuseStep 1411531 = 2117297) B2117297
theorem B4770251 : Blo 1411525 4770251 := bstep (se 1 (by rfl) ⟨3577688, by rfl⟩ : syracuseStep 4770251 = 7155377) B7155377
theorem B1411543 : Blo 1411525 1411543 := bstep (se 1 (by rfl) ⟨1058657, by rfl⟩ : syracuseStep 1411543 = 2117315) B2117315
theorem B1411563 : Blo 1411525 1411563 := bstep (se 1 (by rfl) ⟨1058672, by rfl⟩ : syracuseStep 1411563 = 2117345) B2117345
theorem B1411575 : Blo 1411525 1411575 := bstep (se 1 (by rfl) ⟨1058681, by rfl⟩ : syracuseStep 1411575 = 2117363) B2117363
theorem B1411595 : Blo 1411525 1411595 := bstep (se 1 (by rfl) ⟨1058696, by rfl⟩ : syracuseStep 1411595 = 2117393) B2117393
theorem B1411607 : Blo 1411525 1411607 := bstep (se 1 (by rfl) ⟨1058705, by rfl⟩ : syracuseStep 1411607 = 2117411) B2117411
theorem B1411627 : Blo 1411525 1411627 := bstep (se 1 (by rfl) ⟨1058720, by rfl⟩ : syracuseStep 1411627 = 2117441) B2117441
theorem B1411639 : Blo 1411525 1411639 := bstep (se 1 (by rfl) ⟨1058729, by rfl⟩ : syracuseStep 1411639 = 2117459) B2117459
theorem B3312193 : Blo 1411525 3312193 := bstep (se 2 (by rfl) ⟨1242072, by rfl⟩ : syracuseStep 3312193 = 2484145) B2484145
theorem B1411659 : Blo 1411525 1411659 := bstep (se 1 (by rfl) ⟨1058744, by rfl⟩ : syracuseStep 1411659 = 2117489) B2117489
theorem B4524619 : Blo 1411525 4524619 := bstep (se 1 (by rfl) ⟨3393464, by rfl⟩ : syracuseStep 4524619 = 6786929) B6786929
theorem B1411671 : Blo 1411525 1411671 := bstep (se 1 (by rfl) ⟨1058753, by rfl⟩ : syracuseStep 1411671 = 2117507) B2117507
theorem B1411691 : Blo 1411525 1411691 := bstep (se 1 (by rfl) ⟨1058768, by rfl⟩ : syracuseStep 1411691 = 2117537) B2117537
theorem B1411703 : Blo 1411525 1411703 := bstep (se 1 (by rfl) ⟨1058777, by rfl⟩ : syracuseStep 1411703 = 2117555) B2117555
theorem B10726019 : Blo 1411525 10726019 := bstep (se 1 (by rfl) ⟨8044514, by rfl⟩ : syracuseStep 10726019 = 16089029) B16089029
theorem B1411723 : Blo 1411525 1411723 := bstep (se 1 (by rfl) ⟨1058792, by rfl⟩ : syracuseStep 1411723 = 2117585) B2117585
theorem B1411735 : Blo 1411525 1411735 := bstep (se 1 (by rfl) ⟨1058801, by rfl⟩ : syracuseStep 1411735 = 2117603) B2117603
theorem B1411755 : Blo 1411525 1411755 := bstep (se 1 (by rfl) ⟨1058816, by rfl⟩ : syracuseStep 1411755 = 2117633) B2117633
theorem B9054899 : Blo 1411525 9054899 := bstep (se 1 (by rfl) ⟨6791174, by rfl⟩ : syracuseStep 9054899 = 13582349) B13582349
theorem B1411767 : Blo 1411525 1411767 := bstep (se 1 (by rfl) ⟨1058825, by rfl⟩ : syracuseStep 1411767 = 2117651) B2117651
theorem B1411787 : Blo 1411525 1411787 := bstep (se 1 (by rfl) ⟨1058840, by rfl⟩ : syracuseStep 1411787 = 2117681) B2117681
theorem B1411799 : Blo 1411525 1411799 := bstep (se 1 (by rfl) ⟨1058849, by rfl⟩ : syracuseStep 1411799 = 2117699) B2117699
theorem B3574489 : Blo 1411525 3574489 := bstep (se 2 (by rfl) ⟨1340433, by rfl⟩ : syracuseStep 3574489 = 2680867) B2680867
theorem B4770521 : Blo 1411525 4770521 := bstep (se 2 (by rfl) ⟨1788945, by rfl⟩ : syracuseStep 4770521 = 3577891) B3577891
theorem B1411819 : Blo 1411525 1411819 := bstep (se 1 (by rfl) ⟨1058864, by rfl⟩ : syracuseStep 1411819 = 2117729) B2117729
theorem B1411831 : Blo 1411525 1411831 := bstep (se 1 (by rfl) ⟨1058873, by rfl⟩ : syracuseStep 1411831 = 2117747) B2117747
theorem B23538437 : Blo 1411525 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B1411851 : Blo 1411525 1411851 := bstep (se 1 (by rfl) ⟨1058888, by rfl⟩ : syracuseStep 1411851 = 2117777) B2117777
theorem B1411863 : Blo 1411525 1411863 := bstep (se 1 (by rfl) ⟨1058897, by rfl⟩ : syracuseStep 1411863 = 2117795) B2117795
theorem B1411883 : Blo 1411525 1411883 := bstep (se 1 (by rfl) ⟨1058912, by rfl⟩ : syracuseStep 1411883 = 2117825) B2117825
theorem B1411895 : Blo 1411525 1411895 := bstep (se 1 (by rfl) ⟨1058921, by rfl⟩ : syracuseStep 1411895 = 2117843) B2117843
theorem B7146305 : Blo 1411525 7146305 := bstep (se 2 (by rfl) ⟨2679864, by rfl⟩ : syracuseStep 7146305 = 5359729) B5359729
theorem B1411915 : Blo 1411525 1411915 := bstep (se 1 (by rfl) ⟨1058936, by rfl⟩ : syracuseStep 1411915 = 2117873) B2117873
theorem B1411927 : Blo 1411525 1411927 := bstep (se 1 (by rfl) ⟨1058945, by rfl⟩ : syracuseStep 1411927 = 2117891) B2117891
theorem B2681687 : Blo 1411525 2681687 := bstep (se 1 (by rfl) ⟨2011265, by rfl⟩ : syracuseStep 2681687 = 4022531) B4022531
theorem B1411947 : Blo 1411525 1411947 := bstep (se 1 (by rfl) ⟨1058960, by rfl⟩ : syracuseStep 1411947 = 2117921) B2117921
theorem B1411959 : Blo 1411525 1411959 := bstep (se 1 (by rfl) ⟨1058969, by rfl⟩ : syracuseStep 1411959 = 2117939) B2117939
theorem B1411979 : Blo 1411525 1411979 := bstep (se 1 (by rfl) ⟨1058984, by rfl⟩ : syracuseStep 1411979 = 2117969) B2117969
theorem B1411991 : Blo 1411525 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B1412011 : Blo 1411525 1412011 := bstep (se 1 (by rfl) ⟨1059008, by rfl⟩ : syracuseStep 1412011 = 2118017) B2118017
theorem B1412023 : Blo 1411525 1412023 := bstep (se 1 (by rfl) ⟨1059017, by rfl⟩ : syracuseStep 1412023 = 2118035) B2118035
theorem B1412043 : Blo 1411525 1412043 := bstep (se 1 (by rfl) ⟨1059032, by rfl⟩ : syracuseStep 1412043 = 2118065) B2118065
theorem B1412055 : Blo 1411525 1412055 := bstep (se 1 (by rfl) ⟨1059041, by rfl⟩ : syracuseStep 1412055 = 2118083) B2118083
theorem B1412075 : Blo 1411525 1412075 := bstep (se 1 (by rfl) ⟨1059056, by rfl⟩ : syracuseStep 1412075 = 2118113) B2118113
theorem B1412087 : Blo 1411525 1412087 := bstep (se 1 (by rfl) ⟨1059065, by rfl⟩ : syracuseStep 1412087 = 2118131) B2118131
theorem B1412107 : Blo 1411525 1412107 := bstep (se 1 (by rfl) ⟨1059080, by rfl⟩ : syracuseStep 1412107 = 2118161) B2118161
theorem B1412119 : Blo 1411525 1412119 := bstep (se 1 (by rfl) ⟨1059089, by rfl⟩ : syracuseStep 1412119 = 2118179) B2118179
theorem B3017753 : Blo 1411525 3017753 := bstep (se 2 (by rfl) ⟨1131657, by rfl⟩ : syracuseStep 3017753 = 2263315) B2263315
theorem B1412139 : Blo 1411525 1412139 := bstep (se 1 (by rfl) ⟨1059104, by rfl⟩ : syracuseStep 1412139 = 2118209) B2118209
theorem B1412151 : Blo 1411525 1412151 := bstep (se 1 (by rfl) ⟨1059113, by rfl⟩ : syracuseStep 1412151 = 2118227) B2118227
theorem B1412171 : Blo 1411525 1412171 := bstep (se 1 (by rfl) ⟨1059128, by rfl⟩ : syracuseStep 1412171 = 2118257) B2118257
theorem B1412183 : Blo 1411525 1412183 := bstep (se 1 (by rfl) ⟨1059137, by rfl⟩ : syracuseStep 1412183 = 2118275) B2118275
theorem B1412203 : Blo 1411525 1412203 := bstep (se 1 (by rfl) ⟨1059152, by rfl⟩ : syracuseStep 1412203 = 2118305) B2118305
theorem B1412215 : Blo 1411525 1412215 := bstep (se 1 (by rfl) ⟨1059161, by rfl⟩ : syracuseStep 1412215 = 2118323) B2118323
theorem B1412235 : Blo 1411525 1412235 := bstep (se 1 (by rfl) ⟨1059176, by rfl⟩ : syracuseStep 1412235 = 2118353) B2118353
theorem B2010263 : Blo 1411525 2010263 := bstep (se 1 (by rfl) ⟨1507697, by rfl⟩ : syracuseStep 2010263 = 3015395) B3015395
theorem B1412247 : Blo 1411525 1412247 := bstep (se 1 (by rfl) ⟨1059185, by rfl⟩ : syracuseStep 1412247 = 2118371) B2118371
theorem B1412267 : Blo 1411525 1412267 := bstep (se 1 (by rfl) ⟨1059200, by rfl⟩ : syracuseStep 1412267 = 2118401) B2118401
theorem B8047795 : Blo 1411525 8047795 := bstep (se 1 (by rfl) ⟨6035846, by rfl⟩ : syracuseStep 8047795 = 12071693) B12071693
theorem B1412279 : Blo 1411525 1412279 := bstep (se 1 (by rfl) ⟨1059209, by rfl⟩ : syracuseStep 1412279 = 2118419) B2118419
theorem B1412299 : Blo 1411525 1412299 := bstep (se 1 (by rfl) ⟨1059224, by rfl⟩ : syracuseStep 1412299 = 2118449) B2118449
theorem B1412311 : Blo 1411525 1412311 := bstep (se 1 (by rfl) ⟨1059233, by rfl⟩ : syracuseStep 1412311 = 2118467) B2118467
theorem B1412331 : Blo 1411525 1412331 := bstep (se 1 (by rfl) ⟨1059248, by rfl⟩ : syracuseStep 1412331 = 2118497) B2118497
theorem B1412343 : Blo 1411525 1412343 := bstep (se 1 (by rfl) ⟨1059257, by rfl⟩ : syracuseStep 1412343 = 2118515) B2118515
theorem B1412363 : Blo 1411525 1412363 := bstep (se 1 (by rfl) ⟨1059272, by rfl⟩ : syracuseStep 1412363 = 2118545) B2118545
theorem B1412375 : Blo 1411525 1412375 := bstep (se 1 (by rfl) ⟨1059281, by rfl⟩ : syracuseStep 1412375 = 2118563) B2118563
theorem B1412395 : Blo 1411525 1412395 := bstep (se 1 (by rfl) ⟨1059296, by rfl⟩ : syracuseStep 1412395 = 2118593) B2118593
theorem B4295987 : Blo 1411525 4295987 := bstep (se 1 (by rfl) ⟨3221990, by rfl⟩ : syracuseStep 4295987 = 6443981) B6443981
theorem B1412407 : Blo 1411525 1412407 := bstep (se 1 (by rfl) ⟨1059305, by rfl⟩ : syracuseStep 1412407 = 2118611) B2118611
theorem B1412427 : Blo 1411525 1412427 := bstep (se 1 (by rfl) ⟨1059320, by rfl⟩ : syracuseStep 1412427 = 2118641) B2118641
theorem B1412439 : Blo 1411525 1412439 := bstep (se 1 (by rfl) ⟨1059329, by rfl⟩ : syracuseStep 1412439 = 2118659) B2118659
theorem B2010457 : Blo 1411525 2010457 := bstep (se 2 (by rfl) ⟨753921, by rfl⟩ : syracuseStep 2010457 = 1507843) B1507843
theorem B1412459 : Blo 1411525 1412459 := bstep (se 1 (by rfl) ⟨1059344, by rfl⟩ : syracuseStep 1412459 = 2118689) B2118689
theorem B2682227 : Blo 1411525 2682227 := bstep (se 1 (by rfl) ⟨2011670, by rfl⟩ : syracuseStep 2682227 = 4023341) B4023341
theorem B1412471 : Blo 1411525 1412471 := bstep (se 1 (by rfl) ⟨1059353, by rfl⟩ : syracuseStep 1412471 = 2118707) B2118707
theorem B1412491 : Blo 1411525 1412491 := bstep (se 1 (by rfl) ⟨1059368, by rfl⟩ : syracuseStep 1412491 = 2118737) B2118737
theorem B1412503 : Blo 1411525 1412503 := bstep (se 1 (by rfl) ⟨1059377, by rfl⟩ : syracuseStep 1412503 = 2118755) B2118755
theorem B12070295 : Blo 1411525 12070295 := bstep (se 1 (by rfl) ⟨9052721, by rfl⟩ : syracuseStep 12070295 = 18105443) B18105443
theorem B1412523 : Blo 1411525 1412523 := bstep (se 1 (by rfl) ⟨1059392, by rfl⟩ : syracuseStep 1412523 = 2118785) B2118785
theorem B3018163 : Blo 1411525 3018163 := bstep (se 1 (by rfl) ⟨2263622, by rfl⟩ : syracuseStep 3018163 = 4527245) B4527245
theorem B1412535 : Blo 1411525 1412535 := bstep (se 1 (by rfl) ⟨1059401, by rfl⟩ : syracuseStep 1412535 = 2118803) B2118803
theorem B1412555 : Blo 1411525 1412555 := bstep (se 1 (by rfl) ⟨1059416, by rfl⟩ : syracuseStep 1412555 = 2118833) B2118833
theorem B1412567 : Blo 1411525 1412567 := bstep (se 1 (by rfl) ⟨1059425, by rfl⟩ : syracuseStep 1412567 = 2118851) B2118851
theorem B1412587 : Blo 1411525 1412587 := bstep (se 1 (by rfl) ⟨1059440, by rfl⟩ : syracuseStep 1412587 = 2118881) B2118881
theorem B1412599 : Blo 1411525 1412599 := bstep (se 1 (by rfl) ⟨1059449, by rfl⟩ : syracuseStep 1412599 = 2118899) B2118899
theorem B1412619 : Blo 1411525 1412619 := bstep (se 1 (by rfl) ⟨1059464, by rfl⟩ : syracuseStep 1412619 = 2118929) B2118929
theorem B1412631 : Blo 1411525 1412631 := bstep (se 1 (by rfl) ⟨1059473, by rfl⟩ : syracuseStep 1412631 = 2118947) B2118947
theorem B1412651 : Blo 1411525 1412651 := bstep (se 1 (by rfl) ⟨1059488, by rfl⟩ : syracuseStep 1412651 = 2118977) B2118977
theorem B1412663 : Blo 1411525 1412663 := bstep (se 1 (by rfl) ⟨1059497, by rfl⟩ : syracuseStep 1412663 = 2118995) B2118995
theorem B1412683 : Blo 1411525 1412683 := bstep (se 1 (by rfl) ⟨1059512, by rfl⟩ : syracuseStep 1412683 = 2119025) B2119025
theorem B1412695 : Blo 1411525 1412695 := bstep (se 1 (by rfl) ⟨1059521, by rfl⟩ : syracuseStep 1412695 = 2119043) B2119043
theorem B1412715 : Blo 1411525 1412715 := bstep (se 1 (by rfl) ⟨1059536, by rfl⟩ : syracuseStep 1412715 = 2119073) B2119073
theorem B1412727 : Blo 1411525 1412727 := bstep (se 1 (by rfl) ⟨1059545, by rfl⟩ : syracuseStep 1412727 = 2119091) B2119091
theorem B1412747 : Blo 1411525 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B1412759 : Blo 1411525 1412759 := bstep (se 1 (by rfl) ⟨1059569, by rfl⟩ : syracuseStep 1412759 = 2119139) B2119139
theorem B1412779 : Blo 1411525 1412779 := bstep (se 1 (by rfl) ⟨1059584, by rfl⟩ : syracuseStep 1412779 = 2119169) B2119169
theorem B1412791 : Blo 1411525 1412791 := bstep (se 1 (by rfl) ⟨1059593, by rfl⟩ : syracuseStep 1412791 = 2119187) B2119187
theorem B1412811 : Blo 1411525 1412811 := bstep (se 1 (by rfl) ⟨1059608, by rfl⟩ : syracuseStep 1412811 = 2119217) B2119217
theorem B1412823 : Blo 1411525 1412823 := bstep (se 1 (by rfl) ⟨1059617, by rfl⟩ : syracuseStep 1412823 = 2119235) B2119235
theorem B6033113 : Blo 1411525 6033113 := bstep (se 2 (by rfl) ⟨2262417, by rfl⟩ : syracuseStep 6033113 = 4524835) B4524835
theorem B1412843 : Blo 1411525 1412843 := bstep (se 1 (by rfl) ⟨1059632, by rfl⟩ : syracuseStep 1412843 = 2119265) B2119265
theorem B1412855 : Blo 1411525 1412855 := bstep (se 1 (by rfl) ⟨1059641, by rfl⟩ : syracuseStep 1412855 = 2119283) B2119283
theorem B2117387 : Blo 1411525 2117387 := bstep (se 1 (by rfl) ⟨1588040, by rfl⟩ : syracuseStep 2117387 = 3176081) B3176081
theorem B1412875 : Blo 1411525 1412875 := bstep (se 1 (by rfl) ⟨1059656, by rfl⟩ : syracuseStep 1412875 = 2119313) B2119313
theorem B9047825 : Blo 1411525 9047825 := bstep (se 2 (by rfl) ⟨3392934, by rfl⟩ : syracuseStep 9047825 = 6785869) B6785869
theorem B2117399 : Blo 1411525 2117399 := bstep (se 1 (by rfl) ⟨1588049, by rfl⟩ : syracuseStep 2117399 = 3176099) B3176099
theorem B1412887 : Blo 1411525 1412887 := bstep (se 1 (by rfl) ⟨1059665, by rfl⟩ : syracuseStep 1412887 = 2119331) B2119331
theorem B1412907 : Blo 1411525 1412907 := bstep (se 1 (by rfl) ⟨1059680, by rfl⟩ : syracuseStep 1412907 = 2119361) B2119361
theorem B3575603 : Blo 1411525 3575603 := bstep (se 1 (by rfl) ⟨2681702, by rfl⟩ : syracuseStep 3575603 = 5363405) B5363405
theorem B1412919 : Blo 1411525 1412919 := bstep (se 1 (by rfl) ⟨1059689, by rfl⟩ : syracuseStep 1412919 = 2119379) B2119379
theorem B1412939 : Blo 1411525 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B1412951 : Blo 1411525 1412951 := bstep (se 1 (by rfl) ⟨1059713, by rfl⟩ : syracuseStep 1412951 = 2119427) B2119427
theorem B4829017 : Blo 1411525 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B2117465 : Blo 1411525 2117465 := bstep (se 2 (by rfl) ⟨794049, by rfl⟩ : syracuseStep 2117465 = 1588099) B1588099
theorem B2682713 : Blo 1411525 2682713 := bstep (se 2 (by rfl) ⟨1006017, by rfl⟩ : syracuseStep 2682713 = 2012035) B2012035
theorem B9301853 : Blo 1411525 9301853 := bstep (se 3 (by rfl) ⟨1744097, by rfl⟩ : syracuseStep 9301853 = 3488195) B3488195
theorem B1412971 : Blo 1411525 1412971 := bstep (se 1 (by rfl) ⟨1059728, by rfl⟩ : syracuseStep 1412971 = 2119457) B2119457
theorem B1412983 : Blo 1411525 1412983 := bstep (se 1 (by rfl) ⟨1059737, by rfl⟩ : syracuseStep 1412983 = 2119475) B2119475
theorem B8040323 : Blo 1411525 8040323 := bstep (se 1 (by rfl) ⟨6030242, by rfl⟩ : syracuseStep 8040323 = 12060485) B12060485
theorem B1413003 : Blo 1411525 1413003 := bstep (se 1 (by rfl) ⟨1059752, by rfl⟩ : syracuseStep 1413003 = 2119505) B2119505
theorem B1413015 : Blo 1411525 1413015 := bstep (se 1 (by rfl) ⟨1059761, by rfl⟩ : syracuseStep 1413015 = 2119523) B2119523
theorem B1413035 : Blo 1411525 1413035 := bstep (se 1 (by rfl) ⟨1059776, by rfl⟩ : syracuseStep 1413035 = 2119553) B2119553
theorem B1413047 : Blo 1411525 1413047 := bstep (se 1 (by rfl) ⟨1059785, by rfl⟩ : syracuseStep 1413047 = 2119571) B2119571
theorem B2117579 : Blo 1411525 2117579 := bstep (se 1 (by rfl) ⟨1588184, by rfl⟩ : syracuseStep 2117579 = 3176369) B3176369
theorem B1413067 : Blo 1411525 1413067 := bstep (se 1 (by rfl) ⟨1059800, by rfl⟩ : syracuseStep 1413067 = 2119601) B2119601
theorem B2117591 : Blo 1411525 2117591 := bstep (se 1 (by rfl) ⟨1588193, by rfl⟩ : syracuseStep 2117591 = 3176387) B3176387
theorem B1413079 : Blo 1411525 1413079 := bstep (se 1 (by rfl) ⟨1059809, by rfl⟩ : syracuseStep 1413079 = 2119619) B2119619
theorem B1413099 : Blo 1411525 1413099 := bstep (se 1 (by rfl) ⟨1059824, by rfl⟩ : syracuseStep 1413099 = 2119649) B2119649
theorem B1413111 : Blo 1411525 1413111 := bstep (se 1 (by rfl) ⟨1059833, by rfl⟩ : syracuseStep 1413111 = 2119667) B2119667
theorem B1413131 : Blo 1411525 1413131 := bstep (se 1 (by rfl) ⟨1059848, by rfl⟩ : syracuseStep 1413131 = 2119697) B2119697
theorem B1413143 : Blo 1411525 1413143 := bstep (se 1 (by rfl) ⟨1059857, by rfl⟩ : syracuseStep 1413143 = 2119715) B2119715
theorem B2117657 : Blo 1411525 2117657 := bstep (se 2 (by rfl) ⟨794121, by rfl⟩ : syracuseStep 2117657 = 1588243) B1588243
theorem B1413163 : Blo 1411525 1413163 := bstep (se 1 (by rfl) ⟨1059872, by rfl⟩ : syracuseStep 1413163 = 2119745) B2119745
theorem B1413175 : Blo 1411525 1413175 := bstep (se 1 (by rfl) ⟨1059881, by rfl⟩ : syracuseStep 1413175 = 2119763) B2119763
theorem B1413195 : Blo 1411525 1413195 := bstep (se 1 (by rfl) ⟨1059896, by rfl⟩ : syracuseStep 1413195 = 2119793) B2119793
theorem B1413207 : Blo 1411525 1413207 := bstep (se 1 (by rfl) ⟨1059905, by rfl⟩ : syracuseStep 1413207 = 2119811) B2119811
theorem B3575897 : Blo 1411525 3575897 := bstep (se 2 (by rfl) ⟨1340961, by rfl⟩ : syracuseStep 3575897 = 2681923) B2681923
theorem B1413227 : Blo 1411525 1413227 := bstep (se 1 (by rfl) ⟨1059920, by rfl⟩ : syracuseStep 1413227 = 2119841) B2119841
theorem B1413239 : Blo 1411525 1413239 := bstep (se 1 (by rfl) ⟨1059929, by rfl⟩ : syracuseStep 1413239 = 2119859) B2119859
theorem B2117771 : Blo 1411525 2117771 := bstep (se 1 (by rfl) ⟨1588328, by rfl⟩ : syracuseStep 2117771 = 3176657) B3176657
theorem B1413259 : Blo 1411525 1413259 := bstep (se 1 (by rfl) ⟨1059944, by rfl⟩ : syracuseStep 1413259 = 2119889) B2119889
theorem B2117783 : Blo 1411525 2117783 := bstep (se 1 (by rfl) ⟨1588337, by rfl⟩ : syracuseStep 2117783 = 3176675) B3176675
theorem B13570199 : Blo 1411525 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B1413271 : Blo 1411525 1413271 := bstep (se 1 (by rfl) ⟨1059953, by rfl⟩ : syracuseStep 1413271 = 2119907) B2119907
theorem B7155863 : Blo 1411525 7155863 := bstep (se 1 (by rfl) ⟨5366897, by rfl⟩ : syracuseStep 7155863 = 10733795) B10733795
theorem B1413291 : Blo 1411525 1413291 := bstep (se 1 (by rfl) ⟨1059968, by rfl⟩ : syracuseStep 1413291 = 2119937) B2119937
theorem B1413303 : Blo 1411525 1413303 := bstep (se 1 (by rfl) ⟨1059977, by rfl⟩ : syracuseStep 1413303 = 2119955) B2119955
theorem B1413323 : Blo 1411525 1413323 := bstep (se 1 (by rfl) ⟨1059992, by rfl⟩ : syracuseStep 1413323 = 2119985) B2119985
theorem B1413335 : Blo 1411525 1413335 := bstep (se 1 (by rfl) ⟨1060001, by rfl⟩ : syracuseStep 1413335 = 2120003) B2120003
theorem B2117849 : Blo 1411525 2117849 := bstep (se 2 (by rfl) ⟨794193, by rfl⟩ : syracuseStep 2117849 = 1588387) B1588387
theorem B10178777 : Blo 1411525 10178777 := bstep (se 2 (by rfl) ⟨3817041, by rfl⟩ : syracuseStep 10178777 = 7634083) B7634083
theorem B1413355 : Blo 1411525 1413355 := bstep (se 1 (by rfl) ⟨1060016, by rfl⟩ : syracuseStep 1413355 = 2120033) B2120033
theorem B1413367 : Blo 1411525 1413367 := bstep (se 1 (by rfl) ⟨1060025, by rfl⟩ : syracuseStep 1413367 = 2120051) B2120051
theorem B1413387 : Blo 1411525 1413387 := bstep (se 1 (by rfl) ⟨1060040, by rfl⟩ : syracuseStep 1413387 = 2120081) B2120081
theorem B6115601 : Blo 1411525 6115601 := bstep (se 2 (by rfl) ⟨2293350, by rfl⟩ : syracuseStep 6115601 = 4586701) B4586701
theorem B1413399 : Blo 1411525 1413399 := bstep (se 1 (by rfl) ⟨1060049, by rfl⟩ : syracuseStep 1413399 = 2120099) B2120099
theorem B1413419 : Blo 1411525 1413419 := bstep (se 1 (by rfl) ⟨1060064, by rfl⟩ : syracuseStep 1413419 = 2120129) B2120129
theorem B38670637 : Blo 1411525 38670637 := bstep (se 3 (by rfl) ⟨7250744, by rfl⟩ : syracuseStep 38670637 = 14501489) B14501489
theorem B2543923 : Blo 1411525 2543923 := bstep (se 1 (by rfl) ⟨1907942, by rfl⟩ : syracuseStep 2543923 = 3815885) B3815885
theorem B2756915 : Blo 1411525 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B1413431 : Blo 1411525 1413431 := bstep (se 1 (by rfl) ⟨1060073, by rfl⟩ : syracuseStep 1413431 = 2120147) B2120147
theorem B8040779 : Blo 1411525 8040779 := bstep (se 1 (by rfl) ⟨6030584, by rfl⟩ : syracuseStep 8040779 = 12061169) B12061169
theorem B2117963 : Blo 1411525 2117963 := bstep (se 1 (by rfl) ⟨1588472, by rfl⟩ : syracuseStep 2117963 = 3176945) B3176945
theorem B1413451 : Blo 1411525 1413451 := bstep (se 1 (by rfl) ⟨1060088, by rfl⟩ : syracuseStep 1413451 = 2120177) B2120177
theorem B2117975 : Blo 1411525 2117975 := bstep (se 1 (by rfl) ⟨1588481, by rfl⟩ : syracuseStep 2117975 = 3176963) B3176963
theorem B1413463 : Blo 1411525 1413463 := bstep (se 1 (by rfl) ⟨1060097, by rfl⟩ : syracuseStep 1413463 = 2120195) B2120195
theorem B1413483 : Blo 1411525 1413483 := bstep (se 1 (by rfl) ⟨1060112, by rfl⟩ : syracuseStep 1413483 = 2120225) B2120225
theorem B1413495 : Blo 1411525 1413495 := bstep (se 1 (by rfl) ⟨1060121, by rfl⟩ : syracuseStep 1413495 = 2120243) B2120243
theorem B1413515 : Blo 1411525 1413515 := bstep (se 1 (by rfl) ⟨1060136, by rfl⟩ : syracuseStep 1413515 = 2120273) B2120273
theorem B2118041 : Blo 1411525 2118041 := bstep (se 2 (by rfl) ⟨794265, by rfl⟩ : syracuseStep 2118041 = 1588531) B1588531
theorem B5157323 : Blo 1411525 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B2544139 : Blo 1411525 2544139 := bstep (se 1 (by rfl) ⟨1908104, by rfl⟩ : syracuseStep 2544139 = 3816209) B3816209
theorem B2118155 : Blo 1411525 2118155 := bstep (se 1 (by rfl) ⟨1588616, by rfl⟩ : syracuseStep 2118155 = 3177233) B3177233
theorem B2118167 : Blo 1411525 2118167 := bstep (se 1 (by rfl) ⟨1588625, by rfl⟩ : syracuseStep 2118167 = 3177251) B3177251
theorem B2863667 : Blo 1411525 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B2118233 : Blo 1411525 2118233 := bstep (se 2 (by rfl) ⟨794337, by rfl⟩ : syracuseStep 2118233 = 1588675) B1588675
theorem B8049253 : Blo 1411525 8049253 := bstep (se 4 (by rfl) ⟨754617, by rfl⟩ : syracuseStep 8049253 = 1509235) B1509235
theorem B4764311 : Blo 1411525 4764311 := bstep (se 1 (by rfl) ⟨3573233, by rfl⟩ : syracuseStep 4764311 = 7146467) B7146467
theorem B2118347 : Blo 1411525 2118347 := bstep (se 1 (by rfl) ⟨1588760, by rfl⟩ : syracuseStep 2118347 = 3177521) B3177521
theorem B2118359 : Blo 1411525 2118359 := bstep (se 1 (by rfl) ⟨1588769, by rfl⟩ : syracuseStep 2118359 = 3177539) B3177539
theorem B7148249 : Blo 1411525 7148249 := bstep (se 2 (by rfl) ⟨2680593, by rfl⟩ : syracuseStep 7148249 = 5361187) B5361187
theorem B2544385 : Blo 1411525 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B2011915 : Blo 1411525 2011915 := bstep (se 1 (by rfl) ⟨1508936, by rfl⟩ : syracuseStep 2011915 = 3017873) B3017873
theorem B2118425 : Blo 1411525 2118425 := bstep (se 2 (by rfl) ⟨794409, by rfl⟩ : syracuseStep 2118425 = 1588819) B1588819
theorem B2118539 : Blo 1411525 2118539 := bstep (se 1 (by rfl) ⟨1588904, by rfl⟩ : syracuseStep 2118539 = 3177809) B3177809
theorem B2118551 : Blo 1411525 2118551 := bstep (se 1 (by rfl) ⟨1588913, by rfl⟩ : syracuseStep 2118551 = 3177827) B3177827
theorem B2118617 : Blo 1411525 2118617 := bstep (se 2 (by rfl) ⟨794481, by rfl⟩ : syracuseStep 2118617 = 1588963) B1588963
theorem B2118731 : Blo 1411525 2118731 := bstep (se 1 (by rfl) ⟨1589048, by rfl⟩ : syracuseStep 2118731 = 3178097) B3178097
theorem B2118743 : Blo 1411525 2118743 := bstep (se 1 (by rfl) ⟨1589057, by rfl⟩ : syracuseStep 2118743 = 3178115) B3178115
theorem B4527193 : Blo 1411525 4527193 := bstep (se 2 (by rfl) ⟨1697697, by rfl⟩ : syracuseStep 4527193 = 3395395) B3395395
theorem B9172099 : Blo 1411525 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B2118809 : Blo 1411525 2118809 := bstep (se 2 (by rfl) ⟨794553, by rfl⟩ : syracuseStep 2118809 = 1589107) B1589107
theorem B4764851 : Blo 1411525 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B4297931 : Blo 1411525 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B24122609 : Blo 1411525 24122609 := bstep (se 2 (by rfl) ⟨9045978, by rfl⟩ : syracuseStep 24122609 = 18091957) B18091957
theorem B2716915 : Blo 1411525 2716915 := bstep (se 1 (by rfl) ⟨2037686, by rfl⟩ : syracuseStep 2716915 = 4075373) B4075373
theorem B2118923 : Blo 1411525 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B2118935 : Blo 1411525 2118935 := bstep (se 1 (by rfl) ⟨1589201, by rfl⟩ : syracuseStep 2118935 = 3178403) B3178403
theorem B2544947 : Blo 1411525 2544947 := bstep (se 1 (by rfl) ⟨1908710, by rfl⟩ : syracuseStep 2544947 = 3817421) B3817421
theorem B6034753 : Blo 1411525 6034753 := bstep (se 2 (by rfl) ⟨2263032, by rfl⟩ : syracuseStep 6034753 = 4526065) B4526065
theorem B2119001 : Blo 1411525 2119001 := bstep (se 2 (by rfl) ⟨794625, by rfl⟩ : syracuseStep 2119001 = 1589251) B1589251
theorem B5363117 : Blo 1411525 5363117 := bstep (se 3 (by rfl) ⟨1005584, by rfl⟩ : syracuseStep 5363117 = 2011169) B2011169
theorem B4765121 : Blo 1411525 4765121 := bstep (se 2 (by rfl) ⟨1786920, by rfl⟩ : syracuseStep 4765121 = 3573841) B3573841
theorem B2119115 : Blo 1411525 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B2119127 : Blo 1411525 2119127 := bstep (se 1 (by rfl) ⟨1589345, by rfl⟩ : syracuseStep 2119127 = 3178691) B3178691
theorem B3175937 : Blo 1411525 3175937 := bstep (se 2 (by rfl) ⟨1190976, by rfl⟩ : syracuseStep 3175937 = 2381953) B2381953
theorem B2119193 : Blo 1411525 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B2119307 : Blo 1411525 2119307 := bstep (se 1 (by rfl) ⟨1589480, by rfl⟩ : syracuseStep 2119307 = 3178961) B3178961
theorem B2119319 : Blo 1411525 2119319 := bstep (se 1 (by rfl) ⟨1589489, by rfl⟩ : syracuseStep 2119319 = 3178979) B3178979
theorem B1529515 : Blo 1411525 1529515 := bstep (se 1 (by rfl) ⟨1147136, by rfl⟩ : syracuseStep 1529515 = 2294273) B2294273
theorem B4527809 : Blo 1411525 4527809 := bstep (se 2 (by rfl) ⟨1697928, by rfl⟩ : syracuseStep 4527809 = 3395857) B3395857
theorem B3577547 : Blo 1411525 3577547 := bstep (se 1 (by rfl) ⟨2683160, by rfl⟩ : syracuseStep 3577547 = 5366321) B5366321
theorem B3176153 : Blo 1411525 3176153 := bstep (se 2 (by rfl) ⟨1191057, by rfl⟩ : syracuseStep 3176153 = 2382115) B2382115
theorem B2119385 : Blo 1411525 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B3176243 : Blo 1411525 3176243 := bstep (se 1 (by rfl) ⟨2382182, by rfl⟩ : syracuseStep 3176243 = 4764365) B4764365
theorem B10180417 : Blo 1411525 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B2119499 : Blo 1411525 2119499 := bstep (se 1 (by rfl) ⟨1589624, by rfl⟩ : syracuseStep 2119499 = 3179249) B3179249
theorem B3176279 : Blo 1411525 3176279 := bstep (se 1 (by rfl) ⟨2382209, by rfl⟩ : syracuseStep 3176279 = 4764419) B4764419
theorem B2119511 : Blo 1411525 2119511 := bstep (se 1 (by rfl) ⟨1589633, by rfl⟩ : syracuseStep 2119511 = 3179267) B3179267
theorem B61962083 : Blo 1411525 61962083 := bstep (se 1 (by rfl) ⟨46471562, by rfl⟩ : syracuseStep 61962083 = 92943125) B92943125
theorem B2119577 : Blo 1411525 2119577 := bstep (se 2 (by rfl) ⟨794841, by rfl⟩ : syracuseStep 2119577 = 1589683) B1589683
theorem B10729421 : Blo 1411525 10729421 := bstep (se 3 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 10729421 = 4023533) B4023533
theorem B4020185 : Blo 1411525 4020185 := bstep (se 2 (by rfl) ⟨1507569, by rfl⟩ : syracuseStep 4020185 = 3015139) B3015139
theorem B4765661 : Blo 1411525 4765661 := bstep (se 3 (by rfl) ⟨893561, by rfl⟩ : syracuseStep 4765661 = 1787123) B1787123
theorem B3176459 : Blo 1411525 3176459 := bstep (se 1 (by rfl) ⟨2382344, by rfl⟩ : syracuseStep 3176459 = 4764689) B4764689
theorem B2119691 : Blo 1411525 2119691 := bstep (se 1 (by rfl) ⟨1589768, by rfl⟩ : syracuseStep 2119691 = 3179537) B3179537
theorem B15267857 : Blo 1411525 15267857 := bstep (se 2 (by rfl) ⟨5725446, by rfl⟩ : syracuseStep 15267857 = 11450893) B11450893
theorem B2119703 : Blo 1411525 2119703 := bstep (se 1 (by rfl) ⟨1589777, by rfl⟩ : syracuseStep 2119703 = 3179555) B3179555
theorem B4773953 : Blo 1411525 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B3176513 : Blo 1411525 3176513 := bstep (se 2 (by rfl) ⟨1191192, by rfl⟩ : syracuseStep 3176513 = 2382385) B2382385
theorem B4020299 : Blo 1411525 4020299 := bstep (se 1 (by rfl) ⟨3015224, by rfl⟩ : syracuseStep 4020299 = 6030449) B6030449
theorem B2119769 : Blo 1411525 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B5363891 : Blo 1411525 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B2119883 : Blo 1411525 2119883 := bstep (se 1 (by rfl) ⟨1589912, by rfl⟩ : syracuseStep 2119883 = 3179825) B3179825
theorem B2119895 : Blo 1411525 2119895 := bstep (se 1 (by rfl) ⟨1589921, by rfl⟩ : syracuseStep 2119895 = 3179843) B3179843
theorem B2382041 : Blo 1411525 2382041 := bstep (se 2 (by rfl) ⟨893265, by rfl⟩ : syracuseStep 2382041 = 1786531) B1786531
theorem B3922141 : Blo 1411525 3922141 := bstep (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) B1470803
theorem B3176729 : Blo 1411525 3176729 := bstep (se 2 (by rfl) ⟨1191273, by rfl⟩ : syracuseStep 3176729 = 2382547) B2382547
theorem B2119961 : Blo 1411525 2119961 := bstep (se 2 (by rfl) ⟨794985, by rfl⟩ : syracuseStep 2119961 = 1589971) B1589971
theorem B7149869 : Blo 1411525 7149869 := bstep (se 3 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 7149869 = 2681201) B2681201
theorem B2545985 : Blo 1411525 2545985 := bstep (se 2 (by rfl) ⟨954744, by rfl⟩ : syracuseStep 2545985 = 1909489) B1909489
theorem B2382169 : Blo 1411525 2382169 := bstep (se 2 (by rfl) ⟨893313, by rfl⟩ : syracuseStep 2382169 = 1786627) B1786627
theorem B10877285 : Blo 1411525 10877285 := bstep (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) B2039491
theorem B3176819 : Blo 1411525 3176819 := bstep (se 1 (by rfl) ⟨2382614, by rfl⟩ : syracuseStep 3176819 = 4765229) B4765229
theorem B2120075 : Blo 1411525 2120075 := bstep (se 1 (by rfl) ⟨1590056, by rfl⟩ : syracuseStep 2120075 = 3180113) B3180113
theorem B3176855 : Blo 1411525 3176855 := bstep (se 1 (by rfl) ⟨2382641, by rfl⟩ : syracuseStep 3176855 = 4765283) B4765283
theorem B2120087 : Blo 1411525 2120087 := bstep (se 1 (by rfl) ⟨1590065, by rfl⟩ : syracuseStep 2120087 = 3180131) B3180131
theorem B10729907 : Blo 1411525 10729907 := bstep (se 1 (by rfl) ⟨8047430, by rfl⟩ : syracuseStep 10729907 = 16094861) B16094861
theorem B2120153 : Blo 1411525 2120153 := bstep (se 2 (by rfl) ⟨795057, by rfl⟩ : syracuseStep 2120153 = 1590115) B1590115
theorem B3177035 : Blo 1411525 3177035 := bstep (se 1 (by rfl) ⟨2382776, by rfl⟩ : syracuseStep 3177035 = 4765553) B4765553
theorem B2120267 : Blo 1411525 2120267 := bstep (se 1 (by rfl) ⟨1590200, by rfl⟩ : syracuseStep 2120267 = 3180401) B3180401
theorem B2120279 : Blo 1411525 2120279 := bstep (se 1 (by rfl) ⟨1590209, by rfl⟩ : syracuseStep 2120279 = 3180419) B3180419
theorem B3177089 : Blo 1411525 3177089 := bstep (se 2 (by rfl) ⟨1191408, by rfl⟩ : syracuseStep 3177089 = 2382817) B2382817
theorem B6036241 : Blo 1411525 6036241 := bstep (se 2 (by rfl) ⟨2263590, by rfl⟩ : syracuseStep 6036241 = 4527181) B4527181
theorem B5094161 : Blo 1411525 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B1587991 : Blo 1411525 1587991 := bstep (se 1 (by rfl) ⟨1190993, by rfl⟩ : syracuseStep 1587991 = 2381987) B2381987
theorem B3177305 : Blo 1411525 3177305 := bstep (se 2 (by rfl) ⟨1191489, by rfl⟩ : syracuseStep 3177305 = 2382979) B2382979
theorem B32635747 : Blo 1411525 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B24148853 : Blo 1411525 24148853 := bstep (se 5 (by rfl) ⟨1131977, by rfl⟩ : syracuseStep 24148853 = 2263955) B2263955
theorem B2382743 : Blo 1411525 2382743 := bstep (se 1 (by rfl) ⟨1787057, by rfl⟩ : syracuseStep 2382743 = 3574115) B3574115
theorem B3177395 : Blo 1411525 3177395 := bstep (se 1 (by rfl) ⟨2383046, by rfl⟩ : syracuseStep 3177395 = 4766093) B4766093
theorem B1588171 : Blo 1411525 1588171 := bstep (se 1 (by rfl) ⟨1191128, by rfl⟩ : syracuseStep 1588171 = 2382257) B2382257
theorem B3177431 : Blo 1411525 3177431 := bstep (se 1 (by rfl) ⟨2383073, by rfl⟩ : syracuseStep 3177431 = 4766147) B4766147
theorem B2382871 : Blo 1411525 2382871 := bstep (se 1 (by rfl) ⟨1787153, by rfl⟩ : syracuseStep 2382871 = 3574307) B3574307
theorem B51526691 : Blo 1411525 51526691 := bstep (se 1 (by rfl) ⟨38645018, by rfl⟩ : syracuseStep 51526691 = 77290037) B77290037
theorem B1588279 : Blo 1411525 1588279 := bstep (se 1 (by rfl) ⟨1191209, by rfl⟩ : syracuseStep 1588279 = 2382419) B2382419
theorem B4766795 : Blo 1411525 4766795 := bstep (se 1 (by rfl) ⟨3575096, by rfl⟩ : syracuseStep 4766795 = 7150193) B7150193
theorem B3177611 : Blo 1411525 3177611 := bstep (se 1 (by rfl) ⟨2383208, by rfl⟩ : syracuseStep 3177611 = 4766417) B4766417
theorem B2038937 : Blo 1411525 2038937 := bstep (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) B1529203
theorem B4021427 : Blo 1411525 4021427 := bstep (se 1 (by rfl) ⟨3016070, by rfl⟩ : syracuseStep 4021427 = 6032141) B6032141
theorem B3177665 : Blo 1411525 3177665 := bstep (se 2 (by rfl) ⟨1191624, by rfl⟩ : syracuseStep 3177665 = 2383249) B2383249
theorem B11459789 : Blo 1411525 11459789 := bstep (se 3 (by rfl) ⟨2148710, by rfl⟩ : syracuseStep 11459789 = 4297421) B4297421
theorem B1588459 : Blo 1411525 1588459 := bstep (se 1 (by rfl) ⟨1191344, by rfl⟩ : syracuseStep 1588459 = 2382689) B2382689
theorem B1588567 : Blo 1411525 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B4767065 : Blo 1411525 4767065 := bstep (se 2 (by rfl) ⟨1787649, by rfl⟩ : syracuseStep 4767065 = 3575299) B3575299
theorem B3177881 : Blo 1411525 3177881 := bstep (se 2 (by rfl) ⟨1191705, by rfl⟩ : syracuseStep 3177881 = 2383411) B2383411
theorem B3177971 : Blo 1411525 3177971 := bstep (se 1 (by rfl) ⟨2383478, by rfl⟩ : syracuseStep 3177971 = 4766957) B4766957
theorem B10182149 : Blo 1411525 10182149 := bstep (se 4 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 10182149 = 1909153) B1909153
theorem B1908235 : Blo 1411525 1908235 := bstep (se 1 (by rfl) ⟨1431176, by rfl⟩ : syracuseStep 1908235 = 2862353) B2862353
theorem B1588747 : Blo 1411525 1588747 := bstep (se 1 (by rfl) ⟨1191560, by rfl⟩ : syracuseStep 1588747 = 2383121) B2383121
theorem B3178007 : Blo 1411525 3178007 := bstep (se 1 (by rfl) ⟨2383505, by rfl⟩ : syracuseStep 3178007 = 4767011) B4767011
theorem B4021825 : Blo 1411525 4021825 := bstep (se 2 (by rfl) ⟨1508184, by rfl⟩ : syracuseStep 4021825 = 3016369) B3016369
theorem B1588855 : Blo 1411525 1588855 := bstep (se 1 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 1588855 = 2383283) B2383283
theorem B5365379 : Blo 1411525 5365379 := bstep (se 1 (by rfl) ⟨4024034, by rfl⟩ : syracuseStep 5365379 = 8048069) B8048069
theorem B2383499 : Blo 1411525 2383499 := bstep (se 1 (by rfl) ⟨1787624, by rfl⟩ : syracuseStep 2383499 = 3575249) B3575249
theorem B3178187 : Blo 1411525 3178187 := bstep (se 1 (by rfl) ⟨2383640, by rfl⟩ : syracuseStep 3178187 = 4767281) B4767281
theorem B3178241 : Blo 1411525 3178241 := bstep (se 2 (by rfl) ⟨1191840, by rfl⟩ : syracuseStep 3178241 = 2383681) B2383681
theorem B2383627 : Blo 1411525 2383627 := bstep (se 1 (by rfl) ⟨1787720, by rfl⟩ : syracuseStep 2383627 = 3575441) B3575441
theorem B1589035 : Blo 1411525 1589035 := bstep (se 1 (by rfl) ⟨1191776, by rfl⟩ : syracuseStep 1589035 = 2383553) B2383553
theorem B10731365 : Blo 1411525 10731365 := bstep (se 4 (by rfl) ⟨1006065, by rfl⟩ : syracuseStep 10731365 = 2012131) B2012131
theorem B1589143 : Blo 1411525 1589143 := bstep (se 1 (by rfl) ⟨1191857, by rfl⟩ : syracuseStep 1589143 = 2383715) B2383715
theorem B2383769 : Blo 1411525 2383769 := bstep (se 2 (by rfl) ⟨893913, by rfl⟩ : syracuseStep 2383769 = 1787827) B1787827
theorem B3178457 : Blo 1411525 3178457 := bstep (se 2 (by rfl) ⟨1191921, by rfl⟩ : syracuseStep 3178457 = 2383843) B2383843
theorem B5439449 : Blo 1411525 5439449 := bstep (se 2 (by rfl) ⟨2039793, by rfl⟩ : syracuseStep 5439449 = 4079587) B4079587
theorem B3178511 : Blo 1411525 3178511 := bstep (se 1 (by rfl) ⟨2383883, by rfl⟩ : syracuseStep 3178511 = 4767767) B4767767
theorem B3178529 : Blo 1411525 3178529 := bstep (se 2 (by rfl) ⟨1191948, by rfl⟩ : syracuseStep 3178529 = 2383897) B2383897
theorem B40714285 : Blo 1411525 40714285 := bstep (se 3 (by rfl) ⟨7633928, by rfl⟩ : syracuseStep 40714285 = 15267857) B15267857
theorem B2383931 : Blo 1411525 2383931 := bstep (se 1 (by rfl) ⟨1787948, by rfl⟩ : syracuseStep 2383931 = 3575897) B3575897
theorem B11452589 : Blo 1411525 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B3440983 : Blo 1411525 3440983 := bstep (se 1 (by rfl) ⟨2580737, by rfl⟩ : syracuseStep 3440983 = 5161475) B5161475
theorem B1909111 : Blo 1411525 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B3178871 : Blo 1411525 3178871 := bstep (se 1 (by rfl) ⟨2384153, by rfl⟩ : syracuseStep 3178871 = 4768307) B4768307
theorem B1589647 : Blo 1411525 1589647 := bstep (se 1 (by rfl) ⟨1192235, by rfl⟩ : syracuseStep 1589647 = 2384471) B2384471
theorem B51560849 : Blo 1411525 51560849 := bstep (se 2 (by rfl) ⟨19335318, by rfl⟩ : syracuseStep 51560849 = 38670637) B38670637
theorem B3391897 : Blo 1411525 3391897 := bstep (se 2 (by rfl) ⟨1271961, by rfl⟩ : syracuseStep 3391897 = 2543923) B2543923
theorem B4022713 : Blo 1411525 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B2384329 : Blo 1411525 2384329 := bstep (se 2 (by rfl) ⟨894123, by rfl⟩ : syracuseStep 2384329 = 1788247) B1788247
theorem B7635467 : Blo 1411525 7635467 := bstep (se 1 (by rfl) ⟨5726600, by rfl⟩ : syracuseStep 7635467 = 11453201) B11453201
theorem B3179051 : Blo 1411525 3179051 := bstep (se 1 (by rfl) ⟨2384288, by rfl⟩ : syracuseStep 3179051 = 4768577) B4768577
theorem B10732337 : Blo 1411525 10732337 := bstep (se 2 (by rfl) ⟨4024626, by rfl⟩ : syracuseStep 10732337 = 8049253) B8049253
theorem B4023101 : Blo 1411525 4023101 := bstep (se 3 (by rfl) ⟨754331, by rfl⟩ : syracuseStep 4023101 = 1508663) B1508663
theorem B16081739 : Blo 1411525 16081739 := bstep (se 1 (by rfl) ⟨12061304, by rfl⟩ : syracuseStep 16081739 = 24122609) B24122609
theorem B1696631 : Blo 1411525 1696631 := bstep (se 1 (by rfl) ⟨1272473, by rfl⟩ : syracuseStep 1696631 = 2544947) B2544947
theorem B1590151 : Blo 1411525 1590151 := bstep (se 1 (by rfl) ⟨1192613, by rfl⟩ : syracuseStep 1590151 = 2385227) B2385227
theorem B6030227 : Blo 1411525 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B3179411 : Blo 1411525 3179411 := bstep (se 1 (by rfl) ⟨2384558, by rfl⟩ : syracuseStep 3179411 = 4769117) B4769117
theorem B3179465 : Blo 1411525 3179465 := bstep (se 2 (by rfl) ⟨1192299, by rfl⟩ : syracuseStep 3179465 = 2384599) B2384599
theorem B3392513 : Blo 1411525 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B6030379 : Blo 1411525 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B27133015 : Blo 1411525 27133015 := bstep (se 1 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 27133015 = 40699523) B40699523
theorem B2385031 : Blo 1411525 2385031 := bstep (se 1 (by rfl) ⟨1788773, by rfl⟩ : syracuseStep 2385031 = 3577547) B3577547
theorem B1787179 : Blo 1411525 1787179 := bstep (se 1 (by rfl) ⟨1340384, by rfl⟩ : syracuseStep 1787179 = 2680769) B2680769
theorem B7152947 : Blo 1411525 7152947 := bstep (se 1 (by rfl) ⟨5364710, by rfl⟩ : syracuseStep 7152947 = 10729421) B10729421
theorem B2680123 : Blo 1411525 2680123 := bstep (se 1 (by rfl) ⟨2010092, by rfl⟩ : syracuseStep 2680123 = 4020185) B4020185
theorem B2680199 : Blo 1411525 2680199 := bstep (se 1 (by rfl) ⟨2010149, by rfl⟩ : syracuseStep 2680199 = 4020299) B4020299
theorem B4769171 : Blo 1411525 4769171 := bstep (se 1 (by rfl) ⟨3576878, by rfl⟩ : syracuseStep 4769171 = 7153757) B7153757
theorem B3573193 : Blo 1411525 3573193 := bstep (se 2 (by rfl) ⟨1339947, by rfl⟩ : syracuseStep 3573193 = 2679895) B2679895
theorem B3016207 : Blo 1411525 3016207 := bstep (se 1 (by rfl) ⟨2262155, by rfl⟩ : syracuseStep 3016207 = 4524311) B4524311
theorem B1697323 : Blo 1411525 1697323 := bstep (se 1 (by rfl) ⟨1272992, by rfl⟩ : syracuseStep 1697323 = 2545985) B2545985
theorem B3573335 : Blo 1411525 3573335 := bstep (se 1 (by rfl) ⟨2680001, by rfl⟩ : syracuseStep 3573335 = 5360003) B5360003
theorem B7153271 : Blo 1411525 7153271 := bstep (se 1 (by rfl) ⟨5364953, by rfl⟩ : syracuseStep 7153271 = 10729907) B10729907
theorem B3180167 : Blo 1411525 3180167 := bstep (se 1 (by rfl) ⟨2385125, by rfl⟩ : syracuseStep 3180167 = 4770251) B4770251
theorem B3622553 : Blo 1411525 3622553 := bstep (se 2 (by rfl) ⟨1358457, by rfl⟩ : syracuseStep 3622553 = 2716915) B2716915
theorem B8046337 : Blo 1411525 8046337 := bstep (se 2 (by rfl) ⟨3017376, by rfl⟩ : syracuseStep 8046337 = 6034753) B6034753
theorem B2680609 : Blo 1411525 2680609 := bstep (se 2 (by rfl) ⟨1005228, by rfl⟩ : syracuseStep 2680609 = 2010457) B2010457
theorem B3180347 : Blo 1411525 3180347 := bstep (se 1 (by rfl) ⟨2385260, by rfl⟩ : syracuseStep 3180347 = 4770521) B4770521
theorem B4024217 : Blo 1411525 4024217 := bstep (se 2 (by rfl) ⟨1509081, by rfl⟩ : syracuseStep 4024217 = 3018163) B3018163
theorem B16099235 : Blo 1411525 16099235 := bstep (se 1 (by rfl) ⟨12074426, by rfl⟩ : syracuseStep 16099235 = 24148853) B24148853
theorem B1935289 : Blo 1411525 1935289 := bstep (se 2 (by rfl) ⟨725733, by rfl⟩ : syracuseStep 1935289 = 1451467) B1451467
theorem B34351127 : Blo 1411525 34351127 := bstep (se 1 (by rfl) ⟨25763345, by rfl⟩ : syracuseStep 34351127 = 51526691) B51526691
theorem B2680951 : Blo 1411525 2680951 := bstep (se 1 (by rfl) ⟨2010713, by rfl⟩ : syracuseStep 2680951 = 4021427) B4021427
theorem B1788151 : Blo 1411525 1788151 := bstep (se 1 (by rfl) ⟨1341113, by rfl⟩ : syracuseStep 1788151 = 2682227) B2682227
theorem B8046863 : Blo 1411525 8046863 := bstep (se 1 (by rfl) ⟨6035147, by rfl⟩ : syracuseStep 8046863 = 12070295) B12070295
theorem B1411591 : Blo 1411525 1411591 := bstep (se 1 (by rfl) ⟨1058693, by rfl⟩ : syracuseStep 1411591 = 2117387) B2117387
theorem B6031883 : Blo 1411525 6031883 := bstep (se 1 (by rfl) ⟨4523912, by rfl⟩ : syracuseStep 6031883 = 9047825) B9047825
theorem B1411599 : Blo 1411525 1411599 := bstep (se 1 (by rfl) ⟨1058699, by rfl⟩ : syracuseStep 1411599 = 2117399) B2117399
theorem B1411643 : Blo 1411525 1411643 := bstep (se 1 (by rfl) ⟨1058732, by rfl⟩ : syracuseStep 1411643 = 2117465) B2117465
theorem B1788475 : Blo 1411525 1788475 := bstep (se 1 (by rfl) ⟨1341356, by rfl⟩ : syracuseStep 1788475 = 2682713) B2682713
theorem B7154243 : Blo 1411525 7154243 := bstep (se 1 (by rfl) ⟨5365682, by rfl⟩ : syracuseStep 7154243 = 10731365) B10731365
theorem B5360215 : Blo 1411525 5360215 := bstep (se 1 (by rfl) ⟨4020161, by rfl⟩ : syracuseStep 5360215 = 8040323) B8040323
theorem B1411719 : Blo 1411525 1411719 := bstep (se 1 (by rfl) ⟨1058789, by rfl⟩ : syracuseStep 1411719 = 2117579) B2117579
theorem B1411727 : Blo 1411525 1411727 := bstep (se 1 (by rfl) ⟨1058795, by rfl⟩ : syracuseStep 1411727 = 2117591) B2117591
theorem B2009785 : Blo 1411525 2009785 := bstep (se 2 (by rfl) ⟨753669, by rfl⟩ : syracuseStep 2009785 = 1507339) B1507339
theorem B1411771 : Blo 1411525 1411771 := bstep (se 1 (by rfl) ⟨1058828, by rfl⟩ : syracuseStep 1411771 = 2117657) B2117657
theorem B13568741 : Blo 1411525 13568741 := bstep (se 4 (by rfl) ⟨1272069, by rfl⟩ : syracuseStep 13568741 = 2544139) B2544139
theorem B1411847 : Blo 1411525 1411847 := bstep (se 1 (by rfl) ⟨1058885, by rfl⟩ : syracuseStep 1411847 = 2117771) B2117771
theorem B1411855 : Blo 1411525 1411855 := bstep (se 1 (by rfl) ⟨1058891, by rfl⟩ : syracuseStep 1411855 = 2117783) B2117783
theorem B9046799 : Blo 1411525 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B4770575 : Blo 1411525 4770575 := bstep (se 1 (by rfl) ⟨3577931, by rfl⟩ : syracuseStep 4770575 = 7155863) B7155863
theorem B1411899 : Blo 1411525 1411899 := bstep (se 1 (by rfl) ⟨1058924, by rfl⟩ : syracuseStep 1411899 = 2117849) B2117849
theorem B6785851 : Blo 1411525 6785851 := bstep (se 1 (by rfl) ⟨5089388, by rfl⟩ : syracuseStep 6785851 = 10178777) B10178777
theorem B5360519 : Blo 1411525 5360519 := bstep (se 1 (by rfl) ⟨4020389, by rfl⟩ : syracuseStep 5360519 = 8040779) B8040779
theorem B1411975 : Blo 1411525 1411975 := bstep (se 1 (by rfl) ⟨1058981, by rfl⟩ : syracuseStep 1411975 = 2117963) B2117963
theorem B7154567 : Blo 1411525 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B1411983 : Blo 1411525 1411983 := bstep (se 1 (by rfl) ⟨1058987, by rfl⟩ : syracuseStep 1411983 = 2117975) B2117975
theorem B8039321 : Blo 1411525 8039321 := bstep (se 2 (by rfl) ⟨3014745, by rfl⟩ : syracuseStep 8039321 = 6029491) B6029491
theorem B1412027 : Blo 1411525 1412027 := bstep (se 1 (by rfl) ⟨1059020, by rfl⟩ : syracuseStep 1412027 = 2118041) B2118041
theorem B5229521 : Blo 1411525 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B1412103 : Blo 1411525 1412103 := bstep (se 1 (by rfl) ⟨1059077, by rfl⟩ : syracuseStep 1412103 = 2118155) B2118155
theorem B1412111 : Blo 1411525 1412111 := bstep (se 1 (by rfl) ⟨1059083, by rfl⟩ : syracuseStep 1412111 = 2118167) B2118167
theorem B1412155 : Blo 1411525 1412155 := bstep (se 1 (by rfl) ⟨1059116, by rfl⟩ : syracuseStep 1412155 = 2118233) B2118233
theorem B5360701 : Blo 1411525 5360701 := bstep (se 3 (by rfl) ⟨1005131, by rfl⟩ : syracuseStep 5360701 = 2010263) B2010263
theorem B1412231 : Blo 1411525 1412231 := bstep (se 1 (by rfl) ⟨1059173, by rfl⟩ : syracuseStep 1412231 = 2118347) B2118347
theorem B1412239 : Blo 1411525 1412239 := bstep (se 1 (by rfl) ⟨1059179, by rfl⟩ : syracuseStep 1412239 = 2118359) B2118359
theorem B1412283 : Blo 1411525 1412283 := bstep (se 1 (by rfl) ⟨1059212, by rfl⟩ : syracuseStep 1412283 = 2118425) B2118425
theorem B1412359 : Blo 1411525 1412359 := bstep (se 1 (by rfl) ⟨1059269, by rfl⟩ : syracuseStep 1412359 = 2118539) B2118539
theorem B1412367 : Blo 1411525 1412367 := bstep (se 1 (by rfl) ⟨1059275, by rfl⟩ : syracuseStep 1412367 = 2118551) B2118551
theorem B1412411 : Blo 1411525 1412411 := bstep (se 1 (by rfl) ⟨1059308, by rfl⟩ : syracuseStep 1412411 = 2118617) B2118617
theorem B1412487 : Blo 1411525 1412487 := bstep (se 1 (by rfl) ⟨1059365, by rfl⟩ : syracuseStep 1412487 = 2118731) B2118731
theorem B1412495 : Blo 1411525 1412495 := bstep (se 1 (by rfl) ⟨1059371, by rfl⟩ : syracuseStep 1412495 = 2118743) B2118743
theorem B34368947 : Blo 1411525 34368947 := bstep (se 1 (by rfl) ⟨25776710, by rfl⟩ : syracuseStep 34368947 = 51553421) B51553421
theorem B6032825 : Blo 1411525 6032825 := bstep (se 2 (by rfl) ⟨2262309, by rfl⟩ : syracuseStep 6032825 = 4524619) B4524619
theorem B1412539 : Blo 1411525 1412539 := bstep (se 1 (by rfl) ⟨1059404, by rfl⟩ : syracuseStep 1412539 = 2118809) B2118809
theorem B1412615 : Blo 1411525 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B1412623 : Blo 1411525 1412623 := bstep (se 1 (by rfl) ⟨1059467, by rfl⟩ : syracuseStep 1412623 = 2118935) B2118935
theorem B1412667 : Blo 1411525 1412667 := bstep (se 1 (by rfl) ⟨1059500, by rfl⟩ : syracuseStep 1412667 = 2119001) B2119001
theorem B3575411 : Blo 1411525 3575411 := bstep (se 1 (by rfl) ⟨2681558, by rfl⟩ : syracuseStep 3575411 = 5363117) B5363117
theorem B1412743 : Blo 1411525 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B1412751 : Blo 1411525 1412751 := bstep (se 1 (by rfl) ⟨1059563, by rfl⟩ : syracuseStep 1412751 = 2119127) B2119127
theorem B2117291 : Blo 1411525 2117291 := bstep (se 1 (by rfl) ⟨1587968, by rfl⟩ : syracuseStep 2117291 = 3175937) B3175937
theorem B2682553 : Blo 1411525 2682553 := bstep (se 2 (by rfl) ⟨1005957, by rfl⟩ : syracuseStep 2682553 = 2011915) B2011915
theorem B1412795 : Blo 1411525 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B8048321 : Blo 1411525 8048321 := bstep (se 2 (by rfl) ⟨3018120, by rfl⟩ : syracuseStep 8048321 = 6036241) B6036241
theorem B2117321 : Blo 1411525 2117321 := bstep (se 2 (by rfl) ⟨793995, by rfl⟩ : syracuseStep 2117321 = 1587991) B1587991
theorem B1412871 : Blo 1411525 1412871 := bstep (se 1 (by rfl) ⟨1059653, by rfl⟩ : syracuseStep 1412871 = 2119307) B2119307
theorem B1412879 : Blo 1411525 1412879 := bstep (se 1 (by rfl) ⟨1059659, by rfl⟩ : syracuseStep 1412879 = 2119319) B2119319
theorem B3018539 : Blo 1411525 3018539 := bstep (se 1 (by rfl) ⟨2263904, by rfl⟩ : syracuseStep 3018539 = 4527809) B4527809
theorem B2117435 : Blo 1411525 2117435 := bstep (se 1 (by rfl) ⟨1588076, by rfl⟩ : syracuseStep 2117435 = 3176153) B3176153
theorem B5091131 : Blo 1411525 5091131 := bstep (se 1 (by rfl) ⟨3818348, by rfl⟩ : syracuseStep 5091131 = 7636697) B7636697
theorem B1412923 : Blo 1411525 1412923 := bstep (se 1 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 1412923 = 2119385) B2119385
theorem B2117495 : Blo 1411525 2117495 := bstep (se 1 (by rfl) ⟨1588121, by rfl⟩ : syracuseStep 2117495 = 3176243) B3176243
theorem B2862983 : Blo 1411525 2862983 := bstep (se 1 (by rfl) ⟨2147237, by rfl⟩ : syracuseStep 2862983 = 4294475) B4294475
theorem B2011015 : Blo 1411525 2011015 := bstep (se 1 (by rfl) ⟨1508261, by rfl⟩ : syracuseStep 2011015 = 3016523) B3016523
theorem B1412999 : Blo 1411525 1412999 := bstep (se 1 (by rfl) ⟨1059749, by rfl⟩ : syracuseStep 1412999 = 2119499) B2119499
theorem B2117519 : Blo 1411525 2117519 := bstep (se 1 (by rfl) ⟨1588139, by rfl⟩ : syracuseStep 2117519 = 3176279) B3176279
theorem B1413007 : Blo 1411525 1413007 := bstep (se 1 (by rfl) ⟨1059755, by rfl⟩ : syracuseStep 1413007 = 2119511) B2119511
theorem B41308055 : Blo 1411525 41308055 := bstep (se 1 (by rfl) ⟨30981041, by rfl⟩ : syracuseStep 41308055 = 61962083) B61962083
theorem B2117561 : Blo 1411525 2117561 := bstep (se 2 (by rfl) ⟨794085, by rfl⟩ : syracuseStep 2117561 = 1588171) B1588171
theorem B1413051 : Blo 1411525 1413051 := bstep (se 1 (by rfl) ⟨1059788, by rfl⟩ : syracuseStep 1413051 = 2119577) B2119577
theorem B2117639 : Blo 1411525 2117639 := bstep (se 1 (by rfl) ⟨1588229, by rfl⟩ : syracuseStep 2117639 = 3176459) B3176459
theorem B1413127 : Blo 1411525 1413127 := bstep (se 1 (by rfl) ⟨1059845, by rfl⟩ : syracuseStep 1413127 = 2119691) B2119691
theorem B1413135 : Blo 1411525 1413135 := bstep (se 1 (by rfl) ⟨1059851, by rfl⟩ : syracuseStep 1413135 = 2119703) B2119703
theorem B2682895 : Blo 1411525 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B70660117 : Blo 1411525 70660117 := bstep (se 6 (by rfl) ⟨1656096, by rfl⟩ : syracuseStep 70660117 = 3312193) B3312193
theorem B8589341 : Blo 1411525 8589341 := bstep (se 3 (by rfl) ⟨1610501, by rfl⟩ : syracuseStep 8589341 = 3221003) B3221003
theorem B3182635 : Blo 1411525 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B2117675 : Blo 1411525 2117675 := bstep (se 1 (by rfl) ⟨1588256, by rfl⟩ : syracuseStep 2117675 = 3176513) B3176513
theorem B1413179 : Blo 1411525 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B2117705 : Blo 1411525 2117705 := bstep (se 2 (by rfl) ⟨794139, by rfl⟩ : syracuseStep 2117705 = 1588279) B1588279
theorem B3575927 : Blo 1411525 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B1413255 : Blo 1411525 1413255 := bstep (se 1 (by rfl) ⟨1059941, by rfl⟩ : syracuseStep 1413255 = 2119883) B2119883
theorem B1413263 : Blo 1411525 1413263 := bstep (se 1 (by rfl) ⟨1059947, by rfl⟩ : syracuseStep 1413263 = 2119895) B2119895
theorem B2117819 : Blo 1411525 2117819 := bstep (se 1 (by rfl) ⟨1588364, by rfl⟩ : syracuseStep 2117819 = 3176729) B3176729
theorem B1413307 : Blo 1411525 1413307 := bstep (se 1 (by rfl) ⟨1059980, by rfl⟩ : syracuseStep 1413307 = 2119961) B2119961
theorem B2117879 : Blo 1411525 2117879 := bstep (se 1 (by rfl) ⟨1588409, by rfl⟩ : syracuseStep 2117879 = 3176819) B3176819
theorem B1413383 : Blo 1411525 1413383 := bstep (se 1 (by rfl) ⟨1060037, by rfl⟩ : syracuseStep 1413383 = 2120075) B2120075
theorem B2117903 : Blo 1411525 2117903 := bstep (se 1 (by rfl) ⟨1588427, by rfl⟩ : syracuseStep 2117903 = 3176855) B3176855
theorem B1413391 : Blo 1411525 1413391 := bstep (se 1 (by rfl) ⟨1060043, by rfl⟩ : syracuseStep 1413391 = 2120087) B2120087
theorem B2117945 : Blo 1411525 2117945 := bstep (se 2 (by rfl) ⟨794229, by rfl⟩ : syracuseStep 2117945 = 1588459) B1588459
theorem B1413435 : Blo 1411525 1413435 := bstep (se 1 (by rfl) ⟨1060076, by rfl⟩ : syracuseStep 1413435 = 2120153) B2120153
theorem B2118023 : Blo 1411525 2118023 := bstep (se 1 (by rfl) ⟨1588517, by rfl⟩ : syracuseStep 2118023 = 3177035) B3177035
theorem B1413511 : Blo 1411525 1413511 := bstep (se 1 (by rfl) ⟨1060133, by rfl⟩ : syracuseStep 1413511 = 2120267) B2120267
theorem B1413519 : Blo 1411525 1413519 := bstep (se 1 (by rfl) ⟨1060139, by rfl⟩ : syracuseStep 1413519 = 2120279) B2120279
theorem B2118059 : Blo 1411525 2118059 := bstep (se 1 (by rfl) ⟨1588544, by rfl⟩ : syracuseStep 2118059 = 3177089) B3177089
theorem B2118089 : Blo 1411525 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B15692291 : Blo 1411525 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B3396107 : Blo 1411525 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B4764203 : Blo 1411525 4764203 := bstep (se 1 (by rfl) ⟨3573152, by rfl⟩ : syracuseStep 4764203 = 7146305) B7146305
theorem B2118203 : Blo 1411525 2118203 := bstep (se 1 (by rfl) ⟨1588652, by rfl⟩ : syracuseStep 2118203 = 3177305) B3177305
theorem B2011721 : Blo 1411525 2011721 := bstep (se 2 (by rfl) ⟨754395, by rfl⟩ : syracuseStep 2011721 = 1508791) B1508791
theorem B2118263 : Blo 1411525 2118263 := bstep (se 1 (by rfl) ⟨1588697, by rfl⟩ : syracuseStep 2118263 = 3177395) B3177395
theorem B2118287 : Blo 1411525 2118287 := bstep (se 1 (by rfl) ⟨1588715, by rfl⟩ : syracuseStep 2118287 = 3177431) B3177431
theorem B2544313 : Blo 1411525 2544313 := bstep (se 2 (by rfl) ⟨954117, by rfl⟩ : syracuseStep 2544313 = 1908235) B1908235
theorem B2118329 : Blo 1411525 2118329 := bstep (se 2 (by rfl) ⟨794373, by rfl⟩ : syracuseStep 2118329 = 1588747) B1588747
theorem B2011835 : Blo 1411525 2011835 := bstep (se 1 (by rfl) ⟨1508876, by rfl⟩ : syracuseStep 2011835 = 3017753) B3017753
theorem B5362433 : Blo 1411525 5362433 := bstep (se 2 (by rfl) ⟨2010912, by rfl⟩ : syracuseStep 5362433 = 4021825) B4021825
theorem B2118407 : Blo 1411525 2118407 := bstep (se 1 (by rfl) ⟨1588805, by rfl⟩ : syracuseStep 2118407 = 3177611) B3177611
theorem B2118443 : Blo 1411525 2118443 := bstep (se 1 (by rfl) ⟨1588832, by rfl⟩ : syracuseStep 2118443 = 3177665) B3177665
theorem B7639859 : Blo 1411525 7639859 := bstep (se 1 (by rfl) ⟨5729894, by rfl⟩ : syracuseStep 7639859 = 11459789) B11459789
theorem B2118473 : Blo 1411525 2118473 := bstep (se 2 (by rfl) ⟨794427, by rfl⟩ : syracuseStep 2118473 = 1588855) B1588855
theorem B2863991 : Blo 1411525 2863991 := bstep (se 1 (by rfl) ⟨2147993, by rfl⟩ : syracuseStep 2863991 = 4295987) B4295987
theorem B2118587 : Blo 1411525 2118587 := bstep (se 1 (by rfl) ⟨1588940, by rfl⟩ : syracuseStep 2118587 = 3177881) B3177881
theorem B2118647 : Blo 1411525 2118647 := bstep (se 1 (by rfl) ⟨1588985, by rfl⟩ : syracuseStep 2118647 = 3177971) B3177971
theorem B6788099 : Blo 1411525 6788099 := bstep (se 1 (by rfl) ⟨5091074, by rfl⟩ : syracuseStep 6788099 = 10182149) B10182149
theorem B2118671 : Blo 1411525 2118671 := bstep (se 1 (by rfl) ⟨1589003, by rfl⟩ : syracuseStep 2118671 = 3178007) B3178007
theorem B7148573 : Blo 1411525 7148573 := bstep (se 3 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 7148573 = 2680715) B2680715
theorem B2118713 : Blo 1411525 2118713 := bstep (se 2 (by rfl) ⟨794517, by rfl⟩ : syracuseStep 2118713 = 1589035) B1589035
theorem B3576919 : Blo 1411525 3576919 := bstep (se 1 (by rfl) ⟨2682689, by rfl⟩ : syracuseStep 3576919 = 5365379) B5365379
theorem B2118791 : Blo 1411525 2118791 := bstep (se 1 (by rfl) ⟨1589093, by rfl⟩ : syracuseStep 2118791 = 3178187) B3178187
theorem B2118827 : Blo 1411525 2118827 := bstep (se 1 (by rfl) ⟨1589120, by rfl⟩ : syracuseStep 2118827 = 3178241) B3178241
theorem B2118857 : Blo 1411525 2118857 := bstep (se 2 (by rfl) ⟨794571, by rfl⟩ : syracuseStep 2118857 = 1589143) B1589143
theorem B18093293 : Blo 1411525 18093293 := bstep (se 3 (by rfl) ⟨3392492, by rfl⟩ : syracuseStep 18093293 = 6784985) B6784985
theorem B2176313 : Blo 1411525 2176313 := bstep (se 2 (by rfl) ⟨816117, by rfl⟩ : syracuseStep 2176313 = 1632235) B1632235
theorem B2012473 : Blo 1411525 2012473 := bstep (se 2 (by rfl) ⟨754677, by rfl⟩ : syracuseStep 2012473 = 1509355) B1509355
theorem B2118971 : Blo 1411525 2118971 := bstep (se 1 (by rfl) ⟨1589228, by rfl⟩ : syracuseStep 2118971 = 3178457) B3178457
theorem B3626299 : Blo 1411525 3626299 := bstep (se 1 (by rfl) ⟨2719724, by rfl⟩ : syracuseStep 3626299 = 5439449) B5439449
theorem B2119031 : Blo 1411525 2119031 := bstep (se 1 (by rfl) ⟨1589273, by rfl⟩ : syracuseStep 2119031 = 3178547) B3178547
theorem B4412807 : Blo 1411525 4412807 := bstep (se 1 (by rfl) ⟨3309605, by rfl⟩ : syracuseStep 4412807 = 6619211) B6619211
theorem B6034823 : Blo 1411525 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B3577223 : Blo 1411525 3577223 := bstep (se 1 (by rfl) ⟨2682917, by rfl⟩ : syracuseStep 3577223 = 5365835) B5365835
theorem B2119055 : Blo 1411525 2119055 := bstep (se 1 (by rfl) ⟨1589291, by rfl⟩ : syracuseStep 2119055 = 3178583) B3178583
theorem B2119097 : Blo 1411525 2119097 := bstep (se 2 (by rfl) ⟨794661, by rfl⟩ : syracuseStep 2119097 = 1589323) B1589323
theorem B7149059 : Blo 1411525 7149059 := bstep (se 1 (by rfl) ⟨5361794, by rfl⟩ : syracuseStep 7149059 = 10723589) B10723589
theorem B2119175 : Blo 1411525 2119175 := bstep (se 1 (by rfl) ⟨1589381, by rfl⟩ : syracuseStep 2119175 = 3178763) B3178763
theorem B4077067 : Blo 1411525 4077067 := bstep (se 1 (by rfl) ⟨3057800, by rfl⟩ : syracuseStep 4077067 = 6115601) B6115601
theorem B3577355 : Blo 1411525 3577355 := bstep (se 1 (by rfl) ⟨2683016, by rfl⟩ : syracuseStep 3577355 = 5366033) B5366033
theorem B2119211 : Blo 1411525 2119211 := bstep (se 1 (by rfl) ⟨1589408, by rfl⟩ : syracuseStep 2119211 = 3178817) B3178817
theorem B2119241 : Blo 1411525 2119241 := bstep (se 2 (by rfl) ⟨794715, by rfl⟩ : syracuseStep 2119241 = 1589431) B1589431
theorem B6444631 : Blo 1411525 6444631 := bstep (se 1 (by rfl) ⟨4833473, by rfl⟩ : syracuseStep 6444631 = 9666947) B9666947
theorem B3438215 : Blo 1411525 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B2119355 : Blo 1411525 2119355 := bstep (se 1 (by rfl) ⟨1589516, by rfl⟩ : syracuseStep 2119355 = 3179033) B3179033
theorem B16307905 : Blo 1411525 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B2119415 : Blo 1411525 2119415 := bstep (se 1 (by rfl) ⟨1589561, by rfl⟩ : syracuseStep 2119415 = 3179123) B3179123
theorem B4019969 : Blo 1411525 4019969 := bstep (se 2 (by rfl) ⟨1507488, by rfl⟩ : syracuseStep 4019969 = 3014977) B3014977
theorem B3176207 : Blo 1411525 3176207 := bstep (se 1 (by rfl) ⟨2382155, by rfl⟩ : syracuseStep 3176207 = 4764311) B4764311
theorem B2119439 : Blo 1411525 2119439 := bstep (se 1 (by rfl) ⟨1589579, by rfl⟩ : syracuseStep 2119439 = 3179159) B3179159
theorem B3176225 : Blo 1411525 3176225 := bstep (se 2 (by rfl) ⟨1191084, by rfl⟩ : syracuseStep 3176225 = 2382169) B2382169
theorem B18339635 : Blo 1411525 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B2119481 : Blo 1411525 2119481 := bstep (se 2 (by rfl) ⟨794805, by rfl⟩ : syracuseStep 2119481 = 1589611) B1589611
theorem B4765499 : Blo 1411525 4765499 := bstep (se 1 (by rfl) ⟨3574124, by rfl⟩ : syracuseStep 4765499 = 7148249) B7148249
theorem B29407093 : Blo 1411525 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B2119559 : Blo 1411525 2119559 := bstep (se 1 (by rfl) ⟨1589669, by rfl⟩ : syracuseStep 2119559 = 3179339) B3179339
theorem B5363603 : Blo 1411525 5363603 := bstep (se 1 (by rfl) ⟨4022702, by rfl⟩ : syracuseStep 5363603 = 8045405) B8045405
theorem B2119595 : Blo 1411525 2119595 := bstep (se 1 (by rfl) ⟨1589696, by rfl⟩ : syracuseStep 2119595 = 3179393) B3179393
theorem B2119625 : Blo 1411525 2119625 := bstep (se 2 (by rfl) ⟨794859, by rfl⟩ : syracuseStep 2119625 = 1589719) B1589719
theorem B18110411 : Blo 1411525 18110411 := bstep (se 1 (by rfl) ⟨13582808, by rfl⟩ : syracuseStep 18110411 = 27165617) B27165617
theorem B3577871 : Blo 1411525 3577871 := bstep (se 1 (by rfl) ⟨2683403, by rfl⟩ : syracuseStep 3577871 = 5366807) B5366807
theorem B2119739 : Blo 1411525 2119739 := bstep (se 1 (by rfl) ⟨1589804, by rfl⟩ : syracuseStep 2119739 = 3179609) B3179609
theorem B3176567 : Blo 1411525 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B2119799 : Blo 1411525 2119799 := bstep (se 1 (by rfl) ⟨1589849, by rfl⟩ : syracuseStep 2119799 = 3179699) B3179699
theorem B2865287 : Blo 1411525 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B2119823 : Blo 1411525 2119823 := bstep (se 1 (by rfl) ⟨1589867, by rfl⟩ : syracuseStep 2119823 = 3179735) B3179735
theorem B9050285 : Blo 1411525 9050285 := bstep (se 3 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 9050285 = 3393857) B3393857
theorem B2119865 : Blo 1411525 2119865 := bstep (se 2 (by rfl) ⟨794949, by rfl⟩ : syracuseStep 2119865 = 1589899) B1589899
theorem B4020425 : Blo 1411525 4020425 := bstep (se 2 (by rfl) ⟨1507659, by rfl⟩ : syracuseStep 4020425 = 3015319) B3015319
theorem B3922121 : Blo 1411525 3922121 := bstep (se 2 (by rfl) ⟨1470795, by rfl⟩ : syracuseStep 3922121 = 2941591) B2941591
theorem B2119943 : Blo 1411525 2119943 := bstep (se 1 (by rfl) ⟨1589957, by rfl⟩ : syracuseStep 2119943 = 3179915) B3179915
theorem B29006093 : Blo 1411525 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B2382095 : Blo 1411525 2382095 := bstep (se 1 (by rfl) ⟨1786571, by rfl⟩ : syracuseStep 2382095 = 3573143) B3573143
theorem B4765985 : Blo 1411525 4765985 := bstep (se 2 (by rfl) ⟨1787244, by rfl⟩ : syracuseStep 4765985 = 3574489) B3574489
theorem B3176747 : Blo 1411525 3176747 := bstep (se 1 (by rfl) ⟨2382560, by rfl⟩ : syracuseStep 3176747 = 4765121) B4765121
theorem B2119979 : Blo 1411525 2119979 := bstep (se 1 (by rfl) ⟨1589984, by rfl⟩ : syracuseStep 2119979 = 3179969) B3179969
theorem B2120009 : Blo 1411525 2120009 := bstep (se 2 (by rfl) ⟨795003, by rfl⟩ : syracuseStep 2120009 = 1590007) B1590007
theorem B5364103 : Blo 1411525 5364103 := bstep (se 1 (by rfl) ⟨4023077, by rfl⟩ : syracuseStep 5364103 = 8046155) B8046155
theorem B2120123 : Blo 1411525 2120123 := bstep (se 1 (by rfl) ⟨1590092, by rfl⟩ : syracuseStep 2120123 = 3180185) B3180185
theorem B43514329 : Blo 1411525 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B2120183 : Blo 1411525 2120183 := bstep (se 1 (by rfl) ⟨1590137, by rfl⟩ : syracuseStep 2120183 = 3180275) B3180275
theorem B2120207 : Blo 1411525 2120207 := bstep (se 1 (by rfl) ⟨1590155, by rfl⟩ : syracuseStep 2120207 = 3180311) B3180311
theorem B2120249 : Blo 1411525 2120249 := bstep (se 2 (by rfl) ⟨795093, by rfl⟩ : syracuseStep 2120249 = 1590187) B1590187
theorem B3177107 : Blo 1411525 3177107 := bstep (se 1 (by rfl) ⟨2382830, by rfl⟩ : syracuseStep 3177107 = 4765661) B4765661
theorem B3177161 : Blo 1411525 3177161 := bstep (se 2 (by rfl) ⟨1191435, by rfl⟩ : syracuseStep 3177161 = 2382871) B2382871
theorem B6036257 : Blo 1411525 6036257 := bstep (se 2 (by rfl) ⟨2263596, by rfl⟩ : syracuseStep 6036257 = 4527193) B4527193
theorem B2382635 : Blo 1411525 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B1588027 : Blo 1411525 1588027 := bstep (se 1 (by rfl) ⟨1191020, by rfl⟩ : syracuseStep 1588027 = 2382041) B2382041
theorem B12229465 : Blo 1411525 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B4766579 : Blo 1411525 4766579 := bstep (se 1 (by rfl) ⟨3574934, by rfl⟩ : syracuseStep 4766579 = 7149869) B7149869
theorem B10730393 : Blo 1411525 10730393 := bstep (se 2 (by rfl) ⟨4023897, by rfl⟩ : syracuseStep 10730393 = 8047795) B8047795
theorem B21748661 : Blo 1411525 21748661 := bstep (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) B2038937
theorem B7150679 : Blo 1411525 7150679 := bstep (se 1 (by rfl) ⟨5363009, by rfl⟩ : syracuseStep 7150679 = 10726019) B10726019
theorem B6036599 : Blo 1411525 6036599 := bstep (se 1 (by rfl) ⟨4527449, by rfl⟩ : syracuseStep 6036599 = 9054899) B9054899
theorem B2383033 : Blo 1411525 2383033 := bstep (se 2 (by rfl) ⟨893637, by rfl⟩ : syracuseStep 2383033 = 1787275) B1787275
theorem B1588495 : Blo 1411525 1588495 := bstep (se 1 (by rfl) ⟨1191371, by rfl⟩ : syracuseStep 1588495 = 2382743) B2382743
theorem B3177863 : Blo 1411525 3177863 := bstep (se 1 (by rfl) ⟨2383397, by rfl⟩ : syracuseStep 3177863 = 4766795) B4766795
theorem B2039353 : Blo 1411525 2039353 := bstep (se 2 (by rfl) ⟨764757, by rfl⟩ : syracuseStep 2039353 = 1529515) B1529515
theorem B3178043 : Blo 1411525 3178043 := bstep (se 1 (by rfl) ⟨2383532, by rfl⟩ : syracuseStep 3178043 = 4767065) B4767065
theorem B7151165 : Blo 1411525 7151165 := bstep (se 3 (by rfl) ⟨1340843, by rfl⟩ : syracuseStep 7151165 = 2681687) B2681687
theorem B3178169 : Blo 1411525 3178169 := bstep (se 2 (by rfl) ⟨1191813, by rfl⟩ : syracuseStep 3178169 = 2383627) B2383627
theorem B13573889 : Blo 1411525 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B1588999 : Blo 1411525 1588999 := bstep (se 1 (by rfl) ⟨1191749, by rfl⟩ : syracuseStep 1588999 = 2383499) B2383499
theorem B6438689 : Blo 1411525 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B4022075 : Blo 1411525 4022075 := bstep (se 1 (by rfl) ⟨3016556, by rfl⟩ : syracuseStep 4022075 = 6033113) B6033113
theorem B2383735 : Blo 1411525 2383735 := bstep (se 1 (by rfl) ⟨1787801, by rfl⟩ : syracuseStep 2383735 = 3575603) B3575603
theorem B6201235 : Blo 1411525 6201235 := bstep (se 1 (by rfl) ⟨4650926, by rfl⟩ : syracuseStep 6201235 = 9301853) B9301853
theorem B1589179 : Blo 1411525 1589179 := bstep (se 1 (by rfl) ⟨1191884, by rfl⟩ : syracuseStep 1589179 = 2383769) B2383769
theorem B5726227 : Blo 1411525 5726227 := bstep (se 1 (by rfl) ⟨4294670, by rfl⟩ : syracuseStep 5726227 = 8589341) B8589341
theorem B1589287 : Blo 1411525 1589287 := bstep (se 1 (by rfl) ⟨1191965, by rfl⟩ : syracuseStep 1589287 = 2383931) B2383931
theorem B4243513 : Blo 1411525 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B2383951 : Blo 1411525 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B7635059 : Blo 1411525 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B34373899 : Blo 1411525 34373899 := bstep (se 1 (by rfl) ⟨25780424, by rfl⟩ : syracuseStep 34373899 = 51560849) B51560849
theorem B2384201 : Blo 1411525 2384201 := bstep (se 2 (by rfl) ⟨894075, by rfl⟩ : syracuseStep 2384201 = 1788151) B1788151
theorem B10461527 : Blo 1411525 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B4587977 : Blo 1411525 4587977 := bstep (se 2 (by rfl) ⟨1720491, by rfl⟩ : syracuseStep 4587977 = 3440983) B3440983
theorem B7152137 : Blo 1411525 7152137 := bstep (se 2 (by rfl) ⟨2682051, by rfl⟩ : syracuseStep 7152137 = 5364103) B5364103
theorem B4522529 : Blo 1411525 4522529 := bstep (se 2 (by rfl) ⟨1695948, by rfl⟩ : syracuseStep 4522529 = 3391897) B3391897
theorem B1909327 : Blo 1411525 1909327 := bstep (se 1 (by rfl) ⟨1431995, by rfl⟩ : syracuseStep 1909327 = 2863991) B2863991
theorem B3179105 : Blo 1411525 3179105 := bstep (se 2 (by rfl) ⟨1192164, by rfl⟩ : syracuseStep 3179105 = 2384329) B2384329
theorem B2261675 : Blo 1411525 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B2384633 : Blo 1411525 2384633 := bstep (se 2 (by rfl) ⟨894237, by rfl⟩ : syracuseStep 2384633 = 1788475) B1788475
theorem B4768631 : Blo 1411525 4768631 := bstep (se 1 (by rfl) ⟨3576473, by rfl⟩ : syracuseStep 4768631 = 7152947) B7152947
theorem B2679713 : Blo 1411525 2679713 := bstep (se 2 (by rfl) ⟨1004892, by rfl⟩ : syracuseStep 2679713 = 2009785) B2009785
theorem B3392417 : Blo 1411525 3392417 := bstep (se 2 (by rfl) ⟨1272156, by rfl⟩ : syracuseStep 3392417 = 2544313) B2544313
theorem B1786799 : Blo 1411525 1786799 := bstep (se 1 (by rfl) ⟨1340099, by rfl⟩ : syracuseStep 1786799 = 2680199) B2680199
theorem B2941871 : Blo 1411525 2941871 := bstep (se 1 (by rfl) ⟨2206403, by rfl⟩ : syracuseStep 2941871 = 4412807) B4412807
theorem B4023215 : Blo 1411525 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B2384815 : Blo 1411525 2384815 := bstep (se 1 (by rfl) ⟨1788611, by rfl⟩ : syracuseStep 2384815 = 3577223) B3577223
theorem B3179447 : Blo 1411525 3179447 := bstep (se 1 (by rfl) ⟨2384585, by rfl⟩ : syracuseStep 3179447 = 4769171) B4769171
theorem B2384903 : Blo 1411525 2384903 := bstep (se 1 (by rfl) ⟨1788677, by rfl⟩ : syracuseStep 2384903 = 3577355) B3577355
theorem B4768847 : Blo 1411525 4768847 := bstep (se 1 (by rfl) ⟨3576635, by rfl⟩ : syracuseStep 4768847 = 7153271) B7153271
theorem B2679979 : Blo 1411525 2679979 := bstep (se 1 (by rfl) ⟨2009984, by rfl⟩ : syracuseStep 2679979 = 4019969) B4019969
theorem B10732823 : Blo 1411525 10732823 := bstep (se 1 (by rfl) ⟨8049617, by rfl⟩ : syracuseStep 10732823 = 16099235) B16099235
theorem B2385247 : Blo 1411525 2385247 := bstep (se 1 (by rfl) ⟨1788935, by rfl⟩ : syracuseStep 2385247 = 3577871) B3577871
theorem B1910191 : Blo 1411525 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B36177353 : Blo 1411525 36177353 := bstep (se 2 (by rfl) ⟨13566507, by rfl⟩ : syracuseStep 36177353 = 27133015) B27133015
theorem B4769225 : Blo 1411525 4769225 := bstep (se 2 (by rfl) ⟨1788459, by rfl⟩ : syracuseStep 4769225 = 3576919) B3576919
theorem B2680283 : Blo 1411525 2680283 := bstep (se 1 (by rfl) ⟨2010212, by rfl⟩ : syracuseStep 2680283 = 4020425) B4020425
theorem B2614747 : Blo 1411525 2614747 := bstep (se 1 (by rfl) ⟨1961060, by rfl⟩ : syracuseStep 2614747 = 3922121) B3922121
theorem B3180041 : Blo 1411525 3180041 := bstep (se 2 (by rfl) ⟨1192515, by rfl⟩ : syracuseStep 3180041 = 2385031) B2385031
theorem B4769495 : Blo 1411525 4769495 := bstep (se 1 (by rfl) ⟨3577121, by rfl⟩ : syracuseStep 4769495 = 7154243) B7154243
theorem B3573497 : Blo 1411525 3573497 := bstep (se 2 (by rfl) ⟨1340061, by rfl⟩ : syracuseStep 3573497 = 2680123) B2680123
theorem B4835065 : Blo 1411525 4835065 := bstep (se 2 (by rfl) ⟨1813149, by rfl⟩ : syracuseStep 4835065 = 3626299) B3626299
theorem B9045827 : Blo 1411525 9045827 := bstep (se 1 (by rfl) ⟨6784370, by rfl⟩ : syracuseStep 9045827 = 13568741) B13568741
theorem B6031199 : Blo 1411525 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B3180383 : Blo 1411525 3180383 := bstep (se 1 (by rfl) ⟨2385287, by rfl⟩ : syracuseStep 3180383 = 4770575) B4770575
theorem B4024171 : Blo 1411525 4024171 := bstep (se 1 (by rfl) ⟨3018128, by rfl⟩ : syracuseStep 4024171 = 6036257) B6036257
theorem B3573679 : Blo 1411525 3573679 := bstep (se 1 (by rfl) ⟨2680259, by rfl⟩ : syracuseStep 3573679 = 5360519) B5360519
theorem B4769711 : Blo 1411525 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B5359547 : Blo 1411525 5359547 := bstep (se 1 (by rfl) ⟨4019660, by rfl⟩ : syracuseStep 5359547 = 8039321) B8039321
theorem B7153595 : Blo 1411525 7153595 := bstep (se 1 (by rfl) ⟨5365196, by rfl⟩ : syracuseStep 7153595 = 10730393) B10730393
theorem B2263097 : Blo 1411525 2263097 := bstep (se 2 (by rfl) ⟨848661, by rfl⟩ : syracuseStep 2263097 = 1697323) B1697323
theorem B4024399 : Blo 1411525 4024399 := bstep (se 1 (by rfl) ⟨3018299, by rfl⟩ : syracuseStep 4024399 = 6036599) B6036599
theorem B10725533 : Blo 1411525 10725533 := bstep (se 3 (by rfl) ⟨2011037, by rfl⟩ : syracuseStep 10725533 = 4022075) B4022075
theorem B13576349 : Blo 1411525 13576349 := bstep (se 3 (by rfl) ⟨2545565, by rfl⟩ : syracuseStep 13576349 = 5091131) B5091131
theorem B21743873 : Blo 1411525 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B4524349 : Blo 1411525 4524349 := bstep (se 3 (by rfl) ⟨848315, by rfl⟩ : syracuseStep 4524349 = 1696631) B1696631
theorem B3574145 : Blo 1411525 3574145 := bstep (se 2 (by rfl) ⟨1340304, by rfl⟩ : syracuseStep 3574145 = 2680609) B2680609
theorem B1411527 : Blo 1411525 1411527 := bstep (se 1 (by rfl) ⟨1058645, by rfl⟩ : syracuseStep 1411527 = 2117291) B2117291
theorem B1411547 : Blo 1411525 1411547 := bstep (se 1 (by rfl) ⟨1058660, by rfl⟩ : syracuseStep 1411547 = 2117321) B2117321
theorem B2681353 : Blo 1411525 2681353 := bstep (se 2 (by rfl) ⟨1005507, by rfl⟩ : syracuseStep 2681353 = 2011015) B2011015
theorem B8268313 : Blo 1411525 8268313 := bstep (se 2 (by rfl) ⟨3100617, by rfl⟩ : syracuseStep 8268313 = 6201235) B6201235
theorem B1411623 : Blo 1411525 1411623 := bstep (se 1 (by rfl) ⟨1058717, by rfl⟩ : syracuseStep 1411623 = 2117435) B2117435
theorem B1411663 : Blo 1411525 1411663 := bstep (se 1 (by rfl) ⟨1058747, by rfl⟩ : syracuseStep 1411663 = 2117495) B2117495
theorem B1411679 : Blo 1411525 1411679 := bstep (se 1 (by rfl) ⟨1058759, by rfl⟩ : syracuseStep 1411679 = 2117519) B2117519
theorem B1411707 : Blo 1411525 1411707 := bstep (se 1 (by rfl) ⟨1058780, by rfl⟩ : syracuseStep 1411707 = 2117561) B2117561
theorem B1411759 : Blo 1411525 1411759 := bstep (se 1 (by rfl) ⟨1058819, by rfl⟩ : syracuseStep 1411759 = 2117639) B2117639
theorem B1411783 : Blo 1411525 1411783 := bstep (se 1 (by rfl) ⟨1058837, by rfl⟩ : syracuseStep 1411783 = 2117675) B2117675
theorem B1411803 : Blo 1411525 1411803 := bstep (se 1 (by rfl) ⟨1058852, by rfl⟩ : syracuseStep 1411803 = 2117705) B2117705
theorem B1411879 : Blo 1411525 1411879 := bstep (se 1 (by rfl) ⟨1058909, by rfl⟩ : syracuseStep 1411879 = 2117819) B2117819
theorem B3574601 : Blo 1411525 3574601 := bstep (se 2 (by rfl) ⟨1340475, by rfl⟩ : syracuseStep 3574601 = 2680951) B2680951
theorem B1411919 : Blo 1411525 1411919 := bstep (se 1 (by rfl) ⟨1058939, by rfl⟩ : syracuseStep 1411919 = 2117879) B2117879
theorem B1411935 : Blo 1411525 1411935 := bstep (se 1 (by rfl) ⟨1058951, by rfl⟩ : syracuseStep 1411935 = 2117903) B2117903
theorem B1411963 : Blo 1411525 1411963 := bstep (se 1 (by rfl) ⟨1058972, by rfl⟩ : syracuseStep 1411963 = 2117945) B2117945
theorem B1412015 : Blo 1411525 1412015 := bstep (se 1 (by rfl) ⟨1059011, by rfl⟩ : syracuseStep 1412015 = 2118023) B2118023
theorem B1412039 : Blo 1411525 1412039 := bstep (se 1 (by rfl) ⟨1059029, by rfl⟩ : syracuseStep 1412039 = 2118059) B2118059
theorem B1412059 : Blo 1411525 1412059 := bstep (se 1 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 1412059 = 2118089) B2118089
theorem B5090311 : Blo 1411525 5090311 := bstep (se 1 (by rfl) ⟨3817733, by rfl⟩ : syracuseStep 5090311 = 7635467) B7635467
theorem B1412135 : Blo 1411525 1412135 := bstep (se 1 (by rfl) ⟨1059101, by rfl⟩ : syracuseStep 1412135 = 2118203) B2118203
theorem B1412175 : Blo 1411525 1412175 := bstep (se 1 (by rfl) ⟨1059131, by rfl⟩ : syracuseStep 1412175 = 2118263) B2118263
theorem B1412191 : Blo 1411525 1412191 := bstep (se 1 (by rfl) ⟨1059143, by rfl⟩ : syracuseStep 1412191 = 2118287) B2118287
theorem B1412219 : Blo 1411525 1412219 := bstep (se 1 (by rfl) ⟨1059164, by rfl⟩ : syracuseStep 1412219 = 2118329) B2118329
theorem B3574955 : Blo 1411525 3574955 := bstep (se 1 (by rfl) ⟨2681216, by rfl⟩ : syracuseStep 3574955 = 5362433) B5362433
theorem B1412271 : Blo 1411525 1412271 := bstep (se 1 (by rfl) ⟨1059203, by rfl⟩ : syracuseStep 1412271 = 2118407) B2118407
theorem B1412295 : Blo 1411525 1412295 := bstep (se 1 (by rfl) ⟨1059221, by rfl⟩ : syracuseStep 1412295 = 2118443) B2118443
theorem B7154891 : Blo 1411525 7154891 := bstep (se 1 (by rfl) ⟨5366168, by rfl⟩ : syracuseStep 7154891 = 10732337) B10732337
theorem B2682067 : Blo 1411525 2682067 := bstep (se 1 (by rfl) ⟨2011550, by rfl⟩ : syracuseStep 2682067 = 4023101) B4023101
theorem B1412315 : Blo 1411525 1412315 := bstep (se 1 (by rfl) ⟨1059236, by rfl⟩ : syracuseStep 1412315 = 2118473) B2118473
theorem B58019105 : Blo 1411525 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B1412391 : Blo 1411525 1412391 := bstep (se 1 (by rfl) ⟨1059293, by rfl⟩ : syracuseStep 1412391 = 2118587) B2118587
theorem B1412431 : Blo 1411525 1412431 := bstep (se 1 (by rfl) ⟨1059323, by rfl⟩ : syracuseStep 1412431 = 2118647) B2118647
theorem B4525399 : Blo 1411525 4525399 := bstep (se 1 (by rfl) ⟨3394049, by rfl⟩ : syracuseStep 4525399 = 6788099) B6788099
theorem B1412447 : Blo 1411525 1412447 := bstep (se 1 (by rfl) ⟨1059335, by rfl⟩ : syracuseStep 1412447 = 2118671) B2118671
theorem B1412475 : Blo 1411525 1412475 := bstep (se 1 (by rfl) ⟨1059356, by rfl⟩ : syracuseStep 1412475 = 2118713) B2118713
theorem B1412527 : Blo 1411525 1412527 := bstep (se 1 (by rfl) ⟨1059395, by rfl⟩ : syracuseStep 1412527 = 2118791) B2118791
theorem B1412551 : Blo 1411525 1412551 := bstep (se 1 (by rfl) ⟨1059413, by rfl⟩ : syracuseStep 1412551 = 2118827) B2118827
theorem B7146953 : Blo 1411525 7146953 := bstep (se 2 (by rfl) ⟨2680107, by rfl⟩ : syracuseStep 7146953 = 5360215) B5360215
theorem B1412571 : Blo 1411525 1412571 := bstep (se 1 (by rfl) ⟨1059428, by rfl⟩ : syracuseStep 1412571 = 2118857) B2118857
theorem B5803501 : Blo 1411525 5803501 := bstep (se 3 (by rfl) ⟨1088156, by rfl⟩ : syracuseStep 5803501 = 2176313) B2176313
theorem B12062195 : Blo 1411525 12062195 := bstep (se 1 (by rfl) ⟨9046646, by rfl⟩ : syracuseStep 12062195 = 18093293) B18093293
theorem B1412647 : Blo 1411525 1412647 := bstep (se 1 (by rfl) ⟨1059485, by rfl⟩ : syracuseStep 1412647 = 2118971) B2118971
theorem B1412687 : Blo 1411525 1412687 := bstep (se 1 (by rfl) ⟨1059515, by rfl⟩ : syracuseStep 1412687 = 2119031) B2119031
theorem B1412703 : Blo 1411525 1412703 := bstep (se 1 (by rfl) ⟨1059527, by rfl⟩ : syracuseStep 1412703 = 2119055) B2119055
theorem B1412731 : Blo 1411525 1412731 := bstep (se 1 (by rfl) ⟨1059548, by rfl⟩ : syracuseStep 1412731 = 2119097) B2119097
theorem B1412783 : Blo 1411525 1412783 := bstep (se 1 (by rfl) ⟨1059587, by rfl⟩ : syracuseStep 1412783 = 2119175) B2119175
theorem B1412807 : Blo 1411525 1412807 := bstep (se 1 (by rfl) ⟨1059605, by rfl⟩ : syracuseStep 1412807 = 2119211) B2119211
theorem B1412827 : Blo 1411525 1412827 := bstep (se 1 (by rfl) ⟨1059620, by rfl⟩ : syracuseStep 1412827 = 2119241) B2119241
theorem B2117369 : Blo 1411525 2117369 := bstep (se 2 (by rfl) ⟨794013, by rfl⟩ : syracuseStep 2117369 = 1588027) B1588027
theorem B9047801 : Blo 1411525 9047801 := bstep (se 2 (by rfl) ⟨3392925, by rfl⟩ : syracuseStep 9047801 = 6785851) B6785851
theorem B16305953 : Blo 1411525 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B1412903 : Blo 1411525 1412903 := bstep (se 1 (by rfl) ⟨1059677, by rfl⟩ : syracuseStep 1412903 = 2119355) B2119355
theorem B1412943 : Blo 1411525 1412943 := bstep (se 1 (by rfl) ⟨1059707, by rfl⟩ : syracuseStep 1412943 = 2119415) B2119415
theorem B2117471 : Blo 1411525 2117471 := bstep (se 1 (by rfl) ⟨1588103, by rfl⟩ : syracuseStep 2117471 = 3176207) B3176207
theorem B1412959 : Blo 1411525 1412959 := bstep (se 1 (by rfl) ⟨1059719, by rfl⟩ : syracuseStep 1412959 = 2119439) B2119439
theorem B2117483 : Blo 1411525 2117483 := bstep (se 1 (by rfl) ⟨1588112, by rfl⟩ : syracuseStep 2117483 = 3176225) B3176225
theorem B1412987 : Blo 1411525 1412987 := bstep (se 1 (by rfl) ⟨1059740, by rfl⟩ : syracuseStep 1412987 = 2119481) B2119481
theorem B1413039 : Blo 1411525 1413039 := bstep (se 1 (by rfl) ⟨1059779, by rfl⟩ : syracuseStep 1413039 = 2119559) B2119559
theorem B3575735 : Blo 1411525 3575735 := bstep (se 1 (by rfl) ⟨2681801, by rfl⟩ : syracuseStep 3575735 = 5363603) B5363603
theorem B2682811 : Blo 1411525 2682811 := bstep (se 1 (by rfl) ⟨2012108, by rfl⟩ : syracuseStep 2682811 = 4024217) B4024217
theorem B1413063 : Blo 1411525 1413063 := bstep (se 1 (by rfl) ⟨1059797, by rfl⟩ : syracuseStep 1413063 = 2119595) B2119595
theorem B1413083 : Blo 1411525 1413083 := bstep (se 1 (by rfl) ⟨1059812, by rfl⟩ : syracuseStep 1413083 = 2119625) B2119625
theorem B22900751 : Blo 1411525 22900751 := bstep (se 1 (by rfl) ⟨17175563, by rfl⟩ : syracuseStep 22900751 = 34351127) B34351127
theorem B9056285 : Blo 1411525 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B1413159 : Blo 1411525 1413159 := bstep (se 1 (by rfl) ⟨1059869, by rfl⟩ : syracuseStep 1413159 = 2119739) B2119739
theorem B8040505 : Blo 1411525 8040505 := bstep (se 2 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 8040505 = 6030379) B6030379
theorem B2117711 : Blo 1411525 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B1413199 : Blo 1411525 1413199 := bstep (se 1 (by rfl) ⟨1059899, by rfl⟩ : syracuseStep 1413199 = 2119799) B2119799
theorem B7147601 : Blo 1411525 7147601 := bstep (se 2 (by rfl) ⟨2680350, by rfl⟩ : syracuseStep 7147601 = 5360701) B5360701
theorem B1413215 : Blo 1411525 1413215 := bstep (se 1 (by rfl) ⟨1059911, by rfl⟩ : syracuseStep 1413215 = 2119823) B2119823
theorem B6033523 : Blo 1411525 6033523 := bstep (se 1 (by rfl) ⟨4525142, by rfl⟩ : syracuseStep 6033523 = 9050285) B9050285
theorem B1413243 : Blo 1411525 1413243 := bstep (se 1 (by rfl) ⟨1059932, by rfl⟩ : syracuseStep 1413243 = 2119865) B2119865
theorem B1413295 : Blo 1411525 1413295 := bstep (se 1 (by rfl) ⟨1059971, by rfl⟩ : syracuseStep 1413295 = 2119943) B2119943
theorem B19337395 : Blo 1411525 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B2117831 : Blo 1411525 2117831 := bstep (se 1 (by rfl) ⟨1588373, by rfl⟩ : syracuseStep 2117831 = 3176747) B3176747
theorem B1413319 : Blo 1411525 1413319 := bstep (se 1 (by rfl) ⟨1059989, by rfl⟩ : syracuseStep 1413319 = 2119979) B2119979
theorem B1413339 : Blo 1411525 1413339 := bstep (se 1 (by rfl) ⟨1060004, by rfl⟩ : syracuseStep 1413339 = 2120009) B2120009
theorem B1413415 : Blo 1411525 1413415 := bstep (se 1 (by rfl) ⟨1060061, by rfl⟩ : syracuseStep 1413415 = 2120123) B2120123
theorem B1413455 : Blo 1411525 1413455 := bstep (se 1 (by rfl) ⟨1060091, by rfl⟩ : syracuseStep 1413455 = 2120183) B2120183
theorem B1413471 : Blo 1411525 1413471 := bstep (se 1 (by rfl) ⟨1060103, by rfl⟩ : syracuseStep 1413471 = 2120207) B2120207
theorem B2117993 : Blo 1411525 2117993 := bstep (se 2 (by rfl) ⟨794247, by rfl⟩ : syracuseStep 2117993 = 1588495) B1588495
theorem B1413499 : Blo 1411525 1413499 := bstep (se 1 (by rfl) ⟨1060124, by rfl⟩ : syracuseStep 1413499 = 2120249) B2120249
theorem B2683297 : Blo 1411525 2683297 := bstep (se 2 (by rfl) ⟨1006236, by rfl⟩ : syracuseStep 2683297 = 2012473) B2012473
theorem B2118071 : Blo 1411525 2118071 := bstep (se 1 (by rfl) ⟨1588553, by rfl⟩ : syracuseStep 2118071 = 3177107) B3177107
theorem B2118107 : Blo 1411525 2118107 := bstep (se 1 (by rfl) ⟨1588580, by rfl⟩ : syracuseStep 2118107 = 3177161) B3177161
theorem B4764257 : Blo 1411525 4764257 := bstep (se 2 (by rfl) ⟨1786596, by rfl⟩ : syracuseStep 4764257 = 3573193) B3573193
theorem B3486347 : Blo 1411525 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B5436089 : Blo 1411525 5436089 := bstep (se 2 (by rfl) ⟨2038533, by rfl⟩ : syracuseStep 5436089 = 4077067) B4077067
theorem B3576737 : Blo 1411525 3576737 := bstep (se 2 (by rfl) ⟨1341276, by rfl⟩ : syracuseStep 3576737 = 2682553) B2682553
theorem B2118575 : Blo 1411525 2118575 := bstep (se 1 (by rfl) ⟨1588931, by rfl⟩ : syracuseStep 2118575 = 3177863) B3177863
theorem B10728449 : Blo 1411525 10728449 := bstep (se 2 (by rfl) ⟨4023168, by rfl⟩ : syracuseStep 10728449 = 8046337) B8046337
theorem B2118665 : Blo 1411525 2118665 := bstep (se 2 (by rfl) ⟨794499, by rfl⟩ : syracuseStep 2118665 = 1588999) B1588999
theorem B2118695 : Blo 1411525 2118695 := bstep (se 1 (by rfl) ⟨1589021, by rfl⟩ : syracuseStep 2118695 = 3178043) B3178043
theorem B2118779 : Blo 1411525 2118779 := bstep (se 1 (by rfl) ⟨1589084, by rfl⟩ : syracuseStep 2118779 = 3178169) B3178169
theorem B9049259 : Blo 1411525 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B2012359 : Blo 1411525 2012359 := bstep (se 1 (by rfl) ⟨1509269, by rfl⟩ : syracuseStep 2012359 = 3018539) B3018539
theorem B2118905 : Blo 1411525 2118905 := bstep (se 2 (by rfl) ⟨794589, by rfl⟩ : syracuseStep 2118905 = 1589179) B1589179
theorem B27538703 : Blo 1411525 27538703 := bstep (se 1 (by rfl) ⟨20654027, by rfl⟩ : syracuseStep 27538703 = 41308055) B41308055
theorem B2119007 : Blo 1411525 2119007 := bstep (se 1 (by rfl) ⟨1589255, by rfl⟩ : syracuseStep 2119007 = 3178511) B3178511
theorem B3577193 : Blo 1411525 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B2119019 : Blo 1411525 2119019 := bstep (se 1 (by rfl) ⟨1589264, by rfl⟩ : syracuseStep 2119019 = 3178529) B3178529
theorem B94213489 : Blo 1411525 94213489 := bstep (se 2 (by rfl) ⟨35330058, by rfl⟩ : syracuseStep 94213489 = 70660117) B70660117
theorem B54285713 : Blo 1411525 54285713 := bstep (se 2 (by rfl) ⟨20357142, by rfl⟩ : syracuseStep 54285713 = 40714285) B40714285
theorem B2119247 : Blo 1411525 2119247 := bstep (se 1 (by rfl) ⟨1589435, by rfl⟩ : syracuseStep 2119247 = 3178871) B3178871
theorem B3176135 : Blo 1411525 3176135 := bstep (se 1 (by rfl) ⟨2382101, by rfl⟩ : syracuseStep 3176135 = 4764203) B4764203
theorem B2119367 : Blo 1411525 2119367 := bstep (se 1 (by rfl) ⟨1589525, by rfl⟩ : syracuseStep 2119367 = 3179051) B3179051
theorem B2545481 : Blo 1411525 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B2119529 : Blo 1411525 2119529 := bstep (se 2 (by rfl) ⟨794823, by rfl⟩ : syracuseStep 2119529 = 1589647) B1589647
theorem B5093239 : Blo 1411525 5093239 := bstep (se 1 (by rfl) ⟨3819929, by rfl⟩ : syracuseStep 5093239 = 7639859) B7639859
theorem B10721159 : Blo 1411525 10721159 := bstep (se 1 (by rfl) ⟨8040869, by rfl⟩ : syracuseStep 10721159 = 16081739) B16081739
theorem B5363617 : Blo 1411525 5363617 := bstep (se 2 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 5363617 = 4022713) B4022713
theorem B4020151 : Blo 1411525 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B2119607 : Blo 1411525 2119607 := bstep (se 1 (by rfl) ⟨1589705, by rfl⟩ : syracuseStep 2119607 = 3179411) B3179411
theorem B2119643 : Blo 1411525 2119643 := bstep (se 1 (by rfl) ⟨1589732, by rfl⟩ : syracuseStep 2119643 = 3179465) B3179465
theorem B4765715 : Blo 1411525 4765715 := bstep (se 1 (by rfl) ⟨3574286, by rfl⟩ : syracuseStep 4765715 = 7148573) B7148573
theorem B4766039 : Blo 1411525 4766039 := bstep (se 1 (by rfl) ⟨3574529, by rfl⟩ : syracuseStep 4766039 = 7149059) B7149059
theorem B2382223 : Blo 1411525 2382223 := bstep (se 1 (by rfl) ⟨1786667, by rfl⟩ : syracuseStep 2382223 = 3573335) B3573335
theorem B2292143 : Blo 1411525 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B2120111 : Blo 1411525 2120111 := bstep (se 1 (by rfl) ⟨1590083, by rfl⟩ : syracuseStep 2120111 = 3180167) B3180167
theorem B2415035 : Blo 1411525 2415035 := bstep (se 1 (by rfl) ⟨1811276, by rfl⟩ : syracuseStep 2415035 = 3622553) B3622553
theorem B2120201 : Blo 1411525 2120201 := bstep (se 2 (by rfl) ⟨795075, by rfl⟩ : syracuseStep 2120201 = 1590151) B1590151
theorem B43506197 : Blo 1411525 43506197 := bstep (se 6 (by rfl) ⟨1019676, by rfl⟩ : syracuseStep 43506197 = 2039353) B2039353
theorem B3176999 : Blo 1411525 3176999 := bstep (se 1 (by rfl) ⟨2382749, by rfl⟩ : syracuseStep 3176999 = 4765499) B4765499
theorem B2120231 : Blo 1411525 2120231 := bstep (se 1 (by rfl) ⟨1590173, by rfl⟩ : syracuseStep 2120231 = 3180347) B3180347
theorem B12073607 : Blo 1411525 12073607 := bstep (se 1 (by rfl) ⟨9055205, by rfl⟩ : syracuseStep 12073607 = 18110411) B18110411
theorem B1588063 : Blo 1411525 1588063 := bstep (se 1 (by rfl) ⟨1191047, by rfl⟩ : syracuseStep 1588063 = 2382095) B2382095
theorem B5364575 : Blo 1411525 5364575 := bstep (se 1 (by rfl) ⟨4023431, by rfl⟩ : syracuseStep 5364575 = 8046863) B8046863
theorem B3177323 : Blo 1411525 3177323 := bstep (se 1 (by rfl) ⟨2382992, by rfl⟩ : syracuseStep 3177323 = 4765985) B4765985
theorem B5364589 : Blo 1411525 5364589 := bstep (se 3 (by rfl) ⟨1005860, by rfl⟩ : syracuseStep 5364589 = 2011721) B2011721
theorem B3177377 : Blo 1411525 3177377 := bstep (se 2 (by rfl) ⟨1191516, by rfl⟩ : syracuseStep 3177377 = 2383033) B2383033
theorem B4021255 : Blo 1411525 4021255 := bstep (se 1 (by rfl) ⟨3015941, by rfl⟩ : syracuseStep 4021255 = 6031883) B6031883
theorem B2382905 : Blo 1411525 2382905 := bstep (se 2 (by rfl) ⟨893589, by rfl⟩ : syracuseStep 2382905 = 1787179) B1787179
theorem B5364893 : Blo 1411525 5364893 := bstep (se 3 (by rfl) ⟨1005917, by rfl⟩ : syracuseStep 5364893 = 2011835) B2011835
theorem B1588423 : Blo 1411525 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B3177719 : Blo 1411525 3177719 := bstep (se 1 (by rfl) ⟨2383289, by rfl⟩ : syracuseStep 3177719 = 4766579) B4766579
theorem B14499107 : Blo 1411525 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B4021609 : Blo 1411525 4021609 := bstep (se 2 (by rfl) ⟨1508103, by rfl⟩ : syracuseStep 4021609 = 3016207) B3016207
theorem B4767119 : Blo 1411525 4767119 := bstep (se 1 (by rfl) ⟨3575339, by rfl⟩ : syracuseStep 4767119 = 7150679) B7150679
theorem B8592841 : Blo 1411525 8592841 := bstep (se 2 (by rfl) ⟨3222315, by rfl⟩ : syracuseStep 8592841 = 6444631) B6444631
theorem B48905693 : Blo 1411525 48905693 := bstep (se 3 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 48905693 = 18339635) B18339635
theorem B22912631 : Blo 1411525 22912631 := bstep (se 1 (by rfl) ⟨17184473, by rfl⟩ : syracuseStep 22912631 = 34368947) B34368947
theorem B4021883 : Blo 1411525 4021883 := bstep (se 1 (by rfl) ⟨3016412, by rfl⟩ : syracuseStep 4021883 = 6032825) B6032825
theorem B7634621 : Blo 1411525 7634621 := bstep (se 3 (by rfl) ⟨1431491, by rfl⟩ : syracuseStep 7634621 = 2862983) B2862983
theorem B4767443 : Blo 1411525 4767443 := bstep (se 1 (by rfl) ⟨3575582, by rfl⟩ : syracuseStep 4767443 = 7151165) B7151165
theorem B2383607 : Blo 1411525 2383607 := bstep (se 1 (by rfl) ⟨1787705, by rfl⟩ : syracuseStep 2383607 = 3575411) B3575411
theorem B627351317 : Blo 1411525 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B5365547 : Blo 1411525 5365547 := bstep (se 1 (by rfl) ⟨4024160, by rfl⟩ : syracuseStep 5365547 = 8048321) B8048321
theorem B3178313 : Blo 1411525 3178313 := bstep (se 2 (by rfl) ⟨1191867, by rfl⟩ : syracuseStep 3178313 = 2383735) B2383735
theorem B4292459 : Blo 1411525 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B2580385 : Blo 1411525 2580385 := bstep (se 2 (by rfl) ⟨967644, by rfl⟩ : syracuseStep 2580385 = 1935289) B1935289
theorem B6037523 : Blo 1411525 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B7634969 : Blo 1411525 7634969 := bstep (se 2 (by rfl) ⟨2863113, by rfl⟩ : syracuseStep 7634969 = 5726227) B5726227
theorem B3178601 : Blo 1411525 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B5365865 : Blo 1411525 5365865 := bstep (se 2 (by rfl) ⟨2012199, by rfl⟩ : syracuseStep 5365865 = 4024399) B4024399
theorem B8044697 : Blo 1411525 8044697 := bstep (se 2 (by rfl) ⟨3016761, by rfl⟩ : syracuseStep 8044697 = 6033523) B6033523
theorem B1589467 : Blo 1411525 1589467 := bstep (se 1 (by rfl) ⟨1192100, by rfl⟩ : syracuseStep 1589467 = 2384201) B2384201
theorem B4768091 : Blo 1411525 4768091 := bstep (se 1 (by rfl) ⟨3576068, by rfl⟩ : syracuseStep 4768091 = 7152137) B7152137
theorem B3015019 : Blo 1411525 3015019 := bstep (se 1 (by rfl) ⟨2261264, by rfl⟩ : syracuseStep 3015019 = 4522529) B4522529
theorem B1507783 : Blo 1411525 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B148750805 : Blo 1411525 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B1589755 : Blo 1411525 1589755 := bstep (se 1 (by rfl) ⟨1192316, by rfl⟩ : syracuseStep 1589755 = 2384633) B2384633
theorem B3179087 : Blo 1411525 3179087 := bstep (se 1 (by rfl) ⟨2384315, by rfl⟩ : syracuseStep 3179087 = 4768631) B4768631
theorem B1786475 : Blo 1411525 1786475 := bstep (se 1 (by rfl) ⟨1339856, by rfl⟩ : syracuseStep 1786475 = 2679713) B2679713
theorem B2261611 : Blo 1411525 2261611 := bstep (se 1 (by rfl) ⟨1696208, by rfl⟩ : syracuseStep 2261611 = 3392417) B3392417
theorem B2384491 : Blo 1411525 2384491 := bstep (se 1 (by rfl) ⟨1788368, by rfl⟩ : syracuseStep 2384491 = 3576737) B3576737
theorem B7152299 : Blo 1411525 7152299 := bstep (se 1 (by rfl) ⟨5364224, by rfl⟩ : syracuseStep 7152299 = 10728449) B10728449
theorem B1589935 : Blo 1411525 1589935 := bstep (se 1 (by rfl) ⟨1192451, by rfl⟩ : syracuseStep 1589935 = 2384903) B2384903
theorem B3179231 : Blo 1411525 3179231 := bstep (se 1 (by rfl) ⟨2384423, by rfl⟩ : syracuseStep 3179231 = 4768847) B4768847
theorem B18359135 : Blo 1411525 18359135 := bstep (se 1 (by rfl) ⟨13769351, by rfl⟩ : syracuseStep 18359135 = 27538703) B27538703
theorem B2384795 : Blo 1411525 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B24118235 : Blo 1411525 24118235 := bstep (se 1 (by rfl) ⟨18088676, by rfl⟩ : syracuseStep 24118235 = 36177353) B36177353
theorem B3179483 : Blo 1411525 3179483 := bstep (se 1 (by rfl) ⟨2384612, by rfl⟩ : syracuseStep 3179483 = 4769225) B4769225
theorem B1786855 : Blo 1411525 1786855 := bstep (se 1 (by rfl) ⟨1340141, by rfl⟩ : syracuseStep 1786855 = 2680283) B2680283
theorem B6112381 : Blo 1411525 6112381 := bstep (se 3 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 6112381 = 2292143) B2292143
theorem B3179663 : Blo 1411525 3179663 := bstep (se 1 (by rfl) ⟨2384747, by rfl⟩ : syracuseStep 3179663 = 4769495) B4769495
theorem B7152785 : Blo 1411525 7152785 := bstep (se 2 (by rfl) ⟨2682294, by rfl⟩ : syracuseStep 7152785 = 5364589) B5364589
theorem B6030551 : Blo 1411525 6030551 := bstep (se 1 (by rfl) ⟨4522913, by rfl⟩ : syracuseStep 6030551 = 9045827) B9045827
theorem B1696987 : Blo 1411525 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B3179753 : Blo 1411525 3179753 := bstep (se 2 (by rfl) ⟨1192407, by rfl⟩ : syracuseStep 3179753 = 2384815) B2384815
theorem B3179807 : Blo 1411525 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B3573031 : Blo 1411525 3573031 := bstep (se 1 (by rfl) ⟨2679773, by rfl⟩ : syracuseStep 3573031 = 5359547) B5359547
theorem B4769063 : Blo 1411525 4769063 := bstep (se 1 (by rfl) ⟨3576797, by rfl⟩ : syracuseStep 4769063 = 7153595) B7153595
theorem B3573305 : Blo 1411525 3573305 := bstep (se 2 (by rfl) ⟨1339989, by rfl⟩ : syracuseStep 3573305 = 2679979) B2679979
theorem B3180329 : Blo 1411525 3180329 := bstep (se 2 (by rfl) ⟨1192623, by rfl⟩ : syracuseStep 3180329 = 2385247) B2385247
theorem B125617985 : Blo 1411525 125617985 := bstep (se 2 (by rfl) ⟨47106744, by rfl⟩ : syracuseStep 125617985 = 94213489) B94213489
theorem B20358989 : Blo 1411525 20358989 := bstep (se 3 (by rfl) ⟨3817310, by rfl⟩ : syracuseStep 20358989 = 7634621) B7634621
theorem B4769927 : Blo 1411525 4769927 := bstep (se 1 (by rfl) ⟨3577445, by rfl⟩ : syracuseStep 4769927 = 7154891) B7154891
theorem B16083197 : Blo 1411525 16083197 := bstep (se 3 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 16083197 = 6031199) B6031199
theorem B2681255 : Blo 1411525 2681255 := bstep (se 1 (by rfl) ⟨2010941, by rfl⟩ : syracuseStep 2681255 = 4021883) B4021883
theorem B1411579 : Blo 1411525 1411579 := bstep (se 1 (by rfl) ⟨1058684, by rfl⟩ : syracuseStep 1411579 = 2117369) B2117369
theorem B6031867 : Blo 1411525 6031867 := bstep (se 1 (by rfl) ⟨4523900, by rfl⟩ : syracuseStep 6031867 = 9047801) B9047801
theorem B1411647 : Blo 1411525 1411647 := bstep (se 1 (by rfl) ⟨1058735, by rfl⟩ : syracuseStep 1411647 = 2117471) B2117471
theorem B2861639 : Blo 1411525 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B1411655 : Blo 1411525 1411655 := bstep (se 1 (by rfl) ⟨1058741, by rfl⟩ : syracuseStep 1411655 = 2117483) B2117483
theorem B5360201 : Blo 1411525 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B1411807 : Blo 1411525 1411807 := bstep (se 1 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 1411807 = 2117711) B2117711
theorem B5090039 : Blo 1411525 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B1411887 : Blo 1411525 1411887 := bstep (se 1 (by rfl) ⟨1058915, by rfl⟩ : syracuseStep 1411887 = 2117831) B2117831
theorem B6974351 : Blo 1411525 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B25783193 : Blo 1411525 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B1411995 : Blo 1411525 1411995 := bstep (se 1 (by rfl) ⟨1058996, by rfl⟩ : syracuseStep 1411995 = 2117993) B2117993
theorem B1412047 : Blo 1411525 1412047 := bstep (se 1 (by rfl) ⟨1059035, by rfl⟩ : syracuseStep 1412047 = 2118071) B2118071
theorem B3058651 : Blo 1411525 3058651 := bstep (se 1 (by rfl) ⟨2293988, by rfl⟩ : syracuseStep 3058651 = 4587977) B4587977
theorem B1412071 : Blo 1411525 1412071 := bstep (se 1 (by rfl) ⟨1059053, by rfl⟩ : syracuseStep 1412071 = 2118107) B2118107
theorem B36203597 : Blo 1411525 36203597 := bstep (se 3 (by rfl) ⟨6788174, by rfl⟩ : syracuseStep 36203597 = 13576349) B13576349
theorem B6032465 : Blo 1411525 6032465 := bstep (se 2 (by rfl) ⟨2262174, by rfl⟩ : syracuseStep 6032465 = 4524349) B4524349
theorem B3624059 : Blo 1411525 3624059 := bstep (se 1 (by rfl) ⟨2718044, by rfl⟩ : syracuseStep 3624059 = 5436089) B5436089
theorem B1412383 : Blo 1411525 1412383 := bstep (se 1 (by rfl) ⟨1059287, by rfl⟩ : syracuseStep 1412383 = 2118575) B2118575
theorem B2682143 : Blo 1411525 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B1412443 : Blo 1411525 1412443 := bstep (se 1 (by rfl) ⟨1059332, by rfl⟩ : syracuseStep 1412443 = 2118665) B2118665
theorem B3575137 : Blo 1411525 3575137 := bstep (se 2 (by rfl) ⟨1340676, by rfl⟩ : syracuseStep 3575137 = 2681353) B2681353
theorem B1412463 : Blo 1411525 1412463 := bstep (se 1 (by rfl) ⟨1059347, by rfl⟩ : syracuseStep 1412463 = 2118695) B2118695
theorem B1412519 : Blo 1411525 1412519 := bstep (se 1 (by rfl) ⟨1059389, by rfl⟩ : syracuseStep 1412519 = 2118779) B2118779
theorem B1412603 : Blo 1411525 1412603 := bstep (se 1 (by rfl) ⟨1059452, by rfl⟩ : syracuseStep 1412603 = 2118905) B2118905
theorem B7155215 : Blo 1411525 7155215 := bstep (se 1 (by rfl) ⟨5366411, by rfl⟩ : syracuseStep 7155215 = 10732823) B10732823
theorem B1412671 : Blo 1411525 1412671 := bstep (se 1 (by rfl) ⟨1059503, by rfl⟩ : syracuseStep 1412671 = 2119007) B2119007
theorem B1412679 : Blo 1411525 1412679 := bstep (se 1 (by rfl) ⟨1059509, by rfl⟩ : syracuseStep 1412679 = 2119019) B2119019
theorem B1412831 : Blo 1411525 1412831 := bstep (se 1 (by rfl) ⟨1059623, by rfl⟩ : syracuseStep 1412831 = 2119247) B2119247
theorem B2117417 : Blo 1411525 2117417 := bstep (se 2 (by rfl) ⟨794031, by rfl⟩ : syracuseStep 2117417 = 1588063) B1588063
theorem B2117423 : Blo 1411525 2117423 := bstep (se 1 (by rfl) ⟨1588067, by rfl⟩ : syracuseStep 2117423 = 3176135) B3176135
theorem B1412911 : Blo 1411525 1412911 := bstep (se 1 (by rfl) ⟨1059683, by rfl⟩ : syracuseStep 1412911 = 2119367) B2119367
theorem B1413019 : Blo 1411525 1413019 := bstep (se 1 (by rfl) ⟨1059764, by rfl⟩ : syracuseStep 1413019 = 2119529) B2119529
theorem B7147439 : Blo 1411525 7147439 := bstep (se 1 (by rfl) ⟨5360579, by rfl⟩ : syracuseStep 7147439 = 10721159) B10721159
theorem B1413071 : Blo 1411525 1413071 := bstep (se 1 (by rfl) ⟨1059803, by rfl⟩ : syracuseStep 1413071 = 2119607) B2119607
theorem B1413095 : Blo 1411525 1413095 := bstep (se 1 (by rfl) ⟨1059821, by rfl⟩ : syracuseStep 1413095 = 2119643) B2119643
theorem B5361673 : Blo 1411525 5361673 := bstep (se 2 (by rfl) ⟨2010627, by rfl⟩ : syracuseStep 5361673 = 4021255) B4021255
theorem B6787081 : Blo 1411525 6787081 := bstep (se 2 (by rfl) ⟨2545155, by rfl⟩ : syracuseStep 6787081 = 5090311) B5090311
theorem B14495915 : Blo 1411525 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B2117897 : Blo 1411525 2117897 := bstep (se 2 (by rfl) ⟨794211, by rfl⟩ : syracuseStep 2117897 = 1588423) B1588423
theorem B2683145 : Blo 1411525 2683145 := bstep (se 2 (by rfl) ⟨1006179, by rfl⟩ : syracuseStep 2683145 = 2012359) B2012359
theorem B3576089 : Blo 1411525 3576089 := bstep (se 2 (by rfl) ⟨1341033, by rfl⟩ : syracuseStep 3576089 = 2682067) B2682067
theorem B1413407 : Blo 1411525 1413407 := bstep (se 1 (by rfl) ⟨1060055, by rfl⟩ : syracuseStep 1413407 = 2120111) B2120111
theorem B1610023 : Blo 1411525 1610023 := bstep (se 1 (by rfl) ⟨1207517, by rfl⟩ : syracuseStep 1610023 = 2415035) B2415035
theorem B1413467 : Blo 1411525 1413467 := bstep (se 1 (by rfl) ⟨1060100, by rfl⟩ : syracuseStep 1413467 = 2120201) B2120201
theorem B29004131 : Blo 1411525 29004131 := bstep (se 1 (by rfl) ⟨21753098, by rfl⟩ : syracuseStep 29004131 = 43506197) B43506197
theorem B2117999 : Blo 1411525 2117999 := bstep (se 1 (by rfl) ⟨1588499, by rfl⟩ : syracuseStep 2117999 = 3176999) B3176999
theorem B1413487 : Blo 1411525 1413487 := bstep (se 1 (by rfl) ⟨1060115, by rfl⟩ : syracuseStep 1413487 = 2120231) B2120231
theorem B8049071 : Blo 1411525 8049071 := bstep (se 1 (by rfl) ⟨6036803, by rfl⟩ : syracuseStep 8049071 = 12073607) B12073607
theorem B6033865 : Blo 1411525 6033865 := bstep (se 2 (by rfl) ⟨2262699, by rfl⟩ : syracuseStep 6033865 = 4525399) B4525399
theorem B5362145 : Blo 1411525 5362145 := bstep (se 2 (by rfl) ⟨2010804, by rfl⟩ : syracuseStep 5362145 = 4021609) B4021609
theorem B3576383 : Blo 1411525 3576383 := bstep (se 1 (by rfl) ⟨2682287, by rfl⟩ : syracuseStep 3576383 = 5364575) B5364575
theorem B2118215 : Blo 1411525 2118215 := bstep (se 1 (by rfl) ⟨1588661, by rfl⟩ : syracuseStep 2118215 = 3177323) B3177323
theorem B11457121 : Blo 1411525 11457121 := bstep (se 2 (by rfl) ⟨4296420, by rfl⟩ : syracuseStep 11457121 = 8592841) B8592841
theorem B2118251 : Blo 1411525 2118251 := bstep (se 1 (by rfl) ⟨1588688, by rfl⟩ : syracuseStep 2118251 = 3177377) B3177377
theorem B3486329 : Blo 1411525 3486329 := bstep (se 2 (by rfl) ⟨1307373, by rfl⟩ : syracuseStep 3486329 = 2614747) B2614747
theorem B7738001 : Blo 1411525 7738001 := bstep (se 2 (by rfl) ⟨2901750, by rfl⟩ : syracuseStep 7738001 = 5803501) B5803501
theorem B3576595 : Blo 1411525 3576595 := bstep (se 1 (by rfl) ⟨2682446, by rfl⟩ : syracuseStep 3576595 = 5364893) B5364893
theorem B2118479 : Blo 1411525 2118479 := bstep (se 1 (by rfl) ⟨1588859, by rfl⟩ : syracuseStep 2118479 = 3177719) B3177719
theorem B38679403 : Blo 1411525 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B4764635 : Blo 1411525 4764635 := bstep (se 1 (by rfl) ⟨3573476, by rfl⟩ : syracuseStep 4764635 = 7146953) B7146953
theorem B8041463 : Blo 1411525 8041463 := bstep (se 1 (by rfl) ⟨6031097, by rfl⟩ : syracuseStep 8041463 = 12062195) B12062195
theorem B15275087 : Blo 1411525 15275087 := bstep (se 1 (by rfl) ⟨11456315, by rfl⟩ : syracuseStep 15275087 = 22912631) B22912631
theorem B4764797 : Blo 1411525 4764797 := bstep (se 3 (by rfl) ⟨893399, by rfl⟩ : syracuseStep 4764797 = 1786799) B1786799
theorem B7844989 : Blo 1411525 7844989 := bstep (se 3 (by rfl) ⟨1470935, by rfl⟩ : syracuseStep 7844989 = 2941871) B2941871
theorem B3577031 : Blo 1411525 3577031 := bstep (se 1 (by rfl) ⟨2682773, by rfl⟩ : syracuseStep 3577031 = 5365547) B5365547
theorem B2118875 : Blo 1411525 2118875 := bstep (se 1 (by rfl) ⟨1589156, by rfl⟩ : syracuseStep 2118875 = 3178313) B3178313
theorem B4764905 : Blo 1411525 4764905 := bstep (se 2 (by rfl) ⟨1786839, by rfl⟩ : syracuseStep 4764905 = 3573679) B3573679
theorem B3577081 : Blo 1411525 3577081 := bstep (se 2 (by rfl) ⟨1341405, by rfl⟩ : syracuseStep 3577081 = 2682811) B2682811
theorem B15267167 : Blo 1411525 15267167 := bstep (se 1 (by rfl) ⟨11450375, by rfl⟩ : syracuseStep 15267167 = 22900751) B22900751
theorem B2119049 : Blo 1411525 2119049 := bstep (se 2 (by rfl) ⟨794643, by rfl⟩ : syracuseStep 2119049 = 1589287) B1589287
theorem B4765067 : Blo 1411525 4765067 := bstep (se 1 (by rfl) ⟨3573800, by rfl⟩ : syracuseStep 4765067 = 7147601) B7147601
theorem B5658017 : Blo 1411525 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B10720673 : Blo 1411525 10720673 := bstep (se 2 (by rfl) ⟨4020252, by rfl⟩ : syracuseStep 10720673 = 8040505) B8040505
theorem B6034925 : Blo 1411525 6034925 := bstep (se 3 (by rfl) ⟨1131548, by rfl⟩ : syracuseStep 6034925 = 2263097) B2263097
theorem B173930165 : Blo 1411525 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B45831865 : Blo 1411525 45831865 := bstep (se 2 (by rfl) ⟨17186949, by rfl⟩ : syracuseStep 45831865 = 34373899) B34373899
theorem B3176171 : Blo 1411525 3176171 := bstep (se 1 (by rfl) ⟨2382128, by rfl⟩ : syracuseStep 3176171 = 4764257) B4764257
theorem B2119403 : Blo 1411525 2119403 := bstep (se 1 (by rfl) ⟨1589552, by rfl⟩ : syracuseStep 2119403 = 3179105) B3179105
theorem B24131357 : Blo 1411525 24131357 := bstep (se 3 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 24131357 = 9049259) B9049259
theorem B3176297 : Blo 1411525 3176297 := bstep (se 2 (by rfl) ⟨1191111, by rfl⟩ : syracuseStep 3176297 = 2382223) B2382223
theorem B3577729 : Blo 1411525 3577729 := bstep (se 2 (by rfl) ⟨1341648, by rfl⟩ : syracuseStep 3577729 = 2683297) B2683297
theorem B2119631 : Blo 1411525 2119631 := bstep (se 1 (by rfl) ⟨1589723, by rfl⟩ : syracuseStep 2119631 = 3179447) B3179447
theorem B11024417 : Blo 1411525 11024417 := bstep (se 2 (by rfl) ⟨4134156, by rfl⟩ : syracuseStep 11024417 = 8268313) B8268313
theorem B2545769 : Blo 1411525 2545769 := bstep (se 2 (by rfl) ⟨954663, by rfl⟩ : syracuseStep 2545769 = 1909327) B1909327
theorem B36190475 : Blo 1411525 36190475 := bstep (se 1 (by rfl) ⟨27142856, by rfl⟩ : syracuseStep 36190475 = 54285713) B54285713
theorem B2120027 : Blo 1411525 2120027 := bstep (se 1 (by rfl) ⟨1590020, by rfl⟩ : syracuseStep 2120027 = 3180041) B3180041
theorem B2382331 : Blo 1411525 2382331 := bstep (se 1 (by rfl) ⟨1786748, by rfl⟩ : syracuseStep 2382331 = 3573497) B3573497
theorem B2120255 : Blo 1411525 2120255 := bstep (se 1 (by rfl) ⟨1590191, by rfl⟩ : syracuseStep 2120255 = 3180383) B3180383
theorem B3177143 : Blo 1411525 3177143 := bstep (se 1 (by rfl) ⟨2382857, by rfl⟩ : syracuseStep 3177143 = 4765715) B4765715
theorem B7150355 : Blo 1411525 7150355 := bstep (se 1 (by rfl) ⟨5362766, by rfl⟩ : syracuseStep 7150355 = 10725533) B10725533
theorem B3177359 : Blo 1411525 3177359 := bstep (se 1 (by rfl) ⟨2383019, by rfl⟩ : syracuseStep 3177359 = 4766039) B4766039
theorem B2382763 : Blo 1411525 2382763 := bstep (se 1 (by rfl) ⟨1787072, by rfl⟩ : syracuseStep 2382763 = 3574145) B3574145
theorem B2383067 : Blo 1411525 2383067 := bstep (se 1 (by rfl) ⟨1787300, by rfl⟩ : syracuseStep 2383067 = 3574601) B3574601
theorem B2546921 : Blo 1411525 2546921 := bstep (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) B1910191
theorem B1588603 : Blo 1411525 1588603 := bstep (se 1 (by rfl) ⟨1191452, by rfl⟩ : syracuseStep 1588603 = 2382905) B2382905
theorem B2383303 : Blo 1411525 2383303 := bstep (se 1 (by rfl) ⟨1787477, by rfl⟩ : syracuseStep 2383303 = 3574955) B3574955
theorem B9666071 : Blo 1411525 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B3178079 : Blo 1411525 3178079 := bstep (se 1 (by rfl) ⟨2383559, by rfl⟩ : syracuseStep 3178079 = 4767119) B4767119
theorem B32603795 : Blo 1411525 32603795 := bstep (se 1 (by rfl) ⟨24452846, by rfl⟩ : syracuseStep 32603795 = 48905693) B48905693
theorem B6446753 : Blo 1411525 6446753 := bstep (se 2 (by rfl) ⟨2417532, by rfl⟩ : syracuseStep 6446753 = 4835065) B4835065
theorem B3178295 : Blo 1411525 3178295 := bstep (se 1 (by rfl) ⟨2383721, by rfl⟩ : syracuseStep 3178295 = 4767443) B4767443
theorem B5365561 : Blo 1411525 5365561 := bstep (se 2 (by rfl) ⟨2012085, by rfl⟩ : syracuseStep 5365561 = 4024171) B4024171
theorem B6790985 : Blo 1411525 6790985 := bstep (se 2 (by rfl) ⟨2546619, by rfl⟩ : syracuseStep 6790985 = 5093239) B5093239
theorem B1589071 : Blo 1411525 1589071 := bstep (se 1 (by rfl) ⟨1191803, by rfl⟩ : syracuseStep 1589071 = 2383607) B2383607
theorem B418234211 : Blo 1411525 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B7151489 : Blo 1411525 7151489 := bstep (se 2 (by rfl) ⟨2681808, by rfl⟩ : syracuseStep 7151489 = 5363617) B5363617
theorem B3440513 : Blo 1411525 3440513 := bstep (se 2 (by rfl) ⟨1290192, by rfl⟩ : syracuseStep 3440513 = 2580385) B2580385
theorem B2383823 : Blo 1411525 2383823 := bstep (se 1 (by rfl) ⟨1787867, by rfl⟩ : syracuseStep 2383823 = 3575735) B3575735
theorem B2384059 : Blo 1411525 2384059 := bstep (se 1 (by rfl) ⟨1788044, by rfl⟩ : syracuseStep 2384059 = 3576089) B3576089
theorem B3178727 : Blo 1411525 3178727 := bstep (se 1 (by rfl) ⟨2384045, by rfl⟩ : syracuseStep 3178727 = 4768091) B4768091
theorem B5366047 : Blo 1411525 5366047 := bstep (se 1 (by rfl) ⟨4024535, by rfl⟩ : syracuseStep 5366047 = 8049071) B8049071
theorem B2384255 : Blo 1411525 2384255 := bstep (se 1 (by rfl) ⟨1788191, by rfl⟩ : syracuseStep 2384255 = 3576383) B3576383
theorem B2146697 : Blo 1411525 2146697 := bstep (se 2 (by rfl) ⟨805011, by rfl⟩ : syracuseStep 2146697 = 1610023) B1610023
theorem B4768199 : Blo 1411525 4768199 := bstep (se 1 (by rfl) ⟨3576149, by rfl⟩ : syracuseStep 4768199 = 7152299) B7152299
theorem B12239423 : Blo 1411525 12239423 := bstep (se 1 (by rfl) ⟨9179567, by rfl⟩ : syracuseStep 12239423 = 18359135) B18359135
theorem B8045153 : Blo 1411525 8045153 := bstep (se 2 (by rfl) ⟨3016932, by rfl⟩ : syracuseStep 8045153 = 6033865) B6033865
theorem B1589863 : Blo 1411525 1589863 := bstep (se 1 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 1589863 = 2384795) B2384795
theorem B6791789 : Blo 1411525 6791789 := bstep (se 3 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 6791789 = 2546921) B2546921
theorem B10183391 : Blo 1411525 10183391 := bstep (se 1 (by rfl) ⟨7637543, by rfl⟩ : syracuseStep 10183391 = 15275087) B15275087
theorem B4768523 : Blo 1411525 4768523 := bstep (se 1 (by rfl) ⟨3576392, by rfl⟩ : syracuseStep 4768523 = 7152785) B7152785
theorem B2384687 : Blo 1411525 2384687 := bstep (se 1 (by rfl) ⟨1788515, by rfl⟩ : syracuseStep 2384687 = 3577031) B3577031
theorem B3015481 : Blo 1411525 3015481 := bstep (se 2 (by rfl) ⟨1130805, by rfl⟩ : syracuseStep 3015481 = 2261611) B2261611
theorem B3179321 : Blo 1411525 3179321 := bstep (se 2 (by rfl) ⟨1192245, by rfl⟩ : syracuseStep 3179321 = 2384491) B2384491
theorem B3179375 : Blo 1411525 3179375 := bstep (se 1 (by rfl) ⟨2384531, by rfl⟩ : syracuseStep 3179375 = 4769063) B4769063
theorem B4023283 : Blo 1411525 4023283 := bstep (se 1 (by rfl) ⟨3017462, by rfl⟩ : syracuseStep 4023283 = 6034925) B6034925
theorem B4768793 : Blo 1411525 4768793 := bstep (se 2 (by rfl) ⟨1788297, by rfl⟩ : syracuseStep 4768793 = 3576595) B3576595
theorem B1697179 : Blo 1411525 1697179 := bstep (se 1 (by rfl) ⟨1272884, by rfl⟩ : syracuseStep 1697179 = 2545769) B2545769
theorem B3179951 : Blo 1411525 3179951 := bstep (se 1 (by rfl) ⟨2384963, by rfl⟩ : syracuseStep 3179951 = 4769927) B4769927
theorem B24126983 : Blo 1411525 24126983 := bstep (se 1 (by rfl) ⟨18095237, by rfl⟩ : syracuseStep 24126983 = 36190475) B36190475
theorem B1787503 : Blo 1411525 1787503 := bstep (se 1 (by rfl) ⟨1340627, by rfl⟩ : syracuseStep 1787503 = 2681255) B2681255
theorem B2262649 : Blo 1411525 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B4769441 : Blo 1411525 4769441 := bstep (se 2 (by rfl) ⟨1788540, by rfl⟩ : syracuseStep 4769441 = 3577081) B3577081
theorem B3573467 : Blo 1411525 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B3393359 : Blo 1411525 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B17188795 : Blo 1411525 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B24135731 : Blo 1411525 24135731 := bstep (se 1 (by rfl) ⟨18101798, by rfl⟩ : syracuseStep 24135731 = 36203597) B36203597
theorem B1788095 : Blo 1411525 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B4770143 : Blo 1411525 4770143 := bstep (se 1 (by rfl) ⟨3577607, by rfl⟩ : syracuseStep 4770143 = 7155215) B7155215
theorem B7154081 : Blo 1411525 7154081 := bstep (se 2 (by rfl) ⟨2682780, by rfl⟩ : syracuseStep 7154081 = 5365561) B5365561
theorem B21735863 : Blo 1411525 21735863 := bstep (se 1 (by rfl) ⟨16301897, by rfl⟩ : syracuseStep 21735863 = 32603795) B32603795
theorem B4770305 : Blo 1411525 4770305 := bstep (se 2 (by rfl) ⟨1788864, by rfl⟩ : syracuseStep 4770305 = 3577729) B3577729
theorem B1411611 : Blo 1411525 1411611 := bstep (se 1 (by rfl) ⟨1058708, by rfl⟩ : syracuseStep 1411611 = 2117417) B2117417
theorem B1411615 : Blo 1411525 1411615 := bstep (se 1 (by rfl) ⟨1058711, by rfl⟩ : syracuseStep 1411615 = 2117423) B2117423
theorem B4025015 : Blo 1411525 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B5089979 : Blo 1411525 5089979 := bstep (se 1 (by rfl) ⟨3817484, by rfl⟩ : syracuseStep 5089979 = 7634969) B7634969
theorem B1411931 : Blo 1411525 1411931 := bstep (se 1 (by rfl) ⟨1058948, by rfl⟩ : syracuseStep 1411931 = 2117897) B2117897
theorem B19336087 : Blo 1411525 19336087 := bstep (se 1 (by rfl) ⟨14502065, by rfl⟩ : syracuseStep 19336087 = 29004131) B29004131
theorem B1411999 : Blo 1411525 1411999 := bstep (se 1 (by rfl) ⟨1058999, by rfl⟩ : syracuseStep 1411999 = 2117999) B2117999
theorem B99167203 : Blo 1411525 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B3574763 : Blo 1411525 3574763 := bstep (se 1 (by rfl) ⟨2681072, by rfl⟩ : syracuseStep 3574763 = 5362145) B5362145
theorem B1412143 : Blo 1411525 1412143 := bstep (se 1 (by rfl) ⟨1059107, by rfl⟩ : syracuseStep 1412143 = 2118215) B2118215
theorem B1412167 : Blo 1411525 1412167 := bstep (se 1 (by rfl) ⟨1059125, by rfl⟩ : syracuseStep 1412167 = 2118251) B2118251
theorem B1412319 : Blo 1411525 1412319 := bstep (se 1 (by rfl) ⟨1059239, by rfl⟩ : syracuseStep 1412319 = 2118479) B2118479
theorem B2010377 : Blo 1411525 2010377 := bstep (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) B1507783
theorem B5360975 : Blo 1411525 5360975 := bstep (se 1 (by rfl) ⟨4020731, by rfl⟩ : syracuseStep 5360975 = 8041463) B8041463
theorem B7155053 : Blo 1411525 7155053 := bstep (se 3 (by rfl) ⟨1341572, by rfl⟩ : syracuseStep 7155053 = 2683145) B2683145
theorem B1412583 : Blo 1411525 1412583 := bstep (se 1 (by rfl) ⟨1059437, by rfl⟩ : syracuseStep 1412583 = 2118875) B2118875
theorem B10178111 : Blo 1411525 10178111 := bstep (se 1 (by rfl) ⟨7633583, by rfl⟩ : syracuseStep 10178111 = 15267167) B15267167
theorem B1412699 : Blo 1411525 1412699 := bstep (se 1 (by rfl) ⟨1059524, by rfl⟩ : syracuseStep 1412699 = 2119049) B2119049
theorem B7147115 : Blo 1411525 7147115 := bstep (se 1 (by rfl) ⟨5360336, by rfl⟩ : syracuseStep 7147115 = 10720673) B10720673
theorem B115953443 : Blo 1411525 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B51572537 : Blo 1411525 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B2117447 : Blo 1411525 2117447 := bstep (se 1 (by rfl) ⟨1588085, by rfl⟩ : syracuseStep 2117447 = 3176171) B3176171
theorem B1412935 : Blo 1411525 1412935 := bstep (se 1 (by rfl) ⟨1059701, by rfl⟩ : syracuseStep 1412935 = 2119403) B2119403
theorem B2117531 : Blo 1411525 2117531 := bstep (se 1 (by rfl) ⟨1588148, by rfl⟩ : syracuseStep 2117531 = 3176297) B3176297
theorem B1413087 : Blo 1411525 1413087 := bstep (se 1 (by rfl) ⟨1059815, by rfl⟩ : syracuseStep 1413087 = 2119631) B2119631
theorem B1413351 : Blo 1411525 1413351 := bstep (se 1 (by rfl) ⟨1060013, by rfl⟩ : syracuseStep 1413351 = 2120027) B2120027
theorem B4763933 : Blo 1411525 4763933 := bstep (se 3 (by rfl) ⟨893237, by rfl⟩ : syracuseStep 4763933 = 1786475) B1786475
theorem B1413503 : Blo 1411525 1413503 := bstep (se 1 (by rfl) ⟨1060127, by rfl⟩ : syracuseStep 1413503 = 2120255) B2120255
theorem B4764041 : Blo 1411525 4764041 := bstep (se 2 (by rfl) ⟨1786515, by rfl⟩ : syracuseStep 4764041 = 3573031) B3573031
theorem B2118095 : Blo 1411525 2118095 := bstep (se 1 (by rfl) ⟨1588571, by rfl⟩ : syracuseStep 2118095 = 3177143) B3177143
theorem B2118137 : Blo 1411525 2118137 := bstep (se 2 (by rfl) ⟨794301, by rfl⟩ : syracuseStep 2118137 = 1588603) B1588603
theorem B2118239 : Blo 1411525 2118239 := bstep (se 1 (by rfl) ⟨1588679, by rfl⟩ : syracuseStep 2118239 = 3177359) B3177359
theorem B4649567 : Blo 1411525 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B61109153 : Blo 1411525 61109153 := bstep (se 2 (by rfl) ⟨22915932, by rfl⟩ : syracuseStep 61109153 = 45831865) B45831865
theorem B6444047 : Blo 1411525 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B2118719 : Blo 1411525 2118719 := bstep (se 1 (by rfl) ⟨1589039, by rfl⟩ : syracuseStep 2118719 = 3178079) B3178079
theorem B2118761 : Blo 1411525 2118761 := bstep (se 2 (by rfl) ⟨794535, by rfl⟩ : syracuseStep 2118761 = 1589071) B1589071
theorem B4297835 : Blo 1411525 4297835 := bstep (se 1 (by rfl) ⟨3223376, by rfl⟩ : syracuseStep 4297835 = 6446753) B6446753
theorem B2118863 : Blo 1411525 2118863 := bstep (se 1 (by rfl) ⟨1589147, by rfl⟩ : syracuseStep 2118863 = 3178295) B3178295
theorem B4527323 : Blo 1411525 4527323 := bstep (se 1 (by rfl) ⟨3395492, by rfl⟩ : syracuseStep 4527323 = 6790985) B6790985
theorem B167359765 : Blo 1411525 167359765 := bstep (se 6 (by rfl) ⟨3922494, by rfl⟩ : syracuseStep 167359765 = 7844989) B7844989
theorem B4764959 : Blo 1411525 4764959 := bstep (se 1 (by rfl) ⟨3573719, by rfl⟩ : syracuseStep 4764959 = 7147439) B7147439
theorem B7148897 : Blo 1411525 7148897 := bstep (se 2 (by rfl) ⟨2680836, by rfl⟩ : syracuseStep 7148897 = 5361673) B5361673
theorem B9049441 : Blo 1411525 9049441 := bstep (se 2 (by rfl) ⟨3393540, by rfl⟩ : syracuseStep 9049441 = 6787081) B6787081
theorem B2119067 : Blo 1411525 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B3577243 : Blo 1411525 3577243 := bstep (se 1 (by rfl) ⟨2682932, by rfl⟩ : syracuseStep 3577243 = 5365865) B5365865
theorem B29398445 : Blo 1411525 29398445 := bstep (se 3 (by rfl) ⟨5512208, by rfl⟩ : syracuseStep 29398445 = 11024417) B11024417
theorem B5363131 : Blo 1411525 5363131 := bstep (se 1 (by rfl) ⟨4022348, by rfl⟩ : syracuseStep 5363131 = 8044697) B8044697
theorem B9663943 : Blo 1411525 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B2119289 : Blo 1411525 2119289 := bstep (se 2 (by rfl) ⟨794733, by rfl⟩ : syracuseStep 2119289 = 1589467) B1589467
theorem B9664157 : Blo 1411525 9664157 := bstep (se 3 (by rfl) ⟨1812029, by rfl⟩ : syracuseStep 9664157 = 3624059) B3624059
theorem B2119391 : Blo 1411525 2119391 := bstep (se 1 (by rfl) ⟨1589543, by rfl⟩ : syracuseStep 2119391 = 3179087) B3179087
theorem B2324219 : Blo 1411525 2324219 := bstep (se 1 (by rfl) ⟨1743164, by rfl⟩ : syracuseStep 2324219 = 3486329) B3486329
theorem B5158667 : Blo 1411525 5158667 := bstep (se 1 (by rfl) ⟨3869000, by rfl⟩ : syracuseStep 5158667 = 7738001) B7738001
theorem B4020025 : Blo 1411525 4020025 := bstep (se 2 (by rfl) ⟨1507509, by rfl⟩ : syracuseStep 4020025 = 3015019) B3015019
theorem B2119487 : Blo 1411525 2119487 := bstep (se 1 (by rfl) ⟨1589615, by rfl⟩ : syracuseStep 2119487 = 3179231) B3179231
theorem B16078823 : Blo 1411525 16078823 := bstep (se 1 (by rfl) ⟨12059117, by rfl⟩ : syracuseStep 16078823 = 24118235) B24118235
theorem B3176423 : Blo 1411525 3176423 := bstep (se 1 (by rfl) ⟨2382317, by rfl⟩ : syracuseStep 3176423 = 4764635) B4764635
theorem B2119655 : Blo 1411525 2119655 := bstep (se 1 (by rfl) ⟨1589741, by rfl⟩ : syracuseStep 2119655 = 3179483) B3179483
theorem B8042489 : Blo 1411525 8042489 := bstep (se 2 (by rfl) ⟨3015933, by rfl⟩ : syracuseStep 8042489 = 6031867) B6031867
theorem B3176441 : Blo 1411525 3176441 := bstep (se 2 (by rfl) ⟨1191165, by rfl⟩ : syracuseStep 3176441 = 2382331) B2382331
theorem B2119673 : Blo 1411525 2119673 := bstep (se 2 (by rfl) ⟨794877, by rfl⟩ : syracuseStep 2119673 = 1589755) B1589755
theorem B3176531 : Blo 1411525 3176531 := bstep (se 1 (by rfl) ⟨2382398, by rfl⟩ : syracuseStep 3176531 = 4764797) B4764797
theorem B2119775 : Blo 1411525 2119775 := bstep (se 1 (by rfl) ⟨1589831, by rfl⟩ : syracuseStep 2119775 = 3179663) B3179663
theorem B15276161 : Blo 1411525 15276161 := bstep (se 2 (by rfl) ⟨5728560, by rfl⟩ : syracuseStep 15276161 = 11457121) B11457121
theorem B4020367 : Blo 1411525 4020367 := bstep (se 1 (by rfl) ⟨3015275, by rfl⟩ : syracuseStep 4020367 = 6030551) B6030551
theorem B3176603 : Blo 1411525 3176603 := bstep (se 1 (by rfl) ⟨2382452, by rfl⟩ : syracuseStep 3176603 = 4764905) B4764905
theorem B2119835 : Blo 1411525 2119835 := bstep (se 1 (by rfl) ⟨1589876, by rfl⟩ : syracuseStep 2119835 = 3179753) B3179753
theorem B2119871 : Blo 1411525 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B2119913 : Blo 1411525 2119913 := bstep (se 2 (by rfl) ⟨794967, by rfl⟩ : syracuseStep 2119913 = 1589935) B1589935
theorem B3176711 : Blo 1411525 3176711 := bstep (se 1 (by rfl) ⟨2382533, by rfl⟩ : syracuseStep 3176711 = 4765067) B4765067
theorem B2382203 : Blo 1411525 2382203 := bstep (se 1 (by rfl) ⟨1786652, by rfl⟩ : syracuseStep 2382203 = 3573305) B3573305
theorem B15088045 : Blo 1411525 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B16087571 : Blo 1411525 16087571 := bstep (se 1 (by rfl) ⟨12065678, by rfl⟩ : syracuseStep 16087571 = 24131357) B24131357
theorem B2120219 : Blo 1411525 2120219 := bstep (se 1 (by rfl) ⟨1590164, by rfl⟩ : syracuseStep 2120219 = 3180329) B3180329
theorem B83745323 : Blo 1411525 83745323 := bstep (se 1 (by rfl) ⟨62808992, by rfl⟩ : syracuseStep 83745323 = 125617985) B125617985
theorem B13572659 : Blo 1411525 13572659 := bstep (se 1 (by rfl) ⟨10179494, by rfl⟩ : syracuseStep 13572659 = 20358989) B20358989
theorem B3177017 : Blo 1411525 3177017 := bstep (se 2 (by rfl) ⟨1191381, by rfl⟩ : syracuseStep 3177017 = 2382763) B2382763
theorem B4078201 : Blo 1411525 4078201 := bstep (se 2 (by rfl) ⟨1529325, by rfl⟩ : syracuseStep 4078201 = 3058651) B3058651
theorem B2382473 : Blo 1411525 2382473 := bstep (se 2 (by rfl) ⟨893427, by rfl⟩ : syracuseStep 2382473 = 1786855) B1786855
theorem B8149841 : Blo 1411525 8149841 := bstep (se 2 (by rfl) ⟨3056190, by rfl⟩ : syracuseStep 8149841 = 6112381) B6112381
theorem B10722131 : Blo 1411525 10722131 := bstep (se 1 (by rfl) ⟨8041598, by rfl⟩ : syracuseStep 10722131 = 16083197) B16083197
theorem B1907759 : Blo 1411525 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B4766849 : Blo 1411525 4766849 := bstep (se 2 (by rfl) ⟨1787568, by rfl⟩ : syracuseStep 4766849 = 3575137) B3575137
theorem B4766903 : Blo 1411525 4766903 := bstep (se 1 (by rfl) ⟨3575177, by rfl⟩ : syracuseStep 4766903 = 7150355) B7150355
theorem B3177737 : Blo 1411525 3177737 := bstep (se 2 (by rfl) ⟨1191651, by rfl⟩ : syracuseStep 3177737 = 2383303) B2383303
theorem B4021643 : Blo 1411525 4021643 := bstep (se 1 (by rfl) ⟨3016232, by rfl⟩ : syracuseStep 4021643 = 6032465) B6032465
theorem B1588711 : Blo 1411525 1588711 := bstep (se 1 (by rfl) ⟨1191533, by rfl⟩ : syracuseStep 1588711 = 2383067) B2383067
theorem B9174701 : Blo 1411525 9174701 := bstep (se 3 (by rfl) ⟨1720256, by rfl⟩ : syracuseStep 9174701 = 3440513) B3440513
theorem B278822807 : Blo 1411525 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B4767659 : Blo 1411525 4767659 := bstep (se 1 (by rfl) ⟨3575744, by rfl⟩ : syracuseStep 4767659 = 7151489) B7151489
theorem B1589215 : Blo 1411525 1589215 := bstep (se 1 (by rfl) ⟨1191911, by rfl⟩ : syracuseStep 1589215 = 2383823) B2383823
theorem B5087357 : Blo 1411525 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B3178745 : Blo 1411525 3178745 := bstep (se 2 (by rfl) ⟨1192029, by rfl⟩ : syracuseStep 3178745 = 2384059) B2384059
theorem B1589503 : Blo 1411525 1589503 := bstep (se 1 (by rfl) ⟨1192127, by rfl⟩ : syracuseStep 1589503 = 2384255) B2384255
theorem B3178799 : Blo 1411525 3178799 := bstep (se 1 (by rfl) ⟨2384099, by rfl⟩ : syracuseStep 3178799 = 4768199) B4768199
theorem B8159615 : Blo 1411525 8159615 := bstep (se 1 (by rfl) ⟨6119711, by rfl⟩ : syracuseStep 8159615 = 12239423) B12239423
theorem B4768253 : Blo 1411525 4768253 := bstep (se 3 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 4768253 = 1788095) B1788095
theorem B3179015 : Blo 1411525 3179015 := bstep (se 1 (by rfl) ⟨2384261, by rfl⟩ : syracuseStep 3179015 = 4768523) B4768523
theorem B1589791 : Blo 1411525 1589791 := bstep (se 1 (by rfl) ⟨1192343, by rfl⟩ : syracuseStep 1589791 = 2384687) B2384687
theorem B40739435 : Blo 1411525 40739435 := bstep (se 1 (by rfl) ⟨30554576, by rfl⟩ : syracuseStep 40739435 = 61109153) B61109153
theorem B3179195 : Blo 1411525 3179195 := bstep (se 1 (by rfl) ⟨2384396, by rfl⟩ : syracuseStep 3179195 = 4768793) B4768793
theorem B3179627 : Blo 1411525 3179627 := bstep (se 1 (by rfl) ⟨2384720, by rfl⟩ : syracuseStep 3179627 = 4769441) B4769441
theorem B25781449 : Blo 1411525 25781449 := bstep (se 2 (by rfl) ⟨9668043, by rfl⟩ : syracuseStep 25781449 = 19336087) B19336087
theorem B2262239 : Blo 1411525 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B16090487 : Blo 1411525 16090487 := bstep (se 1 (by rfl) ⟨12067865, by rfl⟩ : syracuseStep 16090487 = 24135731) B24135731
theorem B3180095 : Blo 1411525 3180095 := bstep (se 1 (by rfl) ⟨2385071, by rfl⟩ : syracuseStep 3180095 = 4770143) B4770143
theorem B4769387 : Blo 1411525 4769387 := bstep (se 1 (by rfl) ⟨3577040, by rfl⟩ : syracuseStep 4769387 = 7154081) B7154081
theorem B3180203 : Blo 1411525 3180203 := bstep (se 1 (by rfl) ⟨2385152, by rfl⟩ : syracuseStep 3180203 = 4770305) B4770305
theorem B10725047 : Blo 1411525 10725047 := bstep (se 1 (by rfl) ⟨8043785, by rfl⟩ : syracuseStep 10725047 = 16087571) B16087571
theorem B55830215 : Blo 1411525 55830215 := bstep (se 1 (by rfl) ⟨41872661, by rfl⟩ : syracuseStep 55830215 = 83745323) B83745323
theorem B3393319 : Blo 1411525 3393319 := bstep (se 1 (by rfl) ⟨2544989, by rfl⟩ : syracuseStep 3393319 = 5089979) B5089979
theorem B2262905 : Blo 1411525 2262905 := bstep (se 2 (by rfl) ⟨848589, by rfl⟩ : syracuseStep 2262905 = 1697179) B1697179
theorem B4769657 : Blo 1411525 4769657 := bstep (se 2 (by rfl) ⟨1788621, by rfl⟩ : syracuseStep 4769657 = 3577243) B3577243
theorem B5433227 : Blo 1411525 5433227 := bstep (se 1 (by rfl) ⟨4074920, by rfl⟩ : syracuseStep 5433227 = 8149841) B8149841
theorem B3016865 : Blo 1411525 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B3573983 : Blo 1411525 3573983 := bstep (se 1 (by rfl) ⟨2680487, by rfl⟩ : syracuseStep 3573983 = 5360975) B5360975
theorem B4770035 : Blo 1411525 4770035 := bstep (se 1 (by rfl) ⟨3577526, by rfl⟩ : syracuseStep 4770035 = 7155053) B7155053
theorem B2681095 : Blo 1411525 2681095 := bstep (se 1 (by rfl) ⟨2010821, by rfl⟩ : syracuseStep 2681095 = 4021643) B4021643
theorem B6785407 : Blo 1411525 6785407 := bstep (se 1 (by rfl) ⟨5089055, by rfl⟩ : syracuseStep 6785407 = 10178111) B10178111
theorem B5360033 : Blo 1411525 5360033 := bstep (se 2 (by rfl) ⟨2010012, by rfl⟩ : syracuseStep 5360033 = 4020025) B4020025
theorem B77302295 : Blo 1411525 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B1411631 : Blo 1411525 1411631 := bstep (se 1 (by rfl) ⟨1058723, by rfl⟩ : syracuseStep 1411631 = 2117447) B2117447
theorem B1411687 : Blo 1411525 1411687 := bstep (se 1 (by rfl) ⟨1058765, by rfl⟩ : syracuseStep 1411687 = 2117531) B2117531
theorem B5360489 : Blo 1411525 5360489 := bstep (se 2 (by rfl) ⟨2010183, by rfl⟩ : syracuseStep 5360489 = 4020367) B4020367
theorem B1412063 : Blo 1411525 1412063 := bstep (se 1 (by rfl) ⟨1059047, by rfl⟩ : syracuseStep 1412063 = 2118095) B2118095
theorem B1412091 : Blo 1411525 1412091 := bstep (se 1 (by rfl) ⟨1059068, by rfl⟩ : syracuseStep 1412091 = 2118137) B2118137
theorem B7154729 : Blo 1411525 7154729 := bstep (se 2 (by rfl) ⟨2683023, by rfl⟩ : syracuseStep 7154729 = 5366047) B5366047
theorem B1412159 : Blo 1411525 1412159 := bstep (se 1 (by rfl) ⟨1059119, by rfl⟩ : syracuseStep 1412159 = 2118239) B2118239
theorem B5361005 : Blo 1411525 5361005 := bstep (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) B2010377
theorem B1412479 : Blo 1411525 1412479 := bstep (se 1 (by rfl) ⟨1059359, by rfl⟩ : syracuseStep 1412479 = 2118719) B2118719
theorem B1412507 : Blo 1411525 1412507 := bstep (se 1 (by rfl) ⟨1059380, by rfl⟩ : syracuseStep 1412507 = 2118761) B2118761
theorem B1412575 : Blo 1411525 1412575 := bstep (se 1 (by rfl) ⟨1059431, by rfl⟩ : syracuseStep 1412575 = 2118863) B2118863
theorem B3018215 : Blo 1411525 3018215 := bstep (se 1 (by rfl) ⟨2263661, by rfl⟩ : syracuseStep 3018215 = 4527323) B4527323
theorem B1412711 : Blo 1411525 1412711 := bstep (se 1 (by rfl) ⟨1059533, by rfl⟩ : syracuseStep 1412711 = 2119067) B2119067
theorem B19598963 : Blo 1411525 19598963 := bstep (se 1 (by rfl) ⟨14699222, by rfl⟩ : syracuseStep 19598963 = 29398445) B29398445
theorem B16084655 : Blo 1411525 16084655 := bstep (se 1 (by rfl) ⟨12063491, by rfl⟩ : syracuseStep 16084655 = 24126983) B24126983
theorem B1412859 : Blo 1411525 1412859 := bstep (se 1 (by rfl) ⟨1059644, by rfl⟩ : syracuseStep 1412859 = 2119289) B2119289
theorem B1412927 : Blo 1411525 1412927 := bstep (se 1 (by rfl) ⟨1059695, by rfl⟩ : syracuseStep 1412927 = 2119391) B2119391
theorem B1412991 : Blo 1411525 1412991 := bstep (se 1 (by rfl) ⟨1059743, by rfl⟩ : syracuseStep 1412991 = 2119487) B2119487
theorem B132222937 : Blo 1411525 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B10719215 : Blo 1411525 10719215 := bstep (se 1 (by rfl) ⟨8039411, by rfl⟩ : syracuseStep 10719215 = 16078823) B16078823
theorem B2117615 : Blo 1411525 2117615 := bstep (se 1 (by rfl) ⟨1588211, by rfl⟩ : syracuseStep 2117615 = 3176423) B3176423
theorem B1413103 : Blo 1411525 1413103 := bstep (se 1 (by rfl) ⟨1059827, by rfl⟩ : syracuseStep 1413103 = 2119655) B2119655
theorem B5361659 : Blo 1411525 5361659 := bstep (se 1 (by rfl) ⟨4021244, by rfl⟩ : syracuseStep 5361659 = 8042489) B8042489
theorem B2117627 : Blo 1411525 2117627 := bstep (se 1 (by rfl) ⟨1588220, by rfl⟩ : syracuseStep 2117627 = 3176441) B3176441
theorem B1413115 : Blo 1411525 1413115 := bstep (se 1 (by rfl) ⟨1059836, by rfl⟩ : syracuseStep 1413115 = 2119673) B2119673
theorem B2117687 : Blo 1411525 2117687 := bstep (se 1 (by rfl) ⟨1588265, by rfl⟩ : syracuseStep 2117687 = 3176531) B3176531
theorem B1413183 : Blo 1411525 1413183 := bstep (se 1 (by rfl) ⟨1059887, by rfl⟩ : syracuseStep 1413183 = 2119775) B2119775
theorem B2117735 : Blo 1411525 2117735 := bstep (se 1 (by rfl) ⟨1588301, by rfl⟩ : syracuseStep 2117735 = 3176603) B3176603
theorem B1413223 : Blo 1411525 1413223 := bstep (se 1 (by rfl) ⟨1059917, by rfl⟩ : syracuseStep 1413223 = 2119835) B2119835
theorem B1413247 : Blo 1411525 1413247 := bstep (se 1 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 1413247 = 2119871) B2119871
theorem B1413275 : Blo 1411525 1413275 := bstep (se 1 (by rfl) ⟨1059956, by rfl⟩ : syracuseStep 1413275 = 2119913) B2119913
theorem B2117807 : Blo 1411525 2117807 := bstep (se 1 (by rfl) ⟨1588355, by rfl⟩ : syracuseStep 2117807 = 3176711) B3176711
theorem B12398845 : Blo 1411525 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B1413479 : Blo 1411525 1413479 := bstep (se 1 (by rfl) ⟨1060109, by rfl⟩ : syracuseStep 1413479 = 2120219) B2120219
theorem B223146353 : Blo 1411525 223146353 := bstep (se 2 (by rfl) ⟨83679882, by rfl⟩ : syracuseStep 223146353 = 167359765) B167359765
theorem B9048439 : Blo 1411525 9048439 := bstep (se 1 (by rfl) ⟨6786329, by rfl⟩ : syracuseStep 9048439 = 13572659) B13572659
theorem B2118011 : Blo 1411525 2118011 := bstep (se 1 (by rfl) ⟨1588508, by rfl⟩ : syracuseStep 2118011 = 3177017) B3177017
theorem B2683343 : Blo 1411525 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B7148087 : Blo 1411525 7148087 := bstep (se 1 (by rfl) ⟨5361065, by rfl⟩ : syracuseStep 7148087 = 10722131) B10722131
theorem B2118281 : Blo 1411525 2118281 := bstep (se 2 (by rfl) ⟨794355, by rfl⟩ : syracuseStep 2118281 = 1588711) B1588711
theorem B6197917 : Blo 1411525 6197917 := bstep (se 3 (by rfl) ⟨1162109, by rfl⟩ : syracuseStep 6197917 = 2324219) B2324219
theorem B2118491 : Blo 1411525 2118491 := bstep (se 1 (by rfl) ⟨1588868, by rfl⟩ : syracuseStep 2118491 = 3177737) B3177737
theorem B4764743 : Blo 1411525 4764743 := bstep (se 1 (by rfl) ⟨3573557, by rfl⟩ : syracuseStep 4764743 = 7147115) B7147115
theorem B6116467 : Blo 1411525 6116467 := bstep (se 1 (by rfl) ⟨4587350, by rfl⟩ : syracuseStep 6116467 = 9174701) B9174701
theorem B22918393 : Blo 1411525 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B185881871 : Blo 1411525 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B2118953 : Blo 1411525 2118953 := bstep (se 2 (by rfl) ⟨794607, by rfl⟩ : syracuseStep 2118953 = 1589215) B1589215
theorem B17184125 : Blo 1411525 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B2119151 : Blo 1411525 2119151 := bstep (se 1 (by rfl) ⟨1589363, by rfl⟩ : syracuseStep 2119151 = 3178727) B3178727
theorem B3175955 : Blo 1411525 3175955 := bstep (se 1 (by rfl) ⟨2381966, by rfl⟩ : syracuseStep 3175955 = 4763933) B4763933
theorem B3176027 : Blo 1411525 3176027 := bstep (se 1 (by rfl) ⟨2382020, by rfl⟩ : syracuseStep 3176027 = 4764041) B4764041
theorem B1431131 : Blo 1411525 1431131 := bstep (se 1 (by rfl) ⟨1073348, by rfl⟩ : syracuseStep 1431131 = 2146697) B2146697
theorem B40736429 : Blo 1411525 40736429 := bstep (se 3 (by rfl) ⟨7638080, by rfl⟩ : syracuseStep 40736429 = 15276161) B15276161
theorem B5363435 : Blo 1411525 5363435 := bstep (se 1 (by rfl) ⟨4022576, by rfl⟩ : syracuseStep 5363435 = 8045153) B8045153
theorem B6788927 : Blo 1411525 6788927 := bstep (se 1 (by rfl) ⟨5091695, by rfl⟩ : syracuseStep 6788927 = 10183391) B10183391
theorem B2119547 : Blo 1411525 2119547 := bstep (se 1 (by rfl) ⟨1589660, by rfl⟩ : syracuseStep 2119547 = 3179321) B3179321
theorem B20117393 : Blo 1411525 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B2119583 : Blo 1411525 2119583 := bstep (se 1 (by rfl) ⟨1589687, by rfl⟩ : syracuseStep 2119583 = 3179375) B3179375
theorem B2865223 : Blo 1411525 2865223 := bstep (se 1 (by rfl) ⟨2148917, by rfl⟩ : syracuseStep 2865223 = 4297835) B4297835
theorem B2119817 : Blo 1411525 2119817 := bstep (se 2 (by rfl) ⟨794931, by rfl⟩ : syracuseStep 2119817 = 1589863) B1589863
theorem B5437601 : Blo 1411525 5437601 := bstep (se 2 (by rfl) ⟨2039100, by rfl⟩ : syracuseStep 5437601 = 4078201) B4078201
theorem B3176639 : Blo 1411525 3176639 := bstep (se 1 (by rfl) ⟨2382479, by rfl⟩ : syracuseStep 3176639 = 4764959) B4764959
theorem B4765931 : Blo 1411525 4765931 := bstep (se 1 (by rfl) ⟨3574448, by rfl⟩ : syracuseStep 4765931 = 7148897) B7148897
theorem B2119967 : Blo 1411525 2119967 := bstep (se 1 (by rfl) ⟨1589975, by rfl⟩ : syracuseStep 2119967 = 3179951) B3179951
theorem B4020641 : Blo 1411525 4020641 := bstep (se 2 (by rfl) ⟨1507740, by rfl⟩ : syracuseStep 4020641 = 3015481) B3015481
theorem B2382311 : Blo 1411525 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B3439111 : Blo 1411525 3439111 := bstep (se 1 (by rfl) ⟨2579333, by rfl⟩ : syracuseStep 3439111 = 5158667) B5158667
theorem B5364377 : Blo 1411525 5364377 := bstep (se 2 (by rfl) ⟨2011641, by rfl⟩ : syracuseStep 5364377 = 4023283) B4023283
theorem B1588135 : Blo 1411525 1588135 := bstep (se 1 (by rfl) ⟨1191101, by rfl⟩ : syracuseStep 1588135 = 2382203) B2382203
theorem B18111437 : Blo 1411525 18111437 := bstep (se 3 (by rfl) ⟨3395894, by rfl⟩ : syracuseStep 18111437 = 6791789) B6791789
theorem B14490575 : Blo 1411525 14490575 := bstep (se 1 (by rfl) ⟨10867931, by rfl⟩ : syracuseStep 14490575 = 21735863) B21735863
theorem B25771085 : Blo 1411525 25771085 := bstep (se 3 (by rfl) ⟨4832078, by rfl⟩ : syracuseStep 25771085 = 9664157) B9664157
theorem B1588315 : Blo 1411525 1588315 := bstep (se 1 (by rfl) ⟨1191236, by rfl⟩ : syracuseStep 1588315 = 2382473) B2382473
theorem B12065921 : Blo 1411525 12065921 := bstep (se 2 (by rfl) ⟨4524720, by rfl⟩ : syracuseStep 12065921 = 9049441) B9049441
theorem B7150841 : Blo 1411525 7150841 := bstep (se 2 (by rfl) ⟨2681565, by rfl⟩ : syracuseStep 7150841 = 5363131) B5363131
theorem B12885257 : Blo 1411525 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B2383175 : Blo 1411525 2383175 := bstep (se 1 (by rfl) ⟨1787381, by rfl⟩ : syracuseStep 2383175 = 3574763) B3574763
theorem B3177899 : Blo 1411525 3177899 := bstep (se 1 (by rfl) ⟨2383424, by rfl⟩ : syracuseStep 3177899 = 4766849) B4766849
theorem B3177935 : Blo 1411525 3177935 := bstep (se 1 (by rfl) ⟨2383451, by rfl⟩ : syracuseStep 3177935 = 4766903) B4766903
theorem B2383337 : Blo 1411525 2383337 := bstep (se 2 (by rfl) ⟨893751, by rfl⟩ : syracuseStep 2383337 = 1787503) B1787503
theorem B34381691 : Blo 1411525 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B3178439 : Blo 1411525 3178439 := bstep (se 1 (by rfl) ⟨2383829, by rfl⟩ : syracuseStep 3178439 = 4767659) B4767659
theorem B3391571 : Blo 1411525 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B5439743 : Blo 1411525 5439743 := bstep (se 1 (by rfl) ⟨4079807, by rfl⟩ : syracuseStep 5439743 = 8159615) B8159615
theorem B16531793 : Blo 1411525 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B3178835 : Blo 1411525 3178835 := bstep (se 1 (by rfl) ⟨2384126, by rfl⟩ : syracuseStep 3178835 = 4768253) B4768253
theorem B1508159 : Blo 1411525 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B123921247 : Blo 1411525 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B3179591 : Blo 1411525 3179591 := bstep (se 1 (by rfl) ⟨2384693, by rfl⟩ : syracuseStep 3179591 = 4769387) B4769387
theorem B27157619 : Blo 1411525 27157619 := bstep (se 1 (by rfl) ⟨20368214, by rfl⟩ : syracuseStep 27157619 = 40736429) B40736429
theorem B1508603 : Blo 1411525 1508603 := bstep (se 1 (by rfl) ⟨1131452, by rfl⟩ : syracuseStep 1508603 = 2262905) B2262905
theorem B3179771 : Blo 1411525 3179771 := bstep (se 1 (by rfl) ⟨2384828, by rfl⟩ : syracuseStep 3179771 = 4769657) B4769657
theorem B3622151 : Blo 1411525 3622151 := bstep (se 1 (by rfl) ⟨2716613, by rfl⟩ : syracuseStep 3622151 = 5433227) B5433227
theorem B13411595 : Blo 1411525 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B3180023 : Blo 1411525 3180023 := bstep (se 1 (by rfl) ⟨2385017, by rfl⟩ : syracuseStep 3180023 = 4770035) B4770035
theorem B34375265 : Blo 1411525 34375265 := bstep (se 2 (by rfl) ⟨12890724, by rfl⟩ : syracuseStep 34375265 = 25781449) B25781449
theorem B3573355 : Blo 1411525 3573355 := bstep (se 1 (by rfl) ⟨2680016, by rfl⟩ : syracuseStep 3573355 = 5360033) B5360033
theorem B2680427 : Blo 1411525 2680427 := bstep (se 1 (by rfl) ⟨2010320, by rfl⟩ : syracuseStep 2680427 = 4020641) B4020641
theorem B3573659 : Blo 1411525 3573659 := bstep (se 1 (by rfl) ⟨2680244, by rfl⟩ : syracuseStep 3573659 = 5360489) B5360489
theorem B9660383 : Blo 1411525 9660383 := bstep (se 1 (by rfl) ⟨7245287, by rfl⟩ : syracuseStep 9660383 = 14490575) B14490575
theorem B4769819 : Blo 1411525 4769819 := bstep (se 1 (by rfl) ⟨3577364, by rfl⟩ : syracuseStep 4769819 = 7154729) B7154729
theorem B17180723 : Blo 1411525 17180723 := bstep (se 1 (by rfl) ⟨12885542, by rfl⟩ : syracuseStep 17180723 = 25771085) B25771085
theorem B3574003 : Blo 1411525 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B4524425 : Blo 1411525 4524425 := bstep (se 2 (by rfl) ⟨1696659, by rfl⟩ : syracuseStep 4524425 = 3393319) B3393319
theorem B7146143 : Blo 1411525 7146143 := bstep (se 1 (by rfl) ⟨5359607, by rfl⟩ : syracuseStep 7146143 = 10719215) B10719215
theorem B1411743 : Blo 1411525 1411743 := bstep (se 1 (by rfl) ⟨1058807, by rfl⟩ : syracuseStep 1411743 = 2117615) B2117615
theorem B1411751 : Blo 1411525 1411751 := bstep (se 1 (by rfl) ⟨1058813, by rfl⟩ : syracuseStep 1411751 = 2117627) B2117627
theorem B3574439 : Blo 1411525 3574439 := bstep (se 1 (by rfl) ⟨2680829, by rfl⟩ : syracuseStep 3574439 = 5361659) B5361659
theorem B1411791 : Blo 1411525 1411791 := bstep (se 1 (by rfl) ⟨1058843, by rfl⟩ : syracuseStep 1411791 = 2117687) B2117687
theorem B1411823 : Blo 1411525 1411823 := bstep (se 1 (by rfl) ⟨1058867, by rfl⟩ : syracuseStep 1411823 = 2117735) B2117735
theorem B3820297 : Blo 1411525 3820297 := bstep (se 2 (by rfl) ⟨1432611, by rfl⟩ : syracuseStep 3820297 = 2865223) B2865223
theorem B1411871 : Blo 1411525 1411871 := bstep (se 1 (by rfl) ⟨1058903, by rfl⟩ : syracuseStep 1411871 = 2117807) B2117807
theorem B1412007 : Blo 1411525 1412007 := bstep (se 1 (by rfl) ⟨1059005, by rfl⟩ : syracuseStep 1412007 = 2118011) B2118011
theorem B1788895 : Blo 1411525 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B3574793 : Blo 1411525 3574793 := bstep (se 2 (by rfl) ⟨1340547, by rfl⟩ : syracuseStep 3574793 = 2681095) B2681095
theorem B27159623 : Blo 1411525 27159623 := bstep (se 1 (by rfl) ⟨20369717, by rfl⟩ : syracuseStep 27159623 = 40739435) B40739435
theorem B1412187 : Blo 1411525 1412187 := bstep (se 1 (by rfl) ⟨1059140, by rfl⟩ : syracuseStep 1412187 = 2118281) B2118281
theorem B9047209 : Blo 1411525 9047209 := bstep (se 2 (by rfl) ⟨3392703, by rfl⟩ : syracuseStep 9047209 = 6785407) B6785407
theorem B1412327 : Blo 1411525 1412327 := bstep (se 1 (by rfl) ⟨1059245, by rfl⟩ : syracuseStep 1412327 = 2118491) B2118491
theorem B1412635 : Blo 1411525 1412635 := bstep (se 1 (by rfl) ⟨1059476, by rfl⟩ : syracuseStep 1412635 = 2118953) B2118953
theorem B10726991 : Blo 1411525 10726991 := bstep (se 1 (by rfl) ⟨8045243, by rfl⟩ : syracuseStep 10726991 = 16090487) B16090487
theorem B11456083 : Blo 1411525 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B15265397 : Blo 1411525 15265397 := bstep (se 5 (by rfl) ⟨715565, by rfl⟩ : syracuseStep 15265397 = 1431131) B1431131
theorem B1412767 : Blo 1411525 1412767 := bstep (se 1 (by rfl) ⟨1059575, by rfl⟩ : syracuseStep 1412767 = 2119151) B2119151
theorem B2117303 : Blo 1411525 2117303 := bstep (se 1 (by rfl) ⟨1587977, by rfl⟩ : syracuseStep 2117303 = 3175955) B3175955
theorem B2117351 : Blo 1411525 2117351 := bstep (se 1 (by rfl) ⟨1588013, by rfl⟩ : syracuseStep 2117351 = 3176027) B3176027
theorem B37220143 : Blo 1411525 37220143 := bstep (se 1 (by rfl) ⟨27915107, by rfl⟩ : syracuseStep 37220143 = 55830215) B55830215
theorem B3575623 : Blo 1411525 3575623 := bstep (se 1 (by rfl) ⟨2681717, by rfl⟩ : syracuseStep 3575623 = 5363435) B5363435
theorem B4525951 : Blo 1411525 4525951 := bstep (se 1 (by rfl) ⟨3394463, by rfl⟩ : syracuseStep 4525951 = 6788927) B6788927
theorem B2117513 : Blo 1411525 2117513 := bstep (se 2 (by rfl) ⟨794067, by rfl⟩ : syracuseStep 2117513 = 1588135) B1588135
theorem B1413031 : Blo 1411525 1413031 := bstep (se 1 (by rfl) ⟨1059773, by rfl⟩ : syracuseStep 1413031 = 2119547) B2119547
theorem B1413055 : Blo 1411525 1413055 := bstep (se 1 (by rfl) ⟨1059791, by rfl⟩ : syracuseStep 1413055 = 2119583) B2119583
theorem B1413211 : Blo 1411525 1413211 := bstep (se 1 (by rfl) ⟨1059908, by rfl⟩ : syracuseStep 1413211 = 2119817) B2119817
theorem B2011243 : Blo 1411525 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B3625067 : Blo 1411525 3625067 := bstep (se 1 (by rfl) ⟨2718800, by rfl⟩ : syracuseStep 3625067 = 5437601) B5437601
theorem B2117753 : Blo 1411525 2117753 := bstep (se 2 (by rfl) ⟨794157, by rfl⟩ : syracuseStep 2117753 = 1588315) B1588315
theorem B2117759 : Blo 1411525 2117759 := bstep (se 1 (by rfl) ⟨1588319, by rfl⟩ : syracuseStep 2117759 = 3176639) B3176639
theorem B8155289 : Blo 1411525 8155289 := bstep (se 2 (by rfl) ⟨3058233, by rfl⟩ : syracuseStep 8155289 = 6116467) B6116467
theorem B1413311 : Blo 1411525 1413311 := bstep (se 1 (by rfl) ⟨1059983, by rfl⟩ : syracuseStep 1413311 = 2119967) B2119967
theorem B3576251 : Blo 1411525 3576251 := bstep (se 1 (by rfl) ⟨2682188, by rfl⟩ : syracuseStep 3576251 = 5364377) B5364377
theorem B8590171 : Blo 1411525 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B2118599 : Blo 1411525 2118599 := bstep (se 1 (by rfl) ⟨1588949, by rfl⟩ : syracuseStep 2118599 = 3177899) B3177899
theorem B2118623 : Blo 1411525 2118623 := bstep (se 1 (by rfl) ⟨1588967, by rfl⟩ : syracuseStep 2118623 = 3177935) B3177935
theorem B2012143 : Blo 1411525 2012143 := bstep (se 1 (by rfl) ⟨1509107, by rfl⟩ : syracuseStep 2012143 = 3018215) B3018215
theorem B176297249 : Blo 1411525 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B2118959 : Blo 1411525 2118959 := bstep (se 1 (by rfl) ⟨1589219, by rfl⟩ : syracuseStep 2118959 = 3178439) B3178439
theorem B2119163 : Blo 1411525 2119163 := bstep (se 1 (by rfl) ⟨1589372, by rfl⟩ : syracuseStep 2119163 = 3178745) B3178745
theorem B2119199 : Blo 1411525 2119199 := bstep (se 1 (by rfl) ⟨1589399, by rfl⟩ : syracuseStep 2119199 = 3178799) B3178799
theorem B148764235 : Blo 1411525 148764235 := bstep (se 1 (by rfl) ⟨111573176, by rfl⟩ : syracuseStep 148764235 = 223146353) B223146353
theorem B2119337 : Blo 1411525 2119337 := bstep (se 2 (by rfl) ⟨794751, by rfl⟩ : syracuseStep 2119337 = 1589503) B1589503
theorem B2119343 : Blo 1411525 2119343 := bstep (se 1 (by rfl) ⟨1589507, by rfl⟩ : syracuseStep 2119343 = 3179015) B3179015
theorem B4765391 : Blo 1411525 4765391 := bstep (se 1 (by rfl) ⟨3574043, by rfl⟩ : syracuseStep 4765391 = 7148087) B7148087
theorem B2119463 : Blo 1411525 2119463 := bstep (se 1 (by rfl) ⟨1589597, by rfl⟩ : syracuseStep 2119463 = 3179195) B3179195
theorem B12064585 : Blo 1411525 12064585 := bstep (se 2 (by rfl) ⟨4524219, by rfl⟩ : syracuseStep 12064585 = 9048439) B9048439
theorem B4585481 : Blo 1411525 4585481 := bstep (se 2 (by rfl) ⟨1719555, by rfl⟩ : syracuseStep 4585481 = 3439111) B3439111
theorem B2119721 : Blo 1411525 2119721 := bstep (se 2 (by rfl) ⟨794895, by rfl⟩ : syracuseStep 2119721 = 1589791) B1589791
theorem B3176495 : Blo 1411525 3176495 := bstep (se 1 (by rfl) ⟨2382371, by rfl⟩ : syracuseStep 3176495 = 4764743) B4764743
theorem B2119751 : Blo 1411525 2119751 := bstep (se 1 (by rfl) ⟨1589813, by rfl⟩ : syracuseStep 2119751 = 3179627) B3179627
theorem B8263889 : Blo 1411525 8263889 := bstep (se 2 (by rfl) ⟨3098958, by rfl⟩ : syracuseStep 8263889 = 6197917) B6197917
theorem B2120063 : Blo 1411525 2120063 := bstep (se 1 (by rfl) ⟨1590047, by rfl⟩ : syracuseStep 2120063 = 3180095) B3180095
theorem B2120135 : Blo 1411525 2120135 := bstep (se 1 (by rfl) ⟨1590101, by rfl⟩ : syracuseStep 2120135 = 3180203) B3180203
theorem B7150031 : Blo 1411525 7150031 := bstep (se 1 (by rfl) ⟨5362523, by rfl⟩ : syracuseStep 7150031 = 10725047) B10725047
theorem B122231429 : Blo 1411525 122231429 := bstep (se 4 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 122231429 = 22918393) B22918393
theorem B2382655 : Blo 1411525 2382655 := bstep (se 1 (by rfl) ⟨1786991, by rfl⟩ : syracuseStep 2382655 = 3573983) B3573983
theorem B3177287 : Blo 1411525 3177287 := bstep (se 1 (by rfl) ⟨2382965, by rfl⟩ : syracuseStep 3177287 = 4765931) B4765931
theorem B52263901 : Blo 1411525 52263901 := bstep (se 3 (by rfl) ⟨9799481, by rfl⟩ : syracuseStep 52263901 = 19598963) B19598963
theorem B1588207 : Blo 1411525 1588207 := bstep (se 1 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 1588207 = 2382311) B2382311
theorem B51534863 : Blo 1411525 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B12074291 : Blo 1411525 12074291 := bstep (se 1 (by rfl) ⟨9055718, by rfl⟩ : syracuseStep 12074291 = 18111437) B18111437
theorem B8043947 : Blo 1411525 8043947 := bstep (se 1 (by rfl) ⟨6032960, by rfl⟩ : syracuseStep 8043947 = 12065921) B12065921
theorem B4767227 : Blo 1411525 4767227 := bstep (se 1 (by rfl) ⟨3575420, by rfl⟩ : syracuseStep 4767227 = 7150841) B7150841
theorem B1588783 : Blo 1411525 1588783 := bstep (se 1 (by rfl) ⟨1191587, by rfl⟩ : syracuseStep 1588783 = 2383175) B2383175
theorem B1588891 : Blo 1411525 1588891 := bstep (se 1 (by rfl) ⟨1191668, by rfl⟩ : syracuseStep 1588891 = 2383337) B2383337
theorem B10723103 : Blo 1411525 10723103 := bstep (se 1 (by rfl) ⟨8042327, by rfl⟩ : syracuseStep 10723103 = 16084655) B16084655
theorem B22921127 : Blo 1411525 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B2261047 : Blo 1411525 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B2416711 : Blo 1411525 2416711 := bstep (se 1 (by rfl) ⟨1812533, by rfl⟩ : syracuseStep 2416711 = 3625067) B3625067
theorem B2384167 : Blo 1411525 2384167 := bstep (se 1 (by rfl) ⟨1788125, by rfl⟩ : syracuseStep 2384167 = 3576251) B3576251
theorem B4022941 : Blo 1411525 4022941 := bstep (se 3 (by rfl) ⟨754301, by rfl⟩ : syracuseStep 4022941 = 1508603) B1508603
theorem B18105079 : Blo 1411525 18105079 := bstep (se 1 (by rfl) ⟨13578809, by rfl⟩ : syracuseStep 18105079 = 27157619) B27157619
theorem B117531499 : Blo 1411525 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B1786951 : Blo 1411525 1786951 := bstep (se 1 (by rfl) ⟨1340213, by rfl⟩ : syracuseStep 1786951 = 2680427) B2680427
theorem B11453561 : Blo 1411525 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B2385193 : Blo 1411525 2385193 := bstep (se 2 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 2385193 = 1788895) B1788895
theorem B6440255 : Blo 1411525 6440255 := bstep (se 1 (by rfl) ⟨4830191, by rfl⟩ : syracuseStep 6440255 = 9660383) B9660383
theorem B3056987 : Blo 1411525 3056987 := bstep (se 1 (by rfl) ⟨2292740, by rfl⟩ : syracuseStep 3056987 = 4585481) B4585481
theorem B3179879 : Blo 1411525 3179879 := bstep (se 1 (by rfl) ⟨2384909, by rfl⟩ : syracuseStep 3179879 = 4769819) B4769819
theorem B11453815 : Blo 1411525 11453815 := bstep (se 1 (by rfl) ⟨8590361, by rfl⟩ : syracuseStep 11453815 = 17180723) B17180723
theorem B3016283 : Blo 1411525 3016283 := bstep (se 1 (by rfl) ⟨2262212, by rfl⟩ : syracuseStep 3016283 = 4524425) B4524425
theorem B81487619 : Blo 1411525 81487619 := bstep (se 1 (by rfl) ⟨61115714, by rfl⟩ : syracuseStep 81487619 = 122231429) B122231429
theorem B18106415 : Blo 1411525 18106415 := bstep (se 1 (by rfl) ⟨13579811, by rfl⟩ : syracuseStep 18106415 = 27159623) B27159623
theorem B10176931 : Blo 1411525 10176931 := bstep (se 1 (by rfl) ⟨7632698, by rfl⟩ : syracuseStep 10176931 = 15265397) B15265397
theorem B1411535 : Blo 1411525 1411535 := bstep (se 1 (by rfl) ⟨1058651, by rfl⟩ : syracuseStep 1411535 = 2117303) B2117303
theorem B1411567 : Blo 1411525 1411567 := bstep (se 1 (by rfl) ⟨1058675, by rfl⟩ : syracuseStep 1411567 = 2117351) B2117351
theorem B1411675 : Blo 1411525 1411675 := bstep (se 1 (by rfl) ⟨1058756, by rfl⟩ : syracuseStep 1411675 = 2117513) B2117513
theorem B15280751 : Blo 1411525 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B1411835 : Blo 1411525 1411835 := bstep (se 1 (by rfl) ⟨1058876, by rfl⟩ : syracuseStep 1411835 = 2117753) B2117753
theorem B1411839 : Blo 1411525 1411839 := bstep (se 1 (by rfl) ⟨1058879, by rfl⟩ : syracuseStep 1411839 = 2117759) B2117759
theorem B2681657 : Blo 1411525 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B11021195 : Blo 1411525 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B61099109 : Blo 1411525 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B1412399 : Blo 1411525 1412399 := bstep (se 1 (by rfl) ⟨1059299, by rfl⟩ : syracuseStep 1412399 = 2118599) B2118599
theorem B1412415 : Blo 1411525 1412415 := bstep (se 1 (by rfl) ⟨1059311, by rfl⟩ : syracuseStep 1412415 = 2118623) B2118623
theorem B1412639 : Blo 1411525 1412639 := bstep (se 1 (by rfl) ⟨1059479, by rfl⟩ : syracuseStep 1412639 = 2118959) B2118959
theorem B1412775 : Blo 1411525 1412775 := bstep (se 1 (by rfl) ⟨1059581, by rfl⟩ : syracuseStep 1412775 = 2119163) B2119163
theorem B1412799 : Blo 1411525 1412799 := bstep (se 1 (by rfl) ⟨1059599, by rfl⟩ : syracuseStep 1412799 = 2119199) B2119199
theorem B22916843 : Blo 1411525 22916843 := bstep (se 1 (by rfl) ⟨17187632, by rfl⟩ : syracuseStep 22916843 = 34375265) B34375265
theorem B1412891 : Blo 1411525 1412891 := bstep (se 1 (by rfl) ⟨1059668, by rfl⟩ : syracuseStep 1412891 = 2119337) B2119337
theorem B1412895 : Blo 1411525 1412895 := bstep (se 1 (by rfl) ⟨1059671, by rfl⟩ : syracuseStep 1412895 = 2119343) B2119343
theorem B165228329 : Blo 1411525 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B1412975 : Blo 1411525 1412975 := bstep (se 1 (by rfl) ⟨1059731, by rfl⟩ : syracuseStep 1412975 = 2119463) B2119463
theorem B69685201 : Blo 1411525 69685201 := bstep (se 2 (by rfl) ⟨26131950, by rfl⟩ : syracuseStep 69685201 = 52263901) B52263901
theorem B2117609 : Blo 1411525 2117609 := bstep (se 2 (by rfl) ⟨794103, by rfl⟩ : syracuseStep 2117609 = 1588207) B1588207
theorem B2682857 : Blo 1411525 2682857 := bstep (se 2 (by rfl) ⟨1006071, by rfl⟩ : syracuseStep 2682857 = 2012143) B2012143
theorem B1413147 : Blo 1411525 1413147 := bstep (se 1 (by rfl) ⟨1059860, by rfl⟩ : syracuseStep 1413147 = 2119721) B2119721
theorem B2117663 : Blo 1411525 2117663 := bstep (se 1 (by rfl) ⟨1588247, by rfl⟩ : syracuseStep 2117663 = 3176495) B3176495
theorem B1413167 : Blo 1411525 1413167 := bstep (se 1 (by rfl) ⟨1059875, by rfl⟩ : syracuseStep 1413167 = 2119751) B2119751
theorem B5509259 : Blo 1411525 5509259 := bstep (se 1 (by rfl) ⟨4131944, by rfl⟩ : syracuseStep 5509259 = 8263889) B8263889
theorem B12062945 : Blo 1411525 12062945 := bstep (se 2 (by rfl) ⟨4523604, by rfl⟩ : syracuseStep 12062945 = 9047209) B9047209
theorem B1413375 : Blo 1411525 1413375 := bstep (se 1 (by rfl) ⟨1060031, by rfl⟩ : syracuseStep 1413375 = 2120063) B2120063
theorem B1413423 : Blo 1411525 1413423 := bstep (se 1 (by rfl) ⟨1060067, by rfl⟩ : syracuseStep 1413423 = 2120135) B2120135
theorem B4764095 : Blo 1411525 4764095 := bstep (se 1 (by rfl) ⟨3573071, by rfl⟩ : syracuseStep 4764095 = 7146143) B7146143
theorem B2118191 : Blo 1411525 2118191 := bstep (se 1 (by rfl) ⟨1588643, by rfl⟩ : syracuseStep 2118191 = 3177287) B3177287
theorem B2118377 : Blo 1411525 2118377 := bstep (se 2 (by rfl) ⟨794391, by rfl⟩ : syracuseStep 2118377 = 1588783) B1588783
theorem B4764473 : Blo 1411525 4764473 := bstep (se 2 (by rfl) ⟨1786677, by rfl⟩ : syracuseStep 4764473 = 3573355) B3573355
theorem B8049527 : Blo 1411525 8049527 := bstep (se 1 (by rfl) ⟨6037145, by rfl⟩ : syracuseStep 8049527 = 12074291) B12074291
theorem B2118521 : Blo 1411525 2118521 := bstep (se 2 (by rfl) ⟨794445, by rfl⟩ : syracuseStep 2118521 = 1588891) B1588891
theorem B5362631 : Blo 1411525 5362631 := bstep (se 1 (by rfl) ⟨4021973, by rfl⟩ : syracuseStep 5362631 = 8043947) B8043947
theorem B16086113 : Blo 1411525 16086113 := bstep (se 2 (by rfl) ⟨6032292, by rfl⟩ : syracuseStep 16086113 = 12064585) B12064585
theorem B6034601 : Blo 1411525 6034601 := bstep (se 2 (by rfl) ⟨2262975, by rfl⟩ : syracuseStep 6034601 = 4525951) B4525951
theorem B7148735 : Blo 1411525 7148735 := bstep (se 1 (by rfl) ⟨5361551, by rfl⟩ : syracuseStep 7148735 = 10723103) B10723103
theorem B3626495 : Blo 1411525 3626495 := bstep (se 1 (by rfl) ⟨2719871, by rfl⟩ : syracuseStep 3626495 = 5439743) B5439743
theorem B2119223 : Blo 1411525 2119223 := bstep (se 1 (by rfl) ⟨1589417, by rfl⟩ : syracuseStep 2119223 = 3178835) B3178835
theorem B4765337 : Blo 1411525 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B21747437 : Blo 1411525 21747437 := bstep (se 3 (by rfl) ⟨4077644, by rfl⟩ : syracuseStep 21747437 = 8155289) B8155289
theorem B35764253 : Blo 1411525 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B2119727 : Blo 1411525 2119727 := bstep (se 1 (by rfl) ⟨1589795, by rfl⟩ : syracuseStep 2119727 = 3179591) B3179591
theorem B2119847 : Blo 1411525 2119847 := bstep (se 1 (by rfl) ⟨1589885, by rfl⟩ : syracuseStep 2119847 = 3179771) B3179771
theorem B2414767 : Blo 1411525 2414767 := bstep (se 1 (by rfl) ⟨1811075, by rfl⟩ : syracuseStep 2414767 = 3622151) B3622151
theorem B2120015 : Blo 1411525 2120015 := bstep (se 1 (by rfl) ⟨1590011, by rfl⟩ : syracuseStep 2120015 = 3180023) B3180023
theorem B5093729 : Blo 1411525 5093729 := bstep (se 2 (by rfl) ⟨1910148, by rfl⟩ : syracuseStep 5093729 = 3820297) B3820297
theorem B3176873 : Blo 1411525 3176873 := bstep (se 2 (by rfl) ⟨1191327, by rfl⟩ : syracuseStep 3176873 = 2382655) B2382655
theorem B3176927 : Blo 1411525 3176927 := bstep (se 1 (by rfl) ⟨2382695, by rfl⟩ : syracuseStep 3176927 = 4765391) B4765391
theorem B2382439 : Blo 1411525 2382439 := bstep (se 1 (by rfl) ⟨1786829, by rfl⟩ : syracuseStep 2382439 = 3573659) B3573659
theorem B4766687 : Blo 1411525 4766687 := bstep (se 1 (by rfl) ⟨3575015, by rfl⟩ : syracuseStep 4766687 = 7150031) B7150031
theorem B2382959 : Blo 1411525 2382959 := bstep (se 1 (by rfl) ⟨1787219, by rfl⟩ : syracuseStep 2382959 = 3574439) B3574439
theorem B2383195 : Blo 1411525 2383195 := bstep (se 1 (by rfl) ⟨1787396, by rfl⟩ : syracuseStep 2383195 = 3574793) B3574793
theorem B34356575 : Blo 1411525 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B198352313 : Blo 1411525 198352313 := bstep (se 2 (by rfl) ⟨74382117, by rfl⟩ : syracuseStep 198352313 = 148764235) B148764235
theorem B4021757 : Blo 1411525 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B3178151 : Blo 1411525 3178151 := bstep (se 1 (by rfl) ⟨2383613, by rfl⟩ : syracuseStep 3178151 = 4767227) B4767227
theorem B7151327 : Blo 1411525 7151327 := bstep (se 1 (by rfl) ⟨5363495, by rfl⟩ : syracuseStep 7151327 = 10726991) B10726991
theorem B49626857 : Blo 1411525 49626857 := bstep (se 2 (by rfl) ⟨18610071, by rfl⟩ : syracuseStep 49626857 = 37220143) B37220143
theorem B4767497 : Blo 1411525 4767497 := bstep (se 2 (by rfl) ⟨1787811, by rfl⟩ : syracuseStep 4767497 = 3575623) B3575623
theorem B3014729 : Blo 1411525 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B3219689 : Blo 1411525 3219689 := bstep (se 2 (by rfl) ⟨1207383, by rfl⟩ : syracuseStep 3219689 = 2414767) B2414767
theorem B3178889 : Blo 1411525 3178889 := bstep (se 2 (by rfl) ⟨1192083, by rfl⟩ : syracuseStep 3178889 = 2384167) B2384167
theorem B5366351 : Blo 1411525 5366351 := bstep (se 1 (by rfl) ⟨4024763, by rfl⟩ : syracuseStep 5366351 = 8049527) B8049527
theorem B10724075 : Blo 1411525 10724075 := bstep (se 1 (by rfl) ⟨8043056, by rfl⟩ : syracuseStep 10724075 = 16086113) B16086113
theorem B7635707 : Blo 1411525 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B4023067 : Blo 1411525 4023067 := bstep (se 1 (by rfl) ⟨3017300, by rfl⟩ : syracuseStep 4023067 = 6034601) B6034601
theorem B4293503 : Blo 1411525 4293503 := bstep (se 1 (by rfl) ⟨3220127, by rfl⟩ : syracuseStep 4293503 = 6440255) B6440255
theorem B2417663 : Blo 1411525 2417663 := bstep (se 1 (by rfl) ⟨1813247, by rfl⟩ : syracuseStep 2417663 = 3626495) B3626495
theorem B3180257 : Blo 1411525 3180257 := bstep (se 2 (by rfl) ⟨1192596, by rfl⟩ : syracuseStep 3180257 = 2385193) B2385193
theorem B15271753 : Blo 1411525 15271753 := bstep (se 2 (by rfl) ⟨5726907, by rfl⟩ : syracuseStep 15271753 = 11453815) B11453815
theorem B1787771 : Blo 1411525 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B40732739 : Blo 1411525 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B2681171 : Blo 1411525 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B110152219 : Blo 1411525 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B1411739 : Blo 1411525 1411739 := bstep (se 1 (by rfl) ⟨1058804, by rfl⟩ : syracuseStep 1411739 = 2117609) B2117609
theorem B1788571 : Blo 1411525 1788571 := bstep (se 1 (by rfl) ⟨1341428, by rfl⟩ : syracuseStep 1788571 = 2682857) B2682857
theorem B1411775 : Blo 1411525 1411775 := bstep (se 1 (by rfl) ⟨1058831, by rfl⟩ : syracuseStep 1411775 = 2117663) B2117663
theorem B3672839 : Blo 1411525 3672839 := bstep (se 1 (by rfl) ⟨2754629, by rfl⟩ : syracuseStep 3672839 = 5509259) B5509259
theorem B3222281 : Blo 1411525 3222281 := bstep (se 2 (by rfl) ⟨1208355, by rfl⟩ : syracuseStep 3222281 = 2416711) B2416711
theorem B1412127 : Blo 1411525 1412127 := bstep (se 1 (by rfl) ⟨1059095, by rfl⟩ : syracuseStep 1412127 = 2118191) B2118191
theorem B1412251 : Blo 1411525 1412251 := bstep (se 1 (by rfl) ⟨1059188, by rfl⟩ : syracuseStep 1412251 = 2118377) B2118377
theorem B13569241 : Blo 1411525 13569241 := bstep (se 2 (by rfl) ⟨5088465, by rfl⟩ : syracuseStep 13569241 = 10176931) B10176931
theorem B1412347 : Blo 1411525 1412347 := bstep (se 1 (by rfl) ⟨1059260, by rfl⟩ : syracuseStep 1412347 = 2118521) B2118521
theorem B3575087 : Blo 1411525 3575087 := bstep (se 1 (by rfl) ⟨2681315, by rfl⟩ : syracuseStep 3575087 = 5362631) B5362631
theorem B1412815 : Blo 1411525 1412815 := bstep (se 1 (by rfl) ⟨1059611, by rfl⟩ : syracuseStep 1412815 = 2119223) B2119223
theorem B156708665 : Blo 1411525 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B54325079 : Blo 1411525 54325079 := bstep (se 1 (by rfl) ⟨40743809, by rfl⟩ : syracuseStep 54325079 = 81487619) B81487619
theorem B23842835 : Blo 1411525 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B12070943 : Blo 1411525 12070943 := bstep (se 1 (by rfl) ⟨9053207, by rfl⟩ : syracuseStep 12070943 = 18106415) B18106415
theorem B1413151 : Blo 1411525 1413151 := bstep (se 1 (by rfl) ⟨1059863, by rfl⟩ : syracuseStep 1413151 = 2119727) B2119727
theorem B1413231 : Blo 1411525 1413231 := bstep (se 1 (by rfl) ⟨1059923, by rfl⟩ : syracuseStep 1413231 = 2119847) B2119847
theorem B1413343 : Blo 1411525 1413343 := bstep (se 1 (by rfl) ⟨1060007, by rfl⟩ : syracuseStep 1413343 = 2120015) B2120015
theorem B3395819 : Blo 1411525 3395819 := bstep (se 1 (by rfl) ⟨2546864, by rfl⟩ : syracuseStep 3395819 = 5093729) B5093729
theorem B2117915 : Blo 1411525 2117915 := bstep (se 1 (by rfl) ⟨1588436, by rfl⟩ : syracuseStep 2117915 = 3176873) B3176873
theorem B2117951 : Blo 1411525 2117951 := bstep (se 1 (by rfl) ⟨1588463, by rfl⟩ : syracuseStep 2117951 = 3176927) B3176927
theorem B10187167 : Blo 1411525 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B29389853 : Blo 1411525 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B2118767 : Blo 1411525 2118767 := bstep (se 1 (by rfl) ⟨1589075, by rfl⟩ : syracuseStep 2118767 = 3178151) B3178151
theorem B33084571 : Blo 1411525 33084571 := bstep (se 1 (by rfl) ⟨24813428, by rfl⟩ : syracuseStep 33084571 = 49626857) B49626857
theorem B8041963 : Blo 1411525 8041963 := bstep (se 1 (by rfl) ⟨6031472, by rfl⟩ : syracuseStep 8041963 = 12062945) B12062945
theorem B3176063 : Blo 1411525 3176063 := bstep (se 1 (by rfl) ⟨2382047, by rfl⟩ : syracuseStep 3176063 = 4764095) B4764095
theorem B3176315 : Blo 1411525 3176315 := bstep (se 1 (by rfl) ⟨2382236, by rfl⟩ : syracuseStep 3176315 = 4764473) B4764473
theorem B4765823 : Blo 1411525 4765823 := bstep (se 1 (by rfl) ⟨3574367, by rfl⟩ : syracuseStep 4765823 = 7148735) B7148735
theorem B3176585 : Blo 1411525 3176585 := bstep (se 2 (by rfl) ⟨1191219, by rfl⟩ : syracuseStep 3176585 = 2382439) B2382439
theorem B5363921 : Blo 1411525 5363921 := bstep (se 2 (by rfl) ⟨2011470, by rfl⟩ : syracuseStep 5363921 = 4022941) B4022941
theorem B2037991 : Blo 1411525 2037991 := bstep (se 1 (by rfl) ⟨1528493, by rfl⟩ : syracuseStep 2037991 = 3056987) B3056987
theorem B2119919 : Blo 1411525 2119919 := bstep (se 1 (by rfl) ⟨1589939, by rfl⟩ : syracuseStep 2119919 = 3179879) B3179879
theorem B24140105 : Blo 1411525 24140105 := bstep (se 2 (by rfl) ⟨9052539, by rfl⟩ : syracuseStep 24140105 = 18105079) B18105079
theorem B3176891 : Blo 1411525 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B14498291 : Blo 1411525 14498291 := bstep (se 1 (by rfl) ⟨10873718, by rfl⟩ : syracuseStep 14498291 = 21747437) B21747437
theorem B2382601 : Blo 1411525 2382601 := bstep (se 2 (by rfl) ⟨893475, by rfl⟩ : syracuseStep 2382601 = 1786951) B1786951
theorem B8043421 : Blo 1411525 8043421 := bstep (se 3 (by rfl) ⟨1508141, by rfl⟩ : syracuseStep 8043421 = 3016283) B3016283
theorem B3177593 : Blo 1411525 3177593 := bstep (se 2 (by rfl) ⟨1191597, by rfl⟩ : syracuseStep 3177593 = 2383195) B2383195
theorem B3177791 : Blo 1411525 3177791 := bstep (se 1 (by rfl) ⟨2383343, by rfl⟩ : syracuseStep 3177791 = 4766687) B4766687
theorem B1588639 : Blo 1411525 1588639 := bstep (se 1 (by rfl) ⟨1191479, by rfl⟩ : syracuseStep 1588639 = 2382959) B2382959
theorem B22904383 : Blo 1411525 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B132234875 : Blo 1411525 132234875 := bstep (se 1 (by rfl) ⟨99176156, by rfl⟩ : syracuseStep 132234875 = 198352313) B198352313
theorem B371654405 : Blo 1411525 371654405 := bstep (se 4 (by rfl) ⟨34842600, by rfl⟩ : syracuseStep 371654405 = 69685201) B69685201
theorem B4767551 : Blo 1411525 4767551 := bstep (se 1 (by rfl) ⟨3575663, by rfl⟩ : syracuseStep 4767551 = 7151327) B7151327
theorem B15277895 : Blo 1411525 15277895 := bstep (se 1 (by rfl) ⟨11458421, by rfl⟩ : syracuseStep 15277895 = 22916843) B22916843
theorem B3178331 : Blo 1411525 3178331 := bstep (se 1 (by rfl) ⟨2383748, by rfl⟩ : syracuseStep 3178331 = 4767497) B4767497
theorem B13582889 : Blo 1411525 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B8585837 : Blo 1411525 8585837 := bstep (se 3 (by rfl) ⟨1609844, by rfl⟩ : syracuseStep 8585837 = 3219689) B3219689
theorem B2384761 : Blo 1411525 2384761 := bstep (se 2 (by rfl) ⟨894285, by rfl⟩ : syracuseStep 2384761 = 1788571) B1788571
theorem B10724561 : Blo 1411525 10724561 := bstep (se 2 (by rfl) ⟨4021710, by rfl⟩ : syracuseStep 10724561 = 8043421) B8043421
theorem B1787447 : Blo 1411525 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B2148187 : Blo 1411525 2148187 := bstep (se 1 (by rfl) ⟨1611140, by rfl⟩ : syracuseStep 2148187 = 3222281) B3222281
theorem B88156583 : Blo 1411525 88156583 := bstep (se 1 (by rfl) ⟨66117437, by rfl⟩ : syracuseStep 88156583 = 132234875) B132234875
theorem B247769603 : Blo 1411525 247769603 := bstep (se 1 (by rfl) ⟨185827202, by rfl⟩ : syracuseStep 247769603 = 371654405) B371654405
theorem B10185263 : Blo 1411525 10185263 := bstep (se 1 (by rfl) ⟨7638947, by rfl⟩ : syracuseStep 10185263 = 15277895) B15277895
theorem B15895223 : Blo 1411525 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B8047295 : Blo 1411525 8047295 := bstep (se 1 (by rfl) ⟨6035471, by rfl⟩ : syracuseStep 8047295 = 12070943) B12070943
theorem B2009819 : Blo 1411525 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B2263879 : Blo 1411525 2263879 := bstep (se 1 (by rfl) ⟨1697909, by rfl⟩ : syracuseStep 2263879 = 3395819) B3395819
theorem B1411943 : Blo 1411525 1411943 := bstep (se 1 (by rfl) ⟨1058957, by rfl⟩ : syracuseStep 1411943 = 2117915) B2117915
theorem B1411967 : Blo 1411525 1411967 := bstep (se 1 (by rfl) ⟨1058975, by rfl⟩ : syracuseStep 1411967 = 2117951) B2117951
theorem B5090471 : Blo 1411525 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B2862335 : Blo 1411525 2862335 := bstep (se 1 (by rfl) ⟨2146751, by rfl⟩ : syracuseStep 2862335 = 4293503) B4293503
theorem B146869625 : Blo 1411525 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B1412511 : Blo 1411525 1412511 := bstep (se 1 (by rfl) ⟨1059383, by rfl⟩ : syracuseStep 1412511 = 2118767) B2118767
theorem B2117375 : Blo 1411525 2117375 := bstep (se 1 (by rfl) ⟨1588031, by rfl⟩ : syracuseStep 2117375 = 3176063) B3176063
theorem B2117543 : Blo 1411525 2117543 := bstep (se 1 (by rfl) ⟨1588157, by rfl⟩ : syracuseStep 2117543 = 3176315) B3176315
theorem B2117723 : Blo 1411525 2117723 := bstep (se 1 (by rfl) ⟨1588292, by rfl⟩ : syracuseStep 2117723 = 3176585) B3176585
theorem B3575947 : Blo 1411525 3575947 := bstep (se 1 (by rfl) ⟨2681960, by rfl⟩ : syracuseStep 3575947 = 5363921) B5363921
theorem B1413279 : Blo 1411525 1413279 := bstep (se 1 (by rfl) ⟨1059959, by rfl⟩ : syracuseStep 1413279 = 2119919) B2119919
theorem B16093403 : Blo 1411525 16093403 := bstep (se 1 (by rfl) ⟨12070052, by rfl⟩ : syracuseStep 16093403 = 24140105) B24140105
theorem B18092321 : Blo 1411525 18092321 := bstep (se 2 (by rfl) ⟨6784620, by rfl⟩ : syracuseStep 18092321 = 13569241) B13569241
theorem B2117927 : Blo 1411525 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B2118185 : Blo 1411525 2118185 := bstep (se 2 (by rfl) ⟨794319, by rfl⟩ : syracuseStep 2118185 = 1588639) B1588639
theorem B2118395 : Blo 1411525 2118395 := bstep (se 1 (by rfl) ⟨1588796, by rfl⟩ : syracuseStep 2118395 = 3177593) B3177593
theorem B2118527 : Blo 1411525 2118527 := bstep (se 1 (by rfl) ⟨1588895, by rfl⟩ : syracuseStep 2118527 = 3177791) B3177791
theorem B20362337 : Blo 1411525 20362337 := bstep (se 2 (by rfl) ⟨7635876, by rfl⟩ : syracuseStep 20362337 = 15271753) B15271753
theorem B2118887 : Blo 1411525 2118887 := bstep (se 1 (by rfl) ⟨1589165, by rfl⟩ : syracuseStep 2118887 = 3178331) B3178331
theorem B2119259 : Blo 1411525 2119259 := bstep (se 1 (by rfl) ⟨1589444, by rfl⟩ : syracuseStep 2119259 = 3178889) B3178889
theorem B2717321 : Blo 1411525 2717321 := bstep (se 2 (by rfl) ⟨1018995, by rfl⟩ : syracuseStep 2717321 = 2037991) B2037991
theorem B3577567 : Blo 1411525 3577567 := bstep (se 1 (by rfl) ⟨2683175, by rfl⟩ : syracuseStep 3577567 = 5366351) B5366351
theorem B7149383 : Blo 1411525 7149383 := bstep (se 1 (by rfl) ⟨5362037, by rfl⟩ : syracuseStep 7149383 = 10724075) B10724075
theorem B1611775 : Blo 1411525 1611775 := bstep (se 1 (by rfl) ⟨1208831, by rfl⟩ : syracuseStep 1611775 = 2417663) B2417663
theorem B19593235 : Blo 1411525 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B3176801 : Blo 1411525 3176801 := bstep (se 2 (by rfl) ⟨1191300, by rfl⟩ : syracuseStep 3176801 = 2382601) B2382601
theorem B5364089 : Blo 1411525 5364089 := bstep (se 2 (by rfl) ⟨2011533, by rfl⟩ : syracuseStep 5364089 = 4023067) B4023067
theorem B2120171 : Blo 1411525 2120171 := bstep (se 1 (by rfl) ⟨1590128, by rfl⟩ : syracuseStep 2120171 = 3180257) B3180257
theorem B27155159 : Blo 1411525 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B3177215 : Blo 1411525 3177215 := bstep (se 1 (by rfl) ⟨2382911, by rfl⟩ : syracuseStep 3177215 = 4765823) B4765823
theorem B44112761 : Blo 1411525 44112761 := bstep (se 2 (by rfl) ⟨16542285, by rfl⟩ : syracuseStep 44112761 = 33084571) B33084571
theorem B9665527 : Blo 1411525 9665527 := bstep (se 1 (by rfl) ⟨7249145, by rfl⟩ : syracuseStep 9665527 = 14498291) B14498291
theorem B2448559 : Blo 1411525 2448559 := bstep (se 1 (by rfl) ⟨1836419, by rfl⟩ : syracuseStep 2448559 = 3672839) B3672839
theorem B10722617 : Blo 1411525 10722617 := bstep (se 2 (by rfl) ⟨4020981, by rfl⟩ : syracuseStep 10722617 = 8041963) B8041963
theorem B30539177 : Blo 1411525 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B2383391 : Blo 1411525 2383391 := bstep (se 1 (by rfl) ⟨1787543, by rfl⟩ : syracuseStep 2383391 = 3575087) B3575087
theorem B4767389 : Blo 1411525 4767389 := bstep (se 3 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 4767389 = 1787771) B1787771
theorem B104472443 : Blo 1411525 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B3178367 : Blo 1411525 3178367 := bstep (se 1 (by rfl) ⟨2383775, by rfl⟩ : syracuseStep 3178367 = 4767551) B4767551
theorem B36216719 : Blo 1411525 36216719 := bstep (se 1 (by rfl) ⟨27162539, by rfl⟩ : syracuseStep 36216719 = 54325079) B54325079
theorem B104497253 : Blo 1411525 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B4767929 : Blo 1411525 4767929 := bstep (se 2 (by rfl) ⟨1787973, by rfl⟩ : syracuseStep 4767929 = 3575947) B3575947
theorem B13574891 : Blo 1411525 13574891 := bstep (se 1 (by rfl) ⟨10181168, by rfl⟩ : syracuseStep 13574891 = 20362337) B20362337
theorem B13058981 : Blo 1411525 13058981 := bstep (se 4 (by rfl) ⟨1224279, by rfl⟩ : syracuseStep 13058981 = 2448559) B2448559
theorem B3179681 : Blo 1411525 3179681 := bstep (se 2 (by rfl) ⟨1192380, by rfl⟩ : syracuseStep 3179681 = 2384761) B2384761
theorem B12887369 : Blo 1411525 12887369 := bstep (se 2 (by rfl) ⟨4832763, by rfl⟩ : syracuseStep 12887369 = 9665527) B9665527
theorem B58771055 : Blo 1411525 58771055 := bstep (se 1 (by rfl) ⟨44078291, by rfl⟩ : syracuseStep 58771055 = 88156583) B88156583
theorem B5359517 : Blo 1411525 5359517 := bstep (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) B2009819
theorem B3393647 : Blo 1411525 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B97913083 : Blo 1411525 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B20359451 : Blo 1411525 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B4770089 : Blo 1411525 4770089 := bstep (se 2 (by rfl) ⟨1788783, by rfl⟩ : syracuseStep 4770089 = 3577567) B3577567
theorem B1411583 : Blo 1411525 1411583 := bstep (se 1 (by rfl) ⟨1058687, by rfl⟩ : syracuseStep 1411583 = 2117375) B2117375
theorem B24144479 : Blo 1411525 24144479 := bstep (se 1 (by rfl) ⟨18108359, by rfl⟩ : syracuseStep 24144479 = 36216719) B36216719
theorem B1411695 : Blo 1411525 1411695 := bstep (se 1 (by rfl) ⟨1058771, by rfl⟩ : syracuseStep 1411695 = 2117543) B2117543
theorem B2149033 : Blo 1411525 2149033 := bstep (se 2 (by rfl) ⟨805887, by rfl⟩ : syracuseStep 2149033 = 1611775) B1611775
theorem B1411815 : Blo 1411525 1411815 := bstep (se 1 (by rfl) ⟨1058861, by rfl⟩ : syracuseStep 1411815 = 2117723) B2117723
theorem B12061547 : Blo 1411525 12061547 := bstep (se 1 (by rfl) ⟨9046160, by rfl⟩ : syracuseStep 12061547 = 18092321) B18092321
theorem B1411951 : Blo 1411525 1411951 := bstep (se 1 (by rfl) ⟨1058963, by rfl⟩ : syracuseStep 1411951 = 2117927) B2117927
theorem B1412123 : Blo 1411525 1412123 := bstep (se 1 (by rfl) ⟨1059092, by rfl⟩ : syracuseStep 1412123 = 2118185) B2118185
theorem B9055259 : Blo 1411525 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B1412263 : Blo 1411525 1412263 := bstep (se 1 (by rfl) ⟨1059197, by rfl⟩ : syracuseStep 1412263 = 2118395) B2118395
theorem B1412351 : Blo 1411525 1412351 := bstep (se 1 (by rfl) ⟨1059263, by rfl⟩ : syracuseStep 1412351 = 2118527) B2118527
theorem B1412591 : Blo 1411525 1412591 := bstep (se 1 (by rfl) ⟨1059443, by rfl⟩ : syracuseStep 1412591 = 2118887) B2118887
theorem B1412839 : Blo 1411525 1412839 := bstep (se 1 (by rfl) ⟨1059629, by rfl⟩ : syracuseStep 1412839 = 2119259) B2119259
theorem B3018505 : Blo 1411525 3018505 := bstep (se 2 (by rfl) ⟨1131939, by rfl⟩ : syracuseStep 3018505 = 2263879) B2263879
theorem B2117867 : Blo 1411525 2117867 := bstep (se 1 (by rfl) ⟨1588400, by rfl⟩ : syracuseStep 2117867 = 3176801) B3176801
theorem B3576059 : Blo 1411525 3576059 := bstep (se 1 (by rfl) ⟨2682044, by rfl⟩ : syracuseStep 3576059 = 5364089) B5364089
theorem B1413447 : Blo 1411525 1413447 := bstep (se 1 (by rfl) ⟨1060085, by rfl⟩ : syracuseStep 1413447 = 2120171) B2120171
theorem B165179735 : Blo 1411525 165179735 := bstep (se 1 (by rfl) ⟨123884801, by rfl⟩ : syracuseStep 165179735 = 247769603) B247769603
theorem B7246189 : Blo 1411525 7246189 := bstep (se 3 (by rfl) ⟨1358660, by rfl⟩ : syracuseStep 7246189 = 2717321) B2717321
theorem B10596815 : Blo 1411525 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B2118143 : Blo 1411525 2118143 := bstep (se 1 (by rfl) ⟨1588607, by rfl⟩ : syracuseStep 2118143 = 3177215) B3177215
theorem B7148411 : Blo 1411525 7148411 := bstep (se 1 (by rfl) ⟨5361308, by rfl⟩ : syracuseStep 7148411 = 10722617) B10722617
theorem B2864249 : Blo 1411525 2864249 := bstep (se 2 (by rfl) ⟨1074093, by rfl⟩ : syracuseStep 2864249 = 2148187) B2148187
theorem B2118911 : Blo 1411525 2118911 := bstep (se 1 (by rfl) ⟨1589183, by rfl⟩ : syracuseStep 2118911 = 3178367) B3178367
theorem B10728935 : Blo 1411525 10728935 := bstep (se 1 (by rfl) ⟨8046701, by rfl⟩ : syracuseStep 10728935 = 16093403) B16093403
theorem B5723891 : Blo 1411525 5723891 := bstep (se 1 (by rfl) ⟨4292918, by rfl⟩ : syracuseStep 5723891 = 8585837) B8585837
theorem B7632893 : Blo 1411525 7632893 := bstep (se 3 (by rfl) ⟨1431167, by rfl⟩ : syracuseStep 7632893 = 2862335) B2862335
theorem B7149707 : Blo 1411525 7149707 := bstep (se 1 (by rfl) ⟨5362280, by rfl⟩ : syracuseStep 7149707 = 10724561) B10724561
theorem B4766255 : Blo 1411525 4766255 := bstep (se 1 (by rfl) ⟨3574691, by rfl⟩ : syracuseStep 4766255 = 7149383) B7149383
theorem B4766525 : Blo 1411525 4766525 := bstep (se 3 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 4766525 = 1787447) B1787447
theorem B6790175 : Blo 1411525 6790175 := bstep (se 1 (by rfl) ⟨5092631, by rfl⟩ : syracuseStep 6790175 = 10185263) B10185263
theorem B5364863 : Blo 1411525 5364863 := bstep (se 1 (by rfl) ⟨4023647, by rfl⟩ : syracuseStep 5364863 = 8047295) B8047295
theorem B18103439 : Blo 1411525 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B29408507 : Blo 1411525 29408507 := bstep (se 1 (by rfl) ⟨22056380, by rfl⟩ : syracuseStep 29408507 = 44112761) B44112761
theorem B278593181 : Blo 1411525 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B1588927 : Blo 1411525 1588927 := bstep (se 1 (by rfl) ⟨1191695, by rfl⟩ : syracuseStep 1588927 = 2383391) B2383391
theorem B3178259 : Blo 1411525 3178259 := bstep (se 1 (by rfl) ⟨2383694, by rfl⟩ : syracuseStep 3178259 = 4767389) B4767389
theorem B69664835 : Blo 1411525 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B3178619 : Blo 1411525 3178619 := bstep (se 1 (by rfl) ⟨2383964, by rfl⟩ : syracuseStep 3178619 = 4767929) B4767929
theorem B2384039 : Blo 1411525 2384039 := bstep (se 1 (by rfl) ⟨1788029, by rfl⟩ : syracuseStep 2384039 = 3576059) B3576059
theorem B1909499 : Blo 1411525 1909499 := bstep (se 1 (by rfl) ⟨1432124, by rfl⟩ : syracuseStep 1909499 = 2864249) B2864249
theorem B7152623 : Blo 1411525 7152623 := bstep (se 1 (by rfl) ⟨5364467, by rfl⟩ : syracuseStep 7152623 = 10728935) B10728935
theorem B3573011 : Blo 1411525 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B5088595 : Blo 1411525 5088595 := bstep (se 1 (by rfl) ⟨3816446, by rfl⟩ : syracuseStep 5088595 = 7632893) B7632893
theorem B2262431 : Blo 1411525 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B3180059 : Blo 1411525 3180059 := bstep (se 1 (by rfl) ⟨2385044, by rfl⟩ : syracuseStep 3180059 = 4770089) B4770089
theorem B156722813 : Blo 1411525 156722813 := bstep (se 3 (by rfl) ⟨29385527, by rfl⟩ : syracuseStep 156722813 = 58771055) B58771055
theorem B12068959 : Blo 1411525 12068959 := bstep (se 1 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 12068959 = 18103439) B18103439
theorem B19605671 : Blo 1411525 19605671 := bstep (se 1 (by rfl) ⟨14704253, by rfl⟩ : syracuseStep 19605671 = 29408507) B29408507
theorem B4024673 : Blo 1411525 4024673 := bstep (se 2 (by rfl) ⟨1509252, by rfl⟩ : syracuseStep 4024673 = 3018505) B3018505
theorem B1411911 : Blo 1411525 1411911 := bstep (se 1 (by rfl) ⟨1058933, by rfl⟩ : syracuseStep 1411911 = 2117867) B2117867
theorem B110119823 : Blo 1411525 110119823 := bstep (se 1 (by rfl) ⟨82589867, by rfl⟩ : syracuseStep 110119823 = 165179735) B165179735
theorem B7064543 : Blo 1411525 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B130550777 : Blo 1411525 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B1412095 : Blo 1411525 1412095 := bstep (se 1 (by rfl) ⟨1059071, by rfl⟩ : syracuseStep 1412095 = 2118143) B2118143
theorem B1412607 : Blo 1411525 1412607 := bstep (se 1 (by rfl) ⟨1059455, by rfl⟩ : syracuseStep 1412607 = 2118911) B2118911
theorem B38646341 : Blo 1411525 38646341 := bstep (se 4 (by rfl) ⟨3623094, by rfl⟩ : syracuseStep 38646341 = 7246189) B7246189
theorem B8041031 : Blo 1411525 8041031 := bstep (se 1 (by rfl) ⟨6030773, by rfl⟩ : syracuseStep 8041031 = 12061547) B12061547
theorem B4526783 : Blo 1411525 4526783 := bstep (se 1 (by rfl) ⟨3395087, by rfl⟩ : syracuseStep 4526783 = 6790175) B6790175
theorem B3576575 : Blo 1411525 3576575 := bstep (se 1 (by rfl) ⟨2682431, by rfl⟩ : syracuseStep 3576575 = 5364863) B5364863
theorem B2118569 : Blo 1411525 2118569 := bstep (se 2 (by rfl) ⟨794463, by rfl⟩ : syracuseStep 2118569 = 1588927) B1588927
theorem B2118839 : Blo 1411525 2118839 := bstep (se 1 (by rfl) ⟨1589129, by rfl⟩ : syracuseStep 2118839 = 3178259) B3178259
theorem B9049927 : Blo 1411525 9049927 := bstep (se 1 (by rfl) ⟨6787445, by rfl⟩ : syracuseStep 9049927 = 13574891) B13574891
theorem B4765607 : Blo 1411525 4765607 := bstep (se 1 (by rfl) ⟨3574205, by rfl⟩ : syracuseStep 4765607 = 7148411) B7148411
theorem B8705987 : Blo 1411525 8705987 := bstep (se 1 (by rfl) ⟨6529490, by rfl⟩ : syracuseStep 8705987 = 13058981) B13058981
theorem B2119787 : Blo 1411525 2119787 := bstep (se 1 (by rfl) ⟨1589840, by rfl⟩ : syracuseStep 2119787 = 3179681) B3179681
theorem B8591579 : Blo 1411525 8591579 := bstep (se 1 (by rfl) ⟨6443684, by rfl⟩ : syracuseStep 8591579 = 12887369) B12887369
theorem B2865377 : Blo 1411525 2865377 := bstep (se 2 (by rfl) ⟨1074516, by rfl⟩ : syracuseStep 2865377 = 2149033) B2149033
theorem B3815927 : Blo 1411525 3815927 := bstep (se 1 (by rfl) ⟨2861945, by rfl⟩ : syracuseStep 3815927 = 5723891) B5723891
theorem B4766471 : Blo 1411525 4766471 := bstep (se 1 (by rfl) ⟨3574853, by rfl⟩ : syracuseStep 4766471 = 7149707) B7149707
theorem B13572967 : Blo 1411525 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B3177503 : Blo 1411525 3177503 := bstep (se 1 (by rfl) ⟨2383127, by rfl⟩ : syracuseStep 3177503 = 4766255) B4766255
theorem B16096319 : Blo 1411525 16096319 := bstep (se 1 (by rfl) ⟨12072239, by rfl⟩ : syracuseStep 16096319 = 24144479) B24144479
theorem B3177683 : Blo 1411525 3177683 := bstep (se 1 (by rfl) ⟨2383262, by rfl⟩ : syracuseStep 3177683 = 4766525) B4766525
theorem B6036839 : Blo 1411525 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B185728787 : Blo 1411525 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B1589359 : Blo 1411525 1589359 := bstep (se 1 (by rfl) ⟨1192019, by rfl⟩ : syracuseStep 1589359 = 2384039) B2384039
theorem B25764227 : Blo 1411525 25764227 := bstep (se 1 (by rfl) ⟨19323170, by rfl⟩ : syracuseStep 25764227 = 38646341) B38646341
theorem B2384383 : Blo 1411525 2384383 := bstep (se 1 (by rfl) ⟨1788287, by rfl⟩ : syracuseStep 2384383 = 3576575) B3576575
theorem B4768415 : Blo 1411525 4768415 := bstep (se 1 (by rfl) ⟨3576311, by rfl⟩ : syracuseStep 4768415 = 7152623) B7152623
theorem B104481875 : Blo 1411525 104481875 := bstep (se 1 (by rfl) ⟨78361406, by rfl⟩ : syracuseStep 104481875 = 156722813) B156722813
theorem B18097289 : Blo 1411525 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B5727719 : Blo 1411525 5727719 := bstep (se 1 (by rfl) ⟨4295789, by rfl⟩ : syracuseStep 5727719 = 8591579) B8591579
theorem B1910251 : Blo 1411525 1910251 := bstep (se 1 (by rfl) ⟨1432688, by rfl⟩ : syracuseStep 1910251 = 2865377) B2865377
theorem B6784793 : Blo 1411525 6784793 := bstep (se 2 (by rfl) ⟨2544297, by rfl⟩ : syracuseStep 6784793 = 5088595) B5088595
theorem B87033851 : Blo 1411525 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B4024559 : Blo 1411525 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B46443223 : Blo 1411525 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B16091945 : Blo 1411525 16091945 := bstep (se 2 (by rfl) ⟨6034479, by rfl⟩ : syracuseStep 16091945 = 12068959) B12068959
theorem B5360687 : Blo 1411525 5360687 := bstep (se 1 (by rfl) ⟨4020515, by rfl⟩ : syracuseStep 5360687 = 8041031) B8041031
theorem B3017855 : Blo 1411525 3017855 := bstep (se 1 (by rfl) ⟨2263391, by rfl⟩ : syracuseStep 3017855 = 4526783) B4526783
theorem B1412379 : Blo 1411525 1412379 := bstep (se 1 (by rfl) ⟨1059284, by rfl⟩ : syracuseStep 1412379 = 2118569) B2118569
theorem B1412559 : Blo 1411525 1412559 := bstep (se 1 (by rfl) ⟨1059419, by rfl⟩ : syracuseStep 1412559 = 2118839) B2118839
theorem B6033149 : Blo 1411525 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B5803991 : Blo 1411525 5803991 := bstep (se 1 (by rfl) ⟨4352993, by rfl⟩ : syracuseStep 5803991 = 8705987) B8705987
theorem B1413191 : Blo 1411525 1413191 := bstep (se 1 (by rfl) ⟨1059893, by rfl⟩ : syracuseStep 1413191 = 2119787) B2119787
theorem B13070447 : Blo 1411525 13070447 := bstep (se 1 (by rfl) ⟨9802835, by rfl⟩ : syracuseStep 13070447 = 19605671) B19605671
theorem B2683115 : Blo 1411525 2683115 := bstep (se 1 (by rfl) ⟨2012336, by rfl⟩ : syracuseStep 2683115 = 4024673) B4024673
theorem B2543951 : Blo 1411525 2543951 := bstep (se 1 (by rfl) ⟨1907963, by rfl⟩ : syracuseStep 2543951 = 3815927) B3815927
theorem B73413215 : Blo 1411525 73413215 := bstep (se 1 (by rfl) ⟨55059911, by rfl⟩ : syracuseStep 73413215 = 110119823) B110119823
theorem B5091997 : Blo 1411525 5091997 := bstep (se 3 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 5091997 = 1909499) B1909499
theorem B2118335 : Blo 1411525 2118335 := bstep (se 1 (by rfl) ⟨1588751, by rfl⟩ : syracuseStep 2118335 = 3177503) B3177503
theorem B2118455 : Blo 1411525 2118455 := bstep (se 1 (by rfl) ⟨1588841, by rfl⟩ : syracuseStep 2118455 = 3177683) B3177683
theorem B123819191 : Blo 1411525 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B18838781 : Blo 1411525 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B2119079 : Blo 1411525 2119079 := bstep (se 1 (by rfl) ⟨1589309, by rfl⟩ : syracuseStep 2119079 = 3178619) B3178619
theorem B2382007 : Blo 1411525 2382007 := bstep (se 1 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 2382007 = 3573011) B3573011
theorem B2120039 : Blo 1411525 2120039 := bstep (se 1 (by rfl) ⟨1590029, by rfl⟩ : syracuseStep 2120039 = 3180059) B3180059
theorem B3177071 : Blo 1411525 3177071 := bstep (se 1 (by rfl) ⟨2382803, by rfl⟩ : syracuseStep 3177071 = 4765607) B4765607
theorem B3177647 : Blo 1411525 3177647 := bstep (se 1 (by rfl) ⟨2383235, by rfl⟩ : syracuseStep 3177647 = 4766471) B4766471
theorem B10730879 : Blo 1411525 10730879 := bstep (se 1 (by rfl) ⟨8048159, by rfl⟩ : syracuseStep 10730879 = 16096319) B16096319
theorem B12066569 : Blo 1411525 12066569 := bstep (se 2 (by rfl) ⟨4524963, by rfl⟩ : syracuseStep 12066569 = 9049927) B9049927
theorem B3178943 : Blo 1411525 3178943 := bstep (se 1 (by rfl) ⟨2384207, by rfl⟩ : syracuseStep 3178943 = 4768415) B4768415
theorem B3179177 : Blo 1411525 3179177 := bstep (se 2 (by rfl) ⟨1192191, by rfl⟩ : syracuseStep 3179177 = 2384383) B2384383
theorem B12559187 : Blo 1411525 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B6783869 : Blo 1411525 6783869 := bstep (se 3 (by rfl) ⟨1271975, by rfl⟩ : syracuseStep 6783869 = 2543951) B2543951
theorem B61924297 : Blo 1411525 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B4523195 : Blo 1411525 4523195 := bstep (se 1 (by rfl) ⟨3392396, by rfl⟩ : syracuseStep 4523195 = 6784793) B6784793
theorem B3573791 : Blo 1411525 3573791 := bstep (se 1 (by rfl) ⟨2680343, by rfl⟩ : syracuseStep 3573791 = 5360687) B5360687
theorem B7153919 : Blo 1411525 7153919 := bstep (se 1 (by rfl) ⟨5365439, by rfl⟩ : syracuseStep 7153919 = 10730879) B10730879
theorem B3869327 : Blo 1411525 3869327 := bstep (se 1 (by rfl) ⟨2901995, by rfl⟩ : syracuseStep 3869327 = 5803991) B5803991
theorem B1788743 : Blo 1411525 1788743 := bstep (se 1 (by rfl) ⟨1341557, by rfl⟩ : syracuseStep 1788743 = 2683115) B2683115
theorem B8047613 : Blo 1411525 8047613 := bstep (se 3 (by rfl) ⟨1508927, by rfl⟩ : syracuseStep 8047613 = 3017855) B3017855
theorem B48942143 : Blo 1411525 48942143 := bstep (se 1 (by rfl) ⟨36706607, by rfl⟩ : syracuseStep 48942143 = 73413215) B73413215
theorem B1412223 : Blo 1411525 1412223 := bstep (se 1 (by rfl) ⟨1059167, by rfl⟩ : syracuseStep 1412223 = 2118335) B2118335
theorem B1412303 : Blo 1411525 1412303 := bstep (se 1 (by rfl) ⟨1059227, by rfl⟩ : syracuseStep 1412303 = 2118455) B2118455
theorem B82546127 : Blo 1411525 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B1412719 : Blo 1411525 1412719 := bstep (se 1 (by rfl) ⟨1059539, by rfl⟩ : syracuseStep 1412719 = 2119079) B2119079
theorem B15273917 : Blo 1411525 15273917 := bstep (se 3 (by rfl) ⟨2863859, by rfl⟩ : syracuseStep 15273917 = 5727719) B5727719
theorem B2683039 : Blo 1411525 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B1413359 : Blo 1411525 1413359 := bstep (se 1 (by rfl) ⟨1060019, by rfl⟩ : syracuseStep 1413359 = 2120039) B2120039
theorem B2118047 : Blo 1411525 2118047 := bstep (se 1 (by rfl) ⟨1588535, by rfl⟩ : syracuseStep 2118047 = 3177071) B3177071
theorem B10727963 : Blo 1411525 10727963 := bstep (se 1 (by rfl) ⟨8045972, by rfl⟩ : syracuseStep 10727963 = 16091945) B16091945
theorem B2118431 : Blo 1411525 2118431 := bstep (se 1 (by rfl) ⟨1588823, by rfl⟩ : syracuseStep 2118431 = 3177647) B3177647
theorem B8713631 : Blo 1411525 8713631 := bstep (se 1 (by rfl) ⟨6535223, by rfl⟩ : syracuseStep 8713631 = 13070447) B13070447
theorem B2119145 : Blo 1411525 2119145 := bstep (se 2 (by rfl) ⟨794679, by rfl⟩ : syracuseStep 2119145 = 1589359) B1589359
theorem B3176009 : Blo 1411525 3176009 := bstep (se 2 (by rfl) ⟨1191003, by rfl⟩ : syracuseStep 3176009 = 2382007) B2382007
theorem B17176151 : Blo 1411525 17176151 := bstep (se 1 (by rfl) ⟨12882113, by rfl⟩ : syracuseStep 17176151 = 25764227) B25764227
theorem B69654583 : Blo 1411525 69654583 := bstep (se 1 (by rfl) ⟨52240937, by rfl⟩ : syracuseStep 69654583 = 104481875) B104481875
theorem B12064859 : Blo 1411525 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B6789329 : Blo 1411525 6789329 := bstep (se 2 (by rfl) ⟨2545998, by rfl⟩ : syracuseStep 6789329 = 5091997) B5091997
theorem B58022567 : Blo 1411525 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B2547001 : Blo 1411525 2547001 := bstep (se 2 (by rfl) ⟨955125, by rfl⟩ : syracuseStep 2547001 = 1910251) B1910251
theorem B4022099 : Blo 1411525 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B8044379 : Blo 1411525 8044379 := bstep (se 1 (by rfl) ⟨6033284, by rfl⟩ : syracuseStep 8044379 = 12066569) B12066569
theorem B92872777 : Blo 1411525 92872777 := bstep (se 2 (by rfl) ⟨34827291, by rfl⟩ : syracuseStep 92872777 = 69654583) B69654583
theorem B7151975 : Blo 1411525 7151975 := bstep (se 1 (by rfl) ⟨5363981, by rfl⟩ : syracuseStep 7151975 = 10727963) B10727963
theorem B8372791 : Blo 1411525 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B3015463 : Blo 1411525 3015463 := bstep (se 1 (by rfl) ⟨2261597, by rfl⟩ : syracuseStep 3015463 = 4523195) B4523195
theorem B5809087 : Blo 1411525 5809087 := bstep (se 1 (by rfl) ⟨4356815, by rfl⟩ : syracuseStep 5809087 = 8713631) B8713631
theorem B4769279 : Blo 1411525 4769279 := bstep (se 1 (by rfl) ⟨3576959, by rfl⟩ : syracuseStep 4769279 = 7153919) B7153919
theorem B4769981 : Blo 1411525 4769981 := bstep (se 3 (by rfl) ⟨894371, by rfl⟩ : syracuseStep 4769981 = 1788743) B1788743
theorem B18090317 : Blo 1411525 18090317 := bstep (se 3 (by rfl) ⟨3391934, by rfl⟩ : syracuseStep 18090317 = 6783869) B6783869
theorem B2681399 : Blo 1411525 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B1412031 : Blo 1411525 1412031 := bstep (se 1 (by rfl) ⟨1059023, by rfl⟩ : syracuseStep 1412031 = 2118047) B2118047
theorem B1412287 : Blo 1411525 1412287 := bstep (se 1 (by rfl) ⟨1059215, by rfl⟩ : syracuseStep 1412287 = 2118431) B2118431
theorem B1412763 : Blo 1411525 1412763 := bstep (se 1 (by rfl) ⟨1059572, by rfl⟩ : syracuseStep 1412763 = 2119145) B2119145
theorem B2117339 : Blo 1411525 2117339 := bstep (se 1 (by rfl) ⟨1588004, by rfl⟩ : syracuseStep 2117339 = 3176009) B3176009
theorem B4526219 : Blo 1411525 4526219 := bstep (se 1 (by rfl) ⟨3394664, by rfl⟩ : syracuseStep 4526219 = 6789329) B6789329
theorem B10318205 : Blo 1411525 10318205 := bstep (se 3 (by rfl) ⟨1934663, by rfl⟩ : syracuseStep 10318205 = 3869327) B3869327
theorem B3396001 : Blo 1411525 3396001 := bstep (se 2 (by rfl) ⟨1273500, by rfl⟩ : syracuseStep 3396001 = 2547001) B2547001
theorem B55030751 : Blo 1411525 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B5362919 : Blo 1411525 5362919 := bstep (se 1 (by rfl) ⟨4022189, by rfl⟩ : syracuseStep 5362919 = 8044379) B8044379
theorem B3577385 : Blo 1411525 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B2119295 : Blo 1411525 2119295 := bstep (se 1 (by rfl) ⟨1589471, by rfl⟩ : syracuseStep 2119295 = 3178943) B3178943
theorem B2119451 : Blo 1411525 2119451 := bstep (se 1 (by rfl) ⟨1589588, by rfl⟩ : syracuseStep 2119451 = 3179177) B3179177
theorem B11450767 : Blo 1411525 11450767 := bstep (se 1 (by rfl) ⟨8588075, by rfl⟩ : syracuseStep 11450767 = 17176151) B17176151
theorem B82565729 : Blo 1411525 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B2382527 : Blo 1411525 2382527 := bstep (se 1 (by rfl) ⟨1786895, by rfl⟩ : syracuseStep 2382527 = 3573791) B3573791
theorem B8043239 : Blo 1411525 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B38681711 : Blo 1411525 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B5365075 : Blo 1411525 5365075 := bstep (se 1 (by rfl) ⟨4023806, by rfl⟩ : syracuseStep 5365075 = 8047613) B8047613
theorem B32628095 : Blo 1411525 32628095 := bstep (se 1 (by rfl) ⟨24471071, by rfl⟩ : syracuseStep 32628095 = 48942143) B48942143
theorem B10182611 : Blo 1411525 10182611 := bstep (se 1 (by rfl) ⟨7636958, by rfl⟩ : syracuseStep 10182611 = 15273917) B15273917
theorem B123830369 : Blo 1411525 123830369 := bstep (se 2 (by rfl) ⟨46436388, by rfl⟩ : syracuseStep 123830369 = 92872777) B92872777
theorem B4767983 : Blo 1411525 4767983 := bstep (se 1 (by rfl) ⟨3575987, by rfl⟩ : syracuseStep 4767983 = 7151975) B7151975
theorem B44654885 : Blo 1411525 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B3179519 : Blo 1411525 3179519 := bstep (se 1 (by rfl) ⟨2384639, by rfl⟩ : syracuseStep 3179519 = 4769279) B4769279
theorem B2384923 : Blo 1411525 2384923 := bstep (se 1 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 2384923 = 3577385) B3577385
theorem B3179987 : Blo 1411525 3179987 := bstep (se 1 (by rfl) ⟨2384990, by rfl⟩ : syracuseStep 3179987 = 4769981) B4769981
theorem B12060211 : Blo 1411525 12060211 := bstep (se 1 (by rfl) ⟨9045158, by rfl⟩ : syracuseStep 12060211 = 18090317) B18090317
theorem B1787599 : Blo 1411525 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B55043819 : Blo 1411525 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B7153433 : Blo 1411525 7153433 := bstep (se 2 (by rfl) ⟨2682537, by rfl⟩ : syracuseStep 7153433 = 5365075) B5365075
theorem B21752063 : Blo 1411525 21752063 := bstep (se 1 (by rfl) ⟨16314047, by rfl⟩ : syracuseStep 21752063 = 32628095) B32628095
theorem B1411559 : Blo 1411525 1411559 := bstep (se 1 (by rfl) ⟨1058669, by rfl⟩ : syracuseStep 1411559 = 2117339) B2117339
theorem B12069917 : Blo 1411525 12069917 := bstep (se 3 (by rfl) ⟨2263109, by rfl⟩ : syracuseStep 12069917 = 4526219) B4526219
theorem B36687167 : Blo 1411525 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B3575279 : Blo 1411525 3575279 := bstep (se 1 (by rfl) ⟨2681459, by rfl⟩ : syracuseStep 3575279 = 5362919) B5362919
theorem B1412863 : Blo 1411525 1412863 := bstep (se 1 (by rfl) ⟨1059647, by rfl⟩ : syracuseStep 1412863 = 2119295) B2119295
theorem B1412967 : Blo 1411525 1412967 := bstep (se 1 (by rfl) ⟨1059725, by rfl⟩ : syracuseStep 1412967 = 2119451) B2119451
theorem B7745449 : Blo 1411525 7745449 := bstep (se 2 (by rfl) ⟨2904543, by rfl⟩ : syracuseStep 7745449 = 5809087) B5809087
theorem B5362159 : Blo 1411525 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B6788407 : Blo 1411525 6788407 := bstep (se 1 (by rfl) ⟨5091305, by rfl⟩ : syracuseStep 6788407 = 10182611) B10182611
theorem B15267689 : Blo 1411525 15267689 := bstep (se 2 (by rfl) ⟨5725383, by rfl⟩ : syracuseStep 15267689 = 11450767) B11450767
theorem B4528001 : Blo 1411525 4528001 := bstep (se 2 (by rfl) ⟨1698000, by rfl⟩ : syracuseStep 4528001 = 3396001) B3396001
theorem B27515213 : Blo 1411525 27515213 := bstep (se 3 (by rfl) ⟨5159102, by rfl⟩ : syracuseStep 27515213 = 10318205) B10318205
theorem B4020617 : Blo 1411525 4020617 := bstep (se 2 (by rfl) ⟨1507731, by rfl⟩ : syracuseStep 4020617 = 3015463) B3015463
theorem B1588351 : Blo 1411525 1588351 := bstep (se 1 (by rfl) ⟨1191263, by rfl⟩ : syracuseStep 1588351 = 2382527) B2382527
theorem B25787807 : Blo 1411525 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B3178655 : Blo 1411525 3178655 := bstep (se 1 (by rfl) ⟨2383991, by rfl⟩ : syracuseStep 3178655 = 4767983) B4767983
theorem B29769923 : Blo 1411525 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B4768955 : Blo 1411525 4768955 := bstep (se 1 (by rfl) ⟨3576716, by rfl⟩ : syracuseStep 4768955 = 7153433) B7153433
theorem B3179897 : Blo 1411525 3179897 := bstep (se 2 (by rfl) ⟨1192461, by rfl⟩ : syracuseStep 3179897 = 2384923) B2384923
theorem B14501375 : Blo 1411525 14501375 := bstep (se 1 (by rfl) ⟨10876031, by rfl⟩ : syracuseStep 14501375 = 21752063) B21752063
theorem B18343475 : Blo 1411525 18343475 := bstep (se 1 (by rfl) ⟨13757606, by rfl⟩ : syracuseStep 18343475 = 27515213) B27515213
theorem B8046611 : Blo 1411525 8046611 := bstep (se 1 (by rfl) ⟨6034958, by rfl⟩ : syracuseStep 8046611 = 12069917) B12069917
theorem B82553579 : Blo 1411525 82553579 := bstep (se 1 (by rfl) ⟨61915184, by rfl⟩ : syracuseStep 82553579 = 123830369) B123830369
theorem B36695879 : Blo 1411525 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B10178459 : Blo 1411525 10178459 := bstep (se 1 (by rfl) ⟨7633844, by rfl⟩ : syracuseStep 10178459 = 15267689) B15267689
theorem B2117801 : Blo 1411525 2117801 := bstep (se 2 (by rfl) ⟨794175, by rfl⟩ : syracuseStep 2117801 = 1588351) B1588351
theorem B24458111 : Blo 1411525 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B17191871 : Blo 1411525 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B10327265 : Blo 1411525 10327265 := bstep (se 2 (by rfl) ⟨3872724, by rfl⟩ : syracuseStep 10327265 = 7745449) B7745449
theorem B7149545 : Blo 1411525 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B2119679 : Blo 1411525 2119679 := bstep (se 1 (by rfl) ⟨1589759, by rfl⟩ : syracuseStep 2119679 = 3179519) B3179519
theorem B2119991 : Blo 1411525 2119991 := bstep (se 1 (by rfl) ⟨1589993, by rfl⟩ : syracuseStep 2119991 = 3179987) B3179987
theorem B10721645 : Blo 1411525 10721645 := bstep (se 3 (by rfl) ⟨2010308, by rfl⟩ : syracuseStep 10721645 = 4020617) B4020617
theorem B9051209 : Blo 1411525 9051209 := bstep (se 2 (by rfl) ⟨3394203, by rfl⟩ : syracuseStep 9051209 = 6788407) B6788407
theorem B16080281 : Blo 1411525 16080281 := bstep (se 2 (by rfl) ⟨6030105, by rfl⟩ : syracuseStep 16080281 = 12060211) B12060211
theorem B2383465 : Blo 1411525 2383465 := bstep (se 2 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 2383465 = 1787599) B1787599
theorem B2383519 : Blo 1411525 2383519 := bstep (se 1 (by rfl) ⟨1787639, by rfl⟩ : syracuseStep 2383519 = 3575279) B3575279
theorem B12074669 : Blo 1411525 12074669 := bstep (se 3 (by rfl) ⟨2264000, by rfl⟩ : syracuseStep 12074669 = 4528001) B4528001
theorem B11461247 : Blo 1411525 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B3179303 : Blo 1411525 3179303 := bstep (se 1 (by rfl) ⟨2384477, by rfl⟩ : syracuseStep 3179303 = 4768955) B4768955
theorem B9667583 : Blo 1411525 9667583 := bstep (se 1 (by rfl) ⟨7250687, by rfl⟩ : syracuseStep 9667583 = 14501375) B14501375
theorem B55035719 : Blo 1411525 55035719 := bstep (se 1 (by rfl) ⟨41276789, by rfl⟩ : syracuseStep 55035719 = 82553579) B82553579
theorem B24463919 : Blo 1411525 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B6785639 : Blo 1411525 6785639 := bstep (se 1 (by rfl) ⟨5089229, by rfl⟩ : syracuseStep 6785639 = 10178459) B10178459
theorem B1411867 : Blo 1411525 1411867 := bstep (se 1 (by rfl) ⟨1058900, by rfl⟩ : syracuseStep 1411867 = 2117801) B2117801
theorem B16305407 : Blo 1411525 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B6884843 : Blo 1411525 6884843 := bstep (se 1 (by rfl) ⟨5163632, by rfl⟩ : syracuseStep 6884843 = 10327265) B10327265
theorem B1413119 : Blo 1411525 1413119 := bstep (se 1 (by rfl) ⟨1059839, by rfl⟩ : syracuseStep 1413119 = 2119679) B2119679
theorem B1413327 : Blo 1411525 1413327 := bstep (se 1 (by rfl) ⟨1059995, by rfl⟩ : syracuseStep 1413327 = 2119991) B2119991
theorem B7147763 : Blo 1411525 7147763 := bstep (se 1 (by rfl) ⟨5360822, by rfl⟩ : syracuseStep 7147763 = 10721645) B10721645
theorem B6034139 : Blo 1411525 6034139 := bstep (se 1 (by rfl) ⟨4525604, by rfl⟩ : syracuseStep 6034139 = 9051209) B9051209
theorem B10720187 : Blo 1411525 10720187 := bstep (se 1 (by rfl) ⟨8040140, by rfl⟩ : syracuseStep 10720187 = 16080281) B16080281
theorem B8049779 : Blo 1411525 8049779 := bstep (se 1 (by rfl) ⟨6037334, by rfl⟩ : syracuseStep 8049779 = 12074669) B12074669
theorem B2119103 : Blo 1411525 2119103 := bstep (se 1 (by rfl) ⟨1589327, by rfl⟩ : syracuseStep 2119103 = 3178655) B3178655
theorem B19846615 : Blo 1411525 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B2119931 : Blo 1411525 2119931 := bstep (se 1 (by rfl) ⟨1589948, by rfl⟩ : syracuseStep 2119931 = 3179897) B3179897
theorem B12228983 : Blo 1411525 12228983 := bstep (se 1 (by rfl) ⟨9171737, by rfl⟩ : syracuseStep 12228983 = 18343475) B18343475
theorem B4766363 : Blo 1411525 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B5364407 : Blo 1411525 5364407 := bstep (se 1 (by rfl) ⟨4023305, by rfl⟩ : syracuseStep 5364407 = 8046611) B8046611
theorem B3177953 : Blo 1411525 3177953 := bstep (se 2 (by rfl) ⟨1191732, by rfl⟩ : syracuseStep 3177953 = 2383465) B2383465
theorem B3178025 : Blo 1411525 3178025 := bstep (se 2 (by rfl) ⟨1191759, by rfl⟩ : syracuseStep 3178025 = 2383519) B2383519
theorem B4022759 : Blo 1411525 4022759 := bstep (se 1 (by rfl) ⟨3017069, by rfl⟩ : syracuseStep 4022759 = 6034139) B6034139
theorem B5366519 : Blo 1411525 5366519 := bstep (se 1 (by rfl) ⟨4024889, by rfl⟩ : syracuseStep 5366519 = 8049779) B8049779
theorem B18359581 : Blo 1411525 18359581 := bstep (se 3 (by rfl) ⟨3442421, by rfl⟩ : syracuseStep 18359581 = 6884843) B6884843
theorem B8152655 : Blo 1411525 8152655 := bstep (se 1 (by rfl) ⟨6114491, by rfl⟩ : syracuseStep 8152655 = 12228983) B12228983
theorem B4523759 : Blo 1411525 4523759 := bstep (se 1 (by rfl) ⟨3392819, by rfl⟩ : syracuseStep 4523759 = 6785639) B6785639
theorem B26462153 : Blo 1411525 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B7146791 : Blo 1411525 7146791 := bstep (se 1 (by rfl) ⟨5360093, by rfl⟩ : syracuseStep 7146791 = 10720187) B10720187
theorem B1412735 : Blo 1411525 1412735 := bstep (se 1 (by rfl) ⟨1059551, by rfl⟩ : syracuseStep 1412735 = 2119103) B2119103
theorem B1413287 : Blo 1411525 1413287 := bstep (se 1 (by rfl) ⟨1059965, by rfl⟩ : syracuseStep 1413287 = 2119931) B2119931
theorem B3576271 : Blo 1411525 3576271 := bstep (se 1 (by rfl) ⟨2682203, by rfl⟩ : syracuseStep 3576271 = 5364407) B5364407
theorem B2118635 : Blo 1411525 2118635 := bstep (se 1 (by rfl) ⟨1588976, by rfl⟩ : syracuseStep 2118635 = 3177953) B3177953
theorem B2118683 : Blo 1411525 2118683 := bstep (se 1 (by rfl) ⟨1589012, by rfl⟩ : syracuseStep 2118683 = 3178025) B3178025
theorem B4765175 : Blo 1411525 4765175 := bstep (se 1 (by rfl) ⟨3573881, by rfl⟩ : syracuseStep 4765175 = 7147763) B7147763
theorem B7640831 : Blo 1411525 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B2119535 : Blo 1411525 2119535 := bstep (se 1 (by rfl) ⟨1589651, by rfl⟩ : syracuseStep 2119535 = 3179303) B3179303
theorem B6445055 : Blo 1411525 6445055 := bstep (se 1 (by rfl) ⟨4833791, by rfl⟩ : syracuseStep 6445055 = 9667583) B9667583
theorem B36690479 : Blo 1411525 36690479 := bstep (se 1 (by rfl) ⟨27517859, by rfl⟩ : syracuseStep 36690479 = 55035719) B55035719
theorem B16309279 : Blo 1411525 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B3177575 : Blo 1411525 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B10870271 : Blo 1411525 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B86982821 : Blo 1411525 86982821 := bstep (se 4 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 86982821 = 16309279) B16309279
theorem B4768361 : Blo 1411525 4768361 := bstep (se 2 (by rfl) ⟨1788135, by rfl⟩ : syracuseStep 4768361 = 3576271) B3576271
theorem B3015839 : Blo 1411525 3015839 := bstep (se 1 (by rfl) ⟨2261879, by rfl⟩ : syracuseStep 3015839 = 4523759) B4523759
theorem B24479441 : Blo 1411525 24479441 := bstep (se 2 (by rfl) ⟨9179790, by rfl⟩ : syracuseStep 24479441 = 18359581) B18359581
theorem B20375549 : Blo 1411525 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B2681839 : Blo 1411525 2681839 := bstep (se 1 (by rfl) ⟨2011379, by rfl⟩ : syracuseStep 2681839 = 4022759) B4022759
theorem B1412423 : Blo 1411525 1412423 := bstep (se 1 (by rfl) ⟨1059317, by rfl⟩ : syracuseStep 1412423 = 2118635) B2118635
theorem B1412455 : Blo 1411525 1412455 := bstep (se 1 (by rfl) ⟨1059341, by rfl⟩ : syracuseStep 1412455 = 2118683) B2118683
theorem B1413023 : Blo 1411525 1413023 := bstep (se 1 (by rfl) ⟨1059767, by rfl⟩ : syracuseStep 1413023 = 2119535) B2119535
theorem B17186813 : Blo 1411525 17186813 := bstep (se 3 (by rfl) ⟨3222527, by rfl⟩ : syracuseStep 17186813 = 6445055) B6445055
theorem B2118383 : Blo 1411525 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B4764527 : Blo 1411525 4764527 := bstep (se 1 (by rfl) ⟨3573395, by rfl⟩ : syracuseStep 4764527 = 7146791) B7146791
theorem B7246847 : Blo 1411525 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B3577679 : Blo 1411525 3577679 := bstep (se 1 (by rfl) ⟨2683259, by rfl⟩ : syracuseStep 3577679 = 5366519) B5366519
theorem B3176783 : Blo 1411525 3176783 := bstep (se 1 (by rfl) ⟨2382587, by rfl⟩ : syracuseStep 3176783 = 4765175) B4765175
theorem B21740413 : Blo 1411525 21740413 := bstep (se 3 (by rfl) ⟨4076327, by rfl⟩ : syracuseStep 21740413 = 8152655) B8152655
theorem B24460319 : Blo 1411525 24460319 := bstep (se 1 (by rfl) ⟨18345239, by rfl⟩ : syracuseStep 24460319 = 36690479) B36690479
theorem B70565741 : Blo 1411525 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B3178907 : Blo 1411525 3178907 := bstep (se 1 (by rfl) ⟨2384180, by rfl⟩ : syracuseStep 3178907 = 4768361) B4768361
theorem B16319627 : Blo 1411525 16319627 := bstep (se 1 (by rfl) ⟨12239720, by rfl⟩ : syracuseStep 16319627 = 24479441) B24479441
theorem B2385119 : Blo 1411525 2385119 := bstep (se 1 (by rfl) ⟨1788839, by rfl⟩ : syracuseStep 2385119 = 3577679) B3577679
theorem B13583699 : Blo 1411525 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B65227517 : Blo 1411525 65227517 := bstep (se 3 (by rfl) ⟨12230159, by rfl⟩ : syracuseStep 65227517 = 24460319) B24460319
theorem B1412255 : Blo 1411525 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B28987217 : Blo 1411525 28987217 := bstep (se 2 (by rfl) ⟨10870206, by rfl⟩ : syracuseStep 28987217 = 21740413) B21740413
theorem B3575785 : Blo 1411525 3575785 := bstep (se 2 (by rfl) ⟨1340919, by rfl⟩ : syracuseStep 3575785 = 2681839) B2681839
theorem B2117855 : Blo 1411525 2117855 := bstep (se 1 (by rfl) ⟨1588391, by rfl⟩ : syracuseStep 2117855 = 3176783) B3176783
theorem B47043827 : Blo 1411525 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B11457875 : Blo 1411525 11457875 := bstep (se 1 (by rfl) ⟨8593406, by rfl⟩ : syracuseStep 11457875 = 17186813) B17186813
theorem B57988547 : Blo 1411525 57988547 := bstep (se 1 (by rfl) ⟨43491410, by rfl⟩ : syracuseStep 57988547 = 86982821) B86982821
theorem B8042237 : Blo 1411525 8042237 := bstep (se 3 (by rfl) ⟨1507919, by rfl⟩ : syracuseStep 8042237 = 3015839) B3015839
theorem B3176351 : Blo 1411525 3176351 := bstep (se 1 (by rfl) ⟨2382263, by rfl⟩ : syracuseStep 3176351 = 4764527) B4764527
theorem B19324925 : Blo 1411525 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B10879751 : Blo 1411525 10879751 := bstep (se 1 (by rfl) ⟨8159813, by rfl⟩ : syracuseStep 10879751 = 16319627) B16319627
theorem B1590079 : Blo 1411525 1590079 := bstep (se 1 (by rfl) ⟨1192559, by rfl⟩ : syracuseStep 1590079 = 2385119) B2385119
theorem B38659031 : Blo 1411525 38659031 := bstep (se 1 (by rfl) ⟨28994273, by rfl⟩ : syracuseStep 38659031 = 57988547) B57988547
theorem B43485011 : Blo 1411525 43485011 := bstep (se 1 (by rfl) ⟨32613758, by rfl⟩ : syracuseStep 43485011 = 65227517) B65227517
theorem B1411903 : Blo 1411525 1411903 := bstep (se 1 (by rfl) ⟨1058927, by rfl⟩ : syracuseStep 1411903 = 2117855) B2117855
theorem B31362551 : Blo 1411525 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B7638583 : Blo 1411525 7638583 := bstep (se 1 (by rfl) ⟨5728937, by rfl⟩ : syracuseStep 7638583 = 11457875) B11457875
theorem B9055799 : Blo 1411525 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B5361491 : Blo 1411525 5361491 := bstep (se 1 (by rfl) ⟨4021118, by rfl⟩ : syracuseStep 5361491 = 8042237) B8042237
theorem B2117567 : Blo 1411525 2117567 := bstep (se 1 (by rfl) ⟨1588175, by rfl⟩ : syracuseStep 2117567 = 3176351) B3176351
theorem B12883283 : Blo 1411525 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B2119271 : Blo 1411525 2119271 := bstep (se 1 (by rfl) ⟨1589453, by rfl⟩ : syracuseStep 2119271 = 3178907) B3178907
theorem B19324811 : Blo 1411525 19324811 := bstep (se 1 (by rfl) ⟨14493608, by rfl⟩ : syracuseStep 19324811 = 28987217) B28987217
theorem B4767713 : Blo 1411525 4767713 := bstep (se 2 (by rfl) ⟨1787892, by rfl⟩ : syracuseStep 4767713 = 3575785) B3575785
theorem B25772687 : Blo 1411525 25772687 := bstep (se 1 (by rfl) ⟨19329515, by rfl⟩ : syracuseStep 25772687 = 38659031) B38659031
theorem B10184777 : Blo 1411525 10184777 := bstep (se 2 (by rfl) ⟨3819291, by rfl⟩ : syracuseStep 10184777 = 7638583) B7638583
theorem B20908367 : Blo 1411525 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B3574327 : Blo 1411525 3574327 := bstep (se 1 (by rfl) ⟨2680745, by rfl⟩ : syracuseStep 3574327 = 5361491) B5361491
theorem B1411711 : Blo 1411525 1411711 := bstep (se 1 (by rfl) ⟨1058783, by rfl⟩ : syracuseStep 1411711 = 2117567) B2117567
theorem B7253167 : Blo 1411525 7253167 := bstep (se 1 (by rfl) ⟨5439875, by rfl⟩ : syracuseStep 7253167 = 10879751) B10879751
theorem B8588855 : Blo 1411525 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B1412847 : Blo 1411525 1412847 := bstep (se 1 (by rfl) ⟨1059635, by rfl⟩ : syracuseStep 1412847 = 2119271) B2119271
theorem B12883207 : Blo 1411525 12883207 := bstep (se 1 (by rfl) ⟨9662405, by rfl⟩ : syracuseStep 12883207 = 19324811) B19324811
theorem B2120105 : Blo 1411525 2120105 := bstep (se 2 (by rfl) ⟨795039, by rfl⟩ : syracuseStep 2120105 = 1590079) B1590079
theorem B28990007 : Blo 1411525 28990007 := bstep (se 1 (by rfl) ⟨21742505, by rfl⟩ : syracuseStep 28990007 = 43485011) B43485011
theorem B6037199 : Blo 1411525 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B3178475 : Blo 1411525 3178475 := bstep (se 1 (by rfl) ⟨2383856, by rfl⟩ : syracuseStep 3178475 = 4767713) B4767713
theorem B19326671 : Blo 1411525 19326671 := bstep (se 1 (by rfl) ⟨14495003, by rfl⟩ : syracuseStep 19326671 = 28990007) B28990007
theorem B4024799 : Blo 1411525 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B17181791 : Blo 1411525 17181791 := bstep (se 1 (by rfl) ⟨12886343, by rfl⟩ : syracuseStep 17181791 = 25772687) B25772687
theorem B13938911 : Blo 1411525 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B9670889 : Blo 1411525 9670889 := bstep (se 2 (by rfl) ⟨3626583, by rfl⟩ : syracuseStep 9670889 = 7253167) B7253167
theorem B1413403 : Blo 1411525 1413403 := bstep (se 1 (by rfl) ⟨1060052, by rfl⟩ : syracuseStep 1413403 = 2120105) B2120105
theorem B2118983 : Blo 1411525 2118983 := bstep (se 1 (by rfl) ⟨1589237, by rfl⟩ : syracuseStep 2118983 = 3178475) B3178475
theorem B4765769 : Blo 1411525 4765769 := bstep (se 2 (by rfl) ⟨1787163, by rfl⟩ : syracuseStep 4765769 = 3574327) B3574327
theorem B6789851 : Blo 1411525 6789851 := bstep (se 1 (by rfl) ⟨5092388, by rfl⟩ : syracuseStep 6789851 = 10184777) B10184777
theorem B17177609 : Blo 1411525 17177609 := bstep (se 2 (by rfl) ⟨6441603, by rfl⟩ : syracuseStep 17177609 = 12883207) B12883207
theorem B5725903 : Blo 1411525 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B6447259 : Blo 1411525 6447259 := bstep (se 1 (by rfl) ⟨4835444, by rfl⟩ : syracuseStep 6447259 = 9670889) B9670889
theorem B11454527 : Blo 1411525 11454527 := bstep (se 1 (by rfl) ⟨8590895, by rfl⟩ : syracuseStep 11454527 = 17181791) B17181791
theorem B9292607 : Blo 1411525 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B1412655 : Blo 1411525 1412655 := bstep (se 1 (by rfl) ⟨1059491, by rfl⟩ : syracuseStep 1412655 = 2118983) B2118983
theorem B2683199 : Blo 1411525 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B4526567 : Blo 1411525 4526567 := bstep (se 1 (by rfl) ⟨3394925, by rfl⟩ : syracuseStep 4526567 = 6789851) B6789851
theorem B45806957 : Blo 1411525 45806957 := bstep (se 3 (by rfl) ⟨8588804, by rfl⟩ : syracuseStep 45806957 = 17177609) B17177609
theorem B12884447 : Blo 1411525 12884447 := bstep (se 1 (by rfl) ⟨9663335, by rfl⟩ : syracuseStep 12884447 = 19326671) B19326671
theorem B3177179 : Blo 1411525 3177179 := bstep (se 1 (by rfl) ⟨2382884, by rfl⟩ : syracuseStep 3177179 = 4765769) B4765769
theorem B7634537 : Blo 1411525 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B7636351 : Blo 1411525 7636351 := bstep (se 1 (by rfl) ⟨5727263, by rfl⟩ : syracuseStep 7636351 = 11454527) B11454527
theorem B6195071 : Blo 1411525 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B5089691 : Blo 1411525 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B1788799 : Blo 1411525 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B3017711 : Blo 1411525 3017711 := bstep (se 1 (by rfl) ⟨2263283, by rfl⟩ : syracuseStep 3017711 = 4526567) B4526567
theorem B34385381 : Blo 1411525 34385381 := bstep (se 4 (by rfl) ⟨3223629, by rfl⟩ : syracuseStep 34385381 = 6447259) B6447259
theorem B8589631 : Blo 1411525 8589631 := bstep (se 1 (by rfl) ⟨6442223, by rfl⟩ : syracuseStep 8589631 = 12884447) B12884447
theorem B2118119 : Blo 1411525 2118119 := bstep (se 1 (by rfl) ⟨1588589, by rfl⟩ : syracuseStep 2118119 = 3177179) B3177179
theorem B30537971 : Blo 1411525 30537971 := bstep (se 1 (by rfl) ⟨22903478, by rfl⟩ : syracuseStep 30537971 = 45806957) B45806957
theorem B11452841 : Blo 1411525 11452841 := bstep (se 2 (by rfl) ⟨4294815, by rfl⟩ : syracuseStep 11452841 = 8589631) B8589631
theorem B2385065 : Blo 1411525 2385065 := bstep (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) B1788799
theorem B4130047 : Blo 1411525 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B20358647 : Blo 1411525 20358647 := bstep (se 1 (by rfl) ⟨15268985, by rfl⟩ : syracuseStep 20358647 = 30537971) B30537971
theorem B3393127 : Blo 1411525 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B22923587 : Blo 1411525 22923587 := bstep (se 1 (by rfl) ⟨17192690, by rfl⟩ : syracuseStep 22923587 = 34385381) B34385381
theorem B1412079 : Blo 1411525 1412079 := bstep (se 1 (by rfl) ⟨1059059, by rfl⟩ : syracuseStep 1412079 = 2118119) B2118119
theorem B2011807 : Blo 1411525 2011807 := bstep (se 1 (by rfl) ⟨1508855, by rfl⟩ : syracuseStep 2011807 = 3017711) B3017711
theorem B10181801 : Blo 1411525 10181801 := bstep (se 2 (by rfl) ⟨3818175, by rfl⟩ : syracuseStep 10181801 = 7636351) B7636351
theorem B7635227 : Blo 1411525 7635227 := bstep (se 1 (by rfl) ⟨5726420, by rfl⟩ : syracuseStep 7635227 = 11452841) B11452841
theorem B1590043 : Blo 1411525 1590043 := bstep (se 1 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 1590043 = 2385065) B2385065
theorem B4524169 : Blo 1411525 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B27151469 : Blo 1411525 27151469 := bstep (se 3 (by rfl) ⟨5090900, by rfl⟩ : syracuseStep 27151469 = 10181801) B10181801
theorem B2682409 : Blo 1411525 2682409 := bstep (se 2 (by rfl) ⟨1005903, by rfl⟩ : syracuseStep 2682409 = 2011807) B2011807
theorem B15282391 : Blo 1411525 15282391 := bstep (se 1 (by rfl) ⟨11461793, by rfl⟩ : syracuseStep 15282391 = 22923587) B22923587
theorem B13572431 : Blo 1411525 13572431 := bstep (se 1 (by rfl) ⟨10179323, by rfl⟩ : syracuseStep 13572431 = 20358647) B20358647
theorem B22026917 : Blo 1411525 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B6032225 : Blo 1411525 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B20376521 : Blo 1411525 20376521 := bstep (se 2 (by rfl) ⟨7641195, by rfl⟩ : syracuseStep 20376521 = 15282391) B15282391
theorem B20360605 : Blo 1411525 20360605 := bstep (se 3 (by rfl) ⟨3817613, by rfl⟩ : syracuseStep 20360605 = 7635227) B7635227
theorem B9048287 : Blo 1411525 9048287 := bstep (se 1 (by rfl) ⟨6786215, by rfl⟩ : syracuseStep 9048287 = 13572431) B13572431
theorem B14684611 : Blo 1411525 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B3576545 : Blo 1411525 3576545 := bstep (se 2 (by rfl) ⟨1341204, by rfl⟩ : syracuseStep 3576545 = 2682409) B2682409
theorem B18100979 : Blo 1411525 18100979 := bstep (se 1 (by rfl) ⟨13575734, by rfl⟩ : syracuseStep 18100979 = 27151469) B27151469
theorem B2120057 : Blo 1411525 2120057 := bstep (se 2 (by rfl) ⟨795021, by rfl⟩ : syracuseStep 2120057 = 1590043) B1590043
theorem B2384363 : Blo 1411525 2384363 := bstep (se 1 (by rfl) ⟨1788272, by rfl⟩ : syracuseStep 2384363 = 3576545) B3576545
theorem B12067319 : Blo 1411525 12067319 := bstep (se 1 (by rfl) ⟨9050489, by rfl⟩ : syracuseStep 12067319 = 18100979) B18100979
theorem B19579481 : Blo 1411525 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B13584347 : Blo 1411525 13584347 := bstep (se 1 (by rfl) ⟨10188260, by rfl⟩ : syracuseStep 13584347 = 20376521) B20376521
theorem B6032191 : Blo 1411525 6032191 := bstep (se 1 (by rfl) ⟨4524143, by rfl⟩ : syracuseStep 6032191 = 9048287) B9048287
theorem B1413371 : Blo 1411525 1413371 := bstep (se 1 (by rfl) ⟨1060028, by rfl⟩ : syracuseStep 1413371 = 2120057) B2120057
theorem B27147473 : Blo 1411525 27147473 := bstep (se 2 (by rfl) ⟨10180302, by rfl⟩ : syracuseStep 27147473 = 20360605) B20360605
theorem B4021483 : Blo 1411525 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B1589575 : Blo 1411525 1589575 := bstep (se 1 (by rfl) ⟨1192181, by rfl⟩ : syracuseStep 1589575 = 2384363) B2384363
theorem B8044879 : Blo 1411525 8044879 := bstep (se 1 (by rfl) ⟨6033659, by rfl⟩ : syracuseStep 8044879 = 12067319) B12067319
theorem B18098315 : Blo 1411525 18098315 := bstep (se 1 (by rfl) ⟨13573736, by rfl⟩ : syracuseStep 18098315 = 27147473) B27147473
theorem B13052987 : Blo 1411525 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B9056231 : Blo 1411525 9056231 := bstep (se 1 (by rfl) ⟨6792173, by rfl⟩ : syracuseStep 9056231 = 13584347) B13584347
theorem B5361977 : Blo 1411525 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B8042921 : Blo 1411525 8042921 := bstep (se 2 (by rfl) ⟨3016095, by rfl⟩ : syracuseStep 8042921 = 6032191) B6032191
theorem B8701991 : Blo 1411525 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B3574651 : Blo 1411525 3574651 := bstep (se 1 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 3574651 = 5361977) B5361977
theorem B10726505 : Blo 1411525 10726505 := bstep (se 2 (by rfl) ⟨4022439, by rfl⟩ : syracuseStep 10726505 = 8044879) B8044879
theorem B5361947 : Blo 1411525 5361947 := bstep (se 1 (by rfl) ⟨4021460, by rfl⟩ : syracuseStep 5361947 = 8042921) B8042921
theorem B2119433 : Blo 1411525 2119433 := bstep (se 2 (by rfl) ⟨794787, by rfl⟩ : syracuseStep 2119433 = 1589575) B1589575
theorem B12065543 : Blo 1411525 12065543 := bstep (se 1 (by rfl) ⟨9049157, by rfl⟩ : syracuseStep 12065543 = 18098315) B18098315
theorem B6037487 : Blo 1411525 6037487 := bstep (se 1 (by rfl) ⟨4528115, by rfl⟩ : syracuseStep 6037487 = 9056231) B9056231
theorem B5801327 : Blo 1411525 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B4024991 : Blo 1411525 4024991 := bstep (se 1 (by rfl) ⟨3018743, by rfl⟩ : syracuseStep 4024991 = 6037487) B6037487
theorem B3574631 : Blo 1411525 3574631 := bstep (se 1 (by rfl) ⟨2680973, by rfl⟩ : syracuseStep 3574631 = 5361947) B5361947
theorem B1412955 : Blo 1411525 1412955 := bstep (se 1 (by rfl) ⟨1059716, by rfl⟩ : syracuseStep 1412955 = 2119433) B2119433
theorem B4766201 : Blo 1411525 4766201 := bstep (se 2 (by rfl) ⟨1787325, by rfl⟩ : syracuseStep 4766201 = 3574651) B3574651
theorem B8043695 : Blo 1411525 8043695 := bstep (se 1 (by rfl) ⟨6032771, by rfl⟩ : syracuseStep 8043695 = 12065543) B12065543
theorem B7151003 : Blo 1411525 7151003 := bstep (se 1 (by rfl) ⟨5363252, by rfl⟩ : syracuseStep 7151003 = 10726505) B10726505
theorem B3867551 : Blo 1411525 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B10733309 : Blo 1411525 10733309 := bstep (se 3 (by rfl) ⟨2012495, by rfl⟩ : syracuseStep 10733309 = 4024991) B4024991
theorem B5362463 : Blo 1411525 5362463 := bstep (se 1 (by rfl) ⟨4021847, by rfl⟩ : syracuseStep 5362463 = 8043695) B8043695
theorem B3177467 : Blo 1411525 3177467 := bstep (se 1 (by rfl) ⟨2383100, by rfl⟩ : syracuseStep 3177467 = 4766201) B4766201
theorem B2383087 : Blo 1411525 2383087 := bstep (se 1 (by rfl) ⟨1787315, by rfl⟩ : syracuseStep 2383087 = 3574631) B3574631
theorem B4767335 : Blo 1411525 4767335 := bstep (se 1 (by rfl) ⟨3575501, by rfl⟩ : syracuseStep 4767335 = 7151003) B7151003
theorem B3574975 : Blo 1411525 3574975 := bstep (se 1 (by rfl) ⟨2681231, by rfl⟩ : syracuseStep 3574975 = 5362463) B5362463
theorem B7155539 : Blo 1411525 7155539 := bstep (se 1 (by rfl) ⟨5366654, by rfl⟩ : syracuseStep 7155539 = 10733309) B10733309
theorem B2118311 : Blo 1411525 2118311 := bstep (se 1 (by rfl) ⟨1588733, by rfl⟩ : syracuseStep 2118311 = 3177467) B3177467
theorem B3177449 : Blo 1411525 3177449 := bstep (se 2 (by rfl) ⟨1191543, by rfl⟩ : syracuseStep 3177449 = 2383087) B2383087
theorem B41253877 : Blo 1411525 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B3178223 : Blo 1411525 3178223 := bstep (se 1 (by rfl) ⟨2383667, by rfl⟩ : syracuseStep 3178223 = 4767335) B4767335
theorem B4770359 : Blo 1411525 4770359 := bstep (se 1 (by rfl) ⟨3577769, by rfl⟩ : syracuseStep 4770359 = 7155539) B7155539
theorem B1412207 : Blo 1411525 1412207 := bstep (se 1 (by rfl) ⟨1059155, by rfl⟩ : syracuseStep 1412207 = 2118311) B2118311
theorem B55005169 : Blo 1411525 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B2118299 : Blo 1411525 2118299 := bstep (se 1 (by rfl) ⟨1588724, by rfl⟩ : syracuseStep 2118299 = 3177449) B3177449
theorem B2118815 : Blo 1411525 2118815 := bstep (se 1 (by rfl) ⟨1589111, by rfl⟩ : syracuseStep 2118815 = 3178223) B3178223
theorem B4766633 : Blo 1411525 4766633 := bstep (se 2 (by rfl) ⟨1787487, by rfl⟩ : syracuseStep 4766633 = 3574975) B3574975
theorem B3180239 : Blo 1411525 3180239 := bstep (se 1 (by rfl) ⟨2385179, by rfl⟩ : syracuseStep 3180239 = 4770359) B4770359
theorem B1412199 : Blo 1411525 1412199 := bstep (se 1 (by rfl) ⟨1059149, by rfl⟩ : syracuseStep 1412199 = 2118299) B2118299
theorem B1412543 : Blo 1411525 1412543 := bstep (se 1 (by rfl) ⟨1059407, by rfl⟩ : syracuseStep 1412543 = 2118815) B2118815
theorem B73340225 : Blo 1411525 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B3177755 : Blo 1411525 3177755 := bstep (se 1 (by rfl) ⟨2383316, by rfl⟩ : syracuseStep 3177755 = 4766633) B4766633
theorem B48893483 : Blo 1411525 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B2118503 : Blo 1411525 2118503 := bstep (se 1 (by rfl) ⟨1588877, by rfl⟩ : syracuseStep 2118503 = 3177755) B3177755
theorem B2120159 : Blo 1411525 2120159 := bstep (se 1 (by rfl) ⟨1590119, by rfl⟩ : syracuseStep 2120159 = 3180239) B3180239
theorem B1412335 : Blo 1411525 1412335 := bstep (se 1 (by rfl) ⟨1059251, by rfl⟩ : syracuseStep 1412335 = 2118503) B2118503
theorem B1413439 : Blo 1411525 1413439 := bstep (se 1 (by rfl) ⟨1060079, by rfl⟩ : syracuseStep 1413439 = 2120159) B2120159
theorem B130382621 : Blo 1411525 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B86921747 : Blo 1411525 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B57947831 : Blo 1411525 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B38631887 : Blo 1411525 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B25754591 : Blo 1411525 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B17169727 : Blo 1411525 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B22892969 : Blo 1411525 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B15261979 : Blo 1411525 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B20349305 : Blo 1411525 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B13566203 : Blo 1411525 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B9044135 : Blo 1411525 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B6029423 : Blo 1411525 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B4019615 : Blo 1411525 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B2679743 : Blo 1411525 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B7145981 : Blo 1411525 7145981 := bstep (se 3 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 7145981 = 2679743) B2679743
theorem B4763987 : Blo 1411525 4763987 := bstep (se 1 (by rfl) ⟨3572990, by rfl⟩ : syracuseStep 4763987 = 7145981) B7145981
theorem B3175991 : Blo 1411525 3175991 := bstep (se 1 (by rfl) ⟨2381993, by rfl⟩ : syracuseStep 3175991 = 4763987) B4763987
theorem B2117327 : Blo 1411525 2117327 := bstep (se 1 (by rfl) ⟨1587995, by rfl⟩ : syracuseStep 2117327 = 3175991) B3175991
theorem B1411551 : Blo 1411525 1411551 := bstep (se 1 (by rfl) ⟨1058663, by rfl⟩ : syracuseStep 1411551 = 2117327) B2117327

theorem C0 (j : ℕ) (h1 : 352881 ≤ j) (h2 : j ≤ 353380) : Blo 1411525 (4 * j + 3) := by
  interval_cases j
  · exact B1411527
  · exact B1411531
  · exact B1411535
  · exact B1411539
  · exact B1411543
  · exact B1411547
  · exact B1411551
  · exact B1411555
  · exact B1411559
  · exact B1411563
  · exact B1411567
  · exact B1411571
  · exact B1411575
  · exact B1411579
  · exact B1411583
  · exact B1411587
  · exact B1411591
  · exact B1411595
  · exact B1411599
  · exact B1411603
  · exact B1411607
  · exact B1411611
  · exact B1411615
  · exact B1411619
  · exact B1411623
  · exact B1411627
  · exact B1411631
  · exact B1411635
  · exact B1411639
  · exact B1411643
  · exact B1411647
  · exact B1411651
  · exact B1411655
  · exact B1411659
  · exact B1411663
  · exact B1411667
  · exact B1411671
  · exact B1411675
  · exact B1411679
  · exact B1411683
  · exact B1411687
  · exact B1411691
  · exact B1411695
  · exact B1411699
  · exact B1411703
  · exact B1411707
  · exact B1411711
  · exact B1411715
  · exact B1411719
  · exact B1411723
  · exact B1411727
  · exact B1411731
  · exact B1411735
  · exact B1411739
  · exact B1411743
  · exact B1411747
  · exact B1411751
  · exact B1411755
  · exact B1411759
  · exact B1411763
  · exact B1411767
  · exact B1411771
  · exact B1411775
  · exact B1411779
  · exact B1411783
  · exact B1411787
  · exact B1411791
  · exact B1411795
  · exact B1411799
  · exact B1411803
  · exact B1411807
  · exact B1411811
  · exact B1411815
  · exact B1411819
  · exact B1411823
  · exact B1411827
  · exact B1411831
  · exact B1411835
  · exact B1411839
  · exact B1411843
  · exact B1411847
  · exact B1411851
  · exact B1411855
  · exact B1411859
  · exact B1411863
  · exact B1411867
  · exact B1411871
  · exact B1411875
  · exact B1411879
  · exact B1411883
  · exact B1411887
  · exact B1411891
  · exact B1411895
  · exact B1411899
  · exact B1411903
  · exact B1411907
  · exact B1411911
  · exact B1411915
  · exact B1411919
  · exact B1411923
  · exact B1411927
  · exact B1411931
  · exact B1411935
  · exact B1411939
  · exact B1411943
  · exact B1411947
  · exact B1411951
  · exact B1411955
  · exact B1411959
  · exact B1411963
  · exact B1411967
  · exact B1411971
  · exact B1411975
  · exact B1411979
  · exact B1411983
  · exact B1411987
  · exact B1411991
  · exact B1411995
  · exact B1411999
  · exact B1412003
  · exact B1412007
  · exact B1412011
  · exact B1412015
  · exact B1412019
  · exact B1412023
  · exact B1412027
  · exact B1412031
  · exact B1412035
  · exact B1412039
  · exact B1412043
  · exact B1412047
  · exact B1412051
  · exact B1412055
  · exact B1412059
  · exact B1412063
  · exact B1412067
  · exact B1412071
  · exact B1412075
  · exact B1412079
  · exact B1412083
  · exact B1412087
  · exact B1412091
  · exact B1412095
  · exact B1412099
  · exact B1412103
  · exact B1412107
  · exact B1412111
  · exact B1412115
  · exact B1412119
  · exact B1412123
  · exact B1412127
  · exact B1412131
  · exact B1412135
  · exact B1412139
  · exact B1412143
  · exact B1412147
  · exact B1412151
  · exact B1412155
  · exact B1412159
  · exact B1412163
  · exact B1412167
  · exact B1412171
  · exact B1412175
  · exact B1412179
  · exact B1412183
  · exact B1412187
  · exact B1412191
  · exact B1412195
  · exact B1412199
  · exact B1412203
  · exact B1412207
  · exact B1412211
  · exact B1412215
  · exact B1412219
  · exact B1412223
  · exact B1412227
  · exact B1412231
  · exact B1412235
  · exact B1412239
  · exact B1412243
  · exact B1412247
  · exact B1412251
  · exact B1412255
  · exact B1412259
  · exact B1412263
  · exact B1412267
  · exact B1412271
  · exact B1412275
  · exact B1412279
  · exact B1412283
  · exact B1412287
  · exact B1412291
  · exact B1412295
  · exact B1412299
  · exact B1412303
  · exact B1412307
  · exact B1412311
  · exact B1412315
  · exact B1412319
  · exact B1412323
  · exact B1412327
  · exact B1412331
  · exact B1412335
  · exact B1412339
  · exact B1412343
  · exact B1412347
  · exact B1412351
  · exact B1412355
  · exact B1412359
  · exact B1412363
  · exact B1412367
  · exact B1412371
  · exact B1412375
  · exact B1412379
  · exact B1412383
  · exact B1412387
  · exact B1412391
  · exact B1412395
  · exact B1412399
  · exact B1412403
  · exact B1412407
  · exact B1412411
  · exact B1412415
  · exact B1412419
  · exact B1412423
  · exact B1412427
  · exact B1412431
  · exact B1412435
  · exact B1412439
  · exact B1412443
  · exact B1412447
  · exact B1412451
  · exact B1412455
  · exact B1412459
  · exact B1412463
  · exact B1412467
  · exact B1412471
  · exact B1412475
  · exact B1412479
  · exact B1412483
  · exact B1412487
  · exact B1412491
  · exact B1412495
  · exact B1412499
  · exact B1412503
  · exact B1412507
  · exact B1412511
  · exact B1412515
  · exact B1412519
  · exact B1412523
  · exact B1412527
  · exact B1412531
  · exact B1412535
  · exact B1412539
  · exact B1412543
  · exact B1412547
  · exact B1412551
  · exact B1412555
  · exact B1412559
  · exact B1412563
  · exact B1412567
  · exact B1412571
  · exact B1412575
  · exact B1412579
  · exact B1412583
  · exact B1412587
  · exact B1412591
  · exact B1412595
  · exact B1412599
  · exact B1412603
  · exact B1412607
  · exact B1412611
  · exact B1412615
  · exact B1412619
  · exact B1412623
  · exact B1412627
  · exact B1412631
  · exact B1412635
  · exact B1412639
  · exact B1412643
  · exact B1412647
  · exact B1412651
  · exact B1412655
  · exact B1412659
  · exact B1412663
  · exact B1412667
  · exact B1412671
  · exact B1412675
  · exact B1412679
  · exact B1412683
  · exact B1412687
  · exact B1412691
  · exact B1412695
  · exact B1412699
  · exact B1412703
  · exact B1412707
  · exact B1412711
  · exact B1412715
  · exact B1412719
  · exact B1412723
  · exact B1412727
  · exact B1412731
  · exact B1412735
  · exact B1412739
  · exact B1412743
  · exact B1412747
  · exact B1412751
  · exact B1412755
  · exact B1412759
  · exact B1412763
  · exact B1412767
  · exact B1412771
  · exact B1412775
  · exact B1412779
  · exact B1412783
  · exact B1412787
  · exact B1412791
  · exact B1412795
  · exact B1412799
  · exact B1412803
  · exact B1412807
  · exact B1412811
  · exact B1412815
  · exact B1412819
  · exact B1412823
  · exact B1412827
  · exact B1412831
  · exact B1412835
  · exact B1412839
  · exact B1412843
  · exact B1412847
  · exact B1412851
  · exact B1412855
  · exact B1412859
  · exact B1412863
  · exact B1412867
  · exact B1412871
  · exact B1412875
  · exact B1412879
  · exact B1412883
  · exact B1412887
  · exact B1412891
  · exact B1412895
  · exact B1412899
  · exact B1412903
  · exact B1412907
  · exact B1412911
  · exact B1412915
  · exact B1412919
  · exact B1412923
  · exact B1412927
  · exact B1412931
  · exact B1412935
  · exact B1412939
  · exact B1412943
  · exact B1412947
  · exact B1412951
  · exact B1412955
  · exact B1412959
  · exact B1412963
  · exact B1412967
  · exact B1412971
  · exact B1412975
  · exact B1412979
  · exact B1412983
  · exact B1412987
  · exact B1412991
  · exact B1412995
  · exact B1412999
  · exact B1413003
  · exact B1413007
  · exact B1413011
  · exact B1413015
  · exact B1413019
  · exact B1413023
  · exact B1413027
  · exact B1413031
  · exact B1413035
  · exact B1413039
  · exact B1413043
  · exact B1413047
  · exact B1413051
  · exact B1413055
  · exact B1413059
  · exact B1413063
  · exact B1413067
  · exact B1413071
  · exact B1413075
  · exact B1413079
  · exact B1413083
  · exact B1413087
  · exact B1413091
  · exact B1413095
  · exact B1413099
  · exact B1413103
  · exact B1413107
  · exact B1413111
  · exact B1413115
  · exact B1413119
  · exact B1413123
  · exact B1413127
  · exact B1413131
  · exact B1413135
  · exact B1413139
  · exact B1413143
  · exact B1413147
  · exact B1413151
  · exact B1413155
  · exact B1413159
  · exact B1413163
  · exact B1413167
  · exact B1413171
  · exact B1413175
  · exact B1413179
  · exact B1413183
  · exact B1413187
  · exact B1413191
  · exact B1413195
  · exact B1413199
  · exact B1413203
  · exact B1413207
  · exact B1413211
  · exact B1413215
  · exact B1413219
  · exact B1413223
  · exact B1413227
  · exact B1413231
  · exact B1413235
  · exact B1413239
  · exact B1413243
  · exact B1413247
  · exact B1413251
  · exact B1413255
  · exact B1413259
  · exact B1413263
  · exact B1413267
  · exact B1413271
  · exact B1413275
  · exact B1413279
  · exact B1413283
  · exact B1413287
  · exact B1413291
  · exact B1413295
  · exact B1413299
  · exact B1413303
  · exact B1413307
  · exact B1413311
  · exact B1413315
  · exact B1413319
  · exact B1413323
  · exact B1413327
  · exact B1413331
  · exact B1413335
  · exact B1413339
  · exact B1413343
  · exact B1413347
  · exact B1413351
  · exact B1413355
  · exact B1413359
  · exact B1413363
  · exact B1413367
  · exact B1413371
  · exact B1413375
  · exact B1413379
  · exact B1413383
  · exact B1413387
  · exact B1413391
  · exact B1413395
  · exact B1413399
  · exact B1413403
  · exact B1413407
  · exact B1413411
  · exact B1413415
  · exact B1413419
  · exact B1413423
  · exact B1413427
  · exact B1413431
  · exact B1413435
  · exact B1413439
  · exact B1413443
  · exact B1413447
  · exact B1413451
  · exact B1413455
  · exact B1413459
  · exact B1413463
  · exact B1413467
  · exact B1413471
  · exact B1413475
  · exact B1413479
  · exact B1413483
  · exact B1413487
  · exact B1413491
  · exact B1413495
  · exact B1413499
  · exact B1413503
  · exact B1413507
  · exact B1413511
  · exact B1413515
  · exact B1413519
  · exact B1413523

theorem solution (m : ℕ) (hlo : 1411525 ≤ m) (hhi : m ≤ 1413525) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 352881 ≤ j := by omega
    have hj2 : j ≤ 353380 := by omega
    have hb : Blo 1411525 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
