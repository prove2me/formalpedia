-- Prove2me | solution 1 for syracuse_descends_range_1717059_1719059
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:28:58.382657+00:00
-- url     : https://prove2.me/submissions/6d59472f-9d38-4230-a784-a06340bca2a0

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


theorem B1933321 : Blo 1717059 1933321 := bbase (se 2 (by rfl) ⟨724995, by rfl⟩ : syracuseStep 1933321 = 1449991) (by norm_num)
theorem B3096613 : Blo 1717059 3096613 := bbase (se 4 (by rfl) ⟨290307, by rfl⟩ : syracuseStep 3096613 = 580615) (by norm_num)
theorem B3866669 : Blo 1717059 3866669 := bbase (se 3 (by rfl) ⟨725000, by rfl⟩ : syracuseStep 3866669 = 1450001) (by norm_num)
theorem B1933357 : Blo 1717059 1933357 := bbase (se 3 (by rfl) ⟨362504, by rfl⟩ : syracuseStep 1933357 = 725009) (by norm_num)
theorem B2900029 : Blo 1717059 2900029 := bbase (se 3 (by rfl) ⟨543755, by rfl⟩ : syracuseStep 2900029 = 1087511) (by norm_num)
theorem B2064457 : Blo 1717059 2064457 := bbase (se 2 (by rfl) ⟨774171, by rfl⟩ : syracuseStep 2064457 = 1548343) (by norm_num)
theorem B1933393 : Blo 1717059 1933393 := bbase (se 2 (by rfl) ⟨725022, by rfl⟩ : syracuseStep 1933393 = 1450045) (by norm_num)
theorem B1859681 : Blo 1717059 1859681 := bbase (se 2 (by rfl) ⟨697380, by rfl⟩ : syracuseStep 1859681 = 1394761) (by norm_num)
theorem B4890725 : Blo 1717059 4890725 := bbase (se 4 (by rfl) ⟨458505, by rfl⟩ : syracuseStep 4890725 = 917011) (by norm_num)
theorem B3866741 : Blo 1717059 3866741 := bbase (se 5 (by rfl) ⟨181253, by rfl⟩ : syracuseStep 3866741 = 362507) (by norm_num)
theorem B1933429 : Blo 1717059 1933429 := bbase (se 5 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 1933429 = 181259) (by norm_num)
theorem B1835141 : Blo 1717059 1835141 := bbase (se 4 (by rfl) ⟨172044, by rfl⟩ : syracuseStep 1835141 = 344089) (by norm_num)
theorem B5800085 : Blo 1717059 5800085 := bbase (se 6 (by rfl) ⟨135939, by rfl⟩ : syracuseStep 5800085 = 271879) (by norm_num)
theorem B2900117 : Blo 1717059 2900117 := bbase (se 6 (by rfl) ⟨67971, by rfl⟩ : syracuseStep 2900117 = 135943) (by norm_num)
theorem B1933465 : Blo 1717059 1933465 := bbase (se 2 (by rfl) ⟨725049, by rfl⟩ : syracuseStep 1933465 = 1450099) (by norm_num)
theorem B4350125 : Blo 1717059 4350125 := bbase (se 3 (by rfl) ⟨815648, by rfl⟩ : syracuseStep 4350125 = 1631297) (by norm_num)
theorem B3866813 : Blo 1717059 3866813 := bbase (se 3 (by rfl) ⟨725027, by rfl⟩ : syracuseStep 3866813 = 1450055) (by norm_num)
theorem B1933501 : Blo 1717059 1933501 := bbase (se 3 (by rfl) ⟨362531, by rfl⟩ : syracuseStep 1933501 = 725063) (by norm_num)
theorem B1958089 : Blo 1717059 1958089 := bbase (se 2 (by rfl) ⟨734283, by rfl⟩ : syracuseStep 1958089 = 1468567) (by norm_num)
theorem B1933537 : Blo 1717059 1933537 := bbase (se 2 (by rfl) ⟨725076, by rfl⟩ : syracuseStep 1933537 = 1450153) (by norm_num)
theorem B3866885 : Blo 1717059 3866885 := bbase (se 4 (by rfl) ⟨362520, by rfl⟩ : syracuseStep 3866885 = 725041) (by norm_num)
theorem B1933573 : Blo 1717059 1933573 := bbase (se 4 (by rfl) ⟨181272, by rfl⟩ : syracuseStep 1933573 = 362545) (by norm_num)
theorem B2900245 : Blo 1717059 2900245 := bbase (se 6 (by rfl) ⟨67974, by rfl⟩ : syracuseStep 2900245 = 135949) (by norm_num)
theorem B1933609 : Blo 1717059 1933609 := bbase (se 2 (by rfl) ⟨725103, by rfl⟩ : syracuseStep 1933609 = 1450207) (by norm_num)
theorem B1958189 : Blo 1717059 1958189 := bbase (se 3 (by rfl) ⟨367160, by rfl⟩ : syracuseStep 1958189 = 734321) (by norm_num)
theorem B3260749 : Blo 1717059 3260749 := bbase (se 3 (by rfl) ⟨611390, by rfl⟩ : syracuseStep 3260749 = 1222781) (by norm_num)
theorem B3866957 : Blo 1717059 3866957 := bbase (se 3 (by rfl) ⟨725054, by rfl⟩ : syracuseStep 3866957 = 1450109) (by norm_num)
theorem B1933645 : Blo 1717059 1933645 := bbase (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) (by norm_num)
theorem B2613589 : Blo 1717059 2613589 := bbase (se 10 (by rfl) ⟨3828, by rfl⟩ : syracuseStep 2613589 = 7657) (by norm_num)
theorem B2900333 : Blo 1717059 2900333 := bbase (se 3 (by rfl) ⟨543812, by rfl⟩ : syracuseStep 2900333 = 1087625) (by norm_num)
theorem B1933681 : Blo 1717059 1933681 := bbase (se 2 (by rfl) ⟨725130, by rfl⟩ : syracuseStep 1933681 = 1450261) (by norm_num)
theorem B1835389 : Blo 1717059 1835389 := bbase (se 3 (by rfl) ⟨344135, by rfl⟩ : syracuseStep 1835389 = 688271) (by norm_num)
theorem B3867029 : Blo 1717059 3867029 := bbase (se 6 (by rfl) ⟨90633, by rfl⟩ : syracuseStep 3867029 = 181267) (by norm_num)
theorem B1933717 : Blo 1717059 1933717 := bbase (se 6 (by rfl) ⟨45321, by rfl⟩ : syracuseStep 1933717 = 90643) (by norm_num)
theorem B3482021 : Blo 1717059 3482021 := bbase (se 4 (by rfl) ⟨326439, by rfl⟩ : syracuseStep 3482021 = 652879) (by norm_num)
theorem B6521269 : Blo 1717059 6521269 := bbase (se 5 (by rfl) ⟨305684, by rfl⟩ : syracuseStep 6521269 = 611369) (by norm_num)
theorem B3350965 : Blo 1717059 3350965 := bbase (se 5 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 3350965 = 314153) (by norm_num)
theorem B1933753 : Blo 1717059 1933753 := bbase (se 2 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 1933753 = 1450315) (by norm_num)
theorem B3260893 : Blo 1717059 3260893 := bbase (se 3 (by rfl) ⟨611417, by rfl⟩ : syracuseStep 3260893 = 1222835) (by norm_num)
theorem B3867101 : Blo 1717059 3867101 := bbase (se 3 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 3867101 = 1450163) (by norm_num)
theorem B1933789 : Blo 1717059 1933789 := bbase (se 3 (by rfl) ⟨362585, by rfl⟩ : syracuseStep 1933789 = 725171) (by norm_num)
theorem B8258021 : Blo 1717059 8258021 := bbase (se 4 (by rfl) ⟨774189, by rfl⟩ : syracuseStep 8258021 = 1548379) (by norm_num)
theorem B2900461 : Blo 1717059 2900461 := bbase (se 3 (by rfl) ⟨543836, by rfl⟩ : syracuseStep 2900461 = 1087673) (by norm_num)
theorem B1933825 : Blo 1717059 1933825 := bbase (se 2 (by rfl) ⟨725184, by rfl⟩ : syracuseStep 1933825 = 1450369) (by norm_num)
theorem B4350469 : Blo 1717059 4350469 := bbase (se 4 (by rfl) ⟨407856, by rfl⟩ : syracuseStep 4350469 = 815713) (by norm_num)
theorem B3867173 : Blo 1717059 3867173 := bbase (se 4 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 3867173 = 725095) (by norm_num)
theorem B1933861 : Blo 1717059 1933861 := bbase (se 4 (by rfl) ⟨181299, by rfl⟩ : syracuseStep 1933861 = 362599) (by norm_num)
theorem B5800517 : Blo 1717059 5800517 := bbase (se 4 (by rfl) ⟨543798, by rfl⟩ : syracuseStep 5800517 = 1087597) (by norm_num)
theorem B2900549 : Blo 1717059 2900549 := bbase (se 4 (by rfl) ⟨271926, by rfl⟩ : syracuseStep 2900549 = 543853) (by norm_num)
theorem B1933897 : Blo 1717059 1933897 := bbase (se 2 (by rfl) ⟨725211, by rfl⟩ : syracuseStep 1933897 = 1450423) (by norm_num)
theorem B3867245 : Blo 1717059 3867245 := bbase (se 3 (by rfl) ⟨725108, by rfl⟩ : syracuseStep 3867245 = 1450217) (by norm_num)
theorem B1933933 : Blo 1717059 1933933 := bbase (se 3 (by rfl) ⟨362612, by rfl⟩ : syracuseStep 1933933 = 725225) (by norm_num)
theorem B8700533 : Blo 1717059 8700533 := bbase (se 5 (by rfl) ⟨407837, by rfl⟩ : syracuseStep 8700533 = 815675) (by norm_num)
theorem B4350581 : Blo 1717059 4350581 := bbase (se 5 (by rfl) ⟨203933, by rfl⟩ : syracuseStep 4350581 = 407867) (by norm_num)
theorem B3261053 : Blo 1717059 3261053 := bbase (se 3 (by rfl) ⟨611447, by rfl⟩ : syracuseStep 3261053 = 1222895) (by norm_num)
theorem B7832213 : Blo 1717059 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B3867317 : Blo 1717059 3867317 := bbase (se 5 (by rfl) ⟨181280, by rfl⟩ : syracuseStep 3867317 = 362561) (by norm_num)
theorem B2900677 : Blo 1717059 2900677 := bbase (se 4 (by rfl) ⟨271938, by rfl⟩ : syracuseStep 2900677 = 543877) (by norm_num)
theorem B2753237 : Blo 1717059 2753237 := bbase (se 7 (by rfl) ⟨32264, by rfl⟩ : syracuseStep 2753237 = 64529) (by norm_num)
theorem B4129501 : Blo 1717059 4129501 := bbase (se 3 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 4129501 = 1548563) (by norm_num)
theorem B6521573 : Blo 1717059 6521573 := bbase (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) (by norm_num)
theorem B3867389 : Blo 1717059 3867389 := bbase (se 3 (by rfl) ⟨725135, by rfl⟩ : syracuseStep 3867389 = 1450271) (by norm_num)
theorem B3261197 : Blo 1717059 3261197 := bbase (se 3 (by rfl) ⟨611474, by rfl⟩ : syracuseStep 3261197 = 1222949) (by norm_num)
theorem B2900765 : Blo 1717059 2900765 := bbase (se 3 (by rfl) ⟨543893, by rfl⟩ : syracuseStep 2900765 = 1087787) (by norm_num)
theorem B3670829 : Blo 1717059 3670829 := bbase (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) (by norm_num)
theorem B3916597 : Blo 1717059 3916597 := bbase (se 5 (by rfl) ⟨183590, by rfl⟩ : syracuseStep 3916597 = 367181) (by norm_num)
theorem B4350773 : Blo 1717059 4350773 := bbase (se 5 (by rfl) ⟨203942, by rfl⟩ : syracuseStep 4350773 = 407885) (by norm_num)
theorem B3867461 : Blo 1717059 3867461 := bbase (se 4 (by rfl) ⟨362574, by rfl⟩ : syracuseStep 3867461 = 725149) (by norm_num)
theorem B1958737 : Blo 1717059 1958737 := bbase (se 2 (by rfl) ⟨734526, by rfl⟩ : syracuseStep 1958737 = 1469053) (by norm_num)
theorem B3916637 : Blo 1717059 3916637 := bbase (se 3 (by rfl) ⟨734369, by rfl⟩ : syracuseStep 3916637 = 1468739) (by norm_num)
theorem B3867533 : Blo 1717059 3867533 := bbase (se 3 (by rfl) ⟨725162, by rfl⟩ : syracuseStep 3867533 = 1450325) (by norm_num)
theorem B2900893 : Blo 1717059 2900893 := bbase (se 3 (by rfl) ⟨543917, by rfl⟩ : syracuseStep 2900893 = 1087835) (by norm_num)
theorem B3867605 : Blo 1717059 3867605 := bbase (se 7 (by rfl) ⟨45323, by rfl⟩ : syracuseStep 3867605 = 90647) (by norm_num)
theorem B5800949 : Blo 1717059 5800949 := bbase (se 5 (by rfl) ⟨271919, by rfl⟩ : syracuseStep 5800949 = 543839) (by norm_num)
theorem B8692757 : Blo 1717059 8692757 := bbase (se 6 (by rfl) ⟨203736, by rfl⟩ : syracuseStep 8692757 = 407473) (by norm_num)
theorem B3867677 : Blo 1717059 3867677 := bbase (se 3 (by rfl) ⟨725189, by rfl⟩ : syracuseStep 3867677 = 1450379) (by norm_num)
theorem B3671077 : Blo 1717059 3671077 := bbase (se 4 (by rfl) ⟨344163, by rfl⟩ : syracuseStep 3671077 = 688327) (by norm_num)
theorem B3261485 : Blo 1717059 3261485 := bbase (se 3 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 3261485 = 1223057) (by norm_num)
theorem B3867749 : Blo 1717059 3867749 := bbase (se 4 (by rfl) ⟨362601, by rfl⟩ : syracuseStep 3867749 = 725203) (by norm_num)
theorem B4351117 : Blo 1717059 4351117 := bbase (se 3 (by rfl) ⟨815834, by rfl⟩ : syracuseStep 4351117 = 1631669) (by norm_num)
theorem B2204821 : Blo 1717059 2204821 := bbase (se 6 (by rfl) ⟨51675, by rfl⟩ : syracuseStep 2204821 = 103351) (by norm_num)
theorem B3867821 : Blo 1717059 3867821 := bbase (se 3 (by rfl) ⟨725216, by rfl⟩ : syracuseStep 3867821 = 1450433) (by norm_num)
theorem B13935797 : Blo 1717059 13935797 := bbase (se 5 (by rfl) ⟨653240, by rfl⟩ : syracuseStep 13935797 = 1306481) (by norm_num)
theorem B3261637 : Blo 1717059 3261637 := bbase (se 4 (by rfl) ⟨305778, by rfl⟩ : syracuseStep 3261637 = 611557) (by norm_num)
theorem B3138797 : Blo 1717059 3138797 := bbase (se 3 (by rfl) ⟨588524, by rfl⟩ : syracuseStep 3138797 = 1177049) (by norm_num)
theorem B4351229 : Blo 1717059 4351229 := bbase (se 3 (by rfl) ⟨815855, by rfl⟩ : syracuseStep 4351229 = 1631711) (by norm_num)
theorem B4891909 : Blo 1717059 4891909 := bbase (se 4 (by rfl) ⟨458616, by rfl⟩ : syracuseStep 4891909 = 917233) (by norm_num)
theorem B2204933 : Blo 1717059 2204933 := bbase (se 4 (by rfl) ⟨206712, by rfl⟩ : syracuseStep 2204933 = 413425) (by norm_num)
theorem B7341349 : Blo 1717059 7341349 := bbase (se 4 (by rfl) ⟨688251, by rfl⟩ : syracuseStep 7341349 = 1376503) (by norm_num)
theorem B3917173 : Blo 1717059 3917173 := bbase (se 5 (by rfl) ⟨183617, by rfl⟩ : syracuseStep 3917173 = 367235) (by norm_num)
theorem B4646261 : Blo 1717059 4646261 := bbase (se 5 (by rfl) ⟨217793, by rfl⟩ : syracuseStep 4646261 = 435587) (by norm_num)
theorem B4892069 : Blo 1717059 4892069 := bbase (se 4 (by rfl) ⟨458631, by rfl⟩ : syracuseStep 4892069 = 917263) (by norm_num)
theorem B5801381 : Blo 1717059 5801381 := bbase (se 4 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 5801381 = 1087759) (by norm_num)
theorem B3261941 : Blo 1717059 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B35276309 : Blo 1717059 35276309 := bbase (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) (by norm_num)
theorem B3483253 : Blo 1717059 3483253 := bbase (se 5 (by rfl) ⟨163277, by rfl⟩ : syracuseStep 3483253 = 326555) (by norm_num)
theorem B2205313 : Blo 1717059 2205313 := bbase (se 2 (by rfl) ⟨826992, by rfl⟩ : syracuseStep 2205313 = 1653985) (by norm_num)
theorem B4892309 : Blo 1717059 4892309 := bbase (se 6 (by rfl) ⟨114663, by rfl⟩ : syracuseStep 4892309 = 229327) (by norm_num)
theorem B4892501 : Blo 1717059 4892501 := bbase (se 9 (by rfl) ⟨14333, by rfl⟩ : syracuseStep 4892501 = 28667) (by norm_num)
theorem B5801813 : Blo 1717059 5801813 := bbase (se 9 (by rfl) ⟨16997, by rfl⟩ : syracuseStep 5801813 = 33995) (by norm_num)
theorem B8701829 : Blo 1717059 8701829 := bbase (se 4 (by rfl) ⟨815796, by rfl⟩ : syracuseStep 8701829 = 1631593) (by norm_num)
theorem B1886129 : Blo 1717059 1886129 := bbase (se 2 (by rfl) ⟨707298, by rfl⟩ : syracuseStep 1886129 = 1414597) (by norm_num)
theorem B4409333 : Blo 1717059 4409333 := bbase (se 5 (by rfl) ⟨206687, by rfl⟩ : syracuseStep 4409333 = 413375) (by norm_num)
theorem B9291829 : Blo 1717059 9291829 := bbase (se 5 (by rfl) ⟨435554, by rfl⟩ : syracuseStep 9291829 = 871109) (by norm_num)
theorem B1960133 : Blo 1717059 1960133 := bbase (se 4 (by rfl) ⟨183762, by rfl⟩ : syracuseStep 1960133 = 367525) (by norm_num)
theorem B3262693 : Blo 1717059 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B2173169 : Blo 1717059 2173169 := bbase (se 2 (by rfl) ⟨814938, by rfl⟩ : syracuseStep 2173169 = 1629877) (by norm_num)
theorem B13224181 : Blo 1717059 13224181 := bbase (se 5 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 13224181 = 1239767) (by norm_num)
theorem B8694053 : Blo 1717059 8694053 := bbase (se 4 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 8694053 = 1630135) (by norm_num)
theorem B2173225 : Blo 1717059 2173225 := bbase (se 2 (by rfl) ⟨814959, by rfl⟩ : syracuseStep 2173225 = 1629919) (by norm_num)
theorem B7833925 : Blo 1717059 7833925 := bbase (se 4 (by rfl) ⟨734430, by rfl⟩ : syracuseStep 7833925 = 1468861) (by norm_num)
theorem B29804885 : Blo 1717059 29804885 := bbase (se 10 (by rfl) ⟨43659, by rfl⟩ : syracuseStep 29804885 = 87319) (by norm_num)
theorem B18581845 : Blo 1717059 18581845 := bbase (se 10 (by rfl) ⟨27219, by rfl⟩ : syracuseStep 18581845 = 54439) (by norm_num)
theorem B3262837 : Blo 1717059 3262837 := bbase (se 5 (by rfl) ⟨152945, by rfl⟩ : syracuseStep 3262837 = 305891) (by norm_num)
theorem B2173321 : Blo 1717059 2173321 := bbase (se 2 (by rfl) ⟨814995, by rfl⟩ : syracuseStep 2173321 = 1629991) (by norm_num)
theorem B5441941 : Blo 1717059 5441941 := bbase (se 6 (by rfl) ⟨127545, by rfl⟩ : syracuseStep 5441941 = 255091) (by norm_num)
theorem B11004437 : Blo 1717059 11004437 := bbase (se 6 (by rfl) ⟨257916, by rfl⟩ : syracuseStep 11004437 = 515833) (by norm_num)
theorem B3262997 : Blo 1717059 3262997 := bbase (se 6 (by rfl) ⟨76476, by rfl⟩ : syracuseStep 3262997 = 152953) (by norm_num)
theorem B2173493 : Blo 1717059 2173493 := bbase (se 5 (by rfl) ⟨101882, by rfl⟩ : syracuseStep 2173493 = 203765) (by norm_num)
theorem B3770957 : Blo 1717059 3770957 := bbase (se 3 (by rfl) ⟨707054, by rfl⟩ : syracuseStep 3770957 = 1414109) (by norm_num)
theorem B13052501 : Blo 1717059 13052501 := bbase (se 8 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 13052501 = 152959) (by norm_num)
theorem B2173549 : Blo 1717059 2173549 := bbase (se 3 (by rfl) ⟨407540, by rfl⟩ : syracuseStep 2173549 = 815081) (by norm_num)
theorem B3263141 : Blo 1717059 3263141 := bbase (se 4 (by rfl) ⟨305919, by rfl⟩ : syracuseStep 3263141 = 611839) (by norm_num)
theorem B2173645 : Blo 1717059 2173645 := bbase (se 3 (by rfl) ⟨407558, by rfl⟩ : syracuseStep 2173645 = 815117) (by norm_num)
theorem B4467413 : Blo 1717059 4467413 := bbase (se 7 (by rfl) ⟨52352, by rfl⟩ : syracuseStep 4467413 = 104705) (by norm_num)
theorem B6523685 : Blo 1717059 6523685 := bbase (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) (by norm_num)
theorem B4893493 : Blo 1717059 4893493 := bbase (se 5 (by rfl) ⟨229382, by rfl⟩ : syracuseStep 4893493 = 458765) (by norm_num)
theorem B2173817 : Blo 1717059 2173817 := bbase (se 2 (by rfl) ⟨815181, by rfl⟩ : syracuseStep 2173817 = 1630363) (by norm_num)
theorem B2173873 : Blo 1717059 2173873 := bbase (se 2 (by rfl) ⟨815202, by rfl⟩ : syracuseStep 2173873 = 1630405) (by norm_num)
theorem B3263429 : Blo 1717059 3263429 := bbase (se 4 (by rfl) ⟨305946, by rfl⟩ : syracuseStep 3263429 = 611893) (by norm_num)
theorem B6966245 : Blo 1717059 6966245 := bbase (se 4 (by rfl) ⟨653085, by rfl⟩ : syracuseStep 6966245 = 1306171) (by norm_num)
theorem B13044725 : Blo 1717059 13044725 := bbase (se 5 (by rfl) ⟨611471, by rfl⟩ : syracuseStep 13044725 = 1222943) (by norm_num)
theorem B2173969 : Blo 1717059 2173969 := bbase (se 2 (by rfl) ⟨815238, by rfl⟩ : syracuseStep 2173969 = 1630477) (by norm_num)
theorem B6523973 : Blo 1717059 6523973 := bbase (se 4 (by rfl) ⟨611622, by rfl⟩ : syracuseStep 6523973 = 1223245) (by norm_num)
theorem B8260709 : Blo 1717059 8260709 := bbase (se 4 (by rfl) ⟨774441, by rfl⟩ : syracuseStep 8260709 = 1548883) (by norm_num)
theorem B2174141 : Blo 1717059 2174141 := bbase (se 3 (by rfl) ⟨407651, by rfl⟩ : syracuseStep 2174141 = 815303) (by norm_num)
theorem B2575589 : Blo 1717059 2575589 := bbase (se 4 (by rfl) ⟨241461, by rfl⟩ : syracuseStep 2575589 = 482923) (by norm_num)
theorem B2174197 : Blo 1717059 2174197 := bbase (se 5 (by rfl) ⟨101915, by rfl⟩ : syracuseStep 2174197 = 203831) (by norm_num)
theorem B2575613 : Blo 1717059 2575613 := bbase (se 3 (by rfl) ⟨482927, by rfl⟩ : syracuseStep 2575613 = 965855) (by norm_num)
theorem B2575637 : Blo 1717059 2575637 := bbase (se 6 (by rfl) ⟨60366, by rfl⟩ : syracuseStep 2575637 = 120733) (by norm_num)
theorem B2575661 : Blo 1717059 2575661 := bbase (se 3 (by rfl) ⟨482936, by rfl⟩ : syracuseStep 2575661 = 965873) (by norm_num)
theorem B3484981 : Blo 1717059 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B2575685 : Blo 1717059 2575685 := bbase (se 4 (by rfl) ⟨241470, by rfl⟩ : syracuseStep 2575685 = 482941) (by norm_num)
theorem B2174293 : Blo 1717059 2174293 := bbase (se 11 (by rfl) ⟨1592, by rfl⟩ : syracuseStep 2174293 = 3185) (by norm_num)
theorem B2575709 : Blo 1717059 2575709 := bbase (se 3 (by rfl) ⟨482945, by rfl⟩ : syracuseStep 2575709 = 965891) (by norm_num)
theorem B2575733 : Blo 1717059 2575733 := bbase (se 5 (by rfl) ⟨120737, by rfl⟩ : syracuseStep 2575733 = 241475) (by norm_num)
theorem B2575757 : Blo 1717059 2575757 := bbase (se 3 (by rfl) ⟨482954, by rfl⟩ : syracuseStep 2575757 = 965909) (by norm_num)
theorem B2575781 : Blo 1717059 2575781 := bbase (se 4 (by rfl) ⟨241479, by rfl⟩ : syracuseStep 2575781 = 482959) (by norm_num)
theorem B2575805 : Blo 1717059 2575805 := bbase (se 3 (by rfl) ⟨482963, by rfl⟩ : syracuseStep 2575805 = 965927) (by norm_num)
theorem B2575829 : Blo 1717059 2575829 := bbase (se 7 (by rfl) ⟨30185, by rfl⟩ : syracuseStep 2575829 = 60371) (by norm_num)
theorem B2575853 : Blo 1717059 2575853 := bbase (se 3 (by rfl) ⟨482972, by rfl⟩ : syracuseStep 2575853 = 965945) (by norm_num)
theorem B2174465 : Blo 1717059 2174465 := bbase (se 2 (by rfl) ⟨815424, by rfl⟩ : syracuseStep 2174465 = 1630849) (by norm_num)
theorem B5795333 : Blo 1717059 5795333 := bbase (se 4 (by rfl) ⟨543312, by rfl⟩ : syracuseStep 5795333 = 1086625) (by norm_num)
theorem B2575877 : Blo 1717059 2575877 := bbase (se 4 (by rfl) ⟨241488, by rfl⟩ : syracuseStep 2575877 = 482977) (by norm_num)
theorem B3919373 : Blo 1717059 3919373 := bbase (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) (by norm_num)
theorem B2575901 : Blo 1717059 2575901 := bbase (se 3 (by rfl) ⟨482981, by rfl⟩ : syracuseStep 2575901 = 965963) (by norm_num)
theorem B2575925 : Blo 1717059 2575925 := bbase (se 5 (by rfl) ⟨120746, by rfl⟩ : syracuseStep 2575925 = 241493) (by norm_num)
theorem B8695349 : Blo 1717059 8695349 := bbase (se 5 (by rfl) ⟨407594, by rfl⟩ : syracuseStep 8695349 = 815189) (by norm_num)
theorem B2174521 : Blo 1717059 2174521 := bbase (se 2 (by rfl) ⟨815445, by rfl⟩ : syracuseStep 2174521 = 1630891) (by norm_num)
theorem B2444861 : Blo 1717059 2444861 := bbase (se 3 (by rfl) ⟨458411, by rfl⟩ : syracuseStep 2444861 = 916823) (by norm_num)
theorem B2575949 : Blo 1717059 2575949 := bbase (se 3 (by rfl) ⟨482990, by rfl⟩ : syracuseStep 2575949 = 965981) (by norm_num)
theorem B2575973 : Blo 1717059 2575973 := bbase (se 4 (by rfl) ⟨241497, by rfl⟩ : syracuseStep 2575973 = 482995) (by norm_num)
theorem B2575997 : Blo 1717059 2575997 := bbase (se 3 (by rfl) ⟨482999, by rfl⟩ : syracuseStep 2575997 = 965999) (by norm_num)
theorem B2444941 : Blo 1717059 2444941 := bbase (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) (by norm_num)
theorem B2576021 : Blo 1717059 2576021 := bbase (se 6 (by rfl) ⟨60375, by rfl⟩ : syracuseStep 2576021 = 120751) (by norm_num)
theorem B2174617 : Blo 1717059 2174617 := bbase (se 2 (by rfl) ⟨815481, by rfl⟩ : syracuseStep 2174617 = 1630963) (by norm_num)
theorem B2576045 : Blo 1717059 2576045 := bbase (se 3 (by rfl) ⟨483008, by rfl⟩ : syracuseStep 2576045 = 966017) (by norm_num)
theorem B2576069 : Blo 1717059 2576069 := bbase (se 4 (by rfl) ⟨241506, by rfl⟩ : syracuseStep 2576069 = 483013) (by norm_num)
theorem B2576093 : Blo 1717059 2576093 := bbase (se 3 (by rfl) ⟨483017, by rfl⟩ : syracuseStep 2576093 = 966035) (by norm_num)
theorem B2576117 : Blo 1717059 2576117 := bbase (se 5 (by rfl) ⟨120755, by rfl⟩ : syracuseStep 2576117 = 241511) (by norm_num)
theorem B2445061 : Blo 1717059 2445061 := bbase (se 4 (by rfl) ⟨229224, by rfl⟩ : syracuseStep 2445061 = 458449) (by norm_num)
theorem B2576141 : Blo 1717059 2576141 := bbase (se 3 (by rfl) ⟨483026, by rfl⟩ : syracuseStep 2576141 = 966053) (by norm_num)
theorem B2576165 : Blo 1717059 2576165 := bbase (se 4 (by rfl) ⟨241515, by rfl⟩ : syracuseStep 2576165 = 483031) (by norm_num)
theorem B5959477 : Blo 1717059 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B2576189 : Blo 1717059 2576189 := bbase (se 3 (by rfl) ⟨483035, by rfl⟩ : syracuseStep 2576189 = 966071) (by norm_num)
theorem B2174789 : Blo 1717059 2174789 := bbase (se 4 (by rfl) ⟨203886, by rfl⟩ : syracuseStep 2174789 = 407773) (by norm_num)
theorem B2576213 : Blo 1717059 2576213 := bbase (se 9 (by rfl) ⟨7547, by rfl⟩ : syracuseStep 2576213 = 15095) (by norm_num)
theorem B2445157 : Blo 1717059 2445157 := bbase (se 4 (by rfl) ⟨229233, by rfl⟩ : syracuseStep 2445157 = 458467) (by norm_num)
theorem B2576237 : Blo 1717059 2576237 := bbase (se 3 (by rfl) ⟨483044, by rfl⟩ : syracuseStep 2576237 = 966089) (by norm_num)
theorem B2174845 : Blo 1717059 2174845 := bbase (se 3 (by rfl) ⟨407783, by rfl⟩ : syracuseStep 2174845 = 815567) (by norm_num)
theorem B1740677 : Blo 1717059 1740677 := bbase (se 4 (by rfl) ⟨163188, by rfl⟩ : syracuseStep 1740677 = 326377) (by norm_num)
theorem B2576261 : Blo 1717059 2576261 := bbase (se 4 (by rfl) ⟨241524, by rfl⟩ : syracuseStep 2576261 = 483049) (by norm_num)
theorem B4894597 : Blo 1717059 4894597 := bbase (se 4 (by rfl) ⟨458868, by rfl⟩ : syracuseStep 4894597 = 917737) (by norm_num)
theorem B2576285 : Blo 1717059 2576285 := bbase (se 3 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 2576285 = 966107) (by norm_num)
theorem B5795765 : Blo 1717059 5795765 := bbase (se 5 (by rfl) ⟨271676, by rfl⟩ : syracuseStep 5795765 = 543353) (by norm_num)
theorem B2576309 : Blo 1717059 2576309 := bbase (se 5 (by rfl) ⟨120764, by rfl⟩ : syracuseStep 2576309 = 241529) (by norm_num)
theorem B2576333 : Blo 1717059 2576333 := bbase (se 3 (by rfl) ⟨483062, by rfl⟩ : syracuseStep 2576333 = 966125) (by norm_num)
theorem B6279125 : Blo 1717059 6279125 := bbase (se 7 (by rfl) ⟨73583, by rfl⟩ : syracuseStep 6279125 = 147167) (by norm_num)
theorem B2174941 : Blo 1717059 2174941 := bbase (se 3 (by rfl) ⟨407801, by rfl⟩ : syracuseStep 2174941 = 815603) (by norm_num)
theorem B2576357 : Blo 1717059 2576357 := bbase (se 4 (by rfl) ⟨241533, by rfl⟩ : syracuseStep 2576357 = 483067) (by norm_num)
theorem B14872565 : Blo 1717059 14872565 := bbase (se 5 (by rfl) ⟨697151, by rfl⟩ : syracuseStep 14872565 = 1394303) (by norm_num)
theorem B2576381 : Blo 1717059 2576381 := bbase (se 3 (by rfl) ⟨483071, by rfl⟩ : syracuseStep 2576381 = 966143) (by norm_num)
theorem B2576405 : Blo 1717059 2576405 := bbase (se 6 (by rfl) ⟨60384, by rfl⟩ : syracuseStep 2576405 = 120769) (by norm_num)
theorem B2576429 : Blo 1717059 2576429 := bbase (se 3 (by rfl) ⟨483080, by rfl⟩ : syracuseStep 2576429 = 966161) (by norm_num)
theorem B2576453 : Blo 1717059 2576453 := bbase (se 4 (by rfl) ⟨241542, by rfl⟩ : syracuseStep 2576453 = 483085) (by norm_num)
theorem B32206933 : Blo 1717059 32206933 := bbase (se 8 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 32206933 = 377425) (by norm_num)
theorem B2576477 : Blo 1717059 2576477 := bbase (se 3 (by rfl) ⟨483089, by rfl⟩ : syracuseStep 2576477 = 966179) (by norm_num)
theorem B2576501 : Blo 1717059 2576501 := bbase (se 5 (by rfl) ⟨120773, by rfl⟩ : syracuseStep 2576501 = 241547) (by norm_num)
theorem B2175113 : Blo 1717059 2175113 := bbase (se 2 (by rfl) ⟨815667, by rfl⟩ : syracuseStep 2175113 = 1631335) (by norm_num)
theorem B2576525 : Blo 1717059 2576525 := bbase (se 3 (by rfl) ⟨483098, by rfl⟩ : syracuseStep 2576525 = 966197) (by norm_num)
theorem B2576549 : Blo 1717059 2576549 := bbase (se 4 (by rfl) ⟨241551, by rfl⟩ : syracuseStep 2576549 = 483103) (by norm_num)
theorem B2576573 : Blo 1717059 2576573 := bbase (se 3 (by rfl) ⟨483107, by rfl⟩ : syracuseStep 2576573 = 966215) (by norm_num)
theorem B2175169 : Blo 1717059 2175169 := bbase (se 2 (by rfl) ⟨815688, by rfl⟩ : syracuseStep 2175169 = 1631377) (by norm_num)
theorem B2576597 : Blo 1717059 2576597 := bbase (se 7 (by rfl) ⟨30194, by rfl⟩ : syracuseStep 2576597 = 60389) (by norm_num)
theorem B6525157 : Blo 1717059 6525157 := bbase (se 4 (by rfl) ⟨611733, by rfl⟩ : syracuseStep 6525157 = 1223467) (by norm_num)
theorem B2576621 : Blo 1717059 2576621 := bbase (se 3 (by rfl) ⟨483116, by rfl⟩ : syracuseStep 2576621 = 966233) (by norm_num)
theorem B2576645 : Blo 1717059 2576645 := bbase (se 4 (by rfl) ⟨241560, by rfl⟩ : syracuseStep 2576645 = 483121) (by norm_num)
theorem B2576669 : Blo 1717059 2576669 := bbase (se 3 (by rfl) ⟨483125, by rfl⟩ : syracuseStep 2576669 = 966251) (by norm_num)
theorem B2175265 : Blo 1717059 2175265 := bbase (se 2 (by rfl) ⟨815724, by rfl⟩ : syracuseStep 2175265 = 1631449) (by norm_num)
theorem B2576693 : Blo 1717059 2576693 := bbase (se 5 (by rfl) ⟨120782, by rfl⟩ : syracuseStep 2576693 = 241565) (by norm_num)
theorem B2576717 : Blo 1717059 2576717 := bbase (se 3 (by rfl) ⟨483134, by rfl⟩ : syracuseStep 2576717 = 966269) (by norm_num)
theorem B7336277 : Blo 1717059 7336277 := bbase (se 10 (by rfl) ⟨10746, by rfl⟩ : syracuseStep 7336277 = 21493) (by norm_num)
theorem B2445653 : Blo 1717059 2445653 := bbase (se 10 (by rfl) ⟨3582, by rfl⟩ : syracuseStep 2445653 = 7165) (by norm_num)
theorem B5796197 : Blo 1717059 5796197 := bbase (se 4 (by rfl) ⟨543393, by rfl⟩ : syracuseStep 5796197 = 1086787) (by norm_num)
theorem B2576741 : Blo 1717059 2576741 := bbase (se 4 (by rfl) ⟨241569, by rfl⟩ : syracuseStep 2576741 = 483139) (by norm_num)
theorem B2576765 : Blo 1717059 2576765 := bbase (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) (by norm_num)
theorem B8253829 : Blo 1717059 8253829 := bbase (se 4 (by rfl) ⟨773796, by rfl⟩ : syracuseStep 8253829 = 1547593) (by norm_num)
theorem B2576789 : Blo 1717059 2576789 := bbase (se 6 (by rfl) ⟨60393, by rfl⟩ : syracuseStep 2576789 = 120787) (by norm_num)
theorem B2576813 : Blo 1717059 2576813 := bbase (se 3 (by rfl) ⟨483152, by rfl⟩ : syracuseStep 2576813 = 966305) (by norm_num)
theorem B2576837 : Blo 1717059 2576837 := bbase (se 4 (by rfl) ⟨241578, by rfl⟩ : syracuseStep 2576837 = 483157) (by norm_num)
theorem B2175437 : Blo 1717059 2175437 := bbase (se 3 (by rfl) ⟨407894, by rfl⟩ : syracuseStep 2175437 = 815789) (by norm_num)
theorem B2576861 : Blo 1717059 2576861 := bbase (se 3 (by rfl) ⟨483161, by rfl⟩ : syracuseStep 2576861 = 966323) (by norm_num)
theorem B2576885 : Blo 1717059 2576885 := bbase (se 5 (by rfl) ⟨120791, by rfl⟩ : syracuseStep 2576885 = 241583) (by norm_num)
theorem B2175493 : Blo 1717059 2175493 := bbase (se 4 (by rfl) ⟨203952, by rfl⟩ : syracuseStep 2175493 = 407905) (by norm_num)
theorem B2576909 : Blo 1717059 2576909 := bbase (se 3 (by rfl) ⟨483170, by rfl⟩ : syracuseStep 2576909 = 966341) (by norm_num)
theorem B6525461 : Blo 1717059 6525461 := bbase (se 6 (by rfl) ⟨152940, by rfl⟩ : syracuseStep 6525461 = 305881) (by norm_num)
theorem B2576933 : Blo 1717059 2576933 := bbase (se 4 (by rfl) ⟨241587, by rfl⟩ : syracuseStep 2576933 = 483175) (by norm_num)
theorem B2576957 : Blo 1717059 2576957 := bbase (se 3 (by rfl) ⟨483179, by rfl⟩ : syracuseStep 2576957 = 966359) (by norm_num)
theorem B2576981 : Blo 1717059 2576981 := bbase (se 8 (by rfl) ⟨15099, by rfl⟩ : syracuseStep 2576981 = 30199) (by norm_num)
theorem B2175589 : Blo 1717059 2175589 := bbase (se 4 (by rfl) ⟨203961, by rfl⟩ : syracuseStep 2175589 = 407923) (by norm_num)
theorem B2577005 : Blo 1717059 2577005 := bbase (se 3 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 2577005 = 966377) (by norm_num)
theorem B7336565 : Blo 1717059 7336565 := bbase (se 5 (by rfl) ⟨343901, by rfl⟩ : syracuseStep 7336565 = 687803) (by norm_num)
theorem B2577029 : Blo 1717059 2577029 := bbase (se 4 (by rfl) ⟨241596, by rfl⟩ : syracuseStep 2577029 = 483193) (by norm_num)
theorem B9786005 : Blo 1717059 9786005 := bbase (se 6 (by rfl) ⟨229359, by rfl⟩ : syracuseStep 9786005 = 458719) (by norm_num)
theorem B2577053 : Blo 1717059 2577053 := bbase (se 3 (by rfl) ⟨483197, by rfl⟩ : syracuseStep 2577053 = 966395) (by norm_num)
theorem B2577077 : Blo 1717059 2577077 := bbase (se 5 (by rfl) ⟨120800, by rfl⟩ : syracuseStep 2577077 = 241601) (by norm_num)
theorem B2577101 : Blo 1717059 2577101 := bbase (se 3 (by rfl) ⟨483206, by rfl⟩ : syracuseStep 2577101 = 966413) (by norm_num)
theorem B4346581 : Blo 1717059 4346581 := bbase (se 7 (by rfl) ⟨50936, by rfl⟩ : syracuseStep 4346581 = 101873) (by norm_num)
theorem B14684885 : Blo 1717059 14684885 := bbase (se 7 (by rfl) ⟨172088, by rfl⟩ : syracuseStep 14684885 = 344177) (by norm_num)
theorem B2577125 : Blo 1717059 2577125 := bbase (se 4 (by rfl) ⟨241605, by rfl⟩ : syracuseStep 2577125 = 483211) (by norm_num)
theorem B2577149 : Blo 1717059 2577149 := bbase (se 3 (by rfl) ⟨483215, by rfl⟩ : syracuseStep 2577149 = 966431) (by norm_num)
theorem B5796629 : Blo 1717059 5796629 := bbase (se 6 (by rfl) ⟨135858, by rfl⟩ : syracuseStep 5796629 = 271717) (by norm_num)
theorem B2577173 : Blo 1717059 2577173 := bbase (se 6 (by rfl) ⟨60402, by rfl⟩ : syracuseStep 2577173 = 120805) (by norm_num)
theorem B2577197 : Blo 1717059 2577197 := bbase (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) (by norm_num)
theorem B4346693 : Blo 1717059 4346693 := bbase (se 4 (by rfl) ⟨407502, by rfl⟩ : syracuseStep 4346693 = 815005) (by norm_num)
theorem B8696645 : Blo 1717059 8696645 := bbase (se 4 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 8696645 = 1630621) (by norm_num)
theorem B2577221 : Blo 1717059 2577221 := bbase (se 4 (by rfl) ⟨241614, by rfl⟩ : syracuseStep 2577221 = 483229) (by norm_num)
theorem B14676821 : Blo 1717059 14676821 := bbase (se 9 (by rfl) ⟨42998, by rfl⟩ : syracuseStep 14676821 = 85997) (by norm_num)
theorem B2577245 : Blo 1717059 2577245 := bbase (se 3 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 2577245 = 966467) (by norm_num)
theorem B2577269 : Blo 1717059 2577269 := bbase (se 5 (by rfl) ⟨120809, by rfl⟩ : syracuseStep 2577269 = 241619) (by norm_num)
theorem B2446205 : Blo 1717059 2446205 := bbase (se 3 (by rfl) ⟨458663, by rfl⟩ : syracuseStep 2446205 = 917327) (by norm_num)
theorem B3863429 : Blo 1717059 3863429 := bbase (se 4 (by rfl) ⟨362196, by rfl⟩ : syracuseStep 3863429 = 724393) (by norm_num)
theorem B2577293 : Blo 1717059 2577293 := bbase (se 3 (by rfl) ⟨483242, by rfl⟩ : syracuseStep 2577293 = 966485) (by norm_num)
theorem B2577317 : Blo 1717059 2577317 := bbase (se 4 (by rfl) ⟨241623, by rfl⟩ : syracuseStep 2577317 = 483247) (by norm_num)
theorem B2577341 : Blo 1717059 2577341 := bbase (se 3 (by rfl) ⟨483251, by rfl⟩ : syracuseStep 2577341 = 966503) (by norm_num)
theorem B3863501 : Blo 1717059 3863501 := bbase (se 3 (by rfl) ⟨724406, by rfl⟩ : syracuseStep 3863501 = 1448813) (by norm_num)
theorem B2577365 : Blo 1717059 2577365 := bbase (se 7 (by rfl) ⟨30203, by rfl⟩ : syracuseStep 2577365 = 60407) (by norm_num)
theorem B2577389 : Blo 1717059 2577389 := bbase (se 3 (by rfl) ⟨483260, by rfl⟩ : syracuseStep 2577389 = 966521) (by norm_num)
theorem B4346885 : Blo 1717059 4346885 := bbase (se 4 (by rfl) ⟨407520, by rfl⟩ : syracuseStep 4346885 = 815041) (by norm_num)
theorem B2577413 : Blo 1717059 2577413 := bbase (se 4 (by rfl) ⟨241632, by rfl⟩ : syracuseStep 2577413 = 483265) (by norm_num)
theorem B1741829 : Blo 1717059 1741829 := bbase (se 4 (by rfl) ⟨163296, by rfl⟩ : syracuseStep 1741829 = 326593) (by norm_num)
theorem B3863573 : Blo 1717059 3863573 := bbase (se 6 (by rfl) ⟨90552, by rfl⟩ : syracuseStep 3863573 = 181105) (by norm_num)
theorem B2577437 : Blo 1717059 2577437 := bbase (se 3 (by rfl) ⟨483269, by rfl⟩ : syracuseStep 2577437 = 966539) (by norm_num)
theorem B2577461 : Blo 1717059 2577461 := bbase (se 5 (by rfl) ⟨120818, by rfl⟩ : syracuseStep 2577461 = 241637) (by norm_num)
theorem B2577485 : Blo 1717059 2577485 := bbase (se 3 (by rfl) ⟨483278, by rfl⟩ : syracuseStep 2577485 = 966557) (by norm_num)
theorem B3863645 : Blo 1717059 3863645 := bbase (se 3 (by rfl) ⟨724433, by rfl⟩ : syracuseStep 3863645 = 1448867) (by norm_num)
theorem B2577509 : Blo 1717059 2577509 := bbase (se 4 (by rfl) ⟨241641, by rfl⟩ : syracuseStep 2577509 = 483283) (by norm_num)
theorem B2577533 : Blo 1717059 2577533 := bbase (se 3 (by rfl) ⟨483287, by rfl⟩ : syracuseStep 2577533 = 966575) (by norm_num)
theorem B2577557 : Blo 1717059 2577557 := bbase (se 6 (by rfl) ⟨60411, by rfl⟩ : syracuseStep 2577557 = 120823) (by norm_num)
theorem B3863717 : Blo 1717059 3863717 := bbase (se 4 (by rfl) ⟨362223, by rfl⟩ : syracuseStep 3863717 = 724447) (by norm_num)
theorem B2577581 : Blo 1717059 2577581 := bbase (se 3 (by rfl) ⟨483296, by rfl⟩ : syracuseStep 2577581 = 966593) (by norm_num)
theorem B5797061 : Blo 1717059 5797061 := bbase (se 4 (by rfl) ⟨543474, by rfl⟩ : syracuseStep 5797061 = 1086949) (by norm_num)
theorem B2577605 : Blo 1717059 2577605 := bbase (se 4 (by rfl) ⟨241650, by rfl⟩ : syracuseStep 2577605 = 483301) (by norm_num)
theorem B2577629 : Blo 1717059 2577629 := bbase (se 3 (by rfl) ⟨483305, by rfl⟩ : syracuseStep 2577629 = 966611) (by norm_num)
theorem B3863789 : Blo 1717059 3863789 := bbase (se 3 (by rfl) ⟨724460, by rfl⟩ : syracuseStep 3863789 = 1448921) (by norm_num)
theorem B2577653 : Blo 1717059 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B2577677 : Blo 1717059 2577677 := bbase (se 3 (by rfl) ⟨483314, by rfl⟩ : syracuseStep 2577677 = 966629) (by norm_num)
theorem B4125973 : Blo 1717059 4125973 := bbase (se 6 (by rfl) ⟨96702, by rfl⟩ : syracuseStep 4125973 = 193405) (by norm_num)
theorem B1742105 : Blo 1717059 1742105 := bbase (se 2 (by rfl) ⟨653289, by rfl⟩ : syracuseStep 1742105 = 1306579) (by norm_num)
theorem B2577701 : Blo 1717059 2577701 := bbase (se 4 (by rfl) ⟨241659, by rfl⟩ : syracuseStep 2577701 = 483319) (by norm_num)
theorem B3863861 : Blo 1717059 3863861 := bbase (se 5 (by rfl) ⟨181118, by rfl⟩ : syracuseStep 3863861 = 362237) (by norm_num)
theorem B2577725 : Blo 1717059 2577725 := bbase (se 3 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 2577725 = 966647) (by norm_num)
theorem B2577749 : Blo 1717059 2577749 := bbase (se 17 (by rfl) ⟨29, by rfl⟩ : syracuseStep 2577749 = 59) (by norm_num)
theorem B4347229 : Blo 1717059 4347229 := bbase (se 3 (by rfl) ⟨815105, by rfl⟩ : syracuseStep 4347229 = 1630211) (by norm_num)
theorem B7337317 : Blo 1717059 7337317 := bbase (se 4 (by rfl) ⟨687873, by rfl⟩ : syracuseStep 7337317 = 1375747) (by norm_num)
theorem B2577773 : Blo 1717059 2577773 := bbase (se 3 (by rfl) ⟨483332, by rfl⟩ : syracuseStep 2577773 = 966665) (by norm_num)
theorem B3863933 : Blo 1717059 3863933 := bbase (se 3 (by rfl) ⟨724487, by rfl⟩ : syracuseStep 3863933 = 1448975) (by norm_num)
theorem B2577797 : Blo 1717059 2577797 := bbase (se 4 (by rfl) ⟨241668, by rfl⟩ : syracuseStep 2577797 = 483337) (by norm_num)
theorem B2577821 : Blo 1717059 2577821 := bbase (se 3 (by rfl) ⟨483341, by rfl⟩ : syracuseStep 2577821 = 966683) (by norm_num)
theorem B11007413 : Blo 1717059 11007413 := bbase (se 5 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 11007413 = 1031945) (by norm_num)
theorem B2577845 : Blo 1717059 2577845 := bbase (se 5 (by rfl) ⟨120836, by rfl⟩ : syracuseStep 2577845 = 241673) (by norm_num)
theorem B3864005 : Blo 1717059 3864005 := bbase (se 4 (by rfl) ⟨362250, by rfl⟩ : syracuseStep 3864005 = 724501) (by norm_num)
theorem B4347341 : Blo 1717059 4347341 := bbase (se 3 (by rfl) ⟨815126, by rfl⟩ : syracuseStep 4347341 = 1630253) (by norm_num)
theorem B2577869 : Blo 1717059 2577869 := bbase (se 3 (by rfl) ⟨483350, by rfl⟩ : syracuseStep 2577869 = 966701) (by norm_num)
theorem B2577893 : Blo 1717059 2577893 := bbase (se 4 (by rfl) ⟨241677, by rfl⟩ : syracuseStep 2577893 = 483355) (by norm_num)
theorem B2577917 : Blo 1717059 2577917 := bbase (se 3 (by rfl) ⟨483359, by rfl⟩ : syracuseStep 2577917 = 966719) (by norm_num)
theorem B3864077 : Blo 1717059 3864077 := bbase (se 3 (by rfl) ⟨724514, by rfl⟩ : syracuseStep 3864077 = 1449029) (by norm_num)
theorem B10589717 : Blo 1717059 10589717 := bbase (se 6 (by rfl) ⟨248196, by rfl⟩ : syracuseStep 10589717 = 496393) (by norm_num)
theorem B2577941 : Blo 1717059 2577941 := bbase (se 6 (by rfl) ⟨60420, by rfl⟩ : syracuseStep 2577941 = 120841) (by norm_num)
theorem B2577965 : Blo 1717059 2577965 := bbase (se 3 (by rfl) ⟨483368, by rfl⟩ : syracuseStep 2577965 = 966737) (by norm_num)
theorem B2577989 : Blo 1717059 2577989 := bbase (se 4 (by rfl) ⟨241686, by rfl⟩ : syracuseStep 2577989 = 483373) (by norm_num)
theorem B1742405 : Blo 1717059 1742405 := bbase (se 4 (by rfl) ⟨163350, by rfl⟩ : syracuseStep 1742405 = 326701) (by norm_num)
theorem B3864149 : Blo 1717059 3864149 := bbase (se 8 (by rfl) ⟨22641, by rfl⟩ : syracuseStep 3864149 = 45283) (by norm_num)
theorem B2578013 : Blo 1717059 2578013 := bbase (se 3 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 2578013 = 966755) (by norm_num)
theorem B1742429 : Blo 1717059 1742429 := bbase (se 3 (by rfl) ⟨326705, by rfl⟩ : syracuseStep 1742429 = 653411) (by norm_num)
theorem B3667565 : Blo 1717059 3667565 := bbase (se 3 (by rfl) ⟨687668, by rfl⟩ : syracuseStep 3667565 = 1375337) (by norm_num)
theorem B2446957 : Blo 1717059 2446957 := bbase (se 3 (by rfl) ⟨458804, by rfl⟩ : syracuseStep 2446957 = 917609) (by norm_num)
theorem B5797493 : Blo 1717059 5797493 := bbase (se 5 (by rfl) ⟨271757, by rfl⟩ : syracuseStep 5797493 = 543515) (by norm_num)
theorem B2578037 : Blo 1717059 2578037 := bbase (se 5 (by rfl) ⟨120845, by rfl⟩ : syracuseStep 2578037 = 241691) (by norm_num)
theorem B4347533 : Blo 1717059 4347533 := bbase (se 3 (by rfl) ⟨815162, by rfl⟩ : syracuseStep 4347533 = 1630325) (by norm_num)
theorem B2578061 : Blo 1717059 2578061 := bbase (se 3 (by rfl) ⟨483386, by rfl⟩ : syracuseStep 2578061 = 966773) (by norm_num)
theorem B16504469 : Blo 1717059 16504469 := bbase (se 6 (by rfl) ⟨386823, by rfl⟩ : syracuseStep 16504469 = 773647) (by norm_num)
theorem B3864221 : Blo 1717059 3864221 := bbase (se 3 (by rfl) ⟨724541, by rfl⟩ : syracuseStep 3864221 = 1449083) (by norm_num)
theorem B5502629 : Blo 1717059 5502629 := bbase (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) (by norm_num)
theorem B2578085 : Blo 1717059 2578085 := bbase (se 4 (by rfl) ⟨241695, by rfl⟩ : syracuseStep 2578085 = 483391) (by norm_num)
theorem B2578109 : Blo 1717059 2578109 := bbase (se 3 (by rfl) ⟨483395, by rfl⟩ : syracuseStep 2578109 = 966791) (by norm_num)
theorem B6190805 : Blo 1717059 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B2578133 : Blo 1717059 2578133 := bbase (se 7 (by rfl) ⟨30212, by rfl⟩ : syracuseStep 2578133 = 60425) (by norm_num)
theorem B3864293 : Blo 1717059 3864293 := bbase (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) (by norm_num)
theorem B2578157 : Blo 1717059 2578157 := bbase (se 3 (by rfl) ⟨483404, by rfl⟩ : syracuseStep 2578157 = 966809) (by norm_num)
theorem B2897653 : Blo 1717059 2897653 := bbase (se 5 (by rfl) ⟨135827, by rfl⟩ : syracuseStep 2897653 = 271655) (by norm_num)
theorem B2578181 : Blo 1717059 2578181 := bbase (se 4 (by rfl) ⟨241704, by rfl⟩ : syracuseStep 2578181 = 483409) (by norm_num)
theorem B9418517 : Blo 1717059 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B2578205 : Blo 1717059 2578205 := bbase (se 3 (by rfl) ⟨483413, by rfl⟩ : syracuseStep 2578205 = 966827) (by norm_num)
theorem B3864365 : Blo 1717059 3864365 := bbase (se 3 (by rfl) ⟨724568, by rfl⟩ : syracuseStep 3864365 = 1449137) (by norm_num)
theorem B9787189 : Blo 1717059 9787189 := bbase (se 5 (by rfl) ⟨458774, by rfl⟩ : syracuseStep 9787189 = 917549) (by norm_num)
theorem B2578229 : Blo 1717059 2578229 := bbase (se 5 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 2578229 = 241709) (by norm_num)
theorem B2897741 : Blo 1717059 2897741 := bbase (se 3 (by rfl) ⟨543326, by rfl⟩ : syracuseStep 2897741 = 1086653) (by norm_num)
theorem B2578253 : Blo 1717059 2578253 := bbase (se 3 (by rfl) ⟨483422, by rfl⟩ : syracuseStep 2578253 = 966845) (by norm_num)
theorem B2578277 : Blo 1717059 2578277 := bbase (se 4 (by rfl) ⟨241713, by rfl⟩ : syracuseStep 2578277 = 483427) (by norm_num)
theorem B3864437 : Blo 1717059 3864437 := bbase (se 5 (by rfl) ⟨181145, by rfl⟩ : syracuseStep 3864437 = 362291) (by norm_num)
theorem B4126589 : Blo 1717059 4126589 := bbase (se 3 (by rfl) ⟨773735, by rfl⟩ : syracuseStep 4126589 = 1547471) (by norm_num)
theorem B2578301 : Blo 1717059 2578301 := bbase (se 3 (by rfl) ⟨483431, by rfl⟩ : syracuseStep 2578301 = 966863) (by norm_num)
theorem B2578325 : Blo 1717059 2578325 := bbase (se 6 (by rfl) ⟨60429, by rfl⟩ : syracuseStep 2578325 = 120859) (by norm_num)
theorem B2578349 : Blo 1717059 2578349 := bbase (se 3 (by rfl) ⟨483440, by rfl⟩ : syracuseStep 2578349 = 966881) (by norm_num)
theorem B3970997 : Blo 1717059 3970997 := bbase (se 5 (by rfl) ⟨186140, by rfl⟩ : syracuseStep 3970997 = 372281) (by norm_num)
theorem B3864509 : Blo 1717059 3864509 := bbase (se 3 (by rfl) ⟨724595, by rfl⟩ : syracuseStep 3864509 = 1449191) (by norm_num)
theorem B2578373 : Blo 1717059 2578373 := bbase (se 4 (by rfl) ⟨241722, by rfl⟩ : syracuseStep 2578373 = 483445) (by norm_num)
theorem B2897869 : Blo 1717059 2897869 := bbase (se 3 (by rfl) ⟨543350, by rfl⟩ : syracuseStep 2897869 = 1086701) (by norm_num)
theorem B3667933 : Blo 1717059 3667933 := bbase (se 3 (by rfl) ⟨687737, by rfl⟩ : syracuseStep 3667933 = 1375475) (by norm_num)
theorem B2578397 : Blo 1717059 2578397 := bbase (se 3 (by rfl) ⟨483449, by rfl⟩ : syracuseStep 2578397 = 966899) (by norm_num)
theorem B4347877 : Blo 1717059 4347877 := bbase (se 4 (by rfl) ⟨407613, by rfl⟩ : syracuseStep 4347877 = 815227) (by norm_num)
theorem B6191093 : Blo 1717059 6191093 := bbase (se 5 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 6191093 = 580415) (by norm_num)
theorem B2578421 : Blo 1717059 2578421 := bbase (se 5 (by rfl) ⟨120863, by rfl⟩ : syracuseStep 2578421 = 241727) (by norm_num)
theorem B3864581 : Blo 1717059 3864581 := bbase (se 4 (by rfl) ⟨362304, by rfl⟩ : syracuseStep 3864581 = 724609) (by norm_num)
theorem B2578445 : Blo 1717059 2578445 := bbase (se 3 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 2578445 = 966917) (by norm_num)
theorem B2897957 : Blo 1717059 2897957 := bbase (se 4 (by rfl) ⟨271683, by rfl⟩ : syracuseStep 2897957 = 543367) (by norm_num)
theorem B5797925 : Blo 1717059 5797925 := bbase (se 4 (by rfl) ⟨543555, by rfl⟩ : syracuseStep 5797925 = 1087111) (by norm_num)
theorem B2578469 : Blo 1717059 2578469 := bbase (se 4 (by rfl) ⟨241731, by rfl⟩ : syracuseStep 2578469 = 483463) (by norm_num)
theorem B4126781 : Blo 1717059 4126781 := bbase (se 3 (by rfl) ⟨773771, by rfl⟩ : syracuseStep 4126781 = 1547543) (by norm_num)
theorem B2578493 : Blo 1717059 2578493 := bbase (se 3 (by rfl) ⟨483467, by rfl⟩ : syracuseStep 2578493 = 966935) (by norm_num)
theorem B7338053 : Blo 1717059 7338053 := bbase (se 4 (by rfl) ⟨687942, by rfl⟩ : syracuseStep 7338053 = 1375885) (by norm_num)
theorem B3864653 : Blo 1717059 3864653 := bbase (se 3 (by rfl) ⟨724622, by rfl⟩ : syracuseStep 3864653 = 1449245) (by norm_num)
theorem B4347989 : Blo 1717059 4347989 := bbase (se 8 (by rfl) ⟨25476, by rfl⟩ : syracuseStep 4347989 = 50953) (by norm_num)
theorem B8697941 : Blo 1717059 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B2578517 : Blo 1717059 2578517 := bbase (se 8 (by rfl) ⟨15108, by rfl⟩ : syracuseStep 2578517 = 30217) (by norm_num)
theorem B2578541 : Blo 1717059 2578541 := bbase (se 3 (by rfl) ⟨483476, by rfl⟩ : syracuseStep 2578541 = 966953) (by norm_num)
theorem B2578565 : Blo 1717059 2578565 := bbase (se 4 (by rfl) ⟨241740, by rfl⟩ : syracuseStep 2578565 = 483481) (by norm_num)
theorem B3864725 : Blo 1717059 3864725 := bbase (se 6 (by rfl) ⟨90579, by rfl⟩ : syracuseStep 3864725 = 181159) (by norm_num)
theorem B2578589 : Blo 1717059 2578589 := bbase (se 3 (by rfl) ⟨483485, by rfl⟩ : syracuseStep 2578589 = 966971) (by norm_num)
theorem B2898085 : Blo 1717059 2898085 := bbase (se 4 (by rfl) ⟨271695, by rfl⟩ : syracuseStep 2898085 = 543391) (by norm_num)
theorem B2119861 : Blo 1717059 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B3864797 : Blo 1717059 3864797 := bbase (se 3 (by rfl) ⟨724649, by rfl⟩ : syracuseStep 3864797 = 1449299) (by norm_num)
theorem B2898173 : Blo 1717059 2898173 := bbase (se 3 (by rfl) ⟨543407, by rfl⟩ : syracuseStep 2898173 = 1086815) (by norm_num)
theorem B5224709 : Blo 1717059 5224709 := bbase (se 4 (by rfl) ⟨489816, by rfl⟩ : syracuseStep 5224709 = 979633) (by norm_num)
theorem B2939141 : Blo 1717059 2939141 := bbase (se 4 (by rfl) ⟨275544, by rfl⟩ : syracuseStep 2939141 = 551089) (by norm_num)
theorem B13220117 : Blo 1717059 13220117 := bbase (se 6 (by rfl) ⟨309846, by rfl⟩ : syracuseStep 13220117 = 619693) (by norm_num)
theorem B4348181 : Blo 1717059 4348181 := bbase (se 6 (by rfl) ⟨101910, by rfl⟩ : syracuseStep 4348181 = 203821) (by norm_num)
theorem B3864869 : Blo 1717059 3864869 := bbase (se 4 (by rfl) ⟨362331, by rfl⟩ : syracuseStep 3864869 = 724663) (by norm_num)
theorem B3864941 : Blo 1717059 3864941 := bbase (se 3 (by rfl) ⟨724676, by rfl⟩ : syracuseStep 3864941 = 1449353) (by norm_num)
theorem B2898301 : Blo 1717059 2898301 := bbase (se 3 (by rfl) ⟨543431, by rfl⟩ : syracuseStep 2898301 = 1086863) (by norm_num)
theorem B3307925 : Blo 1717059 3307925 := bbase (se 6 (by rfl) ⟨77529, by rfl⟩ : syracuseStep 3307925 = 155059) (by norm_num)
theorem B2685349 : Blo 1717059 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B1931701 : Blo 1717059 1931701 := bbase (se 5 (by rfl) ⟨90548, by rfl⟩ : syracuseStep 1931701 = 181097) (by norm_num)
theorem B3865013 : Blo 1717059 3865013 := bbase (se 5 (by rfl) ⟨181172, by rfl⟩ : syracuseStep 3865013 = 362345) (by norm_num)
theorem B2898389 : Blo 1717059 2898389 := bbase (se 7 (by rfl) ⟨33965, by rfl⟩ : syracuseStep 2898389 = 67931) (by norm_num)
theorem B5798357 : Blo 1717059 5798357 := bbase (se 7 (by rfl) ⟨67949, by rfl⟩ : syracuseStep 5798357 = 135899) (by norm_num)
theorem B1931737 : Blo 1717059 1931737 := bbase (se 2 (by rfl) ⟨724401, by rfl⟩ : syracuseStep 1931737 = 1448803) (by norm_num)
theorem B1931773 : Blo 1717059 1931773 := bbase (se 3 (by rfl) ⟨362207, by rfl⟩ : syracuseStep 1931773 = 724415) (by norm_num)
theorem B3865085 : Blo 1717059 3865085 := bbase (se 3 (by rfl) ⟨724703, by rfl⟩ : syracuseStep 3865085 = 1449407) (by norm_num)
theorem B1931809 : Blo 1717059 1931809 := bbase (se 2 (by rfl) ⟨724428, by rfl⟩ : syracuseStep 1931809 = 1448857) (by norm_num)
theorem B1931845 : Blo 1717059 1931845 := bbase (se 4 (by rfl) ⟨181110, by rfl⟩ : syracuseStep 1931845 = 362221) (by norm_num)
theorem B3865157 : Blo 1717059 3865157 := bbase (se 4 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 3865157 = 724717) (by norm_num)
theorem B2898517 : Blo 1717059 2898517 := bbase (se 8 (by rfl) ⟨16983, by rfl⟩ : syracuseStep 2898517 = 33967) (by norm_num)
theorem B1931881 : Blo 1717059 1931881 := bbase (se 2 (by rfl) ⟨724455, by rfl⟩ : syracuseStep 1931881 = 1448911) (by norm_num)
theorem B4348525 : Blo 1717059 4348525 := bbase (se 3 (by rfl) ⟨815348, by rfl⟩ : syracuseStep 4348525 = 1630697) (by norm_num)
theorem B4127357 : Blo 1717059 4127357 := bbase (se 3 (by rfl) ⟨773879, by rfl⟩ : syracuseStep 4127357 = 1547759) (by norm_num)
theorem B1931917 : Blo 1717059 1931917 := bbase (se 3 (by rfl) ⟨362234, by rfl⟩ : syracuseStep 1931917 = 724469) (by norm_num)
theorem B3865229 : Blo 1717059 3865229 := bbase (se 3 (by rfl) ⟨724730, by rfl⟩ : syracuseStep 3865229 = 1449461) (by norm_num)
theorem B1833625 : Blo 1717059 1833625 := bbase (se 2 (by rfl) ⟨687609, by rfl⟩ : syracuseStep 1833625 = 1375219) (by norm_num)
theorem B2898605 : Blo 1717059 2898605 := bbase (se 3 (by rfl) ⟨543488, by rfl⟩ : syracuseStep 2898605 = 1086977) (by norm_num)
theorem B1931953 : Blo 1717059 1931953 := bbase (se 2 (by rfl) ⟨724482, by rfl⟩ : syracuseStep 1931953 = 1448965) (by norm_num)
theorem B1931989 : Blo 1717059 1931989 := bbase (se 7 (by rfl) ⟨22640, by rfl⟩ : syracuseStep 1931989 = 45281) (by norm_num)
theorem B3865301 : Blo 1717059 3865301 := bbase (se 7 (by rfl) ⟨45296, by rfl⟩ : syracuseStep 3865301 = 90593) (by norm_num)
theorem B4348637 : Blo 1717059 4348637 := bbase (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) (by norm_num)
theorem B1833697 : Blo 1717059 1833697 := bbase (se 2 (by rfl) ⟨687636, by rfl⟩ : syracuseStep 1833697 = 1375273) (by norm_num)
theorem B1932025 : Blo 1717059 1932025 := bbase (se 2 (by rfl) ⟨724509, by rfl⟩ : syracuseStep 1932025 = 1449019) (by norm_num)
theorem B33020693 : Blo 1717059 33020693 := bbase (se 6 (by rfl) ⟨773922, by rfl⟩ : syracuseStep 33020693 = 1547845) (by norm_num)
theorem B1932061 : Blo 1717059 1932061 := bbase (se 3 (by rfl) ⟨362261, by rfl⟩ : syracuseStep 1932061 = 724523) (by norm_num)
theorem B3865373 : Blo 1717059 3865373 := bbase (se 3 (by rfl) ⟨724757, by rfl⟩ : syracuseStep 3865373 = 1449515) (by norm_num)
theorem B2898733 : Blo 1717059 2898733 := bbase (se 3 (by rfl) ⟨543512, by rfl⟩ : syracuseStep 2898733 = 1087025) (by norm_num)
theorem B1932097 : Blo 1717059 1932097 := bbase (se 2 (by rfl) ⟨724536, by rfl⟩ : syracuseStep 1932097 = 1449073) (by norm_num)
theorem B1932133 : Blo 1717059 1932133 := bbase (se 4 (by rfl) ⟨181137, by rfl⟩ : syracuseStep 1932133 = 362275) (by norm_num)
theorem B3865445 : Blo 1717059 3865445 := bbase (se 4 (by rfl) ⟨362385, by rfl⟩ : syracuseStep 3865445 = 724771) (by norm_num)
theorem B2898821 : Blo 1717059 2898821 := bbase (se 4 (by rfl) ⟨271764, by rfl⟩ : syracuseStep 2898821 = 543529) (by norm_num)
theorem B5798789 : Blo 1717059 5798789 := bbase (se 4 (by rfl) ⟨543636, by rfl⟩ : syracuseStep 5798789 = 1087273) (by norm_num)
theorem B1932169 : Blo 1717059 1932169 := bbase (se 2 (by rfl) ⟨724563, by rfl⟩ : syracuseStep 1932169 = 1449127) (by norm_num)
theorem B1833877 : Blo 1717059 1833877 := bbase (se 6 (by rfl) ⟨42981, by rfl⟩ : syracuseStep 1833877 = 85963) (by norm_num)
theorem B4348829 : Blo 1717059 4348829 := bbase (se 3 (by rfl) ⟨815405, by rfl⟩ : syracuseStep 4348829 = 1630811) (by norm_num)
theorem B1932205 : Blo 1717059 1932205 := bbase (se 3 (by rfl) ⟨362288, by rfl⟩ : syracuseStep 1932205 = 724577) (by norm_num)
theorem B3865517 : Blo 1717059 3865517 := bbase (se 3 (by rfl) ⟨724784, by rfl⟩ : syracuseStep 3865517 = 1449569) (by norm_num)
theorem B1932241 : Blo 1717059 1932241 := bbase (se 2 (by rfl) ⟨724590, by rfl⟩ : syracuseStep 1932241 = 1449181) (by norm_num)
theorem B6519797 : Blo 1717059 6519797 := bbase (se 5 (by rfl) ⟨305615, by rfl⟩ : syracuseStep 6519797 = 611231) (by norm_num)
theorem B1932277 : Blo 1717059 1932277 := bbase (se 5 (by rfl) ⟨90575, by rfl⟩ : syracuseStep 1932277 = 181151) (by norm_num)
theorem B3865589 : Blo 1717059 3865589 := bbase (se 5 (by rfl) ⟨181199, by rfl⟩ : syracuseStep 3865589 = 362399) (by norm_num)
theorem B4127741 : Blo 1717059 4127741 := bbase (se 3 (by rfl) ⟨773951, by rfl⟩ : syracuseStep 4127741 = 1547903) (by norm_num)
theorem B2898949 : Blo 1717059 2898949 := bbase (se 4 (by rfl) ⟨271776, by rfl⟩ : syracuseStep 2898949 = 543553) (by norm_num)
theorem B1932313 : Blo 1717059 1932313 := bbase (se 2 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 1932313 = 1449235) (by norm_num)
theorem B1932349 : Blo 1717059 1932349 := bbase (se 3 (by rfl) ⟨362315, by rfl⟩ : syracuseStep 1932349 = 724631) (by norm_num)
theorem B3865661 : Blo 1717059 3865661 := bbase (se 3 (by rfl) ⟨724811, by rfl⟩ : syracuseStep 3865661 = 1449623) (by norm_num)
theorem B2751565 : Blo 1717059 2751565 := bbase (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) (by norm_num)
theorem B4406357 : Blo 1717059 4406357 := bbase (se 8 (by rfl) ⟨25818, by rfl⟩ : syracuseStep 4406357 = 51637) (by norm_num)
theorem B2899037 : Blo 1717059 2899037 := bbase (se 3 (by rfl) ⟨543569, by rfl⟩ : syracuseStep 2899037 = 1087139) (by norm_num)
theorem B1932385 : Blo 1717059 1932385 := bbase (se 2 (by rfl) ⟨724644, by rfl⟩ : syracuseStep 1932385 = 1449289) (by norm_num)
theorem B1932421 : Blo 1717059 1932421 := bbase (se 4 (by rfl) ⟨181164, by rfl⟩ : syracuseStep 1932421 = 362329) (by norm_num)
theorem B3865733 : Blo 1717059 3865733 := bbase (se 4 (by rfl) ⟨362412, by rfl⟩ : syracuseStep 3865733 = 724825) (by norm_num)
theorem B1932457 : Blo 1717059 1932457 := bbase (se 2 (by rfl) ⟨724671, by rfl⟩ : syracuseStep 1932457 = 1449343) (by norm_num)
theorem B1932493 : Blo 1717059 1932493 := bbase (se 3 (by rfl) ⟨362342, by rfl⟩ : syracuseStep 1932493 = 724685) (by norm_num)
theorem B3865805 : Blo 1717059 3865805 := bbase (se 3 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 3865805 = 1449677) (by norm_num)
theorem B2899165 : Blo 1717059 2899165 := bbase (se 3 (by rfl) ⟨543593, by rfl⟩ : syracuseStep 2899165 = 1087187) (by norm_num)
theorem B4406501 : Blo 1717059 4406501 := bbase (se 4 (by rfl) ⟨413109, by rfl⟩ : syracuseStep 4406501 = 826219) (by norm_num)
theorem B1932529 : Blo 1717059 1932529 := bbase (se 2 (by rfl) ⟨724698, by rfl⟩ : syracuseStep 1932529 = 1449397) (by norm_num)
theorem B4349173 : Blo 1717059 4349173 := bbase (se 5 (by rfl) ⟨203867, by rfl⟩ : syracuseStep 4349173 = 407735) (by norm_num)
theorem B4406525 : Blo 1717059 4406525 := bbase (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) (by norm_num)
theorem B6520085 : Blo 1717059 6520085 := bbase (se 6 (by rfl) ⟨152814, by rfl⟩ : syracuseStep 6520085 = 305629) (by norm_num)
theorem B1932565 : Blo 1717059 1932565 := bbase (se 6 (by rfl) ⟨45294, by rfl⟩ : syracuseStep 1932565 = 90589) (by norm_num)
theorem B3865877 : Blo 1717059 3865877 := bbase (se 6 (by rfl) ⟨90606, by rfl⟩ : syracuseStep 3865877 = 181213) (by norm_num)
theorem B2899253 : Blo 1717059 2899253 := bbase (se 5 (by rfl) ⟨135902, by rfl⟩ : syracuseStep 2899253 = 271805) (by norm_num)
theorem B5799221 : Blo 1717059 5799221 := bbase (se 5 (by rfl) ⟨271838, by rfl⟩ : syracuseStep 5799221 = 543677) (by norm_num)
theorem B1932601 : Blo 1717059 1932601 := bbase (se 2 (by rfl) ⟨724725, by rfl⟩ : syracuseStep 1932601 = 1449451) (by norm_num)
theorem B1834321 : Blo 1717059 1834321 := bbase (se 2 (by rfl) ⟨687870, by rfl⟩ : syracuseStep 1834321 = 1375741) (by norm_num)
theorem B1932637 : Blo 1717059 1932637 := bbase (se 3 (by rfl) ⟨362369, by rfl⟩ : syracuseStep 1932637 = 724739) (by norm_num)
theorem B3865949 : Blo 1717059 3865949 := bbase (se 3 (by rfl) ⟨724865, by rfl⟩ : syracuseStep 3865949 = 1449731) (by norm_num)
theorem B4349285 : Blo 1717059 4349285 := bbase (se 4 (by rfl) ⟨407745, by rfl⟩ : syracuseStep 4349285 = 815491) (by norm_num)
theorem B8699237 : Blo 1717059 8699237 := bbase (se 4 (by rfl) ⟨815553, by rfl⟩ : syracuseStep 8699237 = 1631107) (by norm_num)
theorem B1932673 : Blo 1717059 1932673 := bbase (se 2 (by rfl) ⟨724752, by rfl⟩ : syracuseStep 1932673 = 1449505) (by norm_num)
theorem B2063765 : Blo 1717059 2063765 := bbase (se 6 (by rfl) ⟨48369, by rfl⟩ : syracuseStep 2063765 = 96739) (by norm_num)
theorem B1932709 : Blo 1717059 1932709 := bbase (se 4 (by rfl) ⟨181191, by rfl⟩ : syracuseStep 1932709 = 362383) (by norm_num)
theorem B3866021 : Blo 1717059 3866021 := bbase (se 4 (by rfl) ⟨362439, by rfl⟩ : syracuseStep 3866021 = 724879) (by norm_num)
theorem B2899381 : Blo 1717059 2899381 := bbase (se 5 (by rfl) ⟨135908, by rfl⟩ : syracuseStep 2899381 = 271817) (by norm_num)
theorem B3669437 : Blo 1717059 3669437 := bbase (se 3 (by rfl) ⟨688019, by rfl⟩ : syracuseStep 3669437 = 1376039) (by norm_num)
theorem B1932745 : Blo 1717059 1932745 := bbase (se 2 (by rfl) ⟨724779, by rfl⟩ : syracuseStep 1932745 = 1449559) (by norm_num)
theorem B1834445 : Blo 1717059 1834445 := bbase (se 3 (by rfl) ⟨343958, by rfl⟩ : syracuseStep 1834445 = 687917) (by norm_num)
theorem B1932781 : Blo 1717059 1932781 := bbase (se 3 (by rfl) ⟨362396, by rfl⟩ : syracuseStep 1932781 = 724793) (by norm_num)
theorem B3866093 : Blo 1717059 3866093 := bbase (se 3 (by rfl) ⟨724892, by rfl⟩ : syracuseStep 3866093 = 1449785) (by norm_num)
theorem B2899469 : Blo 1717059 2899469 := bbase (se 3 (by rfl) ⟨543650, by rfl⟩ : syracuseStep 2899469 = 1087301) (by norm_num)
theorem B1932817 : Blo 1717059 1932817 := bbase (se 2 (by rfl) ⟨724806, by rfl⟩ : syracuseStep 1932817 = 1449613) (by norm_num)
theorem B4349477 : Blo 1717059 4349477 := bbase (se 4 (by rfl) ⟨407763, by rfl⟩ : syracuseStep 4349477 = 815527) (by norm_num)
theorem B14114357 : Blo 1717059 14114357 := bbase (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) (by norm_num)
theorem B2203189 : Blo 1717059 2203189 := bbase (se 5 (by rfl) ⟨103274, by rfl⟩ : syracuseStep 2203189 = 206549) (by norm_num)
theorem B1932853 : Blo 1717059 1932853 := bbase (se 5 (by rfl) ⟨90602, by rfl⟩ : syracuseStep 1932853 = 181205) (by norm_num)
theorem B3866165 : Blo 1717059 3866165 := bbase (se 5 (by rfl) ⟨181226, by rfl⟩ : syracuseStep 3866165 = 362453) (by norm_num)
theorem B3669581 : Blo 1717059 3669581 := bbase (se 3 (by rfl) ⟨688046, by rfl⟩ : syracuseStep 3669581 = 1376093) (by norm_num)
theorem B1932889 : Blo 1717059 1932889 := bbase (se 2 (by rfl) ⟨724833, by rfl⟩ : syracuseStep 1932889 = 1449667) (by norm_num)
theorem B3259997 : Blo 1717059 3259997 := bbase (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) (by norm_num)
theorem B1932925 : Blo 1717059 1932925 := bbase (se 3 (by rfl) ⟨362423, by rfl⟩ : syracuseStep 1932925 = 724847) (by norm_num)
theorem B3866237 : Blo 1717059 3866237 := bbase (se 3 (by rfl) ⟨724919, by rfl⟩ : syracuseStep 3866237 = 1449839) (by norm_num)
theorem B2899597 : Blo 1717059 2899597 := bbase (se 3 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 2899597 = 1087349) (by norm_num)
theorem B1932961 : Blo 1717059 1932961 := bbase (se 2 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 1932961 = 1449721) (by norm_num)
theorem B1932997 : Blo 1717059 1932997 := bbase (se 4 (by rfl) ⟨181218, by rfl⟩ : syracuseStep 1932997 = 362437) (by norm_num)
theorem B3866309 : Blo 1717059 3866309 := bbase (se 4 (by rfl) ⟨362466, by rfl⟩ : syracuseStep 3866309 = 724933) (by norm_num)
theorem B1834697 : Blo 1717059 1834697 := bbase (se 2 (by rfl) ⟨688011, by rfl⟩ : syracuseStep 1834697 = 1376023) (by norm_num)
theorem B2612957 : Blo 1717059 2612957 := bbase (se 3 (by rfl) ⟨489929, by rfl⟩ : syracuseStep 2612957 = 979859) (by norm_num)
theorem B2064101 : Blo 1717059 2064101 := bbase (se 4 (by rfl) ⟨193509, by rfl⟩ : syracuseStep 2064101 = 387019) (by norm_num)
theorem B2899685 : Blo 1717059 2899685 := bbase (se 4 (by rfl) ⟨271845, by rfl⟩ : syracuseStep 2899685 = 543691) (by norm_num)
theorem B5799653 : Blo 1717059 5799653 := bbase (se 4 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 5799653 = 1087435) (by norm_num)
theorem B1933033 : Blo 1717059 1933033 := bbase (se 2 (by rfl) ⟨724887, by rfl⟩ : syracuseStep 1933033 = 1449775) (by norm_num)
theorem B2752237 : Blo 1717059 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B9789173 : Blo 1717059 9789173 := bbase (se 5 (by rfl) ⟨458867, by rfl⟩ : syracuseStep 9789173 = 917735) (by norm_num)
theorem B1933069 : Blo 1717059 1933069 := bbase (se 3 (by rfl) ⟨362450, by rfl⟩ : syracuseStep 1933069 = 724901) (by norm_num)
theorem B3866381 : Blo 1717059 3866381 := bbase (se 3 (by rfl) ⟨724946, by rfl⟩ : syracuseStep 3866381 = 1449893) (by norm_num)
theorem B1933105 : Blo 1717059 1933105 := bbase (se 2 (by rfl) ⟨724914, by rfl⟩ : syracuseStep 1933105 = 1449829) (by norm_num)
theorem B4644661 : Blo 1717059 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B1933141 : Blo 1717059 1933141 := bbase (se 9 (by rfl) ⟨5663, by rfl⟩ : syracuseStep 1933141 = 11327) (by norm_num)
theorem B3866453 : Blo 1717059 3866453 := bbase (se 9 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 3866453 = 22655) (by norm_num)
theorem B2064217 : Blo 1717059 2064217 := bbase (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) (by norm_num)
theorem B2899813 : Blo 1717059 2899813 := bbase (se 4 (by rfl) ⟨271857, by rfl⟩ : syracuseStep 2899813 = 543715) (by norm_num)
theorem B5504885 : Blo 1717059 5504885 := bbase (se 5 (by rfl) ⟨258041, by rfl⟩ : syracuseStep 5504885 = 516083) (by norm_num)
theorem B1933177 : Blo 1717059 1933177 := bbase (se 2 (by rfl) ⟨724941, by rfl⟩ : syracuseStep 1933177 = 1449883) (by norm_num)
theorem B4349821 : Blo 1717059 4349821 := bbase (se 3 (by rfl) ⟨815591, by rfl⟩ : syracuseStep 4349821 = 1631183) (by norm_num)
theorem B1933213 : Blo 1717059 1933213 := bbase (se 3 (by rfl) ⟨362477, by rfl⟩ : syracuseStep 1933213 = 724955) (by norm_num)
theorem B3866525 : Blo 1717059 3866525 := bbase (se 3 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 3866525 = 1449947) (by norm_num)
theorem B2064289 : Blo 1717059 2064289 := bbase (se 2 (by rfl) ⟨774108, by rfl⟩ : syracuseStep 2064289 = 1548217) (by norm_num)
theorem B3669941 : Blo 1717059 3669941 := bbase (se 5 (by rfl) ⟨172028, by rfl⟩ : syracuseStep 3669941 = 344057) (by norm_num)
theorem B2064313 : Blo 1717059 2064313 := bbase (se 2 (by rfl) ⟨774117, by rfl⟩ : syracuseStep 2064313 = 1548235) (by norm_num)
theorem B2899901 : Blo 1717059 2899901 := bbase (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) (by norm_num)
theorem B1933249 : Blo 1717059 1933249 := bbase (se 2 (by rfl) ⟨724968, by rfl⟩ : syracuseStep 1933249 = 1449937) (by norm_num)
theorem B1933285 : Blo 1717059 1933285 := bbase (se 4 (by rfl) ⟨181245, by rfl⟩ : syracuseStep 1933285 = 362491) (by norm_num)
theorem B3866597 : Blo 1717059 3866597 := bbase (se 4 (by rfl) ⟨362493, by rfl⟩ : syracuseStep 3866597 = 724987) (by norm_num)
theorem B4349933 : Blo 1717059 4349933 := bbase (se 3 (by rfl) ⟨815612, by rfl⟩ : syracuseStep 4349933 = 1631225) (by norm_num)
theorem B5505013 : Blo 1717059 5505013 := bbase (se 5 (by rfl) ⟨258047, by rfl⟩ : syracuseStep 5505013 = 516095) (by norm_num)
theorem B4644877 : Blo 1717059 4644877 := bstep (se 3 (by rfl) ⟨870914, by rfl⟩ : syracuseStep 4644877 = 1741829) B1741829
theorem B4128817 : Blo 1717059 4128817 := bstep (se 2 (by rfl) ⟨1548306, by rfl⟩ : syracuseStep 4128817 = 3096613) B3096613
theorem B3260483 : Blo 1717059 3260483 := bstep (se 1 (by rfl) ⟨2445362, by rfl⟩ : syracuseStep 3260483 = 4890725) B4890725
theorem B3866705 : Blo 1717059 3866705 := bstep (se 2 (by rfl) ⟨1450014, by rfl⟩ : syracuseStep 3866705 = 2900029) B2900029
theorem B3866723 : Blo 1717059 3866723 := bstep (se 1 (by rfl) ⟨2900042, by rfl⟩ : syracuseStep 3866723 = 5800085) B5800085
theorem B1933411 : Blo 1717059 1933411 := bstep (se 1 (by rfl) ⟨1450058, by rfl⟩ : syracuseStep 1933411 = 2900117) B2900117
theorem B42942577 : Blo 1717059 42942577 := bstep (se 2 (by rfl) ⟨16103466, by rfl⟩ : syracuseStep 42942577 = 32206933) B32206933
theorem B2900083 : Blo 1717059 2900083 := bstep (se 1 (by rfl) ⟨2175062, by rfl⟩ : syracuseStep 2900083 = 4350125) B4350125
theorem B4890851 : Blo 1717059 4890851 := bstep (se 1 (by rfl) ⟨3668138, by rfl⟩ : syracuseStep 4890851 = 7336277) B7336277
theorem B1933555 : Blo 1717059 1933555 := bstep (se 1 (by rfl) ⟨1450166, by rfl⟩ : syracuseStep 1933555 = 2900333) B2900333
theorem B2900225 : Blo 1717059 2900225 := bstep (se 2 (by rfl) ⟨1087584, by rfl⟩ : syracuseStep 2900225 = 2175169) B2175169
theorem B22028557 : Blo 1717059 22028557 := bstep (se 3 (by rfl) ⟨4130354, by rfl⟩ : syracuseStep 22028557 = 8260709) B8260709
theorem B8700209 : Blo 1717059 8700209 := bstep (se 2 (by rfl) ⟨3262578, by rfl⟩ : syracuseStep 8700209 = 6525157) B6525157
theorem B4350257 : Blo 1717059 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B5505347 : Blo 1717059 5505347 := bstep (se 1 (by rfl) ⟨4129010, by rfl⟩ : syracuseStep 5505347 = 8258021) B8258021
theorem B4350307 : Blo 1717059 4350307 := bstep (se 1 (by rfl) ⟨3262730, by rfl⟩ : syracuseStep 4350307 = 6525461) B6525461
theorem B5800301 : Blo 1717059 5800301 := bstep (se 3 (by rfl) ⟨1087556, by rfl⟩ : syracuseStep 5800301 = 2175113) B2175113
theorem B3866993 : Blo 1717059 3866993 := bstep (se 2 (by rfl) ⟨1450122, by rfl⟩ : syracuseStep 3866993 = 2900245) B2900245
theorem B2900353 : Blo 1717059 2900353 := bstep (se 2 (by rfl) ⟨1087632, by rfl⟩ : syracuseStep 2900353 = 2175265) B2175265
theorem B3867011 : Blo 1717059 3867011 := bstep (se 1 (by rfl) ⟨2900258, by rfl⟩ : syracuseStep 3867011 = 5800517) B5800517
theorem B1933699 : Blo 1717059 1933699 := bstep (se 1 (by rfl) ⟨1450274, by rfl⟩ : syracuseStep 1933699 = 2900549) B2900549
theorem B11010437 : Blo 1717059 11010437 := bstep (se 4 (by rfl) ⟨1032228, by rfl⟩ : syracuseStep 11010437 = 2064457) B2064457
theorem B4891043 : Blo 1717059 4891043 := bstep (se 1 (by rfl) ⟨3668282, by rfl⟩ : syracuseStep 4891043 = 7336565) B7336565
theorem B5800355 : Blo 1717059 5800355 := bstep (se 1 (by rfl) ⟨4350266, by rfl⟩ : syracuseStep 5800355 = 8700533) B8700533
theorem B2900387 : Blo 1717059 2900387 := bstep (se 1 (by rfl) ⟨2175290, by rfl⟩ : syracuseStep 2900387 = 4350581) B4350581
theorem B10445233 : Blo 1717059 10445233 := bstep (se 2 (by rfl) ⟨3916962, by rfl⟩ : syracuseStep 10445233 = 7833925) B7833925
theorem B9789923 : Blo 1717059 9789923 := bstep (se 1 (by rfl) ⟨7342442, by rfl⟩ : syracuseStep 9789923 = 14684885) B14684885
theorem B4350449 : Blo 1717059 4350449 := bstep (se 2 (by rfl) ⟨1631418, by rfl⟩ : syracuseStep 4350449 = 3262837) B3262837
theorem B5227021 : Blo 1717059 5227021 := bstep (se 3 (by rfl) ⟨980066, by rfl⟩ : syracuseStep 5227021 = 1960133) B1960133
theorem B1933843 : Blo 1717059 1933843 := bstep (se 1 (by rfl) ⟨1450382, by rfl⟩ : syracuseStep 1933843 = 2900765) B2900765
theorem B2900515 : Blo 1717059 2900515 := bstep (se 1 (by rfl) ⟨2175386, by rfl⟩ : syracuseStep 2900515 = 4350773) B4350773
theorem B3580465 : Blo 1717059 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B3867281 : Blo 1717059 3867281 := bstep (se 2 (by rfl) ⟨1450230, by rfl⟩ : syracuseStep 3867281 = 2900461) B2900461
theorem B3867299 : Blo 1717059 3867299 := bstep (se 1 (by rfl) ⟨2900474, by rfl⟩ : syracuseStep 3867299 = 5800949) B5800949
theorem B5800625 : Blo 1717059 5800625 := bstep (se 2 (by rfl) ⟨2175234, by rfl⟩ : syracuseStep 5800625 = 4350469) B4350469
theorem B2900657 : Blo 1717059 2900657 := bstep (se 2 (by rfl) ⟨1087746, by rfl⟩ : syracuseStep 2900657 = 2175493) B2175493
theorem B4645613 : Blo 1717059 4645613 := bstep (se 3 (by rfl) ⟨871052, by rfl⟩ : syracuseStep 4645613 = 1742105) B1742105
theorem B9290531 : Blo 1717059 9290531 := bstep (se 1 (by rfl) ⟨6967898, by rfl⟩ : syracuseStep 9290531 = 13935797) B13935797
theorem B2900785 : Blo 1717059 2900785 := bstep (se 2 (by rfl) ⟨1087794, by rfl⟩ : syracuseStep 2900785 = 2175589) B2175589
theorem B2900819 : Blo 1717059 2900819 := bstep (se 1 (by rfl) ⟨2175614, by rfl⟩ : syracuseStep 2900819 = 4351229) B4351229
theorem B6521741 : Blo 1717059 6521741 := bstep (se 3 (by rfl) ⟨1222826, by rfl⟩ : syracuseStep 6521741 = 2445653) B2445653
theorem B3867569 : Blo 1717059 3867569 := bstep (se 2 (by rfl) ⟨1450338, by rfl⟩ : syracuseStep 3867569 = 2900677) B2900677
theorem B3261379 : Blo 1717059 3261379 := bstep (se 1 (by rfl) ⟨2446034, by rfl⟩ : syracuseStep 3261379 = 4892069) B4892069
theorem B3867587 : Blo 1717059 3867587 := bstep (se 1 (by rfl) ⟨2900690, by rfl⟩ : syracuseStep 3867587 = 5801381) B5801381
theorem B11305925 : Blo 1717059 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B5506001 : Blo 1717059 5506001 := bstep (se 2 (by rfl) ⟨2064750, by rfl⟩ : syracuseStep 5506001 = 4129501) B4129501
theorem B11002979 : Blo 1717059 11002979 := bstep (se 1 (by rfl) ⟨8252234, by rfl⟩ : syracuseStep 11002979 = 16504469) B16504469
theorem B3261539 : Blo 1717059 3261539 := bstep (se 1 (by rfl) ⟨2446154, by rfl⟩ : syracuseStep 3261539 = 4892309) B4892309
theorem B4891853 : Blo 1717059 4891853 := bstep (se 3 (by rfl) ⟨917222, by rfl⟩ : syracuseStep 4891853 = 1834445) B1834445
theorem B5801165 : Blo 1717059 5801165 := bstep (se 3 (by rfl) ⟨1087718, by rfl⟩ : syracuseStep 5801165 = 2175437) B2175437
theorem B3867857 : Blo 1717059 3867857 := bstep (se 2 (by rfl) ⟨1450446, by rfl⟩ : syracuseStep 3867857 = 2900893) B2900893
theorem B3867875 : Blo 1717059 3867875 := bstep (se 1 (by rfl) ⟨2900906, by rfl⟩ : syracuseStep 3867875 = 5801813) B5801813
theorem B5801219 : Blo 1717059 5801219 := bstep (se 1 (by rfl) ⟨4350914, by rfl⟩ : syracuseStep 5801219 = 8701829) B8701829
theorem B2647331 : Blo 1717059 2647331 := bstep (se 1 (by rfl) ⟨1985498, by rfl⟩ : syracuseStep 2647331 = 3970997) B3970997
theorem B4892035 : Blo 1717059 4892035 := bstep (se 1 (by rfl) ⟨3669026, by rfl⟩ : syracuseStep 4892035 = 7338053) B7338053
theorem B29345165 : Blo 1717059 29345165 := bstep (se 3 (by rfl) ⟨5502218, by rfl⟩ : syracuseStep 29345165 = 11004437) B11004437
theorem B1959427 : Blo 1717059 1959427 := bstep (se 1 (by rfl) ⟨1469570, by rfl⟩ : syracuseStep 1959427 = 2939141) B2939141
theorem B4646413 : Blo 1717059 4646413 := bstep (se 3 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 4646413 = 1742405) B1742405
theorem B5801489 : Blo 1717059 5801489 := bstep (se 2 (by rfl) ⟨2175558, by rfl⟩ : syracuseStep 5801489 = 4351117) B4351117
theorem B4646477 : Blo 1717059 4646477 := bstep (se 3 (by rfl) ⟨871214, by rfl⟩ : syracuseStep 4646477 = 1742429) B1742429
theorem B6522545 : Blo 1717059 6522545 := bstep (se 2 (by rfl) ⟨2445954, by rfl⟩ : syracuseStep 6522545 = 4891909) B4891909
theorem B8701667 : Blo 1717059 8701667 := bstep (se 1 (by rfl) ⟨6526250, by rfl⟩ : syracuseStep 8701667 = 13052501) B13052501
theorem B4646641 : Blo 1717059 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B9783089 : Blo 1717059 9783089 := bstep (se 2 (by rfl) ⟨3668658, by rfl⟩ : syracuseStep 9783089 = 7337317) B7337317
theorem B22013795 : Blo 1717059 22013795 := bstep (se 1 (by rfl) ⟨16510346, by rfl⟩ : syracuseStep 22013795 = 33020693) B33020693
theorem B4892525 : Blo 1717059 4892525 := bstep (se 3 (by rfl) ⟨917348, by rfl⟩ : syracuseStep 4892525 = 1834697) B1834697
theorem B11913101 : Blo 1717059 11913101 := bstep (se 3 (by rfl) ⟨2233706, by rfl⟩ : syracuseStep 11913101 = 4467413) B4467413
theorem B7341965 : Blo 1717059 7341965 := bstep (se 3 (by rfl) ⟨1376618, by rfl⟩ : syracuseStep 7341965 = 2753237) B2753237
theorem B3262609 : Blo 1717059 3262609 := bstep (se 2 (by rfl) ⟨1223478, by rfl⟩ : syracuseStep 3262609 = 2446957) B2446957
theorem B6523213 : Blo 1717059 6523213 := bstep (se 3 (by rfl) ⟨1223102, by rfl⟩ : syracuseStep 6523213 = 2446205) B2446205
theorem B2173331 : Blo 1717059 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B8702477 : Blo 1717059 8702477 := bstep (se 3 (by rfl) ⟨1631714, by rfl⟩ : syracuseStep 8702477 = 3263429) B3263429
theorem B16509581 : Blo 1717059 16509581 := bstep (se 3 (by rfl) ⟨3095546, by rfl⟩ : syracuseStep 16509581 = 6191093) B6191093
theorem B9915043 : Blo 1717059 9915043 := bstep (se 1 (by rfl) ⟨7436282, by rfl⟩ : syracuseStep 9915043 = 14872565) B14872565
theorem B12389105 : Blo 1717059 12389105 := bstep (se 2 (by rfl) ⟨4645914, by rfl⟩ : syracuseStep 12389105 = 9291829) B9291829
theorem B11750285 : Blo 1717059 11750285 := bstep (se 3 (by rfl) ⟨2203178, by rfl⟩ : syracuseStep 11750285 = 4406357) B4406357
theorem B4959149 : Blo 1717059 4959149 := bstep (se 3 (by rfl) ⟨929840, by rfl⟩ : syracuseStep 4959149 = 1859681) B1859681
theorem B2321347 : Blo 1717059 2321347 := bstep (se 1 (by rfl) ⟨1741010, by rfl⟩ : syracuseStep 2321347 = 3482021) B3482021
theorem B11750341 : Blo 1717059 11750341 := bstep (se 4 (by rfl) ⟨1101594, by rfl⟩ : syracuseStep 11750341 = 2203189) B2203189
theorem B17632241 : Blo 1717059 17632241 := bstep (se 2 (by rfl) ⟨6612090, by rfl⟩ : syracuseStep 17632241 = 13224181) B13224181
theorem B4893709 : Blo 1717059 4893709 := bstep (se 3 (by rfl) ⟨917570, by rfl⟩ : syracuseStep 4893709 = 1835141) B1835141
theorem B2174035 : Blo 1717059 2174035 := bstep (se 1 (by rfl) ⟨1630526, by rfl⟩ : syracuseStep 2174035 = 3261053) B3261053
theorem B5221475 : Blo 1717059 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B6524003 : Blo 1717059 6524003 := bstep (se 1 (by rfl) ⟨4893002, by rfl⟩ : syracuseStep 6524003 = 9786005) B9786005
theorem B24775793 : Blo 1717059 24775793 := bstep (se 2 (by rfl) ⟨9290922, by rfl⟩ : syracuseStep 24775793 = 18581845) B18581845
theorem B11005105 : Blo 1717059 11005105 := bstep (se 2 (by rfl) ⟨4126914, by rfl⟩ : syracuseStep 11005105 = 8253829) B8253829
theorem B2174131 : Blo 1717059 2174131 := bstep (se 1 (by rfl) ⟨1630598, by rfl⟩ : syracuseStep 2174131 = 3261197) B3261197
theorem B9784547 : Blo 1717059 9784547 := bstep (se 1 (by rfl) ⟨7338410, by rfl⟩ : syracuseStep 9784547 = 14676821) B14676821
theorem B2575601 : Blo 1717059 2575601 := bstep (se 2 (by rfl) ⟨965850, by rfl⟩ : syracuseStep 2575601 = 1931701) B1931701
theorem B8695025 : Blo 1717059 8695025 := bstep (se 2 (by rfl) ⟨3260634, by rfl⟩ : syracuseStep 8695025 = 6521269) B6521269
theorem B4467953 : Blo 1717059 4467953 := bstep (se 2 (by rfl) ⟨1675482, by rfl⟩ : syracuseStep 4467953 = 3350965) B3350965
theorem B2575619 : Blo 1717059 2575619 := bstep (se 1 (by rfl) ⟨1931714, by rfl⟩ : syracuseStep 2575619 = 3863429) B3863429
theorem B11750669 : Blo 1717059 11750669 := bstep (se 3 (by rfl) ⟨2203250, by rfl⟩ : syracuseStep 11750669 = 4406501) B4406501
theorem B2575649 : Blo 1717059 2575649 := bstep (se 2 (by rfl) ⟨965868, by rfl⟩ : syracuseStep 2575649 = 1931737) B1931737
theorem B5795117 : Blo 1717059 5795117 := bstep (se 3 (by rfl) ⟨1086584, by rfl⟩ : syracuseStep 5795117 = 2173169) B2173169
theorem B2575667 : Blo 1717059 2575667 := bstep (se 1 (by rfl) ⟨1931750, by rfl⟩ : syracuseStep 2575667 = 3863501) B3863501
theorem B2575697 : Blo 1717059 2575697 := bstep (se 2 (by rfl) ⟨965886, by rfl⟩ : syracuseStep 2575697 = 1931773) B1931773
theorem B5795171 : Blo 1717059 5795171 := bstep (se 1 (by rfl) ⟨4346378, by rfl⟩ : syracuseStep 5795171 = 8692757) B8692757
theorem B2575715 : Blo 1717059 2575715 := bstep (se 1 (by rfl) ⟨1931786, by rfl⟩ : syracuseStep 2575715 = 3863573) B3863573
theorem B2575745 : Blo 1717059 2575745 := bstep (se 2 (by rfl) ⟨965904, by rfl⟩ : syracuseStep 2575745 = 1931809) B1931809
theorem B2575763 : Blo 1717059 2575763 := bstep (se 1 (by rfl) ⟨1931822, by rfl⟩ : syracuseStep 2575763 = 3863645) B3863645
theorem B2575793 : Blo 1717059 2575793 := bstep (se 2 (by rfl) ⟨965922, by rfl⟩ : syracuseStep 2575793 = 1931845) B1931845
theorem B2575811 : Blo 1717059 2575811 := bstep (se 1 (by rfl) ⟨1931858, by rfl⟩ : syracuseStep 2575811 = 3863717) B3863717
theorem B5221837 : Blo 1717059 5221837 := bstep (se 3 (by rfl) ⟨979094, by rfl⟩ : syracuseStep 5221837 = 1958189) B1958189
theorem B2575841 : Blo 1717059 2575841 := bstep (se 2 (by rfl) ⟨965940, by rfl⟩ : syracuseStep 2575841 = 1931881) B1931881
theorem B2575859 : Blo 1717059 2575859 := bstep (se 1 (by rfl) ⟨1931894, by rfl⟩ : syracuseStep 2575859 = 3863789) B3863789
theorem B2575889 : Blo 1717059 2575889 := bstep (se 2 (by rfl) ⟨965958, by rfl⟩ : syracuseStep 2575889 = 1931917) B1931917
theorem B2444833 : Blo 1717059 2444833 := bstep (se 2 (by rfl) ⟨916812, by rfl⟩ : syracuseStep 2444833 = 1833625) B1833625
theorem B2575907 : Blo 1717059 2575907 := bstep (se 1 (by rfl) ⟨1931930, by rfl⟩ : syracuseStep 2575907 = 3863861) B3863861
theorem B2575937 : Blo 1717059 2575937 := bstep (se 2 (by rfl) ⟨965976, by rfl⟩ : syracuseStep 2575937 = 1931953) B1931953
theorem B2575955 : Blo 1717059 2575955 := bstep (se 1 (by rfl) ⟨1931966, by rfl⟩ : syracuseStep 2575955 = 3863933) B3863933
theorem B5795441 : Blo 1717059 5795441 := bstep (se 2 (by rfl) ⟨2173290, by rfl⟩ : syracuseStep 5795441 = 4346581) B4346581
theorem B2575985 : Blo 1717059 2575985 := bstep (se 2 (by rfl) ⟨965994, by rfl⟩ : syracuseStep 2575985 = 1931989) B1931989
theorem B2576003 : Blo 1717059 2576003 := bstep (se 1 (by rfl) ⟨1932002, by rfl⟩ : syracuseStep 2576003 = 3864005) B3864005
theorem B12390029 : Blo 1717059 12390029 := bstep (se 3 (by rfl) ⟨2323130, by rfl⟩ : syracuseStep 12390029 = 4646261) B4646261
theorem B2576033 : Blo 1717059 2576033 := bstep (se 2 (by rfl) ⟨966012, by rfl⟩ : syracuseStep 2576033 = 1932025) B1932025
theorem B2174627 : Blo 1717059 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B2576051 : Blo 1717059 2576051 := bstep (se 1 (by rfl) ⟨1932038, by rfl⟩ : syracuseStep 2576051 = 3864077) B3864077
theorem B2576081 : Blo 1717059 2576081 := bstep (se 2 (by rfl) ⟨966030, by rfl⟩ : syracuseStep 2576081 = 1932061) B1932061
theorem B2576099 : Blo 1717059 2576099 := bstep (se 1 (by rfl) ⟨1932074, by rfl⟩ : syracuseStep 2576099 = 3864149) B3864149
theorem B5222129 : Blo 1717059 5222129 := bstep (se 2 (by rfl) ⟨1958298, by rfl⟩ : syracuseStep 5222129 = 3916597) B3916597
theorem B6524657 : Blo 1717059 6524657 := bstep (se 2 (by rfl) ⟨2446746, by rfl⟩ : syracuseStep 6524657 = 4893493) B4893493
theorem B2576129 : Blo 1717059 2576129 := bstep (se 2 (by rfl) ⟨966048, by rfl⟩ : syracuseStep 2576129 = 1932097) B1932097
theorem B2576147 : Blo 1717059 2576147 := bstep (se 1 (by rfl) ⟨1932110, by rfl⟩ : syracuseStep 2576147 = 3864221) B3864221
theorem B2576177 : Blo 1717059 2576177 := bstep (se 2 (by rfl) ⟨966066, by rfl⟩ : syracuseStep 2576177 = 1932133) B1932133
theorem B2576195 : Blo 1717059 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B2576225 : Blo 1717059 2576225 := bstep (se 2 (by rfl) ⟨966084, by rfl⟩ : syracuseStep 2576225 = 1932169) B1932169
theorem B6279011 : Blo 1717059 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B2445169 : Blo 1717059 2445169 := bstep (se 2 (by rfl) ⟨916938, by rfl⟩ : syracuseStep 2445169 = 1833877) B1833877
theorem B2576243 : Blo 1717059 2576243 := bstep (se 1 (by rfl) ⟨1932182, by rfl⟩ : syracuseStep 2576243 = 3864365) B3864365
theorem B2576273 : Blo 1717059 2576273 := bstep (se 2 (by rfl) ⟨966102, by rfl⟩ : syracuseStep 2576273 = 1932205) B1932205
theorem B2576291 : Blo 1717059 2576291 := bstep (se 1 (by rfl) ⟨1932218, by rfl⟩ : syracuseStep 2576291 = 3864437) B3864437
theorem B2576321 : Blo 1717059 2576321 := bstep (se 2 (by rfl) ⟨966120, by rfl⟩ : syracuseStep 2576321 = 1932241) B1932241
theorem B2576339 : Blo 1717059 2576339 := bstep (se 1 (by rfl) ⟨1932254, by rfl⟩ : syracuseStep 2576339 = 3864509) B3864509
theorem B2576369 : Blo 1717059 2576369 := bstep (se 2 (by rfl) ⟨966138, by rfl⟩ : syracuseStep 2576369 = 1932277) B1932277
theorem B2576387 : Blo 1717059 2576387 := bstep (se 1 (by rfl) ⟨1932290, by rfl⟩ : syracuseStep 2576387 = 3864581) B3864581
theorem B2576417 : Blo 1717059 2576417 := bstep (se 2 (by rfl) ⟨966156, by rfl⟩ : syracuseStep 2576417 = 1932313) B1932313
theorem B4894769 : Blo 1717059 4894769 := bstep (se 2 (by rfl) ⟨1835538, by rfl⟩ : syracuseStep 4894769 = 3671077) B3671077
theorem B2576435 : Blo 1717059 2576435 := bstep (se 1 (by rfl) ⟨1932326, by rfl⟩ : syracuseStep 2576435 = 3864653) B3864653
theorem B2576465 : Blo 1717059 2576465 := bstep (se 2 (by rfl) ⟨966174, by rfl⟩ : syracuseStep 2576465 = 1932349) B1932349
theorem B2576483 : Blo 1717059 2576483 := bstep (se 1 (by rfl) ⟨1932362, by rfl⟩ : syracuseStep 2576483 = 3864725) B3864725
theorem B2576513 : Blo 1717059 2576513 := bstep (se 2 (by rfl) ⟨966192, by rfl⟩ : syracuseStep 2576513 = 1932385) B1932385
theorem B5795981 : Blo 1717059 5795981 := bstep (se 3 (by rfl) ⟨1086746, by rfl⟩ : syracuseStep 5795981 = 2173493) B2173493
theorem B2576531 : Blo 1717059 2576531 := bstep (se 1 (by rfl) ⟨1932398, by rfl⟩ : syracuseStep 2576531 = 3864797) B3864797
theorem B2576561 : Blo 1717059 2576561 := bstep (se 2 (by rfl) ⟨966210, by rfl⟩ : syracuseStep 2576561 = 1932421) B1932421
theorem B5796035 : Blo 1717059 5796035 := bstep (se 1 (by rfl) ⟨4347026, by rfl⟩ : syracuseStep 5796035 = 8694053) B8694053
theorem B2576579 : Blo 1717059 2576579 := bstep (se 1 (by rfl) ⟨1932434, by rfl⟩ : syracuseStep 2576579 = 3864869) B3864869
theorem B9785549 : Blo 1717059 9785549 := bstep (se 3 (by rfl) ⟨1834790, by rfl⟩ : syracuseStep 9785549 = 3669581) B3669581
theorem B2576609 : Blo 1717059 2576609 := bstep (se 2 (by rfl) ⟨966228, by rfl⟩ : syracuseStep 2576609 = 1932457) B1932457
theorem B19869923 : Blo 1717059 19869923 := bstep (se 1 (by rfl) ⟨14902442, by rfl⟩ : syracuseStep 19869923 = 29804885) B29804885
theorem B2576627 : Blo 1717059 2576627 := bstep (se 1 (by rfl) ⟨1932470, by rfl⟩ : syracuseStep 2576627 = 3864941) B3864941
theorem B2576657 : Blo 1717059 2576657 := bstep (se 2 (by rfl) ⟨966246, by rfl⟩ : syracuseStep 2576657 = 1932493) B1932493
theorem B2576675 : Blo 1717059 2576675 := bstep (se 1 (by rfl) ⟨1932506, by rfl⟩ : syracuseStep 2576675 = 3865013) B3865013
theorem B2576705 : Blo 1717059 2576705 := bstep (se 2 (by rfl) ⟨966264, by rfl⟩ : syracuseStep 2576705 = 1932529) B1932529
theorem B2576723 : Blo 1717059 2576723 := bstep (se 1 (by rfl) ⟨1932542, by rfl⟩ : syracuseStep 2576723 = 3865085) B3865085
theorem B2175331 : Blo 1717059 2175331 := bstep (se 1 (by rfl) ⟨1631498, by rfl⟩ : syracuseStep 2175331 = 3262997) B3262997
theorem B5501297 : Blo 1717059 5501297 := bstep (se 2 (by rfl) ⟨2062986, by rfl⟩ : syracuseStep 5501297 = 4125973) B4125973
theorem B2576753 : Blo 1717059 2576753 := bstep (se 2 (by rfl) ⟨966282, by rfl⟩ : syracuseStep 2576753 = 1932565) B1932565
theorem B2576771 : Blo 1717059 2576771 := bstep (se 1 (by rfl) ⟨1932578, by rfl⟩ : syracuseStep 2576771 = 3865157) B3865157
theorem B2576801 : Blo 1717059 2576801 := bstep (se 2 (by rfl) ⟨966300, by rfl⟩ : syracuseStep 2576801 = 1932601) B1932601
theorem B2576819 : Blo 1717059 2576819 := bstep (se 1 (by rfl) ⟨1932614, by rfl⟩ : syracuseStep 2576819 = 3865229) B3865229
theorem B2445761 : Blo 1717059 2445761 := bstep (se 2 (by rfl) ⟨917160, by rfl⟩ : syracuseStep 2445761 = 1834321) B1834321
theorem B2175427 : Blo 1717059 2175427 := bstep (se 1 (by rfl) ⟨1631570, by rfl⟩ : syracuseStep 2175427 = 3263141) B3263141
theorem B13939141 : Blo 1717059 13939141 := bstep (se 4 (by rfl) ⟨1306794, by rfl⟩ : syracuseStep 13939141 = 2613589) B2613589
theorem B5796305 : Blo 1717059 5796305 := bstep (se 2 (by rfl) ⟨2173614, by rfl⟩ : syracuseStep 5796305 = 4347229) B4347229
theorem B2576849 : Blo 1717059 2576849 := bstep (se 2 (by rfl) ⟨966318, by rfl⟩ : syracuseStep 2576849 = 1932637) B1932637
theorem B2576867 : Blo 1717059 2576867 := bstep (se 1 (by rfl) ⟨1932650, by rfl⟩ : syracuseStep 2576867 = 3865301) B3865301
theorem B5222897 : Blo 1717059 5222897 := bstep (se 2 (by rfl) ⟨1958586, by rfl⟩ : syracuseStep 5222897 = 3917173) B3917173
theorem B2576897 : Blo 1717059 2576897 := bstep (se 2 (by rfl) ⟨966336, by rfl⟩ : syracuseStep 2576897 = 1932673) B1932673
theorem B2576915 : Blo 1717059 2576915 := bstep (se 1 (by rfl) ⟨1932686, by rfl⟩ : syracuseStep 2576915 = 3865373) B3865373
theorem B2576945 : Blo 1717059 2576945 := bstep (se 2 (by rfl) ⟨966354, by rfl⟩ : syracuseStep 2576945 = 1932709) B1932709
theorem B2576963 : Blo 1717059 2576963 := bstep (se 1 (by rfl) ⟨1932722, by rfl⟩ : syracuseStep 2576963 = 3865445) B3865445
theorem B6967885 : Blo 1717059 6967885 := bstep (se 3 (by rfl) ⟨1306478, by rfl⟩ : syracuseStep 6967885 = 2612957) B2612957
theorem B2576993 : Blo 1717059 2576993 := bstep (se 2 (by rfl) ⟨966372, by rfl⟩ : syracuseStep 2576993 = 1932745) B1932745
theorem B2577011 : Blo 1717059 2577011 := bstep (se 1 (by rfl) ⟨1932758, by rfl⟩ : syracuseStep 2577011 = 3865517) B3865517
theorem B2577041 : Blo 1717059 2577041 := bstep (se 2 (by rfl) ⟨966390, by rfl⟩ : syracuseStep 2577041 = 1932781) B1932781
theorem B4346531 : Blo 1717059 4346531 := bstep (se 1 (by rfl) ⟨3259898, by rfl⟩ : syracuseStep 4346531 = 6519797) B6519797
theorem B8696483 : Blo 1717059 8696483 := bstep (se 1 (by rfl) ⟨6522362, by rfl⟩ : syracuseStep 8696483 = 13044725) B13044725
theorem B2577059 : Blo 1717059 2577059 := bstep (se 1 (by rfl) ⟨1932794, by rfl⟩ : syracuseStep 2577059 = 3865589) B3865589
theorem B2577089 : Blo 1717059 2577089 := bstep (se 2 (by rfl) ⟨966408, by rfl⟩ : syracuseStep 2577089 = 1932817) B1932817
theorem B2577107 : Blo 1717059 2577107 := bstep (se 1 (by rfl) ⟨1932830, by rfl⟩ : syracuseStep 2577107 = 3865661) B3865661
theorem B2577137 : Blo 1717059 2577137 := bstep (se 2 (by rfl) ⟨966426, by rfl⟩ : syracuseStep 2577137 = 1932853) B1932853
theorem B2577155 : Blo 1717059 2577155 := bstep (se 1 (by rfl) ⟨1932866, by rfl⟩ : syracuseStep 2577155 = 3865733) B3865733
theorem B2577185 : Blo 1717059 2577185 := bstep (se 2 (by rfl) ⟨966444, by rfl⟩ : syracuseStep 2577185 = 1932889) B1932889
theorem B2577203 : Blo 1717059 2577203 := bstep (se 1 (by rfl) ⟨1932902, by rfl⟩ : syracuseStep 2577203 = 3865805) B3865805
theorem B1717059 : Blo 1717059 1717059 := bstep (se 1 (by rfl) ⟨1287794, by rfl⟩ : syracuseStep 1717059 = 2575589) B2575589
theorem B2577233 : Blo 1717059 2577233 := bstep (se 2 (by rfl) ⟨966462, by rfl⟩ : syracuseStep 2577233 = 1932925) B1932925
theorem B1717075 : Blo 1717059 1717075 := bstep (se 1 (by rfl) ⟨1287806, by rfl⟩ : syracuseStep 1717075 = 2575613) B2575613
theorem B2937683 : Blo 1717059 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B1717091 : Blo 1717059 1717091 := bstep (se 1 (by rfl) ⟨1287818, by rfl⟩ : syracuseStep 1717091 = 2575637) B2575637
theorem B4346723 : Blo 1717059 4346723 := bstep (se 1 (by rfl) ⟨3260042, by rfl⟩ : syracuseStep 4346723 = 6520085) B6520085
theorem B2577251 : Blo 1717059 2577251 := bstep (se 1 (by rfl) ⟨1932938, by rfl⟩ : syracuseStep 2577251 = 3865877) B3865877
theorem B1717107 : Blo 1717059 1717107 := bstep (se 1 (by rfl) ⟨1287830, by rfl⟩ : syracuseStep 1717107 = 2575661) B2575661
theorem B2577281 : Blo 1717059 2577281 := bstep (se 2 (by rfl) ⟨966480, by rfl⟩ : syracuseStep 2577281 = 1932961) B1932961
theorem B1717123 : Blo 1717059 1717123 := bstep (se 1 (by rfl) ⟨1287842, by rfl⟩ : syracuseStep 1717123 = 2575685) B2575685
theorem B13046669 : Blo 1717059 13046669 := bstep (se 3 (by rfl) ⟨2446250, by rfl⟩ : syracuseStep 13046669 = 4892501) B4892501
theorem B1717139 : Blo 1717059 1717139 := bstep (se 1 (by rfl) ⟨1287854, by rfl⟩ : syracuseStep 1717139 = 2575709) B2575709
theorem B2577299 : Blo 1717059 2577299 := bstep (se 1 (by rfl) ⟨1932974, by rfl⟩ : syracuseStep 2577299 = 3865949) B3865949
theorem B1717155 : Blo 1717059 1717155 := bstep (se 1 (by rfl) ⟨1287866, by rfl⟩ : syracuseStep 1717155 = 2575733) B2575733
theorem B2577329 : Blo 1717059 2577329 := bstep (se 2 (by rfl) ⟨966498, by rfl⟩ : syracuseStep 2577329 = 1932997) B1932997
theorem B1717171 : Blo 1717059 1717171 := bstep (se 1 (by rfl) ⟨1287878, by rfl⟩ : syracuseStep 1717171 = 2575757) B2575757
theorem B1717187 : Blo 1717059 1717187 := bstep (se 1 (by rfl) ⟨1287890, by rfl⟩ : syracuseStep 1717187 = 2575781) B2575781
theorem B2577347 : Blo 1717059 2577347 := bstep (se 1 (by rfl) ⟨1933010, by rfl⟩ : syracuseStep 2577347 = 3866021) B3866021
theorem B1717203 : Blo 1717059 1717203 := bstep (se 1 (by rfl) ⟨1287902, by rfl⟩ : syracuseStep 1717203 = 2575805) B2575805
theorem B2446291 : Blo 1717059 2446291 := bstep (se 1 (by rfl) ⟨1834718, by rfl⟩ : syracuseStep 2446291 = 3669437) B3669437
theorem B2577377 : Blo 1717059 2577377 := bstep (se 2 (by rfl) ⟨966516, by rfl⟩ : syracuseStep 2577377 = 1933033) B1933033
theorem B1717219 : Blo 1717059 1717219 := bstep (se 1 (by rfl) ⟨1287914, by rfl⟩ : syracuseStep 1717219 = 2575829) B2575829
theorem B5796845 : Blo 1717059 5796845 := bstep (se 3 (by rfl) ⟨1086908, by rfl⟩ : syracuseStep 5796845 = 2173817) B2173817
theorem B3863537 : Blo 1717059 3863537 := bstep (se 2 (by rfl) ⟨1448826, by rfl⟩ : syracuseStep 3863537 = 2897653) B2897653
theorem B1717235 : Blo 1717059 1717235 := bstep (se 1 (by rfl) ⟨1287926, by rfl⟩ : syracuseStep 1717235 = 2575853) B2575853
theorem B2577395 : Blo 1717059 2577395 := bstep (se 1 (by rfl) ⟨1933046, by rfl⟩ : syracuseStep 2577395 = 3866093) B3866093
theorem B3863555 : Blo 1717059 3863555 := bstep (se 1 (by rfl) ⟨2897666, by rfl⟩ : syracuseStep 3863555 = 5795333) B5795333
theorem B1717251 : Blo 1717059 1717251 := bstep (se 1 (by rfl) ⟨1287938, by rfl⟩ : syracuseStep 1717251 = 2575877) B2575877
theorem B4641805 : Blo 1717059 4641805 := bstep (se 3 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 4641805 = 1740677) B1740677
theorem B2577425 : Blo 1717059 2577425 := bstep (se 2 (by rfl) ⟨966534, by rfl⟩ : syracuseStep 2577425 = 1933069) B1933069
theorem B1717267 : Blo 1717059 1717267 := bstep (se 1 (by rfl) ⟨1287950, by rfl⟩ : syracuseStep 1717267 = 2575901) B2575901
theorem B9409571 : Blo 1717059 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B1717283 : Blo 1717059 1717283 := bstep (se 1 (by rfl) ⟨1287962, by rfl⟩ : syracuseStep 1717283 = 2575925) B2575925
theorem B5796899 : Blo 1717059 5796899 := bstep (se 1 (by rfl) ⟨4347674, by rfl⟩ : syracuseStep 5796899 = 8695349) B8695349
theorem B2577443 : Blo 1717059 2577443 := bstep (se 1 (by rfl) ⟨1933082, by rfl⟩ : syracuseStep 2577443 = 3866165) B3866165
theorem B1717299 : Blo 1717059 1717299 := bstep (se 1 (by rfl) ⟨1287974, by rfl⟩ : syracuseStep 1717299 = 2575949) B2575949
theorem B2577473 : Blo 1717059 2577473 := bstep (se 2 (by rfl) ⟨966552, by rfl⟩ : syracuseStep 2577473 = 1933105) B1933105
theorem B1717315 : Blo 1717059 1717315 := bstep (se 1 (by rfl) ⟨1287986, by rfl⟩ : syracuseStep 1717315 = 2575973) B2575973
theorem B1717331 : Blo 1717059 1717331 := bstep (se 1 (by rfl) ⟨1287998, by rfl⟩ : syracuseStep 1717331 = 2575997) B2575997
theorem B2577491 : Blo 1717059 2577491 := bstep (se 1 (by rfl) ⟨1933118, by rfl⟩ : syracuseStep 2577491 = 3866237) B3866237
theorem B1717347 : Blo 1717059 1717347 := bstep (se 1 (by rfl) ⟨1288010, by rfl⟩ : syracuseStep 1717347 = 2576021) B2576021
theorem B2577521 : Blo 1717059 2577521 := bstep (se 2 (by rfl) ⟨966570, by rfl⟩ : syracuseStep 2577521 = 1933141) B1933141
theorem B1717363 : Blo 1717059 1717363 := bstep (se 1 (by rfl) ⟨1288022, by rfl⟩ : syracuseStep 1717363 = 2576045) B2576045
theorem B1717379 : Blo 1717059 1717379 := bstep (se 1 (by rfl) ⟨1288034, by rfl⟩ : syracuseStep 1717379 = 2576069) B2576069
theorem B2577539 : Blo 1717059 2577539 := bstep (se 1 (by rfl) ⟨1933154, by rfl⟩ : syracuseStep 2577539 = 3866309) B3866309
theorem B1717395 : Blo 1717059 1717395 := bstep (se 1 (by rfl) ⟨1288046, by rfl⟩ : syracuseStep 1717395 = 2576093) B2576093
theorem B2577569 : Blo 1717059 2577569 := bstep (se 2 (by rfl) ⟨966588, by rfl⟩ : syracuseStep 2577569 = 1933177) B1933177
theorem B1717411 : Blo 1717059 1717411 := bstep (se 1 (by rfl) ⟨1288058, by rfl⟩ : syracuseStep 1717411 = 2576117) B2576117
theorem B6526115 : Blo 1717059 6526115 := bstep (se 1 (by rfl) ⟨4894586, by rfl⟩ : syracuseStep 6526115 = 9789173) B9789173
theorem B6526129 : Blo 1717059 6526129 := bstep (se 2 (by rfl) ⟨2447298, by rfl⟩ : syracuseStep 6526129 = 4894597) B4894597
theorem B1717427 : Blo 1717059 1717427 := bstep (se 1 (by rfl) ⟨1288070, by rfl⟩ : syracuseStep 1717427 = 2576141) B2576141
theorem B2577587 : Blo 1717059 2577587 := bstep (se 1 (by rfl) ⟨1933190, by rfl⟩ : syracuseStep 2577587 = 3866381) B3866381
theorem B1717443 : Blo 1717059 1717443 := bstep (se 1 (by rfl) ⟨1288082, by rfl⟩ : syracuseStep 1717443 = 2576165) B2576165
theorem B2577617 : Blo 1717059 2577617 := bstep (se 2 (by rfl) ⟨966606, by rfl⟩ : syracuseStep 2577617 = 1933213) B1933213
theorem B1717459 : Blo 1717059 1717459 := bstep (se 1 (by rfl) ⟨1288094, by rfl⟩ : syracuseStep 1717459 = 2576189) B2576189
theorem B1717475 : Blo 1717059 1717475 := bstep (se 1 (by rfl) ⟨1288106, by rfl⟩ : syracuseStep 1717475 = 2576213) B2576213
theorem B2577635 : Blo 1717059 2577635 := bstep (se 1 (by rfl) ⟨1933226, by rfl⟩ : syracuseStep 2577635 = 3866453) B3866453
theorem B1717491 : Blo 1717059 1717491 := bstep (se 1 (by rfl) ⟨1288118, by rfl⟩ : syracuseStep 1717491 = 2576237) B2576237
theorem B2577665 : Blo 1717059 2577665 := bstep (se 2 (by rfl) ⟨966624, by rfl⟩ : syracuseStep 2577665 = 1933249) B1933249
theorem B1717507 : Blo 1717059 1717507 := bstep (se 1 (by rfl) ⟨1288130, by rfl⟩ : syracuseStep 1717507 = 2576261) B2576261
theorem B3863825 : Blo 1717059 3863825 := bstep (se 2 (by rfl) ⟨1448934, by rfl⟩ : syracuseStep 3863825 = 2897869) B2897869
theorem B1717523 : Blo 1717059 1717523 := bstep (se 1 (by rfl) ⟨1288142, by rfl⟩ : syracuseStep 1717523 = 2576285) B2576285
theorem B2577683 : Blo 1717059 2577683 := bstep (se 1 (by rfl) ⟨1933262, by rfl⟩ : syracuseStep 2577683 = 3866525) B3866525
theorem B3863843 : Blo 1717059 3863843 := bstep (se 1 (by rfl) ⟨2897882, by rfl⟩ : syracuseStep 3863843 = 5795765) B5795765
theorem B1717539 : Blo 1717059 1717539 := bstep (se 1 (by rfl) ⟨1288154, by rfl⟩ : syracuseStep 1717539 = 2576309) B2576309
theorem B2446627 : Blo 1717059 2446627 := bstep (se 1 (by rfl) ⟨1834970, by rfl⟩ : syracuseStep 2446627 = 3669941) B3669941
theorem B5797169 : Blo 1717059 5797169 := bstep (se 2 (by rfl) ⟨2173938, by rfl⟩ : syracuseStep 5797169 = 4347877) B4347877
theorem B1717555 : Blo 1717059 1717555 := bstep (se 1 (by rfl) ⟨1288166, by rfl⟩ : syracuseStep 1717555 = 2576333) B2576333
theorem B2577713 : Blo 1717059 2577713 := bstep (se 2 (by rfl) ⟨966642, by rfl⟩ : syracuseStep 2577713 = 1933285) B1933285
theorem B1717571 : Blo 1717059 1717571 := bstep (se 1 (by rfl) ⟨1288178, by rfl⟩ : syracuseStep 1717571 = 2576357) B2576357
theorem B2577731 : Blo 1717059 2577731 := bstep (se 1 (by rfl) ⟨1933298, by rfl⟩ : syracuseStep 2577731 = 3866597) B3866597
theorem B1717587 : Blo 1717059 1717587 := bstep (se 1 (by rfl) ⟨1288190, by rfl⟩ : syracuseStep 1717587 = 2576381) B2576381
theorem B2577761 : Blo 1717059 2577761 := bstep (se 2 (by rfl) ⟨966660, by rfl⟩ : syracuseStep 2577761 = 1933321) B1933321
theorem B1717603 : Blo 1717059 1717603 := bstep (se 1 (by rfl) ⟨1288202, by rfl⟩ : syracuseStep 1717603 = 2576405) B2576405
theorem B1717619 : Blo 1717059 1717619 := bstep (se 1 (by rfl) ⟨1288214, by rfl⟩ : syracuseStep 1717619 = 2576429) B2576429
theorem B2577779 : Blo 1717059 2577779 := bstep (se 1 (by rfl) ⟨1933334, by rfl⟩ : syracuseStep 2577779 = 3866669) B3866669
theorem B1717635 : Blo 1717059 1717635 := bstep (se 1 (by rfl) ⟨1288226, by rfl⟩ : syracuseStep 1717635 = 2576453) B2576453
theorem B2577809 : Blo 1717059 2577809 := bstep (se 2 (by rfl) ⟨966678, by rfl⟩ : syracuseStep 2577809 = 1933357) B1933357
theorem B1717651 : Blo 1717059 1717651 := bstep (se 1 (by rfl) ⟨1288238, by rfl⟩ : syracuseStep 1717651 = 2576477) B2576477
theorem B1717667 : Blo 1717059 1717667 := bstep (se 1 (by rfl) ⟨1288250, by rfl⟩ : syracuseStep 1717667 = 2576501) B2576501
theorem B2577827 : Blo 1717059 2577827 := bstep (se 1 (by rfl) ⟨1933370, by rfl⟩ : syracuseStep 2577827 = 3866741) B3866741
theorem B1717683 : Blo 1717059 1717683 := bstep (se 1 (by rfl) ⟨1288262, by rfl⟩ : syracuseStep 1717683 = 2576525) B2576525
theorem B2577857 : Blo 1717059 2577857 := bstep (se 2 (by rfl) ⟨966696, by rfl⟩ : syracuseStep 2577857 = 1933393) B1933393
theorem B1717699 : Blo 1717059 1717699 := bstep (se 1 (by rfl) ⟨1288274, by rfl⟩ : syracuseStep 1717699 = 2576549) B2576549
theorem B8697293 : Blo 1717059 8697293 := bstep (se 3 (by rfl) ⟨1630742, by rfl⟩ : syracuseStep 8697293 = 3261485) B3261485
theorem B1717715 : Blo 1717059 1717715 := bstep (se 1 (by rfl) ⟨1288286, by rfl⟩ : syracuseStep 1717715 = 2576573) B2576573
theorem B2577875 : Blo 1717059 2577875 := bstep (se 1 (by rfl) ⟨1933406, by rfl⟩ : syracuseStep 2577875 = 3866813) B3866813
theorem B1717731 : Blo 1717059 1717731 := bstep (se 1 (by rfl) ⟨1288298, by rfl⟩ : syracuseStep 1717731 = 2576597) B2576597
theorem B2577905 : Blo 1717059 2577905 := bstep (se 2 (by rfl) ⟨966714, by rfl⟩ : syracuseStep 2577905 = 1933429) B1933429
theorem B1717747 : Blo 1717059 1717747 := bstep (se 1 (by rfl) ⟨1288310, by rfl⟩ : syracuseStep 1717747 = 2576621) B2576621
theorem B1717763 : Blo 1717059 1717763 := bstep (se 1 (by rfl) ⟨1288322, by rfl⟩ : syracuseStep 1717763 = 2576645) B2576645
theorem B2577923 : Blo 1717059 2577923 := bstep (se 1 (by rfl) ⟨1933442, by rfl⟩ : syracuseStep 2577923 = 3866885) B3866885
theorem B1717779 : Blo 1717059 1717779 := bstep (se 1 (by rfl) ⟨1288334, by rfl⟩ : syracuseStep 1717779 = 2576669) B2576669
theorem B2577953 : Blo 1717059 2577953 := bstep (se 2 (by rfl) ⟨966732, by rfl⟩ : syracuseStep 2577953 = 1933465) B1933465
theorem B1717795 : Blo 1717059 1717795 := bstep (se 1 (by rfl) ⟨1288346, by rfl⟩ : syracuseStep 1717795 = 2576693) B2576693
theorem B3864113 : Blo 1717059 3864113 := bstep (se 2 (by rfl) ⟨1449042, by rfl⟩ : syracuseStep 3864113 = 2898085) B2898085
theorem B1717811 : Blo 1717059 1717811 := bstep (se 1 (by rfl) ⟨1288358, by rfl⟩ : syracuseStep 1717811 = 2576717) B2576717
theorem B2577971 : Blo 1717059 2577971 := bstep (se 1 (by rfl) ⟨1933478, by rfl⟩ : syracuseStep 2577971 = 3866957) B3866957
theorem B3864131 : Blo 1717059 3864131 := bstep (se 1 (by rfl) ⟨2898098, by rfl⟩ : syracuseStep 3864131 = 5796197) B5796197
theorem B1717827 : Blo 1717059 1717827 := bstep (se 1 (by rfl) ⟨1288370, by rfl⟩ : syracuseStep 1717827 = 2576741) B2576741
theorem B2578001 : Blo 1717059 2578001 := bstep (se 2 (by rfl) ⟨966750, by rfl⟩ : syracuseStep 2578001 = 1933501) B1933501
theorem B1717843 : Blo 1717059 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B2610785 : Blo 1717059 2610785 := bstep (se 2 (by rfl) ⟨979044, by rfl⟩ : syracuseStep 2610785 = 1958089) B1958089
theorem B1717859 : Blo 1717059 1717859 := bstep (se 1 (by rfl) ⟨1288394, by rfl⟩ : syracuseStep 1717859 = 2576789) B2576789
theorem B2578019 : Blo 1717059 2578019 := bstep (se 1 (by rfl) ⟨1933514, by rfl⟩ : syracuseStep 2578019 = 3867029) B3867029
theorem B1717875 : Blo 1717059 1717875 := bstep (se 1 (by rfl) ⟨1288406, by rfl⟩ : syracuseStep 1717875 = 2576813) B2576813
theorem B2578049 : Blo 1717059 2578049 := bstep (se 2 (by rfl) ⟨966768, by rfl⟩ : syracuseStep 2578049 = 1933537) B1933537
theorem B1717891 : Blo 1717059 1717891 := bstep (se 1 (by rfl) ⟨1288418, by rfl⟩ : syracuseStep 1717891 = 2576837) B2576837
theorem B1717907 : Blo 1717059 1717907 := bstep (se 1 (by rfl) ⟨1288430, by rfl⟩ : syracuseStep 1717907 = 2576861) B2576861
theorem B2578067 : Blo 1717059 2578067 := bstep (se 1 (by rfl) ⟨1933550, by rfl⟩ : syracuseStep 2578067 = 3867101) B3867101
theorem B1717923 : Blo 1717059 1717923 := bstep (se 1 (by rfl) ⟨1288442, by rfl⟩ : syracuseStep 1717923 = 2576885) B2576885
theorem B2578097 : Blo 1717059 2578097 := bstep (se 2 (by rfl) ⟨966786, by rfl⟩ : syracuseStep 2578097 = 1933573) B1933573
theorem B1717939 : Blo 1717059 1717939 := bstep (se 1 (by rfl) ⟨1288454, by rfl⟩ : syracuseStep 1717939 = 2576909) B2576909
theorem B1717955 : Blo 1717059 1717955 := bstep (se 1 (by rfl) ⟨1288466, by rfl⟩ : syracuseStep 1717955 = 2576933) B2576933
theorem B2578115 : Blo 1717059 2578115 := bstep (se 1 (by rfl) ⟨1933586, by rfl⟩ : syracuseStep 2578115 = 3867173) B3867173
theorem B1717971 : Blo 1717059 1717971 := bstep (se 1 (by rfl) ⟨1288478, by rfl⟩ : syracuseStep 1717971 = 2576957) B2576957
theorem B2897633 : Blo 1717059 2897633 := bstep (se 2 (by rfl) ⟨1086612, by rfl⟩ : syracuseStep 2897633 = 2173225) B2173225
theorem B1717987 : Blo 1717059 1717987 := bstep (se 1 (by rfl) ⟨1288490, by rfl⟩ : syracuseStep 1717987 = 2576981) B2576981
theorem B2578145 : Blo 1717059 2578145 := bstep (se 2 (by rfl) ⟨966804, by rfl⟩ : syracuseStep 2578145 = 1933609) B1933609
theorem B1718003 : Blo 1717059 1718003 := bstep (se 1 (by rfl) ⟨1288502, by rfl⟩ : syracuseStep 1718003 = 2577005) B2577005
theorem B2578163 : Blo 1717059 2578163 := bstep (se 1 (by rfl) ⟨1933622, by rfl⟩ : syracuseStep 2578163 = 3867245) B3867245
theorem B1718019 : Blo 1717059 1718019 := bstep (se 1 (by rfl) ⟨1288514, by rfl⟩ : syracuseStep 1718019 = 2577029) B2577029
theorem B4347665 : Blo 1717059 4347665 := bstep (se 2 (by rfl) ⟨1630374, by rfl⟩ : syracuseStep 4347665 = 3260749) B3260749
theorem B1718035 : Blo 1717059 1718035 := bstep (se 1 (by rfl) ⟨1288526, by rfl⟩ : syracuseStep 1718035 = 2577053) B2577053
theorem B2578193 : Blo 1717059 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B1718051 : Blo 1717059 1718051 := bstep (se 1 (by rfl) ⟨1288538, by rfl⟩ : syracuseStep 1718051 = 2577077) B2577077
theorem B2578211 : Blo 1717059 2578211 := bstep (se 1 (by rfl) ⟨1933658, by rfl⟩ : syracuseStep 2578211 = 3867317) B3867317
theorem B1718067 : Blo 1717059 1718067 := bstep (se 1 (by rfl) ⟨1288550, by rfl⟩ : syracuseStep 1718067 = 2577101) B2577101
theorem B2578241 : Blo 1717059 2578241 := bstep (se 2 (by rfl) ⟨966840, by rfl⟩ : syracuseStep 2578241 = 1933681) B1933681
theorem B4347715 : Blo 1717059 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B1718083 : Blo 1717059 1718083 := bstep (se 1 (by rfl) ⟨1288562, by rfl⟩ : syracuseStep 1718083 = 2577125) B2577125
theorem B5797709 : Blo 1717059 5797709 := bstep (se 3 (by rfl) ⟨1087070, by rfl⟩ : syracuseStep 5797709 = 2174141) B2174141
theorem B3864401 : Blo 1717059 3864401 := bstep (se 2 (by rfl) ⟨1449150, by rfl⟩ : syracuseStep 3864401 = 2898301) B2898301
theorem B2447185 : Blo 1717059 2447185 := bstep (se 2 (by rfl) ⟨917694, by rfl⟩ : syracuseStep 2447185 = 1835389) B1835389
theorem B1718099 : Blo 1717059 1718099 := bstep (se 1 (by rfl) ⟨1288574, by rfl⟩ : syracuseStep 1718099 = 2577149) B2577149
theorem B2578259 : Blo 1717059 2578259 := bstep (se 1 (by rfl) ⟨1933694, by rfl⟩ : syracuseStep 2578259 = 3867389) B3867389
theorem B2897761 : Blo 1717059 2897761 := bstep (se 2 (by rfl) ⟨1086660, by rfl⟩ : syracuseStep 2897761 = 2173321) B2173321
theorem B3864419 : Blo 1717059 3864419 := bstep (se 1 (by rfl) ⟨2898314, by rfl⟩ : syracuseStep 3864419 = 5796629) B5796629
theorem B1718115 : Blo 1717059 1718115 := bstep (se 1 (by rfl) ⟨1288586, by rfl⟩ : syracuseStep 1718115 = 2577173) B2577173
theorem B7255921 : Blo 1717059 7255921 := bstep (se 2 (by rfl) ⟨2720970, by rfl⟩ : syracuseStep 7255921 = 5441941) B5441941
theorem B2578289 : Blo 1717059 2578289 := bstep (se 2 (by rfl) ⟨966858, by rfl⟩ : syracuseStep 2578289 = 1933717) B1933717
theorem B1718131 : Blo 1717059 1718131 := bstep (se 1 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 1718131 = 2577197) B2577197
theorem B2447219 : Blo 1717059 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B2897795 : Blo 1717059 2897795 := bstep (se 1 (by rfl) ⟨2173346, by rfl⟩ : syracuseStep 2897795 = 4346693) B4346693
theorem B5797763 : Blo 1717059 5797763 := bstep (se 1 (by rfl) ⟨4348322, by rfl⟩ : syracuseStep 5797763 = 8696645) B8696645
theorem B1718147 : Blo 1717059 1718147 := bstep (se 1 (by rfl) ⟨1288610, by rfl⟩ : syracuseStep 1718147 = 2577221) B2577221
theorem B2578307 : Blo 1717059 2578307 := bstep (se 1 (by rfl) ⟨1933730, by rfl⟩ : syracuseStep 2578307 = 3867461) B3867461
theorem B2611091 : Blo 1717059 2611091 := bstep (se 1 (by rfl) ⟨1958318, by rfl⟩ : syracuseStep 2611091 = 3916637) B3916637
theorem B1718163 : Blo 1717059 1718163 := bstep (se 1 (by rfl) ⟨1288622, by rfl⟩ : syracuseStep 1718163 = 2577245) B2577245
theorem B2578337 : Blo 1717059 2578337 := bstep (se 2 (by rfl) ⟨966876, by rfl⟩ : syracuseStep 2578337 = 1933753) B1933753
theorem B1718179 : Blo 1717059 1718179 := bstep (se 1 (by rfl) ⟨1288634, by rfl⟩ : syracuseStep 1718179 = 2577269) B2577269
theorem B1718195 : Blo 1717059 1718195 := bstep (se 1 (by rfl) ⟨1288646, by rfl⟩ : syracuseStep 1718195 = 2577293) B2577293
theorem B2578355 : Blo 1717059 2578355 := bstep (se 1 (by rfl) ⟨1933766, by rfl⟩ : syracuseStep 2578355 = 3867533) B3867533
theorem B1718211 : Blo 1717059 1718211 := bstep (se 1 (by rfl) ⟨1288658, by rfl⟩ : syracuseStep 1718211 = 2577317) B2577317
theorem B18577349 : Blo 1717059 18577349 := bstep (se 4 (by rfl) ⟨1741626, by rfl⟩ : syracuseStep 18577349 = 3483253) B3483253
theorem B8370125 : Blo 1717059 8370125 := bstep (se 3 (by rfl) ⟨1569398, by rfl⟩ : syracuseStep 8370125 = 3138797) B3138797
theorem B4347857 : Blo 1717059 4347857 := bstep (se 2 (by rfl) ⟨1630446, by rfl⟩ : syracuseStep 4347857 = 3260893) B3260893
theorem B2578385 : Blo 1717059 2578385 := bstep (se 2 (by rfl) ⟨966894, by rfl⟩ : syracuseStep 2578385 = 1933789) B1933789
theorem B1718227 : Blo 1717059 1718227 := bstep (se 1 (by rfl) ⟨1288670, by rfl⟩ : syracuseStep 1718227 = 2577341) B2577341
theorem B1718243 : Blo 1717059 1718243 := bstep (se 1 (by rfl) ⟨1288682, by rfl⟩ : syracuseStep 1718243 = 2577365) B2577365
theorem B2578403 : Blo 1717059 2578403 := bstep (se 1 (by rfl) ⟨1933802, by rfl⟩ : syracuseStep 2578403 = 3867605) B3867605
theorem B1718259 : Blo 1717059 1718259 := bstep (se 1 (by rfl) ⟨1288694, by rfl⟩ : syracuseStep 1718259 = 2577389) B2577389
theorem B2578433 : Blo 1717059 2578433 := bstep (se 2 (by rfl) ⟨966912, by rfl⟩ : syracuseStep 2578433 = 1933825) B1933825
theorem B2897923 : Blo 1717059 2897923 := bstep (se 1 (by rfl) ⟨2173442, by rfl⟩ : syracuseStep 2897923 = 4346885) B4346885
theorem B1718275 : Blo 1717059 1718275 := bstep (se 1 (by rfl) ⟨1288706, by rfl⟩ : syracuseStep 1718275 = 2577413) B2577413
theorem B11761669 : Blo 1717059 11761669 := bstep (se 4 (by rfl) ⟨1102656, by rfl⟩ : syracuseStep 11761669 = 2205313) B2205313
theorem B13932557 : Blo 1717059 13932557 := bstep (se 3 (by rfl) ⟨2612354, by rfl⟩ : syracuseStep 13932557 = 5224709) B5224709
theorem B5879821 : Blo 1717059 5879821 := bstep (se 3 (by rfl) ⟨1102466, by rfl⟩ : syracuseStep 5879821 = 2204933) B2204933
theorem B1718291 : Blo 1717059 1718291 := bstep (se 1 (by rfl) ⟨1288718, by rfl⟩ : syracuseStep 1718291 = 2577437) B2577437
theorem B2578451 : Blo 1717059 2578451 := bstep (se 1 (by rfl) ⟨1933838, by rfl⟩ : syracuseStep 2578451 = 3867677) B3867677
theorem B1718307 : Blo 1717059 1718307 := bstep (se 1 (by rfl) ⟨1288730, by rfl⟩ : syracuseStep 1718307 = 2577461) B2577461
theorem B2578481 : Blo 1717059 2578481 := bstep (se 2 (by rfl) ⟨966930, by rfl⟩ : syracuseStep 2578481 = 1933861) B1933861
theorem B1718323 : Blo 1717059 1718323 := bstep (se 1 (by rfl) ⟨1288742, by rfl⟩ : syracuseStep 1718323 = 2577485) B2577485
theorem B1718339 : Blo 1717059 1718339 := bstep (se 1 (by rfl) ⟨1288754, by rfl⟩ : syracuseStep 1718339 = 2577509) B2577509
theorem B2578499 : Blo 1717059 2578499 := bstep (se 1 (by rfl) ⟨1933874, by rfl⟩ : syracuseStep 2578499 = 3867749) B3867749
theorem B1718355 : Blo 1717059 1718355 := bstep (se 1 (by rfl) ⟨1288766, by rfl⟩ : syracuseStep 1718355 = 2577533) B2577533
theorem B1718371 : Blo 1717059 1718371 := bstep (se 1 (by rfl) ⟨1288778, by rfl⟩ : syracuseStep 1718371 = 2577557) B2577557
theorem B2578529 : Blo 1717059 2578529 := bstep (se 2 (by rfl) ⟨966948, by rfl⟩ : syracuseStep 2578529 = 1933897) B1933897
theorem B3864689 : Blo 1717059 3864689 := bstep (se 2 (by rfl) ⟨1449258, by rfl⟩ : syracuseStep 3864689 = 2898517) B2898517
theorem B1718387 : Blo 1717059 1718387 := bstep (se 1 (by rfl) ⟨1288790, by rfl⟩ : syracuseStep 1718387 = 2577581) B2577581
theorem B2578547 : Blo 1717059 2578547 := bstep (se 1 (by rfl) ⟨1933910, by rfl⟩ : syracuseStep 2578547 = 3867821) B3867821
theorem B3864707 : Blo 1717059 3864707 := bstep (se 1 (by rfl) ⟨2898530, by rfl⟩ : syracuseStep 3864707 = 5797061) B5797061
theorem B1718403 : Blo 1717059 1718403 := bstep (se 1 (by rfl) ⟨1288802, by rfl⟩ : syracuseStep 1718403 = 2577605) B2577605
theorem B2898065 : Blo 1717059 2898065 := bstep (se 2 (by rfl) ⟨1086774, by rfl⟩ : syracuseStep 2898065 = 2173549) B2173549
theorem B5798033 : Blo 1717059 5798033 := bstep (se 2 (by rfl) ⟨2174262, by rfl⟩ : syracuseStep 5798033 = 4348525) B4348525
theorem B1718419 : Blo 1717059 1718419 := bstep (se 1 (by rfl) ⟨1288814, by rfl⟩ : syracuseStep 1718419 = 2577629) B2577629
theorem B2578577 : Blo 1717059 2578577 := bstep (se 2 (by rfl) ⟨966966, by rfl⟩ : syracuseStep 2578577 = 1933933) B1933933
theorem B1718435 : Blo 1717059 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B1718451 : Blo 1717059 1718451 := bstep (se 1 (by rfl) ⟨1288838, by rfl⟩ : syracuseStep 1718451 = 2577677) B2577677
theorem B1718467 : Blo 1717059 1718467 := bstep (se 1 (by rfl) ⟨1288850, by rfl⟩ : syracuseStep 1718467 = 2577701) B2577701
theorem B1718483 : Blo 1717059 1718483 := bstep (se 1 (by rfl) ⟨1288862, by rfl⟩ : syracuseStep 1718483 = 2577725) B2577725
theorem B1718499 : Blo 1717059 1718499 := bstep (se 1 (by rfl) ⟨1288874, by rfl⟩ : syracuseStep 1718499 = 2577749) B2577749
theorem B1718515 : Blo 1717059 1718515 := bstep (se 1 (by rfl) ⟨1288886, by rfl⟩ : syracuseStep 1718515 = 2577773) B2577773
theorem B1718531 : Blo 1717059 1718531 := bstep (se 1 (by rfl) ⟨1288898, by rfl⟩ : syracuseStep 1718531 = 2577797) B2577797
theorem B2898193 : Blo 1717059 2898193 := bstep (se 2 (by rfl) ⟨1086822, by rfl⟩ : syracuseStep 2898193 = 2173645) B2173645
theorem B1718547 : Blo 1717059 1718547 := bstep (se 1 (by rfl) ⟨1288910, by rfl⟩ : syracuseStep 1718547 = 2577821) B2577821
theorem B7338275 : Blo 1717059 7338275 := bstep (se 1 (by rfl) ⟨5503706, by rfl⟩ : syracuseStep 7338275 = 11007413) B11007413
theorem B1718563 : Blo 1717059 1718563 := bstep (se 1 (by rfl) ⟨1288922, by rfl⟩ : syracuseStep 1718563 = 2577845) B2577845
theorem B2898227 : Blo 1717059 2898227 := bstep (se 1 (by rfl) ⟨2173670, by rfl⟩ : syracuseStep 2898227 = 4347341) B4347341
theorem B1718579 : Blo 1717059 1718579 := bstep (se 1 (by rfl) ⟨1288934, by rfl⟩ : syracuseStep 1718579 = 2577869) B2577869
theorem B1718595 : Blo 1717059 1718595 := bstep (se 1 (by rfl) ⟨1288946, by rfl⟩ : syracuseStep 1718595 = 2577893) B2577893
theorem B1718611 : Blo 1717059 1718611 := bstep (se 1 (by rfl) ⟨1288958, by rfl⟩ : syracuseStep 1718611 = 2577917) B2577917
theorem B7059811 : Blo 1717059 7059811 := bstep (se 1 (by rfl) ⟨5294858, by rfl⟩ : syracuseStep 7059811 = 10589717) B10589717
theorem B23517539 : Blo 1717059 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B1718627 : Blo 1717059 1718627 := bstep (se 1 (by rfl) ⟨1288970, by rfl⟩ : syracuseStep 1718627 = 2577941) B2577941
theorem B1718643 : Blo 1717059 1718643 := bstep (se 1 (by rfl) ⟨1288982, by rfl⟩ : syracuseStep 1718643 = 2577965) B2577965
theorem B1718659 : Blo 1717059 1718659 := bstep (se 1 (by rfl) ⟨1288994, by rfl⟩ : syracuseStep 1718659 = 2577989) B2577989
theorem B5503373 : Blo 1717059 5503373 := bstep (se 3 (by rfl) ⟨1031882, by rfl⟩ : syracuseStep 5503373 = 2063765) B2063765
theorem B8821133 : Blo 1717059 8821133 := bstep (se 3 (by rfl) ⟨1653962, by rfl⟩ : syracuseStep 8821133 = 3307925) B3307925
theorem B3864977 : Blo 1717059 3864977 := bstep (se 2 (by rfl) ⟨1449366, by rfl⟩ : syracuseStep 3864977 = 2898733) B2898733
theorem B1718675 : Blo 1717059 1718675 := bstep (se 1 (by rfl) ⟨1289006, by rfl⟩ : syracuseStep 1718675 = 2578013) B2578013
theorem B3864995 : Blo 1717059 3864995 := bstep (se 1 (by rfl) ⟨2898746, by rfl⟩ : syracuseStep 3864995 = 5797493) B5797493
theorem B1718691 : Blo 1717059 1718691 := bstep (se 1 (by rfl) ⟨1289018, by rfl⟩ : syracuseStep 1718691 = 2578037) B2578037
theorem B2898355 : Blo 1717059 2898355 := bstep (se 1 (by rfl) ⟨2173766, by rfl⟩ : syracuseStep 2898355 = 4347533) B4347533
theorem B1718707 : Blo 1717059 1718707 := bstep (se 1 (by rfl) ⟨1289030, by rfl⟩ : syracuseStep 1718707 = 2578061) B2578061
theorem B2611649 : Blo 1717059 2611649 := bstep (se 2 (by rfl) ⟨979368, by rfl⟩ : syracuseStep 2611649 = 1958737) B1958737
theorem B3668419 : Blo 1717059 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B1718723 : Blo 1717059 1718723 := bstep (se 1 (by rfl) ⟨1289042, by rfl⟩ : syracuseStep 1718723 = 2578085) B2578085
theorem B1718739 : Blo 1717059 1718739 := bstep (se 1 (by rfl) ⟨1289054, by rfl⟩ : syracuseStep 1718739 = 2578109) B2578109
theorem B4127203 : Blo 1717059 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B1718755 : Blo 1717059 1718755 := bstep (se 1 (by rfl) ⟨1289066, by rfl⟩ : syracuseStep 1718755 = 2578133) B2578133
theorem B1718771 : Blo 1717059 1718771 := bstep (se 1 (by rfl) ⟨1289078, by rfl⟩ : syracuseStep 1718771 = 2578157) B2578157
theorem B1718787 : Blo 1717059 1718787 := bstep (se 1 (by rfl) ⟨1289090, by rfl⟩ : syracuseStep 1718787 = 2578181) B2578181
theorem B9779717 : Blo 1717059 9779717 := bstep (se 4 (by rfl) ⟨916848, by rfl⟩ : syracuseStep 9779717 = 1833697) B1833697
theorem B1718803 : Blo 1717059 1718803 := bstep (se 1 (by rfl) ⟨1289102, by rfl⟩ : syracuseStep 1718803 = 2578205) B2578205
theorem B1718819 : Blo 1717059 1718819 := bstep (se 1 (by rfl) ⟨1289114, by rfl⟩ : syracuseStep 1718819 = 2578229) B2578229
theorem B1931827 : Blo 1717059 1931827 := bstep (se 1 (by rfl) ⟨1448870, by rfl⟩ : syracuseStep 1931827 = 2897741) B2897741
theorem B1718835 : Blo 1717059 1718835 := bstep (se 1 (by rfl) ⟨1289126, by rfl⟩ : syracuseStep 1718835 = 2578253) B2578253
theorem B2898497 : Blo 1717059 2898497 := bstep (se 2 (by rfl) ⟨1086936, by rfl⟩ : syracuseStep 2898497 = 2173873) B2173873
theorem B1718851 : Blo 1717059 1718851 := bstep (se 1 (by rfl) ⟨1289138, by rfl⟩ : syracuseStep 1718851 = 2578277) B2578277
theorem B14678597 : Blo 1717059 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B2751059 : Blo 1717059 2751059 := bstep (se 1 (by rfl) ⟨2063294, by rfl⟩ : syracuseStep 2751059 = 4126589) B4126589
theorem B1718867 : Blo 1717059 1718867 := bstep (se 1 (by rfl) ⟨1289150, by rfl⟩ : syracuseStep 1718867 = 2578301) B2578301
theorem B1718883 : Blo 1717059 1718883 := bstep (se 1 (by rfl) ⟨1289162, by rfl⟩ : syracuseStep 1718883 = 2578325) B2578325
theorem B1718899 : Blo 1717059 1718899 := bstep (se 1 (by rfl) ⟨1289174, by rfl⟩ : syracuseStep 1718899 = 2578349) B2578349
theorem B1718915 : Blo 1717059 1718915 := bstep (se 1 (by rfl) ⟨1289186, by rfl⟩ : syracuseStep 1718915 = 2578373) B2578373
theorem B1718931 : Blo 1717059 1718931 := bstep (se 1 (by rfl) ⟨1289198, by rfl⟩ : syracuseStep 1718931 = 2578397) B2578397
theorem B2939555 : Blo 1717059 2939555 := bstep (se 1 (by rfl) ⟨2204666, by rfl⟩ : syracuseStep 2939555 = 4409333) B4409333
theorem B1718947 : Blo 1717059 1718947 := bstep (se 1 (by rfl) ⟨1289210, by rfl⟩ : syracuseStep 1718947 = 2578421) B2578421
theorem B5798573 : Blo 1717059 5798573 := bstep (se 3 (by rfl) ⟨1087232, by rfl⟩ : syracuseStep 5798573 = 2174465) B2174465
theorem B3865265 : Blo 1717059 3865265 := bstep (se 2 (by rfl) ⟨1449474, by rfl⟩ : syracuseStep 3865265 = 2898949) B2898949
theorem B1718963 : Blo 1717059 1718963 := bstep (se 1 (by rfl) ⟨1289222, by rfl⟩ : syracuseStep 1718963 = 2578445) B2578445
theorem B2898625 : Blo 1717059 2898625 := bstep (se 2 (by rfl) ⟨1086984, by rfl⟩ : syracuseStep 2898625 = 2173969) B2173969
theorem B1931971 : Blo 1717059 1931971 := bstep (se 1 (by rfl) ⟨1448978, by rfl⟩ : syracuseStep 1931971 = 2897957) B2897957
theorem B3865283 : Blo 1717059 3865283 := bstep (se 1 (by rfl) ⟨2898962, by rfl⟩ : syracuseStep 3865283 = 5797925) B5797925
theorem B1718979 : Blo 1717059 1718979 := bstep (se 1 (by rfl) ⟨1289234, by rfl⟩ : syracuseStep 1718979 = 2578469) B2578469
theorem B2751187 : Blo 1717059 2751187 := bstep (se 1 (by rfl) ⟨2063390, by rfl⟩ : syracuseStep 2751187 = 4126781) B4126781
theorem B1718995 : Blo 1717059 1718995 := bstep (se 1 (by rfl) ⟨1289246, by rfl⟩ : syracuseStep 1718995 = 2578493) B2578493
theorem B2898659 : Blo 1717059 2898659 := bstep (se 1 (by rfl) ⟨2173994, by rfl⟩ : syracuseStep 2898659 = 4347989) B4347989
theorem B5798627 : Blo 1717059 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1719011 : Blo 1717059 1719011 := bstep (se 1 (by rfl) ⟨1289258, by rfl⟩ : syracuseStep 1719011 = 2578517) B2578517
theorem B1719027 : Blo 1717059 1719027 := bstep (se 1 (by rfl) ⟨1289270, by rfl⟩ : syracuseStep 1719027 = 2578541) B2578541
theorem B1719043 : Blo 1717059 1719043 := bstep (se 1 (by rfl) ⟨1289282, by rfl⟩ : syracuseStep 1719043 = 2578565) B2578565
theorem B3668753 : Blo 1717059 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1719059 : Blo 1717059 1719059 := bstep (se 1 (by rfl) ⟨1289294, by rfl⟩ : syracuseStep 1719059 = 2578589) B2578589
theorem B6519629 : Blo 1717059 6519629 := bstep (se 3 (by rfl) ⟨1222430, by rfl⟩ : syracuseStep 6519629 = 2444861) B2444861
theorem B1932115 : Blo 1717059 1932115 := bstep (se 1 (by rfl) ⟨1449086, by rfl⟩ : syracuseStep 1932115 = 2898173) B2898173
theorem B8813411 : Blo 1717059 8813411 := bstep (se 1 (by rfl) ⟨6610058, by rfl⟩ : syracuseStep 8813411 = 13220117) B13220117
theorem B2898787 : Blo 1717059 2898787 := bstep (se 1 (by rfl) ⟨2174090, by rfl⟩ : syracuseStep 2898787 = 4348181) B4348181
theorem B2939761 : Blo 1717059 2939761 := bstep (se 2 (by rfl) ⟨1102410, by rfl⟩ : syracuseStep 2939761 = 2204821) B2204821
theorem B4348849 : Blo 1717059 4348849 := bstep (se 2 (by rfl) ⟨1630818, by rfl⟩ : syracuseStep 4348849 = 3261637) B3261637
theorem B31783877 : Blo 1717059 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B9780173 : Blo 1717059 9780173 := bstep (se 3 (by rfl) ⟨1833782, by rfl⟩ : syracuseStep 9780173 = 3667565) B3667565
theorem B3865553 : Blo 1717059 3865553 := bstep (se 2 (by rfl) ⟨1449582, by rfl⟩ : syracuseStep 3865553 = 2899165) B2899165
theorem B1932259 : Blo 1717059 1932259 := bstep (se 1 (by rfl) ⟨1449194, by rfl⟩ : syracuseStep 1932259 = 2898389) B2898389
theorem B3865571 : Blo 1717059 3865571 := bstep (se 1 (by rfl) ⟨2899178, by rfl⟩ : syracuseStep 3865571 = 5798357) B5798357
theorem B2898929 : Blo 1717059 2898929 := bstep (se 2 (by rfl) ⟨1087098, by rfl⟩ : syracuseStep 2898929 = 2174197) B2174197
theorem B5798897 : Blo 1717059 5798897 := bstep (se 2 (by rfl) ⟨2174586, by rfl⟩ : syracuseStep 5798897 = 4349173) B4349173
theorem B9788465 : Blo 1717059 9788465 := bstep (se 2 (by rfl) ⟨3670674, by rfl⟩ : syracuseStep 9788465 = 7341349) B7341349
theorem B2513971 : Blo 1717059 2513971 := bstep (se 1 (by rfl) ⟨1885478, by rfl⟩ : syracuseStep 2513971 = 3770957) B3770957
theorem B2751571 : Blo 1717059 2751571 := bstep (se 1 (by rfl) ⟨2063678, by rfl⟩ : syracuseStep 2751571 = 4127357) B4127357
theorem B2899057 : Blo 1717059 2899057 := bstep (se 2 (by rfl) ⟨1087146, by rfl⟩ : syracuseStep 2899057 = 2174293) B2174293
theorem B1932403 : Blo 1717059 1932403 := bstep (se 1 (by rfl) ⟨1449302, by rfl⟩ : syracuseStep 1932403 = 2898605) B2898605
theorem B2899091 : Blo 1717059 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B20118709 : Blo 1717059 20118709 := bstep (se 5 (by rfl) ⟨943064, by rfl⟩ : syracuseStep 20118709 = 1886129) B1886129
theorem B4349123 : Blo 1717059 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B13040837 : Blo 1717059 13040837 := bstep (se 4 (by rfl) ⟨1222578, by rfl⟩ : syracuseStep 13040837 = 2445157) B2445157
theorem B3865841 : Blo 1717059 3865841 := bstep (se 2 (by rfl) ⟨1449690, by rfl⟩ : syracuseStep 3865841 = 2899381) B2899381
theorem B1932547 : Blo 1717059 1932547 := bstep (se 1 (by rfl) ⟨1449410, by rfl⟩ : syracuseStep 1932547 = 2898821) B2898821
theorem B3865859 : Blo 1717059 3865859 := bstep (se 1 (by rfl) ⟨2899394, by rfl⟩ : syracuseStep 3865859 = 5798789) B5798789
theorem B5504269 : Blo 1717059 5504269 := bstep (se 3 (by rfl) ⟨1032050, by rfl⟩ : syracuseStep 5504269 = 2064101) B2064101
theorem B2899219 : Blo 1717059 2899219 := bstep (se 1 (by rfl) ⟨2174414, by rfl⟩ : syracuseStep 2899219 = 4348829) B4348829
theorem B4644163 : Blo 1717059 4644163 := bstep (se 1 (by rfl) ⟨3483122, by rfl⟩ : syracuseStep 4644163 = 6966245) B6966245
theorem B2751827 : Blo 1717059 2751827 := bstep (se 1 (by rfl) ⟨2063870, by rfl⟩ : syracuseStep 2751827 = 4127741) B4127741
theorem B4349315 : Blo 1717059 4349315 := bstep (se 1 (by rfl) ⟨3261986, by rfl⟩ : syracuseStep 4349315 = 6523973) B6523973
theorem B1932691 : Blo 1717059 1932691 := bstep (se 1 (by rfl) ⟨1449518, by rfl⟩ : syracuseStep 1932691 = 2899037) B2899037
theorem B2899361 : Blo 1717059 2899361 := bstep (se 2 (by rfl) ⟨1087260, by rfl⟩ : syracuseStep 2899361 = 2174521) B2174521
theorem B5799437 : Blo 1717059 5799437 := bstep (se 3 (by rfl) ⟨1087394, by rfl⟩ : syracuseStep 5799437 = 2174789) B2174789
theorem B3259921 : Blo 1717059 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B3866129 : Blo 1717059 3866129 := bstep (se 2 (by rfl) ⟨1449798, by rfl⟩ : syracuseStep 3866129 = 2899597) B2899597
theorem B2899489 : Blo 1717059 2899489 := bstep (se 2 (by rfl) ⟨1087308, by rfl⟩ : syracuseStep 2899489 = 2174617) B2174617
theorem B1932835 : Blo 1717059 1932835 := bstep (se 1 (by rfl) ⟨1449626, by rfl⟩ : syracuseStep 1932835 = 2899253) B2899253
theorem B3866147 : Blo 1717059 3866147 := bstep (se 1 (by rfl) ⟨2899610, by rfl⟩ : syracuseStep 3866147 = 5799221) B5799221
theorem B2899523 : Blo 1717059 2899523 := bstep (se 1 (by rfl) ⟨2174642, by rfl⟩ : syracuseStep 2899523 = 4349285) B4349285
theorem B5799491 : Blo 1717059 5799491 := bstep (se 1 (by rfl) ⟨4349618, by rfl⟩ : syracuseStep 5799491 = 8699237) B8699237
theorem B3260081 : Blo 1717059 3260081 := bstep (se 2 (by rfl) ⟨1222530, by rfl⟩ : syracuseStep 3260081 = 2445061) B2445061
theorem B1932979 : Blo 1717059 1932979 := bstep (se 1 (by rfl) ⟨1449734, by rfl⟩ : syracuseStep 1932979 = 2899469) B2899469
theorem B2612915 : Blo 1717059 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B2899651 : Blo 1717059 2899651 := bstep (se 1 (by rfl) ⟨2174738, by rfl⟩ : syracuseStep 2899651 = 4349477) B4349477
theorem B6192881 : Blo 1717059 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B13049585 : Blo 1717059 13049585 := bstep (se 2 (by rfl) ⟨4893594, by rfl⟩ : syracuseStep 13049585 = 9787189) B9787189
theorem B2752289 : Blo 1717059 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B3866417 : Blo 1717059 3866417 := bstep (se 2 (by rfl) ⟨1449906, by rfl⟩ : syracuseStep 3866417 = 2899813) B2899813
theorem B1933123 : Blo 1717059 1933123 := bstep (se 1 (by rfl) ⟨1449842, by rfl⟩ : syracuseStep 1933123 = 2899685) B2899685
theorem B3866435 : Blo 1717059 3866435 := bstep (se 1 (by rfl) ⟨2899826, by rfl⟩ : syracuseStep 3866435 = 5799653) B5799653
theorem B2899793 : Blo 1717059 2899793 := bstep (se 2 (by rfl) ⟨1087422, by rfl⟩ : syracuseStep 2899793 = 2174845) B2174845
theorem B5799761 : Blo 1717059 5799761 := bstep (se 2 (by rfl) ⟨2174910, by rfl⟩ : syracuseStep 5799761 = 4349821) B4349821
theorem B2752385 : Blo 1717059 2752385 := bstep (se 2 (by rfl) ⟨1032144, by rfl⟩ : syracuseStep 2752385 = 2064289) B2064289
theorem B16744333 : Blo 1717059 16744333 := bstep (se 3 (by rfl) ⟨3139562, by rfl⟩ : syracuseStep 16744333 = 6279125) B6279125
theorem B2752417 : Blo 1717059 2752417 := bstep (se 2 (by rfl) ⟨1032156, by rfl⟩ : syracuseStep 2752417 = 2064313) B2064313
theorem B3669923 : Blo 1717059 3669923 := bstep (se 1 (by rfl) ⟨2752442, by rfl⟩ : syracuseStep 3669923 = 5504885) B5504885
theorem B4890577 : Blo 1717059 4890577 := bstep (se 2 (by rfl) ⟨1833966, by rfl⟩ : syracuseStep 4890577 = 3667933) B3667933
theorem B2899921 : Blo 1717059 2899921 := bstep (se 2 (by rfl) ⟨1087470, by rfl⟩ : syracuseStep 2899921 = 2174941) B2174941
theorem B1933267 : Blo 1717059 1933267 := bstep (se 1 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 1933267 = 2899901) B2899901
theorem B7340017 : Blo 1717059 7340017 := bstep (se 2 (by rfl) ⟨2752506, by rfl⟩ : syracuseStep 7340017 = 5505013) B5505013
theorem B2899955 : Blo 1717059 2899955 := bstep (se 1 (by rfl) ⟨2174966, by rfl⟩ : syracuseStep 2899955 = 4349933) B4349933
theorem B6193169 : Blo 1717059 6193169 := bstep (se 2 (by rfl) ⟨2322438, by rfl⟩ : syracuseStep 6193169 = 4644877) B4644877
theorem B7839761 : Blo 1717059 7839761 := bstep (se 2 (by rfl) ⟨2939910, by rfl⟩ : syracuseStep 7839761 = 5879821) B5879821
theorem B5505089 : Blo 1717059 5505089 := bstep (se 2 (by rfl) ⟨2064408, by rfl⟩ : syracuseStep 5505089 = 4128817) B4128817
theorem B24756293 : Blo 1717059 24756293 := bstep (se 4 (by rfl) ⟨2320902, by rfl⟩ : syracuseStep 24756293 = 4641805) B4641805
theorem B13246615 : Blo 1717059 13246615 := bstep (se 1 (by rfl) ⟨9934961, by rfl⟩ : syracuseStep 13246615 = 19869923) B19869923
theorem B3260567 : Blo 1717059 3260567 := bstep (se 1 (by rfl) ⟨2445425, by rfl⟩ : syracuseStep 3260567 = 4890851) B4890851
theorem B3866777 : Blo 1717059 3866777 := bstep (se 2 (by rfl) ⟨1450041, by rfl⟩ : syracuseStep 3866777 = 2900083) B2900083
theorem B1933483 : Blo 1717059 1933483 := bstep (se 1 (by rfl) ⟨1450112, by rfl⟩ : syracuseStep 1933483 = 2900225) B2900225
theorem B4350145 : Blo 1717059 4350145 := bstep (se 2 (by rfl) ⟨1631304, by rfl⟩ : syracuseStep 4350145 = 3262609) B3262609
theorem B5800139 : Blo 1717059 5800139 := bstep (se 1 (by rfl) ⟨4350104, by rfl⟩ : syracuseStep 5800139 = 8700209) B8700209
theorem B2900171 : Blo 1717059 2900171 := bstep (se 1 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 2900171 = 4350257) B4350257
theorem B3670231 : Blo 1717059 3670231 := bstep (se 1 (by rfl) ⟨2752673, by rfl⟩ : syracuseStep 3670231 = 5505347) B5505347
theorem B3866867 : Blo 1717059 3866867 := bstep (se 1 (by rfl) ⟨2900150, by rfl⟩ : syracuseStep 3866867 = 5800301) B5800301
theorem B7340291 : Blo 1717059 7340291 := bstep (se 1 (by rfl) ⟨5505218, by rfl⟩ : syracuseStep 7340291 = 11010437) B11010437
theorem B3866903 : Blo 1717059 3866903 := bstep (se 1 (by rfl) ⟨2900177, by rfl⟩ : syracuseStep 3866903 = 5800355) B5800355
theorem B1933591 : Blo 1717059 1933591 := bstep (se 1 (by rfl) ⟨1450193, by rfl⟩ : syracuseStep 1933591 = 2900387) B2900387
theorem B3481931 : Blo 1717059 3481931 := bstep (se 1 (by rfl) ⟨2611448, by rfl⟩ : syracuseStep 3481931 = 5222897) B5222897
theorem B2900299 : Blo 1717059 2900299 := bstep (se 1 (by rfl) ⟨2175224, by rfl⟩ : syracuseStep 2900299 = 4350449) B4350449
theorem B3867083 : Blo 1717059 3867083 := bstep (se 1 (by rfl) ⟨2900312, by rfl⟩ : syracuseStep 3867083 = 5800625) B5800625
theorem B1933771 : Blo 1717059 1933771 := bstep (se 1 (by rfl) ⟨1450328, by rfl⟩ : syracuseStep 1933771 = 2900657) B2900657
theorem B9413081 : Blo 1717059 9413081 := bstep (se 2 (by rfl) ⟨3529905, by rfl⟩ : syracuseStep 9413081 = 7059811) B7059811
theorem B5800409 : Blo 1717059 5800409 := bstep (se 2 (by rfl) ⟨2175153, by rfl⟩ : syracuseStep 5800409 = 4350307) B4350307
theorem B2900441 : Blo 1717059 2900441 := bstep (se 2 (by rfl) ⟨1087665, by rfl⟩ : syracuseStep 2900441 = 2175331) B2175331
theorem B3097075 : Blo 1717059 3097075 := bstep (se 1 (by rfl) ⟨2322806, by rfl⟩ : syracuseStep 3097075 = 4645613) B4645613
theorem B3867137 : Blo 1717059 3867137 := bstep (se 2 (by rfl) ⟨1450176, by rfl⟩ : syracuseStep 3867137 = 2900353) B2900353
theorem B6193687 : Blo 1717059 6193687 := bstep (se 1 (by rfl) ⟨4645265, by rfl⟩ : syracuseStep 6193687 = 9290531) B9290531
theorem B1958455 : Blo 1717059 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B1933879 : Blo 1717059 1933879 := bstep (se 1 (by rfl) ⟨1450409, by rfl⟩ : syracuseStep 1933879 = 2900819) B2900819
theorem B13926977 : Blo 1717059 13926977 := bstep (se 2 (by rfl) ⟨5222616, by rfl⟩ : syracuseStep 13926977 = 10445233) B10445233
theorem B2900569 : Blo 1717059 2900569 := bstep (se 2 (by rfl) ⟨1087713, by rfl⟩ : syracuseStep 2900569 = 2175427) B2175427
theorem B7537283 : Blo 1717059 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B3670667 : Blo 1717059 3670667 := bstep (se 1 (by rfl) ⟨2753000, by rfl⟩ : syracuseStep 3670667 = 5506001) B5506001
theorem B3867353 : Blo 1717059 3867353 := bstep (se 2 (by rfl) ⟨1450257, by rfl⟩ : syracuseStep 3867353 = 2900515) B2900515
theorem B9290513 : Blo 1717059 9290513 := bstep (se 2 (by rfl) ⟨3483942, by rfl⟩ : syracuseStep 9290513 = 6967885) B6967885
theorem B4350743 : Blo 1717059 4350743 := bstep (se 1 (by rfl) ⟨3263057, by rfl⟩ : syracuseStep 4350743 = 6526115) B6526115
theorem B3261235 : Blo 1717059 3261235 := bstep (se 1 (by rfl) ⟨2445926, by rfl⟩ : syracuseStep 3261235 = 4891853) B4891853
theorem B3867443 : Blo 1717059 3867443 := bstep (se 1 (by rfl) ⟨2900582, by rfl⟩ : syracuseStep 3867443 = 5801165) B5801165
theorem B3867479 : Blo 1717059 3867479 := bstep (se 1 (by rfl) ⟨2900609, by rfl⟩ : syracuseStep 3867479 = 5801219) B5801219
theorem B19563443 : Blo 1717059 19563443 := bstep (se 1 (by rfl) ⟨14672582, by rfl⟩ : syracuseStep 19563443 = 29345165) B29345165
theorem B3867659 : Blo 1717059 3867659 := bstep (se 1 (by rfl) ⟨2900744, by rfl⟩ : syracuseStep 3867659 = 5801489) B5801489
theorem B3097651 : Blo 1717059 3097651 := bstep (se 1 (by rfl) ⟨2323238, by rfl⟩ : syracuseStep 3097651 = 4646477) B4646477
theorem B3867713 : Blo 1717059 3867713 := bstep (se 2 (by rfl) ⟨1450392, by rfl⟩ : syracuseStep 3867713 = 2900785) B2900785
theorem B13042781 : Blo 1717059 13042781 := bstep (se 3 (by rfl) ⟨2445521, by rfl⟩ : syracuseStep 13042781 = 4891043) B4891043
theorem B5801111 : Blo 1717059 5801111 := bstep (se 1 (by rfl) ⟨4350833, by rfl⟩ : syracuseStep 5801111 = 8701667) B8701667
theorem B6522029 : Blo 1717059 6522029 := bstep (se 3 (by rfl) ⟨1222880, by rfl⟩ : syracuseStep 6522029 = 2445761) B2445761
theorem B6522059 : Blo 1717059 6522059 := bstep (se 1 (by rfl) ⟨4891544, by rfl⟩ : syracuseStep 6522059 = 9783089) B9783089
theorem B3261683 : Blo 1717059 3261683 := bstep (se 1 (by rfl) ⟨2446262, by rfl⟩ : syracuseStep 3261683 = 4892525) B4892525
theorem B3261721 : Blo 1717059 3261721 := bstep (se 2 (by rfl) ⟨1223145, by rfl⟩ : syracuseStep 3261721 = 2446291) B2446291
theorem B5580083 : Blo 1717059 5580083 := bstep (se 1 (by rfl) ⟨4185062, by rfl⟩ : syracuseStep 5580083 = 8370125) B8370125
theorem B4892183 : Blo 1717059 4892183 := bstep (se 1 (by rfl) ⟨3669137, by rfl⟩ : syracuseStep 4892183 = 7338275) B7338275
theorem B14673473 : Blo 1717059 14673473 := bstep (se 2 (by rfl) ⟨5502552, by rfl⟩ : syracuseStep 14673473 = 11005105) B11005105
theorem B8701505 : Blo 1717059 8701505 := bstep (se 2 (by rfl) ⟨3263064, by rfl⟩ : syracuseStep 8701505 = 6526129) B6526129
theorem B5801651 : Blo 1717059 5801651 := bstep (se 1 (by rfl) ⟨4351238, by rfl⟩ : syracuseStep 5801651 = 8702477) B8702477
theorem B3262169 : Blo 1717059 3262169 := bstep (se 2 (by rfl) ⟨1223313, by rfl⟩ : syracuseStep 3262169 = 2446627) B2446627
theorem B8259403 : Blo 1717059 8259403 := bstep (se 1 (by rfl) ⟨6194552, by rfl⟩ : syracuseStep 8259403 = 12389105) B12389105
theorem B6522713 : Blo 1717059 6522713 := bstep (se 2 (by rfl) ⟨2446017, by rfl⟩ : syracuseStep 6522713 = 4892035) B4892035
theorem B5875607 : Blo 1717059 5875607 := bstep (se 1 (by rfl) ⟨4406705, by rfl⟩ : syracuseStep 5875607 = 8813411) B8813411
theorem B7833523 : Blo 1717059 7833523 := bstep (se 1 (by rfl) ⟨5875142, by rfl⟩ : syracuseStep 7833523 = 11750285) B11750285
theorem B6195217 : Blo 1717059 6195217 := bstep (se 2 (by rfl) ⟨2323206, by rfl⟩ : syracuseStep 6195217 = 4646413) B4646413
theorem B9783341 : Blo 1717059 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B16517195 : Blo 1717059 16517195 := bstep (se 1 (by rfl) ⟨12387896, by rfl⟩ : syracuseStep 16517195 = 24775793) B24775793
theorem B8693891 : Blo 1717059 8693891 := bstep (se 1 (by rfl) ⟨6520418, by rfl⟩ : syracuseStep 8693891 = 13040837) B13040837
theorem B6523031 : Blo 1717059 6523031 := bstep (se 1 (by rfl) ⟨4892273, by rfl⟩ : syracuseStep 6523031 = 9784547) B9784547
theorem B7833779 : Blo 1717059 7833779 := bstep (se 1 (by rfl) ⟨5875334, by rfl⟩ : syracuseStep 7833779 = 11750669) B11750669
theorem B6195521 : Blo 1717059 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B19564901 : Blo 1717059 19564901 := bstep (se 4 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 19564901 = 3668419) B3668419
theorem B8260019 : Blo 1717059 8260019 := bstep (se 1 (by rfl) ⟨6195014, by rfl⟩ : syracuseStep 8260019 = 12390029) B12390029
theorem B3262913 : Blo 1717059 3262913 := bstep (se 2 (by rfl) ⟨1223592, by rfl⟩ : syracuseStep 3262913 = 2447185) B2447185
theorem B2173387 : Blo 1717059 2173387 := bstep (se 1 (by rfl) ⟨1630040, by rfl⟩ : syracuseStep 2173387 = 3260081) B3260081
theorem B13224397 : Blo 1717059 13224397 := bstep (se 3 (by rfl) ⟨2479574, by rfl⟩ : syracuseStep 13224397 = 4959149) B4959149
theorem B22325777 : Blo 1717059 22325777 := bstep (se 2 (by rfl) ⟨8372166, by rfl⟩ : syracuseStep 22325777 = 16744333) B16744333
theorem B62728901 : Blo 1717059 62728901 := bstep (se 4 (by rfl) ⟨5880834, by rfl⟩ : syracuseStep 62728901 = 11761669) B11761669
theorem B3263179 : Blo 1717059 3263179 := bstep (se 1 (by rfl) ⟨2447384, by rfl⟩ : syracuseStep 3263179 = 4894769) B4894769
theorem B2173655 : Blo 1717059 2173655 := bstep (se 1 (by rfl) ⟨1630241, by rfl⟩ : syracuseStep 2173655 = 3260483) B3260483
theorem B6523699 : Blo 1717059 6523699 := bstep (se 1 (by rfl) ⟨4892774, by rfl⟩ : syracuseStep 6523699 = 9785549) B9785549
theorem B57256769 : Blo 1717059 57256769 := bstep (se 2 (by rfl) ⟨21471288, by rfl⟩ : syracuseStep 57256769 = 42942577) B42942577
theorem B1933303 : Blo 1717059 1933303 := bstep (se 1 (by rfl) ⟨1449977, by rfl⟩ : syracuseStep 1933303 = 2899955) B2899955
theorem B29371409 : Blo 1717059 29371409 := bstep (se 2 (by rfl) ⟨11014278, by rfl⟩ : syracuseStep 29371409 = 22028557) B22028557
theorem B2575691 : Blo 1717059 2575691 := bstep (se 1 (by rfl) ⟨1931768, by rfl⟩ : syracuseStep 2575691 = 3863537) B3863537
theorem B2575703 : Blo 1717059 2575703 := bstep (se 1 (by rfl) ⟨1931777, by rfl⟩ : syracuseStep 2575703 = 3863555) B3863555
theorem B7335319 : Blo 1717059 7335319 := bstep (se 1 (by rfl) ⟨5501489, by rfl⟩ : syracuseStep 7335319 = 11002979) B11002979
theorem B2174359 : Blo 1717059 2174359 := bstep (se 1 (by rfl) ⟨1630769, by rfl⟩ : syracuseStep 2174359 = 3261539) B3261539
theorem B2575769 : Blo 1717059 2575769 := bstep (se 2 (by rfl) ⟨965913, by rfl⟩ : syracuseStep 2575769 = 1931827) B1931827
theorem B2575883 : Blo 1717059 2575883 := bstep (se 1 (by rfl) ⟨1931912, by rfl⟩ : syracuseStep 2575883 = 3863825) B3863825
theorem B2575895 : Blo 1717059 2575895 := bstep (se 1 (by rfl) ⟨1931921, by rfl⟩ : syracuseStep 2575895 = 3863843) B3863843
theorem B1764887 : Blo 1717059 1764887 := bstep (se 1 (by rfl) ⟨1323665, by rfl⟩ : syracuseStep 1764887 = 2647331) B2647331
theorem B2575961 : Blo 1717059 2575961 := bstep (se 2 (by rfl) ⟨965985, by rfl⟩ : syracuseStep 2575961 = 1931971) B1931971
theorem B2576075 : Blo 1717059 2576075 := bstep (se 1 (by rfl) ⟨1932056, by rfl⟩ : syracuseStep 2576075 = 3864113) B3864113
theorem B2576087 : Blo 1717059 2576087 := bstep (se 1 (by rfl) ⟨1932065, by rfl⟩ : syracuseStep 2576087 = 3864131) B3864131
theorem B5795549 : Blo 1717059 5795549 := bstep (se 3 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 5795549 = 2173331) B2173331
theorem B2576153 : Blo 1717059 2576153 := bstep (se 2 (by rfl) ⟨966057, by rfl⟩ : syracuseStep 2576153 = 1932115) B1932115
theorem B3919681 : Blo 1717059 3919681 := bstep (se 2 (by rfl) ⟨1469880, by rfl⟩ : syracuseStep 3919681 = 2939761) B2939761
theorem B2576267 : Blo 1717059 2576267 := bstep (se 1 (by rfl) ⟨1932200, by rfl⟩ : syracuseStep 2576267 = 3864401) B3864401
theorem B2576279 : Blo 1717059 2576279 := bstep (se 1 (by rfl) ⟨1932209, by rfl⟩ : syracuseStep 2576279 = 3864419) B3864419
theorem B14675863 : Blo 1717059 14675863 := bstep (se 1 (by rfl) ⟨11006897, by rfl⟩ : syracuseStep 14675863 = 22013795) B22013795
theorem B15667121 : Blo 1717059 15667121 := bstep (se 2 (by rfl) ⟨5875170, by rfl⟩ : syracuseStep 15667121 = 11750341) B11750341
theorem B7942067 : Blo 1717059 7942067 := bstep (se 1 (by rfl) ⟨5956550, by rfl⟩ : syracuseStep 7942067 = 11913101) B11913101
theorem B4894643 : Blo 1717059 4894643 := bstep (se 1 (by rfl) ⟨3670982, by rfl⟩ : syracuseStep 4894643 = 7341965) B7341965
theorem B1740727 : Blo 1717059 1740727 := bstep (se 1 (by rfl) ⟨1305545, by rfl⟩ : syracuseStep 1740727 = 2611091) B2611091
theorem B2576345 : Blo 1717059 2576345 := bstep (se 2 (by rfl) ⟨966129, by rfl⟩ : syracuseStep 2576345 = 1932259) B1932259
theorem B6524945 : Blo 1717059 6524945 := bstep (se 2 (by rfl) ⟨2446854, by rfl⟩ : syracuseStep 6524945 = 4893709) B4893709
theorem B2576459 : Blo 1717059 2576459 := bstep (se 1 (by rfl) ⟨1932344, by rfl⟩ : syracuseStep 2576459 = 3864689) B3864689
theorem B2576471 : Blo 1717059 2576471 := bstep (se 1 (by rfl) ⟨1932353, by rfl⟩ : syracuseStep 2576471 = 3864707) B3864707
theorem B2576537 : Blo 1717059 2576537 := bstep (se 2 (by rfl) ⟨966201, by rfl⟩ : syracuseStep 2576537 = 1932403) B1932403
theorem B26824945 : Blo 1717059 26824945 := bstep (se 2 (by rfl) ⟨10059354, by rfl⟩ : syracuseStep 26824945 = 20118709) B20118709
theorem B2576651 : Blo 1717059 2576651 := bstep (se 1 (by rfl) ⟨1932488, by rfl⟩ : syracuseStep 2576651 = 3864977) B3864977
theorem B2576663 : Blo 1717059 2576663 := bstep (se 1 (by rfl) ⟨1932497, by rfl⟩ : syracuseStep 2576663 = 3864995) B3864995
theorem B1741099 : Blo 1717059 1741099 := bstep (se 1 (by rfl) ⟨1305824, by rfl⟩ : syracuseStep 1741099 = 2611649) B2611649
theorem B2576729 : Blo 1717059 2576729 := bstep (se 2 (by rfl) ⟨966273, by rfl⟩ : syracuseStep 2576729 = 1932547) B1932547
theorem B9785731 : Blo 1717059 9785731 := bstep (se 1 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 9785731 = 14678597) B14678597
theorem B11006387 : Blo 1717059 11006387 := bstep (se 1 (by rfl) ⟨8254790, by rfl⟩ : syracuseStep 11006387 = 16509581) B16509581
theorem B2576843 : Blo 1717059 2576843 := bstep (se 1 (by rfl) ⟨1932632, by rfl⟩ : syracuseStep 2576843 = 3865265) B3865265
theorem B2576855 : Blo 1717059 2576855 := bstep (se 1 (by rfl) ⟨1932641, by rfl⟩ : syracuseStep 2576855 = 3865283) B3865283
theorem B2576921 : Blo 1717059 2576921 := bstep (se 2 (by rfl) ⟨966345, by rfl⟩ : syracuseStep 2576921 = 1932691) B1932691
theorem B4346419 : Blo 1717059 4346419 := bstep (se 1 (by rfl) ⟨3259814, by rfl⟩ : syracuseStep 4346419 = 6519629) B6519629
theorem B21189251 : Blo 1717059 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B2577035 : Blo 1717059 2577035 := bstep (se 1 (by rfl) ⟨1932776, by rfl⟩ : syracuseStep 2577035 = 3865553) B3865553
theorem B2577047 : Blo 1717059 2577047 := bstep (se 1 (by rfl) ⟨1932785, by rfl⟩ : syracuseStep 2577047 = 3865571) B3865571
theorem B4346561 : Blo 1717059 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B6525643 : Blo 1717059 6525643 := bstep (se 1 (by rfl) ⟨4894232, by rfl⟩ : syracuseStep 6525643 = 9788465) B9788465
theorem B2577113 : Blo 1717059 2577113 := bstep (se 2 (by rfl) ⟨966417, by rfl⟩ : syracuseStep 2577113 = 1932835) B1932835
theorem B1717067 : Blo 1717059 1717067 := bstep (se 1 (by rfl) ⟨1287800, by rfl⟩ : syracuseStep 1717067 = 2575601) B2575601
theorem B5796683 : Blo 1717059 5796683 := bstep (se 1 (by rfl) ⟨4347512, by rfl⟩ : syracuseStep 5796683 = 8695025) B8695025
theorem B2978635 : Blo 1717059 2978635 := bstep (se 1 (by rfl) ⟨2233976, by rfl⟩ : syracuseStep 2978635 = 4467953) B4467953
theorem B2577227 : Blo 1717059 2577227 := bstep (se 1 (by rfl) ⟨1932920, by rfl⟩ : syracuseStep 2577227 = 3865841) B3865841
theorem B1717079 : Blo 1717059 1717079 := bstep (se 1 (by rfl) ⟨1287809, by rfl⟩ : syracuseStep 1717079 = 2575619) B2575619
theorem B2577239 : Blo 1717059 2577239 := bstep (se 1 (by rfl) ⟨1932929, by rfl⟩ : syracuseStep 2577239 = 3865859) B3865859
theorem B1717099 : Blo 1717059 1717099 := bstep (se 1 (by rfl) ⟨1287824, by rfl⟩ : syracuseStep 1717099 = 2575649) B2575649
theorem B3863411 : Blo 1717059 3863411 := bstep (se 1 (by rfl) ⟨2897558, by rfl⟩ : syracuseStep 3863411 = 5795117) B5795117
theorem B1717111 : Blo 1717059 1717111 := bstep (se 1 (by rfl) ⟨1287833, by rfl⟩ : syracuseStep 1717111 = 2575667) B2575667
theorem B1717131 : Blo 1717059 1717131 := bstep (se 1 (by rfl) ⟨1287848, by rfl⟩ : syracuseStep 1717131 = 2575697) B2575697
theorem B3863447 : Blo 1717059 3863447 := bstep (se 1 (by rfl) ⟨2897585, by rfl⟩ : syracuseStep 3863447 = 5795171) B5795171
theorem B1717143 : Blo 1717059 1717143 := bstep (se 1 (by rfl) ⟨1287857, by rfl⟩ : syracuseStep 1717143 = 2575715) B2575715
theorem B2577305 : Blo 1717059 2577305 := bstep (se 2 (by rfl) ⟨966489, by rfl⟩ : syracuseStep 2577305 = 1932979) B1932979
theorem B1717163 : Blo 1717059 1717163 := bstep (se 1 (by rfl) ⟨1287872, by rfl⟩ : syracuseStep 1717163 = 2575745) B2575745
theorem B1717175 : Blo 1717059 1717175 := bstep (se 1 (by rfl) ⟨1287881, by rfl⟩ : syracuseStep 1717175 = 2575763) B2575763
theorem B1717195 : Blo 1717059 1717195 := bstep (se 1 (by rfl) ⟨1287896, by rfl⟩ : syracuseStep 1717195 = 2575793) B2575793
theorem B1717207 : Blo 1717059 1717207 := bstep (se 1 (by rfl) ⟨1287905, by rfl⟩ : syracuseStep 1717207 = 2575811) B2575811
theorem B6525917 : Blo 1717059 6525917 := bstep (se 3 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 6525917 = 2447219) B2447219
theorem B1717227 : Blo 1717059 1717227 := bstep (se 1 (by rfl) ⟨1287920, by rfl⟩ : syracuseStep 1717227 = 2575841) B2575841
theorem B1717239 : Blo 1717059 1717239 := bstep (se 1 (by rfl) ⟨1287929, by rfl⟩ : syracuseStep 1717239 = 2575859) B2575859
theorem B1717259 : Blo 1717059 1717259 := bstep (se 1 (by rfl) ⟨1287944, by rfl⟩ : syracuseStep 1717259 = 2575889) B2575889
theorem B2577419 : Blo 1717059 2577419 := bstep (se 1 (by rfl) ⟨1933064, by rfl⟩ : syracuseStep 2577419 = 3866129) B3866129
theorem B1717271 : Blo 1717059 1717271 := bstep (se 1 (by rfl) ⟨1287953, by rfl⟩ : syracuseStep 1717271 = 2575907) B2575907
theorem B2577431 : Blo 1717059 2577431 := bstep (se 1 (by rfl) ⟨1933073, by rfl⟩ : syracuseStep 2577431 = 3866147) B3866147
theorem B1717291 : Blo 1717059 1717291 := bstep (se 1 (by rfl) ⟨1287968, by rfl⟩ : syracuseStep 1717291 = 2575937) B2575937
theorem B1717303 : Blo 1717059 1717303 := bstep (se 1 (by rfl) ⟨1287977, by rfl⟩ : syracuseStep 1717303 = 2575955) B2575955
theorem B3863627 : Blo 1717059 3863627 := bstep (se 1 (by rfl) ⟨2897720, by rfl⟩ : syracuseStep 3863627 = 5795441) B5795441
theorem B1717323 : Blo 1717059 1717323 := bstep (se 1 (by rfl) ⟨1287992, by rfl⟩ : syracuseStep 1717323 = 2575985) B2575985
theorem B1717335 : Blo 1717059 1717335 := bstep (se 1 (by rfl) ⟨1288001, by rfl⟩ : syracuseStep 1717335 = 2576003) B2576003
theorem B5796953 : Blo 1717059 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B2577497 : Blo 1717059 2577497 := bstep (se 2 (by rfl) ⟨966561, by rfl⟩ : syracuseStep 2577497 = 1933123) B1933123
theorem B1717355 : Blo 1717059 1717355 := bstep (se 1 (by rfl) ⟨1288016, by rfl⟩ : syracuseStep 1717355 = 2576033) B2576033
theorem B1717367 : Blo 1717059 1717367 := bstep (se 1 (by rfl) ⟨1288025, by rfl⟩ : syracuseStep 1717367 = 2576051) B2576051
theorem B1741943 : Blo 1717059 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B3863681 : Blo 1717059 3863681 := bstep (se 2 (by rfl) ⟨1448880, by rfl⟩ : syracuseStep 3863681 = 2897761) B2897761
theorem B1717387 : Blo 1717059 1717387 := bstep (se 1 (by rfl) ⟨1288040, by rfl⟩ : syracuseStep 1717387 = 2576081) B2576081
theorem B1717399 : Blo 1717059 1717399 := bstep (se 1 (by rfl) ⟨1288049, by rfl⟩ : syracuseStep 1717399 = 2576099) B2576099
theorem B1717419 : Blo 1717059 1717419 := bstep (se 1 (by rfl) ⟨1288064, by rfl⟩ : syracuseStep 1717419 = 2576129) B2576129
theorem B1717431 : Blo 1717059 1717431 := bstep (se 1 (by rfl) ⟨1288073, by rfl⟩ : syracuseStep 1717431 = 2576147) B2576147
theorem B1717451 : Blo 1717059 1717451 := bstep (se 1 (by rfl) ⟨1288088, by rfl⟩ : syracuseStep 1717451 = 2576177) B2576177
theorem B2577611 : Blo 1717059 2577611 := bstep (se 1 (by rfl) ⟨1933208, by rfl⟩ : syracuseStep 2577611 = 3866417) B3866417
theorem B1717463 : Blo 1717059 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B2577623 : Blo 1717059 2577623 := bstep (se 1 (by rfl) ⟨1933217, by rfl⟩ : syracuseStep 2577623 = 3866435) B3866435
theorem B1717483 : Blo 1717059 1717483 := bstep (se 1 (by rfl) ⟨1288112, by rfl⟩ : syracuseStep 1717483 = 2576225) B2576225
theorem B1717495 : Blo 1717059 1717495 := bstep (se 1 (by rfl) ⟨1288121, by rfl⟩ : syracuseStep 1717495 = 2576243) B2576243
theorem B1717515 : Blo 1717059 1717515 := bstep (se 1 (by rfl) ⟨1288136, by rfl⟩ : syracuseStep 1717515 = 2576273) B2576273
theorem B1717527 : Blo 1717059 1717527 := bstep (se 1 (by rfl) ⟨1288145, by rfl⟩ : syracuseStep 1717527 = 2576291) B2576291
theorem B2446615 : Blo 1717059 2446615 := bstep (se 1 (by rfl) ⟨1834961, by rfl⟩ : syracuseStep 2446615 = 3669923) B3669923
theorem B2577689 : Blo 1717059 2577689 := bstep (se 2 (by rfl) ⟨966633, by rfl⟩ : syracuseStep 2577689 = 1933267) B1933267
theorem B1717547 : Blo 1717059 1717547 := bstep (se 1 (by rfl) ⟨1288160, by rfl⟩ : syracuseStep 1717547 = 2576321) B2576321
theorem B1717559 : Blo 1717059 1717559 := bstep (se 1 (by rfl) ⟨1288169, by rfl⟩ : syracuseStep 1717559 = 2576339) B2576339
theorem B9786689 : Blo 1717059 9786689 := bstep (se 2 (by rfl) ⟨3670008, by rfl⟩ : syracuseStep 9786689 = 7340017) B7340017
theorem B1717579 : Blo 1717059 1717579 := bstep (se 1 (by rfl) ⟨1288184, by rfl⟩ : syracuseStep 1717579 = 2576369) B2576369
theorem B1717591 : Blo 1717059 1717591 := bstep (se 1 (by rfl) ⟨1288193, by rfl⟩ : syracuseStep 1717591 = 2576387) B2576387
theorem B3863897 : Blo 1717059 3863897 := bstep (se 2 (by rfl) ⟨1448961, by rfl⟩ : syracuseStep 3863897 = 2897923) B2897923
theorem B1717611 : Blo 1717059 1717611 := bstep (se 1 (by rfl) ⟨1288208, by rfl⟩ : syracuseStep 1717611 = 2576417) B2576417
theorem B1717623 : Blo 1717059 1717623 := bstep (se 1 (by rfl) ⟨1288217, by rfl⟩ : syracuseStep 1717623 = 2576435) B2576435
theorem B1717643 : Blo 1717059 1717643 := bstep (se 1 (by rfl) ⟨1288232, by rfl⟩ : syracuseStep 1717643 = 2576465) B2576465
theorem B2577803 : Blo 1717059 2577803 := bstep (se 1 (by rfl) ⟨1933352, by rfl⟩ : syracuseStep 2577803 = 3866705) B3866705
theorem B1717655 : Blo 1717059 1717655 := bstep (se 1 (by rfl) ⟨1288241, by rfl⟩ : syracuseStep 1717655 = 2576483) B2576483
theorem B2577815 : Blo 1717059 2577815 := bstep (se 1 (by rfl) ⟨1933361, by rfl⟩ : syracuseStep 2577815 = 3866723) B3866723
theorem B1717675 : Blo 1717059 1717675 := bstep (se 1 (by rfl) ⟨1288256, by rfl⟩ : syracuseStep 1717675 = 2576513) B2576513
theorem B3863987 : Blo 1717059 3863987 := bstep (se 1 (by rfl) ⟨2897990, by rfl⟩ : syracuseStep 3863987 = 5795981) B5795981
theorem B1717687 : Blo 1717059 1717687 := bstep (se 1 (by rfl) ⟨1288265, by rfl⟩ : syracuseStep 1717687 = 2576531) B2576531
theorem B1717707 : Blo 1717059 1717707 := bstep (se 1 (by rfl) ⟨1288280, by rfl⟩ : syracuseStep 1717707 = 2576561) B2576561
theorem B3864023 : Blo 1717059 3864023 := bstep (se 1 (by rfl) ⟨2898017, by rfl⟩ : syracuseStep 3864023 = 5796035) B5796035
theorem B1717719 : Blo 1717059 1717719 := bstep (se 1 (by rfl) ⟨1288289, by rfl⟩ : syracuseStep 1717719 = 2576579) B2576579
theorem B2577881 : Blo 1717059 2577881 := bstep (se 2 (by rfl) ⟨966705, by rfl⟩ : syracuseStep 2577881 = 1933411) B1933411
theorem B1717739 : Blo 1717059 1717739 := bstep (se 1 (by rfl) ⟨1288304, by rfl⟩ : syracuseStep 1717739 = 2576609) B2576609
theorem B1717751 : Blo 1717059 1717751 := bstep (se 1 (by rfl) ⟨1288313, by rfl⟩ : syracuseStep 1717751 = 2576627) B2576627
theorem B1717771 : Blo 1717059 1717771 := bstep (se 1 (by rfl) ⟨1288328, by rfl⟩ : syracuseStep 1717771 = 2576657) B2576657
theorem B1717783 : Blo 1717059 1717783 := bstep (se 1 (by rfl) ⟨1288337, by rfl⟩ : syracuseStep 1717783 = 2576675) B2576675
theorem B1717803 : Blo 1717059 1717803 := bstep (se 1 (by rfl) ⟨1288352, by rfl⟩ : syracuseStep 1717803 = 2576705) B2576705
theorem B1717815 : Blo 1717059 1717815 := bstep (se 1 (by rfl) ⟨1288361, by rfl⟩ : syracuseStep 1717815 = 2576723) B2576723
theorem B3667531 : Blo 1717059 3667531 := bstep (se 1 (by rfl) ⟨2750648, by rfl⟩ : syracuseStep 3667531 = 5501297) B5501297
theorem B1717835 : Blo 1717059 1717835 := bstep (se 1 (by rfl) ⟨1288376, by rfl⟩ : syracuseStep 1717835 = 2576753) B2576753
theorem B2577995 : Blo 1717059 2577995 := bstep (se 1 (by rfl) ⟨1933496, by rfl⟩ : syracuseStep 2577995 = 3866993) B3866993
theorem B1717847 : Blo 1717059 1717847 := bstep (se 1 (by rfl) ⟨1288385, by rfl⟩ : syracuseStep 1717847 = 2576771) B2576771
theorem B2578007 : Blo 1717059 2578007 := bstep (se 1 (by rfl) ⟨1933505, by rfl⟩ : syracuseStep 2578007 = 3867011) B3867011
theorem B13407845 : Blo 1717059 13407845 := bstep (se 4 (by rfl) ⟨1256985, by rfl⟩ : syracuseStep 13407845 = 2513971) B2513971
theorem B1717867 : Blo 1717059 1717867 := bstep (se 1 (by rfl) ⟨1288400, by rfl⟩ : syracuseStep 1717867 = 2576801) B2576801
theorem B1717879 : Blo 1717059 1717879 := bstep (se 1 (by rfl) ⟨1288409, by rfl⟩ : syracuseStep 1717879 = 2576819) B2576819
theorem B3864203 : Blo 1717059 3864203 := bstep (se 1 (by rfl) ⟨2898152, by rfl⟩ : syracuseStep 3864203 = 5796305) B5796305
theorem B1717899 : Blo 1717059 1717899 := bstep (se 1 (by rfl) ⟨1288424, by rfl⟩ : syracuseStep 1717899 = 2576849) B2576849
theorem B1717911 : Blo 1717059 1717911 := bstep (se 1 (by rfl) ⟨1288433, by rfl⟩ : syracuseStep 1717911 = 2576867) B2576867
theorem B6526615 : Blo 1717059 6526615 := bstep (se 1 (by rfl) ⟨4894961, by rfl⟩ : syracuseStep 6526615 = 9789923) B9789923
theorem B2578073 : Blo 1717059 2578073 := bstep (se 2 (by rfl) ⟨966777, by rfl⟩ : syracuseStep 2578073 = 1933555) B1933555
theorem B1717931 : Blo 1717059 1717931 := bstep (se 1 (by rfl) ⟨1288448, by rfl⟩ : syracuseStep 1717931 = 2576897) B2576897
theorem B1717943 : Blo 1717059 1717943 := bstep (se 1 (by rfl) ⟨1288457, by rfl⟩ : syracuseStep 1717943 = 2576915) B2576915
theorem B3864257 : Blo 1717059 3864257 := bstep (se 2 (by rfl) ⟨1449096, by rfl⟩ : syracuseStep 3864257 = 2898193) B2898193
theorem B1717963 : Blo 1717059 1717963 := bstep (se 1 (by rfl) ⟨1288472, by rfl⟩ : syracuseStep 1717963 = 2576945) B2576945
theorem B1717975 : Blo 1717059 1717975 := bstep (se 1 (by rfl) ⟨1288481, by rfl⟩ : syracuseStep 1717975 = 2576963) B2576963
theorem B1717995 : Blo 1717059 1717995 := bstep (se 1 (by rfl) ⟨1288496, by rfl⟩ : syracuseStep 1717995 = 2576993) B2576993
theorem B1718007 : Blo 1717059 1718007 := bstep (se 1 (by rfl) ⟨1288505, by rfl⟩ : syracuseStep 1718007 = 2577011) B2577011
theorem B1718027 : Blo 1717059 1718027 := bstep (se 1 (by rfl) ⟨1288520, by rfl⟩ : syracuseStep 1718027 = 2577041) B2577041
theorem B2578187 : Blo 1717059 2578187 := bstep (se 1 (by rfl) ⟨1933640, by rfl⟩ : syracuseStep 2578187 = 3867281) B3867281
theorem B8697617 : Blo 1717059 8697617 := bstep (se 2 (by rfl) ⟨3261606, by rfl⟩ : syracuseStep 8697617 = 6523213) B6523213
theorem B2897687 : Blo 1717059 2897687 := bstep (se 1 (by rfl) ⟨2173265, by rfl⟩ : syracuseStep 2897687 = 4346531) B4346531
theorem B5797655 : Blo 1717059 5797655 := bstep (se 1 (by rfl) ⟨4348241, by rfl⟩ : syracuseStep 5797655 = 8696483) B8696483
theorem B1718039 : Blo 1717059 1718039 := bstep (se 1 (by rfl) ⟨1288529, by rfl⟩ : syracuseStep 1718039 = 2577059) B2577059
theorem B2578199 : Blo 1717059 2578199 := bstep (se 1 (by rfl) ⟨1933649, by rfl⟩ : syracuseStep 2578199 = 3867299) B3867299
theorem B1718059 : Blo 1717059 1718059 := bstep (se 1 (by rfl) ⟨1288544, by rfl⟩ : syracuseStep 1718059 = 2577089) B2577089
theorem B1718071 : Blo 1717059 1718071 := bstep (se 1 (by rfl) ⟨1288553, by rfl⟩ : syracuseStep 1718071 = 2577107) B2577107
theorem B1718091 : Blo 1717059 1718091 := bstep (se 1 (by rfl) ⟨1288568, by rfl⟩ : syracuseStep 1718091 = 2577137) B2577137
theorem B1718103 : Blo 1717059 1718103 := bstep (se 1 (by rfl) ⟨1288577, by rfl⟩ : syracuseStep 1718103 = 2577155) B2577155
theorem B2578265 : Blo 1717059 2578265 := bstep (se 2 (by rfl) ⟨966849, by rfl⟩ : syracuseStep 2578265 = 1933699) B1933699
theorem B1718123 : Blo 1717059 1718123 := bstep (se 1 (by rfl) ⟨1288592, by rfl⟩ : syracuseStep 1718123 = 2577185) B2577185
theorem B1718135 : Blo 1717059 1718135 := bstep (se 1 (by rfl) ⟨1288601, by rfl⟩ : syracuseStep 1718135 = 2577203) B2577203
theorem B1718155 : Blo 1717059 1718155 := bstep (se 1 (by rfl) ⟨1288616, by rfl⟩ : syracuseStep 1718155 = 2577233) B2577233
theorem B2897815 : Blo 1717059 2897815 := bstep (se 1 (by rfl) ⟨2173361, by rfl⟩ : syracuseStep 2897815 = 4346723) B4346723
theorem B1718167 : Blo 1717059 1718167 := bstep (se 1 (by rfl) ⟨1288625, by rfl⟩ : syracuseStep 1718167 = 2577251) B2577251
theorem B3864473 : Blo 1717059 3864473 := bstep (se 2 (by rfl) ⟨1449177, by rfl⟩ : syracuseStep 3864473 = 2898355) B2898355
theorem B1718187 : Blo 1717059 1718187 := bstep (se 1 (by rfl) ⟨1288640, by rfl⟩ : syracuseStep 1718187 = 2577281) B2577281
theorem B18585521 : Blo 1717059 18585521 := bstep (se 2 (by rfl) ⟨6969570, by rfl⟩ : syracuseStep 18585521 = 13939141) B13939141
theorem B4347827 : Blo 1717059 4347827 := bstep (se 1 (by rfl) ⟨3260870, by rfl⟩ : syracuseStep 4347827 = 6521741) B6521741
theorem B8697779 : Blo 1717059 8697779 := bstep (se 1 (by rfl) ⟨6523334, by rfl⟩ : syracuseStep 8697779 = 13046669) B13046669
theorem B1718199 : Blo 1717059 1718199 := bstep (se 1 (by rfl) ⟨1288649, by rfl⟩ : syracuseStep 1718199 = 2577299) B2577299
theorem B1718219 : Blo 1717059 1718219 := bstep (se 1 (by rfl) ⟨1288664, by rfl⟩ : syracuseStep 1718219 = 2577329) B2577329
theorem B2578379 : Blo 1717059 2578379 := bstep (se 1 (by rfl) ⟨1933784, by rfl⟩ : syracuseStep 2578379 = 3867569) B3867569
theorem B1718231 : Blo 1717059 1718231 := bstep (se 1 (by rfl) ⟨1288673, by rfl⟩ : syracuseStep 1718231 = 2577347) B2577347
theorem B2578391 : Blo 1717059 2578391 := bstep (se 1 (by rfl) ⟨1933793, by rfl⟩ : syracuseStep 2578391 = 3867587) B3867587
theorem B5502937 : Blo 1717059 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B1718251 : Blo 1717059 1718251 := bstep (se 1 (by rfl) ⟨1288688, by rfl⟩ : syracuseStep 1718251 = 2577377) B2577377
theorem B3864563 : Blo 1717059 3864563 := bstep (se 1 (by rfl) ⟨2898422, by rfl⟩ : syracuseStep 3864563 = 5796845) B5796845
theorem B1718263 : Blo 1717059 1718263 := bstep (se 1 (by rfl) ⟨1288697, by rfl⟩ : syracuseStep 1718263 = 2577395) B2577395
theorem B1718283 : Blo 1717059 1718283 := bstep (se 1 (by rfl) ⟨1288712, by rfl⟩ : syracuseStep 1718283 = 2577425) B2577425
theorem B6969361 : Blo 1717059 6969361 := bstep (se 2 (by rfl) ⟨2613510, by rfl⟩ : syracuseStep 6969361 = 5227021) B5227021
theorem B6273047 : Blo 1717059 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B3864599 : Blo 1717059 3864599 := bstep (se 1 (by rfl) ⟨2898449, by rfl⟩ : syracuseStep 3864599 = 5796899) B5796899
theorem B1718295 : Blo 1717059 1718295 := bstep (se 1 (by rfl) ⟨1288721, by rfl⟩ : syracuseStep 1718295 = 2577443) B2577443
theorem B2578457 : Blo 1717059 2578457 := bstep (se 2 (by rfl) ⟨966921, by rfl⟩ : syracuseStep 2578457 = 1933843) B1933843
theorem B1718315 : Blo 1717059 1718315 := bstep (se 1 (by rfl) ⟨1288736, by rfl⟩ : syracuseStep 1718315 = 2577473) B2577473
theorem B1718327 : Blo 1717059 1718327 := bstep (se 1 (by rfl) ⟨1288745, by rfl⟩ : syracuseStep 1718327 = 2577491) B2577491
theorem B4773953 : Blo 1717059 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B1718347 : Blo 1717059 1718347 := bstep (se 1 (by rfl) ⟨1288760, by rfl⟩ : syracuseStep 1718347 = 2577521) B2577521
theorem B1718359 : Blo 1717059 1718359 := bstep (se 1 (by rfl) ⟨1288769, by rfl⟩ : syracuseStep 1718359 = 2577539) B2577539
theorem B1718379 : Blo 1717059 1718379 := bstep (se 1 (by rfl) ⟨1288784, by rfl⟩ : syracuseStep 1718379 = 2577569) B2577569
theorem B1718391 : Blo 1717059 1718391 := bstep (se 1 (by rfl) ⟨1288793, by rfl⟩ : syracuseStep 1718391 = 2577587) B2577587
theorem B1718411 : Blo 1717059 1718411 := bstep (se 1 (by rfl) ⟨1288808, by rfl⟩ : syracuseStep 1718411 = 2577617) B2577617
theorem B2578571 : Blo 1717059 2578571 := bstep (se 1 (by rfl) ⟨1933928, by rfl⟩ : syracuseStep 2578571 = 3867857) B3867857
theorem B1718423 : Blo 1717059 1718423 := bstep (se 1 (by rfl) ⟨1288817, by rfl⟩ : syracuseStep 1718423 = 2577635) B2577635
theorem B2578583 : Blo 1717059 2578583 := bstep (se 1 (by rfl) ⟨1933937, by rfl⟩ : syracuseStep 2578583 = 3867875) B3867875
theorem B1718443 : Blo 1717059 1718443 := bstep (se 1 (by rfl) ⟨1288832, by rfl⟩ : syracuseStep 1718443 = 2577665) B2577665
theorem B1718455 : Blo 1717059 1718455 := bstep (se 1 (by rfl) ⟨1288841, by rfl⟩ : syracuseStep 1718455 = 2577683) B2577683
theorem B3864779 : Blo 1717059 3864779 := bstep (se 1 (by rfl) ⟨2898584, by rfl⟩ : syracuseStep 3864779 = 5797169) B5797169
theorem B1718475 : Blo 1717059 1718475 := bstep (se 1 (by rfl) ⟨1288856, by rfl⟩ : syracuseStep 1718475 = 2577713) B2577713
theorem B1718487 : Blo 1717059 1718487 := bstep (se 1 (by rfl) ⟨1288865, by rfl⟩ : syracuseStep 1718487 = 2577731) B2577731
theorem B13220057 : Blo 1717059 13220057 := bstep (se 2 (by rfl) ⟨4957521, by rfl⟩ : syracuseStep 13220057 = 9915043) B9915043
theorem B7338205 : Blo 1717059 7338205 := bstep (se 3 (by rfl) ⟨1375913, by rfl⟩ : syracuseStep 7338205 = 2751827) B2751827
theorem B1718507 : Blo 1717059 1718507 := bstep (se 1 (by rfl) ⟨1288880, by rfl⟩ : syracuseStep 1718507 = 2577761) B2577761
theorem B1718519 : Blo 1717059 1718519 := bstep (se 1 (by rfl) ⟨1288889, by rfl⟩ : syracuseStep 1718519 = 2577779) B2577779
theorem B3864833 : Blo 1717059 3864833 := bstep (se 2 (by rfl) ⟨1449312, by rfl⟩ : syracuseStep 3864833 = 2898625) B2898625
theorem B1718539 : Blo 1717059 1718539 := bstep (se 1 (by rfl) ⟨1288904, by rfl⟩ : syracuseStep 1718539 = 2577809) B2577809
theorem B1718551 : Blo 1717059 1718551 := bstep (se 1 (by rfl) ⟨1288913, by rfl⟩ : syracuseStep 1718551 = 2577827) B2577827
theorem B3668249 : Blo 1717059 3668249 := bstep (se 2 (by rfl) ⟨1375593, by rfl⟩ : syracuseStep 3668249 = 2751187) B2751187
theorem B1718571 : Blo 1717059 1718571 := bstep (se 1 (by rfl) ⟨1288928, by rfl⟩ : syracuseStep 1718571 = 2577857) B2577857
theorem B5798195 : Blo 1717059 5798195 := bstep (se 1 (by rfl) ⟨4348646, by rfl⟩ : syracuseStep 5798195 = 8697293) B8697293
theorem B1718583 : Blo 1717059 1718583 := bstep (se 1 (by rfl) ⟨1288937, by rfl⟩ : syracuseStep 1718583 = 2577875) B2577875
theorem B1718603 : Blo 1717059 1718603 := bstep (se 1 (by rfl) ⟨1288952, by rfl⟩ : syracuseStep 1718603 = 2577905) B2577905
theorem B1718615 : Blo 1717059 1718615 := bstep (se 1 (by rfl) ⟨1288961, by rfl⟩ : syracuseStep 1718615 = 2577923) B2577923
theorem B1718635 : Blo 1717059 1718635 := bstep (se 1 (by rfl) ⟨1288976, by rfl⟩ : syracuseStep 1718635 = 2577953) B2577953
theorem B1718647 : Blo 1717059 1718647 := bstep (se 1 (by rfl) ⟨1288985, by rfl⟩ : syracuseStep 1718647 = 2577971) B2577971
theorem B1718667 : Blo 1717059 1718667 := bstep (se 1 (by rfl) ⟨1289000, by rfl⟩ : syracuseStep 1718667 = 2578001) B2578001
theorem B1718679 : Blo 1717059 1718679 := bstep (se 1 (by rfl) ⟨1289009, by rfl⟩ : syracuseStep 1718679 = 2578019) B2578019
theorem B1718699 : Blo 1717059 1718699 := bstep (se 1 (by rfl) ⟨1289024, by rfl⟩ : syracuseStep 1718699 = 2578049) B2578049
theorem B1718711 : Blo 1717059 1718711 := bstep (se 1 (by rfl) ⟨1289033, by rfl⟩ : syracuseStep 1718711 = 2578067) B2578067
theorem B4348363 : Blo 1717059 4348363 := bstep (se 1 (by rfl) ⟨3261272, by rfl⟩ : syracuseStep 4348363 = 6522545) B6522545
theorem B1718731 : Blo 1717059 1718731 := bstep (se 1 (by rfl) ⟨1289048, by rfl⟩ : syracuseStep 1718731 = 2578097) B2578097
theorem B1718743 : Blo 1717059 1718743 := bstep (se 1 (by rfl) ⟨1289057, by rfl⟩ : syracuseStep 1718743 = 2578115) B2578115
theorem B3865049 : Blo 1717059 3865049 := bstep (se 2 (by rfl) ⟨1449393, by rfl⟩ : syracuseStep 3865049 = 2898787) B2898787
theorem B1931755 : Blo 1717059 1931755 := bstep (se 1 (by rfl) ⟨1448816, by rfl⟩ : syracuseStep 1931755 = 2897633) B2897633
theorem B1718763 : Blo 1717059 1718763 := bstep (se 1 (by rfl) ⟨1289072, by rfl⟩ : syracuseStep 1718763 = 2578145) B2578145
theorem B1718775 : Blo 1717059 1718775 := bstep (se 1 (by rfl) ⟨1289081, by rfl⟩ : syracuseStep 1718775 = 2578163) B2578163
theorem B2898443 : Blo 1717059 2898443 := bstep (se 1 (by rfl) ⟨2173832, by rfl⟩ : syracuseStep 2898443 = 4347665) B4347665
theorem B1718795 : Blo 1717059 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B1718807 : Blo 1717059 1718807 := bstep (se 1 (by rfl) ⟨1289105, by rfl⟩ : syracuseStep 1718807 = 2578211) B2578211
theorem B1718827 : Blo 1717059 1718827 := bstep (se 1 (by rfl) ⟨1289120, by rfl⟩ : syracuseStep 1718827 = 2578241) B2578241
theorem B3865139 : Blo 1717059 3865139 := bstep (se 1 (by rfl) ⟨2898854, by rfl⟩ : syracuseStep 3865139 = 5797709) B5797709
theorem B1718839 : Blo 1717059 1718839 := bstep (se 1 (by rfl) ⟨1289129, by rfl⟩ : syracuseStep 1718839 = 2578259) B2578259
theorem B5798465 : Blo 1717059 5798465 := bstep (se 2 (by rfl) ⟨2174424, by rfl⟩ : syracuseStep 5798465 = 4348849) B4348849
theorem B1718859 : Blo 1717059 1718859 := bstep (se 1 (by rfl) ⟨1289144, by rfl⟩ : syracuseStep 1718859 = 2578289) B2578289
theorem B1931863 : Blo 1717059 1931863 := bstep (se 1 (by rfl) ⟨1448897, by rfl⟩ : syracuseStep 1931863 = 2897795) B2897795
theorem B3865175 : Blo 1717059 3865175 := bstep (se 1 (by rfl) ⟨2898881, by rfl⟩ : syracuseStep 3865175 = 5797763) B5797763
theorem B3095129 : Blo 1717059 3095129 := bstep (se 2 (by rfl) ⟨1160673, by rfl⟩ : syracuseStep 3095129 = 2321347) B2321347
theorem B4348505 : Blo 1717059 4348505 := bstep (se 2 (by rfl) ⟨1630689, by rfl⟩ : syracuseStep 4348505 = 3261379) B3261379
theorem B1718871 : Blo 1717059 1718871 := bstep (se 1 (by rfl) ⟨1289153, by rfl⟩ : syracuseStep 1718871 = 2578307) B2578307
theorem B1718891 : Blo 1717059 1718891 := bstep (se 1 (by rfl) ⟨1289168, by rfl⟩ : syracuseStep 1718891 = 2578337) B2578337
theorem B1718903 : Blo 1717059 1718903 := bstep (se 1 (by rfl) ⟨1289177, by rfl⟩ : syracuseStep 1718903 = 2578355) B2578355
theorem B12384899 : Blo 1717059 12384899 := bstep (se 1 (by rfl) ⟨9288674, by rfl⟩ : syracuseStep 12384899 = 18577349) B18577349
theorem B2898571 : Blo 1717059 2898571 := bstep (se 1 (by rfl) ⟨2173928, by rfl⟩ : syracuseStep 2898571 = 4347857) B4347857
theorem B1718923 : Blo 1717059 1718923 := bstep (se 1 (by rfl) ⟨1289192, by rfl⟩ : syracuseStep 1718923 = 2578385) B2578385
theorem B1718935 : Blo 1717059 1718935 := bstep (se 1 (by rfl) ⟨1289201, by rfl⟩ : syracuseStep 1718935 = 2578403) B2578403
theorem B1718955 : Blo 1717059 1718955 := bstep (se 1 (by rfl) ⟨1289216, by rfl⟩ : syracuseStep 1718955 = 2578433) B2578433
theorem B9288371 : Blo 1717059 9288371 := bstep (se 1 (by rfl) ⟨6966278, by rfl⟩ : syracuseStep 9288371 = 13932557) B13932557
theorem B1718967 : Blo 1717059 1718967 := bstep (se 1 (by rfl) ⟨1289225, by rfl⟩ : syracuseStep 1718967 = 2578451) B2578451
theorem B1718987 : Blo 1717059 1718987 := bstep (se 1 (by rfl) ⟨1289240, by rfl⟩ : syracuseStep 1718987 = 2578481) B2578481
theorem B1718999 : Blo 1717059 1718999 := bstep (se 1 (by rfl) ⟨1289249, by rfl⟩ : syracuseStep 1718999 = 2578499) B2578499
theorem B1719019 : Blo 1717059 1719019 := bstep (se 1 (by rfl) ⟨1289264, by rfl⟩ : syracuseStep 1719019 = 2578529) B2578529
theorem B1719031 : Blo 1717059 1719031 := bstep (se 1 (by rfl) ⟨1289273, by rfl⟩ : syracuseStep 1719031 = 2578547) B2578547
theorem B1932043 : Blo 1717059 1932043 := bstep (se 1 (by rfl) ⟨1449032, by rfl⟩ : syracuseStep 1932043 = 2898065) B2898065
theorem B3865355 : Blo 1717059 3865355 := bstep (se 1 (by rfl) ⟨2899016, by rfl⟩ : syracuseStep 3865355 = 5798033) B5798033
theorem B1719051 : Blo 1717059 1719051 := bstep (se 1 (by rfl) ⟨1289288, by rfl⟩ : syracuseStep 1719051 = 2578577) B2578577
theorem B2898713 : Blo 1717059 2898713 := bstep (se 2 (by rfl) ⟨1087017, by rfl⟩ : syracuseStep 2898713 = 2174035) B2174035
theorem B3668761 : Blo 1717059 3668761 := bstep (se 2 (by rfl) ⟨1375785, by rfl⟩ : syracuseStep 3668761 = 2751571) B2751571
theorem B3865409 : Blo 1717059 3865409 := bstep (se 2 (by rfl) ⟨1449528, by rfl⟩ : syracuseStep 3865409 = 2899057) B2899057
theorem B1932151 : Blo 1717059 1932151 := bstep (se 1 (by rfl) ⟨1449113, by rfl⟩ : syracuseStep 1932151 = 2898227) B2898227
theorem B15678359 : Blo 1717059 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B2898841 : Blo 1717059 2898841 := bstep (se 2 (by rfl) ⟨1087065, by rfl⟩ : syracuseStep 2898841 = 2174131) B2174131
theorem B6962093 : Blo 1717059 6962093 := bstep (se 3 (by rfl) ⟨1305392, by rfl⟩ : syracuseStep 6962093 = 2610785) B2610785
theorem B3668915 : Blo 1717059 3668915 := bstep (se 1 (by rfl) ⟨2751686, by rfl⟩ : syracuseStep 3668915 = 5503373) B5503373
theorem B5880755 : Blo 1717059 5880755 := bstep (se 1 (by rfl) ⟨4410566, by rfl⟩ : syracuseStep 5880755 = 8821133) B8821133
theorem B6519811 : Blo 1717059 6519811 := bstep (se 1 (by rfl) ⟨4889858, by rfl⟩ : syracuseStep 6519811 = 9779717) B9779717
theorem B7339025 : Blo 1717059 7339025 := bstep (se 2 (by rfl) ⟨2752134, by rfl⟩ : syracuseStep 7339025 = 5504269) B5504269
theorem B3865625 : Blo 1717059 3865625 := bstep (se 2 (by rfl) ⟨1449609, by rfl⟩ : syracuseStep 3865625 = 2899219) B2899219
theorem B1932331 : Blo 1717059 1932331 := bstep (se 1 (by rfl) ⟨1449248, by rfl⟩ : syracuseStep 1932331 = 2898497) B2898497
theorem B1834039 : Blo 1717059 1834039 := bstep (se 1 (by rfl) ⟨1375529, by rfl⟩ : syracuseStep 1834039 = 2751059) B2751059
theorem B6192217 : Blo 1717059 6192217 := bstep (se 2 (by rfl) ⟨2322081, by rfl⟩ : syracuseStep 6192217 = 4644163) B4644163
theorem B5799005 : Blo 1717059 5799005 := bstep (se 3 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 5799005 = 2174627) B2174627
theorem B7838813 : Blo 1717059 7838813 := bstep (se 3 (by rfl) ⟨1469777, by rfl⟩ : syracuseStep 7838813 = 2939555) B2939555
theorem B3865715 : Blo 1717059 3865715 := bstep (se 1 (by rfl) ⟨2899286, by rfl⟩ : syracuseStep 3865715 = 5798573) B5798573
theorem B1932439 : Blo 1717059 1932439 := bstep (se 1 (by rfl) ⟨1449329, by rfl⟩ : syracuseStep 1932439 = 2898659) B2898659
theorem B3865751 : Blo 1717059 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B6962449 : Blo 1717059 6962449 := bstep (se 2 (by rfl) ⟨2610918, by rfl⟩ : syracuseStep 6962449 = 5221837) B5221837
theorem B13925677 : Blo 1717059 13925677 := bstep (se 3 (by rfl) ⟨2611064, by rfl⟩ : syracuseStep 13925677 = 5222129) B5222129
theorem B6520115 : Blo 1717059 6520115 := bstep (se 1 (by rfl) ⟨4890086, by rfl⟩ : syracuseStep 6520115 = 9780173) B9780173
theorem B1932619 : Blo 1717059 1932619 := bstep (se 1 (by rfl) ⟨1449464, by rfl⟩ : syracuseStep 1932619 = 2898929) B2898929
theorem B11754827 : Blo 1717059 11754827 := bstep (se 1 (by rfl) ⟨8816120, by rfl⟩ : syracuseStep 11754827 = 17632241) B17632241
theorem B3865931 : Blo 1717059 3865931 := bstep (se 1 (by rfl) ⟨2899448, by rfl⟩ : syracuseStep 3865931 = 5798897) B5798897
theorem B2612569 : Blo 1717059 2612569 := bstep (se 2 (by rfl) ⟨979713, by rfl⟩ : syracuseStep 2612569 = 1959427) B1959427
theorem B3259777 : Blo 1717059 3259777 := bstep (se 2 (by rfl) ⟨1222416, by rfl⟩ : syracuseStep 3259777 = 2444833) B2444833
theorem B3865985 : Blo 1717059 3865985 := bstep (se 2 (by rfl) ⟨1449744, by rfl⟩ : syracuseStep 3865985 = 2899489) B2899489
theorem B3480983 : Blo 1717059 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B4349335 : Blo 1717059 4349335 := bstep (se 1 (by rfl) ⟨3262001, by rfl⟩ : syracuseStep 4349335 = 6524003) B6524003
theorem B1932727 : Blo 1717059 1932727 := bstep (se 1 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 1932727 = 2899091) B2899091
theorem B2899415 : Blo 1717059 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B2899543 : Blo 1717059 2899543 := bstep (se 1 (by rfl) ⟨2174657, by rfl⟩ : syracuseStep 2899543 = 4349315) B4349315
theorem B3866201 : Blo 1717059 3866201 := bstep (se 2 (by rfl) ⟨1449825, by rfl⟩ : syracuseStep 3866201 = 2899651) B2899651
theorem B1932907 : Blo 1717059 1932907 := bstep (se 1 (by rfl) ⟨1449680, by rfl⟩ : syracuseStep 1932907 = 2899361) B2899361
theorem B7339693 : Blo 1717059 7339693 := bstep (se 3 (by rfl) ⟨1376192, by rfl⟩ : syracuseStep 7339693 = 2752385) B2752385
theorem B3866291 : Blo 1717059 3866291 := bstep (se 1 (by rfl) ⟨2899718, by rfl⟩ : syracuseStep 3866291 = 5799437) B5799437
theorem B1933015 : Blo 1717059 1933015 := bstep (se 1 (by rfl) ⟨1449761, by rfl⟩ : syracuseStep 1933015 = 2899523) B2899523
theorem B3866327 : Blo 1717059 3866327 := bstep (se 1 (by rfl) ⟨2899745, by rfl⟩ : syracuseStep 3866327 = 5799491) B5799491
theorem B3260225 : Blo 1717059 3260225 := bstep (se 2 (by rfl) ⟨1222584, by rfl⟩ : syracuseStep 3260225 = 2445169) B2445169
theorem B9674561 : Blo 1717059 9674561 := bstep (se 2 (by rfl) ⟨3627960, by rfl⟩ : syracuseStep 9674561 = 7255921) B7255921
theorem B4128587 : Blo 1717059 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B4349771 : Blo 1717059 4349771 := bstep (se 1 (by rfl) ⟨3262328, by rfl⟩ : syracuseStep 4349771 = 6524657) B6524657
theorem B8699723 : Blo 1717059 8699723 := bstep (se 1 (by rfl) ⟨6524792, by rfl⟩ : syracuseStep 8699723 = 13049585) B13049585
theorem B1834859 : Blo 1717059 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B3669889 : Blo 1717059 3669889 := bstep (se 2 (by rfl) ⟨1376208, by rfl⟩ : syracuseStep 3669889 = 2752417) B2752417
theorem B1933195 : Blo 1717059 1933195 := bstep (se 1 (by rfl) ⟨1449896, by rfl⟩ : syracuseStep 1933195 = 2899793) B2899793
theorem B3866507 : Blo 1717059 3866507 := bstep (se 1 (by rfl) ⟨2899880, by rfl⟩ : syracuseStep 3866507 = 5799761) B5799761
theorem B4186007 : Blo 1717059 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B6520769 : Blo 1717059 6520769 := bstep (se 2 (by rfl) ⟨2445288, by rfl⟩ : syracuseStep 6520769 = 4890577) B4890577
theorem B3866561 : Blo 1717059 3866561 := bstep (se 2 (by rfl) ⟨1449960, by rfl⟩ : syracuseStep 3866561 = 2899921) B2899921
theorem B4128779 : Blo 1717059 4128779 := bstep (se 1 (by rfl) ⟨3096584, by rfl⟩ : syracuseStep 4128779 = 6193169) B6193169
theorem B4349963 : Blo 1717059 4349963 := bstep (se 1 (by rfl) ⟨3262472, by rfl⟩ : syracuseStep 4349963 = 6524945) B6524945
theorem B19570733 : Blo 1717059 19570733 := bstep (se 3 (by rfl) ⟨3669512, by rfl⟩ : syracuseStep 19570733 = 7339025) B7339025
theorem B20906029 : Blo 1717059 20906029 := bstep (se 3 (by rfl) ⟨3919880, by rfl⟩ : syracuseStep 20906029 = 7839761) B7839761
theorem B3866759 : Blo 1717059 3866759 := bstep (se 1 (by rfl) ⟨2900069, by rfl⟩ : syracuseStep 3866759 = 5800139) B5800139
theorem B1933447 : Blo 1717059 1933447 := bstep (se 1 (by rfl) ⟨1450085, by rfl⟩ : syracuseStep 1933447 = 2900171) B2900171
theorem B14680237 : Blo 1717059 14680237 := bstep (se 3 (by rfl) ⟨2752544, by rfl⟩ : syracuseStep 14680237 = 5505089) B5505089
theorem B17662153 : Blo 1717059 17662153 := bstep (se 2 (by rfl) ⟨6623307, by rfl⟩ : syracuseStep 17662153 = 13246615) B13246615
theorem B5800193 : Blo 1717059 5800193 := bstep (se 2 (by rfl) ⟨2175072, by rfl⟩ : syracuseStep 5800193 = 4350145) B4350145
theorem B6275387 : Blo 1717059 6275387 := bstep (se 1 (by rfl) ⟨4706540, by rfl⟩ : syracuseStep 6275387 = 9413081) B9413081
theorem B3866939 : Blo 1717059 3866939 := bstep (se 1 (by rfl) ⟨2900204, by rfl⟩ : syracuseStep 3866939 = 5800409) B5800409
theorem B4645181 : Blo 1717059 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B1933627 : Blo 1717059 1933627 := bstep (se 1 (by rfl) ⟨1450220, by rfl⟩ : syracuseStep 1933627 = 2900441) B2900441
theorem B35766593 : Blo 1717059 35766593 := bstep (se 2 (by rfl) ⟨13412472, by rfl⟩ : syracuseStep 35766593 = 26824945) B26824945
theorem B3867065 : Blo 1717059 3867065 := bstep (se 2 (by rfl) ⟨1450149, by rfl⟩ : syracuseStep 3867065 = 2900299) B2900299
theorem B6193675 : Blo 1717059 6193675 := bstep (se 1 (by rfl) ⟨4645256, by rfl⟩ : syracuseStep 6193675 = 9290513) B9290513
theorem B2900495 : Blo 1717059 2900495 := bstep (se 1 (by rfl) ⟨2175371, by rfl⟩ : syracuseStep 2900495 = 4350743) B4350743
theorem B13042295 : Blo 1717059 13042295 := bstep (se 1 (by rfl) ⟨9781721, by rfl⟩ : syracuseStep 13042295 = 19563443) B19563443
theorem B4350611 : Blo 1717059 4350611 := bstep (se 1 (by rfl) ⟨3262958, by rfl⟩ : syracuseStep 4350611 = 6525917) B6525917
theorem B4129433 : Blo 1717059 4129433 := bstep (se 2 (by rfl) ⟨1548537, by rfl⟩ : syracuseStep 4129433 = 3097075) B3097075
theorem B8258249 : Blo 1717059 8258249 := bstep (se 2 (by rfl) ⟨3096843, by rfl⟩ : syracuseStep 8258249 = 6193687) B6193687
theorem B3867407 : Blo 1717059 3867407 := bstep (se 1 (by rfl) ⟨2900555, by rfl⟩ : syracuseStep 3867407 = 5801111) B5801111
theorem B3867425 : Blo 1717059 3867425 := bstep (se 2 (by rfl) ⟨1450284, by rfl⟩ : syracuseStep 3867425 = 2900569) B2900569
theorem B3720055 : Blo 1717059 3720055 := bstep (se 1 (by rfl) ⟨2790041, by rfl⟩ : syracuseStep 3720055 = 5580083) B5580083
theorem B8700857 : Blo 1717059 8700857 := bstep (se 2 (by rfl) ⟨3262821, by rfl⟩ : syracuseStep 8700857 = 6525643) B6525643
theorem B4350905 : Blo 1717059 4350905 := bstep (se 2 (by rfl) ⟨1631589, by rfl⟩ : syracuseStep 4350905 = 3263179) B3263179
theorem B3261455 : Blo 1717059 3261455 := bstep (se 1 (by rfl) ⟨2446091, by rfl⟩ : syracuseStep 3261455 = 4892183) B4892183
theorem B4891681 : Blo 1717059 4891681 := bstep (se 2 (by rfl) ⟨1834380, by rfl⟩ : syracuseStep 4891681 = 3668761) B3668761
theorem B9782315 : Blo 1717059 9782315 := bstep (se 1 (by rfl) ⟨7336736, by rfl⟩ : syracuseStep 9782315 = 14673473) B14673473
theorem B5801003 : Blo 1717059 5801003 := bstep (se 1 (by rfl) ⟨4350752, by rfl⟩ : syracuseStep 5801003 = 8701505) B8701505
theorem B3867767 : Blo 1717059 3867767 := bstep (se 1 (by rfl) ⟨2900825, by rfl⟩ : syracuseStep 3867767 = 5801651) B5801651
theorem B3917071 : Blo 1717059 3917071 := bstep (se 1 (by rfl) ⟨2937803, by rfl⟩ : syracuseStep 3917071 = 5875607) B5875607
theorem B8693081 : Blo 1717059 8693081 := bstep (se 2 (by rfl) ⟨3259905, by rfl⟩ : syracuseStep 8693081 = 6519811) B6519811
theorem B6522227 : Blo 1717059 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B11011463 : Blo 1717059 11011463 := bstep (se 1 (by rfl) ⟨8258597, by rfl⟩ : syracuseStep 11011463 = 16517195) B16517195
theorem B4130201 : Blo 1717059 4130201 := bstep (se 2 (by rfl) ⟨1548825, by rfl⟩ : syracuseStep 4130201 = 3097651) B3097651
theorem B4130347 : Blo 1717059 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B13043267 : Blo 1717059 13043267 := bstep (se 1 (by rfl) ⟨9782450, by rfl⟩ : syracuseStep 13043267 = 19564901) B19564901
theorem B5506679 : Blo 1717059 5506679 := bstep (se 1 (by rfl) ⟨4130009, by rfl⟩ : syracuseStep 5506679 = 8260019) B8260019
theorem B9283265 : Blo 1717059 9283265 := bstep (se 2 (by rfl) ⟨3481224, by rfl⟩ : syracuseStep 9283265 = 6962449) B6962449
theorem B3483425 : Blo 1717059 3483425 := bstep (se 2 (by rfl) ⟨1306284, by rfl⟩ : syracuseStep 3483425 = 2612569) B2612569
theorem B19580939 : Blo 1717059 19580939 := bstep (se 1 (by rfl) ⟨14685704, by rfl⟩ : syracuseStep 19580939 = 29371409) B29371409
theorem B8702153 : Blo 1717059 8702153 := bstep (se 2 (by rfl) ⟨3263307, by rfl⟩ : syracuseStep 8702153 = 6526615) B6526615
theorem B2320655 : Blo 1717059 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B4892957 : Blo 1717059 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B11012537 : Blo 1717059 11012537 := bstep (se 2 (by rfl) ⟨4129701, by rfl⟩ : syracuseStep 11012537 = 8259403) B8259403
theorem B9783773 : Blo 1717059 9783773 := bstep (se 3 (by rfl) ⟨1834457, by rfl⟩ : syracuseStep 9783773 = 3668915) B3668915
theorem B4893185 : Blo 1717059 4893185 := bstep (se 2 (by rfl) ⟨1834944, by rfl⟩ : syracuseStep 4893185 = 3669889) B3669889
theorem B2173483 : Blo 1717059 2173483 := bstep (se 1 (by rfl) ⟨1630112, by rfl⟩ : syracuseStep 2173483 = 3260225) B3260225
theorem B6449707 : Blo 1717059 6449707 := bstep (se 1 (by rfl) ⟨4837280, by rfl⟩ : syracuseStep 6449707 = 9674561) B9674561
theorem B2320969 : Blo 1717059 2320969 := bstep (se 2 (by rfl) ⟨870363, by rfl⟩ : syracuseStep 2320969 = 1740727) B1740727
theorem B5294711 : Blo 1717059 5294711 := bstep (se 1 (by rfl) ⟨3971033, by rfl⟩ : syracuseStep 5294711 = 7942067) B7942067
theorem B3263095 : Blo 1717059 3263095 := bstep (se 1 (by rfl) ⟨2447321, by rfl⟩ : syracuseStep 3263095 = 4894643) B4894643
theorem B9292481 : Blo 1717059 9292481 := bstep (se 2 (by rfl) ⟨3484680, by rfl⟩ : syracuseStep 9292481 = 6969361) B6969361
theorem B8260289 : Blo 1717059 8260289 := bstep (se 2 (by rfl) ⟨3097608, by rfl⟩ : syracuseStep 8260289 = 6195217) B6195217
theorem B2173711 : Blo 1717059 2173711 := bstep (se 1 (by rfl) ⟨1630283, by rfl⟩ : syracuseStep 2173711 = 3260567) B3260567
theorem B4893527 : Blo 1717059 4893527 := bstep (se 1 (by rfl) ⟨3670145, by rfl⟩ : syracuseStep 4893527 = 7340291) B7340291
theorem B2321287 : Blo 1717059 2321287 := bstep (se 1 (by rfl) ⟨1740965, by rfl⟩ : syracuseStep 2321287 = 3481931) B3481931
theorem B4893641 : Blo 1717059 4893641 := bstep (se 2 (by rfl) ⟨1835115, by rfl⟩ : syracuseStep 4893641 = 3670231) B3670231
theorem B9784273 : Blo 1717059 9784273 := bstep (se 2 (by rfl) ⟨3669102, by rfl⟩ : syracuseStep 9784273 = 7338205) B7338205
theorem B9284651 : Blo 1717059 9284651 := bstep (se 1 (by rfl) ⟨6963488, by rfl⟩ : syracuseStep 9284651 = 13926977) B13926977
theorem B2321465 : Blo 1717059 2321465 := bstep (se 2 (by rfl) ⟨870549, by rfl⟩ : syracuseStep 2321465 = 1741099) B1741099
theorem B5024855 : Blo 1717059 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B14126167 : Blo 1717059 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B33025157 : Blo 1717059 33025157 := bstep (se 4 (by rfl) ⟨3096108, by rfl⟩ : syracuseStep 33025157 = 6192217) B6192217
theorem B2575607 : Blo 1717059 2575607 := bstep (se 1 (by rfl) ⟨1931705, by rfl⟩ : syracuseStep 2575607 = 3863411) B3863411
theorem B2575631 : Blo 1717059 2575631 := bstep (se 1 (by rfl) ⟨1931723, by rfl⟩ : syracuseStep 2575631 = 3863447) B3863447
theorem B17632529 : Blo 1717059 17632529 := bstep (se 2 (by rfl) ⟨6612198, by rfl⟩ : syracuseStep 17632529 = 13224397) B13224397
theorem B2575673 : Blo 1717059 2575673 := bstep (se 2 (by rfl) ⟨965877, by rfl⟩ : syracuseStep 2575673 = 1931755) B1931755
theorem B2575751 : Blo 1717059 2575751 := bstep (se 1 (by rfl) ⟨1931813, by rfl⟩ : syracuseStep 2575751 = 3863627) B3863627
theorem B8695187 : Blo 1717059 8695187 := bstep (se 1 (by rfl) ⟨6521390, by rfl⟩ : syracuseStep 8695187 = 13042781) B13042781
theorem B5795225 : Blo 1717059 5795225 := bstep (se 2 (by rfl) ⟨2173209, by rfl⟩ : syracuseStep 5795225 = 4346419) B4346419
theorem B2575787 : Blo 1717059 2575787 := bstep (se 1 (by rfl) ⟨1931840, by rfl⟩ : syracuseStep 2575787 = 3863681) B3863681
theorem B2575817 : Blo 1717059 2575817 := bstep (se 2 (by rfl) ⟨965931, by rfl⟩ : syracuseStep 2575817 = 1931863) B1931863
theorem B2174455 : Blo 1717059 2174455 := bstep (se 1 (by rfl) ⟨1630841, by rfl⟩ : syracuseStep 2174455 = 3261683) B3261683
theorem B6524459 : Blo 1717059 6524459 := bstep (se 1 (by rfl) ⟨4893344, by rfl⟩ : syracuseStep 6524459 = 9786689) B9786689
theorem B2575931 : Blo 1717059 2575931 := bstep (se 1 (by rfl) ⟨1931948, by rfl⟩ : syracuseStep 2575931 = 3863897) B3863897
theorem B2575991 : Blo 1717059 2575991 := bstep (se 1 (by rfl) ⟨1931993, by rfl⟩ : syracuseStep 2575991 = 3863987) B3863987
theorem B2576015 : Blo 1717059 2576015 := bstep (se 1 (by rfl) ⟨1932011, by rfl⟩ : syracuseStep 2576015 = 3864023) B3864023
theorem B2576057 : Blo 1717059 2576057 := bstep (se 2 (by rfl) ⟨966021, by rfl⟩ : syracuseStep 2576057 = 1932043) B1932043
theorem B2576135 : Blo 1717059 2576135 := bstep (se 1 (by rfl) ⟨1932101, by rfl⟩ : syracuseStep 2576135 = 3864203) B3864203
theorem B2576171 : Blo 1717059 2576171 := bstep (se 1 (by rfl) ⟨1932128, by rfl⟩ : syracuseStep 2576171 = 3864257) B3864257
theorem B2174779 : Blo 1717059 2174779 := bstep (se 1 (by rfl) ⟨1631084, by rfl⟩ : syracuseStep 2174779 = 3262169) B3262169
theorem B2576201 : Blo 1717059 2576201 := bstep (se 2 (by rfl) ⟨966075, by rfl⟩ : syracuseStep 2576201 = 1932151) B1932151
theorem B2576315 : Blo 1717059 2576315 := bstep (se 1 (by rfl) ⟨1932236, by rfl⟩ : syracuseStep 2576315 = 3864473) B3864473
theorem B12390347 : Blo 1717059 12390347 := bstep (se 1 (by rfl) ⟨9292760, by rfl⟩ : syracuseStep 12390347 = 18585521) B18585521
theorem B2576375 : Blo 1717059 2576375 := bstep (se 1 (by rfl) ⟨1932281, by rfl⟩ : syracuseStep 2576375 = 3864563) B3864563
theorem B4182031 : Blo 1717059 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B2576399 : Blo 1717059 2576399 := bstep (se 1 (by rfl) ⟨1932299, by rfl⟩ : syracuseStep 2576399 = 3864599) B3864599
theorem B3182635 : Blo 1717059 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B2576441 : Blo 1717059 2576441 := bstep (se 2 (by rfl) ⟨966165, by rfl⟩ : syracuseStep 2576441 = 1932331) B1932331
theorem B4706365 : Blo 1717059 4706365 := bstep (se 3 (by rfl) ⟨882443, by rfl⟩ : syracuseStep 4706365 = 1764887) B1764887
theorem B2445385 : Blo 1717059 2445385 := bstep (se 2 (by rfl) ⟨917019, by rfl⟩ : syracuseStep 2445385 = 1834039) B1834039
theorem B5795927 : Blo 1717059 5795927 := bstep (se 1 (by rfl) ⟨4346945, by rfl⟩ : syracuseStep 5795927 = 8693891) B8693891
theorem B5222519 : Blo 1717059 5222519 := bstep (se 1 (by rfl) ⟨3916889, by rfl⟩ : syracuseStep 5222519 = 7833779) B7833779
theorem B2576519 : Blo 1717059 2576519 := bstep (se 1 (by rfl) ⟨1932389, by rfl⟩ : syracuseStep 2576519 = 3864779) B3864779
theorem B2576555 : Blo 1717059 2576555 := bstep (se 1 (by rfl) ⟨1932416, by rfl⟩ : syracuseStep 2576555 = 3864833) B3864833
theorem B2445499 : Blo 1717059 2445499 := bstep (se 1 (by rfl) ⟨1834124, by rfl⟩ : syracuseStep 2445499 = 3668249) B3668249
theorem B2576585 : Blo 1717059 2576585 := bstep (se 2 (by rfl) ⟨966219, by rfl⟩ : syracuseStep 2576585 = 1932439) B1932439
theorem B8253677 : Blo 1717059 8253677 := bstep (se 3 (by rfl) ⟨1547564, by rfl⟩ : syracuseStep 8253677 = 3095129) B3095129
theorem B35754253 : Blo 1717059 35754253 := bstep (se 3 (by rfl) ⟨6703922, by rfl⟩ : syracuseStep 35754253 = 13407845) B13407845
theorem B2175275 : Blo 1717059 2175275 := bstep (se 1 (by rfl) ⟨1631456, by rfl⟩ : syracuseStep 2175275 = 3262913) B3262913
theorem B2576699 : Blo 1717059 2576699 := bstep (se 1 (by rfl) ⟨1932524, by rfl⟩ : syracuseStep 2576699 = 3865049) B3865049
theorem B2576759 : Blo 1717059 2576759 := bstep (se 1 (by rfl) ⟨1932569, by rfl⟩ : syracuseStep 2576759 = 3865139) B3865139
theorem B2576783 : Blo 1717059 2576783 := bstep (se 1 (by rfl) ⟨1932587, by rfl⟩ : syracuseStep 2576783 = 3865175) B3865175
theorem B18567569 : Blo 1717059 18567569 := bstep (se 2 (by rfl) ⟨6962838, by rfl⟩ : syracuseStep 18567569 = 13925677) B13925677
theorem B2576825 : Blo 1717059 2576825 := bstep (se 2 (by rfl) ⟨966309, by rfl⟩ : syracuseStep 2576825 = 1932619) B1932619
theorem B4346369 : Blo 1717059 4346369 := bstep (se 2 (by rfl) ⟨1629888, by rfl⟩ : syracuseStep 4346369 = 3259777) B3259777
theorem B2576903 : Blo 1717059 2576903 := bstep (se 1 (by rfl) ⟨1932677, by rfl⟩ : syracuseStep 2576903 = 3865355) B3865355
theorem B2576939 : Blo 1717059 2576939 := bstep (se 1 (by rfl) ⟨1932704, by rfl⟩ : syracuseStep 2576939 = 3865409) B3865409
theorem B38171179 : Blo 1717059 38171179 := bstep (se 1 (by rfl) ⟨28628384, by rfl⟩ : syracuseStep 38171179 = 57256769) B57256769
theorem B5796413 : Blo 1717059 5796413 := bstep (se 3 (by rfl) ⟨1086827, by rfl⟩ : syracuseStep 5796413 = 2173655) B2173655
theorem B2576969 : Blo 1717059 2576969 := bstep (se 2 (by rfl) ⟨966363, by rfl⟩ : syracuseStep 2576969 = 1932727) B1932727
theorem B4641395 : Blo 1717059 4641395 := bstep (se 1 (by rfl) ⟨3481046, by rfl⟩ : syracuseStep 4641395 = 6962093) B6962093
theorem B3920503 : Blo 1717059 3920503 := bstep (se 1 (by rfl) ⟨2940377, by rfl⟩ : syracuseStep 3920503 = 5880755) B5880755
theorem B2577083 : Blo 1717059 2577083 := bstep (se 1 (by rfl) ⟨1932812, by rfl⟩ : syracuseStep 2577083 = 3865625) B3865625
theorem B2577143 : Blo 1717059 2577143 := bstep (se 1 (by rfl) ⟨1932857, by rfl⟩ : syracuseStep 2577143 = 3865715) B3865715
theorem B2577167 : Blo 1717059 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B2577209 : Blo 1717059 2577209 := bstep (se 2 (by rfl) ⟨966453, by rfl⟩ : syracuseStep 2577209 = 1932907) B1932907
theorem B4346743 : Blo 1717059 4346743 := bstep (se 1 (by rfl) ⟨3260057, by rfl⟩ : syracuseStep 4346743 = 6520115) B6520115
theorem B1717127 : Blo 1717059 1717127 := bstep (se 1 (by rfl) ⟨1287845, by rfl⟩ : syracuseStep 1717127 = 2575691) B2575691
theorem B7836551 : Blo 1717059 7836551 := bstep (se 1 (by rfl) ⟨5877413, by rfl⟩ : syracuseStep 7836551 = 11754827) B11754827
theorem B2577287 : Blo 1717059 2577287 := bstep (se 1 (by rfl) ⟨1932965, by rfl⟩ : syracuseStep 2577287 = 3865931) B3865931
theorem B1717135 : Blo 1717059 1717135 := bstep (se 1 (by rfl) ⟨1287851, by rfl⟩ : syracuseStep 1717135 = 2575703) B2575703
theorem B9786257 : Blo 1717059 9786257 := bstep (se 2 (by rfl) ⟨3669846, by rfl⟩ : syracuseStep 9786257 = 7339693) B7339693
theorem B2577323 : Blo 1717059 2577323 := bstep (se 1 (by rfl) ⟨1932992, by rfl⟩ : syracuseStep 2577323 = 3865985) B3865985
theorem B1717179 : Blo 1717059 1717179 := bstep (se 1 (by rfl) ⟨1287884, by rfl⟩ : syracuseStep 1717179 = 2575769) B2575769
theorem B2577353 : Blo 1717059 2577353 := bstep (se 2 (by rfl) ⟨966507, by rfl⟩ : syracuseStep 2577353 = 1933015) B1933015
theorem B1717255 : Blo 1717059 1717255 := bstep (se 1 (by rfl) ⟨1287941, by rfl⟩ : syracuseStep 1717255 = 2575883) B2575883
theorem B1717263 : Blo 1717059 1717263 := bstep (se 1 (by rfl) ⟨1287947, by rfl⟩ : syracuseStep 1717263 = 2575895) B2575895
theorem B1717307 : Blo 1717059 1717307 := bstep (se 1 (by rfl) ⟨1287980, by rfl⟩ : syracuseStep 1717307 = 2575961) B2575961
theorem B2577467 : Blo 1717059 2577467 := bstep (se 1 (by rfl) ⟨1933100, by rfl⟩ : syracuseStep 2577467 = 3866201) B3866201
theorem B2577527 : Blo 1717059 2577527 := bstep (se 1 (by rfl) ⟨1933145, by rfl⟩ : syracuseStep 2577527 = 3866291) B3866291
theorem B1717383 : Blo 1717059 1717383 := bstep (se 1 (by rfl) ⟨1288037, by rfl⟩ : syracuseStep 1717383 = 2576075) B2576075
theorem B1717391 : Blo 1717059 1717391 := bstep (se 1 (by rfl) ⟨1288043, by rfl⟩ : syracuseStep 1717391 = 2576087) B2576087
theorem B2577551 : Blo 1717059 2577551 := bstep (se 1 (by rfl) ⟨1933163, by rfl⟩ : syracuseStep 2577551 = 3866327) B3866327
theorem B3863699 : Blo 1717059 3863699 := bstep (se 1 (by rfl) ⟨2897774, by rfl⟩ : syracuseStep 3863699 = 5795549) B5795549
theorem B2577593 : Blo 1717059 2577593 := bstep (se 2 (by rfl) ⟨966597, by rfl⟩ : syracuseStep 2577593 = 1933195) B1933195
theorem B1717435 : Blo 1717059 1717435 := bstep (se 1 (by rfl) ⟨1288076, by rfl⟩ : syracuseStep 1717435 = 2576153) B2576153
theorem B3863753 : Blo 1717059 3863753 := bstep (se 2 (by rfl) ⟨1448907, by rfl⟩ : syracuseStep 3863753 = 2897815) B2897815
theorem B19567817 : Blo 1717059 19567817 := bstep (se 2 (by rfl) ⟨7337931, by rfl⟩ : syracuseStep 19567817 = 14675863) B14675863
theorem B1717511 : Blo 1717059 1717511 := bstep (se 1 (by rfl) ⟨1288133, by rfl⟩ : syracuseStep 1717511 = 2576267) B2576267
theorem B2577671 : Blo 1717059 2577671 := bstep (se 1 (by rfl) ⟨1933253, by rfl⟩ : syracuseStep 2577671 = 3866507) B3866507
theorem B1717519 : Blo 1717059 1717519 := bstep (se 1 (by rfl) ⟨1288139, by rfl⟩ : syracuseStep 1717519 = 2576279) B2576279
theorem B2790671 : Blo 1717059 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B7337249 : Blo 1717059 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B4347179 : Blo 1717059 4347179 := bstep (se 1 (by rfl) ⟨3260384, by rfl⟩ : syracuseStep 4347179 = 6520769) B6520769
theorem B2577707 : Blo 1717059 2577707 := bstep (se 1 (by rfl) ⟨1933280, by rfl⟩ : syracuseStep 2577707 = 3866561) B3866561
theorem B1717563 : Blo 1717059 1717563 := bstep (se 1 (by rfl) ⟨1288172, by rfl⟩ : syracuseStep 1717563 = 2576345) B2576345
theorem B2577737 : Blo 1717059 2577737 := bstep (se 2 (by rfl) ⟨966651, by rfl⟩ : syracuseStep 2577737 = 1933303) B1933303
theorem B1717639 : Blo 1717059 1717639 := bstep (se 1 (by rfl) ⟨1288229, by rfl⟩ : syracuseStep 1717639 = 2576459) B2576459
theorem B1717647 : Blo 1717059 1717647 := bstep (se 1 (by rfl) ⟨1288235, by rfl⟩ : syracuseStep 1717647 = 2576471) B2576471
theorem B1717691 : Blo 1717059 1717691 := bstep (se 1 (by rfl) ⟨1288268, by rfl⟩ : syracuseStep 1717691 = 2576537) B2576537
theorem B2577851 : Blo 1717059 2577851 := bstep (se 1 (by rfl) ⟨1933388, by rfl⟩ : syracuseStep 2577851 = 3866777) B3866777
theorem B2577911 : Blo 1717059 2577911 := bstep (se 1 (by rfl) ⟨1933433, by rfl⟩ : syracuseStep 2577911 = 3866867) B3866867
theorem B1717767 : Blo 1717059 1717767 := bstep (se 1 (by rfl) ⟨1288325, by rfl⟩ : syracuseStep 1717767 = 2576651) B2576651
theorem B66016781 : Blo 1717059 66016781 := bstep (se 3 (by rfl) ⟨12378146, by rfl⟩ : syracuseStep 66016781 = 24756293) B24756293
theorem B1717775 : Blo 1717059 1717775 := bstep (se 1 (by rfl) ⟨1288331, by rfl⟩ : syracuseStep 1717775 = 2576663) B2576663
theorem B2577935 : Blo 1717059 2577935 := bstep (se 1 (by rfl) ⟨1933451, by rfl⟩ : syracuseStep 2577935 = 3866903) B3866903
theorem B2577977 : Blo 1717059 2577977 := bstep (se 2 (by rfl) ⟨966741, by rfl⟩ : syracuseStep 2577977 = 1933483) B1933483
theorem B1717819 : Blo 1717059 1717819 := bstep (se 1 (by rfl) ⟨1288364, by rfl⟩ : syracuseStep 1717819 = 2576729) B2576729
theorem B20903501 : Blo 1717059 20903501 := bstep (se 3 (by rfl) ⟨3919406, by rfl⟩ : syracuseStep 20903501 = 7838813) B7838813
theorem B7337591 : Blo 1717059 7337591 := bstep (se 1 (by rfl) ⟨5503193, by rfl⟩ : syracuseStep 7337591 = 11006387) B11006387
theorem B1717895 : Blo 1717059 1717895 := bstep (se 1 (by rfl) ⟨1288421, by rfl⟩ : syracuseStep 1717895 = 2576843) B2576843
theorem B2578055 : Blo 1717059 2578055 := bstep (se 1 (by rfl) ⟨1933541, by rfl⟩ : syracuseStep 2578055 = 3867083) B3867083
theorem B1717903 : Blo 1717059 1717903 := bstep (se 1 (by rfl) ⟨1288427, by rfl⟩ : syracuseStep 1717903 = 2576855) B2576855
theorem B2578091 : Blo 1717059 2578091 := bstep (se 1 (by rfl) ⟨1933568, by rfl⟩ : syracuseStep 2578091 = 3867137) B3867137
theorem B1717947 : Blo 1717059 1717947 := bstep (se 1 (by rfl) ⟨1288460, by rfl⟩ : syracuseStep 1717947 = 2576921) B2576921
theorem B2578121 : Blo 1717059 2578121 := bstep (se 2 (by rfl) ⟨966795, by rfl⟩ : syracuseStep 2578121 = 1933591) B1933591
theorem B1718023 : Blo 1717059 1718023 := bstep (se 1 (by rfl) ⟨1288517, by rfl⟩ : syracuseStep 1718023 = 2577035) B2577035
theorem B2447111 : Blo 1717059 2447111 := bstep (se 1 (by rfl) ⟨1835333, by rfl⟩ : syracuseStep 2447111 = 3670667) B3670667
theorem B1718031 : Blo 1717059 1718031 := bstep (se 1 (by rfl) ⟨1288523, by rfl⟩ : syracuseStep 1718031 = 2577047) B2577047
theorem B2897707 : Blo 1717059 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B1718075 : Blo 1717059 1718075 := bstep (se 1 (by rfl) ⟨1288556, by rfl⟩ : syracuseStep 1718075 = 2577113) B2577113
theorem B2578235 : Blo 1717059 2578235 := bstep (se 1 (by rfl) ⟨1933676, by rfl⟩ : syracuseStep 2578235 = 3867353) B3867353
theorem B13047641 : Blo 1717059 13047641 := bstep (se 2 (by rfl) ⟨4892865, by rfl⟩ : syracuseStep 13047641 = 9785731) B9785731
theorem B2578295 : Blo 1717059 2578295 := bstep (se 1 (by rfl) ⟨1933721, by rfl⟩ : syracuseStep 2578295 = 3867443) B3867443
theorem B3864455 : Blo 1717059 3864455 := bstep (se 1 (by rfl) ⟨2898341, by rfl⟩ : syracuseStep 3864455 = 5796683) B5796683
theorem B1718151 : Blo 1717059 1718151 := bstep (se 1 (by rfl) ⟨1288613, by rfl⟩ : syracuseStep 1718151 = 2577227) B2577227
theorem B1718159 : Blo 1717059 1718159 := bstep (se 1 (by rfl) ⟨1288619, by rfl⟩ : syracuseStep 1718159 = 2577239) B2577239
theorem B2578319 : Blo 1717059 2578319 := bstep (se 1 (by rfl) ⟨1933739, by rfl⟩ : syracuseStep 2578319 = 3867479) B3867479
theorem B2897849 : Blo 1717059 2897849 := bstep (se 2 (by rfl) ⟨1086693, by rfl⟩ : syracuseStep 2897849 = 2173387) B2173387
theorem B5797817 : Blo 1717059 5797817 := bstep (se 2 (by rfl) ⟨2174181, by rfl⟩ : syracuseStep 5797817 = 4348363) B4348363
theorem B1718203 : Blo 1717059 1718203 := bstep (se 1 (by rfl) ⟨1288652, by rfl⟩ : syracuseStep 1718203 = 2577305) B2577305
theorem B2578361 : Blo 1717059 2578361 := bstep (se 2 (by rfl) ⟨966885, by rfl⟩ : syracuseStep 2578361 = 1933771) B1933771
theorem B1718279 : Blo 1717059 1718279 := bstep (se 1 (by rfl) ⟨1288709, by rfl⟩ : syracuseStep 1718279 = 2577419) B2577419
theorem B2578439 : Blo 1717059 2578439 := bstep (se 1 (by rfl) ⟨1933829, by rfl⟩ : syracuseStep 2578439 = 3867659) B3867659
theorem B1718287 : Blo 1717059 1718287 := bstep (se 1 (by rfl) ⟨1288715, by rfl⟩ : syracuseStep 1718287 = 2577431) B2577431
theorem B2578475 : Blo 1717059 2578475 := bstep (se 1 (by rfl) ⟨1933856, by rfl⟩ : syracuseStep 2578475 = 3867713) B3867713
theorem B3864635 : Blo 1717059 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B1718331 : Blo 1717059 1718331 := bstep (se 1 (by rfl) ⟨1288748, by rfl⟩ : syracuseStep 1718331 = 2577497) B2577497
theorem B2611273 : Blo 1717059 2611273 := bstep (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) B1958455
theorem B2578505 : Blo 1717059 2578505 := bstep (se 2 (by rfl) ⟨966939, by rfl⟩ : syracuseStep 2578505 = 1933879) B1933879
theorem B4348019 : Blo 1717059 4348019 := bstep (se 1 (by rfl) ⟨3261014, by rfl⟩ : syracuseStep 4348019 = 6522029) B6522029
theorem B4348039 : Blo 1717059 4348039 := bstep (se 1 (by rfl) ⟨3261029, by rfl⟩ : syracuseStep 4348039 = 6522059) B6522059
theorem B1718407 : Blo 1717059 1718407 := bstep (se 1 (by rfl) ⟨1288805, by rfl⟩ : syracuseStep 1718407 = 2577611) B2577611
theorem B1718415 : Blo 1717059 1718415 := bstep (se 1 (by rfl) ⟨1288811, by rfl⟩ : syracuseStep 1718415 = 2577623) B2577623
theorem B3864761 : Blo 1717059 3864761 := bstep (se 2 (by rfl) ⟨1449285, by rfl⟩ : syracuseStep 3864761 = 2898571) B2898571
theorem B1718459 : Blo 1717059 1718459 := bstep (se 1 (by rfl) ⟨1288844, by rfl⟩ : syracuseStep 1718459 = 2577689) B2577689
theorem B1718535 : Blo 1717059 1718535 := bstep (se 1 (by rfl) ⟨1288901, by rfl⟩ : syracuseStep 1718535 = 2577803) B2577803
theorem B1718543 : Blo 1717059 1718543 := bstep (se 1 (by rfl) ⟨1288907, by rfl⟩ : syracuseStep 1718543 = 2577815) B2577815
theorem B1718587 : Blo 1717059 1718587 := bstep (se 1 (by rfl) ⟨1288940, by rfl⟩ : syracuseStep 1718587 = 2577881) B2577881
theorem B1718663 : Blo 1717059 1718663 := bstep (se 1 (by rfl) ⟨1288997, by rfl⟩ : syracuseStep 1718663 = 2577995) B2577995
theorem B1718671 : Blo 1717059 1718671 := bstep (se 1 (by rfl) ⟨1289003, by rfl⟩ : syracuseStep 1718671 = 2578007) B2578007
theorem B4348313 : Blo 1717059 4348313 := bstep (se 2 (by rfl) ⟨1630617, by rfl⟩ : syracuseStep 4348313 = 3261235) B3261235
theorem B8698265 : Blo 1717059 8698265 := bstep (se 2 (by rfl) ⟨3261849, by rfl⟩ : syracuseStep 8698265 = 6523699) B6523699
theorem B3971513 : Blo 1717059 3971513 := bstep (se 2 (by rfl) ⟨1489317, by rfl⟩ : syracuseStep 3971513 = 2978635) B2978635
theorem B1718715 : Blo 1717059 1718715 := bstep (se 1 (by rfl) ⟨1289036, by rfl⟩ : syracuseStep 1718715 = 2578073) B2578073
theorem B1718791 : Blo 1717059 1718791 := bstep (se 1 (by rfl) ⟨1289093, by rfl⟩ : syracuseStep 1718791 = 2578187) B2578187
theorem B5798411 : Blo 1717059 5798411 := bstep (se 1 (by rfl) ⟨4348808, by rfl⟩ : syracuseStep 5798411 = 8697617) B8697617
theorem B1931791 : Blo 1717059 1931791 := bstep (se 1 (by rfl) ⟨1448843, by rfl⟩ : syracuseStep 1931791 = 2897687) B2897687
theorem B3865103 : Blo 1717059 3865103 := bstep (se 1 (by rfl) ⟨2898827, by rfl⟩ : syracuseStep 3865103 = 5797655) B5797655
theorem B1718799 : Blo 1717059 1718799 := bstep (se 1 (by rfl) ⟨1289099, by rfl⟩ : syracuseStep 1718799 = 2578199) B2578199
theorem B3865121 : Blo 1717059 3865121 := bstep (se 2 (by rfl) ⟨1449420, by rfl⟩ : syracuseStep 3865121 = 2898841) B2898841
theorem B4348475 : Blo 1717059 4348475 := bstep (se 1 (by rfl) ⟨3261356, by rfl⟩ : syracuseStep 4348475 = 6522713) B6522713
theorem B1718843 : Blo 1717059 1718843 := bstep (se 1 (by rfl) ⟨1289132, by rfl⟩ : syracuseStep 1718843 = 2578265) B2578265
theorem B2898551 : Blo 1717059 2898551 := bstep (se 1 (by rfl) ⟨2173913, by rfl⟩ : syracuseStep 2898551 = 4347827) B4347827
theorem B5798519 : Blo 1717059 5798519 := bstep (se 1 (by rfl) ⟨4348889, by rfl⟩ : syracuseStep 5798519 = 8697779) B8697779
theorem B1718919 : Blo 1717059 1718919 := bstep (se 1 (by rfl) ⟨1289189, by rfl⟩ : syracuseStep 1718919 = 2578379) B2578379
theorem B1718927 : Blo 1717059 1718927 := bstep (se 1 (by rfl) ⟨1289195, by rfl⟩ : syracuseStep 1718927 = 2578391) B2578391
theorem B1718971 : Blo 1717059 1718971 := bstep (se 1 (by rfl) ⟨1289228, by rfl⟩ : syracuseStep 1718971 = 2578457) B2578457
theorem B1719047 : Blo 1717059 1719047 := bstep (se 1 (by rfl) ⟨1289285, by rfl⟩ : syracuseStep 1719047 = 2578571) B2578571
theorem B4348687 : Blo 1717059 4348687 := bstep (se 1 (by rfl) ⟨3261515, by rfl⟩ : syracuseStep 4348687 = 6523031) B6523031
theorem B1719055 : Blo 1717059 1719055 := bstep (se 1 (by rfl) ⟨1289291, by rfl⟩ : syracuseStep 1719055 = 2578583) B2578583
theorem B13048613 : Blo 1717059 13048613 := bstep (se 4 (by rfl) ⟨1223307, by rfl⟩ : syracuseStep 13048613 = 2446615) B2446615
theorem B8813371 : Blo 1717059 8813371 := bstep (se 1 (by rfl) ⟨6610028, by rfl⟩ : syracuseStep 8813371 = 13220057) B13220057
theorem B3865463 : Blo 1717059 3865463 := bstep (se 1 (by rfl) ⟨2899097, by rfl⟩ : syracuseStep 3865463 = 5798195) B5798195
theorem B20904965 : Blo 1717059 20904965 := bstep (se 4 (by rfl) ⟨1959840, by rfl⟩ : syracuseStep 20904965 = 3919681) B3919681
theorem B1932295 : Blo 1717059 1932295 := bstep (se 1 (by rfl) ⟨1449221, by rfl⟩ : syracuseStep 1932295 = 2898443) B2898443
theorem B14883851 : Blo 1717059 14883851 := bstep (se 1 (by rfl) ⟨11162888, by rfl⟩ : syracuseStep 14883851 = 22325777) B22325777
theorem B4348961 : Blo 1717059 4348961 := bstep (se 2 (by rfl) ⟨1630860, by rfl⟩ : syracuseStep 4348961 = 3261721) B3261721
theorem B3865643 : Blo 1717059 3865643 := bstep (se 1 (by rfl) ⟨2899232, by rfl⟩ : syracuseStep 3865643 = 5798465) B5798465
theorem B2899003 : Blo 1717059 2899003 := bstep (se 1 (by rfl) ⟨2174252, by rfl⟩ : syracuseStep 2899003 = 4348505) B4348505
theorem B8256599 : Blo 1717059 8256599 := bstep (se 1 (by rfl) ⟨6192449, by rfl⟩ : syracuseStep 8256599 = 12384899) B12384899
theorem B6192247 : Blo 1717059 6192247 := bstep (se 1 (by rfl) ⟨4644185, by rfl⟩ : syracuseStep 6192247 = 9288371) B9288371
theorem B41819267 : Blo 1717059 41819267 := bstep (se 1 (by rfl) ⟨31364450, by rfl⟩ : syracuseStep 41819267 = 62728901) B62728901
theorem B1932475 : Blo 1717059 1932475 := bstep (se 1 (by rfl) ⟨1449356, by rfl⟩ : syracuseStep 1932475 = 2898713) B2898713
theorem B9780425 : Blo 1717059 9780425 := bstep (se 2 (by rfl) ⟨3667659, by rfl⟩ : syracuseStep 9780425 = 7335319) B7335319
theorem B2899145 : Blo 1717059 2899145 := bstep (se 2 (by rfl) ⟨1087179, by rfl⟩ : syracuseStep 2899145 = 2174359) B2174359
theorem B5799113 : Blo 1717059 5799113 := bstep (se 2 (by rfl) ⟨2174667, by rfl⟩ : syracuseStep 5799113 = 4349335) B4349335
theorem B10452239 : Blo 1717059 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B3866003 : Blo 1717059 3866003 := bstep (se 1 (by rfl) ⟨2899502, by rfl⟩ : syracuseStep 3866003 = 5799005) B5799005
theorem B4890041 : Blo 1717059 4890041 := bstep (se 2 (by rfl) ⟨1833765, by rfl⟩ : syracuseStep 4890041 = 3667531) B3667531
theorem B3866057 : Blo 1717059 3866057 := bstep (se 2 (by rfl) ⟨1449771, by rfl⟩ : syracuseStep 3866057 = 2899543) B2899543
theorem B1932943 : Blo 1717059 1932943 := bstep (se 1 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 1932943 = 2899415) B2899415
theorem B2752391 : Blo 1717059 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B2899847 : Blo 1717059 2899847 := bstep (se 1 (by rfl) ⟨2174885, by rfl⟩ : syracuseStep 2899847 = 4349771) B4349771
theorem B5799815 : Blo 1717059 5799815 := bstep (se 1 (by rfl) ⟨4349861, by rfl⟩ : syracuseStep 5799815 = 8699723) B8699723
theorem B10444697 : Blo 1717059 10444697 := bstep (se 2 (by rfl) ⟨3916761, by rfl⟩ : syracuseStep 10444697 = 7833523) B7833523
theorem B10444747 : Blo 1717059 10444747 := bstep (se 1 (by rfl) ⟨7833560, by rfl⟩ : syracuseStep 10444747 = 15667121) B15667121
theorem B2899975 : Blo 1717059 2899975 := bstep (se 1 (by rfl) ⟨2174981, by rfl⟩ : syracuseStep 2899975 = 4349963) B4349963
theorem B11010077 : Blo 1717059 11010077 := bstep (se 3 (by rfl) ⟨2064389, by rfl⟩ : syracuseStep 11010077 = 4128779) B4128779
theorem B4243513 : Blo 1717059 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B3481679 : Blo 1717059 3481679 := bstep (se 1 (by rfl) ⟨2611259, by rfl⟩ : syracuseStep 3481679 = 5222519) B5222519
theorem B6275153 : Blo 1717059 6275153 := bstep (se 2 (by rfl) ⟨2353182, by rfl⟩ : syracuseStep 6275153 = 4706365) B4706365
theorem B3481697 : Blo 1717059 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B3260513 : Blo 1717059 3260513 := bstep (se 2 (by rfl) ⟨1222692, by rfl⟩ : syracuseStep 3260513 = 2445385) B2445385
theorem B3866795 : Blo 1717059 3866795 := bstep (se 1 (by rfl) ⟨2900096, by rfl⟩ : syracuseStep 3866795 = 5800193) B5800193
theorem B3096787 : Blo 1717059 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B3260665 : Blo 1717059 3260665 := bstep (se 2 (by rfl) ⟨1222749, by rfl⟩ : syracuseStep 3260665 = 2445499) B2445499
theorem B12378379 : Blo 1717059 12378379 := bstep (se 1 (by rfl) ⟨9283784, by rfl⟩ : syracuseStep 12378379 = 18567569) B18567569
theorem B1933663 : Blo 1717059 1933663 := bstep (se 1 (by rfl) ⟨1450247, by rfl⟩ : syracuseStep 1933663 = 2900495) B2900495
theorem B2900407 : Blo 1717059 2900407 := bstep (se 1 (by rfl) ⟨2175305, by rfl⟩ : syracuseStep 2900407 = 4350611) B4350611
theorem B2752955 : Blo 1717059 2752955 := bstep (se 1 (by rfl) ⟨2064716, by rfl⟩ : syracuseStep 2752955 = 4129433) B4129433
theorem B5505499 : Blo 1717059 5505499 := bstep (se 1 (by rfl) ⟨4129124, by rfl⟩ : syracuseStep 5505499 = 8258249) B8258249
theorem B5800571 : Blo 1717059 5800571 := bstep (se 1 (by rfl) ⟨4350428, by rfl⟩ : syracuseStep 5800571 = 8700857) B8700857
theorem B2900603 : Blo 1717059 2900603 := bstep (se 1 (by rfl) ⟨2175452, by rfl⟩ : syracuseStep 2900603 = 4350905) B4350905
theorem B8258233 : Blo 1717059 8258233 := bstep (se 2 (by rfl) ⟨3096837, by rfl⟩ : syracuseStep 8258233 = 6193675) B6193675
theorem B6521543 : Blo 1717059 6521543 := bstep (se 1 (by rfl) ⟨4891157, by rfl⟩ : syracuseStep 6521543 = 9782315) B9782315
theorem B3867335 : Blo 1717059 3867335 := bstep (se 1 (by rfl) ⟨2900501, by rfl⟩ : syracuseStep 3867335 = 5801003) B5801003
theorem B5800733 : Blo 1717059 5800733 := bstep (se 3 (by rfl) ⟨1087637, by rfl⟩ : syracuseStep 5800733 = 2175275) B2175275
theorem B4350793 : Blo 1717059 4350793 := bstep (se 2 (by rfl) ⟨1631547, by rfl⟩ : syracuseStep 4350793 = 3263095) B3263095
theorem B5227337 : Blo 1717059 5227337 := bstep (se 2 (by rfl) ⟨1960251, by rfl⟩ : syracuseStep 5227337 = 3920503) B3920503
theorem B4891499 : Blo 1717059 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B7340975 : Blo 1717059 7340975 := bstep (se 1 (by rfl) ⟨5505731, by rfl⟩ : syracuseStep 7340975 = 11011463) B11011463
theorem B13935667 : Blo 1717059 13935667 := bstep (se 1 (by rfl) ⟨10451750, by rfl⟩ : syracuseStep 13935667 = 20903501) B20903501
theorem B4891727 : Blo 1717059 4891727 := bstep (se 1 (by rfl) ⟨3668795, by rfl⟩ : syracuseStep 4891727 = 7337591) B7337591
theorem B3671119 : Blo 1717059 3671119 := bstep (se 1 (by rfl) ⟨2753339, by rfl⟩ : syracuseStep 3671119 = 5506679) B5506679
theorem B6522241 : Blo 1717059 6522241 := bstep (se 2 (by rfl) ⟨2445840, by rfl⟩ : syracuseStep 6522241 = 4891681) B4891681
theorem B18834889 : Blo 1717059 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B5801435 : Blo 1717059 5801435 := bstep (se 1 (by rfl) ⟨4351076, by rfl⟩ : syracuseStep 5801435 = 8702153) B8702153
theorem B3261971 : Blo 1717059 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B2647675 : Blo 1717059 2647675 := bstep (se 1 (by rfl) ⟨1985756, by rfl⟩ : syracuseStep 2647675 = 3971513) B3971513
theorem B7341691 : Blo 1717059 7341691 := bstep (se 1 (by rfl) ⟨5506268, by rfl⟩ : syracuseStep 7341691 = 11012537) B11012537
theorem B6522515 : Blo 1717059 6522515 := bstep (se 1 (by rfl) ⟨4891886, by rfl⟩ : syracuseStep 6522515 = 9783773) B9783773
theorem B3262123 : Blo 1717059 3262123 := bstep (se 1 (by rfl) ⟨2446592, by rfl⟩ : syracuseStep 3262123 = 4893185) B4893185
theorem B6194987 : Blo 1717059 6194987 := bstep (se 1 (by rfl) ⟨4646240, by rfl⟩ : syracuseStep 6194987 = 9292481) B9292481
theorem B5506859 : Blo 1717059 5506859 := bstep (se 1 (by rfl) ⟨4130144, by rfl⟩ : syracuseStep 5506859 = 8260289) B8260289
theorem B3262351 : Blo 1717059 3262351 := bstep (se 1 (by rfl) ⟨2446763, by rfl⟩ : syracuseStep 3262351 = 4893527) B4893527
theorem B3262427 : Blo 1717059 3262427 := bstep (se 1 (by rfl) ⟨2446820, by rfl⟩ : syracuseStep 3262427 = 4893641) B4893641
theorem B13936643 : Blo 1717059 13936643 := bstep (se 1 (by rfl) ⟨10452482, by rfl⟩ : syracuseStep 13936643 = 20904965) B20904965
theorem B9922567 : Blo 1717059 9922567 := bstep (se 1 (by rfl) ⟨7441925, by rfl⟩ : syracuseStep 9922567 = 14883851) B14883851
theorem B12380197 : Blo 1717059 12380197 := bstep (se 4 (by rfl) ⟨1160643, by rfl⟩ : syracuseStep 12380197 = 2321287) B2321287
theorem B5507129 : Blo 1717059 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B27879511 : Blo 1717059 27879511 := bstep (se 1 (by rfl) ⟨20909633, by rfl⟩ : syracuseStep 27879511 = 41819267) B41819267
theorem B8260231 : Blo 1717059 8260231 := bstep (se 1 (by rfl) ⟨6195173, by rfl⟩ : syracuseStep 8260231 = 12390347) B12390347
theorem B19573649 : Blo 1717059 19573649 := bstep (se 2 (by rfl) ⟨7340118, by rfl⟩ : syracuseStep 19573649 = 14680237) B14680237
theorem B8694863 : Blo 1717059 8694863 := bstep (se 1 (by rfl) ⟨6521147, by rfl⟩ : syracuseStep 8694863 = 13042295) B13042295
theorem B6524171 : Blo 1717059 6524171 := bstep (se 1 (by rfl) ⟨4893128, by rfl⟩ : syracuseStep 6524171 = 9786257) B9786257
theorem B2174303 : Blo 1717059 2174303 := bstep (se 1 (by rfl) ⟨1630727, by rfl⟩ : syracuseStep 2174303 = 3261455) B3261455
theorem B2575721 : Blo 1717059 2575721 := bstep (se 2 (by rfl) ⟨965895, by rfl⟩ : syracuseStep 2575721 = 1931791) B1931791
theorem B6188413 : Blo 1717059 6188413 := bstep (se 3 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 6188413 = 2320655) B2320655
theorem B7441789 : Blo 1717059 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B2575799 : Blo 1717059 2575799 := bstep (se 1 (by rfl) ⟨1931849, by rfl⟩ : syracuseStep 2575799 = 3863699) B3863699
theorem B2575835 : Blo 1717059 2575835 := bstep (se 1 (by rfl) ⟨1931876, by rfl⟩ : syracuseStep 2575835 = 3863753) B3863753
theorem B13045211 : Blo 1717059 13045211 := bstep (se 1 (by rfl) ⟨9783908, by rfl⟩ : syracuseStep 13045211 = 19567817) B19567817
theorem B5795387 : Blo 1717059 5795387 := bstep (se 1 (by rfl) ⟨4346540, by rfl⟩ : syracuseStep 5795387 = 8693081) B8693081
theorem B44011187 : Blo 1717059 44011187 := bstep (se 1 (by rfl) ⟨33008390, by rfl⟩ : syracuseStep 44011187 = 66016781) B66016781
theorem B8695511 : Blo 1717059 8695511 := bstep (se 1 (by rfl) ⟨6521633, by rfl⟩ : syracuseStep 8695511 = 13043267) B13043267
theorem B11013869 : Blo 1717059 11013869 := bstep (se 3 (by rfl) ⟨2065100, by rfl⟩ : syracuseStep 11013869 = 4130201) B4130201
theorem B11751161 : Blo 1717059 11751161 := bstep (se 2 (by rfl) ⟨4406685, by rfl⟩ : syracuseStep 11751161 = 8813371) B8813371
theorem B6188843 : Blo 1717059 6188843 := bstep (se 1 (by rfl) ⟨4641632, by rfl⟩ : syracuseStep 6188843 = 9283265) B9283265
theorem B5795657 : Blo 1717059 5795657 := bstep (se 2 (by rfl) ⟨2173371, by rfl⟩ : syracuseStep 5795657 = 4346743) B4346743
theorem B4960073 : Blo 1717059 4960073 := bstep (se 2 (by rfl) ⟨1860027, by rfl⟩ : syracuseStep 4960073 = 3720055) B3720055
theorem B2322283 : Blo 1717059 2322283 := bstep (se 1 (by rfl) ⟨1741712, by rfl⟩ : syracuseStep 2322283 = 3483425) B3483425
theorem B2576303 : Blo 1717059 2576303 := bstep (se 1 (by rfl) ⟨1932227, by rfl⟩ : syracuseStep 2576303 = 3864455) B3864455
theorem B13045697 : Blo 1717059 13045697 := bstep (se 2 (by rfl) ⟨4892136, by rfl⟩ : syracuseStep 13045697 = 9784273) B9784273
theorem B13053959 : Blo 1717059 13053959 := bstep (se 1 (by rfl) ⟨9790469, by rfl⟩ : syracuseStep 13053959 = 19580939) B19580939
theorem B2576393 : Blo 1717059 2576393 := bstep (se 2 (by rfl) ⟨966147, by rfl⟩ : syracuseStep 2576393 = 1932295) B1932295
theorem B2576423 : Blo 1717059 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B190689349 : Blo 1717059 190689349 := bstep (se 4 (by rfl) ⟨17877126, by rfl⟩ : syracuseStep 190689349 = 35754253) B35754253
theorem B2576507 : Blo 1717059 2576507 := bstep (se 1 (by rfl) ⟨1932380, by rfl⟩ : syracuseStep 2576507 = 3864761) B3864761
theorem B2576633 : Blo 1717059 2576633 := bstep (se 2 (by rfl) ⟨966237, by rfl⟩ : syracuseStep 2576633 = 1932475) B1932475
theorem B2576735 : Blo 1717059 2576735 := bstep (se 1 (by rfl) ⟨1932551, by rfl⟩ : syracuseStep 2576735 = 3865103) B3865103
theorem B5222761 : Blo 1717059 5222761 := bstep (se 2 (by rfl) ⟨1958535, by rfl⟩ : syracuseStep 5222761 = 3917071) B3917071
theorem B2576747 : Blo 1717059 2576747 := bstep (se 1 (by rfl) ⟨1932560, by rfl⟩ : syracuseStep 2576747 = 3865121) B3865121
theorem B2576975 : Blo 1717059 2576975 := bstep (se 1 (by rfl) ⟨1932731, by rfl⟩ : syracuseStep 2576975 = 3865463) B3865463
theorem B6525629 : Blo 1717059 6525629 := bstep (se 3 (by rfl) ⟨1223555, by rfl⟩ : syracuseStep 6525629 = 2447111) B2447111
theorem B6189767 : Blo 1717059 6189767 := bstep (se 1 (by rfl) ⟨4642325, by rfl⟩ : syracuseStep 6189767 = 9284651) B9284651
theorem B2577095 : Blo 1717059 2577095 := bstep (se 1 (by rfl) ⟨1932821, by rfl⟩ : syracuseStep 2577095 = 3865643) B3865643
theorem B22016771 : Blo 1717059 22016771 := bstep (se 1 (by rfl) ⟨16512578, by rfl⟩ : syracuseStep 22016771 = 33025157) B33025157
theorem B1717071 : Blo 1717059 1717071 := bstep (se 1 (by rfl) ⟨1287803, by rfl⟩ : syracuseStep 1717071 = 2575607) B2575607
theorem B1717087 : Blo 1717059 1717087 := bstep (se 1 (by rfl) ⟨1287815, by rfl⟩ : syracuseStep 1717087 = 2575631) B2575631
theorem B6968159 : Blo 1717059 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B2577257 : Blo 1717059 2577257 := bstep (se 2 (by rfl) ⟨966471, by rfl⟩ : syracuseStep 2577257 = 1932943) B1932943
theorem B1717115 : Blo 1717059 1717115 := bstep (se 1 (by rfl) ⟨1287836, by rfl⟩ : syracuseStep 1717115 = 2575673) B2575673
theorem B1717167 : Blo 1717059 1717167 := bstep (se 1 (by rfl) ⟨1287875, by rfl⟩ : syracuseStep 1717167 = 2575751) B2575751
theorem B5796791 : Blo 1717059 5796791 := bstep (se 1 (by rfl) ⟨4347593, by rfl⟩ : syracuseStep 5796791 = 8695187) B8695187
theorem B2577335 : Blo 1717059 2577335 := bstep (se 1 (by rfl) ⟨1933001, by rfl⟩ : syracuseStep 2577335 = 3866003) B3866003
theorem B3863483 : Blo 1717059 3863483 := bstep (se 1 (by rfl) ⟨2897612, by rfl⟩ : syracuseStep 3863483 = 5795225) B5795225
theorem B1717191 : Blo 1717059 1717191 := bstep (se 1 (by rfl) ⟨1287893, by rfl⟩ : syracuseStep 1717191 = 2575787) B2575787
theorem B1717211 : Blo 1717059 1717211 := bstep (se 1 (by rfl) ⟨1287908, by rfl⟩ : syracuseStep 1717211 = 2575817) B2575817
theorem B2577371 : Blo 1717059 2577371 := bstep (se 1 (by rfl) ⟨1933028, by rfl⟩ : syracuseStep 2577371 = 3866057) B3866057
theorem B1717287 : Blo 1717059 1717287 := bstep (se 1 (by rfl) ⟨1287965, by rfl⟩ : syracuseStep 1717287 = 2575931) B2575931
theorem B3863609 : Blo 1717059 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B1717327 : Blo 1717059 1717327 := bstep (se 1 (by rfl) ⟨1287995, by rfl⟩ : syracuseStep 1717327 = 2575991) B2575991
theorem B1717343 : Blo 1717059 1717343 := bstep (se 1 (by rfl) ⟨1288007, by rfl⟩ : syracuseStep 1717343 = 2576015) B2576015
theorem B1717371 : Blo 1717059 1717371 := bstep (se 1 (by rfl) ⟨1288028, by rfl⟩ : syracuseStep 1717371 = 2576057) B2576057
theorem B1717423 : Blo 1717059 1717423 := bstep (se 1 (by rfl) ⟨1288067, by rfl⟩ : syracuseStep 1717423 = 2576135) B2576135
theorem B1717447 : Blo 1717059 1717447 := bstep (se 1 (by rfl) ⟨1288085, by rfl⟩ : syracuseStep 1717447 = 2576171) B2576171
theorem B1717467 : Blo 1717059 1717467 := bstep (se 1 (by rfl) ⟨1288100, by rfl⟩ : syracuseStep 1717467 = 2576201) B2576201
theorem B1717543 : Blo 1717059 1717543 := bstep (se 1 (by rfl) ⟨1288157, by rfl⟩ : syracuseStep 1717543 = 2576315) B2576315
theorem B1717583 : Blo 1717059 1717583 := bstep (se 1 (by rfl) ⟨1288187, by rfl⟩ : syracuseStep 1717583 = 2576375) B2576375
theorem B1717599 : Blo 1717059 1717599 := bstep (se 1 (by rfl) ⟨1288199, by rfl⟩ : syracuseStep 1717599 = 2576399) B2576399
theorem B13047155 : Blo 1717059 13047155 := bstep (se 1 (by rfl) ⟨9785366, by rfl⟩ : syracuseStep 13047155 = 19570733) B19570733
theorem B1717627 : Blo 1717059 1717627 := bstep (se 1 (by rfl) ⟨1288220, by rfl⟩ : syracuseStep 1717627 = 2576441) B2576441
theorem B3863951 : Blo 1717059 3863951 := bstep (se 1 (by rfl) ⟨2897963, by rfl⟩ : syracuseStep 3863951 = 5795927) B5795927
theorem B27874705 : Blo 1717059 27874705 := bstep (se 2 (by rfl) ⟨10453014, by rfl⟩ : syracuseStep 27874705 = 20906029) B20906029
theorem B22304165 : Blo 1717059 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B1717679 : Blo 1717059 1717679 := bstep (se 1 (by rfl) ⟨1288259, by rfl⟩ : syracuseStep 1717679 = 2576519) B2576519
theorem B2577839 : Blo 1717059 2577839 := bstep (se 1 (by rfl) ⟨1933379, by rfl⟩ : syracuseStep 2577839 = 3866759) B3866759
theorem B1717703 : Blo 1717059 1717703 := bstep (se 1 (by rfl) ⟨1288277, by rfl⟩ : syracuseStep 1717703 = 2576555) B2576555
theorem B1717723 : Blo 1717059 1717723 := bstep (se 1 (by rfl) ⟨1288292, by rfl⟩ : syracuseStep 1717723 = 2576585) B2576585
theorem B5502451 : Blo 1717059 5502451 := bstep (se 1 (by rfl) ⟨4126838, by rfl⟩ : syracuseStep 5502451 = 8253677) B8253677
theorem B5797385 : Blo 1717059 5797385 := bstep (se 2 (by rfl) ⟨2174019, by rfl⟩ : syracuseStep 5797385 = 4348039) B4348039
theorem B2577929 : Blo 1717059 2577929 := bstep (se 2 (by rfl) ⟨966723, by rfl⟩ : syracuseStep 2577929 = 1933447) B1933447
theorem B4183591 : Blo 1717059 4183591 := bstep (se 1 (by rfl) ⟨3137693, by rfl⟩ : syracuseStep 4183591 = 6275387) B6275387
theorem B1717799 : Blo 1717059 1717799 := bstep (se 1 (by rfl) ⟨1288349, by rfl⟩ : syracuseStep 1717799 = 2576699) B2576699
theorem B2577959 : Blo 1717059 2577959 := bstep (se 1 (by rfl) ⟨1933469, by rfl⟩ : syracuseStep 2577959 = 3866939) B3866939
theorem B23844395 : Blo 1717059 23844395 := bstep (se 1 (by rfl) ⟨17883296, by rfl⟩ : syracuseStep 23844395 = 35766593) B35766593
theorem B13399613 : Blo 1717059 13399613 := bstep (se 3 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 13399613 = 5024855) B5024855
theorem B1717839 : Blo 1717059 1717839 := bstep (se 1 (by rfl) ⟨1288379, by rfl⟩ : syracuseStep 1717839 = 2576759) B2576759
theorem B1717855 : Blo 1717059 1717855 := bstep (se 1 (by rfl) ⟨1288391, by rfl⟩ : syracuseStep 1717855 = 2576783) B2576783
theorem B23549537 : Blo 1717059 23549537 := bstep (se 2 (by rfl) ⟨8831076, by rfl⟩ : syracuseStep 23549537 = 17662153) B17662153
theorem B1717883 : Blo 1717059 1717883 := bstep (se 1 (by rfl) ⟨1288412, by rfl⟩ : syracuseStep 1717883 = 2576825) B2576825
theorem B2578043 : Blo 1717059 2578043 := bstep (se 1 (by rfl) ⟨1933532, by rfl⟩ : syracuseStep 2578043 = 3867065) B3867065
theorem B2897579 : Blo 1717059 2897579 := bstep (se 1 (by rfl) ⟨2173184, by rfl⟩ : syracuseStep 2897579 = 4346369) B4346369
theorem B1717935 : Blo 1717059 1717935 := bstep (se 1 (by rfl) ⟨1288451, by rfl⟩ : syracuseStep 1717935 = 2576903) B2576903
theorem B1717959 : Blo 1717059 1717959 := bstep (se 1 (by rfl) ⟨1288469, by rfl⟩ : syracuseStep 1717959 = 2576939) B2576939
theorem B3864275 : Blo 1717059 3864275 := bstep (se 1 (by rfl) ⟨2898206, by rfl⟩ : syracuseStep 3864275 = 5796413) B5796413
theorem B1717979 : Blo 1717059 1717979 := bstep (se 1 (by rfl) ⟨1288484, by rfl⟩ : syracuseStep 1717979 = 2576969) B2576969
theorem B2578169 : Blo 1717059 2578169 := bstep (se 2 (by rfl) ⟨966813, by rfl⟩ : syracuseStep 2578169 = 1933627) B1933627
theorem B1718055 : Blo 1717059 1718055 := bstep (se 1 (by rfl) ⟨1288541, by rfl⟩ : syracuseStep 1718055 = 2577083) B2577083
theorem B1718095 : Blo 1717059 1718095 := bstep (se 1 (by rfl) ⟨1288571, by rfl⟩ : syracuseStep 1718095 = 2577143) B2577143
theorem B1718111 : Blo 1717059 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B2578271 : Blo 1717059 2578271 := bstep (se 1 (by rfl) ⟨1933703, by rfl⟩ : syracuseStep 2578271 = 3867407) B3867407
theorem B2578283 : Blo 1717059 2578283 := bstep (se 1 (by rfl) ⟨1933712, by rfl⟩ : syracuseStep 2578283 = 3867425) B3867425
theorem B1718139 : Blo 1717059 1718139 := bstep (se 1 (by rfl) ⟨1288604, by rfl⟩ : syracuseStep 1718139 = 2577209) B2577209
theorem B5224367 : Blo 1717059 5224367 := bstep (se 1 (by rfl) ⟨3918275, by rfl⟩ : syracuseStep 5224367 = 7836551) B7836551
theorem B1718191 : Blo 1717059 1718191 := bstep (se 1 (by rfl) ⟨1288643, by rfl⟩ : syracuseStep 1718191 = 2577287) B2577287
theorem B24762293 : Blo 1717059 24762293 := bstep (se 5 (by rfl) ⟨1160732, by rfl⟩ : syracuseStep 24762293 = 2321465) B2321465
theorem B1718215 : Blo 1717059 1718215 := bstep (se 1 (by rfl) ⟨1288661, by rfl⟩ : syracuseStep 1718215 = 2577323) B2577323
theorem B1718235 : Blo 1717059 1718235 := bstep (se 1 (by rfl) ⟨1288676, by rfl⟩ : syracuseStep 1718235 = 2577353) B2577353
theorem B1718311 : Blo 1717059 1718311 := bstep (se 1 (by rfl) ⟨1288733, by rfl⟩ : syracuseStep 1718311 = 2577467) B2577467
theorem B2897977 : Blo 1717059 2897977 := bstep (se 2 (by rfl) ⟨1086741, by rfl⟩ : syracuseStep 2897977 = 2173483) B2173483
theorem B50894905 : Blo 1717059 50894905 := bstep (se 2 (by rfl) ⟨19085589, by rfl⟩ : syracuseStep 50894905 = 38171179) B38171179
theorem B8599609 : Blo 1717059 8599609 := bstep (se 2 (by rfl) ⟨3224853, by rfl⟩ : syracuseStep 8599609 = 6449707) B6449707
theorem B1718351 : Blo 1717059 1718351 := bstep (se 1 (by rfl) ⟨1288763, by rfl⟩ : syracuseStep 1718351 = 2577527) B2577527
theorem B2578511 : Blo 1717059 2578511 := bstep (se 1 (by rfl) ⟨1933883, by rfl⟩ : syracuseStep 2578511 = 3867767) B3867767
theorem B3094625 : Blo 1717059 3094625 := bstep (se 2 (by rfl) ⟨1160484, by rfl⟩ : syracuseStep 3094625 = 2320969) B2320969
theorem B1718367 : Blo 1717059 1718367 := bstep (se 1 (by rfl) ⟨1288775, by rfl⟩ : syracuseStep 1718367 = 2577551) B2577551
theorem B1718395 : Blo 1717059 1718395 := bstep (se 1 (by rfl) ⟨1288796, by rfl⟩ : syracuseStep 1718395 = 2577593) B2577593
theorem B1718447 : Blo 1717059 1718447 := bstep (se 1 (by rfl) ⟨1288835, by rfl⟩ : syracuseStep 1718447 = 2577671) B2577671
theorem B2898119 : Blo 1717059 2898119 := bstep (se 1 (by rfl) ⟨2173589, by rfl⟩ : syracuseStep 2898119 = 4347179) B4347179
theorem B1718471 : Blo 1717059 1718471 := bstep (se 1 (by rfl) ⟨1288853, by rfl⟩ : syracuseStep 1718471 = 2577707) B2577707
theorem B1718491 : Blo 1717059 1718491 := bstep (se 1 (by rfl) ⟨1288868, by rfl⟩ : syracuseStep 1718491 = 2577737) B2577737
theorem B4348151 : Blo 1717059 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B1718567 : Blo 1717059 1718567 := bstep (se 1 (by rfl) ⟨1288925, by rfl⟩ : syracuseStep 1718567 = 2577851) B2577851
theorem B1718607 : Blo 1717059 1718607 := bstep (se 1 (by rfl) ⟨1288955, by rfl⟩ : syracuseStep 1718607 = 2577911) B2577911
theorem B1718623 : Blo 1717059 1718623 := bstep (se 1 (by rfl) ⟨1288967, by rfl⟩ : syracuseStep 1718623 = 2577935) B2577935
theorem B2898281 : Blo 1717059 2898281 := bstep (se 2 (by rfl) ⟨1086855, by rfl⟩ : syracuseStep 2898281 = 2173711) B2173711
theorem B5798249 : Blo 1717059 5798249 := bstep (se 2 (by rfl) ⟨2174343, by rfl⟩ : syracuseStep 5798249 = 4348687) B4348687
theorem B1718651 : Blo 1717059 1718651 := bstep (se 1 (by rfl) ⟨1288988, by rfl⟩ : syracuseStep 1718651 = 2577977) B2577977
theorem B1718703 : Blo 1717059 1718703 := bstep (se 1 (by rfl) ⟨1289027, by rfl⟩ : syracuseStep 1718703 = 2578055) B2578055
theorem B1718727 : Blo 1717059 1718727 := bstep (se 1 (by rfl) ⟨1289045, by rfl⟩ : syracuseStep 1718727 = 2578091) B2578091
theorem B1718747 : Blo 1717059 1718747 := bstep (se 1 (by rfl) ⟨1289060, by rfl⟩ : syracuseStep 1718747 = 2578121) B2578121
theorem B1718823 : Blo 1717059 1718823 := bstep (se 1 (by rfl) ⟨1289117, by rfl⟩ : syracuseStep 1718823 = 2578235) B2578235
theorem B8698427 : Blo 1717059 8698427 := bstep (se 1 (by rfl) ⟨6523820, by rfl⟩ : syracuseStep 8698427 = 13047641) B13047641
theorem B1718863 : Blo 1717059 1718863 := bstep (se 1 (by rfl) ⟨1289147, by rfl⟩ : syracuseStep 1718863 = 2578295) B2578295
theorem B1718879 : Blo 1717059 1718879 := bstep (se 1 (by rfl) ⟨1289159, by rfl⟩ : syracuseStep 1718879 = 2578319) B2578319
theorem B1931899 : Blo 1717059 1931899 := bstep (se 1 (by rfl) ⟨1448924, by rfl⟩ : syracuseStep 1931899 = 2897849) B2897849
theorem B3865211 : Blo 1717059 3865211 := bstep (se 1 (by rfl) ⟨2898908, by rfl⟩ : syracuseStep 3865211 = 5797817) B5797817
theorem B1718907 : Blo 1717059 1718907 := bstep (se 1 (by rfl) ⟨1289180, by rfl⟩ : syracuseStep 1718907 = 2578361) B2578361
theorem B1718959 : Blo 1717059 1718959 := bstep (se 1 (by rfl) ⟨1289219, by rfl⟩ : syracuseStep 1718959 = 2578439) B2578439
theorem B1718983 : Blo 1717059 1718983 := bstep (se 1 (by rfl) ⟨1289237, by rfl⟩ : syracuseStep 1718983 = 2578475) B2578475
theorem B1719003 : Blo 1717059 1719003 := bstep (se 1 (by rfl) ⟨1289252, by rfl⟩ : syracuseStep 1719003 = 2578505) B2578505
theorem B2898679 : Blo 1717059 2898679 := bstep (se 1 (by rfl) ⟨2174009, by rfl⟩ : syracuseStep 2898679 = 4348019) B4348019
theorem B3865337 : Blo 1717059 3865337 := bstep (se 2 (by rfl) ⟨1449501, by rfl⟩ : syracuseStep 3865337 = 2899003) B2899003
theorem B8256329 : Blo 1717059 8256329 := bstep (se 2 (by rfl) ⟨3096123, by rfl⟩ : syracuseStep 8256329 = 6192247) B6192247
theorem B2898875 : Blo 1717059 2898875 := bstep (se 1 (by rfl) ⟨2174156, by rfl⟩ : syracuseStep 2898875 = 4348313) B4348313
theorem B5798843 : Blo 1717059 5798843 := bstep (se 1 (by rfl) ⟨4349132, by rfl⟩ : syracuseStep 5798843 = 8698265) B8698265
theorem B12377053 : Blo 1717059 12377053 := bstep (se 3 (by rfl) ⟨2320697, by rfl⟩ : syracuseStep 12377053 = 4641395) B4641395
theorem B3865607 : Blo 1717059 3865607 := bstep (se 1 (by rfl) ⟨2899205, by rfl⟩ : syracuseStep 3865607 = 5798411) B5798411
theorem B2898983 : Blo 1717059 2898983 := bstep (se 1 (by rfl) ⟨2174237, by rfl⟩ : syracuseStep 2898983 = 4348475) B4348475
theorem B1932367 : Blo 1717059 1932367 := bstep (se 1 (by rfl) ⟨1449275, by rfl⟩ : syracuseStep 1932367 = 2898551) B2898551
theorem B3529807 : Blo 1717059 3529807 := bstep (se 1 (by rfl) ⟨2647355, by rfl⟩ : syracuseStep 3529807 = 5294711) B5294711
theorem B3865679 : Blo 1717059 3865679 := bstep (se 1 (by rfl) ⟨2899259, by rfl⟩ : syracuseStep 3865679 = 5798519) B5798519
theorem B8699075 : Blo 1717059 8699075 := bstep (se 1 (by rfl) ⟨6524306, by rfl⟩ : syracuseStep 8699075 = 13048613) B13048613
theorem B2899273 : Blo 1717059 2899273 := bstep (se 2 (by rfl) ⟨1087227, by rfl⟩ : syracuseStep 2899273 = 2174455) B2174455
theorem B2899307 : Blo 1717059 2899307 := bstep (se 1 (by rfl) ⟨2174480, by rfl⟩ : syracuseStep 2899307 = 4348961) B4348961
theorem B5504399 : Blo 1717059 5504399 := bstep (se 1 (by rfl) ⟨4128299, by rfl⟩ : syracuseStep 5504399 = 8256599) B8256599
theorem B6520283 : Blo 1717059 6520283 := bstep (se 1 (by rfl) ⟨4890212, by rfl⟩ : syracuseStep 6520283 = 9780425) B9780425
theorem B1932763 : Blo 1717059 1932763 := bstep (se 1 (by rfl) ⟨1449572, by rfl⟩ : syracuseStep 1932763 = 2899145) B2899145
theorem B3866075 : Blo 1717059 3866075 := bstep (se 1 (by rfl) ⟨2899556, by rfl⟩ : syracuseStep 3866075 = 5799113) B5799113
theorem B11755019 : Blo 1717059 11755019 := bstep (se 1 (by rfl) ⟨8816264, by rfl⟩ : syracuseStep 11755019 = 17632529) B17632529
theorem B3260027 : Blo 1717059 3260027 := bstep (se 1 (by rfl) ⟨2445020, by rfl⟩ : syracuseStep 3260027 = 4890041) B4890041
theorem B7339709 : Blo 1717059 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B4349639 : Blo 1717059 4349639 := bstep (se 1 (by rfl) ⟨3262229, by rfl⟩ : syracuseStep 4349639 = 6524459) B6524459
theorem B2899705 : Blo 1717059 2899705 := bstep (se 2 (by rfl) ⟨1087389, by rfl⟩ : syracuseStep 2899705 = 2174779) B2174779
theorem B1933231 : Blo 1717059 1933231 := bstep (se 1 (by rfl) ⟨1449923, by rfl⟩ : syracuseStep 1933231 = 2899847) B2899847
theorem B3866543 : Blo 1717059 3866543 := bstep (se 1 (by rfl) ⟨2899907, by rfl⟩ : syracuseStep 3866543 = 5799815) B5799815
theorem B13926329 : Blo 1717059 13926329 := bstep (se 2 (by rfl) ⟨5222373, by rfl⟩ : syracuseStep 13926329 = 10444747) B10444747
theorem B6963131 : Blo 1717059 6963131 := bstep (se 1 (by rfl) ⟨5222348, by rfl⟩ : syracuseStep 6963131 = 10444697) B10444697
theorem B3866633 : Blo 1717059 3866633 := bstep (se 2 (by rfl) ⟨1449987, by rfl⟩ : syracuseStep 3866633 = 2899975) B2899975
theorem B13230089 : Blo 1717059 13230089 := bstep (se 2 (by rfl) ⟨4961283, by rfl⟩ : syracuseStep 13230089 = 9922567) B9922567
theorem B7340051 : Blo 1717059 7340051 := bstep (se 1 (by rfl) ⟨5505038, by rfl⟩ : syracuseStep 7340051 = 11010077) B11010077
theorem B16506929 : Blo 1717059 16506929 := bstep (se 2 (by rfl) ⟨6190098, by rfl⟩ : syracuseStep 16506929 = 12380197) B12380197
theorem B4129049 : Blo 1717059 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B1835303 : Blo 1717059 1835303 := bstep (se 1 (by rfl) ⟨1376477, by rfl⟩ : syracuseStep 1835303 = 2752955) B2752955
theorem B18825637 : Blo 1717059 18825637 := bstep (se 4 (by rfl) ⟨1764903, by rfl⟩ : syracuseStep 18825637 = 3529807) B3529807
theorem B3867047 : Blo 1717059 3867047 := bstep (se 1 (by rfl) ⟨2900285, by rfl⟩ : syracuseStep 3867047 = 5800571) B5800571
theorem B1933735 : Blo 1717059 1933735 := bstep (se 1 (by rfl) ⟨1450301, by rfl⟩ : syracuseStep 1933735 = 2900603) B2900603
theorem B4350419 : Blo 1717059 4350419 := bstep (se 1 (by rfl) ⟨3262814, by rfl⟩ : syracuseStep 4350419 = 6525629) B6525629
theorem B3867155 : Blo 1717059 3867155 := bstep (se 1 (by rfl) ⟨2900366, by rfl⟩ : syracuseStep 3867155 = 5800733) B5800733
theorem B4645439 : Blo 1717059 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B3260999 : Blo 1717059 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B3867209 : Blo 1717059 3867209 := bstep (se 2 (by rfl) ⟨1450203, by rfl⟩ : syracuseStep 3867209 = 2900407) B2900407
theorem B3261151 : Blo 1717059 3261151 := bstep (se 1 (by rfl) ⟨2445863, by rfl⟩ : syracuseStep 3261151 = 4891727) B4891727
theorem B11010977 : Blo 1717059 11010977 := bstep (se 2 (by rfl) ⟨4129116, by rfl⟩ : syracuseStep 11010977 = 8258233) B8258233
theorem B3867623 : Blo 1717059 3867623 := bstep (se 1 (by rfl) ⟨2900717, by rfl⟩ : syracuseStep 3867623 = 5801435) B5801435
theorem B5801057 : Blo 1717059 5801057 := bstep (se 2 (by rfl) ⟨2175396, by rfl⟩ : syracuseStep 5801057 = 4350793) B4350793
theorem B4129991 : Blo 1717059 4129991 := bstep (se 1 (by rfl) ⟨3097493, by rfl⟩ : syracuseStep 4129991 = 6194987) B6194987
theorem B3671239 : Blo 1717059 3671239 := bstep (se 1 (by rfl) ⟨2753429, by rfl⟩ : syracuseStep 3671239 = 5506859) B5506859
theorem B3482911 : Blo 1717059 3482911 := bstep (se 1 (by rfl) ⟨2612183, by rfl⟩ : syracuseStep 3482911 = 5224367) B5224367
theorem B16508195 : Blo 1717059 16508195 := bstep (se 1 (by rfl) ⟨12381146, by rfl⟩ : syracuseStep 16508195 = 24762293) B24762293
theorem B9291095 : Blo 1717059 9291095 := bstep (se 1 (by rfl) ⟨6968321, by rfl⟩ : syracuseStep 9291095 = 13936643) B13936643
theorem B3671419 : Blo 1717059 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B18580889 : Blo 1717059 18580889 := bstep (se 2 (by rfl) ⟨6967833, by rfl⟩ : syracuseStep 18580889 = 13935667) B13935667
theorem B8693405 : Blo 1717059 8693405 := bstep (se 3 (by rfl) ⟨1630013, by rfl⟩ : syracuseStep 8693405 = 3260027) B3260027
theorem B8251217 : Blo 1717059 8251217 := bstep (se 2 (by rfl) ⟨3094206, by rfl⟩ : syracuseStep 8251217 = 6188413) B6188413
theorem B9922385 : Blo 1717059 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B31336429 : Blo 1717059 31336429 := bstep (se 3 (by rfl) ⟨5875580, by rfl⟩ : syracuseStep 31336429 = 11751161) B11751161
theorem B4893139 : Blo 1717059 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B29362661 : Blo 1717059 29362661 := bstep (se 4 (by rfl) ⟨2752749, by rfl⟩ : syracuseStep 29362661 = 5505499) B5505499
theorem B7342579 : Blo 1717059 7342579 := bstep (se 1 (by rfl) ⟨5506934, by rfl⟩ : syracuseStep 7342579 = 11013869) B11013869
theorem B9284219 : Blo 1717059 9284219 := bstep (se 1 (by rfl) ⟨6963164, by rfl⟩ : syracuseStep 9284219 = 13926329) B13926329
theorem B8702639 : Blo 1717059 8702639 := bstep (se 1 (by rfl) ⟨6526979, by rfl⟩ : syracuseStep 8702639 = 13053959) B13053959
theorem B2321119 : Blo 1717059 2321119 := bstep (se 1 (by rfl) ⟨1740839, by rfl⟩ : syracuseStep 2321119 = 3481679) B3481679
theorem B2321131 : Blo 1717059 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B8694701 : Blo 1717059 8694701 := bstep (se 3 (by rfl) ⟨1630256, by rfl⟩ : syracuseStep 8694701 = 3260513) B3260513
theorem B3484891 : Blo 1717059 3484891 := bstep (se 1 (by rfl) ⟨2613668, by rfl⟩ : syracuseStep 3484891 = 5227337) B5227337
theorem B4893983 : Blo 1717059 4893983 := bstep (se 1 (by rfl) ⟨3670487, by rfl⟩ : syracuseStep 4893983 = 7340975) B7340975
theorem B2575655 : Blo 1717059 2575655 := bstep (se 1 (by rfl) ⟨1931741, by rfl⟩ : syracuseStep 2575655 = 3863483) B3863483
theorem B2575739 : Blo 1717059 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B2575865 : Blo 1717059 2575865 := bstep (se 2 (by rfl) ⟨965949, by rfl⟩ : syracuseStep 2575865 = 1931899) B1931899
theorem B11013641 : Blo 1717059 11013641 := bstep (se 2 (by rfl) ⟨4130115, by rfl⟩ : syracuseStep 11013641 = 8260231) B8260231
theorem B2575967 : Blo 1717059 2575967 := bstep (se 1 (by rfl) ⟨1931975, by rfl⟩ : syracuseStep 2575967 = 3863951) B3863951
theorem B15896263 : Blo 1717059 15896263 := bstep (se 1 (by rfl) ⟨11922197, by rfl⟩ : syracuseStep 15896263 = 23844395) B23844395
theorem B8933075 : Blo 1717059 8933075 := bstep (se 1 (by rfl) ⟨6699806, by rfl⟩ : syracuseStep 8933075 = 13399613) B13399613
theorem B15699691 : Blo 1717059 15699691 := bstep (se 1 (by rfl) ⟨11774768, by rfl⟩ : syracuseStep 15699691 = 23549537) B23549537
theorem B59477773 : Blo 1717059 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B2576183 : Blo 1717059 2576183 := bstep (se 1 (by rfl) ⟨1932137, by rfl⟩ : syracuseStep 2576183 = 3864275) B3864275
theorem B16502737 : Blo 1717059 16502737 := bstep (se 2 (by rfl) ⟨6188526, by rfl⟩ : syracuseStep 16502737 = 12377053) B12377053
theorem B2174951 : Blo 1717059 2174951 := bstep (se 1 (by rfl) ⟨1631213, by rfl⟩ : syracuseStep 2174951 = 3262427) B3262427
theorem B2576489 : Blo 1717059 2576489 := bstep (se 2 (by rfl) ⟨966183, by rfl⟩ : syracuseStep 2576489 = 1932367) B1932367
theorem B4894825 : Blo 1717059 4894825 := bstep (se 2 (by rfl) ⟨1835559, by rfl⟩ : syracuseStep 4894825 = 3671119) B3671119
theorem B2576807 : Blo 1717059 2576807 := bstep (se 1 (by rfl) ⟨1932605, by rfl⟩ : syracuseStep 2576807 = 3865211) B3865211
theorem B2576891 : Blo 1717059 2576891 := bstep (se 1 (by rfl) ⟨1932668, by rfl⟩ : syracuseStep 2576891 = 3865337) B3865337
theorem B8696321 : Blo 1717059 8696321 := bstep (se 2 (by rfl) ⟨3261120, by rfl⟩ : syracuseStep 8696321 = 6522241) B6522241
theorem B25113185 : Blo 1717059 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B2577017 : Blo 1717059 2577017 := bstep (se 2 (by rfl) ⟨966381, by rfl⟩ : syracuseStep 2577017 = 1932763) B1932763
theorem B7336601 : Blo 1717059 7336601 := bstep (se 2 (by rfl) ⟨2751225, by rfl⟩ : syracuseStep 7336601 = 5502451) B5502451
theorem B2577071 : Blo 1717059 2577071 := bstep (se 1 (by rfl) ⟨1932803, by rfl⟩ : syracuseStep 2577071 = 3865607) B3865607
theorem B5796575 : Blo 1717059 5796575 := bstep (se 1 (by rfl) ⟨4347431, by rfl⟩ : syracuseStep 5796575 = 8694863) B8694863
theorem B2577119 : Blo 1717059 2577119 := bstep (se 1 (by rfl) ⟨1932839, by rfl⟩ : syracuseStep 2577119 = 3865679) B3865679
theorem B16503581 : Blo 1717059 16503581 := bstep (se 3 (by rfl) ⟨3094421, by rfl⟩ : syracuseStep 16503581 = 6188843) B6188843
theorem B13226861 : Blo 1717059 13226861 := bstep (se 3 (by rfl) ⟨2480036, by rfl⟩ : syracuseStep 13226861 = 4960073) B4960073
theorem B1717147 : Blo 1717059 1717147 := bstep (se 1 (by rfl) ⟨1287860, by rfl⟩ : syracuseStep 1717147 = 2575721) B2575721
theorem B1717199 : Blo 1717059 1717199 := bstep (se 1 (by rfl) ⟨1287899, by rfl⟩ : syracuseStep 1717199 = 2575799) B2575799
theorem B1717223 : Blo 1717059 1717223 := bstep (se 1 (by rfl) ⟨1287917, by rfl⟩ : syracuseStep 1717223 = 2575835) B2575835
theorem B4346855 : Blo 1717059 4346855 := bstep (se 1 (by rfl) ⟨3260141, by rfl⟩ : syracuseStep 4346855 = 6520283) B6520283
theorem B8696807 : Blo 1717059 8696807 := bstep (se 1 (by rfl) ⟨6522605, by rfl⟩ : syracuseStep 8696807 = 13045211) B13045211
theorem B2577383 : Blo 1717059 2577383 := bstep (se 1 (by rfl) ⟨1933037, by rfl⟩ : syracuseStep 2577383 = 3866075) B3866075
theorem B7836679 : Blo 1717059 7836679 := bstep (se 1 (by rfl) ⟨5877509, by rfl⟩ : syracuseStep 7836679 = 11755019) B11755019
theorem B3863591 : Blo 1717059 3863591 := bstep (se 1 (by rfl) ⟨2897693, by rfl⟩ : syracuseStep 3863591 = 5795387) B5795387
theorem B29340791 : Blo 1717059 29340791 := bstep (se 1 (by rfl) ⟨22005593, by rfl⟩ : syracuseStep 29340791 = 44011187) B44011187
theorem B5797007 : Blo 1717059 5797007 := bstep (se 1 (by rfl) ⟨4347755, by rfl⟩ : syracuseStep 5797007 = 8695511) B8695511
theorem B18568349 : Blo 1717059 18568349 := bstep (se 3 (by rfl) ⟨3481565, by rfl⟩ : syracuseStep 18568349 = 6963131) B6963131
theorem B3863771 : Blo 1717059 3863771 := bstep (se 1 (by rfl) ⟨2897828, by rfl⟩ : syracuseStep 3863771 = 5795657) B5795657
theorem B2577641 : Blo 1717059 2577641 := bstep (se 2 (by rfl) ⟨966615, by rfl⟩ : syracuseStep 2577641 = 1933231) B1933231
theorem B1717535 : Blo 1717059 1717535 := bstep (se 1 (by rfl) ⟨1288151, by rfl⟩ : syracuseStep 1717535 = 2576303) B2576303
theorem B2577695 : Blo 1717059 2577695 := bstep (se 1 (by rfl) ⟨1933271, by rfl⟩ : syracuseStep 2577695 = 3866543) B3866543
theorem B8697131 : Blo 1717059 8697131 := bstep (se 1 (by rfl) ⟨6522848, by rfl⟩ : syracuseStep 8697131 = 13045697) B13045697
theorem B1717595 : Blo 1717059 1717595 := bstep (se 1 (by rfl) ⟨1288196, by rfl⟩ : syracuseStep 1717595 = 2576393) B2576393
theorem B1717615 : Blo 1717059 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B4183435 : Blo 1717059 4183435 := bstep (se 1 (by rfl) ⟨3137576, by rfl⟩ : syracuseStep 4183435 = 6275153) B6275153
theorem B3863969 : Blo 1717059 3863969 := bstep (se 2 (by rfl) ⟨1448988, by rfl⟩ : syracuseStep 3863969 = 2897977) B2897977
theorem B67859873 : Blo 1717059 67859873 := bstep (se 2 (by rfl) ⟨25447452, by rfl⟩ : syracuseStep 67859873 = 50894905) B50894905
theorem B5658017 : Blo 1717059 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B1717671 : Blo 1717059 1717671 := bstep (se 1 (by rfl) ⟨1288253, by rfl⟩ : syracuseStep 1717671 = 2576507) B2576507
theorem B254252465 : Blo 1717059 254252465 := bstep (se 2 (by rfl) ⟨95344674, by rfl⟩ : syracuseStep 254252465 = 190689349) B190689349
theorem B2577863 : Blo 1717059 2577863 := bstep (se 1 (by rfl) ⟨1933397, by rfl⟩ : syracuseStep 2577863 = 3866795) B3866795
theorem B37172681 : Blo 1717059 37172681 := bstep (se 2 (by rfl) ⟨13939755, by rfl⟩ : syracuseStep 37172681 = 27879511) B27879511
theorem B1717755 : Blo 1717059 1717755 := bstep (se 1 (by rfl) ⟨1288316, by rfl⟩ : syracuseStep 1717755 = 2576633) B2576633
theorem B1717823 : Blo 1717059 1717823 := bstep (se 1 (by rfl) ⟨1288367, by rfl⟩ : syracuseStep 1717823 = 2576735) B2576735
theorem B1717831 : Blo 1717059 1717831 := bstep (se 1 (by rfl) ⟨1288373, by rfl⟩ : syracuseStep 1717831 = 2576747) B2576747
theorem B45864581 : Blo 1717059 45864581 := bstep (se 4 (by rfl) ⟨4299804, by rfl⟩ : syracuseStep 45864581 = 8599609) B8599609
theorem B4347553 : Blo 1717059 4347553 := bstep (se 2 (by rfl) ⟨1630332, by rfl⟩ : syracuseStep 4347553 = 3260665) B3260665
theorem B16504505 : Blo 1717059 16504505 := bstep (se 2 (by rfl) ⟨6189189, by rfl⟩ : syracuseStep 16504505 = 12378379) B12378379
theorem B1717983 : Blo 1717059 1717983 := bstep (se 1 (by rfl) ⟨1288487, by rfl⟩ : syracuseStep 1717983 = 2576975) B2576975
theorem B2578217 : Blo 1717059 2578217 := bstep (se 2 (by rfl) ⟨966831, by rfl⟩ : syracuseStep 2578217 = 1933663) B1933663
theorem B4126511 : Blo 1717059 4126511 := bstep (se 1 (by rfl) ⟨3094883, by rfl⟩ : syracuseStep 4126511 = 6189767) B6189767
theorem B4347695 : Blo 1717059 4347695 := bstep (se 1 (by rfl) ⟨3260771, by rfl⟩ : syracuseStep 4347695 = 6521543) B6521543
theorem B1718063 : Blo 1717059 1718063 := bstep (se 1 (by rfl) ⟨1288547, by rfl⟩ : syracuseStep 1718063 = 2577095) B2577095
theorem B2578223 : Blo 1717059 2578223 := bstep (se 1 (by rfl) ⟨1933667, by rfl⟩ : syracuseStep 2578223 = 3867335) B3867335
theorem B14677847 : Blo 1717059 14677847 := bstep (se 1 (by rfl) ⟨11008385, by rfl⟩ : syracuseStep 14677847 = 22016771) B22016771
theorem B1718171 : Blo 1717059 1718171 := bstep (se 1 (by rfl) ⟨1288628, by rfl⟩ : syracuseStep 1718171 = 2577257) B2577257
theorem B3864527 : Blo 1717059 3864527 := bstep (se 1 (by rfl) ⟨2898395, by rfl⟩ : syracuseStep 3864527 = 5796791) B5796791
theorem B1718223 : Blo 1717059 1718223 := bstep (se 1 (by rfl) ⟨1288667, by rfl⟩ : syracuseStep 1718223 = 2577335) B2577335
theorem B1718247 : Blo 1717059 1718247 := bstep (se 1 (by rfl) ⟨1288685, by rfl⟩ : syracuseStep 1718247 = 2577371) B2577371
theorem B8698103 : Blo 1717059 8698103 := bstep (se 1 (by rfl) ⟨6523577, by rfl⟩ : syracuseStep 8698103 = 13047155) B13047155
theorem B5798141 : Blo 1717059 5798141 := bstep (se 3 (by rfl) ⟨1087151, by rfl⟩ : syracuseStep 5798141 = 2174303) B2174303
theorem B1718559 : Blo 1717059 1718559 := bstep (se 1 (by rfl) ⟨1288919, by rfl⟩ : syracuseStep 1718559 = 2577839) B2577839
theorem B3864905 : Blo 1717059 3864905 := bstep (se 2 (by rfl) ⟨1449339, by rfl⟩ : syracuseStep 3864905 = 2898679) B2898679
theorem B3864923 : Blo 1717059 3864923 := bstep (se 1 (by rfl) ⟨2898692, by rfl⟩ : syracuseStep 3864923 = 5797385) B5797385
theorem B1718619 : Blo 1717059 1718619 := bstep (se 1 (by rfl) ⟨1288964, by rfl⟩ : syracuseStep 1718619 = 2577929) B2577929
theorem B1718639 : Blo 1717059 1718639 := bstep (se 1 (by rfl) ⟨1288979, by rfl⟩ : syracuseStep 1718639 = 2577959) B2577959
theorem B1718695 : Blo 1717059 1718695 := bstep (se 1 (by rfl) ⟨1289021, by rfl⟩ : syracuseStep 1718695 = 2578043) B2578043
theorem B4348343 : Blo 1717059 4348343 := bstep (se 1 (by rfl) ⟨3261257, by rfl⟩ : syracuseStep 4348343 = 6522515) B6522515
theorem B1931719 : Blo 1717059 1931719 := bstep (se 1 (by rfl) ⟨1448789, by rfl⟩ : syracuseStep 1931719 = 2897579) B2897579
theorem B1718779 : Blo 1717059 1718779 := bstep (se 1 (by rfl) ⟨1289084, by rfl⟩ : syracuseStep 1718779 = 2578169) B2578169
theorem B1718847 : Blo 1717059 1718847 := bstep (se 1 (by rfl) ⟨1289135, by rfl⟩ : syracuseStep 1718847 = 2578271) B2578271
theorem B1718855 : Blo 1717059 1718855 := bstep (se 1 (by rfl) ⟨1289141, by rfl⟩ : syracuseStep 1718855 = 2578283) B2578283
theorem B8698589 : Blo 1717059 8698589 := bstep (se 3 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 8698589 = 3261971) B3261971
theorem B1719007 : Blo 1717059 1719007 := bstep (se 1 (by rfl) ⟨1289255, by rfl⟩ : syracuseStep 1719007 = 2578511) B2578511
theorem B2063083 : Blo 1717059 2063083 := bstep (se 1 (by rfl) ⟨1547312, by rfl⟩ : syracuseStep 2063083 = 3094625) B3094625
theorem B1932079 : Blo 1717059 1932079 := bstep (se 1 (by rfl) ⟨1449059, by rfl⟩ : syracuseStep 1932079 = 2898119) B2898119
theorem B2898767 : Blo 1717059 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B1932187 : Blo 1717059 1932187 := bstep (se 1 (by rfl) ⟨1449140, by rfl⟩ : syracuseStep 1932187 = 2898281) B2898281
theorem B3865499 : Blo 1717059 3865499 := bstep (se 1 (by rfl) ⟨2899124, by rfl⟩ : syracuseStep 3865499 = 5798249) B5798249
theorem B5798951 : Blo 1717059 5798951 := bstep (se 1 (by rfl) ⟨4349213, by rfl⟩ : syracuseStep 5798951 = 8698427) B8698427
theorem B3865697 : Blo 1717059 3865697 := bstep (se 2 (by rfl) ⟨1449636, by rfl⟩ : syracuseStep 3865697 = 2899273) B2899273
theorem B37166273 : Blo 1717059 37166273 := bstep (se 2 (by rfl) ⟨13937352, by rfl⟩ : syracuseStep 37166273 = 27874705) B27874705
theorem B5504219 : Blo 1717059 5504219 := bstep (se 1 (by rfl) ⟨4128164, by rfl⟩ : syracuseStep 5504219 = 8256329) B8256329
theorem B13049099 : Blo 1717059 13049099 := bstep (se 1 (by rfl) ⟨9786824, by rfl⟩ : syracuseStep 13049099 = 19573649) B19573649
theorem B1932583 : Blo 1717059 1932583 := bstep (se 1 (by rfl) ⟨1449437, by rfl⟩ : syracuseStep 1932583 = 2898875) B2898875
theorem B3865895 : Blo 1717059 3865895 := bstep (se 1 (by rfl) ⟨2899421, by rfl⟩ : syracuseStep 3865895 = 5798843) B5798843
theorem B1932655 : Blo 1717059 1932655 := bstep (se 1 (by rfl) ⟨1449491, by rfl⟩ : syracuseStep 1932655 = 2898983) B2898983
theorem B5578121 : Blo 1717059 5578121 := bstep (se 2 (by rfl) ⟨2091795, by rfl⟩ : syracuseStep 5578121 = 4183591) B4183591
theorem B5799383 : Blo 1717059 5799383 := bstep (se 1 (by rfl) ⟨4349537, by rfl⟩ : syracuseStep 5799383 = 8699075) B8699075
theorem B3530233 : Blo 1717059 3530233 := bstep (se 2 (by rfl) ⟨1323837, by rfl⟩ : syracuseStep 3530233 = 2647675) B2647675
theorem B9788921 : Blo 1717059 9788921 := bstep (se 2 (by rfl) ⟨3670845, by rfl⟩ : syracuseStep 9788921 = 7341691) B7341691
theorem B4349447 : Blo 1717059 4349447 := bstep (se 1 (by rfl) ⟨3262085, by rfl⟩ : syracuseStep 4349447 = 6524171) B6524171
theorem B111418901 : Blo 1717059 111418901 := bstep (se 6 (by rfl) ⟨2611380, by rfl⟩ : syracuseStep 111418901 = 5222761) B5222761
theorem B4349497 : Blo 1717059 4349497 := bstep (se 2 (by rfl) ⟨1631061, by rfl⟩ : syracuseStep 4349497 = 3262123) B3262123
theorem B1932871 : Blo 1717059 1932871 := bstep (se 1 (by rfl) ⟨1449653, by rfl⟩ : syracuseStep 1932871 = 2899307) B2899307
theorem B3669599 : Blo 1717059 3669599 := bstep (se 1 (by rfl) ⟨2752199, by rfl⟩ : syracuseStep 3669599 = 5504399) B5504399
theorem B3866273 : Blo 1717059 3866273 := bstep (se 2 (by rfl) ⟨1449852, by rfl⟩ : syracuseStep 3866273 = 2899705) B2899705
theorem B2899759 : Blo 1717059 2899759 := bstep (se 1 (by rfl) ⟨2174819, by rfl⟩ : syracuseStep 2899759 = 4349639) B4349639
theorem B3096377 : Blo 1717059 3096377 := bstep (se 2 (by rfl) ⟨1161141, by rfl⟩ : syracuseStep 3096377 = 2322283) B2322283
theorem B4349801 : Blo 1717059 4349801 := bstep (se 2 (by rfl) ⟨1631175, by rfl⟩ : syracuseStep 4349801 = 3262351) B3262351
theorem B41795621 : Blo 1717059 41795621 := bstep (se 4 (by rfl) ⟨3918339, by rfl⟩ : syracuseStep 41795621 = 7836679) B7836679
theorem B2752699 : Blo 1717059 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B2900279 : Blo 1717059 2900279 := bstep (se 1 (by rfl) ⟨2175209, by rfl⟩ : syracuseStep 2900279 = 4350419) B4350419
theorem B3096959 : Blo 1717059 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B4891067 : Blo 1717059 4891067 := bstep (se 1 (by rfl) ⟨3668300, by rfl⟩ : syracuseStep 4891067 = 7336601) B7336601
theorem B11002387 : Blo 1717059 11002387 := bstep (se 1 (by rfl) ⟨8251790, by rfl⟩ : syracuseStep 11002387 = 16503581) B16503581
theorem B25100849 : Blo 1717059 25100849 := bstep (se 2 (by rfl) ⟨9412818, by rfl⟩ : syracuseStep 25100849 = 18825637) B18825637
theorem B7340651 : Blo 1717059 7340651 := bstep (se 1 (by rfl) ⟨5505488, by rfl⟩ : syracuseStep 7340651 = 11010977) B11010977
theorem B9790105 : Blo 1717059 9790105 := bstep (se 2 (by rfl) ⟨3671289, by rfl⟩ : syracuseStep 9790105 = 7342579) B7342579
theorem B3867371 : Blo 1717059 3867371 := bstep (se 1 (by rfl) ⟨2900528, by rfl⟩ : syracuseStep 3867371 = 5801057) B5801057
theorem B12378899 : Blo 1717059 12378899 := bstep (se 1 (by rfl) ⟨9284174, by rfl⟩ : syracuseStep 12378899 = 18568349) B18568349
theorem B2753327 : Blo 1717059 2753327 := bstep (se 1 (by rfl) ⟨2064995, by rfl⟩ : syracuseStep 2753327 = 4129991) B4129991
theorem B6194063 : Blo 1717059 6194063 := bstep (se 1 (by rfl) ⟨4645547, by rfl⟩ : syracuseStep 6194063 = 9291095) B9291095
theorem B12387259 : Blo 1717059 12387259 := bstep (se 1 (by rfl) ⟨9290444, by rfl⟩ : syracuseStep 12387259 = 18580889) B18580889
theorem B169501643 : Blo 1717059 169501643 := bstep (se 1 (by rfl) ⟨127126232, by rfl⟩ : syracuseStep 169501643 = 254252465) B254252465
theorem B24781787 : Blo 1717059 24781787 := bstep (se 1 (by rfl) ⟨18586340, by rfl⟩ : syracuseStep 24781787 = 37172681) B37172681
theorem B11003003 : Blo 1717059 11003003 := bstep (se 1 (by rfl) ⟨8252252, by rfl⟩ : syracuseStep 11003003 = 16504505) B16504505
theorem B12379301 : Blo 1717059 12379301 := bstep (se 4 (by rfl) ⟨1160559, by rfl⟩ : syracuseStep 12379301 = 2321119) B2321119
theorem B4646521 : Blo 1717059 4646521 := bstep (se 2 (by rfl) ⟨1742445, by rfl⟩ : syracuseStep 4646521 = 3484891) B3484891
theorem B5801759 : Blo 1717059 5801759 := bstep (se 1 (by rfl) ⟨4351319, by rfl⟩ : syracuseStep 5801759 = 8702639) B8702639
theorem B3262655 : Blo 1717059 3262655 := bstep (se 1 (by rfl) ⟨2446991, by rfl⟩ : syracuseStep 3262655 = 4893983) B4893983
theorem B21195017 : Blo 1717059 21195017 := bstep (se 2 (by rfl) ⟨7948131, by rfl⟩ : syracuseStep 21195017 = 15896263) B15896263
theorem B20932921 : Blo 1717059 20932921 := bstep (se 2 (by rfl) ⟨7849845, by rfl⟩ : syracuseStep 20932921 = 15699691) B15699691
theorem B7342427 : Blo 1717059 7342427 := bstep (se 1 (by rfl) ⟨5506820, by rfl⟩ : syracuseStep 7342427 = 11013641) B11013641
theorem B74279267 : Blo 1717059 74279267 := bstep (se 1 (by rfl) ⟨55709450, by rfl⟩ : syracuseStep 74279267 = 111418901) B111418901
theorem B41781905 : Blo 1717059 41781905 := bstep (se 2 (by rfl) ⟨15668214, by rfl⟩ : syracuseStep 41781905 = 31336429) B31336429
theorem B4893367 : Blo 1717059 4893367 := bstep (se 1 (by rfl) ⟨3670025, by rfl⟩ : syracuseStep 4893367 = 7340051) B7340051
theorem B11004619 : Blo 1717059 11004619 := bstep (se 1 (by rfl) ⟨8253464, by rfl⟩ : syracuseStep 11004619 = 16506929) B16506929
theorem B2575625 : Blo 1717059 2575625 := bstep (se 2 (by rfl) ⟨965859, by rfl⟩ : syracuseStep 2575625 = 1931719) B1931719
theorem B6524185 : Blo 1717059 6524185 := bstep (se 2 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 6524185 = 4893139) B4893139
theorem B2575727 : Blo 1717059 2575727 := bstep (se 1 (by rfl) ⟨1931795, by rfl⟩ : syracuseStep 2575727 = 3863591) B3863591
theorem B2575847 : Blo 1717059 2575847 := bstep (se 1 (by rfl) ⟨1931885, by rfl⟩ : syracuseStep 2575847 = 3863771) B3863771
theorem B11005463 : Blo 1717059 11005463 := bstep (se 1 (by rfl) ⟨8254097, by rfl⟩ : syracuseStep 11005463 = 16508195) B16508195
theorem B2575979 : Blo 1717059 2575979 := bstep (se 1 (by rfl) ⟨1931984, by rfl⟩ : syracuseStep 2575979 = 3863969) B3863969
theorem B45239915 : Blo 1717059 45239915 := bstep (se 1 (by rfl) ⟨33929936, by rfl⟩ : syracuseStep 45239915 = 67859873) B67859873
theorem B2576105 : Blo 1717059 2576105 := bstep (se 2 (by rfl) ⟨966039, by rfl⟩ : syracuseStep 2576105 = 1932079) B1932079
theorem B5795603 : Blo 1717059 5795603 := bstep (se 1 (by rfl) ⟨4346702, by rfl⟩ : syracuseStep 5795603 = 8693405) B8693405
theorem B2576249 : Blo 1717059 2576249 := bstep (se 2 (by rfl) ⟨966093, by rfl⟩ : syracuseStep 2576249 = 1932187) B1932187
theorem B5500811 : Blo 1717059 5500811 := bstep (se 1 (by rfl) ⟨4125608, by rfl⟩ : syracuseStep 5500811 = 8251217) B8251217
theorem B9785231 : Blo 1717059 9785231 := bstep (se 1 (by rfl) ⟨7338923, by rfl⟩ : syracuseStep 9785231 = 14677847) B14677847
theorem B2576351 : Blo 1717059 2576351 := bstep (se 1 (by rfl) ⟨1932263, by rfl⟩ : syracuseStep 2576351 = 3864527) B3864527
theorem B8695997 : Blo 1717059 8695997 := bstep (se 3 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 8695997 = 3260999) B3260999
theorem B2576603 : Blo 1717059 2576603 := bstep (se 1 (by rfl) ⟨1932452, by rfl⟩ : syracuseStep 2576603 = 3864905) B3864905
theorem B2576615 : Blo 1717059 2576615 := bstep (se 1 (by rfl) ⟨1932461, by rfl⟩ : syracuseStep 2576615 = 3864923) B3864923
theorem B4894985 : Blo 1717059 4894985 := bstep (se 2 (by rfl) ⟨1835619, by rfl⟩ : syracuseStep 4894985 = 3671239) B3671239
theorem B19575107 : Blo 1717059 19575107 := bstep (se 1 (by rfl) ⟨14681330, by rfl⟩ : syracuseStep 19575107 = 29362661) B29362661
theorem B2576777 : Blo 1717059 2576777 := bstep (se 2 (by rfl) ⟨966291, by rfl⟩ : syracuseStep 2576777 = 1932583) B1932583
theorem B6189479 : Blo 1717059 6189479 := bstep (se 1 (by rfl) ⟨4642109, by rfl⟩ : syracuseStep 6189479 = 9284219) B9284219
theorem B2576873 : Blo 1717059 2576873 := bstep (se 2 (by rfl) ⟨966327, by rfl⟩ : syracuseStep 2576873 = 1932655) B1932655
theorem B4895225 : Blo 1717059 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B2576999 : Blo 1717059 2576999 := bstep (se 1 (by rfl) ⟨1932749, by rfl⟩ : syracuseStep 2576999 = 3865499) B3865499
theorem B5796467 : Blo 1717059 5796467 := bstep (se 1 (by rfl) ⟨4347350, by rfl⟩ : syracuseStep 5796467 = 8694701) B8694701
theorem B4706977 : Blo 1717059 4706977 := bstep (se 2 (by rfl) ⟨1765116, by rfl⟩ : syracuseStep 4706977 = 3530233) B3530233
theorem B2577131 : Blo 1717059 2577131 := bstep (se 1 (by rfl) ⟨1932848, by rfl⟩ : syracuseStep 2577131 = 3865697) B3865697
theorem B2577161 : Blo 1717059 2577161 := bstep (se 2 (by rfl) ⟨966435, by rfl⟩ : syracuseStep 2577161 = 1932871) B1932871
theorem B24777515 : Blo 1717059 24777515 := bstep (se 1 (by rfl) ⟨18583136, by rfl⟩ : syracuseStep 24777515 = 37166273) B37166273
theorem B1717103 : Blo 1717059 1717103 := bstep (se 1 (by rfl) ⟨1287827, by rfl⟩ : syracuseStep 1717103 = 2575655) B2575655
theorem B2577263 : Blo 1717059 2577263 := bstep (se 1 (by rfl) ⟨1932947, by rfl⟩ : syracuseStep 2577263 = 3865895) B3865895
theorem B5796737 : Blo 1717059 5796737 := bstep (se 2 (by rfl) ⟨2173776, by rfl⟩ : syracuseStep 5796737 = 4347553) B4347553
theorem B1717159 : Blo 1717059 1717159 := bstep (se 1 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 1717159 = 2575739) B2575739
theorem B35271629 : Blo 1717059 35271629 := bstep (se 3 (by rfl) ⟨6613430, by rfl⟩ : syracuseStep 35271629 = 13226861) B13226861
theorem B1717243 : Blo 1717059 1717243 := bstep (se 1 (by rfl) ⟨1287932, by rfl⟩ : syracuseStep 1717243 = 2575865) B2575865
theorem B6525947 : Blo 1717059 6525947 := bstep (se 1 (by rfl) ⟨4894460, by rfl⟩ : syracuseStep 6525947 = 9788921) B9788921
theorem B79303697 : Blo 1717059 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B1717311 : Blo 1717059 1717311 := bstep (se 1 (by rfl) ⟨1287983, by rfl⟩ : syracuseStep 1717311 = 2575967) B2575967
theorem B2446399 : Blo 1717059 2446399 := bstep (se 1 (by rfl) ⟨1834799, by rfl⟩ : syracuseStep 2446399 = 3669599) B3669599
theorem B2577515 : Blo 1717059 2577515 := bstep (se 1 (by rfl) ⟨1933136, by rfl⟩ : syracuseStep 2577515 = 3866273) B3866273
theorem B1717455 : Blo 1717059 1717455 := bstep (se 1 (by rfl) ⟨1288091, by rfl⟩ : syracuseStep 1717455 = 2576183) B2576183
theorem B2577755 : Blo 1717059 2577755 := bstep (se 1 (by rfl) ⟨1933316, by rfl⟩ : syracuseStep 2577755 = 3866633) B3866633
theorem B8820059 : Blo 1717059 8820059 := bstep (se 1 (by rfl) ⟨6615044, by rfl⟩ : syracuseStep 8820059 = 13230089) B13230089
theorem B1717659 : Blo 1717059 1717659 := bstep (se 1 (by rfl) ⟨1288244, by rfl⟩ : syracuseStep 1717659 = 2576489) B2576489
theorem B6526433 : Blo 1717059 6526433 := bstep (se 2 (by rfl) ⟨2447412, by rfl⟩ : syracuseStep 6526433 = 4894825) B4894825
theorem B1717871 : Blo 1717059 1717871 := bstep (se 1 (by rfl) ⟨1288403, by rfl⟩ : syracuseStep 1717871 = 2576807) B2576807
theorem B2578031 : Blo 1717059 2578031 := bstep (se 1 (by rfl) ⟨1933523, by rfl⟩ : syracuseStep 2578031 = 3867047) B3867047
theorem B1717927 : Blo 1717059 1717927 := bstep (se 1 (by rfl) ⟨1288445, by rfl⟩ : syracuseStep 1717927 = 2576891) B2576891
theorem B5797547 : Blo 1717059 5797547 := bstep (se 1 (by rfl) ⟨4348160, by rfl⟩ : syracuseStep 5797547 = 8696321) B8696321
theorem B2578103 : Blo 1717059 2578103 := bstep (se 1 (by rfl) ⟨1933577, by rfl⟩ : syracuseStep 2578103 = 3867155) B3867155
theorem B2578139 : Blo 1717059 2578139 := bstep (se 1 (by rfl) ⟨1933604, by rfl⟩ : syracuseStep 2578139 = 3867209) B3867209
theorem B16742123 : Blo 1717059 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B19576565 : Blo 1717059 19576565 := bstep (se 5 (by rfl) ⟨917651, by rfl⟩ : syracuseStep 19576565 = 1835303) B1835303
theorem B1718011 : Blo 1717059 1718011 := bstep (se 1 (by rfl) ⟨1288508, by rfl⟩ : syracuseStep 1718011 = 2577017) B2577017
theorem B1718047 : Blo 1717059 1718047 := bstep (se 1 (by rfl) ⟨1288535, by rfl⟩ : syracuseStep 1718047 = 2577071) B2577071
theorem B3864383 : Blo 1717059 3864383 := bstep (se 1 (by rfl) ⟨2898287, by rfl⟩ : syracuseStep 3864383 = 5796575) B5796575
theorem B1718079 : Blo 1717059 1718079 := bstep (se 1 (by rfl) ⟨1288559, by rfl⟩ : syracuseStep 1718079 = 2577119) B2577119
theorem B2578313 : Blo 1717059 2578313 := bstep (se 2 (by rfl) ⟨966867, by rfl⟩ : syracuseStep 2578313 = 1933735) B1933735
theorem B2897903 : Blo 1717059 2897903 := bstep (se 1 (by rfl) ⟨2173427, by rfl⟩ : syracuseStep 2897903 = 4346855) B4346855
theorem B5797871 : Blo 1717059 5797871 := bstep (se 1 (by rfl) ⟨4348403, by rfl⟩ : syracuseStep 5797871 = 8696807) B8696807
theorem B1718255 : Blo 1717059 1718255 := bstep (se 1 (by rfl) ⟨1288691, by rfl⟩ : syracuseStep 1718255 = 2577383) B2577383
theorem B2578415 : Blo 1717059 2578415 := bstep (se 1 (by rfl) ⟨1933811, by rfl⟩ : syracuseStep 2578415 = 3867623) B3867623
theorem B19560527 : Blo 1717059 19560527 := bstep (se 1 (by rfl) ⟨14670395, by rfl⟩ : syracuseStep 19560527 = 29340791) B29340791
theorem B3864671 : Blo 1717059 3864671 := bstep (se 1 (by rfl) ⟨2898503, by rfl⟩ : syracuseStep 3864671 = 5797007) B5797007
theorem B1718427 : Blo 1717059 1718427 := bstep (se 1 (by rfl) ⟨1288820, by rfl⟩ : syracuseStep 1718427 = 2577641) B2577641
theorem B1718463 : Blo 1717059 1718463 := bstep (se 1 (by rfl) ⟨1288847, by rfl⟩ : syracuseStep 1718463 = 2577695) B2577695
theorem B5798087 : Blo 1717059 5798087 := bstep (se 1 (by rfl) ⟨4348565, by rfl⟩ : syracuseStep 5798087 = 8697131) B8697131
theorem B4348201 : Blo 1717059 4348201 := bstep (se 2 (by rfl) ⟨1630575, by rfl⟩ : syracuseStep 4348201 = 3261151) B3261151
theorem B1718575 : Blo 1717059 1718575 := bstep (se 1 (by rfl) ⟨1288931, by rfl⟩ : syracuseStep 1718575 = 2577863) B2577863
theorem B2750777 : Blo 1717059 2750777 := bstep (se 2 (by rfl) ⟨1031541, by rfl⟩ : syracuseStep 2750777 = 2063083) B2063083
theorem B3094841 : Blo 1717059 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B15088045 : Blo 1717059 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B1718811 : Blo 1717059 1718811 := bstep (se 1 (by rfl) ⟨1289108, by rfl⟩ : syracuseStep 1718811 = 2578217) B2578217
theorem B2751007 : Blo 1717059 2751007 := bstep (se 1 (by rfl) ⟨2063255, by rfl⟩ : syracuseStep 2751007 = 4126511) B4126511
theorem B2898463 : Blo 1717059 2898463 := bstep (se 1 (by rfl) ⟨2173847, by rfl⟩ : syracuseStep 2898463 = 4347695) B4347695
theorem B1718815 : Blo 1717059 1718815 := bstep (se 1 (by rfl) ⟨1289111, by rfl⟩ : syracuseStep 1718815 = 2578223) B2578223
theorem B5798735 : Blo 1717059 5798735 := bstep (se 1 (by rfl) ⟨4349051, by rfl⟩ : syracuseStep 5798735 = 8698103) B8698103
theorem B3865427 : Blo 1717059 3865427 := bstep (se 1 (by rfl) ⟨2899070, by rfl⟩ : syracuseStep 3865427 = 5798141) B5798141
theorem B2898895 : Blo 1717059 2898895 := bstep (se 1 (by rfl) ⟨2174171, by rfl⟩ : syracuseStep 2898895 = 4348343) B4348343
theorem B122305549 : Blo 1717059 122305549 := bstep (se 3 (by rfl) ⟨22932290, by rfl⟩ : syracuseStep 122305549 = 45864581) B45864581
theorem B4643881 : Blo 1717059 4643881 := bstep (se 2 (by rfl) ⟨1741455, by rfl⟩ : syracuseStep 4643881 = 3482911) B3482911
theorem B5799059 : Blo 1717059 5799059 := bstep (se 1 (by rfl) ⟨4349294, by rfl⟩ : syracuseStep 5799059 = 8698589) B8698589
theorem B5577913 : Blo 1717059 5577913 := bstep (se 2 (by rfl) ⟨2091717, by rfl⟩ : syracuseStep 5577913 = 4183435) B4183435
theorem B1932511 : Blo 1717059 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B3865967 : Blo 1717059 3865967 := bstep (se 1 (by rfl) ⟨2899475, by rfl⟩ : syracuseStep 3865967 = 5798951) B5798951
theorem B5799329 : Blo 1717059 5799329 := bstep (se 2 (by rfl) ⟨2174748, by rfl⟩ : syracuseStep 5799329 = 4349497) B4349497
theorem B3669479 : Blo 1717059 3669479 := bstep (se 1 (by rfl) ⟨2752109, by rfl⟩ : syracuseStep 3669479 = 5504219) B5504219
theorem B8699399 : Blo 1717059 8699399 := bstep (se 1 (by rfl) ⟨6524549, by rfl⟩ : syracuseStep 8699399 = 13049099) B13049099
theorem B26459693 : Blo 1717059 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B3718747 : Blo 1717059 3718747 := bstep (se 1 (by rfl) ⟨2789060, by rfl⟩ : syracuseStep 3718747 = 5578121) B5578121
theorem B3866255 : Blo 1717059 3866255 := bstep (se 1 (by rfl) ⟨2899691, by rfl⟩ : syracuseStep 3866255 = 5799383) B5799383
theorem B2899631 : Blo 1717059 2899631 := bstep (se 1 (by rfl) ⟨2174723, by rfl⟩ : syracuseStep 2899631 = 4349447) B4349447
theorem B3866345 : Blo 1717059 3866345 := bstep (se 2 (by rfl) ⟨1449879, by rfl⟩ : syracuseStep 3866345 = 2899759) B2899759
theorem B5955383 : Blo 1717059 5955383 := bstep (se 1 (by rfl) ⟨4466537, by rfl⟩ : syracuseStep 5955383 = 8933075) B8933075
theorem B2064251 : Blo 1717059 2064251 := bstep (se 1 (by rfl) ⟨1548188, by rfl⟩ : syracuseStep 2064251 = 3096377) B3096377
theorem B2899867 : Blo 1717059 2899867 := bstep (se 1 (by rfl) ⟨2174900, by rfl⟩ : syracuseStep 2899867 = 4349801) B4349801
theorem B5799869 : Blo 1717059 5799869 := bstep (se 3 (by rfl) ⟨1087475, by rfl⟩ : syracuseStep 5799869 = 2174951) B2174951
theorem B22003649 : Blo 1717059 22003649 := bstep (se 2 (by rfl) ⟨8251368, by rfl⟩ : syracuseStep 22003649 = 16502737) B16502737
theorem B1933519 : Blo 1717059 1933519 := bstep (se 1 (by rfl) ⟨1450139, by rfl⟩ : syracuseStep 1933519 = 2900279) B2900279
theorem B13050071 : Blo 1717059 13050071 := bstep (se 1 (by rfl) ⟨9787553, by rfl⟩ : syracuseStep 13050071 = 19575107) B19575107
theorem B3670265 : Blo 1717059 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B3260711 : Blo 1717059 3260711 := bstep (se 1 (by rfl) ⟨2445533, by rfl⟩ : syracuseStep 3260711 = 4891067) B4891067
theorem B27910561 : Blo 1717059 27910561 := bstep (se 2 (by rfl) ⟨10466460, by rfl⟩ : syracuseStep 27910561 = 20932921) B20932921
theorem B1835551 : Blo 1717059 1835551 := bstep (se 1 (by rfl) ⟨1376663, by rfl⟩ : syracuseStep 1835551 = 2753327) B2753327
theorem B4129375 : Blo 1717059 4129375 := bstep (se 1 (by rfl) ⟨3097031, by rfl⟩ : syracuseStep 4129375 = 6194063) B6194063
theorem B113001095 : Blo 1717059 113001095 := bstep (se 1 (by rfl) ⟨84750821, by rfl⟩ : syracuseStep 113001095 = 169501643) B169501643
theorem B4350631 : Blo 1717059 4350631 := bstep (se 1 (by rfl) ⟨3262973, by rfl⟩ : syracuseStep 4350631 = 6525947) B6525947
theorem B6275969 : Blo 1717059 6275969 := bstep (se 2 (by rfl) ⟨2353488, by rfl⟩ : syracuseStep 6275969 = 4706977) B4706977
theorem B14672825 : Blo 1717059 14672825 := bstep (se 2 (by rfl) ⟨5502309, by rfl⟩ : syracuseStep 14672825 = 11004619) B11004619
theorem B4350955 : Blo 1717059 4350955 := bstep (se 1 (by rfl) ⟨3263216, by rfl⟩ : syracuseStep 4350955 = 6526433) B6526433
theorem B8258557 : Blo 1717059 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B13051043 : Blo 1717059 13051043 := bstep (se 1 (by rfl) ⟨9788282, by rfl⟩ : syracuseStep 13051043 = 19576565) B19576565
theorem B3867839 : Blo 1717059 3867839 := bstep (se 1 (by rfl) ⟨2900879, by rfl⟩ : syracuseStep 3867839 = 5801759) B5801759
theorem B16516345 : Blo 1717059 16516345 := bstep (se 2 (by rfl) ⟨6193629, by rfl⟩ : syracuseStep 16516345 = 12387259) B12387259
theorem B3261865 : Blo 1717059 3261865 := bstep (se 2 (by rfl) ⟨1223199, by rfl⟩ : syracuseStep 3261865 = 2446399) B2446399
theorem B27854603 : Blo 1717059 27854603 := bstep (se 1 (by rfl) ⟨20890952, by rfl⟩ : syracuseStep 27854603 = 41781905) B41781905
theorem B4958329 : Blo 1717059 4958329 := bstep (se 2 (by rfl) ⟨1859373, by rfl⟩ : syracuseStep 4958329 = 3718747) B3718747
theorem B6195361 : Blo 1717059 6195361 := bstep (se 2 (by rfl) ⟨2323260, by rfl⟩ : syracuseStep 6195361 = 4646521) B4646521
theorem B17639795 : Blo 1717059 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B6523487 : Blo 1717059 6523487 := bstep (se 1 (by rfl) ⟨4892615, by rfl⟩ : syracuseStep 6523487 = 9785231) B9785231
theorem B27863747 : Blo 1717059 27863747 := bstep (se 1 (by rfl) ⟨20897810, by rfl⟩ : syracuseStep 27863747 = 41795621) B41795621
theorem B3263323 : Blo 1717059 3263323 := bstep (se 1 (by rfl) ⟨2447492, by rfl⟩ : syracuseStep 3263323 = 4894985) B4894985
theorem B24767365 : Blo 1717059 24767365 := bstep (se 4 (by rfl) ⟨2321940, by rfl⟩ : syracuseStep 24767365 = 4643881) B4643881
theorem B3263483 : Blo 1717059 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B4893767 : Blo 1717059 4893767 := bstep (se 1 (by rfl) ⟨3670325, by rfl⟩ : syracuseStep 4893767 = 7340651) B7340651
theorem B8252599 : Blo 1717059 8252599 := bstep (se 1 (by rfl) ⟨6189449, by rfl⟩ : syracuseStep 8252599 = 12378899) B12378899
theorem B16518343 : Blo 1717059 16518343 := bstep (se 1 (by rfl) ⟨12388757, by rfl⟩ : syracuseStep 16518343 = 24777515) B24777515
theorem B23514419 : Blo 1717059 23514419 := bstep (se 1 (by rfl) ⟨17635814, by rfl⟩ : syracuseStep 23514419 = 35271629) B35271629
theorem B7335335 : Blo 1717059 7335335 := bstep (se 1 (by rfl) ⟨5501501, by rfl⟩ : syracuseStep 7335335 = 11003003) B11003003
theorem B8252867 : Blo 1717059 8252867 := bstep (se 1 (by rfl) ⟨6189650, by rfl⟩ : syracuseStep 8252867 = 12379301) B12379301
theorem B13053473 : Blo 1717059 13053473 := bstep (se 2 (by rfl) ⟨4895052, by rfl⟩ : syracuseStep 13053473 = 9790105) B9790105
theorem B6524489 : Blo 1717059 6524489 := bstep (se 2 (by rfl) ⟨2446683, by rfl⟩ : syracuseStep 6524489 = 4893367) B4893367
theorem B94080629 : Blo 1717059 94080629 := bstep (se 5 (by rfl) ⟨4410029, by rfl⟩ : syracuseStep 94080629 = 8820059) B8820059
theorem B11161415 : Blo 1717059 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B2576255 : Blo 1717059 2576255 := bstep (se 1 (by rfl) ⟨1932191, by rfl⟩ : syracuseStep 2576255 = 3864383) B3864383
theorem B163074065 : Blo 1717059 163074065 := bstep (se 2 (by rfl) ⟨61152774, by rfl⟩ : syracuseStep 163074065 = 122305549) B122305549
theorem B2576447 : Blo 1717059 2576447 := bstep (se 1 (by rfl) ⟨1932335, by rfl⟩ : syracuseStep 2576447 = 3864671) B3864671
theorem B2175103 : Blo 1717059 2175103 := bstep (se 1 (by rfl) ⟨1631327, by rfl⟩ : syracuseStep 2175103 = 3262655) B3262655
theorem B4894951 : Blo 1717059 4894951 := bstep (se 1 (by rfl) ⟨3671213, by rfl⟩ : syracuseStep 4894951 = 7342427) B7342427
theorem B120639773 : Blo 1717059 120639773 := bstep (se 3 (by rfl) ⟨22619957, by rfl⟩ : syracuseStep 120639773 = 45239915) B45239915
theorem B2576681 : Blo 1717059 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B2576951 : Blo 1717059 2576951 := bstep (se 1 (by rfl) ⟨1932713, by rfl⟩ : syracuseStep 2576951 = 3865427) B3865427
theorem B15881021 : Blo 1717059 15881021 := bstep (se 3 (by rfl) ⟨2977691, by rfl⟩ : syracuseStep 15881021 = 5955383) B5955383
theorem B1717083 : Blo 1717059 1717083 := bstep (se 1 (by rfl) ⟨1287812, by rfl⟩ : syracuseStep 1717083 = 2575625) B2575625
theorem B1717151 : Blo 1717059 1717151 := bstep (se 1 (by rfl) ⟨1287863, by rfl⟩ : syracuseStep 1717151 = 2575727) B2575727
theorem B2577311 : Blo 1717059 2577311 := bstep (se 1 (by rfl) ⟨1932983, by rfl⟩ : syracuseStep 2577311 = 3865967) B3865967
theorem B1717231 : Blo 1717059 1717231 := bstep (se 1 (by rfl) ⟨1287923, by rfl⟩ : syracuseStep 1717231 = 2575847) B2575847
theorem B2446319 : Blo 1717059 2446319 := bstep (se 1 (by rfl) ⟨1834739, by rfl⟩ : syracuseStep 2446319 = 3669479) B3669479
theorem B7336975 : Blo 1717059 7336975 := bstep (se 1 (by rfl) ⟨5502731, by rfl⟩ : syracuseStep 7336975 = 11005463) B11005463
theorem B1717319 : Blo 1717059 1717319 := bstep (se 1 (by rfl) ⟨1287989, by rfl⟩ : syracuseStep 1717319 = 2575979) B2575979
theorem B2577503 : Blo 1717059 2577503 := bstep (se 1 (by rfl) ⟨1933127, by rfl⟩ : syracuseStep 2577503 = 3866255) B3866255
theorem B1717403 : Blo 1717059 1717403 := bstep (se 1 (by rfl) ⟨1288052, by rfl⟩ : syracuseStep 1717403 = 2576105) B2576105
theorem B2577563 : Blo 1717059 2577563 := bstep (se 1 (by rfl) ⟨1933172, by rfl⟩ : syracuseStep 2577563 = 3866345) B3866345
theorem B3863735 : Blo 1717059 3863735 := bstep (se 1 (by rfl) ⟨2897801, by rfl⟩ : syracuseStep 3863735 = 5795603) B5795603
theorem B1717499 : Blo 1717059 1717499 := bstep (se 1 (by rfl) ⟨1288124, by rfl⟩ : syracuseStep 1717499 = 2576249) B2576249
theorem B3667207 : Blo 1717059 3667207 := bstep (se 1 (by rfl) ⟨2750405, by rfl⟩ : syracuseStep 3667207 = 5500811) B5500811
theorem B14669099 : Blo 1717059 14669099 := bstep (se 1 (by rfl) ⟨11001824, by rfl⟩ : syracuseStep 14669099 = 22003649) B22003649
theorem B1717567 : Blo 1717059 1717567 := bstep (se 1 (by rfl) ⟨1288175, by rfl⟩ : syracuseStep 1717567 = 2576351) B2576351
theorem B5797331 : Blo 1717059 5797331 := bstep (se 1 (by rfl) ⟨4347998, by rfl⟩ : syracuseStep 5797331 = 8695997) B8695997
theorem B1717735 : Blo 1717059 1717735 := bstep (se 1 (by rfl) ⟨1288301, by rfl⟩ : syracuseStep 1717735 = 2576603) B2576603
theorem B1717743 : Blo 1717059 1717743 := bstep (se 1 (by rfl) ⟨1288307, by rfl⟩ : syracuseStep 1717743 = 2576615) B2576615
theorem B1717851 : Blo 1717059 1717851 := bstep (se 1 (by rfl) ⟨1288388, by rfl⟩ : syracuseStep 1717851 = 2576777) B2576777
theorem B4126319 : Blo 1717059 4126319 := bstep (se 1 (by rfl) ⟨3094739, by rfl⟩ : syracuseStep 4126319 = 6189479) B6189479
theorem B1717915 : Blo 1717059 1717915 := bstep (se 1 (by rfl) ⟨1288436, by rfl⟩ : syracuseStep 1717915 = 2576873) B2576873
theorem B16733899 : Blo 1717059 16733899 := bstep (se 1 (by rfl) ⟨12550424, by rfl⟩ : syracuseStep 16733899 = 25100849) B25100849
theorem B5797601 : Blo 1717059 5797601 := bstep (se 2 (by rfl) ⟨2174100, by rfl⟩ : syracuseStep 5797601 = 4348201) B4348201
theorem B1717999 : Blo 1717059 1717999 := bstep (se 1 (by rfl) ⟨1288499, by rfl⟩ : syracuseStep 1717999 = 2576999) B2576999
theorem B3864311 : Blo 1717059 3864311 := bstep (se 1 (by rfl) ⟨2898233, by rfl⟩ : syracuseStep 3864311 = 5796467) B5796467
theorem B1718087 : Blo 1717059 1718087 := bstep (se 1 (by rfl) ⟨1288565, by rfl⟩ : syracuseStep 1718087 = 2577131) B2577131
theorem B2578247 : Blo 1717059 2578247 := bstep (se 1 (by rfl) ⟨1933685, by rfl⟩ : syracuseStep 2578247 = 3867371) B3867371
theorem B1718107 : Blo 1717059 1718107 := bstep (se 1 (by rfl) ⟨1288580, by rfl⟩ : syracuseStep 1718107 = 2577161) B2577161
theorem B20117393 : Blo 1717059 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B1718175 : Blo 1717059 1718175 := bstep (se 1 (by rfl) ⟨1288631, by rfl⟩ : syracuseStep 1718175 = 2577263) B2577263
theorem B3864491 : Blo 1717059 3864491 := bstep (se 1 (by rfl) ⟨2898368, by rfl⟩ : syracuseStep 3864491 = 5796737) B5796737
theorem B16521191 : Blo 1717059 16521191 := bstep (se 1 (by rfl) ⟨12390893, by rfl⟩ : syracuseStep 16521191 = 24781787) B24781787
theorem B52869131 : Blo 1717059 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B14669849 : Blo 1717059 14669849 := bstep (se 2 (by rfl) ⟨5501193, by rfl⟩ : syracuseStep 14669849 = 11002387) B11002387
theorem B3668009 : Blo 1717059 3668009 := bstep (se 2 (by rfl) ⟨1375503, by rfl⟩ : syracuseStep 3668009 = 2751007) B2751007
theorem B3864617 : Blo 1717059 3864617 := bstep (se 2 (by rfl) ⟨1449231, by rfl⟩ : syracuseStep 3864617 = 2898463) B2898463
theorem B1718343 : Blo 1717059 1718343 := bstep (se 1 (by rfl) ⟨1288757, by rfl⟩ : syracuseStep 1718343 = 2577515) B2577515
theorem B1718503 : Blo 1717059 1718503 := bstep (se 1 (by rfl) ⟨1288877, by rfl⟩ : syracuseStep 1718503 = 2577755) B2577755
theorem B1718687 : Blo 1717059 1718687 := bstep (se 1 (by rfl) ⟨1289015, by rfl⟩ : syracuseStep 1718687 = 2578031) B2578031
theorem B3865031 : Blo 1717059 3865031 := bstep (se 1 (by rfl) ⟨2898773, by rfl⟩ : syracuseStep 3865031 = 5797547) B5797547
theorem B1718735 : Blo 1717059 1718735 := bstep (se 1 (by rfl) ⟨1289051, by rfl⟩ : syracuseStep 1718735 = 2578103) B2578103
theorem B1718759 : Blo 1717059 1718759 := bstep (se 1 (by rfl) ⟨1289069, by rfl⟩ : syracuseStep 1718759 = 2578139) B2578139
theorem B1718875 : Blo 1717059 1718875 := bstep (se 1 (by rfl) ⟨1289156, by rfl⟩ : syracuseStep 1718875 = 2578313) B2578313
theorem B3865193 : Blo 1717059 3865193 := bstep (se 2 (by rfl) ⟨1449447, by rfl⟩ : syracuseStep 3865193 = 2898895) B2898895
theorem B1931935 : Blo 1717059 1931935 := bstep (se 1 (by rfl) ⟨1448951, by rfl⟩ : syracuseStep 1931935 = 2897903) B2897903
theorem B3865247 : Blo 1717059 3865247 := bstep (se 1 (by rfl) ⟨2898935, by rfl⟩ : syracuseStep 3865247 = 5797871) B5797871
theorem B1718943 : Blo 1717059 1718943 := bstep (se 1 (by rfl) ⟨1289207, by rfl⟩ : syracuseStep 1718943 = 2578415) B2578415
theorem B13040351 : Blo 1717059 13040351 := bstep (se 1 (by rfl) ⟨9780263, by rfl⟩ : syracuseStep 13040351 = 19560527) B19560527
theorem B3865391 : Blo 1717059 3865391 := bstep (se 1 (by rfl) ⟨2899043, by rfl⟩ : syracuseStep 3865391 = 5798087) B5798087
theorem B14130011 : Blo 1717059 14130011 := bstep (se 1 (by rfl) ⟨10597508, by rfl⟩ : syracuseStep 14130011 = 21195017) B21195017
theorem B1833851 : Blo 1717059 1833851 := bstep (se 1 (by rfl) ⟨1375388, by rfl⟩ : syracuseStep 1833851 = 2750777) B2750777
theorem B2063227 : Blo 1717059 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B49519511 : Blo 1717059 49519511 := bstep (se 1 (by rfl) ⟨37139633, by rfl⟩ : syracuseStep 49519511 = 74279267) B74279267
theorem B7437217 : Blo 1717059 7437217 := bstep (se 2 (by rfl) ⟨2788956, by rfl⟩ : syracuseStep 7437217 = 5577913) B5577913
theorem B8698913 : Blo 1717059 8698913 := bstep (se 2 (by rfl) ⟨3262092, by rfl⟩ : syracuseStep 8698913 = 6524185) B6524185
theorem B3865823 : Blo 1717059 3865823 := bstep (se 1 (by rfl) ⟨2899367, by rfl⟩ : syracuseStep 3865823 = 5798735) B5798735
theorem B3866039 : Blo 1717059 3866039 := bstep (se 1 (by rfl) ⟨2899529, by rfl⟩ : syracuseStep 3866039 = 5799059) B5799059
theorem B3866219 : Blo 1717059 3866219 := bstep (se 1 (by rfl) ⟨2899664, by rfl⟩ : syracuseStep 3866219 = 5799329) B5799329
theorem B5504669 : Blo 1717059 5504669 := bstep (se 3 (by rfl) ⟨1032125, by rfl⟩ : syracuseStep 5504669 = 2064251) B2064251
theorem B5799599 : Blo 1717059 5799599 := bstep (se 1 (by rfl) ⟨4349699, by rfl⟩ : syracuseStep 5799599 = 8699399) B8699399
theorem B1933087 : Blo 1717059 1933087 := bstep (se 1 (by rfl) ⟨1449815, by rfl⟩ : syracuseStep 1933087 = 2899631) B2899631
theorem B3866489 : Blo 1717059 3866489 := bstep (se 2 (by rfl) ⟨1449933, by rfl⟩ : syracuseStep 3866489 = 2899867) B2899867
theorem B3866579 : Blo 1717059 3866579 := bstep (se 1 (by rfl) ⟨2899934, by rfl⟩ : syracuseStep 3866579 = 5799869) B5799869
theorem B434864173 : Blo 1717059 434864173 := bstep (se 3 (by rfl) ⟨81537032, by rfl⟩ : syracuseStep 434864173 = 163074065) B163074065
theorem B9781357 : Blo 1717059 9781357 := bstep (se 3 (by rfl) ⟨1834004, by rfl⟩ : syracuseStep 9781357 = 3668009) B3668009
theorem B8700047 : Blo 1717059 8700047 := bstep (se 1 (by rfl) ⟨6525035, by rfl⟩ : syracuseStep 8700047 = 13050071) B13050071
theorem B6611105 : Blo 1717059 6611105 := bstep (se 2 (by rfl) ⟨2479164, by rfl⟩ : syracuseStep 6611105 = 4958329) B4958329
theorem B9789605 : Blo 1717059 9789605 := bstep (se 4 (by rfl) ⟨917775, by rfl⟩ : syracuseStep 9789605 = 1835551) B1835551
theorem B2900137 : Blo 1717059 2900137 := bstep (se 2 (by rfl) ⟨1087551, by rfl⟩ : syracuseStep 2900137 = 2175103) B2175103
theorem B75334063 : Blo 1717059 75334063 := bstep (se 1 (by rfl) ⟨56500547, by rfl⟩ : syracuseStep 75334063 = 113001095) B113001095
theorem B9781883 : Blo 1717059 9781883 := bstep (se 1 (by rfl) ⟨7336412, by rfl⟩ : syracuseStep 9781883 = 14672825) B14672825
theorem B8700695 : Blo 1717059 8700695 := bstep (se 1 (by rfl) ⟨6525521, by rfl⟩ : syracuseStep 8700695 = 13051043) B13051043
theorem B5505833 : Blo 1717059 5505833 := bstep (se 2 (by rfl) ⟨2064687, by rfl⟩ : syracuseStep 5505833 = 4129375) B4129375
theorem B5800841 : Blo 1717059 5800841 := bstep (se 2 (by rfl) ⟨2175315, by rfl⟩ : syracuseStep 5800841 = 4350631) B4350631
theorem B47039453 : Blo 1717059 47039453 := bstep (se 3 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 47039453 = 17639795) B17639795
theorem B4351097 : Blo 1717059 4351097 := bstep (se 2 (by rfl) ⟨1631661, by rfl⟩ : syracuseStep 4351097 = 3263323) B3263323
theorem B33023153 : Blo 1717059 33023153 := bstep (se 2 (by rfl) ⟨12383682, by rfl⟩ : syracuseStep 33023153 = 24767365) B24767365
theorem B13411595 : Blo 1717059 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B5801273 : Blo 1717059 5801273 := bstep (se 2 (by rfl) ⟨2175477, by rfl⟩ : syracuseStep 5801273 = 4350955) B4350955
theorem B11011409 : Blo 1717059 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B9782633 : Blo 1717059 9782633 := bstep (se 2 (by rfl) ⟨3668487, by rfl⟩ : syracuseStep 9782633 = 7336975) B7336975
theorem B11003465 : Blo 1717059 11003465 := bstep (se 2 (by rfl) ⟨4126299, by rfl⟩ : syracuseStep 11003465 = 8252599) B8252599
theorem B22021793 : Blo 1717059 22021793 := bstep (se 2 (by rfl) ⟨8258172, by rfl⟩ : syracuseStep 22021793 = 16516345) B16516345
theorem B8693567 : Blo 1717059 8693567 := bstep (se 1 (by rfl) ⟨6520175, by rfl⟩ : syracuseStep 8693567 = 13040351) B13040351
theorem B3262511 : Blo 1717059 3262511 := bstep (se 1 (by rfl) ⟨2446883, by rfl⟩ : syracuseStep 3262511 = 4893767) B4893767
theorem B29763773 : Blo 1717059 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B8702315 : Blo 1717059 8702315 := bstep (se 1 (by rfl) ⟨6526736, by rfl⟩ : syracuseStep 8702315 = 13053473) B13053473
theorem B62720419 : Blo 1717059 62720419 := bstep (se 1 (by rfl) ⟨47040314, by rfl⟩ : syracuseStep 62720419 = 94080629) B94080629
theorem B6523517 : Blo 1717059 6523517 := bstep (se 3 (by rfl) ⟨1223159, by rfl⟩ : syracuseStep 6523517 = 2446319) B2446319
theorem B2173807 : Blo 1717059 2173807 := bstep (se 1 (by rfl) ⟨1630355, by rfl⟩ : syracuseStep 2173807 = 3260711) B3260711
theorem B8260481 : Blo 1717059 8260481 := bstep (se 2 (by rfl) ⟨3097680, by rfl⟩ : syracuseStep 8260481 = 6195361) B6195361
theorem B10587347 : Blo 1717059 10587347 := bstep (se 1 (by rfl) ⟨7940510, by rfl⟩ : syracuseStep 10587347 = 15881021) B15881021
theorem B2575823 : Blo 1717059 2575823 := bstep (se 1 (by rfl) ⟨1931867, by rfl⟩ : syracuseStep 2575823 = 3863735) B3863735
theorem B62705117 : Blo 1717059 62705117 := bstep (se 3 (by rfl) ⟨11757209, by rfl⟩ : syracuseStep 62705117 = 23514419) B23514419
theorem B2575913 : Blo 1717059 2575913 := bstep (se 2 (by rfl) ⟨965967, by rfl⟩ : syracuseStep 2575913 = 1931935) B1931935
theorem B2576207 : Blo 1717059 2576207 := bstep (se 1 (by rfl) ⟨1932155, by rfl⟩ : syracuseStep 2576207 = 3864311) B3864311
theorem B22007645 : Blo 1717059 22007645 := bstep (se 3 (by rfl) ⟨4126433, by rfl⟩ : syracuseStep 22007645 = 8252867) B8252867
theorem B9916289 : Blo 1717059 9916289 := bstep (se 2 (by rfl) ⟨3718608, by rfl⟩ : syracuseStep 9916289 = 7437217) B7437217
theorem B2576327 : Blo 1717059 2576327 := bstep (se 1 (by rfl) ⟨1932245, by rfl⟩ : syracuseStep 2576327 = 3864491) B3864491
theorem B11014127 : Blo 1717059 11014127 := bstep (se 1 (by rfl) ⟨8260595, by rfl⟩ : syracuseStep 11014127 = 16521191) B16521191
theorem B35246087 : Blo 1717059 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B2576411 : Blo 1717059 2576411 := bstep (se 1 (by rfl) ⟨1932308, by rfl⟩ : syracuseStep 2576411 = 3864617) B3864617
theorem B22024457 : Blo 1717059 22024457 := bstep (se 2 (by rfl) ⟨8259171, by rfl⟩ : syracuseStep 22024457 = 16518343) B16518343
theorem B2576687 : Blo 1717059 2576687 := bstep (se 1 (by rfl) ⟨1932515, by rfl⟩ : syracuseStep 2576687 = 3865031) B3865031
theorem B2576795 : Blo 1717059 2576795 := bstep (se 1 (by rfl) ⟨1932596, by rfl⟩ : syracuseStep 2576795 = 3865193) B3865193
theorem B2576831 : Blo 1717059 2576831 := bstep (se 1 (by rfl) ⟨1932623, by rfl⟩ : syracuseStep 2576831 = 3865247) B3865247
theorem B18575831 : Blo 1717059 18575831 := bstep (se 1 (by rfl) ⟨13931873, by rfl⟩ : syracuseStep 18575831 = 27863747) B27863747
theorem B2576927 : Blo 1717059 2576927 := bstep (se 1 (by rfl) ⟨1932695, by rfl⟩ : syracuseStep 2576927 = 3865391) B3865391
theorem B2175655 : Blo 1717059 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B2577215 : Blo 1717059 2577215 := bstep (se 1 (by rfl) ⟨1932911, by rfl⟩ : syracuseStep 2577215 = 3865823) B3865823
theorem B37680029 : Blo 1717059 37680029 := bstep (se 3 (by rfl) ⟨7065005, by rfl⟩ : syracuseStep 37680029 = 14130011) B14130011
theorem B22311865 : Blo 1717059 22311865 := bstep (se 2 (by rfl) ⟨8366949, by rfl⟩ : syracuseStep 22311865 = 16733899) B16733899
theorem B2577359 : Blo 1717059 2577359 := bstep (se 1 (by rfl) ⟨1933019, by rfl⟩ : syracuseStep 2577359 = 3866039) B3866039
theorem B2577449 : Blo 1717059 2577449 := bstep (se 2 (by rfl) ⟨966543, by rfl⟩ : syracuseStep 2577449 = 1933087) B1933087
theorem B2577479 : Blo 1717059 2577479 := bstep (se 1 (by rfl) ⟨1933109, by rfl⟩ : syracuseStep 2577479 = 3866219) B3866219
theorem B2577659 : Blo 1717059 2577659 := bstep (se 1 (by rfl) ⟨1933244, by rfl⟩ : syracuseStep 2577659 = 3866489) B3866489
theorem B1717503 : Blo 1717059 1717503 := bstep (se 1 (by rfl) ⟨1288127, by rfl⟩ : syracuseStep 1717503 = 2576255) B2576255
theorem B2577719 : Blo 1717059 2577719 := bstep (se 1 (by rfl) ⟨1933289, by rfl⟩ : syracuseStep 2577719 = 3866579) B3866579
theorem B1717631 : Blo 1717059 1717631 := bstep (se 1 (by rfl) ⟨1288223, by rfl⟩ : syracuseStep 1717631 = 2576447) B2576447
theorem B2446843 : Blo 1717059 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B80426515 : Blo 1717059 80426515 := bstep (se 1 (by rfl) ⟨60319886, by rfl⟩ : syracuseStep 80426515 = 120639773) B120639773
theorem B1717787 : Blo 1717059 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B2578025 : Blo 1717059 2578025 := bstep (se 2 (by rfl) ⟨966759, by rfl⟩ : syracuseStep 2578025 = 1933519) B1933519
theorem B6526601 : Blo 1717059 6526601 := bstep (se 2 (by rfl) ⟨2447475, by rfl⟩ : syracuseStep 6526601 = 4894951) B4894951
theorem B1717967 : Blo 1717059 1717967 := bstep (se 1 (by rfl) ⟨1288475, by rfl⟩ : syracuseStep 1717967 = 2576951) B2576951
theorem B37214081 : Blo 1717059 37214081 := bstep (se 2 (by rfl) ⟨13955280, by rfl⟩ : syracuseStep 37214081 = 27910561) B27910561
theorem B4183979 : Blo 1717059 4183979 := bstep (se 1 (by rfl) ⟨3137984, by rfl⟩ : syracuseStep 4183979 = 6275969) B6275969
theorem B1718207 : Blo 1717059 1718207 := bstep (se 1 (by rfl) ⟨1288655, by rfl⟩ : syracuseStep 1718207 = 2577311) B2577311
theorem B1718335 : Blo 1717059 1718335 := bstep (se 1 (by rfl) ⟨1288751, by rfl⟩ : syracuseStep 1718335 = 2577503) B2577503
theorem B1718375 : Blo 1717059 1718375 := bstep (se 1 (by rfl) ⟨1288781, by rfl⟩ : syracuseStep 1718375 = 2577563) B2577563
theorem B2578559 : Blo 1717059 2578559 := bstep (se 1 (by rfl) ⟨1933919, by rfl⟩ : syracuseStep 2578559 = 3867839) B3867839
theorem B9779399 : Blo 1717059 9779399 := bstep (se 1 (by rfl) ⟨7334549, by rfl⟩ : syracuseStep 9779399 = 14669099) B14669099
theorem B3864887 : Blo 1717059 3864887 := bstep (se 1 (by rfl) ⟨2898665, by rfl⟩ : syracuseStep 3864887 = 5797331) B5797331
theorem B2750879 : Blo 1717059 2750879 := bstep (se 1 (by rfl) ⟨2063159, by rfl⟩ : syracuseStep 2750879 = 4126319) B4126319
theorem B3865067 : Blo 1717059 3865067 := bstep (se 1 (by rfl) ⟨2898800, by rfl⟩ : syracuseStep 3865067 = 5797601) B5797601
theorem B2750969 : Blo 1717059 2750969 := bstep (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) B2063227
theorem B18569735 : Blo 1717059 18569735 := bstep (se 1 (by rfl) ⟨13927301, by rfl⟩ : syracuseStep 18569735 = 27854603) B27854603
theorem B1718831 : Blo 1717059 1718831 := bstep (se 1 (by rfl) ⟨1289123, by rfl⟩ : syracuseStep 1718831 = 2578247) B2578247
theorem B9779899 : Blo 1717059 9779899 := bstep (se 1 (by rfl) ⟨7334924, by rfl⟩ : syracuseStep 9779899 = 14669849) B14669849
theorem B4889609 : Blo 1717059 4889609 := bstep (se 2 (by rfl) ⟨1833603, by rfl⟩ : syracuseStep 4889609 = 3667207) B3667207
theorem B4348991 : Blo 1717059 4348991 := bstep (se 1 (by rfl) ⟨3261743, by rfl⟩ : syracuseStep 4348991 = 6523487) B6523487
theorem B4349153 : Blo 1717059 4349153 := bstep (se 2 (by rfl) ⟨1630932, by rfl⟩ : syracuseStep 4349153 = 3261865) B3261865
theorem B33013007 : Blo 1717059 33013007 := bstep (se 1 (by rfl) ⟨24759755, by rfl⟩ : syracuseStep 33013007 = 49519511) B49519511
theorem B5799275 : Blo 1717059 5799275 := bstep (se 1 (by rfl) ⟨4349456, by rfl⟩ : syracuseStep 5799275 = 8698913) B8698913
theorem B4890223 : Blo 1717059 4890223 := bstep (se 1 (by rfl) ⟨3667667, by rfl⟩ : syracuseStep 4890223 = 7335335) B7335335
theorem B4890269 : Blo 1717059 4890269 := bstep (se 3 (by rfl) ⟨916925, by rfl⟩ : syracuseStep 4890269 = 1833851) B1833851
theorem B4349659 : Blo 1717059 4349659 := bstep (se 1 (by rfl) ⟨3262244, by rfl⟩ : syracuseStep 4349659 = 6524489) B6524489
theorem B3669779 : Blo 1717059 3669779 := bstep (se 1 (by rfl) ⟨2752334, by rfl⟩ : syracuseStep 3669779 = 5504669) B5504669
theorem B3866399 : Blo 1717059 3866399 := bstep (se 1 (by rfl) ⟨2899799, by rfl⟩ : syracuseStep 3866399 = 5799599) B5799599
theorem B5800031 : Blo 1717059 5800031 := bstep (se 1 (by rfl) ⟨4350023, by rfl⟩ : syracuseStep 5800031 = 8700047) B8700047
theorem B13041809 : Blo 1717059 13041809 := bstep (se 2 (by rfl) ⟨4890678, by rfl⟩ : syracuseStep 13041809 = 9781357) B9781357
theorem B3866849 : Blo 1717059 3866849 := bstep (se 2 (by rfl) ⟨1450068, by rfl⟩ : syracuseStep 3866849 = 2900137) B2900137
theorem B6521255 : Blo 1717059 6521255 := bstep (se 1 (by rfl) ⟨4890941, by rfl⟩ : syracuseStep 6521255 = 9781883) B9781883
theorem B17629613 : Blo 1717059 17629613 := bstep (se 3 (by rfl) ⟨3305552, by rfl⟩ : syracuseStep 17629613 = 6611105) B6611105
theorem B5800463 : Blo 1717059 5800463 := bstep (se 1 (by rfl) ⟨4350347, by rfl⟩ : syracuseStep 5800463 = 8700695) B8700695
theorem B3867227 : Blo 1717059 3867227 := bstep (se 1 (by rfl) ⟨2900420, by rfl⟩ : syracuseStep 3867227 = 5800841) B5800841
theorem B31359635 : Blo 1717059 31359635 := bstep (se 1 (by rfl) ⟨23519726, by rfl⟩ : syracuseStep 31359635 = 47039453) B47039453
theorem B2900731 : Blo 1717059 2900731 := bstep (se 1 (by rfl) ⟨2175548, by rfl⟩ : syracuseStep 2900731 = 4351097) B4351097
theorem B3867515 : Blo 1717059 3867515 := bstep (se 1 (by rfl) ⟨2900636, by rfl⟩ : syracuseStep 3867515 = 5801273) B5801273
theorem B2900873 : Blo 1717059 2900873 := bstep (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) B2175655
theorem B7340939 : Blo 1717059 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B6521755 : Blo 1717059 6521755 := bstep (se 1 (by rfl) ⟨4891316, by rfl⟩ : syracuseStep 6521755 = 9782633) B9782633
theorem B4351067 : Blo 1717059 4351067 := bstep (se 1 (by rfl) ⟨3263300, by rfl⟩ : syracuseStep 4351067 = 6526601) B6526601
theorem B14681195 : Blo 1717059 14681195 := bstep (se 1 (by rfl) ⟨11010896, by rfl⟩ : syracuseStep 14681195 = 22021793) B22021793
theorem B19842515 : Blo 1717059 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B5801543 : Blo 1717059 5801543 := bstep (se 1 (by rfl) ⟨4351157, by rfl⟩ : syracuseStep 5801543 = 8702315) B8702315
theorem B12379823 : Blo 1717059 12379823 := bstep (se 1 (by rfl) ⟨9284867, by rfl⟩ : syracuseStep 12379823 = 18569735) B18569735
theorem B5506987 : Blo 1717059 5506987 := bstep (se 1 (by rfl) ⟨4130240, by rfl⟩ : syracuseStep 5506987 = 8260481) B8260481
theorem B3262457 : Blo 1717059 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B107235353 : Blo 1717059 107235353 := bstep (se 2 (by rfl) ⟨40213257, by rfl⟩ : syracuseStep 107235353 = 80426515) B80426515
theorem B14682221 : Blo 1717059 14682221 := bstep (se 3 (by rfl) ⟨2752916, by rfl⟩ : syracuseStep 14682221 = 5505833) B5505833
theorem B7342751 : Blo 1717059 7342751 := bstep (se 1 (by rfl) ⟨5507063, by rfl⟩ : syracuseStep 7342751 = 11014127) B11014127
theorem B23497391 : Blo 1717059 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B14682971 : Blo 1717059 14682971 := bstep (se 1 (by rfl) ⟨11012228, by rfl⟩ : syracuseStep 14682971 = 22024457) B22024457
theorem B83627225 : Blo 1717059 83627225 := bstep (se 2 (by rfl) ⟨31360209, by rfl⟩ : syracuseStep 83627225 = 62720419) B62720419
theorem B100445417 : Blo 1717059 100445417 := bstep (se 2 (by rfl) ⟨37667031, by rfl⟩ : syracuseStep 100445417 = 75334063) B75334063
theorem B25120019 : Blo 1717059 25120019 := bstep (se 1 (by rfl) ⟨18840014, by rfl⟩ : syracuseStep 25120019 = 37680029) B37680029
theorem B22015435 : Blo 1717059 22015435 := bstep (se 1 (by rfl) ⟨16511576, by rfl⟩ : syracuseStep 22015435 = 33023153) B33023153
theorem B7335643 : Blo 1717059 7335643 := bstep (se 1 (by rfl) ⟨5501732, by rfl⟩ : syracuseStep 7335643 = 11003465) B11003465
theorem B7335677 : Blo 1717059 7335677 := bstep (se 3 (by rfl) ⟨1375439, by rfl⟩ : syracuseStep 7335677 = 2750879) B2750879
theorem B5795711 : Blo 1717059 5795711 := bstep (se 1 (by rfl) ⟨4346783, by rfl⟩ : syracuseStep 5795711 = 8693567) B8693567
theorem B29749153 : Blo 1717059 29749153 := bstep (se 2 (by rfl) ⟨11155932, by rfl⟩ : syracuseStep 29749153 = 22311865) B22311865
theorem B24809387 : Blo 1717059 24809387 := bstep (se 1 (by rfl) ⟨18607040, by rfl⟩ : syracuseStep 24809387 = 37214081) B37214081
theorem B7335917 : Blo 1717059 7335917 := bstep (se 3 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 7335917 = 2750969) B2750969
theorem B2175007 : Blo 1717059 2175007 := bstep (se 1 (by rfl) ⟨1631255, by rfl⟩ : syracuseStep 2175007 = 3262511) B3262511
theorem B2576591 : Blo 1717059 2576591 := bstep (se 1 (by rfl) ⟨1932443, by rfl⟩ : syracuseStep 2576591 = 3864887) B3864887
theorem B2576711 : Blo 1717059 2576711 := bstep (se 1 (by rfl) ⟨1932533, by rfl⟩ : syracuseStep 2576711 = 3865067) B3865067
theorem B7058231 : Blo 1717059 7058231 := bstep (se 1 (by rfl) ⟨5293673, by rfl⟩ : syracuseStep 7058231 = 10587347) B10587347
theorem B22008671 : Blo 1717059 22008671 := bstep (se 1 (by rfl) ⟨16506503, by rfl⟩ : syracuseStep 22008671 = 33013007) B33013007
theorem B1717215 : Blo 1717059 1717215 := bstep (se 1 (by rfl) ⟨1287911, by rfl⟩ : syracuseStep 1717215 = 2575823) B2575823
theorem B1717275 : Blo 1717059 1717275 := bstep (se 1 (by rfl) ⟨1287956, by rfl⟩ : syracuseStep 1717275 = 2575913) B2575913
theorem B2446519 : Blo 1717059 2446519 := bstep (se 1 (by rfl) ⟨1834889, by rfl⟩ : syracuseStep 2446519 = 3669779) B3669779
theorem B2577599 : Blo 1717059 2577599 := bstep (se 1 (by rfl) ⟨1933199, by rfl⟩ : syracuseStep 2577599 = 3866399) B3866399
theorem B1717471 : Blo 1717059 1717471 := bstep (se 1 (by rfl) ⟨1288103, by rfl⟩ : syracuseStep 1717471 = 2576207) B2576207
theorem B1717551 : Blo 1717059 1717551 := bstep (se 1 (by rfl) ⟨1288163, by rfl⟩ : syracuseStep 1717551 = 2576327) B2576327
theorem B1717607 : Blo 1717059 1717607 := bstep (se 1 (by rfl) ⟨1288205, by rfl⟩ : syracuseStep 1717607 = 2576411) B2576411
theorem B579818897 : Blo 1717059 579818897 := bstep (se 2 (by rfl) ⟨217432086, by rfl⟩ : syracuseStep 579818897 = 434864173) B434864173
theorem B6526403 : Blo 1717059 6526403 := bstep (se 1 (by rfl) ⟨4894802, by rfl⟩ : syracuseStep 6526403 = 9789605) B9789605
theorem B1717791 : Blo 1717059 1717791 := bstep (se 1 (by rfl) ⟨1288343, by rfl⟩ : syracuseStep 1717791 = 2576687) B2576687
theorem B1717863 : Blo 1717059 1717863 := bstep (se 1 (by rfl) ⟨1288397, by rfl⟩ : syracuseStep 1717863 = 2576795) B2576795
theorem B1717887 : Blo 1717059 1717887 := bstep (se 1 (by rfl) ⟨1288415, by rfl⟩ : syracuseStep 1717887 = 2576831) B2576831
theorem B1717951 : Blo 1717059 1717951 := bstep (se 1 (by rfl) ⟨1288463, by rfl⟩ : syracuseStep 1717951 = 2576927) B2576927
theorem B1718143 : Blo 1717059 1718143 := bstep (se 1 (by rfl) ⟨1288607, by rfl⟩ : syracuseStep 1718143 = 2577215) B2577215
theorem B1718239 : Blo 1717059 1718239 := bstep (se 1 (by rfl) ⟨1288679, by rfl⟩ : syracuseStep 1718239 = 2577359) B2577359
theorem B1718299 : Blo 1717059 1718299 := bstep (se 1 (by rfl) ⟨1288724, by rfl⟩ : syracuseStep 1718299 = 2577449) B2577449
theorem B35764253 : Blo 1717059 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B1718319 : Blo 1717059 1718319 := bstep (se 1 (by rfl) ⟨1288739, by rfl⟩ : syracuseStep 1718319 = 2577479) B2577479
theorem B1718439 : Blo 1717059 1718439 := bstep (se 1 (by rfl) ⟨1288829, by rfl⟩ : syracuseStep 1718439 = 2577659) B2577659
theorem B1718479 : Blo 1717059 1718479 := bstep (se 1 (by rfl) ⟨1288859, by rfl⟩ : syracuseStep 1718479 = 2577719) B2577719
theorem B13039865 : Blo 1717059 13039865 := bstep (se 2 (by rfl) ⟨4889949, by rfl⟩ : syracuseStep 13039865 = 9779899) B9779899
theorem B1718683 : Blo 1717059 1718683 := bstep (se 1 (by rfl) ⟨1289012, by rfl⟩ : syracuseStep 1718683 = 2578025) B2578025
theorem B2898409 : Blo 1717059 2898409 := bstep (se 2 (by rfl) ⟨1086903, by rfl⟩ : syracuseStep 2898409 = 2173807) B2173807
theorem B49535549 : Blo 1717059 49535549 := bstep (se 3 (by rfl) ⟨9287915, by rfl⟩ : syracuseStep 49535549 = 18575831) B18575831
theorem B1719039 : Blo 1717059 1719039 := bstep (se 1 (by rfl) ⟨1289279, by rfl⟩ : syracuseStep 1719039 = 2578559) B2578559
theorem B6519599 : Blo 1717059 6519599 := bstep (se 1 (by rfl) ⟨4889699, by rfl⟩ : syracuseStep 6519599 = 9779399) B9779399
theorem B4349011 : Blo 1717059 4349011 := bstep (se 1 (by rfl) ⟨3261758, by rfl⟩ : syracuseStep 4349011 = 6523517) B6523517
theorem B44629109 : Blo 1717059 44629109 := bstep (se 5 (by rfl) ⟨2091989, by rfl⟩ : syracuseStep 44629109 = 4183979) B4183979
theorem B3259739 : Blo 1717059 3259739 := bstep (se 1 (by rfl) ⟨2444804, by rfl⟩ : syracuseStep 3259739 = 4889609) B4889609
theorem B2899327 : Blo 1717059 2899327 := bstep (se 1 (by rfl) ⟨2174495, by rfl⟩ : syracuseStep 2899327 = 4348991) B4348991
theorem B6520297 : Blo 1717059 6520297 := bstep (se 2 (by rfl) ⟨2445111, by rfl⟩ : syracuseStep 6520297 = 4890223) B4890223
theorem B2899435 : Blo 1717059 2899435 := bstep (se 1 (by rfl) ⟨2174576, by rfl⟩ : syracuseStep 2899435 = 4349153) B4349153
theorem B3866183 : Blo 1717059 3866183 := bstep (se 1 (by rfl) ⟨2899637, by rfl⟩ : syracuseStep 3866183 = 5799275) B5799275
theorem B5799545 : Blo 1717059 5799545 := bstep (se 2 (by rfl) ⟨2174829, by rfl⟩ : syracuseStep 5799545 = 4349659) B4349659
theorem B41803411 : Blo 1717059 41803411 := bstep (se 1 (by rfl) ⟨31352558, by rfl⟩ : syracuseStep 41803411 = 62705117) B62705117
theorem B3260179 : Blo 1717059 3260179 := bstep (se 1 (by rfl) ⟨2445134, by rfl⟩ : syracuseStep 3260179 = 4890269) B4890269
theorem B14671763 : Blo 1717059 14671763 := bstep (se 1 (by rfl) ⟨11003822, by rfl⟩ : syracuseStep 14671763 = 22007645) B22007645
theorem B6610859 : Blo 1717059 6610859 := bstep (se 1 (by rfl) ⟨4958144, by rfl⟩ : syracuseStep 6610859 = 9916289) B9916289
theorem B2900009 : Blo 1717059 2900009 := bstep (se 2 (by rfl) ⟨1087503, by rfl⟩ : syracuseStep 2900009 = 2175007) B2175007
theorem B3866687 : Blo 1717059 3866687 := bstep (se 1 (by rfl) ⟨2900015, by rfl⟩ : syracuseStep 3866687 = 5800031) B5800031
theorem B3866975 : Blo 1717059 3866975 := bstep (se 1 (by rfl) ⟨2900231, by rfl⟩ : syracuseStep 3866975 = 5800463) B5800463
theorem B20906423 : Blo 1717059 20906423 := bstep (se 1 (by rfl) ⟨15679817, by rfl⟩ : syracuseStep 20906423 = 31359635) B31359635
theorem B14672447 : Blo 1717059 14672447 := bstep (se 1 (by rfl) ⟨11004335, by rfl⟩ : syracuseStep 14672447 = 22008671) B22008671
theorem B1933915 : Blo 1717059 1933915 := bstep (se 1 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 1933915 = 2900873) B2900873
theorem B2900711 : Blo 1717059 2900711 := bstep (se 1 (by rfl) ⟨2175533, by rfl⟩ : syracuseStep 2900711 = 4351067) B4351067
theorem B4350935 : Blo 1717059 4350935 := bstep (se 1 (by rfl) ⟨3263201, by rfl⟩ : syracuseStep 4350935 = 6526403) B6526403
theorem B3867641 : Blo 1717059 3867641 := bstep (se 2 (by rfl) ⟨1450365, by rfl⟩ : syracuseStep 3867641 = 2900731) B2900731
theorem B3867695 : Blo 1717059 3867695 := bstep (se 1 (by rfl) ⟨2900771, by rfl⟩ : syracuseStep 3867695 = 5801543) B5801543
theorem B8693243 : Blo 1717059 8693243 := bstep (se 1 (by rfl) ⟨6519932, by rfl⟩ : syracuseStep 8693243 = 13039865) B13039865
theorem B3262025 : Blo 1717059 3262025 := bstep (se 2 (by rfl) ⟨1223259, by rfl⟩ : syracuseStep 3262025 = 2446519) B2446519
theorem B33023699 : Blo 1717059 33023699 := bstep (se 1 (by rfl) ⟨24767774, by rfl⟩ : syracuseStep 33023699 = 49535549) B49535549
theorem B15664927 : Blo 1717059 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B29353913 : Blo 1717059 29353913 := bstep (se 2 (by rfl) ⟨11007717, by rfl⟩ : syracuseStep 29353913 = 22015435) B22015435
theorem B8693729 : Blo 1717059 8693729 := bstep (se 2 (by rfl) ⟨3260148, by rfl⟩ : syracuseStep 8693729 = 6520297) B6520297
theorem B66963611 : Blo 1717059 66963611 := bstep (se 1 (by rfl) ⟨50222708, by rfl⟩ : syracuseStep 66963611 = 100445417) B100445417
theorem B16746679 : Blo 1717059 16746679 := bstep (se 1 (by rfl) ⟨12560009, by rfl⟩ : syracuseStep 16746679 = 25120019) B25120019
theorem B2173159 : Blo 1717059 2173159 := bstep (se 1 (by rfl) ⟨1629869, by rfl⟩ : syracuseStep 2173159 = 3259739) B3259739
theorem B7342649 : Blo 1717059 7342649 := bstep (se 2 (by rfl) ⟨2753493, by rfl⟩ : syracuseStep 7342649 = 5506987) B5506987
theorem B8694539 : Blo 1717059 8694539 := bstep (se 1 (by rfl) ⟨6520904, by rfl⟩ : syracuseStep 8694539 = 13041809) B13041809
theorem B4705487 : Blo 1717059 4705487 := bstep (se 1 (by rfl) ⟨3529115, by rfl⟩ : syracuseStep 4705487 = 7058231) B7058231
theorem B4893959 : Blo 1717059 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B8253215 : Blo 1717059 8253215 := bstep (se 1 (by rfl) ⟨6189911, by rfl⟩ : syracuseStep 8253215 = 12379823) B12379823
theorem B8695673 : Blo 1717059 8695673 := bstep (se 2 (by rfl) ⟨3260877, by rfl⟩ : syracuseStep 8695673 = 6521755) B6521755
theorem B23842835 : Blo 1717059 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B4895167 : Blo 1717059 4895167 := bstep (se 1 (by rfl) ⟨3671375, by rfl⟩ : syracuseStep 4895167 = 7342751) B7342751
theorem B4346399 : Blo 1717059 4346399 := bstep (se 1 (by rfl) ⟨3259799, by rfl⟩ : syracuseStep 4346399 = 6519599) B6519599
theorem B55751483 : Blo 1717059 55751483 := bstep (se 1 (by rfl) ⟨41813612, by rfl⟩ : syracuseStep 55751483 = 83627225) B83627225
theorem B4346905 : Blo 1717059 4346905 := bstep (se 2 (by rfl) ⟨1630089, by rfl⟩ : syracuseStep 4346905 = 3260179) B3260179
theorem B2577455 : Blo 1717059 2577455 := bstep (se 1 (by rfl) ⟨1933091, by rfl⟩ : syracuseStep 2577455 = 3866183) B3866183
theorem B3863807 : Blo 1717059 3863807 := bstep (se 1 (by rfl) ⟨2897855, by rfl⟩ : syracuseStep 3863807 = 5795711) B5795711
theorem B1717727 : Blo 1717059 1717727 := bstep (se 1 (by rfl) ⟨1288295, by rfl⟩ : syracuseStep 1717727 = 2576591) B2576591
theorem B2577899 : Blo 1717059 2577899 := bstep (se 1 (by rfl) ⟨1933424, by rfl⟩ : syracuseStep 2577899 = 3866849) B3866849
theorem B1717807 : Blo 1717059 1717807 := bstep (se 1 (by rfl) ⟨1288355, by rfl⟩ : syracuseStep 1717807 = 2576711) B2576711
theorem B4347503 : Blo 1717059 4347503 := bstep (se 1 (by rfl) ⟨3260627, by rfl⟩ : syracuseStep 4347503 = 6521255) B6521255
theorem B11753075 : Blo 1717059 11753075 := bstep (se 1 (by rfl) ⟨8814806, by rfl⟩ : syracuseStep 11753075 = 17629613) B17629613
theorem B2578151 : Blo 1717059 2578151 := bstep (se 1 (by rfl) ⟨1933613, by rfl⟩ : syracuseStep 2578151 = 3867227) B3867227
theorem B2578343 : Blo 1717059 2578343 := bstep (se 1 (by rfl) ⟨1933757, by rfl⟩ : syracuseStep 2578343 = 3867515) B3867515
theorem B3864545 : Blo 1717059 3864545 := bstep (se 2 (by rfl) ⟨1449204, by rfl⟩ : syracuseStep 3864545 = 2898409) B2898409
theorem B9787463 : Blo 1717059 9787463 := bstep (se 1 (by rfl) ⟨7340597, by rfl⟩ : syracuseStep 9787463 = 14681195) B14681195
theorem B1718399 : Blo 1717059 1718399 := bstep (se 1 (by rfl) ⟨1288799, by rfl⟩ : syracuseStep 1718399 = 2577599) B2577599
theorem B386545931 : Blo 1717059 386545931 := bstep (se 1 (by rfl) ⟨289909448, by rfl⟩ : syracuseStep 386545931 = 579818897) B579818897
theorem B13228343 : Blo 1717059 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B71490235 : Blo 1717059 71490235 := bstep (se 1 (by rfl) ⟨53617676, by rfl⟩ : syracuseStep 71490235 = 107235353) B107235353
theorem B9788147 : Blo 1717059 9788147 := bstep (se 1 (by rfl) ⟨7341110, by rfl⟩ : syracuseStep 9788147 = 14682221) B14682221
theorem B5798681 : Blo 1717059 5798681 := bstep (se 2 (by rfl) ⟨2174505, by rfl⟩ : syracuseStep 5798681 = 4349011) B4349011
theorem B3865769 : Blo 1717059 3865769 := bstep (se 2 (by rfl) ⟨1449663, by rfl⟩ : syracuseStep 3865769 = 2899327) B2899327
theorem B9788647 : Blo 1717059 9788647 := bstep (se 1 (by rfl) ⟨7341485, by rfl⟩ : syracuseStep 9788647 = 14682971) B14682971
theorem B3865913 : Blo 1717059 3865913 := bstep (se 2 (by rfl) ⟨1449717, by rfl⟩ : syracuseStep 3865913 = 2899435) B2899435
theorem B29752739 : Blo 1717059 29752739 := bstep (se 1 (by rfl) ⟨22314554, by rfl⟩ : syracuseStep 29752739 = 44629109) B44629109
theorem B55737881 : Blo 1717059 55737881 := bstep (se 2 (by rfl) ⟨20901705, by rfl⟩ : syracuseStep 55737881 = 41803411) B41803411
theorem B9780857 : Blo 1717059 9780857 := bstep (se 2 (by rfl) ⟨3667821, by rfl⟩ : syracuseStep 9780857 = 7335643) B7335643
theorem B3866363 : Blo 1717059 3866363 := bstep (se 1 (by rfl) ⟨2899772, by rfl⟩ : syracuseStep 3866363 = 5799545) B5799545
theorem B66158365 : Blo 1717059 66158365 := bstep (se 3 (by rfl) ⟨12404693, by rfl⟩ : syracuseStep 66158365 = 24809387) B24809387
theorem B4890451 : Blo 1717059 4890451 := bstep (se 1 (by rfl) ⟨3667838, by rfl⟩ : syracuseStep 4890451 = 7335677) B7335677
theorem B39665537 : Blo 1717059 39665537 := bstep (se 2 (by rfl) ⟨14874576, by rfl⟩ : syracuseStep 39665537 = 29749153) B29749153
theorem B9781175 : Blo 1717059 9781175 := bstep (se 1 (by rfl) ⟨7335881, by rfl⟩ : syracuseStep 9781175 = 14671763) B14671763
theorem B4407239 : Blo 1717059 4407239 := bstep (se 1 (by rfl) ⟨3305429, by rfl⟩ : syracuseStep 4407239 = 6610859) B6610859
theorem B8699885 : Blo 1717059 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B4890611 : Blo 1717059 4890611 := bstep (se 1 (by rfl) ⟨3667958, by rfl⟩ : syracuseStep 4890611 = 7335917) B7335917
theorem B1933339 : Blo 1717059 1933339 := bstep (se 1 (by rfl) ⟨1450004, by rfl⟩ : syracuseStep 1933339 = 2900009) B2900009
theorem B9781631 : Blo 1717059 9781631 := bstep (se 1 (by rfl) ⟨7336223, by rfl⟩ : syracuseStep 9781631 = 14672447) B14672447
theorem B178569629 : Blo 1717059 178569629 := bstep (se 3 (by rfl) ⟨33481805, by rfl⟩ : syracuseStep 178569629 = 66963611) B66963611
theorem B1933807 : Blo 1717059 1933807 := bstep (se 1 (by rfl) ⟨1450355, by rfl⟩ : syracuseStep 1933807 = 2900711) B2900711
theorem B37167655 : Blo 1717059 37167655 := bstep (se 1 (by rfl) ⟨27875741, by rfl⟩ : syracuseStep 37167655 = 55751483) B55751483
theorem B2900623 : Blo 1717059 2900623 := bstep (se 1 (by rfl) ⟨2175467, by rfl⟩ : syracuseStep 2900623 = 4350935) B4350935
theorem B13050557 : Blo 1717059 13050557 := bstep (se 3 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 13050557 = 4893959) B4893959
theorem B257697287 : Blo 1717059 257697287 := bstep (se 1 (by rfl) ⟨193272965, by rfl⟩ : syracuseStep 257697287 = 386545931) B386545931
theorem B13051529 : Blo 1717059 13051529 := bstep (se 2 (by rfl) ⟨4894323, by rfl⟩ : syracuseStep 13051529 = 9788647) B9788647
theorem B19835159 : Blo 1717059 19835159 := bstep (se 1 (by rfl) ⟨14876369, by rfl⟩ : syracuseStep 19835159 = 29752739) B29752739
theorem B15895223 : Blo 1717059 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B13937615 : Blo 1717059 13937615 := bstep (se 1 (by rfl) ⟨10453211, by rfl⟩ : syracuseStep 13937615 = 20906423) B20906423
theorem B2575871 : Blo 1717059 2575871 := bstep (se 1 (by rfl) ⟨1931903, by rfl⟩ : syracuseStep 2575871 = 3863807) B3863807
theorem B5795495 : Blo 1717059 5795495 := bstep (se 1 (by rfl) ⟨4346621, by rfl⟩ : syracuseStep 5795495 = 8693243) B8693243
theorem B2174683 : Blo 1717059 2174683 := bstep (se 1 (by rfl) ⟨1631012, by rfl⟩ : syracuseStep 2174683 = 3262025) B3262025
theorem B7835383 : Blo 1717059 7835383 := bstep (se 1 (by rfl) ⟨5876537, by rfl⟩ : syracuseStep 7835383 = 11753075) B11753075
theorem B22015799 : Blo 1717059 22015799 := bstep (se 1 (by rfl) ⟨16511849, by rfl⟩ : syracuseStep 22015799 = 33023699) B33023699
theorem B5795819 : Blo 1717059 5795819 := bstep (se 1 (by rfl) ⟨4346864, by rfl⟩ : syracuseStep 5795819 = 8693729) B8693729
theorem B2576363 : Blo 1717059 2576363 := bstep (se 1 (by rfl) ⟨1932272, by rfl⟩ : syracuseStep 2576363 = 3864545) B3864545
theorem B5795873 : Blo 1717059 5795873 := bstep (se 2 (by rfl) ⟨2173452, by rfl⟩ : syracuseStep 5795873 = 4346905) B4346905
theorem B6524975 : Blo 1717059 6524975 := bstep (se 1 (by rfl) ⟨4893731, by rfl⟩ : syracuseStep 6524975 = 9787463) B9787463
theorem B8818895 : Blo 1717059 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B4895099 : Blo 1717059 4895099 := bstep (se 1 (by rfl) ⟨3671324, by rfl⟩ : syracuseStep 4895099 = 7342649) B7342649
theorem B6525431 : Blo 1717059 6525431 := bstep (se 1 (by rfl) ⟨4894073, by rfl⟩ : syracuseStep 6525431 = 9788147) B9788147
theorem B5796359 : Blo 1717059 5796359 := bstep (se 1 (by rfl) ⟨4347269, by rfl⟩ : syracuseStep 5796359 = 8694539) B8694539
theorem B2577179 : Blo 1717059 2577179 := bstep (se 1 (by rfl) ⟨1932884, by rfl⟩ : syracuseStep 2577179 = 3865769) B3865769
theorem B2577275 : Blo 1717059 2577275 := bstep (se 1 (by rfl) ⟨1932956, by rfl⟩ : syracuseStep 2577275 = 3865913) B3865913
theorem B20886569 : Blo 1717059 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B2577575 : Blo 1717059 2577575 := bstep (se 1 (by rfl) ⟨1933181, by rfl⟩ : syracuseStep 2577575 = 3866363) B3866363
theorem B5502143 : Blo 1717059 5502143 := bstep (se 1 (by rfl) ⟨4126607, by rfl⟩ : syracuseStep 5502143 = 8253215) B8253215
theorem B5797115 : Blo 1717059 5797115 := bstep (se 1 (by rfl) ⟨4347836, by rfl⟩ : syracuseStep 5797115 = 8695673) B8695673
theorem B2938159 : Blo 1717059 2938159 := bstep (se 1 (by rfl) ⟨2203619, by rfl⟩ : syracuseStep 2938159 = 4407239) B4407239
theorem B2577791 : Blo 1717059 2577791 := bstep (se 1 (by rfl) ⟨1933343, by rfl⟩ : syracuseStep 2577791 = 3866687) B3866687
theorem B2577983 : Blo 1717059 2577983 := bstep (se 1 (by rfl) ⟨1933487, by rfl⟩ : syracuseStep 2577983 = 3866975) B3866975
theorem B22328905 : Blo 1717059 22328905 := bstep (se 2 (by rfl) ⟨8373339, by rfl⟩ : syracuseStep 22328905 = 16746679) B16746679
theorem B2897545 : Blo 1717059 2897545 := bstep (se 2 (by rfl) ⟨1086579, by rfl⟩ : syracuseStep 2897545 = 2173159) B2173159
theorem B2897599 : Blo 1717059 2897599 := bstep (se 1 (by rfl) ⟨2173199, by rfl⟩ : syracuseStep 2897599 = 4346399) B4346399
theorem B6526889 : Blo 1717059 6526889 := bstep (se 2 (by rfl) ⟨2447583, by rfl⟩ : syracuseStep 6526889 = 4895167) B4895167
theorem B2578427 : Blo 1717059 2578427 := bstep (se 1 (by rfl) ⟨1933820, by rfl⟩ : syracuseStep 2578427 = 3867641) B3867641
theorem B1718303 : Blo 1717059 1718303 := bstep (se 1 (by rfl) ⟨1288727, by rfl⟩ : syracuseStep 1718303 = 2577455) B2577455
theorem B2578463 : Blo 1717059 2578463 := bstep (se 1 (by rfl) ⟨1933847, by rfl⟩ : syracuseStep 2578463 = 3867695) B3867695
theorem B2578553 : Blo 1717059 2578553 := bstep (se 2 (by rfl) ⟨966957, by rfl⟩ : syracuseStep 2578553 = 1933915) B1933915
theorem B95320313 : Blo 1717059 95320313 := bstep (se 2 (by rfl) ⟨35745117, by rfl⟩ : syracuseStep 95320313 = 71490235) B71490235
theorem B1718599 : Blo 1717059 1718599 := bstep (se 1 (by rfl) ⟨1288949, by rfl⟩ : syracuseStep 1718599 = 2577899) B2577899
theorem B2898335 : Blo 1717059 2898335 := bstep (se 1 (by rfl) ⟨2173751, by rfl⟩ : syracuseStep 2898335 = 4347503) B4347503
theorem B1718767 : Blo 1717059 1718767 := bstep (se 1 (by rfl) ⟨1289075, by rfl⟩ : syracuseStep 1718767 = 2578151) B2578151
theorem B1718895 : Blo 1717059 1718895 := bstep (se 1 (by rfl) ⟨1289171, by rfl⟩ : syracuseStep 1718895 = 2578343) B2578343
theorem B19569275 : Blo 1717059 19569275 := bstep (se 1 (by rfl) ⟨14676956, by rfl⟩ : syracuseStep 19569275 = 29353913) B29353913
theorem B3865787 : Blo 1717059 3865787 := bstep (se 1 (by rfl) ⟨2899340, by rfl⟩ : syracuseStep 3865787 = 5798681) B5798681
theorem B3136991 : Blo 1717059 3136991 := bstep (se 1 (by rfl) ⟨2352743, by rfl⟩ : syracuseStep 3136991 = 4705487) B4705487
theorem B37158587 : Blo 1717059 37158587 := bstep (se 1 (by rfl) ⟨27868940, by rfl⟩ : syracuseStep 37158587 = 55737881) B55737881
theorem B88211153 : Blo 1717059 88211153 := bstep (se 2 (by rfl) ⟨33079182, by rfl⟩ : syracuseStep 88211153 = 66158365) B66158365
theorem B6520571 : Blo 1717059 6520571 := bstep (se 1 (by rfl) ⟨4890428, by rfl⟩ : syracuseStep 6520571 = 9780857) B9780857
theorem B6520601 : Blo 1717059 6520601 := bstep (se 2 (by rfl) ⟨2445225, by rfl⟩ : syracuseStep 6520601 = 4890451) B4890451
theorem B26443691 : Blo 1717059 26443691 := bstep (se 1 (by rfl) ⟨19832768, by rfl⟩ : syracuseStep 26443691 = 39665537) B39665537
theorem B6520783 : Blo 1717059 6520783 := bstep (se 1 (by rfl) ⟨4890587, by rfl⟩ : syracuseStep 6520783 = 9781175) B9781175
theorem B5799923 : Blo 1717059 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B3260407 : Blo 1717059 3260407 := bstep (se 1 (by rfl) ⟨2445305, by rfl⟩ : syracuseStep 3260407 = 4890611) B4890611
theorem B4349983 : Blo 1717059 4349983 := bstep (se 1 (by rfl) ⟨3262487, by rfl⟩ : syracuseStep 4349983 = 6524975) B6524975
theorem B6521087 : Blo 1717059 6521087 := bstep (se 1 (by rfl) ⟨4890815, by rfl⟩ : syracuseStep 6521087 = 9781631) B9781631
theorem B119046419 : Blo 1717059 119046419 := bstep (se 1 (by rfl) ⟨89284814, by rfl⟩ : syracuseStep 119046419 = 178569629) B178569629
theorem B4350287 : Blo 1717059 4350287 := bstep (se 1 (by rfl) ⟨3262715, by rfl⟩ : syracuseStep 4350287 = 6525431) B6525431
theorem B8700371 : Blo 1717059 8700371 := bstep (se 1 (by rfl) ⟨6525278, by rfl⟩ : syracuseStep 8700371 = 13050557) B13050557
theorem B3867497 : Blo 1717059 3867497 := bstep (se 2 (by rfl) ⟨1450311, by rfl⟩ : syracuseStep 3867497 = 2900623) B2900623
theorem B8701019 : Blo 1717059 8701019 := bstep (se 1 (by rfl) ⟨6525764, by rfl⟩ : syracuseStep 8701019 = 13051529) B13051529
theorem B4351259 : Blo 1717059 4351259 := bstep (se 1 (by rfl) ⟨3263444, by rfl⟩ : syracuseStep 4351259 = 6526889) B6526889
theorem B63546875 : Blo 1717059 63546875 := bstep (se 1 (by rfl) ⟨47660156, by rfl⟩ : syracuseStep 63546875 = 95320313) B95320313
theorem B3917545 : Blo 1717059 3917545 := bstep (se 2 (by rfl) ⟨1469079, by rfl⟩ : syracuseStep 3917545 = 2938159) B2938159
theorem B9291743 : Blo 1717059 9291743 := bstep (se 1 (by rfl) ⟨6968807, by rfl⟩ : syracuseStep 9291743 = 13937615) B13937615
theorem B29771873 : Blo 1717059 29771873 := bstep (se 2 (by rfl) ⟨11164452, by rfl⟩ : syracuseStep 29771873 = 22328905) B22328905
theorem B10447177 : Blo 1717059 10447177 := bstep (se 2 (by rfl) ⟨3917691, by rfl⟩ : syracuseStep 10447177 = 7835383) B7835383
theorem B8694377 : Blo 1717059 8694377 := bstep (se 2 (by rfl) ⟨3260391, by rfl⟩ : syracuseStep 8694377 = 6520783) B6520783
theorem B3263399 : Blo 1717059 3263399 := bstep (se 1 (by rfl) ⟨2447549, by rfl⟩ : syracuseStep 3263399 = 4895099) B4895099
theorem B49556873 : Blo 1717059 49556873 := bstep (se 2 (by rfl) ⟨18583827, by rfl⟩ : syracuseStep 49556873 = 37167655) B37167655
theorem B171798191 : Blo 1717059 171798191 := bstep (se 1 (by rfl) ⟨128848643, by rfl⟩ : syracuseStep 171798191 = 257697287) B257697287
theorem B13046183 : Blo 1717059 13046183 := bstep (se 1 (by rfl) ⟨9784637, by rfl⟩ : syracuseStep 13046183 = 19569275) B19569275
theorem B10596815 : Blo 1717059 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B235229741 : Blo 1717059 235229741 := bstep (se 3 (by rfl) ⟨44105576, by rfl⟩ : syracuseStep 235229741 = 88211153) B88211153
theorem B2577191 : Blo 1717059 2577191 := bstep (se 1 (by rfl) ⟨1932893, by rfl⟩ : syracuseStep 2577191 = 3865787) B3865787
theorem B3863393 : Blo 1717059 3863393 := bstep (se 2 (by rfl) ⟨1448772, by rfl⟩ : syracuseStep 3863393 = 2897545) B2897545
theorem B3863465 : Blo 1717059 3863465 := bstep (se 2 (by rfl) ⟨1448799, by rfl⟩ : syracuseStep 3863465 = 2897599) B2897599
theorem B33461237 : Blo 1717059 33461237 := bstep (se 5 (by rfl) ⟨1568495, by rfl⟩ : syracuseStep 33461237 = 3136991) B3136991
theorem B1717247 : Blo 1717059 1717247 := bstep (se 1 (by rfl) ⟨1287935, by rfl⟩ : syracuseStep 1717247 = 2575871) B2575871
theorem B3863663 : Blo 1717059 3863663 := bstep (se 1 (by rfl) ⟨2897747, by rfl⟩ : syracuseStep 3863663 = 5795495) B5795495
theorem B4347047 : Blo 1717059 4347047 := bstep (se 1 (by rfl) ⟨3260285, by rfl⟩ : syracuseStep 4347047 = 6520571) B6520571
theorem B4347067 : Blo 1717059 4347067 := bstep (se 1 (by rfl) ⟨3260300, by rfl⟩ : syracuseStep 4347067 = 6520601) B6520601
theorem B14677199 : Blo 1717059 14677199 := bstep (se 1 (by rfl) ⟨11007899, by rfl⟩ : syracuseStep 14677199 = 22015799) B22015799
theorem B3863879 : Blo 1717059 3863879 := bstep (se 1 (by rfl) ⟨2897909, by rfl⟩ : syracuseStep 3863879 = 5795819) B5795819
theorem B1717575 : Blo 1717059 1717575 := bstep (se 1 (by rfl) ⟨1288181, by rfl⟩ : syracuseStep 1717575 = 2576363) B2576363
theorem B4347209 : Blo 1717059 4347209 := bstep (se 2 (by rfl) ⟨1630203, by rfl⟩ : syracuseStep 4347209 = 3260407) B3260407
theorem B3863915 : Blo 1717059 3863915 := bstep (se 1 (by rfl) ⟨2897936, by rfl⟩ : syracuseStep 3863915 = 5795873) B5795873
theorem B2577785 : Blo 1717059 2577785 := bstep (se 2 (by rfl) ⟨966669, by rfl⟩ : syracuseStep 2577785 = 1933339) B1933339
theorem B3864239 : Blo 1717059 3864239 := bstep (se 1 (by rfl) ⟨2898179, by rfl⟩ : syracuseStep 3864239 = 5796359) B5796359
theorem B1718119 : Blo 1717059 1718119 := bstep (se 1 (by rfl) ⟨1288589, by rfl⟩ : syracuseStep 1718119 = 2577179) B2577179
theorem B23517053 : Blo 1717059 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B1718183 : Blo 1717059 1718183 := bstep (se 1 (by rfl) ⟨1288637, by rfl⟩ : syracuseStep 1718183 = 2577275) B2577275
theorem B3866615 : Blo 1717059 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B2578409 : Blo 1717059 2578409 := bstep (se 2 (by rfl) ⟨966903, by rfl⟩ : syracuseStep 2578409 = 1933807) B1933807
theorem B13924379 : Blo 1717059 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B52893757 : Blo 1717059 52893757 := bstep (se 3 (by rfl) ⟨9917579, by rfl⟩ : syracuseStep 52893757 = 19835159) B19835159
theorem B1718383 : Blo 1717059 1718383 := bstep (se 1 (by rfl) ⟨1288787, by rfl⟩ : syracuseStep 1718383 = 2577575) B2577575
theorem B3668095 : Blo 1717059 3668095 := bstep (se 1 (by rfl) ⟨2751071, by rfl⟩ : syracuseStep 3668095 = 5502143) B5502143
theorem B3864743 : Blo 1717059 3864743 := bstep (se 1 (by rfl) ⟨2898557, by rfl⟩ : syracuseStep 3864743 = 5797115) B5797115
theorem B1718527 : Blo 1717059 1718527 := bstep (se 1 (by rfl) ⟨1288895, by rfl⟩ : syracuseStep 1718527 = 2577791) B2577791
theorem B1718655 : Blo 1717059 1718655 := bstep (se 1 (by rfl) ⟨1288991, by rfl⟩ : syracuseStep 1718655 = 2577983) B2577983
theorem B1718951 : Blo 1717059 1718951 := bstep (se 1 (by rfl) ⟨1289213, by rfl⟩ : syracuseStep 1718951 = 2578427) B2578427
theorem B1718975 : Blo 1717059 1718975 := bstep (se 1 (by rfl) ⟨1289231, by rfl⟩ : syracuseStep 1718975 = 2578463) B2578463
theorem B1719035 : Blo 1717059 1719035 := bstep (se 1 (by rfl) ⟨1289276, by rfl⟩ : syracuseStep 1719035 = 2578553) B2578553
theorem B1932223 : Blo 1717059 1932223 := bstep (se 1 (by rfl) ⟨1449167, by rfl⟩ : syracuseStep 1932223 = 2898335) B2898335
theorem B2899577 : Blo 1717059 2899577 := bstep (se 2 (by rfl) ⟨1087341, by rfl⟩ : syracuseStep 2899577 = 2174683) B2174683
theorem B24772391 : Blo 1717059 24772391 := bstep (se 1 (by rfl) ⟨18579293, by rfl⟩ : syracuseStep 24772391 = 37158587) B37158587
theorem B17629127 : Blo 1717059 17629127 := bstep (se 1 (by rfl) ⟨13221845, by rfl⟩ : syracuseStep 17629127 = 26443691) B26443691
theorem B5799977 : Blo 1717059 5799977 := bstep (se 2 (by rfl) ⟨2174991, by rfl⟩ : syracuseStep 5799977 = 4349983) B4349983
theorem B70525009 : Blo 1717059 70525009 := bstep (se 2 (by rfl) ⟨26446878, by rfl⟩ : syracuseStep 70525009 = 52893757) B52893757
theorem B4890793 : Blo 1717059 4890793 := bstep (se 2 (by rfl) ⟨1834047, by rfl⟩ : syracuseStep 4890793 = 3668095) B3668095
theorem B79364279 : Blo 1717059 79364279 := bstep (se 1 (by rfl) ⟨59523209, by rfl⟩ : syracuseStep 79364279 = 119046419) B119046419
theorem B2900191 : Blo 1717059 2900191 := bstep (se 1 (by rfl) ⟨2175143, by rfl⟩ : syracuseStep 2900191 = 4350287) B4350287
theorem B5800247 : Blo 1717059 5800247 := bstep (se 1 (by rfl) ⟨4350185, by rfl⟩ : syracuseStep 5800247 = 8700371) B8700371
theorem B156819827 : Blo 1717059 156819827 := bstep (se 1 (by rfl) ⟨117614870, by rfl⟩ : syracuseStep 156819827 = 235229741) B235229741
theorem B22307491 : Blo 1717059 22307491 := bstep (se 1 (by rfl) ⟨16730618, by rfl⟩ : syracuseStep 22307491 = 33461237) B33461237
theorem B5800679 : Blo 1717059 5800679 := bstep (se 1 (by rfl) ⟨4350509, by rfl⟩ : syracuseStep 5800679 = 8701019) B8701019
theorem B2900839 : Blo 1717059 2900839 := bstep (se 1 (by rfl) ⟨2175629, by rfl⟩ : syracuseStep 2900839 = 4351259) B4351259
theorem B6194495 : Blo 1717059 6194495 := bstep (se 1 (by rfl) ⟨4645871, by rfl⟩ : syracuseStep 6194495 = 9291743) B9291743
theorem B9282919 : Blo 1717059 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B7064543 : Blo 1717059 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B13929569 : Blo 1717059 13929569 := bstep (se 2 (by rfl) ⟨5223588, by rfl⟩ : syracuseStep 13929569 = 10447177) B10447177
theorem B2575595 : Blo 1717059 2575595 := bstep (se 1 (by rfl) ⟨1931696, by rfl⟩ : syracuseStep 2575595 = 3863393) B3863393
theorem B2575643 : Blo 1717059 2575643 := bstep (se 1 (by rfl) ⟨1931732, by rfl⟩ : syracuseStep 2575643 = 3863465) B3863465
theorem B2575775 : Blo 1717059 2575775 := bstep (se 1 (by rfl) ⟨1931831, by rfl⟩ : syracuseStep 2575775 = 3863663) B3863663
theorem B9784799 : Blo 1717059 9784799 := bstep (se 1 (by rfl) ⟨7338599, by rfl⟩ : syracuseStep 9784799 = 14677199) B14677199
theorem B2575919 : Blo 1717059 2575919 := bstep (se 1 (by rfl) ⟨1931939, by rfl⟩ : syracuseStep 2575919 = 3863879) B3863879
theorem B2575943 : Blo 1717059 2575943 := bstep (se 1 (by rfl) ⟨1931957, by rfl⟩ : syracuseStep 2575943 = 3863915) B3863915
theorem B42364583 : Blo 1717059 42364583 := bstep (se 1 (by rfl) ⟨31773437, by rfl⟩ : syracuseStep 42364583 = 63546875) B63546875
theorem B2576159 : Blo 1717059 2576159 := bstep (se 1 (by rfl) ⟨1932119, by rfl⟩ : syracuseStep 2576159 = 3864239) B3864239
theorem B20893573 : Blo 1717059 20893573 := bstep (se 4 (by rfl) ⟨1958772, by rfl⟩ : syracuseStep 20893573 = 3917545) B3917545
theorem B2576297 : Blo 1717059 2576297 := bstep (se 2 (by rfl) ⟨966111, by rfl⟩ : syracuseStep 2576297 = 1932223) B1932223
theorem B2576495 : Blo 1717059 2576495 := bstep (se 1 (by rfl) ⟨1932371, by rfl⟩ : syracuseStep 2576495 = 3864743) B3864743
theorem B5796089 : Blo 1717059 5796089 := bstep (se 2 (by rfl) ⟨2173533, by rfl⟩ : syracuseStep 5796089 = 4347067) B4347067
theorem B5796251 : Blo 1717059 5796251 := bstep (se 1 (by rfl) ⟨4347188, by rfl⟩ : syracuseStep 5796251 = 8694377) B8694377
theorem B2175599 : Blo 1717059 2175599 := bstep (se 1 (by rfl) ⟨1631699, by rfl⟩ : syracuseStep 2175599 = 3263399) B3263399
theorem B11752751 : Blo 1717059 11752751 := bstep (se 1 (by rfl) ⟨8814563, by rfl⟩ : syracuseStep 11752751 = 17629127) B17629127
theorem B2577743 : Blo 1717059 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B4347391 : Blo 1717059 4347391 := bstep (se 1 (by rfl) ⟨3260543, by rfl⟩ : syracuseStep 4347391 = 6521087) B6521087
theorem B8697455 : Blo 1717059 8697455 := bstep (se 1 (by rfl) ⟨6523091, by rfl⟩ : syracuseStep 8697455 = 13046183) B13046183
theorem B1718127 : Blo 1717059 1718127 := bstep (se 1 (by rfl) ⟨1288595, by rfl⟩ : syracuseStep 1718127 = 2577191) B2577191
theorem B2578331 : Blo 1717059 2578331 := bstep (se 1 (by rfl) ⟨1933748, by rfl⟩ : syracuseStep 2578331 = 3867497) B3867497
theorem B2898031 : Blo 1717059 2898031 := bstep (se 1 (by rfl) ⟨2173523, by rfl⟩ : syracuseStep 2898031 = 4347047) B4347047
theorem B2898139 : Blo 1717059 2898139 := bstep (se 1 (by rfl) ⟨2173604, by rfl⟩ : syracuseStep 2898139 = 4347209) B4347209
theorem B1718523 : Blo 1717059 1718523 := bstep (se 1 (by rfl) ⟨1288892, by rfl⟩ : syracuseStep 1718523 = 2577785) B2577785
theorem B15678035 : Blo 1717059 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B1718939 : Blo 1717059 1718939 := bstep (se 1 (by rfl) ⟨1289204, by rfl⟩ : syracuseStep 1718939 = 2578409) B2578409
theorem B19847915 : Blo 1717059 19847915 := bstep (se 1 (by rfl) ⟨14885936, by rfl⟩ : syracuseStep 19847915 = 29771873) B29771873
theorem B33037915 : Blo 1717059 33037915 := bstep (se 1 (by rfl) ⟨24778436, by rfl⟩ : syracuseStep 33037915 = 49556873) B49556873
theorem B1933051 : Blo 1717059 1933051 := bstep (se 1 (by rfl) ⟨1449788, by rfl⟩ : syracuseStep 1933051 = 2899577) B2899577
theorem B114532127 : Blo 1717059 114532127 := bstep (se 1 (by rfl) ⟨85899095, by rfl⟩ : syracuseStep 114532127 = 171798191) B171798191
theorem B16514927 : Blo 1717059 16514927 := bstep (se 1 (by rfl) ⟨12386195, by rfl⟩ : syracuseStep 16514927 = 24772391) B24772391
theorem B3866651 : Blo 1717059 3866651 := bstep (se 1 (by rfl) ⟨2899988, by rfl⟩ : syracuseStep 3866651 = 5799977) B5799977
theorem B3866831 : Blo 1717059 3866831 := bstep (se 1 (by rfl) ⟨2900123, by rfl⟩ : syracuseStep 3866831 = 5800247) B5800247
theorem B6521057 : Blo 1717059 6521057 := bstep (se 2 (by rfl) ⟨2445396, by rfl⟩ : syracuseStep 6521057 = 4890793) B4890793
theorem B104546551 : Blo 1717059 104546551 := bstep (se 1 (by rfl) ⟨78409913, by rfl⟩ : syracuseStep 104546551 = 156819827) B156819827
theorem B3866921 : Blo 1717059 3866921 := bstep (se 2 (by rfl) ⟨1450095, by rfl⟩ : syracuseStep 3866921 = 2900191) B2900191
theorem B3867119 : Blo 1717059 3867119 := bstep (se 1 (by rfl) ⟨2900339, by rfl⟩ : syracuseStep 3867119 = 5800679) B5800679
theorem B3867785 : Blo 1717059 3867785 := bstep (se 2 (by rfl) ⟨1450419, by rfl⟩ : syracuseStep 3867785 = 2900839) B2900839
theorem B5801597 : Blo 1717059 5801597 := bstep (se 3 (by rfl) ⟨1087799, by rfl⟩ : syracuseStep 5801597 = 2175599) B2175599
theorem B13231943 : Blo 1717059 13231943 := bstep (se 1 (by rfl) ⟨9923957, by rfl⟩ : syracuseStep 13231943 = 19847915) B19847915
theorem B44050553 : Blo 1717059 44050553 := bstep (se 2 (by rfl) ⟨16518957, by rfl⟩ : syracuseStep 44050553 = 33037915) B33037915
theorem B6523199 : Blo 1717059 6523199 := bstep (se 1 (by rfl) ⟨4892399, by rfl⟩ : syracuseStep 6523199 = 9784799) B9784799
theorem B16518653 : Blo 1717059 16518653 := bstep (se 3 (by rfl) ⟨3097247, by rfl⟩ : syracuseStep 16518653 = 6194495) B6194495
theorem B7835167 : Blo 1717059 7835167 := bstep (se 1 (by rfl) ⟨5876375, by rfl⟩ : syracuseStep 7835167 = 11752751) B11752751
theorem B5796521 : Blo 1717059 5796521 := bstep (se 2 (by rfl) ⟨2173695, by rfl⟩ : syracuseStep 5796521 = 4347391) B4347391
theorem B9286379 : Blo 1717059 9286379 := bstep (se 1 (by rfl) ⟨6964784, by rfl⟩ : syracuseStep 9286379 = 13929569) B13929569
theorem B1717063 : Blo 1717059 1717063 := bstep (se 1 (by rfl) ⟨1287797, by rfl⟩ : syracuseStep 1717063 = 2575595) B2575595
theorem B1717095 : Blo 1717059 1717095 := bstep (se 1 (by rfl) ⟨1287821, by rfl⟩ : syracuseStep 1717095 = 2575643) B2575643
theorem B1717183 : Blo 1717059 1717183 := bstep (se 1 (by rfl) ⟨1287887, by rfl⟩ : syracuseStep 1717183 = 2575775) B2575775
theorem B2577401 : Blo 1717059 2577401 := bstep (se 2 (by rfl) ⟨966525, by rfl⟩ : syracuseStep 2577401 = 1933051) B1933051
theorem B1717279 : Blo 1717059 1717279 := bstep (se 1 (by rfl) ⟨1287959, by rfl⟩ : syracuseStep 1717279 = 2575919) B2575919
theorem B1717295 : Blo 1717059 1717295 := bstep (se 1 (by rfl) ⟨1287971, by rfl⟩ : syracuseStep 1717295 = 2575943) B2575943
theorem B28243055 : Blo 1717059 28243055 := bstep (se 1 (by rfl) ⟨21182291, by rfl⟩ : syracuseStep 28243055 = 42364583) B42364583
theorem B27858097 : Blo 1717059 27858097 := bstep (se 2 (by rfl) ⟨10446786, by rfl⟩ : syracuseStep 27858097 = 20893573) B20893573
theorem B1717439 : Blo 1717059 1717439 := bstep (se 1 (by rfl) ⟨1288079, by rfl⟩ : syracuseStep 1717439 = 2576159) B2576159
theorem B76354751 : Blo 1717059 76354751 := bstep (se 1 (by rfl) ⟨57266063, by rfl⟩ : syracuseStep 76354751 = 114532127) B114532127
theorem B18838781 : Blo 1717059 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B1717531 : Blo 1717059 1717531 := bstep (se 1 (by rfl) ⟨1288148, by rfl⟩ : syracuseStep 1717531 = 2576297) B2576297
theorem B1717663 : Blo 1717059 1717663 := bstep (se 1 (by rfl) ⟨1288247, by rfl⟩ : syracuseStep 1717663 = 2576495) B2576495
theorem B94033345 : Blo 1717059 94033345 := bstep (se 2 (by rfl) ⟨35262504, by rfl⟩ : syracuseStep 94033345 = 70525009) B70525009
theorem B52909519 : Blo 1717059 52909519 := bstep (se 1 (by rfl) ⟨39682139, by rfl⟩ : syracuseStep 52909519 = 79364279) B79364279
theorem B3864041 : Blo 1717059 3864041 := bstep (se 2 (by rfl) ⟨1449015, by rfl⟩ : syracuseStep 3864041 = 2898031) B2898031
theorem B3864059 : Blo 1717059 3864059 := bstep (se 1 (by rfl) ⟨2898044, by rfl⟩ : syracuseStep 3864059 = 5796089) B5796089
theorem B3864167 : Blo 1717059 3864167 := bstep (se 1 (by rfl) ⟨2898125, by rfl⟩ : syracuseStep 3864167 = 5796251) B5796251
theorem B3864185 : Blo 1717059 3864185 := bstep (se 2 (by rfl) ⟨1449069, by rfl⟩ : syracuseStep 3864185 = 2898139) B2898139
theorem B29743321 : Blo 1717059 29743321 := bstep (se 2 (by rfl) ⟨11153745, by rfl⟩ : syracuseStep 29743321 = 22307491) B22307491
theorem B1718495 : Blo 1717059 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B5798303 : Blo 1717059 5798303 := bstep (se 1 (by rfl) ⟨4348727, by rfl⟩ : syracuseStep 5798303 = 8697455) B8697455
theorem B1718887 : Blo 1717059 1718887 := bstep (se 1 (by rfl) ⟨1289165, by rfl⟩ : syracuseStep 1718887 = 2578331) B2578331
theorem B10452023 : Blo 1717059 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B12377225 : Blo 1717059 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B11009951 : Blo 1717059 11009951 := bstep (se 1 (by rfl) ⟨8257463, by rfl⟩ : syracuseStep 11009951 = 16514927) B16514927
theorem B39657761 : Blo 1717059 39657761 := bstep (se 2 (by rfl) ⟨14871660, by rfl⟩ : syracuseStep 39657761 = 29743321) B29743321
theorem B139395401 : Blo 1717059 139395401 := bstep (se 2 (by rfl) ⟨52273275, by rfl⟩ : syracuseStep 139395401 = 104546551) B104546551
theorem B203612669 : Blo 1717059 203612669 := bstep (se 3 (by rfl) ⟨38177375, by rfl⟩ : syracuseStep 203612669 = 76354751) B76354751
theorem B12559187 : Blo 1717059 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B3867731 : Blo 1717059 3867731 := bstep (se 1 (by rfl) ⟨2900798, by rfl⟩ : syracuseStep 3867731 = 5801597) B5801597
theorem B37144129 : Blo 1717059 37144129 := bstep (se 2 (by rfl) ⟨13929048, by rfl⟩ : syracuseStep 37144129 = 27858097) B27858097
theorem B10446889 : Blo 1717059 10446889 := bstep (se 2 (by rfl) ⟨3917583, by rfl⟩ : syracuseStep 10446889 = 7835167) B7835167
theorem B8251483 : Blo 1717059 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B11012435 : Blo 1717059 11012435 := bstep (se 1 (by rfl) ⟨8259326, by rfl⟩ : syracuseStep 11012435 = 16518653) B16518653
theorem B18828703 : Blo 1717059 18828703 := bstep (se 1 (by rfl) ⟨14121527, by rfl⟩ : syracuseStep 18828703 = 28243055) B28243055
theorem B2576027 : Blo 1717059 2576027 := bstep (se 1 (by rfl) ⟨1932020, by rfl⟩ : syracuseStep 2576027 = 3864041) B3864041
theorem B2576039 : Blo 1717059 2576039 := bstep (se 1 (by rfl) ⟨1932029, by rfl⟩ : syracuseStep 2576039 = 3864059) B3864059
theorem B2576111 : Blo 1717059 2576111 := bstep (se 1 (by rfl) ⟨1932083, by rfl⟩ : syracuseStep 2576111 = 3864167) B3864167
theorem B2576123 : Blo 1717059 2576123 := bstep (se 1 (by rfl) ⟨1932092, by rfl⟩ : syracuseStep 2576123 = 3864185) B3864185
theorem B70546025 : Blo 1717059 70546025 := bstep (se 2 (by rfl) ⟨26454759, by rfl⟩ : syracuseStep 70546025 = 52909519) B52909519
theorem B6968015 : Blo 1717059 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B2577767 : Blo 1717059 2577767 := bstep (se 1 (by rfl) ⟨1933325, by rfl⟩ : syracuseStep 2577767 = 3866651) B3866651
theorem B2577887 : Blo 1717059 2577887 := bstep (se 1 (by rfl) ⟨1933415, by rfl⟩ : syracuseStep 2577887 = 3866831) B3866831
theorem B4347371 : Blo 1717059 4347371 := bstep (se 1 (by rfl) ⟨3260528, by rfl⟩ : syracuseStep 4347371 = 6521057) B6521057
theorem B2577947 : Blo 1717059 2577947 := bstep (se 1 (by rfl) ⟨1933460, by rfl⟩ : syracuseStep 2577947 = 3866921) B3866921
theorem B2578079 : Blo 1717059 2578079 := bstep (se 1 (by rfl) ⟨1933559, by rfl⟩ : syracuseStep 2578079 = 3867119) B3867119
theorem B3864347 : Blo 1717059 3864347 := bstep (se 1 (by rfl) ⟨2898260, by rfl⟩ : syracuseStep 3864347 = 5796521) B5796521
theorem B6190919 : Blo 1717059 6190919 := bstep (se 1 (by rfl) ⟨4643189, by rfl⟩ : syracuseStep 6190919 = 9286379) B9286379
theorem B1718267 : Blo 1717059 1718267 := bstep (se 1 (by rfl) ⟨1288700, by rfl⟩ : syracuseStep 1718267 = 2577401) B2577401
theorem B2578523 : Blo 1717059 2578523 := bstep (se 1 (by rfl) ⟨1933892, by rfl⟩ : syracuseStep 2578523 = 3867785) B3867785
theorem B8821295 : Blo 1717059 8821295 := bstep (se 1 (by rfl) ⟨6615971, by rfl⟩ : syracuseStep 8821295 = 13231943) B13231943
theorem B29367035 : Blo 1717059 29367035 := bstep (se 1 (by rfl) ⟨22025276, by rfl⟩ : syracuseStep 29367035 = 44050553) B44050553
theorem B4348799 : Blo 1717059 4348799 := bstep (se 1 (by rfl) ⟨3261599, by rfl⟩ : syracuseStep 4348799 = 6523199) B6523199
theorem B3865535 : Blo 1717059 3865535 := bstep (se 1 (by rfl) ⟨2899151, by rfl⟩ : syracuseStep 3865535 = 5798303) B5798303
theorem B125377793 : Blo 1717059 125377793 := bstep (se 2 (by rfl) ⟨47016672, by rfl⟩ : syracuseStep 125377793 = 94033345) B94033345
theorem B7339967 : Blo 1717059 7339967 := bstep (se 1 (by rfl) ⟨5504975, by rfl⟩ : syracuseStep 7339967 = 11009951) B11009951
theorem B11001977 : Blo 1717059 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B92930267 : Blo 1717059 92930267 := bstep (se 1 (by rfl) ⟨69697700, by rfl⟩ : syracuseStep 92930267 = 139395401) B139395401
theorem B135741779 : Blo 1717059 135741779 := bstep (se 1 (by rfl) ⟨101806334, by rfl⟩ : syracuseStep 135741779 = 203612669) B203612669
theorem B4645343 : Blo 1717059 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B8372791 : Blo 1717059 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B7341623 : Blo 1717059 7341623 := bstep (se 1 (by rfl) ⟨5506217, by rfl⟩ : syracuseStep 7341623 = 11012435) B11012435
theorem B188122733 : Blo 1717059 188122733 := bstep (se 3 (by rfl) ⟨35273012, by rfl⟩ : syracuseStep 188122733 = 70546025) B70546025
theorem B100419749 : Blo 1717059 100419749 := bstep (se 4 (by rfl) ⟨9414351, by rfl⟩ : syracuseStep 100419749 = 18828703) B18828703
theorem B83585195 : Blo 1717059 83585195 := bstep (se 1 (by rfl) ⟨62688896, by rfl⟩ : syracuseStep 83585195 = 125377793) B125377793
theorem B4893311 : Blo 1717059 4893311 := bstep (se 1 (by rfl) ⟨3669983, by rfl⟩ : syracuseStep 4893311 = 7339967) B7339967
theorem B13929185 : Blo 1717059 13929185 := bstep (se 2 (by rfl) ⟨5223444, by rfl⟩ : syracuseStep 13929185 = 10446889) B10446889
theorem B26438507 : Blo 1717059 26438507 := bstep (se 1 (by rfl) ⟨19828880, by rfl⟩ : syracuseStep 26438507 = 39657761) B39657761
theorem B2576231 : Blo 1717059 2576231 := bstep (se 1 (by rfl) ⟨1932173, by rfl⟩ : syracuseStep 2576231 = 3864347) B3864347
theorem B2577023 : Blo 1717059 2577023 := bstep (se 1 (by rfl) ⟨1932767, by rfl⟩ : syracuseStep 2577023 = 3865535) B3865535
theorem B49525505 : Blo 1717059 49525505 := bstep (se 2 (by rfl) ⟨18572064, by rfl⟩ : syracuseStep 49525505 = 37144129) B37144129
theorem B1717351 : Blo 1717059 1717351 := bstep (se 1 (by rfl) ⟨1288013, by rfl⟩ : syracuseStep 1717351 = 2576027) B2576027
theorem B1717359 : Blo 1717059 1717359 := bstep (se 1 (by rfl) ⟨1288019, by rfl⟩ : syracuseStep 1717359 = 2576039) B2576039
theorem B1717407 : Blo 1717059 1717407 := bstep (se 1 (by rfl) ⟨1288055, by rfl⟩ : syracuseStep 1717407 = 2576111) B2576111
theorem B1717415 : Blo 1717059 1717415 := bstep (se 1 (by rfl) ⟨1288061, by rfl⟩ : syracuseStep 1717415 = 2576123) B2576123
theorem B2578487 : Blo 1717059 2578487 := bstep (se 1 (by rfl) ⟨1933865, by rfl⟩ : syracuseStep 2578487 = 3867731) B3867731
theorem B1718511 : Blo 1717059 1718511 := bstep (se 1 (by rfl) ⟨1288883, by rfl⟩ : syracuseStep 1718511 = 2577767) B2577767
theorem B1718591 : Blo 1717059 1718591 := bstep (se 1 (by rfl) ⟨1288943, by rfl⟩ : syracuseStep 1718591 = 2577887) B2577887
theorem B2898247 : Blo 1717059 2898247 := bstep (se 1 (by rfl) ⟨2173685, by rfl⟩ : syracuseStep 2898247 = 4347371) B4347371
theorem B1718631 : Blo 1717059 1718631 := bstep (se 1 (by rfl) ⟨1288973, by rfl⟩ : syracuseStep 1718631 = 2577947) B2577947
theorem B1718719 : Blo 1717059 1718719 := bstep (se 1 (by rfl) ⟨1289039, by rfl⟩ : syracuseStep 1718719 = 2578079) B2578079
theorem B4127279 : Blo 1717059 4127279 := bstep (se 1 (by rfl) ⟨3095459, by rfl⟩ : syracuseStep 4127279 = 6190919) B6190919
theorem B1719015 : Blo 1717059 1719015 := bstep (se 1 (by rfl) ⟨1289261, by rfl⟩ : syracuseStep 1719015 = 2578523) B2578523
theorem B5880863 : Blo 1717059 5880863 := bstep (se 1 (by rfl) ⟨4410647, by rfl⟩ : syracuseStep 5880863 = 8821295) B8821295
theorem B19578023 : Blo 1717059 19578023 := bstep (se 1 (by rfl) ⟨14683517, by rfl⟩ : syracuseStep 19578023 = 29367035) B29367035
theorem B2899199 : Blo 1717059 2899199 := bstep (se 1 (by rfl) ⟨2174399, by rfl⟩ : syracuseStep 2899199 = 4348799) B4348799
theorem B44654885 : Blo 1717059 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B3096895 : Blo 1717059 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B44024309 : Blo 1717059 44024309 := bstep (se 5 (by rfl) ⟨2063639, by rfl⟩ : syracuseStep 44024309 = 4127279) B4127279
theorem B66946499 : Blo 1717059 66946499 := bstep (se 1 (by rfl) ⟨50209874, by rfl⟩ : syracuseStep 66946499 = 100419749) B100419749
theorem B55723463 : Blo 1717059 55723463 := bstep (se 1 (by rfl) ⟨41792597, by rfl⟩ : syracuseStep 55723463 = 83585195) B83585195
theorem B3262207 : Blo 1717059 3262207 := bstep (se 1 (by rfl) ⟨2446655, by rfl⟩ : syracuseStep 3262207 = 4893311) B4893311
theorem B13052015 : Blo 1717059 13052015 := bstep (se 1 (by rfl) ⟨9789011, by rfl⟩ : syracuseStep 13052015 = 19578023) B19578023
theorem B7334651 : Blo 1717059 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B33017003 : Blo 1717059 33017003 := bstep (se 1 (by rfl) ⟨24762752, by rfl⟩ : syracuseStep 33017003 = 49525505) B49525505
theorem B4894415 : Blo 1717059 4894415 := bstep (se 1 (by rfl) ⟨3670811, by rfl⟩ : syracuseStep 4894415 = 7341623) B7341623
theorem B125415155 : Blo 1717059 125415155 := bstep (se 1 (by rfl) ⟨94061366, by rfl⟩ : syracuseStep 125415155 = 188122733) B188122733
theorem B9286123 : Blo 1717059 9286123 := bstep (se 1 (by rfl) ⟨6964592, by rfl⟩ : syracuseStep 9286123 = 13929185) B13929185
theorem B17625671 : Blo 1717059 17625671 := bstep (se 1 (by rfl) ⟨13219253, by rfl⟩ : syracuseStep 17625671 = 26438507) B26438507
theorem B3920575 : Blo 1717059 3920575 := bstep (se 1 (by rfl) ⟨2940431, by rfl⟩ : syracuseStep 3920575 = 5880863) B5880863
theorem B1717487 : Blo 1717059 1717487 := bstep (se 1 (by rfl) ⟨1288115, by rfl⟩ : syracuseStep 1717487 = 2576231) B2576231
theorem B61953511 : Blo 1717059 61953511 := bstep (se 1 (by rfl) ⟨46465133, by rfl⟩ : syracuseStep 61953511 = 92930267) B92930267
theorem B90494519 : Blo 1717059 90494519 := bstep (se 1 (by rfl) ⟨67870889, by rfl⟩ : syracuseStep 90494519 = 135741779) B135741779
theorem B1718015 : Blo 1717059 1718015 := bstep (se 1 (by rfl) ⟨1288511, by rfl⟩ : syracuseStep 1718015 = 2577023) B2577023
theorem B3864329 : Blo 1717059 3864329 := bstep (se 2 (by rfl) ⟨1449123, by rfl⟩ : syracuseStep 3864329 = 2898247) B2898247
theorem B1718991 : Blo 1717059 1718991 := bstep (se 1 (by rfl) ⟨1289243, by rfl⟩ : syracuseStep 1718991 = 2578487) B2578487
theorem B1932799 : Blo 1717059 1932799 := bstep (se 1 (by rfl) ⟨1449599, by rfl⟩ : syracuseStep 1932799 = 2899199) B2899199
theorem B29769923 : Blo 1717059 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B4129193 : Blo 1717059 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B5227433 : Blo 1717059 5227433 := bstep (se 2 (by rfl) ⟨1960287, by rfl⟩ : syracuseStep 5227433 = 3920575) B3920575
theorem B44630999 : Blo 1717059 44630999 := bstep (se 1 (by rfl) ⟨33473249, by rfl⟩ : syracuseStep 44630999 = 66946499) B66946499
theorem B8701343 : Blo 1717059 8701343 := bstep (se 1 (by rfl) ⟨6526007, by rfl⟩ : syracuseStep 8701343 = 13052015) B13052015
theorem B3262943 : Blo 1717059 3262943 := bstep (se 1 (by rfl) ⟨2447207, by rfl⟩ : syracuseStep 3262943 = 4894415) B4894415
theorem B83610103 : Blo 1717059 83610103 := bstep (se 1 (by rfl) ⟨62707577, by rfl⟩ : syracuseStep 83610103 = 125415155) B125415155
theorem B11750447 : Blo 1717059 11750447 := bstep (se 1 (by rfl) ⟨8812835, by rfl⟩ : syracuseStep 11750447 = 17625671) B17625671
theorem B965274869 : Blo 1717059 965274869 := bstep (se 5 (by rfl) ⟨45247259, by rfl⟩ : syracuseStep 965274869 = 90494519) B90494519
theorem B12381497 : Blo 1717059 12381497 := bstep (se 2 (by rfl) ⟨4643061, by rfl⟩ : syracuseStep 12381497 = 9286123) B9286123
theorem B2576219 : Blo 1717059 2576219 := bstep (se 1 (by rfl) ⟨1932164, by rfl⟩ : syracuseStep 2576219 = 3864329) B3864329
theorem B82604681 : Blo 1717059 82604681 := bstep (se 2 (by rfl) ⟨30976755, by rfl⟩ : syracuseStep 82604681 = 61953511) B61953511
theorem B19559069 : Blo 1717059 19559069 := bstep (se 3 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 19559069 = 7334651) B7334651
theorem B2577065 : Blo 1717059 2577065 := bstep (se 2 (by rfl) ⟨966399, by rfl⟩ : syracuseStep 2577065 = 1932799) B1932799
theorem B29349539 : Blo 1717059 29349539 := bstep (se 1 (by rfl) ⟨22012154, by rfl⟩ : syracuseStep 29349539 = 44024309) B44024309
theorem B37148975 : Blo 1717059 37148975 := bstep (se 1 (by rfl) ⟨27861731, by rfl⟩ : syracuseStep 37148975 = 55723463) B55723463
theorem B22011335 : Blo 1717059 22011335 := bstep (se 1 (by rfl) ⟨16508501, by rfl⟩ : syracuseStep 22011335 = 33017003) B33017003
theorem B4349609 : Blo 1717059 4349609 := bstep (se 2 (by rfl) ⟨1631103, by rfl⟩ : syracuseStep 4349609 = 3262207) B3262207
theorem B31334525 : Blo 1717059 31334525 := bstep (se 3 (by rfl) ⟨5875223, by rfl⟩ : syracuseStep 31334525 = 11750447) B11750447
theorem B2752795 : Blo 1717059 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B29753999 : Blo 1717059 29753999 := bstep (se 1 (by rfl) ⟨22315499, by rfl⟩ : syracuseStep 29753999 = 44630999) B44630999
theorem B5800895 : Blo 1717059 5800895 := bstep (se 1 (by rfl) ⟨4350671, by rfl⟩ : syracuseStep 5800895 = 8701343) B8701343
theorem B8701181 : Blo 1717059 8701181 := bstep (se 3 (by rfl) ⟨1631471, by rfl⟩ : syracuseStep 8701181 = 3262943) B3262943
theorem B24765983 : Blo 1717059 24765983 := bstep (se 1 (by rfl) ⟨18574487, by rfl⟩ : syracuseStep 24765983 = 37148975) B37148975
theorem B643516579 : Blo 1717059 643516579 := bstep (se 1 (by rfl) ⟨482637434, by rfl⟩ : syracuseStep 643516579 = 965274869) B965274869
theorem B14674223 : Blo 1717059 14674223 := bstep (se 1 (by rfl) ⟨11005667, by rfl⟩ : syracuseStep 14674223 = 22011335) B22011335
theorem B55069787 : Blo 1717059 55069787 := bstep (se 1 (by rfl) ⟨41302340, by rfl⟩ : syracuseStep 55069787 = 82604681) B82604681
theorem B3484955 : Blo 1717059 3484955 := bstep (se 1 (by rfl) ⟨2613716, by rfl⟩ : syracuseStep 3484955 = 5227433) B5227433
theorem B111480137 : Blo 1717059 111480137 := bstep (se 2 (by rfl) ⟨41805051, by rfl⟩ : syracuseStep 111480137 = 83610103) B83610103
theorem B19566359 : Blo 1717059 19566359 := bstep (se 1 (by rfl) ⟨14674769, by rfl⟩ : syracuseStep 19566359 = 29349539) B29349539
theorem B8254331 : Blo 1717059 8254331 := bstep (se 1 (by rfl) ⟨6190748, by rfl⟩ : syracuseStep 8254331 = 12381497) B12381497
theorem B1717479 : Blo 1717059 1717479 := bstep (se 1 (by rfl) ⟨1288109, by rfl⟩ : syracuseStep 1717479 = 2576219) B2576219
theorem B19846615 : Blo 1717059 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B13039379 : Blo 1717059 13039379 := bstep (se 1 (by rfl) ⟨9779534, by rfl⟩ : syracuseStep 13039379 = 19559069) B19559069
theorem B1718043 : Blo 1717059 1718043 := bstep (se 1 (by rfl) ⟨1288532, by rfl⟩ : syracuseStep 1718043 = 2577065) B2577065
theorem B2899739 : Blo 1717059 2899739 := bstep (se 1 (by rfl) ⟨2174804, by rfl⟩ : syracuseStep 2899739 = 4349609) B4349609
theorem B20889683 : Blo 1717059 20889683 := bstep (se 1 (by rfl) ⟨15667262, by rfl⟩ : syracuseStep 20889683 = 31334525) B31334525
theorem B3867263 : Blo 1717059 3867263 := bstep (se 1 (by rfl) ⟨2900447, by rfl⟩ : syracuseStep 3867263 = 5800895) B5800895
theorem B5800787 : Blo 1717059 5800787 := bstep (se 1 (by rfl) ⟨4350590, by rfl⟩ : syracuseStep 5800787 = 8701181) B8701181
theorem B3432088421 : Blo 1717059 3432088421 := bstep (se 4 (by rfl) ⟨321758289, by rfl⟩ : syracuseStep 3432088421 = 643516579) B643516579
theorem B8692919 : Blo 1717059 8692919 := bstep (se 1 (by rfl) ⟨6519689, by rfl⟩ : syracuseStep 8692919 = 13039379) B13039379
theorem B14681573 : Blo 1717059 14681573 := bstep (se 4 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 14681573 = 2752795) B2752795
theorem B9782815 : Blo 1717059 9782815 := bstep (se 1 (by rfl) ⟨7337111, by rfl⟩ : syracuseStep 9782815 = 14674223) B14674223
theorem B26462153 : Blo 1717059 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B74320091 : Blo 1717059 74320091 := bstep (se 1 (by rfl) ⟨55740068, by rfl⟩ : syracuseStep 74320091 = 111480137) B111480137
theorem B13044239 : Blo 1717059 13044239 := bstep (se 1 (by rfl) ⟨9783179, by rfl⟩ : syracuseStep 13044239 = 19566359) B19566359
theorem B19835999 : Blo 1717059 19835999 := bstep (se 1 (by rfl) ⟨14876999, by rfl⟩ : syracuseStep 19835999 = 29753999) B29753999
theorem B9293213 : Blo 1717059 9293213 := bstep (se 3 (by rfl) ⟨1742477, by rfl⟩ : syracuseStep 9293213 = 3484955) B3484955
theorem B16510655 : Blo 1717059 16510655 := bstep (se 1 (by rfl) ⟨12382991, by rfl⟩ : syracuseStep 16510655 = 24765983) B24765983
theorem B36713191 : Blo 1717059 36713191 := bstep (se 1 (by rfl) ⟨27534893, by rfl⟩ : syracuseStep 36713191 = 55069787) B55069787
theorem B5502887 : Blo 1717059 5502887 := bstep (se 1 (by rfl) ⟨4127165, by rfl⟩ : syracuseStep 5502887 = 8254331) B8254331
theorem B1933159 : Blo 1717059 1933159 := bstep (se 1 (by rfl) ⟨1449869, by rfl⟩ : syracuseStep 1933159 = 2899739) B2899739
theorem B13926455 : Blo 1717059 13926455 := bstep (se 1 (by rfl) ⟨10444841, by rfl⟩ : syracuseStep 13926455 = 20889683) B20889683
theorem B3867191 : Blo 1717059 3867191 := bstep (se 1 (by rfl) ⟨2900393, by rfl⟩ : syracuseStep 3867191 = 5800787) B5800787
theorem B2288058947 : Blo 1717059 2288058947 := bstep (se 1 (by rfl) ⟨1716044210, by rfl⟩ : syracuseStep 2288058947 = 3432088421) B3432088421
theorem B49546727 : Blo 1717059 49546727 := bstep (se 1 (by rfl) ⟨37160045, by rfl⟩ : syracuseStep 49546727 = 74320091) B74320091
theorem B13043753 : Blo 1717059 13043753 := bstep (se 2 (by rfl) ⟨4891407, by rfl⟩ : syracuseStep 13043753 = 9782815) B9782815
theorem B13223999 : Blo 1717059 13223999 := bstep (se 1 (by rfl) ⟨9917999, by rfl⟩ : syracuseStep 13223999 = 19835999) B19835999
theorem B6195475 : Blo 1717059 6195475 := bstep (se 1 (by rfl) ⟨4646606, by rfl⟩ : syracuseStep 6195475 = 9293213) B9293213
theorem B5795279 : Blo 1717059 5795279 := bstep (se 1 (by rfl) ⟨4346459, by rfl⟩ : syracuseStep 5795279 = 8692919) B8692919
theorem B48950921 : Blo 1717059 48950921 := bstep (se 2 (by rfl) ⟨18356595, by rfl⟩ : syracuseStep 48950921 = 36713191) B36713191
theorem B8696159 : Blo 1717059 8696159 := bstep (se 1 (by rfl) ⟨6522119, by rfl⟩ : syracuseStep 8696159 = 13044239) B13044239
theorem B11007103 : Blo 1717059 11007103 := bstep (se 1 (by rfl) ⟨8255327, by rfl⟩ : syracuseStep 11007103 = 16510655) B16510655
theorem B2577545 : Blo 1717059 2577545 := bstep (se 2 (by rfl) ⟨966579, by rfl⟩ : syracuseStep 2577545 = 1933159) B1933159
theorem B2578175 : Blo 1717059 2578175 := bstep (se 1 (by rfl) ⟨1933631, by rfl⟩ : syracuseStep 2578175 = 3867263) B3867263
theorem B9787715 : Blo 1717059 9787715 := bstep (se 1 (by rfl) ⟨7340786, by rfl⟩ : syracuseStep 9787715 = 14681573) B14681573
theorem B3668591 : Blo 1717059 3668591 := bstep (se 1 (by rfl) ⟨2751443, by rfl⟩ : syracuseStep 3668591 = 5502887) B5502887
theorem B70565741 : Blo 1717059 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B33031151 : Blo 1717059 33031151 := bstep (se 1 (by rfl) ⟨24773363, by rfl⟩ : syracuseStep 33031151 = 49546727) B49546727
theorem B8815999 : Blo 1717059 8815999 := bstep (se 1 (by rfl) ⟨6611999, by rfl⟩ : syracuseStep 8815999 = 13223999) B13223999
theorem B9284303 : Blo 1717059 9284303 := bstep (se 1 (by rfl) ⟨6963227, by rfl⟩ : syracuseStep 9284303 = 13926455) B13926455
theorem B8260633 : Blo 1717059 8260633 := bstep (se 2 (by rfl) ⟨3097737, by rfl⟩ : syracuseStep 8260633 = 6195475) B6195475
theorem B8695835 : Blo 1717059 8695835 := bstep (se 1 (by rfl) ⟨6521876, by rfl⟩ : syracuseStep 8695835 = 13043753) B13043753
theorem B14676137 : Blo 1717059 14676137 := bstep (se 2 (by rfl) ⟨5503551, by rfl⟩ : syracuseStep 14676137 = 11007103) B11007103
theorem B6525143 : Blo 1717059 6525143 := bstep (se 1 (by rfl) ⟨4893857, by rfl⟩ : syracuseStep 6525143 = 9787715) B9787715
theorem B2445727 : Blo 1717059 2445727 := bstep (se 1 (by rfl) ⟨1834295, by rfl⟩ : syracuseStep 2445727 = 3668591) B3668591
theorem B3863519 : Blo 1717059 3863519 := bstep (se 1 (by rfl) ⟨2897639, by rfl⟩ : syracuseStep 3863519 = 5795279) B5795279
theorem B32633947 : Blo 1717059 32633947 := bstep (se 1 (by rfl) ⟨24475460, by rfl⟩ : syracuseStep 32633947 = 48950921) B48950921
theorem B47043827 : Blo 1717059 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B5797439 : Blo 1717059 5797439 := bstep (se 1 (by rfl) ⟨4348079, by rfl⟩ : syracuseStep 5797439 = 8696159) B8696159
theorem B2578127 : Blo 1717059 2578127 := bstep (se 1 (by rfl) ⟨1933595, by rfl⟩ : syracuseStep 2578127 = 3867191) B3867191
theorem B1525372631 : Blo 1717059 1525372631 := bstep (se 1 (by rfl) ⟨1144029473, by rfl⟩ : syracuseStep 1525372631 = 2288058947) B2288058947
theorem B1718363 : Blo 1717059 1718363 := bstep (se 1 (by rfl) ⟨1288772, by rfl⟩ : syracuseStep 1718363 = 2577545) B2577545
theorem B1718783 : Blo 1717059 1718783 := bstep (se 1 (by rfl) ⟨1289087, by rfl⟩ : syracuseStep 1718783 = 2578175) B2578175
theorem B4350095 : Blo 1717059 4350095 := bstep (se 1 (by rfl) ⟨3262571, by rfl⟩ : syracuseStep 4350095 = 6525143) B6525143
theorem B174047717 : Blo 1717059 174047717 := bstep (se 4 (by rfl) ⟨16316973, by rfl⟩ : syracuseStep 174047717 = 32633947) B32633947
theorem B3260969 : Blo 1717059 3260969 := bstep (se 2 (by rfl) ⟨1222863, by rfl⟩ : syracuseStep 3260969 = 2445727) B2445727
theorem B22020767 : Blo 1717059 22020767 := bstep (se 1 (by rfl) ⟨16515575, by rfl⟩ : syracuseStep 22020767 = 33031151) B33031151
theorem B1016915087 : Blo 1717059 1016915087 := bstep (se 1 (by rfl) ⟨762686315, by rfl⟩ : syracuseStep 1016915087 = 1525372631) B1525372631
theorem B9784091 : Blo 1717059 9784091 := bstep (se 1 (by rfl) ⟨7338068, by rfl⟩ : syracuseStep 9784091 = 14676137) B14676137
theorem B2575679 : Blo 1717059 2575679 := bstep (se 1 (by rfl) ⟨1931759, by rfl⟩ : syracuseStep 2575679 = 3863519) B3863519
theorem B31362551 : Blo 1717059 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B11014177 : Blo 1717059 11014177 := bstep (se 2 (by rfl) ⟨4130316, by rfl⟩ : syracuseStep 11014177 = 8260633) B8260633
theorem B6189535 : Blo 1717059 6189535 := bstep (se 1 (by rfl) ⟨4642151, by rfl⟩ : syracuseStep 6189535 = 9284303) B9284303
theorem B5797223 : Blo 1717059 5797223 := bstep (se 1 (by rfl) ⟨4347917, by rfl⟩ : syracuseStep 5797223 = 8695835) B8695835
theorem B3864959 : Blo 1717059 3864959 := bstep (se 1 (by rfl) ⟨2898719, by rfl⟩ : syracuseStep 3864959 = 5797439) B5797439
theorem B1718751 : Blo 1717059 1718751 := bstep (se 1 (by rfl) ⟨1289063, by rfl⟩ : syracuseStep 1718751 = 2578127) B2578127
theorem B11754665 : Blo 1717059 11754665 := bstep (se 2 (by rfl) ⟨4407999, by rfl⟩ : syracuseStep 11754665 = 8815999) B8815999
theorem B2900063 : Blo 1717059 2900063 := bstep (se 1 (by rfl) ⟨2175047, by rfl⟩ : syracuseStep 2900063 = 4350095) B4350095
theorem B14680511 : Blo 1717059 14680511 := bstep (se 1 (by rfl) ⟨11010383, by rfl⟩ : syracuseStep 14680511 = 22020767) B22020767
theorem B464127245 : Blo 1717059 464127245 := bstep (se 3 (by rfl) ⟨87023858, by rfl⟩ : syracuseStep 464127245 = 174047717) B174047717
theorem B6522727 : Blo 1717059 6522727 := bstep (se 1 (by rfl) ⟨4892045, by rfl⟩ : syracuseStep 6522727 = 9784091) B9784091
theorem B20908367 : Blo 1717059 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B2173979 : Blo 1717059 2173979 := bstep (se 1 (by rfl) ⟨1630484, by rfl⟩ : syracuseStep 2173979 = 3260969) B3260969
theorem B8252713 : Blo 1717059 8252713 := bstep (se 2 (by rfl) ⟨3094767, by rfl⟩ : syracuseStep 8252713 = 6189535) B6189535
theorem B2576639 : Blo 1717059 2576639 := bstep (se 1 (by rfl) ⟨1932479, by rfl⟩ : syracuseStep 2576639 = 3864959) B3864959
theorem B7836443 : Blo 1717059 7836443 := bstep (se 1 (by rfl) ⟨5877332, by rfl⟩ : syracuseStep 7836443 = 11754665) B11754665
theorem B1717119 : Blo 1717059 1717119 := bstep (se 1 (by rfl) ⟨1287839, by rfl⟩ : syracuseStep 1717119 = 2575679) B2575679
theorem B14685569 : Blo 1717059 14685569 := bstep (se 2 (by rfl) ⟨5507088, by rfl⟩ : syracuseStep 14685569 = 11014177) B11014177
theorem B677943391 : Blo 1717059 677943391 := bstep (se 1 (by rfl) ⟨508457543, by rfl⟩ : syracuseStep 677943391 = 1016915087) B1016915087
theorem B3864815 : Blo 1717059 3864815 := bstep (se 1 (by rfl) ⟨2898611, by rfl⟩ : syracuseStep 3864815 = 5797223) B5797223
theorem B1933375 : Blo 1717059 1933375 := bstep (se 1 (by rfl) ⟨1450031, by rfl⟩ : syracuseStep 1933375 = 2900063) B2900063
theorem B9790379 : Blo 1717059 9790379 := bstep (se 1 (by rfl) ⟨7342784, by rfl⟩ : syracuseStep 9790379 = 14685569) B14685569
theorem B11003617 : Blo 1717059 11003617 := bstep (se 2 (by rfl) ⟨4126356, by rfl⟩ : syracuseStep 11003617 = 8252713) B8252713
theorem B903924521 : Blo 1717059 903924521 := bstep (se 2 (by rfl) ⟨338971695, by rfl⟩ : syracuseStep 903924521 = 677943391) B677943391
theorem B2576543 : Blo 1717059 2576543 := bstep (se 1 (by rfl) ⟨1932407, by rfl⟩ : syracuseStep 2576543 = 3864815) B3864815
theorem B13938911 : Blo 1717059 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B8696969 : Blo 1717059 8696969 := bstep (se 2 (by rfl) ⟨3261363, by rfl⟩ : syracuseStep 8696969 = 6522727) B6522727
theorem B5797277 : Blo 1717059 5797277 := bstep (se 3 (by rfl) ⟨1086989, by rfl⟩ : syracuseStep 5797277 = 2173979) B2173979
theorem B1717759 : Blo 1717059 1717759 := bstep (se 1 (by rfl) ⟨1288319, by rfl⟩ : syracuseStep 1717759 = 2576639) B2576639
theorem B9787007 : Blo 1717059 9787007 := bstep (se 1 (by rfl) ⟨7340255, by rfl⟩ : syracuseStep 9787007 = 14680511) B14680511
theorem B5224295 : Blo 1717059 5224295 := bstep (se 1 (by rfl) ⟨3918221, by rfl⟩ : syracuseStep 5224295 = 7836443) B7836443
theorem B309418163 : Blo 1717059 309418163 := bstep (se 1 (by rfl) ⟨232063622, by rfl⟩ : syracuseStep 309418163 = 464127245) B464127245
theorem B9292607 : Blo 1717059 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B6524671 : Blo 1717059 6524671 := bstep (se 1 (by rfl) ⟨4893503, by rfl⟩ : syracuseStep 6524671 = 9787007) B9787007
theorem B206278775 : Blo 1717059 206278775 := bstep (se 1 (by rfl) ⟨154709081, by rfl⟩ : syracuseStep 206278775 = 309418163) B309418163
theorem B602616347 : Blo 1717059 602616347 := bstep (se 1 (by rfl) ⟨451962260, by rfl⟩ : syracuseStep 602616347 = 903924521) B903924521
theorem B13931453 : Blo 1717059 13931453 := bstep (se 3 (by rfl) ⟨2612147, by rfl⟩ : syracuseStep 13931453 = 5224295) B5224295
theorem B2577833 : Blo 1717059 2577833 := bstep (se 2 (by rfl) ⟨966687, by rfl⟩ : syracuseStep 2577833 = 1933375) B1933375
theorem B1717695 : Blo 1717059 1717695 := bstep (se 1 (by rfl) ⟨1288271, by rfl⟩ : syracuseStep 1717695 = 2576543) B2576543
theorem B6526919 : Blo 1717059 6526919 := bstep (se 1 (by rfl) ⟨4895189, by rfl⟩ : syracuseStep 6526919 = 9790379) B9790379
theorem B5797979 : Blo 1717059 5797979 := bstep (se 1 (by rfl) ⟨4348484, by rfl⟩ : syracuseStep 5797979 = 8696969) B8696969
theorem B3864851 : Blo 1717059 3864851 := bstep (se 1 (by rfl) ⟨2898638, by rfl⟩ : syracuseStep 3864851 = 5797277) B5797277
theorem B14671489 : Blo 1717059 14671489 := bstep (se 2 (by rfl) ⟨5501808, by rfl⟩ : syracuseStep 14671489 = 11003617) B11003617
theorem B137519183 : Blo 1717059 137519183 := bstep (se 1 (by rfl) ⟨103139387, by rfl⟩ : syracuseStep 137519183 = 206278775) B206278775
theorem B401744231 : Blo 1717059 401744231 := bstep (se 1 (by rfl) ⟨301308173, by rfl⟩ : syracuseStep 401744231 = 602616347) B602616347
theorem B4351279 : Blo 1717059 4351279 := bstep (se 1 (by rfl) ⟨3263459, by rfl⟩ : syracuseStep 4351279 = 6526919) B6526919
theorem B6195071 : Blo 1717059 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B2576567 : Blo 1717059 2576567 := bstep (se 1 (by rfl) ⟨1932425, by rfl⟩ : syracuseStep 2576567 = 3864851) B3864851
theorem B9287635 : Blo 1717059 9287635 := bstep (se 1 (by rfl) ⟨6965726, by rfl⟩ : syracuseStep 9287635 = 13931453) B13931453
theorem B1718555 : Blo 1717059 1718555 := bstep (se 1 (by rfl) ⟨1288916, by rfl⟩ : syracuseStep 1718555 = 2577833) B2577833
theorem B3865319 : Blo 1717059 3865319 := bstep (se 1 (by rfl) ⟨2898989, by rfl⟩ : syracuseStep 3865319 = 5797979) B5797979
theorem B19561985 : Blo 1717059 19561985 := bstep (se 2 (by rfl) ⟨7335744, by rfl⟩ : syracuseStep 19561985 = 14671489) B14671489
theorem B8699561 : Blo 1717059 8699561 := bstep (se 2 (by rfl) ⟨3262335, by rfl⟩ : syracuseStep 8699561 = 6524671) B6524671
theorem B267829487 : Blo 1717059 267829487 := bstep (se 1 (by rfl) ⟨200872115, by rfl⟩ : syracuseStep 267829487 = 401744231) B401744231
theorem B4130047 : Blo 1717059 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B5801705 : Blo 1717059 5801705 := bstep (se 2 (by rfl) ⟨2175639, by rfl⟩ : syracuseStep 5801705 = 4351279) B4351279
theorem B91679455 : Blo 1717059 91679455 := bstep (se 1 (by rfl) ⟨68759591, by rfl⟩ : syracuseStep 91679455 = 137519183) B137519183
theorem B2576879 : Blo 1717059 2576879 := bstep (se 1 (by rfl) ⟨1932659, by rfl⟩ : syracuseStep 2576879 = 3865319) B3865319
theorem B12383513 : Blo 1717059 12383513 := bstep (se 2 (by rfl) ⟨4643817, by rfl⟩ : syracuseStep 12383513 = 9287635) B9287635
theorem B1717711 : Blo 1717059 1717711 := bstep (se 1 (by rfl) ⟨1288283, by rfl⟩ : syracuseStep 1717711 = 2576567) B2576567
theorem B13041323 : Blo 1717059 13041323 := bstep (se 1 (by rfl) ⟨9780992, by rfl⟩ : syracuseStep 13041323 = 19561985) B19561985
theorem B5799707 : Blo 1717059 5799707 := bstep (se 1 (by rfl) ⟨4349780, by rfl⟩ : syracuseStep 5799707 = 8699561) B8699561
theorem B178552991 : Blo 1717059 178552991 := bstep (se 1 (by rfl) ⟨133914743, by rfl⟩ : syracuseStep 178552991 = 267829487) B267829487
theorem B3867803 : Blo 1717059 3867803 := bstep (se 1 (by rfl) ⟨2900852, by rfl⟩ : syracuseStep 3867803 = 5801705) B5801705
theorem B8694215 : Blo 1717059 8694215 := bstep (se 1 (by rfl) ⟨6520661, by rfl⟩ : syracuseStep 8694215 = 13041323) B13041323
theorem B1717919 : Blo 1717059 1717919 := bstep (se 1 (by rfl) ⟨1288439, by rfl⟩ : syracuseStep 1717919 = 2576879) B2576879
theorem B8255675 : Blo 1717059 8255675 := bstep (se 1 (by rfl) ⟨6191756, by rfl⟩ : syracuseStep 8255675 = 12383513) B12383513
theorem B122239273 : Blo 1717059 122239273 := bstep (se 2 (by rfl) ⟨45839727, by rfl⟩ : syracuseStep 122239273 = 91679455) B91679455
theorem B22026917 : Blo 1717059 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B3866471 : Blo 1717059 3866471 := bstep (se 1 (by rfl) ⟨2899853, by rfl⟩ : syracuseStep 3866471 = 5799707) B5799707
theorem B5796143 : Blo 1717059 5796143 := bstep (se 1 (by rfl) ⟨4347107, by rfl⟩ : syracuseStep 5796143 = 8694215) B8694215
theorem B14684611 : Blo 1717059 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B2577647 : Blo 1717059 2577647 := bstep (se 1 (by rfl) ⟨1933235, by rfl⟩ : syracuseStep 2577647 = 3866471) B3866471
theorem B119035327 : Blo 1717059 119035327 := bstep (se 1 (by rfl) ⟨89276495, by rfl⟩ : syracuseStep 119035327 = 178552991) B178552991
theorem B162985697 : Blo 1717059 162985697 := bstep (se 2 (by rfl) ⟨61119636, by rfl⟩ : syracuseStep 162985697 = 122239273) B122239273
theorem B2578535 : Blo 1717059 2578535 := bstep (se 1 (by rfl) ⟨1933901, by rfl⟩ : syracuseStep 2578535 = 3867803) B3867803
theorem B5503783 : Blo 1717059 5503783 := bstep (se 1 (by rfl) ⟨4127837, by rfl⟩ : syracuseStep 5503783 = 8255675) B8255675
theorem B19579481 : Blo 1717059 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B158713769 : Blo 1717059 158713769 := bstep (se 2 (by rfl) ⟨59517663, by rfl⟩ : syracuseStep 158713769 = 119035327) B119035327
theorem B3864095 : Blo 1717059 3864095 := bstep (se 1 (by rfl) ⟨2898071, by rfl⟩ : syracuseStep 3864095 = 5796143) B5796143
theorem B1718431 : Blo 1717059 1718431 := bstep (se 1 (by rfl) ⟨1288823, by rfl⟩ : syracuseStep 1718431 = 2577647) B2577647
theorem B7338377 : Blo 1717059 7338377 := bstep (se 2 (by rfl) ⟨2751891, by rfl⟩ : syracuseStep 7338377 = 5503783) B5503783
theorem B108657131 : Blo 1717059 108657131 := bstep (se 1 (by rfl) ⟨81492848, by rfl⟩ : syracuseStep 108657131 = 162985697) B162985697
theorem B1719023 : Blo 1717059 1719023 := bstep (se 1 (by rfl) ⟨1289267, by rfl⟩ : syracuseStep 1719023 = 2578535) B2578535
theorem B105809179 : Blo 1717059 105809179 := bstep (se 1 (by rfl) ⟨79356884, by rfl⟩ : syracuseStep 105809179 = 158713769) B158713769
theorem B289752349 : Blo 1717059 289752349 := bstep (se 3 (by rfl) ⟨54328565, by rfl⟩ : syracuseStep 289752349 = 108657131) B108657131
theorem B4892251 : Blo 1717059 4892251 := bstep (se 1 (by rfl) ⟨3669188, by rfl⟩ : syracuseStep 4892251 = 7338377) B7338377
theorem B13052987 : Blo 1717059 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B2576063 : Blo 1717059 2576063 := bstep (se 1 (by rfl) ⟨1932047, by rfl⟩ : syracuseStep 2576063 = 3864095) B3864095
theorem B386336465 : Blo 1717059 386336465 := bstep (se 2 (by rfl) ⟨144876174, by rfl⟩ : syracuseStep 386336465 = 289752349) B289752349
theorem B8701991 : Blo 1717059 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B6523001 : Blo 1717059 6523001 := bstep (se 2 (by rfl) ⟨2446125, by rfl⟩ : syracuseStep 6523001 = 4892251) B4892251
theorem B141078905 : Blo 1717059 141078905 := bstep (se 2 (by rfl) ⟨52904589, by rfl⟩ : syracuseStep 141078905 = 105809179) B105809179
theorem B1717375 : Blo 1717059 1717375 := bstep (se 1 (by rfl) ⟨1288031, by rfl⟩ : syracuseStep 1717375 = 2576063) B2576063
theorem B94052603 : Blo 1717059 94052603 := bstep (se 1 (by rfl) ⟨70539452, by rfl⟩ : syracuseStep 94052603 = 141078905) B141078905
theorem B257557643 : Blo 1717059 257557643 := bstep (se 1 (by rfl) ⟨193168232, by rfl⟩ : syracuseStep 257557643 = 386336465) B386336465
theorem B5801327 : Blo 1717059 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B4348667 : Blo 1717059 4348667 := bstep (se 1 (by rfl) ⟨3261500, by rfl⟩ : syracuseStep 4348667 = 6523001) B6523001
theorem B62701735 : Blo 1717059 62701735 := bstep (se 1 (by rfl) ⟨47026301, by rfl⟩ : syracuseStep 62701735 = 94052603) B94052603
theorem B171705095 : Blo 1717059 171705095 := bstep (se 1 (by rfl) ⟨128778821, by rfl⟩ : syracuseStep 171705095 = 257557643) B257557643
theorem B3867551 : Blo 1717059 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B2899111 : Blo 1717059 2899111 := bstep (se 1 (by rfl) ⟨2174333, by rfl⟩ : syracuseStep 2899111 = 4348667) B4348667
theorem B83602313 : Blo 1717059 83602313 := bstep (se 2 (by rfl) ⟨31350867, by rfl⟩ : syracuseStep 83602313 = 62701735) B62701735
theorem B114470063 : Blo 1717059 114470063 := bstep (se 1 (by rfl) ⟨85852547, by rfl⟩ : syracuseStep 114470063 = 171705095) B171705095
theorem B2578367 : Blo 1717059 2578367 := bstep (se 1 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 2578367 = 3867551) B3867551
theorem B3865481 : Blo 1717059 3865481 := bstep (se 2 (by rfl) ⟨1449555, by rfl⟩ : syracuseStep 3865481 = 2899111) B2899111
theorem B2576987 : Blo 1717059 2576987 := bstep (se 1 (by rfl) ⟨1932740, by rfl⟩ : syracuseStep 2576987 = 3865481) B3865481
theorem B55734875 : Blo 1717059 55734875 := bstep (se 1 (by rfl) ⟨41801156, by rfl⟩ : syracuseStep 55734875 = 83602313) B83602313
theorem B76313375 : Blo 1717059 76313375 := bstep (se 1 (by rfl) ⟨57235031, by rfl⟩ : syracuseStep 76313375 = 114470063) B114470063
theorem B1718911 : Blo 1717059 1718911 := bstep (se 1 (by rfl) ⟨1289183, by rfl⟩ : syracuseStep 1718911 = 2578367) B2578367
theorem B50875583 : Blo 1717059 50875583 := bstep (se 1 (by rfl) ⟨38156687, by rfl⟩ : syracuseStep 50875583 = 76313375) B76313375
theorem B1717991 : Blo 1717059 1717991 := bstep (se 1 (by rfl) ⟨1288493, by rfl⟩ : syracuseStep 1717991 = 2576987) B2576987
theorem B37156583 : Blo 1717059 37156583 := bstep (se 1 (by rfl) ⟨27867437, by rfl⟩ : syracuseStep 37156583 = 55734875) B55734875
theorem B99084221 : Blo 1717059 99084221 := bstep (se 3 (by rfl) ⟨18578291, by rfl⟩ : syracuseStep 99084221 = 37156583) B37156583
theorem B542672885 : Blo 1717059 542672885 := bstep (se 5 (by rfl) ⟨25437791, by rfl⟩ : syracuseStep 542672885 = 50875583) B50875583
theorem B66056147 : Blo 1717059 66056147 := bstep (se 1 (by rfl) ⟨49542110, by rfl⟩ : syracuseStep 66056147 = 99084221) B99084221
theorem B361781923 : Blo 1717059 361781923 := bstep (se 1 (by rfl) ⟨271336442, by rfl⟩ : syracuseStep 361781923 = 542672885) B542672885
theorem B44037431 : Blo 1717059 44037431 := bstep (se 1 (by rfl) ⟨33028073, by rfl⟩ : syracuseStep 44037431 = 66056147) B66056147
theorem B482375897 : Blo 1717059 482375897 := bstep (se 2 (by rfl) ⟨180890961, by rfl⟩ : syracuseStep 482375897 = 361781923) B361781923
theorem B29358287 : Blo 1717059 29358287 := bstep (se 1 (by rfl) ⟨22018715, by rfl⟩ : syracuseStep 29358287 = 44037431) B44037431
theorem B321583931 : Blo 1717059 321583931 := bstep (se 1 (by rfl) ⟨241187948, by rfl⟩ : syracuseStep 321583931 = 482375897) B482375897
theorem B19572191 : Blo 1717059 19572191 := bstep (se 1 (by rfl) ⟨14679143, by rfl⟩ : syracuseStep 19572191 = 29358287) B29358287
theorem B214389287 : Blo 1717059 214389287 := bstep (se 1 (by rfl) ⟨160791965, by rfl⟩ : syracuseStep 214389287 = 321583931) B321583931
theorem B142926191 : Blo 1717059 142926191 := bstep (se 1 (by rfl) ⟨107194643, by rfl⟩ : syracuseStep 142926191 = 214389287) B214389287
theorem B13048127 : Blo 1717059 13048127 := bstep (se 1 (by rfl) ⟨9786095, by rfl⟩ : syracuseStep 13048127 = 19572191) B19572191
theorem B95284127 : Blo 1717059 95284127 := bstep (se 1 (by rfl) ⟨71463095, by rfl⟩ : syracuseStep 95284127 = 142926191) B142926191
theorem B8698751 : Blo 1717059 8698751 := bstep (se 1 (by rfl) ⟨6524063, by rfl⟩ : syracuseStep 8698751 = 13048127) B13048127
theorem B5799167 : Blo 1717059 5799167 := bstep (se 1 (by rfl) ⟨4349375, by rfl⟩ : syracuseStep 5799167 = 8698751) B8698751
theorem B254091005 : Blo 1717059 254091005 := bstep (se 3 (by rfl) ⟨47642063, by rfl⟩ : syracuseStep 254091005 = 95284127) B95284127
theorem B3866111 : Blo 1717059 3866111 := bstep (se 1 (by rfl) ⟨2899583, by rfl⟩ : syracuseStep 3866111 = 5799167) B5799167
theorem B169394003 : Blo 1717059 169394003 := bstep (se 1 (by rfl) ⟨127045502, by rfl⟩ : syracuseStep 169394003 = 254091005) B254091005
theorem B112929335 : Blo 1717059 112929335 := bstep (se 1 (by rfl) ⟨84697001, by rfl⟩ : syracuseStep 112929335 = 169394003) B169394003
theorem B2577407 : Blo 1717059 2577407 := bstep (se 1 (by rfl) ⟨1933055, by rfl⟩ : syracuseStep 2577407 = 3866111) B3866111
theorem B75286223 : Blo 1717059 75286223 := bstep (se 1 (by rfl) ⟨56464667, by rfl⟩ : syracuseStep 75286223 = 112929335) B112929335
theorem B1718271 : Blo 1717059 1718271 := bstep (se 1 (by rfl) ⟨1288703, by rfl⟩ : syracuseStep 1718271 = 2577407) B2577407
theorem B50190815 : Blo 1717059 50190815 := bstep (se 1 (by rfl) ⟨37643111, by rfl⟩ : syracuseStep 50190815 = 75286223) B75286223
theorem B33460543 : Blo 1717059 33460543 := bstep (se 1 (by rfl) ⟨25095407, by rfl⟩ : syracuseStep 33460543 = 50190815) B50190815
theorem B178456229 : Blo 1717059 178456229 := bstep (se 4 (by rfl) ⟨16730271, by rfl⟩ : syracuseStep 178456229 = 33460543) B33460543
theorem B118970819 : Blo 1717059 118970819 := bstep (se 1 (by rfl) ⟨89228114, by rfl⟩ : syracuseStep 118970819 = 178456229) B178456229
theorem B79313879 : Blo 1717059 79313879 := bstep (se 1 (by rfl) ⟨59485409, by rfl⟩ : syracuseStep 79313879 = 118970819) B118970819
theorem B52875919 : Blo 1717059 52875919 := bstep (se 1 (by rfl) ⟨39656939, by rfl⟩ : syracuseStep 52875919 = 79313879) B79313879
theorem B70501225 : Blo 1717059 70501225 := bstep (se 2 (by rfl) ⟨26437959, by rfl⟩ : syracuseStep 70501225 = 52875919) B52875919
theorem B94001633 : Blo 1717059 94001633 := bstep (se 2 (by rfl) ⟨35250612, by rfl⟩ : syracuseStep 94001633 = 70501225) B70501225
theorem B62667755 : Blo 1717059 62667755 := bstep (se 1 (by rfl) ⟨47000816, by rfl⟩ : syracuseStep 62667755 = 94001633) B94001633
theorem B41778503 : Blo 1717059 41778503 := bstep (se 1 (by rfl) ⟨31333877, by rfl⟩ : syracuseStep 41778503 = 62667755) B62667755
theorem B27852335 : Blo 1717059 27852335 := bstep (se 1 (by rfl) ⟨20889251, by rfl⟩ : syracuseStep 27852335 = 41778503) B41778503
theorem B18568223 : Blo 1717059 18568223 := bstep (se 1 (by rfl) ⟨13926167, by rfl⟩ : syracuseStep 18568223 = 27852335) B27852335
theorem B12378815 : Blo 1717059 12378815 := bstep (se 1 (by rfl) ⟨9284111, by rfl⟩ : syracuseStep 12378815 = 18568223) B18568223
theorem B8252543 : Blo 1717059 8252543 := bstep (se 1 (by rfl) ⟨6189407, by rfl⟩ : syracuseStep 8252543 = 12378815) B12378815
theorem B5501695 : Blo 1717059 5501695 := bstep (se 1 (by rfl) ⟨4126271, by rfl⟩ : syracuseStep 5501695 = 8252543) B8252543
theorem B7335593 : Blo 1717059 7335593 := bstep (se 2 (by rfl) ⟨2750847, by rfl⟩ : syracuseStep 7335593 = 5501695) B5501695
theorem B4890395 : Blo 1717059 4890395 := bstep (se 1 (by rfl) ⟨3667796, by rfl⟩ : syracuseStep 4890395 = 7335593) B7335593
theorem B3260263 : Blo 1717059 3260263 := bstep (se 1 (by rfl) ⟨2445197, by rfl⟩ : syracuseStep 3260263 = 4890395) B4890395
theorem B4347017 : Blo 1717059 4347017 := bstep (se 2 (by rfl) ⟨1630131, by rfl⟩ : syracuseStep 4347017 = 3260263) B3260263
theorem B2898011 : Blo 1717059 2898011 := bstep (se 1 (by rfl) ⟨2173508, by rfl⟩ : syracuseStep 2898011 = 4347017) B4347017
theorem B1932007 : Blo 1717059 1932007 := bstep (se 1 (by rfl) ⟨1449005, by rfl⟩ : syracuseStep 1932007 = 2898011) B2898011
theorem B2576009 : Blo 1717059 2576009 := bstep (se 2 (by rfl) ⟨966003, by rfl⟩ : syracuseStep 2576009 = 1932007) B1932007
theorem B1717339 : Blo 1717059 1717339 := bstep (se 1 (by rfl) ⟨1288004, by rfl⟩ : syracuseStep 1717339 = 2576009) B2576009

theorem C0 (j : ℕ) (h1 : 429264 ≤ j) (h2 : j ≤ 429764) : Blo 1717059 (4 * j + 3) := by
  interval_cases j
  · exact B1717059
  · exact B1717063
  · exact B1717067
  · exact B1717071
  · exact B1717075
  · exact B1717079
  · exact B1717083
  · exact B1717087
  · exact B1717091
  · exact B1717095
  · exact B1717099
  · exact B1717103
  · exact B1717107
  · exact B1717111
  · exact B1717115
  · exact B1717119
  · exact B1717123
  · exact B1717127
  · exact B1717131
  · exact B1717135
  · exact B1717139
  · exact B1717143
  · exact B1717147
  · exact B1717151
  · exact B1717155
  · exact B1717159
  · exact B1717163
  · exact B1717167
  · exact B1717171
  · exact B1717175
  · exact B1717179
  · exact B1717183
  · exact B1717187
  · exact B1717191
  · exact B1717195
  · exact B1717199
  · exact B1717203
  · exact B1717207
  · exact B1717211
  · exact B1717215
  · exact B1717219
  · exact B1717223
  · exact B1717227
  · exact B1717231
  · exact B1717235
  · exact B1717239
  · exact B1717243
  · exact B1717247
  · exact B1717251
  · exact B1717255
  · exact B1717259
  · exact B1717263
  · exact B1717267
  · exact B1717271
  · exact B1717275
  · exact B1717279
  · exact B1717283
  · exact B1717287
  · exact B1717291
  · exact B1717295
  · exact B1717299
  · exact B1717303
  · exact B1717307
  · exact B1717311
  · exact B1717315
  · exact B1717319
  · exact B1717323
  · exact B1717327
  · exact B1717331
  · exact B1717335
  · exact B1717339
  · exact B1717343
  · exact B1717347
  · exact B1717351
  · exact B1717355
  · exact B1717359
  · exact B1717363
  · exact B1717367
  · exact B1717371
  · exact B1717375
  · exact B1717379
  · exact B1717383
  · exact B1717387
  · exact B1717391
  · exact B1717395
  · exact B1717399
  · exact B1717403
  · exact B1717407
  · exact B1717411
  · exact B1717415
  · exact B1717419
  · exact B1717423
  · exact B1717427
  · exact B1717431
  · exact B1717435
  · exact B1717439
  · exact B1717443
  · exact B1717447
  · exact B1717451
  · exact B1717455
  · exact B1717459
  · exact B1717463
  · exact B1717467
  · exact B1717471
  · exact B1717475
  · exact B1717479
  · exact B1717483
  · exact B1717487
  · exact B1717491
  · exact B1717495
  · exact B1717499
  · exact B1717503
  · exact B1717507
  · exact B1717511
  · exact B1717515
  · exact B1717519
  · exact B1717523
  · exact B1717527
  · exact B1717531
  · exact B1717535
  · exact B1717539
  · exact B1717543
  · exact B1717547
  · exact B1717551
  · exact B1717555
  · exact B1717559
  · exact B1717563
  · exact B1717567
  · exact B1717571
  · exact B1717575
  · exact B1717579
  · exact B1717583
  · exact B1717587
  · exact B1717591
  · exact B1717595
  · exact B1717599
  · exact B1717603
  · exact B1717607
  · exact B1717611
  · exact B1717615
  · exact B1717619
  · exact B1717623
  · exact B1717627
  · exact B1717631
  · exact B1717635
  · exact B1717639
  · exact B1717643
  · exact B1717647
  · exact B1717651
  · exact B1717655
  · exact B1717659
  · exact B1717663
  · exact B1717667
  · exact B1717671
  · exact B1717675
  · exact B1717679
  · exact B1717683
  · exact B1717687
  · exact B1717691
  · exact B1717695
  · exact B1717699
  · exact B1717703
  · exact B1717707
  · exact B1717711
  · exact B1717715
  · exact B1717719
  · exact B1717723
  · exact B1717727
  · exact B1717731
  · exact B1717735
  · exact B1717739
  · exact B1717743
  · exact B1717747
  · exact B1717751
  · exact B1717755
  · exact B1717759
  · exact B1717763
  · exact B1717767
  · exact B1717771
  · exact B1717775
  · exact B1717779
  · exact B1717783
  · exact B1717787
  · exact B1717791
  · exact B1717795
  · exact B1717799
  · exact B1717803
  · exact B1717807
  · exact B1717811
  · exact B1717815
  · exact B1717819
  · exact B1717823
  · exact B1717827
  · exact B1717831
  · exact B1717835
  · exact B1717839
  · exact B1717843
  · exact B1717847
  · exact B1717851
  · exact B1717855
  · exact B1717859
  · exact B1717863
  · exact B1717867
  · exact B1717871
  · exact B1717875
  · exact B1717879
  · exact B1717883
  · exact B1717887
  · exact B1717891
  · exact B1717895
  · exact B1717899
  · exact B1717903
  · exact B1717907
  · exact B1717911
  · exact B1717915
  · exact B1717919
  · exact B1717923
  · exact B1717927
  · exact B1717931
  · exact B1717935
  · exact B1717939
  · exact B1717943
  · exact B1717947
  · exact B1717951
  · exact B1717955
  · exact B1717959
  · exact B1717963
  · exact B1717967
  · exact B1717971
  · exact B1717975
  · exact B1717979
  · exact B1717983
  · exact B1717987
  · exact B1717991
  · exact B1717995
  · exact B1717999
  · exact B1718003
  · exact B1718007
  · exact B1718011
  · exact B1718015
  · exact B1718019
  · exact B1718023
  · exact B1718027
  · exact B1718031
  · exact B1718035
  · exact B1718039
  · exact B1718043
  · exact B1718047
  · exact B1718051
  · exact B1718055
  · exact B1718059
  · exact B1718063
  · exact B1718067
  · exact B1718071
  · exact B1718075
  · exact B1718079
  · exact B1718083
  · exact B1718087
  · exact B1718091
  · exact B1718095
  · exact B1718099
  · exact B1718103
  · exact B1718107
  · exact B1718111
  · exact B1718115
  · exact B1718119
  · exact B1718123
  · exact B1718127
  · exact B1718131
  · exact B1718135
  · exact B1718139
  · exact B1718143
  · exact B1718147
  · exact B1718151
  · exact B1718155
  · exact B1718159
  · exact B1718163
  · exact B1718167
  · exact B1718171
  · exact B1718175
  · exact B1718179
  · exact B1718183
  · exact B1718187
  · exact B1718191
  · exact B1718195
  · exact B1718199
  · exact B1718203
  · exact B1718207
  · exact B1718211
  · exact B1718215
  · exact B1718219
  · exact B1718223
  · exact B1718227
  · exact B1718231
  · exact B1718235
  · exact B1718239
  · exact B1718243
  · exact B1718247
  · exact B1718251
  · exact B1718255
  · exact B1718259
  · exact B1718263
  · exact B1718267
  · exact B1718271
  · exact B1718275
  · exact B1718279
  · exact B1718283
  · exact B1718287
  · exact B1718291
  · exact B1718295
  · exact B1718299
  · exact B1718303
  · exact B1718307
  · exact B1718311
  · exact B1718315
  · exact B1718319
  · exact B1718323
  · exact B1718327
  · exact B1718331
  · exact B1718335
  · exact B1718339
  · exact B1718343
  · exact B1718347
  · exact B1718351
  · exact B1718355
  · exact B1718359
  · exact B1718363
  · exact B1718367
  · exact B1718371
  · exact B1718375
  · exact B1718379
  · exact B1718383
  · exact B1718387
  · exact B1718391
  · exact B1718395
  · exact B1718399
  · exact B1718403
  · exact B1718407
  · exact B1718411
  · exact B1718415
  · exact B1718419
  · exact B1718423
  · exact B1718427
  · exact B1718431
  · exact B1718435
  · exact B1718439
  · exact B1718443
  · exact B1718447
  · exact B1718451
  · exact B1718455
  · exact B1718459
  · exact B1718463
  · exact B1718467
  · exact B1718471
  · exact B1718475
  · exact B1718479
  · exact B1718483
  · exact B1718487
  · exact B1718491
  · exact B1718495
  · exact B1718499
  · exact B1718503
  · exact B1718507
  · exact B1718511
  · exact B1718515
  · exact B1718519
  · exact B1718523
  · exact B1718527
  · exact B1718531
  · exact B1718535
  · exact B1718539
  · exact B1718543
  · exact B1718547
  · exact B1718551
  · exact B1718555
  · exact B1718559
  · exact B1718563
  · exact B1718567
  · exact B1718571
  · exact B1718575
  · exact B1718579
  · exact B1718583
  · exact B1718587
  · exact B1718591
  · exact B1718595
  · exact B1718599
  · exact B1718603
  · exact B1718607
  · exact B1718611
  · exact B1718615
  · exact B1718619
  · exact B1718623
  · exact B1718627
  · exact B1718631
  · exact B1718635
  · exact B1718639
  · exact B1718643
  · exact B1718647
  · exact B1718651
  · exact B1718655
  · exact B1718659
  · exact B1718663
  · exact B1718667
  · exact B1718671
  · exact B1718675
  · exact B1718679
  · exact B1718683
  · exact B1718687
  · exact B1718691
  · exact B1718695
  · exact B1718699
  · exact B1718703
  · exact B1718707
  · exact B1718711
  · exact B1718715
  · exact B1718719
  · exact B1718723
  · exact B1718727
  · exact B1718731
  · exact B1718735
  · exact B1718739
  · exact B1718743
  · exact B1718747
  · exact B1718751
  · exact B1718755
  · exact B1718759
  · exact B1718763
  · exact B1718767
  · exact B1718771
  · exact B1718775
  · exact B1718779
  · exact B1718783
  · exact B1718787
  · exact B1718791
  · exact B1718795
  · exact B1718799
  · exact B1718803
  · exact B1718807
  · exact B1718811
  · exact B1718815
  · exact B1718819
  · exact B1718823
  · exact B1718827
  · exact B1718831
  · exact B1718835
  · exact B1718839
  · exact B1718843
  · exact B1718847
  · exact B1718851
  · exact B1718855
  · exact B1718859
  · exact B1718863
  · exact B1718867
  · exact B1718871
  · exact B1718875
  · exact B1718879
  · exact B1718883
  · exact B1718887
  · exact B1718891
  · exact B1718895
  · exact B1718899
  · exact B1718903
  · exact B1718907
  · exact B1718911
  · exact B1718915
  · exact B1718919
  · exact B1718923
  · exact B1718927
  · exact B1718931
  · exact B1718935
  · exact B1718939
  · exact B1718943
  · exact B1718947
  · exact B1718951
  · exact B1718955
  · exact B1718959
  · exact B1718963
  · exact B1718967
  · exact B1718971
  · exact B1718975
  · exact B1718979
  · exact B1718983
  · exact B1718987
  · exact B1718991
  · exact B1718995
  · exact B1718999
  · exact B1719003
  · exact B1719007
  · exact B1719011
  · exact B1719015
  · exact B1719019
  · exact B1719023
  · exact B1719027
  · exact B1719031
  · exact B1719035
  · exact B1719039
  · exact B1719043
  · exact B1719047
  · exact B1719051
  · exact B1719055
  · exact B1719059

theorem solution (m : ℕ) (hlo : 1717059 ≤ m) (hhi : m ≤ 1719059) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 429264 ≤ j := by omega
    have hj2 : j ≤ 429764 := by omega
    have hb : Blo 1717059 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
