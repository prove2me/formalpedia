-- Prove2me | solution 1 for syracuse_descends_range_1461050_1462550
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:44:11.972132+00:00
-- url     : https://prove2.me/submissions/26b73005-ac05-4465-950e-65e118085dc3

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


theorem B2465869 : Blo 1461050 2465869 := bbase (se 3 (by rfl) ⟨462350, by rfl⟩ : syracuseStep 2465869 = 924701) (by norm_num)
theorem B2080885 : Blo 1461050 2080885 := bbase (se 5 (by rfl) ⟨97541, by rfl⟩ : syracuseStep 2080885 = 195083) (by norm_num)
theorem B2465957 : Blo 1461050 2465957 := bbase (se 4 (by rfl) ⟨231183, by rfl⟩ : syracuseStep 2465957 = 462367) (by norm_num)
theorem B4931765 : Blo 1461050 4931765 := bbase (se 5 (by rfl) ⟨231176, by rfl⟩ : syracuseStep 4931765 = 462353) (by norm_num)
theorem B6004949 : Blo 1461050 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B6086917 : Blo 1461050 6086917 := bbase (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) (by norm_num)
theorem B2466085 : Blo 1461050 2466085 := bbase (se 4 (by rfl) ⟨231195, by rfl⟩ : syracuseStep 2466085 = 462391) (by norm_num)
theorem B2466173 : Blo 1461050 2466173 := bbase (se 3 (by rfl) ⟨462407, by rfl⟩ : syracuseStep 2466173 = 924815) (by norm_num)
theorem B12493237 : Blo 1461050 12493237 := bbase (se 5 (by rfl) ⟨585620, by rfl⟩ : syracuseStep 12493237 = 1171241) (by norm_num)
theorem B2081261 : Blo 1461050 2081261 := bbase (se 3 (by rfl) ⟨390236, by rfl⟩ : syracuseStep 2081261 = 780473) (by norm_num)
theorem B2466301 : Blo 1461050 2466301 := bbase (se 3 (by rfl) ⟨462431, by rfl⟩ : syracuseStep 2466301 = 924863) (by norm_num)
theorem B3121669 : Blo 1461050 3121669 := bbase (se 4 (by rfl) ⟨292656, by rfl⟩ : syracuseStep 3121669 = 585313) (by norm_num)
theorem B11100725 : Blo 1461050 11100725 := bbase (se 5 (by rfl) ⟨520346, by rfl⟩ : syracuseStep 11100725 = 1040693) (by norm_num)
theorem B1901117 : Blo 1461050 1901117 := bbase (se 3 (by rfl) ⟨356459, by rfl⟩ : syracuseStep 1901117 = 712919) (by norm_num)
theorem B2466389 : Blo 1461050 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B4932197 : Blo 1461050 4932197 := bbase (se 4 (by rfl) ⟨462393, by rfl⟩ : syracuseStep 4932197 = 924787) (by norm_num)
theorem B7398053 : Blo 1461050 7398053 := bbase (se 4 (by rfl) ⟨693567, by rfl⟩ : syracuseStep 7398053 = 1387135) (by norm_num)
theorem B2466517 : Blo 1461050 2466517 := bbase (se 7 (by rfl) ⟨28904, by rfl⟩ : syracuseStep 2466517 = 57809) (by norm_num)
theorem B2851549 : Blo 1461050 2851549 := bbase (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) (by norm_num)
theorem B1581853 : Blo 1461050 1581853 := bbase (se 3 (by rfl) ⟨296597, by rfl⟩ : syracuseStep 1581853 = 593195) (by norm_num)
theorem B2466605 : Blo 1461050 2466605 := bbase (se 3 (by rfl) ⟨462488, by rfl⟩ : syracuseStep 2466605 = 924977) (by norm_num)
theorem B2466733 : Blo 1461050 2466733 := bbase (se 3 (by rfl) ⟨462512, by rfl⟩ : syracuseStep 2466733 = 925025) (by norm_num)
theorem B3122165 : Blo 1461050 3122165 := bbase (se 5 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 3122165 = 292703) (by norm_num)
theorem B10003445 : Blo 1461050 10003445 := bbase (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) (by norm_num)
theorem B1713145 : Blo 1461050 1713145 := bbase (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) (by norm_num)
theorem B2466821 : Blo 1461050 2466821 := bbase (se 4 (by rfl) ⟨231264, by rfl⟩ : syracuseStep 2466821 = 462529) (by norm_num)
theorem B4932629 : Blo 1461050 4932629 := bbase (se 6 (by rfl) ⟨115608, by rfl⟩ : syracuseStep 4932629 = 231217) (by norm_num)
theorem B1975357 : Blo 1461050 1975357 := bbase (se 3 (by rfl) ⟨370379, by rfl⟩ : syracuseStep 1975357 = 740759) (by norm_num)
theorem B2466949 : Blo 1461050 2466949 := bbase (se 4 (by rfl) ⟨231276, by rfl⟩ : syracuseStep 2466949 = 462553) (by norm_num)
theorem B11854997 : Blo 1461050 11854997 := bbase (se 6 (by rfl) ⟨277851, by rfl⟩ : syracuseStep 11854997 = 555703) (by norm_num)
theorem B2467037 : Blo 1461050 2467037 := bbase (se 3 (by rfl) ⟨462569, by rfl⟩ : syracuseStep 2467037 = 925139) (by norm_num)
theorem B7120133 : Blo 1461050 7120133 := bbase (se 4 (by rfl) ⟨667512, by rfl⟩ : syracuseStep 7120133 = 1335025) (by norm_num)
theorem B4162853 : Blo 1461050 4162853 := bbase (se 4 (by rfl) ⟨390267, by rfl⟩ : syracuseStep 4162853 = 780535) (by norm_num)
theorem B2467165 : Blo 1461050 2467165 := bbase (se 3 (by rfl) ⟨462593, by rfl⟩ : syracuseStep 2467165 = 925187) (by norm_num)
theorem B6243749 : Blo 1461050 6243749 := bbase (se 4 (by rfl) ⟨585351, by rfl⟩ : syracuseStep 6243749 = 1170703) (by norm_num)
theorem B2467253 : Blo 1461050 2467253 := bbase (se 5 (by rfl) ⟨115652, by rfl⟩ : syracuseStep 2467253 = 231305) (by norm_num)
theorem B4933061 : Blo 1461050 4933061 := bbase (se 4 (by rfl) ⟨462474, by rfl⟩ : syracuseStep 4933061 = 924949) (by norm_num)
theorem B11855317 : Blo 1461050 11855317 := bbase (se 7 (by rfl) ⟨138929, by rfl⟩ : syracuseStep 11855317 = 277859) (by norm_num)
theorem B4220389 : Blo 1461050 4220389 := bbase (se 4 (by rfl) ⟨395661, by rfl⟩ : syracuseStep 4220389 = 791323) (by norm_num)
theorem B2467381 : Blo 1461050 2467381 := bbase (se 5 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 2467381 = 231317) (by norm_num)
theorem B2467469 : Blo 1461050 2467469 := bbase (se 3 (by rfl) ⟨462650, by rfl⟩ : syracuseStep 2467469 = 925301) (by norm_num)
theorem B2467597 : Blo 1461050 2467597 := bbase (se 3 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 2467597 = 925349) (by norm_num)
theorem B5547797 : Blo 1461050 5547797 := bbase (se 6 (by rfl) ⟨130026, by rfl⟩ : syracuseStep 5547797 = 260053) (by norm_num)
theorem B3123029 : Blo 1461050 3123029 := bbase (se 9 (by rfl) ⟨9149, by rfl⟩ : syracuseStep 3123029 = 18299) (by norm_num)
theorem B2467685 : Blo 1461050 2467685 := bbase (se 4 (by rfl) ⟨231345, by rfl⟩ : syracuseStep 2467685 = 462691) (by norm_num)
theorem B4933493 : Blo 1461050 4933493 := bbase (se 5 (by rfl) ⟨231257, by rfl⟩ : syracuseStep 4933493 = 462515) (by norm_num)
theorem B7399349 : Blo 1461050 7399349 := bbase (se 5 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 7399349 = 693689) (by norm_num)
theorem B4163525 : Blo 1461050 4163525 := bbase (se 4 (by rfl) ⟨390330, by rfl⟩ : syracuseStep 4163525 = 780661) (by norm_num)
theorem B3123173 : Blo 1461050 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B2467813 : Blo 1461050 2467813 := bbase (se 4 (by rfl) ⟨231357, by rfl⟩ : syracuseStep 2467813 = 462715) (by norm_num)
theorem B10823669 : Blo 1461050 10823669 := bbase (se 5 (by rfl) ⟨507359, by rfl⟩ : syracuseStep 10823669 = 1014719) (by norm_num)
theorem B1583101 : Blo 1461050 1583101 := bbase (se 3 (by rfl) ⟨296831, by rfl⟩ : syracuseStep 1583101 = 593663) (by norm_num)
theorem B5548085 : Blo 1461050 5548085 := bbase (se 5 (by rfl) ⟨260066, by rfl⟩ : syracuseStep 5548085 = 520133) (by norm_num)
theorem B2467901 : Blo 1461050 2467901 := bbase (se 3 (by rfl) ⟨462731, by rfl⟩ : syracuseStep 2467901 = 925463) (by norm_num)
theorem B2468029 : Blo 1461050 2468029 := bbase (se 3 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 2468029 = 925511) (by norm_num)
theorem B1755373 : Blo 1461050 1755373 := bbase (se 3 (by rfl) ⟨329132, by rfl⟩ : syracuseStep 1755373 = 658265) (by norm_num)
theorem B1976557 : Blo 1461050 1976557 := bbase (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) (by norm_num)
theorem B4933925 : Blo 1461050 4933925 := bbase (se 4 (by rfl) ⟨462555, by rfl⟩ : syracuseStep 4933925 = 925111) (by norm_num)
theorem B1976621 : Blo 1461050 1976621 := bbase (se 3 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 1976621 = 741233) (by norm_num)
theorem B4163957 : Blo 1461050 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B1780093 : Blo 1461050 1780093 := bbase (se 3 (by rfl) ⟨333767, by rfl⟩ : syracuseStep 1780093 = 667535) (by norm_num)
theorem B3287429 : Blo 1461050 3287429 := bbase (se 4 (by rfl) ⟨308196, by rfl⟩ : syracuseStep 3287429 = 616393) (by norm_num)
theorem B1755589 : Blo 1461050 1755589 := bbase (se 4 (by rfl) ⟨164586, by rfl⟩ : syracuseStep 1755589 = 329173) (by norm_num)
theorem B3287501 : Blo 1461050 3287501 := bbase (se 3 (by rfl) ⟨616406, by rfl⟩ : syracuseStep 3287501 = 1232813) (by norm_num)
theorem B2812429 : Blo 1461050 2812429 := bbase (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) (by norm_num)
theorem B3287573 : Blo 1461050 3287573 := bbase (se 6 (by rfl) ⟨77052, by rfl⟩ : syracuseStep 3287573 = 154105) (by norm_num)
theorem B7023125 : Blo 1461050 7023125 := bbase (se 6 (by rfl) ⟨164604, by rfl⟩ : syracuseStep 7023125 = 329209) (by norm_num)
theorem B1804853 : Blo 1461050 1804853 := bbase (se 5 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 1804853 = 169205) (by norm_num)
theorem B3287645 : Blo 1461050 3287645 := bbase (se 3 (by rfl) ⟨616433, by rfl⟩ : syracuseStep 3287645 = 1232867) (by norm_num)
theorem B1755757 : Blo 1461050 1755757 := bbase (se 3 (by rfl) ⟨329204, by rfl⟩ : syracuseStep 1755757 = 658409) (by norm_num)
theorem B3287717 : Blo 1461050 3287717 := bbase (se 4 (by rfl) ⟨308223, by rfl⟩ : syracuseStep 3287717 = 616447) (by norm_num)
theorem B10537685 : Blo 1461050 10537685 := bbase (se 7 (by rfl) ⟨123488, by rfl⟩ : syracuseStep 10537685 = 246977) (by norm_num)
theorem B4934357 : Blo 1461050 4934357 := bbase (se 7 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 4934357 = 115649) (by norm_num)
theorem B3287789 : Blo 1461050 3287789 := bbase (se 3 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 3287789 = 1232921) (by norm_num)
theorem B3287861 : Blo 1461050 3287861 := bbase (se 5 (by rfl) ⟨154118, by rfl⟩ : syracuseStep 3287861 = 308237) (by norm_num)
theorem B3287933 : Blo 1461050 3287933 := bbase (se 3 (by rfl) ⟨616487, by rfl⟩ : syracuseStep 3287933 = 1232975) (by norm_num)
theorem B2501525 : Blo 1461050 2501525 := bbase (se 6 (by rfl) ⟨58629, by rfl⟩ : syracuseStep 2501525 = 117259) (by norm_num)
theorem B3288005 : Blo 1461050 3288005 := bbase (se 4 (by rfl) ⟨308250, by rfl⟩ : syracuseStep 3288005 = 616501) (by norm_num)
theorem B3288077 : Blo 1461050 3288077 := bbase (se 3 (by rfl) ⟨616514, by rfl⟩ : syracuseStep 3288077 = 1233029) (by norm_num)
theorem B3288149 : Blo 1461050 3288149 := bbase (se 8 (by rfl) ⟨19266, by rfl⟩ : syracuseStep 3288149 = 38533) (by norm_num)
theorem B5925973 : Blo 1461050 5925973 := bbase (se 8 (by rfl) ⟨34722, by rfl⟩ : syracuseStep 5925973 = 69445) (by norm_num)
theorem B4164709 : Blo 1461050 4164709 := bbase (se 4 (by rfl) ⟨390441, by rfl⟩ : syracuseStep 4164709 = 780883) (by norm_num)
theorem B1756285 : Blo 1461050 1756285 := bbase (se 3 (by rfl) ⟨329303, by rfl⟩ : syracuseStep 1756285 = 658607) (by norm_num)
theorem B4934789 : Blo 1461050 4934789 := bbase (se 4 (by rfl) ⟨462636, by rfl⟩ : syracuseStep 4934789 = 925273) (by norm_num)
theorem B6245525 : Blo 1461050 6245525 := bbase (se 6 (by rfl) ⟨146379, by rfl⟩ : syracuseStep 6245525 = 292759) (by norm_num)
theorem B3288221 : Blo 1461050 3288221 := bbase (se 3 (by rfl) ⟨616541, by rfl⟩ : syracuseStep 3288221 = 1233083) (by norm_num)
theorem B7400645 : Blo 1461050 7400645 := bbase (se 4 (by rfl) ⟨693810, by rfl⟩ : syracuseStep 7400645 = 1387621) (by norm_num)
theorem B5549269 : Blo 1461050 5549269 := bbase (se 7 (by rfl) ⟨65030, by rfl⟩ : syracuseStep 5549269 = 130061) (by norm_num)
theorem B3288293 : Blo 1461050 3288293 := bbase (se 4 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 3288293 = 616555) (by norm_num)
theorem B3288365 : Blo 1461050 3288365 := bbase (se 3 (by rfl) ⟨616568, by rfl⟩ : syracuseStep 3288365 = 1233137) (by norm_num)
theorem B2223445 : Blo 1461050 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B3288437 : Blo 1461050 3288437 := bbase (se 5 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 3288437 = 308291) (by norm_num)
theorem B5270933 : Blo 1461050 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B3288509 : Blo 1461050 3288509 := bbase (se 3 (by rfl) ⟨616595, by rfl⟩ : syracuseStep 3288509 = 1233191) (by norm_num)
theorem B3288581 : Blo 1461050 3288581 := bbase (se 4 (by rfl) ⟨308304, by rfl⟩ : syracuseStep 3288581 = 616609) (by norm_num)
theorem B5549573 : Blo 1461050 5549573 := bbase (se 4 (by rfl) ⟨520272, by rfl⟩ : syracuseStep 5549573 = 1040545) (by norm_num)
theorem B4574773 : Blo 1461050 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B4935221 : Blo 1461050 4935221 := bbase (se 5 (by rfl) ⟨231338, by rfl⟩ : syracuseStep 4935221 = 462677) (by norm_num)
theorem B3288653 : Blo 1461050 3288653 := bbase (se 3 (by rfl) ⟨616622, by rfl⟩ : syracuseStep 3288653 = 1233245) (by norm_num)
theorem B3288725 : Blo 1461050 3288725 := bbase (se 6 (by rfl) ⟨77079, by rfl⟩ : syracuseStep 3288725 = 154159) (by norm_num)
theorem B3288797 : Blo 1461050 3288797 := bbase (se 3 (by rfl) ⟨616649, by rfl⟩ : syracuseStep 3288797 = 1233299) (by norm_num)
theorem B3288869 : Blo 1461050 3288869 := bbase (se 4 (by rfl) ⟨308331, by rfl⟩ : syracuseStep 3288869 = 616663) (by norm_num)
theorem B3952421 : Blo 1461050 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B7499573 : Blo 1461050 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B1560421 : Blo 1461050 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B3288941 : Blo 1461050 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B3698581 : Blo 1461050 3698581 := bbase (se 6 (by rfl) ⟨86685, by rfl⟩ : syracuseStep 3698581 = 173371) (by norm_num)
theorem B1560493 : Blo 1461050 1560493 := bbase (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) (by norm_num)
theorem B3289013 : Blo 1461050 3289013 := bbase (se 5 (by rfl) ⟨154172, by rfl⟩ : syracuseStep 3289013 = 308345) (by norm_num)
theorem B4935653 : Blo 1461050 4935653 := bbase (se 4 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 4935653 = 925435) (by norm_num)
theorem B3289085 : Blo 1461050 3289085 := bbase (se 3 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 3289085 = 1233407) (by norm_num)
theorem B3698693 : Blo 1461050 3698693 := bbase (se 4 (by rfl) ⟨346752, by rfl⟩ : syracuseStep 3698693 = 693505) (by norm_num)
theorem B3289157 : Blo 1461050 3289157 := bbase (se 4 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 3289157 = 616717) (by norm_num)
theorem B4681813 : Blo 1461050 4681813 := bbase (se 8 (by rfl) ⟨27432, by rfl⟩ : syracuseStep 4681813 = 54865) (by norm_num)
theorem B2003053 : Blo 1461050 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B6246517 : Blo 1461050 6246517 := bbase (se 5 (by rfl) ⟨292805, by rfl⟩ : syracuseStep 6246517 = 585611) (by norm_num)
theorem B3289229 : Blo 1461050 3289229 := bbase (se 3 (by rfl) ⟨616730, by rfl⟩ : syracuseStep 3289229 = 1233461) (by norm_num)
theorem B3698885 : Blo 1461050 3698885 := bbase (se 4 (by rfl) ⟨346770, by rfl⟩ : syracuseStep 3698885 = 693541) (by norm_num)
theorem B31600853 : Blo 1461050 31600853 := bbase (se 7 (by rfl) ⟨370322, by rfl⟩ : syracuseStep 31600853 = 740645) (by norm_num)
theorem B3289301 : Blo 1461050 3289301 := bbase (se 7 (by rfl) ⟨38546, by rfl⟩ : syracuseStep 3289301 = 77093) (by norm_num)
theorem B2191589 : Blo 1461050 2191589 := bbase (se 4 (by rfl) ⟨205461, by rfl⟩ : syracuseStep 2191589 = 410923) (by norm_num)
theorem B2191613 : Blo 1461050 2191613 := bbase (se 3 (by rfl) ⟨410927, by rfl⟩ : syracuseStep 2191613 = 821855) (by norm_num)
theorem B2191637 : Blo 1461050 2191637 := bbase (se 6 (by rfl) ⟨51366, by rfl⟩ : syracuseStep 2191637 = 102733) (by norm_num)
theorem B3289373 : Blo 1461050 3289373 := bbase (se 3 (by rfl) ⟨616757, by rfl⟩ : syracuseStep 3289373 = 1233515) (by norm_num)
theorem B1560865 : Blo 1461050 1560865 := bbase (se 2 (by rfl) ⟨585324, by rfl⟩ : syracuseStep 1560865 = 1170649) (by norm_num)
theorem B2191661 : Blo 1461050 2191661 := bbase (se 3 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 2191661 = 821873) (by norm_num)
theorem B2191685 : Blo 1461050 2191685 := bbase (se 4 (by rfl) ⟨205470, by rfl⟩ : syracuseStep 2191685 = 410941) (by norm_num)
theorem B2191709 : Blo 1461050 2191709 := bbase (se 3 (by rfl) ⟨410945, by rfl⟩ : syracuseStep 2191709 = 821891) (by norm_num)
theorem B3289445 : Blo 1461050 3289445 := bbase (se 4 (by rfl) ⟨308385, by rfl⟩ : syracuseStep 3289445 = 616771) (by norm_num)
theorem B2191733 : Blo 1461050 2191733 := bbase (se 5 (by rfl) ⟨102737, by rfl⟩ : syracuseStep 2191733 = 205475) (by norm_num)
theorem B2191757 : Blo 1461050 2191757 := bbase (se 3 (by rfl) ⟨410954, by rfl⟩ : syracuseStep 2191757 = 821909) (by norm_num)
theorem B4936085 : Blo 1461050 4936085 := bbase (se 6 (by rfl) ⟨115689, by rfl⟩ : syracuseStep 4936085 = 231379) (by norm_num)
theorem B2191781 : Blo 1461050 2191781 := bbase (se 4 (by rfl) ⟨205479, by rfl⟩ : syracuseStep 2191781 = 410959) (by norm_num)
theorem B3289517 : Blo 1461050 3289517 := bbase (se 3 (by rfl) ⟨616784, by rfl⟩ : syracuseStep 3289517 = 1233569) (by norm_num)
theorem B2191805 : Blo 1461050 2191805 := bbase (se 3 (by rfl) ⟨410963, by rfl⟩ : syracuseStep 2191805 = 821927) (by norm_num)
theorem B2191829 : Blo 1461050 2191829 := bbase (se 7 (by rfl) ⟨25685, by rfl⟩ : syracuseStep 2191829 = 51371) (by norm_num)
theorem B7401941 : Blo 1461050 7401941 := bbase (se 7 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 7401941 = 173483) (by norm_num)
theorem B2191853 : Blo 1461050 2191853 := bbase (se 3 (by rfl) ⟨410972, by rfl⟩ : syracuseStep 2191853 = 821945) (by norm_num)
theorem B3289589 : Blo 1461050 3289589 := bbase (se 5 (by rfl) ⟨154199, by rfl⟩ : syracuseStep 3289589 = 308399) (by norm_num)
theorem B2191877 : Blo 1461050 2191877 := bbase (se 4 (by rfl) ⟨205488, by rfl⟩ : syracuseStep 2191877 = 410977) (by norm_num)
theorem B2191901 : Blo 1461050 2191901 := bbase (se 3 (by rfl) ⟨410981, by rfl⟩ : syracuseStep 2191901 = 821963) (by norm_num)
theorem B3699229 : Blo 1461050 3699229 := bbase (se 3 (by rfl) ⟨693605, by rfl⟩ : syracuseStep 3699229 = 1387211) (by norm_num)
theorem B2191925 : Blo 1461050 2191925 := bbase (se 5 (by rfl) ⟨102746, by rfl⟩ : syracuseStep 2191925 = 205493) (by norm_num)
theorem B3289661 : Blo 1461050 3289661 := bbase (se 3 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 3289661 = 1233623) (by norm_num)
theorem B2191949 : Blo 1461050 2191949 := bbase (se 3 (by rfl) ⟨410990, by rfl⟩ : syracuseStep 2191949 = 821981) (by norm_num)
theorem B2191973 : Blo 1461050 2191973 := bbase (se 4 (by rfl) ⟨205497, by rfl⟩ : syracuseStep 2191973 = 410995) (by norm_num)
theorem B2110061 : Blo 1461050 2110061 := bbase (se 3 (by rfl) ⟨395636, by rfl⟩ : syracuseStep 2110061 = 791273) (by norm_num)
theorem B2191997 : Blo 1461050 2191997 := bbase (se 3 (by rfl) ⟨410999, by rfl⟩ : syracuseStep 2191997 = 821999) (by norm_num)
theorem B3289733 : Blo 1461050 3289733 := bbase (se 4 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 3289733 = 616825) (by norm_num)
theorem B3699341 : Blo 1461050 3699341 := bbase (se 3 (by rfl) ⟨693626, by rfl⟩ : syracuseStep 3699341 = 1387253) (by norm_num)
theorem B2192021 : Blo 1461050 2192021 := bbase (se 6 (by rfl) ⟨51375, by rfl⟩ : syracuseStep 2192021 = 102751) (by norm_num)
theorem B1561241 : Blo 1461050 1561241 := bbase (se 2 (by rfl) ⟨585465, by rfl⟩ : syracuseStep 1561241 = 1170931) (by norm_num)
theorem B2372261 : Blo 1461050 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B2192045 : Blo 1461050 2192045 := bbase (se 3 (by rfl) ⟨411008, by rfl⟩ : syracuseStep 2192045 = 822017) (by norm_num)
theorem B2192069 : Blo 1461050 2192069 := bbase (se 4 (by rfl) ⟨205506, by rfl⟩ : syracuseStep 2192069 = 411013) (by norm_num)
theorem B3961541 : Blo 1461050 3961541 := bbase (se 4 (by rfl) ⟨371394, by rfl⟩ : syracuseStep 3961541 = 742789) (by norm_num)
theorem B3289805 : Blo 1461050 3289805 := bbase (se 3 (by rfl) ⟨616838, by rfl⟩ : syracuseStep 3289805 = 1233677) (by norm_num)
theorem B2192093 : Blo 1461050 2192093 := bbase (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) (by norm_num)
theorem B1561313 : Blo 1461050 1561313 := bbase (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) (by norm_num)
theorem B2192117 : Blo 1461050 2192117 := bbase (se 5 (by rfl) ⟨102755, by rfl⟩ : syracuseStep 2192117 = 205511) (by norm_num)
theorem B2192141 : Blo 1461050 2192141 := bbase (se 3 (by rfl) ⟨411026, by rfl⟩ : syracuseStep 2192141 = 822053) (by norm_num)
theorem B3289877 : Blo 1461050 3289877 := bbase (se 6 (by rfl) ⟨77106, by rfl⟩ : syracuseStep 3289877 = 154213) (by norm_num)
theorem B2192165 : Blo 1461050 2192165 := bbase (se 4 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 2192165 = 411031) (by norm_num)
theorem B2192189 : Blo 1461050 2192189 := bbase (se 3 (by rfl) ⟨411035, by rfl⟩ : syracuseStep 2192189 = 822071) (by norm_num)
theorem B3699533 : Blo 1461050 3699533 := bbase (se 3 (by rfl) ⟨693662, by rfl⟩ : syracuseStep 3699533 = 1387325) (by norm_num)
theorem B2192213 : Blo 1461050 2192213 := bbase (se 9 (by rfl) ⟨6422, by rfl⟩ : syracuseStep 2192213 = 12845) (by norm_num)
theorem B3289949 : Blo 1461050 3289949 := bbase (se 3 (by rfl) ⟨616865, by rfl⟩ : syracuseStep 3289949 = 1233731) (by norm_num)
theorem B2192237 : Blo 1461050 2192237 := bbase (se 3 (by rfl) ⟨411044, by rfl⟩ : syracuseStep 2192237 = 822089) (by norm_num)
theorem B7025525 : Blo 1461050 7025525 := bbase (se 5 (by rfl) ⟨329321, by rfl⟩ : syracuseStep 7025525 = 658643) (by norm_num)
theorem B2192261 : Blo 1461050 2192261 := bbase (se 4 (by rfl) ⟨205524, by rfl⟩ : syracuseStep 2192261 = 411049) (by norm_num)
theorem B8893333 : Blo 1461050 8893333 := bbase (se 6 (by rfl) ⟨208437, by rfl⟩ : syracuseStep 8893333 = 416875) (by norm_num)
theorem B2192285 : Blo 1461050 2192285 := bbase (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) (by norm_num)
theorem B1561501 : Blo 1461050 1561501 := bbase (se 3 (by rfl) ⟨292781, by rfl⟩ : syracuseStep 1561501 = 585563) (by norm_num)
theorem B3290021 : Blo 1461050 3290021 := bbase (se 4 (by rfl) ⟨308439, by rfl⟩ : syracuseStep 3290021 = 616879) (by norm_num)
theorem B3748781 : Blo 1461050 3748781 := bbase (se 3 (by rfl) ⟨702896, by rfl⟩ : syracuseStep 3748781 = 1405793) (by norm_num)
theorem B2192309 : Blo 1461050 2192309 := bbase (se 5 (by rfl) ⟨102764, by rfl⟩ : syracuseStep 2192309 = 205529) (by norm_num)
theorem B6329285 : Blo 1461050 6329285 := bbase (se 4 (by rfl) ⟨593370, by rfl⟩ : syracuseStep 6329285 = 1186741) (by norm_num)
theorem B2192333 : Blo 1461050 2192333 := bbase (se 3 (by rfl) ⟨411062, by rfl⟩ : syracuseStep 2192333 = 822125) (by norm_num)
theorem B2372573 : Blo 1461050 2372573 := bbase (se 3 (by rfl) ⟨444857, by rfl⟩ : syracuseStep 2372573 = 889715) (by norm_num)
theorem B2192357 : Blo 1461050 2192357 := bbase (se 4 (by rfl) ⟨205533, by rfl⟩ : syracuseStep 2192357 = 411067) (by norm_num)
theorem B2773997 : Blo 1461050 2773997 := bbase (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) (by norm_num)
theorem B3290093 : Blo 1461050 3290093 := bbase (se 3 (by rfl) ⟨616892, by rfl⟩ : syracuseStep 3290093 = 1233785) (by norm_num)
theorem B2192381 : Blo 1461050 2192381 := bbase (se 3 (by rfl) ⟨411071, by rfl⟩ : syracuseStep 2192381 = 822143) (by norm_num)
theorem B2192405 : Blo 1461050 2192405 := bbase (se 6 (by rfl) ⟨51384, by rfl⟩ : syracuseStep 2192405 = 102769) (by norm_num)
theorem B2192429 : Blo 1461050 2192429 := bbase (se 3 (by rfl) ⟨411080, by rfl⟩ : syracuseStep 2192429 = 822161) (by norm_num)
theorem B3290165 : Blo 1461050 3290165 := bbase (se 5 (by rfl) ⟨154226, by rfl⟩ : syracuseStep 3290165 = 308453) (by norm_num)
theorem B2192453 : Blo 1461050 2192453 := bbase (se 4 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 2192453 = 411085) (by norm_num)
theorem B21353557 : Blo 1461050 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B39998549 : Blo 1461050 39998549 := bbase (se 8 (by rfl) ⟨234366, by rfl⟩ : syracuseStep 39998549 = 468733) (by norm_num)
theorem B1561685 : Blo 1461050 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B2192477 : Blo 1461050 2192477 := bbase (se 3 (by rfl) ⟨411089, by rfl⟩ : syracuseStep 2192477 = 822179) (by norm_num)
theorem B2192501 : Blo 1461050 2192501 := bbase (se 5 (by rfl) ⟨102773, by rfl⟩ : syracuseStep 2192501 = 205547) (by norm_num)
theorem B3290237 : Blo 1461050 3290237 := bbase (se 3 (by rfl) ⟨616919, by rfl⟩ : syracuseStep 3290237 = 1233839) (by norm_num)
theorem B2192525 : Blo 1461050 2192525 := bbase (se 3 (by rfl) ⟨411098, by rfl⟩ : syracuseStep 2192525 = 822197) (by norm_num)
theorem B2962597 : Blo 1461050 2962597 := bbase (se 4 (by rfl) ⟨277743, by rfl⟩ : syracuseStep 2962597 = 555487) (by norm_num)
theorem B3699877 : Blo 1461050 3699877 := bbase (se 4 (by rfl) ⟨346863, by rfl⟩ : syracuseStep 3699877 = 693727) (by norm_num)
theorem B2192549 : Blo 1461050 2192549 := bbase (se 4 (by rfl) ⟨205551, by rfl⟩ : syracuseStep 2192549 = 411103) (by norm_num)
theorem B1643701 : Blo 1461050 1643701 := bbase (se 5 (by rfl) ⟨77048, by rfl⟩ : syracuseStep 1643701 = 154097) (by norm_num)
theorem B2192573 : Blo 1461050 2192573 := bbase (se 3 (by rfl) ⟨411107, by rfl⟩ : syracuseStep 2192573 = 822215) (by norm_num)
theorem B3290309 : Blo 1461050 3290309 := bbase (se 4 (by rfl) ⟨308466, by rfl⟩ : syracuseStep 3290309 = 616933) (by norm_num)
theorem B2192597 : Blo 1461050 2192597 := bbase (se 7 (by rfl) ⟨25694, by rfl⟩ : syracuseStep 2192597 = 51389) (by norm_num)
theorem B1643737 : Blo 1461050 1643737 := bbase (se 2 (by rfl) ⟨616401, by rfl⟩ : syracuseStep 1643737 = 1232803) (by norm_num)
theorem B2192621 : Blo 1461050 2192621 := bbase (se 3 (by rfl) ⟨411116, by rfl⟩ : syracuseStep 2192621 = 822233) (by norm_num)
theorem B1643773 : Blo 1461050 1643773 := bbase (se 3 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 1643773 = 616415) (by norm_num)
theorem B2192645 : Blo 1461050 2192645 := bbase (se 4 (by rfl) ⟨205560, by rfl⟩ : syracuseStep 2192645 = 411121) (by norm_num)
theorem B3290381 : Blo 1461050 3290381 := bbase (se 3 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 3290381 = 1233893) (by norm_num)
theorem B3699989 : Blo 1461050 3699989 := bbase (se 6 (by rfl) ⟨86718, by rfl⟩ : syracuseStep 3699989 = 173437) (by norm_num)
theorem B2192669 : Blo 1461050 2192669 := bbase (se 3 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 2192669 = 822251) (by norm_num)
theorem B1643809 : Blo 1461050 1643809 := bbase (se 2 (by rfl) ⟨616428, by rfl⟩ : syracuseStep 1643809 = 1232857) (by norm_num)
theorem B2192693 : Blo 1461050 2192693 := bbase (se 5 (by rfl) ⟨102782, by rfl⟩ : syracuseStep 2192693 = 205565) (by norm_num)
theorem B1643845 : Blo 1461050 1643845 := bbase (se 4 (by rfl) ⟨154110, by rfl⟩ : syracuseStep 1643845 = 308221) (by norm_num)
theorem B2192717 : Blo 1461050 2192717 := bbase (se 3 (by rfl) ⟨411134, by rfl⟩ : syracuseStep 2192717 = 822269) (by norm_num)
theorem B14054741 : Blo 1461050 14054741 := bbase (se 13 (by rfl) ⟨2573, by rfl⟩ : syracuseStep 14054741 = 5147) (by norm_num)
theorem B3290453 : Blo 1461050 3290453 := bbase (se 13 (by rfl) ⟨602, by rfl⟩ : syracuseStep 3290453 = 1205) (by norm_num)
theorem B2192741 : Blo 1461050 2192741 := bbase (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) (by norm_num)
theorem B1643881 : Blo 1461050 1643881 := bbase (se 2 (by rfl) ⟨616455, by rfl⟩ : syracuseStep 1643881 = 1232911) (by norm_num)
theorem B2192765 : Blo 1461050 2192765 := bbase (se 3 (by rfl) ⟨411143, by rfl⟩ : syracuseStep 2192765 = 822287) (by norm_num)
theorem B1643917 : Blo 1461050 1643917 := bbase (se 3 (by rfl) ⟨308234, by rfl⟩ : syracuseStep 1643917 = 616469) (by norm_num)
theorem B2192789 : Blo 1461050 2192789 := bbase (se 6 (by rfl) ⟨51393, by rfl⟩ : syracuseStep 2192789 = 102787) (by norm_num)
theorem B3290525 : Blo 1461050 3290525 := bbase (se 3 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 3290525 = 1233947) (by norm_num)
theorem B2192813 : Blo 1461050 2192813 := bbase (se 3 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 2192813 = 822305) (by norm_num)
theorem B1643953 : Blo 1461050 1643953 := bbase (se 2 (by rfl) ⟨616482, by rfl⟩ : syracuseStep 1643953 = 1232965) (by norm_num)
theorem B2192837 : Blo 1461050 2192837 := bbase (se 4 (by rfl) ⟨205578, by rfl⟩ : syracuseStep 2192837 = 411157) (by norm_num)
theorem B1643989 : Blo 1461050 1643989 := bbase (se 7 (by rfl) ⟨19265, by rfl⟩ : syracuseStep 1643989 = 38531) (by norm_num)
theorem B3700181 : Blo 1461050 3700181 := bbase (se 7 (by rfl) ⟨43361, by rfl⟩ : syracuseStep 3700181 = 86723) (by norm_num)
theorem B2192861 : Blo 1461050 2192861 := bbase (se 3 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 2192861 = 822323) (by norm_num)
theorem B2635229 : Blo 1461050 2635229 := bbase (se 3 (by rfl) ⟨494105, by rfl⟩ : syracuseStep 2635229 = 988211) (by norm_num)
theorem B3290597 : Blo 1461050 3290597 := bbase (se 4 (by rfl) ⟨308493, by rfl⟩ : syracuseStep 3290597 = 616987) (by norm_num)
theorem B2192885 : Blo 1461050 2192885 := bbase (se 5 (by rfl) ⟨102791, by rfl⟩ : syracuseStep 2192885 = 205583) (by norm_num)
theorem B1644025 : Blo 1461050 1644025 := bbase (se 2 (by rfl) ⟨616509, by rfl⟩ : syracuseStep 1644025 = 1233019) (by norm_num)
theorem B2192909 : Blo 1461050 2192909 := bbase (se 3 (by rfl) ⟨411170, by rfl⟩ : syracuseStep 2192909 = 822341) (by norm_num)
theorem B1644061 : Blo 1461050 1644061 := bbase (se 3 (by rfl) ⟨308261, by rfl⟩ : syracuseStep 1644061 = 616523) (by norm_num)
theorem B2373157 : Blo 1461050 2373157 := bbase (se 4 (by rfl) ⟨222483, by rfl⟩ : syracuseStep 2373157 = 444967) (by norm_num)
theorem B2192933 : Blo 1461050 2192933 := bbase (se 4 (by rfl) ⟨205587, by rfl⟩ : syracuseStep 2192933 = 411175) (by norm_num)
theorem B3290669 : Blo 1461050 3290669 := bbase (se 3 (by rfl) ⟨617000, by rfl⟩ : syracuseStep 3290669 = 1234001) (by norm_num)
theorem B10532405 : Blo 1461050 10532405 := bbase (se 5 (by rfl) ⟨493706, by rfl⟩ : syracuseStep 10532405 = 987413) (by norm_num)
theorem B2283061 : Blo 1461050 2283061 := bbase (se 5 (by rfl) ⟨107018, by rfl⟩ : syracuseStep 2283061 = 214037) (by norm_num)
theorem B2192957 : Blo 1461050 2192957 := bbase (se 3 (by rfl) ⟨411179, by rfl⟩ : syracuseStep 2192957 = 822359) (by norm_num)
theorem B1644097 : Blo 1461050 1644097 := bbase (se 2 (by rfl) ⟨616536, by rfl⟩ : syracuseStep 1644097 = 1233073) (by norm_num)
theorem B5551685 : Blo 1461050 5551685 := bbase (se 4 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 5551685 = 1040941) (by norm_num)
theorem B2192981 : Blo 1461050 2192981 := bbase (se 8 (by rfl) ⟨12849, by rfl⟩ : syracuseStep 2192981 = 25699) (by norm_num)
theorem B1644133 : Blo 1461050 1644133 := bbase (se 4 (by rfl) ⟨154137, by rfl⟩ : syracuseStep 1644133 = 308275) (by norm_num)
theorem B2193005 : Blo 1461050 2193005 := bbase (se 3 (by rfl) ⟨411188, by rfl⟩ : syracuseStep 2193005 = 822377) (by norm_num)
theorem B2193029 : Blo 1461050 2193029 := bbase (se 4 (by rfl) ⟨205596, by rfl⟩ : syracuseStep 2193029 = 411193) (by norm_num)
theorem B1644169 : Blo 1461050 1644169 := bbase (se 2 (by rfl) ⟨616563, by rfl⟩ : syracuseStep 1644169 = 1233127) (by norm_num)
theorem B2193053 : Blo 1461050 2193053 := bbase (se 3 (by rfl) ⟨411197, by rfl⟩ : syracuseStep 2193053 = 822395) (by norm_num)
theorem B1644205 : Blo 1461050 1644205 := bbase (se 3 (by rfl) ⟨308288, by rfl⟩ : syracuseStep 1644205 = 616577) (by norm_num)
theorem B2193077 : Blo 1461050 2193077 := bbase (se 5 (by rfl) ⟨102800, by rfl⟩ : syracuseStep 2193077 = 205601) (by norm_num)
theorem B2193101 : Blo 1461050 2193101 := bbase (se 3 (by rfl) ⟨411206, by rfl⟩ : syracuseStep 2193101 = 822413) (by norm_num)
theorem B1644241 : Blo 1461050 1644241 := bbase (se 2 (by rfl) ⟨616590, by rfl⟩ : syracuseStep 1644241 = 1233181) (by norm_num)
theorem B2774749 : Blo 1461050 2774749 := bbase (se 3 (by rfl) ⟨520265, by rfl⟩ : syracuseStep 2774749 = 1040531) (by norm_num)
theorem B2193125 : Blo 1461050 2193125 := bbase (se 4 (by rfl) ⟨205605, by rfl⟩ : syracuseStep 2193125 = 411211) (by norm_num)
theorem B7403237 : Blo 1461050 7403237 := bbase (se 4 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 7403237 = 1388107) (by norm_num)
theorem B1644277 : Blo 1461050 1644277 := bbase (se 5 (by rfl) ⟨77075, by rfl⟩ : syracuseStep 1644277 = 154151) (by norm_num)
theorem B2193149 : Blo 1461050 2193149 := bbase (se 3 (by rfl) ⟨411215, by rfl⟩ : syracuseStep 2193149 = 822431) (by norm_num)
theorem B2963213 : Blo 1461050 2963213 := bbase (se 3 (by rfl) ⟨555602, by rfl⟩ : syracuseStep 2963213 = 1111205) (by norm_num)
theorem B2193173 : Blo 1461050 2193173 := bbase (se 6 (by rfl) ⟨51402, by rfl⟩ : syracuseStep 2193173 = 102805) (by norm_num)
theorem B1644313 : Blo 1461050 1644313 := bbase (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) (by norm_num)
theorem B3700525 : Blo 1461050 3700525 := bbase (se 3 (by rfl) ⟨693848, by rfl⟩ : syracuseStep 3700525 = 1387697) (by norm_num)
theorem B2193197 : Blo 1461050 2193197 := bbase (se 3 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 2193197 = 822449) (by norm_num)
theorem B1644349 : Blo 1461050 1644349 := bbase (se 3 (by rfl) ⟨308315, by rfl⟩ : syracuseStep 1644349 = 616631) (by norm_num)
theorem B2193221 : Blo 1461050 2193221 := bbase (se 4 (by rfl) ⟨205614, by rfl⟩ : syracuseStep 2193221 = 411229) (by norm_num)
theorem B1849169 : Blo 1461050 1849169 := bbase (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) (by norm_num)
theorem B2193245 : Blo 1461050 2193245 := bbase (se 3 (by rfl) ⟨411233, by rfl⟩ : syracuseStep 2193245 = 822467) (by norm_num)
theorem B1644385 : Blo 1461050 1644385 := bbase (se 2 (by rfl) ⟨616644, by rfl⟩ : syracuseStep 1644385 = 1233289) (by norm_num)
theorem B5551973 : Blo 1461050 5551973 := bbase (se 4 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 5551973 = 1040995) (by norm_num)
theorem B2774893 : Blo 1461050 2774893 := bbase (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) (by norm_num)
theorem B2193269 : Blo 1461050 2193269 := bbase (se 5 (by rfl) ⟨102809, by rfl⟩ : syracuseStep 2193269 = 205619) (by norm_num)
theorem B1644421 : Blo 1461050 1644421 := bbase (se 4 (by rfl) ⟨154164, by rfl⟩ : syracuseStep 1644421 = 308329) (by norm_num)
theorem B1849225 : Blo 1461050 1849225 := bbase (se 2 (by rfl) ⟨693459, by rfl⟩ : syracuseStep 1849225 = 1386919) (by norm_num)
theorem B2193293 : Blo 1461050 2193293 := bbase (se 3 (by rfl) ⟨411242, by rfl⟩ : syracuseStep 2193293 = 822485) (by norm_num)
theorem B3700637 : Blo 1461050 3700637 := bbase (se 3 (by rfl) ⟨693869, by rfl⟩ : syracuseStep 3700637 = 1387739) (by norm_num)
theorem B2193317 : Blo 1461050 2193317 := bbase (se 4 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 2193317 = 411247) (by norm_num)
theorem B1644457 : Blo 1461050 1644457 := bbase (se 2 (by rfl) ⟨616671, by rfl⟩ : syracuseStep 1644457 = 1233343) (by norm_num)
theorem B2193341 : Blo 1461050 2193341 := bbase (se 3 (by rfl) ⟨411251, by rfl⟩ : syracuseStep 2193341 = 822503) (by norm_num)
theorem B1644493 : Blo 1461050 1644493 := bbase (se 3 (by rfl) ⟨308342, by rfl⟩ : syracuseStep 1644493 = 616685) (by norm_num)
theorem B6330325 : Blo 1461050 6330325 := bbase (se 7 (by rfl) ⟨74183, by rfl⟩ : syracuseStep 6330325 = 148367) (by norm_num)
theorem B2193365 : Blo 1461050 2193365 := bbase (se 7 (by rfl) ⟨25703, by rfl⟩ : syracuseStep 2193365 = 51407) (by norm_num)
theorem B1849321 : Blo 1461050 1849321 := bbase (se 2 (by rfl) ⟨693495, by rfl⟩ : syracuseStep 1849321 = 1386991) (by norm_num)
theorem B2193389 : Blo 1461050 2193389 := bbase (se 3 (by rfl) ⟨411260, by rfl⟩ : syracuseStep 2193389 = 822521) (by norm_num)
theorem B1644529 : Blo 1461050 1644529 := bbase (se 2 (by rfl) ⟨616698, by rfl⟩ : syracuseStep 1644529 = 1233397) (by norm_num)
theorem B5625845 : Blo 1461050 5625845 := bbase (se 5 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 5625845 = 527423) (by norm_num)
theorem B2193413 : Blo 1461050 2193413 := bbase (se 4 (by rfl) ⟨205632, by rfl⟩ : syracuseStep 2193413 = 411265) (by norm_num)
theorem B2775053 : Blo 1461050 2775053 := bbase (se 3 (by rfl) ⟨520322, by rfl⟩ : syracuseStep 2775053 = 1040645) (by norm_num)
theorem B1644565 : Blo 1461050 1644565 := bbase (se 6 (by rfl) ⟨38544, by rfl⟩ : syracuseStep 1644565 = 77089) (by norm_num)
theorem B2193437 : Blo 1461050 2193437 := bbase (se 3 (by rfl) ⟨411269, by rfl⟩ : syracuseStep 2193437 = 822539) (by norm_num)
theorem B2193461 : Blo 1461050 2193461 := bbase (se 5 (by rfl) ⟨102818, by rfl⟩ : syracuseStep 2193461 = 205637) (by norm_num)
theorem B1644601 : Blo 1461050 1644601 := bbase (se 2 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 1644601 = 1233451) (by norm_num)
theorem B2193485 : Blo 1461050 2193485 := bbase (se 3 (by rfl) ⟨411278, by rfl⟩ : syracuseStep 2193485 = 822557) (by norm_num)
theorem B1644637 : Blo 1461050 1644637 := bbase (se 3 (by rfl) ⟨308369, by rfl⟩ : syracuseStep 1644637 = 616739) (by norm_num)
theorem B3700829 : Blo 1461050 3700829 := bbase (se 3 (by rfl) ⟨693905, by rfl⟩ : syracuseStep 3700829 = 1387811) (by norm_num)
theorem B2193509 : Blo 1461050 2193509 := bbase (se 4 (by rfl) ⟨205641, by rfl⟩ : syracuseStep 2193509 = 411283) (by norm_num)
theorem B2193533 : Blo 1461050 2193533 := bbase (se 3 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 2193533 = 822575) (by norm_num)
theorem B1644673 : Blo 1461050 1644673 := bbase (se 2 (by rfl) ⟨616752, by rfl⟩ : syracuseStep 1644673 = 1233505) (by norm_num)
theorem B1849493 : Blo 1461050 1849493 := bbase (se 6 (by rfl) ⟨43347, by rfl⟩ : syracuseStep 1849493 = 86695) (by norm_num)
theorem B2193557 : Blo 1461050 2193557 := bbase (se 6 (by rfl) ⟨51411, by rfl⟩ : syracuseStep 2193557 = 102823) (by norm_num)
theorem B2775197 : Blo 1461050 2775197 := bbase (se 3 (by rfl) ⟨520349, by rfl⟩ : syracuseStep 2775197 = 1040699) (by norm_num)
theorem B1644709 : Blo 1461050 1644709 := bbase (se 4 (by rfl) ⟨154191, by rfl⟩ : syracuseStep 1644709 = 308383) (by norm_num)
theorem B2193581 : Blo 1461050 2193581 := bbase (se 3 (by rfl) ⟨411296, by rfl⟩ : syracuseStep 2193581 = 822593) (by norm_num)
theorem B2193605 : Blo 1461050 2193605 := bbase (se 4 (by rfl) ⟨205650, by rfl⟩ : syracuseStep 2193605 = 411301) (by norm_num)
theorem B1644745 : Blo 1461050 1644745 := bbase (se 2 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 1644745 = 1233559) (by norm_num)
theorem B1849549 : Blo 1461050 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B29997269 : Blo 1461050 29997269 := bbase (se 7 (by rfl) ⟨351530, by rfl⟩ : syracuseStep 29997269 = 703061) (by norm_num)
theorem B2193629 : Blo 1461050 2193629 := bbase (se 3 (by rfl) ⟨411305, by rfl⟩ : syracuseStep 2193629 = 822611) (by norm_num)
theorem B1644781 : Blo 1461050 1644781 := bbase (se 3 (by rfl) ⟨308396, by rfl⟩ : syracuseStep 1644781 = 616793) (by norm_num)
theorem B2193653 : Blo 1461050 2193653 := bbase (se 5 (by rfl) ⟨102827, by rfl⟩ : syracuseStep 2193653 = 205655) (by norm_num)
theorem B2193677 : Blo 1461050 2193677 := bbase (se 3 (by rfl) ⟨411314, by rfl⟩ : syracuseStep 2193677 = 822629) (by norm_num)
theorem B1644817 : Blo 1461050 1644817 := bbase (se 2 (by rfl) ⟨616806, by rfl⟩ : syracuseStep 1644817 = 1233613) (by norm_num)
theorem B2193701 : Blo 1461050 2193701 := bbase (se 4 (by rfl) ⟨205659, by rfl⟩ : syracuseStep 2193701 = 411319) (by norm_num)
theorem B1849645 : Blo 1461050 1849645 := bbase (se 3 (by rfl) ⟨346808, by rfl⟩ : syracuseStep 1849645 = 693617) (by norm_num)
theorem B1644853 : Blo 1461050 1644853 := bbase (se 5 (by rfl) ⟨77102, by rfl⟩ : syracuseStep 1644853 = 154205) (by norm_num)
theorem B2193725 : Blo 1461050 2193725 := bbase (se 3 (by rfl) ⟨411323, by rfl⟩ : syracuseStep 2193725 = 822647) (by norm_num)
theorem B2193749 : Blo 1461050 2193749 := bbase (se 10 (by rfl) ⟨3213, by rfl⟩ : syracuseStep 2193749 = 6427) (by norm_num)
theorem B1644889 : Blo 1461050 1644889 := bbase (se 2 (by rfl) ⟨616833, by rfl⟩ : syracuseStep 1644889 = 1233667) (by norm_num)
theorem B2193773 : Blo 1461050 2193773 := bbase (se 3 (by rfl) ⟨411332, by rfl⟩ : syracuseStep 2193773 = 822665) (by norm_num)
theorem B1644925 : Blo 1461050 1644925 := bbase (se 3 (by rfl) ⟨308423, by rfl⟩ : syracuseStep 1644925 = 616847) (by norm_num)
theorem B2193797 : Blo 1461050 2193797 := bbase (se 4 (by rfl) ⟨205668, by rfl⟩ : syracuseStep 2193797 = 411337) (by norm_num)
theorem B10541461 : Blo 1461050 10541461 := bbase (se 6 (by rfl) ⟨247065, by rfl⟩ : syracuseStep 10541461 = 494131) (by norm_num)
theorem B2193821 : Blo 1461050 2193821 := bbase (se 3 (by rfl) ⟨411341, by rfl⟩ : syracuseStep 2193821 = 822683) (by norm_num)
theorem B1644961 : Blo 1461050 1644961 := bbase (se 2 (by rfl) ⟨616860, by rfl⟩ : syracuseStep 1644961 = 1233721) (by norm_num)
theorem B3701173 : Blo 1461050 3701173 := bbase (se 5 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 3701173 = 346985) (by norm_num)
theorem B2775485 : Blo 1461050 2775485 := bbase (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) (by norm_num)
theorem B1644997 : Blo 1461050 1644997 := bbase (se 4 (by rfl) ⟨154218, by rfl⟩ : syracuseStep 1644997 = 308437) (by norm_num)
theorem B1849817 : Blo 1461050 1849817 := bbase (se 2 (by rfl) ⟨693681, by rfl⟩ : syracuseStep 1849817 = 1387363) (by norm_num)
theorem B1645033 : Blo 1461050 1645033 := bbase (se 2 (by rfl) ⟨616887, by rfl⟩ : syracuseStep 1645033 = 1233775) (by norm_num)
theorem B2341381 : Blo 1461050 2341381 := bbase (se 4 (by rfl) ⟨219504, by rfl⟩ : syracuseStep 2341381 = 439009) (by norm_num)
theorem B1645069 : Blo 1461050 1645069 := bbase (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) (by norm_num)
theorem B1849873 : Blo 1461050 1849873 := bbase (se 2 (by rfl) ⟨693702, by rfl⟩ : syracuseStep 1849873 = 1387405) (by norm_num)
theorem B3701285 : Blo 1461050 3701285 := bbase (se 4 (by rfl) ⟨346995, by rfl⟩ : syracuseStep 3701285 = 693991) (by norm_num)
theorem B1645105 : Blo 1461050 1645105 := bbase (se 2 (by rfl) ⟨616914, by rfl⟩ : syracuseStep 1645105 = 1233829) (by norm_num)
theorem B2775637 : Blo 1461050 2775637 := bbase (se 8 (by rfl) ⟨16263, by rfl⟩ : syracuseStep 2775637 = 32527) (by norm_num)
theorem B1645141 : Blo 1461050 1645141 := bbase (se 8 (by rfl) ⟨9639, by rfl⟩ : syracuseStep 1645141 = 19279) (by norm_num)
theorem B1849969 : Blo 1461050 1849969 := bbase (se 2 (by rfl) ⟨693738, by rfl⟩ : syracuseStep 1849969 = 1387477) (by norm_num)
theorem B1645177 : Blo 1461050 1645177 := bbase (se 2 (by rfl) ⟨616941, by rfl⟩ : syracuseStep 1645177 = 1233883) (by norm_num)
theorem B1645213 : Blo 1461050 1645213 := bbase (se 3 (by rfl) ⟨308477, by rfl⟩ : syracuseStep 1645213 = 616955) (by norm_num)
theorem B1874605 : Blo 1461050 1874605 := bbase (se 3 (by rfl) ⟨351488, by rfl⟩ : syracuseStep 1874605 = 702977) (by norm_num)
theorem B8321717 : Blo 1461050 8321717 := bbase (se 5 (by rfl) ⟨390080, by rfl⟩ : syracuseStep 8321717 = 780161) (by norm_num)
theorem B1645249 : Blo 1461050 1645249 := bbase (se 2 (by rfl) ⟨616968, by rfl⟩ : syracuseStep 1645249 = 1233937) (by norm_num)
theorem B3701477 : Blo 1461050 3701477 := bbase (se 4 (by rfl) ⟨347013, by rfl⟩ : syracuseStep 3701477 = 694027) (by norm_num)
theorem B1645285 : Blo 1461050 1645285 := bbase (se 4 (by rfl) ⟨154245, by rfl⟩ : syracuseStep 1645285 = 308491) (by norm_num)
theorem B3750637 : Blo 1461050 3750637 := bbase (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) (by norm_num)
theorem B1481473 : Blo 1461050 1481473 := bbase (se 2 (by rfl) ⟨555552, by rfl⟩ : syracuseStep 1481473 = 1111105) (by norm_num)
theorem B2341637 : Blo 1461050 2341637 := bbase (se 4 (by rfl) ⟨219528, by rfl⟩ : syracuseStep 2341637 = 439057) (by norm_num)
theorem B1645321 : Blo 1461050 1645321 := bbase (se 2 (by rfl) ⟨616995, by rfl⟩ : syracuseStep 1645321 = 1233991) (by norm_num)
theorem B1850141 : Blo 1461050 1850141 := bbase (se 3 (by rfl) ⟨346901, by rfl⟩ : syracuseStep 1850141 = 693803) (by norm_num)
theorem B1481509 : Blo 1461050 1481509 := bbase (se 4 (by rfl) ⟨138891, by rfl⟩ : syracuseStep 1481509 = 277783) (by norm_num)
theorem B2964269 : Blo 1461050 2964269 := bbase (se 3 (by rfl) ⟨555800, by rfl⟩ : syracuseStep 2964269 = 1111601) (by norm_num)
theorem B1645357 : Blo 1461050 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B1850197 : Blo 1461050 1850197 := bbase (se 9 (by rfl) ⟨5420, by rfl⟩ : syracuseStep 1850197 = 10841) (by norm_num)
theorem B4684645 : Blo 1461050 4684645 := bbase (se 4 (by rfl) ⟨439185, by rfl⟩ : syracuseStep 4684645 = 878371) (by norm_num)
theorem B2775941 : Blo 1461050 2775941 := bbase (se 4 (by rfl) ⟨260244, by rfl⟩ : syracuseStep 2775941 = 520489) (by norm_num)
theorem B4684709 : Blo 1461050 4684709 := bbase (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) (by norm_num)
theorem B1850293 : Blo 1461050 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B2341829 : Blo 1461050 2341829 := bbase (se 4 (by rfl) ⟨219546, by rfl⟩ : syracuseStep 2341829 = 439093) (by norm_num)
theorem B3701821 : Blo 1461050 3701821 := bbase (se 3 (by rfl) ⟨694091, by rfl⟩ : syracuseStep 3701821 = 1388183) (by norm_num)
theorem B57736277 : Blo 1461050 57736277 := bbase (se 8 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 57736277 = 676597) (by norm_num)
theorem B1850465 : Blo 1461050 1850465 := bbase (se 2 (by rfl) ⟨693924, by rfl⟩ : syracuseStep 1850465 = 1387849) (by norm_num)
theorem B5266549 : Blo 1461050 5266549 := bbase (se 5 (by rfl) ⟨246869, by rfl⟩ : syracuseStep 5266549 = 493739) (by norm_num)
theorem B3513493 : Blo 1461050 3513493 := bbase (se 6 (by rfl) ⟨82347, by rfl⟩ : syracuseStep 3513493 = 164695) (by norm_num)
theorem B1850521 : Blo 1461050 1850521 := bbase (se 2 (by rfl) ⟨693945, by rfl⟩ : syracuseStep 1850521 = 1387891) (by norm_num)
theorem B3701933 : Blo 1461050 3701933 := bbase (se 3 (by rfl) ⟨694112, by rfl⟩ : syracuseStep 3701933 = 1388225) (by norm_num)
theorem B1850617 : Blo 1461050 1850617 := bbase (se 2 (by rfl) ⟨693981, by rfl⟩ : syracuseStep 1850617 = 1387963) (by norm_num)
theorem B7396757 : Blo 1461050 7396757 := bbase (se 6 (by rfl) ⟨173361, by rfl⟩ : syracuseStep 7396757 = 346723) (by norm_num)
theorem B1850789 : Blo 1461050 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B1850845 : Blo 1461050 1850845 := bbase (se 3 (by rfl) ⟨347033, by rfl⟩ : syracuseStep 1850845 = 694067) (by norm_num)
theorem B1850941 : Blo 1461050 1850941 := bbase (se 3 (by rfl) ⟨347051, by rfl⟩ : syracuseStep 1850941 = 694103) (by norm_num)
theorem B3513917 : Blo 1461050 3513917 := bbase (se 3 (by rfl) ⟨658859, by rfl⟩ : syracuseStep 3513917 = 1317719) (by norm_num)
theorem B2080333 : Blo 1461050 2080333 := bbase (se 3 (by rfl) ⟨390062, by rfl⟩ : syracuseStep 2080333 = 780125) (by norm_num)
theorem B3120781 : Blo 1461050 3120781 := bbase (se 3 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 3120781 = 1170293) (by norm_num)
theorem B2465525 : Blo 1461050 2465525 := bbase (se 5 (by rfl) ⟨115571, by rfl⟩ : syracuseStep 2465525 = 231143) (by norm_num)
theorem B4161269 : Blo 1461050 4161269 := bbase (se 5 (by rfl) ⟨195059, by rfl⟩ : syracuseStep 4161269 = 390119) (by norm_num)
theorem B4931333 : Blo 1461050 4931333 := bbase (se 4 (by rfl) ⟨462312, by rfl⟩ : syracuseStep 4931333 = 924625) (by norm_num)
theorem B2465653 : Blo 1461050 2465653 := bbase (se 5 (by rfl) ⟨115577, by rfl⟩ : syracuseStep 2465653 = 231155) (by norm_num)
theorem B2080669 : Blo 1461050 2080669 := bbase (se 3 (by rfl) ⟨390125, by rfl⟩ : syracuseStep 2080669 = 780251) (by norm_num)
theorem B2465741 : Blo 1461050 2465741 := bbase (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) (by norm_num)
theorem B2465795 : Blo 1461050 2465795 := bstep (se 1 (by rfl) ⟨1849346, by rfl⟩ : syracuseStep 2465795 = 3698693) B3698693
theorem B6242417 : Blo 1461050 6242417 := bstep (se 2 (by rfl) ⟨2340906, by rfl⟩ : syracuseStep 6242417 = 4681813) B4681813
theorem B2465923 : Blo 1461050 2465923 := bstep (se 1 (by rfl) ⟨1849442, by rfl⟩ : syracuseStep 2465923 = 3698885) B3698885
theorem B2670737 : Blo 1461050 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B12656837 : Blo 1461050 12656837 := bstep (se 4 (by rfl) ⟨1186578, by rfl⟩ : syracuseStep 12656837 = 2373157) B2373157
theorem B2466065 : Blo 1461050 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B2081153 : Blo 1461050 2081153 := bstep (se 2 (by rfl) ⟨780432, by rfl⟩ : syracuseStep 2081153 = 1560865) B1560865
theorem B4931981 : Blo 1461050 4931981 := bstep (se 3 (by rfl) ⟨924746, by rfl⟩ : syracuseStep 4931981 = 1849493) B1849493
theorem B16654733 : Blo 1461050 16654733 := bstep (se 3 (by rfl) ⟨3122762, by rfl⟩ : syracuseStep 16654733 = 6245525) B6245525
theorem B2466193 : Blo 1461050 2466193 := bstep (se 2 (by rfl) ⟨924822, by rfl⟩ : syracuseStep 2466193 = 1849645) B1849645
theorem B2466227 : Blo 1461050 2466227 := bstep (se 1 (by rfl) ⟨1849670, by rfl⟩ : syracuseStep 2466227 = 3699341) B3699341
theorem B4932035 : Blo 1461050 4932035 := bstep (se 1 (by rfl) ⟨3699026, by rfl⟩ : syracuseStep 4932035 = 7398053) B7398053
theorem B2466355 : Blo 1461050 2466355 := bstep (se 1 (by rfl) ⟨1849766, by rfl⟩ : syracuseStep 2466355 = 3699533) B3699533
theorem B2499187 : Blo 1461050 2499187 := bstep (se 1 (by rfl) ⟨1874390, by rfl⟩ : syracuseStep 2499187 = 3748781) B3748781
theorem B4219523 : Blo 1461050 4219523 := bstep (se 1 (by rfl) ⟨3164642, by rfl⟩ : syracuseStep 4219523 = 6329285) B6329285
theorem B1581715 : Blo 1461050 1581715 := bstep (se 1 (by rfl) ⟨1186286, by rfl⟩ : syracuseStep 1581715 = 2372573) B2372573
theorem B6668963 : Blo 1461050 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B3121841 : Blo 1461050 3121841 := bstep (se 2 (by rfl) ⟨1170690, by rfl⟩ : syracuseStep 3121841 = 2341381) B2341381
theorem B2466497 : Blo 1461050 2466497 := bstep (se 2 (by rfl) ⟨924936, by rfl⟩ : syracuseStep 2466497 = 1849873) B1849873
theorem B4932305 : Blo 1461050 4932305 := bstep (se 2 (by rfl) ⟨1849614, by rfl⟩ : syracuseStep 4932305 = 3699229) B3699229
theorem B26665699 : Blo 1461050 26665699 := bstep (se 1 (by rfl) ⟨19999274, by rfl⟩ : syracuseStep 26665699 = 39998549) B39998549
theorem B2466625 : Blo 1461050 2466625 := bstep (se 2 (by rfl) ⟨924984, by rfl⟩ : syracuseStep 2466625 = 1849969) B1849969
theorem B2466659 : Blo 1461050 2466659 := bstep (se 1 (by rfl) ⟨1849994, by rfl⟩ : syracuseStep 2466659 = 3699989) B3699989
theorem B2499473 : Blo 1461050 2499473 := bstep (se 2 (by rfl) ⟨937302, by rfl⟩ : syracuseStep 2499473 = 1874605) B1874605
theorem B4162499 : Blo 1461050 4162499 := bstep (se 1 (by rfl) ⟨3121874, by rfl⟩ : syracuseStep 4162499 = 6243749) B6243749
theorem B2466787 : Blo 1461050 2466787 := bstep (se 1 (by rfl) ⟨1850090, by rfl⟩ : syracuseStep 2466787 = 3700181) B3700181
theorem B1975297 : Blo 1461050 1975297 := bstep (se 2 (by rfl) ⟨740736, by rfl⟩ : syracuseStep 1975297 = 1481473) B1481473
theorem B7021603 : Blo 1461050 7021603 := bstep (se 1 (by rfl) ⟨5266202, by rfl⟩ : syracuseStep 7021603 = 10532405) B10532405
theorem B2466929 : Blo 1461050 2466929 := bstep (se 2 (by rfl) ⟨925098, by rfl⟩ : syracuseStep 2466929 = 1850197) B1850197
theorem B1975475 : Blo 1461050 1975475 := bstep (se 1 (by rfl) ⟨1481606, by rfl⟩ : syracuseStep 1975475 = 2963213) B2963213
theorem B2082019 : Blo 1461050 2082019 := bstep (se 1 (by rfl) ⟨1561514, by rfl⟩ : syracuseStep 2082019 = 3123029) B3123029
theorem B4932845 : Blo 1461050 4932845 := bstep (se 3 (by rfl) ⟨924908, by rfl⟩ : syracuseStep 4932845 = 1849817) B1849817
theorem B2467057 : Blo 1461050 2467057 := bstep (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) B1850293
theorem B2467091 : Blo 1461050 2467091 := bstep (se 1 (by rfl) ⟨1850318, by rfl⟩ : syracuseStep 2467091 = 3700637) B3700637
theorem B4932899 : Blo 1461050 4932899 := bstep (se 1 (by rfl) ⟨3699674, by rfl⟩ : syracuseStep 4932899 = 7399349) B7399349
theorem B2082115 : Blo 1461050 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B2467219 : Blo 1461050 2467219 := bstep (se 1 (by rfl) ⟨1850414, by rfl⟩ : syracuseStep 2467219 = 3700829) B3700829
theorem B19998179 : Blo 1461050 19998179 := bstep (se 1 (by rfl) ⟨14998634, by rfl⟩ : syracuseStep 19998179 = 29997269) B29997269
theorem B7022065 : Blo 1461050 7022065 := bstep (se 2 (by rfl) ⟨2633274, by rfl⟩ : syracuseStep 7022065 = 5266549) B5266549
theorem B2467361 : Blo 1461050 2467361 := bstep (se 2 (by rfl) ⟨925260, by rfl⟩ : syracuseStep 2467361 = 1850521) B1850521
theorem B3950129 : Blo 1461050 3950129 := bstep (se 2 (by rfl) ⟨1481298, by rfl⟩ : syracuseStep 3950129 = 2962597) B2962597
theorem B4933169 : Blo 1461050 4933169 := bstep (se 2 (by rfl) ⟨1849938, by rfl⟩ : syracuseStep 4933169 = 3699877) B3699877
theorem B7399025 : Blo 1461050 7399025 := bstep (se 2 (by rfl) ⟨2774634, by rfl⟩ : syracuseStep 7399025 = 5549269) B5549269
theorem B2467489 : Blo 1461050 2467489 := bstep (se 2 (by rfl) ⟨925308, by rfl⟩ : syracuseStep 2467489 = 1850617) B1850617
theorem B2467523 : Blo 1461050 2467523 := bstep (se 1 (by rfl) ⟨1850642, by rfl⟩ : syracuseStep 2467523 = 3701285) B3701285
theorem B4163309 : Blo 1461050 4163309 := bstep (se 3 (by rfl) ⟨780620, by rfl⟩ : syracuseStep 4163309 = 1561241) B1561241
theorem B6326029 : Blo 1461050 6326029 := bstep (se 3 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 6326029 = 2372261) B2372261
theorem B5547811 : Blo 1461050 5547811 := bstep (se 1 (by rfl) ⟨4160858, by rfl⟩ : syracuseStep 5547811 = 8321717) B8321717
theorem B2467651 : Blo 1461050 2467651 := bstep (se 1 (by rfl) ⟨1850738, by rfl⟩ : syracuseStep 2467651 = 3701477) B3701477
theorem B1976179 : Blo 1461050 1976179 := bstep (se 1 (by rfl) ⟨1482134, by rfl⟩ : syracuseStep 1976179 = 2964269) B2964269
theorem B4163501 : Blo 1461050 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B3123139 : Blo 1461050 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B2467793 : Blo 1461050 2467793 := bstep (se 2 (by rfl) ⟨925422, by rfl⟩ : syracuseStep 2467793 = 1850845) B1850845
theorem B4933709 : Blo 1461050 4933709 := bstep (se 3 (by rfl) ⟨925070, by rfl⟩ : syracuseStep 4933709 = 1850141) B1850141
theorem B2467921 : Blo 1461050 2467921 := bstep (se 2 (by rfl) ⟨925470, by rfl⟩ : syracuseStep 2467921 = 1850941) B1850941
theorem B2467955 : Blo 1461050 2467955 := bstep (se 1 (by rfl) ⟨1850966, by rfl⟩ : syracuseStep 2467955 = 3701933) B3701933
theorem B4933763 : Blo 1461050 4933763 := bstep (se 1 (by rfl) ⟨3700322, by rfl⟩ : syracuseStep 4933763 = 7400645) B7400645
theorem B4934033 : Blo 1461050 4934033 := bstep (se 2 (by rfl) ⟨1850262, by rfl⟩ : syracuseStep 4934033 = 3700525) B3700525
theorem B3287537 : Blo 1461050 3287537 := bstep (se 2 (by rfl) ⟨1232826, by rfl⟩ : syracuseStep 3287537 = 2465653) B2465653
theorem B3287555 : Blo 1461050 3287555 := bstep (se 1 (by rfl) ⟨2465666, by rfl⟩ : syracuseStep 3287555 = 4931333) B4931333
theorem B6244877 : Blo 1461050 6244877 := bstep (se 3 (by rfl) ⟨1170914, by rfl⟩ : syracuseStep 6244877 = 2341829) B2341829
theorem B4999715 : Blo 1461050 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B8440433 : Blo 1461050 8440433 := bstep (se 2 (by rfl) ⟨3165162, by rfl⟩ : syracuseStep 8440433 = 6330325) B6330325
theorem B8325773 : Blo 1461050 8325773 := bstep (se 3 (by rfl) ⟨1561082, by rfl⟩ : syracuseStep 8325773 = 3122165) B3122165
theorem B16648901 : Blo 1461050 16648901 := bstep (se 4 (by rfl) ⟨1560834, by rfl⟩ : syracuseStep 16648901 = 3121669) B3121669
theorem B3287825 : Blo 1461050 3287825 := bstep (se 2 (by rfl) ⟨1232934, by rfl⟩ : syracuseStep 3287825 = 2465869) B2465869
theorem B3287843 : Blo 1461050 3287843 := bstep (se 1 (by rfl) ⟨2465882, by rfl⟩ : syracuseStep 3287843 = 4931765) B4931765
theorem B1461059 : Blo 1461050 1461059 := bstep (se 1 (by rfl) ⟨1095794, by rfl⟩ : syracuseStep 1461059 = 2191589) B2191589
theorem B1461075 : Blo 1461050 1461075 := bstep (se 1 (by rfl) ⟨1095806, by rfl⟩ : syracuseStep 1461075 = 2191613) B2191613
theorem B1461091 : Blo 1461050 1461091 := bstep (se 1 (by rfl) ⟨1095818, by rfl⟩ : syracuseStep 1461091 = 2191637) B2191637
theorem B1461107 : Blo 1461050 1461107 := bstep (se 1 (by rfl) ⟨1095830, by rfl⟩ : syracuseStep 1461107 = 2191661) B2191661
theorem B1461123 : Blo 1461050 1461123 := bstep (se 1 (by rfl) ⟨1095842, by rfl⟩ : syracuseStep 1461123 = 2191685) B2191685
theorem B4164493 : Blo 1461050 4164493 := bstep (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) B1561685
theorem B1461139 : Blo 1461050 1461139 := bstep (se 1 (by rfl) ⟨1095854, by rfl⟩ : syracuseStep 1461139 = 2191709) B2191709
theorem B1461155 : Blo 1461050 1461155 := bstep (se 1 (by rfl) ⟨1095866, by rfl⟩ : syracuseStep 1461155 = 2191733) B2191733
theorem B4934573 : Blo 1461050 4934573 := bstep (se 3 (by rfl) ⟨925232, by rfl⟩ : syracuseStep 4934573 = 1850465) B1850465
theorem B1461171 : Blo 1461050 1461171 := bstep (se 1 (by rfl) ⟨1095878, by rfl⟩ : syracuseStep 1461171 = 2191757) B2191757
theorem B1461187 : Blo 1461050 1461187 := bstep (se 1 (by rfl) ⟨1095890, by rfl⟩ : syracuseStep 1461187 = 2191781) B2191781
theorem B1461203 : Blo 1461050 1461203 := bstep (se 1 (by rfl) ⟨1095902, by rfl⟩ : syracuseStep 1461203 = 2191805) B2191805
theorem B1461219 : Blo 1461050 1461219 := bstep (se 1 (by rfl) ⟨1095914, by rfl⟩ : syracuseStep 1461219 = 2191829) B2191829
theorem B4934627 : Blo 1461050 4934627 := bstep (se 1 (by rfl) ⟨3700970, by rfl⟩ : syracuseStep 4934627 = 7401941) B7401941
theorem B1461235 : Blo 1461050 1461235 := bstep (se 1 (by rfl) ⟨1095926, by rfl⟩ : syracuseStep 1461235 = 2191853) B2191853
theorem B1461251 : Blo 1461050 1461251 := bstep (se 1 (by rfl) ⟨1095938, by rfl⟩ : syracuseStep 1461251 = 2191877) B2191877
theorem B1461267 : Blo 1461050 1461267 := bstep (se 1 (by rfl) ⟨1095950, by rfl⟩ : syracuseStep 1461267 = 2191901) B2191901
theorem B1461283 : Blo 1461050 1461283 := bstep (se 1 (by rfl) ⟨1095962, by rfl⟩ : syracuseStep 1461283 = 2191925) B2191925
theorem B7400483 : Blo 1461050 7400483 := bstep (se 1 (by rfl) ⟨5550362, by rfl⟩ : syracuseStep 7400483 = 11100725) B11100725
theorem B3288113 : Blo 1461050 3288113 := bstep (se 2 (by rfl) ⟨1233042, by rfl⟩ : syracuseStep 3288113 = 2466085) B2466085
theorem B1461299 : Blo 1461050 1461299 := bstep (se 1 (by rfl) ⟨1095974, by rfl⟩ : syracuseStep 1461299 = 2191949) B2191949
theorem B1461315 : Blo 1461050 1461315 := bstep (se 1 (by rfl) ⟨1095986, by rfl⟩ : syracuseStep 1461315 = 2191973) B2191973
theorem B3288131 : Blo 1461050 3288131 := bstep (se 1 (by rfl) ⟨2466098, by rfl⟩ : syracuseStep 3288131 = 4932197) B4932197
theorem B1461331 : Blo 1461050 1461331 := bstep (se 1 (by rfl) ⟨1095998, by rfl⟩ : syracuseStep 1461331 = 2191997) B2191997
theorem B1461347 : Blo 1461050 1461347 := bstep (se 1 (by rfl) ⟨1096010, by rfl⟩ : syracuseStep 1461347 = 2192021) B2192021
theorem B1461363 : Blo 1461050 1461363 := bstep (se 1 (by rfl) ⟨1096022, by rfl⟩ : syracuseStep 1461363 = 2192045) B2192045
theorem B1461379 : Blo 1461050 1461379 := bstep (se 1 (by rfl) ⟨1096034, by rfl⟩ : syracuseStep 1461379 = 2192069) B2192069
theorem B2641027 : Blo 1461050 2641027 := bstep (se 1 (by rfl) ⟨1980770, by rfl⟩ : syracuseStep 2641027 = 3961541) B3961541
theorem B1461395 : Blo 1461050 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B1461411 : Blo 1461050 1461411 := bstep (se 1 (by rfl) ⟨1096058, by rfl⟩ : syracuseStep 1461411 = 2192117) B2192117
theorem B1461427 : Blo 1461050 1461427 := bstep (se 1 (by rfl) ⟨1096070, by rfl⟩ : syracuseStep 1461427 = 2192141) B2192141
theorem B1461443 : Blo 1461050 1461443 := bstep (se 1 (by rfl) ⟨1096082, by rfl⟩ : syracuseStep 1461443 = 2192165) B2192165
theorem B1461459 : Blo 1461050 1461459 := bstep (se 1 (by rfl) ⟨1096094, by rfl⟩ : syracuseStep 1461459 = 2192189) B2192189
theorem B1461475 : Blo 1461050 1461475 := bstep (se 1 (by rfl) ⟨1096106, by rfl⟩ : syracuseStep 1461475 = 2192213) B2192213
theorem B4934897 : Blo 1461050 4934897 := bstep (se 2 (by rfl) ⟨1850586, by rfl⟩ : syracuseStep 4934897 = 3701173) B3701173
theorem B1461491 : Blo 1461050 1461491 := bstep (se 1 (by rfl) ⟨1096118, by rfl⟩ : syracuseStep 1461491 = 2192237) B2192237
theorem B16657649 : Blo 1461050 16657649 := bstep (se 2 (by rfl) ⟨6246618, by rfl⟩ : syracuseStep 16657649 = 12493237) B12493237
theorem B1461507 : Blo 1461050 1461507 := bstep (se 1 (by rfl) ⟨1096130, by rfl⟩ : syracuseStep 1461507 = 2192261) B2192261
theorem B1461523 : Blo 1461050 1461523 := bstep (se 1 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 1461523 = 2192285) B2192285
theorem B1461539 : Blo 1461050 1461539 := bstep (se 1 (by rfl) ⟨1096154, by rfl⟩ : syracuseStep 1461539 = 2192309) B2192309
theorem B1461555 : Blo 1461050 1461555 := bstep (se 1 (by rfl) ⟨1096166, by rfl⟩ : syracuseStep 1461555 = 2192333) B2192333
theorem B1461571 : Blo 1461050 1461571 := bstep (se 1 (by rfl) ⟨1096178, by rfl⟩ : syracuseStep 1461571 = 2192357) B2192357
theorem B9366853 : Blo 1461050 9366853 := bstep (se 4 (by rfl) ⟨878142, by rfl⟩ : syracuseStep 9366853 = 1756285) B1756285
theorem B3288401 : Blo 1461050 3288401 := bstep (se 2 (by rfl) ⟨1233150, by rfl⟩ : syracuseStep 3288401 = 2466301) B2466301
theorem B1461587 : Blo 1461050 1461587 := bstep (se 1 (by rfl) ⟨1096190, by rfl⟩ : syracuseStep 1461587 = 2192381) B2192381
theorem B3288419 : Blo 1461050 3288419 := bstep (se 1 (by rfl) ⟨2466314, by rfl⟩ : syracuseStep 3288419 = 4932629) B4932629
theorem B1461603 : Blo 1461050 1461603 := bstep (se 1 (by rfl) ⟨1096202, by rfl⟩ : syracuseStep 1461603 = 2192405) B2192405
theorem B1461619 : Blo 1461050 1461619 := bstep (se 1 (by rfl) ⟨1096214, by rfl⟩ : syracuseStep 1461619 = 2192429) B2192429
theorem B1461635 : Blo 1461050 1461635 := bstep (se 1 (by rfl) ⟨1096226, by rfl⟩ : syracuseStep 1461635 = 2192453) B2192453
theorem B1461651 : Blo 1461050 1461651 := bstep (se 1 (by rfl) ⟨1096238, by rfl⟩ : syracuseStep 1461651 = 2192477) B2192477
theorem B1461667 : Blo 1461050 1461667 := bstep (se 1 (by rfl) ⟨1096250, by rfl⟩ : syracuseStep 1461667 = 2192501) B2192501
theorem B1461683 : Blo 1461050 1461683 := bstep (se 1 (by rfl) ⟨1096262, by rfl⟩ : syracuseStep 1461683 = 2192525) B2192525
theorem B1461699 : Blo 1461050 1461699 := bstep (se 1 (by rfl) ⟨1096274, by rfl⟩ : syracuseStep 1461699 = 2192549) B2192549
theorem B5270989 : Blo 1461050 5270989 := bstep (se 3 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 5270989 = 1976621) B1976621
theorem B1461715 : Blo 1461050 1461715 := bstep (se 1 (by rfl) ⟨1096286, by rfl⟩ : syracuseStep 1461715 = 2192573) B2192573
theorem B1461731 : Blo 1461050 1461731 := bstep (se 1 (by rfl) ⟨1096298, by rfl⟩ : syracuseStep 1461731 = 2192597) B2192597
theorem B1461747 : Blo 1461050 1461747 := bstep (se 1 (by rfl) ⟨1096310, by rfl⟩ : syracuseStep 1461747 = 2192621) B2192621
theorem B4746755 : Blo 1461050 4746755 := bstep (se 1 (by rfl) ⟨3560066, by rfl⟩ : syracuseStep 4746755 = 7120133) B7120133
theorem B1461763 : Blo 1461050 1461763 := bstep (se 1 (by rfl) ⟨1096322, by rfl⟩ : syracuseStep 1461763 = 2192645) B2192645
theorem B1461779 : Blo 1461050 1461779 := bstep (se 1 (by rfl) ⟨1096334, by rfl⟩ : syracuseStep 1461779 = 2192669) B2192669
theorem B1461795 : Blo 1461050 1461795 := bstep (se 1 (by rfl) ⟨1096346, by rfl⟩ : syracuseStep 1461795 = 2192693) B2192693
theorem B1461811 : Blo 1461050 1461811 := bstep (se 1 (by rfl) ⟨1096358, by rfl⟩ : syracuseStep 1461811 = 2192717) B2192717
theorem B1461827 : Blo 1461050 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B1461843 : Blo 1461050 1461843 := bstep (se 1 (by rfl) ⟨1096382, by rfl⟩ : syracuseStep 1461843 = 2192765) B2192765
theorem B1461859 : Blo 1461050 1461859 := bstep (se 1 (by rfl) ⟨1096394, by rfl⟩ : syracuseStep 1461859 = 2192789) B2192789
theorem B3288689 : Blo 1461050 3288689 := bstep (se 2 (by rfl) ⟨1233258, by rfl⟩ : syracuseStep 3288689 = 2466517) B2466517
theorem B1461875 : Blo 1461050 1461875 := bstep (se 1 (by rfl) ⟨1096406, by rfl⟩ : syracuseStep 1461875 = 2192813) B2192813
theorem B3288707 : Blo 1461050 3288707 := bstep (se 1 (by rfl) ⟨2466530, by rfl⟩ : syracuseStep 3288707 = 4933061) B4933061
theorem B1461891 : Blo 1461050 1461891 := bstep (se 1 (by rfl) ⟨1096418, by rfl⟩ : syracuseStep 1461891 = 2192837) B2192837
theorem B5000849 : Blo 1461050 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B1461907 : Blo 1461050 1461907 := bstep (se 1 (by rfl) ⟨1096430, by rfl⟩ : syracuseStep 1461907 = 2192861) B2192861
theorem B1756819 : Blo 1461050 1756819 := bstep (se 1 (by rfl) ⟨1317614, by rfl⟩ : syracuseStep 1756819 = 2635229) B2635229
theorem B1461923 : Blo 1461050 1461923 := bstep (se 1 (by rfl) ⟨1096442, by rfl⟩ : syracuseStep 1461923 = 2192885) B2192885
theorem B1461939 : Blo 1461050 1461939 := bstep (se 1 (by rfl) ⟨1096454, by rfl⟩ : syracuseStep 1461939 = 2192909) B2192909
theorem B1461955 : Blo 1461050 1461955 := bstep (se 1 (by rfl) ⟨1096466, by rfl⟩ : syracuseStep 1461955 = 2192933) B2192933
theorem B2109137 : Blo 1461050 2109137 := bstep (se 2 (by rfl) ⟨790926, by rfl⟩ : syracuseStep 2109137 = 1581853) B1581853
theorem B1461971 : Blo 1461050 1461971 := bstep (se 1 (by rfl) ⟨1096478, by rfl⟩ : syracuseStep 1461971 = 2192957) B2192957
theorem B1461987 : Blo 1461050 1461987 := bstep (se 1 (by rfl) ⟨1096490, by rfl⟩ : syracuseStep 1461987 = 2192981) B2192981
theorem B1462003 : Blo 1461050 1462003 := bstep (se 1 (by rfl) ⟨1096502, by rfl⟩ : syracuseStep 1462003 = 2193005) B2193005
theorem B1462019 : Blo 1461050 1462019 := bstep (se 1 (by rfl) ⟨1096514, by rfl⟩ : syracuseStep 1462019 = 2193029) B2193029
theorem B4935437 : Blo 1461050 4935437 := bstep (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) B1850789
theorem B1462035 : Blo 1461050 1462035 := bstep (se 1 (by rfl) ⟨1096526, by rfl⟩ : syracuseStep 1462035 = 2193053) B2193053
theorem B1462051 : Blo 1461050 1462051 := bstep (se 1 (by rfl) ⟨1096538, by rfl⟩ : syracuseStep 1462051 = 2193077) B2193077
theorem B6246193 : Blo 1461050 6246193 := bstep (se 2 (by rfl) ⟨2342322, by rfl⟩ : syracuseStep 6246193 = 4684645) B4684645
theorem B1462067 : Blo 1461050 1462067 := bstep (se 1 (by rfl) ⟨1096550, by rfl⟩ : syracuseStep 1462067 = 2193101) B2193101
theorem B1462083 : Blo 1461050 1462083 := bstep (se 1 (by rfl) ⟨1096562, by rfl⟩ : syracuseStep 1462083 = 2193125) B2193125
theorem B4935491 : Blo 1461050 4935491 := bstep (se 1 (by rfl) ⟨3701618, by rfl⟩ : syracuseStep 4935491 = 7403237) B7403237
theorem B7401293 : Blo 1461050 7401293 := bstep (se 3 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 7401293 = 2775485) B2775485
theorem B1462099 : Blo 1461050 1462099 := bstep (se 1 (by rfl) ⟨1096574, by rfl⟩ : syracuseStep 1462099 = 2193149) B2193149
theorem B3698531 : Blo 1461050 3698531 := bstep (se 1 (by rfl) ⟨2773898, by rfl⟩ : syracuseStep 3698531 = 5547797) B5547797
theorem B1462115 : Blo 1461050 1462115 := bstep (se 1 (by rfl) ⟨1096586, by rfl⟩ : syracuseStep 1462115 = 2193173) B2193173
theorem B1462131 : Blo 1461050 1462131 := bstep (se 1 (by rfl) ⟨1096598, by rfl⟩ : syracuseStep 1462131 = 2193197) B2193197
theorem B1462147 : Blo 1461050 1462147 := bstep (se 1 (by rfl) ⟨1096610, by rfl⟩ : syracuseStep 1462147 = 2193221) B2193221
theorem B3288977 : Blo 1461050 3288977 := bstep (se 2 (by rfl) ⟨1233366, by rfl⟩ : syracuseStep 3288977 = 2466733) B2466733
theorem B1462163 : Blo 1461050 1462163 := bstep (se 1 (by rfl) ⟨1096622, by rfl⟩ : syracuseStep 1462163 = 2193245) B2193245
theorem B3288995 : Blo 1461050 3288995 := bstep (se 1 (by rfl) ⟨2466746, by rfl⟩ : syracuseStep 3288995 = 4933493) B4933493
theorem B1462179 : Blo 1461050 1462179 := bstep (se 1 (by rfl) ⟨1096634, by rfl⟩ : syracuseStep 1462179 = 2193269) B2193269
theorem B1462195 : Blo 1461050 1462195 := bstep (se 1 (by rfl) ⟨1096646, by rfl⟩ : syracuseStep 1462195 = 2193293) B2193293
theorem B1462211 : Blo 1461050 1462211 := bstep (se 1 (by rfl) ⟨1096658, by rfl⟩ : syracuseStep 1462211 = 2193317) B2193317
theorem B5550029 : Blo 1461050 5550029 := bstep (se 3 (by rfl) ⟨1040630, by rfl⟩ : syracuseStep 5550029 = 2081261) B2081261
theorem B1462227 : Blo 1461050 1462227 := bstep (se 1 (by rfl) ⟨1096670, by rfl⟩ : syracuseStep 1462227 = 2193341) B2193341
theorem B1462243 : Blo 1461050 1462243 := bstep (se 1 (by rfl) ⟨1096682, by rfl⟩ : syracuseStep 1462243 = 2193365) B2193365
theorem B1462259 : Blo 1461050 1462259 := bstep (se 1 (by rfl) ⟨1096694, by rfl⟩ : syracuseStep 1462259 = 2193389) B2193389
theorem B1462275 : Blo 1461050 1462275 := bstep (se 1 (by rfl) ⟨1096706, by rfl⟩ : syracuseStep 1462275 = 2193413) B2193413
theorem B1462291 : Blo 1461050 1462291 := bstep (se 1 (by rfl) ⟨1096718, by rfl⟩ : syracuseStep 1462291 = 2193437) B2193437
theorem B3698723 : Blo 1461050 3698723 := bstep (se 1 (by rfl) ⟨2774042, by rfl⟩ : syracuseStep 3698723 = 5548085) B5548085
theorem B1462307 : Blo 1461050 1462307 := bstep (se 1 (by rfl) ⟨1096730, by rfl⟩ : syracuseStep 1462307 = 2193461) B2193461
theorem B1462323 : Blo 1461050 1462323 := bstep (se 1 (by rfl) ⟨1096742, by rfl⟩ : syracuseStep 1462323 = 2193485) B2193485
theorem B1462339 : Blo 1461050 1462339 := bstep (se 1 (by rfl) ⟨1096754, by rfl⟩ : syracuseStep 1462339 = 2193509) B2193509
theorem B2633809 : Blo 1461050 2633809 := bstep (se 2 (by rfl) ⟨987678, by rfl⟩ : syracuseStep 2633809 = 1975357) B1975357
theorem B1462355 : Blo 1461050 1462355 := bstep (se 1 (by rfl) ⟨1096766, by rfl⟩ : syracuseStep 1462355 = 2193533) B2193533
theorem B4935761 : Blo 1461050 4935761 := bstep (se 2 (by rfl) ⟨1850910, by rfl⟩ : syracuseStep 4935761 = 3701821) B3701821
theorem B1462371 : Blo 1461050 1462371 := bstep (se 1 (by rfl) ⟨1096778, by rfl⟩ : syracuseStep 1462371 = 2193557) B2193557
theorem B28471409 : Blo 1461050 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B7901297 : Blo 1461050 7901297 := bstep (se 2 (by rfl) ⟨2962986, by rfl⟩ : syracuseStep 7901297 = 5925973) B5925973
theorem B1462387 : Blo 1461050 1462387 := bstep (se 1 (by rfl) ⟨1096790, by rfl⟩ : syracuseStep 1462387 = 2193581) B2193581
theorem B1462403 : Blo 1461050 1462403 := bstep (se 1 (by rfl) ⟨1096802, by rfl⟩ : syracuseStep 1462403 = 2193605) B2193605
theorem B4812941 : Blo 1461050 4812941 := bstep (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) B1804853
theorem B1462419 : Blo 1461050 1462419 := bstep (se 1 (by rfl) ⟨1096814, by rfl⟩ : syracuseStep 1462419 = 2193629) B2193629
theorem B1462435 : Blo 1461050 1462435 := bstep (se 1 (by rfl) ⟨1096826, by rfl⟩ : syracuseStep 1462435 = 2193653) B2193653
theorem B3289265 : Blo 1461050 3289265 := bstep (se 2 (by rfl) ⟨1233474, by rfl⟩ : syracuseStep 3289265 = 2466949) B2466949
theorem B1462451 : Blo 1461050 1462451 := bstep (se 1 (by rfl) ⟨1096838, by rfl⟩ : syracuseStep 1462451 = 2193677) B2193677
theorem B3289283 : Blo 1461050 3289283 := bstep (se 1 (by rfl) ⟨2466962, by rfl⟩ : syracuseStep 3289283 = 4933925) B4933925
theorem B1462467 : Blo 1461050 1462467 := bstep (se 1 (by rfl) ⟨1096850, by rfl⟩ : syracuseStep 1462467 = 2193701) B2193701
theorem B7901381 : Blo 1461050 7901381 := bstep (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) B1481509
theorem B1462483 : Blo 1461050 1462483 := bstep (se 1 (by rfl) ⟨1096862, by rfl⟩ : syracuseStep 1462483 = 2193725) B2193725
theorem B1462499 : Blo 1461050 1462499 := bstep (se 1 (by rfl) ⟨1096874, by rfl⟩ : syracuseStep 1462499 = 2193749) B2193749
theorem B2191601 : Blo 1461050 2191601 := bstep (se 2 (by rfl) ⟨821850, by rfl⟩ : syracuseStep 2191601 = 1643701) B1643701
theorem B1462515 : Blo 1461050 1462515 := bstep (se 1 (by rfl) ⟨1096886, by rfl⟩ : syracuseStep 1462515 = 2193773) B2193773
theorem B2191619 : Blo 1461050 2191619 := bstep (se 1 (by rfl) ⟨1643714, by rfl⟩ : syracuseStep 2191619 = 3287429) B3287429
theorem B1462531 : Blo 1461050 1462531 := bstep (se 1 (by rfl) ⟨1096898, by rfl⟩ : syracuseStep 1462531 = 2193797) B2193797
theorem B1462547 : Blo 1461050 1462547 := bstep (se 1 (by rfl) ⟨1096910, by rfl⟩ : syracuseStep 1462547 = 2193821) B2193821
theorem B2191649 : Blo 1461050 2191649 := bstep (se 2 (by rfl) ⟨821868, by rfl⟩ : syracuseStep 2191649 = 1643737) B1643737
theorem B2191667 : Blo 1461050 2191667 := bstep (se 1 (by rfl) ⟨1643750, by rfl⟩ : syracuseStep 2191667 = 3287501) B3287501
theorem B2191697 : Blo 1461050 2191697 := bstep (se 2 (by rfl) ⟨821886, by rfl⟩ : syracuseStep 2191697 = 1643773) B1643773
theorem B2191715 : Blo 1461050 2191715 := bstep (se 1 (by rfl) ⟨1643786, by rfl⟩ : syracuseStep 2191715 = 3287573) B3287573
theorem B4682083 : Blo 1461050 4682083 := bstep (se 1 (by rfl) ⟨3511562, by rfl⟩ : syracuseStep 4682083 = 7023125) B7023125
theorem B2191745 : Blo 1461050 2191745 := bstep (se 2 (by rfl) ⟨821904, by rfl⟩ : syracuseStep 2191745 = 1643809) B1643809
theorem B2191763 : Blo 1461050 2191763 := bstep (se 1 (by rfl) ⟨1643822, by rfl⟩ : syracuseStep 2191763 = 3287645) B3287645
theorem B2191793 : Blo 1461050 2191793 := bstep (se 2 (by rfl) ⟨821922, by rfl⟩ : syracuseStep 2191793 = 1643845) B1643845
theorem B2191811 : Blo 1461050 2191811 := bstep (se 1 (by rfl) ⟨1643858, by rfl⟩ : syracuseStep 2191811 = 3287717) B3287717
theorem B3289553 : Blo 1461050 3289553 := bstep (se 2 (by rfl) ⟨1233582, by rfl⟩ : syracuseStep 3289553 = 2467165) B2467165
theorem B2191841 : Blo 1461050 2191841 := bstep (se 2 (by rfl) ⟨821940, by rfl⟩ : syracuseStep 2191841 = 1643881) B1643881
theorem B7025123 : Blo 1461050 7025123 := bstep (se 1 (by rfl) ⟨5268842, by rfl⟩ : syracuseStep 7025123 = 10537685) B10537685
theorem B3289571 : Blo 1461050 3289571 := bstep (se 1 (by rfl) ⟨2467178, by rfl⟩ : syracuseStep 3289571 = 4934357) B4934357
theorem B2191859 : Blo 1461050 2191859 := bstep (se 1 (by rfl) ⟨1643894, by rfl⟩ : syracuseStep 2191859 = 3287789) B3287789
theorem B1561091 : Blo 1461050 1561091 := bstep (se 1 (by rfl) ⟨1170818, by rfl⟩ : syracuseStep 1561091 = 2341637) B2341637
theorem B2191889 : Blo 1461050 2191889 := bstep (se 2 (by rfl) ⟨821958, by rfl⟩ : syracuseStep 2191889 = 1643917) B1643917
theorem B2191907 : Blo 1461050 2191907 := bstep (se 1 (by rfl) ⟨1643930, by rfl⟩ : syracuseStep 2191907 = 3287861) B3287861
theorem B2191937 : Blo 1461050 2191937 := bstep (se 2 (by rfl) ⟨821976, by rfl⟩ : syracuseStep 2191937 = 1643953) B1643953
theorem B2191955 : Blo 1461050 2191955 := bstep (se 1 (by rfl) ⟨1643966, by rfl⟩ : syracuseStep 2191955 = 3287933) B3287933
theorem B1667683 : Blo 1461050 1667683 := bstep (se 1 (by rfl) ⟨1250762, by rfl⟩ : syracuseStep 1667683 = 2501525) B2501525
theorem B2191985 : Blo 1461050 2191985 := bstep (se 2 (by rfl) ⟨821994, by rfl⟩ : syracuseStep 2191985 = 1643989) B1643989
theorem B15807089 : Blo 1461050 15807089 := bstep (se 2 (by rfl) ⟨5927658, by rfl⟩ : syracuseStep 15807089 = 11855317) B11855317
theorem B2192003 : Blo 1461050 2192003 := bstep (se 1 (by rfl) ⟨1644002, by rfl⟩ : syracuseStep 2192003 = 3288005) B3288005
theorem B2192033 : Blo 1461050 2192033 := bstep (se 2 (by rfl) ⟨822012, by rfl⟩ : syracuseStep 2192033 = 1644025) B1644025
theorem B2192051 : Blo 1461050 2192051 := bstep (se 1 (by rfl) ⟨1644038, by rfl⟩ : syracuseStep 2192051 = 3288077) B3288077
theorem B2192081 : Blo 1461050 2192081 := bstep (se 2 (by rfl) ⟨822030, by rfl⟩ : syracuseStep 2192081 = 1644061) B1644061
theorem B2192099 : Blo 1461050 2192099 := bstep (se 1 (by rfl) ⟨1644074, by rfl⟩ : syracuseStep 2192099 = 3288149) B3288149
theorem B38490851 : Blo 1461050 38490851 := bstep (se 1 (by rfl) ⟨28868138, by rfl⟩ : syracuseStep 38490851 = 57736277) B57736277
theorem B6099697 : Blo 1461050 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B3044081 : Blo 1461050 3044081 := bstep (se 2 (by rfl) ⟨1141530, by rfl⟩ : syracuseStep 3044081 = 2283061) B2283061
theorem B3289841 : Blo 1461050 3289841 := bstep (se 2 (by rfl) ⟨1233690, by rfl⟩ : syracuseStep 3289841 = 2467381) B2467381
theorem B2192129 : Blo 1461050 2192129 := bstep (se 2 (by rfl) ⟨822048, by rfl⟩ : syracuseStep 2192129 = 1644097) B1644097
theorem B3289859 : Blo 1461050 3289859 := bstep (se 1 (by rfl) ⟨2467394, by rfl⟩ : syracuseStep 3289859 = 4934789) B4934789
theorem B2773777 : Blo 1461050 2773777 := bstep (se 2 (by rfl) ⟨1040166, by rfl⟩ : syracuseStep 2773777 = 2080333) B2080333
theorem B2192147 : Blo 1461050 2192147 := bstep (se 1 (by rfl) ⟨1644110, by rfl⟩ : syracuseStep 2192147 = 3288221) B3288221
theorem B2192177 : Blo 1461050 2192177 := bstep (se 2 (by rfl) ⟨822066, by rfl⟩ : syracuseStep 2192177 = 1644133) B1644133
theorem B2192195 : Blo 1461050 2192195 := bstep (se 1 (by rfl) ⟨1644146, by rfl⟩ : syracuseStep 2192195 = 3288293) B3288293
theorem B8328005 : Blo 1461050 8328005 := bstep (se 4 (by rfl) ⟨780750, by rfl⟩ : syracuseStep 8328005 = 1561501) B1561501
theorem B2192225 : Blo 1461050 2192225 := bstep (se 2 (by rfl) ⟨822084, by rfl⟩ : syracuseStep 2192225 = 1644169) B1644169
theorem B2192243 : Blo 1461050 2192243 := bstep (se 1 (by rfl) ⟨1644182, by rfl⟩ : syracuseStep 2192243 = 3288365) B3288365
theorem B2192273 : Blo 1461050 2192273 := bstep (se 2 (by rfl) ⟨822102, by rfl⟩ : syracuseStep 2192273 = 1644205) B1644205
theorem B2192291 : Blo 1461050 2192291 := bstep (se 1 (by rfl) ⟨1644218, by rfl⟩ : syracuseStep 2192291 = 3288437) B3288437
theorem B2192321 : Blo 1461050 2192321 := bstep (se 2 (by rfl) ⟨822120, by rfl⟩ : syracuseStep 2192321 = 1644241) B1644241
theorem B3699665 : Blo 1461050 3699665 := bstep (se 2 (by rfl) ⟨1387374, by rfl⟩ : syracuseStep 3699665 = 2774749) B2774749
theorem B2192339 : Blo 1461050 2192339 := bstep (se 1 (by rfl) ⟨1644254, by rfl⟩ : syracuseStep 2192339 = 3288509) B3288509
theorem B2192369 : Blo 1461050 2192369 := bstep (se 2 (by rfl) ⟨822138, by rfl⟩ : syracuseStep 2192369 = 1644277) B1644277
theorem B2192387 : Blo 1461050 2192387 := bstep (se 1 (by rfl) ⟨1644290, by rfl⟩ : syracuseStep 2192387 = 3288581) B3288581
theorem B3699715 : Blo 1461050 3699715 := bstep (se 1 (by rfl) ⟨2774786, by rfl⟩ : syracuseStep 3699715 = 5549573) B5549573
theorem B3290129 : Blo 1461050 3290129 := bstep (se 2 (by rfl) ⟨1233798, by rfl⟩ : syracuseStep 3290129 = 2467597) B2467597
theorem B2192417 : Blo 1461050 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B3290147 : Blo 1461050 3290147 := bstep (se 1 (by rfl) ⟨2467610, by rfl⟩ : syracuseStep 3290147 = 4935221) B4935221
theorem B2192435 : Blo 1461050 2192435 := bstep (se 1 (by rfl) ⟨1644326, by rfl⟩ : syracuseStep 2192435 = 3288653) B3288653
theorem B2192465 : Blo 1461050 2192465 := bstep (se 2 (by rfl) ⟨822174, by rfl⟩ : syracuseStep 2192465 = 1644349) B1644349
theorem B2192483 : Blo 1461050 2192483 := bstep (se 1 (by rfl) ⟨1644362, by rfl⟩ : syracuseStep 2192483 = 3288725) B3288725
theorem B2192513 : Blo 1461050 2192513 := bstep (se 2 (by rfl) ⟨822192, by rfl⟩ : syracuseStep 2192513 = 1644385) B1644385
theorem B3699857 : Blo 1461050 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B2192531 : Blo 1461050 2192531 := bstep (se 1 (by rfl) ⟨1644398, by rfl⟩ : syracuseStep 2192531 = 3288797) B3288797
theorem B1643683 : Blo 1461050 1643683 := bstep (se 1 (by rfl) ⟨1232762, by rfl⟩ : syracuseStep 1643683 = 2465525) B2465525
theorem B2774179 : Blo 1461050 2774179 := bstep (se 1 (by rfl) ⟨2080634, by rfl⟩ : syracuseStep 2774179 = 4161269) B4161269
theorem B2192561 : Blo 1461050 2192561 := bstep (se 2 (by rfl) ⟨822210, by rfl⟩ : syracuseStep 2192561 = 1644421) B1644421
theorem B2192579 : Blo 1461050 2192579 := bstep (se 1 (by rfl) ⟨1644434, by rfl⟩ : syracuseStep 2192579 = 3288869) B3288869
theorem B2634947 : Blo 1461050 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B22508741 : Blo 1461050 22508741 := bstep (se 4 (by rfl) ⟨2110194, by rfl⟩ : syracuseStep 22508741 = 4220389) B4220389
theorem B2774225 : Blo 1461050 2774225 := bstep (se 2 (by rfl) ⟨1040334, by rfl⟩ : syracuseStep 2774225 = 2080669) B2080669
theorem B2192609 : Blo 1461050 2192609 := bstep (se 2 (by rfl) ⟨822228, by rfl⟩ : syracuseStep 2192609 = 1644457) B1644457
theorem B2192627 : Blo 1461050 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B2192657 : Blo 1461050 2192657 := bstep (se 2 (by rfl) ⟨822246, by rfl⟩ : syracuseStep 2192657 = 1644493) B1644493
theorem B2192675 : Blo 1461050 2192675 := bstep (se 1 (by rfl) ⟨1644506, by rfl⟩ : syracuseStep 2192675 = 3289013) B3289013
theorem B3290417 : Blo 1461050 3290417 := bstep (se 2 (by rfl) ⟨1233906, by rfl⟩ : syracuseStep 3290417 = 2467813) B2467813
theorem B1643827 : Blo 1461050 1643827 := bstep (se 1 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 1643827 = 2465741) B2465741
theorem B2192705 : Blo 1461050 2192705 := bstep (se 2 (by rfl) ⟨822264, by rfl⟩ : syracuseStep 2192705 = 1644529) B1644529
theorem B3290435 : Blo 1461050 3290435 := bstep (se 1 (by rfl) ⟨2467826, by rfl⟩ : syracuseStep 3290435 = 4935653) B4935653
theorem B2110801 : Blo 1461050 2110801 := bstep (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) B1583101
theorem B2192723 : Blo 1461050 2192723 := bstep (se 1 (by rfl) ⟨1644542, by rfl⟩ : syracuseStep 2192723 = 3289085) B3289085
theorem B2192753 : Blo 1461050 2192753 := bstep (se 2 (by rfl) ⟨822282, by rfl⟩ : syracuseStep 2192753 = 1644565) B1644565
theorem B2192771 : Blo 1461050 2192771 := bstep (se 1 (by rfl) ⟨1644578, by rfl⟩ : syracuseStep 2192771 = 3289157) B3289157
theorem B2192801 : Blo 1461050 2192801 := bstep (se 2 (by rfl) ⟨822300, by rfl⟩ : syracuseStep 2192801 = 1644601) B1644601
theorem B2192819 : Blo 1461050 2192819 := bstep (se 1 (by rfl) ⟨1644614, by rfl⟩ : syracuseStep 2192819 = 3289229) B3289229
theorem B1643971 : Blo 1461050 1643971 := bstep (se 1 (by rfl) ⟨1232978, by rfl⟩ : syracuseStep 1643971 = 2465957) B2465957
theorem B2192849 : Blo 1461050 2192849 := bstep (se 2 (by rfl) ⟨822318, by rfl⟩ : syracuseStep 2192849 = 1644637) B1644637
theorem B21067235 : Blo 1461050 21067235 := bstep (se 1 (by rfl) ⟨15800426, by rfl⟩ : syracuseStep 21067235 = 31600853) B31600853
theorem B2192867 : Blo 1461050 2192867 := bstep (se 1 (by rfl) ⟨1644650, by rfl⟩ : syracuseStep 2192867 = 3289301) B3289301
theorem B2774513 : Blo 1461050 2774513 := bstep (se 2 (by rfl) ⟨1040442, by rfl⟩ : syracuseStep 2774513 = 2080885) B2080885
theorem B8328689 : Blo 1461050 8328689 := bstep (se 2 (by rfl) ⟨3123258, by rfl⟩ : syracuseStep 8328689 = 6246517) B6246517
theorem B2192897 : Blo 1461050 2192897 := bstep (se 2 (by rfl) ⟨822336, by rfl⟩ : syracuseStep 2192897 = 1644673) B1644673
theorem B2192915 : Blo 1461050 2192915 := bstep (se 1 (by rfl) ⟨1644686, by rfl⟩ : syracuseStep 2192915 = 3289373) B3289373
theorem B2192945 : Blo 1461050 2192945 := bstep (se 2 (by rfl) ⟨822354, by rfl⟩ : syracuseStep 2192945 = 1644709) B1644709
theorem B2192963 : Blo 1461050 2192963 := bstep (se 1 (by rfl) ⟨1644722, by rfl⟩ : syracuseStep 2192963 = 3289445) B3289445
theorem B3290705 : Blo 1461050 3290705 := bstep (se 2 (by rfl) ⟨1234014, by rfl⟩ : syracuseStep 3290705 = 2468029) B2468029
theorem B1644115 : Blo 1461050 1644115 := bstep (se 1 (by rfl) ⟨1233086, by rfl⟩ : syracuseStep 1644115 = 2466173) B2466173
theorem B2192993 : Blo 1461050 2192993 := bstep (se 2 (by rfl) ⟨822372, by rfl⟩ : syracuseStep 2192993 = 1644745) B1644745
theorem B3290723 : Blo 1461050 3290723 := bstep (se 1 (by rfl) ⟨2468042, by rfl⟩ : syracuseStep 3290723 = 4936085) B4936085
theorem B2193011 : Blo 1461050 2193011 := bstep (se 1 (by rfl) ⟨1644758, by rfl⟩ : syracuseStep 2193011 = 3289517) B3289517
theorem B2340497 : Blo 1461050 2340497 := bstep (se 2 (by rfl) ⟨877686, by rfl⟩ : syracuseStep 2340497 = 1755373) B1755373
theorem B2193041 : Blo 1461050 2193041 := bstep (se 2 (by rfl) ⟨822390, by rfl⟩ : syracuseStep 2193041 = 1644781) B1644781
theorem B2635409 : Blo 1461050 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B2193059 : Blo 1461050 2193059 := bstep (se 1 (by rfl) ⟨1644794, by rfl⟩ : syracuseStep 2193059 = 3289589) B3289589
theorem B8115889 : Blo 1461050 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B2193089 : Blo 1461050 2193089 := bstep (se 2 (by rfl) ⟨822408, by rfl⟩ : syracuseStep 2193089 = 1644817) B1644817
theorem B2193107 : Blo 1461050 2193107 := bstep (se 1 (by rfl) ⟨1644830, by rfl⟩ : syracuseStep 2193107 = 3289661) B3289661
theorem B1644259 : Blo 1461050 1644259 := bstep (se 1 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 1644259 = 2466389) B2466389
theorem B2193137 : Blo 1461050 2193137 := bstep (se 2 (by rfl) ⟨822426, by rfl⟩ : syracuseStep 2193137 = 1644853) B1644853
theorem B2193155 : Blo 1461050 2193155 := bstep (se 1 (by rfl) ⟨1644866, by rfl⟩ : syracuseStep 2193155 = 3289733) B3289733
theorem B2193185 : Blo 1461050 2193185 := bstep (se 2 (by rfl) ⟨822444, by rfl⟩ : syracuseStep 2193185 = 1644889) B1644889
theorem B2193203 : Blo 1461050 2193203 := bstep (se 1 (by rfl) ⟨1644902, by rfl⟩ : syracuseStep 2193203 = 3289805) B3289805
theorem B2373457 : Blo 1461050 2373457 := bstep (se 2 (by rfl) ⟨890046, by rfl⟩ : syracuseStep 2373457 = 1780093) B1780093
theorem B2193233 : Blo 1461050 2193233 := bstep (se 2 (by rfl) ⟨822462, by rfl⟩ : syracuseStep 2193233 = 1644925) B1644925
theorem B2193251 : Blo 1461050 2193251 := bstep (se 1 (by rfl) ⟨1644938, by rfl⟩ : syracuseStep 2193251 = 3289877) B3289877
theorem B14055281 : Blo 1461050 14055281 := bstep (se 2 (by rfl) ⟨5270730, by rfl⟩ : syracuseStep 14055281 = 10541461) B10541461
theorem B1644403 : Blo 1461050 1644403 := bstep (se 1 (by rfl) ⟨1233302, by rfl⟩ : syracuseStep 1644403 = 2466605) B2466605
theorem B2193281 : Blo 1461050 2193281 := bstep (se 2 (by rfl) ⟨822480, by rfl⟩ : syracuseStep 2193281 = 1644961) B1644961
theorem B16013197 : Blo 1461050 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B2193299 : Blo 1461050 2193299 := bstep (se 1 (by rfl) ⟨1644974, by rfl⟩ : syracuseStep 2193299 = 3289949) B3289949
theorem B4683683 : Blo 1461050 4683683 := bstep (se 1 (by rfl) ⟨3512762, by rfl⟩ : syracuseStep 4683683 = 7025525) B7025525
theorem B2340785 : Blo 1461050 2340785 := bstep (se 2 (by rfl) ⟨877794, by rfl⟩ : syracuseStep 2340785 = 1755589) B1755589
theorem B2193329 : Blo 1461050 2193329 := bstep (se 2 (by rfl) ⟨822498, by rfl⟩ : syracuseStep 2193329 = 1644997) B1644997
theorem B2193347 : Blo 1461050 2193347 := bstep (se 1 (by rfl) ⟨1645010, by rfl⟩ : syracuseStep 2193347 = 3290021) B3290021
theorem B2193377 : Blo 1461050 2193377 := bstep (se 2 (by rfl) ⟨822516, by rfl⟩ : syracuseStep 2193377 = 1645033) B1645033
theorem B1849331 : Blo 1461050 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B2193395 : Blo 1461050 2193395 := bstep (se 1 (by rfl) ⟨1645046, by rfl⟩ : syracuseStep 2193395 = 3290093) B3290093
theorem B1644547 : Blo 1461050 1644547 := bstep (se 1 (by rfl) ⟨1233410, by rfl⟩ : syracuseStep 1644547 = 2466821) B2466821
theorem B3749905 : Blo 1461050 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B2193425 : Blo 1461050 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B2193443 : Blo 1461050 2193443 := bstep (se 1 (by rfl) ⟨1645082, by rfl⟩ : syracuseStep 2193443 = 3290165) B3290165
theorem B2193473 : Blo 1461050 2193473 := bstep (se 2 (by rfl) ⟨822552, by rfl⟩ : syracuseStep 2193473 = 1645105) B1645105
theorem B2193491 : Blo 1461050 2193491 := bstep (se 1 (by rfl) ⟨1645118, by rfl⟩ : syracuseStep 2193491 = 3290237) B3290237
theorem B7903331 : Blo 1461050 7903331 := bstep (se 1 (by rfl) ⟨5927498, by rfl⟩ : syracuseStep 7903331 = 11854997) B11854997
theorem B3700849 : Blo 1461050 3700849 := bstep (se 2 (by rfl) ⟨1387818, by rfl⟩ : syracuseStep 3700849 = 2775637) B2775637
theorem B2193521 : Blo 1461050 2193521 := bstep (se 2 (by rfl) ⟨822570, by rfl⟩ : syracuseStep 2193521 = 1645141) B1645141
theorem B2193539 : Blo 1461050 2193539 := bstep (se 1 (by rfl) ⟨1645154, by rfl⟩ : syracuseStep 2193539 = 3290309) B3290309
theorem B2341009 : Blo 1461050 2341009 := bstep (se 2 (by rfl) ⟨877878, by rfl⟩ : syracuseStep 2341009 = 1755757) B1755757
theorem B1644691 : Blo 1461050 1644691 := bstep (se 1 (by rfl) ⟨1233518, by rfl⟩ : syracuseStep 1644691 = 2467037) B2467037
theorem B2193569 : Blo 1461050 2193569 := bstep (se 2 (by rfl) ⟨822588, by rfl⟩ : syracuseStep 2193569 = 1645177) B1645177
theorem B2193587 : Blo 1461050 2193587 := bstep (se 1 (by rfl) ⟨1645190, by rfl⟩ : syracuseStep 2193587 = 3290381) B3290381
theorem B2775235 : Blo 1461050 2775235 := bstep (se 1 (by rfl) ⟨2081426, by rfl⟩ : syracuseStep 2775235 = 4162853) B4162853
theorem B2193617 : Blo 1461050 2193617 := bstep (se 2 (by rfl) ⟨822606, by rfl⟩ : syracuseStep 2193617 = 1645213) B1645213
theorem B9369827 : Blo 1461050 9369827 := bstep (se 1 (by rfl) ⟨7027370, by rfl⟩ : syracuseStep 9369827 = 14054741) B14054741
theorem B2193635 : Blo 1461050 2193635 := bstep (se 1 (by rfl) ⟨1645226, by rfl⟩ : syracuseStep 2193635 = 3290453) B3290453
theorem B2193665 : Blo 1461050 2193665 := bstep (se 2 (by rfl) ⟨822624, by rfl⟩ : syracuseStep 2193665 = 1645249) B1645249
theorem B2193683 : Blo 1461050 2193683 := bstep (se 1 (by rfl) ⟨1645262, by rfl⟩ : syracuseStep 2193683 = 3290525) B3290525
theorem B1644835 : Blo 1461050 1644835 := bstep (se 1 (by rfl) ⟨1233626, by rfl⟩ : syracuseStep 1644835 = 2467253) B2467253
theorem B2193713 : Blo 1461050 2193713 := bstep (se 2 (by rfl) ⟨822642, by rfl⟩ : syracuseStep 2193713 = 1645285) B1645285
theorem B2193731 : Blo 1461050 2193731 := bstep (se 1 (by rfl) ⟨1645298, by rfl⟩ : syracuseStep 2193731 = 3290597) B3290597
theorem B2193761 : Blo 1461050 2193761 := bstep (se 2 (by rfl) ⟨822660, by rfl⟩ : syracuseStep 2193761 = 1645321) B1645321
theorem B2193779 : Blo 1461050 2193779 := bstep (se 1 (by rfl) ⟨1645334, by rfl⟩ : syracuseStep 2193779 = 3290669) B3290669
theorem B3701123 : Blo 1461050 3701123 := bstep (se 1 (by rfl) ⟨2775842, by rfl⟩ : syracuseStep 3701123 = 5551685) B5551685
theorem B2193809 : Blo 1461050 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B1644979 : Blo 1461050 1644979 := bstep (se 1 (by rfl) ⟨1233734, by rfl⟩ : syracuseStep 1644979 = 2467469) B2467469
theorem B3701315 : Blo 1461050 3701315 := bstep (se 1 (by rfl) ⟨2775986, by rfl⟩ : syracuseStep 3701315 = 5551973) B5551973
theorem B1645123 : Blo 1461050 1645123 := bstep (se 1 (by rfl) ⟨1233842, by rfl⟩ : syracuseStep 1645123 = 2467685) B2467685
theorem B2775683 : Blo 1461050 2775683 := bstep (se 1 (by rfl) ⟨2081762, by rfl⟩ : syracuseStep 2775683 = 4163525) B4163525
theorem B2284193 : Blo 1461050 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B7215779 : Blo 1461050 7215779 := bstep (se 1 (by rfl) ⟨5411834, by rfl⟩ : syracuseStep 7215779 = 10823669) B10823669
theorem B3750563 : Blo 1461050 3750563 := bstep (se 1 (by rfl) ⟨2812922, by rfl⟩ : syracuseStep 3750563 = 5625845) B5625845
theorem B1850035 : Blo 1461050 1850035 := bstep (se 1 (by rfl) ⟨1387526, by rfl⟩ : syracuseStep 1850035 = 2775053) B2775053
theorem B1645267 : Blo 1461050 1645267 := bstep (se 1 (by rfl) ⟨1233950, by rfl⟩ : syracuseStep 1645267 = 2467901) B2467901
theorem B1850131 : Blo 1461050 1850131 := bstep (se 1 (by rfl) ⟨1387598, by rfl⟩ : syracuseStep 1850131 = 2775197) B2775197
theorem B5552945 : Blo 1461050 5552945 := bstep (se 2 (by rfl) ⟨2082354, by rfl⟩ : syracuseStep 5552945 = 4164709) B4164709
theorem B5069645 : Blo 1461050 5069645 := bstep (se 3 (by rfl) ⟨950558, by rfl⟩ : syracuseStep 5069645 = 1901117) B1901117
theorem B4684657 : Blo 1461050 4684657 := bstep (se 2 (by rfl) ⟨1756746, by rfl⟩ : syracuseStep 4684657 = 3513493) B3513493
theorem B2775971 : Blo 1461050 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B5626829 : Blo 1461050 5626829 := bstep (se 3 (by rfl) ⟨1055030, by rfl⟩ : syracuseStep 5626829 = 2110061) B2110061
theorem B2964593 : Blo 1461050 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B1850627 : Blo 1461050 1850627 := bstep (se 1 (by rfl) ⟨1387970, by rfl⟩ : syracuseStep 1850627 = 2775941) B2775941
theorem B60833045 : Blo 1461050 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B47431109 : Blo 1461050 47431109 := bstep (se 4 (by rfl) ⟨4446666, by rfl⟩ : syracuseStep 47431109 = 8893333) B8893333
theorem B4161041 : Blo 1461050 4161041 := bstep (se 2 (by rfl) ⟨1560390, by rfl⟩ : syracuseStep 4161041 = 3120781) B3120781
theorem B4931117 : Blo 1461050 4931117 := bstep (se 3 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 4931117 = 1849169) B1849169
theorem B4931171 : Blo 1461050 4931171 := bstep (se 1 (by rfl) ⟨3698378, by rfl⟩ : syracuseStep 4931171 = 7396757) B7396757
theorem B3513955 : Blo 1461050 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B2342611 : Blo 1461050 2342611 := bstep (se 1 (by rfl) ⟨1756958, by rfl⟩ : syracuseStep 2342611 = 3513917) B3513917
theorem B2080561 : Blo 1461050 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B2465633 : Blo 1461050 2465633 := bstep (se 2 (by rfl) ⟨924612, by rfl⟩ : syracuseStep 2465633 = 1849225) B1849225
theorem B4931441 : Blo 1461050 4931441 := bstep (se 2 (by rfl) ⟨1849290, by rfl⟩ : syracuseStep 4931441 = 3698581) B3698581
theorem B2080657 : Blo 1461050 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B2465761 : Blo 1461050 2465761 := bstep (se 2 (by rfl) ⟨924660, by rfl⟩ : syracuseStep 2465761 = 1849321) B1849321
theorem B2465815 : Blo 1461050 2465815 := bstep (se 1 (by rfl) ⟨1849361, by rfl⟩ : syracuseStep 2465815 = 3698723) B3698723
theorem B18980939 : Blo 1461050 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B4161611 : Blo 1461050 4161611 := bstep (se 1 (by rfl) ⟨3121208, by rfl⟩ : syracuseStep 4161611 = 6242417) B6242417
theorem B5267531 : Blo 1461050 5267531 := bstep (se 1 (by rfl) ⟨3950648, by rfl⟩ : syracuseStep 5267531 = 7901297) B7901297
theorem B5267587 : Blo 1461050 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B8437891 : Blo 1461050 8437891 := bstep (se 1 (by rfl) ⟨6328418, by rfl⟩ : syracuseStep 8437891 = 12656837) B12656837
theorem B3121345 : Blo 1461050 3121345 := bstep (se 2 (by rfl) ⟨1170504, by rfl⟩ : syracuseStep 3121345 = 2341009) B2341009
theorem B2081227 : Blo 1461050 2081227 := bstep (se 1 (by rfl) ⟨1560920, by rfl⟩ : syracuseStep 2081227 = 3121841) B3121841
theorem B6242777 : Blo 1461050 6242777 := bstep (se 2 (by rfl) ⟨2341041, by rfl⟩ : syracuseStep 6242777 = 4682083) B4682083
theorem B5267933 : Blo 1461050 5267933 := bstep (se 3 (by rfl) ⟨987737, by rfl⟩ : syracuseStep 5267933 = 1975475) B1975475
theorem B2466443 : Blo 1461050 2466443 := bstep (se 1 (by rfl) ⟨1849832, by rfl⟩ : syracuseStep 2466443 = 3699665) B3699665
theorem B2466571 : Blo 1461050 2466571 := bstep (se 1 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 2466571 = 3699857) B3699857
theorem B2466713 : Blo 1461050 2466713 := bstep (se 2 (by rfl) ⟨925017, by rfl⟩ : syracuseStep 2466713 = 1850035) B1850035
theorem B35554265 : Blo 1461050 35554265 := bstep (se 2 (by rfl) ⟨13332849, by rfl⟩ : syracuseStep 35554265 = 26665699) B26665699
theorem B2466841 : Blo 1461050 2466841 := bstep (se 2 (by rfl) ⟨925065, by rfl⟩ : syracuseStep 2466841 = 1850131) B1850131
theorem B4932683 : Blo 1461050 4932683 := bstep (se 1 (by rfl) ⟨3699512, by rfl⟩ : syracuseStep 4932683 = 7399025) B7399025
theorem B32531717 : Blo 1461050 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B7398701 : Blo 1461050 7398701 := bstep (se 3 (by rfl) ⟨1387256, by rfl⟩ : syracuseStep 7398701 = 2774513) B2774513
theorem B4932953 : Blo 1461050 4932953 := bstep (se 2 (by rfl) ⟨1849857, by rfl⟩ : syracuseStep 4932953 = 3699715) B3699715
theorem B4162909 : Blo 1461050 4162909 := bstep (se 3 (by rfl) ⟨780545, by rfl⟩ : syracuseStep 4162909 = 1561091) B1561091
theorem B5268887 : Blo 1461050 5268887 := bstep (se 1 (by rfl) ⟨3951665, by rfl⟩ : syracuseStep 5268887 = 7903331) B7903331
theorem B2467415 : Blo 1461050 2467415 := bstep (se 1 (by rfl) ⟨1850561, by rfl⟩ : syracuseStep 2467415 = 3701123) B3701123
theorem B4163251 : Blo 1461050 4163251 := bstep (se 1 (by rfl) ⟨3122438, by rfl⟩ : syracuseStep 4163251 = 6244877) B6244877
theorem B2467543 : Blo 1461050 2467543 := bstep (se 1 (by rfl) ⟨1850657, by rfl⟩ : syracuseStep 2467543 = 3701315) B3701315
theorem B4810519 : Blo 1461050 4810519 := bstep (se 1 (by rfl) ⟨3607889, by rfl⟩ : syracuseStep 4810519 = 7215779) B7215779
theorem B4933655 : Blo 1461050 4933655 := bstep (se 1 (by rfl) ⟨3700241, by rfl⟩ : syracuseStep 4933655 = 7400483) B7400483
theorem B85403717 : Blo 1461050 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B1976395 : Blo 1461050 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B3123481 : Blo 1461050 3123481 := bstep (se 2 (by rfl) ⟨1171305, by rfl⟩ : syracuseStep 3123481 = 2342611) B2342611
theorem B3164503 : Blo 1461050 3164503 := bstep (se 1 (by rfl) ⟨2373377, by rfl⟩ : syracuseStep 3164503 = 4746755) B4746755
theorem B3287411 : Blo 1461050 3287411 := bstep (se 1 (by rfl) ⟨2465558, by rfl⟩ : syracuseStep 3287411 = 4931117) B4931117
theorem B3287447 : Blo 1461050 3287447 := bstep (se 1 (by rfl) ⟨2465585, by rfl⟩ : syracuseStep 3287447 = 4931171) B4931171
theorem B3164609 : Blo 1461050 3164609 := bstep (se 2 (by rfl) ⟨1186728, by rfl⟩ : syracuseStep 3164609 = 2373457) B2373457
theorem B11102669 : Blo 1461050 11102669 := bstep (se 3 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 11102669 = 4163501) B4163501
theorem B4934195 : Blo 1461050 4934195 := bstep (se 1 (by rfl) ⟨3700646, by rfl⟩ : syracuseStep 4934195 = 7401293) B7401293
theorem B3287627 : Blo 1461050 3287627 := bstep (se 1 (by rfl) ⟨2465720, by rfl⟩ : syracuseStep 3287627 = 4931441) B4931441
theorem B4164185 : Blo 1461050 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B3287681 : Blo 1461050 3287681 := bstep (se 2 (by rfl) ⟨1232880, by rfl⟩ : syracuseStep 3287681 = 2465761) B2465761
theorem B19999493 : Blo 1461050 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B4934465 : Blo 1461050 4934465 := bstep (se 2 (by rfl) ⟨1850424, by rfl⟩ : syracuseStep 4934465 = 3700849) B3700849
theorem B1461067 : Blo 1461050 1461067 := bstep (se 1 (by rfl) ⟨1095800, by rfl⟩ : syracuseStep 1461067 = 2191601) B2191601
theorem B1461079 : Blo 1461050 1461079 := bstep (se 1 (by rfl) ⟨1095809, by rfl⟩ : syracuseStep 1461079 = 2191619) B2191619
theorem B3287897 : Blo 1461050 3287897 := bstep (se 2 (by rfl) ⟨1232961, by rfl⟩ : syracuseStep 3287897 = 2465923) B2465923
theorem B1461099 : Blo 1461050 1461099 := bstep (se 1 (by rfl) ⟨1095824, by rfl⟩ : syracuseStep 1461099 = 2191649) B2191649
theorem B1461111 : Blo 1461050 1461111 := bstep (se 1 (by rfl) ⟨1095833, by rfl⟩ : syracuseStep 1461111 = 2191667) B2191667
theorem B1461131 : Blo 1461050 1461131 := bstep (se 1 (by rfl) ⟨1095848, by rfl⟩ : syracuseStep 1461131 = 2191697) B2191697
theorem B1461143 : Blo 1461050 1461143 := bstep (se 1 (by rfl) ⟨1095857, by rfl⟩ : syracuseStep 1461143 = 2191715) B2191715
theorem B1461163 : Blo 1461050 1461163 := bstep (se 1 (by rfl) ⟨1095872, by rfl⟩ : syracuseStep 1461163 = 2191745) B2191745
theorem B3287987 : Blo 1461050 3287987 := bstep (se 1 (by rfl) ⟨2465990, by rfl⟩ : syracuseStep 3287987 = 4931981) B4931981
theorem B11103155 : Blo 1461050 11103155 := bstep (se 1 (by rfl) ⟨8327366, by rfl⟩ : syracuseStep 11103155 = 16654733) B16654733
theorem B1461175 : Blo 1461050 1461175 := bstep (se 1 (by rfl) ⟨1095881, by rfl⟩ : syracuseStep 1461175 = 2191763) B2191763
theorem B1461195 : Blo 1461050 1461195 := bstep (se 1 (by rfl) ⟨1095896, by rfl⟩ : syracuseStep 1461195 = 2191793) B2191793
theorem B1461207 : Blo 1461050 1461207 := bstep (se 1 (by rfl) ⟨1095905, by rfl⟩ : syracuseStep 1461207 = 2191811) B2191811
theorem B3288023 : Blo 1461050 3288023 := bstep (se 1 (by rfl) ⟨2466017, by rfl⟩ : syracuseStep 3288023 = 4932035) B4932035
theorem B1461227 : Blo 1461050 1461227 := bstep (se 1 (by rfl) ⟨1095920, by rfl⟩ : syracuseStep 1461227 = 2191841) B2191841
theorem B1461239 : Blo 1461050 1461239 := bstep (se 1 (by rfl) ⟨1095929, by rfl⟩ : syracuseStep 1461239 = 2191859) B2191859
theorem B1461259 : Blo 1461050 1461259 := bstep (se 1 (by rfl) ⟨1095944, by rfl⟩ : syracuseStep 1461259 = 2191889) B2191889
theorem B1461271 : Blo 1461050 1461271 := bstep (se 1 (by rfl) ⟨1095953, by rfl⟩ : syracuseStep 1461271 = 2191907) B2191907
theorem B1461291 : Blo 1461050 1461291 := bstep (se 1 (by rfl) ⟨1095968, by rfl⟩ : syracuseStep 1461291 = 2191937) B2191937
theorem B1461303 : Blo 1461050 1461303 := bstep (se 1 (by rfl) ⟨1095977, by rfl⟩ : syracuseStep 1461303 = 2191955) B2191955
theorem B1461323 : Blo 1461050 1461323 := bstep (se 1 (by rfl) ⟨1095992, by rfl⟩ : syracuseStep 1461323 = 2191985) B2191985
theorem B10538059 : Blo 1461050 10538059 := bstep (se 1 (by rfl) ⟨7903544, by rfl⟩ : syracuseStep 10538059 = 15807089) B15807089
theorem B1461335 : Blo 1461050 1461335 := bstep (se 1 (by rfl) ⟨1096001, by rfl⟩ : syracuseStep 1461335 = 2192003) B2192003
theorem B2813015 : Blo 1461050 2813015 := bstep (se 1 (by rfl) ⟨2109761, by rfl⟩ : syracuseStep 2813015 = 4219523) B4219523
theorem B1461355 : Blo 1461050 1461355 := bstep (se 1 (by rfl) ⟨1096016, by rfl⟩ : syracuseStep 1461355 = 2192033) B2192033
theorem B1461367 : Blo 1461050 1461367 := bstep (se 1 (by rfl) ⟨1096025, by rfl⟩ : syracuseStep 1461367 = 2192051) B2192051
theorem B1461387 : Blo 1461050 1461387 := bstep (se 1 (by rfl) ⟨1096040, by rfl⟩ : syracuseStep 1461387 = 2192081) B2192081
theorem B3288203 : Blo 1461050 3288203 := bstep (se 1 (by rfl) ⟨2466152, by rfl⟩ : syracuseStep 3288203 = 4932305) B4932305
theorem B1461399 : Blo 1461050 1461399 := bstep (se 1 (by rfl) ⟨1096049, by rfl⟩ : syracuseStep 1461399 = 2192099) B2192099
theorem B25660567 : Blo 1461050 25660567 := bstep (se 1 (by rfl) ⟨19245425, by rfl⟩ : syracuseStep 25660567 = 38490851) B38490851
theorem B1461419 : Blo 1461050 1461419 := bstep (se 1 (by rfl) ⟨1096064, by rfl⟩ : syracuseStep 1461419 = 2192129) B2192129
theorem B1461431 : Blo 1461050 1461431 := bstep (se 1 (by rfl) ⟨1096073, by rfl⟩ : syracuseStep 1461431 = 2192147) B2192147
theorem B3288257 : Blo 1461050 3288257 := bstep (se 2 (by rfl) ⟨1233096, by rfl⟩ : syracuseStep 3288257 = 2466193) B2466193
theorem B1461451 : Blo 1461050 1461451 := bstep (se 1 (by rfl) ⟨1096088, by rfl⟩ : syracuseStep 1461451 = 2192177) B2192177
theorem B1461463 : Blo 1461050 1461463 := bstep (se 1 (by rfl) ⟨1096097, by rfl⟩ : syracuseStep 1461463 = 2192195) B2192195
theorem B1461483 : Blo 1461050 1461483 := bstep (se 1 (by rfl) ⟨1096112, by rfl⟩ : syracuseStep 1461483 = 2192225) B2192225
theorem B1461495 : Blo 1461050 1461495 := bstep (se 1 (by rfl) ⟨1096121, by rfl⟩ : syracuseStep 1461495 = 2192243) B2192243
theorem B1666315 : Blo 1461050 1666315 := bstep (se 1 (by rfl) ⟨1249736, by rfl⟩ : syracuseStep 1666315 = 2499473) B2499473
theorem B1461515 : Blo 1461050 1461515 := bstep (se 1 (by rfl) ⟨1096136, by rfl⟩ : syracuseStep 1461515 = 2192273) B2192273
theorem B1461527 : Blo 1461050 1461527 := bstep (se 1 (by rfl) ⟨1096145, by rfl⟩ : syracuseStep 1461527 = 2192291) B2192291
theorem B1461547 : Blo 1461050 1461547 := bstep (se 1 (by rfl) ⟨1096160, by rfl⟩ : syracuseStep 1461547 = 2192321) B2192321
theorem B1461559 : Blo 1461050 1461559 := bstep (se 1 (by rfl) ⟨1096169, by rfl⟩ : syracuseStep 1461559 = 2192339) B2192339
theorem B1461579 : Blo 1461050 1461579 := bstep (se 1 (by rfl) ⟨1096184, by rfl⟩ : syracuseStep 1461579 = 2192369) B2192369
theorem B1461591 : Blo 1461050 1461591 := bstep (se 1 (by rfl) ⟨1096193, by rfl⟩ : syracuseStep 1461591 = 2192387) B2192387
theorem B4935005 : Blo 1461050 4935005 := bstep (se 3 (by rfl) ⟨925313, by rfl⟩ : syracuseStep 4935005 = 1850627) B1850627
theorem B1461611 : Blo 1461050 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B1461623 : Blo 1461050 1461623 := bstep (se 1 (by rfl) ⟨1096217, by rfl⟩ : syracuseStep 1461623 = 2192435) B2192435
theorem B1461643 : Blo 1461050 1461643 := bstep (se 1 (by rfl) ⟨1096232, by rfl⟩ : syracuseStep 1461643 = 2192465) B2192465
theorem B1461655 : Blo 1461050 1461655 := bstep (se 1 (by rfl) ⟨1096241, by rfl⟩ : syracuseStep 1461655 = 2192483) B2192483
theorem B3288473 : Blo 1461050 3288473 := bstep (se 2 (by rfl) ⟨1233177, by rfl⟩ : syracuseStep 3288473 = 2466355) B2466355
theorem B1461675 : Blo 1461050 1461675 := bstep (se 1 (by rfl) ⟨1096256, by rfl⟩ : syracuseStep 1461675 = 2192513) B2192513
theorem B1461687 : Blo 1461050 1461687 := bstep (se 1 (by rfl) ⟨1096265, by rfl⟩ : syracuseStep 1461687 = 2192531) B2192531
theorem B1461707 : Blo 1461050 1461707 := bstep (se 1 (by rfl) ⟨1096280, by rfl⟩ : syracuseStep 1461707 = 2192561) B2192561
theorem B1461719 : Blo 1461050 1461719 := bstep (se 1 (by rfl) ⟨1096289, by rfl⟩ : syracuseStep 1461719 = 2192579) B2192579
theorem B1756631 : Blo 1461050 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B2223577 : Blo 1461050 2223577 := bstep (se 2 (by rfl) ⟨833841, by rfl⟩ : syracuseStep 2223577 = 1667683) B1667683
theorem B1461739 : Blo 1461050 1461739 := bstep (se 1 (by rfl) ⟨1096304, by rfl⟩ : syracuseStep 1461739 = 2192609) B2192609
theorem B3288563 : Blo 1461050 3288563 := bstep (se 1 (by rfl) ⟨2466422, by rfl⟩ : syracuseStep 3288563 = 4932845) B4932845
theorem B1461751 : Blo 1461050 1461751 := bstep (se 1 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 1461751 = 2192627) B2192627
theorem B1461771 : Blo 1461050 1461771 := bstep (se 1 (by rfl) ⟨1096328, by rfl⟩ : syracuseStep 1461771 = 2192657) B2192657
theorem B3288599 : Blo 1461050 3288599 := bstep (se 1 (by rfl) ⟨2466449, by rfl⟩ : syracuseStep 3288599 = 4932899) B4932899
theorem B1461783 : Blo 1461050 1461783 := bstep (se 1 (by rfl) ⟨1096337, by rfl⟩ : syracuseStep 1461783 = 2192675) B2192675
theorem B2108953 : Blo 1461050 2108953 := bstep (se 2 (by rfl) ⟨790857, by rfl⟩ : syracuseStep 2108953 = 1581715) B1581715
theorem B1461803 : Blo 1461050 1461803 := bstep (se 1 (by rfl) ⟨1096352, by rfl⟩ : syracuseStep 1461803 = 2192705) B2192705
theorem B1461815 : Blo 1461050 1461815 := bstep (se 1 (by rfl) ⟨1096361, by rfl⟩ : syracuseStep 1461815 = 2192723) B2192723
theorem B1461835 : Blo 1461050 1461835 := bstep (se 1 (by rfl) ⟨1096376, by rfl⟩ : syracuseStep 1461835 = 2192753) B2192753
theorem B1461847 : Blo 1461050 1461847 := bstep (se 1 (by rfl) ⟨1096385, by rfl⟩ : syracuseStep 1461847 = 2192771) B2192771
theorem B1461867 : Blo 1461050 1461867 := bstep (se 1 (by rfl) ⟨1096400, by rfl⟩ : syracuseStep 1461867 = 2192801) B2192801
theorem B1461879 : Blo 1461050 1461879 := bstep (se 1 (by rfl) ⟨1096409, by rfl⟩ : syracuseStep 1461879 = 2192819) B2192819
theorem B1461899 : Blo 1461050 1461899 := bstep (se 1 (by rfl) ⟨1096424, by rfl⟩ : syracuseStep 1461899 = 2192849) B2192849
theorem B14044823 : Blo 1461050 14044823 := bstep (se 1 (by rfl) ⟨10533617, by rfl⟩ : syracuseStep 14044823 = 21067235) B21067235
theorem B13332119 : Blo 1461050 13332119 := bstep (se 1 (by rfl) ⟨9999089, by rfl⟩ : syracuseStep 13332119 = 19998179) B19998179
theorem B1461911 : Blo 1461050 1461911 := bstep (se 1 (by rfl) ⟨1096433, by rfl⟩ : syracuseStep 1461911 = 2192867) B2192867
theorem B1461931 : Blo 1461050 1461931 := bstep (se 1 (by rfl) ⟨1096448, by rfl⟩ : syracuseStep 1461931 = 2192897) B2192897
theorem B5549741 : Blo 1461050 5549741 := bstep (se 3 (by rfl) ⟨1040576, by rfl⟩ : syracuseStep 5549741 = 2081153) B2081153
theorem B1461943 : Blo 1461050 1461943 := bstep (se 1 (by rfl) ⟨1096457, by rfl⟩ : syracuseStep 1461943 = 2192915) B2192915
theorem B3698369 : Blo 1461050 3698369 := bstep (se 2 (by rfl) ⟨1386888, by rfl⟩ : syracuseStep 3698369 = 2773777) B2773777
theorem B2633419 : Blo 1461050 2633419 := bstep (se 1 (by rfl) ⟨1975064, by rfl⟩ : syracuseStep 2633419 = 3950129) B3950129
theorem B3288779 : Blo 1461050 3288779 := bstep (se 1 (by rfl) ⟨2466584, by rfl⟩ : syracuseStep 3288779 = 4933169) B4933169
theorem B1461963 : Blo 1461050 1461963 := bstep (se 1 (by rfl) ⟨1096472, by rfl⟩ : syracuseStep 1461963 = 2192945) B2192945
theorem B1461975 : Blo 1461050 1461975 := bstep (se 1 (by rfl) ⟨1096481, by rfl⟩ : syracuseStep 1461975 = 2192963) B2192963
theorem B1461995 : Blo 1461050 1461995 := bstep (se 1 (by rfl) ⟨1096496, by rfl⟩ : syracuseStep 1461995 = 2192993) B2192993
theorem B1462007 : Blo 1461050 1462007 := bstep (se 1 (by rfl) ⟨1096505, by rfl⟩ : syracuseStep 1462007 = 2193011) B2193011
theorem B3288833 : Blo 1461050 3288833 := bstep (se 2 (by rfl) ⟨1233312, by rfl⟩ : syracuseStep 3288833 = 2466625) B2466625
theorem B1560331 : Blo 1461050 1560331 := bstep (se 1 (by rfl) ⟨1170248, by rfl⟩ : syracuseStep 1560331 = 2340497) B2340497
theorem B1462027 : Blo 1461050 1462027 := bstep (se 1 (by rfl) ⟨1096520, by rfl⟩ : syracuseStep 1462027 = 2193041) B2193041
theorem B1756939 : Blo 1461050 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B1462039 : Blo 1461050 1462039 := bstep (se 1 (by rfl) ⟨1096529, by rfl⟩ : syracuseStep 1462039 = 2193059) B2193059
theorem B1462059 : Blo 1461050 1462059 := bstep (se 1 (by rfl) ⟨1096544, by rfl⟩ : syracuseStep 1462059 = 2193089) B2193089
theorem B1462071 : Blo 1461050 1462071 := bstep (se 1 (by rfl) ⟨1096553, by rfl⟩ : syracuseStep 1462071 = 2193107) B2193107
theorem B6246209 : Blo 1461050 6246209 := bstep (se 2 (by rfl) ⟨2342328, by rfl⟩ : syracuseStep 6246209 = 4684657) B4684657
theorem B1462091 : Blo 1461050 1462091 := bstep (se 1 (by rfl) ⟨1096568, by rfl⟩ : syracuseStep 1462091 = 2193137) B2193137
theorem B1462103 : Blo 1461050 1462103 := bstep (se 1 (by rfl) ⟨1096577, by rfl⟩ : syracuseStep 1462103 = 2193155) B2193155
theorem B1462123 : Blo 1461050 1462123 := bstep (se 1 (by rfl) ⟨1096592, by rfl⟩ : syracuseStep 1462123 = 2193185) B2193185
theorem B1462135 : Blo 1461050 1462135 := bstep (se 1 (by rfl) ⟨1096601, by rfl⟩ : syracuseStep 1462135 = 2193203) B2193203
theorem B1462155 : Blo 1461050 1462155 := bstep (se 1 (by rfl) ⟨1096616, by rfl⟩ : syracuseStep 1462155 = 2193233) B2193233
theorem B1462167 : Blo 1461050 1462167 := bstep (se 1 (by rfl) ⟨1096625, by rfl⟩ : syracuseStep 1462167 = 2193251) B2193251
theorem B1462187 : Blo 1461050 1462187 := bstep (se 1 (by rfl) ⟨1096640, by rfl⟩ : syracuseStep 1462187 = 2193281) B2193281
theorem B1462199 : Blo 1461050 1462199 := bstep (se 1 (by rfl) ⟨1096649, by rfl⟩ : syracuseStep 1462199 = 2193299) B2193299
theorem B1462219 : Blo 1461050 1462219 := bstep (se 1 (by rfl) ⟨1096664, by rfl⟩ : syracuseStep 1462219 = 2193329) B2193329
theorem B1462231 : Blo 1461050 1462231 := bstep (se 1 (by rfl) ⟨1096673, by rfl⟩ : syracuseStep 1462231 = 2193347) B2193347
theorem B3289049 : Blo 1461050 3289049 := bstep (se 2 (by rfl) ⟨1233393, by rfl⟩ : syracuseStep 3289049 = 2466787) B2466787
theorem B1462251 : Blo 1461050 1462251 := bstep (se 1 (by rfl) ⟨1096688, by rfl⟩ : syracuseStep 1462251 = 2193377) B2193377
theorem B1462263 : Blo 1461050 1462263 := bstep (se 1 (by rfl) ⟨1096697, by rfl⟩ : syracuseStep 1462263 = 2193395) B2193395
theorem B2633729 : Blo 1461050 2633729 := bstep (se 2 (by rfl) ⟨987648, by rfl⟩ : syracuseStep 2633729 = 1975297) B1975297
theorem B1462283 : Blo 1461050 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B1462295 : Blo 1461050 1462295 := bstep (se 1 (by rfl) ⟨1096721, by rfl⟩ : syracuseStep 1462295 = 2193443) B2193443
theorem B1462315 : Blo 1461050 1462315 := bstep (se 1 (by rfl) ⟨1096736, by rfl⟩ : syracuseStep 1462315 = 2193473) B2193473
theorem B3289139 : Blo 1461050 3289139 := bstep (se 1 (by rfl) ⟨2466854, by rfl⟩ : syracuseStep 3289139 = 4933709) B4933709
theorem B1462327 : Blo 1461050 1462327 := bstep (se 1 (by rfl) ⟨1096745, by rfl⟩ : syracuseStep 1462327 = 2193491) B2193491
theorem B1462347 : Blo 1461050 1462347 := bstep (se 1 (by rfl) ⟨1096760, by rfl⟩ : syracuseStep 1462347 = 2193521) B2193521
theorem B3289175 : Blo 1461050 3289175 := bstep (se 1 (by rfl) ⟨2466881, by rfl⟩ : syracuseStep 3289175 = 4933763) B4933763
theorem B1462359 : Blo 1461050 1462359 := bstep (se 1 (by rfl) ⟨1096769, by rfl⟩ : syracuseStep 1462359 = 2193539) B2193539
theorem B1462379 : Blo 1461050 1462379 := bstep (se 1 (by rfl) ⟨1096784, by rfl⟩ : syracuseStep 1462379 = 2193569) B2193569
theorem B1462391 : Blo 1461050 1462391 := bstep (se 1 (by rfl) ⟨1096793, by rfl⟩ : syracuseStep 1462391 = 2193587) B2193587
theorem B1462411 : Blo 1461050 1462411 := bstep (se 1 (by rfl) ⟨1096808, by rfl⟩ : syracuseStep 1462411 = 2193617) B2193617
theorem B6246551 : Blo 1461050 6246551 := bstep (se 1 (by rfl) ⟨4684913, by rfl⟩ : syracuseStep 6246551 = 9369827) B9369827
theorem B1462423 : Blo 1461050 1462423 := bstep (se 1 (by rfl) ⟨1096817, by rfl⟩ : syracuseStep 1462423 = 2193635) B2193635
theorem B1462443 : Blo 1461050 1462443 := bstep (se 1 (by rfl) ⟨1096832, by rfl⟩ : syracuseStep 1462443 = 2193665) B2193665
theorem B28487861 : Blo 1461050 28487861 := bstep (se 5 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 28487861 = 2670737) B2670737
theorem B1462455 : Blo 1461050 1462455 := bstep (se 1 (by rfl) ⟨1096841, by rfl⟩ : syracuseStep 1462455 = 2193683) B2193683
theorem B1462475 : Blo 1461050 1462475 := bstep (se 1 (by rfl) ⟨1096856, by rfl⟩ : syracuseStep 1462475 = 2193713) B2193713
theorem B1462487 : Blo 1461050 1462487 := bstep (se 1 (by rfl) ⟨1096865, by rfl⟩ : syracuseStep 1462487 = 2193731) B2193731
theorem B2191577 : Blo 1461050 2191577 := bstep (se 2 (by rfl) ⟨821841, by rfl⟩ : syracuseStep 2191577 = 1643683) B1643683
theorem B3698905 : Blo 1461050 3698905 := bstep (se 2 (by rfl) ⟨1387089, by rfl⟩ : syracuseStep 3698905 = 2774179) B2774179
theorem B1462507 : Blo 1461050 1462507 := bstep (se 1 (by rfl) ⟨1096880, by rfl⟩ : syracuseStep 1462507 = 2193761) B2193761
theorem B1462519 : Blo 1461050 1462519 := bstep (se 1 (by rfl) ⟨1096889, by rfl⟩ : syracuseStep 1462519 = 2193779) B2193779
theorem B3289355 : Blo 1461050 3289355 := bstep (se 1 (by rfl) ⟨2467016, by rfl⟩ : syracuseStep 3289355 = 4934033) B4934033
theorem B1462539 : Blo 1461050 1462539 := bstep (se 1 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 1462539 = 2193809) B2193809
theorem B3289409 : Blo 1461050 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B2191691 : Blo 1461050 2191691 := bstep (se 1 (by rfl) ⟨1643768, by rfl⟩ : syracuseStep 2191691 = 3287537) B3287537
theorem B2191703 : Blo 1461050 2191703 := bstep (se 1 (by rfl) ⟨1643777, by rfl⟩ : syracuseStep 2191703 = 3287555) B3287555
theorem B11104613 : Blo 1461050 11104613 := bstep (se 4 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 11104613 = 2082115) B2082115
theorem B2191769 : Blo 1461050 2191769 := bstep (se 2 (by rfl) ⟨821913, by rfl⟩ : syracuseStep 2191769 = 1643827) B1643827
theorem B12489137 : Blo 1461050 12489137 := bstep (se 2 (by rfl) ⟨4683426, by rfl⟩ : syracuseStep 12489137 = 9366853) B9366853
theorem B5550515 : Blo 1461050 5550515 := bstep (se 1 (by rfl) ⟨4162886, by rfl⟩ : syracuseStep 5550515 = 8325773) B8325773
theorem B2814401 : Blo 1461050 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B2191883 : Blo 1461050 2191883 := bstep (se 1 (by rfl) ⟨1643912, by rfl⟩ : syracuseStep 2191883 = 3287825) B3287825
theorem B2191895 : Blo 1461050 2191895 := bstep (se 1 (by rfl) ⟨1643921, by rfl⟩ : syracuseStep 2191895 = 3287843) B3287843
theorem B3289625 : Blo 1461050 3289625 := bstep (se 2 (by rfl) ⟨1233609, by rfl⟩ : syracuseStep 3289625 = 2467219) B2467219
theorem B5624365 : Blo 1461050 5624365 := bstep (se 3 (by rfl) ⟨1054568, by rfl⟩ : syracuseStep 5624365 = 2109137) B2109137
theorem B3379763 : Blo 1461050 3379763 := bstep (se 1 (by rfl) ⟨2534822, by rfl⟩ : syracuseStep 3379763 = 5069645) B5069645
theorem B2191961 : Blo 1461050 2191961 := bstep (se 2 (by rfl) ⟨821985, by rfl⟩ : syracuseStep 2191961 = 1643971) B1643971
theorem B3289715 : Blo 1461050 3289715 := bstep (se 1 (by rfl) ⟨2467286, by rfl⟩ : syracuseStep 3289715 = 4934573) B4934573
theorem B3289751 : Blo 1461050 3289751 := bstep (se 1 (by rfl) ⟨2467313, by rfl⟩ : syracuseStep 3289751 = 4934627) B4934627
theorem B2192075 : Blo 1461050 2192075 := bstep (se 1 (by rfl) ⟨1644056, by rfl⟩ : syracuseStep 2192075 = 3288113) B3288113
theorem B2192087 : Blo 1461050 2192087 := bstep (se 1 (by rfl) ⟨1644065, by rfl⟩ : syracuseStep 2192087 = 3288131) B3288131
theorem B11096837 : Blo 1461050 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B2192153 : Blo 1461050 2192153 := bstep (se 2 (by rfl) ⟨822057, by rfl⟩ : syracuseStep 2192153 = 1644115) B1644115
theorem B3289931 : Blo 1461050 3289931 := bstep (se 1 (by rfl) ⟨2467448, by rfl⟩ : syracuseStep 3289931 = 4934897) B4934897
theorem B11105099 : Blo 1461050 11105099 := bstep (se 1 (by rfl) ⟨8328824, by rfl⟩ : syracuseStep 11105099 = 16657649) B16657649
theorem B40555363 : Blo 1461050 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B3289985 : Blo 1461050 3289985 := bstep (se 2 (by rfl) ⟨1233744, by rfl⟩ : syracuseStep 3289985 = 2467489) B2467489
theorem B2192267 : Blo 1461050 2192267 := bstep (se 1 (by rfl) ⟨1644200, by rfl⟩ : syracuseStep 2192267 = 3288401) B3288401
theorem B2192279 : Blo 1461050 2192279 := bstep (se 1 (by rfl) ⟨1644209, by rfl⟩ : syracuseStep 2192279 = 3288419) B3288419
theorem B2192345 : Blo 1461050 2192345 := bstep (se 2 (by rfl) ⟨822129, by rfl⟩ : syracuseStep 2192345 = 1644259) B1644259
theorem B2774027 : Blo 1461050 2774027 := bstep (se 1 (by rfl) ⟨2080520, by rfl⟩ : syracuseStep 2774027 = 4161041) B4161041
theorem B8434705 : Blo 1461050 8434705 := bstep (se 2 (by rfl) ⟨3163014, by rfl⟩ : syracuseStep 8434705 = 6326029) B6326029
theorem B2774081 : Blo 1461050 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B8328257 : Blo 1461050 8328257 := bstep (se 2 (by rfl) ⟨3123096, by rfl⟩ : syracuseStep 8328257 = 6246193) B6246193
theorem B2192459 : Blo 1461050 2192459 := bstep (se 1 (by rfl) ⟨1644344, by rfl⟩ : syracuseStep 2192459 = 3288689) B3288689
theorem B2192471 : Blo 1461050 2192471 := bstep (se 1 (by rfl) ⟨1644353, by rfl⟩ : syracuseStep 2192471 = 3288707) B3288707
theorem B3290201 : Blo 1461050 3290201 := bstep (se 2 (by rfl) ⟨1233825, by rfl⟩ : syracuseStep 3290201 = 2467651) B2467651
theorem B12489821 : Blo 1461050 12489821 := bstep (se 3 (by rfl) ⟨2341841, by rfl⟩ : syracuseStep 12489821 = 4683683) B4683683
theorem B7402589 : Blo 1461050 7402589 := bstep (se 3 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 7402589 = 2775971) B2775971
theorem B2192537 : Blo 1461050 2192537 := bstep (se 2 (by rfl) ⟨822201, by rfl⟩ : syracuseStep 2192537 = 1644403) B1644403
theorem B2634905 : Blo 1461050 2634905 := bstep (se 2 (by rfl) ⟨988089, by rfl⟩ : syracuseStep 2634905 = 1976179) B1976179
theorem B3290291 : Blo 1461050 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B3290327 : Blo 1461050 3290327 := bstep (se 1 (by rfl) ⟨2467745, by rfl⟩ : syracuseStep 3290327 = 4935491) B4935491
theorem B1643755 : Blo 1461050 1643755 := bstep (se 1 (by rfl) ⟨1232816, by rfl⟩ : syracuseStep 1643755 = 2465633) B2465633
theorem B2192651 : Blo 1461050 2192651 := bstep (se 1 (by rfl) ⟨1644488, by rfl⟩ : syracuseStep 2192651 = 3288977) B3288977
theorem B2192663 : Blo 1461050 2192663 := bstep (se 1 (by rfl) ⟨1644497, by rfl⟩ : syracuseStep 2192663 = 3288995) B3288995
theorem B3700019 : Blo 1461050 3700019 := bstep (se 1 (by rfl) ⟨2775014, by rfl⟩ : syracuseStep 3700019 = 5550029) B5550029
theorem B1643863 : Blo 1461050 1643863 := bstep (se 1 (by rfl) ⟨1232897, by rfl⟩ : syracuseStep 1643863 = 2465795) B2465795
theorem B2192729 : Blo 1461050 2192729 := bstep (se 2 (by rfl) ⟨822273, by rfl⟩ : syracuseStep 2192729 = 1644547) B1644547
theorem B3290507 : Blo 1461050 3290507 := bstep (se 1 (by rfl) ⟨2467880, by rfl⟩ : syracuseStep 3290507 = 4935761) B4935761
theorem B3208627 : Blo 1461050 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B3511745 : Blo 1461050 3511745 := bstep (se 2 (by rfl) ⟨1316904, by rfl⟩ : syracuseStep 3511745 = 2633809) B2633809
theorem B3290561 : Blo 1461050 3290561 := bstep (se 2 (by rfl) ⟨1233960, by rfl⟩ : syracuseStep 3290561 = 2467921) B2467921
theorem B2192843 : Blo 1461050 2192843 := bstep (se 1 (by rfl) ⟨1644632, by rfl⟩ : syracuseStep 2192843 = 3289265) B3289265
theorem B2192855 : Blo 1461050 2192855 := bstep (se 1 (by rfl) ⟨1644641, by rfl⟩ : syracuseStep 2192855 = 3289283) B3289283
theorem B1644043 : Blo 1461050 1644043 := bstep (se 1 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 1644043 = 2466065) B2466065
theorem B2192921 : Blo 1461050 2192921 := bstep (se 2 (by rfl) ⟨822345, by rfl⟩ : syracuseStep 2192921 = 1644691) B1644691
theorem B3700313 : Blo 1461050 3700313 := bstep (se 2 (by rfl) ⟨1387617, by rfl⟩ : syracuseStep 3700313 = 2775235) B2775235
theorem B1644151 : Blo 1461050 1644151 := bstep (se 1 (by rfl) ⟨1233113, by rfl⟩ : syracuseStep 1644151 = 2466227) B2466227
theorem B2193035 : Blo 1461050 2193035 := bstep (se 1 (by rfl) ⟨1644776, by rfl⟩ : syracuseStep 2193035 = 3289553) B3289553
theorem B4683415 : Blo 1461050 4683415 := bstep (se 1 (by rfl) ⟨3512561, by rfl⟩ : syracuseStep 4683415 = 7025123) B7025123
theorem B2193047 : Blo 1461050 2193047 := bstep (se 1 (by rfl) ⟨1644785, by rfl⟩ : syracuseStep 2193047 = 3289571) B3289571
theorem B2193113 : Blo 1461050 2193113 := bstep (se 2 (by rfl) ⟨822417, by rfl⟩ : syracuseStep 2193113 = 1644835) B1644835
theorem B4445975 : Blo 1461050 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B1644331 : Blo 1461050 1644331 := bstep (se 1 (by rfl) ⟨1233248, by rfl⟩ : syracuseStep 1644331 = 2466497) B2466497
theorem B2193227 : Blo 1461050 2193227 := bstep (se 1 (by rfl) ⟨1644920, by rfl⟩ : syracuseStep 2193227 = 3289841) B3289841
theorem B2193239 : Blo 1461050 2193239 := bstep (se 1 (by rfl) ⟨1644929, by rfl⟩ : syracuseStep 2193239 = 3289859) B3289859
theorem B5552003 : Blo 1461050 5552003 := bstep (se 1 (by rfl) ⟨4164002, by rfl⟩ : syracuseStep 5552003 = 8328005) B8328005
theorem B1644439 : Blo 1461050 1644439 := bstep (se 1 (by rfl) ⟨1233329, by rfl⟩ : syracuseStep 1644439 = 2466659) B2466659
theorem B2193305 : Blo 1461050 2193305 := bstep (se 2 (by rfl) ⟨822489, by rfl⟩ : syracuseStep 2193305 = 1644979) B1644979
theorem B2774999 : Blo 1461050 2774999 := bstep (se 1 (by rfl) ⟨2081249, by rfl⟩ : syracuseStep 2774999 = 4162499) B4162499
theorem B2193419 : Blo 1461050 2193419 := bstep (se 1 (by rfl) ⟨1645064, by rfl⟩ : syracuseStep 2193419 = 3290129) B3290129
theorem B2193431 : Blo 1461050 2193431 := bstep (se 1 (by rfl) ⟨1645073, by rfl⟩ : syracuseStep 2193431 = 3290147) B3290147
theorem B1644619 : Blo 1461050 1644619 := bstep (se 1 (by rfl) ⟨1233464, by rfl⟩ : syracuseStep 1644619 = 2466929) B2466929
theorem B2193497 : Blo 1461050 2193497 := bstep (se 2 (by rfl) ⟨822561, by rfl⟩ : syracuseStep 2193497 = 1645123) B1645123
theorem B9369701 : Blo 1461050 9369701 := bstep (se 4 (by rfl) ⟨878409, by rfl⟩ : syracuseStep 9369701 = 1756819) B1756819
theorem B15005827 : Blo 1461050 15005827 := bstep (se 1 (by rfl) ⟨11254370, by rfl⟩ : syracuseStep 15005827 = 22508741) B22508741
theorem B1849483 : Blo 1461050 1849483 := bstep (se 1 (by rfl) ⟨1387112, by rfl⟩ : syracuseStep 1849483 = 2774225) B2774225
theorem B3332249 : Blo 1461050 3332249 := bstep (se 2 (by rfl) ⟨1249593, by rfl⟩ : syracuseStep 3332249 = 2499187) B2499187
theorem B1644727 : Blo 1461050 1644727 := bstep (se 1 (by rfl) ⟨1233545, by rfl⟩ : syracuseStep 1644727 = 2467091) B2467091
theorem B2193611 : Blo 1461050 2193611 := bstep (se 1 (by rfl) ⟨1645208, by rfl⟩ : syracuseStep 2193611 = 3290417) B3290417
theorem B2193623 : Blo 1461050 2193623 := bstep (se 1 (by rfl) ⟨1645217, by rfl⟩ : syracuseStep 2193623 = 3290435) B3290435
theorem B2193689 : Blo 1461050 2193689 := bstep (se 2 (by rfl) ⟨822633, by rfl⟩ : syracuseStep 2193689 = 1645267) B1645267
theorem B5552459 : Blo 1461050 5552459 := bstep (se 1 (by rfl) ⟨4164344, by rfl⟩ : syracuseStep 5552459 = 8328689) B8328689
theorem B1644907 : Blo 1461050 1644907 := bstep (se 1 (by rfl) ⟨1233680, by rfl⟩ : syracuseStep 1644907 = 2467361) B2467361
theorem B2193803 : Blo 1461050 2193803 := bstep (se 1 (by rfl) ⟨1645352, by rfl⟩ : syracuseStep 2193803 = 3290705) B3290705
theorem B2193815 : Blo 1461050 2193815 := bstep (se 1 (by rfl) ⟨1645361, by rfl⟩ : syracuseStep 2193815 = 3290723) B3290723
theorem B1645015 : Blo 1461050 1645015 := bstep (se 1 (by rfl) ⟨1233761, by rfl⟩ : syracuseStep 1645015 = 2467523) B2467523
theorem B2775539 : Blo 1461050 2775539 := bstep (se 1 (by rfl) ⟨2081654, by rfl⟩ : syracuseStep 2775539 = 4163309) B4163309
theorem B126482957 : Blo 1461050 126482957 := bstep (se 3 (by rfl) ⟨23715554, by rfl⟩ : syracuseStep 126482957 = 47431109) B47431109
theorem B5552657 : Blo 1461050 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B9370187 : Blo 1461050 9370187 := bstep (se 1 (by rfl) ⟨7027640, by rfl⟩ : syracuseStep 9370187 = 14055281) B14055281
theorem B1645195 : Blo 1461050 1645195 := bstep (se 1 (by rfl) ⟨1233896, by rfl⟩ : syracuseStep 1645195 = 2467793) B2467793
theorem B9362137 : Blo 1461050 9362137 := bstep (se 2 (by rfl) ⟨3510801, by rfl⟩ : syracuseStep 9362137 = 7021603) B7021603
theorem B1645303 : Blo 1461050 1645303 := bstep (se 1 (by rfl) ⟨1233977, by rfl⟩ : syracuseStep 1645303 = 2467955) B2467955
theorem B3521369 : Blo 1461050 3521369 := bstep (se 2 (by rfl) ⟨1320513, by rfl⟩ : syracuseStep 3521369 = 2641027) B2641027
theorem B2776025 : Blo 1461050 2776025 := bstep (se 2 (by rfl) ⟨1041009, by rfl⟩ : syracuseStep 2776025 = 2082019) B2082019
theorem B3333143 : Blo 1461050 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B5626955 : Blo 1461050 5626955 := bstep (se 1 (by rfl) ⟨4220216, by rfl⟩ : syracuseStep 5626955 = 8440433) B8440433
theorem B1850455 : Blo 1461050 1850455 := bstep (se 1 (by rfl) ⟨1387841, by rfl⟩ : syracuseStep 1850455 = 2775683) B2775683
theorem B10001501 : Blo 1461050 10001501 := bstep (se 3 (by rfl) ⟨1875281, by rfl⟩ : syracuseStep 10001501 = 3750563) B3750563
theorem B1522795 : Blo 1461050 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B11099267 : Blo 1461050 11099267 := bstep (se 1 (by rfl) ⟨8324450, by rfl⟩ : syracuseStep 11099267 = 16648901) B16648901
theorem B3701963 : Blo 1461050 3701963 := bstep (se 1 (by rfl) ⟨2776472, by rfl⟩ : syracuseStep 3701963 = 5552945) B5552945
theorem B7027985 : Blo 1461050 7027985 := bstep (se 2 (by rfl) ⟨2635494, by rfl⟩ : syracuseStep 7027985 = 5270989) B5270989
theorem B8117549 : Blo 1461050 8117549 := bstep (se 3 (by rfl) ⟨1522040, by rfl⟩ : syracuseStep 8117549 = 3044081) B3044081
theorem B3751219 : Blo 1461050 3751219 := bstep (se 1 (by rfl) ⟨2813414, by rfl⟩ : syracuseStep 3751219 = 5626829) B5626829
theorem B9362753 : Blo 1461050 9362753 := bstep (se 2 (by rfl) ⟨3511032, by rfl⟩ : syracuseStep 9362753 = 7022065) B7022065
theorem B4685273 : Blo 1461050 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B10821185 : Blo 1461050 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B7397081 : Blo 1461050 7397081 := bstep (se 2 (by rfl) ⟨2773905, by rfl⟩ : syracuseStep 7397081 = 5547811) B5547811
theorem B3333899 : Blo 1461050 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B6242093 : Blo 1461050 6242093 := bstep (se 3 (by rfl) ⟨1170392, by rfl⟩ : syracuseStep 6242093 = 2340785) B2340785
theorem B2465687 : Blo 1461050 2465687 := bstep (se 1 (by rfl) ⟨1849265, by rfl⟩ : syracuseStep 2465687 = 3698531) B3698531
theorem B4931549 : Blo 1461050 4931549 := bstep (se 3 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 4931549 = 1849331) B1849331
theorem B7397405 : Blo 1461050 7397405 := bstep (se 3 (by rfl) ⟨1387013, by rfl⟩ : syracuseStep 7397405 = 2774027) B2774027
theorem B2465977 : Blo 1461050 2465977 := bstep (se 2 (by rfl) ⟨924741, by rfl⟩ : syracuseStep 2465977 = 1849483) B1849483
theorem B4161793 : Blo 1461050 4161793 := bstep (se 2 (by rfl) ⟨1560672, by rfl⟩ : syracuseStep 4161793 = 3121345) B3121345
theorem B4931873 : Blo 1461050 4931873 := bstep (se 2 (by rfl) ⟨1849452, by rfl⟩ : syracuseStep 4931873 = 3698905) B3698905
theorem B1876267 : Blo 1461050 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B4161851 : Blo 1461050 4161851 := bstep (se 1 (by rfl) ⟨3121388, by rfl⟩ : syracuseStep 4161851 = 6242777) B6242777
theorem B4219337 : Blo 1461050 4219337 := bstep (se 2 (by rfl) ⟨1582251, by rfl⟩ : syracuseStep 4219337 = 3164503) B3164503
theorem B7397891 : Blo 1461050 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B4932467 : Blo 1461050 4932467 := bstep (se 1 (by rfl) ⟨3699350, by rfl⟩ : syracuseStep 4932467 = 7398701) B7398701
theorem B2466679 : Blo 1461050 2466679 := bstep (se 1 (by rfl) ⟨1850009, by rfl⟩ : syracuseStep 2466679 = 3700019) B3700019
theorem B2466875 : Blo 1461050 2466875 := bstep (se 1 (by rfl) ⟨1850156, by rfl⟩ : syracuseStep 2466875 = 3700313) B3700313
theorem B56935811 : Blo 1461050 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B14050745 : Blo 1461050 14050745 := bstep (se 2 (by rfl) ⟨5269029, by rfl⟩ : syracuseStep 14050745 = 10538059) B10538059
theorem B2221499 : Blo 1461050 2221499 := bstep (se 1 (by rfl) ⟨1666124, by rfl⟩ : syracuseStep 2221499 = 3332249) B3332249
theorem B2467273 : Blo 1461050 2467273 := bstep (se 2 (by rfl) ⟨925227, by rfl⟩ : syracuseStep 2467273 = 1850455) B1850455
theorem B9012701 : Blo 1461050 9012701 := bstep (se 3 (by rfl) ⟨1689881, by rfl⟩ : syracuseStep 9012701 = 3379763) B3379763
theorem B84321971 : Blo 1461050 84321971 := bstep (se 1 (by rfl) ⟨63241478, by rfl⟩ : syracuseStep 84321971 = 126482957) B126482957
theorem B2221753 : Blo 1461050 2221753 := bstep (se 2 (by rfl) ⟨833157, by rfl⟩ : syracuseStep 2221753 = 1666315) B1666315
theorem B4278169 : Blo 1461050 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B2222095 : Blo 1461050 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B8890397 : Blo 1461050 8890397 := bstep (se 3 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 8890397 = 3333899) B3333899
theorem B2811937 : Blo 1461050 2811937 := bstep (se 2 (by rfl) ⟨1054476, by rfl⟩ : syracuseStep 2811937 = 2108953) B2108953
theorem B11855933 : Blo 1461050 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B7399511 : Blo 1461050 7399511 := bstep (se 1 (by rfl) ⟨5549633, by rfl⟩ : syracuseStep 7399511 = 11099267) B11099267
theorem B2467975 : Blo 1461050 2467975 := bstep (se 1 (by rfl) ⟨1850981, by rfl⟩ : syracuseStep 2467975 = 3701963) B3701963
theorem B6244553 : Blo 1461050 6244553 := bstep (se 2 (by rfl) ⟨2341707, by rfl⟩ : syracuseStep 6244553 = 4683415) B4683415
theorem B3123515 : Blo 1461050 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B4164139 : Blo 1461050 4164139 := bstep (se 1 (by rfl) ⟨3123104, by rfl⟩ : syracuseStep 4164139 = 6246209) B6246209
theorem B7399997 : Blo 1461050 7399997 := bstep (se 3 (by rfl) ⟨1387499, by rfl⟩ : syracuseStep 7399997 = 2774999) B2774999
theorem B3287699 : Blo 1461050 3287699 := bstep (se 1 (by rfl) ⟨2465774, by rfl⟩ : syracuseStep 3287699 = 4931549) B4931549
theorem B7023277 : Blo 1461050 7023277 := bstep (se 3 (by rfl) ⟨1316864, by rfl⟩ : syracuseStep 7023277 = 2633729) B2633729
theorem B3287753 : Blo 1461050 3287753 := bstep (se 2 (by rfl) ⟨1232907, by rfl⟩ : syracuseStep 3287753 = 2465815) B2465815
theorem B4164367 : Blo 1461050 4164367 := bstep (se 1 (by rfl) ⟨3123275, by rfl⟩ : syracuseStep 4164367 = 6246551) B6246551
theorem B18991907 : Blo 1461050 18991907 := bstep (se 1 (by rfl) ⟨14243930, by rfl⟩ : syracuseStep 18991907 = 28487861) B28487861
theorem B1461051 : Blo 1461050 1461051 := bstep (se 1 (by rfl) ⟨1095788, by rfl⟩ : syracuseStep 1461051 = 2191577) B2191577
theorem B7023449 : Blo 1461050 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B11250521 : Blo 1461050 11250521 := bstep (se 2 (by rfl) ⟨4218945, by rfl⟩ : syracuseStep 11250521 = 8437891) B8437891
theorem B1461127 : Blo 1461050 1461127 := bstep (se 1 (by rfl) ⟨1095845, by rfl⟩ : syracuseStep 1461127 = 2191691) B2191691
theorem B1461135 : Blo 1461050 1461135 := bstep (se 1 (by rfl) ⟨1095851, by rfl⟩ : syracuseStep 1461135 = 2191703) B2191703
theorem B1461179 : Blo 1461050 1461179 := bstep (se 1 (by rfl) ⟨1095884, by rfl⟩ : syracuseStep 1461179 = 2191769) B2191769
theorem B8326091 : Blo 1461050 8326091 := bstep (se 1 (by rfl) ⟨6244568, by rfl⟩ : syracuseStep 8326091 = 12489137) B12489137
theorem B1461255 : Blo 1461050 1461255 := bstep (se 1 (by rfl) ⟨1095941, by rfl⟩ : syracuseStep 1461255 = 2191883) B2191883
theorem B1461263 : Blo 1461050 1461263 := bstep (se 1 (by rfl) ⟨1095947, by rfl⟩ : syracuseStep 1461263 = 2191895) B2191895
theorem B4164641 : Blo 1461050 4164641 := bstep (se 2 (by rfl) ⟨1561740, by rfl⟩ : syracuseStep 4164641 = 3123481) B3123481
theorem B1461307 : Blo 1461050 1461307 := bstep (se 1 (by rfl) ⟨1095980, by rfl⟩ : syracuseStep 1461307 = 2191961) B2191961
theorem B1461383 : Blo 1461050 1461383 := bstep (se 1 (by rfl) ⟨1096037, by rfl⟩ : syracuseStep 1461383 = 2192075) B2192075
theorem B1461391 : Blo 1461050 1461391 := bstep (se 1 (by rfl) ⟨1096043, by rfl⟩ : syracuseStep 1461391 = 2192087) B2192087
theorem B1461435 : Blo 1461050 1461435 := bstep (se 1 (by rfl) ⟨1096076, by rfl⟩ : syracuseStep 1461435 = 2192153) B2192153
theorem B1461511 : Blo 1461050 1461511 := bstep (se 1 (by rfl) ⟨1096133, by rfl⟩ : syracuseStep 1461511 = 2192267) B2192267
theorem B1461519 : Blo 1461050 1461519 := bstep (se 1 (by rfl) ⟨1096139, by rfl⟩ : syracuseStep 1461519 = 2192279) B2192279
theorem B23702843 : Blo 1461050 23702843 := bstep (se 1 (by rfl) ⟨17777132, by rfl⟩ : syracuseStep 23702843 = 35554265) B35554265
theorem B1461563 : Blo 1461050 1461563 := bstep (se 1 (by rfl) ⟨1096172, by rfl⟩ : syracuseStep 1461563 = 2192345) B2192345
theorem B80031077 : Blo 1461050 80031077 := bstep (se 4 (by rfl) ⟨7502913, by rfl⟩ : syracuseStep 80031077 = 15005827) B15005827
theorem B3288455 : Blo 1461050 3288455 := bstep (se 1 (by rfl) ⟨2466341, by rfl⟩ : syracuseStep 3288455 = 4932683) B4932683
theorem B1461639 : Blo 1461050 1461639 := bstep (se 1 (by rfl) ⟨1096229, by rfl⟩ : syracuseStep 1461639 = 2192459) B2192459
theorem B1461647 : Blo 1461050 1461647 := bstep (se 1 (by rfl) ⟨1096235, by rfl⟩ : syracuseStep 1461647 = 2192471) B2192471
theorem B7499153 : Blo 1461050 7499153 := bstep (se 2 (by rfl) ⟨2812182, by rfl⟩ : syracuseStep 7499153 = 5624365) B5624365
theorem B8326547 : Blo 1461050 8326547 := bstep (se 1 (by rfl) ⟨6244910, by rfl⟩ : syracuseStep 8326547 = 12489821) B12489821
theorem B4935059 : Blo 1461050 4935059 := bstep (se 1 (by rfl) ⟨3701294, by rfl⟩ : syracuseStep 4935059 = 7402589) B7402589
theorem B1461691 : Blo 1461050 1461691 := bstep (se 1 (by rfl) ⟨1096268, by rfl⟩ : syracuseStep 1461691 = 2192537) B2192537
theorem B1756603 : Blo 1461050 1756603 := bstep (se 1 (by rfl) ⟨1317452, by rfl⟩ : syracuseStep 1756603 = 2634905) B2634905
theorem B1461767 : Blo 1461050 1461767 := bstep (se 1 (by rfl) ⟨1096325, by rfl⟩ : syracuseStep 1461767 = 2192651) B2192651
theorem B1461775 : Blo 1461050 1461775 := bstep (se 1 (by rfl) ⟨1096331, by rfl⟩ : syracuseStep 1461775 = 2192663) B2192663
theorem B3288635 : Blo 1461050 3288635 := bstep (se 1 (by rfl) ⟨2466476, by rfl⟩ : syracuseStep 3288635 = 4932953) B4932953
theorem B1461819 : Blo 1461050 1461819 := bstep (se 1 (by rfl) ⟨1096364, by rfl⟩ : syracuseStep 1461819 = 2192729) B2192729
theorem B1461895 : Blo 1461050 1461895 := bstep (se 1 (by rfl) ⟨1096421, by rfl⟩ : syracuseStep 1461895 = 2192843) B2192843
theorem B1461903 : Blo 1461050 1461903 := bstep (se 1 (by rfl) ⟨1096427, by rfl⟩ : syracuseStep 1461903 = 2192855) B2192855
theorem B3288761 : Blo 1461050 3288761 := bstep (se 2 (by rfl) ⟨1233285, by rfl⟩ : syracuseStep 3288761 = 2466571) B2466571
theorem B1461947 : Blo 1461050 1461947 := bstep (se 1 (by rfl) ⟨1096460, by rfl⟩ : syracuseStep 1461947 = 2192921) B2192921
theorem B150245077 : Blo 1461050 150245077 := bstep (se 7 (by rfl) ⟨1760684, by rfl⟩ : syracuseStep 150245077 = 3521369) B3521369
theorem B1462023 : Blo 1461050 1462023 := bstep (se 1 (by rfl) ⟨1096517, by rfl⟩ : syracuseStep 1462023 = 2193035) B2193035
theorem B1462031 : Blo 1461050 1462031 := bstep (se 1 (by rfl) ⟨1096523, by rfl⟩ : syracuseStep 1462031 = 2193047) B2193047
theorem B1462075 : Blo 1461050 1462075 := bstep (se 1 (by rfl) ⟨1096556, by rfl⟩ : syracuseStep 1462075 = 2193113) B2193113
theorem B1462151 : Blo 1461050 1462151 := bstep (se 1 (by rfl) ⟨1096613, by rfl⟩ : syracuseStep 1462151 = 2193227) B2193227
theorem B1462159 : Blo 1461050 1462159 := bstep (se 1 (by rfl) ⟨1096619, by rfl⟩ : syracuseStep 1462159 = 2193239) B2193239
theorem B1462203 : Blo 1461050 1462203 := bstep (se 1 (by rfl) ⟨1096652, by rfl⟩ : syracuseStep 1462203 = 2193305) B2193305
theorem B1462279 : Blo 1461050 1462279 := bstep (se 1 (by rfl) ⟨1096709, by rfl⟩ : syracuseStep 1462279 = 2193419) B2193419
theorem B3289103 : Blo 1461050 3289103 := bstep (se 1 (by rfl) ⟨2466827, by rfl⟩ : syracuseStep 3289103 = 4933655) B4933655
theorem B1462287 : Blo 1461050 1462287 := bstep (se 1 (by rfl) ⟨1096715, by rfl⟩ : syracuseStep 1462287 = 2193431) B2193431
theorem B3289121 : Blo 1461050 3289121 := bstep (se 2 (by rfl) ⟨1233420, by rfl⟩ : syracuseStep 3289121 = 2466841) B2466841
theorem B1462331 : Blo 1461050 1462331 := bstep (se 1 (by rfl) ⟨1096748, by rfl⟩ : syracuseStep 1462331 = 2193497) B2193497
theorem B6246467 : Blo 1461050 6246467 := bstep (se 1 (by rfl) ⟨4684850, by rfl⟩ : syracuseStep 6246467 = 9369701) B9369701
theorem B1462407 : Blo 1461050 1462407 := bstep (se 1 (by rfl) ⟨1096805, by rfl⟩ : syracuseStep 1462407 = 2193611) B2193611
theorem B1462415 : Blo 1461050 1462415 := bstep (se 1 (by rfl) ⟨1096811, by rfl⟩ : syracuseStep 1462415 = 2193623) B2193623
theorem B1462459 : Blo 1461050 1462459 := bstep (se 1 (by rfl) ⟨1096844, by rfl⟩ : syracuseStep 1462459 = 2193689) B2193689
theorem B34214089 : Blo 1461050 34214089 := bstep (se 2 (by rfl) ⟨12830283, by rfl⟩ : syracuseStep 34214089 = 25660567) B25660567
theorem B2191607 : Blo 1461050 2191607 := bstep (se 1 (by rfl) ⟨1643705, by rfl⟩ : syracuseStep 2191607 = 3287411) B3287411
theorem B1462535 : Blo 1461050 1462535 := bstep (se 1 (by rfl) ⟨1096901, by rfl⟩ : syracuseStep 1462535 = 2193803) B2193803
theorem B2191631 : Blo 1461050 2191631 := bstep (se 1 (by rfl) ⟨1643723, by rfl⟩ : syracuseStep 2191631 = 3287447) B3287447
theorem B1462543 : Blo 1461050 1462543 := bstep (se 1 (by rfl) ⟨1096907, by rfl⟩ : syracuseStep 1462543 = 2193815) B2193815
theorem B2109739 : Blo 1461050 2109739 := bstep (se 1 (by rfl) ⟨1582304, by rfl⟩ : syracuseStep 2109739 = 3164609) B3164609
theorem B7401779 : Blo 1461050 7401779 := bstep (se 1 (by rfl) ⟨5551334, by rfl⟩ : syracuseStep 7401779 = 11102669) B11102669
theorem B2191673 : Blo 1461050 2191673 := bstep (se 2 (by rfl) ⟨821877, by rfl⟩ : syracuseStep 2191673 = 1643755) B1643755
theorem B3289463 : Blo 1461050 3289463 := bstep (se 1 (by rfl) ⟨2467097, by rfl⟩ : syracuseStep 3289463 = 4934195) B4934195
theorem B2191751 : Blo 1461050 2191751 := bstep (se 1 (by rfl) ⟨1643813, by rfl⟩ : syracuseStep 2191751 = 3287627) B3287627
theorem B6246791 : Blo 1461050 6246791 := bstep (se 1 (by rfl) ⟨4685093, by rfl⟩ : syracuseStep 6246791 = 9370187) B9370187
theorem B5001625 : Blo 1461050 5001625 := bstep (se 2 (by rfl) ⟨1875609, by rfl⟩ : syracuseStep 5001625 = 3751219) B3751219
theorem B2191787 : Blo 1461050 2191787 := bstep (se 1 (by rfl) ⟨1643840, by rfl⟩ : syracuseStep 2191787 = 3287681) B3287681
theorem B2191817 : Blo 1461050 2191817 := bstep (se 2 (by rfl) ⟨821931, by rfl⟩ : syracuseStep 2191817 = 1643863) B1643863
theorem B5550545 : Blo 1461050 5550545 := bstep (se 2 (by rfl) ⟨2081454, by rfl⟩ : syracuseStep 5550545 = 4162909) B4162909
theorem B13332995 : Blo 1461050 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B3289643 : Blo 1461050 3289643 := bstep (se 1 (by rfl) ⟨2467232, by rfl⟩ : syracuseStep 3289643 = 4934465) B4934465
theorem B2191931 : Blo 1461050 2191931 := bstep (se 1 (by rfl) ⟨1643948, by rfl⟩ : syracuseStep 2191931 = 3287897) B3287897
theorem B2191991 : Blo 1461050 2191991 := bstep (se 1 (by rfl) ⟨1643993, by rfl⟩ : syracuseStep 2191991 = 3287987) B3287987
theorem B7402103 : Blo 1461050 7402103 := bstep (se 1 (by rfl) ⟨5551577, by rfl⟩ : syracuseStep 7402103 = 11103155) B11103155
theorem B2192015 : Blo 1461050 2192015 := bstep (se 1 (by rfl) ⟨1644011, by rfl⟩ : syracuseStep 2192015 = 3288023) B3288023
theorem B2192057 : Blo 1461050 2192057 := bstep (se 2 (by rfl) ⟨822021, by rfl⟩ : syracuseStep 2192057 = 1644043) B1644043
theorem B2192135 : Blo 1461050 2192135 := bstep (se 1 (by rfl) ⟨1644101, by rfl⟩ : syracuseStep 2192135 = 3288203) B3288203
theorem B2192171 : Blo 1461050 2192171 := bstep (se 1 (by rfl) ⟨1644128, by rfl⟩ : syracuseStep 2192171 = 3288257) B3288257
theorem B2192201 : Blo 1461050 2192201 := bstep (se 2 (by rfl) ⟨822075, by rfl⟩ : syracuseStep 2192201 = 1644151) B1644151
theorem B5411699 : Blo 1461050 5411699 := bstep (se 1 (by rfl) ⟨4058774, by rfl⟩ : syracuseStep 5411699 = 8117549) B8117549
theorem B3290003 : Blo 1461050 3290003 := bstep (se 1 (by rfl) ⟨2467502, by rfl⟩ : syracuseStep 3290003 = 4935005) B4935005
theorem B5551001 : Blo 1461050 5551001 := bstep (se 2 (by rfl) ⟨2081625, by rfl⟩ : syracuseStep 5551001 = 4163251) B4163251
theorem B3511225 : Blo 1461050 3511225 := bstep (se 2 (by rfl) ⟨1316709, by rfl⟩ : syracuseStep 3511225 = 2633419) B2633419
theorem B2192315 : Blo 1461050 2192315 := bstep (se 1 (by rfl) ⟨1644236, by rfl⟩ : syracuseStep 2192315 = 3288473) B3288473
theorem B3290057 : Blo 1461050 3290057 := bstep (se 2 (by rfl) ⟨1233771, by rfl⟩ : syracuseStep 3290057 = 2467543) B2467543
theorem B2192375 : Blo 1461050 2192375 := bstep (se 1 (by rfl) ⟨1644281, by rfl⟩ : syracuseStep 2192375 = 3288563) B3288563
theorem B2192399 : Blo 1461050 2192399 := bstep (se 1 (by rfl) ⟨1644299, by rfl⟩ : syracuseStep 2192399 = 3288599) B3288599
theorem B7214123 : Blo 1461050 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B2192441 : Blo 1461050 2192441 := bstep (se 2 (by rfl) ⟨822165, by rfl⟩ : syracuseStep 2192441 = 1644331) B1644331
theorem B3699827 : Blo 1461050 3699827 := bstep (se 1 (by rfl) ⟨2774870, by rfl⟩ : syracuseStep 3699827 = 5549741) B5549741
theorem B2192519 : Blo 1461050 2192519 := bstep (se 1 (by rfl) ⟨1644389, by rfl⟩ : syracuseStep 2192519 = 3288779) B3288779
theorem B2192555 : Blo 1461050 2192555 := bstep (se 1 (by rfl) ⟨1644416, by rfl⟩ : syracuseStep 2192555 = 3288833) B3288833
theorem B2192585 : Blo 1461050 2192585 := bstep (se 2 (by rfl) ⟨822219, by rfl⟩ : syracuseStep 2192585 = 1644439) B1644439
theorem B1643791 : Blo 1461050 1643791 := bstep (se 1 (by rfl) ⟨1232843, by rfl⟩ : syracuseStep 1643791 = 2465687) B2465687
theorem B2192699 : Blo 1461050 2192699 := bstep (se 1 (by rfl) ⟨1644524, by rfl⟩ : syracuseStep 2192699 = 3289049) B3289049
theorem B2192759 : Blo 1461050 2192759 := bstep (se 1 (by rfl) ⟨1644569, by rfl⟩ : syracuseStep 2192759 = 3289139) B3289139
theorem B2774407 : Blo 1461050 2774407 := bstep (se 1 (by rfl) ⟨2080805, by rfl⟩ : syracuseStep 2774407 = 4161611) B4161611
theorem B3511687 : Blo 1461050 3511687 := bstep (se 1 (by rfl) ⟨2633765, by rfl⟩ : syracuseStep 3511687 = 5267531) B5267531
theorem B2192783 : Blo 1461050 2192783 := bstep (se 1 (by rfl) ⟨1644587, by rfl⟩ : syracuseStep 2192783 = 3289175) B3289175
theorem B2192825 : Blo 1461050 2192825 := bstep (se 2 (by rfl) ⟨822309, by rfl⟩ : syracuseStep 2192825 = 1644619) B1644619
theorem B2635193 : Blo 1461050 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B2192903 : Blo 1461050 2192903 := bstep (se 1 (by rfl) ⟨1644677, by rfl⟩ : syracuseStep 2192903 = 3289355) B3289355
theorem B50615837 : Blo 1461050 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B15005213 : Blo 1461050 15005213 := bstep (se 3 (by rfl) ⟨2813477, by rfl⟩ : syracuseStep 15005213 = 5626955) B5626955
theorem B2192939 : Blo 1461050 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B7501373 : Blo 1461050 7501373 := bstep (se 3 (by rfl) ⟨1406507, by rfl⟩ : syracuseStep 7501373 = 2813015) B2813015
theorem B7403075 : Blo 1461050 7403075 := bstep (se 1 (by rfl) ⟨5552306, by rfl⟩ : syracuseStep 7403075 = 11104613) B11104613
theorem B2192969 : Blo 1461050 2192969 := bstep (se 2 (by rfl) ⟨822363, by rfl⟩ : syracuseStep 2192969 = 1644727) B1644727
theorem B3700343 : Blo 1461050 3700343 := bstep (se 1 (by rfl) ⟨2775257, by rfl⟩ : syracuseStep 3700343 = 5550515) B5550515
theorem B3511955 : Blo 1461050 3511955 := bstep (se 1 (by rfl) ⟨2633966, by rfl⟩ : syracuseStep 3511955 = 5267933) B5267933
theorem B2193083 : Blo 1461050 2193083 := bstep (se 1 (by rfl) ⟨1644812, by rfl⟩ : syracuseStep 2193083 = 3289625) B3289625
theorem B2193143 : Blo 1461050 2193143 := bstep (se 1 (by rfl) ⟨1644857, by rfl⟩ : syracuseStep 2193143 = 3289715) B3289715
theorem B1644295 : Blo 1461050 1644295 := bstep (se 1 (by rfl) ⟨1233221, by rfl⟩ : syracuseStep 1644295 = 2466443) B2466443
theorem B2193167 : Blo 1461050 2193167 := bstep (se 1 (by rfl) ⟨1644875, by rfl⟩ : syracuseStep 2193167 = 3289751) B3289751
theorem B2193209 : Blo 1461050 2193209 := bstep (se 2 (by rfl) ⟨822453, by rfl⟩ : syracuseStep 2193209 = 1644907) B1644907
theorem B2193287 : Blo 1461050 2193287 := bstep (se 1 (by rfl) ⟨1644965, by rfl⟩ : syracuseStep 2193287 = 3289931) B3289931
theorem B7403399 : Blo 1461050 7403399 := bstep (se 1 (by rfl) ⟨5552549, by rfl⟩ : syracuseStep 7403399 = 11105099) B11105099
theorem B2193323 : Blo 1461050 2193323 := bstep (se 1 (by rfl) ⟨1644992, by rfl⟩ : syracuseStep 2193323 = 3289985) B3289985
theorem B2774969 : Blo 1461050 2774969 := bstep (se 2 (by rfl) ⟨1040613, by rfl⟩ : syracuseStep 2774969 = 2081227) B2081227
theorem B1644475 : Blo 1461050 1644475 := bstep (se 1 (by rfl) ⟨1233356, by rfl⟩ : syracuseStep 1644475 = 2466713) B2466713
theorem B2193353 : Blo 1461050 2193353 := bstep (se 2 (by rfl) ⟨822507, by rfl⟩ : syracuseStep 2193353 = 1645015) B1645015
theorem B86751245 : Blo 1461050 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B1849387 : Blo 1461050 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B5552171 : Blo 1461050 5552171 := bstep (se 1 (by rfl) ⟨4164128, by rfl⟩ : syracuseStep 5552171 = 8328257) B8328257
theorem B18741293 : Blo 1461050 18741293 := bstep (se 3 (by rfl) ⟨3513992, by rfl⟩ : syracuseStep 18741293 = 7027985) B7027985
theorem B2193467 : Blo 1461050 2193467 := bstep (se 1 (by rfl) ⟨1645100, by rfl⟩ : syracuseStep 2193467 = 3290201) B3290201
theorem B2193527 : Blo 1461050 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B2193551 : Blo 1461050 2193551 := bstep (se 1 (by rfl) ⟨1645163, by rfl⟩ : syracuseStep 2193551 = 3290327) B3290327
theorem B2193593 : Blo 1461050 2193593 := bstep (se 2 (by rfl) ⟨822597, by rfl⟩ : syracuseStep 2193593 = 1645195) B1645195
theorem B2193671 : Blo 1461050 2193671 := bstep (se 1 (by rfl) ⟨1645253, by rfl⟩ : syracuseStep 2193671 = 3290507) B3290507
theorem B3512591 : Blo 1461050 3512591 := bstep (se 1 (by rfl) ⟨2634443, by rfl⟩ : syracuseStep 3512591 = 5268887) B5268887
theorem B12482849 : Blo 1461050 12482849 := bstep (se 2 (by rfl) ⟨4681068, by rfl⟩ : syracuseStep 12482849 = 9362137) B9362137
theorem B2341163 : Blo 1461050 2341163 := bstep (se 1 (by rfl) ⟨1755872, by rfl⟩ : syracuseStep 2341163 = 3511745) B3511745
theorem B2193707 : Blo 1461050 2193707 := bstep (se 1 (by rfl) ⟨1645280, by rfl⟩ : syracuseStep 2193707 = 3290561) B3290561
theorem B2193737 : Blo 1461050 2193737 := bstep (se 2 (by rfl) ⟨822651, by rfl⟩ : syracuseStep 2193737 = 1645303) B1645303
theorem B1644943 : Blo 1461050 1644943 := bstep (se 1 (by rfl) ⟨1233707, by rfl⟩ : syracuseStep 1644943 = 2467415) B2467415
theorem B54073817 : Blo 1461050 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B4684349 : Blo 1461050 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B3701335 : Blo 1461050 3701335 := bstep (se 1 (by rfl) ⟨2776001, by rfl⟩ : syracuseStep 3701335 = 5552003) B5552003
theorem B11246273 : Blo 1461050 11246273 := bstep (se 2 (by rfl) ⟨4217352, by rfl⟩ : syracuseStep 11246273 = 8434705) B8434705
theorem B25656101 : Blo 1461050 25656101 := bstep (se 4 (by rfl) ⟨2405259, by rfl⟩ : syracuseStep 25656101 = 4810519) B4810519
theorem B2030393 : Blo 1461050 2030393 := bstep (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) B1522795
theorem B3701639 : Blo 1461050 3701639 := bstep (se 1 (by rfl) ⟨2776229, by rfl⟩ : syracuseStep 3701639 = 5552459) B5552459
theorem B1850359 : Blo 1461050 1850359 := bstep (se 1 (by rfl) ⟨1387769, by rfl⟩ : syracuseStep 1850359 = 2775539) B2775539
theorem B3701771 : Blo 1461050 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B2776123 : Blo 1461050 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B35552317 : Blo 1461050 35552317 := bstep (se 3 (by rfl) ⟨6666059, by rfl⟩ : syracuseStep 35552317 = 13332119) B13332119
theorem B2964769 : Blo 1461050 2964769 := bstep (se 2 (by rfl) ⟨1111788, by rfl⟩ : syracuseStep 2964769 = 2223577) B2223577
theorem B1850683 : Blo 1461050 1850683 := bstep (se 1 (by rfl) ⟨1388012, by rfl⟩ : syracuseStep 1850683 = 2776025) B2776025
theorem B6667667 : Blo 1461050 6667667 := bstep (se 1 (by rfl) ⟨5000750, by rfl⟩ : syracuseStep 6667667 = 10001501) B10001501
theorem B6241835 : Blo 1461050 6241835 := bstep (se 1 (by rfl) ⟨4681376, by rfl⟩ : syracuseStep 6241835 = 9362753) B9362753
theorem B2080441 : Blo 1461050 2080441 := bstep (se 2 (by rfl) ⟨780165, by rfl⟩ : syracuseStep 2080441 = 1560331) B1560331
theorem B2342585 : Blo 1461050 2342585 := bstep (se 2 (by rfl) ⟨878469, by rfl⟩ : syracuseStep 2342585 = 1756939) B1756939
theorem B9363215 : Blo 1461050 9363215 := bstep (se 1 (by rfl) ⟨7022411, by rfl⟩ : syracuseStep 9363215 = 14044823) B14044823
theorem B2465579 : Blo 1461050 2465579 := bstep (se 1 (by rfl) ⟨1849184, by rfl⟩ : syracuseStep 2465579 = 3698369) B3698369
theorem B4931387 : Blo 1461050 4931387 := bstep (se 1 (by rfl) ⟨3698540, by rfl⟩ : syracuseStep 4931387 = 7397081) B7397081
theorem B4161395 : Blo 1461050 4161395 := bstep (se 1 (by rfl) ⟨3121046, by rfl⟩ : syracuseStep 4161395 = 6242093) B6242093
theorem B4931603 : Blo 1461050 4931603 := bstep (se 1 (by rfl) ⟨3698702, by rfl⟩ : syracuseStep 4931603 = 7397405) B7397405
theorem B2465849 : Blo 1461050 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B4931927 : Blo 1461050 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B8888663 : Blo 1461050 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B6668833 : Blo 1461050 6668833 := bstep (se 2 (by rfl) ⟨2500812, by rfl⟩ : syracuseStep 6668833 = 5001625) B5001625
theorem B4809415 : Blo 1461050 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B2466551 : Blo 1461050 2466551 := bstep (se 1 (by rfl) ⟨1849913, by rfl⟩ : syracuseStep 2466551 = 3699827) B3699827
theorem B6243101 : Blo 1461050 6243101 := bstep (se 3 (by rfl) ⟨1170581, by rfl⟩ : syracuseStep 6243101 = 2341163) B2341163
theorem B9364369 : Blo 1461050 9364369 := bstep (se 2 (by rfl) ⟨3511638, by rfl⟩ : syracuseStep 9364369 = 7023277) B7023277
theorem B33743891 : Blo 1461050 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B10003475 : Blo 1461050 10003475 := bstep (se 1 (by rfl) ⟨7502606, by rfl⟩ : syracuseStep 10003475 = 15005213) B15005213
theorem B19997741 : Blo 1461050 19997741 := bstep (se 3 (by rfl) ⟨3749576, by rfl⟩ : syracuseStep 19997741 = 7499153) B7499153
theorem B2466895 : Blo 1461050 2466895 := bstep (se 1 (by rfl) ⟨1850171, by rfl⟩ : syracuseStep 2466895 = 3700343) B3700343
theorem B56214647 : Blo 1461050 56214647 := bstep (se 1 (by rfl) ⟨42160985, by rfl⟩ : syracuseStep 56214647 = 84321971) B84321971
theorem B2467145 : Blo 1461050 2467145 := bstep (se 2 (by rfl) ⟨925179, by rfl⟩ : syracuseStep 2467145 = 1850359) B1850359
theorem B12494195 : Blo 1461050 12494195 := bstep (se 1 (by rfl) ⟨9370646, by rfl⟩ : syracuseStep 12494195 = 18741293) B18741293
theorem B4933007 : Blo 1461050 4933007 := bstep (se 1 (by rfl) ⟨3699755, by rfl⟩ : syracuseStep 4933007 = 7399511) B7399511
theorem B4163035 : Blo 1461050 4163035 := bstep (se 1 (by rfl) ⟨3122276, by rfl⟩ : syracuseStep 4163035 = 6244553) B6244553
theorem B15812101 : Blo 1461050 15812101 := bstep (se 4 (by rfl) ⟨1482384, by rfl⟩ : syracuseStep 15812101 = 2964769) B2964769
theorem B2082343 : Blo 1461050 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B4933331 : Blo 1461050 4933331 := bstep (se 1 (by rfl) ⟨3699998, by rfl⟩ : syracuseStep 4933331 = 7399997) B7399997
theorem B9365213 : Blo 1461050 9365213 := bstep (se 3 (by rfl) ⟨1755977, by rfl⟩ : syracuseStep 9365213 = 3511955) B3511955
theorem B2467577 : Blo 1461050 2467577 := bstep (se 2 (by rfl) ⟨925341, by rfl⟩ : syracuseStep 2467577 = 1850683) B1850683
theorem B7497515 : Blo 1461050 7497515 := bstep (se 1 (by rfl) ⟨5623136, by rfl⟩ : syracuseStep 7497515 = 11246273) B11246273
theorem B2467759 : Blo 1461050 2467759 := bstep (se 1 (by rfl) ⟨1850819, by rfl⟩ : syracuseStep 2467759 = 3701639) B3701639
theorem B2467847 : Blo 1461050 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B5704225 : Blo 1461050 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B3287591 : Blo 1461050 3287591 := bstep (se 1 (by rfl) ⟨2465693, by rfl⟩ : syracuseStep 3287591 = 4931387) B4931387
theorem B4164311 : Blo 1461050 4164311 := bstep (se 1 (by rfl) ⟨3123233, by rfl⟩ : syracuseStep 4164311 = 6246467) B6246467
theorem B1461071 : Blo 1461050 1461071 := bstep (se 1 (by rfl) ⟨1095803, by rfl⟩ : syracuseStep 1461071 = 2191607) B2191607
theorem B1461087 : Blo 1461050 1461087 := bstep (se 1 (by rfl) ⟨1095815, by rfl⟩ : syracuseStep 1461087 = 2191631) B2191631
theorem B3287915 : Blo 1461050 3287915 := bstep (se 1 (by rfl) ⟨2465936, by rfl⟩ : syracuseStep 3287915 = 4931873) B4931873
theorem B4934519 : Blo 1461050 4934519 := bstep (se 1 (by rfl) ⟨3700889, by rfl⟩ : syracuseStep 4934519 = 7401779) B7401779
theorem B1461115 : Blo 1461050 1461115 := bstep (se 1 (by rfl) ⟨1095836, by rfl⟩ : syracuseStep 1461115 = 2191673) B2191673
theorem B3287969 : Blo 1461050 3287969 := bstep (se 2 (by rfl) ⟨1232988, by rfl⟩ : syracuseStep 3287969 = 2465977) B2465977
theorem B1461167 : Blo 1461050 1461167 := bstep (se 1 (by rfl) ⟨1095875, by rfl⟩ : syracuseStep 1461167 = 2191751) B2191751
theorem B4164527 : Blo 1461050 4164527 := bstep (se 1 (by rfl) ⟨3123395, by rfl⟩ : syracuseStep 4164527 = 6246791) B6246791
theorem B1461191 : Blo 1461050 1461191 := bstep (se 1 (by rfl) ⟨1095893, by rfl⟩ : syracuseStep 1461191 = 2191787) B2191787
theorem B1461211 : Blo 1461050 1461211 := bstep (se 1 (by rfl) ⟨1095908, by rfl⟩ : syracuseStep 1461211 = 2191817) B2191817
theorem B5549057 : Blo 1461050 5549057 := bstep (se 2 (by rfl) ⟨2080896, by rfl⟩ : syracuseStep 5549057 = 4161793) B4161793
theorem B1461287 : Blo 1461050 1461287 := bstep (se 1 (by rfl) ⟨1095965, by rfl⟩ : syracuseStep 1461287 = 2191931) B2191931
theorem B2812985 : Blo 1461050 2812985 := bstep (se 2 (by rfl) ⟨1054869, by rfl⟩ : syracuseStep 2812985 = 2109739) B2109739
theorem B2501689 : Blo 1461050 2501689 := bstep (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) B1876267
theorem B1461327 : Blo 1461050 1461327 := bstep (se 1 (by rfl) ⟨1095995, by rfl⟩ : syracuseStep 1461327 = 2191991) B2191991
theorem B4934735 : Blo 1461050 4934735 := bstep (se 1 (by rfl) ⟨3701051, by rfl⟩ : syracuseStep 4934735 = 7402103) B7402103
theorem B1461343 : Blo 1461050 1461343 := bstep (se 1 (by rfl) ⟨1096007, by rfl⟩ : syracuseStep 1461343 = 2192015) B2192015
theorem B1461371 : Blo 1461050 1461371 := bstep (se 1 (by rfl) ⟨1096028, by rfl⟩ : syracuseStep 1461371 = 2192057) B2192057
theorem B1461423 : Blo 1461050 1461423 := bstep (se 1 (by rfl) ⟨1096067, by rfl⟩ : syracuseStep 1461423 = 2192135) B2192135
theorem B1461447 : Blo 1461050 1461447 := bstep (se 1 (by rfl) ⟨1096085, by rfl⟩ : syracuseStep 1461447 = 2192171) B2192171
theorem B1461467 : Blo 1461050 1461467 := bstep (se 1 (by rfl) ⟨1096100, by rfl⟩ : syracuseStep 1461467 = 2192201) B2192201
theorem B3607799 : Blo 1461050 3607799 := bstep (se 1 (by rfl) ⟨2705849, by rfl⟩ : syracuseStep 3607799 = 5411699) B5411699
theorem B3288311 : Blo 1461050 3288311 := bstep (se 1 (by rfl) ⟨2466233, by rfl⟩ : syracuseStep 3288311 = 4932467) B4932467
theorem B1461543 : Blo 1461050 1461543 := bstep (se 1 (by rfl) ⟨1096157, by rfl⟩ : syracuseStep 1461543 = 2192315) B2192315
theorem B1461583 : Blo 1461050 1461583 := bstep (se 1 (by rfl) ⟨1096187, by rfl⟩ : syracuseStep 1461583 = 2192375) B2192375
theorem B1461599 : Blo 1461050 1461599 := bstep (se 1 (by rfl) ⟨1096199, by rfl⟩ : syracuseStep 1461599 = 2192399) B2192399
theorem B1461627 : Blo 1461050 1461627 := bstep (se 1 (by rfl) ⟨1096220, by rfl⟩ : syracuseStep 1461627 = 2192441) B2192441
theorem B1461679 : Blo 1461050 1461679 := bstep (se 1 (by rfl) ⟨1096259, by rfl⟩ : syracuseStep 1461679 = 2192519) B2192519
theorem B1461703 : Blo 1461050 1461703 := bstep (se 1 (by rfl) ⟨1096277, by rfl⟩ : syracuseStep 1461703 = 2192555) B2192555
theorem B4935113 : Blo 1461050 4935113 := bstep (se 2 (by rfl) ⟨1850667, by rfl⟩ : syracuseStep 4935113 = 3701335) B3701335
theorem B1461723 : Blo 1461050 1461723 := bstep (se 1 (by rfl) ⟨1096292, by rfl⟩ : syracuseStep 1461723 = 2192585) B2192585
theorem B1461799 : Blo 1461050 1461799 := bstep (se 1 (by rfl) ⟨1096349, by rfl⟩ : syracuseStep 1461799 = 2192699) B2192699
theorem B1461839 : Blo 1461050 1461839 := bstep (se 1 (by rfl) ⟨1096379, by rfl⟩ : syracuseStep 1461839 = 2192759) B2192759
theorem B37957207 : Blo 1461050 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B1461855 : Blo 1461050 1461855 := bstep (se 1 (by rfl) ⟨1096391, by rfl⟩ : syracuseStep 1461855 = 2192783) B2192783
theorem B1461883 : Blo 1461050 1461883 := bstep (se 1 (by rfl) ⟨1096412, by rfl⟩ : syracuseStep 1461883 = 2192825) B2192825
theorem B9367163 : Blo 1461050 9367163 := bstep (se 1 (by rfl) ⟨7025372, by rfl⟩ : syracuseStep 9367163 = 14050745) B14050745
theorem B6008467 : Blo 1461050 6008467 := bstep (se 1 (by rfl) ⟨4506350, by rfl⟩ : syracuseStep 6008467 = 9012701) B9012701
theorem B1461935 : Blo 1461050 1461935 := bstep (se 1 (by rfl) ⟨1096451, by rfl⟩ : syracuseStep 1461935 = 2192903) B2192903
theorem B1461959 : Blo 1461050 1461959 := bstep (se 1 (by rfl) ⟨1096469, by rfl⟩ : syracuseStep 1461959 = 2192939) B2192939
theorem B5000915 : Blo 1461050 5000915 := bstep (se 1 (by rfl) ⟨3750686, by rfl⟩ : syracuseStep 5000915 = 7501373) B7501373
theorem B4935383 : Blo 1461050 4935383 := bstep (se 1 (by rfl) ⟨3701537, by rfl⟩ : syracuseStep 4935383 = 7403075) B7403075
theorem B1461979 : Blo 1461050 1461979 := bstep (se 1 (by rfl) ⟨1096484, by rfl⟩ : syracuseStep 1461979 = 2192969) B2192969
theorem B1462055 : Blo 1461050 1462055 := bstep (se 1 (by rfl) ⟨1096541, by rfl⟩ : syracuseStep 1462055 = 2193083) B2193083
theorem B3288905 : Blo 1461050 3288905 := bstep (se 2 (by rfl) ⟨1233339, by rfl⟩ : syracuseStep 3288905 = 2466679) B2466679
theorem B1462095 : Blo 1461050 1462095 := bstep (se 1 (by rfl) ⟨1096571, by rfl⟩ : syracuseStep 1462095 = 2193143) B2193143
theorem B1462111 : Blo 1461050 1462111 := bstep (se 1 (by rfl) ⟨1096583, by rfl⟩ : syracuseStep 1462111 = 2193167) B2193167
theorem B11251565 : Blo 1461050 11251565 := bstep (se 3 (by rfl) ⟨2109668, by rfl⟩ : syracuseStep 11251565 = 4219337) B4219337
theorem B1462139 : Blo 1461050 1462139 := bstep (se 1 (by rfl) ⟨1096604, by rfl⟩ : syracuseStep 1462139 = 2193209) B2193209
theorem B4681633 : Blo 1461050 4681633 := bstep (se 2 (by rfl) ⟨1755612, by rfl⟩ : syracuseStep 4681633 = 3511225) B3511225
theorem B1462191 : Blo 1461050 1462191 := bstep (se 1 (by rfl) ⟨1096643, by rfl⟩ : syracuseStep 1462191 = 2193287) B2193287
theorem B4935599 : Blo 1461050 4935599 := bstep (se 1 (by rfl) ⟨3701699, by rfl⟩ : syracuseStep 4935599 = 7403399) B7403399
theorem B1462215 : Blo 1461050 1462215 := bstep (se 1 (by rfl) ⟨1096661, by rfl⟩ : syracuseStep 1462215 = 2193323) B2193323
theorem B1462235 : Blo 1461050 1462235 := bstep (se 1 (by rfl) ⟨1096676, by rfl⟩ : syracuseStep 1462235 = 2193353) B2193353
theorem B5926931 : Blo 1461050 5926931 := bstep (se 1 (by rfl) ⟨4445198, by rfl⟩ : syracuseStep 5926931 = 8890397) B8890397
theorem B1462311 : Blo 1461050 1462311 := bstep (se 1 (by rfl) ⟨1096733, by rfl⟩ : syracuseStep 1462311 = 2193467) B2193467
theorem B1462351 : Blo 1461050 1462351 := bstep (se 1 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 1462351 = 2193527) B2193527
theorem B47403089 : Blo 1461050 47403089 := bstep (se 2 (by rfl) ⟨17776158, by rfl⟩ : syracuseStep 47403089 = 35552317) B35552317
theorem B1462367 : Blo 1461050 1462367 := bstep (se 1 (by rfl) ⟨1096775, by rfl⟩ : syracuseStep 1462367 = 2193551) B2193551
theorem B1462395 : Blo 1461050 1462395 := bstep (se 1 (by rfl) ⟨1096796, by rfl⟩ : syracuseStep 1462395 = 2193593) B2193593
theorem B1462447 : Blo 1461050 1462447 := bstep (se 1 (by rfl) ⟨1096835, by rfl⟩ : syracuseStep 1462447 = 2193671) B2193671
theorem B1462471 : Blo 1461050 1462471 := bstep (se 1 (by rfl) ⟨1096853, by rfl⟩ : syracuseStep 1462471 = 2193707) B2193707
theorem B1462491 : Blo 1461050 1462491 := bstep (se 1 (by rfl) ⟨1096868, by rfl⟩ : syracuseStep 1462491 = 2193737) B2193737
theorem B36049211 : Blo 1461050 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B2191721 : Blo 1461050 2191721 := bstep (se 2 (by rfl) ⟨821895, by rfl⟩ : syracuseStep 2191721 = 1643791) B1643791
theorem B2191799 : Blo 1461050 2191799 := bstep (se 1 (by rfl) ⟨1643849, by rfl⟩ : syracuseStep 2191799 = 3287699) B3287699
theorem B2191835 : Blo 1461050 2191835 := bstep (se 1 (by rfl) ⟨1643876, by rfl⟩ : syracuseStep 2191835 = 3287753) B3287753
theorem B3699209 : Blo 1461050 3699209 := bstep (se 2 (by rfl) ⟨1387203, by rfl⟩ : syracuseStep 3699209 = 2774407) B2774407
theorem B4682249 : Blo 1461050 4682249 := bstep (se 2 (by rfl) ⟨1755843, by rfl⟩ : syracuseStep 4682249 = 3511687) B3511687
theorem B12661271 : Blo 1461050 12661271 := bstep (se 1 (by rfl) ⟨9495953, by rfl⟩ : syracuseStep 12661271 = 18991907) B18991907
theorem B4682299 : Blo 1461050 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B7500347 : Blo 1461050 7500347 := bstep (se 1 (by rfl) ⟨5625260, by rfl⟩ : syracuseStep 7500347 = 11250521) B11250521
theorem B3289697 : Blo 1461050 3289697 := bstep (se 2 (by rfl) ⟨1233636, by rfl⟩ : syracuseStep 3289697 = 2467273) B2467273
theorem B5550727 : Blo 1461050 5550727 := bstep (se 1 (by rfl) ⟨4163045, by rfl⟩ : syracuseStep 5550727 = 8326091) B8326091
theorem B2773921 : Blo 1461050 2773921 := bstep (se 2 (by rfl) ⟨1040220, by rfl⟩ : syracuseStep 2773921 = 2080441) B2080441
theorem B2962337 : Blo 1461050 2962337 := bstep (se 2 (by rfl) ⟨1110876, by rfl⟩ : syracuseStep 2962337 = 2221753) B2221753
theorem B2192303 : Blo 1461050 2192303 := bstep (se 1 (by rfl) ⟨1644227, by rfl⟩ : syracuseStep 2192303 = 3288455) B3288455
theorem B4445111 : Blo 1461050 4445111 := bstep (se 1 (by rfl) ⟨3333833, by rfl⟩ : syracuseStep 4445111 = 6667667) B6667667
theorem B5551031 : Blo 1461050 5551031 := bstep (se 1 (by rfl) ⟨4163273, by rfl⟩ : syracuseStep 5551031 = 8326547) B8326547
theorem B3290039 : Blo 1461050 3290039 := bstep (se 1 (by rfl) ⟨2467529, by rfl⟩ : syracuseStep 3290039 = 4935059) B4935059
theorem B2192393 : Blo 1461050 2192393 := bstep (se 2 (by rfl) ⟨822147, by rfl⟩ : syracuseStep 2192393 = 1644295) B1644295
theorem B2192423 : Blo 1461050 2192423 := bstep (se 1 (by rfl) ⟨1644317, by rfl⟩ : syracuseStep 2192423 = 3288635) B3288635
theorem B2192507 : Blo 1461050 2192507 := bstep (se 1 (by rfl) ⟨1644380, by rfl⟩ : syracuseStep 2192507 = 3288761) B3288761
theorem B1561723 : Blo 1461050 1561723 := bstep (se 1 (by rfl) ⟨1171292, by rfl⟩ : syracuseStep 1561723 = 2342585) B2342585
theorem B1643719 : Blo 1461050 1643719 := bstep (se 1 (by rfl) ⟨1232789, by rfl⟩ : syracuseStep 1643719 = 2465579) B2465579
theorem B2774263 : Blo 1461050 2774263 := bstep (se 1 (by rfl) ⟨2080697, by rfl⟩ : syracuseStep 2774263 = 4161395) B4161395
theorem B2192633 : Blo 1461050 2192633 := bstep (se 2 (by rfl) ⟨822237, by rfl⟩ : syracuseStep 2192633 = 1644475) B1644475
theorem B2192735 : Blo 1461050 2192735 := bstep (se 1 (by rfl) ⟨1644551, by rfl⟩ : syracuseStep 2192735 = 3289103) B3289103
theorem B2962793 : Blo 1461050 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B2192747 : Blo 1461050 2192747 := bstep (se 1 (by rfl) ⟨1644560, by rfl⟩ : syracuseStep 2192747 = 3289121) B3289121
theorem B3749249 : Blo 1461050 3749249 := bstep (se 2 (by rfl) ⟨1405968, by rfl⟩ : syracuseStep 3749249 = 2811937) B2811937
theorem B3290633 : Blo 1461050 3290633 := bstep (se 2 (by rfl) ⟨1233987, by rfl⟩ : syracuseStep 3290633 = 2467975) B2467975
theorem B2774567 : Blo 1461050 2774567 := bstep (se 1 (by rfl) ⟨2080925, by rfl⟩ : syracuseStep 2774567 = 4161851) B4161851
theorem B2192975 : Blo 1461050 2192975 := bstep (se 1 (by rfl) ⟨1644731, by rfl⟩ : syracuseStep 2192975 = 3289463) B3289463
theorem B45618785 : Blo 1461050 45618785 := bstep (se 2 (by rfl) ⟨17107044, by rfl⟩ : syracuseStep 45618785 = 34214089) B34214089
theorem B3700363 : Blo 1461050 3700363 := bstep (se 1 (by rfl) ⟨2775272, by rfl⟩ : syracuseStep 3700363 = 5550545) B5550545
theorem B2193095 : Blo 1461050 2193095 := bstep (se 1 (by rfl) ⟨1644821, by rfl⟩ : syracuseStep 2193095 = 3289643) B3289643
theorem B2193257 : Blo 1461050 2193257 := bstep (se 2 (by rfl) ⟨822471, by rfl⟩ : syracuseStep 2193257 = 1644943) B1644943
theorem B2193335 : Blo 1461050 2193335 := bstep (se 1 (by rfl) ⟨1645001, by rfl⟩ : syracuseStep 2193335 = 3290003) B3290003
theorem B3700667 : Blo 1461050 3700667 := bstep (se 1 (by rfl) ⟨2775500, by rfl⟩ : syracuseStep 3700667 = 5551001) B5551001
theorem B2193371 : Blo 1461050 2193371 := bstep (se 1 (by rfl) ⟨1645028, by rfl⟩ : syracuseStep 2193371 = 3290057) B3290057
theorem B1644583 : Blo 1461050 1644583 := bstep (se 1 (by rfl) ⟨1233437, by rfl⟩ : syracuseStep 1644583 = 2466875) B2466875
theorem B5552185 : Blo 1461050 5552185 := bstep (se 2 (by rfl) ⟨2082069, by rfl⟩ : syracuseStep 5552185 = 4164139) B4164139
theorem B1480999 : Blo 1461050 1480999 := bstep (se 1 (by rfl) ⟨1110749, by rfl⟩ : syracuseStep 1480999 = 2221499) B2221499
theorem B5552489 : Blo 1461050 5552489 := bstep (se 2 (by rfl) ⟨2082183, by rfl⟩ : syracuseStep 5552489 = 4164367) B4164367
theorem B7027181 : Blo 1461050 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B1849979 : Blo 1461050 1849979 := bstep (se 1 (by rfl) ⟨1387484, by rfl⟩ : syracuseStep 1849979 = 2774969) B2774969
theorem B57834163 : Blo 1461050 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B3701447 : Blo 1461050 3701447 := bstep (se 1 (by rfl) ⟨2776085, by rfl⟩ : syracuseStep 3701447 = 5552171) B5552171
theorem B7903955 : Blo 1461050 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B3701497 : Blo 1461050 3701497 := bstep (se 2 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 3701497 = 2776123) B2776123
theorem B12491597 : Blo 1461050 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B2341727 : Blo 1461050 2341727 := bstep (se 1 (by rfl) ⟨1756295, by rfl⟩ : syracuseStep 2341727 = 3512591) B3512591
theorem B8321899 : Blo 1461050 8321899 := bstep (se 1 (by rfl) ⟨6241424, by rfl⟩ : syracuseStep 8321899 = 12482849) B12482849
theorem B17104067 : Blo 1461050 17104067 := bstep (se 1 (by rfl) ⟨12828050, by rfl⟩ : syracuseStep 17104067 = 25656101) B25656101
theorem B2342137 : Blo 1461050 2342137 := bstep (se 2 (by rfl) ⟨878301, by rfl⟩ : syracuseStep 2342137 = 1756603) B1756603
theorem B2776427 : Blo 1461050 2776427 := bstep (se 1 (by rfl) ⟨2082320, by rfl⟩ : syracuseStep 2776427 = 4164641) B4164641
theorem B5414381 : Blo 1461050 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B15801895 : Blo 1461050 15801895 := bstep (se 1 (by rfl) ⟨11851421, by rfl⟩ : syracuseStep 15801895 = 23702843) B23702843
theorem B53354051 : Blo 1461050 53354051 := bstep (se 1 (by rfl) ⟨40015538, by rfl⟩ : syracuseStep 53354051 = 80031077) B80031077
theorem B200326769 : Blo 1461050 200326769 := bstep (se 2 (by rfl) ⟨75122538, by rfl⟩ : syracuseStep 200326769 = 150245077) B150245077
theorem B4161223 : Blo 1461050 4161223 := bstep (se 1 (by rfl) ⟨3120917, by rfl⟩ : syracuseStep 4161223 = 6241835) B6241835
theorem B6242143 : Blo 1461050 6242143 := bstep (se 1 (by rfl) ⟨4681607, by rfl⟩ : syracuseStep 6242143 = 9363215) B9363215
theorem B2466139 : Blo 1461050 2466139 := bstep (se 1 (by rfl) ⟨1849604, by rfl⟩ : syracuseStep 2466139 = 3699209) B3699209
theorem B3121499 : Blo 1461050 3121499 := bstep (se 1 (by rfl) ⟨2341124, by rfl⟩ : syracuseStep 3121499 = 4682249) B4682249
theorem B1974665 : Blo 1461050 1974665 := bstep (se 2 (by rfl) ⟨740499, by rfl⟩ : syracuseStep 1974665 = 1480999) B1480999
theorem B4162067 : Blo 1461050 4162067 := bstep (se 1 (by rfl) ⟨3121550, by rfl⟩ : syracuseStep 4162067 = 6243101) B6243101
theorem B22495927 : Blo 1461050 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B6668983 : Blo 1461050 6668983 := bstep (se 1 (by rfl) ⟨5001737, by rfl⟩ : syracuseStep 6668983 = 10003475) B10003475
theorem B6243065 : Blo 1461050 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B77112217 : Blo 1461050 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B1975195 : Blo 1461050 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B2499499 : Blo 1461050 2499499 := bstep (se 1 (by rfl) ⟨1874624, by rfl⟩ : syracuseStep 2499499 = 3749249) B3749249
theorem B6243475 : Blo 1461050 6243475 := bstep (se 1 (by rfl) ⟨4682606, by rfl⟩ : syracuseStep 6243475 = 9365213) B9365213
theorem B12485825 : Blo 1461050 12485825 := bstep (se 2 (by rfl) ⟨4682184, by rfl⟩ : syracuseStep 12485825 = 9364369) B9364369
theorem B4998343 : Blo 1461050 4998343 := bstep (se 1 (by rfl) ⟨3748757, by rfl⟩ : syracuseStep 4998343 = 7497515) B7497515
theorem B2467111 : Blo 1461050 2467111 := bstep (se 1 (by rfl) ⟨1850333, by rfl⟩ : syracuseStep 2467111 = 3700667) B3700667
theorem B3335585 : Blo 1461050 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B4933277 : Blo 1461050 4933277 := bstep (se 3 (by rfl) ⟨924989, by rfl⟩ : syracuseStep 4933277 = 1849979) B1849979
theorem B3122849 : Blo 1461050 3122849 := bstep (se 2 (by rfl) ⟨1171068, by rfl⟩ : syracuseStep 3122849 = 2342137) B2342137
theorem B2467631 : Blo 1461050 2467631 := bstep (se 1 (by rfl) ⟨1850723, by rfl⟩ : syracuseStep 2467631 = 3701447) B3701447
theorem B5269303 : Blo 1461050 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B4933817 : Blo 1461050 4933817 := bstep (se 2 (by rfl) ⟨1850181, by rfl⟩ : syracuseStep 4933817 = 3700363) B3700363
theorem B5548297 : Blo 1461050 5548297 := bstep (se 2 (by rfl) ⟨2080611, by rfl⟩ : syracuseStep 5548297 = 4161223) B4161223
theorem B6244775 : Blo 1461050 6244775 := bstep (se 1 (by rfl) ⟨4683581, by rfl⟩ : syracuseStep 6244775 = 9367163) B9367163
theorem B7899565 : Blo 1461050 7899565 := bstep (se 3 (by rfl) ⟨1481168, by rfl⟩ : syracuseStep 7899565 = 2962337) B2962337
theorem B3287735 : Blo 1461050 3287735 := bstep (se 1 (by rfl) ⟨2465801, by rfl⟩ : syracuseStep 3287735 = 4931603) B4931603
theorem B3951287 : Blo 1461050 3951287 := bstep (se 1 (by rfl) ⟨2963465, by rfl⟩ : syracuseStep 3951287 = 5926931) B5926931
theorem B3287951 : Blo 1461050 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B1461147 : Blo 1461050 1461147 := bstep (se 1 (by rfl) ⟨1095860, by rfl⟩ : syracuseStep 1461147 = 2191721) B2191721
theorem B1461199 : Blo 1461050 1461199 := bstep (se 1 (by rfl) ⟨1095899, by rfl⟩ : syracuseStep 1461199 = 2191799) B2191799
theorem B1461223 : Blo 1461050 1461223 := bstep (se 1 (by rfl) ⟨1095917, by rfl⟩ : syracuseStep 1461223 = 2191835) B2191835
theorem B8440847 : Blo 1461050 8440847 := bstep (se 1 (by rfl) ⟨6330635, by rfl⟩ : syracuseStep 8440847 = 12661271) B12661271
theorem B5000231 : Blo 1461050 5000231 := bstep (se 1 (by rfl) ⟨3750173, by rfl⟩ : syracuseStep 5000231 = 7500347) B7500347
theorem B1461535 : Blo 1461050 1461535 := bstep (se 1 (by rfl) ⟨1096151, by rfl⟩ : syracuseStep 1461535 = 2192303) B2192303
theorem B9620797 : Blo 1461050 9620797 := bstep (se 3 (by rfl) ⟨1803899, by rfl⟩ : syracuseStep 9620797 = 3607799) B3607799
theorem B1461595 : Blo 1461050 1461595 := bstep (se 1 (by rfl) ⟨1096196, by rfl⟩ : syracuseStep 1461595 = 2192393) B2192393
theorem B1461615 : Blo 1461050 1461615 := bstep (se 1 (by rfl) ⟨1096211, by rfl⟩ : syracuseStep 1461615 = 2192423) B2192423
theorem B13331827 : Blo 1461050 13331827 := bstep (se 1 (by rfl) ⟨9998870, by rfl⟩ : syracuseStep 13331827 = 19997741) B19997741
theorem B8891777 : Blo 1461050 8891777 := bstep (se 2 (by rfl) ⟨3334416, by rfl⟩ : syracuseStep 8891777 = 6668833) B6668833
theorem B1461671 : Blo 1461050 1461671 := bstep (se 1 (by rfl) ⟨1096253, by rfl⟩ : syracuseStep 1461671 = 2192507) B2192507
theorem B1461755 : Blo 1461050 1461755 := bstep (se 1 (by rfl) ⟨1096316, by rfl⟩ : syracuseStep 1461755 = 2192633) B2192633
theorem B7400969 : Blo 1461050 7400969 := bstep (se 2 (by rfl) ⟨2775363, by rfl⟩ : syracuseStep 7400969 = 5550727) B5550727
theorem B23703101 : Blo 1461050 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B1461823 : Blo 1461050 1461823 := bstep (se 1 (by rfl) ⟨1096367, by rfl⟩ : syracuseStep 1461823 = 2192735) B2192735
theorem B1461831 : Blo 1461050 1461831 := bstep (se 1 (by rfl) ⟨1096373, by rfl⟩ : syracuseStep 1461831 = 2192747) B2192747
theorem B3288671 : Blo 1461050 3288671 := bstep (se 1 (by rfl) ⟨2466503, by rfl⟩ : syracuseStep 3288671 = 4933007) B4933007
theorem B4935329 : Blo 1461050 4935329 := bstep (se 2 (by rfl) ⟨1850748, by rfl⟩ : syracuseStep 4935329 = 3701497) B3701497
theorem B1461983 : Blo 1461050 1461983 := bstep (se 1 (by rfl) ⟨1096487, by rfl⟩ : syracuseStep 1461983 = 2192975) B2192975
theorem B30412523 : Blo 1461050 30412523 := bstep (se 1 (by rfl) ⟨22809392, by rfl⟩ : syracuseStep 30412523 = 45618785) B45618785
theorem B1462063 : Blo 1461050 1462063 := bstep (se 1 (by rfl) ⟨1096547, by rfl⟩ : syracuseStep 1462063 = 2193095) B2193095
theorem B3288887 : Blo 1461050 3288887 := bstep (se 1 (by rfl) ⟨2466665, by rfl⟩ : syracuseStep 3288887 = 4933331) B4933331
theorem B11095865 : Blo 1461050 11095865 := bstep (se 2 (by rfl) ⟨4160949, by rfl⟩ : syracuseStep 11095865 = 8321899) B8321899
theorem B3698561 : Blo 1461050 3698561 := bstep (se 2 (by rfl) ⟨1386960, by rfl⟩ : syracuseStep 3698561 = 2773921) B2773921
theorem B1462171 : Blo 1461050 1462171 := bstep (se 1 (by rfl) ⟨1096628, by rfl⟩ : syracuseStep 1462171 = 2193257) B2193257
theorem B1462223 : Blo 1461050 1462223 := bstep (se 1 (by rfl) ⟨1096667, by rfl⟩ : syracuseStep 1462223 = 2193335) B2193335
theorem B1462247 : Blo 1461050 1462247 := bstep (se 1 (by rfl) ⟨1096685, by rfl⟩ : syracuseStep 1462247 = 2193371) B2193371
theorem B3289193 : Blo 1461050 3289193 := bstep (se 2 (by rfl) ⟨1233447, by rfl⟩ : syracuseStep 3289193 = 2466895) B2466895
theorem B2191625 : Blo 1461050 2191625 := bstep (se 2 (by rfl) ⟨821859, by rfl⟩ : syracuseStep 2191625 = 1643719) B1643719
theorem B3699017 : Blo 1461050 3699017 := bstep (se 2 (by rfl) ⟨1387131, by rfl⟩ : syracuseStep 3699017 = 2774263) B2774263
theorem B2191727 : Blo 1461050 2191727 := bstep (se 1 (by rfl) ⟨1643795, by rfl⟩ : syracuseStep 2191727 = 3287591) B3287591
theorem B8327731 : Blo 1461050 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B1561151 : Blo 1461050 1561151 := bstep (se 1 (by rfl) ⟨1170863, by rfl⟩ : syracuseStep 1561151 = 2341727) B2341727
theorem B2191943 : Blo 1461050 2191943 := bstep (se 1 (by rfl) ⟨1643957, by rfl⟩ : syracuseStep 2191943 = 3287915) B3287915
theorem B3289679 : Blo 1461050 3289679 := bstep (se 1 (by rfl) ⟨2467259, by rfl⟩ : syracuseStep 3289679 = 4934519) B4934519
theorem B2191979 : Blo 1461050 2191979 := bstep (se 1 (by rfl) ⟨1643984, by rfl⟩ : syracuseStep 2191979 = 3287969) B3287969
theorem B5550713 : Blo 1461050 5550713 := bstep (se 2 (by rfl) ⟨2081517, by rfl⟩ : syracuseStep 5550713 = 4163035) B4163035
theorem B3699371 : Blo 1461050 3699371 := bstep (se 1 (by rfl) ⟨2774528, by rfl⟩ : syracuseStep 3699371 = 5549057) B5549057
theorem B21082801 : Blo 1461050 21082801 := bstep (se 2 (by rfl) ⟨7906050, by rfl⟩ : syracuseStep 21082801 = 15812101) B15812101
theorem B3289823 : Blo 1461050 3289823 := bstep (se 1 (by rfl) ⟨2467367, by rfl⟩ : syracuseStep 3289823 = 4934735) B4934735
theorem B2192207 : Blo 1461050 2192207 := bstep (se 1 (by rfl) ⟨1644155, by rfl⟩ : syracuseStep 2192207 = 3288311) B3288311
theorem B3290075 : Blo 1461050 3290075 := bstep (se 1 (by rfl) ⟨2467556, by rfl⟩ : syracuseStep 3290075 = 4935113) B4935113
theorem B3609587 : Blo 1461050 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B133551179 : Blo 1461050 133551179 := bstep (se 1 (by rfl) ⟨100163384, by rfl⟩ : syracuseStep 133551179 = 200326769) B200326769
theorem B3290255 : Blo 1461050 3290255 := bstep (se 1 (by rfl) ⟨2467691, by rfl⟩ : syracuseStep 3290255 = 4935383) B4935383
theorem B2192603 : Blo 1461050 2192603 := bstep (se 1 (by rfl) ⟨1644452, by rfl⟩ : syracuseStep 2192603 = 3288905) B3288905
theorem B3290345 : Blo 1461050 3290345 := bstep (se 2 (by rfl) ⟨1233879, by rfl⟩ : syracuseStep 3290345 = 2467759) B2467759
theorem B7501043 : Blo 1461050 7501043 := bstep (se 1 (by rfl) ⟨5625782, by rfl⟩ : syracuseStep 7501043 = 11251565) B11251565
theorem B3290399 : Blo 1461050 3290399 := bstep (se 1 (by rfl) ⟨2467799, by rfl⟩ : syracuseStep 3290399 = 4935599) B4935599
theorem B1643899 : Blo 1461050 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B2192777 : Blo 1461050 2192777 := bstep (se 2 (by rfl) ⟨822291, by rfl⟩ : syracuseStep 2192777 = 1644583) B1644583
theorem B31602059 : Blo 1461050 31602059 := bstep (se 1 (by rfl) ⟨23701544, by rfl⟩ : syracuseStep 31602059 = 47403089) B47403089
theorem B7402913 : Blo 1461050 7402913 := bstep (se 2 (by rfl) ⟨2776092, by rfl⟩ : syracuseStep 7402913 = 5552185) B5552185
theorem B24032807 : Blo 1461050 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B2193131 : Blo 1461050 2193131 := bstep (se 1 (by rfl) ⟨1644848, by rfl⟩ : syracuseStep 2193131 = 3289697) B3289697
theorem B1644367 : Blo 1461050 1644367 := bstep (se 1 (by rfl) ⟨1233275, by rfl⟩ : syracuseStep 1644367 = 2466551) B2466551
theorem B2963407 : Blo 1461050 2963407 := bstep (se 1 (by rfl) ⟨2222555, by rfl⟩ : syracuseStep 2963407 = 4445111) B4445111
theorem B3700687 : Blo 1461050 3700687 := bstep (se 1 (by rfl) ⟨2775515, by rfl⟩ : syracuseStep 3700687 = 5551031) B5551031
theorem B2193359 : Blo 1461050 2193359 := bstep (se 1 (by rfl) ⟨1645019, by rfl⟩ : syracuseStep 2193359 = 3290039) B3290039
theorem B8329189 : Blo 1461050 8329189 := bstep (se 4 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 8329189 = 1561723) B1561723
theorem B121690133 : Blo 1461050 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B37476431 : Blo 1461050 37476431 := bstep (se 1 (by rfl) ⟨28107323, by rfl⟩ : syracuseStep 37476431 = 56214647) B56214647
theorem B1644763 : Blo 1461050 1644763 := bstep (se 1 (by rfl) ⟨1233572, by rfl⟩ : syracuseStep 1644763 = 2467145) B2467145
theorem B8329463 : Blo 1461050 8329463 := bstep (se 1 (by rfl) ⟨6247097, by rfl⟩ : syracuseStep 8329463 = 12494195) B12494195
theorem B6412553 : Blo 1461050 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B2193755 : Blo 1461050 2193755 := bstep (se 1 (by rfl) ⟨1645316, by rfl⟩ : syracuseStep 2193755 = 3290633) B3290633
theorem B1849711 : Blo 1461050 1849711 := bstep (se 1 (by rfl) ⟨1387283, by rfl⟩ : syracuseStep 1849711 = 2774567) B2774567
theorem B1645051 : Blo 1461050 1645051 := bstep (se 1 (by rfl) ⟨1233788, by rfl⟩ : syracuseStep 1645051 = 2467577) B2467577
theorem B1645231 : Blo 1461050 1645231 := bstep (se 1 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 1645231 = 2467847) B2467847
theorem B3701659 : Blo 1461050 3701659 := bstep (se 1 (by rfl) ⟨2776244, by rfl⟩ : syracuseStep 3701659 = 5552489) B5552489
theorem B4684787 : Blo 1461050 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B2776207 : Blo 1461050 2776207 := bstep (se 1 (by rfl) ⟨2082155, by rfl⟩ : syracuseStep 2776207 = 4164311) B4164311
theorem B2776351 : Blo 1461050 2776351 := bstep (se 1 (by rfl) ⟨2082263, by rfl⟩ : syracuseStep 2776351 = 4164527) B4164527
theorem B1875323 : Blo 1461050 1875323 := bstep (se 1 (by rfl) ⟨1406492, by rfl⟩ : syracuseStep 1875323 = 2812985) B2812985
theorem B21069193 : Blo 1461050 21069193 := bstep (se 2 (by rfl) ⟨7900947, by rfl⟩ : syracuseStep 21069193 = 15801895) B15801895
theorem B2776457 : Blo 1461050 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B50609609 : Blo 1461050 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B11402711 : Blo 1461050 11402711 := bstep (se 1 (by rfl) ⟨8552033, by rfl⟩ : syracuseStep 11402711 = 17104067) B17104067
theorem B8011289 : Blo 1461050 8011289 := bstep (se 2 (by rfl) ⟨3004233, by rfl⟩ : syracuseStep 8011289 = 6008467) B6008467
theorem B1850951 : Blo 1461050 1850951 := bstep (se 1 (by rfl) ⟨1388213, by rfl⟩ : syracuseStep 1850951 = 2776427) B2776427
theorem B35569367 : Blo 1461050 35569367 := bstep (se 1 (by rfl) ⟨26677025, by rfl⟩ : syracuseStep 35569367 = 53354051) B53354051
theorem B8322857 : Blo 1461050 8322857 := bstep (se 2 (by rfl) ⟨3121071, by rfl⟩ : syracuseStep 8322857 = 6242143) B6242143
theorem B3333943 : Blo 1461050 3333943 := bstep (se 1 (by rfl) ⟨2500457, by rfl⟩ : syracuseStep 3333943 = 5000915) B5000915
theorem B6242177 : Blo 1461050 6242177 := bstep (se 2 (by rfl) ⟨2340816, by rfl⟩ : syracuseStep 6242177 = 4681633) B4681633
theorem B2466011 : Blo 1461050 2466011 := bstep (se 1 (by rfl) ⟨1849508, by rfl⟩ : syracuseStep 2466011 = 3699017) B3699017
theorem B2080999 : Blo 1461050 2080999 := bstep (se 1 (by rfl) ⟨1560749, by rfl⟩ : syracuseStep 2080999 = 3121499) B3121499
theorem B7397729 : Blo 1461050 7397729 := bstep (se 2 (by rfl) ⟨2774148, by rfl⟩ : syracuseStep 7397729 = 5548297) B5548297
theorem B2466247 : Blo 1461050 2466247 := bstep (se 1 (by rfl) ⟨1849685, by rfl⟩ : syracuseStep 2466247 = 3699371) B3699371
theorem B2466281 : Blo 1461050 2466281 := bstep (se 2 (by rfl) ⟨924855, by rfl⟩ : syracuseStep 2466281 = 1849711) B1849711
theorem B4162043 : Blo 1461050 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B8323883 : Blo 1461050 8323883 := bstep (se 1 (by rfl) ⟨6242912, by rfl⟩ : syracuseStep 8323883 = 12485825) B12485825
theorem B2081899 : Blo 1461050 2081899 := bstep (se 1 (by rfl) ⟨1561424, by rfl⟩ : syracuseStep 2081899 = 3122849) B3122849
theorem B81126755 : Blo 1461050 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B4163069 : Blo 1461050 4163069 := bstep (se 3 (by rfl) ⟨780575, by rfl⟩ : syracuseStep 4163069 = 1561151) B1561151
theorem B8324633 : Blo 1461050 8324633 := bstep (se 2 (by rfl) ⟨3121737, by rfl⟩ : syracuseStep 8324633 = 6243475) B6243475
theorem B4163183 : Blo 1461050 4163183 := bstep (se 1 (by rfl) ⟨3122387, by rfl⟩ : syracuseStep 4163183 = 6244775) B6244775
theorem B28092257 : Blo 1461050 28092257 := bstep (se 2 (by rfl) ⟨10534596, by rfl⟩ : syracuseStep 28092257 = 21069193) B21069193
theorem B3123191 : Blo 1461050 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B4933979 : Blo 1461050 4933979 := bstep (se 1 (by rfl) ⟨3700484, by rfl⟩ : syracuseStep 4933979 = 7400969) B7400969
theorem B5548571 : Blo 1461050 5548571 := bstep (se 1 (by rfl) ⟨4161428, by rfl⟩ : syracuseStep 5548571 = 8322857) B8322857
theorem B3951209 : Blo 1461050 3951209 := bstep (se 2 (by rfl) ⟨1481703, by rfl⟩ : syracuseStep 3951209 = 2963407) B2963407
theorem B4934249 : Blo 1461050 4934249 := bstep (se 2 (by rfl) ⟨1850343, by rfl⟩ : syracuseStep 4934249 = 3700687) B3700687
theorem B1461083 : Blo 1461050 1461083 := bstep (se 1 (by rfl) ⟨1095812, by rfl⟩ : syracuseStep 1461083 = 2191625) B2191625
theorem B1461151 : Blo 1461050 1461151 := bstep (se 1 (by rfl) ⟨1095863, by rfl⟩ : syracuseStep 1461151 = 2191727) B2191727
theorem B1461295 : Blo 1461050 1461295 := bstep (se 1 (by rfl) ⟨1095971, by rfl⟩ : syracuseStep 1461295 = 2191943) B2191943
theorem B1461319 : Blo 1461050 1461319 := bstep (se 1 (by rfl) ⟨1095989, by rfl⟩ : syracuseStep 1461319 = 2191979) B2191979
theorem B3288185 : Blo 1461050 3288185 := bstep (se 2 (by rfl) ⟨1233069, by rfl⟩ : syracuseStep 3288185 = 2466139) B2466139
theorem B1461471 : Blo 1461050 1461471 := bstep (se 1 (by rfl) ⟨1096103, by rfl⟩ : syracuseStep 1461471 = 2192207) B2192207
theorem B89034119 : Blo 1461050 89034119 := bstep (se 1 (by rfl) ⟨66775589, by rfl⟩ : syracuseStep 89034119 = 133551179) B133551179
theorem B11103641 : Blo 1461050 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B1461735 : Blo 1461050 1461735 := bstep (se 1 (by rfl) ⟨1096301, by rfl⟩ : syracuseStep 1461735 = 2192603) B2192603
theorem B28110401 : Blo 1461050 28110401 := bstep (se 2 (by rfl) ⟨10541400, by rfl⟩ : syracuseStep 28110401 = 21082801) B21082801
theorem B29994569 : Blo 1461050 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B8891977 : Blo 1461050 8891977 := bstep (se 2 (by rfl) ⟨3334491, by rfl⟩ : syracuseStep 8891977 = 6668983) B6668983
theorem B1461851 : Blo 1461050 1461851 := bstep (se 1 (by rfl) ⟨1096388, by rfl⟩ : syracuseStep 1461851 = 2192777) B2192777
theorem B4935275 : Blo 1461050 4935275 := bstep (se 1 (by rfl) ⟨3701456, by rfl⟩ : syracuseStep 4935275 = 7402913) B7402913
theorem B5000861 : Blo 1461050 5000861 := bstep (se 3 (by rfl) ⟨937661, by rfl⟩ : syracuseStep 5000861 = 1875323) B1875323
theorem B3288851 : Blo 1461050 3288851 := bstep (se 1 (by rfl) ⟨2466638, by rfl⟩ : syracuseStep 3288851 = 4933277) B4933277
theorem B1462087 : Blo 1461050 1462087 := bstep (se 1 (by rfl) ⟨1096565, by rfl⟩ : syracuseStep 1462087 = 2193131) B2193131
theorem B2633593 : Blo 1461050 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B4935545 : Blo 1461050 4935545 := bstep (se 2 (by rfl) ⟨1850829, by rfl⟩ : syracuseStep 4935545 = 3701659) B3701659
theorem B1462239 : Blo 1461050 1462239 := bstep (se 1 (by rfl) ⟨1096679, by rfl⟩ : syracuseStep 1462239 = 2193359) B2193359
theorem B3289211 : Blo 1461050 3289211 := bstep (se 1 (by rfl) ⟨2466908, by rfl⟩ : syracuseStep 3289211 = 4933817) B4933817
theorem B4935869 : Blo 1461050 4935869 := bstep (se 3 (by rfl) ⟨925475, by rfl⟩ : syracuseStep 4935869 = 1850951) B1850951
theorem B1462503 : Blo 1461050 1462503 := bstep (se 1 (by rfl) ⟨1096877, by rfl⟩ : syracuseStep 1462503 = 2193755) B2193755
theorem B6664457 : Blo 1461050 6664457 := bstep (se 2 (by rfl) ⟨2499171, by rfl⟩ : syracuseStep 6664457 = 4998343) B4998343
theorem B17781029 : Blo 1461050 17781029 := bstep (se 4 (by rfl) ⟨1666971, by rfl⟩ : syracuseStep 17781029 = 3333943) B3333943
theorem B28102949 : Blo 1461050 28102949 := bstep (se 4 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 28102949 = 5269303) B5269303
theorem B3289481 : Blo 1461050 3289481 := bstep (se 2 (by rfl) ⟨1233555, by rfl⟩ : syracuseStep 3289481 = 2467111) B2467111
theorem B2191823 : Blo 1461050 2191823 := bstep (se 1 (by rfl) ⟨1643867, by rfl⟩ : syracuseStep 2191823 = 3287735) B3287735
theorem B2634191 : Blo 1461050 2634191 := bstep (se 1 (by rfl) ⟨1975643, by rfl⟩ : syracuseStep 2634191 = 3951287) B3951287
theorem B2191865 : Blo 1461050 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B2191967 : Blo 1461050 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B5927851 : Blo 1461050 5927851 := bstep (se 1 (by rfl) ⟨4445888, by rfl⟩ : syracuseStep 5927851 = 8891777) B8891777
theorem B33739739 : Blo 1461050 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B2192447 : Blo 1461050 2192447 := bstep (se 1 (by rfl) ⟨1644335, by rfl⟩ : syracuseStep 2192447 = 3288671) B3288671
theorem B2192489 : Blo 1461050 2192489 := bstep (se 2 (by rfl) ⟨822183, by rfl⟩ : syracuseStep 2192489 = 1644367) B1644367
theorem B3290219 : Blo 1461050 3290219 := bstep (se 1 (by rfl) ⟨2467664, by rfl⟩ : syracuseStep 3290219 = 4935329) B4935329
theorem B23712911 : Blo 1461050 23712911 := bstep (se 1 (by rfl) ⟨17784683, by rfl⟩ : syracuseStep 23712911 = 35569367) B35569367
theorem B2192591 : Blo 1461050 2192591 := bstep (se 1 (by rfl) ⟨1644443, by rfl⟩ : syracuseStep 2192591 = 3288887) B3288887
theorem B11105585 : Blo 1461050 11105585 := bstep (se 2 (by rfl) ⟨4164594, by rfl⟩ : syracuseStep 11105585 = 8329189) B8329189
theorem B2192795 : Blo 1461050 2192795 := bstep (se 1 (by rfl) ⟨1644596, by rfl⟩ : syracuseStep 2192795 = 3289193) B3289193
theorem B2193017 : Blo 1461050 2193017 := bstep (se 2 (by rfl) ⟨822381, by rfl⟩ : syracuseStep 2193017 = 1644763) B1644763
theorem B2774711 : Blo 1461050 2774711 := bstep (se 1 (by rfl) ⟨2081033, by rfl⟩ : syracuseStep 2774711 = 4162067) B4162067
theorem B2193119 : Blo 1461050 2193119 := bstep (se 1 (by rfl) ⟨1644839, by rfl⟩ : syracuseStep 2193119 = 3289679) B3289679
theorem B3700475 : Blo 1461050 3700475 := bstep (se 1 (by rfl) ⟨2775356, by rfl⟩ : syracuseStep 3700475 = 5550713) B5550713
theorem B2193215 : Blo 1461050 2193215 := bstep (se 1 (by rfl) ⟨1644911, by rfl⟩ : syracuseStep 2193215 = 3289823) B3289823
theorem B10532753 : Blo 1461050 10532753 := bstep (se 2 (by rfl) ⟨3949782, by rfl⟩ : syracuseStep 10532753 = 7899565) B7899565
theorem B20002781 : Blo 1461050 20002781 := bstep (se 3 (by rfl) ⟨3750521, by rfl⟩ : syracuseStep 20002781 = 7501043) B7501043
theorem B2193383 : Blo 1461050 2193383 := bstep (se 1 (by rfl) ⟨1645037, by rfl⟩ : syracuseStep 2193383 = 3290075) B3290075
theorem B2406391 : Blo 1461050 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B2193401 : Blo 1461050 2193401 := bstep (se 2 (by rfl) ⟨822525, by rfl⟩ : syracuseStep 2193401 = 1645051) B1645051
theorem B2193503 : Blo 1461050 2193503 := bstep (se 1 (by rfl) ⟨1645127, by rfl⟩ : syracuseStep 2193503 = 3290255) B3290255
theorem B2193563 : Blo 1461050 2193563 := bstep (se 1 (by rfl) ⟨1645172, by rfl⟩ : syracuseStep 2193563 = 3290345) B3290345
theorem B2193599 : Blo 1461050 2193599 := bstep (se 1 (by rfl) ⟨1645199, by rfl⟩ : syracuseStep 2193599 = 3290399) B3290399
theorem B2193641 : Blo 1461050 2193641 := bstep (se 2 (by rfl) ⟨822615, by rfl⟩ : syracuseStep 2193641 = 1645231) B1645231
theorem B21068039 : Blo 1461050 21068039 := bstep (se 1 (by rfl) ⟨15801029, by rfl⟩ : syracuseStep 21068039 = 31602059) B31602059
theorem B5265773 : Blo 1461050 5265773 := bstep (se 3 (by rfl) ⟨987332, by rfl⟩ : syracuseStep 5265773 = 1974665) B1974665
theorem B7403885 : Blo 1461050 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B16021871 : Blo 1461050 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B8894893 : Blo 1461050 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B1645087 : Blo 1461050 1645087 := bstep (se 1 (by rfl) ⟨1233815, by rfl⟩ : syracuseStep 1645087 = 2467631) B2467631
theorem B102816289 : Blo 1461050 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B3332665 : Blo 1461050 3332665 := bstep (se 2 (by rfl) ⟨1249749, by rfl⟩ : syracuseStep 3332665 = 2499499) B2499499
theorem B24984287 : Blo 1461050 24984287 := bstep (se 1 (by rfl) ⟨18738215, by rfl⟩ : syracuseStep 24984287 = 37476431) B37476431
theorem B5552975 : Blo 1461050 5552975 := bstep (se 1 (by rfl) ⟨4164731, by rfl⟩ : syracuseStep 5552975 = 8329463) B8329463
theorem B4275035 : Blo 1461050 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B3701609 : Blo 1461050 3701609 := bstep (se 2 (by rfl) ⟨1388103, by rfl⟩ : syracuseStep 3701609 = 2776207) B2776207
theorem B3701801 : Blo 1461050 3701801 := bstep (se 2 (by rfl) ⟨1388175, by rfl⟩ : syracuseStep 3701801 = 2776351) B2776351
theorem B12827729 : Blo 1461050 12827729 := bstep (se 2 (by rfl) ⟨4810398, by rfl⟩ : syracuseStep 12827729 = 9620797) B9620797
theorem B17775769 : Blo 1461050 17775769 := bstep (se 2 (by rfl) ⟨6665913, by rfl⟩ : syracuseStep 17775769 = 13331827) B13331827
theorem B81100061 : Blo 1461050 81100061 := bstep (se 3 (by rfl) ⟨15206261, by rfl⟩ : syracuseStep 81100061 = 30412523) B30412523
theorem B5627231 : Blo 1461050 5627231 := bstep (se 1 (by rfl) ⟨4220423, by rfl⟩ : syracuseStep 5627231 = 8440847) B8440847
theorem B3333487 : Blo 1461050 3333487 := bstep (se 1 (by rfl) ⟨2500115, by rfl⟩ : syracuseStep 3333487 = 5000231) B5000231
theorem B7601807 : Blo 1461050 7601807 := bstep (se 1 (by rfl) ⟨5701355, by rfl⟩ : syracuseStep 7601807 = 11402711) B11402711
theorem B5340859 : Blo 1461050 5340859 := bstep (se 1 (by rfl) ⟨4005644, by rfl⟩ : syracuseStep 5340859 = 8011289) B8011289
theorem B15802067 : Blo 1461050 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B7397243 : Blo 1461050 7397243 := bstep (se 1 (by rfl) ⟨5547932, by rfl⟩ : syracuseStep 7397243 = 11095865) B11095865
theorem B2465707 : Blo 1461050 2465707 := bstep (se 1 (by rfl) ⟨1849280, by rfl⟩ : syracuseStep 2465707 = 3698561) B3698561
theorem B4161451 : Blo 1461050 4161451 := bstep (se 1 (by rfl) ⟨3121088, by rfl⟩ : syracuseStep 4161451 = 6242177) B6242177
theorem B11854019 : Blo 1461050 11854019 := bstep (se 1 (by rfl) ⟨8890514, by rfl⟩ : syracuseStep 11854019 = 17781029) B17781029
theorem B18735299 : Blo 1461050 18735299 := bstep (se 1 (by rfl) ⟨14051474, by rfl⟩ : syracuseStep 18735299 = 28102949) B28102949
theorem B4931819 : Blo 1461050 4931819 := bstep (se 1 (by rfl) ⟨3698864, by rfl⟩ : syracuseStep 4931819 = 7397729) B7397729
theorem B54084503 : Blo 1461050 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B2466983 : Blo 1461050 2466983 := bstep (se 1 (by rfl) ⟨1850237, by rfl⟩ : syracuseStep 2466983 = 3700475) B3700475
theorem B18728171 : Blo 1461050 18728171 := bstep (se 1 (by rfl) ⟨14046128, by rfl⟩ : syracuseStep 18728171 = 28092257) B28092257
theorem B7021835 : Blo 1461050 7021835 := bstep (se 1 (by rfl) ⟨5266376, by rfl⟩ : syracuseStep 7021835 = 10532753) B10532753
theorem B2082127 : Blo 1461050 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B23701025 : Blo 1461050 23701025 := bstep (se 2 (by rfl) ⟨8887884, by rfl⟩ : syracuseStep 23701025 = 17775769) B17775769
theorem B16656191 : Blo 1461050 16656191 := bstep (se 1 (by rfl) ⟨12492143, by rfl⟩ : syracuseStep 16656191 = 24984287) B24984287
theorem B2467739 : Blo 1461050 2467739 := bstep (se 1 (by rfl) ⟨1850804, by rfl⟩ : syracuseStep 2467739 = 3701609) B3701609
theorem B2467867 : Blo 1461050 2467867 := bstep (se 1 (by rfl) ⟨1850900, by rfl⟩ : syracuseStep 2467867 = 3701801) B3701801
theorem B11855969 : Blo 1461050 11855969 := bstep (se 2 (by rfl) ⟨4445988, by rfl⟩ : syracuseStep 11855969 = 8891977) B8891977
theorem B3287609 : Blo 1461050 3287609 := bstep (se 2 (by rfl) ⟨1232853, by rfl⟩ : syracuseStep 3287609 = 2465707) B2465707
theorem B5548601 : Blo 1461050 5548601 := bstep (se 2 (by rfl) ⟨2080725, by rfl⟩ : syracuseStep 5548601 = 4161451) B4161451
theorem B4442971 : Blo 1461050 4442971 := bstep (se 1 (by rfl) ⟨3332228, by rfl⟩ : syracuseStep 4442971 = 6664457) B6664457
theorem B1461215 : Blo 1461050 1461215 := bstep (se 1 (by rfl) ⟨1095911, by rfl⟩ : syracuseStep 1461215 = 2191823) B2191823
theorem B1756127 : Blo 1461050 1756127 := bstep (se 1 (by rfl) ⟨1317095, by rfl⟩ : syracuseStep 1756127 = 2634191) B2634191
theorem B1461243 : Blo 1461050 1461243 := bstep (se 1 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 1461243 = 2191865) B2191865
theorem B1461311 : Blo 1461050 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B5549255 : Blo 1461050 5549255 := bstep (se 1 (by rfl) ⟨4161941, by rfl⟩ : syracuseStep 5549255 = 8323883) B8323883
theorem B3288329 : Blo 1461050 3288329 := bstep (se 2 (by rfl) ⟨1233123, by rfl⟩ : syracuseStep 3288329 = 2466247) B2466247
theorem B1461631 : Blo 1461050 1461631 := bstep (se 1 (by rfl) ⟨1096223, by rfl⟩ : syracuseStep 1461631 = 2192447) B2192447
theorem B137088385 : Blo 1461050 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B1461659 : Blo 1461050 1461659 := bstep (se 1 (by rfl) ⟨1096244, by rfl⟩ : syracuseStep 1461659 = 2192489) B2192489
theorem B4443553 : Blo 1461050 4443553 := bstep (se 2 (by rfl) ⟨1666332, by rfl⟩ : syracuseStep 4443553 = 3332665) B3332665
theorem B1461727 : Blo 1461050 1461727 := bstep (se 1 (by rfl) ⟨1096295, by rfl⟩ : syracuseStep 1461727 = 2192591) B2192591
theorem B1461863 : Blo 1461050 1461863 := bstep (se 1 (by rfl) ⟨1096397, by rfl⟩ : syracuseStep 1461863 = 2192795) B2192795
theorem B5549755 : Blo 1461050 5549755 := bstep (se 1 (by rfl) ⟨4162316, by rfl⟩ : syracuseStep 5549755 = 8324633) B8324633
theorem B1462011 : Blo 1461050 1462011 := bstep (se 1 (by rfl) ⟨1096508, by rfl⟩ : syracuseStep 1462011 = 2193017) B2193017
theorem B1462079 : Blo 1461050 1462079 := bstep (se 1 (by rfl) ⟨1096559, by rfl⟩ : syracuseStep 1462079 = 2193119) B2193119
theorem B1462143 : Blo 1461050 1462143 := bstep (se 1 (by rfl) ⟨1096607, by rfl⟩ : syracuseStep 1462143 = 2193215) B2193215
theorem B113938325 : Blo 1461050 113938325 := bstep (se 6 (by rfl) ⟨2670429, by rfl⟩ : syracuseStep 113938325 = 5340859) B5340859
theorem B1462255 : Blo 1461050 1462255 := bstep (se 1 (by rfl) ⟨1096691, by rfl⟩ : syracuseStep 1462255 = 2193383) B2193383
theorem B1462267 : Blo 1461050 1462267 := bstep (se 1 (by rfl) ⟨1096700, by rfl⟩ : syracuseStep 1462267 = 2193401) B2193401
theorem B1462335 : Blo 1461050 1462335 := bstep (se 1 (by rfl) ⟨1096751, by rfl⟩ : syracuseStep 1462335 = 2193503) B2193503
theorem B1462375 : Blo 1461050 1462375 := bstep (se 1 (by rfl) ⟨1096781, by rfl⟩ : syracuseStep 1462375 = 2193563) B2193563
theorem B1462399 : Blo 1461050 1462399 := bstep (se 1 (by rfl) ⟨1096799, by rfl⟩ : syracuseStep 1462399 = 2193599) B2193599
theorem B1462427 : Blo 1461050 1462427 := bstep (se 1 (by rfl) ⟨1096820, by rfl⟩ : syracuseStep 1462427 = 2193641) B2193641
theorem B14045359 : Blo 1461050 14045359 := bstep (se 1 (by rfl) ⟨10534019, by rfl⟩ : syracuseStep 14045359 = 21068039) B21068039
theorem B3289319 : Blo 1461050 3289319 := bstep (se 1 (by rfl) ⟨2466989, by rfl⟩ : syracuseStep 3289319 = 4933979) B4933979
theorem B3510515 : Blo 1461050 3510515 := bstep (se 1 (by rfl) ⟨2632886, by rfl⟩ : syracuseStep 3510515 = 5265773) B5265773
theorem B4935923 : Blo 1461050 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B3699047 : Blo 1461050 3699047 := bstep (se 1 (by rfl) ⟨2774285, by rfl⟩ : syracuseStep 3699047 = 5548571) B5548571
theorem B20271485 : Blo 1461050 20271485 := bstep (se 3 (by rfl) ⟨3800903, by rfl⟩ : syracuseStep 20271485 = 7601807) B7601807
theorem B2634139 : Blo 1461050 2634139 := bstep (se 1 (by rfl) ⟨1975604, by rfl⟩ : syracuseStep 2634139 = 3951209) B3951209
theorem B3289499 : Blo 1461050 3289499 := bstep (se 1 (by rfl) ⟨2467124, by rfl⟩ : syracuseStep 3289499 = 4934249) B4934249
theorem B4444649 : Blo 1461050 4444649 := bstep (se 2 (by rfl) ⟨1666743, by rfl⟩ : syracuseStep 4444649 = 3333487) B3333487
theorem B2192123 : Blo 1461050 2192123 := bstep (se 1 (by rfl) ⟨1644092, by rfl⟩ : syracuseStep 2192123 = 3288185) B3288185
theorem B59356079 : Blo 1461050 59356079 := bstep (se 1 (by rfl) ⟨44517059, by rfl⟩ : syracuseStep 59356079 = 89034119) B89034119
theorem B7402427 : Blo 1461050 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B18740267 : Blo 1461050 18740267 := bstep (se 1 (by rfl) ⟨14055200, by rfl⟩ : syracuseStep 18740267 = 28110401) B28110401
theorem B3290183 : Blo 1461050 3290183 := bstep (se 1 (by rfl) ⟨2467637, by rfl⟩ : syracuseStep 3290183 = 4935275) B4935275
theorem B51336341 : Blo 1461050 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B3511457 : Blo 1461050 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B2192567 : Blo 1461050 2192567 := bstep (se 1 (by rfl) ⟨1644425, by rfl⟩ : syracuseStep 2192567 = 3288851) B3288851
theorem B3290363 : Blo 1461050 3290363 := bstep (se 1 (by rfl) ⟨2467772, by rfl⟩ : syracuseStep 3290363 = 4935545) B4935545
theorem B2192807 : Blo 1461050 2192807 := bstep (se 1 (by rfl) ⟨1644605, by rfl⟩ : syracuseStep 2192807 = 3289211) B3289211
theorem B3290579 : Blo 1461050 3290579 := bstep (se 1 (by rfl) ⟨2467934, by rfl⟩ : syracuseStep 3290579 = 4935869) B4935869
theorem B1644007 : Blo 1461050 1644007 := bstep (se 1 (by rfl) ⟨1233005, by rfl⟩ : syracuseStep 1644007 = 2466011) B2466011
theorem B34207277 : Blo 1461050 34207277 := bstep (se 3 (by rfl) ⟨6413864, by rfl⟩ : syracuseStep 34207277 = 12827729) B12827729
theorem B2192987 : Blo 1461050 2192987 := bstep (se 1 (by rfl) ⟨1644740, by rfl⟩ : syracuseStep 2192987 = 3289481) B3289481
theorem B2774665 : Blo 1461050 2774665 := bstep (se 2 (by rfl) ⟨1040499, by rfl⟩ : syracuseStep 2774665 = 2080999) B2080999
theorem B1644187 : Blo 1461050 1644187 := bstep (se 1 (by rfl) ⟨1233140, by rfl⟩ : syracuseStep 1644187 = 2466281) B2466281
theorem B11859857 : Blo 1461050 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B22493159 : Blo 1461050 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B2193449 : Blo 1461050 2193449 := bstep (se 2 (by rfl) ⟨822543, by rfl⟩ : syracuseStep 2193449 = 1645087) B1645087
theorem B2193479 : Blo 1461050 2193479 := bstep (se 1 (by rfl) ⟨1645109, by rfl⟩ : syracuseStep 2193479 = 3290219) B3290219
theorem B15808607 : Blo 1461050 15808607 := bstep (se 1 (by rfl) ⟨11856455, by rfl⟩ : syracuseStep 15808607 = 23712911) B23712911
theorem B7403723 : Blo 1461050 7403723 := bstep (se 1 (by rfl) ⟨5552792, by rfl⟩ : syracuseStep 7403723 = 11105585) B11105585
theorem B2775379 : Blo 1461050 2775379 := bstep (se 1 (by rfl) ⟨2081534, by rfl⟩ : syracuseStep 2775379 = 4163069) B4163069
theorem B2775455 : Blo 1461050 2775455 := bstep (se 1 (by rfl) ⟨2081591, by rfl⟩ : syracuseStep 2775455 = 4163183) B4163183
theorem B1849807 : Blo 1461050 1849807 := bstep (se 1 (by rfl) ⟨1387355, by rfl⟩ : syracuseStep 1849807 = 2774711) B2774711
theorem B7903801 : Blo 1461050 7903801 := bstep (se 2 (by rfl) ⟨2963925, by rfl⟩ : syracuseStep 7903801 = 5927851) B5927851
theorem B13335187 : Blo 1461050 13335187 := bstep (se 1 (by rfl) ⟨10001390, by rfl⟩ : syracuseStep 13335187 = 20002781) B20002781
theorem B11098781 : Blo 1461050 11098781 := bstep (se 3 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 11098781 = 4162043) B4162043
theorem B2775865 : Blo 1461050 2775865 := bstep (se 2 (by rfl) ⟨1040949, by rfl⟩ : syracuseStep 2775865 = 2081899) B2081899
theorem B10681247 : Blo 1461050 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B3701983 : Blo 1461050 3701983 := bstep (se 1 (by rfl) ⟨2776487, by rfl⟩ : syracuseStep 3701983 = 5552975) B5552975
theorem B2850023 : Blo 1461050 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B54066707 : Blo 1461050 54066707 := bstep (se 1 (by rfl) ⟨40550030, by rfl⟩ : syracuseStep 54066707 = 81100061) B81100061
theorem B3751487 : Blo 1461050 3751487 := bstep (se 1 (by rfl) ⟨2813615, by rfl⟩ : syracuseStep 3751487 = 5627231) B5627231
theorem B19996379 : Blo 1461050 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B3333907 : Blo 1461050 3333907 := bstep (se 1 (by rfl) ⟨2500430, by rfl⟩ : syracuseStep 3333907 = 5000861) B5000861
theorem B10534711 : Blo 1461050 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B4931495 : Blo 1461050 4931495 := bstep (se 1 (by rfl) ⟨3698621, by rfl⟩ : syracuseStep 4931495 = 7397243) B7397243
theorem B2924552213 : Blo 1461050 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B18727145 : Blo 1461050 18727145 := bstep (se 2 (by rfl) ⟨7022679, by rfl⟩ : syracuseStep 18727145 = 14045359) B14045359
theorem B2466031 : Blo 1461050 2466031 := bstep (se 1 (by rfl) ⟨1849523, by rfl⟩ : syracuseStep 2466031 = 3699047) B3699047
theorem B2466409 : Blo 1461050 2466409 := bstep (se 2 (by rfl) ⟨924903, by rfl⟩ : syracuseStep 2466409 = 1849807) B1849807
theorem B12493511 : Blo 1461050 12493511 := bstep (se 1 (by rfl) ⟨9370133, by rfl⟩ : syracuseStep 12493511 = 18740267) B18740267
theorem B12485447 : Blo 1461050 12485447 := bstep (se 1 (by rfl) ⟨9364085, by rfl⟩ : syracuseStep 12485447 = 18728171) B18728171
theorem B5923961 : Blo 1461050 5923961 := bstep (se 2 (by rfl) ⟨2221485, by rfl⟩ : syracuseStep 5923961 = 4442971) B4442971
theorem B7906571 : Blo 1461050 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B91219405 : Blo 1461050 91219405 := bstep (se 3 (by rfl) ⟨17103638, by rfl⟩ : syracuseStep 91219405 = 34207277) B34207277
theorem B7399187 : Blo 1461050 7399187 := bstep (se 1 (by rfl) ⟨5549390, by rfl⟩ : syracuseStep 7399187 = 11098781) B11098781
theorem B5924737 : Blo 1461050 5924737 := bstep (se 2 (by rfl) ⟨2221776, by rfl⟩ : syracuseStep 5924737 = 4443553) B4443553
theorem B7120831 : Blo 1461050 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B2532526037 : Blo 1461050 2532526037 := bstep (se 7 (by rfl) ⟨29678039, by rfl⟩ : syracuseStep 2532526037 = 59356079) B59356079
theorem B7399673 : Blo 1461050 7399673 := bstep (se 2 (by rfl) ⟨2774877, by rfl⟩ : syracuseStep 7399673 = 5549755) B5549755
theorem B2500991 : Blo 1461050 2500991 := bstep (se 1 (by rfl) ⟨1875743, by rfl⟩ : syracuseStep 2500991 = 3751487) B3751487
theorem B13330919 : Blo 1461050 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B75958883 : Blo 1461050 75958883 := bstep (se 1 (by rfl) ⟨56969162, by rfl⟩ : syracuseStep 75958883 = 113938325) B113938325
theorem B3287663 : Blo 1461050 3287663 := bstep (se 1 (by rfl) ⟨2465747, by rfl⟩ : syracuseStep 3287663 = 4931495) B4931495
theorem B3287879 : Blo 1461050 3287879 := bstep (se 1 (by rfl) ⟨2465909, by rfl⟩ : syracuseStep 3287879 = 4931819) B4931819
theorem B1461415 : Blo 1461050 1461415 := bstep (se 1 (by rfl) ⟨1096061, by rfl⟩ : syracuseStep 1461415 = 2192123) B2192123
theorem B36056335 : Blo 1461050 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B4934951 : Blo 1461050 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B1461711 : Blo 1461050 1461711 := bstep (se 1 (by rfl) ⟨1096283, by rfl⟩ : syracuseStep 1461711 = 2192567) B2192567
theorem B4681223 : Blo 1461050 4681223 := bstep (se 1 (by rfl) ⟨3510917, by rfl⟩ : syracuseStep 4681223 = 7021835) B7021835
theorem B17780249 : Blo 1461050 17780249 := bstep (se 2 (by rfl) ⟨6667593, by rfl⟩ : syracuseStep 17780249 = 13335187) B13335187
theorem B1461871 : Blo 1461050 1461871 := bstep (se 1 (by rfl) ⟨1096403, by rfl⟩ : syracuseStep 1461871 = 2192807) B2192807
theorem B1461991 : Blo 1461050 1461991 := bstep (se 1 (by rfl) ⟨1096493, by rfl⟩ : syracuseStep 1461991 = 2192987) B2192987
theorem B11104127 : Blo 1461050 11104127 := bstep (se 1 (by rfl) ⟨8328095, by rfl⟩ : syracuseStep 11104127 = 16656191) B16656191
theorem B14995439 : Blo 1461050 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B1462299 : Blo 1461050 1462299 := bstep (se 1 (by rfl) ⟨1096724, by rfl⟩ : syracuseStep 1462299 = 2193449) B2193449
theorem B1462319 : Blo 1461050 1462319 := bstep (se 1 (by rfl) ⟨1096739, by rfl⟩ : syracuseStep 1462319 = 2193479) B2193479
theorem B10539071 : Blo 1461050 10539071 := bstep (se 1 (by rfl) ⟨7904303, by rfl⟩ : syracuseStep 10539071 = 15808607) B15808607
theorem B4935815 : Blo 1461050 4935815 := bstep (se 1 (by rfl) ⟨3701861, by rfl⟩ : syracuseStep 4935815 = 7403723) B7403723
theorem B4935977 : Blo 1461050 4935977 := bstep (se 2 (by rfl) ⟨1850991, by rfl⟩ : syracuseStep 4935977 = 3701983) B3701983
theorem B2191739 : Blo 1461050 2191739 := bstep (se 1 (by rfl) ⟨1643804, by rfl⟩ : syracuseStep 2191739 = 3287609) B3287609
theorem B3699067 : Blo 1461050 3699067 := bstep (se 1 (by rfl) ⟨2774300, by rfl⟩ : syracuseStep 3699067 = 5548601) B5548601
theorem B2192009 : Blo 1461050 2192009 := bstep (se 2 (by rfl) ⟨822003, by rfl⟩ : syracuseStep 2192009 = 1644007) B1644007
theorem B3699503 : Blo 1461050 3699503 := bstep (se 1 (by rfl) ⟨2774627, by rfl⟩ : syracuseStep 3699503 = 5549255) B5549255
theorem B2192219 : Blo 1461050 2192219 := bstep (se 1 (by rfl) ⟨1644164, by rfl⟩ : syracuseStep 2192219 = 3288329) B3288329
theorem B3699553 : Blo 1461050 3699553 := bstep (se 2 (by rfl) ⟨1387332, by rfl⟩ : syracuseStep 3699553 = 2774665) B2774665
theorem B2192249 : Blo 1461050 2192249 := bstep (se 2 (by rfl) ⟨822093, by rfl⟩ : syracuseStep 2192249 = 1644187) B1644187
theorem B4445209 : Blo 1461050 4445209 := bstep (se 2 (by rfl) ⟨1666953, by rfl⟩ : syracuseStep 4445209 = 3333907) B3333907
theorem B14046281 : Blo 1461050 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B4683005 : Blo 1461050 4683005 := bstep (se 3 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 4683005 = 1756127) B1756127
theorem B3290489 : Blo 1461050 3290489 := bstep (se 2 (by rfl) ⟨1233933, by rfl⟩ : syracuseStep 3290489 = 2467867) B2467867
theorem B7902679 : Blo 1461050 7902679 := bstep (se 1 (by rfl) ⟨5927009, by rfl⟩ : syracuseStep 7902679 = 11854019) B11854019
theorem B12490199 : Blo 1461050 12490199 := bstep (se 1 (by rfl) ⟨9367649, by rfl⟩ : syracuseStep 12490199 = 18735299) B18735299
theorem B2192879 : Blo 1461050 2192879 := bstep (se 1 (by rfl) ⟨1644659, by rfl⟩ : syracuseStep 2192879 = 3289319) B3289319
theorem B2340343 : Blo 1461050 2340343 := bstep (se 1 (by rfl) ⟨1755257, by rfl⟩ : syracuseStep 2340343 = 3510515) B3510515
theorem B3290615 : Blo 1461050 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B13514323 : Blo 1461050 13514323 := bstep (se 1 (by rfl) ⟨10135742, by rfl⟩ : syracuseStep 13514323 = 20271485) B20271485
theorem B2192999 : Blo 1461050 2192999 := bstep (se 1 (by rfl) ⟨1644749, by rfl⟩ : syracuseStep 2192999 = 3289499) B3289499
theorem B42153605 : Blo 1461050 42153605 := bstep (se 4 (by rfl) ⟨3951900, by rfl⟩ : syracuseStep 42153605 = 7903801) B7903801
theorem B2963099 : Blo 1461050 2963099 := bstep (se 1 (by rfl) ⟨2222324, by rfl⟩ : syracuseStep 2963099 = 4444649) B4444649
theorem B3700505 : Blo 1461050 3700505 := bstep (se 2 (by rfl) ⟨1387689, by rfl⟩ : syracuseStep 3700505 = 2775379) B2775379
theorem B7600061 : Blo 1461050 7600061 := bstep (se 3 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 7600061 = 2850023) B2850023
theorem B2193455 : Blo 1461050 2193455 := bstep (se 1 (by rfl) ⟨1645091, by rfl⟩ : syracuseStep 2193455 = 3290183) B3290183
theorem B34224227 : Blo 1461050 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B2340971 : Blo 1461050 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B1644655 : Blo 1461050 1644655 := bstep (se 1 (by rfl) ⟨1233491, by rfl⟩ : syracuseStep 1644655 = 2466983) B2466983
theorem B2193575 : Blo 1461050 2193575 := bstep (se 1 (by rfl) ⟨1645181, by rfl⟩ : syracuseStep 2193575 = 3290363) B3290363
theorem B2193719 : Blo 1461050 2193719 := bstep (se 1 (by rfl) ⟨1645289, by rfl⟩ : syracuseStep 2193719 = 3290579) B3290579
theorem B15800683 : Blo 1461050 15800683 := bstep (se 1 (by rfl) ⟨11850512, by rfl⟩ : syracuseStep 15800683 = 23701025) B23701025
theorem B3701153 : Blo 1461050 3701153 := bstep (se 2 (by rfl) ⟨1387932, by rfl⟩ : syracuseStep 3701153 = 2775865) B2775865
theorem B1645159 : Blo 1461050 1645159 := bstep (se 1 (by rfl) ⟨1233869, by rfl⟩ : syracuseStep 1645159 = 2467739) B2467739
theorem B7903979 : Blo 1461050 7903979 := bstep (se 1 (by rfl) ⟨5927984, by rfl⟩ : syracuseStep 7903979 = 11855969) B11855969
theorem B1850303 : Blo 1461050 1850303 := bstep (se 1 (by rfl) ⟨1387727, by rfl⟩ : syracuseStep 1850303 = 2775455) B2775455
theorem B2776169 : Blo 1461050 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B14048741 : Blo 1461050 14048741 := bstep (se 4 (by rfl) ⟨1317069, by rfl⟩ : syracuseStep 14048741 = 2634139) B2634139
theorem B36044471 : Blo 1461050 36044471 := bstep (se 1 (by rfl) ⟨27033353, by rfl⟩ : syracuseStep 36044471 = 54066707) B54066707
theorem B12484763 : Blo 1461050 12484763 := bstep (se 1 (by rfl) ⟨9363572, by rfl⟩ : syracuseStep 12484763 = 18727145) B18727145
theorem B4932089 : Blo 1461050 4932089 := bstep (se 2 (by rfl) ⟨1849533, by rfl⟩ : syracuseStep 4932089 = 3699067) B3699067
theorem B2466335 : Blo 1461050 2466335 := bstep (se 1 (by rfl) ⟨1849751, by rfl⟩ : syracuseStep 2466335 = 3699503) B3699503
theorem B8323631 : Blo 1461050 8323631 := bstep (se 1 (by rfl) ⟨6242723, by rfl⟩ : syracuseStep 8323631 = 12485447) B12485447
theorem B9364187 : Blo 1461050 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B3949307 : Blo 1461050 3949307 := bstep (se 1 (by rfl) ⟨2961980, by rfl⟩ : syracuseStep 3949307 = 5923961) B5923961
theorem B3122003 : Blo 1461050 3122003 := bstep (se 1 (by rfl) ⟨2341502, by rfl⟩ : syracuseStep 3122003 = 4683005) B4683005
theorem B4932737 : Blo 1461050 4932737 := bstep (se 2 (by rfl) ⟨1849776, by rfl⟩ : syracuseStep 4932737 = 3699553) B3699553
theorem B4932791 : Blo 1461050 4932791 := bstep (se 1 (by rfl) ⟨3699593, by rfl⟩ : syracuseStep 4932791 = 7399187) B7399187
theorem B2467003 : Blo 1461050 2467003 := bstep (se 1 (by rfl) ⟨1850252, by rfl⟩ : syracuseStep 2467003 = 3700505) B3700505
theorem B37463309 : Blo 1461050 37463309 := bstep (se 3 (by rfl) ⟨7024370, by rfl⟩ : syracuseStep 37463309 = 14048741) B14048741
theorem B22816151 : Blo 1461050 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B4933115 : Blo 1461050 4933115 := bstep (se 1 (by rfl) ⟨3699836, by rfl⟩ : syracuseStep 4933115 = 7399673) B7399673
theorem B2467435 : Blo 1461050 2467435 := bstep (se 1 (by rfl) ⟨1850576, by rfl⟩ : syracuseStep 2467435 = 3701153) B3701153
theorem B96118589 : Blo 1461050 96118589 := bstep (se 3 (by rfl) ⟨18022235, by rfl⟩ : syracuseStep 96118589 = 36044471) B36044471
theorem B5269319 : Blo 1461050 5269319 := bstep (se 1 (by rfl) ⟨3951989, by rfl⟩ : syracuseStep 5269319 = 7903979) B7903979
theorem B10536905 : Blo 1461050 10536905 := bstep (se 2 (by rfl) ⟨3951339, by rfl⟩ : syracuseStep 10536905 = 7902679) B7902679
theorem B4934141 : Blo 1461050 4934141 := bstep (se 3 (by rfl) ⟨925151, by rfl⟩ : syracuseStep 4934141 = 1850303) B1850303
theorem B7899649 : Blo 1461050 7899649 := bstep (se 2 (by rfl) ⟨2962368, by rfl⟩ : syracuseStep 7899649 = 5924737) B5924737
theorem B9996959 : Blo 1461050 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B1461159 : Blo 1461050 1461159 := bstep (se 1 (by rfl) ⟨1095869, by rfl⟩ : syracuseStep 1461159 = 2191739) B2191739
theorem B3288041 : Blo 1461050 3288041 := bstep (se 2 (by rfl) ⟨1233015, by rfl⟩ : syracuseStep 3288041 = 2466031) B2466031
theorem B1461339 : Blo 1461050 1461339 := bstep (se 1 (by rfl) ⟨1096004, by rfl⟩ : syracuseStep 1461339 = 2192009) B2192009
theorem B1461479 : Blo 1461050 1461479 := bstep (se 1 (by rfl) ⟨1096109, by rfl⟩ : syracuseStep 1461479 = 2192219) B2192219
theorem B1461499 : Blo 1461050 1461499 := bstep (se 1 (by rfl) ⟨1096124, by rfl⟩ : syracuseStep 1461499 = 2192249) B2192249
theorem B3288545 : Blo 1461050 3288545 := bstep (se 2 (by rfl) ⟨1233204, by rfl⟩ : syracuseStep 3288545 = 2466409) B2466409
theorem B5271047 : Blo 1461050 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B8326799 : Blo 1461050 8326799 := bstep (se 1 (by rfl) ⟨6245099, by rfl⟩ : syracuseStep 8326799 = 12490199) B12490199
theorem B1461919 : Blo 1461050 1461919 := bstep (se 1 (by rfl) ⟨1096439, by rfl⟩ : syracuseStep 1461919 = 2192879) B2192879
theorem B1461999 : Blo 1461050 1461999 := bstep (se 1 (by rfl) ⟨1096499, by rfl⟩ : syracuseStep 1461999 = 2192999) B2192999
theorem B28102403 : Blo 1461050 28102403 := bstep (se 1 (by rfl) ⟨21076802, by rfl⟩ : syracuseStep 28102403 = 42153605) B42153605
theorem B35549117 : Blo 1461050 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B5066707 : Blo 1461050 5066707 := bstep (se 1 (by rfl) ⟨3800030, by rfl⟩ : syracuseStep 5066707 = 7600061) B7600061
theorem B1688350691 : Blo 1461050 1688350691 := bstep (se 1 (by rfl) ⟨1266263018, by rfl⟩ : syracuseStep 1688350691 = 2532526037) B2532526037
theorem B1462303 : Blo 1461050 1462303 := bstep (se 1 (by rfl) ⟨1096727, by rfl⟩ : syracuseStep 1462303 = 2193455) B2193455
theorem B5926945 : Blo 1461050 5926945 := bstep (se 2 (by rfl) ⟨2222604, by rfl⟩ : syracuseStep 5926945 = 4445209) B4445209
theorem B1560647 : Blo 1461050 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B1462383 : Blo 1461050 1462383 := bstep (se 1 (by rfl) ⟨1096787, by rfl⟩ : syracuseStep 1462383 = 2193575) B2193575
theorem B1462479 : Blo 1461050 1462479 := bstep (se 1 (by rfl) ⟨1096859, by rfl⟩ : syracuseStep 1462479 = 2193719) B2193719
theorem B1667327 : Blo 1461050 1667327 := bstep (se 1 (by rfl) ⟨1250495, by rfl⟩ : syracuseStep 1667327 = 2500991) B2500991
theorem B48075113 : Blo 1461050 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B50639255 : Blo 1461050 50639255 := bstep (se 1 (by rfl) ⟨37979441, by rfl⟩ : syracuseStep 50639255 = 75958883) B75958883
theorem B7901597 : Blo 1461050 7901597 := bstep (se 3 (by rfl) ⟨1481549, by rfl⟩ : syracuseStep 7901597 = 2963099) B2963099
theorem B2191775 : Blo 1461050 2191775 := bstep (se 1 (by rfl) ⟨1643831, by rfl⟩ : syracuseStep 2191775 = 3287663) B3287663
theorem B2191919 : Blo 1461050 2191919 := bstep (se 1 (by rfl) ⟨1643939, by rfl⟩ : syracuseStep 2191919 = 3287879) B3287879
theorem B18019097 : Blo 1461050 18019097 := bstep (se 2 (by rfl) ⟨6757161, by rfl⟩ : syracuseStep 18019097 = 13514323) B13514323
theorem B3289967 : Blo 1461050 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B7402751 : Blo 1461050 7402751 := bstep (se 1 (by rfl) ⟨5552063, by rfl⟩ : syracuseStep 7402751 = 11104127) B11104127
theorem B1949701475 : Blo 1461050 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B7026047 : Blo 1461050 7026047 := bstep (se 1 (by rfl) ⟨5269535, by rfl⟩ : syracuseStep 7026047 = 10539071) B10539071
theorem B3290543 : Blo 1461050 3290543 := bstep (se 1 (by rfl) ⟨2467907, by rfl⟩ : syracuseStep 3290543 = 4935815) B4935815
theorem B2192873 : Blo 1461050 2192873 := bstep (se 2 (by rfl) ⟨822327, by rfl⟩ : syracuseStep 2192873 = 1644655) B1644655
theorem B3290651 : Blo 1461050 3290651 := bstep (se 1 (by rfl) ⟨2467988, by rfl⟩ : syracuseStep 3290651 = 4935977) B4935977
theorem B8329007 : Blo 1461050 8329007 := bstep (se 1 (by rfl) ⟨6246755, by rfl⟩ : syracuseStep 8329007 = 12493511) B12493511
theorem B21067577 : Blo 1461050 21067577 := bstep (se 2 (by rfl) ⟨7900341, by rfl⟩ : syracuseStep 21067577 = 15800683) B15800683
theorem B2193545 : Blo 1461050 2193545 := bstep (se 2 (by rfl) ⟨822579, by rfl⟩ : syracuseStep 2193545 = 1645159) B1645159
theorem B2193659 : Blo 1461050 2193659 := bstep (se 1 (by rfl) ⟨1645244, by rfl⟩ : syracuseStep 2193659 = 3290489) B3290489
theorem B2193743 : Blo 1461050 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B121625873 : Blo 1461050 121625873 := bstep (se 2 (by rfl) ⟨45609702, by rfl⟩ : syracuseStep 121625873 = 91219405) B91219405
theorem B3120457 : Blo 1461050 3120457 := bstep (se 2 (by rfl) ⟨1170171, by rfl⟩ : syracuseStep 3120457 = 2340343) B2340343
theorem B1850779 : Blo 1461050 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B3120815 : Blo 1461050 3120815 := bstep (se 1 (by rfl) ⟨2340611, by rfl⟩ : syracuseStep 3120815 = 4681223) B4681223
theorem B11853499 : Blo 1461050 11853499 := bstep (se 1 (by rfl) ⟨8890124, by rfl⟩ : syracuseStep 11853499 = 17780249) B17780249
theorem B9494441 : Blo 1461050 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B42131461 : Blo 1461050 42131461 := bstep (se 4 (by rfl) ⟨3949824, by rfl⟩ : syracuseStep 42131461 = 7899649) B7899649
theorem B8323175 : Blo 1461050 8323175 := bstep (se 1 (by rfl) ⟨6242381, by rfl⟩ : syracuseStep 8323175 = 12484763) B12484763
theorem B4161725 : Blo 1461050 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B33759503 : Blo 1461050 33759503 := bstep (se 1 (by rfl) ⟨25319627, by rfl⟩ : syracuseStep 33759503 = 50639255) B50639255
theorem B21070925 : Blo 1461050 21070925 := bstep (se 3 (by rfl) ⟨3950798, by rfl⟩ : syracuseStep 21070925 = 7901597) B7901597
theorem B64079059 : Blo 1461050 64079059 := bstep (se 1 (by rfl) ⟨48059294, by rfl⟩ : syracuseStep 64079059 = 96118589) B96118589
theorem B2467705 : Blo 1461050 2467705 := bstep (se 2 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 2467705 = 1850779) B1850779
theorem B24971165 : Blo 1461050 24971165 := bstep (se 3 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 24971165 = 9364187) B9364187
theorem B8325341 : Blo 1461050 8325341 := bstep (se 3 (by rfl) ⟨1561001, by rfl⟩ : syracuseStep 8325341 = 3122003) B3122003
theorem B15804665 : Blo 1461050 15804665 := bstep (se 2 (by rfl) ⟨5926749, by rfl⟩ : syracuseStep 15804665 = 11853499) B11853499
theorem B1125567127 : Blo 1461050 1125567127 := bstep (se 1 (by rfl) ⟨844175345, by rfl⟩ : syracuseStep 1125567127 = 1688350691) B1688350691
theorem B32050075 : Blo 1461050 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B1461183 : Blo 1461050 1461183 := bstep (se 1 (by rfl) ⟨1095887, by rfl⟩ : syracuseStep 1461183 = 2191775) B2191775
theorem B3288059 : Blo 1461050 3288059 := bstep (se 1 (by rfl) ⟨2466044, by rfl⟩ : syracuseStep 3288059 = 4932089) B4932089
theorem B1461279 : Blo 1461050 1461279 := bstep (se 1 (by rfl) ⟨1095959, by rfl⟩ : syracuseStep 1461279 = 2191919) B2191919
theorem B5549087 : Blo 1461050 5549087 := bstep (se 1 (by rfl) ⟨4161815, by rfl⟩ : syracuseStep 5549087 = 8323631) B8323631
theorem B2632871 : Blo 1461050 2632871 := bstep (se 1 (by rfl) ⟨1974653, by rfl⟩ : syracuseStep 2632871 = 3949307) B3949307
theorem B12012731 : Blo 1461050 12012731 := bstep (se 1 (by rfl) ⟨9009548, by rfl⟩ : syracuseStep 12012731 = 18019097) B18019097
theorem B3288491 : Blo 1461050 3288491 := bstep (se 1 (by rfl) ⟨2466368, by rfl⟩ : syracuseStep 3288491 = 4932737) B4932737
theorem B3288527 : Blo 1461050 3288527 := bstep (se 1 (by rfl) ⟨2466395, by rfl⟩ : syracuseStep 3288527 = 4932791) B4932791
theorem B4935167 : Blo 1461050 4935167 := bstep (se 1 (by rfl) ⟨3701375, by rfl⟩ : syracuseStep 4935167 = 7402751) B7402751
theorem B5199203933 : Blo 1461050 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B1461915 : Blo 1461050 1461915 := bstep (se 1 (by rfl) ⟨1096436, by rfl⟩ : syracuseStep 1461915 = 2192873) B2192873
theorem B3288743 : Blo 1461050 3288743 := bstep (se 1 (by rfl) ⟨2466557, by rfl⟩ : syracuseStep 3288743 = 4933115) B4933115
theorem B14045051 : Blo 1461050 14045051 := bstep (se 1 (by rfl) ⟨10533788, by rfl⟩ : syracuseStep 14045051 = 21067577) B21067577
theorem B7024603 : Blo 1461050 7024603 := bstep (se 1 (by rfl) ⟨5268452, by rfl⟩ : syracuseStep 7024603 = 10536905) B10536905
theorem B1462363 : Blo 1461050 1462363 := bstep (se 1 (by rfl) ⟨1096772, by rfl⟩ : syracuseStep 1462363 = 2193545) B2193545
theorem B1462439 : Blo 1461050 1462439 := bstep (se 1 (by rfl) ⟨1096829, by rfl⟩ : syracuseStep 1462439 = 2193659) B2193659
theorem B1462495 : Blo 1461050 1462495 := bstep (se 1 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 1462495 = 2193743) B2193743
theorem B3289337 : Blo 1461050 3289337 := bstep (se 2 (by rfl) ⟨1233501, by rfl⟩ : syracuseStep 3289337 = 2467003) B2467003
theorem B3289427 : Blo 1461050 3289427 := bstep (se 1 (by rfl) ⟨2467070, by rfl⟩ : syracuseStep 3289427 = 4934141) B4934141
theorem B6664639 : Blo 1461050 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B2192027 : Blo 1461050 2192027 := bstep (se 1 (by rfl) ⟨1644020, by rfl⟩ : syracuseStep 2192027 = 3288041) B3288041
theorem B3289913 : Blo 1461050 3289913 := bstep (se 2 (by rfl) ⟨1233717, by rfl⟩ : syracuseStep 3289913 = 2467435) B2467435
theorem B2192363 : Blo 1461050 2192363 := bstep (se 1 (by rfl) ⟨1644272, by rfl⟩ : syracuseStep 2192363 = 3288545) B3288545
theorem B5551199 : Blo 1461050 5551199 := bstep (se 1 (by rfl) ⟨4163399, by rfl⟩ : syracuseStep 5551199 = 8326799) B8326799
theorem B6755609 : Blo 1461050 6755609 := bstep (se 2 (by rfl) ⟨2533353, by rfl⟩ : syracuseStep 6755609 = 5066707) B5066707
theorem B6329627 : Blo 1461050 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B7902593 : Blo 1461050 7902593 := bstep (se 2 (by rfl) ⟨2963472, by rfl⟩ : syracuseStep 7902593 = 5926945) B5926945
theorem B1644223 : Blo 1461050 1644223 := bstep (se 1 (by rfl) ⟨1233167, by rfl⟩ : syracuseStep 1644223 = 2466335) B2466335
theorem B2193311 : Blo 1461050 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B24975539 : Blo 1461050 24975539 := bstep (se 1 (by rfl) ⟨18731654, by rfl⟩ : syracuseStep 24975539 = 37463309) B37463309
theorem B4684031 : Blo 1461050 4684031 := bstep (se 1 (by rfl) ⟨3513023, by rfl⟩ : syracuseStep 4684031 = 7026047) B7026047
theorem B15210767 : Blo 1461050 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B2193695 : Blo 1461050 2193695 := bstep (se 1 (by rfl) ⟨1645271, by rfl⟩ : syracuseStep 2193695 = 3290543) B3290543
theorem B2193767 : Blo 1461050 2193767 := bstep (se 1 (by rfl) ⟨1645325, by rfl⟩ : syracuseStep 2193767 = 3290651) B3290651
theorem B5552671 : Blo 1461050 5552671 := bstep (se 1 (by rfl) ⟨4164503, by rfl⟩ : syracuseStep 5552671 = 8329007) B8329007
theorem B3512879 : Blo 1461050 3512879 := bstep (se 1 (by rfl) ⟨2634659, by rfl⟩ : syracuseStep 3512879 = 5269319) B5269319
theorem B4160609 : Blo 1461050 4160609 := bstep (se 2 (by rfl) ⟨1560228, by rfl⟩ : syracuseStep 4160609 = 3120457) B3120457
theorem B8322173 : Blo 1461050 8322173 := bstep (se 3 (by rfl) ⟨1560407, by rfl⟩ : syracuseStep 8322173 = 3120815) B3120815
theorem B81083915 : Blo 1461050 81083915 := bstep (se 1 (by rfl) ⟨60812936, by rfl⟩ : syracuseStep 81083915 = 121625873) B121625873
theorem B3514031 : Blo 1461050 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B18734935 : Blo 1461050 18734935 := bstep (se 1 (by rfl) ⟨14051201, by rfl⟩ : syracuseStep 18734935 = 28102403) B28102403
theorem B23699411 : Blo 1461050 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B17784821 : Blo 1461050 17784821 := bstep (se 5 (by rfl) ⟨833663, by rfl⟩ : syracuseStep 17784821 = 1667327) B1667327
theorem B7020989 : Blo 1461050 7020989 := bstep (se 3 (by rfl) ⟨1316435, by rfl⟩ : syracuseStep 7020989 = 2632871) B2632871
theorem B18014957 : Blo 1461050 18014957 := bstep (se 3 (by rfl) ⟨3377804, by rfl⟩ : syracuseStep 18014957 = 6755609) B6755609
theorem B4219751 : Blo 1461050 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B5268395 : Blo 1461050 5268395 := bstep (se 1 (by rfl) ⟨3951296, by rfl⟩ : syracuseStep 5268395 = 7902593) B7902593
theorem B16647443 : Blo 1461050 16647443 := bstep (se 1 (by rfl) ⟨12485582, by rfl⟩ : syracuseStep 16647443 = 24971165) B24971165
theorem B10536443 : Blo 1461050 10536443 := bstep (se 1 (by rfl) ⟨7902332, by rfl⟩ : syracuseStep 10536443 = 15804665) B15804665
theorem B3122687 : Blo 1461050 3122687 := bstep (se 1 (by rfl) ⟨2342015, by rfl⟩ : syracuseStep 3122687 = 4684031) B4684031
theorem B5548115 : Blo 1461050 5548115 := bstep (se 1 (by rfl) ⟨4161086, by rfl⟩ : syracuseStep 5548115 = 8322173) B8322173
theorem B3466135955 : Blo 1461050 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B24979913 : Blo 1461050 24979913 := bstep (se 2 (by rfl) ⟨9367467, by rfl⟩ : syracuseStep 24979913 = 18734935) B18734935
theorem B9366137 : Blo 1461050 9366137 := bstep (se 2 (by rfl) ⟨3512301, by rfl⟩ : syracuseStep 9366137 = 7024603) B7024603
theorem B11856547 : Blo 1461050 11856547 := bstep (se 1 (by rfl) ⟨8892410, by rfl⟩ : syracuseStep 11856547 = 17784821) B17784821
theorem B56175281 : Blo 1461050 56175281 := bstep (se 2 (by rfl) ⟨21065730, by rfl⟩ : syracuseStep 56175281 = 42131461) B42131461
theorem B5548783 : Blo 1461050 5548783 := bstep (se 1 (by rfl) ⟨4161587, by rfl⟩ : syracuseStep 5548783 = 8323175) B8323175
theorem B22506335 : Blo 1461050 22506335 := bstep (se 1 (by rfl) ⟨16879751, by rfl⟩ : syracuseStep 22506335 = 33759503) B33759503
theorem B1461351 : Blo 1461050 1461351 := bstep (se 1 (by rfl) ⟨1096013, by rfl⟩ : syracuseStep 1461351 = 2192027) B2192027
theorem B1461575 : Blo 1461050 1461575 := bstep (se 1 (by rfl) ⟨1096181, by rfl⟩ : syracuseStep 1461575 = 2192363) B2192363
theorem B40562045 : Blo 1461050 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B42733433 : Blo 1461050 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B1462207 : Blo 1461050 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B16650359 : Blo 1461050 16650359 := bstep (se 1 (by rfl) ⟨12487769, by rfl⟩ : syracuseStep 16650359 = 24975539) B24975539
theorem B5550227 : Blo 1461050 5550227 := bstep (se 1 (by rfl) ⟨4162670, by rfl⟩ : syracuseStep 5550227 = 8325341) B8325341
theorem B1462463 : Blo 1461050 1462463 := bstep (se 1 (by rfl) ⟨1096847, by rfl⟩ : syracuseStep 1462463 = 2193695) B2193695
theorem B1462511 : Blo 1461050 1462511 := bstep (se 1 (by rfl) ⟨1096883, by rfl⟩ : syracuseStep 1462511 = 2193767) B2193767
theorem B85438745 : Blo 1461050 85438745 := bstep (se 2 (by rfl) ⟨32039529, by rfl⟩ : syracuseStep 85438745 = 64079059) B64079059
theorem B2192039 : Blo 1461050 2192039 := bstep (se 1 (by rfl) ⟨1644029, by rfl⟩ : syracuseStep 2192039 = 3288059) B3288059
theorem B3699391 : Blo 1461050 3699391 := bstep (se 1 (by rfl) ⟨2774543, by rfl⟩ : syracuseStep 3699391 = 5549087) B5549087
theorem B2773739 : Blo 1461050 2773739 := bstep (se 1 (by rfl) ⟨2080304, by rfl⟩ : syracuseStep 2773739 = 4160609) B4160609
theorem B8008487 : Blo 1461050 8008487 := bstep (se 1 (by rfl) ⟨6006365, by rfl⟩ : syracuseStep 8008487 = 12012731) B12012731
theorem B2192297 : Blo 1461050 2192297 := bstep (se 2 (by rfl) ⟨822111, by rfl⟩ : syracuseStep 2192297 = 1644223) B1644223
theorem B2192327 : Blo 1461050 2192327 := bstep (se 1 (by rfl) ⟨1644245, by rfl⟩ : syracuseStep 2192327 = 3288491) B3288491
theorem B2192351 : Blo 1461050 2192351 := bstep (se 1 (by rfl) ⟨1644263, by rfl⟩ : syracuseStep 2192351 = 3288527) B3288527
theorem B3290111 : Blo 1461050 3290111 := bstep (se 1 (by rfl) ⟨2467583, by rfl⟩ : syracuseStep 3290111 = 4935167) B4935167
theorem B54055943 : Blo 1461050 54055943 := bstep (se 1 (by rfl) ⟨40541957, by rfl⟩ : syracuseStep 54055943 = 81083915) B81083915
theorem B2192495 : Blo 1461050 2192495 := bstep (se 1 (by rfl) ⟨1644371, by rfl⟩ : syracuseStep 2192495 = 3288743) B3288743
theorem B3290273 : Blo 1461050 3290273 := bstep (se 2 (by rfl) ⟨1233852, by rfl⟩ : syracuseStep 3290273 = 2467705) B2467705
theorem B15799607 : Blo 1461050 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B2774483 : Blo 1461050 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B2192891 : Blo 1461050 2192891 := bstep (se 1 (by rfl) ⟨1644668, by rfl⟩ : syracuseStep 2192891 = 3289337) B3289337
theorem B2192951 : Blo 1461050 2192951 := bstep (se 1 (by rfl) ⟨1644713, by rfl⟩ : syracuseStep 2192951 = 3289427) B3289427
theorem B2193275 : Blo 1461050 2193275 := bstep (se 1 (by rfl) ⟨1644956, by rfl⟩ : syracuseStep 2193275 = 3289913) B3289913
theorem B8886185 : Blo 1461050 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B7403561 : Blo 1461050 7403561 := bstep (se 2 (by rfl) ⟨2776335, by rfl⟩ : syracuseStep 7403561 = 5552671) B5552671
theorem B14047283 : Blo 1461050 14047283 := bstep (se 1 (by rfl) ⟨10535462, by rfl⟩ : syracuseStep 14047283 = 21070925) B21070925
theorem B3700799 : Blo 1461050 3700799 := bstep (se 1 (by rfl) ⟨2775599, by rfl⟩ : syracuseStep 3700799 = 5551199) B5551199
theorem B1500756169 : Blo 1461050 1500756169 := bstep (se 2 (by rfl) ⟨562783563, by rfl⟩ : syracuseStep 1500756169 = 1125567127) B1125567127
theorem B2341919 : Blo 1461050 2341919 := bstep (se 1 (by rfl) ⟨1756439, by rfl⟩ : syracuseStep 2341919 = 3512879) B3512879
theorem B2342687 : Blo 1461050 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B9363367 : Blo 1461050 9363367 := bstep (se 1 (by rfl) ⟨7022525, by rfl⟩ : syracuseStep 9363367 = 14045051) B14045051
theorem B11100239 : Blo 1461050 11100239 := bstep (se 1 (by rfl) ⟨8325179, by rfl⟩ : syracuseStep 11100239 = 16650359) B16650359
theorem B56959163 : Blo 1461050 56959163 := bstep (se 1 (by rfl) ⟨42719372, by rfl⟩ : syracuseStep 56959163 = 85438745) B85438745
theorem B12009971 : Blo 1461050 12009971 := bstep (se 1 (by rfl) ⟨9007478, by rfl⟩ : syracuseStep 12009971 = 18014957) B18014957
theorem B36037295 : Blo 1461050 36037295 := bstep (se 1 (by rfl) ⟨27027971, by rfl⟩ : syracuseStep 36037295 = 54055943) B54055943
theorem B63234917 : Blo 1461050 63234917 := bstep (se 4 (by rfl) ⟨5928273, by rfl⟩ : syracuseStep 63234917 = 11856547) B11856547
theorem B4932521 : Blo 1461050 4932521 := bstep (se 2 (by rfl) ⟨1849695, by rfl⟩ : syracuseStep 4932521 = 3699391) B3699391
theorem B7398377 : Blo 1461050 7398377 := bstep (se 2 (by rfl) ⟨2774391, by rfl⟩ : syracuseStep 7398377 = 5548783) B5548783
theorem B2081791 : Blo 1461050 2081791 := bstep (se 1 (by rfl) ⟨1561343, by rfl⟩ : syracuseStep 2081791 = 3122687) B3122687
theorem B5924123 : Blo 1461050 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B9364855 : Blo 1461050 9364855 := bstep (se 1 (by rfl) ⟨7023641, by rfl⟩ : syracuseStep 9364855 = 14047283) B14047283
theorem B2467199 : Blo 1461050 2467199 := bstep (se 1 (by rfl) ⟨1850399, by rfl⟩ : syracuseStep 2467199 = 3700799) B3700799
theorem B6244091 : Blo 1461050 6244091 := bstep (se 1 (by rfl) ⟨4683068, by rfl⟩ : syracuseStep 6244091 = 9366137) B9366137
theorem B4680659 : Blo 1461050 4680659 := bstep (se 1 (by rfl) ⟨3510494, by rfl⟩ : syracuseStep 4680659 = 7020989) B7020989
theorem B24988661 : Blo 1461050 24988661 := bstep (se 5 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 24988661 = 2342687) B2342687
theorem B1461359 : Blo 1461050 1461359 := bstep (se 1 (by rfl) ⟨1096019, by rfl⟩ : syracuseStep 1461359 = 2192039) B2192039
theorem B1461531 : Blo 1461050 1461531 := bstep (se 1 (by rfl) ⟨1096148, by rfl⟩ : syracuseStep 1461531 = 2192297) B2192297
theorem B1461551 : Blo 1461050 1461551 := bstep (se 1 (by rfl) ⟨1096163, by rfl⟩ : syracuseStep 1461551 = 2192327) B2192327
theorem B1461567 : Blo 1461050 1461567 := bstep (se 1 (by rfl) ⟨1096175, by rfl⟩ : syracuseStep 1461567 = 2192351) B2192351
theorem B1461663 : Blo 1461050 1461663 := bstep (se 1 (by rfl) ⟨1096247, by rfl⟩ : syracuseStep 1461663 = 2192495) B2192495
theorem B7024295 : Blo 1461050 7024295 := bstep (se 1 (by rfl) ⟨5268221, by rfl⟩ : syracuseStep 7024295 = 10536443) B10536443
theorem B1461927 : Blo 1461050 1461927 := bstep (se 1 (by rfl) ⟨1096445, by rfl⟩ : syracuseStep 1461927 = 2192891) B2192891
theorem B1461967 : Blo 1461050 1461967 := bstep (se 1 (by rfl) ⟨1096475, by rfl⟩ : syracuseStep 1461967 = 2192951) B2192951
theorem B1462183 : Blo 1461050 1462183 := bstep (se 1 (by rfl) ⟨1096637, by rfl⟩ : syracuseStep 1462183 = 2193275) B2193275
theorem B4935707 : Blo 1461050 4935707 := bstep (se 1 (by rfl) ⟨3701780, by rfl⟩ : syracuseStep 4935707 = 7403561) B7403561
theorem B3698743 : Blo 1461050 3698743 := bstep (se 1 (by rfl) ⟨2774057, by rfl⟩ : syracuseStep 3698743 = 5548115) B5548115
theorem B37450187 : Blo 1461050 37450187 := bstep (se 1 (by rfl) ⟨28087640, by rfl⟩ : syracuseStep 37450187 = 56175281) B56175281
theorem B15004223 : Blo 1461050 15004223 := bstep (se 1 (by rfl) ⟨11253167, by rfl⟩ : syracuseStep 15004223 = 22506335) B22506335
theorem B1561279 : Blo 1461050 1561279 := bstep (se 1 (by rfl) ⟨1170959, by rfl⟩ : syracuseStep 1561279 = 2341919) B2341919
theorem B28488955 : Blo 1461050 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B3700151 : Blo 1461050 3700151 := bstep (se 1 (by rfl) ⟨2775113, by rfl⟩ : syracuseStep 3700151 = 5550227) B5550227
theorem B2001008225 : Blo 1461050 2001008225 := bstep (se 2 (by rfl) ⟨750378084, by rfl⟩ : syracuseStep 2001008225 = 1500756169) B1500756169
theorem B1849159 : Blo 1461050 1849159 := bstep (se 1 (by rfl) ⟨1386869, by rfl⟩ : syracuseStep 1849159 = 2773739) B2773739
theorem B5338991 : Blo 1461050 5338991 := bstep (se 1 (by rfl) ⟨4004243, by rfl⟩ : syracuseStep 5338991 = 8008487) B8008487
theorem B3512263 : Blo 1461050 3512263 := bstep (se 1 (by rfl) ⟨2634197, by rfl⟩ : syracuseStep 3512263 = 5268395) B5268395
theorem B2193407 : Blo 1461050 2193407 := bstep (se 1 (by rfl) ⟨1645055, by rfl⟩ : syracuseStep 2193407 = 3290111) B3290111
theorem B2193515 : Blo 1461050 2193515 := bstep (se 1 (by rfl) ⟨1645136, by rfl⟩ : syracuseStep 2193515 = 3290273) B3290273
theorem B11098295 : Blo 1461050 11098295 := bstep (se 1 (by rfl) ⟨8323721, by rfl⟩ : syracuseStep 11098295 = 16647443) B16647443
theorem B10533071 : Blo 1461050 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B1849655 : Blo 1461050 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B2310757303 : Blo 1461050 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B180042709 : Blo 1461050 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B16653275 : Blo 1461050 16653275 := bstep (se 1 (by rfl) ⟨12489956, by rfl⟩ : syracuseStep 16653275 = 24979913) B24979913
theorem B27041363 : Blo 1461050 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B12484489 : Blo 1461050 12484489 := bstep (se 2 (by rfl) ⟨4681683, by rfl⟩ : syracuseStep 12484489 = 9363367) B9363367
theorem B4931657 : Blo 1461050 4931657 := bstep (se 2 (by rfl) ⟨1849371, by rfl⟩ : syracuseStep 4931657 = 3698743) B3698743
theorem B10002815 : Blo 1461050 10002815 := bstep (se 1 (by rfl) ⟨7502111, by rfl⟩ : syracuseStep 10002815 = 15004223) B15004223
theorem B42156611 : Blo 1461050 42156611 := bstep (se 1 (by rfl) ⟨31617458, by rfl⟩ : syracuseStep 42156611 = 63234917) B63234917
theorem B4932251 : Blo 1461050 4932251 := bstep (se 1 (by rfl) ⟨3699188, by rfl⟩ : syracuseStep 4932251 = 7398377) B7398377
theorem B4932413 : Blo 1461050 4932413 := bstep (se 3 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 4932413 = 1849655) B1849655
theorem B3949415 : Blo 1461050 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B2081705 : Blo 1461050 2081705 := bstep (se 2 (by rfl) ⟨780639, by rfl⟩ : syracuseStep 2081705 = 1561279) B1561279
theorem B2466767 : Blo 1461050 2466767 := bstep (se 1 (by rfl) ⟨1850075, by rfl⟩ : syracuseStep 2466767 = 3700151) B3700151
theorem B4162727 : Blo 1461050 4162727 := bstep (se 1 (by rfl) ⟨3122045, by rfl⟩ : syracuseStep 4162727 = 6244091) B6244091
theorem B7398863 : Blo 1461050 7398863 := bstep (se 1 (by rfl) ⟨5549147, by rfl⟩ : syracuseStep 7398863 = 11098295) B11098295
theorem B7022047 : Blo 1461050 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B12486473 : Blo 1461050 12486473 := bstep (se 2 (by rfl) ⟨4682427, by rfl⟩ : syracuseStep 12486473 = 9364855) B9364855
theorem B11102183 : Blo 1461050 11102183 := bstep (se 1 (by rfl) ⟨8326637, by rfl⟩ : syracuseStep 11102183 = 16653275) B16653275
theorem B7400159 : Blo 1461050 7400159 := bstep (se 1 (by rfl) ⟨5550119, by rfl⟩ : syracuseStep 7400159 = 11100239) B11100239
theorem B37972775 : Blo 1461050 37972775 := bstep (se 1 (by rfl) ⟨28479581, by rfl⟩ : syracuseStep 37972775 = 56959163) B56959163
theorem B3288347 : Blo 1461050 3288347 := bstep (se 1 (by rfl) ⟨2466260, by rfl⟩ : syracuseStep 3288347 = 4932521) B4932521
theorem B1334005483 : Blo 1461050 1334005483 := bstep (se 1 (by rfl) ⟨1000504112, by rfl⟩ : syracuseStep 1334005483 = 2001008225) B2001008225
theorem B32026589 : Blo 1461050 32026589 := bstep (se 3 (by rfl) ⟨6004985, by rfl⟩ : syracuseStep 32026589 = 12009971) B12009971
theorem B1462271 : Blo 1461050 1462271 := bstep (se 1 (by rfl) ⟨1096703, by rfl⟩ : syracuseStep 1462271 = 2193407) B2193407
theorem B1462343 : Blo 1461050 1462343 := bstep (se 1 (by rfl) ⟨1096757, by rfl⟩ : syracuseStep 1462343 = 2193515) B2193515
theorem B16659107 : Blo 1461050 16659107 := bstep (se 1 (by rfl) ⟨12494330, by rfl⟩ : syracuseStep 16659107 = 24988661) B24988661
theorem B18027575 : Blo 1461050 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B4682863 : Blo 1461050 4682863 := bstep (se 1 (by rfl) ⟨3512147, by rfl⟩ : syracuseStep 4682863 = 7024295) B7024295
theorem B4683017 : Blo 1461050 4683017 := bstep (se 2 (by rfl) ⟨1756131, by rfl⟩ : syracuseStep 4683017 = 3512263) B3512263
theorem B3290471 : Blo 1461050 3290471 := bstep (se 1 (by rfl) ⟨2467853, by rfl⟩ : syracuseStep 3290471 = 4935707) B4935707
theorem B24966791 : Blo 1461050 24966791 := bstep (se 1 (by rfl) ⟨18725093, by rfl⟩ : syracuseStep 24966791 = 37450187) B37450187
theorem B24024863 : Blo 1461050 24024863 := bstep (se 1 (by rfl) ⟨18018647, by rfl⟩ : syracuseStep 24024863 = 36037295) B36037295
theorem B1644799 : Blo 1461050 1644799 := bstep (se 1 (by rfl) ⟨1233599, by rfl⟩ : syracuseStep 1644799 = 2467199) B2467199
theorem B3081009737 : Blo 1461050 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B240056945 : Blo 1461050 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B2775721 : Blo 1461050 2775721 := bstep (se 2 (by rfl) ⟨1040895, by rfl⟩ : syracuseStep 2775721 = 2081791) B2081791
theorem B37985273 : Blo 1461050 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B3120439 : Blo 1461050 3120439 := bstep (se 1 (by rfl) ⟨2340329, by rfl⟩ : syracuseStep 3120439 = 4680659) B4680659
theorem B14237309 : Blo 1461050 14237309 := bstep (se 3 (by rfl) ⟨2669495, by rfl⟩ : syracuseStep 14237309 = 5338991) B5338991
theorem B2465545 : Blo 1461050 2465545 := bstep (se 2 (by rfl) ⟨924579, by rfl⟩ : syracuseStep 2465545 = 1849159) B1849159
theorem B16645985 : Blo 1461050 16645985 := bstep (se 2 (by rfl) ⟨6242244, by rfl⟩ : syracuseStep 16645985 = 12484489) B12484489
theorem B6668543 : Blo 1461050 6668543 := bstep (se 1 (by rfl) ⟨5001407, by rfl⟩ : syracuseStep 6668543 = 10002815) B10002815
theorem B12018383 : Blo 1461050 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B3122011 : Blo 1461050 3122011 := bstep (se 1 (by rfl) ⟨2341508, by rfl⟩ : syracuseStep 3122011 = 4683017) B4683017
theorem B4932575 : Blo 1461050 4932575 := bstep (se 1 (by rfl) ⟨3699431, by rfl⟩ : syracuseStep 4932575 = 7398863) B7398863
theorem B16016575 : Blo 1461050 16016575 := bstep (se 1 (by rfl) ⟨12012431, by rfl⟩ : syracuseStep 16016575 = 24024863) B24024863
theorem B8324315 : Blo 1461050 8324315 := bstep (se 1 (by rfl) ⟨6243236, by rfl⟩ : syracuseStep 8324315 = 12486473) B12486473
theorem B6243817 : Blo 1461050 6243817 := bstep (se 2 (by rfl) ⟨2341431, by rfl⟩ : syracuseStep 6243817 = 4682863) B4682863
theorem B4933439 : Blo 1461050 4933439 := bstep (se 1 (by rfl) ⟨3700079, by rfl⟩ : syracuseStep 4933439 = 7400159) B7400159
theorem B25315183 : Blo 1461050 25315183 := bstep (se 1 (by rfl) ⟨18986387, by rfl⟩ : syracuseStep 25315183 = 37972775) B37972775
theorem B25323515 : Blo 1461050 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B1778673977 : Blo 1461050 1778673977 := bstep (se 2 (by rfl) ⟨667002741, by rfl⟩ : syracuseStep 1778673977 = 1334005483) B1334005483
theorem B3287393 : Blo 1461050 3287393 := bstep (se 2 (by rfl) ⟨1232772, by rfl⟩ : syracuseStep 3287393 = 2465545) B2465545
theorem B21351059 : Blo 1461050 21351059 := bstep (se 1 (by rfl) ⟨16013294, by rfl⟩ : syracuseStep 21351059 = 32026589) B32026589
theorem B3287771 : Blo 1461050 3287771 := bstep (se 1 (by rfl) ⟨2465828, by rfl⟩ : syracuseStep 3287771 = 4931657) B4931657
theorem B3288167 : Blo 1461050 3288167 := bstep (se 1 (by rfl) ⟨2466125, by rfl⟩ : syracuseStep 3288167 = 4932251) B4932251
theorem B3288275 : Blo 1461050 3288275 := bstep (se 1 (by rfl) ⟨2466206, by rfl⟩ : syracuseStep 3288275 = 4932413) B4932413
theorem B2632943 : Blo 1461050 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B7401455 : Blo 1461050 7401455 := bstep (se 1 (by rfl) ⟨5551091, by rfl⟩ : syracuseStep 7401455 = 11102183) B11102183
theorem B2192231 : Blo 1461050 2192231 := bstep (se 1 (by rfl) ⟨1644173, by rfl⟩ : syracuseStep 2192231 = 3288347) B3288347
theorem B9491539 : Blo 1461050 9491539 := bstep (se 1 (by rfl) ⟨7118654, by rfl⟩ : syracuseStep 9491539 = 14237309) B14237309
theorem B5551213 : Blo 1461050 5551213 := bstep (se 3 (by rfl) ⟨1040852, by rfl⟩ : syracuseStep 5551213 = 2081705) B2081705
theorem B11097323 : Blo 1461050 11097323 := bstep (se 1 (by rfl) ⟨8322992, by rfl⟩ : syracuseStep 11097323 = 16645985) B16645985
theorem B2193065 : Blo 1461050 2193065 := bstep (se 2 (by rfl) ⟨822399, by rfl⟩ : syracuseStep 2193065 = 1644799) B1644799
theorem B28104407 : Blo 1461050 28104407 := bstep (se 1 (by rfl) ⟨21078305, by rfl⟩ : syracuseStep 28104407 = 42156611) B42156611
theorem B11106071 : Blo 1461050 11106071 := bstep (se 1 (by rfl) ⟨8329553, by rfl⟩ : syracuseStep 11106071 = 16659107) B16659107
theorem B1644511 : Blo 1461050 1644511 := bstep (se 1 (by rfl) ⟨1233383, by rfl⟩ : syracuseStep 1644511 = 2466767) B2466767
theorem B2775151 : Blo 1461050 2775151 := bstep (se 1 (by rfl) ⟨2081363, by rfl⟩ : syracuseStep 2775151 = 4162727) B4162727
theorem B3700961 : Blo 1461050 3700961 := bstep (se 2 (by rfl) ⟨1387860, by rfl⟩ : syracuseStep 3700961 = 2775721) B2775721
theorem B2193647 : Blo 1461050 2193647 := bstep (se 1 (by rfl) ⟨1645235, by rfl⟩ : syracuseStep 2193647 = 3290471) B3290471
theorem B16644527 : Blo 1461050 16644527 := bstep (se 1 (by rfl) ⟨12483395, by rfl⟩ : syracuseStep 16644527 = 24966791) B24966791
theorem B8216025965 : Blo 1461050 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B4160585 : Blo 1461050 4160585 := bstep (se 2 (by rfl) ⟨1560219, by rfl⟩ : syracuseStep 4160585 = 3120439) B3120439
theorem B160037963 : Blo 1461050 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B9362729 : Blo 1461050 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B8012255 : Blo 1461050 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B7021181 : Blo 1461050 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B7398215 : Blo 1461050 7398215 := bstep (se 1 (by rfl) ⟨5548661, by rfl⟩ : syracuseStep 7398215 = 11097323) B11097323
theorem B4162681 : Blo 1461050 4162681 := bstep (se 2 (by rfl) ⟨1561005, by rfl⟩ : syracuseStep 4162681 = 3122011) B3122011
theorem B18736271 : Blo 1461050 18736271 := bstep (se 1 (by rfl) ⟨14052203, by rfl⟩ : syracuseStep 18736271 = 28104407) B28104407
theorem B2467307 : Blo 1461050 2467307 := bstep (se 1 (by rfl) ⟨1850480, by rfl⟩ : syracuseStep 2467307 = 3700961) B3700961
theorem B135014309 : Blo 1461050 135014309 := bstep (se 4 (by rfl) ⟨12657591, by rfl⟩ : syracuseStep 135014309 = 25315183) B25315183
theorem B8325089 : Blo 1461050 8325089 := bstep (se 2 (by rfl) ⟨3121908, by rfl⟩ : syracuseStep 8325089 = 6243817) B6243817
theorem B4934303 : Blo 1461050 4934303 := bstep (se 1 (by rfl) ⟨3700727, by rfl⟩ : syracuseStep 4934303 = 7401455) B7401455
theorem B11094893 : Blo 1461050 11094893 := bstep (se 3 (by rfl) ⟨2080292, by rfl⟩ : syracuseStep 11094893 = 4160585) B4160585
theorem B1461487 : Blo 1461050 1461487 := bstep (se 1 (by rfl) ⟨1096115, by rfl⟩ : syracuseStep 1461487 = 2192231) B2192231
theorem B3288383 : Blo 1461050 3288383 := bstep (se 1 (by rfl) ⟨2466287, by rfl⟩ : syracuseStep 3288383 = 4932575) B4932575
theorem B5549543 : Blo 1461050 5549543 := bstep (se 1 (by rfl) ⟨4162157, by rfl⟩ : syracuseStep 5549543 = 8324315) B8324315
theorem B1462043 : Blo 1461050 1462043 := bstep (se 1 (by rfl) ⟨1096532, by rfl⟩ : syracuseStep 1462043 = 2193065) B2193065
theorem B3288959 : Blo 1461050 3288959 := bstep (se 1 (by rfl) ⟨2466719, by rfl⟩ : syracuseStep 3288959 = 4933439) B4933439
theorem B7401617 : Blo 1461050 7401617 := bstep (se 2 (by rfl) ⟨2775606, by rfl⟩ : syracuseStep 7401617 = 5551213) B5551213
theorem B1462431 : Blo 1461050 1462431 := bstep (se 1 (by rfl) ⟨1096823, by rfl⟩ : syracuseStep 1462431 = 2193647) B2193647
theorem B2191595 : Blo 1461050 2191595 := bstep (se 1 (by rfl) ⟨1643696, by rfl⟩ : syracuseStep 2191595 = 3287393) B3287393
theorem B11096351 : Blo 1461050 11096351 := bstep (se 1 (by rfl) ⟨8322263, by rfl⟩ : syracuseStep 11096351 = 16644527) B16644527
theorem B14234039 : Blo 1461050 14234039 := bstep (se 1 (by rfl) ⟨10675529, by rfl⟩ : syracuseStep 14234039 = 21351059) B21351059
theorem B2191847 : Blo 1461050 2191847 := bstep (se 1 (by rfl) ⟨1643885, by rfl⟩ : syracuseStep 2191847 = 3287771) B3287771
theorem B2192111 : Blo 1461050 2192111 := bstep (se 1 (by rfl) ⟨1644083, by rfl⟩ : syracuseStep 2192111 = 3288167) B3288167
theorem B2192183 : Blo 1461050 2192183 := bstep (se 1 (by rfl) ⟨1644137, by rfl⟩ : syracuseStep 2192183 = 3288275) B3288275
theorem B2192681 : Blo 1461050 2192681 := bstep (se 2 (by rfl) ⟨822255, by rfl⟩ : syracuseStep 2192681 = 1644511) B1644511
theorem B3700201 : Blo 1461050 3700201 := bstep (se 2 (by rfl) ⟨1387575, by rfl⟩ : syracuseStep 3700201 = 2775151) B2775151
theorem B4445695 : Blo 1461050 4445695 := bstep (se 1 (by rfl) ⟨3334271, by rfl⟩ : syracuseStep 4445695 = 6668543) B6668543
theorem B7404047 : Blo 1461050 7404047 := bstep (se 1 (by rfl) ⟨5553035, by rfl⟩ : syracuseStep 7404047 = 11106071) B11106071
theorem B16882343 : Blo 1461050 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B12655385 : Blo 1461050 12655385 := bstep (se 2 (by rfl) ⟨4745769, by rfl⟩ : syracuseStep 12655385 = 9491539) B9491539
theorem B1185782651 : Blo 1461050 1185782651 := bstep (se 1 (by rfl) ⟨889336988, by rfl⟩ : syracuseStep 1185782651 = 1778673977) B1778673977
theorem B21355433 : Blo 1461050 21355433 := bstep (se 2 (by rfl) ⟨8008287, by rfl⟩ : syracuseStep 21355433 = 16016575) B16016575
theorem B5477350643 : Blo 1461050 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B106691975 : Blo 1461050 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B6241819 : Blo 1461050 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B7397567 : Blo 1461050 7397567 := bstep (se 1 (by rfl) ⟨5548175, by rfl⟩ : syracuseStep 7397567 = 11096351) B11096351
theorem B4932143 : Blo 1461050 4932143 := bstep (se 1 (by rfl) ⟨3699107, by rfl⟩ : syracuseStep 4932143 = 7398215) B7398215
theorem B21366013 : Blo 1461050 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B790521767 : Blo 1461050 790521767 := bstep (se 1 (by rfl) ⟨592891325, by rfl⟩ : syracuseStep 790521767 = 1185782651) B1185782651
theorem B4933601 : Blo 1461050 4933601 := bstep (se 2 (by rfl) ⟨1850100, by rfl⟩ : syracuseStep 4933601 = 3700201) B3700201
theorem B4934411 : Blo 1461050 4934411 := bstep (se 1 (by rfl) ⟨3700808, by rfl⟩ : syracuseStep 4934411 = 7401617) B7401617
theorem B1461063 : Blo 1461050 1461063 := bstep (se 1 (by rfl) ⟨1095797, by rfl⟩ : syracuseStep 1461063 = 2191595) B2191595
theorem B9489359 : Blo 1461050 9489359 := bstep (se 1 (by rfl) ⟨7117019, by rfl⟩ : syracuseStep 9489359 = 14234039) B14234039
theorem B1461231 : Blo 1461050 1461231 := bstep (se 1 (by rfl) ⟨1095923, by rfl⟩ : syracuseStep 1461231 = 2191847) B2191847
theorem B1461407 : Blo 1461050 1461407 := bstep (se 1 (by rfl) ⟨1096055, by rfl⟩ : syracuseStep 1461407 = 2192111) B2192111
theorem B1461455 : Blo 1461050 1461455 := bstep (se 1 (by rfl) ⟨1096091, by rfl⟩ : syracuseStep 1461455 = 2192183) B2192183
theorem B1461787 : Blo 1461050 1461787 := bstep (se 1 (by rfl) ⟨1096340, by rfl⟩ : syracuseStep 1461787 = 2192681) B2192681
theorem B90009539 : Blo 1461050 90009539 := bstep (se 1 (by rfl) ⟨67507154, by rfl⟩ : syracuseStep 90009539 = 135014309) B135014309
theorem B5550059 : Blo 1461050 5550059 := bstep (se 1 (by rfl) ⟨4162544, by rfl⟩ : syracuseStep 5550059 = 8325089) B8325089
theorem B5550241 : Blo 1461050 5550241 := bstep (se 2 (by rfl) ⟨2081340, by rfl⟩ : syracuseStep 5550241 = 4162681) B4162681
theorem B18723149 : Blo 1461050 18723149 := bstep (se 3 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 18723149 = 7021181) B7021181
theorem B4936031 : Blo 1461050 4936031 := bstep (se 1 (by rfl) ⟨3702023, by rfl⟩ : syracuseStep 4936031 = 7404047) B7404047
theorem B3289535 : Blo 1461050 3289535 := bstep (se 1 (by rfl) ⟨2467151, by rfl⟩ : syracuseStep 3289535 = 4934303) B4934303
theorem B5927593 : Blo 1461050 5927593 := bstep (se 2 (by rfl) ⟨2222847, by rfl⟩ : syracuseStep 5927593 = 4445695) B4445695
theorem B2192255 : Blo 1461050 2192255 := bstep (se 1 (by rfl) ⟨1644191, by rfl⟩ : syracuseStep 2192255 = 3288383) B3288383
theorem B71127983 : Blo 1461050 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B3699695 : Blo 1461050 3699695 := bstep (se 1 (by rfl) ⟨2774771, by rfl⟩ : syracuseStep 3699695 = 5549543) B5549543
theorem B2192639 : Blo 1461050 2192639 := bstep (se 1 (by rfl) ⟨1644479, by rfl⟩ : syracuseStep 2192639 = 3288959) B3288959
theorem B12490847 : Blo 1461050 12490847 := bstep (se 1 (by rfl) ⟨9368135, by rfl⟩ : syracuseStep 12490847 = 18736271) B18736271
theorem B1644871 : Blo 1461050 1644871 := bstep (se 1 (by rfl) ⟨1233653, by rfl⟩ : syracuseStep 1644871 = 2467307) B2467307
theorem B11254895 : Blo 1461050 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B8436923 : Blo 1461050 8436923 := bstep (se 1 (by rfl) ⟨6327692, by rfl⟩ : syracuseStep 8436923 = 12655385) B12655385
theorem B7396595 : Blo 1461050 7396595 := bstep (se 1 (by rfl) ⟨5547446, by rfl⟩ : syracuseStep 7396595 = 11094893) B11094893
theorem B14236955 : Blo 1461050 14236955 := bstep (se 1 (by rfl) ⟨10677716, by rfl⟩ : syracuseStep 14236955 = 21355433) B21355433
theorem B8322425 : Blo 1461050 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B3651567095 : Blo 1461050 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B4931711 : Blo 1461050 4931711 := bstep (se 1 (by rfl) ⟨3698783, by rfl⟩ : syracuseStep 4931711 = 7397567) B7397567
theorem B2466463 : Blo 1461050 2466463 := bstep (se 1 (by rfl) ⟨1849847, by rfl⟩ : syracuseStep 2466463 = 3699695) B3699695
theorem B5548283 : Blo 1461050 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B2434378063 : Blo 1461050 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B7400321 : Blo 1461050 7400321 := bstep (se 2 (by rfl) ⟨2775120, by rfl⟩ : syracuseStep 7400321 = 5550241) B5550241
theorem B3288095 : Blo 1461050 3288095 := bstep (se 1 (by rfl) ⟨2466071, by rfl⟩ : syracuseStep 3288095 = 4932143) B4932143
theorem B1461503 : Blo 1461050 1461503 := bstep (se 1 (by rfl) ⟨1096127, by rfl⟩ : syracuseStep 1461503 = 2192255) B2192255
theorem B47418655 : Blo 1461050 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B1461759 : Blo 1461050 1461759 := bstep (se 1 (by rfl) ⟨1096319, by rfl⟩ : syracuseStep 1461759 = 2192639) B2192639
theorem B3289067 : Blo 1461050 3289067 := bstep (se 1 (by rfl) ⟨2466800, by rfl⟩ : syracuseStep 3289067 = 4933601) B4933601
theorem B8327231 : Blo 1461050 8327231 := bstep (se 1 (by rfl) ⟨6245423, by rfl⟩ : syracuseStep 8327231 = 12490847) B12490847
theorem B28488017 : Blo 1461050 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B3289607 : Blo 1461050 3289607 := bstep (se 1 (by rfl) ⟨2467205, by rfl⟩ : syracuseStep 3289607 = 4934411) B4934411
theorem B5624615 : Blo 1461050 5624615 := bstep (se 1 (by rfl) ⟨4218461, by rfl⟩ : syracuseStep 5624615 = 8436923) B8436923
theorem B9491303 : Blo 1461050 9491303 := bstep (se 1 (by rfl) ⟨7118477, by rfl⟩ : syracuseStep 9491303 = 14236955) B14236955
theorem B3700039 : Blo 1461050 3700039 := bstep (se 1 (by rfl) ⟨2775029, by rfl⟩ : syracuseStep 3700039 = 5550059) B5550059
theorem B12482099 : Blo 1461050 12482099 := bstep (se 1 (by rfl) ⟨9361574, by rfl⟩ : syracuseStep 12482099 = 18723149) B18723149
theorem B3290687 : Blo 1461050 3290687 := bstep (se 1 (by rfl) ⟨2468015, by rfl⟩ : syracuseStep 3290687 = 4936031) B4936031
theorem B2193023 : Blo 1461050 2193023 := bstep (se 1 (by rfl) ⟨1644767, by rfl⟩ : syracuseStep 2193023 = 3289535) B3289535
theorem B2193161 : Blo 1461050 2193161 := bstep (se 2 (by rfl) ⟨822435, by rfl⟩ : syracuseStep 2193161 = 1644871) B1644871
theorem B7903457 : Blo 1461050 7903457 := bstep (se 2 (by rfl) ⟨2963796, by rfl⟩ : syracuseStep 7903457 = 5927593) B5927593
theorem B527014511 : Blo 1461050 527014511 := bstep (se 1 (by rfl) ⟨395260883, by rfl⟩ : syracuseStep 527014511 = 790521767) B790521767
theorem B7503263 : Blo 1461050 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B4931063 : Blo 1461050 4931063 := bstep (se 1 (by rfl) ⟨3698297, by rfl⟩ : syracuseStep 4931063 = 7396595) B7396595
theorem B25304957 : Blo 1461050 25304957 := bstep (se 3 (by rfl) ⟨4744679, by rfl⟩ : syracuseStep 25304957 = 9489359) B9489359
theorem B60006359 : Blo 1461050 60006359 := bstep (se 1 (by rfl) ⟨45004769, by rfl⟩ : syracuseStep 60006359 = 90009539) B90009539
theorem B5268971 : Blo 1461050 5268971 := bstep (se 1 (by rfl) ⟨3951728, by rfl⟩ : syracuseStep 5268971 = 7903457) B7903457
theorem B4933385 : Blo 1461050 4933385 := bstep (se 2 (by rfl) ⟨1850019, by rfl⟩ : syracuseStep 4933385 = 3700039) B3700039
theorem B4933547 : Blo 1461050 4933547 := bstep (se 1 (by rfl) ⟨3700160, by rfl⟩ : syracuseStep 4933547 = 7400321) B7400321
theorem B3287375 : Blo 1461050 3287375 := bstep (se 1 (by rfl) ⟨2465531, by rfl⟩ : syracuseStep 3287375 = 4931063) B4931063
theorem B16869971 : Blo 1461050 16869971 := bstep (se 1 (by rfl) ⟨12652478, by rfl⟩ : syracuseStep 16869971 = 25304957) B25304957
theorem B40004239 : Blo 1461050 40004239 := bstep (se 1 (by rfl) ⟨30003179, by rfl⟩ : syracuseStep 40004239 = 60006359) B60006359
theorem B3287807 : Blo 1461050 3287807 := bstep (se 1 (by rfl) ⟨2465855, by rfl⟩ : syracuseStep 3287807 = 4931711) B4931711
theorem B18992011 : Blo 1461050 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B3245837417 : Blo 1461050 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B3288617 : Blo 1461050 3288617 := bstep (se 2 (by rfl) ⟨1233231, by rfl⟩ : syracuseStep 3288617 = 2466463) B2466463
theorem B1462015 : Blo 1461050 1462015 := bstep (se 1 (by rfl) ⟨1096511, by rfl⟩ : syracuseStep 1462015 = 2193023) B2193023
theorem B1462107 : Blo 1461050 1462107 := bstep (se 1 (by rfl) ⟨1096580, by rfl⟩ : syracuseStep 1462107 = 2193161) B2193161
theorem B3698855 : Blo 1461050 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B351343007 : Blo 1461050 351343007 := bstep (se 1 (by rfl) ⟨263507255, by rfl⟩ : syracuseStep 351343007 = 527014511) B527014511
theorem B2192063 : Blo 1461050 2192063 := bstep (se 1 (by rfl) ⟨1644047, by rfl⟩ : syracuseStep 2192063 = 3288095) B3288095
theorem B25310141 : Blo 1461050 25310141 := bstep (se 3 (by rfl) ⟨4745651, by rfl⟩ : syracuseStep 25310141 = 9491303) B9491303
theorem B5002175 : Blo 1461050 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B2192711 : Blo 1461050 2192711 := bstep (se 1 (by rfl) ⟨1644533, by rfl⟩ : syracuseStep 2192711 = 3289067) B3289067
theorem B5551487 : Blo 1461050 5551487 := bstep (se 1 (by rfl) ⟨4163615, by rfl⟩ : syracuseStep 5551487 = 8327231) B8327231
theorem B2193071 : Blo 1461050 2193071 := bstep (se 1 (by rfl) ⟨1644803, by rfl⟩ : syracuseStep 2193071 = 3289607) B3289607
theorem B3749743 : Blo 1461050 3749743 := bstep (se 1 (by rfl) ⟨2812307, by rfl⟩ : syracuseStep 3749743 = 5624615) B5624615
theorem B8321399 : Blo 1461050 8321399 := bstep (se 1 (by rfl) ⟨6241049, by rfl⟩ : syracuseStep 8321399 = 12482099) B12482099
theorem B2193791 : Blo 1461050 2193791 := bstep (se 1 (by rfl) ⟨1645343, by rfl⟩ : syracuseStep 2193791 = 3290687) B3290687
theorem B63224873 : Blo 1461050 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B2465903 : Blo 1461050 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B3334783 : Blo 1461050 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B53338985 : Blo 1461050 53338985 := bstep (se 2 (by rfl) ⟨20002119, by rfl⟩ : syracuseStep 53338985 = 40004239) B40004239
theorem B25322681 : Blo 1461050 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B5547599 : Blo 1461050 5547599 := bstep (se 1 (by rfl) ⟨4160699, by rfl⟩ : syracuseStep 5547599 = 8321399) B8321399
theorem B42149915 : Blo 1461050 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B4999657 : Blo 1461050 4999657 := bstep (se 2 (by rfl) ⟨1874871, by rfl⟩ : syracuseStep 4999657 = 3749743) B3749743
theorem B234228671 : Blo 1461050 234228671 := bstep (se 1 (by rfl) ⟨175671503, by rfl⟩ : syracuseStep 234228671 = 351343007) B351343007
theorem B1461375 : Blo 1461050 1461375 := bstep (se 1 (by rfl) ⟨1096031, by rfl⟩ : syracuseStep 1461375 = 2192063) B2192063
theorem B1461807 : Blo 1461050 1461807 := bstep (se 1 (by rfl) ⟨1096355, by rfl⟩ : syracuseStep 1461807 = 2192711) B2192711
theorem B1462047 : Blo 1461050 1462047 := bstep (se 1 (by rfl) ⟨1096535, by rfl⟩ : syracuseStep 1462047 = 2193071) B2193071
theorem B3288923 : Blo 1461050 3288923 := bstep (se 1 (by rfl) ⟨2466692, by rfl⟩ : syracuseStep 3288923 = 4933385) B4933385
theorem B3289031 : Blo 1461050 3289031 := bstep (se 1 (by rfl) ⟨2466773, by rfl⟩ : syracuseStep 3289031 = 4933547) B4933547
theorem B2191583 : Blo 1461050 2191583 := bstep (se 1 (by rfl) ⟨1643687, by rfl⟩ : syracuseStep 2191583 = 3287375) B3287375
theorem B1462527 : Blo 1461050 1462527 := bstep (se 1 (by rfl) ⟨1096895, by rfl⟩ : syracuseStep 1462527 = 2193791) B2193791
theorem B2191871 : Blo 1461050 2191871 := bstep (se 1 (by rfl) ⟨1643903, by rfl⟩ : syracuseStep 2191871 = 3287807) B3287807
theorem B2192411 : Blo 1461050 2192411 := bstep (se 1 (by rfl) ⟨1644308, by rfl⟩ : syracuseStep 2192411 = 3288617) B3288617
theorem B16873427 : Blo 1461050 16873427 := bstep (se 1 (by rfl) ⟨12655070, by rfl⟩ : syracuseStep 16873427 = 25310141) B25310141
theorem B3700991 : Blo 1461050 3700991 := bstep (se 1 (by rfl) ⟨2775743, by rfl⟩ : syracuseStep 3700991 = 5551487) B5551487
theorem B3512647 : Blo 1461050 3512647 := bstep (se 1 (by rfl) ⟨2634485, by rfl⟩ : syracuseStep 3512647 = 5268971) B5268971
theorem B11246647 : Blo 1461050 11246647 := bstep (se 1 (by rfl) ⟨8434985, by rfl⟩ : syracuseStep 11246647 = 16869971) B16869971
theorem B2163891611 : Blo 1461050 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B11248951 : Blo 1461050 11248951 := bstep (se 1 (by rfl) ⟨8436713, by rfl⟩ : syracuseStep 11248951 = 16873427) B16873427
theorem B28099943 : Blo 1461050 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B2467327 : Blo 1461050 2467327 := bstep (se 1 (by rfl) ⟨1850495, by rfl⟩ : syracuseStep 2467327 = 3700991) B3700991
theorem B1461055 : Blo 1461050 1461055 := bstep (se 1 (by rfl) ⟨1095791, by rfl⟩ : syracuseStep 1461055 = 2191583) B2191583
theorem B1461247 : Blo 1461050 1461247 := bstep (se 1 (by rfl) ⟨1095935, by rfl⟩ : syracuseStep 1461247 = 2191871) B2191871
theorem B1461607 : Blo 1461050 1461607 := bstep (se 1 (by rfl) ⟨1096205, by rfl⟩ : syracuseStep 1461607 = 2192411) B2192411
theorem B3698399 : Blo 1461050 3698399 := bstep (se 1 (by rfl) ⟨2773799, by rfl⟩ : syracuseStep 3698399 = 5547599) B5547599
theorem B14995529 : Blo 1461050 14995529 := bstep (se 2 (by rfl) ⟨5623323, by rfl⟩ : syracuseStep 14995529 = 11246647) B11246647
theorem B156152447 : Blo 1461050 156152447 := bstep (se 1 (by rfl) ⟨117114335, by rfl⟩ : syracuseStep 156152447 = 234228671) B234228671
theorem B2192615 : Blo 1461050 2192615 := bstep (se 1 (by rfl) ⟨1644461, by rfl⟩ : syracuseStep 2192615 = 3288923) B3288923
theorem B2192687 : Blo 1461050 2192687 := bstep (se 1 (by rfl) ⟨1644515, by rfl⟩ : syracuseStep 2192687 = 3289031) B3289031
theorem B1643935 : Blo 1461050 1643935 := bstep (se 1 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 1643935 = 2465903) B2465903
theorem B4683529 : Blo 1461050 4683529 := bstep (se 2 (by rfl) ⟨1756323, by rfl⟩ : syracuseStep 4683529 = 3512647) B3512647
theorem B35559323 : Blo 1461050 35559323 := bstep (se 1 (by rfl) ⟨26669492, by rfl⟩ : syracuseStep 35559323 = 53338985) B53338985
theorem B6666209 : Blo 1461050 6666209 := bstep (se 2 (by rfl) ⟨2499828, by rfl⟩ : syracuseStep 6666209 = 4999657) B4999657
theorem B16881787 : Blo 1461050 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B4446377 : Blo 1461050 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B1442594407 : Blo 1461050 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B1923459209 : Blo 1461050 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B6244705 : Blo 1461050 6244705 := bstep (se 2 (by rfl) ⟨2341764, by rfl⟩ : syracuseStep 6244705 = 4683529) B4683529
theorem B9997019 : Blo 1461050 9997019 := bstep (se 1 (by rfl) ⟨7497764, by rfl⟩ : syracuseStep 9997019 = 14995529) B14995529
theorem B1461743 : Blo 1461050 1461743 := bstep (se 1 (by rfl) ⟨1096307, by rfl⟩ : syracuseStep 1461743 = 2192615) B2192615
theorem B1461791 : Blo 1461050 1461791 := bstep (se 1 (by rfl) ⟨1096343, by rfl⟩ : syracuseStep 1461791 = 2192687) B2192687
theorem B4444139 : Blo 1461050 4444139 := bstep (se 1 (by rfl) ⟨3333104, by rfl⟩ : syracuseStep 4444139 = 6666209) B6666209
theorem B2191913 : Blo 1461050 2191913 := bstep (se 2 (by rfl) ⟨821967, by rfl⟩ : syracuseStep 2191913 = 1643935) B1643935
theorem B3289769 : Blo 1461050 3289769 := bstep (se 2 (by rfl) ⟨1233663, by rfl⟩ : syracuseStep 3289769 = 2467327) B2467327
theorem B22509049 : Blo 1461050 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B104101631 : Blo 1461050 104101631 := bstep (se 1 (by rfl) ⟨78076223, by rfl⟩ : syracuseStep 104101631 = 156152447) B156152447
theorem B18733295 : Blo 1461050 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B23706215 : Blo 1461050 23706215 := bstep (se 1 (by rfl) ⟨17779661, by rfl⟩ : syracuseStep 23706215 = 35559323) B35559323
theorem B2964251 : Blo 1461050 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B14998601 : Blo 1461050 14998601 := bstep (se 2 (by rfl) ⟨5624475, by rfl⟩ : syracuseStep 14998601 = 11248951) B11248951
theorem B2465599 : Blo 1461050 2465599 := bstep (se 1 (by rfl) ⟨1849199, by rfl⟩ : syracuseStep 2465599 = 3698399) B3698399
theorem B15804143 : Blo 1461050 15804143 := bstep (se 1 (by rfl) ⟨11853107, by rfl⟩ : syracuseStep 15804143 = 23706215) B23706215
theorem B1976167 : Blo 1461050 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B3287465 : Blo 1461050 3287465 := bstep (se 2 (by rfl) ⟨1232799, by rfl⟩ : syracuseStep 3287465 = 2465599) B2465599
theorem B1461275 : Blo 1461050 1461275 := bstep (se 1 (by rfl) ⟨1095956, by rfl⟩ : syracuseStep 1461275 = 2191913) B2191913
theorem B8326273 : Blo 1461050 8326273 := bstep (se 2 (by rfl) ⟨3122352, by rfl⟩ : syracuseStep 8326273 = 6244705) B6244705
theorem B1282306139 : Blo 1461050 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B12488863 : Blo 1461050 12488863 := bstep (se 1 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 12488863 = 18733295) B18733295
theorem B6664679 : Blo 1461050 6664679 := bstep (se 1 (by rfl) ⟨4998509, by rfl⟩ : syracuseStep 6664679 = 9997019) B9997019
theorem B30012065 : Blo 1461050 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B9999067 : Blo 1461050 9999067 := bstep (se 1 (by rfl) ⟨7499300, by rfl⟩ : syracuseStep 9999067 = 14998601) B14998601
theorem B2962759 : Blo 1461050 2962759 := bstep (se 1 (by rfl) ⟨2222069, by rfl⟩ : syracuseStep 2962759 = 4444139) B4444139
theorem B2193179 : Blo 1461050 2193179 := bstep (se 1 (by rfl) ⟨1644884, by rfl⟩ : syracuseStep 2193179 = 3289769) B3289769
theorem B69401087 : Blo 1461050 69401087 := bstep (se 1 (by rfl) ⟨52050815, by rfl⟩ : syracuseStep 69401087 = 104101631) B104101631
theorem B10536095 : Blo 1461050 10536095 := bstep (se 1 (by rfl) ⟨7902071, by rfl⟩ : syracuseStep 10536095 = 15804143) B15804143
theorem B11101697 : Blo 1461050 11101697 := bstep (se 2 (by rfl) ⟨4163136, by rfl⟩ : syracuseStep 11101697 = 8326273) B8326273
theorem B3950345 : Blo 1461050 3950345 := bstep (se 2 (by rfl) ⟨1481379, by rfl⟩ : syracuseStep 3950345 = 2962759) B2962759
theorem B854870759 : Blo 1461050 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B4443119 : Blo 1461050 4443119 := bstep (se 1 (by rfl) ⟨3332339, by rfl⟩ : syracuseStep 4443119 = 6664679) B6664679
theorem B20008043 : Blo 1461050 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B13332089 : Blo 1461050 13332089 := bstep (se 2 (by rfl) ⟨4999533, by rfl⟩ : syracuseStep 13332089 = 9999067) B9999067
theorem B1462119 : Blo 1461050 1462119 := bstep (se 1 (by rfl) ⟨1096589, by rfl⟩ : syracuseStep 1462119 = 2193179) B2193179
theorem B2191643 : Blo 1461050 2191643 := bstep (se 1 (by rfl) ⟨1643732, by rfl⟩ : syracuseStep 2191643 = 3287465) B3287465
theorem B10539557 : Blo 1461050 10539557 := bstep (se 4 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 10539557 = 1976167) B1976167
theorem B16651817 : Blo 1461050 16651817 := bstep (se 2 (by rfl) ⟨6244431, by rfl⟩ : syracuseStep 16651817 = 12488863) B12488863
theorem B46267391 : Blo 1461050 46267391 := bstep (se 1 (by rfl) ⟨34700543, by rfl⟩ : syracuseStep 46267391 = 69401087) B69401087
theorem B11101211 : Blo 1461050 11101211 := bstep (se 1 (by rfl) ⟨8325908, by rfl⟩ : syracuseStep 11101211 = 16651817) B16651817
theorem B30844927 : Blo 1461050 30844927 := bstep (se 1 (by rfl) ⟨23133695, by rfl⟩ : syracuseStep 30844927 = 46267391) B46267391
theorem B13338695 : Blo 1461050 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B1461095 : Blo 1461050 1461095 := bstep (se 1 (by rfl) ⟨1095821, by rfl⟩ : syracuseStep 1461095 = 2191643) B2191643
theorem B7401131 : Blo 1461050 7401131 := bstep (se 1 (by rfl) ⟨5550848, by rfl⟩ : syracuseStep 7401131 = 11101697) B11101697
theorem B2633563 : Blo 1461050 2633563 := bstep (se 1 (by rfl) ⟨1975172, by rfl⟩ : syracuseStep 2633563 = 3950345) B3950345
theorem B569913839 : Blo 1461050 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B2962079 : Blo 1461050 2962079 := bstep (se 1 (by rfl) ⟨2221559, by rfl⟩ : syracuseStep 2962079 = 4443119) B4443119
theorem B7026371 : Blo 1461050 7026371 := bstep (se 1 (by rfl) ⟨5269778, by rfl⟩ : syracuseStep 7026371 = 10539557) B10539557
theorem B28096253 : Blo 1461050 28096253 := bstep (se 3 (by rfl) ⟨5268047, by rfl⟩ : syracuseStep 28096253 = 10536095) B10536095
theorem B8888059 : Blo 1461050 8888059 := bstep (se 1 (by rfl) ⟨6666044, by rfl⟩ : syracuseStep 8888059 = 13332089) B13332089
theorem B1974719 : Blo 1461050 1974719 := bstep (se 1 (by rfl) ⟨1481039, by rfl⟩ : syracuseStep 1974719 = 2962079) B2962079
theorem B4934087 : Blo 1461050 4934087 := bstep (se 1 (by rfl) ⟨3700565, by rfl⟩ : syracuseStep 4934087 = 7401131) B7401131
theorem B164506277 : Blo 1461050 164506277 := bstep (se 4 (by rfl) ⟨15422463, by rfl⟩ : syracuseStep 164506277 = 30844927) B30844927
theorem B7400807 : Blo 1461050 7400807 := bstep (se 1 (by rfl) ⟨5550605, by rfl⟩ : syracuseStep 7400807 = 11101211) B11101211
theorem B18730835 : Blo 1461050 18730835 := bstep (se 1 (by rfl) ⟨14048126, by rfl⟩ : syracuseStep 18730835 = 28096253) B28096253
theorem B8892463 : Blo 1461050 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B11850745 : Blo 1461050 11850745 := bstep (se 2 (by rfl) ⟨4444029, by rfl⟩ : syracuseStep 11850745 = 8888059) B8888059
theorem B3511417 : Blo 1461050 3511417 := bstep (se 2 (by rfl) ⟨1316781, by rfl⟩ : syracuseStep 3511417 = 2633563) B2633563
theorem B379942559 : Blo 1461050 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B4684247 : Blo 1461050 4684247 := bstep (se 1 (by rfl) ⟨3513185, by rfl⟩ : syracuseStep 4684247 = 7026371) B7026371
theorem B3122831 : Blo 1461050 3122831 := bstep (se 1 (by rfl) ⟨2342123, by rfl⟩ : syracuseStep 3122831 = 4684247) B4684247
theorem B4933871 : Blo 1461050 4933871 := bstep (se 1 (by rfl) ⟨3700403, by rfl⟩ : syracuseStep 4933871 = 7400807) B7400807
theorem B12487223 : Blo 1461050 12487223 := bstep (se 1 (by rfl) ⟨9365417, by rfl⟩ : syracuseStep 12487223 = 18730835) B18730835
theorem B11856617 : Blo 1461050 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B4681889 : Blo 1461050 4681889 := bstep (se 2 (by rfl) ⟨1755708, by rfl⟩ : syracuseStep 4681889 = 3511417) B3511417
theorem B3289391 : Blo 1461050 3289391 := bstep (se 1 (by rfl) ⟨2467043, by rfl⟩ : syracuseStep 3289391 = 4934087) B4934087
theorem B109670851 : Blo 1461050 109670851 := bstep (se 1 (by rfl) ⟨82253138, by rfl⟩ : syracuseStep 109670851 = 164506277) B164506277
theorem B253295039 : Blo 1461050 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B5265917 : Blo 1461050 5265917 := bstep (se 3 (by rfl) ⟨987359, by rfl⟩ : syracuseStep 5265917 = 1974719) B1974719
theorem B15800993 : Blo 1461050 15800993 := bstep (se 2 (by rfl) ⟨5925372, by rfl⟩ : syracuseStep 15800993 = 11850745) B11850745
theorem B3121259 : Blo 1461050 3121259 := bstep (se 1 (by rfl) ⟨2340944, by rfl⟩ : syracuseStep 3121259 = 4681889) B4681889
theorem B168863359 : Blo 1461050 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B8324815 : Blo 1461050 8324815 := bstep (se 1 (by rfl) ⟨6243611, by rfl⟩ : syracuseStep 8324815 = 12487223) B12487223
theorem B584911205 : Blo 1461050 584911205 := bstep (se 4 (by rfl) ⟨54835425, by rfl⟩ : syracuseStep 584911205 = 109670851) B109670851
theorem B3289247 : Blo 1461050 3289247 := bstep (se 1 (by rfl) ⟨2466935, by rfl⟩ : syracuseStep 3289247 = 4933871) B4933871
theorem B3510611 : Blo 1461050 3510611 := bstep (se 1 (by rfl) ⟨2632958, by rfl⟩ : syracuseStep 3510611 = 5265917) B5265917
theorem B8327549 : Blo 1461050 8327549 := bstep (se 3 (by rfl) ⟨1561415, by rfl⟩ : syracuseStep 8327549 = 3122831) B3122831
theorem B2192927 : Blo 1461050 2192927 := bstep (se 1 (by rfl) ⟨1644695, by rfl⟩ : syracuseStep 2192927 = 3289391) B3289391
theorem B10533995 : Blo 1461050 10533995 := bstep (se 1 (by rfl) ⟨7900496, by rfl⟩ : syracuseStep 10533995 = 15800993) B15800993
theorem B7904411 : Blo 1461050 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B8323357 : Blo 1461050 8323357 := bstep (se 3 (by rfl) ⟨1560629, by rfl⟩ : syracuseStep 8323357 = 3121259) B3121259
theorem B389940803 : Blo 1461050 389940803 := bstep (se 1 (by rfl) ⟨292455602, by rfl⟩ : syracuseStep 389940803 = 584911205) B584911205
theorem B7022663 : Blo 1461050 7022663 := bstep (se 1 (by rfl) ⟨5266997, by rfl⟩ : syracuseStep 7022663 = 10533995) B10533995
theorem B5269607 : Blo 1461050 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B225151145 : Blo 1461050 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B1461951 : Blo 1461050 1461951 := bstep (se 1 (by rfl) ⟨1096463, by rfl⟩ : syracuseStep 1461951 = 2192927) B2192927
theorem B2192831 : Blo 1461050 2192831 := bstep (se 1 (by rfl) ⟨1644623, by rfl⟩ : syracuseStep 2192831 = 3289247) B3289247
theorem B2340407 : Blo 1461050 2340407 := bstep (se 1 (by rfl) ⟨1755305, by rfl⟩ : syracuseStep 2340407 = 3510611) B3510611
theorem B5551699 : Blo 1461050 5551699 := bstep (se 1 (by rfl) ⟨4163774, by rfl⟩ : syracuseStep 5551699 = 8327549) B8327549
theorem B11099753 : Blo 1461050 11099753 := bstep (se 2 (by rfl) ⟨4162407, by rfl⟩ : syracuseStep 11099753 = 8324815) B8324815
theorem B7399835 : Blo 1461050 7399835 := bstep (se 1 (by rfl) ⟨5549876, by rfl⟩ : syracuseStep 7399835 = 11099753) B11099753
theorem B1461887 : Blo 1461050 1461887 := bstep (se 1 (by rfl) ⟨1096415, by rfl⟩ : syracuseStep 1461887 = 2192831) B2192831
theorem B1560271 : Blo 1461050 1560271 := bstep (se 1 (by rfl) ⟨1170203, by rfl⟩ : syracuseStep 1560271 = 2340407) B2340407
theorem B259960535 : Blo 1461050 259960535 := bstep (se 1 (by rfl) ⟨194970401, by rfl⟩ : syracuseStep 259960535 = 389940803) B389940803
theorem B4681775 : Blo 1461050 4681775 := bstep (se 1 (by rfl) ⟨3511331, by rfl⟩ : syracuseStep 4681775 = 7022663) B7022663
theorem B2401612213 : Blo 1461050 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B7402265 : Blo 1461050 7402265 := bstep (se 2 (by rfl) ⟨2775849, by rfl⟩ : syracuseStep 7402265 = 5551699) B5551699
theorem B11097809 : Blo 1461050 11097809 := bstep (se 2 (by rfl) ⟨4161678, by rfl⟩ : syracuseStep 11097809 = 8323357) B8323357
theorem B3513071 : Blo 1461050 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B3121183 : Blo 1461050 3121183 := bstep (se 1 (by rfl) ⟨2340887, by rfl⟩ : syracuseStep 3121183 = 4681775) B4681775
theorem B7398539 : Blo 1461050 7398539 := bstep (se 1 (by rfl) ⟨5548904, by rfl⟩ : syracuseStep 7398539 = 11097809) B11097809
theorem B4933223 : Blo 1461050 4933223 := bstep (se 1 (by rfl) ⟨3699917, by rfl⟩ : syracuseStep 4933223 = 7399835) B7399835
theorem B4934843 : Blo 1461050 4934843 := bstep (se 1 (by rfl) ⟨3701132, by rfl⟩ : syracuseStep 4934843 = 7402265) B7402265
theorem B3202149617 : Blo 1461050 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B173307023 : Blo 1461050 173307023 := bstep (se 1 (by rfl) ⟨129980267, by rfl⟩ : syracuseStep 173307023 = 259960535) B259960535
theorem B2342047 : Blo 1461050 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B2080361 : Blo 1461050 2080361 := bstep (se 2 (by rfl) ⟨780135, by rfl⟩ : syracuseStep 2080361 = 1560271) B1560271
theorem B4161577 : Blo 1461050 4161577 := bstep (se 2 (by rfl) ⟨1560591, by rfl⟩ : syracuseStep 4161577 = 3121183) B3121183
theorem B4932359 : Blo 1461050 4932359 := bstep (se 1 (by rfl) ⟨3699269, by rfl⟩ : syracuseStep 4932359 = 7398539) B7398539
theorem B3122729 : Blo 1461050 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B5547629 : Blo 1461050 5547629 := bstep (se 3 (by rfl) ⟨1040180, by rfl⟩ : syracuseStep 5547629 = 2080361) B2080361
theorem B3288815 : Blo 1461050 3288815 := bstep (se 1 (by rfl) ⟨2466611, by rfl⟩ : syracuseStep 3288815 = 4933223) B4933223
theorem B3289895 : Blo 1461050 3289895 := bstep (se 1 (by rfl) ⟨2467421, by rfl⟩ : syracuseStep 3289895 = 4934843) B4934843
theorem B2134766411 : Blo 1461050 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B115538015 : Blo 1461050 115538015 := bstep (se 1 (by rfl) ⟨86653511, by rfl⟩ : syracuseStep 115538015 = 173307023) B173307023
theorem B2081819 : Blo 1461050 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B5548769 : Blo 1461050 5548769 := bstep (se 2 (by rfl) ⟨2080788, by rfl⟩ : syracuseStep 5548769 = 4161577) B4161577
theorem B3288239 : Blo 1461050 3288239 := bstep (se 1 (by rfl) ⟨2466179, by rfl⟩ : syracuseStep 3288239 = 4932359) B4932359
theorem B3698419 : Blo 1461050 3698419 := bstep (se 1 (by rfl) ⟨2773814, by rfl⟩ : syracuseStep 3698419 = 5547629) B5547629
theorem B77025343 : Blo 1461050 77025343 := bstep (se 1 (by rfl) ⟨57769007, by rfl⟩ : syracuseStep 77025343 = 115538015) B115538015
theorem B2192543 : Blo 1461050 2192543 := bstep (se 1 (by rfl) ⟨1644407, by rfl⟩ : syracuseStep 2192543 = 3288815) B3288815
theorem B2193263 : Blo 1461050 2193263 := bstep (se 1 (by rfl) ⟨1644947, by rfl⟩ : syracuseStep 2193263 = 3289895) B3289895
theorem B1423177607 : Blo 1461050 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B1461695 : Blo 1461050 1461695 := bstep (se 1 (by rfl) ⟨1096271, by rfl⟩ : syracuseStep 1461695 = 2192543) B2192543
theorem B1462175 : Blo 1461050 1462175 := bstep (se 1 (by rfl) ⟨1096631, by rfl⟩ : syracuseStep 1462175 = 2193263) B2193263
theorem B948785071 : Blo 1461050 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B3699179 : Blo 1461050 3699179 := bstep (se 1 (by rfl) ⟨2774384, by rfl⟩ : syracuseStep 3699179 = 5548769) B5548769
theorem B2192159 : Blo 1461050 2192159 := bstep (se 1 (by rfl) ⟨1644119, by rfl⟩ : syracuseStep 2192159 = 3288239) B3288239
theorem B5551517 : Blo 1461050 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B102700457 : Blo 1461050 102700457 := bstep (se 2 (by rfl) ⟨38512671, by rfl⟩ : syracuseStep 102700457 = 77025343) B77025343
theorem B4931225 : Blo 1461050 4931225 := bstep (se 2 (by rfl) ⟨1849209, by rfl⟩ : syracuseStep 4931225 = 3698419) B3698419
theorem B2466119 : Blo 1461050 2466119 := bstep (se 1 (by rfl) ⟨1849589, by rfl⟩ : syracuseStep 2466119 = 3699179) B3699179
theorem B3287483 : Blo 1461050 3287483 := bstep (se 1 (by rfl) ⟨2465612, by rfl⟩ : syracuseStep 3287483 = 4931225) B4931225
theorem B1461439 : Blo 1461050 1461439 := bstep (se 1 (by rfl) ⟨1096079, by rfl⟩ : syracuseStep 1461439 = 2192159) B2192159
theorem B1265046761 : Blo 1461050 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B3701011 : Blo 1461050 3701011 := bstep (se 1 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 3701011 = 5551517) B5551517
theorem B68466971 : Blo 1461050 68466971 := bstep (se 1 (by rfl) ⟨51350228, by rfl⟩ : syracuseStep 68466971 = 102700457) B102700457
theorem B4934681 : Blo 1461050 4934681 := bstep (se 2 (by rfl) ⟨1850505, by rfl⟩ : syracuseStep 4934681 = 3701011) B3701011
theorem B2191655 : Blo 1461050 2191655 := bstep (se 1 (by rfl) ⟨1643741, by rfl⟩ : syracuseStep 2191655 = 3287483) B3287483
theorem B1644079 : Blo 1461050 1644079 := bstep (se 1 (by rfl) ⟨1233059, by rfl⟩ : syracuseStep 1644079 = 2466119) B2466119
theorem B843364507 : Blo 1461050 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B45644647 : Blo 1461050 45644647 := bstep (se 1 (by rfl) ⟨34233485, by rfl⟩ : syracuseStep 45644647 = 68466971) B68466971
theorem B60859529 : Blo 1461050 60859529 := bstep (se 2 (by rfl) ⟨22822323, by rfl⟩ : syracuseStep 60859529 = 45644647) B45644647
theorem B1461103 : Blo 1461050 1461103 := bstep (se 1 (by rfl) ⟨1095827, by rfl⟩ : syracuseStep 1461103 = 2191655) B2191655
theorem B1124486009 : Blo 1461050 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B3289787 : Blo 1461050 3289787 := bstep (se 1 (by rfl) ⟨2467340, by rfl⟩ : syracuseStep 3289787 = 4934681) B4934681
theorem B2192105 : Blo 1461050 2192105 := bstep (se 2 (by rfl) ⟨822039, by rfl⟩ : syracuseStep 2192105 = 1644079) B1644079
theorem B1461403 : Blo 1461050 1461403 := bstep (se 1 (by rfl) ⟨1096052, by rfl⟩ : syracuseStep 1461403 = 2192105) B2192105
theorem B2193191 : Blo 1461050 2193191 := bstep (se 1 (by rfl) ⟨1644893, by rfl⟩ : syracuseStep 2193191 = 3289787) B3289787
theorem B40573019 : Blo 1461050 40573019 := bstep (se 1 (by rfl) ⟨30429764, by rfl⟩ : syracuseStep 40573019 = 60859529) B60859529
theorem B749657339 : Blo 1461050 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B499771559 : Blo 1461050 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B108194717 : Blo 1461050 108194717 := bstep (se 3 (by rfl) ⟨20286509, by rfl⟩ : syracuseStep 108194717 = 40573019) B40573019
theorem B1462127 : Blo 1461050 1462127 := bstep (se 1 (by rfl) ⟨1096595, by rfl⟩ : syracuseStep 1462127 = 2193191) B2193191
theorem B333181039 : Blo 1461050 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B288519245 : Blo 1461050 288519245 := bstep (se 3 (by rfl) ⟨54097358, by rfl⟩ : syracuseStep 288519245 = 108194717) B108194717
theorem B444241385 : Blo 1461050 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B192346163 : Blo 1461050 192346163 := bstep (se 1 (by rfl) ⟨144259622, by rfl⟩ : syracuseStep 192346163 = 288519245) B288519245
theorem B128230775 : Blo 1461050 128230775 := bstep (se 1 (by rfl) ⟨96173081, by rfl⟩ : syracuseStep 128230775 = 192346163) B192346163
theorem B296160923 : Blo 1461050 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B85487183 : Blo 1461050 85487183 := bstep (se 1 (by rfl) ⟨64115387, by rfl⟩ : syracuseStep 85487183 = 128230775) B128230775
theorem B197440615 : Blo 1461050 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B263254153 : Blo 1461050 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B56991455 : Blo 1461050 56991455 := bstep (se 1 (by rfl) ⟨42743591, by rfl⟩ : syracuseStep 56991455 = 85487183) B85487183
theorem B351005537 : Blo 1461050 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B37994303 : Blo 1461050 37994303 := bstep (se 1 (by rfl) ⟨28495727, by rfl⟩ : syracuseStep 37994303 = 56991455) B56991455
theorem B234003691 : Blo 1461050 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B101318141 : Blo 1461050 101318141 := bstep (se 3 (by rfl) ⟨18997151, by rfl⟩ : syracuseStep 101318141 = 37994303) B37994303
theorem B67545427 : Blo 1461050 67545427 := bstep (se 1 (by rfl) ⟨50659070, by rfl⟩ : syracuseStep 67545427 = 101318141) B101318141
theorem B312004921 : Blo 1461050 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B416006561 : Blo 1461050 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B90060569 : Blo 1461050 90060569 := bstep (se 2 (by rfl) ⟨33772713, by rfl⟩ : syracuseStep 90060569 = 67545427) B67545427
theorem B60040379 : Blo 1461050 60040379 := bstep (se 1 (by rfl) ⟨45030284, by rfl⟩ : syracuseStep 60040379 = 90060569) B90060569
theorem B1109350829 : Blo 1461050 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B40026919 : Blo 1461050 40026919 := bstep (se 1 (by rfl) ⟨30020189, by rfl⟩ : syracuseStep 40026919 = 60040379) B60040379
theorem B739567219 : Blo 1461050 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B986089625 : Blo 1461050 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B53369225 : Blo 1461050 53369225 := bstep (se 2 (by rfl) ⟨20013459, by rfl⟩ : syracuseStep 53369225 = 40026919) B40026919
theorem B657393083 : Blo 1461050 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B35579483 : Blo 1461050 35579483 := bstep (se 1 (by rfl) ⟨26684612, by rfl⟩ : syracuseStep 35579483 = 53369225) B53369225
theorem B23719655 : Blo 1461050 23719655 := bstep (se 1 (by rfl) ⟨17789741, by rfl⟩ : syracuseStep 23719655 = 35579483) B35579483
theorem B438262055 : Blo 1461050 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B15813103 : Blo 1461050 15813103 := bstep (se 1 (by rfl) ⟨11859827, by rfl⟩ : syracuseStep 15813103 = 23719655) B23719655
theorem B292174703 : Blo 1461050 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 1461050 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B21084137 : Blo 1461050 21084137 := bstep (se 2 (by rfl) ⟨7906551, by rfl⟩ : syracuseStep 21084137 = 15813103) B15813103
theorem B14056091 : Blo 1461050 14056091 := bstep (se 1 (by rfl) ⟨10542068, by rfl⟩ : syracuseStep 14056091 = 21084137) B21084137
theorem B519421693 : Blo 1461050 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 1461050 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B9370727 : Blo 1461050 9370727 := bstep (se 1 (by rfl) ⟨7028045, by rfl⟩ : syracuseStep 9370727 = 14056091) B14056091
theorem B6247151 : Blo 1461050 6247151 := bstep (se 1 (by rfl) ⟨4685363, by rfl⟩ : syracuseStep 6247151 = 9370727) B9370727
theorem B461708171 : Blo 1461050 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B4164767 : Blo 1461050 4164767 := bstep (se 1 (by rfl) ⟨3123575, by rfl⟩ : syracuseStep 4164767 = 6247151) B6247151
theorem B307805447 : Blo 1461050 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B205203631 : Blo 1461050 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B2776511 : Blo 1461050 2776511 := bstep (se 1 (by rfl) ⟨2082383, by rfl⟩ : syracuseStep 2776511 = 4164767) B4164767
theorem B273604841 : Blo 1461050 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B1851007 : Blo 1461050 1851007 := bstep (se 1 (by rfl) ⟨1388255, by rfl⟩ : syracuseStep 1851007 = 2776511) B2776511
theorem B182403227 : Blo 1461050 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B2468009 : Blo 1461050 2468009 := bstep (se 2 (by rfl) ⟨925503, by rfl⟩ : syracuseStep 2468009 = 1851007) B1851007
theorem B121602151 : Blo 1461050 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B1645339 : Blo 1461050 1645339 := bstep (se 1 (by rfl) ⟨1234004, by rfl⟩ : syracuseStep 1645339 = 2468009) B2468009
theorem B648544805 : Blo 1461050 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B2193785 : Blo 1461050 2193785 := bstep (se 2 (by rfl) ⟨822669, by rfl⟩ : syracuseStep 2193785 = 1645339) B1645339
theorem B1462523 : Blo 1461050 1462523 := bstep (se 1 (by rfl) ⟨1096892, by rfl⟩ : syracuseStep 1462523 = 2193785) B2193785
theorem B432363203 : Blo 1461050 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 1461050 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 1461050 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 1461050 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 1461050 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 1461050 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 1461050 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 1461050 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 1461050 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 1461050 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 1461050 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 1461050 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 1461050 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 1461050 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 1461050 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 1461050 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 1461050 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 1461050 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 1461050 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 1461050 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B16643069 : Blo 1461050 16643069 := bstep (se 3 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 16643069 = 6241151) B6241151
theorem B11095379 : Blo 1461050 11095379 := bstep (se 1 (by rfl) ⟨8321534, by rfl⟩ : syracuseStep 11095379 = 16643069) B16643069
theorem B7396919 : Blo 1461050 7396919 := bstep (se 1 (by rfl) ⟨5547689, by rfl⟩ : syracuseStep 7396919 = 11095379) B11095379
theorem B4931279 : Blo 1461050 4931279 := bstep (se 1 (by rfl) ⟨3698459, by rfl⟩ : syracuseStep 4931279 = 7396919) B7396919
theorem B3287519 : Blo 1461050 3287519 := bstep (se 1 (by rfl) ⟨2465639, by rfl⟩ : syracuseStep 3287519 = 4931279) B4931279
theorem B2191679 : Blo 1461050 2191679 := bstep (se 1 (by rfl) ⟨1643759, by rfl⟩ : syracuseStep 2191679 = 3287519) B3287519
theorem B1461119 : Blo 1461050 1461119 := bstep (se 1 (by rfl) ⟨1095839, by rfl⟩ : syracuseStep 1461119 = 2191679) B2191679

theorem C0 (j : ℕ) (h1 : 365262 ≤ j) (h2 : j ≤ 365636) : Blo 1461050 (4 * j + 3) := by
  interval_cases j
  · exact B1461051
  · exact B1461055
  · exact B1461059
  · exact B1461063
  · exact B1461067
  · exact B1461071
  · exact B1461075
  · exact B1461079
  · exact B1461083
  · exact B1461087
  · exact B1461091
  · exact B1461095
  · exact B1461099
  · exact B1461103
  · exact B1461107
  · exact B1461111
  · exact B1461115
  · exact B1461119
  · exact B1461123
  · exact B1461127
  · exact B1461131
  · exact B1461135
  · exact B1461139
  · exact B1461143
  · exact B1461147
  · exact B1461151
  · exact B1461155
  · exact B1461159
  · exact B1461163
  · exact B1461167
  · exact B1461171
  · exact B1461175
  · exact B1461179
  · exact B1461183
  · exact B1461187
  · exact B1461191
  · exact B1461195
  · exact B1461199
  · exact B1461203
  · exact B1461207
  · exact B1461211
  · exact B1461215
  · exact B1461219
  · exact B1461223
  · exact B1461227
  · exact B1461231
  · exact B1461235
  · exact B1461239
  · exact B1461243
  · exact B1461247
  · exact B1461251
  · exact B1461255
  · exact B1461259
  · exact B1461263
  · exact B1461267
  · exact B1461271
  · exact B1461275
  · exact B1461279
  · exact B1461283
  · exact B1461287
  · exact B1461291
  · exact B1461295
  · exact B1461299
  · exact B1461303
  · exact B1461307
  · exact B1461311
  · exact B1461315
  · exact B1461319
  · exact B1461323
  · exact B1461327
  · exact B1461331
  · exact B1461335
  · exact B1461339
  · exact B1461343
  · exact B1461347
  · exact B1461351
  · exact B1461355
  · exact B1461359
  · exact B1461363
  · exact B1461367
  · exact B1461371
  · exact B1461375
  · exact B1461379
  · exact B1461383
  · exact B1461387
  · exact B1461391
  · exact B1461395
  · exact B1461399
  · exact B1461403
  · exact B1461407
  · exact B1461411
  · exact B1461415
  · exact B1461419
  · exact B1461423
  · exact B1461427
  · exact B1461431
  · exact B1461435
  · exact B1461439
  · exact B1461443
  · exact B1461447
  · exact B1461451
  · exact B1461455
  · exact B1461459
  · exact B1461463
  · exact B1461467
  · exact B1461471
  · exact B1461475
  · exact B1461479
  · exact B1461483
  · exact B1461487
  · exact B1461491
  · exact B1461495
  · exact B1461499
  · exact B1461503
  · exact B1461507
  · exact B1461511
  · exact B1461515
  · exact B1461519
  · exact B1461523
  · exact B1461527
  · exact B1461531
  · exact B1461535
  · exact B1461539
  · exact B1461543
  · exact B1461547
  · exact B1461551
  · exact B1461555
  · exact B1461559
  · exact B1461563
  · exact B1461567
  · exact B1461571
  · exact B1461575
  · exact B1461579
  · exact B1461583
  · exact B1461587
  · exact B1461591
  · exact B1461595
  · exact B1461599
  · exact B1461603
  · exact B1461607
  · exact B1461611
  · exact B1461615
  · exact B1461619
  · exact B1461623
  · exact B1461627
  · exact B1461631
  · exact B1461635
  · exact B1461639
  · exact B1461643
  · exact B1461647
  · exact B1461651
  · exact B1461655
  · exact B1461659
  · exact B1461663
  · exact B1461667
  · exact B1461671
  · exact B1461675
  · exact B1461679
  · exact B1461683
  · exact B1461687
  · exact B1461691
  · exact B1461695
  · exact B1461699
  · exact B1461703
  · exact B1461707
  · exact B1461711
  · exact B1461715
  · exact B1461719
  · exact B1461723
  · exact B1461727
  · exact B1461731
  · exact B1461735
  · exact B1461739
  · exact B1461743
  · exact B1461747
  · exact B1461751
  · exact B1461755
  · exact B1461759
  · exact B1461763
  · exact B1461767
  · exact B1461771
  · exact B1461775
  · exact B1461779
  · exact B1461783
  · exact B1461787
  · exact B1461791
  · exact B1461795
  · exact B1461799
  · exact B1461803
  · exact B1461807
  · exact B1461811
  · exact B1461815
  · exact B1461819
  · exact B1461823
  · exact B1461827
  · exact B1461831
  · exact B1461835
  · exact B1461839
  · exact B1461843
  · exact B1461847
  · exact B1461851
  · exact B1461855
  · exact B1461859
  · exact B1461863
  · exact B1461867
  · exact B1461871
  · exact B1461875
  · exact B1461879
  · exact B1461883
  · exact B1461887
  · exact B1461891
  · exact B1461895
  · exact B1461899
  · exact B1461903
  · exact B1461907
  · exact B1461911
  · exact B1461915
  · exact B1461919
  · exact B1461923
  · exact B1461927
  · exact B1461931
  · exact B1461935
  · exact B1461939
  · exact B1461943
  · exact B1461947
  · exact B1461951
  · exact B1461955
  · exact B1461959
  · exact B1461963
  · exact B1461967
  · exact B1461971
  · exact B1461975
  · exact B1461979
  · exact B1461983
  · exact B1461987
  · exact B1461991
  · exact B1461995
  · exact B1461999
  · exact B1462003
  · exact B1462007
  · exact B1462011
  · exact B1462015
  · exact B1462019
  · exact B1462023
  · exact B1462027
  · exact B1462031
  · exact B1462035
  · exact B1462039
  · exact B1462043
  · exact B1462047
  · exact B1462051
  · exact B1462055
  · exact B1462059
  · exact B1462063
  · exact B1462067
  · exact B1462071
  · exact B1462075
  · exact B1462079
  · exact B1462083
  · exact B1462087
  · exact B1462091
  · exact B1462095
  · exact B1462099
  · exact B1462103
  · exact B1462107
  · exact B1462111
  · exact B1462115
  · exact B1462119
  · exact B1462123
  · exact B1462127
  · exact B1462131
  · exact B1462135
  · exact B1462139
  · exact B1462143
  · exact B1462147
  · exact B1462151
  · exact B1462155
  · exact B1462159
  · exact B1462163
  · exact B1462167
  · exact B1462171
  · exact B1462175
  · exact B1462179
  · exact B1462183
  · exact B1462187
  · exact B1462191
  · exact B1462195
  · exact B1462199
  · exact B1462203
  · exact B1462207
  · exact B1462211
  · exact B1462215
  · exact B1462219
  · exact B1462223
  · exact B1462227
  · exact B1462231
  · exact B1462235
  · exact B1462239
  · exact B1462243
  · exact B1462247
  · exact B1462251
  · exact B1462255
  · exact B1462259
  · exact B1462263
  · exact B1462267
  · exact B1462271
  · exact B1462275
  · exact B1462279
  · exact B1462283
  · exact B1462287
  · exact B1462291
  · exact B1462295
  · exact B1462299
  · exact B1462303
  · exact B1462307
  · exact B1462311
  · exact B1462315
  · exact B1462319
  · exact B1462323
  · exact B1462327
  · exact B1462331
  · exact B1462335
  · exact B1462339
  · exact B1462343
  · exact B1462347
  · exact B1462351
  · exact B1462355
  · exact B1462359
  · exact B1462363
  · exact B1462367
  · exact B1462371
  · exact B1462375
  · exact B1462379
  · exact B1462383
  · exact B1462387
  · exact B1462391
  · exact B1462395
  · exact B1462399
  · exact B1462403
  · exact B1462407
  · exact B1462411
  · exact B1462415
  · exact B1462419
  · exact B1462423
  · exact B1462427
  · exact B1462431
  · exact B1462435
  · exact B1462439
  · exact B1462443
  · exact B1462447
  · exact B1462451
  · exact B1462455
  · exact B1462459
  · exact B1462463
  · exact B1462467
  · exact B1462471
  · exact B1462475
  · exact B1462479
  · exact B1462483
  · exact B1462487
  · exact B1462491
  · exact B1462495
  · exact B1462499
  · exact B1462503
  · exact B1462507
  · exact B1462511
  · exact B1462515
  · exact B1462519
  · exact B1462523
  · exact B1462527
  · exact B1462531
  · exact B1462535
  · exact B1462539
  · exact B1462543
  · exact B1462547

theorem solution (m : ℕ) (hlo : 1461050 ≤ m) (hhi : m ≤ 1462550) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 365262 ≤ j := by omega
    have hj2 : j ≤ 365636 := by omega
    have hb : Blo 1461050 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
