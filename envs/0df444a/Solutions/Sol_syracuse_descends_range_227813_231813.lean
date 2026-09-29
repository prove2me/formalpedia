-- Prove2me | solution 1 for syracuse_descends_range_227813_231813
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:58.103949+00:00
-- url     : https://prove2.me/submissions/e74c4f29-522b-4f74-b5d4-c5884c6dd6fa

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


theorem B262153 : Blo 227813 262153 := bbase (se 2 (by rfl) ⟨98307, by rfl⟩ : syracuseStep 262153 = 196615) (by norm_num)
theorem B491597 : Blo 227813 491597 := bbase (se 3 (by rfl) ⟨92174, by rfl⟩ : syracuseStep 491597 = 184349) (by norm_num)
theorem B622741 : Blo 227813 622741 := bbase (se 6 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 622741 = 29191) (by norm_num)
theorem B327845 : Blo 227813 327845 := bbase (se 4 (by rfl) ⟨30735, by rfl⟩ : syracuseStep 327845 = 61471) (by norm_num)
theorem B327925 : Blo 227813 327925 := bbase (se 5 (by rfl) ⟨15371, by rfl⟩ : syracuseStep 327925 = 30743) (by norm_num)
theorem B262445 : Blo 227813 262445 := bbase (se 3 (by rfl) ⟨49208, by rfl⟩ : syracuseStep 262445 = 98417) (by norm_num)
theorem B328045 : Blo 227813 328045 := bbase (se 3 (by rfl) ⟨61508, by rfl⟩ : syracuseStep 328045 = 123017) (by norm_num)
theorem B328141 : Blo 227813 328141 := bbase (se 3 (by rfl) ⟨61526, by rfl⟩ : syracuseStep 328141 = 123053) (by norm_num)
theorem B262769 : Blo 227813 262769 := bbase (se 2 (by rfl) ⟨98538, by rfl⟩ : syracuseStep 262769 = 197077) (by norm_num)
theorem B590741 : Blo 227813 590741 := bbase (se 6 (by rfl) ⟨13845, by rfl⟩ : syracuseStep 590741 = 27691) (by norm_num)
theorem B328637 : Blo 227813 328637 := bbase (se 3 (by rfl) ⟨61619, by rfl⟩ : syracuseStep 328637 = 123239) (by norm_num)
theorem B492485 : Blo 227813 492485 := bbase (se 4 (by rfl) ⟨46170, by rfl⟩ : syracuseStep 492485 = 92341) (by norm_num)
theorem B492725 : Blo 227813 492725 := bbase (se 5 (by rfl) ⟨23096, by rfl⟩ : syracuseStep 492725 = 46193) (by norm_num)
theorem B591077 : Blo 227813 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B656693 : Blo 227813 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B525685 : Blo 227813 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B329189 : Blo 227813 329189 := bbase (se 4 (by rfl) ⟨30861, by rfl⟩ : syracuseStep 329189 = 61723) (by norm_num)
theorem B296441 : Blo 227813 296441 := bbase (se 2 (by rfl) ⟨111165, by rfl⟩ : syracuseStep 296441 = 222331) (by norm_num)
theorem B984629 : Blo 227813 984629 := bbase (se 5 (by rfl) ⟨46154, by rfl⟩ : syracuseStep 984629 = 92309) (by norm_num)
theorem B362053 : Blo 227813 362053 := bbase (se 4 (by rfl) ⟨33942, by rfl⟩ : syracuseStep 362053 = 67885) (by norm_num)
theorem B886373 : Blo 227813 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B2360981 : Blo 227813 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B296617 : Blo 227813 296617 := bbase (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) (by norm_num)
theorem B493229 : Blo 227813 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B1738421 : Blo 227813 1738421 := bbase (se 5 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 1738421 = 162977) (by norm_num)
theorem B493237 : Blo 227813 493237 := bbase (se 5 (by rfl) ⟨23120, by rfl⟩ : syracuseStep 493237 = 46241) (by norm_num)
theorem B984869 : Blo 227813 984869 := bbase (se 4 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 984869 = 184663) (by norm_num)
theorem B427933 : Blo 227813 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B264097 : Blo 227813 264097 := bbase (se 2 (by rfl) ⟨99036, by rfl⟩ : syracuseStep 264097 = 198073) (by norm_num)
theorem B329941 : Blo 227813 329941 := bbase (se 7 (by rfl) ⟨3866, by rfl⟩ : syracuseStep 329941 = 7733) (by norm_num)
theorem B526589 : Blo 227813 526589 := bbase (se 3 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 526589 = 197471) (by norm_num)
theorem B395597 : Blo 227813 395597 := bbase (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) (by norm_num)
theorem B3705173 : Blo 227813 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B559445 : Blo 227813 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B231833 : Blo 227813 231833 := bbase (se 2 (by rfl) ⟨86937, by rfl⟩ : syracuseStep 231833 = 173875) (by norm_num)
theorem B1477045 : Blo 227813 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B1051093 : Blo 227813 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B657877 : Blo 227813 657877 := bbase (se 7 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 657877 = 15419) (by norm_num)
theorem B625205 : Blo 227813 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B526933 : Blo 227813 526933 := bbase (se 8 (by rfl) ⟨3087, by rfl⟩ : syracuseStep 526933 = 6175) (by norm_num)
theorem B658037 : Blo 227813 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B232093 : Blo 227813 232093 := bbase (se 3 (by rfl) ⟨43517, by rfl⟩ : syracuseStep 232093 = 87035) (by norm_num)
theorem B494365 : Blo 227813 494365 := bbase (se 3 (by rfl) ⟨92693, by rfl⟩ : syracuseStep 494365 = 185387) (by norm_num)
theorem B658277 : Blo 227813 658277 := bbase (se 4 (by rfl) ⟨61713, by rfl⟩ : syracuseStep 658277 = 123427) (by norm_num)
theorem B297865 : Blo 227813 297865 := bbase (se 2 (by rfl) ⟨111699, by rfl⟩ : syracuseStep 297865 = 223399) (by norm_num)
theorem B232409 : Blo 227813 232409 := bbase (se 2 (by rfl) ⟨87153, by rfl⟩ : syracuseStep 232409 = 174307) (by norm_num)
theorem B658469 : Blo 227813 658469 := bbase (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) (by norm_num)
theorem B494741 : Blo 227813 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B593173 : Blo 227813 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B232993 : Blo 227813 232993 := bbase (se 2 (by rfl) ⟨87372, by rfl⟩ : syracuseStep 232993 = 174745) (by norm_num)
theorem B822917 : Blo 227813 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B1118069 : Blo 227813 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B397181 : Blo 227813 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B659461 : Blo 227813 659461 := bbase (se 4 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 659461 = 123649) (by norm_num)
theorem B987157 : Blo 227813 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B463277 : Blo 227813 463277 := bbase (se 3 (by rfl) ⟨86864, by rfl⟩ : syracuseStep 463277 = 173729) (by norm_num)
theorem B1249717 : Blo 227813 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B233933 : Blo 227813 233933 := bbase (se 3 (by rfl) ⟨43862, by rfl⟩ : syracuseStep 233933 = 87725) (by norm_num)
theorem B463325 : Blo 227813 463325 := bbase (se 3 (by rfl) ⟨86873, by rfl⟩ : syracuseStep 463325 = 173747) (by norm_num)
theorem B823861 : Blo 227813 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B234085 : Blo 227813 234085 := bbase (se 4 (by rfl) ⟨21945, by rfl⟩ : syracuseStep 234085 = 43891) (by norm_num)
theorem B824021 : Blo 227813 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B463973 : Blo 227813 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B365725 : Blo 227813 365725 := bbase (se 3 (by rfl) ⟨68573, by rfl⟩ : syracuseStep 365725 = 137147) (by norm_num)
theorem B333173 : Blo 227813 333173 := bbase (se 5 (by rfl) ⟨15617, by rfl⟩ : syracuseStep 333173 = 31235) (by norm_num)
theorem B988645 : Blo 227813 988645 := bbase (se 4 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 988645 = 185371) (by norm_num)
theorem B988661 : Blo 227813 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B1316533 : Blo 227813 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B890677 : Blo 227813 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B366437 : Blo 227813 366437 := bbase (se 4 (by rfl) ⟨34353, by rfl⟩ : syracuseStep 366437 = 68707) (by norm_num)
theorem B1185749 : Blo 227813 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B465077 : Blo 227813 465077 := bbase (se 5 (by rfl) ⟨21800, by rfl⟩ : syracuseStep 465077 = 43601) (by norm_num)
theorem B432533 : Blo 227813 432533 := bbase (se 6 (by rfl) ⟨10137, by rfl⟩ : syracuseStep 432533 = 20275) (by norm_num)
theorem B367109 : Blo 227813 367109 := bbase (se 4 (by rfl) ⟨34416, by rfl⟩ : syracuseStep 367109 = 68833) (by norm_num)
theorem B432677 : Blo 227813 432677 := bbase (se 4 (by rfl) ⟨40563, by rfl⟩ : syracuseStep 432677 = 81127) (by norm_num)
theorem B432965 : Blo 227813 432965 := bbase (se 4 (by rfl) ⟨40590, by rfl⟩ : syracuseStep 432965 = 81181) (by norm_num)
theorem B1153925 : Blo 227813 1153925 := bbase (se 4 (by rfl) ⟨108180, by rfl⟩ : syracuseStep 1153925 = 216361) (by norm_num)
theorem B1579925 : Blo 227813 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B433117 : Blo 227813 433117 := bbase (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) (by norm_num)
theorem B367621 : Blo 227813 367621 := bbase (se 4 (by rfl) ⟨34464, by rfl⟩ : syracuseStep 367621 = 68929) (by norm_num)
theorem B1317941 : Blo 227813 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B924821 : Blo 227813 924821 := bbase (se 6 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 924821 = 43351) (by norm_num)
theorem B433421 : Blo 227813 433421 := bbase (se 3 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 433421 = 162533) (by norm_num)
theorem B695573 : Blo 227813 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B924965 : Blo 227813 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B38083925 : Blo 227813 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B826789 : Blo 227813 826789 := bbase (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) (by norm_num)
theorem B368077 : Blo 227813 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B826949 : Blo 227813 826949 := bbase (se 4 (by rfl) ⟨77526, by rfl⟩ : syracuseStep 826949 = 155053) (by norm_num)
theorem B1777301 : Blo 227813 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B2989781 : Blo 227813 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B434173 : Blo 227813 434173 := bbase (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) (by norm_num)
theorem B7610453 : Blo 227813 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B368749 : Blo 227813 368749 := bbase (se 3 (by rfl) ⟨69140, by rfl⟩ : syracuseStep 368749 = 138281) (by norm_num)
theorem B270445 : Blo 227813 270445 := bbase (se 3 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 270445 = 101417) (by norm_num)
theorem B237685 : Blo 227813 237685 := bbase (se 5 (by rfl) ⟨11141, by rfl⟩ : syracuseStep 237685 = 22283) (by norm_num)
theorem B434317 : Blo 227813 434317 := bbase (se 3 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 434317 = 162869) (by norm_num)
theorem B1155221 : Blo 227813 1155221 := bbase (se 6 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 1155221 = 54151) (by norm_num)
theorem B1319125 : Blo 227813 1319125 := bbase (se 7 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 1319125 = 30917) (by norm_num)
theorem B1515797 : Blo 227813 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B434477 : Blo 227813 434477 := bbase (se 3 (by rfl) ⟨81464, by rfl⟩ : syracuseStep 434477 = 162929) (by norm_num)
theorem B1188229 : Blo 227813 1188229 := bbase (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) (by norm_num)
theorem B434621 : Blo 227813 434621 := bbase (se 3 (by rfl) ⟨81491, by rfl⟩ : syracuseStep 434621 = 162983) (by norm_num)
theorem B369173 : Blo 227813 369173 := bbase (se 6 (by rfl) ⟨8652, by rfl⟩ : syracuseStep 369173 = 17305) (by norm_num)
theorem B434909 : Blo 227813 434909 := bbase (se 3 (by rfl) ⟨81545, by rfl⟩ : syracuseStep 434909 = 163091) (by norm_num)
theorem B795413 : Blo 227813 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B369461 : Blo 227813 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B435061 : Blo 227813 435061 := bbase (se 5 (by rfl) ⟨20393, by rfl⟩ : syracuseStep 435061 = 40787) (by norm_num)
theorem B5022805 : Blo 227813 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B435365 : Blo 227813 435365 := bbase (se 4 (by rfl) ⟨40815, by rfl⟩ : syracuseStep 435365 = 81631) (by norm_num)
theorem B1746197 : Blo 227813 1746197 := bbase (se 6 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 1746197 = 81853) (by norm_num)
theorem B1156517 : Blo 227813 1156517 := bbase (se 4 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 1156517 = 216847) (by norm_num)
theorem B4793813 : Blo 227813 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B370261 : Blo 227813 370261 := bbase (se 8 (by rfl) ⟨2169, by rfl⟩ : syracuseStep 370261 = 4339) (by norm_num)
theorem B1484405 : Blo 227813 1484405 := bbase (se 5 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 1484405 = 139163) (by norm_num)
theorem B829109 : Blo 227813 829109 := bbase (se 5 (by rfl) ⟨38864, by rfl⟩ : syracuseStep 829109 = 77729) (by norm_num)
theorem B436117 : Blo 227813 436117 := bbase (se 6 (by rfl) ⟨10221, by rfl⟩ : syracuseStep 436117 = 20443) (by norm_num)
theorem B829397 : Blo 227813 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B436261 : Blo 227813 436261 := bbase (se 4 (by rfl) ⟨40899, by rfl⟩ : syracuseStep 436261 = 81799) (by norm_num)
theorem B370813 : Blo 227813 370813 := bbase (se 3 (by rfl) ⟨69527, by rfl⟩ : syracuseStep 370813 = 139055) (by norm_num)
theorem B469157 : Blo 227813 469157 := bbase (se 4 (by rfl) ⟨43983, by rfl⟩ : syracuseStep 469157 = 87967) (by norm_num)
theorem B1976501 : Blo 227813 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B436421 : Blo 227813 436421 := bbase (se 4 (by rfl) ⟨40914, by rfl⟩ : syracuseStep 436421 = 81829) (by norm_num)
theorem B436565 : Blo 227813 436565 := bbase (se 10 (by rfl) ⟨639, by rfl⟩ : syracuseStep 436565 = 1279) (by norm_num)
theorem B371069 : Blo 227813 371069 := bbase (se 3 (by rfl) ⟨69575, by rfl⟩ : syracuseStep 371069 = 139151) (by norm_num)
theorem B436853 : Blo 227813 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B1157813 : Blo 227813 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B437005 : Blo 227813 437005 := bbase (se 3 (by rfl) ⟨81938, by rfl⟩ : syracuseStep 437005 = 163877) (by norm_num)
theorem B469813 : Blo 227813 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B994117 : Blo 227813 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B732053 : Blo 227813 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B437309 : Blo 227813 437309 := bbase (se 3 (by rfl) ⟨81995, by rfl⟩ : syracuseStep 437309 = 163991) (by norm_num)
theorem B699781 : Blo 227813 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B438061 : Blo 227813 438061 := bbase (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) (by norm_num)
theorem B2207573 : Blo 227813 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B274313 : Blo 227813 274313 := bbase (se 2 (by rfl) ⟨102867, by rfl⟩ : syracuseStep 274313 = 205735) (by norm_num)
theorem B438205 : Blo 227813 438205 := bbase (se 3 (by rfl) ⟨82163, by rfl⟩ : syracuseStep 438205 = 164327) (by norm_num)
theorem B1159109 : Blo 227813 1159109 := bbase (se 4 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 1159109 = 217333) (by norm_num)
theorem B733141 : Blo 227813 733141 := bbase (se 7 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 733141 = 17183) (by norm_num)
theorem B438365 : Blo 227813 438365 := bbase (se 3 (by rfl) ⟨82193, by rfl⟩ : syracuseStep 438365 = 164387) (by norm_num)
theorem B438509 : Blo 227813 438509 := bbase (se 3 (by rfl) ⟨82220, by rfl⟩ : syracuseStep 438509 = 164441) (by norm_num)
theorem B1323317 : Blo 227813 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B274909 : Blo 227813 274909 := bbase (se 3 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 274909 = 103091) (by norm_num)
theorem B438797 : Blo 227813 438797 := bbase (se 3 (by rfl) ⟨82274, by rfl⟩ : syracuseStep 438797 = 164549) (by norm_num)
theorem B700949 : Blo 227813 700949 := bbase (se 6 (by rfl) ⟨16428, by rfl⟩ : syracuseStep 700949 = 32857) (by norm_num)
theorem B1487413 : Blo 227813 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B275005 : Blo 227813 275005 := bbase (se 3 (by rfl) ⟨51563, by rfl⟩ : syracuseStep 275005 = 103127) (by norm_num)
theorem B438949 : Blo 227813 438949 := bbase (se 4 (by rfl) ⟨41151, by rfl⟩ : syracuseStep 438949 = 82303) (by norm_num)
theorem B438989 : Blo 227813 438989 := bbase (se 3 (by rfl) ⟨82310, by rfl⟩ : syracuseStep 438989 = 164621) (by norm_num)
theorem B373469 : Blo 227813 373469 := bbase (se 3 (by rfl) ⟨70025, by rfl⟩ : syracuseStep 373469 = 140051) (by norm_num)
theorem B439253 : Blo 227813 439253 := bbase (se 7 (by rfl) ⟨5147, by rfl⟩ : syracuseStep 439253 = 10295) (by norm_num)
theorem B1979477 : Blo 227813 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B734309 : Blo 227813 734309 := bbase (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) (by norm_num)
theorem B1160405 : Blo 227813 1160405 := bbase (se 7 (by rfl) ⟨13598, by rfl⟩ : syracuseStep 1160405 = 27197) (by norm_num)
theorem B276149 : Blo 227813 276149 := bbase (se 5 (by rfl) ⟨12944, by rfl⟩ : syracuseStep 276149 = 25889) (by norm_num)
theorem B440005 : Blo 227813 440005 := bbase (se 4 (by rfl) ⟨41250, by rfl⟩ : syracuseStep 440005 = 82501) (by norm_num)
theorem B341741 : Blo 227813 341741 := bbase (se 3 (by rfl) ⟨64076, by rfl⟩ : syracuseStep 341741 = 128153) (by norm_num)
theorem B341765 : Blo 227813 341765 := bbase (se 4 (by rfl) ⟨32040, by rfl⟩ : syracuseStep 341765 = 64081) (by norm_num)
theorem B341789 : Blo 227813 341789 := bbase (se 3 (by rfl) ⟨64085, by rfl⟩ : syracuseStep 341789 = 128171) (by norm_num)
theorem B341813 : Blo 227813 341813 := bbase (se 5 (by rfl) ⟨16022, by rfl⟩ : syracuseStep 341813 = 32045) (by norm_num)
theorem B341837 : Blo 227813 341837 := bbase (se 3 (by rfl) ⟨64094, by rfl⟩ : syracuseStep 341837 = 128189) (by norm_num)
theorem B341861 : Blo 227813 341861 := bbase (se 4 (by rfl) ⟨32049, by rfl⟩ : syracuseStep 341861 = 64099) (by norm_num)
theorem B341885 : Blo 227813 341885 := bbase (se 3 (by rfl) ⟨64103, by rfl⟩ : syracuseStep 341885 = 128207) (by norm_num)
theorem B341909 : Blo 227813 341909 := bbase (se 6 (by rfl) ⟨8013, by rfl⟩ : syracuseStep 341909 = 16027) (by norm_num)
theorem B2537365 : Blo 227813 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B341933 : Blo 227813 341933 := bbase (se 3 (by rfl) ⟨64112, by rfl⟩ : syracuseStep 341933 = 128225) (by norm_num)
theorem B341957 : Blo 227813 341957 := bbase (se 4 (by rfl) ⟨32058, by rfl⟩ : syracuseStep 341957 = 64117) (by norm_num)
theorem B341981 : Blo 227813 341981 := bbase (se 3 (by rfl) ⟨64121, by rfl⟩ : syracuseStep 341981 = 128243) (by norm_num)
theorem B243697 : Blo 227813 243697 := bbase (se 2 (by rfl) ⟨91386, by rfl⟩ : syracuseStep 243697 = 182773) (by norm_num)
theorem B342005 : Blo 227813 342005 := bbase (se 5 (by rfl) ⟨16031, by rfl⟩ : syracuseStep 342005 = 32063) (by norm_num)
theorem B276481 : Blo 227813 276481 := bbase (se 2 (by rfl) ⟨103680, by rfl⟩ : syracuseStep 276481 = 207361) (by norm_num)
theorem B342029 : Blo 227813 342029 := bbase (se 3 (by rfl) ⟨64130, by rfl⟩ : syracuseStep 342029 = 128261) (by norm_num)
theorem B342053 : Blo 227813 342053 := bbase (se 4 (by rfl) ⟨32067, by rfl⟩ : syracuseStep 342053 = 64135) (by norm_num)
theorem B243757 : Blo 227813 243757 := bbase (se 3 (by rfl) ⟨45704, by rfl⟩ : syracuseStep 243757 = 91409) (by norm_num)
theorem B342077 : Blo 227813 342077 := bbase (se 3 (by rfl) ⟨64139, by rfl⟩ : syracuseStep 342077 = 128279) (by norm_num)
theorem B342101 : Blo 227813 342101 := bbase (se 8 (by rfl) ⟨2004, by rfl⟩ : syracuseStep 342101 = 4009) (by norm_num)
theorem B342125 : Blo 227813 342125 := bbase (se 3 (by rfl) ⟨64148, by rfl⟩ : syracuseStep 342125 = 128297) (by norm_num)
theorem B342149 : Blo 227813 342149 := bbase (se 4 (by rfl) ⟨32076, by rfl⟩ : syracuseStep 342149 = 64153) (by norm_num)
theorem B1947797 : Blo 227813 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B342173 : Blo 227813 342173 := bbase (se 3 (by rfl) ⟨64157, by rfl⟩ : syracuseStep 342173 = 128315) (by norm_num)
theorem B342197 : Blo 227813 342197 := bbase (se 5 (by rfl) ⟨16040, by rfl⟩ : syracuseStep 342197 = 32081) (by norm_num)
theorem B342221 : Blo 227813 342221 := bbase (se 3 (by rfl) ⟨64166, by rfl⟩ : syracuseStep 342221 = 128333) (by norm_num)
theorem B342245 : Blo 227813 342245 := bbase (se 4 (by rfl) ⟨32085, by rfl⟩ : syracuseStep 342245 = 64171) (by norm_num)
theorem B342269 : Blo 227813 342269 := bbase (se 3 (by rfl) ⟨64175, by rfl⟩ : syracuseStep 342269 = 128351) (by norm_num)
theorem B342293 : Blo 227813 342293 := bbase (se 6 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 342293 = 16045) (by norm_num)
theorem B342317 : Blo 227813 342317 := bbase (se 3 (by rfl) ⟨64184, by rfl⟩ : syracuseStep 342317 = 128369) (by norm_num)
theorem B342341 : Blo 227813 342341 := bbase (se 4 (by rfl) ⟨32094, by rfl⟩ : syracuseStep 342341 = 64189) (by norm_num)
theorem B1096021 : Blo 227813 1096021 := bbase (se 10 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 1096021 = 3211) (by norm_num)
theorem B866645 : Blo 227813 866645 := bbase (se 10 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 866645 = 2539) (by norm_num)
theorem B342365 : Blo 227813 342365 := bbase (se 3 (by rfl) ⟨64193, by rfl⟩ : syracuseStep 342365 = 128387) (by norm_num)
theorem B244073 : Blo 227813 244073 := bbase (se 2 (by rfl) ⟨91527, by rfl⟩ : syracuseStep 244073 = 183055) (by norm_num)
theorem B342389 : Blo 227813 342389 := bbase (se 5 (by rfl) ⟨16049, by rfl⟩ : syracuseStep 342389 = 32099) (by norm_num)
theorem B342413 : Blo 227813 342413 := bbase (se 3 (by rfl) ⟨64202, by rfl⟩ : syracuseStep 342413 = 128405) (by norm_num)
theorem B342437 : Blo 227813 342437 := bbase (se 4 (by rfl) ⟨32103, by rfl⟩ : syracuseStep 342437 = 64207) (by norm_num)
theorem B342461 : Blo 227813 342461 := bbase (se 3 (by rfl) ⟨64211, by rfl⟩ : syracuseStep 342461 = 128423) (by norm_num)
theorem B342485 : Blo 227813 342485 := bbase (se 7 (by rfl) ⟨4013, by rfl⟩ : syracuseStep 342485 = 8027) (by norm_num)
theorem B1161701 : Blo 227813 1161701 := bbase (se 4 (by rfl) ⟨108909, by rfl⟩ : syracuseStep 1161701 = 217819) (by norm_num)
theorem B342509 : Blo 227813 342509 := bbase (se 3 (by rfl) ⟨64220, by rfl⟩ : syracuseStep 342509 = 128441) (by norm_num)
theorem B342533 : Blo 227813 342533 := bbase (se 4 (by rfl) ⟨32112, by rfl⟩ : syracuseStep 342533 = 64225) (by norm_num)
theorem B342557 : Blo 227813 342557 := bbase (se 3 (by rfl) ⟨64229, by rfl⟩ : syracuseStep 342557 = 128459) (by norm_num)
theorem B342581 : Blo 227813 342581 := bbase (se 5 (by rfl) ⟨16058, by rfl⟩ : syracuseStep 342581 = 32117) (by norm_num)
theorem B342605 : Blo 227813 342605 := bbase (se 3 (by rfl) ⟨64238, by rfl⟩ : syracuseStep 342605 = 128477) (by norm_num)
theorem B342629 : Blo 227813 342629 := bbase (se 4 (by rfl) ⟨32121, by rfl⟩ : syracuseStep 342629 = 64243) (by norm_num)
theorem B866933 : Blo 227813 866933 := bbase (se 5 (by rfl) ⟨40637, by rfl⟩ : syracuseStep 866933 = 81275) (by norm_num)
theorem B342653 : Blo 227813 342653 := bbase (se 3 (by rfl) ⟨64247, by rfl⟩ : syracuseStep 342653 = 128495) (by norm_num)
theorem B342677 : Blo 227813 342677 := bbase (se 6 (by rfl) ⟨8031, by rfl⟩ : syracuseStep 342677 = 16063) (by norm_num)
theorem B342701 : Blo 227813 342701 := bbase (se 3 (by rfl) ⟨64256, by rfl⟩ : syracuseStep 342701 = 128513) (by norm_num)
theorem B277177 : Blo 227813 277177 := bbase (se 2 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 277177 = 207883) (by norm_num)
theorem B342725 : Blo 227813 342725 := bbase (se 4 (by rfl) ⟨32130, by rfl⟩ : syracuseStep 342725 = 64261) (by norm_num)
theorem B342749 : Blo 227813 342749 := bbase (se 3 (by rfl) ⟨64265, by rfl⟩ : syracuseStep 342749 = 128531) (by norm_num)
theorem B277225 : Blo 227813 277225 := bbase (se 2 (by rfl) ⟨103959, by rfl⟩ : syracuseStep 277225 = 207919) (by norm_num)
theorem B342773 : Blo 227813 342773 := bbase (se 5 (by rfl) ⟨16067, by rfl⟩ : syracuseStep 342773 = 32135) (by norm_num)
theorem B342797 : Blo 227813 342797 := bbase (se 3 (by rfl) ⟨64274, by rfl⟩ : syracuseStep 342797 = 128549) (by norm_num)
theorem B342821 : Blo 227813 342821 := bbase (se 4 (by rfl) ⟨32139, by rfl⟩ : syracuseStep 342821 = 64279) (by norm_num)
theorem B244517 : Blo 227813 244517 := bbase (se 4 (by rfl) ⟨22923, by rfl⟩ : syracuseStep 244517 = 45847) (by norm_num)
theorem B342845 : Blo 227813 342845 := bbase (se 3 (by rfl) ⟨64283, by rfl⟩ : syracuseStep 342845 = 128567) (by norm_num)
theorem B342869 : Blo 227813 342869 := bbase (se 9 (by rfl) ⟨1004, by rfl⟩ : syracuseStep 342869 = 2009) (by norm_num)
theorem B244577 : Blo 227813 244577 := bbase (se 2 (by rfl) ⟨91716, by rfl⟩ : syracuseStep 244577 = 183433) (by norm_num)
theorem B342893 : Blo 227813 342893 := bbase (se 3 (by rfl) ⟨64292, by rfl⟩ : syracuseStep 342893 = 128585) (by norm_num)
theorem B342917 : Blo 227813 342917 := bbase (se 4 (by rfl) ⟨32148, by rfl⟩ : syracuseStep 342917 = 64297) (by norm_num)
theorem B342941 : Blo 227813 342941 := bbase (se 3 (by rfl) ⟨64301, by rfl⟩ : syracuseStep 342941 = 128603) (by norm_num)
theorem B736165 : Blo 227813 736165 := bbase (se 4 (by rfl) ⟨69015, by rfl⟩ : syracuseStep 736165 = 138031) (by norm_num)
theorem B342965 : Blo 227813 342965 := bbase (se 5 (by rfl) ⟨16076, by rfl⟩ : syracuseStep 342965 = 32153) (by norm_num)
theorem B277453 : Blo 227813 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B342989 : Blo 227813 342989 := bbase (se 3 (by rfl) ⟨64310, by rfl⟩ : syracuseStep 342989 = 128621) (by norm_num)
theorem B244705 : Blo 227813 244705 := bbase (se 2 (by rfl) ⟨91764, by rfl⟩ : syracuseStep 244705 = 183529) (by norm_num)
theorem B343013 : Blo 227813 343013 := bbase (se 4 (by rfl) ⟨32157, by rfl⟩ : syracuseStep 343013 = 64315) (by norm_num)
theorem B769013 : Blo 227813 769013 := bbase (se 5 (by rfl) ⟨36047, by rfl⟩ : syracuseStep 769013 = 72095) (by norm_num)
theorem B343037 : Blo 227813 343037 := bbase (se 3 (by rfl) ⟨64319, by rfl⟩ : syracuseStep 343037 = 128639) (by norm_num)
theorem B343061 : Blo 227813 343061 := bbase (se 6 (by rfl) ⟨8040, by rfl⟩ : syracuseStep 343061 = 16081) (by norm_num)
theorem B343085 : Blo 227813 343085 := bbase (se 3 (by rfl) ⟨64328, by rfl⟩ : syracuseStep 343085 = 128657) (by norm_num)
theorem B343109 : Blo 227813 343109 := bbase (se 4 (by rfl) ⟨32166, by rfl⟩ : syracuseStep 343109 = 64333) (by norm_num)
theorem B310349 : Blo 227813 310349 := bbase (se 3 (by rfl) ⟨58190, by rfl⟩ : syracuseStep 310349 = 116381) (by norm_num)
theorem B343133 : Blo 227813 343133 := bbase (se 3 (by rfl) ⟨64337, by rfl⟩ : syracuseStep 343133 = 128675) (by norm_num)
theorem B343157 : Blo 227813 343157 := bbase (se 5 (by rfl) ⟨16085, by rfl⟩ : syracuseStep 343157 = 32171) (by norm_num)
theorem B375925 : Blo 227813 375925 := bbase (se 5 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 375925 = 35243) (by norm_num)
theorem B343181 : Blo 227813 343181 := bbase (se 3 (by rfl) ⟨64346, by rfl⟩ : syracuseStep 343181 = 128693) (by norm_num)
theorem B343205 : Blo 227813 343205 := bbase (se 4 (by rfl) ⟨32175, by rfl⟩ : syracuseStep 343205 = 64351) (by norm_num)
theorem B343229 : Blo 227813 343229 := bbase (se 3 (by rfl) ⟨64355, by rfl⟩ : syracuseStep 343229 = 128711) (by norm_num)
theorem B343253 : Blo 227813 343253 := bbase (se 7 (by rfl) ⟨4022, by rfl⟩ : syracuseStep 343253 = 8045) (by norm_num)
theorem B343277 : Blo 227813 343277 := bbase (se 3 (by rfl) ⟨64364, by rfl⟩ : syracuseStep 343277 = 128729) (by norm_num)
theorem B343301 : Blo 227813 343301 := bbase (se 4 (by rfl) ⟨32184, by rfl⟩ : syracuseStep 343301 = 64369) (by norm_num)
theorem B933125 : Blo 227813 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B343325 : Blo 227813 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B343349 : Blo 227813 343349 := bbase (se 5 (by rfl) ⟨16094, by rfl⟩ : syracuseStep 343349 = 32189) (by norm_num)
theorem B343373 : Blo 227813 343373 := bbase (se 3 (by rfl) ⟨64382, by rfl⟩ : syracuseStep 343373 = 128765) (by norm_num)
theorem B310613 : Blo 227813 310613 := bbase (se 11 (by rfl) ⟨227, by rfl⟩ : syracuseStep 310613 = 455) (by norm_num)
theorem B343397 : Blo 227813 343397 := bbase (se 4 (by rfl) ⟨32193, by rfl⟩ : syracuseStep 343397 = 64387) (by norm_num)
theorem B343421 : Blo 227813 343421 := bbase (se 3 (by rfl) ⟨64391, by rfl⟩ : syracuseStep 343421 = 128783) (by norm_num)
theorem B343445 : Blo 227813 343445 := bbase (se 6 (by rfl) ⟨8049, by rfl⟩ : syracuseStep 343445 = 16099) (by norm_num)
theorem B245149 : Blo 227813 245149 := bbase (se 3 (by rfl) ⟨45965, by rfl⟩ : syracuseStep 245149 = 91931) (by norm_num)
theorem B769445 : Blo 227813 769445 := bbase (se 4 (by rfl) ⟨72135, by rfl⟩ : syracuseStep 769445 = 144271) (by norm_num)
theorem B343469 : Blo 227813 343469 := bbase (se 3 (by rfl) ⟨64400, by rfl⟩ : syracuseStep 343469 = 128801) (by norm_num)
theorem B343493 : Blo 227813 343493 := bbase (se 4 (by rfl) ⟨32202, by rfl⟩ : syracuseStep 343493 = 64405) (by norm_num)
theorem B343517 : Blo 227813 343517 := bbase (se 3 (by rfl) ⟨64409, by rfl⟩ : syracuseStep 343517 = 128819) (by norm_num)
theorem B310765 : Blo 227813 310765 := bbase (se 3 (by rfl) ⟨58268, by rfl⟩ : syracuseStep 310765 = 116537) (by norm_num)
theorem B343541 : Blo 227813 343541 := bbase (se 5 (by rfl) ⟨16103, by rfl⟩ : syracuseStep 343541 = 32207) (by norm_num)
theorem B343565 : Blo 227813 343565 := bbase (se 3 (by rfl) ⟨64418, by rfl⟩ : syracuseStep 343565 = 128837) (by norm_num)
theorem B245269 : Blo 227813 245269 := bbase (se 6 (by rfl) ⟨5748, by rfl⟩ : syracuseStep 245269 = 11497) (by norm_num)
theorem B343589 : Blo 227813 343589 := bbase (se 4 (by rfl) ⟨32211, by rfl⟩ : syracuseStep 343589 = 64423) (by norm_num)
theorem B343613 : Blo 227813 343613 := bbase (se 3 (by rfl) ⟨64427, by rfl⟩ : syracuseStep 343613 = 128855) (by norm_num)
theorem B343637 : Blo 227813 343637 := bbase (se 8 (by rfl) ⟨2013, by rfl⟩ : syracuseStep 343637 = 4027) (by norm_num)
theorem B343661 : Blo 227813 343661 := bbase (se 3 (by rfl) ⟨64436, by rfl⟩ : syracuseStep 343661 = 128873) (by norm_num)
theorem B343685 : Blo 227813 343685 := bbase (se 4 (by rfl) ⟨32220, by rfl⟩ : syracuseStep 343685 = 64441) (by norm_num)
theorem B343709 : Blo 227813 343709 := bbase (se 3 (by rfl) ⟨64445, by rfl⟩ : syracuseStep 343709 = 128891) (by norm_num)
theorem B343733 : Blo 227813 343733 := bbase (se 5 (by rfl) ⟨16112, by rfl⟩ : syracuseStep 343733 = 32225) (by norm_num)
theorem B343757 : Blo 227813 343757 := bbase (se 3 (by rfl) ⟨64454, by rfl⟩ : syracuseStep 343757 = 128909) (by norm_num)
theorem B343781 : Blo 227813 343781 := bbase (se 4 (by rfl) ⟨32229, by rfl⟩ : syracuseStep 343781 = 64459) (by norm_num)
theorem B442093 : Blo 227813 442093 := bbase (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) (by norm_num)
theorem B1162997 : Blo 227813 1162997 := bbase (se 5 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 1162997 = 109031) (by norm_num)
theorem B343805 : Blo 227813 343805 := bbase (se 3 (by rfl) ⟨64463, by rfl⟩ : syracuseStep 343805 = 128927) (by norm_num)
theorem B278273 : Blo 227813 278273 := bbase (se 2 (by rfl) ⟨104352, by rfl⟩ : syracuseStep 278273 = 208705) (by norm_num)
theorem B245521 : Blo 227813 245521 := bbase (se 2 (by rfl) ⟨92070, by rfl⟩ : syracuseStep 245521 = 184141) (by norm_num)
theorem B868117 : Blo 227813 868117 := bbase (se 6 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 868117 = 40693) (by norm_num)
theorem B343829 : Blo 227813 343829 := bbase (se 6 (by rfl) ⟨8058, by rfl⟩ : syracuseStep 343829 = 16117) (by norm_num)
theorem B245525 : Blo 227813 245525 := bbase (se 6 (by rfl) ⟨5754, by rfl⟩ : syracuseStep 245525 = 11509) (by norm_num)
theorem B343853 : Blo 227813 343853 := bbase (se 3 (by rfl) ⟨64472, by rfl⟩ : syracuseStep 343853 = 128945) (by norm_num)
theorem B343877 : Blo 227813 343877 := bbase (se 4 (by rfl) ⟨32238, by rfl⟩ : syracuseStep 343877 = 64477) (by norm_num)
theorem B769877 : Blo 227813 769877 := bbase (se 9 (by rfl) ⟨2255, by rfl⟩ : syracuseStep 769877 = 4511) (by norm_num)
theorem B343901 : Blo 227813 343901 := bbase (se 3 (by rfl) ⟨64481, by rfl⟩ : syracuseStep 343901 = 128963) (by norm_num)
theorem B343925 : Blo 227813 343925 := bbase (se 5 (by rfl) ⟨16121, by rfl⟩ : syracuseStep 343925 = 32243) (by norm_num)
theorem B343949 : Blo 227813 343949 := bbase (se 3 (by rfl) ⟨64490, by rfl⟩ : syracuseStep 343949 = 128981) (by norm_num)
theorem B343973 : Blo 227813 343973 := bbase (se 4 (by rfl) ⟨32247, by rfl⟩ : syracuseStep 343973 = 64495) (by norm_num)
theorem B343997 : Blo 227813 343997 := bbase (se 3 (by rfl) ⟨64499, by rfl⟩ : syracuseStep 343997 = 128999) (by norm_num)
theorem B344021 : Blo 227813 344021 := bbase (se 7 (by rfl) ⟨4031, by rfl⟩ : syracuseStep 344021 = 8063) (by norm_num)
theorem B344045 : Blo 227813 344045 := bbase (se 3 (by rfl) ⟨64508, by rfl⟩ : syracuseStep 344045 = 129017) (by norm_num)
theorem B344069 : Blo 227813 344069 := bbase (se 4 (by rfl) ⟨32256, by rfl⟩ : syracuseStep 344069 = 64513) (by norm_num)
theorem B344093 : Blo 227813 344093 := bbase (se 3 (by rfl) ⟨64517, by rfl⟩ : syracuseStep 344093 = 129035) (by norm_num)
theorem B344117 : Blo 227813 344117 := bbase (se 5 (by rfl) ⟨16130, by rfl⟩ : syracuseStep 344117 = 32261) (by norm_num)
theorem B868421 : Blo 227813 868421 := bbase (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) (by norm_num)
theorem B344141 : Blo 227813 344141 := bbase (se 3 (by rfl) ⟨64526, by rfl⟩ : syracuseStep 344141 = 129053) (by norm_num)
theorem B344165 : Blo 227813 344165 := bbase (se 4 (by rfl) ⟨32265, by rfl⟩ : syracuseStep 344165 = 64531) (by norm_num)
theorem B344189 : Blo 227813 344189 := bbase (se 3 (by rfl) ⟨64535, by rfl⟩ : syracuseStep 344189 = 129071) (by norm_num)
theorem B344213 : Blo 227813 344213 := bbase (se 6 (by rfl) ⟨8067, by rfl⟩ : syracuseStep 344213 = 16135) (by norm_num)
theorem B344237 : Blo 227813 344237 := bbase (se 3 (by rfl) ⟨64544, by rfl⟩ : syracuseStep 344237 = 129089) (by norm_num)
theorem B344261 : Blo 227813 344261 := bbase (se 4 (by rfl) ⟨32274, by rfl⟩ : syracuseStep 344261 = 64549) (by norm_num)
theorem B344285 : Blo 227813 344285 := bbase (se 3 (by rfl) ⟨64553, by rfl⟩ : syracuseStep 344285 = 129107) (by norm_num)
theorem B344309 : Blo 227813 344309 := bbase (se 5 (by rfl) ⟨16139, by rfl⟩ : syracuseStep 344309 = 32279) (by norm_num)
theorem B737525 : Blo 227813 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B770309 : Blo 227813 770309 := bbase (se 4 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 770309 = 144433) (by norm_num)
theorem B344333 : Blo 227813 344333 := bbase (se 3 (by rfl) ⟨64562, by rfl⟩ : syracuseStep 344333 = 129125) (by norm_num)
theorem B344357 : Blo 227813 344357 := bbase (se 4 (by rfl) ⟨32283, by rfl⟩ : syracuseStep 344357 = 64567) (by norm_num)
theorem B344381 : Blo 227813 344381 := bbase (se 3 (by rfl) ⟨64571, by rfl⟩ : syracuseStep 344381 = 129143) (by norm_num)
theorem B246089 : Blo 227813 246089 := bbase (se 2 (by rfl) ⟨92283, by rfl⟩ : syracuseStep 246089 = 184567) (by norm_num)
theorem B344405 : Blo 227813 344405 := bbase (se 10 (by rfl) ⟨504, by rfl⟩ : syracuseStep 344405 = 1009) (by norm_num)
theorem B344429 : Blo 227813 344429 := bbase (se 3 (by rfl) ⟨64580, by rfl⟩ : syracuseStep 344429 = 129161) (by norm_num)
theorem B344453 : Blo 227813 344453 := bbase (se 4 (by rfl) ⟨32292, by rfl⟩ : syracuseStep 344453 = 64585) (by norm_num)
theorem B344477 : Blo 227813 344477 := bbase (se 3 (by rfl) ⟨64589, by rfl⟩ : syracuseStep 344477 = 129179) (by norm_num)
theorem B344501 : Blo 227813 344501 := bbase (se 5 (by rfl) ⟨16148, by rfl⟩ : syracuseStep 344501 = 32297) (by norm_num)
theorem B344525 : Blo 227813 344525 := bbase (se 3 (by rfl) ⟨64598, by rfl⟩ : syracuseStep 344525 = 129197) (by norm_num)
theorem B344549 : Blo 227813 344549 := bbase (se 4 (by rfl) ⟨32301, by rfl⟩ : syracuseStep 344549 = 64603) (by norm_num)
theorem B344573 : Blo 227813 344573 := bbase (se 3 (by rfl) ⟨64607, by rfl⟩ : syracuseStep 344573 = 129215) (by norm_num)
theorem B246277 : Blo 227813 246277 := bbase (se 4 (by rfl) ⟨23088, by rfl⟩ : syracuseStep 246277 = 46177) (by norm_num)
theorem B344597 : Blo 227813 344597 := bbase (se 6 (by rfl) ⟨8076, by rfl⟩ : syracuseStep 344597 = 16153) (by norm_num)
theorem B344621 : Blo 227813 344621 := bbase (se 3 (by rfl) ⟨64616, by rfl⟩ : syracuseStep 344621 = 129233) (by norm_num)
theorem B344645 : Blo 227813 344645 := bbase (se 4 (by rfl) ⟨32310, by rfl⟩ : syracuseStep 344645 = 64621) (by norm_num)
theorem B344669 : Blo 227813 344669 := bbase (se 3 (by rfl) ⟨64625, by rfl⟩ : syracuseStep 344669 = 129251) (by norm_num)
theorem B344693 : Blo 227813 344693 := bbase (se 5 (by rfl) ⟨16157, by rfl⟩ : syracuseStep 344693 = 32315) (by norm_num)
theorem B344717 : Blo 227813 344717 := bbase (se 3 (by rfl) ⟨64634, by rfl⟩ : syracuseStep 344717 = 129269) (by norm_num)
theorem B344741 : Blo 227813 344741 := bbase (se 4 (by rfl) ⟨32319, by rfl⟩ : syracuseStep 344741 = 64639) (by norm_num)
theorem B770741 : Blo 227813 770741 := bbase (se 5 (by rfl) ⟨36128, by rfl⟩ : syracuseStep 770741 = 72257) (by norm_num)
theorem B344765 : Blo 227813 344765 := bbase (se 3 (by rfl) ⟨64643, by rfl⟩ : syracuseStep 344765 = 129287) (by norm_num)
theorem B344789 : Blo 227813 344789 := bbase (se 7 (by rfl) ⟨4040, by rfl⟩ : syracuseStep 344789 = 8081) (by norm_num)
theorem B344813 : Blo 227813 344813 := bbase (se 3 (by rfl) ⟨64652, by rfl⟩ : syracuseStep 344813 = 129305) (by norm_num)
theorem B344837 : Blo 227813 344837 := bbase (se 4 (by rfl) ⟨32328, by rfl⟩ : syracuseStep 344837 = 64657) (by norm_num)
theorem B344861 : Blo 227813 344861 := bbase (se 3 (by rfl) ⟨64661, by rfl⟩ : syracuseStep 344861 = 129323) (by norm_num)
theorem B344885 : Blo 227813 344885 := bbase (se 5 (by rfl) ⟨16166, by rfl⟩ : syracuseStep 344885 = 32333) (by norm_num)
theorem B344909 : Blo 227813 344909 := bbase (se 3 (by rfl) ⟨64670, by rfl⟩ : syracuseStep 344909 = 129341) (by norm_num)
theorem B344933 : Blo 227813 344933 := bbase (se 4 (by rfl) ⟨32337, by rfl⟩ : syracuseStep 344933 = 64675) (by norm_num)
theorem B1753973 : Blo 227813 1753973 := bbase (se 5 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 1753973 = 164435) (by norm_num)
theorem B344957 : Blo 227813 344957 := bbase (se 3 (by rfl) ⟨64679, by rfl⟩ : syracuseStep 344957 = 129359) (by norm_num)
theorem B344981 : Blo 227813 344981 := bbase (se 6 (by rfl) ⟨8085, by rfl⟩ : syracuseStep 344981 = 16171) (by norm_num)
theorem B345005 : Blo 227813 345005 := bbase (se 3 (by rfl) ⟨64688, by rfl⟩ : syracuseStep 345005 = 129377) (by norm_num)
theorem B345029 : Blo 227813 345029 := bbase (se 4 (by rfl) ⟨32346, by rfl⟩ : syracuseStep 345029 = 64693) (by norm_num)
theorem B345053 : Blo 227813 345053 := bbase (se 3 (by rfl) ⟨64697, by rfl⟩ : syracuseStep 345053 = 129395) (by norm_num)
theorem B345077 : Blo 227813 345077 := bbase (se 5 (by rfl) ⟨16175, by rfl⟩ : syracuseStep 345077 = 32351) (by norm_num)
theorem B1164293 : Blo 227813 1164293 := bbase (se 4 (by rfl) ⟨109152, by rfl⟩ : syracuseStep 1164293 = 218305) (by norm_num)
theorem B345101 : Blo 227813 345101 := bbase (se 3 (by rfl) ⟨64706, by rfl⟩ : syracuseStep 345101 = 129413) (by norm_num)
theorem B345125 : Blo 227813 345125 := bbase (se 4 (by rfl) ⟨32355, by rfl⟩ : syracuseStep 345125 = 64711) (by norm_num)
theorem B345149 : Blo 227813 345149 := bbase (se 3 (by rfl) ⟨64715, by rfl⟩ : syracuseStep 345149 = 129431) (by norm_num)
theorem B345173 : Blo 227813 345173 := bbase (se 8 (by rfl) ⟨2022, by rfl⟩ : syracuseStep 345173 = 4045) (by norm_num)
theorem B771173 : Blo 227813 771173 := bbase (se 4 (by rfl) ⟨72297, by rfl⟩ : syracuseStep 771173 = 144595) (by norm_num)
theorem B345197 : Blo 227813 345197 := bbase (se 3 (by rfl) ⟨64724, by rfl⟩ : syracuseStep 345197 = 129449) (by norm_num)
theorem B345221 : Blo 227813 345221 := bbase (se 4 (by rfl) ⟨32364, by rfl⟩ : syracuseStep 345221 = 64729) (by norm_num)
theorem B345245 : Blo 227813 345245 := bbase (se 3 (by rfl) ⟨64733, by rfl⟩ : syracuseStep 345245 = 129467) (by norm_num)
theorem B345269 : Blo 227813 345269 := bbase (se 5 (by rfl) ⟨16184, by rfl⟩ : syracuseStep 345269 = 32369) (by norm_num)
theorem B345293 : Blo 227813 345293 := bbase (se 3 (by rfl) ⟨64742, by rfl⟩ : syracuseStep 345293 = 129485) (by norm_num)
theorem B345317 : Blo 227813 345317 := bbase (se 4 (by rfl) ⟨32373, by rfl⟩ : syracuseStep 345317 = 64747) (by norm_num)
theorem B345341 : Blo 227813 345341 := bbase (se 3 (by rfl) ⟨64751, by rfl⟩ : syracuseStep 345341 = 129503) (by norm_num)
theorem B345365 : Blo 227813 345365 := bbase (se 6 (by rfl) ⟨8094, by rfl⟩ : syracuseStep 345365 = 16189) (by norm_num)
theorem B345389 : Blo 227813 345389 := bbase (se 3 (by rfl) ⟨64760, by rfl⟩ : syracuseStep 345389 = 129521) (by norm_num)
theorem B247097 : Blo 227813 247097 := bbase (se 2 (by rfl) ⟨92661, by rfl⟩ : syracuseStep 247097 = 185323) (by norm_num)
theorem B345413 : Blo 227813 345413 := bbase (se 4 (by rfl) ⟨32382, by rfl⟩ : syracuseStep 345413 = 64765) (by norm_num)
theorem B345437 : Blo 227813 345437 := bbase (se 3 (by rfl) ⟨64769, by rfl⟩ : syracuseStep 345437 = 129539) (by norm_num)
theorem B345461 : Blo 227813 345461 := bbase (se 5 (by rfl) ⟨16193, by rfl⟩ : syracuseStep 345461 = 32387) (by norm_num)
theorem B345485 : Blo 227813 345485 := bbase (se 3 (by rfl) ⟨64778, by rfl⟩ : syracuseStep 345485 = 129557) (by norm_num)
theorem B345509 : Blo 227813 345509 := bbase (se 4 (by rfl) ⟨32391, by rfl⟩ : syracuseStep 345509 = 64783) (by norm_num)
theorem B345533 : Blo 227813 345533 := bbase (se 3 (by rfl) ⟨64787, by rfl⟩ : syracuseStep 345533 = 129575) (by norm_num)
theorem B247249 : Blo 227813 247249 := bbase (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) (by norm_num)
theorem B345557 : Blo 227813 345557 := bbase (se 7 (by rfl) ⟨4049, by rfl⟩ : syracuseStep 345557 = 8099) (by norm_num)
theorem B345581 : Blo 227813 345581 := bbase (se 3 (by rfl) ⟨64796, by rfl⟩ : syracuseStep 345581 = 129593) (by norm_num)
theorem B345605 : Blo 227813 345605 := bbase (se 4 (by rfl) ⟨32400, by rfl⟩ : syracuseStep 345605 = 64801) (by norm_num)
theorem B771605 : Blo 227813 771605 := bbase (se 6 (by rfl) ⟨18084, by rfl⟩ : syracuseStep 771605 = 36169) (by norm_num)
theorem B345629 : Blo 227813 345629 := bbase (se 3 (by rfl) ⟨64805, by rfl⟩ : syracuseStep 345629 = 129611) (by norm_num)
theorem B345653 : Blo 227813 345653 := bbase (se 5 (by rfl) ⟨16202, by rfl⟩ : syracuseStep 345653 = 32405) (by norm_num)
theorem B345677 : Blo 227813 345677 := bbase (se 3 (by rfl) ⟨64814, by rfl⟩ : syracuseStep 345677 = 129629) (by norm_num)
theorem B345701 : Blo 227813 345701 := bbase (se 4 (by rfl) ⟨32409, by rfl⟩ : syracuseStep 345701 = 64819) (by norm_num)
theorem B345725 : Blo 227813 345725 := bbase (se 3 (by rfl) ⟨64823, by rfl⟩ : syracuseStep 345725 = 129647) (by norm_num)
theorem B345749 : Blo 227813 345749 := bbase (se 6 (by rfl) ⟨8103, by rfl⟩ : syracuseStep 345749 = 16207) (by norm_num)
theorem B345773 : Blo 227813 345773 := bbase (se 3 (by rfl) ⟨64832, by rfl⟩ : syracuseStep 345773 = 129665) (by norm_num)
theorem B345797 : Blo 227813 345797 := bbase (se 4 (by rfl) ⟨32418, by rfl⟩ : syracuseStep 345797 = 64837) (by norm_num)
theorem B345821 : Blo 227813 345821 := bbase (se 3 (by rfl) ⟨64841, by rfl⟩ : syracuseStep 345821 = 129683) (by norm_num)
theorem B345845 : Blo 227813 345845 := bbase (se 5 (by rfl) ⟨16211, by rfl⟩ : syracuseStep 345845 = 32423) (by norm_num)
theorem B247541 : Blo 227813 247541 := bbase (se 5 (by rfl) ⟨11603, by rfl⟩ : syracuseStep 247541 = 23207) (by norm_num)
theorem B345869 : Blo 227813 345869 := bbase (se 3 (by rfl) ⟨64850, by rfl⟩ : syracuseStep 345869 = 129701) (by norm_num)
theorem B345893 : Blo 227813 345893 := bbase (se 4 (by rfl) ⟨32427, by rfl⟩ : syracuseStep 345893 = 64855) (by norm_num)
theorem B345917 : Blo 227813 345917 := bbase (se 3 (by rfl) ⟨64859, by rfl⟩ : syracuseStep 345917 = 129719) (by norm_num)
theorem B345941 : Blo 227813 345941 := bbase (se 9 (by rfl) ⟨1013, by rfl⟩ : syracuseStep 345941 = 2027) (by norm_num)
theorem B411493 : Blo 227813 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B345965 : Blo 227813 345965 := bbase (se 3 (by rfl) ⟨64868, by rfl⟩ : syracuseStep 345965 = 129737) (by norm_num)
theorem B345989 : Blo 227813 345989 := bbase (se 4 (by rfl) ⟨32436, by rfl⟩ : syracuseStep 345989 = 64873) (by norm_num)
theorem B346013 : Blo 227813 346013 := bbase (se 3 (by rfl) ⟨64877, by rfl⟩ : syracuseStep 346013 = 129755) (by norm_num)
theorem B346037 : Blo 227813 346037 := bbase (se 5 (by rfl) ⟨16220, by rfl⟩ : syracuseStep 346037 = 32441) (by norm_num)
theorem B772037 : Blo 227813 772037 := bbase (se 4 (by rfl) ⟨72378, by rfl⟩ : syracuseStep 772037 = 144757) (by norm_num)
theorem B346061 : Blo 227813 346061 := bbase (se 3 (by rfl) ⟨64886, by rfl⟩ : syracuseStep 346061 = 129773) (by norm_num)
theorem B346085 : Blo 227813 346085 := bbase (se 4 (by rfl) ⟨32445, by rfl⟩ : syracuseStep 346085 = 64891) (by norm_num)
theorem B346109 : Blo 227813 346109 := bbase (se 3 (by rfl) ⟨64895, by rfl⟩ : syracuseStep 346109 = 129791) (by norm_num)
theorem B346133 : Blo 227813 346133 := bbase (se 6 (by rfl) ⟨8112, by rfl⟩ : syracuseStep 346133 = 16225) (by norm_num)
theorem B346157 : Blo 227813 346157 := bbase (se 3 (by rfl) ⟨64904, by rfl⟩ : syracuseStep 346157 = 129809) (by norm_num)
theorem B346181 : Blo 227813 346181 := bbase (se 4 (by rfl) ⟨32454, by rfl⟩ : syracuseStep 346181 = 64909) (by norm_num)
theorem B346205 : Blo 227813 346205 := bbase (se 3 (by rfl) ⟨64913, by rfl⟩ : syracuseStep 346205 = 129827) (by norm_num)
theorem B1656949 : Blo 227813 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B346229 : Blo 227813 346229 := bbase (se 5 (by rfl) ⟨16229, by rfl⟩ : syracuseStep 346229 = 32459) (by norm_num)
theorem B870533 : Blo 227813 870533 := bbase (se 4 (by rfl) ⟨81612, by rfl⟩ : syracuseStep 870533 = 163225) (by norm_num)
theorem B346253 : Blo 227813 346253 := bbase (se 3 (by rfl) ⟨64922, by rfl⟩ : syracuseStep 346253 = 129845) (by norm_num)
theorem B1099925 : Blo 227813 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B346277 : Blo 227813 346277 := bbase (se 4 (by rfl) ⟨32463, by rfl⟩ : syracuseStep 346277 = 64927) (by norm_num)
theorem B346301 : Blo 227813 346301 := bbase (se 3 (by rfl) ⟨64931, by rfl⟩ : syracuseStep 346301 = 129863) (by norm_num)
theorem B346325 : Blo 227813 346325 := bbase (se 7 (by rfl) ⟨4058, by rfl⟩ : syracuseStep 346325 = 8117) (by norm_num)
theorem B346349 : Blo 227813 346349 := bbase (se 3 (by rfl) ⟨64940, by rfl⟩ : syracuseStep 346349 = 129881) (by norm_num)
theorem B346373 : Blo 227813 346373 := bbase (se 4 (by rfl) ⟨32472, by rfl⟩ : syracuseStep 346373 = 64945) (by norm_num)
theorem B1165589 : Blo 227813 1165589 := bbase (se 6 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 1165589 = 54637) (by norm_num)
theorem B346397 : Blo 227813 346397 := bbase (se 3 (by rfl) ⟨64949, by rfl⟩ : syracuseStep 346397 = 129899) (by norm_num)
theorem B346421 : Blo 227813 346421 := bbase (se 5 (by rfl) ⟨16238, by rfl⟩ : syracuseStep 346421 = 32477) (by norm_num)
theorem B346445 : Blo 227813 346445 := bbase (se 3 (by rfl) ⟨64958, by rfl⟩ : syracuseStep 346445 = 129917) (by norm_num)
theorem B346469 : Blo 227813 346469 := bbase (se 4 (by rfl) ⟨32481, by rfl⟩ : syracuseStep 346469 = 64963) (by norm_num)
theorem B772469 : Blo 227813 772469 := bbase (se 5 (by rfl) ⟨36209, by rfl⟩ : syracuseStep 772469 = 72419) (by norm_num)
theorem B346493 : Blo 227813 346493 := bbase (se 3 (by rfl) ⟨64967, by rfl⟩ : syracuseStep 346493 = 129935) (by norm_num)
theorem B346517 : Blo 227813 346517 := bbase (se 6 (by rfl) ⟨8121, by rfl⟩ : syracuseStep 346517 = 16243) (by norm_num)
theorem B870821 : Blo 227813 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B346541 : Blo 227813 346541 := bbase (se 3 (by rfl) ⟨64976, by rfl⟩ : syracuseStep 346541 = 129953) (by norm_num)
theorem B346565 : Blo 227813 346565 := bbase (se 4 (by rfl) ⟨32490, by rfl⟩ : syracuseStep 346565 = 64981) (by norm_num)
theorem B346589 : Blo 227813 346589 := bbase (se 3 (by rfl) ⟨64985, by rfl⟩ : syracuseStep 346589 = 129971) (by norm_num)
theorem B346613 : Blo 227813 346613 := bbase (se 5 (by rfl) ⟨16247, by rfl⟩ : syracuseStep 346613 = 32495) (by norm_num)
theorem B346637 : Blo 227813 346637 := bbase (se 3 (by rfl) ⟨64994, by rfl⟩ : syracuseStep 346637 = 129989) (by norm_num)
theorem B346661 : Blo 227813 346661 := bbase (se 4 (by rfl) ⟨32499, by rfl⟩ : syracuseStep 346661 = 64999) (by norm_num)
theorem B346685 : Blo 227813 346685 := bbase (se 3 (by rfl) ⟨65003, by rfl⟩ : syracuseStep 346685 = 130007) (by norm_num)
theorem B346709 : Blo 227813 346709 := bbase (se 8 (by rfl) ⟨2031, by rfl⟩ : syracuseStep 346709 = 4063) (by norm_num)
theorem B346733 : Blo 227813 346733 := bbase (se 3 (by rfl) ⟨65012, by rfl⟩ : syracuseStep 346733 = 130025) (by norm_num)
theorem B346757 : Blo 227813 346757 := bbase (se 4 (by rfl) ⟨32508, by rfl⟩ : syracuseStep 346757 = 65017) (by norm_num)
theorem B1493653 : Blo 227813 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B346781 : Blo 227813 346781 := bbase (se 3 (by rfl) ⟨65021, by rfl⟩ : syracuseStep 346781 = 130043) (by norm_num)
theorem B936629 : Blo 227813 936629 := bbase (se 5 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 936629 = 87809) (by norm_num)
theorem B346805 : Blo 227813 346805 := bbase (se 5 (by rfl) ⟨16256, by rfl⟩ : syracuseStep 346805 = 32513) (by norm_num)
theorem B346829 : Blo 227813 346829 := bbase (se 3 (by rfl) ⟨65030, by rfl⟩ : syracuseStep 346829 = 130061) (by norm_num)
theorem B9358037 : Blo 227813 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B346853 : Blo 227813 346853 := bbase (se 4 (by rfl) ⟨32517, by rfl⟩ : syracuseStep 346853 = 65035) (by norm_num)
theorem B346877 : Blo 227813 346877 := bbase (se 3 (by rfl) ⟨65039, by rfl⟩ : syracuseStep 346877 = 130079) (by norm_num)
theorem B346901 : Blo 227813 346901 := bbase (se 6 (by rfl) ⟨8130, by rfl⟩ : syracuseStep 346901 = 16261) (by norm_num)
theorem B772901 : Blo 227813 772901 := bbase (se 4 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 772901 = 144919) (by norm_num)
theorem B346925 : Blo 227813 346925 := bbase (se 3 (by rfl) ⟨65048, by rfl⟩ : syracuseStep 346925 = 130097) (by norm_num)
theorem B346949 : Blo 227813 346949 := bbase (se 4 (by rfl) ⟨32526, by rfl⟩ : syracuseStep 346949 = 65053) (by norm_num)
theorem B346973 : Blo 227813 346973 := bbase (se 3 (by rfl) ⟨65057, by rfl⟩ : syracuseStep 346973 = 130115) (by norm_num)
theorem B346997 : Blo 227813 346997 := bbase (se 5 (by rfl) ⟨16265, by rfl⟩ : syracuseStep 346997 = 32531) (by norm_num)
theorem B347021 : Blo 227813 347021 := bbase (se 3 (by rfl) ⟨65066, by rfl⟩ : syracuseStep 347021 = 130133) (by norm_num)
theorem B347045 : Blo 227813 347045 := bbase (se 4 (by rfl) ⟨32535, by rfl⟩ : syracuseStep 347045 = 65071) (by norm_num)
theorem B347069 : Blo 227813 347069 := bbase (se 3 (by rfl) ⟨65075, by rfl⟩ : syracuseStep 347069 = 130151) (by norm_num)
theorem B347093 : Blo 227813 347093 := bbase (se 7 (by rfl) ⟨4067, by rfl⟩ : syracuseStep 347093 = 8135) (by norm_num)
theorem B347117 : Blo 227813 347117 := bbase (se 3 (by rfl) ⟨65084, by rfl⟩ : syracuseStep 347117 = 130169) (by norm_num)
theorem B347141 : Blo 227813 347141 := bbase (se 4 (by rfl) ⟨32544, by rfl⟩ : syracuseStep 347141 = 65089) (by norm_num)
theorem B347165 : Blo 227813 347165 := bbase (se 3 (by rfl) ⟨65093, by rfl⟩ : syracuseStep 347165 = 130187) (by norm_num)
theorem B412709 : Blo 227813 412709 := bbase (se 4 (by rfl) ⟨38691, by rfl⟩ : syracuseStep 412709 = 77383) (by norm_num)
theorem B347189 : Blo 227813 347189 := bbase (se 5 (by rfl) ⟨16274, by rfl⟩ : syracuseStep 347189 = 32549) (by norm_num)
theorem B347213 : Blo 227813 347213 := bbase (se 3 (by rfl) ⟨65102, by rfl⟩ : syracuseStep 347213 = 130205) (by norm_num)
theorem B347237 : Blo 227813 347237 := bbase (se 4 (by rfl) ⟨32553, by rfl⟩ : syracuseStep 347237 = 65107) (by norm_num)
theorem B347261 : Blo 227813 347261 := bbase (se 3 (by rfl) ⟨65111, by rfl⟩ : syracuseStep 347261 = 130223) (by norm_num)
theorem B347285 : Blo 227813 347285 := bbase (se 6 (by rfl) ⟨8139, by rfl⟩ : syracuseStep 347285 = 16279) (by norm_num)
theorem B347309 : Blo 227813 347309 := bbase (se 3 (by rfl) ⟨65120, by rfl⟩ : syracuseStep 347309 = 130241) (by norm_num)
theorem B347333 : Blo 227813 347333 := bbase (se 4 (by rfl) ⟨32562, by rfl⟩ : syracuseStep 347333 = 65125) (by norm_num)
theorem B412877 : Blo 227813 412877 := bbase (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) (by norm_num)
theorem B773333 : Blo 227813 773333 := bbase (se 7 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 773333 = 18125) (by norm_num)
theorem B347357 : Blo 227813 347357 := bbase (se 3 (by rfl) ⟨65129, by rfl⟩ : syracuseStep 347357 = 130259) (by norm_num)
theorem B347381 : Blo 227813 347381 := bbase (se 5 (by rfl) ⟨16283, by rfl⟩ : syracuseStep 347381 = 32567) (by norm_num)
theorem B347405 : Blo 227813 347405 := bbase (se 3 (by rfl) ⟨65138, by rfl⟩ : syracuseStep 347405 = 130277) (by norm_num)
theorem B347429 : Blo 227813 347429 := bbase (se 4 (by rfl) ⟨32571, by rfl⟩ : syracuseStep 347429 = 65143) (by norm_num)
theorem B576821 : Blo 227813 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B347453 : Blo 227813 347453 := bbase (se 3 (by rfl) ⟨65147, by rfl⟩ : syracuseStep 347453 = 130295) (by norm_num)
theorem B347477 : Blo 227813 347477 := bbase (se 11 (by rfl) ⟨254, by rfl⟩ : syracuseStep 347477 = 509) (by norm_num)
theorem B347501 : Blo 227813 347501 := bbase (se 3 (by rfl) ⟨65156, by rfl⟩ : syracuseStep 347501 = 130313) (by norm_num)
theorem B1297781 : Blo 227813 1297781 := bbase (se 5 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 1297781 = 121667) (by norm_num)
theorem B347525 : Blo 227813 347525 := bbase (se 4 (by rfl) ⟨32580, by rfl⟩ : syracuseStep 347525 = 65161) (by norm_num)
theorem B347549 : Blo 227813 347549 := bbase (se 3 (by rfl) ⟨65165, by rfl⟩ : syracuseStep 347549 = 130331) (by norm_num)
theorem B347573 : Blo 227813 347573 := bbase (se 5 (by rfl) ⟨16292, by rfl⟩ : syracuseStep 347573 = 32585) (by norm_num)
theorem B347597 : Blo 227813 347597 := bbase (se 3 (by rfl) ⟨65174, by rfl⟩ : syracuseStep 347597 = 130349) (by norm_num)
theorem B347621 : Blo 227813 347621 := bbase (se 4 (by rfl) ⟨32589, by rfl⟩ : syracuseStep 347621 = 65179) (by norm_num)
theorem B282109 : Blo 227813 282109 := bbase (se 3 (by rfl) ⟨52895, by rfl⟩ : syracuseStep 282109 = 105791) (by norm_num)
theorem B347645 : Blo 227813 347645 := bbase (se 3 (by rfl) ⟨65183, by rfl⟩ : syracuseStep 347645 = 130367) (by norm_num)
theorem B347669 : Blo 227813 347669 := bbase (se 6 (by rfl) ⟨8148, by rfl⟩ : syracuseStep 347669 = 16297) (by norm_num)
theorem B1166885 : Blo 227813 1166885 := bbase (se 4 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 1166885 = 218791) (by norm_num)
theorem B347693 : Blo 227813 347693 := bbase (se 3 (by rfl) ⟨65192, by rfl⟩ : syracuseStep 347693 = 130385) (by norm_num)
theorem B872005 : Blo 227813 872005 := bbase (se 4 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 872005 = 163501) (by norm_num)
theorem B740933 : Blo 227813 740933 := bbase (se 4 (by rfl) ⟨69462, by rfl⟩ : syracuseStep 740933 = 138925) (by norm_num)
theorem B347717 : Blo 227813 347717 := bbase (se 4 (by rfl) ⟨32598, by rfl⟩ : syracuseStep 347717 = 65197) (by norm_num)
theorem B773765 : Blo 227813 773765 := bbase (se 4 (by rfl) ⟨72540, by rfl⟩ : syracuseStep 773765 = 145081) (by norm_num)
theorem B577165 : Blo 227813 577165 := bbase (se 3 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 577165 = 216437) (by norm_num)
theorem B249565 : Blo 227813 249565 := bbase (se 3 (by rfl) ⟨46793, by rfl⟩ : syracuseStep 249565 = 93587) (by norm_num)
theorem B577277 : Blo 227813 577277 := bbase (se 3 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 577277 = 216479) (by norm_num)
theorem B872309 : Blo 227813 872309 := bbase (se 5 (by rfl) ⟨40889, by rfl⟩ : syracuseStep 872309 = 81779) (by norm_num)
theorem B577469 : Blo 227813 577469 := bbase (se 3 (by rfl) ⟨108275, by rfl⟩ : syracuseStep 577469 = 216551) (by norm_num)
theorem B937973 : Blo 227813 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B446485 : Blo 227813 446485 := bbase (se 6 (by rfl) ⟨10464, by rfl⟩ : syracuseStep 446485 = 20929) (by norm_num)
theorem B774197 : Blo 227813 774197 := bbase (se 5 (by rfl) ⟨36290, by rfl⟩ : syracuseStep 774197 = 72581) (by norm_num)
theorem B1101941 : Blo 227813 1101941 := bbase (se 5 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 1101941 = 103307) (by norm_num)
theorem B577813 : Blo 227813 577813 := bbase (se 6 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 577813 = 27085) (by norm_num)
theorem B577925 : Blo 227813 577925 := bbase (se 4 (by rfl) ⟨54180, by rfl⟩ : syracuseStep 577925 = 108361) (by norm_num)
theorem B348565 : Blo 227813 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B774629 : Blo 227813 774629 := bbase (se 4 (by rfl) ⟨72621, by rfl⟩ : syracuseStep 774629 = 145243) (by norm_num)
theorem B578117 : Blo 227813 578117 := bbase (se 4 (by rfl) ⟨54198, by rfl⟩ : syracuseStep 578117 = 108397) (by norm_num)
theorem B512621 : Blo 227813 512621 := bbase (se 3 (by rfl) ⟨96116, by rfl⟩ : syracuseStep 512621 = 192233) (by norm_num)
theorem B512693 : Blo 227813 512693 := bbase (se 5 (by rfl) ⟨24032, by rfl⟩ : syracuseStep 512693 = 48065) (by norm_num)
theorem B512765 : Blo 227813 512765 := bbase (se 3 (by rfl) ⟨96143, by rfl⟩ : syracuseStep 512765 = 192287) (by norm_num)
theorem B1168181 : Blo 227813 1168181 := bbase (se 5 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 1168181 = 109517) (by norm_num)
theorem B512837 : Blo 227813 512837 := bbase (se 4 (by rfl) ⟨48078, by rfl⟩ : syracuseStep 512837 = 96157) (by norm_num)
theorem B742213 : Blo 227813 742213 := bbase (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) (by norm_num)
theorem B1102693 : Blo 227813 1102693 := bbase (se 4 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 1102693 = 206755) (by norm_num)
theorem B512909 : Blo 227813 512909 := bbase (se 3 (by rfl) ⟨96170, by rfl⟩ : syracuseStep 512909 = 192341) (by norm_num)
theorem B775061 : Blo 227813 775061 := bbase (se 6 (by rfl) ⟨18165, by rfl⟩ : syracuseStep 775061 = 36331) (by norm_num)
theorem B578461 : Blo 227813 578461 := bbase (se 3 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 578461 = 216923) (by norm_num)
theorem B512981 : Blo 227813 512981 := bbase (se 7 (by rfl) ⟨6011, by rfl⟩ : syracuseStep 512981 = 12023) (by norm_num)
theorem B1463285 : Blo 227813 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B578573 : Blo 227813 578573 := bbase (se 3 (by rfl) ⟨108482, by rfl⟩ : syracuseStep 578573 = 216965) (by norm_num)
theorem B513053 : Blo 227813 513053 := bbase (se 3 (by rfl) ⟨96197, by rfl⟩ : syracuseStep 513053 = 192395) (by norm_num)
theorem B513125 : Blo 227813 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B513197 : Blo 227813 513197 := bbase (se 3 (by rfl) ⟨96224, by rfl⟩ : syracuseStep 513197 = 192449) (by norm_num)
theorem B578765 : Blo 227813 578765 := bbase (se 3 (by rfl) ⟨108518, by rfl⟩ : syracuseStep 578765 = 217037) (by norm_num)
theorem B513269 : Blo 227813 513269 := bbase (se 5 (by rfl) ⟨24059, by rfl⟩ : syracuseStep 513269 = 48119) (by norm_num)
theorem B513341 : Blo 227813 513341 := bbase (se 3 (by rfl) ⟨96251, by rfl⟩ : syracuseStep 513341 = 192503) (by norm_num)
theorem B775493 : Blo 227813 775493 := bbase (se 4 (by rfl) ⟨72702, by rfl⟩ : syracuseStep 775493 = 145405) (by norm_num)
theorem B513413 : Blo 227813 513413 := bbase (se 4 (by rfl) ⟨48132, by rfl⟩ : syracuseStep 513413 = 96265) (by norm_num)
theorem B513485 : Blo 227813 513485 := bbase (se 3 (by rfl) ⟨96278, by rfl⟩ : syracuseStep 513485 = 192557) (by norm_num)
theorem B513557 : Blo 227813 513557 := bbase (se 6 (by rfl) ⟨12036, by rfl⟩ : syracuseStep 513557 = 24073) (by norm_num)
theorem B1299989 : Blo 227813 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B579109 : Blo 227813 579109 := bbase (se 4 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 579109 = 108583) (by norm_num)
theorem B513629 : Blo 227813 513629 := bbase (se 3 (by rfl) ⟨96305, by rfl⟩ : syracuseStep 513629 = 192611) (by norm_num)
theorem B579221 : Blo 227813 579221 := bbase (se 6 (by rfl) ⟨13575, by rfl⟩ : syracuseStep 579221 = 27151) (by norm_num)
theorem B513701 : Blo 227813 513701 := bbase (se 4 (by rfl) ⟨48159, by rfl⟩ : syracuseStep 513701 = 96319) (by norm_num)
theorem B513773 : Blo 227813 513773 := bbase (se 3 (by rfl) ⟨96332, by rfl⟩ : syracuseStep 513773 = 192665) (by norm_num)
theorem B775925 : Blo 227813 775925 := bbase (se 5 (by rfl) ⟨36371, by rfl⟩ : syracuseStep 775925 = 72743) (by norm_num)
theorem B415477 : Blo 227813 415477 := bbase (se 5 (by rfl) ⟨19475, by rfl⟩ : syracuseStep 415477 = 38951) (by norm_num)
theorem B513845 : Blo 227813 513845 := bbase (se 5 (by rfl) ⟨24086, by rfl⟩ : syracuseStep 513845 = 48173) (by norm_num)
theorem B579413 : Blo 227813 579413 := bbase (se 9 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 579413 = 3395) (by norm_num)
theorem B382837 : Blo 227813 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B513917 : Blo 227813 513917 := bbase (se 3 (by rfl) ⟨96359, by rfl⟩ : syracuseStep 513917 = 192719) (by norm_num)
theorem B874421 : Blo 227813 874421 := bbase (se 5 (by rfl) ⟨40988, by rfl⟩ : syracuseStep 874421 = 81977) (by norm_num)
theorem B513989 : Blo 227813 513989 := bbase (se 4 (by rfl) ⟨48186, by rfl⟩ : syracuseStep 513989 = 96373) (by norm_num)
theorem B514061 : Blo 227813 514061 := bbase (se 3 (by rfl) ⟨96386, by rfl⟩ : syracuseStep 514061 = 192773) (by norm_num)
theorem B415781 : Blo 227813 415781 := bbase (se 4 (by rfl) ⟨38979, by rfl⟩ : syracuseStep 415781 = 77959) (by norm_num)
theorem B1169477 : Blo 227813 1169477 := bbase (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) (by norm_num)
theorem B514133 : Blo 227813 514133 := bbase (se 8 (by rfl) ⟨3012, by rfl⟩ : syracuseStep 514133 = 6025) (by norm_num)
theorem B514205 : Blo 227813 514205 := bbase (se 3 (by rfl) ⟨96413, by rfl⟩ : syracuseStep 514205 = 192827) (by norm_num)
theorem B776357 : Blo 227813 776357 := bbase (se 4 (by rfl) ⟨72783, by rfl⟩ : syracuseStep 776357 = 145567) (by norm_num)
theorem B579757 : Blo 227813 579757 := bbase (se 3 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 579757 = 217409) (by norm_num)
theorem B874709 : Blo 227813 874709 := bbase (se 7 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 874709 = 20501) (by norm_num)
theorem B514277 : Blo 227813 514277 := bbase (se 4 (by rfl) ⟨48213, by rfl⟩ : syracuseStep 514277 = 96427) (by norm_num)
theorem B579869 : Blo 227813 579869 := bbase (se 3 (by rfl) ⟨108725, by rfl⟩ : syracuseStep 579869 = 217451) (by norm_num)
theorem B514349 : Blo 227813 514349 := bbase (se 3 (by rfl) ⟨96440, by rfl⟩ : syracuseStep 514349 = 192881) (by norm_num)
theorem B514421 : Blo 227813 514421 := bbase (se 5 (by rfl) ⟨24113, by rfl⟩ : syracuseStep 514421 = 48227) (by norm_num)
theorem B514493 : Blo 227813 514493 := bbase (se 3 (by rfl) ⟨96467, by rfl⟩ : syracuseStep 514493 = 192935) (by norm_num)
theorem B580061 : Blo 227813 580061 := bbase (se 3 (by rfl) ⟨108761, by rfl⟩ : syracuseStep 580061 = 217523) (by norm_num)
theorem B514565 : Blo 227813 514565 := bbase (se 4 (by rfl) ⟨48240, by rfl⟩ : syracuseStep 514565 = 96481) (by norm_num)
theorem B514637 : Blo 227813 514637 := bbase (se 3 (by rfl) ⟨96494, by rfl⟩ : syracuseStep 514637 = 192989) (by norm_num)
theorem B776789 : Blo 227813 776789 := bbase (se 8 (by rfl) ⟨4551, by rfl⟩ : syracuseStep 776789 = 9103) (by norm_num)
theorem B514709 : Blo 227813 514709 := bbase (se 6 (by rfl) ⟨12063, by rfl⟩ : syracuseStep 514709 = 24127) (by norm_num)
theorem B514781 : Blo 227813 514781 := bbase (se 3 (by rfl) ⟨96521, by rfl⟩ : syracuseStep 514781 = 193043) (by norm_num)
theorem B449293 : Blo 227813 449293 := bbase (se 3 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 449293 = 168485) (by norm_num)
theorem B514853 : Blo 227813 514853 := bbase (se 4 (by rfl) ⟨48267, by rfl⟩ : syracuseStep 514853 = 96535) (by norm_num)
theorem B580405 : Blo 227813 580405 := bbase (se 5 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 580405 = 54413) (by norm_num)
theorem B2087765 : Blo 227813 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B547685 : Blo 227813 547685 := bbase (se 4 (by rfl) ⟨51345, by rfl⟩ : syracuseStep 547685 = 102691) (by norm_num)
theorem B514925 : Blo 227813 514925 := bbase (se 3 (by rfl) ⟨96548, by rfl⟩ : syracuseStep 514925 = 193097) (by norm_num)
theorem B1235861 : Blo 227813 1235861 := bbase (se 6 (by rfl) ⟨28965, by rfl⟩ : syracuseStep 1235861 = 57931) (by norm_num)
theorem B842645 : Blo 227813 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B547741 : Blo 227813 547741 := bbase (se 3 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 547741 = 205403) (by norm_num)
theorem B580517 : Blo 227813 580517 := bbase (se 4 (by rfl) ⟨54423, by rfl⟩ : syracuseStep 580517 = 108847) (by norm_num)
theorem B514997 : Blo 227813 514997 := bbase (se 5 (by rfl) ⟨24140, by rfl⟩ : syracuseStep 514997 = 48281) (by norm_num)
theorem B515069 : Blo 227813 515069 := bbase (se 3 (by rfl) ⟨96575, by rfl⟩ : syracuseStep 515069 = 193151) (by norm_num)
theorem B777221 : Blo 227813 777221 := bbase (se 4 (by rfl) ⟨72864, by rfl⟩ : syracuseStep 777221 = 145729) (by norm_num)
theorem B351253 : Blo 227813 351253 := bbase (se 6 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 351253 = 16465) (by norm_num)
theorem B515141 : Blo 227813 515141 := bbase (se 4 (by rfl) ⟨48294, by rfl⟩ : syracuseStep 515141 = 96589) (by norm_num)
theorem B580709 : Blo 227813 580709 := bbase (se 4 (by rfl) ⟨54441, by rfl⟩ : syracuseStep 580709 = 108883) (by norm_num)
theorem B1039493 : Blo 227813 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B515213 : Blo 227813 515213 := bbase (se 3 (by rfl) ⟨96602, by rfl⟩ : syracuseStep 515213 = 193205) (by norm_num)
theorem B515285 : Blo 227813 515285 := bbase (se 7 (by rfl) ⟨6038, by rfl⟩ : syracuseStep 515285 = 12077) (by norm_num)
theorem B515357 : Blo 227813 515357 := bbase (se 3 (by rfl) ⟨96629, by rfl⟩ : syracuseStep 515357 = 193259) (by norm_num)
theorem B1170773 : Blo 227813 1170773 := bbase (se 11 (by rfl) ⟨857, by rfl⟩ : syracuseStep 1170773 = 1715) (by norm_num)
theorem B515429 : Blo 227813 515429 := bbase (se 4 (by rfl) ⟨48321, by rfl⟩ : syracuseStep 515429 = 96643) (by norm_num)
theorem B875893 : Blo 227813 875893 := bbase (se 5 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 875893 = 82115) (by norm_num)
theorem B515501 : Blo 227813 515501 := bbase (se 3 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 515501 = 193313) (by norm_num)
theorem B777653 : Blo 227813 777653 := bbase (se 5 (by rfl) ⟨36452, by rfl⟩ : syracuseStep 777653 = 72905) (by norm_num)
theorem B581053 : Blo 227813 581053 := bbase (se 3 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 581053 = 217895) (by norm_num)
theorem B384493 : Blo 227813 384493 := bbase (se 3 (by rfl) ⟨72092, by rfl⟩ : syracuseStep 384493 = 144185) (by norm_num)
theorem B515573 : Blo 227813 515573 := bbase (se 5 (by rfl) ⟨24167, by rfl⟩ : syracuseStep 515573 = 48335) (by norm_num)
theorem B3923477 : Blo 227813 3923477 := bbase (se 6 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 3923477 = 183913) (by norm_num)
theorem B581165 : Blo 227813 581165 := bbase (se 3 (by rfl) ⟨108968, by rfl⟩ : syracuseStep 581165 = 217937) (by norm_num)
theorem B515645 : Blo 227813 515645 := bbase (se 3 (by rfl) ⟨96683, by rfl⟩ : syracuseStep 515645 = 193367) (by norm_num)
theorem B384581 : Blo 227813 384581 := bbase (se 4 (by rfl) ⟨36054, by rfl⟩ : syracuseStep 384581 = 72109) (by norm_num)
theorem B515717 : Blo 227813 515717 := bbase (se 4 (by rfl) ⟨48348, by rfl⟩ : syracuseStep 515717 = 96697) (by norm_num)
theorem B876197 : Blo 227813 876197 := bbase (se 4 (by rfl) ⟨82143, by rfl⟩ : syracuseStep 876197 = 164287) (by norm_num)
theorem B2088629 : Blo 227813 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B384709 : Blo 227813 384709 := bbase (se 4 (by rfl) ⟨36066, by rfl⟩ : syracuseStep 384709 = 72133) (by norm_num)
theorem B515789 : Blo 227813 515789 := bbase (se 3 (by rfl) ⟨96710, by rfl⟩ : syracuseStep 515789 = 193421) (by norm_num)
theorem B581357 : Blo 227813 581357 := bbase (se 3 (by rfl) ⟨109004, by rfl⟩ : syracuseStep 581357 = 218009) (by norm_num)
theorem B515861 : Blo 227813 515861 := bbase (se 6 (by rfl) ⟨12090, by rfl⟩ : syracuseStep 515861 = 24181) (by norm_num)
theorem B384797 : Blo 227813 384797 := bbase (se 3 (by rfl) ⟨72149, by rfl⟩ : syracuseStep 384797 = 144299) (by norm_num)
theorem B515933 : Blo 227813 515933 := bbase (se 3 (by rfl) ⟨96737, by rfl⟩ : syracuseStep 515933 = 193475) (by norm_num)
theorem B778085 : Blo 227813 778085 := bbase (se 4 (by rfl) ⟨72945, by rfl⟩ : syracuseStep 778085 = 145891) (by norm_num)
theorem B548741 : Blo 227813 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B384925 : Blo 227813 384925 := bbase (se 3 (by rfl) ⟨72173, by rfl⟩ : syracuseStep 384925 = 144347) (by norm_num)
theorem B516005 : Blo 227813 516005 := bbase (se 4 (by rfl) ⟨48375, by rfl⟩ : syracuseStep 516005 = 96751) (by norm_num)
theorem B516077 : Blo 227813 516077 := bbase (se 3 (by rfl) ⟨96764, by rfl⟩ : syracuseStep 516077 = 193529) (by norm_num)
theorem B385013 : Blo 227813 385013 := bbase (se 5 (by rfl) ⟨18047, by rfl⟩ : syracuseStep 385013 = 36095) (by norm_num)
theorem B516149 : Blo 227813 516149 := bbase (se 5 (by rfl) ⟨24194, by rfl⟩ : syracuseStep 516149 = 48389) (by norm_num)
theorem B581701 : Blo 227813 581701 := bbase (se 4 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 581701 = 109069) (by norm_num)
theorem B385141 : Blo 227813 385141 := bbase (se 5 (by rfl) ⟨18053, by rfl⟩ : syracuseStep 385141 = 36107) (by norm_num)
theorem B516221 : Blo 227813 516221 := bbase (se 3 (by rfl) ⟨96791, by rfl⟩ : syracuseStep 516221 = 193583) (by norm_num)
theorem B352421 : Blo 227813 352421 := bbase (se 4 (by rfl) ⟨33039, by rfl⟩ : syracuseStep 352421 = 66079) (by norm_num)
theorem B581813 : Blo 227813 581813 := bbase (se 5 (by rfl) ⟨27272, by rfl⟩ : syracuseStep 581813 = 54545) (by norm_num)
theorem B516293 : Blo 227813 516293 := bbase (se 4 (by rfl) ⟨48402, by rfl⟩ : syracuseStep 516293 = 96805) (by norm_num)
theorem B385229 : Blo 227813 385229 := bbase (se 3 (by rfl) ⟨72230, by rfl⟩ : syracuseStep 385229 = 144461) (by norm_num)
theorem B516365 : Blo 227813 516365 := bbase (se 3 (by rfl) ⟨96818, by rfl⟩ : syracuseStep 516365 = 193637) (by norm_num)
theorem B778517 : Blo 227813 778517 := bbase (se 6 (by rfl) ⟨18246, by rfl⟩ : syracuseStep 778517 = 36493) (by norm_num)
theorem B385357 : Blo 227813 385357 := bbase (se 3 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 385357 = 144509) (by norm_num)
theorem B516437 : Blo 227813 516437 := bbase (se 10 (by rfl) ⟨756, by rfl⟩ : syracuseStep 516437 = 1513) (by norm_num)
theorem B582005 : Blo 227813 582005 := bbase (se 5 (by rfl) ⟨27281, by rfl⟩ : syracuseStep 582005 = 54563) (by norm_num)
theorem B516509 : Blo 227813 516509 := bbase (se 3 (by rfl) ⟨96845, by rfl⟩ : syracuseStep 516509 = 193691) (by norm_num)
theorem B385445 : Blo 227813 385445 := bbase (se 4 (by rfl) ⟨36135, by rfl⟩ : syracuseStep 385445 = 72271) (by norm_num)
theorem B516581 : Blo 227813 516581 := bbase (se 4 (by rfl) ⟨48429, by rfl⟩ : syracuseStep 516581 = 96859) (by norm_num)
theorem B385573 : Blo 227813 385573 := bbase (se 4 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 385573 = 72295) (by norm_num)
theorem B516653 : Blo 227813 516653 := bbase (se 3 (by rfl) ⟨96872, by rfl⟩ : syracuseStep 516653 = 193745) (by norm_num)
theorem B1172069 : Blo 227813 1172069 := bbase (se 4 (by rfl) ⟨109881, by rfl⟩ : syracuseStep 1172069 = 219763) (by norm_num)
theorem B516725 : Blo 227813 516725 := bbase (se 5 (by rfl) ⟨24221, by rfl⟩ : syracuseStep 516725 = 48443) (by norm_num)
theorem B385661 : Blo 227813 385661 := bbase (se 3 (by rfl) ⟨72311, by rfl⟩ : syracuseStep 385661 = 144623) (by norm_num)
theorem B516797 : Blo 227813 516797 := bbase (se 3 (by rfl) ⟨96899, by rfl⟩ : syracuseStep 516797 = 193799) (by norm_num)
theorem B778949 : Blo 227813 778949 := bbase (se 4 (by rfl) ⟨73026, by rfl⟩ : syracuseStep 778949 = 146053) (by norm_num)
theorem B582349 : Blo 227813 582349 := bbase (se 3 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 582349 = 218381) (by norm_num)
theorem B385789 : Blo 227813 385789 := bbase (se 3 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 385789 = 144671) (by norm_num)
theorem B516869 : Blo 227813 516869 := bbase (se 4 (by rfl) ⟨48456, by rfl⟩ : syracuseStep 516869 = 96913) (by norm_num)
theorem B582461 : Blo 227813 582461 := bbase (se 3 (by rfl) ⟨109211, by rfl⟩ : syracuseStep 582461 = 218423) (by norm_num)
theorem B516941 : Blo 227813 516941 := bbase (se 3 (by rfl) ⟨96926, by rfl⟩ : syracuseStep 516941 = 193853) (by norm_num)
theorem B385877 : Blo 227813 385877 := bbase (se 9 (by rfl) ⟨1130, by rfl⟩ : syracuseStep 385877 = 2261) (by norm_num)
theorem B517013 : Blo 227813 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B975797 : Blo 227813 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B386005 : Blo 227813 386005 := bbase (se 7 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 386005 = 9047) (by norm_num)
theorem B517085 : Blo 227813 517085 := bbase (se 3 (by rfl) ⟨96953, by rfl⟩ : syracuseStep 517085 = 193907) (by norm_num)
theorem B582653 : Blo 227813 582653 := bbase (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) (by norm_num)
theorem B517157 : Blo 227813 517157 := bbase (se 4 (by rfl) ⟨48483, by rfl⟩ : syracuseStep 517157 = 96967) (by norm_num)
theorem B386093 : Blo 227813 386093 := bbase (se 3 (by rfl) ⟨72392, by rfl⟩ : syracuseStep 386093 = 144785) (by norm_num)
theorem B517229 : Blo 227813 517229 := bbase (se 3 (by rfl) ⟨96980, by rfl⟩ : syracuseStep 517229 = 193961) (by norm_num)
theorem B779381 : Blo 227813 779381 := bbase (se 5 (by rfl) ⟨36533, by rfl⟩ : syracuseStep 779381 = 73067) (by norm_num)
theorem B386221 : Blo 227813 386221 := bbase (se 3 (by rfl) ⟨72416, by rfl⟩ : syracuseStep 386221 = 144833) (by norm_num)
theorem B517301 : Blo 227813 517301 := bbase (se 5 (by rfl) ⟨24248, by rfl⟩ : syracuseStep 517301 = 48497) (by norm_num)
theorem B517373 : Blo 227813 517373 := bbase (se 3 (by rfl) ⟨97007, by rfl⟩ : syracuseStep 517373 = 194015) (by norm_num)
theorem B386309 : Blo 227813 386309 := bbase (se 4 (by rfl) ⟨36216, by rfl⟩ : syracuseStep 386309 = 72433) (by norm_num)
theorem B517445 : Blo 227813 517445 := bbase (se 4 (by rfl) ⟨48510, by rfl⟩ : syracuseStep 517445 = 97021) (by norm_num)
theorem B582997 : Blo 227813 582997 := bbase (se 12 (by rfl) ⟨213, by rfl⟩ : syracuseStep 582997 = 427) (by norm_num)
theorem B386437 : Blo 227813 386437 := bbase (se 4 (by rfl) ⟨36228, by rfl⟩ : syracuseStep 386437 = 72457) (by norm_num)
theorem B517517 : Blo 227813 517517 := bbase (se 3 (by rfl) ⟨97034, by rfl⟩ : syracuseStep 517517 = 194069) (by norm_num)
theorem B583109 : Blo 227813 583109 := bbase (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) (by norm_num)
theorem B517589 : Blo 227813 517589 := bbase (se 7 (by rfl) ⟨6065, by rfl⟩ : syracuseStep 517589 = 12131) (by norm_num)
theorem B386525 : Blo 227813 386525 := bbase (se 3 (by rfl) ⟨72473, by rfl⟩ : syracuseStep 386525 = 144947) (by norm_num)
theorem B517661 : Blo 227813 517661 := bbase (se 3 (by rfl) ⟨97061, by rfl⟩ : syracuseStep 517661 = 194123) (by norm_num)
theorem B779813 : Blo 227813 779813 := bbase (se 4 (by rfl) ⟨73107, by rfl⟩ : syracuseStep 779813 = 146215) (by norm_num)
theorem B386653 : Blo 227813 386653 := bbase (se 3 (by rfl) ⟨72497, by rfl⟩ : syracuseStep 386653 = 144995) (by norm_num)
theorem B517733 : Blo 227813 517733 := bbase (se 4 (by rfl) ⟨48537, by rfl⟩ : syracuseStep 517733 = 97075) (by norm_num)
theorem B583301 : Blo 227813 583301 := bbase (se 4 (by rfl) ⟨54684, by rfl⟩ : syracuseStep 583301 = 109369) (by norm_num)
theorem B517805 : Blo 227813 517805 := bbase (se 3 (by rfl) ⟨97088, by rfl⟩ : syracuseStep 517805 = 194177) (by norm_num)
theorem B386741 : Blo 227813 386741 := bbase (se 5 (by rfl) ⟨18128, by rfl⟩ : syracuseStep 386741 = 36257) (by norm_num)
theorem B648901 : Blo 227813 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B288461 : Blo 227813 288461 := bbase (se 3 (by rfl) ⟨54086, by rfl⟩ : syracuseStep 288461 = 108173) (by norm_num)
theorem B779989 : Blo 227813 779989 := bbase (se 7 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 779989 = 18281) (by norm_num)
theorem B878309 : Blo 227813 878309 := bbase (se 4 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 878309 = 164683) (by norm_num)
theorem B517877 : Blo 227813 517877 := bbase (se 5 (by rfl) ⟨24275, by rfl⟩ : syracuseStep 517877 = 48551) (by norm_num)
theorem B288517 : Blo 227813 288517 := bbase (se 4 (by rfl) ⟨27048, by rfl⟩ : syracuseStep 288517 = 54097) (by norm_num)
theorem B386869 : Blo 227813 386869 := bbase (se 5 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 386869 = 36269) (by norm_num)
theorem B288569 : Blo 227813 288569 := bbase (se 2 (by rfl) ⟨108213, by rfl⟩ : syracuseStep 288569 = 216427) (by norm_num)
theorem B517949 : Blo 227813 517949 := bbase (se 3 (by rfl) ⟨97115, by rfl⟩ : syracuseStep 517949 = 194231) (by norm_num)
theorem B288613 : Blo 227813 288613 := bbase (se 4 (by rfl) ⟨27057, by rfl⟩ : syracuseStep 288613 = 54115) (by norm_num)
theorem B1173365 : Blo 227813 1173365 := bbase (se 5 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 1173365 = 110003) (by norm_num)
theorem B518021 : Blo 227813 518021 := bbase (se 4 (by rfl) ⟨48564, by rfl⟩ : syracuseStep 518021 = 97129) (by norm_num)
theorem B386957 : Blo 227813 386957 := bbase (se 3 (by rfl) ⟨72554, by rfl⟩ : syracuseStep 386957 = 145109) (by norm_num)
theorem B976805 : Blo 227813 976805 := bbase (se 4 (by rfl) ⟨91575, by rfl⟩ : syracuseStep 976805 = 183151) (by norm_num)
theorem B518093 : Blo 227813 518093 := bbase (se 3 (by rfl) ⟨97142, by rfl⟩ : syracuseStep 518093 = 194285) (by norm_num)
theorem B780245 : Blo 227813 780245 := bbase (se 7 (by rfl) ⟨9143, by rfl⟩ : syracuseStep 780245 = 18287) (by norm_num)
theorem B583645 : Blo 227813 583645 := bbase (se 3 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 583645 = 218867) (by norm_num)
theorem B878597 : Blo 227813 878597 := bbase (se 4 (by rfl) ⟨82368, by rfl⟩ : syracuseStep 878597 = 164737) (by norm_num)
theorem B387085 : Blo 227813 387085 := bbase (se 3 (by rfl) ⟨72578, by rfl⟩ : syracuseStep 387085 = 145157) (by norm_num)
theorem B288785 : Blo 227813 288785 := bbase (se 2 (by rfl) ⟨108294, by rfl⟩ : syracuseStep 288785 = 216589) (by norm_num)
theorem B518165 : Blo 227813 518165 := bbase (se 6 (by rfl) ⟨12144, by rfl⟩ : syracuseStep 518165 = 24289) (by norm_num)
theorem B288841 : Blo 227813 288841 := bbase (se 2 (by rfl) ⟨108315, by rfl⟩ : syracuseStep 288841 = 216631) (by norm_num)
theorem B583757 : Blo 227813 583757 := bbase (se 3 (by rfl) ⟨109454, by rfl⟩ : syracuseStep 583757 = 218909) (by norm_num)
theorem B1730645 : Blo 227813 1730645 := bbase (se 8 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 1730645 = 20281) (by norm_num)
theorem B518237 : Blo 227813 518237 := bbase (se 3 (by rfl) ⟨97169, by rfl⟩ : syracuseStep 518237 = 194339) (by norm_num)
theorem B387173 : Blo 227813 387173 := bbase (se 4 (by rfl) ⟨36297, by rfl⟩ : syracuseStep 387173 = 72595) (by norm_num)
theorem B2648213 : Blo 227813 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B518309 : Blo 227813 518309 := bbase (se 4 (by rfl) ⟨48591, by rfl⟩ : syracuseStep 518309 = 97183) (by norm_num)
theorem B288937 : Blo 227813 288937 := bbase (se 2 (by rfl) ⟨108351, by rfl⟩ : syracuseStep 288937 = 216703) (by norm_num)
theorem B551117 : Blo 227813 551117 := bbase (se 3 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 551117 = 206669) (by norm_num)
theorem B387301 : Blo 227813 387301 := bbase (se 4 (by rfl) ⟨36309, by rfl⟩ : syracuseStep 387301 = 72619) (by norm_num)
theorem B518381 : Blo 227813 518381 := bbase (se 3 (by rfl) ⟨97196, by rfl⟩ : syracuseStep 518381 = 194393) (by norm_num)
theorem B583949 : Blo 227813 583949 := bbase (se 3 (by rfl) ⟨109490, by rfl⟩ : syracuseStep 583949 = 218981) (by norm_num)
theorem B256297 : Blo 227813 256297 := bbase (se 2 (by rfl) ⟨96111, by rfl⟩ : syracuseStep 256297 = 192223) (by norm_num)
theorem B518453 : Blo 227813 518453 := bbase (se 5 (by rfl) ⟨24302, by rfl⟩ : syracuseStep 518453 = 48605) (by norm_num)
theorem B387389 : Blo 227813 387389 := bbase (se 3 (by rfl) ⟨72635, by rfl⟩ : syracuseStep 387389 = 145271) (by norm_num)
theorem B256333 : Blo 227813 256333 := bbase (se 3 (by rfl) ⟨48062, by rfl⟩ : syracuseStep 256333 = 96125) (by norm_num)
theorem B289109 : Blo 227813 289109 := bbase (se 10 (by rfl) ⟨423, by rfl⟩ : syracuseStep 289109 = 847) (by norm_num)
theorem B256369 : Blo 227813 256369 := bbase (se 2 (by rfl) ⟨96138, by rfl⟩ : syracuseStep 256369 = 192277) (by norm_num)
theorem B518525 : Blo 227813 518525 := bbase (se 3 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 518525 = 194447) (by norm_num)
theorem B616837 : Blo 227813 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B780677 : Blo 227813 780677 := bbase (se 4 (by rfl) ⟨73188, by rfl⟩ : syracuseStep 780677 = 146377) (by norm_num)
theorem B289165 : Blo 227813 289165 := bbase (se 3 (by rfl) ⟨54218, by rfl⟩ : syracuseStep 289165 = 108437) (by norm_num)
theorem B256405 : Blo 227813 256405 := bbase (se 6 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 256405 = 12019) (by norm_num)
theorem B1173941 : Blo 227813 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B256441 : Blo 227813 256441 := bbase (se 2 (by rfl) ⟨96165, by rfl⟩ : syracuseStep 256441 = 192331) (by norm_num)
theorem B387517 : Blo 227813 387517 := bbase (se 3 (by rfl) ⟨72659, by rfl⟩ : syracuseStep 387517 = 145319) (by norm_num)
theorem B616901 : Blo 227813 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B518597 : Blo 227813 518597 := bbase (se 4 (by rfl) ⟨48618, by rfl⟩ : syracuseStep 518597 = 97237) (by norm_num)
theorem B256477 : Blo 227813 256477 := bbase (se 3 (by rfl) ⟨48089, by rfl⟩ : syracuseStep 256477 = 96179) (by norm_num)
theorem B289261 : Blo 227813 289261 := bbase (se 3 (by rfl) ⟨54236, by rfl⟩ : syracuseStep 289261 = 108473) (by norm_num)
theorem B256513 : Blo 227813 256513 := bbase (se 2 (by rfl) ⟨96192, by rfl⟩ : syracuseStep 256513 = 192385) (by norm_num)
theorem B518669 : Blo 227813 518669 := bbase (se 3 (by rfl) ⟨97250, by rfl⟩ : syracuseStep 518669 = 194501) (by norm_num)
theorem B387605 : Blo 227813 387605 := bbase (se 6 (by rfl) ⟨9084, by rfl⟩ : syracuseStep 387605 = 18169) (by norm_num)
theorem B256549 : Blo 227813 256549 := bbase (se 4 (by rfl) ⟨24051, by rfl⟩ : syracuseStep 256549 = 48103) (by norm_num)
theorem B256585 : Blo 227813 256585 := bbase (se 2 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 256585 = 192439) (by norm_num)
theorem B551501 : Blo 227813 551501 := bbase (se 3 (by rfl) ⟨103406, by rfl⟩ : syracuseStep 551501 = 206813) (by norm_num)
theorem B518741 : Blo 227813 518741 := bbase (se 8 (by rfl) ⟨3039, by rfl⟩ : syracuseStep 518741 = 6079) (by norm_num)
theorem B584293 : Blo 227813 584293 := bbase (se 4 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 584293 = 109555) (by norm_num)
theorem B256621 : Blo 227813 256621 := bbase (se 3 (by rfl) ⟨48116, by rfl⟩ : syracuseStep 256621 = 96233) (by norm_num)
theorem B256657 : Blo 227813 256657 := bbase (se 2 (by rfl) ⟨96246, by rfl⟩ : syracuseStep 256657 = 192493) (by norm_num)
theorem B387733 : Blo 227813 387733 := bbase (se 6 (by rfl) ⟨9087, by rfl⟩ : syracuseStep 387733 = 18175) (by norm_num)
theorem B289433 : Blo 227813 289433 := bbase (se 2 (by rfl) ⟨108537, by rfl⟩ : syracuseStep 289433 = 217075) (by norm_num)
theorem B518813 : Blo 227813 518813 := bbase (se 3 (by rfl) ⟨97277, by rfl⟩ : syracuseStep 518813 = 194555) (by norm_num)
theorem B256693 : Blo 227813 256693 := bbase (se 5 (by rfl) ⟨12032, by rfl⟩ : syracuseStep 256693 = 24065) (by norm_num)
theorem B289489 : Blo 227813 289489 := bbase (se 2 (by rfl) ⟨108558, by rfl⟩ : syracuseStep 289489 = 217117) (by norm_num)
theorem B584405 : Blo 227813 584405 := bbase (se 7 (by rfl) ⟨6848, by rfl⟩ : syracuseStep 584405 = 13697) (by norm_num)
theorem B256729 : Blo 227813 256729 := bbase (se 2 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 256729 = 192547) (by norm_num)
theorem B518885 : Blo 227813 518885 := bbase (se 4 (by rfl) ⟨48645, by rfl⟩ : syracuseStep 518885 = 97291) (by norm_num)
theorem B387821 : Blo 227813 387821 := bbase (se 3 (by rfl) ⟨72716, by rfl⟩ : syracuseStep 387821 = 145433) (by norm_num)
theorem B879349 : Blo 227813 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B256765 : Blo 227813 256765 := bbase (se 3 (by rfl) ⟨48143, by rfl⟩ : syracuseStep 256765 = 96287) (by norm_num)
theorem B551701 : Blo 227813 551701 := bbase (se 6 (by rfl) ⟨12930, by rfl⟩ : syracuseStep 551701 = 25861) (by norm_num)
theorem B256801 : Blo 227813 256801 := bbase (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) (by norm_num)
theorem B518957 : Blo 227813 518957 := bbase (se 3 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 518957 = 194609) (by norm_num)
theorem B289585 : Blo 227813 289585 := bbase (se 2 (by rfl) ⟨108594, by rfl⟩ : syracuseStep 289585 = 217189) (by norm_num)
theorem B781109 : Blo 227813 781109 := bbase (se 5 (by rfl) ⟨36614, by rfl⟩ : syracuseStep 781109 = 73229) (by norm_num)
theorem B256837 : Blo 227813 256837 := bbase (se 4 (by rfl) ⟨24078, by rfl⟩ : syracuseStep 256837 = 48157) (by norm_num)
theorem B256873 : Blo 227813 256873 := bbase (se 2 (by rfl) ⟨96327, by rfl⟩ : syracuseStep 256873 = 192655) (by norm_num)
theorem B387949 : Blo 227813 387949 := bbase (se 3 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 387949 = 145481) (by norm_num)
theorem B519029 : Blo 227813 519029 := bbase (se 5 (by rfl) ⟨24329, by rfl⟩ : syracuseStep 519029 = 48659) (by norm_num)
theorem B256909 : Blo 227813 256909 := bbase (se 3 (by rfl) ⟨48170, by rfl⟩ : syracuseStep 256909 = 96341) (by norm_num)
theorem B584597 : Blo 227813 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B256945 : Blo 227813 256945 := bbase (se 2 (by rfl) ⟨96354, by rfl⟩ : syracuseStep 256945 = 192709) (by norm_num)
theorem B519101 : Blo 227813 519101 := bbase (se 3 (by rfl) ⟨97331, by rfl⟩ : syracuseStep 519101 = 194663) (by norm_num)
theorem B388037 : Blo 227813 388037 := bbase (se 4 (by rfl) ⟨36378, by rfl⟩ : syracuseStep 388037 = 72757) (by norm_num)
theorem B256981 : Blo 227813 256981 := bbase (se 7 (by rfl) ⟨3011, by rfl⟩ : syracuseStep 256981 = 6023) (by norm_num)
theorem B289757 : Blo 227813 289757 := bbase (se 3 (by rfl) ⟨54329, by rfl⟩ : syracuseStep 289757 = 108659) (by norm_num)
theorem B257017 : Blo 227813 257017 := bbase (se 2 (by rfl) ⟨96381, by rfl⟩ : syracuseStep 257017 = 192763) (by norm_num)
theorem B519173 : Blo 227813 519173 := bbase (se 4 (by rfl) ⟨48672, by rfl⟩ : syracuseStep 519173 = 97345) (by norm_num)
theorem B289813 : Blo 227813 289813 := bbase (se 6 (by rfl) ⟨6792, by rfl⟩ : syracuseStep 289813 = 13585) (by norm_num)
theorem B257053 : Blo 227813 257053 := bbase (se 3 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 257053 = 96395) (by norm_num)
theorem B257089 : Blo 227813 257089 := bbase (se 2 (by rfl) ⟨96408, by rfl⟩ : syracuseStep 257089 = 192817) (by norm_num)
theorem B388165 : Blo 227813 388165 := bbase (se 4 (by rfl) ⟨36390, by rfl⟩ : syracuseStep 388165 = 72781) (by norm_num)
theorem B519245 : Blo 227813 519245 := bbase (se 3 (by rfl) ⟨97358, by rfl⟩ : syracuseStep 519245 = 194717) (by norm_num)
theorem B257125 : Blo 227813 257125 := bbase (se 4 (by rfl) ⟨24105, by rfl⟩ : syracuseStep 257125 = 48211) (by norm_num)
theorem B289909 : Blo 227813 289909 := bbase (se 5 (by rfl) ⟨13589, by rfl⟩ : syracuseStep 289909 = 27179) (by norm_num)
theorem B257161 : Blo 227813 257161 := bbase (se 2 (by rfl) ⟨96435, by rfl⟩ : syracuseStep 257161 = 192871) (by norm_num)
theorem B519317 : Blo 227813 519317 := bbase (se 6 (by rfl) ⟨12171, by rfl⟩ : syracuseStep 519317 = 24343) (by norm_num)
theorem B486557 : Blo 227813 486557 := bbase (se 3 (by rfl) ⟨91229, by rfl⟩ : syracuseStep 486557 = 182459) (by norm_num)
theorem B388253 : Blo 227813 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B650405 : Blo 227813 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B879781 : Blo 227813 879781 := bbase (se 4 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 879781 = 164959) (by norm_num)
theorem B257197 : Blo 227813 257197 := bbase (se 3 (by rfl) ⟨48224, by rfl⟩ : syracuseStep 257197 = 96449) (by norm_num)
theorem B257233 : Blo 227813 257233 := bbase (se 2 (by rfl) ⟨96462, by rfl⟩ : syracuseStep 257233 = 192925) (by norm_num)
theorem B519389 : Blo 227813 519389 := bbase (se 3 (by rfl) ⟨97385, by rfl⟩ : syracuseStep 519389 = 194771) (by norm_num)
theorem B781541 : Blo 227813 781541 := bbase (se 4 (by rfl) ⟨73269, by rfl⟩ : syracuseStep 781541 = 146539) (by norm_num)
theorem B584941 : Blo 227813 584941 := bbase (se 3 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 584941 = 219353) (by norm_num)
theorem B257269 : Blo 227813 257269 := bbase (se 5 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 257269 = 24119) (by norm_num)
theorem B781589 : Blo 227813 781589 := bbase (se 6 (by rfl) ⟨18318, by rfl⟩ : syracuseStep 781589 = 36637) (by norm_num)
theorem B257305 : Blo 227813 257305 := bbase (se 2 (by rfl) ⟨96489, by rfl⟩ : syracuseStep 257305 = 192979) (by norm_num)
theorem B388381 : Blo 227813 388381 := bbase (se 3 (by rfl) ⟨72821, by rfl⟩ : syracuseStep 388381 = 145643) (by norm_num)
theorem B290081 : Blo 227813 290081 := bbase (se 2 (by rfl) ⟨108780, by rfl⟩ : syracuseStep 290081 = 217561) (by norm_num)
theorem B519461 : Blo 227813 519461 := bbase (se 4 (by rfl) ⟨48699, by rfl⟩ : syracuseStep 519461 = 97399) (by norm_num)
theorem B257341 : Blo 227813 257341 := bbase (se 3 (by rfl) ⟨48251, by rfl⟩ : syracuseStep 257341 = 96503) (by norm_num)
theorem B290137 : Blo 227813 290137 := bbase (se 2 (by rfl) ⟨108801, by rfl⟩ : syracuseStep 290137 = 217603) (by norm_num)
theorem B585053 : Blo 227813 585053 := bbase (se 3 (by rfl) ⟨109697, by rfl⟩ : syracuseStep 585053 = 219395) (by norm_num)
theorem B257377 : Blo 227813 257377 := bbase (se 2 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 257377 = 193033) (by norm_num)
theorem B519533 : Blo 227813 519533 := bbase (se 3 (by rfl) ⟨97412, by rfl⟩ : syracuseStep 519533 = 194825) (by norm_num)
theorem B388469 : Blo 227813 388469 := bbase (se 5 (by rfl) ⟨18209, by rfl⟩ : syracuseStep 388469 = 36419) (by norm_num)
theorem B257413 : Blo 227813 257413 := bbase (se 4 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 257413 = 48265) (by norm_num)
theorem B486805 : Blo 227813 486805 := bbase (se 6 (by rfl) ⟨11409, by rfl⟩ : syracuseStep 486805 = 22819) (by norm_num)
theorem B257449 : Blo 227813 257449 := bbase (se 2 (by rfl) ⟨96543, by rfl⟩ : syracuseStep 257449 = 193087) (by norm_num)
theorem B519605 : Blo 227813 519605 := bbase (se 5 (by rfl) ⟨24356, by rfl⟩ : syracuseStep 519605 = 48713) (by norm_num)
theorem B290233 : Blo 227813 290233 := bbase (se 2 (by rfl) ⟨108837, by rfl⟩ : syracuseStep 290233 = 217675) (by norm_num)
theorem B945605 : Blo 227813 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B257485 : Blo 227813 257485 := bbase (se 3 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 257485 = 96557) (by norm_num)
theorem B880085 : Blo 227813 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B1109477 : Blo 227813 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B257521 : Blo 227813 257521 := bbase (se 2 (by rfl) ⟨96570, by rfl⟩ : syracuseStep 257521 = 193141) (by norm_num)
theorem B388597 : Blo 227813 388597 := bbase (se 5 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 388597 = 36431) (by norm_num)
theorem B421373 : Blo 227813 421373 := bbase (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) (by norm_num)
theorem B519677 : Blo 227813 519677 := bbase (se 3 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 519677 = 194879) (by norm_num)
theorem B257557 : Blo 227813 257557 := bbase (se 6 (by rfl) ⟨6036, by rfl⟩ : syracuseStep 257557 = 12073) (by norm_num)
theorem B585245 : Blo 227813 585245 := bbase (se 3 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 585245 = 219467) (by norm_num)
theorem B257593 : Blo 227813 257593 := bbase (se 2 (by rfl) ⟨96597, by rfl⟩ : syracuseStep 257593 = 193195) (by norm_num)
theorem B519749 : Blo 227813 519749 := bbase (se 4 (by rfl) ⟨48726, by rfl⟩ : syracuseStep 519749 = 97453) (by norm_num)
theorem B388685 : Blo 227813 388685 := bbase (se 3 (by rfl) ⟨72878, by rfl⟩ : syracuseStep 388685 = 145757) (by norm_num)
theorem B257629 : Blo 227813 257629 := bbase (se 3 (by rfl) ⟨48305, by rfl⟩ : syracuseStep 257629 = 96611) (by norm_num)
theorem B290405 : Blo 227813 290405 := bbase (se 4 (by rfl) ⟨27225, by rfl⟩ : syracuseStep 290405 = 54451) (by norm_num)
theorem B257665 : Blo 227813 257665 := bbase (se 2 (by rfl) ⟨96624, by rfl⟩ : syracuseStep 257665 = 193249) (by norm_num)
theorem B519821 : Blo 227813 519821 := bbase (se 3 (by rfl) ⟨97466, by rfl⟩ : syracuseStep 519821 = 194933) (by norm_num)
theorem B978581 : Blo 227813 978581 := bbase (se 6 (by rfl) ⟨22935, by rfl⟩ : syracuseStep 978581 = 45871) (by norm_num)
theorem B781973 : Blo 227813 781973 := bbase (se 6 (by rfl) ⟨18327, by rfl⟩ : syracuseStep 781973 = 36655) (by norm_num)
theorem B290461 : Blo 227813 290461 := bbase (se 3 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 290461 = 108923) (by norm_num)
theorem B257701 : Blo 227813 257701 := bbase (se 4 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 257701 = 48319) (by norm_num)
theorem B585413 : Blo 227813 585413 := bbase (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) (by norm_num)
theorem B257737 : Blo 227813 257737 := bbase (se 2 (by rfl) ⟨96651, by rfl⟩ : syracuseStep 257737 = 193303) (by norm_num)
theorem B388813 : Blo 227813 388813 := bbase (se 3 (by rfl) ⟨72902, by rfl⟩ : syracuseStep 388813 = 145805) (by norm_num)
theorem B519893 : Blo 227813 519893 := bbase (se 7 (by rfl) ⟨6092, by rfl⟩ : syracuseStep 519893 = 12185) (by norm_num)
theorem B257773 : Blo 227813 257773 := bbase (se 3 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 257773 = 96665) (by norm_num)
theorem B290557 : Blo 227813 290557 := bbase (se 3 (by rfl) ⟨54479, by rfl⟩ : syracuseStep 290557 = 108959) (by norm_num)
theorem B257809 : Blo 227813 257809 := bbase (se 2 (by rfl) ⟨96678, by rfl⟩ : syracuseStep 257809 = 193357) (by norm_num)
theorem B2617109 : Blo 227813 2617109 := bbase (se 6 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 2617109 = 122677) (by norm_num)
theorem B519965 : Blo 227813 519965 := bbase (se 3 (by rfl) ⟨97493, by rfl⟩ : syracuseStep 519965 = 194987) (by norm_num)
theorem B388901 : Blo 227813 388901 := bbase (se 4 (by rfl) ⟨36459, by rfl⟩ : syracuseStep 388901 = 72919) (by norm_num)
theorem B257845 : Blo 227813 257845 := bbase (se 5 (by rfl) ⟨12086, by rfl⟩ : syracuseStep 257845 = 24173) (by norm_num)
theorem B257881 : Blo 227813 257881 := bbase (se 2 (by rfl) ⟨96705, by rfl⟩ : syracuseStep 257881 = 193411) (by norm_num)
theorem B520037 : Blo 227813 520037 := bbase (se 4 (by rfl) ⟨48753, by rfl⟩ : syracuseStep 520037 = 97507) (by norm_num)
theorem B585589 : Blo 227813 585589 := bbase (se 5 (by rfl) ⟨27449, by rfl⟩ : syracuseStep 585589 = 54899) (by norm_num)
theorem B257917 : Blo 227813 257917 := bbase (se 3 (by rfl) ⟨48359, by rfl⟩ : syracuseStep 257917 = 96719) (by norm_num)
theorem B487309 : Blo 227813 487309 := bbase (se 3 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 487309 = 182741) (by norm_num)
theorem B257953 : Blo 227813 257953 := bbase (se 2 (by rfl) ⟨96732, by rfl⟩ : syracuseStep 257953 = 193465) (by norm_num)
theorem B389029 : Blo 227813 389029 := bbase (se 4 (by rfl) ⟨36471, by rfl⟩ : syracuseStep 389029 = 72943) (by norm_num)
theorem B290729 : Blo 227813 290729 := bbase (se 2 (by rfl) ⟨109023, by rfl⟩ : syracuseStep 290729 = 218047) (by norm_num)
theorem B520109 : Blo 227813 520109 := bbase (se 3 (by rfl) ⟨97520, by rfl⟩ : syracuseStep 520109 = 195041) (by norm_num)
theorem B257989 : Blo 227813 257989 := bbase (se 4 (by rfl) ⟨24186, by rfl⟩ : syracuseStep 257989 = 48373) (by norm_num)
theorem B290785 : Blo 227813 290785 := bbase (se 2 (by rfl) ⟨109044, by rfl⟩ : syracuseStep 290785 = 218089) (by norm_num)
theorem B585701 : Blo 227813 585701 := bbase (se 4 (by rfl) ⟨54909, by rfl⟩ : syracuseStep 585701 = 109819) (by norm_num)
theorem B258025 : Blo 227813 258025 := bbase (se 2 (by rfl) ⟨96759, by rfl⟩ : syracuseStep 258025 = 193519) (by norm_num)
theorem B520181 : Blo 227813 520181 := bbase (se 5 (by rfl) ⟨24383, by rfl⟩ : syracuseStep 520181 = 48767) (by norm_num)
theorem B389117 : Blo 227813 389117 := bbase (se 3 (by rfl) ⟨72959, by rfl⟩ : syracuseStep 389117 = 145919) (by norm_num)
theorem B258061 : Blo 227813 258061 := bbase (se 3 (by rfl) ⟨48386, by rfl⟩ : syracuseStep 258061 = 96773) (by norm_num)
theorem B258097 : Blo 227813 258097 := bbase (se 2 (by rfl) ⟨96786, by rfl⟩ : syracuseStep 258097 = 193573) (by norm_num)
theorem B520253 : Blo 227813 520253 := bbase (se 3 (by rfl) ⟨97547, by rfl⟩ : syracuseStep 520253 = 195095) (by norm_num)
theorem B290881 : Blo 227813 290881 := bbase (se 2 (by rfl) ⟨109080, by rfl⟩ : syracuseStep 290881 = 218161) (by norm_num)
theorem B2093141 : Blo 227813 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B258133 : Blo 227813 258133 := bbase (se 8 (by rfl) ⟨1512, by rfl⟩ : syracuseStep 258133 = 3025) (by norm_num)
theorem B258169 : Blo 227813 258169 := bbase (se 2 (by rfl) ⟨96813, by rfl⟩ : syracuseStep 258169 = 193627) (by norm_num)
theorem B389245 : Blo 227813 389245 := bbase (se 3 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 389245 = 145967) (by norm_num)
theorem B520325 : Blo 227813 520325 := bbase (se 4 (by rfl) ⟨48780, by rfl⟩ : syracuseStep 520325 = 97561) (by norm_num)
theorem B258205 : Blo 227813 258205 := bbase (se 3 (by rfl) ⟨48413, by rfl⟩ : syracuseStep 258205 = 96827) (by norm_num)
theorem B585893 : Blo 227813 585893 := bbase (se 4 (by rfl) ⟨54927, by rfl⟩ : syracuseStep 585893 = 109855) (by norm_num)
theorem B258241 : Blo 227813 258241 := bbase (se 2 (by rfl) ⟨96840, by rfl⟩ : syracuseStep 258241 = 193681) (by norm_num)
theorem B520397 : Blo 227813 520397 := bbase (se 3 (by rfl) ⟨97574, by rfl⟩ : syracuseStep 520397 = 195149) (by norm_num)
theorem B389333 : Blo 227813 389333 := bbase (se 7 (by rfl) ⟨4562, by rfl⟩ : syracuseStep 389333 = 9125) (by norm_num)
theorem B258277 : Blo 227813 258277 := bbase (se 4 (by rfl) ⟨24213, by rfl⟩ : syracuseStep 258277 = 48427) (by norm_num)
theorem B291053 : Blo 227813 291053 := bbase (se 3 (by rfl) ⟨54572, by rfl⟩ : syracuseStep 291053 = 109145) (by norm_num)
theorem B258313 : Blo 227813 258313 := bbase (se 2 (by rfl) ⟨96867, by rfl⟩ : syracuseStep 258313 = 193735) (by norm_num)
theorem B520469 : Blo 227813 520469 := bbase (se 6 (by rfl) ⟨12198, by rfl⟩ : syracuseStep 520469 = 24397) (by norm_num)
theorem B291109 : Blo 227813 291109 := bbase (se 4 (by rfl) ⟨27291, by rfl⟩ : syracuseStep 291109 = 54583) (by norm_num)
theorem B258349 : Blo 227813 258349 := bbase (se 3 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 258349 = 96881) (by norm_num)
theorem B553277 : Blo 227813 553277 := bbase (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) (by norm_num)
theorem B258385 : Blo 227813 258385 := bbase (se 2 (by rfl) ⟨96894, by rfl⟩ : syracuseStep 258385 = 193789) (by norm_num)
theorem B389461 : Blo 227813 389461 := bbase (se 10 (by rfl) ⟨570, by rfl⟩ : syracuseStep 389461 = 1141) (by norm_num)
theorem B520541 : Blo 227813 520541 := bbase (se 3 (by rfl) ⟨97601, by rfl⟩ : syracuseStep 520541 = 195203) (by norm_num)
theorem B258421 : Blo 227813 258421 := bbase (se 5 (by rfl) ⟨12113, by rfl⟩ : syracuseStep 258421 = 24227) (by norm_num)
theorem B291205 : Blo 227813 291205 := bbase (se 4 (by rfl) ⟨27300, by rfl⟩ : syracuseStep 291205 = 54601) (by norm_num)
theorem B258457 : Blo 227813 258457 := bbase (se 2 (by rfl) ⟨96921, by rfl⟩ : syracuseStep 258457 = 193843) (by norm_num)
theorem B422309 : Blo 227813 422309 := bbase (se 4 (by rfl) ⟨39591, by rfl⟩ : syracuseStep 422309 = 79183) (by norm_num)
theorem B520613 : Blo 227813 520613 := bbase (se 4 (by rfl) ⟨48807, by rfl⟩ : syracuseStep 520613 = 97615) (by norm_num)
theorem B389549 : Blo 227813 389549 := bbase (se 3 (by rfl) ⟨73040, by rfl⟩ : syracuseStep 389549 = 146081) (by norm_num)
theorem B258493 : Blo 227813 258493 := bbase (se 3 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 258493 = 96935) (by norm_num)
theorem B258529 : Blo 227813 258529 := bbase (se 2 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 258529 = 193897) (by norm_num)
theorem B520685 : Blo 227813 520685 := bbase (se 3 (by rfl) ⟨97628, by rfl⟩ : syracuseStep 520685 = 195257) (by norm_num)
theorem B586237 : Blo 227813 586237 := bbase (se 3 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 586237 = 219839) (by norm_num)
theorem B258565 : Blo 227813 258565 := bbase (se 4 (by rfl) ⟨24240, by rfl⟩ : syracuseStep 258565 = 48481) (by norm_num)
theorem B258601 : Blo 227813 258601 := bbase (se 2 (by rfl) ⟨96975, by rfl⟩ : syracuseStep 258601 = 193951) (by norm_num)
theorem B389677 : Blo 227813 389677 := bbase (se 3 (by rfl) ⟨73064, by rfl⟩ : syracuseStep 389677 = 146129) (by norm_num)
theorem B291377 : Blo 227813 291377 := bbase (se 2 (by rfl) ⟨109266, by rfl⟩ : syracuseStep 291377 = 218533) (by norm_num)
theorem B520757 : Blo 227813 520757 := bbase (se 5 (by rfl) ⟨24410, by rfl⟩ : syracuseStep 520757 = 48821) (by norm_num)
theorem B258637 : Blo 227813 258637 := bbase (se 3 (by rfl) ⟨48494, by rfl⟩ : syracuseStep 258637 = 96989) (by norm_num)
theorem B1110629 : Blo 227813 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B291433 : Blo 227813 291433 := bbase (se 2 (by rfl) ⟨109287, by rfl⟩ : syracuseStep 291433 = 218575) (by norm_num)
theorem B586349 : Blo 227813 586349 := bbase (se 3 (by rfl) ⟨109940, by rfl⟩ : syracuseStep 586349 = 219881) (by norm_num)
theorem B258673 : Blo 227813 258673 := bbase (se 2 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 258673 = 194005) (by norm_num)
theorem B520829 : Blo 227813 520829 := bbase (se 3 (by rfl) ⟨97655, by rfl⟩ : syracuseStep 520829 = 195311) (by norm_num)
theorem B389765 : Blo 227813 389765 := bbase (se 4 (by rfl) ⟨36540, by rfl⟩ : syracuseStep 389765 = 73081) (by norm_num)
theorem B258709 : Blo 227813 258709 := bbase (se 6 (by rfl) ⟨6063, by rfl⟩ : syracuseStep 258709 = 12127) (by norm_num)
theorem B258745 : Blo 227813 258745 := bbase (se 2 (by rfl) ⟨97029, by rfl⟩ : syracuseStep 258745 = 194059) (by norm_num)
theorem B520901 : Blo 227813 520901 := bbase (se 4 (by rfl) ⟨48834, by rfl⟩ : syracuseStep 520901 = 97669) (by norm_num)
theorem B291529 : Blo 227813 291529 := bbase (se 2 (by rfl) ⟨109323, by rfl⟩ : syracuseStep 291529 = 218647) (by norm_num)
theorem B651989 : Blo 227813 651989 := bbase (se 7 (by rfl) ⟨7640, by rfl⟩ : syracuseStep 651989 = 15281) (by norm_num)
theorem B7533269 : Blo 227813 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B258781 : Blo 227813 258781 := bbase (se 3 (by rfl) ⟨48521, by rfl⟩ : syracuseStep 258781 = 97043) (by norm_num)
theorem B258817 : Blo 227813 258817 := bbase (se 2 (by rfl) ⟨97056, by rfl⟩ : syracuseStep 258817 = 194113) (by norm_num)
theorem B488197 : Blo 227813 488197 := bbase (se 4 (by rfl) ⟨45768, by rfl⟩ : syracuseStep 488197 = 91537) (by norm_num)
theorem B389893 : Blo 227813 389893 := bbase (se 4 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 389893 = 73105) (by norm_num)
theorem B520973 : Blo 227813 520973 := bbase (se 3 (by rfl) ⟨97682, by rfl⟩ : syracuseStep 520973 = 195365) (by norm_num)
theorem B258853 : Blo 227813 258853 := bbase (se 4 (by rfl) ⟨24267, by rfl⟩ : syracuseStep 258853 = 48535) (by norm_num)
theorem B586541 : Blo 227813 586541 := bbase (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) (by norm_num)
theorem B258889 : Blo 227813 258889 := bbase (se 2 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 258889 = 194167) (by norm_num)
theorem B521045 : Blo 227813 521045 := bbase (se 9 (by rfl) ⟨1526, by rfl⟩ : syracuseStep 521045 = 3053) (by norm_num)
theorem B389981 : Blo 227813 389981 := bbase (se 3 (by rfl) ⟨73121, by rfl⟩ : syracuseStep 389981 = 146243) (by norm_num)
theorem B258925 : Blo 227813 258925 := bbase (se 3 (by rfl) ⟨48548, by rfl⟩ : syracuseStep 258925 = 97097) (by norm_num)
theorem B291701 : Blo 227813 291701 := bbase (se 5 (by rfl) ⟨13673, by rfl⟩ : syracuseStep 291701 = 27347) (by norm_num)
theorem B258961 : Blo 227813 258961 := bbase (se 2 (by rfl) ⟨97110, by rfl⟩ : syracuseStep 258961 = 194221) (by norm_num)
theorem B521117 : Blo 227813 521117 := bbase (se 3 (by rfl) ⟨97709, by rfl⟩ : syracuseStep 521117 = 195419) (by norm_num)
theorem B291757 : Blo 227813 291757 := bbase (se 3 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 291757 = 109409) (by norm_num)
theorem B258997 : Blo 227813 258997 := bbase (se 5 (by rfl) ⟨12140, by rfl⟩ : syracuseStep 258997 = 24281) (by norm_num)
theorem B586685 : Blo 227813 586685 := bbase (se 3 (by rfl) ⟨110003, by rfl⟩ : syracuseStep 586685 = 220007) (by norm_num)
theorem B259033 : Blo 227813 259033 := bbase (se 2 (by rfl) ⟨97137, by rfl⟩ : syracuseStep 259033 = 194275) (by norm_num)
theorem B390109 : Blo 227813 390109 := bbase (se 3 (by rfl) ⟨73145, by rfl⟩ : syracuseStep 390109 = 146291) (by norm_num)
theorem B521189 : Blo 227813 521189 := bbase (se 4 (by rfl) ⟨48861, by rfl⟩ : syracuseStep 521189 = 97723) (by norm_num)
theorem B259069 : Blo 227813 259069 := bbase (se 3 (by rfl) ⟨48575, by rfl⟩ : syracuseStep 259069 = 97151) (by norm_num)
theorem B291853 : Blo 227813 291853 := bbase (se 3 (by rfl) ⟨54722, by rfl⟩ : syracuseStep 291853 = 109445) (by norm_num)
theorem B259105 : Blo 227813 259105 := bbase (se 2 (by rfl) ⟨97164, by rfl⟩ : syracuseStep 259105 = 194329) (by norm_num)
theorem B521261 : Blo 227813 521261 := bbase (se 3 (by rfl) ⟨97736, by rfl⟩ : syracuseStep 521261 = 195473) (by norm_num)
theorem B390197 : Blo 227813 390197 := bbase (se 5 (by rfl) ⟨18290, by rfl⟩ : syracuseStep 390197 = 36581) (by norm_num)
theorem B259141 : Blo 227813 259141 := bbase (se 4 (by rfl) ⟨24294, by rfl⟩ : syracuseStep 259141 = 48589) (by norm_num)
theorem B259177 : Blo 227813 259177 := bbase (se 2 (by rfl) ⟨97191, by rfl⟩ : syracuseStep 259177 = 194383) (by norm_num)
theorem B521333 : Blo 227813 521333 := bbase (se 5 (by rfl) ⟨24437, by rfl⟩ : syracuseStep 521333 = 48875) (by norm_num)
theorem B259213 : Blo 227813 259213 := bbase (se 3 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 259213 = 97205) (by norm_num)
theorem B259249 : Blo 227813 259249 := bbase (se 2 (by rfl) ⟨97218, by rfl⟩ : syracuseStep 259249 = 194437) (by norm_num)
theorem B390325 : Blo 227813 390325 := bbase (se 5 (by rfl) ⟨18296, by rfl⟩ : syracuseStep 390325 = 36593) (by norm_num)
theorem B292025 : Blo 227813 292025 := bbase (se 2 (by rfl) ⟨109509, by rfl⟩ : syracuseStep 292025 = 219019) (by norm_num)
theorem B521405 : Blo 227813 521405 := bbase (se 3 (by rfl) ⟨97763, by rfl⟩ : syracuseStep 521405 = 195527) (by norm_num)
theorem B259285 : Blo 227813 259285 := bbase (se 7 (by rfl) ⟨3038, by rfl⟩ : syracuseStep 259285 = 6077) (by norm_num)
theorem B292081 : Blo 227813 292081 := bbase (se 2 (by rfl) ⟨109530, by rfl⟩ : syracuseStep 292081 = 219061) (by norm_num)
theorem B488693 : Blo 227813 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B259321 : Blo 227813 259321 := bbase (se 2 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 259321 = 194491) (by norm_num)
theorem B521477 : Blo 227813 521477 := bbase (se 4 (by rfl) ⟨48888, by rfl⟩ : syracuseStep 521477 = 97777) (by norm_num)
theorem B390413 : Blo 227813 390413 := bbase (se 3 (by rfl) ⟨73202, by rfl⟩ : syracuseStep 390413 = 146405) (by norm_num)
theorem B259357 : Blo 227813 259357 := bbase (se 3 (by rfl) ⟨48629, by rfl⟩ : syracuseStep 259357 = 97259) (by norm_num)
theorem B324901 : Blo 227813 324901 := bbase (se 4 (by rfl) ⟨30459, by rfl⟩ : syracuseStep 324901 = 60919) (by norm_num)
theorem B259393 : Blo 227813 259393 := bbase (se 2 (by rfl) ⟨97272, by rfl⟩ : syracuseStep 259393 = 194545) (by norm_num)
theorem B521549 : Blo 227813 521549 := bbase (se 3 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 521549 = 195581) (by norm_num)
theorem B292177 : Blo 227813 292177 := bbase (se 2 (by rfl) ⟨109566, by rfl⟩ : syracuseStep 292177 = 219133) (by norm_num)
theorem B259429 : Blo 227813 259429 := bbase (se 4 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 259429 = 48643) (by norm_num)
theorem B652661 : Blo 227813 652661 := bbase (se 5 (by rfl) ⟨30593, by rfl⟩ : syracuseStep 652661 = 61187) (by norm_num)
theorem B259465 : Blo 227813 259465 := bbase (se 2 (by rfl) ⟨97299, by rfl⟩ : syracuseStep 259465 = 194599) (by norm_num)
theorem B390541 : Blo 227813 390541 := bbase (se 3 (by rfl) ⟨73226, by rfl⟩ : syracuseStep 390541 = 146453) (by norm_num)
theorem B259501 : Blo 227813 259501 := bbase (se 3 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 259501 = 97313) (by norm_num)
theorem B259537 : Blo 227813 259537 := bbase (se 2 (by rfl) ⟨97326, by rfl⟩ : syracuseStep 259537 = 194653) (by norm_num)
theorem B390629 : Blo 227813 390629 := bbase (se 4 (by rfl) ⟨36621, by rfl⟩ : syracuseStep 390629 = 73243) (by norm_num)
theorem B259573 : Blo 227813 259573 := bbase (se 5 (by rfl) ⟨12167, by rfl⟩ : syracuseStep 259573 = 24335) (by norm_num)
theorem B292349 : Blo 227813 292349 := bbase (se 3 (by rfl) ⟨54815, by rfl⟩ : syracuseStep 292349 = 109631) (by norm_num)
theorem B259609 : Blo 227813 259609 := bbase (se 2 (by rfl) ⟨97353, by rfl⟩ : syracuseStep 259609 = 194707) (by norm_num)
theorem B292405 : Blo 227813 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B259645 : Blo 227813 259645 := bbase (se 3 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 259645 = 97367) (by norm_num)
theorem B259681 : Blo 227813 259681 := bbase (se 2 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 259681 = 194761) (by norm_num)
theorem B390757 : Blo 227813 390757 := bbase (se 4 (by rfl) ⟨36633, by rfl⟩ : syracuseStep 390757 = 73267) (by norm_num)
theorem B325237 : Blo 227813 325237 := bbase (se 5 (by rfl) ⟨15245, by rfl⟩ : syracuseStep 325237 = 30491) (by norm_num)
theorem B259717 : Blo 227813 259717 := bbase (se 4 (by rfl) ⟨24348, by rfl⟩ : syracuseStep 259717 = 48697) (by norm_num)
theorem B292501 : Blo 227813 292501 := bbase (se 6 (by rfl) ⟨6855, by rfl⟩ : syracuseStep 292501 = 13711) (by norm_num)
theorem B259753 : Blo 227813 259753 := bbase (se 2 (by rfl) ⟨97407, by rfl⟩ : syracuseStep 259753 = 194815) (by norm_num)
theorem B390845 : Blo 227813 390845 := bbase (se 3 (by rfl) ⟨73283, by rfl⟩ : syracuseStep 390845 = 146567) (by norm_num)
theorem B554701 : Blo 227813 554701 := bbase (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) (by norm_num)
theorem B259789 : Blo 227813 259789 := bbase (se 3 (by rfl) ⟨48710, by rfl⟩ : syracuseStep 259789 = 97421) (by norm_num)
theorem B259825 : Blo 227813 259825 := bbase (se 2 (by rfl) ⟨97434, by rfl⟩ : syracuseStep 259825 = 194869) (by norm_num)
theorem B259861 : Blo 227813 259861 := bbase (se 6 (by rfl) ⟨6090, by rfl⟩ : syracuseStep 259861 = 12181) (by norm_num)
theorem B653093 : Blo 227813 653093 := bbase (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) (by norm_num)
theorem B259897 : Blo 227813 259897 := bbase (se 2 (by rfl) ⟨97461, by rfl⟩ : syracuseStep 259897 = 194923) (by norm_num)
theorem B390973 : Blo 227813 390973 := bbase (se 3 (by rfl) ⟨73307, by rfl⟩ : syracuseStep 390973 = 146615) (by norm_num)
theorem B292673 : Blo 227813 292673 := bbase (se 2 (by rfl) ⟨109752, by rfl⟩ : syracuseStep 292673 = 219505) (by norm_num)
theorem B325453 : Blo 227813 325453 := bbase (se 3 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 325453 = 122045) (by norm_num)
theorem B259933 : Blo 227813 259933 := bbase (se 3 (by rfl) ⟨48737, by rfl⟩ : syracuseStep 259933 = 97475) (by norm_num)
theorem B292729 : Blo 227813 292729 := bbase (se 2 (by rfl) ⟨109773, by rfl⟩ : syracuseStep 292729 = 219547) (by norm_num)
theorem B259969 : Blo 227813 259969 := bbase (se 2 (by rfl) ⟨97488, by rfl⟩ : syracuseStep 259969 = 194977) (by norm_num)
theorem B391061 : Blo 227813 391061 := bbase (se 6 (by rfl) ⟨9165, by rfl⟩ : syracuseStep 391061 = 18331) (by norm_num)
theorem B260005 : Blo 227813 260005 := bbase (se 4 (by rfl) ⟨24375, by rfl⟩ : syracuseStep 260005 = 48751) (by norm_num)
theorem B260041 : Blo 227813 260041 := bbase (se 2 (by rfl) ⟨97515, by rfl⟩ : syracuseStep 260041 = 195031) (by norm_num)
theorem B292825 : Blo 227813 292825 := bbase (se 2 (by rfl) ⟨109809, by rfl⟩ : syracuseStep 292825 = 219619) (by norm_num)
theorem B260077 : Blo 227813 260077 := bbase (se 3 (by rfl) ⟨48764, by rfl⟩ : syracuseStep 260077 = 97529) (by norm_num)
theorem B260113 : Blo 227813 260113 := bbase (se 2 (by rfl) ⟨97542, by rfl⟩ : syracuseStep 260113 = 195085) (by norm_num)
theorem B260149 : Blo 227813 260149 := bbase (se 5 (by rfl) ⟨12194, by rfl⟩ : syracuseStep 260149 = 24389) (by norm_num)
theorem B260185 : Blo 227813 260185 := bbase (se 2 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 260185 = 195139) (by norm_num)
theorem B489581 : Blo 227813 489581 := bbase (se 3 (by rfl) ⟨91796, by rfl⟩ : syracuseStep 489581 = 183593) (by norm_num)
theorem B260221 : Blo 227813 260221 := bbase (se 3 (by rfl) ⟨48791, by rfl⟩ : syracuseStep 260221 = 97583) (by norm_num)
theorem B292997 : Blo 227813 292997 := bbase (se 4 (by rfl) ⟨27468, by rfl⟩ : syracuseStep 292997 = 54937) (by norm_num)
theorem B260257 : Blo 227813 260257 := bbase (se 2 (by rfl) ⟨97596, by rfl⟩ : syracuseStep 260257 = 195193) (by norm_num)
theorem B293053 : Blo 227813 293053 := bbase (se 3 (by rfl) ⟨54947, by rfl⟩ : syracuseStep 293053 = 109895) (by norm_num)
theorem B325829 : Blo 227813 325829 := bbase (se 4 (by rfl) ⟨30546, by rfl⟩ : syracuseStep 325829 = 61093) (by norm_num)
theorem B260293 : Blo 227813 260293 := bbase (se 4 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 260293 = 48805) (by norm_num)
theorem B489701 : Blo 227813 489701 := bbase (se 4 (by rfl) ⟨45909, by rfl⟩ : syracuseStep 489701 = 91819) (by norm_num)
theorem B260329 : Blo 227813 260329 := bbase (se 2 (by rfl) ⟨97623, by rfl⟩ : syracuseStep 260329 = 195247) (by norm_num)
theorem B260365 : Blo 227813 260365 := bbase (se 3 (by rfl) ⟨48818, by rfl⟩ : syracuseStep 260365 = 97637) (by norm_num)
theorem B293149 : Blo 227813 293149 := bbase (se 3 (by rfl) ⟨54965, by rfl⟩ : syracuseStep 293149 = 109931) (by norm_num)
theorem B260401 : Blo 227813 260401 := bbase (se 2 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 260401 = 195301) (by norm_num)
theorem B260437 : Blo 227813 260437 := bbase (se 10 (by rfl) ⟨381, by rfl⟩ : syracuseStep 260437 = 763) (by norm_num)
theorem B555373 : Blo 227813 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B260473 : Blo 227813 260473 := bbase (se 2 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 260473 = 195355) (by norm_num)
theorem B260509 : Blo 227813 260509 := bbase (se 3 (by rfl) ⟨48845, by rfl⟩ : syracuseStep 260509 = 97691) (by norm_num)
theorem B1997237 : Blo 227813 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B260545 : Blo 227813 260545 := bbase (se 2 (by rfl) ⟨97704, by rfl⟩ : syracuseStep 260545 = 195409) (by norm_num)
theorem B293321 : Blo 227813 293321 := bbase (se 2 (by rfl) ⟨109995, by rfl⟩ : syracuseStep 293321 = 219991) (by norm_num)
theorem B260581 : Blo 227813 260581 := bbase (se 4 (by rfl) ⟨24429, by rfl⟩ : syracuseStep 260581 = 48859) (by norm_num)
theorem B293377 : Blo 227813 293377 := bbase (se 2 (by rfl) ⟨110016, by rfl⟩ : syracuseStep 293377 = 220033) (by norm_num)
theorem B260617 : Blo 227813 260617 := bbase (se 2 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 260617 = 195463) (by norm_num)
theorem B653845 : Blo 227813 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B260653 : Blo 227813 260653 := bbase (se 3 (by rfl) ⟨48872, by rfl⟩ : syracuseStep 260653 = 97745) (by norm_num)
theorem B1112629 : Blo 227813 1112629 := bbase (se 5 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 1112629 = 104309) (by norm_num)
theorem B260689 : Blo 227813 260689 := bbase (se 2 (by rfl) ⟨97758, by rfl⟩ : syracuseStep 260689 = 195517) (by norm_num)
theorem B260693 : Blo 227813 260693 := bbase (se 8 (by rfl) ⟨1527, by rfl⟩ : syracuseStep 260693 = 3055) (by norm_num)
theorem B555605 : Blo 227813 555605 := bbase (se 8 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 555605 = 6511) (by norm_num)
theorem B260725 : Blo 227813 260725 := bbase (se 5 (by rfl) ⟨12221, by rfl⟩ : syracuseStep 260725 = 24443) (by norm_num)
theorem B555653 : Blo 227813 555653 := bbase (se 4 (by rfl) ⟨52092, by rfl⟩ : syracuseStep 555653 = 104185) (by norm_num)
theorem B260761 : Blo 227813 260761 := bbase (se 2 (by rfl) ⟨97785, by rfl⟩ : syracuseStep 260761 = 195571) (by norm_num)
theorem B490333 : Blo 227813 490333 := bbase (se 3 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 490333 = 183875) (by norm_num)
theorem B785285 : Blo 227813 785285 := bbase (se 4 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 785285 = 147241) (by norm_num)
theorem B293773 : Blo 227813 293773 := bbase (se 3 (by rfl) ⟨55082, by rfl⟩ : syracuseStep 293773 = 110165) (by norm_num)
theorem B293917 : Blo 227813 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B1309877 : Blo 227813 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B261625 : Blo 227813 261625 := bbase (se 2 (by rfl) ⟨98109, by rfl⟩ : syracuseStep 261625 = 196219) (by norm_num)
theorem B556541 : Blo 227813 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B2227733 : Blo 227813 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B261697 : Blo 227813 261697 := bbase (se 2 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 261697 = 196273) (by norm_num)
theorem B327253 : Blo 227813 327253 := bbase (se 8 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 327253 = 3835) (by norm_num)
theorem B491221 : Blo 227813 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B982853 : Blo 227813 982853 := bbase (se 4 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 982853 = 184285) (by norm_num)
theorem B491341 : Blo 227813 491341 := bbase (se 3 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 491341 = 184253) (by norm_num)
theorem B229379 : Blo 227813 229379 := bstep (se 1 (by rfl) ⟨172034, by rfl⟩ : syracuseStep 229379 = 344069) B344069
theorem B229395 : Blo 227813 229395 := bstep (se 1 (by rfl) ⟨172046, by rfl⟩ : syracuseStep 229395 = 344093) B344093
theorem B229411 : Blo 227813 229411 := bstep (se 1 (by rfl) ⟨172058, by rfl⟩ : syracuseStep 229411 = 344117) B344117
theorem B229427 : Blo 227813 229427 := bstep (se 1 (by rfl) ⟨172070, by rfl⟩ : syracuseStep 229427 = 344141) B344141
theorem B327731 : Blo 227813 327731 := bstep (se 1 (by rfl) ⟨245798, by rfl⟩ : syracuseStep 327731 = 491597) B491597
theorem B229443 : Blo 227813 229443 := bstep (se 1 (by rfl) ⟨172082, by rfl⟩ : syracuseStep 229443 = 344165) B344165
theorem B229459 : Blo 227813 229459 := bstep (se 1 (by rfl) ⟨172094, by rfl⟩ : syracuseStep 229459 = 344189) B344189
theorem B229475 : Blo 227813 229475 := bstep (se 1 (by rfl) ⟨172106, by rfl⟩ : syracuseStep 229475 = 344213) B344213
theorem B229491 : Blo 227813 229491 := bstep (se 1 (by rfl) ⟨172118, by rfl⟩ : syracuseStep 229491 = 344237) B344237
theorem B229507 : Blo 227813 229507 := bstep (se 1 (by rfl) ⟨172130, by rfl⟩ : syracuseStep 229507 = 344261) B344261
theorem B491665 : Blo 227813 491665 := bstep (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) B368749
theorem B360593 : Blo 227813 360593 := bstep (se 2 (by rfl) ⟨135222, by rfl⟩ : syracuseStep 360593 = 270445) B270445
theorem B229523 : Blo 227813 229523 := bstep (se 1 (by rfl) ⟨172142, by rfl⟩ : syracuseStep 229523 = 344285) B344285
theorem B229539 : Blo 227813 229539 := bstep (se 1 (by rfl) ⟨172154, by rfl⟩ : syracuseStep 229539 = 344309) B344309
theorem B491683 : Blo 227813 491683 := bstep (se 1 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 491683 = 737525) B737525
theorem B229555 : Blo 227813 229555 := bstep (se 1 (by rfl) ⟨172166, by rfl⟩ : syracuseStep 229555 = 344333) B344333
theorem B229571 : Blo 227813 229571 := bstep (se 1 (by rfl) ⟨172178, by rfl⟩ : syracuseStep 229571 = 344357) B344357
theorem B229587 : Blo 227813 229587 := bstep (se 1 (by rfl) ⟨172190, by rfl⟩ : syracuseStep 229587 = 344381) B344381
theorem B229603 : Blo 227813 229603 := bstep (se 1 (by rfl) ⟨172202, by rfl⟩ : syracuseStep 229603 = 344405) B344405
theorem B229619 : Blo 227813 229619 := bstep (se 1 (by rfl) ⟨172214, by rfl⟩ : syracuseStep 229619 = 344429) B344429
theorem B229635 : Blo 227813 229635 := bstep (se 1 (by rfl) ⟨172226, by rfl⟩ : syracuseStep 229635 = 344453) B344453
theorem B229651 : Blo 227813 229651 := bstep (se 1 (by rfl) ⟨172238, by rfl⟩ : syracuseStep 229651 = 344477) B344477
theorem B229667 : Blo 227813 229667 := bstep (se 1 (by rfl) ⟨172250, by rfl⟩ : syracuseStep 229667 = 344501) B344501
theorem B229683 : Blo 227813 229683 := bstep (se 1 (by rfl) ⟨172262, by rfl⟩ : syracuseStep 229683 = 344525) B344525
theorem B229699 : Blo 227813 229699 := bstep (se 1 (by rfl) ⟨172274, by rfl⟩ : syracuseStep 229699 = 344549) B344549
theorem B229715 : Blo 227813 229715 := bstep (se 1 (by rfl) ⟨172286, by rfl⟩ : syracuseStep 229715 = 344573) B344573
theorem B229731 : Blo 227813 229731 := bstep (se 1 (by rfl) ⟨172298, by rfl⟩ : syracuseStep 229731 = 344597) B344597
theorem B229747 : Blo 227813 229747 := bstep (se 1 (by rfl) ⟨172310, by rfl⟩ : syracuseStep 229747 = 344621) B344621
theorem B229763 : Blo 227813 229763 := bstep (se 1 (by rfl) ⟨172322, by rfl⟩ : syracuseStep 229763 = 344645) B344645
theorem B229779 : Blo 227813 229779 := bstep (se 1 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 229779 = 344669) B344669
theorem B229795 : Blo 227813 229795 := bstep (se 1 (by rfl) ⟨172346, by rfl⟩ : syracuseStep 229795 = 344693) B344693
theorem B229811 : Blo 227813 229811 := bstep (se 1 (by rfl) ⟨172358, by rfl⟩ : syracuseStep 229811 = 344717) B344717
theorem B229827 : Blo 227813 229827 := bstep (se 1 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 229827 = 344741) B344741
theorem B229843 : Blo 227813 229843 := bstep (se 1 (by rfl) ⟨172382, by rfl⟩ : syracuseStep 229843 = 344765) B344765
theorem B229859 : Blo 227813 229859 := bstep (se 1 (by rfl) ⟨172394, by rfl⟩ : syracuseStep 229859 = 344789) B344789
theorem B229875 : Blo 227813 229875 := bstep (se 1 (by rfl) ⟨172406, by rfl⟩ : syracuseStep 229875 = 344813) B344813
theorem B229891 : Blo 227813 229891 := bstep (se 1 (by rfl) ⟨172418, by rfl⟩ : syracuseStep 229891 = 344837) B344837
theorem B229907 : Blo 227813 229907 := bstep (se 1 (by rfl) ⟨172430, by rfl⟩ : syracuseStep 229907 = 344861) B344861
theorem B229923 : Blo 227813 229923 := bstep (se 1 (by rfl) ⟨172442, by rfl⟩ : syracuseStep 229923 = 344885) B344885
theorem B229939 : Blo 227813 229939 := bstep (se 1 (by rfl) ⟨172454, by rfl⟩ : syracuseStep 229939 = 344909) B344909
theorem B229955 : Blo 227813 229955 := bstep (se 1 (by rfl) ⟨172466, by rfl⟩ : syracuseStep 229955 = 344933) B344933
theorem B229971 : Blo 227813 229971 := bstep (se 1 (by rfl) ⟨172478, by rfl⟩ : syracuseStep 229971 = 344957) B344957
theorem B229987 : Blo 227813 229987 := bstep (se 1 (by rfl) ⟨172490, by rfl⟩ : syracuseStep 229987 = 344981) B344981
theorem B393827 : Blo 227813 393827 := bstep (se 1 (by rfl) ⟨295370, by rfl⟩ : syracuseStep 393827 = 590741) B590741
theorem B230003 : Blo 227813 230003 := bstep (se 1 (by rfl) ⟨172502, by rfl⟩ : syracuseStep 230003 = 345005) B345005
theorem B230019 : Blo 227813 230019 := bstep (se 1 (by rfl) ⟨172514, by rfl⟩ : syracuseStep 230019 = 345029) B345029
theorem B230035 : Blo 227813 230035 := bstep (se 1 (by rfl) ⟨172526, by rfl⟩ : syracuseStep 230035 = 345053) B345053
theorem B230051 : Blo 227813 230051 := bstep (se 1 (by rfl) ⟨172538, by rfl⟩ : syracuseStep 230051 = 345077) B345077
theorem B328369 : Blo 227813 328369 := bstep (se 2 (by rfl) ⟨123138, by rfl⟩ : syracuseStep 328369 = 246277) B246277
theorem B230067 : Blo 227813 230067 := bstep (se 1 (by rfl) ⟨172550, by rfl⟩ : syracuseStep 230067 = 345101) B345101
theorem B230083 : Blo 227813 230083 := bstep (se 1 (by rfl) ⟨172562, by rfl⟩ : syracuseStep 230083 = 345125) B345125
theorem B230099 : Blo 227813 230099 := bstep (se 1 (by rfl) ⟨172574, by rfl⟩ : syracuseStep 230099 = 345149) B345149
theorem B230115 : Blo 227813 230115 := bstep (se 1 (by rfl) ⟨172586, by rfl⟩ : syracuseStep 230115 = 345173) B345173
theorem B230131 : Blo 227813 230131 := bstep (se 1 (by rfl) ⟨172598, by rfl⟩ : syracuseStep 230131 = 345197) B345197
theorem B230147 : Blo 227813 230147 := bstep (se 1 (by rfl) ⟨172610, by rfl⟩ : syracuseStep 230147 = 345221) B345221
theorem B230163 : Blo 227813 230163 := bstep (se 1 (by rfl) ⟨172622, by rfl⟩ : syracuseStep 230163 = 345245) B345245
theorem B230179 : Blo 227813 230179 := bstep (se 1 (by rfl) ⟨172634, by rfl⟩ : syracuseStep 230179 = 345269) B345269
theorem B328483 : Blo 227813 328483 := bstep (se 1 (by rfl) ⟨246362, by rfl⟩ : syracuseStep 328483 = 492725) B492725
theorem B230195 : Blo 227813 230195 := bstep (se 1 (by rfl) ⟨172646, by rfl⟩ : syracuseStep 230195 = 345293) B345293
theorem B230211 : Blo 227813 230211 := bstep (se 1 (by rfl) ⟨172658, by rfl⟩ : syracuseStep 230211 = 345317) B345317
theorem B1475405 : Blo 227813 1475405 := bstep (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) B553277
theorem B230227 : Blo 227813 230227 := bstep (se 1 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 230227 = 345341) B345341
theorem B230243 : Blo 227813 230243 := bstep (se 1 (by rfl) ⟨172682, by rfl⟩ : syracuseStep 230243 = 345365) B345365
theorem B656237 : Blo 227813 656237 := bstep (se 3 (by rfl) ⟨123044, by rfl⟩ : syracuseStep 656237 = 246089) B246089
theorem B230259 : Blo 227813 230259 := bstep (se 1 (by rfl) ⟨172694, by rfl⟩ : syracuseStep 230259 = 345389) B345389
theorem B230275 : Blo 227813 230275 := bstep (se 1 (by rfl) ⟨172706, by rfl⟩ : syracuseStep 230275 = 345413) B345413
theorem B230291 : Blo 227813 230291 := bstep (se 1 (by rfl) ⟨172718, by rfl⟩ : syracuseStep 230291 = 345437) B345437
theorem B230307 : Blo 227813 230307 := bstep (se 1 (by rfl) ⟨172730, by rfl⟩ : syracuseStep 230307 = 345461) B345461
theorem B230323 : Blo 227813 230323 := bstep (se 1 (by rfl) ⟨172742, by rfl⟩ : syracuseStep 230323 = 345485) B345485
theorem B230339 : Blo 227813 230339 := bstep (se 1 (by rfl) ⟨172754, by rfl⟩ : syracuseStep 230339 = 345509) B345509
theorem B230355 : Blo 227813 230355 := bstep (se 1 (by rfl) ⟨172766, by rfl⟩ : syracuseStep 230355 = 345533) B345533
theorem B230371 : Blo 227813 230371 := bstep (se 1 (by rfl) ⟨172778, by rfl⟩ : syracuseStep 230371 = 345557) B345557
theorem B230387 : Blo 227813 230387 := bstep (se 1 (by rfl) ⟨172790, by rfl⟩ : syracuseStep 230387 = 345581) B345581
theorem B230403 : Blo 227813 230403 := bstep (se 1 (by rfl) ⟨172802, by rfl⟩ : syracuseStep 230403 = 345605) B345605
theorem B230419 : Blo 227813 230419 := bstep (se 1 (by rfl) ⟨172814, by rfl⟩ : syracuseStep 230419 = 345629) B345629
theorem B230435 : Blo 227813 230435 := bstep (se 1 (by rfl) ⟨172826, by rfl⟩ : syracuseStep 230435 = 345653) B345653
theorem B656419 : Blo 227813 656419 := bstep (se 1 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 656419 = 984629) B984629
theorem B230451 : Blo 227813 230451 := bstep (se 1 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 230451 = 345677) B345677
theorem B4949045 : Blo 227813 4949045 := bstep (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) B463973
theorem B590915 : Blo 227813 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B230467 : Blo 227813 230467 := bstep (se 1 (by rfl) ⟨172850, by rfl⟩ : syracuseStep 230467 = 345701) B345701
theorem B230483 : Blo 227813 230483 := bstep (se 1 (by rfl) ⟨172862, by rfl⟩ : syracuseStep 230483 = 345725) B345725
theorem B1573987 : Blo 227813 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B230499 : Blo 227813 230499 := bstep (se 1 (by rfl) ⟨172874, by rfl⟩ : syracuseStep 230499 = 345749) B345749
theorem B230515 : Blo 227813 230515 := bstep (se 1 (by rfl) ⟨172886, by rfl⟩ : syracuseStep 230515 = 345773) B345773
theorem B230531 : Blo 227813 230531 := bstep (se 1 (by rfl) ⟨172898, by rfl⟩ : syracuseStep 230531 = 345797) B345797
theorem B230547 : Blo 227813 230547 := bstep (se 1 (by rfl) ⟨172910, by rfl⟩ : syracuseStep 230547 = 345821) B345821
theorem B230563 : Blo 227813 230563 := bstep (se 1 (by rfl) ⟨172922, by rfl⟩ : syracuseStep 230563 = 345845) B345845
theorem B230579 : Blo 227813 230579 := bstep (se 1 (by rfl) ⟨172934, by rfl⟩ : syracuseStep 230579 = 345869) B345869
theorem B656579 : Blo 227813 656579 := bstep (se 1 (by rfl) ⟨492434, by rfl⟩ : syracuseStep 656579 = 984869) B984869
theorem B230595 : Blo 227813 230595 := bstep (se 1 (by rfl) ⟨172946, by rfl⟩ : syracuseStep 230595 = 345893) B345893
theorem B230611 : Blo 227813 230611 := bstep (se 1 (by rfl) ⟨172958, by rfl⟩ : syracuseStep 230611 = 345917) B345917
theorem B230627 : Blo 227813 230627 := bstep (se 1 (by rfl) ⟨172970, by rfl⟩ : syracuseStep 230627 = 345941) B345941
theorem B230643 : Blo 227813 230643 := bstep (se 1 (by rfl) ⟨172982, by rfl⟩ : syracuseStep 230643 = 345965) B345965
theorem B230659 : Blo 227813 230659 := bstep (se 1 (by rfl) ⟨172994, by rfl⟩ : syracuseStep 230659 = 345989) B345989
theorem B230675 : Blo 227813 230675 := bstep (se 1 (by rfl) ⟨173006, by rfl⟩ : syracuseStep 230675 = 346013) B346013
theorem B230691 : Blo 227813 230691 := bstep (se 1 (by rfl) ⟨173018, by rfl⟩ : syracuseStep 230691 = 346037) B346037
theorem B230707 : Blo 227813 230707 := bstep (se 1 (by rfl) ⟨173030, by rfl⟩ : syracuseStep 230707 = 346061) B346061
theorem B230723 : Blo 227813 230723 := bstep (se 1 (by rfl) ⟨173042, by rfl⟩ : syracuseStep 230723 = 346085) B346085
theorem B230739 : Blo 227813 230739 := bstep (se 1 (by rfl) ⟨173054, by rfl⟩ : syracuseStep 230739 = 346109) B346109
theorem B230755 : Blo 227813 230755 := bstep (se 1 (by rfl) ⟨173066, by rfl⟩ : syracuseStep 230755 = 346133) B346133
theorem B230771 : Blo 227813 230771 := bstep (se 1 (by rfl) ⟨173078, by rfl⟩ : syracuseStep 230771 = 346157) B346157
theorem B230787 : Blo 227813 230787 := bstep (se 1 (by rfl) ⟨173090, by rfl⟩ : syracuseStep 230787 = 346181) B346181
theorem B230803 : Blo 227813 230803 := bstep (se 1 (by rfl) ⟨173102, by rfl⟩ : syracuseStep 230803 = 346205) B346205
theorem B230819 : Blo 227813 230819 := bstep (se 1 (by rfl) ⟨173114, by rfl⟩ : syracuseStep 230819 = 346229) B346229
theorem B230835 : Blo 227813 230835 := bstep (se 1 (by rfl) ⟨173126, by rfl⟩ : syracuseStep 230835 = 346253) B346253
theorem B230851 : Blo 227813 230851 := bstep (se 1 (by rfl) ⟨173138, by rfl⟩ : syracuseStep 230851 = 346277) B346277
theorem B230867 : Blo 227813 230867 := bstep (se 1 (by rfl) ⟨173150, by rfl⟩ : syracuseStep 230867 = 346301) B346301
theorem B230883 : Blo 227813 230883 := bstep (se 1 (by rfl) ⟨173162, by rfl⟩ : syracuseStep 230883 = 346325) B346325
theorem B230899 : Blo 227813 230899 := bstep (se 1 (by rfl) ⟨173174, by rfl⟩ : syracuseStep 230899 = 346349) B346349
theorem B230915 : Blo 227813 230915 := bstep (se 1 (by rfl) ⟨173186, by rfl⟩ : syracuseStep 230915 = 346373) B346373
theorem B230931 : Blo 227813 230931 := bstep (se 1 (by rfl) ⟨173198, by rfl⟩ : syracuseStep 230931 = 346397) B346397
theorem B230947 : Blo 227813 230947 := bstep (se 1 (by rfl) ⟨173210, by rfl⟩ : syracuseStep 230947 = 346421) B346421
theorem B230963 : Blo 227813 230963 := bstep (se 1 (by rfl) ⟨173222, by rfl⟩ : syracuseStep 230963 = 346445) B346445
theorem B230979 : Blo 227813 230979 := bstep (se 1 (by rfl) ⟨173234, by rfl⟩ : syracuseStep 230979 = 346469) B346469
theorem B230995 : Blo 227813 230995 := bstep (se 1 (by rfl) ⟨173246, by rfl⟩ : syracuseStep 230995 = 346493) B346493
theorem B231011 : Blo 227813 231011 := bstep (se 1 (by rfl) ⟨173258, by rfl⟩ : syracuseStep 231011 = 346517) B346517
theorem B231027 : Blo 227813 231027 := bstep (se 1 (by rfl) ⟨173270, by rfl⟩ : syracuseStep 231027 = 346541) B346541
theorem B231043 : Blo 227813 231043 := bstep (se 1 (by rfl) ⟨173282, by rfl⟩ : syracuseStep 231043 = 346565) B346565
theorem B231059 : Blo 227813 231059 := bstep (se 1 (by rfl) ⟨173294, by rfl⟩ : syracuseStep 231059 = 346589) B346589
theorem B231075 : Blo 227813 231075 := bstep (se 1 (by rfl) ⟨173306, by rfl⟩ : syracuseStep 231075 = 346613) B346613
theorem B231091 : Blo 227813 231091 := bstep (se 1 (by rfl) ⟨173318, by rfl⟩ : syracuseStep 231091 = 346637) B346637
theorem B231107 : Blo 227813 231107 := bstep (se 1 (by rfl) ⟨173330, by rfl⟩ : syracuseStep 231107 = 346661) B346661
theorem B231123 : Blo 227813 231123 := bstep (se 1 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 231123 = 346685) B346685
theorem B231139 : Blo 227813 231139 := bstep (se 1 (by rfl) ⟨173354, by rfl⟩ : syracuseStep 231139 = 346709) B346709
theorem B231155 : Blo 227813 231155 := bstep (se 1 (by rfl) ⟨173366, by rfl⟩ : syracuseStep 231155 = 346733) B346733
theorem B231171 : Blo 227813 231171 := bstep (se 1 (by rfl) ⟨173378, by rfl⟩ : syracuseStep 231171 = 346757) B346757
theorem B231187 : Blo 227813 231187 := bstep (se 1 (by rfl) ⟨173390, by rfl⟩ : syracuseStep 231187 = 346781) B346781
theorem B624419 : Blo 227813 624419 := bstep (se 1 (by rfl) ⟨468314, by rfl⟩ : syracuseStep 624419 = 936629) B936629
theorem B231203 : Blo 227813 231203 := bstep (se 1 (by rfl) ⟨173402, by rfl⟩ : syracuseStep 231203 = 346805) B346805
theorem B231219 : Blo 227813 231219 := bstep (se 1 (by rfl) ⟨173414, by rfl⟩ : syracuseStep 231219 = 346829) B346829
theorem B231235 : Blo 227813 231235 := bstep (se 1 (by rfl) ⟨173426, by rfl⟩ : syracuseStep 231235 = 346853) B346853
theorem B231251 : Blo 227813 231251 := bstep (se 1 (by rfl) ⟨173438, by rfl⟩ : syracuseStep 231251 = 346877) B346877
theorem B231267 : Blo 227813 231267 := bstep (se 1 (by rfl) ⟨173450, by rfl⟩ : syracuseStep 231267 = 346901) B346901
theorem B231283 : Blo 227813 231283 := bstep (se 1 (by rfl) ⟨173462, by rfl⟩ : syracuseStep 231283 = 346925) B346925
theorem B231299 : Blo 227813 231299 := bstep (se 1 (by rfl) ⟨173474, by rfl⟩ : syracuseStep 231299 = 346949) B346949
theorem B231315 : Blo 227813 231315 := bstep (se 1 (by rfl) ⟨173486, by rfl⟩ : syracuseStep 231315 = 346973) B346973
theorem B231331 : Blo 227813 231331 := bstep (se 1 (by rfl) ⟨173498, by rfl⟩ : syracuseStep 231331 = 346997) B346997
theorem B231347 : Blo 227813 231347 := bstep (se 1 (by rfl) ⟨173510, by rfl⟩ : syracuseStep 231347 = 347021) B347021
theorem B329665 : Blo 227813 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B231363 : Blo 227813 231363 := bstep (se 1 (by rfl) ⟨173522, by rfl⟩ : syracuseStep 231363 = 347045) B347045
theorem B231379 : Blo 227813 231379 := bstep (se 1 (by rfl) ⟨173534, by rfl⟩ : syracuseStep 231379 = 347069) B347069
theorem B231395 : Blo 227813 231395 := bstep (se 1 (by rfl) ⟨173546, by rfl⟩ : syracuseStep 231395 = 347093) B347093
theorem B231411 : Blo 227813 231411 := bstep (se 1 (by rfl) ⟨173558, by rfl⟩ : syracuseStep 231411 = 347117) B347117
theorem B231427 : Blo 227813 231427 := bstep (se 1 (by rfl) ⟨173570, by rfl⟩ : syracuseStep 231427 = 347141) B347141
theorem B231443 : Blo 227813 231443 := bstep (se 1 (by rfl) ⟨173582, by rfl⟩ : syracuseStep 231443 = 347165) B347165
theorem B231459 : Blo 227813 231459 := bstep (se 1 (by rfl) ⟨173594, by rfl⟩ : syracuseStep 231459 = 347189) B347189
theorem B231475 : Blo 227813 231475 := bstep (se 1 (by rfl) ⟨173606, by rfl⟩ : syracuseStep 231475 = 347213) B347213
theorem B231491 : Blo 227813 231491 := bstep (se 1 (by rfl) ⟨173618, by rfl⟩ : syracuseStep 231491 = 347237) B347237
theorem B231507 : Blo 227813 231507 := bstep (se 1 (by rfl) ⟨173630, by rfl⟩ : syracuseStep 231507 = 347261) B347261
theorem B231523 : Blo 227813 231523 := bstep (se 1 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 231523 = 347285) B347285
theorem B329827 : Blo 227813 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B231539 : Blo 227813 231539 := bstep (se 1 (by rfl) ⟨173654, by rfl⟩ : syracuseStep 231539 = 347309) B347309
theorem B231555 : Blo 227813 231555 := bstep (se 1 (by rfl) ⟨173666, by rfl⟩ : syracuseStep 231555 = 347333) B347333
theorem B985229 : Blo 227813 985229 := bstep (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) B369461
theorem B231571 : Blo 227813 231571 := bstep (se 1 (by rfl) ⟨173678, by rfl⟩ : syracuseStep 231571 = 347357) B347357
theorem B231587 : Blo 227813 231587 := bstep (se 1 (by rfl) ⟨173690, by rfl⟩ : syracuseStep 231587 = 347381) B347381
theorem B231603 : Blo 227813 231603 := bstep (se 1 (by rfl) ⟨173702, by rfl⟩ : syracuseStep 231603 = 347405) B347405
theorem B231619 : Blo 227813 231619 := bstep (se 1 (by rfl) ⟨173714, by rfl⟩ : syracuseStep 231619 = 347429) B347429
theorem B231635 : Blo 227813 231635 := bstep (se 1 (by rfl) ⟨173726, by rfl⟩ : syracuseStep 231635 = 347453) B347453
theorem B395489 : Blo 227813 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B231651 : Blo 227813 231651 := bstep (se 1 (by rfl) ⟨173738, by rfl⟩ : syracuseStep 231651 = 347477) B347477
theorem B657649 : Blo 227813 657649 := bstep (se 2 (by rfl) ⟨246618, by rfl⟩ : syracuseStep 657649 = 493237) B493237
theorem B231667 : Blo 227813 231667 := bstep (se 1 (by rfl) ⟨173750, by rfl⟩ : syracuseStep 231667 = 347501) B347501
theorem B231683 : Blo 227813 231683 := bstep (se 1 (by rfl) ⟨173762, by rfl⟩ : syracuseStep 231683 = 347525) B347525
theorem B231699 : Blo 227813 231699 := bstep (se 1 (by rfl) ⟨173774, by rfl⟩ : syracuseStep 231699 = 347549) B347549
theorem B231715 : Blo 227813 231715 := bstep (se 1 (by rfl) ⟨173786, by rfl⟩ : syracuseStep 231715 = 347573) B347573
theorem B231731 : Blo 227813 231731 := bstep (se 1 (by rfl) ⟨173798, by rfl⟩ : syracuseStep 231731 = 347597) B347597
theorem B231747 : Blo 227813 231747 := bstep (se 1 (by rfl) ⟨173810, by rfl⟩ : syracuseStep 231747 = 347621) B347621
theorem B231763 : Blo 227813 231763 := bstep (se 1 (by rfl) ⟨173822, by rfl⟩ : syracuseStep 231763 = 347645) B347645
theorem B231779 : Blo 227813 231779 := bstep (se 1 (by rfl) ⟨173834, by rfl⟩ : syracuseStep 231779 = 347669) B347669
theorem B231795 : Blo 227813 231795 := bstep (se 1 (by rfl) ⟨173846, by rfl⟩ : syracuseStep 231795 = 347693) B347693
theorem B493955 : Blo 227813 493955 := bstep (se 1 (by rfl) ⟨370466, by rfl⟩ : syracuseStep 493955 = 740933) B740933
theorem B231811 : Blo 227813 231811 := bstep (se 1 (by rfl) ⟨173858, by rfl⟩ : syracuseStep 231811 = 347717) B347717
theorem B1313293 : Blo 227813 1313293 := bstep (se 3 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 1313293 = 492485) B492485
theorem B625315 : Blo 227813 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B494417 : Blo 227813 494417 := bstep (se 2 (by rfl) ⟨185406, by rfl⟩ : syracuseStep 494417 = 370813) B370813
theorem B4393925 : Blo 227813 4393925 := bstep (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) B823861
theorem B822449 : Blo 227813 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B1969393 : Blo 227813 1969393 := bstep (se 2 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 1969393 = 1477045) B1477045
theorem B1576205 : Blo 227813 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B658925 : Blo 227813 658925 := bstep (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) B247097
theorem B888461 : Blo 227813 888461 := bstep (se 3 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 888461 = 333173) B333173
theorem B659107 : Blo 227813 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B659153 : Blo 227813 659153 := bstep (se 2 (by rfl) ⟨247182, by rfl⟩ : syracuseStep 659153 = 494365) B494365
theorem B626417 : Blo 227813 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B397153 : Blo 227813 397153 := bstep (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) B297865
theorem B1478533 : Blo 227813 1478533 := bstep (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) B277225
theorem B790499 : Blo 227813 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B790897 : Blo 227813 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B1315277 : Blo 227813 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B365123 : Blo 227813 365123 := bstep (se 1 (by rfl) ⟨273842, by rfl⟩ : syracuseStep 365123 = 547685) B547685
theorem B823907 : Blo 227813 823907 := bstep (se 1 (by rfl) ⟨617930, by rfl⟩ : syracuseStep 823907 = 1235861) B1235861
theorem B561763 : Blo 227813 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B1053283 : Blo 227813 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B692995 : Blo 227813 692995 := bstep (se 1 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 692995 = 1039493) B1039493
theorem B2495285 : Blo 227813 2495285 := bstep (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) B233933
theorem B2921285 : Blo 227813 2921285 := bstep (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) B547741
theorem B463715 : Blo 227813 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B332753 : Blo 227813 332753 := bstep (se 2 (by rfl) ⟨124782, by rfl⟩ : syracuseStep 332753 = 249565) B249565
theorem B1184867 : Blo 227813 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B595313 : Blo 227813 595313 := bstep (se 2 (by rfl) ⟨223242, by rfl⟩ : syracuseStep 595313 = 446485) B446485
theorem B1316209 : Blo 227813 1316209 := bstep (se 2 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 1316209 = 987157) B987157
theorem B234947 : Blo 227813 234947 := bstep (se 1 (by rfl) ⟨176210, by rfl⟩ : syracuseStep 234947 = 352421) B352421
theorem B1251085 : Blo 227813 1251085 := bstep (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) B469157
theorem B530275 : Blo 227813 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B464753 : Blo 227813 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B366545 : Blo 227813 366545 := bstep (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) B274909
theorem B1054925 : Blo 227813 1054925 := bstep (se 3 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 1054925 = 395597) B395597
theorem B989603 : Blo 227813 989603 := bstep (se 1 (by rfl) ⟨742202, by rfl⟩ : syracuseStep 989603 = 1484405) B1484405
theorem B1645069 : Blo 227813 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B1153763 : Blo 227813 1153763 := bstep (se 1 (by rfl) ⟨865322, by rfl⟩ : syracuseStep 1153763 = 1730645) B1730645
theorem B1317667 : Blo 227813 1317667 := bstep (se 1 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 1317667 = 1976501) B1976501
theorem B367411 : Blo 227813 367411 := bstep (se 1 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 367411 = 551117) B551117
theorem B433201 : Blo 227813 433201 := bstep (se 2 (by rfl) ⟨162450, by rfl⟩ : syracuseStep 433201 = 324901) B324901
theorem B367667 : Blo 227813 367667 := bstep (se 1 (by rfl) ⟨275750, by rfl⟩ : syracuseStep 367667 = 551501) B551501
theorem B1318193 : Blo 227813 1318193 := bstep (se 2 (by rfl) ⟨494322, by rfl⟩ : syracuseStep 1318193 = 988645) B988645
theorem B433603 : Blo 227813 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B433649 : Blo 227813 433649 := bstep (se 2 (by rfl) ⟨162618, by rfl⟩ : syracuseStep 433649 = 325237) B325237
theorem B1154573 : Blo 227813 1154573 := bstep (se 3 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 1154573 = 432965) B432965
theorem B1187569 : Blo 227813 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B433937 : Blo 227813 433937 := bstep (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) B325453
theorem B1744739 : Blo 227813 1744739 := bstep (se 1 (by rfl) ⟨1308554, by rfl⟩ : syracuseStep 1744739 = 2617109) B2617109
theorem B3383153 : Blo 227813 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B368641 : Blo 227813 368641 := bstep (se 2 (by rfl) ⟨138240, by rfl⟩ : syracuseStep 368641 = 276481) B276481
theorem B827597 : Blo 227813 827597 := bstep (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) B310349
theorem B467299 : Blo 227813 467299 := bstep (se 1 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 467299 = 700949) B700949
theorem B1974725 : Blo 227813 1974725 := bstep (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) B370261
theorem B434659 : Blo 227813 434659 := bstep (se 1 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 434659 = 651989) B651989
theorem B5022179 : Blo 227813 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B1319651 : Blo 227813 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B1483505 : Blo 227813 1483505 := bstep (se 2 (by rfl) ⟨556314, by rfl⟩ : syracuseStep 1483505 = 1112629) B1112629
theorem B828301 : Blo 227813 828301 := bstep (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) B310613
theorem B369569 : Blo 227813 369569 := bstep (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) B277177
theorem B435107 : Blo 227813 435107 := bstep (se 1 (by rfl) ⟨326330, by rfl⟩ : syracuseStep 435107 = 652661) B652661
theorem B599057 : Blo 227813 599057 := bstep (se 2 (by rfl) ⟨224646, by rfl⟩ : syracuseStep 599057 = 449293) B449293
theorem B435395 : Blo 227813 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B369937 : Blo 227813 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B1123661 : Blo 227813 1123661 := bstep (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) B421373
theorem B468337 : Blo 227813 468337 := bstep (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) B351253
theorem B501233 : Blo 227813 501233 := bstep (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) B375925
theorem B370403 : Blo 227813 370403 := bstep (se 1 (by rfl) ⟨277802, by rfl⟩ : syracuseStep 370403 = 555605) B555605
theorem B370435 : Blo 227813 370435 := bstep (se 1 (by rfl) ⟨277826, by rfl⟩ : syracuseStep 370435 = 555653) B555653
theorem B436337 : Blo 227813 436337 := bstep (se 2 (by rfl) ⟨163626, by rfl⟩ : syracuseStep 436337 = 327253) B327253
theorem B1059149 : Blo 227813 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B371027 : Blo 227813 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B1485155 : Blo 227813 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B731501 : Blo 227813 731501 := bstep (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) B274313
theorem B1157489 : Blo 227813 1157489 := bstep (se 2 (by rfl) ⟨434058, by rfl⟩ : syracuseStep 1157489 = 868117) B868117
theorem B830321 : Blo 227813 830321 := bstep (se 2 (by rfl) ⟨311370, by rfl⟩ : syracuseStep 830321 = 622741) B622741
theorem B437233 : Blo 227813 437233 := bstep (se 2 (by rfl) ⟨163962, by rfl⟩ : syracuseStep 437233 = 327925) B327925
theorem B437393 : Blo 227813 437393 := bstep (se 2 (by rfl) ⟨164022, by rfl⟩ : syracuseStep 437393 = 328045) B328045
theorem B1584305 : Blo 227813 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B699853 : Blo 227813 699853 := bstep (se 3 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 699853 = 262445) B262445
theorem B437795 : Blo 227813 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B1158947 : Blo 227813 1158947 := bstep (se 1 (by rfl) ⟨869210, by rfl⟩ : syracuseStep 1158947 = 1738421) B1738421
theorem B733283 : Blo 227813 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B6697073 : Blo 227813 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B2470115 : Blo 227813 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B2961677 : Blo 227813 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B438691 : Blo 227813 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B6238691 : Blo 227813 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B700913 : Blo 227813 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B438851 : Blo 227813 438851 := bstep (se 1 (by rfl) ⟨329138, by rfl⟩ : syracuseStep 438851 = 658277) B658277
theorem B1159757 : Blo 227813 1159757 := bstep (se 3 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 1159757 = 434909) B434909
theorem B995917 : Blo 227813 995917 := bstep (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) B373469
theorem B275251 : Blo 227813 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B865187 : Blo 227813 865187 := bstep (se 1 (by rfl) ⟨648890, by rfl⟩ : syracuseStep 865187 = 1297781) B1297781
theorem B865201 : Blo 227813 865201 := bstep (se 2 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 865201 = 648901) B648901
theorem B1750085 : Blo 227813 1750085 := bstep (se 4 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 1750085 = 328141) B328141
theorem B570577 : Blo 227813 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B734627 : Blo 227813 734627 := bstep (se 1 (by rfl) ⟨550970, by rfl⟩ : syracuseStep 734627 = 1101941) B1101941
theorem B2209265 : Blo 227813 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B439921 : Blo 227813 439921 := bstep (se 2 (by rfl) ⟨164970, by rfl⟩ : syracuseStep 439921 = 329941) B329941
theorem B341729 : Blo 227813 341729 := bstep (se 2 (by rfl) ⟨128148, by rfl⟩ : syracuseStep 341729 = 256297) B256297
theorem B341747 : Blo 227813 341747 := bstep (se 1 (by rfl) ⟨256310, by rfl⟩ : syracuseStep 341747 = 512621) B512621
theorem B341777 : Blo 227813 341777 := bstep (se 2 (by rfl) ⟨128166, by rfl⟩ : syracuseStep 341777 = 256333) B256333
theorem B341795 : Blo 227813 341795 := bstep (se 1 (by rfl) ⟨256346, by rfl⟩ : syracuseStep 341795 = 512693) B512693
theorem B341825 : Blo 227813 341825 := bstep (se 2 (by rfl) ⟨128184, by rfl⟩ : syracuseStep 341825 = 256369) B256369
theorem B341843 : Blo 227813 341843 := bstep (se 1 (by rfl) ⟨256382, by rfl⟩ : syracuseStep 341843 = 512765) B512765
theorem B341873 : Blo 227813 341873 := bstep (se 2 (by rfl) ⟨128202, by rfl⟩ : syracuseStep 341873 = 256405) B256405
theorem B341891 : Blo 227813 341891 := bstep (se 1 (by rfl) ⟨256418, by rfl⟩ : syracuseStep 341891 = 512837) B512837
theorem B341921 : Blo 227813 341921 := bstep (se 2 (by rfl) ⟨128220, by rfl⟩ : syracuseStep 341921 = 256441) B256441
theorem B341939 : Blo 227813 341939 := bstep (se 1 (by rfl) ⟨256454, by rfl⟩ : syracuseStep 341939 = 512909) B512909
theorem B341969 : Blo 227813 341969 := bstep (se 2 (by rfl) ⟨128238, by rfl⟩ : syracuseStep 341969 = 256477) B256477
theorem B341987 : Blo 227813 341987 := bstep (se 1 (by rfl) ⟨256490, by rfl⟩ : syracuseStep 341987 = 512981) B512981
theorem B342017 : Blo 227813 342017 := bstep (se 2 (by rfl) ⟨128256, by rfl⟩ : syracuseStep 342017 = 256513) B256513
theorem B342035 : Blo 227813 342035 := bstep (se 1 (by rfl) ⟨256526, by rfl⟩ : syracuseStep 342035 = 513053) B513053
theorem B342065 : Blo 227813 342065 := bstep (se 2 (by rfl) ⟨128274, by rfl⟩ : syracuseStep 342065 = 256549) B256549
theorem B342083 : Blo 227813 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B342113 : Blo 227813 342113 := bstep (se 2 (by rfl) ⟨128292, by rfl⟩ : syracuseStep 342113 = 256585) B256585
theorem B702577 : Blo 227813 702577 := bstep (se 2 (by rfl) ⟨263466, by rfl⟩ : syracuseStep 702577 = 526933) B526933
theorem B342131 : Blo 227813 342131 := bstep (se 1 (by rfl) ⟨256598, by rfl⟩ : syracuseStep 342131 = 513197) B513197
theorem B342161 : Blo 227813 342161 := bstep (se 2 (by rfl) ⟨128310, by rfl⟩ : syracuseStep 342161 = 256621) B256621
theorem B342179 : Blo 227813 342179 := bstep (se 1 (by rfl) ⟨256634, by rfl⟩ : syracuseStep 342179 = 513269) B513269
theorem B342209 : Blo 227813 342209 := bstep (se 2 (by rfl) ⟨128328, by rfl⟩ : syracuseStep 342209 = 256657) B256657
theorem B309457 : Blo 227813 309457 := bstep (se 2 (by rfl) ⟨116046, by rfl⟩ : syracuseStep 309457 = 232093) B232093
theorem B342227 : Blo 227813 342227 := bstep (se 1 (by rfl) ⟨256670, by rfl⟩ : syracuseStep 342227 = 513341) B513341
theorem B342257 : Blo 227813 342257 := bstep (se 2 (by rfl) ⟨128346, by rfl⟩ : syracuseStep 342257 = 256693) B256693
theorem B342275 : Blo 227813 342275 := bstep (se 1 (by rfl) ⟨256706, by rfl⟩ : syracuseStep 342275 = 513413) B513413
theorem B342305 : Blo 227813 342305 := bstep (se 2 (by rfl) ⟨128364, by rfl⟩ : syracuseStep 342305 = 256729) B256729
theorem B342323 : Blo 227813 342323 := bstep (se 1 (by rfl) ⟨256742, by rfl⟩ : syracuseStep 342323 = 513485) B513485
theorem B342353 : Blo 227813 342353 := bstep (se 2 (by rfl) ⟨128382, by rfl⟩ : syracuseStep 342353 = 256765) B256765
theorem B342371 : Blo 227813 342371 := bstep (se 1 (by rfl) ⟨256778, by rfl⟩ : syracuseStep 342371 = 513557) B513557
theorem B866659 : Blo 227813 866659 := bstep (se 1 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 866659 = 1299989) B1299989
theorem B342401 : Blo 227813 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B342419 : Blo 227813 342419 := bstep (se 1 (by rfl) ⟨256814, by rfl⟩ : syracuseStep 342419 = 513629) B513629
theorem B342449 : Blo 227813 342449 := bstep (se 2 (by rfl) ⟨128418, by rfl⟩ : syracuseStep 342449 = 256837) B256837
theorem B1325489 : Blo 227813 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B342467 : Blo 227813 342467 := bstep (se 1 (by rfl) ⟨256850, by rfl⟩ : syracuseStep 342467 = 513701) B513701
theorem B342497 : Blo 227813 342497 := bstep (se 2 (by rfl) ⟨128436, by rfl⟩ : syracuseStep 342497 = 256873) B256873
theorem B342515 : Blo 227813 342515 := bstep (se 1 (by rfl) ⟨256886, by rfl⟩ : syracuseStep 342515 = 513773) B513773
theorem B342545 : Blo 227813 342545 := bstep (se 2 (by rfl) ⟨128454, by rfl⟩ : syracuseStep 342545 = 256909) B256909
theorem B342563 : Blo 227813 342563 := bstep (se 1 (by rfl) ⟨256922, by rfl⟩ : syracuseStep 342563 = 513845) B513845
theorem B342593 : Blo 227813 342593 := bstep (se 2 (by rfl) ⟨128472, by rfl⟩ : syracuseStep 342593 = 256945) B256945
theorem B244291 : Blo 227813 244291 := bstep (se 1 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 244291 = 366437) B366437
theorem B342611 : Blo 227813 342611 := bstep (se 1 (by rfl) ⟨256958, by rfl⟩ : syracuseStep 342611 = 513917) B513917
theorem B342641 : Blo 227813 342641 := bstep (se 2 (by rfl) ⟨128490, by rfl⟩ : syracuseStep 342641 = 256981) B256981
theorem B342659 : Blo 227813 342659 := bstep (se 1 (by rfl) ⟨256994, by rfl⟩ : syracuseStep 342659 = 513989) B513989
theorem B342689 : Blo 227813 342689 := bstep (se 2 (by rfl) ⟨128508, by rfl⟩ : syracuseStep 342689 = 257017) B257017
theorem B342707 : Blo 227813 342707 := bstep (se 1 (by rfl) ⟨257030, by rfl⟩ : syracuseStep 342707 = 514061) B514061
theorem B277187 : Blo 227813 277187 := bstep (se 1 (by rfl) ⟨207890, by rfl⟩ : syracuseStep 277187 = 415781) B415781
theorem B342737 : Blo 227813 342737 := bstep (se 2 (by rfl) ⟨128526, by rfl⟩ : syracuseStep 342737 = 257053) B257053
theorem B342755 : Blo 227813 342755 := bstep (se 1 (by rfl) ⟨257066, by rfl⟩ : syracuseStep 342755 = 514133) B514133
theorem B342785 : Blo 227813 342785 := bstep (se 2 (by rfl) ⟨128544, by rfl⟩ : syracuseStep 342785 = 257089) B257089
theorem B342803 : Blo 227813 342803 := bstep (se 1 (by rfl) ⟨257102, by rfl⟩ : syracuseStep 342803 = 514205) B514205
theorem B310051 : Blo 227813 310051 := bstep (se 1 (by rfl) ⟨232538, by rfl⟩ : syracuseStep 310051 = 465077) B465077
theorem B342833 : Blo 227813 342833 := bstep (se 2 (by rfl) ⟨128562, by rfl⟩ : syracuseStep 342833 = 257125) B257125
theorem B342851 : Blo 227813 342851 := bstep (se 1 (by rfl) ⟨257138, by rfl⟩ : syracuseStep 342851 = 514277) B514277
theorem B342881 : Blo 227813 342881 := bstep (se 2 (by rfl) ⟨128580, by rfl⟩ : syracuseStep 342881 = 257161) B257161
theorem B342899 : Blo 227813 342899 := bstep (se 1 (by rfl) ⟨257174, by rfl⟩ : syracuseStep 342899 = 514349) B514349
theorem B342929 : Blo 227813 342929 := bstep (se 2 (by rfl) ⟨128598, by rfl⟩ : syracuseStep 342929 = 257197) B257197
theorem B342947 : Blo 227813 342947 := bstep (se 1 (by rfl) ⟨257210, by rfl⟩ : syracuseStep 342947 = 514421) B514421
theorem B342977 : Blo 227813 342977 := bstep (se 2 (by rfl) ⟨128616, by rfl⟩ : syracuseStep 342977 = 257233) B257233
theorem B342995 : Blo 227813 342995 := bstep (se 1 (by rfl) ⟨257246, by rfl⟩ : syracuseStep 342995 = 514493) B514493
theorem B343025 : Blo 227813 343025 := bstep (se 2 (by rfl) ⟨128634, by rfl⟩ : syracuseStep 343025 = 257269) B257269
theorem B343043 : Blo 227813 343043 := bstep (se 1 (by rfl) ⟨257282, by rfl⟩ : syracuseStep 343043 = 514565) B514565
theorem B244739 : Blo 227813 244739 := bstep (se 1 (by rfl) ⟨183554, by rfl⟩ : syracuseStep 244739 = 367109) B367109
theorem B343073 : Blo 227813 343073 := bstep (se 2 (by rfl) ⟨128652, by rfl⟩ : syracuseStep 343073 = 257305) B257305
theorem B343091 : Blo 227813 343091 := bstep (se 1 (by rfl) ⟨257318, by rfl⟩ : syracuseStep 343091 = 514637) B514637
theorem B343121 : Blo 227813 343121 := bstep (se 2 (by rfl) ⟨128670, by rfl⟩ : syracuseStep 343121 = 257341) B257341
theorem B343139 : Blo 227813 343139 := bstep (se 1 (by rfl) ⟨257354, by rfl⟩ : syracuseStep 343139 = 514709) B514709
theorem B343169 : Blo 227813 343169 := bstep (se 2 (by rfl) ⟨128688, by rfl⟩ : syracuseStep 343169 = 257377) B257377
theorem B736397 : Blo 227813 736397 := bstep (se 3 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 736397 = 276149) B276149
theorem B343187 : Blo 227813 343187 := bstep (se 1 (by rfl) ⟨257390, by rfl⟩ : syracuseStep 343187 = 514781) B514781
theorem B343217 : Blo 227813 343217 := bstep (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) B257413
theorem B933041 : Blo 227813 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B343235 : Blo 227813 343235 := bstep (se 1 (by rfl) ⟨257426, by rfl⟩ : syracuseStep 343235 = 514853) B514853
theorem B769229 : Blo 227813 769229 := bstep (se 3 (by rfl) ⟨144230, by rfl⟩ : syracuseStep 769229 = 288461) B288461
theorem B343265 : Blo 227813 343265 := bstep (se 2 (by rfl) ⟨128724, by rfl⟩ : syracuseStep 343265 = 257449) B257449
theorem B1391843 : Blo 227813 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B343283 : Blo 227813 343283 := bstep (se 1 (by rfl) ⟨257462, by rfl⟩ : syracuseStep 343283 = 514925) B514925
theorem B769283 : Blo 227813 769283 := bstep (se 1 (by rfl) ⟨576962, by rfl⟩ : syracuseStep 769283 = 1153925) B1153925
theorem B343313 : Blo 227813 343313 := bstep (se 2 (by rfl) ⟨128742, by rfl⟩ : syracuseStep 343313 = 257485) B257485
theorem B343331 : Blo 227813 343331 := bstep (se 1 (by rfl) ⟨257498, by rfl⟩ : syracuseStep 343331 = 514997) B514997
theorem B343361 : Blo 227813 343361 := bstep (se 2 (by rfl) ⟨128760, by rfl⟩ : syracuseStep 343361 = 257521) B257521
theorem B376145 : Blo 227813 376145 := bstep (se 2 (by rfl) ⟨141054, by rfl⟩ : syracuseStep 376145 = 282109) B282109
theorem B343379 : Blo 227813 343379 := bstep (se 1 (by rfl) ⟨257534, by rfl⟩ : syracuseStep 343379 = 515069) B515069
theorem B343409 : Blo 227813 343409 := bstep (se 2 (by rfl) ⟨128778, by rfl⟩ : syracuseStep 343409 = 257557) B257557
theorem B310657 : Blo 227813 310657 := bstep (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) B232993
theorem B343427 : Blo 227813 343427 := bstep (se 1 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 343427 = 515141) B515141
theorem B343457 : Blo 227813 343457 := bstep (se 2 (by rfl) ⟨128796, by rfl⟩ : syracuseStep 343457 = 257593) B257593
theorem B1162673 : Blo 227813 1162673 := bstep (se 2 (by rfl) ⟨436002, by rfl⟩ : syracuseStep 1162673 = 872005) B872005
theorem B343475 : Blo 227813 343475 := bstep (se 1 (by rfl) ⟨257606, by rfl⟩ : syracuseStep 343475 = 515213) B515213
theorem B343505 : Blo 227813 343505 := bstep (se 2 (by rfl) ⟨128814, by rfl⟩ : syracuseStep 343505 = 257629) B257629
theorem B343523 : Blo 227813 343523 := bstep (se 1 (by rfl) ⟨257642, by rfl⟩ : syracuseStep 343523 = 515285) B515285
theorem B769517 : Blo 227813 769517 := bstep (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) B288569
theorem B343553 : Blo 227813 343553 := bstep (se 2 (by rfl) ⟨128832, by rfl⟩ : syracuseStep 343553 = 257665) B257665
theorem B769553 : Blo 227813 769553 := bstep (se 2 (by rfl) ⟨288582, by rfl⟩ : syracuseStep 769553 = 577165) B577165
theorem B343571 : Blo 227813 343571 := bstep (se 1 (by rfl) ⟨257678, by rfl⟩ : syracuseStep 343571 = 515357) B515357
theorem B343601 : Blo 227813 343601 := bstep (se 2 (by rfl) ⟨128850, by rfl⟩ : syracuseStep 343601 = 257701) B257701
theorem B343619 : Blo 227813 343619 := bstep (se 1 (by rfl) ⟨257714, by rfl⟩ : syracuseStep 343619 = 515429) B515429
theorem B343649 : Blo 227813 343649 := bstep (se 2 (by rfl) ⟨128868, by rfl⟩ : syracuseStep 343649 = 257737) B257737
theorem B343667 : Blo 227813 343667 := bstep (se 1 (by rfl) ⟨257750, by rfl⟩ : syracuseStep 343667 = 515501) B515501
theorem B343697 : Blo 227813 343697 := bstep (se 2 (by rfl) ⟨128886, by rfl⟩ : syracuseStep 343697 = 257773) B257773
theorem B343715 : Blo 227813 343715 := bstep (se 1 (by rfl) ⟨257786, by rfl⟩ : syracuseStep 343715 = 515573) B515573
theorem B343745 : Blo 227813 343745 := bstep (se 2 (by rfl) ⟨128904, by rfl⟩ : syracuseStep 343745 = 257809) B257809
theorem B343763 : Blo 227813 343763 := bstep (se 1 (by rfl) ⟨257822, by rfl⟩ : syracuseStep 343763 = 515645) B515645
theorem B343793 : Blo 227813 343793 := bstep (se 2 (by rfl) ⟨128922, by rfl⟩ : syracuseStep 343793 = 257845) B257845
theorem B343811 : Blo 227813 343811 := bstep (se 1 (by rfl) ⟨257858, by rfl⟩ : syracuseStep 343811 = 515717) B515717
theorem B343841 : Blo 227813 343841 := bstep (se 2 (by rfl) ⟨128940, by rfl⟩ : syracuseStep 343841 = 257881) B257881
theorem B1392419 : Blo 227813 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B343859 : Blo 227813 343859 := bstep (se 1 (by rfl) ⟨257894, by rfl⟩ : syracuseStep 343859 = 515789) B515789
theorem B343889 : Blo 227813 343889 := bstep (se 2 (by rfl) ⟨128958, by rfl⟩ : syracuseStep 343889 = 257917) B257917
theorem B343907 : Blo 227813 343907 := bstep (se 1 (by rfl) ⟨257930, by rfl⟩ : syracuseStep 343907 = 515861) B515861
theorem B343937 : Blo 227813 343937 := bstep (se 2 (by rfl) ⟨128976, by rfl⟩ : syracuseStep 343937 = 257953) B257953
theorem B2211725 : Blo 227813 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B343955 : Blo 227813 343955 := bstep (se 1 (by rfl) ⟨257966, by rfl⟩ : syracuseStep 343955 = 515933) B515933
theorem B343985 : Blo 227813 343985 := bstep (se 2 (by rfl) ⟨128994, by rfl⟩ : syracuseStep 343985 = 257989) B257989
theorem B3162037 : Blo 227813 3162037 := bstep (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) B296441
theorem B344003 : Blo 227813 344003 := bstep (se 1 (by rfl) ⟨258002, by rfl⟩ : syracuseStep 344003 = 516005) B516005
theorem B344033 : Blo 227813 344033 := bstep (se 2 (by rfl) ⟨129012, by rfl⟩ : syracuseStep 344033 = 258025) B258025
theorem B344051 : Blo 227813 344051 := bstep (se 1 (by rfl) ⟨258038, by rfl⟩ : syracuseStep 344051 = 516077) B516077
theorem B344081 : Blo 227813 344081 := bstep (se 2 (by rfl) ⟨129030, by rfl⟩ : syracuseStep 344081 = 258061) B258061
theorem B344099 : Blo 227813 344099 := bstep (se 1 (by rfl) ⟨258074, by rfl⟩ : syracuseStep 344099 = 516149) B516149
theorem B770093 : Blo 227813 770093 := bstep (se 3 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 770093 = 288785) B288785
theorem B344129 : Blo 227813 344129 := bstep (se 2 (by rfl) ⟨129048, by rfl⟩ : syracuseStep 344129 = 258097) B258097
theorem B344147 : Blo 227813 344147 := bstep (se 1 (by rfl) ⟨258110, by rfl⟩ : syracuseStep 344147 = 516221) B516221
theorem B770147 : Blo 227813 770147 := bstep (se 1 (by rfl) ⟨577610, by rfl⟩ : syracuseStep 770147 = 1155221) B1155221
theorem B344177 : Blo 227813 344177 := bstep (se 2 (by rfl) ⟨129066, by rfl⟩ : syracuseStep 344177 = 258133) B258133
theorem B344195 : Blo 227813 344195 := bstep (se 1 (by rfl) ⟨258146, by rfl⟩ : syracuseStep 344195 = 516293) B516293
theorem B344225 : Blo 227813 344225 := bstep (se 2 (by rfl) ⟨129084, by rfl⟩ : syracuseStep 344225 = 258169) B258169
theorem B344243 : Blo 227813 344243 := bstep (se 1 (by rfl) ⟨258182, by rfl⟩ : syracuseStep 344243 = 516365) B516365
theorem B344273 : Blo 227813 344273 := bstep (se 2 (by rfl) ⟨129102, by rfl⟩ : syracuseStep 344273 = 258205) B258205
theorem B344291 : Blo 227813 344291 := bstep (se 1 (by rfl) ⟨258218, by rfl⟩ : syracuseStep 344291 = 516437) B516437
theorem B344321 : Blo 227813 344321 := bstep (se 2 (by rfl) ⟨129120, by rfl⟩ : syracuseStep 344321 = 258241) B258241
theorem B344339 : Blo 227813 344339 := bstep (se 1 (by rfl) ⟨258254, by rfl⟩ : syracuseStep 344339 = 516509) B516509
theorem B344369 : Blo 227813 344369 := bstep (se 2 (by rfl) ⟨129138, by rfl⟩ : syracuseStep 344369 = 258277) B258277
theorem B344387 : Blo 227813 344387 := bstep (se 1 (by rfl) ⟨258290, by rfl⟩ : syracuseStep 344387 = 516581) B516581
theorem B344417 : Blo 227813 344417 := bstep (se 2 (by rfl) ⟨129156, by rfl⟩ : syracuseStep 344417 = 258313) B258313
theorem B246115 : Blo 227813 246115 := bstep (se 1 (by rfl) ⟨184586, by rfl⟩ : syracuseStep 246115 = 369173) B369173
theorem B770417 : Blo 227813 770417 := bstep (se 2 (by rfl) ⟨288906, by rfl⟩ : syracuseStep 770417 = 577813) B577813
theorem B344435 : Blo 227813 344435 := bstep (se 1 (by rfl) ⟨258326, by rfl⟩ : syracuseStep 344435 = 516653) B516653
theorem B344465 : Blo 227813 344465 := bstep (se 2 (by rfl) ⟨129174, by rfl⟩ : syracuseStep 344465 = 258349) B258349
theorem B344483 : Blo 227813 344483 := bstep (se 1 (by rfl) ⟨258362, by rfl⟩ : syracuseStep 344483 = 516725) B516725
theorem B344513 : Blo 227813 344513 := bstep (se 2 (by rfl) ⟨129192, by rfl⟩ : syracuseStep 344513 = 258385) B258385
theorem B344531 : Blo 227813 344531 := bstep (se 1 (by rfl) ⟨258398, by rfl⟩ : syracuseStep 344531 = 516797) B516797
theorem B344561 : Blo 227813 344561 := bstep (se 2 (by rfl) ⟨129210, by rfl⟩ : syracuseStep 344561 = 258421) B258421
theorem B344579 : Blo 227813 344579 := bstep (se 1 (by rfl) ⟨258434, by rfl⟩ : syracuseStep 344579 = 516869) B516869
theorem B868877 : Blo 227813 868877 := bstep (se 3 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 868877 = 325829) B325829
theorem B344609 : Blo 227813 344609 := bstep (se 2 (by rfl) ⟨129228, by rfl⟩ : syracuseStep 344609 = 258457) B258457
theorem B344627 : Blo 227813 344627 := bstep (se 1 (by rfl) ⟨258470, by rfl⟩ : syracuseStep 344627 = 516941) B516941
theorem B344657 : Blo 227813 344657 := bstep (se 2 (by rfl) ⟨129246, by rfl⟩ : syracuseStep 344657 = 258493) B258493
theorem B344675 : Blo 227813 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B344705 : Blo 227813 344705 := bstep (se 2 (by rfl) ⟨129264, by rfl⟩ : syracuseStep 344705 = 258529) B258529
theorem B344723 : Blo 227813 344723 := bstep (se 1 (by rfl) ⟨258542, by rfl⟩ : syracuseStep 344723 = 517085) B517085
theorem B344753 : Blo 227813 344753 := bstep (se 2 (by rfl) ⟨129282, by rfl⟩ : syracuseStep 344753 = 258565) B258565
theorem B344771 : Blo 227813 344771 := bstep (se 1 (by rfl) ⟨258578, by rfl⟩ : syracuseStep 344771 = 517157) B517157
theorem B344801 : Blo 227813 344801 := bstep (se 2 (by rfl) ⟨129300, by rfl⟩ : syracuseStep 344801 = 258601) B258601
theorem B1983217 : Blo 227813 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B344819 : Blo 227813 344819 := bstep (se 1 (by rfl) ⟨258614, by rfl⟩ : syracuseStep 344819 = 517229) B517229
theorem B344849 : Blo 227813 344849 := bstep (se 2 (by rfl) ⟨129318, by rfl⟩ : syracuseStep 344849 = 258637) B258637
theorem B344867 : Blo 227813 344867 := bstep (se 1 (by rfl) ⟨258650, by rfl⟩ : syracuseStep 344867 = 517301) B517301
theorem B312113 : Blo 227813 312113 := bstep (se 2 (by rfl) ⟨117042, by rfl⟩ : syracuseStep 312113 = 234085) B234085
theorem B344897 : Blo 227813 344897 := bstep (se 2 (by rfl) ⟨129336, by rfl⟩ : syracuseStep 344897 = 258673) B258673
theorem B344915 : Blo 227813 344915 := bstep (se 1 (by rfl) ⟨258686, by rfl⟩ : syracuseStep 344915 = 517373) B517373
theorem B1164131 : Blo 227813 1164131 := bstep (se 1 (by rfl) ⟨873098, by rfl⟩ : syracuseStep 1164131 = 1746197) B1746197
theorem B344945 : Blo 227813 344945 := bstep (se 2 (by rfl) ⟨129354, by rfl⟩ : syracuseStep 344945 = 258709) B258709
theorem B344963 : Blo 227813 344963 := bstep (se 1 (by rfl) ⟨258722, by rfl⟩ : syracuseStep 344963 = 517445) B517445
theorem B770957 : Blo 227813 770957 := bstep (se 3 (by rfl) ⟨144554, by rfl⟩ : syracuseStep 770957 = 289109) B289109
theorem B1491853 : Blo 227813 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B344993 : Blo 227813 344993 := bstep (se 2 (by rfl) ⟨129372, by rfl⟩ : syracuseStep 344993 = 258745) B258745
theorem B345011 : Blo 227813 345011 := bstep (se 1 (by rfl) ⟨258758, by rfl⟩ : syracuseStep 345011 = 517517) B517517
theorem B771011 : Blo 227813 771011 := bstep (se 1 (by rfl) ⟨578258, by rfl⟩ : syracuseStep 771011 = 1156517) B1156517
theorem B345041 : Blo 227813 345041 := bstep (se 2 (by rfl) ⟨129390, by rfl⟩ : syracuseStep 345041 = 258781) B258781
theorem B345059 : Blo 227813 345059 := bstep (se 1 (by rfl) ⟨258794, by rfl⟩ : syracuseStep 345059 = 517589) B517589
theorem B3195875 : Blo 227813 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B345089 : Blo 227813 345089 := bstep (se 2 (by rfl) ⟨129408, by rfl⟩ : syracuseStep 345089 = 258817) B258817
theorem B345107 : Blo 227813 345107 := bstep (se 1 (by rfl) ⟨258830, by rfl⟩ : syracuseStep 345107 = 517661) B517661
theorem B345137 : Blo 227813 345137 := bstep (se 2 (by rfl) ⟨129426, by rfl⟩ : syracuseStep 345137 = 258853) B258853
theorem B345155 : Blo 227813 345155 := bstep (se 1 (by rfl) ⟨258866, by rfl⟩ : syracuseStep 345155 = 517733) B517733
theorem B345185 : Blo 227813 345185 := bstep (se 2 (by rfl) ⟨129444, by rfl⟩ : syracuseStep 345185 = 258889) B258889
theorem B345203 : Blo 227813 345203 := bstep (se 1 (by rfl) ⟨258902, by rfl⟩ : syracuseStep 345203 = 517805) B517805
theorem B345233 : Blo 227813 345233 := bstep (se 2 (by rfl) ⟨129462, by rfl⟩ : syracuseStep 345233 = 258925) B258925
theorem B345251 : Blo 227813 345251 := bstep (se 1 (by rfl) ⟨258938, by rfl⟩ : syracuseStep 345251 = 517877) B517877
theorem B2802869 : Blo 227813 2802869 := bstep (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) B262769
theorem B345281 : Blo 227813 345281 := bstep (se 2 (by rfl) ⟨129480, by rfl⟩ : syracuseStep 345281 = 258961) B258961
theorem B771281 : Blo 227813 771281 := bstep (se 2 (by rfl) ⟨289230, by rfl⟩ : syracuseStep 771281 = 578461) B578461
theorem B345299 : Blo 227813 345299 := bstep (se 1 (by rfl) ⟨258974, by rfl⟩ : syracuseStep 345299 = 517949) B517949
theorem B345329 : Blo 227813 345329 := bstep (se 2 (by rfl) ⟨129498, by rfl⟩ : syracuseStep 345329 = 258997) B258997
theorem B345347 : Blo 227813 345347 := bstep (se 1 (by rfl) ⟨259010, by rfl⟩ : syracuseStep 345347 = 518021) B518021
theorem B345377 : Blo 227813 345377 := bstep (se 2 (by rfl) ⟨129516, by rfl⟩ : syracuseStep 345377 = 259033) B259033
theorem B345395 : Blo 227813 345395 := bstep (se 1 (by rfl) ⟨259046, by rfl⟩ : syracuseStep 345395 = 518093) B518093
theorem B345425 : Blo 227813 345425 := bstep (se 2 (by rfl) ⟨129534, by rfl⟩ : syracuseStep 345425 = 259069) B259069
theorem B345443 : Blo 227813 345443 := bstep (se 1 (by rfl) ⟨259082, by rfl⟩ : syracuseStep 345443 = 518165) B518165
theorem B345473 : Blo 227813 345473 := bstep (se 2 (by rfl) ⟨129552, by rfl⟩ : syracuseStep 345473 = 259105) B259105
theorem B345491 : Blo 227813 345491 := bstep (se 1 (by rfl) ⟨259118, by rfl⟩ : syracuseStep 345491 = 518237) B518237
theorem B345521 : Blo 227813 345521 := bstep (se 2 (by rfl) ⟨129570, by rfl⟩ : syracuseStep 345521 = 259141) B259141
theorem B345539 : Blo 227813 345539 := bstep (se 1 (by rfl) ⟨259154, by rfl⟩ : syracuseStep 345539 = 518309) B518309
theorem B345569 : Blo 227813 345569 := bstep (se 2 (by rfl) ⟨129588, by rfl⟩ : syracuseStep 345569 = 259177) B259177
theorem B345587 : Blo 227813 345587 := bstep (se 1 (by rfl) ⟨259190, by rfl⟩ : syracuseStep 345587 = 518381) B518381
theorem B345617 : Blo 227813 345617 := bstep (se 2 (by rfl) ⟨129606, by rfl⟩ : syracuseStep 345617 = 259213) B259213
theorem B345635 : Blo 227813 345635 := bstep (se 1 (by rfl) ⟨259226, by rfl⟩ : syracuseStep 345635 = 518453) B518453
theorem B345665 : Blo 227813 345665 := bstep (se 2 (by rfl) ⟨129624, by rfl⟩ : syracuseStep 345665 = 259249) B259249
theorem B345683 : Blo 227813 345683 := bstep (se 1 (by rfl) ⟨259262, by rfl⟩ : syracuseStep 345683 = 518525) B518525
theorem B247379 : Blo 227813 247379 := bstep (se 1 (by rfl) ⟨185534, by rfl⟩ : syracuseStep 247379 = 371069) B371069
theorem B345713 : Blo 227813 345713 := bstep (se 2 (by rfl) ⟨129642, by rfl⟩ : syracuseStep 345713 = 259285) B259285
theorem B345731 : Blo 227813 345731 := bstep (se 1 (by rfl) ⟨259298, by rfl⟩ : syracuseStep 345731 = 518597) B518597
theorem B1164941 : Blo 227813 1164941 := bstep (se 3 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 1164941 = 436853) B436853
theorem B345761 : Blo 227813 345761 := bstep (se 2 (by rfl) ⟨129660, by rfl⟩ : syracuseStep 345761 = 259321) B259321
theorem B345779 : Blo 227813 345779 := bstep (se 1 (by rfl) ⟨259334, by rfl⟩ : syracuseStep 345779 = 518669) B518669
theorem B345809 : Blo 227813 345809 := bstep (se 2 (by rfl) ⟨129678, by rfl⟩ : syracuseStep 345809 = 259357) B259357
theorem B345827 : Blo 227813 345827 := bstep (se 1 (by rfl) ⟨259370, by rfl⟩ : syracuseStep 345827 = 518741) B518741
theorem B771821 : Blo 227813 771821 := bstep (se 3 (by rfl) ⟨144716, by rfl⟩ : syracuseStep 771821 = 289433) B289433
theorem B345857 : Blo 227813 345857 := bstep (se 2 (by rfl) ⟨129696, by rfl⟩ : syracuseStep 345857 = 259393) B259393
theorem B345875 : Blo 227813 345875 := bstep (se 1 (by rfl) ⟨259406, by rfl⟩ : syracuseStep 345875 = 518813) B518813
theorem B771875 : Blo 227813 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B345905 : Blo 227813 345905 := bstep (se 2 (by rfl) ⟨129714, by rfl⟩ : syracuseStep 345905 = 259429) B259429
theorem B345923 : Blo 227813 345923 := bstep (se 1 (by rfl) ⟨259442, by rfl⟩ : syracuseStep 345923 = 518885) B518885
theorem B345953 : Blo 227813 345953 := bstep (se 2 (by rfl) ⟨129732, by rfl⟩ : syracuseStep 345953 = 259465) B259465
theorem B345971 : Blo 227813 345971 := bstep (se 1 (by rfl) ⟨259478, by rfl⟩ : syracuseStep 345971 = 518957) B518957
theorem B346001 : Blo 227813 346001 := bstep (se 2 (by rfl) ⟨129750, by rfl⟩ : syracuseStep 346001 = 259501) B259501
theorem B346019 : Blo 227813 346019 := bstep (se 1 (by rfl) ⟨259514, by rfl⟩ : syracuseStep 346019 = 519029) B519029
theorem B346049 : Blo 227813 346049 := bstep (se 2 (by rfl) ⟨129768, by rfl⟩ : syracuseStep 346049 = 259537) B259537
theorem B346067 : Blo 227813 346067 := bstep (se 1 (by rfl) ⟨259550, by rfl⟩ : syracuseStep 346067 = 519101) B519101
theorem B346097 : Blo 227813 346097 := bstep (se 2 (by rfl) ⟨129786, by rfl⟩ : syracuseStep 346097 = 259573) B259573
theorem B346115 : Blo 227813 346115 := bstep (se 1 (by rfl) ⟨259586, by rfl⟩ : syracuseStep 346115 = 519173) B519173
theorem B346145 : Blo 227813 346145 := bstep (se 2 (by rfl) ⟨129804, by rfl⟩ : syracuseStep 346145 = 259609) B259609
theorem B772145 : Blo 227813 772145 := bstep (se 2 (by rfl) ⟨289554, by rfl⟩ : syracuseStep 772145 = 579109) B579109
theorem B346163 : Blo 227813 346163 := bstep (se 1 (by rfl) ⟨259622, by rfl⟩ : syracuseStep 346163 = 519245) B519245
theorem B346193 : Blo 227813 346193 := bstep (se 2 (by rfl) ⟨129822, by rfl⟩ : syracuseStep 346193 = 259645) B259645
theorem B346211 : Blo 227813 346211 := bstep (se 1 (by rfl) ⟨259658, by rfl⟩ : syracuseStep 346211 = 519317) B519317
theorem B346241 : Blo 227813 346241 := bstep (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) B259681
theorem B346259 : Blo 227813 346259 := bstep (se 1 (by rfl) ⟨259694, by rfl⟩ : syracuseStep 346259 = 519389) B519389
theorem B346289 : Blo 227813 346289 := bstep (se 2 (by rfl) ⟨129858, by rfl⟩ : syracuseStep 346289 = 259717) B259717
theorem B346307 : Blo 227813 346307 := bstep (se 1 (by rfl) ⟨259730, by rfl⟩ : syracuseStep 346307 = 519461) B519461
theorem B346337 : Blo 227813 346337 := bstep (se 2 (by rfl) ⟨129876, by rfl⟩ : syracuseStep 346337 = 259753) B259753
theorem B1755377 : Blo 227813 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B346355 : Blo 227813 346355 := bstep (se 1 (by rfl) ⟨259766, by rfl⟩ : syracuseStep 346355 = 519533) B519533
theorem B739601 : Blo 227813 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B346385 : Blo 227813 346385 := bstep (se 2 (by rfl) ⟨129894, by rfl⟩ : syracuseStep 346385 = 259789) B259789
theorem B346403 : Blo 227813 346403 := bstep (se 1 (by rfl) ⟨259802, by rfl⟩ : syracuseStep 346403 = 519605) B519605
theorem B346433 : Blo 227813 346433 := bstep (se 2 (by rfl) ⟨129912, by rfl⟩ : syracuseStep 346433 = 259825) B259825
theorem B739651 : Blo 227813 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B346451 : Blo 227813 346451 := bstep (se 1 (by rfl) ⟨259838, by rfl⟩ : syracuseStep 346451 = 519677) B519677
theorem B346481 : Blo 227813 346481 := bstep (se 2 (by rfl) ⟨129930, by rfl⟩ : syracuseStep 346481 = 259861) B259861
theorem B346499 : Blo 227813 346499 := bstep (se 1 (by rfl) ⟨259874, by rfl⟩ : syracuseStep 346499 = 519749) B519749
theorem B346529 : Blo 227813 346529 := bstep (se 2 (by rfl) ⟨129948, by rfl⟩ : syracuseStep 346529 = 259897) B259897
theorem B346547 : Blo 227813 346547 := bstep (se 1 (by rfl) ⟨259910, by rfl⟩ : syracuseStep 346547 = 519821) B519821
theorem B346577 : Blo 227813 346577 := bstep (se 2 (by rfl) ⟨129966, by rfl⟩ : syracuseStep 346577 = 259933) B259933
theorem B346595 : Blo 227813 346595 := bstep (se 1 (by rfl) ⟨259946, by rfl⟩ : syracuseStep 346595 = 519893) B519893
theorem B510449 : Blo 227813 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B346625 : Blo 227813 346625 := bstep (se 2 (by rfl) ⟨129984, by rfl⟩ : syracuseStep 346625 = 259969) B259969
theorem B346643 : Blo 227813 346643 := bstep (se 1 (by rfl) ⟨259982, by rfl⟩ : syracuseStep 346643 = 519965) B519965
theorem B346673 : Blo 227813 346673 := bstep (se 2 (by rfl) ⟨130002, by rfl⟩ : syracuseStep 346673 = 260005) B260005
theorem B2640437 : Blo 227813 2640437 := bstep (se 5 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 2640437 = 247541) B247541
theorem B346691 : Blo 227813 346691 := bstep (se 1 (by rfl) ⟨260018, by rfl⟩ : syracuseStep 346691 = 520037) B520037
theorem B772685 : Blo 227813 772685 := bstep (se 3 (by rfl) ⟨144878, by rfl⟩ : syracuseStep 772685 = 289757) B289757
theorem B346721 : Blo 227813 346721 := bstep (se 2 (by rfl) ⟨130020, by rfl⟩ : syracuseStep 346721 = 260041) B260041
theorem B346739 : Blo 227813 346739 := bstep (se 1 (by rfl) ⟨260054, by rfl⟩ : syracuseStep 346739 = 520109) B520109
theorem B772739 : Blo 227813 772739 := bstep (se 1 (by rfl) ⟨579554, by rfl⟩ : syracuseStep 772739 = 1159109) B1159109
theorem B346769 : Blo 227813 346769 := bstep (se 2 (by rfl) ⟨130038, by rfl⟩ : syracuseStep 346769 = 260077) B260077
theorem B346787 : Blo 227813 346787 := bstep (se 1 (by rfl) ⟨260090, by rfl⟩ : syracuseStep 346787 = 520181) B520181
theorem B346817 : Blo 227813 346817 := bstep (se 2 (by rfl) ⟨130056, by rfl⟩ : syracuseStep 346817 = 260113) B260113
theorem B346835 : Blo 227813 346835 := bstep (se 1 (by rfl) ⟨260126, by rfl⟩ : syracuseStep 346835 = 520253) B520253
theorem B1395427 : Blo 227813 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B346865 : Blo 227813 346865 := bstep (se 2 (by rfl) ⟨130074, by rfl⟩ : syracuseStep 346865 = 260149) B260149
theorem B346883 : Blo 227813 346883 := bstep (se 1 (by rfl) ⟨260162, by rfl⟩ : syracuseStep 346883 = 520325) B520325
theorem B1100557 : Blo 227813 1100557 := bstep (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) B412709
theorem B1755917 : Blo 227813 1755917 := bstep (se 3 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 1755917 = 658469) B658469
theorem B346913 : Blo 227813 346913 := bstep (se 2 (by rfl) ⟨130092, by rfl⟩ : syracuseStep 346913 = 260185) B260185
theorem B346931 : Blo 227813 346931 := bstep (se 1 (by rfl) ⟨260198, by rfl⟩ : syracuseStep 346931 = 520397) B520397
theorem B346961 : Blo 227813 346961 := bstep (se 2 (by rfl) ⟨130110, by rfl⟩ : syracuseStep 346961 = 260221) B260221
theorem B346979 : Blo 227813 346979 := bstep (se 1 (by rfl) ⟨260234, by rfl⟩ : syracuseStep 346979 = 520469) B520469
theorem B347009 : Blo 227813 347009 := bstep (se 2 (by rfl) ⟨130128, by rfl⟩ : syracuseStep 347009 = 260257) B260257
theorem B773009 : Blo 227813 773009 := bstep (se 2 (by rfl) ⟨289878, by rfl⟩ : syracuseStep 773009 = 579757) B579757
theorem B347027 : Blo 227813 347027 := bstep (se 1 (by rfl) ⟨260270, by rfl⟩ : syracuseStep 347027 = 520541) B520541
theorem B347057 : Blo 227813 347057 := bstep (se 2 (by rfl) ⟨130146, by rfl⟩ : syracuseStep 347057 = 260293) B260293
theorem B281539 : Blo 227813 281539 := bstep (se 1 (by rfl) ⟨211154, by rfl⟩ : syracuseStep 281539 = 422309) B422309
theorem B347075 : Blo 227813 347075 := bstep (se 1 (by rfl) ⟨260306, by rfl⟩ : syracuseStep 347075 = 520613) B520613
theorem B347105 : Blo 227813 347105 := bstep (se 2 (by rfl) ⟨130164, by rfl⟩ : syracuseStep 347105 = 260329) B260329
theorem B347123 : Blo 227813 347123 := bstep (se 1 (by rfl) ⟨260342, by rfl⟩ : syracuseStep 347123 = 520685) B520685
theorem B347153 : Blo 227813 347153 := bstep (se 2 (by rfl) ⟨130182, by rfl⟩ : syracuseStep 347153 = 260365) B260365
theorem B347171 : Blo 227813 347171 := bstep (se 1 (by rfl) ⟨260378, by rfl⟩ : syracuseStep 347171 = 520757) B520757
theorem B347201 : Blo 227813 347201 := bstep (se 2 (by rfl) ⟨130200, by rfl⟩ : syracuseStep 347201 = 260401) B260401
theorem B347219 : Blo 227813 347219 := bstep (se 1 (by rfl) ⟨260414, by rfl⟩ : syracuseStep 347219 = 520829) B520829
theorem B1461361 : Blo 227813 1461361 := bstep (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) B1096021
theorem B347249 : Blo 227813 347249 := bstep (se 2 (by rfl) ⟨130218, by rfl⟩ : syracuseStep 347249 = 260437) B260437
theorem B347267 : Blo 227813 347267 := bstep (se 1 (by rfl) ⟨260450, by rfl⟩ : syracuseStep 347267 = 520901) B520901
theorem B740497 : Blo 227813 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B347297 : Blo 227813 347297 := bstep (se 2 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 347297 = 260473) B260473
theorem B347315 : Blo 227813 347315 := bstep (se 1 (by rfl) ⟨260486, by rfl⟩ : syracuseStep 347315 = 520973) B520973
theorem B347345 : Blo 227813 347345 := bstep (se 2 (by rfl) ⟨130254, by rfl⟩ : syracuseStep 347345 = 260509) B260509
theorem B347363 : Blo 227813 347363 := bstep (se 1 (by rfl) ⟨260522, by rfl⟩ : syracuseStep 347363 = 521045) B521045
theorem B347393 : Blo 227813 347393 := bstep (se 2 (by rfl) ⟨130272, by rfl⟩ : syracuseStep 347393 = 260545) B260545
theorem B347411 : Blo 227813 347411 := bstep (se 1 (by rfl) ⟨260558, by rfl⟩ : syracuseStep 347411 = 521117) B521117
theorem B347441 : Blo 227813 347441 := bstep (se 2 (by rfl) ⟨130290, by rfl⟩ : syracuseStep 347441 = 260581) B260581
theorem B347459 : Blo 227813 347459 := bstep (se 1 (by rfl) ⟨260594, by rfl⟩ : syracuseStep 347459 = 521189) B521189
theorem B347489 : Blo 227813 347489 := bstep (se 2 (by rfl) ⟨130308, by rfl⟩ : syracuseStep 347489 = 260617) B260617
theorem B871793 : Blo 227813 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B347507 : Blo 227813 347507 := bstep (se 1 (by rfl) ⟨260630, by rfl⟩ : syracuseStep 347507 = 521261) B521261
theorem B347537 : Blo 227813 347537 := bstep (se 2 (by rfl) ⟨130326, by rfl⟩ : syracuseStep 347537 = 260653) B260653
theorem B347555 : Blo 227813 347555 := bstep (se 1 (by rfl) ⟨260666, by rfl⟩ : syracuseStep 347555 = 521333) B521333
theorem B773549 : Blo 227813 773549 := bstep (se 3 (by rfl) ⟨145040, by rfl⟩ : syracuseStep 773549 = 290081) B290081
theorem B347585 : Blo 227813 347585 := bstep (se 2 (by rfl) ⟨130344, by rfl⟩ : syracuseStep 347585 = 260689) B260689
theorem B347603 : Blo 227813 347603 := bstep (se 1 (by rfl) ⟨260702, by rfl⟩ : syracuseStep 347603 = 521405) B521405
theorem B773603 : Blo 227813 773603 := bstep (se 1 (by rfl) ⟨580202, by rfl⟩ : syracuseStep 773603 = 1160405) B1160405
theorem B347633 : Blo 227813 347633 := bstep (se 2 (by rfl) ⟨130362, by rfl⟩ : syracuseStep 347633 = 260725) B260725
theorem B347651 : Blo 227813 347651 := bstep (se 1 (by rfl) ⟨260738, by rfl⟩ : syracuseStep 347651 = 521477) B521477
theorem B347681 : Blo 227813 347681 := bstep (se 2 (by rfl) ⟨130380, by rfl⟩ : syracuseStep 347681 = 260761) B260761
theorem B347699 : Blo 227813 347699 := bstep (se 1 (by rfl) ⟨260774, by rfl⟩ : syracuseStep 347699 = 521549) B521549
theorem B773873 : Blo 227813 773873 := bstep (se 2 (by rfl) ⟨290202, by rfl⟩ : syracuseStep 773873 = 580405) B580405
theorem B577489 : Blo 227813 577489 := bstep (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) B433117
theorem B1298531 : Blo 227813 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B577763 : Blo 227813 577763 := bstep (se 1 (by rfl) ⟨433322, by rfl⟩ : syracuseStep 577763 = 866645) B866645
theorem B774413 : Blo 227813 774413 := bstep (se 3 (by rfl) ⟨145202, by rfl⟩ : syracuseStep 774413 = 290405) B290405
theorem B1331491 : Blo 227813 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B774467 : Blo 227813 774467 := bstep (se 1 (by rfl) ⟨580850, by rfl⟩ : syracuseStep 774467 = 1161701) B1161701
theorem B577955 : Blo 227813 577955 := bstep (se 1 (by rfl) ⟨433466, by rfl⟩ : syracuseStep 577955 = 866933) B866933
theorem B1167857 : Blo 227813 1167857 := bstep (se 2 (by rfl) ⟨437946, by rfl⟩ : syracuseStep 1167857 = 875893) B875893
theorem B1102385 : Blo 227813 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B774737 : Blo 227813 774737 := bstep (se 2 (by rfl) ⟨290526, by rfl⟩ : syracuseStep 774737 = 581053) B581053
theorem B512657 : Blo 227813 512657 := bstep (se 2 (by rfl) ⟨192246, by rfl⟩ : syracuseStep 512657 = 384493) B384493
theorem B414353 : Blo 227813 414353 := bstep (se 2 (by rfl) ⟨155382, by rfl⟩ : syracuseStep 414353 = 310765) B310765
theorem B348833 : Blo 227813 348833 := bstep (se 2 (by rfl) ⟨130812, by rfl⟩ : syracuseStep 348833 = 261625) B261625
theorem B512675 : Blo 227813 512675 := bstep (se 1 (by rfl) ⟨384506, by rfl⟩ : syracuseStep 512675 = 769013) B769013
theorem B742061 : Blo 227813 742061 := bstep (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) B278273
theorem B348929 : Blo 227813 348929 := bstep (se 2 (by rfl) ⟨130848, by rfl⟩ : syracuseStep 348929 = 261697) B261697
theorem B873251 : Blo 227813 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B512945 : Blo 227813 512945 := bstep (se 2 (by rfl) ⟨192354, by rfl⟩ : syracuseStep 512945 = 384709) B384709
theorem B512963 : Blo 227813 512963 := bstep (se 1 (by rfl) ⟨384722, by rfl⟩ : syracuseStep 512963 = 769445) B769445
theorem B1463309 : Blo 227813 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B775277 : Blo 227813 775277 := bstep (se 3 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 775277 = 290729) B290729
theorem B775331 : Blo 227813 775331 := bstep (se 1 (by rfl) ⟨581498, by rfl⟩ : syracuseStep 775331 = 1162997) B1162997
theorem B513233 : Blo 227813 513233 := bstep (se 2 (by rfl) ⟨192462, by rfl⟩ : syracuseStep 513233 = 384925) B384925
theorem B513251 : Blo 227813 513251 := bstep (se 1 (by rfl) ⟨384938, by rfl⟩ : syracuseStep 513251 = 769877) B769877
theorem B578897 : Blo 227813 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B349537 : Blo 227813 349537 := bstep (se 2 (by rfl) ⟨131076, by rfl⟩ : syracuseStep 349537 = 262153) B262153
theorem B578947 : Blo 227813 578947 := bstep (se 1 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 578947 = 868421) B868421
theorem B775601 : Blo 227813 775601 := bstep (se 2 (by rfl) ⟨290850, by rfl⟩ : syracuseStep 775601 = 581701) B581701
theorem B513521 : Blo 227813 513521 := bstep (se 2 (by rfl) ⟨192570, by rfl⟩ : syracuseStep 513521 = 385141) B385141
theorem B316913 : Blo 227813 316913 := bstep (se 2 (by rfl) ⟨118842, by rfl⟩ : syracuseStep 316913 = 237685) B237685
theorem B513539 : Blo 227813 513539 := bstep (se 1 (by rfl) ⟨385154, by rfl⟩ : syracuseStep 513539 = 770309) B770309
theorem B579089 : Blo 227813 579089 := bstep (se 2 (by rfl) ⟨217158, by rfl⟩ : syracuseStep 579089 = 434317) B434317
theorem B1758833 : Blo 227813 1758833 := bstep (se 2 (by rfl) ⟨659562, by rfl⟩ : syracuseStep 1758833 = 1319125) B1319125
theorem B874253 : Blo 227813 874253 := bstep (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) B327845
theorem B513809 : Blo 227813 513809 := bstep (se 2 (by rfl) ⟨192678, by rfl⟩ : syracuseStep 513809 = 385357) B385357
theorem B513827 : Blo 227813 513827 := bstep (se 1 (by rfl) ⟨385370, by rfl⟩ : syracuseStep 513827 = 770741) B770741
theorem B1169315 : Blo 227813 1169315 := bstep (se 1 (by rfl) ⟨876986, by rfl⟩ : syracuseStep 1169315 = 1753973) B1753973
theorem B776141 : Blo 227813 776141 := bstep (se 3 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 776141 = 291053) B291053
theorem B776195 : Blo 227813 776195 := bstep (se 1 (by rfl) ⟨582146, by rfl⟩ : syracuseStep 776195 = 1164293) B1164293
theorem B514097 : Blo 227813 514097 := bstep (se 2 (by rfl) ⟨192786, by rfl⟩ : syracuseStep 514097 = 385573) B385573
theorem B514115 : Blo 227813 514115 := bstep (se 1 (by rfl) ⟨385586, by rfl⟩ : syracuseStep 514115 = 771173) B771173
theorem B3528845 : Blo 227813 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B776465 : Blo 227813 776465 := bstep (se 2 (by rfl) ⟨291174, by rfl⟩ : syracuseStep 776465 = 582349) B582349
theorem B514385 : Blo 227813 514385 := bstep (se 2 (by rfl) ⟨192894, by rfl⟩ : syracuseStep 514385 = 385789) B385789
theorem B514403 : Blo 227813 514403 := bstep (se 1 (by rfl) ⟨385802, by rfl⟩ : syracuseStep 514403 = 771605) B771605
theorem B1235405 : Blo 227813 1235405 := bstep (se 3 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 1235405 = 463277) B463277
theorem B580081 : Blo 227813 580081 := bstep (se 2 (by rfl) ⟨217530, by rfl⟩ : syracuseStep 580081 = 435061) B435061
theorem B1235533 : Blo 227813 1235533 := bstep (se 3 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 1235533 = 463325) B463325
theorem B514673 : Blo 227813 514673 := bstep (se 2 (by rfl) ⟨193002, by rfl⟩ : syracuseStep 514673 = 386005) B386005
theorem B514691 : Blo 227813 514691 := bstep (se 1 (by rfl) ⟨386018, by rfl⟩ : syracuseStep 514691 = 772037) B772037
theorem B1170125 : Blo 227813 1170125 := bstep (se 3 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 1170125 = 438797) B438797
theorem B580355 : Blo 227813 580355 := bstep (se 1 (by rfl) ⟨435266, by rfl⟩ : syracuseStep 580355 = 870533) B870533
theorem B777005 : Blo 227813 777005 := bstep (se 3 (by rfl) ⟨145688, by rfl⟩ : syracuseStep 777005 = 291377) B291377
theorem B351059 : Blo 227813 351059 := bstep (se 1 (by rfl) ⟨263294, by rfl⟩ : syracuseStep 351059 = 526589) B526589
theorem B777059 : Blo 227813 777059 := bstep (se 1 (by rfl) ⟨582794, by rfl⟩ : syracuseStep 777059 = 1165589) B1165589
theorem B514961 : Blo 227813 514961 := bstep (se 2 (by rfl) ⟨193110, by rfl⟩ : syracuseStep 514961 = 386221) B386221
theorem B514979 : Blo 227813 514979 := bstep (se 1 (by rfl) ⟨386234, by rfl⟩ : syracuseStep 514979 = 772469) B772469
theorem B580547 : Blo 227813 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B777329 : Blo 227813 777329 := bstep (se 2 (by rfl) ⟨291498, by rfl⟩ : syracuseStep 777329 = 582997) B582997
theorem B515249 : Blo 227813 515249 := bstep (se 2 (by rfl) ⟨193218, by rfl⟩ : syracuseStep 515249 = 386437) B386437
theorem B515267 : Blo 227813 515267 := bstep (se 1 (by rfl) ⟨386450, by rfl⟩ : syracuseStep 515267 = 772901) B772901
theorem B482737 : Blo 227813 482737 := bstep (se 2 (by rfl) ⟨181026, by rfl⟩ : syracuseStep 482737 = 362053) B362053
theorem B515537 : Blo 227813 515537 := bstep (se 2 (by rfl) ⟨193326, by rfl⟩ : syracuseStep 515537 = 386653) B386653
theorem B515555 : Blo 227813 515555 := bstep (se 1 (by rfl) ⟨386666, by rfl⟩ : syracuseStep 515555 = 773333) B773333
theorem B384547 : Blo 227813 384547 := bstep (se 1 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 384547 = 576821) B576821
theorem B1039985 : Blo 227813 1039985 := bstep (se 2 (by rfl) ⟨389994, by rfl⟩ : syracuseStep 1039985 = 779989) B779989
theorem B777869 : Blo 227813 777869 := bstep (se 3 (by rfl) ⟨145850, by rfl⟩ : syracuseStep 777869 = 291701) B291701
theorem B384689 : Blo 227813 384689 := bstep (se 2 (by rfl) ⟨144258, by rfl⟩ : syracuseStep 384689 = 288517) B288517
theorem B777923 : Blo 227813 777923 := bstep (se 1 (by rfl) ⟨583442, by rfl⟩ : syracuseStep 777923 = 1166885) B1166885
theorem B515825 : Blo 227813 515825 := bstep (se 2 (by rfl) ⟨193434, by rfl⟩ : syracuseStep 515825 = 386869) B386869
theorem B515843 : Blo 227813 515843 := bstep (se 1 (by rfl) ⟨386882, by rfl⟩ : syracuseStep 515843 = 773765) B773765
theorem B384817 : Blo 227813 384817 := bstep (se 2 (by rfl) ⟨144306, by rfl⟩ : syracuseStep 384817 = 288613) B288613
theorem B548657 : Blo 227813 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B876365 : Blo 227813 876365 := bstep (se 3 (by rfl) ⟨164318, by rfl⟩ : syracuseStep 876365 = 328637) B328637
theorem B384851 : Blo 227813 384851 := bstep (se 1 (by rfl) ⟨288638, by rfl⟩ : syracuseStep 384851 = 577277) B577277
theorem B581489 : Blo 227813 581489 := bstep (se 2 (by rfl) ⟨218058, by rfl⟩ : syracuseStep 581489 = 436117) B436117
theorem B352129 : Blo 227813 352129 := bstep (se 2 (by rfl) ⟨132048, by rfl⟩ : syracuseStep 352129 = 264097) B264097
theorem B745379 : Blo 227813 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B581539 : Blo 227813 581539 := bstep (se 1 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 581539 = 872309) B872309
theorem B778193 : Blo 227813 778193 := bstep (se 2 (by rfl) ⟨291822, by rfl⟩ : syracuseStep 778193 = 583645) B583645
theorem B384979 : Blo 227813 384979 := bstep (se 1 (by rfl) ⟨288734, by rfl⟩ : syracuseStep 384979 = 577469) B577469
theorem B516113 : Blo 227813 516113 := bstep (se 2 (by rfl) ⟨193542, by rfl⟩ : syracuseStep 516113 = 387085) B387085
theorem B516131 : Blo 227813 516131 := bstep (se 1 (by rfl) ⟨387098, by rfl⟩ : syracuseStep 516131 = 774197) B774197
theorem B581681 : Blo 227813 581681 := bstep (se 2 (by rfl) ⟨218130, by rfl⟩ : syracuseStep 581681 = 436261) B436261
theorem B385121 : Blo 227813 385121 := bstep (se 2 (by rfl) ⟨144420, by rfl⟩ : syracuseStep 385121 = 288841) B288841
theorem B385249 : Blo 227813 385249 := bstep (se 2 (by rfl) ⟨144468, by rfl⟩ : syracuseStep 385249 = 288937) B288937
theorem B385283 : Blo 227813 385283 := bstep (se 1 (by rfl) ⟨288962, by rfl⟩ : syracuseStep 385283 = 577925) B577925
theorem B516401 : Blo 227813 516401 := bstep (se 2 (by rfl) ⟨193650, by rfl⟩ : syracuseStep 516401 = 387301) B387301
theorem B516419 : Blo 227813 516419 := bstep (se 1 (by rfl) ⟨387314, by rfl⟩ : syracuseStep 516419 = 774629) B774629
theorem B1466693 : Blo 227813 1466693 := bstep (se 4 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 1466693 = 275005) B275005
theorem B385411 : Blo 227813 385411 := bstep (se 1 (by rfl) ⟨289058, by rfl⟩ : syracuseStep 385411 = 578117) B578117
theorem B549347 : Blo 227813 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B778733 : Blo 227813 778733 := bstep (se 3 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 778733 = 292025) B292025
theorem B385553 : Blo 227813 385553 := bstep (se 2 (by rfl) ⟨144582, by rfl⟩ : syracuseStep 385553 = 289165) B289165
theorem B778787 : Blo 227813 778787 := bstep (se 1 (by rfl) ⟨584090, by rfl⟩ : syracuseStep 778787 = 1168181) B1168181
theorem B516689 : Blo 227813 516689 := bstep (se 2 (by rfl) ⟨193758, by rfl⟩ : syracuseStep 516689 = 387517) B387517
theorem B516707 : Blo 227813 516707 := bstep (se 1 (by rfl) ⟨387530, by rfl⟩ : syracuseStep 516707 = 775061) B775061
theorem B1401457 : Blo 227813 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B877169 : Blo 227813 877169 := bstep (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) B657877
theorem B385681 : Blo 227813 385681 := bstep (se 2 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 385681 = 289261) B289261
theorem B975523 : Blo 227813 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B385715 : Blo 227813 385715 := bstep (se 1 (by rfl) ⟨289286, by rfl⟩ : syracuseStep 385715 = 578573) B578573
theorem B779057 : Blo 227813 779057 := bstep (se 2 (by rfl) ⟨292146, by rfl⟩ : syracuseStep 779057 = 584293) B584293
theorem B385843 : Blo 227813 385843 := bstep (se 1 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 385843 = 578765) B578765
theorem B516977 : Blo 227813 516977 := bstep (se 2 (by rfl) ⟨193866, by rfl⟩ : syracuseStep 516977 = 387733) B387733
theorem B1991537 : Blo 227813 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B516995 : Blo 227813 516995 := bstep (se 1 (by rfl) ⟨387746, by rfl⟩ : syracuseStep 516995 = 775493) B775493
theorem B385985 : Blo 227813 385985 := bstep (se 2 (by rfl) ⟨144744, by rfl⟩ : syracuseStep 385985 = 289489) B289489
theorem B1172465 : Blo 227813 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B582673 : Blo 227813 582673 := bstep (se 2 (by rfl) ⟨218502, by rfl⟩ : syracuseStep 582673 = 437005) B437005
theorem B386113 : Blo 227813 386113 := bstep (se 2 (by rfl) ⟨144792, by rfl⟩ : syracuseStep 386113 = 289585) B289585
theorem B386147 : Blo 227813 386147 := bstep (se 1 (by rfl) ⟨289610, by rfl⟩ : syracuseStep 386147 = 579221) B579221
theorem B517265 : Blo 227813 517265 := bstep (se 2 (by rfl) ⟨193974, by rfl⟩ : syracuseStep 517265 = 387949) B387949
theorem B517283 : Blo 227813 517283 := bstep (se 1 (by rfl) ⟨387962, by rfl⟩ : syracuseStep 517283 = 775925) B775925
theorem B386275 : Blo 227813 386275 := bstep (se 1 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 386275 = 579413) B579413
theorem B877837 : Blo 227813 877837 := bstep (se 3 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 877837 = 329189) B329189
theorem B582947 : Blo 227813 582947 := bstep (se 1 (by rfl) ⟨437210, by rfl⟩ : syracuseStep 582947 = 874421) B874421
theorem B779597 : Blo 227813 779597 := bstep (se 3 (by rfl) ⟨146174, by rfl⟩ : syracuseStep 779597 = 292349) B292349
theorem B386417 : Blo 227813 386417 := bstep (se 2 (by rfl) ⟨144906, by rfl⟩ : syracuseStep 386417 = 289813) B289813
theorem B779651 : Blo 227813 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B517553 : Blo 227813 517553 := bstep (se 2 (by rfl) ⟨194082, by rfl⟩ : syracuseStep 517553 = 388165) B388165
theorem B517571 : Blo 227813 517571 := bstep (se 1 (by rfl) ⟨388178, by rfl⟩ : syracuseStep 517571 = 776357) B776357
theorem B2942405 : Blo 227813 2942405 := bstep (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) B551701
theorem B583139 : Blo 227813 583139 := bstep (se 1 (by rfl) ⟨437354, by rfl⟩ : syracuseStep 583139 = 874709) B874709
theorem B386545 : Blo 227813 386545 := bstep (se 2 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 386545 = 289909) B289909
theorem B386579 : Blo 227813 386579 := bstep (se 1 (by rfl) ⟨289934, by rfl⟩ : syracuseStep 386579 = 579869) B579869
theorem B1173041 : Blo 227813 1173041 := bstep (se 2 (by rfl) ⟨439890, by rfl⟩ : syracuseStep 1173041 = 879781) B879781
theorem B288355 : Blo 227813 288355 := bstep (se 1 (by rfl) ⟨216266, by rfl⟩ : syracuseStep 288355 = 432533) B432533
theorem B779921 : Blo 227813 779921 := bstep (se 2 (by rfl) ⟨292470, by rfl⟩ : syracuseStep 779921 = 584941) B584941
theorem B386707 : Blo 227813 386707 := bstep (se 1 (by rfl) ⟨290030, by rfl⟩ : syracuseStep 386707 = 580061) B580061
theorem B288451 : Blo 227813 288451 := bstep (se 1 (by rfl) ⟨216338, by rfl⟩ : syracuseStep 288451 = 432677) B432677
theorem B3958469 : Blo 227813 3958469 := bstep (se 4 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 3958469 = 742213) B742213
theorem B517841 : Blo 227813 517841 := bstep (se 2 (by rfl) ⟨194190, by rfl⟩ : syracuseStep 517841 = 388381) B388381
theorem B517859 : Blo 227813 517859 := bstep (se 1 (by rfl) ⟨388394, by rfl⟩ : syracuseStep 517859 = 776789) B776789
theorem B386849 : Blo 227813 386849 := bstep (se 2 (by rfl) ⟨145068, by rfl⟩ : syracuseStep 386849 = 290137) B290137
theorem B649073 : Blo 227813 649073 := bstep (se 2 (by rfl) ⟨243402, by rfl⟩ : syracuseStep 649073 = 486805) B486805
theorem B386977 : Blo 227813 386977 := bstep (se 2 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 386977 = 290233) B290233
theorem B387011 : Blo 227813 387011 := bstep (se 1 (by rfl) ⟨290258, by rfl⟩ : syracuseStep 387011 = 580517) B580517
theorem B518129 : Blo 227813 518129 := bstep (se 2 (by rfl) ⟨194298, by rfl⟩ : syracuseStep 518129 = 388597) B388597
theorem B518147 : Blo 227813 518147 := bstep (se 1 (by rfl) ⟨388610, by rfl⟩ : syracuseStep 518147 = 777221) B777221
theorem B878627 : Blo 227813 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B387139 : Blo 227813 387139 := bstep (se 1 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 387139 = 580709) B580709
theorem B616547 : Blo 227813 616547 := bstep (se 1 (by rfl) ⟨462410, by rfl⟩ : syracuseStep 616547 = 924821) B924821
theorem B780461 : Blo 227813 780461 := bstep (se 3 (by rfl) ⟨146336, by rfl⟩ : syracuseStep 780461 = 292673) B292673
theorem B288947 : Blo 227813 288947 := bstep (se 1 (by rfl) ⟨216710, by rfl⟩ : syracuseStep 288947 = 433421) B433421
theorem B616643 : Blo 227813 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B387281 : Blo 227813 387281 := bstep (se 2 (by rfl) ⟨145230, by rfl⟩ : syracuseStep 387281 = 290461) B290461
theorem B25389283 : Blo 227813 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B780515 : Blo 227813 780515 := bstep (se 1 (by rfl) ⟨585386, by rfl⟩ : syracuseStep 780515 = 1170773) B1170773
theorem B518417 : Blo 227813 518417 := bstep (se 2 (by rfl) ⟨194406, by rfl⟩ : syracuseStep 518417 = 388813) B388813
theorem B518435 : Blo 227813 518435 := bstep (se 1 (by rfl) ⟨388826, by rfl⟩ : syracuseStep 518435 = 777653) B777653
theorem B387409 : Blo 227813 387409 := bstep (se 2 (by rfl) ⟨145278, by rfl⟩ : syracuseStep 387409 = 290557) B290557
theorem B2615651 : Blo 227813 2615651 := bstep (se 1 (by rfl) ⟨1961738, by rfl⟩ : syracuseStep 2615651 = 3923477) B3923477
theorem B387443 : Blo 227813 387443 := bstep (se 1 (by rfl) ⟨290582, by rfl⟩ : syracuseStep 387443 = 581165) B581165
theorem B256387 : Blo 227813 256387 := bstep (se 1 (by rfl) ⟨192290, by rfl⟩ : syracuseStep 256387 = 384581) B384581
theorem B551299 : Blo 227813 551299 := bstep (se 1 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 551299 = 826949) B826949
theorem B584081 : Blo 227813 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B584131 : Blo 227813 584131 := bstep (se 1 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 584131 = 876197) B876197
theorem B1993187 : Blo 227813 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B780785 : Blo 227813 780785 := bstep (se 2 (by rfl) ⟨292794, by rfl⟩ : syracuseStep 780785 = 585589) B585589
theorem B387571 : Blo 227813 387571 := bstep (se 1 (by rfl) ⟨290678, by rfl⟩ : syracuseStep 387571 = 581357) B581357
theorem B649745 : Blo 227813 649745 := bstep (se 2 (by rfl) ⟨243654, by rfl⟩ : syracuseStep 649745 = 487309) B487309
theorem B256531 : Blo 227813 256531 := bstep (se 1 (by rfl) ⟨192398, by rfl⟩ : syracuseStep 256531 = 384797) B384797
theorem B518705 : Blo 227813 518705 := bstep (se 2 (by rfl) ⟨194514, by rfl⟩ : syracuseStep 518705 = 389029) B389029
theorem B518723 : Blo 227813 518723 := bstep (se 1 (by rfl) ⟨389042, by rfl⟩ : syracuseStep 518723 = 778085) B778085
theorem B584273 : Blo 227813 584273 := bstep (se 2 (by rfl) ⟨219102, by rfl⟩ : syracuseStep 584273 = 438205) B438205
theorem B977521 : Blo 227813 977521 := bstep (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) B733141
theorem B387713 : Blo 227813 387713 := bstep (se 2 (by rfl) ⟨145392, by rfl⟩ : syracuseStep 387713 = 290785) B290785
theorem B256675 : Blo 227813 256675 := bstep (se 1 (by rfl) ⟨192506, by rfl⟩ : syracuseStep 256675 = 385013) B385013
theorem B879281 : Blo 227813 879281 := bstep (se 2 (by rfl) ⟨329730, by rfl⟩ : syracuseStep 879281 = 659461) B659461
theorem B1960645 : Blo 227813 1960645 := bstep (se 4 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 1960645 = 367621) B367621
theorem B5073635 : Blo 227813 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B387841 : Blo 227813 387841 := bstep (se 2 (by rfl) ⟨145440, by rfl⟩ : syracuseStep 387841 = 290881) B290881
theorem B387875 : Blo 227813 387875 := bstep (se 1 (by rfl) ⟨290906, by rfl⟩ : syracuseStep 387875 = 581813) B581813
theorem B256819 : Blo 227813 256819 := bstep (se 1 (by rfl) ⟨192614, by rfl⟩ : syracuseStep 256819 = 385229) B385229
theorem B518993 : Blo 227813 518993 := bstep (se 2 (by rfl) ⟨194622, by rfl⟩ : syracuseStep 518993 = 389245) B389245
theorem B1010531 : Blo 227813 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B519011 : Blo 227813 519011 := bstep (se 1 (by rfl) ⟨389258, by rfl⟩ : syracuseStep 519011 = 778517) B778517
theorem B289651 : Blo 227813 289651 := bstep (se 1 (by rfl) ⟨217238, by rfl⟩ : syracuseStep 289651 = 434477) B434477
theorem B388003 : Blo 227813 388003 := bstep (se 1 (by rfl) ⟨291002, by rfl⟩ : syracuseStep 388003 = 582005) B582005
theorem B256963 : Blo 227813 256963 := bstep (se 1 (by rfl) ⟨192722, by rfl⟩ : syracuseStep 256963 = 385445) B385445
theorem B289747 : Blo 227813 289747 := bstep (se 1 (by rfl) ⟨217310, by rfl⟩ : syracuseStep 289747 = 434621) B434621
theorem B781325 : Blo 227813 781325 := bstep (se 3 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 781325 = 292997) B292997
theorem B388145 : Blo 227813 388145 := bstep (se 2 (by rfl) ⟨145554, by rfl⟩ : syracuseStep 388145 = 291109) B291109
theorem B781379 : Blo 227813 781379 := bstep (se 1 (by rfl) ⟨586034, by rfl⟩ : syracuseStep 781379 = 1172069) B1172069
theorem B257107 : Blo 227813 257107 := bstep (se 1 (by rfl) ⟨192830, by rfl⟩ : syracuseStep 257107 = 385661) B385661
theorem B519281 : Blo 227813 519281 := bstep (se 2 (by rfl) ⟨194730, by rfl⟩ : syracuseStep 519281 = 389461) B389461
theorem B519299 : Blo 227813 519299 := bstep (se 1 (by rfl) ⟨389474, by rfl⟩ : syracuseStep 519299 = 778949) B778949
theorem B388273 : Blo 227813 388273 := bstep (se 2 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 388273 = 291205) B291205
theorem B388307 : Blo 227813 388307 := bstep (se 1 (by rfl) ⟨291230, by rfl⟩ : syracuseStep 388307 = 582461) B582461
theorem B257251 : Blo 227813 257251 := bstep (se 1 (by rfl) ⟨192938, by rfl⟩ : syracuseStep 257251 = 385877) B385877
theorem B1666289 : Blo 227813 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B650531 : Blo 227813 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B781649 : Blo 227813 781649 := bstep (se 2 (by rfl) ⟨293118, by rfl⟩ : syracuseStep 781649 = 586237) B586237
theorem B388435 : Blo 227813 388435 := bstep (se 1 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 388435 = 582653) B582653
theorem B257395 : Blo 227813 257395 := bstep (se 1 (by rfl) ⟨193046, by rfl⟩ : syracuseStep 257395 = 386093) B386093
theorem B519569 : Blo 227813 519569 := bstep (se 2 (by rfl) ⟨194838, by rfl⟩ : syracuseStep 519569 = 389677) B389677
theorem B519587 : Blo 227813 519587 := bstep (se 1 (by rfl) ⟨389690, by rfl⟩ : syracuseStep 519587 = 779381) B779381
theorem B290243 : Blo 227813 290243 := bstep (se 1 (by rfl) ⟨217682, by rfl⟩ : syracuseStep 290243 = 435365) B435365
theorem B388577 : Blo 227813 388577 := bstep (se 2 (by rfl) ⟨145716, by rfl⟩ : syracuseStep 388577 = 291433) B291433
theorem B257539 : Blo 227813 257539 := bstep (se 1 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 257539 = 386309) B386309
theorem B585265 : Blo 227813 585265 := bstep (se 2 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 585265 = 438949) B438949
theorem B2780725 : Blo 227813 2780725 := bstep (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) B260693
theorem B388705 : Blo 227813 388705 := bstep (se 2 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 388705 = 291529) B291529
theorem B650861 : Blo 227813 650861 := bstep (se 3 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 650861 = 244073) B244073
theorem B388739 : Blo 227813 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B257683 : Blo 227813 257683 := bstep (se 1 (by rfl) ⟨193262, by rfl⟩ : syracuseStep 257683 = 386525) B386525
theorem B650929 : Blo 227813 650929 := bstep (se 2 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 650929 = 488197) B488197
theorem B519857 : Blo 227813 519857 := bstep (se 2 (by rfl) ⟨194946, by rfl⟩ : syracuseStep 519857 = 389893) B389893
theorem B519875 : Blo 227813 519875 := bstep (se 1 (by rfl) ⟨389906, by rfl⟩ : syracuseStep 519875 = 779813) B779813
theorem B618221 : Blo 227813 618221 := bstep (se 3 (by rfl) ⟨115916, by rfl⟩ : syracuseStep 618221 = 231833) B231833
theorem B388867 : Blo 227813 388867 := bstep (se 1 (by rfl) ⟨291650, by rfl⟩ : syracuseStep 388867 = 583301) B583301
theorem B257827 : Blo 227813 257827 := bstep (se 1 (by rfl) ⟨193370, by rfl⟩ : syracuseStep 257827 = 386741) B386741
theorem B552739 : Blo 227813 552739 := bstep (se 1 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 552739 = 829109) B829109
theorem B1470257 : Blo 227813 1470257 := bstep (se 2 (by rfl) ⟨551346, by rfl⟩ : syracuseStep 1470257 = 1102693) B1102693
theorem B585539 : Blo 227813 585539 := bstep (se 1 (by rfl) ⟨439154, by rfl⟩ : syracuseStep 585539 = 878309) B878309
theorem B782189 : Blo 227813 782189 := bstep (se 3 (by rfl) ⟨146660, by rfl⟩ : syracuseStep 782189 = 293321) B293321
theorem B389009 : Blo 227813 389009 := bstep (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) B291757
theorem B782243 : Blo 227813 782243 := bstep (se 1 (by rfl) ⟨586682, by rfl⟩ : syracuseStep 782243 = 1173365) B1173365
theorem B257971 : Blo 227813 257971 := bstep (se 1 (by rfl) ⟨193478, by rfl⟩ : syracuseStep 257971 = 386957) B386957
theorem B651203 : Blo 227813 651203 := bstep (se 1 (by rfl) ⟨488402, by rfl⟩ : syracuseStep 651203 = 976805) B976805
theorem B520145 : Blo 227813 520145 := bstep (se 2 (by rfl) ⟨195054, by rfl⟩ : syracuseStep 520145 = 390109) B390109
theorem B520163 : Blo 227813 520163 := bstep (se 1 (by rfl) ⟨390122, by rfl⟩ : syracuseStep 520163 = 780245) B780245
theorem B585731 : Blo 227813 585731 := bstep (se 1 (by rfl) ⟨439298, by rfl⟩ : syracuseStep 585731 = 878597) B878597
theorem B389137 : Blo 227813 389137 := bstep (se 2 (by rfl) ⟨145926, by rfl⟩ : syracuseStep 389137 = 291853) B291853
theorem B389171 : Blo 227813 389171 := bstep (se 1 (by rfl) ⟨291878, by rfl⟩ : syracuseStep 389171 = 583757) B583757
theorem B258115 : Blo 227813 258115 := bstep (se 1 (by rfl) ⟨193586, by rfl⟩ : syracuseStep 258115 = 387173) B387173
theorem B1765475 : Blo 227813 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B290947 : Blo 227813 290947 := bstep (se 1 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 290947 = 436421) B436421
theorem B1667213 : Blo 227813 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B389299 : Blo 227813 389299 := bstep (se 1 (by rfl) ⟨291974, by rfl⟩ : syracuseStep 389299 = 583949) B583949
theorem B487633 : Blo 227813 487633 := bstep (se 2 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 487633 = 365725) B365725
theorem B258259 : Blo 227813 258259 := bstep (se 1 (by rfl) ⟨193694, by rfl⟩ : syracuseStep 258259 = 387389) B387389
theorem B291043 : Blo 227813 291043 := bstep (se 1 (by rfl) ⟨218282, by rfl⟩ : syracuseStep 291043 = 436565) B436565
theorem B520433 : Blo 227813 520433 := bstep (se 2 (by rfl) ⟨195162, by rfl⟩ : syracuseStep 520433 = 390325) B390325
theorem B520451 : Blo 227813 520451 := bstep (se 1 (by rfl) ⟨390338, by rfl⟩ : syracuseStep 520451 = 780677) B780677
theorem B782627 : Blo 227813 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B389441 : Blo 227813 389441 := bstep (se 2 (by rfl) ⟨146040, by rfl⟩ : syracuseStep 389441 = 292081) B292081
theorem B258403 : Blo 227813 258403 := bstep (se 1 (by rfl) ⟨193802, by rfl⟩ : syracuseStep 258403 = 387605) B387605
theorem B389569 : Blo 227813 389569 := bstep (se 2 (by rfl) ⟨146088, by rfl⟩ : syracuseStep 389569 = 292177) B292177
theorem B389603 : Blo 227813 389603 := bstep (se 1 (by rfl) ⟨292202, by rfl⟩ : syracuseStep 389603 = 584405) B584405
theorem B258547 : Blo 227813 258547 := bstep (se 1 (by rfl) ⟨193910, by rfl⟩ : syracuseStep 258547 = 387821) B387821
theorem B520721 : Blo 227813 520721 := bstep (se 2 (by rfl) ⟨195270, by rfl⟩ : syracuseStep 520721 = 390541) B390541
theorem B520739 : Blo 227813 520739 := bstep (se 1 (by rfl) ⟨390554, by rfl⟩ : syracuseStep 520739 = 781109) B781109
theorem B488035 : Blo 227813 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B389731 : Blo 227813 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B258691 : Blo 227813 258691 := bstep (se 1 (by rfl) ⟨194018, by rfl⟩ : syracuseStep 258691 = 388037) B388037
theorem B291539 : Blo 227813 291539 := bstep (se 1 (by rfl) ⟨218654, by rfl⟩ : syracuseStep 291539 = 437309) B437309
theorem B389873 : Blo 227813 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B652045 : Blo 227813 652045 := bstep (se 3 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 652045 = 244517) B244517
theorem B324371 : Blo 227813 324371 := bstep (se 1 (by rfl) ⟨243278, by rfl⟩ : syracuseStep 324371 = 486557) B486557
theorem B258835 : Blo 227813 258835 := bstep (se 1 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 258835 = 388253) B388253
theorem B521009 : Blo 227813 521009 := bstep (se 2 (by rfl) ⟨195378, by rfl⟩ : syracuseStep 521009 = 390757) B390757
theorem B4682549 : Blo 227813 4682549 := bstep (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) B438989
theorem B521027 : Blo 227813 521027 := bstep (se 1 (by rfl) ⟨390770, by rfl⟩ : syracuseStep 521027 = 781541) B781541
theorem B1307461 : Blo 227813 1307461 := bstep (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) B245149
theorem B521059 : Blo 227813 521059 := bstep (se 1 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 521059 = 781589) B781589
theorem B390001 : Blo 227813 390001 := bstep (se 2 (by rfl) ⟨146250, by rfl⟩ : syracuseStep 390001 = 292501) B292501
theorem B390035 : Blo 227813 390035 := bstep (se 1 (by rfl) ⟨292526, by rfl⟩ : syracuseStep 390035 = 585053) B585053
theorem B258979 : Blo 227813 258979 := bstep (se 1 (by rfl) ⟨194234, by rfl⟩ : syracuseStep 258979 = 388469) B388469
theorem B652205 : Blo 227813 652205 := bstep (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) B244577
theorem B586673 : Blo 227813 586673 := bstep (se 2 (by rfl) ⟨220002, by rfl⟩ : syracuseStep 586673 = 440005) B440005
theorem B586723 : Blo 227813 586723 := bstep (se 1 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 586723 = 880085) B880085
theorem B553969 : Blo 227813 553969 := bstep (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) B415477
theorem B390163 : Blo 227813 390163 := bstep (se 1 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 390163 = 585245) B585245
theorem B259123 : Blo 227813 259123 := bstep (se 1 (by rfl) ⟨194342, by rfl⟩ : syracuseStep 259123 = 388685) B388685
theorem B521297 : Blo 227813 521297 := bstep (se 2 (by rfl) ⟨195486, by rfl⟩ : syracuseStep 521297 = 390973) B390973
theorem B652387 : Blo 227813 652387 := bstep (se 1 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 652387 = 978581) B978581
theorem B521315 : Blo 227813 521315 := bstep (se 1 (by rfl) ⟨390986, by rfl⟩ : syracuseStep 521315 = 781973) B781973
theorem B390275 : Blo 227813 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B390305 : Blo 227813 390305 := bstep (se 2 (by rfl) ⟨146364, by rfl⟩ : syracuseStep 390305 = 292729) B292729
theorem B259267 : Blo 227813 259267 := bstep (se 1 (by rfl) ⟨194450, by rfl⟩ : syracuseStep 259267 = 388901) B388901
theorem B1471715 : Blo 227813 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B619757 : Blo 227813 619757 := bstep (se 3 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 619757 = 232409) B232409
theorem B390433 : Blo 227813 390433 := bstep (se 2 (by rfl) ⟨146412, by rfl⟩ : syracuseStep 390433 = 292825) B292825
theorem B324929 : Blo 227813 324929 := bstep (se 2 (by rfl) ⟨121848, by rfl⟩ : syracuseStep 324929 = 243697) B243697
theorem B390467 : Blo 227813 390467 := bstep (se 1 (by rfl) ⟨292850, by rfl⟩ : syracuseStep 390467 = 585701) B585701
theorem B259411 : Blo 227813 259411 := bstep (se 1 (by rfl) ⟨194558, by rfl⟩ : syracuseStep 259411 = 389117) B389117
theorem B325009 : Blo 227813 325009 := bstep (se 2 (by rfl) ⟨121878, by rfl⟩ : syracuseStep 325009 = 243757) B243757
theorem B292243 : Blo 227813 292243 := bstep (se 1 (by rfl) ⟨219182, by rfl⟩ : syracuseStep 292243 = 438365) B438365
theorem B390595 : Blo 227813 390595 := bstep (se 1 (by rfl) ⟨292946, by rfl⟩ : syracuseStep 390595 = 585893) B585893
theorem B259555 : Blo 227813 259555 := bstep (se 1 (by rfl) ⟨194666, by rfl⟩ : syracuseStep 259555 = 389333) B389333
theorem B292339 : Blo 227813 292339 := bstep (se 1 (by rfl) ⟨219254, by rfl⟩ : syracuseStep 292339 = 438509) B438509
theorem B390737 : Blo 227813 390737 := bstep (se 2 (by rfl) ⟨146526, by rfl⟩ : syracuseStep 390737 = 293053) B293053
theorem B259699 : Blo 227813 259699 := bstep (se 1 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 259699 = 389549) B389549
theorem B390865 : Blo 227813 390865 := bstep (se 2 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 390865 = 293149) B293149
theorem B390899 : Blo 227813 390899 := bstep (se 1 (by rfl) ⟨293174, by rfl⟩ : syracuseStep 390899 = 586349) B586349
theorem B259843 : Blo 227813 259843 := bstep (se 1 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 259843 = 389765) B389765
theorem B391027 : Blo 227813 391027 := bstep (se 1 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 391027 = 586541) B586541
theorem B259987 : Blo 227813 259987 := bstep (se 1 (by rfl) ⟨194990, by rfl⟩ : syracuseStep 259987 = 389981) B389981
theorem B391123 : Blo 227813 391123 := bstep (se 1 (by rfl) ⟨293342, by rfl⟩ : syracuseStep 391123 = 586685) B586685
theorem B292835 : Blo 227813 292835 := bstep (se 1 (by rfl) ⟨219626, by rfl⟩ : syracuseStep 292835 = 439253) B439253
theorem B391169 : Blo 227813 391169 := bstep (se 2 (by rfl) ⟨146688, by rfl⟩ : syracuseStep 391169 = 293377) B293377
theorem B2488333 : Blo 227813 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B260131 : Blo 227813 260131 := bstep (se 1 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 260131 = 390197) B390197
theorem B489539 : Blo 227813 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B325795 : Blo 227813 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B260275 : Blo 227813 260275 := bstep (se 1 (by rfl) ⟨195206, by rfl⟩ : syracuseStep 260275 = 390413) B390413
theorem B260419 : Blo 227813 260419 := bstep (se 1 (by rfl) ⟨195314, by rfl⟩ : syracuseStep 260419 = 390629) B390629
theorem B653777 : Blo 227813 653777 := bstep (se 2 (by rfl) ⟨245166, by rfl⟩ : syracuseStep 653777 = 490333) B490333
theorem B260563 : Blo 227813 260563 := bstep (se 1 (by rfl) ⟨195422, by rfl⟩ : syracuseStep 260563 = 390845) B390845
theorem B227827 : Blo 227813 227827 := bstep (se 1 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 227827 = 341741) B341741
theorem B227843 : Blo 227813 227843 := bstep (se 1 (by rfl) ⟨170882, by rfl⟩ : syracuseStep 227843 = 341765) B341765
theorem B2521613 : Blo 227813 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B391697 : Blo 227813 391697 := bstep (se 2 (by rfl) ⟨146886, by rfl⟩ : syracuseStep 391697 = 293773) B293773
theorem B227859 : Blo 227813 227859 := bstep (se 1 (by rfl) ⟨170894, by rfl⟩ : syracuseStep 227859 = 341789) B341789
theorem B227875 : Blo 227813 227875 := bstep (se 1 (by rfl) ⟨170906, by rfl⟩ : syracuseStep 227875 = 341813) B341813
theorem B981553 : Blo 227813 981553 := bstep (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) B736165
theorem B227891 : Blo 227813 227891 := bstep (se 1 (by rfl) ⟨170918, by rfl⟩ : syracuseStep 227891 = 341837) B341837
theorem B227907 : Blo 227813 227907 := bstep (se 1 (by rfl) ⟨170930, by rfl⟩ : syracuseStep 227907 = 341861) B341861
theorem B227923 : Blo 227813 227923 := bstep (se 1 (by rfl) ⟨170942, by rfl⟩ : syracuseStep 227923 = 341885) B341885
theorem B227939 : Blo 227813 227939 := bstep (se 1 (by rfl) ⟨170954, by rfl⟩ : syracuseStep 227939 = 341909) B341909
theorem B260707 : Blo 227813 260707 := bstep (se 1 (by rfl) ⟨195530, by rfl⟩ : syracuseStep 260707 = 391061) B391061
theorem B227955 : Blo 227813 227955 := bstep (se 1 (by rfl) ⟨170966, by rfl⟩ : syracuseStep 227955 = 341933) B341933
theorem B326273 : Blo 227813 326273 := bstep (se 2 (by rfl) ⟨122352, by rfl⟩ : syracuseStep 326273 = 244705) B244705
theorem B227971 : Blo 227813 227971 := bstep (se 1 (by rfl) ⟨170978, by rfl⟩ : syracuseStep 227971 = 341957) B341957
theorem B227987 : Blo 227813 227987 := bstep (se 1 (by rfl) ⟨170990, by rfl⟩ : syracuseStep 227987 = 341981) B341981
theorem B228003 : Blo 227813 228003 := bstep (se 1 (by rfl) ⟨171002, by rfl⟩ : syracuseStep 228003 = 342005) B342005
theorem B228019 : Blo 227813 228019 := bstep (se 1 (by rfl) ⟨171014, by rfl⟩ : syracuseStep 228019 = 342029) B342029
theorem B228035 : Blo 227813 228035 := bstep (se 1 (by rfl) ⟨171026, by rfl⟩ : syracuseStep 228035 = 342053) B342053
theorem B391889 : Blo 227813 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B228051 : Blo 227813 228051 := bstep (se 1 (by rfl) ⟨171038, by rfl⟩ : syracuseStep 228051 = 342077) B342077
theorem B228067 : Blo 227813 228067 := bstep (se 1 (by rfl) ⟨171050, by rfl⟩ : syracuseStep 228067 = 342101) B342101
theorem B228083 : Blo 227813 228083 := bstep (se 1 (by rfl) ⟨171062, by rfl⟩ : syracuseStep 228083 = 342125) B342125
theorem B326387 : Blo 227813 326387 := bstep (se 1 (by rfl) ⟨244790, by rfl⟩ : syracuseStep 326387 = 489581) B489581
theorem B228099 : Blo 227813 228099 := bstep (se 1 (by rfl) ⟨171074, by rfl⟩ : syracuseStep 228099 = 342149) B342149
theorem B1309445 : Blo 227813 1309445 := bstep (se 4 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 1309445 = 245521) B245521
theorem B228115 : Blo 227813 228115 := bstep (se 1 (by rfl) ⟨171086, by rfl⟩ : syracuseStep 228115 = 342173) B342173
theorem B228131 : Blo 227813 228131 := bstep (se 1 (by rfl) ⟨171098, by rfl⟩ : syracuseStep 228131 = 342197) B342197
theorem B228147 : Blo 227813 228147 := bstep (se 1 (by rfl) ⟨171110, by rfl⟩ : syracuseStep 228147 = 342221) B342221
theorem B228163 : Blo 227813 228163 := bstep (se 1 (by rfl) ⟨171122, by rfl⟩ : syracuseStep 228163 = 342245) B342245
theorem B326467 : Blo 227813 326467 := bstep (se 1 (by rfl) ⟨244850, by rfl⟩ : syracuseStep 326467 = 489701) B489701
theorem B228179 : Blo 227813 228179 := bstep (se 1 (by rfl) ⟨171134, by rfl⟩ : syracuseStep 228179 = 342269) B342269
theorem B228195 : Blo 227813 228195 := bstep (se 1 (by rfl) ⟨171146, by rfl⟩ : syracuseStep 228195 = 342293) B342293
theorem B228211 : Blo 227813 228211 := bstep (se 1 (by rfl) ⟨171158, by rfl⟩ : syracuseStep 228211 = 342317) B342317
theorem B228227 : Blo 227813 228227 := bstep (se 1 (by rfl) ⟨171170, by rfl⟩ : syracuseStep 228227 = 342341) B342341
theorem B228243 : Blo 227813 228243 := bstep (se 1 (by rfl) ⟨171182, by rfl⟩ : syracuseStep 228243 = 342365) B342365
theorem B228259 : Blo 227813 228259 := bstep (se 1 (by rfl) ⟨171194, by rfl⟩ : syracuseStep 228259 = 342389) B342389
theorem B228275 : Blo 227813 228275 := bstep (se 1 (by rfl) ⟨171206, by rfl⟩ : syracuseStep 228275 = 342413) B342413
theorem B228291 : Blo 227813 228291 := bstep (se 1 (by rfl) ⟨171218, by rfl⟩ : syracuseStep 228291 = 342437) B342437
theorem B228307 : Blo 227813 228307 := bstep (se 1 (by rfl) ⟨171230, by rfl⟩ : syracuseStep 228307 = 342461) B342461
theorem B228323 : Blo 227813 228323 := bstep (se 1 (by rfl) ⟨171242, by rfl⟩ : syracuseStep 228323 = 342485) B342485
theorem B228339 : Blo 227813 228339 := bstep (se 1 (by rfl) ⟨171254, by rfl⟩ : syracuseStep 228339 = 342509) B342509
theorem B228355 : Blo 227813 228355 := bstep (se 1 (by rfl) ⟨171266, by rfl⟩ : syracuseStep 228355 = 342533) B342533
theorem B2194445 : Blo 227813 2194445 := bstep (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) B822917
theorem B228371 : Blo 227813 228371 := bstep (se 1 (by rfl) ⟨171278, by rfl⟩ : syracuseStep 228371 = 342557) B342557
theorem B228387 : Blo 227813 228387 := bstep (se 1 (by rfl) ⟨171290, by rfl⟩ : syracuseStep 228387 = 342581) B342581
theorem B228403 : Blo 227813 228403 := bstep (se 1 (by rfl) ⟨171302, by rfl⟩ : syracuseStep 228403 = 342605) B342605
theorem B228419 : Blo 227813 228419 := bstep (se 1 (by rfl) ⟨171314, by rfl⟩ : syracuseStep 228419 = 342629) B342629
theorem B228435 : Blo 227813 228435 := bstep (se 1 (by rfl) ⟨171326, by rfl⟩ : syracuseStep 228435 = 342653) B342653
theorem B228451 : Blo 227813 228451 := bstep (se 1 (by rfl) ⟨171338, by rfl⟩ : syracuseStep 228451 = 342677) B342677
theorem B228467 : Blo 227813 228467 := bstep (se 1 (by rfl) ⟨171350, by rfl⟩ : syracuseStep 228467 = 342701) B342701
theorem B228483 : Blo 227813 228483 := bstep (se 1 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 228483 = 342725) B342725
theorem B228499 : Blo 227813 228499 := bstep (se 1 (by rfl) ⟨171374, by rfl⟩ : syracuseStep 228499 = 342749) B342749
theorem B228515 : Blo 227813 228515 := bstep (se 1 (by rfl) ⟨171386, by rfl⟩ : syracuseStep 228515 = 342773) B342773
theorem B228531 : Blo 227813 228531 := bstep (se 1 (by rfl) ⟨171398, by rfl⟩ : syracuseStep 228531 = 342797) B342797
theorem B228547 : Blo 227813 228547 := bstep (se 1 (by rfl) ⟨171410, by rfl⟩ : syracuseStep 228547 = 342821) B342821
theorem B228563 : Blo 227813 228563 := bstep (se 1 (by rfl) ⟨171422, by rfl⟩ : syracuseStep 228563 = 342845) B342845
theorem B228579 : Blo 227813 228579 := bstep (se 1 (by rfl) ⟨171434, by rfl⟩ : syracuseStep 228579 = 342869) B342869
theorem B228595 : Blo 227813 228595 := bstep (se 1 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 228595 = 342893) B342893
theorem B228611 : Blo 227813 228611 := bstep (se 1 (by rfl) ⟨171458, by rfl⟩ : syracuseStep 228611 = 342917) B342917
theorem B523523 : Blo 227813 523523 := bstep (se 1 (by rfl) ⟨392642, by rfl⟩ : syracuseStep 523523 = 785285) B785285
theorem B490769 : Blo 227813 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B228627 : Blo 227813 228627 := bstep (se 1 (by rfl) ⟨171470, by rfl⟩ : syracuseStep 228627 = 342941) B342941
theorem B228643 : Blo 227813 228643 := bstep (se 1 (by rfl) ⟨171482, by rfl⟩ : syracuseStep 228643 = 342965) B342965
theorem B228659 : Blo 227813 228659 := bstep (se 1 (by rfl) ⟨171494, by rfl⟩ : syracuseStep 228659 = 342989) B342989
theorem B228675 : Blo 227813 228675 := bstep (se 1 (by rfl) ⟨171506, by rfl⟩ : syracuseStep 228675 = 343013) B343013
theorem B228691 : Blo 227813 228691 := bstep (se 1 (by rfl) ⟨171518, by rfl⟩ : syracuseStep 228691 = 343037) B343037
theorem B228707 : Blo 227813 228707 := bstep (se 1 (by rfl) ⟨171530, by rfl⟩ : syracuseStep 228707 = 343061) B343061
theorem B327025 : Blo 227813 327025 := bstep (se 2 (by rfl) ⟨122634, by rfl⟩ : syracuseStep 327025 = 245269) B245269
theorem B228723 : Blo 227813 228723 := bstep (se 1 (by rfl) ⟨171542, by rfl⟩ : syracuseStep 228723 = 343085) B343085
theorem B228739 : Blo 227813 228739 := bstep (se 1 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 228739 = 343109) B343109
theorem B654733 : Blo 227813 654733 := bstep (se 3 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 654733 = 245525) B245525
theorem B228755 : Blo 227813 228755 := bstep (se 1 (by rfl) ⟨171566, by rfl⟩ : syracuseStep 228755 = 343133) B343133
theorem B228771 : Blo 227813 228771 := bstep (se 1 (by rfl) ⟨171578, by rfl⟩ : syracuseStep 228771 = 343157) B343157
theorem B228787 : Blo 227813 228787 := bstep (se 1 (by rfl) ⟨171590, by rfl⟩ : syracuseStep 228787 = 343181) B343181
theorem B228803 : Blo 227813 228803 := bstep (se 1 (by rfl) ⟨171602, by rfl⟩ : syracuseStep 228803 = 343205) B343205
theorem B228819 : Blo 227813 228819 := bstep (se 1 (by rfl) ⟨171614, by rfl⟩ : syracuseStep 228819 = 343229) B343229
theorem B228835 : Blo 227813 228835 := bstep (se 1 (by rfl) ⟨171626, by rfl⟩ : syracuseStep 228835 = 343253) B343253
theorem B228851 : Blo 227813 228851 := bstep (se 1 (by rfl) ⟨171638, by rfl⟩ : syracuseStep 228851 = 343277) B343277
theorem B228867 : Blo 227813 228867 := bstep (se 1 (by rfl) ⟨171650, by rfl⟩ : syracuseStep 228867 = 343301) B343301
theorem B228883 : Blo 227813 228883 := bstep (se 1 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 228883 = 343325) B343325
theorem B228899 : Blo 227813 228899 := bstep (se 1 (by rfl) ⟨171674, by rfl⟩ : syracuseStep 228899 = 343349) B343349
theorem B228915 : Blo 227813 228915 := bstep (se 1 (by rfl) ⟨171686, by rfl⟩ : syracuseStep 228915 = 343373) B343373
theorem B228931 : Blo 227813 228931 := bstep (se 1 (by rfl) ⟨171698, by rfl⟩ : syracuseStep 228931 = 343397) B343397
theorem B228947 : Blo 227813 228947 := bstep (se 1 (by rfl) ⟨171710, by rfl⟩ : syracuseStep 228947 = 343421) B343421
theorem B228963 : Blo 227813 228963 := bstep (se 1 (by rfl) ⟨171722, by rfl⟩ : syracuseStep 228963 = 343445) B343445
theorem B654961 : Blo 227813 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B228979 : Blo 227813 228979 := bstep (se 1 (by rfl) ⟨171734, by rfl⟩ : syracuseStep 228979 = 343469) B343469
theorem B228995 : Blo 227813 228995 := bstep (se 1 (by rfl) ⟨171746, by rfl⟩ : syracuseStep 228995 = 343493) B343493
theorem B589457 : Blo 227813 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B229011 : Blo 227813 229011 := bstep (se 1 (by rfl) ⟨171758, by rfl⟩ : syracuseStep 229011 = 343517) B343517
theorem B229027 : Blo 227813 229027 := bstep (se 1 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 229027 = 343541) B343541
theorem B229043 : Blo 227813 229043 := bstep (se 1 (by rfl) ⟨171782, by rfl⟩ : syracuseStep 229043 = 343565) B343565
theorem B229059 : Blo 227813 229059 := bstep (se 1 (by rfl) ⟨171794, by rfl⟩ : syracuseStep 229059 = 343589) B343589
theorem B229075 : Blo 227813 229075 := bstep (se 1 (by rfl) ⟨171806, by rfl⟩ : syracuseStep 229075 = 343613) B343613
theorem B229091 : Blo 227813 229091 := bstep (se 1 (by rfl) ⟨171818, by rfl⟩ : syracuseStep 229091 = 343637) B343637
theorem B229107 : Blo 227813 229107 := bstep (se 1 (by rfl) ⟨171830, by rfl⟩ : syracuseStep 229107 = 343661) B343661
theorem B229123 : Blo 227813 229123 := bstep (se 1 (by rfl) ⟨171842, by rfl⟩ : syracuseStep 229123 = 343685) B343685
theorem B655121 : Blo 227813 655121 := bstep (se 2 (by rfl) ⟨245670, by rfl⟩ : syracuseStep 655121 = 491341) B491341
theorem B229139 : Blo 227813 229139 := bstep (se 1 (by rfl) ⟨171854, by rfl⟩ : syracuseStep 229139 = 343709) B343709
theorem B229155 : Blo 227813 229155 := bstep (se 1 (by rfl) ⟨171866, by rfl⟩ : syracuseStep 229155 = 343733) B343733
theorem B229171 : Blo 227813 229171 := bstep (se 1 (by rfl) ⟨171878, by rfl⟩ : syracuseStep 229171 = 343757) B343757
theorem B229187 : Blo 227813 229187 := bstep (se 1 (by rfl) ⟨171890, by rfl⟩ : syracuseStep 229187 = 343781) B343781
theorem B229203 : Blo 227813 229203 := bstep (se 1 (by rfl) ⟨171902, by rfl⟩ : syracuseStep 229203 = 343805) B343805
theorem B229219 : Blo 227813 229219 := bstep (se 1 (by rfl) ⟨171914, by rfl⟩ : syracuseStep 229219 = 343829) B343829
theorem B229235 : Blo 227813 229235 := bstep (se 1 (by rfl) ⟨171926, by rfl⟩ : syracuseStep 229235 = 343853) B343853
theorem B229251 : Blo 227813 229251 := bstep (se 1 (by rfl) ⟨171938, by rfl⟩ : syracuseStep 229251 = 343877) B343877
theorem B655235 : Blo 227813 655235 := bstep (se 1 (by rfl) ⟨491426, by rfl⟩ : syracuseStep 655235 = 982853) B982853
theorem B229267 : Blo 227813 229267 := bstep (se 1 (by rfl) ⟨171950, by rfl⟩ : syracuseStep 229267 = 343901) B343901
theorem B229283 : Blo 227813 229283 := bstep (se 1 (by rfl) ⟨171962, by rfl⟩ : syracuseStep 229283 = 343925) B343925
theorem B229299 : Blo 227813 229299 := bstep (se 1 (by rfl) ⟨171974, by rfl⟩ : syracuseStep 229299 = 343949) B343949
theorem B229315 : Blo 227813 229315 := bstep (se 1 (by rfl) ⟨171986, by rfl⟩ : syracuseStep 229315 = 343973) B343973
theorem B229331 : Blo 227813 229331 := bstep (se 1 (by rfl) ⟨171998, by rfl⟩ : syracuseStep 229331 = 343997) B343997
theorem B229347 : Blo 227813 229347 := bstep (se 1 (by rfl) ⟨172010, by rfl⟩ : syracuseStep 229347 = 344021) B344021
theorem B229363 : Blo 227813 229363 := bstep (se 1 (by rfl) ⟨172022, by rfl⟩ : syracuseStep 229363 = 344045) B344045
theorem B491521 : Blo 227813 491521 := bstep (se 2 (by rfl) ⟨184320, by rfl⟩ : syracuseStep 491521 = 368641) B368641
theorem B229387 : Blo 227813 229387 := bstep (se 1 (by rfl) ⟨172040, by rfl⟩ : syracuseStep 229387 = 344081) B344081
theorem B229399 : Blo 227813 229399 := bstep (se 1 (by rfl) ⟨172049, by rfl⟩ : syracuseStep 229399 = 344099) B344099
theorem B229419 : Blo 227813 229419 := bstep (se 1 (by rfl) ⟨172064, by rfl⟩ : syracuseStep 229419 = 344129) B344129
theorem B229431 : Blo 227813 229431 := bstep (se 1 (by rfl) ⟨172073, by rfl⟩ : syracuseStep 229431 = 344147) B344147
theorem B229451 : Blo 227813 229451 := bstep (se 1 (by rfl) ⟨172088, by rfl⟩ : syracuseStep 229451 = 344177) B344177
theorem B229463 : Blo 227813 229463 := bstep (se 1 (by rfl) ⟨172097, by rfl⟩ : syracuseStep 229463 = 344195) B344195
theorem B229483 : Blo 227813 229483 := bstep (se 1 (by rfl) ⟨172112, by rfl⟩ : syracuseStep 229483 = 344225) B344225
theorem B229495 : Blo 227813 229495 := bstep (se 1 (by rfl) ⟨172121, by rfl⟩ : syracuseStep 229495 = 344243) B344243
theorem B229515 : Blo 227813 229515 := bstep (se 1 (by rfl) ⟨172136, by rfl⟩ : syracuseStep 229515 = 344273) B344273
theorem B229527 : Blo 227813 229527 := bstep (se 1 (by rfl) ⟨172145, by rfl⟩ : syracuseStep 229527 = 344291) B344291
theorem B229547 : Blo 227813 229547 := bstep (se 1 (by rfl) ⟨172160, by rfl⟩ : syracuseStep 229547 = 344321) B344321
theorem B229559 : Blo 227813 229559 := bstep (se 1 (by rfl) ⟨172169, by rfl⟩ : syracuseStep 229559 = 344339) B344339
theorem B655553 : Blo 227813 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B229579 : Blo 227813 229579 := bstep (se 1 (by rfl) ⟨172184, by rfl⟩ : syracuseStep 229579 = 344369) B344369
theorem B229591 : Blo 227813 229591 := bstep (se 1 (by rfl) ⟨172193, by rfl⟩ : syracuseStep 229591 = 344387) B344387
theorem B655577 : Blo 227813 655577 := bstep (se 2 (by rfl) ⟨245841, by rfl⟩ : syracuseStep 655577 = 491683) B491683
theorem B229611 : Blo 227813 229611 := bstep (se 1 (by rfl) ⟨172208, by rfl⟩ : syracuseStep 229611 = 344417) B344417
theorem B229623 : Blo 227813 229623 := bstep (se 1 (by rfl) ⟨172217, by rfl⟩ : syracuseStep 229623 = 344435) B344435
theorem B229643 : Blo 227813 229643 := bstep (se 1 (by rfl) ⟨172232, by rfl⟩ : syracuseStep 229643 = 344465) B344465
theorem B229655 : Blo 227813 229655 := bstep (se 1 (by rfl) ⟨172241, by rfl⟩ : syracuseStep 229655 = 344483) B344483
theorem B229675 : Blo 227813 229675 := bstep (se 1 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 229675 = 344513) B344513
theorem B229687 : Blo 227813 229687 := bstep (se 1 (by rfl) ⟨172265, by rfl⟩ : syracuseStep 229687 = 344531) B344531
theorem B229707 : Blo 227813 229707 := bstep (se 1 (by rfl) ⟨172280, by rfl⟩ : syracuseStep 229707 = 344561) B344561
theorem B229719 : Blo 227813 229719 := bstep (se 1 (by rfl) ⟨172289, by rfl⟩ : syracuseStep 229719 = 344579) B344579
theorem B229739 : Blo 227813 229739 := bstep (se 1 (by rfl) ⟨172304, by rfl⟩ : syracuseStep 229739 = 344609) B344609
theorem B229751 : Blo 227813 229751 := bstep (se 1 (by rfl) ⟨172313, by rfl⟩ : syracuseStep 229751 = 344627) B344627
theorem B229771 : Blo 227813 229771 := bstep (se 1 (by rfl) ⟨172328, by rfl⟩ : syracuseStep 229771 = 344657) B344657
theorem B229783 : Blo 227813 229783 := bstep (se 1 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 229783 = 344675) B344675
theorem B229803 : Blo 227813 229803 := bstep (se 1 (by rfl) ⟨172352, by rfl⟩ : syracuseStep 229803 = 344705) B344705
theorem B229815 : Blo 227813 229815 := bstep (se 1 (by rfl) ⟨172361, by rfl⟩ : syracuseStep 229815 = 344723) B344723
theorem B229835 : Blo 227813 229835 := bstep (se 1 (by rfl) ⟨172376, by rfl⟩ : syracuseStep 229835 = 344753) B344753
theorem B229847 : Blo 227813 229847 := bstep (se 1 (by rfl) ⟨172385, by rfl⟩ : syracuseStep 229847 = 344771) B344771
theorem B328153 : Blo 227813 328153 := bstep (se 2 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 328153 = 246115) B246115
theorem B623065 : Blo 227813 623065 := bstep (se 2 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 623065 = 467299) B467299
theorem B229867 : Blo 227813 229867 := bstep (se 1 (by rfl) ⟨172400, by rfl⟩ : syracuseStep 229867 = 344801) B344801
theorem B229879 : Blo 227813 229879 := bstep (se 1 (by rfl) ⟨172409, by rfl⟩ : syracuseStep 229879 = 344819) B344819
theorem B229899 : Blo 227813 229899 := bstep (se 1 (by rfl) ⟨172424, by rfl⟩ : syracuseStep 229899 = 344849) B344849
theorem B229911 : Blo 227813 229911 := bstep (se 1 (by rfl) ⟨172433, by rfl⟩ : syracuseStep 229911 = 344867) B344867
theorem B229931 : Blo 227813 229931 := bstep (se 1 (by rfl) ⟨172448, by rfl⟩ : syracuseStep 229931 = 344897) B344897
theorem B983603 : Blo 227813 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B229943 : Blo 227813 229943 := bstep (se 1 (by rfl) ⟨172457, by rfl⟩ : syracuseStep 229943 = 344915) B344915
theorem B229963 : Blo 227813 229963 := bstep (se 1 (by rfl) ⟨172472, by rfl⟩ : syracuseStep 229963 = 344945) B344945
theorem B229975 : Blo 227813 229975 := bstep (se 1 (by rfl) ⟨172481, by rfl⟩ : syracuseStep 229975 = 344963) B344963
theorem B229995 : Blo 227813 229995 := bstep (se 1 (by rfl) ⟨172496, by rfl⟩ : syracuseStep 229995 = 344993) B344993
theorem B230007 : Blo 227813 230007 := bstep (se 1 (by rfl) ⟨172505, by rfl⟩ : syracuseStep 230007 = 345011) B345011
theorem B230027 : Blo 227813 230027 := bstep (se 1 (by rfl) ⟨172520, by rfl⟩ : syracuseStep 230027 = 345041) B345041
theorem B230039 : Blo 227813 230039 := bstep (se 1 (by rfl) ⟨172529, by rfl⟩ : syracuseStep 230039 = 345059) B345059
theorem B2130583 : Blo 227813 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B230059 : Blo 227813 230059 := bstep (se 1 (by rfl) ⟨172544, by rfl⟩ : syracuseStep 230059 = 345089) B345089
theorem B230071 : Blo 227813 230071 := bstep (se 1 (by rfl) ⟨172553, by rfl⟩ : syracuseStep 230071 = 345107) B345107
theorem B230091 : Blo 227813 230091 := bstep (se 1 (by rfl) ⟨172568, by rfl⟩ : syracuseStep 230091 = 345137) B345137
theorem B230103 : Blo 227813 230103 := bstep (se 1 (by rfl) ⟨172577, by rfl⟩ : syracuseStep 230103 = 345155) B345155
theorem B393943 : Blo 227813 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B230123 : Blo 227813 230123 := bstep (se 1 (by rfl) ⟨172592, by rfl⟩ : syracuseStep 230123 = 345185) B345185
theorem B230135 : Blo 227813 230135 := bstep (se 1 (by rfl) ⟨172601, by rfl⟩ : syracuseStep 230135 = 345203) B345203
theorem B230155 : Blo 227813 230155 := bstep (se 1 (by rfl) ⟨172616, by rfl⟩ : syracuseStep 230155 = 345233) B345233
theorem B230167 : Blo 227813 230167 := bstep (se 1 (by rfl) ⟨172625, by rfl⟩ : syracuseStep 230167 = 345251) B345251
theorem B1868579 : Blo 227813 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B230187 : Blo 227813 230187 := bstep (se 1 (by rfl) ⟨172640, by rfl⟩ : syracuseStep 230187 = 345281) B345281
theorem B230199 : Blo 227813 230199 := bstep (se 1 (by rfl) ⟨172649, by rfl⟩ : syracuseStep 230199 = 345299) B345299
theorem B1868609 : Blo 227813 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B230219 : Blo 227813 230219 := bstep (se 1 (by rfl) ⟨172664, by rfl⟩ : syracuseStep 230219 = 345329) B345329
theorem B230231 : Blo 227813 230231 := bstep (se 1 (by rfl) ⟨172673, by rfl⟩ : syracuseStep 230231 = 345347) B345347
theorem B230251 : Blo 227813 230251 := bstep (se 1 (by rfl) ⟨172688, by rfl⟩ : syracuseStep 230251 = 345377) B345377
theorem B230263 : Blo 227813 230263 := bstep (se 1 (by rfl) ⟨172697, by rfl⟩ : syracuseStep 230263 = 345395) B345395
theorem B230283 : Blo 227813 230283 := bstep (se 1 (by rfl) ⟨172712, by rfl⟩ : syracuseStep 230283 = 345425) B345425
theorem B230295 : Blo 227813 230295 := bstep (se 1 (by rfl) ⟨172721, by rfl⟩ : syracuseStep 230295 = 345443) B345443
theorem B230315 : Blo 227813 230315 := bstep (se 1 (by rfl) ⟨172736, by rfl⟩ : syracuseStep 230315 = 345473) B345473
theorem B230327 : Blo 227813 230327 := bstep (se 1 (by rfl) ⟨172745, by rfl⟩ : syracuseStep 230327 = 345491) B345491
theorem B230347 : Blo 227813 230347 := bstep (se 1 (by rfl) ⟨172760, by rfl⟩ : syracuseStep 230347 = 345521) B345521
theorem B230359 : Blo 227813 230359 := bstep (se 1 (by rfl) ⟨172769, by rfl⟩ : syracuseStep 230359 = 345539) B345539
theorem B230379 : Blo 227813 230379 := bstep (se 1 (by rfl) ⟨172784, by rfl⟩ : syracuseStep 230379 = 345569) B345569
theorem B230391 : Blo 227813 230391 := bstep (se 1 (by rfl) ⟨172793, by rfl⟩ : syracuseStep 230391 = 345587) B345587
theorem B230411 : Blo 227813 230411 := bstep (se 1 (by rfl) ⟨172808, by rfl⟩ : syracuseStep 230411 = 345617) B345617
theorem B230423 : Blo 227813 230423 := bstep (se 1 (by rfl) ⟨172817, by rfl⟩ : syracuseStep 230423 = 345635) B345635
theorem B230443 : Blo 227813 230443 := bstep (se 1 (by rfl) ⟨172832, by rfl⟩ : syracuseStep 230443 = 345665) B345665
theorem B230455 : Blo 227813 230455 := bstep (se 1 (by rfl) ⟨172841, by rfl⟩ : syracuseStep 230455 = 345683) B345683
theorem B230475 : Blo 227813 230475 := bstep (se 1 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 230475 = 345713) B345713
theorem B230487 : Blo 227813 230487 := bstep (se 1 (by rfl) ⟨172865, by rfl⟩ : syracuseStep 230487 = 345731) B345731
theorem B230507 : Blo 227813 230507 := bstep (se 1 (by rfl) ⟨172880, by rfl⟩ : syracuseStep 230507 = 345761) B345761
theorem B230519 : Blo 227813 230519 := bstep (se 1 (by rfl) ⟨172889, by rfl⟩ : syracuseStep 230519 = 345779) B345779
theorem B230539 : Blo 227813 230539 := bstep (se 1 (by rfl) ⟨172904, by rfl⟩ : syracuseStep 230539 = 345809) B345809
theorem B230551 : Blo 227813 230551 := bstep (se 1 (by rfl) ⟨172913, by rfl⟩ : syracuseStep 230551 = 345827) B345827
theorem B230571 : Blo 227813 230571 := bstep (se 1 (by rfl) ⟨172928, by rfl⟩ : syracuseStep 230571 = 345857) B345857
theorem B230583 : Blo 227813 230583 := bstep (se 1 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 230583 = 345875) B345875
theorem B230603 : Blo 227813 230603 := bstep (se 1 (by rfl) ⟨172952, by rfl⟩ : syracuseStep 230603 = 345905) B345905
theorem B230615 : Blo 227813 230615 := bstep (se 1 (by rfl) ⟨172961, by rfl⟩ : syracuseStep 230615 = 345923) B345923
theorem B230635 : Blo 227813 230635 := bstep (se 1 (by rfl) ⟨172976, by rfl⟩ : syracuseStep 230635 = 345953) B345953
theorem B230647 : Blo 227813 230647 := bstep (se 1 (by rfl) ⟨172985, by rfl⟩ : syracuseStep 230647 = 345971) B345971
theorem B230667 : Blo 227813 230667 := bstep (se 1 (by rfl) ⟨173000, by rfl⟩ : syracuseStep 230667 = 346001) B346001
theorem B230679 : Blo 227813 230679 := bstep (se 1 (by rfl) ⟨173009, by rfl⟩ : syracuseStep 230679 = 346019) B346019
theorem B230699 : Blo 227813 230699 := bstep (se 1 (by rfl) ⟨173024, by rfl⟩ : syracuseStep 230699 = 346049) B346049
theorem B1869101 : Blo 227813 1869101 := bstep (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) B700913
theorem B230711 : Blo 227813 230711 := bstep (se 1 (by rfl) ⟨173033, by rfl⟩ : syracuseStep 230711 = 346067) B346067
theorem B230731 : Blo 227813 230731 := bstep (se 1 (by rfl) ⟨173048, by rfl⟩ : syracuseStep 230731 = 346097) B346097
theorem B230743 : Blo 227813 230743 := bstep (se 1 (by rfl) ⟨173057, by rfl⟩ : syracuseStep 230743 = 346115) B346115
theorem B230763 : Blo 227813 230763 := bstep (se 1 (by rfl) ⟨173072, by rfl⟩ : syracuseStep 230763 = 346145) B346145
theorem B230775 : Blo 227813 230775 := bstep (se 1 (by rfl) ⟨173081, by rfl⟩ : syracuseStep 230775 = 346163) B346163
theorem B230795 : Blo 227813 230795 := bstep (se 1 (by rfl) ⟨173096, by rfl⟩ : syracuseStep 230795 = 346193) B346193
theorem B230807 : Blo 227813 230807 := bstep (se 1 (by rfl) ⟨173105, by rfl⟩ : syracuseStep 230807 = 346211) B346211
theorem B230827 : Blo 227813 230827 := bstep (se 1 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 230827 = 346241) B346241
theorem B656819 : Blo 227813 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B230839 : Blo 227813 230839 := bstep (se 1 (by rfl) ⟨173129, by rfl⟩ : syracuseStep 230839 = 346259) B346259
theorem B230859 : Blo 227813 230859 := bstep (se 1 (by rfl) ⟨173144, by rfl⟩ : syracuseStep 230859 = 346289) B346289
theorem B230871 : Blo 227813 230871 := bstep (se 1 (by rfl) ⟨173153, by rfl⟩ : syracuseStep 230871 = 346307) B346307
theorem B2098649 : Blo 227813 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B230891 : Blo 227813 230891 := bstep (se 1 (by rfl) ⟨173168, by rfl⟩ : syracuseStep 230891 = 346337) B346337
theorem B230903 : Blo 227813 230903 := bstep (se 1 (by rfl) ⟨173177, by rfl⟩ : syracuseStep 230903 = 346355) B346355
theorem B493067 : Blo 227813 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B230923 : Blo 227813 230923 := bstep (se 1 (by rfl) ⟨173192, by rfl⟩ : syracuseStep 230923 = 346385) B346385
theorem B230935 : Blo 227813 230935 := bstep (se 1 (by rfl) ⟨173201, by rfl⟩ : syracuseStep 230935 = 346403) B346403
theorem B230955 : Blo 227813 230955 := bstep (se 1 (by rfl) ⟨173216, by rfl⟩ : syracuseStep 230955 = 346433) B346433
theorem B230967 : Blo 227813 230967 := bstep (se 1 (by rfl) ⟨173225, by rfl⟩ : syracuseStep 230967 = 346451) B346451
theorem B230987 : Blo 227813 230987 := bstep (se 1 (by rfl) ⟨173240, by rfl⟩ : syracuseStep 230987 = 346481) B346481
theorem B230999 : Blo 227813 230999 := bstep (se 1 (by rfl) ⟨173249, by rfl⟩ : syracuseStep 230999 = 346499) B346499
theorem B329303 : Blo 227813 329303 := bstep (se 1 (by rfl) ⟨246977, by rfl⟩ : syracuseStep 329303 = 493955) B493955
theorem B1050205 : Blo 227813 1050205 := bstep (se 3 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 1050205 = 393827) B393827
theorem B231019 : Blo 227813 231019 := bstep (se 1 (by rfl) ⟨173264, by rfl⟩ : syracuseStep 231019 = 346529) B346529
theorem B231031 : Blo 227813 231031 := bstep (se 1 (by rfl) ⟨173273, by rfl⟩ : syracuseStep 231031 = 346547) B346547
theorem B231051 : Blo 227813 231051 := bstep (se 1 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 231051 = 346577) B346577
theorem B231063 : Blo 227813 231063 := bstep (se 1 (by rfl) ⟨173297, by rfl⟩ : syracuseStep 231063 = 346595) B346595
theorem B231083 : Blo 227813 231083 := bstep (se 1 (by rfl) ⟨173312, by rfl⟩ : syracuseStep 231083 = 346625) B346625
theorem B231095 : Blo 227813 231095 := bstep (se 1 (by rfl) ⟨173321, by rfl⟩ : syracuseStep 231095 = 346643) B346643
theorem B493249 : Blo 227813 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B231115 : Blo 227813 231115 := bstep (se 1 (by rfl) ⟨173336, by rfl⟩ : syracuseStep 231115 = 346673) B346673
theorem B231127 : Blo 227813 231127 := bstep (se 1 (by rfl) ⟨173345, by rfl⟩ : syracuseStep 231127 = 346691) B346691
theorem B231147 : Blo 227813 231147 := bstep (se 1 (by rfl) ⟨173360, by rfl⟩ : syracuseStep 231147 = 346721) B346721
theorem B231159 : Blo 227813 231159 := bstep (se 1 (by rfl) ⟨173369, by rfl⟩ : syracuseStep 231159 = 346739) B346739
theorem B231179 : Blo 227813 231179 := bstep (se 1 (by rfl) ⟨173384, by rfl⟩ : syracuseStep 231179 = 346769) B346769
theorem B231191 : Blo 227813 231191 := bstep (se 1 (by rfl) ⟨173393, by rfl⟩ : syracuseStep 231191 = 346787) B346787
theorem B231211 : Blo 227813 231211 := bstep (se 1 (by rfl) ⟨173408, by rfl⟩ : syracuseStep 231211 = 346817) B346817
theorem B231223 : Blo 227813 231223 := bstep (se 1 (by rfl) ⟨173417, by rfl⟩ : syracuseStep 231223 = 346835) B346835
theorem B624449 : Blo 227813 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B231243 : Blo 227813 231243 := bstep (se 1 (by rfl) ⟨173432, by rfl⟩ : syracuseStep 231243 = 346865) B346865
theorem B231255 : Blo 227813 231255 := bstep (se 1 (by rfl) ⟨173441, by rfl⟩ : syracuseStep 231255 = 346883) B346883
theorem B231275 : Blo 227813 231275 := bstep (se 1 (by rfl) ⟨173456, by rfl⟩ : syracuseStep 231275 = 346913) B346913
theorem B231287 : Blo 227813 231287 := bstep (se 1 (by rfl) ⟨173465, by rfl⟩ : syracuseStep 231287 = 346931) B346931
theorem B231307 : Blo 227813 231307 := bstep (se 1 (by rfl) ⟨173480, by rfl⟩ : syracuseStep 231307 = 346961) B346961
theorem B329611 : Blo 227813 329611 := bstep (se 1 (by rfl) ⟨247208, by rfl⟩ : syracuseStep 329611 = 494417) B494417
theorem B231319 : Blo 227813 231319 := bstep (se 1 (by rfl) ⟨173489, by rfl⟩ : syracuseStep 231319 = 346979) B346979
theorem B231339 : Blo 227813 231339 := bstep (se 1 (by rfl) ⟨173504, by rfl⟩ : syracuseStep 231339 = 347009) B347009
theorem B231351 : Blo 227813 231351 := bstep (se 1 (by rfl) ⟨173513, by rfl⟩ : syracuseStep 231351 = 347027) B347027
theorem B231371 : Blo 227813 231371 := bstep (se 1 (by rfl) ⟨173528, by rfl⟩ : syracuseStep 231371 = 347057) B347057
theorem B231383 : Blo 227813 231383 := bstep (se 1 (by rfl) ⟨173537, by rfl⟩ : syracuseStep 231383 = 347075) B347075
theorem B231403 : Blo 227813 231403 := bstep (se 1 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 231403 = 347105) B347105
theorem B231415 : Blo 227813 231415 := bstep (se 1 (by rfl) ⟨173561, by rfl⟩ : syracuseStep 231415 = 347123) B347123
theorem B231435 : Blo 227813 231435 := bstep (se 1 (by rfl) ⟨173576, by rfl⟩ : syracuseStep 231435 = 347153) B347153
theorem B231447 : Blo 227813 231447 := bstep (se 1 (by rfl) ⟨173585, by rfl⟩ : syracuseStep 231447 = 347171) B347171
theorem B231467 : Blo 227813 231467 := bstep (se 1 (by rfl) ⟨173600, by rfl⟩ : syracuseStep 231467 = 347201) B347201
theorem B231479 : Blo 227813 231479 := bstep (se 1 (by rfl) ⟨173609, by rfl⟩ : syracuseStep 231479 = 347219) B347219
theorem B231499 : Blo 227813 231499 := bstep (se 1 (by rfl) ⟨173624, by rfl⟩ : syracuseStep 231499 = 347249) B347249
theorem B231511 : Blo 227813 231511 := bstep (se 1 (by rfl) ⟨173633, by rfl⟩ : syracuseStep 231511 = 347267) B347267
theorem B231531 : Blo 227813 231531 := bstep (se 1 (by rfl) ⟨173648, by rfl⟩ : syracuseStep 231531 = 347297) B347297
theorem B231543 : Blo 227813 231543 := bstep (se 1 (by rfl) ⟨173657, by rfl⟩ : syracuseStep 231543 = 347315) B347315
theorem B231563 : Blo 227813 231563 := bstep (se 1 (by rfl) ⟨173672, by rfl⟩ : syracuseStep 231563 = 347345) B347345
theorem B231575 : Blo 227813 231575 := bstep (se 1 (by rfl) ⟨173681, by rfl⟩ : syracuseStep 231575 = 347363) B347363
theorem B231595 : Blo 227813 231595 := bstep (se 1 (by rfl) ⟨173696, by rfl⟩ : syracuseStep 231595 = 347393) B347393
theorem B1050803 : Blo 227813 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B231607 : Blo 227813 231607 := bstep (se 1 (by rfl) ⟨173705, by rfl⟩ : syracuseStep 231607 = 347411) B347411
theorem B231627 : Blo 227813 231627 := bstep (se 1 (by rfl) ⟨173720, by rfl⟩ : syracuseStep 231627 = 347441) B347441
theorem B231639 : Blo 227813 231639 := bstep (se 1 (by rfl) ⟨173729, by rfl⟩ : syracuseStep 231639 = 347459) B347459
theorem B231659 : Blo 227813 231659 := bstep (se 1 (by rfl) ⟨173744, by rfl⟩ : syracuseStep 231659 = 347489) B347489
theorem B231671 : Blo 227813 231671 := bstep (se 1 (by rfl) ⟨173753, by rfl⟩ : syracuseStep 231671 = 347507) B347507
theorem B231691 : Blo 227813 231691 := bstep (se 1 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 231691 = 347537) B347537
theorem B231703 : Blo 227813 231703 := bstep (se 1 (by rfl) ⟨173777, by rfl⟩ : syracuseStep 231703 = 347555) B347555
theorem B231723 : Blo 227813 231723 := bstep (se 1 (by rfl) ⟨173792, by rfl⟩ : syracuseStep 231723 = 347585) B347585
theorem B231735 : Blo 227813 231735 := bstep (se 1 (by rfl) ⟨173801, by rfl⟩ : syracuseStep 231735 = 347603) B347603
theorem B231755 : Blo 227813 231755 := bstep (se 1 (by rfl) ⟨173816, by rfl⟩ : syracuseStep 231755 = 347633) B347633
theorem B231767 : Blo 227813 231767 := bstep (se 1 (by rfl) ⟨173825, by rfl⟩ : syracuseStep 231767 = 347651) B347651
theorem B493913 : Blo 227813 493913 := bstep (se 2 (by rfl) ⟨185217, by rfl⟩ : syracuseStep 493913 = 370435) B370435
theorem B231787 : Blo 227813 231787 := bstep (se 1 (by rfl) ⟨173840, by rfl⟩ : syracuseStep 231787 = 347681) B347681
theorem B231799 : Blo 227813 231799 := bstep (se 1 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 231799 = 347699) B347699
theorem B985517 : Blo 227813 985517 := bstep (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) B369569
theorem B592307 : Blo 227813 592307 := bstep (se 1 (by rfl) ⟨444230, by rfl⟩ : syracuseStep 592307 = 888461) B888461
theorem B526999 : Blo 227813 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B33852377 : Blo 227813 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B986201 : Blo 227813 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B232555 : Blo 227813 232555 := bstep (se 1 (by rfl) ⟨174416, by rfl⟩ : syracuseStep 232555 = 348833) B348833
theorem B494707 : Blo 227813 494707 := bstep (se 1 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 494707 = 742061) B742061
theorem B789911 : Blo 227813 789911 := bstep (se 1 (by rfl) ⟨592433, by rfl⟩ : syracuseStep 789911 = 1184867) B1184867
theorem B396875 : Blo 227813 396875 := bstep (se 1 (by rfl) ⟨297656, by rfl⟩ : syracuseStep 396875 = 595313) B595313
theorem B626525 : Blo 227813 626525 := bstep (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) B234947
theorem B987329 : Blo 227813 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B659677 : Blo 227813 659677 := bstep (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) B247379
theorem B659735 : Blo 227813 659735 := bstep (se 1 (by rfl) ⟨494801, by rfl⟩ : syracuseStep 659735 = 989603) B989603
theorem B823603 : Blo 227813 823603 := bstep (se 1 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 823603 = 1235405) B1235405
theorem B2625857 : Blo 227813 2625857 := bstep (se 2 (by rfl) ⟨984696, by rfl⟩ : syracuseStep 2625857 = 1969393) B1969393
theorem B3707633 : Blo 227813 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B693323 : Blo 227813 693323 := bstep (se 1 (by rfl) ⟨519992, by rfl⟩ : syracuseStep 693323 = 1039985) B1039985
theorem B1971377 : Blo 227813 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B365771 : Blo 227813 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B2954501 : Blo 227813 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B496919 : Blo 227813 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B1316483 : Blo 227813 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B3348119 : Blo 227813 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B1775321 : Blo 227813 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B1054529 : Blo 227813 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B989003 : Blo 227813 989003 := bstep (se 1 (by rfl) ⟨741752, by rfl⟩ : syracuseStep 989003 = 1483505) B1483505
theorem B1054637 : Blo 227813 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B399371 : Blo 227813 399371 := bstep (se 1 (by rfl) ⟨299528, by rfl⟩ : syracuseStep 399371 = 599057) B599057
theorem B923993 : Blo 227813 923993 := bstep (se 2 (by rfl) ⟨346497, by rfl⟩ : syracuseStep 923993 = 692995) B692995
theorem B367001 : Blo 227813 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B1743281 : Blo 227813 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B694745 : Blo 227813 694745 := bstep (se 2 (by rfl) ⟨260529, by rfl⟩ : syracuseStep 694745 = 521059) B521059
theorem B1153601 : Blo 227813 1153601 := bstep (se 2 (by rfl) ⟨432600, by rfl⟩ : syracuseStep 1153601 = 865201) B865201
theorem B432715 : Blo 227813 432715 := bstep (se 1 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 432715 = 649073) B649073
theorem B990103 : Blo 227813 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B1743767 : Blo 227813 1743767 := bstep (se 1 (by rfl) ⟨1307825, by rfl⟩ : syracuseStep 1743767 = 2615651) B2615651
theorem B760769 : Blo 227813 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B433163 : Blo 227813 433163 := bstep (se 1 (by rfl) ⟨324872, by rfl⟩ : syracuseStep 433163 = 649745) B649745
theorem B466049 : Blo 227813 466049 := bstep (se 2 (by rfl) ⟨174768, by rfl⟩ : syracuseStep 466049 = 349537) B349537
theorem B433345 : Blo 227813 433345 := bstep (se 2 (by rfl) ⟨162504, by rfl⟩ : syracuseStep 433345 = 325009) B325009
theorem B1056203 : Blo 227813 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B433687 : Blo 227813 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B433907 : Blo 227813 433907 := bstep (se 1 (by rfl) ⟨325430, by rfl⟩ : syracuseStep 433907 = 650861) B650861
theorem B925613 : Blo 227813 925613 := bstep (se 3 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 925613 = 347105) B347105
theorem B434135 : Blo 227813 434135 := bstep (se 1 (by rfl) ⟨325601, by rfl⟩ : syracuseStep 434135 = 651203) B651203
theorem B3317777 : Blo 227813 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B4464715 : Blo 227813 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B1646743 : Blo 227813 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B1974451 : Blo 227813 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B434393 : Blo 227813 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B1155545 : Blo 227813 1155545 := bstep (se 2 (by rfl) ⟨433329, by rfl⟩ : syracuseStep 1155545 = 866659) B866659
theorem B3121699 : Blo 227813 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B3711581 : Blo 227813 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B434803 : Blo 227813 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B1647377 : Blo 227813 1647377 := bstep (se 2 (by rfl) ⟨617766, by rfl⟩ : syracuseStep 1647377 = 1235533) B1235533
theorem B10298389 : Blo 227813 10298389 := bstep (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) B482737
theorem B435289 : Blo 227813 435289 := bstep (se 2 (by rfl) ⟨163233, by rfl⟩ : syracuseStep 435289 = 326467) B326467
theorem B435851 : Blo 227813 435851 := bstep (se 1 (by rfl) ⟨326888, by rfl⟩ : syracuseStep 435851 = 653777) B653777
theorem B1681075 : Blo 227813 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B436033 : Blo 227813 436033 := bstep (se 2 (by rfl) ⟨163512, by rfl⟩ : syracuseStep 436033 = 327025) B327025
theorem B1157165 : Blo 227813 1157165 := bstep (se 3 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 1157165 = 433937) B433937
theorem B3549365 : Blo 227813 3549365 := bstep (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) B332753
theorem B1583425 : Blo 227813 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B469505 : Blo 227813 469505 := bstep (se 2 (by rfl) ⟨176064, by rfl⟩ : syracuseStep 469505 = 352129) B352129
theorem B436747 : Blo 227813 436747 := bstep (se 1 (by rfl) ⟨327560, by rfl⟩ : syracuseStep 436747 = 655121) B655121
theorem B928279 : Blo 227813 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B436823 : Blo 227813 436823 := bstep (se 1 (by rfl) ⟨327617, by rfl⟩ : syracuseStep 436823 = 655235) B655235
theorem B240395 : Blo 227813 240395 := bstep (se 1 (by rfl) ⟨180296, by rfl⟩ : syracuseStep 240395 = 360593) B360593
theorem B2206925 : Blo 227813 2206925 := bstep (se 3 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 2206925 = 827597) B827597
theorem B437491 : Blo 227813 437491 := bstep (se 1 (by rfl) ⟨328118, by rfl⟩ : syracuseStep 437491 = 656237) B656237
theorem B437719 : Blo 227813 437719 := bstep (se 1 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 437719 = 656579) B656579
theorem B437825 : Blo 227813 437825 := bstep (se 2 (by rfl) ⟨164184, by rfl⟩ : syracuseStep 437825 = 328369) B328369
theorem B437977 : Blo 227813 437977 := bstep (se 2 (by rfl) ⟨164241, by rfl⟩ : syracuseStep 437977 = 328483) B328483
theorem B2929283 : Blo 227813 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B864989 : Blo 227813 864989 := bstep (se 3 (by rfl) ⟨162185, by rfl⟩ : syracuseStep 864989 = 324371) B324371
theorem B832301 : Blo 227813 832301 := bstep (se 3 (by rfl) ⟨156056, by rfl⟩ : syracuseStep 832301 = 312113) B312113
theorem B439283 : Blo 227813 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B439435 : Blo 227813 439435 := bstep (se 1 (by rfl) ⟨329576, by rfl⟩ : syracuseStep 439435 = 659153) B659153
theorem B439553 : Blo 227813 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B865687 : Blo 227813 865687 := bstep (se 1 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 865687 = 1298531) B1298531
theorem B439769 : Blo 227813 439769 := bstep (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) B329827
theorem B734923 : Blo 227813 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B243415 : Blo 227813 243415 := bstep (se 1 (by rfl) ⟨182561, by rfl⟩ : syracuseStep 243415 = 365123) B365123
theorem B341771 : Blo 227813 341771 := bstep (se 1 (by rfl) ⟨256328, by rfl⟩ : syracuseStep 341771 = 512657) B512657
theorem B341783 : Blo 227813 341783 := bstep (se 1 (by rfl) ⟨256337, by rfl⟩ : syracuseStep 341783 = 512675) B512675
theorem B341849 : Blo 227813 341849 := bstep (se 2 (by rfl) ⟨128193, by rfl⟩ : syracuseStep 341849 = 256387) B256387
theorem B735065 : Blo 227813 735065 := bstep (se 2 (by rfl) ⟨275649, by rfl⟩ : syracuseStep 735065 = 551299) B551299
theorem B1161053 : Blo 227813 1161053 := bstep (se 3 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 1161053 = 435395) B435395
theorem B1947523 : Blo 227813 1947523 := bstep (se 1 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 1947523 = 2921285) B2921285
theorem B309143 : Blo 227813 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B341963 : Blo 227813 341963 := bstep (se 1 (by rfl) ⟨256472, by rfl⟩ : syracuseStep 341963 = 512945) B512945
theorem B341975 : Blo 227813 341975 := bstep (se 1 (by rfl) ⟨256481, by rfl⟩ : syracuseStep 341975 = 512963) B512963
theorem B1751057 : Blo 227813 1751057 := bstep (se 2 (by rfl) ⟨656646, by rfl⟩ : syracuseStep 1751057 = 1313293) B1313293
theorem B342041 : Blo 227813 342041 := bstep (se 2 (by rfl) ⟨128265, by rfl⟩ : syracuseStep 342041 = 256531) B256531
theorem B342155 : Blo 227813 342155 := bstep (se 1 (by rfl) ⟨256616, by rfl⟩ : syracuseStep 342155 = 513233) B513233
theorem B342167 : Blo 227813 342167 := bstep (se 1 (by rfl) ⟨256625, by rfl⟩ : syracuseStep 342167 = 513251) B513251
theorem B866477 : Blo 227813 866477 := bstep (se 3 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 866477 = 324929) B324929
theorem B342233 : Blo 227813 342233 := bstep (se 2 (by rfl) ⟨128337, by rfl⟩ : syracuseStep 342233 = 256675) B256675
theorem B833753 : Blo 227813 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B342347 : Blo 227813 342347 := bstep (se 1 (by rfl) ⟨256760, by rfl⟩ : syracuseStep 342347 = 513521) B513521
theorem B342359 : Blo 227813 342359 := bstep (se 1 (by rfl) ⟨256769, by rfl⟩ : syracuseStep 342359 = 513539) B513539
theorem B342425 : Blo 227813 342425 := bstep (se 2 (by rfl) ⟨128409, by rfl⟩ : syracuseStep 342425 = 256819) B256819
theorem B342539 : Blo 227813 342539 := bstep (se 1 (by rfl) ⟨256904, by rfl⟩ : syracuseStep 342539 = 513809) B513809
theorem B342551 : Blo 227813 342551 := bstep (se 1 (by rfl) ⟨256913, by rfl⟩ : syracuseStep 342551 = 513827) B513827
theorem B309835 : Blo 227813 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B342617 : Blo 227813 342617 := bstep (se 2 (by rfl) ⟨128481, by rfl⟩ : syracuseStep 342617 = 256963) B256963
theorem B375385 : Blo 227813 375385 := bstep (se 2 (by rfl) ⟨140769, by rfl⟩ : syracuseStep 375385 = 281539) B281539
theorem B342731 : Blo 227813 342731 := bstep (se 1 (by rfl) ⟨257048, by rfl⟩ : syracuseStep 342731 = 514097) B514097
theorem B342743 : Blo 227813 342743 := bstep (se 1 (by rfl) ⟨257057, by rfl⟩ : syracuseStep 342743 = 514115) B514115
theorem B342809 : Blo 227813 342809 := bstep (se 2 (by rfl) ⟨128553, by rfl⟩ : syracuseStep 342809 = 257107) B257107
theorem B703283 : Blo 227813 703283 := bstep (se 1 (by rfl) ⟨527462, by rfl⟩ : syracuseStep 703283 = 1054925) B1054925
theorem B1948481 : Blo 227813 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B1653605 : Blo 227813 1653605 := bstep (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) B310051
theorem B342923 : Blo 227813 342923 := bstep (se 1 (by rfl) ⟨257192, by rfl⟩ : syracuseStep 342923 = 514385) B514385
theorem B342935 : Blo 227813 342935 := bstep (se 1 (by rfl) ⟨257201, by rfl⟩ : syracuseStep 342935 = 514403) B514403
theorem B343001 : Blo 227813 343001 := bstep (se 2 (by rfl) ⟨128625, by rfl⟩ : syracuseStep 343001 = 257251) B257251
theorem B343115 : Blo 227813 343115 := bstep (se 1 (by rfl) ⟨257336, by rfl⟩ : syracuseStep 343115 = 514673) B514673
theorem B343127 : Blo 227813 343127 := bstep (se 1 (by rfl) ⟨257345, by rfl⟩ : syracuseStep 343127 = 514691) B514691
theorem B769175 : Blo 227813 769175 := bstep (se 1 (by rfl) ⟨576881, by rfl⟩ : syracuseStep 769175 = 1153763) B1153763
theorem B343193 : Blo 227813 343193 := bstep (se 2 (by rfl) ⟨128697, by rfl⟩ : syracuseStep 343193 = 257395) B257395
theorem B343307 : Blo 227813 343307 := bstep (se 1 (by rfl) ⟨257480, by rfl⟩ : syracuseStep 343307 = 514961) B514961
theorem B933137 : Blo 227813 933137 := bstep (se 2 (by rfl) ⟨349926, by rfl⟩ : syracuseStep 933137 = 699853) B699853
theorem B343319 : Blo 227813 343319 := bstep (se 1 (by rfl) ⟨257489, by rfl⟩ : syracuseStep 343319 = 514979) B514979
theorem B343385 : Blo 227813 343385 := bstep (se 2 (by rfl) ⟨128769, by rfl⟩ : syracuseStep 343385 = 257539) B257539
theorem B245111 : Blo 227813 245111 := bstep (se 1 (by rfl) ⟨183833, by rfl⟩ : syracuseStep 245111 = 367667) B367667
theorem B343499 : Blo 227813 343499 := bstep (se 1 (by rfl) ⟨257624, by rfl⟩ : syracuseStep 343499 = 515249) B515249
theorem B343511 : Blo 227813 343511 := bstep (se 1 (by rfl) ⟨257633, by rfl⟩ : syracuseStep 343511 = 515267) B515267
theorem B343577 : Blo 227813 343577 := bstep (se 2 (by rfl) ⟨128841, by rfl⟩ : syracuseStep 343577 = 257683) B257683
theorem B867905 : Blo 227813 867905 := bstep (se 2 (by rfl) ⟨325464, by rfl⟩ : syracuseStep 867905 = 650929) B650929
theorem B343691 : Blo 227813 343691 := bstep (se 1 (by rfl) ⟨257768, by rfl⟩ : syracuseStep 343691 = 515537) B515537
theorem B343703 : Blo 227813 343703 := bstep (se 1 (by rfl) ⟨257777, by rfl⟩ : syracuseStep 343703 = 515555) B515555
theorem B769715 : Blo 227813 769715 := bstep (se 1 (by rfl) ⟨577286, by rfl⟩ : syracuseStep 769715 = 1154573) B1154573
theorem B343769 : Blo 227813 343769 := bstep (se 2 (by rfl) ⟨128913, by rfl⟩ : syracuseStep 343769 = 257827) B257827
theorem B736985 : Blo 227813 736985 := bstep (se 2 (by rfl) ⟨276369, by rfl⟩ : syracuseStep 736985 = 552739) B552739
theorem B343883 : Blo 227813 343883 := bstep (se 1 (by rfl) ⟨257912, by rfl⟩ : syracuseStep 343883 = 515825) B515825
theorem B343895 : Blo 227813 343895 := bstep (se 1 (by rfl) ⟨257921, by rfl⟩ : syracuseStep 343895 = 515843) B515843
theorem B1163159 : Blo 227813 1163159 := bstep (se 1 (by rfl) ⟨872369, by rfl⟩ : syracuseStep 1163159 = 1744739) B1744739
theorem B343961 : Blo 227813 343961 := bstep (se 2 (by rfl) ⟨128985, by rfl⟩ : syracuseStep 343961 = 257971) B257971
theorem B769985 : Blo 227813 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B344075 : Blo 227813 344075 := bstep (se 1 (by rfl) ⟨258056, by rfl⟩ : syracuseStep 344075 = 516113) B516113
theorem B344087 : Blo 227813 344087 := bstep (se 1 (by rfl) ⟨258065, by rfl⟩ : syracuseStep 344087 = 516131) B516131
theorem B344153 : Blo 227813 344153 := bstep (se 2 (by rfl) ⟨129057, by rfl⟩ : syracuseStep 344153 = 258115) B258115
theorem B344267 : Blo 227813 344267 := bstep (se 1 (by rfl) ⟨258200, by rfl⟩ : syracuseStep 344267 = 516401) B516401
theorem B344279 : Blo 227813 344279 := bstep (se 1 (by rfl) ⟨258209, by rfl⟩ : syracuseStep 344279 = 516419) B516419
theorem B344345 : Blo 227813 344345 := bstep (se 2 (by rfl) ⟨129129, by rfl⟩ : syracuseStep 344345 = 258259) B258259
theorem B344459 : Blo 227813 344459 := bstep (se 1 (by rfl) ⟨258344, by rfl⟩ : syracuseStep 344459 = 516689) B516689
theorem B344471 : Blo 227813 344471 := bstep (se 1 (by rfl) ⟨258353, by rfl⟩ : syracuseStep 344471 = 516707) B516707
theorem B344537 : Blo 227813 344537 := bstep (se 2 (by rfl) ⟨129201, by rfl⟩ : syracuseStep 344537 = 258403) B258403
theorem B770525 : Blo 227813 770525 := bstep (se 3 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 770525 = 288947) B288947
theorem B344651 : Blo 227813 344651 := bstep (se 1 (by rfl) ⟨258488, by rfl⟩ : syracuseStep 344651 = 516977) B516977
theorem B1327691 : Blo 227813 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B344663 : Blo 227813 344663 := bstep (se 1 (by rfl) ⟨258497, by rfl⟩ : syracuseStep 344663 = 516995) B516995
theorem B344729 : Blo 227813 344729 := bstep (se 2 (by rfl) ⟨129273, by rfl⟩ : syracuseStep 344729 = 258547) B258547
theorem B344843 : Blo 227813 344843 := bstep (se 1 (by rfl) ⟨258632, by rfl⟩ : syracuseStep 344843 = 517265) B517265
theorem B1327889 : Blo 227813 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B344855 : Blo 227813 344855 := bstep (se 1 (by rfl) ⟨258641, by rfl⟩ : syracuseStep 344855 = 517283) B517283
theorem B344921 : Blo 227813 344921 := bstep (se 2 (by rfl) ⟨129345, by rfl⟩ : syracuseStep 344921 = 258691) B258691
theorem B345035 : Blo 227813 345035 := bstep (se 1 (by rfl) ⟨258776, by rfl⟩ : syracuseStep 345035 = 517553) B517553
theorem B345047 : Blo 227813 345047 := bstep (se 1 (by rfl) ⟨258785, by rfl⟩ : syracuseStep 345047 = 517571) B517571
theorem B869393 : Blo 227813 869393 := bstep (se 2 (by rfl) ⟨326022, by rfl⟩ : syracuseStep 869393 = 652045) B652045
theorem B345113 : Blo 227813 345113 := bstep (se 2 (by rfl) ⟨129417, by rfl⟩ : syracuseStep 345113 = 258835) B258835
theorem B2638979 : Blo 227813 2638979 := bstep (se 1 (by rfl) ⟨1979234, by rfl⟩ : syracuseStep 2638979 = 3958469) B3958469
theorem B345227 : Blo 227813 345227 := bstep (se 1 (by rfl) ⟨258920, by rfl⟩ : syracuseStep 345227 = 517841) B517841
theorem B345239 : Blo 227813 345239 := bstep (se 1 (by rfl) ⟨258929, by rfl⟩ : syracuseStep 345239 = 517859) B517859
theorem B246935 : Blo 227813 246935 := bstep (se 1 (by rfl) ⟨185201, by rfl⟩ : syracuseStep 246935 = 370403) B370403
theorem B345305 : Blo 227813 345305 := bstep (se 2 (by rfl) ⟨129489, by rfl⟩ : syracuseStep 345305 = 258979) B258979
theorem B1361197 : Blo 227813 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B345419 : Blo 227813 345419 := bstep (se 1 (by rfl) ⟨259064, by rfl⟩ : syracuseStep 345419 = 518129) B518129
theorem B345431 : Blo 227813 345431 := bstep (se 1 (by rfl) ⟨259073, by rfl⟩ : syracuseStep 345431 = 518147) B518147
theorem B411031 : Blo 227813 411031 := bstep (se 1 (by rfl) ⟨308273, by rfl⟩ : syracuseStep 411031 = 616547) B616547
theorem B345497 : Blo 227813 345497 := bstep (se 2 (by rfl) ⟨129561, by rfl⟩ : syracuseStep 345497 = 259123) B259123
theorem B411095 : Blo 227813 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B869849 : Blo 227813 869849 := bstep (se 2 (by rfl) ⟨326193, by rfl⟩ : syracuseStep 869849 = 652387) B652387
theorem B345611 : Blo 227813 345611 := bstep (se 1 (by rfl) ⟨259208, by rfl⟩ : syracuseStep 345611 = 518417) B518417
theorem B345623 : Blo 227813 345623 := bstep (se 1 (by rfl) ⟨259217, by rfl⟩ : syracuseStep 345623 = 518435) B518435
theorem B706099 : Blo 227813 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B247351 : Blo 227813 247351 := bstep (se 1 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 247351 = 371027) B371027
theorem B771659 : Blo 227813 771659 := bstep (se 1 (by rfl) ⟨578744, by rfl⟩ : syracuseStep 771659 = 1157489) B1157489
theorem B345689 : Blo 227813 345689 := bstep (se 2 (by rfl) ⟨129633, by rfl⟩ : syracuseStep 345689 = 259267) B259267
theorem B1328791 : Blo 227813 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B870061 : Blo 227813 870061 := bstep (se 3 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 870061 = 326273) B326273
theorem B345803 : Blo 227813 345803 := bstep (se 1 (by rfl) ⟨259352, by rfl⟩ : syracuseStep 345803 = 518705) B518705
theorem B345815 : Blo 227813 345815 := bstep (se 1 (by rfl) ⟨259361, by rfl⟩ : syracuseStep 345815 = 518723) B518723
theorem B345881 : Blo 227813 345881 := bstep (se 2 (by rfl) ⟨129705, by rfl⟩ : syracuseStep 345881 = 259411) B259411
theorem B1754945 : Blo 227813 1754945 := bstep (se 2 (by rfl) ⟨658104, by rfl⟩ : syracuseStep 1754945 = 1316209) B1316209
theorem B771929 : Blo 227813 771929 := bstep (se 2 (by rfl) ⟨289473, by rfl⟩ : syracuseStep 771929 = 578947) B578947
theorem B739165 : Blo 227813 739165 := bstep (se 3 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 739165 = 277187) B277187
theorem B345995 : Blo 227813 345995 := bstep (se 1 (by rfl) ⟨259496, by rfl⟩ : syracuseStep 345995 = 518993) B518993
theorem B673687 : Blo 227813 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B346007 : Blo 227813 346007 := bstep (se 1 (by rfl) ⟨259505, by rfl⟩ : syracuseStep 346007 = 519011) B519011
theorem B346073 : Blo 227813 346073 := bstep (se 2 (by rfl) ⟨129777, by rfl⟩ : syracuseStep 346073 = 259555) B259555
theorem B870365 : Blo 227813 870365 := bstep (se 3 (by rfl) ⟨163193, by rfl⟩ : syracuseStep 870365 = 326387) B326387
theorem B346187 : Blo 227813 346187 := bstep (se 1 (by rfl) ⟨259640, by rfl⟩ : syracuseStep 346187 = 519281) B519281
theorem B346199 : Blo 227813 346199 := bstep (se 1 (by rfl) ⟨259649, by rfl⟩ : syracuseStep 346199 = 519299) B519299
theorem B346265 : Blo 227813 346265 := bstep (se 2 (by rfl) ⟨129849, by rfl⟩ : syracuseStep 346265 = 259699) B259699
theorem B936157 : Blo 227813 936157 := bstep (se 3 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 936157 = 351059) B351059
theorem B346379 : Blo 227813 346379 := bstep (se 1 (by rfl) ⟨259784, by rfl⟩ : syracuseStep 346379 = 519569) B519569
theorem B346391 : Blo 227813 346391 := bstep (se 1 (by rfl) ⟨259793, by rfl⟩ : syracuseStep 346391 = 519587) B519587
theorem B346457 : Blo 227813 346457 := bstep (se 2 (by rfl) ⟨129921, by rfl⟩ : syracuseStep 346457 = 259843) B259843
theorem B346571 : Blo 227813 346571 := bstep (se 1 (by rfl) ⟨259928, by rfl⟩ : syracuseStep 346571 = 519857) B519857
theorem B346583 : Blo 227813 346583 := bstep (se 1 (by rfl) ⟨259937, by rfl⟩ : syracuseStep 346583 = 519875) B519875
theorem B707033 : Blo 227813 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B412147 : Blo 227813 412147 := bstep (se 1 (by rfl) ⟨309110, by rfl⟩ : syracuseStep 412147 = 618221) B618221
theorem B772631 : Blo 227813 772631 := bstep (se 1 (by rfl) ⟨579473, by rfl⟩ : syracuseStep 772631 = 1158947) B1158947
theorem B346649 : Blo 227813 346649 := bstep (se 2 (by rfl) ⟨129993, by rfl⟩ : syracuseStep 346649 = 259987) B259987
theorem B346763 : Blo 227813 346763 := bstep (se 1 (by rfl) ⟨260072, by rfl⟩ : syracuseStep 346763 = 520145) B520145
theorem B346775 : Blo 227813 346775 := bstep (se 1 (by rfl) ⟨260081, by rfl⟩ : syracuseStep 346775 = 520163) B520163
theorem B3721909 : Blo 227813 3721909 := bstep (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) B348929
theorem B346841 : Blo 227813 346841 := bstep (se 2 (by rfl) ⟨130065, by rfl⟩ : syracuseStep 346841 = 260131) B260131
theorem B936769 : Blo 227813 936769 := bstep (se 2 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 936769 = 702577) B702577
theorem B346955 : Blo 227813 346955 := bstep (se 1 (by rfl) ⟨260216, by rfl⟩ : syracuseStep 346955 = 520433) B520433
theorem B346967 : Blo 227813 346967 := bstep (se 1 (by rfl) ⟨260225, by rfl⟩ : syracuseStep 346967 = 520451) B520451
theorem B347033 : Blo 227813 347033 := bstep (se 2 (by rfl) ⟨130137, by rfl⟩ : syracuseStep 347033 = 260275) B260275
theorem B412609 : Blo 227813 412609 := bstep (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) B309457
theorem B347147 : Blo 227813 347147 := bstep (se 1 (by rfl) ⟨260360, by rfl⟩ : syracuseStep 347147 = 520721) B520721
theorem B347159 : Blo 227813 347159 := bstep (se 1 (by rfl) ⟨260369, by rfl⟩ : syracuseStep 347159 = 520739) B520739
theorem B773171 : Blo 227813 773171 := bstep (se 1 (by rfl) ⟨579878, by rfl⟩ : syracuseStep 773171 = 1159757) B1159757
theorem B347225 : Blo 227813 347225 := bstep (se 2 (by rfl) ⟨130209, by rfl⟩ : syracuseStep 347225 = 260419) B260419
theorem B347339 : Blo 227813 347339 := bstep (se 1 (by rfl) ⟨260504, by rfl⟩ : syracuseStep 347339 = 521009) B521009
theorem B347351 : Blo 227813 347351 := bstep (se 1 (by rfl) ⟨260513, by rfl⟩ : syracuseStep 347351 = 521027) B521027
theorem B576791 : Blo 227813 576791 := bstep (se 1 (by rfl) ⟨432593, by rfl⟩ : syracuseStep 576791 = 865187) B865187
theorem B347417 : Blo 227813 347417 := bstep (se 2 (by rfl) ⟨130281, by rfl⟩ : syracuseStep 347417 = 260563) B260563
theorem B4443437 : Blo 227813 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B773441 : Blo 227813 773441 := bstep (se 2 (by rfl) ⟨290040, by rfl⟩ : syracuseStep 773441 = 580081) B580081
theorem B1166723 : Blo 227813 1166723 := bstep (se 1 (by rfl) ⟨875042, by rfl⟩ : syracuseStep 1166723 = 1750085) B1750085
theorem B347531 : Blo 227813 347531 := bstep (se 1 (by rfl) ⟨260648, by rfl⟩ : syracuseStep 347531 = 521297) B521297
theorem B347543 : Blo 227813 347543 := bstep (se 1 (by rfl) ⟨260657, by rfl⟩ : syracuseStep 347543 = 521315) B521315
theorem B347609 : Blo 227813 347609 := bstep (se 2 (by rfl) ⟨130353, by rfl⟩ : syracuseStep 347609 = 260707) B260707
theorem B413171 : Blo 227813 413171 := bstep (se 1 (by rfl) ⟨309878, by rfl⟩ : syracuseStep 413171 = 619757) B619757
theorem B1756889 : Blo 227813 1756889 := bstep (se 2 (by rfl) ⟨658833, by rfl⟩ : syracuseStep 1756889 = 1317667) B1317667
theorem B773981 : Blo 227813 773981 := bstep (se 3 (by rfl) ⟨145121, by rfl⟩ : syracuseStep 773981 = 290243) B290243
theorem B577601 : Blo 227813 577601 := bstep (se 2 (by rfl) ⟨216600, by rfl⟩ : syracuseStep 577601 = 433201) B433201
theorem B414209 : Blo 227813 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B872963 : Blo 227813 872963 := bstep (se 1 (by rfl) ⟨654722, by rfl⟩ : syracuseStep 872963 = 1309445) B1309445
theorem B2118149 : Blo 227813 2118149 := bstep (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) B397153
theorem B872977 : Blo 227813 872977 := bstep (se 2 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 872977 = 654733) B654733
theorem B578137 : Blo 227813 578137 := bstep (se 2 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 578137 = 433603) B433603
theorem B1462963 : Blo 227813 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B512729 : Blo 227813 512729 := bstep (se 2 (by rfl) ⟨192273, by rfl⟩ : syracuseStep 512729 = 384547) B384547
theorem B512819 : Blo 227813 512819 := bstep (se 1 (by rfl) ⟨384614, by rfl⟩ : syracuseStep 512819 = 769229) B769229
theorem B873281 : Blo 227813 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B512855 : Blo 227813 512855 := bstep (se 1 (by rfl) ⟨384641, by rfl⟩ : syracuseStep 512855 = 769283) B769283
theorem B349015 : Blo 227813 349015 := bstep (se 1 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 349015 = 523523) B523523
theorem B250763 : Blo 227813 250763 := bstep (se 1 (by rfl) ⟨188072, by rfl⟩ : syracuseStep 250763 = 376145) B376145
theorem B775115 : Blo 227813 775115 := bstep (se 1 (by rfl) ⟨581336, by rfl⟩ : syracuseStep 775115 = 1162673) B1162673
theorem B513011 : Blo 227813 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B513035 : Blo 227813 513035 := bstep (se 1 (by rfl) ⟨384776, by rfl⟩ : syracuseStep 513035 = 769553) B769553
theorem B513089 : Blo 227813 513089 := bstep (se 2 (by rfl) ⟨192408, by rfl⟩ : syracuseStep 513089 = 384817) B384817
theorem B775385 : Blo 227813 775385 := bstep (se 2 (by rfl) ⟨290769, by rfl⟩ : syracuseStep 775385 = 581539) B581539
theorem B4216049 : Blo 227813 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B513305 : Blo 227813 513305 := bstep (se 2 (by rfl) ⟨192489, by rfl⟩ : syracuseStep 513305 = 384979) B384979
theorem B513395 : Blo 227813 513395 := bstep (se 1 (by rfl) ⟨385046, by rfl⟩ : syracuseStep 513395 = 770093) B770093
theorem B513431 : Blo 227813 513431 := bstep (se 1 (by rfl) ⟨385073, by rfl⟩ : syracuseStep 513431 = 770147) B770147
theorem B873949 : Blo 227813 873949 := bstep (se 3 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 873949 = 327731) B327731
theorem B513611 : Blo 227813 513611 := bstep (se 1 (by rfl) ⟨385208, by rfl⟩ : syracuseStep 513611 = 770417) B770417
theorem B513665 : Blo 227813 513665 := bstep (se 2 (by rfl) ⟨192624, by rfl⟩ : syracuseStep 513665 = 385249) B385249
theorem B579251 : Blo 227813 579251 := bstep (se 1 (by rfl) ⟨434438, by rfl⟩ : syracuseStep 579251 = 868877) B868877
theorem B513881 : Blo 227813 513881 := bstep (se 2 (by rfl) ⟨192705, by rfl⟩ : syracuseStep 513881 = 385411) B385411
theorem B776087 : Blo 227813 776087 := bstep (se 1 (by rfl) ⟨582065, by rfl⟩ : syracuseStep 776087 = 1164131) B1164131
theorem B513971 : Blo 227813 513971 := bstep (se 1 (by rfl) ⟨385478, by rfl⟩ : syracuseStep 513971 = 770957) B770957
theorem B514007 : Blo 227813 514007 := bstep (se 1 (by rfl) ⟨385505, by rfl⟩ : syracuseStep 514007 = 771011) B771011
theorem B579545 : Blo 227813 579545 := bstep (se 2 (by rfl) ⟨217329, by rfl⟩ : syracuseStep 579545 = 434659) B434659
theorem B3299363 : Blo 227813 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B514187 : Blo 227813 514187 := bstep (se 1 (by rfl) ⟨385640, by rfl⟩ : syracuseStep 514187 = 771281) B771281
theorem B514241 : Blo 227813 514241 := bstep (se 2 (by rfl) ⟨192840, by rfl⟩ : syracuseStep 514241 = 385681) B385681
theorem B1300697 : Blo 227813 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B2644289 : Blo 227813 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B514457 : Blo 227813 514457 := bstep (se 2 (by rfl) ⟨192921, by rfl⟩ : syracuseStep 514457 = 385843) B385843
theorem B776627 : Blo 227813 776627 := bstep (se 1 (by rfl) ⟨582470, by rfl⟩ : syracuseStep 776627 = 1164941) B1164941
theorem B514547 : Blo 227813 514547 := bstep (se 1 (by rfl) ⟨385910, by rfl⟩ : syracuseStep 514547 = 771821) B771821
theorem B1989137 : Blo 227813 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1104401 : Blo 227813 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B514583 : Blo 227813 514583 := bstep (se 1 (by rfl) ⟨385937, by rfl⟩ : syracuseStep 514583 = 771875) B771875
theorem B416279 : Blo 227813 416279 := bstep (se 1 (by rfl) ⟨312209, by rfl⟩ : syracuseStep 416279 = 624419) B624419
theorem B1464925 : Blo 227813 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B776897 : Blo 227813 776897 := bstep (se 2 (by rfl) ⟨291336, by rfl⟩ : syracuseStep 776897 = 582673) B582673
theorem B514763 : Blo 227813 514763 := bstep (se 1 (by rfl) ⟨386072, by rfl⟩ : syracuseStep 514763 = 772145) B772145
theorem B875225 : Blo 227813 875225 := bstep (se 2 (by rfl) ⟨328209, by rfl⟩ : syracuseStep 875225 = 656419) B656419
theorem B514817 : Blo 227813 514817 := bstep (se 2 (by rfl) ⟨193056, by rfl⟩ : syracuseStep 514817 = 386113) B386113
theorem B1170251 : Blo 227813 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B515033 : Blo 227813 515033 := bstep (se 2 (by rfl) ⟨193137, by rfl⟩ : syracuseStep 515033 = 386275) B386275
theorem B1170449 : Blo 227813 1170449 := bstep (se 2 (by rfl) ⟨438918, by rfl⟩ : syracuseStep 1170449 = 877837) B877837
theorem B1760291 : Blo 227813 1760291 := bstep (se 1 (by rfl) ⟨1320218, by rfl⟩ : syracuseStep 1760291 = 2640437) B2640437
theorem B1104941 : Blo 227813 1104941 := bstep (se 3 (by rfl) ⟨207176, by rfl⟩ : syracuseStep 1104941 = 414353) B414353
theorem B515123 : Blo 227813 515123 := bstep (se 1 (by rfl) ⟨386342, by rfl⟩ : syracuseStep 515123 = 772685) B772685
theorem B515159 : Blo 227813 515159 := bstep (se 1 (by rfl) ⟨386369, by rfl⟩ : syracuseStep 515159 = 772739) B772739
theorem B1170611 : Blo 227813 1170611 := bstep (se 1 (by rfl) ⟨877958, by rfl⟩ : syracuseStep 1170611 = 1755917) B1755917
theorem B777437 : Blo 227813 777437 := bstep (se 3 (by rfl) ⟨145769, by rfl⟩ : syracuseStep 777437 = 291539) B291539
theorem B515339 : Blo 227813 515339 := bstep (se 1 (by rfl) ⟨386504, by rfl⟩ : syracuseStep 515339 = 773009) B773009
theorem B515393 : Blo 227813 515393 := bstep (se 2 (by rfl) ⟨193272, by rfl⟩ : syracuseStep 515393 = 386545) B386545
theorem B548299 : Blo 227813 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B384473 : Blo 227813 384473 := bstep (se 2 (by rfl) ⟨144177, by rfl⟩ : syracuseStep 384473 = 288355) B288355
theorem B515609 : Blo 227813 515609 := bstep (se 2 (by rfl) ⟨193353, by rfl⟩ : syracuseStep 515609 = 386707) B386707
theorem B581195 : Blo 227813 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B384601 : Blo 227813 384601 := bstep (se 2 (by rfl) ⟨144225, by rfl⟩ : syracuseStep 384601 = 288451) B288451
theorem B515699 : Blo 227813 515699 := bstep (se 1 (by rfl) ⟨386774, by rfl⟩ : syracuseStep 515699 = 773549) B773549
theorem B515735 : Blo 227813 515735 := bstep (se 1 (by rfl) ⟨386801, by rfl⟩ : syracuseStep 515735 = 773603) B773603
theorem B515915 : Blo 227813 515915 := bstep (se 1 (by rfl) ⟨386936, by rfl⟩ : syracuseStep 515915 = 773873) B773873
theorem B417611 : Blo 227813 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B515969 : Blo 227813 515969 := bstep (se 2 (by rfl) ⟨193488, by rfl⟩ : syracuseStep 515969 = 386977) B386977
theorem B516185 : Blo 227813 516185 := bstep (se 2 (by rfl) ⟨193569, by rfl⟩ : syracuseStep 516185 = 387139) B387139
theorem B385175 : Blo 227813 385175 := bstep (se 1 (by rfl) ⟨288881, by rfl⟩ : syracuseStep 385175 = 577763) B577763
theorem B516275 : Blo 227813 516275 := bstep (se 1 (by rfl) ⟨387206, by rfl⟩ : syracuseStep 516275 = 774413) B774413
theorem B516311 : Blo 227813 516311 := bstep (se 1 (by rfl) ⟨387233, by rfl⟩ : syracuseStep 516311 = 774467) B774467
theorem B385303 : Blo 227813 385303 := bstep (se 1 (by rfl) ⟨288977, by rfl⟩ : syracuseStep 385303 = 577955) B577955
theorem B876851 : Blo 227813 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B876865 : Blo 227813 876865 := bstep (se 2 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 876865 = 657649) B657649
theorem B778571 : Blo 227813 778571 := bstep (se 1 (by rfl) ⟨583928, by rfl⟩ : syracuseStep 778571 = 1167857) B1167857
theorem B8348021 : Blo 227813 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B516491 : Blo 227813 516491 := bstep (se 1 (by rfl) ⟨387368, by rfl⟩ : syracuseStep 516491 = 774737) B774737
theorem B549271 : Blo 227813 549271 := bstep (se 1 (by rfl) ⟨411953, by rfl⟩ : syracuseStep 549271 = 823907) B823907
theorem B516545 : Blo 227813 516545 := bstep (se 2 (by rfl) ⟨193704, by rfl⟩ : syracuseStep 516545 = 387409) B387409
theorem B582167 : Blo 227813 582167 := bstep (se 1 (by rfl) ⟨436625, by rfl⟩ : syracuseStep 582167 = 873251) B873251
theorem B1663523 : Blo 227813 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B778841 : Blo 227813 778841 := bstep (se 2 (by rfl) ⟨292065, by rfl⟩ : syracuseStep 778841 = 584131) B584131
theorem B516761 : Blo 227813 516761 := bstep (se 2 (by rfl) ⟨193785, by rfl⟩ : syracuseStep 516761 = 387571) B387571
theorem B975539 : Blo 227813 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B516851 : Blo 227813 516851 := bstep (se 1 (by rfl) ⟨387638, by rfl⟩ : syracuseStep 516851 = 775277) B775277
theorem B516887 : Blo 227813 516887 := bstep (se 1 (by rfl) ⟨387665, by rfl⟩ : syracuseStep 516887 = 775331) B775331
theorem B1303361 : Blo 227813 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B385931 : Blo 227813 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B2614193 : Blo 227813 2614193 := bstep (se 2 (by rfl) ⟨980322, by rfl⟩ : syracuseStep 2614193 = 1960645) B1960645
theorem B517067 : Blo 227813 517067 := bstep (se 1 (by rfl) ⟨387800, by rfl⟩ : syracuseStep 517067 = 775601) B775601
theorem B1860569 : Blo 227813 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B517121 : Blo 227813 517121 := bstep (se 2 (by rfl) ⟨193920, by rfl⟩ : syracuseStep 517121 = 387841) B387841
theorem B386059 : Blo 227813 386059 := bstep (se 1 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 386059 = 579089) B579089
theorem B1467409 : Blo 227813 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B1172555 : Blo 227813 1172555 := bstep (se 1 (by rfl) ⟨879416, by rfl⟩ : syracuseStep 1172555 = 1758833) B1758833
theorem B1959005 : Blo 227813 1959005 := bstep (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) B734627
theorem B386201 : Blo 227813 386201 := bstep (se 2 (by rfl) ⟨144825, by rfl⟩ : syracuseStep 386201 = 289651) B289651
theorem B582835 : Blo 227813 582835 := bstep (se 1 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 582835 = 874253) B874253
theorem B517337 : Blo 227813 517337 := bstep (se 2 (by rfl) ⟨194001, by rfl⟩ : syracuseStep 517337 = 388003) B388003
theorem B779543 : Blo 227813 779543 := bstep (se 1 (by rfl) ⟨584657, by rfl⟩ : syracuseStep 779543 = 1169315) B1169315
theorem B386329 : Blo 227813 386329 := bstep (se 2 (by rfl) ⟨144873, by rfl⟩ : syracuseStep 386329 = 289747) B289747
theorem B845101 : Blo 227813 845101 := bstep (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) B316913
theorem B1336621 : Blo 227813 1336621 := bstep (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) B501233
theorem B517427 : Blo 227813 517427 := bstep (se 1 (by rfl) ⟨388070, by rfl⟩ : syracuseStep 517427 = 776141) B776141
theorem B582977 : Blo 227813 582977 := bstep (se 2 (by rfl) ⟨218616, by rfl⟩ : syracuseStep 582977 = 437233) B437233
theorem B517463 : Blo 227813 517463 := bstep (se 1 (by rfl) ⟨388097, by rfl⟩ : syracuseStep 517463 = 776195) B776195
theorem B2352563 : Blo 227813 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B517643 : Blo 227813 517643 := bstep (se 1 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 517643 = 776465) B776465
theorem B517697 : Blo 227813 517697 := bstep (se 2 (by rfl) ⟨194136, by rfl⟩ : syracuseStep 517697 = 388273) B388273
theorem B517913 : Blo 227813 517913 := bstep (se 2 (by rfl) ⟨194217, by rfl⟩ : syracuseStep 517913 = 388435) B388435
theorem B780083 : Blo 227813 780083 := bstep (se 1 (by rfl) ⟨585062, by rfl⟩ : syracuseStep 780083 = 1170125) B1170125
theorem B386903 : Blo 227813 386903 := bstep (se 1 (by rfl) ⟨290177, by rfl⟩ : syracuseStep 386903 = 580355) B580355
theorem B518003 : Blo 227813 518003 := bstep (se 1 (by rfl) ⟨388502, by rfl⟩ : syracuseStep 518003 = 777005) B777005
theorem B518039 : Blo 227813 518039 := bstep (se 1 (by rfl) ⟨388529, by rfl⟩ : syracuseStep 518039 = 777059) B777059
theorem B387031 : Blo 227813 387031 := bstep (se 1 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 387031 = 580547) B580547
theorem B780353 : Blo 227813 780353 := bstep (se 2 (by rfl) ⟨292632, by rfl⟩ : syracuseStep 780353 = 585265) B585265
theorem B518219 : Blo 227813 518219 := bstep (se 1 (by rfl) ⟨388664, by rfl⟩ : syracuseStep 518219 = 777329) B777329
theorem B518273 : Blo 227813 518273 := bstep (se 2 (by rfl) ⟨194352, by rfl⟩ : syracuseStep 518273 = 388705) B388705
theorem B878795 : Blo 227813 878795 := bstep (se 1 (by rfl) ⟨659096, by rfl⟩ : syracuseStep 878795 = 1318193) B1318193
theorem B878809 : Blo 227813 878809 := bstep (se 2 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 878809 = 659107) B659107
theorem B289099 : Blo 227813 289099 := bstep (se 1 (by rfl) ⟨216824, by rfl⟩ : syracuseStep 289099 = 433649) B433649
theorem B518489 : Blo 227813 518489 := bstep (se 2 (by rfl) ⟨194433, by rfl⟩ : syracuseStep 518489 = 388867) B388867
theorem B518579 : Blo 227813 518579 := bstep (se 1 (by rfl) ⟨388934, by rfl⟩ : syracuseStep 518579 = 777869) B777869
theorem B256459 : Blo 227813 256459 := bstep (se 1 (by rfl) ⟨192344, by rfl⟩ : syracuseStep 256459 = 384689) B384689
theorem B518615 : Blo 227813 518615 := bstep (se 1 (by rfl) ⟨388961, by rfl⟩ : syracuseStep 518615 = 777923) B777923
theorem B977453 : Blo 227813 977453 := bstep (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) B366545
theorem B584243 : Blo 227813 584243 := bstep (se 1 (by rfl) ⟨438182, by rfl⟩ : syracuseStep 584243 = 876365) B876365
theorem B256567 : Blo 227813 256567 := bstep (se 1 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 256567 = 384851) B384851
theorem B387659 : Blo 227813 387659 := bstep (se 1 (by rfl) ⟨290744, by rfl⟩ : syracuseStep 387659 = 581489) B581489
theorem B2255435 : Blo 227813 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B780893 : Blo 227813 780893 := bstep (se 3 (by rfl) ⟨146417, by rfl⟩ : syracuseStep 780893 = 292835) B292835
theorem B518795 : Blo 227813 518795 := bstep (se 1 (by rfl) ⟨389096, by rfl⟩ : syracuseStep 518795 = 778193) B778193
theorem B518849 : Blo 227813 518849 := bstep (se 2 (by rfl) ⟨194568, by rfl⟩ : syracuseStep 518849 = 389137) B389137
theorem B387787 : Blo 227813 387787 := bstep (se 1 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 387787 = 581681) B581681
theorem B256747 : Blo 227813 256747 := bstep (se 1 (by rfl) ⟨192560, by rfl⟩ : syracuseStep 256747 = 385121) B385121
theorem B256855 : Blo 227813 256855 := bstep (se 1 (by rfl) ⟨192641, by rfl⟩ : syracuseStep 256855 = 385283) B385283
theorem B387929 : Blo 227813 387929 := bstep (se 2 (by rfl) ⟨145473, by rfl⟩ : syracuseStep 387929 = 290947) B290947
theorem B977795 : Blo 227813 977795 := bstep (se 1 (by rfl) ⟨733346, by rfl⟩ : syracuseStep 977795 = 1466693) B1466693
theorem B519065 : Blo 227813 519065 := bstep (se 2 (by rfl) ⟨194649, by rfl⟩ : syracuseStep 519065 = 389299) B389299
theorem B650177 : Blo 227813 650177 := bstep (se 2 (by rfl) ⟨243816, by rfl⟩ : syracuseStep 650177 = 487633) B487633
theorem B388057 : Blo 227813 388057 := bstep (se 2 (by rfl) ⟨145521, by rfl⟩ : syracuseStep 388057 = 291043) B291043
theorem B519155 : Blo 227813 519155 := bstep (se 1 (by rfl) ⟨389366, by rfl⟩ : syracuseStep 519155 = 778733) B778733
theorem B257035 : Blo 227813 257035 := bstep (se 1 (by rfl) ⟨192776, by rfl⟩ : syracuseStep 257035 = 385553) B385553
theorem B519191 : Blo 227813 519191 := bstep (se 1 (by rfl) ⟨389393, by rfl⟩ : syracuseStep 519191 = 778787) B778787
theorem B584779 : Blo 227813 584779 := bstep (se 1 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 584779 = 877169) B877169
theorem B257143 : Blo 227813 257143 := bstep (se 1 (by rfl) ⟨192857, by rfl⟩ : syracuseStep 257143 = 385715) B385715
theorem B879767 : Blo 227813 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B519371 : Blo 227813 519371 := bstep (se 1 (by rfl) ⟨389528, by rfl⟩ : syracuseStep 519371 = 779057) B779057
theorem B584921 : Blo 227813 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B519425 : Blo 227813 519425 := bstep (se 2 (by rfl) ⟨194784, by rfl⟩ : syracuseStep 519425 = 389569) B389569
theorem B290071 : Blo 227813 290071 := bstep (se 1 (by rfl) ⟨217553, by rfl⟩ : syracuseStep 290071 = 435107) B435107
theorem B257323 : Blo 227813 257323 := bstep (se 1 (by rfl) ⟨192992, by rfl⟩ : syracuseStep 257323 = 385985) B385985
theorem B781643 : Blo 227813 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B257431 : Blo 227813 257431 := bstep (se 1 (by rfl) ⟨193073, by rfl⟩ : syracuseStep 257431 = 386147) B386147
theorem B650713 : Blo 227813 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B749017 : Blo 227813 749017 := bstep (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) B561763
theorem B1404377 : Blo 227813 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B519641 : Blo 227813 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B388631 : Blo 227813 388631 := bstep (se 1 (by rfl) ⟨291473, by rfl⟩ : syracuseStep 388631 = 582947) B582947
theorem B749107 : Blo 227813 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B519731 : Blo 227813 519731 := bstep (se 1 (by rfl) ⟨389798, by rfl⟩ : syracuseStep 519731 = 779597) B779597
theorem B257611 : Blo 227813 257611 := bstep (se 1 (by rfl) ⟨193208, by rfl⟩ : syracuseStep 257611 = 386417) B386417
theorem B519767 : Blo 227813 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B1961603 : Blo 227813 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B388759 : Blo 227813 388759 := bstep (se 1 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 388759 = 583139) B583139
theorem B257719 : Blo 227813 257719 := bstep (se 1 (by rfl) ⟨193289, by rfl⟩ : syracuseStep 257719 = 386579) B386579
theorem B782027 : Blo 227813 782027 := bstep (se 1 (by rfl) ⟨586520, by rfl⟩ : syracuseStep 782027 = 1173041) B1173041
theorem B519947 : Blo 227813 519947 := bstep (se 1 (by rfl) ⟨389960, by rfl⟩ : syracuseStep 519947 = 779921) B779921
theorem B3534637 : Blo 227813 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B520001 : Blo 227813 520001 := bstep (se 2 (by rfl) ⟨195000, by rfl⟩ : syracuseStep 520001 = 390001) B390001
theorem B257899 : Blo 227813 257899 := bstep (se 1 (by rfl) ⟨193424, by rfl⟩ : syracuseStep 257899 = 386849) B386849
theorem B258007 : Blo 227813 258007 := bstep (se 1 (by rfl) ⟨193505, by rfl⟩ : syracuseStep 258007 = 387011) B387011
theorem B782297 : Blo 227813 782297 := bstep (se 2 (by rfl) ⟨293361, by rfl⟩ : syracuseStep 782297 = 586723) B586723
theorem B585751 : Blo 227813 585751 := bstep (se 1 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 585751 = 878627) B878627
theorem B520217 : Blo 227813 520217 := bstep (se 2 (by rfl) ⟨195081, by rfl⟩ : syracuseStep 520217 = 390163) B390163
theorem B290891 : Blo 227813 290891 := bstep (se 1 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 290891 = 436337) B436337
theorem B520307 : Blo 227813 520307 := bstep (se 1 (by rfl) ⟨390230, by rfl⟩ : syracuseStep 520307 = 780461) B780461
theorem B258187 : Blo 227813 258187 := bstep (se 1 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 258187 = 387281) B387281
theorem B520343 : Blo 227813 520343 := bstep (se 1 (by rfl) ⟨390257, by rfl⟩ : syracuseStep 520343 = 780515) B780515
theorem B487667 : Blo 227813 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B258295 : Blo 227813 258295 := bstep (se 1 (by rfl) ⟨193721, by rfl⟩ : syracuseStep 258295 = 387443) B387443
theorem B389387 : Blo 227813 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B520523 : Blo 227813 520523 := bstep (se 1 (by rfl) ⟨390392, by rfl⟩ : syracuseStep 520523 = 780785) B780785
theorem B520577 : Blo 227813 520577 := bstep (se 2 (by rfl) ⟨195216, by rfl⟩ : syracuseStep 520577 = 390433) B390433
theorem B389515 : Blo 227813 389515 := bstep (se 1 (by rfl) ⟨292136, by rfl⟩ : syracuseStep 389515 = 584273) B584273
theorem B258475 : Blo 227813 258475 := bstep (se 1 (by rfl) ⟨193856, by rfl⟩ : syracuseStep 258475 = 387713) B387713
theorem B586187 : Blo 227813 586187 := bstep (se 1 (by rfl) ⟨439640, by rfl⟩ : syracuseStep 586187 = 879281) B879281
theorem B258583 : Blo 227813 258583 := bstep (se 1 (by rfl) ⟨193937, by rfl⟩ : syracuseStep 258583 = 387875) B387875
theorem B389657 : Blo 227813 389657 := bstep (se 2 (by rfl) ⟨146121, by rfl⟩ : syracuseStep 389657 = 292243) B292243
theorem B1045037 : Blo 227813 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B553547 : Blo 227813 553547 := bstep (se 1 (by rfl) ⟨415160, by rfl⟩ : syracuseStep 553547 = 830321) B830321
theorem B520793 : Blo 227813 520793 := bstep (se 2 (by rfl) ⟨195297, by rfl⟩ : syracuseStep 520793 = 390595) B390595
theorem B13529693 : Blo 227813 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B389785 : Blo 227813 389785 := bstep (se 2 (by rfl) ⟨146169, by rfl⟩ : syracuseStep 389785 = 292339) B292339
theorem B520883 : Blo 227813 520883 := bstep (se 1 (by rfl) ⟨390662, by rfl⟩ : syracuseStep 520883 = 781325) B781325
theorem B258763 : Blo 227813 258763 := bstep (se 1 (by rfl) ⟨194072, by rfl⟩ : syracuseStep 258763 = 388145) B388145
theorem B520919 : Blo 227813 520919 := bstep (se 1 (by rfl) ⟨390689, by rfl⟩ : syracuseStep 520919 = 781379) B781379
theorem B291595 : Blo 227813 291595 := bstep (se 1 (by rfl) ⟨218696, by rfl⟩ : syracuseStep 291595 = 437393) B437393
theorem B258871 : Blo 227813 258871 := bstep (se 1 (by rfl) ⟨194153, by rfl⟩ : syracuseStep 258871 = 388307) B388307
theorem B586561 : Blo 227813 586561 := bstep (se 2 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 586561 = 439921) B439921
theorem B521099 : Blo 227813 521099 := bstep (se 1 (by rfl) ⟨390824, by rfl⟩ : syracuseStep 521099 = 781649) B781649
theorem B521153 : Blo 227813 521153 := bstep (se 2 (by rfl) ⟨195432, by rfl⟩ : syracuseStep 521153 = 390865) B390865
theorem B259051 : Blo 227813 259051 := bstep (se 1 (by rfl) ⟨194288, by rfl⟩ : syracuseStep 259051 = 388577) B388577
theorem B1668113 : Blo 227813 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B291863 : Blo 227813 291863 := bstep (se 1 (by rfl) ⟨218897, by rfl⟩ : syracuseStep 291863 = 437795) B437795
theorem B259159 : Blo 227813 259159 := bstep (se 1 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 259159 = 388739) B388739
theorem B521369 : Blo 227813 521369 := bstep (se 2 (by rfl) ⟨195513, by rfl⟩ : syracuseStep 521369 = 391027) B391027
theorem B980171 : Blo 227813 980171 := bstep (se 1 (by rfl) ⟨735128, by rfl⟩ : syracuseStep 980171 = 1470257) B1470257
theorem B390359 : Blo 227813 390359 := bstep (se 1 (by rfl) ⟨292769, by rfl⟩ : syracuseStep 390359 = 585539) B585539
theorem B521459 : Blo 227813 521459 := bstep (se 1 (by rfl) ⟨391094, by rfl⟩ : syracuseStep 521459 = 782189) B782189
theorem B259339 : Blo 227813 259339 := bstep (se 1 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 259339 = 389009) B389009
theorem B521495 : Blo 227813 521495 := bstep (se 1 (by rfl) ⟨391121, by rfl⟩ : syracuseStep 521495 = 782243) B782243
theorem B521497 : Blo 227813 521497 := bstep (se 2 (by rfl) ⟨195561, by rfl⟩ : syracuseStep 521497 = 391123) B391123
theorem B390487 : Blo 227813 390487 := bstep (se 1 (by rfl) ⟨292865, by rfl⟩ : syracuseStep 390487 = 585731) B585731
theorem B652637 : Blo 227813 652637 := bstep (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) B244739
theorem B259447 : Blo 227813 259447 := bstep (se 1 (by rfl) ⟨194585, by rfl⟩ : syracuseStep 259447 = 389171) B389171
theorem B488855 : Blo 227813 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B1176983 : Blo 227813 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B1111475 : Blo 227813 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B259627 : Blo 227813 259627 := bstep (se 1 (by rfl) ⟨194720, by rfl⟩ : syracuseStep 259627 = 389441) B389441
theorem B4159127 : Blo 227813 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B259735 : Blo 227813 259735 := bstep (se 1 (by rfl) ⟨194801, by rfl⟩ : syracuseStep 259735 = 389603) B389603
theorem B292567 : Blo 227813 292567 := bstep (se 1 (by rfl) ⟨219425, by rfl⟩ : syracuseStep 292567 = 438851) B438851
theorem B259915 : Blo 227813 259915 := bstep (se 1 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 259915 = 389873) B389873
theorem B260023 : Blo 227813 260023 := bstep (se 1 (by rfl) ⟨195017, by rfl⟩ : syracuseStep 260023 = 390035) B390035
theorem B391115 : Blo 227813 391115 := bstep (se 1 (by rfl) ⟨293336, by rfl⟩ : syracuseStep 391115 = 586673) B586673
theorem B2193425 : Blo 227813 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B1308737 : Blo 227813 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B260183 : Blo 227813 260183 := bstep (se 1 (by rfl) ⟨195137, by rfl⟩ : syracuseStep 260183 = 390275) B390275
theorem B325721 : Blo 227813 325721 := bstep (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) B244291
theorem B260203 : Blo 227813 260203 := bstep (se 1 (by rfl) ⟨195152, by rfl⟩ : syracuseStep 260203 = 390305) B390305
theorem B981143 : Blo 227813 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B260311 : Blo 227813 260311 := bstep (se 1 (by rfl) ⟨195233, by rfl⟩ : syracuseStep 260311 = 390467) B390467
theorem B1472843 : Blo 227813 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B260491 : Blo 227813 260491 := bstep (se 1 (by rfl) ⟨195368, by rfl⟩ : syracuseStep 260491 = 390737) B390737
theorem B489881 : Blo 227813 489881 := bstep (se 2 (by rfl) ⟨183705, by rfl⟩ : syracuseStep 489881 = 367411) B367411
theorem B227819 : Blo 227813 227819 := bstep (se 1 (by rfl) ⟨170864, by rfl⟩ : syracuseStep 227819 = 341729) B341729
theorem B227831 : Blo 227813 227831 := bstep (se 1 (by rfl) ⟨170873, by rfl⟩ : syracuseStep 227831 = 341747) B341747
theorem B260599 : Blo 227813 260599 := bstep (se 1 (by rfl) ⟨195449, by rfl⟩ : syracuseStep 260599 = 390899) B390899
theorem B227851 : Blo 227813 227851 := bstep (se 1 (by rfl) ⟨170888, by rfl⟩ : syracuseStep 227851 = 341777) B341777
theorem B227863 : Blo 227813 227863 := bstep (se 1 (by rfl) ⟨170897, by rfl⟩ : syracuseStep 227863 = 341795) B341795
theorem B227883 : Blo 227813 227883 := bstep (se 1 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 227883 = 341825) B341825
theorem B227895 : Blo 227813 227895 := bstep (se 1 (by rfl) ⟨170921, by rfl⟩ : syracuseStep 227895 = 341843) B341843
theorem B227915 : Blo 227813 227915 := bstep (se 1 (by rfl) ⟨170936, by rfl⟩ : syracuseStep 227915 = 341873) B341873
theorem B227927 : Blo 227813 227927 := bstep (se 1 (by rfl) ⟨170945, by rfl⟩ : syracuseStep 227927 = 341891) B341891
theorem B227947 : Blo 227813 227947 := bstep (se 1 (by rfl) ⟨170960, by rfl⟩ : syracuseStep 227947 = 341921) B341921
theorem B227959 : Blo 227813 227959 := bstep (se 1 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 227959 = 341939) B341939
theorem B227979 : Blo 227813 227979 := bstep (se 1 (by rfl) ⟨170984, by rfl⟩ : syracuseStep 227979 = 341969) B341969
theorem B227991 : Blo 227813 227991 := bstep (se 1 (by rfl) ⟨170993, by rfl⟩ : syracuseStep 227991 = 341987) B341987
theorem B228011 : Blo 227813 228011 := bstep (se 1 (by rfl) ⟨171008, by rfl⟩ : syracuseStep 228011 = 342017) B342017
theorem B260779 : Blo 227813 260779 := bstep (se 1 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 260779 = 391169) B391169
theorem B228023 : Blo 227813 228023 := bstep (se 1 (by rfl) ⟨171017, by rfl⟩ : syracuseStep 228023 = 342035) B342035
theorem B228043 : Blo 227813 228043 := bstep (se 1 (by rfl) ⟨171032, by rfl⟩ : syracuseStep 228043 = 342065) B342065
theorem B228055 : Blo 227813 228055 := bstep (se 1 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 228055 = 342083) B342083
theorem B326359 : Blo 227813 326359 := bstep (se 1 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 326359 = 489539) B489539
theorem B228075 : Blo 227813 228075 := bstep (se 1 (by rfl) ⟨171056, by rfl⟩ : syracuseStep 228075 = 342113) B342113
theorem B228087 : Blo 227813 228087 := bstep (se 1 (by rfl) ⟨171065, by rfl⟩ : syracuseStep 228087 = 342131) B342131
theorem B228107 : Blo 227813 228107 := bstep (se 1 (by rfl) ⟨171080, by rfl⟩ : syracuseStep 228107 = 342161) B342161
theorem B228119 : Blo 227813 228119 := bstep (se 1 (by rfl) ⟨171089, by rfl⟩ : syracuseStep 228119 = 342179) B342179
theorem B228139 : Blo 227813 228139 := bstep (se 1 (by rfl) ⟨171104, by rfl⟩ : syracuseStep 228139 = 342209) B342209
theorem B228151 : Blo 227813 228151 := bstep (se 1 (by rfl) ⟨171113, by rfl⟩ : syracuseStep 228151 = 342227) B342227
theorem B228171 : Blo 227813 228171 := bstep (se 1 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 228171 = 342257) B342257
theorem B228183 : Blo 227813 228183 := bstep (se 1 (by rfl) ⟨171137, by rfl⟩ : syracuseStep 228183 = 342275) B342275
theorem B228203 : Blo 227813 228203 := bstep (se 1 (by rfl) ⟨171152, by rfl⟩ : syracuseStep 228203 = 342305) B342305
theorem B228215 : Blo 227813 228215 := bstep (se 1 (by rfl) ⟨171161, by rfl⟩ : syracuseStep 228215 = 342323) B342323
theorem B228235 : Blo 227813 228235 := bstep (se 1 (by rfl) ⟨171176, by rfl⟩ : syracuseStep 228235 = 342353) B342353
theorem B228247 : Blo 227813 228247 := bstep (se 1 (by rfl) ⟨171185, by rfl⟩ : syracuseStep 228247 = 342371) B342371
theorem B228267 : Blo 227813 228267 := bstep (se 1 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 228267 = 342401) B342401
theorem B228279 : Blo 227813 228279 := bstep (se 1 (by rfl) ⟨171209, by rfl⟩ : syracuseStep 228279 = 342419) B342419
theorem B228299 : Blo 227813 228299 := bstep (se 1 (by rfl) ⟨171224, by rfl⟩ : syracuseStep 228299 = 342449) B342449
theorem B228311 : Blo 227813 228311 := bstep (se 1 (by rfl) ⟨171233, by rfl⟩ : syracuseStep 228311 = 342467) B342467
theorem B228331 : Blo 227813 228331 := bstep (se 1 (by rfl) ⟨171248, by rfl⟩ : syracuseStep 228331 = 342497) B342497
theorem B228343 : Blo 227813 228343 := bstep (se 1 (by rfl) ⟨171257, by rfl⟩ : syracuseStep 228343 = 342515) B342515
theorem B228363 : Blo 227813 228363 := bstep (se 1 (by rfl) ⟨171272, by rfl⟩ : syracuseStep 228363 = 342545) B342545
theorem B261131 : Blo 227813 261131 := bstep (se 1 (by rfl) ⟨195848, by rfl⟩ : syracuseStep 261131 = 391697) B391697
theorem B228375 : Blo 227813 228375 := bstep (se 1 (by rfl) ⟨171281, by rfl⟩ : syracuseStep 228375 = 342563) B342563
theorem B228395 : Blo 227813 228395 := bstep (se 1 (by rfl) ⟨171296, by rfl⟩ : syracuseStep 228395 = 342593) B342593
theorem B1571885 : Blo 227813 1571885 := bstep (se 3 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 1571885 = 589457) B589457
theorem B228407 : Blo 227813 228407 := bstep (se 1 (by rfl) ⟨171305, by rfl⟩ : syracuseStep 228407 = 342611) B342611
theorem B228427 : Blo 227813 228427 := bstep (se 1 (by rfl) ⟨171320, by rfl⟩ : syracuseStep 228427 = 342641) B342641
theorem B228439 : Blo 227813 228439 := bstep (se 1 (by rfl) ⟨171329, by rfl⟩ : syracuseStep 228439 = 342659) B342659
theorem B228459 : Blo 227813 228459 := bstep (se 1 (by rfl) ⟨171344, by rfl⟩ : syracuseStep 228459 = 342689) B342689
theorem B228471 : Blo 227813 228471 := bstep (se 1 (by rfl) ⟨171353, by rfl⟩ : syracuseStep 228471 = 342707) B342707
theorem B228491 : Blo 227813 228491 := bstep (se 1 (by rfl) ⟨171368, by rfl⟩ : syracuseStep 228491 = 342737) B342737
theorem B228503 : Blo 227813 228503 := bstep (se 1 (by rfl) ⟨171377, by rfl⟩ : syracuseStep 228503 = 342755) B342755
theorem B228523 : Blo 227813 228523 := bstep (se 1 (by rfl) ⟨171392, by rfl⟩ : syracuseStep 228523 = 342785) B342785
theorem B228535 : Blo 227813 228535 := bstep (se 1 (by rfl) ⟨171401, by rfl⟩ : syracuseStep 228535 = 342803) B342803
theorem B228555 : Blo 227813 228555 := bstep (se 1 (by rfl) ⟨171416, by rfl⟩ : syracuseStep 228555 = 342833) B342833
theorem B228567 : Blo 227813 228567 := bstep (se 1 (by rfl) ⟨171425, by rfl⟩ : syracuseStep 228567 = 342851) B342851
theorem B228587 : Blo 227813 228587 := bstep (se 1 (by rfl) ⟨171440, by rfl⟩ : syracuseStep 228587 = 342881) B342881
theorem B228599 : Blo 227813 228599 := bstep (se 1 (by rfl) ⟨171449, by rfl⟩ : syracuseStep 228599 = 342899) B342899
theorem B228619 : Blo 227813 228619 := bstep (se 1 (by rfl) ⟨171464, by rfl⟩ : syracuseStep 228619 = 342929) B342929
theorem B228631 : Blo 227813 228631 := bstep (se 1 (by rfl) ⟨171473, by rfl⟩ : syracuseStep 228631 = 342947) B342947
theorem B228651 : Blo 227813 228651 := bstep (se 1 (by rfl) ⟨171488, by rfl⟩ : syracuseStep 228651 = 342977) B342977
theorem B228663 : Blo 227813 228663 := bstep (se 1 (by rfl) ⟨171497, by rfl⟩ : syracuseStep 228663 = 342995) B342995
theorem B228683 : Blo 227813 228683 := bstep (se 1 (by rfl) ⟨171512, by rfl⟩ : syracuseStep 228683 = 343025) B343025
theorem B228695 : Blo 227813 228695 := bstep (se 1 (by rfl) ⟨171521, by rfl⟩ : syracuseStep 228695 = 343043) B343043
theorem B228715 : Blo 227813 228715 := bstep (se 1 (by rfl) ⟨171536, by rfl⟩ : syracuseStep 228715 = 343073) B343073
theorem B228727 : Blo 227813 228727 := bstep (se 1 (by rfl) ⟨171545, by rfl⟩ : syracuseStep 228727 = 343091) B343091
theorem B228747 : Blo 227813 228747 := bstep (se 1 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 228747 = 343121) B343121
theorem B228759 : Blo 227813 228759 := bstep (se 1 (by rfl) ⟨171569, by rfl⟩ : syracuseStep 228759 = 343139) B343139
theorem B228779 : Blo 227813 228779 := bstep (se 1 (by rfl) ⟨171584, by rfl⟩ : syracuseStep 228779 = 343169) B343169
theorem B490931 : Blo 227813 490931 := bstep (se 1 (by rfl) ⟨368198, by rfl⟩ : syracuseStep 490931 = 736397) B736397
theorem B228791 : Blo 227813 228791 := bstep (se 1 (by rfl) ⟨171593, by rfl⟩ : syracuseStep 228791 = 343187) B343187
theorem B228811 : Blo 227813 228811 := bstep (se 1 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 228811 = 343217) B343217
theorem B622027 : Blo 227813 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B228823 : Blo 227813 228823 := bstep (se 1 (by rfl) ⟨171617, by rfl⟩ : syracuseStep 228823 = 343235) B343235
theorem B228843 : Blo 227813 228843 := bstep (se 1 (by rfl) ⟨171632, by rfl⟩ : syracuseStep 228843 = 343265) B343265
theorem B228855 : Blo 227813 228855 := bstep (se 1 (by rfl) ⟨171641, by rfl⟩ : syracuseStep 228855 = 343283) B343283
theorem B228875 : Blo 227813 228875 := bstep (se 1 (by rfl) ⟨171656, by rfl⟩ : syracuseStep 228875 = 343313) B343313
theorem B327179 : Blo 227813 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B228887 : Blo 227813 228887 := bstep (se 1 (by rfl) ⟨171665, by rfl⟩ : syracuseStep 228887 = 343331) B343331
theorem B228907 : Blo 227813 228907 := bstep (se 1 (by rfl) ⟨171680, by rfl⟩ : syracuseStep 228907 = 343361) B343361
theorem B228919 : Blo 227813 228919 := bstep (se 1 (by rfl) ⟨171689, by rfl⟩ : syracuseStep 228919 = 343379) B343379
theorem B228939 : Blo 227813 228939 := bstep (se 1 (by rfl) ⟨171704, by rfl⟩ : syracuseStep 228939 = 343409) B343409
theorem B228951 : Blo 227813 228951 := bstep (se 1 (by rfl) ⟨171713, by rfl⟩ : syracuseStep 228951 = 343427) B343427
theorem B228971 : Blo 227813 228971 := bstep (se 1 (by rfl) ⟨171728, by rfl⟩ : syracuseStep 228971 = 343457) B343457
theorem B228983 : Blo 227813 228983 := bstep (se 1 (by rfl) ⟨171737, by rfl⟩ : syracuseStep 228983 = 343475) B343475
theorem B229003 : Blo 227813 229003 := bstep (se 1 (by rfl) ⟨171752, by rfl⟩ : syracuseStep 229003 = 343505) B343505
theorem B229015 : Blo 227813 229015 := bstep (se 1 (by rfl) ⟨171761, by rfl⟩ : syracuseStep 229015 = 343523) B343523
theorem B229035 : Blo 227813 229035 := bstep (se 1 (by rfl) ⟨171776, by rfl⟩ : syracuseStep 229035 = 343553) B343553
theorem B229047 : Blo 227813 229047 := bstep (se 1 (by rfl) ⟨171785, by rfl⟩ : syracuseStep 229047 = 343571) B343571
theorem B229067 : Blo 227813 229067 := bstep (se 1 (by rfl) ⟨171800, by rfl⟩ : syracuseStep 229067 = 343601) B343601
theorem B229079 : Blo 227813 229079 := bstep (se 1 (by rfl) ⟨171809, by rfl⟩ : syracuseStep 229079 = 343619) B343619
theorem B229099 : Blo 227813 229099 := bstep (se 1 (by rfl) ⟨171824, by rfl⟩ : syracuseStep 229099 = 343649) B343649
theorem B229111 : Blo 227813 229111 := bstep (se 1 (by rfl) ⟨171833, by rfl⟩ : syracuseStep 229111 = 343667) B343667
theorem B229131 : Blo 227813 229131 := bstep (se 1 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 229131 = 343697) B343697
theorem B229143 : Blo 227813 229143 := bstep (se 1 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 229143 = 343715) B343715
theorem B229163 : Blo 227813 229163 := bstep (se 1 (by rfl) ⟨171872, by rfl⟩ : syracuseStep 229163 = 343745) B343745
theorem B229175 : Blo 227813 229175 := bstep (se 1 (by rfl) ⟨171881, by rfl⟩ : syracuseStep 229175 = 343763) B343763
theorem B229195 : Blo 227813 229195 := bstep (se 1 (by rfl) ⟨171896, by rfl⟩ : syracuseStep 229195 = 343793) B343793
theorem B229207 : Blo 227813 229207 := bstep (se 1 (by rfl) ⟨171905, by rfl⟩ : syracuseStep 229207 = 343811) B343811
theorem B229227 : Blo 227813 229227 := bstep (se 1 (by rfl) ⟨171920, by rfl⟩ : syracuseStep 229227 = 343841) B343841
theorem B229239 : Blo 227813 229239 := bstep (se 1 (by rfl) ⟨171929, by rfl⟩ : syracuseStep 229239 = 343859) B343859
theorem B229259 : Blo 227813 229259 := bstep (se 1 (by rfl) ⟨171944, by rfl⟩ : syracuseStep 229259 = 343889) B343889
theorem B229271 : Blo 227813 229271 := bstep (se 1 (by rfl) ⟨171953, by rfl⟩ : syracuseStep 229271 = 343907) B343907
theorem B229291 : Blo 227813 229291 := bstep (se 1 (by rfl) ⟨171968, by rfl⟩ : syracuseStep 229291 = 343937) B343937
theorem B1474483 : Blo 227813 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B229303 : Blo 227813 229303 := bstep (se 1 (by rfl) ⟨171977, by rfl⟩ : syracuseStep 229303 = 343955) B343955
theorem B229323 : Blo 227813 229323 := bstep (se 1 (by rfl) ⟨171992, by rfl⟩ : syracuseStep 229323 = 343985) B343985
theorem B229335 : Blo 227813 229335 := bstep (se 1 (by rfl) ⟨172001, by rfl⟩ : syracuseStep 229335 = 344003) B344003
theorem B229355 : Blo 227813 229355 := bstep (se 1 (by rfl) ⟨172016, by rfl⟩ : syracuseStep 229355 = 344033) B344033
theorem B229367 : Blo 227813 229367 := bstep (se 1 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 229367 = 344051) B344051
theorem B655361 : Blo 227813 655361 := bstep (se 2 (by rfl) ⟨245760, by rfl⟩ : syracuseStep 655361 = 491521) B491521
theorem B229383 : Blo 227813 229383 := bstep (se 1 (by rfl) ⟨172037, by rfl⟩ : syracuseStep 229383 = 344075) B344075
theorem B229391 : Blo 227813 229391 := bstep (se 1 (by rfl) ⟨172043, by rfl⟩ : syracuseStep 229391 = 344087) B344087
theorem B229435 : Blo 227813 229435 := bstep (se 1 (by rfl) ⟨172076, by rfl⟩ : syracuseStep 229435 = 344153) B344153
theorem B4259957 : Blo 227813 4259957 := bstep (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) B399371
theorem B229511 : Blo 227813 229511 := bstep (se 1 (by rfl) ⟨172133, by rfl⟩ : syracuseStep 229511 = 344267) B344267
theorem B229519 : Blo 227813 229519 := bstep (se 1 (by rfl) ⟨172139, by rfl⟩ : syracuseStep 229519 = 344279) B344279
theorem B229563 : Blo 227813 229563 := bstep (se 1 (by rfl) ⟨172172, by rfl⟩ : syracuseStep 229563 = 344345) B344345
theorem B2195657 : Blo 227813 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B229639 : Blo 227813 229639 := bstep (se 1 (by rfl) ⟨172229, by rfl⟩ : syracuseStep 229639 = 344459) B344459
theorem B229647 : Blo 227813 229647 := bstep (se 1 (by rfl) ⟨172235, by rfl⟩ : syracuseStep 229647 = 344471) B344471
theorem B229691 : Blo 227813 229691 := bstep (se 1 (by rfl) ⟨172268, by rfl⟩ : syracuseStep 229691 = 344537) B344537
theorem B229767 : Blo 227813 229767 := bstep (se 1 (by rfl) ⟨172325, by rfl⟩ : syracuseStep 229767 = 344651) B344651
theorem B885127 : Blo 227813 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B229775 : Blo 227813 229775 := bstep (se 1 (by rfl) ⟨172331, by rfl⟩ : syracuseStep 229775 = 344663) B344663
theorem B229819 : Blo 227813 229819 := bstep (se 1 (by rfl) ⟨172364, by rfl⟩ : syracuseStep 229819 = 344729) B344729
theorem B229895 : Blo 227813 229895 := bstep (se 1 (by rfl) ⟨172421, by rfl⟩ : syracuseStep 229895 = 344843) B344843
theorem B885259 : Blo 227813 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B229903 : Blo 227813 229903 := bstep (se 1 (by rfl) ⟨172427, by rfl⟩ : syracuseStep 229903 = 344855) B344855
theorem B1245719 : Blo 227813 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B229947 : Blo 227813 229947 := bstep (se 1 (by rfl) ⟨172460, by rfl⟩ : syracuseStep 229947 = 344921) B344921
theorem B230023 : Blo 227813 230023 := bstep (se 1 (by rfl) ⟨172517, by rfl⟩ : syracuseStep 230023 = 345035) B345035
theorem B230031 : Blo 227813 230031 := bstep (se 1 (by rfl) ⟨172523, by rfl⟩ : syracuseStep 230031 = 345047) B345047
theorem B230075 : Blo 227813 230075 := bstep (se 1 (by rfl) ⟨172556, by rfl⟩ : syracuseStep 230075 = 345113) B345113
theorem B4162265 : Blo 227813 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B230151 : Blo 227813 230151 := bstep (se 1 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 230151 = 345227) B345227
theorem B230159 : Blo 227813 230159 := bstep (se 1 (by rfl) ⟨172619, by rfl⟩ : syracuseStep 230159 = 345239) B345239
theorem B230203 : Blo 227813 230203 := bstep (se 1 (by rfl) ⟨172652, by rfl⟩ : syracuseStep 230203 = 345305) B345305
theorem B1246067 : Blo 227813 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B230279 : Blo 227813 230279 := bstep (se 1 (by rfl) ⟨172709, by rfl⟩ : syracuseStep 230279 = 345419) B345419
theorem B230287 : Blo 227813 230287 := bstep (se 1 (by rfl) ⟨172715, by rfl⟩ : syracuseStep 230287 = 345431) B345431
theorem B230331 : Blo 227813 230331 := bstep (se 1 (by rfl) ⟨172748, by rfl⟩ : syracuseStep 230331 = 345497) B345497
theorem B525257 : Blo 227813 525257 := bstep (se 2 (by rfl) ⟨196971, by rfl⟩ : syracuseStep 525257 = 393943) B393943
theorem B230407 : Blo 227813 230407 := bstep (se 1 (by rfl) ⟨172805, by rfl⟩ : syracuseStep 230407 = 345611) B345611
theorem B328711 : Blo 227813 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B230415 : Blo 227813 230415 := bstep (se 1 (by rfl) ⟨172811, by rfl⟩ : syracuseStep 230415 = 345623) B345623
theorem B230459 : Blo 227813 230459 := bstep (se 1 (by rfl) ⟨172844, by rfl⟩ : syracuseStep 230459 = 345689) B345689
theorem B230535 : Blo 227813 230535 := bstep (se 1 (by rfl) ⟨172901, by rfl⟩ : syracuseStep 230535 = 345803) B345803
theorem B230543 : Blo 227813 230543 := bstep (se 1 (by rfl) ⟨172907, by rfl⟩ : syracuseStep 230543 = 345815) B345815
theorem B5276821 : Blo 227813 5276821 := bstep (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) B247351
theorem B230587 : Blo 227813 230587 := bstep (se 1 (by rfl) ⟨172940, by rfl⟩ : syracuseStep 230587 = 345881) B345881
theorem B230663 : Blo 227813 230663 := bstep (se 1 (by rfl) ⟨172997, by rfl⟩ : syracuseStep 230663 = 345995) B345995
theorem B230671 : Blo 227813 230671 := bstep (se 1 (by rfl) ⟨173003, by rfl⟩ : syracuseStep 230671 = 346007) B346007
theorem B230715 : Blo 227813 230715 := bstep (se 1 (by rfl) ⟨173036, by rfl⟩ : syracuseStep 230715 = 346073) B346073
theorem B13731185 : Blo 227813 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B230791 : Blo 227813 230791 := bstep (se 1 (by rfl) ⟨173093, by rfl⟩ : syracuseStep 230791 = 346187) B346187
theorem B230799 : Blo 227813 230799 := bstep (se 1 (by rfl) ⟨173099, by rfl⟩ : syracuseStep 230799 = 346199) B346199
theorem B230843 : Blo 227813 230843 := bstep (se 1 (by rfl) ⟨173132, by rfl⟩ : syracuseStep 230843 = 346265) B346265
theorem B2622941 : Blo 227813 2622941 := bstep (se 3 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 2622941 = 983603) B983603
theorem B230919 : Blo 227813 230919 := bstep (se 1 (by rfl) ⟨173189, by rfl⟩ : syracuseStep 230919 = 346379) B346379
theorem B230927 : Blo 227813 230927 := bstep (se 1 (by rfl) ⟨173195, by rfl⟩ : syracuseStep 230927 = 346391) B346391
theorem B230971 : Blo 227813 230971 := bstep (se 1 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 230971 = 346457) B346457
theorem B329275 : Blo 227813 329275 := bstep (se 1 (by rfl) ⟨246956, by rfl⟩ : syracuseStep 329275 = 493913) B493913
theorem B36079181 : Blo 227813 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B657011 : Blo 227813 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B394871 : Blo 227813 394871 := bstep (se 1 (by rfl) ⟨296153, by rfl⟩ : syracuseStep 394871 = 592307) B592307
theorem B231047 : Blo 227813 231047 := bstep (se 1 (by rfl) ⟨173285, by rfl⟩ : syracuseStep 231047 = 346571) B346571
theorem B231055 : Blo 227813 231055 := bstep (se 1 (by rfl) ⟨173291, by rfl⟩ : syracuseStep 231055 = 346583) B346583
theorem B231099 : Blo 227813 231099 := bstep (se 1 (by rfl) ⟨173324, by rfl⟩ : syracuseStep 231099 = 346649) B346649
theorem B231175 : Blo 227813 231175 := bstep (se 1 (by rfl) ⟨173381, by rfl⟩ : syracuseStep 231175 = 346763) B346763
theorem B231183 : Blo 227813 231183 := bstep (se 1 (by rfl) ⟨173387, by rfl⟩ : syracuseStep 231183 = 346775) B346775
theorem B231227 : Blo 227813 231227 := bstep (se 1 (by rfl) ⟨173420, by rfl⟩ : syracuseStep 231227 = 346841) B346841
theorem B231303 : Blo 227813 231303 := bstep (se 1 (by rfl) ⟨173477, by rfl⟩ : syracuseStep 231303 = 346955) B346955
theorem B231311 : Blo 227813 231311 := bstep (se 1 (by rfl) ⟨173483, by rfl⟩ : syracuseStep 231311 = 346967) B346967
theorem B231355 : Blo 227813 231355 := bstep (se 1 (by rfl) ⟨173516, by rfl⟩ : syracuseStep 231355 = 347033) B347033
theorem B231431 : Blo 227813 231431 := bstep (se 1 (by rfl) ⟨173573, by rfl⟩ : syracuseStep 231431 = 347147) B347147
theorem B231439 : Blo 227813 231439 := bstep (se 1 (by rfl) ⟨173579, by rfl⟩ : syracuseStep 231439 = 347159) B347159
theorem B657467 : Blo 227813 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B231483 : Blo 227813 231483 := bstep (se 1 (by rfl) ⟨173612, by rfl⟩ : syracuseStep 231483 = 347225) B347225
theorem B231559 : Blo 227813 231559 := bstep (se 1 (by rfl) ⟨173669, by rfl⟩ : syracuseStep 231559 = 347339) B347339
theorem B231567 : Blo 227813 231567 := bstep (se 1 (by rfl) ⟨173675, by rfl⟩ : syracuseStep 231567 = 347351) B347351
theorem B4982957 : Blo 227813 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B231611 : Blo 227813 231611 := bstep (se 1 (by rfl) ⟨173708, by rfl⟩ : syracuseStep 231611 = 347417) B347417
theorem B1771721 : Blo 227813 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B657665 : Blo 227813 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B231687 : Blo 227813 231687 := bstep (se 1 (by rfl) ⟨173765, by rfl⟩ : syracuseStep 231687 = 347531) B347531
theorem B526607 : Blo 227813 526607 := bstep (se 1 (by rfl) ⟨394955, by rfl⟩ : syracuseStep 526607 = 789911) B789911
theorem B231695 : Blo 227813 231695 := bstep (se 1 (by rfl) ⟨173771, by rfl⟩ : syracuseStep 231695 = 347543) B347543
theorem B231739 : Blo 227813 231739 := bstep (se 1 (by rfl) ⟨173804, by rfl⟩ : syracuseStep 231739 = 347609) B347609
theorem B985553 : Blo 227813 985553 := bstep (se 2 (by rfl) ⟨369582, by rfl⟩ : syracuseStep 985553 = 739165) B739165
theorem B2198117 : Blo 227813 2198117 := bstep (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) B412147
theorem B4950821 : Blo 227813 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B658219 : Blo 227813 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B1248209 : Blo 227813 1248209 := bstep (se 2 (by rfl) ⟨468078, by rfl⟩ : syracuseStep 1248209 = 936157) B936157
theorem B1412099 : Blo 227813 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B658493 : Blo 227813 658493 := bstep (se 3 (by rfl) ⟨123467, by rfl⟩ : syracuseStep 658493 = 246935) B246935
theorem B462215 : Blo 227813 462215 := bstep (se 1 (by rfl) ⟨346661, by rfl⟩ : syracuseStep 462215 = 693323) B693323
theorem B1314251 : Blo 227813 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B1969667 : Blo 227813 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B1740365 : Blo 227813 1740365 := bstep (se 3 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 1740365 = 652637) B652637
theorem B1249025 : Blo 227813 1249025 := bstep (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) B936769
theorem B1183547 : Blo 227813 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B659335 : Blo 227813 659335 := bstep (se 1 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 659335 = 989003) B989003
theorem B2199575 : Blo 227813 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B659609 : Blo 227813 659609 := bstep (se 2 (by rfl) ⟨247353, by rfl⟩ : syracuseStep 659609 = 494707) B494707
theorem B463163 : Blo 227813 463163 := bstep (se 1 (by rfl) ⟨347372, by rfl⟩ : syracuseStep 463163 = 694745) B694745
theorem B824381 : Blo 227813 824381 := bstep (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) B309143
theorem B693821 : Blo 227813 693821 := bstep (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) B260183
theorem B1742795 : Blo 227813 1742795 := bstep (se 1 (by rfl) ⟨1307096, by rfl⟩ : syracuseStep 1742795 = 2614193) B2614193
theorem B465353 : Blo 227813 465353 := bstep (se 2 (by rfl) ⟨174507, by rfl⟩ : syracuseStep 465353 = 349015) B349015
theorem B2366243 : Blo 227813 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B1154249 : Blo 227813 1154249 := bstep (se 2 (by rfl) ⟨432843, by rfl⟩ : syracuseStep 1154249 = 865687) B865687
theorem B433451 : Blo 227813 433451 := bstep (se 1 (by rfl) ⟨325088, by rfl⟩ : syracuseStep 433451 = 650177) B650177
theorem B1875421 : Blo 227813 1875421 := bstep (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) B703283
theorem B2924261 : Blo 227813 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B2596697 : Blo 227813 2596697 := bstep (se 2 (by rfl) ⟨973761, by rfl⟩ : syracuseStep 2596697 = 1947523) B1947523
theorem B696349 : Blo 227813 696349 := bstep (se 3 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 696349 = 261131) B261131
theorem B696691 : Blo 227813 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B369031 : Blo 227813 369031 := bstep (se 1 (by rfl) ⟨276773, by rfl⟩ : syracuseStep 369031 = 553547) B553547
theorem B500513 : Blo 227813 500513 := bstep (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) B375385
theorem B435145 : Blo 227813 435145 := bstep (se 2 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 435145 = 326359) B326359
theorem B1320137 : Blo 227813 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B1058333 : Blo 227813 1058333 := bstep (se 3 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 1058333 = 396875) B396875
theorem B829369 : Blo 227813 829369 := bstep (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) B622027
theorem B437051 : Blo 227813 437051 := bstep (se 1 (by rfl) ⟨327788, by rfl⟩ : syracuseStep 437051 = 655577) B655577
theorem B2632601 : Blo 227813 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B1748141 : Blo 227813 1748141 := bstep (se 3 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 1748141 = 655553) B655553
theorem B732361 : Blo 227813 732361 := bstep (se 2 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 732361 = 549271) B549271
theorem B437537 : Blo 227813 437537 := bstep (se 2 (by rfl) ⟨164076, by rfl⟩ : syracuseStep 437537 = 328153) B328153
theorem B830753 : Blo 227813 830753 := bstep (se 2 (by rfl) ⟨311532, by rfl⟩ : syracuseStep 830753 = 623065) B623065
theorem B437879 : Blo 227813 437879 := bstep (se 1 (by rfl) ⟨328409, by rfl⟩ : syracuseStep 437879 = 656819) B656819
theorem B700535 : Blo 227813 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B1814929 : Blo 227813 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B1126801 : Blo 227813 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B1782161 : Blo 227813 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B2962291 : Blo 227813 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B1160081 : Blo 227813 1160081 := bstep (se 2 (by rfl) ⟨435030, by rfl⟩ : syracuseStep 1160081 = 870061) B870061
theorem B2241433 : Blo 227813 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B275447 : Blo 227813 275447 := bstep (se 1 (by rfl) ⟨206585, by rfl⟩ : syracuseStep 275447 = 413171) B413171
theorem B668701 : Blo 227813 668701 := bstep (se 3 (by rfl) ⟨125381, by rfl⟩ : syracuseStep 668701 = 250763) B250763
theorem B439481 : Blo 227813 439481 := bstep (se 2 (by rfl) ⟨164805, by rfl⟩ : syracuseStep 439481 = 329611) B329611
theorem B898249 : Blo 227813 898249 := bstep (se 2 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 898249 = 673687) B673687
theorem B439823 : Blo 227813 439823 := bstep (se 1 (by rfl) ⟨329867, by rfl⟩ : syracuseStep 439823 = 659735) B659735
theorem B1750571 : Blo 227813 1750571 := bstep (se 1 (by rfl) ⟨1312928, by rfl⟩ : syracuseStep 1750571 = 2625857) B2625857
theorem B276139 : Blo 227813 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B2111233 : Blo 227813 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B341819 : Blo 227813 341819 := bstep (se 1 (by rfl) ⟨256364, by rfl⟩ : syracuseStep 341819 = 512729) B512729
theorem B2471755 : Blo 227813 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B341879 : Blo 227813 341879 := bstep (se 1 (by rfl) ⟨256409, by rfl⟩ : syracuseStep 341879 = 512819) B512819
theorem B341903 : Blo 227813 341903 := bstep (se 1 (by rfl) ⟨256427, by rfl⟩ : syracuseStep 341903 = 512855) B512855
theorem B341945 : Blo 227813 341945 := bstep (se 2 (by rfl) ⟨128229, by rfl⟩ : syracuseStep 341945 = 256459) B256459
theorem B342023 : Blo 227813 342023 := bstep (se 1 (by rfl) ⟨256517, by rfl⟩ : syracuseStep 342023 = 513035) B513035
theorem B342059 : Blo 227813 342059 := bstep (se 1 (by rfl) ⟨256544, by rfl⟩ : syracuseStep 342059 = 513089) B513089
theorem B1325117 : Blo 227813 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B342089 : Blo 227813 342089 := bstep (se 2 (by rfl) ⟨128283, by rfl⟩ : syracuseStep 342089 = 256567) B256567
theorem B243847 : Blo 227813 243847 := bstep (se 1 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 243847 = 365771) B365771
theorem B342203 : Blo 227813 342203 := bstep (se 1 (by rfl) ⟨256652, by rfl⟩ : syracuseStep 342203 = 513305) B513305
theorem B702665 : Blo 227813 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B4962545 : Blo 227813 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B342263 : Blo 227813 342263 := bstep (se 1 (by rfl) ⟨256697, by rfl⟩ : syracuseStep 342263 = 513395) B513395
theorem B342287 : Blo 227813 342287 := bstep (se 1 (by rfl) ⟨256715, by rfl⟩ : syracuseStep 342287 = 513431) B513431
theorem B342329 : Blo 227813 342329 := bstep (se 2 (by rfl) ⟨128373, by rfl⟩ : syracuseStep 342329 = 256747) B256747
theorem B342407 : Blo 227813 342407 := bstep (se 1 (by rfl) ⟨256805, by rfl⟩ : syracuseStep 342407 = 513611) B513611
theorem B342443 : Blo 227813 342443 := bstep (se 1 (by rfl) ⟨256832, by rfl⟩ : syracuseStep 342443 = 513665) B513665
theorem B342473 : Blo 227813 342473 := bstep (se 2 (by rfl) ⟨128427, by rfl⟩ : syracuseStep 342473 = 256855) B256855
theorem B703019 : Blo 227813 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B342587 : Blo 227813 342587 := bstep (se 1 (by rfl) ⟨256940, by rfl⟩ : syracuseStep 342587 = 513881) B513881
theorem B1096253 : Blo 227813 1096253 := bstep (se 3 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 1096253 = 411095) B411095
theorem B703091 : Blo 227813 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B342647 : Blo 227813 342647 := bstep (se 1 (by rfl) ⟨256985, by rfl⟩ : syracuseStep 342647 = 513971) B513971
theorem B342671 : Blo 227813 342671 := bstep (se 1 (by rfl) ⟨257003, by rfl⟩ : syracuseStep 342671 = 514007) B514007
theorem B342713 : Blo 227813 342713 := bstep (se 2 (by rfl) ⟨128517, by rfl⟩ : syracuseStep 342713 = 257035) B257035
theorem B342791 : Blo 227813 342791 := bstep (se 1 (by rfl) ⟨257093, by rfl⟩ : syracuseStep 342791 = 514187) B514187
theorem B342827 : Blo 227813 342827 := bstep (se 1 (by rfl) ⟨257120, by rfl⟩ : syracuseStep 342827 = 514241) B514241
theorem B310073 : Blo 227813 310073 := bstep (se 2 (by rfl) ⟨116277, by rfl⟩ : syracuseStep 310073 = 232555) B232555
theorem B867131 : Blo 227813 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B342857 : Blo 227813 342857 := bstep (se 2 (by rfl) ⟨128571, by rfl⟩ : syracuseStep 342857 = 257143) B257143
theorem B342971 : Blo 227813 342971 := bstep (se 1 (by rfl) ⟨257228, by rfl⟩ : syracuseStep 342971 = 514457) B514457
theorem B244667 : Blo 227813 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B1162187 : Blo 227813 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B343031 : Blo 227813 343031 := bstep (se 1 (by rfl) ⟨257273, by rfl⟩ : syracuseStep 343031 = 514547) B514547
theorem B343055 : Blo 227813 343055 := bstep (se 1 (by rfl) ⟨257291, by rfl⟩ : syracuseStep 343055 = 514583) B514583
theorem B277519 : Blo 227813 277519 := bstep (se 1 (by rfl) ⟨208139, by rfl⟩ : syracuseStep 277519 = 416279) B416279
theorem B769067 : Blo 227813 769067 := bstep (se 1 (by rfl) ⟨576800, by rfl⟩ : syracuseStep 769067 = 1153601) B1153601
theorem B343097 : Blo 227813 343097 := bstep (se 2 (by rfl) ⟨128661, by rfl⟩ : syracuseStep 343097 = 257323) B257323
theorem B8928317 : Blo 227813 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B343175 : Blo 227813 343175 := bstep (se 1 (by rfl) ⟨257381, by rfl⟩ : syracuseStep 343175 = 514763) B514763
theorem B343211 : Blo 227813 343211 := bstep (se 1 (by rfl) ⟨257408, by rfl⟩ : syracuseStep 343211 = 514817) B514817
theorem B343241 : Blo 227813 343241 := bstep (se 2 (by rfl) ⟨128715, by rfl⟩ : syracuseStep 343241 = 257431) B257431
theorem B1162511 : Blo 227813 1162511 := bstep (se 1 (by rfl) ⟨871883, by rfl⟩ : syracuseStep 1162511 = 1743767) B1743767
theorem B867617 : Blo 227813 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B998689 : Blo 227813 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B507179 : Blo 227813 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B343355 : Blo 227813 343355 := bstep (se 1 (by rfl) ⟨257516, by rfl⟩ : syracuseStep 343355 = 515033) B515033
theorem B736627 : Blo 227813 736627 := bstep (se 1 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 736627 = 1104941) B1104941
theorem B343415 : Blo 227813 343415 := bstep (se 1 (by rfl) ⟨257561, by rfl⟩ : syracuseStep 343415 = 515123) B515123
theorem B343439 : Blo 227813 343439 := bstep (se 1 (by rfl) ⟨257579, by rfl⟩ : syracuseStep 343439 = 515159) B515159
theorem B343481 : Blo 227813 343481 := bstep (se 2 (by rfl) ⟨128805, by rfl⟩ : syracuseStep 343481 = 257611) B257611
theorem B343559 : Blo 227813 343559 := bstep (se 1 (by rfl) ⟨257669, by rfl⟩ : syracuseStep 343559 = 515339) B515339
theorem B343595 : Blo 227813 343595 := bstep (se 1 (by rfl) ⟨257696, by rfl⟩ : syracuseStep 343595 = 515393) B515393
theorem B343625 : Blo 227813 343625 := bstep (se 2 (by rfl) ⟨128859, by rfl⟩ : syracuseStep 343625 = 257719) B257719
theorem B704135 : Blo 227813 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B343739 : Blo 227813 343739 := bstep (se 1 (by rfl) ⟨257804, by rfl⟩ : syracuseStep 343739 = 515609) B515609
theorem B343799 : Blo 227813 343799 := bstep (se 1 (by rfl) ⟨257849, by rfl⟩ : syracuseStep 343799 = 515699) B515699
theorem B343823 : Blo 227813 343823 := bstep (se 1 (by rfl) ⟨257867, by rfl⟩ : syracuseStep 343823 = 515735) B515735
theorem B343865 : Blo 227813 343865 := bstep (se 2 (by rfl) ⟨128949, by rfl⟩ : syracuseStep 343865 = 257899) B257899
theorem B343943 : Blo 227813 343943 := bstep (se 1 (by rfl) ⟨257957, by rfl⟩ : syracuseStep 343943 = 515915) B515915
theorem B278407 : Blo 227813 278407 := bstep (se 1 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 278407 = 417611) B417611
theorem B343979 : Blo 227813 343979 := bstep (se 1 (by rfl) ⟨257984, by rfl⟩ : syracuseStep 343979 = 515969) B515969
theorem B344009 : Blo 227813 344009 := bstep (se 2 (by rfl) ⟨129003, by rfl⟩ : syracuseStep 344009 = 258007) B258007
theorem B2211851 : Blo 227813 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B344123 : Blo 227813 344123 := bstep (se 1 (by rfl) ⟨258092, by rfl⟩ : syracuseStep 344123 = 516185) B516185
theorem B344183 : Blo 227813 344183 := bstep (se 1 (by rfl) ⟨258137, by rfl⟩ : syracuseStep 344183 = 516275) B516275
theorem B344207 : Blo 227813 344207 := bstep (se 1 (by rfl) ⟨258155, by rfl⟩ : syracuseStep 344207 = 516311) B516311
theorem B344249 : Blo 227813 344249 := bstep (se 2 (by rfl) ⟨129093, by rfl⟩ : syracuseStep 344249 = 258187) B258187
theorem B868589 : Blo 227813 868589 := bstep (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) B325721
theorem B344327 : Blo 227813 344327 := bstep (se 1 (by rfl) ⟨258245, by rfl⟩ : syracuseStep 344327 = 516491) B516491
theorem B344363 : Blo 227813 344363 := bstep (se 1 (by rfl) ⟨258272, by rfl⟩ : syracuseStep 344363 = 516545) B516545
theorem B770363 : Blo 227813 770363 := bstep (se 1 (by rfl) ⟨577772, by rfl⟩ : syracuseStep 770363 = 1155545) B1155545
theorem B344393 : Blo 227813 344393 := bstep (se 2 (by rfl) ⟨129147, by rfl⟩ : syracuseStep 344393 = 258295) B258295
theorem B2474387 : Blo 227813 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B1098137 : Blo 227813 1098137 := bstep (se 2 (by rfl) ⟨411801, by rfl⟩ : syracuseStep 1098137 = 823603) B823603
theorem B344507 : Blo 227813 344507 := bstep (se 1 (by rfl) ⟨258380, by rfl⟩ : syracuseStep 344507 = 516761) B516761
theorem B344567 : Blo 227813 344567 := bstep (se 1 (by rfl) ⟨258425, by rfl⟩ : syracuseStep 344567 = 516851) B516851
theorem B1098251 : Blo 227813 1098251 := bstep (se 1 (by rfl) ⟨823688, by rfl⟩ : syracuseStep 1098251 = 1647377) B1647377
theorem B344591 : Blo 227813 344591 := bstep (se 1 (by rfl) ⟨258443, by rfl⟩ : syracuseStep 344591 = 516887) B516887
theorem B868907 : Blo 227813 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B344633 : Blo 227813 344633 := bstep (se 2 (by rfl) ⟨129237, by rfl⟩ : syracuseStep 344633 = 258475) B258475
theorem B344711 : Blo 227813 344711 := bstep (se 1 (by rfl) ⟨258533, by rfl⟩ : syracuseStep 344711 = 517067) B517067
theorem B344747 : Blo 227813 344747 := bstep (se 1 (by rfl) ⟨258560, by rfl⟩ : syracuseStep 344747 = 517121) B517121
theorem B1163969 : Blo 227813 1163969 := bstep (se 2 (by rfl) ⟨436488, by rfl⟩ : syracuseStep 1163969 = 872977) B872977
theorem B344777 : Blo 227813 344777 := bstep (se 2 (by rfl) ⟨129291, by rfl⟩ : syracuseStep 344777 = 258583) B258583
theorem B770849 : Blo 227813 770849 := bstep (se 2 (by rfl) ⟨289068, by rfl⟩ : syracuseStep 770849 = 578137) B578137
theorem B344891 : Blo 227813 344891 := bstep (se 1 (by rfl) ⟨258668, by rfl⟩ : syracuseStep 344891 = 517337) B517337
theorem B344951 : Blo 227813 344951 := bstep (se 1 (by rfl) ⟨258713, by rfl⟩ : syracuseStep 344951 = 517427) B517427
theorem B344975 : Blo 227813 344975 := bstep (se 1 (by rfl) ⟨258731, by rfl⟩ : syracuseStep 344975 = 517463) B517463
theorem B1950617 : Blo 227813 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B345017 : Blo 227813 345017 := bstep (se 2 (by rfl) ⟨129381, by rfl⟩ : syracuseStep 345017 = 258763) B258763
theorem B345095 : Blo 227813 345095 := bstep (se 1 (by rfl) ⟨258821, by rfl⟩ : syracuseStep 345095 = 517643) B517643
theorem B345131 : Blo 227813 345131 := bstep (se 1 (by rfl) ⟨258848, by rfl⟩ : syracuseStep 345131 = 517697) B517697
theorem B345161 : Blo 227813 345161 := bstep (se 2 (by rfl) ⟨129435, by rfl⟩ : syracuseStep 345161 = 258871) B258871
theorem B345275 : Blo 227813 345275 := bstep (se 1 (by rfl) ⟨258956, by rfl⟩ : syracuseStep 345275 = 517913) B517913
theorem B1885421 : Blo 227813 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B345335 : Blo 227813 345335 := bstep (se 1 (by rfl) ⟨259001, by rfl⟩ : syracuseStep 345335 = 518003) B518003
theorem B345359 : Blo 227813 345359 := bstep (se 1 (by rfl) ⟨259019, by rfl⟩ : syracuseStep 345359 = 518039) B518039
theorem B345401 : Blo 227813 345401 := bstep (se 2 (by rfl) ⟨129525, by rfl⟩ : syracuseStep 345401 = 259051) B259051
theorem B771443 : Blo 227813 771443 := bstep (se 1 (by rfl) ⟨578582, by rfl⟩ : syracuseStep 771443 = 1157165) B1157165
theorem B345479 : Blo 227813 345479 := bstep (se 1 (by rfl) ⟨259109, by rfl⟩ : syracuseStep 345479 = 518219) B518219
theorem B345515 : Blo 227813 345515 := bstep (se 1 (by rfl) ⟨259136, by rfl⟩ : syracuseStep 345515 = 518273) B518273
theorem B345545 : Blo 227813 345545 := bstep (se 2 (by rfl) ⟨129579, by rfl⟩ : syracuseStep 345545 = 259159) B259159
theorem B345659 : Blo 227813 345659 := bstep (se 1 (by rfl) ⟨259244, by rfl⟩ : syracuseStep 345659 = 518489) B518489
theorem B345719 : Blo 227813 345719 := bstep (se 1 (by rfl) ⟨259289, by rfl⟩ : syracuseStep 345719 = 518579) B518579
theorem B345743 : Blo 227813 345743 := bstep (se 1 (by rfl) ⟨259307, by rfl⟩ : syracuseStep 345743 = 518615) B518615
theorem B313003 : Blo 227813 313003 := bstep (se 1 (by rfl) ⟨234752, by rfl⟩ : syracuseStep 313003 = 469505) B469505
theorem B345785 : Blo 227813 345785 := bstep (se 2 (by rfl) ⟨129669, by rfl⟩ : syracuseStep 345785 = 259339) B259339
theorem B345863 : Blo 227813 345863 := bstep (se 1 (by rfl) ⟨259397, by rfl⟩ : syracuseStep 345863 = 518795) B518795
theorem B345899 : Blo 227813 345899 := bstep (se 1 (by rfl) ⟨259424, by rfl⟩ : syracuseStep 345899 = 518849) B518849
theorem B345929 : Blo 227813 345929 := bstep (se 2 (by rfl) ⟨129723, by rfl⟩ : syracuseStep 345929 = 259447) B259447
theorem B346043 : Blo 227813 346043 := bstep (se 1 (by rfl) ⟨259532, by rfl⟩ : syracuseStep 346043 = 519065) B519065
theorem B1165265 : Blo 227813 1165265 := bstep (se 2 (by rfl) ⟨436974, by rfl⟩ : syracuseStep 1165265 = 873949) B873949
theorem B346103 : Blo 227813 346103 := bstep (se 1 (by rfl) ⟨259577, by rfl⟩ : syracuseStep 346103 = 519155) B519155
theorem B346127 : Blo 227813 346127 := bstep (se 1 (by rfl) ⟨259595, by rfl⟩ : syracuseStep 346127 = 519191) B519191
theorem B641053 : Blo 227813 641053 := bstep (se 3 (by rfl) ⟨120197, by rfl⟩ : syracuseStep 641053 = 240395) B240395
theorem B346169 : Blo 227813 346169 := bstep (se 2 (by rfl) ⟨129813, by rfl⟩ : syracuseStep 346169 = 259627) B259627
theorem B346247 : Blo 227813 346247 := bstep (se 1 (by rfl) ⟨259685, by rfl⟩ : syracuseStep 346247 = 519371) B519371
theorem B346283 : Blo 227813 346283 := bstep (se 1 (by rfl) ⟨259712, by rfl⟩ : syracuseStep 346283 = 519425) B519425
theorem B346313 : Blo 227813 346313 := bstep (se 2 (by rfl) ⟨129867, by rfl⟩ : syracuseStep 346313 = 259735) B259735
theorem B936251 : Blo 227813 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B346427 : Blo 227813 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B346487 : Blo 227813 346487 := bstep (se 1 (by rfl) ⟨259865, by rfl⟩ : syracuseStep 346487 = 519731) B519731
theorem B346511 : Blo 227813 346511 := bstep (se 1 (by rfl) ⟨259883, by rfl⟩ : syracuseStep 346511 = 519767) B519767
theorem B346553 : Blo 227813 346553 := bstep (se 2 (by rfl) ⟨129957, by rfl⟩ : syracuseStep 346553 = 259915) B259915
theorem B346631 : Blo 227813 346631 := bstep (se 1 (by rfl) ⟨259973, by rfl⟩ : syracuseStep 346631 = 519947) B519947
theorem B346667 : Blo 227813 346667 := bstep (se 1 (by rfl) ⟨260000, by rfl⟩ : syracuseStep 346667 = 520001) B520001
theorem B346697 : Blo 227813 346697 := bstep (se 2 (by rfl) ⟨130011, by rfl⟩ : syracuseStep 346697 = 260023) B260023
theorem B346811 : Blo 227813 346811 := bstep (se 1 (by rfl) ⟨260108, by rfl⟩ : syracuseStep 346811 = 520217) B520217
theorem B346871 : Blo 227813 346871 := bstep (se 1 (by rfl) ⟨260153, by rfl⟩ : syracuseStep 346871 = 520307) B520307
theorem B346895 : Blo 227813 346895 := bstep (se 1 (by rfl) ⟨260171, by rfl⟩ : syracuseStep 346895 = 520343) B520343
theorem B346937 : Blo 227813 346937 := bstep (se 2 (by rfl) ⟨130101, by rfl⟩ : syracuseStep 346937 = 260203) B260203
theorem B347015 : Blo 227813 347015 := bstep (se 1 (by rfl) ⟨260261, by rfl⟩ : syracuseStep 347015 = 520523) B520523
theorem B347051 : Blo 227813 347051 := bstep (se 1 (by rfl) ⟨260288, by rfl⟩ : syracuseStep 347051 = 520577) B520577
theorem B347081 : Blo 227813 347081 := bstep (se 2 (by rfl) ⟨130155, by rfl⟩ : syracuseStep 347081 = 260311) B260311
theorem B347195 : Blo 227813 347195 := bstep (se 1 (by rfl) ⟨260396, by rfl⟩ : syracuseStep 347195 = 520793) B520793
theorem B1952855 : Blo 227813 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B347255 : Blo 227813 347255 := bstep (se 1 (by rfl) ⟨260441, by rfl⟩ : syracuseStep 347255 = 520883) B520883
theorem B347279 : Blo 227813 347279 := bstep (se 1 (by rfl) ⟨260459, by rfl⟩ : syracuseStep 347279 = 520919) B520919
theorem B576659 : Blo 227813 576659 := bstep (se 1 (by rfl) ⟨432494, by rfl⟩ : syracuseStep 576659 = 864989) B864989
theorem B347321 : Blo 227813 347321 := bstep (se 2 (by rfl) ⟨130245, by rfl⟩ : syracuseStep 347321 = 260491) B260491
theorem B347399 : Blo 227813 347399 := bstep (se 1 (by rfl) ⟨260549, by rfl⟩ : syracuseStep 347399 = 521099) B521099
theorem B347435 : Blo 227813 347435 := bstep (se 1 (by rfl) ⟨260576, by rfl⟩ : syracuseStep 347435 = 521153) B521153
theorem B347465 : Blo 227813 347465 := bstep (se 2 (by rfl) ⟨130299, by rfl⟩ : syracuseStep 347465 = 260599) B260599
theorem B576953 : Blo 227813 576953 := bstep (se 2 (by rfl) ⟨216357, by rfl⟩ : syracuseStep 576953 = 432715) B432715
theorem B413113 : Blo 227813 413113 := bstep (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) B309835
theorem B347579 : Blo 227813 347579 := bstep (se 1 (by rfl) ⟨260684, by rfl⟩ : syracuseStep 347579 = 521369) B521369
theorem B1953233 : Blo 227813 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B347639 : Blo 227813 347639 := bstep (se 1 (by rfl) ⟨260729, by rfl⟩ : syracuseStep 347639 = 521459) B521459
theorem B347663 : Blo 227813 347663 := bstep (se 1 (by rfl) ⟨260747, by rfl⟩ : syracuseStep 347663 = 521495) B521495
theorem B347705 : Blo 227813 347705 := bstep (se 2 (by rfl) ⟨130389, by rfl⟩ : syracuseStep 347705 = 260779) B260779
theorem B740983 : Blo 227813 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B2772751 : Blo 227813 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B1298213 : Blo 227813 1298213 := bstep (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) B243415
theorem B774035 : Blo 227813 774035 := bstep (se 1 (by rfl) ⟨580526, by rfl⟩ : syracuseStep 774035 = 1161053) B1161053
theorem B1462283 : Blo 227813 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B1167371 : Blo 227813 1167371 := bstep (se 1 (by rfl) ⟨875528, by rfl⟩ : syracuseStep 1167371 = 1751057) B1751057
theorem B872477 : Blo 227813 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B872491 : Blo 227813 872491 := bstep (se 1 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 872491 = 1308737) B1308737
theorem B577651 : Blo 227813 577651 := bstep (se 1 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 577651 = 866477) B866477
theorem B1167533 : Blo 227813 1167533 := bstep (se 3 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 1167533 = 437825) B437825
theorem B577793 : Blo 227813 577793 := bstep (se 2 (by rfl) ⟨216672, by rfl⟩ : syracuseStep 577793 = 433345) B433345
theorem B1298987 : Blo 227813 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B1102403 : Blo 227813 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B578249 : Blo 227813 578249 := bstep (se 2 (by rfl) ⟨216843, by rfl⟩ : syracuseStep 578249 = 433687) B433687
theorem B512783 : Blo 227813 512783 := bstep (se 1 (by rfl) ⟨384587, by rfl⟩ : syracuseStep 512783 = 769175) B769175
theorem B512801 : Blo 227813 512801 := bstep (se 2 (by rfl) ⟨192300, by rfl⟩ : syracuseStep 512801 = 384601) B384601
theorem B578603 : Blo 227813 578603 := bstep (se 1 (by rfl) ⟨433952, by rfl⟩ : syracuseStep 578603 = 867905) B867905
theorem B513143 : Blo 227813 513143 := bstep (se 1 (by rfl) ⟨384857, by rfl⟩ : syracuseStep 513143 = 769715) B769715
theorem B775439 : Blo 227813 775439 := bstep (se 1 (by rfl) ⟨581579, by rfl⟩ : syracuseStep 775439 = 1163159) B1163159
theorem B513323 : Blo 227813 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B5952953 : Blo 227813 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B775709 : Blo 227813 775709 := bstep (se 3 (by rfl) ⟨145445, by rfl⟩ : syracuseStep 775709 = 290891) B290891
theorem B513683 : Blo 227813 513683 := bstep (se 1 (by rfl) ⟨385262, by rfl⟩ : syracuseStep 513683 = 770525) B770525
theorem B513737 : Blo 227813 513737 := bstep (se 2 (by rfl) ⟨192651, by rfl⟩ : syracuseStep 513737 = 385303) B385303
theorem B1169153 : Blo 227813 1169153 := bstep (se 2 (by rfl) ⟨438432, by rfl⟩ : syracuseStep 1169153 = 876865) B876865
theorem B1300445 : Blo 227813 1300445 := bstep (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) B487667
theorem B579595 : Blo 227813 579595 := bstep (se 1 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 579595 = 869393) B869393
theorem B1759319 : Blo 227813 1759319 := bstep (se 1 (by rfl) ⟨1319489, by rfl⟩ : syracuseStep 1759319 = 2638979) B2638979
theorem B579737 : Blo 227813 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B2840777 : Blo 227813 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B579899 : Blo 227813 579899 := bstep (se 1 (by rfl) ⟨434924, by rfl⟩ : syracuseStep 579899 = 869849) B869849
theorem B514439 : Blo 227813 514439 := bstep (se 1 (by rfl) ⟨385829, by rfl⟩ : syracuseStep 514439 = 771659) B771659
theorem B1169963 : Blo 227813 1169963 := bstep (se 1 (by rfl) ⟨877472, by rfl⟩ : syracuseStep 1169963 = 1754945) B1754945
theorem B514619 : Blo 227813 514619 := bstep (se 1 (by rfl) ⟨385964, by rfl⟩ : syracuseStep 514619 = 771929) B771929
theorem B580243 : Blo 227813 580243 := bstep (se 1 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 580243 = 870365) B870365
theorem B514745 : Blo 227813 514745 := bstep (se 2 (by rfl) ⟨193029, by rfl⟩ : syracuseStep 514745 = 386059) B386059
theorem B1956545 : Blo 227813 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B580385 : Blo 227813 580385 := bstep (se 2 (by rfl) ⟨217644, by rfl⟩ : syracuseStep 580385 = 435289) B435289
theorem B777113 : Blo 227813 777113 := bstep (se 2 (by rfl) ⟨291417, by rfl⟩ : syracuseStep 777113 = 582835) B582835
theorem B515087 : Blo 227813 515087 := bstep (se 1 (by rfl) ⟨386315, by rfl⟩ : syracuseStep 515087 = 772631) B772631
theorem B515105 : Blo 227813 515105 := bstep (se 2 (by rfl) ⟨193164, by rfl⟩ : syracuseStep 515105 = 386329) B386329
theorem B548041 : Blo 227813 548041 := bstep (se 2 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 548041 = 411031) B411031
theorem B515447 : Blo 227813 515447 := bstep (se 1 (by rfl) ⟨386585, by rfl⟩ : syracuseStep 515447 = 773171) B773171
theorem B941465 : Blo 227813 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B1400273 : Blo 227813 1400273 := bstep (se 2 (by rfl) ⟨525102, by rfl⟩ : syracuseStep 1400273 = 1050205) B1050205
theorem B384527 : Blo 227813 384527 := bstep (se 1 (by rfl) ⟨288395, by rfl⟩ : syracuseStep 384527 = 576791) B576791
theorem B515627 : Blo 227813 515627 := bstep (se 1 (by rfl) ⟨386720, by rfl⟩ : syracuseStep 515627 = 773441) B773441
theorem B777815 : Blo 227813 777815 := bstep (se 1 (by rfl) ⟨583361, by rfl⟩ : syracuseStep 777815 = 1166723) B1166723
theorem B581377 : Blo 227813 581377 := bstep (se 2 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 581377 = 436033) B436033
theorem B1171259 : Blo 227813 1171259 := bstep (se 1 (by rfl) ⟨878444, by rfl⟩ : syracuseStep 1171259 = 1756889) B1756889
theorem B515987 : Blo 227813 515987 := bstep (se 1 (by rfl) ⟨386990, by rfl⟩ : syracuseStep 515987 = 773981) B773981
theorem B417683 : Blo 227813 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B516041 : Blo 227813 516041 := bstep (se 2 (by rfl) ⟨193515, by rfl⟩ : syracuseStep 516041 = 387031) B387031
theorem B1368029 : Blo 227813 1368029 := bstep (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) B513011
theorem B1171421 : Blo 227813 1171421 := bstep (se 3 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 1171421 = 439283) B439283
theorem B385067 : Blo 227813 385067 := bstep (se 1 (by rfl) ⟨288800, by rfl⟩ : syracuseStep 385067 = 577601) B577601
theorem B778301 : Blo 227813 778301 := bstep (se 3 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 778301 = 291863) B291863
theorem B1171745 : Blo 227813 1171745 := bstep (se 2 (by rfl) ⟨439404, by rfl⟩ : syracuseStep 1171745 = 878809) B878809
theorem B581975 : Blo 227813 581975 := bstep (se 1 (by rfl) ⟨436481, by rfl⟩ : syracuseStep 581975 = 872963) B872963
theorem B385465 : Blo 227813 385465 := bstep (se 2 (by rfl) ⟨144549, by rfl⟩ : syracuseStep 385465 = 289099) B289099
theorem B582187 : Blo 227813 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B516743 : Blo 227813 516743 := bstep (se 1 (by rfl) ⟨387557, by rfl⟩ : syracuseStep 516743 = 775115) B775115
theorem B1172141 : Blo 227813 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B582329 : Blo 227813 582329 := bstep (se 2 (by rfl) ⟨218373, by rfl⟩ : syracuseStep 582329 = 436747) B436747
theorem B516923 : Blo 227813 516923 := bstep (se 1 (by rfl) ⟨387692, by rfl⟩ : syracuseStep 516923 = 775385) B775385
theorem B2810699 : Blo 227813 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B517049 : Blo 227813 517049 := bstep (se 2 (by rfl) ⟨193893, by rfl⟩ : syracuseStep 517049 = 387787) B387787
theorem B1303613 : Blo 227813 1303613 := bstep (se 3 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 1303613 = 488855) B488855
theorem B877655 : Blo 227813 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B386167 : Blo 227813 386167 := bstep (se 1 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 386167 = 579251) B579251
theorem B5596397 : Blo 227813 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B1172717 : Blo 227813 1172717 := bstep (se 3 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 1172717 = 439769) B439769
theorem B550145 : Blo 227813 550145 := bstep (se 2 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 550145 = 412609) B412609
theorem B517391 : Blo 227813 517391 := bstep (se 1 (by rfl) ⟨388043, by rfl⟩ : syracuseStep 517391 = 776087) B776087
theorem B517409 : Blo 227813 517409 := bstep (se 2 (by rfl) ⟨194028, by rfl⟩ : syracuseStep 517409 = 388057) B388057
theorem B386363 : Blo 227813 386363 := bstep (se 1 (by rfl) ⟨289772, by rfl⟩ : syracuseStep 386363 = 579545) B579545
theorem B779705 : Blo 227813 779705 := bstep (se 2 (by rfl) ⟨292389, by rfl⟩ : syracuseStep 779705 = 584779) B584779
theorem B1762859 : Blo 227813 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B615995 : Blo 227813 615995 := bstep (se 1 (by rfl) ⟨461996, by rfl⟩ : syracuseStep 615995 = 923993) B923993
theorem B878141 : Blo 227813 878141 := bstep (se 3 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 878141 = 329303) B329303
theorem B517751 : Blo 227813 517751 := bstep (se 1 (by rfl) ⟨388313, by rfl⟩ : syracuseStep 517751 = 776627) B776627
theorem B583321 : Blo 227813 583321 := bstep (se 2 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 583321 = 437491) B437491
theorem B386761 : Blo 227813 386761 := bstep (se 2 (by rfl) ⟨145035, by rfl⟩ : syracuseStep 386761 = 290071) B290071
theorem B517931 : Blo 227813 517931 := bstep (se 1 (by rfl) ⟨388448, by rfl⟩ : syracuseStep 517931 = 776897) B776897
theorem B583483 : Blo 227813 583483 := bstep (se 1 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 583483 = 875225) B875225
theorem B780167 : Blo 227813 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B583625 : Blo 227813 583625 := bstep (se 2 (by rfl) ⟨218859, by rfl⟩ : syracuseStep 583625 = 437719) B437719
theorem B288775 : Blo 227813 288775 := bstep (se 1 (by rfl) ⟨216581, by rfl⟩ : syracuseStep 288775 = 433163) B433163
theorem B780299 : Blo 227813 780299 := bstep (se 1 (by rfl) ⟨585224, by rfl⟩ : syracuseStep 780299 = 1170449) B1170449
theorem B1173527 : Blo 227813 1173527 := bstep (se 1 (by rfl) ⟨880145, by rfl⟩ : syracuseStep 1173527 = 1760291) B1760291
theorem B780407 : Blo 227813 780407 := bstep (se 1 (by rfl) ⟨585305, by rfl⟩ : syracuseStep 780407 = 1170611) B1170611
theorem B518291 : Blo 227813 518291 := bstep (se 1 (by rfl) ⟨388718, by rfl⟩ : syracuseStep 518291 = 777437) B777437
theorem B1665197 : Blo 227813 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B518345 : Blo 227813 518345 := bstep (se 2 (by rfl) ⟨194379, by rfl⟩ : syracuseStep 518345 = 388759) B388759
theorem B583969 : Blo 227813 583969 := bstep (se 2 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 583969 = 437977) B437977
theorem B256315 : Blo 227813 256315 := bstep (se 1 (by rfl) ⟨192236, by rfl⟩ : syracuseStep 256315 = 384473) B384473
theorem B387463 : Blo 227813 387463 := bstep (se 1 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 387463 = 581195) B581195
theorem B4712849 : Blo 227813 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B289271 : Blo 227813 289271 := bstep (se 1 (by rfl) ⟨216953, by rfl⟩ : syracuseStep 289271 = 433907) B433907
theorem B617075 : Blo 227813 617075 := bstep (se 1 (by rfl) ⟨462806, by rfl⟩ : syracuseStep 617075 = 925613) B925613
theorem B289423 : Blo 227813 289423 := bstep (se 1 (by rfl) ⟨217067, by rfl⟩ : syracuseStep 289423 = 434135) B434135
theorem B781001 : Blo 227813 781001 := bstep (se 2 (by rfl) ⟨292875, by rfl⟩ : syracuseStep 781001 = 585751) B585751
theorem B256783 : Blo 227813 256783 := bstep (se 1 (by rfl) ⟨192587, by rfl⟩ : syracuseStep 256783 = 385175) B385175
theorem B289595 : Blo 227813 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B584567 : Blo 227813 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B519047 : Blo 227813 519047 := bstep (se 1 (by rfl) ⟨389285, by rfl⟩ : syracuseStep 519047 = 778571) B778571
theorem B5565347 : Blo 227813 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B879569 : Blo 227813 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B388111 : Blo 227813 388111 := bstep (se 1 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 388111 = 582167) B582167
theorem B1109015 : Blo 227813 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B519227 : Blo 227813 519227 := bstep (se 1 (by rfl) ⟨389420, by rfl⟩ : syracuseStep 519227 = 778841) B778841
theorem B650359 : Blo 227813 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B519353 : Blo 227813 519353 := bstep (se 2 (by rfl) ⟨194757, by rfl⟩ : syracuseStep 519353 = 389515) B389515
theorem B257287 : Blo 227813 257287 := bstep (se 1 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 257287 = 385931) B385931
theorem B1240379 : Blo 227813 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B781703 : Blo 227813 781703 := bstep (se 1 (by rfl) ⟨586277, by rfl⟩ : syracuseStep 781703 = 1172555) B1172555
theorem B1306003 : Blo 227813 1306003 := bstep (se 1 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 1306003 = 1959005) B1959005
theorem B257467 : Blo 227813 257467 := bstep (se 1 (by rfl) ⟨193100, by rfl⟩ : syracuseStep 257467 = 386201) B386201
theorem B519695 : Blo 227813 519695 := bstep (se 1 (by rfl) ⟨389771, by rfl⟩ : syracuseStep 519695 = 779543) B779543
theorem B519713 : Blo 227813 519713 := bstep (se 2 (by rfl) ⟨194892, by rfl⟩ : syracuseStep 519713 = 389785) B389785
theorem B388651 : Blo 227813 388651 := bstep (se 1 (by rfl) ⟨291488, by rfl⟩ : syracuseStep 388651 = 582977) B582977
theorem B1568375 : Blo 227813 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B388793 : Blo 227813 388793 := bstep (se 2 (by rfl) ⟨145797, by rfl⟩ : syracuseStep 388793 = 291595) B291595
theorem B782081 : Blo 227813 782081 := bstep (se 2 (by rfl) ⟨293280, by rfl⟩ : syracuseStep 782081 = 586561) B586561
theorem B290567 : Blo 227813 290567 := bstep (se 1 (by rfl) ⟨217925, by rfl⟩ : syracuseStep 290567 = 435851) B435851
theorem B520055 : Blo 227813 520055 := bstep (se 1 (by rfl) ⟨390041, by rfl⟩ : syracuseStep 520055 = 780083) B780083
theorem B257935 : Blo 227813 257935 := bstep (se 1 (by rfl) ⟨193451, by rfl⟩ : syracuseStep 257935 = 386903) B386903
theorem B520235 : Blo 227813 520235 := bstep (se 1 (by rfl) ⟨390176, by rfl⟩ : syracuseStep 520235 = 780353) B780353
theorem B5304365 : Blo 227813 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B2945069 : Blo 227813 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B2781317 : Blo 227813 2781317 := bstep (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) B521497
theorem B585863 : Blo 227813 585863 := bstep (se 1 (by rfl) ⟨439397, by rfl⟩ : syracuseStep 585863 = 878795) B878795
theorem B585913 : Blo 227813 585913 := bstep (se 2 (by rfl) ⟨219717, by rfl⟩ : syracuseStep 585913 = 439435) B439435
theorem B651635 : Blo 227813 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B389495 : Blo 227813 389495 := bstep (se 1 (by rfl) ⟨292121, by rfl⟩ : syracuseStep 389495 = 584243) B584243
theorem B258439 : Blo 227813 258439 := bstep (se 1 (by rfl) ⟨193829, by rfl⟩ : syracuseStep 258439 = 387659) B387659
theorem B1503623 : Blo 227813 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B291215 : Blo 227813 291215 := bstep (se 1 (by rfl) ⟨218411, by rfl⟩ : syracuseStep 291215 = 436823) B436823
theorem B520595 : Blo 227813 520595 := bstep (se 1 (by rfl) ⟨390446, by rfl⟩ : syracuseStep 520595 = 780893) B780893
theorem B520649 : Blo 227813 520649 := bstep (se 2 (by rfl) ⟨195243, by rfl⟩ : syracuseStep 520649 = 390487) B390487
theorem B258619 : Blo 227813 258619 := bstep (se 1 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 258619 = 387929) B387929
theorem B651863 : Blo 227813 651863 := bstep (se 1 (by rfl) ⟨488897, by rfl⟩ : syracuseStep 651863 = 977795) B977795
theorem B586511 : Blo 227813 586511 := bstep (se 1 (by rfl) ⟨439883, by rfl⟩ : syracuseStep 586511 = 879767) B879767
theorem B1471283 : Blo 227813 1471283 := bstep (se 1 (by rfl) ⟨1103462, by rfl⟩ : syracuseStep 1471283 = 2206925) B2206925
theorem B389947 : Blo 227813 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B521095 : Blo 227813 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B979897 : Blo 227813 979897 := bstep (se 2 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 979897 = 734923) B734923
theorem B390089 : Blo 227813 390089 := bstep (se 2 (by rfl) ⟨146283, by rfl⟩ : syracuseStep 390089 = 292567) B292567
theorem B259087 : Blo 227813 259087 := bstep (se 1 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 259087 = 388631) B388631
theorem B1307735 : Blo 227813 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B521351 : Blo 227813 521351 := bstep (se 1 (by rfl) ⟨391013, by rfl⟩ : syracuseStep 521351 = 782027) B782027
theorem B90273005 : Blo 227813 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B521531 : Blo 227813 521531 := bstep (se 1 (by rfl) ⟨391148, by rfl⟩ : syracuseStep 521531 = 782297) B782297
theorem B259591 : Blo 227813 259591 := bstep (se 1 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 259591 = 389387) B389387
theorem B3995237 : Blo 227813 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B390791 : Blo 227813 390791 := bstep (se 1 (by rfl) ⟨293093, by rfl⟩ : syracuseStep 390791 = 586187) B586187
theorem B1242797 : Blo 227813 1242797 := bstep (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) B466049
theorem B259771 : Blo 227813 259771 := bstep (se 1 (by rfl) ⟨194828, by rfl⟩ : syracuseStep 259771 = 389657) B389657
theorem B554867 : Blo 227813 554867 := bstep (se 1 (by rfl) ⟨416150, by rfl⟩ : syracuseStep 554867 = 832301) B832301
theorem B1112075 : Blo 227813 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B653447 : Blo 227813 653447 := bstep (se 1 (by rfl) ⟨490085, by rfl⟩ : syracuseStep 653447 = 980171) B980171
theorem B260239 : Blo 227813 260239 := bstep (se 1 (by rfl) ⟨195179, by rfl⟩ : syracuseStep 260239 = 390359) B390359
theorem B784655 : Blo 227813 784655 := bstep (se 1 (by rfl) ⟨588491, by rfl⟩ : syracuseStep 784655 = 1176983) B1176983
theorem B653629 : Blo 227813 653629 := bstep (se 3 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 653629 = 245111) B245111
theorem B227847 : Blo 227813 227847 := bstep (se 1 (by rfl) ⟨170885, by rfl⟩ : syracuseStep 227847 = 341771) B341771
theorem B227855 : Blo 227813 227855 := bstep (se 1 (by rfl) ⟨170891, by rfl⟩ : syracuseStep 227855 = 341783) B341783
theorem B227899 : Blo 227813 227899 := bstep (se 1 (by rfl) ⟨170924, by rfl⟩ : syracuseStep 227899 = 341849) B341849
theorem B490043 : Blo 227813 490043 := bstep (se 1 (by rfl) ⟨367532, by rfl⟩ : syracuseStep 490043 = 735065) B735065
theorem B227975 : Blo 227813 227975 := bstep (se 1 (by rfl) ⟨170981, by rfl⟩ : syracuseStep 227975 = 341963) B341963
theorem B260743 : Blo 227813 260743 := bstep (se 1 (by rfl) ⟨195557, by rfl⟩ : syracuseStep 260743 = 391115) B391115
theorem B227983 : Blo 227813 227983 := bstep (se 1 (by rfl) ⟨170987, by rfl⟩ : syracuseStep 227983 = 341975) B341975
theorem B228027 : Blo 227813 228027 := bstep (se 1 (by rfl) ⟨171020, by rfl⟩ : syracuseStep 228027 = 342041) B342041
theorem B228103 : Blo 227813 228103 := bstep (se 1 (by rfl) ⟨171077, by rfl⟩ : syracuseStep 228103 = 342155) B342155
theorem B228111 : Blo 227813 228111 := bstep (se 1 (by rfl) ⟨171083, by rfl⟩ : syracuseStep 228111 = 342167) B342167
theorem B654095 : Blo 227813 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B228155 : Blo 227813 228155 := bstep (se 1 (by rfl) ⟨171116, by rfl⟩ : syracuseStep 228155 = 342233) B342233
theorem B555835 : Blo 227813 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B228231 : Blo 227813 228231 := bstep (se 1 (by rfl) ⟨171173, by rfl⟩ : syracuseStep 228231 = 342347) B342347
theorem B981895 : Blo 227813 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B228239 : Blo 227813 228239 := bstep (se 1 (by rfl) ⟨171179, by rfl⟩ : syracuseStep 228239 = 342359) B342359
theorem B228283 : Blo 227813 228283 := bstep (se 1 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 228283 = 342425) B342425
theorem B326587 : Blo 227813 326587 := bstep (se 1 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 326587 = 489881) B489881
theorem B228359 : Blo 227813 228359 := bstep (se 1 (by rfl) ⟨171269, by rfl⟩ : syracuseStep 228359 = 342539) B342539
theorem B228367 : Blo 227813 228367 := bstep (se 1 (by rfl) ⟨171275, by rfl⟩ : syracuseStep 228367 = 342551) B342551
theorem B228411 : Blo 227813 228411 := bstep (se 1 (by rfl) ⟨171308, by rfl⟩ : syracuseStep 228411 = 342617) B342617
theorem B228487 : Blo 227813 228487 := bstep (se 1 (by rfl) ⟨171365, by rfl⟩ : syracuseStep 228487 = 342731) B342731
theorem B228495 : Blo 227813 228495 := bstep (se 1 (by rfl) ⟨171371, by rfl⟩ : syracuseStep 228495 = 342743) B342743
theorem B228539 : Blo 227813 228539 := bstep (se 1 (by rfl) ⟨171404, by rfl⟩ : syracuseStep 228539 = 342809) B342809
theorem B1965293 : Blo 227813 1965293 := bstep (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) B736985
theorem B228615 : Blo 227813 228615 := bstep (se 1 (by rfl) ⟨171461, by rfl⟩ : syracuseStep 228615 = 342923) B342923
theorem B228623 : Blo 227813 228623 := bstep (se 1 (by rfl) ⟨171467, by rfl⟩ : syracuseStep 228623 = 342935) B342935
theorem B228667 : Blo 227813 228667 := bstep (se 1 (by rfl) ⟨171500, by rfl⟩ : syracuseStep 228667 = 343001) B343001
theorem B1047923 : Blo 227813 1047923 := bstep (se 1 (by rfl) ⟨785942, by rfl⟩ : syracuseStep 1047923 = 1571885) B1571885
theorem B228743 : Blo 227813 228743 := bstep (se 1 (by rfl) ⟨171557, by rfl⟩ : syracuseStep 228743 = 343115) B343115
theorem B228751 : Blo 227813 228751 := bstep (se 1 (by rfl) ⟨171563, by rfl⟩ : syracuseStep 228751 = 343127) B343127
theorem B228795 : Blo 227813 228795 := bstep (se 1 (by rfl) ⟨171596, by rfl⟩ : syracuseStep 228795 = 343193) B343193
theorem B228871 : Blo 227813 228871 := bstep (se 1 (by rfl) ⟨171653, by rfl⟩ : syracuseStep 228871 = 343307) B343307
theorem B622091 : Blo 227813 622091 := bstep (se 1 (by rfl) ⟨466568, by rfl⟩ : syracuseStep 622091 = 933137) B933137
theorem B228879 : Blo 227813 228879 := bstep (se 1 (by rfl) ⟨171659, by rfl⟩ : syracuseStep 228879 = 343319) B343319
theorem B228923 : Blo 227813 228923 := bstep (se 1 (by rfl) ⟨171692, by rfl⟩ : syracuseStep 228923 = 343385) B343385
theorem B327287 : Blo 227813 327287 := bstep (se 1 (by rfl) ⟨245465, by rfl⟩ : syracuseStep 327287 = 490931) B490931
theorem B228999 : Blo 227813 228999 := bstep (se 1 (by rfl) ⟨171749, by rfl⟩ : syracuseStep 228999 = 343499) B343499
theorem B229007 : Blo 227813 229007 := bstep (se 1 (by rfl) ⟨171755, by rfl⟩ : syracuseStep 229007 = 343511) B343511
theorem B229051 : Blo 227813 229051 := bstep (se 1 (by rfl) ⟨171788, by rfl⟩ : syracuseStep 229051 = 343577) B343577
theorem B229127 : Blo 227813 229127 := bstep (se 1 (by rfl) ⟨171845, by rfl⟩ : syracuseStep 229127 = 343691) B343691
theorem B229135 : Blo 227813 229135 := bstep (se 1 (by rfl) ⟨171851, by rfl⟩ : syracuseStep 229135 = 343703) B343703
theorem B229179 : Blo 227813 229179 := bstep (se 1 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 229179 = 343769) B343769
theorem B229255 : Blo 227813 229255 := bstep (se 1 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 229255 = 343883) B343883
theorem B229263 : Blo 227813 229263 := bstep (se 1 (by rfl) ⟨171947, by rfl⟩ : syracuseStep 229263 = 343895) B343895
theorem B1965977 : Blo 227813 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B229307 : Blo 227813 229307 := bstep (se 1 (by rfl) ⟨171980, by rfl⟩ : syracuseStep 229307 = 343961) B343961
theorem B5898269 : Blo 227813 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B229415 : Blo 227813 229415 := bstep (se 1 (by rfl) ⟨172061, by rfl⟩ : syracuseStep 229415 = 344123) B344123
theorem B5865533 : Blo 227813 5865533 := bstep (se 3 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 5865533 = 2199575) B2199575
theorem B229455 : Blo 227813 229455 := bstep (se 1 (by rfl) ⟨172091, by rfl⟩ : syracuseStep 229455 = 344183) B344183
theorem B229471 : Blo 227813 229471 := bstep (se 1 (by rfl) ⟨172103, by rfl⟩ : syracuseStep 229471 = 344207) B344207
theorem B229499 : Blo 227813 229499 := bstep (se 1 (by rfl) ⟨172124, by rfl⟩ : syracuseStep 229499 = 344249) B344249
theorem B229551 : Blo 227813 229551 := bstep (se 1 (by rfl) ⟨172163, by rfl⟩ : syracuseStep 229551 = 344327) B344327
theorem B229575 : Blo 227813 229575 := bstep (se 1 (by rfl) ⟨172181, by rfl⟩ : syracuseStep 229575 = 344363) B344363
theorem B229595 : Blo 227813 229595 := bstep (se 1 (by rfl) ⟨172196, by rfl⟩ : syracuseStep 229595 = 344393) B344393
theorem B229671 : Blo 227813 229671 := bstep (se 1 (by rfl) ⟨172253, by rfl⟩ : syracuseStep 229671 = 344507) B344507
theorem B1868093 : Blo 227813 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B229711 : Blo 227813 229711 := bstep (se 1 (by rfl) ⟨172283, by rfl⟩ : syracuseStep 229711 = 344567) B344567
theorem B229727 : Blo 227813 229727 := bstep (se 1 (by rfl) ⟨172295, by rfl⟩ : syracuseStep 229727 = 344591) B344591
theorem B229755 : Blo 227813 229755 := bstep (se 1 (by rfl) ⟨172316, by rfl⟩ : syracuseStep 229755 = 344633) B344633
theorem B229807 : Blo 227813 229807 := bstep (se 1 (by rfl) ⟨172355, by rfl⟩ : syracuseStep 229807 = 344711) B344711
theorem B229831 : Blo 227813 229831 := bstep (se 1 (by rfl) ⟨172373, by rfl⟩ : syracuseStep 229831 = 344747) B344747
theorem B229851 : Blo 227813 229851 := bstep (se 1 (by rfl) ⟨172388, by rfl⟩ : syracuseStep 229851 = 344777) B344777
theorem B1180169 : Blo 227813 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B492041 : Blo 227813 492041 := bstep (se 2 (by rfl) ⟨184515, by rfl⟩ : syracuseStep 492041 = 369031) B369031
theorem B229927 : Blo 227813 229927 := bstep (se 1 (by rfl) ⟨172445, by rfl⟩ : syracuseStep 229927 = 344891) B344891
theorem B229967 : Blo 227813 229967 := bstep (se 1 (by rfl) ⟨172475, by rfl⟩ : syracuseStep 229967 = 344951) B344951
theorem B229983 : Blo 227813 229983 := bstep (se 1 (by rfl) ⟨172487, by rfl⟩ : syracuseStep 229983 = 344975) B344975
theorem B230011 : Blo 227813 230011 := bstep (se 1 (by rfl) ⟨172508, by rfl⟩ : syracuseStep 230011 = 345017) B345017
theorem B230063 : Blo 227813 230063 := bstep (se 1 (by rfl) ⟨172547, by rfl⟩ : syracuseStep 230063 = 345095) B345095
theorem B1180345 : Blo 227813 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B230087 : Blo 227813 230087 := bstep (se 1 (by rfl) ⟨172565, by rfl⟩ : syracuseStep 230087 = 345131) B345131
theorem B230107 : Blo 227813 230107 := bstep (se 1 (by rfl) ⟨172580, by rfl⟩ : syracuseStep 230107 = 345161) B345161
theorem B230183 : Blo 227813 230183 := bstep (se 1 (by rfl) ⟨172637, by rfl⟩ : syracuseStep 230183 = 345275) B345275
theorem B230223 : Blo 227813 230223 := bstep (se 1 (by rfl) ⟨172667, by rfl⟩ : syracuseStep 230223 = 345335) B345335
theorem B230239 : Blo 227813 230239 := bstep (se 1 (by rfl) ⟨172679, by rfl⟩ : syracuseStep 230239 = 345359) B345359
theorem B230267 : Blo 227813 230267 := bstep (se 1 (by rfl) ⟨172700, by rfl⟩ : syracuseStep 230267 = 345401) B345401
theorem B230319 : Blo 227813 230319 := bstep (se 1 (by rfl) ⟨172739, by rfl⟩ : syracuseStep 230319 = 345479) B345479
theorem B230343 : Blo 227813 230343 := bstep (se 1 (by rfl) ⟨172757, by rfl⟩ : syracuseStep 230343 = 345515) B345515
theorem B230363 : Blo 227813 230363 := bstep (se 1 (by rfl) ⟨172772, by rfl⟩ : syracuseStep 230363 = 345545) B345545
theorem B230439 : Blo 227813 230439 := bstep (se 1 (by rfl) ⟨172829, by rfl⟩ : syracuseStep 230439 = 345659) B345659
theorem B24052787 : Blo 227813 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B230479 : Blo 227813 230479 := bstep (se 1 (by rfl) ⟨172859, by rfl⟩ : syracuseStep 230479 = 345719) B345719
theorem B230495 : Blo 227813 230495 := bstep (se 1 (by rfl) ⟨172871, by rfl⟩ : syracuseStep 230495 = 345743) B345743
theorem B230523 : Blo 227813 230523 := bstep (se 1 (by rfl) ⟨172892, by rfl⟩ : syracuseStep 230523 = 345785) B345785
theorem B230575 : Blo 227813 230575 := bstep (se 1 (by rfl) ⟨172931, by rfl⟩ : syracuseStep 230575 = 345863) B345863
theorem B230599 : Blo 227813 230599 := bstep (se 1 (by rfl) ⟨172949, by rfl⟩ : syracuseStep 230599 = 345899) B345899
theorem B230619 : Blo 227813 230619 := bstep (se 1 (by rfl) ⟨172964, by rfl⟩ : syracuseStep 230619 = 345929) B345929
theorem B230695 : Blo 227813 230695 := bstep (se 1 (by rfl) ⟨173021, by rfl⟩ : syracuseStep 230695 = 346043) B346043
theorem B230735 : Blo 227813 230735 := bstep (se 1 (by rfl) ⟨173051, by rfl⟩ : syracuseStep 230735 = 346103) B346103
theorem B230751 : Blo 227813 230751 := bstep (se 1 (by rfl) ⟨173063, by rfl⟩ : syracuseStep 230751 = 346127) B346127
theorem B230779 : Blo 227813 230779 := bstep (se 1 (by rfl) ⟨173084, by rfl⟩ : syracuseStep 230779 = 346169) B346169
theorem B230831 : Blo 227813 230831 := bstep (se 1 (by rfl) ⟨173123, by rfl⟩ : syracuseStep 230831 = 346247) B346247
theorem B230855 : Blo 227813 230855 := bstep (se 1 (by rfl) ⟨173141, by rfl⟩ : syracuseStep 230855 = 346283) B346283
theorem B1181147 : Blo 227813 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B230875 : Blo 227813 230875 := bstep (se 1 (by rfl) ⟨173156, by rfl⟩ : syracuseStep 230875 = 346313) B346313
theorem B624167 : Blo 227813 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B230951 : Blo 227813 230951 := bstep (se 1 (by rfl) ⟨173213, by rfl⟩ : syracuseStep 230951 = 346427) B346427
theorem B230991 : Blo 227813 230991 := bstep (se 1 (by rfl) ⟨173243, by rfl⟩ : syracuseStep 230991 = 346487) B346487
theorem B231007 : Blo 227813 231007 := bstep (se 1 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 231007 = 346511) B346511
theorem B231035 : Blo 227813 231035 := bstep (se 1 (by rfl) ⟨173276, by rfl⟩ : syracuseStep 231035 = 346553) B346553
theorem B657035 : Blo 227813 657035 := bstep (se 1 (by rfl) ⟨492776, by rfl⟩ : syracuseStep 657035 = 985553) B985553
theorem B231087 : Blo 227813 231087 := bstep (se 1 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 231087 = 346631) B346631
theorem B231111 : Blo 227813 231111 := bstep (se 1 (by rfl) ⟨173333, by rfl⟩ : syracuseStep 231111 = 346667) B346667
theorem B231131 : Blo 227813 231131 := bstep (se 1 (by rfl) ⟨173348, by rfl⟩ : syracuseStep 231131 = 346697) B346697
theorem B231207 : Blo 227813 231207 := bstep (se 1 (by rfl) ⟨173405, by rfl⟩ : syracuseStep 231207 = 346811) B346811
theorem B231247 : Blo 227813 231247 := bstep (se 1 (by rfl) ⟨173435, by rfl⟩ : syracuseStep 231247 = 346871) B346871
theorem B231263 : Blo 227813 231263 := bstep (se 1 (by rfl) ⟨173447, by rfl⟩ : syracuseStep 231263 = 346895) B346895
theorem B231291 : Blo 227813 231291 := bstep (se 1 (by rfl) ⟨173468, by rfl⟩ : syracuseStep 231291 = 346937) B346937
theorem B231343 : Blo 227813 231343 := bstep (se 1 (by rfl) ⟨173507, by rfl⟩ : syracuseStep 231343 = 347015) B347015
theorem B231367 : Blo 227813 231367 := bstep (se 1 (by rfl) ⟨173525, by rfl⟩ : syracuseStep 231367 = 347051) B347051
theorem B231387 : Blo 227813 231387 := bstep (se 1 (by rfl) ⟨173540, by rfl⟩ : syracuseStep 231387 = 347081) B347081
theorem B231463 : Blo 227813 231463 := bstep (se 1 (by rfl) ⟨173597, by rfl⟩ : syracuseStep 231463 = 347195) B347195
theorem B231503 : Blo 227813 231503 := bstep (se 1 (by rfl) ⟨173627, by rfl⟩ : syracuseStep 231503 = 347255) B347255
theorem B231519 : Blo 227813 231519 := bstep (se 1 (by rfl) ⟨173639, by rfl⟩ : syracuseStep 231519 = 347279) B347279
theorem B231547 : Blo 227813 231547 := bstep (se 1 (by rfl) ⟨173660, by rfl⟩ : syracuseStep 231547 = 347321) B347321
theorem B231599 : Blo 227813 231599 := bstep (se 1 (by rfl) ⟨173699, by rfl⟩ : syracuseStep 231599 = 347399) B347399
theorem B231623 : Blo 227813 231623 := bstep (se 1 (by rfl) ⟨173717, by rfl⟩ : syracuseStep 231623 = 347435) B347435
theorem B231643 : Blo 227813 231643 := bstep (se 1 (by rfl) ⟨173732, by rfl⟩ : syracuseStep 231643 = 347465) B347465
theorem B231719 : Blo 227813 231719 := bstep (se 1 (by rfl) ⟨173789, by rfl⟩ : syracuseStep 231719 = 347579) B347579
theorem B231759 : Blo 227813 231759 := bstep (se 1 (by rfl) ⟨173819, by rfl⟩ : syracuseStep 231759 = 347639) B347639
theorem B1313111 : Blo 227813 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B231775 : Blo 227813 231775 := bstep (se 1 (by rfl) ⟨173831, by rfl⟩ : syracuseStep 231775 = 347663) B347663
theorem B231803 : Blo 227813 231803 := bstep (se 1 (by rfl) ⟨173852, by rfl⟩ : syracuseStep 231803 = 347705) B347705
theorem B789031 : Blo 227813 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B3968635 : Blo 227813 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B462547 : Blo 227813 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B2822221 : Blo 227813 2822221 := bstep (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) B1058333
theorem B3314125 : Blo 227813 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B1577495 : Blo 227813 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B1741337 : Blo 227813 1741337 := bstep (se 2 (by rfl) ⟨653001, by rfl⟩ : syracuseStep 1741337 = 1306003) B1306003
theorem B987977 : Blo 227813 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B627643 : Blo 227813 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B1873799 : Blo 227813 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B366763 : Blo 227813 366763 := bstep (se 1 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 366763 = 550145) B550145
theorem B694793 : Blo 227813 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B1874909 : Blo 227813 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B3710231 : Blo 227813 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B1744253 : Blo 227813 1744253 := bstep (se 3 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 1744253 = 654095) B654095
theorem B826861 : Blo 227813 826861 := bstep (se 3 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 826861 = 310073) B310073
theorem B826919 : Blo 227813 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B7020269 : Blo 227813 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B434423 : Blo 227813 434423 := bstep (se 1 (by rfl) ⟨325817, by rfl⟩ : syracuseStep 434423 = 651635) B651635
theorem B1188107 : Blo 227813 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B434575 : Blo 227813 434575 := bstep (se 1 (by rfl) ⟨325931, by rfl⟩ : syracuseStep 434575 = 651863) B651863
theorem B1155869 : Blo 227813 1155869 := bstep (se 3 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 1155869 = 433451) B433451
theorem B1352477 : Blo 227813 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B2663491 : Blo 227813 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B369911 : Blo 227813 369911 := bstep (se 1 (by rfl) ⟨277433, by rfl⟩ : syracuseStep 369911 = 554867) B554867
theorem B435449 : Blo 227813 435449 := bstep (se 2 (by rfl) ⟨163293, by rfl⟩ : syracuseStep 435449 = 326587) B326587
theorem B370025 : Blo 227813 370025 := bstep (se 2 (by rfl) ⟨138759, by rfl⟩ : syracuseStep 370025 = 277519) B277519
theorem B435631 : Blo 227813 435631 := bstep (se 1 (by rfl) ⟨326723, by rfl⟩ : syracuseStep 435631 = 653447) B653447
theorem B468443 : Blo 227813 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B730721 : Blo 227813 730721 := bstep (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) B548041
theorem B468679 : Blo 227813 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B730835 : Blo 227813 730835 := bstep (se 1 (by rfl) ⟨548126, by rfl⟩ : syracuseStep 730835 = 1096253) B1096253
theorem B2500561 : Blo 227813 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B1484837 : Blo 227813 1484837 := bstep (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) B278407
theorem B698615 : Blo 227813 698615 := bstep (se 1 (by rfl) ⟨523961, by rfl⟩ : syracuseStep 698615 = 1047923) B1047923
theorem B469423 : Blo 227813 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B3648077 : Blo 227813 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B436907 : Blo 227813 436907 := bstep (se 1 (by rfl) ⟨327680, by rfl⟩ : syracuseStep 436907 = 655361) B655361
theorem B928465 : Blo 227813 928465 := bstep (se 2 (by rfl) ⟨348174, by rfl⟩ : syracuseStep 928465 = 696349) B696349
theorem B3418949 : Blo 227813 3418949 := bstep (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) B641053
theorem B1649591 : Blo 227813 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B732091 : Blo 227813 732091 := bstep (se 1 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 732091 = 1098137) B1098137
theorem B732167 : Blo 227813 732167 := bstep (se 1 (by rfl) ⟨549125, by rfl⟩ : syracuseStep 732167 = 1098251) B1098251
theorem B928921 : Blo 227813 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B830711 : Blo 227813 830711 := bstep (se 1 (by rfl) ⟨623033, by rfl⟩ : syracuseStep 830711 = 1246067) B1246067
theorem B1748627 : Blo 227813 1748627 := bstep (se 1 (by rfl) ⟨1311470, by rfl⟩ : syracuseStep 1748627 = 2622941) B2622941
theorem B4009661 : Blo 227813 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B438281 : Blo 227813 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B438311 : Blo 227813 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B3321917 : Blo 227813 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B3321971 : Blo 227813 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B438443 : Blo 227813 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B832139 : Blo 227813 832139 := bstep (se 1 (by rfl) ⟨624104, by rfl⟩ : syracuseStep 832139 = 1248209) B1248209
theorem B438995 : Blo 227813 438995 := bstep (se 1 (by rfl) ⟨329246, by rfl⟩ : syracuseStep 438995 = 658493) B658493
theorem B439033 : Blo 227813 439033 := bstep (se 2 (by rfl) ⟨164637, by rfl⟩ : syracuseStep 439033 = 329275) B329275
theorem B9679621 : Blo 227813 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B308143 : Blo 227813 308143 := bstep (se 1 (by rfl) ⟨231107, by rfl⟩ : syracuseStep 308143 = 462215) B462215
theorem B1160243 : Blo 227813 1160243 := bstep (se 1 (by rfl) ⟨870182, by rfl⟩ : syracuseStep 1160243 = 1740365) B1740365
theorem B865475 : Blo 227813 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B734525 : Blo 227813 734525 := bstep (se 3 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 734525 = 275447) B275447
theorem B439739 : Blo 227813 439739 := bstep (se 1 (by rfl) ⟨329804, by rfl⟩ : syracuseStep 439739 = 659609) B659609
theorem B865991 : Blo 227813 865991 := bstep (se 1 (by rfl) ⟨649493, by rfl⟩ : syracuseStep 865991 = 1298987) B1298987
theorem B734935 : Blo 227813 734935 := bstep (se 1 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 734935 = 1102403) B1102403
theorem B341753 : Blo 227813 341753 := bstep (se 2 (by rfl) ⟨128157, by rfl⟩ : syracuseStep 341753 = 256315) B256315
theorem B341855 : Blo 227813 341855 := bstep (se 1 (by rfl) ⟨256391, by rfl⟩ : syracuseStep 341855 = 512783) B512783
theorem B341867 : Blo 227813 341867 := bstep (se 1 (by rfl) ⟨256400, by rfl⟩ : syracuseStep 341867 = 512801) B512801
theorem B5027789 : Blo 227813 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B342095 : Blo 227813 342095 := bstep (se 1 (by rfl) ⟨256571, by rfl⟩ : syracuseStep 342095 = 513143) B513143
theorem B342215 : Blo 227813 342215 := bstep (se 1 (by rfl) ⟨256661, by rfl⟩ : syracuseStep 342215 = 513323) B513323
theorem B36616493 : Blo 227813 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B342377 : Blo 227813 342377 := bstep (se 2 (by rfl) ⟨128391, by rfl⟩ : syracuseStep 342377 = 256783) B256783
theorem B342455 : Blo 227813 342455 := bstep (se 1 (by rfl) ⟨256841, by rfl⟩ : syracuseStep 342455 = 513683) B513683
theorem B342491 : Blo 227813 342491 := bstep (se 1 (by rfl) ⟨256868, by rfl⟩ : syracuseStep 342491 = 513737) B513737
theorem B1161863 : Blo 227813 1161863 := bstep (se 1 (by rfl) ⟨871397, by rfl⟩ : syracuseStep 1161863 = 1742795) B1742795
theorem B866963 : Blo 227813 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B867145 : Blo 227813 867145 := bstep (se 2 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 867145 = 650359) B650359
theorem B342959 : Blo 227813 342959 := bstep (se 1 (by rfl) ⟨257219, by rfl⟩ : syracuseStep 342959 = 514439) B514439
theorem B310235 : Blo 227813 310235 := bstep (se 1 (by rfl) ⟨232676, by rfl⟩ : syracuseStep 310235 = 465353) B465353
theorem B1752029 : Blo 227813 1752029 := bstep (se 3 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 1752029 = 657011) B657011
theorem B343049 : Blo 227813 343049 := bstep (se 2 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 343049 = 257287) B257287
theorem B343079 : Blo 227813 343079 := bstep (se 1 (by rfl) ⟨257309, by rfl⟩ : syracuseStep 343079 = 514619) B514619
theorem B343163 : Blo 227813 343163 := bstep (se 1 (by rfl) ⟨257372, by rfl⟩ : syracuseStep 343163 = 514745) B514745
theorem B343289 : Blo 227813 343289 := bstep (se 2 (by rfl) ⟨128733, by rfl⟩ : syracuseStep 343289 = 257467) B257467
theorem B343391 : Blo 227813 343391 := bstep (se 1 (by rfl) ⟨257543, by rfl⟩ : syracuseStep 343391 = 515087) B515087
theorem B343403 : Blo 227813 343403 := bstep (se 1 (by rfl) ⟨257552, by rfl⟩ : syracuseStep 343403 = 515105) B515105
theorem B769499 : Blo 227813 769499 := bstep (se 1 (by rfl) ⟨577124, by rfl⟩ : syracuseStep 769499 = 1154249) B1154249
theorem B343631 : Blo 227813 343631 := bstep (se 1 (by rfl) ⟨257723, by rfl⟩ : syracuseStep 343631 = 515447) B515447
theorem B933515 : Blo 227813 933515 := bstep (se 1 (by rfl) ⟨700136, by rfl⟩ : syracuseStep 933515 = 1400273) B1400273
theorem B343751 : Blo 227813 343751 := bstep (se 1 (by rfl) ⟨257813, by rfl⟩ : syracuseStep 343751 = 515627) B515627
theorem B1949507 : Blo 227813 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B343913 : Blo 227813 343913 := bstep (se 2 (by rfl) ⟨128967, by rfl⟩ : syracuseStep 343913 = 257935) B257935
theorem B343991 : Blo 227813 343991 := bstep (se 1 (by rfl) ⟨257993, by rfl⟩ : syracuseStep 343991 = 515987) B515987
theorem B344027 : Blo 227813 344027 := bstep (se 1 (by rfl) ⟨258020, by rfl⟩ : syracuseStep 344027 = 516041) B516041
theorem B1163321 : Blo 227813 1163321 := bstep (se 2 (by rfl) ⟨436245, by rfl⟩ : syracuseStep 1163321 = 872491) B872491
theorem B770201 : Blo 227813 770201 := bstep (se 2 (by rfl) ⟨288825, by rfl⟩ : syracuseStep 770201 = 577651) B577651
theorem B344495 : Blo 227813 344495 := bstep (se 1 (by rfl) ⟨258371, by rfl⟩ : syracuseStep 344495 = 516743) B516743
theorem B344585 : Blo 227813 344585 := bstep (se 2 (by rfl) ⟨129219, by rfl⟩ : syracuseStep 344585 = 258439) B258439
theorem B344615 : Blo 227813 344615 := bstep (se 1 (by rfl) ⟨258461, by rfl⟩ : syracuseStep 344615 = 516923) B516923
theorem B344699 : Blo 227813 344699 := bstep (se 1 (by rfl) ⟨258524, by rfl⟩ : syracuseStep 344699 = 517049) B517049
theorem B869075 : Blo 227813 869075 := bstep (se 1 (by rfl) ⟨651806, by rfl⟩ : syracuseStep 869075 = 1303613) B1303613
theorem B344825 : Blo 227813 344825 := bstep (se 2 (by rfl) ⟨129309, by rfl⟩ : syracuseStep 344825 = 258619) B258619
theorem B344927 : Blo 227813 344927 := bstep (se 1 (by rfl) ⟨258695, by rfl⟩ : syracuseStep 344927 = 517391) B517391
theorem B344939 : Blo 227813 344939 := bstep (se 1 (by rfl) ⟨258704, by rfl⟩ : syracuseStep 344939 = 517409) B517409
theorem B410663 : Blo 227813 410663 := bstep (se 1 (by rfl) ⟨307997, by rfl⟩ : syracuseStep 410663 = 615995) B615995
theorem B345167 : Blo 227813 345167 := bstep (se 1 (by rfl) ⟨258875, by rfl⟩ : syracuseStep 345167 = 517751) B517751
theorem B3949721 : Blo 227813 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B345287 : Blo 227813 345287 := bstep (se 1 (by rfl) ⟨258965, by rfl⟩ : syracuseStep 345287 = 517931) B517931
theorem B4211957 : Blo 227813 4211957 := bstep (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) B394871
theorem B771389 : Blo 227813 771389 := bstep (se 3 (by rfl) ⟨144635, by rfl⟩ : syracuseStep 771389 = 289271) B289271
theorem B345449 : Blo 227813 345449 := bstep (se 2 (by rfl) ⟨129543, by rfl⟩ : syracuseStep 345449 = 259087) B259087
theorem B345527 : Blo 227813 345527 := bstep (se 1 (by rfl) ⟨259145, by rfl⟩ : syracuseStep 345527 = 518291) B518291
theorem B345563 : Blo 227813 345563 := bstep (se 1 (by rfl) ⟨259172, by rfl⟩ : syracuseStep 345563 = 518345) B518345
theorem B1197665 : Blo 227813 1197665 := bstep (se 2 (by rfl) ⟨449124, by rfl⟩ : syracuseStep 1197665 = 898249) B898249
theorem B411383 : Blo 227813 411383 := bstep (se 1 (by rfl) ⟨308537, by rfl⟩ : syracuseStep 411383 = 617075) B617075
theorem B346031 : Blo 227813 346031 := bstep (se 1 (by rfl) ⟨259523, by rfl⟩ : syracuseStep 346031 = 519047) B519047
theorem B346121 : Blo 227813 346121 := bstep (se 2 (by rfl) ⟨129795, by rfl⟩ : syracuseStep 346121 = 259591) B259591
theorem B739343 : Blo 227813 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B346151 : Blo 227813 346151 := bstep (se 1 (by rfl) ⟨259613, by rfl⟩ : syracuseStep 346151 = 519227) B519227
theorem B1165427 : Blo 227813 1165427 := bstep (se 1 (by rfl) ⟨874070, by rfl⟩ : syracuseStep 1165427 = 1748141) B1748141
theorem B346235 : Blo 227813 346235 := bstep (se 1 (by rfl) ⟨259676, by rfl⟩ : syracuseStep 346235 = 519353) B519353
theorem B772253 : Blo 227813 772253 := bstep (se 3 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 772253 = 289595) B289595
theorem B346361 : Blo 227813 346361 := bstep (se 2 (by rfl) ⟨129885, by rfl⟩ : syracuseStep 346361 = 259771) B259771
theorem B346463 : Blo 227813 346463 := bstep (se 1 (by rfl) ⟨259847, by rfl⟩ : syracuseStep 346463 = 519695) B519695
theorem B346475 : Blo 227813 346475 := bstep (se 1 (by rfl) ⟨259856, by rfl⟩ : syracuseStep 346475 = 519713) B519713
theorem B3295673 : Blo 227813 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B346703 : Blo 227813 346703 := bstep (se 1 (by rfl) ⟨260027, by rfl⟩ : syracuseStep 346703 = 520055) B520055
theorem B772793 : Blo 227813 772793 := bstep (se 2 (by rfl) ⟨289797, by rfl⟩ : syracuseStep 772793 = 579595) B579595
theorem B346823 : Blo 227813 346823 := bstep (se 1 (by rfl) ⟨260117, by rfl⟩ : syracuseStep 346823 = 520235) B520235
theorem B1854211 : Blo 227813 1854211 := bstep (se 1 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 1854211 = 2781317) B2781317
theorem B346985 : Blo 227813 346985 := bstep (se 2 (by rfl) ⟨130119, by rfl⟩ : syracuseStep 346985 = 260239) B260239
theorem B347063 : Blo 227813 347063 := bstep (se 1 (by rfl) ⟨260297, by rfl⟩ : syracuseStep 347063 = 520595) B520595
theorem B347099 : Blo 227813 347099 := bstep (se 1 (by rfl) ⟨260324, by rfl⟩ : syracuseStep 347099 = 520649) B520649
theorem B871505 : Blo 227813 871505 := bstep (se 2 (by rfl) ⟨326814, by rfl⟩ : syracuseStep 871505 = 653629) B653629
theorem B773387 : Blo 227813 773387 := bstep (se 1 (by rfl) ⟨580040, by rfl⟩ : syracuseStep 773387 = 1160081) B1160081
theorem B871823 : Blo 227813 871823 := bstep (se 1 (by rfl) ⟨653867, by rfl⟩ : syracuseStep 871823 = 1307735) B1307735
theorem B347567 : Blo 227813 347567 := bstep (se 1 (by rfl) ⟨260675, by rfl⟩ : syracuseStep 347567 = 521351) B521351
theorem B60182003 : Blo 227813 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B347657 : Blo 227813 347657 := bstep (se 2 (by rfl) ⟨130371, by rfl⟩ : syracuseStep 347657 = 260743) B260743
theorem B773657 : Blo 227813 773657 := bstep (se 2 (by rfl) ⟨290121, by rfl⟩ : syracuseStep 773657 = 580243) B580243
theorem B347687 : Blo 227813 347687 := bstep (se 1 (by rfl) ⟨260765, by rfl⟩ : syracuseStep 347687 = 521531) B521531
theorem B1167047 : Blo 227813 1167047 := bstep (se 1 (by rfl) ⟨875285, by rfl⟩ : syracuseStep 1167047 = 1750571) B1750571
theorem B741113 : Blo 227813 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B741383 : Blo 227813 741383 := bstep (se 1 (by rfl) ⟨556037, by rfl⟩ : syracuseStep 741383 = 1112075) B1112075
theorem B872765 : Blo 227813 872765 := bstep (se 3 (by rfl) ⟨163643, by rfl⟩ : syracuseStep 872765 = 327287) B327287
theorem B1331585 : Blo 227813 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B578087 : Blo 227813 578087 := bstep (se 1 (by rfl) ⟨433565, by rfl⟩ : syracuseStep 578087 = 867131) B867131
theorem B774791 : Blo 227813 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B3330733 : Blo 227813 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B774845 : Blo 227813 774845 := bstep (se 3 (by rfl) ⟨145283, by rfl⟩ : syracuseStep 774845 = 290567) B290567
theorem B512711 : Blo 227813 512711 := bstep (se 1 (by rfl) ⟨384533, by rfl⟩ : syracuseStep 512711 = 769067) B769067
theorem B5952211 : Blo 227813 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B775007 : Blo 227813 775007 := bstep (se 1 (by rfl) ⟨581255, by rfl⟩ : syracuseStep 775007 = 1162511) B1162511
theorem B578411 : Blo 227813 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B775169 : Blo 227813 775169 := bstep (se 2 (by rfl) ⟨290688, by rfl⟩ : syracuseStep 775169 = 581377) B581377
theorem B414727 : Blo 227813 414727 := bstep (se 1 (by rfl) ⟨311045, by rfl⟩ : syracuseStep 414727 = 622091) B622091
theorem B1463771 : Blo 227813 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B579059 : Blo 227813 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B513575 : Blo 227813 513575 := bstep (se 1 (by rfl) ⟨385181, by rfl⟩ : syracuseStep 513575 = 770363) B770363
theorem B579271 : Blo 227813 579271 := bstep (se 1 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 579271 = 868907) B868907
theorem B775979 : Blo 227813 775979 := bstep (se 1 (by rfl) ⟨581984, by rfl⟩ : syracuseStep 775979 = 1163969) B1163969
theorem B2774843 : Blo 227813 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B513899 : Blo 227813 513899 := bstep (se 1 (by rfl) ⟨385424, by rfl⟩ : syracuseStep 513899 = 770849) B770849
theorem B513953 : Blo 227813 513953 := bstep (se 2 (by rfl) ⟨192732, by rfl⟩ : syracuseStep 513953 = 385465) B385465
theorem B1300411 : Blo 227813 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B350171 : Blo 227813 350171 := bstep (se 1 (by rfl) ⟨262628, by rfl⟩ : syracuseStep 350171 = 525257) B525257
theorem B776249 : Blo 227813 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B1235101 : Blo 227813 1235101 := bstep (se 3 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 1235101 = 463163) B463163
theorem B514295 : Blo 227813 514295 := bstep (se 1 (by rfl) ⟨385721, by rfl⟩ : syracuseStep 514295 = 771443) B771443
theorem B776573 : Blo 227813 776573 := bstep (se 3 (by rfl) ⟨145607, by rfl⟩ : syracuseStep 776573 = 291215) B291215
theorem B45439541 : Blo 227813 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B580193 : Blo 227813 580193 := bstep (se 2 (by rfl) ⟨217572, by rfl⟩ : syracuseStep 580193 = 435145) B435145
theorem B776843 : Blo 227813 776843 := bstep (se 1 (by rfl) ⟨582632, by rfl⟩ : syracuseStep 776843 = 1165265) B1165265
theorem B514889 : Blo 227813 514889 := bstep (se 2 (by rfl) ⟨193083, by rfl⟩ : syracuseStep 514889 = 386167) B386167
theorem B351071 : Blo 227813 351071 := bstep (se 1 (by rfl) ⟨263303, by rfl⟩ : syracuseStep 351071 = 526607) B526607
theorem B7035761 : Blo 227813 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B1465411 : Blo 227813 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B941399 : Blo 227813 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B1301903 : Blo 227813 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B1334701 : Blo 227813 1334701 := bstep (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) B500513
theorem B384439 : Blo 227813 384439 := bstep (se 1 (by rfl) ⟨288329, by rfl⟩ : syracuseStep 384439 = 576659) B576659
theorem B777761 : Blo 227813 777761 := bstep (se 2 (by rfl) ⟨291660, by rfl⟩ : syracuseStep 777761 = 583321) B583321
theorem B515681 : Blo 227813 515681 := bstep (se 2 (by rfl) ⟨193380, by rfl⟩ : syracuseStep 515681 = 386761) B386761
theorem B384635 : Blo 227813 384635 := bstep (se 1 (by rfl) ⟨288476, by rfl⟩ : syracuseStep 384635 = 576953) B576953
theorem B876167 : Blo 227813 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B1302155 : Blo 227813 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B777977 : Blo 227813 777977 := bstep (se 2 (by rfl) ⟨291741, by rfl⟩ : syracuseStep 777977 = 583483) B583483
theorem B1105825 : Blo 227813 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B516023 : Blo 227813 516023 := bstep (se 1 (by rfl) ⟨387017, by rfl⟩ : syracuseStep 516023 = 774035) B774035
theorem B974855 : Blo 227813 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B778247 : Blo 227813 778247 := bstep (se 1 (by rfl) ⟨583685, by rfl⟩ : syracuseStep 778247 = 1167371) B1167371
theorem B385033 : Blo 227813 385033 := bstep (se 2 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 385033 = 288775) B288775
theorem B581651 : Blo 227813 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B778355 : Blo 227813 778355 := bstep (se 1 (by rfl) ⟨583766, by rfl⟩ : syracuseStep 778355 = 1167533) B1167533
theorem B385195 : Blo 227813 385195 := bstep (se 1 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 385195 = 577793) B577793
theorem B778625 : Blo 227813 778625 := bstep (se 2 (by rfl) ⟨291984, by rfl⟩ : syracuseStep 778625 = 583969) B583969
theorem B385499 : Blo 227813 385499 := bstep (se 1 (by rfl) ⟨289124, by rfl⟩ : syracuseStep 385499 = 578249) B578249
theorem B516617 : Blo 227813 516617 := bstep (se 2 (by rfl) ⟨193731, by rfl⟩ : syracuseStep 516617 = 387463) B387463
theorem B385735 : Blo 227813 385735 := bstep (se 1 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 385735 = 578603) B578603
theorem B549587 : Blo 227813 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B516959 : Blo 227813 516959 := bstep (se 1 (by rfl) ⟨387719, by rfl⟩ : syracuseStep 516959 = 775439) B775439
theorem B385897 : Blo 227813 385897 := bstep (se 2 (by rfl) ⟨144711, by rfl⟩ : syracuseStep 385897 = 289423) B289423
theorem B517139 : Blo 227813 517139 := bstep (se 1 (by rfl) ⟨387854, by rfl⟩ : syracuseStep 517139 = 775709) B775709
theorem B877625 : Blo 227813 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B779435 : Blo 227813 779435 := bstep (se 1 (by rfl) ⟨584576, by rfl⟩ : syracuseStep 779435 = 1169153) B1169153
theorem B517481 : Blo 227813 517481 := bstep (se 2 (by rfl) ⟨194055, by rfl⟩ : syracuseStep 517481 = 388111) B388111
theorem B1172879 : Blo 227813 1172879 := bstep (se 1 (by rfl) ⟨879659, by rfl⟩ : syracuseStep 1172879 = 1759319) B1759319
theorem B386491 : Blo 227813 386491 := bstep (se 1 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 386491 = 579737) B579737
theorem B1893851 : Blo 227813 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B386599 : Blo 227813 386599 := bstep (se 1 (by rfl) ⟨289949, by rfl⟩ : syracuseStep 386599 = 579899) B579899
theorem B976481 : Blo 227813 976481 := bstep (se 2 (by rfl) ⟨366180, by rfl⟩ : syracuseStep 976481 = 732361) B732361
theorem B779975 : Blo 227813 779975 := bstep (se 1 (by rfl) ⟨584981, by rfl⟩ : syracuseStep 779975 = 1169963) B1169963
theorem B1304363 : Blo 227813 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B386923 : Blo 227813 386923 := bstep (se 1 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 386923 = 580385) B580385
theorem B550817 : Blo 227813 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B518075 : Blo 227813 518075 := bstep (se 1 (by rfl) ⟨388556, by rfl⟩ : syracuseStep 518075 = 777113) B777113
theorem B518201 : Blo 227813 518201 := bstep (se 2 (by rfl) ⟨194325, by rfl⟩ : syracuseStep 518201 = 388651) B388651
theorem B11954309 : Blo 227813 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B256351 : Blo 227813 256351 := bstep (se 1 (by rfl) ⟨192263, by rfl⟩ : syracuseStep 256351 = 384527) B384527
theorem B3697001 : Blo 227813 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B518543 : Blo 227813 518543 := bstep (se 1 (by rfl) ⟨388907, by rfl⟩ : syracuseStep 518543 = 777815) B777815
theorem B879113 : Blo 227813 879113 := bstep (se 2 (by rfl) ⟨329667, by rfl⟩ : syracuseStep 879113 = 659335) B659335
theorem B780839 : Blo 227813 780839 := bstep (se 1 (by rfl) ⟨585629, by rfl⟩ : syracuseStep 780839 = 1171259) B1171259
theorem B1731131 : Blo 227813 1731131 := bstep (se 1 (by rfl) ⟨1298348, by rfl⟩ : syracuseStep 1731131 = 2596697) B2596697
theorem B780947 : Blo 227813 780947 := bstep (se 1 (by rfl) ⟨585710, by rfl⟩ : syracuseStep 780947 = 1171421) B1171421
theorem B256711 : Blo 227813 256711 := bstep (se 1 (by rfl) ⟨192533, by rfl⟩ : syracuseStep 256711 = 385067) B385067
theorem B518867 : Blo 227813 518867 := bstep (se 1 (by rfl) ⟨389150, by rfl⟩ : syracuseStep 518867 = 778301) B778301
theorem B3566405 : Blo 227813 3566405 := bstep (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) B668701
theorem B3533645 : Blo 227813 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B781163 : Blo 227813 781163 := bstep (se 1 (by rfl) ⟨585872, by rfl⟩ : syracuseStep 781163 = 1171745) B1171745
theorem B387983 : Blo 227813 387983 := bstep (se 1 (by rfl) ⟨290987, by rfl⟩ : syracuseStep 387983 = 581975) B581975
theorem B781217 : Blo 227813 781217 := bstep (se 2 (by rfl) ⟨292956, by rfl⟩ : syracuseStep 781217 = 585913) B585913
theorem B781427 : Blo 227813 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B388219 : Blo 227813 388219 := bstep (se 1 (by rfl) ⟨291164, by rfl⟩ : syracuseStep 388219 = 582329) B582329
theorem B1502401 : Blo 227813 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B585103 : Blo 227813 585103 := bstep (se 1 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 585103 = 877655) B877655
theorem B880091 : Blo 227813 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B3730931 : Blo 227813 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B781811 : Blo 227813 781811 := bstep (se 1 (by rfl) ⟨586358, by rfl⟩ : syracuseStep 781811 = 1172717) B1172717
theorem B257575 : Blo 227813 257575 := bstep (se 1 (by rfl) ⟨193181, by rfl⟩ : syracuseStep 257575 = 386363) B386363
theorem B519803 : Blo 227813 519803 := bstep (se 1 (by rfl) ⟨389852, by rfl⟩ : syracuseStep 519803 = 779705) B779705
theorem B1175239 : Blo 227813 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B585427 : Blo 227813 585427 := bstep (se 1 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 585427 = 878141) B878141
theorem B519929 : Blo 227813 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B1306529 : Blo 227813 1306529 := bstep (se 2 (by rfl) ⟨489948, by rfl⟩ : syracuseStep 1306529 = 979897) B979897
theorem B520111 : Blo 227813 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B389083 : Blo 227813 389083 := bstep (se 1 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 389083 = 583625) B583625
theorem B520199 : Blo 227813 520199 := bstep (se 1 (by rfl) ⟨390149, by rfl⟩ : syracuseStep 520199 = 780299) B780299
theorem B782351 : Blo 227813 782351 := bstep (se 1 (by rfl) ⟨586763, by rfl⟩ : syracuseStep 782351 = 1173527) B1173527
theorem B520271 : Blo 227813 520271 := bstep (se 1 (by rfl) ⟨390203, by rfl⟩ : syracuseStep 520271 = 780407) B780407
theorem B1110131 : Blo 227813 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B3141899 : Blo 227813 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B520667 : Blo 227813 520667 := bstep (se 1 (by rfl) ⟨390500, by rfl⟩ : syracuseStep 520667 = 781001) B781001
theorem B291367 : Blo 227813 291367 := bstep (se 1 (by rfl) ⟨218525, by rfl⟩ : syracuseStep 291367 = 437051) B437051
theorem B389711 : Blo 227813 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B586379 : Blo 227813 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B13202189 : Blo 227813 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B291691 : Blo 227813 291691 := bstep (se 1 (by rfl) ⟨218768, by rfl⟩ : syracuseStep 291691 = 437537) B437537
theorem B553835 : Blo 227813 553835 := bstep (se 1 (by rfl) ⟨415376, by rfl⟩ : syracuseStep 553835 = 830753) B830753
theorem B521135 : Blo 227813 521135 := bstep (se 1 (by rfl) ⟨390851, by rfl⟩ : syracuseStep 521135 = 781703) B781703
theorem B2814977 : Blo 227813 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B1045583 : Blo 227813 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B291919 : Blo 227813 291919 := bstep (se 1 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 291919 = 437879) B437879
theorem B259195 : Blo 227813 259195 := bstep (se 1 (by rfl) ⟨194396, by rfl⟩ : syracuseStep 259195 = 388793) B388793
theorem B652445 : Blo 227813 652445 := bstep (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) B244667
theorem B521387 : Blo 227813 521387 := bstep (se 1 (by rfl) ⟨391040, by rfl⟩ : syracuseStep 521387 = 782081) B782081
theorem B3536243 : Blo 227813 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B1963379 : Blo 227813 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B390575 : Blo 227813 390575 := bstep (se 1 (by rfl) ⟨292931, by rfl⟩ : syracuseStep 390575 = 585863) B585863
theorem B325129 : Blo 227813 325129 := bstep (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) B243847
theorem B259663 : Blo 227813 259663 := bstep (se 1 (by rfl) ⟨194747, by rfl⟩ : syracuseStep 259663 = 389495) B389495
theorem B391007 : Blo 227813 391007 := bstep (se 1 (by rfl) ⟨293255, by rfl⟩ : syracuseStep 391007 = 586511) B586511
theorem B980855 : Blo 227813 980855 := bstep (se 1 (by rfl) ⟨735641, by rfl⟩ : syracuseStep 980855 = 1471283) B1471283
theorem B260059 : Blo 227813 260059 := bstep (se 1 (by rfl) ⟨195044, by rfl⟩ : syracuseStep 260059 = 390089) B390089
theorem B292987 : Blo 227813 292987 := bstep (se 1 (by rfl) ⟨219740, by rfl⟩ : syracuseStep 292987 = 439481) B439481
theorem B1472741 : Blo 227813 1472741 := bstep (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) B276139
theorem B1669349 : Blo 227813 1669349 := bstep (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) B313003
theorem B293215 : Blo 227813 293215 := bstep (se 1 (by rfl) ⟨219911, by rfl⟩ : syracuseStep 293215 = 439823) B439823
theorem B260527 : Blo 227813 260527 := bstep (se 1 (by rfl) ⟨195395, by rfl⟩ : syracuseStep 260527 = 390791) B390791
theorem B1309193 : Blo 227813 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B227879 : Blo 227813 227879 := bstep (se 1 (by rfl) ⟨170909, by rfl⟩ : syracuseStep 227879 = 341819) B341819
theorem B227919 : Blo 227813 227919 := bstep (se 1 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 227919 = 341879) B341879
theorem B227935 : Blo 227813 227935 := bstep (se 1 (by rfl) ⟨170951, by rfl⟩ : syracuseStep 227935 = 341903) B341903
theorem B227963 : Blo 227813 227963 := bstep (se 1 (by rfl) ⟨170972, by rfl⟩ : syracuseStep 227963 = 341945) B341945
theorem B228015 : Blo 227813 228015 := bstep (se 1 (by rfl) ⟨171011, by rfl⟩ : syracuseStep 228015 = 342023) B342023
theorem B228039 : Blo 227813 228039 := bstep (se 1 (by rfl) ⟨171029, by rfl⟩ : syracuseStep 228039 = 342059) B342059
theorem B228059 : Blo 227813 228059 := bstep (se 1 (by rfl) ⟨171044, by rfl⟩ : syracuseStep 228059 = 342089) B342089
theorem B228135 : Blo 227813 228135 := bstep (se 1 (by rfl) ⟨171101, by rfl⟩ : syracuseStep 228135 = 342203) B342203
theorem B3308363 : Blo 227813 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B228175 : Blo 227813 228175 := bstep (se 1 (by rfl) ⟨171131, by rfl⟩ : syracuseStep 228175 = 342263) B342263
theorem B228191 : Blo 227813 228191 := bstep (se 1 (by rfl) ⟨171143, by rfl⟩ : syracuseStep 228191 = 342287) B342287
theorem B523103 : Blo 227813 523103 := bstep (se 1 (by rfl) ⟨392327, by rfl⟩ : syracuseStep 523103 = 784655) B784655
theorem B228219 : Blo 227813 228219 := bstep (se 1 (by rfl) ⟨171164, by rfl⟩ : syracuseStep 228219 = 342329) B342329
theorem B228271 : Blo 227813 228271 := bstep (se 1 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 228271 = 342407) B342407
theorem B228295 : Blo 227813 228295 := bstep (se 1 (by rfl) ⟨171221, by rfl⟩ : syracuseStep 228295 = 342443) B342443
theorem B228315 : Blo 227813 228315 := bstep (se 1 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 228315 = 342473) B342473
theorem B228391 : Blo 227813 228391 := bstep (se 1 (by rfl) ⟨171293, by rfl⟩ : syracuseStep 228391 = 342587) B342587
theorem B326695 : Blo 227813 326695 := bstep (se 1 (by rfl) ⟨245021, by rfl⟩ : syracuseStep 326695 = 490043) B490043
theorem B228431 : Blo 227813 228431 := bstep (se 1 (by rfl) ⟨171323, by rfl⟩ : syracuseStep 228431 = 342647) B342647
theorem B228447 : Blo 227813 228447 := bstep (se 1 (by rfl) ⟨171335, by rfl⟩ : syracuseStep 228447 = 342671) B342671
theorem B228475 : Blo 227813 228475 := bstep (se 1 (by rfl) ⟨171356, by rfl⟩ : syracuseStep 228475 = 342713) B342713
theorem B982169 : Blo 227813 982169 := bstep (se 2 (by rfl) ⟨368313, by rfl⟩ : syracuseStep 982169 = 736627) B736627
theorem B228527 : Blo 227813 228527 := bstep (se 1 (by rfl) ⟨171395, by rfl⟩ : syracuseStep 228527 = 342791) B342791
theorem B228551 : Blo 227813 228551 := bstep (se 1 (by rfl) ⟨171413, by rfl⟩ : syracuseStep 228551 = 342827) B342827
theorem B228571 : Blo 227813 228571 := bstep (se 1 (by rfl) ⟨171428, by rfl⟩ : syracuseStep 228571 = 342857) B342857
theorem B228647 : Blo 227813 228647 := bstep (se 1 (by rfl) ⟨171485, by rfl⟩ : syracuseStep 228647 = 342971) B342971
theorem B228687 : Blo 227813 228687 := bstep (se 1 (by rfl) ⟨171515, by rfl⟩ : syracuseStep 228687 = 343031) B343031
theorem B228703 : Blo 227813 228703 := bstep (se 1 (by rfl) ⟨171527, by rfl⟩ : syracuseStep 228703 = 343055) B343055
theorem B228731 : Blo 227813 228731 := bstep (se 1 (by rfl) ⟨171548, by rfl⟩ : syracuseStep 228731 = 343097) B343097
theorem B228783 : Blo 227813 228783 := bstep (se 1 (by rfl) ⟨171587, by rfl⟩ : syracuseStep 228783 = 343175) B343175
theorem B228807 : Blo 227813 228807 := bstep (se 1 (by rfl) ⟨171605, by rfl⟩ : syracuseStep 228807 = 343211) B343211
theorem B228827 : Blo 227813 228827 := bstep (se 1 (by rfl) ⟨171620, by rfl⟩ : syracuseStep 228827 = 343241) B343241
theorem B1310195 : Blo 227813 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B228903 : Blo 227813 228903 := bstep (se 1 (by rfl) ⟨171677, by rfl⟩ : syracuseStep 228903 = 343355) B343355
theorem B228943 : Blo 227813 228943 := bstep (se 1 (by rfl) ⟨171707, by rfl⟩ : syracuseStep 228943 = 343415) B343415
theorem B228959 : Blo 227813 228959 := bstep (se 1 (by rfl) ⟨171719, by rfl⟩ : syracuseStep 228959 = 343439) B343439
theorem B228987 : Blo 227813 228987 := bstep (se 1 (by rfl) ⟨171740, by rfl⟩ : syracuseStep 228987 = 343481) B343481
theorem B229039 : Blo 227813 229039 := bstep (se 1 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 229039 = 343559) B343559
theorem B229063 : Blo 227813 229063 := bstep (se 1 (by rfl) ⟨171797, by rfl⟩ : syracuseStep 229063 = 343595) B343595
theorem B229083 : Blo 227813 229083 := bstep (se 1 (by rfl) ⟨171812, by rfl⟩ : syracuseStep 229083 = 343625) B343625
theorem B1113821 : Blo 227813 1113821 := bstep (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) B417683
theorem B229159 : Blo 227813 229159 := bstep (se 1 (by rfl) ⟨171869, by rfl⟩ : syracuseStep 229159 = 343739) B343739
theorem B229199 : Blo 227813 229199 := bstep (se 1 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 229199 = 343799) B343799
theorem B229215 : Blo 227813 229215 := bstep (se 1 (by rfl) ⟨171911, by rfl⟩ : syracuseStep 229215 = 343823) B343823
theorem B229243 : Blo 227813 229243 := bstep (se 1 (by rfl) ⟨171932, by rfl⟩ : syracuseStep 229243 = 343865) B343865
theorem B229295 : Blo 227813 229295 := bstep (se 1 (by rfl) ⟨171971, by rfl⟩ : syracuseStep 229295 = 343943) B343943
theorem B1310651 : Blo 227813 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B229319 : Blo 227813 229319 := bstep (se 1 (by rfl) ⟨171989, by rfl⟩ : syracuseStep 229319 = 343979) B343979
theorem B229339 : Blo 227813 229339 := bstep (se 1 (by rfl) ⟨172004, by rfl⟩ : syracuseStep 229339 = 344009) B344009
theorem B15728717 : Blo 227813 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1245395 : Blo 227813 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B229663 : Blo 227813 229663 := bstep (se 1 (by rfl) ⟨172247, by rfl⟩ : syracuseStep 229663 = 344495) B344495
theorem B229723 : Blo 227813 229723 := bstep (se 1 (by rfl) ⟨172292, by rfl⟩ : syracuseStep 229723 = 344585) B344585
theorem B786779 : Blo 227813 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B229743 : Blo 227813 229743 := bstep (se 1 (by rfl) ⟨172307, by rfl⟩ : syracuseStep 229743 = 344615) B344615
theorem B229799 : Blo 227813 229799 := bstep (se 1 (by rfl) ⟨172349, by rfl⟩ : syracuseStep 229799 = 344699) B344699
theorem B229883 : Blo 227813 229883 := bstep (se 1 (by rfl) ⟨172412, by rfl⟩ : syracuseStep 229883 = 344825) B344825
theorem B229951 : Blo 227813 229951 := bstep (se 1 (by rfl) ⟨172463, by rfl⟩ : syracuseStep 229951 = 344927) B344927
theorem B229959 : Blo 227813 229959 := bstep (se 1 (by rfl) ⟨172469, by rfl⟩ : syracuseStep 229959 = 344939) B344939
theorem B230111 : Blo 227813 230111 := bstep (se 1 (by rfl) ⟨172583, by rfl⟩ : syracuseStep 230111 = 345167) B345167
theorem B230191 : Blo 227813 230191 := bstep (se 1 (by rfl) ⟨172643, by rfl⟩ : syracuseStep 230191 = 345287) B345287
theorem B230299 : Blo 227813 230299 := bstep (se 1 (by rfl) ⟨172724, by rfl⟩ : syracuseStep 230299 = 345449) B345449
theorem B1573793 : Blo 227813 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B230351 : Blo 227813 230351 := bstep (se 1 (by rfl) ⟨172763, by rfl⟩ : syracuseStep 230351 = 345527) B345527
theorem B230375 : Blo 227813 230375 := bstep (se 1 (by rfl) ⟨172781, by rfl⟩ : syracuseStep 230375 = 345563) B345563
theorem B230687 : Blo 227813 230687 := bstep (se 1 (by rfl) ⟨173015, by rfl⟩ : syracuseStep 230687 = 346031) B346031
theorem B230747 : Blo 227813 230747 := bstep (se 1 (by rfl) ⟨173060, by rfl⟩ : syracuseStep 230747 = 346121) B346121
theorem B492895 : Blo 227813 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B1312109 : Blo 227813 1312109 := bstep (se 3 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 1312109 = 492041) B492041
theorem B230767 : Blo 227813 230767 := bstep (se 1 (by rfl) ⟨173075, by rfl⟩ : syracuseStep 230767 = 346151) B346151
theorem B230823 : Blo 227813 230823 := bstep (se 1 (by rfl) ⟨173117, by rfl⟩ : syracuseStep 230823 = 346235) B346235
theorem B230907 : Blo 227813 230907 := bstep (se 1 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 230907 = 346361) B346361
theorem B230975 : Blo 227813 230975 := bstep (se 1 (by rfl) ⟨173231, by rfl⟩ : syracuseStep 230975 = 346463) B346463
theorem B230983 : Blo 227813 230983 := bstep (se 1 (by rfl) ⟨173237, by rfl⟩ : syracuseStep 230983 = 346475) B346475
theorem B2197115 : Blo 227813 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B231135 : Blo 227813 231135 := bstep (se 1 (by rfl) ⟨173351, by rfl⟩ : syracuseStep 231135 = 346703) B346703
theorem B231215 : Blo 227813 231215 := bstep (se 1 (by rfl) ⟨173411, by rfl⟩ : syracuseStep 231215 = 346823) B346823
theorem B231323 : Blo 227813 231323 := bstep (se 1 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 231323 = 346985) B346985
theorem B231375 : Blo 227813 231375 := bstep (se 1 (by rfl) ⟨173531, by rfl⟩ : syracuseStep 231375 = 347063) B347063
theorem B231399 : Blo 227813 231399 := bstep (se 1 (by rfl) ⟨173549, by rfl⟩ : syracuseStep 231399 = 347099) B347099
theorem B3606605 : Blo 227813 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B624905 : Blo 227813 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B1476893 : Blo 227813 1476893 := bstep (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) B553835
theorem B231711 : Blo 227813 231711 := bstep (se 1 (by rfl) ⟨173783, by rfl⟩ : syracuseStep 231711 = 347567) B347567
theorem B231771 : Blo 227813 231771 := bstep (se 1 (by rfl) ⟨173828, by rfl⟩ : syracuseStep 231771 = 347657) B347657
theorem B231791 : Blo 227813 231791 := bstep (se 1 (by rfl) ⟨173843, by rfl⟩ : syracuseStep 231791 = 347687) B347687
theorem B494075 : Blo 227813 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B494255 : Blo 227813 494255 := bstep (se 1 (by rfl) ⟨370691, by rfl⟩ : syracuseStep 494255 = 741383) B741383
theorem B887723 : Blo 227813 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B1051663 : Blo 227813 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B625897 : Blo 227813 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B4951813 : Blo 227813 4951813 := bstep (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) B928465
theorem B3149725 : Blo 227813 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B1249181 : Blo 227813 1249181 := bstep (se 3 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 1249181 = 468443) B468443
theorem B1249199 : Blo 227813 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B233447 : Blo 227813 233447 := bstep (se 1 (by rfl) ⟨175085, by rfl⟩ : syracuseStep 233447 = 350171) B350171
theorem B2003201 : Blo 227813 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B463195 : Blo 227813 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B234047 : Blo 227813 234047 := bstep (se 1 (by rfl) ⟨175535, by rfl⟩ : syracuseStep 234047 = 351071) B351071
theorem B4690507 : Blo 227813 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B1249939 : Blo 227813 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B627599 : Blo 227813 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B1643429 : Blo 227813 1643429 := bstep (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) B308143
theorem B13407437 : Blo 227813 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B693481 : Blo 227813 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B792071 : Blo 227813 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B366391 : Blo 227813 366391 := bstep (se 1 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 366391 = 549587) B549587
theorem B367211 : Blo 227813 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B989891 : Blo 227813 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B465743 : Blo 227813 465743 := bstep (se 1 (by rfl) ⟨349307, by rfl⟩ : syracuseStep 465743 = 698615) B698615
theorem B2464667 : Blo 227813 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B1154087 : Blo 227813 1154087 := bstep (se 1 (by rfl) ⟨865565, by rfl⟩ : syracuseStep 1154087 = 1731131) B1731131
theorem B2432051 : Blo 227813 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B433505 : Blo 227813 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B7118405 : Blo 227813 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B1646801 : Blo 227813 1646801 := bstep (se 2 (by rfl) ⟨617550, by rfl⟩ : syracuseStep 1646801 = 1235101) B1235101
theorem B1876651 : Blo 227813 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B697055 : Blo 227813 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B434963 : Blo 227813 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B1156193 : Blo 227813 1156193 := bstep (se 2 (by rfl) ⟨433572, by rfl⟩ : syracuseStep 1156193 = 867145) B867145
theorem B435593 : Blo 227813 435593 := bstep (se 2 (by rfl) ⟨163347, by rfl⟩ : syracuseStep 435593 = 326695) B326695
theorem B2205575 : Blo 227813 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B2599613 : Blo 227813 2599613 := bstep (se 3 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 2599613 = 974855) B974855
theorem B3910355 : Blo 227813 3910355 := bstep (se 1 (by rfl) ⟨2932766, by rfl⟩ : syracuseStep 3910355 = 5865533) B5865533
theorem B15051845 : Blo 227813 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B1158461 : Blo 227813 1158461 := bstep (se 3 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 1158461 = 434423) B434423
theorem B273775 : Blo 227813 273775 := bstep (se 1 (by rfl) ⟨205331, by rfl⟩ : syracuseStep 273775 = 410663) B410663
theorem B16035191 : Blo 227813 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B2633147 : Blo 227813 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B798443 : Blo 227813 798443 := bstep (se 1 (by rfl) ⟨598832, by rfl⟩ : syracuseStep 798443 = 1197665) B1197665
theorem B438023 : Blo 227813 438023 := bstep (se 1 (by rfl) ⟨328517, by rfl⟩ : syracuseStep 438023 = 657035) B657035
theorem B274255 : Blo 227813 274255 := bstep (se 1 (by rfl) ⟨205691, by rfl⟩ : syracuseStep 274255 = 411383) B411383
theorem B3551321 : Blo 227813 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B2634605 : Blo 227813 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B40121335 : Blo 227813 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B4208165 : Blo 227813 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B1160891 : Blo 227813 1160891 := bstep (se 1 (by rfl) ⟨870668, by rfl⟩ : syracuseStep 1160891 = 1741337) B1741337
theorem B341801 : Blo 227813 341801 := bstep (se 2 (by rfl) ⟨128175, by rfl⟩ : syracuseStep 341801 = 256351) B256351
theorem B341807 : Blo 227813 341807 := bstep (se 1 (by rfl) ⟨256355, by rfl⟩ : syracuseStep 341807 = 512711) B512711
theorem B342281 : Blo 227813 342281 := bstep (se 2 (by rfl) ⟨128355, by rfl⟩ : syracuseStep 342281 = 256711) B256711
theorem B2472281 : Blo 227813 2472281 := bstep (se 2 (by rfl) ⟨927105, by rfl⟩ : syracuseStep 2472281 = 1854211) B1854211
theorem B342383 : Blo 227813 342383 := bstep (se 1 (by rfl) ⟨256787, by rfl⟩ : syracuseStep 342383 = 513575) B513575
theorem B1849895 : Blo 227813 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B342599 : Blo 227813 342599 := bstep (se 1 (by rfl) ⟨256949, by rfl⟩ : syracuseStep 342599 = 513899) B513899
theorem B342635 : Blo 227813 342635 := bstep (se 1 (by rfl) ⟨256976, by rfl⟩ : syracuseStep 342635 = 513953) B513953
theorem B342863 : Blo 227813 342863 := bstep (se 1 (by rfl) ⟨257147, by rfl⟩ : syracuseStep 342863 = 514295) B514295
theorem B30293027 : Blo 227813 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B343259 : Blo 227813 343259 := bstep (se 1 (by rfl) ⟨257444, by rfl⟩ : syracuseStep 343259 = 514889) B514889
theorem B343433 : Blo 227813 343433 := bstep (se 2 (by rfl) ⟨128787, by rfl⟩ : syracuseStep 343433 = 257575) B257575
theorem B5291513 : Blo 227813 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B2473487 : Blo 227813 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B1162835 : Blo 227813 1162835 := bstep (se 1 (by rfl) ⟨872126, by rfl⟩ : syracuseStep 1162835 = 1744253) B1744253
theorem B867935 : Blo 227813 867935 := bstep (se 1 (by rfl) ⟨650951, by rfl⟩ : syracuseStep 867935 = 1301903) B1301903
theorem B343787 : Blo 227813 343787 := bstep (se 1 (by rfl) ⟨257840, by rfl⟩ : syracuseStep 343787 = 515681) B515681
theorem B868103 : Blo 227813 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B344015 : Blo 227813 344015 := bstep (se 1 (by rfl) ⟨258011, by rfl⟩ : syracuseStep 344015 = 516023) B516023
theorem B2211877 : Blo 227813 2211877 := bstep (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) B414727
theorem B344411 : Blo 227813 344411 := bstep (se 1 (by rfl) ⟨258308, by rfl⟩ : syracuseStep 344411 = 516617) B516617
theorem B770579 : Blo 227813 770579 := bstep (se 1 (by rfl) ⟨577934, by rfl⟩ : syracuseStep 770579 = 1155869) B1155869
theorem B344639 : Blo 227813 344639 := bstep (se 1 (by rfl) ⟨258479, by rfl⟩ : syracuseStep 344639 = 516959) B516959
theorem B344759 : Blo 227813 344759 := bstep (se 1 (by rfl) ⟨258569, by rfl⟩ : syracuseStep 344759 = 517139) B517139
theorem B246607 : Blo 227813 246607 := bstep (se 1 (by rfl) ⟨184955, by rfl⟩ : syracuseStep 246607 = 369911) B369911
theorem B4440977 : Blo 227813 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B344987 : Blo 227813 344987 := bstep (se 1 (by rfl) ⟨258740, by rfl⟩ : syracuseStep 344987 = 517481) B517481
theorem B246683 : Blo 227813 246683 := bstep (se 1 (by rfl) ⟨185012, by rfl⟩ : syracuseStep 246683 = 370025) B370025
theorem B1262567 : Blo 227813 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B869575 : Blo 227813 869575 := bstep (se 1 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 869575 = 1304363) B1304363
theorem B836857 : Blo 227813 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B345383 : Blo 227813 345383 := bstep (se 1 (by rfl) ⟨259037, by rfl⟩ : syracuseStep 345383 = 518075) B518075
theorem B345467 : Blo 227813 345467 := bstep (se 1 (by rfl) ⟨259100, by rfl⟩ : syracuseStep 345467 = 518201) B518201
theorem B345593 : Blo 227813 345593 := bstep (se 2 (by rfl) ⟨129597, by rfl⟩ : syracuseStep 345593 = 259195) B259195
theorem B345695 : Blo 227813 345695 := bstep (se 1 (by rfl) ⟨259271, by rfl⟩ : syracuseStep 345695 = 518543) B518543
theorem B345911 : Blo 227813 345911 := bstep (se 1 (by rfl) ⟨259433, by rfl⟩ : syracuseStep 345911 = 518867) B518867
theorem B2279299 : Blo 227813 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B2377603 : Blo 227813 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B1099727 : Blo 227813 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B346217 : Blo 227813 346217 := bstep (se 2 (by rfl) ⟨129831, by rfl⟩ : syracuseStep 346217 = 259663) B259663
theorem B9423053 : Blo 227813 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1394941 : Blo 227813 1394941 := bstep (se 3 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 1394941 = 523103) B523103
theorem B772361 : Blo 227813 772361 := bstep (se 2 (by rfl) ⟨289635, by rfl⟩ : syracuseStep 772361 = 579271) B579271
theorem B346535 : Blo 227813 346535 := bstep (se 1 (by rfl) ⟨259901, by rfl⟩ : syracuseStep 346535 = 519803) B519803
theorem B1165751 : Blo 227813 1165751 := bstep (se 1 (by rfl) ⟨874313, by rfl⟩ : syracuseStep 1165751 = 1748627) B1748627
theorem B2673107 : Blo 227813 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B346619 : Blo 227813 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B871019 : Blo 227813 871019 := bstep (se 1 (by rfl) ⟨653264, by rfl⟩ : syracuseStep 871019 = 1306529) B1306529
theorem B346745 : Blo 227813 346745 := bstep (se 2 (by rfl) ⟨130029, by rfl⟩ : syracuseStep 346745 = 260059) B260059
theorem B346799 : Blo 227813 346799 := bstep (se 1 (by rfl) ⟨260099, by rfl⟩ : syracuseStep 346799 = 520199) B520199
theorem B2214611 : Blo 227813 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B346847 : Blo 227813 346847 := bstep (se 1 (by rfl) ⟨260135, by rfl⟩ : syracuseStep 346847 = 520271) B520271
theorem B2214647 : Blo 227813 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B740087 : Blo 227813 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B347111 : Blo 227813 347111 := bstep (se 1 (by rfl) ⟨260333, by rfl⟩ : syracuseStep 347111 = 520667) B520667
theorem B8801459 : Blo 227813 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B347369 : Blo 227813 347369 := bstep (se 2 (by rfl) ⟨130263, by rfl⟩ : syracuseStep 347369 = 260527) B260527
theorem B347423 : Blo 227813 347423 := bstep (se 1 (by rfl) ⟨260567, by rfl⟩ : syracuseStep 347423 = 521135) B521135
theorem B773495 : Blo 227813 773495 := bstep (se 1 (by rfl) ⟨580121, by rfl⟩ : syracuseStep 773495 = 1160243) B1160243
theorem B347591 : Blo 227813 347591 := bstep (se 1 (by rfl) ⟨260693, by rfl⟩ : syracuseStep 347591 = 521387) B521387
theorem B576983 : Blo 227813 576983 := bstep (se 1 (by rfl) ⟨432737, by rfl⟩ : syracuseStep 576983 = 865475) B865475
theorem B577327 : Blo 227813 577327 := bstep (se 1 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 577327 = 865991) B865991
theorem B1953881 : Blo 227813 1953881 := bstep (se 2 (by rfl) ⟨732705, by rfl⟩ : syracuseStep 1953881 = 1465411) B1465411
theorem B872795 : Blo 227813 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B774575 : Blo 227813 774575 := bstep (se 1 (by rfl) ⟨580931, by rfl⟩ : syracuseStep 774575 = 1161863) B1161863
theorem B577975 : Blo 227813 577975 := bstep (se 1 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 577975 = 866963) B866963
theorem B512585 : Blo 227813 512585 := bstep (se 2 (by rfl) ⟨192219, by rfl⟩ : syracuseStep 512585 = 384439) B384439
theorem B1102481 : Blo 227813 1102481 := bstep (se 2 (by rfl) ⟨413430, by rfl⟩ : syracuseStep 1102481 = 826861) B826861
theorem B1168019 : Blo 227813 1168019 := bstep (se 1 (by rfl) ⟨876014, by rfl⟩ : syracuseStep 1168019 = 1752029) B1752029
theorem B512999 : Blo 227813 512999 := bstep (se 1 (by rfl) ⟨384749, by rfl⟩ : syracuseStep 512999 = 769499) B769499
theorem B873463 : Blo 227813 873463 := bstep (se 1 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 873463 = 1310195) B1310195
theorem B742547 : Blo 227813 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B1299671 : Blo 227813 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B873767 : Blo 227813 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B513377 : Blo 227813 513377 := bstep (se 2 (by rfl) ⟨192516, by rfl⟩ : syracuseStep 513377 = 385033) B385033
theorem B775547 : Blo 227813 775547 := bstep (se 1 (by rfl) ⟨581660, by rfl⟩ : syracuseStep 775547 = 1163321) B1163321
theorem B513467 : Blo 227813 513467 := bstep (se 1 (by rfl) ⟨385100, by rfl⟩ : syracuseStep 513467 = 770201) B770201
theorem B1168829 : Blo 227813 1168829 := bstep (se 3 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 1168829 = 438311) B438311
theorem B513593 : Blo 227813 513593 := bstep (se 2 (by rfl) ⟨192597, by rfl⟩ : syracuseStep 513593 = 385195) B385195
theorem B579383 : Blo 227813 579383 := bstep (se 1 (by rfl) ⟨434537, by rfl⟩ : syracuseStep 579383 = 869075) B869075
theorem B579433 : Blo 227813 579433 := bstep (se 2 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 579433 = 434575) B434575
theorem B514259 : Blo 227813 514259 := bstep (se 1 (by rfl) ⟨385694, by rfl⟩ : syracuseStep 514259 = 771389) B771389
theorem B514313 : Blo 227813 514313 := bstep (se 2 (by rfl) ⟨192867, by rfl⟩ : syracuseStep 514313 = 385735) B385735
theorem B416111 : Blo 227813 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B514529 : Blo 227813 514529 := bstep (se 2 (by rfl) ⟨192948, by rfl⟩ : syracuseStep 514529 = 385897) B385897
theorem B776951 : Blo 227813 776951 := bstep (se 1 (by rfl) ⟨582713, by rfl⟩ : syracuseStep 776951 = 1165427) B1165427
theorem B514835 : Blo 227813 514835 := bstep (se 1 (by rfl) ⟨386126, by rfl⟩ : syracuseStep 514835 = 772253) B772253
theorem B875407 : Blo 227813 875407 := bstep (se 1 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 875407 = 1313111) B1313111
theorem B515195 : Blo 227813 515195 := bstep (se 1 (by rfl) ⟨386396, by rfl⟩ : syracuseStep 515195 = 772793) B772793
theorem B580841 : Blo 227813 580841 := bstep (se 2 (by rfl) ⟨217815, by rfl⟩ : syracuseStep 580841 = 435631) B435631
theorem B515321 : Blo 227813 515321 := bstep (se 2 (by rfl) ⟨193245, by rfl⟩ : syracuseStep 515321 = 386491) B386491
theorem B515465 : Blo 227813 515465 := bstep (se 2 (by rfl) ⟨193299, by rfl⟩ : syracuseStep 515465 = 386599) B386599
theorem B581003 : Blo 227813 581003 := bstep (se 1 (by rfl) ⟨435752, by rfl⟩ : syracuseStep 581003 = 871505) B871505
theorem B515591 : Blo 227813 515591 := bstep (se 1 (by rfl) ⟨386693, by rfl⟩ : syracuseStep 515591 = 773387) B773387
theorem B581215 : Blo 227813 581215 := bstep (se 1 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 581215 = 871823) B871823
theorem B515771 : Blo 227813 515771 := bstep (se 1 (by rfl) ⟨386828, by rfl⟩ : syracuseStep 515771 = 773657) B773657
theorem B778031 : Blo 227813 778031 := bstep (se 1 (by rfl) ⟨583523, by rfl⟩ : syracuseStep 778031 = 1167047) B1167047
theorem B515897 : Blo 227813 515897 := bstep (se 2 (by rfl) ⟨193461, by rfl⟩ : syracuseStep 515897 = 386923) B386923
theorem B3334081 : Blo 227813 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B581843 : Blo 227813 581843 := bstep (se 1 (by rfl) ⟨436382, by rfl⟩ : syracuseStep 581843 = 872765) B872765
theorem B385391 : Blo 227813 385391 := bstep (se 1 (by rfl) ⟨289043, by rfl⟩ : syracuseStep 385391 = 578087) B578087
theorem B516527 : Blo 227813 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B516563 : Blo 227813 516563 := bstep (se 1 (by rfl) ⟨387422, by rfl⟩ : syracuseStep 516563 = 774845) B774845
theorem B516671 : Blo 227813 516671 := bstep (se 1 (by rfl) ⟨387503, by rfl⟩ : syracuseStep 516671 = 775007) B775007
theorem B385607 : Blo 227813 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B11231885 : Blo 227813 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B516779 : Blo 227813 516779 := bstep (se 1 (by rfl) ⟨387584, by rfl⟩ : syracuseStep 516779 = 775169) B775169
theorem B975847 : Blo 227813 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B386039 : Blo 227813 386039 := bstep (se 1 (by rfl) ⟨289529, by rfl⟩ : syracuseStep 386039 = 579059) B579059
theorem B31745125 : Blo 227813 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B517319 : Blo 227813 517319 := bstep (se 1 (by rfl) ⟨387989, by rfl⟩ : syracuseStep 517319 = 775979) B775979
theorem B976121 : Blo 227813 976121 := bstep (se 2 (by rfl) ⟨366045, by rfl⟩ : syracuseStep 976121 = 732091) B732091
theorem B517499 : Blo 227813 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B517625 : Blo 227813 517625 := bstep (se 2 (by rfl) ⟨194109, by rfl⟩ : syracuseStep 517625 = 388219) B388219
theorem B1238561 : Blo 227813 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B517715 : Blo 227813 517715 := bstep (se 1 (by rfl) ⟨388286, by rfl⟩ : syracuseStep 517715 = 776573) B776573
theorem B386795 : Blo 227813 386795 := bstep (se 1 (by rfl) ⟨290096, by rfl⟩ : syracuseStep 386795 = 580193) B580193
theorem B517895 : Blo 227813 517895 := bstep (se 1 (by rfl) ⟨388421, by rfl⟩ : syracuseStep 517895 = 776843) B776843
theorem B780137 : Blo 227813 780137 := bstep (se 2 (by rfl) ⟨292551, by rfl⟩ : syracuseStep 780137 = 585103) B585103
theorem B1566985 : Blo 227813 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B616729 : Blo 227813 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B780569 : Blo 227813 780569 := bstep (se 2 (by rfl) ⟨292713, by rfl⟩ : syracuseStep 780569 = 585427) B585427
theorem B518507 : Blo 227813 518507 := bstep (se 1 (by rfl) ⟨388880, by rfl⟩ : syracuseStep 518507 = 777761) B777761
theorem B551279 : Blo 227813 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B256423 : Blo 227813 256423 := bstep (se 1 (by rfl) ⟨192317, by rfl⟩ : syracuseStep 256423 = 384635) B384635
theorem B584111 : Blo 227813 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B4680179 : Blo 227813 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B518651 : Blo 227813 518651 := bstep (se 1 (by rfl) ⟨388988, by rfl⟩ : syracuseStep 518651 = 777977) B777977
theorem B518777 : Blo 227813 518777 := bstep (se 2 (by rfl) ⟨194541, by rfl⟩ : syracuseStep 518777 = 389083) B389083
theorem B518831 : Blo 227813 518831 := bstep (se 1 (by rfl) ⟨389123, by rfl⟩ : syracuseStep 518831 = 778247) B778247
theorem B387767 : Blo 227813 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B518903 : Blo 227813 518903 := bstep (se 1 (by rfl) ⟨389177, by rfl⟩ : syracuseStep 518903 = 778355) B778355
theorem B519083 : Blo 227813 519083 := bstep (se 1 (by rfl) ⟨389312, by rfl⟩ : syracuseStep 519083 = 778625) B778625
theorem B256999 : Blo 227813 256999 := bstep (se 1 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 256999 = 385499) B385499
theorem B31878157 : Blo 227813 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B4418833 : Blo 227813 4418833 := bstep (se 2 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 4418833 = 3314125) B3314125
theorem B585083 : Blo 227813 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B388489 : Blo 227813 388489 := bstep (se 2 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 388489 = 291367) B291367
theorem B519623 : Blo 227813 519623 := bstep (se 1 (by rfl) ⟨389717, by rfl⟩ : syracuseStep 519623 = 779435) B779435
theorem B97643981 : Blo 227813 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B290299 : Blo 227813 290299 := bstep (se 1 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 290299 = 435449) B435449
theorem B781919 : Blo 227813 781919 := bstep (se 1 (by rfl) ⟨586439, by rfl⟩ : syracuseStep 781919 = 1172879) B1172879
theorem B585377 : Blo 227813 585377 := bstep (se 2 (by rfl) ⟨219516, by rfl⟩ : syracuseStep 585377 = 439033) B439033
theorem B12906161 : Blo 227813 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B487147 : Blo 227813 487147 := bstep (se 1 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 487147 = 730721) B730721
theorem B650987 : Blo 227813 650987 := bstep (se 1 (by rfl) ⟨488240, by rfl⟩ : syracuseStep 650987 = 976481) B976481
theorem B519983 : Blo 227813 519983 := bstep (se 1 (by rfl) ⟨389987, by rfl⟩ : syracuseStep 519983 = 779975) B779975
theorem B487223 : Blo 227813 487223 := bstep (se 1 (by rfl) ⟨365417, by rfl⟩ : syracuseStep 487223 = 730835) B730835
theorem B388921 : Blo 227813 388921 := bstep (se 2 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 388921 = 291691) B291691
theorem B389225 : Blo 227813 389225 := bstep (se 2 (by rfl) ⟨145959, by rfl⟩ : syracuseStep 389225 = 291919) B291919
theorem B586075 : Blo 227813 586075 := bstep (se 1 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 586075 = 879113) B879113
theorem B520559 : Blo 227813 520559 := bstep (se 1 (by rfl) ⟨390419, by rfl⟩ : syracuseStep 520559 = 780839) B780839
theorem B520631 : Blo 227813 520631 := bstep (se 1 (by rfl) ⟨390473, by rfl⟩ : syracuseStep 520631 = 780947) B780947
theorem B291271 : Blo 227813 291271 := bstep (se 1 (by rfl) ⟨218453, by rfl⟩ : syracuseStep 291271 = 436907) B436907
theorem B520775 : Blo 227813 520775 := bstep (se 1 (by rfl) ⟨390581, by rfl⟩ : syracuseStep 520775 = 781163) B781163
theorem B258655 : Blo 227813 258655 := bstep (se 1 (by rfl) ⟨193991, by rfl⟩ : syracuseStep 258655 = 387983) B387983
theorem B520811 : Blo 227813 520811 := bstep (se 1 (by rfl) ⟨390608, by rfl⟩ : syracuseStep 520811 = 781217) B781217
theorem B488111 : Blo 227813 488111 := bstep (se 1 (by rfl) ⟨366083, by rfl⟩ : syracuseStep 488111 = 732167) B732167
theorem B520951 : Blo 227813 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B553807 : Blo 227813 553807 := bstep (se 1 (by rfl) ⟨415355, by rfl⟩ : syracuseStep 553807 = 830711) B830711
theorem B979913 : Blo 227813 979913 := bstep (se 2 (by rfl) ⟨367467, by rfl⟩ : syracuseStep 979913 = 734935) B734935
theorem B586727 : Blo 227813 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B2487287 : Blo 227813 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B521207 : Blo 227813 521207 := bstep (se 1 (by rfl) ⟨390905, by rfl⟩ : syracuseStep 521207 = 781811) B781811
theorem B1733881 : Blo 227813 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B292187 : Blo 227813 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B521567 : Blo 227813 521567 := bstep (se 1 (by rfl) ⟨391175, by rfl⟩ : syracuseStep 521567 = 782351) B782351
theorem B292295 : Blo 227813 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B390649 : Blo 227813 390649 := bstep (se 2 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 390649 = 292987) B292987
theorem B2094599 : Blo 227813 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B489017 : Blo 227813 489017 := bstep (se 2 (by rfl) ⟨183381, by rfl⟩ : syracuseStep 489017 = 366763) B366763
theorem B259807 : Blo 227813 259807 := bstep (se 1 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 259807 = 389711) B389711
theorem B554759 : Blo 227813 554759 := bstep (se 1 (by rfl) ⟨416069, by rfl⟩ : syracuseStep 554759 = 832139) B832139
theorem B390919 : Blo 227813 390919 := bstep (se 1 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 390919 = 586379) B586379
theorem B390953 : Blo 227813 390953 := bstep (se 2 (by rfl) ⟨146607, by rfl⟩ : syracuseStep 390953 = 293215) B293215
theorem B292663 : Blo 227813 292663 := bstep (se 1 (by rfl) ⟨219497, by rfl⟩ : syracuseStep 292663 = 438995) B438995
theorem B489683 : Blo 227813 489683 := bstep (se 1 (by rfl) ⟨367262, by rfl⟩ : syracuseStep 489683 = 734525) B734525
theorem B2357495 : Blo 227813 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B1308919 : Blo 227813 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B260383 : Blo 227813 260383 := bstep (se 1 (by rfl) ⟨195287, by rfl⟩ : syracuseStep 260383 = 390575) B390575
theorem B293159 : Blo 227813 293159 := bstep (se 1 (by rfl) ⟨219869, by rfl⟩ : syracuseStep 293159 = 439739) B439739
theorem B227835 : Blo 227813 227835 := bstep (se 1 (by rfl) ⟨170876, by rfl⟩ : syracuseStep 227835 = 341753) B341753
theorem B227903 : Blo 227813 227903 := bstep (se 1 (by rfl) ⟨170927, by rfl⟩ : syracuseStep 227903 = 341855) B341855
theorem B260671 : Blo 227813 260671 := bstep (se 1 (by rfl) ⟨195503, by rfl⟩ : syracuseStep 260671 = 391007) B391007
theorem B227911 : Blo 227813 227911 := bstep (se 1 (by rfl) ⟨170933, by rfl⟩ : syracuseStep 227911 = 341867) B341867
theorem B653903 : Blo 227813 653903 := bstep (se 1 (by rfl) ⟨490427, by rfl⟩ : syracuseStep 653903 = 980855) B980855
theorem B228063 : Blo 227813 228063 := bstep (se 1 (by rfl) ⟨171047, by rfl⟩ : syracuseStep 228063 = 342095) B342095
theorem B228143 : Blo 227813 228143 := bstep (se 1 (by rfl) ⟨171107, by rfl⟩ : syracuseStep 228143 = 342215) B342215
theorem B981827 : Blo 227813 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B1112899 : Blo 227813 1112899 := bstep (se 1 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 1112899 = 1669349) B1669349
theorem B228251 : Blo 227813 228251 := bstep (se 1 (by rfl) ⟨171188, by rfl⟩ : syracuseStep 228251 = 342377) B342377
theorem B228303 : Blo 227813 228303 := bstep (se 1 (by rfl) ⟨171227, by rfl⟩ : syracuseStep 228303 = 342455) B342455
theorem B228327 : Blo 227813 228327 := bstep (se 1 (by rfl) ⟨171245, by rfl⟩ : syracuseStep 228327 = 342491) B342491
theorem B228639 : Blo 227813 228639 := bstep (se 1 (by rfl) ⟨171479, by rfl⟩ : syracuseStep 228639 = 342959) B342959
theorem B228699 : Blo 227813 228699 := bstep (se 1 (by rfl) ⟨171524, by rfl⟩ : syracuseStep 228699 = 343049) B343049
theorem B228719 : Blo 227813 228719 := bstep (se 1 (by rfl) ⟨171539, by rfl⟩ : syracuseStep 228719 = 343079) B343079
theorem B228775 : Blo 227813 228775 := bstep (se 1 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 228775 = 343163) B343163
theorem B654779 : Blo 227813 654779 := bstep (se 1 (by rfl) ⟨491084, by rfl⟩ : syracuseStep 654779 = 982169) B982169
theorem B228859 : Blo 227813 228859 := bstep (se 1 (by rfl) ⟨171644, by rfl⟩ : syracuseStep 228859 = 343289) B343289
theorem B228927 : Blo 227813 228927 := bstep (se 1 (by rfl) ⟨171695, by rfl⟩ : syracuseStep 228927 = 343391) B343391
theorem B228935 : Blo 227813 228935 := bstep (se 1 (by rfl) ⟨171701, by rfl⟩ : syracuseStep 228935 = 343403) B343403
theorem B3309173 : Blo 227813 3309173 := bstep (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) B310235
theorem B229087 : Blo 227813 229087 := bstep (se 1 (by rfl) ⟨171815, by rfl⟩ : syracuseStep 229087 = 343631) B343631
theorem B622343 : Blo 227813 622343 := bstep (se 1 (by rfl) ⟨466757, by rfl⟩ : syracuseStep 622343 = 933515) B933515
theorem B229167 : Blo 227813 229167 := bstep (se 1 (by rfl) ⟨171875, by rfl⟩ : syracuseStep 229167 = 343751) B343751
theorem B1474433 : Blo 227813 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B229275 : Blo 227813 229275 := bstep (se 1 (by rfl) ⟨171956, by rfl⟩ : syracuseStep 229275 = 343913) B343913
theorem B229327 : Blo 227813 229327 := bstep (se 1 (by rfl) ⟨171995, by rfl⟩ : syracuseStep 229327 = 343991) B343991
theorem B229351 : Blo 227813 229351 := bstep (se 1 (by rfl) ⟨172013, by rfl⟩ : syracuseStep 229351 = 344027) B344027
theorem B2949169 : Blo 227813 2949169 := bstep (se 2 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 2949169 = 2211877) B2211877
theorem B10485811 : Blo 227813 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B229607 : Blo 227813 229607 := bstep (se 1 (by rfl) ⟨172205, by rfl⟩ : syracuseStep 229607 = 344411) B344411
theorem B524519 : Blo 227813 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B9470189 : Blo 227813 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B229759 : Blo 227813 229759 := bstep (se 1 (by rfl) ⟨172319, by rfl⟩ : syracuseStep 229759 = 344639) B344639
theorem B229839 : Blo 227813 229839 := bstep (se 1 (by rfl) ⟨172379, by rfl⟩ : syracuseStep 229839 = 344759) B344759
theorem B229991 : Blo 227813 229991 := bstep (se 1 (by rfl) ⟨172493, by rfl⟩ : syracuseStep 229991 = 344987) B344987
theorem B1049195 : Blo 227813 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B230255 : Blo 227813 230255 := bstep (se 1 (by rfl) ⟨172691, by rfl⟩ : syracuseStep 230255 = 345383) B345383
theorem B230311 : Blo 227813 230311 := bstep (se 1 (by rfl) ⟨172733, by rfl⟩ : syracuseStep 230311 = 345467) B345467
theorem B230395 : Blo 227813 230395 := bstep (se 1 (by rfl) ⟨172796, by rfl⟩ : syracuseStep 230395 = 345593) B345593
theorem B230463 : Blo 227813 230463 := bstep (se 1 (by rfl) ⟨172847, by rfl⟩ : syracuseStep 230463 = 345695) B345695
theorem B230607 : Blo 227813 230607 := bstep (se 1 (by rfl) ⟨172955, by rfl⟩ : syracuseStep 230607 = 345911) B345911
theorem B230811 : Blo 227813 230811 := bstep (se 1 (by rfl) ⟨173108, by rfl⟩ : syracuseStep 230811 = 346217) B346217
theorem B624125 : Blo 227813 624125 := bstep (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) B234047
theorem B984595 : Blo 227813 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B231023 : Blo 227813 231023 := bstep (se 1 (by rfl) ⟨173267, by rfl⟩ : syracuseStep 231023 = 346535) B346535
theorem B231079 : Blo 227813 231079 := bstep (se 1 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 231079 = 346619) B346619
theorem B329383 : Blo 227813 329383 := bstep (se 1 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 329383 = 494075) B494075
theorem B231163 : Blo 227813 231163 := bstep (se 1 (by rfl) ⟨173372, by rfl⟩ : syracuseStep 231163 = 346745) B346745
theorem B231199 : Blo 227813 231199 := bstep (se 1 (by rfl) ⟨173399, by rfl⟩ : syracuseStep 231199 = 346799) B346799
theorem B329503 : Blo 227813 329503 := bstep (se 1 (by rfl) ⟨247127, by rfl⟩ : syracuseStep 329503 = 494255) B494255
theorem B1476407 : Blo 227813 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B231231 : Blo 227813 231231 := bstep (se 1 (by rfl) ⟨173423, by rfl⟩ : syracuseStep 231231 = 346847) B346847
theorem B1476431 : Blo 227813 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B493391 : Blo 227813 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B591815 : Blo 227813 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B231407 : Blo 227813 231407 := bstep (se 1 (by rfl) ⟨173555, by rfl⟩ : syracuseStep 231407 = 347111) B347111
theorem B5867639 : Blo 227813 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B231579 : Blo 227813 231579 := bstep (se 1 (by rfl) ⟨173684, by rfl⟩ : syracuseStep 231579 = 347369) B347369
theorem B231615 : Blo 227813 231615 := bstep (se 1 (by rfl) ⟨173711, by rfl⟩ : syracuseStep 231615 = 347423) B347423
theorem B231727 : Blo 227813 231727 := bstep (se 1 (by rfl) ⟨173795, by rfl⟩ : syracuseStep 231727 = 347591) B347591
theorem B1673597 : Blo 227813 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B657821 : Blo 227813 657821 := bstep (se 3 (by rfl) ⟨123341, by rfl⟩ : syracuseStep 657821 = 246683) B246683
theorem B822305 : Blo 227813 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B528047 : Blo 227813 528047 := bstep (se 1 (by rfl) ⟨396035, by rfl⟩ : syracuseStep 528047 = 792071) B792071
theorem B42504209 : Blo 227813 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B1315237 : Blo 227813 1315237 := bstep (se 4 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 1315237 = 246607) B246607
theorem B659927 : Blo 227813 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B365033 : Blo 227813 365033 := bstep (se 2 (by rfl) ⟨136887, by rfl⟩ : syracuseStep 365033 = 273775) B273775
theorem B1643111 : Blo 227813 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B4199633 : Blo 227813 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B694601 : Blo 227813 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B825707 : Blo 227813 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B4463237 : Blo 227813 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B367519 : Blo 227813 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B924641 : Blo 227813 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B3120119 : Blo 227813 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B2628773 : Blo 227813 2628773 := bstep (se 4 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 2628773 = 492895) B492895
theorem B10690127 : Blo 227813 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B433991 : Blo 227813 433991 := bstep (se 1 (by rfl) ⟨325493, by rfl⟩ : syracuseStep 433991 = 650987) B650987
theorem B532295 : Blo 227813 532295 := bstep (se 1 (by rfl) ⟨399221, by rfl⟩ : syracuseStep 532295 = 798443) B798443
theorem B1745225 : Blo 227813 1745225 := bstep (se 2 (by rfl) ⟨654459, by rfl⟩ : syracuseStep 1745225 = 1308919) B1308919
theorem B1483865 : Blo 227813 1483865 := bstep (se 2 (by rfl) ⟨556449, by rfl⟩ : syracuseStep 1483865 = 1112899) B1112899
theorem B369839 : Blo 227813 369839 := bstep (se 1 (by rfl) ⟨277379, by rfl⟩ : syracuseStep 369839 = 554759) B554759
theorem B1648187 : Blo 227813 1648187 := bstep (se 1 (by rfl) ⟨1236140, by rfl⟩ : syracuseStep 1648187 = 2472281) B2472281
theorem B435935 : Blo 227813 435935 := bstep (se 1 (by rfl) ⟨326951, by rfl⟩ : syracuseStep 435935 = 653903) B653903
theorem B20195351 : Blo 227813 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B436519 : Blo 227813 436519 := bstep (se 1 (by rfl) ⟨327389, by rfl⟩ : syracuseStep 436519 = 654779) B654779
theorem B1648991 : Blo 227813 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B2206115 : Blo 227813 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B830263 : Blo 227813 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B2960651 : Blo 227813 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B733151 : Blo 227813 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B2404403 : Blo 227813 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B1159433 : Blo 227813 1159433 := bstep (se 2 (by rfl) ⟨434787, by rfl⟩ : syracuseStep 1159433 = 869575) B869575
theorem B1782071 : Blo 227813 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B832787 : Blo 227813 832787 := bstep (se 1 (by rfl) ⟨624590, by rfl⟩ : syracuseStep 832787 = 1249181) B1249181
theorem B832799 : Blo 227813 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B341723 : Blo 227813 341723 := bstep (se 1 (by rfl) ⟨256292, by rfl⟩ : syracuseStep 341723 = 512585) B512585
theorem B1980125 : Blo 227813 1980125 := bstep (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) B742547
theorem B734987 : Blo 227813 734987 := bstep (se 1 (by rfl) ⟨551240, by rfl⟩ : syracuseStep 734987 = 1102481) B1102481
theorem B341897 : Blo 227813 341897 := bstep (se 2 (by rfl) ⟨128211, by rfl⟩ : syracuseStep 341897 = 256423) B256423
theorem B1095619 : Blo 227813 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B341999 : Blo 227813 341999 := bstep (se 1 (by rfl) ⟨256499, by rfl⟩ : syracuseStep 341999 = 512999) B512999
theorem B866447 : Blo 227813 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B10008805 : Blo 227813 10008805 := bstep (se 4 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 10008805 = 1876651) B1876651
theorem B342251 : Blo 227813 342251 := bstep (se 1 (by rfl) ⟨256688, by rfl⟩ : syracuseStep 342251 = 513377) B513377
theorem B342311 : Blo 227813 342311 := bstep (se 1 (by rfl) ⟨256733, by rfl⟩ : syracuseStep 342311 = 513467) B513467
theorem B342395 : Blo 227813 342395 := bstep (se 1 (by rfl) ⟨256796, by rfl⟩ : syracuseStep 342395 = 513593) B513593
theorem B342665 : Blo 227813 342665 := bstep (se 2 (by rfl) ⟨128499, by rfl⟩ : syracuseStep 342665 = 256999) B256999
theorem B5585597 : Blo 227813 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B342839 : Blo 227813 342839 := bstep (se 1 (by rfl) ⟨257129, by rfl⟩ : syracuseStep 342839 = 514259) B514259
theorem B342875 : Blo 227813 342875 := bstep (se 1 (by rfl) ⟨257156, by rfl⟩ : syracuseStep 342875 = 514313) B514313
theorem B834529 : Blo 227813 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B343019 : Blo 227813 343019 := bstep (se 1 (by rfl) ⟨257264, by rfl⟩ : syracuseStep 343019 = 514529) B514529
theorem B343223 : Blo 227813 343223 := bstep (se 1 (by rfl) ⟨257417, by rfl⟩ : syracuseStep 343223 = 514835) B514835
theorem B310495 : Blo 227813 310495 := bstep (se 1 (by rfl) ⟨232871, by rfl⟩ : syracuseStep 310495 = 465743) B465743
theorem B769391 : Blo 227813 769391 := bstep (se 1 (by rfl) ⟨577043, by rfl⟩ : syracuseStep 769391 = 1154087) B1154087
theorem B1621367 : Blo 227813 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B343463 : Blo 227813 343463 := bstep (se 1 (by rfl) ⟨257597, by rfl⟩ : syracuseStep 343463 = 515195) B515195
theorem B343547 : Blo 227813 343547 := bstep (se 1 (by rfl) ⟨257660, by rfl⟩ : syracuseStep 343547 = 515321) B515321
theorem B343643 : Blo 227813 343643 := bstep (se 1 (by rfl) ⟨257732, by rfl⟩ : syracuseStep 343643 = 515465) B515465
theorem B343727 : Blo 227813 343727 := bstep (se 1 (by rfl) ⟨257795, by rfl⟩ : syracuseStep 343727 = 515591) B515591
theorem B6602417 : Blo 227813 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B769769 : Blo 227813 769769 := bstep (se 2 (by rfl) ⟨288663, by rfl⟩ : syracuseStep 769769 = 577327) B577327
theorem B343847 : Blo 227813 343847 := bstep (se 1 (by rfl) ⟨257885, by rfl⟩ : syracuseStep 343847 = 515771) B515771
theorem B343931 : Blo 227813 343931 := bstep (se 1 (by rfl) ⟨257948, by rfl⟩ : syracuseStep 343931 = 515897) B515897
theorem B1097867 : Blo 227813 1097867 := bstep (se 1 (by rfl) ⟨823400, by rfl⟩ : syracuseStep 1097867 = 1646801) B1646801
theorem B344351 : Blo 227813 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B344375 : Blo 227813 344375 := bstep (se 1 (by rfl) ⟨258281, by rfl⟩ : syracuseStep 344375 = 516563) B516563
theorem B344447 : Blo 227813 344447 := bstep (se 1 (by rfl) ⟨258335, by rfl⟩ : syracuseStep 344447 = 516671) B516671
theorem B7487923 : Blo 227813 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B344519 : Blo 227813 344519 := bstep (se 1 (by rfl) ⟨258389, by rfl⟩ : syracuseStep 344519 = 516779) B516779
theorem B770633 : Blo 227813 770633 := bstep (se 2 (by rfl) ⟨288987, by rfl⟩ : syracuseStep 770633 = 577975) B577975
theorem B770795 : Blo 227813 770795 := bstep (se 1 (by rfl) ⟨578096, by rfl⟩ : syracuseStep 770795 = 1156193) B1156193
theorem B344873 : Blo 227813 344873 := bstep (se 2 (by rfl) ⟨129327, by rfl⟩ : syracuseStep 344873 = 258655) B258655
theorem B344879 : Blo 227813 344879 := bstep (se 1 (by rfl) ⟨258659, by rfl⟩ : syracuseStep 344879 = 517319) B517319
theorem B344999 : Blo 227813 344999 := bstep (se 1 (by rfl) ⟨258749, by rfl⟩ : syracuseStep 344999 = 517499) B517499
theorem B345083 : Blo 227813 345083 := bstep (se 1 (by rfl) ⟨258812, by rfl⟩ : syracuseStep 345083 = 517625) B517625
theorem B345143 : Blo 227813 345143 := bstep (se 1 (by rfl) ⟨258857, by rfl⟩ : syracuseStep 345143 = 517715) B517715
theorem B738409 : Blo 227813 738409 := bstep (se 2 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 738409 = 553807) B553807
theorem B345263 : Blo 227813 345263 := bstep (se 1 (by rfl) ⟨258947, by rfl⟩ : syracuseStep 345263 = 517895) B517895
theorem B53495113 : Blo 227813 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B1164617 : Blo 227813 1164617 := bstep (se 2 (by rfl) ⟨436731, by rfl⟩ : syracuseStep 1164617 = 873463) B873463
theorem B345671 : Blo 227813 345671 := bstep (se 1 (by rfl) ⟨259253, by rfl⟩ : syracuseStep 345671 = 518507) B518507
theorem B2311841 : Blo 227813 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B345767 : Blo 227813 345767 := bstep (se 1 (by rfl) ⟨259325, by rfl⟩ : syracuseStep 345767 = 518651) B518651
theorem B345851 : Blo 227813 345851 := bstep (se 1 (by rfl) ⟨259388, by rfl⟩ : syracuseStep 345851 = 518777) B518777
theorem B345887 : Blo 227813 345887 := bstep (se 1 (by rfl) ⟨259415, by rfl⟩ : syracuseStep 345887 = 518831) B518831
theorem B2606903 : Blo 227813 2606903 := bstep (se 1 (by rfl) ⟨1955177, by rfl⟩ : syracuseStep 2606903 = 3910355) B3910355
theorem B345935 : Blo 227813 345935 := bstep (se 1 (by rfl) ⟨259451, by rfl⟩ : syracuseStep 345935 = 518903) B518903
theorem B346055 : Blo 227813 346055 := bstep (se 1 (by rfl) ⟨259541, by rfl⟩ : syracuseStep 346055 = 519083) B519083
theorem B772307 : Blo 227813 772307 := bstep (se 1 (by rfl) ⟨579230, by rfl⟩ : syracuseStep 772307 = 1158461) B1158461
theorem B1755431 : Blo 227813 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B346409 : Blo 227813 346409 := bstep (se 2 (by rfl) ⟨129903, by rfl⟩ : syracuseStep 346409 = 259807) B259807
theorem B346415 : Blo 227813 346415 := bstep (se 1 (by rfl) ⟨259811, by rfl⟩ : syracuseStep 346415 = 519623) B519623
theorem B65095987 : Blo 227813 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B8604107 : Blo 227813 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B772577 : Blo 227813 772577 := bstep (se 2 (by rfl) ⟨289716, by rfl⟩ : syracuseStep 772577 = 579433) B579433
theorem B346655 : Blo 227813 346655 := bstep (se 1 (by rfl) ⟨259991, by rfl⟩ : syracuseStep 346655 = 519983) B519983
theorem B347039 : Blo 227813 347039 := bstep (se 1 (by rfl) ⟨260279, by rfl⟩ : syracuseStep 347039 = 520559) B520559
theorem B347087 : Blo 227813 347087 := bstep (se 1 (by rfl) ⟨260315, by rfl⟩ : syracuseStep 347087 = 520631) B520631
theorem B347177 : Blo 227813 347177 := bstep (se 2 (by rfl) ⟨130191, by rfl⟩ : syracuseStep 347177 = 260383) B260383
theorem B347183 : Blo 227813 347183 := bstep (se 1 (by rfl) ⟨260387, by rfl⟩ : syracuseStep 347183 = 520775) B520775
theorem B347207 : Blo 227813 347207 := bstep (se 1 (by rfl) ⟨260405, by rfl⟩ : syracuseStep 347207 = 520811) B520811
theorem B1756403 : Blo 227813 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B1658191 : Blo 227813 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B347471 : Blo 227813 347471 := bstep (se 1 (by rfl) ⟨260603, by rfl⟩ : syracuseStep 347471 = 521207) B521207
theorem B347561 : Blo 227813 347561 := bstep (se 2 (by rfl) ⟨130335, by rfl⟩ : syracuseStep 347561 = 260671) B260671
theorem B347711 : Blo 227813 347711 := bstep (se 1 (by rfl) ⟨260783, by rfl⟩ : syracuseStep 347711 = 521567) B521567
theorem B1560221 : Blo 227813 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B2805443 : Blo 227813 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B773927 : Blo 227813 773927 := bstep (se 1 (by rfl) ⟨580445, by rfl⟩ : syracuseStep 773927 = 1160891) B1160891
theorem B1167209 : Blo 227813 1167209 := bstep (se 2 (by rfl) ⟨437703, by rfl⟩ : syracuseStep 1167209 = 875407) B875407
theorem B1233263 : Blo 227813 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B1462693 : Blo 227813 1462693 := bstep (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) B274255
theorem B774953 : Blo 227813 774953 := bstep (se 2 (by rfl) ⟨290607, by rfl⟩ : syracuseStep 774953 = 581215) B581215
theorem B3527675 : Blo 227813 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B775223 : Blo 227813 775223 := bstep (se 1 (by rfl) ⟨581417, by rfl⟩ : syracuseStep 775223 = 1162835) B1162835
theorem B578623 : Blo 227813 578623 := bstep (se 1 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 578623 = 867935) B867935
theorem B578735 : Blo 227813 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B414895 : Blo 227813 414895 := bstep (se 1 (by rfl) ⟨311171, by rfl⟩ : syracuseStep 414895 = 622343) B622343
theorem B4445441 : Blo 227813 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B513719 : Blo 227813 513719 := bstep (se 1 (by rfl) ⟨385289, by rfl⟩ : syracuseStep 513719 = 770579) B770579
theorem B841711 : Blo 227813 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B874739 : Blo 227813 874739 := bstep (se 1 (by rfl) ⟨656054, by rfl⟩ : syracuseStep 874739 = 1312109) B1312109
theorem B1464743 : Blo 227813 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B1301129 : Blo 227813 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B42326833 : Blo 227813 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B6282035 : Blo 227813 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B416603 : Blo 227813 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B514907 : Blo 227813 514907 := bstep (se 1 (by rfl) ⟨386180, by rfl⟩ : syracuseStep 514907 = 772361) B772361
theorem B777167 : Blo 227813 777167 := bstep (se 1 (by rfl) ⟨582875, by rfl⟩ : syracuseStep 777167 = 1165751) B1165751
theorem B580679 : Blo 227813 580679 := bstep (se 1 (by rfl) ⟨435509, by rfl⟩ : syracuseStep 580679 = 871019) B871019
theorem B1301629 : Blo 227813 1301629 := bstep (se 3 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 1301629 = 488111) B488111
theorem B515663 : Blo 227813 515663 := bstep (se 1 (by rfl) ⟨386747, by rfl⟩ : syracuseStep 515663 = 773495) B773495
theorem B384655 : Blo 227813 384655 := bstep (se 1 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 384655 = 576983) B576983
theorem B3039065 : Blo 227813 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B3170137 : Blo 227813 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B1302587 : Blo 227813 1302587 := bstep (se 1 (by rfl) ⟨976940, by rfl⟩ : syracuseStep 1302587 = 1953881) B1953881
theorem B1335467 : Blo 227813 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B581863 : Blo 227813 581863 := bstep (se 1 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 581863 = 872795) B872795
theorem B516383 : Blo 227813 516383 := bstep (se 1 (by rfl) ⟨387287, by rfl⟩ : syracuseStep 516383 = 774575) B774575
theorem B1859921 : Blo 227813 1859921 := bstep (se 2 (by rfl) ⟨697470, by rfl⟩ : syracuseStep 1859921 = 1394941) B1394941
theorem B2089313 : Blo 227813 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B778679 : Blo 227813 778679 := bstep (se 1 (by rfl) ⟨584009, by rfl⟩ : syracuseStep 778679 = 1168019) B1168019
theorem B8938291 : Blo 227813 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B582511 : Blo 227813 582511 := bstep (se 1 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 582511 = 873767) B873767
theorem B779165 : Blo 227813 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B517031 : Blo 227813 517031 := bstep (se 1 (by rfl) ⟨387773, by rfl⟩ : syracuseStep 517031 = 775547) B775547
theorem B779219 : Blo 227813 779219 := bstep (se 1 (by rfl) ⟨584414, by rfl⟩ : syracuseStep 779219 = 1168829) B1168829
theorem B779453 : Blo 227813 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B386255 : Blo 227813 386255 := bstep (se 1 (by rfl) ⟨289691, by rfl⟩ : syracuseStep 386255 = 579383) B579383
theorem B1402217 : Blo 227813 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B1304045 : Blo 227813 1304045 := bstep (se 3 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 1304045 = 489017) B489017
theorem B5891777 : Blo 227813 5891777 := bstep (se 2 (by rfl) ⟨2209416, by rfl⟩ : syracuseStep 5891777 = 4418833) B4418833
theorem B517967 : Blo 227813 517967 := bstep (se 1 (by rfl) ⟨388475, by rfl⟩ : syracuseStep 517967 = 776951) B776951
theorem B517985 : Blo 227813 517985 := bstep (se 2 (by rfl) ⟨194244, by rfl⟩ : syracuseStep 517985 = 388489) B388489
theorem B387065 : Blo 227813 387065 := bstep (se 2 (by rfl) ⟨145149, by rfl⟩ : syracuseStep 387065 = 290299) B290299
theorem B387227 : Blo 227813 387227 := bstep (se 1 (by rfl) ⟨290420, by rfl⟩ : syracuseStep 387227 = 580841) B580841
theorem B289003 : Blo 227813 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B387335 : Blo 227813 387335 := bstep (se 1 (by rfl) ⟨290501, by rfl⟩ : syracuseStep 387335 = 581003) B581003
theorem B649529 : Blo 227813 649529 := bstep (se 2 (by rfl) ⟨243573, by rfl⟩ : syracuseStep 649529 = 487147) B487147
theorem B4745603 : Blo 227813 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B518561 : Blo 227813 518561 := bstep (se 2 (by rfl) ⟨194460, by rfl⟩ : syracuseStep 518561 = 388921) B388921
theorem B518687 : Blo 227813 518687 := bstep (se 1 (by rfl) ⟨389015, by rfl⟩ : syracuseStep 518687 = 778031) B778031
theorem B387895 : Blo 227813 387895 := bstep (se 1 (by rfl) ⟨290921, by rfl⟩ : syracuseStep 387895 = 581843) B581843
theorem B256927 : Blo 227813 256927 := bstep (se 1 (by rfl) ⟨192695, by rfl⟩ : syracuseStep 256927 = 385391) B385391
theorem B257071 : Blo 227813 257071 := bstep (se 1 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 257071 = 385607) B385607
theorem B617593 : Blo 227813 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B781433 : Blo 227813 781433 := bstep (se 2 (by rfl) ⟨293037, by rfl⟩ : syracuseStep 781433 = 586075) B586075
theorem B289975 : Blo 227813 289975 := bstep (se 1 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 289975 = 434963) B434963
theorem B1305821 : Blo 227813 1305821 := bstep (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) B489683
theorem B388361 : Blo 227813 388361 := bstep (se 2 (by rfl) ⟨145635, by rfl⟩ : syracuseStep 388361 = 291271) B291271
theorem B257359 : Blo 227813 257359 := bstep (se 1 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 257359 = 386039) B386039
theorem B6254009 : Blo 227813 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B781757 : Blo 227813 781757 := bstep (se 3 (by rfl) ⟨146579, by rfl⟩ : syracuseStep 781757 = 293159) B293159
theorem B650747 : Blo 227813 650747 := bstep (se 1 (by rfl) ⟨488060, by rfl⟩ : syracuseStep 650747 = 976121) B976121
theorem B1666585 : Blo 227813 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B290395 : Blo 227813 290395 := bstep (se 1 (by rfl) ⟨217796, by rfl⟩ : syracuseStep 290395 = 435593) B435593
theorem B1109629 : Blo 227813 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B257863 : Blo 227813 257863 := bstep (se 1 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 257863 = 386795) B386795
theorem B520091 : Blo 227813 520091 := bstep (se 1 (by rfl) ⟨390068, by rfl⟩ : syracuseStep 520091 = 780137) B780137
theorem B1470383 : Blo 227813 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B520379 : Blo 227813 520379 := bstep (se 1 (by rfl) ⟨390284, by rfl⟩ : syracuseStep 520379 = 780569) B780569
theorem B979229 : Blo 227813 979229 := bstep (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) B367211
theorem B389407 : Blo 227813 389407 := bstep (se 1 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 389407 = 584111) B584111
theorem B258511 : Blo 227813 258511 := bstep (se 1 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 258511 = 387767) B387767
theorem B1733075 : Blo 227813 1733075 := bstep (se 1 (by rfl) ⟨1299806, by rfl⟩ : syracuseStep 1733075 = 2599613) B2599613
theorem B520865 : Blo 227813 520865 := bstep (se 2 (by rfl) ⟨195324, by rfl⟩ : syracuseStep 520865 = 390649) B390649
theorem B390055 : Blo 227813 390055 := bstep (se 1 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 390055 = 585083) B585083
theorem B7435253 : Blo 227813 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B521225 : Blo 227813 521225 := bstep (se 2 (by rfl) ⟨195459, by rfl⟩ : syracuseStep 521225 = 390919) B390919
theorem B521279 : Blo 227813 521279 := bstep (se 1 (by rfl) ⟨390959, by rfl⟩ : syracuseStep 521279 = 781919) B781919
theorem B488521 : Blo 227813 488521 := bstep (se 2 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 488521 = 366391) B366391
theorem B390217 : Blo 227813 390217 := bstep (se 2 (by rfl) ⟨146331, by rfl⟩ : syracuseStep 390217 = 292663) B292663
theorem B390251 : Blo 227813 390251 := bstep (se 1 (by rfl) ⟨292688, by rfl⟩ : syracuseStep 390251 = 585377) B585377
theorem B292015 : Blo 227813 292015 := bstep (se 1 (by rfl) ⟨219011, by rfl⟩ : syracuseStep 292015 = 438023) B438023
theorem B324815 : Blo 227813 324815 := bstep (se 1 (by rfl) ⟨243611, by rfl⟩ : syracuseStep 324815 = 487223) B487223
theorem B259483 : Blo 227813 259483 := bstep (se 1 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 259483 = 389225) B389225
theorem B40138253 : Blo 227813 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B653275 : Blo 227813 653275 := bstep (se 1 (by rfl) ⟨489956, by rfl⟩ : syracuseStep 653275 = 979913) B979913
theorem B391151 : Blo 227813 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B227867 : Blo 227813 227867 := bstep (se 1 (by rfl) ⟨170900, by rfl⟩ : syracuseStep 227867 = 341801) B341801
theorem B260635 : Blo 227813 260635 := bstep (se 1 (by rfl) ⟨195476, by rfl⟩ : syracuseStep 260635 = 390953) B390953
theorem B227871 : Blo 227813 227871 := bstep (se 1 (by rfl) ⟨170903, by rfl⟩ : syracuseStep 227871 = 341807) B341807
theorem B1571663 : Blo 227813 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B228187 : Blo 227813 228187 := bstep (se 1 (by rfl) ⟨171140, by rfl⟩ : syracuseStep 228187 = 342281) B342281
theorem B228255 : Blo 227813 228255 := bstep (se 1 (by rfl) ⟨171191, by rfl⟩ : syracuseStep 228255 = 342383) B342383
theorem B228399 : Blo 227813 228399 := bstep (se 1 (by rfl) ⟨171299, by rfl⟩ : syracuseStep 228399 = 342599) B342599
theorem B228423 : Blo 227813 228423 := bstep (se 1 (by rfl) ⟨171317, by rfl⟩ : syracuseStep 228423 = 342635) B342635
theorem B654551 : Blo 227813 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B228575 : Blo 227813 228575 := bstep (se 1 (by rfl) ⟨171431, by rfl⟩ : syracuseStep 228575 = 342863) B342863
theorem B228839 : Blo 227813 228839 := bstep (se 1 (by rfl) ⟨171629, by rfl⟩ : syracuseStep 228839 = 343259) B343259
theorem B228955 : Blo 227813 228955 := bstep (se 1 (by rfl) ⟨171716, by rfl⟩ : syracuseStep 228955 = 343433) B343433
theorem B229191 : Blo 227813 229191 := bstep (se 1 (by rfl) ⟨171893, by rfl⟩ : syracuseStep 229191 = 343787) B343787
theorem B982955 : Blo 227813 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B622525 : Blo 227813 622525 := bstep (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) B233447
theorem B229343 : Blo 227813 229343 := bstep (se 1 (by rfl) ⟨172007, by rfl⟩ : syracuseStep 229343 = 344015) B344015
theorem B3932225 : Blo 227813 3932225 := bstep (se 2 (by rfl) ⟨1474584, by rfl⟩ : syracuseStep 3932225 = 2949169) B2949169
theorem B229567 : Blo 227813 229567 := bstep (se 1 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 229567 = 344351) B344351
theorem B229583 : Blo 227813 229583 := bstep (se 1 (by rfl) ⟨172187, by rfl⟩ : syracuseStep 229583 = 344375) B344375
theorem B229631 : Blo 227813 229631 := bstep (se 1 (by rfl) ⟨172223, by rfl⟩ : syracuseStep 229631 = 344447) B344447
theorem B229679 : Blo 227813 229679 := bstep (se 1 (by rfl) ⟨172259, by rfl⟩ : syracuseStep 229679 = 344519) B344519
theorem B229915 : Blo 227813 229915 := bstep (se 1 (by rfl) ⟨172436, by rfl⟩ : syracuseStep 229915 = 344873) B344873
theorem B229919 : Blo 227813 229919 := bstep (se 1 (by rfl) ⟨172439, by rfl⟩ : syracuseStep 229919 = 344879) B344879
theorem B229999 : Blo 227813 229999 := bstep (se 1 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 229999 = 344999) B344999
theorem B230055 : Blo 227813 230055 := bstep (se 1 (by rfl) ⟨172541, by rfl⟩ : syracuseStep 230055 = 345083) B345083
theorem B230095 : Blo 227813 230095 := bstep (se 1 (by rfl) ⟨172571, by rfl⟩ : syracuseStep 230095 = 345143) B345143
theorem B230175 : Blo 227813 230175 := bstep (se 1 (by rfl) ⟨172631, by rfl⟩ : syracuseStep 230175 = 345263) B345263
theorem B230447 : Blo 227813 230447 := bstep (se 1 (by rfl) ⟨172835, by rfl⟩ : syracuseStep 230447 = 345671) B345671
theorem B1541227 : Blo 227813 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B230511 : Blo 227813 230511 := bstep (se 1 (by rfl) ⟨172883, by rfl⟩ : syracuseStep 230511 = 345767) B345767
theorem B230567 : Blo 227813 230567 := bstep (se 1 (by rfl) ⟨172925, by rfl⟩ : syracuseStep 230567 = 345851) B345851
theorem B230591 : Blo 227813 230591 := bstep (se 1 (by rfl) ⟨172943, by rfl⟩ : syracuseStep 230591 = 345887) B345887
theorem B1737935 : Blo 227813 1737935 := bstep (se 1 (by rfl) ⟨1303451, by rfl⟩ : syracuseStep 1737935 = 2606903) B2606903
theorem B984271 : Blo 227813 984271 := bstep (se 1 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 984271 = 1476407) B1476407
theorem B984287 : Blo 227813 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B230623 : Blo 227813 230623 := bstep (se 1 (by rfl) ⟨172967, by rfl⟩ : syracuseStep 230623 = 345935) B345935
theorem B394543 : Blo 227813 394543 := bstep (se 1 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 394543 = 591815) B591815
theorem B230703 : Blo 227813 230703 := bstep (se 1 (by rfl) ⟨173027, by rfl⟩ : syracuseStep 230703 = 346055) B346055
theorem B984545 : Blo 227813 984545 := bstep (se 2 (by rfl) ⟨369204, by rfl⟩ : syracuseStep 984545 = 738409) B738409
theorem B230939 : Blo 227813 230939 := bstep (se 1 (by rfl) ⟨173204, by rfl⟩ : syracuseStep 230939 = 346409) B346409
theorem B230943 : Blo 227813 230943 := bstep (se 1 (by rfl) ⟨173207, by rfl⟩ : syracuseStep 230943 = 346415) B346415
theorem B1115731 : Blo 227813 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B5736071 : Blo 227813 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B231103 : Blo 227813 231103 := bstep (se 1 (by rfl) ⟨173327, by rfl⟩ : syracuseStep 231103 = 346655) B346655
theorem B231359 : Blo 227813 231359 := bstep (se 1 (by rfl) ⟨173519, by rfl⟩ : syracuseStep 231359 = 347039) B347039
theorem B231391 : Blo 227813 231391 := bstep (se 1 (by rfl) ⟨173543, by rfl⟩ : syracuseStep 231391 = 347087) B347087
theorem B1312793 : Blo 227813 1312793 := bstep (se 2 (by rfl) ⟨492297, by rfl⟩ : syracuseStep 1312793 = 984595) B984595
theorem B231451 : Blo 227813 231451 := bstep (se 1 (by rfl) ⟨173588, by rfl⟩ : syracuseStep 231451 = 347177) B347177
theorem B231455 : Blo 227813 231455 := bstep (se 1 (by rfl) ⟨173591, by rfl⟩ : syracuseStep 231455 = 347183) B347183
theorem B231471 : Blo 227813 231471 := bstep (se 1 (by rfl) ⟨173603, by rfl⟩ : syracuseStep 231471 = 347207) B347207
theorem B231647 : Blo 227813 231647 := bstep (se 1 (by rfl) ⟨173735, by rfl⟩ : syracuseStep 231647 = 347471) B347471
theorem B231707 : Blo 227813 231707 := bstep (se 1 (by rfl) ⟨173780, by rfl⟩ : syracuseStep 231707 = 347561) B347561
theorem B231807 : Blo 227813 231807 := bstep (se 1 (by rfl) ⟨173855, by rfl⟩ : syracuseStep 231807 = 347711) B347711
theorem B1870295 : Blo 227813 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B823457 : Blo 227813 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B463067 : Blo 227813 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B1315709 : Blo 227813 1315709 := bstep (se 3 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 1315709 = 493391) B493391
theorem B890311 : Blo 227813 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B989243 : Blo 227813 989243 := bstep (se 1 (by rfl) ⟨741932, by rfl⟩ : syracuseStep 989243 = 1483865) B1483865
theorem B3905981 : Blo 227813 3905981 := bstep (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) B1464743
theorem B433019 : Blo 227813 433019 := bstep (se 1 (by rfl) ⟨324764, by rfl⟩ : syracuseStep 433019 = 649529) B649529
theorem B1973767 : Blo 227813 1973767 := bstep (se 1 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 1973767 = 2960651) B2960651
theorem B4169339 : Blo 227813 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B433831 : Blo 227813 433831 := bstep (se 1 (by rfl) ⟨325373, by rfl⟩ : syracuseStep 433831 = 650747) B650747
theorem B1122281 : Blo 227813 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B1188047 : Blo 227813 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B13345073 : Blo 227813 13345073 := bstep (se 2 (by rfl) ⟨5004402, by rfl⟩ : syracuseStep 13345073 = 10008805) B10008805
theorem B1155383 : Blo 227813 1155383 := bstep (se 1 (by rfl) ⟨866537, by rfl⟩ : syracuseStep 1155383 = 1733075) B1733075
theorem B4956835 : Blo 227813 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B56435777 : Blo 227813 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B1320083 : Blo 227813 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B436367 : Blo 227813 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B4401611 : Blo 227813 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B830033 : Blo 227813 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B731911 : Blo 227813 731911 := bstep (se 1 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 731911 = 1097867) B1097867
theorem B699463 : Blo 227813 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B3288701 : Blo 227813 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B3911759 : Blo 227813 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B438547 : Blo 227813 438547 := bstep (se 1 (by rfl) ⟨328910, by rfl⟩ : syracuseStep 438547 = 657821) B657821
theorem B439177 : Blo 227813 439177 := bstep (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) B329383
theorem B439337 : Blo 227813 439337 := bstep (se 2 (by rfl) ⟨164751, by rfl⟩ : syracuseStep 439337 = 329503) B329503
theorem B1095407 : Blo 227813 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B866173 : Blo 227813 866173 := bstep (se 3 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 866173 = 324815) B324815
theorem B2799755 : Blo 227813 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B2963627 : Blo 227813 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B342479 : Blo 227813 342479 := bstep (se 1 (by rfl) ⟨256859, by rfl⟩ : syracuseStep 342479 = 513719) B513719
theorem B342569 : Blo 227813 342569 := bstep (se 2 (by rfl) ⟨128463, by rfl⟩ : syracuseStep 342569 = 256927) B256927
theorem B342761 : Blo 227813 342761 := bstep (se 2 (by rfl) ⟨128535, by rfl⟩ : syracuseStep 342761 = 257071) B257071
theorem B867419 : Blo 227813 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B343145 : Blo 227813 343145 := bstep (se 2 (by rfl) ⟨128679, by rfl⟩ : syracuseStep 343145 = 257359) B257359
theorem B2210921 : Blo 227813 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B343271 : Blo 227813 343271 := bstep (se 1 (by rfl) ⟨257453, by rfl⟩ : syracuseStep 343271 = 514907) B514907
theorem B2080079 : Blo 227813 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B1752515 : Blo 227813 1752515 := bstep (se 1 (by rfl) ⟨1314386, by rfl⟩ : syracuseStep 1752515 = 2628773) B2628773
theorem B7126751 : Blo 227813 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B343775 : Blo 227813 343775 := bstep (se 1 (by rfl) ⟨257831, by rfl⟩ : syracuseStep 343775 = 515663) B515663
theorem B343817 : Blo 227813 343817 := bstep (se 2 (by rfl) ⟨128931, by rfl⟩ : syracuseStep 343817 = 257863) B257863
theorem B868391 : Blo 227813 868391 := bstep (se 1 (by rfl) ⟨651293, by rfl⟩ : syracuseStep 868391 = 1302587) B1302587
theorem B344255 : Blo 227813 344255 := bstep (se 1 (by rfl) ⟨258191, by rfl⟩ : syracuseStep 344255 = 516383) B516383
theorem B1163483 : Blo 227813 1163483 := bstep (se 1 (by rfl) ⟨872612, by rfl⟩ : syracuseStep 1163483 = 1745225) B1745225
theorem B1392875 : Blo 227813 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B2605445 : Blo 227813 2605445 := bstep (se 4 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 2605445 = 488521) B488521
theorem B1753649 : Blo 227813 1753649 := bstep (se 2 (by rfl) ⟨657618, by rfl⟩ : syracuseStep 1753649 = 1315237) B1315237
theorem B1950257 : Blo 227813 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B344681 : Blo 227813 344681 := bstep (se 2 (by rfl) ⟨129255, by rfl⟩ : syracuseStep 344681 = 258511) B258511
theorem B344687 : Blo 227813 344687 := bstep (se 1 (by rfl) ⟨258515, by rfl⟩ : syracuseStep 344687 = 517031) B517031
theorem B246559 : Blo 227813 246559 := bstep (se 1 (by rfl) ⟨184919, by rfl⟩ : syracuseStep 246559 = 369839) B369839
theorem B934811 : Blo 227813 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B869363 : Blo 227813 869363 := bstep (se 1 (by rfl) ⟨652022, by rfl⟩ : syracuseStep 869363 = 1304045) B1304045
theorem B1098791 : Blo 227813 1098791 := bstep (se 1 (by rfl) ⟨824093, by rfl⟩ : syracuseStep 1098791 = 1648187) B1648187
theorem B345311 : Blo 227813 345311 := bstep (se 1 (by rfl) ⟨258983, by rfl⟩ : syracuseStep 345311 = 517967) B517967
theorem B345323 : Blo 227813 345323 := bstep (se 1 (by rfl) ⟨258992, by rfl⟩ : syracuseStep 345323 = 517985) B517985
theorem B771497 : Blo 227813 771497 := bstep (se 2 (by rfl) ⟨289311, by rfl⟩ : syracuseStep 771497 = 578623) B578623
theorem B1099327 : Blo 227813 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B3163735 : Blo 227813 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B345707 : Blo 227813 345707 := bstep (se 1 (by rfl) ⟨259280, by rfl⟩ : syracuseStep 345707 = 518561) B518561
theorem B345791 : Blo 227813 345791 := bstep (se 1 (by rfl) ⟨259343, by rfl⟩ : syracuseStep 345791 = 518687) B518687
theorem B345977 : Blo 227813 345977 := bstep (se 2 (by rfl) ⟨129741, by rfl⟩ : syracuseStep 345977 = 259483) B259483
theorem B870547 : Blo 227813 870547 := bstep (se 1 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 870547 = 1305821) B1305821
theorem B1460825 : Blo 227813 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B346727 : Blo 227813 346727 := bstep (se 1 (by rfl) ⟨260045, by rfl⟩ : syracuseStep 346727 = 520091) B520091
theorem B871033 : Blo 227813 871033 := bstep (se 2 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 871033 = 653275) B653275
theorem B346919 : Blo 227813 346919 := bstep (se 1 (by rfl) ⟨260189, by rfl⟩ : syracuseStep 346919 = 520379) B520379
theorem B772955 : Blo 227813 772955 := bstep (se 1 (by rfl) ⟨579716, by rfl⟩ : syracuseStep 772955 = 1159433) B1159433
theorem B347243 : Blo 227813 347243 := bstep (se 1 (by rfl) ⟨260432, by rfl⟩ : syracuseStep 347243 = 520865) B520865
theorem B5918021 : Blo 227813 5918021 := bstep (se 4 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 5918021 = 1109629) B1109629
theorem B347483 : Blo 227813 347483 := bstep (se 1 (by rfl) ⟨260612, by rfl⟩ : syracuseStep 347483 = 521225) B521225
theorem B347513 : Blo 227813 347513 := bstep (se 2 (by rfl) ⟨130317, by rfl⟩ : syracuseStep 347513 = 260635) B260635
theorem B347519 : Blo 227813 347519 := bstep (se 1 (by rfl) ⟨260639, by rfl⟩ : syracuseStep 347519 = 521279) B521279
theorem B26758835 : Blo 227813 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B577631 : Blo 227813 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B413993 : Blo 227813 413993 := bstep (se 2 (by rfl) ⟨155247, by rfl⟩ : syracuseStep 413993 = 310495) B310495
theorem B3723731 : Blo 227813 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B512873 : Blo 227813 512873 := bstep (se 2 (by rfl) ⟨192327, by rfl⟩ : syracuseStep 512873 = 384655) B384655
theorem B512927 : Blo 227813 512927 := bstep (se 1 (by rfl) ⟨384695, by rfl⟩ : syracuseStep 512927 = 769391) B769391
theorem B513179 : Blo 227813 513179 := bstep (se 1 (by rfl) ⟨384884, by rfl⟩ : syracuseStep 513179 = 769769) B769769
theorem B13981081 : Blo 227813 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B349679 : Blo 227813 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B6313459 : Blo 227813 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B775817 : Blo 227813 775817 := bstep (se 2 (by rfl) ⟨290931, by rfl⟩ : syracuseStep 775817 = 581863) B581863
theorem B513755 : Blo 227813 513755 := bstep (se 1 (by rfl) ⟨385316, by rfl⟩ : syracuseStep 513755 = 770633) B770633
theorem B513863 : Blo 227813 513863 := bstep (se 1 (by rfl) ⟨385397, by rfl⟩ : syracuseStep 513863 = 770795) B770795
theorem B9983897 : Blo 227813 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B2611277 : Blo 227813 2611277 := bstep (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) B979229
theorem B776411 : Blo 227813 776411 := bstep (se 1 (by rfl) ⟨582308, by rfl⟩ : syracuseStep 776411 = 1164617) B1164617
theorem B416083 : Blo 227813 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B11917721 : Blo 227813 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B776681 : Blo 227813 776681 := bstep (se 2 (by rfl) ⟨291255, by rfl⟩ : syracuseStep 776681 = 582511) B582511
theorem B1759805 : Blo 227813 1759805 := bstep (se 3 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 1759805 = 659927) B659927
theorem B973421 : Blo 227813 973421 := bstep (se 3 (by rfl) ⟨182516, by rfl⟩ : syracuseStep 973421 = 365033) B365033
theorem B514871 : Blo 227813 514871 := bstep (se 1 (by rfl) ⟨386153, by rfl⟩ : syracuseStep 514871 = 772307) B772307
theorem B1170287 : Blo 227813 1170287 := bstep (se 1 (by rfl) ⟨877715, by rfl⟩ : syracuseStep 1170287 = 1755431) B1755431
theorem B515051 : Blo 227813 515051 := bstep (se 1 (by rfl) ⟨386288, by rfl⟩ : syracuseStep 515051 = 772577) B772577
theorem B71326817 : Blo 227813 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B548203 : Blo 227813 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B1170935 : Blo 227813 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B1040147 : Blo 227813 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B352031 : Blo 227813 352031 := bstep (se 1 (by rfl) ⟨264023, by rfl⟩ : syracuseStep 352031 = 528047) B528047
theorem B515951 : Blo 227813 515951 := bstep (se 1 (by rfl) ⟨386963, by rfl⟩ : syracuseStep 515951 = 773927) B773927
theorem B778139 : Blo 227813 778139 := bstep (se 1 (by rfl) ⟨583604, by rfl⟩ : syracuseStep 778139 = 1167209) B1167209
theorem B28336139 : Blo 227813 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B385337 : Blo 227813 385337 := bstep (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) B289003
theorem B582025 : Blo 227813 582025 := bstep (se 2 (by rfl) ⟨218259, by rfl⟩ : syracuseStep 582025 = 436519) B436519
theorem B86794649 : Blo 227813 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B516635 : Blo 227813 516635 := bstep (se 1 (by rfl) ⟨387476, by rfl⟩ : syracuseStep 516635 = 774953) B774953
theorem B2351783 : Blo 227813 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B516815 : Blo 227813 516815 := bstep (se 1 (by rfl) ⟨387611, by rfl⟩ : syracuseStep 516815 = 775223) B775223
theorem B2220797 : Blo 227813 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B385823 : Blo 227813 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B517193 : Blo 227813 517193 := bstep (se 2 (by rfl) ⟨193947, by rfl⟩ : syracuseStep 517193 = 387895) B387895
theorem B1107017 : Blo 227813 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B583159 : Blo 227813 583159 := bstep (se 1 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 583159 = 874739) B874739
theorem B550471 : Blo 227813 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B386633 : Blo 227813 386633 := bstep (se 2 (by rfl) ⟨144987, by rfl⟩ : syracuseStep 386633 = 289975) B289975
theorem B2975491 : Blo 227813 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B4188023 : Blo 227813 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B518111 : Blo 227813 518111 := bstep (se 1 (by rfl) ⟨388583, by rfl⟩ : syracuseStep 518111 = 777167) B777167
theorem B616427 : Blo 227813 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B2222113 : Blo 227813 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B387119 : Blo 227813 387119 := bstep (se 1 (by rfl) ⟨290339, by rfl⟩ : syracuseStep 387119 = 580679) B580679
theorem B387193 : Blo 227813 387193 := bstep (se 2 (by rfl) ⟨145197, by rfl⟩ : syracuseStep 387193 = 290395) B290395
theorem B289327 : Blo 227813 289327 := bstep (se 1 (by rfl) ⟨216995, by rfl⟩ : syracuseStep 289327 = 433991) B433991
theorem B354863 : Blo 227813 354863 := bstep (se 1 (by rfl) ⟨266147, by rfl⟩ : syracuseStep 354863 = 532295) B532295
theorem B2026043 : Blo 227813 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B1239947 : Blo 227813 1239947 := bstep (se 1 (by rfl) ⟨929960, by rfl⟩ : syracuseStep 1239947 = 1859921) B1859921
theorem B519119 : Blo 227813 519119 := bstep (se 1 (by rfl) ⟨389339, by rfl⟩ : syracuseStep 519119 = 778679) B778679
theorem B519209 : Blo 227813 519209 := bstep (se 2 (by rfl) ⟨194703, by rfl⟩ : syracuseStep 519209 = 389407) B389407
theorem B519443 : Blo 227813 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B519479 : Blo 227813 519479 := bstep (se 1 (by rfl) ⟨389609, by rfl⟩ : syracuseStep 519479 = 779219) B779219
theorem B519635 : Blo 227813 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B257503 : Blo 227813 257503 := bstep (se 1 (by rfl) ⟨193127, by rfl⟩ : syracuseStep 257503 = 386255) B386255
theorem B3927851 : Blo 227813 3927851 := bstep (se 1 (by rfl) ⟨2945888, by rfl⟩ : syracuseStep 3927851 = 5891777) B5891777
theorem B290623 : Blo 227813 290623 := bstep (se 1 (by rfl) ⟨217967, by rfl⟩ : syracuseStep 290623 = 435935) B435935
theorem B520073 : Blo 227813 520073 := bstep (se 2 (by rfl) ⟨195027, by rfl⟩ : syracuseStep 520073 = 390055) B390055
theorem B258043 : Blo 227813 258043 := bstep (se 1 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 258043 = 387065) B387065
theorem B13463567 : Blo 227813 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B520289 : Blo 227813 520289 := bstep (se 2 (by rfl) ⟨195108, by rfl⟩ : syracuseStep 520289 = 390217) B390217
theorem B258151 : Blo 227813 258151 := bstep (se 1 (by rfl) ⟨193613, by rfl⟩ : syracuseStep 258151 = 387227) B387227
theorem B258223 : Blo 227813 258223 := bstep (se 1 (by rfl) ⟨193667, by rfl⟩ : syracuseStep 258223 = 387335) B387335
theorem B553193 : Blo 227813 553193 := bstep (se 2 (by rfl) ⟨207447, by rfl⟩ : syracuseStep 553193 = 414895) B414895
theorem B389353 : Blo 227813 389353 := bstep (se 2 (by rfl) ⟨146007, by rfl⟩ : syracuseStep 389353 = 292015) B292015
theorem B1470743 : Blo 227813 1470743 := bstep (se 1 (by rfl) ⟨1103057, by rfl⟩ : syracuseStep 1470743 = 2206115) B2206115
theorem B520955 : Blo 227813 520955 := bstep (se 1 (by rfl) ⟨390716, by rfl⟩ : syracuseStep 520955 = 781433) B781433
theorem B258907 : Blo 227813 258907 := bstep (se 1 (by rfl) ⟨194180, by rfl⟩ : syracuseStep 258907 = 388361) B388361
theorem B1110941 : Blo 227813 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B521171 : Blo 227813 521171 := bstep (se 1 (by rfl) ⟨390878, by rfl⟩ : syracuseStep 521171 = 781757) B781757
theorem B980255 : Blo 227813 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B488767 : Blo 227813 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B1602935 : Blo 227813 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B260167 : Blo 227813 260167 := bstep (se 1 (by rfl) ⟨195125, by rfl⟩ : syracuseStep 260167 = 390251) B390251
theorem B555191 : Blo 227813 555191 := bstep (se 1 (by rfl) ⟨416393, by rfl⟩ : syracuseStep 555191 = 832787) B832787
theorem B227815 : Blo 227813 227815 := bstep (se 1 (by rfl) ⟨170861, by rfl⟩ : syracuseStep 227815 = 341723) B341723
theorem B489991 : Blo 227813 489991 := bstep (se 1 (by rfl) ⟨367493, by rfl⟩ : syracuseStep 489991 = 734987) B734987
theorem B490025 : Blo 227813 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B227931 : Blo 227813 227931 := bstep (se 1 (by rfl) ⟨170948, by rfl⟩ : syracuseStep 227931 = 341897) B341897
theorem B1112705 : Blo 227813 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B227999 : Blo 227813 227999 := bstep (se 1 (by rfl) ⟨170999, by rfl⟩ : syracuseStep 227999 = 341999) B341999
theorem B260767 : Blo 227813 260767 := bstep (se 1 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 260767 = 391151) B391151
theorem B228167 : Blo 227813 228167 := bstep (se 1 (by rfl) ⟨171125, by rfl⟩ : syracuseStep 228167 = 342251) B342251
theorem B1735505 : Blo 227813 1735505 := bstep (se 2 (by rfl) ⟨650814, by rfl⟩ : syracuseStep 1735505 = 1301629) B1301629
theorem B228207 : Blo 227813 228207 := bstep (se 1 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 228207 = 342311) B342311
theorem B228263 : Blo 227813 228263 := bstep (se 1 (by rfl) ⟨171197, by rfl⟩ : syracuseStep 228263 = 342395) B342395
theorem B228443 : Blo 227813 228443 := bstep (se 1 (by rfl) ⟨171332, by rfl⟩ : syracuseStep 228443 = 342665) B342665
theorem B228559 : Blo 227813 228559 := bstep (se 1 (by rfl) ⟨171419, by rfl⟩ : syracuseStep 228559 = 342839) B342839
theorem B1047775 : Blo 227813 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B228583 : Blo 227813 228583 := bstep (se 1 (by rfl) ⟨171437, by rfl⟩ : syracuseStep 228583 = 342875) B342875
theorem B228679 : Blo 227813 228679 := bstep (se 1 (by rfl) ⟨171509, by rfl⟩ : syracuseStep 228679 = 343019) B343019
theorem B228815 : Blo 227813 228815 := bstep (se 1 (by rfl) ⟨171611, by rfl⟩ : syracuseStep 228815 = 343223) B343223
theorem B1080911 : Blo 227813 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B228975 : Blo 227813 228975 := bstep (se 1 (by rfl) ⟨171731, by rfl⟩ : syracuseStep 228975 = 343463) B343463
theorem B229031 : Blo 227813 229031 := bstep (se 1 (by rfl) ⟨171773, by rfl⟩ : syracuseStep 229031 = 343547) B343547
theorem B229095 : Blo 227813 229095 := bstep (se 1 (by rfl) ⟨171821, by rfl⟩ : syracuseStep 229095 = 343643) B343643
theorem B229151 : Blo 227813 229151 := bstep (se 1 (by rfl) ⟨171863, by rfl⟩ : syracuseStep 229151 = 343727) B343727
theorem B4226849 : Blo 227813 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B229231 : Blo 227813 229231 := bstep (se 1 (by rfl) ⟨171923, by rfl⟩ : syracuseStep 229231 = 343847) B343847
theorem B229287 : Blo 227813 229287 := bstep (se 1 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 229287 = 343931) B343931
theorem B655303 : Blo 227813 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B2621483 : Blo 227813 2621483 := bstep (se 1 (by rfl) ⟨1966112, by rfl⟩ : syracuseStep 2621483 = 3932225) B3932225
theorem B229503 : Blo 227813 229503 := bstep (se 1 (by rfl) ⟨172127, by rfl⟩ : syracuseStep 229503 = 344255) B344255
theorem B1736963 : Blo 227813 1736963 := bstep (se 1 (by rfl) ⟨1302722, by rfl⟩ : syracuseStep 1736963 = 2605445) B2605445
theorem B229787 : Blo 227813 229787 := bstep (se 1 (by rfl) ⟨172340, by rfl⟩ : syracuseStep 229787 = 344681) B344681
theorem B229791 : Blo 227813 229791 := bstep (se 1 (by rfl) ⟨172343, by rfl⟩ : syracuseStep 229791 = 344687) B344687
theorem B2195885 : Blo 227813 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B623207 : Blo 227813 623207 := bstep (se 1 (by rfl) ⟨467405, by rfl⟩ : syracuseStep 623207 = 934811) B934811
theorem B230207 : Blo 227813 230207 := bstep (se 1 (by rfl) ⟨172655, by rfl⟩ : syracuseStep 230207 = 345311) B345311
theorem B656191 : Blo 227813 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B230215 : Blo 227813 230215 := bstep (se 1 (by rfl) ⟨172661, by rfl⟩ : syracuseStep 230215 = 345323) B345323
theorem B656363 : Blo 227813 656363 := bstep (se 1 (by rfl) ⟨492272, by rfl⟩ : syracuseStep 656363 = 984545) B984545
theorem B328745 : Blo 227813 328745 := bstep (se 2 (by rfl) ⟨123279, by rfl⟩ : syracuseStep 328745 = 246559) B246559
theorem B230471 : Blo 227813 230471 := bstep (se 1 (by rfl) ⟨172853, by rfl⟩ : syracuseStep 230471 = 345707) B345707
theorem B230527 : Blo 227813 230527 := bstep (se 1 (by rfl) ⟨172895, by rfl⟩ : syracuseStep 230527 = 345791) B345791
theorem B230651 : Blo 227813 230651 := bstep (se 1 (by rfl) ⟨172988, by rfl⟩ : syracuseStep 230651 = 345977) B345977
theorem B1312361 : Blo 227813 1312361 := bstep (se 2 (by rfl) ⟨492135, by rfl⟩ : syracuseStep 1312361 = 984271) B984271
theorem B526057 : Blo 227813 526057 := bstep (se 2 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 526057 = 394543) B394543
theorem B231151 : Blo 227813 231151 := bstep (se 1 (by rfl) ⟨173363, by rfl⟩ : syracuseStep 231151 = 346727) B346727
theorem B231279 : Blo 227813 231279 := bstep (se 1 (by rfl) ⟨173459, by rfl⟩ : syracuseStep 231279 = 346919) B346919
theorem B231495 : Blo 227813 231495 := bstep (se 1 (by rfl) ⟨173621, by rfl⟩ : syracuseStep 231495 = 347243) B347243
theorem B231655 : Blo 227813 231655 := bstep (se 1 (by rfl) ⟨173741, by rfl⟩ : syracuseStep 231655 = 347483) B347483
theorem B231675 : Blo 227813 231675 := bstep (se 1 (by rfl) ⟨173756, by rfl⟩ : syracuseStep 231675 = 347513) B347513
theorem B231679 : Blo 227813 231679 := bstep (se 1 (by rfl) ⟨173759, by rfl⟩ : syracuseStep 231679 = 347519) B347519
theorem B3967321 : Blo 227813 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B233119 : Blo 227813 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B6655931 : Blo 227813 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B659495 : Blo 227813 659495 := bstep (se 1 (by rfl) ⟨494621, by rfl⟩ : syracuseStep 659495 = 989243) B989243
theorem B1740851 : Blo 227813 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B47551211 : Blo 227813 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B693431 : Blo 227813 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B792031 : Blo 227813 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B1480531 : Blo 227813 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B37623851 : Blo 227813 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B4987453 : Blo 227813 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B2792015 : Blo 227813 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B236575 : Blo 227813 236575 := bstep (se 1 (by rfl) ⟨177431, by rfl⟩ : syracuseStep 236575 = 354863) B354863
theorem B1350695 : Blo 227813 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B826631 : Blo 227813 826631 := bstep (se 1 (by rfl) ⟨619973, by rfl⟩ : syracuseStep 826631 = 1239947) B1239947
theorem B1187081 : Blo 227813 1187081 := bstep (se 2 (by rfl) ⟨445155, by rfl⟩ : syracuseStep 1187081 = 890311) B890311
theorem B1154897 : Blo 227813 1154897 := bstep (se 2 (by rfl) ⟨433086, by rfl⟩ : syracuseStep 1154897 = 866173) B866173
theorem B368795 : Blo 227813 368795 := bstep (se 1 (by rfl) ⟨276596, by rfl⟩ : syracuseStep 368795 = 553193) B553193
theorem B730271 : Blo 227813 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B1975751 : Blo 227813 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B370127 : Blo 227813 370127 := bstep (se 1 (by rfl) ⟨277595, by rfl⟩ : syracuseStep 370127 = 555191) B555191
theorem B730937 : Blo 227813 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B1157003 : Blo 227813 1157003 := bstep (se 1 (by rfl) ⟨867752, by rfl⟩ : syracuseStep 1157003 = 1735505) B1735505
theorem B2631689 : Blo 227813 2631689 := bstep (se 2 (by rfl) ⟨986883, by rfl⟩ : syracuseStep 2631689 = 1973767) B1973767
theorem B1386719 : Blo 227813 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B928583 : Blo 227813 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B732527 : Blo 227813 732527 := bstep (se 1 (by rfl) ⟨549395, by rfl⟩ : syracuseStep 732527 = 1098791) B1098791
theorem B1158623 : Blo 227813 1158623 := bstep (se 1 (by rfl) ⟨868967, by rfl⟩ : syracuseStep 1158623 = 1737935) B1737935
theorem B733961 : Blo 227813 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B1487641 : Blo 227813 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B3945347 : Blo 227813 3945347 := bstep (se 1 (by rfl) ⟨2959010, by rfl⟩ : syracuseStep 3945347 = 5918021) B5918021
theorem B17839223 : Blo 227813 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B2962817 : Blo 227813 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B308711 : Blo 227813 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B1160729 : Blo 227813 1160729 := bstep (se 2 (by rfl) ⟨435273, by rfl⟩ : syracuseStep 1160729 = 870547) B870547
theorem B275995 : Blo 227813 275995 := bstep (se 1 (by rfl) ⟨206996, by rfl⟩ : syracuseStep 275995 = 413993) B413993
theorem B341915 : Blo 227813 341915 := bstep (se 1 (by rfl) ⟨256436, by rfl⟩ : syracuseStep 341915 = 512873) B512873
theorem B341951 : Blo 227813 341951 := bstep (se 1 (by rfl) ⟨256463, by rfl⟩ : syracuseStep 341951 = 512927) B512927
theorem B342119 : Blo 227813 342119 := bstep (se 1 (by rfl) ⟨256589, by rfl⟩ : syracuseStep 342119 = 513179) B513179
theorem B1161377 : Blo 227813 1161377 := bstep (se 2 (by rfl) ⟨435516, by rfl⟩ : syracuseStep 1161377 = 871033) B871033
theorem B342503 : Blo 227813 342503 := bstep (se 1 (by rfl) ⟨256877, by rfl⟩ : syracuseStep 342503 = 513755) B513755
theorem B342575 : Blo 227813 342575 := bstep (se 1 (by rfl) ⟨256931, by rfl⟩ : syracuseStep 342575 = 513863) B513863
theorem B932617 : Blo 227813 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B7945147 : Blo 227813 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B2603987 : Blo 227813 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B343247 : Blo 227813 343247 := bstep (se 1 (by rfl) ⟨257435, by rfl⟩ : syracuseStep 343247 = 514871) B514871
theorem B343337 : Blo 227813 343337 := bstep (se 2 (by rfl) ⟨128751, by rfl⟩ : syracuseStep 343337 = 257503) B257503
theorem B343367 : Blo 227813 343367 := bstep (se 1 (by rfl) ⟨257525, by rfl⟩ : syracuseStep 343367 = 515051) B515051
theorem B343967 : Blo 227813 343967 := bstep (se 1 (by rfl) ⟨257975, by rfl⟩ : syracuseStep 343967 = 515951) B515951
theorem B344057 : Blo 227813 344057 := bstep (se 2 (by rfl) ⟨129021, by rfl⟩ : syracuseStep 344057 = 258043) B258043
theorem B18890759 : Blo 227813 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B344201 : Blo 227813 344201 := bstep (se 2 (by rfl) ⟨129075, by rfl⟩ : syracuseStep 344201 = 258151) B258151
theorem B8896715 : Blo 227813 8896715 := bstep (se 1 (by rfl) ⟨6672536, by rfl⟩ : syracuseStep 8896715 = 13345073) B13345073
theorem B770255 : Blo 227813 770255 := bstep (se 1 (by rfl) ⟨577691, by rfl⟩ : syracuseStep 770255 = 1155383) B1155383
theorem B344297 : Blo 227813 344297 := bstep (se 2 (by rfl) ⟨129111, by rfl⟩ : syracuseStep 344297 = 258223) B258223
theorem B344423 : Blo 227813 344423 := bstep (se 1 (by rfl) ⟨258317, by rfl⟩ : syracuseStep 344423 = 516635) B516635
theorem B1163645 : Blo 227813 1163645 := bstep (se 3 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 1163645 = 436367) B436367
theorem B344543 : Blo 227813 344543 := bstep (se 1 (by rfl) ⟨258407, by rfl⟩ : syracuseStep 344543 = 516815) B516815
theorem B344795 : Blo 227813 344795 := bstep (se 1 (by rfl) ⟨258596, by rfl⟩ : syracuseStep 344795 = 517193) B517193
theorem B738011 : Blo 227813 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B345209 : Blo 227813 345209 := bstep (se 2 (by rfl) ⟨129453, by rfl⟩ : syracuseStep 345209 = 258907) B258907
theorem B345407 : Blo 227813 345407 := bstep (se 1 (by rfl) ⟨259055, by rfl⟩ : syracuseStep 345407 = 518111) B518111
theorem B410951 : Blo 227813 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B2934407 : Blo 227813 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B346079 : Blo 227813 346079 := bstep (se 1 (by rfl) ⟨259559, by rfl⟩ : syracuseStep 346079 = 519119) B519119
theorem B346139 : Blo 227813 346139 := bstep (se 1 (by rfl) ⟨259604, by rfl⟩ : syracuseStep 346139 = 519209) B519209
theorem B346295 : Blo 227813 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B346319 : Blo 227813 346319 := bstep (se 1 (by rfl) ⟨259739, by rfl⟩ : syracuseStep 346319 = 519479) B519479
theorem B346423 : Blo 227813 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B346715 : Blo 227813 346715 := bstep (se 1 (by rfl) ⟨260036, by rfl⟩ : syracuseStep 346715 = 520073) B520073
theorem B2607839 : Blo 227813 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B346859 : Blo 227813 346859 := bstep (se 1 (by rfl) ⟨260144, by rfl⟩ : syracuseStep 346859 = 520289) B520289
theorem B346889 : Blo 227813 346889 := bstep (se 2 (by rfl) ⟨130083, by rfl⟩ : syracuseStep 346889 = 260167) B260167
theorem B3754997 : Blo 227813 3754997 := bstep (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) B352031
theorem B347303 : Blo 227813 347303 := bstep (se 1 (by rfl) ⟨260477, by rfl⟩ : syracuseStep 347303 = 520955) B520955
theorem B740627 : Blo 227813 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B347447 : Blo 227813 347447 := bstep (se 1 (by rfl) ⟨260585, by rfl⟩ : syracuseStep 347447 = 521171) B521171
theorem B347689 : Blo 227813 347689 := bstep (se 2 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 347689 = 260767) B260767
theorem B1068623 : Blo 227813 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B1397033 : Blo 227813 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B741803 : Blo 227813 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B578279 : Blo 227813 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B578441 : Blo 227813 578441 := bstep (se 2 (by rfl) ⟨216915, by rfl⟩ : syracuseStep 578441 = 433831) B433831
theorem B1168343 : Blo 227813 1168343 := bstep (se 1 (by rfl) ⟨876257, by rfl⟩ : syracuseStep 1168343 = 1752515) B1752515
theorem B873737 : Blo 227813 873737 := bstep (se 2 (by rfl) ⟨327651, by rfl⟩ : syracuseStep 873737 = 655303) B655303
theorem B578927 : Blo 227813 578927 := bstep (se 1 (by rfl) ⟨434195, by rfl⟩ : syracuseStep 578927 = 868391) B868391
theorem B775655 : Blo 227813 775655 := bstep (se 1 (by rfl) ⟨581741, by rfl⟩ : syracuseStep 775655 = 1163483) B1163483
theorem B1169099 : Blo 227813 1169099 := bstep (se 1 (by rfl) ⟨876824, by rfl⟩ : syracuseStep 1169099 = 1753649) B1753649
theorem B1300171 : Blo 227813 1300171 := bstep (se 1 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 1300171 = 1950257) B1950257
theorem B776033 : Blo 227813 776033 := bstep (se 2 (by rfl) ⟨291012, by rfl⟩ : syracuseStep 776033 = 582025) B582025
theorem B579575 : Blo 227813 579575 := bstep (se 1 (by rfl) ⟨434681, by rfl⟩ : syracuseStep 579575 = 869363) B869363
theorem B6609113 : Blo 227813 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B514331 : Blo 227813 514331 := bstep (se 1 (by rfl) ⟨385748, by rfl⟩ : syracuseStep 514331 = 771497) B771497
theorem B3824047 : Blo 227813 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B875195 : Blo 227813 875195 := bstep (se 1 (by rfl) ⟨656396, by rfl⟩ : syracuseStep 875195 = 1312793) B1312793
theorem B2054969 : Blo 227813 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B973883 : Blo 227813 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B515303 : Blo 227813 515303 := bstep (se 1 (by rfl) ⟨386477, by rfl⟩ : syracuseStep 515303 = 772955) B772955
theorem B777545 : Blo 227813 777545 := bstep (se 2 (by rfl) ⟨291579, by rfl⟩ : syracuseStep 777545 = 583159) B583159
theorem B1465769 : Blo 227813 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B4218313 : Blo 227813 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B385087 : Blo 227813 385087 := bstep (se 1 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 385087 = 577631) B577631
theorem B516257 : Blo 227813 516257 := bstep (se 2 (by rfl) ⟨193596, by rfl⟩ : syracuseStep 516257 = 387193) B387193
theorem B2482487 : Blo 227813 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B877139 : Blo 227813 877139 := bstep (se 1 (by rfl) ⟨657854, by rfl⟩ : syracuseStep 877139 = 1315709) B1315709
theorem B385769 : Blo 227813 385769 := bstep (se 2 (by rfl) ⟨144663, by rfl⟩ : syracuseStep 385769 = 289327) B289327
theorem B975881 : Blo 227813 975881 := bstep (se 2 (by rfl) ⟨365955, by rfl⟩ : syracuseStep 975881 = 731911) B731911
theorem B517211 : Blo 227813 517211 := bstep (se 1 (by rfl) ⟨387908, by rfl⟩ : syracuseStep 517211 = 775817) B775817
theorem B517607 : Blo 227813 517607 := bstep (se 1 (by rfl) ⟨388205, by rfl⟩ : syracuseStep 517607 = 776411) B776411
theorem B517787 : Blo 227813 517787 := bstep (se 1 (by rfl) ⟨388340, by rfl⟩ : syracuseStep 517787 = 776681) B776681
theorem B1173203 : Blo 227813 1173203 := bstep (se 1 (by rfl) ⟨879902, by rfl⟩ : syracuseStep 1173203 = 1759805) B1759805
theorem B648947 : Blo 227813 648947 := bstep (se 1 (by rfl) ⟨486710, by rfl⟩ : syracuseStep 648947 = 973421) B973421
theorem B780191 : Blo 227813 780191 := bstep (se 1 (by rfl) ⟨585143, by rfl⟩ : syracuseStep 780191 = 1170287) B1170287
theorem B288679 : Blo 227813 288679 := bstep (se 1 (by rfl) ⟨216509, by rfl⟩ : syracuseStep 288679 = 433019) B433019
theorem B780623 : Blo 227813 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B2779559 : Blo 227813 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B387497 : Blo 227813 387497 := bstep (se 2 (by rfl) ⟨145311, by rfl⟩ : syracuseStep 387497 = 290623) B290623
theorem B518759 : Blo 227813 518759 := bstep (se 1 (by rfl) ⟨389069, by rfl⟩ : syracuseStep 518759 = 778139) B778139
theorem B748187 : Blo 227813 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B256891 : Blo 227813 256891 := bstep (se 1 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 256891 = 385337) B385337
theorem B57863099 : Blo 227813 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B519137 : Blo 227813 519137 := bstep (se 2 (by rfl) ⟨194676, by rfl⟩ : syracuseStep 519137 = 389353) B389353
theorem B584729 : Blo 227813 584729 := bstep (se 2 (by rfl) ⟨219273, by rfl⟩ : syracuseStep 584729 = 438547) B438547
theorem B1567855 : Blo 227813 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B257215 : Blo 227813 257215 := bstep (se 1 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 257215 = 385823) B385823
theorem B880055 : Blo 227813 880055 := bstep (se 1 (by rfl) ⟨660041, by rfl⟩ : syracuseStep 880055 = 1320083) B1320083
theorem B257755 : Blo 227813 257755 := bstep (se 1 (by rfl) ⟨193316, by rfl⟩ : syracuseStep 257755 = 386633) B386633
theorem B585569 : Blo 227813 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B258079 : Blo 227813 258079 := bstep (se 1 (by rfl) ⟨193559, by rfl⟩ : syracuseStep 258079 = 387119) B387119
theorem B553355 : Blo 227813 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B651689 : Blo 227813 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B18641441 : Blo 227813 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B8417945 : Blo 227813 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B2192467 : Blo 227813 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B2618567 : Blo 227813 2618567 := bstep (se 1 (by rfl) ⟨1963925, by rfl⟩ : syracuseStep 2618567 = 3927851) B3927851
theorem B8975711 : Blo 227813 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B980495 : Blo 227813 980495 := bstep (se 1 (by rfl) ⟨735371, by rfl⟩ : syracuseStep 980495 = 1470743) B1470743
theorem B554777 : Blo 227813 554777 := bstep (se 2 (by rfl) ⟨208041, by rfl⟩ : syracuseStep 554777 = 416083) B416083
theorem B653321 : Blo 227813 653321 := bstep (se 2 (by rfl) ⟨244995, by rfl⟩ : syracuseStep 653321 = 489991) B489991
theorem B292891 : Blo 227813 292891 := bstep (se 1 (by rfl) ⟨219668, by rfl⟩ : syracuseStep 292891 = 439337) B439337
theorem B653503 : Blo 227813 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B1866503 : Blo 227813 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B2882429 : Blo 227813 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B228319 : Blo 227813 228319 := bstep (se 1 (by rfl) ⟨171239, by rfl⟩ : syracuseStep 228319 = 342479) B342479
theorem B228379 : Blo 227813 228379 := bstep (se 1 (by rfl) ⟨171284, by rfl⟩ : syracuseStep 228379 = 342569) B342569
theorem B326683 : Blo 227813 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B228507 : Blo 227813 228507 := bstep (se 1 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 228507 = 342761) B342761
theorem B19004669 : Blo 227813 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B228763 : Blo 227813 228763 := bstep (se 1 (by rfl) ⟨171572, by rfl⟩ : syracuseStep 228763 = 343145) B343145
theorem B1473947 : Blo 227813 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B228847 : Blo 227813 228847 := bstep (se 1 (by rfl) ⟨171635, by rfl⟩ : syracuseStep 228847 = 343271) B343271
theorem B229183 : Blo 227813 229183 := bstep (se 1 (by rfl) ⟨171887, by rfl⟩ : syracuseStep 229183 = 343775) B343775
theorem B229211 : Blo 227813 229211 := bstep (se 1 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 229211 = 343817) B343817
theorem B2817899 : Blo 227813 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B229467 : Blo 227813 229467 := bstep (se 1 (by rfl) ⟨172100, by rfl⟩ : syracuseStep 229467 = 344201) B344201
theorem B5931143 : Blo 227813 5931143 := bstep (se 1 (by rfl) ⟨4448357, by rfl⟩ : syracuseStep 5931143 = 8896715) B8896715
theorem B229531 : Blo 227813 229531 := bstep (se 1 (by rfl) ⟨172148, by rfl⟩ : syracuseStep 229531 = 344297) B344297
theorem B229615 : Blo 227813 229615 := bstep (se 1 (by rfl) ⟨172211, by rfl⟩ : syracuseStep 229615 = 344423) B344423
theorem B229695 : Blo 227813 229695 := bstep (se 1 (by rfl) ⟨172271, by rfl⟩ : syracuseStep 229695 = 344543) B344543
theorem B229863 : Blo 227813 229863 := bstep (se 1 (by rfl) ⟨172397, by rfl⟩ : syracuseStep 229863 = 344795) B344795
theorem B492007 : Blo 227813 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B230139 : Blo 227813 230139 := bstep (se 1 (by rfl) ⟨172604, by rfl⟩ : syracuseStep 230139 = 345209) B345209
theorem B230271 : Blo 227813 230271 := bstep (se 1 (by rfl) ⟨172703, by rfl⟩ : syracuseStep 230271 = 345407) B345407
theorem B230719 : Blo 227813 230719 := bstep (se 1 (by rfl) ⟨173039, by rfl⟩ : syracuseStep 230719 = 346079) B346079
theorem B230759 : Blo 227813 230759 := bstep (se 1 (by rfl) ⟨173069, by rfl⟩ : syracuseStep 230759 = 346139) B346139
theorem B230863 : Blo 227813 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B230879 : Blo 227813 230879 := bstep (se 1 (by rfl) ⟨173159, by rfl⟩ : syracuseStep 230879 = 346319) B346319
theorem B231143 : Blo 227813 231143 := bstep (se 1 (by rfl) ⟨173357, by rfl⟩ : syracuseStep 231143 = 346715) B346715
theorem B1738559 : Blo 227813 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B231239 : Blo 227813 231239 := bstep (se 1 (by rfl) ⟨173429, by rfl⟩ : syracuseStep 231239 = 346859) B346859
theorem B231259 : Blo 227813 231259 := bstep (se 1 (by rfl) ⟨173444, by rfl⟩ : syracuseStep 231259 = 346889) B346889
theorem B231535 : Blo 227813 231535 := bstep (se 1 (by rfl) ⟨173651, by rfl⟩ : syracuseStep 231535 = 347303) B347303
theorem B493751 : Blo 227813 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B231631 : Blo 227813 231631 := bstep (se 1 (by rfl) ⟨173723, by rfl⟩ : syracuseStep 231631 = 347447) B347447
theorem B461897 : Blo 227813 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B462287 : Blo 227813 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B987005 : Blo 227813 987005 := bstep (se 3 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 987005 = 370127) B370127
theorem B823229 : Blo 227813 823229 := bstep (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) B308711
theorem B6951349 : Blo 227813 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B463585 : Blo 227813 463585 := bstep (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) B347689
theorem B791387 : Blo 227813 791387 := bstep (se 1 (by rfl) ⟨593540, by rfl⟩ : syracuseStep 791387 = 1187081) B1187081
theorem B42374117 : Blo 227813 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B1742309 : Blo 227813 1742309 := bstep (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) B326683
theorem B8361893 : Blo 227813 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B1317167 : Blo 227813 1317167 := bstep (se 1 (by rfl) ⟨987875, by rfl⟩ : syracuseStep 1317167 = 1975751) B1975751
theorem B432631 : Blo 227813 432631 := bstep (se 1 (by rfl) ⟨324473, by rfl⟩ : syracuseStep 432631 = 648947) B648947
theorem B2923289 : Blo 227813 2923289 := bstep (se 2 (by rfl) ⟨1096233, by rfl⟩ : syracuseStep 2923289 = 2192467) B2192467
theorem B924479 : Blo 227813 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B498791 : Blo 227813 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B38575399 : Blo 227813 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B1056041 : Blo 227813 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B367993 : Blo 227813 367993 := bstep (se 2 (by rfl) ⟨137997, by rfl⟩ : syracuseStep 367993 = 275995) B275995
theorem B1974041 : Blo 227813 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B368903 : Blo 227813 368903 := bstep (se 1 (by rfl) ⟨276677, by rfl⟩ : syracuseStep 368903 = 553355) B553355
theorem B12427627 : Blo 227813 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B5611963 : Blo 227813 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B2630231 : Blo 227813 2630231 := bstep (se 1 (by rfl) ⟨1972673, by rfl⟩ : syracuseStep 2630231 = 3945347) B3945347
theorem B1745711 : Blo 227813 1745711 := bstep (se 1 (by rfl) ⟨1309283, by rfl⟩ : syracuseStep 1745711 = 2618567) B2618567
theorem B1975211 : Blo 227813 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B369851 : Blo 227813 369851 := bstep (se 1 (by rfl) ⟨277388, by rfl⟩ : syracuseStep 369851 = 554777) B554777
theorem B435547 : Blo 227813 435547 := bstep (se 1 (by rfl) ⟨326660, by rfl⟩ : syracuseStep 435547 = 653321) B653321
theorem B1878599 : Blo 227813 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B12593839 : Blo 227813 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B1747655 : Blo 227813 1747655 := bstep (se 1 (by rfl) ⟨1310741, by rfl⟩ : syracuseStep 1747655 = 2621483) B2621483
theorem B1157975 : Blo 227813 1157975 := bstep (se 1 (by rfl) ⟨868481, by rfl⟩ : syracuseStep 1157975 = 1736963) B1736963
theorem B437575 : Blo 227813 437575 := bstep (se 1 (by rfl) ⟨328181, by rfl⟩ : syracuseStep 437575 = 656363) B656363
theorem B1978141 : Blo 227813 1978141 := bstep (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) B741803
theorem B2503331 : Blo 227813 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B4437287 : Blo 227813 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B439663 : Blo 227813 439663 := bstep (se 1 (by rfl) ⟨329747, by rfl⟩ : syracuseStep 439663 = 659495) B659495
theorem B1160567 : Blo 227813 1160567 := bstep (se 1 (by rfl) ⟨870425, by rfl⟩ : syracuseStep 1160567 = 1740851) B1740851
theorem B931355 : Blo 227813 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B5289761 : Blo 227813 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B31700807 : Blo 227813 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B1095869 : Blo 227813 1095869 := bstep (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) B410951
theorem B342521 : Blo 227813 342521 := bstep (se 2 (by rfl) ⟨128445, by rfl⟩ : syracuseStep 342521 = 256891) B256891
theorem B25082567 : Blo 227813 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B4406075 : Blo 227813 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B342887 : Blo 227813 342887 := bstep (se 1 (by rfl) ⟨257165, by rfl⟩ : syracuseStep 342887 = 514331) B514331
theorem B342953 : Blo 227813 342953 := bstep (se 2 (by rfl) ⟨128607, by rfl⟩ : syracuseStep 342953 = 257215) B257215
theorem B343535 : Blo 227813 343535 := bstep (se 1 (by rfl) ⟨257651, by rfl⟩ : syracuseStep 343535 = 515303) B515303
theorem B310825 : Blo 227813 310825 := bstep (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) B233119
theorem B343673 : Blo 227813 343673 := bstep (se 2 (by rfl) ⟨128877, by rfl⟩ : syracuseStep 343673 = 257755) B257755
theorem B769931 : Blo 227813 769931 := bstep (se 1 (by rfl) ⟨577448, by rfl⟩ : syracuseStep 769931 = 1154897) B1154897
theorem B344105 : Blo 227813 344105 := bstep (se 2 (by rfl) ⟨129039, by rfl⟩ : syracuseStep 344105 = 258079) B258079
theorem B245863 : Blo 227813 245863 := bstep (se 1 (by rfl) ⟨184397, by rfl⟩ : syracuseStep 245863 = 368795) B368795
theorem B344171 : Blo 227813 344171 := bstep (se 1 (by rfl) ⟨258128, by rfl⟩ : syracuseStep 344171 = 516257) B516257
theorem B1654991 : Blo 227813 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B344807 : Blo 227813 344807 := bstep (se 1 (by rfl) ⟨258605, by rfl⟩ : syracuseStep 344807 = 517211) B517211
theorem B345071 : Blo 227813 345071 := bstep (se 1 (by rfl) ⟨258803, by rfl⟩ : syracuseStep 345071 = 517607) B517607
theorem B1983521 : Blo 227813 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B345191 : Blo 227813 345191 := bstep (se 1 (by rfl) ⟨258893, by rfl⟩ : syracuseStep 345191 = 517787) B517787
theorem B771335 : Blo 227813 771335 := bstep (se 1 (by rfl) ⟨578501, by rfl⟩ : syracuseStep 771335 = 1157003) B1157003
theorem B1754459 : Blo 227813 1754459 := bstep (se 1 (by rfl) ⟨1315844, by rfl⟩ : syracuseStep 1754459 = 2631689) B2631689
theorem B1853039 : Blo 227813 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B345839 : Blo 227813 345839 := bstep (se 1 (by rfl) ⟨259379, by rfl⟩ : syracuseStep 345839 = 518759) B518759
theorem B346091 : Blo 227813 346091 := bstep (se 1 (by rfl) ⟨259568, by rfl⟩ : syracuseStep 346091 = 519137) B519137
theorem B772415 : Blo 227813 772415 := bstep (se 1 (by rfl) ⟨579311, by rfl⟩ : syracuseStep 772415 = 1158623) B1158623
theorem B871337 : Blo 227813 871337 := bstep (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) B653503
theorem B5098729 : Blo 227813 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B5983807 : Blo 227813 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B773819 : Blo 227813 773819 := bstep (se 1 (by rfl) ⟨580364, by rfl⟩ : syracuseStep 773819 = 1160729) B1160729
theorem B2805637 : Blo 227813 2805637 := bstep (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) B526057
theorem B315433 : Blo 227813 315433 := bstep (se 2 (by rfl) ⟨118287, by rfl⟩ : syracuseStep 315433 = 236575) B236575
theorem B774251 : Blo 227813 774251 := bstep (se 1 (by rfl) ⟨580688, by rfl⟩ : syracuseStep 774251 = 1161377) B1161377
theorem B1921619 : Blo 227813 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B5624417 : Blo 227813 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B12669779 : Blo 227813 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B513449 : Blo 227813 513449 := bstep (se 2 (by rfl) ⟨192543, by rfl⟩ : syracuseStep 513449 = 385087) B385087
theorem B513503 : Blo 227813 513503 := bstep (se 1 (by rfl) ⟨385127, by rfl⟩ : syracuseStep 513503 = 770255) B770255
theorem B775763 : Blo 227813 775763 := bstep (se 1 (by rfl) ⟨581822, by rfl⟩ : syracuseStep 775763 = 1163645) B1163645
theorem B1463923 : Blo 227813 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B415471 : Blo 227813 415471 := bstep (se 1 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 415471 = 623207) B623207
theorem B874907 : Blo 227813 874907 := bstep (se 1 (by rfl) ⟨656180, by rfl⟩ : syracuseStep 874907 = 1312361) B1312361
theorem B874921 : Blo 227813 874921 := bstep (se 2 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 874921 = 656191) B656191
theorem B1956271 : Blo 227813 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B1957229 : Blo 227813 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B712415 : Blo 227813 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B384905 : Blo 227813 384905 := bstep (se 2 (by rfl) ⟨144339, by rfl⟩ : syracuseStep 384905 = 288679) B288679
theorem B876653 : Blo 227813 876653 := bstep (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) B328745
theorem B385519 : Blo 227813 385519 := bstep (se 1 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 385519 = 578279) B578279
theorem B385627 : Blo 227813 385627 := bstep (se 1 (by rfl) ⟨289220, by rfl⟩ : syracuseStep 385627 = 578441) B578441
theorem B778895 : Blo 227813 778895 := bstep (se 1 (by rfl) ⟨584171, by rfl⟩ : syracuseStep 778895 = 1168343) B1168343
theorem B582491 : Blo 227813 582491 := bstep (se 1 (by rfl) ⟨436868, by rfl⟩ : syracuseStep 582491 = 873737) B873737
theorem B385951 : Blo 227813 385951 := bstep (se 1 (by rfl) ⟨289463, by rfl⟩ : syracuseStep 385951 = 578927) B578927
theorem B517103 : Blo 227813 517103 := bstep (se 1 (by rfl) ⟨387827, by rfl⟩ : syracuseStep 517103 = 775655) B775655
theorem B779399 : Blo 227813 779399 := bstep (se 1 (by rfl) ⟨584549, by rfl⟩ : syracuseStep 779399 = 1169099) B1169099
theorem B517355 : Blo 227813 517355 := bstep (se 1 (by rfl) ⟨388016, by rfl⟩ : syracuseStep 517355 = 776033) B776033
theorem B386383 : Blo 227813 386383 := bstep (se 1 (by rfl) ⟨289787, by rfl⟩ : syracuseStep 386383 = 579575) B579575
theorem B4973957 : Blo 227813 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B1861343 : Blo 227813 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B583463 : Blo 227813 583463 := bstep (se 1 (by rfl) ⟨437597, by rfl⟩ : syracuseStep 583463 = 875195) B875195
theorem B1369979 : Blo 227813 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B649255 : Blo 227813 649255 := bstep (se 1 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 649255 = 973883) B973883
theorem B551087 : Blo 227813 551087 := bstep (se 1 (by rfl) ⟨413315, by rfl⟩ : syracuseStep 551087 = 826631) B826631
theorem B518363 : Blo 227813 518363 := bstep (se 1 (by rfl) ⟨388772, by rfl⟩ : syracuseStep 518363 = 777545) B777545
theorem B977179 : Blo 227813 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B584759 : Blo 227813 584759 := bstep (se 1 (by rfl) ⟨438569, by rfl⟩ : syracuseStep 584759 = 877139) B877139
theorem B257179 : Blo 227813 257179 := bstep (se 1 (by rfl) ⟨192884, by rfl⟩ : syracuseStep 257179 = 385769) B385769
theorem B650587 : Blo 227813 650587 := bstep (se 1 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 650587 = 975881) B975881
theorem B486847 : Blo 227813 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B782135 : Blo 227813 782135 := bstep (se 1 (by rfl) ⟨586601, by rfl⟩ : syracuseStep 782135 = 1173203) B1173203
theorem B487291 : Blo 227813 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B520127 : Blo 227813 520127 := bstep (se 1 (by rfl) ⟨390095, by rfl⟩ : syracuseStep 520127 = 780191) B780191
theorem B520415 : Blo 227813 520415 := bstep (se 1 (by rfl) ⟨390311, by rfl⟩ : syracuseStep 520415 = 780623) B780623
theorem B258331 : Blo 227813 258331 := bstep (se 1 (by rfl) ⟨193748, by rfl⟩ : syracuseStep 258331 = 387497) B387497
theorem B619055 : Blo 227813 619055 := bstep (se 1 (by rfl) ⟨464291, by rfl⟩ : syracuseStep 619055 = 928583) B928583
theorem B389819 : Blo 227813 389819 := bstep (se 1 (by rfl) ⟨292364, by rfl⟩ : syracuseStep 389819 = 584729) B584729
theorem B488351 : Blo 227813 488351 := bstep (se 1 (by rfl) ⟨366263, by rfl⟩ : syracuseStep 488351 = 732527) B732527
theorem B1733561 : Blo 227813 1733561 := bstep (se 2 (by rfl) ⟨650085, by rfl⟩ : syracuseStep 1733561 = 1300171) B1300171
theorem B586703 : Blo 227813 586703 := bstep (se 1 (by rfl) ⟨440027, by rfl⟩ : syracuseStep 586703 = 880055) B880055
theorem B390379 : Blo 227813 390379 := bstep (se 1 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 390379 = 585569) B585569
theorem B390521 : Blo 227813 390521 := bstep (se 2 (by rfl) ⟨146445, by rfl⟩ : syracuseStep 390521 = 292891) B292891
theorem B3601853 : Blo 227813 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B11892815 : Blo 227813 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B6649937 : Blo 227813 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B653663 : Blo 227813 653663 := bstep (se 1 (by rfl) ⟨490247, by rfl⟩ : syracuseStep 653663 = 980495) B980495
theorem B227943 : Blo 227813 227943 := bstep (se 1 (by rfl) ⟨170957, by rfl⟩ : syracuseStep 227943 = 341915) B341915
theorem B227967 : Blo 227813 227967 := bstep (se 1 (by rfl) ⟨170975, by rfl⟩ : syracuseStep 227967 = 341951) B341951
theorem B228079 : Blo 227813 228079 := bstep (se 1 (by rfl) ⟨171059, by rfl⟩ : syracuseStep 228079 = 342119) B342119
theorem B228335 : Blo 227813 228335 := bstep (se 1 (by rfl) ⟨171251, by rfl⟩ : syracuseStep 228335 = 342503) B342503
theorem B228383 : Blo 227813 228383 := bstep (se 1 (by rfl) ⟨171287, by rfl⟩ : syracuseStep 228383 = 342575) B342575
theorem B1244335 : Blo 227813 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B1735991 : Blo 227813 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B228831 : Blo 227813 228831 := bstep (se 1 (by rfl) ⟨171623, by rfl⟩ : syracuseStep 228831 = 343247) B343247
theorem B228891 : Blo 227813 228891 := bstep (se 1 (by rfl) ⟨171668, by rfl⟩ : syracuseStep 228891 = 343337) B343337
theorem B228911 : Blo 227813 228911 := bstep (se 1 (by rfl) ⟨171683, by rfl⟩ : syracuseStep 228911 = 343367) B343367
theorem B982631 : Blo 227813 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B229311 : Blo 227813 229311 := bstep (se 1 (by rfl) ⟨171983, by rfl⟩ : syracuseStep 229311 = 343967) B343967
theorem B229371 : Blo 227813 229371 := bstep (se 1 (by rfl) ⟨172028, by rfl⟩ : syracuseStep 229371 = 344057) B344057
theorem B229403 : Blo 227813 229403 := bstep (se 1 (by rfl) ⟨172052, by rfl⟩ : syracuseStep 229403 = 344105) B344105
theorem B229447 : Blo 227813 229447 := bstep (se 1 (by rfl) ⟨172085, by rfl⟩ : syracuseStep 229447 = 344171) B344171
theorem B327817 : Blo 227813 327817 := bstep (se 2 (by rfl) ⟨122931, by rfl⟩ : syracuseStep 327817 = 245863) B245863
theorem B229871 : Blo 227813 229871 := bstep (se 1 (by rfl) ⟨172403, by rfl⟩ : syracuseStep 229871 = 344807) B344807
theorem B656009 : Blo 227813 656009 := bstep (se 2 (by rfl) ⟨246003, by rfl⟩ : syracuseStep 656009 = 492007) B492007
theorem B230047 : Blo 227813 230047 := bstep (se 1 (by rfl) ⟨172535, by rfl⟩ : syracuseStep 230047 = 345071) B345071
theorem B230127 : Blo 227813 230127 := bstep (se 1 (by rfl) ⟨172595, by rfl⟩ : syracuseStep 230127 = 345191) B345191
theorem B230559 : Blo 227813 230559 := bstep (se 1 (by rfl) ⟨172919, by rfl⟩ : syracuseStep 230559 = 345839) B345839
theorem B230727 : Blo 227813 230727 := bstep (se 1 (by rfl) ⟨173045, by rfl⟩ : syracuseStep 230727 = 346091) B346091
theorem B329167 : Blo 227813 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B658003 : Blo 227813 658003 := bstep (se 1 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 658003 = 987005) B987005
theorem B1281079 : Blo 227813 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B986269 : Blo 227813 986269 := bstep (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) B369851
theorem B527591 : Blo 227813 527591 := bstep (se 1 (by rfl) ⟨395693, by rfl⟩ : syracuseStep 527591 = 791387) B791387
theorem B28249411 : Blo 227813 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B5574595 : Blo 227813 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B332527 : Blo 227813 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B3740849 : Blo 227813 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B1316027 : Blo 227813 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B1316807 : Blo 227813 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B3315971 : Blo 227813 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B367391 : Blo 227813 367391 := bstep (se 1 (by rfl) ⟨275543, by rfl⟩ : syracuseStep 367391 = 551087) B551087
theorem B1155707 : Blo 227813 1155707 := bstep (se 1 (by rfl) ⟨866780, by rfl⟩ : syracuseStep 1155707 = 1733561) B1733561
theorem B2958191 : Blo 227813 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B2401235 : Blo 227813 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B4433291 : Blo 227813 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B730579 : Blo 227813 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B435775 : Blo 227813 435775 := bstep (se 1 (by rfl) ⟨326831, by rfl⟩ : syracuseStep 435775 = 653663) B653663
theorem B16721711 : Blo 227813 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B1157327 : Blo 227813 1157327 := bstep (se 1 (by rfl) ⟨867995, by rfl⟩ : syracuseStep 1157327 = 1735991) B1735991
theorem B1682309 : Blo 227813 1682309 := bstep (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) B315433
theorem B7482617 : Blo 227813 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B1322347 : Blo 227813 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B4926901 : Blo 227813 4926901 := bstep (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) B461897
theorem B1159039 : Blo 227813 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B865673 : Blo 227813 865673 := bstep (se 2 (by rfl) ⟨324627, by rfl⟩ : syracuseStep 865673 = 649255) B649255
theorem B16791785 : Blo 227813 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B342299 : Blo 227813 342299 := bstep (se 1 (by rfl) ⟨256724, by rfl⟩ : syracuseStep 342299 = 513449) B513449
theorem B342335 : Blo 227813 342335 := bstep (se 1 (by rfl) ⟨256751, by rfl⟩ : syracuseStep 342335 = 513503) B513503
theorem B1161539 : Blo 227813 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B342905 : Blo 227813 342905 := bstep (se 2 (by rfl) ⟨128589, by rfl⟩ : syracuseStep 342905 = 257179) B257179
theorem B6798305 : Blo 227813 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B867449 : Blo 227813 867449 := bstep (se 2 (by rfl) ⟨325293, by rfl⟩ : syracuseStep 867449 = 650587) B650587
theorem B1948859 : Blo 227813 1948859 := bstep (se 1 (by rfl) ⟨1461644, by rfl⟩ : syracuseStep 1948859 = 2923289) B2923289
theorem B7978409 : Blo 227813 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B704027 : Blo 227813 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B2637521 : Blo 227813 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B245935 : Blo 227813 245935 := bstep (se 1 (by rfl) ⟨184451, by rfl⟩ : syracuseStep 245935 = 368903) B368903
theorem B344441 : Blo 227813 344441 := bstep (se 2 (by rfl) ⟨129165, by rfl⟩ : syracuseStep 344441 = 258331) B258331
theorem B1753487 : Blo 227813 1753487 := bstep (se 1 (by rfl) ⟨1315115, by rfl⟩ : syracuseStep 1753487 = 2630231) B2630231
theorem B1163807 : Blo 227813 1163807 := bstep (se 1 (by rfl) ⟨872855, by rfl⟩ : syracuseStep 1163807 = 1745711) B1745711
theorem B344735 : Blo 227813 344735 := bstep (se 1 (by rfl) ⟨258551, by rfl⟩ : syracuseStep 344735 = 517103) B517103
theorem B344903 : Blo 227813 344903 := bstep (se 1 (by rfl) ⟨258677, by rfl⟩ : syracuseStep 344903 = 517355) B517355
theorem B345575 : Blo 227813 345575 := bstep (se 1 (by rfl) ⟨259181, by rfl⟩ : syracuseStep 345575 = 518363) B518363
theorem B1165103 : Blo 227813 1165103 := bstep (se 1 (by rfl) ⟨873827, by rfl⟩ : syracuseStep 1165103 = 1747655) B1747655
theorem B771983 : Blo 227813 771983 := bstep (se 1 (by rfl) ⟨578987, by rfl⟩ : syracuseStep 771983 = 1157975) B1157975
theorem B1951897 : Blo 227813 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B346751 : Blo 227813 346751 := bstep (se 1 (by rfl) ⟨260063, by rfl⟩ : syracuseStep 346751 = 520127) B520127
theorem B346943 : Blo 227813 346943 := bstep (se 1 (by rfl) ⟨260207, by rfl⟩ : syracuseStep 346943 = 520415) B520415
theorem B412703 : Blo 227813 412703 := bstep (se 1 (by rfl) ⟨309527, by rfl⟩ : syracuseStep 412703 = 619055) B619055
theorem B1166561 : Blo 227813 1166561 := bstep (se 2 (by rfl) ⟨437460, by rfl⟩ : syracuseStep 1166561 = 874921) B874921
theorem B2608361 : Blo 227813 2608361 := bstep (se 2 (by rfl) ⟨978135, by rfl⟩ : syracuseStep 2608361 = 1956271) B1956271
theorem B576841 : Blo 227813 576841 := bstep (se 2 (by rfl) ⟨216315, by rfl⟩ : syracuseStep 576841 = 432631) B432631
theorem B773711 : Blo 227813 773711 := bstep (se 1 (by rfl) ⟨580283, by rfl⟩ : syracuseStep 773711 = 1160567) B1160567
theorem B3526507 : Blo 227813 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B1232765 : Blo 227813 1232765 := bstep (se 3 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 1232765 = 462287) B462287
theorem B1659113 : Blo 227813 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B51433865 : Blo 227813 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B2937383 : Blo 227813 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B414433 : Blo 227813 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B513287 : Blo 227813 513287 := bstep (se 1 (by rfl) ⟨384965, by rfl⟩ : syracuseStep 513287 = 769931) B769931
theorem B3954095 : Blo 227813 3954095 := bstep (se 1 (by rfl) ⟨2965571, by rfl⟩ : syracuseStep 3954095 = 5931143) B5931143
theorem B1103327 : Blo 227813 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B16570169 : Blo 227813 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B514025 : Blo 227813 514025 := bstep (se 2 (by rfl) ⟨192759, by rfl⟩ : syracuseStep 514025 = 385519) B385519
theorem B514169 : Blo 227813 514169 := bstep (se 2 (by rfl) ⟨192813, by rfl⟩ : syracuseStep 514169 = 385627) B385627
theorem B514223 : Blo 227813 514223 := bstep (se 1 (by rfl) ⟨385667, by rfl⟩ : syracuseStep 514223 = 771335) B771335
theorem B1169639 : Blo 227813 1169639 := bstep (se 1 (by rfl) ⟨877229, by rfl⟩ : syracuseStep 1169639 = 1754459) B1754459
theorem B1235359 : Blo 227813 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B514601 : Blo 227813 514601 := bstep (se 2 (by rfl) ⟨192975, by rfl⟩ : syracuseStep 514601 = 385951) B385951
theorem B514943 : Blo 227813 514943 := bstep (se 1 (by rfl) ⟨386207, by rfl⟩ : syracuseStep 514943 = 772415) B772415
theorem B14998445 : Blo 227813 14998445 := bstep (se 3 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 14998445 = 5624417) B5624417
theorem B515177 : Blo 227813 515177 := bstep (se 2 (by rfl) ⟨193191, by rfl⟩ : syracuseStep 515177 = 386383) B386383
theorem B580729 : Blo 227813 580729 := bstep (se 2 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 580729 = 435547) B435547
theorem B580891 : Blo 227813 580891 := bstep (se 1 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 580891 = 871337) B871337
theorem B515879 : Blo 227813 515879 := bstep (se 1 (by rfl) ⟨386909, by rfl⟩ : syracuseStep 515879 = 773819) B773819
theorem B548819 : Blo 227813 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B516167 : Blo 227813 516167 := bstep (se 1 (by rfl) ⟨387125, by rfl⟩ : syracuseStep 516167 = 774251) B774251
theorem B1302905 : Blo 227813 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B8446519 : Blo 227813 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B517175 : Blo 227813 517175 := bstep (se 1 (by rfl) ⟨387881, by rfl⟩ : syracuseStep 517175 = 775763) B775763
theorem B878111 : Blo 227813 878111 := bstep (se 1 (by rfl) ⟨658583, by rfl⟩ : syracuseStep 878111 = 1317167) B1317167
theorem B583271 : Blo 227813 583271 := bstep (se 1 (by rfl) ⟨437453, by rfl⟩ : syracuseStep 583271 = 874907) B874907
theorem B583433 : Blo 227813 583433 := bstep (se 2 (by rfl) ⟨218787, by rfl⟩ : syracuseStep 583433 = 437575) B437575
theorem B616319 : Blo 227813 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B649129 : Blo 227813 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B1304819 : Blo 227813 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B649721 : Blo 227813 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B256603 : Blo 227813 256603 := bstep (se 1 (by rfl) ⟨192452, by rfl⟩ : syracuseStep 256603 = 384905) B384905
theorem B584435 : Blo 227813 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B519263 : Blo 227813 519263 := bstep (se 1 (by rfl) ⟨389447, by rfl⟩ : syracuseStep 519263 = 778895) B778895
theorem B388327 : Blo 227813 388327 := bstep (se 1 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 388327 = 582491) B582491
theorem B9268465 : Blo 227813 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B519599 : Blo 227813 519599 := bstep (se 1 (by rfl) ⟨389699, by rfl⟩ : syracuseStep 519599 = 779399) B779399
theorem B618113 : Blo 227813 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B1240895 : Blo 227813 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B388975 : Blo 227813 388975 := bstep (se 1 (by rfl) ⟨291731, by rfl⟩ : syracuseStep 388975 = 583463) B583463
theorem B913319 : Blo 227813 913319 := bstep (se 1 (by rfl) ⟨684989, by rfl⟩ : syracuseStep 913319 = 1369979) B1369979
theorem B5009597 : Blo 227813 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B520505 : Blo 227813 520505 := bstep (se 2 (by rfl) ⟨195189, by rfl⟩ : syracuseStep 520505 = 390379) B390379
theorem B586217 : Blo 227813 586217 := bstep (se 2 (by rfl) ⟨219831, by rfl⟩ : syracuseStep 586217 = 439663) B439663
theorem B1962629 : Blo 227813 1962629 := bstep (se 4 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 1962629 = 367993) B367993
theorem B389839 : Blo 227813 389839 := bstep (se 1 (by rfl) ⟨292379, by rfl⟩ : syracuseStep 389839 = 584759) B584759
theorem B553961 : Blo 227813 553961 := bstep (se 2 (by rfl) ⟨207735, by rfl⟩ : syracuseStep 553961 = 415471) B415471
theorem B521423 : Blo 227813 521423 := bstep (se 1 (by rfl) ⟨391067, by rfl⟩ : syracuseStep 521423 = 782135) B782135
theorem B1668887 : Blo 227813 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B259879 : Blo 227813 259879 := bstep (se 1 (by rfl) ⟨194909, by rfl⟩ : syracuseStep 259879 = 389819) B389819
theorem B325567 : Blo 227813 325567 := bstep (se 1 (by rfl) ⟨244175, by rfl⟩ : syracuseStep 325567 = 488351) B488351
theorem B391135 : Blo 227813 391135 := bstep (se 1 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 391135 = 586703) B586703
theorem B260347 : Blo 227813 260347 := bstep (se 1 (by rfl) ⟨195260, by rfl⟩ : syracuseStep 260347 = 390521) B390521
theorem B620903 : Blo 227813 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B21133871 : Blo 227813 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B7928543 : Blo 227813 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B228347 : Blo 227813 228347 := bstep (se 1 (by rfl) ⟨171260, by rfl⟩ : syracuseStep 228347 = 342521) B342521
theorem B228591 : Blo 227813 228591 := bstep (se 1 (by rfl) ⟨171443, by rfl⟩ : syracuseStep 228591 = 342887) B342887
theorem B1899773 : Blo 227813 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B228635 : Blo 227813 228635 := bstep (se 1 (by rfl) ⟨171476, by rfl⟩ : syracuseStep 228635 = 342953) B342953
theorem B229023 : Blo 227813 229023 := bstep (se 1 (by rfl) ⟨171767, by rfl⟩ : syracuseStep 229023 = 343535) B343535
theorem B655087 : Blo 227813 655087 := bstep (se 1 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 655087 = 982631) B982631
theorem B229115 : Blo 227813 229115 := bstep (se 1 (by rfl) ⟨171836, by rfl⟩ : syracuseStep 229115 = 343673) B343673
theorem B229627 : Blo 227813 229627 := bstep (se 1 (by rfl) ⟨172220, by rfl⟩ : syracuseStep 229627 = 344441) B344441
theorem B229823 : Blo 227813 229823 := bstep (se 1 (by rfl) ⟨172367, by rfl⟩ : syracuseStep 229823 = 344735) B344735
theorem B229935 : Blo 227813 229935 := bstep (se 1 (by rfl) ⟨172451, by rfl⟩ : syracuseStep 229935 = 344903) B344903
theorem B1311653 : Blo 227813 1311653 := bstep (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) B245935
theorem B230383 : Blo 227813 230383 := bstep (se 1 (by rfl) ⟨172787, by rfl⟩ : syracuseStep 230383 = 345575) B345575
theorem B231167 : Blo 227813 231167 := bstep (se 1 (by rfl) ⟨173375, by rfl⟩ : syracuseStep 231167 = 346751) B346751
theorem B231295 : Blo 227813 231295 := bstep (se 1 (by rfl) ⟨173471, by rfl⟩ : syracuseStep 231295 = 346943) B346943
theorem B1738907 : Blo 227813 1738907 := bstep (se 1 (by rfl) ⟨1304180, by rfl⟩ : syracuseStep 1738907 = 2608361) B2608361
theorem B821843 : Blo 227813 821843 := bstep (se 1 (by rfl) ⟨616382, by rfl⟩ : syracuseStep 821843 = 1232765) B1232765
theorem B2493899 : Blo 227813 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B11046779 : Blo 227813 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B1315025 : Blo 227813 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B12357953 : Blo 227813 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B9998963 : Blo 227813 9998963 := bstep (se 1 (by rfl) ⟨7499222, by rfl⟩ : syracuseStep 9998963 = 14998445) B14998445
theorem B365879 : Blo 227813 365879 := bstep (se 1 (by rfl) ⟨274409, by rfl⟩ : syracuseStep 365879 = 548819) B548819
theorem B1972127 : Blo 227813 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B2955527 : Blo 227813 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B11147807 : Blo 227813 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B1121539 : Blo 227813 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B4988411 : Blo 227813 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B827263 : Blo 227813 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B434089 : Blo 227813 434089 := bstep (se 2 (by rfl) ⟨162783, by rfl⟩ : syracuseStep 434089 = 325567) B325567
theorem B1647145 : Blo 227813 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B369307 : Blo 227813 369307 := bstep (se 1 (by rfl) ⟨276980, by rfl⟩ : syracuseStep 369307 = 553961) B553961
theorem B5285695 : Blo 227813 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B4532203 : Blo 227813 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B5318939 : Blo 227813 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B469351 : Blo 227813 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B437089 : Blo 227813 437089 := bstep (se 2 (by rfl) ⟨163908, by rfl⟩ : syracuseStep 437089 = 327817) B327817
theorem B437339 : Blo 227813 437339 := bstep (se 1 (by rfl) ⟨328004, by rfl⟩ : syracuseStep 437339 = 656009) B656009
theorem B438889 : Blo 227813 438889 := bstep (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) B329167
theorem B275135 : Blo 227813 275135 := bstep (se 1 (by rfl) ⟨206351, by rfl⟩ : syracuseStep 275135 = 412703) B412703
theorem B865505 : Blo 227813 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B2602529 : Blo 227813 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B34289243 : Blo 227813 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B342137 : Blo 227813 342137 := bstep (se 2 (by rfl) ⟨128301, by rfl⟩ : syracuseStep 342137 = 256603) B256603
theorem B342191 : Blo 227813 342191 := bstep (se 1 (by rfl) ⟨256643, by rfl⟩ : syracuseStep 342191 = 513287) B513287
theorem B2636063 : Blo 227813 2636063 := bstep (se 1 (by rfl) ⟨1977047, by rfl⟩ : syracuseStep 2636063 = 3954095) B3954095
theorem B735551 : Blo 227813 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B342683 : Blo 227813 342683 := bstep (se 1 (by rfl) ⟨257012, by rfl⟩ : syracuseStep 342683 = 514025) B514025
theorem B342779 : Blo 227813 342779 := bstep (se 1 (by rfl) ⟨257084, by rfl⟩ : syracuseStep 342779 = 514169) B514169
theorem B342815 : Blo 227813 342815 := bstep (se 1 (by rfl) ⟨257111, by rfl⟩ : syracuseStep 342815 = 514223) B514223
theorem B2210647 : Blo 227813 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B343067 : Blo 227813 343067 := bstep (se 1 (by rfl) ⟨257300, by rfl⟩ : syracuseStep 343067 = 514601) B514601
theorem B37665881 : Blo 227813 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B769121 : Blo 227813 769121 := bstep (se 2 (by rfl) ⟨288420, by rfl⟩ : syracuseStep 769121 = 576841) B576841
theorem B244927 : Blo 227813 244927 := bstep (se 1 (by rfl) ⟨183695, by rfl⟩ : syracuseStep 244927 = 367391) B367391
theorem B6569201 : Blo 227813 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B343295 : Blo 227813 343295 := bstep (se 1 (by rfl) ⟨257471, by rfl⟩ : syracuseStep 343295 = 514943) B514943
theorem B343451 : Blo 227813 343451 := bstep (se 1 (by rfl) ⟨257588, by rfl⟩ : syracuseStep 343451 = 515177) B515177
theorem B4702009 : Blo 227813 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B343919 : Blo 227813 343919 := bstep (se 1 (by rfl) ⟨257939, by rfl⟩ : syracuseStep 343919 = 515879) B515879
theorem B344111 : Blo 227813 344111 := bstep (se 1 (by rfl) ⟨258083, by rfl⟩ : syracuseStep 344111 = 516167) B516167
theorem B868603 : Blo 227813 868603 := bstep (se 1 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 868603 = 1302905) B1302905
theorem B6832421 : Blo 227813 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B770471 : Blo 227813 770471 := bstep (se 1 (by rfl) ⟨577853, by rfl⟩ : syracuseStep 770471 = 1155707) B1155707
theorem B344783 : Blo 227813 344783 := bstep (se 1 (by rfl) ⟨258587, by rfl⟩ : syracuseStep 344783 = 517175) B517175
theorem B1655741 : Blo 227813 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B443369 : Blo 227813 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B410879 : Blo 227813 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B771551 : Blo 227813 771551 := bstep (se 1 (by rfl) ⟨578663, by rfl⟩ : syracuseStep 771551 = 1157327) B1157327
theorem B869879 : Blo 227813 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B346175 : Blo 227813 346175 := bstep (se 1 (by rfl) ⟨259631, by rfl⟩ : syracuseStep 346175 = 519263) B519263
theorem B346399 : Blo 227813 346399 := bstep (se 1 (by rfl) ⟨259799, by rfl⟩ : syracuseStep 346399 = 519599) B519599
theorem B346505 : Blo 227813 346505 := bstep (se 2 (by rfl) ⟨129939, by rfl⟩ : syracuseStep 346505 = 259879) B259879
theorem B412075 : Blo 227813 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B608879 : Blo 227813 608879 := bstep (se 1 (by rfl) ⟨456659, by rfl⟩ : syracuseStep 608879 = 913319) B913319
theorem B347003 : Blo 227813 347003 := bstep (se 1 (by rfl) ⟨260252, by rfl⟩ : syracuseStep 347003 = 520505) B520505
theorem B347129 : Blo 227813 347129 := bstep (se 2 (by rfl) ⟨130173, by rfl⟩ : syracuseStep 347129 = 260347) B260347
theorem B347615 : Blo 227813 347615 := bstep (se 1 (by rfl) ⟨260711, by rfl⟩ : syracuseStep 347615 = 521423) B521423
theorem B577115 : Blo 227813 577115 := bstep (se 1 (by rfl) ⟨432836, by rfl⟩ : syracuseStep 577115 = 865673) B865673
theorem B11194523 : Blo 227813 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B774305 : Blo 227813 774305 := bstep (se 2 (by rfl) ⟨290364, by rfl⟩ : syracuseStep 774305 = 580729) B580729
theorem B774359 : Blo 227813 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B774521 : Blo 227813 774521 := bstep (se 2 (by rfl) ⟨290445, by rfl⟩ : syracuseStep 774521 = 580891) B580891
theorem B6181541 : Blo 227813 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B578299 : Blo 227813 578299 := bstep (se 1 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 578299 = 867449) B867449
theorem B1299239 : Blo 227813 1299239 := bstep (se 1 (by rfl) ⟨974429, by rfl⟩ : syracuseStep 1299239 = 1948859) B1948859
theorem B1266515 : Blo 227813 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B873449 : Blo 227813 873449 := bstep (se 2 (by rfl) ⟨327543, by rfl⟩ : syracuseStep 873449 = 655087) B655087
theorem B1758347 : Blo 227813 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B1168991 : Blo 227813 1168991 := bstep (se 1 (by rfl) ⟨876743, by rfl⟩ : syracuseStep 1168991 = 1753487) B1753487
theorem B775871 : Blo 227813 775871 := bstep (se 1 (by rfl) ⟨581903, by rfl⟩ : syracuseStep 775871 = 1163807) B1163807
theorem B11262025 : Blo 227813 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B776735 : Blo 227813 776735 := bstep (se 1 (by rfl) ⟨582551, by rfl⟩ : syracuseStep 776735 = 1165103) B1165103
theorem B514655 : Blo 227813 514655 := bstep (se 1 (by rfl) ⟨385991, by rfl⟩ : syracuseStep 514655 = 771983) B771983
theorem B974105 : Blo 227813 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B581033 : Blo 227813 581033 := bstep (se 2 (by rfl) ⟨217887, by rfl⟩ : syracuseStep 581033 = 435775) B435775
theorem B777707 : Blo 227813 777707 := bstep (se 1 (by rfl) ⟨583280, by rfl⟩ : syracuseStep 777707 = 1166561) B1166561
theorem B515807 : Blo 227813 515807 := bstep (se 1 (by rfl) ⟨386855, by rfl⟩ : syracuseStep 515807 = 773711) B773711
theorem B1106075 : Blo 227813 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B1958255 : Blo 227813 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B877337 : Blo 227813 877337 := bstep (se 2 (by rfl) ⟨329001, by rfl⟩ : syracuseStep 877337 = 658003) B658003
theorem B877351 : Blo 227813 877351 := bstep (se 1 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 877351 = 1316027) B1316027
theorem B877871 : Blo 227813 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B779759 : Blo 227813 779759 := bstep (se 1 (by rfl) ⟨584819, by rfl⟩ : syracuseStep 779759 = 1169639) B1169639
theorem B517769 : Blo 227813 517769 := bstep (se 2 (by rfl) ⟨194163, by rfl⟩ : syracuseStep 517769 = 388327) B388327
theorem B1763129 : Blo 227813 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B518633 : Blo 227813 518633 := bstep (se 2 (by rfl) ⟨194487, by rfl⟩ : syracuseStep 518633 = 388975) B388975
theorem B7432793 : Blo 227813 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B1600823 : Blo 227813 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B519785 : Blo 227813 519785 := bstep (se 2 (by rfl) ⟨194919, by rfl⟩ : syracuseStep 519785 = 389839) B389839
theorem B552577 : Blo 227813 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B585407 : Blo 227813 585407 := bstep (se 1 (by rfl) ⟨439055, by rfl⟩ : syracuseStep 585407 = 878111) B878111
theorem B388847 : Blo 227813 388847 := bstep (se 1 (by rfl) ⟨291635, by rfl⟩ : syracuseStep 388847 = 583271) B583271
theorem B388955 : Blo 227813 388955 := bstep (se 1 (by rfl) ⟨291716, by rfl⟩ : syracuseStep 388955 = 583433) B583433
theorem B1732589 : Blo 227813 1732589 := bstep (se 3 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 1732589 = 649721) B649721
theorem B389623 : Blo 227813 389623 := bstep (se 1 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 389623 = 584435) B584435
theorem B521513 : Blo 227813 521513 := bstep (se 2 (by rfl) ⟨195567, by rfl⟩ : syracuseStep 521513 = 391135) B391135
theorem B3339731 : Blo 227813 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B390811 : Blo 227813 390811 := bstep (se 1 (by rfl) ⟨293108, by rfl⟩ : syracuseStep 390811 = 586217) B586217
theorem B1308419 : Blo 227813 1308419 := bstep (se 1 (by rfl) ⟨981314, by rfl⟩ : syracuseStep 1308419 = 1962629) B1962629
theorem B1406909 : Blo 227813 1406909 := bstep (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) B527591
theorem B1112591 : Blo 227813 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B228199 : Blo 227813 228199 := bstep (se 1 (by rfl) ⟨171149, by rfl⟩ : syracuseStep 228199 = 342299) B342299
theorem B228223 : Blo 227813 228223 := bstep (se 1 (by rfl) ⟨171167, by rfl⟩ : syracuseStep 228223 = 342335) B342335
theorem B14089247 : Blo 227813 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B228603 : Blo 227813 228603 := bstep (se 1 (by rfl) ⟨171452, by rfl⟩ : syracuseStep 228603 = 342905) B342905
theorem B229407 : Blo 227813 229407 := bstep (se 1 (by rfl) ⟨172055, by rfl⟩ : syracuseStep 229407 = 344111) B344111
theorem B4554947 : Blo 227813 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B2949533 : Blo 227813 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B229855 : Blo 227813 229855 := bstep (se 1 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 229855 = 344783) B344783
theorem B295579 : Blo 227813 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B2196193 : Blo 227813 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B492409 : Blo 227813 492409 := bstep (se 2 (by rfl) ⟨184653, by rfl⟩ : syracuseStep 492409 = 369307) B369307
theorem B230783 : Blo 227813 230783 := bstep (se 1 (by rfl) ⟨173087, by rfl⟩ : syracuseStep 230783 = 346175) B346175
theorem B231003 : Blo 227813 231003 := bstep (se 1 (by rfl) ⟨173252, by rfl⟩ : syracuseStep 231003 = 346505) B346505
theorem B231335 : Blo 227813 231335 := bstep (se 1 (by rfl) ⟨173501, by rfl⟩ : syracuseStep 231335 = 347003) B347003
theorem B231419 : Blo 227813 231419 := bstep (se 1 (by rfl) ⟨173564, by rfl⟩ : syracuseStep 231419 = 347129) B347129
theorem B231743 : Blo 227813 231743 := bstep (se 1 (by rfl) ⟨173807, by rfl⟩ : syracuseStep 231743 = 347615) B347615
theorem B7047593 : Blo 227813 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B625801 : Blo 227813 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B1314751 : Blo 227813 1314751 := bstep (se 1 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 1314751 = 1972127) B1972127
theorem B1970351 : Blo 227813 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B3545959 : Blo 227813 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B4955195 : Blo 227813 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B1155059 : Blo 227813 1155059 := bstep (se 1 (by rfl) ⟨866294, by rfl⟩ : syracuseStep 1155059 = 1732589) B1732589
theorem B15016033 : Blo 227813 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B25110587 : Blo 227813 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B6269345 : Blo 227813 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B1158137 : Blo 227813 1158137 := bstep (se 2 (by rfl) ⟨434301, by rfl⟩ : syracuseStep 1158137 = 868603) B868603
theorem B1159271 : Blo 227813 1159271 := bstep (se 1 (by rfl) ⟨869453, by rfl⟩ : syracuseStep 1159271 = 1738907) B1738907
theorem B1847461 : Blo 227813 1847461 := bstep (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) B346399
theorem B405919 : Blo 227813 405919 := bstep (se 1 (by rfl) ⟨304439, by rfl⟩ : syracuseStep 405919 = 608879) B608879
theorem B733693 : Blo 227813 733693 := bstep (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) B275135
theorem B6042937 : Blo 227813 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B8238635 : Blo 227813 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B6665975 : Blo 227813 6665975 := bstep (se 1 (by rfl) ⟨4999481, by rfl⟩ : syracuseStep 6665975 = 9998963) B9998963
theorem B866159 : Blo 227813 866159 := bstep (se 1 (by rfl) ⟨649619, by rfl⟩ : syracuseStep 866159 = 1299239) B1299239
theorem B1095677 : Blo 227813 1095677 := bstep (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) B410879
theorem B243919 : Blo 227813 243919 := bstep (se 1 (by rfl) ⟨182939, by rfl⟩ : syracuseStep 243919 = 365879) B365879
theorem B343103 : Blo 227813 343103 := bstep (se 1 (by rfl) ⟨257327, by rfl⟩ : syracuseStep 343103 = 514655) B514655
theorem B736769 : Blo 227813 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B3325607 : Blo 227813 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B343871 : Blo 227813 343871 := bstep (se 1 (by rfl) ⟨257903, by rfl⟩ : syracuseStep 343871 = 515807) B515807
theorem B771065 : Blo 227813 771065 := bstep (se 2 (by rfl) ⟨289149, by rfl⟩ : syracuseStep 771065 = 578299) B578299
theorem B345179 : Blo 227813 345179 := bstep (se 1 (by rfl) ⟨258884, by rfl⟩ : syracuseStep 345179 = 517769) B517769
theorem B345755 : Blo 227813 345755 := bstep (se 1 (by rfl) ⟨259316, by rfl⟩ : syracuseStep 345755 = 518633) B518633
theorem B1067215 : Blo 227813 1067215 := bstep (se 1 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 1067215 = 1600823) B1600823
theorem B346523 : Blo 227813 346523 := bstep (se 1 (by rfl) ⟨259892, by rfl⟩ : syracuseStep 346523 = 519785) B519785
theorem B1166237 : Blo 227813 1166237 := bstep (se 3 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 1166237 = 437339) B437339
theorem B577003 : Blo 227813 577003 := bstep (se 1 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 577003 = 865505) B865505
theorem B347675 : Blo 227813 347675 := bstep (se 1 (by rfl) ⟨260756, by rfl⟩ : syracuseStep 347675 = 521513) B521513
theorem B22859495 : Blo 227813 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B872279 : Blo 227813 872279 := bstep (se 1 (by rfl) ⟨654209, by rfl⟩ : syracuseStep 872279 = 1308419) B1308419
theorem B937939 : Blo 227813 937939 := bstep (se 1 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 937939 = 1406909) B1406909
theorem B1757375 : Blo 227813 1757375 := bstep (se 1 (by rfl) ⟨1318031, by rfl⟩ : syracuseStep 1757375 = 2636063) B2636063
theorem B1495385 : Blo 227813 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B741727 : Blo 227813 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B4412069 : Blo 227813 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B9392831 : Blo 227813 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B512747 : Blo 227813 512747 := bstep (se 1 (by rfl) ⟨384560, by rfl⟩ : syracuseStep 512747 = 769121) B769121
theorem B4379467 : Blo 227813 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B578785 : Blo 227813 578785 := bstep (se 2 (by rfl) ⟨217044, by rfl⟩ : syracuseStep 578785 = 434089) B434089
theorem B513647 : Blo 227813 513647 := bstep (se 1 (by rfl) ⟨385235, by rfl⟩ : syracuseStep 513647 = 770471) B770471
theorem B874435 : Blo 227813 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B1103827 : Blo 227813 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B514367 : Blo 227813 514367 := bstep (se 1 (by rfl) ⟨385775, by rfl⟩ : syracuseStep 514367 = 771551) B771551
theorem B579919 : Blo 227813 579919 := bstep (se 1 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 579919 = 869879) B869879
theorem B1169801 : Blo 227813 1169801 := bstep (se 2 (by rfl) ⟨438675, by rfl⟩ : syracuseStep 1169801 = 877351) B877351
theorem B547895 : Blo 227813 547895 := bstep (se 1 (by rfl) ⟨410921, by rfl⟩ : syracuseStep 547895 = 821843) B821843
theorem B1662599 : Blo 227813 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B384743 : Blo 227813 384743 := bstep (se 1 (by rfl) ⟨288557, by rfl⟩ : syracuseStep 384743 = 577115) B577115
theorem B7364519 : Blo 227813 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B7463015 : Blo 227813 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B516203 : Blo 227813 516203 := bstep (se 1 (by rfl) ⟨387152, by rfl⟩ : syracuseStep 516203 = 774305) B774305
theorem B876683 : Blo 227813 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B516239 : Blo 227813 516239 := bstep (se 1 (by rfl) ⟨387179, by rfl⟩ : syracuseStep 516239 = 774359) B774359
theorem B516347 : Blo 227813 516347 := bstep (se 1 (by rfl) ⟨387260, by rfl⟩ : syracuseStep 516347 = 774521) B774521
theorem B4121027 : Blo 227813 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B844343 : Blo 227813 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B549433 : Blo 227813 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B582299 : Blo 227813 582299 := bstep (se 1 (by rfl) ⟨436724, by rfl⟩ : syracuseStep 582299 = 873449) B873449
theorem B1172231 : Blo 227813 1172231 := bstep (se 1 (by rfl) ⟨879173, by rfl⟩ : syracuseStep 1172231 = 1758347) B1758347
theorem B779327 : Blo 227813 779327 := bstep (se 1 (by rfl) ⟨584495, by rfl⟩ : syracuseStep 779327 = 1168991) B1168991
theorem B517247 : Blo 227813 517247 := bstep (se 1 (by rfl) ⟨387935, by rfl⟩ : syracuseStep 517247 = 775871) B775871
theorem B582785 : Blo 227813 582785 := bstep (se 2 (by rfl) ⟨218544, by rfl⟩ : syracuseStep 582785 = 437089) B437089
theorem B7431871 : Blo 227813 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B517823 : Blo 227813 517823 := bstep (se 1 (by rfl) ⟨388367, by rfl⟩ : syracuseStep 517823 = 776735) B776735
theorem B649403 : Blo 227813 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B387355 : Blo 227813 387355 := bstep (se 1 (by rfl) ⟨290516, by rfl⟩ : syracuseStep 387355 = 581033) B581033
theorem B518471 : Blo 227813 518471 := bstep (se 1 (by rfl) ⟨388853, by rfl⟩ : syracuseStep 518471 = 777707) B777707
theorem B1305503 : Blo 227813 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B584891 : Blo 227813 584891 := bstep (se 1 (by rfl) ⟨438668, by rfl⟩ : syracuseStep 584891 = 877337) B877337
theorem B519497 : Blo 227813 519497 := bstep (se 2 (by rfl) ⟨194811, by rfl⟩ : syracuseStep 519497 = 389623) B389623
theorem B585185 : Blo 227813 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B585247 : Blo 227813 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B519839 : Blo 227813 519839 := bstep (se 1 (by rfl) ⟨389879, by rfl⟩ : syracuseStep 519839 = 779759) B779759
theorem B1306277 : Blo 227813 1306277 := bstep (se 4 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 1306277 = 244927) B244927
theorem B1175419 : Blo 227813 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B521081 : Blo 227813 521081 := bstep (se 2 (by rfl) ⟨195405, by rfl⟩ : syracuseStep 521081 = 390811) B390811
theorem B390271 : Blo 227813 390271 := bstep (se 1 (by rfl) ⟨292703, by rfl⟩ : syracuseStep 390271 = 585407) B585407
theorem B259231 : Blo 227813 259231 := bstep (se 1 (by rfl) ⟨194423, by rfl⟩ : syracuseStep 259231 = 388847) B388847
theorem B259303 : Blo 227813 259303 := bstep (se 1 (by rfl) ⟨194477, by rfl⟩ : syracuseStep 259303 = 388955) B388955
theorem B2226487 : Blo 227813 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B1735019 : Blo 227813 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B2947529 : Blo 227813 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B228091 : Blo 227813 228091 := bstep (se 1 (by rfl) ⟨171068, by rfl⟩ : syracuseStep 228091 = 342137) B342137
theorem B228127 : Blo 227813 228127 := bstep (se 1 (by rfl) ⟨171095, by rfl⟩ : syracuseStep 228127 = 342191) B342191
theorem B490367 : Blo 227813 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B228455 : Blo 227813 228455 := bstep (se 1 (by rfl) ⟨171341, by rfl⟩ : syracuseStep 228455 = 342683) B342683
theorem B228519 : Blo 227813 228519 := bstep (se 1 (by rfl) ⟨171389, by rfl⟩ : syracuseStep 228519 = 342779) B342779
theorem B228543 : Blo 227813 228543 := bstep (se 1 (by rfl) ⟨171407, by rfl⟩ : syracuseStep 228543 = 342815) B342815
theorem B228711 : Blo 227813 228711 := bstep (se 1 (by rfl) ⟨171533, by rfl⟩ : syracuseStep 228711 = 343067) B343067
theorem B228863 : Blo 227813 228863 := bstep (se 1 (by rfl) ⟨171647, by rfl⟩ : syracuseStep 228863 = 343295) B343295
theorem B228967 : Blo 227813 228967 := bstep (se 1 (by rfl) ⟨171725, by rfl⟩ : syracuseStep 228967 = 343451) B343451
theorem B229279 : Blo 227813 229279 := bstep (se 1 (by rfl) ⟨171959, by rfl⟩ : syracuseStep 229279 = 343919) B343919
theorem B20021377 : Blo 227813 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B1966355 : Blo 227813 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B230119 : Blo 227813 230119 := bstep (se 1 (by rfl) ⟨172589, by rfl⟩ : syracuseStep 230119 = 345179) B345179
theorem B230503 : Blo 227813 230503 := bstep (se 1 (by rfl) ⟨172877, by rfl⟩ : syracuseStep 230503 = 345755) B345755
theorem B656545 : Blo 227813 656545 := bstep (se 2 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 656545 = 492409) B492409
theorem B231015 : Blo 227813 231015 := bstep (se 1 (by rfl) ⟨173261, by rfl⟩ : syracuseStep 231015 = 346523) B346523
theorem B231783 : Blo 227813 231783 := bstep (se 1 (by rfl) ⟨173837, by rfl⟩ : syracuseStep 231783 = 347675) B347675
theorem B15239663 : Blo 227813 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B1313567 : Blo 227813 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B6261887 : Blo 227813 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B1576421 : Blo 227813 1576421 := bstep (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) B295579
theorem B1250585 : Blo 227813 1250585 := bstep (se 2 (by rfl) ⟨468969, by rfl⟩ : syracuseStep 1250585 = 937939) B937939
theorem B2463281 : Blo 227813 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B562895 : Blo 227813 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B988969 : Blo 227813 988969 := bstep (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) B741727
theorem B5839289 : Blo 227813 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B432935 : Blo 227813 432935 := bstep (se 1 (by rfl) ⟨324701, by rfl⟩ : syracuseStep 432935 = 649403) B649403
theorem B4727945 : Blo 227813 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B730451 : Blo 227813 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B1156679 : Blo 227813 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B732577 : Blo 227813 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B2928257 : Blo 227813 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B4698395 : Blo 227813 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B9909161 : Blo 227813 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B996923 : Blo 227813 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B1422953 : Blo 227813 1422953 := bstep (se 2 (by rfl) ⟨533607, by rfl⟩ : syracuseStep 1422953 = 1067215) B1067215
theorem B341831 : Blo 227813 341831 := bstep (se 1 (by rfl) ⟨256373, by rfl⟩ : syracuseStep 341831 = 512747) B512747
theorem B342431 : Blo 227813 342431 := bstep (se 1 (by rfl) ⟨256823, by rfl⟩ : syracuseStep 342431 = 513647) B513647
theorem B834401 : Blo 227813 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B342911 : Blo 227813 342911 := bstep (se 1 (by rfl) ⟨257183, by rfl⟩ : syracuseStep 342911 = 514367) B514367
theorem B769337 : Blo 227813 769337 := bstep (se 2 (by rfl) ⟨288501, by rfl⟩ : syracuseStep 769337 = 577003) B577003
theorem B1753001 : Blo 227813 1753001 := bstep (se 2 (by rfl) ⟨657375, by rfl⟩ : syracuseStep 1753001 = 1314751) B1314751
theorem B770039 : Blo 227813 770039 := bstep (se 1 (by rfl) ⟨577529, by rfl⟩ : syracuseStep 770039 = 1155059) B1155059
theorem B344135 : Blo 227813 344135 := bstep (se 1 (by rfl) ⟨258101, by rfl⟩ : syracuseStep 344135 = 516203) B516203
theorem B344159 : Blo 227813 344159 := bstep (se 1 (by rfl) ⟨258119, by rfl⟩ : syracuseStep 344159 = 516239) B516239
theorem B66961565 : Blo 227813 66961565 := bstep (se 3 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 66961565 = 25110587) B25110587
theorem B344231 : Blo 227813 344231 := bstep (se 1 (by rfl) ⟨258173, by rfl⟩ : syracuseStep 344231 = 516347) B516347
theorem B541225 : Blo 227813 541225 := bstep (se 2 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 541225 = 405919) B405919
theorem B344831 : Blo 227813 344831 := bstep (se 1 (by rfl) ⟨258623, by rfl⟩ : syracuseStep 344831 = 517247) B517247
theorem B345215 : Blo 227813 345215 := bstep (se 1 (by rfl) ⟨258911, by rfl⟩ : syracuseStep 345215 = 517823) B517823
theorem B345641 : Blo 227813 345641 := bstep (se 2 (by rfl) ⟨129615, by rfl⟩ : syracuseStep 345641 = 259231) B259231
theorem B345647 : Blo 227813 345647 := bstep (se 1 (by rfl) ⟨259235, by rfl⟩ : syracuseStep 345647 = 518471) B518471
theorem B4179563 : Blo 227813 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B771713 : Blo 227813 771713 := bstep (se 2 (by rfl) ⟨289392, by rfl⟩ : syracuseStep 771713 = 578785) B578785
theorem B345737 : Blo 227813 345737 := bstep (se 2 (by rfl) ⟨129651, by rfl⟩ : syracuseStep 345737 = 259303) B259303
theorem B870335 : Blo 227813 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B772091 : Blo 227813 772091 := bstep (se 1 (by rfl) ⟨579068, by rfl⟩ : syracuseStep 772091 = 1158137) B1158137
theorem B346331 : Blo 227813 346331 := bstep (se 1 (by rfl) ⟨259748, by rfl⟩ : syracuseStep 346331 = 519497) B519497
theorem B346559 : Blo 227813 346559 := bstep (se 1 (by rfl) ⟨259919, by rfl⟩ : syracuseStep 346559 = 519839) B519839
theorem B870851 : Blo 227813 870851 := bstep (se 1 (by rfl) ⟨653138, by rfl⟩ : syracuseStep 870851 = 1306277) B1306277
theorem B1165913 : Blo 227813 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B772847 : Blo 227813 772847 := bstep (se 1 (by rfl) ⟨579635, by rfl⟩ : syracuseStep 772847 = 1159271) B1159271
theorem B1461053 : Blo 227813 1461053 := bstep (se 3 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 1461053 = 547895) B547895
theorem B2968649 : Blo 227813 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B773225 : Blo 227813 773225 := bstep (se 2 (by rfl) ⟨289959, by rfl⟩ : syracuseStep 773225 = 579919) B579919
theorem B347387 : Blo 227813 347387 := bstep (se 1 (by rfl) ⟨260540, by rfl⟩ : syracuseStep 347387 = 521081) B521081
theorem B5492423 : Blo 227813 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B4443983 : Blo 227813 4443983 := bstep (se 1 (by rfl) ⟨3332987, by rfl⟩ : syracuseStep 4443983 = 6665975) B6665975
theorem B577439 : Blo 227813 577439 := bstep (se 1 (by rfl) ⟨433079, by rfl⟩ : syracuseStep 577439 = 866159) B866159
theorem B1560493 : Blo 227813 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B2217071 : Blo 227813 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B3036631 : Blo 227813 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B514043 : Blo 227813 514043 := bstep (se 1 (by rfl) ⟨385532, by rfl⟩ : syracuseStep 514043 = 771065) B771065
theorem B777491 : Blo 227813 777491 := bstep (se 1 (by rfl) ⟨583118, by rfl⟩ : syracuseStep 777491 = 1166237) B1166237
theorem B581519 : Blo 227813 581519 := bstep (se 1 (by rfl) ⟨436139, by rfl⟩ : syracuseStep 581519 = 872279) B872279
theorem B1171583 : Blo 227813 1171583 := bstep (se 1 (by rfl) ⟨878687, by rfl⟩ : syracuseStep 1171583 = 1757375) B1757375
theorem B516473 : Blo 227813 516473 := bstep (se 2 (by rfl) ⟨193677, by rfl⟩ : syracuseStep 516473 = 387355) B387355
theorem B2941379 : Blo 227813 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B779867 : Blo 227813 779867 := bstep (se 1 (by rfl) ⟨584900, by rfl⟩ : syracuseStep 779867 = 1169801) B1169801
theorem B3303463 : Blo 227813 3303463 := bstep (se 1 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 3303463 = 4955195) B4955195
theorem B780329 : Blo 227813 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B1108399 : Blo 227813 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B256495 : Blo 227813 256495 := bstep (se 1 (by rfl) ⟨192371, by rfl⟩ : syracuseStep 256495 = 384743) B384743
theorem B1567225 : Blo 227813 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B4909679 : Blo 227813 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B4975343 : Blo 227813 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B584455 : Blo 227813 584455 := bstep (se 1 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 584455 = 876683) B876683
theorem B2747351 : Blo 227813 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B388199 : Blo 227813 388199 := bstep (se 1 (by rfl) ⟨291149, by rfl⟩ : syracuseStep 388199 = 582299) B582299
theorem B781487 : Blo 227813 781487 := bstep (se 1 (by rfl) ⟨586115, by rfl⟩ : syracuseStep 781487 = 1172231) B1172231
theorem B978257 : Blo 227813 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B519551 : Blo 227813 519551 := bstep (se 1 (by rfl) ⟨389663, by rfl⟩ : syracuseStep 519551 = 779327) B779327
theorem B388523 : Blo 227813 388523 := bstep (se 1 (by rfl) ⟨291392, by rfl⟩ : syracuseStep 388523 = 582785) B582785
theorem B520361 : Blo 227813 520361 := bstep (se 2 (by rfl) ⟨195135, by rfl⟩ : syracuseStep 520361 = 390271) B390271
theorem B8057249 : Blo 227813 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B389927 : Blo 227813 389927 := bstep (se 1 (by rfl) ⟨292445, by rfl⟩ : syracuseStep 389927 = 584891) B584891
theorem B1471769 : Blo 227813 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B325225 : Blo 227813 325225 := bstep (se 2 (by rfl) ⟨121959, by rfl⟩ : syracuseStep 325225 = 243919) B243919
theorem B1965019 : Blo 227813 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B326911 : Blo 227813 326911 := bstep (se 1 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 326911 = 490367) B490367
theorem B228735 : Blo 227813 228735 := bstep (se 1 (by rfl) ⟨171551, by rfl⟩ : syracuseStep 228735 = 343103) B343103
theorem B491179 : Blo 227813 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B229247 : Blo 227813 229247 := bstep (se 1 (by rfl) ⟨171935, by rfl⟩ : syracuseStep 229247 = 343871) B343871
theorem B229423 : Blo 227813 229423 := bstep (se 1 (by rfl) ⟨172067, by rfl⟩ : syracuseStep 229423 = 344135) B344135
theorem B229439 : Blo 227813 229439 := bstep (se 1 (by rfl) ⟨172079, by rfl⟩ : syracuseStep 229439 = 344159) B344159
theorem B229487 : Blo 227813 229487 := bstep (se 1 (by rfl) ⟨172115, by rfl⟩ : syracuseStep 229487 = 344231) B344231
theorem B1310903 : Blo 227813 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B229887 : Blo 227813 229887 := bstep (se 1 (by rfl) ⟨172415, by rfl⟩ : syracuseStep 229887 = 344831) B344831
theorem B230143 : Blo 227813 230143 := bstep (se 1 (by rfl) ⟨172607, by rfl⟩ : syracuseStep 230143 = 345215) B345215
theorem B230427 : Blo 227813 230427 := bstep (se 1 (by rfl) ⟨172820, by rfl⟩ : syracuseStep 230427 = 345641) B345641
theorem B230431 : Blo 227813 230431 := bstep (se 1 (by rfl) ⟨172823, by rfl⟩ : syracuseStep 230431 = 345647) B345647
theorem B2786375 : Blo 227813 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B230491 : Blo 227813 230491 := bstep (se 1 (by rfl) ⟨172868, by rfl⟩ : syracuseStep 230491 = 345737) B345737
theorem B230887 : Blo 227813 230887 := bstep (se 1 (by rfl) ⟨173165, by rfl⟩ : syracuseStep 230887 = 346331) B346331
theorem B231039 : Blo 227813 231039 := bstep (se 1 (by rfl) ⟨173279, by rfl⟩ : syracuseStep 231039 = 346559) B346559
theorem B10159775 : Blo 227813 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B231591 : Blo 227813 231591 := bstep (se 1 (by rfl) ⟨173693, by rfl⟩ : syracuseStep 231591 = 347387) B347387
theorem B1050947 : Blo 227813 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B2886533 : Blo 227813 2886533 := bstep (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) B541225
theorem B1477865 : Blo 227813 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1478047 : Blo 227813 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B1642187 : Blo 227813 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B3151963 : Blo 227813 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B3316895 : Blo 227813 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B1318625 : Blo 227813 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B664615 : Blo 227813 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B435881 : Blo 227813 435881 := bstep (se 2 (by rfl) ⟨163455, by rfl⟩ : syracuseStep 435881 = 326911) B326911
theorem B44641043 : Blo 227813 44641043 := bstep (se 1 (by rfl) ⟨33480782, by rfl⟩ : syracuseStep 44641043 = 66961565) B66961565
theorem B1979099 : Blo 227813 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B4174591 : Blo 227813 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B2962655 : Blo 227813 2962655 := bstep (se 1 (by rfl) ⟨2221991, by rfl⟩ : syracuseStep 2962655 = 4443983) B4443983
theorem B4404617 : Blo 227813 4404617 := bstep (se 2 (by rfl) ⟨1651731, by rfl⟩ : syracuseStep 4404617 = 3303463) B3303463
theorem B341993 : Blo 227813 341993 := bstep (se 2 (by rfl) ⟨128247, by rfl⟩ : syracuseStep 341993 = 256495) B256495
theorem B833723 : Blo 227813 833723 := bstep (se 1 (by rfl) ⟨625292, by rfl⟩ : syracuseStep 833723 = 1250585) B1250585
theorem B375263 : Blo 227813 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B342695 : Blo 227813 342695 := bstep (se 1 (by rfl) ⟨257021, by rfl⟩ : syracuseStep 342695 = 514043) B514043
theorem B2080657 : Blo 227813 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B344315 : Blo 227813 344315 := bstep (se 1 (by rfl) ⟨258236, by rfl⟩ : syracuseStep 344315 = 516473) B516473
theorem B771119 : Blo 227813 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B4048841 : Blo 227813 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B346367 : Blo 227813 346367 := bstep (se 1 (by rfl) ⟨259775, by rfl⟩ : syracuseStep 346367 = 519551) B519551
theorem B1952171 : Blo 227813 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B346907 : Blo 227813 346907 := bstep (se 1 (by rfl) ⟨260180, by rfl⟩ : syracuseStep 346907 = 520361) B520361
theorem B3132263 : Blo 227813 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B6606107 : Blo 227813 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B512891 : Blo 227813 512891 := bstep (se 1 (by rfl) ⟨384668, by rfl⟩ : syracuseStep 512891 = 769337) B769337
theorem B1168667 : Blo 227813 1168667 := bstep (se 1 (by rfl) ⟨876500, by rfl⟩ : syracuseStep 1168667 = 1753001) B1753001
theorem B513359 : Blo 227813 513359 := bstep (se 1 (by rfl) ⟨385019, by rfl⟩ : syracuseStep 513359 = 770039) B770039
theorem B26695169 : Blo 227813 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B514475 : Blo 227813 514475 := bstep (se 1 (by rfl) ⟨385856, by rfl⟩ : syracuseStep 514475 = 771713) B771713
theorem B580223 : Blo 227813 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B514727 : Blo 227813 514727 := bstep (se 1 (by rfl) ⟨386045, by rfl⟩ : syracuseStep 514727 = 772091) B772091
theorem B875393 : Blo 227813 875393 := bstep (se 2 (by rfl) ⟨328272, by rfl⟩ : syracuseStep 875393 = 656545) B656545
theorem B580567 : Blo 227813 580567 := bstep (se 1 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 580567 = 870851) B870851
theorem B777275 : Blo 227813 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B515231 : Blo 227813 515231 := bstep (se 1 (by rfl) ⟨386423, by rfl⟩ : syracuseStep 515231 = 772847) B772847
theorem B875711 : Blo 227813 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B974035 : Blo 227813 974035 := bstep (se 1 (by rfl) ⟨730526, by rfl⟩ : syracuseStep 974035 = 1461053) B1461053
theorem B515483 : Blo 227813 515483 := bstep (se 1 (by rfl) ⟨386612, by rfl⟩ : syracuseStep 515483 = 773225) B773225
theorem B3661615 : Blo 227813 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B384959 : Blo 227813 384959 := bstep (se 1 (by rfl) ⟨288719, by rfl⟩ : syracuseStep 384959 = 577439) B577439
theorem B2089633 : Blo 227813 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B779273 : Blo 227813 779273 := bstep (se 2 (by rfl) ⟨292227, by rfl⟩ : syracuseStep 779273 = 584455) B584455
theorem B3892859 : Blo 227813 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B288623 : Blo 227813 288623 := bstep (se 1 (by rfl) ⟨216467, by rfl⟩ : syracuseStep 288623 = 432935) B432935
theorem B976769 : Blo 227813 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B518327 : Blo 227813 518327 := bstep (se 1 (by rfl) ⟨388745, by rfl⟩ : syracuseStep 518327 = 777491) B777491
theorem B387679 : Blo 227813 387679 := bstep (se 1 (by rfl) ⟨290759, by rfl⟩ : syracuseStep 387679 = 581519) B581519
theorem B781055 : Blo 227813 781055 := bstep (se 1 (by rfl) ⟨585791, by rfl⟩ : syracuseStep 781055 = 1171583) B1171583
theorem B1960919 : Blo 227813 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B486967 : Blo 227813 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B519911 : Blo 227813 519911 := bstep (se 1 (by rfl) ⟨389933, by rfl⟩ : syracuseStep 519911 = 779867) B779867
theorem B520219 : Blo 227813 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B3273119 : Blo 227813 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B1831567 : Blo 227813 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B258799 : Blo 227813 258799 := bstep (se 1 (by rfl) ⟨194099, by rfl⟩ : syracuseStep 258799 = 388199) B388199
theorem B520991 : Blo 227813 520991 := bstep (se 1 (by rfl) ⟨390743, by rfl⟩ : syracuseStep 520991 = 781487) B781487
theorem B652171 : Blo 227813 652171 := bstep (se 1 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 652171 = 978257) B978257
theorem B2225069 : Blo 227813 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B259015 : Blo 227813 259015 := bstep (se 1 (by rfl) ⟨194261, by rfl⟩ : syracuseStep 259015 = 388523) B388523
theorem B5371499 : Blo 227813 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B259951 : Blo 227813 259951 := bstep (se 1 (by rfl) ⟨194963, by rfl⟩ : syracuseStep 259951 = 389927) B389927
theorem B1734533 : Blo 227813 1734533 := bstep (se 4 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 1734533 = 325225) B325225
theorem B981179 : Blo 227813 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B948635 : Blo 227813 948635 := bstep (se 1 (by rfl) ⟨711476, by rfl⟩ : syracuseStep 948635 = 1422953) B1422953
theorem B227887 : Blo 227813 227887 := bstep (se 1 (by rfl) ⟨170915, by rfl⟩ : syracuseStep 227887 = 341831) B341831
theorem B2620025 : Blo 227813 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B228287 : Blo 227813 228287 := bstep (se 1 (by rfl) ⟨171215, by rfl⟩ : syracuseStep 228287 = 342431) B342431
theorem B228607 : Blo 227813 228607 := bstep (se 1 (by rfl) ⟨171455, by rfl⟩ : syracuseStep 228607 = 342911) B342911
theorem B654905 : Blo 227813 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B229543 : Blo 227813 229543 := bstep (se 1 (by rfl) ⟨172157, by rfl⟩ : syracuseStep 229543 = 344315) B344315
theorem B2786177 : Blo 227813 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B886153 : Blo 227813 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B230911 : Blo 227813 230911 := bstep (se 1 (by rfl) ⟨173183, by rfl⟩ : syracuseStep 230911 = 346367) B346367
theorem B231271 : Blo 227813 231271 := bstep (se 1 (by rfl) ⟨173453, by rfl⟩ : syracuseStep 231271 = 346907) B346907
theorem B17796779 : Blo 227813 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B1970729 : Blo 227813 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B693625 : Blo 227813 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B2595239 : Blo 227813 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B29760695 : Blo 227813 29760695 := bstep (se 1 (by rfl) ⟨22320521, by rfl⟩ : syracuseStep 29760695 = 44641043) B44641043
theorem B4202617 : Blo 227813 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B1319399 : Blo 227813 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B3940973 : Blo 227813 3940973 := bstep (se 3 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 3940973 = 1477865) B1477865
theorem B1483379 : Blo 227813 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B1975103 : Blo 227813 1975103 := bstep (se 1 (by rfl) ⟨1481327, by rfl⟩ : syracuseStep 1975103 = 2962655) B2962655
theorem B3580999 : Blo 227813 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B1156355 : Blo 227813 1156355 := bstep (se 1 (by rfl) ⟨867266, by rfl⟩ : syracuseStep 1156355 = 1734533) B1734533
theorem B632423 : Blo 227813 632423 := bstep (se 1 (by rfl) ⟨474317, by rfl⟩ : syracuseStep 632423 = 948635) B948635
theorem B1746683 : Blo 227813 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B436603 : Blo 227813 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B2699227 : Blo 227813 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B700631 : Blo 227813 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B4404071 : Blo 227813 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B1094791 : Blo 227813 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B341927 : Blo 227813 341927 := bstep (se 1 (by rfl) ⟨256445, by rfl⟩ : syracuseStep 341927 = 512891) B512891
theorem B342239 : Blo 227813 342239 := bstep (se 1 (by rfl) ⟨256679, by rfl⟩ : syracuseStep 342239 = 513359) B513359
theorem B342983 : Blo 227813 342983 := bstep (se 1 (by rfl) ⟨257237, by rfl⟩ : syracuseStep 342983 = 514475) B514475
theorem B1162349 : Blo 227813 1162349 := bstep (se 3 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 1162349 = 435881) B435881
theorem B343151 : Blo 227813 343151 := bstep (se 1 (by rfl) ⟨257363, by rfl⟩ : syracuseStep 343151 = 514727) B514727
theorem B343487 : Blo 227813 343487 := bstep (se 1 (by rfl) ⟨257615, by rfl⟩ : syracuseStep 343487 = 515231) B515231
theorem B2211263 : Blo 227813 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B343655 : Blo 227813 343655 := bstep (se 1 (by rfl) ⟨257741, by rfl⟩ : syracuseStep 343655 = 515483) B515483
theorem B769661 : Blo 227813 769661 := bstep (se 3 (by rfl) ⟨144311, by rfl⟩ : syracuseStep 769661 = 288623) B288623
theorem B2442089 : Blo 227813 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B345065 : Blo 227813 345065 := bstep (se 2 (by rfl) ⟨129399, by rfl⟩ : syracuseStep 345065 = 258799) B258799
theorem B869561 : Blo 227813 869561 := bstep (se 2 (by rfl) ⟨326085, by rfl⟩ : syracuseStep 869561 = 652171) B652171
theorem B345353 : Blo 227813 345353 := bstep (se 2 (by rfl) ⟨129507, by rfl⟩ : syracuseStep 345353 = 259015) B259015
theorem B345551 : Blo 227813 345551 := bstep (se 1 (by rfl) ⟨259163, by rfl⟩ : syracuseStep 345551 = 518327) B518327
theorem B346601 : Blo 227813 346601 := bstep (se 2 (by rfl) ⟨129975, by rfl⟩ : syracuseStep 346601 = 259951) B259951
theorem B346607 : Blo 227813 346607 := bstep (se 1 (by rfl) ⟨259955, by rfl⟩ : syracuseStep 346607 = 519911) B519911
theorem B2182079 : Blo 227813 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B347327 : Blo 227813 347327 := bstep (se 1 (by rfl) ⟨260495, by rfl⟩ : syracuseStep 347327 = 520991) B520991
theorem B2936411 : Blo 227813 2936411 := bstep (se 1 (by rfl) ⟨2202308, by rfl⟩ : syracuseStep 2936411 = 4404617) B4404617
theorem B774089 : Blo 227813 774089 := bstep (se 2 (by rfl) ⟨290283, by rfl⟩ : syracuseStep 774089 = 580567) B580567
theorem B1298713 : Blo 227813 1298713 := bstep (se 2 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 1298713 = 974035) B974035
theorem B250175 : Blo 227813 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B11096837 : Blo 227813 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B873935 : Blo 227813 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B514079 : Blo 227813 514079 := bstep (se 1 (by rfl) ⟨385559, by rfl⟩ : syracuseStep 514079 = 771119) B771119
theorem B1857583 : Blo 227813 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B6773183 : Blo 227813 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B1301447 : Blo 227813 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B2088175 : Blo 227813 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B1924355 : Blo 227813 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B516905 : Blo 227813 516905 := bstep (se 2 (by rfl) ⟨193839, by rfl⟩ : syracuseStep 516905 = 387679) B387679
theorem B779111 : Blo 227813 779111 := bstep (se 1 (by rfl) ⟨584333, by rfl⟩ : syracuseStep 779111 = 1168667) B1168667
theorem B386815 : Blo 227813 386815 := bstep (se 1 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 386815 = 580223) B580223
theorem B583595 : Blo 227813 583595 := bstep (se 1 (by rfl) ⟨437696, by rfl⟩ : syracuseStep 583595 = 875393) B875393
theorem B518183 : Blo 227813 518183 := bstep (se 1 (by rfl) ⟨388637, by rfl⟩ : syracuseStep 518183 = 777275) B777275
theorem B649289 : Blo 227813 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B583807 : Blo 227813 583807 := bstep (se 1 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 583807 = 875711) B875711
theorem B879083 : Blo 227813 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B256639 : Blo 227813 256639 := bstep (se 1 (by rfl) ⟨192479, by rfl⟩ : syracuseStep 256639 = 384959) B384959
theorem B519515 : Blo 227813 519515 := bstep (se 1 (by rfl) ⟨389636, by rfl⟩ : syracuseStep 519515 = 779273) B779273
theorem B5566121 : Blo 227813 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B651179 : Blo 227813 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B520703 : Blo 227813 520703 := bstep (se 1 (by rfl) ⟨390527, by rfl⟩ : syracuseStep 520703 = 781055) B781055
theorem B1307279 : Blo 227813 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B227995 : Blo 227813 227995 := bstep (se 1 (by rfl) ⟨170996, by rfl⟩ : syracuseStep 227995 = 341993) B341993
theorem B654119 : Blo 227813 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B555815 : Blo 227813 555815 := bstep (se 1 (by rfl) ⟨416861, by rfl⟩ : syracuseStep 555815 = 833723) B833723
theorem B19528613 : Blo 227813 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B228463 : Blo 227813 228463 := bstep (se 1 (by rfl) ⟨171347, by rfl⟩ : syracuseStep 228463 = 342695) B342695
theorem B5603489 : Blo 227813 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B230043 : Blo 227813 230043 := bstep (se 1 (by rfl) ⟨172532, by rfl⟩ : syracuseStep 230043 = 345065) B345065
theorem B230235 : Blo 227813 230235 := bstep (se 1 (by rfl) ⟨172676, by rfl⟩ : syracuseStep 230235 = 345353) B345353
theorem B230367 : Blo 227813 230367 := bstep (se 1 (by rfl) ⟨172775, by rfl⟩ : syracuseStep 230367 = 345551) B345551
theorem B231067 : Blo 227813 231067 := bstep (se 1 (by rfl) ⟨173300, by rfl⟩ : syracuseStep 231067 = 346601) B346601
theorem B231071 : Blo 227813 231071 := bstep (se 1 (by rfl) ⟨173303, by rfl⟩ : syracuseStep 231071 = 346607) B346607
theorem B1181537 : Blo 227813 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B231551 : Blo 227813 231551 := bstep (se 1 (by rfl) ⟨173663, by rfl⟩ : syracuseStep 231551 = 347327) B347327
theorem B11864519 : Blo 227813 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B1313819 : Blo 227813 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B2627315 : Blo 227813 2627315 := bstep (se 1 (by rfl) ⟨1970486, by rfl⟩ : syracuseStep 2627315 = 3940973) B3940973
theorem B988919 : Blo 227813 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B1316735 : Blo 227813 1316735 := bstep (se 1 (by rfl) ⟨987551, by rfl⟩ : syracuseStep 1316735 = 1975103) B1975103
theorem B432859 : Blo 227813 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B924833 : Blo 227813 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B3710747 : Blo 227813 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B467087 : Blo 227813 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B436079 : Blo 227813 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B370543 : Blo 227813 370543 := bstep (se 1 (by rfl) ⟨277907, by rfl⟩ : syracuseStep 370543 = 555815) B555815
theorem B13019075 : Blo 227813 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B14395877 : Blo 227813 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B667133 : Blo 227813 667133 := bstep (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) B250175
theorem B342185 : Blo 227813 342185 := bstep (se 2 (by rfl) ⟨128319, by rfl⟩ : syracuseStep 342185 = 256639) B256639
theorem B342719 : Blo 227813 342719 := bstep (se 1 (by rfl) ⟨257039, by rfl⟩ : syracuseStep 342719 = 514079) B514079
theorem B867631 : Blo 227813 867631 := bstep (se 1 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 867631 = 1301447) B1301447
theorem B19840463 : Blo 227813 19840463 := bstep (se 1 (by rfl) ⟨14880347, by rfl⟩ : syracuseStep 19840463 = 29760695) B29760695
theorem B344603 : Blo 227813 344603 := bstep (se 1 (by rfl) ⟨258452, by rfl⟩ : syracuseStep 344603 = 516905) B516905
theorem B770903 : Blo 227813 770903 := bstep (se 1 (by rfl) ⟨578177, by rfl⟩ : syracuseStep 770903 = 1156355) B1156355
theorem B1164455 : Blo 227813 1164455 := bstep (se 1 (by rfl) ⟨873341, by rfl⟩ : syracuseStep 1164455 = 1746683) B1746683
theorem B345455 : Blo 227813 345455 := bstep (se 1 (by rfl) ⟨259091, by rfl⟩ : syracuseStep 345455 = 518183) B518183
theorem B1459721 : Blo 227813 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B346343 : Blo 227813 346343 := bstep (se 1 (by rfl) ⟨259757, by rfl⟩ : syracuseStep 346343 = 519515) B519515
theorem B5818877 : Blo 227813 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B2476777 : Blo 227813 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B347135 : Blo 227813 347135 := bstep (se 1 (by rfl) ⟨260351, by rfl⟩ : syracuseStep 347135 = 520703) B520703
theorem B871519 : Blo 227813 871519 := bstep (se 1 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 871519 = 1307279) B1307279
theorem B2936047 : Blo 227813 2936047 := bstep (se 1 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 2936047 = 4404071) B4404071
theorem B5131613 : Blo 227813 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B774899 : Blo 227813 774899 := bstep (se 1 (by rfl) ⟨581174, by rfl⟩ : syracuseStep 774899 = 1162349) B1162349
theorem B513107 : Blo 227813 513107 := bstep (se 1 (by rfl) ⟨384830, by rfl⟩ : syracuseStep 513107 = 769661) B769661
theorem B1628059 : Blo 227813 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B1857451 : Blo 227813 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B579707 : Blo 227813 579707 := bstep (se 1 (by rfl) ⟨434780, by rfl⟩ : syracuseStep 579707 = 869561) B869561
theorem B515753 : Blo 227813 515753 := bstep (se 2 (by rfl) ⟨193407, by rfl⟩ : syracuseStep 515753 = 386815) B386815
theorem B1957607 : Blo 227813 1957607 := bstep (se 1 (by rfl) ⟨1468205, by rfl⟩ : syracuseStep 1957607 = 2936411) B2936411
theorem B516059 : Blo 227813 516059 := bstep (se 1 (by rfl) ⟨387044, by rfl⟩ : syracuseStep 516059 = 774089) B774089
theorem B778409 : Blo 227813 778409 := bstep (se 2 (by rfl) ⟨291903, by rfl⟩ : syracuseStep 778409 = 583807) B583807
theorem B582137 : Blo 227813 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B7397891 : Blo 227813 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B582623 : Blo 227813 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B1730159 : Blo 227813 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B4515455 : Blo 227813 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B879599 : Blo 227813 879599 := bstep (se 1 (by rfl) ⟨659699, by rfl⟩ : syracuseStep 879599 = 1319399) B1319399
theorem B1731617 : Blo 227813 1731617 := bstep (se 2 (by rfl) ⟨649356, by rfl⟩ : syracuseStep 1731617 = 1298713) B1298713
theorem B19098661 : Blo 227813 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B519407 : Blo 227813 519407 := bstep (se 1 (by rfl) ⟨389555, by rfl⟩ : syracuseStep 519407 = 779111) B779111
theorem B421615 : Blo 227813 421615 := bstep (se 1 (by rfl) ⟨316211, by rfl⟩ : syracuseStep 421615 = 632423) B632423
theorem B389063 : Blo 227813 389063 := bstep (se 1 (by rfl) ⟨291797, by rfl⟩ : syracuseStep 389063 = 583595) B583595
theorem B586055 : Blo 227813 586055 := bstep (se 1 (by rfl) ⟨439541, by rfl⟩ : syracuseStep 586055 = 879083) B879083
theorem B227951 : Blo 227813 227951 := bstep (se 1 (by rfl) ⟨170963, by rfl⟩ : syracuseStep 227951 = 341927) B341927
theorem B228159 : Blo 227813 228159 := bstep (se 1 (by rfl) ⟨171119, by rfl⟩ : syracuseStep 228159 = 342239) B342239
theorem B2784233 : Blo 227813 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B228655 : Blo 227813 228655 := bstep (se 1 (by rfl) ⟨171491, by rfl⟩ : syracuseStep 228655 = 342983) B342983
theorem B228767 : Blo 227813 228767 := bstep (se 1 (by rfl) ⟨171575, by rfl⟩ : syracuseStep 228767 = 343151) B343151
theorem B228991 : Blo 227813 228991 := bstep (se 1 (by rfl) ⟨171743, by rfl⟩ : syracuseStep 228991 = 343487) B343487
theorem B1474175 : Blo 227813 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B229103 : Blo 227813 229103 := bstep (se 1 (by rfl) ⟨171827, by rfl⟩ : syracuseStep 229103 = 343655) B343655
theorem B1736477 : Blo 227813 1736477 := bstep (se 3 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 1736477 = 651179) B651179
theorem B3735659 : Blo 227813 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B229735 : Blo 227813 229735 := bstep (se 1 (by rfl) ⟨172301, by rfl⟩ : syracuseStep 229735 = 344603) B344603
theorem B1245565 : Blo 227813 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B230303 : Blo 227813 230303 := bstep (se 1 (by rfl) ⟨172727, by rfl⟩ : syracuseStep 230303 = 345455) B345455
theorem B787691 : Blo 227813 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B230895 : Blo 227813 230895 := bstep (se 1 (by rfl) ⟨173171, by rfl⟩ : syracuseStep 230895 = 346343) B346343
theorem B231423 : Blo 227813 231423 := bstep (se 1 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 231423 = 347135) B347135
theorem B494057 : Blo 227813 494057 := bstep (se 2 (by rfl) ⟨185271, by rfl⟩ : syracuseStep 494057 = 370543) B370543
theorem B659279 : Blo 227813 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B25464881 : Blo 227813 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B562153 : Blo 227813 562153 := bstep (se 2 (by rfl) ⟨210807, by rfl⟩ : syracuseStep 562153 = 421615) B421615
theorem B1153439 : Blo 227813 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B1154411 : Blo 227813 1154411 := bstep (se 1 (by rfl) ⟨865808, by rfl⟩ : syracuseStep 1154411 = 1731617) B1731617
theorem B2170745 : Blo 227813 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B1156841 : Blo 227813 1156841 := bstep (se 2 (by rfl) ⟨433815, by rfl⟩ : syracuseStep 1156841 = 867631) B867631
theorem B1157651 : Blo 227813 1157651 := bstep (se 1 (by rfl) ⟨868238, by rfl⟩ : syracuseStep 1157651 = 1736477) B1736477
theorem B7909679 : Blo 227813 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B3879251 : Blo 227813 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B342071 : Blo 227813 342071 := bstep (se 1 (by rfl) ⟨256553, by rfl⟩ : syracuseStep 342071 = 513107) B513107
theorem B1751543 : Blo 227813 1751543 := bstep (se 1 (by rfl) ⟨1313657, by rfl⟩ : syracuseStep 1751543 = 2627315) B2627315
theorem B1162025 : Blo 227813 1162025 := bstep (se 2 (by rfl) ⟨435759, by rfl⟩ : syracuseStep 1162025 = 871519) B871519
theorem B3914729 : Blo 227813 3914729 := bstep (se 2 (by rfl) ⟨1468023, by rfl⟩ : syracuseStep 3914729 = 2936047) B2936047
theorem B343835 : Blo 227813 343835 := bstep (se 1 (by rfl) ⟨257876, by rfl⟩ : syracuseStep 343835 = 515753) B515753
theorem B2473831 : Blo 227813 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B344039 : Blo 227813 344039 := bstep (se 1 (by rfl) ⟨258029, by rfl⟩ : syracuseStep 344039 = 516059) B516059
theorem B4931927 : Blo 227813 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B346271 : Blo 227813 346271 := bstep (se 1 (by rfl) ⟨259703, by rfl⟩ : syracuseStep 346271 = 519407) B519407
theorem B444755 : Blo 227813 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B2476601 : Blo 227813 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B13684301 : Blo 227813 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B577145 : Blo 227813 577145 := bstep (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) B432859
theorem B1856155 : Blo 227813 1856155 := bstep (se 1 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 1856155 = 2784233) B2784233
theorem B13226975 : Blo 227813 13226975 := bstep (se 1 (by rfl) ⟨9920231, by rfl⟩ : syracuseStep 13226975 = 19840463) B19840463
theorem B513935 : Blo 227813 513935 := bstep (se 1 (by rfl) ⟨385451, by rfl⟩ : syracuseStep 513935 = 770903) B770903
theorem B776303 : Blo 227813 776303 := bstep (se 1 (by rfl) ⟨582227, by rfl⟩ : syracuseStep 776303 = 1164455) B1164455
theorem B973147 : Blo 227813 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B875879 : Blo 227813 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B516599 : Blo 227813 516599 := bstep (se 1 (by rfl) ⟨387449, by rfl⟩ : syracuseStep 516599 = 774899) B774899
theorem B3302369 : Blo 227813 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B877823 : Blo 227813 877823 := bstep (se 1 (by rfl) ⟨658367, by rfl⟩ : syracuseStep 877823 = 1316735) B1316735
theorem B386471 : Blo 227813 386471 := bstep (se 1 (by rfl) ⟨289853, by rfl⟩ : syracuseStep 386471 = 579707) B579707
theorem B616555 : Blo 227813 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B1305071 : Blo 227813 1305071 := bstep (se 1 (by rfl) ⟨978803, by rfl⟩ : syracuseStep 1305071 = 1957607) B1957607
theorem B518939 : Blo 227813 518939 := bstep (se 1 (by rfl) ⟨389204, by rfl⟩ : syracuseStep 518939 = 778409) B778409
theorem B388091 : Blo 227813 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B388415 : Blo 227813 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B3010303 : Blo 227813 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B290719 : Blo 227813 290719 := bstep (se 1 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 290719 = 436079) B436079
theorem B8679383 : Blo 227813 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B9597251 : Blo 227813 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B586399 : Blo 227813 586399 := bstep (se 1 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 586399 = 879599) B879599
theorem B259375 : Blo 227813 259375 := bstep (se 1 (by rfl) ⟨194531, by rfl⟩ : syracuseStep 259375 = 389063) B389063
theorem B390703 : Blo 227813 390703 := bstep (se 1 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 390703 = 586055) B586055
theorem B228123 : Blo 227813 228123 := bstep (se 1 (by rfl) ⟨171092, by rfl⟩ : syracuseStep 228123 = 342185) B342185
theorem B228479 : Blo 227813 228479 := bstep (se 1 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 228479 = 342719) B342719
theorem B982783 : Blo 227813 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B2490439 : Blo 227813 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B525127 : Blo 227813 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B25592669 : Blo 227813 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B230847 : Blo 227813 230847 := bstep (se 1 (by rfl) ⟨173135, by rfl⟩ : syracuseStep 230847 = 346271) B346271
theorem B296503 : Blo 227813 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B16976587 : Blo 227813 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B822073 : Blo 227813 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B8817983 : Blo 227813 8817983 := bstep (se 1 (by rfl) ⟨6613487, by rfl⟩ : syracuseStep 8817983 = 13226975) B13226975
theorem B1447163 : Blo 227813 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B2201579 : Blo 227813 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B1317485 : Blo 227813 1317485 := bstep (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) B494057
theorem B3287951 : Blo 227813 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B1651067 : Blo 227813 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B9122867 : Blo 227813 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B439519 : Blo 227813 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B342623 : Blo 227813 342623 := bstep (se 1 (by rfl) ⟨256967, by rfl⟩ : syracuseStep 342623 = 513935) B513935
theorem B768959 : Blo 227813 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B769607 : Blo 227813 769607 := bstep (se 1 (by rfl) ⟨577205, by rfl⟩ : syracuseStep 769607 = 1154411) B1154411
theorem B344399 : Blo 227813 344399 := bstep (se 1 (by rfl) ⟨258299, by rfl⟩ : syracuseStep 344399 = 516599) B516599
theorem B2474873 : Blo 227813 2474873 := bstep (se 2 (by rfl) ⟨928077, by rfl⟩ : syracuseStep 2474873 = 1856155) B1856155
theorem B771227 : Blo 227813 771227 := bstep (se 1 (by rfl) ⟨578420, by rfl⟩ : syracuseStep 771227 = 1156841) B1156841
theorem B870047 : Blo 227813 870047 := bstep (se 1 (by rfl) ⟨652535, by rfl⟩ : syracuseStep 870047 = 1305071) B1305071
theorem B771767 : Blo 227813 771767 := bstep (se 1 (by rfl) ⟨578825, by rfl⟩ : syracuseStep 771767 = 1157651) B1157651
theorem B345833 : Blo 227813 345833 := bstep (se 2 (by rfl) ⟨129687, by rfl⟩ : syracuseStep 345833 = 259375) B259375
theorem B345959 : Blo 227813 345959 := bstep (se 1 (by rfl) ⟨259469, by rfl⟩ : syracuseStep 345959 = 518939) B518939
theorem B5786255 : Blo 227813 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B1297529 : Blo 227813 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B1167695 : Blo 227813 1167695 := bstep (se 1 (by rfl) ⟨875771, by rfl⟩ : syracuseStep 1167695 = 1751543) B1751543
theorem B774683 : Blo 227813 774683 := bstep (se 1 (by rfl) ⟨581012, by rfl⟩ : syracuseStep 774683 = 1162025) B1162025
theorem B2609819 : Blo 227813 2609819 := bstep (se 1 (by rfl) ⟨1957364, by rfl⟩ : syracuseStep 2609819 = 3914729) B3914729
theorem B3298441 : Blo 227813 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B1660753 : Blo 227813 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B384763 : Blo 227813 384763 := bstep (se 1 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 384763 = 577145) B577145
theorem B517535 : Blo 227813 517535 := bstep (se 1 (by rfl) ⟨388151, by rfl⟩ : syracuseStep 517535 = 776303) B776303
theorem B583919 : Blo 227813 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B387625 : Blo 227813 387625 := bstep (se 2 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 387625 = 290719) B290719
theorem B585215 : Blo 227813 585215 := bstep (se 1 (by rfl) ⟨438911, by rfl⟩ : syracuseStep 585215 = 877823) B877823
theorem B781865 : Blo 227813 781865 := bstep (se 2 (by rfl) ⟨293199, by rfl⟩ : syracuseStep 781865 = 586399) B586399
theorem B257647 : Blo 227813 257647 := bstep (se 1 (by rfl) ⟨193235, by rfl⟩ : syracuseStep 257647 = 386471) B386471
theorem B749537 : Blo 227813 749537 := bstep (se 2 (by rfl) ⟨281076, by rfl⟩ : syracuseStep 749537 = 562153) B562153
theorem B258727 : Blo 227813 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B520937 : Blo 227813 520937 := bstep (se 2 (by rfl) ⟨195351, by rfl⟩ : syracuseStep 520937 = 390703) B390703
theorem B258943 : Blo 227813 258943 := bstep (se 1 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 258943 = 388415) B388415
theorem B5273119 : Blo 227813 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B2586167 : Blo 227813 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B16054949 : Blo 227813 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B228047 : Blo 227813 228047 := bstep (se 1 (by rfl) ⟨171035, by rfl⟩ : syracuseStep 228047 = 342071) B342071
theorem B1310377 : Blo 227813 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B229223 : Blo 227813 229223 := bstep (se 1 (by rfl) ⟨171917, by rfl⟩ : syracuseStep 229223 = 343835) B343835
theorem B229359 : Blo 227813 229359 := bstep (se 1 (by rfl) ⟨172019, by rfl⟩ : syracuseStep 229359 = 344039) B344039
theorem B229599 : Blo 227813 229599 := bstep (se 1 (by rfl) ⟨172199, by rfl⟩ : syracuseStep 229599 = 344399) B344399
theorem B6325397 : Blo 227813 6325397 := bstep (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) B296503
theorem B230555 : Blo 227813 230555 := bstep (se 1 (by rfl) ⟨172916, by rfl⟩ : syracuseStep 230555 = 345833) B345833
theorem B230639 : Blo 227813 230639 := bstep (se 1 (by rfl) ⟨172979, by rfl⟩ : syracuseStep 230639 = 345959) B345959
theorem B1739879 : Blo 227813 1739879 := bstep (se 1 (by rfl) ⟨1304909, by rfl⟩ : syracuseStep 1739879 = 2609819) B2609819
theorem B4397921 : Blo 227813 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B499691 : Blo 227813 499691 := bstep (se 1 (by rfl) ⟨374768, by rfl⟩ : syracuseStep 499691 = 749537) B749537
theorem B28123301 : Blo 227813 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B8857349 : Blo 227813 8857349 := bstep (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) B1660753
theorem B1747169 : Blo 227813 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B3320585 : Blo 227813 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B1649915 : Blo 227813 1649915 := bstep (se 1 (by rfl) ⟨1237436, by rfl⟩ : syracuseStep 1649915 = 2474873) B2474873
theorem B700169 : Blo 227813 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B865019 : Blo 227813 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B5878655 : Blo 227813 5878655 := bstep (se 1 (by rfl) ⟨4408991, by rfl⟩ : syracuseStep 5878655 = 8817983) B8817983
theorem B964775 : Blo 227813 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B1096097 : Blo 227813 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B343529 : Blo 227813 343529 := bstep (se 2 (by rfl) ⟨128823, by rfl⟩ : syracuseStep 343529 = 257647) B257647
theorem B344969 : Blo 227813 344969 := bstep (se 2 (by rfl) ⟨129363, by rfl⟩ : syracuseStep 344969 = 258727) B258727
theorem B345023 : Blo 227813 345023 := bstep (se 1 (by rfl) ⟨258767, by rfl⟩ : syracuseStep 345023 = 517535) B517535
theorem B345257 : Blo 227813 345257 := bstep (se 2 (by rfl) ⟨129471, by rfl⟩ : syracuseStep 345257 = 258943) B258943
theorem B1100711 : Blo 227813 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B347291 : Blo 227813 347291 := bstep (se 1 (by rfl) ⟨260468, by rfl⟩ : syracuseStep 347291 = 520937) B520937
theorem B6081911 : Blo 227813 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B1724111 : Blo 227813 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B10703299 : Blo 227813 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B512639 : Blo 227813 512639 := bstep (se 1 (by rfl) ⟨384479, by rfl⟩ : syracuseStep 512639 = 768959) B768959
theorem B513017 : Blo 227813 513017 := bstep (se 2 (by rfl) ⟨192381, by rfl⟩ : syracuseStep 513017 = 384763) B384763
theorem B513071 : Blo 227813 513071 := bstep (se 1 (by rfl) ⟨384803, by rfl⟩ : syracuseStep 513071 = 769607) B769607
theorem B17061779 : Blo 227813 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B514151 : Blo 227813 514151 := bstep (se 1 (by rfl) ⟨385613, by rfl⟩ : syracuseStep 514151 = 771227) B771227
theorem B580031 : Blo 227813 580031 := bstep (se 1 (by rfl) ⟨435023, by rfl⟩ : syracuseStep 580031 = 870047) B870047
theorem B514511 : Blo 227813 514511 := bstep (se 1 (by rfl) ⟨385883, by rfl⟩ : syracuseStep 514511 = 771767) B771767
theorem B3857503 : Blo 227813 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B778463 : Blo 227813 778463 := bstep (se 1 (by rfl) ⟨583847, by rfl⟩ : syracuseStep 778463 = 1167695) B1167695
theorem B516455 : Blo 227813 516455 := bstep (se 1 (by rfl) ⟨387341, by rfl⟩ : syracuseStep 516455 = 774683) B774683
theorem B516833 : Blo 227813 516833 := bstep (se 2 (by rfl) ⟨193812, by rfl⟩ : syracuseStep 516833 = 387625) B387625
theorem B22635449 : Blo 227813 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B1467719 : Blo 227813 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B878323 : Blo 227813 878323 := bstep (se 1 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 878323 = 1317485) B1317485
theorem B389279 : Blo 227813 389279 := bstep (se 1 (by rfl) ⟨291959, by rfl⟩ : syracuseStep 389279 = 583919) B583919
theorem B586025 : Blo 227813 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B2191967 : Blo 227813 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B390143 : Blo 227813 390143 := bstep (se 1 (by rfl) ⟨292607, by rfl⟩ : syracuseStep 390143 = 585215) B585215
theorem B521243 : Blo 227813 521243 := bstep (se 1 (by rfl) ⟨390932, by rfl⟩ : syracuseStep 521243 = 781865) B781865
theorem B228415 : Blo 227813 228415 := bstep (se 1 (by rfl) ⟨171311, by rfl⟩ : syracuseStep 228415 = 342623) B342623
theorem B229979 : Blo 227813 229979 := bstep (se 1 (by rfl) ⟨172484, by rfl⟩ : syracuseStep 229979 = 344969) B344969
theorem B230015 : Blo 227813 230015 := bstep (se 1 (by rfl) ⟨172511, by rfl⟩ : syracuseStep 230015 = 345023) B345023
theorem B230171 : Blo 227813 230171 := bstep (se 1 (by rfl) ⟨172628, by rfl⟩ : syracuseStep 230171 = 345257) B345257
theorem B231527 : Blo 227813 231527 := bstep (se 1 (by rfl) ⟨173645, by rfl⟩ : syracuseStep 231527 = 347291) B347291
theorem B1149407 : Blo 227813 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B11374519 : Blo 227813 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B333127 : Blo 227813 333127 := bstep (se 1 (by rfl) ⟨249845, by rfl⟩ : syracuseStep 333127 = 499691) B499691
theorem B18748867 : Blo 227813 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B2922925 : Blo 227813 2922925 := bstep (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) B1096097
theorem B5904899 : Blo 227813 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B733807 : Blo 227813 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B1159919 : Blo 227813 1159919 := bstep (se 1 (by rfl) ⟨869939, by rfl⟩ : syracuseStep 1159919 = 1739879) B1739879
theorem B341759 : Blo 227813 341759 := bstep (se 1 (by rfl) ⟨256319, by rfl⟩ : syracuseStep 341759 = 512639) B512639
theorem B342011 : Blo 227813 342011 := bstep (se 1 (by rfl) ⟨256508, by rfl⟩ : syracuseStep 342011 = 513017) B513017
theorem B342047 : Blo 227813 342047 := bstep (se 1 (by rfl) ⟨256535, by rfl⟩ : syracuseStep 342047 = 513071) B513071
theorem B342767 : Blo 227813 342767 := bstep (se 1 (by rfl) ⟨257075, by rfl⟩ : syracuseStep 342767 = 514151) B514151
theorem B343007 : Blo 227813 343007 := bstep (se 1 (by rfl) ⟨257255, by rfl⟩ : syracuseStep 343007 = 514511) B514511
theorem B2931947 : Blo 227813 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B344303 : Blo 227813 344303 := bstep (se 1 (by rfl) ⟨258227, by rfl⟩ : syracuseStep 344303 = 516455) B516455
theorem B344555 : Blo 227813 344555 := bstep (se 1 (by rfl) ⟨258416, by rfl⟩ : syracuseStep 344555 = 516833) B516833
theorem B14271065 : Blo 227813 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B15090299 : Blo 227813 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B1164779 : Blo 227813 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B2213723 : Blo 227813 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B1099943 : Blo 227813 1099943 := bstep (se 1 (by rfl) ⟨824957, by rfl⟩ : syracuseStep 1099943 = 1649915) B1649915
theorem B1461311 : Blo 227813 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B576679 : Blo 227813 576679 := bstep (se 1 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 576679 = 865019) B865019
theorem B3919103 : Blo 227813 3919103 := bstep (se 1 (by rfl) ⟨2939327, by rfl⟩ : syracuseStep 3919103 = 5878655) B5878655
theorem B347495 : Blo 227813 347495 := bstep (se 1 (by rfl) ⟨260621, by rfl⟩ : syracuseStep 347495 = 521243) B521243
theorem B643183 : Blo 227813 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B4216931 : Blo 227813 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B4054607 : Blo 227813 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B1171097 : Blo 227813 1171097 := bstep (se 2 (by rfl) ⟨439161, by rfl⟩ : syracuseStep 1171097 = 878323) B878323
theorem B386687 : Blo 227813 386687 := bstep (se 1 (by rfl) ⟨290015, by rfl⟩ : syracuseStep 386687 = 580031) B580031
theorem B518975 : Blo 227813 518975 := bstep (se 1 (by rfl) ⟨389231, by rfl⟩ : syracuseStep 518975 = 778463) B778463
theorem B978479 : Blo 227813 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B7468469 : Blo 227813 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B259519 : Blo 227813 259519 := bstep (se 1 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 259519 = 389279) B389279
theorem B390683 : Blo 227813 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B260095 : Blo 227813 260095 := bstep (se 1 (by rfl) ⟨195071, by rfl⟩ : syracuseStep 260095 = 390143) B390143
theorem B5143337 : Blo 227813 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B229019 : Blo 227813 229019 := bstep (se 1 (by rfl) ⟨171764, by rfl⟩ : syracuseStep 229019 = 343529) B343529
theorem B229535 : Blo 227813 229535 := bstep (se 1 (by rfl) ⟨172151, by rfl⟩ : syracuseStep 229535 = 344303) B344303
theorem B229703 : Blo 227813 229703 := bstep (se 1 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 229703 = 344555) B344555
theorem B10060199 : Blo 227813 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B1475815 : Blo 227813 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B231663 : Blo 227813 231663 := bstep (se 1 (by rfl) ⟨173747, by rfl⟩ : syracuseStep 231663 = 347495) B347495
theorem B3936599 : Blo 227813 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B9514043 : Blo 227813 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B733295 : Blo 227813 733295 := bstep (se 1 (by rfl) ⟨549971, by rfl⟩ : syracuseStep 733295 = 1099943) B1099943
theorem B766271 : Blo 227813 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B768905 : Blo 227813 768905 := bstep (se 2 (by rfl) ⟨288339, by rfl⟩ : syracuseStep 768905 = 576679) B576679
theorem B2703071 : Blo 227813 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B444169 : Blo 227813 444169 := bstep (se 2 (by rfl) ⟨166563, by rfl⟩ : syracuseStep 444169 = 333127) B333127
theorem B345983 : Blo 227813 345983 := bstep (se 1 (by rfl) ⟨259487, by rfl⟩ : syracuseStep 345983 = 518975) B518975
theorem B346025 : Blo 227813 346025 := bstep (se 2 (by rfl) ⟨129759, by rfl⟩ : syracuseStep 346025 = 259519) B259519
theorem B346793 : Blo 227813 346793 := bstep (se 2 (by rfl) ⟨130047, by rfl⟩ : syracuseStep 346793 = 260095) B260095
theorem B773279 : Blo 227813 773279 := bstep (se 1 (by rfl) ⟨579959, by rfl⟩ : syracuseStep 773279 = 1159919) B1159919
theorem B3428891 : Blo 227813 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B1954631 : Blo 227813 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B776519 : Blo 227813 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B974207 : Blo 227813 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B2612735 : Blo 227813 2612735 := bstep (se 1 (by rfl) ⟨1959551, by rfl⟩ : syracuseStep 2612735 = 3919103) B3919103
theorem B13721237 : Blo 227813 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B2811287 : Blo 227813 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B780731 : Blo 227813 780731 := bstep (se 1 (by rfl) ⟨585548, by rfl⟩ : syracuseStep 780731 = 1171097) B1171097
theorem B15166025 : Blo 227813 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B978409 : Blo 227813 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B257791 : Blo 227813 257791 := bstep (se 1 (by rfl) ⟨193343, by rfl⟩ : syracuseStep 257791 = 386687) B386687
theorem B24998489 : Blo 227813 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B652319 : Blo 227813 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B3897233 : Blo 227813 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B4978979 : Blo 227813 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B260455 : Blo 227813 260455 := bstep (se 1 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 260455 = 390683) B390683
theorem B227839 : Blo 227813 227839 := bstep (se 1 (by rfl) ⟨170879, by rfl⟩ : syracuseStep 227839 = 341759) B341759
theorem B228007 : Blo 227813 228007 := bstep (se 1 (by rfl) ⟨171005, by rfl⟩ : syracuseStep 228007 = 342011) B342011
theorem B228031 : Blo 227813 228031 := bstep (se 1 (by rfl) ⟨171023, by rfl⟩ : syracuseStep 228031 = 342047) B342047
theorem B228511 : Blo 227813 228511 := bstep (se 1 (by rfl) ⟨171383, by rfl⟩ : syracuseStep 228511 = 342767) B342767
theorem B228671 : Blo 227813 228671 := bstep (se 1 (by rfl) ⟨171503, by rfl⟩ : syracuseStep 228671 = 343007) B343007
theorem B230655 : Blo 227813 230655 := bstep (se 1 (by rfl) ⟨172991, by rfl⟩ : syracuseStep 230655 = 345983) B345983
theorem B230683 : Blo 227813 230683 := bstep (se 1 (by rfl) ⟨173012, by rfl⟩ : syracuseStep 230683 = 346025) B346025
theorem B1967753 : Blo 227813 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B231195 : Blo 227813 231195 := bstep (se 1 (by rfl) ⟨173396, by rfl⟩ : syracuseStep 231195 = 346793) B346793
theorem B2624399 : Blo 227813 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B1741823 : Blo 227813 1741823 := bstep (se 1 (by rfl) ⟨1306367, by rfl⟩ : syracuseStep 1741823 = 2612735) B2612735
theorem B9147491 : Blo 227813 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B1874191 : Blo 227813 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B434879 : Blo 227813 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B2598155 : Blo 227813 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B2368901 : Blo 227813 2368901 := bstep (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) B444169
theorem B3319319 : Blo 227813 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2043389 : Blo 227813 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B343721 : Blo 227813 343721 := bstep (se 2 (by rfl) ⟨128895, by rfl⟩ : syracuseStep 343721 = 257791) B257791
theorem B10110683 : Blo 227813 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B6342695 : Blo 227813 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B16665659 : Blo 227813 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B347273 : Blo 227813 347273 := bstep (se 2 (by rfl) ⟨130227, by rfl⟩ : syracuseStep 347273 = 260455) B260455
theorem B512603 : Blo 227813 512603 := bstep (se 1 (by rfl) ⟨384452, by rfl⟩ : syracuseStep 512603 = 768905) B768905
theorem B6706799 : Blo 227813 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B515519 : Blo 227813 515519 := bstep (se 1 (by rfl) ⟨386639, by rfl⟩ : syracuseStep 515519 = 773279) B773279
theorem B2285927 : Blo 227813 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B1303087 : Blo 227813 1303087 := bstep (se 1 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 1303087 = 1954631) B1954631
theorem B517679 : Blo 227813 517679 := bstep (se 1 (by rfl) ⟨388259, by rfl⟩ : syracuseStep 517679 = 776519) B776519
theorem B1304545 : Blo 227813 1304545 := bstep (se 2 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 1304545 = 978409) B978409
theorem B649471 : Blo 227813 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B520487 : Blo 227813 520487 := bstep (se 1 (by rfl) ⟨390365, by rfl⟩ : syracuseStep 520487 = 780731) B780731
theorem B488863 : Blo 227813 488863 := bstep (se 1 (by rfl) ⟨366647, by rfl⟩ : syracuseStep 488863 = 733295) B733295
theorem B1802047 : Blo 227813 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B1737449 : Blo 227813 1737449 := bstep (se 2 (by rfl) ⟨651543, by rfl⟩ : syracuseStep 1737449 = 1303087) B1303087
theorem B1311835 : Blo 227813 1311835 := bstep (se 1 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 1311835 = 1967753) B1967753
theorem B4228463 : Blo 227813 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B11110439 : Blo 227813 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B231515 : Blo 227813 231515 := bstep (se 1 (by rfl) ⟨173636, by rfl⟩ : syracuseStep 231515 = 347273) B347273
theorem B1739393 : Blo 227813 1739393 := bstep (se 2 (by rfl) ⟨652272, by rfl⟩ : syracuseStep 1739393 = 1304545) B1304545
theorem B6098327 : Blo 227813 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B1579267 : Blo 227813 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B2498921 : Blo 227813 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B5449037 : Blo 227813 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B2402729 : Blo 227813 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B1749599 : Blo 227813 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B865961 : Blo 227813 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B341735 : Blo 227813 341735 := bstep (se 1 (by rfl) ⟨256301, by rfl⟩ : syracuseStep 341735 = 512603) B512603
theorem B1161215 : Blo 227813 1161215 := bstep (se 1 (by rfl) ⟨870911, by rfl⟩ : syracuseStep 1161215 = 1741823) B1741823
theorem B4471199 : Blo 227813 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B343679 : Blo 227813 343679 := bstep (se 1 (by rfl) ⟨257759, by rfl⟩ : syracuseStep 343679 = 515519) B515519
theorem B1523951 : Blo 227813 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B2212879 : Blo 227813 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B345119 : Blo 227813 345119 := bstep (se 1 (by rfl) ⟨258839, by rfl⟩ : syracuseStep 345119 = 517679) B517679
theorem B346991 : Blo 227813 346991 := bstep (se 1 (by rfl) ⟨260243, by rfl⟩ : syracuseStep 346991 = 520487) B520487
theorem B6740455 : Blo 227813 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B289919 : Blo 227813 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B1732103 : Blo 227813 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B651817 : Blo 227813 651817 := bstep (se 2 (by rfl) ⟨244431, by rfl⟩ : syracuseStep 651817 = 488863) B488863
theorem B229147 : Blo 227813 229147 := bstep (se 1 (by rfl) ⟨171860, by rfl⟩ : syracuseStep 229147 = 343721) B343721
theorem B1015967 : Blo 227813 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B230079 : Blo 227813 230079 := bstep (se 1 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 230079 = 345119) B345119
theorem B2818975 : Blo 227813 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B2950505 : Blo 227813 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B7406959 : Blo 227813 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B231327 : Blo 227813 231327 := bstep (se 1 (by rfl) ⟨173495, by rfl⟩ : syracuseStep 231327 = 346991) B346991
theorem B4065551 : Blo 227813 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B1154735 : Blo 227813 1154735 := bstep (se 1 (by rfl) ⟨866051, by rfl⟩ : syracuseStep 1154735 = 1732103) B1732103
theorem B2105689 : Blo 227813 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B8987273 : Blo 227813 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B1158299 : Blo 227813 1158299 := bstep (se 1 (by rfl) ⟨868724, by rfl⟩ : syracuseStep 1158299 = 1737449) B1737449
theorem B1749113 : Blo 227813 1749113 := bstep (se 2 (by rfl) ⟨655917, by rfl⟩ : syracuseStep 1749113 = 1311835) B1311835
theorem B1159595 : Blo 227813 1159595 := bstep (se 1 (by rfl) ⟨869696, by rfl⟩ : syracuseStep 1159595 = 1739393) B1739393
theorem B14530765 : Blo 227813 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B869089 : Blo 227813 869089 := bstep (se 2 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 869089 = 651817) B651817
theorem B773117 : Blo 227813 773117 := bstep (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) B289919
theorem B1166399 : Blo 227813 1166399 := bstep (se 1 (by rfl) ⟨874799, by rfl⟩ : syracuseStep 1166399 = 1749599) B1749599
theorem B577307 : Blo 227813 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B774143 : Blo 227813 774143 := bstep (se 1 (by rfl) ⟨580607, by rfl⟩ : syracuseStep 774143 = 1161215) B1161215
theorem B1665947 : Blo 227813 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B1601819 : Blo 227813 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B227823 : Blo 227813 227823 := bstep (se 1 (by rfl) ⟨170867, by rfl⟩ : syracuseStep 227823 = 341735) B341735
theorem B2980799 : Blo 227813 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B229119 : Blo 227813 229119 := bstep (se 1 (by rfl) ⟨171839, by rfl⟩ : syracuseStep 229119 = 343679) B343679
theorem B1967003 : Blo 227813 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B19374353 : Blo 227813 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B1158785 : Blo 227813 1158785 := bstep (se 2 (by rfl) ⟨434544, by rfl⟩ : syracuseStep 1158785 = 869089) B869089
theorem B9875945 : Blo 227813 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B769823 : Blo 227813 769823 := bstep (se 1 (by rfl) ⟨577367, by rfl⟩ : syracuseStep 769823 = 1154735) B1154735
theorem B772199 : Blo 227813 772199 := bstep (se 1 (by rfl) ⟨579149, by rfl⟩ : syracuseStep 772199 = 1158299) B1158299
theorem B1166075 : Blo 227813 1166075 := bstep (se 1 (by rfl) ⟨874556, by rfl⟩ : syracuseStep 1166075 = 1749113) B1749113
theorem B1067879 : Blo 227813 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B773063 : Blo 227813 773063 := bstep (se 1 (by rfl) ⟨579797, by rfl⟩ : syracuseStep 773063 = 1159595) B1159595
theorem B1987199 : Blo 227813 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B2709245 : Blo 227813 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B2807585 : Blo 227813 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B3758633 : Blo 227813 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B2710367 : Blo 227813 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B515411 : Blo 227813 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B777599 : Blo 227813 777599 := bstep (se 1 (by rfl) ⟨583199, by rfl⟩ : syracuseStep 777599 = 1166399) B1166399
theorem B384871 : Blo 227813 384871 := bstep (se 1 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 384871 = 577307) B577307
theorem B516095 : Blo 227813 516095 := bstep (se 1 (by rfl) ⟨387071, by rfl⟩ : syracuseStep 516095 = 774143) B774143
theorem B5991515 : Blo 227813 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B1110631 : Blo 227813 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B1311335 : Blo 227813 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B1871723 : Blo 227813 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B1806911 : Blo 227813 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B12916235 : Blo 227813 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B1480841 : Blo 227813 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B1324799 : Blo 227813 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B2505755 : Blo 227813 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B7224653 : Blo 227813 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B343607 : Blo 227813 343607 := bstep (se 1 (by rfl) ⟨257705, by rfl⟩ : syracuseStep 343607 = 515411) B515411
theorem B344063 : Blo 227813 344063 := bstep (se 1 (by rfl) ⟨258047, by rfl⟩ : syracuseStep 344063 = 516095) B516095
theorem B772523 : Blo 227813 772523 := bstep (se 1 (by rfl) ⟨579392, by rfl⟩ : syracuseStep 772523 = 1158785) B1158785
theorem B513161 : Blo 227813 513161 := bstep (se 2 (by rfl) ⟨192435, by rfl⟩ : syracuseStep 513161 = 384871) B384871
theorem B513215 : Blo 227813 513215 := bstep (se 1 (by rfl) ⟨384911, by rfl⟩ : syracuseStep 513215 = 769823) B769823
theorem B514799 : Blo 227813 514799 := bstep (se 1 (by rfl) ⟨386099, by rfl⟩ : syracuseStep 514799 = 772199) B772199
theorem B777383 : Blo 227813 777383 := bstep (se 1 (by rfl) ⟨583037, by rfl⟩ : syracuseStep 777383 = 1166075) B1166075
theorem B711919 : Blo 227813 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B515375 : Blo 227813 515375 := bstep (se 1 (by rfl) ⟨386531, by rfl⟩ : syracuseStep 515375 = 773063) B773063
theorem B518399 : Blo 227813 518399 := bstep (se 1 (by rfl) ⟨388799, by rfl⟩ : syracuseStep 518399 = 777599) B777599
theorem B3994343 : Blo 227813 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B6583963 : Blo 227813 6583963 := bstep (se 1 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 6583963 = 9875945) B9875945
theorem B1247815 : Blo 227813 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B987227 : Blo 227813 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B2662895 : Blo 227813 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B342107 : Blo 227813 342107 := bstep (se 1 (by rfl) ⟨256580, by rfl⟩ : syracuseStep 342107 = 513161) B513161
theorem B342143 : Blo 227813 342143 := bstep (se 1 (by rfl) ⟨256607, by rfl⟩ : syracuseStep 342143 = 513215) B513215
theorem B343199 : Blo 227813 343199 := bstep (se 1 (by rfl) ⟨257399, by rfl⟩ : syracuseStep 343199 = 514799) B514799
theorem B343583 : Blo 227813 343583 := bstep (se 1 (by rfl) ⟨257687, by rfl⟩ : syracuseStep 343583 = 515375) B515375
theorem B345599 : Blo 227813 345599 := bstep (se 1 (by rfl) ⟨259199, by rfl⟩ : syracuseStep 345599 = 518399) B518399
theorem B874223 : Blo 227813 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B515015 : Blo 227813 515015 := bstep (se 1 (by rfl) ⟨386261, by rfl⟩ : syracuseStep 515015 = 772523) B772523
theorem B1204607 : Blo 227813 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B8610823 : Blo 227813 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B518255 : Blo 227813 518255 := bstep (se 1 (by rfl) ⟨388691, by rfl⟩ : syracuseStep 518255 = 777383) B777383
theorem B8778617 : Blo 227813 8778617 := bstep (se 2 (by rfl) ⟨3291981, by rfl⟩ : syracuseStep 8778617 = 6583963) B6583963
theorem B883199 : Blo 227813 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B949225 : Blo 227813 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B1670503 : Blo 227813 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B4816435 : Blo 227813 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B229071 : Blo 227813 229071 := bstep (se 1 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 229071 = 343607) B343607
theorem B229375 : Blo 227813 229375 := bstep (se 1 (by rfl) ⟨172031, by rfl⟩ : syracuseStep 229375 = 344063) B344063
theorem B230399 : Blo 227813 230399 := bstep (se 1 (by rfl) ⟨172799, by rfl⟩ : syracuseStep 230399 = 345599) B345599
theorem B658151 : Blo 227813 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B11481097 : Blo 227813 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B343343 : Blo 227813 343343 := bstep (se 1 (by rfl) ⟨257507, by rfl⟩ : syracuseStep 343343 = 515015) B515015
theorem B803071 : Blo 227813 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B345503 : Blo 227813 345503 := bstep (se 1 (by rfl) ⟨259127, by rfl⟩ : syracuseStep 345503 = 518255) B518255
theorem B5852411 : Blo 227813 5852411 := bstep (se 1 (by rfl) ⟨4389308, by rfl⟩ : syracuseStep 5852411 = 8778617) B8778617
theorem B1265633 : Blo 227813 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B7101053 : Blo 227813 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B1663753 : Blo 227813 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B582815 : Blo 227813 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B228071 : Blo 227813 228071 := bstep (se 1 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 228071 = 342107) B342107
theorem B228095 : Blo 227813 228095 := bstep (se 1 (by rfl) ⟨171071, by rfl⟩ : syracuseStep 228095 = 342143) B342143
theorem B588799 : Blo 227813 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B2227337 : Blo 227813 2227337 := bstep (se 2 (by rfl) ⟨835251, by rfl⟩ : syracuseStep 2227337 = 1670503) B1670503
theorem B6421913 : Blo 227813 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B228799 : Blo 227813 228799 := bstep (se 1 (by rfl) ⟨171599, by rfl⟩ : syracuseStep 228799 = 343199) B343199
theorem B229055 : Blo 227813 229055 := bstep (se 1 (by rfl) ⟨171791, by rfl⟩ : syracuseStep 229055 = 343583) B343583
theorem B230335 : Blo 227813 230335 := bstep (se 1 (by rfl) ⟨172751, by rfl⟩ : syracuseStep 230335 = 345503) B345503
theorem B3901607 : Blo 227813 3901607 := bstep (se 1 (by rfl) ⟨2926205, by rfl⟩ : syracuseStep 3901607 = 5852411) B5852411
theorem B15308129 : Blo 227813 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B1484891 : Blo 227813 1484891 := bstep (se 1 (by rfl) ⟨1113668, by rfl⟩ : syracuseStep 1484891 = 2227337) B2227337
theorem B438767 : Blo 227813 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B4734035 : Blo 227813 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B4281275 : Blo 227813 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B1070761 : Blo 227813 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B2218337 : Blo 227813 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B843755 : Blo 227813 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B388543 : Blo 227813 388543 := bstep (se 1 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 388543 = 582815) B582815
theorem B785065 : Blo 227813 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B228895 : Blo 227813 228895 := bstep (se 1 (by rfl) ⟨171671, by rfl⟩ : syracuseStep 228895 = 343343) B343343
theorem B1478891 : Blo 227813 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B989927 : Blo 227813 989927 := bstep (se 1 (by rfl) ⟨742445, by rfl⟩ : syracuseStep 989927 = 1484891) B1484891
theorem B3156023 : Blo 227813 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B2601071 : Blo 227813 2601071 := bstep (se 1 (by rfl) ⟨1950803, by rfl⟩ : syracuseStep 2601071 = 3901607) B3901607
theorem B11416733 : Blo 227813 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B1427681 : Blo 227813 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B2250013 : Blo 227813 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B40821677 : Blo 227813 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B518057 : Blo 227813 518057 := bstep (se 2 (by rfl) ⟨194271, by rfl⟩ : syracuseStep 518057 = 388543) B388543
theorem B292511 : Blo 227813 292511 := bstep (se 1 (by rfl) ⟨219383, by rfl⟩ : syracuseStep 292511 = 438767) B438767
theorem B1046753 : Blo 227813 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B951787 : Blo 227813 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B985927 : Blo 227813 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B659951 : Blo 227813 659951 := bstep (se 1 (by rfl) ⟨494963, by rfl⟩ : syracuseStep 659951 = 989927) B989927
theorem B2104015 : Blo 227813 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B7611155 : Blo 227813 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B697835 : Blo 227813 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B27214451 : Blo 227813 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B345371 : Blo 227813 345371 := bstep (se 1 (by rfl) ⟨259028, by rfl⟩ : syracuseStep 345371 = 518057) B518057
theorem B3000017 : Blo 227813 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B780029 : Blo 227813 780029 := bstep (se 3 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 780029 = 292511) B292511
theorem B1734047 : Blo 227813 1734047 := bstep (se 1 (by rfl) ⟨1300535, by rfl⟩ : syracuseStep 1734047 = 2601071) B2601071
theorem B230247 : Blo 227813 230247 := bstep (se 1 (by rfl) ⟨172685, by rfl⟩ : syracuseStep 230247 = 345371) B345371
theorem B1314569 : Blo 227813 1314569 := bstep (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) B985927
theorem B8000045 : Blo 227813 8000045 := bstep (se 3 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 8000045 = 3000017) B3000017
theorem B1156031 : Blo 227813 1156031 := bstep (se 1 (by rfl) ⟨867023, by rfl⟩ : syracuseStep 1156031 = 1734047) B1734047
theorem B439967 : Blo 227813 439967 := bstep (se 1 (by rfl) ⟨329975, by rfl⟩ : syracuseStep 439967 = 659951) B659951
theorem B2805353 : Blo 227813 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B18142967 : Blo 227813 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B1269049 : Blo 227813 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B1860893 : Blo 227813 1860893 := bstep (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) B697835
theorem B5074103 : Blo 227813 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B520019 : Blo 227813 520019 := bstep (se 1 (by rfl) ⟨390014, by rfl⟩ : syracuseStep 520019 = 780029) B780029
theorem B1870235 : Blo 227813 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B3382735 : Blo 227813 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B48381245 : Blo 227813 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B770687 : Blo 227813 770687 := bstep (se 1 (by rfl) ⟨578015, by rfl⟩ : syracuseStep 770687 = 1156031) B1156031
theorem B346679 : Blo 227813 346679 := bstep (se 1 (by rfl) ⟨260009, by rfl⟩ : syracuseStep 346679 = 520019) B520019
theorem B1692065 : Blo 227813 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B876379 : Blo 227813 876379 := bstep (se 1 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 876379 = 1314569) B1314569
theorem B5333363 : Blo 227813 5333363 := bstep (se 1 (by rfl) ⟨4000022, by rfl⟩ : syracuseStep 5333363 = 8000045) B8000045
theorem B1240595 : Blo 227813 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B293311 : Blo 227813 293311 := bstep (se 1 (by rfl) ⟨219983, by rfl⟩ : syracuseStep 293311 = 439967) B439967
theorem B1246823 : Blo 227813 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B231119 : Blo 227813 231119 := bstep (se 1 (by rfl) ⟨173339, by rfl⟩ : syracuseStep 231119 = 346679) B346679
theorem B827063 : Blo 227813 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B32254163 : Blo 227813 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B1128043 : Blo 227813 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B3555575 : Blo 227813 3555575 := bstep (se 1 (by rfl) ⟨2666681, by rfl⟩ : syracuseStep 3555575 = 5333363) B5333363
theorem B4510313 : Blo 227813 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B1168505 : Blo 227813 1168505 := bstep (se 2 (by rfl) ⟨438189, by rfl⟩ : syracuseStep 1168505 = 876379) B876379
theorem B513791 : Blo 227813 513791 := bstep (se 1 (by rfl) ⟨385343, by rfl⟩ : syracuseStep 513791 = 770687) B770687
theorem B391081 : Blo 227813 391081 := bstep (se 2 (by rfl) ⟨146655, by rfl⟩ : syracuseStep 391081 = 293311) B293311
theorem B21502775 : Blo 227813 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B2370383 : Blo 227813 2370383 := bstep (se 1 (by rfl) ⟨1777787, by rfl⟩ : syracuseStep 2370383 = 3555575) B3555575
theorem B831215 : Blo 227813 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B342527 : Blo 227813 342527 := bstep (se 1 (by rfl) ⟨256895, by rfl⟩ : syracuseStep 342527 = 513791) B513791
theorem B3006875 : Blo 227813 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B779003 : Blo 227813 779003 := bstep (se 1 (by rfl) ⟨584252, by rfl⟩ : syracuseStep 779003 = 1168505) B1168505
theorem B551375 : Blo 227813 551375 := bstep (se 1 (by rfl) ⟨413531, by rfl⟩ : syracuseStep 551375 = 827063) B827063
theorem B1504057 : Blo 227813 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B521441 : Blo 227813 521441 := bstep (se 2 (by rfl) ⟨195540, by rfl⟩ : syracuseStep 521441 = 391081) B391081
theorem B2004583 : Blo 227813 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B2005409 : Blo 227813 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B367583 : Blo 227813 367583 := bstep (se 1 (by rfl) ⟨275687, by rfl⟩ : syracuseStep 367583 = 551375) B551375
theorem B1580255 : Blo 227813 1580255 := bstep (se 1 (by rfl) ⟨1185191, by rfl⟩ : syracuseStep 1580255 = 2370383) B2370383
theorem B14335183 : Blo 227813 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B347627 : Blo 227813 347627 := bstep (se 1 (by rfl) ⟨260720, by rfl⟩ : syracuseStep 347627 = 521441) B521441
theorem B519335 : Blo 227813 519335 := bstep (se 1 (by rfl) ⟨389501, by rfl⟩ : syracuseStep 519335 = 779003) B779003
theorem B554143 : Blo 227813 554143 := bstep (se 1 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 554143 = 831215) B831215
theorem B228351 : Blo 227813 228351 := bstep (se 1 (by rfl) ⟨171263, by rfl⟩ : syracuseStep 228351 = 342527) B342527
theorem B231751 : Blo 227813 231751 := bstep (se 1 (by rfl) ⟨173813, by rfl⟩ : syracuseStep 231751 = 347627) B347627
theorem B1053503 : Blo 227813 1053503 := bstep (se 1 (by rfl) ⟨790127, by rfl⟩ : syracuseStep 1053503 = 1580255) B1580255
theorem B5347757 : Blo 227813 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B19113577 : Blo 227813 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B738857 : Blo 227813 738857 := bstep (se 2 (by rfl) ⟨277071, by rfl⟩ : syracuseStep 738857 = 554143) B554143
theorem B346223 : Blo 227813 346223 := bstep (se 1 (by rfl) ⟨259667, by rfl⟩ : syracuseStep 346223 = 519335) B519335
theorem B2672777 : Blo 227813 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B980221 : Blo 227813 980221 := bstep (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) B367583
theorem B492571 : Blo 227813 492571 := bstep (se 1 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 492571 = 738857) B738857
theorem B230815 : Blo 227813 230815 := bstep (se 1 (by rfl) ⟨173111, by rfl⟩ : syracuseStep 230815 = 346223) B346223
theorem B1781851 : Blo 227813 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B702335 : Blo 227813 702335 := bstep (se 1 (by rfl) ⟨526751, by rfl⟩ : syracuseStep 702335 = 1053503) B1053503
theorem B3565171 : Blo 227813 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B1306961 : Blo 227813 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B101939077 : Blo 227813 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B656761 : Blo 227813 656761 := bstep (se 2 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 656761 = 492571) B492571
theorem B4753561 : Blo 227813 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B468223 : Blo 227813 468223 := bstep (se 1 (by rfl) ⟨351167, by rfl⟩ : syracuseStep 468223 = 702335) B702335
theorem B2375801 : Blo 227813 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B871307 : Blo 227813 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B135918769 : Blo 227813 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B2497189 : Blo 227813 2497189 := bstep (se 4 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 2497189 = 468223) B468223
theorem B1583867 : Blo 227813 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B6338081 : Blo 227813 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B181225025 : Blo 227813 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B875681 : Blo 227813 875681 := bstep (se 2 (by rfl) ⟨328380, by rfl⟩ : syracuseStep 875681 = 656761) B656761
theorem B580871 : Blo 227813 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B120816683 : Blo 227813 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B1055911 : Blo 227813 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B3329585 : Blo 227813 3329585 := bstep (se 2 (by rfl) ⟨1248594, by rfl⟩ : syracuseStep 3329585 = 2497189) B2497189
theorem B583787 : Blo 227813 583787 := bstep (se 1 (by rfl) ⟨437840, by rfl⟩ : syracuseStep 583787 = 875681) B875681
theorem B387247 : Blo 227813 387247 := bstep (se 1 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 387247 = 580871) B580871
theorem B4225387 : Blo 227813 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B80544455 : Blo 227813 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B2219723 : Blo 227813 2219723 := bstep (se 1 (by rfl) ⟨1664792, by rfl⟩ : syracuseStep 2219723 = 3329585) B3329585
theorem B516329 : Blo 227813 516329 := bstep (se 2 (by rfl) ⟨193623, by rfl⟩ : syracuseStep 516329 = 387247) B387247
theorem B389191 : Blo 227813 389191 := bstep (se 1 (by rfl) ⟨291893, by rfl⟩ : syracuseStep 389191 = 583787) B583787
theorem B5633849 : Blo 227813 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B1407881 : Blo 227813 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B1479815 : Blo 227813 1479815 := bstep (se 1 (by rfl) ⟨1109861, by rfl⟩ : syracuseStep 1479815 = 2219723) B2219723
theorem B344219 : Blo 227813 344219 := bstep (se 1 (by rfl) ⟨258164, by rfl⟩ : syracuseStep 344219 = 516329) B516329
theorem B3754349 : Blo 227813 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B3755899 : Blo 227813 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B53696303 : Blo 227813 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B518921 : Blo 227813 518921 := bstep (se 2 (by rfl) ⟨194595, by rfl⟩ : syracuseStep 518921 = 389191) B389191
theorem B229479 : Blo 227813 229479 := bstep (se 1 (by rfl) ⟨172109, by rfl⟩ : syracuseStep 229479 = 344219) B344219
theorem B986543 : Blo 227813 986543 := bstep (se 1 (by rfl) ⟨739907, by rfl⟩ : syracuseStep 986543 = 1479815) B1479815
theorem B2502899 : Blo 227813 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B35797535 : Blo 227813 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B345947 : Blo 227813 345947 := bstep (se 1 (by rfl) ⟨259460, by rfl⟩ : syracuseStep 345947 = 518921) B518921
theorem B5007865 : Blo 227813 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B230631 : Blo 227813 230631 := bstep (se 1 (by rfl) ⟨172973, by rfl⟩ : syracuseStep 230631 = 345947) B345947
theorem B657695 : Blo 227813 657695 := bstep (se 1 (by rfl) ⟨493271, by rfl⟩ : syracuseStep 657695 = 986543) B986543
theorem B23865023 : Blo 227813 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B6677153 : Blo 227813 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B1668599 : Blo 227813 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B438463 : Blo 227813 438463 := bstep (se 1 (by rfl) ⟨328847, by rfl⟩ : syracuseStep 438463 = 657695) B657695
theorem B15910015 : Blo 227813 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B4451435 : Blo 227813 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B1112399 : Blo 227813 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B21213353 : Blo 227813 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B2967623 : Blo 227813 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B741599 : Blo 227813 741599 := bstep (se 1 (by rfl) ⟨556199, by rfl⟩ : syracuseStep 741599 = 1112399) B1112399
theorem B584617 : Blo 227813 584617 := bstep (se 2 (by rfl) ⟨219231, by rfl⟩ : syracuseStep 584617 = 438463) B438463
theorem B494399 : Blo 227813 494399 := bstep (se 1 (by rfl) ⟨370799, by rfl⟩ : syracuseStep 494399 = 741599) B741599
theorem B1978415 : Blo 227813 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B14142235 : Blo 227813 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B779489 : Blo 227813 779489 := bstep (se 2 (by rfl) ⟨292308, by rfl⟩ : syracuseStep 779489 = 584617) B584617
theorem B329599 : Blo 227813 329599 := bstep (se 1 (by rfl) ⟨247199, by rfl⟩ : syracuseStep 329599 = 494399) B494399
theorem B1318943 : Blo 227813 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B18856313 : Blo 227813 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B519659 : Blo 227813 519659 := bstep (se 1 (by rfl) ⟨389744, by rfl⟩ : syracuseStep 519659 = 779489) B779489
theorem B346439 : Blo 227813 346439 := bstep (se 1 (by rfl) ⟨259829, by rfl⟩ : syracuseStep 346439 = 519659) B519659
theorem B12570875 : Blo 227813 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B1757861 : Blo 227813 1757861 := bstep (se 4 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 1757861 = 329599) B329599
theorem B879295 : Blo 227813 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B230959 : Blo 227813 230959 := bstep (se 1 (by rfl) ⟨173219, by rfl⟩ : syracuseStep 230959 = 346439) B346439
theorem B8380583 : Blo 227813 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B1171907 : Blo 227813 1171907 := bstep (se 1 (by rfl) ⟨878930, by rfl⟩ : syracuseStep 1171907 = 1757861) B1757861
theorem B1172393 : Blo 227813 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B5587055 : Blo 227813 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B781271 : Blo 227813 781271 := bstep (se 1 (by rfl) ⟨585953, by rfl⟩ : syracuseStep 781271 = 1171907) B1171907
theorem B781595 : Blo 227813 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B3724703 : Blo 227813 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B520847 : Blo 227813 520847 := bstep (se 1 (by rfl) ⟨390635, by rfl⟩ : syracuseStep 520847 = 781271) B781271
theorem B521063 : Blo 227813 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B347231 : Blo 227813 347231 := bstep (se 1 (by rfl) ⟨260423, by rfl⟩ : syracuseStep 347231 = 520847) B520847
theorem B347375 : Blo 227813 347375 := bstep (se 1 (by rfl) ⟨260531, by rfl⟩ : syracuseStep 347375 = 521063) B521063
theorem B2483135 : Blo 227813 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B231487 : Blo 227813 231487 := bstep (se 1 (by rfl) ⟨173615, by rfl⟩ : syracuseStep 231487 = 347231) B347231
theorem B231583 : Blo 227813 231583 := bstep (se 1 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 231583 = 347375) B347375
theorem B1655423 : Blo 227813 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B1103615 : Blo 227813 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B735743 : Blo 227813 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B1961981 : Blo 227813 1961981 := bstep (se 3 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 1961981 = 735743) B735743
theorem B1307987 : Blo 227813 1307987 := bstep (se 1 (by rfl) ⟨980990, by rfl⟩ : syracuseStep 1307987 = 1961981) B1961981
theorem B871991 : Blo 227813 871991 := bstep (se 1 (by rfl) ⟨653993, by rfl⟩ : syracuseStep 871991 = 1307987) B1307987
theorem B581327 : Blo 227813 581327 := bstep (se 1 (by rfl) ⟨435995, by rfl⟩ : syracuseStep 581327 = 871991) B871991
theorem B387551 : Blo 227813 387551 := bstep (se 1 (by rfl) ⟨290663, by rfl⟩ : syracuseStep 387551 = 581327) B581327
theorem B258367 : Blo 227813 258367 := bstep (se 1 (by rfl) ⟨193775, by rfl⟩ : syracuseStep 258367 = 387551) B387551
theorem B344489 : Blo 227813 344489 := bstep (se 2 (by rfl) ⟨129183, by rfl⟩ : syracuseStep 344489 = 258367) B258367
theorem B229659 : Blo 227813 229659 := bstep (se 1 (by rfl) ⟨172244, by rfl⟩ : syracuseStep 229659 = 344489) B344489

theorem C0 (j : ℕ) (h1 : 56953 ≤ j) (h2 : j ≤ 57652) : Blo 227813 (4 * j + 3) := by
  interval_cases j
  · exact B227815
  · exact B227819
  · exact B227823
  · exact B227827
  · exact B227831
  · exact B227835
  · exact B227839
  · exact B227843
  · exact B227847
  · exact B227851
  · exact B227855
  · exact B227859
  · exact B227863
  · exact B227867
  · exact B227871
  · exact B227875
  · exact B227879
  · exact B227883
  · exact B227887
  · exact B227891
  · exact B227895
  · exact B227899
  · exact B227903
  · exact B227907
  · exact B227911
  · exact B227915
  · exact B227919
  · exact B227923
  · exact B227927
  · exact B227931
  · exact B227935
  · exact B227939
  · exact B227943
  · exact B227947
  · exact B227951
  · exact B227955
  · exact B227959
  · exact B227963
  · exact B227967
  · exact B227971
  · exact B227975
  · exact B227979
  · exact B227983
  · exact B227987
  · exact B227991
  · exact B227995
  · exact B227999
  · exact B228003
  · exact B228007
  · exact B228011
  · exact B228015
  · exact B228019
  · exact B228023
  · exact B228027
  · exact B228031
  · exact B228035
  · exact B228039
  · exact B228043
  · exact B228047
  · exact B228051
  · exact B228055
  · exact B228059
  · exact B228063
  · exact B228067
  · exact B228071
  · exact B228075
  · exact B228079
  · exact B228083
  · exact B228087
  · exact B228091
  · exact B228095
  · exact B228099
  · exact B228103
  · exact B228107
  · exact B228111
  · exact B228115
  · exact B228119
  · exact B228123
  · exact B228127
  · exact B228131
  · exact B228135
  · exact B228139
  · exact B228143
  · exact B228147
  · exact B228151
  · exact B228155
  · exact B228159
  · exact B228163
  · exact B228167
  · exact B228171
  · exact B228175
  · exact B228179
  · exact B228183
  · exact B228187
  · exact B228191
  · exact B228195
  · exact B228199
  · exact B228203
  · exact B228207
  · exact B228211
  · exact B228215
  · exact B228219
  · exact B228223
  · exact B228227
  · exact B228231
  · exact B228235
  · exact B228239
  · exact B228243
  · exact B228247
  · exact B228251
  · exact B228255
  · exact B228259
  · exact B228263
  · exact B228267
  · exact B228271
  · exact B228275
  · exact B228279
  · exact B228283
  · exact B228287
  · exact B228291
  · exact B228295
  · exact B228299
  · exact B228303
  · exact B228307
  · exact B228311
  · exact B228315
  · exact B228319
  · exact B228323
  · exact B228327
  · exact B228331
  · exact B228335
  · exact B228339
  · exact B228343
  · exact B228347
  · exact B228351
  · exact B228355
  · exact B228359
  · exact B228363
  · exact B228367
  · exact B228371
  · exact B228375
  · exact B228379
  · exact B228383
  · exact B228387
  · exact B228391
  · exact B228395
  · exact B228399
  · exact B228403
  · exact B228407
  · exact B228411
  · exact B228415
  · exact B228419
  · exact B228423
  · exact B228427
  · exact B228431
  · exact B228435
  · exact B228439
  · exact B228443
  · exact B228447
  · exact B228451
  · exact B228455
  · exact B228459
  · exact B228463
  · exact B228467
  · exact B228471
  · exact B228475
  · exact B228479
  · exact B228483
  · exact B228487
  · exact B228491
  · exact B228495
  · exact B228499
  · exact B228503
  · exact B228507
  · exact B228511
  · exact B228515
  · exact B228519
  · exact B228523
  · exact B228527
  · exact B228531
  · exact B228535
  · exact B228539
  · exact B228543
  · exact B228547
  · exact B228551
  · exact B228555
  · exact B228559
  · exact B228563
  · exact B228567
  · exact B228571
  · exact B228575
  · exact B228579
  · exact B228583
  · exact B228587
  · exact B228591
  · exact B228595
  · exact B228599
  · exact B228603
  · exact B228607
  · exact B228611
  · exact B228615
  · exact B228619
  · exact B228623
  · exact B228627
  · exact B228631
  · exact B228635
  · exact B228639
  · exact B228643
  · exact B228647
  · exact B228651
  · exact B228655
  · exact B228659
  · exact B228663
  · exact B228667
  · exact B228671
  · exact B228675
  · exact B228679
  · exact B228683
  · exact B228687
  · exact B228691
  · exact B228695
  · exact B228699
  · exact B228703
  · exact B228707
  · exact B228711
  · exact B228715
  · exact B228719
  · exact B228723
  · exact B228727
  · exact B228731
  · exact B228735
  · exact B228739
  · exact B228743
  · exact B228747
  · exact B228751
  · exact B228755
  · exact B228759
  · exact B228763
  · exact B228767
  · exact B228771
  · exact B228775
  · exact B228779
  · exact B228783
  · exact B228787
  · exact B228791
  · exact B228795
  · exact B228799
  · exact B228803
  · exact B228807
  · exact B228811
  · exact B228815
  · exact B228819
  · exact B228823
  · exact B228827
  · exact B228831
  · exact B228835
  · exact B228839
  · exact B228843
  · exact B228847
  · exact B228851
  · exact B228855
  · exact B228859
  · exact B228863
  · exact B228867
  · exact B228871
  · exact B228875
  · exact B228879
  · exact B228883
  · exact B228887
  · exact B228891
  · exact B228895
  · exact B228899
  · exact B228903
  · exact B228907
  · exact B228911
  · exact B228915
  · exact B228919
  · exact B228923
  · exact B228927
  · exact B228931
  · exact B228935
  · exact B228939
  · exact B228943
  · exact B228947
  · exact B228951
  · exact B228955
  · exact B228959
  · exact B228963
  · exact B228967
  · exact B228971
  · exact B228975
  · exact B228979
  · exact B228983
  · exact B228987
  · exact B228991
  · exact B228995
  · exact B228999
  · exact B229003
  · exact B229007
  · exact B229011
  · exact B229015
  · exact B229019
  · exact B229023
  · exact B229027
  · exact B229031
  · exact B229035
  · exact B229039
  · exact B229043
  · exact B229047
  · exact B229051
  · exact B229055
  · exact B229059
  · exact B229063
  · exact B229067
  · exact B229071
  · exact B229075
  · exact B229079
  · exact B229083
  · exact B229087
  · exact B229091
  · exact B229095
  · exact B229099
  · exact B229103
  · exact B229107
  · exact B229111
  · exact B229115
  · exact B229119
  · exact B229123
  · exact B229127
  · exact B229131
  · exact B229135
  · exact B229139
  · exact B229143
  · exact B229147
  · exact B229151
  · exact B229155
  · exact B229159
  · exact B229163
  · exact B229167
  · exact B229171
  · exact B229175
  · exact B229179
  · exact B229183
  · exact B229187
  · exact B229191
  · exact B229195
  · exact B229199
  · exact B229203
  · exact B229207
  · exact B229211
  · exact B229215
  · exact B229219
  · exact B229223
  · exact B229227
  · exact B229231
  · exact B229235
  · exact B229239
  · exact B229243
  · exact B229247
  · exact B229251
  · exact B229255
  · exact B229259
  · exact B229263
  · exact B229267
  · exact B229271
  · exact B229275
  · exact B229279
  · exact B229283
  · exact B229287
  · exact B229291
  · exact B229295
  · exact B229299
  · exact B229303
  · exact B229307
  · exact B229311
  · exact B229315
  · exact B229319
  · exact B229323
  · exact B229327
  · exact B229331
  · exact B229335
  · exact B229339
  · exact B229343
  · exact B229347
  · exact B229351
  · exact B229355
  · exact B229359
  · exact B229363
  · exact B229367
  · exact B229371
  · exact B229375
  · exact B229379
  · exact B229383
  · exact B229387
  · exact B229391
  · exact B229395
  · exact B229399
  · exact B229403
  · exact B229407
  · exact B229411
  · exact B229415
  · exact B229419
  · exact B229423
  · exact B229427
  · exact B229431
  · exact B229435
  · exact B229439
  · exact B229443
  · exact B229447
  · exact B229451
  · exact B229455
  · exact B229459
  · exact B229463
  · exact B229467
  · exact B229471
  · exact B229475
  · exact B229479
  · exact B229483
  · exact B229487
  · exact B229491
  · exact B229495
  · exact B229499
  · exact B229503
  · exact B229507
  · exact B229511
  · exact B229515
  · exact B229519
  · exact B229523
  · exact B229527
  · exact B229531
  · exact B229535
  · exact B229539
  · exact B229543
  · exact B229547
  · exact B229551
  · exact B229555
  · exact B229559
  · exact B229563
  · exact B229567
  · exact B229571
  · exact B229575
  · exact B229579
  · exact B229583
  · exact B229587
  · exact B229591
  · exact B229595
  · exact B229599
  · exact B229603
  · exact B229607
  · exact B229611
  · exact B229615
  · exact B229619
  · exact B229623
  · exact B229627
  · exact B229631
  · exact B229635
  · exact B229639
  · exact B229643
  · exact B229647
  · exact B229651
  · exact B229655
  · exact B229659
  · exact B229663
  · exact B229667
  · exact B229671
  · exact B229675
  · exact B229679
  · exact B229683
  · exact B229687
  · exact B229691
  · exact B229695
  · exact B229699
  · exact B229703
  · exact B229707
  · exact B229711
  · exact B229715
  · exact B229719
  · exact B229723
  · exact B229727
  · exact B229731
  · exact B229735
  · exact B229739
  · exact B229743
  · exact B229747
  · exact B229751
  · exact B229755
  · exact B229759
  · exact B229763
  · exact B229767
  · exact B229771
  · exact B229775
  · exact B229779
  · exact B229783
  · exact B229787
  · exact B229791
  · exact B229795
  · exact B229799
  · exact B229803
  · exact B229807
  · exact B229811
  · exact B229815
  · exact B229819
  · exact B229823
  · exact B229827
  · exact B229831
  · exact B229835
  · exact B229839
  · exact B229843
  · exact B229847
  · exact B229851
  · exact B229855
  · exact B229859
  · exact B229863
  · exact B229867
  · exact B229871
  · exact B229875
  · exact B229879
  · exact B229883
  · exact B229887
  · exact B229891
  · exact B229895
  · exact B229899
  · exact B229903
  · exact B229907
  · exact B229911
  · exact B229915
  · exact B229919
  · exact B229923
  · exact B229927
  · exact B229931
  · exact B229935
  · exact B229939
  · exact B229943
  · exact B229947
  · exact B229951
  · exact B229955
  · exact B229959
  · exact B229963
  · exact B229967
  · exact B229971
  · exact B229975
  · exact B229979
  · exact B229983
  · exact B229987
  · exact B229991
  · exact B229995
  · exact B229999
  · exact B230003
  · exact B230007
  · exact B230011
  · exact B230015
  · exact B230019
  · exact B230023
  · exact B230027
  · exact B230031
  · exact B230035
  · exact B230039
  · exact B230043
  · exact B230047
  · exact B230051
  · exact B230055
  · exact B230059
  · exact B230063
  · exact B230067
  · exact B230071
  · exact B230075
  · exact B230079
  · exact B230083
  · exact B230087
  · exact B230091
  · exact B230095
  · exact B230099
  · exact B230103
  · exact B230107
  · exact B230111
  · exact B230115
  · exact B230119
  · exact B230123
  · exact B230127
  · exact B230131
  · exact B230135
  · exact B230139
  · exact B230143
  · exact B230147
  · exact B230151
  · exact B230155
  · exact B230159
  · exact B230163
  · exact B230167
  · exact B230171
  · exact B230175
  · exact B230179
  · exact B230183
  · exact B230187
  · exact B230191
  · exact B230195
  · exact B230199
  · exact B230203
  · exact B230207
  · exact B230211
  · exact B230215
  · exact B230219
  · exact B230223
  · exact B230227
  · exact B230231
  · exact B230235
  · exact B230239
  · exact B230243
  · exact B230247
  · exact B230251
  · exact B230255
  · exact B230259
  · exact B230263
  · exact B230267
  · exact B230271
  · exact B230275
  · exact B230279
  · exact B230283
  · exact B230287
  · exact B230291
  · exact B230295
  · exact B230299
  · exact B230303
  · exact B230307
  · exact B230311
  · exact B230315
  · exact B230319
  · exact B230323
  · exact B230327
  · exact B230331
  · exact B230335
  · exact B230339
  · exact B230343
  · exact B230347
  · exact B230351
  · exact B230355
  · exact B230359
  · exact B230363
  · exact B230367
  · exact B230371
  · exact B230375
  · exact B230379
  · exact B230383
  · exact B230387
  · exact B230391
  · exact B230395
  · exact B230399
  · exact B230403
  · exact B230407
  · exact B230411
  · exact B230415
  · exact B230419
  · exact B230423
  · exact B230427
  · exact B230431
  · exact B230435
  · exact B230439
  · exact B230443
  · exact B230447
  · exact B230451
  · exact B230455
  · exact B230459
  · exact B230463
  · exact B230467
  · exact B230471
  · exact B230475
  · exact B230479
  · exact B230483
  · exact B230487
  · exact B230491
  · exact B230495
  · exact B230499
  · exact B230503
  · exact B230507
  · exact B230511
  · exact B230515
  · exact B230519
  · exact B230523
  · exact B230527
  · exact B230531
  · exact B230535
  · exact B230539
  · exact B230543
  · exact B230547
  · exact B230551
  · exact B230555
  · exact B230559
  · exact B230563
  · exact B230567
  · exact B230571
  · exact B230575
  · exact B230579
  · exact B230583
  · exact B230587
  · exact B230591
  · exact B230595
  · exact B230599
  · exact B230603
  · exact B230607
  · exact B230611

theorem C1 (j : ℕ) (h1 : 57653 ≤ j) (h2 : j ≤ 57952) : Blo 227813 (4 * j + 3) := by
  interval_cases j
  · exact B230615
  · exact B230619
  · exact B230623
  · exact B230627
  · exact B230631
  · exact B230635
  · exact B230639
  · exact B230643
  · exact B230647
  · exact B230651
  · exact B230655
  · exact B230659
  · exact B230663
  · exact B230667
  · exact B230671
  · exact B230675
  · exact B230679
  · exact B230683
  · exact B230687
  · exact B230691
  · exact B230695
  · exact B230699
  · exact B230703
  · exact B230707
  · exact B230711
  · exact B230715
  · exact B230719
  · exact B230723
  · exact B230727
  · exact B230731
  · exact B230735
  · exact B230739
  · exact B230743
  · exact B230747
  · exact B230751
  · exact B230755
  · exact B230759
  · exact B230763
  · exact B230767
  · exact B230771
  · exact B230775
  · exact B230779
  · exact B230783
  · exact B230787
  · exact B230791
  · exact B230795
  · exact B230799
  · exact B230803
  · exact B230807
  · exact B230811
  · exact B230815
  · exact B230819
  · exact B230823
  · exact B230827
  · exact B230831
  · exact B230835
  · exact B230839
  · exact B230843
  · exact B230847
  · exact B230851
  · exact B230855
  · exact B230859
  · exact B230863
  · exact B230867
  · exact B230871
  · exact B230875
  · exact B230879
  · exact B230883
  · exact B230887
  · exact B230891
  · exact B230895
  · exact B230899
  · exact B230903
  · exact B230907
  · exact B230911
  · exact B230915
  · exact B230919
  · exact B230923
  · exact B230927
  · exact B230931
  · exact B230935
  · exact B230939
  · exact B230943
  · exact B230947
  · exact B230951
  · exact B230955
  · exact B230959
  · exact B230963
  · exact B230967
  · exact B230971
  · exact B230975
  · exact B230979
  · exact B230983
  · exact B230987
  · exact B230991
  · exact B230995
  · exact B230999
  · exact B231003
  · exact B231007
  · exact B231011
  · exact B231015
  · exact B231019
  · exact B231023
  · exact B231027
  · exact B231031
  · exact B231035
  · exact B231039
  · exact B231043
  · exact B231047
  · exact B231051
  · exact B231055
  · exact B231059
  · exact B231063
  · exact B231067
  · exact B231071
  · exact B231075
  · exact B231079
  · exact B231083
  · exact B231087
  · exact B231091
  · exact B231095
  · exact B231099
  · exact B231103
  · exact B231107
  · exact B231111
  · exact B231115
  · exact B231119
  · exact B231123
  · exact B231127
  · exact B231131
  · exact B231135
  · exact B231139
  · exact B231143
  · exact B231147
  · exact B231151
  · exact B231155
  · exact B231159
  · exact B231163
  · exact B231167
  · exact B231171
  · exact B231175
  · exact B231179
  · exact B231183
  · exact B231187
  · exact B231191
  · exact B231195
  · exact B231199
  · exact B231203
  · exact B231207
  · exact B231211
  · exact B231215
  · exact B231219
  · exact B231223
  · exact B231227
  · exact B231231
  · exact B231235
  · exact B231239
  · exact B231243
  · exact B231247
  · exact B231251
  · exact B231255
  · exact B231259
  · exact B231263
  · exact B231267
  · exact B231271
  · exact B231275
  · exact B231279
  · exact B231283
  · exact B231287
  · exact B231291
  · exact B231295
  · exact B231299
  · exact B231303
  · exact B231307
  · exact B231311
  · exact B231315
  · exact B231319
  · exact B231323
  · exact B231327
  · exact B231331
  · exact B231335
  · exact B231339
  · exact B231343
  · exact B231347
  · exact B231351
  · exact B231355
  · exact B231359
  · exact B231363
  · exact B231367
  · exact B231371
  · exact B231375
  · exact B231379
  · exact B231383
  · exact B231387
  · exact B231391
  · exact B231395
  · exact B231399
  · exact B231403
  · exact B231407
  · exact B231411
  · exact B231415
  · exact B231419
  · exact B231423
  · exact B231427
  · exact B231431
  · exact B231435
  · exact B231439
  · exact B231443
  · exact B231447
  · exact B231451
  · exact B231455
  · exact B231459
  · exact B231463
  · exact B231467
  · exact B231471
  · exact B231475
  · exact B231479
  · exact B231483
  · exact B231487
  · exact B231491
  · exact B231495
  · exact B231499
  · exact B231503
  · exact B231507
  · exact B231511
  · exact B231515
  · exact B231519
  · exact B231523
  · exact B231527
  · exact B231531
  · exact B231535
  · exact B231539
  · exact B231543
  · exact B231547
  · exact B231551
  · exact B231555
  · exact B231559
  · exact B231563
  · exact B231567
  · exact B231571
  · exact B231575
  · exact B231579
  · exact B231583
  · exact B231587
  · exact B231591
  · exact B231595
  · exact B231599
  · exact B231603
  · exact B231607
  · exact B231611
  · exact B231615
  · exact B231619
  · exact B231623
  · exact B231627
  · exact B231631
  · exact B231635
  · exact B231639
  · exact B231643
  · exact B231647
  · exact B231651
  · exact B231655
  · exact B231659
  · exact B231663
  · exact B231667
  · exact B231671
  · exact B231675
  · exact B231679
  · exact B231683
  · exact B231687
  · exact B231691
  · exact B231695
  · exact B231699
  · exact B231703
  · exact B231707
  · exact B231711
  · exact B231715
  · exact B231719
  · exact B231723
  · exact B231727
  · exact B231731
  · exact B231735
  · exact B231739
  · exact B231743
  · exact B231747
  · exact B231751
  · exact B231755
  · exact B231759
  · exact B231763
  · exact B231767
  · exact B231771
  · exact B231775
  · exact B231779
  · exact B231783
  · exact B231787
  · exact B231791
  · exact B231795
  · exact B231799
  · exact B231803
  · exact B231807
  · exact B231811

theorem solution (m : ℕ) (hlo : 227813 ≤ m) (hhi : m ≤ 231813) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 56953 ≤ j := by omega
    have hj2 : j ≤ 57952 := by omega
    have hb : Blo 227813 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 57653 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
