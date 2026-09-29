-- Prove2me | solution 1 for syracuse_descends_range_327838_330749
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:26.16321+00:00
-- url     : https://prove2.me/submissions/0da47da2-2e41-4edf-8774-5b75572ab7d5

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


theorem B417793 : Blo 327838 417793 := bbase (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) (by norm_num)
theorem B557077 : Blo 327838 557077 := bbase (se 6 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 557077 = 26113) (by norm_num)
theorem B1245253 : Blo 327838 1245253 := bbase (se 4 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 1245253 = 233485) (by norm_num)
theorem B1114181 : Blo 327838 1114181 := bbase (se 4 (by rfl) ⟨104454, by rfl⟩ : syracuseStep 1114181 = 208909) (by norm_num)
theorem B475213 : Blo 327838 475213 := bbase (se 3 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 475213 = 178205) (by norm_num)
theorem B417889 : Blo 327838 417889 := bbase (se 2 (by rfl) ⟨156708, by rfl⟩ : syracuseStep 417889 = 313417) (by norm_num)
theorem B557165 : Blo 327838 557165 := bbase (se 3 (by rfl) ⟨104468, by rfl⟩ : syracuseStep 557165 = 208937) (by norm_num)
theorem B835717 : Blo 327838 835717 := bbase (se 4 (by rfl) ⟨78348, by rfl⟩ : syracuseStep 835717 = 156697) (by norm_num)
theorem B622741 : Blo 327838 622741 := bbase (se 6 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 622741 = 29191) (by norm_num)
theorem B704693 : Blo 327838 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B368833 : Blo 327838 368833 := bbase (se 2 (by rfl) ⟨138312, by rfl⟩ : syracuseStep 368833 = 276625) (by norm_num)
theorem B2367701 : Blo 327838 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B499925 : Blo 327838 499925 := bbase (se 7 (by rfl) ⟨5858, by rfl⟩ : syracuseStep 499925 = 11717) (by norm_num)
theorem B368869 : Blo 327838 368869 := bbase (se 4 (by rfl) ⟨34581, by rfl⟩ : syracuseStep 368869 = 69163) (by norm_num)
theorem B557293 : Blo 327838 557293 := bbase (se 3 (by rfl) ⟨104492, by rfl⟩ : syracuseStep 557293 = 208985) (by norm_num)
theorem B491765 : Blo 327838 491765 := bbase (se 5 (by rfl) ⟨23051, by rfl⟩ : syracuseStep 491765 = 46103) (by norm_num)
theorem B835829 : Blo 327838 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B565501 : Blo 327838 565501 := bbase (se 3 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 565501 = 212063) (by norm_num)
theorem B352517 : Blo 327838 352517 := bbase (se 4 (by rfl) ⟨33048, by rfl⟩ : syracuseStep 352517 = 66097) (by norm_num)
theorem B368905 : Blo 327838 368905 := bbase (se 2 (by rfl) ⟨138339, by rfl⟩ : syracuseStep 368905 = 276679) (by norm_num)
theorem B491789 : Blo 327838 491789 := bbase (se 3 (by rfl) ⟨92210, by rfl⟩ : syracuseStep 491789 = 184421) (by norm_num)
theorem B418061 : Blo 327838 418061 := bbase (se 3 (by rfl) ⟨78386, by rfl⟩ : syracuseStep 418061 = 156773) (by norm_num)
theorem B467221 : Blo 327838 467221 := bbase (se 6 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 467221 = 21901) (by norm_num)
theorem B1663253 : Blo 327838 1663253 := bbase (se 6 (by rfl) ⟨38982, by rfl⟩ : syracuseStep 1663253 = 77965) (by norm_num)
theorem B491813 : Blo 327838 491813 := bbase (se 4 (by rfl) ⟨46107, by rfl⟩ : syracuseStep 491813 = 92215) (by norm_num)
theorem B622885 : Blo 327838 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B368941 : Blo 327838 368941 := bbase (se 3 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 368941 = 138353) (by norm_num)
theorem B491837 : Blo 327838 491837 := bbase (se 3 (by rfl) ⟨92219, by rfl⟩ : syracuseStep 491837 = 184439) (by norm_num)
theorem B557381 : Blo 327838 557381 := bbase (se 4 (by rfl) ⟨52254, by rfl⟩ : syracuseStep 557381 = 104509) (by norm_num)
theorem B418117 : Blo 327838 418117 := bbase (se 4 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 418117 = 78397) (by norm_num)
theorem B368977 : Blo 327838 368977 := bbase (se 2 (by rfl) ⟨138366, by rfl⟩ : syracuseStep 368977 = 276733) (by norm_num)
theorem B491861 : Blo 327838 491861 := bbase (se 10 (by rfl) ⟨720, by rfl⟩ : syracuseStep 491861 = 1441) (by norm_num)
theorem B483685 : Blo 327838 483685 := bbase (se 4 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 483685 = 90691) (by norm_num)
theorem B491885 : Blo 327838 491885 := bbase (se 3 (by rfl) ⟨92228, by rfl⟩ : syracuseStep 491885 = 184457) (by norm_num)
theorem B369013 : Blo 327838 369013 := bbase (se 5 (by rfl) ⟨17297, by rfl⟩ : syracuseStep 369013 = 34595) (by norm_num)
theorem B1245557 : Blo 327838 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B1057141 : Blo 327838 1057141 := bbase (se 5 (by rfl) ⟨49553, by rfl⟩ : syracuseStep 1057141 = 99107) (by norm_num)
theorem B491909 : Blo 327838 491909 := bbase (se 4 (by rfl) ⟨46116, by rfl⟩ : syracuseStep 491909 = 92233) (by norm_num)
theorem B369049 : Blo 327838 369049 := bbase (se 2 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 369049 = 276787) (by norm_num)
theorem B737693 : Blo 327838 737693 := bbase (se 3 (by rfl) ⟨138317, by rfl⟩ : syracuseStep 737693 = 276635) (by norm_num)
theorem B491933 : Blo 327838 491933 := bbase (se 3 (by rfl) ⟨92237, by rfl⟩ : syracuseStep 491933 = 184475) (by norm_num)
theorem B418213 : Blo 327838 418213 := bbase (se 4 (by rfl) ⟨39207, by rfl⟩ : syracuseStep 418213 = 78415) (by norm_num)
theorem B491957 : Blo 327838 491957 := bbase (se 5 (by rfl) ⟨23060, by rfl⟩ : syracuseStep 491957 = 46121) (by norm_num)
theorem B836021 : Blo 327838 836021 := bbase (se 5 (by rfl) ⟨39188, by rfl⟩ : syracuseStep 836021 = 78377) (by norm_num)
theorem B369085 : Blo 327838 369085 := bbase (se 3 (by rfl) ⟨69203, by rfl⟩ : syracuseStep 369085 = 138407) (by norm_num)
theorem B623045 : Blo 327838 623045 := bbase (se 4 (by rfl) ⟨58410, by rfl⟩ : syracuseStep 623045 = 116821) (by norm_num)
theorem B557509 : Blo 327838 557509 := bbase (se 4 (by rfl) ⟨52266, by rfl⟩ : syracuseStep 557509 = 104533) (by norm_num)
theorem B491981 : Blo 327838 491981 := bbase (se 3 (by rfl) ⟨92246, by rfl⟩ : syracuseStep 491981 = 184493) (by norm_num)
theorem B369121 : Blo 327838 369121 := bbase (se 2 (by rfl) ⟨138420, by rfl⟩ : syracuseStep 369121 = 276841) (by norm_num)
theorem B737765 : Blo 327838 737765 := bbase (se 4 (by rfl) ⟨69165, by rfl⟩ : syracuseStep 737765 = 138331) (by norm_num)
theorem B492005 : Blo 327838 492005 := bbase (se 4 (by rfl) ⟨46125, by rfl⟩ : syracuseStep 492005 = 92251) (by norm_num)
theorem B565733 : Blo 327838 565733 := bbase (se 4 (by rfl) ⟨53037, by rfl⟩ : syracuseStep 565733 = 106075) (by norm_num)
theorem B1114613 : Blo 327838 1114613 := bbase (se 5 (by rfl) ⟨52247, by rfl⟩ : syracuseStep 1114613 = 104495) (by norm_num)
theorem B492029 : Blo 327838 492029 := bbase (se 3 (by rfl) ⟨92255, by rfl⟩ : syracuseStep 492029 = 184511) (by norm_num)
theorem B352765 : Blo 327838 352765 := bbase (se 3 (by rfl) ⟨66143, by rfl⟩ : syracuseStep 352765 = 132287) (by norm_num)
theorem B369157 : Blo 327838 369157 := bbase (se 4 (by rfl) ⟨34608, by rfl⟩ : syracuseStep 369157 = 69217) (by norm_num)
theorem B492053 : Blo 327838 492053 := bbase (se 6 (by rfl) ⟨11532, by rfl⟩ : syracuseStep 492053 = 23065) (by norm_num)
theorem B557597 : Blo 327838 557597 := bbase (se 3 (by rfl) ⟨104549, by rfl⟩ : syracuseStep 557597 = 209099) (by norm_num)
theorem B369193 : Blo 327838 369193 := bbase (se 2 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 369193 = 276895) (by norm_num)
theorem B737837 : Blo 327838 737837 := bbase (se 3 (by rfl) ⟨138344, by rfl⟩ : syracuseStep 737837 = 276689) (by norm_num)
theorem B492077 : Blo 327838 492077 := bbase (se 3 (by rfl) ⟨92264, by rfl⟩ : syracuseStep 492077 = 184529) (by norm_num)
theorem B492101 : Blo 327838 492101 := bbase (se 4 (by rfl) ⟨46134, by rfl⟩ : syracuseStep 492101 = 92269) (by norm_num)
theorem B369229 : Blo 327838 369229 := bbase (se 3 (by rfl) ⟨69230, by rfl⟩ : syracuseStep 369229 = 138461) (by norm_num)
theorem B623189 : Blo 327838 623189 := bbase (se 8 (by rfl) ⟨3651, by rfl⟩ : syracuseStep 623189 = 7303) (by norm_num)
theorem B492125 : Blo 327838 492125 := bbase (se 3 (by rfl) ⟨92273, by rfl⟩ : syracuseStep 492125 = 184547) (by norm_num)
theorem B369265 : Blo 327838 369265 := bbase (se 2 (by rfl) ⟨138474, by rfl⟩ : syracuseStep 369265 = 276949) (by norm_num)
theorem B737909 : Blo 327838 737909 := bbase (se 5 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 737909 = 69179) (by norm_num)
theorem B492149 : Blo 327838 492149 := bbase (se 5 (by rfl) ⟨23069, by rfl⟩ : syracuseStep 492149 = 46139) (by norm_num)
theorem B492173 : Blo 327838 492173 := bbase (se 3 (by rfl) ⟨92282, by rfl⟩ : syracuseStep 492173 = 184565) (by norm_num)
theorem B418441 : Blo 327838 418441 := bbase (se 2 (by rfl) ⟨156915, by rfl⟩ : syracuseStep 418441 = 313831) (by norm_num)
theorem B369301 : Blo 327838 369301 := bbase (se 6 (by rfl) ⟨8655, by rfl⟩ : syracuseStep 369301 = 17311) (by norm_num)
theorem B557725 : Blo 327838 557725 := bbase (se 3 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 557725 = 209147) (by norm_num)
theorem B492197 : Blo 327838 492197 := bbase (se 4 (by rfl) ⟨46143, by rfl⟩ : syracuseStep 492197 = 92287) (by norm_num)
theorem B369337 : Blo 327838 369337 := bbase (se 2 (by rfl) ⟨138501, by rfl⟩ : syracuseStep 369337 = 277003) (by norm_num)
theorem B737981 : Blo 327838 737981 := bbase (se 3 (by rfl) ⟨138371, by rfl⟩ : syracuseStep 737981 = 276743) (by norm_num)
theorem B492221 : Blo 327838 492221 := bbase (se 3 (by rfl) ⟨92291, by rfl⟩ : syracuseStep 492221 = 184583) (by norm_num)
theorem B492245 : Blo 327838 492245 := bbase (se 7 (by rfl) ⟨5768, by rfl⟩ : syracuseStep 492245 = 11537) (by norm_num)
theorem B2114261 : Blo 327838 2114261 := bbase (se 7 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 2114261 = 49553) (by norm_num)
theorem B369373 : Blo 327838 369373 := bbase (se 3 (by rfl) ⟨69257, by rfl⟩ : syracuseStep 369373 = 138515) (by norm_num)
theorem B418537 : Blo 327838 418537 := bbase (se 2 (by rfl) ⟨156951, by rfl⟩ : syracuseStep 418537 = 313903) (by norm_num)
theorem B492269 : Blo 327838 492269 := bbase (se 3 (by rfl) ⟨92300, by rfl⟩ : syracuseStep 492269 = 184601) (by norm_num)
theorem B557813 : Blo 327838 557813 := bbase (se 5 (by rfl) ⟨26147, by rfl⟩ : syracuseStep 557813 = 52295) (by norm_num)
theorem B369409 : Blo 327838 369409 := bbase (se 2 (by rfl) ⟨138528, by rfl⟩ : syracuseStep 369409 = 277057) (by norm_num)
theorem B738053 : Blo 327838 738053 := bbase (se 4 (by rfl) ⟨69192, by rfl⟩ : syracuseStep 738053 = 138385) (by norm_num)
theorem B492293 : Blo 327838 492293 := bbase (se 4 (by rfl) ⟨46152, by rfl⟩ : syracuseStep 492293 = 92305) (by norm_num)
theorem B836365 : Blo 327838 836365 := bbase (se 3 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 836365 = 313637) (by norm_num)
theorem B492317 : Blo 327838 492317 := bbase (se 3 (by rfl) ⟨92309, by rfl⟩ : syracuseStep 492317 = 184619) (by norm_num)
theorem B369445 : Blo 327838 369445 := bbase (se 4 (by rfl) ⟨34635, by rfl⟩ : syracuseStep 369445 = 69271) (by norm_num)
theorem B492341 : Blo 327838 492341 := bbase (se 5 (by rfl) ⟨23078, by rfl⟩ : syracuseStep 492341 = 46157) (by norm_num)
theorem B369481 : Blo 327838 369481 := bbase (se 2 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 369481 = 277111) (by norm_num)
theorem B738125 : Blo 327838 738125 := bbase (se 3 (by rfl) ⟨138398, by rfl⟩ : syracuseStep 738125 = 276797) (by norm_num)
theorem B492365 : Blo 327838 492365 := bbase (se 3 (by rfl) ⟨92318, by rfl⟩ : syracuseStep 492365 = 184637) (by norm_num)
theorem B492389 : Blo 327838 492389 := bbase (se 4 (by rfl) ⟨46161, by rfl⟩ : syracuseStep 492389 = 92323) (by norm_num)
theorem B467813 : Blo 327838 467813 := bbase (se 4 (by rfl) ⟨43857, by rfl⟩ : syracuseStep 467813 = 87715) (by norm_num)
theorem B394093 : Blo 327838 394093 := bbase (se 3 (by rfl) ⟨73892, by rfl⟩ : syracuseStep 394093 = 147785) (by norm_num)
theorem B369517 : Blo 327838 369517 := bbase (se 3 (by rfl) ⟨69284, by rfl⟩ : syracuseStep 369517 = 138569) (by norm_num)
theorem B623477 : Blo 327838 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B557941 : Blo 327838 557941 := bbase (se 5 (by rfl) ⟨26153, by rfl⟩ : syracuseStep 557941 = 52307) (by norm_num)
theorem B492413 : Blo 327838 492413 := bbase (se 3 (by rfl) ⟨92327, by rfl⟩ : syracuseStep 492413 = 184655) (by norm_num)
theorem B836477 : Blo 327838 836477 := bbase (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) (by norm_num)
theorem B369553 : Blo 327838 369553 := bbase (se 2 (by rfl) ⟨138582, by rfl⟩ : syracuseStep 369553 = 277165) (by norm_num)
theorem B361361 : Blo 327838 361361 := bbase (se 2 (by rfl) ⟨135510, by rfl⟩ : syracuseStep 361361 = 271021) (by norm_num)
theorem B1106837 : Blo 327838 1106837 := bbase (se 6 (by rfl) ⟨25941, by rfl⟩ : syracuseStep 1106837 = 51883) (by norm_num)
theorem B738197 : Blo 327838 738197 := bbase (se 6 (by rfl) ⟨17301, by rfl⟩ : syracuseStep 738197 = 34603) (by norm_num)
theorem B492437 : Blo 327838 492437 := bbase (se 6 (by rfl) ⟨11541, by rfl⟩ : syracuseStep 492437 = 23083) (by norm_num)
theorem B1115045 : Blo 327838 1115045 := bbase (se 4 (by rfl) ⟨104535, by rfl⟩ : syracuseStep 1115045 = 209071) (by norm_num)
theorem B492461 : Blo 327838 492461 := bbase (se 3 (by rfl) ⟨92336, by rfl⟩ : syracuseStep 492461 = 184673) (by norm_num)
theorem B369589 : Blo 327838 369589 := bbase (se 5 (by rfl) ⟨17324, by rfl⟩ : syracuseStep 369589 = 34649) (by norm_num)
theorem B467893 : Blo 327838 467893 := bbase (se 5 (by rfl) ⟨21932, by rfl⟩ : syracuseStep 467893 = 43865) (by norm_num)
theorem B492485 : Blo 327838 492485 := bbase (se 4 (by rfl) ⟨46170, by rfl⟩ : syracuseStep 492485 = 92341) (by norm_num)
theorem B1582021 : Blo 327838 1582021 := bbase (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) (by norm_num)
theorem B558029 : Blo 327838 558029 := bbase (se 3 (by rfl) ⟨104630, by rfl⟩ : syracuseStep 558029 = 209261) (by norm_num)
theorem B369625 : Blo 327838 369625 := bbase (se 2 (by rfl) ⟨138609, by rfl⟩ : syracuseStep 369625 = 277219) (by norm_num)
theorem B738269 : Blo 327838 738269 := bbase (se 3 (by rfl) ⟨138425, by rfl⟩ : syracuseStep 738269 = 276851) (by norm_num)
theorem B492509 : Blo 327838 492509 := bbase (se 3 (by rfl) ⟨92345, by rfl⟩ : syracuseStep 492509 = 184691) (by norm_num)
theorem B492533 : Blo 327838 492533 := bbase (se 5 (by rfl) ⟨23087, by rfl⟩ : syracuseStep 492533 = 46175) (by norm_num)
theorem B394237 : Blo 327838 394237 := bbase (se 3 (by rfl) ⟨73919, by rfl⟩ : syracuseStep 394237 = 147839) (by norm_num)
theorem B369661 : Blo 327838 369661 := bbase (se 3 (by rfl) ⟨69311, by rfl⟩ : syracuseStep 369661 = 138623) (by norm_num)
theorem B492557 : Blo 327838 492557 := bbase (se 3 (by rfl) ⟨92354, by rfl⟩ : syracuseStep 492557 = 184709) (by norm_num)
theorem B623629 : Blo 327838 623629 := bbase (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) (by norm_num)
theorem B369697 : Blo 327838 369697 := bbase (se 2 (by rfl) ⟨138636, by rfl⟩ : syracuseStep 369697 = 277273) (by norm_num)
theorem B738341 : Blo 327838 738341 := bbase (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) (by norm_num)
theorem B492581 : Blo 327838 492581 := bbase (se 4 (by rfl) ⟨46179, by rfl⟩ : syracuseStep 492581 = 92359) (by norm_num)
theorem B468013 : Blo 327838 468013 := bbase (se 3 (by rfl) ⟨87752, by rfl⟩ : syracuseStep 468013 = 175505) (by norm_num)
theorem B492605 : Blo 327838 492605 := bbase (se 3 (by rfl) ⟨92363, by rfl⟩ : syracuseStep 492605 = 184727) (by norm_num)
theorem B836669 : Blo 327838 836669 := bbase (se 3 (by rfl) ⟨156875, by rfl⟩ : syracuseStep 836669 = 313751) (by norm_num)
theorem B369733 : Blo 327838 369733 := bbase (se 4 (by rfl) ⟨34662, by rfl⟩ : syracuseStep 369733 = 69325) (by norm_num)
theorem B492629 : Blo 327838 492629 := bbase (se 8 (by rfl) ⟨2886, by rfl⟩ : syracuseStep 492629 = 5773) (by norm_num)
theorem B369769 : Blo 327838 369769 := bbase (se 2 (by rfl) ⟨138663, by rfl⟩ : syracuseStep 369769 = 277327) (by norm_num)
theorem B738413 : Blo 327838 738413 := bbase (se 3 (by rfl) ⟨138452, by rfl⟩ : syracuseStep 738413 = 276905) (by norm_num)
theorem B492653 : Blo 327838 492653 := bbase (se 3 (by rfl) ⟨92372, by rfl⟩ : syracuseStep 492653 = 184745) (by norm_num)
theorem B492677 : Blo 327838 492677 := bbase (se 4 (by rfl) ⟨46188, by rfl⟩ : syracuseStep 492677 = 92377) (by norm_num)
theorem B1672325 : Blo 327838 1672325 := bbase (se 4 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 1672325 = 313561) (by norm_num)
theorem B369805 : Blo 327838 369805 := bbase (se 3 (by rfl) ⟨69338, by rfl⟩ : syracuseStep 369805 = 138677) (by norm_num)
theorem B468109 : Blo 327838 468109 := bbase (se 3 (by rfl) ⟨87770, by rfl⟩ : syracuseStep 468109 = 175541) (by norm_num)
theorem B492701 : Blo 327838 492701 := bbase (se 3 (by rfl) ⟨92381, by rfl⟩ : syracuseStep 492701 = 184763) (by norm_num)
theorem B1688741 : Blo 327838 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B369841 : Blo 327838 369841 := bbase (se 2 (by rfl) ⟨138690, by rfl⟩ : syracuseStep 369841 = 277381) (by norm_num)
theorem B738485 : Blo 327838 738485 := bbase (se 5 (by rfl) ⟨34616, by rfl⟩ : syracuseStep 738485 = 69233) (by norm_num)
theorem B492725 : Blo 327838 492725 := bbase (se 5 (by rfl) ⟨23096, by rfl⟩ : syracuseStep 492725 = 46193) (by norm_num)
theorem B492749 : Blo 327838 492749 := bbase (se 3 (by rfl) ⟨92390, by rfl⟩ : syracuseStep 492749 = 184781) (by norm_num)
theorem B664789 : Blo 327838 664789 := bbase (se 7 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 664789 = 15581) (by norm_num)
theorem B369877 : Blo 327838 369877 := bbase (se 7 (by rfl) ⟨4334, by rfl⟩ : syracuseStep 369877 = 8669) (by norm_num)
theorem B525541 : Blo 327838 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B492773 : Blo 327838 492773 := bbase (se 4 (by rfl) ⟨46197, by rfl⟩ : syracuseStep 492773 = 92395) (by norm_num)
theorem B369913 : Blo 327838 369913 := bbase (se 2 (by rfl) ⟨138717, by rfl⟩ : syracuseStep 369913 = 277435) (by norm_num)
theorem B738557 : Blo 327838 738557 := bbase (se 3 (by rfl) ⟨138479, by rfl⟩ : syracuseStep 738557 = 276959) (by norm_num)
theorem B492797 : Blo 327838 492797 := bbase (se 3 (by rfl) ⟨92399, by rfl⟩ : syracuseStep 492797 = 184799) (by norm_num)
theorem B3736853 : Blo 327838 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B492821 : Blo 327838 492821 := bbase (se 6 (by rfl) ⟨11550, by rfl⟩ : syracuseStep 492821 = 23101) (by norm_num)
theorem B369949 : Blo 327838 369949 := bbase (se 3 (by rfl) ⟨69365, by rfl⟩ : syracuseStep 369949 = 138731) (by norm_num)
theorem B492845 : Blo 327838 492845 := bbase (se 3 (by rfl) ⟨92408, by rfl⟩ : syracuseStep 492845 = 184817) (by norm_num)
theorem B845101 : Blo 327838 845101 := bbase (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) (by norm_num)
theorem B623933 : Blo 327838 623933 := bbase (se 3 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 623933 = 233975) (by norm_num)
theorem B369985 : Blo 327838 369985 := bbase (se 2 (by rfl) ⟨138744, by rfl⟩ : syracuseStep 369985 = 277489) (by norm_num)
theorem B1107269 : Blo 327838 1107269 := bbase (se 4 (by rfl) ⟨103806, by rfl⟩ : syracuseStep 1107269 = 207613) (by norm_num)
theorem B738629 : Blo 327838 738629 := bbase (se 4 (by rfl) ⟨69246, by rfl⟩ : syracuseStep 738629 = 138493) (by norm_num)
theorem B492869 : Blo 327838 492869 := bbase (se 4 (by rfl) ⟨46206, by rfl⟩ : syracuseStep 492869 = 92413) (by norm_num)
theorem B1115477 : Blo 327838 1115477 := bbase (se 12 (by rfl) ⟨408, by rfl⟩ : syracuseStep 1115477 = 817) (by norm_num)
theorem B492893 : Blo 327838 492893 := bbase (se 3 (by rfl) ⟨92417, by rfl⟩ : syracuseStep 492893 = 184835) (by norm_num)
theorem B370021 : Blo 327838 370021 := bbase (se 4 (by rfl) ⟨34689, by rfl⟩ : syracuseStep 370021 = 69379) (by norm_num)
theorem B492917 : Blo 327838 492917 := bbase (se 5 (by rfl) ⟨23105, by rfl⟩ : syracuseStep 492917 = 46211) (by norm_num)
theorem B714101 : Blo 327838 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B370057 : Blo 327838 370057 := bbase (se 2 (by rfl) ⟨138771, by rfl⟩ : syracuseStep 370057 = 277543) (by norm_num)
theorem B738701 : Blo 327838 738701 := bbase (se 3 (by rfl) ⟨138506, by rfl⟩ : syracuseStep 738701 = 277013) (by norm_num)
theorem B492941 : Blo 327838 492941 := bbase (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) (by norm_num)
theorem B837013 : Blo 327838 837013 := bbase (se 6 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 837013 = 39235) (by norm_num)
theorem B492965 : Blo 327838 492965 := bbase (se 4 (by rfl) ⟨46215, by rfl⟩ : syracuseStep 492965 = 92431) (by norm_num)
theorem B370093 : Blo 327838 370093 := bbase (se 3 (by rfl) ⟨69392, by rfl⟩ : syracuseStep 370093 = 138785) (by norm_num)
theorem B492989 : Blo 327838 492989 := bbase (se 3 (by rfl) ⟨92435, by rfl⟩ : syracuseStep 492989 = 184871) (by norm_num)
theorem B452045 : Blo 327838 452045 := bbase (se 3 (by rfl) ⟨84758, by rfl⟩ : syracuseStep 452045 = 169517) (by norm_num)
theorem B370129 : Blo 327838 370129 := bbase (se 2 (by rfl) ⟨138798, by rfl⟩ : syracuseStep 370129 = 277597) (by norm_num)
theorem B738773 : Blo 327838 738773 := bbase (se 7 (by rfl) ⟨8657, by rfl⟩ : syracuseStep 738773 = 17315) (by norm_num)
theorem B493013 : Blo 327838 493013 := bbase (se 7 (by rfl) ⟨5777, by rfl⟩ : syracuseStep 493013 = 11555) (by norm_num)
theorem B2508245 : Blo 327838 2508245 := bbase (se 7 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 2508245 = 58787) (by norm_num)
theorem B493037 : Blo 327838 493037 := bbase (se 3 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 493037 = 184889) (by norm_num)
theorem B370165 : Blo 327838 370165 := bbase (se 5 (by rfl) ⟨17351, by rfl⟩ : syracuseStep 370165 = 34703) (by norm_num)
theorem B493061 : Blo 327838 493061 := bbase (se 4 (by rfl) ⟨46224, by rfl⟩ : syracuseStep 493061 = 92449) (by norm_num)
theorem B837125 : Blo 327838 837125 := bbase (se 4 (by rfl) ⟨78480, by rfl⟩ : syracuseStep 837125 = 156961) (by norm_num)
theorem B2106901 : Blo 327838 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B370201 : Blo 327838 370201 := bbase (se 2 (by rfl) ⟨138825, by rfl⟩ : syracuseStep 370201 = 277651) (by norm_num)
theorem B738845 : Blo 327838 738845 := bbase (se 3 (by rfl) ⟨138533, by rfl⟩ : syracuseStep 738845 = 277067) (by norm_num)
theorem B493085 : Blo 327838 493085 := bbase (se 3 (by rfl) ⟨92453, by rfl⟩ : syracuseStep 493085 = 184907) (by norm_num)
theorem B1664549 : Blo 327838 1664549 := bbase (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) (by norm_num)
theorem B493109 : Blo 327838 493109 := bbase (se 5 (by rfl) ⟨23114, by rfl⟩ : syracuseStep 493109 = 46229) (by norm_num)
theorem B370237 : Blo 327838 370237 := bbase (se 3 (by rfl) ⟨69419, by rfl⟩ : syracuseStep 370237 = 138839) (by norm_num)
theorem B493133 : Blo 327838 493133 := bbase (se 3 (by rfl) ⟨92462, by rfl⟩ : syracuseStep 493133 = 184925) (by norm_num)
theorem B1222229 : Blo 327838 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B370273 : Blo 327838 370273 := bbase (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) (by norm_num)
theorem B738917 : Blo 327838 738917 := bbase (se 4 (by rfl) ⟨69273, by rfl⟩ : syracuseStep 738917 = 138547) (by norm_num)
theorem B493157 : Blo 327838 493157 := bbase (se 4 (by rfl) ⟨46233, by rfl⟩ : syracuseStep 493157 = 92467) (by norm_num)
theorem B493181 : Blo 327838 493181 := bbase (se 3 (by rfl) ⟨92471, by rfl⟩ : syracuseStep 493181 = 184943) (by norm_num)
theorem B468605 : Blo 327838 468605 := bbase (se 3 (by rfl) ⟨87863, by rfl⟩ : syracuseStep 468605 = 175727) (by norm_num)
theorem B370309 : Blo 327838 370309 := bbase (se 4 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 370309 = 69433) (by norm_num)
theorem B493205 : Blo 327838 493205 := bbase (se 6 (by rfl) ⟨11559, by rfl⟩ : syracuseStep 493205 = 23119) (by norm_num)
theorem B370345 : Blo 327838 370345 := bbase (se 2 (by rfl) ⟨138879, by rfl⟩ : syracuseStep 370345 = 277759) (by norm_num)
theorem B738989 : Blo 327838 738989 := bbase (se 3 (by rfl) ⟨138560, by rfl⟩ : syracuseStep 738989 = 277121) (by norm_num)
theorem B493229 : Blo 327838 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B493253 : Blo 327838 493253 := bbase (se 4 (by rfl) ⟨46242, by rfl⟩ : syracuseStep 493253 = 92485) (by norm_num)
theorem B1058501 : Blo 327838 1058501 := bbase (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) (by norm_num)
theorem B665293 : Blo 327838 665293 := bbase (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) (by norm_num)
theorem B370381 : Blo 327838 370381 := bbase (se 3 (by rfl) ⟨69446, by rfl⟩ : syracuseStep 370381 = 138893) (by norm_num)
theorem B493277 : Blo 327838 493277 := bbase (se 3 (by rfl) ⟨92489, by rfl⟩ : syracuseStep 493277 = 184979) (by norm_num)
theorem B370417 : Blo 327838 370417 := bbase (se 2 (by rfl) ⟨138906, by rfl⟩ : syracuseStep 370417 = 277813) (by norm_num)
theorem B1107701 : Blo 327838 1107701 := bbase (se 5 (by rfl) ⟨51923, by rfl⟩ : syracuseStep 1107701 = 103847) (by norm_num)
theorem B739061 : Blo 327838 739061 := bbase (se 5 (by rfl) ⟨34643, by rfl⟩ : syracuseStep 739061 = 69287) (by norm_num)
theorem B493301 : Blo 327838 493301 := bbase (se 5 (by rfl) ⟨23123, by rfl⟩ : syracuseStep 493301 = 46247) (by norm_num)
theorem B1410821 : Blo 327838 1410821 := bbase (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) (by norm_num)
theorem B493325 : Blo 327838 493325 := bbase (se 3 (by rfl) ⟨92498, by rfl⟩ : syracuseStep 493325 = 184997) (by norm_num)
theorem B370453 : Blo 327838 370453 := bbase (se 6 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 370453 = 17365) (by norm_num)
theorem B706333 : Blo 327838 706333 := bbase (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) (by norm_num)
theorem B493349 : Blo 327838 493349 := bbase (se 4 (by rfl) ⟨46251, by rfl⟩ : syracuseStep 493349 = 92503) (by norm_num)
theorem B1877813 : Blo 327838 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B370489 : Blo 327838 370489 := bbase (se 2 (by rfl) ⟨138933, by rfl⟩ : syracuseStep 370489 = 277867) (by norm_num)
theorem B739133 : Blo 327838 739133 := bbase (se 3 (by rfl) ⟨138587, by rfl⟩ : syracuseStep 739133 = 277175) (by norm_num)
theorem B493373 : Blo 327838 493373 := bbase (se 3 (by rfl) ⟨92507, by rfl⟩ : syracuseStep 493373 = 185015) (by norm_num)
theorem B1058629 : Blo 327838 1058629 := bbase (se 4 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 1058629 = 198493) (by norm_num)
theorem B493397 : Blo 327838 493397 := bbase (se 9 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 493397 = 2891) (by norm_num)
theorem B370525 : Blo 327838 370525 := bbase (se 3 (by rfl) ⟨69473, by rfl⟩ : syracuseStep 370525 = 138947) (by norm_num)
theorem B493421 : Blo 327838 493421 := bbase (se 3 (by rfl) ⟨92516, by rfl⟩ : syracuseStep 493421 = 185033) (by norm_num)
theorem B1181557 : Blo 327838 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B2500469 : Blo 327838 2500469 := bbase (se 5 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 2500469 = 234419) (by norm_num)
theorem B370561 : Blo 327838 370561 := bbase (se 2 (by rfl) ⟨138960, by rfl⟩ : syracuseStep 370561 = 277921) (by norm_num)
theorem B1402757 : Blo 327838 1402757 := bbase (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) (by norm_num)
theorem B526213 : Blo 327838 526213 := bbase (se 4 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 526213 = 98665) (by norm_num)
theorem B739205 : Blo 327838 739205 := bbase (se 4 (by rfl) ⟨69300, by rfl⟩ : syracuseStep 739205 = 138601) (by norm_num)
theorem B493445 : Blo 327838 493445 := bbase (se 4 (by rfl) ⟨46260, by rfl⟩ : syracuseStep 493445 = 92521) (by norm_num)
theorem B493469 : Blo 327838 493469 := bbase (se 3 (by rfl) ⟨92525, by rfl⟩ : syracuseStep 493469 = 185051) (by norm_num)
theorem B370597 : Blo 327838 370597 := bbase (se 4 (by rfl) ⟨34743, by rfl⟩ : syracuseStep 370597 = 69487) (by norm_num)
theorem B1869749 : Blo 327838 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B493493 : Blo 327838 493493 := bbase (se 5 (by rfl) ⟨23132, by rfl⟩ : syracuseStep 493493 = 46265) (by norm_num)
theorem B370633 : Blo 327838 370633 := bbase (se 2 (by rfl) ⟨138987, by rfl⟩ : syracuseStep 370633 = 277975) (by norm_num)
theorem B739277 : Blo 327838 739277 := bbase (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) (by norm_num)
theorem B493517 : Blo 327838 493517 := bbase (se 3 (by rfl) ⟨92534, by rfl⟩ : syracuseStep 493517 = 185069) (by norm_num)
theorem B493541 : Blo 327838 493541 := bbase (se 4 (by rfl) ⟨46269, by rfl⟩ : syracuseStep 493541 = 92539) (by norm_num)
theorem B370669 : Blo 327838 370669 := bbase (se 3 (by rfl) ⟨69500, by rfl⟩ : syracuseStep 370669 = 139001) (by norm_num)
theorem B591869 : Blo 327838 591869 := bbase (se 3 (by rfl) ⟨110975, by rfl⟩ : syracuseStep 591869 = 221951) (by norm_num)
theorem B493565 : Blo 327838 493565 := bbase (se 3 (by rfl) ⟨92543, by rfl⟩ : syracuseStep 493565 = 185087) (by norm_num)
theorem B370705 : Blo 327838 370705 := bbase (se 2 (by rfl) ⟨139014, by rfl⟩ : syracuseStep 370705 = 278029) (by norm_num)
theorem B739349 : Blo 327838 739349 := bbase (se 6 (by rfl) ⟨17328, by rfl⟩ : syracuseStep 739349 = 34657) (by norm_num)
theorem B395285 : Blo 327838 395285 := bbase (se 6 (by rfl) ⟨9264, by rfl⟩ : syracuseStep 395285 = 18529) (by norm_num)
theorem B493589 : Blo 327838 493589 := bbase (se 6 (by rfl) ⟨11568, by rfl⟩ : syracuseStep 493589 = 23137) (by norm_num)
theorem B1255445 : Blo 327838 1255445 := bbase (se 6 (by rfl) ⟨29424, by rfl⟩ : syracuseStep 1255445 = 58849) (by norm_num)
theorem B624685 : Blo 327838 624685 := bbase (se 3 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 624685 = 234257) (by norm_num)
theorem B493613 : Blo 327838 493613 := bbase (se 3 (by rfl) ⟨92552, by rfl⟩ : syracuseStep 493613 = 185105) (by norm_num)
theorem B370741 : Blo 327838 370741 := bbase (se 5 (by rfl) ⟨17378, by rfl⟩ : syracuseStep 370741 = 34757) (by norm_num)
theorem B493637 : Blo 327838 493637 := bbase (se 4 (by rfl) ⟨46278, by rfl⟩ : syracuseStep 493637 = 92557) (by norm_num)
theorem B1058885 : Blo 327838 1058885 := bbase (se 4 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 1058885 = 198541) (by norm_num)
theorem B370777 : Blo 327838 370777 := bbase (se 2 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 370777 = 278083) (by norm_num)
theorem B739421 : Blo 327838 739421 := bbase (se 3 (by rfl) ⟨138641, by rfl⟩ : syracuseStep 739421 = 277283) (by norm_num)
theorem B493661 : Blo 327838 493661 := bbase (se 3 (by rfl) ⟨92561, by rfl⟩ : syracuseStep 493661 = 185123) (by norm_num)
theorem B493685 : Blo 327838 493685 := bbase (se 5 (by rfl) ⟨23141, by rfl⟩ : syracuseStep 493685 = 46283) (by norm_num)
theorem B370813 : Blo 327838 370813 := bbase (se 3 (by rfl) ⟨69527, by rfl⟩ : syracuseStep 370813 = 139055) (by norm_num)
theorem B493709 : Blo 327838 493709 := bbase (se 3 (by rfl) ⟨92570, by rfl⟩ : syracuseStep 493709 = 185141) (by norm_num)
theorem B370849 : Blo 327838 370849 := bbase (se 2 (by rfl) ⟨139068, by rfl⟩ : syracuseStep 370849 = 278137) (by norm_num)
theorem B1108133 : Blo 327838 1108133 := bbase (se 4 (by rfl) ⟨103887, by rfl⟩ : syracuseStep 1108133 = 207775) (by norm_num)
theorem B739493 : Blo 327838 739493 := bbase (se 4 (by rfl) ⟨69327, by rfl⟩ : syracuseStep 739493 = 138655) (by norm_num)
theorem B493733 : Blo 327838 493733 := bbase (se 4 (by rfl) ⟨46287, by rfl⟩ : syracuseStep 493733 = 92575) (by norm_num)
theorem B469157 : Blo 327838 469157 := bbase (se 4 (by rfl) ⟨43983, by rfl⟩ : syracuseStep 469157 = 87967) (by norm_num)
theorem B624829 : Blo 327838 624829 := bbase (se 3 (by rfl) ⟨117155, by rfl⟩ : syracuseStep 624829 = 234311) (by norm_num)
theorem B493757 : Blo 327838 493757 := bbase (se 3 (by rfl) ⟨92579, by rfl⟩ : syracuseStep 493757 = 185159) (by norm_num)
theorem B370885 : Blo 327838 370885 := bbase (se 4 (by rfl) ⟨34770, by rfl⟩ : syracuseStep 370885 = 69541) (by norm_num)
theorem B493781 : Blo 327838 493781 := bbase (se 7 (by rfl) ⟨5786, by rfl⟩ : syracuseStep 493781 = 11573) (by norm_num)
theorem B3565781 : Blo 327838 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B370921 : Blo 327838 370921 := bbase (se 2 (by rfl) ⟨139095, by rfl⟩ : syracuseStep 370921 = 278191) (by norm_num)
theorem B600301 : Blo 327838 600301 := bbase (se 3 (by rfl) ⟨112556, by rfl⟩ : syracuseStep 600301 = 225113) (by norm_num)
theorem B739565 : Blo 327838 739565 := bbase (se 3 (by rfl) ⟨138668, by rfl⟩ : syracuseStep 739565 = 277337) (by norm_num)
theorem B493805 : Blo 327838 493805 := bbase (se 3 (by rfl) ⟨92588, by rfl⟩ : syracuseStep 493805 = 185177) (by norm_num)
theorem B493829 : Blo 327838 493829 := bbase (se 4 (by rfl) ⟨46296, by rfl⟩ : syracuseStep 493829 = 92593) (by norm_num)
theorem B444685 : Blo 327838 444685 := bbase (se 3 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 444685 = 166757) (by norm_num)
theorem B370957 : Blo 327838 370957 := bbase (se 3 (by rfl) ⟨69554, by rfl⟩ : syracuseStep 370957 = 139109) (by norm_num)
theorem B2492693 : Blo 327838 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B493853 : Blo 327838 493853 := bbase (se 3 (by rfl) ⟨92597, by rfl⟩ : syracuseStep 493853 = 185195) (by norm_num)
theorem B788773 : Blo 327838 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B526637 : Blo 327838 526637 := bbase (se 3 (by rfl) ⟨98744, by rfl⟩ : syracuseStep 526637 = 197489) (by norm_num)
theorem B370993 : Blo 327838 370993 := bbase (se 2 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 370993 = 278245) (by norm_num)
theorem B739637 : Blo 327838 739637 := bbase (se 5 (by rfl) ⟨34670, by rfl⟩ : syracuseStep 739637 = 69341) (by norm_num)
theorem B493877 : Blo 327838 493877 := bbase (se 5 (by rfl) ⟨23150, by rfl⟩ : syracuseStep 493877 = 46301) (by norm_num)
theorem B1255733 : Blo 327838 1255733 := bbase (se 5 (by rfl) ⟨58862, by rfl⟩ : syracuseStep 1255733 = 117725) (by norm_num)
theorem B493901 : Blo 327838 493901 := bbase (se 3 (by rfl) ⟨92606, by rfl⟩ : syracuseStep 493901 = 185213) (by norm_num)
theorem B371029 : Blo 327838 371029 := bbase (se 10 (by rfl) ⟨543, by rfl⟩ : syracuseStep 371029 = 1087) (by norm_num)
theorem B624989 : Blo 327838 624989 := bbase (se 3 (by rfl) ⟨117185, by rfl⟩ : syracuseStep 624989 = 234371) (by norm_num)
theorem B395617 : Blo 327838 395617 := bbase (se 2 (by rfl) ⟨148356, by rfl⟩ : syracuseStep 395617 = 296713) (by norm_num)
theorem B493925 : Blo 327838 493925 := bbase (se 4 (by rfl) ⟨46305, by rfl⟩ : syracuseStep 493925 = 92611) (by norm_num)
theorem B371065 : Blo 327838 371065 := bbase (se 2 (by rfl) ⟨139149, by rfl⟩ : syracuseStep 371065 = 278299) (by norm_num)
theorem B739709 : Blo 327838 739709 := bbase (se 3 (by rfl) ⟨138695, by rfl⟩ : syracuseStep 739709 = 277391) (by norm_num)
theorem B493949 : Blo 327838 493949 := bbase (se 3 (by rfl) ⟨92615, by rfl⟩ : syracuseStep 493949 = 185231) (by norm_num)
theorem B747917 : Blo 327838 747917 := bbase (se 3 (by rfl) ⟨140234, by rfl⟩ : syracuseStep 747917 = 280469) (by norm_num)
theorem B493973 : Blo 327838 493973 := bbase (se 6 (by rfl) ⟨11577, by rfl⟩ : syracuseStep 493973 = 23155) (by norm_num)
theorem B1673621 : Blo 327838 1673621 := bbase (se 6 (by rfl) ⟨39225, by rfl⟩ : syracuseStep 1673621 = 78451) (by norm_num)
theorem B371101 : Blo 327838 371101 := bbase (se 3 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 371101 = 139163) (by norm_num)
theorem B493997 : Blo 327838 493997 := bbase (se 3 (by rfl) ⟨92624, by rfl⟩ : syracuseStep 493997 = 185249) (by norm_num)
theorem B1247669 : Blo 327838 1247669 := bbase (se 5 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 1247669 = 116969) (by norm_num)
theorem B829885 : Blo 327838 829885 := bbase (se 3 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 829885 = 311207) (by norm_num)
theorem B338369 : Blo 327838 338369 := bbase (se 2 (by rfl) ⟨126888, by rfl⟩ : syracuseStep 338369 = 253777) (by norm_num)
theorem B371137 : Blo 327838 371137 := bbase (se 2 (by rfl) ⟨139176, by rfl⟩ : syracuseStep 371137 = 278353) (by norm_num)
theorem B739781 : Blo 327838 739781 := bbase (se 4 (by rfl) ⟨69354, by rfl⟩ : syracuseStep 739781 = 138709) (by norm_num)
theorem B494021 : Blo 327838 494021 := bbase (se 4 (by rfl) ⟨46314, by rfl⟩ : syracuseStep 494021 = 92629) (by norm_num)
theorem B1051093 : Blo 327838 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B534997 : Blo 327838 534997 := bbase (se 7 (by rfl) ⟨6269, by rfl⟩ : syracuseStep 534997 = 12539) (by norm_num)
theorem B494045 : Blo 327838 494045 := bbase (se 3 (by rfl) ⟨92633, by rfl⟩ : syracuseStep 494045 = 185267) (by norm_num)
theorem B846301 : Blo 327838 846301 := bbase (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) (by norm_num)
theorem B444901 : Blo 327838 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B371173 : Blo 327838 371173 := bbase (se 4 (by rfl) ⟨34797, by rfl⟩ : syracuseStep 371173 = 69595) (by norm_num)
theorem B625133 : Blo 327838 625133 := bbase (se 3 (by rfl) ⟨117212, by rfl⟩ : syracuseStep 625133 = 234425) (by norm_num)
theorem B494069 : Blo 327838 494069 := bbase (se 5 (by rfl) ⟨23159, by rfl⟩ : syracuseStep 494069 = 46319) (by norm_num)
theorem B371209 : Blo 327838 371209 := bbase (se 2 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 371209 = 278407) (by norm_num)
theorem B739853 : Blo 327838 739853 := bbase (se 3 (by rfl) ⟨138722, by rfl⟩ : syracuseStep 739853 = 277445) (by norm_num)
theorem B494093 : Blo 327838 494093 := bbase (se 3 (by rfl) ⟨92642, by rfl⟩ : syracuseStep 494093 = 185285) (by norm_num)
theorem B494117 : Blo 327838 494117 := bbase (se 4 (by rfl) ⟨46323, by rfl⟩ : syracuseStep 494117 = 92647) (by norm_num)
theorem B829997 : Blo 327838 829997 := bbase (se 3 (by rfl) ⟨155624, by rfl⟩ : syracuseStep 829997 = 311249) (by norm_num)
theorem B371245 : Blo 327838 371245 := bbase (se 3 (by rfl) ⟨69608, by rfl⟩ : syracuseStep 371245 = 139217) (by norm_num)
theorem B494141 : Blo 327838 494141 := bbase (se 3 (by rfl) ⟨92651, by rfl⟩ : syracuseStep 494141 = 185303) (by norm_num)
theorem B526925 : Blo 327838 526925 := bbase (se 3 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 526925 = 197597) (by norm_num)
theorem B371281 : Blo 327838 371281 := bbase (se 2 (by rfl) ⟨139230, by rfl⟩ : syracuseStep 371281 = 278461) (by norm_num)
theorem B1108565 : Blo 327838 1108565 := bbase (se 8 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 1108565 = 12991) (by norm_num)
theorem B739925 : Blo 327838 739925 := bbase (se 8 (by rfl) ⟨4335, by rfl⟩ : syracuseStep 739925 = 8671) (by norm_num)
theorem B494165 : Blo 327838 494165 := bbase (se 8 (by rfl) ⟨2895, by rfl⟩ : syracuseStep 494165 = 5791) (by norm_num)
theorem B502357 : Blo 327838 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B494189 : Blo 327838 494189 := bbase (se 3 (by rfl) ⟨92660, by rfl⟩ : syracuseStep 494189 = 185321) (by norm_num)
theorem B846445 : Blo 327838 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B371317 : Blo 327838 371317 := bbase (se 5 (by rfl) ⟨17405, by rfl⟩ : syracuseStep 371317 = 34811) (by norm_num)
theorem B494213 : Blo 327838 494213 := bbase (se 4 (by rfl) ⟨46332, by rfl⟩ : syracuseStep 494213 = 92665) (by norm_num)
theorem B1428101 : Blo 327838 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B371353 : Blo 327838 371353 := bbase (se 2 (by rfl) ⟨139257, by rfl⟩ : syracuseStep 371353 = 278515) (by norm_num)
theorem B739997 : Blo 327838 739997 := bbase (se 3 (by rfl) ⟨138749, by rfl⟩ : syracuseStep 739997 = 277499) (by norm_num)
theorem B494237 : Blo 327838 494237 := bbase (se 3 (by rfl) ⟨92669, by rfl⟩ : syracuseStep 494237 = 185339) (by norm_num)
theorem B3156661 : Blo 327838 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B936629 : Blo 327838 936629 := bbase (se 5 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 936629 = 87809) (by norm_num)
theorem B494261 : Blo 327838 494261 := bbase (se 5 (by rfl) ⟨23168, by rfl⟩ : syracuseStep 494261 = 46337) (by norm_num)
theorem B371389 : Blo 327838 371389 := bbase (se 3 (by rfl) ⟨69635, by rfl⟩ : syracuseStep 371389 = 139271) (by norm_num)
theorem B494285 : Blo 327838 494285 := bbase (se 3 (by rfl) ⟨92678, by rfl⟩ : syracuseStep 494285 = 185357) (by norm_num)
theorem B1247957 : Blo 327838 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B371425 : Blo 327838 371425 := bbase (se 2 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 371425 = 278569) (by norm_num)
theorem B740069 : Blo 327838 740069 := bbase (se 4 (by rfl) ⟨69381, by rfl⟩ : syracuseStep 740069 = 138763) (by norm_num)
theorem B494309 : Blo 327838 494309 := bbase (se 4 (by rfl) ⟨46341, by rfl⟩ : syracuseStep 494309 = 92683) (by norm_num)
theorem B830189 : Blo 327838 830189 := bbase (se 3 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 830189 = 311321) (by norm_num)
theorem B494333 : Blo 327838 494333 := bbase (se 3 (by rfl) ⟨92687, by rfl⟩ : syracuseStep 494333 = 185375) (by norm_num)
theorem B371461 : Blo 327838 371461 := bbase (se 4 (by rfl) ⟨34824, by rfl⟩ : syracuseStep 371461 = 69649) (by norm_num)
theorem B625421 : Blo 327838 625421 := bbase (se 3 (by rfl) ⟨117266, by rfl⟩ : syracuseStep 625421 = 234533) (by norm_num)
theorem B494357 : Blo 327838 494357 := bbase (se 6 (by rfl) ⟨11586, by rfl⟩ : syracuseStep 494357 = 23173) (by norm_num)
theorem B371497 : Blo 327838 371497 := bbase (se 2 (by rfl) ⟨139311, by rfl⟩ : syracuseStep 371497 = 278623) (by norm_num)
theorem B740141 : Blo 327838 740141 := bbase (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) (by norm_num)
theorem B494381 : Blo 327838 494381 := bbase (se 3 (by rfl) ⟨92696, by rfl⟩ : syracuseStep 494381 = 185393) (by norm_num)
theorem B1665845 : Blo 327838 1665845 := bbase (se 5 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 1665845 = 156173) (by norm_num)
theorem B494405 : Blo 327838 494405 := bbase (se 4 (by rfl) ⟨46350, by rfl⟩ : syracuseStep 494405 = 92701) (by norm_num)
theorem B371533 : Blo 327838 371533 := bbase (se 3 (by rfl) ⟨69662, by rfl⟩ : syracuseStep 371533 = 139325) (by norm_num)
theorem B1115909 : Blo 327838 1115909 := bbase (se 4 (by rfl) ⟨104616, by rfl⟩ : syracuseStep 1115909 = 209233) (by norm_num)
theorem B494429 : Blo 327838 494429 := bbase (se 3 (by rfl) ⟨92705, by rfl⟩ : syracuseStep 494429 = 185411) (by norm_num)
theorem B371569 : Blo 327838 371569 := bbase (se 2 (by rfl) ⟨139338, by rfl⟩ : syracuseStep 371569 = 278677) (by norm_num)
theorem B740213 : Blo 327838 740213 := bbase (se 5 (by rfl) ⟨34697, by rfl⟩ : syracuseStep 740213 = 69395) (by norm_num)
theorem B494453 : Blo 327838 494453 := bbase (se 5 (by rfl) ⟨23177, by rfl⟩ : syracuseStep 494453 = 46355) (by norm_num)
theorem B789389 : Blo 327838 789389 := bbase (se 3 (by rfl) ⟨148010, by rfl⟩ : syracuseStep 789389 = 296021) (by norm_num)
theorem B494477 : Blo 327838 494477 := bbase (se 3 (by rfl) ⟨92714, by rfl⟩ : syracuseStep 494477 = 185429) (by norm_num)
theorem B469909 : Blo 327838 469909 := bbase (se 6 (by rfl) ⟨11013, by rfl⟩ : syracuseStep 469909 = 22027) (by norm_num)
theorem B3173269 : Blo 327838 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B371605 : Blo 327838 371605 := bbase (se 6 (by rfl) ⟨8709, by rfl⟩ : syracuseStep 371605 = 17419) (by norm_num)
theorem B625573 : Blo 327838 625573 := bbase (se 4 (by rfl) ⟨58647, by rfl⟩ : syracuseStep 625573 = 117295) (by norm_num)
theorem B494501 : Blo 327838 494501 := bbase (se 4 (by rfl) ⟨46359, by rfl⟩ : syracuseStep 494501 = 92719) (by norm_num)
theorem B355249 : Blo 327838 355249 := bbase (se 2 (by rfl) ⟨133218, by rfl⟩ : syracuseStep 355249 = 266437) (by norm_num)
theorem B371641 : Blo 327838 371641 := bbase (se 2 (by rfl) ⟨139365, by rfl⟩ : syracuseStep 371641 = 278731) (by norm_num)
theorem B740285 : Blo 327838 740285 := bbase (se 3 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 740285 = 277607) (by norm_num)
theorem B494525 : Blo 327838 494525 := bbase (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) (by norm_num)
theorem B494549 : Blo 327838 494549 := bbase (se 7 (by rfl) ⟨5795, by rfl⟩ : syracuseStep 494549 = 11591) (by norm_num)
theorem B1878997 : Blo 327838 1878997 := bbase (se 7 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 1878997 = 44039) (by norm_num)
theorem B371677 : Blo 327838 371677 := bbase (se 3 (by rfl) ⟨69689, by rfl⟩ : syracuseStep 371677 = 139379) (by norm_num)
theorem B494573 : Blo 327838 494573 := bbase (se 3 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 494573 = 185465) (by norm_num)
theorem B371713 : Blo 327838 371713 := bbase (se 2 (by rfl) ⟨139392, by rfl⟩ : syracuseStep 371713 = 278785) (by norm_num)
theorem B1108997 : Blo 327838 1108997 := bbase (se 4 (by rfl) ⟨103968, by rfl⟩ : syracuseStep 1108997 = 207937) (by norm_num)
theorem B740357 : Blo 327838 740357 := bbase (se 4 (by rfl) ⟨69408, by rfl⟩ : syracuseStep 740357 = 138817) (by norm_num)
theorem B494597 : Blo 327838 494597 := bbase (se 4 (by rfl) ⟨46368, by rfl⟩ : syracuseStep 494597 = 92737) (by norm_num)
theorem B494621 : Blo 327838 494621 := bbase (se 3 (by rfl) ⟨92741, by rfl⟩ : syracuseStep 494621 = 185483) (by norm_num)
theorem B371749 : Blo 327838 371749 := bbase (se 4 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 371749 = 69703) (by norm_num)
theorem B494645 : Blo 327838 494645 := bbase (se 5 (by rfl) ⟨23186, by rfl⟩ : syracuseStep 494645 = 46373) (by norm_num)
theorem B830533 : Blo 327838 830533 := bbase (se 4 (by rfl) ⟨77862, by rfl⟩ : syracuseStep 830533 = 155725) (by norm_num)
theorem B371785 : Blo 327838 371785 := bbase (se 2 (by rfl) ⟨139419, by rfl⟩ : syracuseStep 371785 = 278839) (by norm_num)
theorem B740429 : Blo 327838 740429 := bbase (se 3 (by rfl) ⟨138830, by rfl⟩ : syracuseStep 740429 = 277661) (by norm_num)
theorem B494669 : Blo 327838 494669 := bbase (se 3 (by rfl) ⟨92750, by rfl⟩ : syracuseStep 494669 = 185501) (by norm_num)
theorem B494693 : Blo 327838 494693 := bbase (se 4 (by rfl) ⟨46377, by rfl⟩ : syracuseStep 494693 = 92755) (by norm_num)
theorem B371821 : Blo 327838 371821 := bbase (se 3 (by rfl) ⟨69716, by rfl⟩ : syracuseStep 371821 = 139433) (by norm_num)
theorem B494717 : Blo 327838 494717 := bbase (se 3 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 494717 = 185519) (by norm_num)
theorem B371857 : Blo 327838 371857 := bbase (se 2 (by rfl) ⟨139446, by rfl⟩ : syracuseStep 371857 = 278893) (by norm_num)
theorem B740501 : Blo 327838 740501 := bbase (se 6 (by rfl) ⟨17355, by rfl⟩ : syracuseStep 740501 = 34711) (by norm_num)
theorem B494741 : Blo 327838 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B494765 : Blo 327838 494765 := bbase (se 3 (by rfl) ⟨92768, by rfl⟩ : syracuseStep 494765 = 185537) (by norm_num)
theorem B830645 : Blo 327838 830645 := bbase (se 5 (by rfl) ⟨38936, by rfl⟩ : syracuseStep 830645 = 77873) (by norm_num)
theorem B371893 : Blo 327838 371893 := bbase (se 5 (by rfl) ⟨17432, by rfl⟩ : syracuseStep 371893 = 34865) (by norm_num)
theorem B494789 : Blo 327838 494789 := bbase (se 4 (by rfl) ⟨46386, by rfl⟩ : syracuseStep 494789 = 92773) (by norm_num)
theorem B625877 : Blo 327838 625877 := bbase (se 7 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 625877 = 14669) (by norm_num)
theorem B1338581 : Blo 327838 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B396505 : Blo 327838 396505 := bbase (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) (by norm_num)
theorem B371929 : Blo 327838 371929 := bbase (se 2 (by rfl) ⟨139473, by rfl⟩ : syracuseStep 371929 = 278947) (by norm_num)
theorem B740573 : Blo 327838 740573 := bbase (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) (by norm_num)
theorem B494813 : Blo 327838 494813 := bbase (se 3 (by rfl) ⟨92777, by rfl⟩ : syracuseStep 494813 = 185555) (by norm_num)
theorem B494837 : Blo 327838 494837 := bbase (se 5 (by rfl) ⟨23195, by rfl⟩ : syracuseStep 494837 = 46391) (by norm_num)
theorem B371965 : Blo 327838 371965 := bbase (se 3 (by rfl) ⟨69743, by rfl⟩ : syracuseStep 371965 = 139487) (by norm_num)
theorem B494861 : Blo 327838 494861 := bbase (se 3 (by rfl) ⟨92786, by rfl⟩ : syracuseStep 494861 = 185573) (by norm_num)
theorem B593173 : Blo 327838 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B372001 : Blo 327838 372001 := bbase (se 2 (by rfl) ⟨139500, by rfl⟩ : syracuseStep 372001 = 279001) (by norm_num)
theorem B740645 : Blo 327838 740645 := bbase (se 4 (by rfl) ⟨69435, by rfl⟩ : syracuseStep 740645 = 138871) (by norm_num)
theorem B494885 : Blo 327838 494885 := bbase (se 4 (by rfl) ⟨46395, by rfl⟩ : syracuseStep 494885 = 92791) (by norm_num)
theorem B494909 : Blo 327838 494909 := bbase (se 3 (by rfl) ⟨92795, by rfl⟩ : syracuseStep 494909 = 185591) (by norm_num)
theorem B372037 : Blo 327838 372037 := bbase (se 4 (by rfl) ⟨34878, by rfl⟩ : syracuseStep 372037 = 69757) (by norm_num)
theorem B494933 : Blo 327838 494933 := bbase (se 11 (by rfl) ⟨362, by rfl⟩ : syracuseStep 494933 = 725) (by norm_num)
theorem B372073 : Blo 327838 372073 := bbase (se 2 (by rfl) ⟨139527, by rfl⟩ : syracuseStep 372073 = 279055) (by norm_num)
theorem B740717 : Blo 327838 740717 := bbase (se 3 (by rfl) ⟨138884, by rfl⟩ : syracuseStep 740717 = 277769) (by norm_num)
theorem B527725 : Blo 327838 527725 := bbase (se 3 (by rfl) ⟨98948, by rfl⟩ : syracuseStep 527725 = 197897) (by norm_num)
theorem B494957 : Blo 327838 494957 := bbase (se 3 (by rfl) ⟨92804, by rfl⟩ : syracuseStep 494957 = 185609) (by norm_num)
theorem B1011061 : Blo 327838 1011061 := bbase (se 5 (by rfl) ⟨47393, by rfl⟩ : syracuseStep 1011061 = 94787) (by norm_num)
theorem B830837 : Blo 327838 830837 := bbase (se 5 (by rfl) ⟨38945, by rfl⟩ : syracuseStep 830837 = 77891) (by norm_num)
theorem B494981 : Blo 327838 494981 := bbase (se 4 (by rfl) ⟨46404, by rfl⟩ : syracuseStep 494981 = 92809) (by norm_num)
theorem B495005 : Blo 327838 495005 := bbase (se 3 (by rfl) ⟨92813, by rfl⟩ : syracuseStep 495005 = 185627) (by norm_num)
theorem B1109429 : Blo 327838 1109429 := bbase (se 5 (by rfl) ⟨52004, by rfl⟩ : syracuseStep 1109429 = 104009) (by norm_num)
theorem B740789 : Blo 327838 740789 := bbase (se 5 (by rfl) ⟨34724, by rfl⟩ : syracuseStep 740789 = 69449) (by norm_num)
theorem B495029 : Blo 327838 495029 := bbase (se 5 (by rfl) ⟨23204, by rfl⟩ : syracuseStep 495029 = 46409) (by norm_num)
theorem B495053 : Blo 327838 495053 := bbase (se 3 (by rfl) ⟨92822, by rfl⟩ : syracuseStep 495053 = 185645) (by norm_num)
theorem B855517 : Blo 327838 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B847325 : Blo 327838 847325 := bbase (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) (by norm_num)
theorem B667109 : Blo 327838 667109 := bbase (se 4 (by rfl) ⟨62541, by rfl⟩ : syracuseStep 667109 = 125083) (by norm_num)
theorem B495077 : Blo 327838 495077 := bbase (se 4 (by rfl) ⟨46413, by rfl⟩ : syracuseStep 495077 = 92827) (by norm_num)
theorem B740861 : Blo 327838 740861 := bbase (se 3 (by rfl) ⟨138911, by rfl⟩ : syracuseStep 740861 = 277823) (by norm_num)
theorem B495101 : Blo 327838 495101 := bbase (se 3 (by rfl) ⟨92831, by rfl⟩ : syracuseStep 495101 = 185663) (by norm_num)
theorem B495125 : Blo 327838 495125 := bbase (se 6 (by rfl) ⟨11604, by rfl⟩ : syracuseStep 495125 = 23209) (by norm_num)
theorem B495149 : Blo 327838 495149 := bbase (se 3 (by rfl) ⟨92840, by rfl⟩ : syracuseStep 495149 = 185681) (by norm_num)
theorem B1691189 : Blo 327838 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B740933 : Blo 327838 740933 := bbase (se 4 (by rfl) ⟨69462, by rfl⟩ : syracuseStep 740933 = 138925) (by norm_num)
theorem B495173 : Blo 327838 495173 := bbase (se 4 (by rfl) ⟨46422, by rfl⟩ : syracuseStep 495173 = 92845) (by norm_num)
theorem B495197 : Blo 327838 495197 := bbase (se 3 (by rfl) ⟨92849, by rfl⟩ : syracuseStep 495197 = 185699) (by norm_num)
theorem B1404533 : Blo 327838 1404533 := bbase (se 5 (by rfl) ⟨65837, by rfl⟩ : syracuseStep 1404533 = 131675) (by norm_num)
theorem B495221 : Blo 327838 495221 := bbase (se 5 (by rfl) ⟨23213, by rfl⟩ : syracuseStep 495221 = 46427) (by norm_num)
theorem B790157 : Blo 327838 790157 := bbase (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) (by norm_num)
theorem B741005 : Blo 327838 741005 := bbase (se 3 (by rfl) ⟨138938, by rfl⟩ : syracuseStep 741005 = 277877) (by norm_num)
theorem B495245 : Blo 327838 495245 := bbase (se 3 (by rfl) ⟨92858, by rfl⟩ : syracuseStep 495245 = 185717) (by norm_num)
theorem B790165 : Blo 327838 790165 := bbase (se 6 (by rfl) ⟨18519, by rfl⟩ : syracuseStep 790165 = 37039) (by norm_num)
theorem B421529 : Blo 327838 421529 := bbase (se 2 (by rfl) ⟨158073, by rfl⟩ : syracuseStep 421529 = 316147) (by norm_num)
theorem B495269 : Blo 327838 495269 := bbase (se 4 (by rfl) ⟨46431, by rfl⟩ : syracuseStep 495269 = 92863) (by norm_num)
theorem B470701 : Blo 327838 470701 := bbase (se 3 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 470701 = 176513) (by norm_num)
theorem B2248373 : Blo 327838 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B495293 : Blo 327838 495293 := bbase (se 3 (by rfl) ⟨92867, by rfl⟩ : syracuseStep 495293 = 185735) (by norm_num)
theorem B831181 : Blo 327838 831181 := bbase (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) (by norm_num)
theorem B741077 : Blo 327838 741077 := bbase (se 7 (by rfl) ⟨8684, by rfl⟩ : syracuseStep 741077 = 17369) (by norm_num)
theorem B495317 : Blo 327838 495317 := bbase (se 7 (by rfl) ⟨5804, by rfl⟩ : syracuseStep 495317 = 11609) (by norm_num)
theorem B495341 : Blo 327838 495341 := bbase (se 3 (by rfl) ⟨92876, by rfl⟩ : syracuseStep 495341 = 185753) (by norm_num)
theorem B495365 : Blo 327838 495365 := bbase (se 4 (by rfl) ⟨46440, by rfl⟩ : syracuseStep 495365 = 92881) (by norm_num)
theorem B593677 : Blo 327838 593677 := bbase (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) (by norm_num)
theorem B741149 : Blo 327838 741149 := bbase (se 3 (by rfl) ⟨138965, by rfl⟩ : syracuseStep 741149 = 277931) (by norm_num)
theorem B495389 : Blo 327838 495389 := bbase (se 3 (by rfl) ⟨92885, by rfl⟩ : syracuseStep 495389 = 185771) (by norm_num)
theorem B1052453 : Blo 327838 1052453 := bbase (se 4 (by rfl) ⟨98667, by rfl⟩ : syracuseStep 1052453 = 197335) (by norm_num)
theorem B495413 : Blo 327838 495413 := bbase (se 5 (by rfl) ⟨23222, by rfl⟩ : syracuseStep 495413 = 46445) (by norm_num)
theorem B831293 : Blo 327838 831293 := bbase (se 3 (by rfl) ⟨155867, by rfl⟩ : syracuseStep 831293 = 311735) (by norm_num)
theorem B495437 : Blo 327838 495437 := bbase (se 3 (by rfl) ⟨92894, by rfl⟩ : syracuseStep 495437 = 185789) (by norm_num)
theorem B937813 : Blo 327838 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B2117461 : Blo 327838 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B1109861 : Blo 327838 1109861 := bbase (se 4 (by rfl) ⟨104049, by rfl⟩ : syracuseStep 1109861 = 208099) (by norm_num)
theorem B1404773 : Blo 327838 1404773 := bbase (se 4 (by rfl) ⟨131697, by rfl⟩ : syracuseStep 1404773 = 263395) (by norm_num)
theorem B741221 : Blo 327838 741221 := bbase (se 4 (by rfl) ⟨69489, by rfl⟩ : syracuseStep 741221 = 138979) (by norm_num)
theorem B495461 : Blo 327838 495461 := bbase (se 4 (by rfl) ⟨46449, by rfl⟩ : syracuseStep 495461 = 92899) (by norm_num)
theorem B2666357 : Blo 327838 2666357 := bbase (se 5 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 2666357 = 249971) (by norm_num)
theorem B1249141 : Blo 327838 1249141 := bbase (se 5 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 1249141 = 117107) (by norm_num)
theorem B700285 : Blo 327838 700285 := bbase (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) (by norm_num)
theorem B495485 : Blo 327838 495485 := bbase (se 3 (by rfl) ⟨92903, by rfl⟩ : syracuseStep 495485 = 185807) (by norm_num)
theorem B528277 : Blo 327838 528277 := bbase (se 6 (by rfl) ⟨12381, by rfl⟩ : syracuseStep 528277 = 24763) (by norm_num)
theorem B495509 : Blo 327838 495509 := bbase (se 6 (by rfl) ⟨11613, by rfl⟩ : syracuseStep 495509 = 23227) (by norm_num)
theorem B561053 : Blo 327838 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B741293 : Blo 327838 741293 := bbase (se 3 (by rfl) ⟨138992, by rfl⟩ : syracuseStep 741293 = 277985) (by norm_num)
theorem B495533 : Blo 327838 495533 := bbase (se 3 (by rfl) ⟨92912, by rfl⟩ : syracuseStep 495533 = 185825) (by norm_num)
theorem B626629 : Blo 327838 626629 := bbase (se 4 (by rfl) ⟨58746, by rfl⟩ : syracuseStep 626629 = 117493) (by norm_num)
theorem B495557 : Blo 327838 495557 := bbase (se 4 (by rfl) ⟨46458, by rfl⟩ : syracuseStep 495557 = 92917) (by norm_num)
theorem B495581 : Blo 327838 495581 := bbase (se 3 (by rfl) ⟨92921, by rfl⟩ : syracuseStep 495581 = 185843) (by norm_num)
theorem B356333 : Blo 327838 356333 := bbase (se 3 (by rfl) ⟨66812, by rfl⟩ : syracuseStep 356333 = 133625) (by norm_num)
theorem B937973 : Blo 327838 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B741365 : Blo 327838 741365 := bbase (se 5 (by rfl) ⟨34751, by rfl⟩ : syracuseStep 741365 = 69503) (by norm_num)
theorem B495605 : Blo 327838 495605 := bbase (se 5 (by rfl) ⟨23231, by rfl⟩ : syracuseStep 495605 = 46463) (by norm_num)
theorem B831485 : Blo 327838 831485 := bbase (se 3 (by rfl) ⟨155903, by rfl⟩ : syracuseStep 831485 = 311807) (by norm_num)
theorem B495629 : Blo 327838 495629 := bbase (se 3 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 495629 = 185861) (by norm_num)
theorem B4739093 : Blo 327838 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B495653 : Blo 327838 495653 := bbase (se 4 (by rfl) ⟨46467, by rfl⟩ : syracuseStep 495653 = 92935) (by norm_num)
theorem B741437 : Blo 327838 741437 := bbase (se 3 (by rfl) ⟨139019, by rfl⟩ : syracuseStep 741437 = 278039) (by norm_num)
theorem B495677 : Blo 327838 495677 := bbase (se 3 (by rfl) ⟨92939, by rfl⟩ : syracuseStep 495677 = 185879) (by norm_num)
theorem B1667141 : Blo 327838 1667141 := bbase (se 4 (by rfl) ⟨156294, by rfl⟩ : syracuseStep 1667141 = 312589) (by norm_num)
theorem B2819285 : Blo 327838 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B626773 : Blo 327838 626773 := bbase (se 8 (by rfl) ⟨3672, by rfl⟩ : syracuseStep 626773 = 7345) (by norm_num)
theorem B495701 : Blo 327838 495701 := bbase (se 8 (by rfl) ⟨2904, by rfl⟩ : syracuseStep 495701 = 5809) (by norm_num)
theorem B495725 : Blo 327838 495725 := bbase (se 3 (by rfl) ⟨92948, by rfl⟩ : syracuseStep 495725 = 185897) (by norm_num)
theorem B2355317 : Blo 327838 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B422021 : Blo 327838 422021 := bbase (se 4 (by rfl) ⟨39564, by rfl⟩ : syracuseStep 422021 = 79129) (by norm_num)
theorem B741509 : Blo 327838 741509 := bbase (se 4 (by rfl) ⟨69516, by rfl⟩ : syracuseStep 741509 = 139033) (by norm_num)
theorem B495749 : Blo 327838 495749 := bbase (se 4 (by rfl) ⟨46476, by rfl⟩ : syracuseStep 495749 = 92953) (by norm_num)
theorem B528533 : Blo 327838 528533 := bbase (se 6 (by rfl) ⟨12387, by rfl⟩ : syracuseStep 528533 = 24775) (by norm_num)
theorem B495773 : Blo 327838 495773 := bbase (se 3 (by rfl) ⟨92957, by rfl⟩ : syracuseStep 495773 = 185915) (by norm_num)
theorem B1249445 : Blo 327838 1249445 := bbase (se 4 (by rfl) ⟨117135, by rfl⟩ : syracuseStep 1249445 = 234271) (by norm_num)
theorem B495797 : Blo 327838 495797 := bbase (se 5 (by rfl) ⟨23240, by rfl⟩ : syracuseStep 495797 = 46481) (by norm_num)
theorem B741581 : Blo 327838 741581 := bbase (se 3 (by rfl) ⟨139046, by rfl⟩ : syracuseStep 741581 = 278093) (by norm_num)
theorem B495821 : Blo 327838 495821 := bbase (se 3 (by rfl) ⟨92966, by rfl⟩ : syracuseStep 495821 = 185933) (by norm_num)
theorem B938213 : Blo 327838 938213 := bbase (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) (by norm_num)
theorem B495845 : Blo 327838 495845 := bbase (se 4 (by rfl) ⟨46485, by rfl⟩ : syracuseStep 495845 = 92971) (by norm_num)
theorem B626933 : Blo 327838 626933 := bbase (se 5 (by rfl) ⟨29387, by rfl⟩ : syracuseStep 626933 = 58775) (by norm_num)
theorem B495869 : Blo 327838 495869 := bbase (se 3 (by rfl) ⟨92975, by rfl⟩ : syracuseStep 495869 = 185951) (by norm_num)
theorem B1110293 : Blo 327838 1110293 := bbase (se 6 (by rfl) ⟨26022, by rfl⟩ : syracuseStep 1110293 = 52045) (by norm_num)
theorem B741653 : Blo 327838 741653 := bbase (se 6 (by rfl) ⟨17382, by rfl⟩ : syracuseStep 741653 = 34765) (by norm_num)
theorem B495893 : Blo 327838 495893 := bbase (se 6 (by rfl) ⟨11622, by rfl⟩ : syracuseStep 495893 = 23245) (by norm_num)
theorem B495917 : Blo 327838 495917 := bbase (se 3 (by rfl) ⟨92984, by rfl⟩ : syracuseStep 495917 = 185969) (by norm_num)
theorem B553277 : Blo 327838 553277 := bbase (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) (by norm_num)
theorem B495941 : Blo 327838 495941 := bbase (se 4 (by rfl) ⟨46494, by rfl⟩ : syracuseStep 495941 = 92989) (by norm_num)
theorem B3993941 : Blo 327838 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B831829 : Blo 327838 831829 := bbase (se 10 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 831829 = 2437) (by norm_num)
theorem B741725 : Blo 327838 741725 := bbase (se 3 (by rfl) ⟨139073, by rfl⟩ : syracuseStep 741725 = 278147) (by norm_num)
theorem B495965 : Blo 327838 495965 := bbase (se 3 (by rfl) ⟨92993, by rfl⟩ : syracuseStep 495965 = 185987) (by norm_num)
theorem B1577333 : Blo 327838 1577333 := bbase (se 5 (by rfl) ⟨73937, by rfl⟩ : syracuseStep 1577333 = 147875) (by norm_num)
theorem B495989 : Blo 327838 495989 := bbase (se 5 (by rfl) ⟨23249, by rfl⟩ : syracuseStep 495989 = 46499) (by norm_num)
theorem B627077 : Blo 327838 627077 := bbase (se 4 (by rfl) ⟨58788, by rfl⟩ : syracuseStep 627077 = 117577) (by norm_num)
theorem B496013 : Blo 327838 496013 := bbase (se 3 (by rfl) ⟨93002, by rfl⟩ : syracuseStep 496013 = 186005) (by norm_num)
theorem B938405 : Blo 327838 938405 := bbase (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) (by norm_num)
theorem B741797 : Blo 327838 741797 := bbase (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) (by norm_num)
theorem B496037 : Blo 327838 496037 := bbase (se 4 (by rfl) ⟨46503, by rfl⟩ : syracuseStep 496037 = 93007) (by norm_num)
theorem B553405 : Blo 327838 553405 := bbase (se 3 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 553405 = 207527) (by norm_num)
theorem B790973 : Blo 327838 790973 := bbase (se 3 (by rfl) ⟨148307, by rfl⟩ : syracuseStep 790973 = 296615) (by norm_num)
theorem B496061 : Blo 327838 496061 := bbase (se 3 (by rfl) ⟨93011, by rfl⟩ : syracuseStep 496061 = 186023) (by norm_num)
theorem B1331653 : Blo 327838 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B831941 : Blo 327838 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B602581 : Blo 327838 602581 := bbase (se 7 (by rfl) ⟨7061, by rfl⟩ : syracuseStep 602581 = 14123) (by norm_num)
theorem B496085 : Blo 327838 496085 := bbase (se 7 (by rfl) ⟨5813, by rfl⟩ : syracuseStep 496085 = 11627) (by norm_num)
theorem B741869 : Blo 327838 741869 := bbase (se 3 (by rfl) ⟨139100, by rfl⟩ : syracuseStep 741869 = 278201) (by norm_num)
theorem B496109 : Blo 327838 496109 := bbase (se 3 (by rfl) ⟨93020, by rfl⟩ : syracuseStep 496109 = 186041) (by norm_num)
theorem B553493 : Blo 327838 553493 := bbase (se 6 (by rfl) ⟨12972, by rfl⟩ : syracuseStep 553493 = 25945) (by norm_num)
theorem B561709 : Blo 327838 561709 := bbase (se 3 (by rfl) ⟨105320, by rfl⟩ : syracuseStep 561709 = 210641) (by norm_num)
theorem B741941 : Blo 327838 741941 := bbase (se 5 (by rfl) ⟨34778, by rfl⟩ : syracuseStep 741941 = 69557) (by norm_num)
theorem B742013 : Blo 327838 742013 := bbase (se 3 (by rfl) ⟨139127, by rfl⟩ : syracuseStep 742013 = 278255) (by norm_num)
theorem B594557 : Blo 327838 594557 := bbase (se 3 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 594557 = 222959) (by norm_num)
theorem B832133 : Blo 327838 832133 := bbase (se 4 (by rfl) ⟨78012, by rfl⟩ : syracuseStep 832133 = 156025) (by norm_num)
theorem B553621 : Blo 327838 553621 := bbase (se 6 (by rfl) ⟨12975, by rfl⟩ : syracuseStep 553621 = 25951) (by norm_num)
theorem B627365 : Blo 327838 627365 := bbase (se 4 (by rfl) ⟨58815, by rfl⟩ : syracuseStep 627365 = 117631) (by norm_num)
theorem B1110725 : Blo 327838 1110725 := bbase (se 4 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 1110725 = 208261) (by norm_num)
theorem B742085 : Blo 327838 742085 := bbase (se 4 (by rfl) ⟨69570, by rfl⟩ : syracuseStep 742085 = 139141) (by norm_num)
theorem B422617 : Blo 327838 422617 := bbase (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) (by norm_num)
theorem B1127141 : Blo 327838 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B553709 : Blo 327838 553709 := bbase (se 3 (by rfl) ⟨103820, by rfl⟩ : syracuseStep 553709 = 207641) (by norm_num)
theorem B701173 : Blo 327838 701173 := bbase (se 5 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 701173 = 65735) (by norm_num)
theorem B2372341 : Blo 327838 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B742157 : Blo 327838 742157 := bbase (se 3 (by rfl) ⟨139154, by rfl⟩ : syracuseStep 742157 = 278309) (by norm_num)
theorem B332605 : Blo 327838 332605 := bbase (se 3 (by rfl) ⟨62363, by rfl⟩ : syracuseStep 332605 = 124727) (by norm_num)
theorem B627517 : Blo 327838 627517 := bbase (se 3 (by rfl) ⟨117659, by rfl⟩ : syracuseStep 627517 = 235319) (by norm_num)
theorem B742229 : Blo 327838 742229 := bbase (se 9 (by rfl) ⟨2174, by rfl⟩ : syracuseStep 742229 = 4349) (by norm_num)
theorem B529237 : Blo 327838 529237 := bbase (se 9 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 529237 = 3101) (by norm_num)
theorem B553837 : Blo 327838 553837 := bbase (se 3 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 553837 = 207689) (by norm_num)
theorem B701293 : Blo 327838 701293 := bbase (se 3 (by rfl) ⟨131492, by rfl⟩ : syracuseStep 701293 = 262985) (by norm_num)
theorem B799621 : Blo 327838 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B1880981 : Blo 327838 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B742301 : Blo 327838 742301 := bbase (se 3 (by rfl) ⟨139181, by rfl⟩ : syracuseStep 742301 = 278363) (by norm_num)
theorem B1143733 : Blo 327838 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B553925 : Blo 327838 553925 := bbase (se 4 (by rfl) ⟨51930, by rfl⟩ : syracuseStep 553925 = 103861) (by norm_num)
theorem B832477 : Blo 327838 832477 := bbase (se 3 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 832477 = 312179) (by norm_num)
theorem B742373 : Blo 327838 742373 := bbase (se 4 (by rfl) ⟨69597, by rfl⟩ : syracuseStep 742373 = 139195) (by norm_num)
theorem B1586213 : Blo 327838 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B742445 : Blo 327838 742445 := bbase (se 3 (by rfl) ⟨139208, by rfl⟩ : syracuseStep 742445 = 278417) (by norm_num)
theorem B554053 : Blo 327838 554053 := bbase (se 4 (by rfl) ⟨51942, by rfl⟩ : syracuseStep 554053 = 103885) (by norm_num)
theorem B832589 : Blo 327838 832589 := bbase (se 3 (by rfl) ⟨156110, by rfl⟩ : syracuseStep 832589 = 312221) (by norm_num)
theorem B947285 : Blo 327838 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B701549 : Blo 327838 701549 := bbase (se 3 (by rfl) ⟨131540, by rfl⟩ : syracuseStep 701549 = 263081) (by norm_num)
theorem B627821 : Blo 327838 627821 := bbase (se 3 (by rfl) ⟨117716, by rfl⟩ : syracuseStep 627821 = 235433) (by norm_num)
theorem B1111157 : Blo 327838 1111157 := bbase (se 5 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 1111157 = 104171) (by norm_num)
theorem B742517 : Blo 327838 742517 := bbase (se 5 (by rfl) ⟨34805, by rfl⟩ : syracuseStep 742517 = 69611) (by norm_num)
theorem B554141 : Blo 327838 554141 := bbase (se 3 (by rfl) ⟨103901, by rfl⟩ : syracuseStep 554141 = 207803) (by norm_num)
theorem B742589 : Blo 327838 742589 := bbase (se 3 (by rfl) ⟨139235, by rfl⟩ : syracuseStep 742589 = 278471) (by norm_num)
theorem B414973 : Blo 327838 414973 := bbase (se 3 (by rfl) ⟨77807, by rfl⟩ : syracuseStep 414973 = 155615) (by norm_num)
theorem B529661 : Blo 327838 529661 := bbase (se 3 (by rfl) ⟨99311, by rfl⟩ : syracuseStep 529661 = 198623) (by norm_num)
theorem B742661 : Blo 327838 742661 := bbase (se 4 (by rfl) ⟨69624, by rfl⟩ : syracuseStep 742661 = 139249) (by norm_num)
theorem B832781 : Blo 327838 832781 := bbase (se 3 (by rfl) ⟨156146, by rfl⟩ : syracuseStep 832781 = 312293) (by norm_num)
theorem B554269 : Blo 327838 554269 := bbase (se 3 (by rfl) ⟨103925, by rfl⟩ : syracuseStep 554269 = 207851) (by norm_num)
theorem B742733 : Blo 327838 742733 := bbase (se 3 (by rfl) ⟨139262, by rfl⟩ : syracuseStep 742733 = 278525) (by norm_num)
theorem B1668437 : Blo 327838 1668437 := bbase (se 13 (by rfl) ⟨305, by rfl⟩ : syracuseStep 1668437 = 611) (by norm_num)
theorem B865637 : Blo 327838 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B333157 : Blo 327838 333157 := bbase (se 4 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 333157 = 62467) (by norm_num)
theorem B554357 : Blo 327838 554357 := bbase (se 5 (by rfl) ⟨25985, by rfl⟩ : syracuseStep 554357 = 51971) (by norm_num)
theorem B939397 : Blo 327838 939397 := bbase (se 4 (by rfl) ⟨88068, by rfl⟩ : syracuseStep 939397 = 176137) (by norm_num)
theorem B742805 : Blo 327838 742805 := bbase (se 6 (by rfl) ⟨17409, by rfl⟩ : syracuseStep 742805 = 34819) (by norm_num)
theorem B415145 : Blo 327838 415145 := bbase (se 2 (by rfl) ⟨155679, by rfl⟩ : syracuseStep 415145 = 311359) (by norm_num)
theorem B2840021 : Blo 327838 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B2004437 : Blo 327838 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B857557 : Blo 327838 857557 := bbase (se 7 (by rfl) ⟨10049, by rfl⟩ : syracuseStep 857557 = 20099) (by norm_num)
theorem B742877 : Blo 327838 742877 := bbase (se 3 (by rfl) ⟨139289, by rfl⟩ : syracuseStep 742877 = 278579) (by norm_num)
theorem B415201 : Blo 327838 415201 := bbase (se 2 (by rfl) ⟨155700, by rfl⟩ : syracuseStep 415201 = 311401) (by norm_num)
theorem B554485 : Blo 327838 554485 := bbase (se 5 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 554485 = 51983) (by norm_num)
theorem B366077 : Blo 327838 366077 := bbase (se 3 (by rfl) ⟨68639, by rfl⟩ : syracuseStep 366077 = 137279) (by norm_num)
theorem B1111589 : Blo 327838 1111589 := bbase (se 4 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 1111589 = 208423) (by norm_num)
theorem B742949 : Blo 327838 742949 := bbase (se 4 (by rfl) ⟨69651, by rfl⟩ : syracuseStep 742949 = 139303) (by norm_num)
theorem B415297 : Blo 327838 415297 := bbase (se 2 (by rfl) ⟨155736, by rfl⟩ : syracuseStep 415297 = 311473) (by norm_num)
theorem B554573 : Blo 327838 554573 := bbase (se 3 (by rfl) ⟨103982, by rfl⟩ : syracuseStep 554573 = 207965) (by norm_num)
theorem B996965 : Blo 327838 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B833125 : Blo 327838 833125 := bbase (se 4 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 833125 = 156211) (by norm_num)
theorem B743021 : Blo 327838 743021 := bbase (se 3 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 743021 = 278633) (by norm_num)
theorem B595565 : Blo 327838 595565 := bbase (se 3 (by rfl) ⟨111668, by rfl⟩ : syracuseStep 595565 = 223337) (by norm_num)
theorem B1070725 : Blo 327838 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B743093 : Blo 327838 743093 := bbase (se 5 (by rfl) ⟨34832, by rfl⟩ : syracuseStep 743093 = 69665) (by norm_num)
theorem B3176117 : Blo 327838 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B554701 : Blo 327838 554701 := bbase (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) (by norm_num)
theorem B833237 : Blo 327838 833237 := bbase (se 7 (by rfl) ⟨9764, by rfl⟩ : syracuseStep 833237 = 19529) (by norm_num)
theorem B669397 : Blo 327838 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B1185509 : Blo 327838 1185509 := bbase (se 4 (by rfl) ⟨111141, by rfl⟩ : syracuseStep 1185509 = 222283) (by norm_num)
theorem B415469 : Blo 327838 415469 := bbase (se 3 (by rfl) ⟨77900, by rfl⟩ : syracuseStep 415469 = 155801) (by norm_num)
theorem B1660661 : Blo 327838 1660661 := bbase (se 5 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 1660661 = 155687) (by norm_num)
theorem B743165 : Blo 327838 743165 := bbase (se 3 (by rfl) ⟨139343, by rfl⟩ : syracuseStep 743165 = 278687) (by norm_num)
theorem B415525 : Blo 327838 415525 := bbase (se 4 (by rfl) ⟨38955, by rfl⟩ : syracuseStep 415525 = 77911) (by norm_num)
theorem B554789 : Blo 327838 554789 := bbase (se 4 (by rfl) ⟨52011, by rfl⟩ : syracuseStep 554789 = 104023) (by norm_num)
theorem B743237 : Blo 327838 743237 := bbase (se 4 (by rfl) ⟨69678, by rfl⟩ : syracuseStep 743237 = 139357) (by norm_num)
theorem B415621 : Blo 327838 415621 := bbase (se 4 (by rfl) ⟨38964, by rfl⟩ : syracuseStep 415621 = 77929) (by norm_num)
theorem B743309 : Blo 327838 743309 := bbase (se 3 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 743309 = 278741) (by norm_num)
theorem B833429 : Blo 327838 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B2537365 : Blo 327838 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B554917 : Blo 327838 554917 := bbase (se 4 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 554917 = 104047) (by norm_num)
theorem B350125 : Blo 327838 350125 := bbase (se 3 (by rfl) ⟨65648, by rfl⟩ : syracuseStep 350125 = 131297) (by norm_num)
theorem B2996149 : Blo 327838 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B1112021 : Blo 327838 1112021 := bbase (se 7 (by rfl) ⟨13031, by rfl⟩ : syracuseStep 1112021 = 26063) (by norm_num)
theorem B743381 : Blo 327838 743381 := bbase (se 7 (by rfl) ⟨8711, by rfl⟩ : syracuseStep 743381 = 17423) (by norm_num)
theorem B702437 : Blo 327838 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B1718261 : Blo 327838 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B555005 : Blo 327838 555005 := bbase (se 3 (by rfl) ⟨104063, by rfl⟩ : syracuseStep 555005 = 208127) (by norm_num)
theorem B743453 : Blo 327838 743453 := bbase (se 3 (by rfl) ⟨139397, by rfl⟩ : syracuseStep 743453 = 278795) (by norm_num)
theorem B350245 : Blo 327838 350245 := bbase (se 4 (by rfl) ⟨32835, by rfl⟩ : syracuseStep 350245 = 65671) (by norm_num)
theorem B415793 : Blo 327838 415793 := bbase (se 2 (by rfl) ⟨155922, by rfl⟩ : syracuseStep 415793 = 311845) (by norm_num)
theorem B759869 : Blo 327838 759869 := bbase (se 3 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 759869 = 284951) (by norm_num)
theorem B1407061 : Blo 327838 1407061 := bbase (se 8 (by rfl) ⟨8244, by rfl⟩ : syracuseStep 1407061 = 16489) (by norm_num)
theorem B743525 : Blo 327838 743525 := bbase (se 4 (by rfl) ⟨69705, by rfl⟩ : syracuseStep 743525 = 139411) (by norm_num)
theorem B415849 : Blo 327838 415849 := bbase (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) (by norm_num)
theorem B555133 : Blo 327838 555133 := bbase (se 3 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 555133 = 208175) (by norm_num)
theorem B891013 : Blo 327838 891013 := bbase (se 4 (by rfl) ⟨83532, by rfl⟩ : syracuseStep 891013 = 167065) (by norm_num)
theorem B342185 : Blo 327838 342185 := bbase (se 2 (by rfl) ⟨128319, by rfl⟩ : syracuseStep 342185 = 256639) (by norm_num)
theorem B743597 : Blo 327838 743597 := bbase (se 3 (by rfl) ⟨139424, by rfl⟩ : syracuseStep 743597 = 278849) (by norm_num)
theorem B415945 : Blo 327838 415945 := bbase (se 2 (by rfl) ⟨155979, by rfl⟩ : syracuseStep 415945 = 311959) (by norm_num)
theorem B702677 : Blo 327838 702677 := bbase (se 7 (by rfl) ⟨8234, by rfl⟩ : syracuseStep 702677 = 16469) (by norm_num)
theorem B555221 : Blo 327838 555221 := bbase (se 7 (by rfl) ⟨6506, by rfl⟩ : syracuseStep 555221 = 13013) (by norm_num)
theorem B1251557 : Blo 327838 1251557 := bbase (se 4 (by rfl) ⟨117333, by rfl⟩ : syracuseStep 1251557 = 234667) (by norm_num)
theorem B833773 : Blo 327838 833773 := bbase (se 3 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 833773 = 312665) (by norm_num)
theorem B743669 : Blo 327838 743669 := bbase (se 5 (by rfl) ⟨34859, by rfl⟩ : syracuseStep 743669 = 69719) (by norm_num)
theorem B350497 : Blo 327838 350497 := bbase (se 2 (by rfl) ⟨131436, by rfl⟩ : syracuseStep 350497 = 262873) (by norm_num)
theorem B350501 : Blo 327838 350501 := bbase (se 4 (by rfl) ⟨32859, by rfl⟩ : syracuseStep 350501 = 65719) (by norm_num)
theorem B2816309 : Blo 327838 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B743741 : Blo 327838 743741 := bbase (se 3 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 743741 = 278903) (by norm_num)
theorem B555349 : Blo 327838 555349 := bbase (se 10 (by rfl) ⟨813, by rfl⟩ : syracuseStep 555349 = 1627) (by norm_num)
theorem B833885 : Blo 327838 833885 := bbase (se 3 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 833885 = 312707) (by norm_num)
theorem B1587557 : Blo 327838 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B416117 : Blo 327838 416117 := bbase (se 5 (by rfl) ⟨19505, by rfl⟩ : syracuseStep 416117 = 39011) (by norm_num)
theorem B1112453 : Blo 327838 1112453 := bbase (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) (by norm_num)
theorem B743813 : Blo 327838 743813 := bbase (se 4 (by rfl) ⟨69732, by rfl⟩ : syracuseStep 743813 = 139465) (by norm_num)
theorem B416173 : Blo 327838 416173 := bbase (se 3 (by rfl) ⟨78032, by rfl⟩ : syracuseStep 416173 = 156065) (by norm_num)
theorem B555437 : Blo 327838 555437 := bbase (se 3 (by rfl) ⟨104144, by rfl⟩ : syracuseStep 555437 = 208289) (by norm_num)
theorem B670141 : Blo 327838 670141 := bbase (se 3 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 670141 = 251303) (by norm_num)
theorem B743885 : Blo 327838 743885 := bbase (se 3 (by rfl) ⟨139478, by rfl⟩ : syracuseStep 743885 = 278957) (by norm_num)
theorem B3365333 : Blo 327838 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B940501 : Blo 327838 940501 := bbase (se 7 (by rfl) ⟨11021, by rfl⟩ : syracuseStep 940501 = 22043) (by norm_num)
theorem B1251845 : Blo 327838 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B416269 : Blo 327838 416269 := bbase (se 3 (by rfl) ⟨78050, by rfl⟩ : syracuseStep 416269 = 156101) (by norm_num)
theorem B743957 : Blo 327838 743957 := bbase (se 6 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 743957 = 34873) (by norm_num)
theorem B834077 : Blo 327838 834077 := bbase (se 3 (by rfl) ⟨156389, by rfl⟩ : syracuseStep 834077 = 312779) (by norm_num)
theorem B555565 : Blo 327838 555565 := bbase (se 3 (by rfl) ⟨104168, by rfl⟩ : syracuseStep 555565 = 208337) (by norm_num)
theorem B5331541 : Blo 327838 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B744029 : Blo 327838 744029 := bbase (se 3 (by rfl) ⟨139505, by rfl⟩ : syracuseStep 744029 = 279011) (by norm_num)
theorem B1669733 : Blo 327838 1669733 := bbase (se 4 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 1669733 = 313075) (by norm_num)
theorem B490093 : Blo 327838 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B555653 : Blo 327838 555653 := bbase (se 4 (by rfl) ⟨52092, by rfl⟩ : syracuseStep 555653 = 104185) (by norm_num)
theorem B744101 : Blo 327838 744101 := bbase (se 4 (by rfl) ⟨69759, by rfl⟩ : syracuseStep 744101 = 139519) (by norm_num)
theorem B416441 : Blo 327838 416441 := bbase (se 2 (by rfl) ⟨156165, by rfl⟩ : syracuseStep 416441 = 312331) (by norm_num)
theorem B703181 : Blo 327838 703181 := bbase (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) (by norm_num)
theorem B703189 : Blo 327838 703189 := bbase (se 7 (by rfl) ⟨8240, by rfl⟩ : syracuseStep 703189 = 16481) (by norm_num)
theorem B744173 : Blo 327838 744173 := bbase (se 3 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 744173 = 279065) (by norm_num)
theorem B416497 : Blo 327838 416497 := bbase (se 2 (by rfl) ⟨156186, by rfl⟩ : syracuseStep 416497 = 312373) (by norm_num)
theorem B555781 : Blo 327838 555781 := bbase (se 4 (by rfl) ⟨52104, by rfl⟩ : syracuseStep 555781 = 104209) (by norm_num)
theorem B1112885 : Blo 327838 1112885 := bbase (se 5 (by rfl) ⟨52166, by rfl⟩ : syracuseStep 1112885 = 104333) (by norm_num)
theorem B334649 : Blo 327838 334649 := bbase (se 2 (by rfl) ⟨125493, by rfl⟩ : syracuseStep 334649 = 250987) (by norm_num)
theorem B1694533 : Blo 327838 1694533 := bbase (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) (by norm_num)
theorem B416593 : Blo 327838 416593 := bbase (se 2 (by rfl) ⟨156222, by rfl⟩ : syracuseStep 416593 = 312445) (by norm_num)
theorem B2087765 : Blo 327838 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B351065 : Blo 327838 351065 := bbase (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) (by norm_num)
theorem B555869 : Blo 327838 555869 := bbase (se 3 (by rfl) ⟨104225, by rfl⟩ : syracuseStep 555869 = 208451) (by norm_num)
theorem B834421 : Blo 327838 834421 := bbase (se 5 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 834421 = 78227) (by norm_num)
theorem B555997 : Blo 327838 555997 := bbase (se 3 (by rfl) ⟨104249, by rfl⟩ : syracuseStep 555997 = 208499) (by norm_num)
theorem B834533 : Blo 327838 834533 := bbase (se 4 (by rfl) ⟨78237, by rfl⟩ : syracuseStep 834533 = 156475) (by norm_num)
theorem B375797 : Blo 327838 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B416765 : Blo 327838 416765 := bbase (se 3 (by rfl) ⟨78143, by rfl⟩ : syracuseStep 416765 = 156287) (by norm_num)
theorem B1661957 : Blo 327838 1661957 := bbase (se 4 (by rfl) ⟨155808, by rfl⟩ : syracuseStep 1661957 = 311617) (by norm_num)
theorem B351253 : Blo 327838 351253 := bbase (se 6 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 351253 = 16465) (by norm_num)
theorem B416821 : Blo 327838 416821 := bbase (se 5 (by rfl) ⟨19538, by rfl⟩ : syracuseStep 416821 = 39077) (by norm_num)
theorem B556085 : Blo 327838 556085 := bbase (se 5 (by rfl) ⟨26066, by rfl⟩ : syracuseStep 556085 = 52133) (by norm_num)
theorem B1883189 : Blo 327838 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B1055861 : Blo 327838 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B793741 : Blo 327838 793741 := bbase (se 3 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 793741 = 297653) (by norm_num)
theorem B416917 : Blo 327838 416917 := bbase (se 6 (by rfl) ⟨9771, by rfl⟩ : syracuseStep 416917 = 19543) (by norm_num)
theorem B834725 : Blo 327838 834725 := bbase (se 4 (by rfl) ⟨78255, by rfl⟩ : syracuseStep 834725 = 156511) (by norm_num)
theorem B556213 : Blo 327838 556213 := bbase (se 5 (by rfl) ⟨26072, by rfl⟩ : syracuseStep 556213 = 52145) (by norm_num)
theorem B1408213 : Blo 327838 1408213 := bbase (se 7 (by rfl) ⟨16502, by rfl⟩ : syracuseStep 1408213 = 33005) (by norm_num)
theorem B1113317 : Blo 327838 1113317 := bbase (se 4 (by rfl) ⟨104373, by rfl⟩ : syracuseStep 1113317 = 208747) (by norm_num)
theorem B556301 : Blo 327838 556301 := bbase (se 3 (by rfl) ⟨104306, by rfl⟩ : syracuseStep 556301 = 208613) (by norm_num)
theorem B1187093 : Blo 327838 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B417089 : Blo 327838 417089 := bbase (se 2 (by rfl) ⟨156408, by rfl⟩ : syracuseStep 417089 = 312817) (by norm_num)
theorem B417145 : Blo 327838 417145 := bbase (se 2 (by rfl) ⟨156429, by rfl⟩ : syracuseStep 417145 = 312859) (by norm_num)
theorem B353197 : Blo 327838 353197 := bbase (se 3 (by rfl) ⟨66224, by rfl⟩ : syracuseStep 353197 = 132449) (by norm_num)
theorem B556429 : Blo 327838 556429 := bbase (se 3 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 556429 = 208661) (by norm_num)
theorem B417241 : Blo 327838 417241 := bbase (se 2 (by rfl) ⟨156465, by rfl⟩ : syracuseStep 417241 = 312931) (by norm_num)
theorem B556517 : Blo 327838 556517 := bbase (se 4 (by rfl) ⟨52173, by rfl⟩ : syracuseStep 556517 = 104347) (by norm_num)
theorem B835069 : Blo 327838 835069 := bbase (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) (by norm_num)
theorem B900629 : Blo 327838 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B1408549 : Blo 327838 1408549 := bbase (se 4 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 1408549 = 264103) (by norm_num)
theorem B1408565 : Blo 327838 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B556645 : Blo 327838 556645 := bbase (se 4 (by rfl) ⟨52185, by rfl⟩ : syracuseStep 556645 = 104371) (by norm_num)
theorem B835181 : Blo 327838 835181 := bbase (se 3 (by rfl) ⟨156596, by rfl⟩ : syracuseStep 835181 = 313193) (by norm_num)
theorem B417413 : Blo 327838 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B1113749 : Blo 327838 1113749 := bbase (se 6 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 1113749 = 52207) (by norm_num)
theorem B794261 : Blo 327838 794261 := bbase (se 6 (by rfl) ⟨18615, by rfl⟩ : syracuseStep 794261 = 37231) (by norm_num)
theorem B1253029 : Blo 327838 1253029 := bbase (se 4 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 1253029 = 234943) (by norm_num)
theorem B418385 : Blo 327838 418385 := bbase (se 2 (by rfl) ⟨156894, by rfl⟩ : syracuseStep 418385 = 313789) (by norm_num)
theorem B417469 : Blo 327838 417469 := bbase (se 3 (by rfl) ⟨78275, by rfl⟩ : syracuseStep 417469 = 156551) (by norm_num)
theorem B556733 : Blo 327838 556733 := bbase (se 3 (by rfl) ⟨104387, by rfl⟩ : syracuseStep 556733 = 208775) (by norm_num)
theorem B892613 : Blo 327838 892613 := bbase (se 4 (by rfl) ⟨83682, by rfl⟩ : syracuseStep 892613 = 167365) (by norm_num)
theorem B376553 : Blo 327838 376553 := bbase (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) (by norm_num)
theorem B794357 : Blo 327838 794357 := bbase (se 5 (by rfl) ⟨37235, by rfl⟩ : syracuseStep 794357 = 74471) (by norm_num)
theorem B5603093 : Blo 327838 5603093 := bbase (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) (by norm_num)
theorem B417565 : Blo 327838 417565 := bbase (se 3 (by rfl) ⟨78293, by rfl⟩ : syracuseStep 417565 = 156587) (by norm_num)
theorem B835373 : Blo 327838 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B704317 : Blo 327838 704317 := bbase (se 3 (by rfl) ⟨132059, by rfl⟩ : syracuseStep 704317 = 264119) (by norm_num)
theorem B556861 : Blo 327838 556861 := bbase (se 3 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 556861 = 208823) (by norm_num)
theorem B352073 : Blo 327838 352073 := bbase (se 2 (by rfl) ⟨132027, by rfl⟩ : syracuseStep 352073 = 264055) (by norm_num)
theorem B1671029 : Blo 327838 1671029 := bbase (se 5 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 1671029 = 156659) (by norm_num)
theorem B933781 : Blo 327838 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B556949 : Blo 327838 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B860053 : Blo 327838 860053 := bbase (se 6 (by rfl) ⟨20157, by rfl⟩ : syracuseStep 860053 = 40315) (by norm_num)
theorem B417737 : Blo 327838 417737 := bbase (se 2 (by rfl) ⟨156651, by rfl⟩ : syracuseStep 417737 = 313303) (by norm_num)
theorem B1253333 : Blo 327838 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B565213 : Blo 327838 565213 := bbase (se 3 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 565213 = 211955) (by norm_num)
theorem B557057 : Blo 327838 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B466993 : Blo 327838 466993 := bstep (se 2 (by rfl) ⟨175122, by rfl⟩ : syracuseStep 466993 = 350245) B350245
theorem B3760181 : Blo 327838 3760181 := bstep (se 5 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 3760181 = 352517) B352517
theorem B352355 : Blo 327838 352355 := bstep (se 1 (by rfl) ⟨264266, by rfl⟩ : syracuseStep 352355 = 528533) B528533
theorem B1876081 : Blo 327838 1876081 := bstep (se 2 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 1876081 = 1407061) B1407061
theorem B835697 : Blo 327838 835697 := bstep (se 2 (by rfl) ⟨313386, by rfl⟩ : syracuseStep 835697 = 626773) B626773
theorem B557185 : Blo 327838 557185 := bstep (se 2 (by rfl) ⟨208944, by rfl⟩ : syracuseStep 557185 = 417889) B417889
theorem B327843 : Blo 327838 327843 := bstep (se 1 (by rfl) ⟨245882, by rfl⟩ : syracuseStep 327843 = 491765) B491765
theorem B557219 : Blo 327838 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B417955 : Blo 327838 417955 := bstep (se 1 (by rfl) ⟨313466, by rfl⟩ : syracuseStep 417955 = 626933) B626933
theorem B1188017 : Blo 327838 1188017 := bstep (se 2 (by rfl) ⟨445506, by rfl⟩ : syracuseStep 1188017 = 891013) B891013
theorem B1114289 : Blo 327838 1114289 := bstep (se 2 (by rfl) ⟨417858, by rfl⟩ : syracuseStep 1114289 = 835717) B835717
theorem B327859 : Blo 327838 327859 := bstep (se 1 (by rfl) ⟨245894, by rfl⟩ : syracuseStep 327859 = 491789) B491789
theorem B327875 : Blo 327838 327875 := bstep (se 1 (by rfl) ⟨245906, by rfl⟩ : syracuseStep 327875 = 491813) B491813
theorem B368851 : Blo 327838 368851 := bstep (se 1 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 368851 = 553277) B553277
theorem B327891 : Blo 327838 327891 := bstep (se 1 (by rfl) ⟨245918, by rfl⟩ : syracuseStep 327891 = 491837) B491837
theorem B327907 : Blo 327838 327907 := bstep (se 1 (by rfl) ⟨245930, by rfl⟩ : syracuseStep 327907 = 491861) B491861
theorem B2662627 : Blo 327838 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B327923 : Blo 327838 327923 := bstep (se 1 (by rfl) ⟨245942, by rfl⟩ : syracuseStep 327923 = 491885) B491885
theorem B491777 : Blo 327838 491777 := bstep (se 2 (by rfl) ⟨184416, by rfl⟩ : syracuseStep 491777 = 368833) B368833
theorem B327939 : Blo 327838 327939 := bstep (se 1 (by rfl) ⟨245954, by rfl⟩ : syracuseStep 327939 = 491909) B491909
theorem B418051 : Blo 327838 418051 := bstep (se 1 (by rfl) ⟨313538, by rfl⟩ : syracuseStep 418051 = 627077) B627077
theorem B491795 : Blo 327838 491795 := bstep (se 1 (by rfl) ⟨368846, by rfl⟩ : syracuseStep 491795 = 737693) B737693
theorem B327955 : Blo 327838 327955 := bstep (se 1 (by rfl) ⟨245966, by rfl⟩ : syracuseStep 327955 = 491933) B491933
theorem B327971 : Blo 327838 327971 := bstep (se 1 (by rfl) ⟨245978, by rfl⟩ : syracuseStep 327971 = 491957) B491957
theorem B557347 : Blo 327838 557347 := bstep (se 1 (by rfl) ⟨418010, by rfl⟩ : syracuseStep 557347 = 836021) B836021
theorem B491825 : Blo 327838 491825 := bstep (se 2 (by rfl) ⟨184434, by rfl⟩ : syracuseStep 491825 = 368869) B368869
theorem B327987 : Blo 327838 327987 := bstep (se 1 (by rfl) ⟨245990, by rfl⟩ : syracuseStep 327987 = 491981) B491981
theorem B491843 : Blo 327838 491843 := bstep (se 1 (by rfl) ⟨368882, by rfl⟩ : syracuseStep 491843 = 737765) B737765
theorem B328003 : Blo 327838 328003 := bstep (se 1 (by rfl) ⟨246002, by rfl⟩ : syracuseStep 328003 = 492005) B492005
theorem B377155 : Blo 327838 377155 := bstep (se 1 (by rfl) ⟨282866, by rfl⟩ : syracuseStep 377155 = 565733) B565733
theorem B328019 : Blo 327838 328019 := bstep (se 1 (by rfl) ⟨246014, by rfl⟩ : syracuseStep 328019 = 492029) B492029
theorem B754001 : Blo 327838 754001 := bstep (se 2 (by rfl) ⟨282750, by rfl⟩ : syracuseStep 754001 = 565501) B565501
theorem B491873 : Blo 327838 491873 := bstep (se 2 (by rfl) ⟨184452, by rfl⟩ : syracuseStep 491873 = 368905) B368905
theorem B368995 : Blo 327838 368995 := bstep (se 1 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 368995 = 553493) B553493
theorem B328035 : Blo 327838 328035 := bstep (se 1 (by rfl) ⟨246026, by rfl⟩ : syracuseStep 328035 = 492053) B492053
theorem B622961 : Blo 327838 622961 := bstep (se 2 (by rfl) ⟨233610, by rfl⟩ : syracuseStep 622961 = 467221) B467221
theorem B491891 : Blo 327838 491891 := bstep (se 1 (by rfl) ⟨368918, by rfl⟩ : syracuseStep 491891 = 737837) B737837
theorem B328051 : Blo 327838 328051 := bstep (se 1 (by rfl) ⟨246038, by rfl⟩ : syracuseStep 328051 = 492077) B492077
theorem B328067 : Blo 327838 328067 := bstep (se 1 (by rfl) ⟨246050, by rfl⟩ : syracuseStep 328067 = 492101) B492101
theorem B491921 : Blo 327838 491921 := bstep (se 2 (by rfl) ⟨184470, by rfl⟩ : syracuseStep 491921 = 368941) B368941
theorem B328083 : Blo 327838 328083 := bstep (se 1 (by rfl) ⟨246062, by rfl⟩ : syracuseStep 328083 = 492125) B492125
theorem B491939 : Blo 327838 491939 := bstep (se 1 (by rfl) ⟨368954, by rfl⟩ : syracuseStep 491939 = 737909) B737909
theorem B328099 : Blo 327838 328099 := bstep (se 1 (by rfl) ⟨246074, by rfl⟩ : syracuseStep 328099 = 492149) B492149
theorem B328115 : Blo 327838 328115 := bstep (se 1 (by rfl) ⟨246086, by rfl⟩ : syracuseStep 328115 = 492173) B492173
theorem B557489 : Blo 327838 557489 := bstep (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) B418117
theorem B491969 : Blo 327838 491969 := bstep (se 2 (by rfl) ⟨184488, by rfl⟩ : syracuseStep 491969 = 368977) B368977
theorem B328131 : Blo 327838 328131 := bstep (se 1 (by rfl) ⟨246098, by rfl⟩ : syracuseStep 328131 = 492197) B492197
theorem B491987 : Blo 327838 491987 := bstep (se 1 (by rfl) ⟨368990, by rfl⟩ : syracuseStep 491987 = 737981) B737981
theorem B328147 : Blo 327838 328147 := bstep (se 1 (by rfl) ⟨246110, by rfl⟩ : syracuseStep 328147 = 492221) B492221
theorem B418547 : Blo 327838 418547 := bstep (se 1 (by rfl) ⟨313910, by rfl⟩ : syracuseStep 418547 = 627821) B627821
theorem B328163 : Blo 327838 328163 := bstep (se 1 (by rfl) ⟨246122, by rfl⟩ : syracuseStep 328163 = 492245) B492245
theorem B1409507 : Blo 327838 1409507 := bstep (se 1 (by rfl) ⟨1057130, by rfl⟩ : syracuseStep 1409507 = 2114261) B2114261
theorem B492017 : Blo 327838 492017 := bstep (se 2 (by rfl) ⟨184506, by rfl⟩ : syracuseStep 492017 = 369013) B369013
theorem B369139 : Blo 327838 369139 := bstep (se 1 (by rfl) ⟨276854, by rfl⟩ : syracuseStep 369139 = 553709) B553709
theorem B328179 : Blo 327838 328179 := bstep (se 1 (by rfl) ⟨246134, by rfl⟩ : syracuseStep 328179 = 492269) B492269
theorem B492035 : Blo 327838 492035 := bstep (se 1 (by rfl) ⟨369026, by rfl⟩ : syracuseStep 492035 = 738053) B738053
theorem B328195 : Blo 327838 328195 := bstep (se 1 (by rfl) ⟨246146, by rfl⟩ : syracuseStep 328195 = 492293) B492293
theorem B328211 : Blo 327838 328211 := bstep (se 1 (by rfl) ⟨246158, by rfl⟩ : syracuseStep 328211 = 492317) B492317
theorem B492065 : Blo 327838 492065 := bstep (se 2 (by rfl) ⟨184524, by rfl⟩ : syracuseStep 492065 = 369049) B369049
theorem B328227 : Blo 327838 328227 := bstep (se 1 (by rfl) ⟨246170, by rfl⟩ : syracuseStep 328227 = 492341) B492341
theorem B492083 : Blo 327838 492083 := bstep (se 1 (by rfl) ⟨369062, by rfl⟩ : syracuseStep 492083 = 738125) B738125
theorem B328243 : Blo 327838 328243 := bstep (se 1 (by rfl) ⟨246182, by rfl⟩ : syracuseStep 328243 = 492365) B492365
theorem B557617 : Blo 327838 557617 := bstep (se 2 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 557617 = 418213) B418213
theorem B328259 : Blo 327838 328259 := bstep (se 1 (by rfl) ⟨246194, by rfl⟩ : syracuseStep 328259 = 492389) B492389
theorem B1106513 : Blo 327838 1106513 := bstep (se 2 (by rfl) ⟨414942, by rfl⟩ : syracuseStep 1106513 = 829885) B829885
theorem B737873 : Blo 327838 737873 := bstep (se 2 (by rfl) ⟨276702, by rfl⟩ : syracuseStep 737873 = 553405) B553405
theorem B492113 : Blo 327838 492113 := bstep (se 2 (by rfl) ⟨184542, by rfl⟩ : syracuseStep 492113 = 369085) B369085
theorem B328275 : Blo 327838 328275 := bstep (se 1 (by rfl) ⟨246206, by rfl⟩ : syracuseStep 328275 = 492413) B492413
theorem B737891 : Blo 327838 737891 := bstep (se 1 (by rfl) ⟨553418, by rfl⟩ : syracuseStep 737891 = 1106837) B1106837
theorem B492131 : Blo 327838 492131 := bstep (se 1 (by rfl) ⟨369098, by rfl⟩ : syracuseStep 492131 = 738197) B738197
theorem B328291 : Blo 327838 328291 := bstep (se 1 (by rfl) ⟨246218, by rfl⟩ : syracuseStep 328291 = 492437) B492437
theorem B1253987 : Blo 327838 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B1401457 : Blo 327838 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B328307 : Blo 327838 328307 := bstep (se 1 (by rfl) ⟨246230, by rfl⟩ : syracuseStep 328307 = 492461) B492461
theorem B803441 : Blo 327838 803441 := bstep (se 2 (by rfl) ⟨301290, by rfl⟩ : syracuseStep 803441 = 602581) B602581
theorem B1254001 : Blo 327838 1254001 := bstep (se 2 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 1254001 = 940501) B940501
theorem B492161 : Blo 327838 492161 := bstep (se 2 (by rfl) ⟨184560, by rfl⟩ : syracuseStep 492161 = 369121) B369121
theorem B369283 : Blo 327838 369283 := bstep (se 1 (by rfl) ⟨276962, by rfl⟩ : syracuseStep 369283 = 553925) B553925
theorem B328323 : Blo 327838 328323 := bstep (se 1 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 328323 = 492485) B492485
theorem B492179 : Blo 327838 492179 := bstep (se 1 (by rfl) ⟨369134, by rfl⟩ : syracuseStep 492179 = 738269) B738269
theorem B328339 : Blo 327838 328339 := bstep (se 1 (by rfl) ⟨246254, by rfl⟩ : syracuseStep 328339 = 492509) B492509
theorem B328355 : Blo 327838 328355 := bstep (se 1 (by rfl) ⟨246266, by rfl⟩ : syracuseStep 328355 = 492533) B492533
theorem B492209 : Blo 327838 492209 := bstep (se 2 (by rfl) ⟨184578, by rfl⟩ : syracuseStep 492209 = 369157) B369157
theorem B328371 : Blo 327838 328371 := bstep (se 1 (by rfl) ⟨246278, by rfl⟩ : syracuseStep 328371 = 492557) B492557
theorem B492227 : Blo 327838 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B328387 : Blo 327838 328387 := bstep (se 1 (by rfl) ⟨246290, by rfl⟩ : syracuseStep 328387 = 492581) B492581
theorem B1057475 : Blo 327838 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B1114829 : Blo 327838 1114829 := bstep (se 3 (by rfl) ⟨209030, by rfl⟩ : syracuseStep 1114829 = 418061) B418061
theorem B328403 : Blo 327838 328403 := bstep (se 1 (by rfl) ⟨246302, by rfl⟩ : syracuseStep 328403 = 492605) B492605
theorem B557779 : Blo 327838 557779 := bstep (se 1 (by rfl) ⟨418334, by rfl⟩ : syracuseStep 557779 = 836669) B836669
theorem B492257 : Blo 327838 492257 := bstep (se 2 (by rfl) ⟨184596, by rfl⟩ : syracuseStep 492257 = 369193) B369193
theorem B631523 : Blo 327838 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B328419 : Blo 327838 328419 := bstep (se 1 (by rfl) ⟨246314, by rfl⟩ : syracuseStep 328419 = 492629) B492629
theorem B492275 : Blo 327838 492275 := bstep (se 1 (by rfl) ⟨369206, by rfl⟩ : syracuseStep 492275 = 738413) B738413
theorem B328435 : Blo 327838 328435 := bstep (se 1 (by rfl) ⟨246326, by rfl⟩ : syracuseStep 328435 = 492653) B492653
theorem B467699 : Blo 327838 467699 := bstep (se 1 (by rfl) ⟨350774, by rfl⟩ : syracuseStep 467699 = 701549) B701549
theorem B328451 : Blo 327838 328451 := bstep (se 1 (by rfl) ⟨246338, by rfl⟩ : syracuseStep 328451 = 492677) B492677
theorem B1114883 : Blo 327838 1114883 := bstep (se 1 (by rfl) ⟨836162, by rfl⟩ : syracuseStep 1114883 = 1672325) B1672325
theorem B934669 : Blo 327838 934669 := bstep (se 3 (by rfl) ⟨175250, by rfl⟩ : syracuseStep 934669 = 350501) B350501
theorem B492305 : Blo 327838 492305 := bstep (se 2 (by rfl) ⟨184614, by rfl⟩ : syracuseStep 492305 = 369229) B369229
theorem B369427 : Blo 327838 369427 := bstep (se 1 (by rfl) ⟨277070, by rfl⟩ : syracuseStep 369427 = 554141) B554141
theorem B328467 : Blo 327838 328467 := bstep (se 1 (by rfl) ⟨246350, by rfl⟩ : syracuseStep 328467 = 492701) B492701
theorem B492323 : Blo 327838 492323 := bstep (se 1 (by rfl) ⟨369242, by rfl⟩ : syracuseStep 492323 = 738485) B738485
theorem B328483 : Blo 327838 328483 := bstep (se 1 (by rfl) ⟨246362, by rfl⟩ : syracuseStep 328483 = 492725) B492725
theorem B328499 : Blo 327838 328499 := bstep (se 1 (by rfl) ⟨246374, by rfl⟩ : syracuseStep 328499 = 492749) B492749
theorem B492353 : Blo 327838 492353 := bstep (se 2 (by rfl) ⟨184632, by rfl⟩ : syracuseStep 492353 = 369265) B369265
theorem B328515 : Blo 327838 328515 := bstep (se 1 (by rfl) ⟨246386, by rfl⟩ : syracuseStep 328515 = 492773) B492773
theorem B492371 : Blo 327838 492371 := bstep (se 1 (by rfl) ⟨369278, by rfl⟩ : syracuseStep 492371 = 738557) B738557
theorem B328531 : Blo 327838 328531 := bstep (se 1 (by rfl) ⟨246398, by rfl⟩ : syracuseStep 328531 = 492797) B492797
theorem B353107 : Blo 327838 353107 := bstep (se 1 (by rfl) ⟨264830, by rfl⟩ : syracuseStep 353107 = 529661) B529661
theorem B2491235 : Blo 327838 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B328547 : Blo 327838 328547 := bstep (se 1 (by rfl) ⟨246410, by rfl⟩ : syracuseStep 328547 = 492821) B492821
theorem B557921 : Blo 327838 557921 := bstep (se 2 (by rfl) ⟨209220, by rfl⟩ : syracuseStep 557921 = 418441) B418441
theorem B738161 : Blo 327838 738161 := bstep (se 2 (by rfl) ⟨276810, by rfl⟩ : syracuseStep 738161 = 553621) B553621
theorem B492401 : Blo 327838 492401 := bstep (se 2 (by rfl) ⟨184650, by rfl⟩ : syracuseStep 492401 = 369301) B369301
theorem B328563 : Blo 327838 328563 := bstep (se 1 (by rfl) ⟨246422, by rfl⟩ : syracuseStep 328563 = 492845) B492845
theorem B738179 : Blo 327838 738179 := bstep (se 1 (by rfl) ⟨553634, by rfl⟩ : syracuseStep 738179 = 1107269) B1107269
theorem B492419 : Blo 327838 492419 := bstep (se 1 (by rfl) ⟨369314, by rfl⟩ : syracuseStep 492419 = 738629) B738629
theorem B328579 : Blo 327838 328579 := bstep (se 1 (by rfl) ⟨246434, by rfl⟩ : syracuseStep 328579 = 492869) B492869
theorem B328595 : Blo 327838 328595 := bstep (se 1 (by rfl) ⟨246446, by rfl⟩ : syracuseStep 328595 = 492893) B492893
theorem B492449 : Blo 327838 492449 := bstep (se 2 (by rfl) ⟨184668, by rfl⟩ : syracuseStep 492449 = 369337) B369337
theorem B369571 : Blo 327838 369571 := bstep (se 1 (by rfl) ⟨277178, by rfl⟩ : syracuseStep 369571 = 554357) B554357
theorem B328611 : Blo 327838 328611 := bstep (se 1 (by rfl) ⟨246458, by rfl⟩ : syracuseStep 328611 = 492917) B492917
theorem B492467 : Blo 327838 492467 := bstep (se 1 (by rfl) ⟨369350, by rfl⟩ : syracuseStep 492467 = 738701) B738701
theorem B328627 : Blo 327838 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B328643 : Blo 327838 328643 := bstep (se 1 (by rfl) ⟨246482, by rfl⟩ : syracuseStep 328643 = 492965) B492965
theorem B492497 : Blo 327838 492497 := bstep (se 2 (by rfl) ⟨184686, by rfl⟩ : syracuseStep 492497 = 369373) B369373
theorem B328659 : Blo 327838 328659 := bstep (se 1 (by rfl) ⟨246494, by rfl⟩ : syracuseStep 328659 = 492989) B492989
theorem B558049 : Blo 327838 558049 := bstep (se 2 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 558049 = 418537) B418537
theorem B1893347 : Blo 327838 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B492515 : Blo 327838 492515 := bstep (se 1 (by rfl) ⟨369386, by rfl⟩ : syracuseStep 492515 = 738773) B738773
theorem B328675 : Blo 327838 328675 := bstep (se 1 (by rfl) ⟨246506, by rfl⟩ : syracuseStep 328675 = 493013) B493013
theorem B1672163 : Blo 327838 1672163 := bstep (se 1 (by rfl) ⟨1254122, by rfl⟩ : syracuseStep 1672163 = 2508245) B2508245
theorem B934897 : Blo 327838 934897 := bstep (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) B701173
theorem B328691 : Blo 327838 328691 := bstep (se 1 (by rfl) ⟨246518, by rfl⟩ : syracuseStep 328691 = 493037) B493037
theorem B3163121 : Blo 327838 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B492545 : Blo 327838 492545 := bstep (se 2 (by rfl) ⟨184704, by rfl⟩ : syracuseStep 492545 = 369409) B369409
theorem B328707 : Blo 327838 328707 := bstep (se 1 (by rfl) ⟨246530, by rfl⟩ : syracuseStep 328707 = 493061) B493061
theorem B558083 : Blo 327838 558083 := bstep (se 1 (by rfl) ⟨418562, by rfl⟩ : syracuseStep 558083 = 837125) B837125
theorem B1115153 : Blo 327838 1115153 := bstep (se 2 (by rfl) ⟨418182, by rfl⟩ : syracuseStep 1115153 = 836365) B836365
theorem B492563 : Blo 327838 492563 := bstep (se 1 (by rfl) ⟨369422, by rfl⟩ : syracuseStep 492563 = 738845) B738845
theorem B328723 : Blo 327838 328723 := bstep (se 1 (by rfl) ⟨246542, by rfl⟩ : syracuseStep 328723 = 493085) B493085
theorem B328739 : Blo 327838 328739 := bstep (se 1 (by rfl) ⟨246554, by rfl⟩ : syracuseStep 328739 = 493109) B493109
theorem B492593 : Blo 327838 492593 := bstep (se 2 (by rfl) ⟨184722, by rfl⟩ : syracuseStep 492593 = 369445) B369445
theorem B369715 : Blo 327838 369715 := bstep (se 1 (by rfl) ⟨277286, by rfl⟩ : syracuseStep 369715 = 554573) B554573
theorem B328755 : Blo 327838 328755 := bstep (se 1 (by rfl) ⟨246566, by rfl⟩ : syracuseStep 328755 = 493133) B493133
theorem B664643 : Blo 327838 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B492611 : Blo 327838 492611 := bstep (se 1 (by rfl) ⟨369458, by rfl⟩ : syracuseStep 492611 = 738917) B738917
theorem B328771 : Blo 327838 328771 := bstep (se 1 (by rfl) ⟨246578, by rfl⟩ : syracuseStep 328771 = 493157) B493157
theorem B836689 : Blo 327838 836689 := bstep (se 2 (by rfl) ⟨313758, by rfl⟩ : syracuseStep 836689 = 627517) B627517
theorem B328787 : Blo 327838 328787 := bstep (se 1 (by rfl) ⟨246590, by rfl⟩ : syracuseStep 328787 = 493181) B493181
theorem B492641 : Blo 327838 492641 := bstep (se 2 (by rfl) ⟨184740, by rfl⟩ : syracuseStep 492641 = 369481) B369481
theorem B328803 : Blo 327838 328803 := bstep (se 1 (by rfl) ⟨246602, by rfl⟩ : syracuseStep 328803 = 493205) B493205
theorem B1107053 : Blo 327838 1107053 := bstep (se 3 (by rfl) ⟨207572, by rfl⟩ : syracuseStep 1107053 = 415145) B415145
theorem B492659 : Blo 327838 492659 := bstep (se 1 (by rfl) ⟨369494, by rfl⟩ : syracuseStep 492659 = 738989) B738989
theorem B328819 : Blo 327838 328819 := bstep (se 1 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 328819 = 493229) B493229
theorem B328835 : Blo 327838 328835 := bstep (se 1 (by rfl) ⟨246626, by rfl⟩ : syracuseStep 328835 = 493253) B493253
theorem B705667 : Blo 327838 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B2114693 : Blo 327838 2114693 := bstep (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) B396505
theorem B525457 : Blo 327838 525457 := bstep (se 2 (by rfl) ⟨197046, by rfl⟩ : syracuseStep 525457 = 394093) B394093
theorem B738449 : Blo 327838 738449 := bstep (se 2 (by rfl) ⟨276918, by rfl⟩ : syracuseStep 738449 = 553837) B553837
theorem B935057 : Blo 327838 935057 := bstep (se 2 (by rfl) ⟨350646, by rfl⟩ : syracuseStep 935057 = 701293) B701293
theorem B492689 : Blo 327838 492689 := bstep (se 2 (by rfl) ⟨184758, by rfl⟩ : syracuseStep 492689 = 369517) B369517
theorem B328851 : Blo 327838 328851 := bstep (se 1 (by rfl) ⟨246638, by rfl⟩ : syracuseStep 328851 = 493277) B493277
theorem B1107107 : Blo 327838 1107107 := bstep (se 1 (by rfl) ⟨830330, by rfl⟩ : syracuseStep 1107107 = 1660661) B1660661
theorem B738467 : Blo 327838 738467 := bstep (se 1 (by rfl) ⟨553850, by rfl⟩ : syracuseStep 738467 = 1107701) B1107701
theorem B492707 : Blo 327838 492707 := bstep (se 1 (by rfl) ⟨369530, by rfl⟩ : syracuseStep 492707 = 739061) B739061
theorem B328867 : Blo 327838 328867 := bstep (se 1 (by rfl) ⟨246650, by rfl⟩ : syracuseStep 328867 = 493301) B493301
theorem B328883 : Blo 327838 328883 := bstep (se 1 (by rfl) ⟨246662, by rfl⟩ : syracuseStep 328883 = 493325) B493325
theorem B492737 : Blo 327838 492737 := bstep (se 2 (by rfl) ⟨184776, by rfl⟩ : syracuseStep 492737 = 369553) B369553
theorem B369859 : Blo 327838 369859 := bstep (se 1 (by rfl) ⟨277394, by rfl⟩ : syracuseStep 369859 = 554789) B554789
theorem B328899 : Blo 327838 328899 := bstep (se 1 (by rfl) ⟨246674, by rfl⟩ : syracuseStep 328899 = 493349) B493349
theorem B1205453 : Blo 327838 1205453 := bstep (se 3 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 1205453 = 452045) B452045
theorem B492755 : Blo 327838 492755 := bstep (se 1 (by rfl) ⟨369566, by rfl⟩ : syracuseStep 492755 = 739133) B739133
theorem B328915 : Blo 327838 328915 := bstep (se 1 (by rfl) ⟨246686, by rfl⟩ : syracuseStep 328915 = 493373) B493373
theorem B328931 : Blo 327838 328931 := bstep (se 1 (by rfl) ⟨246698, by rfl⟩ : syracuseStep 328931 = 493397) B493397
theorem B492785 : Blo 327838 492785 := bstep (se 2 (by rfl) ⟨184794, by rfl⟩ : syracuseStep 492785 = 369589) B369589
theorem B623857 : Blo 327838 623857 := bstep (se 2 (by rfl) ⟨233946, by rfl⟩ : syracuseStep 623857 = 467893) B467893
theorem B328947 : Blo 327838 328947 := bstep (se 1 (by rfl) ⟨246710, by rfl⟩ : syracuseStep 328947 = 493421) B493421
theorem B1524977 : Blo 327838 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B935171 : Blo 327838 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B492803 : Blo 327838 492803 := bstep (se 1 (by rfl) ⟨369602, by rfl⟩ : syracuseStep 492803 = 739205) B739205
theorem B328963 : Blo 327838 328963 := bstep (se 1 (by rfl) ⟨246722, by rfl⟩ : syracuseStep 328963 = 493445) B493445
theorem B328979 : Blo 327838 328979 := bstep (se 1 (by rfl) ⟨246734, by rfl⟩ : syracuseStep 328979 = 493469) B493469
theorem B492833 : Blo 327838 492833 := bstep (se 2 (by rfl) ⟨184812, by rfl⟩ : syracuseStep 492833 = 369625) B369625
theorem B1246499 : Blo 327838 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B328995 : Blo 327838 328995 := bstep (se 1 (by rfl) ⟨246746, by rfl⟩ : syracuseStep 328995 = 493493) B493493
theorem B492851 : Blo 327838 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B329011 : Blo 327838 329011 := bstep (se 1 (by rfl) ⟨246758, by rfl⟩ : syracuseStep 329011 = 493517) B493517
theorem B329027 : Blo 327838 329027 := bstep (se 1 (by rfl) ⟨246770, by rfl⟩ : syracuseStep 329027 = 493541) B493541
theorem B976205 : Blo 327838 976205 := bstep (se 3 (by rfl) ⟨183038, by rfl⟩ : syracuseStep 976205 = 366077) B366077
theorem B492881 : Blo 327838 492881 := bstep (se 2 (by rfl) ⟨184830, by rfl⟩ : syracuseStep 492881 = 369661) B369661
theorem B394579 : Blo 327838 394579 := bstep (se 1 (by rfl) ⟨295934, by rfl⟩ : syracuseStep 394579 = 591869) B591869
theorem B370003 : Blo 327838 370003 := bstep (se 1 (by rfl) ⟨277502, by rfl⟩ : syracuseStep 370003 = 555005) B555005
theorem B329043 : Blo 327838 329043 := bstep (se 1 (by rfl) ⟨246782, by rfl⟩ : syracuseStep 329043 = 493565) B493565
theorem B492899 : Blo 327838 492899 := bstep (se 1 (by rfl) ⟨369674, by rfl⟩ : syracuseStep 492899 = 739349) B739349
theorem B329059 : Blo 327838 329059 := bstep (se 1 (by rfl) ⟨246794, by rfl⟩ : syracuseStep 329059 = 493589) B493589
theorem B836963 : Blo 327838 836963 := bstep (se 1 (by rfl) ⟨627722, by rfl⟩ : syracuseStep 836963 = 1255445) B1255445
theorem B468337 : Blo 327838 468337 := bstep (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) B351253
theorem B329075 : Blo 327838 329075 := bstep (se 1 (by rfl) ⟨246806, by rfl⟩ : syracuseStep 329075 = 493613) B493613
theorem B492929 : Blo 327838 492929 := bstep (se 2 (by rfl) ⟨184848, by rfl⟩ : syracuseStep 492929 = 369697) B369697
theorem B329091 : Blo 327838 329091 := bstep (se 1 (by rfl) ⟨246818, by rfl⟩ : syracuseStep 329091 = 493637) B493637
theorem B705923 : Blo 327838 705923 := bstep (se 1 (by rfl) ⟨529442, by rfl⟩ : syracuseStep 705923 = 1058885) B1058885
theorem B624017 : Blo 327838 624017 := bstep (se 2 (by rfl) ⟨234006, by rfl⟩ : syracuseStep 624017 = 468013) B468013
theorem B492947 : Blo 327838 492947 := bstep (se 1 (by rfl) ⟨369710, by rfl⟩ : syracuseStep 492947 = 739421) B739421
theorem B329107 : Blo 327838 329107 := bstep (se 1 (by rfl) ⟨246830, by rfl⟩ : syracuseStep 329107 = 493661) B493661
theorem B329123 : Blo 327838 329123 := bstep (se 1 (by rfl) ⟨246842, by rfl⟩ : syracuseStep 329123 = 493685) B493685
theorem B1107377 : Blo 327838 1107377 := bstep (se 2 (by rfl) ⟨415266, by rfl⟩ : syracuseStep 1107377 = 830533) B830533
theorem B738737 : Blo 327838 738737 := bstep (se 2 (by rfl) ⟨277026, by rfl⟩ : syracuseStep 738737 = 554053) B554053
theorem B492977 : Blo 327838 492977 := bstep (se 2 (by rfl) ⟨184866, by rfl⟩ : syracuseStep 492977 = 369733) B369733
theorem B329139 : Blo 327838 329139 := bstep (se 1 (by rfl) ⟨246854, by rfl⟩ : syracuseStep 329139 = 493709) B493709
theorem B738755 : Blo 327838 738755 := bstep (se 1 (by rfl) ⟨554066, by rfl⟩ : syracuseStep 738755 = 1108133) B1108133
theorem B492995 : Blo 327838 492995 := bstep (se 1 (by rfl) ⟨369746, by rfl⟩ : syracuseStep 492995 = 739493) B739493
theorem B329155 : Blo 327838 329155 := bstep (se 1 (by rfl) ⟨246866, by rfl⟩ : syracuseStep 329155 = 493733) B493733
theorem B329171 : Blo 327838 329171 := bstep (se 1 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 329171 = 493757) B493757
theorem B493025 : Blo 327838 493025 := bstep (se 2 (by rfl) ⟨184884, by rfl⟩ : syracuseStep 493025 = 369769) B369769
theorem B468451 : Blo 327838 468451 := bstep (se 1 (by rfl) ⟨351338, by rfl⟩ : syracuseStep 468451 = 702677) B702677
theorem B370147 : Blo 327838 370147 := bstep (se 1 (by rfl) ⟨277610, by rfl⟩ : syracuseStep 370147 = 555221) B555221
theorem B329187 : Blo 327838 329187 := bstep (se 1 (by rfl) ⟨246890, by rfl⟩ : syracuseStep 329187 = 493781) B493781
theorem B2377187 : Blo 327838 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B493043 : Blo 327838 493043 := bstep (se 1 (by rfl) ⟨369782, by rfl⟩ : syracuseStep 493043 = 739565) B739565
theorem B329203 : Blo 327838 329203 := bstep (se 1 (by rfl) ⟨246902, by rfl⟩ : syracuseStep 329203 = 493805) B493805
theorem B329219 : Blo 327838 329219 := bstep (se 1 (by rfl) ⟨246914, by rfl⟩ : syracuseStep 329219 = 493829) B493829
theorem B1869317 : Blo 327838 1869317 := bstep (se 4 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 1869317 = 350497) B350497
theorem B493073 : Blo 327838 493073 := bstep (se 2 (by rfl) ⟨184902, by rfl⟩ : syracuseStep 493073 = 369805) B369805
theorem B1058321 : Blo 327838 1058321 := bstep (se 2 (by rfl) ⟨396870, by rfl⟩ : syracuseStep 1058321 = 793741) B793741
theorem B329235 : Blo 327838 329235 := bstep (se 1 (by rfl) ⟨246926, by rfl⟩ : syracuseStep 329235 = 493853) B493853
theorem B493091 : Blo 327838 493091 := bstep (se 1 (by rfl) ⟨369818, by rfl⟩ : syracuseStep 493091 = 739637) B739637
theorem B329251 : Blo 327838 329251 := bstep (se 1 (by rfl) ⟨246938, by rfl⟩ : syracuseStep 329251 = 493877) B493877
theorem B1877539 : Blo 327838 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B837155 : Blo 327838 837155 := bstep (se 1 (by rfl) ⟨627866, by rfl⟩ : syracuseStep 837155 = 1255733) B1255733
theorem B1115693 : Blo 327838 1115693 := bstep (se 3 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 1115693 = 418385) B418385
theorem B329267 : Blo 327838 329267 := bstep (se 1 (by rfl) ⟨246950, by rfl⟩ : syracuseStep 329267 = 493901) B493901
theorem B493121 : Blo 327838 493121 := bstep (se 2 (by rfl) ⟨184920, by rfl⟩ : syracuseStep 493121 = 369841) B369841
theorem B329283 : Blo 327838 329283 := bstep (se 1 (by rfl) ⟨246962, by rfl⟩ : syracuseStep 329283 = 493925) B493925
theorem B493139 : Blo 327838 493139 := bstep (se 1 (by rfl) ⟨369854, by rfl⟩ : syracuseStep 493139 = 739709) B739709
theorem B329299 : Blo 327838 329299 := bstep (se 1 (by rfl) ⟨246974, by rfl⟩ : syracuseStep 329299 = 493949) B493949
theorem B329315 : Blo 327838 329315 := bstep (se 1 (by rfl) ⟨246986, by rfl⟩ : syracuseStep 329315 = 493973) B493973
theorem B1115747 : Blo 327838 1115747 := bstep (se 1 (by rfl) ⟨836810, by rfl⟩ : syracuseStep 1115747 = 1673621) B1673621
theorem B886385 : Blo 327838 886385 := bstep (se 2 (by rfl) ⟨332394, by rfl⟩ : syracuseStep 886385 = 664789) B664789
theorem B493169 : Blo 327838 493169 := bstep (se 2 (by rfl) ⟨184938, by rfl⟩ : syracuseStep 493169 = 369877) B369877
theorem B1877617 : Blo 327838 1877617 := bstep (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) B1408213
theorem B370291 : Blo 327838 370291 := bstep (se 1 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 370291 = 555437) B555437
theorem B329331 : Blo 327838 329331 := bstep (se 1 (by rfl) ⟨246998, by rfl⟩ : syracuseStep 329331 = 493997) B493997
theorem B493187 : Blo 327838 493187 := bstep (se 1 (by rfl) ⟨369890, by rfl⟩ : syracuseStep 493187 = 739781) B739781
theorem B329347 : Blo 327838 329347 := bstep (se 1 (by rfl) ⟨247010, by rfl⟩ : syracuseStep 329347 = 494021) B494021
theorem B329363 : Blo 327838 329363 := bstep (se 1 (by rfl) ⟨247022, by rfl⟩ : syracuseStep 329363 = 494045) B494045
theorem B493217 : Blo 327838 493217 := bstep (se 2 (by rfl) ⟨184956, by rfl⟩ : syracuseStep 493217 = 369913) B369913
theorem B329379 : Blo 327838 329379 := bstep (se 1 (by rfl) ⟨247034, by rfl⟩ : syracuseStep 329379 = 494069) B494069
theorem B493235 : Blo 327838 493235 := bstep (se 1 (by rfl) ⟨369926, by rfl⟩ : syracuseStep 493235 = 739853) B739853
theorem B329395 : Blo 327838 329395 := bstep (se 1 (by rfl) ⟨247046, by rfl⟩ : syracuseStep 329395 = 494093) B494093
theorem B329411 : Blo 327838 329411 := bstep (se 1 (by rfl) ⟨247058, by rfl⟩ : syracuseStep 329411 = 494117) B494117
theorem B739025 : Blo 327838 739025 := bstep (se 2 (by rfl) ⟨277134, by rfl⟩ : syracuseStep 739025 = 554269) B554269
theorem B493265 : Blo 327838 493265 := bstep (se 2 (by rfl) ⟨184974, by rfl⟩ : syracuseStep 493265 = 369949) B369949
theorem B329427 : Blo 327838 329427 := bstep (se 1 (by rfl) ⟨247070, by rfl⟩ : syracuseStep 329427 = 494141) B494141
theorem B739043 : Blo 327838 739043 := bstep (se 1 (by rfl) ⟨554282, by rfl⟩ : syracuseStep 739043 = 1108565) B1108565
theorem B493283 : Blo 327838 493283 := bstep (se 1 (by rfl) ⟨369962, by rfl⟩ : syracuseStep 493283 = 739925) B739925
theorem B329443 : Blo 327838 329443 := bstep (se 1 (by rfl) ⟨247082, by rfl⟩ : syracuseStep 329443 = 494165) B494165
theorem B1124077 : Blo 327838 1124077 := bstep (se 3 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 1124077 = 421529) B421529
theorem B329459 : Blo 327838 329459 := bstep (se 1 (by rfl) ⟨247094, by rfl⟩ : syracuseStep 329459 = 494189) B494189
theorem B493313 : Blo 327838 493313 := bstep (se 2 (by rfl) ⟨184992, by rfl⟩ : syracuseStep 493313 = 369985) B369985
theorem B370435 : Blo 327838 370435 := bstep (se 1 (by rfl) ⟨277826, by rfl⟩ : syracuseStep 370435 = 555653) B555653
theorem B329475 : Blo 327838 329475 := bstep (se 1 (by rfl) ⟨247106, by rfl⟩ : syracuseStep 329475 = 494213) B494213
theorem B952067 : Blo 327838 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B1672973 : Blo 327838 1672973 := bstep (se 3 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 1672973 = 627365) B627365
theorem B493331 : Blo 327838 493331 := bstep (se 1 (by rfl) ⟨369998, by rfl⟩ : syracuseStep 493331 = 739997) B739997
theorem B329491 : Blo 327838 329491 := bstep (se 1 (by rfl) ⟨247118, by rfl⟩ : syracuseStep 329491 = 494237) B494237
theorem B624419 : Blo 327838 624419 := bstep (se 1 (by rfl) ⟨468314, by rfl⟩ : syracuseStep 624419 = 936629) B936629
theorem B329507 : Blo 327838 329507 := bstep (se 1 (by rfl) ⟨247130, by rfl⟩ : syracuseStep 329507 = 494261) B494261
theorem B444209 : Blo 327838 444209 := bstep (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) B333157
theorem B493361 : Blo 327838 493361 := bstep (se 2 (by rfl) ⟨185010, by rfl⟩ : syracuseStep 493361 = 370021) B370021
theorem B329523 : Blo 327838 329523 := bstep (se 1 (by rfl) ⟨247142, by rfl⟩ : syracuseStep 329523 = 494285) B494285
theorem B493379 : Blo 327838 493379 := bstep (se 1 (by rfl) ⟨370034, by rfl⟩ : syracuseStep 493379 = 740069) B740069
theorem B329539 : Blo 327838 329539 := bstep (se 1 (by rfl) ⟨247154, by rfl⟩ : syracuseStep 329539 = 494309) B494309
theorem B329555 : Blo 327838 329555 := bstep (se 1 (by rfl) ⟨247166, by rfl⟩ : syracuseStep 329555 = 494333) B494333
theorem B493409 : Blo 327838 493409 := bstep (se 2 (by rfl) ⟨185028, by rfl⟩ : syracuseStep 493409 = 370057) B370057
theorem B329571 : Blo 327838 329571 := bstep (se 1 (by rfl) ⟨247178, by rfl⟩ : syracuseStep 329571 = 494357) B494357
theorem B493427 : Blo 327838 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B329587 : Blo 327838 329587 := bstep (se 1 (by rfl) ⟨247190, by rfl⟩ : syracuseStep 329587 = 494381) B494381
theorem B329603 : Blo 327838 329603 := bstep (se 1 (by rfl) ⟨247202, by rfl⟩ : syracuseStep 329603 = 494405) B494405
theorem B493457 : Blo 327838 493457 := bstep (se 2 (by rfl) ⟨185046, by rfl⟩ : syracuseStep 493457 = 370093) B370093
theorem B370579 : Blo 327838 370579 := bstep (se 1 (by rfl) ⟨277934, by rfl⟩ : syracuseStep 370579 = 555869) B555869
theorem B329619 : Blo 327838 329619 := bstep (se 1 (by rfl) ⟨247214, by rfl⟩ : syracuseStep 329619 = 494429) B494429
theorem B493475 : Blo 327838 493475 := bstep (se 1 (by rfl) ⟨370106, by rfl⟩ : syracuseStep 493475 = 740213) B740213
theorem B329635 : Blo 327838 329635 := bstep (se 1 (by rfl) ⟨247226, by rfl⟩ : syracuseStep 329635 = 494453) B494453
theorem B526259 : Blo 327838 526259 := bstep (se 1 (by rfl) ⟨394694, by rfl⟩ : syracuseStep 526259 = 789389) B789389
theorem B329651 : Blo 327838 329651 := bstep (se 1 (by rfl) ⟨247238, by rfl⟩ : syracuseStep 329651 = 494477) B494477
theorem B493505 : Blo 327838 493505 := bstep (se 2 (by rfl) ⟨185064, by rfl⟩ : syracuseStep 493505 = 370129) B370129
theorem B329667 : Blo 327838 329667 := bstep (se 1 (by rfl) ⟨247250, by rfl⟩ : syracuseStep 329667 = 494501) B494501
theorem B6301637 : Blo 327838 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B5392325 : Blo 327838 5392325 := bstep (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) B1011061
theorem B5638085 : Blo 327838 5638085 := bstep (se 4 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 5638085 = 1057141) B1057141
theorem B1107917 : Blo 327838 1107917 := bstep (se 3 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 1107917 = 415469) B415469
theorem B1140689 : Blo 327838 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B493523 : Blo 327838 493523 := bstep (se 1 (by rfl) ⟨370142, by rfl⟩ : syracuseStep 493523 = 740285) B740285
theorem B329683 : Blo 327838 329683 := bstep (se 1 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 329683 = 494525) B494525
theorem B329699 : Blo 327838 329699 := bstep (se 1 (by rfl) ⟨247274, by rfl⟩ : syracuseStep 329699 = 494549) B494549
theorem B739313 : Blo 327838 739313 := bstep (se 2 (by rfl) ⟨277242, by rfl⟩ : syracuseStep 739313 = 554485) B554485
theorem B493553 : Blo 327838 493553 := bstep (se 2 (by rfl) ⟨185082, by rfl⟩ : syracuseStep 493553 = 370165) B370165
theorem B329715 : Blo 327838 329715 := bstep (se 1 (by rfl) ⟨247286, by rfl⟩ : syracuseStep 329715 = 494573) B494573
theorem B1107971 : Blo 327838 1107971 := bstep (se 1 (by rfl) ⟨830978, by rfl⟩ : syracuseStep 1107971 = 1661957) B1661957
theorem B739331 : Blo 327838 739331 := bstep (se 1 (by rfl) ⟨554498, by rfl⟩ : syracuseStep 739331 = 1108997) B1108997
theorem B493571 : Blo 327838 493571 := bstep (se 1 (by rfl) ⟨370178, by rfl⟩ : syracuseStep 493571 = 740357) B740357
theorem B329731 : Blo 327838 329731 := bstep (se 1 (by rfl) ⟨247298, by rfl⟩ : syracuseStep 329731 = 494597) B494597
theorem B329747 : Blo 327838 329747 := bstep (se 1 (by rfl) ⟨247310, by rfl⟩ : syracuseStep 329747 = 494621) B494621
theorem B493601 : Blo 327838 493601 := bstep (se 2 (by rfl) ⟨185100, by rfl⟩ : syracuseStep 493601 = 370201) B370201
theorem B370723 : Blo 327838 370723 := bstep (se 1 (by rfl) ⟨278042, by rfl⟩ : syracuseStep 370723 = 556085) B556085
theorem B329763 : Blo 327838 329763 := bstep (se 1 (by rfl) ⟨247322, by rfl⟩ : syracuseStep 329763 = 494645) B494645
theorem B1255459 : Blo 327838 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B1878065 : Blo 327838 1878065 := bstep (se 2 (by rfl) ⟨704274, by rfl⟩ : syracuseStep 1878065 = 1408549) B1408549
theorem B493619 : Blo 327838 493619 := bstep (se 1 (by rfl) ⟨370214, by rfl⟩ : syracuseStep 493619 = 740429) B740429
theorem B329779 : Blo 327838 329779 := bstep (se 1 (by rfl) ⟨247334, by rfl⟩ : syracuseStep 329779 = 494669) B494669
theorem B329795 : Blo 327838 329795 := bstep (se 1 (by rfl) ⟨247346, by rfl⟩ : syracuseStep 329795 = 494693) B494693
theorem B493649 : Blo 327838 493649 := bstep (se 2 (by rfl) ⟨185118, by rfl⟩ : syracuseStep 493649 = 370237) B370237
theorem B329811 : Blo 327838 329811 := bstep (se 1 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 329811 = 494717) B494717
theorem B493667 : Blo 327838 493667 := bstep (se 1 (by rfl) ⟨370250, by rfl⟩ : syracuseStep 493667 = 740501) B740501
theorem B329827 : Blo 327838 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B329843 : Blo 327838 329843 := bstep (se 1 (by rfl) ⟨247382, by rfl⟩ : syracuseStep 329843 = 494765) B494765
theorem B493697 : Blo 327838 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B329859 : Blo 327838 329859 := bstep (se 1 (by rfl) ⟨247394, by rfl⟩ : syracuseStep 329859 = 494789) B494789
theorem B493715 : Blo 327838 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B329875 : Blo 327838 329875 := bstep (se 1 (by rfl) ⟨247406, by rfl⟩ : syracuseStep 329875 = 494813) B494813
theorem B329891 : Blo 327838 329891 := bstep (se 1 (by rfl) ⟨247418, by rfl⟩ : syracuseStep 329891 = 494837) B494837
theorem B493745 : Blo 327838 493745 := bstep (se 2 (by rfl) ⟨185154, by rfl⟩ : syracuseStep 493745 = 370309) B370309
theorem B1427633 : Blo 327838 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B370867 : Blo 327838 370867 := bstep (se 1 (by rfl) ⟨278150, by rfl⟩ : syracuseStep 370867 = 556301) B556301
theorem B329907 : Blo 327838 329907 := bstep (se 1 (by rfl) ⟨247430, by rfl⟩ : syracuseStep 329907 = 494861) B494861
theorem B493763 : Blo 327838 493763 := bstep (se 1 (by rfl) ⟨370322, by rfl⟩ : syracuseStep 493763 = 740645) B740645
theorem B329923 : Blo 327838 329923 := bstep (se 1 (by rfl) ⟨247442, by rfl⟩ : syracuseStep 329923 = 494885) B494885
theorem B329939 : Blo 327838 329939 := bstep (se 1 (by rfl) ⟨247454, by rfl⟩ : syracuseStep 329939 = 494909) B494909
theorem B493793 : Blo 327838 493793 := bstep (se 2 (by rfl) ⟨185172, by rfl⟩ : syracuseStep 493793 = 370345) B370345
theorem B329955 : Blo 327838 329955 := bstep (se 1 (by rfl) ⟨247466, by rfl⟩ : syracuseStep 329955 = 494933) B494933
theorem B936173 : Blo 327838 936173 := bstep (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) B351065
theorem B493811 : Blo 327838 493811 := bstep (se 1 (by rfl) ⟨370358, by rfl⟩ : syracuseStep 493811 = 740717) B740717
theorem B329971 : Blo 327838 329971 := bstep (se 1 (by rfl) ⟨247478, by rfl⟩ : syracuseStep 329971 = 494957) B494957
theorem B329987 : Blo 327838 329987 := bstep (se 1 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 329987 = 494981) B494981
theorem B1894661 : Blo 327838 1894661 := bstep (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) B355249
theorem B1247501 : Blo 327838 1247501 := bstep (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) B467813
theorem B887057 : Blo 327838 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B1108241 : Blo 327838 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B739601 : Blo 327838 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B493841 : Blo 327838 493841 := bstep (se 2 (by rfl) ⟨185190, by rfl⟩ : syracuseStep 493841 = 370381) B370381
theorem B330003 : Blo 327838 330003 := bstep (se 1 (by rfl) ⟨247502, by rfl⟩ : syracuseStep 330003 = 495005) B495005
theorem B10455317 : Blo 327838 10455317 := bstep (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) B490093
theorem B739619 : Blo 327838 739619 := bstep (se 1 (by rfl) ⟨554714, by rfl⟩ : syracuseStep 739619 = 1109429) B1109429
theorem B493859 : Blo 327838 493859 := bstep (se 1 (by rfl) ⟨370394, by rfl⟩ : syracuseStep 493859 = 740789) B740789
theorem B330019 : Blo 327838 330019 := bstep (se 1 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 330019 = 495029) B495029
theorem B330035 : Blo 327838 330035 := bstep (se 1 (by rfl) ⟨247526, by rfl⟩ : syracuseStep 330035 = 495053) B495053
theorem B493889 : Blo 327838 493889 := bstep (se 2 (by rfl) ⟨185208, by rfl⟩ : syracuseStep 493889 = 370417) B370417
theorem B444739 : Blo 327838 444739 := bstep (se 1 (by rfl) ⟨333554, by rfl⟩ : syracuseStep 444739 = 667109) B667109
theorem B371011 : Blo 327838 371011 := bstep (se 1 (by rfl) ⟨278258, by rfl⟩ : syracuseStep 371011 = 556517) B556517
theorem B330051 : Blo 327838 330051 := bstep (se 1 (by rfl) ⟨247538, by rfl⟩ : syracuseStep 330051 = 495077) B495077
theorem B493907 : Blo 327838 493907 := bstep (se 1 (by rfl) ⟨370430, by rfl⟩ : syracuseStep 493907 = 740861) B740861
theorem B330067 : Blo 327838 330067 := bstep (se 1 (by rfl) ⟨247550, by rfl⟩ : syracuseStep 330067 = 495101) B495101
theorem B600419 : Blo 327838 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B330083 : Blo 327838 330083 := bstep (se 1 (by rfl) ⟨247562, by rfl⟩ : syracuseStep 330083 = 495125) B495125
theorem B493937 : Blo 327838 493937 := bstep (se 2 (by rfl) ⟨185226, by rfl⟩ : syracuseStep 493937 = 370453) B370453
theorem B330099 : Blo 327838 330099 := bstep (se 1 (by rfl) ⟨247574, by rfl⟩ : syracuseStep 330099 = 495149) B495149
theorem B493955 : Blo 327838 493955 := bstep (se 1 (by rfl) ⟨370466, by rfl⟩ : syracuseStep 493955 = 740933) B740933
theorem B330115 : Blo 327838 330115 := bstep (se 1 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 330115 = 495173) B495173
theorem B330131 : Blo 327838 330131 := bstep (se 1 (by rfl) ⟨247598, by rfl⟩ : syracuseStep 330131 = 495197) B495197
theorem B493985 : Blo 327838 493985 := bstep (se 2 (by rfl) ⟨185244, by rfl⟩ : syracuseStep 493985 = 370489) B370489
theorem B936355 : Blo 327838 936355 := bstep (se 1 (by rfl) ⟨702266, by rfl⟩ : syracuseStep 936355 = 1404533) B1404533
theorem B330147 : Blo 327838 330147 := bstep (se 1 (by rfl) ⟨247610, by rfl⟩ : syracuseStep 330147 = 495221) B495221
theorem B1411505 : Blo 327838 1411505 := bstep (se 2 (by rfl) ⟨529314, by rfl⟩ : syracuseStep 1411505 = 1058629) B1058629
theorem B526771 : Blo 327838 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B494003 : Blo 327838 494003 := bstep (se 1 (by rfl) ⟨370502, by rfl⟩ : syracuseStep 494003 = 741005) B741005
theorem B330163 : Blo 327838 330163 := bstep (se 1 (by rfl) ⟨247622, by rfl⟩ : syracuseStep 330163 = 495245) B495245
theorem B2853317 : Blo 327838 2853317 := bstep (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) B534997
theorem B330179 : Blo 327838 330179 := bstep (se 1 (by rfl) ⟨247634, by rfl⟩ : syracuseStep 330179 = 495269) B495269
theorem B494033 : Blo 327838 494033 := bstep (se 2 (by rfl) ⟨185262, by rfl⟩ : syracuseStep 494033 = 370525) B370525
theorem B371155 : Blo 327838 371155 := bstep (se 1 (by rfl) ⟨278366, by rfl⟩ : syracuseStep 371155 = 556733) B556733
theorem B330195 : Blo 327838 330195 := bstep (se 1 (by rfl) ⟨247646, by rfl⟩ : syracuseStep 330195 = 495293) B495293
theorem B494051 : Blo 327838 494051 := bstep (se 1 (by rfl) ⟨370538, by rfl⟩ : syracuseStep 494051 = 741077) B741077
theorem B330211 : Blo 327838 330211 := bstep (se 1 (by rfl) ⟨247658, by rfl⟩ : syracuseStep 330211 = 495317) B495317
theorem B1665521 : Blo 327838 1665521 := bstep (se 2 (by rfl) ⟨624570, by rfl⟩ : syracuseStep 1665521 = 1249141) B1249141
theorem B330227 : Blo 327838 330227 := bstep (se 1 (by rfl) ⟨247670, by rfl⟩ : syracuseStep 330227 = 495341) B495341
theorem B494081 : Blo 327838 494081 := bstep (se 2 (by rfl) ⟨185280, by rfl⟩ : syracuseStep 494081 = 370561) B370561
theorem B330243 : Blo 327838 330243 := bstep (se 1 (by rfl) ⟨247682, by rfl⟩ : syracuseStep 330243 = 495365) B495365
theorem B494099 : Blo 327838 494099 := bstep (se 1 (by rfl) ⟨370574, by rfl⟩ : syracuseStep 494099 = 741149) B741149
theorem B330259 : Blo 327838 330259 := bstep (se 1 (by rfl) ⟨247694, by rfl⟩ : syracuseStep 330259 = 495389) B495389
theorem B330275 : Blo 327838 330275 := bstep (se 1 (by rfl) ⟨247706, by rfl⟩ : syracuseStep 330275 = 495413) B495413
theorem B739889 : Blo 327838 739889 := bstep (se 2 (by rfl) ⟨277458, by rfl⟩ : syracuseStep 739889 = 554917) B554917
theorem B494129 : Blo 327838 494129 := bstep (se 2 (by rfl) ⟨185298, by rfl⟩ : syracuseStep 494129 = 370597) B370597
theorem B330291 : Blo 327838 330291 := bstep (se 1 (by rfl) ⟨247718, by rfl⟩ : syracuseStep 330291 = 495437) B495437
theorem B739907 : Blo 327838 739907 := bstep (se 1 (by rfl) ⟨554930, by rfl⟩ : syracuseStep 739907 = 1109861) B1109861
theorem B936515 : Blo 327838 936515 := bstep (se 1 (by rfl) ⟨702386, by rfl⟩ : syracuseStep 936515 = 1404773) B1404773
theorem B494147 : Blo 327838 494147 := bstep (se 1 (by rfl) ⟨370610, by rfl⟩ : syracuseStep 494147 = 741221) B741221
theorem B330307 : Blo 327838 330307 := bstep (se 1 (by rfl) ⟨247730, by rfl⟩ : syracuseStep 330307 = 495461) B495461
theorem B330323 : Blo 327838 330323 := bstep (se 1 (by rfl) ⟨247742, by rfl⟩ : syracuseStep 330323 = 495485) B495485
theorem B494177 : Blo 327838 494177 := bstep (se 2 (by rfl) ⟨185316, by rfl⟩ : syracuseStep 494177 = 370633) B370633
theorem B371299 : Blo 327838 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B330339 : Blo 327838 330339 := bstep (se 1 (by rfl) ⟨247754, by rfl⟩ : syracuseStep 330339 = 495509) B495509
theorem B494195 : Blo 327838 494195 := bstep (se 1 (by rfl) ⟨370646, by rfl⟩ : syracuseStep 494195 = 741293) B741293
theorem B330355 : Blo 327838 330355 := bstep (se 1 (by rfl) ⟨247766, by rfl⟩ : syracuseStep 330355 = 495533) B495533
theorem B330371 : Blo 327838 330371 := bstep (se 1 (by rfl) ⟨247778, by rfl⟩ : syracuseStep 330371 = 495557) B495557
theorem B1002125 : Blo 327838 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B494225 : Blo 327838 494225 := bstep (se 2 (by rfl) ⟨185334, by rfl⟩ : syracuseStep 494225 = 370669) B370669
theorem B330387 : Blo 327838 330387 := bstep (se 1 (by rfl) ⟨247790, by rfl⟩ : syracuseStep 330387 = 495581) B495581
theorem B625315 : Blo 327838 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B494243 : Blo 327838 494243 := bstep (se 1 (by rfl) ⟨370682, by rfl⟩ : syracuseStep 494243 = 741365) B741365
theorem B330403 : Blo 327838 330403 := bstep (se 1 (by rfl) ⟨247802, by rfl⟩ : syracuseStep 330403 = 495605) B495605
theorem B330419 : Blo 327838 330419 := bstep (se 1 (by rfl) ⟨247814, by rfl⟩ : syracuseStep 330419 = 495629) B495629
theorem B494273 : Blo 327838 494273 := bstep (se 2 (by rfl) ⟨185352, by rfl⟩ : syracuseStep 494273 = 370705) B370705
theorem B330435 : Blo 327838 330435 := bstep (se 1 (by rfl) ⟨247826, by rfl⟩ : syracuseStep 330435 = 495653) B495653
theorem B494291 : Blo 327838 494291 := bstep (se 1 (by rfl) ⟨370718, by rfl⟩ : syracuseStep 494291 = 741437) B741437
theorem B330451 : Blo 327838 330451 := bstep (se 1 (by rfl) ⟨247838, by rfl⟩ : syracuseStep 330451 = 495677) B495677
theorem B330467 : Blo 327838 330467 := bstep (se 1 (by rfl) ⟨247850, by rfl⟩ : syracuseStep 330467 = 495701) B495701
theorem B494321 : Blo 327838 494321 := bstep (se 2 (by rfl) ⟨185370, by rfl⟩ : syracuseStep 494321 = 370741) B370741
theorem B371443 : Blo 327838 371443 := bstep (se 1 (by rfl) ⟨278582, by rfl⟩ : syracuseStep 371443 = 557165) B557165
theorem B330483 : Blo 327838 330483 := bstep (se 1 (by rfl) ⟨247862, by rfl⟩ : syracuseStep 330483 = 495725) B495725
theorem B494339 : Blo 327838 494339 := bstep (se 1 (by rfl) ⟨370754, by rfl⟩ : syracuseStep 494339 = 741509) B741509
theorem B330499 : Blo 327838 330499 := bstep (se 1 (by rfl) ⟨247874, by rfl⟩ : syracuseStep 330499 = 495749) B495749
theorem B633617 : Blo 327838 633617 := bstep (se 2 (by rfl) ⟨237606, by rfl⟩ : syracuseStep 633617 = 475213) B475213
theorem B330515 : Blo 327838 330515 := bstep (se 1 (by rfl) ⟨247886, by rfl⟩ : syracuseStep 330515 = 495773) B495773
theorem B494369 : Blo 327838 494369 := bstep (se 2 (by rfl) ⟨185388, by rfl⟩ : syracuseStep 494369 = 370777) B370777
theorem B469795 : Blo 327838 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B330531 : Blo 327838 330531 := bstep (se 1 (by rfl) ⟨247898, by rfl⟩ : syracuseStep 330531 = 495797) B495797
theorem B1108781 : Blo 327838 1108781 := bstep (se 3 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 1108781 = 415793) B415793
theorem B494387 : Blo 327838 494387 := bstep (se 1 (by rfl) ⟨370790, by rfl⟩ : syracuseStep 494387 = 741581) B741581
theorem B330547 : Blo 327838 330547 := bstep (se 1 (by rfl) ⟨247910, by rfl⟩ : syracuseStep 330547 = 495821) B495821
theorem B625475 : Blo 327838 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B330563 : Blo 327838 330563 := bstep (se 1 (by rfl) ⟨247922, by rfl⟩ : syracuseStep 330563 = 495845) B495845
theorem B740177 : Blo 327838 740177 := bstep (se 2 (by rfl) ⟨277566, by rfl⟩ : syracuseStep 740177 = 555133) B555133
theorem B494417 : Blo 327838 494417 := bstep (se 2 (by rfl) ⟨185406, by rfl⟩ : syracuseStep 494417 = 370813) B370813
theorem B330579 : Blo 327838 330579 := bstep (se 1 (by rfl) ⟨247934, by rfl⟩ : syracuseStep 330579 = 495869) B495869
theorem B1108835 : Blo 327838 1108835 := bstep (se 1 (by rfl) ⟨831626, by rfl⟩ : syracuseStep 1108835 = 1663253) B1663253
theorem B740195 : Blo 327838 740195 := bstep (se 1 (by rfl) ⟨555146, by rfl⟩ : syracuseStep 740195 = 1110293) B1110293
theorem B494435 : Blo 327838 494435 := bstep (se 1 (by rfl) ⟨370826, by rfl⟩ : syracuseStep 494435 = 741653) B741653
theorem B330595 : Blo 327838 330595 := bstep (se 1 (by rfl) ⟨247946, by rfl⟩ : syracuseStep 330595 = 495893) B495893
theorem B830321 : Blo 327838 830321 := bstep (se 2 (by rfl) ⟨311370, by rfl⟩ : syracuseStep 830321 = 622741) B622741
theorem B330611 : Blo 327838 330611 := bstep (se 1 (by rfl) ⟨247958, by rfl⟩ : syracuseStep 330611 = 495917) B495917
theorem B494465 : Blo 327838 494465 := bstep (se 2 (by rfl) ⟨185424, by rfl⟩ : syracuseStep 494465 = 370849) B370849
theorem B371587 : Blo 327838 371587 := bstep (se 1 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 371587 = 557381) B557381
theorem B330627 : Blo 327838 330627 := bstep (se 1 (by rfl) ⟨247970, by rfl⟩ : syracuseStep 330627 = 495941) B495941
theorem B494483 : Blo 327838 494483 := bstep (se 1 (by rfl) ⟨370862, by rfl⟩ : syracuseStep 494483 = 741725) B741725
theorem B330643 : Blo 327838 330643 := bstep (se 1 (by rfl) ⟨247982, by rfl⟩ : syracuseStep 330643 = 495965) B495965
theorem B830371 : Blo 327838 830371 := bstep (se 1 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 830371 = 1245557) B1245557
theorem B1051555 : Blo 327838 1051555 := bstep (se 1 (by rfl) ⟨788666, by rfl⟩ : syracuseStep 1051555 = 1577333) B1577333
theorem B330659 : Blo 327838 330659 := bstep (se 1 (by rfl) ⟨247994, by rfl⟩ : syracuseStep 330659 = 495989) B495989
theorem B494513 : Blo 327838 494513 := bstep (se 2 (by rfl) ⟨185442, by rfl⟩ : syracuseStep 494513 = 370885) B370885
theorem B330675 : Blo 327838 330675 := bstep (se 1 (by rfl) ⟨248006, by rfl⟩ : syracuseStep 330675 = 496013) B496013
theorem B494531 : Blo 327838 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B330691 : Blo 327838 330691 := bstep (se 1 (by rfl) ⟨248018, by rfl⟩ : syracuseStep 330691 = 496037) B496037
theorem B527315 : Blo 327838 527315 := bstep (se 1 (by rfl) ⟨395486, by rfl⟩ : syracuseStep 527315 = 790973) B790973
theorem B330707 : Blo 327838 330707 := bstep (se 1 (by rfl) ⟨248030, by rfl⟩ : syracuseStep 330707 = 496061) B496061
theorem B494561 : Blo 327838 494561 := bstep (se 2 (by rfl) ⟨185460, by rfl⟩ : syracuseStep 494561 = 370921) B370921
theorem B330723 : Blo 327838 330723 := bstep (se 1 (by rfl) ⟨248042, by rfl⟩ : syracuseStep 330723 = 496085) B496085
theorem B494579 : Blo 327838 494579 := bstep (se 1 (by rfl) ⟨370934, by rfl⟩ : syracuseStep 494579 = 741869) B741869
theorem B330739 : Blo 327838 330739 := bstep (se 1 (by rfl) ⟨248054, by rfl⟩ : syracuseStep 330739 = 496109) B496109
theorem B1125389 : Blo 327838 1125389 := bstep (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) B422021
theorem B592913 : Blo 327838 592913 := bstep (se 2 (by rfl) ⟨222342, by rfl⟩ : syracuseStep 592913 = 444685) B444685
theorem B494609 : Blo 327838 494609 := bstep (se 2 (by rfl) ⟨185478, by rfl⟩ : syracuseStep 494609 = 370957) B370957
theorem B371731 : Blo 327838 371731 := bstep (se 1 (by rfl) ⟨278798, by rfl⟩ : syracuseStep 371731 = 557597) B557597
theorem B494627 : Blo 327838 494627 := bstep (se 1 (by rfl) ⟨370970, by rfl⟩ : syracuseStep 494627 = 741941) B741941
theorem B830513 : Blo 327838 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B1051697 : Blo 327838 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B494657 : Blo 327838 494657 := bstep (se 2 (by rfl) ⟨185496, by rfl⟩ : syracuseStep 494657 = 370993) B370993
theorem B494675 : Blo 327838 494675 := bstep (se 1 (by rfl) ⟨371006, by rfl⟩ : syracuseStep 494675 = 742013) B742013
theorem B396371 : Blo 327838 396371 := bstep (se 1 (by rfl) ⟨297278, by rfl⟩ : syracuseStep 396371 = 594557) B594557
theorem B912493 : Blo 327838 912493 := bstep (se 3 (by rfl) ⟨171092, by rfl⟩ : syracuseStep 912493 = 342185) B342185
theorem B1109105 : Blo 327838 1109105 := bstep (se 2 (by rfl) ⟨415914, by rfl⟩ : syracuseStep 1109105 = 831829) B831829
theorem B740465 : Blo 327838 740465 := bstep (se 2 (by rfl) ⟨277674, by rfl⟩ : syracuseStep 740465 = 555349) B555349
theorem B494705 : Blo 327838 494705 := bstep (se 2 (by rfl) ⟨185514, by rfl⟩ : syracuseStep 494705 = 371029) B371029
theorem B527489 : Blo 327838 527489 := bstep (se 2 (by rfl) ⟨197808, by rfl⟩ : syracuseStep 527489 = 395617) B395617
theorem B740483 : Blo 327838 740483 := bstep (se 1 (by rfl) ⟨555362, by rfl⟩ : syracuseStep 740483 = 1110725) B1110725
theorem B494723 : Blo 327838 494723 := bstep (se 1 (by rfl) ⟨371042, by rfl⟩ : syracuseStep 494723 = 742085) B742085
theorem B494753 : Blo 327838 494753 := bstep (se 2 (by rfl) ⟨185532, by rfl⟩ : syracuseStep 494753 = 371065) B371065
theorem B371875 : Blo 327838 371875 := bstep (se 1 (by rfl) ⟨278906, by rfl⟩ : syracuseStep 371875 = 557813) B557813
theorem B494771 : Blo 327838 494771 := bstep (se 1 (by rfl) ⟨371078, by rfl⟩ : syracuseStep 494771 = 742157) B742157
theorem B494801 : Blo 327838 494801 := bstep (se 2 (by rfl) ⟨185550, by rfl⟩ : syracuseStep 494801 = 371101) B371101
theorem B494819 : Blo 327838 494819 := bstep (se 1 (by rfl) ⟨371114, by rfl⟩ : syracuseStep 494819 = 742229) B742229
theorem B494849 : Blo 327838 494849 := bstep (se 2 (by rfl) ⟨185568, by rfl⟩ : syracuseStep 494849 = 371137) B371137
theorem B494867 : Blo 327838 494867 := bstep (se 1 (by rfl) ⟨371150, by rfl⟩ : syracuseStep 494867 = 742301) B742301
theorem B593201 : Blo 327838 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B494897 : Blo 327838 494897 := bstep (se 2 (by rfl) ⟨185586, by rfl⟩ : syracuseStep 494897 = 371173) B371173
theorem B372019 : Blo 327838 372019 := bstep (se 1 (by rfl) ⟨279014, by rfl⟩ : syracuseStep 372019 = 558029) B558029
theorem B494915 : Blo 327838 494915 := bstep (se 1 (by rfl) ⟨371186, by rfl⟩ : syracuseStep 494915 = 742373) B742373
theorem B494945 : Blo 327838 494945 := bstep (se 2 (by rfl) ⟨185604, by rfl⟩ : syracuseStep 494945 = 371209) B371209
theorem B1116017 : Blo 327838 1116017 := bstep (se 2 (by rfl) ⟨418506, by rfl⟩ : syracuseStep 1116017 = 837013) B837013
theorem B494963 : Blo 327838 494963 := bstep (se 1 (by rfl) ⟨371222, by rfl⟩ : syracuseStep 494963 = 742445) B742445
theorem B3165581 : Blo 327838 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B748945 : Blo 327838 748945 := bstep (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) B561709
theorem B740753 : Blo 327838 740753 := bstep (se 2 (by rfl) ⟨277782, by rfl⟩ : syracuseStep 740753 = 555565) B555565
theorem B494993 : Blo 327838 494993 := bstep (se 2 (by rfl) ⟨185622, by rfl⟩ : syracuseStep 494993 = 371245) B371245
theorem B740771 : Blo 327838 740771 := bstep (se 1 (by rfl) ⟨555578, by rfl⟩ : syracuseStep 740771 = 1111157) B1111157
theorem B495011 : Blo 327838 495011 := bstep (se 1 (by rfl) ⟨371258, by rfl⟩ : syracuseStep 495011 = 742517) B742517
theorem B495041 : Blo 327838 495041 := bstep (se 2 (by rfl) ⟨185640, by rfl⟩ : syracuseStep 495041 = 371281) B371281
theorem B1125827 : Blo 327838 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B4214213 : Blo 327838 4214213 := bstep (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) B790165
theorem B495059 : Blo 327838 495059 := bstep (se 1 (by rfl) ⟨371294, by rfl⟩ : syracuseStep 495059 = 742589) B742589
theorem B1879523 : Blo 327838 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B495089 : Blo 327838 495089 := bstep (se 2 (by rfl) ⟨185658, by rfl⟩ : syracuseStep 495089 = 371317) B371317
theorem B495107 : Blo 327838 495107 := bstep (se 1 (by rfl) ⟨371330, by rfl⟩ : syracuseStep 495107 = 742661) B742661
theorem B495137 : Blo 327838 495137 := bstep (se 2 (by rfl) ⟨185676, by rfl⟩ : syracuseStep 495137 = 371353) B371353
theorem B495155 : Blo 327838 495155 := bstep (se 1 (by rfl) ⟨371366, by rfl⟩ : syracuseStep 495155 = 742733) B742733
theorem B577091 : Blo 327838 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B495185 : Blo 327838 495185 := bstep (se 2 (by rfl) ⟨185694, by rfl⟩ : syracuseStep 495185 = 371389) B371389
theorem B495203 : Blo 327838 495203 := bstep (se 1 (by rfl) ⟨371402, by rfl⟩ : syracuseStep 495203 = 742805) B742805
theorem B937585 : Blo 327838 937585 := bstep (se 2 (by rfl) ⟨351594, by rfl⟩ : syracuseStep 937585 = 703189) B703189
theorem B495233 : Blo 327838 495233 := bstep (se 2 (by rfl) ⟨185712, by rfl⟩ : syracuseStep 495233 = 371425) B371425
theorem B1109645 : Blo 327838 1109645 := bstep (se 3 (by rfl) ⟨208058, by rfl⟩ : syracuseStep 1109645 = 416117) B416117
theorem B1904269 : Blo 327838 1904269 := bstep (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) B714101
theorem B495251 : Blo 327838 495251 := bstep (se 1 (by rfl) ⟨371438, by rfl⟩ : syracuseStep 495251 = 742877) B742877
theorem B741041 : Blo 327838 741041 := bstep (se 2 (by rfl) ⟨277890, by rfl⟩ : syracuseStep 741041 = 555781) B555781
theorem B495281 : Blo 327838 495281 := bstep (se 2 (by rfl) ⟨185730, by rfl⟩ : syracuseStep 495281 = 371461) B371461
theorem B1109699 : Blo 327838 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B741059 : Blo 327838 741059 := bstep (se 1 (by rfl) ⟨555794, by rfl⟩ : syracuseStep 741059 = 1111589) B1111589
theorem B495299 : Blo 327838 495299 := bstep (se 1 (by rfl) ⟨371474, by rfl⟩ : syracuseStep 495299 = 742949) B742949
theorem B495329 : Blo 327838 495329 := bstep (se 2 (by rfl) ⟨185748, by rfl⟩ : syracuseStep 495329 = 371497) B371497
theorem B495347 : Blo 327838 495347 := bstep (se 1 (by rfl) ⟨371510, by rfl⟩ : syracuseStep 495347 = 743021) B743021
theorem B397043 : Blo 327838 397043 := bstep (se 1 (by rfl) ⟨297782, by rfl⟩ : syracuseStep 397043 = 595565) B595565
theorem B2502413 : Blo 327838 2502413 := bstep (se 3 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 2502413 = 938405) B938405
theorem B495377 : Blo 327838 495377 := bstep (se 2 (by rfl) ⟨185766, by rfl⟩ : syracuseStep 495377 = 371533) B371533
theorem B495395 : Blo 327838 495395 := bstep (se 1 (by rfl) ⟨371546, by rfl⟩ : syracuseStep 495395 = 743093) B743093
theorem B2117411 : Blo 327838 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B495425 : Blo 327838 495425 := bstep (se 2 (by rfl) ⟨185784, by rfl⟩ : syracuseStep 495425 = 371569) B371569
theorem B790339 : Blo 327838 790339 := bstep (se 1 (by rfl) ⟨592754, by rfl⟩ : syracuseStep 790339 = 1185509) B1185509
theorem B495443 : Blo 327838 495443 := bstep (se 1 (by rfl) ⟨371582, by rfl⟩ : syracuseStep 495443 = 743165) B743165
theorem B626545 : Blo 327838 626545 := bstep (se 2 (by rfl) ⟨234954, by rfl⟩ : syracuseStep 626545 = 469909) B469909
theorem B4231025 : Blo 327838 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B495473 : Blo 327838 495473 := bstep (se 2 (by rfl) ⟨185802, by rfl⟩ : syracuseStep 495473 = 371605) B371605
theorem B495491 : Blo 327838 495491 := bstep (se 1 (by rfl) ⟨371618, by rfl⟩ : syracuseStep 495491 = 743237) B743237
theorem B5345165 : Blo 327838 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B470929 : Blo 327838 470929 := bstep (se 2 (by rfl) ⟨176598, by rfl⟩ : syracuseStep 470929 = 353197) B353197
theorem B495521 : Blo 327838 495521 := bstep (se 2 (by rfl) ⟨185820, by rfl⟩ : syracuseStep 495521 = 371641) B371641
theorem B1666979 : Blo 327838 1666979 := bstep (se 1 (by rfl) ⟨1250234, by rfl⟩ : syracuseStep 1666979 = 2500469) B2500469
theorem B557651 : Blo 327838 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B495539 : Blo 327838 495539 := bstep (se 1 (by rfl) ⟨371654, by rfl⟩ : syracuseStep 495539 = 743309) B743309
theorem B1109969 : Blo 327838 1109969 := bstep (se 2 (by rfl) ⟨416238, by rfl⟩ : syracuseStep 1109969 = 832477) B832477
theorem B741329 : Blo 327838 741329 := bstep (se 2 (by rfl) ⟨277998, by rfl⟩ : syracuseStep 741329 = 555997) B555997
theorem B495569 : Blo 327838 495569 := bstep (se 2 (by rfl) ⟨185838, by rfl⟩ : syracuseStep 495569 = 371677) B371677
theorem B741347 : Blo 327838 741347 := bstep (se 1 (by rfl) ⟨556010, by rfl⟩ : syracuseStep 741347 = 1112021) B1112021
theorem B495587 : Blo 327838 495587 := bstep (se 1 (by rfl) ⟨371690, by rfl⟩ : syracuseStep 495587 = 743381) B743381
theorem B495617 : Blo 327838 495617 := bstep (se 2 (by rfl) ⟨185856, by rfl⟩ : syracuseStep 495617 = 371713) B371713
theorem B831505 : Blo 327838 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B495635 : Blo 327838 495635 := bstep (se 1 (by rfl) ⟨371726, by rfl⟩ : syracuseStep 495635 = 743453) B743453
theorem B495665 : Blo 327838 495665 := bstep (se 2 (by rfl) ⟨185874, by rfl⟩ : syracuseStep 495665 = 371749) B371749
theorem B495683 : Blo 327838 495683 := bstep (se 1 (by rfl) ⟨371762, by rfl⟩ : syracuseStep 495683 = 743525) B743525
theorem B495713 : Blo 327838 495713 := bstep (se 2 (by rfl) ⟨185892, by rfl⟩ : syracuseStep 495713 = 371785) B371785
theorem B495731 : Blo 327838 495731 := bstep (se 1 (by rfl) ⟨371798, by rfl⟩ : syracuseStep 495731 = 743597) B743597
theorem B495761 : Blo 327838 495761 := bstep (se 2 (by rfl) ⟨185910, by rfl⟩ : syracuseStep 495761 = 371821) B371821
theorem B495779 : Blo 327838 495779 := bstep (se 1 (by rfl) ⟨371834, by rfl⟩ : syracuseStep 495779 = 743669) B743669
theorem B495809 : Blo 327838 495809 := bstep (se 2 (by rfl) ⟨185928, by rfl⟩ : syracuseStep 495809 = 371857) B371857
theorem B1405133 : Blo 327838 1405133 := bstep (se 3 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 1405133 = 526925) B526925
theorem B495827 : Blo 327838 495827 := bstep (se 1 (by rfl) ⟨371870, by rfl⟩ : syracuseStep 495827 = 743741) B743741
theorem B741617 : Blo 327838 741617 := bstep (se 2 (by rfl) ⟨278106, by rfl⟩ : syracuseStep 741617 = 556213) B556213
theorem B495857 : Blo 327838 495857 := bstep (se 2 (by rfl) ⟨185946, by rfl⟩ : syracuseStep 495857 = 371893) B371893
theorem B741635 : Blo 327838 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B495875 : Blo 327838 495875 := bstep (se 1 (by rfl) ⟨371906, by rfl⟩ : syracuseStep 495875 = 743813) B743813
theorem B495905 : Blo 327838 495905 := bstep (se 2 (by rfl) ⟨185964, by rfl⟩ : syracuseStep 495905 = 371929) B371929
theorem B831779 : Blo 327838 831779 := bstep (se 1 (by rfl) ⟨623834, by rfl⟩ : syracuseStep 831779 = 1247669) B1247669
theorem B700721 : Blo 327838 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B495923 : Blo 327838 495923 := bstep (se 1 (by rfl) ⟨371942, by rfl⟩ : syracuseStep 495923 = 743885) B743885
theorem B1773893 : Blo 327838 1773893 := bstep (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) B332605
theorem B1249613 : Blo 327838 1249613 := bstep (se 3 (by rfl) ⟨234302, by rfl⟩ : syracuseStep 1249613 = 468605) B468605
theorem B553297 : Blo 327838 553297 := bstep (se 2 (by rfl) ⟨207486, by rfl⟩ : syracuseStep 553297 = 414973) B414973
theorem B495953 : Blo 327838 495953 := bstep (se 2 (by rfl) ⟨185982, by rfl⟩ : syracuseStep 495953 = 371965) B371965
theorem B495971 : Blo 327838 495971 := bstep (se 1 (by rfl) ⟨371978, by rfl⟩ : syracuseStep 495971 = 743957) B743957
theorem B790897 : Blo 327838 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B553331 : Blo 327838 553331 := bstep (se 1 (by rfl) ⟨414998, by rfl⟩ : syracuseStep 553331 = 829997) B829997
theorem B496001 : Blo 327838 496001 := bstep (se 2 (by rfl) ⟨186000, by rfl⟩ : syracuseStep 496001 = 372001) B372001
theorem B1126801 : Blo 327838 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B496019 : Blo 327838 496019 := bstep (se 1 (by rfl) ⟨372014, by rfl⟩ : syracuseStep 496019 = 744029) B744029
theorem B496049 : Blo 327838 496049 := bstep (se 2 (by rfl) ⟨186018, by rfl⟩ : syracuseStep 496049 = 372037) B372037
theorem B496067 : Blo 327838 496067 := bstep (se 1 (by rfl) ⟨372050, by rfl⟩ : syracuseStep 496067 = 744101) B744101
theorem B2822597 : Blo 327838 2822597 := bstep (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) B529237
theorem B496097 : Blo 327838 496097 := bstep (se 2 (by rfl) ⟨186036, by rfl⟩ : syracuseStep 496097 = 372073) B372073
theorem B831971 : Blo 327838 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B1110509 : Blo 327838 1110509 := bstep (se 3 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 1110509 = 416441) B416441
theorem B553459 : Blo 327838 553459 := bstep (se 1 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 553459 = 830189) B830189
theorem B496115 : Blo 327838 496115 := bstep (se 1 (by rfl) ⟨372086, by rfl⟩ : syracuseStep 496115 = 744173) B744173
theorem B741905 : Blo 327838 741905 := bstep (se 2 (by rfl) ⟨278214, by rfl⟩ : syracuseStep 741905 = 556429) B556429
theorem B1110563 : Blo 327838 1110563 := bstep (se 1 (by rfl) ⟨832922, by rfl⟩ : syracuseStep 1110563 = 1665845) B1665845
theorem B741923 : Blo 327838 741923 := bstep (se 1 (by rfl) ⟨556442, by rfl⟩ : syracuseStep 741923 = 1112885) B1112885
theorem B2814533 : Blo 327838 2814533 := bstep (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) B527725
theorem B1004141 : Blo 327838 1004141 := bstep (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) B376553
theorem B1143409 : Blo 327838 1143409 := bstep (se 2 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 1143409 = 857557) B857557
theorem B553601 : Blo 327838 553601 := bstep (se 2 (by rfl) ⟨207600, by rfl⟩ : syracuseStep 553601 = 415201) B415201
theorem B3609269 : Blo 327838 3609269 := bstep (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) B338369
theorem B4264645 : Blo 327838 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B1667789 : Blo 327838 1667789 := bstep (se 3 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 1667789 = 625421) B625421
theorem B553729 : Blo 327838 553729 := bstep (se 2 (by rfl) ⟨207648, by rfl⟩ : syracuseStep 553729 = 415297) B415297
theorem B553763 : Blo 327838 553763 := bstep (se 1 (by rfl) ⟨415322, by rfl⟩ : syracuseStep 553763 = 830645) B830645
theorem B1110833 : Blo 327838 1110833 := bstep (se 2 (by rfl) ⟨416562, by rfl⟩ : syracuseStep 1110833 = 833125) B833125
theorem B742193 : Blo 327838 742193 := bstep (se 2 (by rfl) ⟨278322, by rfl⟩ : syracuseStep 742193 = 556645) B556645
theorem B742211 : Blo 327838 742211 := bstep (se 1 (by rfl) ⟨556658, by rfl⟩ : syracuseStep 742211 = 1113317) B1113317
theorem B938861 : Blo 327838 938861 := bstep (se 3 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 938861 = 352073) B352073
theorem B627601 : Blo 327838 627601 := bstep (se 2 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 627601 = 470701) B470701
theorem B553891 : Blo 327838 553891 := bstep (se 1 (by rfl) ⟨415418, by rfl⟩ : syracuseStep 553891 = 830837) B830837
theorem B791569 : Blo 327838 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B1127459 : Blo 327838 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B939043 : Blo 327838 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B963629 : Blo 327838 963629 := bstep (se 3 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 963629 = 361361) B361361
theorem B554033 : Blo 327838 554033 := bstep (se 2 (by rfl) ⟨207762, by rfl⟩ : syracuseStep 554033 = 415525) B415525
theorem B1496141 : Blo 327838 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B939089 : Blo 327838 939089 := bstep (se 2 (by rfl) ⟨352158, by rfl⟩ : syracuseStep 939089 = 704317) B704317
theorem B742481 : Blo 327838 742481 := bstep (se 2 (by rfl) ⟨278430, by rfl⟩ : syracuseStep 742481 = 556861) B556861
theorem B742499 : Blo 327838 742499 := bstep (se 1 (by rfl) ⟨556874, by rfl⟩ : syracuseStep 742499 = 1113749) B1113749
theorem B529507 : Blo 327838 529507 := bstep (se 1 (by rfl) ⟨397130, by rfl⟩ : syracuseStep 529507 = 794261) B794261
theorem B1250417 : Blo 327838 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B2823281 : Blo 327838 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B595075 : Blo 327838 595075 := bstep (se 1 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 595075 = 892613) B892613
theorem B529571 : Blo 327838 529571 := bstep (se 1 (by rfl) ⟨397178, by rfl⟩ : syracuseStep 529571 = 794357) B794357
theorem B554161 : Blo 327838 554161 := bstep (se 2 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 554161 = 415621) B415621
theorem B701617 : Blo 327838 701617 := bstep (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) B526213
theorem B701635 : Blo 327838 701635 := bstep (se 1 (by rfl) ⟨526226, by rfl⟩ : syracuseStep 701635 = 1052453) B1052453
theorem B554195 : Blo 327838 554195 := bstep (se 1 (by rfl) ⟨415646, by rfl⟩ : syracuseStep 554195 = 831293) B831293
theorem B3994865 : Blo 327838 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B1873165 : Blo 327838 1873165 := bstep (se 3 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 1873165 = 702437) B702437
theorem B2102597 : Blo 327838 2102597 := bstep (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) B394237
theorem B1881413 : Blo 327838 1881413 := bstep (se 4 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 1881413 = 352765) B352765
theorem B1111373 : Blo 327838 1111373 := bstep (se 3 (by rfl) ⟨208382, by rfl⟩ : syracuseStep 1111373 = 416765) B416765
theorem B554323 : Blo 327838 554323 := bstep (se 1 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 554323 = 831485) B831485
theorem B3159395 : Blo 327838 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B742769 : Blo 327838 742769 := bstep (se 2 (by rfl) ⟨278538, by rfl⟩ : syracuseStep 742769 = 557077) B557077
theorem B1111427 : Blo 327838 1111427 := bstep (se 1 (by rfl) ⟨833570, by rfl⟩ : syracuseStep 1111427 = 1667141) B1667141
theorem B742787 : Blo 327838 742787 := bstep (se 1 (by rfl) ⟨557090, by rfl⟩ : syracuseStep 742787 = 1114181) B1114181
theorem B1054093 : Blo 327838 1054093 := bstep (se 3 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 1054093 = 395285) B395285
theorem B832913 : Blo 327838 832913 := bstep (se 2 (by rfl) ⟨312342, by rfl⟩ : syracuseStep 832913 = 624685) B624685
theorem B1570211 : Blo 327838 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B1660337 : Blo 327838 1660337 := bstep (se 2 (by rfl) ⟨622626, by rfl⟩ : syracuseStep 1660337 = 1245253) B1245253
theorem B832963 : Blo 327838 832963 := bstep (se 1 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 832963 = 1249445) B1249445
theorem B554465 : Blo 327838 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B1578467 : Blo 327838 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B333283 : Blo 327838 333283 := bstep (se 1 (by rfl) ⟨249962, by rfl⟩ : syracuseStep 333283 = 499925) B499925
theorem B833105 : Blo 327838 833105 := bstep (se 2 (by rfl) ⟨312414, by rfl⟩ : syracuseStep 833105 = 624829) B624829
theorem B554593 : Blo 327838 554593 := bstep (se 2 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 554593 = 415945) B415945
theorem B415363 : Blo 327838 415363 := bstep (se 1 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 415363 = 623045) B623045
theorem B554627 : Blo 327838 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B800401 : Blo 327838 800401 := bstep (se 2 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 800401 = 600301) B600301
theorem B1111697 : Blo 327838 1111697 := bstep (se 2 (by rfl) ⟨416886, by rfl⟩ : syracuseStep 1111697 = 833773) B833773
theorem B743057 : Blo 327838 743057 := bstep (se 2 (by rfl) ⟨278646, by rfl⟩ : syracuseStep 743057 = 557293) B557293
theorem B743075 : Blo 327838 743075 := bstep (se 1 (by rfl) ⟨557306, by rfl⟩ : syracuseStep 743075 = 1114613) B1114613
theorem B415459 : Blo 327838 415459 := bstep (se 1 (by rfl) ⟨311594, by rfl⟩ : syracuseStep 415459 = 623189) B623189
theorem B554755 : Blo 327838 554755 := bstep (se 1 (by rfl) ⟨416066, by rfl⟩ : syracuseStep 554755 = 832133) B832133
theorem B1251085 : Blo 327838 1251085 := bstep (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) B469157
theorem B751427 : Blo 327838 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B554897 : Blo 327838 554897 := bstep (se 2 (by rfl) ⟨208086, by rfl⟩ : syracuseStep 554897 = 416173) B416173
theorem B1775537 : Blo 327838 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B743345 : Blo 327838 743345 := bstep (se 2 (by rfl) ⟨278754, by rfl⟩ : syracuseStep 743345 = 557509) B557509
theorem B743363 : Blo 327838 743363 := bstep (se 1 (by rfl) ⟨557522, by rfl⟩ : syracuseStep 743363 = 1115045) B1115045
theorem B1128401 : Blo 327838 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B555025 : Blo 327838 555025 := bstep (se 2 (by rfl) ⟨208134, by rfl⟩ : syracuseStep 555025 = 416269) B416269
theorem B555059 : Blo 327838 555059 := bstep (se 1 (by rfl) ⟨416294, by rfl⟩ : syracuseStep 555059 = 832589) B832589
theorem B2496581 : Blo 327838 2496581 := bstep (se 4 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 2496581 = 468109) B468109
theorem B7108721 : Blo 327838 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B669809 : Blo 327838 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B1128593 : Blo 327838 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B893521 : Blo 327838 893521 := bstep (se 2 (by rfl) ⟨335070, by rfl⟩ : syracuseStep 893521 = 670141) B670141
theorem B1112237 : Blo 327838 1112237 := bstep (se 3 (by rfl) ⟨208544, by rfl⟩ : syracuseStep 1112237 = 417089) B417089
theorem B555187 : Blo 327838 555187 := bstep (se 1 (by rfl) ⟨416390, by rfl⟩ : syracuseStep 555187 = 832781) B832781
theorem B743633 : Blo 327838 743633 := bstep (se 2 (by rfl) ⟨278862, by rfl⟩ : syracuseStep 743633 = 557725) B557725
theorem B415955 : Blo 327838 415955 := bstep (se 1 (by rfl) ⟨311966, by rfl⟩ : syracuseStep 415955 = 623933) B623933
theorem B1112291 : Blo 327838 1112291 := bstep (se 1 (by rfl) ⟨834218, by rfl⟩ : syracuseStep 1112291 = 1668437) B1668437
theorem B743651 : Blo 327838 743651 := bstep (se 1 (by rfl) ⟨557738, by rfl⟩ : syracuseStep 743651 = 1115477) B1115477
theorem B4208881 : Blo 327838 4208881 := bstep (se 2 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 4208881 = 3156661) B3156661
theorem B4233485 : Blo 327838 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B563489 : Blo 327838 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B555329 : Blo 327838 555329 := bstep (se 2 (by rfl) ⟨208248, by rfl⟩ : syracuseStep 555329 = 416497) B416497
theorem B2259377 : Blo 327838 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B555457 : Blo 327838 555457 := bstep (se 2 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 555457 = 416593) B416593
theorem B555491 : Blo 327838 555491 := bstep (se 1 (by rfl) ⟨416618, by rfl⟩ : syracuseStep 555491 = 833237) B833237
theorem B1112561 : Blo 327838 1112561 := bstep (se 2 (by rfl) ⟨417210, by rfl⟩ : syracuseStep 1112561 = 834421) B834421
theorem B743921 : Blo 327838 743921 := bstep (se 2 (by rfl) ⟨278970, by rfl⟩ : syracuseStep 743921 = 557941) B557941
theorem B940547 : Blo 327838 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B743939 : Blo 327838 743939 := bstep (se 1 (by rfl) ⟨557954, by rfl⟩ : syracuseStep 743939 = 1115909) B1115909
theorem B1251875 : Blo 327838 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B834097 : Blo 327838 834097 := bstep (se 2 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 834097 = 625573) B625573
theorem B2259533 : Blo 327838 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B555619 : Blo 327838 555619 := bstep (se 1 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 555619 = 833429) B833429
theorem B2505329 : Blo 327838 2505329 := bstep (se 2 (by rfl) ⟨939498, by rfl⟩ : syracuseStep 2505329 = 1878997) B1878997
theorem B1145507 : Blo 327838 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B506579 : Blo 327838 506579 := bstep (se 1 (by rfl) ⟨379934, by rfl⟩ : syracuseStep 506579 = 759869) B759869
theorem B555761 : Blo 327838 555761 := bstep (se 2 (by rfl) ⟨208410, by rfl⟩ : syracuseStep 555761 = 416821) B416821
theorem B834371 : Blo 327838 834371 := bstep (se 1 (by rfl) ⟨625778, by rfl⟩ : syracuseStep 834371 = 1251557) B1251557
theorem B1661795 : Blo 327838 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B555889 : Blo 327838 555889 := bstep (se 2 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 555889 = 416917) B416917
theorem B351091 : Blo 327838 351091 := bstep (se 1 (by rfl) ⟨263318, by rfl⟩ : syracuseStep 351091 = 526637) B526637
theorem B3259277 : Blo 327838 3259277 := bstep (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) B1222229
theorem B416659 : Blo 327838 416659 := bstep (se 1 (by rfl) ⟨312494, by rfl⟩ : syracuseStep 416659 = 624989) B624989
theorem B555923 : Blo 327838 555923 := bstep (se 1 (by rfl) ⟨416942, by rfl⟩ : syracuseStep 555923 = 833885) B833885
theorem B498611 : Blo 327838 498611 := bstep (se 1 (by rfl) ⟨373958, by rfl⟩ : syracuseStep 498611 = 747917) B747917
theorem B2243555 : Blo 327838 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B416755 : Blo 327838 416755 := bstep (se 1 (by rfl) ⟨312566, by rfl⟩ : syracuseStep 416755 = 625133) B625133
theorem B834563 : Blo 327838 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B1113101 : Blo 327838 1113101 := bstep (se 3 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 1113101 = 417413) B417413
theorem B556051 : Blo 327838 556051 := bstep (se 1 (by rfl) ⟨417038, by rfl⟩ : syracuseStep 556051 = 834077) B834077
theorem B1113155 : Blo 327838 1113155 := bstep (se 1 (by rfl) ⟨834866, by rfl⟩ : syracuseStep 1113155 = 1669733) B1669733
theorem B556193 : Blo 327838 556193 := bstep (se 2 (by rfl) ⟨208572, by rfl⟩ : syracuseStep 556193 = 417145) B417145
theorem B1252529 : Blo 327838 1252529 := bstep (se 2 (by rfl) ⟨469698, by rfl⟩ : syracuseStep 1252529 = 939397) B939397
theorem B2579653 : Blo 327838 2579653 := bstep (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) B483685
theorem B1875149 : Blo 327838 1875149 := bstep (se 3 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 1875149 = 703181) B703181
theorem B1391843 : Blo 327838 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B556321 : Blo 327838 556321 := bstep (se 2 (by rfl) ⟨208620, by rfl⟩ : syracuseStep 556321 = 417241) B417241
theorem B556355 : Blo 327838 556355 := bstep (se 1 (by rfl) ⟨417266, by rfl⟩ : syracuseStep 556355 = 834533) B834533
theorem B1113425 : Blo 327838 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B2809201 : Blo 327838 2809201 := bstep (se 2 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 2809201 = 2106901) B2106901
theorem B703907 : Blo 327838 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B556483 : Blo 327838 556483 := bstep (se 1 (by rfl) ⟨417362, by rfl⟩ : syracuseStep 556483 = 834725) B834725
theorem B417251 : Blo 327838 417251 := bstep (se 1 (by rfl) ⟨312938, by rfl⟩ : syracuseStep 417251 = 625877) B625877
theorem B892387 : Blo 327838 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B892397 : Blo 327838 892397 := bstep (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) B334649
theorem B1670705 : Blo 327838 1670705 := bstep (se 2 (by rfl) ⟨626514, by rfl⟩ : syracuseStep 1670705 = 1253029) B1253029
theorem B1867333 : Blo 327838 1867333 := bstep (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) B350125
theorem B556625 : Blo 327838 556625 := bstep (se 2 (by rfl) ⟨208734, by rfl⟩ : syracuseStep 556625 = 417469) B417469
theorem B892529 : Blo 327838 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B1662605 : Blo 327838 1662605 := bstep (se 3 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 1662605 = 623477) B623477
theorem B8437445 : Blo 327838 8437445 := bstep (se 4 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 8437445 = 1582021) B1582021
theorem B556753 : Blo 327838 556753 := bstep (se 2 (by rfl) ⟨208782, by rfl⟩ : syracuseStep 556753 = 417565) B417565
theorem B941777 : Blo 327838 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B556787 : Blo 327838 556787 := bstep (se 1 (by rfl) ⟨417590, by rfl⟩ : syracuseStep 556787 = 835181) B835181
theorem B1498915 : Blo 327838 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B933713 : Blo 327838 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B3735395 : Blo 327838 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B1113965 : Blo 327838 1113965 := bstep (se 3 (by rfl) ⟨208868, by rfl⟩ : syracuseStep 1113965 = 417737) B417737
theorem B1245041 : Blo 327838 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B3383153 : Blo 327838 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B704369 : Blo 327838 704369 := bstep (se 2 (by rfl) ⟨264138, by rfl⟩ : syracuseStep 704369 = 528277) B528277
theorem B556915 : Blo 327838 556915 := bstep (se 1 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 556915 = 835373) B835373
theorem B1146737 : Blo 327838 1146737 := bstep (se 2 (by rfl) ⟨430026, by rfl⟩ : syracuseStep 1146737 = 860053) B860053
theorem B1777571 : Blo 327838 1777571 := bstep (se 1 (by rfl) ⟨1333178, by rfl⟩ : syracuseStep 1777571 = 2666357) B2666357
theorem B1114019 : Blo 327838 1114019 := bstep (se 1 (by rfl) ⟨835514, by rfl⟩ : syracuseStep 1114019 = 1671029) B1671029
theorem B835505 : Blo 327838 835505 := bstep (se 2 (by rfl) ⟨313314, by rfl⟩ : syracuseStep 835505 = 626629) B626629
theorem B950221 : Blo 327838 950221 := bstep (se 3 (by rfl) ⟨178166, by rfl⟩ : syracuseStep 950221 = 356333) B356333
theorem B753617 : Blo 327838 753617 := bstep (se 2 (by rfl) ⟨282606, by rfl⟩ : syracuseStep 753617 = 565213) B565213
theorem B835555 : Blo 327838 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B2506787 : Blo 327838 2506787 := bstep (se 1 (by rfl) ⟨1880090, by rfl⟩ : syracuseStep 2506787 = 3760181) B3760181
theorem B622657 : Blo 327838 622657 := bstep (se 2 (by rfl) ⟨233496, by rfl⟩ : syracuseStep 622657 = 466993) B466993
theorem B557131 : Blo 327838 557131 := bstep (se 1 (by rfl) ⟨417848, by rfl⟩ : syracuseStep 557131 = 835697) B835697
theorem B3006557 : Blo 327838 3006557 := bstep (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) B1127459
theorem B327851 : Blo 327838 327851 := bstep (se 1 (by rfl) ⟨245888, by rfl⟩ : syracuseStep 327851 = 491777) B491777
theorem B327863 : Blo 327838 327863 := bstep (se 1 (by rfl) ⟨245897, by rfl⟩ : syracuseStep 327863 = 491795) B491795
theorem B327883 : Blo 327838 327883 := bstep (se 1 (by rfl) ⟨245912, by rfl⟩ : syracuseStep 327883 = 491825) B491825
theorem B467147 : Blo 327838 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B327895 : Blo 327838 327895 := bstep (se 1 (by rfl) ⟨245921, by rfl⟩ : syracuseStep 327895 = 491843) B491843
theorem B557273 : Blo 327838 557273 := bstep (se 2 (by rfl) ⟨208977, by rfl⟩ : syracuseStep 557273 = 417955) B417955
theorem B1056989 : Blo 327838 1056989 := bstep (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) B396371
theorem B327915 : Blo 327838 327915 := bstep (se 1 (by rfl) ⟨245936, by rfl⟩ : syracuseStep 327915 = 491873) B491873
theorem B368887 : Blo 327838 368887 := bstep (se 1 (by rfl) ⟨276665, by rfl⟩ : syracuseStep 368887 = 553331) B553331
theorem B327927 : Blo 327838 327927 := bstep (se 1 (by rfl) ⟨245945, by rfl⟩ : syracuseStep 327927 = 491891) B491891
theorem B327947 : Blo 327838 327947 := bstep (se 1 (by rfl) ⟨245960, by rfl⟩ : syracuseStep 327947 = 491921) B491921
theorem B327959 : Blo 327838 327959 := bstep (se 1 (by rfl) ⟨245969, by rfl⟩ : syracuseStep 327959 = 491939) B491939
theorem B491801 : Blo 327838 491801 := bstep (se 2 (by rfl) ⟨184425, by rfl⟩ : syracuseStep 491801 = 368851) B368851
theorem B327979 : Blo 327838 327979 := bstep (se 1 (by rfl) ⟨245984, by rfl⟩ : syracuseStep 327979 = 491969) B491969
theorem B1786157 : Blo 327838 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B327991 : Blo 327838 327991 := bstep (se 1 (by rfl) ⟨245993, by rfl⟩ : syracuseStep 327991 = 491987) B491987
theorem B5611841 : Blo 327838 5611841 := bstep (se 2 (by rfl) ⟨2104440, by rfl⟩ : syracuseStep 5611841 = 4208881) B4208881
theorem B328011 : Blo 327838 328011 := bstep (se 1 (by rfl) ⟨246008, by rfl⟩ : syracuseStep 328011 = 492017) B492017
theorem B328023 : Blo 327838 328023 := bstep (se 1 (by rfl) ⟨246017, by rfl⟩ : syracuseStep 328023 = 492035) B492035
theorem B557401 : Blo 327838 557401 := bstep (se 2 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 557401 = 418051) B418051
theorem B328043 : Blo 327838 328043 := bstep (se 1 (by rfl) ⟨246032, by rfl⟩ : syracuseStep 328043 = 492065) B492065
theorem B328055 : Blo 327838 328055 := bstep (se 1 (by rfl) ⟨246041, by rfl⟩ : syracuseStep 328055 = 492083) B492083
theorem B1876355 : Blo 327838 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B737675 : Blo 327838 737675 := bstep (se 1 (by rfl) ⟨553256, by rfl⟩ : syracuseStep 737675 = 1106513) B1106513
theorem B491915 : Blo 327838 491915 := bstep (se 1 (by rfl) ⟨368936, by rfl⟩ : syracuseStep 491915 = 737873) B737873
theorem B328075 : Blo 327838 328075 := bstep (se 1 (by rfl) ⟨246056, by rfl⟩ : syracuseStep 328075 = 492113) B492113
theorem B491927 : Blo 327838 491927 := bstep (se 1 (by rfl) ⟨368945, by rfl⟩ : syracuseStep 491927 = 737891) B737891
theorem B328087 : Blo 327838 328087 := bstep (se 1 (by rfl) ⟨246065, by rfl⟩ : syracuseStep 328087 = 492131) B492131
theorem B835991 : Blo 327838 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B369067 : Blo 327838 369067 := bstep (se 1 (by rfl) ⟨276800, by rfl⟩ : syracuseStep 369067 = 553601) B553601
theorem B328107 : Blo 327838 328107 := bstep (se 1 (by rfl) ⟨246080, by rfl⟩ : syracuseStep 328107 = 492161) B492161
theorem B328119 : Blo 327838 328119 := bstep (se 1 (by rfl) ⟨246089, by rfl⟩ : syracuseStep 328119 = 492179) B492179
theorem B737729 : Blo 327838 737729 := bstep (se 2 (by rfl) ⟨276648, by rfl⟩ : syracuseStep 737729 = 553297) B553297
theorem B328139 : Blo 327838 328139 := bstep (se 1 (by rfl) ⟨246104, by rfl⟩ : syracuseStep 328139 = 492209) B492209
theorem B328151 : Blo 327838 328151 := bstep (se 1 (by rfl) ⟨246113, by rfl⟩ : syracuseStep 328151 = 492227) B492227
theorem B491993 : Blo 327838 491993 := bstep (se 2 (by rfl) ⟨184497, by rfl⟩ : syracuseStep 491993 = 368995) B368995
theorem B328171 : Blo 327838 328171 := bstep (se 1 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 328171 = 492257) B492257
theorem B328183 : Blo 327838 328183 := bstep (se 1 (by rfl) ⟨246137, by rfl⟩ : syracuseStep 328183 = 492275) B492275
theorem B328203 : Blo 327838 328203 := bstep (se 1 (by rfl) ⟨246152, by rfl⟩ : syracuseStep 328203 = 492305) B492305
theorem B369175 : Blo 327838 369175 := bstep (se 1 (by rfl) ⟨276881, by rfl⟩ : syracuseStep 369175 = 553763) B553763
theorem B328215 : Blo 327838 328215 := bstep (se 1 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 328215 = 492323) B492323
theorem B328235 : Blo 327838 328235 := bstep (se 1 (by rfl) ⟨246176, by rfl⟩ : syracuseStep 328235 = 492353) B492353
theorem B328247 : Blo 327838 328247 := bstep (se 1 (by rfl) ⟨246185, by rfl⟩ : syracuseStep 328247 = 492371) B492371
theorem B492107 : Blo 327838 492107 := bstep (se 1 (by rfl) ⟨369080, by rfl⟩ : syracuseStep 492107 = 738161) B738161
theorem B328267 : Blo 327838 328267 := bstep (se 1 (by rfl) ⟨246200, by rfl⟩ : syracuseStep 328267 = 492401) B492401
theorem B492119 : Blo 327838 492119 := bstep (se 1 (by rfl) ⟨369089, by rfl⟩ : syracuseStep 492119 = 738179) B738179
theorem B328279 : Blo 327838 328279 := bstep (se 1 (by rfl) ⟨246209, by rfl⟩ : syracuseStep 328279 = 492419) B492419
theorem B3711581 : Blo 327838 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B328299 : Blo 327838 328299 := bstep (se 1 (by rfl) ⟨246224, by rfl⟩ : syracuseStep 328299 = 492449) B492449
theorem B328311 : Blo 327838 328311 := bstep (se 1 (by rfl) ⟨246233, by rfl⟩ : syracuseStep 328311 = 492467) B492467
theorem B328331 : Blo 327838 328331 := bstep (se 1 (by rfl) ⟨246248, by rfl⟩ : syracuseStep 328331 = 492497) B492497
theorem B1262231 : Blo 327838 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B328343 : Blo 327838 328343 := bstep (se 1 (by rfl) ⟨246257, by rfl⟩ : syracuseStep 328343 = 492515) B492515
theorem B737945 : Blo 327838 737945 := bstep (se 2 (by rfl) ⟨276729, by rfl⟩ : syracuseStep 737945 = 553459) B553459
theorem B492185 : Blo 327838 492185 := bstep (se 2 (by rfl) ⟨184569, by rfl⟩ : syracuseStep 492185 = 369139) B369139
theorem B1114775 : Blo 327838 1114775 := bstep (se 1 (by rfl) ⟨836081, by rfl⟩ : syracuseStep 1114775 = 1672163) B1672163
theorem B328363 : Blo 327838 328363 := bstep (se 1 (by rfl) ⟨246272, by rfl⟩ : syracuseStep 328363 = 492545) B492545
theorem B328375 : Blo 327838 328375 := bstep (se 1 (by rfl) ⟨246281, by rfl⟩ : syracuseStep 328375 = 492563) B492563
theorem B369355 : Blo 327838 369355 := bstep (se 1 (by rfl) ⟨277016, by rfl⟩ : syracuseStep 369355 = 554033) B554033
theorem B328395 : Blo 327838 328395 := bstep (se 1 (by rfl) ⟨246296, by rfl⟩ : syracuseStep 328395 = 492593) B492593
theorem B328407 : Blo 327838 328407 := bstep (se 1 (by rfl) ⟨246305, by rfl⟩ : syracuseStep 328407 = 492611) B492611
theorem B328427 : Blo 327838 328427 := bstep (se 1 (by rfl) ⟨246320, by rfl⟩ : syracuseStep 328427 = 492641) B492641
theorem B738035 : Blo 327838 738035 := bstep (se 1 (by rfl) ⟨553526, by rfl⟩ : syracuseStep 738035 = 1107053) B1107053
theorem B328439 : Blo 327838 328439 := bstep (se 1 (by rfl) ⟨246329, by rfl⟩ : syracuseStep 328439 = 492659) B492659
theorem B1409795 : Blo 327838 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B2802437 : Blo 327838 2802437 := bstep (se 4 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 2802437 = 525457) B525457
theorem B492299 : Blo 327838 492299 := bstep (se 1 (by rfl) ⟨369224, by rfl⟩ : syracuseStep 492299 = 738449) B738449
theorem B623371 : Blo 327838 623371 := bstep (se 1 (by rfl) ⟨467528, by rfl⟩ : syracuseStep 623371 = 935057) B935057
theorem B328459 : Blo 327838 328459 := bstep (se 1 (by rfl) ⟨246344, by rfl⟩ : syracuseStep 328459 = 492689) B492689
theorem B738071 : Blo 327838 738071 := bstep (se 1 (by rfl) ⟨553553, by rfl⟩ : syracuseStep 738071 = 1107107) B1107107
theorem B492311 : Blo 327838 492311 := bstep (se 1 (by rfl) ⟨369233, by rfl⟩ : syracuseStep 492311 = 738467) B738467
theorem B328471 : Blo 327838 328471 := bstep (se 1 (by rfl) ⟨246353, by rfl⟩ : syracuseStep 328471 = 492707) B492707
theorem B353047 : Blo 327838 353047 := bstep (se 1 (by rfl) ⟨264785, by rfl⟩ : syracuseStep 353047 = 529571) B529571
theorem B328491 : Blo 327838 328491 := bstep (se 1 (by rfl) ⟨246368, by rfl⟩ : syracuseStep 328491 = 492737) B492737
theorem B1581869 : Blo 327838 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B369463 : Blo 327838 369463 := bstep (se 1 (by rfl) ⟨277097, by rfl⟩ : syracuseStep 369463 = 554195) B554195
theorem B328503 : Blo 327838 328503 := bstep (se 1 (by rfl) ⟨246377, by rfl⟩ : syracuseStep 328503 = 492755) B492755
theorem B1868609 : Blo 327838 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B1524545 : Blo 327838 1524545 := bstep (se 2 (by rfl) ⟨571704, by rfl⟩ : syracuseStep 1524545 = 1143409) B1143409
theorem B1672001 : Blo 327838 1672001 := bstep (se 2 (by rfl) ⟨627000, by rfl⟩ : syracuseStep 1672001 = 1254001) B1254001
theorem B2663243 : Blo 327838 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B328523 : Blo 327838 328523 := bstep (se 1 (by rfl) ⟨246392, by rfl⟩ : syracuseStep 328523 = 492785) B492785
theorem B1016651 : Blo 327838 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B623447 : Blo 327838 623447 := bstep (se 1 (by rfl) ⟨467585, by rfl⟩ : syracuseStep 623447 = 935171) B935171
theorem B328535 : Blo 327838 328535 := bstep (se 1 (by rfl) ⟨246401, by rfl⟩ : syracuseStep 328535 = 492803) B492803
theorem B492377 : Blo 327838 492377 := bstep (se 2 (by rfl) ⟨184641, by rfl⟩ : syracuseStep 492377 = 369283) B369283
theorem B328555 : Blo 327838 328555 := bstep (se 1 (by rfl) ⟨246416, by rfl⟩ : syracuseStep 328555 = 492833) B492833
theorem B328567 : Blo 327838 328567 := bstep (se 1 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 328567 = 492851) B492851
theorem B1401731 : Blo 327838 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B1254275 : Blo 327838 1254275 := bstep (se 1 (by rfl) ⟨940706, by rfl⟩ : syracuseStep 1254275 = 1881413) B1881413
theorem B328587 : Blo 327838 328587 := bstep (se 1 (by rfl) ⟨246440, by rfl⟩ : syracuseStep 328587 = 492881) B492881
theorem B328599 : Blo 327838 328599 := bstep (se 1 (by rfl) ⟨246449, by rfl⟩ : syracuseStep 328599 = 492899) B492899
theorem B2106263 : Blo 327838 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B557975 : Blo 327838 557975 := bstep (se 1 (by rfl) ⟨418481, by rfl⟩ : syracuseStep 557975 = 836963) B836963
theorem B328619 : Blo 327838 328619 := bstep (se 1 (by rfl) ⟨246464, by rfl⟩ : syracuseStep 328619 = 492929) B492929
theorem B5686193 : Blo 327838 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B328631 : Blo 327838 328631 := bstep (se 1 (by rfl) ⟨246473, by rfl⟩ : syracuseStep 328631 = 492947) B492947
theorem B1106891 : Blo 327838 1106891 := bstep (se 1 (by rfl) ⟨830168, by rfl⟩ : syracuseStep 1106891 = 1660337) B1660337
theorem B738251 : Blo 327838 738251 := bstep (se 1 (by rfl) ⟨553688, by rfl⟩ : syracuseStep 738251 = 1107377) B1107377
theorem B492491 : Blo 327838 492491 := bstep (se 1 (by rfl) ⟨369368, by rfl⟩ : syracuseStep 492491 = 738737) B738737
theorem B328651 : Blo 327838 328651 := bstep (se 1 (by rfl) ⟨246488, by rfl⟩ : syracuseStep 328651 = 492977) B492977
theorem B492503 : Blo 327838 492503 := bstep (se 1 (by rfl) ⟨369377, by rfl⟩ : syracuseStep 492503 = 738755) B738755
theorem B328663 : Blo 327838 328663 := bstep (se 1 (by rfl) ⟨246497, by rfl⟩ : syracuseStep 328663 = 492995) B492995
theorem B369643 : Blo 327838 369643 := bstep (se 1 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 369643 = 554465) B554465
theorem B328683 : Blo 327838 328683 := bstep (se 1 (by rfl) ⟨246512, by rfl⟩ : syracuseStep 328683 = 493025) B493025
theorem B328695 : Blo 327838 328695 := bstep (se 1 (by rfl) ⟨246521, by rfl⟩ : syracuseStep 328695 = 493043) B493043
theorem B738305 : Blo 327838 738305 := bstep (se 2 (by rfl) ⟨276864, by rfl⟩ : syracuseStep 738305 = 553729) B553729
theorem B1246211 : Blo 327838 1246211 := bstep (se 1 (by rfl) ⟨934658, by rfl⟩ : syracuseStep 1246211 = 1869317) B1869317
theorem B328715 : Blo 327838 328715 := bstep (se 1 (by rfl) ⟨246536, by rfl⟩ : syracuseStep 328715 = 493073) B493073
theorem B705547 : Blo 327838 705547 := bstep (se 1 (by rfl) ⟨529160, by rfl⟩ : syracuseStep 705547 = 1058321) B1058321
theorem B1246225 : Blo 327838 1246225 := bstep (se 2 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 1246225 = 934669) B934669
theorem B328727 : Blo 327838 328727 := bstep (se 1 (by rfl) ⟨246545, by rfl⟩ : syracuseStep 328727 = 493091) B493091
theorem B558103 : Blo 327838 558103 := bstep (se 1 (by rfl) ⟨418577, by rfl⟩ : syracuseStep 558103 = 837155) B837155
theorem B492569 : Blo 327838 492569 := bstep (se 2 (by rfl) ⟨184713, by rfl⟩ : syracuseStep 492569 = 369427) B369427
theorem B328747 : Blo 327838 328747 := bstep (se 1 (by rfl) ⟨246560, by rfl⟩ : syracuseStep 328747 = 493121) B493121
theorem B328759 : Blo 327838 328759 := bstep (se 1 (by rfl) ⟨246569, by rfl⟩ : syracuseStep 328759 = 493139) B493139
theorem B590923 : Blo 327838 590923 := bstep (se 1 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 590923 = 886385) B886385
theorem B328779 : Blo 327838 328779 := bstep (se 1 (by rfl) ⟨246584, by rfl⟩ : syracuseStep 328779 = 493169) B493169
theorem B369751 : Blo 327838 369751 := bstep (se 1 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 369751 = 554627) B554627
theorem B328791 : Blo 327838 328791 := bstep (se 1 (by rfl) ⟨246593, by rfl⟩ : syracuseStep 328791 = 493187) B493187
theorem B328811 : Blo 327838 328811 := bstep (se 1 (by rfl) ⟨246608, by rfl⟩ : syracuseStep 328811 = 493217) B493217
theorem B328823 : Blo 327838 328823 := bstep (se 1 (by rfl) ⟨246617, by rfl⟩ : syracuseStep 328823 = 493235) B493235
theorem B492683 : Blo 327838 492683 := bstep (se 1 (by rfl) ⟨369512, by rfl⟩ : syracuseStep 492683 = 739025) B739025
theorem B328843 : Blo 327838 328843 := bstep (se 1 (by rfl) ⟨246632, by rfl⟩ : syracuseStep 328843 = 493265) B493265
theorem B492695 : Blo 327838 492695 := bstep (se 1 (by rfl) ⟨369521, by rfl⟩ : syracuseStep 492695 = 739043) B739043
theorem B328855 : Blo 327838 328855 := bstep (se 1 (by rfl) ⟨246641, by rfl⟩ : syracuseStep 328855 = 493283) B493283
theorem B468121 : Blo 327838 468121 := bstep (se 2 (by rfl) ⟨175545, by rfl⟩ : syracuseStep 468121 = 351091) B351091
theorem B328875 : Blo 327838 328875 := bstep (se 1 (by rfl) ⟨246656, by rfl⟩ : syracuseStep 328875 = 493313) B493313
theorem B1115315 : Blo 327838 1115315 := bstep (se 1 (by rfl) ⟨836486, by rfl⟩ : syracuseStep 1115315 = 1672973) B1672973
theorem B328887 : Blo 327838 328887 := bstep (se 1 (by rfl) ⟨246665, by rfl⟩ : syracuseStep 328887 = 493331) B493331
theorem B836801 : Blo 327838 836801 := bstep (se 2 (by rfl) ⟨313800, by rfl⟩ : syracuseStep 836801 = 627601) B627601
theorem B328907 : Blo 327838 328907 := bstep (se 1 (by rfl) ⟨246680, by rfl⟩ : syracuseStep 328907 = 493361) B493361
theorem B328919 : Blo 327838 328919 := bstep (se 1 (by rfl) ⟨246689, by rfl⟩ : syracuseStep 328919 = 493379) B493379
theorem B500951 : Blo 327838 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B1107161 : Blo 327838 1107161 := bstep (se 2 (by rfl) ⟨415185, by rfl⟩ : syracuseStep 1107161 = 830371) B830371
theorem B738521 : Blo 327838 738521 := bstep (se 2 (by rfl) ⟨276945, by rfl⟩ : syracuseStep 738521 = 553891) B553891
theorem B1402073 : Blo 327838 1402073 := bstep (se 2 (by rfl) ⟨525777, by rfl⟩ : syracuseStep 1402073 = 1051555) B1051555
theorem B492761 : Blo 327838 492761 := bstep (se 2 (by rfl) ⟨184785, by rfl⟩ : syracuseStep 492761 = 369571) B369571
theorem B328939 : Blo 327838 328939 := bstep (se 1 (by rfl) ⟨246704, by rfl⟩ : syracuseStep 328939 = 493409) B493409
theorem B328951 : Blo 327838 328951 := bstep (se 1 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 328951 = 493427) B493427
theorem B369931 : Blo 327838 369931 := bstep (se 1 (by rfl) ⟨277448, by rfl⟩ : syracuseStep 369931 = 554897) B554897
theorem B328971 : Blo 327838 328971 := bstep (se 1 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 328971 = 493457) B493457
theorem B328983 : Blo 327838 328983 := bstep (se 1 (by rfl) ⟨246737, by rfl⟩ : syracuseStep 328983 = 493475) B493475
theorem B329003 : Blo 327838 329003 := bstep (se 1 (by rfl) ⟨246752, by rfl⟩ : syracuseStep 329003 = 493505) B493505
theorem B738611 : Blo 327838 738611 := bstep (se 1 (by rfl) ⟨553958, by rfl⟩ : syracuseStep 738611 = 1107917) B1107917
theorem B329015 : Blo 327838 329015 := bstep (se 1 (by rfl) ⟨246761, by rfl⟩ : syracuseStep 329015 = 493523) B493523
theorem B1246529 : Blo 327838 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B492875 : Blo 327838 492875 := bstep (se 1 (by rfl) ⟨369656, by rfl⟩ : syracuseStep 492875 = 739313) B739313
theorem B329035 : Blo 327838 329035 := bstep (se 1 (by rfl) ⟨246776, by rfl⟩ : syracuseStep 329035 = 493553) B493553
theorem B738647 : Blo 327838 738647 := bstep (se 1 (by rfl) ⟨553985, by rfl⟩ : syracuseStep 738647 = 1107971) B1107971
theorem B492887 : Blo 327838 492887 := bstep (se 1 (by rfl) ⟨369665, by rfl⟩ : syracuseStep 492887 = 739331) B739331
theorem B329047 : Blo 327838 329047 := bstep (se 1 (by rfl) ⟨246785, by rfl⟩ : syracuseStep 329047 = 493571) B493571
theorem B329067 : Blo 327838 329067 := bstep (se 1 (by rfl) ⟨246800, by rfl⟩ : syracuseStep 329067 = 493601) B493601
theorem B370039 : Blo 327838 370039 := bstep (se 1 (by rfl) ⟨277529, by rfl⟩ : syracuseStep 370039 = 555059) B555059
theorem B329079 : Blo 327838 329079 := bstep (se 1 (by rfl) ⟨246809, by rfl⟩ : syracuseStep 329079 = 493619) B493619
theorem B1664387 : Blo 327838 1664387 := bstep (se 1 (by rfl) ⟨1248290, by rfl⟩ : syracuseStep 1664387 = 2496581) B2496581
theorem B329099 : Blo 327838 329099 := bstep (se 1 (by rfl) ⟨246824, by rfl⟩ : syracuseStep 329099 = 493649) B493649
theorem B329111 : Blo 327838 329111 := bstep (se 1 (by rfl) ⟨246833, by rfl⟩ : syracuseStep 329111 = 493667) B493667
theorem B492953 : Blo 327838 492953 := bstep (se 2 (by rfl) ⟨184857, by rfl⟩ : syracuseStep 492953 = 369715) B369715
theorem B329131 : Blo 327838 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B329143 : Blo 327838 329143 := bstep (se 1 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 329143 = 493715) B493715
theorem B1115585 : Blo 327838 1115585 := bstep (se 2 (by rfl) ⟨418344, by rfl⟩ : syracuseStep 1115585 = 836689) B836689
theorem B329163 : Blo 327838 329163 := bstep (se 1 (by rfl) ⟨246872, by rfl⟩ : syracuseStep 329163 = 493745) B493745
theorem B951755 : Blo 327838 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B329175 : Blo 327838 329175 := bstep (se 1 (by rfl) ⟨246881, by rfl⟩ : syracuseStep 329175 = 493763) B493763
theorem B706009 : Blo 327838 706009 := bstep (se 2 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 706009 = 529507) B529507
theorem B329195 : Blo 327838 329195 := bstep (se 1 (by rfl) ⟨246896, by rfl⟩ : syracuseStep 329195 = 493793) B493793
theorem B624115 : Blo 327838 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B329207 : Blo 327838 329207 := bstep (se 1 (by rfl) ⟨246905, by rfl⟩ : syracuseStep 329207 = 493811) B493811
theorem B1263107 : Blo 327838 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B591371 : Blo 327838 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B738827 : Blo 327838 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B493067 : Blo 327838 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B329227 : Blo 327838 329227 := bstep (se 1 (by rfl) ⟨246920, by rfl⟩ : syracuseStep 329227 = 493841) B493841
theorem B493079 : Blo 327838 493079 := bstep (se 1 (by rfl) ⟨369809, by rfl⟩ : syracuseStep 493079 = 739619) B739619
theorem B329239 : Blo 327838 329239 := bstep (se 1 (by rfl) ⟨246929, by rfl⟩ : syracuseStep 329239 = 493859) B493859
theorem B370219 : Blo 327838 370219 := bstep (se 1 (by rfl) ⟨277664, by rfl⟩ : syracuseStep 370219 = 555329) B555329
theorem B329259 : Blo 327838 329259 := bstep (se 1 (by rfl) ⟨246944, by rfl⟩ : syracuseStep 329259 = 493889) B493889
theorem B329271 : Blo 327838 329271 := bstep (se 1 (by rfl) ⟨246953, by rfl⟩ : syracuseStep 329271 = 493907) B493907
theorem B738881 : Blo 327838 738881 := bstep (se 2 (by rfl) ⟨277080, by rfl⟩ : syracuseStep 738881 = 554161) B554161
theorem B935489 : Blo 327838 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B329291 : Blo 327838 329291 := bstep (se 1 (by rfl) ⟨246968, by rfl⟩ : syracuseStep 329291 = 493937) B493937
theorem B329303 : Blo 327838 329303 := bstep (se 1 (by rfl) ⟨246977, by rfl⟩ : syracuseStep 329303 = 493955) B493955
theorem B935513 : Blo 327838 935513 := bstep (se 2 (by rfl) ⟨350817, by rfl⟩ : syracuseStep 935513 = 701635) B701635
theorem B493145 : Blo 327838 493145 := bstep (se 2 (by rfl) ⟨184929, by rfl⟩ : syracuseStep 493145 = 369859) B369859
theorem B329323 : Blo 327838 329323 := bstep (se 1 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 329323 = 493985) B493985
theorem B329335 : Blo 327838 329335 := bstep (se 1 (by rfl) ⟨247001, by rfl⟩ : syracuseStep 329335 = 494003) B494003
theorem B329355 : Blo 327838 329355 := bstep (se 1 (by rfl) ⟨247016, by rfl⟩ : syracuseStep 329355 = 494033) B494033
theorem B370327 : Blo 327838 370327 := bstep (se 1 (by rfl) ⟨277745, by rfl⟩ : syracuseStep 370327 = 555491) B555491
theorem B329367 : Blo 327838 329367 := bstep (se 1 (by rfl) ⟨247025, by rfl⟩ : syracuseStep 329367 = 494051) B494051
theorem B329387 : Blo 327838 329387 := bstep (se 1 (by rfl) ⟨247040, by rfl⟩ : syracuseStep 329387 = 494081) B494081
theorem B329399 : Blo 327838 329399 := bstep (se 1 (by rfl) ⟨247049, by rfl⟩ : syracuseStep 329399 = 494099) B494099
theorem B493259 : Blo 327838 493259 := bstep (se 1 (by rfl) ⟨369944, by rfl⟩ : syracuseStep 493259 = 739889) B739889
theorem B329419 : Blo 327838 329419 := bstep (se 1 (by rfl) ⟨247064, by rfl⟩ : syracuseStep 329419 = 494129) B494129
theorem B493271 : Blo 327838 493271 := bstep (se 1 (by rfl) ⟨369953, by rfl⟩ : syracuseStep 493271 = 739907) B739907
theorem B624343 : Blo 327838 624343 := bstep (se 1 (by rfl) ⟨468257, by rfl⟩ : syracuseStep 624343 = 936515) B936515
theorem B329431 : Blo 327838 329431 := bstep (se 1 (by rfl) ⟨247073, by rfl⟩ : syracuseStep 329431 = 494147) B494147
theorem B329451 : Blo 327838 329451 := bstep (se 1 (by rfl) ⟨247088, by rfl⟩ : syracuseStep 329451 = 494177) B494177
theorem B329463 : Blo 327838 329463 := bstep (se 1 (by rfl) ⟨247097, by rfl⟩ : syracuseStep 329463 = 494195) B494195
theorem B329483 : Blo 327838 329483 := bstep (se 1 (by rfl) ⟨247112, by rfl⟩ : syracuseStep 329483 = 494225) B494225
theorem B329495 : Blo 327838 329495 := bstep (se 1 (by rfl) ⟨247121, by rfl⟩ : syracuseStep 329495 = 494243) B494243
theorem B526105 : Blo 327838 526105 := bstep (se 2 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 526105 = 394579) B394579
theorem B739097 : Blo 327838 739097 := bstep (se 2 (by rfl) ⟨277161, by rfl⟩ : syracuseStep 739097 = 554323) B554323
theorem B493337 : Blo 327838 493337 := bstep (se 2 (by rfl) ⟨185001, by rfl⟩ : syracuseStep 493337 = 370003) B370003
theorem B329515 : Blo 327838 329515 := bstep (se 1 (by rfl) ⟨247136, by rfl⟩ : syracuseStep 329515 = 494273) B494273
theorem B329527 : Blo 327838 329527 := bstep (se 1 (by rfl) ⟨247145, by rfl⟩ : syracuseStep 329527 = 494291) B494291
theorem B3745601 : Blo 327838 3745601 := bstep (se 2 (by rfl) ⟨1404600, by rfl⟩ : syracuseStep 3745601 = 2809201) B2809201
theorem B624449 : Blo 327838 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B370507 : Blo 327838 370507 := bstep (se 1 (by rfl) ⟨277880, by rfl⟩ : syracuseStep 370507 = 555761) B555761
theorem B329547 : Blo 327838 329547 := bstep (se 1 (by rfl) ⟨247160, by rfl⟩ : syracuseStep 329547 = 494321) B494321
theorem B329559 : Blo 327838 329559 := bstep (se 1 (by rfl) ⟨247169, by rfl⟩ : syracuseStep 329559 = 494339) B494339
theorem B2819933 : Blo 327838 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B329579 : Blo 327838 329579 := bstep (se 1 (by rfl) ⟨247184, by rfl⟩ : syracuseStep 329579 = 494369) B494369
theorem B739187 : Blo 327838 739187 := bstep (se 1 (by rfl) ⟨554390, by rfl⟩ : syracuseStep 739187 = 1108781) B1108781
theorem B329591 : Blo 327838 329591 := bstep (se 1 (by rfl) ⟨247193, by rfl⟩ : syracuseStep 329591 = 494387) B494387
theorem B493451 : Blo 327838 493451 := bstep (se 1 (by rfl) ⟨370088, by rfl⟩ : syracuseStep 493451 = 740177) B740177
theorem B329611 : Blo 327838 329611 := bstep (se 1 (by rfl) ⟨247208, by rfl⟩ : syracuseStep 329611 = 494417) B494417
theorem B1107863 : Blo 327838 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B739223 : Blo 327838 739223 := bstep (se 1 (by rfl) ⟨554417, by rfl⟩ : syracuseStep 739223 = 1108835) B1108835
theorem B493463 : Blo 327838 493463 := bstep (se 1 (by rfl) ⟨370097, by rfl⟩ : syracuseStep 493463 = 740195) B740195
theorem B329623 : Blo 327838 329623 := bstep (se 1 (by rfl) ⟨247217, by rfl⟩ : syracuseStep 329623 = 494435) B494435
theorem B329643 : Blo 327838 329643 := bstep (se 1 (by rfl) ⟨247232, by rfl⟩ : syracuseStep 329643 = 494465) B494465
theorem B370615 : Blo 327838 370615 := bstep (se 1 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 370615 = 555923) B555923
theorem B329655 : Blo 327838 329655 := bstep (se 1 (by rfl) ⟨247241, by rfl⟩ : syracuseStep 329655 = 494483) B494483
theorem B2172851 : Blo 327838 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B329675 : Blo 327838 329675 := bstep (se 1 (by rfl) ⟨247256, by rfl⟩ : syracuseStep 329675 = 494513) B494513
theorem B329687 : Blo 327838 329687 := bstep (se 1 (by rfl) ⟨247265, by rfl⟩ : syracuseStep 329687 = 494531) B494531
theorem B444377 : Blo 327838 444377 := bstep (se 2 (by rfl) ⟨166641, by rfl⟩ : syracuseStep 444377 = 333283) B333283
theorem B624601 : Blo 327838 624601 := bstep (se 2 (by rfl) ⟨234225, by rfl⟩ : syracuseStep 624601 = 468451) B468451
theorem B493529 : Blo 327838 493529 := bstep (se 2 (by rfl) ⟨185073, by rfl⟩ : syracuseStep 493529 = 370147) B370147
theorem B1247197 : Blo 327838 1247197 := bstep (se 3 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 1247197 = 467699) B467699
theorem B1116125 : Blo 327838 1116125 := bstep (se 3 (by rfl) ⟨209273, by rfl⟩ : syracuseStep 1116125 = 418547) B418547
theorem B329707 : Blo 327838 329707 := bstep (se 1 (by rfl) ⟨247280, by rfl⟩ : syracuseStep 329707 = 494561) B494561
theorem B329719 : Blo 327838 329719 := bstep (se 1 (by rfl) ⟨247289, by rfl⟩ : syracuseStep 329719 = 494579) B494579
theorem B395275 : Blo 327838 395275 := bstep (se 1 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 395275 = 592913) B592913
theorem B329739 : Blo 327838 329739 := bstep (se 1 (by rfl) ⟨247304, by rfl⟩ : syracuseStep 329739 = 494609) B494609
theorem B329751 : Blo 327838 329751 := bstep (se 1 (by rfl) ⟨247313, by rfl⟩ : syracuseStep 329751 = 494627) B494627
theorem B329771 : Blo 327838 329771 := bstep (se 1 (by rfl) ⟨247328, by rfl⟩ : syracuseStep 329771 = 494657) B494657
theorem B329783 : Blo 327838 329783 := bstep (se 1 (by rfl) ⟨247337, by rfl⟩ : syracuseStep 329783 = 494675) B494675
theorem B739403 : Blo 327838 739403 := bstep (se 1 (by rfl) ⟨554552, by rfl⟩ : syracuseStep 739403 = 1109105) B1109105
theorem B493643 : Blo 327838 493643 := bstep (se 1 (by rfl) ⟨370232, by rfl⟩ : syracuseStep 493643 = 740465) B740465
theorem B329803 : Blo 327838 329803 := bstep (se 1 (by rfl) ⟨247352, by rfl⟩ : syracuseStep 329803 = 494705) B494705
theorem B493655 : Blo 327838 493655 := bstep (se 1 (by rfl) ⟨370241, by rfl⟩ : syracuseStep 493655 = 740483) B740483
theorem B329815 : Blo 327838 329815 := bstep (se 1 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 329815 = 494723) B494723
theorem B370795 : Blo 327838 370795 := bstep (se 1 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 370795 = 556193) B556193
theorem B329835 : Blo 327838 329835 := bstep (se 1 (by rfl) ⟨247376, by rfl⟩ : syracuseStep 329835 = 494753) B494753
theorem B329847 : Blo 327838 329847 := bstep (se 1 (by rfl) ⟨247385, by rfl⟩ : syracuseStep 329847 = 494771) B494771
theorem B739457 : Blo 327838 739457 := bstep (se 2 (by rfl) ⟨277296, by rfl⟩ : syracuseStep 739457 = 554593) B554593
theorem B329867 : Blo 327838 329867 := bstep (se 1 (by rfl) ⟨247400, by rfl⟩ : syracuseStep 329867 = 494801) B494801
theorem B329879 : Blo 327838 329879 := bstep (se 1 (by rfl) ⟨247409, by rfl⟩ : syracuseStep 329879 = 494819) B494819
theorem B493721 : Blo 327838 493721 := bstep (se 2 (by rfl) ⟨185145, by rfl⟩ : syracuseStep 493721 = 370291) B370291
theorem B329899 : Blo 327838 329899 := bstep (se 1 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 329899 = 494849) B494849
theorem B329911 : Blo 327838 329911 := bstep (se 1 (by rfl) ⟨247433, by rfl⟩ : syracuseStep 329911 = 494867) B494867
theorem B1067201 : Blo 327838 1067201 := bstep (se 2 (by rfl) ⟨400200, by rfl⟩ : syracuseStep 1067201 = 800401) B800401
theorem B329931 : Blo 327838 329931 := bstep (se 1 (by rfl) ⟨247448, by rfl⟩ : syracuseStep 329931 = 494897) B494897
theorem B370903 : Blo 327838 370903 := bstep (se 1 (by rfl) ⟨278177, by rfl⟩ : syracuseStep 370903 = 556355) B556355
theorem B329943 : Blo 327838 329943 := bstep (se 1 (by rfl) ⟨247457, by rfl⟩ : syracuseStep 329943 = 494915) B494915
theorem B329963 : Blo 327838 329963 := bstep (se 1 (by rfl) ⟨247472, by rfl⟩ : syracuseStep 329963 = 494945) B494945
theorem B329975 : Blo 327838 329975 := bstep (se 1 (by rfl) ⟨247481, by rfl⟩ : syracuseStep 329975 = 494963) B494963
theorem B493835 : Blo 327838 493835 := bstep (se 1 (by rfl) ⟨370376, by rfl⟩ : syracuseStep 493835 = 740753) B740753
theorem B329995 : Blo 327838 329995 := bstep (se 1 (by rfl) ⟨247496, by rfl⟩ : syracuseStep 329995 = 494993) B494993
theorem B493847 : Blo 327838 493847 := bstep (se 1 (by rfl) ⟨370385, by rfl⟩ : syracuseStep 493847 = 740771) B740771
theorem B469271 : Blo 327838 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B330007 : Blo 327838 330007 := bstep (se 1 (by rfl) ⟨247505, by rfl⟩ : syracuseStep 330007 = 495011) B495011
theorem B330027 : Blo 327838 330027 := bstep (se 1 (by rfl) ⟨247520, by rfl⟩ : syracuseStep 330027 = 495041) B495041
theorem B330039 : Blo 327838 330039 := bstep (se 1 (by rfl) ⟨247529, by rfl⟩ : syracuseStep 330039 = 495059) B495059
theorem B330059 : Blo 327838 330059 := bstep (se 1 (by rfl) ⟨247544, by rfl⟩ : syracuseStep 330059 = 495089) B495089
theorem B330071 : Blo 327838 330071 := bstep (se 1 (by rfl) ⟨247553, by rfl⟩ : syracuseStep 330071 = 495107) B495107
theorem B739673 : Blo 327838 739673 := bstep (se 2 (by rfl) ⟨277377, by rfl⟩ : syracuseStep 739673 = 554755) B554755
theorem B493913 : Blo 327838 493913 := bstep (se 2 (by rfl) ⟨185217, by rfl⟩ : syracuseStep 493913 = 370435) B370435
theorem B330091 : Blo 327838 330091 := bstep (se 1 (by rfl) ⟨247568, by rfl⟩ : syracuseStep 330091 = 495137) B495137
theorem B330103 : Blo 327838 330103 := bstep (se 1 (by rfl) ⟨247577, by rfl⟩ : syracuseStep 330103 = 495155) B495155
theorem B371083 : Blo 327838 371083 := bstep (se 1 (by rfl) ⟨278312, by rfl⟩ : syracuseStep 371083 = 556625) B556625
theorem B330123 : Blo 327838 330123 := bstep (se 1 (by rfl) ⟨247592, by rfl⟩ : syracuseStep 330123 = 495185) B495185
theorem B330135 : Blo 327838 330135 := bstep (se 1 (by rfl) ⟨247601, by rfl⟩ : syracuseStep 330135 = 495203) B495203
theorem B330155 : Blo 327838 330155 := bstep (se 1 (by rfl) ⟨247616, by rfl⟩ : syracuseStep 330155 = 495233) B495233
theorem B1108403 : Blo 327838 1108403 := bstep (se 1 (by rfl) ⟨831302, by rfl⟩ : syracuseStep 1108403 = 1662605) B1662605
theorem B739763 : Blo 327838 739763 := bstep (se 1 (by rfl) ⟨554822, by rfl⟩ : syracuseStep 739763 = 1109645) B1109645
theorem B330167 : Blo 327838 330167 := bstep (se 1 (by rfl) ⟨247625, by rfl⟩ : syracuseStep 330167 = 495251) B495251
theorem B494027 : Blo 327838 494027 := bstep (se 1 (by rfl) ⟨370520, by rfl⟩ : syracuseStep 494027 = 741041) B741041
theorem B330187 : Blo 327838 330187 := bstep (se 1 (by rfl) ⟨247640, by rfl⟩ : syracuseStep 330187 = 495281) B495281
theorem B739799 : Blo 327838 739799 := bstep (se 1 (by rfl) ⟨554849, by rfl⟩ : syracuseStep 739799 = 1109699) B1109699
theorem B494039 : Blo 327838 494039 := bstep (se 1 (by rfl) ⟨370529, by rfl⟩ : syracuseStep 494039 = 741059) B741059
theorem B330199 : Blo 327838 330199 := bstep (se 1 (by rfl) ⟨247649, by rfl⟩ : syracuseStep 330199 = 495299) B495299
theorem B330219 : Blo 327838 330219 := bstep (se 1 (by rfl) ⟨247664, by rfl⟩ : syracuseStep 330219 = 495329) B495329
theorem B371191 : Blo 327838 371191 := bstep (se 1 (by rfl) ⟨278393, by rfl⟩ : syracuseStep 371191 = 556787) B556787
theorem B330231 : Blo 327838 330231 := bstep (se 1 (by rfl) ⟨247673, by rfl⟩ : syracuseStep 330231 = 495347) B495347
theorem B330251 : Blo 327838 330251 := bstep (se 1 (by rfl) ⟨247688, by rfl⟩ : syracuseStep 330251 = 495377) B495377
theorem B330263 : Blo 327838 330263 := bstep (se 1 (by rfl) ⟨247697, by rfl⟩ : syracuseStep 330263 = 495395) B495395
theorem B1411607 : Blo 327838 1411607 := bstep (se 1 (by rfl) ⟨1058705, by rfl⟩ : syracuseStep 1411607 = 2117411) B2117411
theorem B494105 : Blo 327838 494105 := bstep (se 2 (by rfl) ⟨185289, by rfl⟩ : syracuseStep 494105 = 370579) B370579
theorem B330283 : Blo 327838 330283 := bstep (se 1 (by rfl) ⟨247712, by rfl⟩ : syracuseStep 330283 = 495425) B495425
theorem B3041837 : Blo 327838 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B330295 : Blo 327838 330295 := bstep (se 1 (by rfl) ⟨247721, by rfl⟩ : syracuseStep 330295 = 495443) B495443
theorem B830027 : Blo 327838 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B2255435 : Blo 327838 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B469579 : Blo 327838 469579 := bstep (se 1 (by rfl) ⟨352184, by rfl⟩ : syracuseStep 469579 = 704369) B704369
theorem B2820683 : Blo 327838 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B330315 : Blo 327838 330315 := bstep (se 1 (by rfl) ⟨247736, by rfl⟩ : syracuseStep 330315 = 495473) B495473
theorem B330327 : Blo 327838 330327 := bstep (se 1 (by rfl) ⟨247745, by rfl⟩ : syracuseStep 330327 = 495491) B495491
theorem B330347 : Blo 327838 330347 := bstep (se 1 (by rfl) ⟨247760, by rfl⟩ : syracuseStep 330347 = 495521) B495521
theorem B330359 : Blo 327838 330359 := bstep (se 1 (by rfl) ⟨247769, by rfl⟩ : syracuseStep 330359 = 495539) B495539
theorem B739979 : Blo 327838 739979 := bstep (se 1 (by rfl) ⟨554984, by rfl⟩ : syracuseStep 739979 = 1109969) B1109969
theorem B494219 : Blo 327838 494219 := bstep (se 1 (by rfl) ⟨370664, by rfl⟩ : syracuseStep 494219 = 741329) B741329
theorem B330379 : Blo 327838 330379 := bstep (se 1 (by rfl) ⟨247784, by rfl⟩ : syracuseStep 330379 = 495569) B495569
theorem B494231 : Blo 327838 494231 := bstep (se 1 (by rfl) ⟨370673, by rfl⟩ : syracuseStep 494231 = 741347) B741347
theorem B330391 : Blo 327838 330391 := bstep (se 1 (by rfl) ⟨247793, by rfl⟩ : syracuseStep 330391 = 495587) B495587
theorem B371371 : Blo 327838 371371 := bstep (se 1 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 371371 = 557057) B557057
theorem B330411 : Blo 327838 330411 := bstep (se 1 (by rfl) ⟨247808, by rfl⟩ : syracuseStep 330411 = 495617) B495617
theorem B330423 : Blo 327838 330423 := bstep (se 1 (by rfl) ⟨247817, by rfl⟩ : syracuseStep 330423 = 495635) B495635
theorem B1108673 : Blo 327838 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B740033 : Blo 327838 740033 := bstep (se 2 (by rfl) ⟨277512, by rfl⟩ : syracuseStep 740033 = 555025) B555025
theorem B330443 : Blo 327838 330443 := bstep (se 1 (by rfl) ⟨247832, by rfl⟩ : syracuseStep 330443 = 495665) B495665
theorem B330455 : Blo 327838 330455 := bstep (se 1 (by rfl) ⟨247841, by rfl⟩ : syracuseStep 330455 = 495683) B495683
theorem B494297 : Blo 327838 494297 := bstep (se 2 (by rfl) ⟨185361, by rfl⟩ : syracuseStep 494297 = 370723) B370723
theorem B1673945 : Blo 327838 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B330475 : Blo 327838 330475 := bstep (se 1 (by rfl) ⟨247856, by rfl⟩ : syracuseStep 330475 = 495713) B495713
theorem B330487 : Blo 327838 330487 := bstep (se 1 (by rfl) ⟨247865, by rfl⟩ : syracuseStep 330487 = 495731) B495731
theorem B330507 : Blo 327838 330507 := bstep (se 1 (by rfl) ⟨247880, by rfl⟩ : syracuseStep 330507 = 495761) B495761
theorem B371479 : Blo 327838 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B330519 : Blo 327838 330519 := bstep (se 1 (by rfl) ⟨247889, by rfl⟩ : syracuseStep 330519 = 495779) B495779
theorem B330539 : Blo 327838 330539 := bstep (se 1 (by rfl) ⟨247904, by rfl⟩ : syracuseStep 330539 = 495809) B495809
theorem B936755 : Blo 327838 936755 := bstep (se 1 (by rfl) ⟨702566, by rfl⟩ : syracuseStep 936755 = 1405133) B1405133
theorem B330551 : Blo 327838 330551 := bstep (se 1 (by rfl) ⟨247913, by rfl⟩ : syracuseStep 330551 = 495827) B495827
theorem B2501441 : Blo 327838 2501441 := bstep (se 2 (by rfl) ⟨938040, by rfl⟩ : syracuseStep 2501441 = 1876081) B1876081
theorem B494411 : Blo 327838 494411 := bstep (se 1 (by rfl) ⟨370808, by rfl⟩ : syracuseStep 494411 = 741617) B741617
theorem B330571 : Blo 327838 330571 := bstep (se 1 (by rfl) ⟨247928, by rfl⟩ : syracuseStep 330571 = 495857) B495857
theorem B494423 : Blo 327838 494423 := bstep (se 1 (by rfl) ⟨370817, by rfl⟩ : syracuseStep 494423 = 741635) B741635
theorem B330583 : Blo 327838 330583 := bstep (se 1 (by rfl) ⟨247937, by rfl⟩ : syracuseStep 330583 = 495875) B495875
theorem B1772381 : Blo 327838 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B330603 : Blo 327838 330603 := bstep (se 1 (by rfl) ⟨247952, by rfl⟩ : syracuseStep 330603 = 495905) B495905
theorem B330615 : Blo 327838 330615 := bstep (se 1 (by rfl) ⟨247961, by rfl⟩ : syracuseStep 330615 = 495923) B495923
theorem B1182595 : Blo 327838 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B502667 : Blo 327838 502667 := bstep (se 1 (by rfl) ⟨377000, by rfl⟩ : syracuseStep 502667 = 754001) B754001
theorem B330635 : Blo 327838 330635 := bstep (se 1 (by rfl) ⟨247976, by rfl⟩ : syracuseStep 330635 = 495953) B495953
theorem B330647 : Blo 327838 330647 := bstep (se 1 (by rfl) ⟨247985, by rfl⟩ : syracuseStep 330647 = 495971) B495971
theorem B740249 : Blo 327838 740249 := bstep (se 2 (by rfl) ⟨277593, by rfl⟩ : syracuseStep 740249 = 555187) B555187
theorem B494489 : Blo 327838 494489 := bstep (se 2 (by rfl) ⟨185433, by rfl⟩ : syracuseStep 494489 = 370867) B370867
theorem B330667 : Blo 327838 330667 := bstep (se 1 (by rfl) ⟨248000, by rfl⟩ : syracuseStep 330667 = 496001) B496001
theorem B330679 : Blo 327838 330679 := bstep (se 1 (by rfl) ⟨248009, by rfl⟩ : syracuseStep 330679 = 496019) B496019
theorem B371659 : Blo 327838 371659 := bstep (se 1 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 371659 = 557489) B557489
theorem B330699 : Blo 327838 330699 := bstep (se 1 (by rfl) ⟨248024, by rfl⟩ : syracuseStep 330699 = 496049) B496049
theorem B3550169 : Blo 327838 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B330711 : Blo 327838 330711 := bstep (se 1 (by rfl) ⟨248033, by rfl⟩ : syracuseStep 330711 = 496067) B496067
theorem B330731 : Blo 327838 330731 := bstep (se 1 (by rfl) ⟨248048, by rfl⟩ : syracuseStep 330731 = 496097) B496097
theorem B740339 : Blo 327838 740339 := bstep (se 1 (by rfl) ⟨555254, by rfl⟩ : syracuseStep 740339 = 1110509) B1110509
theorem B330743 : Blo 327838 330743 := bstep (se 1 (by rfl) ⟨248057, by rfl⟩ : syracuseStep 330743 = 496115) B496115
theorem B494603 : Blo 327838 494603 := bstep (se 1 (by rfl) ⟨370952, by rfl⟩ : syracuseStep 494603 = 741905) B741905
theorem B740375 : Blo 327838 740375 := bstep (se 1 (by rfl) ⟨555281, by rfl⟩ : syracuseStep 740375 = 1110563) B1110563
theorem B494615 : Blo 327838 494615 := bstep (se 1 (by rfl) ⟨370961, by rfl⟩ : syracuseStep 494615 = 741923) B741923
theorem B371767 : Blo 327838 371767 := bstep (se 1 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 371767 = 557651) B557651
theorem B535627 : Blo 327838 535627 := bstep (se 1 (by rfl) ⟨401720, by rfl⟩ : syracuseStep 535627 = 803441) B803441
theorem B592985 : Blo 327838 592985 := bstep (se 2 (by rfl) ⟨222369, by rfl⟩ : syracuseStep 592985 = 444739) B444739
theorem B494681 : Blo 327838 494681 := bstep (se 2 (by rfl) ⟨185505, by rfl⟩ : syracuseStep 494681 = 371011) B371011
theorem B1502401 : Blo 327838 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B740555 : Blo 327838 740555 := bstep (se 1 (by rfl) ⟨555416, by rfl⟩ : syracuseStep 740555 = 1110833) B1110833
theorem B494795 : Blo 327838 494795 := bstep (se 1 (by rfl) ⟨371096, by rfl⟩ : syracuseStep 494795 = 742193) B742193
theorem B3214541 : Blo 327838 3214541 := bstep (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) B1205453
theorem B494807 : Blo 327838 494807 := bstep (se 1 (by rfl) ⟨371105, by rfl⟩ : syracuseStep 494807 = 742211) B742211
theorem B1248473 : Blo 327838 1248473 := bstep (se 2 (by rfl) ⟨468177, by rfl⟩ : syracuseStep 1248473 = 936355) B936355
theorem B1109213 : Blo 327838 1109213 := bstep (se 3 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 1109213 = 415955) B415955
theorem B371947 : Blo 327838 371947 := bstep (se 1 (by rfl) ⟨278960, by rfl⟩ : syracuseStep 371947 = 557921) B557921
theorem B625907 : Blo 327838 625907 := bstep (se 1 (by rfl) ⟨469430, by rfl⟩ : syracuseStep 625907 = 938861) B938861
theorem B740609 : Blo 327838 740609 := bstep (se 2 (by rfl) ⟨277728, by rfl⟩ : syracuseStep 740609 = 555457) B555457
theorem B494873 : Blo 327838 494873 := bstep (se 2 (by rfl) ⟨185577, by rfl⟩ : syracuseStep 494873 = 371155) B371155
theorem B2108747 : Blo 327838 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B372055 : Blo 327838 372055 := bstep (se 1 (by rfl) ⟨279041, by rfl⟩ : syracuseStep 372055 = 558083) B558083
theorem B642419 : Blo 327838 642419 := bstep (se 1 (by rfl) ⟨481814, by rfl⟩ : syracuseStep 642419 = 963629) B963629
theorem B626059 : Blo 327838 626059 := bstep (se 1 (by rfl) ⟨469544, by rfl⟩ : syracuseStep 626059 = 939089) B939089
theorem B494987 : Blo 327838 494987 := bstep (se 1 (by rfl) ⟨371240, by rfl⟩ : syracuseStep 494987 = 742481) B742481
theorem B494999 : Blo 327838 494999 := bstep (se 1 (by rfl) ⟨371249, by rfl⟩ : syracuseStep 494999 = 742499) B742499
theorem B1191361 : Blo 327838 1191361 := bstep (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) B893521
theorem B740825 : Blo 327838 740825 := bstep (se 2 (by rfl) ⟨277809, by rfl⟩ : syracuseStep 740825 = 555619) B555619
theorem B495065 : Blo 327838 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B830999 : Blo 327838 830999 := bstep (se 1 (by rfl) ⟨623249, by rfl⟩ : syracuseStep 830999 = 1246499) B1246499
theorem B650803 : Blo 327838 650803 := bstep (se 1 (by rfl) ⟨488102, by rfl⟩ : syracuseStep 650803 = 976205) B976205
theorem B740915 : Blo 327838 740915 := bstep (se 1 (by rfl) ⟨555686, by rfl⟩ : syracuseStep 740915 = 1111373) B1111373
theorem B495179 : Blo 327838 495179 := bstep (se 1 (by rfl) ⟨371384, by rfl⟩ : syracuseStep 495179 = 742769) B742769
theorem B740951 : Blo 327838 740951 := bstep (se 1 (by rfl) ⟨555713, by rfl⟩ : syracuseStep 740951 = 1111427) B1111427
theorem B495191 : Blo 327838 495191 := bstep (se 1 (by rfl) ⟨371393, by rfl⟩ : syracuseStep 495191 = 742787) B742787
theorem B470615 : Blo 327838 470615 := bstep (se 1 (by rfl) ⟨352961, by rfl⟩ : syracuseStep 470615 = 705923) B705923
theorem B1601117 : Blo 327838 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B1584791 : Blo 327838 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B495257 : Blo 327838 495257 := bstep (se 2 (by rfl) ⟨185721, by rfl⟩ : syracuseStep 495257 = 371443) B371443
theorem B13758149 : Blo 327838 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B626393 : Blo 327838 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B741131 : Blo 327838 741131 := bstep (se 1 (by rfl) ⟨555848, by rfl⟩ : syracuseStep 741131 = 1111697) B1111697
theorem B495371 : Blo 327838 495371 := bstep (se 1 (by rfl) ⟨371528, by rfl⟩ : syracuseStep 495371 = 743057) B743057
theorem B495383 : Blo 327838 495383 := bstep (se 1 (by rfl) ⟨371537, by rfl⟩ : syracuseStep 495383 = 743075) B743075
theorem B470809 : Blo 327838 470809 := bstep (se 2 (by rfl) ⟨176553, by rfl⟩ : syracuseStep 470809 = 353107) B353107
theorem B741185 : Blo 327838 741185 := bstep (se 2 (by rfl) ⟨277944, by rfl⟩ : syracuseStep 741185 = 555889) B555889
theorem B634711 : Blo 327838 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B495449 : Blo 327838 495449 := bstep (se 2 (by rfl) ⟨185793, by rfl⟩ : syracuseStep 495449 = 371587) B371587
theorem B1183691 : Blo 327838 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B495563 : Blo 327838 495563 := bstep (se 1 (by rfl) ⟨371672, by rfl⟩ : syracuseStep 495563 = 743345) B743345
theorem B495575 : Blo 327838 495575 := bstep (se 1 (by rfl) ⟨371681, by rfl⟩ : syracuseStep 495575 = 743363) B743363
theorem B741401 : Blo 327838 741401 := bstep (se 2 (by rfl) ⟨278025, by rfl⟩ : syracuseStep 741401 = 556051) B556051
theorem B495641 : Blo 327838 495641 := bstep (se 2 (by rfl) ⟨185865, by rfl⟩ : syracuseStep 495641 = 371731) B371731
theorem B4739147 : Blo 327838 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B741491 : Blo 327838 741491 := bstep (se 1 (by rfl) ⟨556118, by rfl⟩ : syracuseStep 741491 = 1112237) B1112237
theorem B495755 : Blo 327838 495755 := bstep (se 1 (by rfl) ⟨371816, by rfl⟩ : syracuseStep 495755 = 743633) B743633
theorem B1216657 : Blo 327838 1216657 := bstep (se 2 (by rfl) ⟨456246, by rfl⟩ : syracuseStep 1216657 = 912493) B912493
theorem B741527 : Blo 327838 741527 := bstep (se 1 (by rfl) ⟨556145, by rfl⟩ : syracuseStep 741527 = 1112291) B1112291
theorem B495767 : Blo 327838 495767 := bstep (se 1 (by rfl) ⟨371825, by rfl⟩ : syracuseStep 495767 = 743651) B743651
theorem B831667 : Blo 327838 831667 := bstep (se 1 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 831667 = 1247501) B1247501
theorem B2822323 : Blo 327838 2822323 := bstep (se 1 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 2822323 = 4233485) B4233485
theorem B764491 : Blo 327838 764491 := bstep (se 1 (by rfl) ⟨573368, by rfl⟩ : syracuseStep 764491 = 1146737) B1146737
theorem B6025421 : Blo 327838 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B495833 : Blo 327838 495833 := bstep (se 2 (by rfl) ⟨185937, by rfl⟩ : syracuseStep 495833 = 371875) B371875
theorem B831809 : Blo 327838 831809 := bstep (se 2 (by rfl) ⟨311928, by rfl⟩ : syracuseStep 831809 = 623857) B623857
theorem B1110347 : Blo 327838 1110347 := bstep (se 1 (by rfl) ⟨832760, by rfl⟩ : syracuseStep 1110347 = 1665521) B1665521
theorem B741707 : Blo 327838 741707 := bstep (se 1 (by rfl) ⟨556280, by rfl⟩ : syracuseStep 741707 = 1112561) B1112561
theorem B495947 : Blo 327838 495947 := bstep (se 1 (by rfl) ⟨371960, by rfl⟩ : syracuseStep 495947 = 743921) B743921
theorem B627031 : Blo 327838 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B495959 : Blo 327838 495959 := bstep (se 1 (by rfl) ⟨371969, by rfl⟩ : syracuseStep 495959 = 743939) B743939
theorem B2011493 : Blo 327838 2011493 := bstep (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) B377155
theorem B741761 : Blo 327838 741761 := bstep (se 2 (by rfl) ⟨278160, by rfl⟩ : syracuseStep 741761 = 556321) B556321
theorem B496025 : Blo 327838 496025 := bstep (se 2 (by rfl) ⟨186009, by rfl⟩ : syracuseStep 496025 = 372019) B372019
theorem B668083 : Blo 327838 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B422411 : Blo 327838 422411 := bstep (se 1 (by rfl) ⟨316808, by rfl⟩ : syracuseStep 422411 = 633617) B633617
theorem B502411 : Blo 327838 502411 := bstep (se 1 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 502411 = 753617) B753617
theorem B1405457 : Blo 327838 1405457 := bstep (se 2 (by rfl) ⟨527046, by rfl⟩ : syracuseStep 1405457 = 1054093) B1054093
theorem B553547 : Blo 327838 553547 := bstep (se 1 (by rfl) ⟨415160, by rfl⟩ : syracuseStep 553547 = 830321) B830321
theorem B1110617 : Blo 327838 1110617 := bstep (se 2 (by rfl) ⟨416481, by rfl⟩ : syracuseStep 1110617 = 832963) B832963
theorem B741977 : Blo 327838 741977 := bstep (se 2 (by rfl) ⟨278241, by rfl⟩ : syracuseStep 741977 = 556483) B556483
theorem B1684061 : Blo 327838 1684061 := bstep (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) B631523
theorem B332407 : Blo 327838 332407 := bstep (se 1 (by rfl) ⟨249305, by rfl⟩ : syracuseStep 332407 = 498611) B498611
theorem B1495703 : Blo 327838 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B750259 : Blo 327838 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B742067 : Blo 327838 742067 := bstep (se 1 (by rfl) ⟨556550, by rfl⟩ : syracuseStep 742067 = 1113101) B1113101
theorem B553675 : Blo 327838 553675 := bstep (se 1 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 553675 = 830513) B830513
theorem B701131 : Blo 327838 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B742103 : Blo 327838 742103 := bstep (se 1 (by rfl) ⟨556577, by rfl⟩ : syracuseStep 742103 = 1113155) B1113155
theorem B2503385 : Blo 327838 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B3994373 : Blo 327838 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B1184557 : Blo 327838 1184557 := bstep (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) B444209
theorem B1250099 : Blo 327838 1250099 := bstep (se 1 (by rfl) ⟨937574, by rfl⟩ : syracuseStep 1250099 = 1875149) B1875149
theorem B2503489 : Blo 327838 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B1250113 : Blo 327838 1250113 := bstep (se 2 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 1250113 = 937585) B937585
theorem B553817 : Blo 327838 553817 := bstep (se 2 (by rfl) ⟨207681, by rfl⟩ : syracuseStep 553817 = 415363) B415363
theorem B742283 : Blo 327838 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B2110387 : Blo 327838 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B742337 : Blo 327838 742337 := bstep (se 2 (by rfl) ⟨278376, by rfl⟩ : syracuseStep 742337 = 556753) B556753
theorem B750551 : Blo 327838 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B553945 : Blo 327838 553945 := bstep (se 2 (by rfl) ⟨207729, by rfl⟩ : syracuseStep 553945 = 415459) B415459
theorem B594931 : Blo 327838 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B1668113 : Blo 327838 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B595019 : Blo 327838 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B1053785 : Blo 327838 1053785 := bstep (se 2 (by rfl) ⟨395169, by rfl⟩ : syracuseStep 1053785 = 790339) B790339
theorem B5624963 : Blo 327838 5624963 := bstep (se 1 (by rfl) ⟨4218722, by rfl⟩ : syracuseStep 5624963 = 8437445) B8437445
theorem B627851 : Blo 327838 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B742553 : Blo 327838 742553 := bstep (se 2 (by rfl) ⟨278457, by rfl⟩ : syracuseStep 742553 = 556915) B556915
theorem B1668275 : Blo 327838 1668275 := bstep (se 1 (by rfl) ⟨1251206, by rfl⟩ : syracuseStep 1668275 = 2502413) B2502413
theorem B627905 : Blo 327838 627905 := bstep (se 2 (by rfl) ⟨235464, by rfl⟩ : syracuseStep 627905 = 470929) B470929
theorem B1406173 : Blo 327838 1406173 := bstep (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) B527315
theorem B742643 : Blo 327838 742643 := bstep (se 1 (by rfl) ⟨556982, by rfl⟩ : syracuseStep 742643 = 1113965) B1113965
theorem B1266961 : Blo 327838 1266961 := bstep (se 2 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 1266961 = 950221) B950221
theorem B1185047 : Blo 327838 1185047 := bstep (se 1 (by rfl) ⟨888785, by rfl⟩ : syracuseStep 1185047 = 1777571) B1777571
theorem B1111319 : Blo 327838 1111319 := bstep (se 1 (by rfl) ⟨833489, by rfl⟩ : syracuseStep 1111319 = 1666979) B1666979
theorem B742679 : Blo 327838 742679 := bstep (se 1 (by rfl) ⟨557009, by rfl⟩ : syracuseStep 742679 = 1114019) B1114019
theorem B792011 : Blo 327838 792011 := bstep (se 1 (by rfl) ⟨594008, by rfl⟩ : syracuseStep 792011 = 1188017) B1188017
theorem B742859 : Blo 327838 742859 := bstep (se 1 (by rfl) ⟨557144, by rfl⟩ : syracuseStep 742859 = 1114289) B1114289
theorem B742913 : Blo 327838 742913 := bstep (se 2 (by rfl) ⟨278592, by rfl⟩ : syracuseStep 742913 = 557185) B557185
theorem B554519 : Blo 327838 554519 := bstep (se 1 (by rfl) ⟨415889, by rfl⟩ : syracuseStep 554519 = 831779) B831779
theorem B833075 : Blo 327838 833075 := bstep (se 1 (by rfl) ⟨624806, by rfl⟩ : syracuseStep 833075 = 1249613) B1249613
theorem B415307 : Blo 327838 415307 := bstep (se 1 (by rfl) ⟨311480, by rfl⟩ : syracuseStep 415307 = 622961) B622961
theorem B939613 : Blo 327838 939613 := bstep (se 3 (by rfl) ⟨176177, by rfl⟩ : syracuseStep 939613 = 352355) B352355
theorem B1881731 : Blo 327838 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B554647 : Blo 327838 554647 := bstep (se 1 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 554647 = 831971) B831971
theorem B939671 : Blo 327838 939671 := bstep (se 1 (by rfl) ⟨704753, by rfl⟩ : syracuseStep 939671 = 1409507) B1409507
theorem B743129 : Blo 327838 743129 := bstep (se 2 (by rfl) ⟨278673, by rfl⟩ : syracuseStep 743129 = 557347) B557347
theorem B669427 : Blo 327838 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B2406179 : Blo 327838 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B1111859 : Blo 327838 1111859 := bstep (se 1 (by rfl) ⟨833894, by rfl⟩ : syracuseStep 1111859 = 1667789) B1667789
theorem B743219 : Blo 327838 743219 := bstep (se 1 (by rfl) ⟨557414, by rfl⟩ : syracuseStep 743219 = 1114829) B1114829
theorem B1054529 : Blo 327838 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B743255 : Blo 327838 743255 := bstep (se 1 (by rfl) ⟨557441, by rfl⟩ : syracuseStep 743255 = 1114883) B1114883
theorem B1660823 : Blo 327838 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B702361 : Blo 327838 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B743435 : Blo 327838 743435 := bstep (se 1 (by rfl) ⟨557576, by rfl⟩ : syracuseStep 743435 = 1115153) B1115153
theorem B997427 : Blo 327838 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B1112129 : Blo 327838 1112129 := bstep (se 2 (by rfl) ⟨417048, by rfl⟩ : syracuseStep 1112129 = 834097) B834097
theorem B743489 : Blo 327838 743489 := bstep (se 2 (by rfl) ⟨278808, by rfl⟩ : syracuseStep 743489 = 557617) B557617
theorem B833611 : Blo 327838 833611 := bstep (se 1 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 833611 = 1250417) B1250417
theorem B1882187 : Blo 327838 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B1189849 : Blo 327838 1189849 := bstep (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) B892387
theorem B833753 : Blo 327838 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B416011 : Blo 327838 416011 := bstep (se 1 (by rfl) ⟨312008, by rfl⟩ : syracuseStep 416011 = 624017) B624017
theorem B555275 : Blo 327838 555275 := bstep (se 1 (by rfl) ⟨416456, by rfl⟩ : syracuseStep 555275 = 832913) B832913
theorem B1046807 : Blo 327838 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B743705 : Blo 327838 743705 := bstep (se 2 (by rfl) ⟨278889, by rfl⟩ : syracuseStep 743705 = 557779) B557779
theorem B743795 : Blo 327838 743795 := bstep (se 1 (by rfl) ⟨557846, by rfl⟩ : syracuseStep 743795 = 1115693) B1115693
theorem B555403 : Blo 327838 555403 := bstep (se 1 (by rfl) ⟨416552, by rfl⟩ : syracuseStep 555403 = 833105) B833105
theorem B743831 : Blo 327838 743831 := bstep (se 1 (by rfl) ⟨557873, by rfl⟩ : syracuseStep 743831 = 1115747) B1115747
theorem B7608845 : Blo 327838 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B416279 : Blo 327838 416279 := bstep (se 1 (by rfl) ⟨312209, by rfl⟩ : syracuseStep 416279 = 624419) B624419
theorem B555545 : Blo 327838 555545 := bstep (se 2 (by rfl) ⟨208329, by rfl⟩ : syracuseStep 555545 = 416659) B416659
theorem B744011 : Blo 327838 744011 := bstep (se 1 (by rfl) ⟨558008, by rfl⟩ : syracuseStep 744011 = 1116017) B1116017
theorem B4209245 : Blo 327838 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B1112669 : Blo 327838 1112669 := bstep (se 3 (by rfl) ⟨208625, by rfl⟩ : syracuseStep 1112669 = 417251) B417251
theorem B350839 : Blo 327838 350839 := bstep (se 1 (by rfl) ⟨263129, by rfl⟩ : syracuseStep 350839 = 526259) B526259
theorem B4201091 : Blo 327838 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B3594883 : Blo 327838 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B3758723 : Blo 327838 3758723 := bstep (se 1 (by rfl) ⟨2819042, by rfl⟩ : syracuseStep 3758723 = 5638085) B5638085
theorem B744065 : Blo 327838 744065 := bstep (se 2 (by rfl) ⟨279024, by rfl⟩ : syracuseStep 744065 = 558049) B558049
theorem B752267 : Blo 327838 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B555673 : Blo 327838 555673 := bstep (se 2 (by rfl) ⟨208377, by rfl⟩ : syracuseStep 555673 = 416755) B416755
theorem B1055425 : Blo 327838 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B1252043 : Blo 327838 1252043 := bstep (se 1 (by rfl) ⟨939032, by rfl⟩ : syracuseStep 1252043 = 1878065) B1878065
theorem B1252057 : Blo 327838 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B752395 : Blo 327838 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B793433 : Blo 327838 793433 := bstep (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) B595075
theorem B940889 : Blo 327838 940889 := bstep (se 2 (by rfl) ⟨352833, by rfl⟩ : syracuseStep 940889 = 705667) B705667
theorem B1538909 : Blo 327838 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B6970211 : Blo 327838 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B375659 : Blo 327838 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B1506251 : Blo 327838 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B941003 : Blo 327838 941003 := bstep (se 1 (by rfl) ⟨705752, by rfl⟩ : syracuseStep 941003 = 1411505) B1411505
theorem B2497553 : Blo 327838 2497553 := bstep (se 2 (by rfl) ⟨936582, by rfl⟩ : syracuseStep 2497553 = 1873165) B1873165
theorem B834583 : Blo 327838 834583 := bstep (se 1 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 834583 = 1251875) B1251875
theorem B1670219 : Blo 327838 1670219 := bstep (se 1 (by rfl) ⟨1252664, by rfl⟩ : syracuseStep 1670219 = 2505329) B2505329
theorem B3054685 : Blo 327838 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B416983 : Blo 327838 416983 := bstep (se 1 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 416983 = 625475) B625475
theorem B556247 : Blo 327838 556247 := bstep (se 1 (by rfl) ⟨417185, by rfl⟩ : syracuseStep 556247 = 834371) B834371
theorem B1350877 : Blo 327838 1350877 := bstep (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) B506579
theorem B556375 : Blo 327838 556375 := bstep (se 1 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 556375 = 834563) B834563
theorem B351659 : Blo 327838 351659 := bstep (se 1 (by rfl) ⟨263744, by rfl⟩ : syracuseStep 351659 = 527489) B527489
theorem B2489777 : Blo 327838 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B835019 : Blo 327838 835019 := bstep (se 1 (by rfl) ⟨626264, by rfl⟩ : syracuseStep 835019 = 1252529) B1252529
theorem B2539025 : Blo 327838 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B2809475 : Blo 327838 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B1498769 : Blo 327838 1498769 := bstep (se 2 (by rfl) ⟨562038, by rfl⟩ : syracuseStep 1498769 = 1124077) B1124077
theorem B1253015 : Blo 327838 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B1113803 : Blo 327838 1113803 := bstep (se 1 (by rfl) ⟨835352, by rfl⟩ : syracuseStep 1113803 = 1670705) B1670705
theorem B1998553 : Blo 327838 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B835393 : Blo 327838 835393 := bstep (se 2 (by rfl) ⟨313272, by rfl⟩ : syracuseStep 835393 = 626545) B626545
theorem B4235125 : Blo 327838 4235125 := bstep (se 5 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 4235125 = 397043) B397043
theorem B622475 : Blo 327838 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B2490263 : Blo 327838 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B3563443 : Blo 327838 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B557003 : Blo 327838 557003 := bstep (se 1 (by rfl) ⟨417752, by rfl⟩ : syracuseStep 557003 = 835505) B835505
theorem B1114073 : Blo 327838 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B1671191 : Blo 327838 1671191 := bstep (se 1 (by rfl) ⟨1253393, by rfl⟩ : syracuseStep 1671191 = 2506787) B2506787
theorem B704659 : Blo 327838 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B327867 : Blo 327838 327867 := bstep (se 1 (by rfl) ⟨245900, by rfl⟩ : syracuseStep 327867 = 491801) B491801
theorem B1622209 : Blo 327838 1622209 := bstep (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) B1216657
theorem B491783 : Blo 327838 491783 := bstep (se 1 (by rfl) ⟨368837, by rfl⟩ : syracuseStep 491783 = 737675) B737675
theorem B327943 : Blo 327838 327943 := bstep (se 1 (by rfl) ⟨245957, by rfl⟩ : syracuseStep 327943 = 491915) B491915
theorem B327951 : Blo 327838 327951 := bstep (se 1 (by rfl) ⟨245963, by rfl⟩ : syracuseStep 327951 = 491927) B491927
theorem B557327 : Blo 327838 557327 := bstep (se 1 (by rfl) ⟨417995, by rfl⟩ : syracuseStep 557327 = 835991) B835991
theorem B491819 : Blo 327838 491819 := bstep (se 1 (by rfl) ⟨368864, by rfl⟩ : syracuseStep 491819 = 737729) B737729
theorem B327995 : Blo 327838 327995 := bstep (se 1 (by rfl) ⟨245996, by rfl⟩ : syracuseStep 327995 = 491993) B491993
theorem B491849 : Blo 327838 491849 := bstep (se 2 (by rfl) ⟨184443, by rfl⟩ : syracuseStep 491849 = 368887) B368887
theorem B369031 : Blo 327838 369031 := bstep (se 1 (by rfl) ⟨276773, by rfl⟩ : syracuseStep 369031 = 553547) B553547
theorem B328071 : Blo 327838 328071 := bstep (se 1 (by rfl) ⟨246053, by rfl⟩ : syracuseStep 328071 = 492107) B492107
theorem B328079 : Blo 327838 328079 := bstep (se 1 (by rfl) ⟨246059, by rfl⟩ : syracuseStep 328079 = 492119) B492119
theorem B1122707 : Blo 327838 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B2474387 : Blo 327838 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B491963 : Blo 327838 491963 := bstep (se 1 (by rfl) ⟨368972, by rfl⟩ : syracuseStep 491963 = 737945) B737945
theorem B328123 : Blo 327838 328123 := bstep (se 1 (by rfl) ⟨246092, by rfl⟩ : syracuseStep 328123 = 492185) B492185
theorem B836041 : Blo 327838 836041 := bstep (se 2 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 836041 = 627031) B627031
theorem B492023 : Blo 327838 492023 := bstep (se 1 (by rfl) ⟨369017, by rfl⟩ : syracuseStep 492023 = 738035) B738035
theorem B1868291 : Blo 327838 1868291 := bstep (se 1 (by rfl) ⟨1401218, by rfl⟩ : syracuseStep 1868291 = 2802437) B2802437
theorem B328199 : Blo 327838 328199 := bstep (se 1 (by rfl) ⟨246149, by rfl⟩ : syracuseStep 328199 = 492299) B492299
theorem B492047 : Blo 327838 492047 := bstep (se 1 (by rfl) ⟨369035, by rfl⟩ : syracuseStep 492047 = 738071) B738071
theorem B328207 : Blo 327838 328207 := bstep (se 1 (by rfl) ⟨246155, by rfl⟩ : syracuseStep 328207 = 492311) B492311
theorem B1245725 : Blo 327838 1245725 := bstep (se 3 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 1245725 = 467147) B467147
theorem B1245739 : Blo 327838 1245739 := bstep (se 1 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 1245739 = 1868609) B1868609
theorem B1016363 : Blo 327838 1016363 := bstep (se 1 (by rfl) ⟨762272, by rfl⟩ : syracuseStep 1016363 = 1524545) B1524545
theorem B1114667 : Blo 327838 1114667 := bstep (se 1 (by rfl) ⟨836000, by rfl⟩ : syracuseStep 1114667 = 1672001) B1672001
theorem B492089 : Blo 327838 492089 := bstep (se 2 (by rfl) ⟨184533, by rfl⟩ : syracuseStep 492089 = 369067) B369067
theorem B369211 : Blo 327838 369211 := bstep (se 1 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 369211 = 553817) B553817
theorem B328251 : Blo 327838 328251 := bstep (se 1 (by rfl) ⟨246188, by rfl⟩ : syracuseStep 328251 = 492377) B492377
theorem B1335869 : Blo 327838 1335869 := bstep (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) B500951
theorem B934487 : Blo 327838 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B836183 : Blo 327838 836183 := bstep (se 1 (by rfl) ⟨627137, by rfl⟩ : syracuseStep 836183 = 1254275) B1254275
theorem B737927 : Blo 327838 737927 := bstep (se 1 (by rfl) ⟨553445, by rfl⟩ : syracuseStep 737927 = 1106891) B1106891
theorem B492167 : Blo 327838 492167 := bstep (se 1 (by rfl) ⟨369125, by rfl⟩ : syracuseStep 492167 = 738251) B738251
theorem B328327 : Blo 327838 328327 := bstep (se 1 (by rfl) ⟨246245, by rfl⟩ : syracuseStep 328327 = 492491) B492491
theorem B328335 : Blo 327838 328335 := bstep (se 1 (by rfl) ⟨246251, by rfl⟩ : syracuseStep 328335 = 492503) B492503
theorem B492203 : Blo 327838 492203 := bstep (se 1 (by rfl) ⟨369152, by rfl⟩ : syracuseStep 492203 = 738305) B738305
theorem B328379 : Blo 327838 328379 := bstep (se 1 (by rfl) ⟨246284, by rfl⟩ : syracuseStep 328379 = 492569) B492569
theorem B492233 : Blo 327838 492233 := bstep (se 2 (by rfl) ⟨184587, by rfl⟩ : syracuseStep 492233 = 369175) B369175
theorem B418603 : Blo 327838 418603 := bstep (se 1 (by rfl) ⟨313952, by rfl⟩ : syracuseStep 418603 = 627905) B627905
theorem B328455 : Blo 327838 328455 := bstep (se 1 (by rfl) ⟨246341, by rfl⟩ : syracuseStep 328455 = 492683) B492683
theorem B328463 : Blo 327838 328463 := bstep (se 1 (by rfl) ⟨246347, by rfl⟩ : syracuseStep 328463 = 492695) B492695
theorem B557867 : Blo 327838 557867 := bstep (se 1 (by rfl) ⟨418400, by rfl⟩ : syracuseStep 557867 = 836801) B836801
theorem B738107 : Blo 327838 738107 := bstep (se 1 (by rfl) ⟨553580, by rfl⟩ : syracuseStep 738107 = 1107161) B1107161
theorem B492347 : Blo 327838 492347 := bstep (se 1 (by rfl) ⟨369260, by rfl⟩ : syracuseStep 492347 = 738521) B738521
theorem B934715 : Blo 327838 934715 := bstep (se 1 (by rfl) ⟨701036, by rfl⟩ : syracuseStep 934715 = 1402073) B1402073
theorem B328507 : Blo 327838 328507 := bstep (se 1 (by rfl) ⟨246380, by rfl⟩ : syracuseStep 328507 = 492761) B492761
theorem B467785 : Blo 327838 467785 := bstep (se 2 (by rfl) ⟨175419, by rfl⟩ : syracuseStep 467785 = 350839) B350839
theorem B4793177 : Blo 327838 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B492407 : Blo 327838 492407 := bstep (se 1 (by rfl) ⟨369305, by rfl⟩ : syracuseStep 492407 = 738611) B738611
theorem B328583 : Blo 327838 328583 := bstep (se 1 (by rfl) ⟨246437, by rfl⟩ : syracuseStep 328583 = 492875) B492875
theorem B492431 : Blo 327838 492431 := bstep (se 1 (by rfl) ⟨369323, by rfl⟩ : syracuseStep 492431 = 738647) B738647
theorem B328591 : Blo 327838 328591 := bstep (se 1 (by rfl) ⟨246443, by rfl⟩ : syracuseStep 328591 = 492887) B492887
theorem B1000345 : Blo 327838 1000345 := bstep (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) B750259
theorem B738233 : Blo 327838 738233 := bstep (se 2 (by rfl) ⟨276837, by rfl⟩ : syracuseStep 738233 = 553675) B553675
theorem B934841 : Blo 327838 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B492473 : Blo 327838 492473 := bstep (se 2 (by rfl) ⟨184677, by rfl⟩ : syracuseStep 492473 = 369355) B369355
theorem B328635 : Blo 327838 328635 := bstep (se 1 (by rfl) ⟨246476, by rfl⟩ : syracuseStep 328635 = 492953) B492953
theorem B394247 : Blo 327838 394247 := bstep (se 1 (by rfl) ⟨295685, by rfl⟩ : syracuseStep 394247 = 591371) B591371
theorem B492551 : Blo 327838 492551 := bstep (se 1 (by rfl) ⟨369413, by rfl⟩ : syracuseStep 492551 = 738827) B738827
theorem B328711 : Blo 327838 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B369679 : Blo 327838 369679 := bstep (se 1 (by rfl) ⟨277259, by rfl⟩ : syracuseStep 369679 = 554519) B554519
theorem B328719 : Blo 327838 328719 := bstep (se 1 (by rfl) ⟨246539, by rfl⟩ : syracuseStep 328719 = 493079) B493079
theorem B492587 : Blo 327838 492587 := bstep (se 1 (by rfl) ⟨369440, by rfl⟩ : syracuseStep 492587 = 738881) B738881
theorem B623675 : Blo 327838 623675 := bstep (se 1 (by rfl) ⟨467756, by rfl⟩ : syracuseStep 623675 = 935513) B935513
theorem B328763 : Blo 327838 328763 := bstep (se 1 (by rfl) ⟨246572, by rfl⟩ : syracuseStep 328763 = 493145) B493145
theorem B492617 : Blo 327838 492617 := bstep (se 2 (by rfl) ⟨184731, by rfl⟩ : syracuseStep 492617 = 369463) B369463
theorem B1254487 : Blo 327838 1254487 := bstep (se 1 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 1254487 = 1881731) B1881731
theorem B4007029 : Blo 327838 4007029 := bstep (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) B375659
theorem B328839 : Blo 327838 328839 := bstep (se 1 (by rfl) ⟨246629, by rfl⟩ : syracuseStep 328839 = 493259) B493259
theorem B328847 : Blo 327838 328847 := bstep (se 1 (by rfl) ⟨246635, by rfl⟩ : syracuseStep 328847 = 493271) B493271
theorem B492731 : Blo 327838 492731 := bstep (se 1 (by rfl) ⟨369548, by rfl⟩ : syracuseStep 492731 = 739097) B739097
theorem B328891 : Blo 327838 328891 := bstep (se 1 (by rfl) ⟨246668, by rfl⟩ : syracuseStep 328891 = 493337) B493337
theorem B492791 : Blo 327838 492791 := bstep (se 1 (by rfl) ⟨369593, by rfl⟩ : syracuseStep 492791 = 739187) B739187
theorem B328967 : Blo 327838 328967 := bstep (se 1 (by rfl) ⟨246725, by rfl⟩ : syracuseStep 328967 = 493451) B493451
theorem B1107215 : Blo 327838 1107215 := bstep (se 1 (by rfl) ⟨830411, by rfl⟩ : syracuseStep 1107215 = 1660823) B1660823
theorem B738575 : Blo 327838 738575 := bstep (se 1 (by rfl) ⟨553931, by rfl⟩ : syracuseStep 738575 = 1107863) B1107863
theorem B492815 : Blo 327838 492815 := bstep (se 1 (by rfl) ⟨369611, by rfl⟩ : syracuseStep 492815 = 739223) B739223
theorem B328975 : Blo 327838 328975 := bstep (se 1 (by rfl) ⟨246731, by rfl⟩ : syracuseStep 328975 = 493463) B493463
theorem B738593 : Blo 327838 738593 := bstep (se 2 (by rfl) ⟨276972, by rfl⟩ : syracuseStep 738593 = 553945) B553945
theorem B492857 : Blo 327838 492857 := bstep (se 2 (by rfl) ⟨184821, by rfl⟩ : syracuseStep 492857 = 369643) B369643
theorem B329019 : Blo 327838 329019 := bstep (se 1 (by rfl) ⟨246764, by rfl⟩ : syracuseStep 329019 = 493529) B493529
theorem B664951 : Blo 327838 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B492935 : Blo 327838 492935 := bstep (se 1 (by rfl) ⟨369701, by rfl⟩ : syracuseStep 492935 = 739403) B739403
theorem B329095 : Blo 327838 329095 := bstep (se 1 (by rfl) ⟨246821, by rfl⟩ : syracuseStep 329095 = 493643) B493643
theorem B1254791 : Blo 327838 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B329103 : Blo 327838 329103 := bstep (se 1 (by rfl) ⟨246827, by rfl⟩ : syracuseStep 329103 = 493655) B493655
theorem B492971 : Blo 327838 492971 := bstep (se 1 (by rfl) ⟨369728, by rfl⟩ : syracuseStep 492971 = 739457) B739457
theorem B787897 : Blo 327838 787897 := bstep (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) B590923
theorem B714169 : Blo 327838 714169 := bstep (se 2 (by rfl) ⟨267813, by rfl⟩ : syracuseStep 714169 = 535627) B535627
theorem B329147 : Blo 327838 329147 := bstep (se 1 (by rfl) ⟨246860, by rfl⟩ : syracuseStep 329147 = 493721) B493721
theorem B493001 : Blo 327838 493001 := bstep (se 2 (by rfl) ⟨184875, by rfl⟩ : syracuseStep 493001 = 369751) B369751
theorem B4072913 : Blo 327838 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B370183 : Blo 327838 370183 := bstep (se 1 (by rfl) ⟨277637, by rfl⟩ : syracuseStep 370183 = 555275) B555275
theorem B329223 : Blo 327838 329223 := bstep (se 1 (by rfl) ⟨246917, by rfl⟩ : syracuseStep 329223 = 493835) B493835
theorem B329231 : Blo 327838 329231 := bstep (se 1 (by rfl) ⟨246923, by rfl⟩ : syracuseStep 329231 = 493847) B493847
theorem B697871 : Blo 327838 697871 := bstep (se 1 (by rfl) ⟨523403, by rfl⟩ : syracuseStep 697871 = 1046807) B1046807
theorem B1107485 : Blo 327838 1107485 := bstep (se 3 (by rfl) ⟨207653, by rfl⟩ : syracuseStep 1107485 = 415307) B415307
theorem B624161 : Blo 327838 624161 := bstep (se 2 (by rfl) ⟨234060, by rfl⟩ : syracuseStep 624161 = 468121) B468121
theorem B493115 : Blo 327838 493115 := bstep (se 1 (by rfl) ⟨369836, by rfl⟩ : syracuseStep 493115 = 739673) B739673
theorem B329275 : Blo 327838 329275 := bstep (se 1 (by rfl) ⟨246956, by rfl⟩ : syracuseStep 329275 = 493913) B493913
theorem B1254973 : Blo 327838 1254973 := bstep (se 3 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 1254973 = 470615) B470615
theorem B738935 : Blo 327838 738935 := bstep (se 1 (by rfl) ⟨554201, by rfl⟩ : syracuseStep 738935 = 1108403) B1108403
theorem B493175 : Blo 327838 493175 := bstep (se 1 (by rfl) ⟨369881, by rfl⟩ : syracuseStep 493175 = 739763) B739763
theorem B329351 : Blo 327838 329351 := bstep (se 1 (by rfl) ⟨247013, by rfl⟩ : syracuseStep 329351 = 494027) B494027
theorem B493199 : Blo 327838 493199 := bstep (se 1 (by rfl) ⟨369899, by rfl⟩ : syracuseStep 493199 = 739799) B739799
theorem B329359 : Blo 327838 329359 := bstep (se 1 (by rfl) ⟨247019, by rfl⟩ : syracuseStep 329359 = 494039) B494039
theorem B5072563 : Blo 327838 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B493241 : Blo 327838 493241 := bstep (se 2 (by rfl) ⟨184965, by rfl⟩ : syracuseStep 493241 = 369931) B369931
theorem B370363 : Blo 327838 370363 := bstep (se 1 (by rfl) ⟨277772, by rfl⟩ : syracuseStep 370363 = 555545) B555545
theorem B329403 : Blo 327838 329403 := bstep (se 1 (by rfl) ⟨247052, by rfl⟩ : syracuseStep 329403 = 494105) B494105
theorem B1689281 : Blo 327838 1689281 := bstep (se 2 (by rfl) ⟨633480, by rfl⟩ : syracuseStep 1689281 = 1266961) B1266961
theorem B493319 : Blo 327838 493319 := bstep (se 1 (by rfl) ⟨369989, by rfl⟩ : syracuseStep 493319 = 739979) B739979
theorem B329479 : Blo 327838 329479 := bstep (se 1 (by rfl) ⟨247109, by rfl⟩ : syracuseStep 329479 = 494219) B494219
theorem B329487 : Blo 327838 329487 := bstep (se 1 (by rfl) ⟨247115, by rfl⟩ : syracuseStep 329487 = 494231) B494231
theorem B739115 : Blo 327838 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B493355 : Blo 327838 493355 := bstep (se 1 (by rfl) ⟨370016, by rfl⟩ : syracuseStep 493355 = 740033) B740033
theorem B329531 : Blo 327838 329531 := bstep (se 1 (by rfl) ⟨247148, by rfl⟩ : syracuseStep 329531 = 494297) B494297
theorem B1115963 : Blo 327838 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B493385 : Blo 327838 493385 := bstep (se 2 (by rfl) ⟨185019, by rfl⟩ : syracuseStep 493385 = 370039) B370039
theorem B624503 : Blo 327838 624503 := bstep (se 1 (by rfl) ⟨468377, by rfl⟩ : syracuseStep 624503 = 936755) B936755
theorem B329607 : Blo 327838 329607 := bstep (se 1 (by rfl) ⟨247205, by rfl⟩ : syracuseStep 329607 = 494411) B494411
theorem B329615 : Blo 327838 329615 := bstep (se 1 (by rfl) ⟨247211, by rfl⟩ : syracuseStep 329615 = 494423) B494423
theorem B1025939 : Blo 327838 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B4646807 : Blo 327838 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B493499 : Blo 327838 493499 := bstep (se 1 (by rfl) ⟨370124, by rfl⟩ : syracuseStep 493499 = 740249) B740249
theorem B329659 : Blo 327838 329659 := bstep (se 1 (by rfl) ⟨247244, by rfl⟩ : syracuseStep 329659 = 494489) B494489
theorem B493559 : Blo 327838 493559 := bstep (se 1 (by rfl) ⟨370169, by rfl⟩ : syracuseStep 493559 = 740339) B740339
theorem B329735 : Blo 327838 329735 := bstep (se 1 (by rfl) ⟨247301, by rfl⟩ : syracuseStep 329735 = 494603) B494603
theorem B1665035 : Blo 327838 1665035 := bstep (se 1 (by rfl) ⟨1248776, by rfl⟩ : syracuseStep 1665035 = 2497553) B2497553
theorem B10651661 : Blo 327838 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B493583 : Blo 327838 493583 := bstep (se 1 (by rfl) ⟨370187, by rfl⟩ : syracuseStep 493583 = 740375) B740375
theorem B329743 : Blo 327838 329743 := bstep (se 1 (by rfl) ⟨247307, by rfl⟩ : syracuseStep 329743 = 494615) B494615
theorem B395323 : Blo 327838 395323 := bstep (se 1 (by rfl) ⟨296492, by rfl⟩ : syracuseStep 395323 = 592985) B592985
theorem B493625 : Blo 327838 493625 := bstep (se 2 (by rfl) ⟨185109, by rfl⟩ : syracuseStep 493625 = 370219) B370219
theorem B329787 : Blo 327838 329787 := bstep (se 1 (by rfl) ⟨247340, by rfl⟩ : syracuseStep 329787 = 494681) B494681
theorem B10152053 : Blo 327838 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B493703 : Blo 327838 493703 := bstep (se 1 (by rfl) ⟨370277, by rfl⟩ : syracuseStep 493703 = 740555) B740555
theorem B329863 : Blo 327838 329863 := bstep (se 1 (by rfl) ⟨247397, by rfl⟩ : syracuseStep 329863 = 494795) B494795
theorem B370831 : Blo 327838 370831 := bstep (se 1 (by rfl) ⟨278123, by rfl⟩ : syracuseStep 370831 = 556247) B556247
theorem B329871 : Blo 327838 329871 := bstep (se 1 (by rfl) ⟨247403, by rfl⟩ : syracuseStep 329871 = 494807) B494807
theorem B739475 : Blo 327838 739475 := bstep (se 1 (by rfl) ⟨554606, by rfl⟩ : syracuseStep 739475 = 1109213) B1109213
theorem B493739 : Blo 327838 493739 := bstep (se 1 (by rfl) ⟨370304, by rfl⟩ : syracuseStep 493739 = 740609) B740609
theorem B1665197 : Blo 327838 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B329915 : Blo 327838 329915 := bstep (se 1 (by rfl) ⟨247436, by rfl⟩ : syracuseStep 329915 = 494873) B494873
theorem B739529 : Blo 327838 739529 := bstep (se 2 (by rfl) ⟨277323, by rfl⟩ : syracuseStep 739529 = 554647) B554647
theorem B493769 : Blo 327838 493769 := bstep (se 2 (by rfl) ⟨185163, by rfl⟩ : syracuseStep 493769 = 370327) B370327
theorem B8005877 : Blo 327838 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B428279 : Blo 327838 428279 := bstep (se 1 (by rfl) ⟨321209, by rfl⟩ : syracuseStep 428279 = 642419) B642419
theorem B329991 : Blo 327838 329991 := bstep (se 1 (by rfl) ⟨247493, by rfl⟩ : syracuseStep 329991 = 494987) B494987
theorem B329999 : Blo 327838 329999 := bstep (se 1 (by rfl) ⟨247499, by rfl⟩ : syracuseStep 329999 = 494999) B494999
theorem B2664737 : Blo 327838 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B493883 : Blo 327838 493883 := bstep (se 1 (by rfl) ⟨370412, by rfl⟩ : syracuseStep 493883 = 740825) B740825
theorem B330043 : Blo 327838 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B493943 : Blo 327838 493943 := bstep (se 1 (by rfl) ⟨370457, by rfl⟩ : syracuseStep 493943 = 740915) B740915
theorem B330119 : Blo 327838 330119 := bstep (se 1 (by rfl) ⟨247589, by rfl⟩ : syracuseStep 330119 = 495179) B495179
theorem B493967 : Blo 327838 493967 := bstep (se 1 (by rfl) ⟨370475, by rfl⟩ : syracuseStep 493967 = 740951) B740951
theorem B330127 : Blo 327838 330127 := bstep (se 1 (by rfl) ⟨247595, by rfl⟩ : syracuseStep 330127 = 495191) B495191
theorem B1067411 : Blo 327838 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B494009 : Blo 327838 494009 := bstep (se 2 (by rfl) ⟨185253, by rfl⟩ : syracuseStep 494009 = 370507) B370507
theorem B330171 : Blo 327838 330171 := bstep (se 1 (by rfl) ⟨247628, by rfl⟩ : syracuseStep 330171 = 495257) B495257
theorem B846281 : Blo 327838 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B5646833 : Blo 327838 5646833 := bstep (se 2 (by rfl) ⟨2117562, by rfl⟩ : syracuseStep 5646833 = 4235125) B4235125
theorem B494087 : Blo 327838 494087 := bstep (se 1 (by rfl) ⟨370565, by rfl⟩ : syracuseStep 494087 = 741131) B741131
theorem B330247 : Blo 327838 330247 := bstep (se 1 (by rfl) ⟨247685, by rfl⟩ : syracuseStep 330247 = 495371) B495371
theorem B330255 : Blo 327838 330255 := bstep (se 1 (by rfl) ⟨247691, by rfl⟩ : syracuseStep 330255 = 495383) B495383
theorem B3156509 : Blo 327838 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B936481 : Blo 327838 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B494123 : Blo 327838 494123 := bstep (se 1 (by rfl) ⟨370592, by rfl⟩ : syracuseStep 494123 = 741185) B741185
theorem B330299 : Blo 327838 330299 := bstep (se 1 (by rfl) ⟨247724, by rfl⟩ : syracuseStep 330299 = 495449) B495449
theorem B494153 : Blo 327838 494153 := bstep (se 2 (by rfl) ⟨185307, by rfl⟩ : syracuseStep 494153 = 370615) B370615
theorem B371335 : Blo 327838 371335 := bstep (se 1 (by rfl) ⟨278501, by rfl⟩ : syracuseStep 371335 = 557003) B557003
theorem B330375 : Blo 327838 330375 := bstep (se 1 (by rfl) ⟨247781, by rfl⟩ : syracuseStep 330375 = 495563) B495563
theorem B330383 : Blo 327838 330383 := bstep (se 1 (by rfl) ⟨247787, by rfl⟩ : syracuseStep 330383 = 495575) B495575
theorem B527033 : Blo 327838 527033 := bstep (se 2 (by rfl) ⟨197637, by rfl⟩ : syracuseStep 527033 = 395275) B395275
theorem B494267 : Blo 327838 494267 := bstep (se 1 (by rfl) ⟨370700, by rfl⟩ : syracuseStep 494267 = 741401) B741401
theorem B330427 : Blo 327838 330427 := bstep (se 1 (by rfl) ⟨247820, by rfl⟩ : syracuseStep 330427 = 495641) B495641
theorem B494327 : Blo 327838 494327 := bstep (se 1 (by rfl) ⟨370745, by rfl⟩ : syracuseStep 494327 = 741491) B741491
theorem B830209 : Blo 327838 830209 := bstep (se 2 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 830209 = 622657) B622657
theorem B330503 : Blo 327838 330503 := bstep (se 1 (by rfl) ⟨247877, by rfl⟩ : syracuseStep 330503 = 495755) B495755
theorem B494351 : Blo 327838 494351 := bstep (se 1 (by rfl) ⟨370763, by rfl⟩ : syracuseStep 494351 = 741527) B741527
theorem B330511 : Blo 327838 330511 := bstep (se 1 (by rfl) ⟨247883, by rfl⟩ : syracuseStep 330511 = 495767) B495767
theorem B4016947 : Blo 327838 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B494393 : Blo 327838 494393 := bstep (se 2 (by rfl) ⟨185397, by rfl⟩ : syracuseStep 494393 = 370795) B370795
theorem B371515 : Blo 327838 371515 := bstep (se 1 (by rfl) ⟨278636, by rfl⟩ : syracuseStep 371515 = 557273) B557273
theorem B330555 : Blo 327838 330555 := bstep (se 1 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 330555 = 495833) B495833
theorem B1190771 : Blo 327838 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B740231 : Blo 327838 740231 := bstep (se 1 (by rfl) ⟨555173, by rfl⟩ : syracuseStep 740231 = 1110347) B1110347
theorem B494471 : Blo 327838 494471 := bstep (se 1 (by rfl) ⟨370853, by rfl⟩ : syracuseStep 494471 = 741707) B741707
theorem B330631 : Blo 327838 330631 := bstep (se 1 (by rfl) ⟨247973, by rfl⟩ : syracuseStep 330631 = 495947) B495947
theorem B330639 : Blo 327838 330639 := bstep (se 1 (by rfl) ⟨247979, by rfl⟩ : syracuseStep 330639 = 495959) B495959
theorem B1108889 : Blo 327838 1108889 := bstep (se 2 (by rfl) ⟨415833, by rfl⟩ : syracuseStep 1108889 = 831667) B831667
theorem B3763097 : Blo 327838 3763097 := bstep (se 2 (by rfl) ⟨1411161, by rfl⟩ : syracuseStep 3763097 = 2822323) B2822323
theorem B494507 : Blo 327838 494507 := bstep (se 1 (by rfl) ⟨370880, by rfl⟩ : syracuseStep 494507 = 741761) B741761
theorem B330683 : Blo 327838 330683 := bstep (se 1 (by rfl) ⟨248012, by rfl⟩ : syracuseStep 330683 = 496025) B496025
theorem B494537 : Blo 327838 494537 := bstep (se 2 (by rfl) ⟨185451, by rfl⟩ : syracuseStep 494537 = 370903) B370903
theorem B936971 : Blo 327838 936971 := bstep (se 1 (by rfl) ⟨702728, by rfl⟩ : syracuseStep 936971 = 1405457) B1405457
theorem B1674269 : Blo 327838 1674269 := bstep (se 3 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 1674269 = 627851) B627851
theorem B740411 : Blo 327838 740411 := bstep (se 1 (by rfl) ⟨555308, by rfl⟩ : syracuseStep 740411 = 1110617) B1110617
theorem B494651 : Blo 327838 494651 := bstep (se 1 (by rfl) ⟨370988, by rfl⟩ : syracuseStep 494651 = 741977) B741977
theorem B494711 : Blo 327838 494711 := bstep (se 1 (by rfl) ⟨371033, by rfl⟩ : syracuseStep 494711 = 742067) B742067
theorem B494735 : Blo 327838 494735 := bstep (se 1 (by rfl) ⟨371051, by rfl⟩ : syracuseStep 494735 = 742103) B742103
theorem B740537 : Blo 327838 740537 := bstep (se 2 (by rfl) ⟨277701, by rfl⟩ : syracuseStep 740537 = 555403) B555403
theorem B494777 : Blo 327838 494777 := bstep (se 2 (by rfl) ⟨185541, by rfl⟩ : syracuseStep 494777 = 371083) B371083
theorem B494855 : Blo 327838 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B1404175 : Blo 327838 1404175 := bstep (se 1 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 1404175 = 2106263) B2106263
theorem B371983 : Blo 327838 371983 := bstep (se 1 (by rfl) ⟨278987, by rfl⟩ : syracuseStep 371983 = 557975) B557975
theorem B1772837 : Blo 327838 1772837 := bstep (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) B332407
theorem B494891 : Blo 327838 494891 := bstep (se 1 (by rfl) ⟨371168, by rfl⟩ : syracuseStep 494891 = 742337) B742337
theorem B494921 : Blo 327838 494921 := bstep (se 2 (by rfl) ⟨185595, by rfl⟩ : syracuseStep 494921 = 371191) B371191
theorem B830807 : Blo 327838 830807 := bstep (se 1 (by rfl) ⟨623105, by rfl⟩ : syracuseStep 830807 = 1246211) B1246211
theorem B396679 : Blo 327838 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B626105 : Blo 327838 626105 := bstep (se 2 (by rfl) ⟨234789, by rfl⟩ : syracuseStep 626105 = 469579) B469579
theorem B1019321 : Blo 327838 1019321 := bstep (se 2 (by rfl) ⟨382245, by rfl⟩ : syracuseStep 1019321 = 764491) B764491
theorem B495035 : Blo 327838 495035 := bstep (se 1 (by rfl) ⟨371276, by rfl⟩ : syracuseStep 495035 = 742553) B742553
theorem B495095 : Blo 327838 495095 := bstep (se 1 (by rfl) ⟨371321, by rfl⟩ : syracuseStep 495095 = 742643) B742643
theorem B790031 : Blo 327838 790031 := bstep (se 1 (by rfl) ⟨592523, by rfl⟩ : syracuseStep 790031 = 1185047) B1185047
theorem B740879 : Blo 327838 740879 := bstep (se 1 (by rfl) ⟨555659, by rfl⟩ : syracuseStep 740879 = 1111319) B1111319
theorem B495119 : Blo 327838 495119 := bstep (se 1 (by rfl) ⟨371339, by rfl⟩ : syracuseStep 495119 = 742679) B742679
theorem B740897 : Blo 327838 740897 := bstep (se 2 (by rfl) ⟨277836, by rfl⟩ : syracuseStep 740897 = 555673) B555673
theorem B831019 : Blo 327838 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B495161 : Blo 327838 495161 := bstep (se 2 (by rfl) ⟨185685, by rfl⟩ : syracuseStep 495161 = 371371) B371371
theorem B1109591 : Blo 327838 1109591 := bstep (se 1 (by rfl) ⟨832193, by rfl⟩ : syracuseStep 1109591 = 1664387) B1664387
theorem B528007 : Blo 327838 528007 := bstep (se 1 (by rfl) ⟨396005, by rfl⟩ : syracuseStep 528007 = 792011) B792011
theorem B495239 : Blo 327838 495239 := bstep (se 1 (by rfl) ⟨371429, by rfl⟩ : syracuseStep 495239 = 742859) B742859
theorem B495275 : Blo 327838 495275 := bstep (se 1 (by rfl) ⟨371456, by rfl⟩ : syracuseStep 495275 = 742913) B742913
theorem B831161 : Blo 327838 831161 := bstep (se 2 (by rfl) ⟨311685, by rfl⟩ : syracuseStep 831161 = 623371) B623371
theorem B1003193 : Blo 327838 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B495305 : Blo 327838 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B470729 : Blo 327838 470729 := bstep (se 2 (by rfl) ⟨176523, by rfl⟩ : syracuseStep 470729 = 353047) B353047
theorem B2115821 : Blo 327838 2115821 := bstep (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) B793433
theorem B3337985 : Blo 327838 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B1666817 : Blo 327838 1666817 := bstep (se 2 (by rfl) ⟨625056, by rfl⟩ : syracuseStep 1666817 = 1250113) B1250113
theorem B626447 : Blo 327838 626447 := bstep (se 1 (by rfl) ⟨469835, by rfl⟩ : syracuseStep 626447 = 939671) B939671
theorem B937757 : Blo 327838 937757 := bstep (se 3 (by rfl) ⟨175829, by rfl⟩ : syracuseStep 937757 = 351659) B351659
theorem B495419 : Blo 327838 495419 := bstep (se 1 (by rfl) ⟨371564, by rfl⟩ : syracuseStep 495419 = 743129) B743129
theorem B1576793 : Blo 327838 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B741239 : Blo 327838 741239 := bstep (se 1 (by rfl) ⟨555929, by rfl⟩ : syracuseStep 741239 = 1111859) B1111859
theorem B495479 : Blo 327838 495479 := bstep (se 1 (by rfl) ⟨371609, by rfl⟩ : syracuseStep 495479 = 743219) B743219
theorem B495503 : Blo 327838 495503 := bstep (se 1 (by rfl) ⟨371627, by rfl⟩ : syracuseStep 495503 = 743255) B743255
theorem B1879955 : Blo 327838 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B2813849 : Blo 327838 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B495545 : Blo 327838 495545 := bstep (se 2 (by rfl) ⟨185829, by rfl⟩ : syracuseStep 495545 = 371659) B371659
theorem B495623 : Blo 327838 495623 := bstep (se 1 (by rfl) ⟨371717, by rfl⟩ : syracuseStep 495623 = 743435) B743435
theorem B1126429 : Blo 327838 1126429 := bstep (se 3 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 1126429 = 422411) B422411
theorem B741419 : Blo 327838 741419 := bstep (se 1 (by rfl) ⟨556064, by rfl⟩ : syracuseStep 741419 = 1112129) B1112129
theorem B495659 : Blo 327838 495659 := bstep (se 1 (by rfl) ⟨371744, by rfl⟩ : syracuseStep 495659 = 743489) B743489
theorem B1110077 : Blo 327838 1110077 := bstep (se 3 (by rfl) ⟨208139, by rfl⟩ : syracuseStep 1110077 = 416279) B416279
theorem B495689 : Blo 327838 495689 := bstep (se 2 (by rfl) ⟨185883, by rfl⟩ : syracuseStep 495689 = 371767) B371767
theorem B2494637 : Blo 327838 2494637 := bstep (se 3 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 2494637 = 935489) B935489
theorem B495803 : Blo 327838 495803 := bstep (se 1 (by rfl) ⟨371852, by rfl⟩ : syracuseStep 495803 = 743705) B743705
theorem B495863 : Blo 327838 495863 := bstep (se 1 (by rfl) ⟨371897, by rfl⟩ : syracuseStep 495863 = 743795) B743795
theorem B2003201 : Blo 327838 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B495887 : Blo 327838 495887 := bstep (se 1 (by rfl) ⟨371915, by rfl⟩ : syracuseStep 495887 = 743831) B743831
theorem B495929 : Blo 327838 495929 := bstep (se 2 (by rfl) ⟨185973, by rfl⟩ : syracuseStep 495929 = 371947) B371947
theorem B2027891 : Blo 327838 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B553351 : Blo 327838 553351 := bstep (se 1 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 553351 = 830027) B830027
theorem B1503623 : Blo 327838 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1880455 : Blo 327838 1880455 := bstep (se 1 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 1880455 = 2820683) B2820683
theorem B496007 : Blo 327838 496007 := bstep (se 1 (by rfl) ⟨372005, by rfl⟩ : syracuseStep 496007 = 744011) B744011
theorem B2806163 : Blo 327838 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B741779 : Blo 327838 741779 := bstep (se 1 (by rfl) ⟨556334, by rfl⟩ : syracuseStep 741779 = 1112669) B1112669
theorem B496043 : Blo 327838 496043 := bstep (se 1 (by rfl) ⟨372032, by rfl⟩ : syracuseStep 496043 = 744065) B744065
theorem B741833 : Blo 327838 741833 := bstep (se 2 (by rfl) ⟨278187, by rfl⟩ : syracuseStep 741833 = 556375) B556375
theorem B496073 : Blo 327838 496073 := bstep (se 2 (by rfl) ⟨186027, by rfl⟩ : syracuseStep 496073 = 372055) B372055
theorem B1667627 : Blo 327838 1667627 := bstep (se 1 (by rfl) ⟨1250720, by rfl⟩ : syracuseStep 1667627 = 2501441) B2501441
theorem B627259 : Blo 327838 627259 := bstep (se 1 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 627259 = 940889) B940889
theorem B1004167 : Blo 327838 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B627335 : Blo 327838 627335 := bstep (se 1 (by rfl) ⟨470501, by rfl⟩ : syracuseStep 627335 = 941003) B941003
theorem B832153 : Blo 327838 832153 := bstep (se 2 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 832153 = 624115) B624115
theorem B2143027 : Blo 327838 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B832315 : Blo 327838 832315 := bstep (se 1 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 832315 = 1248473) B1248473
theorem B1405831 : Blo 327838 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B832457 : Blo 327838 832457 := bstep (se 2 (by rfl) ⟨312171, by rfl⟩ : syracuseStep 832457 = 624343) B624343
theorem B1659851 : Blo 327838 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B1692683 : Blo 327838 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B553999 : Blo 327838 553999 := bstep (se 1 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 553999 = 830999) B830999
theorem B701473 : Blo 327838 701473 := bstep (se 2 (by rfl) ⟨263052, by rfl⟩ : syracuseStep 701473 = 526105) B526105
theorem B627745 : Blo 327838 627745 := bstep (se 2 (by rfl) ⟨235404, by rfl⟩ : syracuseStep 627745 = 470809) B470809
theorem B1872983 : Blo 327838 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B9172099 : Blo 327838 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B742535 : Blo 327838 742535 := bstep (se 1 (by rfl) ⟨556901, by rfl⟩ : syracuseStep 742535 = 1113803) B1113803
theorem B1185005 : Blo 327838 1185005 := bstep (se 3 (by rfl) ⟨222188, by rfl⟩ : syracuseStep 1185005 = 444377) B444377
theorem B414983 : Blo 327838 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B1660175 : Blo 327838 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B832801 : Blo 327838 832801 := bstep (se 2 (by rfl) ⟨312300, by rfl⟩ : syracuseStep 832801 = 624601) B624601
theorem B1586465 : Blo 327838 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B742715 : Blo 327838 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B3159431 : Blo 327838 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B2004371 : Blo 327838 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B1111481 : Blo 327838 1111481 := bstep (se 2 (by rfl) ⟨416805, by rfl⟩ : syracuseStep 1111481 = 833611) B833611
theorem B742841 : Blo 327838 742841 := bstep (se 2 (by rfl) ⟨278565, by rfl⟩ : syracuseStep 742841 = 557131) B557131
theorem B3741227 : Blo 327838 3741227 := bstep (se 1 (by rfl) ⟨2805920, by rfl⟩ : syracuseStep 3741227 = 5611841) B5611841
theorem B554539 : Blo 327838 554539 := bstep (se 1 (by rfl) ⟨415904, by rfl⟩ : syracuseStep 554539 = 831809) B831809
theorem B1250903 : Blo 327838 1250903 := bstep (se 1 (by rfl) ⟨938177, by rfl⟩ : syracuseStep 1250903 = 1876355) B1876355
theorem B554681 : Blo 327838 554681 := bstep (se 2 (by rfl) ⟨208005, by rfl⟩ : syracuseStep 554681 = 416011) B416011
theorem B841487 : Blo 327838 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B743183 : Blo 327838 743183 := bstep (se 1 (by rfl) ⟨557387, by rfl⟩ : syracuseStep 743183 = 1114775) B1114775
theorem B743201 : Blo 327838 743201 := bstep (se 2 (by rfl) ⟨278700, by rfl⟩ : syracuseStep 743201 = 557401) B557401
theorem B1668923 : Blo 327838 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B939863 : Blo 327838 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B1054579 : Blo 327838 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B833399 : Blo 327838 833399 := bstep (se 1 (by rfl) ⟨625049, by rfl⟩ : syracuseStep 833399 = 1250099) B1250099
theorem B1775495 : Blo 327838 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B415631 : Blo 327838 415631 := bstep (se 1 (by rfl) ⟨311723, by rfl⟩ : syracuseStep 415631 = 623447) B623447
theorem B890777 : Blo 327838 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B3790795 : Blo 327838 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B1669085 : Blo 327838 1669085 := bstep (se 3 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 1669085 = 625907) B625907
theorem B1112075 : Blo 327838 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B702523 : Blo 327838 702523 := bstep (se 1 (by rfl) ⟨526892, by rfl⟩ : syracuseStep 702523 = 1053785) B1053785
theorem B1251389 : Blo 327838 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B3749975 : Blo 327838 3749975 := bstep (se 1 (by rfl) ⟨2812481, by rfl⟩ : syracuseStep 3749975 = 5624963) B5624963
theorem B1112183 : Blo 327838 1112183 := bstep (se 1 (by rfl) ⟨834137, by rfl⟩ : syracuseStep 1112183 = 1668275) B1668275
theorem B743543 : Blo 327838 743543 := bstep (se 1 (by rfl) ⟨557657, by rfl⟩ : syracuseStep 743543 = 1115315) B1115315
theorem B669881 : Blo 327838 669881 := bstep (se 2 (by rfl) ⟨251205, by rfl⟩ : syracuseStep 669881 = 502411) B502411
theorem B1407233 : Blo 327838 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B5363981 : Blo 327838 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B1669409 : Blo 327838 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B743723 : Blo 327838 743723 := bstep (se 1 (by rfl) ⟨557792, by rfl⟩ : syracuseStep 743723 = 1115585) B1115585
theorem B842071 : Blo 327838 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B555383 : Blo 327838 555383 := bstep (se 1 (by rfl) ⟨416537, by rfl⟩ : syracuseStep 555383 = 833075) B833075
theorem B1579409 : Blo 327838 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B1604119 : Blo 327838 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B2497067 : Blo 327838 2497067 := bstep (se 1 (by rfl) ⟨1872800, by rfl⟩ : syracuseStep 2497067 = 3745601) B3745601
theorem B703019 : Blo 327838 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B3570277 : Blo 327838 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B1448567 : Blo 327838 1448567 := bstep (se 1 (by rfl) ⟨1086425, by rfl⟩ : syracuseStep 1448567 = 2172851) B2172851
theorem B744083 : Blo 327838 744083 := bstep (se 1 (by rfl) ⟨558062, by rfl⟩ : syracuseStep 744083 = 1116125) B1116125
theorem B793241 : Blo 327838 793241 := bstep (se 2 (by rfl) ⟨297465, by rfl⟩ : syracuseStep 793241 = 594931) B594931
theorem B940729 : Blo 327838 940729 := bstep (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) B705547
theorem B1661633 : Blo 327838 1661633 := bstep (se 2 (by rfl) ⟨623112, by rfl⟩ : syracuseStep 1661633 = 1246225) B1246225
theorem B1112777 : Blo 327838 1112777 := bstep (se 2 (by rfl) ⟨417291, by rfl⟩ : syracuseStep 1112777 = 834583) B834583
theorem B744137 : Blo 327838 744137 := bstep (se 2 (by rfl) ⟨279051, by rfl⟩ : syracuseStep 744137 = 558103) B558103
theorem B711467 : Blo 327838 711467 := bstep (se 1 (by rfl) ⟨533600, by rfl⟩ : syracuseStep 711467 = 1067201) B1067201
theorem B555835 : Blo 327838 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B555977 : Blo 327838 555977 := bstep (se 2 (by rfl) ⟨208491, by rfl⟩ : syracuseStep 555977 = 416983) B416983
theorem B1801169 : Blo 327838 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B1874897 : Blo 327838 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B941071 : Blo 327838 941071 := bstep (se 1 (by rfl) ⟨705803, by rfl⟩ : syracuseStep 941071 = 1411607) B1411607
theorem B2006045 : Blo 327838 2006045 := bstep (se 3 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 2006045 = 752267) B752267
theorem B3988541 : Blo 327838 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B2800727 : Blo 327838 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B2505815 : Blo 327838 2505815 := bstep (se 1 (by rfl) ⟨1879361, by rfl⟩ : syracuseStep 2505815 = 3758723) B3758723
theorem B834695 : Blo 327838 834695 := bstep (se 1 (by rfl) ⟨626021, by rfl⟩ : syracuseStep 834695 = 1252043) B1252043
theorem B834745 : Blo 327838 834745 := bstep (se 2 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 834745 = 626059) B626059
theorem B1670381 : Blo 327838 1670381 := bstep (se 3 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 1670381 = 626393) B626393
theorem B1588481 : Blo 327838 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B335111 : Blo 327838 335111 := bstep (se 1 (by rfl) ⟨251333, by rfl⟩ : syracuseStep 335111 = 502667) B502667
theorem B941345 : Blo 327838 941345 := bstep (se 2 (by rfl) ⟨353004, by rfl⟩ : syracuseStep 941345 = 706009) B706009
theorem B2366779 : Blo 327838 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B1113479 : Blo 327838 1113479 := bstep (se 1 (by rfl) ⟨835109, by rfl⟩ : syracuseStep 1113479 = 1670219) B1670219
theorem B867737 : Blo 327838 867737 := bstep (se 2 (by rfl) ⟨325401, by rfl⟩ : syracuseStep 867737 = 650803) B650803
theorem B1252817 : Blo 327838 1252817 := bstep (se 2 (by rfl) ⟨469806, by rfl⟩ : syracuseStep 1252817 = 939613) B939613
theorem B2711069 : Blo 327838 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B4726349 : Blo 327838 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B556679 : Blo 327838 556679 := bstep (se 1 (by rfl) ⟨417509, by rfl⟩ : syracuseStep 556679 = 835019) B835019
theorem B1113857 : Blo 327838 1113857 := bstep (se 2 (by rfl) ⟨417696, by rfl⟩ : syracuseStep 1113857 = 835393) B835393
theorem B999179 : Blo 327838 999179 := bstep (se 1 (by rfl) ⟨749384, by rfl⟩ : syracuseStep 999179 = 1498769) B1498769
theorem B1056527 : Blo 327838 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B835343 : Blo 327838 835343 := bstep (se 1 (by rfl) ⟨626507, by rfl⟩ : syracuseStep 835343 = 1253015) B1253015
theorem B4751257 : Blo 327838 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B1662929 : Blo 327838 1662929 := bstep (se 2 (by rfl) ⟨623598, by rfl⟩ : syracuseStep 1662929 = 1247197) B1247197
theorem B1114127 : Blo 327838 1114127 := bstep (se 1 (by rfl) ⟨835595, by rfl⟩ : syracuseStep 1114127 = 1671191) B1671191
theorem B1663091 : Blo 327838 1663091 := bstep (se 1 (by rfl) ⟨1247318, by rfl⟩ : syracuseStep 1663091 = 2494637) B2494637
theorem B1335467 : Blo 327838 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B327855 : Blo 327838 327855 := bstep (se 1 (by rfl) ⟨245891, by rfl⟩ : syracuseStep 327855 = 491783) B491783
theorem B327879 : Blo 327838 327879 := bstep (se 1 (by rfl) ⟨245909, by rfl⟩ : syracuseStep 327879 = 491819) B491819
theorem B327899 : Blo 327838 327899 := bstep (se 1 (by rfl) ⟨245924, by rfl⟩ : syracuseStep 327899 = 491849) B491849
theorem B1351927 : Blo 327838 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B2162945 : Blo 327838 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B327975 : Blo 327838 327975 := bstep (se 1 (by rfl) ⟨245981, by rfl⟩ : syracuseStep 327975 = 491963) B491963
theorem B328015 : Blo 327838 328015 := bstep (se 1 (by rfl) ⟨246011, by rfl⟩ : syracuseStep 328015 = 492023) B492023
theorem B1245527 : Blo 327838 1245527 := bstep (se 1 (by rfl) ⟨934145, by rfl⟩ : syracuseStep 1245527 = 1868291) B1868291
theorem B328031 : Blo 327838 328031 := bstep (se 1 (by rfl) ⟨246023, by rfl⟩ : syracuseStep 328031 = 492047) B492047
theorem B328059 : Blo 327838 328059 := bstep (se 1 (by rfl) ⟨246044, by rfl⟩ : syracuseStep 328059 = 492089) B492089
theorem B622991 : Blo 327838 622991 := bstep (se 1 (by rfl) ⟨467243, by rfl⟩ : syracuseStep 622991 = 934487) B934487
theorem B557455 : Blo 327838 557455 := bstep (se 1 (by rfl) ⟨418091, by rfl⟩ : syracuseStep 557455 = 836183) B836183
theorem B491951 : Blo 327838 491951 := bstep (se 1 (by rfl) ⟨368963, by rfl⟩ : syracuseStep 491951 = 737927) B737927
theorem B328111 : Blo 327838 328111 := bstep (se 1 (by rfl) ⟨246083, by rfl⟩ : syracuseStep 328111 = 492167) B492167
theorem B328135 : Blo 327838 328135 := bstep (se 1 (by rfl) ⟨246101, by rfl⟩ : syracuseStep 328135 = 492203) B492203
theorem B1122761 : Blo 327838 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B328155 : Blo 327838 328155 := bstep (se 1 (by rfl) ⟨246116, by rfl⟩ : syracuseStep 328155 = 492233) B492233
theorem B1786349 : Blo 327838 1786349 := bstep (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) B669881
theorem B737801 : Blo 327838 737801 := bstep (se 2 (by rfl) ⟨276675, by rfl⟩ : syracuseStep 737801 = 553351) B553351
theorem B492041 : Blo 327838 492041 := bstep (se 2 (by rfl) ⟨184515, by rfl⟩ : syracuseStep 492041 = 369031) B369031
theorem B2507273 : Blo 327838 2507273 := bstep (se 2 (by rfl) ⟨940227, by rfl⟩ : syracuseStep 2507273 = 1880455) B1880455
theorem B492071 : Blo 327838 492071 := bstep (se 1 (by rfl) ⟨369053, by rfl⟩ : syracuseStep 492071 = 738107) B738107
theorem B328231 : Blo 327838 328231 := bstep (se 1 (by rfl) ⟨246173, by rfl⟩ : syracuseStep 328231 = 492347) B492347
theorem B623143 : Blo 327838 623143 := bstep (se 1 (by rfl) ⟨467357, by rfl⟩ : syracuseStep 623143 = 934715) B934715
theorem B3195451 : Blo 327838 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B328271 : Blo 327838 328271 := bstep (se 1 (by rfl) ⟨246203, by rfl⟩ : syracuseStep 328271 = 492407) B492407
theorem B328287 : Blo 327838 328287 := bstep (se 1 (by rfl) ⟨246215, by rfl⟩ : syracuseStep 328287 = 492431) B492431
theorem B1114721 : Blo 327838 1114721 := bstep (se 2 (by rfl) ⟨418020, by rfl⟩ : syracuseStep 1114721 = 836041) B836041
theorem B492155 : Blo 327838 492155 := bstep (se 1 (by rfl) ⟨369116, by rfl⟩ : syracuseStep 492155 = 738233) B738233
theorem B623227 : Blo 327838 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B328315 : Blo 327838 328315 := bstep (se 1 (by rfl) ⟨246236, by rfl⟩ : syracuseStep 328315 = 492473) B492473
theorem B1106567 : Blo 327838 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B328367 : Blo 327838 328367 := bstep (se 1 (by rfl) ⟨246275, by rfl⟩ : syracuseStep 328367 = 492551) B492551
theorem B1106621 : Blo 327838 1106621 := bstep (se 3 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 1106621 = 414983) B414983
theorem B893629 : Blo 327838 893629 := bstep (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) B335111
theorem B328391 : Blo 327838 328391 := bstep (se 1 (by rfl) ⟨246293, by rfl⟩ : syracuseStep 328391 = 492587) B492587
theorem B2138825 : Blo 327838 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B328411 : Blo 327838 328411 := bstep (se 1 (by rfl) ⟨246308, by rfl⟩ : syracuseStep 328411 = 492617) B492617
theorem B492281 : Blo 327838 492281 := bstep (se 2 (by rfl) ⟨184605, by rfl⟩ : syracuseStep 492281 = 369211) B369211
theorem B836345 : Blo 327838 836345 := bstep (se 2 (by rfl) ⟨313629, by rfl⟩ : syracuseStep 836345 = 627259) B627259
theorem B328487 : Blo 327838 328487 := bstep (se 1 (by rfl) ⟨246365, by rfl⟩ : syracuseStep 328487 = 492731) B492731
theorem B4760369 : Blo 327838 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B328527 : Blo 327838 328527 := bstep (se 1 (by rfl) ⟨246395, by rfl⟩ : syracuseStep 328527 = 492791) B492791
theorem B1106783 : Blo 327838 1106783 := bstep (se 1 (by rfl) ⟨830087, by rfl⟩ : syracuseStep 1106783 = 1660175) B1660175
theorem B738143 : Blo 327838 738143 := bstep (se 1 (by rfl) ⟨553607, by rfl⟩ : syracuseStep 738143 = 1107215) B1107215
theorem B492383 : Blo 327838 492383 := bstep (se 1 (by rfl) ⟨369287, by rfl⟩ : syracuseStep 492383 = 738575) B738575
theorem B328543 : Blo 327838 328543 := bstep (se 1 (by rfl) ⟨246407, by rfl⟩ : syracuseStep 328543 = 492815) B492815
theorem B492395 : Blo 327838 492395 := bstep (se 1 (by rfl) ⟨369296, by rfl⟩ : syracuseStep 492395 = 738593) B738593
theorem B1057643 : Blo 327838 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B328571 : Blo 327838 328571 := bstep (se 1 (by rfl) ⟨246428, by rfl⟩ : syracuseStep 328571 = 492857) B492857
theorem B1254305 : Blo 327838 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B328623 : Blo 327838 328623 := bstep (se 1 (by rfl) ⟨246467, by rfl⟩ : syracuseStep 328623 = 492935) B492935
theorem B2106287 : Blo 327838 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B836527 : Blo 327838 836527 := bstep (se 1 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 836527 = 1254791) B1254791
theorem B1336247 : Blo 327838 1336247 := bstep (se 1 (by rfl) ⟨1002185, by rfl⟩ : syracuseStep 1336247 = 2004371) B2004371
theorem B328647 : Blo 327838 328647 := bstep (se 1 (by rfl) ⟨246485, by rfl⟩ : syracuseStep 328647 = 492971) B492971
theorem B328667 : Blo 327838 328667 := bstep (se 1 (by rfl) ⟨246500, by rfl⟩ : syracuseStep 328667 = 493001) B493001
theorem B1106945 : Blo 327838 1106945 := bstep (se 2 (by rfl) ⟨415104, by rfl⟩ : syracuseStep 1106945 = 830209) B830209
theorem B738323 : Blo 327838 738323 := bstep (se 1 (by rfl) ⟨553742, by rfl⟩ : syracuseStep 738323 = 1107485) B1107485
theorem B328743 : Blo 327838 328743 := bstep (se 1 (by rfl) ⟨246557, by rfl⟩ : syracuseStep 328743 = 493115) B493115
theorem B558137 : Blo 327838 558137 := bstep (se 2 (by rfl) ⟨209301, by rfl⟩ : syracuseStep 558137 = 418603) B418603
theorem B492623 : Blo 327838 492623 := bstep (se 1 (by rfl) ⟨369467, by rfl⟩ : syracuseStep 492623 = 738935) B738935
theorem B328783 : Blo 327838 328783 := bstep (se 1 (by rfl) ⟨246587, by rfl⟩ : syracuseStep 328783 = 493175) B493175
theorem B328799 : Blo 327838 328799 := bstep (se 1 (by rfl) ⟨246599, by rfl⟩ : syracuseStep 328799 = 493199) B493199
theorem B623713 : Blo 327838 623713 := bstep (se 2 (by rfl) ⟨233892, by rfl⟩ : syracuseStep 623713 = 467785) B467785
theorem B369787 : Blo 327838 369787 := bstep (se 1 (by rfl) ⟨277340, by rfl⟩ : syracuseStep 369787 = 554681) B554681
theorem B328827 : Blo 327838 328827 := bstep (se 1 (by rfl) ⟨246620, by rfl⟩ : syracuseStep 328827 = 493241) B493241
theorem B328879 : Blo 327838 328879 := bstep (se 1 (by rfl) ⟨246659, by rfl⟩ : syracuseStep 328879 = 493319) B493319
theorem B492743 : Blo 327838 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B328903 : Blo 327838 328903 := bstep (se 1 (by rfl) ⟨246677, by rfl⟩ : syracuseStep 328903 = 493355) B493355
theorem B328923 : Blo 327838 328923 := bstep (se 1 (by rfl) ⟨246692, by rfl⟩ : syracuseStep 328923 = 493385) B493385
theorem B3097871 : Blo 327838 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B328999 : Blo 327838 328999 := bstep (se 1 (by rfl) ⟨246749, by rfl⟩ : syracuseStep 328999 = 493499) B493499
theorem B329039 : Blo 327838 329039 := bstep (se 1 (by rfl) ⟨246779, by rfl⟩ : syracuseStep 329039 = 493559) B493559
theorem B329055 : Blo 327838 329055 := bstep (se 1 (by rfl) ⟨246791, by rfl⟩ : syracuseStep 329055 = 493583) B493583
theorem B738665 : Blo 327838 738665 := bstep (se 2 (by rfl) ⟨276999, by rfl⟩ : syracuseStep 738665 = 553999) B553999
theorem B492905 : Blo 327838 492905 := bstep (se 2 (by rfl) ⟨184839, by rfl⟩ : syracuseStep 492905 = 369679) B369679
theorem B1254761 : Blo 327838 1254761 := bstep (se 2 (by rfl) ⟨470535, by rfl⟩ : syracuseStep 1254761 = 941071) B941071
theorem B2106749 : Blo 327838 2106749 := bstep (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) B790031
theorem B329083 : Blo 327838 329083 := bstep (se 1 (by rfl) ⟨246812, by rfl⟩ : syracuseStep 329083 = 493625) B493625
theorem B935297 : Blo 327838 935297 := bstep (se 2 (by rfl) ⟨350736, by rfl⟩ : syracuseStep 935297 = 701473) B701473
theorem B1860989 : Blo 327838 1860989 := bstep (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) B697871
theorem B2499983 : Blo 327838 2499983 := bstep (se 1 (by rfl) ⟨1874987, by rfl⟩ : syracuseStep 2499983 = 3749975) B3749975
theorem B6768035 : Blo 327838 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B329135 : Blo 327838 329135 := bstep (se 1 (by rfl) ⟨246851, by rfl⟩ : syracuseStep 329135 = 493703) B493703
theorem B492983 : Blo 327838 492983 := bstep (se 1 (by rfl) ⟨369737, by rfl⟩ : syracuseStep 492983 = 739475) B739475
theorem B329159 : Blo 327838 329159 := bstep (se 1 (by rfl) ⟨246869, by rfl⟩ : syracuseStep 329159 = 493739) B493739
theorem B1672649 : Blo 327838 1672649 := bstep (se 2 (by rfl) ⟨627243, by rfl⟩ : syracuseStep 1672649 = 1254487) B1254487
theorem B493019 : Blo 327838 493019 := bstep (se 1 (by rfl) ⟨369764, by rfl⟩ : syracuseStep 493019 = 739529) B739529
theorem B329179 : Blo 327838 329179 := bstep (se 1 (by rfl) ⟨246884, by rfl⟩ : syracuseStep 329179 = 493769) B493769
theorem B329255 : Blo 327838 329255 := bstep (se 1 (by rfl) ⟨246941, by rfl⟩ : syracuseStep 329255 = 493883) B493883
theorem B370255 : Blo 327838 370255 := bstep (se 1 (by rfl) ⟨277691, by rfl⟩ : syracuseStep 370255 = 555383) B555383
theorem B329295 : Blo 327838 329295 := bstep (se 1 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 329295 = 493943) B493943
theorem B329311 : Blo 327838 329311 := bstep (se 1 (by rfl) ⟨246983, by rfl⟩ : syracuseStep 329311 = 493967) B493967
theorem B329339 : Blo 327838 329339 := bstep (se 1 (by rfl) ⟨247004, by rfl⟩ : syracuseStep 329339 = 494009) B494009
theorem B329391 : Blo 327838 329391 := bstep (se 1 (by rfl) ⟨247043, by rfl⟩ : syracuseStep 329391 = 494087) B494087
theorem B1664711 : Blo 327838 1664711 := bstep (se 1 (by rfl) ⟨1248533, by rfl⟩ : syracuseStep 1664711 = 2497067) B2497067
theorem B468679 : Blo 327838 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B329415 : Blo 327838 329415 := bstep (se 1 (by rfl) ⟨247061, by rfl⟩ : syracuseStep 329415 = 494123) B494123
theorem B329435 : Blo 327838 329435 := bstep (se 1 (by rfl) ⟨247076, by rfl⟩ : syracuseStep 329435 = 494153) B494153
theorem B3155705 : Blo 327838 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B329511 : Blo 327838 329511 := bstep (se 1 (by rfl) ⟨247133, by rfl⟩ : syracuseStep 329511 = 494267) B494267
theorem B1107755 : Blo 327838 1107755 := bstep (se 1 (by rfl) ⟨830816, by rfl⟩ : syracuseStep 1107755 = 1661633) B1661633
theorem B886601 : Blo 327838 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B329551 : Blo 327838 329551 := bstep (se 1 (by rfl) ⟨247163, by rfl⟩ : syracuseStep 329551 = 494327) B494327
theorem B329567 : Blo 327838 329567 := bstep (se 1 (by rfl) ⟨247175, by rfl⟩ : syracuseStep 329567 = 494351) B494351
theorem B1255277 : Blo 327838 1255277 := bstep (se 3 (by rfl) ⟨235364, by rfl⟩ : syracuseStep 1255277 = 470729) B470729
theorem B329595 : Blo 327838 329595 := bstep (se 1 (by rfl) ⟨247196, by rfl⟩ : syracuseStep 329595 = 494393) B494393
theorem B952225 : Blo 327838 952225 := bstep (se 2 (by rfl) ⟨357084, by rfl⟩ : syracuseStep 952225 = 714169) B714169
theorem B493487 : Blo 327838 493487 := bstep (se 1 (by rfl) ⟨370115, by rfl⟩ : syracuseStep 493487 = 740231) B740231
theorem B329647 : Blo 327838 329647 := bstep (se 1 (by rfl) ⟨247235, by rfl⟩ : syracuseStep 329647 = 494471) B494471
theorem B739259 : Blo 327838 739259 := bstep (se 1 (by rfl) ⟨554444, by rfl⟩ : syracuseStep 739259 = 1108889) B1108889
theorem B2508731 : Blo 327838 2508731 := bstep (se 1 (by rfl) ⟨1881548, by rfl⟩ : syracuseStep 2508731 = 3763097) B3763097
theorem B329671 : Blo 327838 329671 := bstep (se 1 (by rfl) ⟨247253, by rfl⟩ : syracuseStep 329671 = 494507) B494507
theorem B370651 : Blo 327838 370651 := bstep (se 1 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 370651 = 555977) B555977
theorem B329691 : Blo 327838 329691 := bstep (se 1 (by rfl) ⟨247268, by rfl⟩ : syracuseStep 329691 = 494537) B494537
theorem B624647 : Blo 327838 624647 := bstep (se 1 (by rfl) ⟨468485, by rfl⟩ : syracuseStep 624647 = 936971) B936971
theorem B493577 : Blo 327838 493577 := bstep (se 2 (by rfl) ⟨185091, by rfl⟩ : syracuseStep 493577 = 370183) B370183
theorem B1337363 : Blo 327838 1337363 := bstep (se 1 (by rfl) ⟨1003022, by rfl⟩ : syracuseStep 1337363 = 2006045) B2006045
theorem B1116179 : Blo 327838 1116179 := bstep (se 1 (by rfl) ⟨837134, by rfl⟩ : syracuseStep 1116179 = 1674269) B1674269
theorem B493607 : Blo 327838 493607 := bstep (se 1 (by rfl) ⟨370205, by rfl⟩ : syracuseStep 493607 = 740411) B740411
theorem B329767 : Blo 327838 329767 := bstep (se 1 (by rfl) ⟨247325, by rfl⟩ : syracuseStep 329767 = 494651) B494651
theorem B1108025 : Blo 327838 1108025 := bstep (se 2 (by rfl) ⟨415509, by rfl⟩ : syracuseStep 1108025 = 831019) B831019
theorem B739385 : Blo 327838 739385 := bstep (se 2 (by rfl) ⟨277269, by rfl⟩ : syracuseStep 739385 = 554539) B554539
theorem B329807 : Blo 327838 329807 := bstep (se 1 (by rfl) ⟨247355, by rfl⟩ : syracuseStep 329807 = 494711) B494711
theorem B1673297 : Blo 327838 1673297 := bstep (se 2 (by rfl) ⟨627486, by rfl⟩ : syracuseStep 1673297 = 1254973) B1254973
theorem B329823 : Blo 327838 329823 := bstep (se 1 (by rfl) ⟨247367, by rfl⟩ : syracuseStep 329823 = 494735) B494735
theorem B493691 : Blo 327838 493691 := bstep (se 1 (by rfl) ⟨370268, by rfl⟩ : syracuseStep 493691 = 740537) B740537
theorem B329851 : Blo 327838 329851 := bstep (se 1 (by rfl) ⟨247388, by rfl⟩ : syracuseStep 329851 = 494777) B494777
theorem B1058987 : Blo 327838 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B329903 : Blo 327838 329903 := bstep (se 1 (by rfl) ⟨247427, by rfl⟩ : syracuseStep 329903 = 494855) B494855
theorem B1181891 : Blo 327838 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B329927 : Blo 327838 329927 := bstep (se 1 (by rfl) ⟨247445, by rfl⟩ : syracuseStep 329927 = 494891) B494891
theorem B329947 : Blo 327838 329947 := bstep (se 1 (by rfl) ⟨247460, by rfl⟩ : syracuseStep 329947 = 494921) B494921
theorem B4204781 : Blo 327838 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B493817 : Blo 327838 493817 := bstep (se 2 (by rfl) ⟨185181, by rfl⟩ : syracuseStep 493817 = 370363) B370363
theorem B330023 : Blo 327838 330023 := bstep (se 1 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 330023 = 495035) B495035
theorem B330063 : Blo 327838 330063 := bstep (se 1 (by rfl) ⟨247547, by rfl⟩ : syracuseStep 330063 = 495095) B495095
theorem B493919 : Blo 327838 493919 := bstep (se 1 (by rfl) ⟨370439, by rfl⟩ : syracuseStep 493919 = 740879) B740879
theorem B330079 : Blo 327838 330079 := bstep (se 1 (by rfl) ⟨247559, by rfl⟩ : syracuseStep 330079 = 495119) B495119
theorem B493931 : Blo 327838 493931 := bstep (se 1 (by rfl) ⟨370448, by rfl⟩ : syracuseStep 493931 = 740897) B740897
theorem B330107 : Blo 327838 330107 := bstep (se 1 (by rfl) ⟨247580, by rfl⟩ : syracuseStep 330107 = 495161) B495161
theorem B1108349 : Blo 327838 1108349 := bstep (se 3 (by rfl) ⟨207815, by rfl⟩ : syracuseStep 1108349 = 415631) B415631
theorem B739727 : Blo 327838 739727 := bstep (se 1 (by rfl) ⟨554795, by rfl⟩ : syracuseStep 739727 = 1109591) B1109591
theorem B371119 : Blo 327838 371119 := bstep (se 1 (by rfl) ⟨278339, by rfl⟩ : syracuseStep 371119 = 556679) B556679
theorem B330159 : Blo 327838 330159 := bstep (se 1 (by rfl) ⟨247619, by rfl⟩ : syracuseStep 330159 = 495239) B495239
theorem B330183 : Blo 327838 330183 := bstep (se 1 (by rfl) ⟨247637, by rfl⟩ : syracuseStep 330183 = 495275) B495275
theorem B330203 : Blo 327838 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B5342705 : Blo 327838 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B1410547 : Blo 327838 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B666119 : Blo 327838 666119 := bstep (se 1 (by rfl) ⟨499589, by rfl⟩ : syracuseStep 666119 = 999179) B999179
theorem B625171 : Blo 327838 625171 := bstep (se 1 (by rfl) ⟨468878, by rfl⟩ : syracuseStep 625171 = 937757) B937757
theorem B6335009 : Blo 327838 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B330279 : Blo 327838 330279 := bstep (se 1 (by rfl) ⟨247709, by rfl⟩ : syracuseStep 330279 = 495419) B495419
theorem B494159 : Blo 327838 494159 := bstep (se 1 (by rfl) ⟨370619, by rfl⟩ : syracuseStep 494159 = 741239) B741239
theorem B330319 : Blo 327838 330319 := bstep (se 1 (by rfl) ⟨247739, by rfl⟩ : syracuseStep 330319 = 495479) B495479
theorem B330335 : Blo 327838 330335 := bstep (se 1 (by rfl) ⟨247751, by rfl⟩ : syracuseStep 330335 = 495503) B495503
theorem B330363 : Blo 327838 330363 := bstep (se 1 (by rfl) ⟨247772, by rfl⟩ : syracuseStep 330363 = 495545) B495545
theorem B1108619 : Blo 327838 1108619 := bstep (se 1 (by rfl) ⟨831464, by rfl⟩ : syracuseStep 1108619 = 1662929) B1662929
theorem B330415 : Blo 327838 330415 := bstep (se 1 (by rfl) ⟨247811, by rfl⟩ : syracuseStep 330415 = 495623) B495623
theorem B1051325 : Blo 327838 1051325 := bstep (se 3 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 1051325 = 394247) B394247
theorem B494279 : Blo 327838 494279 := bstep (se 1 (by rfl) ⟨370709, by rfl⟩ : syracuseStep 494279 = 741419) B741419
theorem B330439 : Blo 327838 330439 := bstep (se 1 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 330439 = 495659) B495659
theorem B740051 : Blo 327838 740051 := bstep (se 1 (by rfl) ⟨555038, by rfl⟩ : syracuseStep 740051 = 1110077) B1110077
theorem B330459 : Blo 327838 330459 := bstep (se 1 (by rfl) ⟨247844, by rfl⟩ : syracuseStep 330459 = 495689) B495689
theorem B936697 : Blo 327838 936697 := bstep (se 2 (by rfl) ⟨351261, by rfl⟩ : syracuseStep 936697 = 702523) B702523
theorem B330535 : Blo 327838 330535 := bstep (se 1 (by rfl) ⟨247901, by rfl⟩ : syracuseStep 330535 = 495803) B495803
theorem B6007621 : Blo 327838 6007621 := bstep (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) B1126429
theorem B330575 : Blo 327838 330575 := bstep (se 1 (by rfl) ⟨247931, by rfl⟩ : syracuseStep 330575 = 495863) B495863
theorem B371551 : Blo 327838 371551 := bstep (se 1 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 371551 = 557327) B557327
theorem B330591 : Blo 327838 330591 := bstep (se 1 (by rfl) ⟨247943, by rfl⟩ : syracuseStep 330591 = 495887) B495887
theorem B494441 : Blo 327838 494441 := bstep (se 2 (by rfl) ⟨185415, by rfl⟩ : syracuseStep 494441 = 370831) B370831
theorem B330619 : Blo 327838 330619 := bstep (se 1 (by rfl) ⟨247964, by rfl⟩ : syracuseStep 330619 = 495929) B495929
theorem B836993 : Blo 327838 836993 := bstep (se 2 (by rfl) ⟨313872, by rfl⟩ : syracuseStep 836993 = 627745) B627745
theorem B330671 : Blo 327838 330671 := bstep (se 1 (by rfl) ⟨248003, by rfl⟩ : syracuseStep 330671 = 496007) B496007
theorem B1870775 : Blo 327838 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B1649591 : Blo 327838 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B494519 : Blo 327838 494519 := bstep (se 1 (by rfl) ⟨370889, by rfl⟩ : syracuseStep 494519 = 741779) B741779
theorem B330695 : Blo 327838 330695 := bstep (se 1 (by rfl) ⟨248021, by rfl⟩ : syracuseStep 330695 = 496043) B496043
theorem B494555 : Blo 327838 494555 := bstep (se 1 (by rfl) ⟨370916, by rfl⟩ : syracuseStep 494555 = 741833) B741833
theorem B330715 : Blo 327838 330715 := bstep (se 1 (by rfl) ⟨248036, by rfl⟩ : syracuseStep 330715 = 496073) B496073
theorem B2108389 : Blo 327838 2108389 := bstep (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) B395323
theorem B830483 : Blo 327838 830483 := bstep (se 1 (by rfl) ⟨622862, by rfl⟩ : syracuseStep 830483 = 1245725) B1245725
theorem B7588981 : Blo 327838 7588981 := bstep (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) B711467
theorem B371911 : Blo 327838 371911 := bstep (se 1 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 371911 = 557867) B557867
theorem B1248641 : Blo 327838 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B1248655 : Blo 327838 1248655 := bstep (se 1 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 1248655 = 1872983) B1872983
theorem B495023 : Blo 327838 495023 := bstep (se 1 (by rfl) ⟨371267, by rfl⟩ : syracuseStep 495023 = 742535) B742535
theorem B790003 : Blo 327838 790003 := bstep (se 1 (by rfl) ⟨592502, by rfl⟩ : syracuseStep 790003 = 1185005) B1185005
theorem B495113 : Blo 327838 495113 := bstep (se 2 (by rfl) ⟨185667, by rfl⟩ : syracuseStep 495113 = 371335) B371335
theorem B1338889 : Blo 327838 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B1109537 : Blo 327838 1109537 := bstep (se 2 (by rfl) ⟨416076, by rfl⟩ : syracuseStep 1109537 = 832153) B832153
theorem B495143 : Blo 327838 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B27053669 : Blo 327838 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B740987 : Blo 327838 740987 := bstep (se 1 (by rfl) ⟨555740, by rfl⟩ : syracuseStep 740987 = 1111481) B1111481
theorem B495227 : Blo 327838 495227 := bstep (se 1 (by rfl) ⟨371420, by rfl⟩ : syracuseStep 495227 = 742841) B742841
theorem B2715275 : Blo 327838 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B4009661 : Blo 327838 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B2494151 : Blo 327838 2494151 := bstep (se 1 (by rfl) ⟨1870613, by rfl⟩ : syracuseStep 2494151 = 3741227) B3741227
theorem B2993885 : Blo 327838 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B1109753 : Blo 327838 1109753 := bstep (se 2 (by rfl) ⟨416157, by rfl⟩ : syracuseStep 1109753 = 832315) B832315
theorem B741113 : Blo 327838 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B495353 : Blo 327838 495353 := bstep (se 2 (by rfl) ⟨185757, by rfl⟩ : syracuseStep 495353 = 371515) B371515
theorem B1126187 : Blo 327838 1126187 := bstep (se 1 (by rfl) ⟨844640, by rfl⟩ : syracuseStep 1126187 = 1689281) B1689281
theorem B495455 : Blo 327838 495455 := bstep (se 1 (by rfl) ⟨371591, by rfl⟩ : syracuseStep 495455 = 743183) B743183
theorem B495467 : Blo 327838 495467 := bstep (se 1 (by rfl) ⟨371600, by rfl⟩ : syracuseStep 495467 = 743201) B743201
theorem B1183663 : Blo 327838 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B683959 : Blo 327838 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B593851 : Blo 327838 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B1110023 : Blo 327838 1110023 := bstep (se 1 (by rfl) ⟨832517, by rfl⟩ : syracuseStep 1110023 = 1665035) B1665035
theorem B741383 : Blo 327838 741383 := bstep (se 1 (by rfl) ⟨556037, by rfl⟩ : syracuseStep 741383 = 1112075) B1112075
theorem B741455 : Blo 327838 741455 := bstep (se 1 (by rfl) ⟨556091, by rfl⟩ : syracuseStep 741455 = 1112183) B1112183
theorem B495695 : Blo 327838 495695 := bstep (se 1 (by rfl) ⟨371771, by rfl⟩ : syracuseStep 495695 = 743543) B743543
theorem B1110131 : Blo 327838 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B5337251 : Blo 327838 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B938155 : Blo 327838 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B3575987 : Blo 327838 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B495815 : Blo 327838 495815 := bstep (se 1 (by rfl) ⟨371861, by rfl⟩ : syracuseStep 495815 = 743723) B743723
theorem B1052939 : Blo 327838 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B3764555 : Blo 327838 3764555 := bstep (se 1 (by rfl) ⟨2823416, by rfl⟩ : syracuseStep 3764555 = 5646833) B5646833
theorem B1872233 : Blo 327838 1872233 := bstep (se 2 (by rfl) ⟨702087, by rfl⟩ : syracuseStep 1872233 = 1404175) B1404175
theorem B495977 : Blo 327838 495977 := bstep (se 2 (by rfl) ⟨185991, by rfl⟩ : syracuseStep 495977 = 371983) B371983
theorem B1110401 : Blo 327838 1110401 := bstep (se 2 (by rfl) ⟨416400, by rfl⟩ : syracuseStep 1110401 = 832801) B832801
theorem B496055 : Blo 327838 496055 := bstep (se 1 (by rfl) ⟨372041, by rfl⟩ : syracuseStep 496055 = 744083) B744083
theorem B528827 : Blo 327838 528827 := bstep (se 1 (by rfl) ⟨396620, by rfl⟩ : syracuseStep 528827 = 793241) B793241
theorem B741851 : Blo 327838 741851 := bstep (se 1 (by rfl) ⟨556388, by rfl⟩ : syracuseStep 741851 = 1112777) B1112777
theorem B496091 : Blo 327838 496091 := bstep (se 1 (by rfl) ⟨372068, by rfl⟩ : syracuseStep 496091 = 744137) B744137
theorem B1405421 : Blo 327838 1405421 := bstep (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) B527033
theorem B528905 : Blo 327838 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B1200779 : Blo 327838 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B1249931 : Blo 327838 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B2659027 : Blo 327838 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B627563 : Blo 327838 627563 := bstep (se 1 (by rfl) ⟨470672, by rfl⟩ : syracuseStep 627563 = 941345) B941345
theorem B553871 : Blo 327838 553871 := bstep (se 1 (by rfl) ⟨415403, by rfl⟩ : syracuseStep 553871 = 830807) B830807
theorem B742319 : Blo 327838 742319 := bstep (se 1 (by rfl) ⟨556739, by rfl⟩ : syracuseStep 742319 = 1113479) B1113479
theorem B578491 : Blo 327838 578491 := bstep (se 1 (by rfl) ⟨433868, by rfl⟩ : syracuseStep 578491 = 867737) B867737
theorem B1807379 : Blo 327838 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B3150899 : Blo 327838 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B554107 : Blo 327838 554107 := bstep (se 1 (by rfl) ⟨415580, by rfl⟩ : syracuseStep 554107 = 831161) B831161
theorem B668795 : Blo 327838 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B1406105 : Blo 327838 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B2225323 : Blo 327838 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B1111211 : Blo 327838 1111211 := bstep (se 1 (by rfl) ⟨833408, by rfl⟩ : syracuseStep 1111211 = 1666817) B1666817
theorem B742571 : Blo 327838 742571 := bstep (se 1 (by rfl) ⟨556928, by rfl⟩ : syracuseStep 742571 = 1113857) B1113857
theorem B4568309 : Blo 327838 4568309 := bstep (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) B428279
theorem B939545 : Blo 327838 939545 := bstep (se 2 (by rfl) ⟨352329, by rfl⟩ : syracuseStep 939545 = 704659) B704659
theorem B1111751 : Blo 327838 1111751 := bstep (se 1 (by rfl) ⟨833813, by rfl⟩ : syracuseStep 1111751 = 1667627) B1667627
theorem B677575 : Blo 327838 677575 := bstep (se 1 (by rfl) ⟨508181, by rfl⟩ : syracuseStep 677575 = 1016363) B1016363
theorem B743111 : Blo 327838 743111 := bstep (se 1 (by rfl) ⟨557333, by rfl⟩ : syracuseStep 743111 = 1114667) B1114667
theorem B890579 : Blo 327838 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B554971 : Blo 327838 554971 := bstep (se 1 (by rfl) ⟨416228, by rfl⟩ : syracuseStep 554971 = 832457) B832457
theorem B1128455 : Blo 327838 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B415783 : Blo 327838 415783 := bstep (se 1 (by rfl) ⟨311837, by rfl⟩ : syracuseStep 415783 = 623675) B623675
theorem B1660985 : Blo 327838 1660985 := bstep (se 2 (by rfl) ⟨622869, by rfl⟩ : syracuseStep 1660985 = 1245739) B1245739
theorem B416107 : Blo 327838 416107 := bstep (se 1 (by rfl) ⟨312080, by rfl⟩ : syracuseStep 416107 = 624161) B624161
theorem B833935 : Blo 327838 833935 := bstep (se 1 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 833935 = 1250903) B1250903
theorem B2857369 : Blo 327838 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B5355929 : Blo 327838 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B1874441 : Blo 327838 1874441 := bstep (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) B1405831
theorem B1333793 : Blo 327838 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B1112615 : Blo 327838 1112615 := bstep (se 1 (by rfl) ⟨834461, by rfl⟩ : syracuseStep 1112615 = 1668923) B1668923
theorem B743975 : Blo 327838 743975 := bstep (se 1 (by rfl) ⟨557981, by rfl⟩ : syracuseStep 743975 = 1115963) B1115963
theorem B416335 : Blo 327838 416335 := bstep (se 1 (by rfl) ⟨312251, by rfl⟩ : syracuseStep 416335 = 624503) B624503
theorem B555599 : Blo 327838 555599 := bstep (se 1 (by rfl) ⟨416699, by rfl⟩ : syracuseStep 555599 = 833399) B833399
theorem B1112723 : Blo 327838 1112723 := bstep (se 1 (by rfl) ⟨834542, by rfl⟩ : syracuseStep 1112723 = 1669085) B1669085
theorem B7101107 : Blo 327838 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B834259 : Blo 327838 834259 := bstep (se 1 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 834259 = 1251389) B1251389
theorem B12229465 : Blo 327838 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B1776491 : Blo 327838 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B1112939 : Blo 327838 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B418223 : Blo 327838 418223 := bstep (se 1 (by rfl) ⟨313667, by rfl⟩ : syracuseStep 418223 = 627335) B627335
theorem B1112993 : Blo 327838 1112993 := bstep (se 2 (by rfl) ⟨417372, by rfl⟩ : syracuseStep 1112993 = 834745) B834745
theorem B711607 : Blo 327838 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B564187 : Blo 327838 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B2104339 : Blo 327838 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B965711 : Blo 327838 965711 := bstep (se 1 (by rfl) ⟨724283, by rfl⟩ : syracuseStep 965711 = 1448567) B1448567
theorem B793847 : Blo 327838 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B2243965 : Blo 327838 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B1867151 : Blo 327838 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B1670543 : Blo 327838 1670543 := bstep (se 1 (by rfl) ⟨1252907, by rfl⟩ : syracuseStep 1670543 = 2505815) B2505815
theorem B556463 : Blo 327838 556463 := bstep (se 1 (by rfl) ⟨417347, by rfl⟩ : syracuseStep 556463 = 834695) B834695
theorem B1113587 : Blo 327838 1113587 := bstep (se 1 (by rfl) ⟨835190, by rfl⟩ : syracuseStep 1113587 = 1670381) B1670381
theorem B704009 : Blo 327838 704009 := bstep (se 2 (by rfl) ⟨264003, by rfl⟩ : syracuseStep 704009 = 528007) B528007
theorem B2506301 : Blo 327838 2506301 := bstep (se 3 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 2506301 = 939863) B939863
theorem B417403 : Blo 327838 417403 := bstep (se 1 (by rfl) ⟨313052, by rfl⟩ : syracuseStep 417403 = 626105) B626105
theorem B679547 : Blo 327838 679547 := bstep (se 1 (by rfl) ⟨509660, by rfl⟩ : syracuseStep 679547 = 1019321) B1019321
theorem B4202117 : Blo 327838 4202117 := bstep (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) B787897
theorem B835211 : Blo 327838 835211 := bstep (se 1 (by rfl) ⟨626408, by rfl⟩ : syracuseStep 835211 = 1252817) B1252817
theorem B704351 : Blo 327838 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B417631 : Blo 327838 417631 := bstep (se 1 (by rfl) ⟨313223, by rfl⟩ : syracuseStep 417631 = 626447) B626447
theorem B556895 : Blo 327838 556895 := bstep (se 1 (by rfl) ⟨417671, by rfl⟩ : syracuseStep 556895 = 835343) B835343
theorem B1253303 : Blo 327838 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B5054393 : Blo 327838 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1875899 : Blo 327838 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B2383991 : Blo 327838 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B1441963 : Blo 327838 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B327967 : Blo 327838 327967 := bstep (se 1 (by rfl) ⟨245975, by rfl⟩ : syracuseStep 327967 = 491951) B491951
theorem B1802569 : Blo 327838 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B491867 : Blo 327838 491867 := bstep (se 1 (by rfl) ⟨368900, by rfl⟩ : syracuseStep 491867 = 737801) B737801
theorem B328027 : Blo 327838 328027 := bstep (se 1 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 328027 = 492041) B492041
theorem B1671515 : Blo 327838 1671515 := bstep (se 1 (by rfl) ⟨1253636, by rfl⟩ : syracuseStep 1671515 = 2507273) B2507273
theorem B352603 : Blo 327838 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B328047 : Blo 327838 328047 := bstep (se 1 (by rfl) ⟨246035, by rfl⟩ : syracuseStep 328047 = 492071) B492071
theorem B328103 : Blo 327838 328103 := bstep (se 1 (by rfl) ⟨246077, by rfl⟩ : syracuseStep 328103 = 492155) B492155
theorem B737711 : Blo 327838 737711 := bstep (se 1 (by rfl) ⟨553283, by rfl⟩ : syracuseStep 737711 = 1106567) B1106567
theorem B737747 : Blo 327838 737747 := bstep (se 1 (by rfl) ⟨553310, by rfl⟩ : syracuseStep 737747 = 1106621) B1106621
theorem B1425883 : Blo 327838 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B328187 : Blo 327838 328187 := bstep (se 1 (by rfl) ⟨246140, by rfl⟩ : syracuseStep 328187 = 492281) B492281
theorem B557563 : Blo 327838 557563 := bstep (se 1 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 557563 = 836345) B836345
theorem B3809825 : Blo 327838 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B737855 : Blo 327838 737855 := bstep (se 1 (by rfl) ⟨553391, by rfl⟩ : syracuseStep 737855 = 1106783) B1106783
theorem B492095 : Blo 327838 492095 := bstep (se 1 (by rfl) ⟨369071, by rfl⟩ : syracuseStep 492095 = 738143) B738143
theorem B328255 : Blo 327838 328255 := bstep (se 1 (by rfl) ⟨246191, by rfl⟩ : syracuseStep 328255 = 492383) B492383
theorem B328263 : Blo 327838 328263 := bstep (se 1 (by rfl) ⟨246197, by rfl⟩ : syracuseStep 328263 = 492395) B492395
theorem B705095 : Blo 327838 705095 := bstep (se 1 (by rfl) ⟨528821, by rfl⟩ : syracuseStep 705095 = 1057643) B1057643
theorem B418375 : Blo 327838 418375 := bstep (se 1 (by rfl) ⟨313781, by rfl⟩ : syracuseStep 418375 = 627563) B627563
theorem B369247 : Blo 327838 369247 := bstep (se 1 (by rfl) ⟨276935, by rfl⟩ : syracuseStep 369247 = 553871) B553871
theorem B836203 : Blo 327838 836203 := bstep (se 1 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 836203 = 1254305) B1254305
theorem B737963 : Blo 327838 737963 := bstep (se 1 (by rfl) ⟨553472, by rfl⟩ : syracuseStep 737963 = 1106945) B1106945
theorem B492215 : Blo 327838 492215 := bstep (se 1 (by rfl) ⟨369161, by rfl⟩ : syracuseStep 492215 = 738323) B738323
theorem B1204919 : Blo 327838 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B328415 : Blo 327838 328415 := bstep (se 1 (by rfl) ⟨246311, by rfl⟩ : syracuseStep 328415 = 492623) B492623
theorem B4260601 : Blo 327838 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B328495 : Blo 327838 328495 := bstep (se 1 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 328495 = 492743) B492743
theorem B492443 : Blo 327838 492443 := bstep (se 1 (by rfl) ⟨369332, by rfl⟩ : syracuseStep 492443 = 738665) B738665
theorem B328603 : Blo 327838 328603 := bstep (se 1 (by rfl) ⟨246452, by rfl⟩ : syracuseStep 328603 = 492905) B492905
theorem B836507 : Blo 327838 836507 := bstep (se 1 (by rfl) ⟨627380, by rfl⟩ : syracuseStep 836507 = 1254761) B1254761
theorem B623531 : Blo 327838 623531 := bstep (se 1 (by rfl) ⟨467648, by rfl⟩ : syracuseStep 623531 = 935297) B935297
theorem B557995 : Blo 327838 557995 := bstep (se 1 (by rfl) ⟨418496, by rfl⟩ : syracuseStep 557995 = 836993) B836993
theorem B328655 : Blo 327838 328655 := bstep (se 1 (by rfl) ⟨246491, by rfl⟩ : syracuseStep 328655 = 492983) B492983
theorem B1115099 : Blo 327838 1115099 := bstep (se 1 (by rfl) ⟨836324, by rfl⟩ : syracuseStep 1115099 = 1672649) B1672649
theorem B328679 : Blo 327838 328679 := bstep (se 1 (by rfl) ⟨246509, by rfl⟩ : syracuseStep 328679 = 493019) B493019
theorem B1115261 : Blo 327838 1115261 := bstep (se 3 (by rfl) ⟨209111, by rfl⟩ : syracuseStep 1115261 = 418223) B418223
theorem B1410205 : Blo 327838 1410205 := bstep (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) B528827
theorem B738503 : Blo 327838 738503 := bstep (se 1 (by rfl) ⟨553877, by rfl⟩ : syracuseStep 738503 = 1107755) B1107755
theorem B591067 : Blo 327838 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B1115369 : Blo 327838 1115369 := bstep (se 2 (by rfl) ⟨418263, by rfl⟩ : syracuseStep 1115369 = 836527) B836527
theorem B836851 : Blo 327838 836851 := bstep (se 1 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 836851 = 1255277) B1255277
theorem B328991 : Blo 327838 328991 := bstep (se 1 (by rfl) ⟨246743, by rfl⟩ : syracuseStep 328991 = 493487) B493487
theorem B492839 : Blo 327838 492839 := bstep (se 1 (by rfl) ⟨369629, by rfl⟩ : syracuseStep 492839 = 739259) B739259
theorem B1672487 : Blo 327838 1672487 := bstep (se 1 (by rfl) ⟨1254365, by rfl⟩ : syracuseStep 1672487 = 2508731) B2508731
theorem B2811185 : Blo 327838 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B329051 : Blo 327838 329051 := bstep (se 1 (by rfl) ⟨246788, by rfl⟩ : syracuseStep 329051 = 493577) B493577
theorem B1877357 : Blo 327838 1877357 := bstep (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) B704009
theorem B329071 : Blo 327838 329071 := bstep (se 1 (by rfl) ⟨246803, by rfl⟩ : syracuseStep 329071 = 493607) B493607
theorem B1107323 : Blo 327838 1107323 := bstep (se 1 (by rfl) ⟨830492, by rfl⟩ : syracuseStep 1107323 = 1660985) B1660985
theorem B738683 : Blo 327838 738683 := bstep (se 1 (by rfl) ⟨554012, by rfl⟩ : syracuseStep 738683 = 1108025) B1108025
theorem B492923 : Blo 327838 492923 := bstep (se 1 (by rfl) ⟨369692, by rfl⟩ : syracuseStep 492923 = 739385) B739385
theorem B1115531 : Blo 327838 1115531 := bstep (se 1 (by rfl) ⟨836648, by rfl⟩ : syracuseStep 1115531 = 1673297) B1673297
theorem B329127 : Blo 327838 329127 := bstep (se 1 (by rfl) ⟨246845, by rfl⟩ : syracuseStep 329127 = 493691) B493691
theorem B3556781 : Blo 327838 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B705991 : Blo 327838 705991 := bstep (se 1 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 705991 = 1058987) B1058987
theorem B10118641 : Blo 327838 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B2803187 : Blo 327838 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B738809 : Blo 327838 738809 := bstep (se 2 (by rfl) ⟨277053, by rfl⟩ : syracuseStep 738809 = 554107) B554107
theorem B493049 : Blo 327838 493049 := bstep (se 2 (by rfl) ⟨184893, by rfl⟩ : syracuseStep 493049 = 369787) B369787
theorem B329211 : Blo 327838 329211 := bstep (se 1 (by rfl) ⟨246908, by rfl⟩ : syracuseStep 329211 = 493817) B493817
theorem B329279 : Blo 327838 329279 := bstep (se 1 (by rfl) ⟨246959, by rfl⟩ : syracuseStep 329279 = 493919) B493919
theorem B329287 : Blo 327838 329287 := bstep (se 1 (by rfl) ⟨246965, by rfl⟩ : syracuseStep 329287 = 493931) B493931
theorem B738899 : Blo 327838 738899 := bstep (se 1 (by rfl) ⟨554174, by rfl⟩ : syracuseStep 738899 = 1108349) B1108349
theorem B493151 : Blo 327838 493151 := bstep (se 1 (by rfl) ⟨369863, by rfl⟩ : syracuseStep 493151 = 739727) B739727
theorem B444079 : Blo 327838 444079 := bstep (se 1 (by rfl) ⟨333059, by rfl⟩ : syracuseStep 444079 = 666119) B666119
theorem B370399 : Blo 327838 370399 := bstep (se 1 (by rfl) ⟨277799, by rfl⟩ : syracuseStep 370399 = 555599) B555599
theorem B329439 : Blo 327838 329439 := bstep (se 1 (by rfl) ⟨247079, by rfl⟩ : syracuseStep 329439 = 494159) B494159
theorem B739079 : Blo 327838 739079 := bstep (se 1 (by rfl) ⟨554309, by rfl⟩ : syracuseStep 739079 = 1108619) B1108619
theorem B329519 : Blo 327838 329519 := bstep (se 1 (by rfl) ⟨247139, by rfl⟩ : syracuseStep 329519 = 494279) B494279
theorem B493367 : Blo 327838 493367 := bstep (se 1 (by rfl) ⟨370025, by rfl⟩ : syracuseStep 493367 = 740051) B740051
theorem B2991953 : Blo 327838 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B1664873 : Blo 327838 1664873 := bstep (se 2 (by rfl) ⟨624327, by rfl⟩ : syracuseStep 1664873 = 1248655) B1248655
theorem B329627 : Blo 327838 329627 := bstep (se 1 (by rfl) ⟨247220, by rfl⟩ : syracuseStep 329627 = 494441) B494441
theorem B1247183 : Blo 327838 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B1099727 : Blo 327838 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B329679 : Blo 327838 329679 := bstep (se 1 (by rfl) ⟨247259, by rfl⟩ : syracuseStep 329679 = 494519) B494519
theorem B329703 : Blo 327838 329703 := bstep (se 1 (by rfl) ⟨247277, by rfl⟩ : syracuseStep 329703 = 494555) B494555
theorem B493673 : Blo 327838 493673 := bstep (se 2 (by rfl) ⟨185127, by rfl⟩ : syracuseStep 493673 = 370255) B370255
theorem B624905 : Blo 327838 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B903433 : Blo 327838 903433 := bstep (se 2 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 903433 = 677575) B677575
theorem B370975 : Blo 327838 370975 := bstep (se 1 (by rfl) ⟨278231, by rfl⟩ : syracuseStep 370975 = 556463) B556463
theorem B330015 : Blo 327838 330015 := bstep (se 1 (by rfl) ⟨247511, by rfl⟩ : syracuseStep 330015 = 495023) B495023
theorem B330075 : Blo 327838 330075 := bstep (se 1 (by rfl) ⟨247556, by rfl⟩ : syracuseStep 330075 = 495113) B495113
theorem B739691 : Blo 327838 739691 := bstep (se 1 (by rfl) ⟨554768, by rfl⟩ : syracuseStep 739691 = 1109537) B1109537
theorem B330095 : Blo 327838 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B493991 : Blo 327838 493991 := bstep (se 1 (by rfl) ⟨370493, by rfl⟩ : syracuseStep 493991 = 740987) B740987
theorem B330151 : Blo 327838 330151 := bstep (se 1 (by rfl) ⟨247613, by rfl⟩ : syracuseStep 330151 = 495227) B495227
theorem B453031 : Blo 327838 453031 := bstep (se 1 (by rfl) ⟨339773, by rfl⟩ : syracuseStep 453031 = 679547) B679547
theorem B2673107 : Blo 327838 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B739835 : Blo 327838 739835 := bstep (se 1 (by rfl) ⟨554876, by rfl⟩ : syracuseStep 739835 = 1109753) B1109753
theorem B494075 : Blo 327838 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B330235 : Blo 327838 330235 := bstep (se 1 (by rfl) ⟨247676, by rfl⟩ : syracuseStep 330235 = 495353) B495353
theorem B469567 : Blo 327838 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B371263 : Blo 327838 371263 := bstep (se 1 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 371263 = 556895) B556895
theorem B330303 : Blo 327838 330303 := bstep (se 1 (by rfl) ⟨247727, by rfl⟩ : syracuseStep 330303 = 495455) B495455
theorem B330311 : Blo 327838 330311 := bstep (se 1 (by rfl) ⟨247733, by rfl⟩ : syracuseStep 330311 = 495467) B495467
theorem B911945 : Blo 327838 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B739961 : Blo 327838 739961 := bstep (se 2 (by rfl) ⟨277485, by rfl⟩ : syracuseStep 739961 = 554971) B554971
theorem B494201 : Blo 327838 494201 := bstep (se 2 (by rfl) ⟨185325, by rfl⟩ : syracuseStep 494201 = 370651) B370651
theorem B3369595 : Blo 327838 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B740015 : Blo 327838 740015 := bstep (se 1 (by rfl) ⟨555011, by rfl⟩ : syracuseStep 740015 = 1110023) B1110023
theorem B494255 : Blo 327838 494255 := bstep (se 1 (by rfl) ⟨370691, by rfl⟩ : syracuseStep 494255 = 741383) B741383
theorem B494303 : Blo 327838 494303 := bstep (se 1 (by rfl) ⟨370727, by rfl⟩ : syracuseStep 494303 = 741455) B741455
theorem B330463 : Blo 327838 330463 := bstep (se 1 (by rfl) ⟨247847, by rfl⟩ : syracuseStep 330463 = 495695) B495695
theorem B1108727 : Blo 327838 1108727 := bstep (se 1 (by rfl) ⟨831545, by rfl⟩ : syracuseStep 1108727 = 1663091) B1663091
theorem B740087 : Blo 327838 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B3558167 : Blo 327838 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B330543 : Blo 327838 330543 := bstep (se 1 (by rfl) ⟨247907, by rfl⟩ : syracuseStep 330543 = 495815) B495815
theorem B2509703 : Blo 327838 2509703 := bstep (se 1 (by rfl) ⟨1882277, by rfl⟩ : syracuseStep 2509703 = 3764555) B3764555
theorem B830351 : Blo 327838 830351 := bstep (se 1 (by rfl) ⟨622763, by rfl⟩ : syracuseStep 830351 = 1245527) B1245527
theorem B1248155 : Blo 327838 1248155 := bstep (se 1 (by rfl) ⟨936116, by rfl⟩ : syracuseStep 1248155 = 1872233) B1872233
theorem B330651 : Blo 327838 330651 := bstep (se 1 (by rfl) ⟨247988, by rfl⟩ : syracuseStep 330651 = 495977) B495977
theorem B740267 : Blo 327838 740267 := bstep (se 1 (by rfl) ⟨555200, by rfl⟩ : syracuseStep 740267 = 1110401) B1110401
theorem B330703 : Blo 327838 330703 := bstep (se 1 (by rfl) ⟨248027, by rfl⟩ : syracuseStep 330703 = 496055) B496055
theorem B494567 : Blo 327838 494567 := bstep (se 1 (by rfl) ⟨370925, by rfl⟩ : syracuseStep 494567 = 741851) B741851
theorem B330727 : Blo 327838 330727 := bstep (se 1 (by rfl) ⟨248045, by rfl⟩ : syracuseStep 330727 = 496091) B496091
theorem B936947 : Blo 327838 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B1190899 : Blo 327838 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B3173579 : Blo 327838 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B494825 : Blo 327838 494825 := bstep (se 2 (by rfl) ⟨185559, by rfl⟩ : syracuseStep 494825 = 371119) B371119
theorem B2065247 : Blo 327838 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1404191 : Blo 327838 1404191 := bstep (se 1 (by rfl) ⟨1053143, by rfl⟩ : syracuseStep 1404191 = 2106287) B2106287
theorem B494879 : Blo 327838 494879 := bstep (se 1 (by rfl) ⟨371159, by rfl⟩ : syracuseStep 494879 = 742319) B742319
theorem B2116925 : Blo 327838 2116925 := bstep (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) B793847
theorem B2100599 : Blo 327838 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B372091 : Blo 327838 372091 := bstep (se 1 (by rfl) ⟨279068, by rfl⟩ : syracuseStep 372091 = 558137) B558137
theorem B830857 : Blo 327838 830857 := bstep (se 2 (by rfl) ⟨311571, by rfl⟩ : syracuseStep 830857 = 623143) B623143
theorem B937403 : Blo 327838 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B740807 : Blo 327838 740807 := bstep (se 1 (by rfl) ⟨555605, by rfl⟩ : syracuseStep 740807 = 1111211) B1111211
theorem B495047 : Blo 327838 495047 := bstep (se 1 (by rfl) ⟨371285, by rfl⟩ : syracuseStep 495047 = 742571) B742571
theorem B830969 : Blo 327838 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B1191505 : Blo 327838 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B1404499 : Blo 327838 1404499 := bstep (se 1 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 1404499 = 2106749) B2106749
theorem B1666655 : Blo 327838 1666655 := bstep (se 1 (by rfl) ⟨1249991, by rfl⟩ : syracuseStep 1666655 = 2499983) B2499983
theorem B1248929 : Blo 327838 1248929 := bstep (se 2 (by rfl) ⟨468348, by rfl⟩ : syracuseStep 1248929 = 936697) B936697
theorem B626363 : Blo 327838 626363 := bstep (se 1 (by rfl) ⟨469772, by rfl⟩ : syracuseStep 626363 = 939545) B939545
theorem B14282477 : Blo 327838 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B16305953 : Blo 327838 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B495401 : Blo 327838 495401 := bstep (se 2 (by rfl) ⟨185775, by rfl⟩ : syracuseStep 495401 = 371551) B371551
theorem B1109807 : Blo 327838 1109807 := bstep (se 1 (by rfl) ⟨832355, by rfl⟩ : syracuseStep 1109807 = 1664711) B1664711
theorem B741167 : Blo 327838 741167 := bstep (se 1 (by rfl) ⟨555875, by rfl⟩ : syracuseStep 741167 = 1111751) B1111751
theorem B495407 : Blo 327838 495407 := bstep (se 1 (by rfl) ⟨371555, by rfl⟩ : syracuseStep 495407 = 743111) B743111
theorem B2994029 : Blo 327838 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B2805785 : Blo 327838 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B831617 : Blo 327838 831617 := bstep (se 2 (by rfl) ⟨311856, by rfl⟩ : syracuseStep 831617 = 623713) B623713
theorem B495881 : Blo 327838 495881 := bstep (se 2 (by rfl) ⟨185955, by rfl⟩ : syracuseStep 495881 = 371911) B371911
theorem B1249627 : Blo 327838 1249627 := bstep (se 1 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 1249627 = 1874441) B1874441
theorem B4223339 : Blo 327838 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B741743 : Blo 327838 741743 := bstep (se 1 (by rfl) ⟨556307, by rfl⟩ : syracuseStep 741743 = 1112615) B1112615
theorem B495983 : Blo 327838 495983 := bstep (se 1 (by rfl) ⟨371987, by rfl⟩ : syracuseStep 495983 = 743975) B743975
theorem B741815 : Blo 327838 741815 := bstep (se 1 (by rfl) ⟨556361, by rfl⟩ : syracuseStep 741815 = 1112723) B1112723
theorem B700883 : Blo 327838 700883 := bstep (se 1 (by rfl) ⟨525662, by rfl⟩ : syracuseStep 700883 = 1051325) B1051325
theorem B1184327 : Blo 327838 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B741959 : Blo 327838 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B741995 : Blo 327838 741995 := bstep (se 1 (by rfl) ⟨556496, by rfl⟩ : syracuseStep 741995 = 1112993) B1112993
theorem B1053337 : Blo 327838 1053337 := bstep (se 2 (by rfl) ⟨395001, by rfl⟩ : syracuseStep 1053337 = 790003) B790003
theorem B1880729 : Blo 327838 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B553655 : Blo 327838 553655 := bstep (se 1 (by rfl) ⟨415241, by rfl⟩ : syracuseStep 553655 = 830483) B830483
theorem B643807 : Blo 327838 643807 := bstep (se 1 (by rfl) ⟨482855, by rfl⟩ : syracuseStep 643807 = 965711) B965711
theorem B832427 : Blo 327838 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B3085285 : Blo 327838 3085285 := bstep (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) B578491
theorem B742391 : Blo 327838 742391 := bstep (se 1 (by rfl) ⟨556793, by rfl⟩ : syracuseStep 742391 = 1113587) B1113587
theorem B18035779 : Blo 327838 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B1995923 : Blo 327838 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B750791 : Blo 327838 750791 := bstep (se 1 (by rfl) ⟨563093, by rfl⟩ : syracuseStep 750791 = 1126187) B1126187
theorem B1578217 : Blo 327838 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B791801 : Blo 327838 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B1250599 : Blo 327838 1250599 := bstep (se 1 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 1250599 = 1875899) B1875899
theorem B742751 : Blo 327838 742751 := bstep (se 1 (by rfl) ⟨557063, by rfl⟩ : syracuseStep 742751 = 1114127) B1114127
theorem B554377 : Blo 327838 554377 := bstep (se 2 (by rfl) ⟨207891, by rfl⟩ : syracuseStep 554377 = 415783) B415783
theorem B890311 : Blo 327838 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B701959 : Blo 327838 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B1250873 : Blo 327838 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B1783453 : Blo 327838 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B743147 : Blo 327838 743147 := bstep (se 1 (by rfl) ⟨557360, by rfl⟩ : syracuseStep 743147 = 1114721) B1114721
theorem B800519 : Blo 327838 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B833287 : Blo 327838 833287 := bstep (se 1 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 833287 = 1249931) B1249931
theorem B554809 : Blo 327838 554809 := bstep (se 2 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 554809 = 416107) B416107
theorem B3151709 : Blo 327838 3151709 := bstep (se 3 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 3151709 = 1181891) B1181891
theorem B1111913 : Blo 327838 1111913 := bstep (se 2 (by rfl) ⟨416967, by rfl⟩ : syracuseStep 1111913 = 833935) B833935
theorem B743273 : Blo 327838 743273 := bstep (se 2 (by rfl) ⟨278727, by rfl⟩ : syracuseStep 743273 = 557455) B557455
theorem B890831 : Blo 327838 890831 := bstep (se 1 (by rfl) ⟨668123, by rfl⟩ : syracuseStep 890831 = 1336247) B1336247
theorem B833561 : Blo 327838 833561 := bstep (se 2 (by rfl) ⟨312585, by rfl⟩ : syracuseStep 833561 = 625171) B625171
theorem B555113 : Blo 327838 555113 := bstep (se 2 (by rfl) ⟨208167, by rfl⟩ : syracuseStep 555113 = 416335) B416335
theorem B3045539 : Blo 327838 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B11868389 : Blo 327838 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B4512023 : Blo 327838 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B3545369 : Blo 327838 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B1112345 : Blo 327838 1112345 := bstep (se 2 (by rfl) ⟨417129, by rfl⟩ : syracuseStep 1112345 = 834259) B834259
theorem B3561803 : Blo 327838 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B4962637 : Blo 327838 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1661309 : Blo 327838 1661309 := bstep (se 3 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 1661309 = 622991) B622991
theorem B8010161 : Blo 327838 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B2103803 : Blo 327838 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B948809 : Blo 327838 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B752249 : Blo 327838 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B416431 : Blo 327838 416431 := bstep (se 1 (by rfl) ⟨312323, by rfl⟩ : syracuseStep 416431 = 624647) B624647
theorem B752303 : Blo 327838 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B891575 : Blo 327838 891575 := bstep (se 1 (by rfl) ⟨668681, by rfl⟩ : syracuseStep 891575 = 1337363) B1337363
theorem B744119 : Blo 327838 744119 := bstep (se 1 (by rfl) ⟨558089, by rfl⟩ : syracuseStep 744119 = 1116179) B1116179
theorem B4734071 : Blo 327838 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B2374877 : Blo 327838 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B1785185 : Blo 327838 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B556537 : Blo 327838 556537 := bstep (se 2 (by rfl) ⟨208701, by rfl⟩ : syracuseStep 556537 = 417403) B417403
theorem B5078533 : Blo 327838 5078533 := bstep (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) B952225
theorem B1244767 : Blo 327838 1244767 := bstep (se 1 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 1244767 = 1867151) B1867151
theorem B1113695 : Blo 327838 1113695 := bstep (se 1 (by rfl) ⟨835271, by rfl⟩ : syracuseStep 1113695 = 1670543) B1670543
theorem B1670867 : Blo 327838 1670867 := bstep (se 1 (by rfl) ⟨1253150, by rfl⟩ : syracuseStep 1670867 = 2506301) B2506301
theorem B2801411 : Blo 327838 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B556807 : Blo 327838 556807 := bstep (se 1 (by rfl) ⟨417605, by rfl⟩ : syracuseStep 556807 = 835211) B835211
theorem B1810183 : Blo 327838 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B556841 : Blo 327838 556841 := bstep (se 2 (by rfl) ⟨208815, by rfl⟩ : syracuseStep 556841 = 417631) B417631
theorem B1662767 : Blo 327838 1662767 := bstep (se 1 (by rfl) ⟨1247075, by rfl⟩ : syracuseStep 1662767 = 2494151) B2494151
theorem B835535 : Blo 327838 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B1589327 : Blo 327838 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B327911 : Blo 327838 327911 := bstep (se 1 (by rfl) ⟨245933, by rfl⟩ : syracuseStep 327911 = 491867) B491867
theorem B1114343 : Blo 327838 1114343 := bstep (se 1 (by rfl) ⟨835757, by rfl⟩ : syracuseStep 1114343 = 1671515) B1671515
theorem B491807 : Blo 327838 491807 := bstep (se 1 (by rfl) ⟨368855, by rfl⟩ : syracuseStep 491807 = 737711) B737711
theorem B491831 : Blo 327838 491831 := bstep (se 1 (by rfl) ⟨368873, by rfl⟩ : syracuseStep 491831 = 737747) B737747
theorem B467255 : Blo 327838 467255 := bstep (se 1 (by rfl) ⟨350441, by rfl⟩ : syracuseStep 467255 = 700883) B700883
theorem B1204577 : Blo 327838 1204577 := bstep (se 2 (by rfl) ⟨451716, by rfl⟩ : syracuseStep 1204577 = 903433) B903433
theorem B2539883 : Blo 327838 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B491903 : Blo 327838 491903 := bstep (se 1 (by rfl) ⟨368927, by rfl⟩ : syracuseStep 491903 = 737855) B737855
theorem B328063 : Blo 327838 328063 := bstep (se 1 (by rfl) ⟨246047, by rfl⟩ : syracuseStep 328063 = 492095) B492095
theorem B1253819 : Blo 327838 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B491975 : Blo 327838 491975 := bstep (se 1 (by rfl) ⟨368981, by rfl⟩ : syracuseStep 491975 = 737963) B737963
theorem B369103 : Blo 327838 369103 := bstep (se 1 (by rfl) ⟨276827, by rfl⟩ : syracuseStep 369103 = 553655) B553655
theorem B328143 : Blo 327838 328143 := bstep (se 1 (by rfl) ⟨246107, by rfl⟩ : syracuseStep 328143 = 492215) B492215
theorem B803279 : Blo 327838 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B1376831 : Blo 327838 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B6333005 : Blo 327838 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B328295 : Blo 327838 328295 := bstep (se 1 (by rfl) ⟨246221, by rfl⟩ : syracuseStep 328295 = 492443) B492443
theorem B557671 : Blo 327838 557671 := bstep (se 1 (by rfl) ⟨418253, by rfl⟩ : syracuseStep 557671 = 836507) B836507
theorem B1901177 : Blo 327838 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B557833 : Blo 327838 557833 := bstep (se 2 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 557833 = 418375) B418375
theorem B492329 : Blo 327838 492329 := bstep (se 2 (by rfl) ⟨184623, by rfl⟩ : syracuseStep 492329 = 369247) B369247
theorem B492335 : Blo 327838 492335 := bstep (se 1 (by rfl) ⟨369251, by rfl⟩ : syracuseStep 492335 = 738503) B738503
theorem B500527 : Blo 327838 500527 := bstep (se 1 (by rfl) ⟨375395, by rfl⟩ : syracuseStep 500527 = 750791) B750791
theorem B1114937 : Blo 327838 1114937 := bstep (se 2 (by rfl) ⟨418101, by rfl⟩ : syracuseStep 1114937 = 836203) B836203
theorem B328559 : Blo 327838 328559 := bstep (se 1 (by rfl) ⟨246419, by rfl⟩ : syracuseStep 328559 = 492839) B492839
theorem B1114991 : Blo 327838 1114991 := bstep (se 1 (by rfl) ⟨836243, by rfl⟩ : syracuseStep 1114991 = 1672487) B1672487
theorem B738215 : Blo 327838 738215 := bstep (se 1 (by rfl) ⟨553661, by rfl⟩ : syracuseStep 738215 = 1107323) B1107323
theorem B492455 : Blo 327838 492455 := bstep (se 1 (by rfl) ⟨369341, by rfl⟩ : syracuseStep 492455 = 738683) B738683
theorem B328615 : Blo 327838 328615 := bstep (se 1 (by rfl) ⟨246461, by rfl⟩ : syracuseStep 328615 = 492923) B492923
theorem B1868791 : Blo 327838 1868791 := bstep (se 1 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 1868791 = 2803187) B2803187
theorem B492539 : Blo 327838 492539 := bstep (se 1 (by rfl) ⟨369404, by rfl⟩ : syracuseStep 492539 = 738809) B738809
theorem B328699 : Blo 327838 328699 := bstep (se 1 (by rfl) ⟨246524, by rfl⟩ : syracuseStep 328699 = 493049) B493049
theorem B492599 : Blo 327838 492599 := bstep (se 1 (by rfl) ⟨369449, by rfl⟩ : syracuseStep 492599 = 738899) B738899
theorem B328767 : Blo 327838 328767 := bstep (se 1 (by rfl) ⟨246575, by rfl⟩ : syracuseStep 328767 = 493151) B493151
theorem B3433637 : Blo 327838 3433637 := bstep (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) B643807
theorem B492719 : Blo 327838 492719 := bstep (se 1 (by rfl) ⟨369539, by rfl⟩ : syracuseStep 492719 = 739079) B739079
theorem B328911 : Blo 327838 328911 := bstep (se 1 (by rfl) ⟨246683, by rfl⟩ : syracuseStep 328911 = 493367) B493367
theorem B4113713 : Blo 327838 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B370075 : Blo 327838 370075 := bstep (se 1 (by rfl) ⟨277556, by rfl⟩ : syracuseStep 370075 = 555113) B555113
theorem B329115 : Blo 327838 329115 := bstep (se 1 (by rfl) ⟨246836, by rfl⟩ : syracuseStep 329115 = 493673) B493673
theorem B3008015 : Blo 327838 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B493127 : Blo 327838 493127 := bstep (se 1 (by rfl) ⟨369845, by rfl⟩ : syracuseStep 493127 = 739691) B739691
theorem B1107539 : Blo 327838 1107539 := bstep (se 1 (by rfl) ⟨830654, by rfl⟩ : syracuseStep 1107539 = 1661309) B1661309
theorem B329327 : Blo 327838 329327 := bstep (se 1 (by rfl) ⟨246995, by rfl⟩ : syracuseStep 329327 = 493991) B493991
theorem B1115801 : Blo 327838 1115801 := bstep (se 2 (by rfl) ⟨418425, by rfl⟩ : syracuseStep 1115801 = 836851) B836851
theorem B1402535 : Blo 327838 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B493223 : Blo 327838 493223 := bstep (se 1 (by rfl) ⟨369917, by rfl⟩ : syracuseStep 493223 = 739835) B739835
theorem B329383 : Blo 327838 329383 := bstep (se 1 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 329383 = 494075) B494075
theorem B632539 : Blo 327838 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B493307 : Blo 327838 493307 := bstep (se 1 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 493307 = 739961) B739961
theorem B329467 : Blo 327838 329467 := bstep (se 1 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 329467 = 494201) B494201
theorem B501499 : Blo 327838 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B493343 : Blo 327838 493343 := bstep (se 1 (by rfl) ⟨370007, by rfl⟩ : syracuseStep 493343 = 740015) B740015
theorem B329503 : Blo 327838 329503 := bstep (se 1 (by rfl) ⟨247127, by rfl⟩ : syracuseStep 329503 = 494255) B494255
theorem B501535 : Blo 327838 501535 := bstep (se 1 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 501535 = 752303) B752303
theorem B329535 : Blo 327838 329535 := bstep (se 1 (by rfl) ⟨247151, by rfl⟩ : syracuseStep 329535 = 494303) B494303
theorem B739151 : Blo 327838 739151 := bstep (se 1 (by rfl) ⟨554363, by rfl⟩ : syracuseStep 739151 = 1108727) B1108727
theorem B493391 : Blo 327838 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B1107809 : Blo 327838 1107809 := bstep (se 2 (by rfl) ⟨415428, by rfl⟩ : syracuseStep 1107809 = 830857) B830857
theorem B739169 : Blo 327838 739169 := bstep (se 2 (by rfl) ⟨277188, by rfl⟩ : syracuseStep 739169 = 554377) B554377
theorem B1673135 : Blo 327838 1673135 := bstep (se 1 (by rfl) ⟨1254851, by rfl⟩ : syracuseStep 1673135 = 2509703) B2509703
theorem B493511 : Blo 327838 493511 := bstep (se 1 (by rfl) ⟨370133, by rfl⟩ : syracuseStep 493511 = 740267) B740267
theorem B329711 : Blo 327838 329711 := bstep (se 1 (by rfl) ⟨247283, by rfl⟩ : syracuseStep 329711 = 494567) B494567
theorem B935945 : Blo 327838 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B3156047 : Blo 327838 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B2115719 : Blo 327838 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B329883 : Blo 327838 329883 := bstep (se 1 (by rfl) ⟨247412, by rfl⟩ : syracuseStep 329883 = 494825) B494825
theorem B936127 : Blo 327838 936127 := bstep (se 1 (by rfl) ⟨702095, by rfl⟩ : syracuseStep 936127 = 1404191) B1404191
theorem B329919 : Blo 327838 329919 := bstep (se 1 (by rfl) ⟨247439, by rfl⟩ : syracuseStep 329919 = 494879) B494879
theorem B2377937 : Blo 327838 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B1411283 : Blo 327838 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B592105 : Blo 327838 592105 := bstep (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) B444079
theorem B624935 : Blo 327838 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B493865 : Blo 327838 493865 := bstep (se 2 (by rfl) ⟨185199, by rfl⟩ : syracuseStep 493865 = 370399) B370399
theorem B493871 : Blo 327838 493871 := bstep (se 1 (by rfl) ⟨370403, by rfl⟩ : syracuseStep 493871 = 740807) B740807
theorem B330031 : Blo 327838 330031 := bstep (se 1 (by rfl) ⟨247523, by rfl⟩ : syracuseStep 330031 = 495047) B495047
theorem B739745 : Blo 327838 739745 := bstep (se 2 (by rfl) ⟨277404, by rfl⟩ : syracuseStep 739745 = 554809) B554809
theorem B9521651 : Blo 327838 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B371227 : Blo 327838 371227 := bstep (se 1 (by rfl) ⟨278420, by rfl⟩ : syracuseStep 371227 = 556841) B556841
theorem B330267 : Blo 327838 330267 := bstep (se 1 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 330267 = 495401) B495401
theorem B1108511 : Blo 327838 1108511 := bstep (se 1 (by rfl) ⟨831383, by rfl⟩ : syracuseStep 1108511 = 1662767) B1662767
theorem B739871 : Blo 327838 739871 := bstep (se 1 (by rfl) ⟨554903, by rfl⟩ : syracuseStep 739871 = 1109807) B1109807
theorem B494111 : Blo 327838 494111 := bstep (se 1 (by rfl) ⟨370583, by rfl⟩ : syracuseStep 494111 = 741167) B741167
theorem B330271 : Blo 327838 330271 := bstep (se 1 (by rfl) ⟨247703, by rfl⟩ : syracuseStep 330271 = 495407) B495407
theorem B1870523 : Blo 327838 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B330587 : Blo 327838 330587 := bstep (se 1 (by rfl) ⟨247940, by rfl⟩ : syracuseStep 330587 = 495881) B495881
theorem B494495 : Blo 327838 494495 := bstep (se 1 (by rfl) ⟨370871, by rfl⟩ : syracuseStep 494495 = 741743) B741743
theorem B330655 : Blo 327838 330655 := bstep (se 1 (by rfl) ⟨247991, by rfl⟩ : syracuseStep 330655 = 495983) B495983
theorem B494543 : Blo 327838 494543 := bstep (se 1 (by rfl) ⟨370907, by rfl⟩ : syracuseStep 494543 = 741815) B741815
theorem B494633 : Blo 327838 494633 := bstep (se 2 (by rfl) ⟨185487, by rfl⟩ : syracuseStep 494633 = 370975) B370975
theorem B789551 : Blo 327838 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B494639 : Blo 327838 494639 := bstep (se 1 (by rfl) ⟨370979, by rfl⟩ : syracuseStep 494639 = 741959) B741959
theorem B470063 : Blo 327838 470063 := bstep (se 1 (by rfl) ⟨352547, by rfl⟩ : syracuseStep 470063 = 705095) B705095
theorem B494663 : Blo 327838 494663 := bstep (se 1 (by rfl) ⟨370997, by rfl⟩ : syracuseStep 494663 = 741995) B741995
theorem B2403425 : Blo 327838 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B1666169 : Blo 327838 1666169 := bstep (se 2 (by rfl) ⟨624813, by rfl⟩ : syracuseStep 1666169 = 1249627) B1249627
theorem B470137 : Blo 327838 470137 := bstep (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) B352603
theorem B494927 : Blo 327838 494927 := bstep (se 1 (by rfl) ⟨371195, by rfl⟩ : syracuseStep 494927 = 742391) B742391
theorem B495017 : Blo 327838 495017 := bstep (se 2 (by rfl) ⟨185631, by rfl⟩ : syracuseStep 495017 = 371263) B371263
theorem B1330615 : Blo 327838 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B4492793 : Blo 327838 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B527867 : Blo 327838 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B1404449 : Blo 327838 1404449 := bstep (se 2 (by rfl) ⟨526668, by rfl⟩ : syracuseStep 1404449 = 1053337) B1053337
theorem B495167 : Blo 327838 495167 := bstep (se 1 (by rfl) ⟨371375, by rfl⟩ : syracuseStep 495167 = 742751) B742751
theorem B2371187 : Blo 327838 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B5680801 : Blo 327838 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B495431 : Blo 327838 495431 := bstep (se 1 (by rfl) ⟨371573, by rfl⟩ : syracuseStep 495431 = 743147) B743147
theorem B1994635 : Blo 327838 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B2101139 : Blo 327838 2101139 := bstep (se 1 (by rfl) ⟨1575854, by rfl⟩ : syracuseStep 2101139 = 3151709) B3151709
theorem B1109915 : Blo 327838 1109915 := bstep (se 1 (by rfl) ⟨832436, by rfl⟩ : syracuseStep 1109915 = 1664873) B1664873
theorem B741275 : Blo 327838 741275 := bstep (se 1 (by rfl) ⟨555956, by rfl⟩ : syracuseStep 741275 = 1111913) B1111913
theorem B495515 : Blo 327838 495515 := bstep (se 1 (by rfl) ⟨371636, by rfl⟩ : syracuseStep 495515 = 743273) B743273
theorem B831455 : Blo 327838 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B593887 : Blo 327838 593887 := bstep (se 1 (by rfl) ⟨445415, by rfl⟩ : syracuseStep 593887 = 890831) B890831
theorem B733151 : Blo 327838 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B24047705 : Blo 327838 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B2363579 : Blo 327838 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B741563 : Blo 327838 741563 := bstep (se 1 (by rfl) ⟨556172, by rfl⟩ : syracuseStep 741563 = 1112345) B1112345
theorem B1880273 : Blo 327838 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1782071 : Blo 327838 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B1667465 : Blo 327838 1667465 := bstep (se 2 (by rfl) ⟨625299, by rfl⟩ : syracuseStep 1667465 = 1250599) B1250599
theorem B594383 : Blo 327838 594383 := bstep (se 1 (by rfl) ⟨445787, by rfl⟩ : syracuseStep 594383 = 891575) B891575
theorem B496079 : Blo 327838 496079 := bstep (se 1 (by rfl) ⟨372059, by rfl⟩ : syracuseStep 496079 = 744119) B744119
theorem B496121 : Blo 327838 496121 := bstep (se 2 (by rfl) ⟨186045, by rfl⟩ : syracuseStep 496121 = 372091) B372091
theorem B2372111 : Blo 327838 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B553567 : Blo 327838 553567 := bstep (se 1 (by rfl) ⟨415175, by rfl⟩ : syracuseStep 553567 = 830351) B830351
theorem B832103 : Blo 327838 832103 := bstep (se 1 (by rfl) ⟨624077, by rfl⟩ : syracuseStep 832103 = 1248155) B1248155
theorem B742049 : Blo 327838 742049 := bstep (se 2 (by rfl) ⟨278268, by rfl⟩ : syracuseStep 742049 = 556537) B556537
theorem B6771377 : Blo 327838 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B2134717 : Blo 327838 2134717 := bstep (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) B800519
theorem B1872665 : Blo 327838 1872665 := bstep (se 2 (by rfl) ⟨702249, by rfl⟩ : syracuseStep 1872665 = 1404499) B1404499
theorem B1659689 : Blo 327838 1659689 := bstep (se 2 (by rfl) ⟨622383, by rfl⟩ : syracuseStep 1659689 = 1244767) B1244767
theorem B553979 : Blo 327838 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B1111049 : Blo 327838 1111049 := bstep (se 2 (by rfl) ⟨416643, by rfl⟩ : syracuseStep 1111049 = 833287) B833287
theorem B742409 : Blo 327838 742409 := bstep (se 2 (by rfl) ⟨278403, by rfl⟩ : syracuseStep 742409 = 556807) B556807
theorem B2413577 : Blo 327838 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1111103 : Blo 327838 1111103 := bstep (se 1 (by rfl) ⟨833327, by rfl⟩ : syracuseStep 1111103 = 1666655) B1666655
theorem B742463 : Blo 327838 742463 := bstep (se 1 (by rfl) ⟨556847, by rfl⟩ : syracuseStep 742463 = 1113695) B1113695
theorem B832619 : Blo 327838 832619 := bstep (se 1 (by rfl) ⟨624464, by rfl⟩ : syracuseStep 832619 = 1248929) B1248929
theorem B1996019 : Blo 327838 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B554411 : Blo 327838 554411 := bstep (se 1 (by rfl) ⟨415808, by rfl⟩ : syracuseStep 554411 = 831617) B831617
theorem B1922617 : Blo 327838 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B2815559 : Blo 327838 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B2504357 : Blo 327838 2504357 := bstep (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) B469567
theorem B173930165 : Blo 327838 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B6616849 : Blo 327838 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B415687 : Blo 327838 415687 := bstep (se 1 (by rfl) ⟨311765, by rfl⟩ : syracuseStep 415687 = 623531) B623531
theorem B554951 : Blo 327838 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B743399 : Blo 327838 743399 := bstep (se 1 (by rfl) ⟨557549, by rfl⟩ : syracuseStep 743399 = 1115099) B1115099
theorem B743417 : Blo 327838 743417 := bstep (se 2 (by rfl) ⟨278781, by rfl⟩ : syracuseStep 743417 = 557563) B557563
theorem B743507 : Blo 327838 743507 := bstep (se 1 (by rfl) ⟨557630, by rfl⟩ : syracuseStep 743507 = 1115261) B1115261
theorem B9664661 : Blo 327838 9664661 := bstep (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) B453031
theorem B743579 : Blo 327838 743579 := bstep (se 1 (by rfl) ⟨557684, by rfl⟩ : syracuseStep 743579 = 1115369) B1115369
theorem B1874123 : Blo 327838 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B555241 : Blo 327838 555241 := bstep (se 2 (by rfl) ⟨208215, by rfl⟩ : syracuseStep 555241 = 416431) B416431
theorem B1251571 : Blo 327838 1251571 := bstep (se 1 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 1251571 = 1877357) B1877357
theorem B743687 : Blo 327838 743687 := bstep (se 1 (by rfl) ⟨557765, by rfl⟩ : syracuseStep 743687 = 1115531) B1115531
theorem B833915 : Blo 327838 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B3152357 : Blo 327838 3152357 := bstep (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) B591067
theorem B743993 : Blo 327838 743993 := bstep (se 2 (by rfl) ⟨278997, by rfl⟩ : syracuseStep 743993 = 557995) B557995
theorem B1587865 : Blo 327838 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B555707 : Blo 327838 555707 := bstep (se 1 (by rfl) ⟨416780, by rfl⟩ : syracuseStep 555707 = 833561) B833561
theorem B2030359 : Blo 327838 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B7912259 : Blo 327838 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B416603 : Blo 327838 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B2431853 : Blo 327838 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B2374535 : Blo 327838 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B5340107 : Blo 327838 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B2104289 : Blo 327838 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B1187081 : Blo 327838 1187081 := bstep (se 2 (by rfl) ⟨445155, by rfl⟩ : syracuseStep 1187081 = 890311) B890311
theorem B941321 : Blo 327838 941321 := bstep (se 2 (by rfl) ⟨352995, by rfl⟩ : syracuseStep 941321 = 705991) B705991
theorem B13491521 : Blo 327838 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B1588673 : Blo 327838 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B1190123 : Blo 327838 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B1400399 : Blo 327838 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B417575 : Blo 327838 417575 := bstep (se 1 (by rfl) ⟨313181, by rfl⟩ : syracuseStep 417575 = 626363) B626363
theorem B1113911 : Blo 327838 1113911 := bstep (se 1 (by rfl) ⟨835433, by rfl⟩ : syracuseStep 1113911 = 1670867) B1670867
theorem B1867607 : Blo 327838 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B2498525 : Blo 327838 2498525 := bstep (se 3 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 2498525 = 936947) B936947
theorem B557023 : Blo 327838 557023 := bstep (se 1 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 557023 = 835535) B835535
theorem B16031803 : Blo 327838 16031803 := bstep (se 1 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 16031803 = 24047705) B24047705
theorem B1253501 : Blo 327838 1253501 := bstep (se 3 (by rfl) ⟨235031, by rfl⟩ : syracuseStep 1253501 = 470063) B470063
theorem B1253515 : Blo 327838 1253515 := bstep (se 1 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 1253515 = 1880273) B1880273
theorem B327871 : Blo 327838 327871 := bstep (se 1 (by rfl) ⟨245903, by rfl⟩ : syracuseStep 327871 = 491807) B491807
theorem B327887 : Blo 327838 327887 := bstep (se 1 (by rfl) ⟨245915, by rfl⟩ : syracuseStep 327887 = 491831) B491831
theorem B1188047 : Blo 327838 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B803051 : Blo 327838 803051 := bstep (se 1 (by rfl) ⟨602288, by rfl⟩ : syracuseStep 803051 = 1204577) B1204577
theorem B327935 : Blo 327838 327935 := bstep (se 1 (by rfl) ⟨245951, by rfl⟩ : syracuseStep 327935 = 491903) B491903
theorem B835879 : Blo 327838 835879 := bstep (se 1 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 835879 = 1253819) B1253819
theorem B327983 : Blo 327838 327983 := bstep (se 1 (by rfl) ⟨245987, by rfl⟩ : syracuseStep 327983 = 491975) B491975
theorem B1581407 : Blo 327838 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B917887 : Blo 327838 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B4514251 : Blo 327838 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B1106459 : Blo 327838 1106459 := bstep (se 1 (by rfl) ⟨829844, by rfl⟩ : syracuseStep 1106459 = 1659689) B1659689
theorem B328219 : Blo 327838 328219 := bstep (se 1 (by rfl) ⟨246164, by rfl⟩ : syracuseStep 328219 = 492329) B492329
theorem B328223 : Blo 327838 328223 := bstep (se 1 (by rfl) ⟨246167, by rfl⟩ : syracuseStep 328223 = 492335) B492335
theorem B492137 : Blo 327838 492137 := bstep (se 2 (by rfl) ⟨184551, by rfl⟩ : syracuseStep 492137 = 369103) B369103
theorem B492143 : Blo 327838 492143 := bstep (se 1 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 492143 = 738215) B738215
theorem B328303 : Blo 327838 328303 := bstep (se 1 (by rfl) ⟨246227, by rfl⟩ : syracuseStep 328303 = 492455) B492455
theorem B369319 : Blo 327838 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B328359 : Blo 327838 328359 := bstep (se 1 (by rfl) ⟨246269, by rfl⟩ : syracuseStep 328359 = 492539) B492539
theorem B328399 : Blo 327838 328399 := bstep (se 1 (by rfl) ⟨246299, by rfl⟩ : syracuseStep 328399 = 492599) B492599
theorem B328479 : Blo 327838 328479 := bstep (se 1 (by rfl) ⟨246359, by rfl⟩ : syracuseStep 328479 = 492719) B492719
theorem B738089 : Blo 327838 738089 := bstep (se 2 (by rfl) ⟨276783, by rfl⟩ : syracuseStep 738089 = 553567) B553567
theorem B10969901 : Blo 327838 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B1246013 : Blo 327838 1246013 := bstep (se 3 (by rfl) ⟨233627, by rfl⟩ : syracuseStep 1246013 = 467255) B467255
theorem B369607 : Blo 327838 369607 := bstep (se 1 (by rfl) ⟨277205, by rfl⟩ : syracuseStep 369607 = 554411) B554411
theorem B328751 : Blo 327838 328751 := bstep (se 1 (by rfl) ⟨246563, by rfl⟩ : syracuseStep 328751 = 493127) B493127
theorem B1877039 : Blo 327838 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B738359 : Blo 327838 738359 := bstep (se 1 (by rfl) ⟨553769, by rfl⟩ : syracuseStep 738359 = 1107539) B1107539
theorem B935023 : Blo 327838 935023 := bstep (se 1 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 935023 = 1402535) B1402535
theorem B328815 : Blo 327838 328815 := bstep (se 1 (by rfl) ⟨246611, by rfl⟩ : syracuseStep 328815 = 493223) B493223
theorem B328871 : Blo 327838 328871 := bstep (se 1 (by rfl) ⟨246653, by rfl⟩ : syracuseStep 328871 = 493307) B493307
theorem B4236461 : Blo 327838 4236461 := bstep (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) B1588673
theorem B328895 : Blo 327838 328895 := bstep (se 1 (by rfl) ⟨246671, by rfl⟩ : syracuseStep 328895 = 493343) B493343
theorem B492767 : Blo 327838 492767 := bstep (se 1 (by rfl) ⟨369575, by rfl⟩ : syracuseStep 492767 = 739151) B739151
theorem B328927 : Blo 327838 328927 := bstep (se 1 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 328927 = 493391) B493391
theorem B738539 : Blo 327838 738539 := bstep (se 1 (by rfl) ⟨553904, by rfl⟩ : syracuseStep 738539 = 1107809) B1107809
theorem B492779 : Blo 327838 492779 := bstep (se 1 (by rfl) ⟨369584, by rfl⟩ : syracuseStep 492779 = 739169) B739169
theorem B1115423 : Blo 327838 1115423 := bstep (se 1 (by rfl) ⟨836567, by rfl⟩ : syracuseStep 1115423 = 1673135) B1673135
theorem B369967 : Blo 327838 369967 := bstep (se 1 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 369967 = 554951) B554951
theorem B329007 : Blo 327838 329007 := bstep (se 1 (by rfl) ⟨246755, by rfl⟩ : syracuseStep 329007 = 493511) B493511
theorem B2491721 : Blo 327838 2491721 := bstep (se 2 (by rfl) ⟨934395, by rfl⟩ : syracuseStep 2491721 = 1868791) B1868791
theorem B623963 : Blo 327838 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B1410479 : Blo 327838 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B329243 : Blo 327838 329243 := bstep (se 1 (by rfl) ⟨246932, by rfl⟩ : syracuseStep 329243 = 493865) B493865
theorem B329247 : Blo 327838 329247 := bstep (se 1 (by rfl) ⟨246935, by rfl⟩ : syracuseStep 329247 = 493871) B493871
theorem B493163 : Blo 327838 493163 := bstep (se 1 (by rfl) ⟨369872, by rfl⟩ : syracuseStep 493163 = 739745) B739745
theorem B739007 : Blo 327838 739007 := bstep (se 1 (by rfl) ⟨554255, by rfl⟩ : syracuseStep 739007 = 1108511) B1108511
theorem B493247 : Blo 327838 493247 := bstep (se 1 (by rfl) ⟨369935, by rfl⟩ : syracuseStep 493247 = 739871) B739871
theorem B329407 : Blo 327838 329407 := bstep (se 1 (by rfl) ⟨247055, by rfl⟩ : syracuseStep 329407 = 494111) B494111
theorem B1247015 : Blo 327838 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B370471 : Blo 327838 370471 := bstep (se 1 (by rfl) ⟨277853, by rfl⟩ : syracuseStep 370471 = 555707) B555707
theorem B493433 : Blo 327838 493433 := bstep (se 2 (by rfl) ⟨185037, by rfl⟩ : syracuseStep 493433 = 370075) B370075
theorem B1583023 : Blo 327838 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B329663 : Blo 327838 329663 := bstep (se 1 (by rfl) ⟨247247, by rfl⟩ : syracuseStep 329663 = 494495) B494495
theorem B329695 : Blo 327838 329695 := bstep (se 1 (by rfl) ⟨247271, by rfl⟩ : syracuseStep 329695 = 494543) B494543
theorem B1402859 : Blo 327838 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B329755 : Blo 327838 329755 := bstep (se 1 (by rfl) ⟨247316, by rfl⟩ : syracuseStep 329755 = 494633) B494633
theorem B526367 : Blo 327838 526367 := bstep (se 1 (by rfl) ⟨394775, by rfl⟩ : syracuseStep 526367 = 789551) B789551
theorem B329759 : Blo 327838 329759 := bstep (se 1 (by rfl) ⟨247319, by rfl⟩ : syracuseStep 329759 = 494639) B494639
theorem B329775 : Blo 327838 329775 := bstep (se 1 (by rfl) ⟨247331, by rfl⟩ : syracuseStep 329775 = 494663) B494663
theorem B329951 : Blo 327838 329951 := bstep (se 1 (by rfl) ⟨247463, by rfl⟩ : syracuseStep 329951 = 494927) B494927
theorem B330011 : Blo 327838 330011 := bstep (se 1 (by rfl) ⟨247508, by rfl⟩ : syracuseStep 330011 = 495017) B495017
theorem B936299 : Blo 327838 936299 := bstep (se 1 (by rfl) ⟨702224, by rfl⟩ : syracuseStep 936299 = 1404449) B1404449
theorem B330111 : Blo 327838 330111 := bstep (se 1 (by rfl) ⟨247583, by rfl⟩ : syracuseStep 330111 = 495167) B495167
theorem B330287 : Blo 327838 330287 := bstep (se 1 (by rfl) ⟨247715, by rfl⟩ : syracuseStep 330287 = 495431) B495431
theorem B739943 : Blo 327838 739943 := bstep (se 1 (by rfl) ⟨554957, by rfl⟩ : syracuseStep 739943 = 1109915) B1109915
theorem B494183 : Blo 327838 494183 := bstep (se 1 (by rfl) ⟨370637, by rfl⟩ : syracuseStep 494183 = 741275) B741275
theorem B330343 : Blo 327838 330343 := bstep (se 1 (by rfl) ⟨247757, by rfl⟩ : syracuseStep 330343 = 495515) B495515
theorem B1665683 : Blo 327838 1665683 := bstep (se 1 (by rfl) ⟨1249262, by rfl⟩ : syracuseStep 1665683 = 2498525) B2498525
theorem B1059551 : Blo 327838 1059551 := bstep (se 1 (by rfl) ⟨794663, by rfl⟩ : syracuseStep 1059551 = 1589327) B1589327
theorem B1575719 : Blo 327838 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B494375 : Blo 327838 494375 := bstep (se 1 (by rfl) ⟨370781, by rfl⟩ : syracuseStep 494375 = 741563) B741563
theorem B1248169 : Blo 327838 1248169 := bstep (se 2 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 1248169 = 936127) B936127
theorem B535519 : Blo 327838 535519 := bstep (se 1 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 535519 = 803279) B803279
theorem B330719 : Blo 327838 330719 := bstep (se 1 (by rfl) ⟨248039, by rfl⟩ : syracuseStep 330719 = 496079) B496079
theorem B789473 : Blo 327838 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B740321 : Blo 327838 740321 := bstep (se 2 (by rfl) ⟨277620, by rfl⟩ : syracuseStep 740321 = 555241) B555241
theorem B330747 : Blo 327838 330747 := bstep (se 1 (by rfl) ⟨248060, by rfl⟩ : syracuseStep 330747 = 496121) B496121
theorem B4222003 : Blo 327838 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B494699 : Blo 327838 494699 := bstep (se 1 (by rfl) ⟨371024, by rfl⟩ : syracuseStep 494699 = 742049) B742049
theorem B1248443 : Blo 327838 1248443 := bstep (se 1 (by rfl) ⟨936332, by rfl⟩ : syracuseStep 1248443 = 1872665) B1872665
theorem B740699 : Blo 327838 740699 := bstep (se 1 (by rfl) ⟨555524, by rfl⟩ : syracuseStep 740699 = 1111049) B1111049
theorem B494939 : Blo 327838 494939 := bstep (se 1 (by rfl) ⟨371204, by rfl⟩ : syracuseStep 494939 = 742409) B742409
theorem B2510189 : Blo 327838 2510189 := bstep (se 3 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 2510189 = 941321) B941321
theorem B494969 : Blo 327838 494969 := bstep (se 2 (by rfl) ⟨185613, by rfl⟩ : syracuseStep 494969 = 371227) B371227
theorem B740735 : Blo 327838 740735 := bstep (se 1 (by rfl) ⟨555551, by rfl⟩ : syracuseStep 740735 = 1111103) B1111103
theorem B494975 : Blo 327838 494975 := bstep (se 1 (by rfl) ⟨371231, by rfl⟩ : syracuseStep 494975 = 742463) B742463
theorem B1666493 : Blo 327838 1666493 := bstep (se 3 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 1666493 = 624935) B624935
theorem B2289091 : Blo 327838 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B1330679 : Blo 327838 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B2117153 : Blo 327838 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B2707145 : Blo 327838 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B667369 : Blo 327838 667369 := bstep (se 2 (by rfl) ⟨250263, by rfl⟩ : syracuseStep 667369 = 500527) B500527
theorem B115953443 : Blo 327838 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B1585021 : Blo 327838 1585021 := bstep (se 3 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 1585021 = 594383) B594383
theorem B11980781 : Blo 327838 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B495599 : Blo 327838 495599 := bstep (se 1 (by rfl) ⟨371699, by rfl⟩ : syracuseStep 495599 = 743399) B743399
theorem B495611 : Blo 327838 495611 := bstep (se 1 (by rfl) ⟨371708, by rfl⟩ : syracuseStep 495611 = 743417) B743417
theorem B495671 : Blo 327838 495671 := bstep (se 1 (by rfl) ⟨371753, by rfl⟩ : syracuseStep 495671 = 743507) B743507
theorem B6443107 : Blo 327838 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B495719 : Blo 327838 495719 := bstep (se 1 (by rfl) ⟨371789, by rfl⟩ : syracuseStep 495719 = 743579) B743579
theorem B1249415 : Blo 327838 1249415 := bstep (se 1 (by rfl) ⟨937061, by rfl⟩ : syracuseStep 1249415 = 1874123) B1874123
theorem B1585291 : Blo 327838 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B626849 : Blo 327838 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B2674853 : Blo 327838 2674853 := bstep (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) B501535
theorem B495791 : Blo 327838 495791 := bstep (se 1 (by rfl) ⟨371843, by rfl⟩ : syracuseStep 495791 = 743687) B743687
theorem B2101571 : Blo 327838 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B495995 : Blo 327838 495995 := bstep (se 1 (by rfl) ⟨371996, by rfl⟩ : syracuseStep 495995 = 743993) B743993
theorem B1774153 : Blo 327838 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B3560071 : Blo 327838 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B1602283 : Blo 327838 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1110779 : Blo 327838 1110779 := bstep (se 1 (by rfl) ⟨833084, by rfl⟩ : syracuseStep 1110779 = 1666169) B1666169
theorem B791387 : Blo 327838 791387 := bstep (se 1 (by rfl) ⟨593540, by rfl⟩ : syracuseStep 791387 = 1187081) B1187081
theorem B7574401 : Blo 327838 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B1110941 : Blo 327838 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B668665 : Blo 327838 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B2659513 : Blo 327838 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B742607 : Blo 327838 742607 := bstep (se 1 (by rfl) ⟨556955, by rfl⟩ : syracuseStep 742607 = 1113911) B1113911
theorem B554249 : Blo 327838 554249 := bstep (se 2 (by rfl) ⟨207843, by rfl⟩ : syracuseStep 554249 = 415687) B415687
theorem B791849 : Blo 327838 791849 := bstep (se 2 (by rfl) ⟨296943, by rfl⟩ : syracuseStep 791849 = 593887) B593887
theorem B742697 : Blo 327838 742697 := bstep (se 2 (by rfl) ⟨278511, by rfl⟩ : syracuseStep 742697 = 557023) B557023
theorem B554303 : Blo 327838 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B488767 : Blo 327838 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B6436205 : Blo 327838 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B742895 : Blo 327838 742895 := bstep (se 1 (by rfl) ⟨557171, by rfl⟩ : syracuseStep 742895 = 1114343) B1114343
theorem B1111643 : Blo 327838 1111643 := bstep (se 1 (by rfl) ⟨833732, by rfl⟩ : syracuseStep 1111643 = 1667465) B1667465
theorem B1668761 : Blo 327838 1668761 := bstep (se 2 (by rfl) ⟨625785, by rfl⟩ : syracuseStep 1668761 = 1251571) B1251571
theorem B554735 : Blo 327838 554735 := bstep (se 1 (by rfl) ⟨416051, by rfl⟩ : syracuseStep 554735 = 832103) B832103
theorem B1267451 : Blo 327838 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B743291 : Blo 327838 743291 := bstep (se 1 (by rfl) ⟨557468, by rfl⟩ : syracuseStep 743291 = 1114937) B1114937
theorem B743327 : Blo 327838 743327 := bstep (se 1 (by rfl) ⟨557495, by rfl⟩ : syracuseStep 743327 = 1114991) B1114991
theorem B555079 : Blo 327838 555079 := bstep (se 1 (by rfl) ⟨416309, by rfl⟩ : syracuseStep 555079 = 832619) B832619
theorem B743561 : Blo 327838 743561 := bstep (se 2 (by rfl) ⟨278835, by rfl⟩ : syracuseStep 743561 = 557671) B557671
theorem B6773021 : Blo 327838 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B11385157 : Blo 327838 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B2005343 : Blo 327838 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B743777 : Blo 327838 743777 := bstep (se 2 (by rfl) ⟨278916, by rfl⟩ : syracuseStep 743777 = 557833) B557833
theorem B743867 : Blo 327838 743867 := bstep (se 1 (by rfl) ⟨557900, by rfl⟩ : syracuseStep 743867 = 1115801) B1115801
theorem B1669571 : Blo 327838 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B2104031 : Blo 327838 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B940855 : Blo 327838 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B793415 : Blo 327838 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B555943 : Blo 327838 555943 := bstep (se 1 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 555943 = 833915) B833915
theorem B6347767 : Blo 327838 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B5274839 : Blo 327838 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B1621235 : Blo 327838 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B2563489 : Blo 327838 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B1113533 : Blo 327838 1113533 := bstep (se 3 (by rfl) ⟨208787, by rfl⟩ : syracuseStep 1113533 = 417575) B417575
theorem B8994347 : Blo 327838 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B843385 : Blo 327838 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B351911 : Blo 327838 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B8822465 : Blo 327838 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B933599 : Blo 327838 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B1580791 : Blo 327838 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B1245071 : Blo 327838 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B1400759 : Blo 327838 1400759 := bstep (se 1 (by rfl) ⟨1050569, by rfl⟩ : syracuseStep 1400759 = 2101139) B2101139
theorem B835667 : Blo 327838 835667 := bstep (se 1 (by rfl) ⟨626750, by rfl⟩ : syracuseStep 835667 = 1253501) B1253501
theorem B417899 : Blo 327838 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B2113721 : Blo 327838 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B1671353 : Blo 327838 1671353 := bstep (se 2 (by rfl) ⟨626757, by rfl⟩ : syracuseStep 1671353 = 1253515) B1253515
theorem B1401047 : Blo 327838 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B737639 : Blo 327838 737639 := bstep (se 1 (by rfl) ⟨553229, by rfl⟩ : syracuseStep 737639 = 1106459) B1106459
theorem B1114505 : Blo 327838 1114505 := bstep (se 2 (by rfl) ⟨417939, by rfl⟩ : syracuseStep 1114505 = 835879) B835879
theorem B328091 : Blo 327838 328091 := bstep (se 1 (by rfl) ⟨246068, by rfl⟩ : syracuseStep 328091 = 492137) B492137
theorem B328095 : Blo 327838 328095 := bstep (se 1 (by rfl) ⟨246071, by rfl⟩ : syracuseStep 328095 = 492143) B492143
theorem B15180209 : Blo 327838 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B492059 : Blo 327838 492059 := bstep (se 1 (by rfl) ⟨369044, by rfl⟩ : syracuseStep 492059 = 738089) B738089
theorem B14066237 : Blo 327838 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B492239 : Blo 327838 492239 := bstep (se 1 (by rfl) ⟨369179, by rfl⟩ : syracuseStep 492239 = 738359) B738359
theorem B328511 : Blo 327838 328511 := bstep (se 1 (by rfl) ⟨246383, by rfl⟩ : syracuseStep 328511 = 492767) B492767
theorem B492359 : Blo 327838 492359 := bstep (se 1 (by rfl) ⟨369269, by rfl⟩ : syracuseStep 492359 = 738539) B738539
theorem B328519 : Blo 327838 328519 := bstep (se 1 (by rfl) ⟨246389, by rfl⟩ : syracuseStep 328519 = 492779) B492779
theorem B369499 : Blo 327838 369499 := bstep (se 1 (by rfl) ⟨277124, by rfl⟩ : syracuseStep 369499 = 554249) B554249
theorem B369535 : Blo 327838 369535 := bstep (se 1 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 369535 = 554303) B554303
theorem B492425 : Blo 327838 492425 := bstep (se 2 (by rfl) ⟨184659, by rfl⟩ : syracuseStep 492425 = 369319) B369319
theorem B1663901 : Blo 327838 1663901 := bstep (se 3 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 1663901 = 623963) B623963
theorem B328775 : Blo 327838 328775 := bstep (se 1 (by rfl) ⟨246581, by rfl⟩ : syracuseStep 328775 = 493163) B493163
theorem B1254473 : Blo 327838 1254473 := bstep (se 2 (by rfl) ⟨470427, by rfl⟩ : syracuseStep 1254473 = 940855) B940855
theorem B492671 : Blo 327838 492671 := bstep (se 1 (by rfl) ⟨369503, by rfl⟩ : syracuseStep 492671 = 739007) B739007
theorem B328831 : Blo 327838 328831 := bstep (se 1 (by rfl) ⟨246623, by rfl⟩ : syracuseStep 328831 = 493247) B493247
theorem B369823 : Blo 327838 369823 := bstep (se 1 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 369823 = 554735) B554735
theorem B844967 : Blo 327838 844967 := bstep (se 1 (by rfl) ⟨633725, by rfl⟩ : syracuseStep 844967 = 1267451) B1267451
theorem B1664225 : Blo 327838 1664225 := bstep (se 2 (by rfl) ⟨624084, by rfl⟩ : syracuseStep 1664225 = 1248169) B1248169
theorem B328955 : Blo 327838 328955 := bstep (se 1 (by rfl) ⟨246716, by rfl⟩ : syracuseStep 328955 = 493433) B493433
theorem B492809 : Blo 327838 492809 := bstep (se 2 (by rfl) ⟨184803, by rfl⟩ : syracuseStep 492809 = 369607) B369607
theorem B714025 : Blo 327838 714025 := bstep (se 2 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 714025 = 535519) B535519
theorem B935239 : Blo 327838 935239 := bstep (se 1 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 935239 = 1402859) B1402859
theorem B8463689 : Blo 327838 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B5629337 : Blo 327838 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B1246697 : Blo 327838 1246697 := bstep (se 2 (by rfl) ⟨467511, by rfl⟩ : syracuseStep 1246697 = 935023) B935023
theorem B4515347 : Blo 327838 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B1336895 : Blo 327838 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B624199 : Blo 327838 624199 := bstep (se 1 (by rfl) ⟨468149, by rfl⟩ : syracuseStep 624199 = 936299) B936299
theorem B493289 : Blo 327838 493289 := bstep (se 2 (by rfl) ⟨184983, by rfl⟩ : syracuseStep 493289 = 369967) B369967
theorem B493295 : Blo 327838 493295 := bstep (se 1 (by rfl) ⟨369971, by rfl⟩ : syracuseStep 493295 = 739943) B739943
theorem B329455 : Blo 327838 329455 := bstep (se 1 (by rfl) ⟨247091, by rfl⟩ : syracuseStep 329455 = 494183) B494183
theorem B1402687 : Blo 327838 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B706367 : Blo 327838 706367 := bstep (se 1 (by rfl) ⟨529775, by rfl⟩ : syracuseStep 706367 = 1059551) B1059551
theorem B1050479 : Blo 327838 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B329583 : Blo 327838 329583 := bstep (se 1 (by rfl) ⟨247187, by rfl⟩ : syracuseStep 329583 = 494375) B494375
theorem B3417985 : Blo 327838 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B493547 : Blo 327838 493547 := bstep (se 1 (by rfl) ⟨370160, by rfl⟩ : syracuseStep 493547 = 740321) B740321
theorem B329799 : Blo 327838 329799 := bstep (se 1 (by rfl) ⟨247349, by rfl⟩ : syracuseStep 329799 = 494699) B494699
theorem B1124513 : Blo 327838 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B493799 : Blo 327838 493799 := bstep (se 1 (by rfl) ⟨370349, by rfl⟩ : syracuseStep 493799 = 740699) B740699
theorem B329959 : Blo 327838 329959 := bstep (se 1 (by rfl) ⟨247469, by rfl⟩ : syracuseStep 329959 = 494939) B494939
theorem B329979 : Blo 327838 329979 := bstep (se 1 (by rfl) ⟨247484, by rfl⟩ : syracuseStep 329979 = 494969) B494969
theorem B493823 : Blo 327838 493823 := bstep (se 1 (by rfl) ⟨370367, by rfl⟩ : syracuseStep 493823 = 740735) B740735
theorem B329983 : Blo 327838 329983 := bstep (se 1 (by rfl) ⟨247487, by rfl⟩ : syracuseStep 329983 = 494975) B494975
theorem B2107721 : Blo 327838 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B887119 : Blo 327838 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B1411435 : Blo 327838 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B493961 : Blo 327838 493961 := bstep (se 2 (by rfl) ⟨185235, by rfl⟩ : syracuseStep 493961 = 370471) B370471
theorem B1804763 : Blo 327838 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B77302295 : Blo 327838 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B830047 : Blo 327838 830047 := bstep (se 1 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 830047 = 1245071) B1245071
theorem B3566213 : Blo 327838 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B330399 : Blo 327838 330399 := bstep (se 1 (by rfl) ⟨247799, by rfl⟩ : syracuseStep 330399 = 495599) B495599
theorem B330407 : Blo 327838 330407 := bstep (se 1 (by rfl) ⟨247805, by rfl⟩ : syracuseStep 330407 = 495611) B495611
theorem B330447 : Blo 327838 330447 := bstep (se 1 (by rfl) ⟨247835, by rfl⟩ : syracuseStep 330447 = 495671) B495671
theorem B330479 : Blo 327838 330479 := bstep (se 1 (by rfl) ⟨247859, by rfl⟩ : syracuseStep 330479 = 495719) B495719
theorem B21375737 : Blo 327838 21375737 := bstep (se 2 (by rfl) ⟨8015901, by rfl⟩ : syracuseStep 21375737 = 16031803) B16031803
theorem B740105 : Blo 327838 740105 := bstep (se 2 (by rfl) ⟨277539, by rfl⟩ : syracuseStep 740105 = 555079) B555079
theorem B330527 : Blo 327838 330527 := bstep (se 1 (by rfl) ⟨247895, by rfl⟩ : syracuseStep 330527 = 495791) B495791
theorem B535367 : Blo 327838 535367 := bstep (se 1 (by rfl) ⟨401525, by rfl⟩ : syracuseStep 535367 = 803051) B803051
theorem B330663 : Blo 327838 330663 := bstep (se 1 (by rfl) ⟨247997, by rfl⟩ : syracuseStep 330663 = 495995) B495995
theorem B740519 : Blo 327838 740519 := bstep (se 1 (by rfl) ⟨555389, by rfl⟩ : syracuseStep 740519 = 1110779) B1110779
theorem B1223849 : Blo 327838 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B830675 : Blo 327838 830675 := bstep (se 1 (by rfl) ⟨623006, by rfl⟩ : syracuseStep 830675 = 1246013) B1246013
theorem B527591 : Blo 327838 527591 := bstep (se 1 (by rfl) ⟨395693, by rfl⟩ : syracuseStep 527591 = 791387) B791387
theorem B740627 : Blo 327838 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B495071 : Blo 327838 495071 := bstep (se 1 (by rfl) ⟨371303, by rfl⟩ : syracuseStep 495071 = 742607) B742607
theorem B4746761 : Blo 327838 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B527899 : Blo 327838 527899 := bstep (se 1 (by rfl) ⟨395924, by rfl⟩ : syracuseStep 527899 = 791849) B791849
theorem B495131 : Blo 327838 495131 := bstep (se 1 (by rfl) ⟨371348, by rfl⟩ : syracuseStep 495131 = 742697) B742697
theorem B495263 : Blo 327838 495263 := bstep (se 1 (by rfl) ⟨371447, by rfl⟩ : syracuseStep 495263 = 742895) B742895
theorem B741095 : Blo 327838 741095 := bstep (se 1 (by rfl) ⟨555821, by rfl⟩ : syracuseStep 741095 = 1111643) B1111643
theorem B831343 : Blo 327838 831343 := bstep (se 1 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 831343 = 1247015) B1247015
theorem B741257 : Blo 327838 741257 := bstep (se 2 (by rfl) ⟨277971, by rfl⟩ : syracuseStep 741257 = 555943) B555943
theorem B495527 : Blo 327838 495527 := bstep (se 1 (by rfl) ⟨371645, by rfl⟩ : syracuseStep 495527 = 743291) B743291
theorem B495551 : Blo 327838 495551 := bstep (se 1 (by rfl) ⟨371663, by rfl⟩ : syracuseStep 495551 = 743327) B743327
theorem B495707 : Blo 327838 495707 := bstep (se 1 (by rfl) ⟨371780, by rfl⟩ : syracuseStep 495707 = 743561) B743561
theorem B495851 : Blo 327838 495851 := bstep (se 1 (by rfl) ⟨371888, by rfl⟩ : syracuseStep 495851 = 743777) B743777
theorem B495911 : Blo 327838 495911 := bstep (se 1 (by rfl) ⟨371933, by rfl⟩ : syracuseStep 495911 = 743867) B743867
theorem B651689 : Blo 327838 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B1110455 : Blo 327838 1110455 := bstep (se 1 (by rfl) ⟨832841, by rfl⟩ : syracuseStep 1110455 = 1665683) B1665683
theorem B938429 : Blo 327838 938429 := bstep (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) B351911
theorem B528943 : Blo 327838 528943 := bstep (se 1 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 528943 = 793415) B793415
theorem B3052121 : Blo 327838 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B832295 : Blo 327838 832295 := bstep (se 1 (by rfl) ⟨624221, by rfl⟩ : syracuseStep 832295 = 1248443) B1248443
theorem B1110995 : Blo 327838 1110995 := bstep (se 1 (by rfl) ⟨833246, by rfl⟩ : syracuseStep 1110995 = 1666493) B1666493
theorem B742355 : Blo 327838 742355 := bstep (se 1 (by rfl) ⟨556766, by rfl⟩ : syracuseStep 742355 = 1113533) B1113533
theorem B889825 : Blo 327838 889825 := bstep (se 2 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 889825 = 667369) B667369
theorem B2110697 : Blo 327838 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B832943 : Blo 327838 832943 := bstep (se 1 (by rfl) ⟨624707, by rfl⟩ : syracuseStep 832943 = 1249415) B1249415
theorem B1783235 : Blo 327838 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B792031 : Blo 327838 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B1054271 : Blo 327838 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B34363237 : Blo 327838 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B7313267 : Blo 327838 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B6019001 : Blo 327838 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B1251359 : Blo 327838 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B2365537 : Blo 327838 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B2824307 : Blo 327838 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B743615 : Blo 327838 743615 := bstep (se 1 (by rfl) ⟨557711, by rfl⟩ : syracuseStep 743615 = 1115423) B1115423
theorem B1661147 : Blo 327838 1661147 := bstep (se 1 (by rfl) ⟨1245860, by rfl⟩ : syracuseStep 1661147 = 2491721) B2491721
theorem B4290803 : Blo 327838 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B1673459 : Blo 327838 1673459 := bstep (se 1 (by rfl) ⟨1255094, by rfl⟩ : syracuseStep 1673459 = 2510189) B2510189
theorem B940319 : Blo 327838 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B2136377 : Blo 327838 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B1112507 : Blo 327838 1112507 := bstep (se 1 (by rfl) ⟨834380, by rfl⟩ : syracuseStep 1112507 = 1668761) B1668761
theorem B10099201 : Blo 327838 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B350911 : Blo 327838 350911 := bstep (se 1 (by rfl) ⟨263183, by rfl⟩ : syracuseStep 350911 = 526367) B526367
theorem B3546017 : Blo 327838 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B1113047 : Blo 327838 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B1080823 : Blo 327838 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B5996231 : Blo 327838 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B5881643 : Blo 327838 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B622399 : Blo 327838 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B2113361 : Blo 327838 2113361 := bstep (se 2 (by rfl) ⟨792510, by rfl⟩ : syracuseStep 2113361 = 1585021) B1585021
theorem B2105261 : Blo 327838 2105261 := bstep (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) B789473
theorem B933839 : Blo 327838 933839 := bstep (se 1 (by rfl) ⟨700379, by rfl⟩ : syracuseStep 933839 = 1400759) B1400759
theorem B7987187 : Blo 327838 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B557111 : Blo 327838 557111 := bstep (se 1 (by rfl) ⟨417833, by rfl⟩ : syracuseStep 557111 = 835667) B835667
theorem B1409147 : Blo 327838 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B1114235 : Blo 327838 1114235 := bstep (se 1 (by rfl) ⟨835676, by rfl⟩ : syracuseStep 1114235 = 1671353) B1671353
theorem B3154049 : Blo 327838 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B934031 : Blo 327838 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B491759 : Blo 327838 491759 := bstep (se 1 (by rfl) ⟨368819, by rfl⟩ : syracuseStep 491759 = 737639) B737639
theorem B1114397 : Blo 327838 1114397 := bstep (se 3 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 1114397 = 417899) B417899
theorem B328039 : Blo 327838 328039 := bstep (se 1 (by rfl) ⟨246029, by rfl⟩ : syracuseStep 328039 = 492059) B492059
theorem B328159 : Blo 327838 328159 := bstep (se 1 (by rfl) ⟨246119, by rfl⟩ : syracuseStep 328159 = 492239) B492239
theorem B328239 : Blo 327838 328239 := bstep (se 1 (by rfl) ⟨246179, by rfl⟩ : syracuseStep 328239 = 492359) B492359
theorem B328283 : Blo 327838 328283 := bstep (se 1 (by rfl) ⟨246212, by rfl⟩ : syracuseStep 328283 = 492425) B492425
theorem B836315 : Blo 327838 836315 := bstep (se 1 (by rfl) ⟨627236, by rfl⟩ : syracuseStep 836315 = 1254473) B1254473
theorem B705257 : Blo 327838 705257 := bstep (se 2 (by rfl) ⟨264471, by rfl⟩ : syracuseStep 705257 = 528943) B528943
theorem B328447 : Blo 327838 328447 := bstep (se 1 (by rfl) ⟨246335, by rfl⟩ : syracuseStep 328447 = 492671) B492671
theorem B1106729 : Blo 327838 1106729 := bstep (se 2 (by rfl) ⟨415023, by rfl⟩ : syracuseStep 1106729 = 830047) B830047
theorem B328539 : Blo 327838 328539 := bstep (se 1 (by rfl) ⟨246404, by rfl⟩ : syracuseStep 328539 = 492809) B492809
theorem B5620589 : Blo 327838 5620589 := bstep (se 3 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 5620589 = 2107721) B2107721
theorem B3752891 : Blo 327838 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B1188823 : Blo 327838 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B492665 : Blo 327838 492665 := bstep (se 2 (by rfl) ⟨184749, by rfl⟩ : syracuseStep 492665 = 369499) B369499
theorem B328859 : Blo 327838 328859 := bstep (se 1 (by rfl) ⟨246644, by rfl⟩ : syracuseStep 328859 = 493289) B493289
theorem B328863 : Blo 327838 328863 := bstep (se 1 (by rfl) ⟨246647, by rfl⟩ : syracuseStep 328863 = 493295) B493295
theorem B492713 : Blo 327838 492713 := bstep (se 2 (by rfl) ⟨184767, by rfl⟩ : syracuseStep 492713 = 369535) B369535
theorem B329031 : Blo 327838 329031 := bstep (se 1 (by rfl) ⟨246773, by rfl⟩ : syracuseStep 329031 = 493547) B493547
theorem B1107431 : Blo 327838 1107431 := bstep (se 1 (by rfl) ⟨830573, by rfl⟩ : syracuseStep 1107431 = 1661147) B1661147
theorem B329199 : Blo 327838 329199 := bstep (se 1 (by rfl) ⟨246899, by rfl⟩ : syracuseStep 329199 = 493799) B493799
theorem B2860535 : Blo 327838 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B329215 : Blo 327838 329215 := bstep (se 1 (by rfl) ⟨246911, by rfl⟩ : syracuseStep 329215 = 493823) B493823
theorem B1115639 : Blo 327838 1115639 := bstep (se 1 (by rfl) ⟨836729, by rfl⟩ : syracuseStep 1115639 = 1673459) B1673459
theorem B493097 : Blo 327838 493097 := bstep (se 2 (by rfl) ⟨184911, by rfl⟩ : syracuseStep 493097 = 369823) B369823
theorem B329307 : Blo 327838 329307 := bstep (se 1 (by rfl) ⟨246980, by rfl⟩ : syracuseStep 329307 = 493961) B493961
theorem B952033 : Blo 327838 952033 := bstep (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) B714025
theorem B2377475 : Blo 327838 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B1246985 : Blo 327838 1246985 := bstep (se 2 (by rfl) ⟨467619, by rfl⟩ : syracuseStep 1246985 = 935239) B935239
theorem B493403 : Blo 327838 493403 := bstep (se 1 (by rfl) ⟨370052, by rfl⟩ : syracuseStep 493403 = 740105) B740105
theorem B493679 : Blo 327838 493679 := bstep (se 1 (by rfl) ⟨370259, by rfl⟩ : syracuseStep 493679 = 740519) B740519
theorem B493751 : Blo 327838 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B330047 : Blo 327838 330047 := bstep (se 1 (by rfl) ⟨247535, by rfl⟩ : syracuseStep 330047 = 495071) B495071
theorem B3164507 : Blo 327838 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B330087 : Blo 327838 330087 := bstep (se 1 (by rfl) ⟨247565, by rfl⟩ : syracuseStep 330087 = 495131) B495131
theorem B829865 : Blo 327838 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B1870249 : Blo 327838 1870249 := bstep (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) B1402687
theorem B330175 : Blo 327838 330175 := bstep (se 1 (by rfl) ⟨247631, by rfl⟩ : syracuseStep 330175 = 495263) B495263
theorem B1108457 : Blo 327838 1108457 := bstep (se 2 (by rfl) ⟨415671, by rfl⟩ : syracuseStep 1108457 = 831343) B831343
theorem B494063 : Blo 327838 494063 := bstep (se 1 (by rfl) ⟨370547, by rfl⟩ : syracuseStep 494063 = 741095) B741095
theorem B4557313 : Blo 327838 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B494171 : Blo 327838 494171 := bstep (se 1 (by rfl) ⟨370628, by rfl⟩ : syracuseStep 494171 = 741257) B741257
theorem B330351 : Blo 327838 330351 := bstep (se 1 (by rfl) ⟨247763, by rfl⟩ : syracuseStep 330351 = 495527) B495527
theorem B1403507 : Blo 327838 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B330367 : Blo 327838 330367 := bstep (se 1 (by rfl) ⟨247775, by rfl⟩ : syracuseStep 330367 = 495551) B495551
theorem B330471 : Blo 327838 330471 := bstep (se 1 (by rfl) ⟨247853, by rfl⟩ : syracuseStep 330471 = 495707) B495707
theorem B330567 : Blo 327838 330567 := bstep (se 1 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 330567 = 495851) B495851
theorem B330607 : Blo 327838 330607 := bstep (se 1 (by rfl) ⟨247955, by rfl⟩ : syracuseStep 330607 = 495911) B495911
theorem B10120139 : Blo 327838 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B740303 : Blo 327838 740303 := bstep (se 1 (by rfl) ⟨555227, by rfl⟩ : syracuseStep 740303 = 1110455) B1110455
theorem B625619 : Blo 327838 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B3263597 : Blo 327838 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B1109267 : Blo 327838 1109267 := bstep (se 1 (by rfl) ⟨831950, by rfl⟩ : syracuseStep 1109267 = 1663901) B1663901
theorem B740663 : Blo 327838 740663 := bstep (se 1 (by rfl) ⟨555497, by rfl⟩ : syracuseStep 740663 = 1110995) B1110995
theorem B494903 : Blo 327838 494903 := bstep (se 1 (by rfl) ⟨371177, by rfl⟩ : syracuseStep 494903 = 742355) B742355
theorem B1109483 : Blo 327838 1109483 := bstep (se 1 (by rfl) ⟨832112, by rfl⟩ : syracuseStep 1109483 = 1664225) B1664225
theorem B831131 : Blo 327838 831131 := bstep (se 1 (by rfl) ⟨623348, by rfl⟩ : syracuseStep 831131 = 1246697) B1246697
theorem B1871525 : Blo 327838 1871525 := bstep (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) B350911
theorem B3010231 : Blo 327838 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B700319 : Blo 327838 700319 := bstep (se 1 (by rfl) ⟨525239, by rfl⟩ : syracuseStep 700319 = 1050479) B1050479
theorem B749675 : Blo 327838 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B495743 : Blo 327838 495743 := bstep (se 1 (by rfl) ⟨371807, by rfl⟩ : syracuseStep 495743 = 743615) B743615
theorem B626879 : Blo 327838 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B8138989 : Blo 327838 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B741671 : Blo 327838 741671 := bstep (se 1 (by rfl) ⟨556253, by rfl⟩ : syracuseStep 741671 = 1112507) B1112507
theorem B4731301 : Blo 327838 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B6951349 : Blo 327838 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B14250491 : Blo 327838 14250491 := bstep (se 1 (by rfl) ⟨10687868, by rfl⟩ : syracuseStep 14250491 = 21375737) B21375737
theorem B356911 : Blo 327838 356911 := bstep (se 1 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 356911 = 535367) B535367
theorem B2364011 : Blo 327838 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B742031 : Blo 327838 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B832265 : Blo 327838 832265 := bstep (se 2 (by rfl) ⟨312099, by rfl⟩ : syracuseStep 832265 = 624199) B624199
theorem B553783 : Blo 327838 553783 := bstep (se 1 (by rfl) ⟨415337, by rfl⟩ : syracuseStep 553783 = 830675) B830675
theorem B19502045 : Blo 327838 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B3921095 : Blo 327838 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B743003 : Blo 327838 743003 := bstep (se 1 (by rfl) ⟨557252, by rfl⟩ : syracuseStep 743003 = 1114505) B1114505
theorem B9377491 : Blo 327838 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B1881913 : Blo 327838 1881913 := bstep (se 2 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 1881913 = 1411435) B1411435
theorem B554863 : Blo 327838 554863 := bstep (se 1 (by rfl) ⟨416147, by rfl⟩ : syracuseStep 554863 = 832295) B832295
theorem B1406909 : Blo 327838 1406909 := bstep (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) B527591
theorem B13465601 : Blo 327838 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B563311 : Blo 327838 563311 := bstep (se 1 (by rfl) ⟨422483, by rfl⟩ : syracuseStep 563311 = 844967) B844967
theorem B1407131 : Blo 327838 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B5642459 : Blo 327838 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B555295 : Blo 327838 555295 := bstep (se 1 (by rfl) ⟨416471, by rfl⟩ : syracuseStep 555295 = 832943) B832943
theorem B702847 : Blo 327838 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B891263 : Blo 327838 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B4012667 : Blo 327838 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B1186433 : Blo 327838 1186433 := bstep (se 2 (by rfl) ⟨444912, by rfl⟩ : syracuseStep 1186433 = 889825) B889825
theorem B834239 : Blo 327838 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B1882871 : Blo 327838 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B1424251 : Blo 327838 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B1203175 : Blo 327838 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B51534863 : Blo 327838 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B1056041 : Blo 327838 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B1441097 : Blo 327838 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B703865 : Blo 327838 703865 := bstep (se 2 (by rfl) ⟨263949, by rfl⟩ : syracuseStep 703865 = 527899) B527899
theorem B1883645 : Blo 327838 1883645 := bstep (se 3 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 1883645 = 706367) B706367
theorem B3997487 : Blo 327838 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B45817649 : Blo 327838 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B1408907 : Blo 327838 1408907 := bstep (se 1 (by rfl) ⟨1056680, by rfl⟩ : syracuseStep 1408907 = 2113361) B2113361
theorem B622559 : Blo 327838 622559 := bstep (se 1 (by rfl) ⟨466919, by rfl⟩ : syracuseStep 622559 = 933839) B933839
theorem B5324791 : Blo 327838 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B327839 : Blo 327838 327839 := bstep (se 1 (by rfl) ⟨245879, by rfl⟩ : syracuseStep 327839 = 491759) B491759
theorem B1999133 : Blo 327838 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B2490749 : Blo 327838 2490749 := bstep (se 3 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 2490749 = 934031) B934031
theorem B557543 : Blo 327838 557543 := bstep (se 1 (by rfl) ⟨418157, by rfl⟩ : syracuseStep 557543 = 836315) B836315
theorem B1671677 : Blo 327838 1671677 := bstep (se 3 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 1671677 = 626879) B626879
theorem B737819 : Blo 327838 737819 := bstep (se 1 (by rfl) ⟨553364, by rfl⟩ : syracuseStep 737819 = 1106729) B1106729
theorem B6308401 : Blo 327838 6308401 := bstep (se 2 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 6308401 = 4731301) B4731301
theorem B13001363 : Blo 327838 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B328443 : Blo 327838 328443 := bstep (se 1 (by rfl) ⟨246332, by rfl⟩ : syracuseStep 328443 = 492665) B492665
theorem B328475 : Blo 327838 328475 := bstep (se 1 (by rfl) ⟨246356, by rfl⟩ : syracuseStep 328475 = 492713) B492713
theorem B738287 : Blo 327838 738287 := bstep (se 1 (by rfl) ⟨553715, by rfl⟩ : syracuseStep 738287 = 1107431) B1107431
theorem B2376701 : Blo 327838 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B328731 : Blo 327838 328731 := bstep (se 1 (by rfl) ⟨246548, by rfl⟩ : syracuseStep 328731 = 493097) B493097
theorem B738377 : Blo 327838 738377 := bstep (se 2 (by rfl) ⟨276891, by rfl⟩ : syracuseStep 738377 = 553783) B553783
theorem B328935 : Blo 327838 328935 := bstep (se 1 (by rfl) ⟨246701, by rfl⟩ : syracuseStep 328935 = 493403) B493403
theorem B329119 : Blo 327838 329119 := bstep (se 1 (by rfl) ⟨246839, by rfl⟩ : syracuseStep 329119 = 493679) B493679
theorem B329167 : Blo 327838 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B738971 : Blo 327838 738971 := bstep (se 1 (by rfl) ⟨554228, by rfl⟩ : syracuseStep 738971 = 1108457) B1108457
theorem B329375 : Blo 327838 329375 := bstep (se 1 (by rfl) ⟨247031, by rfl⟩ : syracuseStep 329375 = 494063) B494063
theorem B329447 : Blo 327838 329447 := bstep (se 1 (by rfl) ⟨247085, by rfl⟩ : syracuseStep 329447 = 494171) B494171
theorem B1255247 : Blo 327838 1255247 := bstep (se 1 (by rfl) ⟨941435, by rfl⟩ : syracuseStep 1255247 = 1882871) B1882871
theorem B493535 : Blo 327838 493535 := bstep (se 1 (by rfl) ⟨370151, by rfl⟩ : syracuseStep 493535 = 740303) B740303
theorem B3761639 : Blo 327838 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B739511 : Blo 327838 739511 := bstep (se 1 (by rfl) ⟨554633, by rfl⟩ : syracuseStep 739511 = 1109267) B1109267
theorem B493775 : Blo 327838 493775 := bstep (se 1 (by rfl) ⟨370331, by rfl⟩ : syracuseStep 493775 = 740663) B740663
theorem B329935 : Blo 327838 329935 := bstep (se 1 (by rfl) ⟨247451, by rfl⟩ : syracuseStep 329935 = 494903) B494903
theorem B960731 : Blo 327838 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B469243 : Blo 327838 469243 := bstep (se 1 (by rfl) ⟨351932, by rfl⟩ : syracuseStep 469243 = 703865) B703865
theorem B12503321 : Blo 327838 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B739655 : Blo 327838 739655 := bstep (se 1 (by rfl) ⟨554741, by rfl⟩ : syracuseStep 739655 = 1109483) B1109483
theorem B1255763 : Blo 327838 1255763 := bstep (se 1 (by rfl) ⟨941822, by rfl⟩ : syracuseStep 1255763 = 1883645) B1883645
theorem B2509217 : Blo 327838 2509217 := bstep (se 2 (by rfl) ⟨940956, by rfl⟩ : syracuseStep 2509217 = 1881913) B1881913
theorem B1247683 : Blo 327838 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B739817 : Blo 327838 739817 := bstep (se 2 (by rfl) ⟨277431, by rfl⟩ : syracuseStep 739817 = 554863) B554863
theorem B2664991 : Blo 327838 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B371407 : Blo 327838 371407 := bstep (se 1 (by rfl) ⟨278555, by rfl⟩ : syracuseStep 371407 = 557111) B557111
theorem B330495 : Blo 327838 330495 := bstep (se 1 (by rfl) ⟨247871, by rfl⟩ : syracuseStep 330495 = 495743) B495743
theorem B494447 : Blo 327838 494447 := bstep (se 1 (by rfl) ⟨370835, by rfl⟩ : syracuseStep 494447 = 741671) B741671
theorem B740393 : Blo 327838 740393 := bstep (se 2 (by rfl) ⟨277647, by rfl⟩ : syracuseStep 740393 = 555295) B555295
theorem B1576007 : Blo 327838 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B494687 : Blo 327838 494687 := bstep (se 1 (by rfl) ⟨371015, by rfl⟩ : syracuseStep 494687 = 742031) B742031
theorem B470171 : Blo 327838 470171 := bstep (se 1 (by rfl) ⟨352628, by rfl⟩ : syracuseStep 470171 = 705257) B705257
theorem B10456253 : Blo 327838 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B2493665 : Blo 327838 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B9268465 : Blo 327838 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B3747059 : Blo 327838 3747059 := bstep (se 1 (by rfl) ⟨2810294, by rfl⟩ : syracuseStep 3747059 = 5620589) B5620589
theorem B2501927 : Blo 327838 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B7614101 : Blo 327838 7614101 := bstep (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) B356911
theorem B495335 : Blo 327838 495335 := bstep (se 1 (by rfl) ⟨371501, by rfl⟩ : syracuseStep 495335 = 743003) B743003
theorem B1584983 : Blo 327838 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B831323 : Blo 327838 831323 := bstep (se 1 (by rfl) ⟨623492, by rfl⟩ : syracuseStep 831323 = 1246985) B1246985
theorem B1585097 : Blo 327838 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B937939 : Blo 327838 937939 := bstep (se 1 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 937939 = 1406909) B1406909
theorem B938087 : Blo 327838 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B2109671 : Blo 327838 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B553243 : Blo 327838 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B2675111 : Blo 327838 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B790955 : Blo 327838 790955 := bstep (se 1 (by rfl) ⟨593216, by rfl⟩ : syracuseStep 790955 = 1186433) B1186433
theorem B6746759 : Blo 327838 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B3748517 : Blo 327838 3748517 := bstep (se 4 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 3748517 = 702847) B702847
theorem B2175731 : Blo 327838 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B554087 : Blo 327838 554087 := bstep (se 1 (by rfl) ⟨415565, by rfl⟩ : syracuseStep 554087 = 831131) B831131
theorem B30545099 : Blo 327838 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B939271 : Blo 327838 939271 := bstep (se 1 (by rfl) ⟨704453, by rfl⟩ : syracuseStep 939271 = 1408907) B1408907
theorem B415039 : Blo 327838 415039 := bstep (se 1 (by rfl) ⟨311279, by rfl⟩ : syracuseStep 415039 = 622559) B622559
theorem B7099721 : Blo 327838 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B939431 : Blo 327838 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B742823 : Blo 327838 742823 := bstep (se 1 (by rfl) ⟨557117, by rfl⟩ : syracuseStep 742823 = 1114235) B1114235
theorem B2102699 : Blo 327838 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B751081 : Blo 327838 751081 := bstep (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) B563311
theorem B742931 : Blo 327838 742931 := bstep (se 1 (by rfl) ⟨557198, by rfl⟩ : syracuseStep 742931 = 1114397) B1114397
theorem B10851985 : Blo 327838 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B9500327 : Blo 327838 9500327 := bstep (se 1 (by rfl) ⟨7125245, by rfl⟩ : syracuseStep 9500327 = 14250491) B14250491
theorem B554843 : Blo 327838 554843 := bstep (se 1 (by rfl) ⟨416132, by rfl⟩ : syracuseStep 554843 = 832265) B832265
theorem B6076417 : Blo 327838 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B1907023 : Blo 327838 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B743759 : Blo 327838 743759 := bstep (se 1 (by rfl) ⟨557819, by rfl⟩ : syracuseStep 743759 = 1115639) B1115639
theorem B1899001 : Blo 327838 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B1604233 : Blo 327838 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B8977067 : Blo 327838 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B3742685 : Blo 327838 3742685 := bstep (se 3 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 3742685 = 1403507) B1403507
theorem B556159 : Blo 327838 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B417079 : Blo 327838 417079 := bstep (se 1 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 417079 = 625619) B625619
theorem B34356575 : Blo 327838 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B704027 : Blo 327838 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B4013641 : Blo 327838 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B1269377 : Blo 327838 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B466879 : Blo 327838 466879 := bstep (se 1 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 466879 = 700319) B700319
theorem B8101889 : Blo 327838 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B1114451 : Blo 327838 1114451 := bstep (se 1 (by rfl) ⟨835838, by rfl⟩ : syracuseStep 1114451 = 1671677) B1671677
theorem B491879 : Blo 327838 491879 := bstep (se 1 (by rfl) ⟨368909, by rfl⟩ : syracuseStep 491879 = 737819) B737819
theorem B737657 : Blo 327838 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B1253789 : Blo 327838 1253789 := bstep (se 3 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 1253789 = 470171) B470171
theorem B4497839 : Blo 327838 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B8667575 : Blo 327838 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B2499011 : Blo 327838 2499011 := bstep (se 1 (by rfl) ⟨1874258, by rfl⟩ : syracuseStep 2499011 = 3748517) B3748517
theorem B1450487 : Blo 327838 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B1663577 : Blo 327838 1663577 := bstep (se 2 (by rfl) ⟨623841, by rfl⟩ : syracuseStep 1663577 = 1247683) B1247683
theorem B492191 : Blo 327838 492191 := bstep (se 1 (by rfl) ⟨369143, by rfl⟩ : syracuseStep 492191 = 738287) B738287
theorem B2532001 : Blo 327838 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B492251 : Blo 327838 492251 := bstep (se 1 (by rfl) ⟨369188, by rfl⟩ : syracuseStep 492251 = 738377) B738377
theorem B369391 : Blo 327838 369391 := bstep (se 1 (by rfl) ⟨277043, by rfl⟩ : syracuseStep 369391 = 554087) B554087
theorem B2138977 : Blo 327838 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B1401799 : Blo 327838 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B2507759 : Blo 327838 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B492647 : Blo 327838 492647 := bstep (se 1 (by rfl) ⟨369485, by rfl⟩ : syracuseStep 492647 = 738971) B738971
theorem B6333551 : Blo 327838 6333551 := bstep (se 1 (by rfl) ⟨4750163, by rfl⟩ : syracuseStep 6333551 = 9500327) B9500327
theorem B836831 : Blo 327838 836831 := bstep (se 1 (by rfl) ⟨627623, by rfl⟩ : syracuseStep 836831 = 1255247) B1255247
theorem B369895 : Blo 327838 369895 := bstep (se 1 (by rfl) ⟨277421, by rfl⟩ : syracuseStep 369895 = 554843) B554843
theorem B329023 : Blo 327838 329023 := bstep (se 1 (by rfl) ⟨246767, by rfl⟩ : syracuseStep 329023 = 493535) B493535
theorem B493007 : Blo 327838 493007 := bstep (se 1 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 493007 = 739511) B739511
theorem B329183 : Blo 327838 329183 := bstep (se 1 (by rfl) ⟨246887, by rfl⟩ : syracuseStep 329183 = 493775) B493775
theorem B640487 : Blo 327838 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B493103 : Blo 327838 493103 := bstep (se 1 (by rfl) ⟨369827, by rfl⟩ : syracuseStep 493103 = 739655) B739655
theorem B837175 : Blo 327838 837175 := bstep (se 1 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 837175 = 1255763) B1255763
theorem B1672811 : Blo 327838 1672811 := bstep (se 1 (by rfl) ⟨1254608, by rfl⟩ : syracuseStep 1672811 = 2509217) B2509217
theorem B493211 : Blo 327838 493211 := bstep (se 1 (by rfl) ⟨369908, by rfl⟩ : syracuseStep 493211 = 739817) B739817
theorem B329631 : Blo 327838 329631 := bstep (se 1 (by rfl) ⟨247223, by rfl⟩ : syracuseStep 329631 = 494447) B494447
theorem B1001441 : Blo 327838 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B493595 : Blo 327838 493595 := bstep (se 1 (by rfl) ⟨370196, by rfl⟩ : syracuseStep 493595 = 740393) B740393
theorem B1050671 : Blo 327838 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B329791 : Blo 327838 329791 := bstep (se 1 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 329791 = 494687) B494687
theorem B5351521 : Blo 327838 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B14469313 : Blo 327838 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B469351 : Blo 327838 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B846251 : Blo 327838 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B330223 : Blo 327838 330223 := bstep (se 1 (by rfl) ⟨247667, by rfl⟩ : syracuseStep 330223 = 495335) B495335
theorem B625391 : Blo 327838 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B527303 : Blo 327838 527303 := bstep (se 1 (by rfl) ⟨395477, by rfl⟩ : syracuseStep 527303 = 790955) B790955
theorem B371695 : Blo 327838 371695 := bstep (se 1 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 371695 = 557543) B557543
theorem B625657 : Blo 327838 625657 := bstep (se 2 (by rfl) ⟨234621, by rfl⟩ : syracuseStep 625657 = 469243) B469243
theorem B2542697 : Blo 327838 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B1584467 : Blo 327838 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B495209 : Blo 327838 495209 := bstep (se 2 (by rfl) ⟨185703, by rfl⟩ : syracuseStep 495209 = 371407) B371407
theorem B626287 : Blo 327838 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B495215 : Blo 327838 495215 := bstep (se 1 (by rfl) ⟨371411, by rfl⟩ : syracuseStep 495215 = 742823) B742823
theorem B495287 : Blo 327838 495287 := bstep (se 1 (by rfl) ⟨371465, by rfl⟩ : syracuseStep 495287 = 742931) B742931
theorem B741545 : Blo 327838 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B8335547 : Blo 327838 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B495839 : Blo 327838 495839 := bstep (se 1 (by rfl) ⟨371879, by rfl⟩ : syracuseStep 495839 = 743759) B743759
theorem B12357953 : Blo 327838 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B20304269 : Blo 327838 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B553385 : Blo 327838 553385 := bstep (se 2 (by rfl) ⟨207519, by rfl⟩ : syracuseStep 553385 = 415039) B415039
theorem B5984711 : Blo 327838 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B2495123 : Blo 327838 2495123 := bstep (se 1 (by rfl) ⟨1871342, by rfl⟩ : syracuseStep 2495123 = 3742685) B3742685
theorem B1667951 : Blo 327838 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B554215 : Blo 327838 554215 := bstep (se 1 (by rfl) ⟨415661, by rfl⟩ : syracuseStep 554215 = 831323) B831323
theorem B1250585 : Blo 327838 1250585 := bstep (se 2 (by rfl) ⟨468969, by rfl⟩ : syracuseStep 1250585 = 937939) B937939
theorem B1406447 : Blo 327838 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B1332755 : Blo 327838 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B1660499 : Blo 327838 1660499 := bstep (se 1 (by rfl) ⟨1245374, by rfl⟩ : syracuseStep 1660499 = 2490749) B2490749
theorem B3553321 : Blo 327838 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B8411201 : Blo 327838 8411201 := bstep (se 2 (by rfl) ⟨3154200, by rfl⟩ : syracuseStep 8411201 = 6308401) B6308401
theorem B20363399 : Blo 327838 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B4733147 : Blo 327838 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B7133629 : Blo 327838 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B1252361 : Blo 327838 1252361 := bstep (se 2 (by rfl) ⟨469635, by rfl⟩ : syracuseStep 1252361 = 939271) B939271
theorem B556105 : Blo 327838 556105 := bstep (se 2 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 556105 = 417079) B417079
theorem B6970835 : Blo 327838 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B1662443 : Blo 327838 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B2498039 : Blo 327838 2498039 := bstep (se 1 (by rfl) ⟨1873529, by rfl⟩ : syracuseStep 2498039 = 3747059) B3747059
theorem B22904383 : Blo 327838 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B1056655 : Blo 327838 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B622505 : Blo 327838 622505 := bstep (se 2 (by rfl) ⟨233439, by rfl⟩ : syracuseStep 622505 = 466879) B466879
theorem B1056731 : Blo 327838 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B2801789 : Blo 327838 2801789 := bstep (se 3 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 2801789 = 1050671) B1050671
theorem B7135361 : Blo 327838 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B327919 : Blo 327838 327919 := bstep (se 1 (by rfl) ⟨245939, by rfl⟩ : syracuseStep 327919 = 491879) B491879
theorem B491771 : Blo 327838 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B19292417 : Blo 327838 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B835859 : Blo 327838 835859 := bstep (se 1 (by rfl) ⟨626894, by rfl⟩ : syracuseStep 835859 = 1253789) B1253789
theorem B368923 : Blo 327838 368923 := bstep (se 1 (by rfl) ⟨276692, by rfl⟩ : syracuseStep 368923 = 553385) B553385
theorem B2998559 : Blo 327838 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B3989807 : Blo 327838 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B966991 : Blo 327838 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B1663415 : Blo 327838 1663415 := bstep (se 1 (by rfl) ⟨1247561, by rfl⟩ : syracuseStep 1663415 = 2495123) B2495123
theorem B328127 : Blo 327838 328127 := bstep (se 1 (by rfl) ⟨246095, by rfl⟩ : syracuseStep 328127 = 492191) B492191
theorem B328167 : Blo 327838 328167 := bstep (se 1 (by rfl) ⟨246125, by rfl⟩ : syracuseStep 328167 = 492251) B492251
theorem B9511505 : Blo 327838 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B1671839 : Blo 327838 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B328431 : Blo 327838 328431 := bstep (se 1 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 328431 = 492647) B492647
theorem B3376001 : Blo 327838 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B328671 : Blo 327838 328671 := bstep (se 1 (by rfl) ⟨246503, by rfl⟩ : syracuseStep 328671 = 493007) B493007
theorem B492521 : Blo 327838 492521 := bstep (se 2 (by rfl) ⟨184695, by rfl⟩ : syracuseStep 492521 = 369391) B369391
theorem B328735 : Blo 327838 328735 := bstep (se 1 (by rfl) ⟨246551, by rfl⟩ : syracuseStep 328735 = 493103) B493103
theorem B1106999 : Blo 327838 1106999 := bstep (se 1 (by rfl) ⟨830249, by rfl⟩ : syracuseStep 1106999 = 1660499) B1660499
theorem B1115207 : Blo 327838 1115207 := bstep (se 1 (by rfl) ⟨836405, by rfl⟩ : syracuseStep 1115207 = 1672811) B1672811
theorem B328807 : Blo 327838 328807 := bstep (se 1 (by rfl) ⟨246605, by rfl⟩ : syracuseStep 328807 = 493211) B493211
theorem B2851969 : Blo 327838 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B1869065 : Blo 327838 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B329063 : Blo 327838 329063 := bstep (se 1 (by rfl) ⟨246797, by rfl⟩ : syracuseStep 329063 = 493595) B493595
theorem B13575599 : Blo 327838 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B3155431 : Blo 327838 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B738953 : Blo 327838 738953 := bstep (se 2 (by rfl) ⟨277107, by rfl⟩ : syracuseStep 738953 = 554215) B554215
theorem B493193 : Blo 327838 493193 := bstep (se 2 (by rfl) ⟨184947, by rfl⟩ : syracuseStep 493193 = 369895) B369895
theorem B1116233 : Blo 327838 1116233 := bstep (se 2 (by rfl) ⟨418587, by rfl⟩ : syracuseStep 1116233 = 837175) B837175
theorem B4647223 : Blo 327838 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1108295 : Blo 327838 1108295 := bstep (se 1 (by rfl) ⟨831221, by rfl⟩ : syracuseStep 1108295 = 1662443) B1662443
theorem B1665359 : Blo 327838 1665359 := bstep (se 1 (by rfl) ⟨1249019, by rfl⟩ : syracuseStep 1665359 = 2498039) B2498039
theorem B330139 : Blo 327838 330139 := bstep (se 1 (by rfl) ⟨247604, by rfl⟩ : syracuseStep 330139 = 495209) B495209
theorem B330143 : Blo 327838 330143 := bstep (se 1 (by rfl) ⟨247607, by rfl⟩ : syracuseStep 330143 = 495215) B495215
theorem B330191 : Blo 327838 330191 := bstep (se 1 (by rfl) ⟨247643, by rfl⟩ : syracuseStep 330191 = 495287) B495287
theorem B5401259 : Blo 327838 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B4737761 : Blo 327838 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B494363 : Blo 327838 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B5557031 : Blo 327838 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B330559 : Blo 327838 330559 := bstep (se 1 (by rfl) ⟨247919, by rfl⟩ : syracuseStep 330559 = 495839) B495839
theorem B13536179 : Blo 327838 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B5778383 : Blo 327838 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B1666007 : Blo 327838 1666007 := bstep (se 1 (by rfl) ⟨1249505, by rfl⟩ : syracuseStep 1666007 = 2499011) B2499011
theorem B1109051 : Blo 327838 1109051 := bstep (se 1 (by rfl) ⟨831788, by rfl⟩ : syracuseStep 1109051 = 1663577) B1663577
theorem B625801 : Blo 327838 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B4222367 : Blo 327838 4222367 := bstep (se 1 (by rfl) ⟨3166775, by rfl⟩ : syracuseStep 4222367 = 6333551) B6333551
theorem B937631 : Blo 327838 937631 := bstep (se 1 (by rfl) ⟨703223, by rfl⟩ : syracuseStep 937631 = 1406447) B1406447
theorem B888503 : Blo 327838 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B1707965 : Blo 327838 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B495593 : Blo 327838 495593 := bstep (se 2 (by rfl) ⟨185847, by rfl⟩ : syracuseStep 495593 = 371695) B371695
theorem B5607467 : Blo 327838 5607467 := bstep (se 1 (by rfl) ⟨4205600, by rfl⟩ : syracuseStep 5607467 = 8411201) B8411201
theorem B741473 : Blo 327838 741473 := bstep (se 2 (by rfl) ⟨278052, by rfl⟩ : syracuseStep 741473 = 556105) B556105
theorem B557887 : Blo 327838 557887 := bstep (se 1 (by rfl) ⟨418415, by rfl⟩ : syracuseStep 557887 = 836831) B836831
theorem B1660013 : Blo 327838 1660013 := bstep (se 3 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 1660013 = 622505) B622505
theorem B8238635 : Blo 327838 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B742967 : Blo 327838 742967 := bstep (se 1 (by rfl) ⟨557225, by rfl⟩ : syracuseStep 742967 = 1114451) B1114451
theorem B1111967 : Blo 327838 1111967 := bstep (se 1 (by rfl) ⟨833975, by rfl⟩ : syracuseStep 1111967 = 1667951) B1667951
theorem B833723 : Blo 327838 833723 := bstep (se 1 (by rfl) ⟨625292, by rfl⟩ : syracuseStep 833723 = 1250585) B1250585
theorem B834209 : Blo 327838 834209 := bstep (se 2 (by rfl) ⟨312828, by rfl⟩ : syracuseStep 834209 = 625657) B625657
theorem B564167 : Blo 327838 564167 := bstep (se 1 (by rfl) ⟨423125, by rfl⟩ : syracuseStep 564167 = 846251) B846251
theorem B416927 : Blo 327838 416927 := bstep (se 1 (by rfl) ⟨312695, by rfl⟩ : syracuseStep 416927 = 625391) B625391
theorem B351535 : Blo 327838 351535 := bstep (se 1 (by rfl) ⟨263651, by rfl⟩ : syracuseStep 351535 = 527303) B527303
theorem B834907 : Blo 327838 834907 := bstep (se 1 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 834907 = 1252361) B1252361
theorem B1695131 : Blo 327838 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B30539177 : Blo 327838 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B835049 : Blo 327838 835049 := bstep (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) B626287
theorem B1056311 : Blo 327838 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B1408873 : Blo 327838 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B2817949 : Blo 327838 2817949 := bstep (se 3 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 2817949 = 1056731) B1056731
theorem B2670509 : Blo 327838 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B1867859 : Blo 327838 1867859 := bstep (se 1 (by rfl) ⟨1400894, by rfl⟩ : syracuseStep 1867859 = 2801789) B2801789
theorem B327847 : Blo 327838 327847 := bstep (se 1 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 327847 = 491771) B491771
theorem B12861611 : Blo 327838 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B557239 : Blo 327838 557239 := bstep (se 1 (by rfl) ⟨417929, by rfl⟩ : syracuseStep 557239 = 835859) B835859
theorem B1999039 : Blo 327838 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B491897 : Blo 327838 491897 := bstep (se 2 (by rfl) ⟨184461, by rfl⟩ : syracuseStep 491897 = 368923) B368923
theorem B6341003 : Blo 327838 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B1114559 : Blo 327838 1114559 := bstep (se 1 (by rfl) ⟨835919, by rfl⟩ : syracuseStep 1114559 = 1671839) B1671839
theorem B328347 : Blo 327838 328347 := bstep (se 1 (by rfl) ⟨246260, by rfl⟩ : syracuseStep 328347 = 492521) B492521
theorem B737999 : Blo 327838 737999 := bstep (se 1 (by rfl) ⟨553499, by rfl⟩ : syracuseStep 737999 = 1106999) B1106999
theorem B1106675 : Blo 327838 1106675 := bstep (se 1 (by rfl) ⟨830006, by rfl⟩ : syracuseStep 1106675 = 1660013) B1660013
theorem B1246043 : Blo 327838 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B492635 : Blo 327838 492635 := bstep (se 1 (by rfl) ⟨369476, by rfl⟩ : syracuseStep 492635 = 738953) B738953
theorem B328795 : Blo 327838 328795 := bstep (se 1 (by rfl) ⟨246596, by rfl⟩ : syracuseStep 328795 = 493193) B493193
theorem B3802625 : Blo 327838 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B738863 : Blo 327838 738863 := bstep (se 1 (by rfl) ⟨554147, by rfl⟩ : syracuseStep 738863 = 1108295) B1108295
theorem B468713 : Blo 327838 468713 := bstep (se 2 (by rfl) ⟨175767, by rfl⟩ : syracuseStep 468713 = 351535) B351535
theorem B2369341 : Blo 327838 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B329575 : Blo 327838 329575 := bstep (se 1 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 329575 = 494363) B494363
theorem B3704687 : Blo 327838 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B739367 : Blo 327838 739367 := bstep (se 1 (by rfl) ⟨554525, by rfl⟩ : syracuseStep 739367 = 1109051) B1109051
theorem B20359451 : Blo 327838 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B625087 : Blo 327838 625087 := bstep (se 1 (by rfl) ⟨468815, by rfl⟩ : syracuseStep 625087 = 937631) B937631
theorem B1878497 : Blo 327838 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B1780339 : Blo 327838 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B330395 : Blo 327838 330395 := bstep (se 1 (by rfl) ⟨247796, by rfl⟩ : syracuseStep 330395 = 495593) B495593
theorem B3738311 : Blo 327838 3738311 := bstep (se 1 (by rfl) ⟨2803733, by rfl⟩ : syracuseStep 3738311 = 5607467) B5607467
theorem B494315 : Blo 327838 494315 := bstep (se 1 (by rfl) ⟨370736, by rfl⟩ : syracuseStep 494315 = 741473) B741473
theorem B1108943 : Blo 327838 1108943 := bstep (se 1 (by rfl) ⟨831707, by rfl⟩ : syracuseStep 1108943 = 1663415) B1663415
theorem B1289321 : Blo 327838 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B5492423 : Blo 327838 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B495311 : Blo 327838 495311 := bstep (se 1 (by rfl) ⟨371483, by rfl⟩ : syracuseStep 495311 = 742967) B742967
theorem B741311 : Blo 327838 741311 := bstep (se 1 (by rfl) ⟨555983, by rfl⟩ : syracuseStep 741311 = 1111967) B1111967
theorem B1110239 : Blo 327838 1110239 := bstep (se 1 (by rfl) ⟨832679, by rfl⟩ : syracuseStep 1110239 = 1665359) B1665359
theorem B24785189 : Blo 327838 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B3600839 : Blo 327838 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B3158507 : Blo 327838 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B9024119 : Blo 327838 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B4207241 : Blo 327838 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B1110671 : Blo 327838 1110671 := bstep (se 1 (by rfl) ⟨833003, by rfl⟩ : syracuseStep 1110671 = 1666007) B1666007
theorem B2814911 : Blo 327838 2814911 := bstep (se 1 (by rfl) ⟨2111183, by rfl⟩ : syracuseStep 2814911 = 4222367) B4222367
theorem B3757265 : Blo 327838 3757265 := bstep (se 2 (by rfl) ⟨1408974, by rfl⟩ : syracuseStep 3757265 = 2817949) B2817949
theorem B4756907 : Blo 327838 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B2659871 : Blo 327838 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B1111805 : Blo 327838 1111805 := bstep (se 3 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 1111805 = 416927) B416927
theorem B2250667 : Blo 327838 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B743471 : Blo 327838 743471 := bstep (se 1 (by rfl) ⟨557603, by rfl⟩ : syracuseStep 743471 = 1115207) B1115207
theorem B9050399 : Blo 327838 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B743849 : Blo 327838 743849 := bstep (se 2 (by rfl) ⟨278943, by rfl⟩ : syracuseStep 743849 = 557887) B557887
theorem B744155 : Blo 327838 744155 := bstep (se 1 (by rfl) ⟨558116, by rfl⟩ : syracuseStep 744155 = 1116233) B1116233
theorem B555815 : Blo 327838 555815 := bstep (se 1 (by rfl) ⟨416861, by rfl⟩ : syracuseStep 555815 = 833723) B833723
theorem B834401 : Blo 327838 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B556139 : Blo 327838 556139 := bstep (se 1 (by rfl) ⟨417104, by rfl⟩ : syracuseStep 556139 = 834209) B834209
theorem B1113209 : Blo 327838 1113209 := bstep (se 2 (by rfl) ⟨417453, by rfl⟩ : syracuseStep 1113209 = 834907) B834907
theorem B376111 : Blo 327838 376111 := bstep (se 1 (by rfl) ⟨282083, by rfl⟩ : syracuseStep 376111 = 564167) B564167
theorem B61636085 : Blo 327838 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B1130087 : Blo 327838 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B556699 : Blo 327838 556699 := bstep (se 1 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 556699 = 835049) B835049
theorem B704207 : Blo 327838 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B1138643 : Blo 327838 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B1245239 : Blo 327838 1245239 := bstep (se 1 (by rfl) ⟨933929, by rfl⟩ : syracuseStep 1245239 = 1867859) B1867859
theorem B16523459 : Blo 327838 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B327931 : Blo 327838 327931 := bstep (se 1 (by rfl) ⟨245948, by rfl⟩ : syracuseStep 327931 = 491897) B491897
theorem B4227335 : Blo 327838 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B2400559 : Blo 327838 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B2105671 : Blo 327838 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B491999 : Blo 327838 491999 := bstep (se 1 (by rfl) ⟨368999, by rfl⟩ : syracuseStep 491999 = 737999) B737999
theorem B737783 : Blo 327838 737783 := bstep (se 1 (by rfl) ⟨553337, by rfl⟩ : syracuseStep 737783 = 1106675) B1106675
theorem B1876607 : Blo 327838 1876607 := bstep (se 1 (by rfl) ⟨1407455, by rfl⟩ : syracuseStep 1876607 = 2814911) B2814911
theorem B328423 : Blo 327838 328423 := bstep (se 1 (by rfl) ⟨246317, by rfl⟩ : syracuseStep 328423 = 492635) B492635
theorem B3171271 : Blo 327838 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B492575 : Blo 327838 492575 := bstep (se 1 (by rfl) ⟨369431, by rfl⟩ : syracuseStep 492575 = 738863) B738863
theorem B492911 : Blo 327838 492911 := bstep (se 1 (by rfl) ⟨369683, by rfl⟩ : syracuseStep 492911 = 739367) B739367
theorem B501481 : Blo 327838 501481 := bstep (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) B376111
theorem B2492207 : Blo 327838 2492207 := bstep (se 1 (by rfl) ⟨1869155, by rfl⟩ : syracuseStep 2492207 = 3738311) B3738311
theorem B329543 : Blo 327838 329543 := bstep (se 1 (by rfl) ⟨247157, by rfl⟩ : syracuseStep 329543 = 494315) B494315
theorem B370543 : Blo 327838 370543 := bstep (se 1 (by rfl) ⟨277907, by rfl⟩ : syracuseStep 370543 = 555815) B555815
theorem B739295 : Blo 327838 739295 := bstep (se 1 (by rfl) ⟨554471, by rfl⟩ : syracuseStep 739295 = 1108943) B1108943
theorem B370759 : Blo 327838 370759 := bstep (se 1 (by rfl) ⟨278069, by rfl⟩ : syracuseStep 370759 = 556139) B556139
theorem B469471 : Blo 327838 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B330207 : Blo 327838 330207 := bstep (se 1 (by rfl) ⟨247655, by rfl⟩ : syracuseStep 330207 = 495311) B495311
theorem B3000889 : Blo 327838 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B494207 : Blo 327838 494207 := bstep (se 1 (by rfl) ⟨370655, by rfl⟩ : syracuseStep 494207 = 741311) B741311
theorem B740159 : Blo 327838 740159 := bstep (se 1 (by rfl) ⟨555119, by rfl⟩ : syracuseStep 740159 = 1110239) B1110239
theorem B2665385 : Blo 327838 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B6016079 : Blo 327838 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B2804827 : Blo 327838 2804827 := bstep (se 1 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 2804827 = 4207241) B4207241
theorem B740447 : Blo 327838 740447 := bstep (se 1 (by rfl) ⟨555335, by rfl⟩ : syracuseStep 740447 = 1110671) B1110671
theorem B830695 : Blo 327838 830695 := bstep (se 1 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 830695 = 1246043) B1246043
theorem B2535083 : Blo 327838 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B1773247 : Blo 327838 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B741203 : Blo 327838 741203 := bstep (se 1 (by rfl) ⟨555902, by rfl⟩ : syracuseStep 741203 = 1111805) B1111805
theorem B2469791 : Blo 327838 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B495647 : Blo 327838 495647 := bstep (se 1 (by rfl) ⟨371735, by rfl⟩ : syracuseStep 495647 = 743471) B743471
theorem B6033599 : Blo 327838 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B495899 : Blo 327838 495899 := bstep (se 1 (by rfl) ⟨371924, by rfl⟩ : syracuseStep 495899 = 743849) B743849
theorem B12636485 : Blo 327838 12636485 := bstep (se 4 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 12636485 = 2369341) B2369341
theorem B496103 : Blo 327838 496103 := bstep (se 1 (by rfl) ⟨372077, by rfl⟩ : syracuseStep 496103 = 744155) B744155
theorem B1249901 : Blo 327838 1249901 := bstep (se 3 (by rfl) ⟨234356, by rfl⟩ : syracuseStep 1249901 = 468713) B468713
theorem B742139 : Blo 327838 742139 := bstep (se 1 (by rfl) ⟨556604, by rfl⟩ : syracuseStep 742139 = 1113209) B1113209
theorem B742265 : Blo 327838 742265 := bstep (se 2 (by rfl) ⟨278349, by rfl⟩ : syracuseStep 742265 = 556699) B556699
theorem B759095 : Blo 327838 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B8574407 : Blo 327838 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B742985 : Blo 327838 742985 := bstep (se 2 (by rfl) ⟨278619, by rfl⟩ : syracuseStep 742985 = 557239) B557239
theorem B743039 : Blo 327838 743039 := bstep (se 1 (by rfl) ⟨557279, by rfl⟩ : syracuseStep 743039 = 1114559) B1114559
theorem B833449 : Blo 327838 833449 := bstep (se 2 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 833449 = 625087) B625087
theorem B2504843 : Blo 327838 2504843 := bstep (se 1 (by rfl) ⟨1878632, by rfl⟩ : syracuseStep 2504843 = 3757265) B3757265
theorem B2373785 : Blo 327838 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B13572967 : Blo 327838 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B1252331 : Blo 327838 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B556267 : Blo 327838 556267 := bstep (se 1 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 556267 = 834401) B834401
theorem B859547 : Blo 327838 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B41090723 : Blo 327838 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B753391 : Blo 327838 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B3661615 : Blo 327838 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B4022399 : Blo 327838 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B2818223 : Blo 327838 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B327999 : Blo 327838 327999 := bstep (se 1 (by rfl) ⟨245999, by rfl⟩ : syracuseStep 327999 = 491999) B491999
theorem B491855 : Blo 327838 491855 := bstep (se 1 (by rfl) ⟨368891, by rfl⟩ : syracuseStep 491855 = 737783) B737783
theorem B328383 : Blo 327838 328383 := bstep (se 1 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 328383 = 492575) B492575
theorem B328607 : Blo 327838 328607 := bstep (se 1 (by rfl) ⟨246455, by rfl⟩ : syracuseStep 328607 = 492911) B492911
theorem B18097289 : Blo 327838 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B4228361 : Blo 327838 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B492863 : Blo 327838 492863 := bstep (se 1 (by rfl) ⟨369647, by rfl⟩ : syracuseStep 492863 = 739295) B739295
theorem B1582523 : Blo 327838 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B1107593 : Blo 327838 1107593 := bstep (se 2 (by rfl) ⟨415347, by rfl⟩ : syracuseStep 1107593 = 830695) B830695
theorem B329471 : Blo 327838 329471 := bstep (se 1 (by rfl) ⟨247103, by rfl⟩ : syracuseStep 329471 = 494207) B494207
theorem B493439 : Blo 327838 493439 := bstep (se 1 (by rfl) ⟨370079, by rfl⟩ : syracuseStep 493439 = 740159) B740159
theorem B493631 : Blo 327838 493631 := bstep (se 1 (by rfl) ⟨370223, by rfl⟩ : syracuseStep 493631 = 740447) B740447
theorem B1690055 : Blo 327838 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B494057 : Blo 327838 494057 := bstep (se 2 (by rfl) ⟨185271, by rfl⟩ : syracuseStep 494057 = 370543) B370543
theorem B494135 : Blo 327838 494135 := bstep (se 1 (by rfl) ⟨370601, by rfl⟩ : syracuseStep 494135 = 741203) B741203
theorem B330431 : Blo 327838 330431 := bstep (se 1 (by rfl) ⟨247823, by rfl⟩ : syracuseStep 330431 = 495647) B495647
theorem B830159 : Blo 327838 830159 := bstep (se 1 (by rfl) ⟨622619, by rfl⟩ : syracuseStep 830159 = 1245239) B1245239
theorem B494345 : Blo 327838 494345 := bstep (se 2 (by rfl) ⟨185379, by rfl⟩ : syracuseStep 494345 = 370759) B370759
theorem B330599 : Blo 327838 330599 := bstep (se 1 (by rfl) ⟨247949, by rfl⟩ : syracuseStep 330599 = 495899) B495899
theorem B8424323 : Blo 327838 8424323 := bstep (se 1 (by rfl) ⟨6318242, by rfl⟩ : syracuseStep 8424323 = 12636485) B12636485
theorem B330735 : Blo 327838 330735 := bstep (se 1 (by rfl) ⟨248051, by rfl⟩ : syracuseStep 330735 = 496103) B496103
theorem B494759 : Blo 327838 494759 := bstep (se 1 (by rfl) ⟨371069, by rfl⟩ : syracuseStep 494759 = 742139) B742139
theorem B494843 : Blo 327838 494843 := bstep (se 1 (by rfl) ⟨371132, by rfl⟩ : syracuseStep 494843 = 742265) B742265
theorem B625961 : Blo 327838 625961 := bstep (se 2 (by rfl) ⟨234735, by rfl⟩ : syracuseStep 625961 = 469471) B469471
theorem B4001185 : Blo 327838 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B495323 : Blo 327838 495323 := bstep (se 1 (by rfl) ⟨371492, by rfl⟩ : syracuseStep 495323 = 742985) B742985
theorem B495359 : Blo 327838 495359 := bstep (se 1 (by rfl) ⟨371519, by rfl⟩ : syracuseStep 495359 = 743039) B743039
theorem B2674565 : Blo 327838 2674565 := bstep (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) B501481
theorem B3739769 : Blo 327838 3739769 := bstep (se 2 (by rfl) ⟨1402413, by rfl⟩ : syracuseStep 3739769 = 2804827) B2804827
theorem B741689 : Blo 327838 741689 := bstep (se 2 (by rfl) ⟨278133, by rfl⟩ : syracuseStep 741689 = 556267) B556267
theorem B4010719 : Blo 327838 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B2364329 : Blo 327838 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B1004521 : Blo 327838 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B1111265 : Blo 327838 1111265 := bstep (se 2 (by rfl) ⟨416724, by rfl⟩ : syracuseStep 1111265 = 833449) B833449
theorem B11015639 : Blo 327838 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B833267 : Blo 327838 833267 := bstep (se 1 (by rfl) ⟨624950, by rfl⟩ : syracuseStep 833267 = 1249901) B1249901
theorem B1251071 : Blo 327838 1251071 := bstep (se 1 (by rfl) ⟨938303, by rfl⟩ : syracuseStep 1251071 = 1876607) B1876607
theorem B2807561 : Blo 327838 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B506063 : Blo 327838 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B5716271 : Blo 327838 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B1661471 : Blo 327838 1661471 := bstep (se 1 (by rfl) ⟨1246103, by rfl⟩ : syracuseStep 1661471 = 2492207) B2492207
theorem B1669895 : Blo 327838 1669895 := bstep (se 1 (by rfl) ⟨1252421, by rfl⟩ : syracuseStep 1669895 = 2504843) B2504843
theorem B12802981 : Blo 327838 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B19528613 : Blo 327838 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B1776923 : Blo 327838 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B834887 : Blo 327838 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B573031 : Blo 327838 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B27393815 : Blo 327838 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B1646527 : Blo 327838 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B327903 : Blo 327838 327903 := bstep (se 1 (by rfl) ⟨245927, by rfl⟩ : syracuseStep 327903 = 491855) B491855
theorem B328575 : Blo 327838 328575 := bstep (se 1 (by rfl) ⟨246431, by rfl⟩ : syracuseStep 328575 = 492863) B492863
theorem B738395 : Blo 327838 738395 := bstep (se 1 (by rfl) ⟨553796, by rfl⟩ : syracuseStep 738395 = 1107593) B1107593
theorem B328959 : Blo 327838 328959 := bstep (se 1 (by rfl) ⟨246719, by rfl⟩ : syracuseStep 328959 = 493439) B493439
theorem B329087 : Blo 327838 329087 := bstep (se 1 (by rfl) ⟨246815, by rfl⟩ : syracuseStep 329087 = 493631) B493631
theorem B337375 : Blo 327838 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B329371 : Blo 327838 329371 := bstep (se 1 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 329371 = 494057) B494057
theorem B1107647 : Blo 327838 1107647 := bstep (se 1 (by rfl) ⟨830735, by rfl⟩ : syracuseStep 1107647 = 1661471) B1661471
theorem B329423 : Blo 327838 329423 := bstep (se 1 (by rfl) ⟨247067, by rfl⟩ : syracuseStep 329423 = 494135) B494135
theorem B329563 : Blo 327838 329563 := bstep (se 1 (by rfl) ⟨247172, by rfl⟩ : syracuseStep 329563 = 494345) B494345
theorem B5334913 : Blo 327838 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B13019075 : Blo 327838 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B329839 : Blo 327838 329839 := bstep (se 1 (by rfl) ⟨247379, by rfl⟩ : syracuseStep 329839 = 494759) B494759
theorem B764041 : Blo 327838 764041 := bstep (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) B573031
theorem B329895 : Blo 327838 329895 := bstep (se 1 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 329895 = 494843) B494843
theorem B2818907 : Blo 327838 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B330215 : Blo 327838 330215 := bstep (se 1 (by rfl) ⟨247661, by rfl⟩ : syracuseStep 330215 = 495323) B495323
theorem B330239 : Blo 327838 330239 := bstep (se 1 (by rfl) ⟨247679, by rfl⟩ : syracuseStep 330239 = 495359) B495359
theorem B18262543 : Blo 327838 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B2493179 : Blo 327838 2493179 := bstep (se 1 (by rfl) ⟨1869884, by rfl⟩ : syracuseStep 2493179 = 3739769) B3739769
theorem B2681599 : Blo 327838 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B1878815 : Blo 327838 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B494459 : Blo 327838 494459 := bstep (se 1 (by rfl) ⟨370844, by rfl⟩ : syracuseStep 494459 = 741689) B741689
theorem B1576219 : Blo 327838 1576219 := bstep (se 1 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 1576219 = 2364329) B2364329
theorem B740843 : Blo 327838 740843 := bstep (se 1 (by rfl) ⟨555632, by rfl⟩ : syracuseStep 740843 = 1111265) B1111265
theorem B7343759 : Blo 327838 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B1871707 : Blo 327838 1871707 := bstep (se 1 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 1871707 = 2807561) B2807561
theorem B1339361 : Blo 327838 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B1126703 : Blo 327838 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B553439 : Blo 327838 553439 := bstep (se 1 (by rfl) ⟨415079, by rfl⟩ : syracuseStep 553439 = 830159) B830159
theorem B5616215 : Blo 327838 5616215 := bstep (se 1 (by rfl) ⟨4212161, by rfl⟩ : syracuseStep 5616215 = 8424323) B8424323
theorem B1184615 : Blo 327838 1184615 := bstep (se 1 (by rfl) ⟨888461, by rfl⟩ : syracuseStep 1184615 = 1776923) B1776923
theorem B1783043 : Blo 327838 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B12064859 : Blo 327838 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B15243389 : Blo 327838 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B1055015 : Blo 327838 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B5347625 : Blo 327838 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B555511 : Blo 327838 555511 := bstep (se 1 (by rfl) ⟨416633, by rfl⟩ : syracuseStep 555511 = 833267) B833267
theorem B834047 : Blo 327838 834047 := bstep (se 1 (by rfl) ⟨625535, by rfl⟩ : syracuseStep 834047 = 1251071) B1251071
theorem B17070641 : Blo 327838 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B1113263 : Blo 327838 1113263 := bstep (se 1 (by rfl) ⟨834947, by rfl⟩ : syracuseStep 1113263 = 1669895) B1669895
theorem B417307 : Blo 327838 417307 := bstep (se 1 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 417307 = 625961) B625961
theorem B556591 : Blo 327838 556591 := bstep (se 1 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 556591 = 834887) B834887
theorem B2195369 : Blo 327838 2195369 := bstep (se 2 (by rfl) ⟨823263, by rfl⟩ : syracuseStep 2195369 = 1646527) B1646527
theorem B368959 : Blo 327838 368959 := bstep (se 1 (by rfl) ⟨276719, by rfl⟩ : syracuseStep 368959 = 553439) B553439
theorem B3744143 : Blo 327838 3744143 := bstep (se 1 (by rfl) ⟨2808107, by rfl⟩ : syracuseStep 3744143 = 5616215) B5616215
theorem B492263 : Blo 327838 492263 := bstep (se 1 (by rfl) ⟨369197, by rfl⟩ : syracuseStep 492263 = 738395) B738395
theorem B1188695 : Blo 327838 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B738431 : Blo 327838 738431 := bstep (se 1 (by rfl) ⟨553823, by rfl⟩ : syracuseStep 738431 = 1107647) B1107647
theorem B11380427 : Blo 327838 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B329639 : Blo 327838 329639 := bstep (se 1 (by rfl) ⟨247229, by rfl⟩ : syracuseStep 329639 = 494459) B494459
theorem B493895 : Blo 327838 493895 := bstep (se 1 (by rfl) ⟨370421, by rfl⟩ : syracuseStep 493895 = 740843) B740843
theorem B7113217 : Blo 327838 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B1018721 : Blo 327838 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B1879271 : Blo 327838 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B789743 : Blo 327838 789743 := bstep (se 1 (by rfl) ⟨592307, by rfl⟩ : syracuseStep 789743 = 1184615) B1184615
theorem B740681 : Blo 327838 740681 := bstep (se 2 (by rfl) ⟨277755, by rfl⟩ : syracuseStep 740681 = 555511) B555511
theorem B24350057 : Blo 327838 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B3575465 : Blo 327838 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B8679383 : Blo 327838 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B10162259 : Blo 327838 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B2101625 : Blo 327838 2101625 := bstep (se 2 (by rfl) ⟨788109, by rfl⟩ : syracuseStep 2101625 = 1576219) B1576219
theorem B742121 : Blo 327838 742121 := bstep (se 2 (by rfl) ⟨278295, by rfl⟩ : syracuseStep 742121 = 556591) B556591
theorem B742175 : Blo 327838 742175 := bstep (se 1 (by rfl) ⟨556631, by rfl⟩ : syracuseStep 742175 = 1113263) B1113263
theorem B4895839 : Blo 327838 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B2495609 : Blo 327838 2495609 := bstep (se 2 (by rfl) ⟨935853, by rfl⟩ : syracuseStep 2495609 = 1871707) B1871707
theorem B1799333 : Blo 327838 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B1463579 : Blo 327838 1463579 := bstep (se 1 (by rfl) ⟨1097684, by rfl⟩ : syracuseStep 1463579 = 2195369) B2195369
theorem B751135 : Blo 327838 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B14260333 : Blo 327838 14260333 := bstep (se 3 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 14260333 = 5347625) B5347625
theorem B8043239 : Blo 327838 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B703343 : Blo 327838 703343 := bstep (se 1 (by rfl) ⟨527507, by rfl⟩ : syracuseStep 703343 = 1055015) B1055015
theorem B556031 : Blo 327838 556031 := bstep (se 1 (by rfl) ⟨417023, by rfl⟩ : syracuseStep 556031 = 834047) B834047
theorem B1662119 : Blo 327838 1662119 := bstep (se 1 (by rfl) ⟨1246589, by rfl⟩ : syracuseStep 1662119 = 2493179) B2493179
theorem B1252543 : Blo 327838 1252543 := bstep (se 1 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 1252543 = 1878815) B1878815
theorem B556409 : Blo 327838 556409 := bstep (se 2 (by rfl) ⟨208653, by rfl⟩ : syracuseStep 556409 = 417307) B417307
theorem B892907 : Blo 327838 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B6774839 : Blo 327838 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B19013777 : Blo 327838 19013777 := bstep (se 2 (by rfl) ⟨7130166, by rfl⟩ : syracuseStep 19013777 = 14260333) B14260333
theorem B1401083 : Blo 327838 1401083 := bstep (se 1 (by rfl) ⟨1050812, by rfl⟩ : syracuseStep 1401083 = 2101625) B2101625
theorem B491945 : Blo 327838 491945 := bstep (se 2 (by rfl) ⟨184479, by rfl⟩ : syracuseStep 491945 = 368959) B368959
theorem B328175 : Blo 327838 328175 := bstep (se 1 (by rfl) ⟨246131, by rfl⟩ : syracuseStep 328175 = 492263) B492263
theorem B1663739 : Blo 327838 1663739 := bstep (se 1 (by rfl) ⟨1247804, by rfl⟩ : syracuseStep 1663739 = 2495609) B2495609
theorem B492287 : Blo 327838 492287 := bstep (se 1 (by rfl) ⟨369215, by rfl⟩ : syracuseStep 492287 = 738431) B738431
theorem B975719 : Blo 327838 975719 := bstep (se 1 (by rfl) ⟨731789, by rfl⟩ : syracuseStep 975719 = 1463579) B1463579
theorem B7586951 : Blo 327838 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B329263 : Blo 327838 329263 := bstep (se 1 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 329263 = 493895) B493895
theorem B370687 : Blo 327838 370687 := bstep (se 1 (by rfl) ⟨278015, by rfl⟩ : syracuseStep 370687 = 556031) B556031
theorem B1001513 : Blo 327838 1001513 := bstep (se 2 (by rfl) ⟨375567, by rfl⟩ : syracuseStep 1001513 = 751135) B751135
theorem B1108079 : Blo 327838 1108079 := bstep (se 1 (by rfl) ⟨831059, by rfl⟩ : syracuseStep 1108079 = 1662119) B1662119
theorem B526495 : Blo 327838 526495 := bstep (se 1 (by rfl) ⟨394871, by rfl⟩ : syracuseStep 526495 = 789743) B789743
theorem B493787 : Blo 327838 493787 := bstep (se 1 (by rfl) ⟨370340, by rfl⟩ : syracuseStep 493787 = 740681) B740681
theorem B370939 : Blo 327838 370939 := bstep (se 1 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 370939 = 556409) B556409
theorem B5786255 : Blo 327838 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B494747 : Blo 327838 494747 := bstep (se 1 (by rfl) ⟨371060, by rfl⟩ : syracuseStep 494747 = 742121) B742121
theorem B494783 : Blo 327838 494783 := bstep (se 1 (by rfl) ⟨371087, by rfl⟩ : syracuseStep 494783 = 742175) B742175
theorem B1199555 : Blo 327838 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B5362159 : Blo 327838 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B16233371 : Blo 327838 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B595271 : Blo 327838 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B2496095 : Blo 327838 2496095 := bstep (se 1 (by rfl) ⟨1872071, by rfl⟩ : syracuseStep 2496095 = 3744143) B3744143
theorem B9484289 : Blo 327838 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B6527785 : Blo 327838 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B1670057 : Blo 327838 1670057 := bstep (se 2 (by rfl) ⟨626271, by rfl⟩ : syracuseStep 1670057 = 1252543) B1252543
theorem B679147 : Blo 327838 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B1252847 : Blo 327838 1252847 := bstep (se 1 (by rfl) ⟨939635, by rfl⟩ : syracuseStep 1252847 = 1879271) B1879271
theorem B3169853 : Blo 327838 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B1875581 : Blo 327838 1875581 := bstep (se 3 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 1875581 = 703343) B703343
theorem B2383643 : Blo 327838 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B934055 : Blo 327838 934055 := bstep (se 1 (by rfl) ⟨700541, by rfl⟩ : syracuseStep 934055 = 1401083) B1401083
theorem B327963 : Blo 327838 327963 := bstep (se 1 (by rfl) ⟨245972, by rfl⟩ : syracuseStep 327963 = 491945) B491945
theorem B328191 : Blo 327838 328191 := bstep (se 1 (by rfl) ⟨246143, by rfl⟩ : syracuseStep 328191 = 492287) B492287
theorem B10822247 : Blo 327838 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B1664063 : Blo 327838 1664063 := bstep (se 1 (by rfl) ⟨1248047, by rfl⟩ : syracuseStep 1664063 = 2496095) B2496095
theorem B3622117 : Blo 327838 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B738719 : Blo 327838 738719 := bstep (se 1 (by rfl) ⟨554039, by rfl⟩ : syracuseStep 738719 = 1108079) B1108079
theorem B329191 : Blo 327838 329191 := bstep (se 1 (by rfl) ⟨246893, by rfl⟩ : syracuseStep 329191 = 493787) B493787
theorem B329831 : Blo 327838 329831 := bstep (se 1 (by rfl) ⟨247373, by rfl⟩ : syracuseStep 329831 = 494747) B494747
theorem B329855 : Blo 327838 329855 := bstep (se 1 (by rfl) ⟨247391, by rfl⟩ : syracuseStep 329855 = 494783) B494783
theorem B494249 : Blo 327838 494249 := bstep (se 2 (by rfl) ⟨185343, by rfl⟩ : syracuseStep 494249 = 370687) B370687
theorem B4516559 : Blo 327838 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B12675851 : Blo 327838 12675851 := bstep (se 1 (by rfl) ⟨9506888, by rfl⟩ : syracuseStep 12675851 = 19013777) B19013777
theorem B494585 : Blo 327838 494585 := bstep (se 2 (by rfl) ⟨185469, by rfl⟩ : syracuseStep 494585 = 370939) B370939
theorem B1109159 : Blo 327838 1109159 := bstep (se 1 (by rfl) ⟨831869, by rfl⟩ : syracuseStep 1109159 = 1663739) B1663739
theorem B650479 : Blo 327838 650479 := bstep (se 1 (by rfl) ⟨487859, by rfl⟩ : syracuseStep 650479 = 975719) B975719
theorem B396847 : Blo 327838 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B8703713 : Blo 327838 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B667675 : Blo 327838 667675 := bstep (se 1 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 667675 = 1001513) B1001513
theorem B799703 : Blo 327838 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B1250387 : Blo 327838 1250387 := bstep (se 1 (by rfl) ⟨937790, by rfl⟩ : syracuseStep 1250387 = 1875581) B1875581
theorem B701993 : Blo 327838 701993 := bstep (se 2 (by rfl) ⟨263247, by rfl⟩ : syracuseStep 701993 = 526495) B526495
theorem B20231869 : Blo 327838 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B7149545 : Blo 327838 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B6322859 : Blo 327838 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B3857503 : Blo 327838 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B1113371 : Blo 327838 1113371 := bstep (se 1 (by rfl) ⟨835028, by rfl⟩ : syracuseStep 1113371 = 1670057) B1670057
theorem B835231 : Blo 327838 835231 := bstep (se 1 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 835231 = 1252847) B1252847
theorem B2113235 : Blo 327838 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B1589095 : Blo 327838 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B622703 : Blo 327838 622703 := bstep (se 1 (by rfl) ⟨467027, by rfl⟩ : syracuseStep 622703 = 934055) B934055
theorem B533135 : Blo 327838 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B492479 : Blo 327838 492479 := bstep (se 1 (by rfl) ⟨369359, by rfl⟩ : syracuseStep 492479 = 738719) B738719
theorem B329499 : Blo 327838 329499 := bstep (se 1 (by rfl) ⟨247124, by rfl⟩ : syracuseStep 329499 = 494249) B494249
theorem B23209901 : Blo 327838 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B329723 : Blo 327838 329723 := bstep (se 1 (by rfl) ⟨247292, by rfl⟩ : syracuseStep 329723 = 494585) B494585
theorem B739439 : Blo 327838 739439 := bstep (se 1 (by rfl) ⟨554579, by rfl⟩ : syracuseStep 739439 = 1109159) B1109159
theorem B1109375 : Blo 327838 1109375 := bstep (se 1 (by rfl) ⟨832031, by rfl⟩ : syracuseStep 1109375 = 1664063) B1664063
theorem B1871981 : Blo 327838 1871981 := bstep (se 3 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 1871981 = 701993) B701993
theorem B4829489 : Blo 327838 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B4215239 : Blo 327838 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B3011039 : Blo 327838 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B8450567 : Blo 327838 8450567 := bstep (se 1 (by rfl) ⟨6337925, by rfl⟩ : syracuseStep 8450567 = 12675851) B12675851
theorem B529129 : Blo 327838 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B742247 : Blo 327838 742247 := bstep (se 1 (by rfl) ⟨556685, by rfl⟩ : syracuseStep 742247 = 1113371) B1113371
theorem B2118793 : Blo 327838 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B890233 : Blo 327838 890233 := bstep (se 2 (by rfl) ⟨333837, by rfl⟩ : syracuseStep 890233 = 667675) B667675
theorem B7214831 : Blo 327838 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B833591 : Blo 327838 833591 := bstep (se 1 (by rfl) ⟨625193, by rfl⟩ : syracuseStep 833591 = 1250387) B1250387
theorem B4766363 : Blo 327838 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B5143337 : Blo 327838 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B867305 : Blo 327838 867305 := bstep (se 2 (by rfl) ⟨325239, by rfl⟩ : syracuseStep 867305 = 650479) B650479
theorem B1113641 : Blo 327838 1113641 := bstep (se 2 (by rfl) ⟨417615, by rfl⟩ : syracuseStep 1113641 = 835231) B835231
theorem B26975825 : Blo 327838 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B1408823 : Blo 327838 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B3219659 : Blo 327838 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B2810159 : Blo 327838 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B2007359 : Blo 327838 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B328319 : Blo 327838 328319 := bstep (se 1 (by rfl) ⟨246239, by rfl⟩ : syracuseStep 328319 = 492479) B492479
theorem B705505 : Blo 327838 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B4809887 : Blo 327838 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B492959 : Blo 327838 492959 := bstep (se 1 (by rfl) ⟨369719, by rfl⟩ : syracuseStep 492959 = 739439) B739439
theorem B739583 : Blo 327838 739583 := bstep (se 1 (by rfl) ⟨554687, by rfl⟩ : syracuseStep 739583 = 1109375) B1109375
theorem B17983883 : Blo 327838 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B2312813 : Blo 327838 2312813 := bstep (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) B867305
theorem B1247987 : Blo 327838 1247987 := bstep (se 1 (by rfl) ⟨935990, by rfl⟩ : syracuseStep 1247987 = 1871981) B1871981
theorem B355423 : Blo 327838 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B494831 : Blo 327838 494831 := bstep (se 1 (by rfl) ⟨371123, by rfl⟩ : syracuseStep 494831 = 742247) B742247
theorem B3428891 : Blo 327838 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B4747909 : Blo 327838 4747909 := bstep (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) B890233
theorem B742427 : Blo 327838 742427 := bstep (se 1 (by rfl) ⟨556820, by rfl⟩ : syracuseStep 742427 = 1113641) B1113641
theorem B939215 : Blo 327838 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B415135 : Blo 327838 415135 := bstep (se 1 (by rfl) ⟨311351, by rfl⟩ : syracuseStep 415135 = 622703) B622703
theorem B5633711 : Blo 327838 5633711 := bstep (se 1 (by rfl) ⟨4225283, by rfl⟩ : syracuseStep 5633711 = 8450567) B8450567
theorem B15473267 : Blo 327838 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B555727 : Blo 327838 555727 := bstep (se 1 (by rfl) ⟨416795, by rfl⟩ : syracuseStep 555727 = 833591) B833591
theorem B2825057 : Blo 327838 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B3177575 : Blo 327838 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B2146439 : Blo 327838 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B2285927 : Blo 327838 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B328639 : Blo 327838 328639 := bstep (se 1 (by rfl) ⟨246479, by rfl⟩ : syracuseStep 328639 = 492959) B492959
theorem B493055 : Blo 327838 493055 := bstep (se 1 (by rfl) ⟨369791, by rfl⟩ : syracuseStep 493055 = 739583) B739583
theorem B10315511 : Blo 327838 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B329887 : Blo 327838 329887 := bstep (se 1 (by rfl) ⟨247415, by rfl⟩ : syracuseStep 329887 = 494831) B494831
theorem B1338239 : Blo 327838 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B494951 : Blo 327838 494951 := bstep (se 1 (by rfl) ⟨371213, by rfl⟩ : syracuseStep 494951 = 742427) B742427
theorem B3206591 : Blo 327838 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B626143 : Blo 327838 626143 := bstep (se 1 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 626143 = 939215) B939215
theorem B740969 : Blo 327838 740969 := bstep (se 2 (by rfl) ⟨277863, by rfl⟩ : syracuseStep 740969 = 555727) B555727
theorem B3755807 : Blo 327838 3755807 := bstep (se 1 (by rfl) ⟨2816855, by rfl⟩ : syracuseStep 3755807 = 5633711) B5633711
theorem B11989255 : Blo 327838 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B831991 : Blo 327838 831991 := bstep (se 1 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 831991 = 1247987) B1247987
theorem B553513 : Blo 327838 553513 := bstep (se 2 (by rfl) ⟨207567, by rfl⟩ : syracuseStep 553513 = 415135) B415135
theorem B2118383 : Blo 327838 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B1873439 : Blo 327838 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B6330545 : Blo 327838 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B940673 : Blo 327838 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B473897 : Blo 327838 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B6167501 : Blo 327838 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B1883371 : Blo 327838 1883371 := bstep (se 1 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 1883371 = 2825057) B2825057
theorem B1523951 : Blo 327838 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B738017 : Blo 327838 738017 := bstep (se 2 (by rfl) ⟨276756, by rfl⟩ : syracuseStep 738017 = 553513) B553513
theorem B328703 : Blo 327838 328703 := bstep (se 1 (by rfl) ⟨246527, by rfl⟩ : syracuseStep 328703 = 493055) B493055
theorem B4220363 : Blo 327838 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B1263725 : Blo 327838 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B329967 : Blo 327838 329967 := bstep (se 1 (by rfl) ⟨247475, by rfl⟩ : syracuseStep 329967 = 494951) B494951
theorem B493979 : Blo 327838 493979 := bstep (se 1 (by rfl) ⟨370484, by rfl⟩ : syracuseStep 493979 = 740969) B740969
theorem B15985673 : Blo 327838 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B1412255 : Blo 327838 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B1109321 : Blo 327838 1109321 := bstep (se 2 (by rfl) ⟨415995, by rfl⟩ : syracuseStep 1109321 = 831991) B831991
theorem B1248959 : Blo 327838 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B6877007 : Blo 327838 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B2511161 : Blo 327838 2511161 := bstep (se 2 (by rfl) ⟨941685, by rfl⟩ : syracuseStep 2511161 = 1883371) B1883371
theorem B627115 : Blo 327838 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B3568637 : Blo 327838 3568637 := bstep (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) B1338239
theorem B2503871 : Blo 327838 2503871 := bstep (se 1 (by rfl) ⟨1877903, by rfl⟩ : syracuseStep 2503871 = 3755807) B3755807
theorem B1430959 : Blo 327838 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B834857 : Blo 327838 834857 := bstep (se 2 (by rfl) ⟨313071, by rfl⟩ : syracuseStep 834857 = 626143) B626143
theorem B4111667 : Blo 327838 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B2137727 : Blo 327838 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B1015967 : Blo 327838 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B492011 : Blo 327838 492011 := bstep (se 1 (by rfl) ⟨369008, by rfl⟩ : syracuseStep 492011 = 738017) B738017
theorem B836153 : Blo 327838 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B329319 : Blo 327838 329319 := bstep (se 1 (by rfl) ⟨246989, by rfl⟩ : syracuseStep 329319 = 493979) B493979
theorem B739547 : Blo 327838 739547 := bstep (se 1 (by rfl) ⟨554660, by rfl⟩ : syracuseStep 739547 = 1109321) B1109321
theorem B1674107 : Blo 327838 1674107 := bstep (se 1 (by rfl) ⟨1255580, by rfl⟩ : syracuseStep 1674107 = 2511161) B2511161
theorem B2379091 : Blo 327838 2379091 := bstep (se 1 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 2379091 = 3568637) B3568637
theorem B2813575 : Blo 327838 2813575 := bstep (se 1 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 2813575 = 4220363) B4220363
theorem B2741111 : Blo 327838 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B832639 : Blo 327838 832639 := bstep (se 1 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 832639 = 1248959) B1248959
theorem B4584671 : Blo 327838 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B3766013 : Blo 327838 3766013 := bstep (se 3 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 3766013 = 1412255) B1412255
theorem B1669247 : Blo 327838 1669247 := bstep (se 1 (by rfl) ⟨1251935, by rfl⟩ : syracuseStep 1669247 = 2503871) B2503871
theorem B842483 : Blo 327838 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B1907945 : Blo 327838 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B10657115 : Blo 327838 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B556571 : Blo 327838 556571 := bstep (se 1 (by rfl) ⟨417428, by rfl⟩ : syracuseStep 556571 = 834857) B834857
theorem B1425151 : Blo 327838 1425151 := bstep (se 1 (by rfl) ⟨1068863, by rfl⟩ : syracuseStep 1425151 = 2137727) B2137727
theorem B328007 : Blo 327838 328007 := bstep (se 1 (by rfl) ⟨246005, by rfl⟩ : syracuseStep 328007 = 492011) B492011
theorem B557435 : Blo 327838 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B1827407 : Blo 327838 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B3056447 : Blo 327838 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B493031 : Blo 327838 493031 := bstep (se 1 (by rfl) ⟨369773, by rfl⟩ : syracuseStep 493031 = 739547) B739547
theorem B3172121 : Blo 327838 3172121 := bstep (se 2 (by rfl) ⟨1189545, by rfl⟩ : syracuseStep 3172121 = 2379091) B2379091
theorem B1116071 : Blo 327838 1116071 := bstep (se 1 (by rfl) ⟨837053, by rfl⟩ : syracuseStep 1116071 = 1674107) B1674107
theorem B1271963 : Blo 327838 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B7104743 : Blo 327838 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B371047 : Blo 327838 371047 := bstep (se 1 (by rfl) ⟨278285, by rfl⟩ : syracuseStep 371047 = 556571) B556571
theorem B1110185 : Blo 327838 1110185 := bstep (se 2 (by rfl) ⟨416319, by rfl⟩ : syracuseStep 1110185 = 832639) B832639
theorem B561655 : Blo 327838 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B2709245 : Blo 327838 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B1112831 : Blo 327838 1112831 := bstep (se 1 (by rfl) ⟨834623, by rfl⟩ : syracuseStep 1112831 = 1669247) B1669247
theorem B3751433 : Blo 327838 3751433 := bstep (se 2 (by rfl) ⟨1406787, by rfl⟩ : syracuseStep 3751433 = 2813575) B2813575
theorem B1900201 : Blo 327838 1900201 := bstep (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) B1425151
theorem B2510675 : Blo 327838 2510675 := bstep (se 1 (by rfl) ⟨1883006, by rfl⟩ : syracuseStep 2510675 = 3766013) B3766013
theorem B3391901 : Blo 327838 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B328687 : Blo 327838 328687 := bstep (se 1 (by rfl) ⟨246515, by rfl⟩ : syracuseStep 328687 = 493031) B493031
theorem B2114747 : Blo 327838 2114747 := bstep (se 1 (by rfl) ⟨1586060, by rfl⟩ : syracuseStep 2114747 = 3172121) B3172121
theorem B4736495 : Blo 327838 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B2533601 : Blo 327838 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B2500955 : Blo 327838 2500955 := bstep (se 1 (by rfl) ⟨1875716, by rfl⟩ : syracuseStep 2500955 = 3751433) B3751433
theorem B1673783 : Blo 327838 1673783 := bstep (se 1 (by rfl) ⟨1255337, by rfl⟩ : syracuseStep 1673783 = 2510675) B2510675
theorem B740123 : Blo 327838 740123 := bstep (se 1 (by rfl) ⟨555092, by rfl⟩ : syracuseStep 740123 = 1110185) B1110185
theorem B371623 : Blo 327838 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B494729 : Blo 327838 494729 := bstep (se 2 (by rfl) ⟨185523, by rfl⟩ : syracuseStep 494729 = 371047) B371047
theorem B748873 : Blo 327838 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B741887 : Blo 327838 741887 := bstep (se 1 (by rfl) ⟨556415, by rfl⟩ : syracuseStep 741887 = 1112831) B1112831
theorem B2037631 : Blo 327838 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B744047 : Blo 327838 744047 := bstep (se 1 (by rfl) ⟨558035, by rfl⟩ : syracuseStep 744047 = 1116071) B1116071
theorem B4873085 : Blo 327838 4873085 := bstep (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) B1827407
theorem B7224653 : Blo 327838 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B2261267 : Blo 327838 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B1409831 : Blo 327838 1409831 := bstep (se 1 (by rfl) ⟨1057373, by rfl⟩ : syracuseStep 1409831 = 2114747) B2114747
theorem B1689067 : Blo 327838 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B1115855 : Blo 327838 1115855 := bstep (se 1 (by rfl) ⟨836891, by rfl⟩ : syracuseStep 1115855 = 1673783) B1673783
theorem B493415 : Blo 327838 493415 := bstep (se 1 (by rfl) ⟨370061, by rfl⟩ : syracuseStep 493415 = 740123) B740123
theorem B329819 : Blo 327838 329819 := bstep (se 1 (by rfl) ⟨247364, by rfl⟩ : syracuseStep 329819 = 494729) B494729
theorem B494591 : Blo 327838 494591 := bstep (se 1 (by rfl) ⟨370943, by rfl⟩ : syracuseStep 494591 = 741887) B741887
theorem B3157663 : Blo 327838 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B495497 : Blo 327838 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B1667303 : Blo 327838 1667303 := bstep (se 1 (by rfl) ⟨1250477, by rfl⟩ : syracuseStep 1667303 = 2500955) B2500955
theorem B496031 : Blo 327838 496031 := bstep (se 1 (by rfl) ⟨372023, by rfl⟩ : syracuseStep 496031 = 744047) B744047
theorem B3248723 : Blo 327838 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B2716841 : Blo 327838 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B998497 : Blo 327838 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B4816435 : Blo 327838 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B1507511 : Blo 327838 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B328943 : Blo 327838 328943 := bstep (se 1 (by rfl) ⟨246707, by rfl⟩ : syracuseStep 328943 = 493415) B493415
theorem B329727 : Blo 327838 329727 := bstep (se 1 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 329727 = 494591) B494591
theorem B330331 : Blo 327838 330331 := bstep (se 1 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 330331 = 495497) B495497
theorem B330687 : Blo 327838 330687 := bstep (se 1 (by rfl) ⟨248015, by rfl⟩ : syracuseStep 330687 = 496031) B496031
theorem B2165815 : Blo 327838 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B7244909 : Blo 327838 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B1331329 : Blo 327838 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B1111535 : Blo 327838 1111535 := bstep (se 1 (by rfl) ⟨833651, by rfl⟩ : syracuseStep 1111535 = 1667303) B1667303
theorem B939887 : Blo 327838 939887 := bstep (se 1 (by rfl) ⟨704915, by rfl⟩ : syracuseStep 939887 = 1409831) B1409831
theorem B743903 : Blo 327838 743903 := bstep (se 1 (by rfl) ⟨557927, by rfl⟩ : syracuseStep 743903 = 1115855) B1115855
theorem B2252089 : Blo 327838 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B6421913 : Blo 327838 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B4210217 : Blo 327838 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B12011141 : Blo 327838 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B741023 : Blo 327838 741023 := bstep (se 1 (by rfl) ⟨555767, by rfl⟩ : syracuseStep 741023 = 1111535) B1111535
theorem B626591 : Blo 327838 626591 := bstep (se 1 (by rfl) ⟨469943, by rfl⟩ : syracuseStep 626591 = 939887) B939887
theorem B2887753 : Blo 327838 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B495935 : Blo 327838 495935 := bstep (se 1 (by rfl) ⟨371951, by rfl⟩ : syracuseStep 495935 = 743903) B743903
theorem B4829939 : Blo 327838 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B4281275 : Blo 327838 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B2806811 : Blo 327838 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B1005007 : Blo 327838 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B1775105 : Blo 327838 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B3850337 : Blo 327838 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B494015 : Blo 327838 494015 := bstep (se 1 (by rfl) ⟨370511, by rfl⟩ : syracuseStep 494015 = 741023) B741023
theorem B330623 : Blo 327838 330623 := bstep (se 1 (by rfl) ⟨247967, by rfl⟩ : syracuseStep 330623 = 495935) B495935
theorem B1871207 : Blo 327838 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B1183403 : Blo 327838 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B8007427 : Blo 327838 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B1340009 : Blo 327838 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B3219959 : Blo 327838 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B11416733 : Blo 327838 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B417727 : Blo 327838 417727 := bstep (se 1 (by rfl) ⟨313295, by rfl⟩ : syracuseStep 417727 = 626591) B626591
theorem B2146639 : Blo 327838 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B893339 : Blo 327838 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B7611155 : Blo 327838 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B329343 : Blo 327838 329343 := bstep (se 1 (by rfl) ⟨247007, by rfl⟩ : syracuseStep 329343 = 494015) B494015
theorem B1247471 : Blo 327838 1247471 := bstep (se 1 (by rfl) ⟨935603, by rfl⟩ : syracuseStep 1247471 = 1871207) B1871207
theorem B10676569 : Blo 327838 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B788935 : Blo 327838 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B2566891 : Blo 327838 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B556969 : Blo 327838 556969 := bstep (se 2 (by rfl) ⟨208863, by rfl⟩ : syracuseStep 556969 = 417727) B417727
theorem B2862185 : Blo 327838 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B5074103 : Blo 327838 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B1051913 : Blo 327838 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B831647 : Blo 327838 831647 := bstep (se 1 (by rfl) ⟨623735, by rfl⟩ : syracuseStep 831647 = 1247471) B1247471
theorem B742625 : Blo 327838 742625 := bstep (se 2 (by rfl) ⟨278484, by rfl⟩ : syracuseStep 742625 = 556969) B556969
theorem B595559 : Blo 327838 595559 := bstep (se 1 (by rfl) ⟨446669, by rfl⟩ : syracuseStep 595559 = 893339) B893339
theorem B14235425 : Blo 327838 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B3422521 : Blo 327838 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B4563361 : Blo 327838 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B2805101 : Blo 327838 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B495083 : Blo 327838 495083 := bstep (se 1 (by rfl) ⟨371312, by rfl⟩ : syracuseStep 495083 = 742625) B742625
theorem B9490283 : Blo 327838 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B554431 : Blo 327838 554431 := bstep (se 1 (by rfl) ⟨415823, by rfl⟩ : syracuseStep 554431 = 831647) B831647
theorem B30529973 : Blo 327838 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B1588157 : Blo 327838 1588157 := bstep (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) B595559
theorem B3382735 : Blo 327838 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B739241 : Blo 327838 739241 := bstep (se 2 (by rfl) ⟨277215, by rfl⟩ : syracuseStep 739241 = 554431) B554431
theorem B1058771 : Blo 327838 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B1870067 : Blo 327838 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B330055 : Blo 327838 330055 := bstep (se 1 (by rfl) ⟨247541, by rfl⟩ : syracuseStep 330055 = 495083) B495083
theorem B6326855 : Blo 327838 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B20353315 : Blo 327838 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B4510313 : Blo 327838 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B24337925 : Blo 327838 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B3006875 : Blo 327838 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B492827 : Blo 327838 492827 := bstep (se 1 (by rfl) ⟨369620, by rfl⟩ : syracuseStep 492827 = 739241) B739241
theorem B705847 : Blo 327838 705847 := bstep (se 1 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 705847 = 1058771) B1058771
theorem B1246711 : Blo 327838 1246711 := bstep (se 1 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 1246711 = 1870067) B1870067
theorem B16225283 : Blo 327838 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B27137753 : Blo 327838 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B4217903 : Blo 327838 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B328551 : Blo 327838 328551 := bstep (se 1 (by rfl) ⟨246413, by rfl⟩ : syracuseStep 328551 = 492827) B492827
theorem B2811935 : Blo 327838 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B18091835 : Blo 327838 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B43267421 : Blo 327838 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B2004583 : Blo 327838 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B941129 : Blo 327838 941129 := bstep (se 2 (by rfl) ⟨352923, by rfl⟩ : syracuseStep 941129 = 705847) B705847
theorem B1662281 : Blo 327838 1662281 := bstep (se 2 (by rfl) ⟨623355, by rfl⟩ : syracuseStep 1662281 = 1246711) B1246711
theorem B28844947 : Blo 327838 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B2672777 : Blo 327838 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B1108187 : Blo 327838 1108187 := bstep (se 1 (by rfl) ⟨831140, by rfl⟩ : syracuseStep 1108187 = 1662281) B1662281
theorem B12061223 : Blo 327838 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B627419 : Blo 327838 627419 := bstep (se 1 (by rfl) ⟨470564, by rfl⟩ : syracuseStep 627419 = 941129) B941129
theorem B1874623 : Blo 327838 1874623 := bstep (se 1 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 1874623 = 2811935) B2811935
theorem B418279 : Blo 327838 418279 := bstep (se 1 (by rfl) ⟨313709, by rfl⟩ : syracuseStep 418279 = 627419) B627419
theorem B2499497 : Blo 327838 2499497 := bstep (se 2 (by rfl) ⟨937311, by rfl⟩ : syracuseStep 2499497 = 1874623) B1874623
theorem B738791 : Blo 327838 738791 := bstep (se 1 (by rfl) ⟨554093, by rfl⟩ : syracuseStep 738791 = 1108187) B1108187
theorem B1781851 : Blo 327838 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B8040815 : Blo 327838 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B38459929 : Blo 327838 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B2375801 : Blo 327838 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B557705 : Blo 327838 557705 := bstep (se 2 (by rfl) ⟨209139, by rfl⟩ : syracuseStep 557705 = 418279) B418279
theorem B492527 : Blo 327838 492527 := bstep (se 1 (by rfl) ⟨369395, by rfl⟩ : syracuseStep 492527 = 738791) B738791
theorem B5360543 : Blo 327838 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B1666331 : Blo 327838 1666331 := bstep (se 1 (by rfl) ⟨1249748, by rfl⟩ : syracuseStep 1666331 = 2499497) B2499497
theorem B51279905 : Blo 327838 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B328351 : Blo 327838 328351 := bstep (se 1 (by rfl) ⟨246263, by rfl⟩ : syracuseStep 328351 = 492527) B492527
theorem B3573695 : Blo 327838 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B1583867 : Blo 327838 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B371803 : Blo 327838 371803 := bstep (se 1 (by rfl) ⟨278852, by rfl⟩ : syracuseStep 371803 = 557705) B557705
theorem B1110887 : Blo 327838 1110887 := bstep (se 1 (by rfl) ⟨833165, by rfl⟩ : syracuseStep 1110887 = 1666331) B1666331
theorem B136746413 : Blo 327838 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B740591 : Blo 327838 740591 := bstep (se 1 (by rfl) ⟨555443, by rfl⟩ : syracuseStep 740591 = 1110887) B1110887
theorem B91164275 : Blo 327838 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B495737 : Blo 327838 495737 := bstep (se 2 (by rfl) ⟨185901, by rfl⟩ : syracuseStep 495737 = 371803) B371803
theorem B2382463 : Blo 327838 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B1055911 : Blo 327838 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B493727 : Blo 327838 493727 := bstep (se 1 (by rfl) ⟨370295, by rfl⟩ : syracuseStep 493727 = 740591) B740591
theorem B330491 : Blo 327838 330491 := bstep (se 1 (by rfl) ⟨247868, by rfl⟩ : syracuseStep 330491 = 495737) B495737
theorem B3176617 : Blo 327838 3176617 := bstep (se 2 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 3176617 = 2382463) B2382463
theorem B1407881 : Blo 327838 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B60776183 : Blo 327838 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B4235489 : Blo 327838 4235489 := bstep (se 2 (by rfl) ⟨1588308, by rfl⟩ : syracuseStep 4235489 = 3176617) B3176617
theorem B329151 : Blo 327838 329151 := bstep (se 1 (by rfl) ⟨246863, by rfl⟩ : syracuseStep 329151 = 493727) B493727
theorem B3754349 : Blo 327838 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B40517455 : Blo 327838 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B2502899 : Blo 327838 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B54023273 : Blo 327838 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B2823659 : Blo 327838 2823659 := bstep (se 1 (by rfl) ⟨2117744, by rfl⟩ : syracuseStep 2823659 = 4235489) B4235489
theorem B36015515 : Blo 327838 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B1668599 : Blo 327838 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B1882439 : Blo 327838 1882439 := bstep (se 1 (by rfl) ⟨1411829, by rfl⟩ : syracuseStep 1882439 = 2823659) B2823659
theorem B1254959 : Blo 327838 1254959 := bstep (se 1 (by rfl) ⟨941219, by rfl⟩ : syracuseStep 1254959 = 1882439) B1882439
theorem B1112399 : Blo 327838 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B24010343 : Blo 327838 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B836639 : Blo 327838 836639 := bstep (se 1 (by rfl) ⟨627479, by rfl⟩ : syracuseStep 836639 = 1254959) B1254959
theorem B741599 : Blo 327838 741599 := bstep (se 1 (by rfl) ⟨556199, by rfl⟩ : syracuseStep 741599 = 1112399) B1112399
theorem B16006895 : Blo 327838 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B557759 : Blo 327838 557759 := bstep (se 1 (by rfl) ⟨418319, by rfl⟩ : syracuseStep 557759 = 836639) B836639
theorem B494399 : Blo 327838 494399 := bstep (se 1 (by rfl) ⟨370799, by rfl⟩ : syracuseStep 494399 = 741599) B741599
theorem B10671263 : Blo 327838 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B329599 : Blo 327838 329599 := bstep (se 1 (by rfl) ⟨247199, by rfl⟩ : syracuseStep 329599 = 494399) B494399
theorem B371839 : Blo 327838 371839 := bstep (se 1 (by rfl) ⟨278879, by rfl⟩ : syracuseStep 371839 = 557759) B557759
theorem B7114175 : Blo 327838 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B495785 : Blo 327838 495785 := bstep (se 2 (by rfl) ⟨185919, by rfl⟩ : syracuseStep 495785 = 371839) B371839
theorem B4742783 : Blo 327838 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B330523 : Blo 327838 330523 := bstep (se 1 (by rfl) ⟨247892, by rfl⟩ : syracuseStep 330523 = 495785) B495785
theorem B3161855 : Blo 327838 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B2107903 : Blo 327838 2107903 := bstep (se 1 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 2107903 = 3161855) B3161855
theorem B2810537 : Blo 327838 2810537 := bstep (se 2 (by rfl) ⟨1053951, by rfl⟩ : syracuseStep 2810537 = 2107903) B2107903
theorem B1873691 : Blo 327838 1873691 := bstep (se 1 (by rfl) ⟨1405268, by rfl⟩ : syracuseStep 1873691 = 2810537) B2810537
theorem B1249127 : Blo 327838 1249127 := bstep (se 1 (by rfl) ⟨936845, by rfl⟩ : syracuseStep 1249127 = 1873691) B1873691
theorem B832751 : Blo 327838 832751 := bstep (se 1 (by rfl) ⟨624563, by rfl⟩ : syracuseStep 832751 = 1249127) B1249127
theorem B555167 : Blo 327838 555167 := bstep (se 1 (by rfl) ⟨416375, by rfl⟩ : syracuseStep 555167 = 832751) B832751
theorem B370111 : Blo 327838 370111 := bstep (se 1 (by rfl) ⟨277583, by rfl⟩ : syracuseStep 370111 = 555167) B555167
theorem B493481 : Blo 327838 493481 := bstep (se 2 (by rfl) ⟨185055, by rfl⟩ : syracuseStep 493481 = 370111) B370111
theorem B328987 : Blo 327838 328987 := bstep (se 1 (by rfl) ⟨246740, by rfl⟩ : syracuseStep 328987 = 493481) B493481

theorem C0 (j : ℕ) (h1 : 81959 ≤ j) (h2 : j ≤ 82658) : Blo 327838 (4 * j + 3) := by
  interval_cases j
  · exact B327839
  · exact B327843
  · exact B327847
  · exact B327851
  · exact B327855
  · exact B327859
  · exact B327863
  · exact B327867
  · exact B327871
  · exact B327875
  · exact B327879
  · exact B327883
  · exact B327887
  · exact B327891
  · exact B327895
  · exact B327899
  · exact B327903
  · exact B327907
  · exact B327911
  · exact B327915
  · exact B327919
  · exact B327923
  · exact B327927
  · exact B327931
  · exact B327935
  · exact B327939
  · exact B327943
  · exact B327947
  · exact B327951
  · exact B327955
  · exact B327959
  · exact B327963
  · exact B327967
  · exact B327971
  · exact B327975
  · exact B327979
  · exact B327983
  · exact B327987
  · exact B327991
  · exact B327995
  · exact B327999
  · exact B328003
  · exact B328007
  · exact B328011
  · exact B328015
  · exact B328019
  · exact B328023
  · exact B328027
  · exact B328031
  · exact B328035
  · exact B328039
  · exact B328043
  · exact B328047
  · exact B328051
  · exact B328055
  · exact B328059
  · exact B328063
  · exact B328067
  · exact B328071
  · exact B328075
  · exact B328079
  · exact B328083
  · exact B328087
  · exact B328091
  · exact B328095
  · exact B328099
  · exact B328103
  · exact B328107
  · exact B328111
  · exact B328115
  · exact B328119
  · exact B328123
  · exact B328127
  · exact B328131
  · exact B328135
  · exact B328139
  · exact B328143
  · exact B328147
  · exact B328151
  · exact B328155
  · exact B328159
  · exact B328163
  · exact B328167
  · exact B328171
  · exact B328175
  · exact B328179
  · exact B328183
  · exact B328187
  · exact B328191
  · exact B328195
  · exact B328199
  · exact B328203
  · exact B328207
  · exact B328211
  · exact B328215
  · exact B328219
  · exact B328223
  · exact B328227
  · exact B328231
  · exact B328235
  · exact B328239
  · exact B328243
  · exact B328247
  · exact B328251
  · exact B328255
  · exact B328259
  · exact B328263
  · exact B328267
  · exact B328271
  · exact B328275
  · exact B328279
  · exact B328283
  · exact B328287
  · exact B328291
  · exact B328295
  · exact B328299
  · exact B328303
  · exact B328307
  · exact B328311
  · exact B328315
  · exact B328319
  · exact B328323
  · exact B328327
  · exact B328331
  · exact B328335
  · exact B328339
  · exact B328343
  · exact B328347
  · exact B328351
  · exact B328355
  · exact B328359
  · exact B328363
  · exact B328367
  · exact B328371
  · exact B328375
  · exact B328379
  · exact B328383
  · exact B328387
  · exact B328391
  · exact B328395
  · exact B328399
  · exact B328403
  · exact B328407
  · exact B328411
  · exact B328415
  · exact B328419
  · exact B328423
  · exact B328427
  · exact B328431
  · exact B328435
  · exact B328439
  · exact B328443
  · exact B328447
  · exact B328451
  · exact B328455
  · exact B328459
  · exact B328463
  · exact B328467
  · exact B328471
  · exact B328475
  · exact B328479
  · exact B328483
  · exact B328487
  · exact B328491
  · exact B328495
  · exact B328499
  · exact B328503
  · exact B328507
  · exact B328511
  · exact B328515
  · exact B328519
  · exact B328523
  · exact B328527
  · exact B328531
  · exact B328535
  · exact B328539
  · exact B328543
  · exact B328547
  · exact B328551
  · exact B328555
  · exact B328559
  · exact B328563
  · exact B328567
  · exact B328571
  · exact B328575
  · exact B328579
  · exact B328583
  · exact B328587
  · exact B328591
  · exact B328595
  · exact B328599
  · exact B328603
  · exact B328607
  · exact B328611
  · exact B328615
  · exact B328619
  · exact B328623
  · exact B328627
  · exact B328631
  · exact B328635
  · exact B328639
  · exact B328643
  · exact B328647
  · exact B328651
  · exact B328655
  · exact B328659
  · exact B328663
  · exact B328667
  · exact B328671
  · exact B328675
  · exact B328679
  · exact B328683
  · exact B328687
  · exact B328691
  · exact B328695
  · exact B328699
  · exact B328703
  · exact B328707
  · exact B328711
  · exact B328715
  · exact B328719
  · exact B328723
  · exact B328727
  · exact B328731
  · exact B328735
  · exact B328739
  · exact B328743
  · exact B328747
  · exact B328751
  · exact B328755
  · exact B328759
  · exact B328763
  · exact B328767
  · exact B328771
  · exact B328775
  · exact B328779
  · exact B328783
  · exact B328787
  · exact B328791
  · exact B328795
  · exact B328799
  · exact B328803
  · exact B328807
  · exact B328811
  · exact B328815
  · exact B328819
  · exact B328823
  · exact B328827
  · exact B328831
  · exact B328835
  · exact B328839
  · exact B328843
  · exact B328847
  · exact B328851
  · exact B328855
  · exact B328859
  · exact B328863
  · exact B328867
  · exact B328871
  · exact B328875
  · exact B328879
  · exact B328883
  · exact B328887
  · exact B328891
  · exact B328895
  · exact B328899
  · exact B328903
  · exact B328907
  · exact B328911
  · exact B328915
  · exact B328919
  · exact B328923
  · exact B328927
  · exact B328931
  · exact B328935
  · exact B328939
  · exact B328943
  · exact B328947
  · exact B328951
  · exact B328955
  · exact B328959
  · exact B328963
  · exact B328967
  · exact B328971
  · exact B328975
  · exact B328979
  · exact B328983
  · exact B328987
  · exact B328991
  · exact B328995
  · exact B328999
  · exact B329003
  · exact B329007
  · exact B329011
  · exact B329015
  · exact B329019
  · exact B329023
  · exact B329027
  · exact B329031
  · exact B329035
  · exact B329039
  · exact B329043
  · exact B329047
  · exact B329051
  · exact B329055
  · exact B329059
  · exact B329063
  · exact B329067
  · exact B329071
  · exact B329075
  · exact B329079
  · exact B329083
  · exact B329087
  · exact B329091
  · exact B329095
  · exact B329099
  · exact B329103
  · exact B329107
  · exact B329111
  · exact B329115
  · exact B329119
  · exact B329123
  · exact B329127
  · exact B329131
  · exact B329135
  · exact B329139
  · exact B329143
  · exact B329147
  · exact B329151
  · exact B329155
  · exact B329159
  · exact B329163
  · exact B329167
  · exact B329171
  · exact B329175
  · exact B329179
  · exact B329183
  · exact B329187
  · exact B329191
  · exact B329195
  · exact B329199
  · exact B329203
  · exact B329207
  · exact B329211
  · exact B329215
  · exact B329219
  · exact B329223
  · exact B329227
  · exact B329231
  · exact B329235
  · exact B329239
  · exact B329243
  · exact B329247
  · exact B329251
  · exact B329255
  · exact B329259
  · exact B329263
  · exact B329267
  · exact B329271
  · exact B329275
  · exact B329279
  · exact B329283
  · exact B329287
  · exact B329291
  · exact B329295
  · exact B329299
  · exact B329303
  · exact B329307
  · exact B329311
  · exact B329315
  · exact B329319
  · exact B329323
  · exact B329327
  · exact B329331
  · exact B329335
  · exact B329339
  · exact B329343
  · exact B329347
  · exact B329351
  · exact B329355
  · exact B329359
  · exact B329363
  · exact B329367
  · exact B329371
  · exact B329375
  · exact B329379
  · exact B329383
  · exact B329387
  · exact B329391
  · exact B329395
  · exact B329399
  · exact B329403
  · exact B329407
  · exact B329411
  · exact B329415
  · exact B329419
  · exact B329423
  · exact B329427
  · exact B329431
  · exact B329435
  · exact B329439
  · exact B329443
  · exact B329447
  · exact B329451
  · exact B329455
  · exact B329459
  · exact B329463
  · exact B329467
  · exact B329471
  · exact B329475
  · exact B329479
  · exact B329483
  · exact B329487
  · exact B329491
  · exact B329495
  · exact B329499
  · exact B329503
  · exact B329507
  · exact B329511
  · exact B329515
  · exact B329519
  · exact B329523
  · exact B329527
  · exact B329531
  · exact B329535
  · exact B329539
  · exact B329543
  · exact B329547
  · exact B329551
  · exact B329555
  · exact B329559
  · exact B329563
  · exact B329567
  · exact B329571
  · exact B329575
  · exact B329579
  · exact B329583
  · exact B329587
  · exact B329591
  · exact B329595
  · exact B329599
  · exact B329603
  · exact B329607
  · exact B329611
  · exact B329615
  · exact B329619
  · exact B329623
  · exact B329627
  · exact B329631
  · exact B329635
  · exact B329639
  · exact B329643
  · exact B329647
  · exact B329651
  · exact B329655
  · exact B329659
  · exact B329663
  · exact B329667
  · exact B329671
  · exact B329675
  · exact B329679
  · exact B329683
  · exact B329687
  · exact B329691
  · exact B329695
  · exact B329699
  · exact B329703
  · exact B329707
  · exact B329711
  · exact B329715
  · exact B329719
  · exact B329723
  · exact B329727
  · exact B329731
  · exact B329735
  · exact B329739
  · exact B329743
  · exact B329747
  · exact B329751
  · exact B329755
  · exact B329759
  · exact B329763
  · exact B329767
  · exact B329771
  · exact B329775
  · exact B329779
  · exact B329783
  · exact B329787
  · exact B329791
  · exact B329795
  · exact B329799
  · exact B329803
  · exact B329807
  · exact B329811
  · exact B329815
  · exact B329819
  · exact B329823
  · exact B329827
  · exact B329831
  · exact B329835
  · exact B329839
  · exact B329843
  · exact B329847
  · exact B329851
  · exact B329855
  · exact B329859
  · exact B329863
  · exact B329867
  · exact B329871
  · exact B329875
  · exact B329879
  · exact B329883
  · exact B329887
  · exact B329891
  · exact B329895
  · exact B329899
  · exact B329903
  · exact B329907
  · exact B329911
  · exact B329915
  · exact B329919
  · exact B329923
  · exact B329927
  · exact B329931
  · exact B329935
  · exact B329939
  · exact B329943
  · exact B329947
  · exact B329951
  · exact B329955
  · exact B329959
  · exact B329963
  · exact B329967
  · exact B329971
  · exact B329975
  · exact B329979
  · exact B329983
  · exact B329987
  · exact B329991
  · exact B329995
  · exact B329999
  · exact B330003
  · exact B330007
  · exact B330011
  · exact B330015
  · exact B330019
  · exact B330023
  · exact B330027
  · exact B330031
  · exact B330035
  · exact B330039
  · exact B330043
  · exact B330047
  · exact B330051
  · exact B330055
  · exact B330059
  · exact B330063
  · exact B330067
  · exact B330071
  · exact B330075
  · exact B330079
  · exact B330083
  · exact B330087
  · exact B330091
  · exact B330095
  · exact B330099
  · exact B330103
  · exact B330107
  · exact B330111
  · exact B330115
  · exact B330119
  · exact B330123
  · exact B330127
  · exact B330131
  · exact B330135
  · exact B330139
  · exact B330143
  · exact B330147
  · exact B330151
  · exact B330155
  · exact B330159
  · exact B330163
  · exact B330167
  · exact B330171
  · exact B330175
  · exact B330179
  · exact B330183
  · exact B330187
  · exact B330191
  · exact B330195
  · exact B330199
  · exact B330203
  · exact B330207
  · exact B330211
  · exact B330215
  · exact B330219
  · exact B330223
  · exact B330227
  · exact B330231
  · exact B330235
  · exact B330239
  · exact B330243
  · exact B330247
  · exact B330251
  · exact B330255
  · exact B330259
  · exact B330263
  · exact B330267
  · exact B330271
  · exact B330275
  · exact B330279
  · exact B330283
  · exact B330287
  · exact B330291
  · exact B330295
  · exact B330299
  · exact B330303
  · exact B330307
  · exact B330311
  · exact B330315
  · exact B330319
  · exact B330323
  · exact B330327
  · exact B330331
  · exact B330335
  · exact B330339
  · exact B330343
  · exact B330347
  · exact B330351
  · exact B330355
  · exact B330359
  · exact B330363
  · exact B330367
  · exact B330371
  · exact B330375
  · exact B330379
  · exact B330383
  · exact B330387
  · exact B330391
  · exact B330395
  · exact B330399
  · exact B330403
  · exact B330407
  · exact B330411
  · exact B330415
  · exact B330419
  · exact B330423
  · exact B330427
  · exact B330431
  · exact B330435
  · exact B330439
  · exact B330443
  · exact B330447
  · exact B330451
  · exact B330455
  · exact B330459
  · exact B330463
  · exact B330467
  · exact B330471
  · exact B330475
  · exact B330479
  · exact B330483
  · exact B330487
  · exact B330491
  · exact B330495
  · exact B330499
  · exact B330503
  · exact B330507
  · exact B330511
  · exact B330515
  · exact B330519
  · exact B330523
  · exact B330527
  · exact B330531
  · exact B330535
  · exact B330539
  · exact B330543
  · exact B330547
  · exact B330551
  · exact B330555
  · exact B330559
  · exact B330563
  · exact B330567
  · exact B330571
  · exact B330575
  · exact B330579
  · exact B330583
  · exact B330587
  · exact B330591
  · exact B330595
  · exact B330599
  · exact B330603
  · exact B330607
  · exact B330611
  · exact B330615
  · exact B330619
  · exact B330623
  · exact B330627
  · exact B330631
  · exact B330635

theorem C1 (j : ℕ) (h1 : 82659 ≤ j) (h2 : j ≤ 82686) : Blo 327838 (4 * j + 3) := by
  interval_cases j
  · exact B330639
  · exact B330643
  · exact B330647
  · exact B330651
  · exact B330655
  · exact B330659
  · exact B330663
  · exact B330667
  · exact B330671
  · exact B330675
  · exact B330679
  · exact B330683
  · exact B330687
  · exact B330691
  · exact B330695
  · exact B330699
  · exact B330703
  · exact B330707
  · exact B330711
  · exact B330715
  · exact B330719
  · exact B330723
  · exact B330727
  · exact B330731
  · exact B330735
  · exact B330739
  · exact B330743
  · exact B330747

theorem solution (m : ℕ) (hlo : 327838 ≤ m) (hhi : m ≤ 330749) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 81959 ≤ j := by omega
    have hj2 : j ≤ 82686 := by omega
    have hb : Blo 327838 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 82659 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
