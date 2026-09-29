-- Prove2me | solution 1 for syracuse_descends_range_1152637_1156637
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:48.492257+00:00
-- url     : https://prove2.me/submissions/db84acd4-60d8-43c1-b793-f866dec08d77

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


theorem B4390949 : Blo 1152637 4390949 := bbase (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) (by norm_num)
theorem B2195581 : Blo 1152637 2195581 := bbase (se 3 (by rfl) ⟨411671, by rfl⟩ : syracuseStep 2195581 = 823343) (by norm_num)
theorem B2195741 : Blo 1152637 2195741 := bbase (se 3 (by rfl) ⟨411701, by rfl⟩ : syracuseStep 2195741 = 823403) (by norm_num)
theorem B3899717 : Blo 1152637 3899717 := bbase (se 4 (by rfl) ⟨365598, by rfl⟩ : syracuseStep 3899717 = 731197) (by norm_num)
theorem B2851549 : Blo 1152637 2851549 := bbase (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) (by norm_num)
theorem B3900149 : Blo 1152637 3900149 := bbase (se 5 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 3900149 = 365639) (by norm_num)
theorem B7406549 : Blo 1152637 7406549 := bbase (se 7 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 7406549 = 173591) (by norm_num)
theorem B3900581 : Blo 1152637 3900581 := bbase (se 4 (by rfl) ⟨365679, by rfl⟩ : syracuseStep 3900581 = 731359) (by norm_num)
theorem B1443065 : Blo 1152637 1443065 := bbase (se 2 (by rfl) ⟨541149, by rfl⟩ : syracuseStep 1443065 = 1082299) (by norm_num)
theorem B2917741 : Blo 1152637 2917741 := bbase (se 3 (by rfl) ⟨547076, by rfl⟩ : syracuseStep 2917741 = 1094153) (by norm_num)
theorem B2917853 : Blo 1152637 2917853 := bbase (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) (by norm_num)
theorem B3901013 : Blo 1152637 3901013 := bbase (se 8 (by rfl) ⟨22857, by rfl⟩ : syracuseStep 3901013 = 45715) (by norm_num)
theorem B2918045 : Blo 1152637 2918045 := bbase (se 3 (by rfl) ⟨547133, by rfl⟩ : syracuseStep 2918045 = 1094267) (by norm_num)
theorem B2918389 : Blo 1152637 2918389 := bbase (se 5 (by rfl) ⟨136799, by rfl⟩ : syracuseStep 2918389 = 273599) (by norm_num)
theorem B3901445 : Blo 1152637 3901445 := bbase (se 4 (by rfl) ⟨365760, by rfl⟩ : syracuseStep 3901445 = 731521) (by norm_num)
theorem B53413973 : Blo 1152637 53413973 := bbase (se 8 (by rfl) ⟨312972, by rfl⟩ : syracuseStep 53413973 = 625945) (by norm_num)
theorem B2918501 : Blo 1152637 2918501 := bbase (se 4 (by rfl) ⟨273609, by rfl⟩ : syracuseStep 2918501 = 547219) (by norm_num)
theorem B2918693 : Blo 1152637 2918693 := bbase (se 4 (by rfl) ⟨273627, by rfl⟩ : syracuseStep 2918693 = 547255) (by norm_num)
theorem B3705173 : Blo 1152637 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B3901877 : Blo 1152637 3901877 := bbase (se 5 (by rfl) ⟨182900, by rfl⟩ : syracuseStep 3901877 = 365801) (by norm_num)
theorem B2919037 : Blo 1152637 2919037 := bbase (se 3 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 2919037 = 1094639) (by norm_num)
theorem B2919149 : Blo 1152637 2919149 := bbase (se 3 (by rfl) ⟨547340, by rfl⟩ : syracuseStep 2919149 = 1094681) (by norm_num)
theorem B66489173 : Blo 1152637 66489173 := bbase (se 9 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 66489173 = 389585) (by norm_num)
theorem B3902309 : Blo 1152637 3902309 := bbase (se 4 (by rfl) ⟨365841, by rfl⟩ : syracuseStep 3902309 = 731683) (by norm_num)
theorem B3115925 : Blo 1152637 3115925 := bbase (se 6 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 3115925 = 146059) (by norm_num)
theorem B1641389 : Blo 1152637 1641389 := bbase (se 3 (by rfl) ⟨307760, by rfl⟩ : syracuseStep 1641389 = 615521) (by norm_num)
theorem B2919341 : Blo 1152637 2919341 := bbase (se 3 (by rfl) ⟨547376, by rfl⟩ : syracuseStep 2919341 = 1094753) (by norm_num)
theorem B2919685 : Blo 1152637 2919685 := bbase (se 4 (by rfl) ⟨273720, by rfl⟩ : syracuseStep 2919685 = 547441) (by norm_num)
theorem B3902741 : Blo 1152637 3902741 := bbase (se 6 (by rfl) ⟨91470, by rfl⟩ : syracuseStep 3902741 = 182941) (by norm_num)
theorem B2919797 : Blo 1152637 2919797 := bbase (se 5 (by rfl) ⟨136865, by rfl⟩ : syracuseStep 2919797 = 273731) (by norm_num)
theorem B23662037 : Blo 1152637 23662037 := bbase (se 7 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 23662037 = 554579) (by norm_num)
theorem B2919989 : Blo 1152637 2919989 := bbase (se 5 (by rfl) ⟨136874, by rfl⟩ : syracuseStep 2919989 = 273749) (by norm_num)
theorem B5836373 : Blo 1152637 5836373 := bbase (se 8 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 5836373 = 68395) (by norm_num)
theorem B1642141 : Blo 1152637 1642141 := bbase (se 3 (by rfl) ⟨307901, by rfl⟩ : syracuseStep 1642141 = 615803) (by norm_num)
theorem B3903173 : Blo 1152637 3903173 := bbase (se 4 (by rfl) ⟨365922, by rfl⟩ : syracuseStep 3903173 = 731845) (by norm_num)
theorem B1806149 : Blo 1152637 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B1314677 : Blo 1152637 1314677 := bbase (se 5 (by rfl) ⟨61625, by rfl⟩ : syracuseStep 1314677 = 123251) (by norm_num)
theorem B2920333 : Blo 1152637 2920333 := bbase (se 3 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 2920333 = 1095125) (by norm_num)
theorem B6655925 : Blo 1152637 6655925 := bbase (se 5 (by rfl) ⟨311996, by rfl⟩ : syracuseStep 6655925 = 623993) (by norm_num)
theorem B2920445 : Blo 1152637 2920445 := bbase (se 3 (by rfl) ⟨547583, by rfl⟩ : syracuseStep 2920445 = 1095167) (by norm_num)
theorem B3903605 : Blo 1152637 3903605 := bbase (se 5 (by rfl) ⟨182981, by rfl⟩ : syracuseStep 3903605 = 365963) (by norm_num)
theorem B2920637 : Blo 1152637 2920637 := bbase (se 3 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 2920637 = 1095239) (by norm_num)
theorem B1642933 : Blo 1152637 1642933 := bbase (se 5 (by rfl) ⟨77012, by rfl⟩ : syracuseStep 1642933 = 154025) (by norm_num)
theorem B12489173 : Blo 1152637 12489173 := bbase (se 7 (by rfl) ⟨146357, by rfl⟩ : syracuseStep 12489173 = 292715) (by norm_num)
theorem B2462213 : Blo 1152637 2462213 := bbase (se 4 (by rfl) ⟨230832, by rfl⟩ : syracuseStep 2462213 = 461665) (by norm_num)
theorem B2920981 : Blo 1152637 2920981 := bbase (se 6 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 2920981 = 136921) (by norm_num)
theorem B2921093 : Blo 1152637 2921093 := bbase (se 4 (by rfl) ⟨273852, by rfl⟩ : syracuseStep 2921093 = 547705) (by norm_num)
theorem B2462357 : Blo 1152637 2462357 := bbase (se 6 (by rfl) ⟨57711, by rfl⟩ : syracuseStep 2462357 = 115423) (by norm_num)
theorem B2593493 : Blo 1152637 2593493 := bbase (se 7 (by rfl) ⟨30392, by rfl⟩ : syracuseStep 2593493 = 60785) (by norm_num)
theorem B3117797 : Blo 1152637 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1643269 : Blo 1152637 1643269 := bbase (se 4 (by rfl) ⟨154056, by rfl⟩ : syracuseStep 1643269 = 308113) (by norm_num)
theorem B2593565 : Blo 1152637 2593565 := bbase (se 3 (by rfl) ⟨486293, by rfl⟩ : syracuseStep 2593565 = 972587) (by norm_num)
theorem B2921285 : Blo 1152637 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B2593637 : Blo 1152637 2593637 := bbase (se 4 (by rfl) ⟨243153, by rfl⟩ : syracuseStep 2593637 = 486307) (by norm_num)
theorem B5837669 : Blo 1152637 5837669 := bbase (se 4 (by rfl) ⟨547281, by rfl⟩ : syracuseStep 5837669 = 1094563) (by norm_num)
theorem B8426389 : Blo 1152637 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B2593709 : Blo 1152637 2593709 := bbase (se 3 (by rfl) ⟨486320, by rfl⟩ : syracuseStep 2593709 = 972641) (by norm_num)
theorem B1643485 : Blo 1152637 1643485 := bbase (se 3 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 1643485 = 616307) (by norm_num)
theorem B2593781 : Blo 1152637 2593781 := bbase (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) (by norm_num)
theorem B4166645 : Blo 1152637 4166645 := bbase (se 5 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 4166645 = 390623) (by norm_num)
theorem B2462717 : Blo 1152637 2462717 := bbase (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) (by norm_num)
theorem B2593853 : Blo 1152637 2593853 := bbase (se 3 (by rfl) ⟨486347, by rfl⟩ : syracuseStep 2593853 = 972695) (by norm_num)
theorem B5706821 : Blo 1152637 5706821 := bbase (se 4 (by rfl) ⟨535014, by rfl⟩ : syracuseStep 5706821 = 1070029) (by norm_num)
theorem B14783573 : Blo 1152637 14783573 := bbase (se 8 (by rfl) ⟨86622, by rfl⟩ : syracuseStep 14783573 = 173245) (by norm_num)
theorem B2593925 : Blo 1152637 2593925 := bbase (se 4 (by rfl) ⟨243180, by rfl⟩ : syracuseStep 2593925 = 486361) (by norm_num)
theorem B2921629 : Blo 1152637 2921629 := bbase (se 3 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 2921629 = 1095611) (by norm_num)
theorem B2593997 : Blo 1152637 2593997 := bbase (se 3 (by rfl) ⟨486374, by rfl⟩ : syracuseStep 2593997 = 972749) (by norm_num)
theorem B2921741 : Blo 1152637 2921741 := bbase (se 3 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 2921741 = 1095653) (by norm_num)
theorem B2594069 : Blo 1152637 2594069 := bbase (se 6 (by rfl) ⟨60798, by rfl⟩ : syracuseStep 2594069 = 121597) (by norm_num)
theorem B1643861 : Blo 1152637 1643861 := bbase (se 14 (by rfl) ⟨150, by rfl⟩ : syracuseStep 1643861 = 301) (by norm_num)
theorem B2594141 : Blo 1152637 2594141 := bbase (se 3 (by rfl) ⟨486401, by rfl⟩ : syracuseStep 2594141 = 972803) (by norm_num)
theorem B2594213 : Blo 1152637 2594213 := bbase (se 4 (by rfl) ⟨243207, by rfl⟩ : syracuseStep 2594213 = 486415) (by norm_num)
theorem B2921933 : Blo 1152637 2921933 := bbase (se 3 (by rfl) ⟨547862, by rfl⟩ : syracuseStep 2921933 = 1095725) (by norm_num)
theorem B2594285 : Blo 1152637 2594285 := bbase (se 3 (by rfl) ⟨486428, by rfl⟩ : syracuseStep 2594285 = 972857) (by norm_num)
theorem B3282437 : Blo 1152637 3282437 := bbase (se 4 (by rfl) ⟨307728, by rfl⟩ : syracuseStep 3282437 = 615457) (by norm_num)
theorem B14816789 : Blo 1152637 14816789 := bbase (se 6 (by rfl) ⟨347268, by rfl⟩ : syracuseStep 14816789 = 694537) (by norm_num)
theorem B2594357 : Blo 1152637 2594357 := bbase (se 5 (by rfl) ⟨121610, by rfl⟩ : syracuseStep 2594357 = 243221) (by norm_num)
theorem B2594429 : Blo 1152637 2594429 := bbase (se 3 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 2594429 = 972911) (by norm_num)
theorem B2594501 : Blo 1152637 2594501 := bbase (se 4 (by rfl) ⟨243234, by rfl⟩ : syracuseStep 2594501 = 486469) (by norm_num)
theorem B3282677 : Blo 1152637 3282677 := bbase (se 5 (by rfl) ⟨153875, by rfl⟩ : syracuseStep 3282677 = 307751) (by norm_num)
theorem B2594573 : Blo 1152637 2594573 := bbase (se 3 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 2594573 = 972965) (by norm_num)
theorem B2922277 : Blo 1152637 2922277 := bbase (se 4 (by rfl) ⟨273963, by rfl⟩ : syracuseStep 2922277 = 547927) (by norm_num)
theorem B2594645 : Blo 1152637 2594645 := bbase (se 9 (by rfl) ⟨7601, by rfl⟩ : syracuseStep 2594645 = 15203) (by norm_num)
theorem B5543765 : Blo 1152637 5543765 := bbase (se 9 (by rfl) ⟨16241, by rfl⟩ : syracuseStep 5543765 = 32483) (by norm_num)
theorem B2463605 : Blo 1152637 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B4167557 : Blo 1152637 4167557 := bbase (se 4 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 4167557 = 781417) (by norm_num)
theorem B2922389 : Blo 1152637 2922389 := bbase (se 6 (by rfl) ⟨68493, by rfl⟩ : syracuseStep 2922389 = 136987) (by norm_num)
theorem B2594717 : Blo 1152637 2594717 := bbase (se 3 (by rfl) ⟨486509, by rfl⟩ : syracuseStep 2594717 = 973019) (by norm_num)
theorem B3282869 : Blo 1152637 3282869 := bbase (se 5 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 3282869 = 307769) (by norm_num)
theorem B2594789 : Blo 1152637 2594789 := bbase (se 4 (by rfl) ⟨243261, by rfl⟩ : syracuseStep 2594789 = 486523) (by norm_num)
theorem B1218601 : Blo 1152637 1218601 := bbase (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) (by norm_num)
theorem B2594861 : Blo 1152637 2594861 := bbase (se 3 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 2594861 = 973073) (by norm_num)
theorem B2922581 : Blo 1152637 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B1972325 : Blo 1152637 1972325 := bbase (se 4 (by rfl) ⟨184905, by rfl⟩ : syracuseStep 1972325 = 369811) (by norm_num)
theorem B2463853 : Blo 1152637 2463853 := bbase (se 3 (by rfl) ⟨461972, by rfl⟩ : syracuseStep 2463853 = 923945) (by norm_num)
theorem B2594933 : Blo 1152637 2594933 := bbase (se 5 (by rfl) ⟨121637, by rfl⟩ : syracuseStep 2594933 = 243275) (by norm_num)
theorem B5838965 : Blo 1152637 5838965 := bbase (se 5 (by rfl) ⟨273701, by rfl⟩ : syracuseStep 5838965 = 547403) (by norm_num)
theorem B2595005 : Blo 1152637 2595005 := bbase (se 3 (by rfl) ⟨486563, by rfl⟩ : syracuseStep 2595005 = 973127) (by norm_num)
theorem B1251545 : Blo 1152637 1251545 := bbase (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) (by norm_num)
theorem B2595077 : Blo 1152637 2595077 := bbase (se 4 (by rfl) ⟨243288, by rfl⟩ : syracuseStep 2595077 = 486577) (by norm_num)
theorem B6658325 : Blo 1152637 6658325 := bbase (se 6 (by rfl) ⟨156054, by rfl⟩ : syracuseStep 6658325 = 312109) (by norm_num)
theorem B2595149 : Blo 1152637 2595149 := bbase (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) (by norm_num)
theorem B2595221 : Blo 1152637 2595221 := bbase (se 6 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 2595221 = 121651) (by norm_num)
theorem B1317269 : Blo 1152637 1317269 := bbase (se 6 (by rfl) ⟨30873, by rfl⟩ : syracuseStep 1317269 = 61747) (by norm_num)
theorem B2922925 : Blo 1152637 2922925 := bbase (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) (by norm_num)
theorem B7018933 : Blo 1152637 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B2595293 : Blo 1152637 2595293 := bbase (se 3 (by rfl) ⟨486617, by rfl⟩ : syracuseStep 2595293 = 973235) (by norm_num)
theorem B2923037 : Blo 1152637 2923037 := bbase (se 3 (by rfl) ⟨548069, by rfl⟩ : syracuseStep 2923037 = 1096139) (by norm_num)
theorem B2595365 : Blo 1152637 2595365 := bbase (se 4 (by rfl) ⟨243315, by rfl⟩ : syracuseStep 2595365 = 486631) (by norm_num)
theorem B2464357 : Blo 1152637 2464357 := bbase (se 4 (by rfl) ⟨231033, by rfl⟩ : syracuseStep 2464357 = 462067) (by norm_num)
theorem B2595437 : Blo 1152637 2595437 := bbase (se 3 (by rfl) ⟨486644, by rfl⟩ : syracuseStep 2595437 = 973289) (by norm_num)
theorem B2595509 : Blo 1152637 2595509 := bbase (se 5 (by rfl) ⟨121664, by rfl⟩ : syracuseStep 2595509 = 243329) (by norm_num)
theorem B2923229 : Blo 1152637 2923229 := bbase (se 3 (by rfl) ⟨548105, by rfl⟩ : syracuseStep 2923229 = 1096211) (by norm_num)
theorem B1645285 : Blo 1152637 1645285 := bbase (se 4 (by rfl) ⟨154245, by rfl⟩ : syracuseStep 1645285 = 308491) (by norm_num)
theorem B2595581 : Blo 1152637 2595581 := bbase (se 3 (by rfl) ⟨486671, by rfl⟩ : syracuseStep 2595581 = 973343) (by norm_num)
theorem B2595653 : Blo 1152637 2595653 := bbase (se 4 (by rfl) ⟨243342, by rfl⟩ : syracuseStep 2595653 = 486685) (by norm_num)
theorem B11836277 : Blo 1152637 11836277 := bbase (se 5 (by rfl) ⟨554825, by rfl⟩ : syracuseStep 11836277 = 1109651) (by norm_num)
theorem B2595725 : Blo 1152637 2595725 := bbase (se 3 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 2595725 = 973397) (by norm_num)
theorem B3283861 : Blo 1152637 3283861 := bbase (se 6 (by rfl) ⟨76965, by rfl⟩ : syracuseStep 3283861 = 153931) (by norm_num)
theorem B2595797 : Blo 1152637 2595797 := bbase (se 7 (by rfl) ⟨30419, by rfl⟩ : syracuseStep 2595797 = 60839) (by norm_num)
theorem B2595869 : Blo 1152637 2595869 := bbase (se 3 (by rfl) ⟨486725, by rfl⟩ : syracuseStep 2595869 = 973451) (by norm_num)
theorem B2923573 : Blo 1152637 2923573 := bbase (se 5 (by rfl) ⟨137042, by rfl⟩ : syracuseStep 2923573 = 274085) (by norm_num)
theorem B48012373 : Blo 1152637 48012373 := bbase (se 8 (by rfl) ⟨281322, by rfl⟩ : syracuseStep 48012373 = 562645) (by norm_num)
theorem B2595941 : Blo 1152637 2595941 := bbase (se 4 (by rfl) ⟨243369, by rfl⟩ : syracuseStep 2595941 = 486739) (by norm_num)
theorem B1875077 : Blo 1152637 1875077 := bbase (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) (by norm_num)
theorem B3513493 : Blo 1152637 3513493 := bbase (se 6 (by rfl) ⟨82347, by rfl⟩ : syracuseStep 3513493 = 164695) (by norm_num)
theorem B2923685 : Blo 1152637 2923685 := bbase (se 4 (by rfl) ⟨274095, by rfl⟩ : syracuseStep 2923685 = 548191) (by norm_num)
theorem B2596013 : Blo 1152637 2596013 := bbase (se 3 (by rfl) ⟨486752, by rfl⟩ : syracuseStep 2596013 = 973505) (by norm_num)
theorem B1875181 : Blo 1152637 1875181 := bbase (se 3 (by rfl) ⟨351596, by rfl⟩ : syracuseStep 1875181 = 703193) (by norm_num)
theorem B2596085 : Blo 1152637 2596085 := bbase (se 5 (by rfl) ⟨121691, by rfl⟩ : syracuseStep 2596085 = 243383) (by norm_num)
theorem B1645877 : Blo 1152637 1645877 := bbase (se 5 (by rfl) ⟨77150, by rfl⟩ : syracuseStep 1645877 = 154301) (by norm_num)
theorem B2596157 : Blo 1152637 2596157 := bbase (se 3 (by rfl) ⟨486779, by rfl⟩ : syracuseStep 2596157 = 973559) (by norm_num)
theorem B2923877 : Blo 1152637 2923877 := bbase (se 4 (by rfl) ⟨274113, by rfl⟩ : syracuseStep 2923877 = 548227) (by norm_num)
theorem B5840261 : Blo 1152637 5840261 := bbase (se 4 (by rfl) ⟨547524, by rfl⟩ : syracuseStep 5840261 = 1095049) (by norm_num)
theorem B2596229 : Blo 1152637 2596229 := bbase (se 4 (by rfl) ⟨243396, by rfl⟩ : syracuseStep 2596229 = 486793) (by norm_num)
theorem B1645957 : Blo 1152637 1645957 := bbase (se 4 (by rfl) ⟨154308, by rfl⟩ : syracuseStep 1645957 = 308617) (by norm_num)
theorem B3120565 : Blo 1152637 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B2596301 : Blo 1152637 2596301 := bbase (se 3 (by rfl) ⟨486806, by rfl⟩ : syracuseStep 2596301 = 973613) (by norm_num)
theorem B2465245 : Blo 1152637 2465245 := bbase (se 3 (by rfl) ⟨462233, by rfl⟩ : syracuseStep 2465245 = 924467) (by norm_num)
theorem B1646077 : Blo 1152637 1646077 := bbase (se 3 (by rfl) ⟨308639, by rfl⟩ : syracuseStep 1646077 = 617279) (by norm_num)
theorem B2596373 : Blo 1152637 2596373 := bbase (se 6 (by rfl) ⟨60852, by rfl⟩ : syracuseStep 2596373 = 121705) (by norm_num)
theorem B2596445 : Blo 1152637 2596445 := bbase (se 3 (by rfl) ⟨486833, by rfl⟩ : syracuseStep 2596445 = 973667) (by norm_num)
theorem B1646173 : Blo 1152637 1646173 := bbase (se 3 (by rfl) ⟨308657, by rfl⟩ : syracuseStep 1646173 = 617315) (by norm_num)
theorem B1580693 : Blo 1152637 1580693 := bbase (se 6 (by rfl) ⟨37047, by rfl⟩ : syracuseStep 1580693 = 74095) (by norm_num)
theorem B2596517 : Blo 1152637 2596517 := bbase (se 4 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 2596517 = 486847) (by norm_num)
theorem B2924221 : Blo 1152637 2924221 := bbase (se 3 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 2924221 = 1096583) (by norm_num)
theorem B2596589 : Blo 1152637 2596589 := bbase (se 3 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 2596589 = 973721) (by norm_num)
theorem B2924333 : Blo 1152637 2924333 := bbase (se 3 (by rfl) ⟨548312, by rfl⟩ : syracuseStep 2924333 = 1096625) (by norm_num)
theorem B2596661 : Blo 1152637 2596661 := bbase (se 5 (by rfl) ⟨121718, by rfl⟩ : syracuseStep 2596661 = 243437) (by norm_num)
theorem B1482553 : Blo 1152637 1482553 := bbase (se 2 (by rfl) ⟨555957, by rfl⟩ : syracuseStep 1482553 = 1111915) (by norm_num)
theorem B2596733 : Blo 1152637 2596733 := bbase (se 3 (by rfl) ⟨486887, by rfl⟩ : syracuseStep 2596733 = 973775) (by norm_num)
theorem B2596805 : Blo 1152637 2596805 := bbase (se 4 (by rfl) ⟨243450, by rfl⟩ : syracuseStep 2596805 = 486901) (by norm_num)
theorem B2465741 : Blo 1152637 2465741 := bbase (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) (by norm_num)
theorem B3284965 : Blo 1152637 3284965 := bbase (se 4 (by rfl) ⟨307965, by rfl⟩ : syracuseStep 3284965 = 615931) (by norm_num)
theorem B1974245 : Blo 1152637 1974245 := bbase (se 4 (by rfl) ⟨185085, by rfl⟩ : syracuseStep 1974245 = 370171) (by norm_num)
theorem B2924525 : Blo 1152637 2924525 := bbase (se 3 (by rfl) ⟨548348, by rfl⟩ : syracuseStep 2924525 = 1096697) (by norm_num)
theorem B2596877 : Blo 1152637 2596877 := bbase (se 3 (by rfl) ⟨486914, by rfl⟩ : syracuseStep 2596877 = 973829) (by norm_num)
theorem B2629693 : Blo 1152637 2629693 := bbase (se 3 (by rfl) ⟨493067, by rfl⟩ : syracuseStep 2629693 = 986135) (by norm_num)
theorem B1646669 : Blo 1152637 1646669 := bbase (se 3 (by rfl) ⟨308750, by rfl⟩ : syracuseStep 1646669 = 617501) (by norm_num)
theorem B2596949 : Blo 1152637 2596949 := bbase (se 8 (by rfl) ⟨15216, by rfl⟩ : syracuseStep 2596949 = 30433) (by norm_num)
theorem B7610453 : Blo 1152637 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1876117 : Blo 1152637 1876117 := bbase (se 6 (by rfl) ⟨43971, by rfl⟩ : syracuseStep 1876117 = 87943) (by norm_num)
theorem B2597021 : Blo 1152637 2597021 := bbase (se 3 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 2597021 = 973883) (by norm_num)
theorem B2498725 : Blo 1152637 2498725 := bbase (se 4 (by rfl) ⟨234255, by rfl⟩ : syracuseStep 2498725 = 468511) (by norm_num)
theorem B8331445 : Blo 1152637 8331445 := bbase (se 5 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 8331445 = 781073) (by norm_num)
theorem B4923605 : Blo 1152637 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B2597093 : Blo 1152637 2597093 := bbase (se 4 (by rfl) ⟨243477, by rfl⟩ : syracuseStep 2597093 = 486955) (by norm_num)
theorem B2597165 : Blo 1152637 2597165 := bbase (se 3 (by rfl) ⟨486968, by rfl⟩ : syracuseStep 2597165 = 973937) (by norm_num)
theorem B2924869 : Blo 1152637 2924869 := bbase (se 4 (by rfl) ⟨274206, by rfl⟩ : syracuseStep 2924869 = 548413) (by norm_num)
theorem B2597237 : Blo 1152637 2597237 := bbase (se 5 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 2597237 = 243491) (by norm_num)
theorem B3514757 : Blo 1152637 3514757 := bbase (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) (by norm_num)
theorem B2924981 : Blo 1152637 2924981 := bbase (se 5 (by rfl) ⟨137108, by rfl⟩ : syracuseStep 2924981 = 274217) (by norm_num)
theorem B2597309 : Blo 1152637 2597309 := bbase (se 3 (by rfl) ⟨486995, by rfl⟩ : syracuseStep 2597309 = 973991) (by norm_num)
theorem B2597381 : Blo 1152637 2597381 := bbase (se 4 (by rfl) ⟨243504, by rfl⟩ : syracuseStep 2597381 = 487009) (by norm_num)
theorem B2597453 : Blo 1152637 2597453 := bbase (se 3 (by rfl) ⟨487022, by rfl⟩ : syracuseStep 2597453 = 974045) (by norm_num)
theorem B2925173 : Blo 1152637 2925173 := bbase (se 5 (by rfl) ⟨137117, by rfl⟩ : syracuseStep 2925173 = 274235) (by norm_num)
theorem B5841557 : Blo 1152637 5841557 := bbase (se 6 (by rfl) ⟨136911, by rfl⟩ : syracuseStep 5841557 = 273823) (by norm_num)
theorem B2597525 : Blo 1152637 2597525 := bbase (se 6 (by rfl) ⟨60879, by rfl⟩ : syracuseStep 2597525 = 121759) (by norm_num)
theorem B2597597 : Blo 1152637 2597597 := bbase (se 3 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 2597597 = 974099) (by norm_num)
theorem B2597669 : Blo 1152637 2597669 := bbase (se 4 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 2597669 = 487063) (by norm_num)
theorem B2466629 : Blo 1152637 2466629 := bbase (se 4 (by rfl) ⟨231246, by rfl⟩ : syracuseStep 2466629 = 462493) (by norm_num)
theorem B2597741 : Blo 1152637 2597741 := bbase (se 3 (by rfl) ⟨487076, by rfl⟩ : syracuseStep 2597741 = 974153) (by norm_num)
theorem B1385345 : Blo 1152637 1385345 := bbase (se 2 (by rfl) ⟨519504, by rfl⟩ : syracuseStep 1385345 = 1039009) (by norm_num)
theorem B2597813 : Blo 1152637 2597813 := bbase (se 5 (by rfl) ⟨121772, by rfl⟩ : syracuseStep 2597813 = 243545) (by norm_num)
theorem B2466749 : Blo 1152637 2466749 := bbase (se 3 (by rfl) ⟨462515, by rfl⟩ : syracuseStep 2466749 = 925031) (by norm_num)
theorem B2925517 : Blo 1152637 2925517 := bbase (se 3 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 2925517 = 1097069) (by norm_num)
theorem B1385461 : Blo 1152637 1385461 := bbase (se 5 (by rfl) ⟨64943, by rfl⟩ : syracuseStep 1385461 = 129887) (by norm_num)
theorem B2597885 : Blo 1152637 2597885 := bbase (se 3 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 2597885 = 974207) (by norm_num)
theorem B1385533 : Blo 1152637 1385533 := bbase (se 3 (by rfl) ⟨259787, by rfl⟩ : syracuseStep 1385533 = 519575) (by norm_num)
theorem B2925629 : Blo 1152637 2925629 := bbase (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) (by norm_num)
theorem B2597957 : Blo 1152637 2597957 := bbase (se 4 (by rfl) ⟨243558, by rfl⟩ : syracuseStep 2597957 = 487117) (by norm_num)
theorem B6661237 : Blo 1152637 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B2598029 : Blo 1152637 2598029 := bbase (se 3 (by rfl) ⟨487130, by rfl⟩ : syracuseStep 2598029 = 974261) (by norm_num)
theorem B1385653 : Blo 1152637 1385653 := bbase (se 5 (by rfl) ⟨64952, by rfl⟩ : syracuseStep 1385653 = 129905) (by norm_num)
theorem B2598101 : Blo 1152637 2598101 := bbase (se 7 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 2598101 = 60893) (by norm_num)
theorem B2925821 : Blo 1152637 2925821 := bbase (se 3 (by rfl) ⟨548591, by rfl⟩ : syracuseStep 2925821 = 1097183) (by norm_num)
theorem B2598173 : Blo 1152637 2598173 := bbase (se 3 (by rfl) ⟨487157, by rfl⟩ : syracuseStep 2598173 = 974315) (by norm_num)
theorem B2598245 : Blo 1152637 2598245 := bbase (se 4 (by rfl) ⟨243585, by rfl⟩ : syracuseStep 2598245 = 487171) (by norm_num)
theorem B2598317 : Blo 1152637 2598317 := bbase (se 3 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 2598317 = 974369) (by norm_num)
theorem B3286469 : Blo 1152637 3286469 := bbase (se 4 (by rfl) ⟨308106, by rfl⟩ : syracuseStep 3286469 = 616213) (by norm_num)
theorem B2598389 : Blo 1152637 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B1386037 : Blo 1152637 1386037 := bbase (se 5 (by rfl) ⟨64970, by rfl⟩ : syracuseStep 1386037 = 129941) (by norm_num)
theorem B1975861 : Blo 1152637 1975861 := bbase (se 5 (by rfl) ⟨92618, by rfl⟩ : syracuseStep 1975861 = 185237) (by norm_num)
theorem B2467381 : Blo 1152637 2467381 := bbase (se 5 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 2467381 = 231317) (by norm_num)
theorem B2598461 : Blo 1152637 2598461 := bbase (se 3 (by rfl) ⟨487211, by rfl⟩ : syracuseStep 2598461 = 974423) (by norm_num)
theorem B2926165 : Blo 1152637 2926165 := bbase (se 8 (by rfl) ⟨17145, by rfl⟩ : syracuseStep 2926165 = 34291) (by norm_num)
theorem B2598533 : Blo 1152637 2598533 := bbase (se 4 (by rfl) ⟨243612, by rfl⟩ : syracuseStep 2598533 = 487225) (by norm_num)
theorem B5547685 : Blo 1152637 5547685 := bbase (se 4 (by rfl) ⟨520095, by rfl⟩ : syracuseStep 5547685 = 1040191) (by norm_num)
theorem B2926277 : Blo 1152637 2926277 := bbase (se 4 (by rfl) ⟨274338, by rfl⟩ : syracuseStep 2926277 = 548677) (by norm_num)
theorem B2598605 : Blo 1152637 2598605 := bbase (se 3 (by rfl) ⟨487238, by rfl⟩ : syracuseStep 2598605 = 974477) (by norm_num)
theorem B2631397 : Blo 1152637 2631397 := bbase (se 4 (by rfl) ⟨246693, by rfl⟩ : syracuseStep 2631397 = 493387) (by norm_num)
theorem B2598677 : Blo 1152637 2598677 := bbase (se 6 (by rfl) ⟨60906, by rfl⟩ : syracuseStep 2598677 = 121813) (by norm_num)
theorem B6235957 : Blo 1152637 6235957 := bbase (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) (by norm_num)
theorem B2598749 : Blo 1152637 2598749 := bbase (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) (by norm_num)
theorem B2926469 : Blo 1152637 2926469 := bbase (se 4 (by rfl) ⟨274356, by rfl⟩ : syracuseStep 2926469 = 548713) (by norm_num)
theorem B5842853 : Blo 1152637 5842853 := bbase (se 4 (by rfl) ⟨547767, by rfl⟩ : syracuseStep 5842853 = 1095535) (by norm_num)
theorem B2598821 : Blo 1152637 2598821 := bbase (se 4 (by rfl) ⟨243639, by rfl⟩ : syracuseStep 2598821 = 487279) (by norm_num)
theorem B2598893 : Blo 1152637 2598893 := bbase (se 3 (by rfl) ⟨487292, by rfl⟩ : syracuseStep 2598893 = 974585) (by norm_num)
theorem B2336797 : Blo 1152637 2336797 := bbase (se 3 (by rfl) ⟨438149, by rfl⟩ : syracuseStep 2336797 = 876299) (by norm_num)
theorem B2598965 : Blo 1152637 2598965 := bbase (se 5 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 2598965 = 243653) (by norm_num)
theorem B2599037 : Blo 1152637 2599037 := bbase (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) (by norm_num)
theorem B2599109 : Blo 1152637 2599109 := bbase (se 4 (by rfl) ⟨243666, by rfl⟩ : syracuseStep 2599109 = 487333) (by norm_num)
theorem B2926813 : Blo 1152637 2926813 := bbase (se 3 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 2926813 = 1097555) (by norm_num)
theorem B1386725 : Blo 1152637 1386725 := bbase (se 4 (by rfl) ⟨130005, by rfl⟩ : syracuseStep 1386725 = 260011) (by norm_num)
theorem B2599181 : Blo 1152637 2599181 := bbase (se 3 (by rfl) ⟨487346, by rfl⟩ : syracuseStep 2599181 = 974693) (by norm_num)
theorem B2926925 : Blo 1152637 2926925 := bbase (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) (by norm_num)
theorem B2599253 : Blo 1152637 2599253 := bbase (se 10 (by rfl) ⟨3807, by rfl⟩ : syracuseStep 2599253 = 7615) (by norm_num)
theorem B2599325 : Blo 1152637 2599325 := bbase (se 3 (by rfl) ⟨487373, by rfl⟩ : syracuseStep 2599325 = 974747) (by norm_num)
theorem B2468269 : Blo 1152637 2468269 := bbase (se 3 (by rfl) ⟨462800, by rfl⟩ : syracuseStep 2468269 = 925601) (by norm_num)
theorem B2599397 : Blo 1152637 2599397 := bbase (se 4 (by rfl) ⟨243693, by rfl⟩ : syracuseStep 2599397 = 487387) (by norm_num)
theorem B2927117 : Blo 1152637 2927117 := bbase (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) (by norm_num)
theorem B2468389 : Blo 1152637 2468389 := bbase (se 4 (by rfl) ⟨231411, by rfl⟩ : syracuseStep 2468389 = 462823) (by norm_num)
theorem B2107949 : Blo 1152637 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B2599469 : Blo 1152637 2599469 := bbase (se 3 (by rfl) ⟨487400, by rfl⟩ : syracuseStep 2599469 = 974801) (by norm_num)
theorem B2108005 : Blo 1152637 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B2599541 : Blo 1152637 2599541 := bbase (se 5 (by rfl) ⟨121853, by rfl⟩ : syracuseStep 2599541 = 243707) (by norm_num)
theorem B2599613 : Blo 1152637 2599613 := bbase (se 3 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 2599613 = 974855) (by norm_num)
theorem B2599685 : Blo 1152637 2599685 := bbase (se 4 (by rfl) ⟨243720, by rfl⟩ : syracuseStep 2599685 = 487441) (by norm_num)
theorem B2468645 : Blo 1152637 2468645 := bbase (se 4 (by rfl) ⟨231435, by rfl⟩ : syracuseStep 2468645 = 462871) (by norm_num)
theorem B1387325 : Blo 1152637 1387325 := bbase (se 3 (by rfl) ⟨260123, by rfl⟩ : syracuseStep 1387325 = 520247) (by norm_num)
theorem B2599757 : Blo 1152637 2599757 := bbase (se 3 (by rfl) ⟨487454, by rfl⟩ : syracuseStep 2599757 = 974909) (by norm_num)
theorem B8760149 : Blo 1152637 8760149 := bbase (se 9 (by rfl) ⟨25664, by rfl⟩ : syracuseStep 8760149 = 51329) (by norm_num)
theorem B2927461 : Blo 1152637 2927461 := bbase (se 4 (by rfl) ⟨274449, by rfl⟩ : syracuseStep 2927461 = 548899) (by norm_num)
theorem B2599829 : Blo 1152637 2599829 := bbase (se 6 (by rfl) ⟨60933, by rfl⟩ : syracuseStep 2599829 = 121867) (by norm_num)
theorem B18754517 : Blo 1152637 18754517 := bbase (se 7 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 18754517 = 439559) (by norm_num)
theorem B2927573 : Blo 1152637 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B2599901 : Blo 1152637 2599901 := bbase (se 3 (by rfl) ⟨487481, by rfl⟩ : syracuseStep 2599901 = 974963) (by norm_num)
theorem B3288053 : Blo 1152637 3288053 := bbase (se 5 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 3288053 = 308255) (by norm_num)
theorem B2599973 : Blo 1152637 2599973 := bbase (se 4 (by rfl) ⟨243747, by rfl⟩ : syracuseStep 2599973 = 487495) (by norm_num)
theorem B2600045 : Blo 1152637 2600045 := bbase (se 3 (by rfl) ⟨487508, by rfl⟩ : syracuseStep 2600045 = 975017) (by norm_num)
theorem B1387633 : Blo 1152637 1387633 := bbase (se 2 (by rfl) ⟨520362, by rfl⟩ : syracuseStep 1387633 = 1040725) (by norm_num)
theorem B5844149 : Blo 1152637 5844149 := bbase (se 5 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 5844149 = 547889) (by norm_num)
theorem B2600117 : Blo 1152637 2600117 := bbase (se 5 (by rfl) ⟨121880, by rfl⟩ : syracuseStep 2600117 = 243761) (by norm_num)
theorem B1387729 : Blo 1152637 1387729 := bbase (se 2 (by rfl) ⟨520398, by rfl⟩ : syracuseStep 1387729 = 1040797) (by norm_num)
theorem B2600189 : Blo 1152637 2600189 := bbase (se 3 (by rfl) ⟨487535, by rfl⟩ : syracuseStep 2600189 = 975071) (by norm_num)
theorem B1387777 : Blo 1152637 1387777 := bbase (se 2 (by rfl) ⟨520416, by rfl⟩ : syracuseStep 1387777 = 1040833) (by norm_num)
theorem B2600261 : Blo 1152637 2600261 := bbase (se 4 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 2600261 = 487549) (by norm_num)
theorem B1977709 : Blo 1152637 1977709 := bbase (se 3 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 1977709 = 741641) (by norm_num)
theorem B2600333 : Blo 1152637 2600333 := bbase (se 3 (by rfl) ⟨487562, by rfl⟩ : syracuseStep 2600333 = 975125) (by norm_num)
theorem B4926901 : Blo 1152637 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B2600405 : Blo 1152637 2600405 := bbase (se 7 (by rfl) ⟨30473, by rfl⟩ : syracuseStep 2600405 = 60947) (by norm_num)
theorem B1945093 : Blo 1152637 1945093 := bbase (se 4 (by rfl) ⟨182352, by rfl⟩ : syracuseStep 1945093 = 364705) (by norm_num)
theorem B2600477 : Blo 1152637 2600477 := bbase (se 3 (by rfl) ⟨487589, by rfl⟩ : syracuseStep 2600477 = 975179) (by norm_num)
theorem B1977941 : Blo 1152637 1977941 := bbase (se 8 (by rfl) ⟨11589, by rfl⟩ : syracuseStep 1977941 = 23179) (by norm_num)
theorem B1945181 : Blo 1152637 1945181 := bbase (se 3 (by rfl) ⟨364721, by rfl⟩ : syracuseStep 1945181 = 729443) (by norm_num)
theorem B2600549 : Blo 1152637 2600549 := bbase (se 4 (by rfl) ⟨243801, by rfl⟩ : syracuseStep 2600549 = 487603) (by norm_num)
theorem B3288725 : Blo 1152637 3288725 := bbase (se 6 (by rfl) ⟨77079, by rfl⟩ : syracuseStep 3288725 = 154159) (by norm_num)
theorem B2469533 : Blo 1152637 2469533 := bbase (se 3 (by rfl) ⟨463037, by rfl⟩ : syracuseStep 2469533 = 926075) (by norm_num)
theorem B2600621 : Blo 1152637 2600621 := bbase (se 3 (by rfl) ⟨487616, by rfl⟩ : syracuseStep 2600621 = 975233) (by norm_num)
theorem B1846973 : Blo 1152637 1846973 := bbase (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) (by norm_num)
theorem B2338517 : Blo 1152637 2338517 := bbase (se 7 (by rfl) ⟨27404, by rfl⟩ : syracuseStep 2338517 = 54809) (by norm_num)
theorem B1945309 : Blo 1152637 1945309 := bbase (se 3 (by rfl) ⟨364745, by rfl⟩ : syracuseStep 1945309 = 729491) (by norm_num)
theorem B2600693 : Blo 1152637 2600693 := bbase (se 5 (by rfl) ⟨121907, by rfl⟩ : syracuseStep 2600693 = 243815) (by norm_num)
theorem B1945397 : Blo 1152637 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B2600765 : Blo 1152637 2600765 := bbase (se 3 (by rfl) ⟨487643, by rfl⟩ : syracuseStep 2600765 = 975287) (by norm_num)
theorem B2600837 : Blo 1152637 2600837 := bbase (se 4 (by rfl) ⟨243828, by rfl⟩ : syracuseStep 2600837 = 487657) (by norm_num)
theorem B2469773 : Blo 1152637 2469773 := bbase (se 3 (by rfl) ⟨463082, by rfl⟩ : syracuseStep 2469773 = 926165) (by norm_num)
theorem B1945525 : Blo 1152637 1945525 := bbase (se 5 (by rfl) ⟨91196, by rfl⟩ : syracuseStep 1945525 = 182393) (by norm_num)
theorem B2600909 : Blo 1152637 2600909 := bbase (se 3 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 2600909 = 975341) (by norm_num)
theorem B1945613 : Blo 1152637 1945613 := bbase (se 3 (by rfl) ⟨364802, by rfl⟩ : syracuseStep 1945613 = 729605) (by norm_num)
theorem B2600981 : Blo 1152637 2600981 := bbase (se 6 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 2600981 = 121921) (by norm_num)
theorem B3289157 : Blo 1152637 3289157 := bbase (se 4 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 3289157 = 616717) (by norm_num)
theorem B2601053 : Blo 1152637 2601053 := bbase (se 3 (by rfl) ⟨487697, by rfl⟩ : syracuseStep 2601053 = 975395) (by norm_num)
theorem B1945741 : Blo 1152637 1945741 := bbase (se 3 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 1945741 = 729653) (by norm_num)
theorem B2601125 : Blo 1152637 2601125 := bbase (se 4 (by rfl) ⟨243855, by rfl⟩ : syracuseStep 2601125 = 487711) (by norm_num)
theorem B1945829 : Blo 1152637 1945829 := bbase (se 4 (by rfl) ⟨182421, by rfl⟩ : syracuseStep 1945829 = 364843) (by norm_num)
theorem B2601197 : Blo 1152637 2601197 := bbase (se 3 (by rfl) ⟨487724, by rfl⟩ : syracuseStep 2601197 = 975449) (by norm_num)
theorem B2601269 : Blo 1152637 2601269 := bbase (se 5 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 2601269 = 243869) (by norm_num)
theorem B1945957 : Blo 1152637 1945957 := bbase (se 4 (by rfl) ⟨182433, by rfl⟩ : syracuseStep 1945957 = 364867) (by norm_num)
theorem B2601341 : Blo 1152637 2601341 := bbase (se 3 (by rfl) ⟨487751, by rfl⟩ : syracuseStep 2601341 = 975503) (by norm_num)
theorem B2470277 : Blo 1152637 2470277 := bbase (se 4 (by rfl) ⟨231588, by rfl⟩ : syracuseStep 2470277 = 463177) (by norm_num)
theorem B1946045 : Blo 1152637 1946045 := bbase (se 3 (by rfl) ⟨364883, by rfl⟩ : syracuseStep 1946045 = 729767) (by norm_num)
theorem B1388993 : Blo 1152637 1388993 := bbase (se 2 (by rfl) ⟨520872, by rfl⟩ : syracuseStep 1388993 = 1041745) (by norm_num)
theorem B5845445 : Blo 1152637 5845445 := bbase (se 4 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 5845445 = 1096021) (by norm_num)
theorem B2601413 : Blo 1152637 2601413 := bbase (se 4 (by rfl) ⟨243882, by rfl⟩ : syracuseStep 2601413 = 487765) (by norm_num)
theorem B2601485 : Blo 1152637 2601485 := bbase (se 3 (by rfl) ⟨487778, by rfl⟩ : syracuseStep 2601485 = 975557) (by norm_num)
theorem B9351733 : Blo 1152637 9351733 := bbase (se 5 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 9351733 = 876725) (by norm_num)
theorem B1946173 : Blo 1152637 1946173 := bbase (se 3 (by rfl) ⟨364907, by rfl⟩ : syracuseStep 1946173 = 729815) (by norm_num)
theorem B2601557 : Blo 1152637 2601557 := bbase (se 8 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 2601557 = 30487) (by norm_num)
theorem B1847909 : Blo 1152637 1847909 := bbase (se 4 (by rfl) ⟨173241, by rfl⟩ : syracuseStep 1847909 = 346483) (by norm_num)
theorem B1389161 : Blo 1152637 1389161 := bbase (se 2 (by rfl) ⟨520935, by rfl⟩ : syracuseStep 1389161 = 1041871) (by norm_num)
theorem B1946261 : Blo 1152637 1946261 := bbase (se 6 (by rfl) ⟨45615, by rfl⟩ : syracuseStep 1946261 = 91231) (by norm_num)
theorem B2601629 : Blo 1152637 2601629 := bbase (se 3 (by rfl) ⟨487805, by rfl⟩ : syracuseStep 2601629 = 975611) (by norm_num)
theorem B2601701 : Blo 1152637 2601701 := bbase (se 4 (by rfl) ⟨243909, by rfl⟩ : syracuseStep 2601701 = 487819) (by norm_num)
theorem B1946389 : Blo 1152637 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B2601773 : Blo 1152637 2601773 := bbase (se 3 (by rfl) ⟨487832, by rfl⟩ : syracuseStep 2601773 = 975665) (by norm_num)
theorem B9351989 : Blo 1152637 9351989 := bbase (se 5 (by rfl) ⟨438374, by rfl⟩ : syracuseStep 9351989 = 876749) (by norm_num)
theorem B3289909 : Blo 1152637 3289909 := bbase (se 5 (by rfl) ⟨154214, by rfl⟩ : syracuseStep 3289909 = 308429) (by norm_num)
theorem B2372429 : Blo 1152637 2372429 := bbase (se 3 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 2372429 = 889661) (by norm_num)
theorem B6566741 : Blo 1152637 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B1946477 : Blo 1152637 1946477 := bbase (se 3 (by rfl) ⟨364964, by rfl⟩ : syracuseStep 1946477 = 729929) (by norm_num)
theorem B2601845 : Blo 1152637 2601845 := bbase (se 5 (by rfl) ⟨121961, by rfl⟩ : syracuseStep 2601845 = 243923) (by norm_num)
theorem B1389469 : Blo 1152637 1389469 := bbase (se 3 (by rfl) ⟨260525, by rfl⟩ : syracuseStep 1389469 = 521051) (by norm_num)
theorem B2601917 : Blo 1152637 2601917 := bbase (se 3 (by rfl) ⟨487859, by rfl⟩ : syracuseStep 2601917 = 975719) (by norm_num)
theorem B1946605 : Blo 1152637 1946605 := bbase (se 3 (by rfl) ⟨364988, by rfl⟩ : syracuseStep 1946605 = 729977) (by norm_num)
theorem B2601989 : Blo 1152637 2601989 := bbase (se 4 (by rfl) ⟨243936, by rfl⟩ : syracuseStep 2601989 = 487873) (by norm_num)
theorem B1946693 : Blo 1152637 1946693 := bbase (se 4 (by rfl) ⟨182502, by rfl⟩ : syracuseStep 1946693 = 365005) (by norm_num)
theorem B2602061 : Blo 1152637 2602061 := bbase (se 3 (by rfl) ⟨487886, by rfl⟩ : syracuseStep 2602061 = 975773) (by norm_num)
theorem B2602133 : Blo 1152637 2602133 := bbase (se 6 (by rfl) ⟨60987, by rfl⟩ : syracuseStep 2602133 = 121975) (by norm_num)
theorem B1946821 : Blo 1152637 1946821 := bbase (se 4 (by rfl) ⟨182514, by rfl⟩ : syracuseStep 1946821 = 365029) (by norm_num)
theorem B19739861 : Blo 1152637 19739861 := bbase (se 7 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 19739861 = 462653) (by norm_num)
theorem B2602205 : Blo 1152637 2602205 := bbase (se 3 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 2602205 = 975827) (by norm_num)
theorem B1848557 : Blo 1152637 1848557 := bbase (se 3 (by rfl) ⟨346604, by rfl⟩ : syracuseStep 1848557 = 693209) (by norm_num)
theorem B1946909 : Blo 1152637 1946909 := bbase (se 3 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 1946909 = 730091) (by norm_num)
theorem B2602277 : Blo 1152637 2602277 := bbase (se 4 (by rfl) ⟨243963, by rfl⟩ : syracuseStep 2602277 = 487927) (by norm_num)
theorem B2602349 : Blo 1152637 2602349 := bbase (se 3 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 2602349 = 975881) (by norm_num)
theorem B1947037 : Blo 1152637 1947037 := bbase (se 3 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 1947037 = 730139) (by norm_num)
theorem B2602421 : Blo 1152637 2602421 := bbase (se 5 (by rfl) ⟨121988, by rfl⟩ : syracuseStep 2602421 = 243977) (by norm_num)
theorem B2340317 : Blo 1152637 2340317 := bbase (se 3 (by rfl) ⟨438809, by rfl⟩ : syracuseStep 2340317 = 877619) (by norm_num)
theorem B2373085 : Blo 1152637 2373085 := bbase (se 3 (by rfl) ⟨444953, by rfl⟩ : syracuseStep 2373085 = 889907) (by norm_num)
theorem B1947125 : Blo 1152637 1947125 := bbase (se 5 (by rfl) ⟨91271, by rfl⟩ : syracuseStep 1947125 = 182543) (by norm_num)
theorem B5551685 : Blo 1152637 5551685 := bbase (se 4 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 5551685 = 1040941) (by norm_num)
theorem B8336981 : Blo 1152637 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B1947253 : Blo 1152637 1947253 := bbase (se 5 (by rfl) ⟨91277, by rfl⟩ : syracuseStep 1947253 = 182555) (by norm_num)
theorem B1947341 : Blo 1152637 1947341 := bbase (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) (by norm_num)
theorem B5846741 : Blo 1152637 5846741 := bbase (se 7 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 5846741 = 137033) (by norm_num)
theorem B1947469 : Blo 1152637 1947469 := bbase (se 3 (by rfl) ⟨365150, by rfl⟩ : syracuseStep 1947469 = 730301) (by norm_num)
theorem B5551973 : Blo 1152637 5551973 := bbase (se 4 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 5551973 = 1040995) (by norm_num)
theorem B11384725 : Blo 1152637 11384725 := bbase (se 6 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 11384725 = 533659) (by norm_num)
theorem B1947557 : Blo 1152637 1947557 := bbase (se 4 (by rfl) ⟨182583, by rfl⟩ : syracuseStep 1947557 = 365167) (by norm_num)
theorem B6567925 : Blo 1152637 6567925 := bbase (se 5 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 6567925 = 615743) (by norm_num)
theorem B1947685 : Blo 1152637 1947685 := bbase (se 4 (by rfl) ⟨182595, by rfl⟩ : syracuseStep 1947685 = 365191) (by norm_num)
theorem B2078797 : Blo 1152637 2078797 := bbase (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) (by norm_num)
theorem B2340949 : Blo 1152637 2340949 := bbase (se 8 (by rfl) ⟨13716, by rfl⟩ : syracuseStep 2340949 = 27433) (by norm_num)
theorem B1947773 : Blo 1152637 1947773 := bbase (se 3 (by rfl) ⟨365207, by rfl⟩ : syracuseStep 1947773 = 730415) (by norm_num)
theorem B1849549 : Blo 1152637 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B1947901 : Blo 1152637 1947901 := bbase (se 3 (by rfl) ⟨365231, by rfl⟩ : syracuseStep 1947901 = 730463) (by norm_num)
theorem B1947989 : Blo 1152637 1947989 := bbase (se 10 (by rfl) ⟨2853, by rfl⟩ : syracuseStep 1947989 = 5707) (by norm_num)
theorem B4929893 : Blo 1152637 4929893 := bbase (se 4 (by rfl) ⟨462177, by rfl⟩ : syracuseStep 4929893 = 924355) (by norm_num)
theorem B1948117 : Blo 1152637 1948117 := bbase (se 7 (by rfl) ⟨22829, by rfl⟩ : syracuseStep 1948117 = 45659) (by norm_num)
theorem B1948205 : Blo 1152637 1948205 := bbase (se 3 (by rfl) ⟨365288, by rfl⟩ : syracuseStep 1948205 = 730577) (by norm_num)
theorem B2341469 : Blo 1152637 2341469 := bbase (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) (by norm_num)
theorem B1849997 : Blo 1152637 1849997 := bbase (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) (by norm_num)
theorem B1948333 : Blo 1152637 1948333 := bbase (se 3 (by rfl) ⟨365312, by rfl⟩ : syracuseStep 1948333 = 730625) (by norm_num)
theorem B1948421 : Blo 1152637 1948421 := bbase (se 4 (by rfl) ⟨182664, by rfl⟩ : syracuseStep 1948421 = 365329) (by norm_num)
theorem B2079517 : Blo 1152637 2079517 := bbase (se 3 (by rfl) ⟨389909, by rfl⟩ : syracuseStep 2079517 = 779819) (by norm_num)
theorem B1424177 : Blo 1152637 1424177 := bbase (se 2 (by rfl) ⟨534066, by rfl⟩ : syracuseStep 1424177 = 1068133) (by norm_num)
theorem B1850197 : Blo 1152637 1850197 := bbase (se 9 (by rfl) ⟨5420, by rfl⟩ : syracuseStep 1850197 = 10841) (by norm_num)
theorem B1948549 : Blo 1152637 1948549 := bbase (se 4 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 1948549 = 365353) (by norm_num)
theorem B1948637 : Blo 1152637 1948637 := bbase (se 3 (by rfl) ⟨365369, by rfl⟩ : syracuseStep 1948637 = 730739) (by norm_num)
theorem B5848037 : Blo 1152637 5848037 := bbase (se 4 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 5848037 = 1096507) (by norm_num)
theorem B2079749 : Blo 1152637 2079749 := bbase (se 4 (by rfl) ⟨194976, by rfl⟩ : syracuseStep 2079749 = 389953) (by norm_num)
theorem B1850453 : Blo 1152637 1850453 := bbase (se 8 (by rfl) ⟨10842, by rfl⟩ : syracuseStep 1850453 = 21685) (by norm_num)
theorem B1948765 : Blo 1152637 1948765 := bbase (se 3 (by rfl) ⟨365393, by rfl⟩ : syracuseStep 1948765 = 730787) (by norm_num)
theorem B1948853 : Blo 1152637 1948853 := bbase (se 5 (by rfl) ⟨91352, by rfl⟩ : syracuseStep 1948853 = 182705) (by norm_num)
theorem B7388405 : Blo 1152637 7388405 := bbase (se 5 (by rfl) ⟨346331, by rfl⟩ : syracuseStep 7388405 = 692663) (by norm_num)
theorem B1948981 : Blo 1152637 1948981 := bbase (se 5 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 1948981 = 182717) (by norm_num)
theorem B4930901 : Blo 1152637 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B1949069 : Blo 1152637 1949069 := bbase (se 3 (by rfl) ⟨365450, by rfl⟩ : syracuseStep 1949069 = 730901) (by norm_num)
theorem B2080181 : Blo 1152637 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B2964941 : Blo 1152637 2964941 := bbase (se 3 (by rfl) ⟨555926, by rfl⟩ : syracuseStep 2964941 = 1111853) (by norm_num)
theorem B1949197 : Blo 1152637 1949197 := bbase (se 3 (by rfl) ⟨365474, by rfl⟩ : syracuseStep 1949197 = 730949) (by norm_num)
theorem B2080325 : Blo 1152637 2080325 := bbase (se 4 (by rfl) ⟨195030, by rfl⟩ : syracuseStep 2080325 = 390061) (by norm_num)
theorem B3292757 : Blo 1152637 3292757 := bbase (se 8 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 3292757 = 38587) (by norm_num)
theorem B1949285 : Blo 1152637 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B1949413 : Blo 1152637 1949413 := bbase (se 4 (by rfl) ⟨182757, by rfl⟩ : syracuseStep 1949413 = 365515) (by norm_num)
theorem B1949501 : Blo 1152637 1949501 := bbase (se 3 (by rfl) ⟨365531, by rfl⟩ : syracuseStep 1949501 = 731063) (by norm_num)
theorem B2080613 : Blo 1152637 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B6569909 : Blo 1152637 6569909 := bbase (se 5 (by rfl) ⟨307964, by rfl⟩ : syracuseStep 6569909 = 615929) (by norm_num)
theorem B1949629 : Blo 1152637 1949629 := bbase (se 3 (by rfl) ⟨365555, by rfl⟩ : syracuseStep 1949629 = 731111) (by norm_num)
theorem B1949717 : Blo 1152637 1949717 := bbase (se 6 (by rfl) ⟨45696, by rfl⟩ : syracuseStep 1949717 = 91393) (by norm_num)
theorem B2080837 : Blo 1152637 2080837 := bbase (se 4 (by rfl) ⟨195078, by rfl⟩ : syracuseStep 2080837 = 390157) (by norm_num)
theorem B2080901 : Blo 1152637 2080901 := bbase (se 4 (by rfl) ⟨195084, by rfl⟩ : syracuseStep 2080901 = 390169) (by norm_num)
theorem B1949845 : Blo 1152637 1949845 := bbase (se 6 (by rfl) ⟨45699, by rfl⟩ : syracuseStep 1949845 = 91399) (by norm_num)
theorem B1851581 : Blo 1152637 1851581 := bbase (se 3 (by rfl) ⟨347171, by rfl⟩ : syracuseStep 1851581 = 694343) (by norm_num)
theorem B1949933 : Blo 1152637 1949933 := bbase (se 3 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 1949933 = 731225) (by norm_num)
theorem B5849333 : Blo 1152637 5849333 := bbase (se 5 (by rfl) ⟨274187, by rfl⟩ : syracuseStep 5849333 = 548375) (by norm_num)
theorem B2965805 : Blo 1152637 2965805 := bbase (se 3 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 2965805 = 1112177) (by norm_num)
theorem B1950061 : Blo 1152637 1950061 := bbase (se 3 (by rfl) ⟨365636, by rfl⟩ : syracuseStep 1950061 = 731273) (by norm_num)
theorem B2343277 : Blo 1152637 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B11092373 : Blo 1152637 11092373 := bbase (se 6 (by rfl) ⟨259977, by rfl⟩ : syracuseStep 11092373 = 519955) (by norm_num)
theorem B1950149 : Blo 1152637 1950149 := bbase (se 4 (by rfl) ⟨182826, by rfl⟩ : syracuseStep 1950149 = 365653) (by norm_num)
theorem B7029269 : Blo 1152637 7029269 := bbase (se 6 (by rfl) ⟨164748, by rfl⟩ : syracuseStep 7029269 = 329497) (by norm_num)
theorem B1950277 : Blo 1152637 1950277 := bbase (se 4 (by rfl) ⟨182838, by rfl⟩ : syracuseStep 1950277 = 365677) (by norm_num)
theorem B1950365 : Blo 1152637 1950365 := bbase (se 3 (by rfl) ⟨365693, by rfl⟩ : syracuseStep 1950365 = 731387) (by norm_num)
theorem B1852093 : Blo 1152637 1852093 := bbase (se 3 (by rfl) ⟨347267, by rfl⟩ : syracuseStep 1852093 = 694535) (by norm_num)
theorem B2966213 : Blo 1152637 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B1458901 : Blo 1152637 1458901 := bbase (se 7 (by rfl) ⟨17096, by rfl⟩ : syracuseStep 1458901 = 34193) (by norm_num)
theorem B2769653 : Blo 1152637 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B1950493 : Blo 1152637 1950493 := bbase (se 3 (by rfl) ⟨365717, by rfl⟩ : syracuseStep 1950493 = 731435) (by norm_num)
theorem B1950581 : Blo 1152637 1950581 := bbase (se 5 (by rfl) ⟨91433, by rfl⟩ : syracuseStep 1950581 = 182867) (by norm_num)
theorem B1459073 : Blo 1152637 1459073 := bbase (se 2 (by rfl) ⟨547152, by rfl⟩ : syracuseStep 1459073 = 1094305) (by norm_num)
theorem B1459129 : Blo 1152637 1459129 := bbase (se 2 (by rfl) ⟨547173, by rfl⟩ : syracuseStep 1459129 = 1094347) (by norm_num)
theorem B1950709 : Blo 1152637 1950709 := bbase (se 5 (by rfl) ⟨91439, by rfl⟩ : syracuseStep 1950709 = 182879) (by norm_num)
theorem B1459225 : Blo 1152637 1459225 := bbase (se 2 (by rfl) ⟨547209, by rfl⟩ : syracuseStep 1459225 = 1094419) (by norm_num)
theorem B4932677 : Blo 1152637 4932677 := bbase (se 4 (by rfl) ⟨462438, by rfl⟩ : syracuseStep 4932677 = 924877) (by norm_num)
theorem B1950797 : Blo 1152637 1950797 := bbase (se 3 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 1950797 = 731549) (by norm_num)
theorem B9847925 : Blo 1152637 9847925 := bbase (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) (by norm_num)
theorem B1459397 : Blo 1152637 1459397 := bbase (se 4 (by rfl) ⟨136818, by rfl⟩ : syracuseStep 1459397 = 273637) (by norm_num)
theorem B1950925 : Blo 1152637 1950925 := bbase (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) (by norm_num)
theorem B1852637 : Blo 1152637 1852637 := bbase (se 3 (by rfl) ⟨347369, by rfl⟩ : syracuseStep 1852637 = 694739) (by norm_num)
theorem B1459453 : Blo 1152637 1459453 := bbase (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) (by norm_num)
theorem B1951013 : Blo 1152637 1951013 := bbase (se 4 (by rfl) ⟨182907, by rfl⟩ : syracuseStep 1951013 = 365815) (by norm_num)
theorem B2770229 : Blo 1152637 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B1459549 : Blo 1152637 1459549 := bbase (se 3 (by rfl) ⟨273665, by rfl⟩ : syracuseStep 1459549 = 547331) (by norm_num)
theorem B1951141 : Blo 1152637 1951141 := bbase (se 4 (by rfl) ⟨182919, by rfl⟩ : syracuseStep 1951141 = 365839) (by norm_num)
theorem B2344405 : Blo 1152637 2344405 := bbase (se 7 (by rfl) ⟨27473, by rfl⟩ : syracuseStep 2344405 = 54947) (by norm_num)
theorem B1951229 : Blo 1152637 1951229 := bbase (se 3 (by rfl) ⟨365855, by rfl⟩ : syracuseStep 1951229 = 731711) (by norm_num)
theorem B5850629 : Blo 1152637 5850629 := bbase (se 4 (by rfl) ⟨548496, by rfl⟩ : syracuseStep 5850629 = 1096993) (by norm_num)
theorem B1459721 : Blo 1152637 1459721 := bbase (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) (by norm_num)
theorem B1459777 : Blo 1152637 1459777 := bbase (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) (by norm_num)
theorem B1951357 : Blo 1152637 1951357 := bbase (se 3 (by rfl) ⟨365879, by rfl⟩ : syracuseStep 1951357 = 731759) (by norm_num)
theorem B1459873 : Blo 1152637 1459873 := bbase (se 2 (by rfl) ⟨547452, by rfl⟩ : syracuseStep 1459873 = 1094905) (by norm_num)
theorem B1951445 : Blo 1152637 1951445 := bbase (se 7 (by rfl) ⟨22868, by rfl⟩ : syracuseStep 1951445 = 45737) (by norm_num)
theorem B1460045 : Blo 1152637 1460045 := bbase (se 3 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 1460045 = 547517) (by norm_num)
theorem B1951573 : Blo 1152637 1951573 := bbase (se 9 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 1951573 = 11435) (by norm_num)
theorem B1460101 : Blo 1152637 1460101 := bbase (se 4 (by rfl) ⟨136884, by rfl⟩ : syracuseStep 1460101 = 273769) (by norm_num)
theorem B1951661 : Blo 1152637 1951661 := bbase (se 3 (by rfl) ⟨365936, by rfl⟩ : syracuseStep 1951661 = 731873) (by norm_num)
theorem B1460197 : Blo 1152637 1460197 := bbase (se 4 (by rfl) ⟨136893, by rfl⟩ : syracuseStep 1460197 = 273787) (by norm_num)
theorem B2672645 : Blo 1152637 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B1951789 : Blo 1152637 1951789 := bbase (se 3 (by rfl) ⟨365960, by rfl⟩ : syracuseStep 1951789 = 731921) (by norm_num)
theorem B6572117 : Blo 1152637 6572117 := bbase (se 8 (by rfl) ⟨38508, by rfl⟩ : syracuseStep 6572117 = 77017) (by norm_num)
theorem B1460369 : Blo 1152637 1460369 := bbase (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) (by norm_num)
theorem B1460425 : Blo 1152637 1460425 := bbase (se 2 (by rfl) ⟨547659, by rfl⟩ : syracuseStep 1460425 = 1095319) (by norm_num)
theorem B1231085 : Blo 1152637 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B1460521 : Blo 1152637 1460521 := bbase (se 2 (by rfl) ⟨547695, by rfl⟩ : syracuseStep 1460521 = 1095391) (by norm_num)
theorem B1755445 : Blo 1152637 1755445 := bbase (se 5 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 1755445 = 164573) (by norm_num)
theorem B3754309 : Blo 1152637 3754309 := bbase (se 4 (by rfl) ⟨351966, by rfl⟩ : syracuseStep 3754309 = 703933) (by norm_num)
theorem B1296733 : Blo 1152637 1296733 := bbase (se 3 (by rfl) ⟨243137, by rfl⟩ : syracuseStep 1296733 = 486275) (by norm_num)
theorem B4442485 : Blo 1152637 4442485 := bbase (se 5 (by rfl) ⟨208241, by rfl⟩ : syracuseStep 4442485 = 416483) (by norm_num)
theorem B1296769 : Blo 1152637 1296769 := bbase (se 2 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 1296769 = 972577) (by norm_num)
theorem B1296805 : Blo 1152637 1296805 := bbase (se 4 (by rfl) ⟨121575, by rfl⟩ : syracuseStep 1296805 = 243151) (by norm_num)
theorem B8767925 : Blo 1152637 8767925 := bbase (se 5 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 8767925 = 821993) (by norm_num)
theorem B1296841 : Blo 1152637 1296841 := bbase (se 2 (by rfl) ⟨486315, by rfl⟩ : syracuseStep 1296841 = 972631) (by norm_num)
theorem B1460693 : Blo 1152637 1460693 := bbase (se 7 (by rfl) ⟨17117, by rfl⟩ : syracuseStep 1460693 = 34235) (by norm_num)
theorem B5917157 : Blo 1152637 5917157 := bbase (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) (by norm_num)
theorem B1296877 : Blo 1152637 1296877 := bbase (se 3 (by rfl) ⟨243164, by rfl⟩ : syracuseStep 1296877 = 486329) (by norm_num)
theorem B1460749 : Blo 1152637 1460749 := bbase (se 3 (by rfl) ⟨273890, by rfl⟩ : syracuseStep 1460749 = 547781) (by norm_num)
theorem B1296913 : Blo 1152637 1296913 := bbase (se 2 (by rfl) ⟨486342, by rfl⟩ : syracuseStep 1296913 = 972685) (by norm_num)
theorem B5556757 : Blo 1152637 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B1296949 : Blo 1152637 1296949 := bbase (se 5 (by rfl) ⟨60794, by rfl⟩ : syracuseStep 1296949 = 121589) (by norm_num)
theorem B1296985 : Blo 1152637 1296985 := bbase (se 2 (by rfl) ⟨486369, by rfl⟩ : syracuseStep 1296985 = 972739) (by norm_num)
theorem B1460845 : Blo 1152637 1460845 := bbase (se 3 (by rfl) ⟨273908, by rfl⟩ : syracuseStep 1460845 = 547817) (by norm_num)
theorem B1297021 : Blo 1152637 1297021 := bbase (se 3 (by rfl) ⟨243191, by rfl⟩ : syracuseStep 1297021 = 486383) (by norm_num)
theorem B1297057 : Blo 1152637 1297057 := bbase (se 2 (by rfl) ⟨486396, by rfl⟩ : syracuseStep 1297057 = 972793) (by norm_num)
theorem B1231529 : Blo 1152637 1231529 := bbase (se 2 (by rfl) ⟨461823, by rfl⟩ : syracuseStep 1231529 = 923647) (by norm_num)
theorem B1297093 : Blo 1152637 1297093 := bbase (se 4 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 1297093 = 243205) (by norm_num)
theorem B1297129 : Blo 1152637 1297129 := bbase (se 2 (by rfl) ⟨486423, by rfl⟩ : syracuseStep 1297129 = 972847) (by norm_num)
theorem B1297165 : Blo 1152637 1297165 := bbase (se 3 (by rfl) ⟨243218, by rfl⟩ : syracuseStep 1297165 = 486437) (by norm_num)
theorem B5851925 : Blo 1152637 5851925 := bbase (se 6 (by rfl) ⟨137154, by rfl⟩ : syracuseStep 5851925 = 274309) (by norm_num)
theorem B1461017 : Blo 1152637 1461017 := bbase (se 2 (by rfl) ⟨547881, by rfl⟩ : syracuseStep 1461017 = 1095763) (by norm_num)
theorem B1297201 : Blo 1152637 1297201 := bbase (se 2 (by rfl) ⟨486450, by rfl⟩ : syracuseStep 1297201 = 972901) (by norm_num)
theorem B1461073 : Blo 1152637 1461073 := bbase (se 2 (by rfl) ⟨547902, by rfl⟩ : syracuseStep 1461073 = 1095805) (by norm_num)
theorem B1297237 : Blo 1152637 1297237 := bbase (se 9 (by rfl) ⟨3800, by rfl⟩ : syracuseStep 1297237 = 7601) (by norm_num)
theorem B1297273 : Blo 1152637 1297273 := bbase (se 2 (by rfl) ⟨486477, by rfl⟩ : syracuseStep 1297273 = 972955) (by norm_num)
theorem B1297309 : Blo 1152637 1297309 := bbase (se 3 (by rfl) ⟨243245, by rfl⟩ : syracuseStep 1297309 = 486491) (by norm_num)
theorem B1231777 : Blo 1152637 1231777 := bbase (se 2 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 1231777 = 923833) (by norm_num)
theorem B4377509 : Blo 1152637 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B1461169 : Blo 1152637 1461169 := bbase (se 2 (by rfl) ⟨547938, by rfl⟩ : syracuseStep 1461169 = 1095877) (by norm_num)
theorem B1297345 : Blo 1152637 1297345 := bbase (se 2 (by rfl) ⟨486504, by rfl⟩ : syracuseStep 1297345 = 973009) (by norm_num)
theorem B1297381 : Blo 1152637 1297381 := bbase (se 4 (by rfl) ⟨121629, by rfl⟩ : syracuseStep 1297381 = 243259) (by norm_num)
theorem B1297417 : Blo 1152637 1297417 := bbase (se 2 (by rfl) ⟨486531, by rfl⟩ : syracuseStep 1297417 = 973063) (by norm_num)
theorem B1297453 : Blo 1152637 1297453 := bbase (se 3 (by rfl) ⟨243272, by rfl⟩ : syracuseStep 1297453 = 486545) (by norm_num)
theorem B1297489 : Blo 1152637 1297489 := bbase (se 2 (by rfl) ⟨486558, by rfl⟩ : syracuseStep 1297489 = 973117) (by norm_num)
theorem B1461341 : Blo 1152637 1461341 := bbase (se 3 (by rfl) ⟨274001, by rfl⟩ : syracuseStep 1461341 = 548003) (by norm_num)
theorem B1297525 : Blo 1152637 1297525 := bbase (se 5 (by rfl) ⟨60821, by rfl⟩ : syracuseStep 1297525 = 121643) (by norm_num)
theorem B1461397 : Blo 1152637 1461397 := bbase (se 6 (by rfl) ⟨34251, by rfl⟩ : syracuseStep 1461397 = 68503) (by norm_num)
theorem B1297561 : Blo 1152637 1297561 := bbase (se 2 (by rfl) ⟨486585, by rfl⟩ : syracuseStep 1297561 = 973171) (by norm_num)
theorem B1297597 : Blo 1152637 1297597 := bbase (se 3 (by rfl) ⟨243299, by rfl⟩ : syracuseStep 1297597 = 486599) (by norm_num)
theorem B4377797 : Blo 1152637 4377797 := bbase (se 4 (by rfl) ⟨410418, by rfl⟩ : syracuseStep 4377797 = 820837) (by norm_num)
theorem B1297633 : Blo 1152637 1297633 := bbase (se 2 (by rfl) ⟨486612, by rfl⟩ : syracuseStep 1297633 = 973225) (by norm_num)
theorem B1461493 : Blo 1152637 1461493 := bbase (se 5 (by rfl) ⟨68507, by rfl⟩ : syracuseStep 1461493 = 137015) (by norm_num)
theorem B1297669 : Blo 1152637 1297669 := bbase (se 4 (by rfl) ⟨121656, by rfl⟩ : syracuseStep 1297669 = 243313) (by norm_num)
theorem B1297705 : Blo 1152637 1297705 := bbase (se 2 (by rfl) ⟨486639, by rfl⟩ : syracuseStep 1297705 = 973279) (by norm_num)
theorem B1297741 : Blo 1152637 1297741 := bbase (se 3 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 1297741 = 486653) (by norm_num)
theorem B1232221 : Blo 1152637 1232221 := bbase (se 3 (by rfl) ⟨231041, by rfl⟩ : syracuseStep 1232221 = 462083) (by norm_num)
theorem B1297777 : Blo 1152637 1297777 := bbase (se 2 (by rfl) ⟨486666, by rfl⟩ : syracuseStep 1297777 = 973333) (by norm_num)
theorem B1297813 : Blo 1152637 1297813 := bbase (se 6 (by rfl) ⟨30417, by rfl⟩ : syracuseStep 1297813 = 60835) (by norm_num)
theorem B1232281 : Blo 1152637 1232281 := bbase (se 2 (by rfl) ⟨462105, by rfl⟩ : syracuseStep 1232281 = 924211) (by norm_num)
theorem B1461665 : Blo 1152637 1461665 := bbase (se 2 (by rfl) ⟨548124, by rfl⟩ : syracuseStep 1461665 = 1096249) (by norm_num)
theorem B1297849 : Blo 1152637 1297849 := bbase (se 2 (by rfl) ⟨486693, by rfl⟩ : syracuseStep 1297849 = 973387) (by norm_num)
theorem B1461721 : Blo 1152637 1461721 := bbase (se 2 (by rfl) ⟨548145, by rfl⟩ : syracuseStep 1461721 = 1096291) (by norm_num)
theorem B1297885 : Blo 1152637 1297885 := bbase (se 3 (by rfl) ⟨243353, by rfl⟩ : syracuseStep 1297885 = 486707) (by norm_num)
theorem B1297921 : Blo 1152637 1297921 := bbase (se 2 (by rfl) ⟨486720, by rfl⟩ : syracuseStep 1297921 = 973441) (by norm_num)
theorem B1297957 : Blo 1152637 1297957 := bbase (se 4 (by rfl) ⟨121683, by rfl⟩ : syracuseStep 1297957 = 243367) (by norm_num)
theorem B1560109 : Blo 1152637 1560109 := bbase (se 3 (by rfl) ⟨292520, by rfl⟩ : syracuseStep 1560109 = 585041) (by norm_num)
theorem B1461817 : Blo 1152637 1461817 := bbase (se 2 (by rfl) ⟨548181, by rfl⟩ : syracuseStep 1461817 = 1096363) (by norm_num)
theorem B1297993 : Blo 1152637 1297993 := bbase (se 2 (by rfl) ⟨486747, by rfl⟩ : syracuseStep 1297993 = 973495) (by norm_num)
theorem B1298029 : Blo 1152637 1298029 := bbase (se 3 (by rfl) ⟨243380, by rfl⟩ : syracuseStep 1298029 = 486761) (by norm_num)
theorem B1298065 : Blo 1152637 1298065 := bbase (se 2 (by rfl) ⟨486774, by rfl⟩ : syracuseStep 1298065 = 973549) (by norm_num)
theorem B1298101 : Blo 1152637 1298101 := bbase (se 5 (by rfl) ⟨60848, by rfl⟩ : syracuseStep 1298101 = 121697) (by norm_num)
theorem B1232597 : Blo 1152637 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B1298137 : Blo 1152637 1298137 := bbase (se 2 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 1298137 = 973603) (by norm_num)
theorem B1461989 : Blo 1152637 1461989 := bbase (se 4 (by rfl) ⟨137061, by rfl⟩ : syracuseStep 1461989 = 274123) (by norm_num)
theorem B1298173 : Blo 1152637 1298173 := bbase (se 3 (by rfl) ⟨243407, by rfl⟩ : syracuseStep 1298173 = 486815) (by norm_num)
theorem B1462045 : Blo 1152637 1462045 := bbase (se 3 (by rfl) ⟨274133, by rfl⟩ : syracuseStep 1462045 = 548267) (by norm_num)
theorem B1298209 : Blo 1152637 1298209 := bbase (se 2 (by rfl) ⟨486828, by rfl⟩ : syracuseStep 1298209 = 973657) (by norm_num)
theorem B3952421 : Blo 1152637 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B1298245 : Blo 1152637 1298245 := bbase (se 4 (by rfl) ⟨121710, by rfl⟩ : syracuseStep 1298245 = 243421) (by norm_num)
theorem B2772805 : Blo 1152637 2772805 := bbase (se 4 (by rfl) ⟨259950, by rfl⟩ : syracuseStep 2772805 = 519901) (by norm_num)
theorem B1298281 : Blo 1152637 1298281 := bbase (se 2 (by rfl) ⟨486855, by rfl⟩ : syracuseStep 1298281 = 973711) (by norm_num)
theorem B1462141 : Blo 1152637 1462141 := bbase (se 3 (by rfl) ⟨274151, by rfl⟩ : syracuseStep 1462141 = 548303) (by norm_num)
theorem B1298317 : Blo 1152637 1298317 := bbase (se 3 (by rfl) ⟨243434, by rfl⟩ : syracuseStep 1298317 = 486869) (by norm_num)
theorem B1298353 : Blo 1152637 1298353 := bbase (se 2 (by rfl) ⟨486882, by rfl⟩ : syracuseStep 1298353 = 973765) (by norm_num)
theorem B1298389 : Blo 1152637 1298389 := bbase (se 7 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 1298389 = 30431) (by norm_num)
theorem B1298425 : Blo 1152637 1298425 := bbase (se 2 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 1298425 = 973819) (by norm_num)
theorem B1560589 : Blo 1152637 1560589 := bbase (se 3 (by rfl) ⟨292610, by rfl⟩ : syracuseStep 1560589 = 585221) (by norm_num)
theorem B1298461 : Blo 1152637 1298461 := bbase (se 3 (by rfl) ⟨243461, by rfl⟩ : syracuseStep 1298461 = 486923) (by norm_num)
theorem B5853221 : Blo 1152637 5853221 := bbase (se 4 (by rfl) ⟨548739, by rfl⟩ : syracuseStep 5853221 = 1097479) (by norm_num)
theorem B1462313 : Blo 1152637 1462313 := bbase (se 2 (by rfl) ⟨548367, by rfl⟩ : syracuseStep 1462313 = 1096735) (by norm_num)
theorem B1298497 : Blo 1152637 1298497 := bbase (se 2 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 1298497 = 973873) (by norm_num)
theorem B1462369 : Blo 1152637 1462369 := bbase (se 2 (by rfl) ⟨548388, by rfl⟩ : syracuseStep 1462369 = 1096777) (by norm_num)
theorem B1298533 : Blo 1152637 1298533 := bbase (se 4 (by rfl) ⟨121737, by rfl⟩ : syracuseStep 1298533 = 243475) (by norm_num)
theorem B1298569 : Blo 1152637 1298569 := bbase (se 2 (by rfl) ⟨486963, by rfl⟩ : syracuseStep 1298569 = 973927) (by norm_num)
theorem B1233041 : Blo 1152637 1233041 := bbase (se 2 (by rfl) ⟨462390, by rfl⟩ : syracuseStep 1233041 = 924781) (by norm_num)
theorem B1298605 : Blo 1152637 1298605 := bbase (se 3 (by rfl) ⟨243488, by rfl⟩ : syracuseStep 1298605 = 486977) (by norm_num)
theorem B1462465 : Blo 1152637 1462465 := bbase (se 2 (by rfl) ⟨548424, by rfl⟩ : syracuseStep 1462465 = 1096849) (by norm_num)
theorem B1233101 : Blo 1152637 1233101 := bbase (se 3 (by rfl) ⟨231206, by rfl⟩ : syracuseStep 1233101 = 462413) (by norm_num)
theorem B1298641 : Blo 1152637 1298641 := bbase (se 2 (by rfl) ⟨486990, by rfl⟩ : syracuseStep 1298641 = 973981) (by norm_num)
theorem B1298677 : Blo 1152637 1298677 := bbase (se 5 (by rfl) ⟨60875, by rfl⟩ : syracuseStep 1298677 = 121751) (by norm_num)
theorem B1298713 : Blo 1152637 1298713 := bbase (se 2 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 1298713 = 974035) (by norm_num)
theorem B1298749 : Blo 1152637 1298749 := bbase (se 3 (by rfl) ⟨243515, by rfl⟩ : syracuseStep 1298749 = 487031) (by norm_num)
theorem B1233229 : Blo 1152637 1233229 := bbase (se 3 (by rfl) ⟨231230, by rfl⟩ : syracuseStep 1233229 = 462461) (by norm_num)
theorem B1298785 : Blo 1152637 1298785 := bbase (se 2 (by rfl) ⟨487044, by rfl⟩ : syracuseStep 1298785 = 974089) (by norm_num)
theorem B4378981 : Blo 1152637 4378981 := bbase (se 4 (by rfl) ⟨410529, by rfl⟩ : syracuseStep 4378981 = 821059) (by norm_num)
theorem B1462637 : Blo 1152637 1462637 := bbase (se 3 (by rfl) ⟨274244, by rfl⟩ : syracuseStep 1462637 = 548489) (by norm_num)
theorem B1298821 : Blo 1152637 1298821 := bbase (se 4 (by rfl) ⟨121764, by rfl⟩ : syracuseStep 1298821 = 243529) (by norm_num)
theorem B1462693 : Blo 1152637 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B1298857 : Blo 1152637 1298857 := bbase (se 2 (by rfl) ⟨487071, by rfl⟩ : syracuseStep 1298857 = 974143) (by norm_num)
theorem B1298893 : Blo 1152637 1298893 := bbase (se 3 (by rfl) ⟨243542, by rfl⟩ : syracuseStep 1298893 = 487085) (by norm_num)
theorem B1298929 : Blo 1152637 1298929 := bbase (se 2 (by rfl) ⟨487098, by rfl⟩ : syracuseStep 1298929 = 974197) (by norm_num)
theorem B1462789 : Blo 1152637 1462789 := bbase (se 4 (by rfl) ⟨137136, by rfl⟩ : syracuseStep 1462789 = 274273) (by norm_num)
theorem B1298965 : Blo 1152637 1298965 := bbase (se 6 (by rfl) ⟨30444, by rfl⟩ : syracuseStep 1298965 = 60889) (by norm_num)
theorem B1299001 : Blo 1152637 1299001 := bbase (se 2 (by rfl) ⟨487125, by rfl⟩ : syracuseStep 1299001 = 974251) (by norm_num)
theorem B1299037 : Blo 1152637 1299037 := bbase (se 3 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 1299037 = 487139) (by norm_num)
theorem B1299073 : Blo 1152637 1299073 := bbase (se 2 (by rfl) ⟨487152, by rfl⟩ : syracuseStep 1299073 = 974305) (by norm_num)
theorem B4379285 : Blo 1152637 4379285 := bbase (se 6 (by rfl) ⟨102639, by rfl⟩ : syracuseStep 4379285 = 205279) (by norm_num)
theorem B1299109 : Blo 1152637 1299109 := bbase (se 4 (by rfl) ⟨121791, by rfl⟩ : syracuseStep 1299109 = 243583) (by norm_num)
theorem B1462961 : Blo 1152637 1462961 := bbase (se 2 (by rfl) ⟨548610, by rfl⟩ : syracuseStep 1462961 = 1097221) (by norm_num)
theorem B1299145 : Blo 1152637 1299145 := bbase (se 2 (by rfl) ⟨487179, by rfl⟩ : syracuseStep 1299145 = 974359) (by norm_num)
theorem B1463017 : Blo 1152637 1463017 := bbase (se 2 (by rfl) ⟨548631, by rfl⟩ : syracuseStep 1463017 = 1097263) (by norm_num)
theorem B1299181 : Blo 1152637 1299181 := bbase (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) (by norm_num)
theorem B1233673 : Blo 1152637 1233673 := bbase (se 2 (by rfl) ⟨462627, by rfl⟩ : syracuseStep 1233673 = 925255) (by norm_num)
theorem B1299217 : Blo 1152637 1299217 := bbase (se 2 (by rfl) ⟨487206, by rfl⟩ : syracuseStep 1299217 = 974413) (by norm_num)
theorem B1299253 : Blo 1152637 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B1463113 : Blo 1152637 1463113 := bbase (se 2 (by rfl) ⟨548667, by rfl⟩ : syracuseStep 1463113 = 1097335) (by norm_num)
theorem B1299289 : Blo 1152637 1299289 := bbase (se 2 (by rfl) ⟨487233, by rfl⟩ : syracuseStep 1299289 = 974467) (by norm_num)
theorem B1299325 : Blo 1152637 1299325 := bbase (se 3 (by rfl) ⟨243623, by rfl⟩ : syracuseStep 1299325 = 487247) (by norm_num)
theorem B1233793 : Blo 1152637 1233793 := bbase (se 2 (by rfl) ⟨462672, by rfl⟩ : syracuseStep 1233793 = 925345) (by norm_num)
theorem B13161365 : Blo 1152637 13161365 := bbase (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) (by norm_num)
theorem B1299361 : Blo 1152637 1299361 := bbase (se 2 (by rfl) ⟨487260, by rfl⟩ : syracuseStep 1299361 = 974521) (by norm_num)
theorem B1299397 : Blo 1152637 1299397 := bbase (se 4 (by rfl) ⟨121818, by rfl⟩ : syracuseStep 1299397 = 243637) (by norm_num)
theorem B1299433 : Blo 1152637 1299433 := bbase (se 2 (by rfl) ⟨487287, by rfl⟩ : syracuseStep 1299433 = 974575) (by norm_num)
theorem B2773997 : Blo 1152637 2773997 := bbase (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) (by norm_num)
theorem B1463285 : Blo 1152637 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B1299469 : Blo 1152637 1299469 := bbase (se 3 (by rfl) ⟨243650, by rfl⟩ : syracuseStep 1299469 = 487301) (by norm_num)
theorem B1463341 : Blo 1152637 1463341 := bbase (se 3 (by rfl) ⟨274376, by rfl⟩ : syracuseStep 1463341 = 548753) (by norm_num)
theorem B1299505 : Blo 1152637 1299505 := bbase (se 2 (by rfl) ⟨487314, by rfl⟩ : syracuseStep 1299505 = 974629) (by norm_num)
theorem B21353557 : Blo 1152637 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B1299541 : Blo 1152637 1299541 := bbase (se 8 (by rfl) ⟨7614, by rfl⟩ : syracuseStep 1299541 = 15229) (by norm_num)
theorem B1299577 : Blo 1152637 1299577 := bbase (se 2 (by rfl) ⟨487341, by rfl⟩ : syracuseStep 1299577 = 974683) (by norm_num)
theorem B1234045 : Blo 1152637 1234045 := bbase (se 3 (by rfl) ⟨231383, by rfl⟩ : syracuseStep 1234045 = 462767) (by norm_num)
theorem B1234049 : Blo 1152637 1234049 := bbase (se 2 (by rfl) ⟨462768, by rfl⟩ : syracuseStep 1234049 = 925537) (by norm_num)
theorem B1463437 : Blo 1152637 1463437 := bbase (se 3 (by rfl) ⟨274394, by rfl⟩ : syracuseStep 1463437 = 548789) (by norm_num)
theorem B4052117 : Blo 1152637 4052117 := bbase (se 6 (by rfl) ⟨94971, by rfl⟩ : syracuseStep 4052117 = 189943) (by norm_num)
theorem B7394453 : Blo 1152637 7394453 := bbase (se 6 (by rfl) ⟨173307, by rfl⟩ : syracuseStep 7394453 = 346615) (by norm_num)
theorem B1299613 : Blo 1152637 1299613 := bbase (se 3 (by rfl) ⟨243677, by rfl⟩ : syracuseStep 1299613 = 487355) (by norm_num)
theorem B2774189 : Blo 1152637 2774189 := bbase (se 3 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 2774189 = 1040321) (by norm_num)
theorem B1299649 : Blo 1152637 1299649 := bbase (se 2 (by rfl) ⟨487368, by rfl⟩ : syracuseStep 1299649 = 974737) (by norm_num)
theorem B1299685 : Blo 1152637 1299685 := bbase (se 4 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 1299685 = 243691) (by norm_num)
theorem B1758437 : Blo 1152637 1758437 := bbase (se 4 (by rfl) ⟨164853, by rfl⟩ : syracuseStep 1758437 = 329707) (by norm_num)
theorem B4936949 : Blo 1152637 4936949 := bbase (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) (by norm_num)
theorem B1299721 : Blo 1152637 1299721 := bbase (se 2 (by rfl) ⟨487395, by rfl⟩ : syracuseStep 1299721 = 974791) (by norm_num)
theorem B1299757 : Blo 1152637 1299757 := bbase (se 3 (by rfl) ⟨243704, by rfl⟩ : syracuseStep 1299757 = 487409) (by norm_num)
theorem B5854517 : Blo 1152637 5854517 := bbase (se 5 (by rfl) ⟨274430, by rfl⟩ : syracuseStep 5854517 = 548861) (by norm_num)
theorem B1463609 : Blo 1152637 1463609 := bbase (se 2 (by rfl) ⟨548853, by rfl⟩ : syracuseStep 1463609 = 1097707) (by norm_num)
theorem B1299793 : Blo 1152637 1299793 := bbase (se 2 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 1299793 = 974845) (by norm_num)
theorem B1463665 : Blo 1152637 1463665 := bbase (se 2 (by rfl) ⟨548874, by rfl⟩ : syracuseStep 1463665 = 1097749) (by norm_num)
theorem B1299829 : Blo 1152637 1299829 := bbase (se 5 (by rfl) ⟨60929, by rfl⟩ : syracuseStep 1299829 = 121859) (by norm_num)
theorem B1561973 : Blo 1152637 1561973 := bbase (se 5 (by rfl) ⟨73217, by rfl⟩ : syracuseStep 1561973 = 146435) (by norm_num)
theorem B1299865 : Blo 1152637 1299865 := bbase (se 2 (by rfl) ⟨487449, by rfl⟩ : syracuseStep 1299865 = 974899) (by norm_num)
theorem B1299901 : Blo 1152637 1299901 := bbase (se 3 (by rfl) ⟨243731, by rfl⟩ : syracuseStep 1299901 = 487463) (by norm_num)
theorem B2807245 : Blo 1152637 2807245 := bbase (se 3 (by rfl) ⟨526358, by rfl⟩ : syracuseStep 2807245 = 1052717) (by norm_num)
theorem B1168849 : Blo 1152637 1168849 := bbase (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) (by norm_num)
theorem B1463761 : Blo 1152637 1463761 := bbase (se 2 (by rfl) ⟨548910, by rfl⟩ : syracuseStep 1463761 = 1097821) (by norm_num)
theorem B1299937 : Blo 1152637 1299937 := bbase (se 2 (by rfl) ⟨487476, by rfl⟩ : syracuseStep 1299937 = 974953) (by norm_num)
theorem B1299973 : Blo 1152637 1299973 := bbase (se 4 (by rfl) ⟨121872, by rfl⟩ : syracuseStep 1299973 = 243745) (by norm_num)
theorem B1300009 : Blo 1152637 1300009 := bbase (se 2 (by rfl) ⟨487503, by rfl⟩ : syracuseStep 1300009 = 975007) (by norm_num)
theorem B1300045 : Blo 1152637 1300045 := bbase (se 3 (by rfl) ⟨243758, by rfl⟩ : syracuseStep 1300045 = 487517) (by norm_num)
theorem B4806245 : Blo 1152637 4806245 := bbase (se 4 (by rfl) ⟨450585, by rfl⟩ : syracuseStep 4806245 = 901171) (by norm_num)
theorem B2807405 : Blo 1152637 2807405 := bbase (se 3 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 2807405 = 1052777) (by norm_num)
theorem B1300081 : Blo 1152637 1300081 := bbase (se 2 (by rfl) ⟨487530, by rfl⟩ : syracuseStep 1300081 = 975061) (by norm_num)
theorem B1300117 : Blo 1152637 1300117 := bbase (se 6 (by rfl) ⟨30471, by rfl⟩ : syracuseStep 1300117 = 60943) (by norm_num)
theorem B1234613 : Blo 1152637 1234613 := bbase (se 5 (by rfl) ⟨57872, by rfl⟩ : syracuseStep 1234613 = 115745) (by norm_num)
theorem B1300153 : Blo 1152637 1300153 := bbase (se 2 (by rfl) ⟨487557, by rfl⟩ : syracuseStep 1300153 = 975115) (by norm_num)
theorem B1300189 : Blo 1152637 1300189 := bbase (se 3 (by rfl) ⟨243785, by rfl⟩ : syracuseStep 1300189 = 487571) (by norm_num)
theorem B1300225 : Blo 1152637 1300225 := bbase (se 2 (by rfl) ⟨487584, by rfl⟩ : syracuseStep 1300225 = 975169) (by norm_num)
theorem B1300261 : Blo 1152637 1300261 := bbase (se 4 (by rfl) ⟨121899, by rfl⟩ : syracuseStep 1300261 = 243799) (by norm_num)
theorem B1300297 : Blo 1152637 1300297 := bbase (se 2 (by rfl) ⟨487611, by rfl⟩ : syracuseStep 1300297 = 975223) (by norm_num)
theorem B1300333 : Blo 1152637 1300333 := bbase (se 3 (by rfl) ⟨243812, by rfl⟩ : syracuseStep 1300333 = 487625) (by norm_num)
theorem B1234801 : Blo 1152637 1234801 := bbase (se 2 (by rfl) ⟨463050, by rfl⟩ : syracuseStep 1234801 = 926101) (by norm_num)
theorem B4675445 : Blo 1152637 4675445 := bbase (se 5 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 4675445 = 438323) (by norm_num)
theorem B1300369 : Blo 1152637 1300369 := bbase (se 2 (by rfl) ⟨487638, by rfl⟩ : syracuseStep 1300369 = 975277) (by norm_num)
theorem B1300405 : Blo 1152637 1300405 := bbase (se 5 (by rfl) ⟨60956, by rfl⟩ : syracuseStep 1300405 = 121913) (by norm_num)
theorem B1300441 : Blo 1152637 1300441 := bbase (se 2 (by rfl) ⟨487665, by rfl⟩ : syracuseStep 1300441 = 975331) (by norm_num)
theorem B1300477 : Blo 1152637 1300477 := bbase (se 3 (by rfl) ⟨243839, by rfl⟩ : syracuseStep 1300477 = 487679) (by norm_num)
theorem B1300513 : Blo 1152637 1300513 := bbase (se 2 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 1300513 = 975385) (by norm_num)
theorem B1300549 : Blo 1152637 1300549 := bbase (se 4 (by rfl) ⟨121926, by rfl⟩ : syracuseStep 1300549 = 243853) (by norm_num)
theorem B1300585 : Blo 1152637 1300585 := bbase (se 2 (by rfl) ⟨487719, by rfl⟩ : syracuseStep 1300585 = 975439) (by norm_num)
theorem B1300621 : Blo 1152637 1300621 := bbase (se 3 (by rfl) ⟨243866, by rfl⟩ : syracuseStep 1300621 = 487733) (by norm_num)
theorem B1300657 : Blo 1152637 1300657 := bbase (se 2 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 1300657 = 975493) (by norm_num)
theorem B1300693 : Blo 1152637 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B1300729 : Blo 1152637 1300729 := bbase (se 2 (by rfl) ⟨487773, by rfl⟩ : syracuseStep 1300729 = 975547) (by norm_num)
theorem B1300765 : Blo 1152637 1300765 := bbase (se 3 (by rfl) ⟨243893, by rfl⟩ : syracuseStep 1300765 = 487787) (by norm_num)
theorem B1300801 : Blo 1152637 1300801 := bbase (se 2 (by rfl) ⟨487800, by rfl⟩ : syracuseStep 1300801 = 975601) (by norm_num)
theorem B1300837 : Blo 1152637 1300837 := bbase (se 4 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 1300837 = 243907) (by norm_num)
theorem B1300873 : Blo 1152637 1300873 := bbase (se 2 (by rfl) ⟨487827, by rfl⟩ : syracuseStep 1300873 = 975655) (by norm_num)
theorem B1300909 : Blo 1152637 1300909 := bbase (se 3 (by rfl) ⟨243920, by rfl⟩ : syracuseStep 1300909 = 487841) (by norm_num)
theorem B1300945 : Blo 1152637 1300945 := bbase (se 2 (by rfl) ⟨487854, by rfl⟩ : syracuseStep 1300945 = 975709) (by norm_num)
theorem B1300981 : Blo 1152637 1300981 := bbase (se 5 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 1300981 = 121967) (by norm_num)
theorem B1301017 : Blo 1152637 1301017 := bbase (se 2 (by rfl) ⟨487881, by rfl⟩ : syracuseStep 1301017 = 975763) (by norm_num)
theorem B1301053 : Blo 1152637 1301053 := bbase (se 3 (by rfl) ⟨243947, by rfl⟩ : syracuseStep 1301053 = 487895) (by norm_num)
theorem B1301089 : Blo 1152637 1301089 := bbase (se 2 (by rfl) ⟨487908, by rfl⟩ : syracuseStep 1301089 = 975817) (by norm_num)
theorem B1301125 : Blo 1152637 1301125 := bbase (se 4 (by rfl) ⟨121980, by rfl⟩ : syracuseStep 1301125 = 243961) (by norm_num)
theorem B1301161 : Blo 1152637 1301161 := bbase (se 2 (by rfl) ⟨487935, by rfl⟩ : syracuseStep 1301161 = 975871) (by norm_num)
theorem B1301197 : Blo 1152637 1301197 := bbase (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) (by norm_num)
theorem B4381397 : Blo 1152637 4381397 := bbase (se 7 (by rfl) ⟨51344, by rfl⟩ : syracuseStep 4381397 = 102689) (by norm_num)
theorem B4938725 : Blo 1152637 4938725 := bbase (se 4 (by rfl) ⟨463005, by rfl⟩ : syracuseStep 4938725 = 926011) (by norm_num)
theorem B4381685 : Blo 1152637 4381685 := bbase (se 5 (by rfl) ⟨205391, by rfl⟩ : syracuseStep 4381685 = 410783) (by norm_num)
theorem B3890213 : Blo 1152637 3890213 := bbase (se 4 (by rfl) ⟨364707, by rfl⟩ : syracuseStep 3890213 = 729415) (by norm_num)
theorem B1170569 : Blo 1152637 1170569 := bbase (se 2 (by rfl) ⟨438963, by rfl⟩ : syracuseStep 1170569 = 877927) (by norm_num)
theorem B4938965 : Blo 1152637 4938965 := bbase (se 7 (by rfl) ⟨57878, by rfl⟩ : syracuseStep 4938965 = 115757) (by norm_num)
theorem B4676837 : Blo 1152637 4676837 := bbase (se 4 (by rfl) ⟨438453, by rfl⟩ : syracuseStep 4676837 = 876907) (by norm_num)
theorem B7888117 : Blo 1152637 7888117 := bbase (se 5 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 7888117 = 739511) (by norm_num)
theorem B2776477 : Blo 1152637 2776477 := bbase (se 3 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 2776477 = 1041179) (by norm_num)
theorem B3890645 : Blo 1152637 3890645 := bbase (se 7 (by rfl) ⟨45593, by rfl⟩ : syracuseStep 3890645 = 91187) (by norm_num)
theorem B1170925 : Blo 1152637 1170925 := bbase (se 3 (by rfl) ⟨219548, by rfl⟩ : syracuseStep 1170925 = 439097) (by norm_num)
theorem B5004965 : Blo 1152637 5004965 := bbase (se 4 (by rfl) ⟨469215, by rfl⟩ : syracuseStep 5004965 = 938431) (by norm_num)
theorem B3891077 : Blo 1152637 3891077 := bbase (se 4 (by rfl) ⟨364788, by rfl⟩ : syracuseStep 3891077 = 729577) (by norm_num)
theorem B2777141 : Blo 1152637 2777141 := bbase (se 5 (by rfl) ⟨130178, by rfl⟩ : syracuseStep 2777141 = 260357) (by norm_num)
theorem B1171513 : Blo 1152637 1171513 := bbase (se 2 (by rfl) ⟨439317, by rfl⟩ : syracuseStep 1171513 = 878635) (by norm_num)
theorem B4382869 : Blo 1152637 4382869 := bbase (se 6 (by rfl) ⟨102723, by rfl⟩ : syracuseStep 4382869 = 205447) (by norm_num)
theorem B3891509 : Blo 1152637 3891509 := bbase (se 5 (by rfl) ⟨182414, by rfl⟩ : syracuseStep 3891509 = 364829) (by norm_num)
theorem B18702677 : Blo 1152637 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B3694997 : Blo 1152637 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B1728965 : Blo 1152637 1728965 := bbase (se 4 (by rfl) ⟨162090, by rfl⟩ : syracuseStep 1728965 = 324181) (by norm_num)
theorem B4383173 : Blo 1152637 4383173 := bbase (se 4 (by rfl) ⟨410922, by rfl⟩ : syracuseStep 4383173 = 821845) (by norm_num)
theorem B1728989 : Blo 1152637 1728989 := bbase (se 3 (by rfl) ⟨324185, by rfl⟩ : syracuseStep 1728989 = 648371) (by norm_num)
theorem B1729013 : Blo 1152637 1729013 := bbase (se 5 (by rfl) ⟨81047, by rfl⟩ : syracuseStep 1729013 = 162095) (by norm_num)
theorem B1729037 : Blo 1152637 1729037 := bbase (se 3 (by rfl) ⟨324194, by rfl⟩ : syracuseStep 1729037 = 648389) (by norm_num)
theorem B1729061 : Blo 1152637 1729061 := bbase (se 4 (by rfl) ⟨162099, by rfl⟩ : syracuseStep 1729061 = 324199) (by norm_num)
theorem B1729085 : Blo 1152637 1729085 := bbase (se 3 (by rfl) ⟨324203, by rfl⟩ : syracuseStep 1729085 = 648407) (by norm_num)
theorem B1729109 : Blo 1152637 1729109 := bbase (se 8 (by rfl) ⟨10131, by rfl⟩ : syracuseStep 1729109 = 20263) (by norm_num)
theorem B1729133 : Blo 1152637 1729133 := bbase (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) (by norm_num)
theorem B1729157 : Blo 1152637 1729157 := bbase (se 4 (by rfl) ⟨162108, by rfl⟩ : syracuseStep 1729157 = 324217) (by norm_num)
theorem B1729181 : Blo 1152637 1729181 := bbase (se 3 (by rfl) ⟨324221, by rfl⟩ : syracuseStep 1729181 = 648443) (by norm_num)
theorem B1729205 : Blo 1152637 1729205 := bbase (se 5 (by rfl) ⟨81056, by rfl⟩ : syracuseStep 1729205 = 162113) (by norm_num)
theorem B1729229 : Blo 1152637 1729229 := bbase (se 3 (by rfl) ⟨324230, by rfl⟩ : syracuseStep 1729229 = 648461) (by norm_num)
theorem B1729253 : Blo 1152637 1729253 := bbase (se 4 (by rfl) ⟨162117, by rfl⟩ : syracuseStep 1729253 = 324235) (by norm_num)
theorem B3891941 : Blo 1152637 3891941 := bbase (se 4 (by rfl) ⟨364869, by rfl⟩ : syracuseStep 3891941 = 729739) (by norm_num)
theorem B1729277 : Blo 1152637 1729277 := bbase (se 3 (by rfl) ⟨324239, by rfl⟩ : syracuseStep 1729277 = 648479) (by norm_num)
theorem B1729301 : Blo 1152637 1729301 := bbase (se 6 (by rfl) ⟨40530, by rfl⟩ : syracuseStep 1729301 = 81061) (by norm_num)
theorem B18735893 : Blo 1152637 18735893 := bbase (se 6 (by rfl) ⟨439122, by rfl⟩ : syracuseStep 18735893 = 878245) (by norm_num)
theorem B1729325 : Blo 1152637 1729325 := bbase (se 3 (by rfl) ⟨324248, by rfl⟩ : syracuseStep 1729325 = 648497) (by norm_num)
theorem B4449077 : Blo 1152637 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B1729349 : Blo 1152637 1729349 := bbase (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) (by norm_num)
theorem B1729373 : Blo 1152637 1729373 := bbase (se 3 (by rfl) ⟨324257, by rfl⟩ : syracuseStep 1729373 = 648515) (by norm_num)
theorem B1729397 : Blo 1152637 1729397 := bbase (se 5 (by rfl) ⟨81065, by rfl⟩ : syracuseStep 1729397 = 162131) (by norm_num)
theorem B1729421 : Blo 1152637 1729421 := bbase (se 3 (by rfl) ⟨324266, by rfl⟩ : syracuseStep 1729421 = 648533) (by norm_num)
theorem B1729445 : Blo 1152637 1729445 := bbase (se 4 (by rfl) ⟨162135, by rfl⟩ : syracuseStep 1729445 = 324271) (by norm_num)
theorem B1729469 : Blo 1152637 1729469 := bbase (se 3 (by rfl) ⟨324275, by rfl⟩ : syracuseStep 1729469 = 648551) (by norm_num)
theorem B1729493 : Blo 1152637 1729493 := bbase (se 7 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 1729493 = 40535) (by norm_num)
theorem B1729517 : Blo 1152637 1729517 := bbase (se 3 (by rfl) ⟨324284, by rfl⟩ : syracuseStep 1729517 = 648569) (by norm_num)
theorem B9855989 : Blo 1152637 9855989 := bbase (se 5 (by rfl) ⟨461999, by rfl⟩ : syracuseStep 9855989 = 923999) (by norm_num)
theorem B1729541 : Blo 1152637 1729541 := bbase (se 4 (by rfl) ⟨162144, by rfl⟩ : syracuseStep 1729541 = 324289) (by norm_num)
theorem B1729565 : Blo 1152637 1729565 := bbase (se 3 (by rfl) ⟨324293, by rfl⟩ : syracuseStep 1729565 = 648587) (by norm_num)
theorem B1729589 : Blo 1152637 1729589 := bbase (se 5 (by rfl) ⟨81074, by rfl⟩ : syracuseStep 1729589 = 162149) (by norm_num)
theorem B1729613 : Blo 1152637 1729613 := bbase (se 3 (by rfl) ⟨324302, by rfl⟩ : syracuseStep 1729613 = 648605) (by norm_num)
theorem B1729637 : Blo 1152637 1729637 := bbase (se 4 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 1729637 = 324307) (by norm_num)
theorem B2188397 : Blo 1152637 2188397 := bbase (se 3 (by rfl) ⟨410324, by rfl⟩ : syracuseStep 2188397 = 820649) (by norm_num)
theorem B1729661 : Blo 1152637 1729661 := bbase (se 3 (by rfl) ⟨324311, by rfl⟩ : syracuseStep 1729661 = 648623) (by norm_num)
theorem B1729685 : Blo 1152637 1729685 := bbase (se 6 (by rfl) ⟨40539, by rfl⟩ : syracuseStep 1729685 = 81079) (by norm_num)
theorem B3892373 : Blo 1152637 3892373 := bbase (se 6 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 3892373 = 182455) (by norm_num)
theorem B8316053 : Blo 1152637 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B1729709 : Blo 1152637 1729709 := bbase (se 3 (by rfl) ⟨324320, by rfl⟩ : syracuseStep 1729709 = 648641) (by norm_num)
theorem B1729733 : Blo 1152637 1729733 := bbase (se 4 (by rfl) ⟨162162, by rfl⟩ : syracuseStep 1729733 = 324325) (by norm_num)
theorem B1729757 : Blo 1152637 1729757 := bbase (se 3 (by rfl) ⟨324329, by rfl⟩ : syracuseStep 1729757 = 648659) (by norm_num)
theorem B1729781 : Blo 1152637 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B2188549 : Blo 1152637 2188549 := bbase (se 4 (by rfl) ⟨205176, by rfl⟩ : syracuseStep 2188549 = 410353) (by norm_num)
theorem B1729805 : Blo 1152637 1729805 := bbase (se 3 (by rfl) ⟨324338, by rfl⟩ : syracuseStep 1729805 = 648677) (by norm_num)
theorem B1729829 : Blo 1152637 1729829 := bbase (se 4 (by rfl) ⟨162171, by rfl⟩ : syracuseStep 1729829 = 324343) (by norm_num)
theorem B1729853 : Blo 1152637 1729853 := bbase (se 3 (by rfl) ⟨324347, by rfl⟩ : syracuseStep 1729853 = 648695) (by norm_num)
theorem B1729877 : Blo 1152637 1729877 := bbase (se 12 (by rfl) ⟨633, by rfl⟩ : syracuseStep 1729877 = 1267) (by norm_num)
theorem B1729901 : Blo 1152637 1729901 := bbase (se 3 (by rfl) ⟨324356, by rfl⟩ : syracuseStep 1729901 = 648713) (by norm_num)
theorem B1729925 : Blo 1152637 1729925 := bbase (se 4 (by rfl) ⟨162180, by rfl⟩ : syracuseStep 1729925 = 324361) (by norm_num)
theorem B1729949 : Blo 1152637 1729949 := bbase (se 3 (by rfl) ⟨324365, by rfl⟩ : syracuseStep 1729949 = 648731) (by norm_num)
theorem B2778533 : Blo 1152637 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B1729973 : Blo 1152637 1729973 := bbase (se 5 (by rfl) ⟨81092, by rfl⟩ : syracuseStep 1729973 = 162185) (by norm_num)
theorem B8316341 : Blo 1152637 8316341 := bbase (se 5 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 8316341 = 779657) (by norm_num)
theorem B1729997 : Blo 1152637 1729997 := bbase (se 3 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 1729997 = 648749) (by norm_num)
theorem B1730021 : Blo 1152637 1730021 := bbase (se 4 (by rfl) ⟨162189, by rfl⟩ : syracuseStep 1730021 = 324379) (by norm_num)
theorem B1730045 : Blo 1152637 1730045 := bbase (se 3 (by rfl) ⟨324383, by rfl⟩ : syracuseStep 1730045 = 648767) (by norm_num)
theorem B2778629 : Blo 1152637 2778629 := bbase (se 4 (by rfl) ⟨260496, by rfl⟩ : syracuseStep 2778629 = 520993) (by norm_num)
theorem B1730069 : Blo 1152637 1730069 := bbase (se 6 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 1730069 = 81097) (by norm_num)
theorem B1730093 : Blo 1152637 1730093 := bbase (se 3 (by rfl) ⟨324392, by rfl⟩ : syracuseStep 1730093 = 648785) (by norm_num)
theorem B2188853 : Blo 1152637 2188853 := bbase (se 5 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 2188853 = 205205) (by norm_num)
theorem B1730117 : Blo 1152637 1730117 := bbase (se 4 (by rfl) ⟨162198, by rfl⟩ : syracuseStep 1730117 = 324397) (by norm_num)
theorem B3892805 : Blo 1152637 3892805 := bbase (se 4 (by rfl) ⟨364950, by rfl⟩ : syracuseStep 3892805 = 729901) (by norm_num)
theorem B1730141 : Blo 1152637 1730141 := bbase (se 3 (by rfl) ⟨324401, by rfl⟩ : syracuseStep 1730141 = 648803) (by norm_num)
theorem B1730165 : Blo 1152637 1730165 := bbase (se 5 (by rfl) ⟨81101, by rfl⟩ : syracuseStep 1730165 = 162203) (by norm_num)
theorem B1730189 : Blo 1152637 1730189 := bbase (se 3 (by rfl) ⟨324410, by rfl⟩ : syracuseStep 1730189 = 648821) (by norm_num)
theorem B1730213 : Blo 1152637 1730213 := bbase (se 4 (by rfl) ⟨162207, by rfl⟩ : syracuseStep 1730213 = 324415) (by norm_num)
theorem B3696293 : Blo 1152637 3696293 := bbase (se 4 (by rfl) ⟨346527, by rfl⟩ : syracuseStep 3696293 = 693055) (by norm_num)
theorem B1730237 : Blo 1152637 1730237 := bbase (se 3 (by rfl) ⟨324419, by rfl⟩ : syracuseStep 1730237 = 648839) (by norm_num)
theorem B1730261 : Blo 1152637 1730261 := bbase (se 7 (by rfl) ⟨20276, by rfl⟩ : syracuseStep 1730261 = 40553) (by norm_num)
theorem B14804693 : Blo 1152637 14804693 := bbase (se 7 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 14804693 = 346985) (by norm_num)
theorem B1730285 : Blo 1152637 1730285 := bbase (se 3 (by rfl) ⟨324428, by rfl⟩ : syracuseStep 1730285 = 648857) (by norm_num)
theorem B1730309 : Blo 1152637 1730309 := bbase (se 4 (by rfl) ⟨162216, by rfl⟩ : syracuseStep 1730309 = 324433) (by norm_num)
theorem B1730333 : Blo 1152637 1730333 := bbase (se 3 (by rfl) ⟨324437, by rfl⟩ : syracuseStep 1730333 = 648875) (by norm_num)
theorem B1730357 : Blo 1152637 1730357 := bbase (se 5 (by rfl) ⟨81110, by rfl⟩ : syracuseStep 1730357 = 162221) (by norm_num)
theorem B1730381 : Blo 1152637 1730381 := bbase (se 3 (by rfl) ⟨324446, by rfl⟩ : syracuseStep 1730381 = 648893) (by norm_num)
theorem B1730405 : Blo 1152637 1730405 := bbase (se 4 (by rfl) ⟨162225, by rfl⟩ : syracuseStep 1730405 = 324451) (by norm_num)
theorem B1730429 : Blo 1152637 1730429 := bbase (se 3 (by rfl) ⟨324455, by rfl⟩ : syracuseStep 1730429 = 648911) (by norm_num)
theorem B1730453 : Blo 1152637 1730453 := bbase (se 6 (by rfl) ⟨40557, by rfl⟩ : syracuseStep 1730453 = 81115) (by norm_num)
theorem B1730477 : Blo 1152637 1730477 := bbase (se 3 (by rfl) ⟨324464, by rfl⟩ : syracuseStep 1730477 = 648929) (by norm_num)
theorem B1730501 : Blo 1152637 1730501 := bbase (se 4 (by rfl) ⟨162234, by rfl⟩ : syracuseStep 1730501 = 324469) (by norm_num)
theorem B1730525 : Blo 1152637 1730525 := bbase (se 3 (by rfl) ⟨324473, by rfl⟩ : syracuseStep 1730525 = 648947) (by norm_num)
theorem B3893237 : Blo 1152637 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B1730549 : Blo 1152637 1730549 := bbase (se 5 (by rfl) ⟨81119, by rfl⟩ : syracuseStep 1730549 = 162239) (by norm_num)
theorem B8316917 : Blo 1152637 8316917 := bbase (se 5 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 8316917 = 779711) (by norm_num)
theorem B1730573 : Blo 1152637 1730573 := bbase (se 3 (by rfl) ⟨324482, by rfl⟩ : syracuseStep 1730573 = 648965) (by norm_num)
theorem B4057109 : Blo 1152637 4057109 := bbase (se 6 (by rfl) ⟨95088, by rfl⟩ : syracuseStep 4057109 = 190177) (by norm_num)
theorem B8775701 : Blo 1152637 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B6252565 : Blo 1152637 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B1730597 : Blo 1152637 1730597 := bbase (se 4 (by rfl) ⟨162243, by rfl⟩ : syracuseStep 1730597 = 324487) (by norm_num)
theorem B1730621 : Blo 1152637 1730621 := bbase (se 3 (by rfl) ⟨324491, by rfl⟩ : syracuseStep 1730621 = 648983) (by norm_num)
theorem B4155461 : Blo 1152637 4155461 := bbase (se 4 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 4155461 = 779149) (by norm_num)
theorem B1730645 : Blo 1152637 1730645 := bbase (se 8 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 1730645 = 20281) (by norm_num)
theorem B1730669 : Blo 1152637 1730669 := bbase (se 3 (by rfl) ⟨324500, by rfl⟩ : syracuseStep 1730669 = 649001) (by norm_num)
theorem B1730693 : Blo 1152637 1730693 := bbase (se 4 (by rfl) ⟨162252, by rfl⟩ : syracuseStep 1730693 = 324505) (by norm_num)
theorem B1730717 : Blo 1152637 1730717 := bbase (se 3 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 1730717 = 649019) (by norm_num)
theorem B1730741 : Blo 1152637 1730741 := bbase (se 5 (by rfl) ⟨81128, by rfl⟩ : syracuseStep 1730741 = 162257) (by norm_num)
theorem B1730765 : Blo 1152637 1730765 := bbase (se 3 (by rfl) ⟨324518, by rfl⟩ : syracuseStep 1730765 = 649037) (by norm_num)
theorem B1730789 : Blo 1152637 1730789 := bbase (se 4 (by rfl) ⟨162261, by rfl⟩ : syracuseStep 1730789 = 324523) (by norm_num)
theorem B1730813 : Blo 1152637 1730813 := bbase (se 3 (by rfl) ⟨324527, by rfl⟩ : syracuseStep 1730813 = 649055) (by norm_num)
theorem B5335301 : Blo 1152637 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B1730837 : Blo 1152637 1730837 := bbase (se 6 (by rfl) ⟨40566, by rfl⟩ : syracuseStep 1730837 = 81133) (by norm_num)
theorem B2189605 : Blo 1152637 2189605 := bbase (se 4 (by rfl) ⟨205275, by rfl⟩ : syracuseStep 2189605 = 410551) (by norm_num)
theorem B1730861 : Blo 1152637 1730861 := bbase (se 3 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 1730861 = 649073) (by norm_num)
theorem B1730885 : Blo 1152637 1730885 := bbase (se 4 (by rfl) ⟨162270, by rfl⟩ : syracuseStep 1730885 = 324541) (by norm_num)
theorem B1730909 : Blo 1152637 1730909 := bbase (se 3 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 1730909 = 649091) (by norm_num)
theorem B4155749 : Blo 1152637 4155749 := bbase (se 4 (by rfl) ⟨389601, by rfl⟩ : syracuseStep 4155749 = 779203) (by norm_num)
theorem B1730933 : Blo 1152637 1730933 := bbase (se 5 (by rfl) ⟨81137, by rfl⟩ : syracuseStep 1730933 = 162275) (by norm_num)
theorem B1730957 : Blo 1152637 1730957 := bbase (se 3 (by rfl) ⟨324554, by rfl⟩ : syracuseStep 1730957 = 649109) (by norm_num)
theorem B3893669 : Blo 1152637 3893669 := bbase (se 4 (by rfl) ⟨365031, by rfl⟩ : syracuseStep 3893669 = 730063) (by norm_num)
theorem B1730981 : Blo 1152637 1730981 := bbase (se 4 (by rfl) ⟨162279, by rfl⟩ : syracuseStep 1730981 = 324559) (by norm_num)
theorem B2189749 : Blo 1152637 2189749 := bbase (se 5 (by rfl) ⟨102644, by rfl⟩ : syracuseStep 2189749 = 205289) (by norm_num)
theorem B1731005 : Blo 1152637 1731005 := bbase (se 3 (by rfl) ⟨324563, by rfl⟩ : syracuseStep 1731005 = 649127) (by norm_num)
theorem B1731029 : Blo 1152637 1731029 := bbase (se 7 (by rfl) ⟨20285, by rfl⟩ : syracuseStep 1731029 = 40571) (by norm_num)
theorem B1731053 : Blo 1152637 1731053 := bbase (se 3 (by rfl) ⟨324572, by rfl⟩ : syracuseStep 1731053 = 649145) (by norm_num)
theorem B1731077 : Blo 1152637 1731077 := bbase (se 4 (by rfl) ⟨162288, by rfl⟩ : syracuseStep 1731077 = 324577) (by norm_num)
theorem B4385285 : Blo 1152637 4385285 := bbase (se 4 (by rfl) ⟨411120, by rfl⟩ : syracuseStep 4385285 = 822241) (by norm_num)
theorem B2812429 : Blo 1152637 2812429 := bbase (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) (by norm_num)
theorem B1731101 : Blo 1152637 1731101 := bbase (se 3 (by rfl) ⟨324581, by rfl⟩ : syracuseStep 1731101 = 649163) (by norm_num)
theorem B1731125 : Blo 1152637 1731125 := bbase (se 5 (by rfl) ⟨81146, by rfl⟩ : syracuseStep 1731125 = 162293) (by norm_num)
theorem B1731149 : Blo 1152637 1731149 := bbase (se 3 (by rfl) ⟨324590, by rfl⟩ : syracuseStep 1731149 = 649181) (by norm_num)
theorem B2189909 : Blo 1152637 2189909 := bbase (se 8 (by rfl) ⟨12831, by rfl⟩ : syracuseStep 2189909 = 25663) (by norm_num)
theorem B1731173 : Blo 1152637 1731173 := bbase (se 4 (by rfl) ⟨162297, by rfl⟩ : syracuseStep 1731173 = 324595) (by norm_num)
theorem B1731197 : Blo 1152637 1731197 := bbase (se 3 (by rfl) ⟨324599, by rfl⟩ : syracuseStep 1731197 = 649199) (by norm_num)
theorem B1731221 : Blo 1152637 1731221 := bbase (se 6 (by rfl) ⟨40575, by rfl⟩ : syracuseStep 1731221 = 81151) (by norm_num)
theorem B1731245 : Blo 1152637 1731245 := bbase (se 3 (by rfl) ⟨324608, by rfl⟩ : syracuseStep 1731245 = 649217) (by norm_num)
theorem B1731269 : Blo 1152637 1731269 := bbase (se 4 (by rfl) ⟨162306, by rfl⟩ : syracuseStep 1731269 = 324613) (by norm_num)
theorem B1731293 : Blo 1152637 1731293 := bbase (se 3 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 1731293 = 649235) (by norm_num)
theorem B2190053 : Blo 1152637 2190053 := bbase (se 4 (by rfl) ⟨205317, by rfl⟩ : syracuseStep 2190053 = 410635) (by norm_num)
theorem B1731317 : Blo 1152637 1731317 := bbase (se 5 (by rfl) ⟨81155, by rfl⟩ : syracuseStep 1731317 = 162311) (by norm_num)
theorem B1731341 : Blo 1152637 1731341 := bbase (se 3 (by rfl) ⟨324626, by rfl⟩ : syracuseStep 1731341 = 649253) (by norm_num)
theorem B1501969 : Blo 1152637 1501969 := bbase (se 2 (by rfl) ⟨563238, by rfl⟩ : syracuseStep 1501969 = 1126477) (by norm_num)
theorem B4156181 : Blo 1152637 4156181 := bbase (se 6 (by rfl) ⟨97410, by rfl⟩ : syracuseStep 4156181 = 194821) (by norm_num)
theorem B1731365 : Blo 1152637 1731365 := bbase (se 4 (by rfl) ⟨162315, by rfl⟩ : syracuseStep 1731365 = 324631) (by norm_num)
theorem B4385573 : Blo 1152637 4385573 := bbase (se 4 (by rfl) ⟨411147, by rfl⟩ : syracuseStep 4385573 = 822295) (by norm_num)
theorem B1731389 : Blo 1152637 1731389 := bbase (se 3 (by rfl) ⟨324635, by rfl⟩ : syracuseStep 1731389 = 649271) (by norm_num)
theorem B3894101 : Blo 1152637 3894101 := bbase (se 9 (by rfl) ⟨11408, by rfl⟩ : syracuseStep 3894101 = 22817) (by norm_num)
theorem B1731413 : Blo 1152637 1731413 := bbase (se 9 (by rfl) ⟨5072, by rfl⟩ : syracuseStep 1731413 = 10145) (by norm_num)
theorem B1731437 : Blo 1152637 1731437 := bbase (se 3 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 1731437 = 649289) (by norm_num)
theorem B1731461 : Blo 1152637 1731461 := bbase (se 4 (by rfl) ⟨162324, by rfl⟩ : syracuseStep 1731461 = 324649) (by norm_num)
theorem B1731485 : Blo 1152637 1731485 := bbase (se 3 (by rfl) ⟨324653, by rfl⟩ : syracuseStep 1731485 = 649307) (by norm_num)
theorem B1731509 : Blo 1152637 1731509 := bbase (se 5 (by rfl) ⟨81164, by rfl⟩ : syracuseStep 1731509 = 162329) (by norm_num)
theorem B1731533 : Blo 1152637 1731533 := bbase (se 3 (by rfl) ⟨324662, by rfl⟩ : syracuseStep 1731533 = 649325) (by norm_num)
theorem B1731557 : Blo 1152637 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B1731581 : Blo 1152637 1731581 := bbase (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) (by norm_num)
theorem B2190341 : Blo 1152637 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B1731605 : Blo 1152637 1731605 := bbase (se 6 (by rfl) ⟨40584, by rfl⟩ : syracuseStep 1731605 = 81169) (by norm_num)
theorem B1731629 : Blo 1152637 1731629 := bbase (se 3 (by rfl) ⟨324680, by rfl⟩ : syracuseStep 1731629 = 649361) (by norm_num)
theorem B1731653 : Blo 1152637 1731653 := bbase (se 4 (by rfl) ⟨162342, by rfl⟩ : syracuseStep 1731653 = 324685) (by norm_num)
theorem B1731677 : Blo 1152637 1731677 := bbase (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) (by norm_num)
theorem B1731701 : Blo 1152637 1731701 := bbase (se 5 (by rfl) ⟨81173, by rfl⟩ : syracuseStep 1731701 = 162347) (by norm_num)
theorem B1731725 : Blo 1152637 1731725 := bbase (se 3 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 1731725 = 649397) (by norm_num)
theorem B2190493 : Blo 1152637 2190493 := bbase (se 3 (by rfl) ⟨410717, by rfl⟩ : syracuseStep 2190493 = 821435) (by norm_num)
theorem B1731749 : Blo 1152637 1731749 := bbase (se 4 (by rfl) ⟨162351, by rfl⟩ : syracuseStep 1731749 = 324703) (by norm_num)
theorem B1731773 : Blo 1152637 1731773 := bbase (se 3 (by rfl) ⟨324707, by rfl⟩ : syracuseStep 1731773 = 649415) (by norm_num)
theorem B1731797 : Blo 1152637 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B1731821 : Blo 1152637 1731821 := bbase (se 3 (by rfl) ⟨324716, by rfl⟩ : syracuseStep 1731821 = 649433) (by norm_num)
theorem B3894533 : Blo 1152637 3894533 := bbase (se 4 (by rfl) ⟨365112, by rfl⟩ : syracuseStep 3894533 = 730225) (by norm_num)
theorem B1731845 : Blo 1152637 1731845 := bbase (se 4 (by rfl) ⟨162360, by rfl⟩ : syracuseStep 1731845 = 324721) (by norm_num)
theorem B1731869 : Blo 1152637 1731869 := bbase (se 3 (by rfl) ⟨324725, by rfl⟩ : syracuseStep 1731869 = 649451) (by norm_num)
theorem B1731893 : Blo 1152637 1731893 := bbase (se 5 (by rfl) ⟨81182, by rfl⟩ : syracuseStep 1731893 = 162365) (by norm_num)
theorem B1731917 : Blo 1152637 1731917 := bbase (se 3 (by rfl) ⟨324734, by rfl⟩ : syracuseStep 1731917 = 649469) (by norm_num)
theorem B2223445 : Blo 1152637 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B1731941 : Blo 1152637 1731941 := bbase (se 4 (by rfl) ⟨162369, by rfl⟩ : syracuseStep 1731941 = 324739) (by norm_num)
theorem B1731965 : Blo 1152637 1731965 := bbase (se 3 (by rfl) ⟨324743, by rfl⟩ : syracuseStep 1731965 = 649487) (by norm_num)
theorem B1731989 : Blo 1152637 1731989 := bbase (se 6 (by rfl) ⟨40593, by rfl⟩ : syracuseStep 1731989 = 81187) (by norm_num)
theorem B5270933 : Blo 1152637 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B1732013 : Blo 1152637 1732013 := bbase (se 3 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 1732013 = 649505) (by norm_num)
theorem B1732037 : Blo 1152637 1732037 := bbase (se 4 (by rfl) ⟨162378, by rfl⟩ : syracuseStep 1732037 = 324757) (by norm_num)
theorem B2190797 : Blo 1152637 2190797 := bbase (se 3 (by rfl) ⟨410774, by rfl⟩ : syracuseStep 2190797 = 821549) (by norm_num)
theorem B1732061 : Blo 1152637 1732061 := bbase (se 3 (by rfl) ⟨324761, by rfl⟩ : syracuseStep 1732061 = 649523) (by norm_num)
theorem B3698149 : Blo 1152637 3698149 := bbase (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) (by norm_num)
theorem B1732085 : Blo 1152637 1732085 := bbase (se 5 (by rfl) ⟨81191, by rfl⟩ : syracuseStep 1732085 = 162383) (by norm_num)
theorem B1732109 : Blo 1152637 1732109 := bbase (se 3 (by rfl) ⟨324770, by rfl⟩ : syracuseStep 1732109 = 649541) (by norm_num)
theorem B1732133 : Blo 1152637 1732133 := bbase (se 4 (by rfl) ⟨162387, by rfl⟩ : syracuseStep 1732133 = 324775) (by norm_num)
theorem B1732157 : Blo 1152637 1732157 := bbase (se 3 (by rfl) ⟨324779, by rfl⟩ : syracuseStep 1732157 = 649559) (by norm_num)
theorem B1732181 : Blo 1152637 1732181 := bbase (se 8 (by rfl) ⟨10149, by rfl⟩ : syracuseStep 1732181 = 20299) (by norm_num)
theorem B1732205 : Blo 1152637 1732205 := bbase (se 3 (by rfl) ⟨324788, by rfl⟩ : syracuseStep 1732205 = 649577) (by norm_num)
theorem B1732229 : Blo 1152637 1732229 := bbase (se 4 (by rfl) ⟨162396, by rfl⟩ : syracuseStep 1732229 = 324793) (by norm_num)
theorem B1732253 : Blo 1152637 1732253 := bbase (se 3 (by rfl) ⟨324797, by rfl⟩ : syracuseStep 1732253 = 649595) (by norm_num)
theorem B3894965 : Blo 1152637 3894965 := bbase (se 5 (by rfl) ⟨182576, by rfl⟩ : syracuseStep 3894965 = 365153) (by norm_num)
theorem B1732277 : Blo 1152637 1732277 := bbase (se 5 (by rfl) ⟨81200, by rfl⟩ : syracuseStep 1732277 = 162401) (by norm_num)
theorem B1732301 : Blo 1152637 1732301 := bbase (se 3 (by rfl) ⟨324806, by rfl⟩ : syracuseStep 1732301 = 649613) (by norm_num)
theorem B1732325 : Blo 1152637 1732325 := bbase (se 4 (by rfl) ⟨162405, by rfl⟩ : syracuseStep 1732325 = 324811) (by norm_num)
theorem B6582005 : Blo 1152637 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B1732349 : Blo 1152637 1732349 := bbase (se 3 (by rfl) ⟨324815, by rfl⟩ : syracuseStep 1732349 = 649631) (by norm_num)
theorem B1732373 : Blo 1152637 1732373 := bbase (se 6 (by rfl) ⟨40602, by rfl⟩ : syracuseStep 1732373 = 81205) (by norm_num)
theorem B1732397 : Blo 1152637 1732397 := bbase (se 3 (by rfl) ⟨324824, by rfl⟩ : syracuseStep 1732397 = 649649) (by norm_num)
theorem B1732421 : Blo 1152637 1732421 := bbase (se 4 (by rfl) ⟨162414, by rfl⟩ : syracuseStep 1732421 = 324829) (by norm_num)
theorem B1732445 : Blo 1152637 1732445 := bbase (se 3 (by rfl) ⟨324833, by rfl⟩ : syracuseStep 1732445 = 649667) (by norm_num)
theorem B1732469 : Blo 1152637 1732469 := bbase (se 5 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 1732469 = 162419) (by norm_num)
theorem B1732493 : Blo 1152637 1732493 := bbase (se 3 (by rfl) ⟨324842, by rfl⟩ : syracuseStep 1732493 = 649685) (by norm_num)
theorem B1732517 : Blo 1152637 1732517 := bbase (se 4 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 1732517 = 324847) (by norm_num)
theorem B1732541 : Blo 1152637 1732541 := bbase (se 3 (by rfl) ⟨324851, by rfl⟩ : syracuseStep 1732541 = 649703) (by norm_num)
theorem B4386757 : Blo 1152637 4386757 := bbase (se 4 (by rfl) ⟨411258, by rfl⟩ : syracuseStep 4386757 = 822517) (by norm_num)
theorem B1732565 : Blo 1152637 1732565 := bbase (se 7 (by rfl) ⟨20303, by rfl⟩ : syracuseStep 1732565 = 40607) (by norm_num)
theorem B1732589 : Blo 1152637 1732589 := bbase (se 3 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 1732589 = 649721) (by norm_num)
theorem B1732613 : Blo 1152637 1732613 := bbase (se 4 (by rfl) ⟨162432, by rfl⟩ : syracuseStep 1732613 = 324865) (by norm_num)
theorem B1732637 : Blo 1152637 1732637 := bbase (se 3 (by rfl) ⟨324869, by rfl⟩ : syracuseStep 1732637 = 649739) (by norm_num)
theorem B1732661 : Blo 1152637 1732661 := bbase (se 5 (by rfl) ⟨81218, by rfl⟩ : syracuseStep 1732661 = 162437) (by norm_num)
theorem B1732685 : Blo 1152637 1732685 := bbase (se 3 (by rfl) ⟨324878, by rfl⟩ : syracuseStep 1732685 = 649757) (by norm_num)
theorem B3895397 : Blo 1152637 3895397 := bbase (se 4 (by rfl) ⟨365193, by rfl⟩ : syracuseStep 3895397 = 730387) (by norm_num)
theorem B1732709 : Blo 1152637 1732709 := bbase (se 4 (by rfl) ⟨162441, by rfl⟩ : syracuseStep 1732709 = 324883) (by norm_num)
theorem B1732733 : Blo 1152637 1732733 := bbase (se 3 (by rfl) ⟨324887, by rfl⟩ : syracuseStep 1732733 = 649775) (by norm_num)
theorem B1732757 : Blo 1152637 1732757 := bbase (se 6 (by rfl) ⟨40611, by rfl⟩ : syracuseStep 1732757 = 81223) (by norm_num)
theorem B1732781 : Blo 1152637 1732781 := bbase (se 3 (by rfl) ⟨324896, by rfl⟩ : syracuseStep 1732781 = 649793) (by norm_num)
theorem B2191549 : Blo 1152637 2191549 := bbase (se 3 (by rfl) ⟨410915, by rfl⟩ : syracuseStep 2191549 = 821831) (by norm_num)
theorem B1732805 : Blo 1152637 1732805 := bbase (se 4 (by rfl) ⟨162450, by rfl⟩ : syracuseStep 1732805 = 324901) (by norm_num)
theorem B1732829 : Blo 1152637 1732829 := bbase (se 3 (by rfl) ⟨324905, by rfl⟩ : syracuseStep 1732829 = 649811) (by norm_num)
theorem B1405153 : Blo 1152637 1405153 := bbase (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) (by norm_num)
theorem B1732853 : Blo 1152637 1732853 := bbase (se 5 (by rfl) ⟨81227, by rfl⟩ : syracuseStep 1732853 = 162455) (by norm_num)
theorem B4387061 : Blo 1152637 4387061 := bbase (se 5 (by rfl) ⟨205643, by rfl⟩ : syracuseStep 4387061 = 411287) (by norm_num)
theorem B1732877 : Blo 1152637 1732877 := bbase (se 3 (by rfl) ⟨324914, by rfl⟩ : syracuseStep 1732877 = 649829) (by norm_num)
theorem B1372445 : Blo 1152637 1372445 := bbase (se 3 (by rfl) ⟨257333, by rfl⟩ : syracuseStep 1372445 = 514667) (by norm_num)
theorem B1732901 : Blo 1152637 1732901 := bbase (se 4 (by rfl) ⟨162459, by rfl⟩ : syracuseStep 1732901 = 324919) (by norm_num)
theorem B1732925 : Blo 1152637 1732925 := bbase (se 3 (by rfl) ⟨324923, by rfl⟩ : syracuseStep 1732925 = 649847) (by norm_num)
theorem B2191693 : Blo 1152637 2191693 := bbase (se 3 (by rfl) ⟨410942, by rfl⟩ : syracuseStep 2191693 = 821885) (by norm_num)
theorem B1732949 : Blo 1152637 1732949 := bbase (se 10 (by rfl) ⟨2538, by rfl⟩ : syracuseStep 1732949 = 5077) (by norm_num)
theorem B1732973 : Blo 1152637 1732973 := bbase (se 3 (by rfl) ⟨324932, by rfl⟩ : syracuseStep 1732973 = 649865) (by norm_num)
theorem B1732997 : Blo 1152637 1732997 := bbase (se 4 (by rfl) ⟨162468, by rfl⟩ : syracuseStep 1732997 = 324937) (by norm_num)
theorem B1733021 : Blo 1152637 1733021 := bbase (se 3 (by rfl) ⟨324941, by rfl⟩ : syracuseStep 1733021 = 649883) (by norm_num)
theorem B1733045 : Blo 1152637 1733045 := bbase (se 5 (by rfl) ⟨81236, by rfl⟩ : syracuseStep 1733045 = 162473) (by norm_num)
theorem B1667525 : Blo 1152637 1667525 := bbase (se 4 (by rfl) ⟨156330, by rfl⟩ : syracuseStep 1667525 = 312661) (by norm_num)
theorem B1733069 : Blo 1152637 1733069 := bbase (se 3 (by rfl) ⟨324950, by rfl⟩ : syracuseStep 1733069 = 649901) (by norm_num)
theorem B1733093 : Blo 1152637 1733093 := bbase (se 4 (by rfl) ⟨162477, by rfl⟩ : syracuseStep 1733093 = 324955) (by norm_num)
theorem B2191853 : Blo 1152637 2191853 := bbase (se 3 (by rfl) ⟨410972, by rfl⟩ : syracuseStep 2191853 = 821945) (by norm_num)
theorem B1733117 : Blo 1152637 1733117 := bbase (se 3 (by rfl) ⟨324959, by rfl⟩ : syracuseStep 1733117 = 649919) (by norm_num)
theorem B3895829 : Blo 1152637 3895829 := bbase (se 6 (by rfl) ⟨91308, by rfl⟩ : syracuseStep 3895829 = 182617) (by norm_num)
theorem B1733141 : Blo 1152637 1733141 := bbase (se 6 (by rfl) ⟨40620, by rfl⟩ : syracuseStep 1733141 = 81241) (by norm_num)
theorem B1733165 : Blo 1152637 1733165 := bbase (se 3 (by rfl) ⟨324968, by rfl⟩ : syracuseStep 1733165 = 649937) (by norm_num)
theorem B1733189 : Blo 1152637 1733189 := bbase (se 4 (by rfl) ⟨162486, by rfl⟩ : syracuseStep 1733189 = 324973) (by norm_num)
theorem B1733213 : Blo 1152637 1733213 := bbase (se 3 (by rfl) ⟨324977, by rfl⟩ : syracuseStep 1733213 = 649955) (by norm_num)
theorem B1733237 : Blo 1152637 1733237 := bbase (se 5 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 1733237 = 162491) (by norm_num)
theorem B2191997 : Blo 1152637 2191997 := bbase (se 3 (by rfl) ⟨410999, by rfl⟩ : syracuseStep 2191997 = 821999) (by norm_num)
theorem B1733261 : Blo 1152637 1733261 := bbase (se 3 (by rfl) ⟨324986, by rfl⟩ : syracuseStep 1733261 = 649973) (by norm_num)
theorem B1733285 : Blo 1152637 1733285 := bbase (se 4 (by rfl) ⟨162495, by rfl⟩ : syracuseStep 1733285 = 324991) (by norm_num)
theorem B1733309 : Blo 1152637 1733309 := bbase (se 3 (by rfl) ⟨324995, by rfl⟩ : syracuseStep 1733309 = 649991) (by norm_num)
theorem B1733333 : Blo 1152637 1733333 := bbase (se 7 (by rfl) ⟨20312, by rfl⟩ : syracuseStep 1733333 = 40625) (by norm_num)
theorem B1733357 : Blo 1152637 1733357 := bbase (se 3 (by rfl) ⟨325004, by rfl⟩ : syracuseStep 1733357 = 650009) (by norm_num)
theorem B1733381 : Blo 1152637 1733381 := bbase (se 4 (by rfl) ⟨162504, by rfl⟩ : syracuseStep 1733381 = 325009) (by norm_num)
theorem B4223765 : Blo 1152637 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B1733405 : Blo 1152637 1733405 := bbase (se 3 (by rfl) ⟨325013, by rfl⟩ : syracuseStep 1733405 = 650027) (by norm_num)
theorem B4682549 : Blo 1152637 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B1733429 : Blo 1152637 1733429 := bbase (se 5 (by rfl) ⟨81254, by rfl⟩ : syracuseStep 1733429 = 162509) (by norm_num)
theorem B1733453 : Blo 1152637 1733453 := bbase (se 3 (by rfl) ⟨325022, by rfl⟩ : syracuseStep 1733453 = 650045) (by norm_num)
theorem B1733477 : Blo 1152637 1733477 := bbase (se 4 (by rfl) ⟨162513, by rfl⟩ : syracuseStep 1733477 = 325027) (by norm_num)
theorem B1733501 : Blo 1152637 1733501 := bbase (se 3 (by rfl) ⟨325031, by rfl⟩ : syracuseStep 1733501 = 650063) (by norm_num)
theorem B1733525 : Blo 1152637 1733525 := bbase (se 6 (by rfl) ⟨40629, by rfl⟩ : syracuseStep 1733525 = 81259) (by norm_num)
theorem B2192285 : Blo 1152637 2192285 := bbase (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) (by norm_num)
theorem B1733549 : Blo 1152637 1733549 := bbase (se 3 (by rfl) ⟨325040, by rfl⟩ : syracuseStep 1733549 = 650081) (by norm_num)
theorem B3896261 : Blo 1152637 3896261 := bbase (se 4 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 3896261 = 730549) (by norm_num)
theorem B1733573 : Blo 1152637 1733573 := bbase (se 4 (by rfl) ⟨162522, by rfl⟩ : syracuseStep 1733573 = 325045) (by norm_num)
theorem B1733597 : Blo 1152637 1733597 := bbase (se 3 (by rfl) ⟨325049, by rfl⟩ : syracuseStep 1733597 = 650099) (by norm_num)
theorem B5927909 : Blo 1152637 5927909 := bbase (se 4 (by rfl) ⟨555741, by rfl⟩ : syracuseStep 5927909 = 1111483) (by norm_num)
theorem B1733621 : Blo 1152637 1733621 := bbase (se 5 (by rfl) ⟨81263, by rfl⟩ : syracuseStep 1733621 = 162527) (by norm_num)
theorem B1733645 : Blo 1152637 1733645 := bbase (se 3 (by rfl) ⟨325058, by rfl⟩ : syracuseStep 1733645 = 650117) (by norm_num)
theorem B1733669 : Blo 1152637 1733669 := bbase (se 4 (by rfl) ⟨162531, by rfl⟩ : syracuseStep 1733669 = 325063) (by norm_num)
theorem B2192437 : Blo 1152637 2192437 := bbase (se 5 (by rfl) ⟨102770, by rfl⟩ : syracuseStep 2192437 = 205541) (by norm_num)
theorem B1733693 : Blo 1152637 1733693 := bbase (se 3 (by rfl) ⟨325067, by rfl⟩ : syracuseStep 1733693 = 650135) (by norm_num)
theorem B1733717 : Blo 1152637 1733717 := bbase (se 8 (by rfl) ⟨10158, by rfl⟩ : syracuseStep 1733717 = 20317) (by norm_num)
theorem B1733741 : Blo 1152637 1733741 := bbase (se 3 (by rfl) ⟨325076, by rfl⟩ : syracuseStep 1733741 = 650153) (by norm_num)
theorem B1733765 : Blo 1152637 1733765 := bbase (se 4 (by rfl) ⟨162540, by rfl⟩ : syracuseStep 1733765 = 325081) (by norm_num)
theorem B1733789 : Blo 1152637 1733789 := bbase (se 3 (by rfl) ⟨325085, by rfl⟩ : syracuseStep 1733789 = 650171) (by norm_num)
theorem B1733813 : Blo 1152637 1733813 := bbase (se 5 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 1733813 = 162545) (by norm_num)
theorem B1668277 : Blo 1152637 1668277 := bbase (se 5 (by rfl) ⟨78200, by rfl⟩ : syracuseStep 1668277 = 156401) (by norm_num)
theorem B1733837 : Blo 1152637 1733837 := bbase (se 3 (by rfl) ⟨325094, by rfl⟩ : syracuseStep 1733837 = 650189) (by norm_num)
theorem B1733861 : Blo 1152637 1733861 := bbase (se 4 (by rfl) ⟨162549, by rfl⟩ : syracuseStep 1733861 = 325099) (by norm_num)
theorem B1733885 : Blo 1152637 1733885 := bbase (se 3 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 1733885 = 650207) (by norm_num)
theorem B1733909 : Blo 1152637 1733909 := bbase (se 6 (by rfl) ⟨40638, by rfl⟩ : syracuseStep 1733909 = 81277) (by norm_num)
theorem B1733933 : Blo 1152637 1733933 := bbase (se 3 (by rfl) ⟨325112, by rfl⟩ : syracuseStep 1733933 = 650225) (by norm_num)
theorem B2225461 : Blo 1152637 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B1733957 : Blo 1152637 1733957 := bbase (se 4 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 1733957 = 325117) (by norm_num)
theorem B1733981 : Blo 1152637 1733981 := bbase (se 3 (by rfl) ⟨325121, by rfl⟩ : syracuseStep 1733981 = 650243) (by norm_num)
theorem B2192741 : Blo 1152637 2192741 := bbase (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) (by norm_num)
theorem B3896693 : Blo 1152637 3896693 := bbase (se 5 (by rfl) ⟨182657, by rfl⟩ : syracuseStep 3896693 = 365315) (by norm_num)
theorem B1734005 : Blo 1152637 1734005 := bbase (se 5 (by rfl) ⟨81281, by rfl⟩ : syracuseStep 1734005 = 162563) (by norm_num)
theorem B1734029 : Blo 1152637 1734029 := bbase (se 3 (by rfl) ⟨325130, by rfl⟩ : syracuseStep 1734029 = 650261) (by norm_num)
theorem B1734053 : Blo 1152637 1734053 := bbase (se 4 (by rfl) ⟨162567, by rfl⟩ : syracuseStep 1734053 = 325135) (by norm_num)
theorem B1734077 : Blo 1152637 1734077 := bbase (se 3 (by rfl) ⟨325139, by rfl⟩ : syracuseStep 1734077 = 650279) (by norm_num)
theorem B1734101 : Blo 1152637 1734101 := bbase (se 7 (by rfl) ⟨20321, by rfl⟩ : syracuseStep 1734101 = 40643) (by norm_num)
theorem B1734125 : Blo 1152637 1734125 := bbase (se 3 (by rfl) ⟨325148, by rfl⟩ : syracuseStep 1734125 = 650297) (by norm_num)
theorem B1734149 : Blo 1152637 1734149 := bbase (se 4 (by rfl) ⟨162576, by rfl⟩ : syracuseStep 1734149 = 325153) (by norm_num)
theorem B1734173 : Blo 1152637 1734173 := bbase (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) (by norm_num)
theorem B1734197 : Blo 1152637 1734197 := bbase (se 5 (by rfl) ⟨81290, by rfl⟩ : syracuseStep 1734197 = 162581) (by norm_num)
theorem B1734221 : Blo 1152637 1734221 := bbase (se 3 (by rfl) ⟨325166, by rfl⟩ : syracuseStep 1734221 = 650333) (by norm_num)
theorem B1734245 : Blo 1152637 1734245 := bbase (se 4 (by rfl) ⟨162585, by rfl⟩ : syracuseStep 1734245 = 325171) (by norm_num)
theorem B1734269 : Blo 1152637 1734269 := bbase (se 3 (by rfl) ⟨325175, by rfl⟩ : syracuseStep 1734269 = 650351) (by norm_num)
theorem B4748933 : Blo 1152637 4748933 := bbase (se 4 (by rfl) ⟨445212, by rfl⟩ : syracuseStep 4748933 = 890425) (by norm_num)
theorem B1734293 : Blo 1152637 1734293 := bbase (se 6 (by rfl) ⟨40647, by rfl⟩ : syracuseStep 1734293 = 81295) (by norm_num)
theorem B1734317 : Blo 1152637 1734317 := bbase (se 3 (by rfl) ⟨325184, by rfl⟩ : syracuseStep 1734317 = 650369) (by norm_num)
theorem B1734341 : Blo 1152637 1734341 := bbase (se 4 (by rfl) ⟨162594, by rfl⟩ : syracuseStep 1734341 = 325189) (by norm_num)
theorem B1734365 : Blo 1152637 1734365 := bbase (se 3 (by rfl) ⟨325193, by rfl⟩ : syracuseStep 1734365 = 650387) (by norm_num)
theorem B1734389 : Blo 1152637 1734389 := bbase (se 5 (by rfl) ⟨81299, by rfl⟩ : syracuseStep 1734389 = 162599) (by norm_num)
theorem B1734413 : Blo 1152637 1734413 := bbase (se 3 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 1734413 = 650405) (by norm_num)
theorem B3897125 : Blo 1152637 3897125 := bbase (se 4 (by rfl) ⟨365355, by rfl⟩ : syracuseStep 3897125 = 730711) (by norm_num)
theorem B1734437 : Blo 1152637 1734437 := bbase (se 4 (by rfl) ⟨162603, by rfl⟩ : syracuseStep 1734437 = 325207) (by norm_num)
theorem B1734461 : Blo 1152637 1734461 := bbase (se 3 (by rfl) ⟨325211, by rfl⟩ : syracuseStep 1734461 = 650423) (by norm_num)
theorem B1406789 : Blo 1152637 1406789 := bbase (se 4 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 1406789 = 263773) (by norm_num)
theorem B1734485 : Blo 1152637 1734485 := bbase (se 9 (by rfl) ⟨5081, by rfl⟩ : syracuseStep 1734485 = 10163) (by norm_num)
theorem B1734509 : Blo 1152637 1734509 := bbase (se 3 (by rfl) ⟨325220, by rfl⟩ : syracuseStep 1734509 = 650441) (by norm_num)
theorem B1734533 : Blo 1152637 1734533 := bbase (se 4 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 1734533 = 325225) (by norm_num)
theorem B1734557 : Blo 1152637 1734557 := bbase (se 3 (by rfl) ⟨325229, by rfl⟩ : syracuseStep 1734557 = 650459) (by norm_num)
theorem B1734581 : Blo 1152637 1734581 := bbase (se 5 (by rfl) ⟨81308, by rfl⟩ : syracuseStep 1734581 = 162617) (by norm_num)
theorem B1734605 : Blo 1152637 1734605 := bbase (se 3 (by rfl) ⟨325238, by rfl⟩ : syracuseStep 1734605 = 650477) (by norm_num)
theorem B1734629 : Blo 1152637 1734629 := bbase (se 4 (by rfl) ⟨162621, by rfl⟩ : syracuseStep 1734629 = 325243) (by norm_num)
theorem B1734653 : Blo 1152637 1734653 := bbase (se 3 (by rfl) ⟨325247, by rfl⟩ : syracuseStep 1734653 = 650495) (by norm_num)
theorem B1734677 : Blo 1152637 1734677 := bbase (se 6 (by rfl) ⟨40656, by rfl⟩ : syracuseStep 1734677 = 81313) (by norm_num)
theorem B1734701 : Blo 1152637 1734701 := bbase (se 3 (by rfl) ⟨325256, by rfl⟩ : syracuseStep 1734701 = 650513) (by norm_num)
theorem B4683845 : Blo 1152637 4683845 := bbase (se 4 (by rfl) ⟨439110, by rfl⟩ : syracuseStep 4683845 = 878221) (by norm_num)
theorem B1734725 : Blo 1152637 1734725 := bbase (se 4 (by rfl) ⟨162630, by rfl⟩ : syracuseStep 1734725 = 325261) (by norm_num)
theorem B2193493 : Blo 1152637 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B1734749 : Blo 1152637 1734749 := bbase (se 3 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 1734749 = 650531) (by norm_num)
theorem B1734773 : Blo 1152637 1734773 := bbase (se 5 (by rfl) ⟨81317, by rfl⟩ : syracuseStep 1734773 = 162635) (by norm_num)
theorem B1734797 : Blo 1152637 1734797 := bbase (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) (by norm_num)
theorem B1734821 : Blo 1152637 1734821 := bbase (se 4 (by rfl) ⟨162639, by rfl⟩ : syracuseStep 1734821 = 325279) (by norm_num)
theorem B4159669 : Blo 1152637 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B1734845 : Blo 1152637 1734845 := bbase (se 3 (by rfl) ⟨325283, by rfl⟩ : syracuseStep 1734845 = 650567) (by norm_num)
theorem B3897557 : Blo 1152637 3897557 := bbase (se 7 (by rfl) ⟨45674, by rfl⟩ : syracuseStep 3897557 = 91349) (by norm_num)
theorem B1734869 : Blo 1152637 1734869 := bbase (se 7 (by rfl) ⟨20330, by rfl⟩ : syracuseStep 1734869 = 40661) (by norm_num)
theorem B2193637 : Blo 1152637 2193637 := bbase (se 4 (by rfl) ⟨205653, by rfl⟩ : syracuseStep 2193637 = 411307) (by norm_num)
theorem B1734893 : Blo 1152637 1734893 := bbase (se 3 (by rfl) ⟨325292, by rfl⟩ : syracuseStep 1734893 = 650585) (by norm_num)
theorem B1734917 : Blo 1152637 1734917 := bbase (se 4 (by rfl) ⟨162648, by rfl⟩ : syracuseStep 1734917 = 325297) (by norm_num)
theorem B1734941 : Blo 1152637 1734941 := bbase (se 3 (by rfl) ⟨325301, by rfl⟩ : syracuseStep 1734941 = 650603) (by norm_num)
theorem B4389173 : Blo 1152637 4389173 := bbase (se 5 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 4389173 = 411485) (by norm_num)
theorem B4159829 : Blo 1152637 4159829 := bbase (se 10 (by rfl) ⟨6093, by rfl⟩ : syracuseStep 4159829 = 12187) (by norm_num)
theorem B16644437 : Blo 1152637 16644437 := bbase (se 10 (by rfl) ⟨24381, by rfl⟩ : syracuseStep 16644437 = 48763) (by norm_num)
theorem B2193797 : Blo 1152637 2193797 := bbase (se 4 (by rfl) ⟨205668, by rfl⟩ : syracuseStep 2193797 = 411337) (by norm_num)
theorem B4159957 : Blo 1152637 4159957 := bbase (se 7 (by rfl) ⟨48749, by rfl⟩ : syracuseStep 4159957 = 97499) (by norm_num)
theorem B2193941 : Blo 1152637 2193941 := bbase (se 6 (by rfl) ⟨51420, by rfl⟩ : syracuseStep 2193941 = 102841) (by norm_num)
theorem B2030117 : Blo 1152637 2030117 := bbase (se 4 (by rfl) ⟨190323, by rfl⟩ : syracuseStep 2030117 = 380647) (by norm_num)
theorem B4389461 : Blo 1152637 4389461 := bbase (se 8 (by rfl) ⟨25719, by rfl⟩ : syracuseStep 4389461 = 51439) (by norm_num)
theorem B3897989 : Blo 1152637 3897989 := bbase (se 4 (by rfl) ⟨365436, by rfl⟩ : syracuseStep 3897989 = 730873) (by norm_num)
theorem B2194229 : Blo 1152637 2194229 := bbase (se 5 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 2194229 = 205709) (by norm_num)
theorem B2194381 : Blo 1152637 2194381 := bbase (se 3 (by rfl) ⟨411446, by rfl⟩ : syracuseStep 2194381 = 822893) (by norm_num)
theorem B3898421 : Blo 1152637 3898421 := bbase (se 5 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 3898421 = 365477) (by norm_num)
theorem B57736277 : Blo 1152637 57736277 := bbase (se 8 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 57736277 = 676597) (by norm_num)
theorem B2194685 : Blo 1152637 2194685 := bbase (se 3 (by rfl) ⟨411503, by rfl⟩ : syracuseStep 2194685 = 823007) (by norm_num)
theorem B11107637 : Blo 1152637 11107637 := bbase (se 5 (by rfl) ⟨520670, by rfl⟩ : syracuseStep 11107637 = 1041341) (by norm_num)
theorem B4685141 : Blo 1152637 4685141 := bbase (se 11 (by rfl) ⟨3431, by rfl⟩ : syracuseStep 4685141 = 6863) (by norm_num)
theorem B3898853 : Blo 1152637 3898853 := bbase (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) (by norm_num)
theorem B3702341 : Blo 1152637 3702341 := bbase (se 4 (by rfl) ⟨347094, by rfl⟩ : syracuseStep 3702341 = 694189) (by norm_num)
theorem B4390645 : Blo 1152637 4390645 := bbase (se 5 (by rfl) ⟨205811, by rfl⟩ : syracuseStep 4390645 = 411623) (by norm_num)
theorem B33259349 : Blo 1152637 33259349 := bbase (se 9 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 33259349 = 194879) (by norm_num)
theorem B3899285 : Blo 1152637 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B2195437 : Blo 1152637 2195437 := bbase (se 3 (by rfl) ⟨411644, by rfl⟩ : syracuseStep 2195437 = 823289) (by norm_num)
theorem B28508213 : Blo 1152637 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B3506257 : Blo 1152637 3506257 := bstep (se 2 (by rfl) ⟨1314846, by rfl⟩ : syracuseStep 3506257 = 2629693) B2629693
theorem B3899501 : Blo 1152637 3899501 := bstep (se 3 (by rfl) ⟨731156, by rfl⟩ : syracuseStep 3899501 = 1462313) B1462313
theorem B3899555 : Blo 1152637 3899555 := bstep (se 1 (by rfl) ⟨2924666, by rfl⟩ : syracuseStep 3899555 = 5849333) B5849333
theorem B4391117 : Blo 1152637 4391117 := bstep (se 3 (by rfl) ⟨823334, by rfl⟩ : syracuseStep 4391117 = 1646669) B1646669
theorem B11108593 : Blo 1152637 11108593 := bstep (se 2 (by rfl) ⟨4165722, by rfl⟩ : syracuseStep 11108593 = 8331445) B8331445
theorem B33292565 : Blo 1152637 33292565 := bstep (se 6 (by rfl) ⟨780294, by rfl⟩ : syracuseStep 33292565 = 1560589) B1560589
theorem B4686179 : Blo 1152637 4686179 := bstep (se 1 (by rfl) ⟨3514634, by rfl⟩ : syracuseStep 4686179 = 7029269) B7029269
theorem B3899825 : Blo 1152637 3899825 := bstep (se 2 (by rfl) ⟨1462434, by rfl⟩ : syracuseStep 3899825 = 2924869) B2924869
theorem B49873805 : Blo 1152637 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B3900365 : Blo 1152637 3900365 := bstep (se 3 (by rfl) ⟨731318, by rfl⟩ : syracuseStep 3900365 = 1462637) B1462637
theorem B3900419 : Blo 1152637 3900419 := bstep (se 1 (by rfl) ⟨2925314, by rfl⟩ : syracuseStep 3900419 = 5850629) B5850629
theorem B9372685 : Blo 1152637 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B6587405 : Blo 1152637 6587405 := bstep (se 3 (by rfl) ⟨1235138, by rfl⟩ : syracuseStep 6587405 = 2470277) B2470277
theorem B3703981 : Blo 1152637 3703981 := bstep (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) B1388993
theorem B3900689 : Blo 1152637 3900689 := bstep (se 2 (by rfl) ⟨1462758, by rfl⟩ : syracuseStep 3900689 = 2925517) B2925517
theorem B8881649 : Blo 1152637 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B3704429 : Blo 1152637 3704429 := bstep (se 3 (by rfl) ⟨694580, by rfl⟩ : syracuseStep 3704429 = 1389161) B1389161
theorem B2918065 : Blo 1152637 2918065 := bstep (se 2 (by rfl) ⟨1094274, by rfl⟩ : syracuseStep 2918065 = 2188549) B2188549
theorem B3901229 : Blo 1152637 3901229 := bstep (se 3 (by rfl) ⟨731480, by rfl⟩ : syracuseStep 3901229 = 1462961) B1462961
theorem B3901283 : Blo 1152637 3901283 := bstep (se 1 (by rfl) ⟨2925962, by rfl⟩ : syracuseStep 3901283 = 5851925) B5851925
theorem B2918339 : Blo 1152637 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B3901553 : Blo 1152637 3901553 := bstep (se 2 (by rfl) ⟨1463082, by rfl⟩ : syracuseStep 3901553 = 2926165) B2926165
theorem B2918531 : Blo 1152637 2918531 := bstep (se 1 (by rfl) ⟨2188898, by rfl⟩ : syracuseStep 2918531 = 4377797) B4377797
theorem B3508529 : Blo 1152637 3508529 := bstep (se 2 (by rfl) ⟨1315698, by rfl⟩ : syracuseStep 3508529 = 2631397) B2631397
theorem B3902093 : Blo 1152637 3902093 := bstep (se 3 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 3902093 = 1463285) B1463285
theorem B3902147 : Blo 1152637 3902147 := bstep (se 1 (by rfl) ⟨2926610, by rfl⟩ : syracuseStep 3902147 = 5853221) B5853221
theorem B3115729 : Blo 1152637 3115729 := bstep (se 2 (by rfl) ⟨1168398, by rfl⟩ : syracuseStep 3115729 = 2336797) B2336797
theorem B5835725 : Blo 1152637 5835725 := bstep (se 3 (by rfl) ⟨1094198, by rfl⟩ : syracuseStep 5835725 = 2188397) B2188397
theorem B3902417 : Blo 1152637 3902417 := bstep (se 2 (by rfl) ⟨1463406, by rfl⟩ : syracuseStep 3902417 = 2926813) B2926813
theorem B8326115 : Blo 1152637 8326115 := bstep (se 1 (by rfl) ⟨6244586, by rfl⟩ : syracuseStep 8326115 = 12489173) B12489173
theorem B1641475 : Blo 1152637 1641475 := bstep (se 1 (by rfl) ⟨1231106, by rfl⟩ : syracuseStep 1641475 = 2462213) B2462213
theorem B2919473 : Blo 1152637 2919473 := bstep (se 2 (by rfl) ⟨1094802, by rfl⟩ : syracuseStep 2919473 = 2189605) B2189605
theorem B2919523 : Blo 1152637 2919523 := bstep (se 1 (by rfl) ⟨2189642, by rfl⟩ : syracuseStep 2919523 = 4379285) B4379285
theorem B2919665 : Blo 1152637 2919665 := bstep (se 2 (by rfl) ⟨1094874, by rfl⟩ : syracuseStep 2919665 = 2189749) B2189749
theorem B1641811 : Blo 1152637 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B7409009 : Blo 1152637 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B3902957 : Blo 1152637 3902957 := bstep (se 3 (by rfl) ⟨731804, by rfl⟩ : syracuseStep 3902957 = 1463609) B1463609
theorem B3903011 : Blo 1152637 3903011 := bstep (se 1 (by rfl) ⟨2927258, by rfl⟩ : syracuseStep 3903011 = 5854517) B5854517
theorem B2002625 : Blo 1152637 2002625 := bstep (se 2 (by rfl) ⟨750984, by rfl⟩ : syracuseStep 2002625 = 1501969) B1501969
theorem B1871603 : Blo 1152637 1871603 := bstep (se 1 (by rfl) ⟨1403702, by rfl⟩ : syracuseStep 1871603 = 2807405) B2807405
theorem B3903281 : Blo 1152637 3903281 := bstep (se 2 (by rfl) ⟨1463730, by rfl⟩ : syracuseStep 3903281 = 2927461) B2927461
theorem B1642369 : Blo 1152637 1642369 := bstep (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) B1231777
theorem B3116963 : Blo 1152637 3116963 := bstep (se 1 (by rfl) ⟨2337722, by rfl⟩ : syracuseStep 3116963 = 4675445) B4675445
theorem B1642403 : Blo 1152637 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B7409677 : Blo 1152637 7409677 := bstep (se 3 (by rfl) ⟨1389314, by rfl⟩ : syracuseStep 7409677 = 2778629) B2778629
theorem B1314883 : Blo 1152637 1314883 := bstep (se 1 (by rfl) ⟨986162, by rfl⟩ : syracuseStep 1314883 = 1972325) B1972325
theorem B2920657 : Blo 1152637 2920657 := bstep (se 2 (by rfl) ⟨1095246, by rfl⟩ : syracuseStep 2920657 = 2190493) B2190493
theorem B1642961 : Blo 1152637 1642961 := bstep (se 2 (by rfl) ⟨616110, by rfl⟩ : syracuseStep 1642961 = 1232221) B1232221
theorem B2920931 : Blo 1152637 2920931 := bstep (se 1 (by rfl) ⟨2190698, by rfl⟩ : syracuseStep 2920931 = 4381397) B4381397
theorem B1643041 : Blo 1152637 1643041 := bstep (se 2 (by rfl) ⟨616140, by rfl⟩ : syracuseStep 1643041 = 1232281) B1232281
theorem B2921123 : Blo 1152637 2921123 := bstep (se 1 (by rfl) ⟨2190842, by rfl⟩ : syracuseStep 2921123 = 4381685) B4381685
theorem B2593457 : Blo 1152637 2593457 := bstep (se 2 (by rfl) ⟨972546, by rfl⟩ : syracuseStep 2593457 = 1945093) B1945093
theorem B2593475 : Blo 1152637 2593475 := bstep (se 1 (by rfl) ⟨1945106, by rfl⟩ : syracuseStep 2593475 = 3890213) B3890213
theorem B1250051 : Blo 1152637 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B2593745 : Blo 1152637 2593745 := bstep (se 2 (by rfl) ⟨972654, by rfl⟩ : syracuseStep 2593745 = 1945309) B1945309
theorem B2593763 : Blo 1152637 2593763 := bstep (se 1 (by rfl) ⟨1945322, by rfl⟩ : syracuseStep 2593763 = 3890645) B3890645
theorem B8754317 : Blo 1152637 8754317 := bstep (se 3 (by rfl) ⟨1641434, by rfl⟩ : syracuseStep 8754317 = 3282869) B3282869
theorem B2594033 : Blo 1152637 2594033 := bstep (se 2 (by rfl) ⟨972762, by rfl⟩ : syracuseStep 2594033 = 1945525) B1945525
theorem B2594051 : Blo 1152637 2594051 := bstep (se 1 (by rfl) ⟨1945538, by rfl⟩ : syracuseStep 2594051 = 3891077) B3891077
theorem B1643827 : Blo 1152637 1643827 := bstep (se 1 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 1643827 = 2465741) B2465741
theorem B3282403 : Blo 1152637 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B2594321 : Blo 1152637 2594321 := bstep (se 2 (by rfl) ⟨972870, by rfl⟩ : syracuseStep 2594321 = 1945741) B1945741
theorem B2594339 : Blo 1152637 2594339 := bstep (se 1 (by rfl) ⟨1945754, by rfl⟩ : syracuseStep 2594339 = 3891509) B3891509
theorem B2922065 : Blo 1152637 2922065 := bstep (se 2 (by rfl) ⟨1095774, by rfl⟩ : syracuseStep 2922065 = 2191549) B2191549
theorem B1152643 : Blo 1152637 1152643 := bstep (se 1 (by rfl) ⟨864482, by rfl⟩ : syracuseStep 1152643 = 1728965) B1728965
theorem B2922115 : Blo 1152637 2922115 := bstep (se 1 (by rfl) ⟨2191586, by rfl⟩ : syracuseStep 2922115 = 4383173) B4383173
theorem B1152659 : Blo 1152637 1152659 := bstep (se 1 (by rfl) ⟨864494, by rfl⟩ : syracuseStep 1152659 = 1728989) B1728989
theorem B1152675 : Blo 1152637 1152675 := bstep (se 1 (by rfl) ⟨864506, by rfl⟩ : syracuseStep 1152675 = 1729013) B1729013
theorem B1152691 : Blo 1152637 1152691 := bstep (se 1 (by rfl) ⟨864518, by rfl⟩ : syracuseStep 1152691 = 1729037) B1729037
theorem B1152707 : Blo 1152637 1152707 := bstep (se 1 (by rfl) ⟨864530, by rfl⟩ : syracuseStep 1152707 = 1729061) B1729061
theorem B1152723 : Blo 1152637 1152723 := bstep (se 1 (by rfl) ⟨864542, by rfl⟩ : syracuseStep 1152723 = 1729085) B1729085
theorem B1152739 : Blo 1152637 1152739 := bstep (se 1 (by rfl) ⟨864554, by rfl⟩ : syracuseStep 1152739 = 1729109) B1729109
theorem B1152755 : Blo 1152637 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B1152771 : Blo 1152637 1152771 := bstep (se 1 (by rfl) ⟨864578, by rfl⟩ : syracuseStep 1152771 = 1729157) B1729157
theorem B2922257 : Blo 1152637 2922257 := bstep (se 2 (by rfl) ⟨1095846, by rfl⟩ : syracuseStep 2922257 = 2191693) B2191693
theorem B1644305 : Blo 1152637 1644305 := bstep (se 2 (by rfl) ⟨616614, by rfl⟩ : syracuseStep 1644305 = 1233229) B1233229
theorem B1152787 : Blo 1152637 1152787 := bstep (se 1 (by rfl) ⟨864590, by rfl⟩ : syracuseStep 1152787 = 1729181) B1729181
theorem B1152803 : Blo 1152637 1152803 := bstep (se 1 (by rfl) ⟨864602, by rfl⟩ : syracuseStep 1152803 = 1729205) B1729205
theorem B2594609 : Blo 1152637 2594609 := bstep (se 2 (by rfl) ⟨972978, by rfl⟩ : syracuseStep 2594609 = 1945957) B1945957
theorem B5838641 : Blo 1152637 5838641 := bstep (se 2 (by rfl) ⟨2189490, by rfl⟩ : syracuseStep 5838641 = 4378981) B4378981
theorem B1152819 : Blo 1152637 1152819 := bstep (se 1 (by rfl) ⟨864614, by rfl⟩ : syracuseStep 1152819 = 1729229) B1729229
theorem B22484789 : Blo 1152637 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B1152835 : Blo 1152637 1152835 := bstep (se 1 (by rfl) ⟨864626, by rfl⟩ : syracuseStep 1152835 = 1729253) B1729253
theorem B2594627 : Blo 1152637 2594627 := bstep (se 1 (by rfl) ⟨1945970, by rfl⟩ : syracuseStep 2594627 = 3891941) B3891941
theorem B1152851 : Blo 1152637 1152851 := bstep (se 1 (by rfl) ⟨864638, by rfl⟩ : syracuseStep 1152851 = 1729277) B1729277
theorem B1152867 : Blo 1152637 1152867 := bstep (se 1 (by rfl) ⟨864650, by rfl⟩ : syracuseStep 1152867 = 1729301) B1729301
theorem B12490595 : Blo 1152637 12490595 := bstep (se 1 (by rfl) ⟨9367946, by rfl⟩ : syracuseStep 12490595 = 18735893) B18735893
theorem B1152883 : Blo 1152637 1152883 := bstep (se 1 (by rfl) ⟨864662, by rfl⟩ : syracuseStep 1152883 = 1729325) B1729325
theorem B1152899 : Blo 1152637 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B1644419 : Blo 1152637 1644419 := bstep (se 1 (by rfl) ⟨1233314, by rfl⟩ : syracuseStep 1644419 = 2466629) B2466629
theorem B1152915 : Blo 1152637 1152915 := bstep (se 1 (by rfl) ⟨864686, by rfl⟩ : syracuseStep 1152915 = 1729373) B1729373
theorem B1152931 : Blo 1152637 1152931 := bstep (se 1 (by rfl) ⟨864698, by rfl⟩ : syracuseStep 1152931 = 1729397) B1729397
theorem B1152947 : Blo 1152637 1152947 := bstep (se 1 (by rfl) ⟨864710, by rfl⟩ : syracuseStep 1152947 = 1729421) B1729421
theorem B1152963 : Blo 1152637 1152963 := bstep (se 1 (by rfl) ⟨864722, by rfl⟩ : syracuseStep 1152963 = 1729445) B1729445
theorem B3282893 : Blo 1152637 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B1152979 : Blo 1152637 1152979 := bstep (se 1 (by rfl) ⟨864734, by rfl⟩ : syracuseStep 1152979 = 1729469) B1729469
theorem B1644499 : Blo 1152637 1644499 := bstep (se 1 (by rfl) ⟨1233374, by rfl⟩ : syracuseStep 1644499 = 2466749) B2466749
theorem B1152995 : Blo 1152637 1152995 := bstep (se 1 (by rfl) ⟨864746, by rfl⟩ : syracuseStep 1152995 = 1729493) B1729493
theorem B1153011 : Blo 1152637 1153011 := bstep (se 1 (by rfl) ⟨864758, by rfl⟩ : syracuseStep 1153011 = 1729517) B1729517
theorem B1153027 : Blo 1152637 1153027 := bstep (se 1 (by rfl) ⟨864770, by rfl⟩ : syracuseStep 1153027 = 1729541) B1729541
theorem B1153043 : Blo 1152637 1153043 := bstep (se 1 (by rfl) ⟨864782, by rfl⟩ : syracuseStep 1153043 = 1729565) B1729565
theorem B1153059 : Blo 1152637 1153059 := bstep (se 1 (by rfl) ⟨864794, by rfl⟩ : syracuseStep 1153059 = 1729589) B1729589
theorem B1153075 : Blo 1152637 1153075 := bstep (se 1 (by rfl) ⟨864806, by rfl⟩ : syracuseStep 1153075 = 1729613) B1729613
theorem B1153091 : Blo 1152637 1153091 := bstep (se 1 (by rfl) ⟨864818, by rfl⟩ : syracuseStep 1153091 = 1729637) B1729637
theorem B2594897 : Blo 1152637 2594897 := bstep (se 2 (by rfl) ⟨973086, by rfl⟩ : syracuseStep 2594897 = 1946173) B1946173
theorem B1153107 : Blo 1152637 1153107 := bstep (se 1 (by rfl) ⟨864830, by rfl⟩ : syracuseStep 1153107 = 1729661) B1729661
theorem B1153123 : Blo 1152637 1153123 := bstep (se 1 (by rfl) ⟨864842, by rfl⟩ : syracuseStep 1153123 = 1729685) B1729685
theorem B2594915 : Blo 1152637 2594915 := bstep (se 1 (by rfl) ⟨1946186, by rfl⟩ : syracuseStep 2594915 = 3892373) B3892373
theorem B5544035 : Blo 1152637 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B1153139 : Blo 1152637 1153139 := bstep (se 1 (by rfl) ⟨864854, by rfl⟩ : syracuseStep 1153139 = 1729709) B1729709
theorem B1153155 : Blo 1152637 1153155 := bstep (se 1 (by rfl) ⟨864866, by rfl⟩ : syracuseStep 1153155 = 1729733) B1729733
theorem B1153171 : Blo 1152637 1153171 := bstep (se 1 (by rfl) ⟨864878, by rfl⟩ : syracuseStep 1153171 = 1729757) B1729757
theorem B1153187 : Blo 1152637 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B1153203 : Blo 1152637 1153203 := bstep (se 1 (by rfl) ⟨864902, by rfl⟩ : syracuseStep 1153203 = 1729805) B1729805
theorem B1153219 : Blo 1152637 1153219 := bstep (se 1 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 1153219 = 1729829) B1729829
theorem B1153235 : Blo 1152637 1153235 := bstep (se 1 (by rfl) ⟨864926, by rfl⟩ : syracuseStep 1153235 = 1729853) B1729853
theorem B1153251 : Blo 1152637 1153251 := bstep (se 1 (by rfl) ⟨864938, by rfl⟩ : syracuseStep 1153251 = 1729877) B1729877
theorem B1153267 : Blo 1152637 1153267 := bstep (se 1 (by rfl) ⟨864950, by rfl⟩ : syracuseStep 1153267 = 1729901) B1729901
theorem B1153283 : Blo 1152637 1153283 := bstep (se 1 (by rfl) ⟨864962, by rfl⟩ : syracuseStep 1153283 = 1729925) B1729925
theorem B1153299 : Blo 1152637 1153299 := bstep (se 1 (by rfl) ⟨864974, by rfl⟩ : syracuseStep 1153299 = 1729949) B1729949
theorem B1153315 : Blo 1152637 1153315 := bstep (se 1 (by rfl) ⟨864986, by rfl⟩ : syracuseStep 1153315 = 1729973) B1729973
theorem B5544227 : Blo 1152637 5544227 := bstep (se 1 (by rfl) ⟨4158170, by rfl⟩ : syracuseStep 5544227 = 8316341) B8316341
theorem B1153331 : Blo 1152637 1153331 := bstep (se 1 (by rfl) ⟨864998, by rfl⟩ : syracuseStep 1153331 = 1729997) B1729997
theorem B1153347 : Blo 1152637 1153347 := bstep (se 1 (by rfl) ⟨865010, by rfl⟩ : syracuseStep 1153347 = 1730021) B1730021
theorem B1153363 : Blo 1152637 1153363 := bstep (se 1 (by rfl) ⟨865022, by rfl⟩ : syracuseStep 1153363 = 1730045) B1730045
theorem B1153379 : Blo 1152637 1153379 := bstep (se 1 (by rfl) ⟨865034, by rfl⟩ : syracuseStep 1153379 = 1730069) B1730069
theorem B2595185 : Blo 1152637 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B1153395 : Blo 1152637 1153395 := bstep (se 1 (by rfl) ⟨865046, by rfl⟩ : syracuseStep 1153395 = 1730093) B1730093
theorem B1153411 : Blo 1152637 1153411 := bstep (se 1 (by rfl) ⟨865058, by rfl⟩ : syracuseStep 1153411 = 1730117) B1730117
theorem B2595203 : Blo 1152637 2595203 := bstep (se 1 (by rfl) ⟨1946402, by rfl⟩ : syracuseStep 2595203 = 3892805) B3892805
theorem B3512717 : Blo 1152637 3512717 := bstep (se 3 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 3512717 = 1317269) B1317269
theorem B1153427 : Blo 1152637 1153427 := bstep (se 1 (by rfl) ⟨865070, by rfl⟩ : syracuseStep 1153427 = 1730141) B1730141
theorem B1153443 : Blo 1152637 1153443 := bstep (se 1 (by rfl) ⟨865082, by rfl⟩ : syracuseStep 1153443 = 1730165) B1730165
theorem B1153459 : Blo 1152637 1153459 := bstep (se 1 (by rfl) ⟨865094, by rfl⟩ : syracuseStep 1153459 = 1730189) B1730189
theorem B1153475 : Blo 1152637 1153475 := bstep (se 1 (by rfl) ⟨865106, by rfl⟩ : syracuseStep 1153475 = 1730213) B1730213
theorem B2464195 : Blo 1152637 2464195 := bstep (se 1 (by rfl) ⟨1848146, by rfl⟩ : syracuseStep 2464195 = 3696293) B3696293
theorem B1153491 : Blo 1152637 1153491 := bstep (se 1 (by rfl) ⟨865118, by rfl⟩ : syracuseStep 1153491 = 1730237) B1730237
theorem B1153507 : Blo 1152637 1153507 := bstep (se 1 (by rfl) ⟨865130, by rfl⟩ : syracuseStep 1153507 = 1730261) B1730261
theorem B9869795 : Blo 1152637 9869795 := bstep (se 1 (by rfl) ⟨7402346, by rfl⟩ : syracuseStep 9869795 = 14804693) B14804693
theorem B1153523 : Blo 1152637 1153523 := bstep (se 1 (by rfl) ⟨865142, by rfl⟩ : syracuseStep 1153523 = 1730285) B1730285
theorem B1645057 : Blo 1152637 1645057 := bstep (se 2 (by rfl) ⟨616896, by rfl⟩ : syracuseStep 1645057 = 1233793) B1233793
theorem B1153539 : Blo 1152637 1153539 := bstep (se 1 (by rfl) ⟨865154, by rfl⟩ : syracuseStep 1153539 = 1730309) B1730309
theorem B1153555 : Blo 1152637 1153555 := bstep (se 1 (by rfl) ⟨865166, by rfl⟩ : syracuseStep 1153555 = 1730333) B1730333
theorem B1153571 : Blo 1152637 1153571 := bstep (se 1 (by rfl) ⟨865178, by rfl⟩ : syracuseStep 1153571 = 1730357) B1730357
theorem B1153587 : Blo 1152637 1153587 := bstep (se 1 (by rfl) ⟨865190, by rfl⟩ : syracuseStep 1153587 = 1730381) B1730381
theorem B1153603 : Blo 1152637 1153603 := bstep (se 1 (by rfl) ⟨865202, by rfl⟩ : syracuseStep 1153603 = 1730405) B1730405
theorem B1153619 : Blo 1152637 1153619 := bstep (se 1 (by rfl) ⟨865214, by rfl⟩ : syracuseStep 1153619 = 1730429) B1730429
theorem B1153635 : Blo 1152637 1153635 := bstep (se 1 (by rfl) ⟨865226, by rfl⟩ : syracuseStep 1153635 = 1730453) B1730453
theorem B1153651 : Blo 1152637 1153651 := bstep (se 1 (by rfl) ⟨865238, by rfl⟩ : syracuseStep 1153651 = 1730477) B1730477
theorem B1153667 : Blo 1152637 1153667 := bstep (se 1 (by rfl) ⟨865250, by rfl⟩ : syracuseStep 1153667 = 1730501) B1730501
theorem B2595473 : Blo 1152637 2595473 := bstep (se 2 (by rfl) ⟨973302, by rfl⟩ : syracuseStep 2595473 = 1946605) B1946605
theorem B1153683 : Blo 1152637 1153683 := bstep (se 1 (by rfl) ⟨865262, by rfl⟩ : syracuseStep 1153683 = 1730525) B1730525
theorem B2595491 : Blo 1152637 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B1153699 : Blo 1152637 1153699 := bstep (se 1 (by rfl) ⟨865274, by rfl⟩ : syracuseStep 1153699 = 1730549) B1730549
theorem B5544611 : Blo 1152637 5544611 := bstep (se 1 (by rfl) ⟨4158458, by rfl⟩ : syracuseStep 5544611 = 8316917) B8316917
theorem B1153715 : Blo 1152637 1153715 := bstep (se 1 (by rfl) ⟨865286, by rfl⟩ : syracuseStep 1153715 = 1730573) B1730573
theorem B1153731 : Blo 1152637 1153731 := bstep (se 1 (by rfl) ⟨865298, by rfl⟩ : syracuseStep 1153731 = 1730597) B1730597
theorem B1153747 : Blo 1152637 1153747 := bstep (se 1 (by rfl) ⟨865310, by rfl⟩ : syracuseStep 1153747 = 1730621) B1730621
theorem B1153763 : Blo 1152637 1153763 := bstep (se 1 (by rfl) ⟨865322, by rfl⟩ : syracuseStep 1153763 = 1730645) B1730645
theorem B2923249 : Blo 1152637 2923249 := bstep (se 2 (by rfl) ⟨1096218, by rfl⟩ : syracuseStep 2923249 = 2192437) B2192437
theorem B1153779 : Blo 1152637 1153779 := bstep (se 1 (by rfl) ⟨865334, by rfl⟩ : syracuseStep 1153779 = 1730669) B1730669
theorem B1153795 : Blo 1152637 1153795 := bstep (se 1 (by rfl) ⟨865346, by rfl⟩ : syracuseStep 1153795 = 1730693) B1730693
theorem B5413645 : Blo 1152637 5413645 := bstep (se 3 (by rfl) ⟨1015058, by rfl⟩ : syracuseStep 5413645 = 2030117) B2030117
theorem B1153811 : Blo 1152637 1153811 := bstep (se 1 (by rfl) ⟨865358, by rfl⟩ : syracuseStep 1153811 = 1730717) B1730717
theorem B1153827 : Blo 1152637 1153827 := bstep (se 1 (by rfl) ⟨865370, by rfl⟩ : syracuseStep 1153827 = 1730741) B1730741
theorem B1153843 : Blo 1152637 1153843 := bstep (se 1 (by rfl) ⟨865382, by rfl⟩ : syracuseStep 1153843 = 1730765) B1730765
theorem B1153859 : Blo 1152637 1153859 := bstep (se 1 (by rfl) ⟨865394, by rfl⟩ : syracuseStep 1153859 = 1730789) B1730789
theorem B1153875 : Blo 1152637 1153875 := bstep (se 1 (by rfl) ⟨865406, by rfl⟩ : syracuseStep 1153875 = 1730813) B1730813
theorem B1153891 : Blo 1152637 1153891 := bstep (se 1 (by rfl) ⟨865418, by rfl⟩ : syracuseStep 1153891 = 1730837) B1730837
theorem B1153907 : Blo 1152637 1153907 := bstep (se 1 (by rfl) ⟨865430, by rfl⟩ : syracuseStep 1153907 = 1730861) B1730861
theorem B1153923 : Blo 1152637 1153923 := bstep (se 1 (by rfl) ⟨865442, by rfl⟩ : syracuseStep 1153923 = 1730885) B1730885
theorem B1153939 : Blo 1152637 1153939 := bstep (se 1 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 1153939 = 1730909) B1730909
theorem B1153955 : Blo 1152637 1153955 := bstep (se 1 (by rfl) ⟨865466, by rfl⟩ : syracuseStep 1153955 = 1730933) B1730933
theorem B2595761 : Blo 1152637 2595761 := bstep (se 2 (by rfl) ⟨973410, by rfl⟩ : syracuseStep 2595761 = 1946821) B1946821
theorem B1153971 : Blo 1152637 1153971 := bstep (se 1 (by rfl) ⟨865478, by rfl⟩ : syracuseStep 1153971 = 1730957) B1730957
theorem B2595779 : Blo 1152637 2595779 := bstep (se 1 (by rfl) ⟨1946834, by rfl⟩ : syracuseStep 2595779 = 3893669) B3893669
theorem B1153987 : Blo 1152637 1153987 := bstep (se 1 (by rfl) ⟨865490, by rfl⟩ : syracuseStep 1153987 = 1730981) B1730981
theorem B1154003 : Blo 1152637 1154003 := bstep (se 1 (by rfl) ⟨865502, by rfl⟩ : syracuseStep 1154003 = 1731005) B1731005
theorem B1154019 : Blo 1152637 1154019 := bstep (se 1 (by rfl) ⟨865514, by rfl⟩ : syracuseStep 1154019 = 1731029) B1731029
theorem B1154035 : Blo 1152637 1154035 := bstep (se 1 (by rfl) ⟨865526, by rfl⟩ : syracuseStep 1154035 = 1731053) B1731053
theorem B1154051 : Blo 1152637 1154051 := bstep (se 1 (by rfl) ⟨865538, by rfl⟩ : syracuseStep 1154051 = 1731077) B1731077
theorem B2923523 : Blo 1152637 2923523 := bstep (se 1 (by rfl) ⟨2192642, by rfl⟩ : syracuseStep 2923523 = 4385285) B4385285
theorem B1154067 : Blo 1152637 1154067 := bstep (se 1 (by rfl) ⟨865550, by rfl⟩ : syracuseStep 1154067 = 1731101) B1731101
theorem B1154083 : Blo 1152637 1154083 := bstep (se 1 (by rfl) ⟨865562, by rfl⟩ : syracuseStep 1154083 = 1731125) B1731125
theorem B1154099 : Blo 1152637 1154099 := bstep (se 1 (by rfl) ⟨865574, by rfl⟩ : syracuseStep 1154099 = 1731149) B1731149
theorem B1154115 : Blo 1152637 1154115 := bstep (se 1 (by rfl) ⟨865586, by rfl⟩ : syracuseStep 1154115 = 1731173) B1731173
theorem B1154131 : Blo 1152637 1154131 := bstep (se 1 (by rfl) ⟨865598, by rfl⟩ : syracuseStep 1154131 = 1731197) B1731197
theorem B1154147 : Blo 1152637 1154147 := bstep (se 1 (by rfl) ⟨865610, by rfl⟩ : syracuseStep 1154147 = 1731221) B1731221
theorem B3284077 : Blo 1152637 3284077 := bstep (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) B1231529
theorem B1154163 : Blo 1152637 1154163 := bstep (se 1 (by rfl) ⟨865622, by rfl⟩ : syracuseStep 1154163 = 1731245) B1731245
theorem B1154179 : Blo 1152637 1154179 := bstep (se 1 (by rfl) ⟨865634, by rfl⟩ : syracuseStep 1154179 = 1731269) B1731269
theorem B1154195 : Blo 1152637 1154195 := bstep (se 1 (by rfl) ⟨865646, by rfl⟩ : syracuseStep 1154195 = 1731293) B1731293
theorem B1154211 : Blo 1152637 1154211 := bstep (se 1 (by rfl) ⟨865658, by rfl⟩ : syracuseStep 1154211 = 1731317) B1731317
theorem B1154227 : Blo 1152637 1154227 := bstep (se 1 (by rfl) ⟨865670, by rfl⟩ : syracuseStep 1154227 = 1731341) B1731341
theorem B1154243 : Blo 1152637 1154243 := bstep (se 1 (by rfl) ⟨865682, by rfl⟩ : syracuseStep 1154243 = 1731365) B1731365
theorem B2923715 : Blo 1152637 2923715 := bstep (se 1 (by rfl) ⟨2192786, by rfl⟩ : syracuseStep 2923715 = 4385573) B4385573
theorem B1645763 : Blo 1152637 1645763 := bstep (se 1 (by rfl) ⟨1234322, by rfl⟩ : syracuseStep 1645763 = 2468645) B2468645
theorem B2596049 : Blo 1152637 2596049 := bstep (se 2 (by rfl) ⟨973518, by rfl⟩ : syracuseStep 2596049 = 1947037) B1947037
theorem B1154259 : Blo 1152637 1154259 := bstep (se 1 (by rfl) ⟨865694, by rfl⟩ : syracuseStep 1154259 = 1731389) B1731389
theorem B5840099 : Blo 1152637 5840099 := bstep (se 1 (by rfl) ⟨4380074, by rfl⟩ : syracuseStep 5840099 = 8760149) B8760149
theorem B2596067 : Blo 1152637 2596067 := bstep (se 1 (by rfl) ⟨1947050, by rfl⟩ : syracuseStep 2596067 = 3894101) B3894101
theorem B1154275 : Blo 1152637 1154275 := bstep (se 1 (by rfl) ⟨865706, by rfl⟩ : syracuseStep 1154275 = 1731413) B1731413
theorem B1154291 : Blo 1152637 1154291 := bstep (se 1 (by rfl) ⟨865718, by rfl⟩ : syracuseStep 1154291 = 1731437) B1731437
theorem B1154307 : Blo 1152637 1154307 := bstep (se 1 (by rfl) ⟨865730, by rfl⟩ : syracuseStep 1154307 = 1731461) B1731461
theorem B3742993 : Blo 1152637 3742993 := bstep (se 2 (by rfl) ⟨1403622, by rfl⟩ : syracuseStep 3742993 = 2807245) B2807245
theorem B1154323 : Blo 1152637 1154323 := bstep (se 1 (by rfl) ⟨865742, by rfl⟩ : syracuseStep 1154323 = 1731485) B1731485
theorem B1154339 : Blo 1152637 1154339 := bstep (se 1 (by rfl) ⟨865754, by rfl⟩ : syracuseStep 1154339 = 1731509) B1731509
theorem B1154355 : Blo 1152637 1154355 := bstep (se 1 (by rfl) ⟨865766, by rfl⟩ : syracuseStep 1154355 = 1731533) B1731533
theorem B1154371 : Blo 1152637 1154371 := bstep (se 1 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 1154371 = 1731557) B1731557
theorem B1154387 : Blo 1152637 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B1154403 : Blo 1152637 1154403 := bstep (se 1 (by rfl) ⟨865802, by rfl⟩ : syracuseStep 1154403 = 1731605) B1731605
theorem B1154419 : Blo 1152637 1154419 := bstep (se 1 (by rfl) ⟨865814, by rfl⟩ : syracuseStep 1154419 = 1731629) B1731629
theorem B1154435 : Blo 1152637 1154435 := bstep (se 1 (by rfl) ⟨865826, by rfl⟩ : syracuseStep 1154435 = 1731653) B1731653
theorem B1154451 : Blo 1152637 1154451 := bstep (se 1 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 1154451 = 1731677) B1731677
theorem B1154467 : Blo 1152637 1154467 := bstep (se 1 (by rfl) ⟨865850, by rfl⟩ : syracuseStep 1154467 = 1731701) B1731701
theorem B1154483 : Blo 1152637 1154483 := bstep (se 1 (by rfl) ⟨865862, by rfl⟩ : syracuseStep 1154483 = 1731725) B1731725
theorem B1154499 : Blo 1152637 1154499 := bstep (se 1 (by rfl) ⟨865874, by rfl⟩ : syracuseStep 1154499 = 1731749) B1731749
theorem B1154515 : Blo 1152637 1154515 := bstep (se 1 (by rfl) ⟨865886, by rfl⟩ : syracuseStep 1154515 = 1731773) B1731773
theorem B1154531 : Blo 1152637 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B2596337 : Blo 1152637 2596337 := bstep (se 2 (by rfl) ⟨973626, by rfl⟩ : syracuseStep 2596337 = 1947253) B1947253
theorem B1154547 : Blo 1152637 1154547 := bstep (se 1 (by rfl) ⟨865910, by rfl⟩ : syracuseStep 1154547 = 1731821) B1731821
theorem B2596355 : Blo 1152637 2596355 := bstep (se 1 (by rfl) ⟨1947266, by rfl⟩ : syracuseStep 2596355 = 3894533) B3894533
theorem B1154563 : Blo 1152637 1154563 := bstep (se 1 (by rfl) ⟨865922, by rfl⟩ : syracuseStep 1154563 = 1731845) B1731845
theorem B1154579 : Blo 1152637 1154579 := bstep (se 1 (by rfl) ⟨865934, by rfl⟩ : syracuseStep 1154579 = 1731869) B1731869
theorem B1154595 : Blo 1152637 1154595 := bstep (se 1 (by rfl) ⟨865946, by rfl⟩ : syracuseStep 1154595 = 1731893) B1731893
theorem B1154611 : Blo 1152637 1154611 := bstep (se 1 (by rfl) ⟨865958, by rfl⟩ : syracuseStep 1154611 = 1731917) B1731917
theorem B1154627 : Blo 1152637 1154627 := bstep (se 1 (by rfl) ⟨865970, by rfl⟩ : syracuseStep 1154627 = 1731941) B1731941
theorem B1154643 : Blo 1152637 1154643 := bstep (se 1 (by rfl) ⟨865982, by rfl⟩ : syracuseStep 1154643 = 1731965) B1731965
theorem B1154659 : Blo 1152637 1154659 := bstep (se 1 (by rfl) ⟨865994, by rfl⟩ : syracuseStep 1154659 = 1731989) B1731989
theorem B3513955 : Blo 1152637 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B1154675 : Blo 1152637 1154675 := bstep (se 1 (by rfl) ⟨866006, by rfl⟩ : syracuseStep 1154675 = 1732013) B1732013
theorem B1154691 : Blo 1152637 1154691 := bstep (se 1 (by rfl) ⟨866018, by rfl⟩ : syracuseStep 1154691 = 1732037) B1732037
theorem B1154707 : Blo 1152637 1154707 := bstep (se 1 (by rfl) ⟨866030, by rfl⟩ : syracuseStep 1154707 = 1732061) B1732061
theorem B1154723 : Blo 1152637 1154723 := bstep (se 1 (by rfl) ⟨866042, by rfl⟩ : syracuseStep 1154723 = 1732085) B1732085
theorem B1154739 : Blo 1152637 1154739 := bstep (se 1 (by rfl) ⟨866054, by rfl⟩ : syracuseStep 1154739 = 1732109) B1732109
theorem B1154755 : Blo 1152637 1154755 := bstep (se 1 (by rfl) ⟨866066, by rfl⟩ : syracuseStep 1154755 = 1732133) B1732133
theorem B1154771 : Blo 1152637 1154771 := bstep (se 1 (by rfl) ⟨866078, by rfl⟩ : syracuseStep 1154771 = 1732157) B1732157
theorem B1154787 : Blo 1152637 1154787 := bstep (se 1 (by rfl) ⟨866090, by rfl⟩ : syracuseStep 1154787 = 1732181) B1732181
theorem B1318627 : Blo 1152637 1318627 := bstep (se 1 (by rfl) ⟨988970, by rfl⟩ : syracuseStep 1318627 = 1977941) B1977941
theorem B1154803 : Blo 1152637 1154803 := bstep (se 1 (by rfl) ⟨866102, by rfl⟩ : syracuseStep 1154803 = 1732205) B1732205
theorem B1154819 : Blo 1152637 1154819 := bstep (se 1 (by rfl) ⟨866114, by rfl⟩ : syracuseStep 1154819 = 1732229) B1732229
theorem B6233861 : Blo 1152637 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B2596625 : Blo 1152637 2596625 := bstep (se 2 (by rfl) ⟨973734, by rfl⟩ : syracuseStep 2596625 = 1947469) B1947469
theorem B1154835 : Blo 1152637 1154835 := bstep (se 1 (by rfl) ⟨866126, by rfl⟩ : syracuseStep 1154835 = 1732253) B1732253
theorem B2596643 : Blo 1152637 2596643 := bstep (se 1 (by rfl) ⟨1947482, by rfl⟩ : syracuseStep 2596643 = 3894965) B3894965
theorem B1154851 : Blo 1152637 1154851 := bstep (se 1 (by rfl) ⟨866138, by rfl⟩ : syracuseStep 1154851 = 1732277) B1732277
theorem B1154867 : Blo 1152637 1154867 := bstep (se 1 (by rfl) ⟨866150, by rfl⟩ : syracuseStep 1154867 = 1732301) B1732301
theorem B1646401 : Blo 1152637 1646401 := bstep (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) B1234801
theorem B1154883 : Blo 1152637 1154883 := bstep (se 1 (by rfl) ⟨866162, by rfl⟩ : syracuseStep 1154883 = 1732325) B1732325
theorem B1154899 : Blo 1152637 1154899 := bstep (se 1 (by rfl) ⟨866174, by rfl⟩ : syracuseStep 1154899 = 1732349) B1732349
theorem B1154915 : Blo 1152637 1154915 := bstep (se 1 (by rfl) ⟨866186, by rfl⟩ : syracuseStep 1154915 = 1732373) B1732373
theorem B15179633 : Blo 1152637 15179633 := bstep (se 2 (by rfl) ⟨5692362, by rfl⟩ : syracuseStep 15179633 = 11384725) B11384725
theorem B1154931 : Blo 1152637 1154931 := bstep (se 1 (by rfl) ⟨866198, by rfl⟩ : syracuseStep 1154931 = 1732397) B1732397
theorem B1154947 : Blo 1152637 1154947 := bstep (se 1 (by rfl) ⟨866210, by rfl⟩ : syracuseStep 1154947 = 1732421) B1732421
theorem B1154963 : Blo 1152637 1154963 := bstep (se 1 (by rfl) ⟨866222, by rfl⟩ : syracuseStep 1154963 = 1732445) B1732445
theorem B1154979 : Blo 1152637 1154979 := bstep (se 1 (by rfl) ⟨866234, by rfl⟩ : syracuseStep 1154979 = 1732469) B1732469
theorem B1154995 : Blo 1152637 1154995 := bstep (se 1 (by rfl) ⟨866246, by rfl⟩ : syracuseStep 1154995 = 1732493) B1732493
theorem B1646515 : Blo 1152637 1646515 := bstep (se 1 (by rfl) ⟨1234886, by rfl⟩ : syracuseStep 1646515 = 2469773) B2469773
theorem B1155011 : Blo 1152637 1155011 := bstep (se 1 (by rfl) ⟨866258, by rfl⟩ : syracuseStep 1155011 = 1732517) B1732517
theorem B1155027 : Blo 1152637 1155027 := bstep (se 1 (by rfl) ⟨866270, by rfl⟩ : syracuseStep 1155027 = 1732541) B1732541
theorem B1155043 : Blo 1152637 1155043 := bstep (se 1 (by rfl) ⟨866282, by rfl⟩ : syracuseStep 1155043 = 1732565) B1732565
theorem B8757233 : Blo 1152637 8757233 := bstep (se 2 (by rfl) ⟨3283962, by rfl⟩ : syracuseStep 8757233 = 6567925) B6567925
theorem B1155059 : Blo 1152637 1155059 := bstep (se 1 (by rfl) ⟨866294, by rfl⟩ : syracuseStep 1155059 = 1732589) B1732589
theorem B1155075 : Blo 1152637 1155075 := bstep (se 1 (by rfl) ⟨866306, by rfl⟩ : syracuseStep 1155075 = 1732613) B1732613
theorem B5840909 : Blo 1152637 5840909 := bstep (se 3 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 5840909 = 2190341) B2190341
theorem B1155091 : Blo 1152637 1155091 := bstep (se 1 (by rfl) ⟨866318, by rfl⟩ : syracuseStep 1155091 = 1732637) B1732637
theorem B1155107 : Blo 1152637 1155107 := bstep (se 1 (by rfl) ⟨866330, by rfl⟩ : syracuseStep 1155107 = 1732661) B1732661
theorem B2596913 : Blo 1152637 2596913 := bstep (se 2 (by rfl) ⟨973842, by rfl⟩ : syracuseStep 2596913 = 1947685) B1947685
theorem B1155123 : Blo 1152637 1155123 := bstep (se 1 (by rfl) ⟨866342, by rfl⟩ : syracuseStep 1155123 = 1732685) B1732685
theorem B2596931 : Blo 1152637 2596931 := bstep (se 1 (by rfl) ⟨1947698, by rfl⟩ : syracuseStep 2596931 = 3895397) B3895397
theorem B1155139 : Blo 1152637 1155139 := bstep (se 1 (by rfl) ⟨866354, by rfl⟩ : syracuseStep 1155139 = 1732709) B1732709
theorem B1155155 : Blo 1152637 1155155 := bstep (se 1 (by rfl) ⟨866366, by rfl⟩ : syracuseStep 1155155 = 1732733) B1732733
theorem B1155171 : Blo 1152637 1155171 := bstep (se 1 (by rfl) ⟨866378, by rfl⟩ : syracuseStep 1155171 = 1732757) B1732757
theorem B3121265 : Blo 1152637 3121265 := bstep (se 2 (by rfl) ⟨1170474, by rfl⟩ : syracuseStep 3121265 = 2340949) B2340949
theorem B2924657 : Blo 1152637 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1155187 : Blo 1152637 1155187 := bstep (se 1 (by rfl) ⟨866390, by rfl⟩ : syracuseStep 1155187 = 1732781) B1732781
theorem B1155203 : Blo 1152637 1155203 := bstep (se 1 (by rfl) ⟨866402, by rfl⟩ : syracuseStep 1155203 = 1732805) B1732805
theorem B3285137 : Blo 1152637 3285137 := bstep (se 2 (by rfl) ⟨1231926, by rfl⟩ : syracuseStep 3285137 = 2463853) B2463853
theorem B1155219 : Blo 1152637 1155219 := bstep (se 1 (by rfl) ⟨866414, by rfl⟩ : syracuseStep 1155219 = 1732829) B1732829
theorem B1155235 : Blo 1152637 1155235 := bstep (se 1 (by rfl) ⟨866426, by rfl⟩ : syracuseStep 1155235 = 1732853) B1732853
theorem B2924707 : Blo 1152637 2924707 := bstep (se 1 (by rfl) ⟨2193530, by rfl⟩ : syracuseStep 2924707 = 4387061) B4387061
theorem B1155251 : Blo 1152637 1155251 := bstep (se 1 (by rfl) ⟨866438, by rfl⟩ : syracuseStep 1155251 = 1732877) B1732877
theorem B1155267 : Blo 1152637 1155267 := bstep (se 1 (by rfl) ⟨866450, by rfl⟩ : syracuseStep 1155267 = 1732901) B1732901
theorem B1155283 : Blo 1152637 1155283 := bstep (se 1 (by rfl) ⟨866462, by rfl⟩ : syracuseStep 1155283 = 1732925) B1732925
theorem B1155299 : Blo 1152637 1155299 := bstep (se 1 (by rfl) ⟨866474, by rfl⟩ : syracuseStep 1155299 = 1732949) B1732949
theorem B5546225 : Blo 1152637 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B1155315 : Blo 1152637 1155315 := bstep (se 1 (by rfl) ⟨866486, by rfl⟩ : syracuseStep 1155315 = 1732973) B1732973
theorem B1155331 : Blo 1152637 1155331 := bstep (se 1 (by rfl) ⟨866498, by rfl⟩ : syracuseStep 1155331 = 1732997) B1732997
theorem B2466065 : Blo 1152637 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B1155347 : Blo 1152637 1155347 := bstep (se 1 (by rfl) ⟨866510, by rfl⟩ : syracuseStep 1155347 = 1733021) B1733021
theorem B1155363 : Blo 1152637 1155363 := bstep (se 1 (by rfl) ⟨866522, by rfl⟩ : syracuseStep 1155363 = 1733045) B1733045
theorem B2924849 : Blo 1152637 2924849 := bstep (se 2 (by rfl) ⟨1096818, by rfl⟩ : syracuseStep 2924849 = 2193637) B2193637
theorem B1155379 : Blo 1152637 1155379 := bstep (se 1 (by rfl) ⟨866534, by rfl⟩ : syracuseStep 1155379 = 1733069) B1733069
theorem B1155395 : Blo 1152637 1155395 := bstep (se 1 (by rfl) ⟨866546, by rfl⟩ : syracuseStep 1155395 = 1733093) B1733093
theorem B2597201 : Blo 1152637 2597201 := bstep (se 2 (by rfl) ⟨973950, by rfl⟩ : syracuseStep 2597201 = 1947901) B1947901
theorem B1155411 : Blo 1152637 1155411 := bstep (se 1 (by rfl) ⟨866558, by rfl⟩ : syracuseStep 1155411 = 1733117) B1733117
theorem B2597219 : Blo 1152637 2597219 := bstep (se 1 (by rfl) ⟨1947914, by rfl⟩ : syracuseStep 2597219 = 3895829) B3895829
theorem B1155427 : Blo 1152637 1155427 := bstep (se 1 (by rfl) ⟨866570, by rfl⟩ : syracuseStep 1155427 = 1733141) B1733141
theorem B3121517 : Blo 1152637 3121517 := bstep (se 3 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 3121517 = 1170569) B1170569
theorem B1155443 : Blo 1152637 1155443 := bstep (se 1 (by rfl) ⟨866582, by rfl⟩ : syracuseStep 1155443 = 1733165) B1733165
theorem B1155459 : Blo 1152637 1155459 := bstep (se 1 (by rfl) ⟨866594, by rfl⟩ : syracuseStep 1155459 = 1733189) B1733189
theorem B1155475 : Blo 1152637 1155475 := bstep (se 1 (by rfl) ⟨866606, by rfl⟩ : syracuseStep 1155475 = 1733213) B1733213
theorem B1155491 : Blo 1152637 1155491 := bstep (se 1 (by rfl) ⟨866618, by rfl⟩ : syracuseStep 1155491 = 1733237) B1733237
theorem B1155507 : Blo 1152637 1155507 := bstep (se 1 (by rfl) ⟨866630, by rfl⟩ : syracuseStep 1155507 = 1733261) B1733261
theorem B1155523 : Blo 1152637 1155523 := bstep (se 1 (by rfl) ⟨866642, by rfl⟩ : syracuseStep 1155523 = 1733285) B1733285
theorem B1155539 : Blo 1152637 1155539 := bstep (se 1 (by rfl) ⟨866654, by rfl⟩ : syracuseStep 1155539 = 1733309) B1733309
theorem B1155555 : Blo 1152637 1155555 := bstep (se 1 (by rfl) ⟨866666, by rfl⟩ : syracuseStep 1155555 = 1733333) B1733333
theorem B1155571 : Blo 1152637 1155571 := bstep (se 1 (by rfl) ⟨866678, by rfl⟩ : syracuseStep 1155571 = 1733357) B1733357
theorem B1155587 : Blo 1152637 1155587 := bstep (se 1 (by rfl) ⟨866690, by rfl⟩ : syracuseStep 1155587 = 1733381) B1733381
theorem B1155603 : Blo 1152637 1155603 := bstep (se 1 (by rfl) ⟨866702, by rfl⟩ : syracuseStep 1155603 = 1733405) B1733405
theorem B6234659 : Blo 1152637 6234659 := bstep (se 1 (by rfl) ⟨4675994, by rfl⟩ : syracuseStep 6234659 = 9351989) B9351989
theorem B3121699 : Blo 1152637 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B1155619 : Blo 1152637 1155619 := bstep (se 1 (by rfl) ⟨866714, by rfl⟩ : syracuseStep 1155619 = 1733429) B1733429
theorem B1581619 : Blo 1152637 1581619 := bstep (se 1 (by rfl) ⟨1186214, by rfl⟩ : syracuseStep 1581619 = 2372429) B2372429
theorem B1155635 : Blo 1152637 1155635 := bstep (se 1 (by rfl) ⟨866726, by rfl⟩ : syracuseStep 1155635 = 1733453) B1733453
theorem B1155651 : Blo 1152637 1155651 := bstep (se 1 (by rfl) ⟨866738, by rfl⟩ : syracuseStep 1155651 = 1733477) B1733477
theorem B1155667 : Blo 1152637 1155667 := bstep (se 1 (by rfl) ⟨866750, by rfl⟩ : syracuseStep 1155667 = 1733501) B1733501
theorem B1155683 : Blo 1152637 1155683 := bstep (se 1 (by rfl) ⟨866762, by rfl⟩ : syracuseStep 1155683 = 1733525) B1733525
theorem B5546609 : Blo 1152637 5546609 := bstep (se 2 (by rfl) ⟨2079978, by rfl⟩ : syracuseStep 5546609 = 4159957) B4159957
theorem B2597489 : Blo 1152637 2597489 := bstep (se 2 (by rfl) ⟨974058, by rfl⟩ : syracuseStep 2597489 = 1948117) B1948117
theorem B1155699 : Blo 1152637 1155699 := bstep (se 1 (by rfl) ⟨866774, by rfl⟩ : syracuseStep 1155699 = 1733549) B1733549
theorem B2597507 : Blo 1152637 2597507 := bstep (se 1 (by rfl) ⟨1948130, by rfl⟩ : syracuseStep 2597507 = 3896261) B3896261
theorem B1155715 : Blo 1152637 1155715 := bstep (se 1 (by rfl) ⟨866786, by rfl⟩ : syracuseStep 1155715 = 1733573) B1733573
theorem B1155731 : Blo 1152637 1155731 := bstep (se 1 (by rfl) ⟨866798, by rfl⟩ : syracuseStep 1155731 = 1733597) B1733597
theorem B1155747 : Blo 1152637 1155747 := bstep (se 1 (by rfl) ⟨866810, by rfl⟩ : syracuseStep 1155747 = 1733621) B1733621
theorem B1155763 : Blo 1152637 1155763 := bstep (se 1 (by rfl) ⟨866822, by rfl⟩ : syracuseStep 1155763 = 1733645) B1733645
theorem B1155779 : Blo 1152637 1155779 := bstep (se 1 (by rfl) ⟨866834, by rfl⟩ : syracuseStep 1155779 = 1733669) B1733669
theorem B1155795 : Blo 1152637 1155795 := bstep (se 1 (by rfl) ⟨866846, by rfl⟩ : syracuseStep 1155795 = 1733693) B1733693
theorem B1155811 : Blo 1152637 1155811 := bstep (se 1 (by rfl) ⟨866858, by rfl⟩ : syracuseStep 1155811 = 1733717) B1733717
theorem B1155827 : Blo 1152637 1155827 := bstep (se 1 (by rfl) ⟨866870, by rfl⟩ : syracuseStep 1155827 = 1733741) B1733741
theorem B1155843 : Blo 1152637 1155843 := bstep (se 1 (by rfl) ⟨866882, by rfl⟩ : syracuseStep 1155843 = 1733765) B1733765
theorem B1155859 : Blo 1152637 1155859 := bstep (se 1 (by rfl) ⟨866894, by rfl⟩ : syracuseStep 1155859 = 1733789) B1733789
theorem B1155875 : Blo 1152637 1155875 := bstep (se 1 (by rfl) ⟨866906, by rfl⟩ : syracuseStep 1155875 = 1733813) B1733813
theorem B3285809 : Blo 1152637 3285809 := bstep (se 2 (by rfl) ⟨1232178, by rfl⟩ : syracuseStep 3285809 = 2464357) B2464357
theorem B1155891 : Blo 1152637 1155891 := bstep (se 1 (by rfl) ⟨866918, by rfl⟩ : syracuseStep 1155891 = 1733837) B1733837
theorem B1155907 : Blo 1152637 1155907 := bstep (se 1 (by rfl) ⟨866930, by rfl⟩ : syracuseStep 1155907 = 1733861) B1733861
theorem B1155923 : Blo 1152637 1155923 := bstep (se 1 (by rfl) ⟨866942, by rfl⟩ : syracuseStep 1155923 = 1733885) B1733885
theorem B1155939 : Blo 1152637 1155939 := bstep (se 1 (by rfl) ⟨866954, by rfl⟩ : syracuseStep 1155939 = 1733909) B1733909
theorem B1155955 : Blo 1152637 1155955 := bstep (se 1 (by rfl) ⟨866966, by rfl⟩ : syracuseStep 1155955 = 1733933) B1733933
theorem B1155971 : Blo 1152637 1155971 := bstep (se 1 (by rfl) ⟨866978, by rfl⟩ : syracuseStep 1155971 = 1733957) B1733957
theorem B12493709 : Blo 1152637 12493709 := bstep (se 3 (by rfl) ⟨2342570, by rfl⟩ : syracuseStep 12493709 = 4685141) B4685141
theorem B2597777 : Blo 1152637 2597777 := bstep (se 2 (by rfl) ⟨974166, by rfl⟩ : syracuseStep 2597777 = 1948333) B1948333
theorem B1155987 : Blo 1152637 1155987 := bstep (se 1 (by rfl) ⟨866990, by rfl⟩ : syracuseStep 1155987 = 1733981) B1733981
theorem B2597795 : Blo 1152637 2597795 := bstep (se 1 (by rfl) ⟨1948346, by rfl⟩ : syracuseStep 2597795 = 3896693) B3896693
theorem B1156003 : Blo 1152637 1156003 := bstep (se 1 (by rfl) ⟨867002, by rfl⟩ : syracuseStep 1156003 = 1734005) B1734005
theorem B1156019 : Blo 1152637 1156019 := bstep (se 1 (by rfl) ⟨867014, by rfl⟩ : syracuseStep 1156019 = 1734029) B1734029
theorem B1156035 : Blo 1152637 1156035 := bstep (se 1 (by rfl) ⟨867026, by rfl⟩ : syracuseStep 1156035 = 1734053) B1734053
theorem B1156051 : Blo 1152637 1156051 := bstep (se 1 (by rfl) ⟨867038, by rfl⟩ : syracuseStep 1156051 = 1734077) B1734077
theorem B1156067 : Blo 1152637 1156067 := bstep (se 1 (by rfl) ⟨867050, by rfl⟩ : syracuseStep 1156067 = 1734101) B1734101
theorem B1156083 : Blo 1152637 1156083 := bstep (se 1 (by rfl) ⟨867062, by rfl⟩ : syracuseStep 1156083 = 1734125) B1734125
theorem B1156099 : Blo 1152637 1156099 := bstep (se 1 (by rfl) ⟨867074, by rfl⟩ : syracuseStep 1156099 = 1734149) B1734149
theorem B1156115 : Blo 1152637 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B1156131 : Blo 1152637 1156131 := bstep (se 1 (by rfl) ⟨867098, by rfl⟩ : syracuseStep 1156131 = 1734197) B1734197
theorem B1156147 : Blo 1152637 1156147 := bstep (se 1 (by rfl) ⟨867110, by rfl⟩ : syracuseStep 1156147 = 1734221) B1734221
theorem B1156163 : Blo 1152637 1156163 := bstep (se 1 (by rfl) ⟨867122, by rfl⟩ : syracuseStep 1156163 = 1734245) B1734245
theorem B1156179 : Blo 1152637 1156179 := bstep (se 1 (by rfl) ⟨867134, by rfl⟩ : syracuseStep 1156179 = 1734269) B1734269
theorem B1156195 : Blo 1152637 1156195 := bstep (se 1 (by rfl) ⟨867146, by rfl⟩ : syracuseStep 1156195 = 1734293) B1734293
theorem B2466929 : Blo 1152637 2466929 := bstep (se 2 (by rfl) ⟨925098, by rfl⟩ : syracuseStep 2466929 = 1850197) B1850197
theorem B1156211 : Blo 1152637 1156211 := bstep (se 1 (by rfl) ⟨867158, by rfl⟩ : syracuseStep 1156211 = 1734317) B1734317
theorem B1156227 : Blo 1152637 1156227 := bstep (se 1 (by rfl) ⟨867170, by rfl⟩ : syracuseStep 1156227 = 1734341) B1734341
theorem B5547149 : Blo 1152637 5547149 := bstep (se 3 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 5547149 = 2080181) B2080181
theorem B1156243 : Blo 1152637 1156243 := bstep (se 1 (by rfl) ⟨867182, by rfl⟩ : syracuseStep 1156243 = 1734365) B1734365
theorem B1156259 : Blo 1152637 1156259 := bstep (se 1 (by rfl) ⟨867194, by rfl⟩ : syracuseStep 1156259 = 1734389) B1734389
theorem B2598065 : Blo 1152637 2598065 := bstep (se 2 (by rfl) ⟨974274, by rfl⟩ : syracuseStep 2598065 = 1948549) B1948549
theorem B1156275 : Blo 1152637 1156275 := bstep (se 1 (by rfl) ⟨867206, by rfl⟩ : syracuseStep 1156275 = 1734413) B1734413
theorem B2598083 : Blo 1152637 2598083 := bstep (se 1 (by rfl) ⟨1948562, by rfl⟩ : syracuseStep 2598083 = 3897125) B3897125
theorem B1156291 : Blo 1152637 1156291 := bstep (se 1 (by rfl) ⟨867218, by rfl⟩ : syracuseStep 1156291 = 1734437) B1734437
theorem B1156307 : Blo 1152637 1156307 := bstep (se 1 (by rfl) ⟨867230, by rfl⟩ : syracuseStep 1156307 = 1734461) B1734461
theorem B1156323 : Blo 1152637 1156323 := bstep (se 1 (by rfl) ⟨867242, by rfl⟩ : syracuseStep 1156323 = 1734485) B1734485
theorem B1156339 : Blo 1152637 1156339 := bstep (se 1 (by rfl) ⟨867254, by rfl⟩ : syracuseStep 1156339 = 1734509) B1734509
theorem B1156355 : Blo 1152637 1156355 := bstep (se 1 (by rfl) ⟨867266, by rfl⟩ : syracuseStep 1156355 = 1734533) B1734533
theorem B2925841 : Blo 1152637 2925841 := bstep (se 2 (by rfl) ⟨1097190, by rfl⟩ : syracuseStep 2925841 = 2194381) B2194381
theorem B1156371 : Blo 1152637 1156371 := bstep (se 1 (by rfl) ⟨867278, by rfl⟩ : syracuseStep 1156371 = 1734557) B1734557
theorem B1156387 : Blo 1152637 1156387 := bstep (se 1 (by rfl) ⟨867290, by rfl⟩ : syracuseStep 1156387 = 1734581) B1734581
theorem B1156403 : Blo 1152637 1156403 := bstep (se 1 (by rfl) ⟨867302, by rfl⟩ : syracuseStep 1156403 = 1734605) B1734605
theorem B1156419 : Blo 1152637 1156419 := bstep (se 1 (by rfl) ⟨867314, by rfl⟩ : syracuseStep 1156419 = 1734629) B1734629
theorem B1156435 : Blo 1152637 1156435 := bstep (se 1 (by rfl) ⟨867326, by rfl⟩ : syracuseStep 1156435 = 1734653) B1734653
theorem B1156451 : Blo 1152637 1156451 := bstep (se 1 (by rfl) ⟨867338, by rfl⟩ : syracuseStep 1156451 = 1734677) B1734677
theorem B1156467 : Blo 1152637 1156467 := bstep (se 1 (by rfl) ⟨867350, by rfl⟩ : syracuseStep 1156467 = 1734701) B1734701
theorem B3122563 : Blo 1152637 3122563 := bstep (se 1 (by rfl) ⟨2341922, by rfl⟩ : syracuseStep 3122563 = 4683845) B4683845
theorem B1156483 : Blo 1152637 1156483 := bstep (se 1 (by rfl) ⟨867362, by rfl⟩ : syracuseStep 1156483 = 1734725) B1734725
theorem B1156499 : Blo 1152637 1156499 := bstep (se 1 (by rfl) ⟨867374, by rfl⟩ : syracuseStep 1156499 = 1734749) B1734749
theorem B1156515 : Blo 1152637 1156515 := bstep (se 1 (by rfl) ⟨867386, by rfl⟩ : syracuseStep 1156515 = 1734773) B1734773
theorem B1156531 : Blo 1152637 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B1156547 : Blo 1152637 1156547 := bstep (se 1 (by rfl) ⟨867410, by rfl⟩ : syracuseStep 1156547 = 1734821) B1734821
theorem B2598353 : Blo 1152637 2598353 := bstep (se 2 (by rfl) ⟨974382, by rfl⟩ : syracuseStep 2598353 = 1948765) B1948765
theorem B1156563 : Blo 1152637 1156563 := bstep (se 1 (by rfl) ⟨867422, by rfl⟩ : syracuseStep 1156563 = 1734845) B1734845
theorem B2598371 : Blo 1152637 2598371 := bstep (se 1 (by rfl) ⟨1948778, by rfl⟩ : syracuseStep 2598371 = 3897557) B3897557
theorem B1156579 : Blo 1152637 1156579 := bstep (se 1 (by rfl) ⟨867434, by rfl⟩ : syracuseStep 1156579 = 1734869) B1734869
theorem B1156595 : Blo 1152637 1156595 := bstep (se 1 (by rfl) ⟨867446, by rfl⟩ : syracuseStep 1156595 = 1734893) B1734893
theorem B1156611 : Blo 1152637 1156611 := bstep (se 1 (by rfl) ⟨867458, by rfl⟩ : syracuseStep 1156611 = 1734917) B1734917
theorem B1156627 : Blo 1152637 1156627 := bstep (se 1 (by rfl) ⟨867470, by rfl⟩ : syracuseStep 1156627 = 1734941) B1734941
theorem B2926115 : Blo 1152637 2926115 := bstep (se 1 (by rfl) ⟨2194586, by rfl⟩ : syracuseStep 2926115 = 4389173) B4389173
theorem B3286595 : Blo 1152637 3286595 := bstep (se 1 (by rfl) ⟨2464946, by rfl⟩ : syracuseStep 3286595 = 4929893) B4929893
theorem B2500241 : Blo 1152637 2500241 := bstep (se 2 (by rfl) ⟨937590, by rfl⟩ : syracuseStep 2500241 = 1875181) B1875181
theorem B2926307 : Blo 1152637 2926307 := bstep (se 1 (by rfl) ⟨2194730, by rfl⟩ : syracuseStep 2926307 = 4389461) B4389461
theorem B2598641 : Blo 1152637 2598641 := bstep (se 2 (by rfl) ⟨974490, by rfl⟩ : syracuseStep 2598641 = 1948981) B1948981
theorem B2598659 : Blo 1152637 2598659 := bstep (se 1 (by rfl) ⟨1948994, by rfl⟩ : syracuseStep 2598659 = 3897989) B3897989
theorem B4925261 : Blo 1152637 4925261 := bstep (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) B1846973
theorem B3286925 : Blo 1152637 3286925 := bstep (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) B1232597
theorem B3286993 : Blo 1152637 3286993 := bstep (se 2 (by rfl) ⟨1232622, by rfl⟩ : syracuseStep 3286993 = 2465245) B2465245
theorem B1386499 : Blo 1152637 1386499 := bstep (se 1 (by rfl) ⟨1039874, by rfl⟩ : syracuseStep 1386499 = 2079749) B2079749
theorem B2598929 : Blo 1152637 2598929 := bstep (se 2 (by rfl) ⟨974598, by rfl⟩ : syracuseStep 2598929 = 1949197) B1949197
theorem B2598947 : Blo 1152637 2598947 := bstep (se 1 (by rfl) ⟨1949210, by rfl⟩ : syracuseStep 2598947 = 3898421) B3898421
theorem B4925603 : Blo 1152637 4925603 := bstep (se 1 (by rfl) ⟨3694202, by rfl⟩ : syracuseStep 4925603 = 7388405) B7388405
theorem B3287267 : Blo 1152637 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B5548301 : Blo 1152637 5548301 := bstep (se 3 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 5548301 = 2080613) B2080613
theorem B2599217 : Blo 1152637 2599217 := bstep (se 2 (by rfl) ⟨974706, by rfl⟩ : syracuseStep 2599217 = 1949413) B1949413
theorem B1976627 : Blo 1152637 1976627 := bstep (se 1 (by rfl) ⟨1482470, by rfl⟩ : syracuseStep 1976627 = 2964941) B2964941
theorem B2599235 : Blo 1152637 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B1386883 : Blo 1152637 1386883 := bstep (se 1 (by rfl) ⟨1040162, by rfl⟩ : syracuseStep 1386883 = 2080325) B2080325
theorem B2468227 : Blo 1152637 2468227 := bstep (se 1 (by rfl) ⟨1851170, by rfl⟩ : syracuseStep 2468227 = 3702341) B3702341
theorem B1976737 : Blo 1152637 1976737 := bstep (se 2 (by rfl) ⟨741276, by rfl⟩ : syracuseStep 1976737 = 1482553) B1482553
theorem B44444213 : Blo 1152637 44444213 := bstep (se 5 (by rfl) ⟨2083322, by rfl⟩ : syracuseStep 44444213 = 4166645) B4166645
theorem B2599505 : Blo 1152637 2599505 := bstep (se 2 (by rfl) ⟨974814, by rfl⟩ : syracuseStep 2599505 = 1949629) B1949629
theorem B2599523 : Blo 1152637 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B2927249 : Blo 1152637 2927249 := bstep (se 2 (by rfl) ⟨1097718, by rfl⟩ : syracuseStep 2927249 = 2195437) B2195437
theorem B2927299 : Blo 1152637 2927299 := bstep (se 1 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 2927299 = 4390949) B4390949
theorem B2927441 : Blo 1152637 2927441 := bstep (se 2 (by rfl) ⟨1097790, by rfl⟩ : syracuseStep 2927441 = 2195581) B2195581
theorem B5843825 : Blo 1152637 5843825 := bstep (se 2 (by rfl) ⟨2191434, by rfl⟩ : syracuseStep 5843825 = 4382869) B4382869
theorem B2599793 : Blo 1152637 2599793 := bstep (se 2 (by rfl) ⟨974922, by rfl⟩ : syracuseStep 2599793 = 1949845) B1949845
theorem B2501489 : Blo 1152637 2501489 := bstep (se 2 (by rfl) ⟨938058, by rfl⟩ : syracuseStep 2501489 = 1876117) B1876117
theorem B1977203 : Blo 1152637 1977203 := bstep (se 1 (by rfl) ⟨1482902, by rfl⟩ : syracuseStep 1977203 = 2965805) B2965805
theorem B2599811 : Blo 1152637 2599811 := bstep (se 1 (by rfl) ⟨1949858, by rfl⟩ : syracuseStep 2599811 = 3899717) B3899717
theorem B5549069 : Blo 1152637 5549069 := bstep (se 3 (by rfl) ⟨1040450, by rfl⟩ : syracuseStep 5549069 = 2080901) B2080901
theorem B3288109 : Blo 1152637 3288109 := bstep (se 3 (by rfl) ⟨616520, by rfl⟩ : syracuseStep 3288109 = 1233041) B1233041
theorem B2600081 : Blo 1152637 2600081 := bstep (se 2 (by rfl) ⟨975030, by rfl⟩ : syracuseStep 2600081 = 1950061) B1950061
theorem B3124369 : Blo 1152637 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B2600099 : Blo 1152637 2600099 := bstep (se 1 (by rfl) ⟨1950074, by rfl⟩ : syracuseStep 2600099 = 3900149) B3900149
theorem B3288269 : Blo 1152637 3288269 := bstep (se 3 (by rfl) ⟨616550, by rfl⟩ : syracuseStep 3288269 = 1233101) B1233101
theorem B3288451 : Blo 1152637 3288451 := bstep (se 1 (by rfl) ⟨2466338, by rfl⟩ : syracuseStep 3288451 = 4932677) B4932677
theorem B6565283 : Blo 1152637 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B2600369 : Blo 1152637 2600369 := bstep (se 2 (by rfl) ⟨975138, by rfl⟩ : syracuseStep 2600369 = 1950277) B1950277
theorem B2600387 : Blo 1152637 2600387 := bstep (se 1 (by rfl) ⟨1950290, by rfl⟩ : syracuseStep 2600387 = 3900581) B3900581
theorem B1846819 : Blo 1152637 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B2469457 : Blo 1152637 2469457 := bstep (se 2 (by rfl) ⟨926046, by rfl⟩ : syracuseStep 2469457 = 1852093) B1852093
theorem B1945201 : Blo 1152637 1945201 := bstep (se 2 (by rfl) ⟨729450, by rfl⟩ : syracuseStep 1945201 = 1458901) B1458901
theorem B1945235 : Blo 1152637 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B2600657 : Blo 1152637 2600657 := bstep (se 2 (by rfl) ⟨975246, by rfl⟩ : syracuseStep 2600657 = 1950493) B1950493
theorem B2600675 : Blo 1152637 2600675 := bstep (se 1 (by rfl) ⟨1950506, by rfl⟩ : syracuseStep 2600675 = 3901013) B3901013
theorem B1945363 : Blo 1152637 1945363 := bstep (se 1 (by rfl) ⟨1459022, by rfl⟩ : syracuseStep 1945363 = 2918045) B2918045
theorem B1945505 : Blo 1152637 1945505 := bstep (se 2 (by rfl) ⟨729564, by rfl⟩ : syracuseStep 1945505 = 1459129) B1459129
theorem B1847281 : Blo 1152637 1847281 := bstep (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) B1385461
theorem B2600945 : Blo 1152637 2600945 := bstep (se 2 (by rfl) ⟨975354, by rfl⟩ : syracuseStep 2600945 = 1950709) B1950709
theorem B2600963 : Blo 1152637 2600963 := bstep (se 1 (by rfl) ⟨1950722, by rfl⟩ : syracuseStep 2600963 = 3901445) B3901445
theorem B1945633 : Blo 1152637 1945633 := bstep (se 2 (by rfl) ⟨729612, by rfl⟩ : syracuseStep 1945633 = 1459225) B1459225
theorem B1945667 : Blo 1152637 1945667 := bstep (se 1 (by rfl) ⟨1459250, by rfl⟩ : syracuseStep 1945667 = 2918501) B2918501
theorem B1847377 : Blo 1152637 1847377 := bstep (se 2 (by rfl) ⟨692766, by rfl⟩ : syracuseStep 1847377 = 1385533) B1385533
theorem B1945795 : Blo 1152637 1945795 := bstep (se 1 (by rfl) ⟨1459346, by rfl⟩ : syracuseStep 1945795 = 2918693) B2918693
theorem B2470115 : Blo 1152637 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B1847537 : Blo 1152637 1847537 := bstep (se 2 (by rfl) ⟨692826, by rfl⟩ : syracuseStep 1847537 = 1385653) B1385653
theorem B2601233 : Blo 1152637 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B5845283 : Blo 1152637 5845283 := bstep (se 1 (by rfl) ⟨4383962, by rfl⟩ : syracuseStep 5845283 = 8767925) B8767925
theorem B2601251 : Blo 1152637 2601251 := bstep (se 1 (by rfl) ⟨1950938, by rfl⟩ : syracuseStep 2601251 = 3901877) B3901877
theorem B3944771 : Blo 1152637 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B1945937 : Blo 1152637 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B6566285 : Blo 1152637 6566285 := bstep (se 3 (by rfl) ⟨1231178, by rfl⟩ : syracuseStep 6566285 = 2462357) B2462357
theorem B1946065 : Blo 1152637 1946065 := bstep (se 2 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 1946065 = 1459549) B1459549
theorem B1946099 : Blo 1152637 1946099 := bstep (se 1 (by rfl) ⟨1459574, by rfl⟩ : syracuseStep 1946099 = 2919149) B2919149
theorem B7909901 : Blo 1152637 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B2601521 : Blo 1152637 2601521 := bstep (se 2 (by rfl) ⟨975570, by rfl⟩ : syracuseStep 2601521 = 1951141) B1951141
theorem B2601539 : Blo 1152637 2601539 := bstep (se 1 (by rfl) ⟨1951154, by rfl⟩ : syracuseStep 2601539 = 3902309) B3902309
theorem B2077283 : Blo 1152637 2077283 := bstep (se 1 (by rfl) ⟨1557962, by rfl⟩ : syracuseStep 2077283 = 3115925) B3115925
theorem B3125873 : Blo 1152637 3125873 := bstep (se 2 (by rfl) ⟨1172202, by rfl⟩ : syracuseStep 3125873 = 2344405) B2344405
theorem B1946227 : Blo 1152637 1946227 := bstep (se 1 (by rfl) ⟨1459670, by rfl⟩ : syracuseStep 1946227 = 2919341) B2919341
theorem B7385741 : Blo 1152637 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B2634481 : Blo 1152637 2634481 := bstep (se 2 (by rfl) ⟨987930, by rfl⟩ : syracuseStep 2634481 = 1975861) B1975861
theorem B3289841 : Blo 1152637 3289841 := bstep (se 2 (by rfl) ⟨1233690, by rfl⟩ : syracuseStep 3289841 = 2467381) B2467381
theorem B1946369 : Blo 1152637 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B44970773 : Blo 1152637 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B2601809 : Blo 1152637 2601809 := bstep (se 2 (by rfl) ⟨975678, by rfl⟩ : syracuseStep 2601809 = 1951357) B1951357
theorem B2601827 : Blo 1152637 2601827 := bstep (se 1 (by rfl) ⟨1951370, by rfl⟩ : syracuseStep 2601827 = 3902741) B3902741
theorem B1946497 : Blo 1152637 1946497 := bstep (se 2 (by rfl) ⟨729936, by rfl⟩ : syracuseStep 1946497 = 1459873) B1459873
theorem B1946531 : Blo 1152637 1946531 := bstep (se 1 (by rfl) ⟨1459898, by rfl⟩ : syracuseStep 1946531 = 2919797) B2919797
theorem B15774691 : Blo 1152637 15774691 := bstep (se 1 (by rfl) ⟨11831018, by rfl⟩ : syracuseStep 15774691 = 23662037) B23662037
theorem B1946659 : Blo 1152637 1946659 := bstep (se 1 (by rfl) ⟨1459994, by rfl⟩ : syracuseStep 1946659 = 2919989) B2919989
theorem B5846093 : Blo 1152637 5846093 := bstep (se 3 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 5846093 = 2192285) B2192285
theorem B2602097 : Blo 1152637 2602097 := bstep (se 2 (by rfl) ⟨975786, by rfl⟩ : syracuseStep 2602097 = 1951573) B1951573
theorem B2602115 : Blo 1152637 2602115 := bstep (se 1 (by rfl) ⟨1951586, by rfl⟩ : syracuseStep 2602115 = 3903173) B3903173
theorem B1946801 : Blo 1152637 1946801 := bstep (se 2 (by rfl) ⟨730050, by rfl⟩ : syracuseStep 1946801 = 1460101) B1460101
theorem B2634947 : Blo 1152637 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B15807757 : Blo 1152637 15807757 := bstep (se 3 (by rfl) ⟨2963954, by rfl⟩ : syracuseStep 15807757 = 5927909) B5927909
theorem B4437283 : Blo 1152637 4437283 := bstep (se 1 (by rfl) ⟨3327962, by rfl⟩ : syracuseStep 4437283 = 6655925) B6655925
theorem B1946929 : Blo 1152637 1946929 := bstep (se 2 (by rfl) ⟨730098, by rfl⟩ : syracuseStep 1946929 = 1460197) B1460197
theorem B1946963 : Blo 1152637 1946963 := bstep (se 1 (by rfl) ⟨1460222, by rfl⟩ : syracuseStep 1946963 = 2920445) B2920445
theorem B8336753 : Blo 1152637 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B2602385 : Blo 1152637 2602385 := bstep (se 2 (by rfl) ⟨975894, by rfl⟩ : syracuseStep 2602385 = 1951789) B1951789
theorem B2602403 : Blo 1152637 2602403 := bstep (se 1 (by rfl) ⟨1951802, by rfl⟩ : syracuseStep 2602403 = 3903605) B3903605
theorem B1947091 : Blo 1152637 1947091 := bstep (se 1 (by rfl) ⟨1460318, by rfl⟩ : syracuseStep 1947091 = 2920637) B2920637
theorem B15218189 : Blo 1152637 15218189 := bstep (se 3 (by rfl) ⟨2853410, by rfl⟩ : syracuseStep 15218189 = 5706821) B5706821
theorem B1947233 : Blo 1152637 1947233 := bstep (se 2 (by rfl) ⟨730212, by rfl⟩ : syracuseStep 1947233 = 1460425) B1460425
theorem B3290797 : Blo 1152637 3290797 := bstep (se 3 (by rfl) ⟨617024, by rfl⟩ : syracuseStep 3290797 = 1234049) B1234049
theorem B1947361 : Blo 1152637 1947361 := bstep (se 2 (by rfl) ⟨730260, by rfl⟩ : syracuseStep 1947361 = 1460521) B1460521
theorem B2340593 : Blo 1152637 2340593 := bstep (se 2 (by rfl) ⟨877722, by rfl⟩ : syracuseStep 2340593 = 1755445) B1755445
theorem B1947395 : Blo 1152637 1947395 := bstep (se 1 (by rfl) ⟨1460546, by rfl⟩ : syracuseStep 1947395 = 2921093) B2921093
theorem B2078531 : Blo 1152637 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1947523 : Blo 1152637 1947523 := bstep (se 1 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 1947523 = 2921285) B2921285
theorem B3291025 : Blo 1152637 3291025 := bstep (se 2 (by rfl) ⟨1234134, by rfl⟩ : syracuseStep 3291025 = 2468269) B2468269
theorem B1849331 : Blo 1152637 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B1947665 : Blo 1152637 1947665 := bstep (se 2 (by rfl) ⟨730374, by rfl⟩ : syracuseStep 1947665 = 1460749) B1460749
theorem B3749905 : Blo 1152637 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B3291185 : Blo 1152637 3291185 := bstep (se 2 (by rfl) ⟨1234194, by rfl⟩ : syracuseStep 3291185 = 2468389) B2468389
theorem B4929635 : Blo 1152637 4929635 := bstep (se 1 (by rfl) ⟨3697226, by rfl⟩ : syracuseStep 4929635 = 7394453) B7394453
theorem B1947793 : Blo 1152637 1947793 := bstep (se 2 (by rfl) ⟨730422, by rfl⟩ : syracuseStep 1947793 = 1460845) B1460845
theorem B3291299 : Blo 1152637 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B1947827 : Blo 1152637 1947827 := bstep (se 1 (by rfl) ⟨1460870, by rfl⟩ : syracuseStep 1947827 = 2921741) B2921741
theorem B1947955 : Blo 1152637 1947955 := bstep (se 1 (by rfl) ⟨1460966, by rfl⟩ : syracuseStep 1947955 = 2921933) B2921933
theorem B9877859 : Blo 1152637 9877859 := bstep (se 1 (by rfl) ⟨7408394, by rfl⟩ : syracuseStep 9877859 = 14816789) B14816789
theorem B1948097 : Blo 1152637 1948097 := bstep (se 2 (by rfl) ⟨730536, by rfl⟩ : syracuseStep 1948097 = 1461073) B1461073
theorem B16661045 : Blo 1152637 16661045 := bstep (se 5 (by rfl) ⟨780986, by rfl⟩ : syracuseStep 16661045 = 1561973) B1561973
theorem B1948225 : Blo 1152637 1948225 := bstep (se 2 (by rfl) ⟨730584, by rfl⟩ : syracuseStep 1948225 = 1461169) B1461169
theorem B1948259 : Blo 1152637 1948259 := bstep (se 1 (by rfl) ⟨1461194, by rfl⟩ : syracuseStep 1948259 = 2922389) B2922389
theorem B1948387 : Blo 1152637 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B1850177 : Blo 1152637 1850177 := bstep (se 2 (by rfl) ⟨693816, by rfl⟩ : syracuseStep 1850177 = 1387633) B1387633
theorem B4438883 : Blo 1152637 4438883 := bstep (se 1 (by rfl) ⟨3329162, by rfl⟩ : syracuseStep 4438883 = 6658325) B6658325
theorem B1948529 : Blo 1152637 1948529 := bstep (se 2 (by rfl) ⟨730698, by rfl⟩ : syracuseStep 1948529 = 1461397) B1461397
theorem B1850305 : Blo 1152637 1850305 := bstep (se 2 (by rfl) ⟨693864, by rfl⟩ : syracuseStep 1850305 = 1387729) B1387729
theorem B1948657 : Blo 1152637 1948657 := bstep (se 2 (by rfl) ⟨730746, by rfl⟩ : syracuseStep 1948657 = 1461493) B1461493
theorem B1850369 : Blo 1152637 1850369 := bstep (se 2 (by rfl) ⟨693888, by rfl⟩ : syracuseStep 1850369 = 1387777) B1387777
theorem B1948691 : Blo 1152637 1948691 := bstep (se 1 (by rfl) ⟨1461518, by rfl⟩ : syracuseStep 1948691 = 2923037) B2923037
theorem B2964593 : Blo 1152637 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B3292301 : Blo 1152637 3292301 := bstep (se 3 (by rfl) ⟨617306, by rfl⟩ : syracuseStep 3292301 = 1234613) B1234613
theorem B2636945 : Blo 1152637 2636945 := bstep (se 2 (by rfl) ⟨988854, by rfl⟩ : syracuseStep 2636945 = 1977709) B1977709
theorem B1948819 : Blo 1152637 1948819 := bstep (se 1 (by rfl) ⟨1461614, by rfl⟩ : syracuseStep 1948819 = 2923229) B2923229
theorem B6569201 : Blo 1152637 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B60833045 : Blo 1152637 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1948961 : Blo 1152637 1948961 := bstep (se 2 (by rfl) ⟨730860, by rfl⟩ : syracuseStep 1948961 = 1461721) B1461721
theorem B4930865 : Blo 1152637 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B3292483 : Blo 1152637 3292483 := bstep (se 1 (by rfl) ⟨2469362, by rfl⟩ : syracuseStep 3292483 = 4938725) B4938725
theorem B2080145 : Blo 1152637 2080145 := bstep (se 2 (by rfl) ⟨780054, by rfl⟩ : syracuseStep 2080145 = 1560109) B1560109
theorem B1949089 : Blo 1152637 1949089 := bstep (se 2 (by rfl) ⟨730908, by rfl⟩ : syracuseStep 1949089 = 1461817) B1461817
theorem B1949123 : Blo 1152637 1949123 := bstep (se 1 (by rfl) ⟨1461842, by rfl⟩ : syracuseStep 1949123 = 2923685) B2923685
theorem B3292643 : Blo 1152637 3292643 := bstep (se 1 (by rfl) ⟨2469482, by rfl⟩ : syracuseStep 3292643 = 4938965) B4938965
theorem B1949251 : Blo 1152637 1949251 := bstep (se 1 (by rfl) ⟨1461938, by rfl⟩ : syracuseStep 1949251 = 2923877) B2923877
theorem B1949393 : Blo 1152637 1949393 := bstep (se 2 (by rfl) ⟨731022, by rfl⟩ : syracuseStep 1949393 = 1462045) B1462045
theorem B1949521 : Blo 1152637 1949521 := bstep (se 2 (by rfl) ⟨731070, by rfl⟩ : syracuseStep 1949521 = 1462141) B1462141
theorem B1949555 : Blo 1152637 1949555 := bstep (se 1 (by rfl) ⟨1462166, by rfl⟩ : syracuseStep 1949555 = 2924333) B2924333
theorem B5849009 : Blo 1152637 5849009 := bstep (se 2 (by rfl) ⟨2193378, by rfl⟩ : syracuseStep 5849009 = 4386757) B4386757
theorem B1949683 : Blo 1152637 1949683 := bstep (se 1 (by rfl) ⟨1462262, by rfl⟩ : syracuseStep 1949683 = 2924525) B2924525
theorem B1851427 : Blo 1152637 1851427 := bstep (se 1 (by rfl) ⟨1388570, by rfl⟩ : syracuseStep 1851427 = 2777141) B2777141
theorem B1949825 : Blo 1152637 1949825 := bstep (se 2 (by rfl) ⟨731184, by rfl⟩ : syracuseStep 1949825 = 1462369) B1462369
theorem B1949953 : Blo 1152637 1949953 := bstep (se 2 (by rfl) ⟨731232, by rfl⟩ : syracuseStep 1949953 = 1462465) B1462465
theorem B1949987 : Blo 1152637 1949987 := bstep (se 1 (by rfl) ⟨1462490, by rfl⟩ : syracuseStep 1949987 = 2924981) B2924981
theorem B1950115 : Blo 1152637 1950115 := bstep (se 1 (by rfl) ⟨1462586, by rfl⟩ : syracuseStep 1950115 = 2925173) B2925173
theorem B2966051 : Blo 1152637 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B1950257 : Blo 1152637 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B6570659 : Blo 1152637 6570659 := bstep (se 1 (by rfl) ⟨4927994, by rfl⟩ : syracuseStep 6570659 = 9855989) B9855989
theorem B1950385 : Blo 1152637 1950385 := bstep (se 2 (by rfl) ⟨731394, by rfl⟩ : syracuseStep 1950385 = 1462789) B1462789
theorem B1950419 : Blo 1152637 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B12468977 : Blo 1152637 12468977 := bstep (se 2 (by rfl) ⟨4675866, by rfl⟩ : syracuseStep 12468977 = 9351733) B9351733
theorem B1950547 : Blo 1152637 1950547 := bstep (se 1 (by rfl) ⟨1462910, by rfl⟩ : syracuseStep 1950547 = 2925821) B2925821
theorem B1852355 : Blo 1152637 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B1950689 : Blo 1152637 1950689 := bstep (se 2 (by rfl) ⟨731508, by rfl⟩ : syracuseStep 1950689 = 1463017) B1463017
theorem B1459235 : Blo 1152637 1459235 := bstep (se 1 (by rfl) ⟨1094426, by rfl⟩ : syracuseStep 1459235 = 2188853) B2188853
theorem B1950817 : Blo 1152637 1950817 := bstep (se 2 (by rfl) ⟨731556, by rfl⟩ : syracuseStep 1950817 = 1463113) B1463113
theorem B1950851 : Blo 1152637 1950851 := bstep (se 1 (by rfl) ⟨1463138, by rfl⟩ : syracuseStep 1950851 = 2926277) B2926277
theorem B1852625 : Blo 1152637 1852625 := bstep (se 2 (by rfl) ⟨694734, by rfl⟩ : syracuseStep 1852625 = 1389469) B1389469
theorem B1950979 : Blo 1152637 1950979 := bstep (se 1 (by rfl) ⟨1463234, by rfl⟩ : syracuseStep 1950979 = 2926469) B2926469
theorem B2704739 : Blo 1152637 2704739 := bstep (se 1 (by rfl) ⟨2028554, by rfl⟩ : syracuseStep 2704739 = 4057109) B4057109
theorem B5850467 : Blo 1152637 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B2770307 : Blo 1152637 2770307 := bstep (se 1 (by rfl) ⟨2077730, by rfl⟩ : syracuseStep 2770307 = 4155461) B4155461
theorem B1951121 : Blo 1152637 1951121 := bstep (se 2 (by rfl) ⟨731670, by rfl⟩ : syracuseStep 1951121 = 1463341) B1463341
theorem B3556867 : Blo 1152637 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B1951249 : Blo 1152637 1951249 := bstep (se 2 (by rfl) ⟨731718, by rfl⟩ : syracuseStep 1951249 = 1463437) B1463437
theorem B1951283 : Blo 1152637 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B2770499 : Blo 1152637 2770499 := bstep (se 1 (by rfl) ⟨2077874, by rfl⟩ : syracuseStep 2770499 = 4155749) B4155749
theorem B1951411 : Blo 1152637 1951411 := bstep (se 1 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 1951411 = 2927117) B2927117
theorem B4933325 : Blo 1152637 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B1459939 : Blo 1152637 1459939 := bstep (se 1 (by rfl) ⟨1094954, by rfl⟩ : syracuseStep 1459939 = 2189909) B2189909
theorem B2967281 : Blo 1152637 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B1951553 : Blo 1152637 1951553 := bstep (se 2 (by rfl) ⟨731832, by rfl⟩ : syracuseStep 1951553 = 1463665) B1463665
theorem B1460035 : Blo 1152637 1460035 := bstep (se 1 (by rfl) ⟨1095026, by rfl⟩ : syracuseStep 1460035 = 2190053) B2190053
theorem B2770787 : Blo 1152637 2770787 := bstep (se 1 (by rfl) ⟨2078090, by rfl⟩ : syracuseStep 2770787 = 4156181) B4156181
theorem B1951681 : Blo 1152637 1951681 := bstep (se 2 (by rfl) ⟨731880, by rfl⟩ : syracuseStep 1951681 = 1463761) B1463761
theorem B3164113 : Blo 1152637 3164113 := bstep (se 2 (by rfl) ⟨1186542, by rfl⟩ : syracuseStep 3164113 = 2373085) B2373085
theorem B12503011 : Blo 1152637 12503011 := bstep (se 1 (by rfl) ⟨9377258, by rfl⟩ : syracuseStep 12503011 = 18754517) B18754517
theorem B1951715 : Blo 1152637 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B5851277 : Blo 1152637 5851277 := bstep (se 3 (by rfl) ⟨1097114, by rfl⟩ : syracuseStep 5851277 = 2194229) B2194229
theorem B1460531 : Blo 1152637 1460531 := bstep (se 1 (by rfl) ⟨1095398, by rfl⟩ : syracuseStep 1460531 = 2190797) B2190797
theorem B1296787 : Blo 1152637 1296787 := bstep (se 1 (by rfl) ⟨972590, by rfl⟩ : syracuseStep 1296787 = 1945181) B1945181
theorem B4377037 : Blo 1152637 4377037 := bstep (se 3 (by rfl) ⟨820694, by rfl⟩ : syracuseStep 4377037 = 1641389) B1641389
theorem B1559011 : Blo 1152637 1559011 := bstep (se 1 (by rfl) ⟨1169258, by rfl⟩ : syracuseStep 1559011 = 2338517) B2338517
theorem B1296931 : Blo 1152637 1296931 := bstep (se 1 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 1296931 = 1945397) B1945397
theorem B6244933 : Blo 1152637 6244933 := bstep (se 4 (by rfl) ⟨585462, by rfl⟩ : syracuseStep 6244933 = 1170925) B1170925
theorem B1297075 : Blo 1152637 1297075 := bstep (se 1 (by rfl) ⟨972806, by rfl⟩ : syracuseStep 1297075 = 1945613) B1945613
theorem B1624801 : Blo 1152637 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B2771729 : Blo 1152637 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B1297219 : Blo 1152637 1297219 := bstep (se 1 (by rfl) ⟨972914, by rfl⟩ : syracuseStep 1297219 = 1945829) B1945829
theorem B7392197 : Blo 1152637 7392197 := bstep (se 4 (by rfl) ⟨693018, by rfl⟩ : syracuseStep 7392197 = 1386037) B1386037
theorem B1297363 : Blo 1152637 1297363 := bstep (se 1 (by rfl) ⟨973022, by rfl⟩ : syracuseStep 1297363 = 1946045) B1946045
theorem B1461235 : Blo 1152637 1461235 := bstep (se 1 (by rfl) ⟨1095926, by rfl⟩ : syracuseStep 1461235 = 2191853) B2191853
theorem B1231939 : Blo 1152637 1231939 := bstep (se 1 (by rfl) ⟨923954, by rfl⟩ : syracuseStep 1231939 = 1847909) B1847909
theorem B1461331 : Blo 1152637 1461331 := bstep (se 1 (by rfl) ⟨1095998, by rfl⟩ : syracuseStep 1461331 = 2191997) B2191997
theorem B1297507 : Blo 1152637 1297507 := bstep (se 1 (by rfl) ⟨973130, by rfl⟩ : syracuseStep 1297507 = 1946261) B1946261
theorem B15191221 : Blo 1152637 15191221 := bstep (se 5 (by rfl) ⟨712088, by rfl⟩ : syracuseStep 15191221 = 1424177) B1424177
theorem B4377827 : Blo 1152637 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B9358577 : Blo 1152637 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B1297651 : Blo 1152637 1297651 := bstep (se 1 (by rfl) ⟨973238, by rfl⟩ : syracuseStep 1297651 = 1946477) B1946477
theorem B12471565 : Blo 1152637 12471565 := bstep (se 3 (by rfl) ⟨2338418, by rfl⟩ : syracuseStep 12471565 = 4676837) B4676837
theorem B1297795 : Blo 1152637 1297795 := bstep (se 1 (by rfl) ⟨973346, by rfl⟩ : syracuseStep 1297795 = 1946693) B1946693
theorem B13159907 : Blo 1152637 13159907 := bstep (se 1 (by rfl) ⟨9869930, by rfl⟩ : syracuseStep 13159907 = 19739861) B19739861
theorem B1232371 : Blo 1152637 1232371 := bstep (se 1 (by rfl) ⟨924278, by rfl⟩ : syracuseStep 1232371 = 1848557) B1848557
theorem B1297939 : Blo 1152637 1297939 := bstep (se 1 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 1297939 = 1946909) B1946909
theorem B1461827 : Blo 1152637 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B1560211 : Blo 1152637 1560211 := bstep (se 1 (by rfl) ⟨1170158, by rfl⟩ : syracuseStep 1560211 = 2340317) B2340317
theorem B1298083 : Blo 1152637 1298083 := bstep (se 1 (by rfl) ⟨973562, by rfl⟩ : syracuseStep 1298083 = 1947125) B1947125
theorem B2772689 : Blo 1152637 2772689 := bstep (se 2 (by rfl) ⟨1039758, by rfl⟩ : syracuseStep 2772689 = 2079517) B2079517
theorem B5557987 : Blo 1152637 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B3165955 : Blo 1152637 3165955 := bstep (se 1 (by rfl) ⟨2374466, by rfl⟩ : syracuseStep 3165955 = 4748933) B4748933
theorem B1298227 : Blo 1152637 1298227 := bstep (se 1 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 1298227 = 1947341) B1947341
theorem B4378481 : Blo 1152637 4378481 := bstep (se 2 (by rfl) ⟨1641930, by rfl⟩ : syracuseStep 4378481 = 3283861) B3283861
theorem B1298371 : Blo 1152637 1298371 := bstep (se 1 (by rfl) ⟨973778, by rfl⟩ : syracuseStep 1298371 = 1947557) B1947557
theorem B1298515 : Blo 1152637 1298515 := bstep (se 1 (by rfl) ⟨973886, by rfl⟩ : syracuseStep 1298515 = 1947773) B1947773
theorem B64016497 : Blo 1152637 64016497 := bstep (se 2 (by rfl) ⟨24006186, by rfl⟩ : syracuseStep 64016497 = 48012373) B48012373
theorem B2773219 : Blo 1152637 2773219 := bstep (se 1 (by rfl) ⟨2079914, by rfl⟩ : syracuseStep 2773219 = 4159829) B4159829
theorem B1298659 : Blo 1152637 1298659 := bstep (se 1 (by rfl) ⟨973994, by rfl⟩ : syracuseStep 1298659 = 1947989) B1947989
theorem B11096291 : Blo 1152637 11096291 := bstep (se 1 (by rfl) ⟨8322218, by rfl⟩ : syracuseStep 11096291 = 16644437) B16644437
theorem B1462531 : Blo 1152637 1462531 := bstep (se 1 (by rfl) ⟨1096898, by rfl⟩ : syracuseStep 1462531 = 2193797) B2193797
theorem B1462627 : Blo 1152637 1462627 := bstep (se 1 (by rfl) ⟨1096970, by rfl⟩ : syracuseStep 1462627 = 2193941) B2193941
theorem B1298803 : Blo 1152637 1298803 := bstep (se 1 (by rfl) ⟨974102, by rfl⟩ : syracuseStep 1298803 = 1948205) B1948205
theorem B4215181 : Blo 1152637 4215181 := bstep (se 3 (by rfl) ⟨790346, by rfl⟩ : syracuseStep 4215181 = 1580693) B1580693
theorem B1560979 : Blo 1152637 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B1298947 : Blo 1152637 1298947 := bstep (se 1 (by rfl) ⟨974210, by rfl⟩ : syracuseStep 1298947 = 1948421) B1948421
theorem B1299091 : Blo 1152637 1299091 := bstep (se 1 (by rfl) ⟨974318, by rfl⟩ : syracuseStep 1299091 = 1948637) B1948637
theorem B38490851 : Blo 1152637 38490851 := bstep (se 1 (by rfl) ⟨28868138, by rfl⟩ : syracuseStep 38490851 = 57736277) B57736277
theorem B1233635 : Blo 1152637 1233635 := bstep (se 1 (by rfl) ⟨925226, by rfl⟩ : syracuseStep 1233635 = 1850453) B1850453
theorem B1299235 : Blo 1152637 1299235 := bstep (se 1 (by rfl) ⟨974426, by rfl⟩ : syracuseStep 1299235 = 1948853) B1948853
theorem B1463123 : Blo 1152637 1463123 := bstep (se 1 (by rfl) ⟨1097342, by rfl⟩ : syracuseStep 1463123 = 2194685) B2194685
theorem B1299379 : Blo 1152637 1299379 := bstep (se 1 (by rfl) ⟨974534, by rfl⟩ : syracuseStep 1299379 = 1949069) B1949069
theorem B5854193 : Blo 1152637 5854193 := bstep (se 2 (by rfl) ⟨2195322, by rfl⟩ : syracuseStep 5854193 = 4390645) B4390645
theorem B21058613 : Blo 1152637 21058613 := bstep (se 5 (by rfl) ⟨987122, by rfl⟩ : syracuseStep 21058613 = 1974245) B1974245
theorem B1299523 : Blo 1152637 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B1299667 : Blo 1152637 1299667 := bstep (se 1 (by rfl) ⟨974750, by rfl⟩ : syracuseStep 1299667 = 1949501) B1949501
theorem B22172899 : Blo 1152637 22172899 := bstep (se 1 (by rfl) ⟨16629674, by rfl⟩ : syracuseStep 22172899 = 33259349) B33259349
theorem B4379939 : Blo 1152637 4379939 := bstep (se 1 (by rfl) ⟨3284954, by rfl⟩ : syracuseStep 4379939 = 6569909) B6569909
theorem B4379953 : Blo 1152637 4379953 := bstep (se 2 (by rfl) ⟨1642482, by rfl⟩ : syracuseStep 4379953 = 3284965) B3284965
theorem B1299811 : Blo 1152637 1299811 := bstep (se 1 (by rfl) ⟨974858, by rfl⟩ : syracuseStep 1299811 = 1949717) B1949717
theorem B1562017 : Blo 1152637 1562017 := bstep (se 2 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 1562017 = 1171513) B1171513
theorem B2774449 : Blo 1152637 2774449 := bstep (se 2 (by rfl) ⟨1040418, by rfl⟩ : syracuseStep 2774449 = 2080837) B2080837
theorem B1234387 : Blo 1152637 1234387 := bstep (se 1 (by rfl) ⟨925790, by rfl⟩ : syracuseStep 1234387 = 1851581) B1851581
theorem B1299955 : Blo 1152637 1299955 := bstep (se 1 (by rfl) ⟨974966, by rfl⟩ : syracuseStep 1299955 = 1949933) B1949933
theorem B1463827 : Blo 1152637 1463827 := bstep (se 1 (by rfl) ⟨1097870, by rfl⟩ : syracuseStep 1463827 = 2195741) B2195741
theorem B3331633 : Blo 1152637 3331633 := bstep (se 2 (by rfl) ⟨1249362, by rfl⟩ : syracuseStep 3331633 = 2498725) B2498725
theorem B7394915 : Blo 1152637 7394915 := bstep (se 1 (by rfl) ⟨5546186, by rfl⟩ : syracuseStep 7394915 = 11092373) B11092373
theorem B1300099 : Blo 1152637 1300099 := bstep (se 1 (by rfl) ⟨975074, by rfl⟩ : syracuseStep 1300099 = 1950149) B1950149
theorem B1300243 : Blo 1152637 1300243 := bstep (se 1 (by rfl) ⟨975182, by rfl⟩ : syracuseStep 1300243 = 1950365) B1950365
theorem B1300387 : Blo 1152637 1300387 := bstep (se 1 (by rfl) ⟨975290, by rfl⟩ : syracuseStep 1300387 = 1950581) B1950581
theorem B4937699 : Blo 1152637 4937699 := bstep (se 1 (by rfl) ⟨3703274, by rfl⟩ : syracuseStep 4937699 = 7406549) B7406549
theorem B1300531 : Blo 1152637 1300531 := bstep (se 1 (by rfl) ⟨975398, by rfl⟩ : syracuseStep 1300531 = 1950797) B1950797
theorem B1300675 : Blo 1152637 1300675 := bstep (se 1 (by rfl) ⟨975506, by rfl⟩ : syracuseStep 1300675 = 1951013) B1951013
theorem B1300819 : Blo 1152637 1300819 := bstep (se 1 (by rfl) ⟨975614, by rfl⟩ : syracuseStep 1300819 = 1951229) B1951229
theorem B9853325 : Blo 1152637 9853325 := bstep (se 3 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 9853325 = 3694997) B3694997
theorem B1300963 : Blo 1152637 1300963 := bstep (se 1 (by rfl) ⟨975722, by rfl⟩ : syracuseStep 1300963 = 1951445) B1951445
theorem B7494149 : Blo 1152637 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B4446733 : Blo 1152637 4446733 := bstep (se 3 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 4446733 = 1667525) B1667525
theorem B1301107 : Blo 1152637 1301107 := bstep (se 1 (by rfl) ⟨975830, by rfl⟩ : syracuseStep 1301107 = 1951661) B1951661
theorem B4381411 : Blo 1152637 4381411 := bstep (se 1 (by rfl) ⟨3286058, by rfl⟩ : syracuseStep 4381411 = 6572117) B6572117
theorem B35609315 : Blo 1152637 35609315 := bstep (se 1 (by rfl) ⟨26706986, by rfl⟩ : syracuseStep 35609315 = 53413973) B53413973
theorem B3890321 : Blo 1152637 3890321 := bstep (se 2 (by rfl) ⟨1458870, by rfl⟩ : syracuseStep 3890321 = 2917741) B2917741
theorem B44326115 : Blo 1152637 44326115 := bstep (se 1 (by rfl) ⟨33244586, by rfl⟩ : syracuseStep 44326115 = 66489173) B66489173
theorem B7396913 : Blo 1152637 7396913 := bstep (se 2 (by rfl) ⟨2773842, by rfl⟩ : syracuseStep 7396913 = 5547685) B5547685
theorem B3890861 : Blo 1152637 3890861 := bstep (se 3 (by rfl) ⟨729536, by rfl⟩ : syracuseStep 3890861 = 1459073) B1459073
theorem B3694253 : Blo 1152637 3694253 := bstep (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) B1385345
theorem B3890915 : Blo 1152637 3890915 := bstep (se 1 (by rfl) ⟨2918186, by rfl⟩ : syracuseStep 3890915 = 5836373) B5836373
theorem B8314609 : Blo 1152637 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B15392693 : Blo 1152637 15392693 := bstep (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) B1443065
theorem B3891185 : Blo 1152637 3891185 := bstep (se 2 (by rfl) ⟨1459194, by rfl⟩ : syracuseStep 3891185 = 2918389) B2918389
theorem B14639413 : Blo 1152637 14639413 := bstep (se 5 (by rfl) ⟨686222, by rfl⟩ : syracuseStep 14639413 = 1372445) B1372445
theorem B10805645 : Blo 1152637 10805645 := bstep (se 3 (by rfl) ⟨2026058, by rfl⟩ : syracuseStep 10805645 = 4052117) B4052117
theorem B5005745 : Blo 1152637 5005745 := bstep (se 2 (by rfl) ⟨1877154, by rfl⟩ : syracuseStep 5005745 = 3754309) B3754309
theorem B7397837 : Blo 1152637 7397837 := bstep (se 3 (by rfl) ⟨1387094, by rfl⟩ : syracuseStep 7397837 = 2774189) B2774189
theorem B1728977 : Blo 1152637 1728977 := bstep (se 2 (by rfl) ⟨648366, by rfl⟩ : syracuseStep 1728977 = 1296733) B1296733
theorem B1728995 : Blo 1152637 1728995 := bstep (se 1 (by rfl) ⟨1296746, by rfl⟩ : syracuseStep 1728995 = 2593493) B2593493
theorem B5923313 : Blo 1152637 5923313 := bstep (se 2 (by rfl) ⟨2221242, by rfl⟩ : syracuseStep 5923313 = 4442485) B4442485
theorem B1729025 : Blo 1152637 1729025 := bstep (se 2 (by rfl) ⟨648384, by rfl⟩ : syracuseStep 1729025 = 1296769) B1296769
theorem B3891725 : Blo 1152637 3891725 := bstep (se 3 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 3891725 = 1459397) B1459397
theorem B1729043 : Blo 1152637 1729043 := bstep (se 1 (by rfl) ⟨1296782, by rfl⟩ : syracuseStep 1729043 = 2593565) B2593565
theorem B1729073 : Blo 1152637 1729073 := bstep (se 2 (by rfl) ⟨648402, by rfl⟩ : syracuseStep 1729073 = 1296805) B1296805
theorem B1729091 : Blo 1152637 1729091 := bstep (se 1 (by rfl) ⟨1296818, by rfl⟩ : syracuseStep 1729091 = 2593637) B2593637
theorem B3891779 : Blo 1152637 3891779 := bstep (se 1 (by rfl) ⟨2918834, by rfl⟩ : syracuseStep 3891779 = 5837669) B5837669
theorem B4940365 : Blo 1152637 4940365 := bstep (se 3 (by rfl) ⟨926318, by rfl⟩ : syracuseStep 4940365 = 1852637) B1852637
theorem B1729121 : Blo 1152637 1729121 := bstep (se 2 (by rfl) ⟨648420, by rfl⟩ : syracuseStep 1729121 = 1296841) B1296841
theorem B8774243 : Blo 1152637 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B1729139 : Blo 1152637 1729139 := bstep (se 1 (by rfl) ⟨1296854, by rfl⟩ : syracuseStep 1729139 = 2593709) B2593709
theorem B1729169 : Blo 1152637 1729169 := bstep (se 2 (by rfl) ⟨648438, by rfl⟩ : syracuseStep 1729169 = 1296877) B1296877
theorem B1729187 : Blo 1152637 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B1729217 : Blo 1152637 1729217 := bstep (se 2 (by rfl) ⟨648456, by rfl⟩ : syracuseStep 1729217 = 1296913) B1296913
theorem B1729235 : Blo 1152637 1729235 := bstep (se 1 (by rfl) ⟨1296926, by rfl⟩ : syracuseStep 1729235 = 2593853) B2593853
theorem B9855715 : Blo 1152637 9855715 := bstep (se 1 (by rfl) ⟨7391786, by rfl⟩ : syracuseStep 9855715 = 14783573) B14783573
theorem B1729265 : Blo 1152637 1729265 := bstep (se 2 (by rfl) ⟨648474, by rfl⟩ : syracuseStep 1729265 = 1296949) B1296949
theorem B1729283 : Blo 1152637 1729283 := bstep (se 1 (by rfl) ⟨1296962, by rfl⟩ : syracuseStep 1729283 = 2593925) B2593925
theorem B1729313 : Blo 1152637 1729313 := bstep (se 2 (by rfl) ⟨648492, by rfl⟩ : syracuseStep 1729313 = 1296985) B1296985
theorem B1729331 : Blo 1152637 1729331 := bstep (se 1 (by rfl) ⟨1296998, by rfl⟩ : syracuseStep 1729331 = 2593997) B2593997
theorem B1172291 : Blo 1152637 1172291 := bstep (se 1 (by rfl) ⟨879218, by rfl⟩ : syracuseStep 1172291 = 1758437) B1758437
theorem B1729361 : Blo 1152637 1729361 := bstep (se 2 (by rfl) ⟨648510, by rfl⟩ : syracuseStep 1729361 = 1297021) B1297021
theorem B3892049 : Blo 1152637 3892049 := bstep (se 2 (by rfl) ⟨1459518, by rfl⟩ : syracuseStep 3892049 = 2919037) B2919037
theorem B1729379 : Blo 1152637 1729379 := bstep (se 1 (by rfl) ⟨1297034, by rfl⟩ : syracuseStep 1729379 = 2594069) B2594069
theorem B1729409 : Blo 1152637 1729409 := bstep (se 2 (by rfl) ⟨648528, by rfl⟩ : syracuseStep 1729409 = 1297057) B1297057
theorem B4383629 : Blo 1152637 4383629 := bstep (se 3 (by rfl) ⟨821930, by rfl⟩ : syracuseStep 4383629 = 1643861) B1643861
theorem B1729427 : Blo 1152637 1729427 := bstep (se 1 (by rfl) ⟨1297070, by rfl⟩ : syracuseStep 1729427 = 2594141) B2594141
theorem B1729457 : Blo 1152637 1729457 := bstep (se 2 (by rfl) ⟨648546, by rfl⟩ : syracuseStep 1729457 = 1297093) B1297093
theorem B1729475 : Blo 1152637 1729475 := bstep (se 1 (by rfl) ⟨1297106, by rfl⟩ : syracuseStep 1729475 = 2594213) B2594213
theorem B1729505 : Blo 1152637 1729505 := bstep (se 2 (by rfl) ⟨648564, by rfl⟩ : syracuseStep 1729505 = 1297129) B1297129
theorem B1729523 : Blo 1152637 1729523 := bstep (se 1 (by rfl) ⟨1297142, by rfl⟩ : syracuseStep 1729523 = 2594285) B2594285
theorem B2188291 : Blo 1152637 2188291 := bstep (se 1 (by rfl) ⟨1641218, by rfl⟩ : syracuseStep 2188291 = 3282437) B3282437
theorem B1729553 : Blo 1152637 1729553 := bstep (se 2 (by rfl) ⟨648582, by rfl⟩ : syracuseStep 1729553 = 1297165) B1297165
theorem B1729571 : Blo 1152637 1729571 := bstep (se 1 (by rfl) ⟨1297178, by rfl⟩ : syracuseStep 1729571 = 2594357) B2594357
theorem B1729601 : Blo 1152637 1729601 := bstep (se 2 (by rfl) ⟨648600, by rfl⟩ : syracuseStep 1729601 = 1297201) B1297201
theorem B3204163 : Blo 1152637 3204163 := bstep (se 1 (by rfl) ⟨2403122, by rfl⟩ : syracuseStep 3204163 = 4806245) B4806245
theorem B1729619 : Blo 1152637 1729619 := bstep (se 1 (by rfl) ⟨1297214, by rfl⟩ : syracuseStep 1729619 = 2594429) B2594429
theorem B1729649 : Blo 1152637 1729649 := bstep (se 2 (by rfl) ⟨648618, by rfl⟩ : syracuseStep 1729649 = 1297237) B1297237
theorem B1729667 : Blo 1152637 1729667 := bstep (se 1 (by rfl) ⟨1297250, by rfl⟩ : syracuseStep 1729667 = 2594501) B2594501
theorem B1729697 : Blo 1152637 1729697 := bstep (se 2 (by rfl) ⟨648636, by rfl⟩ : syracuseStep 1729697 = 1297273) B1297273
theorem B2188451 : Blo 1152637 2188451 := bstep (se 1 (by rfl) ⟨1641338, by rfl⟩ : syracuseStep 2188451 = 3282677) B3282677
theorem B1729715 : Blo 1152637 1729715 := bstep (se 1 (by rfl) ⟨1297286, by rfl⟩ : syracuseStep 1729715 = 2594573) B2594573
theorem B1729745 : Blo 1152637 1729745 := bstep (se 2 (by rfl) ⟨648654, by rfl⟩ : syracuseStep 1729745 = 1297309) B1297309
theorem B1729763 : Blo 1152637 1729763 := bstep (se 1 (by rfl) ⟨1297322, by rfl⟩ : syracuseStep 1729763 = 2594645) B2594645
theorem B3695843 : Blo 1152637 3695843 := bstep (se 1 (by rfl) ⟨2771882, by rfl⟩ : syracuseStep 3695843 = 5543765) B5543765
theorem B1729793 : Blo 1152637 1729793 := bstep (se 2 (by rfl) ⟨648672, by rfl⟩ : syracuseStep 1729793 = 1297345) B1297345
theorem B2778371 : Blo 1152637 2778371 := bstep (se 1 (by rfl) ⟨2083778, by rfl⟩ : syracuseStep 2778371 = 4167557) B4167557
theorem B1729811 : Blo 1152637 1729811 := bstep (se 1 (by rfl) ⟨1297358, by rfl⟩ : syracuseStep 1729811 = 2594717) B2594717
theorem B1729841 : Blo 1152637 1729841 := bstep (se 2 (by rfl) ⟨648690, by rfl⟩ : syracuseStep 1729841 = 1297381) B1297381
theorem B1729859 : Blo 1152637 1729859 := bstep (se 1 (by rfl) ⟨1297394, by rfl⟩ : syracuseStep 1729859 = 2594789) B2594789
theorem B1729889 : Blo 1152637 1729889 := bstep (se 2 (by rfl) ⟨648708, by rfl⟩ : syracuseStep 1729889 = 1297417) B1297417
theorem B3892589 : Blo 1152637 3892589 := bstep (se 3 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 3892589 = 1459721) B1459721
theorem B1729907 : Blo 1152637 1729907 := bstep (se 1 (by rfl) ⟨1297430, by rfl⟩ : syracuseStep 1729907 = 2594861) B2594861
theorem B6579589 : Blo 1152637 6579589 := bstep (se 4 (by rfl) ⟨616836, by rfl⟩ : syracuseStep 6579589 = 1233673) B1233673
theorem B1729937 : Blo 1152637 1729937 := bstep (se 2 (by rfl) ⟨648726, by rfl⟩ : syracuseStep 1729937 = 1297453) B1297453
theorem B1729955 : Blo 1152637 1729955 := bstep (se 1 (by rfl) ⟨1297466, by rfl⟩ : syracuseStep 1729955 = 2594933) B2594933
theorem B3892643 : Blo 1152637 3892643 := bstep (se 1 (by rfl) ⟨2919482, by rfl⟩ : syracuseStep 3892643 = 5838965) B5838965
theorem B1729985 : Blo 1152637 1729985 := bstep (se 2 (by rfl) ⟨648744, by rfl⟩ : syracuseStep 1729985 = 1297489) B1297489
theorem B1730003 : Blo 1152637 1730003 := bstep (se 1 (by rfl) ⟨1297502, by rfl⟩ : syracuseStep 1730003 = 2595005) B2595005
theorem B1730033 : Blo 1152637 1730033 := bstep (se 2 (by rfl) ⟨648762, by rfl⟩ : syracuseStep 1730033 = 1297525) B1297525
theorem B1730051 : Blo 1152637 1730051 := bstep (se 1 (by rfl) ⟨1297538, by rfl⟩ : syracuseStep 1730051 = 2595077) B2595077
theorem B1730081 : Blo 1152637 1730081 := bstep (se 2 (by rfl) ⟨648780, by rfl⟩ : syracuseStep 1730081 = 1297561) B1297561
theorem B1730099 : Blo 1152637 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B1730129 : Blo 1152637 1730129 := bstep (se 2 (by rfl) ⟨648798, by rfl⟩ : syracuseStep 1730129 = 1297597) B1297597
theorem B1730147 : Blo 1152637 1730147 := bstep (se 1 (by rfl) ⟨1297610, by rfl⟩ : syracuseStep 1730147 = 2595221) B2595221
theorem B1730177 : Blo 1152637 1730177 := bstep (se 2 (by rfl) ⟨648816, by rfl⟩ : syracuseStep 1730177 = 1297633) B1297633
theorem B1730195 : Blo 1152637 1730195 := bstep (se 1 (by rfl) ⟨1297646, by rfl⟩ : syracuseStep 1730195 = 2595293) B2595293
theorem B3892913 : Blo 1152637 3892913 := bstep (se 2 (by rfl) ⟨1459842, by rfl⟩ : syracuseStep 3892913 = 2919685) B2919685
theorem B1730225 : Blo 1152637 1730225 := bstep (se 2 (by rfl) ⟨648834, by rfl⟩ : syracuseStep 1730225 = 1297669) B1297669
theorem B1730243 : Blo 1152637 1730243 := bstep (se 1 (by rfl) ⟨1297682, by rfl⟩ : syracuseStep 1730243 = 2595365) B2595365
theorem B1730273 : Blo 1152637 1730273 := bstep (se 2 (by rfl) ⟨648852, by rfl⟩ : syracuseStep 1730273 = 1297705) B1297705
theorem B1730291 : Blo 1152637 1730291 := bstep (se 1 (by rfl) ⟨1297718, by rfl⟩ : syracuseStep 1730291 = 2595437) B2595437
theorem B1730321 : Blo 1152637 1730321 := bstep (se 2 (by rfl) ⟨648870, by rfl⟩ : syracuseStep 1730321 = 1297741) B1297741
theorem B1730339 : Blo 1152637 1730339 := bstep (se 1 (by rfl) ⟨1297754, by rfl⟩ : syracuseStep 1730339 = 2595509) B2595509
theorem B1730369 : Blo 1152637 1730369 := bstep (se 2 (by rfl) ⟨648888, by rfl⟩ : syracuseStep 1730369 = 1297777) B1297777
theorem B1730387 : Blo 1152637 1730387 := bstep (se 1 (by rfl) ⟨1297790, by rfl⟩ : syracuseStep 1730387 = 2595581) B2595581
theorem B1730417 : Blo 1152637 1730417 := bstep (se 2 (by rfl) ⟨648906, by rfl⟩ : syracuseStep 1730417 = 1297813) B1297813
theorem B1730435 : Blo 1152637 1730435 := bstep (se 1 (by rfl) ⟨1297826, by rfl⟩ : syracuseStep 1730435 = 2595653) B2595653
theorem B1730465 : Blo 1152637 1730465 := bstep (se 2 (by rfl) ⟨648924, by rfl⟩ : syracuseStep 1730465 = 1297849) B1297849
theorem B7890851 : Blo 1152637 7890851 := bstep (se 1 (by rfl) ⟨5918138, by rfl⟩ : syracuseStep 7890851 = 11836277) B11836277
theorem B1730483 : Blo 1152637 1730483 := bstep (se 1 (by rfl) ⟨1297862, by rfl⟩ : syracuseStep 1730483 = 2595725) B2595725
theorem B1730513 : Blo 1152637 1730513 := bstep (se 2 (by rfl) ⟨648942, by rfl⟩ : syracuseStep 1730513 = 1297885) B1297885
theorem B1730531 : Blo 1152637 1730531 := bstep (se 1 (by rfl) ⟨1297898, by rfl⟩ : syracuseStep 1730531 = 2595797) B2595797
theorem B1730561 : Blo 1152637 1730561 := bstep (se 2 (by rfl) ⟨648960, by rfl⟩ : syracuseStep 1730561 = 1297921) B1297921
theorem B1730579 : Blo 1152637 1730579 := bstep (se 1 (by rfl) ⟨1297934, by rfl⟩ : syracuseStep 1730579 = 2595869) B2595869
theorem B1730609 : Blo 1152637 1730609 := bstep (se 2 (by rfl) ⟨648978, by rfl⟩ : syracuseStep 1730609 = 1297957) B1297957
theorem B1730627 : Blo 1152637 1730627 := bstep (se 1 (by rfl) ⟨1297970, by rfl⟩ : syracuseStep 1730627 = 2595941) B2595941
theorem B1730657 : Blo 1152637 1730657 := bstep (se 2 (by rfl) ⟨648996, by rfl⟩ : syracuseStep 1730657 = 1297993) B1297993
theorem B1730675 : Blo 1152637 1730675 := bstep (se 1 (by rfl) ⟨1298006, by rfl⟩ : syracuseStep 1730675 = 2596013) B2596013
theorem B1730705 : Blo 1152637 1730705 := bstep (se 2 (by rfl) ⟨649014, by rfl⟩ : syracuseStep 1730705 = 1298029) B1298029
theorem B1730723 : Blo 1152637 1730723 := bstep (se 1 (by rfl) ⟨1298042, by rfl⟩ : syracuseStep 1730723 = 2596085) B2596085
theorem B1730753 : Blo 1152637 1730753 := bstep (se 2 (by rfl) ⟨649032, by rfl⟩ : syracuseStep 1730753 = 1298065) B1298065
theorem B3893453 : Blo 1152637 3893453 := bstep (se 3 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 3893453 = 1460045) B1460045
theorem B2189521 : Blo 1152637 2189521 := bstep (se 2 (by rfl) ⟨821070, by rfl⟩ : syracuseStep 2189521 = 1642141) B1642141
theorem B1730771 : Blo 1152637 1730771 := bstep (se 1 (by rfl) ⟨1298078, by rfl⟩ : syracuseStep 1730771 = 2596157) B2596157
theorem B1730801 : Blo 1152637 1730801 := bstep (se 2 (by rfl) ⟨649050, by rfl⟩ : syracuseStep 1730801 = 1298101) B1298101
theorem B3893507 : Blo 1152637 3893507 := bstep (se 1 (by rfl) ⟨2920130, by rfl⟩ : syracuseStep 3893507 = 5840261) B5840261
theorem B1730819 : Blo 1152637 1730819 := bstep (se 1 (by rfl) ⟨1298114, by rfl⟩ : syracuseStep 1730819 = 2596229) B2596229
theorem B1730849 : Blo 1152637 1730849 := bstep (se 2 (by rfl) ⟨649068, by rfl⟩ : syracuseStep 1730849 = 1298137) B1298137
theorem B1730867 : Blo 1152637 1730867 := bstep (se 1 (by rfl) ⟨1298150, by rfl⟩ : syracuseStep 1730867 = 2596301) B2596301
theorem B1730897 : Blo 1152637 1730897 := bstep (se 2 (by rfl) ⟨649086, by rfl⟩ : syracuseStep 1730897 = 1298173) B1298173
theorem B1730915 : Blo 1152637 1730915 := bstep (se 1 (by rfl) ⟨1298186, by rfl⟩ : syracuseStep 1730915 = 2596373) B2596373
theorem B1730945 : Blo 1152637 1730945 := bstep (se 2 (by rfl) ⟨649104, by rfl⟩ : syracuseStep 1730945 = 1298209) B1298209
theorem B1730963 : Blo 1152637 1730963 := bstep (se 1 (by rfl) ⟨1298222, by rfl⟩ : syracuseStep 1730963 = 2596445) B2596445
theorem B1730993 : Blo 1152637 1730993 := bstep (se 2 (by rfl) ⟨649122, by rfl⟩ : syracuseStep 1730993 = 1298245) B1298245
theorem B3697073 : Blo 1152637 3697073 := bstep (se 2 (by rfl) ⟨1386402, by rfl⟩ : syracuseStep 3697073 = 2772805) B2772805
theorem B1731011 : Blo 1152637 1731011 := bstep (se 1 (by rfl) ⟨1298258, by rfl⟩ : syracuseStep 1731011 = 2596517) B2596517
theorem B3336643 : Blo 1152637 3336643 := bstep (se 1 (by rfl) ⟨2502482, by rfl⟩ : syracuseStep 3336643 = 5004965) B5004965
theorem B1731041 : Blo 1152637 1731041 := bstep (se 2 (by rfl) ⟨649140, by rfl⟩ : syracuseStep 1731041 = 1298281) B1298281
theorem B1731059 : Blo 1152637 1731059 := bstep (se 1 (by rfl) ⟨1298294, by rfl⟩ : syracuseStep 1731059 = 2596589) B2596589
theorem B3893777 : Blo 1152637 3893777 := bstep (se 2 (by rfl) ⟨1460166, by rfl⟩ : syracuseStep 3893777 = 2920333) B2920333
theorem B1731089 : Blo 1152637 1731089 := bstep (se 2 (by rfl) ⟨649158, by rfl⟩ : syracuseStep 1731089 = 1298317) B1298317
theorem B1731107 : Blo 1152637 1731107 := bstep (se 1 (by rfl) ⟨1298330, by rfl⟩ : syracuseStep 1731107 = 2596661) B2596661
theorem B1731137 : Blo 1152637 1731137 := bstep (se 2 (by rfl) ⟨649176, by rfl⟩ : syracuseStep 1731137 = 1298353) B1298353
theorem B1731155 : Blo 1152637 1731155 := bstep (se 1 (by rfl) ⟨1298366, by rfl⟩ : syracuseStep 1731155 = 2596733) B2596733
theorem B1731185 : Blo 1152637 1731185 := bstep (se 2 (by rfl) ⟨649194, by rfl⟩ : syracuseStep 1731185 = 1298389) B1298389
theorem B1731203 : Blo 1152637 1731203 := bstep (se 1 (by rfl) ⟨1298402, by rfl⟩ : syracuseStep 1731203 = 2596805) B2596805
theorem B1731233 : Blo 1152637 1731233 := bstep (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) B1298425
theorem B1731251 : Blo 1152637 1731251 := bstep (se 1 (by rfl) ⟨1298438, by rfl⟩ : syracuseStep 1731251 = 2596877) B2596877
theorem B1731281 : Blo 1152637 1731281 := bstep (se 2 (by rfl) ⟨649230, by rfl⟩ : syracuseStep 1731281 = 1298461) B1298461
theorem B1731299 : Blo 1152637 1731299 := bstep (se 1 (by rfl) ⟨1298474, by rfl⟩ : syracuseStep 1731299 = 2596949) B2596949
theorem B5073635 : Blo 1152637 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B1731329 : Blo 1152637 1731329 := bstep (se 2 (by rfl) ⟨649248, by rfl⟩ : syracuseStep 1731329 = 1298497) B1298497
theorem B1731347 : Blo 1152637 1731347 := bstep (se 1 (by rfl) ⟨1298510, by rfl⟩ : syracuseStep 1731347 = 2597021) B2597021
theorem B1731377 : Blo 1152637 1731377 := bstep (se 2 (by rfl) ⟨649266, by rfl⟩ : syracuseStep 1731377 = 1298533) B1298533
theorem B1731395 : Blo 1152637 1731395 := bstep (se 1 (by rfl) ⟨1298546, by rfl⟩ : syracuseStep 1731395 = 2597093) B2597093
theorem B1731425 : Blo 1152637 1731425 := bstep (se 2 (by rfl) ⟨649284, by rfl⟩ : syracuseStep 1731425 = 1298569) B1298569
theorem B1731443 : Blo 1152637 1731443 := bstep (se 1 (by rfl) ⟨1298582, by rfl⟩ : syracuseStep 1731443 = 2597165) B2597165
theorem B1731473 : Blo 1152637 1731473 := bstep (se 2 (by rfl) ⟨649302, by rfl⟩ : syracuseStep 1731473 = 1298605) B1298605
theorem B1731491 : Blo 1152637 1731491 := bstep (se 1 (by rfl) ⟨1298618, by rfl⟩ : syracuseStep 1731491 = 2597237) B2597237
theorem B1731521 : Blo 1152637 1731521 := bstep (se 2 (by rfl) ⟨649320, by rfl⟩ : syracuseStep 1731521 = 1298641) B1298641
theorem B1731539 : Blo 1152637 1731539 := bstep (se 1 (by rfl) ⟨1298654, by rfl⟩ : syracuseStep 1731539 = 2597309) B2597309
theorem B1731569 : Blo 1152637 1731569 := bstep (se 2 (by rfl) ⟨649338, by rfl⟩ : syracuseStep 1731569 = 1298677) B1298677
theorem B1731587 : Blo 1152637 1731587 := bstep (se 1 (by rfl) ⟨1298690, by rfl⟩ : syracuseStep 1731587 = 2597381) B2597381
theorem B1731617 : Blo 1152637 1731617 := bstep (se 2 (by rfl) ⟨649356, by rfl⟩ : syracuseStep 1731617 = 1298713) B1298713
theorem B3894317 : Blo 1152637 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B1731635 : Blo 1152637 1731635 := bstep (se 1 (by rfl) ⟨1298726, by rfl⟩ : syracuseStep 1731635 = 2597453) B2597453
theorem B1731665 : Blo 1152637 1731665 := bstep (se 2 (by rfl) ⟨649374, by rfl⟩ : syracuseStep 1731665 = 1298749) B1298749
theorem B3894371 : Blo 1152637 3894371 := bstep (se 1 (by rfl) ⟨2920778, by rfl⟩ : syracuseStep 3894371 = 5841557) B5841557
theorem B1731683 : Blo 1152637 1731683 := bstep (se 1 (by rfl) ⟨1298762, by rfl⟩ : syracuseStep 1731683 = 2597525) B2597525
theorem B1731713 : Blo 1152637 1731713 := bstep (se 2 (by rfl) ⟨649392, by rfl⟩ : syracuseStep 1731713 = 1298785) B1298785
theorem B1731731 : Blo 1152637 1731731 := bstep (se 1 (by rfl) ⟨1298798, by rfl⟩ : syracuseStep 1731731 = 2597597) B2597597
theorem B1731761 : Blo 1152637 1731761 := bstep (se 2 (by rfl) ⟨649410, by rfl⟩ : syracuseStep 1731761 = 1298821) B1298821
theorem B1731779 : Blo 1152637 1731779 := bstep (se 1 (by rfl) ⟨1298834, by rfl⟩ : syracuseStep 1731779 = 2597669) B2597669
theorem B1731809 : Blo 1152637 1731809 := bstep (se 2 (by rfl) ⟨649428, by rfl⟩ : syracuseStep 1731809 = 1298857) B1298857
theorem B3337453 : Blo 1152637 3337453 := bstep (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) B1251545
theorem B2190577 : Blo 1152637 2190577 := bstep (se 2 (by rfl) ⟨821466, by rfl⟩ : syracuseStep 2190577 = 1642933) B1642933
theorem B1731827 : Blo 1152637 1731827 := bstep (se 1 (by rfl) ⟨1298870, by rfl⟩ : syracuseStep 1731827 = 2597741) B2597741
theorem B3697933 : Blo 1152637 3697933 := bstep (se 3 (by rfl) ⟨693362, by rfl⟩ : syracuseStep 3697933 = 1386725) B1386725
theorem B1731857 : Blo 1152637 1731857 := bstep (se 2 (by rfl) ⟨649446, by rfl⟩ : syracuseStep 1731857 = 1298893) B1298893
theorem B1731875 : Blo 1152637 1731875 := bstep (se 1 (by rfl) ⟨1298906, by rfl⟩ : syracuseStep 1731875 = 2597813) B2597813
theorem B1731905 : Blo 1152637 1731905 := bstep (se 2 (by rfl) ⟨649464, by rfl⟩ : syracuseStep 1731905 = 1298929) B1298929
theorem B6581573 : Blo 1152637 6581573 := bstep (se 4 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 6581573 = 1234045) B1234045
theorem B1731923 : Blo 1152637 1731923 := bstep (se 1 (by rfl) ⟨1298942, by rfl⟩ : syracuseStep 1731923 = 2597885) B2597885
theorem B3894641 : Blo 1152637 3894641 := bstep (se 2 (by rfl) ⟨1460490, by rfl⟩ : syracuseStep 3894641 = 2920981) B2920981
theorem B1731953 : Blo 1152637 1731953 := bstep (se 2 (by rfl) ⟨649482, by rfl⟩ : syracuseStep 1731953 = 1298965) B1298965
theorem B1731971 : Blo 1152637 1731971 := bstep (se 1 (by rfl) ⟨1298978, by rfl⟩ : syracuseStep 1731971 = 2597957) B2597957
theorem B1732001 : Blo 1152637 1732001 := bstep (se 2 (by rfl) ⟨649500, by rfl⟩ : syracuseStep 1732001 = 1299001) B1299001
theorem B1732019 : Blo 1152637 1732019 := bstep (se 1 (by rfl) ⟨1299014, by rfl⟩ : syracuseStep 1732019 = 2598029) B2598029
theorem B1732049 : Blo 1152637 1732049 := bstep (se 2 (by rfl) ⟨649518, by rfl⟩ : syracuseStep 1732049 = 1299037) B1299037
theorem B1732067 : Blo 1152637 1732067 := bstep (se 1 (by rfl) ⟨1299050, by rfl⟩ : syracuseStep 1732067 = 2598101) B2598101
theorem B1732097 : Blo 1152637 1732097 := bstep (se 2 (by rfl) ⟨649536, by rfl⟩ : syracuseStep 1732097 = 1299073) B1299073
theorem B1732115 : Blo 1152637 1732115 := bstep (se 1 (by rfl) ⟨1299086, by rfl⟩ : syracuseStep 1732115 = 2598173) B2598173
theorem B1732145 : Blo 1152637 1732145 := bstep (se 2 (by rfl) ⟨649554, by rfl⟩ : syracuseStep 1732145 = 1299109) B1299109
theorem B1732163 : Blo 1152637 1732163 := bstep (se 1 (by rfl) ⟨1299122, by rfl⟩ : syracuseStep 1732163 = 2598245) B2598245
theorem B1732193 : Blo 1152637 1732193 := bstep (se 2 (by rfl) ⟨649572, by rfl⟩ : syracuseStep 1732193 = 1299145) B1299145
theorem B1732211 : Blo 1152637 1732211 := bstep (se 1 (by rfl) ⟨1299158, by rfl⟩ : syracuseStep 1732211 = 2598317) B2598317
theorem B2190979 : Blo 1152637 2190979 := bstep (se 1 (by rfl) ⟨1643234, by rfl⟩ : syracuseStep 2190979 = 3286469) B3286469
theorem B1732241 : Blo 1152637 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B1732259 : Blo 1152637 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B2191025 : Blo 1152637 2191025 := bstep (se 2 (by rfl) ⟨821634, by rfl⟩ : syracuseStep 2191025 = 1643269) B1643269
theorem B1732289 : Blo 1152637 1732289 := bstep (se 2 (by rfl) ⟨649608, by rfl⟩ : syracuseStep 1732289 = 1299217) B1299217
theorem B1732307 : Blo 1152637 1732307 := bstep (se 1 (by rfl) ⟨1299230, by rfl⟩ : syracuseStep 1732307 = 2598461) B2598461
theorem B1732337 : Blo 1152637 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B4386545 : Blo 1152637 4386545 := bstep (se 2 (by rfl) ⟨1644954, by rfl⟩ : syracuseStep 4386545 = 3289909) B3289909
theorem B1732355 : Blo 1152637 1732355 := bstep (se 1 (by rfl) ⟨1299266, by rfl⟩ : syracuseStep 1732355 = 2598533) B2598533
theorem B1732385 : Blo 1152637 1732385 := bstep (se 2 (by rfl) ⟨649644, by rfl⟩ : syracuseStep 1732385 = 1299289) B1299289
theorem B1732403 : Blo 1152637 1732403 := bstep (se 1 (by rfl) ⟨1299302, by rfl⟩ : syracuseStep 1732403 = 2598605) B2598605
theorem B1732433 : Blo 1152637 1732433 := bstep (se 2 (by rfl) ⟨649662, by rfl⟩ : syracuseStep 1732433 = 1299325) B1299325
theorem B1732451 : Blo 1152637 1732451 := bstep (se 1 (by rfl) ⟨1299338, by rfl⟩ : syracuseStep 1732451 = 2598677) B2598677
theorem B11235185 : Blo 1152637 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B1732481 : Blo 1152637 1732481 := bstep (se 2 (by rfl) ⟨649680, by rfl⟩ : syracuseStep 1732481 = 1299361) B1299361
theorem B3895181 : Blo 1152637 3895181 := bstep (se 3 (by rfl) ⟨730346, by rfl⟩ : syracuseStep 3895181 = 1460693) B1460693
theorem B1732499 : Blo 1152637 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B1732529 : Blo 1152637 1732529 := bstep (se 2 (by rfl) ⟨649698, by rfl⟩ : syracuseStep 1732529 = 1299397) B1299397
theorem B3895235 : Blo 1152637 3895235 := bstep (se 1 (by rfl) ⟨2921426, by rfl⟩ : syracuseStep 3895235 = 5842853) B5842853
theorem B1732547 : Blo 1152637 1732547 := bstep (se 1 (by rfl) ⟨1299410, by rfl⟩ : syracuseStep 1732547 = 2598821) B2598821
theorem B2191313 : Blo 1152637 2191313 := bstep (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) B1643485
theorem B1732577 : Blo 1152637 1732577 := bstep (se 2 (by rfl) ⟨649716, by rfl⟩ : syracuseStep 1732577 = 1299433) B1299433
theorem B1732595 : Blo 1152637 1732595 := bstep (se 1 (by rfl) ⟨1299446, by rfl⟩ : syracuseStep 1732595 = 2598893) B2598893
theorem B1732625 : Blo 1152637 1732625 := bstep (se 2 (by rfl) ⟨649734, by rfl⟩ : syracuseStep 1732625 = 1299469) B1299469
theorem B1732643 : Blo 1152637 1732643 := bstep (se 1 (by rfl) ⟨1299482, by rfl⟩ : syracuseStep 1732643 = 2598965) B2598965
theorem B1732673 : Blo 1152637 1732673 := bstep (se 2 (by rfl) ⟨649752, by rfl⟩ : syracuseStep 1732673 = 1299505) B1299505
theorem B1732691 : Blo 1152637 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B28471409 : Blo 1152637 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B1732721 : Blo 1152637 1732721 := bstep (se 2 (by rfl) ⟨649770, by rfl⟩ : syracuseStep 1732721 = 1299541) B1299541
theorem B1732739 : Blo 1152637 1732739 := bstep (se 1 (by rfl) ⟨1299554, by rfl⟩ : syracuseStep 1732739 = 2599109) B2599109
theorem B1732769 : Blo 1152637 1732769 := bstep (se 2 (by rfl) ⟨649788, by rfl⟩ : syracuseStep 1732769 = 1299577) B1299577
theorem B1732787 : Blo 1152637 1732787 := bstep (se 1 (by rfl) ⟨1299590, by rfl⟩ : syracuseStep 1732787 = 2599181) B2599181
theorem B3895505 : Blo 1152637 3895505 := bstep (se 2 (by rfl) ⟨1460814, by rfl⟩ : syracuseStep 3895505 = 2921629) B2921629
theorem B1732817 : Blo 1152637 1732817 := bstep (se 2 (by rfl) ⟨649806, by rfl⟩ : syracuseStep 1732817 = 1299613) B1299613
theorem B1732835 : Blo 1152637 1732835 := bstep (se 1 (by rfl) ⟨1299626, by rfl⟩ : syracuseStep 1732835 = 2599253) B2599253
theorem B2224369 : Blo 1152637 2224369 := bstep (se 2 (by rfl) ⟨834138, by rfl⟩ : syracuseStep 2224369 = 1668277) B1668277
theorem B1732865 : Blo 1152637 1732865 := bstep (se 2 (by rfl) ⟨649824, by rfl⟩ : syracuseStep 1732865 = 1299649) B1299649
theorem B1732883 : Blo 1152637 1732883 := bstep (se 1 (by rfl) ⟨1299662, by rfl⟩ : syracuseStep 1732883 = 2599325) B2599325
theorem B1732913 : Blo 1152637 1732913 := bstep (se 2 (by rfl) ⟨649842, by rfl⟩ : syracuseStep 1732913 = 1299685) B1299685
theorem B1732931 : Blo 1152637 1732931 := bstep (se 1 (by rfl) ⟨1299698, by rfl⟩ : syracuseStep 1732931 = 2599397) B2599397
theorem B1732961 : Blo 1152637 1732961 := bstep (se 2 (by rfl) ⟨649860, by rfl⟩ : syracuseStep 1732961 = 1299721) B1299721
theorem B1732979 : Blo 1152637 1732979 := bstep (se 1 (by rfl) ⟨1299734, by rfl⟩ : syracuseStep 1732979 = 2599469) B2599469
theorem B1733009 : Blo 1152637 1733009 := bstep (se 2 (by rfl) ⟨649878, by rfl⟩ : syracuseStep 1733009 = 1299757) B1299757
theorem B1733027 : Blo 1152637 1733027 := bstep (se 1 (by rfl) ⟨1299770, by rfl⟩ : syracuseStep 1733027 = 2599541) B2599541
theorem B1733057 : Blo 1152637 1733057 := bstep (se 2 (by rfl) ⟨649896, by rfl⟩ : syracuseStep 1733057 = 1299793) B1299793
theorem B1733075 : Blo 1152637 1733075 := bstep (se 1 (by rfl) ⟨1299806, by rfl⟩ : syracuseStep 1733075 = 2599613) B2599613
theorem B1733105 : Blo 1152637 1733105 := bstep (se 2 (by rfl) ⟨649914, by rfl⟩ : syracuseStep 1733105 = 1299829) B1299829
theorem B1733123 : Blo 1152637 1733123 := bstep (se 1 (by rfl) ⟨1299842, by rfl⟩ : syracuseStep 1733123 = 2599685) B2599685
theorem B1733153 : Blo 1152637 1733153 := bstep (se 2 (by rfl) ⟨649932, by rfl⟩ : syracuseStep 1733153 = 1299865) B1299865
theorem B1733171 : Blo 1152637 1733171 := bstep (se 1 (by rfl) ⟨1299878, by rfl⟩ : syracuseStep 1733171 = 2599757) B2599757
theorem B1733201 : Blo 1152637 1733201 := bstep (se 2 (by rfl) ⟨649950, by rfl⟩ : syracuseStep 1733201 = 1299901) B1299901
theorem B1733219 : Blo 1152637 1733219 := bstep (se 1 (by rfl) ⟨1299914, by rfl⟩ : syracuseStep 1733219 = 2599829) B2599829
theorem B1733249 : Blo 1152637 1733249 := bstep (se 2 (by rfl) ⟨649968, by rfl⟩ : syracuseStep 1733249 = 1299937) B1299937
theorem B1733267 : Blo 1152637 1733267 := bstep (se 1 (by rfl) ⟨1299950, by rfl⟩ : syracuseStep 1733267 = 2599901) B2599901
theorem B2192035 : Blo 1152637 2192035 := bstep (se 1 (by rfl) ⟨1644026, by rfl⟩ : syracuseStep 2192035 = 3288053) B3288053
theorem B1733297 : Blo 1152637 1733297 := bstep (se 2 (by rfl) ⟨649986, by rfl⟩ : syracuseStep 1733297 = 1299973) B1299973
theorem B1733315 : Blo 1152637 1733315 := bstep (se 1 (by rfl) ⟨1299986, by rfl⟩ : syracuseStep 1733315 = 2599973) B2599973
theorem B1733345 : Blo 1152637 1733345 := bstep (se 2 (by rfl) ⟨650004, by rfl⟩ : syracuseStep 1733345 = 1300009) B1300009
theorem B3896045 : Blo 1152637 3896045 := bstep (se 3 (by rfl) ⟨730508, by rfl⟩ : syracuseStep 3896045 = 1461017) B1461017
theorem B1733363 : Blo 1152637 1733363 := bstep (se 1 (by rfl) ⟨1300022, by rfl⟩ : syracuseStep 1733363 = 2600045) B2600045
theorem B1733393 : Blo 1152637 1733393 := bstep (se 2 (by rfl) ⟨650022, by rfl⟩ : syracuseStep 1733393 = 1300045) B1300045
theorem B3896099 : Blo 1152637 3896099 := bstep (se 1 (by rfl) ⟨2922074, by rfl⟩ : syracuseStep 3896099 = 5844149) B5844149
theorem B1733411 : Blo 1152637 1733411 := bstep (se 1 (by rfl) ⟨1300058, by rfl⟩ : syracuseStep 1733411 = 2600117) B2600117
theorem B1733441 : Blo 1152637 1733441 := bstep (se 2 (by rfl) ⟨650040, by rfl⟩ : syracuseStep 1733441 = 1300081) B1300081
theorem B3699533 : Blo 1152637 3699533 := bstep (se 3 (by rfl) ⟨693662, by rfl⟩ : syracuseStep 3699533 = 1387325) B1387325
theorem B1733459 : Blo 1152637 1733459 := bstep (se 1 (by rfl) ⟨1300094, by rfl⟩ : syracuseStep 1733459 = 2600189) B2600189
theorem B1733489 : Blo 1152637 1733489 := bstep (se 2 (by rfl) ⟨650058, by rfl⟩ : syracuseStep 1733489 = 1300117) B1300117
theorem B1733507 : Blo 1152637 1733507 := bstep (se 1 (by rfl) ⟨1300130, by rfl⟩ : syracuseStep 1733507 = 2600261) B2600261
theorem B1733537 : Blo 1152637 1733537 := bstep (se 2 (by rfl) ⟨650076, by rfl⟩ : syracuseStep 1733537 = 1300153) B1300153
theorem B1733555 : Blo 1152637 1733555 := bstep (se 1 (by rfl) ⟨1300166, by rfl⟩ : syracuseStep 1733555 = 2600333) B2600333
theorem B1733585 : Blo 1152637 1733585 := bstep (se 2 (by rfl) ⟨650094, by rfl⟩ : syracuseStep 1733585 = 1300189) B1300189
theorem B1733603 : Blo 1152637 1733603 := bstep (se 1 (by rfl) ⟨1300202, by rfl⟩ : syracuseStep 1733603 = 2600405) B2600405
theorem B1733633 : Blo 1152637 1733633 := bstep (se 2 (by rfl) ⟨650112, by rfl⟩ : syracuseStep 1733633 = 1300225) B1300225
theorem B1733651 : Blo 1152637 1733651 := bstep (se 1 (by rfl) ⟨1300238, by rfl⟩ : syracuseStep 1733651 = 2600477) B2600477
theorem B3896369 : Blo 1152637 3896369 := bstep (se 2 (by rfl) ⟨1461138, by rfl⟩ : syracuseStep 3896369 = 2922277) B2922277
theorem B1733681 : Blo 1152637 1733681 := bstep (se 2 (by rfl) ⟨650130, by rfl⟩ : syracuseStep 1733681 = 1300261) B1300261
theorem B1733699 : Blo 1152637 1733699 := bstep (se 1 (by rfl) ⟨1300274, by rfl⟩ : syracuseStep 1733699 = 2600549) B2600549
theorem B1733729 : Blo 1152637 1733729 := bstep (se 2 (by rfl) ⟨650148, by rfl⟩ : syracuseStep 1733729 = 1300297) B1300297
theorem B2192483 : Blo 1152637 2192483 := bstep (se 1 (by rfl) ⟨1644362, by rfl⟩ : syracuseStep 2192483 = 3288725) B3288725
theorem B1733747 : Blo 1152637 1733747 := bstep (se 1 (by rfl) ⟨1300310, by rfl⟩ : syracuseStep 1733747 = 2600621) B2600621
theorem B1733777 : Blo 1152637 1733777 := bstep (se 2 (by rfl) ⟨650166, by rfl⟩ : syracuseStep 1733777 = 1300333) B1300333
theorem B4388003 : Blo 1152637 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B1733795 : Blo 1152637 1733795 := bstep (se 1 (by rfl) ⟨1300346, by rfl⟩ : syracuseStep 1733795 = 2600693) B2600693
theorem B1733825 : Blo 1152637 1733825 := bstep (se 2 (by rfl) ⟨650184, by rfl⟩ : syracuseStep 1733825 = 1300369) B1300369
theorem B1733843 : Blo 1152637 1733843 := bstep (se 1 (by rfl) ⟨1300382, by rfl⟩ : syracuseStep 1733843 = 2600765) B2600765
theorem B1733873 : Blo 1152637 1733873 := bstep (se 2 (by rfl) ⟨650202, by rfl⟩ : syracuseStep 1733873 = 1300405) B1300405
theorem B1733891 : Blo 1152637 1733891 := bstep (se 1 (by rfl) ⟨1300418, by rfl⟩ : syracuseStep 1733891 = 2600837) B2600837
theorem B1733921 : Blo 1152637 1733921 := bstep (se 2 (by rfl) ⟨650220, by rfl⟩ : syracuseStep 1733921 = 1300441) B1300441
theorem B1733939 : Blo 1152637 1733939 := bstep (se 1 (by rfl) ⟨1300454, by rfl⟩ : syracuseStep 1733939 = 2600909) B2600909
theorem B1733969 : Blo 1152637 1733969 := bstep (se 2 (by rfl) ⟨650238, by rfl⟩ : syracuseStep 1733969 = 1300477) B1300477
theorem B1733987 : Blo 1152637 1733987 := bstep (se 1 (by rfl) ⟨1300490, by rfl⟩ : syracuseStep 1733987 = 2600981) B2600981
theorem B1734017 : Blo 1152637 1734017 := bstep (se 2 (by rfl) ⟨650256, by rfl⟩ : syracuseStep 1734017 = 1300513) B1300513
theorem B2192771 : Blo 1152637 2192771 := bstep (se 1 (by rfl) ⟨1644578, by rfl⟩ : syracuseStep 2192771 = 3289157) B3289157
theorem B1734035 : Blo 1152637 1734035 := bstep (se 1 (by rfl) ⟨1300526, by rfl⟩ : syracuseStep 1734035 = 2601053) B2601053
theorem B1734065 : Blo 1152637 1734065 := bstep (se 2 (by rfl) ⟨650274, by rfl⟩ : syracuseStep 1734065 = 1300549) B1300549
theorem B1734083 : Blo 1152637 1734083 := bstep (se 1 (by rfl) ⟨1300562, by rfl⟩ : syracuseStep 1734083 = 2601125) B2601125
theorem B1734113 : Blo 1152637 1734113 := bstep (se 2 (by rfl) ⟨650292, by rfl⟩ : syracuseStep 1734113 = 1300585) B1300585
theorem B1734131 : Blo 1152637 1734131 := bstep (se 1 (by rfl) ⟨1300598, by rfl⟩ : syracuseStep 1734131 = 2601197) B2601197
theorem B1734161 : Blo 1152637 1734161 := bstep (se 2 (by rfl) ⟨650310, by rfl⟩ : syracuseStep 1734161 = 1300621) B1300621
theorem B1734179 : Blo 1152637 1734179 := bstep (se 1 (by rfl) ⟨1300634, by rfl⟩ : syracuseStep 1734179 = 2601269) B2601269
theorem B1734209 : Blo 1152637 1734209 := bstep (se 2 (by rfl) ⟨650328, by rfl⟩ : syracuseStep 1734209 = 1300657) B1300657
theorem B3896909 : Blo 1152637 3896909 := bstep (se 3 (by rfl) ⟨730670, by rfl⟩ : syracuseStep 3896909 = 1461341) B1461341
theorem B1734227 : Blo 1152637 1734227 := bstep (se 1 (by rfl) ⟨1300670, by rfl⟩ : syracuseStep 1734227 = 2601341) B2601341
theorem B1734257 : Blo 1152637 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B3896963 : Blo 1152637 3896963 := bstep (se 1 (by rfl) ⟨2922722, by rfl⟩ : syracuseStep 3896963 = 5845445) B5845445
theorem B1734275 : Blo 1152637 1734275 := bstep (se 1 (by rfl) ⟨1300706, by rfl⟩ : syracuseStep 1734275 = 2601413) B2601413
theorem B1734305 : Blo 1152637 1734305 := bstep (se 2 (by rfl) ⟨650364, by rfl⟩ : syracuseStep 1734305 = 1300729) B1300729
theorem B1734323 : Blo 1152637 1734323 := bstep (se 1 (by rfl) ⟨1300742, by rfl⟩ : syracuseStep 1734323 = 2601485) B2601485
theorem B1734353 : Blo 1152637 1734353 := bstep (se 2 (by rfl) ⟨650382, by rfl⟩ : syracuseStep 1734353 = 1300765) B1300765
theorem B1734371 : Blo 1152637 1734371 := bstep (se 1 (by rfl) ⟨1300778, by rfl⟩ : syracuseStep 1734371 = 2601557) B2601557
theorem B1734401 : Blo 1152637 1734401 := bstep (se 2 (by rfl) ⟨650400, by rfl⟩ : syracuseStep 1734401 = 1300801) B1300801
theorem B1734419 : Blo 1152637 1734419 := bstep (se 1 (by rfl) ⟨1300814, by rfl⟩ : syracuseStep 1734419 = 2601629) B2601629
theorem B1734449 : Blo 1152637 1734449 := bstep (se 2 (by rfl) ⟨650418, by rfl⟩ : syracuseStep 1734449 = 1300837) B1300837
theorem B1734467 : Blo 1152637 1734467 := bstep (se 1 (by rfl) ⟨1300850, by rfl⟩ : syracuseStep 1734467 = 2601701) B2601701
theorem B8779589 : Blo 1152637 8779589 := bstep (se 4 (by rfl) ⟨823086, by rfl⟩ : syracuseStep 8779589 = 1646173) B1646173
theorem B1734497 : Blo 1152637 1734497 := bstep (se 2 (by rfl) ⟨650436, by rfl⟩ : syracuseStep 1734497 = 1300873) B1300873
theorem B2815843 : Blo 1152637 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1734515 : Blo 1152637 1734515 := bstep (se 1 (by rfl) ⟨1300886, by rfl⟩ : syracuseStep 1734515 = 2601773) B2601773
theorem B3897233 : Blo 1152637 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B1734545 : Blo 1152637 1734545 := bstep (se 2 (by rfl) ⟨650454, by rfl⟩ : syracuseStep 1734545 = 1300909) B1300909
theorem B1734563 : Blo 1152637 1734563 := bstep (se 1 (by rfl) ⟨1300922, by rfl⟩ : syracuseStep 1734563 = 2601845) B2601845
theorem B1734593 : Blo 1152637 1734593 := bstep (se 2 (by rfl) ⟨650472, by rfl⟩ : syracuseStep 1734593 = 1300945) B1300945
theorem B1734611 : Blo 1152637 1734611 := bstep (se 1 (by rfl) ⟨1300958, by rfl⟩ : syracuseStep 1734611 = 2601917) B2601917
theorem B1734641 : Blo 1152637 1734641 := bstep (se 2 (by rfl) ⟨650490, by rfl⟩ : syracuseStep 1734641 = 1300981) B1300981
theorem B1734659 : Blo 1152637 1734659 := bstep (se 1 (by rfl) ⟨1300994, by rfl⟩ : syracuseStep 1734659 = 2601989) B2601989
theorem B1734689 : Blo 1152637 1734689 := bstep (se 2 (by rfl) ⟨650508, by rfl⟩ : syracuseStep 1734689 = 1301017) B1301017
theorem B1734707 : Blo 1152637 1734707 := bstep (se 1 (by rfl) ⟨1301030, by rfl⟩ : syracuseStep 1734707 = 2602061) B2602061
theorem B15005749 : Blo 1152637 15005749 := bstep (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) B1406789
theorem B1734737 : Blo 1152637 1734737 := bstep (se 2 (by rfl) ⟨650526, by rfl⟩ : syracuseStep 1734737 = 1301053) B1301053
theorem B1734755 : Blo 1152637 1734755 := bstep (se 1 (by rfl) ⟨1301066, by rfl⟩ : syracuseStep 1734755 = 2602133) B2602133
theorem B1734785 : Blo 1152637 1734785 := bstep (se 2 (by rfl) ⟨650544, by rfl⟩ : syracuseStep 1734785 = 1301089) B1301089
theorem B4389005 : Blo 1152637 4389005 := bstep (se 3 (by rfl) ⟨822938, by rfl⟩ : syracuseStep 4389005 = 1645877) B1645877
theorem B1734803 : Blo 1152637 1734803 := bstep (se 1 (by rfl) ⟨1301102, by rfl⟩ : syracuseStep 1734803 = 2602205) B2602205
theorem B1734833 : Blo 1152637 1734833 := bstep (se 2 (by rfl) ⟨650562, by rfl⟩ : syracuseStep 1734833 = 1301125) B1301125
theorem B1734851 : Blo 1152637 1734851 := bstep (se 1 (by rfl) ⟨1301138, by rfl⟩ : syracuseStep 1734851 = 2602277) B2602277
theorem B1734881 : Blo 1152637 1734881 := bstep (se 2 (by rfl) ⟨650580, by rfl⟩ : syracuseStep 1734881 = 1301161) B1301161
theorem B1734899 : Blo 1152637 1734899 := bstep (se 1 (by rfl) ⟨1301174, by rfl⟩ : syracuseStep 1734899 = 2602349) B2602349
theorem B1734929 : Blo 1152637 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B1734947 : Blo 1152637 1734947 := bstep (se 1 (by rfl) ⟨1301210, by rfl⟩ : syracuseStep 1734947 = 2602421) B2602421
theorem B2193713 : Blo 1152637 2193713 := bstep (se 2 (by rfl) ⟨822642, by rfl⟩ : syracuseStep 2193713 = 1645285) B1645285
theorem B3701123 : Blo 1152637 3701123 := bstep (se 1 (by rfl) ⟨2775842, by rfl⟩ : syracuseStep 3701123 = 5551685) B5551685
theorem B3897773 : Blo 1152637 3897773 := bstep (se 3 (by rfl) ⟨730832, by rfl⟩ : syracuseStep 3897773 = 1461665) B1461665
theorem B3897827 : Blo 1152637 3897827 := bstep (se 1 (by rfl) ⟨2923370, by rfl⟩ : syracuseStep 3897827 = 5846741) B5846741
theorem B3701315 : Blo 1152637 3701315 := bstep (se 1 (by rfl) ⟨2775986, by rfl⟩ : syracuseStep 3701315 = 5551973) B5551973
theorem B3898097 : Blo 1152637 3898097 := bstep (se 2 (by rfl) ⟨1461786, by rfl⟩ : syracuseStep 3898097 = 2923573) B2923573
theorem B4684657 : Blo 1152637 4684657 := bstep (se 2 (by rfl) ⟨1756746, by rfl⟩ : syracuseStep 4684657 = 3513493) B3513493
theorem B10517489 : Blo 1152637 10517489 := bstep (se 2 (by rfl) ⟨3944058, by rfl⟩ : syracuseStep 10517489 = 7888117) B7888117
theorem B6585421 : Blo 1152637 6585421 := bstep (se 3 (by rfl) ⟨1234766, by rfl⟩ : syracuseStep 6585421 = 2469533) B2469533
theorem B2194609 : Blo 1152637 2194609 := bstep (se 2 (by rfl) ⟨822978, by rfl⟩ : syracuseStep 2194609 = 1645957) B1645957
theorem B3701969 : Blo 1152637 3701969 := bstep (se 2 (by rfl) ⟨1388238, by rfl⟩ : syracuseStep 3701969 = 2776477) B2776477
theorem B4160753 : Blo 1152637 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B3898637 : Blo 1152637 3898637 := bstep (se 3 (by rfl) ⟨730994, by rfl⟩ : syracuseStep 3898637 = 1461989) B1461989
theorem B3898691 : Blo 1152637 3898691 := bstep (se 1 (by rfl) ⟨2924018, by rfl⟩ : syracuseStep 3898691 = 5848037) B5848037
theorem B2194769 : Blo 1152637 2194769 := bstep (se 2 (by rfl) ⟨823038, by rfl⟩ : syracuseStep 2194769 = 1646077) B1646077
theorem B4816397 : Blo 1152637 4816397 := bstep (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) B1806149
theorem B7405091 : Blo 1152637 7405091 := bstep (se 1 (by rfl) ⟨5553818, by rfl⟩ : syracuseStep 7405091 = 11107637) B11107637
theorem B3898961 : Blo 1152637 3898961 := bstep (se 2 (by rfl) ⟨1462110, by rfl⟩ : syracuseStep 3898961 = 2924221) B2924221
theorem B3505805 : Blo 1152637 3505805 := bstep (se 3 (by rfl) ⟨657338, by rfl⟩ : syracuseStep 3505805 = 1314677) B1314677
theorem B2195171 : Blo 1152637 2195171 := bstep (se 1 (by rfl) ⟨1646378, by rfl⟩ : syracuseStep 2195171 = 3292757) B3292757
theorem B19005475 : Blo 1152637 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B3899609 : Blo 1152637 3899609 := bstep (se 2 (by rfl) ⟨1462353, by rfl⟩ : syracuseStep 3899609 = 2924707) B2924707
theorem B8323373 : Blo 1152637 8323373 := bstep (se 3 (by rfl) ⟨1560632, by rfl⟩ : syracuseStep 8323373 = 3121265) B3121265
theorem B14811457 : Blo 1152637 14811457 := bstep (se 2 (by rfl) ⟨5554296, by rfl⟩ : syracuseStep 14811457 = 11108593) B11108593
theorem B29590109 : Blo 1152637 29590109 := bstep (se 3 (by rfl) ⟨5548145, by rfl⟩ : syracuseStep 29590109 = 11096291) B11096291
theorem B4391603 : Blo 1152637 4391603 := bstep (se 1 (by rfl) ⟨3293702, by rfl⟩ : syracuseStep 4391603 = 6587405) B6587405
theorem B4162265 : Blo 1152637 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B6587153 : Blo 1152637 6587153 := bstep (se 2 (by rfl) ⟨2470182, by rfl⟩ : syracuseStep 6587153 = 4940365) B4940365
theorem B3900311 : Blo 1152637 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B13140953 : Blo 1152637 13140953 := bstep (se 2 (by rfl) ⟨4927857, by rfl⟩ : syracuseStep 13140953 = 9855715) B9855715
theorem B2917721 : Blo 1152637 2917721 := bstep (se 2 (by rfl) ⟨1094145, by rfl⟩ : syracuseStep 2917721 = 2188291) B2188291
theorem B3900851 : Blo 1152637 3900851 := bstep (se 1 (by rfl) ⟨2925638, by rfl⟩ : syracuseStep 3900851 = 5851277) B5851277
theorem B5539421 : Blo 1152637 5539421 := bstep (se 3 (by rfl) ⟨1038641, by rfl⟩ : syracuseStep 5539421 = 2077283) B2077283
theorem B3901121 : Blo 1152637 3901121 := bstep (se 2 (by rfl) ⟨1462920, by rfl⟩ : syracuseStep 3901121 = 2925841) B2925841
theorem B4163417 : Blo 1152637 4163417 := bstep (se 2 (by rfl) ⟨1561281, by rfl⟩ : syracuseStep 4163417 = 3122563) B3122563
theorem B2918551 : Blo 1152637 2918551 := bstep (se 1 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 2918551 = 4377827) B4377827
theorem B9865421 : Blo 1152637 9865421 := bstep (se 3 (by rfl) ⟨1849766, by rfl⟩ : syracuseStep 9865421 = 3699533) B3699533
theorem B3901661 : Blo 1152637 3901661 := bstep (se 3 (by rfl) ⟨731561, by rfl⟩ : syracuseStep 3901661 = 1463123) B1463123
theorem B1247735 : Blo 1152637 1247735 := bstep (se 1 (by rfl) ⟨935801, by rfl⟩ : syracuseStep 1247735 = 1871603) B1871603
theorem B2918987 : Blo 1152637 2918987 := bstep (se 1 (by rfl) ⟨2189240, by rfl⟩ : syracuseStep 2918987 = 4378481) B4378481
theorem B2919361 : Blo 1152637 2919361 := bstep (se 2 (by rfl) ⟨1094760, by rfl⟩ : syracuseStep 2919361 = 2189521) B2189521
theorem B25660567 : Blo 1152637 25660567 := bstep (se 1 (by rfl) ⟨19245425, by rfl⟩ : syracuseStep 25660567 = 38490851) B38490851
theorem B5836049 : Blo 1152637 5836049 := bstep (se 2 (by rfl) ⟨2188518, by rfl⟩ : syracuseStep 5836049 = 4377037) B4377037
theorem B3902795 : Blo 1152637 3902795 := bstep (se 1 (by rfl) ⟨2927096, by rfl⟩ : syracuseStep 3902795 = 5854193) B5854193
theorem B8326577 : Blo 1152637 8326577 := bstep (se 2 (by rfl) ⟨3122466, by rfl⟩ : syracuseStep 8326577 = 6244933) B6244933
theorem B5836211 : Blo 1152637 5836211 := bstep (se 1 (by rfl) ⟨4377158, by rfl⟩ : syracuseStep 5836211 = 8754317) B8754317
theorem B2919959 : Blo 1152637 2919959 := bstep (se 1 (by rfl) ⟨2189969, by rfl⟩ : syracuseStep 2919959 = 4379939) B4379939
theorem B3903065 : Blo 1152637 3903065 := bstep (se 2 (by rfl) ⟨1463649, by rfl⟩ : syracuseStep 3903065 = 2927299) B2927299
theorem B7212637 : Blo 1152637 7212637 := bstep (se 3 (by rfl) ⟨1352369, by rfl⟩ : syracuseStep 7212637 = 2704739) B2704739
theorem B2166401 : Blo 1152637 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B16617221 : Blo 1152637 16617221 := bstep (se 4 (by rfl) ⟨1557864, by rfl⟩ : syracuseStep 16617221 = 3115729) B3115729
theorem B8327063 : Blo 1152637 8327063 := bstep (se 1 (by rfl) ⟨6245297, by rfl⟩ : syracuseStep 8327063 = 12490595) B12490595
theorem B4165825 : Blo 1152637 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B20254961 : Blo 1152637 20254961 := bstep (se 2 (by rfl) ⟨7595610, by rfl⟩ : syracuseStep 20254961 = 15191221) B15191221
theorem B2920769 : Blo 1152637 2920769 := bstep (se 2 (by rfl) ⟨1095288, by rfl⟩ : syracuseStep 2920769 = 2190577) B2190577
theorem B1643161 : Blo 1152637 1643161 := bstep (se 2 (by rfl) ⟨616185, by rfl⟩ : syracuseStep 1643161 = 1232371) B1232371
theorem B2593547 : Blo 1152637 2593547 := bstep (se 1 (by rfl) ⟨1945160, by rfl⟩ : syracuseStep 2593547 = 3890321) B3890321
theorem B2593601 : Blo 1152637 2593601 := bstep (se 2 (by rfl) ⟨972600, by rfl⟩ : syracuseStep 2593601 = 1945201) B1945201
theorem B2921305 : Blo 1152637 2921305 := bstep (se 2 (by rfl) ⟨1095489, by rfl⟩ : syracuseStep 2921305 = 2190979) B2190979
theorem B2593817 : Blo 1152637 2593817 := bstep (se 2 (by rfl) ⟨972681, by rfl⟩ : syracuseStep 2593817 = 1945363) B1945363
theorem B2593907 : Blo 1152637 2593907 := bstep (se 1 (by rfl) ⟨1945430, by rfl⟩ : syracuseStep 2593907 = 3890861) B3890861
theorem B2593943 : Blo 1152637 2593943 := bstep (se 1 (by rfl) ⟨1945457, by rfl⟩ : syracuseStep 2593943 = 3890915) B3890915
theorem B2463041 : Blo 1152637 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B2594123 : Blo 1152637 2594123 := bstep (se 1 (by rfl) ⟨1945592, by rfl⟩ : syracuseStep 2594123 = 3891185) B3891185
theorem B5838155 : Blo 1152637 5838155 := bstep (se 1 (by rfl) ⟨4378616, by rfl⟩ : syracuseStep 5838155 = 8757233) B8757233
theorem B2594177 : Blo 1152637 2594177 := bstep (se 2 (by rfl) ⟨972816, by rfl⟩ : syracuseStep 2594177 = 1945633) B1945633
theorem B2594393 : Blo 1152637 2594393 := bstep (se 2 (by rfl) ⟨972897, by rfl⟩ : syracuseStep 2594393 = 1945795) B1945795
theorem B1152651 : Blo 1152637 1152651 := bstep (se 1 (by rfl) ⟨864488, by rfl⟩ : syracuseStep 1152651 = 1728977) B1728977
theorem B1152663 : Blo 1152637 1152663 := bstep (se 1 (by rfl) ⟨864497, by rfl⟩ : syracuseStep 1152663 = 1728995) B1728995
theorem B1152683 : Blo 1152637 1152683 := bstep (se 1 (by rfl) ⟨864512, by rfl⟩ : syracuseStep 1152683 = 1729025) B1729025
theorem B2594483 : Blo 1152637 2594483 := bstep (se 1 (by rfl) ⟨1945862, by rfl⟩ : syracuseStep 2594483 = 3891725) B3891725
theorem B1152695 : Blo 1152637 1152695 := bstep (se 1 (by rfl) ⟨864521, by rfl⟩ : syracuseStep 1152695 = 1729043) B1729043
theorem B1152715 : Blo 1152637 1152715 := bstep (se 1 (by rfl) ⟨864536, by rfl⟩ : syracuseStep 1152715 = 1729073) B1729073
theorem B1152727 : Blo 1152637 1152727 := bstep (se 1 (by rfl) ⟨864545, by rfl⟩ : syracuseStep 1152727 = 1729091) B1729091
theorem B2594519 : Blo 1152637 2594519 := bstep (se 1 (by rfl) ⟨1945889, by rfl⟩ : syracuseStep 2594519 = 3891779) B3891779
theorem B1152747 : Blo 1152637 1152747 := bstep (se 1 (by rfl) ⟨864560, by rfl⟩ : syracuseStep 1152747 = 1729121) B1729121
theorem B1152759 : Blo 1152637 1152759 := bstep (se 1 (by rfl) ⟨864569, by rfl⟩ : syracuseStep 1152759 = 1729139) B1729139
theorem B1152779 : Blo 1152637 1152779 := bstep (se 1 (by rfl) ⟨864584, by rfl⟩ : syracuseStep 1152779 = 1729169) B1729169
theorem B1152791 : Blo 1152637 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B1152811 : Blo 1152637 1152811 := bstep (se 1 (by rfl) ⟨864608, by rfl⟩ : syracuseStep 1152811 = 1729217) B1729217
theorem B1152823 : Blo 1152637 1152823 := bstep (se 1 (by rfl) ⟨864617, by rfl⟩ : syracuseStep 1152823 = 1729235) B1729235
theorem B1152843 : Blo 1152637 1152843 := bstep (se 1 (by rfl) ⟨864632, by rfl⟩ : syracuseStep 1152843 = 1729265) B1729265
theorem B1152855 : Blo 1152637 1152855 := bstep (se 1 (by rfl) ⟨864641, by rfl⟩ : syracuseStep 1152855 = 1729283) B1729283
theorem B1152875 : Blo 1152637 1152875 := bstep (se 1 (by rfl) ⟨864656, by rfl⟩ : syracuseStep 1152875 = 1729313) B1729313
theorem B1152887 : Blo 1152637 1152887 := bstep (se 1 (by rfl) ⟨864665, by rfl⟩ : syracuseStep 1152887 = 1729331) B1729331
theorem B1152907 : Blo 1152637 1152907 := bstep (se 1 (by rfl) ⟨864680, by rfl⟩ : syracuseStep 1152907 = 1729361) B1729361
theorem B2594699 : Blo 1152637 2594699 := bstep (se 1 (by rfl) ⟨1946024, by rfl⟩ : syracuseStep 2594699 = 3892049) B3892049
theorem B1152919 : Blo 1152637 1152919 := bstep (se 1 (by rfl) ⟨864689, by rfl⟩ : syracuseStep 1152919 = 1729379) B1729379
theorem B1152939 : Blo 1152637 1152939 := bstep (se 1 (by rfl) ⟨864704, by rfl⟩ : syracuseStep 1152939 = 1729409) B1729409
theorem B2922419 : Blo 1152637 2922419 := bstep (se 1 (by rfl) ⟨2191814, by rfl⟩ : syracuseStep 2922419 = 4383629) B4383629
theorem B8329139 : Blo 1152637 8329139 := bstep (se 1 (by rfl) ⟨6246854, by rfl⟩ : syracuseStep 8329139 = 12493709) B12493709
theorem B1152951 : Blo 1152637 1152951 := bstep (se 1 (by rfl) ⟨864713, by rfl⟩ : syracuseStep 1152951 = 1729427) B1729427
theorem B2594753 : Blo 1152637 2594753 := bstep (se 2 (by rfl) ⟨973032, by rfl⟩ : syracuseStep 2594753 = 1946065) B1946065
theorem B1152971 : Blo 1152637 1152971 := bstep (se 1 (by rfl) ⟨864728, by rfl⟩ : syracuseStep 1152971 = 1729457) B1729457
theorem B1152983 : Blo 1152637 1152983 := bstep (se 1 (by rfl) ⟨864737, by rfl⟩ : syracuseStep 1152983 = 1729475) B1729475
theorem B1153003 : Blo 1152637 1153003 := bstep (se 1 (by rfl) ⟨864752, by rfl⟩ : syracuseStep 1153003 = 1729505) B1729505
theorem B1153015 : Blo 1152637 1153015 := bstep (se 1 (by rfl) ⟨864761, by rfl⟩ : syracuseStep 1153015 = 1729523) B1729523
theorem B1153035 : Blo 1152637 1153035 := bstep (se 1 (by rfl) ⟨864776, by rfl⟩ : syracuseStep 1153035 = 1729553) B1729553
theorem B1153047 : Blo 1152637 1153047 := bstep (se 1 (by rfl) ⟨864785, by rfl⟩ : syracuseStep 1153047 = 1729571) B1729571
theorem B1153067 : Blo 1152637 1153067 := bstep (se 1 (by rfl) ⟨864800, by rfl⟩ : syracuseStep 1153067 = 1729601) B1729601
theorem B1153079 : Blo 1152637 1153079 := bstep (se 1 (by rfl) ⟨864809, by rfl⟩ : syracuseStep 1153079 = 1729619) B1729619
theorem B1153099 : Blo 1152637 1153099 := bstep (se 1 (by rfl) ⟨864824, by rfl⟩ : syracuseStep 1153099 = 1729649) B1729649
theorem B1644619 : Blo 1152637 1644619 := bstep (se 1 (by rfl) ⟨1233464, by rfl⟩ : syracuseStep 1644619 = 2466929) B2466929
theorem B1153111 : Blo 1152637 1153111 := bstep (se 1 (by rfl) ⟨864833, by rfl⟩ : syracuseStep 1153111 = 1729667) B1729667
theorem B1153131 : Blo 1152637 1153131 := bstep (se 1 (by rfl) ⟨864848, by rfl⟩ : syracuseStep 1153131 = 1729697) B1729697
theorem B1153143 : Blo 1152637 1153143 := bstep (se 1 (by rfl) ⟨864857, by rfl⟩ : syracuseStep 1153143 = 1729715) B1729715
theorem B1153163 : Blo 1152637 1153163 := bstep (se 1 (by rfl) ⟨864872, by rfl⟩ : syracuseStep 1153163 = 1729745) B1729745
theorem B1153175 : Blo 1152637 1153175 := bstep (se 1 (by rfl) ⟨864881, by rfl⟩ : syracuseStep 1153175 = 1729763) B1729763
theorem B2463895 : Blo 1152637 2463895 := bstep (se 1 (by rfl) ⟨1847921, by rfl⟩ : syracuseStep 2463895 = 3695843) B3695843
theorem B2594969 : Blo 1152637 2594969 := bstep (se 2 (by rfl) ⟨973113, by rfl⟩ : syracuseStep 2594969 = 1946227) B1946227
theorem B1153195 : Blo 1152637 1153195 := bstep (se 1 (by rfl) ⟨864896, by rfl⟩ : syracuseStep 1153195 = 1729793) B1729793
theorem B1153207 : Blo 1152637 1153207 := bstep (se 1 (by rfl) ⟨864905, by rfl⟩ : syracuseStep 1153207 = 1729811) B1729811
theorem B1153227 : Blo 1152637 1153227 := bstep (se 1 (by rfl) ⟨864920, by rfl⟩ : syracuseStep 1153227 = 1729841) B1729841
theorem B1153239 : Blo 1152637 1153239 := bstep (se 1 (by rfl) ⟨864929, by rfl⟩ : syracuseStep 1153239 = 1729859) B1729859
theorem B2922713 : Blo 1152637 2922713 := bstep (se 2 (by rfl) ⟨1096017, by rfl⟩ : syracuseStep 2922713 = 2192035) B2192035
theorem B1153259 : Blo 1152637 1153259 := bstep (se 1 (by rfl) ⟨864944, by rfl⟩ : syracuseStep 1153259 = 1729889) B1729889
theorem B2595059 : Blo 1152637 2595059 := bstep (se 1 (by rfl) ⟨1946294, by rfl⟩ : syracuseStep 2595059 = 3892589) B3892589
theorem B1153271 : Blo 1152637 1153271 := bstep (se 1 (by rfl) ⟨864953, by rfl⟩ : syracuseStep 1153271 = 1729907) B1729907
theorem B1153291 : Blo 1152637 1153291 := bstep (se 1 (by rfl) ⟨864968, by rfl⟩ : syracuseStep 1153291 = 1729937) B1729937
theorem B1153303 : Blo 1152637 1153303 := bstep (se 1 (by rfl) ⟨864977, by rfl⟩ : syracuseStep 1153303 = 1729955) B1729955
theorem B2595095 : Blo 1152637 2595095 := bstep (se 1 (by rfl) ⟨1946321, by rfl⟩ : syracuseStep 2595095 = 3892643) B3892643
theorem B1153323 : Blo 1152637 1153323 := bstep (se 1 (by rfl) ⟨864992, by rfl⟩ : syracuseStep 1153323 = 1729985) B1729985
theorem B1153335 : Blo 1152637 1153335 := bstep (se 1 (by rfl) ⟨865001, by rfl⟩ : syracuseStep 1153335 = 1730003) B1730003
theorem B3512641 : Blo 1152637 3512641 := bstep (se 2 (by rfl) ⟨1317240, by rfl⟩ : syracuseStep 3512641 = 2634481) B2634481
theorem B1153355 : Blo 1152637 1153355 := bstep (se 1 (by rfl) ⟨865016, by rfl⟩ : syracuseStep 1153355 = 1730033) B1730033
theorem B1153367 : Blo 1152637 1153367 := bstep (se 1 (by rfl) ⟨865025, by rfl⟩ : syracuseStep 1153367 = 1730051) B1730051
theorem B1153387 : Blo 1152637 1153387 := bstep (se 1 (by rfl) ⟨865040, by rfl⟩ : syracuseStep 1153387 = 1730081) B1730081
theorem B1153399 : Blo 1152637 1153399 := bstep (se 1 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 1153399 = 1730099) B1730099
theorem B1153419 : Blo 1152637 1153419 := bstep (se 1 (by rfl) ⟨865064, by rfl⟩ : syracuseStep 1153419 = 1730129) B1730129
theorem B1153431 : Blo 1152637 1153431 := bstep (se 1 (by rfl) ⟨865073, by rfl⟩ : syracuseStep 1153431 = 1730147) B1730147
theorem B1153451 : Blo 1152637 1153451 := bstep (se 1 (by rfl) ⟨865088, by rfl⟩ : syracuseStep 1153451 = 1730177) B1730177
theorem B1153463 : Blo 1152637 1153463 := bstep (se 1 (by rfl) ⟨865097, by rfl⟩ : syracuseStep 1153463 = 1730195) B1730195
theorem B2595275 : Blo 1152637 2595275 := bstep (se 1 (by rfl) ⟨1946456, by rfl⟩ : syracuseStep 2595275 = 3892913) B3892913
theorem B1153483 : Blo 1152637 1153483 := bstep (se 1 (by rfl) ⟨865112, by rfl⟩ : syracuseStep 1153483 = 1730225) B1730225
theorem B1153495 : Blo 1152637 1153495 := bstep (se 1 (by rfl) ⟨865121, by rfl⟩ : syracuseStep 1153495 = 1730243) B1730243
theorem B1153515 : Blo 1152637 1153515 := bstep (se 1 (by rfl) ⟨865136, by rfl⟩ : syracuseStep 1153515 = 1730273) B1730273
theorem B1153527 : Blo 1152637 1153527 := bstep (se 1 (by rfl) ⟨865145, by rfl⟩ : syracuseStep 1153527 = 1730291) B1730291
theorem B2595329 : Blo 1152637 2595329 := bstep (se 2 (by rfl) ⟨973248, by rfl⟩ : syracuseStep 2595329 = 1946497) B1946497
theorem B1153547 : Blo 1152637 1153547 := bstep (se 1 (by rfl) ⟨865160, by rfl⟩ : syracuseStep 1153547 = 1730321) B1730321
theorem B1153559 : Blo 1152637 1153559 := bstep (se 1 (by rfl) ⟨865169, by rfl⟩ : syracuseStep 1153559 = 1730339) B1730339
theorem B1153579 : Blo 1152637 1153579 := bstep (se 1 (by rfl) ⟨865184, by rfl⟩ : syracuseStep 1153579 = 1730369) B1730369
theorem B3283507 : Blo 1152637 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B1153591 : Blo 1152637 1153591 := bstep (se 1 (by rfl) ⟨865193, by rfl⟩ : syracuseStep 1153591 = 1730387) B1730387
theorem B1153611 : Blo 1152637 1153611 := bstep (se 1 (by rfl) ⟨865208, by rfl⟩ : syracuseStep 1153611 = 1730417) B1730417
theorem B1153623 : Blo 1152637 1153623 := bstep (se 1 (by rfl) ⟨865217, by rfl⟩ : syracuseStep 1153623 = 1730435) B1730435
theorem B1153643 : Blo 1152637 1153643 := bstep (se 1 (by rfl) ⟨865232, by rfl⟩ : syracuseStep 1153643 = 1730465) B1730465
theorem B1153655 : Blo 1152637 1153655 := bstep (se 1 (by rfl) ⟨865241, by rfl⟩ : syracuseStep 1153655 = 1730483) B1730483
theorem B1153675 : Blo 1152637 1153675 := bstep (se 1 (by rfl) ⟨865256, by rfl⟩ : syracuseStep 1153675 = 1730513) B1730513
theorem B1153687 : Blo 1152637 1153687 := bstep (se 1 (by rfl) ⟨865265, by rfl⟩ : syracuseStep 1153687 = 1730531) B1730531
theorem B1153707 : Blo 1152637 1153707 := bstep (se 1 (by rfl) ⟨865280, by rfl⟩ : syracuseStep 1153707 = 1730561) B1730561
theorem B1153719 : Blo 1152637 1153719 := bstep (se 1 (by rfl) ⟨865289, by rfl⟩ : syracuseStep 1153719 = 1730579) B1730579
theorem B1153739 : Blo 1152637 1153739 := bstep (se 1 (by rfl) ⟨865304, by rfl⟩ : syracuseStep 1153739 = 1730609) B1730609
theorem B1153751 : Blo 1152637 1153751 := bstep (se 1 (by rfl) ⟨865313, by rfl⟩ : syracuseStep 1153751 = 1730627) B1730627
theorem B2595545 : Blo 1152637 2595545 := bstep (se 2 (by rfl) ⟨973329, by rfl⟩ : syracuseStep 2595545 = 1946659) B1946659
theorem B1153771 : Blo 1152637 1153771 := bstep (se 1 (by rfl) ⟨865328, by rfl⟩ : syracuseStep 1153771 = 1730657) B1730657
theorem B1153783 : Blo 1152637 1153783 := bstep (se 1 (by rfl) ⟨865337, by rfl⟩ : syracuseStep 1153783 = 1730675) B1730675
theorem B19962629 : Blo 1152637 19962629 := bstep (se 4 (by rfl) ⟨1871496, by rfl⟩ : syracuseStep 19962629 = 3742993) B3742993
theorem B1153803 : Blo 1152637 1153803 := bstep (se 1 (by rfl) ⟨865352, by rfl⟩ : syracuseStep 1153803 = 1730705) B1730705
theorem B3283735 : Blo 1152637 3283735 := bstep (se 1 (by rfl) ⟨2462801, by rfl⟩ : syracuseStep 3283735 = 4925603) B4925603
theorem B1153815 : Blo 1152637 1153815 := bstep (se 1 (by rfl) ⟨865361, by rfl⟩ : syracuseStep 1153815 = 1730723) B1730723
theorem B1153835 : Blo 1152637 1153835 := bstep (se 1 (by rfl) ⟨865376, by rfl⟩ : syracuseStep 1153835 = 1730753) B1730753
theorem B2595635 : Blo 1152637 2595635 := bstep (se 1 (by rfl) ⟨1946726, by rfl⟩ : syracuseStep 2595635 = 3893453) B3893453
theorem B1153847 : Blo 1152637 1153847 := bstep (se 1 (by rfl) ⟨865385, by rfl⟩ : syracuseStep 1153847 = 1730771) B1730771
theorem B1153867 : Blo 1152637 1153867 := bstep (se 1 (by rfl) ⟨865400, by rfl⟩ : syracuseStep 1153867 = 1730801) B1730801
theorem B2595671 : Blo 1152637 2595671 := bstep (se 1 (by rfl) ⟨1946753, by rfl⟩ : syracuseStep 2595671 = 3893507) B3893507
theorem B1153879 : Blo 1152637 1153879 := bstep (se 1 (by rfl) ⟨865409, by rfl⟩ : syracuseStep 1153879 = 1730819) B1730819
theorem B9870173 : Blo 1152637 9870173 := bstep (se 3 (by rfl) ⟨1850657, by rfl⟩ : syracuseStep 9870173 = 3701315) B3701315
theorem B1153899 : Blo 1152637 1153899 := bstep (se 1 (by rfl) ⟨865424, by rfl⟩ : syracuseStep 1153899 = 1730849) B1730849
theorem B1153911 : Blo 1152637 1153911 := bstep (se 1 (by rfl) ⟨865433, by rfl⟩ : syracuseStep 1153911 = 1730867) B1730867
theorem B1317751 : Blo 1152637 1317751 := bstep (se 1 (by rfl) ⟨988313, by rfl⟩ : syracuseStep 1317751 = 1976627) B1976627
theorem B1153931 : Blo 1152637 1153931 := bstep (se 1 (by rfl) ⟨865448, by rfl⟩ : syracuseStep 1153931 = 1730897) B1730897
theorem B1153943 : Blo 1152637 1153943 := bstep (se 1 (by rfl) ⟨865457, by rfl⟩ : syracuseStep 1153943 = 1730915) B1730915
theorem B1153963 : Blo 1152637 1153963 := bstep (se 1 (by rfl) ⟨865472, by rfl⟩ : syracuseStep 1153963 = 1730945) B1730945
theorem B1153975 : Blo 1152637 1153975 := bstep (se 1 (by rfl) ⟨865481, by rfl⟩ : syracuseStep 1153975 = 1730963) B1730963
theorem B1153995 : Blo 1152637 1153995 := bstep (se 1 (by rfl) ⟨865496, by rfl⟩ : syracuseStep 1153995 = 1730993) B1730993
theorem B2464715 : Blo 1152637 2464715 := bstep (se 1 (by rfl) ⟨1848536, by rfl⟩ : syracuseStep 2464715 = 3697073) B3697073
theorem B1154007 : Blo 1152637 1154007 := bstep (se 1 (by rfl) ⟨865505, by rfl⟩ : syracuseStep 1154007 = 1731011) B1731011
theorem B29563865 : Blo 1152637 29563865 := bstep (se 2 (by rfl) ⟨11086449, by rfl⟩ : syracuseStep 29563865 = 22172899) B22172899
theorem B1154027 : Blo 1152637 1154027 := bstep (se 1 (by rfl) ⟨865520, by rfl⟩ : syracuseStep 1154027 = 1731041) B1731041
theorem B1154039 : Blo 1152637 1154039 := bstep (se 1 (by rfl) ⟨865529, by rfl⟩ : syracuseStep 1154039 = 1731059) B1731059
theorem B2595851 : Blo 1152637 2595851 := bstep (se 1 (by rfl) ⟨1946888, by rfl⟩ : syracuseStep 2595851 = 3893777) B3893777
theorem B1154059 : Blo 1152637 1154059 := bstep (se 1 (by rfl) ⟨865544, by rfl⟩ : syracuseStep 1154059 = 1731089) B1731089
theorem B21077009 : Blo 1152637 21077009 := bstep (se 2 (by rfl) ⟨7903878, by rfl⟩ : syracuseStep 21077009 = 15807757) B15807757
theorem B1154071 : Blo 1152637 1154071 := bstep (se 1 (by rfl) ⟨865553, by rfl⟩ : syracuseStep 1154071 = 1731107) B1731107
theorem B29629475 : Blo 1152637 29629475 := bstep (se 1 (by rfl) ⟨22222106, by rfl⟩ : syracuseStep 29629475 = 44444213) B44444213
theorem B1154091 : Blo 1152637 1154091 := bstep (se 1 (by rfl) ⟨865568, by rfl⟩ : syracuseStep 1154091 = 1731137) B1731137
theorem B1154103 : Blo 1152637 1154103 := bstep (se 1 (by rfl) ⟨865577, by rfl⟩ : syracuseStep 1154103 = 1731155) B1731155
theorem B5839937 : Blo 1152637 5839937 := bstep (se 2 (by rfl) ⟨2189976, by rfl⟩ : syracuseStep 5839937 = 4379953) B4379953
theorem B2595905 : Blo 1152637 2595905 := bstep (se 2 (by rfl) ⟨973464, by rfl⟩ : syracuseStep 2595905 = 1946929) B1946929
theorem B1154123 : Blo 1152637 1154123 := bstep (se 1 (by rfl) ⟨865592, by rfl⟩ : syracuseStep 1154123 = 1731185) B1731185
theorem B1154135 : Blo 1152637 1154135 := bstep (se 1 (by rfl) ⟨865601, by rfl⟩ : syracuseStep 1154135 = 1731203) B1731203
theorem B1154155 : Blo 1152637 1154155 := bstep (se 1 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 1154155 = 1731233) B1731233
theorem B1154167 : Blo 1152637 1154167 := bstep (se 1 (by rfl) ⟨865625, by rfl⟩ : syracuseStep 1154167 = 1731251) B1731251
theorem B1154187 : Blo 1152637 1154187 := bstep (se 1 (by rfl) ⟨865640, by rfl⟩ : syracuseStep 1154187 = 1731281) B1731281
theorem B1154199 : Blo 1152637 1154199 := bstep (se 1 (by rfl) ⟨865649, by rfl⟩ : syracuseStep 1154199 = 1731299) B1731299
theorem B1154219 : Blo 1152637 1154219 := bstep (se 1 (by rfl) ⟨865664, by rfl⟩ : syracuseStep 1154219 = 1731329) B1731329
theorem B1154231 : Blo 1152637 1154231 := bstep (se 1 (by rfl) ⟨865673, by rfl⟩ : syracuseStep 1154231 = 1731347) B1731347
theorem B1154251 : Blo 1152637 1154251 := bstep (se 1 (by rfl) ⟨865688, by rfl⟩ : syracuseStep 1154251 = 1731377) B1731377
theorem B1154263 : Blo 1152637 1154263 := bstep (se 1 (by rfl) ⟨865697, by rfl⟩ : syracuseStep 1154263 = 1731395) B1731395
theorem B1154283 : Blo 1152637 1154283 := bstep (se 1 (by rfl) ⟨865712, by rfl⟩ : syracuseStep 1154283 = 1731425) B1731425
theorem B1154295 : Blo 1152637 1154295 := bstep (se 1 (by rfl) ⟨865721, by rfl⟩ : syracuseStep 1154295 = 1731443) B1731443
theorem B1318135 : Blo 1152637 1318135 := bstep (se 1 (by rfl) ⟨988601, by rfl⟩ : syracuseStep 1318135 = 1977203) B1977203
theorem B1154315 : Blo 1152637 1154315 := bstep (se 1 (by rfl) ⟨865736, by rfl⟩ : syracuseStep 1154315 = 1731473) B1731473
theorem B1154327 : Blo 1152637 1154327 := bstep (se 1 (by rfl) ⟨865745, by rfl⟩ : syracuseStep 1154327 = 1731491) B1731491
theorem B2596121 : Blo 1152637 2596121 := bstep (se 2 (by rfl) ⟨973545, by rfl⟩ : syracuseStep 2596121 = 1947091) B1947091
theorem B1645849 : Blo 1152637 1645849 := bstep (se 2 (by rfl) ⟨617193, by rfl⟩ : syracuseStep 1645849 = 1234387) B1234387
theorem B1154347 : Blo 1152637 1154347 := bstep (se 1 (by rfl) ⟨865760, by rfl⟩ : syracuseStep 1154347 = 1731521) B1731521
theorem B1154359 : Blo 1152637 1154359 := bstep (se 1 (by rfl) ⟨865769, by rfl⟩ : syracuseStep 1154359 = 1731539) B1731539
theorem B1154379 : Blo 1152637 1154379 := bstep (se 1 (by rfl) ⟨865784, by rfl⟩ : syracuseStep 1154379 = 1731569) B1731569
theorem B1154391 : Blo 1152637 1154391 := bstep (se 1 (by rfl) ⟨865793, by rfl⟩ : syracuseStep 1154391 = 1731587) B1731587
theorem B1154411 : Blo 1152637 1154411 := bstep (se 1 (by rfl) ⟨865808, by rfl⟩ : syracuseStep 1154411 = 1731617) B1731617
theorem B2596211 : Blo 1152637 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B1154423 : Blo 1152637 1154423 := bstep (se 1 (by rfl) ⟨865817, by rfl⟩ : syracuseStep 1154423 = 1731635) B1731635
theorem B1154443 : Blo 1152637 1154443 := bstep (se 1 (by rfl) ⟨865832, by rfl⟩ : syracuseStep 1154443 = 1731665) B1731665
theorem B2596247 : Blo 1152637 2596247 := bstep (se 1 (by rfl) ⟨1947185, by rfl⟩ : syracuseStep 2596247 = 3894371) B3894371
theorem B1154455 : Blo 1152637 1154455 := bstep (se 1 (by rfl) ⟨865841, by rfl⟩ : syracuseStep 1154455 = 1731683) B1731683
theorem B1154475 : Blo 1152637 1154475 := bstep (se 1 (by rfl) ⟨865856, by rfl⟩ : syracuseStep 1154475 = 1731713) B1731713
theorem B1154487 : Blo 1152637 1154487 := bstep (se 1 (by rfl) ⟨865865, by rfl⟩ : syracuseStep 1154487 = 1731731) B1731731
theorem B1154507 : Blo 1152637 1154507 := bstep (se 1 (by rfl) ⟨865880, by rfl⟩ : syracuseStep 1154507 = 1731761) B1731761
theorem B1154519 : Blo 1152637 1154519 := bstep (se 1 (by rfl) ⟨865889, by rfl⟩ : syracuseStep 1154519 = 1731779) B1731779
theorem B1154539 : Blo 1152637 1154539 := bstep (se 1 (by rfl) ⟨865904, by rfl⟩ : syracuseStep 1154539 = 1731809) B1731809
theorem B1154551 : Blo 1152637 1154551 := bstep (se 1 (by rfl) ⟨865913, by rfl⟩ : syracuseStep 1154551 = 1731827) B1731827
theorem B1154571 : Blo 1152637 1154571 := bstep (se 1 (by rfl) ⟨865928, by rfl⟩ : syracuseStep 1154571 = 1731857) B1731857
theorem B1154583 : Blo 1152637 1154583 := bstep (se 1 (by rfl) ⟨865937, by rfl⟩ : syracuseStep 1154583 = 1731875) B1731875
theorem B1154603 : Blo 1152637 1154603 := bstep (se 1 (by rfl) ⟨865952, by rfl⟩ : syracuseStep 1154603 = 1731905) B1731905
theorem B1154615 : Blo 1152637 1154615 := bstep (se 1 (by rfl) ⟨865961, by rfl⟩ : syracuseStep 1154615 = 1731923) B1731923
theorem B2596427 : Blo 1152637 2596427 := bstep (se 1 (by rfl) ⟨1947320, by rfl⟩ : syracuseStep 2596427 = 3894641) B3894641
theorem B1154635 : Blo 1152637 1154635 := bstep (se 1 (by rfl) ⟨865976, by rfl⟩ : syracuseStep 1154635 = 1731953) B1731953
theorem B1154647 : Blo 1152637 1154647 := bstep (se 1 (by rfl) ⟨865985, by rfl⟩ : syracuseStep 1154647 = 1731971) B1731971
theorem B1154667 : Blo 1152637 1154667 := bstep (se 1 (by rfl) ⟨866000, by rfl⟩ : syracuseStep 1154667 = 1732001) B1732001
theorem B1154679 : Blo 1152637 1154679 := bstep (se 1 (by rfl) ⟨866009, by rfl⟩ : syracuseStep 1154679 = 1732019) B1732019
theorem B2596481 : Blo 1152637 2596481 := bstep (se 2 (by rfl) ⟨973680, by rfl⟩ : syracuseStep 2596481 = 1947361) B1947361
theorem B1154699 : Blo 1152637 1154699 := bstep (se 1 (by rfl) ⟨866024, by rfl⟩ : syracuseStep 1154699 = 1732049) B1732049
theorem B1154711 : Blo 1152637 1154711 := bstep (se 1 (by rfl) ⟨866033, by rfl⟩ : syracuseStep 1154711 = 1732067) B1732067
theorem B1154731 : Blo 1152637 1154731 := bstep (se 1 (by rfl) ⟨866048, by rfl⟩ : syracuseStep 1154731 = 1732097) B1732097
theorem B1154743 : Blo 1152637 1154743 := bstep (se 1 (by rfl) ⟨866057, by rfl⟩ : syracuseStep 1154743 = 1732115) B1732115
theorem B1154763 : Blo 1152637 1154763 := bstep (se 1 (by rfl) ⟨866072, by rfl⟩ : syracuseStep 1154763 = 1732145) B1732145
theorem B1154775 : Blo 1152637 1154775 := bstep (se 1 (by rfl) ⟨866081, by rfl⟩ : syracuseStep 1154775 = 1732163) B1732163
theorem B1154795 : Blo 1152637 1154795 := bstep (se 1 (by rfl) ⟨866096, by rfl⟩ : syracuseStep 1154795 = 1732193) B1732193
theorem B1154807 : Blo 1152637 1154807 := bstep (se 1 (by rfl) ⟨866105, by rfl⟩ : syracuseStep 1154807 = 1732211) B1732211
theorem B1154827 : Blo 1152637 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B1154839 : Blo 1152637 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B1154859 : Blo 1152637 1154859 := bstep (se 1 (by rfl) ⟨866144, by rfl⟩ : syracuseStep 1154859 = 1732289) B1732289
theorem B1154871 : Blo 1152637 1154871 := bstep (se 1 (by rfl) ⟨866153, by rfl⟩ : syracuseStep 1154871 = 1732307) B1732307
theorem B1154891 : Blo 1152637 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B2924363 : Blo 1152637 2924363 := bstep (se 1 (by rfl) ⟨2193272, by rfl⟩ : syracuseStep 2924363 = 4386545) B4386545
theorem B1154903 : Blo 1152637 1154903 := bstep (se 1 (by rfl) ⟨866177, by rfl⟩ : syracuseStep 1154903 = 1732355) B1732355
theorem B2596697 : Blo 1152637 2596697 := bstep (se 2 (by rfl) ⟨973761, by rfl⟩ : syracuseStep 2596697 = 1947523) B1947523
theorem B1154923 : Blo 1152637 1154923 := bstep (se 1 (by rfl) ⟨866192, by rfl⟩ : syracuseStep 1154923 = 1732385) B1732385
theorem B1154935 : Blo 1152637 1154935 := bstep (se 1 (by rfl) ⟨866201, by rfl⟩ : syracuseStep 1154935 = 1732403) B1732403
theorem B1154955 : Blo 1152637 1154955 := bstep (se 1 (by rfl) ⟨866216, by rfl⟩ : syracuseStep 1154955 = 1732433) B1732433
theorem B1154967 : Blo 1152637 1154967 := bstep (se 1 (by rfl) ⟨866225, by rfl⟩ : syracuseStep 1154967 = 1732451) B1732451
theorem B1154987 : Blo 1152637 1154987 := bstep (se 1 (by rfl) ⟨866240, by rfl⟩ : syracuseStep 1154987 = 1732481) B1732481
theorem B2596787 : Blo 1152637 2596787 := bstep (se 1 (by rfl) ⟨1947590, by rfl⟩ : syracuseStep 2596787 = 3895181) B3895181
theorem B1154999 : Blo 1152637 1154999 := bstep (se 1 (by rfl) ⟨866249, by rfl⟩ : syracuseStep 1154999 = 1732499) B1732499
theorem B1155019 : Blo 1152637 1155019 := bstep (se 1 (by rfl) ⟨866264, by rfl⟩ : syracuseStep 1155019 = 1732529) B1732529
theorem B2596823 : Blo 1152637 2596823 := bstep (se 1 (by rfl) ⟨1947617, by rfl⟩ : syracuseStep 2596823 = 3895235) B3895235
theorem B1155031 : Blo 1152637 1155031 := bstep (se 1 (by rfl) ⟨866273, by rfl⟩ : syracuseStep 1155031 = 1732547) B1732547
theorem B1155051 : Blo 1152637 1155051 := bstep (se 1 (by rfl) ⟨866288, by rfl⟩ : syracuseStep 1155051 = 1732577) B1732577
theorem B1155063 : Blo 1152637 1155063 := bstep (se 1 (by rfl) ⟨866297, by rfl⟩ : syracuseStep 1155063 = 1732595) B1732595
theorem B1155083 : Blo 1152637 1155083 := bstep (se 1 (by rfl) ⟨866312, by rfl⟩ : syracuseStep 1155083 = 1732625) B1732625
theorem B1155095 : Blo 1152637 1155095 := bstep (se 1 (by rfl) ⟨866321, by rfl⟩ : syracuseStep 1155095 = 1732643) B1732643
theorem B1155115 : Blo 1152637 1155115 := bstep (se 1 (by rfl) ⟨866336, by rfl⟩ : syracuseStep 1155115 = 1732673) B1732673
theorem B1155127 : Blo 1152637 1155127 := bstep (se 1 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 1155127 = 1732691) B1732691
theorem B18980939 : Blo 1152637 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B1155147 : Blo 1152637 1155147 := bstep (se 1 (by rfl) ⟨866360, by rfl⟩ : syracuseStep 1155147 = 1732721) B1732721
theorem B1155159 : Blo 1152637 1155159 := bstep (se 1 (by rfl) ⟨866369, by rfl⟩ : syracuseStep 1155159 = 1732739) B1732739
theorem B1155179 : Blo 1152637 1155179 := bstep (se 1 (by rfl) ⟨866384, by rfl⟩ : syracuseStep 1155179 = 1732769) B1732769
theorem B1155191 : Blo 1152637 1155191 := bstep (se 1 (by rfl) ⟨866393, by rfl⟩ : syracuseStep 1155191 = 1732787) B1732787
theorem B2597003 : Blo 1152637 2597003 := bstep (se 1 (by rfl) ⟨1947752, by rfl⟩ : syracuseStep 2597003 = 3895505) B3895505
theorem B1155211 : Blo 1152637 1155211 := bstep (se 1 (by rfl) ⟨866408, by rfl⟩ : syracuseStep 1155211 = 1732817) B1732817
theorem B1155223 : Blo 1152637 1155223 := bstep (se 1 (by rfl) ⟨866417, by rfl⟩ : syracuseStep 1155223 = 1732835) B1732835
theorem B1646743 : Blo 1152637 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B1155243 : Blo 1152637 1155243 := bstep (se 1 (by rfl) ⟨866432, by rfl⟩ : syracuseStep 1155243 = 1732865) B1732865
theorem B1155255 : Blo 1152637 1155255 := bstep (se 1 (by rfl) ⟨866441, by rfl⟩ : syracuseStep 1155255 = 1732883) B1732883
theorem B2597057 : Blo 1152637 2597057 := bstep (se 2 (by rfl) ⟨973896, by rfl⟩ : syracuseStep 2597057 = 1947793) B1947793
theorem B1155275 : Blo 1152637 1155275 := bstep (se 1 (by rfl) ⟨866456, by rfl⟩ : syracuseStep 1155275 = 1732913) B1732913
theorem B2629847 : Blo 1152637 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B1155287 : Blo 1152637 1155287 := bstep (se 1 (by rfl) ⟨866465, by rfl⟩ : syracuseStep 1155287 = 1732931) B1732931
theorem B1155307 : Blo 1152637 1155307 := bstep (se 1 (by rfl) ⟨866480, by rfl⟩ : syracuseStep 1155307 = 1732961) B1732961
theorem B1155319 : Blo 1152637 1155319 := bstep (se 1 (by rfl) ⟨866489, by rfl⟩ : syracuseStep 1155319 = 1732979) B1732979
theorem B1155339 : Blo 1152637 1155339 := bstep (se 1 (by rfl) ⟨866504, by rfl⟩ : syracuseStep 1155339 = 1733009) B1733009
theorem B1155351 : Blo 1152637 1155351 := bstep (se 1 (by rfl) ⟨866513, by rfl⟩ : syracuseStep 1155351 = 1733027) B1733027
theorem B1155371 : Blo 1152637 1155371 := bstep (se 1 (by rfl) ⟨866528, by rfl⟩ : syracuseStep 1155371 = 1733057) B1733057
theorem B1155383 : Blo 1152637 1155383 := bstep (se 1 (by rfl) ⟨866537, by rfl⟩ : syracuseStep 1155383 = 1733075) B1733075
theorem B1155403 : Blo 1152637 1155403 := bstep (se 1 (by rfl) ⟨866552, by rfl⟩ : syracuseStep 1155403 = 1733105) B1733105
theorem B1155415 : Blo 1152637 1155415 := bstep (se 1 (by rfl) ⟨866561, by rfl⟩ : syracuseStep 1155415 = 1733123) B1733123
theorem B1155435 : Blo 1152637 1155435 := bstep (se 1 (by rfl) ⟨866576, by rfl⟩ : syracuseStep 1155435 = 1733153) B1733153
theorem B1155447 : Blo 1152637 1155447 := bstep (se 1 (by rfl) ⟨866585, by rfl⟩ : syracuseStep 1155447 = 1733171) B1733171
theorem B1155467 : Blo 1152637 1155467 := bstep (se 1 (by rfl) ⟨866600, by rfl⟩ : syracuseStep 1155467 = 1733201) B1733201
theorem B1155479 : Blo 1152637 1155479 := bstep (se 1 (by rfl) ⟨866609, by rfl⟩ : syracuseStep 1155479 = 1733219) B1733219
theorem B2597273 : Blo 1152637 2597273 := bstep (se 2 (by rfl) ⟨973977, by rfl⟩ : syracuseStep 2597273 = 1947955) B1947955
theorem B1155499 : Blo 1152637 1155499 := bstep (se 1 (by rfl) ⟨866624, by rfl⟩ : syracuseStep 1155499 = 1733249) B1733249
theorem B4923827 : Blo 1152637 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B1155511 : Blo 1152637 1155511 := bstep (se 1 (by rfl) ⟨866633, by rfl⟩ : syracuseStep 1155511 = 1733267) B1733267
theorem B1155531 : Blo 1152637 1155531 := bstep (se 1 (by rfl) ⟨866648, by rfl⟩ : syracuseStep 1155531 = 1733297) B1733297
theorem B1155543 : Blo 1152637 1155543 := bstep (se 1 (by rfl) ⟨866657, by rfl⟩ : syracuseStep 1155543 = 1733315) B1733315
theorem B1155563 : Blo 1152637 1155563 := bstep (se 1 (by rfl) ⟨866672, by rfl⟩ : syracuseStep 1155563 = 1733345) B1733345
theorem B2597363 : Blo 1152637 2597363 := bstep (se 1 (by rfl) ⟨1948022, by rfl⟩ : syracuseStep 2597363 = 3896045) B3896045
theorem B1155575 : Blo 1152637 1155575 := bstep (se 1 (by rfl) ⟨866681, by rfl⟩ : syracuseStep 1155575 = 1733363) B1733363
theorem B1155595 : Blo 1152637 1155595 := bstep (se 1 (by rfl) ⟨866696, by rfl⟩ : syracuseStep 1155595 = 1733393) B1733393
theorem B2597399 : Blo 1152637 2597399 := bstep (se 1 (by rfl) ⟨1948049, by rfl⟩ : syracuseStep 2597399 = 3896099) B3896099
theorem B1155607 : Blo 1152637 1155607 := bstep (se 1 (by rfl) ⟨866705, by rfl⟩ : syracuseStep 1155607 = 1733411) B1733411
theorem B1155627 : Blo 1152637 1155627 := bstep (se 1 (by rfl) ⟨866720, by rfl⟩ : syracuseStep 1155627 = 1733441) B1733441
theorem B1155639 : Blo 1152637 1155639 := bstep (se 1 (by rfl) ⟨866729, by rfl⟩ : syracuseStep 1155639 = 1733459) B1733459
theorem B1155659 : Blo 1152637 1155659 := bstep (se 1 (by rfl) ⟨866744, by rfl⟩ : syracuseStep 1155659 = 1733489) B1733489
theorem B1155671 : Blo 1152637 1155671 := bstep (se 1 (by rfl) ⟨866753, by rfl⟩ : syracuseStep 1155671 = 1733507) B1733507
theorem B3285593 : Blo 1152637 3285593 := bstep (se 2 (by rfl) ⟨1232097, by rfl⟩ : syracuseStep 3285593 = 2464195) B2464195
theorem B1155691 : Blo 1152637 1155691 := bstep (se 1 (by rfl) ⟨866768, by rfl⟩ : syracuseStep 1155691 = 1733537) B1733537
theorem B1155703 : Blo 1152637 1155703 := bstep (se 1 (by rfl) ⟨866777, by rfl⟩ : syracuseStep 1155703 = 1733555) B1733555
theorem B1155723 : Blo 1152637 1155723 := bstep (se 1 (by rfl) ⟨866792, by rfl⟩ : syracuseStep 1155723 = 1733585) B1733585
theorem B1155735 : Blo 1152637 1155735 := bstep (se 1 (by rfl) ⟨866801, by rfl⟩ : syracuseStep 1155735 = 1733603) B1733603
theorem B1155755 : Blo 1152637 1155755 := bstep (se 1 (by rfl) ⟨866816, by rfl⟩ : syracuseStep 1155755 = 1733633) B1733633
theorem B1155767 : Blo 1152637 1155767 := bstep (se 1 (by rfl) ⟨866825, by rfl⟩ : syracuseStep 1155767 = 1733651) B1733651
theorem B2597579 : Blo 1152637 2597579 := bstep (se 1 (by rfl) ⟨1948184, by rfl⟩ : syracuseStep 2597579 = 3896369) B3896369
theorem B1155787 : Blo 1152637 1155787 := bstep (se 1 (by rfl) ⟨866840, by rfl⟩ : syracuseStep 1155787 = 1733681) B1733681
theorem B1155799 : Blo 1152637 1155799 := bstep (se 1 (by rfl) ⟨866849, by rfl⟩ : syracuseStep 1155799 = 1733699) B1733699
theorem B1155819 : Blo 1152637 1155819 := bstep (se 1 (by rfl) ⟨866864, by rfl⟩ : syracuseStep 1155819 = 1733729) B1733729
theorem B1155831 : Blo 1152637 1155831 := bstep (se 1 (by rfl) ⟨866873, by rfl⟩ : syracuseStep 1155831 = 1733747) B1733747
theorem B2597633 : Blo 1152637 2597633 := bstep (se 2 (by rfl) ⟨974112, by rfl⟩ : syracuseStep 2597633 = 1948225) B1948225
theorem B1155851 : Blo 1152637 1155851 := bstep (se 1 (by rfl) ⟨866888, by rfl⟩ : syracuseStep 1155851 = 1733777) B1733777
theorem B2925335 : Blo 1152637 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B1155863 : Blo 1152637 1155863 := bstep (se 1 (by rfl) ⟨866897, by rfl⟩ : syracuseStep 1155863 = 1733795) B1733795
theorem B1155883 : Blo 1152637 1155883 := bstep (se 1 (by rfl) ⟨866912, by rfl⟩ : syracuseStep 1155883 = 1733825) B1733825
theorem B1155895 : Blo 1152637 1155895 := bstep (se 1 (by rfl) ⟨866921, by rfl⟩ : syracuseStep 1155895 = 1733843) B1733843
theorem B1155915 : Blo 1152637 1155915 := bstep (se 1 (by rfl) ⟨866936, by rfl⟩ : syracuseStep 1155915 = 1733873) B1733873
theorem B1155927 : Blo 1152637 1155927 := bstep (se 1 (by rfl) ⟨866945, by rfl⟩ : syracuseStep 1155927 = 1733891) B1733891
theorem B1155947 : Blo 1152637 1155947 := bstep (se 1 (by rfl) ⟨866960, by rfl⟩ : syracuseStep 1155947 = 1733921) B1733921
theorem B1155959 : Blo 1152637 1155959 := bstep (se 1 (by rfl) ⟨866969, by rfl⟩ : syracuseStep 1155959 = 1733939) B1733939
theorem B1155979 : Blo 1152637 1155979 := bstep (se 1 (by rfl) ⟨866984, by rfl⟩ : syracuseStep 1155979 = 1733969) B1733969
theorem B1155991 : Blo 1152637 1155991 := bstep (se 1 (by rfl) ⟨866993, by rfl⟩ : syracuseStep 1155991 = 1733987) B1733987
theorem B1156011 : Blo 1152637 1156011 := bstep (se 1 (by rfl) ⟨867008, by rfl⟩ : syracuseStep 1156011 = 1734017) B1734017
theorem B1156023 : Blo 1152637 1156023 := bstep (se 1 (by rfl) ⟨867017, by rfl⟩ : syracuseStep 1156023 = 1734035) B1734035
theorem B1156043 : Blo 1152637 1156043 := bstep (se 1 (by rfl) ⟨867032, by rfl⟩ : syracuseStep 1156043 = 1734065) B1734065
theorem B1156055 : Blo 1152637 1156055 := bstep (se 1 (by rfl) ⟨867041, by rfl⟩ : syracuseStep 1156055 = 1734083) B1734083
theorem B5841881 : Blo 1152637 5841881 := bstep (se 2 (by rfl) ⟨2190705, by rfl⟩ : syracuseStep 5841881 = 4381411) B4381411
theorem B2597849 : Blo 1152637 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B1156075 : Blo 1152637 1156075 := bstep (se 1 (by rfl) ⟨867056, by rfl⟩ : syracuseStep 1156075 = 1734113) B1734113
theorem B1156087 : Blo 1152637 1156087 := bstep (se 1 (by rfl) ⟨867065, by rfl⟩ : syracuseStep 1156087 = 1734131) B1734131
theorem B1156107 : Blo 1152637 1156107 := bstep (se 1 (by rfl) ⟨867080, by rfl⟩ : syracuseStep 1156107 = 1734161) B1734161
theorem B7218193 : Blo 1152637 7218193 := bstep (se 2 (by rfl) ⟨2706822, by rfl⟩ : syracuseStep 7218193 = 5413645) B5413645
theorem B1156119 : Blo 1152637 1156119 := bstep (se 1 (by rfl) ⟨867089, by rfl⟩ : syracuseStep 1156119 = 1734179) B1734179
theorem B1156139 : Blo 1152637 1156139 := bstep (se 1 (by rfl) ⟨867104, by rfl⟩ : syracuseStep 1156139 = 1734209) B1734209
theorem B2597939 : Blo 1152637 2597939 := bstep (se 1 (by rfl) ⟨1948454, by rfl⟩ : syracuseStep 2597939 = 3896909) B3896909
theorem B1156151 : Blo 1152637 1156151 := bstep (se 1 (by rfl) ⟨867113, by rfl⟩ : syracuseStep 1156151 = 1734227) B1734227
theorem B1156171 : Blo 1152637 1156171 := bstep (se 1 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 1156171 = 1734257) B1734257
theorem B2597975 : Blo 1152637 2597975 := bstep (se 1 (by rfl) ⟨1948481, by rfl⟩ : syracuseStep 2597975 = 3896963) B3896963
theorem B1156183 : Blo 1152637 1156183 := bstep (se 1 (by rfl) ⟨867137, by rfl⟩ : syracuseStep 1156183 = 1734275) B1734275
theorem B1156203 : Blo 1152637 1156203 := bstep (se 1 (by rfl) ⟨867152, by rfl⟩ : syracuseStep 1156203 = 1734305) B1734305
theorem B1156215 : Blo 1152637 1156215 := bstep (se 1 (by rfl) ⟨867161, by rfl⟩ : syracuseStep 1156215 = 1734323) B1734323
theorem B1156235 : Blo 1152637 1156235 := bstep (se 1 (by rfl) ⟨867176, by rfl⟩ : syracuseStep 1156235 = 1734353) B1734353
theorem B1156247 : Blo 1152637 1156247 := bstep (se 1 (by rfl) ⟨867185, by rfl⟩ : syracuseStep 1156247 = 1734371) B1734371
theorem B1156267 : Blo 1152637 1156267 := bstep (se 1 (by rfl) ⟨867200, by rfl⟩ : syracuseStep 1156267 = 1734401) B1734401
theorem B1156279 : Blo 1152637 1156279 := bstep (se 1 (by rfl) ⟨867209, by rfl⟩ : syracuseStep 1156279 = 1734419) B1734419
theorem B1156299 : Blo 1152637 1156299 := bstep (se 1 (by rfl) ⟨867224, by rfl⟩ : syracuseStep 1156299 = 1734449) B1734449
theorem B1385687 : Blo 1152637 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B1156311 : Blo 1152637 1156311 := bstep (se 1 (by rfl) ⟨867233, by rfl⟩ : syracuseStep 1156311 = 1734467) B1734467
theorem B1156331 : Blo 1152637 1156331 := bstep (se 1 (by rfl) ⟨867248, by rfl⟩ : syracuseStep 1156331 = 1734497) B1734497
theorem B1156343 : Blo 1152637 1156343 := bstep (se 1 (by rfl) ⟨867257, by rfl⟩ : syracuseStep 1156343 = 1734515) B1734515
theorem B2467073 : Blo 1152637 2467073 := bstep (se 2 (by rfl) ⟨925152, by rfl⟩ : syracuseStep 2467073 = 1850305) B1850305
theorem B2598155 : Blo 1152637 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B1156363 : Blo 1152637 1156363 := bstep (se 1 (by rfl) ⟨867272, by rfl⟩ : syracuseStep 1156363 = 1734545) B1734545
theorem B1156375 : Blo 1152637 1156375 := bstep (se 1 (by rfl) ⟨867281, by rfl⟩ : syracuseStep 1156375 = 1734563) B1734563
theorem B1156395 : Blo 1152637 1156395 := bstep (se 1 (by rfl) ⟨867296, by rfl⟩ : syracuseStep 1156395 = 1734593) B1734593
theorem B1156407 : Blo 1152637 1156407 := bstep (se 1 (by rfl) ⟨867305, by rfl⟩ : syracuseStep 1156407 = 1734611) B1734611
theorem B2598209 : Blo 1152637 2598209 := bstep (se 2 (by rfl) ⟨974328, by rfl⟩ : syracuseStep 2598209 = 1948657) B1948657
theorem B1156427 : Blo 1152637 1156427 := bstep (se 1 (by rfl) ⟨867320, by rfl⟩ : syracuseStep 1156427 = 1734641) B1734641
theorem B1156439 : Blo 1152637 1156439 := bstep (se 1 (by rfl) ⟨867329, by rfl⟩ : syracuseStep 1156439 = 1734659) B1734659
theorem B16885093 : Blo 1152637 16885093 := bstep (se 4 (by rfl) ⟨1582977, by rfl⟩ : syracuseStep 16885093 = 3165955) B3165955
theorem B1156459 : Blo 1152637 1156459 := bstep (se 1 (by rfl) ⟨867344, by rfl⟩ : syracuseStep 1156459 = 1734689) B1734689
theorem B1156471 : Blo 1152637 1156471 := bstep (se 1 (by rfl) ⟨867353, by rfl⟩ : syracuseStep 1156471 = 1734707) B1734707
theorem B1156491 : Blo 1152637 1156491 := bstep (se 1 (by rfl) ⟨867368, by rfl⟩ : syracuseStep 1156491 = 1734737) B1734737
theorem B3286423 : Blo 1152637 3286423 := bstep (se 1 (by rfl) ⟨2464817, by rfl⟩ : syracuseStep 3286423 = 4929635) B4929635
theorem B1156503 : Blo 1152637 1156503 := bstep (se 1 (by rfl) ⟨867377, by rfl⟩ : syracuseStep 1156503 = 1734755) B1734755
theorem B1156523 : Blo 1152637 1156523 := bstep (se 1 (by rfl) ⟨867392, by rfl⟩ : syracuseStep 1156523 = 1734785) B1734785
theorem B2926003 : Blo 1152637 2926003 := bstep (se 1 (by rfl) ⟨2194502, by rfl⟩ : syracuseStep 2926003 = 4389005) B4389005
theorem B1156535 : Blo 1152637 1156535 := bstep (se 1 (by rfl) ⟨867401, by rfl⟩ : syracuseStep 1156535 = 1734803) B1734803
theorem B1156555 : Blo 1152637 1156555 := bstep (se 1 (by rfl) ⟨867416, by rfl⟩ : syracuseStep 1156555 = 1734833) B1734833
theorem B1156567 : Blo 1152637 1156567 := bstep (se 1 (by rfl) ⟨867425, by rfl⟩ : syracuseStep 1156567 = 1734851) B1734851
theorem B1156587 : Blo 1152637 1156587 := bstep (se 1 (by rfl) ⟨867440, by rfl⟩ : syracuseStep 1156587 = 1734881) B1734881
theorem B1156599 : Blo 1152637 1156599 := bstep (se 1 (by rfl) ⟨867449, by rfl⟩ : syracuseStep 1156599 = 1734899) B1734899
theorem B1156619 : Blo 1152637 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B1156631 : Blo 1152637 1156631 := bstep (se 1 (by rfl) ⟨867473, by rfl⟩ : syracuseStep 1156631 = 1734947) B1734947
theorem B2598425 : Blo 1152637 2598425 := bstep (se 2 (by rfl) ⟨974409, by rfl⟩ : syracuseStep 2598425 = 1948819) B1948819
theorem B2926145 : Blo 1152637 2926145 := bstep (se 2 (by rfl) ⟨1097304, by rfl⟩ : syracuseStep 2926145 = 2194609) B2194609
theorem B2467415 : Blo 1152637 2467415 := bstep (se 1 (by rfl) ⟨1850561, by rfl⟩ : syracuseStep 2467415 = 3701123) B3701123
theorem B2598515 : Blo 1152637 2598515 := bstep (se 1 (by rfl) ⟨1948886, by rfl⟩ : syracuseStep 2598515 = 3897773) B3897773
theorem B2598551 : Blo 1152637 2598551 := bstep (se 1 (by rfl) ⟨1948913, by rfl⟩ : syracuseStep 2598551 = 3897827) B3897827
theorem B2598731 : Blo 1152637 2598731 := bstep (se 1 (by rfl) ⟨1949048, by rfl⟩ : syracuseStep 2598731 = 3898097) B3898097
theorem B2598785 : Blo 1152637 2598785 := bstep (se 2 (by rfl) ⟨974544, by rfl⟩ : syracuseStep 2598785 = 1949089) B1949089
theorem B2959255 : Blo 1152637 2959255 := bstep (se 1 (by rfl) ⟨2219441, by rfl⟩ : syracuseStep 2959255 = 4438883) B4438883
theorem B16623629 : Blo 1152637 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B1976395 : Blo 1152637 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B2599001 : Blo 1152637 2599001 := bstep (se 2 (by rfl) ⟨974625, by rfl⟩ : syracuseStep 2599001 = 1949251) B1949251
theorem B2467979 : Blo 1152637 2467979 := bstep (se 1 (by rfl) ⟨1850984, by rfl⟩ : syracuseStep 2467979 = 3701969) B3701969
theorem B2599091 : Blo 1152637 2599091 := bstep (se 1 (by rfl) ⟨1949318, by rfl⟩ : syracuseStep 2599091 = 3898637) B3898637
theorem B3287243 : Blo 1152637 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B2599127 : Blo 1152637 2599127 := bstep (se 1 (by rfl) ⟨1949345, by rfl⟩ : syracuseStep 2599127 = 3898691) B3898691
theorem B1386763 : Blo 1152637 1386763 := bstep (se 1 (by rfl) ⟨1040072, by rfl⟩ : syracuseStep 1386763 = 2080145) B2080145
theorem B11086145 : Blo 1152637 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B2599307 : Blo 1152637 2599307 := bstep (se 1 (by rfl) ⟨1949480, by rfl⟩ : syracuseStep 2599307 = 3898961) B3898961
theorem B2337203 : Blo 1152637 2337203 := bstep (se 1 (by rfl) ⟨1752902, by rfl⟩ : syracuseStep 2337203 = 3505805) B3505805
theorem B2599361 : Blo 1152637 2599361 := bstep (se 2 (by rfl) ⟨974760, by rfl⟩ : syracuseStep 2599361 = 1949521) B1949521
theorem B5843501 : Blo 1152637 5843501 := bstep (se 3 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 5843501 = 2191313) B2191313
theorem B2599577 : Blo 1152637 2599577 := bstep (se 2 (by rfl) ⟨974841, by rfl⟩ : syracuseStep 2599577 = 1949683) B1949683
theorem B2468569 : Blo 1152637 2468569 := bstep (se 2 (by rfl) ⟨925713, by rfl⟩ : syracuseStep 2468569 = 1851427) B1851427
theorem B2599667 : Blo 1152637 2599667 := bstep (se 1 (by rfl) ⟨1949750, by rfl⟩ : syracuseStep 2599667 = 3899501) B3899501
theorem B19999493 : Blo 1152637 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B2599703 : Blo 1152637 2599703 := bstep (se 1 (by rfl) ⟨1949777, by rfl⟩ : syracuseStep 2599703 = 3899555) B3899555
theorem B2927411 : Blo 1152637 2927411 := bstep (se 1 (by rfl) ⟨2195558, by rfl⟩ : syracuseStep 2927411 = 4391117) B4391117
theorem B22195043 : Blo 1152637 22195043 := bstep (se 1 (by rfl) ⟨16646282, by rfl⟩ : syracuseStep 22195043 = 33292565) B33292565
theorem B2599883 : Blo 1152637 2599883 := bstep (se 1 (by rfl) ⟨1949912, by rfl⟩ : syracuseStep 2599883 = 3899825) B3899825
theorem B2599937 : Blo 1152637 2599937 := bstep (se 2 (by rfl) ⟨974976, by rfl⟩ : syracuseStep 2599937 = 1949953) B1949953
theorem B1977367 : Blo 1152637 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B2600153 : Blo 1152637 2600153 := bstep (se 2 (by rfl) ⟨975057, by rfl⟩ : syracuseStep 2600153 = 1950115) B1950115
theorem B2600243 : Blo 1152637 2600243 := bstep (se 1 (by rfl) ⟨1950182, by rfl⟩ : syracuseStep 2600243 = 3900365) B3900365
theorem B2600279 : Blo 1152637 2600279 := bstep (se 1 (by rfl) ⟨1950209, by rfl⟩ : syracuseStep 2600279 = 3900419) B3900419
theorem B2108825 : Blo 1152637 2108825 := bstep (se 2 (by rfl) ⟨790809, by rfl⟩ : syracuseStep 2108825 = 1581619) B1581619
theorem B2600459 : Blo 1152637 2600459 := bstep (se 1 (by rfl) ⟨1950344, by rfl⟩ : syracuseStep 2600459 = 3900689) B3900689
theorem B2600513 : Blo 1152637 2600513 := bstep (se 2 (by rfl) ⟨975192, by rfl⟩ : syracuseStep 2600513 = 1950385) B1950385
theorem B1846871 : Blo 1152637 1846871 := bstep (se 1 (by rfl) ⟨1385153, by rfl⟩ : syracuseStep 1846871 = 2770307) B2770307
theorem B12496477 : Blo 1152637 12496477 := bstep (se 3 (by rfl) ⟨2343089, by rfl⟩ : syracuseStep 12496477 = 4686179) B4686179
theorem B1846999 : Blo 1152637 1846999 := bstep (se 1 (by rfl) ⟨1385249, by rfl⟩ : syracuseStep 1846999 = 2770499) B2770499
theorem B2469619 : Blo 1152637 2469619 := bstep (se 1 (by rfl) ⟨1852214, by rfl⟩ : syracuseStep 2469619 = 3704429) B3704429
theorem B2600729 : Blo 1152637 2600729 := bstep (se 2 (by rfl) ⟨975273, by rfl⟩ : syracuseStep 2600729 = 1950547) B1950547
theorem B1978187 : Blo 1152637 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B2600819 : Blo 1152637 2600819 := bstep (se 1 (by rfl) ⟨1950614, by rfl⟩ : syracuseStep 2600819 = 3901229) B3901229
theorem B2600855 : Blo 1152637 2600855 := bstep (se 1 (by rfl) ⟨1950641, by rfl⟩ : syracuseStep 2600855 = 3901283) B3901283
theorem B1945559 : Blo 1152637 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B12496913 : Blo 1152637 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B2601035 : Blo 1152637 2601035 := bstep (se 1 (by rfl) ⟨1950776, by rfl⟩ : syracuseStep 2601035 = 3901553) B3901553
theorem B1945687 : Blo 1152637 1945687 := bstep (se 1 (by rfl) ⟨1459265, by rfl⟩ : syracuseStep 1945687 = 2918531) B2918531
theorem B2601089 : Blo 1152637 2601089 := bstep (se 2 (by rfl) ⟨975408, by rfl⟩ : syracuseStep 2601089 = 1950817) B1950817
theorem B2601305 : Blo 1152637 2601305 := bstep (se 2 (by rfl) ⟨975489, by rfl⟩ : syracuseStep 2601305 = 1950979) B1950979
theorem B2601395 : Blo 1152637 2601395 := bstep (se 1 (by rfl) ⟨1951046, by rfl⟩ : syracuseStep 2601395 = 3902093) B3902093
theorem B2601431 : Blo 1152637 2601431 := bstep (se 1 (by rfl) ⟨1951073, by rfl⟩ : syracuseStep 2601431 = 3902147) B3902147
theorem B1847819 : Blo 1152637 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B3289693 : Blo 1152637 3289693 := bstep (se 3 (by rfl) ⟨616817, by rfl⟩ : syracuseStep 3289693 = 1233635) B1233635
theorem B4928131 : Blo 1152637 4928131 := bstep (se 1 (by rfl) ⟨3696098, by rfl⟩ : syracuseStep 4928131 = 7392197) B7392197
theorem B2601611 : Blo 1152637 2601611 := bstep (se 1 (by rfl) ⟨1951208, by rfl⟩ : syracuseStep 2601611 = 3902417) B3902417
theorem B5550743 : Blo 1152637 5550743 := bstep (se 1 (by rfl) ⟨4163057, by rfl⟩ : syracuseStep 5550743 = 8326115) B8326115
theorem B2601665 : Blo 1152637 2601665 := bstep (se 2 (by rfl) ⟨975624, by rfl⟩ : syracuseStep 2601665 = 1951249) B1951249
theorem B1946315 : Blo 1152637 1946315 := bstep (se 1 (by rfl) ⟨1459736, by rfl⟩ : syracuseStep 1946315 = 2919473) B2919473
theorem B1946443 : Blo 1152637 1946443 := bstep (se 1 (by rfl) ⟨1459832, by rfl⟩ : syracuseStep 1946443 = 2919665) B2919665
theorem B6239051 : Blo 1152637 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B3126109 : Blo 1152637 3126109 := bstep (se 3 (by rfl) ⟨586145, by rfl⟩ : syracuseStep 3126109 = 1172291) B1172291
theorem B2601881 : Blo 1152637 2601881 := bstep (se 2 (by rfl) ⟨975705, by rfl⟩ : syracuseStep 2601881 = 1951411) B1951411
theorem B1946585 : Blo 1152637 1946585 := bstep (se 2 (by rfl) ⟨729969, by rfl⟩ : syracuseStep 1946585 = 1459939) B1459939
theorem B2601971 : Blo 1152637 2601971 := bstep (se 1 (by rfl) ⟨1951478, by rfl⟩ : syracuseStep 2601971 = 3902957) B3902957
theorem B2602007 : Blo 1152637 2602007 := bstep (se 1 (by rfl) ⟨1951505, by rfl⟩ : syracuseStep 2602007 = 3903011) B3903011
theorem B1946713 : Blo 1152637 1946713 := bstep (se 2 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 1946713 = 1460035) B1460035
theorem B2602187 : Blo 1152637 2602187 := bstep (se 1 (by rfl) ⟨1951640, by rfl⟩ : syracuseStep 2602187 = 3903281) B3903281
theorem B2602241 : Blo 1152637 2602241 := bstep (se 2 (by rfl) ⟨975840, by rfl⟩ : syracuseStep 2602241 = 1951681) B1951681
theorem B2077975 : Blo 1152637 2077975 := bstep (se 1 (by rfl) ⟨1558481, by rfl⟩ : syracuseStep 2077975 = 3116963) B3116963
theorem B1848665 : Blo 1152637 1848665 := bstep (se 2 (by rfl) ⟨693249, by rfl⟩ : syracuseStep 1848665 = 1386499) B1386499
theorem B1947287 : Blo 1152637 1947287 := bstep (se 1 (by rfl) ⟨1460465, by rfl⟩ : syracuseStep 1947287 = 2920931) B2920931
theorem B1947415 : Blo 1152637 1947415 := bstep (se 1 (by rfl) ⟨1460561, by rfl⟩ : syracuseStep 1947415 = 2921123) B2921123
theorem B1849177 : Blo 1152637 1849177 := bstep (se 2 (by rfl) ⟨693441, by rfl⟩ : syracuseStep 1849177 = 1386883) B1386883
theorem B3290969 : Blo 1152637 3290969 := bstep (se 2 (by rfl) ⟨1234113, by rfl⟩ : syracuseStep 3290969 = 2468227) B2468227
theorem B2635649 : Blo 1152637 2635649 := bstep (se 2 (by rfl) ⟨988368, by rfl⟩ : syracuseStep 2635649 = 1976737) B1976737
theorem B2078681 : Blo 1152637 2078681 := bstep (se 2 (by rfl) ⟨779505, by rfl⟩ : syracuseStep 2078681 = 1559011) B1559011
theorem B14039075 : Blo 1152637 14039075 := bstep (se 1 (by rfl) ⟨10529306, by rfl⟩ : syracuseStep 14039075 = 21058613) B21058613
theorem B5847389 : Blo 1152637 5847389 := bstep (se 3 (by rfl) ⟨1096385, by rfl⟩ : syracuseStep 5847389 = 2192771) B2192771
theorem B1948043 : Blo 1152637 1948043 := bstep (se 1 (by rfl) ⟨1461032, by rfl⟩ : syracuseStep 1948043 = 2922065) B2922065
theorem B4929943 : Blo 1152637 4929943 := bstep (se 1 (by rfl) ⟨3697457, by rfl⟩ : syracuseStep 4929943 = 7394915) B7394915
theorem B1948171 : Blo 1152637 1948171 := bstep (se 1 (by rfl) ⟨1461128, by rfl⟩ : syracuseStep 1948171 = 2922257) B2922257
theorem B14989859 : Blo 1152637 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B1948313 : Blo 1152637 1948313 := bstep (se 2 (by rfl) ⟨730617, by rfl⟩ : syracuseStep 1948313 = 1461235) B1461235
theorem B1948441 : Blo 1152637 1948441 := bstep (se 2 (by rfl) ⟨730665, by rfl⟩ : syracuseStep 1948441 = 1461331) B1461331
theorem B6568883 : Blo 1152637 6568883 := bstep (se 1 (by rfl) ⟨4926662, by rfl⟩ : syracuseStep 6568883 = 9853325) B9853325
theorem B2341811 : Blo 1152637 2341811 := bstep (se 1 (by rfl) ⟨1756358, by rfl⟩ : syracuseStep 2341811 = 3512717) B3512717
theorem B4996099 : Blo 1152637 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B16628753 : Blo 1152637 16628753 := bstep (se 2 (by rfl) ⟨6235782, by rfl⟩ : syracuseStep 16628753 = 12471565) B12471565
theorem B4930577 : Blo 1152637 4930577 := bstep (se 2 (by rfl) ⟨1848966, by rfl⟩ : syracuseStep 4930577 = 3697933) B3697933
theorem B6667309 : Blo 1152637 6667309 := bstep (se 3 (by rfl) ⟨1250120, by rfl⟩ : syracuseStep 6667309 = 2500241) B2500241
theorem B13155533 : Blo 1152637 13155533 := bstep (se 3 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 13155533 = 4933325) B4933325
theorem B1949015 : Blo 1152637 1949015 := bstep (se 1 (by rfl) ⟨1461761, by rfl⟩ : syracuseStep 1949015 = 2923523) B2923523
theorem B3292609 : Blo 1152637 3292609 := bstep (se 2 (by rfl) ⟨1234728, by rfl⟩ : syracuseStep 3292609 = 2469457) B2469457
theorem B1949143 : Blo 1152637 1949143 := bstep (se 1 (by rfl) ⟨1461857, by rfl⟩ : syracuseStep 1949143 = 2923715) B2923715
theorem B7388765 : Blo 1152637 7388765 := bstep (se 3 (by rfl) ⟨1385393, by rfl⟩ : syracuseStep 7388765 = 2770787) B2770787
theorem B4931275 : Blo 1152637 4931275 := bstep (se 1 (by rfl) ⟨3698456, by rfl⟩ : syracuseStep 4931275 = 7396913) B7396913
theorem B4931549 : Blo 1152637 4931549 := bstep (se 3 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 4931549 = 1849331) B1849331
theorem B9879569 : Blo 1152637 9879569 := bstep (se 2 (by rfl) ⟨3704838, by rfl⟩ : syracuseStep 9879569 = 7409677) B7409677
theorem B1949771 : Blo 1152637 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B1753177 : Blo 1152637 1753177 := bstep (se 2 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 1753177 = 1314883) B1314883
theorem B1949899 : Blo 1152637 1949899 := bstep (se 1 (by rfl) ⟨1462424, by rfl⟩ : syracuseStep 1949899 = 2924849) B2924849
theorem B2081011 : Blo 1152637 2081011 := bstep (se 1 (by rfl) ⟨1560758, by rfl⟩ : syracuseStep 2081011 = 3121517) B3121517
theorem B4931891 : Blo 1152637 4931891 := bstep (se 1 (by rfl) ⟨3698918, by rfl⟩ : syracuseStep 4931891 = 7397837) B7397837
theorem B2965825 : Blo 1152637 2965825 := bstep (se 2 (by rfl) ⟨1112184, by rfl⟩ : syracuseStep 2965825 = 2224369) B2224369
theorem B3948875 : Blo 1152637 3948875 := bstep (se 1 (by rfl) ⟨2961656, by rfl⟩ : syracuseStep 3948875 = 5923313) B5923313
theorem B1950041 : Blo 1152637 1950041 := bstep (se 2 (by rfl) ⟨731265, by rfl⟩ : syracuseStep 1950041 = 1462531) B1462531
theorem B6570341 : Blo 1152637 6570341 := bstep (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) B1231939
theorem B17088869 : Blo 1152637 17088869 := bstep (se 4 (by rfl) ⟨1602081, by rfl⟩ : syracuseStep 17088869 = 3204163) B3204163
theorem B5849495 : Blo 1152637 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B1950169 : Blo 1152637 1950169 := bstep (se 2 (by rfl) ⟨731313, by rfl⟩ : syracuseStep 1950169 = 1462627) B1462627
theorem B5620241 : Blo 1152637 5620241 := bstep (se 2 (by rfl) ⟨2107590, by rfl⟩ : syracuseStep 5620241 = 4215181) B4215181
theorem B2081305 : Blo 1152637 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B1458967 : Blo 1152637 1458967 := bstep (se 1 (by rfl) ⟨1094225, by rfl⟩ : syracuseStep 1458967 = 2188451) B2188451
theorem B9356077 : Blo 1152637 9356077 := bstep (se 3 (by rfl) ⟨1754264, by rfl⟩ : syracuseStep 9356077 = 3508529) B3508529
theorem B1852247 : Blo 1152637 1852247 := bstep (se 1 (by rfl) ⟨1389185, by rfl⟩ : syracuseStep 1852247 = 2778371) B2778371
theorem B1950743 : Blo 1152637 1950743 := bstep (se 1 (by rfl) ⟨1463057, by rfl⟩ : syracuseStep 1950743 = 2926115) B2926115
theorem B1950871 : Blo 1152637 1950871 := bstep (se 1 (by rfl) ⟨1463153, by rfl⟩ : syracuseStep 1950871 = 2926307) B2926307
theorem B5260567 : Blo 1152637 5260567 := bstep (se 1 (by rfl) ⟨3945425, by rfl⟩ : syracuseStep 5260567 = 7890851) B7890851
theorem B5916377 : Blo 1152637 5916377 := bstep (se 2 (by rfl) ⟨2218641, by rfl⟩ : syracuseStep 5916377 = 4437283) B4437283
theorem B1951499 : Blo 1152637 1951499 := bstep (se 1 (by rfl) ⟨1463624, by rfl⟩ : syracuseStep 1951499 = 2927249) B2927249
theorem B2082689 : Blo 1152637 2082689 := bstep (se 2 (by rfl) ⟨781008, by rfl⟩ : syracuseStep 2082689 = 1562017) B1562017
theorem B1951627 : Blo 1152637 1951627 := bstep (se 1 (by rfl) ⟨1463720, by rfl⟩ : syracuseStep 1951627 = 2927441) B2927441
theorem B4376537 : Blo 1152637 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B1951769 : Blo 1152637 1951769 := bstep (se 2 (by rfl) ⟨731913, by rfl⟩ : syracuseStep 1951769 = 1463827) B1463827
theorem B4442177 : Blo 1152637 4442177 := bstep (se 2 (by rfl) ⟨1665816, by rfl⟩ : syracuseStep 4442177 = 3331633) B3331633
theorem B4376855 : Blo 1152637 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B1296823 : Blo 1152637 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B1460683 : Blo 1152637 1460683 := bstep (se 1 (by rfl) ⟨1095512, by rfl⟩ : syracuseStep 1460683 = 2191025) B2191025
theorem B3754457 : Blo 1152637 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B7490123 : Blo 1152637 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B1297003 : Blo 1152637 1297003 := bstep (se 1 (by rfl) ⟨972752, by rfl⟩ : syracuseStep 1297003 = 1945505) B1945505
theorem B4934317 : Blo 1152637 4934317 := bstep (se 3 (by rfl) ⟨925184, by rfl⟩ : syracuseStep 4934317 = 1850369) B1850369
theorem B1297111 : Blo 1152637 1297111 := bstep (se 1 (by rfl) ⟨972833, by rfl⟩ : syracuseStep 1297111 = 1945667) B1945667
theorem B20007665 : Blo 1152637 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B1231691 : Blo 1152637 1231691 := bstep (se 1 (by rfl) ⟨923768, by rfl⟩ : syracuseStep 1231691 = 1847537) B1847537
theorem B9849701 : Blo 1152637 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B1297291 : Blo 1152637 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B4377523 : Blo 1152637 4377523 := bstep (se 1 (by rfl) ⟨3283142, by rfl⟩ : syracuseStep 4377523 = 6566285) B6566285
theorem B1297399 : Blo 1152637 1297399 := bstep (se 1 (by rfl) ⟨973049, by rfl⟩ : syracuseStep 1297399 = 1946099) B1946099
theorem B2083915 : Blo 1152637 2083915 := bstep (se 1 (by rfl) ⟨1562936, by rfl⟩ : syracuseStep 2083915 = 3125873) B3125873
theorem B1297579 : Blo 1152637 1297579 := bstep (se 1 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 1297579 = 1946369) B1946369
theorem B1297687 : Blo 1152637 1297687 := bstep (se 1 (by rfl) ⟨973265, by rfl⟩ : syracuseStep 1297687 = 1946531) B1946531
theorem B1461655 : Blo 1152637 1461655 := bstep (se 1 (by rfl) ⟨1096241, by rfl⟩ : syracuseStep 1461655 = 2192483) B2192483
theorem B1297867 : Blo 1152637 1297867 := bstep (se 1 (by rfl) ⟨973400, by rfl⟩ : syracuseStep 1297867 = 1946801) B1946801
theorem B1756631 : Blo 1152637 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B1297975 : Blo 1152637 1297975 := bstep (se 1 (by rfl) ⟨973481, by rfl⟩ : syracuseStep 1297975 = 1946963) B1946963
theorem B5557835 : Blo 1152637 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B10145459 : Blo 1152637 10145459 := bstep (se 1 (by rfl) ⟨7609094, by rfl⟩ : syracuseStep 10145459 = 15218189) B15218189
theorem B1298155 : Blo 1152637 1298155 := bstep (se 1 (by rfl) ⟨973616, by rfl⟩ : syracuseStep 1298155 = 1947233) B1947233
theorem B6246209 : Blo 1152637 6246209 := bstep (se 2 (by rfl) ⟨2342328, by rfl⟩ : syracuseStep 6246209 = 4684657) B4684657
theorem B1560395 : Blo 1152637 1560395 := bstep (se 1 (by rfl) ⟨1170296, by rfl⟩ : syracuseStep 1560395 = 2340593) B2340593
theorem B1298263 : Blo 1152637 1298263 := bstep (se 1 (by rfl) ⟨973697, by rfl⟩ : syracuseStep 1298263 = 1947395) B1947395
theorem B29642597 : Blo 1152637 29642597 := bstep (se 4 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 29642597 = 5557987) B5557987
theorem B5853059 : Blo 1152637 5853059 := bstep (se 1 (by rfl) ⟨4389794, by rfl⟩ : syracuseStep 5853059 = 8779589) B8779589
theorem B1298443 : Blo 1152637 1298443 := bstep (se 1 (by rfl) ⟨973832, by rfl⟩ : syracuseStep 1298443 = 1947665) B1947665
theorem B1298551 : Blo 1152637 1298551 := bstep (se 1 (by rfl) ⟨973913, by rfl⟩ : syracuseStep 1298551 = 1947827) B1947827
theorem B4378769 : Blo 1152637 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B1462475 : Blo 1152637 1462475 := bstep (se 1 (by rfl) ⟨1096856, by rfl⟩ : syracuseStep 1462475 = 2193713) B2193713
theorem B1298731 : Blo 1152637 1298731 := bstep (se 1 (by rfl) ⟨974048, by rfl⟩ : syracuseStep 1298731 = 1948097) B1948097
theorem B1298839 : Blo 1152637 1298839 := bstep (se 1 (by rfl) ⟨974129, by rfl⟩ : syracuseStep 1298839 = 1948259) B1948259
theorem B9851341 : Blo 1152637 9851341 := bstep (se 3 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 9851341 = 3694253) B3694253
theorem B1233451 : Blo 1152637 1233451 := bstep (se 1 (by rfl) ⟨925088, by rfl⟩ : syracuseStep 1233451 = 1850177) B1850177
theorem B7393837 : Blo 1152637 7393837 := bstep (se 3 (by rfl) ⟨1386344, by rfl⟩ : syracuseStep 7393837 = 2772689) B2772689
theorem B1299019 : Blo 1152637 1299019 := bstep (se 1 (by rfl) ⟨974264, by rfl⟩ : syracuseStep 1299019 = 1948529) B1948529
theorem B1299127 : Blo 1152637 1299127 := bstep (se 1 (by rfl) ⟨974345, by rfl⟩ : syracuseStep 1299127 = 1948691) B1948691
theorem B1757963 : Blo 1152637 1757963 := bstep (se 1 (by rfl) ⟨1318472, by rfl⟩ : syracuseStep 1757963 = 2636945) B2636945
theorem B4379467 : Blo 1152637 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B2773835 : Blo 1152637 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B40555363 : Blo 1152637 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1299307 : Blo 1152637 1299307 := bstep (se 1 (by rfl) ⟨974480, by rfl⟩ : syracuseStep 1299307 = 1948961) B1948961
theorem B1463179 : Blo 1152637 1463179 := bstep (se 1 (by rfl) ⟨1097384, by rfl⟩ : syracuseStep 1463179 = 2194769) B2194769
theorem B1299415 : Blo 1152637 1299415 := bstep (se 1 (by rfl) ⟨974561, by rfl⟩ : syracuseStep 1299415 = 1949123) B1949123
theorem B1758169 : Blo 1152637 1758169 := bstep (se 2 (by rfl) ⟨659313, by rfl⟩ : syracuseStep 1758169 = 1318627) B1318627
theorem B4936727 : Blo 1152637 4936727 := bstep (se 1 (by rfl) ⟨3702545, by rfl⟩ : syracuseStep 4936727 = 7405091) B7405091
theorem B4379741 : Blo 1152637 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B1299595 : Blo 1152637 1299595 := bstep (se 1 (by rfl) ⟨974696, by rfl⟩ : syracuseStep 1299595 = 1949393) B1949393
theorem B41047181 : Blo 1152637 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B1463447 : Blo 1152637 1463447 := bstep (se 1 (by rfl) ⟨1097585, by rfl⟩ : syracuseStep 1463447 = 2195171) B2195171
theorem B1299703 : Blo 1152637 1299703 := bstep (se 1 (by rfl) ⟨974777, by rfl⟩ : syracuseStep 1299703 = 1949555) B1949555
theorem B1299883 : Blo 1152637 1299883 := bstep (se 1 (by rfl) ⟨974912, by rfl⟩ : syracuseStep 1299883 = 1949825) B1949825
theorem B4675009 : Blo 1152637 4675009 := bstep (se 2 (by rfl) ⟨1753128, by rfl⟩ : syracuseStep 4675009 = 3506257) B3506257
theorem B1299991 : Blo 1152637 1299991 := bstep (se 1 (by rfl) ⟨974993, by rfl⟩ : syracuseStep 1299991 = 1949987) B1949987
theorem B1300171 : Blo 1152637 1300171 := bstep (se 1 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 1300171 = 1950257) B1950257
theorem B19519217 : Blo 1152637 19519217 := bstep (se 2 (by rfl) ⟨7319706, by rfl⟩ : syracuseStep 19519217 = 14639413) B14639413
theorem B9852677 : Blo 1152637 9852677 := bstep (se 4 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 9852677 = 1847377) B1847377
theorem B4380439 : Blo 1152637 4380439 := bstep (se 1 (by rfl) ⟨3285329, by rfl⟩ : syracuseStep 4380439 = 6570659) B6570659
theorem B1300279 : Blo 1152637 1300279 := bstep (se 1 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 1300279 = 1950419) B1950419
theorem B8312651 : Blo 1152637 8312651 := bstep (se 1 (by rfl) ⟨6234488, by rfl⟩ : syracuseStep 8312651 = 12468977) B12468977
theorem B33249203 : Blo 1152637 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B1300459 : Blo 1152637 1300459 := bstep (se 1 (by rfl) ⟨975344, by rfl⟩ : syracuseStep 1300459 = 1950689) B1950689
theorem B6576173 : Blo 1152637 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B1300567 : Blo 1152637 1300567 := bstep (se 1 (by rfl) ⟨975425, by rfl⟩ : syracuseStep 1300567 = 1950851) B1950851
theorem B1235083 : Blo 1152637 1235083 := bstep (se 1 (by rfl) ⟨926312, by rfl⟩ : syracuseStep 1235083 = 1852625) B1852625
theorem B1300747 : Blo 1152637 1300747 := bstep (se 1 (by rfl) ⟨975560, by rfl⟩ : syracuseStep 1300747 = 1951121) B1951121
theorem B5921099 : Blo 1152637 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B1300855 : Blo 1152637 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B1301035 : Blo 1152637 1301035 := bstep (se 1 (by rfl) ⟨975776, by rfl⟩ : syracuseStep 1301035 = 1951553) B1951553
theorem B4381229 : Blo 1152637 4381229 := bstep (se 3 (by rfl) ⟨821480, by rfl⟩ : syracuseStep 4381229 = 1642961) B1642961
theorem B1301143 : Blo 1152637 1301143 := bstep (se 1 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 1301143 = 1951715) B1951715
theorem B4938641 : Blo 1152637 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B8772785 : Blo 1152637 8772785 := bstep (se 2 (by rfl) ⟨3289794, by rfl⟩ : syracuseStep 8772785 = 6579589) B6579589
theorem B3890483 : Blo 1152637 3890483 := bstep (se 1 (by rfl) ⟨2917862, by rfl⟩ : syracuseStep 3890483 = 5835725) B5835725
theorem B4742489 : Blo 1152637 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B3333469 : Blo 1152637 3333469 := bstep (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) B1250051
theorem B119922061 : Blo 1152637 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B3890753 : Blo 1152637 3890753 := bstep (se 2 (by rfl) ⟨1459032, by rfl⟩ : syracuseStep 3890753 = 2918065) B2918065
theorem B8773271 : Blo 1152637 8773271 := bstep (se 1 (by rfl) ⟨6579953, by rfl⟩ : syracuseStep 8773271 = 13159907) B13159907
theorem B1335083 : Blo 1152637 1335083 := bstep (se 1 (by rfl) ⟨1001312, by rfl⟩ : syracuseStep 1335083 = 2002625) B2002625
theorem B4939613 : Blo 1152637 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B4382657 : Blo 1152637 4382657 := bstep (se 2 (by rfl) ⟨1643496, by rfl⟩ : syracuseStep 4382657 = 3286993) B3286993
theorem B4218817 : Blo 1152637 4218817 := bstep (se 2 (by rfl) ⟨1582056, by rfl⟩ : syracuseStep 4218817 = 3164113) B3164113
theorem B16670681 : Blo 1152637 16670681 := bstep (se 2 (by rfl) ⟨6251505, by rfl⟩ : syracuseStep 16670681 = 12503011) B12503011
theorem B3891293 : Blo 1152637 3891293 := bstep (se 3 (by rfl) ⟨729617, by rfl⟩ : syracuseStep 3891293 = 1459235) B1459235
theorem B1728971 : Blo 1152637 1728971 := bstep (se 1 (by rfl) ⟨1296728, by rfl⟩ : syracuseStep 1728971 = 2593457) B2593457
theorem B1728983 : Blo 1152637 1728983 := bstep (se 1 (by rfl) ⟨1296737, by rfl⟩ : syracuseStep 1728983 = 2593475) B2593475
theorem B1729049 : Blo 1152637 1729049 := bstep (se 2 (by rfl) ⟨648393, by rfl⟩ : syracuseStep 1729049 = 1296787) B1296787
theorem B4448857 : Blo 1152637 4448857 := bstep (se 2 (by rfl) ⟨1668321, by rfl⟩ : syracuseStep 4448857 = 3336643) B3336643
theorem B1729163 : Blo 1152637 1729163 := bstep (se 1 (by rfl) ⟨1296872, by rfl⟩ : syracuseStep 1729163 = 2593745) B2593745
theorem B1729175 : Blo 1152637 1729175 := bstep (se 1 (by rfl) ⟨1296881, by rfl⟩ : syracuseStep 1729175 = 2593763) B2593763
theorem B1729241 : Blo 1152637 1729241 := bstep (se 2 (by rfl) ⟨648465, by rfl⟩ : syracuseStep 1729241 = 1296931) B1296931
theorem B1729355 : Blo 1152637 1729355 := bstep (se 1 (by rfl) ⟨1297016, by rfl⟩ : syracuseStep 1729355 = 2594033) B2594033
theorem B1729367 : Blo 1152637 1729367 := bstep (se 1 (by rfl) ⟨1297025, by rfl⟩ : syracuseStep 1729367 = 2594051) B2594051
theorem B1729433 : Blo 1152637 1729433 := bstep (se 2 (by rfl) ⟨648537, by rfl⟩ : syracuseStep 1729433 = 1297075) B1297075
theorem B1729547 : Blo 1152637 1729547 := bstep (se 1 (by rfl) ⟨1297160, by rfl⟩ : syracuseStep 1729547 = 2594321) B2594321
theorem B1729559 : Blo 1152637 1729559 := bstep (se 1 (by rfl) ⟨1297169, by rfl⟩ : syracuseStep 1729559 = 2594339) B2594339
theorem B1729625 : Blo 1152637 1729625 := bstep (se 2 (by rfl) ⟨648609, by rfl⟩ : syracuseStep 1729625 = 1297219) B1297219
theorem B1729739 : Blo 1152637 1729739 := bstep (se 1 (by rfl) ⟨1297304, by rfl⟩ : syracuseStep 1729739 = 2594609) B2594609
theorem B3892427 : Blo 1152637 3892427 := bstep (se 1 (by rfl) ⟨2919320, by rfl⟩ : syracuseStep 3892427 = 5838641) B5838641
theorem B1729751 : Blo 1152637 1729751 := bstep (se 1 (by rfl) ⟨1297313, by rfl⟩ : syracuseStep 1729751 = 2594627) B2594627
theorem B1729817 : Blo 1152637 1729817 := bstep (se 2 (by rfl) ⟨648681, by rfl⟩ : syracuseStep 1729817 = 1297363) B1297363
theorem B2188595 : Blo 1152637 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B2188633 : Blo 1152637 2188633 := bstep (se 2 (by rfl) ⟨820737, by rfl⟩ : syracuseStep 2188633 = 1641475) B1641475
theorem B1729931 : Blo 1152637 1729931 := bstep (se 1 (by rfl) ⟨1297448, by rfl⟩ : syracuseStep 1729931 = 2594897) B2594897
theorem B4384145 : Blo 1152637 4384145 := bstep (se 2 (by rfl) ⟨1644054, by rfl⟩ : syracuseStep 4384145 = 3288109) B3288109
theorem B1729943 : Blo 1152637 1729943 := bstep (se 1 (by rfl) ⟨1297457, by rfl⟩ : syracuseStep 1729943 = 2594915) B2594915
theorem B3696023 : Blo 1152637 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B1730009 : Blo 1152637 1730009 := bstep (se 2 (by rfl) ⟨648753, by rfl⟩ : syracuseStep 1730009 = 1297507) B1297507
theorem B3892697 : Blo 1152637 3892697 := bstep (se 2 (by rfl) ⟨1459761, by rfl⟩ : syracuseStep 3892697 = 2919523) B2919523
theorem B3696151 : Blo 1152637 3696151 := bstep (se 1 (by rfl) ⟨2772113, by rfl⟩ : syracuseStep 3696151 = 5544227) B5544227
theorem B1730123 : Blo 1152637 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B1730135 : Blo 1152637 1730135 := bstep (se 1 (by rfl) ⟨1297601, by rfl⟩ : syracuseStep 1730135 = 2595203) B2595203
theorem B4449937 : Blo 1152637 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B6579863 : Blo 1152637 6579863 := bstep (se 1 (by rfl) ⟨4934897, by rfl⟩ : syracuseStep 6579863 = 9869795) B9869795
theorem B1730201 : Blo 1152637 1730201 := bstep (se 2 (by rfl) ⟨648825, by rfl⟩ : syracuseStep 1730201 = 1297651) B1297651
theorem B1730315 : Blo 1152637 1730315 := bstep (se 1 (by rfl) ⟨1297736, by rfl⟩ : syracuseStep 1730315 = 2595473) B2595473
theorem B1730327 : Blo 1152637 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B3696407 : Blo 1152637 3696407 := bstep (se 1 (by rfl) ⟨2772305, by rfl⟩ : syracuseStep 3696407 = 5544611) B5544611
theorem B2189081 : Blo 1152637 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B1730393 : Blo 1152637 1730393 := bstep (se 2 (by rfl) ⟨648897, by rfl⟩ : syracuseStep 1730393 = 1297795) B1297795
theorem B4384601 : Blo 1152637 4384601 := bstep (se 2 (by rfl) ⟨1644225, by rfl⟩ : syracuseStep 4384601 = 3288451) B3288451
theorem B1730507 : Blo 1152637 1730507 := bstep (se 1 (by rfl) ⟨1297880, by rfl⟩ : syracuseStep 1730507 = 2595761) B2595761
theorem B1730519 : Blo 1152637 1730519 := bstep (se 1 (by rfl) ⟨1297889, by rfl⟩ : syracuseStep 1730519 = 2595779) B2595779
theorem B1730585 : Blo 1152637 1730585 := bstep (se 2 (by rfl) ⟨648969, by rfl⟩ : syracuseStep 1730585 = 1297939) B1297939
theorem B4384813 : Blo 1152637 4384813 := bstep (se 3 (by rfl) ⟨822152, by rfl⟩ : syracuseStep 4384813 = 1644305) B1644305
theorem B1730699 : Blo 1152637 1730699 := bstep (se 1 (by rfl) ⟨1298024, by rfl⟩ : syracuseStep 1730699 = 2596049) B2596049
theorem B29550743 : Blo 1152637 29550743 := bstep (se 1 (by rfl) ⟨22163057, by rfl⟩ : syracuseStep 29550743 = 44326115) B44326115
theorem B3893399 : Blo 1152637 3893399 := bstep (se 1 (by rfl) ⟨2920049, by rfl⟩ : syracuseStep 3893399 = 5840099) B5840099
theorem B1730711 : Blo 1152637 1730711 := bstep (se 1 (by rfl) ⟨1298033, by rfl⟩ : syracuseStep 1730711 = 2596067) B2596067
theorem B1730777 : Blo 1152637 1730777 := bstep (se 2 (by rfl) ⟨649041, by rfl⟩ : syracuseStep 1730777 = 1298083) B1298083
theorem B1730891 : Blo 1152637 1730891 := bstep (se 1 (by rfl) ⟨1298168, by rfl⟩ : syracuseStep 1730891 = 2596337) B2596337
theorem B1730903 : Blo 1152637 1730903 := bstep (se 1 (by rfl) ⟨1298177, by rfl⟩ : syracuseStep 1730903 = 2596355) B2596355
theorem B4385117 : Blo 1152637 4385117 := bstep (se 3 (by rfl) ⟨822209, by rfl⟩ : syracuseStep 4385117 = 1644419) B1644419
theorem B1730969 : Blo 1152637 1730969 := bstep (se 2 (by rfl) ⟨649113, by rfl⟩ : syracuseStep 1730969 = 1298227) B1298227
theorem B2189825 : Blo 1152637 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B1731083 : Blo 1152637 1731083 := bstep (se 1 (by rfl) ⟨1298312, by rfl⟩ : syracuseStep 1731083 = 2596625) B2596625
theorem B1731095 : Blo 1152637 1731095 := bstep (se 1 (by rfl) ⟨1298321, by rfl⟩ : syracuseStep 1731095 = 2596643) B2596643
theorem B10119755 : Blo 1152637 10119755 := bstep (se 1 (by rfl) ⟨7589816, by rfl⟩ : syracuseStep 10119755 = 15179633) B15179633
theorem B1731161 : Blo 1152637 1731161 := bstep (se 2 (by rfl) ⟨649185, by rfl⟩ : syracuseStep 1731161 = 1298371) B1298371
theorem B13167197 : Blo 1152637 13167197 := bstep (se 3 (by rfl) ⟨2468849, by rfl⟩ : syracuseStep 13167197 = 4937699) B4937699
theorem B3893939 : Blo 1152637 3893939 := bstep (se 1 (by rfl) ⟨2920454, by rfl⟩ : syracuseStep 3893939 = 5840909) B5840909
theorem B1731275 : Blo 1152637 1731275 := bstep (se 1 (by rfl) ⟨1298456, by rfl⟩ : syracuseStep 1731275 = 2596913) B2596913
theorem B1731287 : Blo 1152637 1731287 := bstep (se 1 (by rfl) ⟨1298465, by rfl⟩ : syracuseStep 1731287 = 2596931) B2596931
theorem B2190091 : Blo 1152637 2190091 := bstep (se 1 (by rfl) ⟨1642568, by rfl⟩ : syracuseStep 2190091 = 3285137) B3285137
theorem B1731353 : Blo 1152637 1731353 := bstep (se 2 (by rfl) ⟨649257, by rfl⟩ : syracuseStep 1731353 = 1298515) B1298515
theorem B85355329 : Blo 1152637 85355329 := bstep (se 2 (by rfl) ⟨32008248, by rfl⟩ : syracuseStep 85355329 = 64016497) B64016497
theorem B3697483 : Blo 1152637 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B1731467 : Blo 1152637 1731467 := bstep (se 1 (by rfl) ⟨1298600, by rfl⟩ : syracuseStep 1731467 = 2597201) B2597201
theorem B1731479 : Blo 1152637 1731479 := bstep (se 1 (by rfl) ⟨1298609, by rfl⟩ : syracuseStep 1731479 = 2597219) B2597219
theorem B7203763 : Blo 1152637 7203763 := bstep (se 1 (by rfl) ⟨5402822, by rfl⟩ : syracuseStep 7203763 = 10805645) B10805645
theorem B3894209 : Blo 1152637 3894209 := bstep (se 2 (by rfl) ⟨1460328, by rfl⟩ : syracuseStep 3894209 = 2920657) B2920657
theorem B3337163 : Blo 1152637 3337163 := bstep (se 1 (by rfl) ⟨2502872, by rfl⟩ : syracuseStep 3337163 = 5005745) B5005745
theorem B3697625 : Blo 1152637 3697625 := bstep (se 2 (by rfl) ⟨1386609, by rfl⟩ : syracuseStep 3697625 = 2773219) B2773219
theorem B1731545 : Blo 1152637 1731545 := bstep (se 2 (by rfl) ⟨649329, by rfl⟩ : syracuseStep 1731545 = 1298659) B1298659
theorem B4156439 : Blo 1152637 4156439 := bstep (se 1 (by rfl) ⟨3117329, by rfl⟩ : syracuseStep 4156439 = 6234659) B6234659
theorem B3697739 : Blo 1152637 3697739 := bstep (se 1 (by rfl) ⟨2773304, by rfl⟩ : syracuseStep 3697739 = 5546609) B5546609
theorem B1731659 : Blo 1152637 1731659 := bstep (se 1 (by rfl) ⟨1298744, by rfl⟩ : syracuseStep 1731659 = 2597489) B2597489
theorem B1731671 : Blo 1152637 1731671 := bstep (se 1 (by rfl) ⟨1298753, by rfl⟩ : syracuseStep 1731671 = 2597507) B2597507
theorem B1731737 : Blo 1152637 1731737 := bstep (se 2 (by rfl) ⟨649401, by rfl⟩ : syracuseStep 1731737 = 1298803) B1298803
theorem B2190539 : Blo 1152637 2190539 := bstep (se 1 (by rfl) ⟨1642904, by rfl⟩ : syracuseStep 2190539 = 3285809) B3285809
theorem B1731851 : Blo 1152637 1731851 := bstep (se 1 (by rfl) ⟨1298888, by rfl⟩ : syracuseStep 1731851 = 2597777) B2597777
theorem B1731863 : Blo 1152637 1731863 := bstep (se 1 (by rfl) ⟨1298897, by rfl⟩ : syracuseStep 1731863 = 2597795) B2597795
theorem B1731929 : Blo 1152637 1731929 := bstep (se 2 (by rfl) ⟨649473, by rfl⟩ : syracuseStep 1731929 = 1298947) B1298947
theorem B2190721 : Blo 1152637 2190721 := bstep (se 2 (by rfl) ⟨821520, by rfl⟩ : syracuseStep 2190721 = 1643041) B1643041
theorem B3698099 : Blo 1152637 3698099 := bstep (se 1 (by rfl) ⟨2773574, by rfl⟩ : syracuseStep 3698099 = 5547149) B5547149
theorem B1732043 : Blo 1152637 1732043 := bstep (se 1 (by rfl) ⟨1299032, by rfl⟩ : syracuseStep 1732043 = 2598065) B2598065
theorem B1732055 : Blo 1152637 1732055 := bstep (se 1 (by rfl) ⟨1299041, by rfl⟩ : syracuseStep 1732055 = 2598083) B2598083
theorem B3894749 : Blo 1152637 3894749 := bstep (se 3 (by rfl) ⟨730265, by rfl⟩ : syracuseStep 3894749 = 1460531) B1460531
theorem B1732121 : Blo 1152637 1732121 := bstep (se 2 (by rfl) ⟨649545, by rfl⟩ : syracuseStep 1732121 = 1299091) B1299091
theorem B1732235 : Blo 1152637 1732235 := bstep (se 1 (by rfl) ⟨1299176, by rfl⟩ : syracuseStep 1732235 = 2598353) B2598353
theorem B1732247 : Blo 1152637 1732247 := bstep (se 1 (by rfl) ⟨1299185, by rfl⟩ : syracuseStep 1732247 = 2598371) B2598371
theorem B2191063 : Blo 1152637 2191063 := bstep (se 1 (by rfl) ⟨1643297, by rfl⟩ : syracuseStep 2191063 = 3286595) B3286595
theorem B1732313 : Blo 1152637 1732313 := bstep (se 2 (by rfl) ⟨649617, by rfl⟩ : syracuseStep 1732313 = 1299235) B1299235
theorem B1732427 : Blo 1152637 1732427 := bstep (se 1 (by rfl) ⟨1299320, by rfl⟩ : syracuseStep 1732427 = 2598641) B2598641
theorem B1732439 : Blo 1152637 1732439 := bstep (se 1 (by rfl) ⟨1299329, by rfl⟩ : syracuseStep 1732439 = 2598659) B2598659
theorem B1732505 : Blo 1152637 1732505 := bstep (se 2 (by rfl) ⟨649689, by rfl⟩ : syracuseStep 1732505 = 1299379) B1299379
theorem B2191283 : Blo 1152637 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B21032921 : Blo 1152637 21032921 := bstep (se 2 (by rfl) ⟨7887345, by rfl⟩ : syracuseStep 21032921 = 15774691) B15774691
theorem B1732619 : Blo 1152637 1732619 := bstep (se 1 (by rfl) ⟨1299464, by rfl⟩ : syracuseStep 1732619 = 2598929) B2598929
theorem B1732631 : Blo 1152637 1732631 := bstep (se 1 (by rfl) ⟨1299473, by rfl⟩ : syracuseStep 1732631 = 2598947) B2598947
theorem B1732697 : Blo 1152637 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B2191511 : Blo 1152637 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B3698867 : Blo 1152637 3698867 := bstep (se 1 (by rfl) ⟨2774150, by rfl⟩ : syracuseStep 3698867 = 5548301) B5548301
theorem B1732811 : Blo 1152637 1732811 := bstep (se 1 (by rfl) ⟨1299608, by rfl⟩ : syracuseStep 1732811 = 2599217) B2599217
theorem B1732823 : Blo 1152637 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B1732889 : Blo 1152637 1732889 := bstep (se 2 (by rfl) ⟨649833, by rfl⟩ : syracuseStep 1732889 = 1299667) B1299667
theorem B1733003 : Blo 1152637 1733003 := bstep (se 1 (by rfl) ⟨1299752, by rfl⟩ : syracuseStep 1733003 = 2599505) B2599505
theorem B1733015 : Blo 1152637 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B2191769 : Blo 1152637 2191769 := bstep (se 2 (by rfl) ⟨821913, by rfl⟩ : syracuseStep 2191769 = 1643827) B1643827
theorem B1733081 : Blo 1152637 1733081 := bstep (se 2 (by rfl) ⟨649905, by rfl⟩ : syracuseStep 1733081 = 1299811) B1299811
theorem B3699265 : Blo 1152637 3699265 := bstep (se 2 (by rfl) ⟨1387224, by rfl⟩ : syracuseStep 3699265 = 2774449) B2774449
theorem B3895883 : Blo 1152637 3895883 := bstep (se 1 (by rfl) ⟨2921912, by rfl⟩ : syracuseStep 3895883 = 5843825) B5843825
theorem B1733195 : Blo 1152637 1733195 := bstep (se 1 (by rfl) ⟨1299896, by rfl⟩ : syracuseStep 1733195 = 2599793) B2599793
theorem B1667659 : Blo 1152637 1667659 := bstep (se 1 (by rfl) ⟨1250744, by rfl⟩ : syracuseStep 1667659 = 2501489) B2501489
theorem B1733207 : Blo 1152637 1733207 := bstep (se 1 (by rfl) ⟨1299905, by rfl⟩ : syracuseStep 1733207 = 2599811) B2599811
theorem B13529693 : Blo 1152637 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B94958173 : Blo 1152637 94958173 := bstep (se 3 (by rfl) ⟨17804657, by rfl⟩ : syracuseStep 94958173 = 35609315) B35609315
theorem B1733273 : Blo 1152637 1733273 := bstep (se 2 (by rfl) ⟨649977, by rfl⟩ : syracuseStep 1733273 = 1299955) B1299955
theorem B3699379 : Blo 1152637 3699379 := bstep (se 1 (by rfl) ⟨2774534, by rfl⟩ : syracuseStep 3699379 = 5549069) B5549069
theorem B1733387 : Blo 1152637 1733387 := bstep (se 1 (by rfl) ⟨1300040, by rfl⟩ : syracuseStep 1733387 = 2600081) B2600081
theorem B1733399 : Blo 1152637 1733399 := bstep (se 1 (by rfl) ⟨1300049, by rfl⟩ : syracuseStep 1733399 = 2600099) B2600099
theorem B2192179 : Blo 1152637 2192179 := bstep (se 1 (by rfl) ⟨1644134, by rfl⟩ : syracuseStep 2192179 = 3288269) B3288269
theorem B3896153 : Blo 1152637 3896153 := bstep (se 2 (by rfl) ⟨1461057, by rfl⟩ : syracuseStep 3896153 = 2922115) B2922115
theorem B1733465 : Blo 1152637 1733465 := bstep (se 2 (by rfl) ⟨650049, by rfl⟩ : syracuseStep 1733465 = 1300099) B1300099
theorem B4387715 : Blo 1152637 4387715 := bstep (se 1 (by rfl) ⟨3290786, by rfl⟩ : syracuseStep 4387715 = 6581573) B6581573
theorem B4387729 : Blo 1152637 4387729 := bstep (se 2 (by rfl) ⟨1645398, by rfl⟩ : syracuseStep 4387729 = 3290797) B3290797
theorem B1733579 : Blo 1152637 1733579 := bstep (se 1 (by rfl) ⟨1300184, by rfl⟩ : syracuseStep 1733579 = 2600369) B2600369
theorem B1733591 : Blo 1152637 1733591 := bstep (se 1 (by rfl) ⟨1300193, by rfl⟩ : syracuseStep 1733591 = 2600387) B2600387
theorem B1733657 : Blo 1152637 1733657 := bstep (se 2 (by rfl) ⟨650121, by rfl⟩ : syracuseStep 1733657 = 1300243) B1300243
theorem B1733771 : Blo 1152637 1733771 := bstep (se 1 (by rfl) ⟨1300328, by rfl⟩ : syracuseStep 1733771 = 2600657) B2600657
theorem B1733783 : Blo 1152637 1733783 := bstep (se 1 (by rfl) ⟨1300337, by rfl⟩ : syracuseStep 1733783 = 2600675) B2600675
theorem B4388033 : Blo 1152637 4388033 := bstep (se 2 (by rfl) ⟨1645512, by rfl⟩ : syracuseStep 4388033 = 3291025) B3291025
theorem B1733849 : Blo 1152637 1733849 := bstep (se 2 (by rfl) ⟨650193, by rfl⟩ : syracuseStep 1733849 = 1300387) B1300387
theorem B2192665 : Blo 1152637 2192665 := bstep (se 2 (by rfl) ⟨822249, by rfl⟩ : syracuseStep 2192665 = 1644499) B1644499
theorem B1733963 : Blo 1152637 1733963 := bstep (se 1 (by rfl) ⟨1300472, by rfl⟩ : syracuseStep 1733963 = 2600945) B2600945
theorem B1733975 : Blo 1152637 1733975 := bstep (se 1 (by rfl) ⟨1300481, by rfl⟩ : syracuseStep 1733975 = 2600963) B2600963
theorem B1734041 : Blo 1152637 1734041 := bstep (se 2 (by rfl) ⟨650265, by rfl⟩ : syracuseStep 1734041 = 1300531) B1300531
theorem B1734155 : Blo 1152637 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B3896855 : Blo 1152637 3896855 := bstep (se 1 (by rfl) ⟨2922641, by rfl⟩ : syracuseStep 3896855 = 5845283) B5845283
theorem B1734167 : Blo 1152637 1734167 := bstep (se 1 (by rfl) ⟨1300625, by rfl⟩ : syracuseStep 1734167 = 2601251) B2601251
theorem B1734233 : Blo 1152637 1734233 := bstep (se 2 (by rfl) ⟨650337, by rfl⟩ : syracuseStep 1734233 = 1300675) B1300675
theorem B5273267 : Blo 1152637 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B1734347 : Blo 1152637 1734347 := bstep (se 1 (by rfl) ⟨1300760, by rfl⟩ : syracuseStep 1734347 = 2601521) B2601521
theorem B1734359 : Blo 1152637 1734359 := bstep (se 1 (by rfl) ⟨1300769, by rfl⟩ : syracuseStep 1734359 = 2601539) B2601539
theorem B1734425 : Blo 1152637 1734425 := bstep (se 2 (by rfl) ⟨650409, by rfl⟩ : syracuseStep 1734425 = 1300819) B1300819
theorem B2193227 : Blo 1152637 2193227 := bstep (se 1 (by rfl) ⟨1644920, by rfl⟩ : syracuseStep 2193227 = 3289841) B3289841
theorem B4388701 : Blo 1152637 4388701 := bstep (se 3 (by rfl) ⟨822881, by rfl⟩ : syracuseStep 4388701 = 1645763) B1645763
theorem B1734539 : Blo 1152637 1734539 := bstep (se 1 (by rfl) ⟨1300904, by rfl⟩ : syracuseStep 1734539 = 2601809) B2601809
theorem B1734551 : Blo 1152637 1734551 := bstep (se 1 (by rfl) ⟨1300913, by rfl⟩ : syracuseStep 1734551 = 2601827) B2601827
theorem B1734617 : Blo 1152637 1734617 := bstep (se 2 (by rfl) ⟨650481, by rfl⟩ : syracuseStep 1734617 = 1300963) B1300963
theorem B2193409 : Blo 1152637 2193409 := bstep (se 2 (by rfl) ⟨822528, by rfl⟩ : syracuseStep 2193409 = 1645057) B1645057
theorem B5928977 : Blo 1152637 5928977 := bstep (se 2 (by rfl) ⟨2223366, by rfl⟩ : syracuseStep 5928977 = 4446733) B4446733
theorem B3897395 : Blo 1152637 3897395 := bstep (se 1 (by rfl) ⟨2923046, by rfl⟩ : syracuseStep 3897395 = 5846093) B5846093
theorem B1734731 : Blo 1152637 1734731 := bstep (se 1 (by rfl) ⟨1301048, by rfl⟩ : syracuseStep 1734731 = 2602097) B2602097
theorem B1734743 : Blo 1152637 1734743 := bstep (se 1 (by rfl) ⟨1301057, by rfl⟩ : syracuseStep 1734743 = 2602115) B2602115
theorem B8321125 : Blo 1152637 8321125 := bstep (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) B1560211
theorem B1734809 : Blo 1152637 1734809 := bstep (se 2 (by rfl) ⟨650553, by rfl⟩ : syracuseStep 1734809 = 1301107) B1301107
theorem B1734923 : Blo 1152637 1734923 := bstep (se 1 (by rfl) ⟨1301192, by rfl⟩ : syracuseStep 1734923 = 2602385) B2602385
theorem B1734935 : Blo 1152637 1734935 := bstep (se 1 (by rfl) ⟨1301201, by rfl⟩ : syracuseStep 1734935 = 2602403) B2602403
theorem B19757357 : Blo 1152637 19757357 := bstep (se 3 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 19757357 = 7409009) B7409009
theorem B3897665 : Blo 1152637 3897665 := bstep (se 2 (by rfl) ⟨1461624, by rfl⟩ : syracuseStep 3897665 = 2923249) B2923249
theorem B2194123 : Blo 1152637 2194123 := bstep (se 1 (by rfl) ⟨1645592, by rfl⟩ : syracuseStep 2194123 = 3291185) B3291185
theorem B8780561 : Blo 1152637 8780561 := bstep (se 2 (by rfl) ⟨3292710, by rfl⟩ : syracuseStep 8780561 = 6585421) B6585421
theorem B2194199 : Blo 1152637 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B3898205 : Blo 1152637 3898205 := bstep (se 3 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 3898205 = 1461827) B1461827
theorem B6585239 : Blo 1152637 6585239 := bstep (se 1 (by rfl) ⟨4938929, by rfl⟩ : syracuseStep 6585239 = 9877859) B9877859
theorem B11107363 : Blo 1152637 11107363 := bstep (se 1 (by rfl) ⟨8330522, by rfl⟩ : syracuseStep 11107363 = 16661045) B16661045
theorem B4389977 : Blo 1152637 4389977 := bstep (se 2 (by rfl) ⟨1646241, by rfl⟩ : syracuseStep 4389977 = 3292483) B3292483
theorem B7011659 : Blo 1152637 7011659 := bstep (se 1 (by rfl) ⟨5258744, by rfl⟩ : syracuseStep 7011659 = 10517489) B10517489
theorem B2194867 : Blo 1152637 2194867 := bstep (se 1 (by rfl) ⟨1646150, by rfl⟩ : syracuseStep 2194867 = 3292301) B3292301
theorem B4685273 : Blo 1152637 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B2195095 : Blo 1152637 2195095 := bstep (se 1 (by rfl) ⟨1646321, by rfl⟩ : syracuseStep 2195095 = 3292643) B3292643
theorem B3210931 : Blo 1152637 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B2195201 : Blo 1152637 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B2195353 : Blo 1152637 2195353 := bstep (se 2 (by rfl) ⟨823257, by rfl⟩ : syracuseStep 2195353 = 1646515) B1646515
theorem B3899339 : Blo 1152637 3899339 := bstep (se 1 (by rfl) ⟨2924504, by rfl⟩ : syracuseStep 3899339 = 5849009) B5849009
theorem B6586379 : Blo 1152637 6586379 := bstep (se 1 (by rfl) ⟨4939784, by rfl⟩ : syracuseStep 6586379 = 9879569) B9879569
theorem B2195657 : Blo 1152637 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B3899663 : Blo 1152637 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B19726739 : Blo 1152637 19726739 := bstep (se 1 (by rfl) ⟨14795054, by rfl⟩ : syracuseStep 19726739 = 29590109) B29590109
theorem B4391435 : Blo 1152637 4391435 := bstep (se 1 (by rfl) ⟨3293576, by rfl⟩ : syracuseStep 4391435 = 6587153) B6587153
theorem B3899933 : Blo 1152637 3899933 := bstep (se 3 (by rfl) ⟨731237, by rfl⟩ : syracuseStep 3899933 = 1462475) B1462475
theorem B7012925 : Blo 1152637 7012925 := bstep (se 3 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 7012925 = 2629847) B2629847
theorem B5931809 : Blo 1152637 5931809 := bstep (se 2 (by rfl) ⟨2224428, by rfl⟩ : syracuseStep 5931809 = 4448857) B4448857
theorem B2917691 : Blo 1152637 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B2917903 : Blo 1152637 2917903 := bstep (se 1 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 2917903 = 4376855) B4376855
theorem B36079181 : Blo 1152637 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B7014089 : Blo 1152637 7014089 := bstep (se 2 (by rfl) ⟨2630283, by rfl⟩ : syracuseStep 7014089 = 5260567) B5260567
theorem B2918177 : Blo 1152637 2918177 := bstep (se 2 (by rfl) ⟨1094316, by rfl⟩ : syracuseStep 2918177 = 2188633) B2188633
theorem B22513457 : Blo 1152637 22513457 := bstep (se 2 (by rfl) ⟨8442546, by rfl⟩ : syracuseStep 22513457 = 16885093) B16885093
theorem B13338443 : Blo 1152637 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B3901337 : Blo 1152637 3901337 := bstep (se 2 (by rfl) ⟨1463001, by rfl⟩ : syracuseStep 3901337 = 2926003) B2926003
theorem B4687901 : Blo 1152637 4687901 := bstep (se 3 (by rfl) ⟨878981, by rfl⟩ : syracuseStep 4687901 = 1757963) B1757963
theorem B5933249 : Blo 1152637 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B3705223 : Blo 1152637 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B1444267 : Blo 1152637 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B11078147 : Blo 1152637 11078147 := bstep (se 1 (by rfl) ⟨8308610, by rfl⟩ : syracuseStep 11078147 = 16617221) B16617221
theorem B4164139 : Blo 1152637 4164139 := bstep (se 1 (by rfl) ⟨3123104, by rfl⟩ : syracuseStep 4164139 = 6246209) B6246209
theorem B19761731 : Blo 1152637 19761731 := bstep (se 1 (by rfl) ⟨14821298, by rfl⟩ : syracuseStep 19761731 = 29642597) B29642597
theorem B3902039 : Blo 1152637 3902039 := bstep (se 1 (by rfl) ⟨2926529, by rfl⟩ : syracuseStep 3902039 = 5853059) B5853059
theorem B2919179 : Blo 1152637 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B3902525 : Blo 1152637 3902525 := bstep (se 3 (by rfl) ⟨731723, by rfl⟩ : syracuseStep 3902525 = 1463447) B1463447
theorem B2919827 : Blo 1152637 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B27364787 : Blo 1152637 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B1642027 : Blo 1152637 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B2920121 : Blo 1152637 2920121 := bstep (se 2 (by rfl) ⟨1095045, by rfl⟩ : syracuseStep 2920121 = 2190091) B2190091
theorem B113807105 : Blo 1152637 113807105 := bstep (se 2 (by rfl) ⟨42677664, by rfl⟩ : syracuseStep 113807105 = 85355329) B85355329
theorem B13012811 : Blo 1152637 13012811 := bstep (se 1 (by rfl) ⟨9759608, by rfl⟩ : syracuseStep 13012811 = 19519217) B19519217
theorem B5541767 : Blo 1152637 5541767 := bstep (se 1 (by rfl) ⟨4156325, by rfl⟩ : syracuseStep 5541767 = 8312651) B8312651
theorem B9605017 : Blo 1152637 9605017 := bstep (se 2 (by rfl) ⟨3601881, by rfl⟩ : syracuseStep 9605017 = 7203763) B7203763
theorem B5836697 : Blo 1152637 5836697 := bstep (se 2 (by rfl) ⟨2188761, by rfl⟩ : syracuseStep 5836697 = 4377523) B4377523
theorem B34214089 : Blo 1152637 34214089 := bstep (se 2 (by rfl) ⟨12830283, by rfl⟩ : syracuseStep 34214089 = 25660567) B25660567
theorem B2920819 : Blo 1152637 2920819 := bstep (se 1 (by rfl) ⟨2190614, by rfl⟩ : syracuseStep 2920819 = 4381229) B4381229
theorem B14062045 : Blo 1152637 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B2920961 : Blo 1152637 2920961 := bstep (se 2 (by rfl) ⟨1095360, by rfl⟩ : syracuseStep 2920961 = 2190721) B2190721
theorem B13308419 : Blo 1152637 13308419 := bstep (se 1 (by rfl) ⟨9981314, by rfl⟩ : syracuseStep 13308419 = 19962629) B19962629
theorem B2593655 : Blo 1152637 2593655 := bstep (se 1 (by rfl) ⟨1945241, by rfl⟩ : syracuseStep 2593655 = 3890483) B3890483
theorem B2462665 : Blo 1152637 2462665 := bstep (se 2 (by rfl) ⟨923499, by rfl⟩ : syracuseStep 2462665 = 1846999) B1846999
theorem B2921417 : Blo 1152637 2921417 := bstep (se 2 (by rfl) ⟨1095531, by rfl⟩ : syracuseStep 2921417 = 2191063) B2191063
theorem B2593835 : Blo 1152637 2593835 := bstep (se 1 (by rfl) ⟨1945376, by rfl⟩ : syracuseStep 2593835 = 3890753) B3890753
theorem B5543149 : Blo 1152637 5543149 := bstep (se 3 (by rfl) ⟨1039340, by rfl⟩ : syracuseStep 5543149 = 2078681) B2078681
theorem B2921771 : Blo 1152637 2921771 := bstep (se 1 (by rfl) ⟨2191328, by rfl⟩ : syracuseStep 2921771 = 4382657) B4382657
theorem B11113787 : Blo 1152637 11113787 := bstep (se 1 (by rfl) ⟨8335340, by rfl⟩ : syracuseStep 11113787 = 16670681) B16670681
theorem B26645861 : Blo 1152637 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B2594195 : Blo 1152637 2594195 := bstep (se 1 (by rfl) ⟨1945646, by rfl⟩ : syracuseStep 2594195 = 3891293) B3891293
theorem B2594249 : Blo 1152637 2594249 := bstep (se 2 (by rfl) ⟨972843, by rfl⟩ : syracuseStep 2594249 = 1945687) B1945687
theorem B3282551 : Blo 1152637 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B1152647 : Blo 1152637 1152647 := bstep (se 1 (by rfl) ⟨864485, by rfl⟩ : syracuseStep 1152647 = 1728971) B1728971
theorem B1152655 : Blo 1152637 1152655 := bstep (se 1 (by rfl) ⟨864491, by rfl⟩ : syracuseStep 1152655 = 1728983) B1728983
theorem B1152699 : Blo 1152637 1152699 := bstep (se 1 (by rfl) ⟨864524, by rfl⟩ : syracuseStep 1152699 = 1729049) B1729049
theorem B1152775 : Blo 1152637 1152775 := bstep (se 1 (by rfl) ⟨864581, by rfl⟩ : syracuseStep 1152775 = 1729163) B1729163
theorem B1152783 : Blo 1152637 1152783 := bstep (se 1 (by rfl) ⟨864587, by rfl⟩ : syracuseStep 1152783 = 1729175) B1729175
theorem B1152827 : Blo 1152637 1152827 := bstep (se 1 (by rfl) ⟨864620, by rfl⟩ : syracuseStep 1152827 = 1729241) B1729241
theorem B1152903 : Blo 1152637 1152903 := bstep (se 1 (by rfl) ⟨864677, by rfl⟩ : syracuseStep 1152903 = 1729355) B1729355
theorem B1152911 : Blo 1152637 1152911 := bstep (se 1 (by rfl) ⟨864683, by rfl⟩ : syracuseStep 1152911 = 1729367) B1729367
theorem B1152955 : Blo 1152637 1152955 := bstep (se 1 (by rfl) ⟨864716, by rfl⟩ : syracuseStep 1152955 = 1729433) B1729433
theorem B1153031 : Blo 1152637 1153031 := bstep (se 1 (by rfl) ⟨864773, by rfl⟩ : syracuseStep 1153031 = 1729547) B1729547
theorem B1153039 : Blo 1152637 1153039 := bstep (se 1 (by rfl) ⟨864779, by rfl⟩ : syracuseStep 1153039 = 1729559) B1729559
theorem B1153083 : Blo 1152637 1153083 := bstep (se 1 (by rfl) ⟨864812, by rfl⟩ : syracuseStep 1153083 = 1729625) B1729625
theorem B1153159 : Blo 1152637 1153159 := bstep (se 1 (by rfl) ⟨864869, by rfl⟩ : syracuseStep 1153159 = 1729739) B1729739
theorem B2594951 : Blo 1152637 2594951 := bstep (se 1 (by rfl) ⟨1946213, by rfl⟩ : syracuseStep 2594951 = 3892427) B3892427
theorem B1153167 : Blo 1152637 1153167 := bstep (se 1 (by rfl) ⟨864875, by rfl⟩ : syracuseStep 1153167 = 1729751) B1729751
theorem B1644715 : Blo 1152637 1644715 := bstep (se 1 (by rfl) ⟨1233536, by rfl⟩ : syracuseStep 1644715 = 2467073) B2467073
theorem B1153211 : Blo 1152637 1153211 := bstep (se 1 (by rfl) ⟨864908, by rfl⟩ : syracuseStep 1153211 = 1729817) B1729817
theorem B1153287 : Blo 1152637 1153287 := bstep (se 1 (by rfl) ⟨864965, by rfl⟩ : syracuseStep 1153287 = 1729931) B1729931
theorem B2922763 : Blo 1152637 2922763 := bstep (se 1 (by rfl) ⟨2192072, by rfl⟩ : syracuseStep 2922763 = 4384145) B4384145
theorem B1153295 : Blo 1152637 1153295 := bstep (se 1 (by rfl) ⟨864971, by rfl⟩ : syracuseStep 1153295 = 1729943) B1729943
theorem B2464015 : Blo 1152637 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B1153339 : Blo 1152637 1153339 := bstep (se 1 (by rfl) ⟨865004, by rfl⟩ : syracuseStep 1153339 = 1730009) B1730009
theorem B2595131 : Blo 1152637 2595131 := bstep (se 1 (by rfl) ⟨1946348, by rfl⟩ : syracuseStep 2595131 = 3892697) B3892697
theorem B1153415 : Blo 1152637 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B1153423 : Blo 1152637 1153423 := bstep (se 1 (by rfl) ⟨865067, by rfl⟩ : syracuseStep 1153423 = 1730135) B1730135
theorem B1644943 : Blo 1152637 1644943 := bstep (se 1 (by rfl) ⟨1233707, by rfl⟩ : syracuseStep 1644943 = 2467415) B2467415
theorem B2922905 : Blo 1152637 2922905 := bstep (se 2 (by rfl) ⟨1096089, by rfl⟩ : syracuseStep 2922905 = 2192179) B2192179
theorem B5839289 : Blo 1152637 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B2595257 : Blo 1152637 2595257 := bstep (se 2 (by rfl) ⟨973221, by rfl⟩ : syracuseStep 2595257 = 1946443) B1946443
theorem B1153467 : Blo 1152637 1153467 := bstep (se 1 (by rfl) ⟨865100, by rfl⟩ : syracuseStep 1153467 = 1730201) B1730201
theorem B4168145 : Blo 1152637 4168145 := bstep (se 2 (by rfl) ⟨1563054, by rfl⟩ : syracuseStep 4168145 = 3126109) B3126109
theorem B54073817 : Blo 1152637 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1153543 : Blo 1152637 1153543 := bstep (se 1 (by rfl) ⟨865157, by rfl⟩ : syracuseStep 1153543 = 1730315) B1730315
theorem B1153551 : Blo 1152637 1153551 := bstep (se 1 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 1153551 = 1730327) B1730327
theorem B2464271 : Blo 1152637 2464271 := bstep (se 1 (by rfl) ⟨1848203, by rfl⟩ : syracuseStep 2464271 = 3696407) B3696407
theorem B1153595 : Blo 1152637 1153595 := bstep (se 1 (by rfl) ⟨865196, by rfl⟩ : syracuseStep 1153595 = 1730393) B1730393
theorem B2923067 : Blo 1152637 2923067 := bstep (se 1 (by rfl) ⟨2192300, by rfl⟩ : syracuseStep 2923067 = 4384601) B4384601
theorem B1153671 : Blo 1152637 1153671 := bstep (se 1 (by rfl) ⟨865253, by rfl⟩ : syracuseStep 1153671 = 1730507) B1730507
theorem B1153679 : Blo 1152637 1153679 := bstep (se 1 (by rfl) ⟨865259, by rfl⟩ : syracuseStep 1153679 = 1730519) B1730519
theorem B11082419 : Blo 1152637 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B1153723 : Blo 1152637 1153723 := bstep (se 1 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 1153723 = 1730585) B1730585
theorem B1153799 : Blo 1152637 1153799 := bstep (se 1 (by rfl) ⟨865349, by rfl⟩ : syracuseStep 1153799 = 1730699) B1730699
theorem B1645319 : Blo 1152637 1645319 := bstep (se 1 (by rfl) ⟨1233989, by rfl⟩ : syracuseStep 1645319 = 2467979) B2467979
theorem B19700495 : Blo 1152637 19700495 := bstep (se 1 (by rfl) ⟨14775371, by rfl⟩ : syracuseStep 19700495 = 29550743) B29550743
theorem B2595599 : Blo 1152637 2595599 := bstep (se 1 (by rfl) ⟨1946699, by rfl⟩ : syracuseStep 2595599 = 3893399) B3893399
theorem B1153807 : Blo 1152637 1153807 := bstep (se 1 (by rfl) ⟨865355, by rfl⟩ : syracuseStep 1153807 = 1730711) B1730711
theorem B2595617 : Blo 1152637 2595617 := bstep (se 2 (by rfl) ⟨973356, by rfl⟩ : syracuseStep 2595617 = 1946713) B1946713
theorem B1153851 : Blo 1152637 1153851 := bstep (se 1 (by rfl) ⟨865388, by rfl⟩ : syracuseStep 1153851 = 1730777) B1730777
theorem B1153927 : Blo 1152637 1153927 := bstep (se 1 (by rfl) ⟨865445, by rfl⟩ : syracuseStep 1153927 = 1730891) B1730891
theorem B1153935 : Blo 1152637 1153935 := bstep (se 1 (by rfl) ⟨865451, by rfl⟩ : syracuseStep 1153935 = 1730903) B1730903
theorem B2923411 : Blo 1152637 2923411 := bstep (se 1 (by rfl) ⟨2192558, by rfl⟩ : syracuseStep 2923411 = 4385117) B4385117
theorem B1153979 : Blo 1152637 1153979 := bstep (se 1 (by rfl) ⟨865484, by rfl⟩ : syracuseStep 1153979 = 1730969) B1730969
theorem B1154055 : Blo 1152637 1154055 := bstep (se 1 (by rfl) ⟨865541, by rfl⟩ : syracuseStep 1154055 = 1731083) B1731083
theorem B1154063 : Blo 1152637 1154063 := bstep (se 1 (by rfl) ⟨865547, by rfl⟩ : syracuseStep 1154063 = 1731095) B1731095
theorem B2923553 : Blo 1152637 2923553 := bstep (se 2 (by rfl) ⟨1096332, by rfl⟩ : syracuseStep 2923553 = 2192665) B2192665
theorem B1154107 : Blo 1152637 1154107 := bstep (se 1 (by rfl) ⟨865580, by rfl⟩ : syracuseStep 1154107 = 1731161) B1731161
theorem B2595959 : Blo 1152637 2595959 := bstep (se 1 (by rfl) ⟨1946969, by rfl⟩ : syracuseStep 2595959 = 3893939) B3893939
theorem B1154183 : Blo 1152637 1154183 := bstep (se 1 (by rfl) ⟨865637, by rfl⟩ : syracuseStep 1154183 = 1731275) B1731275
theorem B1154191 : Blo 1152637 1154191 := bstep (se 1 (by rfl) ⟨865643, by rfl⟩ : syracuseStep 1154191 = 1731287) B1731287
theorem B1154235 : Blo 1152637 1154235 := bstep (se 1 (by rfl) ⟨865676, by rfl⟩ : syracuseStep 1154235 = 1731353) B1731353
theorem B6233345 : Blo 1152637 6233345 := bstep (se 2 (by rfl) ⟨2337504, by rfl⟩ : syracuseStep 6233345 = 4675009) B4675009
theorem B1154311 : Blo 1152637 1154311 := bstep (se 1 (by rfl) ⟨865733, by rfl⟩ : syracuseStep 1154311 = 1731467) B1731467
theorem B1154319 : Blo 1152637 1154319 := bstep (se 1 (by rfl) ⟨865739, by rfl⟩ : syracuseStep 1154319 = 1731479) B1731479
theorem B2596139 : Blo 1152637 2596139 := bstep (se 1 (by rfl) ⟨1947104, by rfl⟩ : syracuseStep 2596139 = 3894209) B3894209
theorem B2465083 : Blo 1152637 2465083 := bstep (se 1 (by rfl) ⟨1848812, by rfl⟩ : syracuseStep 2465083 = 3697625) B3697625
theorem B1154363 : Blo 1152637 1154363 := bstep (se 1 (by rfl) ⟨865772, by rfl⟩ : syracuseStep 1154363 = 1731545) B1731545
theorem B2465159 : Blo 1152637 2465159 := bstep (se 1 (by rfl) ⟨1848869, by rfl⟩ : syracuseStep 2465159 = 3697739) B3697739
theorem B1154439 : Blo 1152637 1154439 := bstep (se 1 (by rfl) ⟨865829, by rfl⟩ : syracuseStep 1154439 = 1731659) B1731659
theorem B1154447 : Blo 1152637 1154447 := bstep (se 1 (by rfl) ⟨865835, by rfl⟩ : syracuseStep 1154447 = 1731671) B1731671
theorem B1154491 : Blo 1152637 1154491 := bstep (se 1 (by rfl) ⟨865868, by rfl⟩ : syracuseStep 1154491 = 1731737) B1731737
theorem B1154567 : Blo 1152637 1154567 := bstep (se 1 (by rfl) ⟨865925, by rfl⟩ : syracuseStep 1154567 = 1731851) B1731851
theorem B1154575 : Blo 1152637 1154575 := bstep (se 1 (by rfl) ⟨865931, by rfl⟩ : syracuseStep 1154575 = 1731863) B1731863
theorem B1154619 : Blo 1152637 1154619 := bstep (se 1 (by rfl) ⟨865964, by rfl⟩ : syracuseStep 1154619 = 1731929) B1731929
theorem B2465399 : Blo 1152637 2465399 := bstep (se 1 (by rfl) ⟨1849049, by rfl⟩ : syracuseStep 2465399 = 3698099) B3698099
theorem B1154695 : Blo 1152637 1154695 := bstep (se 1 (by rfl) ⟨866021, by rfl⟩ : syracuseStep 1154695 = 1732043) B1732043
theorem B1154703 : Blo 1152637 1154703 := bstep (se 1 (by rfl) ⟨866027, by rfl⟩ : syracuseStep 1154703 = 1732055) B1732055
theorem B2596499 : Blo 1152637 2596499 := bstep (se 1 (by rfl) ⟨1947374, by rfl⟩ : syracuseStep 2596499 = 3894749) B3894749
theorem B1154747 : Blo 1152637 1154747 := bstep (se 1 (by rfl) ⟨866060, by rfl⟩ : syracuseStep 1154747 = 1732121) B1732121
theorem B5840585 : Blo 1152637 5840585 := bstep (se 2 (by rfl) ⟨2190219, by rfl⟩ : syracuseStep 5840585 = 4380439) B4380439
theorem B2596553 : Blo 1152637 2596553 := bstep (se 2 (by rfl) ⟨973707, by rfl⟩ : syracuseStep 2596553 = 1947415) B1947415
theorem B1154823 : Blo 1152637 1154823 := bstep (se 1 (by rfl) ⟨866117, by rfl⟩ : syracuseStep 1154823 = 1732235) B1732235
theorem B1154831 : Blo 1152637 1154831 := bstep (se 1 (by rfl) ⟨866123, by rfl⟩ : syracuseStep 1154831 = 1732247) B1732247
theorem B2465569 : Blo 1152637 2465569 := bstep (se 2 (by rfl) ⟨924588, by rfl⟩ : syracuseStep 2465569 = 1849177) B1849177
theorem B1154875 : Blo 1152637 1154875 := bstep (se 1 (by rfl) ⟨866156, by rfl⟩ : syracuseStep 1154875 = 1732313) B1732313
theorem B1154951 : Blo 1152637 1154951 := bstep (se 1 (by rfl) ⟨866213, by rfl⟩ : syracuseStep 1154951 = 1732427) B1732427
theorem B1154959 : Blo 1152637 1154959 := bstep (se 1 (by rfl) ⟨866219, by rfl⟩ : syracuseStep 1154959 = 1732439) B1732439
theorem B1155003 : Blo 1152637 1155003 := bstep (se 1 (by rfl) ⟨866252, by rfl⟩ : syracuseStep 1155003 = 1732505) B1732505
theorem B2924545 : Blo 1152637 2924545 := bstep (se 2 (by rfl) ⟨1096704, by rfl⟩ : syracuseStep 2924545 = 2193409) B2193409
theorem B1155079 : Blo 1152637 1155079 := bstep (se 1 (by rfl) ⟨866309, by rfl⟩ : syracuseStep 1155079 = 1732619) B1732619
theorem B8331275 : Blo 1152637 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B1155087 : Blo 1152637 1155087 := bstep (se 1 (by rfl) ⟨866315, by rfl⟩ : syracuseStep 1155087 = 1732631) B1732631
theorem B1155131 : Blo 1152637 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B11083837 : Blo 1152637 11083837 := bstep (se 3 (by rfl) ⟨2078219, by rfl⟩ : syracuseStep 11083837 = 4156439) B4156439
theorem B2465911 : Blo 1152637 2465911 := bstep (se 1 (by rfl) ⟨1849433, by rfl⟩ : syracuseStep 2465911 = 3698867) B3698867
theorem B1155207 : Blo 1152637 1155207 := bstep (se 1 (by rfl) ⟨866405, by rfl⟩ : syracuseStep 1155207 = 1732811) B1732811
theorem B1155215 : Blo 1152637 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B1646777 : Blo 1152637 1646777 := bstep (se 2 (by rfl) ⟨617541, by rfl⟩ : syracuseStep 1646777 = 1235083) B1235083
theorem B1155259 : Blo 1152637 1155259 := bstep (se 1 (by rfl) ⟨866444, by rfl⟩ : syracuseStep 1155259 = 1732889) B1732889
theorem B3285193 : Blo 1152637 3285193 := bstep (se 2 (by rfl) ⟨1231947, by rfl⟩ : syracuseStep 3285193 = 2463895) B2463895
theorem B1155335 : Blo 1152637 1155335 := bstep (se 1 (by rfl) ⟨866501, by rfl⟩ : syracuseStep 1155335 = 1733003) B1733003
theorem B1155343 : Blo 1152637 1155343 := bstep (se 1 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 1155343 = 1733015) B1733015
theorem B1155387 : Blo 1152637 1155387 := bstep (se 1 (by rfl) ⟨866540, by rfl⟩ : syracuseStep 1155387 = 1733081) B1733081
theorem B2597255 : Blo 1152637 2597255 := bstep (se 1 (by rfl) ⟨1947941, by rfl⟩ : syracuseStep 2597255 = 3895883) B3895883
theorem B1155463 : Blo 1152637 1155463 := bstep (se 1 (by rfl) ⟨866597, by rfl⟩ : syracuseStep 1155463 = 1733195) B1733195
theorem B1155471 : Blo 1152637 1155471 := bstep (se 1 (by rfl) ⟨866603, by rfl⟩ : syracuseStep 1155471 = 1733207) B1733207
theorem B1155515 : Blo 1152637 1155515 := bstep (se 1 (by rfl) ⟨866636, by rfl⟩ : syracuseStep 1155515 = 1733273) B1733273
theorem B1155591 : Blo 1152637 1155591 := bstep (se 1 (by rfl) ⟨866693, by rfl⟩ : syracuseStep 1155591 = 1733387) B1733387
theorem B1155599 : Blo 1152637 1155599 := bstep (se 1 (by rfl) ⟨866699, by rfl⟩ : syracuseStep 1155599 = 1733399) B1733399
theorem B2597435 : Blo 1152637 2597435 := bstep (se 1 (by rfl) ⟨1948076, by rfl⟩ : syracuseStep 2597435 = 3896153) B3896153
theorem B1155643 : Blo 1152637 1155643 := bstep (se 1 (by rfl) ⟨866732, by rfl⟩ : syracuseStep 1155643 = 1733465) B1733465
theorem B2925143 : Blo 1152637 2925143 := bstep (se 1 (by rfl) ⟨2193857, by rfl⟩ : syracuseStep 2925143 = 4387715) B4387715
theorem B1155719 : Blo 1152637 1155719 := bstep (se 1 (by rfl) ⟨866789, by rfl⟩ : syracuseStep 1155719 = 1733579) B1733579
theorem B1155727 : Blo 1152637 1155727 := bstep (se 1 (by rfl) ⟨866795, by rfl⟩ : syracuseStep 1155727 = 1733591) B1733591
theorem B2597561 : Blo 1152637 2597561 := bstep (se 2 (by rfl) ⟨974085, by rfl⟩ : syracuseStep 2597561 = 1948171) B1948171
theorem B1155771 : Blo 1152637 1155771 := bstep (se 1 (by rfl) ⟨866828, by rfl⟩ : syracuseStep 1155771 = 1733657) B1733657
theorem B1155847 : Blo 1152637 1155847 := bstep (se 1 (by rfl) ⟨866885, by rfl⟩ : syracuseStep 1155847 = 1733771) B1733771
theorem B1155855 : Blo 1152637 1155855 := bstep (se 1 (by rfl) ⟨866891, by rfl⟩ : syracuseStep 1155855 = 1733783) B1733783
theorem B2925355 : Blo 1152637 2925355 := bstep (se 1 (by rfl) ⟨2194016, by rfl⟩ : syracuseStep 2925355 = 4388033) B4388033
theorem B1155899 : Blo 1152637 1155899 := bstep (se 1 (by rfl) ⟨866924, by rfl⟩ : syracuseStep 1155899 = 1733849) B1733849
theorem B1155975 : Blo 1152637 1155975 := bstep (se 1 (by rfl) ⟨866981, by rfl⟩ : syracuseStep 1155975 = 1733963) B1733963
theorem B1155983 : Blo 1152637 1155983 := bstep (se 1 (by rfl) ⟨866987, by rfl⟩ : syracuseStep 1155983 = 1733975) B1733975
theorem B2925497 : Blo 1152637 2925497 := bstep (se 2 (by rfl) ⟨1097061, by rfl⟩ : syracuseStep 2925497 = 2194123) B2194123
theorem B1156027 : Blo 1152637 1156027 := bstep (se 1 (by rfl) ⟨867020, by rfl⟩ : syracuseStep 1156027 = 1734041) B1734041
theorem B1156103 : Blo 1152637 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B2597903 : Blo 1152637 2597903 := bstep (se 1 (by rfl) ⟨1948427, by rfl⟩ : syracuseStep 2597903 = 3896855) B3896855
theorem B1156111 : Blo 1152637 1156111 := bstep (se 1 (by rfl) ⟨867083, by rfl⟩ : syracuseStep 1156111 = 1734167) B1734167
theorem B2597921 : Blo 1152637 2597921 := bstep (se 2 (by rfl) ⟨974220, by rfl⟩ : syracuseStep 2597921 = 1948441) B1948441
theorem B1156155 : Blo 1152637 1156155 := bstep (se 1 (by rfl) ⟨867116, by rfl⟩ : syracuseStep 1156155 = 1734233) B1734233
theorem B1156231 : Blo 1152637 1156231 := bstep (se 1 (by rfl) ⟨867173, by rfl⟩ : syracuseStep 1156231 = 1734347) B1734347
theorem B1156239 : Blo 1152637 1156239 := bstep (se 1 (by rfl) ⟨867179, by rfl⟩ : syracuseStep 1156239 = 1734359) B1734359
theorem B1156283 : Blo 1152637 1156283 := bstep (se 1 (by rfl) ⟨867212, by rfl⟩ : syracuseStep 1156283 = 1734425) B1734425
theorem B1156359 : Blo 1152637 1156359 := bstep (se 1 (by rfl) ⟨867269, by rfl⟩ : syracuseStep 1156359 = 1734539) B1734539
theorem B1156367 : Blo 1152637 1156367 := bstep (se 1 (by rfl) ⟨867275, by rfl⟩ : syracuseStep 1156367 = 1734551) B1734551
theorem B1156411 : Blo 1152637 1156411 := bstep (se 1 (by rfl) ⟨867308, by rfl⟩ : syracuseStep 1156411 = 1734617) B1734617
theorem B2598263 : Blo 1152637 2598263 := bstep (se 1 (by rfl) ⟨1948697, by rfl⟩ : syracuseStep 2598263 = 3897395) B3897395
theorem B1156487 : Blo 1152637 1156487 := bstep (se 1 (by rfl) ⟨867365, by rfl⟩ : syracuseStep 1156487 = 1734731) B1734731
theorem B1156495 : Blo 1152637 1156495 := bstep (se 1 (by rfl) ⟨867371, by rfl⟩ : syracuseStep 1156495 = 1734743) B1734743
theorem B8889745 : Blo 1152637 8889745 := bstep (se 2 (by rfl) ⟨3333654, by rfl⟩ : syracuseStep 8889745 = 6667309) B6667309
theorem B1156539 : Blo 1152637 1156539 := bstep (se 1 (by rfl) ⟨867404, by rfl⟩ : syracuseStep 1156539 = 1734809) B1734809
theorem B1156615 : Blo 1152637 1156615 := bstep (se 1 (by rfl) ⟨867461, by rfl⟩ : syracuseStep 1156615 = 1734923) B1734923
theorem B1156623 : Blo 1152637 1156623 := bstep (se 1 (by rfl) ⟨867467, by rfl⟩ : syracuseStep 1156623 = 1734935) B1734935
theorem B2598443 : Blo 1152637 2598443 := bstep (se 1 (by rfl) ⟨1948832, by rfl⟩ : syracuseStep 2598443 = 3897665) B3897665
theorem B2598803 : Blo 1152637 2598803 := bstep (se 1 (by rfl) ⟨1949102, by rfl⟩ : syracuseStep 2598803 = 3898205) B3898205
theorem B2926489 : Blo 1152637 2926489 := bstep (se 2 (by rfl) ⟨1097433, by rfl⟩ : syracuseStep 2926489 = 2194867) B2194867
theorem B2598857 : Blo 1152637 2598857 := bstep (se 2 (by rfl) ⟨974571, by rfl⟩ : syracuseStep 2598857 = 1949143) B1949143
theorem B11085835 : Blo 1152637 11085835 := bstep (se 1 (by rfl) ⟨8314376, by rfl⟩ : syracuseStep 11085835 = 16628753) B16628753
theorem B3287051 : Blo 1152637 3287051 := bstep (se 1 (by rfl) ⟨2465288, by rfl⟩ : syracuseStep 3287051 = 4930577) B4930577
theorem B2926651 : Blo 1152637 2926651 := bstep (se 1 (by rfl) ⟨2194988, by rfl⟩ : syracuseStep 2926651 = 4389977) B4389977
theorem B2926793 : Blo 1152637 2926793 := bstep (se 2 (by rfl) ⟨1097547, by rfl⟩ : syracuseStep 2926793 = 2195095) B2195095
theorem B3123515 : Blo 1152637 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B4925843 : Blo 1152637 4925843 := bstep (se 1 (by rfl) ⟨3694382, by rfl⟩ : syracuseStep 4925843 = 7388765) B7388765
theorem B2927137 : Blo 1152637 2927137 := bstep (se 2 (by rfl) ⟨1097676, by rfl⟩ : syracuseStep 2927137 = 2195353) B2195353
theorem B2599559 : Blo 1152637 2599559 := bstep (se 1 (by rfl) ⟨1949669, by rfl⟩ : syracuseStep 2599559 = 3899339) B3899339
theorem B3287699 : Blo 1152637 3287699 := bstep (se 1 (by rfl) ⟨2465774, by rfl⟩ : syracuseStep 3287699 = 4931549) B4931549
theorem B25340633 : Blo 1152637 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B2337569 : Blo 1152637 2337569 := bstep (se 2 (by rfl) ⟨876588, by rfl⟩ : syracuseStep 2337569 = 1753177) B1753177
theorem B2599739 : Blo 1152637 2599739 := bstep (se 1 (by rfl) ⟨1949804, by rfl⟩ : syracuseStep 2599739 = 3899609) B3899609
theorem B5548915 : Blo 1152637 5548915 := bstep (se 1 (by rfl) ⟨4161686, by rfl⟩ : syracuseStep 5548915 = 8323373) B8323373
theorem B3287927 : Blo 1152637 3287927 := bstep (se 1 (by rfl) ⟨2465945, by rfl⟩ : syracuseStep 3287927 = 4931891) B4931891
theorem B2632583 : Blo 1152637 2632583 := bstep (se 1 (by rfl) ⟨1974437, by rfl⟩ : syracuseStep 2632583 = 3948875) B3948875
theorem B2599865 : Blo 1152637 2599865 := bstep (se 2 (by rfl) ⟨974949, by rfl⟩ : syracuseStep 2599865 = 1949899) B1949899
theorem B3746827 : Blo 1152637 3746827 := bstep (se 1 (by rfl) ⟨2810120, by rfl⟩ : syracuseStep 3746827 = 5620241) B5620241
theorem B2927735 : Blo 1152637 2927735 := bstep (se 1 (by rfl) ⟨2195801, by rfl⟩ : syracuseStep 2927735 = 4391603) B4391603
theorem B2600207 : Blo 1152637 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B2600225 : Blo 1152637 2600225 := bstep (se 2 (by rfl) ⟨975084, by rfl⟩ : syracuseStep 2600225 = 1950169) B1950169
theorem B54013229 : Blo 1152637 54013229 := bstep (se 3 (by rfl) ⟨10127480, by rfl⟩ : syracuseStep 54013229 = 20254961) B20254961
theorem B8760635 : Blo 1152637 8760635 := bstep (se 1 (by rfl) ⟨6570476, by rfl⟩ : syracuseStep 8760635 = 13140953) B13140953
theorem B1945147 : Blo 1152637 1945147 := bstep (se 1 (by rfl) ⟨1458860, by rfl⟩ : syracuseStep 1945147 = 2917721) B2917721
theorem B2600567 : Blo 1152637 2600567 := bstep (se 1 (by rfl) ⟨1950425, by rfl⟩ : syracuseStep 2600567 = 3900851) B3900851
theorem B1945289 : Blo 1152637 1945289 := bstep (se 2 (by rfl) ⟨729483, by rfl⟩ : syracuseStep 1945289 = 1458967) B1458967
theorem B2600747 : Blo 1152637 2600747 := bstep (se 1 (by rfl) ⟨1950560, by rfl⟩ : syracuseStep 2600747 = 3901121) B3901121
theorem B3944251 : Blo 1152637 3944251 := bstep (se 1 (by rfl) ⟨2958188, by rfl⟩ : syracuseStep 3944251 = 5916377) B5916377
theorem B1388459 : Blo 1152637 1388459 := bstep (se 1 (by rfl) ⟨1041344, by rfl⟩ : syracuseStep 1388459 = 2082689) B2082689
theorem B4927517 : Blo 1152637 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B2961451 : Blo 1152637 2961451 := bstep (se 1 (by rfl) ⟨2221088, by rfl⟩ : syracuseStep 2961451 = 4442177) B4442177
theorem B2601107 : Blo 1152637 2601107 := bstep (se 1 (by rfl) ⟨1950830, by rfl⟩ : syracuseStep 2601107 = 3901661) B3901661
theorem B2601161 : Blo 1152637 2601161 := bstep (se 2 (by rfl) ⟨975435, by rfl⟩ : syracuseStep 2601161 = 1950871) B1950871
theorem B2502971 : Blo 1152637 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B1945991 : Blo 1152637 1945991 := bstep (se 1 (by rfl) ⟨1459493, by rfl⟩ : syracuseStep 1945991 = 2918987) B2918987
theorem B4993415 : Blo 1152637 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B6566467 : Blo 1152637 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B4928201 : Blo 1152637 4928201 := bstep (se 2 (by rfl) ⟨1848075, by rfl⟩ : syracuseStep 4928201 = 3696151) B3696151
theorem B2601863 : Blo 1152637 2601863 := bstep (se 1 (by rfl) ⟨1951397, by rfl⟩ : syracuseStep 2601863 = 3902795) B3902795
theorem B5551051 : Blo 1152637 5551051 := bstep (se 1 (by rfl) ⟨4163288, by rfl⟩ : syracuseStep 5551051 = 8326577) B8326577
theorem B1946639 : Blo 1152637 1946639 := bstep (se 1 (by rfl) ⟨1459979, by rfl⟩ : syracuseStep 1946639 = 2919959) B2919959
theorem B2602043 : Blo 1152637 2602043 := bstep (se 1 (by rfl) ⟨1951532, by rfl⟩ : syracuseStep 2602043 = 3903065) B3903065
theorem B2602169 : Blo 1152637 2602169 := bstep (se 2 (by rfl) ⟨975813, by rfl⟩ : syracuseStep 2602169 = 1951627) B1951627
theorem B3945673 : Blo 1152637 3945673 := bstep (se 2 (by rfl) ⟨1479627, by rfl⟩ : syracuseStep 3945673 = 2959255) B2959255
theorem B5846417 : Blo 1152637 5846417 := bstep (se 2 (by rfl) ⟨2192406, by rfl⟩ : syracuseStep 5846417 = 4384813) B4384813
theorem B2635193 : Blo 1152637 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B1947179 : Blo 1152637 1947179 := bstep (se 1 (by rfl) ⟨1460384, by rfl⟩ : syracuseStep 1947179 = 2920769) B2920769
theorem B1849223 : Blo 1152637 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B1947577 : Blo 1152637 1947577 := bstep (se 2 (by rfl) ⟨730341, by rfl⟩ : syracuseStep 1947577 = 1460683) B1460683
theorem B3291151 : Blo 1152637 3291151 := bstep (se 1 (by rfl) ⟨2468363, by rfl⟩ : syracuseStep 3291151 = 4936727) B4936727
theorem B3291425 : Blo 1152637 3291425 := bstep (se 2 (by rfl) ⟨1234284, by rfl⟩ : syracuseStep 3291425 = 2468569) B2468569
theorem B4929977 : Blo 1152637 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B6568451 : Blo 1152637 6568451 := bstep (se 1 (by rfl) ⟨4926338, by rfl⟩ : syracuseStep 6568451 = 9852677) B9852677
theorem B22166135 : Blo 1152637 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B1948279 : Blo 1152637 1948279 := bstep (se 1 (by rfl) ⟨1461209, by rfl⟩ : syracuseStep 1948279 = 2922419) B2922419
theorem B5552759 : Blo 1152637 5552759 := bstep (se 1 (by rfl) ⟨4164569, by rfl⟩ : syracuseStep 5552759 = 8329139) B8329139
theorem B2636489 : Blo 1152637 2636489 := bstep (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) B1977367
theorem B1948475 : Blo 1152637 1948475 := bstep (se 1 (by rfl) ⟨1461356, by rfl⟩ : syracuseStep 1948475 = 2922713) B2922713
theorem B3947399 : Blo 1152637 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B1948873 : Blo 1152637 1948873 := bstep (se 2 (by rfl) ⟨730827, by rfl⟩ : syracuseStep 1948873 = 1461655) B1461655
theorem B3292427 : Blo 1152637 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B7028005 : Blo 1152637 7028005 := bstep (se 4 (by rfl) ⟨658875, by rfl⟩ : syracuseStep 7028005 = 1317751) B1317751
theorem B19709243 : Blo 1152637 19709243 := bstep (se 1 (by rfl) ⟨14781932, by rfl⟩ : syracuseStep 19709243 = 29563865) B29563865
theorem B5848523 : Blo 1152637 5848523 := bstep (se 1 (by rfl) ⟨4386392, by rfl⟩ : syracuseStep 5848523 = 8772785) B8772785
theorem B9616849 : Blo 1152637 9616849 := bstep (se 2 (by rfl) ⟨3606318, by rfl⟩ : syracuseStep 9616849 = 7212637) B7212637
theorem B16661969 : Blo 1152637 16661969 := bstep (se 2 (by rfl) ⟨6248238, by rfl⟩ : syracuseStep 16661969 = 12496477) B12496477
theorem B3161659 : Blo 1152637 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B3292825 : Blo 1152637 3292825 := bstep (se 2 (by rfl) ⟨1234809, by rfl⟩ : syracuseStep 3292825 = 2469619) B2469619
theorem B5848847 : Blo 1152637 5848847 := bstep (se 1 (by rfl) ⟨4386635, by rfl⟩ : syracuseStep 5848847 = 8773271) B8773271
theorem B1949575 : Blo 1152637 1949575 := bstep (se 1 (by rfl) ⟨1462181, by rfl⟩ : syracuseStep 1949575 = 2924363) B2924363
theorem B3293075 : Blo 1152637 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B5554433 : Blo 1152637 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1950223 : Blo 1152637 1950223 := bstep (se 1 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 1950223 = 2925335) B2925335
theorem B8765981 : Blo 1152637 8765981 := bstep (se 3 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 8765981 = 3287243) B3287243
theorem B4932353 : Blo 1152637 4932353 := bstep (se 2 (by rfl) ⟨1849632, by rfl⟩ : syracuseStep 4932353 = 3699265) B3699265
theorem B6570841 : Blo 1152637 6570841 := bstep (se 2 (by rfl) ⟨2464065, by rfl⟩ : syracuseStep 6570841 = 4928131) B4928131
theorem B1459063 : Blo 1152637 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B4932505 : Blo 1152637 4932505 := bstep (se 2 (by rfl) ⟨1849689, by rfl⟩ : syracuseStep 4932505 = 3699379) B3699379
theorem B1950763 : Blo 1152637 1950763 := bstep (se 1 (by rfl) ⟨1463072, by rfl⟩ : syracuseStep 1950763 = 2926145) B2926145
theorem B1950905 : Blo 1152637 1950905 := bstep (se 2 (by rfl) ⟨731589, by rfl⟩ : syracuseStep 1950905 = 1463179) B1463179
theorem B1459387 : Blo 1152637 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B5850305 : Blo 1152637 5850305 := bstep (se 2 (by rfl) ⟨2193864, by rfl⟩ : syracuseStep 5850305 = 4387729) B4387729
theorem B2344225 : Blo 1152637 2344225 := bstep (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) B1758169
theorem B3327293 : Blo 1152637 3327293 := bstep (se 3 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 3327293 = 1247735) B1247735
theorem B7390763 : Blo 1152637 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B1558135 : Blo 1152637 1558135 := bstep (se 1 (by rfl) ⟨1168601, by rfl⟩ : syracuseStep 1558135 = 2337203) B2337203
theorem B1459883 : Blo 1152637 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B2770633 : Blo 1152637 2770633 := bstep (se 2 (by rfl) ⟨1038987, by rfl⟩ : syracuseStep 2770633 = 2077975) B2077975
theorem B1951607 : Blo 1152637 1951607 := bstep (se 1 (by rfl) ⟨1463705, by rfl⟩ : syracuseStep 1951607 = 2927411) B2927411
theorem B14796695 : Blo 1152637 14796695 := bstep (se 1 (by rfl) ⟨11097521, by rfl⟩ : syracuseStep 14796695 = 22195043) B22195043
theorem B1460359 : Blo 1152637 1460359 := bstep (se 1 (by rfl) ⟨1095269, by rfl⟩ : syracuseStep 1460359 = 2190539) B2190539
theorem B1231247 : Blo 1152637 1231247 := bstep (se 1 (by rfl) ⟨923435, by rfl⟩ : syracuseStep 1231247 = 1846871) B1846871
theorem B5851601 : Blo 1152637 5851601 := bstep (se 2 (by rfl) ⟨2194350, by rfl⟩ : syracuseStep 5851601 = 4388701) B4388701
theorem B6572573 : Blo 1152637 6572573 := bstep (se 3 (by rfl) ⟨1232357, by rfl⟩ : syracuseStep 6572573 = 2464715) B2464715
theorem B1460855 : Blo 1152637 1460855 := bstep (se 1 (by rfl) ⟨1095641, by rfl⟩ : syracuseStep 1460855 = 2191283) B2191283
theorem B1297039 : Blo 1152637 1297039 := bstep (se 1 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 1297039 = 1945559) B1945559
theorem B1461007 : Blo 1152637 1461007 := bstep (se 1 (by rfl) ⟨1095755, by rfl⟩ : syracuseStep 1461007 = 2191511) B2191511
theorem B11094833 : Blo 1152637 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B1461179 : Blo 1152637 1461179 := bstep (se 1 (by rfl) ⟨1095884, by rfl⟩ : syracuseStep 1461179 = 2191769) B2191769
theorem B1297543 : Blo 1152637 1297543 := bstep (se 1 (by rfl) ⟨973157, by rfl⟩ : syracuseStep 1297543 = 1946315) B1946315
theorem B6573257 : Blo 1152637 6573257 := bstep (se 2 (by rfl) ⟨2464971, by rfl⟩ : syracuseStep 6573257 = 4929943) B4929943
theorem B1297723 : Blo 1152637 1297723 := bstep (se 1 (by rfl) ⟨973292, by rfl⟩ : syracuseStep 1297723 = 1946585) B1946585
theorem B4378009 : Blo 1152637 4378009 := bstep (se 2 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 4378009 = 3283507) B3283507
theorem B1232443 : Blo 1152637 1232443 := bstep (se 1 (by rfl) ⟨924332, by rfl⟩ : syracuseStep 1232443 = 1848665) B1848665
theorem B4378313 : Blo 1152637 4378313 := bstep (se 2 (by rfl) ⟨1641867, by rfl⟩ : syracuseStep 4378313 = 3283735) B3283735
theorem B1298191 : Blo 1152637 1298191 := bstep (se 1 (by rfl) ⟨973643, by rfl⟩ : syracuseStep 1298191 = 1947287) B1947287
theorem B1462151 : Blo 1152637 1462151 := bstep (se 1 (by rfl) ⟨1096613, by rfl⟩ : syracuseStep 1462151 = 2193227) B2193227
theorem B1757099 : Blo 1152637 1757099 := bstep (se 1 (by rfl) ⟨1317824, by rfl⟩ : syracuseStep 1757099 = 2635649) B2635649
theorem B3952651 : Blo 1152637 3952651 := bstep (se 1 (by rfl) ⟨2964488, by rfl⟩ : syracuseStep 3952651 = 5928977) B5928977
theorem B9359383 : Blo 1152637 9359383 := bstep (se 1 (by rfl) ⟨7019537, by rfl⟩ : syracuseStep 9359383 = 14039075) B14039075
theorem B1298695 : Blo 1152637 1298695 := bstep (se 1 (by rfl) ⟨974021, by rfl⟩ : syracuseStep 1298695 = 1948043) B1948043
theorem B1757513 : Blo 1152637 1757513 := bstep (se 2 (by rfl) ⟨659067, by rfl⟩ : syracuseStep 1757513 = 1318135) B1318135
theorem B1298875 : Blo 1152637 1298875 := bstep (se 1 (by rfl) ⟨974156, by rfl⟩ : syracuseStep 1298875 = 1948313) B1948313
theorem B4444625 : Blo 1152637 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B27054557 : Blo 1152637 27054557 := bstep (se 3 (by rfl) ⟨5072729, by rfl⟩ : syracuseStep 27054557 = 10145459) B10145459
theorem B5853707 : Blo 1152637 5853707 := bstep (se 1 (by rfl) ⟨4390280, by rfl⟩ : syracuseStep 5853707 = 8780561) B8780561
theorem B1462799 : Blo 1152637 1462799 := bstep (se 1 (by rfl) ⟨1097099, by rfl⟩ : syracuseStep 1462799 = 2194199) B2194199
theorem B159896081 : Blo 1152637 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B4379255 : Blo 1152637 4379255 := bstep (se 1 (by rfl) ⟨3284441, by rfl⟩ : syracuseStep 4379255 = 6568883) B6568883
theorem B1561207 : Blo 1152637 1561207 := bstep (se 1 (by rfl) ⟨1170905, by rfl⟩ : syracuseStep 1561207 = 2341811) B2341811
theorem B5853869 : Blo 1152637 5853869 := bstep (se 3 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 5853869 = 2195201) B2195201
theorem B3560221 : Blo 1152637 3560221 := bstep (se 3 (by rfl) ⟨667541, by rfl⟩ : syracuseStep 3560221 = 1335083) B1335083
theorem B8770355 : Blo 1152637 8770355 := bstep (se 1 (by rfl) ⟨6577766, by rfl⟩ : syracuseStep 8770355 = 13155533) B13155533
theorem B4674439 : Blo 1152637 4674439 := bstep (se 1 (by rfl) ⟨3505829, by rfl⟩ : syracuseStep 4674439 = 7011659) B7011659
theorem B1299343 : Blo 1152637 1299343 := bstep (se 1 (by rfl) ⟨974507, by rfl⟩ : syracuseStep 1299343 = 1949015) B1949015
theorem B4281241 : Blo 1152637 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B6575033 : Blo 1152637 6575033 := bstep (se 2 (by rfl) ⟨2465637, by rfl⟩ : syracuseStep 6575033 = 4931275) B4931275
theorem B22205501 : Blo 1152637 22205501 := bstep (se 3 (by rfl) ⟨4163531, by rfl⟩ : syracuseStep 22205501 = 8327063) B8327063
theorem B5625089 : Blo 1152637 5625089 := bstep (se 2 (by rfl) ⟨2109408, by rfl⟩ : syracuseStep 5625089 = 4218817) B4218817
theorem B1299847 : Blo 1152637 1299847 := bstep (se 1 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 1299847 = 1949771) B1949771
theorem B50615837 : Blo 1152637 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B1300027 : Blo 1152637 1300027 := bstep (se 1 (by rfl) ⟨975020, by rfl⟩ : syracuseStep 1300027 = 1950041) B1950041
theorem B4380227 : Blo 1152637 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B11392579 : Blo 1152637 11392579 := bstep (se 1 (by rfl) ⟨8544434, by rfl⟩ : syracuseStep 11392579 = 17088869) B17088869
theorem B2774681 : Blo 1152637 2774681 := bstep (se 2 (by rfl) ⟨1040505, by rfl⟩ : syracuseStep 2774681 = 2081011) B2081011
theorem B19748609 : Blo 1152637 19748609 := bstep (se 2 (by rfl) ⟨7405728, by rfl⟩ : syracuseStep 19748609 = 14811457) B14811457
theorem B3954433 : Blo 1152637 3954433 := bstep (se 2 (by rfl) ⟨1482912, by rfl⟩ : syracuseStep 3954433 = 2965825) B2965825
theorem B2774843 : Blo 1152637 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B1300495 : Blo 1152637 1300495 := bstep (se 1 (by rfl) ⟨975371, by rfl⟩ : syracuseStep 1300495 = 1950743) B1950743
theorem B2775073 : Blo 1152637 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B12474769 : Blo 1152637 12474769 := bstep (se 2 (by rfl) ⟨4678038, by rfl⟩ : syracuseStep 12474769 = 9356077) B9356077
theorem B3692947 : Blo 1152637 3692947 := bstep (se 1 (by rfl) ⟨2769710, by rfl⟩ : syracuseStep 3692947 = 5539421) B5539421
theorem B1300999 : Blo 1152637 1300999 := bstep (se 1 (by rfl) ⟨975749, by rfl⟩ : syracuseStep 1300999 = 1951499) B1951499
theorem B2775611 : Blo 1152637 2775611 := bstep (se 1 (by rfl) ⟨2081708, by rfl⟩ : syracuseStep 2775611 = 4163417) B4163417
theorem B1301179 : Blo 1152637 1301179 := bstep (se 1 (by rfl) ⟨975884, by rfl⟩ : syracuseStep 1301179 = 1951769) B1951769
theorem B9624257 : Blo 1152637 9624257 := bstep (se 2 (by rfl) ⟨3609096, by rfl⟩ : syracuseStep 9624257 = 7218193) B7218193
theorem B7396069 : Blo 1152637 7396069 := bstep (se 4 (by rfl) ⟨693381, by rfl⟩ : syracuseStep 7396069 = 1386763) B1386763
theorem B6576947 : Blo 1152637 6576947 := bstep (se 1 (by rfl) ⟨4932710, by rfl⟩ : syracuseStep 6576947 = 9865421) B9865421
theorem B4381897 : Blo 1152637 4381897 := bstep (se 2 (by rfl) ⟨1643211, by rfl⟩ : syracuseStep 4381897 = 3286423) B3286423
theorem B3890699 : Blo 1152637 3890699 := bstep (se 1 (by rfl) ⟨2918024, by rfl⟩ : syracuseStep 3890699 = 5836049) B5836049
theorem B4939325 : Blo 1152637 4939325 := bstep (se 3 (by rfl) ⟨926123, by rfl⟩ : syracuseStep 4939325 = 1852247) B1852247
theorem B3890807 : Blo 1152637 3890807 := bstep (se 1 (by rfl) ⟨2918105, by rfl⟩ : syracuseStep 3890807 = 5836211) B5836211
theorem B3891401 : Blo 1152637 3891401 := bstep (se 2 (by rfl) ⟨1459275, by rfl⟩ : syracuseStep 3891401 = 2918551) B2918551
theorem B6578405 : Blo 1152637 6578405 := bstep (se 4 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 6578405 = 1233451) B1233451
theorem B1729031 : Blo 1152637 1729031 := bstep (se 1 (by rfl) ⟨1296773, by rfl⟩ : syracuseStep 1729031 = 2593547) B2593547
theorem B1729067 : Blo 1152637 1729067 := bstep (se 1 (by rfl) ⟨1296800, by rfl⟩ : syracuseStep 1729067 = 2593601) B2593601
theorem B3695165 : Blo 1152637 3695165 := bstep (se 3 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 3695165 = 1385687) B1385687
theorem B1729097 : Blo 1152637 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B1729211 : Blo 1152637 1729211 := bstep (se 1 (by rfl) ⟨1296908, by rfl⟩ : syracuseStep 1729211 = 2593817) B2593817
theorem B1729271 : Blo 1152637 1729271 := bstep (se 1 (by rfl) ⟨1296953, by rfl⟩ : syracuseStep 1729271 = 2593907) B2593907
theorem B1729295 : Blo 1152637 1729295 := bstep (se 1 (by rfl) ⟨1296971, by rfl⟩ : syracuseStep 1729295 = 2593943) B2593943
theorem B1729337 : Blo 1152637 1729337 := bstep (se 2 (by rfl) ⟨648501, by rfl⟩ : syracuseStep 1729337 = 1297003) B1297003
theorem B1729415 : Blo 1152637 1729415 := bstep (se 1 (by rfl) ⟨1297061, by rfl⟩ : syracuseStep 1729415 = 2594123) B2594123
theorem B3892103 : Blo 1152637 3892103 := bstep (se 1 (by rfl) ⟨2919077, by rfl⟩ : syracuseStep 3892103 = 5838155) B5838155
theorem B6579089 : Blo 1152637 6579089 := bstep (se 2 (by rfl) ⟨2467158, by rfl⟩ : syracuseStep 6579089 = 4934317) B4934317
theorem B1729451 : Blo 1152637 1729451 := bstep (se 1 (by rfl) ⟨1297088, by rfl⟩ : syracuseStep 1729451 = 2594177) B2594177
theorem B1729481 : Blo 1152637 1729481 := bstep (se 2 (by rfl) ⟨648555, by rfl⟩ : syracuseStep 1729481 = 1297111) B1297111
theorem B1729595 : Blo 1152637 1729595 := bstep (se 1 (by rfl) ⟨1297196, by rfl⟩ : syracuseStep 1729595 = 2594393) B2594393
theorem B1729655 : Blo 1152637 1729655 := bstep (se 1 (by rfl) ⟨1297241, by rfl⟩ : syracuseStep 1729655 = 2594483) B2594483
theorem B1729679 : Blo 1152637 1729679 := bstep (se 1 (by rfl) ⟨1297259, by rfl⟩ : syracuseStep 1729679 = 2594519) B2594519
theorem B1729721 : Blo 1152637 1729721 := bstep (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) B1297291
theorem B3892481 : Blo 1152637 3892481 := bstep (se 2 (by rfl) ⟨1459680, by rfl⟩ : syracuseStep 3892481 = 2919361) B2919361
theorem B1729799 : Blo 1152637 1729799 := bstep (se 1 (by rfl) ⟨1297349, by rfl⟩ : syracuseStep 1729799 = 2594699) B2594699
theorem B1729835 : Blo 1152637 1729835 := bstep (se 1 (by rfl) ⟨1297376, by rfl⟩ : syracuseStep 1729835 = 2594753) B2594753
theorem B1729865 : Blo 1152637 1729865 := bstep (se 2 (by rfl) ⟨648699, by rfl⟩ : syracuseStep 1729865 = 1297399) B1297399
theorem B4384115 : Blo 1152637 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B2778553 : Blo 1152637 2778553 := bstep (se 2 (by rfl) ⟨1041957, by rfl⟩ : syracuseStep 2778553 = 2083915) B2083915
theorem B1729979 : Blo 1152637 1729979 := bstep (se 1 (by rfl) ⟨1297484, by rfl⟩ : syracuseStep 1729979 = 2594969) B2594969
theorem B1730039 : Blo 1152637 1730039 := bstep (se 1 (by rfl) ⟨1297529, by rfl⟩ : syracuseStep 1730039 = 2595059) B2595059
theorem B1730063 : Blo 1152637 1730063 := bstep (se 1 (by rfl) ⟨1297547, by rfl⟩ : syracuseStep 1730063 = 2595095) B2595095
theorem B1730105 : Blo 1152637 1730105 := bstep (se 2 (by rfl) ⟨648789, by rfl⟩ : syracuseStep 1730105 = 1297579) B1297579
theorem B1730183 : Blo 1152637 1730183 := bstep (se 1 (by rfl) ⟨1297637, by rfl⟩ : syracuseStep 1730183 = 2595275) B2595275
theorem B1730219 : Blo 1152637 1730219 := bstep (se 1 (by rfl) ⟨1297664, by rfl⟩ : syracuseStep 1730219 = 2595329) B2595329
theorem B1730249 : Blo 1152637 1730249 := bstep (se 2 (by rfl) ⟨648843, by rfl⟩ : syracuseStep 1730249 = 1297687) B1297687
theorem B1730363 : Blo 1152637 1730363 := bstep (se 1 (by rfl) ⟨1297772, by rfl⟩ : syracuseStep 1730363 = 2595545) B2595545
theorem B1730423 : Blo 1152637 1730423 := bstep (se 1 (by rfl) ⟨1297817, by rfl⟩ : syracuseStep 1730423 = 2595635) B2595635
theorem B1730447 : Blo 1152637 1730447 := bstep (se 1 (by rfl) ⟨1297835, by rfl⟩ : syracuseStep 1730447 = 2595671) B2595671
theorem B6580115 : Blo 1152637 6580115 := bstep (se 1 (by rfl) ⟨4935086, by rfl⟩ : syracuseStep 6580115 = 9870173) B9870173
theorem B1730489 : Blo 1152637 1730489 := bstep (se 2 (by rfl) ⟨648933, by rfl⟩ : syracuseStep 1730489 = 1297867) B1297867
theorem B1730567 : Blo 1152637 1730567 := bstep (se 1 (by rfl) ⟨1297925, by rfl⟩ : syracuseStep 1730567 = 2595851) B2595851
theorem B14051339 : Blo 1152637 14051339 := bstep (se 1 (by rfl) ⟨10538504, by rfl⟩ : syracuseStep 14051339 = 21077009) B21077009
theorem B19752983 : Blo 1152637 19752983 := bstep (se 1 (by rfl) ⟨14814737, by rfl⟩ : syracuseStep 19752983 = 29629475) B29629475
theorem B3893291 : Blo 1152637 3893291 := bstep (se 1 (by rfl) ⟨2919968, by rfl⟩ : syracuseStep 3893291 = 5839937) B5839937
theorem B1730603 : Blo 1152637 1730603 := bstep (se 1 (by rfl) ⟨1297952, by rfl⟩ : syracuseStep 1730603 = 2595905) B2595905
theorem B1730633 : Blo 1152637 1730633 := bstep (se 2 (by rfl) ⟨648987, by rfl⟩ : syracuseStep 1730633 = 1297975) B1297975
theorem B1730747 : Blo 1152637 1730747 := bstep (se 1 (by rfl) ⟨1298060, by rfl⟩ : syracuseStep 1730747 = 2596121) B2596121
theorem B1730807 : Blo 1152637 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B1730831 : Blo 1152637 1730831 := bstep (se 1 (by rfl) ⟨1298123, by rfl⟩ : syracuseStep 1730831 = 2596247) B2596247
theorem B1730873 : Blo 1152637 1730873 := bstep (se 2 (by rfl) ⟨649077, by rfl⟩ : syracuseStep 1730873 = 1298155) B1298155
theorem B1730951 : Blo 1152637 1730951 := bstep (se 1 (by rfl) ⟨1298213, by rfl⟩ : syracuseStep 1730951 = 2596427) B2596427
theorem B1730987 : Blo 1152637 1730987 := bstep (se 1 (by rfl) ⟨1298240, by rfl⟩ : syracuseStep 1730987 = 2596481) B2596481
theorem B1731017 : Blo 1152637 1731017 := bstep (se 2 (by rfl) ⟨649131, by rfl⟩ : syracuseStep 1731017 = 1298263) B1298263
theorem B1731131 : Blo 1152637 1731131 := bstep (se 1 (by rfl) ⟨1298348, by rfl⟩ : syracuseStep 1731131 = 2596697) B2596697
theorem B1731191 : Blo 1152637 1731191 := bstep (se 1 (by rfl) ⟨1298393, by rfl⟩ : syracuseStep 1731191 = 2596787) B2596787
theorem B1731215 : Blo 1152637 1731215 := bstep (se 1 (by rfl) ⟨1298411, by rfl⟩ : syracuseStep 1731215 = 2596823) B2596823
theorem B1731257 : Blo 1152637 1731257 := bstep (se 2 (by rfl) ⟨649221, by rfl⟩ : syracuseStep 1731257 = 1298443) B1298443
theorem B1731335 : Blo 1152637 1731335 := bstep (se 1 (by rfl) ⟨1298501, by rfl⟩ : syracuseStep 1731335 = 2597003) B2597003
theorem B1731371 : Blo 1152637 1731371 := bstep (se 1 (by rfl) ⟨1298528, by rfl⟩ : syracuseStep 1731371 = 2597057) B2597057
theorem B1731401 : Blo 1152637 1731401 := bstep (se 2 (by rfl) ⟨649275, by rfl⟩ : syracuseStep 1731401 = 1298551) B1298551
theorem B1731515 : Blo 1152637 1731515 := bstep (se 1 (by rfl) ⟨1298636, by rfl⟩ : syracuseStep 1731515 = 2597273) B2597273
theorem B1731575 : Blo 1152637 1731575 := bstep (se 1 (by rfl) ⟨1298681, by rfl⟩ : syracuseStep 1731575 = 2597363) B2597363
theorem B1731599 : Blo 1152637 1731599 := bstep (se 1 (by rfl) ⟨1298699, by rfl⟩ : syracuseStep 1731599 = 2597399) B2597399
theorem B1731641 : Blo 1152637 1731641 := bstep (se 2 (by rfl) ⟨649365, by rfl⟩ : syracuseStep 1731641 = 1298731) B1298731
theorem B2190395 : Blo 1152637 2190395 := bstep (se 1 (by rfl) ⟨1642796, by rfl⟩ : syracuseStep 2190395 = 3285593) B3285593
theorem B1731719 : Blo 1152637 1731719 := bstep (se 1 (by rfl) ⟨1298789, by rfl⟩ : syracuseStep 1731719 = 2597579) B2597579
theorem B1731755 : Blo 1152637 1731755 := bstep (se 1 (by rfl) ⟨1298816, by rfl⟩ : syracuseStep 1731755 = 2597633) B2597633
theorem B1731785 : Blo 1152637 1731785 := bstep (se 2 (by rfl) ⟨649419, by rfl⟩ : syracuseStep 1731785 = 1298839) B1298839
theorem B13135121 : Blo 1152637 13135121 := bstep (se 2 (by rfl) ⟨4925670, by rfl⟩ : syracuseStep 13135121 = 9851341) B9851341
theorem B3894587 : Blo 1152637 3894587 := bstep (se 1 (by rfl) ⟨2920940, by rfl⟩ : syracuseStep 3894587 = 5841881) B5841881
theorem B1731899 : Blo 1152637 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B1731959 : Blo 1152637 1731959 := bstep (se 1 (by rfl) ⟨1298969, by rfl⟩ : syracuseStep 1731959 = 2597939) B2597939
theorem B1731983 : Blo 1152637 1731983 := bstep (se 1 (by rfl) ⟨1298987, by rfl⟩ : syracuseStep 1731983 = 2597975) B2597975
theorem B9858449 : Blo 1152637 9858449 := bstep (se 2 (by rfl) ⟨3696918, by rfl⟩ : syracuseStep 9858449 = 7393837) B7393837
theorem B1732025 : Blo 1152637 1732025 := bstep (se 2 (by rfl) ⟨649509, by rfl⟩ : syracuseStep 1732025 = 1299019) B1299019
theorem B2223545 : Blo 1152637 2223545 := bstep (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) B1667659
theorem B4386257 : Blo 1152637 4386257 := bstep (se 2 (by rfl) ⟨1644846, by rfl⟩ : syracuseStep 4386257 = 3289693) B3289693
theorem B126610897 : Blo 1152637 126610897 := bstep (se 2 (by rfl) ⟨47479086, by rfl⟩ : syracuseStep 126610897 = 94958173) B94958173
theorem B1732103 : Blo 1152637 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B2190881 : Blo 1152637 2190881 := bstep (se 2 (by rfl) ⟨821580, by rfl⟩ : syracuseStep 2190881 = 1643161) B1643161
theorem B1732139 : Blo 1152637 1732139 := bstep (se 1 (by rfl) ⟨1299104, by rfl⟩ : syracuseStep 1732139 = 2598209) B2598209
theorem B1732169 : Blo 1152637 1732169 := bstep (se 2 (by rfl) ⟨649563, by rfl⟩ : syracuseStep 1732169 = 1299127) B1299127
theorem B1732283 : Blo 1152637 1732283 := bstep (se 1 (by rfl) ⟨1299212, by rfl⟩ : syracuseStep 1732283 = 2598425) B2598425
theorem B1732343 : Blo 1152637 1732343 := bstep (se 1 (by rfl) ⟨1299257, by rfl⟩ : syracuseStep 1732343 = 2598515) B2598515
theorem B1732367 : Blo 1152637 1732367 := bstep (se 1 (by rfl) ⟨1299275, by rfl⟩ : syracuseStep 1732367 = 2598551) B2598551
theorem B4386575 : Blo 1152637 4386575 := bstep (se 1 (by rfl) ⟨3289931, by rfl⟩ : syracuseStep 4386575 = 6579863) B6579863
theorem B3895073 : Blo 1152637 3895073 := bstep (se 2 (by rfl) ⟨1460652, by rfl⟩ : syracuseStep 3895073 = 2921305) B2921305
theorem B1732409 : Blo 1152637 1732409 := bstep (se 2 (by rfl) ⟨649653, by rfl⟩ : syracuseStep 1732409 = 1299307) B1299307
theorem B1732487 : Blo 1152637 1732487 := bstep (se 1 (by rfl) ⟨1299365, by rfl⟩ : syracuseStep 1732487 = 2598731) B2598731
theorem B1732523 : Blo 1152637 1732523 := bstep (se 1 (by rfl) ⟨1299392, by rfl⟩ : syracuseStep 1732523 = 2598785) B2598785
theorem B1732553 : Blo 1152637 1732553 := bstep (se 2 (by rfl) ⟨649707, by rfl⟩ : syracuseStep 1732553 = 1299415) B1299415
theorem B1732667 : Blo 1152637 1732667 := bstep (se 1 (by rfl) ⟨1299500, by rfl⟩ : syracuseStep 1732667 = 2599001) B2599001
theorem B1732727 : Blo 1152637 1732727 := bstep (se 1 (by rfl) ⟨1299545, by rfl⟩ : syracuseStep 1732727 = 2599091) B2599091
theorem B1732751 : Blo 1152637 1732751 := bstep (se 1 (by rfl) ⟨1299563, by rfl⟩ : syracuseStep 1732751 = 2599127) B2599127
theorem B1732793 : Blo 1152637 1732793 := bstep (se 2 (by rfl) ⟨649797, by rfl⟩ : syracuseStep 1732793 = 1299595) B1299595
theorem B1732871 : Blo 1152637 1732871 := bstep (se 1 (by rfl) ⟨1299653, by rfl⟩ : syracuseStep 1732871 = 2599307) B2599307
theorem B1732907 : Blo 1152637 1732907 := bstep (se 1 (by rfl) ⟨1299680, by rfl⟩ : syracuseStep 1732907 = 2599361) B2599361
theorem B1732937 : Blo 1152637 1732937 := bstep (se 2 (by rfl) ⟨649851, by rfl⟩ : syracuseStep 1732937 = 1299703) B1299703
theorem B3895667 : Blo 1152637 3895667 := bstep (se 1 (by rfl) ⟨2921750, by rfl⟩ : syracuseStep 3895667 = 5843501) B5843501
theorem B6746503 : Blo 1152637 6746503 := bstep (se 1 (by rfl) ⟨5059877, by rfl⟩ : syracuseStep 6746503 = 10119755) B10119755
theorem B8778131 : Blo 1152637 8778131 := bstep (se 1 (by rfl) ⟨6583598, by rfl⟩ : syracuseStep 8778131 = 13167197) B13167197
theorem B1733051 : Blo 1152637 1733051 := bstep (se 1 (by rfl) ⟨1299788, by rfl⟩ : syracuseStep 1733051 = 2599577) B2599577
theorem B1733111 : Blo 1152637 1733111 := bstep (se 1 (by rfl) ⟨1299833, by rfl⟩ : syracuseStep 1733111 = 2599667) B2599667
theorem B13332995 : Blo 1152637 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B1733135 : Blo 1152637 1733135 := bstep (se 1 (by rfl) ⟨1299851, by rfl⟩ : syracuseStep 1733135 = 2599703) B2599703
theorem B1733177 : Blo 1152637 1733177 := bstep (se 2 (by rfl) ⟨649941, by rfl⟩ : syracuseStep 1733177 = 1299883) B1299883
theorem B1733255 : Blo 1152637 1733255 := bstep (se 1 (by rfl) ⟨1299941, by rfl⟩ : syracuseStep 1733255 = 2599883) B2599883
theorem B2224775 : Blo 1152637 2224775 := bstep (se 1 (by rfl) ⟨1668581, by rfl⟩ : syracuseStep 2224775 = 3337163) B3337163
theorem B1733291 : Blo 1152637 1733291 := bstep (se 1 (by rfl) ⟨1299968, by rfl⟩ : syracuseStep 1733291 = 2599937) B2599937
theorem B1733321 : Blo 1152637 1733321 := bstep (se 2 (by rfl) ⟨649995, by rfl⟩ : syracuseStep 1733321 = 1299991) B1299991
theorem B1733435 : Blo 1152637 1733435 := bstep (se 1 (by rfl) ⟨1300076, by rfl⟩ : syracuseStep 1733435 = 2600153) B2600153
theorem B1733495 : Blo 1152637 1733495 := bstep (se 1 (by rfl) ⟨1300121, by rfl⟩ : syracuseStep 1733495 = 2600243) B2600243
theorem B1733519 : Blo 1152637 1733519 := bstep (se 1 (by rfl) ⟨1300139, by rfl⟩ : syracuseStep 1733519 = 2600279) B2600279
theorem B1733561 : Blo 1152637 1733561 := bstep (se 2 (by rfl) ⟨650085, by rfl⟩ : syracuseStep 1733561 = 1300171) B1300171
theorem B1405883 : Blo 1152637 1405883 := bstep (se 1 (by rfl) ⟨1054412, by rfl⟩ : syracuseStep 1405883 = 2108825) B2108825
theorem B1733639 : Blo 1152637 1733639 := bstep (se 1 (by rfl) ⟨1300229, by rfl⟩ : syracuseStep 1733639 = 2600459) B2600459
theorem B1733675 : Blo 1152637 1733675 := bstep (se 1 (by rfl) ⟨1300256, by rfl⟩ : syracuseStep 1733675 = 2600513) B2600513
theorem B1733705 : Blo 1152637 1733705 := bstep (se 2 (by rfl) ⟨650139, by rfl⟩ : syracuseStep 1733705 = 1300279) B1300279
theorem B1733819 : Blo 1152637 1733819 := bstep (se 1 (by rfl) ⟨1300364, by rfl⟩ : syracuseStep 1733819 = 2600729) B2600729
theorem B1733879 : Blo 1152637 1733879 := bstep (se 1 (by rfl) ⟨1300409, by rfl⟩ : syracuseStep 1733879 = 2600819) B2600819
theorem B1733903 : Blo 1152637 1733903 := bstep (se 1 (by rfl) ⟨1300427, by rfl⟩ : syracuseStep 1733903 = 2600855) B2600855
theorem B1733945 : Blo 1152637 1733945 := bstep (se 2 (by rfl) ⟨650229, by rfl⟩ : syracuseStep 1733945 = 1300459) B1300459
theorem B14021947 : Blo 1152637 14021947 := bstep (se 1 (by rfl) ⟨10516460, by rfl⟩ : syracuseStep 14021947 = 21032921) B21032921
theorem B1734023 : Blo 1152637 1734023 := bstep (se 1 (by rfl) ⟨1300517, by rfl⟩ : syracuseStep 1734023 = 2601035) B2601035
theorem B1734059 : Blo 1152637 1734059 := bstep (se 1 (by rfl) ⟨1300544, by rfl⟩ : syracuseStep 1734059 = 2601089) B2601089
theorem B2192825 : Blo 1152637 2192825 := bstep (se 2 (by rfl) ⟨822309, by rfl⟩ : syracuseStep 2192825 = 1644619) B1644619
theorem B1734089 : Blo 1152637 1734089 := bstep (se 2 (by rfl) ⟨650283, by rfl⟩ : syracuseStep 1734089 = 1300567) B1300567
theorem B1734203 : Blo 1152637 1734203 := bstep (se 1 (by rfl) ⟨1300652, by rfl⟩ : syracuseStep 1734203 = 2601305) B2601305
theorem B1734263 : Blo 1152637 1734263 := bstep (se 1 (by rfl) ⟨1300697, by rfl⟩ : syracuseStep 1734263 = 2601395) B2601395
theorem B1734287 : Blo 1152637 1734287 := bstep (se 1 (by rfl) ⟨1300715, by rfl⟩ : syracuseStep 1734287 = 2601431) B2601431
theorem B1734329 : Blo 1152637 1734329 := bstep (se 2 (by rfl) ⟨650373, by rfl⟩ : syracuseStep 1734329 = 1300747) B1300747
theorem B4683521 : Blo 1152637 4683521 := bstep (se 2 (by rfl) ⟨1756320, by rfl⟩ : syracuseStep 4683521 = 3512641) B3512641
theorem B1734407 : Blo 1152637 1734407 := bstep (se 1 (by rfl) ⟨1300805, by rfl⟩ : syracuseStep 1734407 = 2601611) B2601611
theorem B3700495 : Blo 1152637 3700495 := bstep (se 1 (by rfl) ⟨2775371, by rfl⟩ : syracuseStep 3700495 = 5550743) B5550743
theorem B1734443 : Blo 1152637 1734443 := bstep (se 1 (by rfl) ⟨1300832, by rfl⟩ : syracuseStep 1734443 = 2601665) B2601665
theorem B1734473 : Blo 1152637 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B4159367 : Blo 1152637 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B1734587 : Blo 1152637 1734587 := bstep (se 1 (by rfl) ⟨1300940, by rfl⟩ : syracuseStep 1734587 = 2601881) B2601881
theorem B1734647 : Blo 1152637 1734647 := bstep (se 1 (by rfl) ⟨1300985, by rfl⟩ : syracuseStep 1734647 = 2601971) B2601971
theorem B1734671 : Blo 1152637 1734671 := bstep (se 1 (by rfl) ⟨1301003, by rfl⟩ : syracuseStep 1734671 = 2602007) B2602007
theorem B1734713 : Blo 1152637 1734713 := bstep (se 2 (by rfl) ⟨650517, by rfl⟩ : syracuseStep 1734713 = 1301035) B1301035
theorem B13138037 : Blo 1152637 13138037 := bstep (se 5 (by rfl) ⟨615845, by rfl⟩ : syracuseStep 13138037 = 1231691) B1231691
theorem B1734791 : Blo 1152637 1734791 := bstep (se 1 (by rfl) ⟨1301093, by rfl⟩ : syracuseStep 1734791 = 2602187) B2602187
theorem B1734827 : Blo 1152637 1734827 := bstep (se 1 (by rfl) ⟨1301120, by rfl⟩ : syracuseStep 1734827 = 2602241) B2602241
theorem B1734857 : Blo 1152637 1734857 := bstep (se 2 (by rfl) ⟨650571, by rfl⟩ : syracuseStep 1734857 = 1301143) B1301143
theorem B2193979 : Blo 1152637 2193979 := bstep (se 1 (by rfl) ⟨1645484, by rfl⟩ : syracuseStep 2193979 = 3290969) B3290969
theorem B4684349 : Blo 1152637 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B14809817 : Blo 1152637 14809817 := bstep (se 2 (by rfl) ⟨5553681, by rfl⟩ : syracuseStep 14809817 = 11107363) B11107363
theorem B13171571 : Blo 1152637 13171571 := bstep (se 1 (by rfl) ⟨9878678, by rfl⟩ : syracuseStep 13171571 = 19757357) B19757357
theorem B3898259 : Blo 1152637 3898259 := bstep (se 1 (by rfl) ⟨2923694, by rfl⟩ : syracuseStep 3898259 = 5847389) B5847389
theorem B9993239 : Blo 1152637 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B2194465 : Blo 1152637 2194465 := bstep (se 2 (by rfl) ⟨822924, by rfl⟩ : syracuseStep 2194465 = 1645849) B1645849
theorem B4390145 : Blo 1152637 4390145 := bstep (se 2 (by rfl) ⟨1646304, by rfl⟩ : syracuseStep 4390145 = 3292609) B3292609
theorem B4390159 : Blo 1152637 4390159 := bstep (se 1 (by rfl) ⟨3292619, by rfl⟩ : syracuseStep 4390159 = 6585239) B6585239
theorem B4161053 : Blo 1152637 4161053 := bstep (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) B1560395
theorem B5275165 : Blo 1152637 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B3899393 : Blo 1152637 3899393 := bstep (se 2 (by rfl) ⟨1462272, by rfl⟩ : syracuseStep 3899393 = 2924545) B2924545
theorem B4390919 : Blo 1152637 4390919 := bstep (se 1 (by rfl) ⟨3293189, by rfl⟩ : syracuseStep 4390919 = 6586379) B6586379
theorem B14778449 : Blo 1152637 14778449 := bstep (se 2 (by rfl) ⟨5541918, by rfl⟩ : syracuseStep 14778449 = 11083837) B11083837
theorem B4391405 : Blo 1152637 4391405 := bstep (se 3 (by rfl) ⟨823388, by rfl⟩ : syracuseStep 4391405 = 1646777) B1646777
theorem B14811821 : Blo 1152637 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B3900203 : Blo 1152637 3900203 := bstep (se 1 (by rfl) ⟨2925152, by rfl⟩ : syracuseStep 3900203 = 5850305) B5850305
theorem B24052787 : Blo 1152637 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B3900473 : Blo 1152637 3900473 := bstep (se 2 (by rfl) ⟨1462677, by rfl⟩ : syracuseStep 3900473 = 2925355) B2925355
theorem B15008971 : Blo 1152637 15008971 := bstep (se 1 (by rfl) ⟨11256728, by rfl⟩ : syracuseStep 15008971 = 22513457) B22513457
theorem B9864463 : Blo 1152637 9864463 := bstep (se 1 (by rfl) ⟨7398347, by rfl⟩ : syracuseStep 9864463 = 14796695) B14796695
theorem B35489117 : Blo 1152637 35489117 := bstep (se 3 (by rfl) ⟨6654209, by rfl⟩ : syracuseStep 35489117 = 13308419) B13308419
theorem B3900797 : Blo 1152637 3900797 := bstep (se 3 (by rfl) ⟨731399, by rfl⟩ : syracuseStep 3900797 = 1462799) B1462799
theorem B3901067 : Blo 1152637 3901067 := bstep (se 1 (by rfl) ⟨2925800, by rfl⟩ : syracuseStep 3901067 = 5851601) B5851601
theorem B5932733 : Blo 1152637 5932733 := bstep (se 3 (by rfl) ⟨1112387, by rfl⟩ : syracuseStep 5932733 = 2224775) B2224775
theorem B13174487 : Blo 1152637 13174487 := bstep (se 1 (by rfl) ⟨9880865, by rfl⟩ : syracuseStep 13174487 = 19761731) B19761731
theorem B3704737 : Blo 1152637 3704737 := bstep (se 2 (by rfl) ⟨1389276, by rfl⟩ : syracuseStep 3704737 = 2778553) B2778553
theorem B2918875 : Blo 1152637 2918875 := bstep (se 1 (by rfl) ⟨2189156, by rfl⟩ : syracuseStep 2918875 = 4378313) B4378313
theorem B3901985 : Blo 1152637 3901985 := bstep (se 2 (by rfl) ⟨1463244, by rfl⟩ : syracuseStep 3901985 = 2926489) B2926489
theorem B14781113 : Blo 1152637 14781113 := bstep (se 2 (by rfl) ⟨5542917, by rfl⟩ : syracuseStep 14781113 = 11085835) B11085835
theorem B3902201 : Blo 1152637 3902201 := bstep (se 2 (by rfl) ⟨1463325, by rfl⟩ : syracuseStep 3902201 = 2926651) B2926651
theorem B3902471 : Blo 1152637 3902471 := bstep (se 1 (by rfl) ⟨2926853, by rfl⟩ : syracuseStep 3902471 = 5853707) B5853707
theorem B106597387 : Blo 1152637 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B2919503 : Blo 1152637 2919503 := bstep (se 1 (by rfl) ⟨2189627, by rfl⟩ : syracuseStep 2919503 = 4379255) B4379255
theorem B3902579 : Blo 1152637 3902579 := bstep (se 1 (by rfl) ⟨2926934, by rfl⟩ : syracuseStep 3902579 = 5853869) B5853869
theorem B3902849 : Blo 1152637 3902849 := bstep (se 2 (by rfl) ⟨1463568, by rfl⟩ : syracuseStep 3902849 = 2927137) B2927137
theorem B7409191 : Blo 1152637 7409191 := bstep (se 1 (by rfl) ⟨5556893, by rfl⟩ : syracuseStep 7409191 = 11113787) B11113787
theorem B17763907 : Blo 1152637 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B2920151 : Blo 1152637 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B36049211 : Blo 1152637 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1642847 : Blo 1152637 1642847 := bstep (se 1 (by rfl) ⟨1232135, by rfl⟩ : syracuseStep 1642847 = 2464271) B2464271
theorem B5837345 : Blo 1152637 5837345 := bstep (se 2 (by rfl) ⟨2189004, by rfl⟩ : syracuseStep 5837345 = 4378009) B4378009
theorem B12489389 : Blo 1152637 12489389 := bstep (se 3 (by rfl) ⟨2341760, by rfl⟩ : syracuseStep 12489389 = 4683521) B4683521
theorem B2593529 : Blo 1152637 2593529 := bstep (se 2 (by rfl) ⟨972573, by rfl⟩ : syracuseStep 2593529 = 1945147) B1945147
theorem B1643257 : Blo 1152637 1643257 := bstep (se 2 (by rfl) ⟨616221, by rfl⟩ : syracuseStep 1643257 = 1232443) B1232443
theorem B2593799 : Blo 1152637 2593799 := bstep (se 1 (by rfl) ⟨1945349, by rfl⟩ : syracuseStep 2593799 = 3890699) B3890699
theorem B2593871 : Blo 1152637 2593871 := bstep (se 1 (by rfl) ⟨1945403, by rfl⟩ : syracuseStep 2593871 = 3890807) B3890807
theorem B1643599 : Blo 1152637 1643599 := bstep (se 1 (by rfl) ⟨1232699, by rfl⟩ : syracuseStep 1643599 = 2465399) B2465399
theorem B2594267 : Blo 1152637 2594267 := bstep (se 1 (by rfl) ⟨1945700, by rfl⟩ : syracuseStep 2594267 = 3891401) B3891401
theorem B45618785 : Blo 1152637 45618785 := bstep (se 2 (by rfl) ⟨17107044, by rfl⟩ : syracuseStep 45618785 = 34214089) B34214089
theorem B1152687 : Blo 1152637 1152687 := bstep (se 1 (by rfl) ⟨864515, by rfl⟩ : syracuseStep 1152687 = 1729031) B1729031
theorem B1152711 : Blo 1152637 1152711 := bstep (se 1 (by rfl) ⟨864533, by rfl⟩ : syracuseStep 1152711 = 1729067) B1729067
theorem B2463443 : Blo 1152637 2463443 := bstep (se 1 (by rfl) ⟨1847582, by rfl⟩ : syracuseStep 2463443 = 3695165) B3695165
theorem B1152731 : Blo 1152637 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B1152807 : Blo 1152637 1152807 := bstep (se 1 (by rfl) ⟨864605, by rfl⟩ : syracuseStep 1152807 = 1729211) B1729211
theorem B1152847 : Blo 1152637 1152847 := bstep (se 1 (by rfl) ⟨864635, by rfl⟩ : syracuseStep 1152847 = 1729271) B1729271
theorem B1152863 : Blo 1152637 1152863 := bstep (se 1 (by rfl) ⟨864647, by rfl⟩ : syracuseStep 1152863 = 1729295) B1729295
theorem B1152891 : Blo 1152637 1152891 := bstep (se 1 (by rfl) ⟨864668, by rfl⟩ : syracuseStep 1152891 = 1729337) B1729337
theorem B1152943 : Blo 1152637 1152943 := bstep (se 1 (by rfl) ⟨864707, by rfl⟩ : syracuseStep 1152943 = 1729415) B1729415
theorem B2594735 : Blo 1152637 2594735 := bstep (se 1 (by rfl) ⟨1946051, by rfl⟩ : syracuseStep 2594735 = 3892103) B3892103
theorem B1152967 : Blo 1152637 1152967 := bstep (se 1 (by rfl) ⟨864725, by rfl⟩ : syracuseStep 1152967 = 1729451) B1729451
theorem B18749393 : Blo 1152637 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B1152987 : Blo 1152637 1152987 := bstep (se 1 (by rfl) ⟨864740, by rfl⟩ : syracuseStep 1152987 = 1729481) B1729481
theorem B1153063 : Blo 1152637 1153063 := bstep (se 1 (by rfl) ⟨864797, by rfl⟩ : syracuseStep 1153063 = 1729595) B1729595
theorem B1153103 : Blo 1152637 1153103 := bstep (se 1 (by rfl) ⟨864827, by rfl⟩ : syracuseStep 1153103 = 1729655) B1729655
theorem B8755289 : Blo 1152637 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B1153119 : Blo 1152637 1153119 := bstep (se 1 (by rfl) ⟨864839, by rfl⟩ : syracuseStep 1153119 = 1729679) B1729679
theorem B1153147 : Blo 1152637 1153147 := bstep (se 1 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 1153147 = 1729721) B1729721
theorem B2594987 : Blo 1152637 2594987 := bstep (se 1 (by rfl) ⟨1946240, by rfl⟩ : syracuseStep 2594987 = 3892481) B3892481
theorem B1153199 : Blo 1152637 1153199 := bstep (se 1 (by rfl) ⟨864899, by rfl⟩ : syracuseStep 1153199 = 1729799) B1729799
theorem B1153223 : Blo 1152637 1153223 := bstep (se 1 (by rfl) ⟨864917, by rfl⟩ : syracuseStep 1153223 = 1729835) B1729835
theorem B1153243 : Blo 1152637 1153243 := bstep (se 1 (by rfl) ⟨864932, by rfl⟩ : syracuseStep 1153243 = 1729865) B1729865
theorem B2922743 : Blo 1152637 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B1153319 : Blo 1152637 1153319 := bstep (se 1 (by rfl) ⟨864989, by rfl⟩ : syracuseStep 1153319 = 1729979) B1729979
theorem B1153359 : Blo 1152637 1153359 := bstep (se 1 (by rfl) ⟨865019, by rfl⟩ : syracuseStep 1153359 = 1730039) B1730039
theorem B1153375 : Blo 1152637 1153375 := bstep (se 1 (by rfl) ⟨865031, by rfl⟩ : syracuseStep 1153375 = 1730063) B1730063
theorem B1153403 : Blo 1152637 1153403 := bstep (se 1 (by rfl) ⟨865052, by rfl⟩ : syracuseStep 1153403 = 1730105) B1730105
theorem B3283325 : Blo 1152637 3283325 := bstep (se 3 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 3283325 = 1231247) B1231247
theorem B1153455 : Blo 1152637 1153455 := bstep (se 1 (by rfl) ⟨865091, by rfl⟩ : syracuseStep 1153455 = 1730183) B1730183
theorem B1153479 : Blo 1152637 1153479 := bstep (se 1 (by rfl) ⟨865109, by rfl⟩ : syracuseStep 1153479 = 1730219) B1730219
theorem B1153499 : Blo 1152637 1153499 := bstep (se 1 (by rfl) ⟨865124, by rfl⟩ : syracuseStep 1153499 = 1730249) B1730249
theorem B6232585 : Blo 1152637 6232585 := bstep (se 2 (by rfl) ⟨2337219, by rfl⟩ : syracuseStep 6232585 = 4674439) B4674439
theorem B5708321 : Blo 1152637 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B1153575 : Blo 1152637 1153575 := bstep (se 1 (by rfl) ⟨865181, by rfl⟩ : syracuseStep 1153575 = 1730363) B1730363
theorem B11115053 : Blo 1152637 11115053 := bstep (se 3 (by rfl) ⟨2084072, by rfl⟩ : syracuseStep 11115053 = 4168145) B4168145
theorem B1153615 : Blo 1152637 1153615 := bstep (se 1 (by rfl) ⟨865211, by rfl⟩ : syracuseStep 1153615 = 1730423) B1730423
theorem B1153631 : Blo 1152637 1153631 := bstep (se 1 (by rfl) ⟨865223, by rfl⟩ : syracuseStep 1153631 = 1730447) B1730447
theorem B3283553 : Blo 1152637 3283553 := bstep (se 2 (by rfl) ⟨1231332, by rfl⟩ : syracuseStep 3283553 = 2462665) B2462665
theorem B1153659 : Blo 1152637 1153659 := bstep (se 1 (by rfl) ⟨865244, by rfl⟩ : syracuseStep 1153659 = 1730489) B1730489
theorem B1153711 : Blo 1152637 1153711 := bstep (se 1 (by rfl) ⟨865283, by rfl⟩ : syracuseStep 1153711 = 1730567) B1730567
theorem B2595527 : Blo 1152637 2595527 := bstep (se 1 (by rfl) ⟨1946645, by rfl⟩ : syracuseStep 2595527 = 3893291) B3893291
theorem B1153735 : Blo 1152637 1153735 := bstep (se 1 (by rfl) ⟨865301, by rfl⟩ : syracuseStep 1153735 = 1730603) B1730603
theorem B1153755 : Blo 1152637 1153755 := bstep (se 1 (by rfl) ⟨865316, by rfl⟩ : syracuseStep 1153755 = 1730633) B1730633
theorem B1153831 : Blo 1152637 1153831 := bstep (se 1 (by rfl) ⟨865373, by rfl⟩ : syracuseStep 1153831 = 1730747) B1730747
theorem B12491597 : Blo 1152637 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B1153871 : Blo 1152637 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B1153887 : Blo 1152637 1153887 := bstep (se 1 (by rfl) ⟨865415, by rfl⟩ : syracuseStep 1153887 = 1730831) B1730831
theorem B1153915 : Blo 1152637 1153915 := bstep (se 1 (by rfl) ⟨865436, by rfl⟩ : syracuseStep 1153915 = 1730873) B1730873
theorem B1153967 : Blo 1152637 1153967 := bstep (se 1 (by rfl) ⟨865475, by rfl⟩ : syracuseStep 1153967 = 1730951) B1730951
theorem B3283895 : Blo 1152637 3283895 := bstep (se 1 (by rfl) ⟨2462921, by rfl⟩ : syracuseStep 3283895 = 4925843) B4925843
theorem B1153991 : Blo 1152637 1153991 := bstep (se 1 (by rfl) ⟨865493, by rfl⟩ : syracuseStep 1153991 = 1730987) B1730987
theorem B1154011 : Blo 1152637 1154011 := bstep (se 1 (by rfl) ⟨865508, by rfl⟩ : syracuseStep 1154011 = 1731017) B1731017
theorem B1154087 : Blo 1152637 1154087 := bstep (se 1 (by rfl) ⟨865565, by rfl⟩ : syracuseStep 1154087 = 1731131) B1731131
theorem B1154127 : Blo 1152637 1154127 := bstep (se 1 (by rfl) ⟨865595, by rfl⟩ : syracuseStep 1154127 = 1731191) B1731191
theorem B1154143 : Blo 1152637 1154143 := bstep (se 1 (by rfl) ⟨865607, by rfl⟩ : syracuseStep 1154143 = 1731215) B1731215
theorem B1154171 : Blo 1152637 1154171 := bstep (se 1 (by rfl) ⟨865628, by rfl⟩ : syracuseStep 1154171 = 1731257) B1731257
theorem B1154223 : Blo 1152637 1154223 := bstep (se 1 (by rfl) ⟨865667, by rfl⟩ : syracuseStep 1154223 = 1731335) B1731335
theorem B1154247 : Blo 1152637 1154247 := bstep (se 1 (by rfl) ⟨865685, by rfl⟩ : syracuseStep 1154247 = 1731371) B1731371
theorem B1154267 : Blo 1152637 1154267 := bstep (se 1 (by rfl) ⟨865700, by rfl⟩ : syracuseStep 1154267 = 1731401) B1731401
theorem B1154343 : Blo 1152637 1154343 := bstep (se 1 (by rfl) ⟨865757, by rfl⟩ : syracuseStep 1154343 = 1731515) B1731515
theorem B1154383 : Blo 1152637 1154383 := bstep (se 1 (by rfl) ⟨865787, by rfl⟩ : syracuseStep 1154383 = 1731575) B1731575
theorem B1154399 : Blo 1152637 1154399 := bstep (se 1 (by rfl) ⟨865799, by rfl⟩ : syracuseStep 1154399 = 1731599) B1731599
theorem B1154427 : Blo 1152637 1154427 := bstep (se 1 (by rfl) ⟨865820, by rfl⟩ : syracuseStep 1154427 = 1731641) B1731641
theorem B1154479 : Blo 1152637 1154479 := bstep (se 1 (by rfl) ⟨865859, by rfl⟩ : syracuseStep 1154479 = 1731719) B1731719
theorem B1154503 : Blo 1152637 1154503 := bstep (se 1 (by rfl) ⟨865877, by rfl⟩ : syracuseStep 1154503 = 1731755) B1731755
theorem B1154523 : Blo 1152637 1154523 := bstep (se 1 (by rfl) ⟨865892, by rfl⟩ : syracuseStep 1154523 = 1731785) B1731785
theorem B8756747 : Blo 1152637 8756747 := bstep (se 1 (by rfl) ⟨6567560, by rfl⟩ : syracuseStep 8756747 = 13135121) B13135121
theorem B5840423 : Blo 1152637 5840423 := bstep (se 1 (by rfl) ⟨4380317, by rfl⟩ : syracuseStep 5840423 = 8760635) B8760635
theorem B2596391 : Blo 1152637 2596391 := bstep (se 1 (by rfl) ⟨1947293, by rfl⟩ : syracuseStep 2596391 = 3894587) B3894587
theorem B1154599 : Blo 1152637 1154599 := bstep (se 1 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 1154599 = 1731899) B1731899
theorem B1154639 : Blo 1152637 1154639 := bstep (se 1 (by rfl) ⟨865979, by rfl⟩ : syracuseStep 1154639 = 1731959) B1731959
theorem B1154655 : Blo 1152637 1154655 := bstep (se 1 (by rfl) ⟨865991, by rfl⟩ : syracuseStep 1154655 = 1731983) B1731983
theorem B1154683 : Blo 1152637 1154683 := bstep (se 1 (by rfl) ⟨866012, by rfl⟩ : syracuseStep 1154683 = 1732025) B1732025
theorem B2924171 : Blo 1152637 2924171 := bstep (se 1 (by rfl) ⟨2193128, by rfl⟩ : syracuseStep 2924171 = 4386257) B4386257
theorem B1154735 : Blo 1152637 1154735 := bstep (se 1 (by rfl) ⟨866051, by rfl⟩ : syracuseStep 1154735 = 1732103) B1732103
theorem B1154759 : Blo 1152637 1154759 := bstep (se 1 (by rfl) ⟨866069, by rfl⟩ : syracuseStep 1154759 = 1732139) B1732139
theorem B1154779 : Blo 1152637 1154779 := bstep (se 1 (by rfl) ⟨866084, by rfl⟩ : syracuseStep 1154779 = 1732169) B1732169
theorem B51289861 : Blo 1152637 51289861 := bstep (se 4 (by rfl) ⟨4808424, by rfl⟩ : syracuseStep 51289861 = 9616849) B9616849
theorem B1154855 : Blo 1152637 1154855 := bstep (se 1 (by rfl) ⟨866141, by rfl⟩ : syracuseStep 1154855 = 1732283) B1732283
theorem B1154895 : Blo 1152637 1154895 := bstep (se 1 (by rfl) ⟨866171, by rfl⟩ : syracuseStep 1154895 = 1732343) B1732343
theorem B1154911 : Blo 1152637 1154911 := bstep (se 1 (by rfl) ⟨866183, by rfl⟩ : syracuseStep 1154911 = 1732367) B1732367
theorem B2924383 : Blo 1152637 2924383 := bstep (se 1 (by rfl) ⟨2193287, by rfl⟩ : syracuseStep 2924383 = 4386575) B4386575
theorem B2596715 : Blo 1152637 2596715 := bstep (se 1 (by rfl) ⟨1947536, by rfl⟩ : syracuseStep 2596715 = 3895073) B3895073
theorem B1154939 : Blo 1152637 1154939 := bstep (se 1 (by rfl) ⟨866204, by rfl⟩ : syracuseStep 1154939 = 1732409) B1732409
theorem B2596769 : Blo 1152637 2596769 := bstep (se 2 (by rfl) ⟨973788, by rfl⟩ : syracuseStep 2596769 = 1947577) B1947577
theorem B1154991 : Blo 1152637 1154991 := bstep (se 1 (by rfl) ⟨866243, by rfl⟩ : syracuseStep 1154991 = 1732487) B1732487
theorem B1155015 : Blo 1152637 1155015 := bstep (se 1 (by rfl) ⟨866261, by rfl⟩ : syracuseStep 1155015 = 1732523) B1732523
theorem B1155035 : Blo 1152637 1155035 := bstep (se 1 (by rfl) ⟨866276, by rfl⟩ : syracuseStep 1155035 = 1732553) B1732553
theorem B3285011 : Blo 1152637 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B1155111 : Blo 1152637 1155111 := bstep (se 1 (by rfl) ⟨866333, by rfl⟩ : syracuseStep 1155111 = 1732667) B1732667
theorem B1155151 : Blo 1152637 1155151 := bstep (se 1 (by rfl) ⟨866363, by rfl⟩ : syracuseStep 1155151 = 1732727) B1732727
theorem B1155167 : Blo 1152637 1155167 := bstep (se 1 (by rfl) ⟨866375, by rfl⟩ : syracuseStep 1155167 = 1732751) B1732751
theorem B1155195 : Blo 1152637 1155195 := bstep (se 1 (by rfl) ⟨866396, by rfl⟩ : syracuseStep 1155195 = 1732793) B1732793
theorem B1155247 : Blo 1152637 1155247 := bstep (se 1 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 1155247 = 1732871) B1732871
theorem B1155271 : Blo 1152637 1155271 := bstep (se 1 (by rfl) ⟨866453, by rfl⟩ : syracuseStep 1155271 = 1732907) B1732907
theorem B1155291 : Blo 1152637 1155291 := bstep (se 1 (by rfl) ⟨866468, by rfl⟩ : syracuseStep 1155291 = 1732937) B1732937
theorem B2597111 : Blo 1152637 2597111 := bstep (se 1 (by rfl) ⟨1947833, by rfl⟩ : syracuseStep 2597111 = 3895667) B3895667
theorem B1155367 : Blo 1152637 1155367 := bstep (se 1 (by rfl) ⟨866525, by rfl⟩ : syracuseStep 1155367 = 1733051) B1733051
theorem B1155407 : Blo 1152637 1155407 := bstep (se 1 (by rfl) ⟨866555, by rfl⟩ : syracuseStep 1155407 = 1733111) B1733111
theorem B8888663 : Blo 1152637 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B1155423 : Blo 1152637 1155423 := bstep (se 1 (by rfl) ⟨866567, by rfl⟩ : syracuseStep 1155423 = 1733135) B1733135
theorem B3285353 : Blo 1152637 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B1155451 : Blo 1152637 1155451 := bstep (se 1 (by rfl) ⟨866588, by rfl⟩ : syracuseStep 1155451 = 1733177) B1733177
theorem B1155503 : Blo 1152637 1155503 := bstep (se 1 (by rfl) ⟨866627, by rfl⟩ : syracuseStep 1155503 = 1733255) B1733255
theorem B1155527 : Blo 1152637 1155527 := bstep (se 1 (by rfl) ⟨866645, by rfl⟩ : syracuseStep 1155527 = 1733291) B1733291
theorem B3285467 : Blo 1152637 3285467 := bstep (se 1 (by rfl) ⟨2464100, by rfl⟩ : syracuseStep 3285467 = 4928201) B4928201
theorem B1155547 : Blo 1152637 1155547 := bstep (se 1 (by rfl) ⟨866660, by rfl⟩ : syracuseStep 1155547 = 1733321) B1733321
theorem B4923929 : Blo 1152637 4923929 := bstep (se 2 (by rfl) ⟨1846473, by rfl⟩ : syracuseStep 4923929 = 3692947) B3692947
theorem B1155623 : Blo 1152637 1155623 := bstep (se 1 (by rfl) ⟨866717, by rfl⟩ : syracuseStep 1155623 = 1733435) B1733435
theorem B1155663 : Blo 1152637 1155663 := bstep (se 1 (by rfl) ⟨866747, by rfl⟩ : syracuseStep 1155663 = 1733495) B1733495
theorem B1155679 : Blo 1152637 1155679 := bstep (se 1 (by rfl) ⟨866759, by rfl⟩ : syracuseStep 1155679 = 1733519) B1733519
theorem B1155707 : Blo 1152637 1155707 := bstep (se 1 (by rfl) ⟨866780, by rfl⟩ : syracuseStep 1155707 = 1733561) B1733561
theorem B1155759 : Blo 1152637 1155759 := bstep (se 1 (by rfl) ⟨866819, by rfl⟩ : syracuseStep 1155759 = 1733639) B1733639
theorem B1155783 : Blo 1152637 1155783 := bstep (se 1 (by rfl) ⟨866837, by rfl⟩ : syracuseStep 1155783 = 1733675) B1733675
theorem B1155803 : Blo 1152637 1155803 := bstep (se 1 (by rfl) ⟨866852, by rfl⟩ : syracuseStep 1155803 = 1733705) B1733705
theorem B2925305 : Blo 1152637 2925305 := bstep (se 2 (by rfl) ⟨1096989, by rfl⟩ : syracuseStep 2925305 = 2193979) B2193979
theorem B1155879 : Blo 1152637 1155879 := bstep (se 1 (by rfl) ⟨866909, by rfl⟩ : syracuseStep 1155879 = 1733819) B1733819
theorem B2597705 : Blo 1152637 2597705 := bstep (se 2 (by rfl) ⟨974139, by rfl⟩ : syracuseStep 2597705 = 1948279) B1948279
theorem B1155919 : Blo 1152637 1155919 := bstep (se 1 (by rfl) ⟨866939, by rfl⟩ : syracuseStep 1155919 = 1733879) B1733879
theorem B1155935 : Blo 1152637 1155935 := bstep (se 1 (by rfl) ⟨866951, by rfl⟩ : syracuseStep 1155935 = 1733903) B1733903
theorem B1155963 : Blo 1152637 1155963 := bstep (se 1 (by rfl) ⟨866972, by rfl⟩ : syracuseStep 1155963 = 1733945) B1733945
theorem B1156015 : Blo 1152637 1156015 := bstep (se 1 (by rfl) ⟨867011, by rfl⟩ : syracuseStep 1156015 = 1734023) B1734023
theorem B1156039 : Blo 1152637 1156039 := bstep (se 1 (by rfl) ⟨867029, by rfl⟩ : syracuseStep 1156039 = 1734059) B1734059
theorem B1156059 : Blo 1152637 1156059 := bstep (se 1 (by rfl) ⟨867044, by rfl⟩ : syracuseStep 1156059 = 1734089) B1734089
theorem B1156135 : Blo 1152637 1156135 := bstep (se 1 (by rfl) ⟨867101, by rfl⟩ : syracuseStep 1156135 = 1734203) B1734203
theorem B1156175 : Blo 1152637 1156175 := bstep (se 1 (by rfl) ⟨867131, by rfl⟩ : syracuseStep 1156175 = 1734263) B1734263
theorem B1156191 : Blo 1152637 1156191 := bstep (se 1 (by rfl) ⟨867143, by rfl⟩ : syracuseStep 1156191 = 1734287) B1734287
theorem B1156219 : Blo 1152637 1156219 := bstep (se 1 (by rfl) ⟨867164, by rfl⟩ : syracuseStep 1156219 = 1734329) B1734329
theorem B1156271 : Blo 1152637 1156271 := bstep (se 1 (by rfl) ⟨867203, by rfl⟩ : syracuseStep 1156271 = 1734407) B1734407
theorem B1156295 : Blo 1152637 1156295 := bstep (se 1 (by rfl) ⟨867221, by rfl⟩ : syracuseStep 1156295 = 1734443) B1734443
theorem B1156315 : Blo 1152637 1156315 := bstep (se 1 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 1156315 = 1734473) B1734473
theorem B1156391 : Blo 1152637 1156391 := bstep (se 1 (by rfl) ⟨867293, by rfl⟩ : syracuseStep 1156391 = 1734587) B1734587
theorem B1156431 : Blo 1152637 1156431 := bstep (se 1 (by rfl) ⟨867323, by rfl⟩ : syracuseStep 1156431 = 1734647) B1734647
theorem B1156447 : Blo 1152637 1156447 := bstep (se 1 (by rfl) ⟨867335, by rfl⟩ : syracuseStep 1156447 = 1734671) B1734671
theorem B1156475 : Blo 1152637 1156475 := bstep (se 1 (by rfl) ⟨867356, by rfl⟩ : syracuseStep 1156475 = 1734713) B1734713
theorem B2925953 : Blo 1152637 2925953 := bstep (se 2 (by rfl) ⟨1097232, by rfl⟩ : syracuseStep 2925953 = 2194465) B2194465
theorem B8758691 : Blo 1152637 8758691 := bstep (se 1 (by rfl) ⟨6569018, by rfl⟩ : syracuseStep 8758691 = 13138037) B13138037
theorem B1156527 : Blo 1152637 1156527 := bstep (se 1 (by rfl) ⟨867395, by rfl⟩ : syracuseStep 1156527 = 1734791) B1734791
theorem B1156551 : Blo 1152637 1156551 := bstep (se 1 (by rfl) ⟨867413, by rfl⟩ : syracuseStep 1156551 = 1734827) B1734827
theorem B1156571 : Blo 1152637 1156571 := bstep (se 1 (by rfl) ⟨867428, by rfl⟩ : syracuseStep 1156571 = 1734857) B1734857
theorem B13149701 : Blo 1152637 13149701 := bstep (se 4 (by rfl) ⟨1232784, by rfl⟩ : syracuseStep 13149701 = 2465569) B2465569
theorem B5842529 : Blo 1152637 5842529 := bstep (se 2 (by rfl) ⟨2190948, by rfl⟩ : syracuseStep 5842529 = 4381897) B4381897
theorem B2598497 : Blo 1152637 2598497 := bstep (se 2 (by rfl) ⟨974436, by rfl⟩ : syracuseStep 2598497 = 1948873) B1948873
theorem B3286651 : Blo 1152637 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B3286777 : Blo 1152637 3286777 := bstep (se 2 (by rfl) ⟨1232541, by rfl⟩ : syracuseStep 3286777 = 2465083) B2465083
theorem B9873211 : Blo 1152637 9873211 := bstep (se 1 (by rfl) ⟨7404908, by rfl⟩ : syracuseStep 9873211 = 14809817) B14809817
theorem B2631599 : Blo 1152637 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B2598839 : Blo 1152637 2598839 := bstep (se 1 (by rfl) ⟨1949129, by rfl⟩ : syracuseStep 2598839 = 3898259) B3898259
theorem B6662159 : Blo 1152637 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B2926763 : Blo 1152637 2926763 := bstep (se 1 (by rfl) ⟨2195072, by rfl⟩ : syracuseStep 2926763 = 4390145) B4390145
theorem B2599433 : Blo 1152637 2599433 := bstep (se 2 (by rfl) ⟨974787, by rfl⟩ : syracuseStep 2599433 = 1949575) B1949575
theorem B3287881 : Blo 1152637 3287881 := bstep (se 2 (by rfl) ⟨1232955, by rfl⟩ : syracuseStep 3287881 = 2465911) B2465911
theorem B2599775 : Blo 1152637 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B13151159 : Blo 1152637 13151159 := bstep (se 1 (by rfl) ⟨9863369, by rfl⟩ : syracuseStep 13151159 = 19726739) B19726739
theorem B2927623 : Blo 1152637 2927623 := bstep (se 1 (by rfl) ⟨2195717, by rfl⟩ : syracuseStep 2927623 = 4391435) B4391435
theorem B5843987 : Blo 1152637 5843987 := bstep (se 1 (by rfl) ⟨4382990, by rfl⟩ : syracuseStep 5843987 = 8765981) B8765981
theorem B2599955 : Blo 1152637 2599955 := bstep (se 1 (by rfl) ⟨1949966, by rfl⟩ : syracuseStep 2599955 = 3899933) B3899933
theorem B3288235 : Blo 1152637 3288235 := bstep (se 1 (by rfl) ⟨2466176, by rfl⟩ : syracuseStep 3288235 = 4932353) B4932353
theorem B2600297 : Blo 1152637 2600297 := bstep (se 2 (by rfl) ⟨975111, by rfl⟩ : syracuseStep 2600297 = 1950223) B1950223
theorem B1945127 : Blo 1152637 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B4927175 : Blo 1152637 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B8761121 : Blo 1152637 8761121 := bstep (se 2 (by rfl) ⟨3285420, by rfl⟩ : syracuseStep 8761121 = 6570841) B6570841
theorem B1945417 : Blo 1152637 1945417 := bstep (se 2 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 1945417 = 1459063) B1459063
theorem B1945451 : Blo 1152637 1945451 := bstep (se 1 (by rfl) ⟨1459088, by rfl⟩ : syracuseStep 1945451 = 2918177) B2918177
theorem B2600891 : Blo 1152637 2600891 := bstep (se 1 (by rfl) ⟨1950668, by rfl⟩ : syracuseStep 2600891 = 3901337) B3901337
theorem B3125267 : Blo 1152637 3125267 := bstep (se 1 (by rfl) ⟨2343950, by rfl⟩ : syracuseStep 3125267 = 4687901) B4687901
theorem B2601017 : Blo 1152637 2601017 := bstep (se 2 (by rfl) ⟨975381, by rfl⟩ : syracuseStep 2601017 = 1950763) B1950763
theorem B1945849 : Blo 1152637 1945849 := bstep (se 2 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 1945849 = 1459387) B1459387
theorem B7385431 : Blo 1152637 7385431 := bstep (se 1 (by rfl) ⟨5539073, by rfl⟩ : syracuseStep 7385431 = 11078147) B11078147
theorem B3125633 : Blo 1152637 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B2601359 : Blo 1152637 2601359 := bstep (se 1 (by rfl) ⟨1951019, by rfl⟩ : syracuseStep 2601359 = 3902039) B3902039
theorem B1946119 : Blo 1152637 1946119 := bstep (se 1 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 1946119 = 2919179) B2919179
theorem B2601683 : Blo 1152637 2601683 := bstep (se 1 (by rfl) ⟨1951262, by rfl⟩ : syracuseStep 2601683 = 3902525) B3902525
theorem B1946551 : Blo 1152637 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B1946747 : Blo 1152637 1946747 := bstep (se 1 (by rfl) ⟨1460060, by rfl⟩ : syracuseStep 1946747 = 2920121) B2920121
theorem B3749021 : Blo 1152637 3749021 := bstep (se 3 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 3749021 = 1405883) B1405883
theorem B75871403 : Blo 1152637 75871403 := bstep (se 1 (by rfl) ⟨56903552, by rfl⟩ : syracuseStep 75871403 = 113807105) B113807105
theorem B1947145 : Blo 1152637 1947145 := bstep (se 2 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 1947145 = 1460359) B1460359
theorem B2963083 : Blo 1152637 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B18036371 : Blo 1152637 18036371 := bstep (se 1 (by rfl) ⟨13527278, by rfl⟩ : syracuseStep 18036371 = 27054557) B27054557
theorem B1947307 : Blo 1152637 1947307 := bstep (se 1 (by rfl) ⟨1460480, by rfl⟩ : syracuseStep 1947307 = 2920961) B2920961
theorem B5846903 : Blo 1152637 5846903 := bstep (se 1 (by rfl) ⟨4385177, by rfl⟩ : syracuseStep 5846903 = 8770355) B8770355
theorem B1947611 : Blo 1152637 1947611 := bstep (se 1 (by rfl) ⟨1460708, by rfl⟩ : syracuseStep 1947611 = 2921417) B2921417
theorem B5552185 : Blo 1152637 5552185 := bstep (se 2 (by rfl) ⟨2082069, by rfl⟩ : syracuseStep 5552185 = 4164139) B4164139
theorem B3750059 : Blo 1152637 3750059 := bstep (se 1 (by rfl) ⟨2812544, by rfl⟩ : syracuseStep 3750059 = 5625089) B5625089
theorem B1947847 : Blo 1152637 1947847 := bstep (se 1 (by rfl) ⟨1460885, by rfl⟩ : syracuseStep 1947847 = 2921771) B2921771
theorem B1948009 : Blo 1152637 1948009 := bstep (se 2 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 1948009 = 1461007) B1461007
theorem B1849787 : Blo 1152637 1849787 := bstep (se 1 (by rfl) ⟨1387340, by rfl⟩ : syracuseStep 1849787 = 2774681) B2774681
theorem B7027181 : Blo 1152637 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B1849895 : Blo 1152637 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B4995769 : Blo 1152637 4995769 := bstep (se 2 (by rfl) ⟨1873413, by rfl⟩ : syracuseStep 4995769 = 3746827) B3746827
theorem B1948603 : Blo 1152637 1948603 := bstep (se 1 (by rfl) ⟨1461452, by rfl⟩ : syracuseStep 1948603 = 2922905) B2922905
theorem B1948711 : Blo 1152637 1948711 := bstep (se 1 (by rfl) ⟨1461533, by rfl⟩ : syracuseStep 1948711 = 2923067) B2923067
theorem B1850407 : Blo 1152637 1850407 := bstep (se 1 (by rfl) ⟨1387805, by rfl⟩ : syracuseStep 1850407 = 2775611) B2775611
theorem B7388279 : Blo 1152637 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B1949035 : Blo 1152637 1949035 := bstep (se 1 (by rfl) ⟨1461776, by rfl⟩ : syracuseStep 1949035 = 2923553) B2923553
theorem B35569181 : Blo 1152637 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B3292883 : Blo 1152637 3292883 := bstep (se 1 (by rfl) ⟨2469662, by rfl⟩ : syracuseStep 3292883 = 4939325) B4939325
theorem B5259001 : Blo 1152637 5259001 := bstep (se 2 (by rfl) ⟨1972125, by rfl⟩ : syracuseStep 5259001 = 3944251) B3944251
theorem B5554183 : Blo 1152637 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B3948601 : Blo 1152637 3948601 := bstep (se 2 (by rfl) ⟨1480725, by rfl⟩ : syracuseStep 3948601 = 2961451) B2961451
theorem B1950095 : Blo 1152637 1950095 := bstep (se 1 (by rfl) ⟨1462571, by rfl⟩ : syracuseStep 1950095 = 2925143) B2925143
theorem B8995337 : Blo 1152637 8995337 := bstep (se 2 (by rfl) ⟨3373251, by rfl⟩ : syracuseStep 8995337 = 6746503) B6746503
theorem B1950331 : Blo 1152637 1950331 := bstep (se 1 (by rfl) ⟨1462748, by rfl⟩ : syracuseStep 1950331 = 2925497) B2925497
theorem B2081609 : Blo 1152637 2081609 := bstep (se 2 (by rfl) ⟨780603, by rfl⟩ : syracuseStep 2081609 = 1561207) B1561207
theorem B1951195 : Blo 1152637 1951195 := bstep (se 1 (by rfl) ⟨1463396, by rfl⟩ : syracuseStep 1951195 = 2926793) B2926793
theorem B2082343 : Blo 1152637 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B5260897 : Blo 1152637 5260897 := bstep (se 2 (by rfl) ⟨1972836, by rfl⟩ : syracuseStep 5260897 = 3945673) B3945673
theorem B7390865 : Blo 1152637 7390865 := bstep (se 2 (by rfl) ⟨2771574, by rfl⟩ : syracuseStep 7390865 = 5543149) B5543149
theorem B18695929 : Blo 1152637 18695929 := bstep (se 2 (by rfl) ⟨7010973, by rfl⟩ : syracuseStep 18695929 = 14021947) B14021947
theorem B16893755 : Blo 1152637 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B1558379 : Blo 1152637 1558379 := bstep (se 1 (by rfl) ⟨1168784, by rfl⟩ : syracuseStep 1558379 = 2337569) B2337569
theorem B7030637 : Blo 1152637 7030637 := bstep (se 3 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 7030637 = 2636489) B2636489
theorem B1755055 : Blo 1152637 1755055 := bstep (se 1 (by rfl) ⟨1316291, by rfl⟩ : syracuseStep 1755055 = 2632583) B2632583
theorem B1460263 : Blo 1152637 1460263 := bstep (se 1 (by rfl) ⟨1095197, by rfl⟩ : syracuseStep 1460263 = 2190395) B2190395
theorem B1951823 : Blo 1152637 1951823 := bstep (se 1 (by rfl) ⟨1463867, by rfl⟩ : syracuseStep 1951823 = 2927735) B2927735
theorem B15190105 : Blo 1152637 15190105 := bstep (se 2 (by rfl) ⟨5696289, by rfl⟩ : syracuseStep 15190105 = 11392579) B11392579
theorem B6572299 : Blo 1152637 6572299 := bstep (se 1 (by rfl) ⟨4929224, by rfl⟩ : syracuseStep 6572299 = 9858449) B9858449
theorem B4933993 : Blo 1152637 4933993 := bstep (se 2 (by rfl) ⟨1850247, by rfl⟩ : syracuseStep 4933993 = 3700495) B3700495
theorem B1460587 : Blo 1152637 1460587 := bstep (se 1 (by rfl) ⟨1095440, by rfl⟩ : syracuseStep 1460587 = 2190881) B2190881
theorem B1296859 : Blo 1152637 1296859 := bstep (se 1 (by rfl) ⟨972644, by rfl⟩ : syracuseStep 1296859 = 1945289) B1945289
theorem B1297327 : Blo 1152637 1297327 := bstep (se 1 (by rfl) ⟨972995, by rfl⟩ : syracuseStep 1297327 = 1945991) B1945991
theorem B3328943 : Blo 1152637 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B5852087 : Blo 1152637 5852087 := bstep (se 1 (by rfl) ⟨4389065, by rfl⟩ : syracuseStep 5852087 = 8778131) B8778131
theorem B16633025 : Blo 1152637 16633025 := bstep (se 2 (by rfl) ⟨6237384, by rfl⟩ : syracuseStep 16633025 = 12474769) B12474769
theorem B8310053 : Blo 1152637 8310053 := bstep (se 4 (by rfl) ⟨779067, by rfl⟩ : syracuseStep 8310053 = 1558135) B1558135
theorem B1297759 : Blo 1152637 1297759 := bstep (se 1 (by rfl) ⟨973319, by rfl⟩ : syracuseStep 1297759 = 1946639) B1946639
theorem B1461883 : Blo 1152637 1461883 := bstep (se 1 (by rfl) ⟨1096412, by rfl⟩ : syracuseStep 1461883 = 2192825) B2192825
theorem B6573757 : Blo 1152637 6573757 := bstep (se 3 (by rfl) ⟨1232579, by rfl⟩ : syracuseStep 6573757 = 2465159) B2465159
theorem B1298119 : Blo 1152637 1298119 := bstep (se 1 (by rfl) ⟨973589, by rfl⟩ : syracuseStep 1298119 = 1947179) B1947179
theorem B2772911 : Blo 1152637 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B1232815 : Blo 1152637 1232815 := bstep (se 1 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 1232815 = 1849223) B1849223
theorem B4378967 : Blo 1152637 4378967 := bstep (se 1 (by rfl) ⟨3284225, by rfl⟩ : syracuseStep 4378967 = 6568451) B6568451
theorem B5853545 : Blo 1152637 5853545 := bstep (se 2 (by rfl) ⟨2195079, by rfl⟩ : syracuseStep 5853545 = 4390159) B4390159
theorem B1298983 : Blo 1152637 1298983 := bstep (se 1 (by rfl) ⟨974237, by rfl⟩ : syracuseStep 1298983 = 1948475) B1948475
theorem B7033553 : Blo 1152637 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B4215545 : Blo 1152637 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B2774035 : Blo 1152637 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B1463771 : Blo 1152637 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B4380257 : Blo 1152637 4380257 := bstep (se 2 (by rfl) ⟨1642596, by rfl⟩ : syracuseStep 4380257 = 3285193) B3285193
theorem B4675283 : Blo 1152637 4675283 := bstep (se 1 (by rfl) ⟨3506462, by rfl⟩ : syracuseStep 4675283 = 7012925) B7012925
theorem B3954539 : Blo 1152637 3954539 := bstep (se 1 (by rfl) ⟨2965904, by rfl⟩ : syracuseStep 3954539 = 5931809) B5931809
theorem B1300603 : Blo 1152637 1300603 := bstep (se 1 (by rfl) ⟨975452, by rfl⟩ : syracuseStep 1300603 = 1950905) B1950905
theorem B2218195 : Blo 1152637 2218195 := bstep (se 1 (by rfl) ⟨1663646, by rfl⟩ : syracuseStep 2218195 = 3327293) B3327293
theorem B8771813 : Blo 1152637 8771813 := bstep (se 4 (by rfl) ⟨822357, by rfl⟩ : syracuseStep 8771813 = 1644715) B1644715
theorem B4676059 : Blo 1152637 4676059 := bstep (se 1 (by rfl) ⟨3507044, by rfl⟩ : syracuseStep 4676059 = 7014089) B7014089
theorem B6576673 : Blo 1152637 6576673 := bstep (se 2 (by rfl) ⟨2466252, by rfl⟩ : syracuseStep 6576673 = 4932505) B4932505
theorem B1301071 : Blo 1152637 1301071 := bstep (se 1 (by rfl) ⟨975803, by rfl⟩ : syracuseStep 1301071 = 1951607) B1951607
theorem B3955499 : Blo 1152637 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B4381715 : Blo 1152637 4381715 := bstep (se 1 (by rfl) ⟨3286286, by rfl⟩ : syracuseStep 4381715 = 6572573) B6572573
theorem B11852993 : Blo 1152637 11852993 := bstep (se 2 (by rfl) ⟨4444872, by rfl⟩ : syracuseStep 11852993 = 8889745) B8889745
theorem B7396555 : Blo 1152637 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B3890537 : Blo 1152637 3890537 := bstep (se 2 (by rfl) ⟨1458951, by rfl⟩ : syracuseStep 3890537 = 2917903) B2917903
theorem B4382171 : Blo 1152637 4382171 := bstep (se 1 (by rfl) ⟨3286628, by rfl⟩ : syracuseStep 4382171 = 6573257) B6573257
theorem B3694177 : Blo 1152637 3694177 := bstep (se 2 (by rfl) ⟨1385316, by rfl⟩ : syracuseStep 3694177 = 2770633) B2770633
theorem B18243191 : Blo 1152637 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B8675207 : Blo 1152637 8675207 := bstep (se 1 (by rfl) ⟨6506405, by rfl⟩ : syracuseStep 8675207 = 13012811) B13012811
theorem B3694511 : Blo 1152637 3694511 := bstep (se 1 (by rfl) ⟨2770883, by rfl⟩ : syracuseStep 3694511 = 5541767) B5541767
theorem B3891131 : Blo 1152637 3891131 := bstep (se 1 (by rfl) ⟨2918348, by rfl⟩ : syracuseStep 3891131 = 5836697) B5836697
theorem B1171675 : Blo 1152637 1171675 := bstep (se 1 (by rfl) ⟨878756, by rfl⟩ : syracuseStep 1171675 = 1757513) B1757513
theorem B4940297 : Blo 1152637 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B1925689 : Blo 1152637 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B1729103 : Blo 1152637 1729103 := bstep (se 1 (by rfl) ⟨1296827, by rfl⟩ : syracuseStep 1729103 = 2593655) B2593655
theorem B4383355 : Blo 1152637 4383355 := bstep (se 1 (by rfl) ⟨3287516, by rfl⟩ : syracuseStep 4383355 = 6575033) B6575033
theorem B1729223 : Blo 1152637 1729223 := bstep (se 1 (by rfl) ⟨1296917, by rfl⟩ : syracuseStep 1729223 = 2593835) B2593835
theorem B14803667 : Blo 1152637 14803667 := bstep (se 1 (by rfl) ⟨11102750, by rfl⟩ : syracuseStep 14803667 = 22205501) B22205501
theorem B1729385 : Blo 1152637 1729385 := bstep (se 2 (by rfl) ⟨648519, by rfl⟩ : syracuseStep 1729385 = 1297039) B1297039
theorem B1729463 : Blo 1152637 1729463 := bstep (se 1 (by rfl) ⟨1297097, by rfl⟩ : syracuseStep 1729463 = 2594195) B2594195
theorem B1729499 : Blo 1152637 1729499 := bstep (se 1 (by rfl) ⟨1297124, by rfl⟩ : syracuseStep 1729499 = 2594249) B2594249
theorem B33743891 : Blo 1152637 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B2188367 : Blo 1152637 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B7398553 : Blo 1152637 7398553 := bstep (se 2 (by rfl) ⟨2774457, by rfl⟩ : syracuseStep 7398553 = 5548915) B5548915
theorem B13165739 : Blo 1152637 13165739 := bstep (se 1 (by rfl) ⟨9874304, by rfl⟩ : syracuseStep 13165739 = 19748609) B19748609
theorem B1729967 : Blo 1152637 1729967 := bstep (se 1 (by rfl) ⟨1297475, by rfl⟩ : syracuseStep 1729967 = 2594951) B2594951
theorem B1730057 : Blo 1152637 1730057 := bstep (se 2 (by rfl) ⟨648771, by rfl⟩ : syracuseStep 1730057 = 1297543) B1297543
theorem B1730087 : Blo 1152637 1730087 := bstep (se 1 (by rfl) ⟨1297565, by rfl⟩ : syracuseStep 1730087 = 2595131) B2595131
theorem B3892859 : Blo 1152637 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B1730171 : Blo 1152637 1730171 := bstep (se 1 (by rfl) ⟨1297628, by rfl⟩ : syracuseStep 1730171 = 2595257) B2595257
theorem B1730297 : Blo 1152637 1730297 := bstep (se 2 (by rfl) ⟨648861, by rfl⟩ : syracuseStep 1730297 = 1297723) B1297723
theorem B3893021 : Blo 1152637 3893021 := bstep (se 3 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 3893021 = 1459883) B1459883
theorem B6416171 : Blo 1152637 6416171 := bstep (se 1 (by rfl) ⟨4812128, by rfl⟩ : syracuseStep 6416171 = 9624257) B9624257
theorem B13133663 : Blo 1152637 13133663 := bstep (se 1 (by rfl) ⟨9850247, by rfl⟩ : syracuseStep 13133663 = 19700495) B19700495
theorem B1730399 : Blo 1152637 1730399 := bstep (se 1 (by rfl) ⟨1297799, by rfl⟩ : syracuseStep 1730399 = 2595599) B2595599
theorem B1730411 : Blo 1152637 1730411 := bstep (se 1 (by rfl) ⟨1297808, by rfl⟩ : syracuseStep 1730411 = 2595617) B2595617
theorem B4384631 : Blo 1152637 4384631 := bstep (se 1 (by rfl) ⟨3288473, by rfl⟩ : syracuseStep 4384631 = 6576947) B6576947
theorem B168814529 : Blo 1152637 168814529 := bstep (se 2 (by rfl) ⟨63305448, by rfl⟩ : syracuseStep 168814529 = 126610897) B126610897
theorem B2189369 : Blo 1152637 2189369 := bstep (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) B1642027
theorem B1730639 : Blo 1152637 1730639 := bstep (se 1 (by rfl) ⟨1297979, by rfl⟩ : syracuseStep 1730639 = 2595959) B2595959
theorem B4155563 : Blo 1152637 4155563 := bstep (se 1 (by rfl) ⟨3116672, by rfl⟩ : syracuseStep 4155563 = 6233345) B6233345
theorem B1730759 : Blo 1152637 1730759 := bstep (se 1 (by rfl) ⟨1298069, by rfl⟩ : syracuseStep 1730759 = 2596139) B2596139
theorem B1730921 : Blo 1152637 1730921 := bstep (se 2 (by rfl) ⟨649095, by rfl⟩ : syracuseStep 1730921 = 1298191) B1298191
theorem B1730999 : Blo 1152637 1730999 := bstep (se 1 (by rfl) ⟨1298249, by rfl⟩ : syracuseStep 1730999 = 2596499) B2596499
theorem B3893723 : Blo 1152637 3893723 := bstep (se 1 (by rfl) ⟨2920292, by rfl⟩ : syracuseStep 3893723 = 5840585) B5840585
theorem B1731035 : Blo 1152637 1731035 := bstep (se 1 (by rfl) ⟨1298276, by rfl⟩ : syracuseStep 1731035 = 2596553) B2596553
theorem B12806689 : Blo 1152637 12806689 := bstep (se 2 (by rfl) ⟨4802508, by rfl⟩ : syracuseStep 12806689 = 9605017) B9605017
theorem B5270201 : Blo 1152637 5270201 := bstep (se 2 (by rfl) ⟨1976325, by rfl⟩ : syracuseStep 5270201 = 3952651) B3952651
theorem B12479177 : Blo 1152637 12479177 := bstep (se 2 (by rfl) ⟨4679691, by rfl⟩ : syracuseStep 12479177 = 9359383) B9359383
theorem B4385603 : Blo 1152637 4385603 := bstep (se 1 (by rfl) ⟨3289202, by rfl⟩ : syracuseStep 4385603 = 6578405) B6578405
theorem B1731503 : Blo 1152637 1731503 := bstep (se 1 (by rfl) ⟨1298627, by rfl⟩ : syracuseStep 1731503 = 2597255) B2597255
theorem B1731593 : Blo 1152637 1731593 := bstep (se 2 (by rfl) ⟨649347, by rfl⟩ : syracuseStep 1731593 = 1298695) B1298695
theorem B1731623 : Blo 1152637 1731623 := bstep (se 1 (by rfl) ⟨1298717, by rfl⟩ : syracuseStep 1731623 = 2597435) B2597435
theorem B1731707 : Blo 1152637 1731707 := bstep (se 1 (by rfl) ⟨1298780, by rfl⟩ : syracuseStep 1731707 = 2597561) B2597561
theorem B3894425 : Blo 1152637 3894425 := bstep (se 2 (by rfl) ⟨1460409, by rfl⟩ : syracuseStep 3894425 = 2920819) B2920819
theorem B1731833 : Blo 1152637 1731833 := bstep (se 2 (by rfl) ⟨649437, by rfl⟩ : syracuseStep 1731833 = 1298875) B1298875
theorem B4386059 : Blo 1152637 4386059 := bstep (se 1 (by rfl) ⟨3289544, by rfl⟩ : syracuseStep 4386059 = 6579089) B6579089
theorem B1731935 : Blo 1152637 1731935 := bstep (se 1 (by rfl) ⟨1298951, by rfl⟩ : syracuseStep 1731935 = 2597903) B2597903
theorem B1731947 : Blo 1152637 1731947 := bstep (se 1 (by rfl) ⟨1298960, by rfl⟩ : syracuseStep 1731947 = 2597921) B2597921
theorem B1732175 : Blo 1152637 1732175 := bstep (se 1 (by rfl) ⟨1299131, by rfl⟩ : syracuseStep 1732175 = 2598263) B2598263
theorem B1732295 : Blo 1152637 1732295 := bstep (se 1 (by rfl) ⟨1299221, by rfl⟩ : syracuseStep 1732295 = 2598443) B2598443
theorem B4746961 : Blo 1152637 4746961 := bstep (se 2 (by rfl) ⟨1780110, by rfl⟩ : syracuseStep 4746961 = 3560221) B3560221
theorem B1732457 : Blo 1152637 1732457 := bstep (se 2 (by rfl) ⟨649671, by rfl⟩ : syracuseStep 1732457 = 1299343) B1299343
theorem B1732535 : Blo 1152637 1732535 := bstep (se 1 (by rfl) ⟨1299401, by rfl⟩ : syracuseStep 1732535 = 2598803) B2598803
theorem B4386743 : Blo 1152637 4386743 := bstep (se 1 (by rfl) ⟨3290057, by rfl⟩ : syracuseStep 4386743 = 6580115) B6580115
theorem B7401401 : Blo 1152637 7401401 := bstep (se 2 (by rfl) ⟨2775525, by rfl⟩ : syracuseStep 7401401 = 5551051) B5551051
theorem B1732571 : Blo 1152637 1732571 := bstep (se 1 (by rfl) ⟨1299428, by rfl⟩ : syracuseStep 1732571 = 2598857) B2598857
theorem B2191367 : Blo 1152637 2191367 := bstep (se 1 (by rfl) ⟨1643525, by rfl⟩ : syracuseStep 2191367 = 3287051) B3287051
theorem B9367559 : Blo 1152637 9367559 := bstep (se 1 (by rfl) ⟨7025669, by rfl⟩ : syracuseStep 9367559 = 14051339) B14051339
theorem B13168655 : Blo 1152637 13168655 := bstep (se 1 (by rfl) ⟨9876491, by rfl⟩ : syracuseStep 13168655 = 19752983) B19752983
theorem B3895613 : Blo 1152637 3895613 := bstep (se 3 (by rfl) ⟨730427, by rfl⟩ : syracuseStep 3895613 = 1460855) B1460855
theorem B14807357 : Blo 1152637 14807357 := bstep (se 3 (by rfl) ⟨2776379, by rfl⟩ : syracuseStep 14807357 = 5552759) B5552759
theorem B1733039 : Blo 1152637 1733039 := bstep (se 1 (by rfl) ⟨1299779, by rfl⟩ : syracuseStep 1733039 = 2599559) B2599559
theorem B2191799 : Blo 1152637 2191799 := bstep (se 1 (by rfl) ⟨1643849, by rfl⟩ : syracuseStep 2191799 = 3287699) B3287699
theorem B1733129 : Blo 1152637 1733129 := bstep (se 2 (by rfl) ⟨649923, by rfl⟩ : syracuseStep 1733129 = 1299847) B1299847
theorem B1733159 : Blo 1152637 1733159 := bstep (se 1 (by rfl) ⟨1299869, by rfl⟩ : syracuseStep 1733159 = 2599739) B2599739
theorem B2191951 : Blo 1152637 2191951 := bstep (se 1 (by rfl) ⟨1643963, by rfl⟩ : syracuseStep 2191951 = 3287927) B3287927
theorem B1733243 : Blo 1152637 1733243 := bstep (se 1 (by rfl) ⟨1299932, by rfl⟩ : syracuseStep 1733243 = 2599865) B2599865
theorem B4387517 : Blo 1152637 4387517 := bstep (se 3 (by rfl) ⟨822659, by rfl⟩ : syracuseStep 4387517 = 1645319) B1645319
theorem B1733369 : Blo 1152637 1733369 := bstep (se 2 (by rfl) ⟨650013, by rfl⟩ : syracuseStep 1733369 = 1300027) B1300027
theorem B1733471 : Blo 1152637 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B1733483 : Blo 1152637 1733483 := bstep (se 1 (by rfl) ⟨1300112, by rfl⟩ : syracuseStep 1733483 = 2600225) B2600225
theorem B36008819 : Blo 1152637 36008819 := bstep (se 1 (by rfl) ⟨27006614, by rfl⟩ : syracuseStep 36008819 = 54013229) B54013229
theorem B5272577 : Blo 1152637 5272577 := bstep (se 2 (by rfl) ⟨1977216, by rfl⟩ : syracuseStep 5272577 = 3954433) B3954433
theorem B1733711 : Blo 1152637 1733711 := bstep (se 1 (by rfl) ⟨1300283, by rfl⟩ : syracuseStep 1733711 = 2600567) B2600567
theorem B3896477 : Blo 1152637 3896477 := bstep (se 3 (by rfl) ⟨730589, by rfl⟩ : syracuseStep 3896477 = 1461179) B1461179
theorem B1733831 : Blo 1152637 1733831 := bstep (se 1 (by rfl) ⟨1300373, by rfl⟩ : syracuseStep 1733831 = 2600747) B2600747
theorem B4388201 : Blo 1152637 4388201 := bstep (se 2 (by rfl) ⟨1645575, by rfl⟩ : syracuseStep 4388201 = 3291151) B3291151
theorem B1733993 : Blo 1152637 1733993 := bstep (se 2 (by rfl) ⟨650247, by rfl⟩ : syracuseStep 1733993 = 1300495) B1300495
theorem B3700097 : Blo 1152637 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B1734071 : Blo 1152637 1734071 := bstep (se 1 (by rfl) ⟨1300553, by rfl⟩ : syracuseStep 1734071 = 2601107) B2601107
theorem B1734107 : Blo 1152637 1734107 := bstep (se 1 (by rfl) ⟨1300580, by rfl⟩ : syracuseStep 1734107 = 2601161) B2601161
theorem B1668647 : Blo 1152637 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B3897017 : Blo 1152637 3897017 := bstep (se 2 (by rfl) ⟨1461381, by rfl⟩ : syracuseStep 3897017 = 2922763) B2922763
theorem B2193257 : Blo 1152637 2193257 := bstep (se 2 (by rfl) ⟨822471, by rfl⟩ : syracuseStep 2193257 = 1644943) B1644943
theorem B1734575 : Blo 1152637 1734575 := bstep (se 1 (by rfl) ⟨1300931, by rfl⟩ : syracuseStep 1734575 = 2601863) B2601863
theorem B1734665 : Blo 1152637 1734665 := bstep (se 2 (by rfl) ⟨650499, by rfl⟩ : syracuseStep 1734665 = 1300999) B1300999
theorem B1734695 : Blo 1152637 1734695 := bstep (se 1 (by rfl) ⟨1301021, by rfl⟩ : syracuseStep 1734695 = 2602043) B2602043
theorem B1734779 : Blo 1152637 1734779 := bstep (se 1 (by rfl) ⟨1301084, by rfl⟩ : syracuseStep 1734779 = 2602169) B2602169
theorem B1734905 : Blo 1152637 1734905 := bstep (se 2 (by rfl) ⟨650589, by rfl⟩ : syracuseStep 1734905 = 1301179) B1301179
theorem B3897611 : Blo 1152637 3897611 := bstep (se 1 (by rfl) ⟨2923208, by rfl⟩ : syracuseStep 3897611 = 5846417) B5846417
theorem B9861425 : Blo 1152637 9861425 := bstep (se 2 (by rfl) ⟨3698034, by rfl⟩ : syracuseStep 9861425 = 7396069) B7396069
theorem B5929453 : Blo 1152637 5929453 := bstep (se 3 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 5929453 = 2223545) B2223545
theorem B3897881 : Blo 1152637 3897881 := bstep (se 2 (by rfl) ⟨1461705, by rfl⟩ : syracuseStep 3897881 = 2923411) B2923411
theorem B2194283 : Blo 1152637 2194283 := bstep (se 1 (by rfl) ⟨1645712, by rfl⟩ : syracuseStep 2194283 = 3291425) B3291425
theorem B9370673 : Blo 1152637 9370673 := bstep (se 2 (by rfl) ⟨3514002, by rfl⟩ : syracuseStep 9370673 = 7028005) B7028005
theorem B14777423 : Blo 1152637 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B8781047 : Blo 1152637 8781047 := bstep (se 1 (by rfl) ⟨6585785, by rfl⟩ : syracuseStep 8781047 = 13171571) B13171571
theorem B2194951 : Blo 1152637 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B4390433 : Blo 1152637 4390433 := bstep (se 2 (by rfl) ⟨1646412, by rfl⟩ : syracuseStep 4390433 = 3292825) B3292825
theorem B13139495 : Blo 1152637 13139495 := bstep (se 1 (by rfl) ⟨9854621, by rfl⟩ : syracuseStep 13139495 = 19709243) B19709243
theorem B3899015 : Blo 1152637 3899015 := bstep (se 1 (by rfl) ⟨2924261, by rfl⟩ : syracuseStep 3899015 = 5848523) B5848523
theorem B11107979 : Blo 1152637 11107979 := bstep (se 1 (by rfl) ⟨8330984, by rfl⟩ : syracuseStep 11107979 = 16661969) B16661969
theorem B3899069 : Blo 1152637 3899069 := bstep (se 3 (by rfl) ⟨731075, by rfl⟩ : syracuseStep 3899069 = 1462151) B1462151
theorem B8781533 : Blo 1152637 8781533 := bstep (se 3 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 8781533 = 3293075) B3293075
theorem B4685597 : Blo 1152637 4685597 := bstep (se 3 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 4685597 = 1757099) B1757099
theorem B3702557 : Blo 1152637 3702557 := bstep (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) B1388459
theorem B3899231 : Blo 1152637 3899231 := bstep (se 1 (by rfl) ⟨2924423, by rfl⟩ : syracuseStep 3899231 = 5848847) B5848847
theorem B7405577 : Blo 1152637 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B5996891 : Blo 1152637 5996891 := bstep (se 1 (by rfl) ⟨4497668, by rfl⟩ : syracuseStep 5996891 = 8995337) B8995337
theorem B23659411 : Blo 1152637 23659411 := bstep (se 1 (by rfl) ⟨17744558, by rfl⟩ : syracuseStep 23659411 = 35489117) B35489117
theorem B11830373 : Blo 1152637 11830373 := bstep (se 4 (by rfl) ⟨1109097, by rfl⟩ : syracuseStep 11830373 = 2218195) B2218195
theorem B8782991 : Blo 1152637 8782991 := bstep (se 1 (by rfl) ⟨6587243, by rfl⟩ : syracuseStep 8782991 = 13174487) B13174487
theorem B4687091 : Blo 1152637 4687091 := bstep (se 1 (by rfl) ⟨3515318, by rfl⟩ : syracuseStep 4687091 = 7030637) B7030637
theorem B9864737 : Blo 1152637 9864737 := bstep (se 2 (by rfl) ⟨3699276, by rfl⟩ : syracuseStep 9864737 = 7398553) B7398553
theorem B3901391 : Blo 1152637 3901391 := bstep (se 1 (by rfl) ⟨2926043, by rfl⟩ : syracuseStep 3901391 = 5852087) B5852087
theorem B7014529 : Blo 1152637 7014529 := bstep (se 2 (by rfl) ⟨2630448, by rfl⟩ : syracuseStep 7014529 = 5260897) B5260897
theorem B20253473 : Blo 1152637 20253473 := bstep (se 2 (by rfl) ⟨7595052, by rfl⟩ : syracuseStep 20253473 = 15190105) B15190105
theorem B2919311 : Blo 1152637 2919311 := bstep (se 1 (by rfl) ⟨2189483, by rfl⟩ : syracuseStep 2919311 = 4378967) B4378967
theorem B3902363 : Blo 1152637 3902363 := bstep (se 1 (by rfl) ⟨2926772, by rfl⟩ : syracuseStep 3902363 = 5853545) B5853545
theorem B8326259 : Blo 1152637 8326259 := bstep (se 1 (by rfl) ⟨6244694, by rfl⟩ : syracuseStep 8326259 = 12489389) B12489389
theorem B4689035 : Blo 1152637 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B17075585 : Blo 1152637 17075585 := bstep (se 2 (by rfl) ⟨6403344, by rfl⟩ : syracuseStep 17075585 = 12806689) B12806689
theorem B2920171 : Blo 1152637 2920171 := bstep (se 1 (by rfl) ⟨2190128, by rfl⟩ : syracuseStep 2920171 = 4380257) B4380257
theorem B30412523 : Blo 1152637 30412523 := bstep (se 1 (by rfl) ⟨22809392, by rfl⟩ : syracuseStep 30412523 = 45618785) B45618785
theorem B3116855 : Blo 1152637 3116855 := bstep (se 1 (by rfl) ⟨2337641, by rfl⟩ : syracuseStep 3116855 = 4675283) B4675283
theorem B1642295 : Blo 1152637 1642295 := bstep (se 1 (by rfl) ⟨1231721, by rfl⟩ : syracuseStep 1642295 = 2463443) B2463443
theorem B3903389 : Blo 1152637 3903389 := bstep (se 3 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 3903389 = 1463771) B1463771
theorem B3903497 : Blo 1152637 3903497 := bstep (se 2 (by rfl) ⟨1463811, by rfl⟩ : syracuseStep 3903497 = 2927623) B2927623
theorem B5836859 : Blo 1152637 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B3805547 : Blo 1152637 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B7410035 : Blo 1152637 7410035 := bstep (se 1 (by rfl) ⟨5557526, by rfl⟩ : syracuseStep 7410035 = 11115053) B11115053
theorem B8327731 : Blo 1152637 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B2921143 : Blo 1152637 2921143 := bstep (se 1 (by rfl) ⟨2190857, by rfl⟩ : syracuseStep 2921143 = 4381715) B4381715
theorem B2593691 : Blo 1152637 2593691 := bstep (se 1 (by rfl) ⟨1945268, by rfl⟩ : syracuseStep 2593691 = 3890537) B3890537
theorem B6329281 : Blo 1152637 6329281 := bstep (se 2 (by rfl) ⟨2373480, by rfl⟩ : syracuseStep 6329281 = 4746961) B4746961
theorem B2921447 : Blo 1152637 2921447 := bstep (se 1 (by rfl) ⟨2191085, by rfl⟩ : syracuseStep 2921447 = 4382171) B4382171
theorem B5837831 : Blo 1152637 5837831 := bstep (se 1 (by rfl) ⟨4378373, by rfl⟩ : syracuseStep 5837831 = 8756747) B8756747
theorem B2593889 : Blo 1152637 2593889 := bstep (se 2 (by rfl) ⟨972708, by rfl⟩ : syracuseStep 2593889 = 1945417) B1945417
theorem B1643753 : Blo 1152637 1643753 := bstep (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) B1232815
theorem B2463007 : Blo 1152637 2463007 := bstep (se 1 (by rfl) ⟨1847255, by rfl⟩ : syracuseStep 2463007 = 3694511) B3694511
theorem B2594087 : Blo 1152637 2594087 := bstep (se 1 (by rfl) ⟨1945565, by rfl⟩ : syracuseStep 2594087 = 3891131) B3891131
theorem B5838317 : Blo 1152637 5838317 := bstep (se 3 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 5838317 = 2189369) B2189369
theorem B9868837 : Blo 1152637 9868837 := bstep (se 4 (by rfl) ⟨925203, by rfl⟩ : syracuseStep 9868837 = 1850407) B1850407
theorem B2594465 : Blo 1152637 2594465 := bstep (se 2 (by rfl) ⟨972924, by rfl⟩ : syracuseStep 2594465 = 1945849) B1945849
theorem B3282619 : Blo 1152637 3282619 := bstep (se 1 (by rfl) ⟨2461964, by rfl⟩ : syracuseStep 3282619 = 4923929) B4923929
theorem B1152735 : Blo 1152637 1152735 := bstep (se 1 (by rfl) ⟨864551, by rfl⟩ : syracuseStep 1152735 = 1729103) B1729103
theorem B1152815 : Blo 1152637 1152815 := bstep (se 1 (by rfl) ⟨864611, by rfl⟩ : syracuseStep 1152815 = 1729223) B1729223
theorem B9869111 : Blo 1152637 9869111 := bstep (se 1 (by rfl) ⟨7401833, by rfl⟩ : syracuseStep 9869111 = 14803667) B14803667
theorem B1152923 : Blo 1152637 1152923 := bstep (se 1 (by rfl) ⟨864692, by rfl⟩ : syracuseStep 1152923 = 1729385) B1729385
theorem B1152975 : Blo 1152637 1152975 := bstep (se 1 (by rfl) ⟨864731, by rfl⟩ : syracuseStep 1152975 = 1729463) B1729463
theorem B1152999 : Blo 1152637 1152999 := bstep (se 1 (by rfl) ⟨864749, by rfl⟩ : syracuseStep 1152999 = 1729499) B1729499
theorem B2594825 : Blo 1152637 2594825 := bstep (se 2 (by rfl) ⟨973059, by rfl⟩ : syracuseStep 2594825 = 1946119) B1946119
theorem B2922601 : Blo 1152637 2922601 := bstep (se 2 (by rfl) ⟨1095975, by rfl⟩ : syracuseStep 2922601 = 2191951) B2191951
theorem B5839127 : Blo 1152637 5839127 := bstep (se 1 (by rfl) ⟨4379345, by rfl⟩ : syracuseStep 5839127 = 8758691) B8758691
theorem B1153311 : Blo 1152637 1153311 := bstep (se 1 (by rfl) ⟨864983, by rfl⟩ : syracuseStep 1153311 = 1729967) B1729967
theorem B1153371 : Blo 1152637 1153371 := bstep (se 1 (by rfl) ⟨865028, by rfl⟩ : syracuseStep 1153371 = 1730057) B1730057
theorem B1153391 : Blo 1152637 1153391 := bstep (se 1 (by rfl) ⟨865043, by rfl⟩ : syracuseStep 1153391 = 1730087) B1730087
theorem B2595239 : Blo 1152637 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B1153447 : Blo 1152637 1153447 := bstep (se 1 (by rfl) ⟨865085, by rfl⟩ : syracuseStep 1153447 = 1730171) B1730171
theorem B1153531 : Blo 1152637 1153531 := bstep (se 1 (by rfl) ⟨865148, by rfl⟩ : syracuseStep 1153531 = 1730297) B1730297
theorem B2595347 : Blo 1152637 2595347 := bstep (se 1 (by rfl) ⟨1946510, by rfl⟩ : syracuseStep 2595347 = 3893021) B3893021
theorem B8755775 : Blo 1152637 8755775 := bstep (se 1 (by rfl) ⟨6566831, by rfl⟩ : syracuseStep 8755775 = 13133663) B13133663
theorem B1153599 : Blo 1152637 1153599 := bstep (se 1 (by rfl) ⟨865199, by rfl⟩ : syracuseStep 1153599 = 1730399) B1730399
theorem B1153607 : Blo 1152637 1153607 := bstep (se 1 (by rfl) ⟨865205, by rfl⟩ : syracuseStep 1153607 = 1730411) B1730411
theorem B2595401 : Blo 1152637 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B2923087 : Blo 1152637 2923087 := bstep (se 1 (by rfl) ⟨2192315, by rfl⟩ : syracuseStep 2923087 = 4384631) B4384631
theorem B1153759 : Blo 1152637 1153759 := bstep (se 1 (by rfl) ⟨865319, by rfl⟩ : syracuseStep 1153759 = 1730639) B1730639
theorem B1153839 : Blo 1152637 1153839 := bstep (se 1 (by rfl) ⟨865379, by rfl⟩ : syracuseStep 1153839 = 1730759) B1730759
theorem B1153947 : Blo 1152637 1153947 := bstep (se 1 (by rfl) ⟨865460, by rfl⟩ : syracuseStep 1153947 = 1730921) B1730921
theorem B1153999 : Blo 1152637 1153999 := bstep (se 1 (by rfl) ⟨865499, by rfl⟩ : syracuseStep 1153999 = 1730999) B1730999
theorem B2595815 : Blo 1152637 2595815 := bstep (se 1 (by rfl) ⟨1946861, by rfl⟩ : syracuseStep 2595815 = 3893723) B3893723
theorem B1154023 : Blo 1152637 1154023 := bstep (se 1 (by rfl) ⟨865517, by rfl⟩ : syracuseStep 1154023 = 1731035) B1731035
theorem B3513467 : Blo 1152637 3513467 := bstep (se 1 (by rfl) ⟨2635100, by rfl⟩ : syracuseStep 3513467 = 5270201) B5270201
theorem B2923735 : Blo 1152637 2923735 := bstep (se 1 (by rfl) ⟨2192801, by rfl⟩ : syracuseStep 2923735 = 4385603) B4385603
theorem B1154335 : Blo 1152637 1154335 := bstep (se 1 (by rfl) ⟨865751, by rfl⟩ : syracuseStep 1154335 = 1731503) B1731503
theorem B63282485 : Blo 1152637 63282485 := bstep (se 5 (by rfl) ⟨2966366, by rfl⟩ : syracuseStep 63282485 = 5932733) B5932733
theorem B1154395 : Blo 1152637 1154395 := bstep (se 1 (by rfl) ⟨865796, by rfl⟩ : syracuseStep 1154395 = 1731593) B1731593
theorem B2596193 : Blo 1152637 2596193 := bstep (se 2 (by rfl) ⟨973572, by rfl⟩ : syracuseStep 2596193 = 1947145) B1947145
theorem B1154415 : Blo 1152637 1154415 := bstep (se 1 (by rfl) ⟨865811, by rfl⟩ : syracuseStep 1154415 = 1731623) B1731623
theorem B1154471 : Blo 1152637 1154471 := bstep (se 1 (by rfl) ⟨865853, by rfl⟩ : syracuseStep 1154471 = 1731707) B1731707
theorem B2596283 : Blo 1152637 2596283 := bstep (se 1 (by rfl) ⟨1947212, by rfl⟩ : syracuseStep 2596283 = 3894425) B3894425
theorem B1154555 : Blo 1152637 1154555 := bstep (se 1 (by rfl) ⟨865916, by rfl⟩ : syracuseStep 1154555 = 1731833) B1731833
theorem B2924039 : Blo 1152637 2924039 := bstep (se 1 (by rfl) ⟨2193029, by rfl⟩ : syracuseStep 2924039 = 4386059) B4386059
theorem B2596409 : Blo 1152637 2596409 := bstep (se 2 (by rfl) ⟨973653, by rfl⟩ : syracuseStep 2596409 = 1947307) B1947307
theorem B1154623 : Blo 1152637 1154623 := bstep (se 1 (by rfl) ⟨865967, by rfl⟩ : syracuseStep 1154623 = 1731935) B1731935
theorem B1154631 : Blo 1152637 1154631 := bstep (se 1 (by rfl) ⟨865973, by rfl⟩ : syracuseStep 1154631 = 1731947) B1731947
theorem B1154783 : Blo 1152637 1154783 := bstep (se 1 (by rfl) ⟨866087, by rfl⟩ : syracuseStep 1154783 = 1732175) B1732175
theorem B3284783 : Blo 1152637 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B1154863 : Blo 1152637 1154863 := bstep (se 1 (by rfl) ⟨866147, by rfl⟩ : syracuseStep 1154863 = 1732295) B1732295
theorem B5840747 : Blo 1152637 5840747 := bstep (se 1 (by rfl) ⟨4380560, by rfl⟩ : syracuseStep 5840747 = 8761121) B8761121
theorem B1154971 : Blo 1152637 1154971 := bstep (se 1 (by rfl) ⟨866228, by rfl⟩ : syracuseStep 1154971 = 1732457) B1732457
theorem B44965813 : Blo 1152637 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B1155023 : Blo 1152637 1155023 := bstep (se 1 (by rfl) ⟨866267, by rfl⟩ : syracuseStep 1155023 = 1732535) B1732535
theorem B2924495 : Blo 1152637 2924495 := bstep (se 1 (by rfl) ⟨2193371, by rfl⟩ : syracuseStep 2924495 = 4386743) B4386743
theorem B1155047 : Blo 1152637 1155047 := bstep (se 1 (by rfl) ⟨866285, by rfl⟩ : syracuseStep 1155047 = 1732571) B1732571
theorem B2597075 : Blo 1152637 2597075 := bstep (se 1 (by rfl) ⟨1947806, by rfl⟩ : syracuseStep 2597075 = 3895613) B3895613
theorem B9871571 : Blo 1152637 9871571 := bstep (se 1 (by rfl) ⟨7403678, by rfl⟩ : syracuseStep 9871571 = 14807357) B14807357
theorem B2597129 : Blo 1152637 2597129 := bstep (se 2 (by rfl) ⟨973923, by rfl⟩ : syracuseStep 2597129 = 1947847) B1947847
theorem B1155359 : Blo 1152637 1155359 := bstep (se 1 (by rfl) ⟨866519, by rfl⟩ : syracuseStep 1155359 = 1733039) B1733039
theorem B1155419 : Blo 1152637 1155419 := bstep (se 1 (by rfl) ⟨866564, by rfl⟩ : syracuseStep 1155419 = 1733129) B1733129
theorem B1155439 : Blo 1152637 1155439 := bstep (se 1 (by rfl) ⟨866579, by rfl⟩ : syracuseStep 1155439 = 1733159) B1733159
theorem B1155495 : Blo 1152637 1155495 := bstep (se 1 (by rfl) ⟨866621, by rfl⟩ : syracuseStep 1155495 = 1733243) B1733243
theorem B2925011 : Blo 1152637 2925011 := bstep (se 1 (by rfl) ⟨2193758, by rfl⟩ : syracuseStep 2925011 = 4387517) B4387517
theorem B2597345 : Blo 1152637 2597345 := bstep (se 2 (by rfl) ⟨974004, by rfl⟩ : syracuseStep 2597345 = 1948009) B1948009
theorem B1155579 : Blo 1152637 1155579 := bstep (se 1 (by rfl) ⟨866684, by rfl⟩ : syracuseStep 1155579 = 1733369) B1733369
theorem B1155647 : Blo 1152637 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B1155655 : Blo 1152637 1155655 := bstep (se 1 (by rfl) ⟨866741, by rfl⟩ : syracuseStep 1155655 = 1733483) B1733483
theorem B6234745 : Blo 1152637 6234745 := bstep (se 2 (by rfl) ⟨2338029, by rfl⟩ : syracuseStep 6234745 = 4676059) B4676059
theorem B7905937 : Blo 1152637 7905937 := bstep (se 2 (by rfl) ⟨2964726, by rfl⟩ : syracuseStep 7905937 = 5929453) B5929453
theorem B3515051 : Blo 1152637 3515051 := bstep (se 1 (by rfl) ⟨2636288, by rfl⟩ : syracuseStep 3515051 = 5272577) B5272577
theorem B1155807 : Blo 1152637 1155807 := bstep (se 1 (by rfl) ⟨866855, by rfl⟩ : syracuseStep 1155807 = 1733711) B1733711
theorem B22160141 : Blo 1152637 22160141 := bstep (se 3 (by rfl) ⟨4155026, by rfl⟩ : syracuseStep 22160141 = 8310053) B8310053
theorem B2499347 : Blo 1152637 2499347 := bstep (se 1 (by rfl) ⟨1874510, by rfl⟩ : syracuseStep 2499347 = 3749021) B3749021
theorem B2597651 : Blo 1152637 2597651 := bstep (se 1 (by rfl) ⟨1948238, by rfl⟩ : syracuseStep 2597651 = 3896477) B3896477
theorem B1155887 : Blo 1152637 1155887 := bstep (se 1 (by rfl) ⟨866915, by rfl⟩ : syracuseStep 1155887 = 1733831) B1733831
theorem B2925467 : Blo 1152637 2925467 := bstep (se 1 (by rfl) ⟨2194100, by rfl⟩ : syracuseStep 2925467 = 4388201) B4388201
theorem B1155995 : Blo 1152637 1155995 := bstep (se 1 (by rfl) ⟨866996, by rfl⟩ : syracuseStep 1155995 = 1733993) B1733993
theorem B6661025 : Blo 1152637 6661025 := bstep (se 2 (by rfl) ⟨2497884, by rfl⟩ : syracuseStep 6661025 = 4995769) B4995769
theorem B2466731 : Blo 1152637 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B1156047 : Blo 1152637 1156047 := bstep (se 1 (by rfl) ⟨867035, by rfl⟩ : syracuseStep 1156047 = 1734071) B1734071
theorem B1156071 : Blo 1152637 1156071 := bstep (se 1 (by rfl) ⟨867053, by rfl⟩ : syracuseStep 1156071 = 1734107) B1734107
theorem B2598011 : Blo 1152637 2598011 := bstep (se 1 (by rfl) ⟨1948508, by rfl⟩ : syracuseStep 2598011 = 3897017) B3897017
theorem B2598137 : Blo 1152637 2598137 := bstep (se 2 (by rfl) ⟨974301, by rfl⟩ : syracuseStep 2598137 = 1948603) B1948603
theorem B1156383 : Blo 1152637 1156383 := bstep (se 1 (by rfl) ⟨867287, by rfl⟩ : syracuseStep 1156383 = 1734575) B1734575
theorem B1156443 : Blo 1152637 1156443 := bstep (se 1 (by rfl) ⟨867332, by rfl⟩ : syracuseStep 1156443 = 1734665) B1734665
theorem B1156463 : Blo 1152637 1156463 := bstep (se 1 (by rfl) ⟨867347, by rfl⟩ : syracuseStep 1156463 = 1734695) B1734695
theorem B2598281 : Blo 1152637 2598281 := bstep (se 2 (by rfl) ⟨974355, by rfl⟩ : syracuseStep 2598281 = 1948711) B1948711
theorem B1156519 : Blo 1152637 1156519 := bstep (se 1 (by rfl) ⟨867389, by rfl⟩ : syracuseStep 1156519 = 1734779) B1734779
theorem B2500039 : Blo 1152637 2500039 := bstep (se 1 (by rfl) ⟨1875029, by rfl⟩ : syracuseStep 2500039 = 3750059) B3750059
theorem B1156603 : Blo 1152637 1156603 := bstep (se 1 (by rfl) ⟨867452, by rfl⟩ : syracuseStep 1156603 = 1734905) B1734905
theorem B2598407 : Blo 1152637 2598407 := bstep (se 1 (by rfl) ⟨1948805, by rfl⟩ : syracuseStep 2598407 = 3897611) B3897611
theorem B2598587 : Blo 1152637 2598587 := bstep (se 1 (by rfl) ⟨1948940, by rfl⟩ : syracuseStep 2598587 = 3897881) B3897881
theorem B2598713 : Blo 1152637 2598713 := bstep (se 2 (by rfl) ⟨974517, by rfl⟩ : syracuseStep 2598713 = 1949035) B1949035
theorem B2926601 : Blo 1152637 2926601 := bstep (se 2 (by rfl) ⟨1097475, by rfl⟩ : syracuseStep 2926601 = 2194951) B2194951
theorem B9873485 : Blo 1152637 9873485 := bstep (se 3 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 9873485 = 3702557) B3702557
theorem B4925519 : Blo 1152637 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B4925569 : Blo 1152637 4925569 := bstep (se 2 (by rfl) ⟨1847088, by rfl⟩ : syracuseStep 4925569 = 3694177) B3694177
theorem B2926955 : Blo 1152637 2926955 := bstep (se 1 (by rfl) ⟨2195216, by rfl⟩ : syracuseStep 2926955 = 4390433) B4390433
theorem B8759663 : Blo 1152637 8759663 := bstep (se 1 (by rfl) ⟨6569747, by rfl⟩ : syracuseStep 8759663 = 13139495) B13139495
theorem B2599343 : Blo 1152637 2599343 := bstep (se 1 (by rfl) ⟨1949507, by rfl⟩ : syracuseStep 2599343 = 3899015) B3899015
theorem B2599379 : Blo 1152637 2599379 := bstep (se 1 (by rfl) ⟨1949534, by rfl⟩ : syracuseStep 2599379 = 3899069) B3899069
theorem B3123731 : Blo 1152637 3123731 := bstep (se 1 (by rfl) ⟨2342798, by rfl⟩ : syracuseStep 3123731 = 4685597) B4685597
theorem B2599487 : Blo 1152637 2599487 := bstep (se 1 (by rfl) ⟨1949615, by rfl⟩ : syracuseStep 2599487 = 3899231) B3899231
theorem B2599595 : Blo 1152637 2599595 := bstep (se 1 (by rfl) ⟨1949696, by rfl⟩ : syracuseStep 2599595 = 3899393) B3899393
theorem B2927279 : Blo 1152637 2927279 := bstep (se 1 (by rfl) ⟨2195459, by rfl⟩ : syracuseStep 2927279 = 4390919) B4390919
theorem B2927603 : Blo 1152637 2927603 := bstep (se 1 (by rfl) ⟨2195702, by rfl⟩ : syracuseStep 2927603 = 4391405) B4391405
theorem B9874547 : Blo 1152637 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B2600135 : Blo 1152637 2600135 := bstep (se 1 (by rfl) ⟨1950101, by rfl⟩ : syracuseStep 2600135 = 3900203) B3900203
theorem B1387739 : Blo 1152637 1387739 := bstep (se 1 (by rfl) ⟨1040804, by rfl⟩ : syracuseStep 1387739 = 2081609) B2081609
theorem B16035191 : Blo 1152637 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B2600315 : Blo 1152637 2600315 := bstep (se 1 (by rfl) ⟨1950236, by rfl⟩ : syracuseStep 2600315 = 3900473) B3900473
theorem B2567585 : Blo 1152637 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B5844473 : Blo 1152637 5844473 := bstep (se 2 (by rfl) ⟨2191677, by rfl⟩ : syracuseStep 5844473 = 4383355) B4383355
theorem B2600441 : Blo 1152637 2600441 := bstep (se 2 (by rfl) ⟨975165, by rfl⟩ : syracuseStep 2600441 = 1950331) B1950331
theorem B23703101 : Blo 1152637 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B2600531 : Blo 1152637 2600531 := bstep (se 1 (by rfl) ⟨1950398, by rfl⟩ : syracuseStep 2600531 = 3900797) B3900797
theorem B2600711 : Blo 1152637 2600711 := bstep (se 1 (by rfl) ⟨1950533, by rfl⟩ : syracuseStep 2600711 = 3901067) B3901067
theorem B4927243 : Blo 1152637 4927243 := bstep (se 1 (by rfl) ⟨3695432, by rfl⟩ : syracuseStep 4927243 = 7390865) B7390865
theorem B5844797 : Blo 1152637 5844797 := bstep (se 3 (by rfl) ⟨1095899, by rfl⟩ : syracuseStep 5844797 = 2191799) B2191799
theorem B13152617 : Blo 1152637 13152617 := bstep (se 2 (by rfl) ⟨4932231, by rfl⟩ : syracuseStep 13152617 = 9864463) B9864463
theorem B2601323 : Blo 1152637 2601323 := bstep (se 1 (by rfl) ⟨1950992, by rfl⟩ : syracuseStep 2601323 = 3901985) B3901985
theorem B2601467 : Blo 1152637 2601467 := bstep (se 1 (by rfl) ⟨1951100, by rfl⟩ : syracuseStep 2601467 = 3902201) B3902201
theorem B2601593 : Blo 1152637 2601593 := bstep (se 2 (by rfl) ⟨975597, by rfl⟩ : syracuseStep 2601593 = 1951195) B1951195
theorem B2601647 : Blo 1152637 2601647 := bstep (se 1 (by rfl) ⟨1951235, by rfl⟩ : syracuseStep 2601647 = 3902471) B3902471
theorem B1946335 : Blo 1152637 1946335 := bstep (se 1 (by rfl) ⟨1459751, by rfl⟩ : syracuseStep 1946335 = 2919503) B2919503
theorem B2601719 : Blo 1152637 2601719 := bstep (se 1 (by rfl) ⟨1951289, by rfl⟩ : syracuseStep 2601719 = 3902579) B3902579
theorem B11088683 : Blo 1152637 11088683 := bstep (se 1 (by rfl) ⟨8316512, by rfl⟩ : syracuseStep 11088683 = 16633025) B16633025
theorem B2601899 : Blo 1152637 2601899 := bstep (se 1 (by rfl) ⟨1951424, by rfl⟩ : syracuseStep 2601899 = 3902849) B3902849
theorem B1946767 : Blo 1152637 1946767 := bstep (se 1 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 1946767 = 2920151) B2920151
theorem B2340073 : Blo 1152637 2340073 := bstep (se 2 (by rfl) ⟨877527, by rfl⟩ : syracuseStep 2340073 = 1755055) B1755055
theorem B1947017 : Blo 1152637 1947017 := bstep (se 2 (by rfl) ⟨730131, by rfl⟩ : syracuseStep 1947017 = 1460263) B1460263
theorem B24032807 : Blo 1152637 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B8763065 : Blo 1152637 8763065 := bstep (se 2 (by rfl) ⟨3286149, by rfl⟩ : syracuseStep 8763065 = 6572299) B6572299
theorem B1947449 : Blo 1152637 1947449 := bstep (se 2 (by rfl) ⟨730293, by rfl⟩ : syracuseStep 1947449 = 1460587) B1460587
theorem B8764037 : Blo 1152637 8764037 := bstep (se 4 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 8764037 = 1643257) B1643257
theorem B12499595 : Blo 1152637 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B33340085 : Blo 1152637 33340085 := bstep (se 5 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 33340085 = 3125633) B3125633
theorem B5847875 : Blo 1152637 5847875 := bstep (se 1 (by rfl) ⟨4385906, by rfl⟩ : syracuseStep 5847875 = 8771813) B8771813
theorem B1948495 : Blo 1152637 1948495 := bstep (se 1 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 1948495 = 2922743) B2922743
theorem B2636999 : Blo 1152637 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B9878921 : Blo 1152637 9878921 := bstep (se 2 (by rfl) ⟨3704595, by rfl⟩ : syracuseStep 9878921 = 7409191) B7409191
theorem B1949177 : Blo 1152637 1949177 := bstep (se 2 (by rfl) ⟨730941, by rfl⟩ : syracuseStep 1949177 = 1461883) B1461883
theorem B8765009 : Blo 1152637 8765009 := bstep (se 2 (by rfl) ⟨3286878, by rfl⟩ : syracuseStep 8765009 = 6573757) B6573757
theorem B5848685 : Blo 1152637 5848685 := bstep (se 3 (by rfl) ⟨1096628, by rfl⟩ : syracuseStep 5848685 = 2193257) B2193257
theorem B1949447 : Blo 1152637 1949447 := bstep (se 1 (by rfl) ⟨1462085, by rfl⟩ : syracuseStep 1949447 = 2924171) B2924171
theorem B5783471 : Blo 1152637 5783471 := bstep (se 1 (by rfl) ⟨4337603, by rfl⟩ : syracuseStep 5783471 = 8675207) B8675207
theorem B3293531 : Blo 1152637 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B9847241 : Blo 1152637 9847241 := bstep (se 2 (by rfl) ⟨3692715, by rfl⟩ : syracuseStep 9847241 = 7385431) B7385431
theorem B1950203 : Blo 1152637 1950203 := bstep (se 1 (by rfl) ⟨1462652, by rfl⟩ : syracuseStep 1950203 = 2925305) B2925305
theorem B22495927 : Blo 1152637 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B1458911 : Blo 1152637 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B1950635 : Blo 1152637 1950635 := bstep (se 1 (by rfl) ⟨1462976, by rfl⟩ : syracuseStep 1950635 = 2925953) B2925953
theorem B8766467 : Blo 1152637 8766467 := bstep (se 1 (by rfl) ⟨6574850, by rfl⟩ : syracuseStep 8766467 = 13149701) B13149701
theorem B4277447 : Blo 1152637 4277447 := bstep (se 1 (by rfl) ⟨3208085, by rfl⟩ : syracuseStep 4277447 = 6416171) B6416171
theorem B1754399 : Blo 1152637 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B112543019 : Blo 1152637 112543019 := bstep (se 1 (by rfl) ⟨84407264, by rfl⟩ : syracuseStep 112543019 = 168814529) B168814529
theorem B4441439 : Blo 1152637 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B2770375 : Blo 1152637 2770375 := bstep (se 1 (by rfl) ⟨2077781, by rfl⟩ : syracuseStep 2770375 = 4155563) B4155563
theorem B1951175 : Blo 1152637 1951175 := bstep (se 1 (by rfl) ⟨1463381, by rfl⟩ : syracuseStep 1951175 = 2926763) B2926763
theorem B8767439 : Blo 1152637 8767439 := bstep (se 1 (by rfl) ⟨6575579, by rfl⟩ : syracuseStep 8767439 = 13151159) B13151159
theorem B3950777 : Blo 1152637 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B1296751 : Blo 1152637 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B1296967 : Blo 1152637 1296967 := bstep (se 1 (by rfl) ⟨972725, by rfl⟩ : syracuseStep 1296967 = 1945451) B1945451
theorem B4934267 : Blo 1152637 4934267 := bstep (se 1 (by rfl) ⟨3700700, by rfl⟩ : syracuseStep 4934267 = 7401401) B7401401
theorem B1460911 : Blo 1152637 1460911 := bstep (se 1 (by rfl) ⟨1095683, by rfl⟩ : syracuseStep 1460911 = 2191367) B2191367
theorem B6245039 : Blo 1152637 6245039 := bstep (se 1 (by rfl) ⟨4683779, by rfl⟩ : syracuseStep 6245039 = 9367559) B9367559
theorem B2083511 : Blo 1152637 2083511 := bstep (se 1 (by rfl) ⟨1562633, by rfl⟩ : syracuseStep 2083511 = 3125267) B3125267
theorem B31607981 : Blo 1152637 31607981 := bstep (se 3 (by rfl) ⟨5926496, by rfl⟩ : syracuseStep 31607981 = 11852993) B11852993
theorem B24005879 : Blo 1152637 24005879 := bstep (se 1 (by rfl) ⟨18004409, by rfl⟩ : syracuseStep 24005879 = 36008819) B36008819
theorem B8310113 : Blo 1152637 8310113 := bstep (se 2 (by rfl) ⟨3116292, by rfl⟩ : syracuseStep 8310113 = 6232585) B6232585
theorem B8768897 : Blo 1152637 8768897 := bstep (se 2 (by rfl) ⟨3288336, by rfl⟩ : syracuseStep 8768897 = 6576673) B6576673
theorem B1297831 : Blo 1152637 1297831 := bstep (se 1 (by rfl) ⟨973373, by rfl⟩ : syracuseStep 1297831 = 1946747) B1946747
theorem B50580935 : Blo 1152637 50580935 := bstep (se 1 (by rfl) ⟨37935701, by rfl⟩ : syracuseStep 50580935 = 75871403) B75871403
theorem B1298407 : Blo 1152637 1298407 := bstep (se 1 (by rfl) ⟨973805, by rfl⟩ : syracuseStep 1298407 = 1947611) B1947611
theorem B6574283 : Blo 1152637 6574283 := bstep (se 1 (by rfl) ⟨4930712, by rfl⟩ : syracuseStep 6574283 = 9861425) B9861425
theorem B1233191 : Blo 1152637 1233191 := bstep (se 1 (by rfl) ⟨924893, by rfl⟩ : syracuseStep 1233191 = 1849787) B1849787
theorem B48648509 : Blo 1152637 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B1233263 : Blo 1152637 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B35508725 : Blo 1152637 35508725 := bstep (se 5 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 35508725 = 3328943) B3328943
theorem B1462855 : Blo 1152637 1462855 := bstep (se 1 (by rfl) ⟨1097141, by rfl⟩ : syracuseStep 1462855 = 2194283) B2194283
theorem B6247115 : Blo 1152637 6247115 := bstep (se 1 (by rfl) ⟨4685336, by rfl⟩ : syracuseStep 6247115 = 9370673) B9370673
theorem B9851615 : Blo 1152637 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B5854031 : Blo 1152637 5854031 := bstep (se 1 (by rfl) ⟨4390523, by rfl⟩ : syracuseStep 5854031 = 8781047) B8781047
theorem B23712787 : Blo 1152637 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B7394429 : Blo 1152637 7394429 := bstep (se 3 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 7394429 = 2772911) B2772911
theorem B5854355 : Blo 1152637 5854355 := bstep (se 1 (by rfl) ⟨4390766, by rfl⟩ : syracuseStep 5854355 = 8781533) B8781533
theorem B9852299 : Blo 1152637 9852299 := bstep (se 1 (by rfl) ⟨7389224, by rfl⟩ : syracuseStep 9852299 = 14778449) B14778449
theorem B5264801 : Blo 1152637 5264801 := bstep (se 2 (by rfl) ⟨1974300, by rfl⟩ : syracuseStep 5264801 = 3948601) B3948601
theorem B1300063 : Blo 1152637 1300063 := bstep (se 1 (by rfl) ⟨975047, by rfl⟩ : syracuseStep 1300063 = 1950095) B1950095
theorem B4380925 : Blo 1152637 4380925 := bstep (se 3 (by rfl) ⟨821423, by rfl⟩ : syracuseStep 4380925 = 1642847) B1642847
theorem B6248933 : Blo 1152637 6248933 := bstep (se 4 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 6248933 = 1171675) B1171675
theorem B11262503 : Blo 1152637 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B1301215 : Blo 1152637 1301215 := bstep (se 1 (by rfl) ⟨975911, by rfl⟩ : syracuseStep 1301215 = 1951823) B1951823
theorem B20011961 : Blo 1152637 20011961 := bstep (se 2 (by rfl) ⟨7504485, by rfl⟩ : syracuseStep 20011961 = 15008971) B15008971
theorem B9854075 : Blo 1152637 9854075 := bstep (se 1 (by rfl) ⟨7390556, by rfl⟩ : syracuseStep 9854075 = 14781113) B14781113
theorem B2776457 : Blo 1152637 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B4382201 : Blo 1152637 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B24927905 : Blo 1152637 24927905 := bstep (se 2 (by rfl) ⟨9347964, by rfl⟩ : syracuseStep 24927905 = 18695929) B18695929
theorem B4382369 : Blo 1152637 4382369 := bstep (se 2 (by rfl) ⟨1643388, by rfl⟩ : syracuseStep 4382369 = 3286777) B3286777
theorem B13164281 : Blo 1152637 13164281 := bstep (se 2 (by rfl) ⟨4936605, by rfl⟩ : syracuseStep 13164281 = 9873211) B9873211
theorem B4939649 : Blo 1152637 4939649 := bstep (se 2 (by rfl) ⟨1852368, by rfl⟩ : syracuseStep 4939649 = 3704737) B3704737
theorem B3891563 : Blo 1152637 3891563 := bstep (se 1 (by rfl) ⟨2918672, by rfl⟩ : syracuseStep 3891563 = 5837345) B5837345
theorem B6578657 : Blo 1152637 6578657 := bstep (se 2 (by rfl) ⟨2466996, by rfl⟩ : syracuseStep 6578657 = 4933993) B4933993
theorem B1729019 : Blo 1152637 1729019 := bstep (se 1 (by rfl) ⟨1296764, by rfl⟩ : syracuseStep 1729019 = 2593529) B2593529
theorem B1729145 : Blo 1152637 1729145 := bstep (se 2 (by rfl) ⟨648429, by rfl⟩ : syracuseStep 1729145 = 1296859) B1296859
theorem B3891833 : Blo 1152637 3891833 := bstep (se 2 (by rfl) ⟨1459437, by rfl⟩ : syracuseStep 3891833 = 2918875) B2918875
theorem B1729199 : Blo 1152637 1729199 := bstep (se 1 (by rfl) ⟨1296899, by rfl⟩ : syracuseStep 1729199 = 2593799) B2593799
theorem B1729247 : Blo 1152637 1729247 := bstep (se 1 (by rfl) ⟨1296935, by rfl⟩ : syracuseStep 1729247 = 2593871) B2593871
theorem B1729511 : Blo 1152637 1729511 := bstep (se 1 (by rfl) ⟨1297133, by rfl⟩ : syracuseStep 1729511 = 2594267) B2594267
theorem B4383841 : Blo 1152637 4383841 := bstep (se 2 (by rfl) ⟨1643940, by rfl⟩ : syracuseStep 4383841 = 3287881) B3287881
theorem B1729769 : Blo 1152637 1729769 := bstep (se 2 (by rfl) ⟨648663, by rfl⟩ : syracuseStep 1729769 = 1297327) B1297327
theorem B1729823 : Blo 1152637 1729823 := bstep (se 1 (by rfl) ⟨1297367, by rfl⟩ : syracuseStep 1729823 = 2594735) B2594735
theorem B4449725 : Blo 1152637 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B1729991 : Blo 1152637 1729991 := bstep (se 1 (by rfl) ⟨1297493, by rfl⟩ : syracuseStep 1729991 = 2594987) B2594987
theorem B4384313 : Blo 1152637 4384313 := bstep (se 2 (by rfl) ⟨1644117, by rfl⟩ : syracuseStep 4384313 = 3288235) B3288235
theorem B2188883 : Blo 1152637 2188883 := bstep (se 1 (by rfl) ⟨1641662, by rfl⟩ : syracuseStep 2188883 = 3283325) B3283325
theorem B2189035 : Blo 1152637 2189035 := bstep (se 1 (by rfl) ⟨1641776, by rfl⟩ : syracuseStep 2189035 = 3283553) B3283553
theorem B1730345 : Blo 1152637 1730345 := bstep (se 2 (by rfl) ⟨648879, by rfl⟩ : syracuseStep 1730345 = 1297759) B1297759
theorem B1730351 : Blo 1152637 1730351 := bstep (se 1 (by rfl) ⟨1297763, by rfl⟩ : syracuseStep 1730351 = 2595527) B2595527
theorem B2189263 : Blo 1152637 2189263 := bstep (se 1 (by rfl) ⟨1641947, by rfl⟩ : syracuseStep 2189263 = 3283895) B3283895
theorem B23685209 : Blo 1152637 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B1730825 : Blo 1152637 1730825 := bstep (se 2 (by rfl) ⟨649059, by rfl⟩ : syracuseStep 1730825 = 1298119) B1298119
theorem B4155677 : Blo 1152637 4155677 := bstep (se 3 (by rfl) ⟨779189, by rfl⟩ : syracuseStep 4155677 = 1558379) B1558379
theorem B10545437 : Blo 1152637 10545437 := bstep (se 3 (by rfl) ⟨1977269, by rfl⟩ : syracuseStep 10545437 = 3954539) B3954539
theorem B3893615 : Blo 1152637 3893615 := bstep (se 1 (by rfl) ⟨2920211, by rfl⟩ : syracuseStep 3893615 = 5840423) B5840423
theorem B1730927 : Blo 1152637 1730927 := bstep (se 1 (by rfl) ⟨1298195, by rfl⟩ : syracuseStep 1730927 = 2596391) B2596391
theorem B1731143 : Blo 1152637 1731143 := bstep (se 1 (by rfl) ⟨1298357, by rfl⟩ : syracuseStep 1731143 = 2596715) B2596715
theorem B1731179 : Blo 1152637 1731179 := bstep (se 1 (by rfl) ⟨1298384, by rfl⟩ : syracuseStep 1731179 = 2596769) B2596769
theorem B2190007 : Blo 1152637 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B568519397 : Blo 1152637 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B1731407 : Blo 1152637 1731407 := bstep (se 1 (by rfl) ⟨1298555, by rfl⟩ : syracuseStep 1731407 = 2597111) B2597111
theorem B2190235 : Blo 1152637 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B2190311 : Blo 1152637 2190311 := bstep (se 1 (by rfl) ⟨1642733, by rfl⟩ : syracuseStep 2190311 = 3285467) B3285467
theorem B1731803 : Blo 1152637 1731803 := bstep (se 1 (by rfl) ⟨1298852, by rfl⟩ : syracuseStep 1731803 = 2597705) B2597705
theorem B1731977 : Blo 1152637 1731977 := bstep (se 2 (by rfl) ⟨649491, by rfl⟩ : syracuseStep 1731977 = 1298983) B1298983
theorem B8777159 : Blo 1152637 8777159 := bstep (se 1 (by rfl) ⟨6582869, by rfl⟩ : syracuseStep 8777159 = 13165739) B13165739
theorem B3895019 : Blo 1152637 3895019 := bstep (se 1 (by rfl) ⟨2921264, by rfl⟩ : syracuseStep 3895019 = 5842529) B5842529
theorem B1732331 : Blo 1152637 1732331 := bstep (se 1 (by rfl) ⟨1299248, by rfl⟩ : syracuseStep 1732331 = 2598497) B2598497
theorem B1732559 : Blo 1152637 1732559 := bstep (se 1 (by rfl) ⟨1299419, by rfl⟩ : syracuseStep 1732559 = 2598839) B2598839
theorem B3698713 : Blo 1152637 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B2191465 : Blo 1152637 2191465 := bstep (se 2 (by rfl) ⟨821799, by rfl⟩ : syracuseStep 2191465 = 1643599) B1643599
theorem B1732955 : Blo 1152637 1732955 := bstep (se 1 (by rfl) ⟨1299716, by rfl⟩ : syracuseStep 1732955 = 2599433) B2599433
theorem B8319451 : Blo 1152637 8319451 := bstep (se 1 (by rfl) ⟨6239588, by rfl⟩ : syracuseStep 8319451 = 12479177) B12479177
theorem B1733183 : Blo 1152637 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B3895991 : Blo 1152637 3895991 := bstep (se 1 (by rfl) ⟨2921993, by rfl⟩ : syracuseStep 3895991 = 5843987) B5843987
theorem B1733303 : Blo 1152637 1733303 := bstep (se 1 (by rfl) ⟨1299977, by rfl⟩ : syracuseStep 1733303 = 2599955) B2599955
theorem B1733531 : Blo 1152637 1733531 := bstep (se 1 (by rfl) ⟨1300148, by rfl⟩ : syracuseStep 1733531 = 2600297) B2600297
theorem B1733927 : Blo 1152637 1733927 := bstep (se 1 (by rfl) ⟨1300445, by rfl⟩ : syracuseStep 1733927 = 2600891) B2600891
theorem B8779103 : Blo 1152637 8779103 := bstep (se 1 (by rfl) ⟨6584327, by rfl⟩ : syracuseStep 8779103 = 13168655) B13168655
theorem B1734011 : Blo 1152637 1734011 := bstep (se 1 (by rfl) ⟨1300508, by rfl⟩ : syracuseStep 1734011 = 2601017) B2601017
theorem B7402913 : Blo 1152637 7402913 := bstep (se 2 (by rfl) ⟨2776092, by rfl⟩ : syracuseStep 7402913 = 5552185) B5552185
theorem B1734137 : Blo 1152637 1734137 := bstep (se 2 (by rfl) ⟨650301, by rfl⟩ : syracuseStep 1734137 = 1300603) B1300603
theorem B1734239 : Blo 1152637 1734239 := bstep (se 1 (by rfl) ⟨1300679, by rfl⟩ : syracuseStep 1734239 = 2601359) B2601359
theorem B1734455 : Blo 1152637 1734455 := bstep (se 1 (by rfl) ⟨1300841, by rfl⟩ : syracuseStep 1734455 = 2601683) B2601683
theorem B1734761 : Blo 1152637 1734761 := bstep (se 2 (by rfl) ⟨650535, by rfl⟩ : syracuseStep 1734761 = 1301071) B1301071
theorem B12024247 : Blo 1152637 12024247 := bstep (se 1 (by rfl) ⟨9018185, by rfl⟩ : syracuseStep 12024247 = 18036371) B18036371
theorem B3897935 : Blo 1152637 3897935 := bstep (se 1 (by rfl) ⟨2923451, by rfl⟩ : syracuseStep 3897935 = 5846903) B5846903
theorem B9862073 : Blo 1152637 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B4684787 : Blo 1152637 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B7012001 : Blo 1152637 7012001 := bstep (se 2 (by rfl) ⟨2629500, by rfl⟩ : syracuseStep 7012001 = 5259001) B5259001
theorem B68386481 : Blo 1152637 68386481 := bstep (se 2 (by rfl) ⟨25644930, by rfl⟩ : syracuseStep 68386481 = 51289861) B51289861
theorem B7405319 : Blo 1152637 7405319 := bstep (se 1 (by rfl) ⟨5553989, by rfl⟩ : syracuseStep 7405319 = 11107979) B11107979
theorem B3899177 : Blo 1152637 3899177 := bstep (se 2 (by rfl) ⟨1462191, by rfl⟩ : syracuseStep 3899177 = 2924383) B2924383
theorem B2195255 : Blo 1152637 2195255 := bstep (se 1 (by rfl) ⟨1646441, by rfl⟩ : syracuseStep 2195255 = 3292883) B3292883
theorem B3997927 : Blo 1152637 3997927 := bstep (se 1 (by rfl) ⟨2998445, by rfl⟩ : syracuseStep 3997927 = 5996891) B5996891
theorem B2195687 : Blo 1152637 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B2851631 : Blo 1152637 2851631 := bstep (se 1 (by rfl) ⟨2138723, by rfl⟩ : syracuseStep 2851631 = 4277447) B4277447
theorem B13502315 : Blo 1152637 13502315 := bstep (se 1 (by rfl) ⟨10126736, by rfl⟩ : syracuseStep 13502315 = 20253473) B20253473
theorem B21071987 : Blo 1152637 21071987 := bstep (se 1 (by rfl) ⟨15803990, by rfl⟩ : syracuseStep 21071987 = 31607981) B31607981
theorem B5540075 : Blo 1152637 5540075 := bstep (se 1 (by rfl) ⟨4155056, by rfl⟩ : syracuseStep 5540075 = 8310113) B8310113
theorem B33720623 : Blo 1152637 33720623 := bstep (se 1 (by rfl) ⟨25290467, by rfl⟩ : syracuseStep 33720623 = 50580935) B50580935
theorem B2918713 : Blo 1152637 2918713 := bstep (se 2 (by rfl) ⟨1094517, by rfl⟩ : syracuseStep 2918713 = 2189035) B2189035
theorem B2919017 : Blo 1152637 2919017 := bstep (se 2 (by rfl) ⟨1094631, by rfl⟩ : syracuseStep 2919017 = 2189263) B2189263
theorem B4164743 : Blo 1152637 4164743 := bstep (se 1 (by rfl) ⟨3123557, by rfl⟩ : syracuseStep 4164743 = 6247115) B6247115
theorem B3902687 : Blo 1152637 3902687 := bstep (se 1 (by rfl) ⟨2927015, by rfl⟩ : syracuseStep 3902687 = 5854031) B5854031
theorem B3902903 : Blo 1152637 3902903 := bstep (se 1 (by rfl) ⟨2927177, by rfl⟩ : syracuseStep 3902903 = 5854355) B5854355
theorem B2920009 : Blo 1152637 2920009 := bstep (se 2 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 2920009 = 2190007) B2190007
theorem B3509867 : Blo 1152637 3509867 := bstep (se 1 (by rfl) ⟨2632400, by rfl⟩ : syracuseStep 3509867 = 5264801) B5264801
theorem B2920313 : Blo 1152637 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B5837021 : Blo 1152637 5837021 := bstep (se 3 (by rfl) ⟨1094441, by rfl⟩ : syracuseStep 5837021 = 2188883) B2188883
theorem B4165955 : Blo 1152637 4165955 := bstep (se 1 (by rfl) ⟨3124466, by rfl⟩ : syracuseStep 4165955 = 6248933) B6248933
theorem B5837183 : Blo 1152637 5837183 := bstep (se 1 (by rfl) ⟨4377887, by rfl⟩ : syracuseStep 5837183 = 8755775) B8755775
theorem B2921467 : Blo 1152637 2921467 := bstep (se 1 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 2921467 = 4382201) B4382201
theorem B16618603 : Blo 1152637 16618603 := bstep (se 1 (by rfl) ⟨12463952, by rfl⟩ : syracuseStep 16618603 = 24927905) B24927905
theorem B2921579 : Blo 1152637 2921579 := bstep (se 1 (by rfl) ⟨2191184, by rfl⟩ : syracuseStep 2921579 = 4382369) B4382369
theorem B2921953 : Blo 1152637 2921953 := bstep (se 2 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 2921953 = 2191465) B2191465
theorem B2594375 : Blo 1152637 2594375 := bstep (se 1 (by rfl) ⟨1945781, by rfl⟩ : syracuseStep 2594375 = 3891563) B3891563
theorem B1152679 : Blo 1152637 1152679 := bstep (se 1 (by rfl) ⟨864509, by rfl⟩ : syracuseStep 1152679 = 1729019) B1729019
theorem B1152763 : Blo 1152637 1152763 := bstep (se 1 (by rfl) ⟨864572, by rfl⟩ : syracuseStep 1152763 = 1729145) B1729145
theorem B2594555 : Blo 1152637 2594555 := bstep (se 1 (by rfl) ⟨1945916, by rfl⟩ : syracuseStep 2594555 = 3891833) B3891833
theorem B1152799 : Blo 1152637 1152799 := bstep (se 1 (by rfl) ⟨864599, by rfl⟩ : syracuseStep 1152799 = 1729199) B1729199
theorem B1152831 : Blo 1152637 1152831 := bstep (se 1 (by rfl) ⟨864623, by rfl⟩ : syracuseStep 1152831 = 1729247) B1729247
theorem B1153007 : Blo 1152637 1153007 := bstep (se 1 (by rfl) ⟨864755, by rfl⟩ : syracuseStep 1153007 = 1729511) B1729511
theorem B28121165 : Blo 1152637 28121165 := bstep (se 3 (by rfl) ⟨5272718, by rfl⟩ : syracuseStep 28121165 = 10545437) B10545437
theorem B1153179 : Blo 1152637 1153179 := bstep (se 1 (by rfl) ⟨864884, by rfl⟩ : syracuseStep 1153179 = 1729769) B1729769
theorem B1153215 : Blo 1152637 1153215 := bstep (se 1 (by rfl) ⟨864911, by rfl⟩ : syracuseStep 1153215 = 1729823) B1729823
theorem B2595113 : Blo 1152637 2595113 := bstep (se 2 (by rfl) ⟨973167, by rfl⟩ : syracuseStep 2595113 = 1946335) B1946335
theorem B1153327 : Blo 1152637 1153327 := bstep (se 1 (by rfl) ⟨864995, by rfl⟩ : syracuseStep 1153327 = 1729991) B1729991
theorem B2922875 : Blo 1152637 2922875 := bstep (se 1 (by rfl) ⟨2192156, by rfl⟩ : syracuseStep 2922875 = 4384313) B4384313
theorem B1153563 : Blo 1152637 1153563 := bstep (se 1 (by rfl) ⟨865172, by rfl⟩ : syracuseStep 1153563 = 1730345) B1730345
theorem B1153567 : Blo 1152637 1153567 := bstep (se 1 (by rfl) ⟨865175, by rfl⟩ : syracuseStep 1153567 = 1730351) B1730351
theorem B8329949 : Blo 1152637 8329949 := bstep (se 3 (by rfl) ⟨1561865, by rfl⟩ : syracuseStep 8329949 = 3123731) B3123731
theorem B3283679 : Blo 1152637 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B1153883 : Blo 1152637 1153883 := bstep (se 1 (by rfl) ⟨865412, by rfl⟩ : syracuseStep 1153883 = 1730825) B1730825
theorem B2595689 : Blo 1152637 2595689 := bstep (se 2 (by rfl) ⟨973383, by rfl⟩ : syracuseStep 2595689 = 1946767) B1946767
theorem B5839775 : Blo 1152637 5839775 := bstep (se 1 (by rfl) ⟨4379831, by rfl⟩ : syracuseStep 5839775 = 8759663) B8759663
theorem B2595743 : Blo 1152637 2595743 := bstep (se 1 (by rfl) ⟨1946807, by rfl⟩ : syracuseStep 2595743 = 3893615) B3893615
theorem B1153951 : Blo 1152637 1153951 := bstep (se 1 (by rfl) ⟨865463, by rfl⟩ : syracuseStep 1153951 = 1730927) B1730927
theorem B3284009 : Blo 1152637 3284009 := bstep (se 2 (by rfl) ⟨1231503, by rfl⟩ : syracuseStep 3284009 = 2463007) B2463007
theorem B1154095 : Blo 1152637 1154095 := bstep (se 1 (by rfl) ⟨865571, by rfl⟩ : syracuseStep 1154095 = 1731143) B1731143
theorem B1154119 : Blo 1152637 1154119 := bstep (se 1 (by rfl) ⟨865589, by rfl⟩ : syracuseStep 1154119 = 1731179) B1731179
theorem B16653437 : Blo 1152637 16653437 := bstep (se 3 (by rfl) ⟨3122519, by rfl⟩ : syracuseStep 16653437 = 6245039) B6245039
theorem B1154271 : Blo 1152637 1154271 := bstep (se 1 (by rfl) ⟨865703, by rfl⟩ : syracuseStep 1154271 = 1731407) B1731407
theorem B1154535 : Blo 1152637 1154535 := bstep (se 1 (by rfl) ⟨865901, by rfl⟩ : syracuseStep 1154535 = 1731803) B1731803
theorem B10690127 : Blo 1152637 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B1154651 : Blo 1152637 1154651 := bstep (se 1 (by rfl) ⟨865988, by rfl⟩ : syracuseStep 1154651 = 1731977) B1731977
theorem B15802067 : Blo 1152637 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B2596679 : Blo 1152637 2596679 := bstep (se 1 (by rfl) ⟨1947509, by rfl⟩ : syracuseStep 2596679 = 3895019) B3895019
theorem B1154887 : Blo 1152637 1154887 := bstep (se 1 (by rfl) ⟨866165, by rfl⟩ : syracuseStep 1154887 = 1732331) B1732331
theorem B1155039 : Blo 1152637 1155039 := bstep (se 1 (by rfl) ⟨866279, by rfl⟩ : syracuseStep 1155039 = 1732559) B1732559
theorem B1155303 : Blo 1152637 1155303 := bstep (se 1 (by rfl) ⟨866477, by rfl⟩ : syracuseStep 1155303 = 1732955) B1732955
theorem B5841233 : Blo 1152637 5841233 := bstep (se 2 (by rfl) ⟨2190462, by rfl⟩ : syracuseStep 5841233 = 4380925) B4380925
theorem B1155455 : Blo 1152637 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B2597327 : Blo 1152637 2597327 := bstep (se 1 (by rfl) ⟨1947995, by rfl⟩ : syracuseStep 2597327 = 3895991) B3895991
theorem B1155535 : Blo 1152637 1155535 := bstep (se 1 (by rfl) ⟨866651, by rfl⟩ : syracuseStep 1155535 = 1733303) B1733303
theorem B16032329 : Blo 1152637 16032329 := bstep (se 2 (by rfl) ⟨6012123, by rfl⟩ : syracuseStep 16032329 = 12024247) B12024247
theorem B1155687 : Blo 1152637 1155687 := bstep (se 1 (by rfl) ⟨866765, by rfl⟩ : syracuseStep 1155687 = 1733531) B1733531
theorem B1155951 : Blo 1152637 1155951 := bstep (se 1 (by rfl) ⟨866963, by rfl⟩ : syracuseStep 1155951 = 1733927) B1733927
theorem B1156007 : Blo 1152637 1156007 := bstep (se 1 (by rfl) ⟨867005, by rfl⟩ : syracuseStep 1156007 = 1734011) B1734011
theorem B1156091 : Blo 1152637 1156091 := bstep (se 1 (by rfl) ⟨867068, by rfl⟩ : syracuseStep 1156091 = 1734137) B1734137
theorem B1156159 : Blo 1152637 1156159 := bstep (se 1 (by rfl) ⟨867119, by rfl⟩ : syracuseStep 1156159 = 1734239) B1734239
theorem B2597993 : Blo 1152637 2597993 := bstep (se 2 (by rfl) ⟨974247, by rfl⟩ : syracuseStep 2597993 = 1948495) B1948495
theorem B5842043 : Blo 1152637 5842043 := bstep (se 1 (by rfl) ⟨4381532, by rfl⟩ : syracuseStep 5842043 = 8763065) B8763065
theorem B1156303 : Blo 1152637 1156303 := bstep (se 1 (by rfl) ⟨867227, by rfl⟩ : syracuseStep 1156303 = 1734455) B1734455
theorem B1156507 : Blo 1152637 1156507 := bstep (se 1 (by rfl) ⟨867380, by rfl⟩ : syracuseStep 1156507 = 1734761) B1734761
theorem B2598623 : Blo 1152637 2598623 := bstep (se 1 (by rfl) ⟨1948967, by rfl⟩ : syracuseStep 2598623 = 3897935) B3897935
theorem B5842691 : Blo 1152637 5842691 := bstep (se 1 (by rfl) ⟨4382018, by rfl⟩ : syracuseStep 5842691 = 8764037) B8764037
theorem B8333063 : Blo 1152637 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B22226723 : Blo 1152637 22226723 := bstep (se 1 (by rfl) ⟨16670042, by rfl⟩ : syracuseStep 22226723 = 33340085) B33340085
theorem B3123191 : Blo 1152637 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B5843339 : Blo 1152637 5843339 := bstep (se 1 (by rfl) ⟨4382504, by rfl⟩ : syracuseStep 5843339 = 8765009) B8765009
theorem B45590987 : Blo 1152637 45590987 := bstep (se 1 (by rfl) ⟨34193240, by rfl⟩ : syracuseStep 45590987 = 68386481) B68386481
theorem B2599451 : Blo 1152637 2599451 := bstep (se 1 (by rfl) ⟨1949588, by rfl⟩ : syracuseStep 2599451 = 3899177) B3899177
theorem B6564827 : Blo 1152637 6564827 := bstep (se 1 (by rfl) ⟨4923620, by rfl⟩ : syracuseStep 6564827 = 9847241) B9847241
theorem B5844311 : Blo 1152637 5844311 := bstep (se 1 (by rfl) ⟨4383233, by rfl⟩ : syracuseStep 5844311 = 8766467) B8766467
theorem B3288509 : Blo 1152637 3288509 := bstep (se 3 (by rfl) ⟨616595, by rfl⟩ : syracuseStep 3288509 = 1233191) B1233191
theorem B3124727 : Blo 1152637 3124727 := bstep (se 1 (by rfl) ⟨2343545, by rfl⟩ : syracuseStep 3124727 = 4687091) B4687091
theorem B2960959 : Blo 1152637 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B29994569 : Blo 1152637 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B3288701 : Blo 1152637 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B5844959 : Blo 1152637 5844959 := bstep (se 1 (by rfl) ⟨4383719, by rfl⟩ : syracuseStep 5844959 = 8767439) B8767439
theorem B2600927 : Blo 1152637 2600927 := bstep (se 1 (by rfl) ⟨1950695, by rfl⟩ : syracuseStep 2600927 = 3901391) B3901391
theorem B2633851 : Blo 1152637 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B5845121 : Blo 1152637 5845121 := bstep (se 2 (by rfl) ⟨2191920, by rfl⟩ : syracuseStep 5845121 = 4383841) B4383841
theorem B3289511 : Blo 1152637 3289511 := bstep (se 1 (by rfl) ⟨2467133, by rfl⟩ : syracuseStep 3289511 = 4934267) B4934267
theorem B1389007 : Blo 1152637 1389007 := bstep (se 1 (by rfl) ⟨1041755, by rfl⟩ : syracuseStep 1389007 = 2083511) B2083511
theorem B1946207 : Blo 1152637 1946207 := bstep (se 1 (by rfl) ⟨1459655, by rfl⟩ : syracuseStep 1946207 = 2919311) B2919311
theorem B2601575 : Blo 1152637 2601575 := bstep (se 1 (by rfl) ⟨1951181, by rfl⟩ : syracuseStep 2601575 = 3902363) B3902363
theorem B6664925 : Blo 1152637 6664925 := bstep (se 3 (by rfl) ⟨1249673, by rfl⟩ : syracuseStep 6664925 = 2499347) B2499347
theorem B5550839 : Blo 1152637 5550839 := bstep (se 1 (by rfl) ⟨4163129, by rfl⟩ : syracuseStep 5550839 = 8326259) B8326259
theorem B3126023 : Blo 1152637 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B16003919 : Blo 1152637 16003919 := bstep (se 1 (by rfl) ⟨12002939, by rfl⟩ : syracuseStep 16003919 = 24005879) B24005879
theorem B11383723 : Blo 1152637 11383723 := bstep (se 1 (by rfl) ⟨8537792, by rfl⟩ : syracuseStep 11383723 = 17075585) B17075585
theorem B5845931 : Blo 1152637 5845931 := bstep (se 1 (by rfl) ⟨4384448, by rfl⟩ : syracuseStep 5845931 = 8768897) B8768897
theorem B2077903 : Blo 1152637 2077903 := bstep (se 1 (by rfl) ⟨1558427, by rfl⟩ : syracuseStep 2077903 = 3116855) B3116855
theorem B2602259 : Blo 1152637 2602259 := bstep (se 1 (by rfl) ⟨1951694, by rfl⟩ : syracuseStep 2602259 = 3903389) B3903389
theorem B2602331 : Blo 1152637 2602331 := bstep (se 1 (by rfl) ⟨1951748, by rfl⟩ : syracuseStep 2602331 = 3903497) B3903497
theorem B6567425 : Blo 1152637 6567425 := bstep (se 2 (by rfl) ⟨2462784, by rfl⟩ : syracuseStep 6567425 = 4925569) B4925569
theorem B23672483 : Blo 1152637 23672483 := bstep (se 1 (by rfl) ⟨17754362, by rfl⟩ : syracuseStep 23672483 = 35508725) B35508725
theorem B6567743 : Blo 1152637 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B1947631 : Blo 1152637 1947631 := bstep (se 1 (by rfl) ⟨1460723, by rfl⟩ : syracuseStep 1947631 = 2921447) B2921447
theorem B4929619 : Blo 1152637 4929619 := bstep (se 1 (by rfl) ⟨3697214, by rfl⟩ : syracuseStep 4929619 = 7394429) B7394429
theorem B1947881 : Blo 1152637 1947881 := bstep (se 2 (by rfl) ⟨730455, by rfl⟩ : syracuseStep 1947881 = 1460911) B1460911
theorem B6568199 : Blo 1152637 6568199 := bstep (se 1 (by rfl) ⟨4926149, by rfl⟩ : syracuseStep 6568199 = 9852299) B9852299
theorem B6569383 : Blo 1152637 6569383 := bstep (se 1 (by rfl) ⟨4927037, by rfl⟩ : syracuseStep 6569383 = 9854075) B9854075
theorem B42188323 : Blo 1152637 42188323 := bstep (se 1 (by rfl) ⟨31641242, by rfl⟩ : syracuseStep 42188323 = 63282485) B63282485
theorem B1949359 : Blo 1152637 1949359 := bstep (se 1 (by rfl) ⟨1462019, by rfl⟩ : syracuseStep 1949359 = 2924039) B2924039
theorem B6569657 : Blo 1152637 6569657 := bstep (se 2 (by rfl) ⟨2463621, by rfl⟩ : syracuseStep 6569657 = 4927243) B4927243
theorem B3293099 : Blo 1152637 3293099 := bstep (se 1 (by rfl) ⟨2469824, by rfl⟩ : syracuseStep 3293099 = 4939649) B4939649
theorem B1949663 : Blo 1152637 1949663 := bstep (se 1 (by rfl) ⟨1462247, by rfl⟩ : syracuseStep 1949663 = 2924495) B2924495
theorem B4931617 : Blo 1152637 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B1950007 : Blo 1152637 1950007 := bstep (se 1 (by rfl) ⟨1462505, by rfl⟩ : syracuseStep 1950007 = 2925011) B2925011
theorem B2343367 : Blo 1152637 2343367 := bstep (se 1 (by rfl) ⟨1757525, by rfl⟩ : syracuseStep 2343367 = 3515051) B3515051
theorem B1950311 : Blo 1152637 1950311 := bstep (se 1 (by rfl) ⟨1462733, by rfl⟩ : syracuseStep 1950311 = 2925467) B2925467
theorem B4440683 : Blo 1152637 4440683 := bstep (se 1 (by rfl) ⟨3330512, by rfl⟩ : syracuseStep 4440683 = 6661025) B6661025
theorem B11092601 : Blo 1152637 11092601 := bstep (se 2 (by rfl) ⟨4159725, by rfl⟩ : syracuseStep 11092601 = 8319451) B8319451
theorem B1950473 : Blo 1152637 1950473 := bstep (se 2 (by rfl) ⟨731427, by rfl⟩ : syracuseStep 1950473 = 1462855) B1462855
theorem B2966483 : Blo 1152637 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B8439041 : Blo 1152637 8439041 := bstep (se 2 (by rfl) ⟨3164640, by rfl⟩ : syracuseStep 8439041 = 6329281) B6329281
theorem B1951067 : Blo 1152637 1951067 := bstep (se 1 (by rfl) ⟨1463300, by rfl⟩ : syracuseStep 1951067 = 2926601) B2926601
theorem B30033341 : Blo 1152637 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B2770451 : Blo 1152637 2770451 := bstep (se 1 (by rfl) ⟨2077838, by rfl⟩ : syracuseStep 2770451 = 4155677) B4155677
theorem B1951303 : Blo 1152637 1951303 := bstep (se 1 (by rfl) ⟨1463477, by rfl⟩ : syracuseStep 1951303 = 2926955) B2926955
theorem B1951519 : Blo 1152637 1951519 := bstep (se 1 (by rfl) ⟨1463639, by rfl⟩ : syracuseStep 1951519 = 2927279) B2927279
theorem B379012931 : Blo 1152637 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B1460207 : Blo 1152637 1460207 := bstep (se 1 (by rfl) ⟨1095155, by rfl⟩ : syracuseStep 1460207 = 2190311) B2190311
theorem B1951735 : Blo 1152637 1951735 := bstep (se 1 (by rfl) ⟨1463801, by rfl⟩ : syracuseStep 1951735 = 2927603) B2927603
theorem B13158449 : Blo 1152637 13158449 := bstep (se 2 (by rfl) ⟨4934418, by rfl⟩ : syracuseStep 13158449 = 9868837) B9868837
theorem B4376825 : Blo 1152637 4376825 := bstep (se 2 (by rfl) ⟨1641309, by rfl⟩ : syracuseStep 4376825 = 3282619) B3282619
theorem B5851439 : Blo 1152637 5851439 := bstep (se 1 (by rfl) ⟨4388579, by rfl⟩ : syracuseStep 5851439 = 8777159) B8777159
theorem B53365229 : Blo 1152637 53365229 := bstep (se 3 (by rfl) ⟨10005980, by rfl⟩ : syracuseStep 53365229 = 20011961) B20011961
theorem B8768411 : Blo 1152637 8768411 := bstep (se 1 (by rfl) ⟨6576308, by rfl⟩ : syracuseStep 8768411 = 13152617) B13152617
theorem B7392455 : Blo 1152637 7392455 := bstep (se 1 (by rfl) ⟨5544341, by rfl⟩ : syracuseStep 7392455 = 11088683) B11088683
theorem B5852735 : Blo 1152637 5852735 := bstep (se 1 (by rfl) ⟨4389551, by rfl⟩ : syracuseStep 5852735 = 8779103) B8779103
theorem B1298011 : Blo 1152637 1298011 := bstep (se 1 (by rfl) ⟨973508, by rfl⟩ : syracuseStep 1298011 = 1947017) B1947017
theorem B4935275 : Blo 1152637 4935275 := bstep (se 1 (by rfl) ⟨3701456, by rfl⟩ : syracuseStep 4935275 = 7402913) B7402913
theorem B1298299 : Blo 1152637 1298299 := bstep (se 1 (by rfl) ⟨973724, by rfl⟩ : syracuseStep 1298299 = 1947449) B1947449
theorem B6574715 : Blo 1152637 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B1757999 : Blo 1152637 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B4379453 : Blo 1152637 4379453 := bstep (se 3 (by rfl) ⟨821147, by rfl⟩ : syracuseStep 4379453 = 1642295) B1642295
theorem B1299451 : Blo 1152637 1299451 := bstep (se 1 (by rfl) ⟨974588, by rfl⟩ : syracuseStep 1299451 = 1949177) B1949177
theorem B4674667 : Blo 1152637 4674667 := bstep (se 1 (by rfl) ⟨3506000, by rfl⟩ : syracuseStep 4674667 = 7012001) B7012001
theorem B1299631 : Blo 1152637 1299631 := bstep (se 1 (by rfl) ⟨974723, by rfl⟩ : syracuseStep 1299631 = 1949447) B1949447
theorem B4936879 : Blo 1152637 4936879 := bstep (se 1 (by rfl) ⟨3702659, by rfl⟩ : syracuseStep 4936879 = 7405319) B7405319
theorem B1463503 : Blo 1152637 1463503 := bstep (se 1 (by rfl) ⟨1097627, by rfl⟩ : syracuseStep 1463503 = 2195255) B2195255
theorem B59954417 : Blo 1152637 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B3855647 : Blo 1152637 3855647 := bstep (se 1 (by rfl) ⟨2891735, by rfl⟩ : syracuseStep 3855647 = 5783471) B5783471
theorem B4937051 : Blo 1152637 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B1300135 : Blo 1152637 1300135 := bstep (se 1 (by rfl) ⟨975101, by rfl⟩ : syracuseStep 1300135 = 1950203) B1950203
theorem B1300423 : Blo 1152637 1300423 := bstep (se 1 (by rfl) ⟨975317, by rfl⟩ : syracuseStep 1300423 = 1950635) B1950635
theorem B37410821 : Blo 1152637 37410821 := bstep (se 4 (by rfl) ⟨3507264, by rfl⟩ : syracuseStep 37410821 = 7014529) B7014529
theorem B7886915 : Blo 1152637 7886915 := bstep (se 1 (by rfl) ⟨5915186, by rfl⟩ : syracuseStep 7886915 = 11830373) B11830373
theorem B5855327 : Blo 1152637 5855327 := bstep (se 1 (by rfl) ⟨4391495, by rfl⟩ : syracuseStep 5855327 = 8782991) B8782991
theorem B8312993 : Blo 1152637 8312993 := bstep (se 2 (by rfl) ⟨3117372, by rfl⟩ : syracuseStep 8312993 = 6234745) B6234745
theorem B10541249 : Blo 1152637 10541249 := bstep (se 2 (by rfl) ⟨3952968, by rfl⟩ : syracuseStep 10541249 = 7905937) B7905937
theorem B75028679 : Blo 1152637 75028679 := bstep (se 1 (by rfl) ⟨56271509, by rfl⟩ : syracuseStep 75028679 = 112543019) B112543019
theorem B10148125 : Blo 1152637 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B1300783 : Blo 1152637 1300783 := bstep (se 1 (by rfl) ⟨975587, by rfl⟩ : syracuseStep 1300783 = 1951175) B1951175
theorem B6576491 : Blo 1152637 6576491 := bstep (se 1 (by rfl) ⟨4932368, by rfl⟩ : syracuseStep 6576491 = 9864737) B9864737
theorem B31545881 : Blo 1152637 31545881 := bstep (se 2 (by rfl) ⟨11829705, by rfl⟩ : syracuseStep 31545881 = 23659411) B23659411
theorem B3890429 : Blo 1152637 3890429 := bstep (se 3 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 3890429 = 1458911) B1458911
theorem B3693833 : Blo 1152637 3693833 := bstep (se 2 (by rfl) ⟨1385187, by rfl⟩ : syracuseStep 3693833 = 2770375) B2770375
theorem B6577949 : Blo 1152637 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B3891239 : Blo 1152637 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B4382855 : Blo 1152637 4382855 := bstep (se 1 (by rfl) ⟨3287141, by rfl⟩ : syracuseStep 4382855 = 6574283) B6574283
theorem B32432339 : Blo 1152637 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B4940023 : Blo 1152637 4940023 := bstep (se 1 (by rfl) ⟨3705017, by rfl⟩ : syracuseStep 4940023 = 7410035) B7410035
theorem B1729001 : Blo 1152637 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B1729127 : Blo 1152637 1729127 := bstep (se 1 (by rfl) ⟨1296845, by rfl⟩ : syracuseStep 1729127 = 2593691) B2593691
theorem B4383341 : Blo 1152637 4383341 := bstep (se 3 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 4383341 = 1643753) B1643753
theorem B3891887 : Blo 1152637 3891887 := bstep (se 1 (by rfl) ⟨2918915, by rfl⟩ : syracuseStep 3891887 = 5837831) B5837831
theorem B1729259 : Blo 1152637 1729259 := bstep (se 1 (by rfl) ⟨1296944, by rfl⟩ : syracuseStep 1729259 = 2593889) B2593889
theorem B4678397 : Blo 1152637 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B1729289 : Blo 1152637 1729289 := bstep (se 2 (by rfl) ⟨648483, by rfl⟩ : syracuseStep 1729289 = 1296967) B1296967
theorem B1729391 : Blo 1152637 1729391 := bstep (se 1 (by rfl) ⟨1297043, by rfl⟩ : syracuseStep 1729391 = 2594087) B2594087
theorem B3892211 : Blo 1152637 3892211 := bstep (se 1 (by rfl) ⟨2919158, by rfl⟩ : syracuseStep 3892211 = 5838317) B5838317
theorem B1729643 : Blo 1152637 1729643 := bstep (se 1 (by rfl) ⟨1297232, by rfl⟩ : syracuseStep 1729643 = 2594465) B2594465
theorem B6579407 : Blo 1152637 6579407 := bstep (se 1 (by rfl) ⟨4934555, by rfl⟩ : syracuseStep 6579407 = 9869111) B9869111
theorem B1729883 : Blo 1152637 1729883 := bstep (se 1 (by rfl) ⟨1297412, by rfl⟩ : syracuseStep 1729883 = 2594825) B2594825
theorem B3892751 : Blo 1152637 3892751 := bstep (se 1 (by rfl) ⟨2919563, by rfl⟩ : syracuseStep 3892751 = 5839127) B5839127
theorem B1730159 : Blo 1152637 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B1730231 : Blo 1152637 1730231 := bstep (se 1 (by rfl) ⟨1297673, by rfl⟩ : syracuseStep 1730231 = 2595347) B2595347
theorem B1730267 : Blo 1152637 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B1730441 : Blo 1152637 1730441 := bstep (se 2 (by rfl) ⟨648915, by rfl⟩ : syracuseStep 1730441 = 1297831) B1297831
theorem B1730543 : Blo 1152637 1730543 := bstep (se 1 (by rfl) ⟨1297907, by rfl⟩ : syracuseStep 1730543 = 2595815) B2595815
theorem B1730795 : Blo 1152637 1730795 := bstep (se 1 (by rfl) ⟨1298096, by rfl⟩ : syracuseStep 1730795 = 2596193) B2596193
theorem B1730855 : Blo 1152637 1730855 := bstep (se 1 (by rfl) ⟨1298141, by rfl⟩ : syracuseStep 1730855 = 2596283) B2596283
theorem B3893561 : Blo 1152637 3893561 := bstep (se 2 (by rfl) ⟨1460085, by rfl⟩ : syracuseStep 3893561 = 2920171) B2920171
theorem B1730939 : Blo 1152637 1730939 := bstep (se 1 (by rfl) ⟨1298204, by rfl⟩ : syracuseStep 1730939 = 2596409) B2596409
theorem B8776187 : Blo 1152637 8776187 := bstep (se 1 (by rfl) ⟨6582140, by rfl⟩ : syracuseStep 8776187 = 13164281) B13164281
theorem B2189855 : Blo 1152637 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B3893831 : Blo 1152637 3893831 := bstep (se 1 (by rfl) ⟨2920373, by rfl⟩ : syracuseStep 3893831 = 5840747) B5840747
theorem B1731209 : Blo 1152637 1731209 := bstep (se 2 (by rfl) ⟨649203, by rfl⟩ : syracuseStep 1731209 = 1298407) B1298407
theorem B1731383 : Blo 1152637 1731383 := bstep (se 1 (by rfl) ⟨1298537, by rfl⟩ : syracuseStep 1731383 = 2597075) B2597075
theorem B6581047 : Blo 1152637 6581047 := bstep (se 1 (by rfl) ⟨4935785, by rfl⟩ : syracuseStep 6581047 = 9871571) B9871571
theorem B1731419 : Blo 1152637 1731419 := bstep (se 1 (by rfl) ⟨1298564, by rfl⟩ : syracuseStep 1731419 = 2597129) B2597129
theorem B1731563 : Blo 1152637 1731563 := bstep (se 1 (by rfl) ⟨1298672, by rfl⟩ : syracuseStep 1731563 = 2597345) B2597345
theorem B4385771 : Blo 1152637 4385771 := bstep (se 1 (by rfl) ⟨3289328, by rfl⟩ : syracuseStep 4385771 = 6578657) B6578657
theorem B14773427 : Blo 1152637 14773427 := bstep (se 1 (by rfl) ⟨11080070, by rfl⟩ : syracuseStep 14773427 = 22160141) B22160141
theorem B1731767 : Blo 1152637 1731767 := bstep (se 1 (by rfl) ⟨1298825, by rfl⟩ : syracuseStep 1731767 = 2597651) B2597651
theorem B11103641 : Blo 1152637 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B1732007 : Blo 1152637 1732007 := bstep (se 1 (by rfl) ⟨1299005, by rfl⟩ : syracuseStep 1732007 = 2598011) B2598011
theorem B1732091 : Blo 1152637 1732091 := bstep (se 1 (by rfl) ⟨1299068, by rfl⟩ : syracuseStep 1732091 = 2598137) B2598137
theorem B3894857 : Blo 1152637 3894857 := bstep (se 2 (by rfl) ⟨1460571, by rfl⟩ : syracuseStep 3894857 = 2921143) B2921143
theorem B1732187 : Blo 1152637 1732187 := bstep (se 1 (by rfl) ⟨1299140, by rfl⟩ : syracuseStep 1732187 = 2598281) B2598281
theorem B1732271 : Blo 1152637 1732271 := bstep (se 1 (by rfl) ⟨1299203, by rfl⟩ : syracuseStep 1732271 = 2598407) B2598407
theorem B1732391 : Blo 1152637 1732391 := bstep (se 1 (by rfl) ⟨1299293, by rfl⟩ : syracuseStep 1732391 = 2598587) B2598587
theorem B1732475 : Blo 1152637 1732475 := bstep (se 1 (by rfl) ⟨1299356, by rfl⟩ : syracuseStep 1732475 = 2598713) B2598713
theorem B12480389 : Blo 1152637 12480389 := bstep (se 4 (by rfl) ⟨1170036, by rfl⟩ : syracuseStep 12480389 = 2340073) B2340073
theorem B31617049 : Blo 1152637 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B6582323 : Blo 1152637 6582323 := bstep (se 1 (by rfl) ⟨4936742, by rfl⟩ : syracuseStep 6582323 = 9873485) B9873485
theorem B15790139 : Blo 1152637 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B1732895 : Blo 1152637 1732895 := bstep (se 1 (by rfl) ⟨1299671, by rfl⟩ : syracuseStep 1732895 = 2599343) B2599343
theorem B1732919 : Blo 1152637 1732919 := bstep (se 1 (by rfl) ⟨1299689, by rfl⟩ : syracuseStep 1732919 = 2599379) B2599379
theorem B1732991 : Blo 1152637 1732991 := bstep (se 1 (by rfl) ⟨1299743, by rfl⟩ : syracuseStep 1732991 = 2599487) B2599487
theorem B1733063 : Blo 1152637 1733063 := bstep (se 1 (by rfl) ⟨1299797, by rfl⟩ : syracuseStep 1733063 = 2599595) B2599595
theorem B6583031 : Blo 1152637 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B1733417 : Blo 1152637 1733417 := bstep (se 2 (by rfl) ⟨650031, by rfl⟩ : syracuseStep 1733417 = 1300063) B1300063
theorem B1733423 : Blo 1152637 1733423 := bstep (se 1 (by rfl) ⟨1300067, by rfl⟩ : syracuseStep 1733423 = 2600135) B2600135
theorem B1733543 : Blo 1152637 1733543 := bstep (se 1 (by rfl) ⟨1300157, by rfl⟩ : syracuseStep 1733543 = 2600315) B2600315
theorem B3896315 : Blo 1152637 3896315 := bstep (se 1 (by rfl) ⟨2922236, by rfl⟩ : syracuseStep 3896315 = 5844473) B5844473
theorem B1733627 : Blo 1152637 1733627 := bstep (se 1 (by rfl) ⟨1300220, by rfl⟩ : syracuseStep 1733627 = 2600441) B2600441
theorem B13333541 : Blo 1152637 13333541 := bstep (se 4 (by rfl) ⟨1250019, by rfl⟩ : syracuseStep 13333541 = 2500039) B2500039
theorem B1733687 : Blo 1152637 1733687 := bstep (se 1 (by rfl) ⟨1300265, by rfl⟩ : syracuseStep 1733687 = 2600531) B2600531
theorem B1733807 : Blo 1152637 1733807 := bstep (se 1 (by rfl) ⟨1300355, by rfl⟩ : syracuseStep 1733807 = 2600711) B2600711
theorem B3896531 : Blo 1152637 3896531 := bstep (se 1 (by rfl) ⟨2922398, by rfl⟩ : syracuseStep 3896531 = 5844797) B5844797
theorem B3896801 : Blo 1152637 3896801 := bstep (se 2 (by rfl) ⟨1461300, by rfl⟩ : syracuseStep 3896801 = 2922601) B2922601
theorem B1734215 : Blo 1152637 1734215 := bstep (se 1 (by rfl) ⟨1300661, by rfl⟩ : syracuseStep 1734215 = 2601323) B2601323
theorem B9369245 : Blo 1152637 9369245 := bstep (se 3 (by rfl) ⟨1756733, by rfl⟩ : syracuseStep 9369245 = 3513467) B3513467
theorem B1734311 : Blo 1152637 1734311 := bstep (se 1 (by rfl) ⟨1300733, by rfl⟩ : syracuseStep 1734311 = 2601467) B2601467
theorem B1734395 : Blo 1152637 1734395 := bstep (se 1 (by rfl) ⟨1300796, by rfl⟩ : syracuseStep 1734395 = 2601593) B2601593
theorem B1734431 : Blo 1152637 1734431 := bstep (se 1 (by rfl) ⟨1300823, by rfl⟩ : syracuseStep 1734431 = 2601647) B2601647
theorem B1734479 : Blo 1152637 1734479 := bstep (se 1 (by rfl) ⟨1300859, by rfl⟩ : syracuseStep 1734479 = 2601719) B2601719
theorem B3700637 : Blo 1152637 3700637 := bstep (se 3 (by rfl) ⟨693869, by rfl⟩ : syracuseStep 3700637 = 1387739) B1387739
theorem B1734599 : Blo 1152637 1734599 := bstep (se 1 (by rfl) ⟨1300949, by rfl⟩ : syracuseStep 1734599 = 2601899) B2601899
theorem B3897449 : Blo 1152637 3897449 := bstep (se 2 (by rfl) ⟨1461543, by rfl⟩ : syracuseStep 3897449 = 2923087) B2923087
theorem B1734953 : Blo 1152637 1734953 := bstep (se 2 (by rfl) ⟨650607, by rfl⟩ : syracuseStep 1734953 = 1301215) B1301215
theorem B7403885 : Blo 1152637 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B16021871 : Blo 1152637 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B6846893 : Blo 1152637 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B3898313 : Blo 1152637 3898313 := bstep (se 2 (by rfl) ⟨1461867, by rfl⟩ : syracuseStep 3898313 = 2923735) B2923735
theorem B3898583 : Blo 1152637 3898583 := bstep (se 1 (by rfl) ⟨2923937, by rfl⟩ : syracuseStep 3898583 = 5847875) B5847875
theorem B81100061 : Blo 1152637 81100061 := bstep (se 3 (by rfl) ⟨15206261, by rfl⟩ : syracuseStep 81100061 = 30412523) B30412523
theorem B6585947 : Blo 1152637 6585947 := bstep (se 1 (by rfl) ⟨4939460, by rfl⟩ : syracuseStep 6585947 = 9878921) B9878921
theorem B3899123 : Blo 1152637 3899123 := bstep (se 1 (by rfl) ⟨2924342, by rfl⟩ : syracuseStep 3899123 = 5848685) B5848685
theorem B6586697 : Blo 1152637 6586697 := bstep (se 2 (by rfl) ⟨2470011, by rfl⟩ : syracuseStep 6586697 = 4940023) B4940023
theorem B1901087 : Blo 1152637 1901087 := bstep (se 1 (by rfl) ⟨1425815, by rfl⟩ : syracuseStep 1901087 = 2851631) B2851631
theorem B20022227 : Blo 1152637 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B252675287 : Blo 1152637 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B2917883 : Blo 1152637 2917883 := bstep (se 1 (by rfl) ⟨2188412, by rfl⟩ : syracuseStep 2917883 = 4376825) B4376825
theorem B22480415 : Blo 1152637 22480415 := bstep (se 1 (by rfl) ⟨16860311, by rfl⟩ : syracuseStep 22480415 = 33720623) B33720623
theorem B3900959 : Blo 1152637 3900959 := bstep (se 1 (by rfl) ⟨2925719, by rfl⟩ : syracuseStep 3900959 = 5851439) B5851439
theorem B3901823 : Blo 1152637 3901823 := bstep (se 1 (by rfl) ⟨2926367, by rfl⟩ : syracuseStep 3901823 = 5852735) B5852735
theorem B7408037 : Blo 1152637 7408037 := bstep (se 4 (by rfl) ⟨694503, by rfl⟩ : syracuseStep 7408037 = 1389007) B1389007
theorem B2919635 : Blo 1152637 2919635 := bstep (se 1 (by rfl) ⟨2189726, by rfl⟩ : syracuseStep 2919635 = 4379453) B4379453
theorem B24940547 : Blo 1152637 24940547 := bstep (se 1 (by rfl) ⟨18705410, by rfl⟩ : syracuseStep 24940547 = 37410821) B37410821
theorem B18747443 : Blo 1152637 18747443 := bstep (se 1 (by rfl) ⟨14060582, by rfl⟩ : syracuseStep 18747443 = 28121165) B28121165
theorem B3903551 : Blo 1152637 3903551 := bstep (se 1 (by rfl) ⟨2927663, by rfl⟩ : syracuseStep 3903551 = 5855327) B5855327
theorem B5541995 : Blo 1152637 5541995 := bstep (se 1 (by rfl) ⟨4156496, by rfl⟩ : syracuseStep 5541995 = 8312993) B8312993
theorem B2593619 : Blo 1152637 2593619 := bstep (se 1 (by rfl) ⟨1945214, by rfl⟩ : syracuseStep 2593619 = 3890429) B3890429
theorem B2462555 : Blo 1152637 2462555 := bstep (se 1 (by rfl) ⟨1846916, by rfl⟩ : syracuseStep 2462555 = 3693833) B3693833
theorem B2594159 : Blo 1152637 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B2921903 : Blo 1152637 2921903 := bstep (se 1 (by rfl) ⟨2191427, by rfl⟩ : syracuseStep 2921903 = 4382855) B4382855
theorem B3511801 : Blo 1152637 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B1152667 : Blo 1152637 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B10688219 : Blo 1152637 10688219 := bstep (se 1 (by rfl) ⟨8016164, by rfl⟩ : syracuseStep 10688219 = 16032329) B16032329
theorem B1152751 : Blo 1152637 1152751 := bstep (se 1 (by rfl) ⟨864563, by rfl⟩ : syracuseStep 1152751 = 1729127) B1729127
theorem B2922227 : Blo 1152637 2922227 := bstep (se 1 (by rfl) ⟨2191670, by rfl⟩ : syracuseStep 2922227 = 4383341) B4383341
theorem B2594591 : Blo 1152637 2594591 := bstep (se 1 (by rfl) ⟨1945943, by rfl⟩ : syracuseStep 2594591 = 3891887) B3891887
theorem B1152839 : Blo 1152637 1152839 := bstep (se 1 (by rfl) ⟨864629, by rfl⟩ : syracuseStep 1152839 = 1729259) B1729259
theorem B3118931 : Blo 1152637 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B1152859 : Blo 1152637 1152859 := bstep (se 1 (by rfl) ⟨864644, by rfl⟩ : syracuseStep 1152859 = 1729289) B1729289
theorem B1152927 : Blo 1152637 1152927 := bstep (se 1 (by rfl) ⟨864695, by rfl⟩ : syracuseStep 1152927 = 1729391) B1729391
theorem B2594807 : Blo 1152637 2594807 := bstep (se 1 (by rfl) ⟨1946105, by rfl⟩ : syracuseStep 2594807 = 3892211) B3892211
theorem B1153095 : Blo 1152637 1153095 := bstep (se 1 (by rfl) ⟨864821, by rfl⟩ : syracuseStep 1153095 = 1729643) B1729643
theorem B1153255 : Blo 1152637 1153255 := bstep (se 1 (by rfl) ⟨864941, by rfl⟩ : syracuseStep 1153255 = 1729883) B1729883
theorem B2595167 : Blo 1152637 2595167 := bstep (se 1 (by rfl) ⟨1946375, by rfl⟩ : syracuseStep 2595167 = 3892751) B3892751
theorem B1153439 : Blo 1152637 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B1153487 : Blo 1152637 1153487 := bstep (se 1 (by rfl) ⟨865115, by rfl⟩ : syracuseStep 1153487 = 1730231) B1730231
theorem B1153511 : Blo 1152637 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B14817815 : Blo 1152637 14817815 := bstep (se 1 (by rfl) ⟨11113361, by rfl⟩ : syracuseStep 14817815 = 22226723) B22226723
theorem B1153627 : Blo 1152637 1153627 := bstep (se 1 (by rfl) ⟨865220, by rfl⟩ : syracuseStep 1153627 = 1730441) B1730441
theorem B1153695 : Blo 1152637 1153695 := bstep (se 1 (by rfl) ⟨865271, by rfl⟩ : syracuseStep 1153695 = 1730543) B1730543
theorem B5839613 : Blo 1152637 5839613 := bstep (se 3 (by rfl) ⟨1094927, by rfl⟩ : syracuseStep 5839613 = 2189855) B2189855
theorem B22158137 : Blo 1152637 22158137 := bstep (se 2 (by rfl) ⟨8309301, by rfl⟩ : syracuseStep 22158137 = 16618603) B16618603
theorem B6232889 : Blo 1152637 6232889 := bstep (se 2 (by rfl) ⟨2337333, by rfl⟩ : syracuseStep 6232889 = 4674667) B4674667
theorem B1153863 : Blo 1152637 1153863 := bstep (se 1 (by rfl) ⟨865397, by rfl⟩ : syracuseStep 1153863 = 1730795) B1730795
theorem B1153903 : Blo 1152637 1153903 := bstep (se 1 (by rfl) ⟨865427, by rfl⟩ : syracuseStep 1153903 = 1730855) B1730855
theorem B2595707 : Blo 1152637 2595707 := bstep (se 1 (by rfl) ⟨1946780, by rfl⟩ : syracuseStep 2595707 = 3893561) B3893561
theorem B1153959 : Blo 1152637 1153959 := bstep (se 1 (by rfl) ⟨865469, by rfl⟩ : syracuseStep 1153959 = 1730939) B1730939
theorem B2595887 : Blo 1152637 2595887 := bstep (se 1 (by rfl) ⟨1946915, by rfl⟩ : syracuseStep 2595887 = 3893831) B3893831
theorem B1154139 : Blo 1152637 1154139 := bstep (se 1 (by rfl) ⟨865604, by rfl⟩ : syracuseStep 1154139 = 1731209) B1731209
theorem B1154255 : Blo 1152637 1154255 := bstep (se 1 (by rfl) ⟨865691, by rfl⟩ : syracuseStep 1154255 = 1731383) B1731383
theorem B1154279 : Blo 1152637 1154279 := bstep (se 1 (by rfl) ⟨865709, by rfl⟩ : syracuseStep 1154279 = 1731419) B1731419
theorem B1154375 : Blo 1152637 1154375 := bstep (se 1 (by rfl) ⟨865781, by rfl⟩ : syracuseStep 1154375 = 1731563) B1731563
theorem B2923847 : Blo 1152637 2923847 := bstep (se 1 (by rfl) ⟨2192885, by rfl⟩ : syracuseStep 2923847 = 4385771) B4385771
theorem B1154511 : Blo 1152637 1154511 := bstep (se 1 (by rfl) ⟨865883, by rfl⟩ : syracuseStep 1154511 = 1731767) B1731767
theorem B1154671 : Blo 1152637 1154671 := bstep (se 1 (by rfl) ⟨866003, by rfl⟩ : syracuseStep 1154671 = 1732007) B1732007
theorem B1154727 : Blo 1152637 1154727 := bstep (se 1 (by rfl) ⟨866045, by rfl⟩ : syracuseStep 1154727 = 1732091) B1732091
theorem B2596571 : Blo 1152637 2596571 := bstep (se 1 (by rfl) ⟨1947428, by rfl⟩ : syracuseStep 2596571 = 3894857) B3894857
theorem B19996379 : Blo 1152637 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B1154791 : Blo 1152637 1154791 := bstep (se 1 (by rfl) ⟨866093, by rfl⟩ : syracuseStep 1154791 = 1732187) B1732187
theorem B1154847 : Blo 1152637 1154847 := bstep (se 1 (by rfl) ⟨866135, by rfl⟩ : syracuseStep 1154847 = 1732271) B1732271
theorem B1154927 : Blo 1152637 1154927 := bstep (se 1 (by rfl) ⟨866195, by rfl⟩ : syracuseStep 1154927 = 1732391) B1732391
theorem B1154983 : Blo 1152637 1154983 := bstep (se 1 (by rfl) ⟨866237, by rfl⟩ : syracuseStep 1154983 = 1732475) B1732475
theorem B2596841 : Blo 1152637 2596841 := bstep (se 2 (by rfl) ⟨973815, by rfl⟩ : syracuseStep 2596841 = 1947631) B1947631
theorem B10526759 : Blo 1152637 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B1155263 : Blo 1152637 1155263 := bstep (se 1 (by rfl) ⟨866447, by rfl⟩ : syracuseStep 1155263 = 1732895) B1732895
theorem B1155279 : Blo 1152637 1155279 := bstep (se 1 (by rfl) ⟨866459, by rfl⟩ : syracuseStep 1155279 = 1732919) B1732919
theorem B1155327 : Blo 1152637 1155327 := bstep (se 1 (by rfl) ⟨866495, by rfl⟩ : syracuseStep 1155327 = 1732991) B1732991
theorem B1155375 : Blo 1152637 1155375 := bstep (se 1 (by rfl) ⟨866531, by rfl⟩ : syracuseStep 1155375 = 1733063) B1733063
theorem B1155611 : Blo 1152637 1155611 := bstep (se 1 (by rfl) ⟨866708, by rfl⟩ : syracuseStep 1155611 = 1733417) B1733417
theorem B1155615 : Blo 1152637 1155615 := bstep (se 1 (by rfl) ⟨866711, by rfl⟩ : syracuseStep 1155615 = 1733423) B1733423
theorem B1155695 : Blo 1152637 1155695 := bstep (se 1 (by rfl) ⟨866771, by rfl⟩ : syracuseStep 1155695 = 1733543) B1733543
theorem B2597543 : Blo 1152637 2597543 := bstep (se 1 (by rfl) ⟨1948157, by rfl⟩ : syracuseStep 2597543 = 3896315) B3896315
theorem B1155751 : Blo 1152637 1155751 := bstep (se 1 (by rfl) ⟨866813, by rfl⟩ : syracuseStep 1155751 = 1733627) B1733627
theorem B1155791 : Blo 1152637 1155791 := bstep (se 1 (by rfl) ⟨866843, by rfl⟩ : syracuseStep 1155791 = 1733687) B1733687
theorem B1155871 : Blo 1152637 1155871 := bstep (se 1 (by rfl) ⟨866903, by rfl⟩ : syracuseStep 1155871 = 1733807) B1733807
theorem B2597687 : Blo 1152637 2597687 := bstep (se 1 (by rfl) ⟨1948265, by rfl⟩ : syracuseStep 2597687 = 3896531) B3896531
theorem B2597867 : Blo 1152637 2597867 := bstep (se 1 (by rfl) ⟨1948400, by rfl⟩ : syracuseStep 2597867 = 3896801) B3896801
theorem B1156143 : Blo 1152637 1156143 := bstep (se 1 (by rfl) ⟨867107, by rfl⟩ : syracuseStep 1156143 = 1734215) B1734215
theorem B1156207 : Blo 1152637 1156207 := bstep (se 1 (by rfl) ⟨867155, by rfl⟩ : syracuseStep 1156207 = 1734311) B1734311
theorem B1156263 : Blo 1152637 1156263 := bstep (se 1 (by rfl) ⟨867197, by rfl⟩ : syracuseStep 1156263 = 1734395) B1734395
theorem B1156287 : Blo 1152637 1156287 := bstep (se 1 (by rfl) ⟨867215, by rfl⟩ : syracuseStep 1156287 = 1734431) B1734431
theorem B1156319 : Blo 1152637 1156319 := bstep (se 1 (by rfl) ⟨867239, by rfl⟩ : syracuseStep 1156319 = 1734479) B1734479
theorem B2467091 : Blo 1152637 2467091 := bstep (se 1 (by rfl) ⟨1850318, by rfl⟩ : syracuseStep 2467091 = 3700637) B3700637
theorem B1156399 : Blo 1152637 1156399 := bstep (se 1 (by rfl) ⟨867299, by rfl⟩ : syracuseStep 1156399 = 1734599) B1734599
theorem B2598299 : Blo 1152637 2598299 := bstep (se 1 (by rfl) ⟨1948724, by rfl⟩ : syracuseStep 2598299 = 3897449) B3897449
theorem B1156635 : Blo 1152637 1156635 := bstep (se 1 (by rfl) ⟨867476, by rfl⟩ : syracuseStep 1156635 = 1734953) B1734953
theorem B4564595 : Blo 1152637 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B8759177 : Blo 1152637 8759177 := bstep (se 2 (by rfl) ⟨3284691, by rfl⟩ : syracuseStep 8759177 = 6569383) B6569383
theorem B2598875 : Blo 1152637 2598875 := bstep (se 1 (by rfl) ⟨1949156, by rfl⟩ : syracuseStep 2598875 = 3898313) B3898313
theorem B2599055 : Blo 1152637 2599055 := bstep (se 1 (by rfl) ⟨1949291, by rfl⟩ : syracuseStep 2599055 = 3898583) B3898583
theorem B2599145 : Blo 1152637 2599145 := bstep (se 2 (by rfl) ⟨974679, by rfl⟩ : syracuseStep 2599145 = 1949359) B1949359
theorem B2599415 : Blo 1152637 2599415 := bstep (se 1 (by rfl) ⟨1949561, by rfl⟩ : syracuseStep 2599415 = 3899123) B3899123
theorem B142224437 : Blo 1152637 142224437 := bstep (se 5 (by rfl) ⟨6666770, by rfl⟩ : syracuseStep 142224437 = 13333541) B13333541
theorem B2960455 : Blo 1152637 2960455 := bstep (se 1 (by rfl) ⟨2220341, by rfl⟩ : syracuseStep 2960455 = 4440683) B4440683
theorem B2600009 : Blo 1152637 2600009 := bstep (se 2 (by rfl) ⟨975003, by rfl⟩ : syracuseStep 2600009 = 1950007) B1950007
theorem B86486237 : Blo 1152637 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B3124489 : Blo 1152637 3124489 := bstep (se 2 (by rfl) ⟨1171683, by rfl⟩ : syracuseStep 3124489 = 2343367) B2343367
theorem B1846967 : Blo 1152637 1846967 := bstep (se 1 (by rfl) ⟨1385225, by rfl⟩ : syracuseStep 1846967 = 2770451) B2770451
theorem B1946011 : Blo 1152637 1946011 := bstep (se 1 (by rfl) ⟨1459508, by rfl⟩ : syracuseStep 1946011 = 2919017) B2919017
theorem B5845607 : Blo 1152637 5845607 := bstep (se 1 (by rfl) ⟨4384205, by rfl⟩ : syracuseStep 5845607 = 8768411) B8768411
theorem B2601737 : Blo 1152637 2601737 := bstep (se 2 (by rfl) ⟨975651, by rfl⟩ : syracuseStep 2601737 = 1951303) B1951303
theorem B4928303 : Blo 1152637 4928303 := bstep (se 1 (by rfl) ⟨3696227, by rfl⟩ : syracuseStep 4928303 = 7392455) B7392455
theorem B2601791 : Blo 1152637 2601791 := bstep (se 1 (by rfl) ⟨1951343, by rfl⟩ : syracuseStep 2601791 = 3902687) B3902687
theorem B2601935 : Blo 1152637 2601935 := bstep (se 1 (by rfl) ⟨1951451, by rfl⟩ : syracuseStep 2601935 = 3902903) B3902903
theorem B2602025 : Blo 1152637 2602025 := bstep (se 2 (by rfl) ⟨975759, by rfl⟩ : syracuseStep 2602025 = 1951519) B1951519
theorem B2339911 : Blo 1152637 2339911 := bstep (se 1 (by rfl) ⟨1754933, by rfl⟩ : syracuseStep 2339911 = 3509867) B3509867
theorem B3290183 : Blo 1152637 3290183 := bstep (se 1 (by rfl) ⟨2467637, by rfl⟩ : syracuseStep 3290183 = 4935275) B4935275
theorem B7910621 : Blo 1152637 7910621 := bstep (se 3 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 7910621 = 2966483) B2966483
theorem B1946875 : Blo 1152637 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B2602313 : Blo 1152637 2602313 := bstep (se 2 (by rfl) ⟨975867, by rfl⟩ : syracuseStep 2602313 = 1951735) B1951735
theorem B1947719 : Blo 1152637 1947719 := bstep (se 1 (by rfl) ⟨1460789, by rfl⟩ : syracuseStep 1947719 = 2921579) B2921579
theorem B3291367 : Blo 1152637 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B5257943 : Blo 1152637 5257943 := bstep (se 1 (by rfl) ⟨3943457, by rfl⟩ : syracuseStep 5257943 = 7886915) B7886915
theorem B7027499 : Blo 1152637 7027499 := bstep (se 1 (by rfl) ⟨5270624, by rfl⟩ : syracuseStep 7027499 = 10541249) B10541249
theorem B50019119 : Blo 1152637 50019119 := bstep (se 1 (by rfl) ⟨37514339, by rfl⟩ : syracuseStep 50019119 = 75028679) B75028679
theorem B1948583 : Blo 1152637 1948583 := bstep (se 1 (by rfl) ⟨1461437, by rfl⟩ : syracuseStep 1948583 = 2922875) B2922875
theorem B5553299 : Blo 1152637 5553299 := bstep (se 1 (by rfl) ⟨4164974, by rfl⟩ : syracuseStep 5553299 = 8329949) B8329949
theorem B3947945 : Blo 1152637 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B7126751 : Blo 1152637 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B10534711 : Blo 1152637 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B42156065 : Blo 1152637 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B5555375 : Blo 1152637 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B2082127 : Blo 1152637 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B2770537 : Blo 1152637 2770537 := bstep (se 2 (by rfl) ⟨1038951, by rfl⟩ : syracuseStep 2770537 = 2077903) B2077903
theorem B1951337 : Blo 1152637 1951337 := bstep (se 2 (by rfl) ⟨731751, by rfl⟩ : syracuseStep 1951337 = 1463503) B1463503
theorem B30393991 : Blo 1152637 30393991 := bstep (se 1 (by rfl) ⟨22795493, by rfl⟩ : syracuseStep 30393991 = 45590987) B45590987
theorem B5850791 : Blo 1152637 5850791 := bstep (se 1 (by rfl) ⟨4388093, by rfl⟩ : syracuseStep 5850791 = 8776187) B8776187
theorem B4376551 : Blo 1152637 4376551 := bstep (se 1 (by rfl) ⟨3282413, by rfl⟩ : syracuseStep 4376551 = 6564827) B6564827
theorem B9848951 : Blo 1152637 9848951 := bstep (se 1 (by rfl) ⟨7386713, by rfl⟩ : syracuseStep 9848951 = 14773427) B14773427
theorem B2083151 : Blo 1152637 2083151 := bstep (se 1 (by rfl) ⟨1562363, by rfl⟩ : syracuseStep 2083151 = 3124727) B3124727
theorem B6572825 : Blo 1152637 6572825 := bstep (se 2 (by rfl) ⟨2464809, by rfl⟩ : syracuseStep 6572825 = 4929619) B4929619
theorem B1297471 : Blo 1152637 1297471 := bstep (se 1 (by rfl) ⟨973103, by rfl⟩ : syracuseStep 1297471 = 1946207) B1946207
theorem B4443283 : Blo 1152637 4443283 := bstep (se 1 (by rfl) ⟨3332462, by rfl⟩ : syracuseStep 4443283 = 6664925) B6664925
theorem B2084015 : Blo 1152637 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B10669279 : Blo 1152637 10669279 := bstep (se 1 (by rfl) ⟨8001959, by rfl⟩ : syracuseStep 10669279 = 16003919) B16003919
theorem B4378283 : Blo 1152637 4378283 := bstep (se 1 (by rfl) ⟨3283712, by rfl⟩ : syracuseStep 4378283 = 6567425) B6567425
theorem B6246163 : Blo 1152637 6246163 := bstep (se 1 (by rfl) ⟨4684622, by rfl⟩ : syracuseStep 6246163 = 9369245) B9369245
theorem B15781655 : Blo 1152637 15781655 := bstep (se 1 (by rfl) ⟨11836241, by rfl⟩ : syracuseStep 15781655 = 23672483) B23672483
theorem B4378495 : Blo 1152637 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B1298587 : Blo 1152637 1298587 := bstep (se 1 (by rfl) ⟨973940, by rfl⟩ : syracuseStep 1298587 = 1947881) B1947881
theorem B4378799 : Blo 1152637 4378799 := bstep (se 1 (by rfl) ⟨3284099, by rfl⟩ : syracuseStep 4378799 = 6568199) B6568199
theorem B4935923 : Blo 1152637 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B8769869 : Blo 1152637 8769869 := bstep (se 3 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 8769869 = 3288701) B3288701
theorem B56251097 : Blo 1152637 56251097 := bstep (se 2 (by rfl) ⟨21094161, by rfl⟩ : syracuseStep 56251097 = 42188323) B42188323
theorem B4379771 : Blo 1152637 4379771 := bstep (se 1 (by rfl) ⟨3284828, by rfl⟩ : syracuseStep 4379771 = 6569657) B6569657
theorem B1299775 : Blo 1152637 1299775 := bstep (se 1 (by rfl) ⟨974831, by rfl⟩ : syracuseStep 1299775 = 1949663) B1949663
theorem B6575489 : Blo 1152637 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B5330569 : Blo 1152637 5330569 := bstep (se 2 (by rfl) ⟨1998963, by rfl⟩ : syracuseStep 5330569 = 3997927) B3997927
theorem B1300207 : Blo 1152637 1300207 := bstep (se 1 (by rfl) ⟨975155, by rfl⟩ : syracuseStep 1300207 = 1950311) B1950311
theorem B7395067 : Blo 1152637 7395067 := bstep (se 1 (by rfl) ⟨5546300, by rfl⟩ : syracuseStep 7395067 = 11092601) B11092601
theorem B1300315 : Blo 1152637 1300315 := bstep (se 1 (by rfl) ⟨975236, by rfl⟩ : syracuseStep 1300315 = 1950473) B1950473
theorem B5855165 : Blo 1152637 5855165 := bstep (se 3 (by rfl) ⟨1097843, by rfl⟩ : syracuseStep 5855165 = 2195687) B2195687
theorem B5626027 : Blo 1152637 5626027 := bstep (se 1 (by rfl) ⟨4219520, by rfl⟩ : syracuseStep 5626027 = 8439041) B8439041
theorem B1300711 : Blo 1152637 1300711 := bstep (se 1 (by rfl) ⟨975533, by rfl⟩ : syracuseStep 1300711 = 1951067) B1951067
theorem B9001543 : Blo 1152637 9001543 := bstep (se 1 (by rfl) ⟨6751157, by rfl⟩ : syracuseStep 9001543 = 13502315) B13502315
theorem B8772299 : Blo 1152637 8772299 := bstep (se 1 (by rfl) ⟨6579224, by rfl⟩ : syracuseStep 8772299 = 13158449) B13158449
theorem B14047991 : Blo 1152637 14047991 := bstep (se 1 (by rfl) ⟨10535993, by rfl⟩ : syracuseStep 14047991 = 21071987) B21071987
theorem B3693383 : Blo 1152637 3693383 := bstep (se 1 (by rfl) ⟨2770037, by rfl⟩ : syracuseStep 3693383 = 5540075) B5540075
theorem B35576819 : Blo 1152637 35576819 := bstep (se 1 (by rfl) ⟨26682614, by rfl⟩ : syracuseStep 35576819 = 53365229) B53365229
theorem B3891347 : Blo 1152637 3891347 := bstep (se 1 (by rfl) ⟨2918510, by rfl⟩ : syracuseStep 3891347 = 5837021) B5837021
theorem B2777303 : Blo 1152637 2777303 := bstep (se 1 (by rfl) ⟨2082977, by rfl⟩ : syracuseStep 2777303 = 4165955) B4165955
theorem B3891455 : Blo 1152637 3891455 := bstep (se 1 (by rfl) ⟨2918591, by rfl⟩ : syracuseStep 3891455 = 5837183) B5837183
theorem B3891617 : Blo 1152637 3891617 := bstep (se 2 (by rfl) ⟨1459356, by rfl⟩ : syracuseStep 3891617 = 2918713) B2918713
theorem B4383143 : Blo 1152637 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B1171999 : Blo 1152637 1171999 := bstep (se 1 (by rfl) ⟨878999, by rfl⟩ : syracuseStep 1171999 = 1757999) B1757999
theorem B10281725 : Blo 1152637 10281725 := bstep (se 3 (by rfl) ⟨1927823, by rfl⟩ : syracuseStep 10281725 = 3855647) B3855647
theorem B39969611 : Blo 1152637 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B1729583 : Blo 1152637 1729583 := bstep (se 1 (by rfl) ⟨1297187, by rfl⟩ : syracuseStep 1729583 = 2594375) B2594375
theorem B8774729 : Blo 1152637 8774729 := bstep (se 2 (by rfl) ⟨3290523, by rfl⟩ : syracuseStep 8774729 = 6581047) B6581047
theorem B1729703 : Blo 1152637 1729703 := bstep (se 1 (by rfl) ⟨1297277, by rfl⟩ : syracuseStep 1729703 = 2594555) B2594555
theorem B1730075 : Blo 1152637 1730075 := bstep (se 1 (by rfl) ⟨1297556, by rfl⟩ : syracuseStep 1730075 = 2595113) B2595113
theorem B4384327 : Blo 1152637 4384327 := bstep (se 1 (by rfl) ⟨3288245, by rfl⟩ : syracuseStep 4384327 = 6576491) B6576491
theorem B21030587 : Blo 1152637 21030587 := bstep (se 1 (by rfl) ⟨15772940, by rfl⟩ : syracuseStep 21030587 = 31545881) B31545881
theorem B2189119 : Blo 1152637 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B1730459 : Blo 1152637 1730459 := bstep (se 1 (by rfl) ⟨1297844, by rfl⟩ : syracuseStep 1730459 = 2595689) B2595689
theorem B3893183 : Blo 1152637 3893183 := bstep (se 1 (by rfl) ⟨2919887, by rfl⟩ : syracuseStep 3893183 = 5839775) B5839775
theorem B1730495 : Blo 1152637 1730495 := bstep (se 1 (by rfl) ⟨1297871, by rfl⟩ : syracuseStep 1730495 = 2595743) B2595743
theorem B2189339 : Blo 1152637 2189339 := bstep (se 1 (by rfl) ⟨1642004, by rfl⟩ : syracuseStep 2189339 = 3284009) B3284009
theorem B11102291 : Blo 1152637 11102291 := bstep (se 1 (by rfl) ⟨8326718, by rfl⟩ : syracuseStep 11102291 = 16653437) B16653437
theorem B3893345 : Blo 1152637 3893345 := bstep (se 2 (by rfl) ⟨1460004, by rfl⟩ : syracuseStep 3893345 = 2920009) B2920009
theorem B1730681 : Blo 1152637 1730681 := bstep (se 2 (by rfl) ⟨649005, by rfl⟩ : syracuseStep 1730681 = 1298011) B1298011
theorem B60713189 : Blo 1152637 60713189 := bstep (se 4 (by rfl) ⟨5691861, by rfl⟩ : syracuseStep 60713189 = 11383723) B11383723
theorem B1731065 : Blo 1152637 1731065 := bstep (se 2 (by rfl) ⟨649149, by rfl⟩ : syracuseStep 1731065 = 1298299) B1298299
theorem B4385299 : Blo 1152637 4385299 := bstep (se 1 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 4385299 = 6577949) B6577949
theorem B1731119 : Blo 1152637 1731119 := bstep (se 1 (by rfl) ⟨1298339, by rfl⟩ : syracuseStep 1731119 = 2596679) B2596679
theorem B3893885 : Blo 1152637 3893885 := bstep (se 3 (by rfl) ⟨730103, by rfl⟩ : syracuseStep 3893885 = 1460207) B1460207
theorem B3894155 : Blo 1152637 3894155 := bstep (se 1 (by rfl) ⟨2920616, by rfl⟩ : syracuseStep 3894155 = 5841233) B5841233
theorem B1731551 : Blo 1152637 1731551 := bstep (se 1 (by rfl) ⟨1298663, by rfl⟩ : syracuseStep 1731551 = 2597327) B2597327
theorem B1731995 : Blo 1152637 1731995 := bstep (se 1 (by rfl) ⟨1298996, by rfl⟩ : syracuseStep 1731995 = 2597993) B2597993
theorem B3894695 : Blo 1152637 3894695 := bstep (se 1 (by rfl) ⟨2921021, by rfl⟩ : syracuseStep 3894695 = 5842043) B5842043
theorem B4386271 : Blo 1152637 4386271 := bstep (se 1 (by rfl) ⟨3289703, by rfl⟩ : syracuseStep 4386271 = 6579407) B6579407
theorem B1732415 : Blo 1152637 1732415 := bstep (se 1 (by rfl) ⟨1299311, by rfl⟩ : syracuseStep 1732415 = 2598623) B2598623
theorem B3895127 : Blo 1152637 3895127 := bstep (se 1 (by rfl) ⟨2921345, by rfl⟩ : syracuseStep 3895127 = 5842691) B5842691
theorem B3895289 : Blo 1152637 3895289 := bstep (se 2 (by rfl) ⟨1460733, by rfl⟩ : syracuseStep 3895289 = 2921467) B2921467
theorem B1732601 : Blo 1152637 1732601 := bstep (se 2 (by rfl) ⟨649725, by rfl⟩ : syracuseStep 1732601 = 1299451) B1299451
theorem B1732841 : Blo 1152637 1732841 := bstep (se 2 (by rfl) ⟨649815, by rfl⟩ : syracuseStep 1732841 = 1299631) B1299631
theorem B6582505 : Blo 1152637 6582505 := bstep (se 2 (by rfl) ⟨2468439, by rfl⟩ : syracuseStep 6582505 = 4936879) B4936879
theorem B3895559 : Blo 1152637 3895559 := bstep (se 1 (by rfl) ⟨2921669, by rfl⟩ : syracuseStep 3895559 = 5843339) B5843339
theorem B1732967 : Blo 1152637 1732967 := bstep (se 1 (by rfl) ⟨1299725, by rfl⟩ : syracuseStep 1732967 = 2599451) B2599451
theorem B3895937 : Blo 1152637 3895937 := bstep (se 2 (by rfl) ⟨1460976, by rfl⟩ : syracuseStep 3895937 = 2921953) B2921953
theorem B1733513 : Blo 1152637 1733513 := bstep (se 2 (by rfl) ⟨650067, by rfl⟩ : syracuseStep 1733513 = 1300135) B1300135
theorem B3896207 : Blo 1152637 3896207 := bstep (se 1 (by rfl) ⟨2922155, by rfl⟩ : syracuseStep 3896207 = 5844311) B5844311
theorem B7402427 : Blo 1152637 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B2192339 : Blo 1152637 2192339 := bstep (se 1 (by rfl) ⟨1644254, by rfl⟩ : syracuseStep 2192339 = 3288509) B3288509
theorem B8320259 : Blo 1152637 8320259 := bstep (se 1 (by rfl) ⟨6240194, by rfl⟩ : syracuseStep 8320259 = 12480389) B12480389
theorem B1733897 : Blo 1152637 1733897 := bstep (se 2 (by rfl) ⟨650211, by rfl⟩ : syracuseStep 1733897 = 1300423) B1300423
theorem B3896639 : Blo 1152637 3896639 := bstep (se 1 (by rfl) ⟨2922479, by rfl⟩ : syracuseStep 3896639 = 5844959) B5844959
theorem B1733951 : Blo 1152637 1733951 := bstep (se 1 (by rfl) ⟨1300463, by rfl⟩ : syracuseStep 1733951 = 2600927) B2600927
theorem B4388215 : Blo 1152637 4388215 := bstep (se 1 (by rfl) ⟨3291161, by rfl⟩ : syracuseStep 4388215 = 6582323) B6582323
theorem B3896747 : Blo 1152637 3896747 := bstep (se 1 (by rfl) ⟨2922560, by rfl⟩ : syracuseStep 3896747 = 5845121) B5845121
theorem B2193007 : Blo 1152637 2193007 := bstep (se 1 (by rfl) ⟨1644755, by rfl⟩ : syracuseStep 2193007 = 3289511) B3289511
theorem B11105981 : Blo 1152637 11105981 := bstep (se 3 (by rfl) ⟨2082371, by rfl⟩ : syracuseStep 11105981 = 4164743) B4164743
theorem B13530833 : Blo 1152637 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B1734377 : Blo 1152637 1734377 := bstep (se 2 (by rfl) ⟨650391, by rfl⟩ : syracuseStep 1734377 = 1300783) B1300783
theorem B1734383 : Blo 1152637 1734383 := bstep (se 1 (by rfl) ⟨1300787, by rfl⟩ : syracuseStep 1734383 = 2601575) B2601575
theorem B3700559 : Blo 1152637 3700559 := bstep (se 1 (by rfl) ⟨2775419, by rfl⟩ : syracuseStep 3700559 = 5550839) B5550839
theorem B4388687 : Blo 1152637 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B3897287 : Blo 1152637 3897287 := bstep (se 1 (by rfl) ⟨2922965, by rfl⟩ : syracuseStep 3897287 = 5845931) B5845931
theorem B1734839 : Blo 1152637 1734839 := bstep (se 1 (by rfl) ⟨1301129, by rfl⟩ : syracuseStep 1734839 = 2602259) B2602259
theorem B1734887 : Blo 1152637 1734887 := bstep (se 1 (by rfl) ⟨1301165, by rfl⟩ : syracuseStep 1734887 = 2602331) B2602331
theorem B10681247 : Blo 1152637 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B54066707 : Blo 1152637 54066707 := bstep (se 1 (by rfl) ⟨40550030, by rfl⟩ : syracuseStep 54066707 = 81100061) B81100061
theorem B4390631 : Blo 1152637 4390631 := bstep (se 1 (by rfl) ⟨3292973, by rfl⟩ : syracuseStep 4390631 = 6585947) B6585947
theorem B2195399 : Blo 1152637 2195399 := bstep (se 1 (by rfl) ⟨1646549, by rfl⟩ : syracuseStep 2195399 = 3293099) B3293099
theorem B4391131 : Blo 1152637 4391131 := bstep (se 1 (by rfl) ⟨3293348, by rfl⟩ : syracuseStep 4391131 = 6586697) B6586697
theorem B3703583 : Blo 1152637 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B3900527 : Blo 1152637 3900527 := bstep (se 1 (by rfl) ⟨2925395, by rfl⟩ : syracuseStep 3900527 = 5850791) B5850791
theorem B2918825 : Blo 1152637 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B2918855 : Blo 1152637 2918855 := bstep (se 1 (by rfl) ⟨2189141, by rfl⟩ : syracuseStep 2918855 = 4378283) B4378283
theorem B10521103 : Blo 1152637 10521103 := bstep (se 1 (by rfl) ⟨7890827, by rfl⟩ : syracuseStep 10521103 = 15781655) B15781655
theorem B5835401 : Blo 1152637 5835401 := bstep (se 2 (by rfl) ⟨2188275, by rfl⟩ : syracuseStep 5835401 = 4376551) B4376551
theorem B2919199 : Blo 1152637 2919199 := bstep (se 1 (by rfl) ⟨2189399, by rfl⟩ : syracuseStep 2919199 = 4378799) B4378799
theorem B1641703 : Blo 1152637 1641703 := bstep (se 1 (by rfl) ⟨1231277, by rfl⟩ : syracuseStep 1641703 = 2462555) B2462555
theorem B22187357 : Blo 1152637 22187357 := bstep (se 3 (by rfl) ⟨4160129, by rfl⟩ : syracuseStep 22187357 = 8320259) B8320259
theorem B2919847 : Blo 1152637 2919847 := bstep (se 1 (by rfl) ⟨2189885, by rfl⟩ : syracuseStep 2919847 = 4379771) B4379771
theorem B3903443 : Blo 1152637 3903443 := bstep (se 1 (by rfl) ⟨2927582, by rfl⟩ : syracuseStep 3903443 = 5855165) B5855165
theorem B14225705 : Blo 1152637 14225705 := bstep (se 2 (by rfl) ⟨5334639, by rfl⟩ : syracuseStep 14225705 = 10669279) B10669279
theorem B4165985 : Blo 1152637 4165985 := bstep (se 2 (by rfl) ⟨1562244, by rfl⟩ : syracuseStep 4165985 = 3124489) B3124489
theorem B2462255 : Blo 1152637 2462255 := bstep (se 1 (by rfl) ⟨1846691, by rfl⟩ : syracuseStep 2462255 = 3693383) B3693383
theorem B8328217 : Blo 1152637 8328217 := bstep (se 2 (by rfl) ⟨3123081, by rfl⟩ : syracuseStep 8328217 = 6246163) B6246163
theorem B5837993 : Blo 1152637 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B7017839 : Blo 1152637 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B2594231 : Blo 1152637 2594231 := bstep (se 1 (by rfl) ⟨1945673, by rfl⟩ : syracuseStep 2594231 = 3891347) B3891347
theorem B2594303 : Blo 1152637 2594303 := bstep (se 1 (by rfl) ⟨1945727, by rfl⟩ : syracuseStep 2594303 = 3891455) B3891455
theorem B2594411 : Blo 1152637 2594411 := bstep (se 1 (by rfl) ⟨1945808, by rfl⟩ : syracuseStep 2594411 = 3891617) B3891617
theorem B2922095 : Blo 1152637 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B6854483 : Blo 1152637 6854483 := bstep (se 1 (by rfl) ⟨5140862, by rfl⟩ : syracuseStep 6854483 = 10281725) B10281725
theorem B2594681 : Blo 1152637 2594681 := bstep (se 2 (by rfl) ⟨973005, by rfl⟩ : syracuseStep 2594681 = 1946011) B1946011
theorem B26646407 : Blo 1152637 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B1153055 : Blo 1152637 1153055 := bstep (se 1 (by rfl) ⟨864791, by rfl⟩ : syracuseStep 1153055 = 1729583) B1729583
theorem B1153135 : Blo 1152637 1153135 := bstep (se 1 (by rfl) ⟨864851, by rfl⟩ : syracuseStep 1153135 = 1729703) B1729703
theorem B1644727 : Blo 1152637 1644727 := bstep (se 1 (by rfl) ⟨1233545, by rfl⟩ : syracuseStep 1644727 = 2467091) B2467091
theorem B1153383 : Blo 1152637 1153383 := bstep (se 1 (by rfl) ⟨865037, by rfl⟩ : syracuseStep 1153383 = 1730075) B1730075
theorem B5839451 : Blo 1152637 5839451 := bstep (se 1 (by rfl) ⟨4379588, by rfl⟩ : syracuseStep 5839451 = 8759177) B8759177
theorem B1153639 : Blo 1152637 1153639 := bstep (se 1 (by rfl) ⟨865229, by rfl⟩ : syracuseStep 1153639 = 1730459) B1730459
theorem B2595455 : Blo 1152637 2595455 := bstep (se 1 (by rfl) ⟨1946591, by rfl⟩ : syracuseStep 2595455 = 3893183) B3893183
theorem B1153663 : Blo 1152637 1153663 := bstep (se 1 (by rfl) ⟨865247, by rfl⟩ : syracuseStep 1153663 = 1730495) B1730495
theorem B2595563 : Blo 1152637 2595563 := bstep (se 1 (by rfl) ⟨1946672, by rfl⟩ : syracuseStep 2595563 = 3893345) B3893345
theorem B1153787 : Blo 1152637 1153787 := bstep (se 1 (by rfl) ⟨865340, by rfl⟩ : syracuseStep 1153787 = 1730681) B1730681
theorem B3119881 : Blo 1152637 3119881 := bstep (se 2 (by rfl) ⟨1169955, by rfl⟩ : syracuseStep 3119881 = 2339911) B2339911
theorem B40475459 : Blo 1152637 40475459 := bstep (se 1 (by rfl) ⟨30356594, by rfl⟩ : syracuseStep 40475459 = 60713189) B60713189
theorem B2595833 : Blo 1152637 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B1154043 : Blo 1152637 1154043 := bstep (se 1 (by rfl) ⟨865532, by rfl⟩ : syracuseStep 1154043 = 1731065) B1731065
theorem B1154079 : Blo 1152637 1154079 := bstep (se 1 (by rfl) ⟨865559, by rfl⟩ : syracuseStep 1154079 = 1731119) B1731119
theorem B2595923 : Blo 1152637 2595923 := bstep (se 1 (by rfl) ⟨1946942, by rfl⟩ : syracuseStep 2595923 = 3893885) B3893885
theorem B2596103 : Blo 1152637 2596103 := bstep (se 1 (by rfl) ⟨1947077, by rfl⟩ : syracuseStep 2596103 = 3894155) B3894155
theorem B1154367 : Blo 1152637 1154367 := bstep (se 1 (by rfl) ⟨865775, by rfl⟩ : syracuseStep 1154367 = 1731551) B1731551
theorem B2924009 : Blo 1152637 2924009 := bstep (se 2 (by rfl) ⟨1096503, by rfl⟩ : syracuseStep 2924009 = 2193007) B2193007
theorem B1154663 : Blo 1152637 1154663 := bstep (se 1 (by rfl) ⟨865997, by rfl⟩ : syracuseStep 1154663 = 1731995) B1731995
theorem B2596463 : Blo 1152637 2596463 := bstep (se 1 (by rfl) ⟨1947347, by rfl⟩ : syracuseStep 2596463 = 3894695) B3894695
theorem B1154943 : Blo 1152637 1154943 := bstep (se 1 (by rfl) ⟨866207, by rfl⟩ : syracuseStep 1154943 = 1732415) B1732415
theorem B2596751 : Blo 1152637 2596751 := bstep (se 1 (by rfl) ⟨1947563, by rfl⟩ : syracuseStep 2596751 = 3895127) B3895127
theorem B1155067 : Blo 1152637 1155067 := bstep (se 1 (by rfl) ⟨866300, by rfl⟩ : syracuseStep 1155067 = 1732601) B1732601
theorem B2596859 : Blo 1152637 2596859 := bstep (se 1 (by rfl) ⟨1947644, by rfl⟩ : syracuseStep 2596859 = 3895289) B3895289
theorem B379265165 : Blo 1152637 379265165 := bstep (se 3 (by rfl) ⟨71112218, by rfl⟩ : syracuseStep 379265165 = 142224437) B142224437
theorem B1155227 : Blo 1152637 1155227 := bstep (se 1 (by rfl) ⟨866420, by rfl⟩ : syracuseStep 1155227 = 1732841) B1732841
theorem B2597039 : Blo 1152637 2597039 := bstep (se 1 (by rfl) ⟨1947779, by rfl⟩ : syracuseStep 2597039 = 3895559) B3895559
theorem B1155311 : Blo 1152637 1155311 := bstep (se 1 (by rfl) ⟨866483, by rfl⟩ : syracuseStep 1155311 = 1732967) B1732967
theorem B2597291 : Blo 1152637 2597291 := bstep (se 1 (by rfl) ⟨1947968, by rfl⟩ : syracuseStep 2597291 = 3895937) B3895937
theorem B3285535 : Blo 1152637 3285535 := bstep (se 1 (by rfl) ⟨2464151, by rfl⟩ : syracuseStep 3285535 = 4928303) B4928303
theorem B1155675 : Blo 1152637 1155675 := bstep (se 1 (by rfl) ⟨866756, by rfl⟩ : syracuseStep 1155675 = 1733513) B1733513
theorem B2597471 : Blo 1152637 2597471 := bstep (se 1 (by rfl) ⟨1948103, by rfl⟩ : syracuseStep 2597471 = 3896207) B3896207
theorem B12002057 : Blo 1152637 12002057 := bstep (se 2 (by rfl) ⟨4500771, by rfl⟩ : syracuseStep 12002057 = 9001543) B9001543
theorem B1155931 : Blo 1152637 1155931 := bstep (se 1 (by rfl) ⟨866948, by rfl⟩ : syracuseStep 1155931 = 1733897) B1733897
theorem B2597759 : Blo 1152637 2597759 := bstep (se 1 (by rfl) ⟨1948319, by rfl⟩ : syracuseStep 2597759 = 3896639) B3896639
theorem B1155967 : Blo 1152637 1155967 := bstep (se 1 (by rfl) ⟨866975, by rfl⟩ : syracuseStep 1155967 = 1733951) B1733951
theorem B2597831 : Blo 1152637 2597831 := bstep (se 1 (by rfl) ⟨1948373, by rfl⟩ : syracuseStep 2597831 = 3896747) B3896747
theorem B10527853 : Blo 1152637 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B9020555 : Blo 1152637 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B1156251 : Blo 1152637 1156251 := bstep (se 1 (by rfl) ⟨867188, by rfl⟩ : syracuseStep 1156251 = 1734377) B1734377
theorem B1156255 : Blo 1152637 1156255 := bstep (se 1 (by rfl) ⟨867191, by rfl⟩ : syracuseStep 1156255 = 1734383) B1734383
theorem B2467039 : Blo 1152637 2467039 := bstep (se 1 (by rfl) ⟨1850279, by rfl⟩ : syracuseStep 2467039 = 3700559) B3700559
theorem B2925791 : Blo 1152637 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B2598191 : Blo 1152637 2598191 := bstep (se 1 (by rfl) ⟨1948643, by rfl⟩ : syracuseStep 2598191 = 3897287) B3897287
theorem B1156559 : Blo 1152637 1156559 := bstep (se 1 (by rfl) ⟨867419, by rfl⟩ : syracuseStep 1156559 = 1734839) B1734839
theorem B1156591 : Blo 1152637 1156591 := bstep (se 1 (by rfl) ⟨867443, by rfl⟩ : syracuseStep 1156591 = 1734887) B1734887
theorem B4925245 : Blo 1152637 4925245 := bstep (se 3 (by rfl) ⟨923483, by rfl⟩ : syracuseStep 4925245 = 1846967) B1846967
theorem B7120831 : Blo 1152637 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B2927087 : Blo 1152637 2927087 := bstep (se 1 (by rfl) ⟨2195315, by rfl⟩ : syracuseStep 2927087 = 4390631) B4390631
theorem B13348151 : Blo 1152637 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B1945255 : Blo 1152637 1945255 := bstep (se 1 (by rfl) ⟨1458941, by rfl⟩ : syracuseStep 1945255 = 2917883) B2917883
theorem B14986943 : Blo 1152637 14986943 := bstep (se 1 (by rfl) ⟨11240207, by rfl⟩ : syracuseStep 14986943 = 22480415) B22480415
theorem B2600639 : Blo 1152637 2600639 := bstep (se 1 (by rfl) ⟨1950479, by rfl⟩ : syracuseStep 2600639 = 3900959) B3900959
theorem B6565967 : Blo 1152637 6565967 := bstep (se 1 (by rfl) ⟨4924475, by rfl⟩ : syracuseStep 6565967 = 9848951) B9848951
theorem B1388767 : Blo 1152637 1388767 := bstep (se 1 (by rfl) ⟨1041575, by rfl⟩ : syracuseStep 1388767 = 2083151) B2083151
theorem B2601215 : Blo 1152637 2601215 := bstep (se 1 (by rfl) ⟨1950911, by rfl⟩ : syracuseStep 2601215 = 3901823) B3901823
theorem B5845769 : Blo 1152637 5845769 := bstep (se 2 (by rfl) ⟨2192163, by rfl⟩ : syracuseStep 5845769 = 4384327) B4384327
theorem B1946423 : Blo 1152637 1946423 := bstep (se 1 (by rfl) ⟨1459817, by rfl⟩ : syracuseStep 1946423 = 2919635) B2919635
theorem B16627031 : Blo 1152637 16627031 := bstep (se 1 (by rfl) ⟨12470273, by rfl⟩ : syracuseStep 16627031 = 24940547) B24940547
theorem B12498295 : Blo 1152637 12498295 := bstep (se 1 (by rfl) ⟨9373721, by rfl⟩ : syracuseStep 12498295 = 18747443) B18747443
theorem B2602367 : Blo 1152637 2602367 := bstep (se 1 (by rfl) ⟨1951775, by rfl⟩ : syracuseStep 2602367 = 3903551) B3903551
theorem B3290615 : Blo 1152637 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B5846579 : Blo 1152637 5846579 := bstep (se 1 (by rfl) ⟨4384934, by rfl⟩ : syracuseStep 5846579 = 8769869) B8769869
theorem B37500731 : Blo 1152637 37500731 := bstep (se 1 (by rfl) ⟨28125548, by rfl⟩ : syracuseStep 37500731 = 56251097) B56251097
theorem B5847065 : Blo 1152637 5847065 := bstep (se 2 (by rfl) ⟨2192649, by rfl⟩ : syracuseStep 5847065 = 4385299) B4385299
theorem B1947935 : Blo 1152637 1947935 := bstep (se 1 (by rfl) ⟨1460951, by rfl⟩ : syracuseStep 1947935 = 2921903) B2921903
theorem B7125479 : Blo 1152637 7125479 := bstep (se 1 (by rfl) ⟨5344109, by rfl⟩ : syracuseStep 7125479 = 10688219) B10688219
theorem B1948151 : Blo 1152637 1948151 := bstep (se 1 (by rfl) ⟨1461113, by rfl⟩ : syracuseStep 1948151 = 2922227) B2922227
theorem B2079287 : Blo 1152637 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B3947273 : Blo 1152637 3947273 := bstep (se 2 (by rfl) ⟨1480227, by rfl⟩ : syracuseStep 3947273 = 2960455) B2960455
theorem B9878543 : Blo 1152637 9878543 := bstep (se 1 (by rfl) ⟨7408907, by rfl⟩ : syracuseStep 9878543 = 14817815) B14817815
theorem B5848199 : Blo 1152637 5848199 := bstep (se 1 (by rfl) ⟨4386149, by rfl⟩ : syracuseStep 5848199 = 8772299) B8772299
theorem B5848361 : Blo 1152637 5848361 := bstep (se 2 (by rfl) ⟨2193135, by rfl⟩ : syracuseStep 5848361 = 4386271) B4386271
theorem B1949231 : Blo 1152637 1949231 := bstep (se 1 (by rfl) ⟨1461923, by rfl⟩ : syracuseStep 1949231 = 2923847) B2923847
theorem B1851535 : Blo 1152637 1851535 := bstep (se 1 (by rfl) ⟨1388651, by rfl⟩ : syracuseStep 1851535 = 2777303) B2777303
theorem B5849819 : Blo 1152637 5849819 := bstep (se 1 (by rfl) ⟨4387364, by rfl⟩ : syracuseStep 5849819 = 8774729) B8774729
theorem B1459559 : Blo 1152637 1459559 := bstep (se 1 (by rfl) ⟨1094669, by rfl⟩ : syracuseStep 1459559 = 2189339) B2189339
theorem B5850953 : Blo 1152637 5850953 := bstep (se 2 (by rfl) ⟨2194107, by rfl⟩ : syracuseStep 5850953 = 4388215) B4388215
theorem B57657491 : Blo 1152637 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B18729605 : Blo 1152637 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B5557373 : Blo 1152637 5557373 := bstep (se 3 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 5557373 = 2084015) B2084015
theorem B4934951 : Blo 1152637 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B1461559 : Blo 1152637 1461559 := bstep (se 1 (by rfl) ⟨1096169, by rfl⟩ : syracuseStep 1461559 = 2192339) B2192339
theorem B1298479 : Blo 1152637 1298479 := bstep (se 1 (by rfl) ⟨973859, by rfl⟩ : syracuseStep 1298479 = 1947719) B1947719
theorem B33346079 : Blo 1152637 33346079 := bstep (se 1 (by rfl) ⟨25009559, by rfl⟩ : syracuseStep 33346079 = 50019119) B50019119
theorem B1299055 : Blo 1152637 1299055 := bstep (se 1 (by rfl) ⟨974291, by rfl⟩ : syracuseStep 1299055 = 1948583) B1948583
theorem B14046281 : Blo 1152637 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B1463599 : Blo 1152637 1463599 := bstep (se 1 (by rfl) ⟨1097699, by rfl⟩ : syracuseStep 1463599 = 2195399) B2195399
theorem B28104043 : Blo 1152637 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B1267391 : Blo 1152637 1267391 := bstep (se 1 (by rfl) ⟨950543, by rfl⟩ : syracuseStep 1267391 = 1901087) B1901087
theorem B168450191 : Blo 1152637 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B1300891 : Blo 1152637 1300891 := bstep (se 1 (by rfl) ⟨975668, by rfl⟩ : syracuseStep 1300891 = 1951337) B1951337
theorem B4938691 : Blo 1152637 4938691 := bstep (se 1 (by rfl) ⟨3704018, by rfl⟩ : syracuseStep 4938691 = 7408037) B7408037
theorem B2776169 : Blo 1152637 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B4381883 : Blo 1152637 4381883 := bstep (se 1 (by rfl) ⟨3286412, by rfl⟩ : syracuseStep 4381883 = 6572825) B6572825
theorem B3694049 : Blo 1152637 3694049 := bstep (se 2 (by rfl) ⟨1385268, by rfl⟩ : syracuseStep 3694049 = 2770537) B2770537
theorem B40525321 : Blo 1152637 40525321 := bstep (se 2 (by rfl) ⟨15196995, by rfl⟩ : syracuseStep 40525321 = 30393991) B30393991
theorem B3694663 : Blo 1152637 3694663 := bstep (se 1 (by rfl) ⟨2770997, by rfl⟩ : syracuseStep 3694663 = 5541995) B5541995
theorem B6250661 : Blo 1152637 6250661 := bstep (se 4 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 6250661 = 1171999) B1171999
theorem B1729079 : Blo 1152637 1729079 := bstep (se 1 (by rfl) ⟨1296809, by rfl⟩ : syracuseStep 1729079 = 2593619) B2593619
theorem B1729439 : Blo 1152637 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B4383659 : Blo 1152637 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B1729727 : Blo 1152637 1729727 := bstep (se 1 (by rfl) ⟨1297295, by rfl⟩ : syracuseStep 1729727 = 2594591) B2594591
theorem B1729871 : Blo 1152637 1729871 := bstep (se 1 (by rfl) ⟨1297403, by rfl⟩ : syracuseStep 1729871 = 2594807) B2594807
theorem B1729961 : Blo 1152637 1729961 := bstep (se 2 (by rfl) ⟨648735, by rfl⟩ : syracuseStep 1729961 = 1297471) B1297471
theorem B5924377 : Blo 1152637 5924377 := bstep (se 2 (by rfl) ⟨2221641, by rfl⟩ : syracuseStep 5924377 = 4443283) B4443283
theorem B1730111 : Blo 1152637 1730111 := bstep (se 1 (by rfl) ⟨1297583, by rfl⟩ : syracuseStep 1730111 = 2595167) B2595167
theorem B9365327 : Blo 1152637 9365327 := bstep (se 1 (by rfl) ⟨7023995, by rfl⟩ : syracuseStep 9365327 = 14047991) B14047991
theorem B3893075 : Blo 1152637 3893075 := bstep (se 1 (by rfl) ⟨2919806, by rfl⟩ : syracuseStep 3893075 = 5839613) B5839613
theorem B14772091 : Blo 1152637 14772091 := bstep (se 1 (by rfl) ⟨11079068, by rfl⟩ : syracuseStep 14772091 = 22158137) B22158137
theorem B4155259 : Blo 1152637 4155259 := bstep (se 1 (by rfl) ⟨3116444, by rfl⟩ : syracuseStep 4155259 = 6232889) B6232889
theorem B1730471 : Blo 1152637 1730471 := bstep (se 1 (by rfl) ⟨1297853, by rfl⟩ : syracuseStep 1730471 = 2595707) B2595707
theorem B23717879 : Blo 1152637 23717879 := bstep (se 1 (by rfl) ⟨17788409, by rfl⟩ : syracuseStep 23717879 = 35576819) B35576819
theorem B1730591 : Blo 1152637 1730591 := bstep (se 1 (by rfl) ⟨1297943, by rfl⟩ : syracuseStep 1730591 = 2595887) B2595887
theorem B1731047 : Blo 1152637 1731047 := bstep (se 1 (by rfl) ⟨1298285, by rfl⟩ : syracuseStep 1731047 = 2596571) B2596571
theorem B13330919 : Blo 1152637 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B1731227 : Blo 1152637 1731227 := bstep (se 1 (by rfl) ⟨1298420, by rfl⟩ : syracuseStep 1731227 = 2596841) B2596841
theorem B1731449 : Blo 1152637 1731449 := bstep (se 2 (by rfl) ⟨649293, by rfl⟩ : syracuseStep 1731449 = 1298587) B1298587
theorem B8776673 : Blo 1152637 8776673 := bstep (se 2 (by rfl) ⟨3291252, by rfl⟩ : syracuseStep 8776673 = 6582505) B6582505
theorem B1731695 : Blo 1152637 1731695 := bstep (se 1 (by rfl) ⟨1298771, by rfl⟩ : syracuseStep 1731695 = 2597543) B2597543
theorem B1731791 : Blo 1152637 1731791 := bstep (se 1 (by rfl) ⟨1298843, by rfl⟩ : syracuseStep 1731791 = 2597687) B2597687
theorem B1731911 : Blo 1152637 1731911 := bstep (se 1 (by rfl) ⟨1298933, by rfl⟩ : syracuseStep 1731911 = 2597867) B2597867
theorem B1732199 : Blo 1152637 1732199 := bstep (se 1 (by rfl) ⟨1299149, by rfl⟩ : syracuseStep 1732199 = 2598299) B2598299
theorem B3043063 : Blo 1152637 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B14020391 : Blo 1152637 14020391 := bstep (se 1 (by rfl) ⟨10515293, by rfl⟩ : syracuseStep 14020391 = 21030587) B21030587
theorem B1732583 : Blo 1152637 1732583 := bstep (se 1 (by rfl) ⟨1299437, by rfl⟩ : syracuseStep 1732583 = 2598875) B2598875
theorem B7401527 : Blo 1152637 7401527 := bstep (se 1 (by rfl) ⟨5551145, by rfl⟩ : syracuseStep 7401527 = 11102291) B11102291
theorem B1732703 : Blo 1152637 1732703 := bstep (se 1 (by rfl) ⟨1299527, by rfl⟩ : syracuseStep 1732703 = 2599055) B2599055
theorem B1732763 : Blo 1152637 1732763 := bstep (se 1 (by rfl) ⟨1299572, by rfl⟩ : syracuseStep 1732763 = 2599145) B2599145
theorem B1732943 : Blo 1152637 1732943 := bstep (se 1 (by rfl) ⟨1299707, by rfl⟩ : syracuseStep 1732943 = 2599415) B2599415
theorem B1733033 : Blo 1152637 1733033 := bstep (se 2 (by rfl) ⟨649887, by rfl⟩ : syracuseStep 1733033 = 1299775) B1299775
theorem B1733339 : Blo 1152637 1733339 := bstep (se 1 (by rfl) ⟨1300004, by rfl⟩ : syracuseStep 1733339 = 2600009) B2600009
theorem B7107425 : Blo 1152637 7107425 := bstep (se 2 (by rfl) ⟨2665284, by rfl⟩ : syracuseStep 7107425 = 5330569) B5330569
theorem B1733609 : Blo 1152637 1733609 := bstep (se 2 (by rfl) ⟨650103, by rfl⟩ : syracuseStep 1733609 = 1300207) B1300207
theorem B9860089 : Blo 1152637 9860089 := bstep (se 2 (by rfl) ⟨3697533, by rfl⟩ : syracuseStep 9860089 = 7395067) B7395067
theorem B1733753 : Blo 1152637 1733753 := bstep (se 2 (by rfl) ⟨650157, by rfl⟩ : syracuseStep 1733753 = 1300315) B1300315
theorem B7501369 : Blo 1152637 7501369 := bstep (se 2 (by rfl) ⟨2813013, by rfl⟩ : syracuseStep 7501369 = 5626027) B5626027
theorem B4388489 : Blo 1152637 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B1734281 : Blo 1152637 1734281 := bstep (se 2 (by rfl) ⟨650355, by rfl⟩ : syracuseStep 1734281 = 1300711) B1300711
theorem B3897071 : Blo 1152637 3897071 := bstep (se 1 (by rfl) ⟨2922803, by rfl⟩ : syracuseStep 3897071 = 5845607) B5845607
theorem B1734491 : Blo 1152637 1734491 := bstep (se 1 (by rfl) ⟨1300868, by rfl⟩ : syracuseStep 1734491 = 2601737) B2601737
theorem B1734527 : Blo 1152637 1734527 := bstep (se 1 (by rfl) ⟨1300895, by rfl⟩ : syracuseStep 1734527 = 2601791) B2601791
theorem B1734623 : Blo 1152637 1734623 := bstep (se 1 (by rfl) ⟨1300967, by rfl⟩ : syracuseStep 1734623 = 2601935) B2601935
theorem B1734683 : Blo 1152637 1734683 := bstep (se 1 (by rfl) ⟨1301012, by rfl⟩ : syracuseStep 1734683 = 2602025) B2602025
theorem B2193455 : Blo 1152637 2193455 := bstep (se 1 (by rfl) ⟨1645091, by rfl⟩ : syracuseStep 2193455 = 3290183) B3290183
theorem B5273747 : Blo 1152637 5273747 := bstep (se 1 (by rfl) ⟨3955310, by rfl⟩ : syracuseStep 5273747 = 7910621) B7910621
theorem B1734875 : Blo 1152637 1734875 := bstep (se 1 (by rfl) ⟨1301156, by rfl⟩ : syracuseStep 1734875 = 2602313) B2602313
theorem B7403987 : Blo 1152637 7403987 := bstep (se 1 (by rfl) ⟨5552990, by rfl⟩ : syracuseStep 7403987 = 11105981) B11105981
theorem B3505295 : Blo 1152637 3505295 := bstep (se 1 (by rfl) ⟨2628971, by rfl⟩ : syracuseStep 3505295 = 5257943) B5257943
theorem B4684999 : Blo 1152637 4684999 := bstep (se 1 (by rfl) ⟨3513749, by rfl⟩ : syracuseStep 4684999 = 7027499) B7027499
theorem B19004669 : Blo 1152637 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B3702199 : Blo 1152637 3702199 := bstep (se 1 (by rfl) ⟨2776649, by rfl⟩ : syracuseStep 3702199 = 5553299) B5553299
theorem B36044471 : Blo 1152637 36044471 := bstep (se 1 (by rfl) ⟨27033353, by rfl⟩ : syracuseStep 36044471 = 54066707) B54066707
theorem B3899879 : Blo 1152637 3899879 := bstep (se 1 (by rfl) ⟨2924909, by rfl⟩ : syracuseStep 3899879 = 5849819) B5849819
theorem B3900635 : Blo 1152637 3900635 := bstep (se 1 (by rfl) ⟨2925476, by rfl⟩ : syracuseStep 3900635 = 5850953) B5850953
theorem B38438327 : Blo 1152637 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B12486403 : Blo 1152637 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B7899169 : Blo 1152637 7899169 := bstep (se 2 (by rfl) ⟨2962188, by rfl⟩ : syracuseStep 7899169 = 5924377) B5924377
theorem B3704915 : Blo 1152637 3704915 := bstep (se 1 (by rfl) ⟨2778686, by rfl⟩ : syracuseStep 3704915 = 5557373) B5557373
theorem B19696121 : Blo 1152637 19696121 := bstep (se 2 (by rfl) ⟨7386045, by rfl⟩ : syracuseStep 19696121 = 14772091) B14772091
theorem B5540345 : Blo 1152637 5540345 := bstep (se 2 (by rfl) ⟨2077629, by rfl⟩ : syracuseStep 5540345 = 4155259) B4155259
theorem B1641503 : Blo 1152637 1641503 := bstep (se 1 (by rfl) ⟨1231127, by rfl⟩ : syracuseStep 1641503 = 2462255) B2462255
theorem B14028137 : Blo 1152637 14028137 := bstep (se 2 (by rfl) ⟨5260551, by rfl⟩ : syracuseStep 14028137 = 10521103) B10521103
theorem B17764271 : Blo 1152637 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B112300127 : Blo 1152637 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B3379709 : Blo 1152637 3379709 := bstep (se 3 (by rfl) ⟨633695, by rfl⟩ : syracuseStep 3379709 = 1267391) B1267391
theorem B2921255 : Blo 1152637 2921255 := bstep (se 1 (by rfl) ⟨2190941, by rfl⟩ : syracuseStep 2921255 = 4381883) B4381883
theorem B2593673 : Blo 1152637 2593673 := bstep (se 2 (by rfl) ⟨972627, by rfl⟩ : syracuseStep 2593673 = 1945255) B1945255
theorem B2462699 : Blo 1152637 2462699 := bstep (se 1 (by rfl) ⟨1847024, by rfl⟩ : syracuseStep 2462699 = 3694049) B3694049
theorem B252843443 : Blo 1152637 252843443 := bstep (se 1 (by rfl) ⟨189632582, by rfl⟩ : syracuseStep 252843443 = 379265165) B379265165
theorem B4167107 : Blo 1152637 4167107 := bstep (se 1 (by rfl) ⟨3125330, by rfl⟩ : syracuseStep 4167107 = 6250661) B6250661
theorem B1152719 : Blo 1152637 1152719 := bstep (se 1 (by rfl) ⟨864539, by rfl⟩ : syracuseStep 1152719 = 1729079) B1729079
theorem B8001371 : Blo 1152637 8001371 := bstep (se 1 (by rfl) ⟨6001028, by rfl⟩ : syracuseStep 8001371 = 12002057) B12002057
theorem B1152959 : Blo 1152637 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B2922439 : Blo 1152637 2922439 := bstep (se 1 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 2922439 = 4383659) B4383659
theorem B1153151 : Blo 1152637 1153151 := bstep (se 1 (by rfl) ⟨864863, by rfl⟩ : syracuseStep 1153151 = 1729727) B1729727
theorem B1153247 : Blo 1152637 1153247 := bstep (se 1 (by rfl) ⟨864935, by rfl⟩ : syracuseStep 1153247 = 1729871) B1729871
theorem B1153307 : Blo 1152637 1153307 := bstep (se 1 (by rfl) ⟨864980, by rfl⟩ : syracuseStep 1153307 = 1729961) B1729961
theorem B1153407 : Blo 1152637 1153407 := bstep (se 1 (by rfl) ⟨865055, by rfl⟩ : syracuseStep 1153407 = 1730111) B1730111
theorem B2595383 : Blo 1152637 2595383 := bstep (se 1 (by rfl) ⟨1946537, by rfl⟩ : syracuseStep 2595383 = 3893075) B3893075
theorem B1153647 : Blo 1152637 1153647 := bstep (se 1 (by rfl) ⟨865235, by rfl⟩ : syracuseStep 1153647 = 1730471) B1730471
theorem B13146785 : Blo 1152637 13146785 := bstep (se 2 (by rfl) ⟨4930044, by rfl⟩ : syracuseStep 13146785 = 9860089) B9860089
theorem B1153727 : Blo 1152637 1153727 := bstep (se 1 (by rfl) ⟨865295, by rfl⟩ : syracuseStep 1153727 = 1730591) B1730591
theorem B1154031 : Blo 1152637 1154031 := bstep (se 1 (by rfl) ⟨865523, by rfl⟩ : syracuseStep 1154031 = 1731047) B1731047
theorem B1154151 : Blo 1152637 1154151 := bstep (se 1 (by rfl) ⟨865613, by rfl⟩ : syracuseStep 1154151 = 1731227) B1731227
theorem B1154299 : Blo 1152637 1154299 := bstep (se 1 (by rfl) ⟨865724, by rfl⟩ : syracuseStep 1154299 = 1731449) B1731449
theorem B1154463 : Blo 1152637 1154463 := bstep (se 1 (by rfl) ⟨865847, by rfl⟩ : syracuseStep 1154463 = 1731695) B1731695
theorem B10001825 : Blo 1152637 10001825 := bstep (se 2 (by rfl) ⟨3750684, by rfl⟩ : syracuseStep 10001825 = 7501369) B7501369
theorem B1154527 : Blo 1152637 1154527 := bstep (se 1 (by rfl) ⟨865895, by rfl⟩ : syracuseStep 1154527 = 1731791) B1731791
theorem B1154607 : Blo 1152637 1154607 := bstep (se 1 (by rfl) ⟨865955, by rfl⟩ : syracuseStep 1154607 = 1731911) B1731911
theorem B1154799 : Blo 1152637 1154799 := bstep (se 1 (by rfl) ⟨866099, by rfl⟩ : syracuseStep 1154799 = 1732199) B1732199
theorem B9346927 : Blo 1152637 9346927 := bstep (se 1 (by rfl) ⟨7010195, by rfl⟩ : syracuseStep 9346927 = 14020391) B14020391
theorem B1155055 : Blo 1152637 1155055 := bstep (se 1 (by rfl) ⟨866291, by rfl⟩ : syracuseStep 1155055 = 1732583) B1732583
theorem B1155135 : Blo 1152637 1155135 := bstep (se 1 (by rfl) ⟨866351, by rfl⟩ : syracuseStep 1155135 = 1732703) B1732703
theorem B1155175 : Blo 1152637 1155175 := bstep (se 1 (by rfl) ⟨866381, by rfl⟩ : syracuseStep 1155175 = 1732763) B1732763
theorem B1155295 : Blo 1152637 1155295 := bstep (se 1 (by rfl) ⟨866471, by rfl⟩ : syracuseStep 1155295 = 1732943) B1732943
theorem B1155355 : Blo 1152637 1155355 := bstep (se 1 (by rfl) ⟨866516, by rfl⟩ : syracuseStep 1155355 = 1733033) B1733033
theorem B1155559 : Blo 1152637 1155559 := bstep (se 1 (by rfl) ⟨866669, by rfl⟩ : syracuseStep 1155559 = 1733339) B1733339
theorem B1155739 : Blo 1152637 1155739 := bstep (se 1 (by rfl) ⟨866804, by rfl⟩ : syracuseStep 1155739 = 1733609) B1733609
theorem B1155835 : Blo 1152637 1155835 := bstep (se 1 (by rfl) ⟨866876, by rfl⟩ : syracuseStep 1155835 = 1733753) B1733753
theorem B11084687 : Blo 1152637 11084687 := bstep (se 1 (by rfl) ⟨8313515, by rfl⟩ : syracuseStep 11084687 = 16627031) B16627031
theorem B2925659 : Blo 1152637 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B1156187 : Blo 1152637 1156187 := bstep (se 1 (by rfl) ⟨867140, by rfl⟩ : syracuseStep 1156187 = 1734281) B1734281
theorem B2598047 : Blo 1152637 2598047 := bstep (se 1 (by rfl) ⟨1948535, by rfl⟩ : syracuseStep 2598047 = 3897071) B3897071
theorem B1156327 : Blo 1152637 1156327 := bstep (se 1 (by rfl) ⟨867245, by rfl⟩ : syracuseStep 1156327 = 1734491) B1734491
theorem B1156351 : Blo 1152637 1156351 := bstep (se 1 (by rfl) ⟨867263, by rfl⟩ : syracuseStep 1156351 = 1734527) B1734527
theorem B1156415 : Blo 1152637 1156415 := bstep (se 1 (by rfl) ⟨867311, by rfl⟩ : syracuseStep 1156415 = 1734623) B1734623
theorem B1156455 : Blo 1152637 1156455 := bstep (se 1 (by rfl) ⟨867341, by rfl⟩ : syracuseStep 1156455 = 1734683) B1734683
theorem B3515831 : Blo 1152637 3515831 := bstep (se 1 (by rfl) ⟨2636873, by rfl⟩ : syracuseStep 3515831 = 5273747) B5273747
theorem B1156583 : Blo 1152637 1156583 := bstep (se 1 (by rfl) ⟨867437, by rfl⟩ : syracuseStep 1156583 = 1734875) B1734875
theorem B1386191 : Blo 1152637 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B96118589 : Blo 1152637 96118589 := bstep (se 3 (by rfl) ⟨18022235, by rfl⟩ : syracuseStep 96118589 = 36044471) B36044471
theorem B2336863 : Blo 1152637 2336863 := bstep (se 1 (by rfl) ⟨1752647, by rfl⟩ : syracuseStep 2336863 = 3505295) B3505295
theorem B2468713 : Blo 1152637 2468713 := bstep (se 2 (by rfl) ⟨925767, by rfl⟩ : syracuseStep 2468713 = 1851535) B1851535
theorem B19704869 : Blo 1152637 19704869 := bstep (se 4 (by rfl) ⟨1847331, by rfl⟩ : syracuseStep 19704869 = 3694663) B3694663
theorem B2469055 : Blo 1152637 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B2600351 : Blo 1152637 2600351 := bstep (se 1 (by rfl) ⟨1950263, by rfl⟩ : syracuseStep 2600351 = 3900527) B3900527
theorem B14037137 : Blo 1152637 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B1945883 : Blo 1152637 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B3289385 : Blo 1152637 3289385 := bstep (se 2 (by rfl) ⟨1233519, by rfl⟩ : syracuseStep 3289385 = 2467039) B2467039
theorem B1945903 : Blo 1152637 1945903 := bstep (se 1 (by rfl) ⟨1459427, by rfl⟩ : syracuseStep 1945903 = 2918855) B2918855
theorem B3289967 : Blo 1152637 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B14791571 : Blo 1152637 14791571 := bstep (se 1 (by rfl) ⟨11093678, by rfl⟩ : syracuseStep 14791571 = 22187357) B22187357
theorem B6566993 : Blo 1152637 6566993 := bstep (se 2 (by rfl) ⟨2462622, by rfl⟩ : syracuseStep 6566993 = 4925245) B4925245
theorem B2602295 : Blo 1152637 2602295 := bstep (se 1 (by rfl) ⟨1951721, by rfl⟩ : syracuseStep 2602295 = 3903443) B3903443
theorem B9483803 : Blo 1152637 9483803 := bstep (se 1 (by rfl) ⟨7112852, by rfl⟩ : syracuseStep 9483803 = 14225705) B14225705
theorem B22230719 : Blo 1152637 22230719 := bstep (se 1 (by rfl) ⟨16673039, by rfl⟩ : syracuseStep 22230719 = 33346079) B33346079
theorem B1948063 : Blo 1152637 1948063 := bstep (se 1 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 1948063 = 2922095) B2922095
theorem B4569655 : Blo 1152637 4569655 := bstep (se 1 (by rfl) ⟨3427241, by rfl⟩ : syracuseStep 4569655 = 6854483) B6854483
theorem B1948745 : Blo 1152637 1948745 := bstep (se 2 (by rfl) ⟨730779, by rfl⟩ : syracuseStep 1948745 = 1461559) B1461559
theorem B26983639 : Blo 1152637 26983639 := bstep (se 1 (by rfl) ⟨20237729, by rfl⟩ : syracuseStep 26983639 = 40475459) B40475459
theorem B1850779 : Blo 1152637 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B1949339 : Blo 1152637 1949339 := bstep (se 1 (by rfl) ⟨1462004, by rfl⟩ : syracuseStep 1949339 = 2924009) B2924009
theorem B1851689 : Blo 1152637 1851689 := bstep (se 2 (by rfl) ⟨694383, by rfl⟩ : syracuseStep 1851689 = 1388767) B1388767
theorem B6013703 : Blo 1152637 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B1950527 : Blo 1152637 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B6243551 : Blo 1152637 6243551 := bstep (se 1 (by rfl) ⟨4682663, by rfl⟩ : syracuseStep 6243551 = 9365327) B9365327
theorem B15811919 : Blo 1152637 15811919 := bstep (se 1 (by rfl) ⟨11858939, by rfl⟩ : syracuseStep 15811919 = 23717879) B23717879
theorem B1951391 : Blo 1152637 1951391 := bstep (se 1 (by rfl) ⟨1463543, by rfl⟩ : syracuseStep 1951391 = 2927087) B2927087
theorem B1951465 : Blo 1152637 1951465 := bstep (se 2 (by rfl) ⟨731799, by rfl⟩ : syracuseStep 1951465 = 1463599) B1463599
theorem B37472057 : Blo 1152637 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B16664393 : Blo 1152637 16664393 := bstep (se 2 (by rfl) ⟨6249147, by rfl⟩ : syracuseStep 16664393 = 12498295) B12498295
theorem B5851115 : Blo 1152637 5851115 := bstep (se 1 (by rfl) ⟨4388336, by rfl⟩ : syracuseStep 5851115 = 8776673) B8776673
theorem B8898767 : Blo 1152637 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B4934351 : Blo 1152637 4934351 := bstep (se 1 (by rfl) ⟨3700763, by rfl⟩ : syracuseStep 4934351 = 7401527) B7401527
theorem B4377311 : Blo 1152637 4377311 := bstep (se 1 (by rfl) ⟨3282983, by rfl⟩ : syracuseStep 4377311 = 6565967) B6565967
theorem B1297615 : Blo 1152637 1297615 := bstep (se 1 (by rfl) ⟨973211, by rfl⟩ : syracuseStep 1297615 = 1946423) B1946423
theorem B4738283 : Blo 1152637 4738283 := bstep (se 1 (by rfl) ⟨3553712, by rfl⟩ : syracuseStep 4738283 = 7107425) B7107425
theorem B1462303 : Blo 1152637 1462303 := bstep (se 1 (by rfl) ⟨1096727, by rfl⟩ : syracuseStep 1462303 = 2193455) B2193455
theorem B1298623 : Blo 1152637 1298623 := bstep (se 1 (by rfl) ⟨973967, by rfl⟩ : syracuseStep 1298623 = 1947935) B1947935
theorem B6246665 : Blo 1152637 6246665 := bstep (se 2 (by rfl) ⟨2342499, by rfl⟩ : syracuseStep 6246665 = 4684999) B4684999
theorem B4935991 : Blo 1152637 4935991 := bstep (se 1 (by rfl) ⟨3701993, by rfl⟩ : syracuseStep 4935991 = 7403987) B7403987
theorem B1298767 : Blo 1152637 1298767 := bstep (se 1 (by rfl) ⟨974075, by rfl⟩ : syracuseStep 1298767 = 1948151) B1948151
theorem B4936265 : Blo 1152637 4936265 := bstep (se 2 (by rfl) ⟨1851099, by rfl⟩ : syracuseStep 4936265 = 3702199) B3702199
theorem B12669779 : Blo 1152637 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B1299487 : Blo 1152637 1299487 := bstep (se 1 (by rfl) ⟨974615, by rfl⟩ : syracuseStep 1299487 = 1949231) B1949231
theorem B5854841 : Blo 1152637 5854841 := bstep (se 2 (by rfl) ⟨2195565, by rfl⟩ : syracuseStep 5854841 = 4391131) B4391131
theorem B4380713 : Blo 1152637 4380713 := bstep (se 2 (by rfl) ⟨1642767, by rfl⟩ : syracuseStep 4380713 = 3285535) B3285535
theorem B3890267 : Blo 1152637 3890267 := bstep (se 1 (by rfl) ⟨2917700, by rfl⟩ : syracuseStep 3890267 = 5835401) B5835401
theorem B9494441 : Blo 1152637 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B2777323 : Blo 1152637 2777323 := bstep (se 1 (by rfl) ⟨2082992, by rfl⟩ : syracuseStep 2777323 = 4165985) B4165985
theorem B9364187 : Blo 1152637 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B3891995 : Blo 1152637 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B4678559 : Blo 1152637 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B3892157 : Blo 1152637 3892157 := bstep (se 3 (by rfl) ⟨729779, by rfl⟩ : syracuseStep 3892157 = 1459559) B1459559
theorem B1729487 : Blo 1152637 1729487 := bstep (se 1 (by rfl) ⟨1297115, by rfl⟩ : syracuseStep 1729487 = 2594231) B2594231
theorem B1729535 : Blo 1152637 1729535 := bstep (se 1 (by rfl) ⟨1297151, by rfl⟩ : syracuseStep 1729535 = 2594303) B2594303
theorem B3892265 : Blo 1152637 3892265 := bstep (se 2 (by rfl) ⟨1459599, by rfl⟩ : syracuseStep 3892265 = 2919199) B2919199
theorem B1729607 : Blo 1152637 1729607 := bstep (se 1 (by rfl) ⟨1297205, by rfl⟩ : syracuseStep 1729607 = 2594411) B2594411
theorem B1729787 : Blo 1152637 1729787 := bstep (se 1 (by rfl) ⟨1297340, by rfl⟩ : syracuseStep 1729787 = 2594681) B2594681
theorem B2188937 : Blo 1152637 2188937 := bstep (se 2 (by rfl) ⟨820851, by rfl⟩ : syracuseStep 2188937 = 1641703) B1641703
theorem B3892967 : Blo 1152637 3892967 := bstep (se 1 (by rfl) ⟨2919725, by rfl⟩ : syracuseStep 3892967 = 5839451) B5839451
theorem B1730303 : Blo 1152637 1730303 := bstep (se 1 (by rfl) ⟨1297727, by rfl⟩ : syracuseStep 1730303 = 2595455) B2595455
theorem B1730375 : Blo 1152637 1730375 := bstep (se 1 (by rfl) ⟨1297781, by rfl⟩ : syracuseStep 1730375 = 2595563) B2595563
theorem B3893129 : Blo 1152637 3893129 := bstep (se 2 (by rfl) ⟨1459923, by rfl⟩ : syracuseStep 3893129 = 2919847) B2919847
theorem B1730555 : Blo 1152637 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B1730615 : Blo 1152637 1730615 := bstep (se 1 (by rfl) ⟨1297961, by rfl⟩ : syracuseStep 1730615 = 2595923) B2595923
theorem B1730735 : Blo 1152637 1730735 := bstep (se 1 (by rfl) ⟨1298051, by rfl⟩ : syracuseStep 1730735 = 2596103) B2596103
theorem B4057417 : Blo 1152637 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B1730975 : Blo 1152637 1730975 := bstep (se 1 (by rfl) ⟨1298231, by rfl⟩ : syracuseStep 1730975 = 2596463) B2596463
theorem B1731167 : Blo 1152637 1731167 := bstep (se 1 (by rfl) ⟨1298375, by rfl⟩ : syracuseStep 1731167 = 2596751) B2596751
theorem B1731239 : Blo 1152637 1731239 := bstep (se 1 (by rfl) ⟨1298429, by rfl⟩ : syracuseStep 1731239 = 2596859) B2596859
theorem B1731305 : Blo 1152637 1731305 := bstep (se 2 (by rfl) ⟨649239, by rfl⟩ : syracuseStep 1731305 = 1298479) B1298479
theorem B1731359 : Blo 1152637 1731359 := bstep (se 1 (by rfl) ⟨1298519, by rfl⟩ : syracuseStep 1731359 = 2597039) B2597039
theorem B1731527 : Blo 1152637 1731527 := bstep (se 1 (by rfl) ⟨1298645, by rfl⟩ : syracuseStep 1731527 = 2597291) B2597291
theorem B1731647 : Blo 1152637 1731647 := bstep (se 1 (by rfl) ⟨1298735, by rfl⟩ : syracuseStep 1731647 = 2597471) B2597471
theorem B1731839 : Blo 1152637 1731839 := bstep (se 1 (by rfl) ⟨1298879, by rfl⟩ : syracuseStep 1731839 = 2597759) B2597759
theorem B1731887 : Blo 1152637 1731887 := bstep (se 1 (by rfl) ⟨1298915, by rfl⟩ : syracuseStep 1731887 = 2597831) B2597831
theorem B1732073 : Blo 1152637 1732073 := bstep (se 2 (by rfl) ⟨649527, by rfl⟩ : syracuseStep 1732073 = 1299055) B1299055
theorem B1732127 : Blo 1152637 1732127 := bstep (se 1 (by rfl) ⟨1299095, by rfl⟩ : syracuseStep 1732127 = 2598191) B2598191
theorem B35549117 : Blo 1152637 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B11104289 : Blo 1152637 11104289 := bstep (se 2 (by rfl) ⟨4164108, by rfl⟩ : syracuseStep 11104289 = 8328217) B8328217
theorem B9991295 : Blo 1152637 9991295 := bstep (se 1 (by rfl) ⟨7493471, by rfl⟩ : syracuseStep 9991295 = 14986943) B14986943
theorem B1733759 : Blo 1152637 1733759 := bstep (se 1 (by rfl) ⟨1300319, by rfl⟩ : syracuseStep 1733759 = 2600639) B2600639
theorem B42104245 : Blo 1152637 42104245 := bstep (se 5 (by rfl) ⟨1973636, by rfl⟩ : syracuseStep 42104245 = 3947273) B3947273
theorem B1734143 : Blo 1152637 1734143 := bstep (se 1 (by rfl) ⟨1300607, by rfl⟩ : syracuseStep 1734143 = 2601215) B2601215
theorem B2192969 : Blo 1152637 2192969 := bstep (se 2 (by rfl) ⟨822363, by rfl⟩ : syracuseStep 2192969 = 1644727) B1644727
theorem B3897179 : Blo 1152637 3897179 := bstep (se 1 (by rfl) ⟨2922884, by rfl⟩ : syracuseStep 3897179 = 5845769) B5845769
theorem B1734521 : Blo 1152637 1734521 := bstep (se 2 (by rfl) ⟨650445, by rfl⟩ : syracuseStep 1734521 = 1300891) B1300891
theorem B1734911 : Blo 1152637 1734911 := bstep (se 1 (by rfl) ⟨1301183, by rfl⟩ : syracuseStep 1734911 = 2602367) B2602367
theorem B2193743 : Blo 1152637 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B4159841 : Blo 1152637 4159841 := bstep (se 2 (by rfl) ⟨1559940, by rfl⟩ : syracuseStep 4159841 = 3119881) B3119881
theorem B3897719 : Blo 1152637 3897719 := bstep (se 1 (by rfl) ⟨2923289, by rfl⟩ : syracuseStep 3897719 = 5846579) B5846579
theorem B25000487 : Blo 1152637 25000487 := bstep (se 1 (by rfl) ⟨18750365, by rfl⟩ : syracuseStep 25000487 = 37500731) B37500731
theorem B6584921 : Blo 1152637 6584921 := bstep (se 2 (by rfl) ⟨2469345, by rfl⟩ : syracuseStep 6584921 = 4938691) B4938691
theorem B3898043 : Blo 1152637 3898043 := bstep (se 1 (by rfl) ⟨2923532, by rfl⟩ : syracuseStep 3898043 = 5847065) B5847065
theorem B4750319 : Blo 1152637 4750319 := bstep (se 1 (by rfl) ⟨3562739, by rfl⟩ : syracuseStep 4750319 = 7125479) B7125479
theorem B6585695 : Blo 1152637 6585695 := bstep (se 1 (by rfl) ⟨4939271, by rfl⟩ : syracuseStep 6585695 = 9878543) B9878543
theorem B54033761 : Blo 1152637 54033761 := bstep (se 2 (by rfl) ⟨20262660, by rfl⟩ : syracuseStep 54033761 = 40525321) B40525321
theorem B3898799 : Blo 1152637 3898799 := bstep (se 1 (by rfl) ⟨2924099, by rfl⟩ : syracuseStep 3898799 = 5848199) B5848199
theorem B3898907 : Blo 1152637 3898907 := bstep (se 1 (by rfl) ⟨2924180, by rfl⟩ : syracuseStep 3898907 = 5848361) B5848361
theorem B3703097 : Blo 1152637 3703097 := bstep (se 2 (by rfl) ⟨1388661, by rfl⟩ : syracuseStep 3703097 = 2777323) B2777323
theorem B4162367 : Blo 1152637 4162367 := bstep (se 1 (by rfl) ⟨3121775, by rfl⟩ : syracuseStep 4162367 = 6243551) B6243551
theorem B11109595 : Blo 1152637 11109595 := bstep (se 1 (by rfl) ⟨8332196, by rfl⟩ : syracuseStep 11109595 = 16664393) B16664393
theorem B3900743 : Blo 1152637 3900743 := bstep (se 1 (by rfl) ⟨2925557, by rfl⟩ : syracuseStep 3900743 = 5851115) B5851115
theorem B5932511 : Blo 1152637 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B2918207 : Blo 1152637 2918207 := bstep (se 1 (by rfl) ⟨2188655, by rfl⟩ : syracuseStep 2918207 = 4377311) B4377311
theorem B24971165 : Blo 1152637 24971165 := bstep (se 3 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 24971165 = 9364187) B9364187
theorem B16648537 : Blo 1152637 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B3115817 : Blo 1152637 3115817 := bstep (se 2 (by rfl) ⟨1168431, by rfl⟩ : syracuseStep 3115817 = 2336863) B2336863
theorem B4164443 : Blo 1152637 4164443 := bstep (se 1 (by rfl) ⟨3123332, by rfl⟩ : syracuseStep 4164443 = 6246665) B6246665
theorem B1641799 : Blo 1152637 1641799 := bstep (se 1 (by rfl) ⟨1231349, by rfl⟩ : syracuseStep 1641799 = 2462699) B2462699
theorem B168562295 : Blo 1152637 168562295 := bstep (se 1 (by rfl) ⟨126421721, by rfl⟩ : syracuseStep 168562295 = 252843443) B252843443
theorem B3903227 : Blo 1152637 3903227 := bstep (se 1 (by rfl) ⟨2927420, by rfl⟩ : syracuseStep 3903227 = 5854841) B5854841
theorem B102502205 : Blo 1152637 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B2920475 : Blo 1152637 2920475 := bstep (se 1 (by rfl) ⟨2190356, by rfl⟩ : syracuseStep 2920475 = 4380713) B4380713
theorem B2593511 : Blo 1152637 2593511 := bstep (se 1 (by rfl) ⟨1945133, by rfl⟩ : syracuseStep 2593511 = 3890267) B3890267
theorem B6329627 : Blo 1152637 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B2594537 : Blo 1152637 2594537 := bstep (se 2 (by rfl) ⟨972951, by rfl⟩ : syracuseStep 2594537 = 1945903) B1945903
theorem B2594663 : Blo 1152637 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B3119039 : Blo 1152637 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B2594771 : Blo 1152637 2594771 := bstep (se 1 (by rfl) ⟨1946078, by rfl⟩ : syracuseStep 2594771 = 3892157) B3892157
theorem B1152991 : Blo 1152637 1152991 := bstep (se 1 (by rfl) ⟨864743, by rfl⟩ : syracuseStep 1152991 = 1729487) B1729487
theorem B1153023 : Blo 1152637 1153023 := bstep (se 1 (by rfl) ⟨864767, by rfl⟩ : syracuseStep 1153023 = 1729535) B1729535
theorem B2594843 : Blo 1152637 2594843 := bstep (se 1 (by rfl) ⟨1946132, by rfl⟩ : syracuseStep 2594843 = 3892265) B3892265
theorem B1153071 : Blo 1152637 1153071 := bstep (se 1 (by rfl) ⟨864803, by rfl⟩ : syracuseStep 1153071 = 1729607) B1729607
theorem B1153191 : Blo 1152637 1153191 := bstep (se 1 (by rfl) ⟨864893, by rfl⟩ : syracuseStep 1153191 = 1729787) B1729787
theorem B2595311 : Blo 1152637 2595311 := bstep (se 1 (by rfl) ⟨1946483, by rfl⟩ : syracuseStep 2595311 = 3892967) B3892967
theorem B1153535 : Blo 1152637 1153535 := bstep (se 1 (by rfl) ⟨865151, by rfl⟩ : syracuseStep 1153535 = 1730303) B1730303
theorem B1153583 : Blo 1152637 1153583 := bstep (se 1 (by rfl) ⟨865187, by rfl⟩ : syracuseStep 1153583 = 1730375) B1730375
theorem B2595419 : Blo 1152637 2595419 := bstep (se 1 (by rfl) ⟨1946564, by rfl⟩ : syracuseStep 2595419 = 3893129) B3893129
theorem B1153703 : Blo 1152637 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B1153743 : Blo 1152637 1153743 := bstep (se 1 (by rfl) ⟨865307, by rfl⟩ : syracuseStep 1153743 = 1730615) B1730615
theorem B1153823 : Blo 1152637 1153823 := bstep (se 1 (by rfl) ⟨865367, by rfl⟩ : syracuseStep 1153823 = 1730735) B1730735
theorem B1153983 : Blo 1152637 1153983 := bstep (se 1 (by rfl) ⟨865487, by rfl⟩ : syracuseStep 1153983 = 1730975) B1730975
theorem B1154111 : Blo 1152637 1154111 := bstep (se 1 (by rfl) ⟨865583, by rfl⟩ : syracuseStep 1154111 = 1731167) B1731167
theorem B1154159 : Blo 1152637 1154159 := bstep (se 1 (by rfl) ⟨865619, by rfl⟩ : syracuseStep 1154159 = 1731239) B1731239
theorem B1154203 : Blo 1152637 1154203 := bstep (se 1 (by rfl) ⟨865652, by rfl⟩ : syracuseStep 1154203 = 1731305) B1731305
theorem B1154239 : Blo 1152637 1154239 := bstep (se 1 (by rfl) ⟨865679, by rfl⟩ : syracuseStep 1154239 = 1731359) B1731359
theorem B56138993 : Blo 1152637 56138993 := bstep (se 2 (by rfl) ⟨21052122, by rfl⟩ : syracuseStep 56138993 = 42104245) B42104245
theorem B1154351 : Blo 1152637 1154351 := bstep (se 1 (by rfl) ⟨865763, by rfl⟩ : syracuseStep 1154351 = 1731527) B1731527
theorem B1154431 : Blo 1152637 1154431 := bstep (se 1 (by rfl) ⟨865823, by rfl⟩ : syracuseStep 1154431 = 1731647) B1731647
theorem B9870821 : Blo 1152637 9870821 := bstep (se 4 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 9870821 = 1850779) B1850779
theorem B1154559 : Blo 1152637 1154559 := bstep (se 1 (by rfl) ⟨865919, by rfl⟩ : syracuseStep 1154559 = 1731839) B1731839
theorem B1154591 : Blo 1152637 1154591 := bstep (se 1 (by rfl) ⟨865943, by rfl⟩ : syracuseStep 1154591 = 1731887) B1731887
theorem B1154715 : Blo 1152637 1154715 := bstep (se 1 (by rfl) ⟨866036, by rfl⟩ : syracuseStep 1154715 = 1732073) B1732073
theorem B1154751 : Blo 1152637 1154751 := bstep (se 1 (by rfl) ⟨866063, by rfl⟩ : syracuseStep 1154751 = 1732127) B1732127
theorem B23699411 : Blo 1152637 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B2597417 : Blo 1152637 2597417 := bstep (se 2 (by rfl) ⟨974031, by rfl⟩ : syracuseStep 2597417 = 1948063) B1948063
theorem B6660863 : Blo 1152637 6660863 := bstep (se 1 (by rfl) ⟨4995647, by rfl⟩ : syracuseStep 6660863 = 9991295) B9991295
theorem B1155839 : Blo 1152637 1155839 := bstep (se 1 (by rfl) ⟨866879, by rfl⟩ : syracuseStep 1155839 = 1733759) B1733759
theorem B144090029 : Blo 1152637 144090029 := bstep (se 3 (by rfl) ⟨27016880, by rfl⟩ : syracuseStep 144090029 = 54033761) B54033761
theorem B1156095 : Blo 1152637 1156095 := bstep (se 1 (by rfl) ⟨867071, by rfl⟩ : syracuseStep 1156095 = 1734143) B1734143
theorem B14820479 : Blo 1152637 14820479 := bstep (se 1 (by rfl) ⟨11115359, by rfl⟩ : syracuseStep 14820479 = 22230719) B22230719
theorem B2598119 : Blo 1152637 2598119 := bstep (se 1 (by rfl) ⟨1948589, by rfl⟩ : syracuseStep 2598119 = 3897179) B3897179
theorem B1156347 : Blo 1152637 1156347 := bstep (se 1 (by rfl) ⟨867260, by rfl⟩ : syracuseStep 1156347 = 1734521) B1734521
theorem B1156607 : Blo 1152637 1156607 := bstep (se 1 (by rfl) ⟨867455, by rfl⟩ : syracuseStep 1156607 = 1734911) B1734911
theorem B2598479 : Blo 1152637 2598479 := bstep (se 1 (by rfl) ⟨1948859, by rfl⟩ : syracuseStep 2598479 = 3897719) B3897719
theorem B2598695 : Blo 1152637 2598695 := bstep (se 1 (by rfl) ⟨1949021, by rfl⟩ : syracuseStep 2598695 = 3898043) B3898043
theorem B2599199 : Blo 1152637 2599199 := bstep (se 1 (by rfl) ⟨1949399, by rfl⟩ : syracuseStep 2599199 = 3898799) B3898799
theorem B2599271 : Blo 1152637 2599271 := bstep (se 1 (by rfl) ⟨1949453, by rfl⟩ : syracuseStep 2599271 = 3898907) B3898907
theorem B12462569 : Blo 1152637 12462569 := bstep (se 2 (by rfl) ⟨4673463, by rfl⟩ : syracuseStep 12462569 = 9346927) B9346927
theorem B2599919 : Blo 1152637 2599919 := bstep (se 1 (by rfl) ⟨1949939, by rfl⟩ : syracuseStep 2599919 = 3899879) B3899879
theorem B2600423 : Blo 1152637 2600423 := bstep (se 1 (by rfl) ⟨1950317, by rfl⟩ : syracuseStep 2600423 = 3900635) B3900635
theorem B24981371 : Blo 1152637 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B2469943 : Blo 1152637 2469943 := bstep (se 1 (by rfl) ⟨1852457, by rfl⟩ : syracuseStep 2469943 = 3704915) B3704915
theorem B21639557 : Blo 1152637 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B3289567 : Blo 1152637 3289567 := bstep (se 1 (by rfl) ⟨2467175, by rfl⟩ : syracuseStep 3289567 = 4934351) B4934351
theorem B16036541 : Blo 1152637 16036541 := bstep (se 3 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 16036541 = 6013703) B6013703
theorem B3158855 : Blo 1152637 3158855 := bstep (se 1 (by rfl) ⟨2369141, by rfl⟩ : syracuseStep 3158855 = 4738283) B4738283
theorem B9352091 : Blo 1152637 9352091 := bstep (se 1 (by rfl) ⟨7014068, by rfl⟩ : syracuseStep 9352091 = 14028137) B14028137
theorem B2601953 : Blo 1152637 2601953 := bstep (se 2 (by rfl) ⟨975732, by rfl⟩ : syracuseStep 2601953 = 1951465) B1951465
theorem B11842847 : Blo 1152637 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B10532225 : Blo 1152637 10532225 := bstep (se 2 (by rfl) ⟨3949584, by rfl⟩ : syracuseStep 10532225 = 7899169) B7899169
theorem B3290843 : Blo 1152637 3290843 := bstep (se 1 (by rfl) ⟨2468132, by rfl⟩ : syracuseStep 3290843 = 4936265) B4936265
theorem B1947503 : Blo 1152637 1947503 := bstep (se 1 (by rfl) ⟨1460627, by rfl⟩ : syracuseStep 1947503 = 2921255) B2921255
theorem B3291617 : Blo 1152637 3291617 := bstep (se 2 (by rfl) ⟨1234356, by rfl⟩ : syracuseStep 3291617 = 2468713) B2468713
theorem B3292073 : Blo 1152637 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B8764523 : Blo 1152637 8764523 := bstep (se 1 (by rfl) ⟨6573392, by rfl⟩ : syracuseStep 8764523 = 13146785) B13146785
theorem B6667883 : Blo 1152637 6667883 := bstep (se 1 (by rfl) ⟨5000912, by rfl⟩ : syracuseStep 6667883 = 10001825) B10001825
theorem B1949737 : Blo 1152637 1949737 := bstep (se 2 (by rfl) ⟨731151, by rfl⟩ : syracuseStep 1949737 = 1462303) B1462303
theorem B7389791 : Blo 1152637 7389791 := bstep (se 1 (by rfl) ⟨5542343, by rfl⟩ : syracuseStep 7389791 = 11084687) B11084687
theorem B1950439 : Blo 1152637 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B5849981 : Blo 1152637 5849981 := bstep (se 3 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 5849981 = 2193743) B2193743
theorem B11092909 : Blo 1152637 11092909 := bstep (se 3 (by rfl) ⟨2079920, by rfl⟩ : syracuseStep 11092909 = 4159841) B4159841
theorem B2343887 : Blo 1152637 2343887 := bstep (se 1 (by rfl) ⟨1757915, by rfl⟩ : syracuseStep 2343887 = 3515831) B3515831
theorem B1459291 : Blo 1152637 1459291 := bstep (se 1 (by rfl) ⟨1094468, by rfl⟩ : syracuseStep 1459291 = 2188937) B2188937
theorem B64079059 : Blo 1152637 64079059 := bstep (se 1 (by rfl) ⟨48059294, by rfl⟩ : syracuseStep 64079059 = 96118589) B96118589
theorem B4377341 : Blo 1152637 4377341 := bstep (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) B1641503
theorem B9358091 : Blo 1152637 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B1297255 : Blo 1152637 1297255 := bstep (se 1 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 1297255 = 1945883) B1945883
theorem B4377995 : Blo 1152637 4377995 := bstep (se 1 (by rfl) ⟨3283496, by rfl⟩ : syracuseStep 4377995 = 6566993) B6566993
theorem B1461979 : Blo 1152637 1461979 := bstep (se 1 (by rfl) ⟨1096484, by rfl⟩ : syracuseStep 1461979 = 2192969) B2192969
theorem B16666991 : Blo 1152637 16666991 := bstep (se 1 (by rfl) ⟨12500243, by rfl⟩ : syracuseStep 16666991 = 25000487) B25000487
theorem B3166879 : Blo 1152637 3166879 := bstep (se 1 (by rfl) ⟨2375159, by rfl⟩ : syracuseStep 3166879 = 4750319) B4750319
theorem B1299163 : Blo 1152637 1299163 := bstep (se 1 (by rfl) ⟨974372, by rfl⟩ : syracuseStep 1299163 = 1948745) B1948745
theorem B1299559 : Blo 1152637 1299559 := bstep (se 1 (by rfl) ⟨974669, by rfl⟩ : syracuseStep 1299559 = 1949339) B1949339
theorem B1234459 : Blo 1152637 1234459 := bstep (se 1 (by rfl) ⟨925844, by rfl⟩ : syracuseStep 1234459 = 1851689) B1851689
theorem B1300351 : Blo 1152637 1300351 := bstep (se 1 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 1300351 = 1950527) B1950527
theorem B10541279 : Blo 1152637 10541279 := bstep (se 1 (by rfl) ⟨7905959, by rfl⟩ : syracuseStep 10541279 = 15811919) B15811919
theorem B1300927 : Blo 1152637 1300927 := bstep (se 1 (by rfl) ⟨975695, by rfl⟩ : syracuseStep 1300927 = 1951391) B1951391
theorem B13130747 : Blo 1152637 13130747 := bstep (se 1 (by rfl) ⟨9848060, by rfl⟩ : syracuseStep 13130747 = 19696121) B19696121
theorem B3693563 : Blo 1152637 3693563 := bstep (se 1 (by rfl) ⟨2770172, by rfl⟩ : syracuseStep 3693563 = 5540345) B5540345
theorem B74866751 : Blo 1152637 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B2253139 : Blo 1152637 2253139 := bstep (se 1 (by rfl) ⟨1689854, by rfl⟩ : syracuseStep 2253139 = 3379709) B3379709
theorem B8446519 : Blo 1152637 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B1729115 : Blo 1152637 1729115 := bstep (se 1 (by rfl) ⟨1296836, by rfl⟩ : syracuseStep 1729115 = 2593673) B2593673
theorem B2778071 : Blo 1152637 2778071 := bstep (se 1 (by rfl) ⟨2083553, by rfl⟩ : syracuseStep 2778071 = 4167107) B4167107
theorem B5334247 : Blo 1152637 5334247 := bstep (se 1 (by rfl) ⟨4000685, by rfl⟩ : syracuseStep 5334247 = 8001371) B8001371
theorem B1730153 : Blo 1152637 1730153 := bstep (se 2 (by rfl) ⟨648807, by rfl⟩ : syracuseStep 1730153 = 1297615) B1297615
theorem B1730255 : Blo 1152637 1730255 := bstep (se 1 (by rfl) ⟨1297691, by rfl⟩ : syracuseStep 1730255 = 2595383) B2595383
theorem B3696509 : Blo 1152637 3696509 := bstep (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) B1386191
theorem B1731497 : Blo 1152637 1731497 := bstep (se 2 (by rfl) ⟨649311, by rfl⟩ : syracuseStep 1731497 = 1298623) B1298623
theorem B6581321 : Blo 1152637 6581321 := bstep (se 2 (by rfl) ⟨2467995, by rfl⟩ : syracuseStep 6581321 = 4935991) B4935991
theorem B1731689 : Blo 1152637 1731689 := bstep (se 2 (by rfl) ⟨649383, by rfl⟩ : syracuseStep 1731689 = 1298767) B1298767
theorem B1732031 : Blo 1152637 1732031 := bstep (se 1 (by rfl) ⟨1299023, by rfl⟩ : syracuseStep 1732031 = 2598047) B2598047
theorem B1732649 : Blo 1152637 1732649 := bstep (se 2 (by rfl) ⟨649743, by rfl⟩ : syracuseStep 1732649 = 1299487) B1299487
theorem B13136579 : Blo 1152637 13136579 := bstep (se 1 (by rfl) ⟨9852434, by rfl⟩ : syracuseStep 13136579 = 19704869) B19704869
theorem B1733567 : Blo 1152637 1733567 := bstep (se 1 (by rfl) ⟨1300175, by rfl⟩ : syracuseStep 1733567 = 2600351) B2600351
theorem B3896585 : Blo 1152637 3896585 := bstep (se 2 (by rfl) ⟨1461219, by rfl⟩ : syracuseStep 3896585 = 2922439) B2922439
theorem B7402859 : Blo 1152637 7402859 := bstep (se 1 (by rfl) ⟨5552144, by rfl⟩ : syracuseStep 7402859 = 11104289) B11104289
theorem B2192923 : Blo 1152637 2192923 := bstep (se 1 (by rfl) ⟨1644692, by rfl⟩ : syracuseStep 2192923 = 3289385) B3289385
theorem B2193311 : Blo 1152637 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B9861047 : Blo 1152637 9861047 := bstep (se 1 (by rfl) ⟨7395785, by rfl⟩ : syracuseStep 9861047 = 14791571) B14791571
theorem B6092873 : Blo 1152637 6092873 := bstep (se 2 (by rfl) ⟨2284827, by rfl⟩ : syracuseStep 6092873 = 4569655) B4569655
theorem B1734863 : Blo 1152637 1734863 := bstep (se 1 (by rfl) ⟨1301147, by rfl⟩ : syracuseStep 1734863 = 2602295) B2602295
theorem B6322535 : Blo 1152637 6322535 := bstep (se 1 (by rfl) ⟨4741901, by rfl⟩ : syracuseStep 6322535 = 9483803) B9483803
theorem B35978185 : Blo 1152637 35978185 := bstep (se 2 (by rfl) ⟨13491819, by rfl⟩ : syracuseStep 35978185 = 26983639) B26983639
theorem B4389947 : Blo 1152637 4389947 := bstep (se 1 (by rfl) ⟨3292460, by rfl⟩ : syracuseStep 4389947 = 6584921) B6584921
theorem B4390463 : Blo 1152637 4390463 := bstep (se 1 (by rfl) ⟨3292847, by rfl⟩ : syracuseStep 4390463 = 6585695) B6585695
theorem B13173029 : Blo 1152637 13173029 := bstep (se 4 (by rfl) ⟨1234971, by rfl⟩ : syracuseStep 13173029 = 2469943) B2469943
theorem B3899987 : Blo 1152637 3899987 := bstep (se 1 (by rfl) ⟨2924990, by rfl⟩ : syracuseStep 3899987 = 5849981) B5849981
theorem B16647443 : Blo 1152637 16647443 := bstep (se 1 (by rfl) ⟨12485582, by rfl⟩ : syracuseStep 16647443 = 24971165) B24971165
theorem B14812793 : Blo 1152637 14812793 := bstep (se 2 (by rfl) ⟨5554797, by rfl⟩ : syracuseStep 14812793 = 11109595) B11109595
theorem B7112329 : Blo 1152637 7112329 := bstep (se 2 (by rfl) ⟨2667123, by rfl⟩ : syracuseStep 7112329 = 5334247) B5334247
theorem B2918227 : Blo 1152637 2918227 := bstep (se 1 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 2918227 = 4377341) B4377341
theorem B2918663 : Blo 1152637 2918663 := bstep (se 1 (by rfl) ⟨2188997, by rfl⟩ : syracuseStep 2918663 = 4377995) B4377995
theorem B7408189 : Blo 1152637 7408189 := bstep (se 3 (by rfl) ⟨1389035, by rfl⟩ : syracuseStep 7408189 = 2778071) B2778071
theorem B11111327 : Blo 1152637 11111327 := bstep (se 1 (by rfl) ⟨8333495, by rfl⟩ : syracuseStep 11111327 = 16666991) B16666991
theorem B28085933 : Blo 1152637 28085933 := bstep (se 3 (by rfl) ⟨5266112, by rfl⟩ : syracuseStep 28085933 = 10532225) B10532225
theorem B8753831 : Blo 1152637 8753831 := bstep (se 1 (by rfl) ⟨6565373, by rfl⟩ : syracuseStep 8753831 = 13130747) B13130747
theorem B2462375 : Blo 1152637 2462375 := bstep (se 1 (by rfl) ⟨1846781, by rfl⟩ : syracuseStep 2462375 = 3693563) B3693563
theorem B37425995 : Blo 1152637 37425995 := bstep (se 1 (by rfl) ⟨28069496, by rfl⟩ : syracuseStep 37425995 = 56138993) B56138993
theorem B15799607 : Blo 1152637 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B49911167 : Blo 1152637 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B1152743 : Blo 1152637 1152743 := bstep (se 1 (by rfl) ⟨864557, by rfl⟩ : syracuseStep 1152743 = 1729115) B1729115
theorem B1153435 : Blo 1152637 1153435 := bstep (se 1 (by rfl) ⟨865076, by rfl⟩ : syracuseStep 1153435 = 1730153) B1730153
theorem B1153503 : Blo 1152637 1153503 := bstep (se 1 (by rfl) ⟨865127, by rfl⟩ : syracuseStep 1153503 = 1730255) B1730255
theorem B2464339 : Blo 1152637 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B8756261 : Blo 1152637 8756261 := bstep (se 4 (by rfl) ⟨820899, by rfl⟩ : syracuseStep 8756261 = 1641799) B1641799
theorem B1154331 : Blo 1152637 1154331 := bstep (se 1 (by rfl) ⟨865748, by rfl⟩ : syracuseStep 1154331 = 1731497) B1731497
theorem B2923897 : Blo 1152637 2923897 := bstep (se 2 (by rfl) ⟨1096461, by rfl⟩ : syracuseStep 2923897 = 2192923) B2192923
theorem B1154459 : Blo 1152637 1154459 := bstep (se 1 (by rfl) ⟨865844, by rfl⟩ : syracuseStep 1154459 = 1731689) B1731689
theorem B1154687 : Blo 1152637 1154687 := bstep (se 1 (by rfl) ⟨866015, by rfl⟩ : syracuseStep 1154687 = 1732031) B1732031
theorem B16654247 : Blo 1152637 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B1155099 : Blo 1152637 1155099 := bstep (se 1 (by rfl) ⟨866324, by rfl⟩ : syracuseStep 1155099 = 1732649) B1732649
theorem B14426371 : Blo 1152637 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B10691027 : Blo 1152637 10691027 := bstep (se 1 (by rfl) ⟨8018270, by rfl⟩ : syracuseStep 10691027 = 16036541) B16036541
theorem B8757719 : Blo 1152637 8757719 := bstep (se 1 (by rfl) ⟨6568289, by rfl⟩ : syracuseStep 8757719 = 13136579) B13136579
theorem B2105903 : Blo 1152637 2105903 := bstep (se 1 (by rfl) ⟨1579427, by rfl⟩ : syracuseStep 2105903 = 3158855) B3158855
theorem B6234727 : Blo 1152637 6234727 := bstep (se 1 (by rfl) ⟨4676045, by rfl⟩ : syracuseStep 6234727 = 9352091) B9352091
theorem B1155711 : Blo 1152637 1155711 := bstep (se 1 (by rfl) ⟨866783, by rfl⟩ : syracuseStep 1155711 = 1733567) B1733567
theorem B2597723 : Blo 1152637 2597723 := bstep (se 1 (by rfl) ⟨1948292, by rfl⟩ : syracuseStep 2597723 = 3896585) B3896585
theorem B1156575 : Blo 1152637 1156575 := bstep (se 1 (by rfl) ⟨867431, by rfl⟩ : syracuseStep 1156575 = 1734863) B1734863
theorem B2926631 : Blo 1152637 2926631 := bstep (se 1 (by rfl) ⟨2194973, by rfl⟩ : syracuseStep 2926631 = 4389947) B4389947
theorem B5843015 : Blo 1152637 5843015 := bstep (se 1 (by rfl) ⟨4382261, by rfl⟩ : syracuseStep 5843015 = 8764523) B8764523
theorem B2926975 : Blo 1152637 2926975 := bstep (se 1 (by rfl) ⟨2195231, by rfl⟩ : syracuseStep 2926975 = 4390463) B4390463
theorem B2599649 : Blo 1152637 2599649 := bstep (se 2 (by rfl) ⟨974868, by rfl⟩ : syracuseStep 2599649 = 1949737) B1949737
theorem B2468731 : Blo 1152637 2468731 := bstep (se 1 (by rfl) ⟨1851548, by rfl⟩ : syracuseStep 2468731 = 3703097) B3703097
theorem B4926527 : Blo 1152637 4926527 := bstep (se 1 (by rfl) ⟨3694895, by rfl⟩ : syracuseStep 4926527 = 7389791) B7389791
theorem B2600495 : Blo 1152637 2600495 := bstep (se 1 (by rfl) ⟨1950371, by rfl⟩ : syracuseStep 2600495 = 3900743) B3900743
theorem B2600585 : Blo 1152637 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B1945471 : Blo 1152637 1945471 := bstep (se 1 (by rfl) ⟨1459103, by rfl⟩ : syracuseStep 1945471 = 2918207) B2918207
theorem B14790545 : Blo 1152637 14790545 := bstep (se 2 (by rfl) ⟨5546454, by rfl⟩ : syracuseStep 14790545 = 11092909) B11092909
theorem B1945721 : Blo 1152637 1945721 := bstep (se 2 (by rfl) ⟨729645, by rfl⟩ : syracuseStep 1945721 = 1459291) B1459291
theorem B85438745 : Blo 1152637 85438745 := bstep (se 2 (by rfl) ⟨32039529, by rfl⟩ : syracuseStep 85438745 = 64079059) B64079059
theorem B6238727 : Blo 1152637 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B2077211 : Blo 1152637 2077211 := bstep (se 1 (by rfl) ⟨1557908, by rfl⟩ : syracuseStep 2077211 = 3115817) B3115817
theorem B112374863 : Blo 1152637 112374863 := bstep (se 1 (by rfl) ⟨84281147, by rfl⟩ : syracuseStep 112374863 = 168562295) B168562295
theorem B2602151 : Blo 1152637 2602151 := bstep (se 1 (by rfl) ⟨1951613, by rfl⟩ : syracuseStep 2602151 = 3903227) B3903227
theorem B68334803 : Blo 1152637 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B1946983 : Blo 1152637 1946983 := bstep (se 1 (by rfl) ⟨1460237, by rfl⟩ : syracuseStep 1946983 = 2920475) B2920475
theorem B22198049 : Blo 1152637 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B2079359 : Blo 1152637 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B7027519 : Blo 1152637 7027519 := bstep (se 1 (by rfl) ⟨5270639, by rfl⟩ : syracuseStep 7027519 = 10541279) B10541279
theorem B1949305 : Blo 1152637 1949305 := bstep (se 2 (by rfl) ⟨730989, by rfl⟩ : syracuseStep 1949305 = 1461979) B1461979
theorem B4440575 : Blo 1152637 4440575 := bstep (se 1 (by rfl) ⟨3330431, by rfl⟩ : syracuseStep 4440575 = 6660863) B6660863
theorem B96060019 : Blo 1152637 96060019 := bstep (se 1 (by rfl) ⟨72045014, by rfl⟩ : syracuseStep 96060019 = 144090029) B144090029
theorem B9880319 : Blo 1152637 9880319 := bstep (se 1 (by rfl) ⟨7410239, by rfl⟩ : syracuseStep 9880319 = 14820479) B14820479
theorem B8308379 : Blo 1152637 8308379 := bstep (se 1 (by rfl) ⟨6231284, by rfl⟩ : syracuseStep 8308379 = 12462569) B12462569
theorem B4935239 : Blo 1152637 4935239 := bstep (se 1 (by rfl) ⟨3701429, by rfl⟩ : syracuseStep 4935239 = 7402859) B7402859
theorem B1298335 : Blo 1152637 1298335 := bstep (se 1 (by rfl) ⟨973751, by rfl⟩ : syracuseStep 1298335 = 1947503) B1947503
theorem B1462207 : Blo 1152637 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B6574031 : Blo 1152637 6574031 := bstep (se 1 (by rfl) ⟨4930523, by rfl⟩ : syracuseStep 6574031 = 9861047) B9861047
theorem B4215023 : Blo 1152637 4215023 := bstep (se 1 (by rfl) ⟨3161267, by rfl⟩ : syracuseStep 4215023 = 6322535) B6322535
theorem B4445255 : Blo 1152637 4445255 := bstep (se 1 (by rfl) ⟨3333941, by rfl⟩ : syracuseStep 4445255 = 6667883) B6667883
theorem B2774911 : Blo 1152637 2774911 := bstep (se 1 (by rfl) ⟨2081183, by rfl⟩ : syracuseStep 2774911 = 4162367) B4162367
theorem B1562591 : Blo 1152637 1562591 := bstep (se 1 (by rfl) ⟨1171943, by rfl⟩ : syracuseStep 1562591 = 2343887) B2343887
theorem B11262025 : Blo 1152637 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B3955007 : Blo 1152637 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B2776295 : Blo 1152637 2776295 := bstep (se 1 (by rfl) ⟨2082221, by rfl⟩ : syracuseStep 2776295 = 4164443) B4164443
theorem B1729007 : Blo 1152637 1729007 := bstep (se 1 (by rfl) ⟨1296755, by rfl⟩ : syracuseStep 1729007 = 2593511) B2593511
theorem B4219751 : Blo 1152637 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B1729673 : Blo 1152637 1729673 := bstep (se 2 (by rfl) ⟨648627, by rfl⟩ : syracuseStep 1729673 = 1297255) B1297255
theorem B1729691 : Blo 1152637 1729691 := bstep (se 1 (by rfl) ⟨1297268, by rfl⟩ : syracuseStep 1729691 = 2594537) B2594537
theorem B1729775 : Blo 1152637 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B1729847 : Blo 1152637 1729847 := bstep (se 1 (by rfl) ⟨1297385, by rfl⟩ : syracuseStep 1729847 = 2594771) B2594771
theorem B1729895 : Blo 1152637 1729895 := bstep (se 1 (by rfl) ⟨1297421, by rfl⟩ : syracuseStep 1729895 = 2594843) B2594843
theorem B1730207 : Blo 1152637 1730207 := bstep (se 1 (by rfl) ⟨1297655, by rfl⟩ : syracuseStep 1730207 = 2595311) B2595311
theorem B1730279 : Blo 1152637 1730279 := bstep (se 1 (by rfl) ⟨1297709, by rfl⟩ : syracuseStep 1730279 = 2595419) B2595419
theorem B6580547 : Blo 1152637 6580547 := bstep (se 1 (by rfl) ⟨4935410, by rfl⟩ : syracuseStep 6580547 = 9870821) B9870821
theorem B1731611 : Blo 1152637 1731611 := bstep (se 1 (by rfl) ⟨1298708, by rfl⟩ : syracuseStep 1731611 = 2597417) B2597417
theorem B4386089 : Blo 1152637 4386089 := bstep (se 2 (by rfl) ⟨1644783, by rfl⟩ : syracuseStep 4386089 = 3289567) B3289567
theorem B1732079 : Blo 1152637 1732079 := bstep (se 1 (by rfl) ⟨1299059, by rfl⟩ : syracuseStep 1732079 = 2598119) B2598119
theorem B4222505 : Blo 1152637 4222505 := bstep (se 2 (by rfl) ⟨1583439, by rfl⟩ : syracuseStep 4222505 = 3166879) B3166879
theorem B1732217 : Blo 1152637 1732217 := bstep (se 2 (by rfl) ⟨649581, by rfl⟩ : syracuseStep 1732217 = 1299163) B1299163
theorem B1732319 : Blo 1152637 1732319 := bstep (se 1 (by rfl) ⟨1299239, by rfl⟩ : syracuseStep 1732319 = 2598479) B2598479
theorem B1732463 : Blo 1152637 1732463 := bstep (se 1 (by rfl) ⟨1299347, by rfl⟩ : syracuseStep 1732463 = 2598695) B2598695
theorem B8777645 : Blo 1152637 8777645 := bstep (se 3 (by rfl) ⟨1645808, by rfl⟩ : syracuseStep 8777645 = 3291617) B3291617
theorem B1732745 : Blo 1152637 1732745 := bstep (se 2 (by rfl) ⟨649779, by rfl⟩ : syracuseStep 1732745 = 1299559) B1299559
theorem B1732799 : Blo 1152637 1732799 := bstep (se 1 (by rfl) ⟨1299599, by rfl⟩ : syracuseStep 1732799 = 2599199) B2599199
theorem B1732847 : Blo 1152637 1732847 := bstep (se 1 (by rfl) ⟨1299635, by rfl⟩ : syracuseStep 1732847 = 2599271) B2599271
theorem B48066965 : Blo 1152637 48066965 := bstep (se 6 (by rfl) ⟨1126569, by rfl⟩ : syracuseStep 48066965 = 2253139) B2253139
theorem B1733279 : Blo 1152637 1733279 := bstep (se 1 (by rfl) ⟨1299959, by rfl⟩ : syracuseStep 1733279 = 2599919) B2599919
theorem B4387547 : Blo 1152637 4387547 := bstep (se 1 (by rfl) ⟨3290660, by rfl⟩ : syracuseStep 4387547 = 6581321) B6581321
theorem B1733615 : Blo 1152637 1733615 := bstep (se 1 (by rfl) ⟨1300211, by rfl⟩ : syracuseStep 1733615 = 2600423) B2600423
theorem B1733801 : Blo 1152637 1733801 := bstep (se 2 (by rfl) ⟨650175, by rfl⟩ : syracuseStep 1733801 = 1300351) B1300351
theorem B6583781 : Blo 1152637 6583781 := bstep (se 4 (by rfl) ⟨617229, by rfl⟩ : syracuseStep 6583781 = 1234459) B1234459
theorem B1734569 : Blo 1152637 1734569 := bstep (se 2 (by rfl) ⟨650463, by rfl⟩ : syracuseStep 1734569 = 1300927) B1300927
theorem B1734635 : Blo 1152637 1734635 := bstep (se 1 (by rfl) ⟨1300976, by rfl⟩ : syracuseStep 1734635 = 2601953) B2601953
theorem B7895231 : Blo 1152637 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B2193895 : Blo 1152637 2193895 := bstep (se 1 (by rfl) ⟨1645421, by rfl⟩ : syracuseStep 2193895 = 3290843) B3290843
theorem B47970913 : Blo 1152637 47970913 := bstep (se 2 (by rfl) ⟨17989092, by rfl⟩ : syracuseStep 47970913 = 35978185) B35978185
theorem B4061915 : Blo 1152637 4061915 := bstep (se 1 (by rfl) ⟨3046436, by rfl⟩ : syracuseStep 4061915 = 6092873) B6092873
theorem B2194715 : Blo 1152637 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B8782019 : Blo 1152637 8782019 := bstep (se 1 (by rfl) ⟨6586514, by rfl⟩ : syracuseStep 8782019 = 13173029) B13173029
theorem B19235161 : Blo 1152637 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B6586879 : Blo 1152637 6586879 := bstep (se 1 (by rfl) ⟨4940159, by rfl⟩ : syracuseStep 6586879 = 9880319) B9880319
theorem B7407551 : Blo 1152637 7407551 := bstep (se 1 (by rfl) ⟨5555663, by rfl⟩ : syracuseStep 7407551 = 11111327) B11111327
theorem B5835887 : Blo 1152637 5835887 := bstep (se 1 (by rfl) ⟨4376915, by rfl⟩ : syracuseStep 5835887 = 8753831) B8753831
theorem B1641583 : Blo 1152637 1641583 := bstep (se 1 (by rfl) ⟨1231187, by rfl⟩ : syracuseStep 1641583 = 2462375) B2462375
theorem B3902633 : Blo 1152637 3902633 := bstep (se 2 (by rfl) ⟨1463487, by rfl⟩ : syracuseStep 3902633 = 2926975) B2926975
theorem B22155677 : Blo 1152637 22155677 := bstep (se 3 (by rfl) ⟨4154189, by rfl⟩ : syracuseStep 22155677 = 8308379) B8308379
theorem B5837507 : Blo 1152637 5837507 := bstep (se 1 (by rfl) ⟨4378130, by rfl⟩ : syracuseStep 5837507 = 8756261) B8756261
theorem B2593961 : Blo 1152637 2593961 := bstep (se 2 (by rfl) ⟨972735, by rfl⟩ : syracuseStep 2593961 = 1945471) B1945471
theorem B4166909 : Blo 1152637 4166909 := bstep (se 3 (by rfl) ⟨781295, by rfl⟩ : syracuseStep 4166909 = 1562591) B1562591
theorem B5838479 : Blo 1152637 5838479 := bstep (se 1 (by rfl) ⟨4378859, by rfl⟩ : syracuseStep 5838479 = 8757719) B8757719
theorem B1152671 : Blo 1152637 1152671 := bstep (se 1 (by rfl) ⟨864503, by rfl⟩ : syracuseStep 1152671 = 1729007) B1729007
theorem B1153115 : Blo 1152637 1153115 := bstep (se 1 (by rfl) ⟨864836, by rfl⟩ : syracuseStep 1153115 = 1729673) B1729673
theorem B1153127 : Blo 1152637 1153127 := bstep (se 1 (by rfl) ⟨864845, by rfl⟩ : syracuseStep 1153127 = 1729691) B1729691
theorem B1153183 : Blo 1152637 1153183 := bstep (se 1 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 1153183 = 1729775) B1729775
theorem B1153231 : Blo 1152637 1153231 := bstep (se 1 (by rfl) ⟨864923, by rfl⟩ : syracuseStep 1153231 = 1729847) B1729847
theorem B1153263 : Blo 1152637 1153263 := bstep (se 1 (by rfl) ⟨864947, by rfl⟩ : syracuseStep 1153263 = 1729895) B1729895
theorem B1153471 : Blo 1152637 1153471 := bstep (se 1 (by rfl) ⟨865103, by rfl⟩ : syracuseStep 1153471 = 1730207) B1730207
theorem B1153519 : Blo 1152637 1153519 := bstep (se 1 (by rfl) ⟨865139, by rfl⟩ : syracuseStep 1153519 = 1730279) B1730279
theorem B2595977 : Blo 1152637 2595977 := bstep (se 2 (by rfl) ⟨973491, by rfl⟩ : syracuseStep 2595977 = 1946983) B1946983
theorem B1154407 : Blo 1152637 1154407 := bstep (se 1 (by rfl) ⟨865805, by rfl⟩ : syracuseStep 1154407 = 1731611) B1731611
theorem B3284351 : Blo 1152637 3284351 := bstep (se 1 (by rfl) ⟨2463263, by rfl⟩ : syracuseStep 3284351 = 4926527) B4926527
theorem B2924059 : Blo 1152637 2924059 := bstep (se 1 (by rfl) ⟨2193044, by rfl⟩ : syracuseStep 2924059 = 4386089) B4386089
theorem B1154719 : Blo 1152637 1154719 := bstep (se 1 (by rfl) ⟨866039, by rfl⟩ : syracuseStep 1154719 = 1732079) B1732079
theorem B1154811 : Blo 1152637 1154811 := bstep (se 1 (by rfl) ⟨866108, by rfl⟩ : syracuseStep 1154811 = 1732217) B1732217
theorem B1154879 : Blo 1152637 1154879 := bstep (se 1 (by rfl) ⟨866159, by rfl⟩ : syracuseStep 1154879 = 1732319) B1732319
theorem B1154975 : Blo 1152637 1154975 := bstep (se 1 (by rfl) ⟨866231, by rfl⟩ : syracuseStep 1154975 = 1732463) B1732463
theorem B1155163 : Blo 1152637 1155163 := bstep (se 1 (by rfl) ⟨866372, by rfl⟩ : syracuseStep 1155163 = 1732745) B1732745
theorem B15016033 : Blo 1152637 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B1155199 : Blo 1152637 1155199 := bstep (se 1 (by rfl) ⟨866399, by rfl⟩ : syracuseStep 1155199 = 1732799) B1732799
theorem B1155231 : Blo 1152637 1155231 := bstep (se 1 (by rfl) ⟨866423, by rfl⟩ : syracuseStep 1155231 = 1732847) B1732847
theorem B56959163 : Blo 1152637 56959163 := bstep (se 1 (by rfl) ⟨42719372, by rfl⟩ : syracuseStep 56959163 = 85438745) B85438745
theorem B1384807 : Blo 1152637 1384807 := bstep (se 1 (by rfl) ⟨1038605, by rfl⟩ : syracuseStep 1384807 = 2077211) B2077211
theorem B1155519 : Blo 1152637 1155519 := bstep (se 1 (by rfl) ⟨866639, by rfl⟩ : syracuseStep 1155519 = 1733279) B1733279
theorem B2925031 : Blo 1152637 2925031 := bstep (se 1 (by rfl) ⟨2193773, by rfl⟩ : syracuseStep 2925031 = 4387547) B4387547
theorem B2925193 : Blo 1152637 2925193 := bstep (se 2 (by rfl) ⟨1096947, by rfl⟩ : syracuseStep 2925193 = 2193895) B2193895
theorem B1155743 : Blo 1152637 1155743 := bstep (se 1 (by rfl) ⟨866807, by rfl⟩ : syracuseStep 1155743 = 1733615) B1733615
theorem B74916575 : Blo 1152637 74916575 := bstep (se 1 (by rfl) ⟨56187431, by rfl⟩ : syracuseStep 74916575 = 112374863) B112374863
theorem B3285785 : Blo 1152637 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B1155867 : Blo 1152637 1155867 := bstep (se 1 (by rfl) ⟨866900, by rfl⟩ : syracuseStep 1155867 = 1733801) B1733801
theorem B45556535 : Blo 1152637 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B1156379 : Blo 1152637 1156379 := bstep (se 1 (by rfl) ⟨867284, by rfl⟩ : syracuseStep 1156379 = 1734569) B1734569
theorem B1156423 : Blo 1152637 1156423 := bstep (se 1 (by rfl) ⟨867317, by rfl⟩ : syracuseStep 1156423 = 1734635) B1734635
theorem B1386239 : Blo 1152637 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B2599073 : Blo 1152637 2599073 := bstep (se 2 (by rfl) ⟨974652, by rfl⟩ : syracuseStep 2599073 = 1949305) B1949305
theorem B2960383 : Blo 1152637 2960383 := bstep (se 1 (by rfl) ⟨2220287, by rfl⟩ : syracuseStep 2960383 = 4440575) B4440575
theorem B2599991 : Blo 1152637 2599991 := bstep (se 1 (by rfl) ⟨1949993, by rfl⟩ : syracuseStep 2599991 = 3899987) B3899987
theorem B9875195 : Blo 1152637 9875195 := bstep (se 1 (by rfl) ⟨7406396, by rfl⟩ : syracuseStep 9875195 = 14812793) B14812793
theorem B1945775 : Blo 1152637 1945775 := bstep (se 1 (by rfl) ⟨1459331, by rfl⟩ : syracuseStep 1945775 = 2918663) B2918663
theorem B11252669 : Blo 1152637 11252669 := bstep (se 3 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 11252669 = 4219751) B4219751
theorem B3290159 : Blo 1152637 3290159 := bstep (se 1 (by rfl) ⟨2467619, by rfl⟩ : syracuseStep 3290159 = 4935239) B4935239
theorem B18723955 : Blo 1152637 18723955 := bstep (se 1 (by rfl) ⟨14042966, by rfl⟩ : syracuseStep 18723955 = 28085933) B28085933
theorem B24950663 : Blo 1152637 24950663 := bstep (se 1 (by rfl) ⟨18712997, by rfl⟩ : syracuseStep 24950663 = 37425995) B37425995
theorem B2963503 : Blo 1152637 2963503 := bstep (se 1 (by rfl) ⟨2222627, by rfl⟩ : syracuseStep 2963503 = 4445255) B4445255
theorem B9877585 : Blo 1152637 9877585 := bstep (se 2 (by rfl) ⟨3704094, by rfl⟩ : syracuseStep 9877585 = 7408189) B7408189
theorem B10533071 : Blo 1152637 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B33274111 : Blo 1152637 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B3291641 : Blo 1152637 3291641 := bstep (se 2 (by rfl) ⟨1234365, by rfl⟩ : syracuseStep 3291641 = 2468731) B2468731
theorem B1850863 : Blo 1152637 1850863 := bstep (se 1 (by rfl) ⟨1388147, by rfl⟩ : syracuseStep 1850863 = 2776295) B2776295
theorem B1949609 : Blo 1152637 1949609 := bstep (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) B1462207
theorem B7127351 : Blo 1152637 7127351 := bstep (se 1 (by rfl) ⟨5345513, by rfl⟩ : syracuseStep 7127351 = 10691027) B10691027
theorem B1951087 : Blo 1152637 1951087 := bstep (se 1 (by rfl) ⟨1463315, by rfl⟩ : syracuseStep 1951087 = 2926631) B2926631
theorem B5851763 : Blo 1152637 5851763 := bstep (se 1 (by rfl) ⟨4388822, by rfl⟩ : syracuseStep 5851763 = 8777645) B8777645
theorem B1297147 : Blo 1152637 1297147 := bstep (se 1 (by rfl) ⟨972860, by rfl⟩ : syracuseStep 1297147 = 1945721) B1945721
theorem B37932421 : Blo 1152637 37932421 := bstep (se 4 (by rfl) ⟨3556164, by rfl⟩ : syracuseStep 37932421 = 7112329) B7112329
theorem B5852573 : Blo 1152637 5852573 := bstep (se 3 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 5852573 = 2194715) B2194715
theorem B14798699 : Blo 1152637 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B5263487 : Blo 1152637 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B2707943 : Blo 1152637 2707943 := bstep (se 1 (by rfl) ⟨2030957, by rfl⟩ : syracuseStep 2707943 = 4061915) B4061915
theorem B8312969 : Blo 1152637 8312969 := bstep (se 2 (by rfl) ⟨3117363, by rfl⟩ : syracuseStep 8312969 = 6234727) B6234727
theorem B128080025 : Blo 1152637 128080025 := bstep (se 2 (by rfl) ⟨48030009, by rfl⟩ : syracuseStep 128080025 = 96060019) B96060019
theorem B11098295 : Blo 1152637 11098295 := bstep (se 1 (by rfl) ⟨8323721, by rfl⟩ : syracuseStep 11098295 = 16647443) B16647443
theorem B3890969 : Blo 1152637 3890969 := bstep (se 2 (by rfl) ⟨1459113, by rfl⟩ : syracuseStep 3890969 = 2918227) B2918227
theorem B4382687 : Blo 1152637 4382687 := bstep (se 1 (by rfl) ⟨3287015, by rfl⟩ : syracuseStep 4382687 = 6574031) B6574031
theorem B2810015 : Blo 1152637 2810015 := bstep (se 1 (by rfl) ⟨2107511, by rfl⟩ : syracuseStep 2810015 = 4215023) B4215023
theorem B1731113 : Blo 1152637 1731113 := bstep (se 2 (by rfl) ⟨649167, by rfl⟩ : syracuseStep 1731113 = 1298335) B1298335
theorem B11102831 : Blo 1152637 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B1403935 : Blo 1152637 1403935 := bstep (se 1 (by rfl) ⟨1052951, by rfl⟩ : syracuseStep 1403935 = 2105903) B2105903
theorem B1731815 : Blo 1152637 1731815 := bstep (se 1 (by rfl) ⟨1298861, by rfl⟩ : syracuseStep 1731815 = 2597723) B2597723
theorem B10546685 : Blo 1152637 10546685 := bstep (se 3 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 10546685 = 3955007) B3955007
theorem B3895343 : Blo 1152637 3895343 := bstep (se 1 (by rfl) ⟨2921507, by rfl⟩ : syracuseStep 3895343 = 5843015) B5843015
theorem B4387031 : Blo 1152637 4387031 := bstep (se 1 (by rfl) ⟨3290273, by rfl⟩ : syracuseStep 4387031 = 6580547) B6580547
theorem B1733099 : Blo 1152637 1733099 := bstep (se 1 (by rfl) ⟨1299824, by rfl⟩ : syracuseStep 1733099 = 2599649) B2599649
theorem B2815003 : Blo 1152637 2815003 := bstep (se 1 (by rfl) ⟨2111252, by rfl⟩ : syracuseStep 2815003 = 4222505) B4222505
theorem B1733663 : Blo 1152637 1733663 := bstep (se 1 (by rfl) ⟨1300247, by rfl⟩ : syracuseStep 1733663 = 2600495) B2600495
theorem B1733723 : Blo 1152637 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B3699881 : Blo 1152637 3699881 := bstep (se 2 (by rfl) ⟨1387455, by rfl⟩ : syracuseStep 3699881 = 2774911) B2774911
theorem B9860363 : Blo 1152637 9860363 := bstep (se 1 (by rfl) ⟨7395272, by rfl⟩ : syracuseStep 9860363 = 14790545) B14790545
theorem B32044643 : Blo 1152637 32044643 := bstep (se 1 (by rfl) ⟨24033482, by rfl⟩ : syracuseStep 32044643 = 48066965) B48066965
theorem B4159151 : Blo 1152637 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B1734767 : Blo 1152637 1734767 := bstep (se 1 (by rfl) ⟨1301075, by rfl⟩ : syracuseStep 1734767 = 2602151) B2602151
theorem B63961217 : Blo 1152637 63961217 := bstep (se 2 (by rfl) ⟨23985456, by rfl⟩ : syracuseStep 63961217 = 47970913) B47970913
theorem B4389187 : Blo 1152637 4389187 := bstep (se 1 (by rfl) ⟨3291890, by rfl⟩ : syracuseStep 4389187 = 6583781) B6583781
theorem B9370025 : Blo 1152637 9370025 := bstep (se 2 (by rfl) ⟨3513759, by rfl⟩ : syracuseStep 9370025 = 7027519) B7027519
theorem B3898529 : Blo 1152637 3898529 := bstep (se 2 (by rfl) ⟨1461948, by rfl⟩ : syracuseStep 3898529 = 2923897) B2923897
theorem B20021377 : Blo 1152637 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B4751567 : Blo 1152637 4751567 := bstep (se 1 (by rfl) ⟨3563675, by rfl⟩ : syracuseStep 4751567 = 7127351) B7127351
theorem B3900041 : Blo 1152637 3900041 := bstep (se 2 (by rfl) ⟨1462515, by rfl⟩ : syracuseStep 3900041 = 2925031) B2925031
theorem B8782505 : Blo 1152637 8782505 := bstep (se 2 (by rfl) ⟨3293439, by rfl⟩ : syracuseStep 8782505 = 6586879) B6586879
theorem B3900257 : Blo 1152637 3900257 := bstep (se 2 (by rfl) ⟨1462596, by rfl⟩ : syracuseStep 3900257 = 2925193) B2925193
theorem B3901175 : Blo 1152637 3901175 := bstep (se 1 (by rfl) ⟨2925881, by rfl⟩ : syracuseStep 3901175 = 5851763) B5851763
theorem B3901715 : Blo 1152637 3901715 := bstep (se 1 (by rfl) ⟨2926286, by rfl⟩ : syracuseStep 3901715 = 5852573) B5852573
theorem B9865799 : Blo 1152637 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B3508991 : Blo 1152637 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B5541979 : Blo 1152637 5541979 := bstep (se 1 (by rfl) ⟨4156484, by rfl⟩ : syracuseStep 5541979 = 8312969) B8312969
theorem B2593979 : Blo 1152637 2593979 := bstep (se 1 (by rfl) ⟨1945484, by rfl⟩ : syracuseStep 2593979 = 3890969) B3890969
theorem B2921791 : Blo 1152637 2921791 := bstep (se 1 (by rfl) ⟨2191343, by rfl⟩ : syracuseStep 2921791 = 4382687) B4382687
theorem B1873343 : Blo 1152637 1873343 := bstep (se 1 (by rfl) ⟨1405007, by rfl⟩ : syracuseStep 1873343 = 2810015) B2810015
theorem B49944383 : Blo 1152637 49944383 := bstep (se 1 (by rfl) ⟨37458287, by rfl⟩ : syracuseStep 49944383 = 74916575) B74916575
theorem B1154075 : Blo 1152637 1154075 := bstep (se 1 (by rfl) ⟨865556, by rfl⟩ : syracuseStep 1154075 = 1731113) B1731113
theorem B1154543 : Blo 1152637 1154543 := bstep (se 1 (by rfl) ⟨865907, by rfl⟩ : syracuseStep 1154543 = 1731815) B1731815
theorem B14786549 : Blo 1152637 14786549 := bstep (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) B1386239
theorem B2596895 : Blo 1152637 2596895 := bstep (se 1 (by rfl) ⟨1947671, by rfl⟩ : syracuseStep 2596895 = 3895343) B3895343
theorem B2924687 : Blo 1152637 2924687 := bstep (se 1 (by rfl) ⟨2193515, by rfl⟩ : syracuseStep 2924687 = 4387031) B4387031
theorem B1155399 : Blo 1152637 1155399 := bstep (se 1 (by rfl) ⟨866549, by rfl⟩ : syracuseStep 1155399 = 1733099) B1733099
theorem B1155775 : Blo 1152637 1155775 := bstep (se 1 (by rfl) ⟨866831, by rfl⟩ : syracuseStep 1155775 = 1733663) B1733663
theorem B1155815 : Blo 1152637 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B2466587 : Blo 1152637 2466587 := bstep (se 1 (by rfl) ⟨1849940, by rfl⟩ : syracuseStep 2466587 = 3699881) B3699881
theorem B1156511 : Blo 1152637 1156511 := bstep (se 1 (by rfl) ⟨867383, by rfl⟩ : syracuseStep 1156511 = 1734767) B1734767
theorem B42640811 : Blo 1152637 42640811 := bstep (se 1 (by rfl) ⟨31980608, by rfl⟩ : syracuseStep 42640811 = 63961217) B63961217
theorem B7022047 : Blo 1152637 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B2467817 : Blo 1152637 2467817 := bstep (se 2 (by rfl) ⟨925431, by rfl⟩ : syracuseStep 2467817 = 1850863) B1850863
theorem B2599019 : Blo 1152637 2599019 := bstep (se 1 (by rfl) ⟨1949264, by rfl⟩ : syracuseStep 2599019 = 3898529) B3898529
theorem B1846409 : Blo 1152637 1846409 := bstep (se 2 (by rfl) ⟨692403, by rfl⟩ : syracuseStep 1846409 = 1384807) B1384807
theorem B2601449 : Blo 1152637 2601449 := bstep (se 2 (by rfl) ⟨975543, by rfl⟩ : syracuseStep 2601449 = 1951087) B1951087
theorem B8762093 : Blo 1152637 8762093 := bstep (se 3 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 8762093 = 3285785) B3285785
theorem B2601755 : Blo 1152637 2601755 := bstep (se 1 (by rfl) ⟨1951316, by rfl⟩ : syracuseStep 2601755 = 3902633) B3902633
theorem B3947177 : Blo 1152637 3947177 := bstep (se 2 (by rfl) ⟨1480191, by rfl⟩ : syracuseStep 3947177 = 2960383) B2960383
theorem B50576561 : Blo 1152637 50576561 := bstep (se 2 (by rfl) ⟨18966210, by rfl⟩ : syracuseStep 50576561 = 37932421) B37932421
theorem B28884725 : Blo 1152637 28884725 := bstep (se 5 (by rfl) ⟨1353971, by rfl⟩ : syracuseStep 28884725 = 2707943) B2707943
theorem B7487653 : Blo 1152637 7487653 := bstep (se 4 (by rfl) ⟨701967, by rfl⟩ : syracuseStep 7487653 = 1403935) B1403935
theorem B3753337 : Blo 1152637 3753337 := bstep (se 2 (by rfl) ⟨1407501, by rfl⟩ : syracuseStep 3753337 = 2815003) B2815003
theorem B7031123 : Blo 1152637 7031123 := bstep (se 1 (by rfl) ⟨5273342, by rfl⟩ : syracuseStep 7031123 = 10546685) B10546685
theorem B3951337 : Blo 1152637 3951337 := bstep (se 2 (by rfl) ⟨1481751, by rfl⟩ : syracuseStep 3951337 = 2963503) B2963503
theorem B1297183 : Blo 1152637 1297183 := bstep (se 1 (by rfl) ⟨972887, by rfl⟩ : syracuseStep 1297183 = 1945775) B1945775
theorem B5852249 : Blo 1152637 5852249 := bstep (se 2 (by rfl) ⟨2194593, by rfl⟩ : syracuseStep 5852249 = 4389187) B4389187
theorem B6573575 : Blo 1152637 6573575 := bstep (se 1 (by rfl) ⟨4930181, by rfl⟩ : syracuseStep 6573575 = 9860363) B9860363
theorem B2772767 : Blo 1152637 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B16633775 : Blo 1152637 16633775 := bstep (se 1 (by rfl) ⟨12475331, by rfl⟩ : syracuseStep 16633775 = 24950663) B24950663
theorem B6246683 : Blo 1152637 6246683 := bstep (se 1 (by rfl) ⟨4685012, by rfl⟩ : syracuseStep 6246683 = 9370025) B9370025
theorem B1299739 : Blo 1152637 1299739 := bstep (se 1 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 1299739 = 1949609) B1949609
theorem B5854679 : Blo 1152637 5854679 := bstep (se 1 (by rfl) ⟨4391009, by rfl⟩ : syracuseStep 5854679 = 8782019) B8782019
theorem B25646881 : Blo 1152637 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B4938367 : Blo 1152637 4938367 := bstep (se 1 (by rfl) ⟨3703775, by rfl⟩ : syracuseStep 4938367 = 7407551) B7407551
theorem B3890591 : Blo 1152637 3890591 := bstep (se 1 (by rfl) ⟨2917943, by rfl⟩ : syracuseStep 3890591 = 5835887) B5835887
theorem B30007117 : Blo 1152637 30007117 := bstep (se 3 (by rfl) ⟨5626334, by rfl⟩ : syracuseStep 30007117 = 11252669) B11252669
theorem B8773757 : Blo 1152637 8773757 := bstep (se 3 (by rfl) ⟨1645079, by rfl⟩ : syracuseStep 8773757 = 3290159) B3290159
theorem B14770451 : Blo 1152637 14770451 := bstep (se 1 (by rfl) ⟨11077838, by rfl⟩ : syracuseStep 14770451 = 22155677) B22155677
theorem B3891671 : Blo 1152637 3891671 := bstep (se 1 (by rfl) ⟨2918753, by rfl⟩ : syracuseStep 3891671 = 5837507) B5837507
theorem B1729307 : Blo 1152637 1729307 := bstep (se 1 (by rfl) ⟨1296980, by rfl⟩ : syracuseStep 1729307 = 2593961) B2593961
theorem B2777939 : Blo 1152637 2777939 := bstep (se 1 (by rfl) ⟨2083454, by rfl⟩ : syracuseStep 2777939 = 4166909) B4166909
theorem B1729529 : Blo 1152637 1729529 := bstep (se 2 (by rfl) ⟨648573, by rfl⟩ : syracuseStep 1729529 = 1297147) B1297147
theorem B3892319 : Blo 1152637 3892319 := bstep (se 1 (by rfl) ⟨2919239, by rfl⟩ : syracuseStep 3892319 = 5838479) B5838479
theorem B85386683 : Blo 1152637 85386683 := bstep (se 1 (by rfl) ⟨64040012, by rfl⟩ : syracuseStep 85386683 = 128080025) B128080025
theorem B7398863 : Blo 1152637 7398863 := bstep (se 1 (by rfl) ⟨5549147, by rfl⟩ : syracuseStep 7398863 = 11098295) B11098295
theorem B2188777 : Blo 1152637 2188777 := bstep (se 2 (by rfl) ⟨820791, by rfl⟩ : syracuseStep 2188777 = 1641583) B1641583
theorem B1730651 : Blo 1152637 1730651 := bstep (se 1 (by rfl) ⟨1297988, by rfl⟩ : syracuseStep 1730651 = 2595977) B2595977
theorem B2189567 : Blo 1152637 2189567 := bstep (se 1 (by rfl) ⟨1642175, by rfl⟩ : syracuseStep 2189567 = 3284351) B3284351
theorem B37972775 : Blo 1152637 37972775 := bstep (se 1 (by rfl) ⟨28479581, by rfl⟩ : syracuseStep 37972775 = 56959163) B56959163
theorem B30371023 : Blo 1152637 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B1732715 : Blo 1152637 1732715 := bstep (se 1 (by rfl) ⟨1299536, by rfl⟩ : syracuseStep 1732715 = 2599073) B2599073
theorem B24965273 : Blo 1152637 24965273 := bstep (se 2 (by rfl) ⟨9361977, by rfl⟩ : syracuseStep 24965273 = 18723955) B18723955
theorem B7401887 : Blo 1152637 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B1733327 : Blo 1152637 1733327 := bstep (se 1 (by rfl) ⟨1299995, by rfl⟩ : syracuseStep 1733327 = 2599991) B2599991
theorem B6583463 : Blo 1152637 6583463 := bstep (se 1 (by rfl) ⟨4937597, by rfl⟩ : syracuseStep 6583463 = 9875195) B9875195
theorem B13170113 : Blo 1152637 13170113 := bstep (se 2 (by rfl) ⟨4938792, by rfl⟩ : syracuseStep 13170113 = 9877585) B9877585
theorem B44365481 : Blo 1152637 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B21363095 : Blo 1152637 21363095 := bstep (se 1 (by rfl) ⟨16022321, by rfl⟩ : syracuseStep 21363095 = 32044643) B32044643
theorem B2194427 : Blo 1152637 2194427 := bstep (se 1 (by rfl) ⟨1645820, by rfl⟩ : syracuseStep 2194427 = 3291641) B3291641
theorem B3898745 : Blo 1152637 3898745 := bstep (se 2 (by rfl) ⟨1462029, by rfl⟩ : syracuseStep 3898745 = 2924059) B2924059
theorem B4687415 : Blo 1152637 4687415 := bstep (se 1 (by rfl) ⟨3515561, by rfl⟩ : syracuseStep 4687415 = 7031123) B7031123
theorem B2918369 : Blo 1152637 2918369 := bstep (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) B2188777
theorem B3901499 : Blo 1152637 3901499 := bstep (se 1 (by rfl) ⟨2926124, by rfl⟩ : syracuseStep 3901499 = 5852249) B5852249
theorem B4164455 : Blo 1152637 4164455 := bstep (se 1 (by rfl) ⟨3123341, by rfl⟩ : syracuseStep 4164455 = 6246683) B6246683
theorem B1248895 : Blo 1152637 1248895 := bstep (se 1 (by rfl) ⟨936671, by rfl⟩ : syracuseStep 1248895 = 1873343) B1873343
theorem B3903119 : Blo 1152637 3903119 := bstep (se 1 (by rfl) ⟨2927339, by rfl⟩ : syracuseStep 3903119 = 5854679) B5854679
theorem B33296255 : Blo 1152637 33296255 := bstep (se 1 (by rfl) ⟨24972191, by rfl⟩ : syracuseStep 33296255 = 49944383) B49944383
theorem B2593727 : Blo 1152637 2593727 := bstep (se 1 (by rfl) ⟨1945295, by rfl⟩ : syracuseStep 2593727 = 3890591) B3890591
theorem B2594447 : Blo 1152637 2594447 := bstep (se 1 (by rfl) ⟨1945835, by rfl⟩ : syracuseStep 2594447 = 3891671) B3891671
theorem B1152871 : Blo 1152637 1152871 := bstep (se 1 (by rfl) ⟨864653, by rfl⟩ : syracuseStep 1152871 = 1729307) B1729307
theorem B1644391 : Blo 1152637 1644391 := bstep (se 1 (by rfl) ⟨1233293, by rfl⟩ : syracuseStep 1644391 = 2466587) B2466587
theorem B1153019 : Blo 1152637 1153019 := bstep (se 1 (by rfl) ⟨864764, by rfl⟩ : syracuseStep 1153019 = 1729529) B1729529
theorem B2594879 : Blo 1152637 2594879 := bstep (se 1 (by rfl) ⟨1946159, by rfl⟩ : syracuseStep 2594879 = 3892319) B3892319
theorem B56924455 : Blo 1152637 56924455 := bstep (se 1 (by rfl) ⟨42693341, by rfl⟩ : syracuseStep 56924455 = 85386683) B85386683
theorem B1645211 : Blo 1152637 1645211 := bstep (se 1 (by rfl) ⟨1233908, by rfl⟩ : syracuseStep 1645211 = 2467817) B2467817
theorem B1153767 : Blo 1152637 1153767 := bstep (se 1 (by rfl) ⟨865325, by rfl⟩ : syracuseStep 1153767 = 1730651) B1730651
theorem B1155143 : Blo 1152637 1155143 := bstep (se 1 (by rfl) ⟨866357, by rfl⟩ : syracuseStep 1155143 = 1732715) B1732715
theorem B4923757 : Blo 1152637 4923757 := bstep (se 3 (by rfl) ⟨923204, by rfl⟩ : syracuseStep 4923757 = 1846409) B1846409
theorem B1155551 : Blo 1152637 1155551 := bstep (se 1 (by rfl) ⟨866663, by rfl⟩ : syracuseStep 1155551 = 1733327) B1733327
theorem B5841395 : Blo 1152637 5841395 := bstep (se 1 (by rfl) ⟨4381046, by rfl⟩ : syracuseStep 5841395 = 8762093) B8762093
theorem B2631451 : Blo 1152637 2631451 := bstep (se 1 (by rfl) ⟨1973588, by rfl⟩ : syracuseStep 2631451 = 3947177) B3947177
theorem B2599163 : Blo 1152637 2599163 := bstep (se 1 (by rfl) ⟨1949372, by rfl⟩ : syracuseStep 2599163 = 3898745) B3898745
theorem B2600027 : Blo 1152637 2600027 := bstep (se 1 (by rfl) ⟨1950020, by rfl⟩ : syracuseStep 2600027 = 3900041) B3900041
theorem B2600171 : Blo 1152637 2600171 := bstep (se 1 (by rfl) ⟨1950128, by rfl⟩ : syracuseStep 2600171 = 3900257) B3900257
theorem B2600783 : Blo 1152637 2600783 := bstep (se 1 (by rfl) ⟨1950587, by rfl⟩ : syracuseStep 2600783 = 3901175) B3901175
theorem B2601143 : Blo 1152637 2601143 := bstep (se 1 (by rfl) ⟨1950857, by rfl⟩ : syracuseStep 2601143 = 3901715) B3901715
theorem B2339327 : Blo 1152637 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B1848511 : Blo 1152637 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B11089183 : Blo 1152637 11089183 := bstep (se 1 (by rfl) ⟨8316887, by rfl⟩ : syracuseStep 11089183 = 16633775) B16633775
theorem B5849171 : Blo 1152637 5849171 := bstep (se 1 (by rfl) ⟨4386878, by rfl⟩ : syracuseStep 5849171 = 8773757) B8773757
theorem B1949791 : Blo 1152637 1949791 := bstep (se 1 (by rfl) ⟨1462343, by rfl⟩ : syracuseStep 1949791 = 2924687) B2924687
theorem B7389305 : Blo 1152637 7389305 := bstep (se 2 (by rfl) ⟨2770989, by rfl⟩ : syracuseStep 7389305 = 5541979) B5541979
theorem B9846967 : Blo 1152637 9846967 := bstep (se 1 (by rfl) ⟨7385225, by rfl⟩ : syracuseStep 9846967 = 14770451) B14770451
theorem B1851959 : Blo 1152637 1851959 := bstep (se 1 (by rfl) ⟨1388969, by rfl⟩ : syracuseStep 1851959 = 2777939) B2777939
theorem B28427207 : Blo 1152637 28427207 := bstep (se 1 (by rfl) ⟨21320405, by rfl⟩ : syracuseStep 28427207 = 42640811) B42640811
theorem B4932575 : Blo 1152637 4932575 := bstep (se 1 (by rfl) ⟨3699431, by rfl⟩ : syracuseStep 4932575 = 7398863) B7398863
theorem B1459711 : Blo 1152637 1459711 := bstep (se 1 (by rfl) ⟨1094783, by rfl⟩ : syracuseStep 1459711 = 2189567) B2189567
theorem B25315183 : Blo 1152637 25315183 := bstep (se 1 (by rfl) ⟨18986387, by rfl⟩ : syracuseStep 25315183 = 37972775) B37972775
theorem B34195841 : Blo 1152637 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B4934591 : Blo 1152637 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B29576987 : Blo 1152637 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B14242063 : Blo 1152637 14242063 := bstep (se 1 (by rfl) ⟨10681547, by rfl⟩ : syracuseStep 14242063 = 21363095) B21363095
theorem B1462951 : Blo 1152637 1462951 := bstep (se 1 (by rfl) ⟨1097213, by rfl⟩ : syracuseStep 1462951 = 2194427) B2194427
theorem B19256483 : Blo 1152637 19256483 := bstep (se 1 (by rfl) ⟨14442362, by rfl⟩ : syracuseStep 19256483 = 28884725) B28884725
theorem B3167711 : Blo 1152637 3167711 := bstep (se 1 (by rfl) ⟨2375783, by rfl⟩ : syracuseStep 3167711 = 4751567) B4751567
theorem B26695169 : Blo 1152637 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B9983537 : Blo 1152637 9983537 := bstep (se 2 (by rfl) ⟨3743826, by rfl⟩ : syracuseStep 9983537 = 7487653) B7487653
theorem B5855003 : Blo 1152637 5855003 := bstep (se 1 (by rfl) ⟨4391252, by rfl⟩ : syracuseStep 5855003 = 8782505) B8782505
theorem B6577199 : Blo 1152637 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B5004449 : Blo 1152637 5004449 := bstep (se 2 (by rfl) ⟨1876668, by rfl⟩ : syracuseStep 5004449 = 3753337) B3753337
theorem B9362729 : Blo 1152637 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B4382383 : Blo 1152637 4382383 := bstep (se 1 (by rfl) ⟨3286787, by rfl⟩ : syracuseStep 4382383 = 6573575) B6573575
theorem B1729319 : Blo 1152637 1729319 := bstep (se 1 (by rfl) ⟨1296989, by rfl⟩ : syracuseStep 1729319 = 2593979) B2593979
theorem B5268449 : Blo 1152637 5268449 := bstep (se 2 (by rfl) ⟨1975668, by rfl⟩ : syracuseStep 5268449 = 3951337) B3951337
theorem B1729577 : Blo 1152637 1729577 := bstep (se 2 (by rfl) ⟨648591, by rfl⟩ : syracuseStep 1729577 = 1297183) B1297183
theorem B40494697 : Blo 1152637 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B9857699 : Blo 1152637 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B1731263 : Blo 1152637 1731263 := bstep (se 1 (by rfl) ⟨1298447, by rfl⟩ : syracuseStep 1731263 = 2596895) B2596895
theorem B1732679 : Blo 1152637 1732679 := bstep (se 1 (by rfl) ⟨1299509, by rfl⟩ : syracuseStep 1732679 = 2599019) B2599019
theorem B1732985 : Blo 1152637 1732985 := bstep (se 2 (by rfl) ⟨649869, by rfl⟩ : syracuseStep 1732985 = 1299739) B1299739
theorem B3895721 : Blo 1152637 3895721 := bstep (se 2 (by rfl) ⟨1460895, by rfl⟩ : syracuseStep 3895721 = 2921791) B2921791
theorem B16643515 : Blo 1152637 16643515 := bstep (se 1 (by rfl) ⟨12482636, by rfl⟩ : syracuseStep 16643515 = 24965273) B24965273
theorem B1734299 : Blo 1152637 1734299 := bstep (se 1 (by rfl) ⟨1300724, by rfl⟩ : syracuseStep 1734299 = 2601449) B2601449
theorem B1734503 : Blo 1152637 1734503 := bstep (se 1 (by rfl) ⟨1300877, by rfl⟩ : syracuseStep 1734503 = 2601755) B2601755
theorem B4388975 : Blo 1152637 4388975 := bstep (se 1 (by rfl) ⟨3291731, by rfl⟩ : syracuseStep 4388975 = 6583463) B6583463
theorem B6584489 : Blo 1152637 6584489 := bstep (se 2 (by rfl) ⟨2469183, by rfl⟩ : syracuseStep 6584489 = 4938367) B4938367
theorem B8780075 : Blo 1152637 8780075 := bstep (se 1 (by rfl) ⟨6585056, by rfl⟩ : syracuseStep 8780075 = 13170113) B13170113
theorem B160037957 : Blo 1152637 160037957 := bstep (se 4 (by rfl) ⟨15003558, by rfl⟩ : syracuseStep 160037957 = 30007117) B30007117
theorem B33717707 : Blo 1152637 33717707 := bstep (se 1 (by rfl) ⟨25288280, by rfl⟩ : syracuseStep 33717707 = 50576561) B50576561
theorem B3899447 : Blo 1152637 3899447 := bstep (se 1 (by rfl) ⟨2924585, by rfl⟩ : syracuseStep 3899447 = 5849171) B5849171
theorem B3508601 : Blo 1152637 3508601 := bstep (se 2 (by rfl) ⟨1315725, by rfl⟩ : syracuseStep 3508601 = 2631451) B2631451
theorem B17796779 : Blo 1152637 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B6655691 : Blo 1152637 6655691 := bstep (se 1 (by rfl) ⟨4991768, by rfl⟩ : syracuseStep 6655691 = 9983537) B9983537
theorem B3903335 : Blo 1152637 3903335 := bstep (se 1 (by rfl) ⟨2927501, by rfl⟩ : syracuseStep 3903335 = 5855003) B5855003
theorem B1152879 : Blo 1152637 1152879 := bstep (se 1 (by rfl) ⟨864659, by rfl⟩ : syracuseStep 1152879 = 1729319) B1729319
theorem B1153051 : Blo 1152637 1153051 := bstep (se 1 (by rfl) ⟨864788, by rfl⟩ : syracuseStep 1153051 = 1729577) B1729577
theorem B2464681 : Blo 1152637 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B14785577 : Blo 1152637 14785577 := bstep (se 2 (by rfl) ⟨5544591, by rfl⟩ : syracuseStep 14785577 = 11089183) B11089183
theorem B1154175 : Blo 1152637 1154175 := bstep (se 1 (by rfl) ⟨865631, by rfl⟩ : syracuseStep 1154175 = 1731263) B1731263
theorem B22191353 : Blo 1152637 22191353 := bstep (se 2 (by rfl) ⟨8321757, by rfl⟩ : syracuseStep 22191353 = 16643515) B16643515
theorem B1155119 : Blo 1152637 1155119 := bstep (se 1 (by rfl) ⟨866339, by rfl⟩ : syracuseStep 1155119 = 1732679) B1732679
theorem B1155323 : Blo 1152637 1155323 := bstep (se 1 (by rfl) ⟨866492, by rfl⟩ : syracuseStep 1155323 = 1732985) B1732985
theorem B2597147 : Blo 1152637 2597147 := bstep (se 1 (by rfl) ⟨1947860, by rfl⟩ : syracuseStep 2597147 = 3895721) B3895721
theorem B75899273 : Blo 1152637 75899273 := bstep (se 2 (by rfl) ⟨28462227, by rfl⟩ : syracuseStep 75899273 = 56924455) B56924455
theorem B1156199 : Blo 1152637 1156199 := bstep (se 1 (by rfl) ⟨867149, by rfl⟩ : syracuseStep 1156199 = 1734299) B1734299
theorem B1156335 : Blo 1152637 1156335 := bstep (se 1 (by rfl) ⟨867251, by rfl⟩ : syracuseStep 1156335 = 1734503) B1734503
theorem B2925983 : Blo 1152637 2925983 := bstep (se 1 (by rfl) ⟨2194487, by rfl⟩ : syracuseStep 2925983 = 4388975) B4388975
theorem B135014309 : Blo 1152637 135014309 := bstep (se 4 (by rfl) ⟨12657591, by rfl⟩ : syracuseStep 135014309 = 25315183) B25315183
theorem B5843177 : Blo 1152637 5843177 := bstep (se 2 (by rfl) ⟨2191191, by rfl⟩ : syracuseStep 5843177 = 4382383) B4382383
theorem B4926203 : Blo 1152637 4926203 := bstep (se 1 (by rfl) ⟨3694652, by rfl⟩ : syracuseStep 4926203 = 7389305) B7389305
theorem B2599721 : Blo 1152637 2599721 := bstep (se 2 (by rfl) ⟨974895, by rfl⟩ : syracuseStep 2599721 = 1949791) B1949791
theorem B6565009 : Blo 1152637 6565009 := bstep (se 2 (by rfl) ⟨2461878, by rfl⟩ : syracuseStep 6565009 = 4923757) B4923757
theorem B3288383 : Blo 1152637 3288383 := bstep (se 1 (by rfl) ⟨2466287, by rfl⟩ : syracuseStep 3288383 = 4932575) B4932575
theorem B3124943 : Blo 1152637 3124943 := bstep (se 1 (by rfl) ⟨2343707, by rfl⟩ : syracuseStep 3124943 = 4687415) B4687415
theorem B1945579 : Blo 1152637 1945579 := bstep (se 1 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 1945579 = 2918369) B2918369
theorem B6238205 : Blo 1152637 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B2600999 : Blo 1152637 2600999 := bstep (se 1 (by rfl) ⟨1950749, by rfl⟩ : syracuseStep 2600999 = 3901499) B3901499
theorem B3289727 : Blo 1152637 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B1946281 : Blo 1152637 1946281 := bstep (se 2 (by rfl) ⟨729855, by rfl⟩ : syracuseStep 1946281 = 1459711) B1459711
theorem B2602079 : Blo 1152637 2602079 := bstep (se 1 (by rfl) ⟨1951559, by rfl⟩ : syracuseStep 2602079 = 3903119) B3903119
theorem B75805885 : Blo 1152637 75805885 := bstep (se 3 (by rfl) ⟨14213603, by rfl⟩ : syracuseStep 75805885 = 28427207) B28427207
theorem B22197503 : Blo 1152637 22197503 := bstep (se 1 (by rfl) ⟨16648127, by rfl⟩ : syracuseStep 22197503 = 33296255) B33296255
theorem B2111807 : Blo 1152637 2111807 := bstep (se 1 (by rfl) ⟨1583855, by rfl⟩ : syracuseStep 2111807 = 3167711) B3167711
theorem B6241819 : Blo 1152637 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B18989417 : Blo 1152637 18989417 := bstep (se 2 (by rfl) ⟨7121031, by rfl⟩ : syracuseStep 18989417 = 14242063) B14242063
theorem B1950601 : Blo 1152637 1950601 := bstep (se 2 (by rfl) ⟨731475, by rfl⟩ : syracuseStep 1950601 = 1462951) B1462951
theorem B6571799 : Blo 1152637 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B5853383 : Blo 1152637 5853383 := bstep (se 1 (by rfl) ⟨4390037, by rfl⟩ : syracuseStep 5853383 = 8780075) B8780075
theorem B13129289 : Blo 1152637 13129289 := bstep (se 2 (by rfl) ⟨4923483, by rfl⟩ : syracuseStep 13129289 = 9846967) B9846967
theorem B1234639 : Blo 1152637 1234639 := bstep (se 1 (by rfl) ⟨925979, by rfl⟩ : syracuseStep 1234639 = 1851959) B1851959
theorem B22797227 : Blo 1152637 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B2776303 : Blo 1152637 2776303 := bstep (se 1 (by rfl) ⟨2082227, by rfl⟩ : syracuseStep 2776303 = 4164455) B4164455
theorem B19717991 : Blo 1152637 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B14049197 : Blo 1152637 14049197 := bstep (se 3 (by rfl) ⟨2634224, by rfl⟩ : syracuseStep 14049197 = 5268449) B5268449
theorem B1729151 : Blo 1152637 1729151 := bstep (se 1 (by rfl) ⟨1296863, by rfl⟩ : syracuseStep 1729151 = 2593727) B2593727
theorem B12837655 : Blo 1152637 12837655 := bstep (se 1 (by rfl) ⟨9628241, by rfl⟩ : syracuseStep 12837655 = 19256483) B19256483
theorem B1729631 : Blo 1152637 1729631 := bstep (se 1 (by rfl) ⟨1297223, by rfl⟩ : syracuseStep 1729631 = 2594447) B2594447
theorem B1729919 : Blo 1152637 1729919 := bstep (se 1 (by rfl) ⟨1297439, by rfl⟩ : syracuseStep 1729919 = 2594879) B2594879
theorem B4384799 : Blo 1152637 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B3336299 : Blo 1152637 3336299 := bstep (se 1 (by rfl) ⟨2502224, by rfl⟩ : syracuseStep 3336299 = 5004449) B5004449
theorem B1665193 : Blo 1152637 1665193 := bstep (se 2 (by rfl) ⟨624447, by rfl⟩ : syracuseStep 1665193 = 1248895) B1248895
theorem B3894263 : Blo 1152637 3894263 := bstep (se 1 (by rfl) ⟨2920697, by rfl⟩ : syracuseStep 3894263 = 5841395) B5841395
theorem B1732775 : Blo 1152637 1732775 := bstep (se 1 (by rfl) ⟨1299581, by rfl⟩ : syracuseStep 1732775 = 2599163) B2599163
theorem B4387229 : Blo 1152637 4387229 := bstep (se 3 (by rfl) ⟨822605, by rfl⟩ : syracuseStep 4387229 = 1645211) B1645211
theorem B1733351 : Blo 1152637 1733351 := bstep (se 1 (by rfl) ⟨1300013, by rfl⟩ : syracuseStep 1733351 = 2600027) B2600027
theorem B1733447 : Blo 1152637 1733447 := bstep (se 1 (by rfl) ⟨1300085, by rfl⟩ : syracuseStep 1733447 = 2600171) B2600171
theorem B2192521 : Blo 1152637 2192521 := bstep (se 2 (by rfl) ⟨822195, by rfl⟩ : syracuseStep 2192521 = 1644391) B1644391
theorem B1733855 : Blo 1152637 1733855 := bstep (se 1 (by rfl) ⟨1300391, by rfl⟩ : syracuseStep 1733855 = 2600783) B2600783
theorem B1734095 : Blo 1152637 1734095 := bstep (se 1 (by rfl) ⟨1300571, by rfl⟩ : syracuseStep 1734095 = 2601143) B2601143
theorem B426767885 : Blo 1152637 426767885 := bstep (se 3 (by rfl) ⟨80018978, by rfl⟩ : syracuseStep 426767885 = 160037957) B160037957
theorem B215971717 : Blo 1152637 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B4389659 : Blo 1152637 4389659 := bstep (se 1 (by rfl) ⟨3292244, by rfl⟩ : syracuseStep 4389659 = 6584489) B6584489
theorem B22478471 : Blo 1152637 22478471 := bstep (se 1 (by rfl) ⟨16858853, by rfl⟩ : syracuseStep 22478471 = 33717707) B33717707
theorem B11864519 : Blo 1152637 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B3902255 : Blo 1152637 3902255 := bstep (se 1 (by rfl) ⟨2926691, by rfl⟩ : syracuseStep 3902255 = 5853383) B5853383
theorem B8752859 : Blo 1152637 8752859 := bstep (se 1 (by rfl) ⟨6564644, by rfl⟩ : syracuseStep 8752859 = 13129289) B13129289
theorem B8753345 : Blo 1152637 8753345 := bstep (se 2 (by rfl) ⟨3282504, by rfl⟩ : syracuseStep 8753345 = 6565009) B6565009
theorem B13145327 : Blo 1152637 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B2594105 : Blo 1152637 2594105 := bstep (se 2 (by rfl) ⟨972789, by rfl⟩ : syracuseStep 2594105 = 1945579) B1945579
theorem B1152767 : Blo 1152637 1152767 := bstep (se 1 (by rfl) ⟨864575, by rfl⟩ : syracuseStep 1152767 = 1729151) B1729151
theorem B1153087 : Blo 1152637 1153087 := bstep (se 1 (by rfl) ⟨864815, by rfl⟩ : syracuseStep 1153087 = 1729631) B1729631
theorem B2595041 : Blo 1152637 2595041 := bstep (se 2 (by rfl) ⟨973140, by rfl⟩ : syracuseStep 2595041 = 1946281) B1946281
theorem B1153279 : Blo 1152637 1153279 := bstep (se 1 (by rfl) ⟨864959, by rfl⟩ : syracuseStep 1153279 = 1729919) B1729919
theorem B2923199 : Blo 1152637 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B2923361 : Blo 1152637 2923361 := bstep (se 2 (by rfl) ⟨1096260, by rfl⟩ : syracuseStep 2923361 = 2192521) B2192521
theorem B3284135 : Blo 1152637 3284135 := bstep (se 1 (by rfl) ⟨2463101, by rfl⟩ : syracuseStep 3284135 = 4926203) B4926203
theorem B2596175 : Blo 1152637 2596175 := bstep (se 1 (by rfl) ⟨1947131, by rfl⟩ : syracuseStep 2596175 = 3894263) B3894263
theorem B1646185 : Blo 1152637 1646185 := bstep (se 2 (by rfl) ⟨617319, by rfl⟩ : syracuseStep 1646185 = 1234639) B1234639
theorem B1155183 : Blo 1152637 1155183 := bstep (se 1 (by rfl) ⟨866387, by rfl⟩ : syracuseStep 1155183 = 1732775) B1732775
theorem B2924819 : Blo 1152637 2924819 := bstep (se 1 (by rfl) ⟨2193614, by rfl⟩ : syracuseStep 2924819 = 4387229) B4387229
theorem B1155567 : Blo 1152637 1155567 := bstep (se 1 (by rfl) ⟨866675, by rfl⟩ : syracuseStep 1155567 = 1733351) B1733351
theorem B1155631 : Blo 1152637 1155631 := bstep (se 1 (by rfl) ⟨866723, by rfl⟩ : syracuseStep 1155631 = 1733447) B1733447
theorem B1155903 : Blo 1152637 1155903 := bstep (se 1 (by rfl) ⟨866927, by rfl⟩ : syracuseStep 1155903 = 1733855) B1733855
theorem B1156063 : Blo 1152637 1156063 := bstep (se 1 (by rfl) ⟨867047, by rfl⟩ : syracuseStep 1156063 = 1734095) B1734095
theorem B3286241 : Blo 1152637 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B2926439 : Blo 1152637 2926439 := bstep (se 1 (by rfl) ⟨2194829, by rfl⟩ : syracuseStep 2926439 = 4389659) B4389659
theorem B14985647 : Blo 1152637 14985647 := bstep (se 1 (by rfl) ⟨11239235, by rfl⟩ : syracuseStep 14985647 = 22478471) B22478471
theorem B2599631 : Blo 1152637 2599631 := bstep (se 1 (by rfl) ⟨1949723, by rfl⟩ : syracuseStep 2599631 = 3899447) B3899447
theorem B12659611 : Blo 1152637 12659611 := bstep (se 1 (by rfl) ⟨9494708, by rfl⟩ : syracuseStep 12659611 = 18989417) B18989417
theorem B2600801 : Blo 1152637 2600801 := bstep (se 2 (by rfl) ⟨975300, by rfl⟩ : syracuseStep 2600801 = 1950601) B1950601
theorem B4437127 : Blo 1152637 4437127 := bstep (se 1 (by rfl) ⟨3327845, by rfl⟩ : syracuseStep 4437127 = 6655691) B6655691
theorem B2602223 : Blo 1152637 2602223 := bstep (se 1 (by rfl) ⟨1951667, by rfl⟩ : syracuseStep 2602223 = 3903335) B3903335
theorem B68467493 : Blo 1152637 68467493 := bstep (se 4 (by rfl) ⟨6418827, by rfl⟩ : syracuseStep 68467493 = 12837655) B12837655
theorem B14794235 : Blo 1152637 14794235 := bstep (se 1 (by rfl) ⟨11095676, by rfl⟩ : syracuseStep 14794235 = 22191353) B22191353
theorem B1950655 : Blo 1152637 1950655 := bstep (se 1 (by rfl) ⟨1462991, by rfl⟩ : syracuseStep 1950655 = 2925983) B2925983
theorem B9356269 : Blo 1152637 9356269 := bstep (se 3 (by rfl) ⟨1754300, by rfl⟩ : syracuseStep 9356269 = 3508601) B3508601
theorem B101074513 : Blo 1152637 101074513 := bstep (se 2 (by rfl) ⟨37902942, by rfl⟩ : syracuseStep 101074513 = 75805885) B75805885
theorem B2083295 : Blo 1152637 2083295 := bstep (se 1 (by rfl) ⟨1562471, by rfl⟩ : syracuseStep 2083295 = 3124943) B3124943
theorem B14798335 : Blo 1152637 14798335 := bstep (se 1 (by rfl) ⟨11098751, by rfl⟩ : syracuseStep 14798335 = 22197503) B22197503
theorem B284511923 : Blo 1152637 284511923 := bstep (se 1 (by rfl) ⟨213383942, by rfl⟩ : syracuseStep 284511923 = 426767885) B426767885
theorem B202398061 : Blo 1152637 202398061 := bstep (se 3 (by rfl) ⟨37949636, by rfl⟩ : syracuseStep 202398061 = 75899273) B75899273
theorem B4381199 : Blo 1152637 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B2220257 : Blo 1152637 2220257 := bstep (se 2 (by rfl) ⟨832596, by rfl⟩ : syracuseStep 2220257 = 1665193) B1665193
theorem B15198151 : Blo 1152637 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B9857051 : Blo 1152637 9857051 := bstep (se 1 (by rfl) ⟨7392788, by rfl⟩ : syracuseStep 9857051 = 14785577) B14785577
theorem B9366131 : Blo 1152637 9366131 := bstep (se 1 (by rfl) ⟨7024598, by rfl⟩ : syracuseStep 9366131 = 14049197) B14049197
theorem B1731431 : Blo 1152637 1731431 := bstep (se 1 (by rfl) ⟨1298573, by rfl⟩ : syracuseStep 1731431 = 2597147) B2597147
theorem B90009539 : Blo 1152637 90009539 := bstep (se 1 (by rfl) ⟨67507154, by rfl⟩ : syracuseStep 90009539 = 135014309) B135014309
theorem B2224199 : Blo 1152637 2224199 := bstep (se 1 (by rfl) ⟨1668149, by rfl⟩ : syracuseStep 2224199 = 3336299) B3336299
theorem B3895451 : Blo 1152637 3895451 := bstep (se 1 (by rfl) ⟨2921588, by rfl⟩ : syracuseStep 3895451 = 5843177) B5843177
theorem B1733147 : Blo 1152637 1733147 := bstep (se 1 (by rfl) ⟨1299860, by rfl⟩ : syracuseStep 1733147 = 2599721) B2599721
theorem B2192255 : Blo 1152637 2192255 := bstep (se 1 (by rfl) ⟨1644191, by rfl⟩ : syracuseStep 2192255 = 3288383) B3288383
theorem B287962289 : Blo 1152637 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B4158803 : Blo 1152637 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B1733999 : Blo 1152637 1733999 := bstep (se 1 (by rfl) ⟨1300499, by rfl⟩ : syracuseStep 1733999 = 2600999) B2600999
theorem B2193151 : Blo 1152637 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B1734719 : Blo 1152637 1734719 := bstep (se 1 (by rfl) ⟨1301039, by rfl⟩ : syracuseStep 1734719 = 2602079) B2602079
theorem B1407871 : Blo 1152637 1407871 := bstep (se 1 (by rfl) ⟨1055903, by rfl⟩ : syracuseStep 1407871 = 2111807) B2111807
theorem B3701737 : Blo 1152637 3701737 := bstep (se 2 (by rfl) ⟨1388151, by rfl⟩ : syracuseStep 3701737 = 2776303) B2776303
theorem B8322425 : Blo 1152637 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B5835239 : Blo 1152637 5835239 := bstep (se 1 (by rfl) ⟨4376429, by rfl⟩ : syracuseStep 5835239 = 8752859) B8752859
theorem B5835563 : Blo 1152637 5835563 := bstep (se 1 (by rfl) ⟨4376672, by rfl⟩ : syracuseStep 5835563 = 8753345) B8753345
theorem B16879481 : Blo 1152637 16879481 := bstep (se 2 (by rfl) ⟨6329805, by rfl⟩ : syracuseStep 16879481 = 12659611) B12659611
theorem B2920799 : Blo 1152637 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B7508645 : Blo 1152637 7508645 := bstep (se 4 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 7508645 = 1407871) B1407871
theorem B19731113 : Blo 1152637 19731113 := bstep (se 2 (by rfl) ⟨7399167, by rfl⟩ : syracuseStep 19731113 = 14798335) B14798335
theorem B1154287 : Blo 1152637 1154287 := bstep (se 1 (by rfl) ⟨865715, by rfl⟩ : syracuseStep 1154287 = 1731431) B1731431
theorem B2924201 : Blo 1152637 2924201 := bstep (se 2 (by rfl) ⟨1096575, by rfl⟩ : syracuseStep 2924201 = 2193151) B2193151
theorem B60006359 : Blo 1152637 60006359 := bstep (se 1 (by rfl) ⟨45004769, by rfl⟩ : syracuseStep 60006359 = 90009539) B90009539
theorem B1482799 : Blo 1152637 1482799 := bstep (se 1 (by rfl) ⟨1112099, by rfl⟩ : syracuseStep 1482799 = 2224199) B2224199
theorem B2596967 : Blo 1152637 2596967 := bstep (se 1 (by rfl) ⟨1947725, by rfl⟩ : syracuseStep 2596967 = 3895451) B3895451
theorem B1155431 : Blo 1152637 1155431 := bstep (se 1 (by rfl) ⟨866573, by rfl⟩ : syracuseStep 1155431 = 1733147) B1733147
theorem B1155999 : Blo 1152637 1155999 := bstep (se 1 (by rfl) ⟨866999, by rfl⟩ : syracuseStep 1155999 = 1733999) B1733999
theorem B1156479 : Blo 1152637 1156479 := bstep (se 1 (by rfl) ⟨867359, by rfl⟩ : syracuseStep 1156479 = 1734719) B1734719
theorem B5548283 : Blo 1152637 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B2600873 : Blo 1152637 2600873 := bstep (se 2 (by rfl) ⟨975327, by rfl⟩ : syracuseStep 2600873 = 1950655) B1950655
theorem B7909679 : Blo 1152637 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B1388863 : Blo 1152637 1388863 := bstep (se 1 (by rfl) ⟨1041647, by rfl⟩ : syracuseStep 1388863 = 2083295) B2083295
theorem B2601503 : Blo 1152637 2601503 := bstep (se 1 (by rfl) ⟨1951127, by rfl⟩ : syracuseStep 2601503 = 3902255) B3902255
theorem B189674615 : Blo 1152637 189674615 := bstep (se 1 (by rfl) ⟨142255961, by rfl⟩ : syracuseStep 189674615 = 284511923) B284511923
theorem B20264201 : Blo 1152637 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B8763551 : Blo 1152637 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B11090141 : Blo 1152637 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B1948799 : Blo 1152637 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B1948907 : Blo 1152637 1948907 := bstep (se 1 (by rfl) ⟨1461680, by rfl⟩ : syracuseStep 1948907 = 2923361) B2923361
theorem B1949879 : Blo 1152637 1949879 := bstep (se 1 (by rfl) ⟨1462409, by rfl⟩ : syracuseStep 1949879 = 2924819) B2924819
theorem B1950959 : Blo 1152637 1950959 := bstep (se 1 (by rfl) ⟨1463219, by rfl⟩ : syracuseStep 1950959 = 2926439) B2926439
theorem B6571367 : Blo 1152637 6571367 := bstep (se 1 (by rfl) ⟨4928525, by rfl⟩ : syracuseStep 6571367 = 9857051) B9857051
theorem B5916169 : Blo 1152637 5916169 := bstep (se 2 (by rfl) ⟨2218563, by rfl⟩ : syracuseStep 5916169 = 4437127) B4437127
theorem B6244087 : Blo 1152637 6244087 := bstep (se 1 (by rfl) ⟨4683065, by rfl⟩ : syracuseStep 6244087 = 9366131) B9366131
theorem B269864081 : Blo 1152637 269864081 := bstep (se 2 (by rfl) ⟨101199030, by rfl⟩ : syracuseStep 269864081 = 202398061) B202398061
theorem B1461503 : Blo 1152637 1461503 := bstep (se 1 (by rfl) ⟨1096127, by rfl⟩ : syracuseStep 1461503 = 2192255) B2192255
theorem B191974859 : Blo 1152637 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B4935649 : Blo 1152637 4935649 := bstep (se 2 (by rfl) ⟨1850868, by rfl⟩ : syracuseStep 4935649 = 3701737) B3701737
theorem B5920685 : Blo 1152637 5920685 := bstep (se 3 (by rfl) ⟨1110128, by rfl⟩ : syracuseStep 5920685 = 2220257) B2220257
theorem B12475025 : Blo 1152637 12475025 := bstep (se 2 (by rfl) ⟨4678134, by rfl⟩ : syracuseStep 12475025 = 9356269) B9356269
theorem B134766017 : Blo 1152637 134766017 := bstep (se 2 (by rfl) ⟨50537256, by rfl⟩ : syracuseStep 134766017 = 101074513) B101074513
theorem B1729403 : Blo 1152637 1729403 := bstep (se 1 (by rfl) ⟨1297052, by rfl⟩ : syracuseStep 1729403 = 2594105) B2594105
theorem B1730027 : Blo 1152637 1730027 := bstep (se 1 (by rfl) ⟨1297520, by rfl⟩ : syracuseStep 1730027 = 2595041) B2595041
theorem B2189423 : Blo 1152637 2189423 := bstep (se 1 (by rfl) ⟨1642067, by rfl⟩ : syracuseStep 2189423 = 3284135) B3284135
theorem B1730783 : Blo 1152637 1730783 := bstep (se 1 (by rfl) ⟨1298087, by rfl⟩ : syracuseStep 1730783 = 2596175) B2596175
theorem B2190827 : Blo 1152637 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B9990431 : Blo 1152637 9990431 := bstep (se 1 (by rfl) ⟨7492823, by rfl⟩ : syracuseStep 9990431 = 14985647) B14985647
theorem B1733087 : Blo 1152637 1733087 := bstep (se 1 (by rfl) ⟨1299815, by rfl⟩ : syracuseStep 1733087 = 2599631) B2599631
theorem B1733867 : Blo 1152637 1733867 := bstep (se 1 (by rfl) ⟨1300400, by rfl⟩ : syracuseStep 1733867 = 2600801) B2600801
theorem B1734815 : Blo 1152637 1734815 := bstep (se 1 (by rfl) ⟨1301111, by rfl⟩ : syracuseStep 1734815 = 2602223) B2602223
theorem B45644995 : Blo 1152637 45644995 := bstep (se 1 (by rfl) ⟨34233746, by rfl⟩ : syracuseStep 45644995 = 68467493) B68467493
theorem B2194913 : Blo 1152637 2194913 := bstep (se 2 (by rfl) ⟨823092, by rfl⟩ : syracuseStep 2194913 = 1646185) B1646185
theorem B9862823 : Blo 1152637 9862823 := bstep (se 1 (by rfl) ⟨7397117, by rfl⟩ : syracuseStep 9862823 = 14794235) B14794235
theorem B8325449 : Blo 1152637 8325449 := bstep (se 2 (by rfl) ⟨3122043, by rfl⟩ : syracuseStep 8325449 = 6244087) B6244087
theorem B1152935 : Blo 1152637 1152935 := bstep (se 1 (by rfl) ⟨864701, by rfl⟩ : syracuseStep 1152935 = 1729403) B1729403
theorem B1153351 : Blo 1152637 1153351 := bstep (se 1 (by rfl) ⟨865013, by rfl⟩ : syracuseStep 1153351 = 1730027) B1730027
theorem B1153855 : Blo 1152637 1153855 := bstep (se 1 (by rfl) ⟨865391, by rfl⟩ : syracuseStep 1153855 = 1730783) B1730783
theorem B6660287 : Blo 1152637 6660287 := bstep (se 1 (by rfl) ⟨4995215, by rfl⟩ : syracuseStep 6660287 = 9990431) B9990431
theorem B1155391 : Blo 1152637 1155391 := bstep (se 1 (by rfl) ⟨866543, by rfl⟩ : syracuseStep 1155391 = 1733087) B1733087
theorem B1155911 : Blo 1152637 1155911 := bstep (se 1 (by rfl) ⟨866933, by rfl⟩ : syracuseStep 1155911 = 1733867) B1733867
theorem B13509467 : Blo 1152637 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B5842205 : Blo 1152637 5842205 := bstep (se 3 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 5842205 = 2190827) B2190827
theorem B5842367 : Blo 1152637 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B1156543 : Blo 1152637 1156543 := bstep (se 1 (by rfl) ⟨867407, by rfl⟩ : syracuseStep 1156543 = 1734815) B1734815
theorem B60859993 : Blo 1152637 60859993 := bstep (se 2 (by rfl) ⟨22822497, by rfl⟩ : syracuseStep 60859993 = 45644995) B45644995
theorem B1977065 : Blo 1152637 1977065 := bstep (se 2 (by rfl) ⟨741399, by rfl⟩ : syracuseStep 1977065 = 1482799) B1482799
theorem B179909387 : Blo 1152637 179909387 := bstep (se 1 (by rfl) ⟨134932040, by rfl⟩ : syracuseStep 179909387 = 269864081) B269864081
theorem B11252987 : Blo 1152637 11252987 := bstep (se 1 (by rfl) ⟨8439740, by rfl⟩ : syracuseStep 11252987 = 16879481) B16879481
theorem B1947199 : Blo 1152637 1947199 := bstep (se 1 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 1947199 = 2920799) B2920799
theorem B13154075 : Blo 1152637 13154075 := bstep (se 1 (by rfl) ⟨9865556, by rfl⟩ : syracuseStep 13154075 = 19731113) B19731113
theorem B3947123 : Blo 1152637 3947123 := bstep (se 1 (by rfl) ⟨2960342, by rfl⟩ : syracuseStep 3947123 = 5920685) B5920685
theorem B1949467 : Blo 1152637 1949467 := bstep (se 1 (by rfl) ⟨1462100, by rfl⟩ : syracuseStep 1949467 = 2924201) B2924201
theorem B1851817 : Blo 1152637 1851817 := bstep (se 2 (by rfl) ⟨694431, by rfl⟩ : syracuseStep 1851817 = 1388863) B1388863
theorem B1459615 : Blo 1152637 1459615 := bstep (se 1 (by rfl) ⟨1094711, by rfl⟩ : syracuseStep 1459615 = 2189423) B2189423
theorem B7393427 : Blo 1152637 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B1299199 : Blo 1152637 1299199 := bstep (se 1 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 1299199 = 1948799) B1948799
theorem B1299271 : Blo 1152637 1299271 := bstep (se 1 (by rfl) ⟨974453, by rfl⟩ : syracuseStep 1299271 = 1948907) B1948907
theorem B1463275 : Blo 1152637 1463275 := bstep (se 1 (by rfl) ⟨1097456, by rfl⟩ : syracuseStep 1463275 = 2194913) B2194913
theorem B6575215 : Blo 1152637 6575215 := bstep (se 1 (by rfl) ⟨4931411, by rfl⟩ : syracuseStep 6575215 = 9862823) B9862823
theorem B1299919 : Blo 1152637 1299919 := bstep (se 1 (by rfl) ⟨974939, by rfl⟩ : syracuseStep 1299919 = 1949879) B1949879
theorem B1300639 : Blo 1152637 1300639 := bstep (se 1 (by rfl) ⟨975479, by rfl⟩ : syracuseStep 1300639 = 1950959) B1950959
theorem B4380911 : Blo 1152637 4380911 := bstep (se 1 (by rfl) ⟨3285683, by rfl⟩ : syracuseStep 4380911 = 6571367) B6571367
theorem B3890159 : Blo 1152637 3890159 := bstep (se 1 (by rfl) ⟨2917619, by rfl⟩ : syracuseStep 3890159 = 5835239) B5835239
theorem B3890375 : Blo 1152637 3890375 := bstep (se 1 (by rfl) ⟨2917781, by rfl⟩ : syracuseStep 3890375 = 5835563) B5835563
theorem B7888225 : Blo 1152637 7888225 := bstep (se 2 (by rfl) ⟨2958084, by rfl⟩ : syracuseStep 7888225 = 5916169) B5916169
theorem B127983239 : Blo 1152637 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B5005763 : Blo 1152637 5005763 := bstep (se 1 (by rfl) ⟨3754322, by rfl⟩ : syracuseStep 5005763 = 7508645) B7508645
theorem B8316683 : Blo 1152637 8316683 := bstep (se 1 (by rfl) ⟨6237512, by rfl⟩ : syracuseStep 8316683 = 12475025) B12475025
theorem B89844011 : Blo 1152637 89844011 := bstep (se 1 (by rfl) ⟨67383008, by rfl⟩ : syracuseStep 89844011 = 134766017) B134766017
theorem B6580865 : Blo 1152637 6580865 := bstep (se 2 (by rfl) ⟨2467824, by rfl⟩ : syracuseStep 6580865 = 4935649) B4935649
theorem B40004239 : Blo 1152637 40004239 := bstep (se 1 (by rfl) ⟨30003179, by rfl⟩ : syracuseStep 40004239 = 60006359) B60006359
theorem B1731311 : Blo 1152637 1731311 := bstep (se 1 (by rfl) ⟨1298483, by rfl⟩ : syracuseStep 1731311 = 2596967) B2596967
theorem B3698855 : Blo 1152637 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B1733915 : Blo 1152637 1733915 := bstep (se 1 (by rfl) ⟨1300436, by rfl⟩ : syracuseStep 1733915 = 2600873) B2600873
theorem B5273119 : Blo 1152637 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B1734335 : Blo 1152637 1734335 := bstep (se 1 (by rfl) ⟨1300751, by rfl⟩ : syracuseStep 1734335 = 2601503) B2601503
theorem B3897341 : Blo 1152637 3897341 := bstep (se 3 (by rfl) ⟨730751, by rfl⟩ : syracuseStep 3897341 = 1461503) B1461503
theorem B126449743 : Blo 1152637 126449743 := bstep (se 1 (by rfl) ⟨94837307, by rfl⟩ : syracuseStep 126449743 = 189674615) B189674615
theorem B2920607 : Blo 1152637 2920607 := bstep (se 1 (by rfl) ⟨2190455, by rfl⟩ : syracuseStep 2920607 = 4380911) B4380911
theorem B2593439 : Blo 1152637 2593439 := bstep (se 1 (by rfl) ⟨1945079, by rfl⟩ : syracuseStep 2593439 = 3890159) B3890159
theorem B2593583 : Blo 1152637 2593583 := bstep (se 1 (by rfl) ⟨1945187, by rfl⟩ : syracuseStep 2593583 = 3890375) B3890375
theorem B5544455 : Blo 1152637 5544455 := bstep (se 1 (by rfl) ⟨4158341, by rfl⟩ : syracuseStep 5544455 = 8316683) B8316683
theorem B1318043 : Blo 1152637 1318043 := bstep (se 1 (by rfl) ⟨988532, by rfl⟩ : syracuseStep 1318043 = 1977065) B1977065
theorem B1154207 : Blo 1152637 1154207 := bstep (se 1 (by rfl) ⟨865655, by rfl⟩ : syracuseStep 1154207 = 1731311) B1731311
theorem B2596265 : Blo 1152637 2596265 := bstep (se 2 (by rfl) ⟨973599, by rfl⟩ : syracuseStep 2596265 = 1947199) B1947199
theorem B168599657 : Blo 1152637 168599657 := bstep (se 2 (by rfl) ⟨63224871, by rfl⟩ : syracuseStep 168599657 = 126449743) B126449743
theorem B2465903 : Blo 1152637 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B28123301 : Blo 1152637 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B119939591 : Blo 1152637 119939591 := bstep (se 1 (by rfl) ⟨89954693, by rfl⟩ : syracuseStep 119939591 = 179909387) B179909387
theorem B1155943 : Blo 1152637 1155943 := bstep (se 1 (by rfl) ⟨866957, by rfl⟩ : syracuseStep 1155943 = 1733915) B1733915
theorem B1156223 : Blo 1152637 1156223 := bstep (se 1 (by rfl) ⟨867167, by rfl⟩ : syracuseStep 1156223 = 1734335) B1734335
theorem B2598227 : Blo 1152637 2598227 := bstep (se 1 (by rfl) ⟨1948670, by rfl⟩ : syracuseStep 2598227 = 3897341) B3897341
theorem B2631415 : Blo 1152637 2631415 := bstep (se 1 (by rfl) ⟨1973561, by rfl⟩ : syracuseStep 2631415 = 3947123) B3947123
theorem B2599289 : Blo 1152637 2599289 := bstep (se 2 (by rfl) ⟨974733, by rfl⟩ : syracuseStep 2599289 = 1949467) B1949467
theorem B2469089 : Blo 1152637 2469089 := bstep (se 2 (by rfl) ⟨925908, by rfl⟩ : syracuseStep 2469089 = 1851817) B1851817
theorem B5550299 : Blo 1152637 5550299 := bstep (se 1 (by rfl) ⟨4162724, by rfl⟩ : syracuseStep 5550299 = 8325449) B8325449
theorem B1946153 : Blo 1152637 1946153 := bstep (se 2 (by rfl) ⟨729807, by rfl⟩ : syracuseStep 1946153 = 1459615) B1459615
theorem B81146657 : Blo 1152637 81146657 := bstep (se 2 (by rfl) ⟨30429996, by rfl⟩ : syracuseStep 81146657 = 60859993) B60859993
theorem B4928951 : Blo 1152637 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B4440191 : Blo 1152637 4440191 := bstep (se 1 (by rfl) ⟨3330143, by rfl⟩ : syracuseStep 4440191 = 6660287) B6660287
theorem B1951033 : Blo 1152637 1951033 := bstep (se 2 (by rfl) ⟨731637, by rfl⟩ : syracuseStep 1951033 = 1463275) B1463275
theorem B8766953 : Blo 1152637 8766953 := bstep (se 2 (by rfl) ⟨3287607, by rfl⟩ : syracuseStep 8766953 = 6575215) B6575215
theorem B8769383 : Blo 1152637 8769383 := bstep (se 1 (by rfl) ⟨6577037, by rfl⟩ : syracuseStep 8769383 = 13154075) B13154075
theorem B53338985 : Blo 1152637 53338985 := bstep (se 2 (by rfl) ⟨20002119, by rfl⟩ : syracuseStep 53338985 = 40004239) B40004239
theorem B85322159 : Blo 1152637 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B3337175 : Blo 1152637 3337175 := bstep (se 1 (by rfl) ⟨2502881, by rfl⟩ : syracuseStep 3337175 = 5005763) B5005763
theorem B9006311 : Blo 1152637 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B3894803 : Blo 1152637 3894803 := bstep (se 1 (by rfl) ⟨2921102, by rfl⟩ : syracuseStep 3894803 = 5842205) B5842205
theorem B3894911 : Blo 1152637 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B1732265 : Blo 1152637 1732265 := bstep (se 2 (by rfl) ⟨649599, by rfl⟩ : syracuseStep 1732265 = 1299199) B1299199
theorem B1732361 : Blo 1152637 1732361 := bstep (se 2 (by rfl) ⟨649635, by rfl⟩ : syracuseStep 1732361 = 1299271) B1299271
theorem B59896007 : Blo 1152637 59896007 := bstep (se 1 (by rfl) ⟨44922005, by rfl⟩ : syracuseStep 59896007 = 89844011) B89844011
theorem B4387243 : Blo 1152637 4387243 := bstep (se 1 (by rfl) ⟨3290432, by rfl⟩ : syracuseStep 4387243 = 6580865) B6580865
theorem B1733225 : Blo 1152637 1733225 := bstep (se 2 (by rfl) ⟨649959, by rfl⟩ : syracuseStep 1733225 = 1299919) B1299919
theorem B1734185 : Blo 1152637 1734185 := bstep (se 2 (by rfl) ⟨650319, by rfl⟩ : syracuseStep 1734185 = 1300639) B1300639
theorem B7501991 : Blo 1152637 7501991 := bstep (se 1 (by rfl) ⟨5626493, by rfl⟩ : syracuseStep 7501991 = 11252987) B11252987
theorem B10517633 : Blo 1152637 10517633 := bstep (se 2 (by rfl) ⟨3944112, by rfl⟩ : syracuseStep 10517633 = 7888225) B7888225
theorem B3508553 : Blo 1152637 3508553 := bstep (se 2 (by rfl) ⟨1315707, by rfl⟩ : syracuseStep 3508553 = 2631415) B2631415
theorem B13143869 : Blo 1152637 13143869 := bstep (se 3 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 13143869 = 4928951) B4928951
theorem B112399771 : Blo 1152637 112399771 := bstep (se 1 (by rfl) ⟨84299828, by rfl⟩ : syracuseStep 112399771 = 168599657) B168599657
theorem B18748867 : Blo 1152637 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B79959727 : Blo 1152637 79959727 := bstep (se 1 (by rfl) ⟨59969795, by rfl⟩ : syracuseStep 79959727 = 119939591) B119939591
theorem B35559323 : Blo 1152637 35559323 := bstep (se 1 (by rfl) ⟨26669492, by rfl⟩ : syracuseStep 35559323 = 53338985) B53338985
theorem B14785213 : Blo 1152637 14785213 := bstep (se 3 (by rfl) ⟨2772227, by rfl⟩ : syracuseStep 14785213 = 5544455) B5544455
theorem B6004207 : Blo 1152637 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B2596535 : Blo 1152637 2596535 := bstep (se 1 (by rfl) ⟨1947401, by rfl⟩ : syracuseStep 2596535 = 3894803) B3894803
theorem B2596607 : Blo 1152637 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B1154843 : Blo 1152637 1154843 := bstep (se 1 (by rfl) ⟨866132, by rfl⟩ : syracuseStep 1154843 = 1732265) B1732265
theorem B1154907 : Blo 1152637 1154907 := bstep (se 1 (by rfl) ⟨866180, by rfl⟩ : syracuseStep 1154907 = 1732361) B1732361
theorem B1155483 : Blo 1152637 1155483 := bstep (se 1 (by rfl) ⟨866612, by rfl⟩ : syracuseStep 1155483 = 1733225) B1733225
theorem B3514781 : Blo 1152637 3514781 := bstep (se 3 (by rfl) ⟨659021, by rfl⟩ : syracuseStep 3514781 = 1318043) B1318043
theorem B1156123 : Blo 1152637 1156123 := bstep (se 1 (by rfl) ⟨867092, by rfl⟩ : syracuseStep 1156123 = 1734185) B1734185
theorem B11840509 : Blo 1152637 11840509 := bstep (se 3 (by rfl) ⟨2220095, by rfl⟩ : syracuseStep 11840509 = 4440191) B4440191
theorem B5844635 : Blo 1152637 5844635 := bstep (se 1 (by rfl) ⟨4383476, by rfl⟩ : syracuseStep 5844635 = 8766953) B8766953
theorem B2601377 : Blo 1152637 2601377 := bstep (se 2 (by rfl) ⟨975516, by rfl⟩ : syracuseStep 2601377 = 1951033) B1951033
theorem B5846255 : Blo 1152637 5846255 := bstep (se 1 (by rfl) ⟨4384691, by rfl⟩ : syracuseStep 5846255 = 8769383) B8769383
theorem B1947071 : Blo 1152637 1947071 := bstep (se 1 (by rfl) ⟨1460303, by rfl⟩ : syracuseStep 1947071 = 2920607) B2920607
theorem B20005309 : Blo 1152637 20005309 := bstep (se 3 (by rfl) ⟨3750995, by rfl⟩ : syracuseStep 20005309 = 7501991) B7501991
theorem B5849657 : Blo 1152637 5849657 := bstep (se 2 (by rfl) ⟨2193621, by rfl⟩ : syracuseStep 5849657 = 4387243) B4387243
theorem B39930671 : Blo 1152637 39930671 := bstep (se 1 (by rfl) ⟨29948003, by rfl⟩ : syracuseStep 39930671 = 59896007) B59896007
theorem B1297435 : Blo 1152637 1297435 := bstep (se 1 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 1297435 = 1946153) B1946153
theorem B6575741 : Blo 1152637 6575741 := bstep (se 3 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 6575741 = 2465903) B2465903
theorem B216391085 : Blo 1152637 216391085 := bstep (se 3 (by rfl) ⟨40573328, by rfl⟩ : syracuseStep 216391085 = 81146657) B81146657
theorem B1728959 : Blo 1152637 1728959 := bstep (se 1 (by rfl) ⟨1296719, by rfl⟩ : syracuseStep 1728959 = 2593439) B2593439
theorem B1729055 : Blo 1152637 1729055 := bstep (se 1 (by rfl) ⟨1296791, by rfl⟩ : syracuseStep 1729055 = 2593583) B2593583
theorem B1730843 : Blo 1152637 1730843 := bstep (se 1 (by rfl) ⟨1298132, by rfl⟩ : syracuseStep 1730843 = 2596265) B2596265
theorem B1732151 : Blo 1152637 1732151 := bstep (se 1 (by rfl) ⟨1299113, by rfl⟩ : syracuseStep 1732151 = 2598227) B2598227
theorem B1732859 : Blo 1152637 1732859 := bstep (se 1 (by rfl) ⟨1299644, by rfl⟩ : syracuseStep 1732859 = 2599289) B2599289
theorem B56881439 : Blo 1152637 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B2224783 : Blo 1152637 2224783 := bstep (se 1 (by rfl) ⟨1668587, by rfl⟩ : syracuseStep 2224783 = 3337175) B3337175
theorem B3700199 : Blo 1152637 3700199 := bstep (se 1 (by rfl) ⟨2775149, by rfl⟩ : syracuseStep 3700199 = 5550299) B5550299
theorem B6584237 : Blo 1152637 6584237 := bstep (se 3 (by rfl) ⟨1234544, by rfl⟩ : syracuseStep 6584237 = 2469089) B2469089
theorem B7011755 : Blo 1152637 7011755 := bstep (se 1 (by rfl) ⟨5258816, by rfl⟩ : syracuseStep 7011755 = 10517633) B10517633
theorem B3899771 : Blo 1152637 3899771 := bstep (se 1 (by rfl) ⟨2924828, by rfl⟩ : syracuseStep 3899771 = 5849657) B5849657
theorem B106694981 : Blo 1152637 106694981 := bstep (se 4 (by rfl) ⟨10002654, by rfl⟩ : syracuseStep 106694981 = 20005309) B20005309
theorem B9867197 : Blo 1152637 9867197 := bstep (se 3 (by rfl) ⟨1850099, by rfl⟩ : syracuseStep 9867197 = 3700199) B3700199
theorem B1152639 : Blo 1152637 1152639 := bstep (se 1 (by rfl) ⟨864479, by rfl⟩ : syracuseStep 1152639 = 1728959) B1728959
theorem B1152703 : Blo 1152637 1152703 := bstep (se 1 (by rfl) ⟨864527, by rfl⟩ : syracuseStep 1152703 = 1729055) B1729055
theorem B1153895 : Blo 1152637 1153895 := bstep (se 1 (by rfl) ⟨865421, by rfl⟩ : syracuseStep 1153895 = 1730843) B1730843
theorem B1154767 : Blo 1152637 1154767 := bstep (se 1 (by rfl) ⟨866075, by rfl⟩ : syracuseStep 1154767 = 1732151) B1732151
theorem B1155239 : Blo 1152637 1155239 := bstep (se 1 (by rfl) ⟨866429, by rfl⟩ : syracuseStep 1155239 = 1732859) B1732859
theorem B37920959 : Blo 1152637 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B8005609 : Blo 1152637 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B26620447 : Blo 1152637 26620447 := bstep (se 1 (by rfl) ⟨19965335, by rfl⟩ : syracuseStep 26620447 = 39930671) B39930671
theorem B8762579 : Blo 1152637 8762579 := bstep (se 1 (by rfl) ⟨6571934, by rfl⟩ : syracuseStep 8762579 = 13143869) B13143869
theorem B23706215 : Blo 1152637 23706215 := bstep (se 1 (by rfl) ⟨17779661, by rfl⟩ : syracuseStep 23706215 = 35559323) B35559323
theorem B144260723 : Blo 1152637 144260723 := bstep (se 1 (by rfl) ⟨108195542, by rfl⟩ : syracuseStep 144260723 = 216391085) B216391085
theorem B2343187 : Blo 1152637 2343187 := bstep (se 1 (by rfl) ⟨1757390, by rfl⟩ : syracuseStep 2343187 = 3514781) B3514781
theorem B2966377 : Blo 1152637 2966377 := bstep (se 2 (by rfl) ⟨1112391, by rfl⟩ : syracuseStep 2966377 = 2224783) B2224783
theorem B9356141 : Blo 1152637 9356141 := bstep (se 3 (by rfl) ⟨1754276, by rfl⟩ : syracuseStep 9356141 = 3508553) B3508553
theorem B149866361 : Blo 1152637 149866361 := bstep (se 2 (by rfl) ⟨56199885, by rfl⟩ : syracuseStep 149866361 = 112399771) B112399771
theorem B106612969 : Blo 1152637 106612969 := bstep (se 2 (by rfl) ⟨39979863, by rfl⟩ : syracuseStep 106612969 = 79959727) B79959727
theorem B19713617 : Blo 1152637 19713617 := bstep (se 2 (by rfl) ⟨7392606, by rfl⟩ : syracuseStep 19713617 = 14785213) B14785213
theorem B1298047 : Blo 1152637 1298047 := bstep (se 1 (by rfl) ⟨973535, by rfl⟩ : syracuseStep 1298047 = 1947071) B1947071
theorem B4674503 : Blo 1152637 4674503 := bstep (se 1 (by rfl) ⟨3505877, by rfl⟩ : syracuseStep 4674503 = 7011755) B7011755
theorem B4383827 : Blo 1152637 4383827 := bstep (se 1 (by rfl) ⟨3287870, by rfl⟩ : syracuseStep 4383827 = 6575741) B6575741
theorem B15787345 : Blo 1152637 15787345 := bstep (se 2 (by rfl) ⟨5920254, by rfl⟩ : syracuseStep 15787345 = 11840509) B11840509
theorem B1729913 : Blo 1152637 1729913 := bstep (se 2 (by rfl) ⟨648717, by rfl⟩ : syracuseStep 1729913 = 1297435) B1297435
theorem B1731023 : Blo 1152637 1731023 := bstep (se 1 (by rfl) ⟨1298267, by rfl⟩ : syracuseStep 1731023 = 2596535) B2596535
theorem B1731071 : Blo 1152637 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B24998489 : Blo 1152637 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B3896423 : Blo 1152637 3896423 := bstep (se 1 (by rfl) ⟨2922317, by rfl⟩ : syracuseStep 3896423 = 5844635) B5844635
theorem B1734251 : Blo 1152637 1734251 := bstep (se 1 (by rfl) ⟨1300688, by rfl⟩ : syracuseStep 1734251 = 2601377) B2601377
theorem B3897503 : Blo 1152637 3897503 := bstep (se 1 (by rfl) ⟨2923127, by rfl⟩ : syracuseStep 3897503 = 5846255) B5846255
theorem B4389491 : Blo 1152637 4389491 := bstep (se 1 (by rfl) ⟨3292118, by rfl⟩ : syracuseStep 4389491 = 6584237) B6584237
theorem B99910907 : Blo 1152637 99910907 := bstep (se 1 (by rfl) ⟨74933180, by rfl⟩ : syracuseStep 99910907 = 149866361) B149866361
theorem B13142411 : Blo 1152637 13142411 := bstep (se 1 (by rfl) ⟨9856808, by rfl⟩ : syracuseStep 13142411 = 19713617) B19713617
theorem B142150625 : Blo 1152637 142150625 := bstep (se 2 (by rfl) ⟨53306484, by rfl⟩ : syracuseStep 142150625 = 106612969) B106612969
theorem B3116335 : Blo 1152637 3116335 := bstep (se 1 (by rfl) ⟨2337251, by rfl⟩ : syracuseStep 3116335 = 4674503) B4674503
theorem B35493929 : Blo 1152637 35493929 := bstep (se 2 (by rfl) ⟨13310223, by rfl⟩ : syracuseStep 35493929 = 26620447) B26620447
theorem B2922551 : Blo 1152637 2922551 := bstep (se 1 (by rfl) ⟨2191913, by rfl⟩ : syracuseStep 2922551 = 4383827) B4383827
theorem B1153275 : Blo 1152637 1153275 := bstep (se 1 (by rfl) ⟨864956, by rfl⟩ : syracuseStep 1153275 = 1729913) B1729913
theorem B1154015 : Blo 1152637 1154015 := bstep (se 1 (by rfl) ⟨865511, by rfl⟩ : syracuseStep 1154015 = 1731023) B1731023
theorem B1154047 : Blo 1152637 1154047 := bstep (se 1 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 1154047 = 1731071) B1731071
theorem B2597615 : Blo 1152637 2597615 := bstep (se 1 (by rfl) ⟨1948211, by rfl⟩ : syracuseStep 2597615 = 3896423) B3896423
theorem B5841719 : Blo 1152637 5841719 := bstep (se 1 (by rfl) ⟨4381289, by rfl⟩ : syracuseStep 5841719 = 8762579) B8762579
theorem B1156167 : Blo 1152637 1156167 := bstep (se 1 (by rfl) ⟨867125, by rfl⟩ : syracuseStep 1156167 = 1734251) B1734251
theorem B2598335 : Blo 1152637 2598335 := bstep (se 1 (by rfl) ⟨1948751, by rfl⟩ : syracuseStep 2598335 = 3897503) B3897503
theorem B15804143 : Blo 1152637 15804143 := bstep (se 1 (by rfl) ⟨11853107, by rfl⟩ : syracuseStep 15804143 = 23706215) B23706215
theorem B2926327 : Blo 1152637 2926327 := bstep (se 1 (by rfl) ⟨2194745, by rfl⟩ : syracuseStep 2926327 = 4389491) B4389491
theorem B2599847 : Blo 1152637 2599847 := bstep (se 1 (by rfl) ⟨1949885, by rfl⟩ : syracuseStep 2599847 = 3899771) B3899771
theorem B6237427 : Blo 1152637 6237427 := bstep (se 1 (by rfl) ⟨4678070, by rfl⟩ : syracuseStep 6237427 = 9356141) B9356141
theorem B12496997 : Blo 1152637 12496997 := bstep (se 4 (by rfl) ⟨1171593, by rfl⟩ : syracuseStep 12496997 = 2343187) B2343187
theorem B21049793 : Blo 1152637 21049793 := bstep (se 2 (by rfl) ⟨7893672, by rfl⟩ : syracuseStep 21049793 = 15787345) B15787345
theorem B25280639 : Blo 1152637 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B16665659 : Blo 1152637 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B3955169 : Blo 1152637 3955169 := bstep (se 2 (by rfl) ⟨1483188, by rfl⟩ : syracuseStep 3955169 = 2966377) B2966377
theorem B71129987 : Blo 1152637 71129987 := bstep (se 1 (by rfl) ⟨53347490, by rfl⟩ : syracuseStep 71129987 = 106694981) B106694981
theorem B6578131 : Blo 1152637 6578131 := bstep (se 1 (by rfl) ⟨4933598, by rfl⟩ : syracuseStep 6578131 = 9867197) B9867197
theorem B10674145 : Blo 1152637 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B1730729 : Blo 1152637 1730729 := bstep (se 2 (by rfl) ⟨649023, by rfl⟩ : syracuseStep 1730729 = 1298047) B1298047
theorem B96173815 : Blo 1152637 96173815 := bstep (se 1 (by rfl) ⟨72130361, by rfl⟩ : syracuseStep 96173815 = 144260723) B144260723
theorem B94767083 : Blo 1152637 94767083 := bstep (se 1 (by rfl) ⟨71075312, by rfl⟩ : syracuseStep 94767083 = 142150625) B142150625
theorem B11110439 : Blo 1152637 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B3901769 : Blo 1152637 3901769 := bstep (se 2 (by rfl) ⟨1463163, by rfl⟩ : syracuseStep 3901769 = 2926327) B2926327
theorem B23662619 : Blo 1152637 23662619 := bstep (se 1 (by rfl) ⟨17746964, by rfl⟩ : syracuseStep 23662619 = 35493929) B35493929
theorem B47419991 : Blo 1152637 47419991 := bstep (se 1 (by rfl) ⟨35564993, by rfl⟩ : syracuseStep 47419991 = 71129987) B71129987
theorem B1153819 : Blo 1152637 1153819 := bstep (se 1 (by rfl) ⟨865364, by rfl⟩ : syracuseStep 1153819 = 1730729) B1730729
theorem B8331331 : Blo 1152637 8331331 := bstep (se 1 (by rfl) ⟨6248498, by rfl⟩ : syracuseStep 8331331 = 12496997) B12496997
theorem B14033195 : Blo 1152637 14033195 := bstep (se 1 (by rfl) ⟨10524896, by rfl⟩ : syracuseStep 14033195 = 21049793) B21049793
theorem B128231753 : Blo 1152637 128231753 := bstep (se 2 (by rfl) ⟨48086907, by rfl⟩ : syracuseStep 128231753 = 96173815) B96173815
theorem B14232193 : Blo 1152637 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B16853759 : Blo 1152637 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B8761607 : Blo 1152637 8761607 := bstep (se 1 (by rfl) ⟨6571205, by rfl⟩ : syracuseStep 8761607 = 13142411) B13142411
theorem B1948367 : Blo 1152637 1948367 := bstep (se 1 (by rfl) ⟨1461275, by rfl⟩ : syracuseStep 1948367 = 2922551) B2922551
theorem B10536095 : Blo 1152637 10536095 := bstep (se 1 (by rfl) ⟨7902071, by rfl⟩ : syracuseStep 10536095 = 15804143) B15804143
theorem B8770841 : Blo 1152637 8770841 := bstep (se 2 (by rfl) ⟨3289065, by rfl⟩ : syracuseStep 8770841 = 6578131) B6578131
theorem B66607271 : Blo 1152637 66607271 := bstep (se 1 (by rfl) ⟨49955453, by rfl⟩ : syracuseStep 66607271 = 99910907) B99910907
theorem B8316569 : Blo 1152637 8316569 := bstep (se 2 (by rfl) ⟨3118713, by rfl⟩ : syracuseStep 8316569 = 6237427) B6237427
theorem B4155113 : Blo 1152637 4155113 := bstep (se 2 (by rfl) ⟨1558167, by rfl⟩ : syracuseStep 4155113 = 3116335) B3116335
theorem B1731743 : Blo 1152637 1731743 := bstep (se 1 (by rfl) ⟨1298807, by rfl⟩ : syracuseStep 1731743 = 2597615) B2597615
theorem B3894479 : Blo 1152637 3894479 := bstep (se 1 (by rfl) ⟨2920859, by rfl⟩ : syracuseStep 3894479 = 5841719) B5841719
theorem B1732223 : Blo 1152637 1732223 := bstep (se 1 (by rfl) ⟨1299167, by rfl⟩ : syracuseStep 1732223 = 2598335) B2598335
theorem B10547117 : Blo 1152637 10547117 := bstep (se 3 (by rfl) ⟨1977584, by rfl⟩ : syracuseStep 10547117 = 3955169) B3955169
theorem B1733231 : Blo 1152637 1733231 := bstep (se 1 (by rfl) ⟨1299923, by rfl⟩ : syracuseStep 1733231 = 2599847) B2599847
theorem B11108441 : Blo 1152637 11108441 := bstep (se 2 (by rfl) ⟨4165665, by rfl⟩ : syracuseStep 11108441 = 8331331) B8331331
theorem B63178055 : Blo 1152637 63178055 := bstep (se 1 (by rfl) ⟨47383541, by rfl⟩ : syracuseStep 63178055 = 94767083) B94767083
theorem B7406959 : Blo 1152637 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B1367805365 : Blo 1152637 1367805365 := bstep (se 5 (by rfl) ⟨64115876, by rfl⟩ : syracuseStep 1367805365 = 128231753) B128231753
theorem B44404847 : Blo 1152637 44404847 := bstep (se 1 (by rfl) ⟨33303635, by rfl⟩ : syracuseStep 44404847 = 66607271) B66607271
theorem B5544379 : Blo 1152637 5544379 := bstep (se 1 (by rfl) ⟨4158284, by rfl⟩ : syracuseStep 5544379 = 8316569) B8316569
theorem B1154495 : Blo 1152637 1154495 := bstep (se 1 (by rfl) ⟨865871, by rfl⟩ : syracuseStep 1154495 = 1731743) B1731743
theorem B2596319 : Blo 1152637 2596319 := bstep (se 1 (by rfl) ⟨1947239, by rfl⟩ : syracuseStep 2596319 = 3894479) B3894479
theorem B1154815 : Blo 1152637 1154815 := bstep (se 1 (by rfl) ⟨866111, by rfl⟩ : syracuseStep 1154815 = 1732223) B1732223
theorem B5841071 : Blo 1152637 5841071 := bstep (se 1 (by rfl) ⟨4380803, by rfl⟩ : syracuseStep 5841071 = 8761607) B8761607
theorem B1155487 : Blo 1152637 1155487 := bstep (se 1 (by rfl) ⟨866615, by rfl⟩ : syracuseStep 1155487 = 1733231) B1733231
theorem B2601179 : Blo 1152637 2601179 := bstep (se 1 (by rfl) ⟨1950884, by rfl⟩ : syracuseStep 2601179 = 3901769) B3901769
theorem B15775079 : Blo 1152637 15775079 := bstep (se 1 (by rfl) ⟨11831309, by rfl⟩ : syracuseStep 15775079 = 23662619) B23662619
theorem B28096253 : Blo 1152637 28096253 := bstep (se 3 (by rfl) ⟨5268047, by rfl⟩ : syracuseStep 28096253 = 10536095) B10536095
theorem B75905029 : Blo 1152637 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B5847227 : Blo 1152637 5847227 := bstep (se 1 (by rfl) ⟨4385420, by rfl⟩ : syracuseStep 5847227 = 8770841) B8770841
theorem B9355463 : Blo 1152637 9355463 := bstep (se 1 (by rfl) ⟨7016597, by rfl⟩ : syracuseStep 9355463 = 14033195) B14033195
theorem B2770075 : Blo 1152637 2770075 := bstep (se 1 (by rfl) ⟨2077556, by rfl⟩ : syracuseStep 2770075 = 4155113) B4155113
theorem B7031411 : Blo 1152637 7031411 := bstep (se 1 (by rfl) ⟨5273558, by rfl⟩ : syracuseStep 7031411 = 10547117) B10547117
theorem B1298911 : Blo 1152637 1298911 := bstep (se 1 (by rfl) ⟨974183, by rfl⟩ : syracuseStep 1298911 = 1948367) B1948367
theorem B31613327 : Blo 1152637 31613327 := bstep (se 1 (by rfl) ⟨23709995, by rfl⟩ : syracuseStep 31613327 = 47419991) B47419991
theorem B11235839 : Blo 1152637 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B7405627 : Blo 1152637 7405627 := bstep (se 1 (by rfl) ⟨5554220, by rfl⟩ : syracuseStep 7405627 = 11108441) B11108441
theorem B4687607 : Blo 1152637 4687607 := bstep (se 1 (by rfl) ⟨3515705, by rfl⟩ : syracuseStep 4687607 = 7031411) B7031411
theorem B911870243 : Blo 1152637 911870243 := bstep (se 1 (by rfl) ⟨683902682, by rfl⟩ : syracuseStep 911870243 = 1367805365) B1367805365
theorem B21075551 : Blo 1152637 21075551 := bstep (se 1 (by rfl) ⟨15806663, by rfl⟩ : syracuseStep 21075551 = 31613327) B31613327
theorem B6236975 : Blo 1152637 6236975 := bstep (se 1 (by rfl) ⟨4677731, by rfl⟩ : syracuseStep 6236975 = 9355463) B9355463
theorem B42118703 : Blo 1152637 42118703 := bstep (se 1 (by rfl) ⟨31589027, by rfl⟩ : syracuseStep 42118703 = 63178055) B63178055
theorem B29962237 : Blo 1152637 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B9875945 : Blo 1152637 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B29603231 : Blo 1152637 29603231 := bstep (se 1 (by rfl) ⟨22202423, by rfl⟩ : syracuseStep 29603231 = 44404847) B44404847
theorem B101206705 : Blo 1152637 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B7392505 : Blo 1152637 7392505 := bstep (se 2 (by rfl) ⟨2772189, by rfl⟩ : syracuseStep 7392505 = 5544379) B5544379
theorem B18730835 : Blo 1152637 18730835 := bstep (se 1 (by rfl) ⟨14048126, by rfl⟩ : syracuseStep 18730835 = 28096253) B28096253
theorem B3693433 : Blo 1152637 3693433 := bstep (se 2 (by rfl) ⟨1385037, by rfl⟩ : syracuseStep 3693433 = 2770075) B2770075
theorem B42066877 : Blo 1152637 42066877 := bstep (se 3 (by rfl) ⟨7887539, by rfl⟩ : syracuseStep 42066877 = 15775079) B15775079
theorem B1730879 : Blo 1152637 1730879 := bstep (se 1 (by rfl) ⟨1298159, by rfl⟩ : syracuseStep 1730879 = 2596319) B2596319
theorem B3894047 : Blo 1152637 3894047 := bstep (se 1 (by rfl) ⟨2920535, by rfl⟩ : syracuseStep 3894047 = 5841071) B5841071
theorem B1731881 : Blo 1152637 1731881 := bstep (se 2 (by rfl) ⟨649455, by rfl⟩ : syracuseStep 1731881 = 1298911) B1298911
theorem B1734119 : Blo 1152637 1734119 := bstep (se 1 (by rfl) ⟨1300589, by rfl⟩ : syracuseStep 1734119 = 2601179) B2601179
theorem B3898151 : Blo 1152637 3898151 := bstep (se 1 (by rfl) ⟨2923613, by rfl⟩ : syracuseStep 3898151 = 5847227) B5847227
theorem B607913495 : Blo 1152637 607913495 := bstep (se 1 (by rfl) ⟨455935121, by rfl⟩ : syracuseStep 607913495 = 911870243) B911870243
theorem B12487223 : Blo 1152637 12487223 := bstep (se 1 (by rfl) ⟨9365417, by rfl⟩ : syracuseStep 12487223 = 18730835) B18730835
theorem B134942273 : Blo 1152637 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B39949649 : Blo 1152637 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B1153919 : Blo 1152637 1153919 := bstep (se 1 (by rfl) ⟨865439, by rfl⟩ : syracuseStep 1153919 = 1730879) B1730879
theorem B2596031 : Blo 1152637 2596031 := bstep (se 1 (by rfl) ⟨1947023, by rfl⟩ : syracuseStep 2596031 = 3894047) B3894047
theorem B1154587 : Blo 1152637 1154587 := bstep (se 1 (by rfl) ⟨865940, by rfl⟩ : syracuseStep 1154587 = 1731881) B1731881
theorem B19735487 : Blo 1152637 19735487 := bstep (se 1 (by rfl) ⟨14801615, by rfl⟩ : syracuseStep 19735487 = 29603231) B29603231
theorem B1156079 : Blo 1152637 1156079 := bstep (se 1 (by rfl) ⟨867059, by rfl⟩ : syracuseStep 1156079 = 1734119) B1734119
theorem B4924577 : Blo 1152637 4924577 := bstep (se 2 (by rfl) ⟨1846716, by rfl⟩ : syracuseStep 4924577 = 3693433) B3693433
theorem B2598767 : Blo 1152637 2598767 := bstep (se 1 (by rfl) ⟨1949075, by rfl⟩ : syracuseStep 2598767 = 3898151) B3898151
theorem B9874169 : Blo 1152637 9874169 := bstep (se 2 (by rfl) ⟨3702813, by rfl⟩ : syracuseStep 9874169 = 7405627) B7405627
theorem B3125071 : Blo 1152637 3125071 := bstep (se 1 (by rfl) ⟨2343803, by rfl⟩ : syracuseStep 3125071 = 4687607) B4687607
theorem B56089169 : Blo 1152637 56089169 := bstep (se 2 (by rfl) ⟨21033438, by rfl⟩ : syracuseStep 56089169 = 42066877) B42066877
theorem B14050367 : Blo 1152637 14050367 := bstep (se 1 (by rfl) ⟨10537775, by rfl⟩ : syracuseStep 14050367 = 21075551) B21075551
theorem B9856673 : Blo 1152637 9856673 := bstep (se 2 (by rfl) ⟨3696252, by rfl⟩ : syracuseStep 9856673 = 7392505) B7392505
theorem B4157983 : Blo 1152637 4157983 := bstep (se 1 (by rfl) ⟨3118487, by rfl⟩ : syracuseStep 4157983 = 6236975) B6236975
theorem B28079135 : Blo 1152637 28079135 := bstep (se 1 (by rfl) ⟨21059351, by rfl⟩ : syracuseStep 28079135 = 42118703) B42118703
theorem B6583963 : Blo 1152637 6583963 := bstep (se 1 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 6583963 = 9875945) B9875945
theorem B405275663 : Blo 1152637 405275663 := bstep (se 1 (by rfl) ⟨303956747, by rfl⟩ : syracuseStep 405275663 = 607913495) B607913495
theorem B37392779 : Blo 1152637 37392779 := bstep (se 1 (by rfl) ⟨28044584, by rfl⟩ : syracuseStep 37392779 = 56089169) B56089169
theorem B5543977 : Blo 1152637 5543977 := bstep (se 2 (by rfl) ⟨2078991, by rfl⟩ : syracuseStep 5543977 = 4157983) B4157983
theorem B33299261 : Blo 1152637 33299261 := bstep (se 3 (by rfl) ⟨6243611, by rfl⟩ : syracuseStep 33299261 = 12487223) B12487223
theorem B18719423 : Blo 1152637 18719423 := bstep (se 1 (by rfl) ⟨14039567, by rfl⟩ : syracuseStep 18719423 = 28079135) B28079135
theorem B89961515 : Blo 1152637 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B13156991 : Blo 1152637 13156991 := bstep (se 1 (by rfl) ⟨9867743, by rfl⟩ : syracuseStep 13156991 = 19735487) B19735487
theorem B6571115 : Blo 1152637 6571115 := bstep (se 1 (by rfl) ⟨4928336, by rfl⟩ : syracuseStep 6571115 = 9856673) B9856673
theorem B16667045 : Blo 1152637 16667045 := bstep (se 4 (by rfl) ⟨1562535, by rfl⟩ : syracuseStep 16667045 = 3125071) B3125071
theorem B13132205 : Blo 1152637 13132205 := bstep (se 3 (by rfl) ⟨2462288, by rfl⟩ : syracuseStep 13132205 = 4924577) B4924577
theorem B26633099 : Blo 1152637 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B1730687 : Blo 1152637 1730687 := bstep (se 1 (by rfl) ⟨1298015, by rfl⟩ : syracuseStep 1730687 = 2596031) B2596031
theorem B9366911 : Blo 1152637 9366911 := bstep (se 1 (by rfl) ⟨7025183, by rfl⟩ : syracuseStep 9366911 = 14050367) B14050367
theorem B1732511 : Blo 1152637 1732511 := bstep (se 1 (by rfl) ⟨1299383, by rfl⟩ : syracuseStep 1732511 = 2598767) B2598767
theorem B6582779 : Blo 1152637 6582779 := bstep (se 1 (by rfl) ⟨4937084, by rfl⟩ : syracuseStep 6582779 = 9874169) B9874169
theorem B8778617 : Blo 1152637 8778617 := bstep (se 2 (by rfl) ⟨3291981, by rfl⟩ : syracuseStep 8778617 = 6583963) B6583963
theorem B11111363 : Blo 1152637 11111363 := bstep (se 1 (by rfl) ⟨8333522, by rfl⟩ : syracuseStep 11111363 = 16667045) B16667045
theorem B8754803 : Blo 1152637 8754803 := bstep (se 1 (by rfl) ⟨6566102, by rfl⟩ : syracuseStep 8754803 = 13132205) B13132205
theorem B1153791 : Blo 1152637 1153791 := bstep (se 1 (by rfl) ⟨865343, by rfl⟩ : syracuseStep 1153791 = 1730687) B1730687
theorem B1155007 : Blo 1152637 1155007 := bstep (se 1 (by rfl) ⟨866255, by rfl⟩ : syracuseStep 1155007 = 1732511) B1732511
theorem B59974343 : Blo 1152637 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B270183775 : Blo 1152637 270183775 := bstep (se 1 (by rfl) ⟨202637831, by rfl⟩ : syracuseStep 270183775 = 405275663) B405275663
theorem B22199507 : Blo 1152637 22199507 := bstep (se 1 (by rfl) ⟨16649630, by rfl⟩ : syracuseStep 22199507 = 33299261) B33299261
theorem B6244607 : Blo 1152637 6244607 := bstep (se 1 (by rfl) ⟨4683455, by rfl⟩ : syracuseStep 6244607 = 9366911) B9366911
theorem B7391969 : Blo 1152637 7391969 := bstep (se 2 (by rfl) ⟨2771988, by rfl⟩ : syracuseStep 7391969 = 5543977) B5543977
theorem B5852411 : Blo 1152637 5852411 := bstep (se 1 (by rfl) ⟨4389308, by rfl⟩ : syracuseStep 5852411 = 8778617) B8778617
theorem B8771327 : Blo 1152637 8771327 := bstep (se 1 (by rfl) ⟨6578495, by rfl⟩ : syracuseStep 8771327 = 13156991) B13156991
theorem B4380743 : Blo 1152637 4380743 := bstep (se 1 (by rfl) ⟨3285557, by rfl⟩ : syracuseStep 4380743 = 6571115) B6571115
theorem B24928519 : Blo 1152637 24928519 := bstep (se 1 (by rfl) ⟨18696389, by rfl⟩ : syracuseStep 24928519 = 37392779) B37392779
theorem B12479615 : Blo 1152637 12479615 := bstep (se 1 (by rfl) ⟨9359711, by rfl⟩ : syracuseStep 12479615 = 18719423) B18719423
theorem B17755399 : Blo 1152637 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B4388519 : Blo 1152637 4388519 := bstep (se 1 (by rfl) ⟨3291389, by rfl⟩ : syracuseStep 4388519 = 6582779) B6582779
theorem B4163071 : Blo 1152637 4163071 := bstep (se 1 (by rfl) ⟨3122303, by rfl⟩ : syracuseStep 4163071 = 6244607) B6244607
theorem B7407575 : Blo 1152637 7407575 := bstep (se 1 (by rfl) ⟨5555681, by rfl⟩ : syracuseStep 7407575 = 11111363) B11111363
theorem B3901607 : Blo 1152637 3901607 := bstep (se 1 (by rfl) ⟨2926205, by rfl⟩ : syracuseStep 3901607 = 5852411) B5852411
theorem B5836535 : Blo 1152637 5836535 := bstep (se 1 (by rfl) ⟨4377401, by rfl⟩ : syracuseStep 5836535 = 8754803) B8754803
theorem B2920495 : Blo 1152637 2920495 := bstep (se 1 (by rfl) ⟨2190371, by rfl⟩ : syracuseStep 2920495 = 4380743) B4380743
theorem B39982895 : Blo 1152637 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B2925679 : Blo 1152637 2925679 := bstep (se 1 (by rfl) ⟨2194259, by rfl⟩ : syracuseStep 2925679 = 4388519) B4388519
theorem B33238025 : Blo 1152637 33238025 := bstep (se 2 (by rfl) ⟨12464259, by rfl⟩ : syracuseStep 33238025 = 24928519) B24928519
theorem B4927979 : Blo 1152637 4927979 := bstep (se 1 (by rfl) ⟨3695984, by rfl⟩ : syracuseStep 4927979 = 7391969) B7391969
theorem B5847551 : Blo 1152637 5847551 := bstep (se 1 (by rfl) ⟨4385663, by rfl⟩ : syracuseStep 5847551 = 8771327) B8771327
theorem B23673865 : Blo 1152637 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B14799671 : Blo 1152637 14799671 := bstep (se 1 (by rfl) ⟨11099753, by rfl⟩ : syracuseStep 14799671 = 22199507) B22199507
theorem B360245033 : Blo 1152637 360245033 := bstep (se 2 (by rfl) ⟨135091887, by rfl⟩ : syracuseStep 360245033 = 270183775) B270183775
theorem B8319743 : Blo 1152637 8319743 := bstep (se 1 (by rfl) ⟨6239807, by rfl⟩ : syracuseStep 8319743 = 12479615) B12479615
theorem B3900905 : Blo 1152637 3900905 := bstep (se 2 (by rfl) ⟨1462839, by rfl⟩ : syracuseStep 3900905 = 2925679) B2925679
theorem B9866447 : Blo 1152637 9866447 := bstep (se 1 (by rfl) ⟨7399835, by rfl⟩ : syracuseStep 9866447 = 14799671) B14799671
theorem B240163355 : Blo 1152637 240163355 := bstep (se 1 (by rfl) ⟨180122516, by rfl⟩ : syracuseStep 240163355 = 360245033) B360245033
theorem B22158683 : Blo 1152637 22158683 := bstep (se 1 (by rfl) ⟨16619012, by rfl⟩ : syracuseStep 22158683 = 33238025) B33238025
theorem B3285319 : Blo 1152637 3285319 := bstep (se 1 (by rfl) ⟨2463989, by rfl⟩ : syracuseStep 3285319 = 4927979) B4927979
theorem B5546495 : Blo 1152637 5546495 := bstep (se 1 (by rfl) ⟨4159871, by rfl⟩ : syracuseStep 5546495 = 8319743) B8319743
theorem B31565153 : Blo 1152637 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B2601071 : Blo 1152637 2601071 := bstep (se 1 (by rfl) ⟨1950803, by rfl⟩ : syracuseStep 2601071 = 3901607) B3901607
theorem B5550761 : Blo 1152637 5550761 := bstep (se 2 (by rfl) ⟨2081535, by rfl⟩ : syracuseStep 5550761 = 4163071) B4163071
theorem B26655263 : Blo 1152637 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B4938383 : Blo 1152637 4938383 := bstep (se 1 (by rfl) ⟨3703787, by rfl⟩ : syracuseStep 4938383 = 7407575) B7407575
theorem B3891023 : Blo 1152637 3891023 := bstep (se 1 (by rfl) ⟨2918267, by rfl⟩ : syracuseStep 3891023 = 5836535) B5836535
theorem B3893993 : Blo 1152637 3893993 := bstep (se 2 (by rfl) ⟨1460247, by rfl⟩ : syracuseStep 3893993 = 2920495) B2920495
theorem B3898367 : Blo 1152637 3898367 := bstep (se 1 (by rfl) ⟨2923775, by rfl⟩ : syracuseStep 3898367 = 5847551) B5847551
theorem B160108903 : Blo 1152637 160108903 := bstep (se 1 (by rfl) ⟨120081677, by rfl⟩ : syracuseStep 160108903 = 240163355) B240163355
theorem B2594015 : Blo 1152637 2594015 := bstep (se 1 (by rfl) ⟨1945511, by rfl⟩ : syracuseStep 2594015 = 3891023) B3891023
theorem B21043435 : Blo 1152637 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B2595995 : Blo 1152637 2595995 := bstep (se 1 (by rfl) ⟨1946996, by rfl⟩ : syracuseStep 2595995 = 3893993) B3893993
theorem B17770175 : Blo 1152637 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B2598911 : Blo 1152637 2598911 := bstep (se 1 (by rfl) ⟨1949183, by rfl⟩ : syracuseStep 2598911 = 3898367) B3898367
theorem B2600603 : Blo 1152637 2600603 := bstep (se 1 (by rfl) ⟨1950452, by rfl⟩ : syracuseStep 2600603 = 3900905) B3900905
theorem B3292255 : Blo 1152637 3292255 := bstep (se 1 (by rfl) ⟨2469191, by rfl⟩ : syracuseStep 3292255 = 4938383) B4938383
theorem B4380425 : Blo 1152637 4380425 := bstep (se 2 (by rfl) ⟨1642659, by rfl⟩ : syracuseStep 4380425 = 3285319) B3285319
theorem B6577631 : Blo 1152637 6577631 := bstep (se 1 (by rfl) ⟨4933223, by rfl⟩ : syracuseStep 6577631 = 9866447) B9866447
theorem B14772455 : Blo 1152637 14772455 := bstep (se 1 (by rfl) ⟨11079341, by rfl⟩ : syracuseStep 14772455 = 22158683) B22158683
theorem B3697663 : Blo 1152637 3697663 := bstep (se 1 (by rfl) ⟨2773247, by rfl⟩ : syracuseStep 3697663 = 5546495) B5546495
theorem B1734047 : Blo 1152637 1734047 := bstep (se 1 (by rfl) ⟨1300535, by rfl⟩ : syracuseStep 1734047 = 2601071) B2601071
theorem B3700507 : Blo 1152637 3700507 := bstep (se 1 (by rfl) ⟨2775380, by rfl⟩ : syracuseStep 3700507 = 5550761) B5550761
theorem B2920283 : Blo 1152637 2920283 := bstep (se 1 (by rfl) ⟨2190212, by rfl⟩ : syracuseStep 2920283 = 4380425) B4380425
theorem B28057913 : Blo 1152637 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B1156031 : Blo 1152637 1156031 := bstep (se 1 (by rfl) ⟨867023, by rfl⟩ : syracuseStep 1156031 = 1734047) B1734047
theorem B4930217 : Blo 1152637 4930217 := bstep (se 2 (by rfl) ⟨1848831, by rfl⟩ : syracuseStep 4930217 = 3697663) B3697663
theorem B11846783 : Blo 1152637 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B9848303 : Blo 1152637 9848303 := bstep (se 1 (by rfl) ⟨7386227, by rfl⟩ : syracuseStep 9848303 = 14772455) B14772455
theorem B4934009 : Blo 1152637 4934009 := bstep (se 2 (by rfl) ⟨1850253, by rfl⟩ : syracuseStep 4934009 = 3700507) B3700507
theorem B1729343 : Blo 1152637 1729343 := bstep (se 1 (by rfl) ⟨1297007, by rfl⟩ : syracuseStep 1729343 = 2594015) B2594015
theorem B1730663 : Blo 1152637 1730663 := bstep (se 1 (by rfl) ⟨1297997, by rfl⟩ : syracuseStep 1730663 = 2595995) B2595995
theorem B4385087 : Blo 1152637 4385087 := bstep (se 1 (by rfl) ⟨3288815, by rfl⟩ : syracuseStep 4385087 = 6577631) B6577631
theorem B213478537 : Blo 1152637 213478537 := bstep (se 2 (by rfl) ⟨80054451, by rfl⟩ : syracuseStep 213478537 = 160108903) B160108903
theorem B1732607 : Blo 1152637 1732607 := bstep (se 1 (by rfl) ⟨1299455, by rfl⟩ : syracuseStep 1732607 = 2598911) B2598911
theorem B1733735 : Blo 1152637 1733735 := bstep (se 1 (by rfl) ⟨1300301, by rfl⟩ : syracuseStep 1733735 = 2600603) B2600603
theorem B4389673 : Blo 1152637 4389673 := bstep (se 2 (by rfl) ⟨1646127, by rfl⟩ : syracuseStep 4389673 = 3292255) B3292255
theorem B31591421 : Blo 1152637 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B1152895 : Blo 1152637 1152895 := bstep (se 1 (by rfl) ⟨864671, by rfl⟩ : syracuseStep 1152895 = 1729343) B1729343
theorem B1153775 : Blo 1152637 1153775 := bstep (se 1 (by rfl) ⟨865331, by rfl⟩ : syracuseStep 1153775 = 1730663) B1730663
theorem B2923391 : Blo 1152637 2923391 := bstep (se 1 (by rfl) ⟨2192543, by rfl⟩ : syracuseStep 2923391 = 4385087) B4385087
theorem B1155071 : Blo 1152637 1155071 := bstep (se 1 (by rfl) ⟨866303, by rfl⟩ : syracuseStep 1155071 = 1732607) B1732607
theorem B1155823 : Blo 1152637 1155823 := bstep (se 1 (by rfl) ⟨866867, by rfl⟩ : syracuseStep 1155823 = 1733735) B1733735
theorem B3286811 : Blo 1152637 3286811 := bstep (se 1 (by rfl) ⟨2465108, by rfl⟩ : syracuseStep 3286811 = 4930217) B4930217
theorem B6565535 : Blo 1152637 6565535 := bstep (se 1 (by rfl) ⟨4924151, by rfl⟩ : syracuseStep 6565535 = 9848303) B9848303
theorem B3289339 : Blo 1152637 3289339 := bstep (se 1 (by rfl) ⟨2467004, by rfl⟩ : syracuseStep 3289339 = 4934009) B4934009
theorem B1946855 : Blo 1152637 1946855 := bstep (se 1 (by rfl) ⟨1460141, by rfl⟩ : syracuseStep 1946855 = 2920283) B2920283
theorem B284638049 : Blo 1152637 284638049 := bstep (se 2 (by rfl) ⟨106739268, by rfl⟩ : syracuseStep 284638049 = 213478537) B213478537
theorem B5852897 : Blo 1152637 5852897 := bstep (se 2 (by rfl) ⟨2194836, by rfl⟩ : syracuseStep 5852897 = 4389673) B4389673
theorem B18705275 : Blo 1152637 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B3901931 : Blo 1152637 3901931 := bstep (se 1 (by rfl) ⟨2926448, by rfl⟩ : syracuseStep 3901931 = 5852897) B5852897
theorem B1948927 : Blo 1152637 1948927 := bstep (se 1 (by rfl) ⟨1461695, by rfl⟩ : syracuseStep 1948927 = 2923391) B2923391
theorem B12470183 : Blo 1152637 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B4377023 : Blo 1152637 4377023 := bstep (se 1 (by rfl) ⟨3282767, by rfl⟩ : syracuseStep 4377023 = 6565535) B6565535
theorem B1297903 : Blo 1152637 1297903 := bstep (se 1 (by rfl) ⟨973427, by rfl⟩ : syracuseStep 1297903 = 1946855) B1946855
theorem B21060947 : Blo 1152637 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B4385785 : Blo 1152637 4385785 := bstep (se 2 (by rfl) ⟨1644669, by rfl⟩ : syracuseStep 4385785 = 3289339) B3289339
theorem B2191207 : Blo 1152637 2191207 := bstep (se 1 (by rfl) ⟨1643405, by rfl⟩ : syracuseStep 2191207 = 3286811) B3286811
theorem B189758699 : Blo 1152637 189758699 := bstep (se 1 (by rfl) ⟨142319024, by rfl⟩ : syracuseStep 189758699 = 284638049) B284638049
theorem B2918015 : Blo 1152637 2918015 := bstep (se 1 (by rfl) ⟨2188511, by rfl⟩ : syracuseStep 2918015 = 4377023) B4377023
theorem B2921609 : Blo 1152637 2921609 := bstep (se 2 (by rfl) ⟨1095603, by rfl⟩ : syracuseStep 2921609 = 2191207) B2191207
theorem B2598569 : Blo 1152637 2598569 := bstep (se 2 (by rfl) ⟨974463, by rfl⟩ : syracuseStep 2598569 = 1948927) B1948927
theorem B2601287 : Blo 1152637 2601287 := bstep (se 1 (by rfl) ⟨1950965, by rfl⟩ : syracuseStep 2601287 = 3901931) B3901931
theorem B5847713 : Blo 1152637 5847713 := bstep (se 2 (by rfl) ⟨2192892, by rfl⟩ : syracuseStep 5847713 = 4385785) B4385785
theorem B14040631 : Blo 1152637 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B126505799 : Blo 1152637 126505799 := bstep (se 1 (by rfl) ⟨94879349, by rfl⟩ : syracuseStep 126505799 = 189758699) B189758699
theorem B8313455 : Blo 1152637 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B1730537 : Blo 1152637 1730537 := bstep (se 2 (by rfl) ⟨648951, by rfl⟩ : syracuseStep 1730537 = 1297903) B1297903
theorem B5542303 : Blo 1152637 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B1153691 : Blo 1152637 1153691 := bstep (se 1 (by rfl) ⟨865268, by rfl⟩ : syracuseStep 1153691 = 1730537) B1730537
theorem B18720841 : Blo 1152637 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B1945343 : Blo 1152637 1945343 := bstep (se 1 (by rfl) ⟨1459007, by rfl⟩ : syracuseStep 1945343 = 2918015) B2918015
theorem B1947739 : Blo 1152637 1947739 := bstep (se 1 (by rfl) ⟨1460804, by rfl⟩ : syracuseStep 1947739 = 2921609) B2921609
theorem B84337199 : Blo 1152637 84337199 := bstep (se 1 (by rfl) ⟨63252899, by rfl⟩ : syracuseStep 84337199 = 126505799) B126505799
theorem B1732379 : Blo 1152637 1732379 := bstep (se 1 (by rfl) ⟨1299284, by rfl⟩ : syracuseStep 1732379 = 2598569) B2598569
theorem B1734191 : Blo 1152637 1734191 := bstep (se 1 (by rfl) ⟨1300643, by rfl⟩ : syracuseStep 1734191 = 2601287) B2601287
theorem B3898475 : Blo 1152637 3898475 := bstep (se 1 (by rfl) ⟨2923856, by rfl⟩ : syracuseStep 3898475 = 5847713) B5847713
theorem B1154919 : Blo 1152637 1154919 := bstep (se 1 (by rfl) ⟨866189, by rfl⟩ : syracuseStep 1154919 = 1732379) B1732379
theorem B2596985 : Blo 1152637 2596985 := bstep (se 2 (by rfl) ⟨973869, by rfl⟩ : syracuseStep 2596985 = 1947739) B1947739
theorem B1156127 : Blo 1152637 1156127 := bstep (se 1 (by rfl) ⟨867095, by rfl⟩ : syracuseStep 1156127 = 1734191) B1734191
theorem B2598983 : Blo 1152637 2598983 := bstep (se 1 (by rfl) ⟨1949237, by rfl⟩ : syracuseStep 2598983 = 3898475) B3898475
theorem B7389737 : Blo 1152637 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B1296895 : Blo 1152637 1296895 := bstep (se 1 (by rfl) ⟨972671, by rfl⟩ : syracuseStep 1296895 = 1945343) B1945343
theorem B24961121 : Blo 1152637 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B56224799 : Blo 1152637 56224799 := bstep (se 1 (by rfl) ⟨42168599, by rfl⟩ : syracuseStep 56224799 = 84337199) B84337199
theorem B4926491 : Blo 1152637 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B1729193 : Blo 1152637 1729193 := bstep (se 2 (by rfl) ⟨648447, by rfl⟩ : syracuseStep 1729193 = 1296895) B1296895
theorem B16640747 : Blo 1152637 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B1731323 : Blo 1152637 1731323 := bstep (se 1 (by rfl) ⟨1298492, by rfl⟩ : syracuseStep 1731323 = 2596985) B2596985
theorem B1732655 : Blo 1152637 1732655 := bstep (se 1 (by rfl) ⟨1299491, by rfl⟩ : syracuseStep 1732655 = 2598983) B2598983
theorem B37483199 : Blo 1152637 37483199 := bstep (se 1 (by rfl) ⟨28112399, by rfl⟩ : syracuseStep 37483199 = 56224799) B56224799
theorem B1152795 : Blo 1152637 1152795 := bstep (se 1 (by rfl) ⟨864596, by rfl⟩ : syracuseStep 1152795 = 1729193) B1729193
theorem B1154215 : Blo 1152637 1154215 := bstep (se 1 (by rfl) ⟨865661, by rfl⟩ : syracuseStep 1154215 = 1731323) B1731323
theorem B3284327 : Blo 1152637 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B1155103 : Blo 1152637 1155103 := bstep (se 1 (by rfl) ⟨866327, by rfl⟩ : syracuseStep 1155103 = 1732655) B1732655
theorem B11093831 : Blo 1152637 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B24988799 : Blo 1152637 24988799 := bstep (se 1 (by rfl) ⟨18741599, by rfl⟩ : syracuseStep 24988799 = 37483199) B37483199
theorem B8758205 : Blo 1152637 8758205 := bstep (se 3 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 8758205 = 3284327) B3284327
theorem B16659199 : Blo 1152637 16659199 := bstep (se 1 (by rfl) ⟨12494399, by rfl⟩ : syracuseStep 16659199 = 24988799) B24988799
theorem B7395887 : Blo 1152637 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B5838803 : Blo 1152637 5838803 := bstep (se 1 (by rfl) ⟨4379102, by rfl⟩ : syracuseStep 5838803 = 8758205) B8758205
theorem B22212265 : Blo 1152637 22212265 := bstep (se 2 (by rfl) ⟨8329599, by rfl⟩ : syracuseStep 22212265 = 16659199) B16659199
theorem B19722365 : Blo 1152637 19722365 := bstep (se 3 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 19722365 = 7395887) B7395887
theorem B13148243 : Blo 1152637 13148243 := bstep (se 1 (by rfl) ⟨9861182, by rfl⟩ : syracuseStep 13148243 = 19722365) B19722365
theorem B3892535 : Blo 1152637 3892535 := bstep (se 1 (by rfl) ⟨2919401, by rfl⟩ : syracuseStep 3892535 = 5838803) B5838803
theorem B29616353 : Blo 1152637 29616353 := bstep (se 2 (by rfl) ⟨11106132, by rfl⟩ : syracuseStep 29616353 = 22212265) B22212265
theorem B2595023 : Blo 1152637 2595023 := bstep (se 1 (by rfl) ⟨1946267, by rfl⟩ : syracuseStep 2595023 = 3892535) B3892535
theorem B8765495 : Blo 1152637 8765495 := bstep (se 1 (by rfl) ⟨6574121, by rfl⟩ : syracuseStep 8765495 = 13148243) B13148243
theorem B19744235 : Blo 1152637 19744235 := bstep (se 1 (by rfl) ⟨14808176, by rfl⟩ : syracuseStep 19744235 = 29616353) B29616353
theorem B5843663 : Blo 1152637 5843663 := bstep (se 1 (by rfl) ⟨4382747, by rfl⟩ : syracuseStep 5843663 = 8765495) B8765495
theorem B13162823 : Blo 1152637 13162823 := bstep (se 1 (by rfl) ⟨9872117, by rfl⟩ : syracuseStep 13162823 = 19744235) B19744235
theorem B1730015 : Blo 1152637 1730015 := bstep (se 1 (by rfl) ⟨1297511, by rfl⟩ : syracuseStep 1730015 = 2595023) B2595023
theorem B1153343 : Blo 1152637 1153343 := bstep (se 1 (by rfl) ⟨865007, by rfl⟩ : syracuseStep 1153343 = 1730015) B1730015
theorem B8775215 : Blo 1152637 8775215 := bstep (se 1 (by rfl) ⟨6581411, by rfl⟩ : syracuseStep 8775215 = 13162823) B13162823
theorem B3895775 : Blo 1152637 3895775 := bstep (se 1 (by rfl) ⟨2921831, by rfl⟩ : syracuseStep 3895775 = 5843663) B5843663
theorem B2597183 : Blo 1152637 2597183 := bstep (se 1 (by rfl) ⟨1947887, by rfl⟩ : syracuseStep 2597183 = 3895775) B3895775
theorem B5850143 : Blo 1152637 5850143 := bstep (se 1 (by rfl) ⟨4387607, by rfl⟩ : syracuseStep 5850143 = 8775215) B8775215
theorem B3900095 : Blo 1152637 3900095 := bstep (se 1 (by rfl) ⟨2925071, by rfl⟩ : syracuseStep 3900095 = 5850143) B5850143
theorem B1731455 : Blo 1152637 1731455 := bstep (se 1 (by rfl) ⟨1298591, by rfl⟩ : syracuseStep 1731455 = 2597183) B2597183
theorem B1154303 : Blo 1152637 1154303 := bstep (se 1 (by rfl) ⟨865727, by rfl⟩ : syracuseStep 1154303 = 1731455) B1731455
theorem B2600063 : Blo 1152637 2600063 := bstep (se 1 (by rfl) ⟨1950047, by rfl⟩ : syracuseStep 2600063 = 3900095) B3900095
theorem B1733375 : Blo 1152637 1733375 := bstep (se 1 (by rfl) ⟨1300031, by rfl⟩ : syracuseStep 1733375 = 2600063) B2600063
theorem B1155583 : Blo 1152637 1155583 := bstep (se 1 (by rfl) ⟨866687, by rfl⟩ : syracuseStep 1155583 = 1733375) B1733375

theorem C0 (j : ℕ) (h1 : 288159 ≤ j) (h2 : j ≤ 288858) : Blo 1152637 (4 * j + 3) := by
  interval_cases j
  · exact B1152639
  · exact B1152643
  · exact B1152647
  · exact B1152651
  · exact B1152655
  · exact B1152659
  · exact B1152663
  · exact B1152667
  · exact B1152671
  · exact B1152675
  · exact B1152679
  · exact B1152683
  · exact B1152687
  · exact B1152691
  · exact B1152695
  · exact B1152699
  · exact B1152703
  · exact B1152707
  · exact B1152711
  · exact B1152715
  · exact B1152719
  · exact B1152723
  · exact B1152727
  · exact B1152731
  · exact B1152735
  · exact B1152739
  · exact B1152743
  · exact B1152747
  · exact B1152751
  · exact B1152755
  · exact B1152759
  · exact B1152763
  · exact B1152767
  · exact B1152771
  · exact B1152775
  · exact B1152779
  · exact B1152783
  · exact B1152787
  · exact B1152791
  · exact B1152795
  · exact B1152799
  · exact B1152803
  · exact B1152807
  · exact B1152811
  · exact B1152815
  · exact B1152819
  · exact B1152823
  · exact B1152827
  · exact B1152831
  · exact B1152835
  · exact B1152839
  · exact B1152843
  · exact B1152847
  · exact B1152851
  · exact B1152855
  · exact B1152859
  · exact B1152863
  · exact B1152867
  · exact B1152871
  · exact B1152875
  · exact B1152879
  · exact B1152883
  · exact B1152887
  · exact B1152891
  · exact B1152895
  · exact B1152899
  · exact B1152903
  · exact B1152907
  · exact B1152911
  · exact B1152915
  · exact B1152919
  · exact B1152923
  · exact B1152927
  · exact B1152931
  · exact B1152935
  · exact B1152939
  · exact B1152943
  · exact B1152947
  · exact B1152951
  · exact B1152955
  · exact B1152959
  · exact B1152963
  · exact B1152967
  · exact B1152971
  · exact B1152975
  · exact B1152979
  · exact B1152983
  · exact B1152987
  · exact B1152991
  · exact B1152995
  · exact B1152999
  · exact B1153003
  · exact B1153007
  · exact B1153011
  · exact B1153015
  · exact B1153019
  · exact B1153023
  · exact B1153027
  · exact B1153031
  · exact B1153035
  · exact B1153039
  · exact B1153043
  · exact B1153047
  · exact B1153051
  · exact B1153055
  · exact B1153059
  · exact B1153063
  · exact B1153067
  · exact B1153071
  · exact B1153075
  · exact B1153079
  · exact B1153083
  · exact B1153087
  · exact B1153091
  · exact B1153095
  · exact B1153099
  · exact B1153103
  · exact B1153107
  · exact B1153111
  · exact B1153115
  · exact B1153119
  · exact B1153123
  · exact B1153127
  · exact B1153131
  · exact B1153135
  · exact B1153139
  · exact B1153143
  · exact B1153147
  · exact B1153151
  · exact B1153155
  · exact B1153159
  · exact B1153163
  · exact B1153167
  · exact B1153171
  · exact B1153175
  · exact B1153179
  · exact B1153183
  · exact B1153187
  · exact B1153191
  · exact B1153195
  · exact B1153199
  · exact B1153203
  · exact B1153207
  · exact B1153211
  · exact B1153215
  · exact B1153219
  · exact B1153223
  · exact B1153227
  · exact B1153231
  · exact B1153235
  · exact B1153239
  · exact B1153243
  · exact B1153247
  · exact B1153251
  · exact B1153255
  · exact B1153259
  · exact B1153263
  · exact B1153267
  · exact B1153271
  · exact B1153275
  · exact B1153279
  · exact B1153283
  · exact B1153287
  · exact B1153291
  · exact B1153295
  · exact B1153299
  · exact B1153303
  · exact B1153307
  · exact B1153311
  · exact B1153315
  · exact B1153319
  · exact B1153323
  · exact B1153327
  · exact B1153331
  · exact B1153335
  · exact B1153339
  · exact B1153343
  · exact B1153347
  · exact B1153351
  · exact B1153355
  · exact B1153359
  · exact B1153363
  · exact B1153367
  · exact B1153371
  · exact B1153375
  · exact B1153379
  · exact B1153383
  · exact B1153387
  · exact B1153391
  · exact B1153395
  · exact B1153399
  · exact B1153403
  · exact B1153407
  · exact B1153411
  · exact B1153415
  · exact B1153419
  · exact B1153423
  · exact B1153427
  · exact B1153431
  · exact B1153435
  · exact B1153439
  · exact B1153443
  · exact B1153447
  · exact B1153451
  · exact B1153455
  · exact B1153459
  · exact B1153463
  · exact B1153467
  · exact B1153471
  · exact B1153475
  · exact B1153479
  · exact B1153483
  · exact B1153487
  · exact B1153491
  · exact B1153495
  · exact B1153499
  · exact B1153503
  · exact B1153507
  · exact B1153511
  · exact B1153515
  · exact B1153519
  · exact B1153523
  · exact B1153527
  · exact B1153531
  · exact B1153535
  · exact B1153539
  · exact B1153543
  · exact B1153547
  · exact B1153551
  · exact B1153555
  · exact B1153559
  · exact B1153563
  · exact B1153567
  · exact B1153571
  · exact B1153575
  · exact B1153579
  · exact B1153583
  · exact B1153587
  · exact B1153591
  · exact B1153595
  · exact B1153599
  · exact B1153603
  · exact B1153607
  · exact B1153611
  · exact B1153615
  · exact B1153619
  · exact B1153623
  · exact B1153627
  · exact B1153631
  · exact B1153635
  · exact B1153639
  · exact B1153643
  · exact B1153647
  · exact B1153651
  · exact B1153655
  · exact B1153659
  · exact B1153663
  · exact B1153667
  · exact B1153671
  · exact B1153675
  · exact B1153679
  · exact B1153683
  · exact B1153687
  · exact B1153691
  · exact B1153695
  · exact B1153699
  · exact B1153703
  · exact B1153707
  · exact B1153711
  · exact B1153715
  · exact B1153719
  · exact B1153723
  · exact B1153727
  · exact B1153731
  · exact B1153735
  · exact B1153739
  · exact B1153743
  · exact B1153747
  · exact B1153751
  · exact B1153755
  · exact B1153759
  · exact B1153763
  · exact B1153767
  · exact B1153771
  · exact B1153775
  · exact B1153779
  · exact B1153783
  · exact B1153787
  · exact B1153791
  · exact B1153795
  · exact B1153799
  · exact B1153803
  · exact B1153807
  · exact B1153811
  · exact B1153815
  · exact B1153819
  · exact B1153823
  · exact B1153827
  · exact B1153831
  · exact B1153835
  · exact B1153839
  · exact B1153843
  · exact B1153847
  · exact B1153851
  · exact B1153855
  · exact B1153859
  · exact B1153863
  · exact B1153867
  · exact B1153871
  · exact B1153875
  · exact B1153879
  · exact B1153883
  · exact B1153887
  · exact B1153891
  · exact B1153895
  · exact B1153899
  · exact B1153903
  · exact B1153907
  · exact B1153911
  · exact B1153915
  · exact B1153919
  · exact B1153923
  · exact B1153927
  · exact B1153931
  · exact B1153935
  · exact B1153939
  · exact B1153943
  · exact B1153947
  · exact B1153951
  · exact B1153955
  · exact B1153959
  · exact B1153963
  · exact B1153967
  · exact B1153971
  · exact B1153975
  · exact B1153979
  · exact B1153983
  · exact B1153987
  · exact B1153991
  · exact B1153995
  · exact B1153999
  · exact B1154003
  · exact B1154007
  · exact B1154011
  · exact B1154015
  · exact B1154019
  · exact B1154023
  · exact B1154027
  · exact B1154031
  · exact B1154035
  · exact B1154039
  · exact B1154043
  · exact B1154047
  · exact B1154051
  · exact B1154055
  · exact B1154059
  · exact B1154063
  · exact B1154067
  · exact B1154071
  · exact B1154075
  · exact B1154079
  · exact B1154083
  · exact B1154087
  · exact B1154091
  · exact B1154095
  · exact B1154099
  · exact B1154103
  · exact B1154107
  · exact B1154111
  · exact B1154115
  · exact B1154119
  · exact B1154123
  · exact B1154127
  · exact B1154131
  · exact B1154135
  · exact B1154139
  · exact B1154143
  · exact B1154147
  · exact B1154151
  · exact B1154155
  · exact B1154159
  · exact B1154163
  · exact B1154167
  · exact B1154171
  · exact B1154175
  · exact B1154179
  · exact B1154183
  · exact B1154187
  · exact B1154191
  · exact B1154195
  · exact B1154199
  · exact B1154203
  · exact B1154207
  · exact B1154211
  · exact B1154215
  · exact B1154219
  · exact B1154223
  · exact B1154227
  · exact B1154231
  · exact B1154235
  · exact B1154239
  · exact B1154243
  · exact B1154247
  · exact B1154251
  · exact B1154255
  · exact B1154259
  · exact B1154263
  · exact B1154267
  · exact B1154271
  · exact B1154275
  · exact B1154279
  · exact B1154283
  · exact B1154287
  · exact B1154291
  · exact B1154295
  · exact B1154299
  · exact B1154303
  · exact B1154307
  · exact B1154311
  · exact B1154315
  · exact B1154319
  · exact B1154323
  · exact B1154327
  · exact B1154331
  · exact B1154335
  · exact B1154339
  · exact B1154343
  · exact B1154347
  · exact B1154351
  · exact B1154355
  · exact B1154359
  · exact B1154363
  · exact B1154367
  · exact B1154371
  · exact B1154375
  · exact B1154379
  · exact B1154383
  · exact B1154387
  · exact B1154391
  · exact B1154395
  · exact B1154399
  · exact B1154403
  · exact B1154407
  · exact B1154411
  · exact B1154415
  · exact B1154419
  · exact B1154423
  · exact B1154427
  · exact B1154431
  · exact B1154435
  · exact B1154439
  · exact B1154443
  · exact B1154447
  · exact B1154451
  · exact B1154455
  · exact B1154459
  · exact B1154463
  · exact B1154467
  · exact B1154471
  · exact B1154475
  · exact B1154479
  · exact B1154483
  · exact B1154487
  · exact B1154491
  · exact B1154495
  · exact B1154499
  · exact B1154503
  · exact B1154507
  · exact B1154511
  · exact B1154515
  · exact B1154519
  · exact B1154523
  · exact B1154527
  · exact B1154531
  · exact B1154535
  · exact B1154539
  · exact B1154543
  · exact B1154547
  · exact B1154551
  · exact B1154555
  · exact B1154559
  · exact B1154563
  · exact B1154567
  · exact B1154571
  · exact B1154575
  · exact B1154579
  · exact B1154583
  · exact B1154587
  · exact B1154591
  · exact B1154595
  · exact B1154599
  · exact B1154603
  · exact B1154607
  · exact B1154611
  · exact B1154615
  · exact B1154619
  · exact B1154623
  · exact B1154627
  · exact B1154631
  · exact B1154635
  · exact B1154639
  · exact B1154643
  · exact B1154647
  · exact B1154651
  · exact B1154655
  · exact B1154659
  · exact B1154663
  · exact B1154667
  · exact B1154671
  · exact B1154675
  · exact B1154679
  · exact B1154683
  · exact B1154687
  · exact B1154691
  · exact B1154695
  · exact B1154699
  · exact B1154703
  · exact B1154707
  · exact B1154711
  · exact B1154715
  · exact B1154719
  · exact B1154723
  · exact B1154727
  · exact B1154731
  · exact B1154735
  · exact B1154739
  · exact B1154743
  · exact B1154747
  · exact B1154751
  · exact B1154755
  · exact B1154759
  · exact B1154763
  · exact B1154767
  · exact B1154771
  · exact B1154775
  · exact B1154779
  · exact B1154783
  · exact B1154787
  · exact B1154791
  · exact B1154795
  · exact B1154799
  · exact B1154803
  · exact B1154807
  · exact B1154811
  · exact B1154815
  · exact B1154819
  · exact B1154823
  · exact B1154827
  · exact B1154831
  · exact B1154835
  · exact B1154839
  · exact B1154843
  · exact B1154847
  · exact B1154851
  · exact B1154855
  · exact B1154859
  · exact B1154863
  · exact B1154867
  · exact B1154871
  · exact B1154875
  · exact B1154879
  · exact B1154883
  · exact B1154887
  · exact B1154891
  · exact B1154895
  · exact B1154899
  · exact B1154903
  · exact B1154907
  · exact B1154911
  · exact B1154915
  · exact B1154919
  · exact B1154923
  · exact B1154927
  · exact B1154931
  · exact B1154935
  · exact B1154939
  · exact B1154943
  · exact B1154947
  · exact B1154951
  · exact B1154955
  · exact B1154959
  · exact B1154963
  · exact B1154967
  · exact B1154971
  · exact B1154975
  · exact B1154979
  · exact B1154983
  · exact B1154987
  · exact B1154991
  · exact B1154995
  · exact B1154999
  · exact B1155003
  · exact B1155007
  · exact B1155011
  · exact B1155015
  · exact B1155019
  · exact B1155023
  · exact B1155027
  · exact B1155031
  · exact B1155035
  · exact B1155039
  · exact B1155043
  · exact B1155047
  · exact B1155051
  · exact B1155055
  · exact B1155059
  · exact B1155063
  · exact B1155067
  · exact B1155071
  · exact B1155075
  · exact B1155079
  · exact B1155083
  · exact B1155087
  · exact B1155091
  · exact B1155095
  · exact B1155099
  · exact B1155103
  · exact B1155107
  · exact B1155111
  · exact B1155115
  · exact B1155119
  · exact B1155123
  · exact B1155127
  · exact B1155131
  · exact B1155135
  · exact B1155139
  · exact B1155143
  · exact B1155147
  · exact B1155151
  · exact B1155155
  · exact B1155159
  · exact B1155163
  · exact B1155167
  · exact B1155171
  · exact B1155175
  · exact B1155179
  · exact B1155183
  · exact B1155187
  · exact B1155191
  · exact B1155195
  · exact B1155199
  · exact B1155203
  · exact B1155207
  · exact B1155211
  · exact B1155215
  · exact B1155219
  · exact B1155223
  · exact B1155227
  · exact B1155231
  · exact B1155235
  · exact B1155239
  · exact B1155243
  · exact B1155247
  · exact B1155251
  · exact B1155255
  · exact B1155259
  · exact B1155263
  · exact B1155267
  · exact B1155271
  · exact B1155275
  · exact B1155279
  · exact B1155283
  · exact B1155287
  · exact B1155291
  · exact B1155295
  · exact B1155299
  · exact B1155303
  · exact B1155307
  · exact B1155311
  · exact B1155315
  · exact B1155319
  · exact B1155323
  · exact B1155327
  · exact B1155331
  · exact B1155335
  · exact B1155339
  · exact B1155343
  · exact B1155347
  · exact B1155351
  · exact B1155355
  · exact B1155359
  · exact B1155363
  · exact B1155367
  · exact B1155371
  · exact B1155375
  · exact B1155379
  · exact B1155383
  · exact B1155387
  · exact B1155391
  · exact B1155395
  · exact B1155399
  · exact B1155403
  · exact B1155407
  · exact B1155411
  · exact B1155415
  · exact B1155419
  · exact B1155423
  · exact B1155427
  · exact B1155431
  · exact B1155435

theorem C1 (j : ℕ) (h1 : 288859 ≤ j) (h2 : j ≤ 289158) : Blo 1152637 (4 * j + 3) := by
  interval_cases j
  · exact B1155439
  · exact B1155443
  · exact B1155447
  · exact B1155451
  · exact B1155455
  · exact B1155459
  · exact B1155463
  · exact B1155467
  · exact B1155471
  · exact B1155475
  · exact B1155479
  · exact B1155483
  · exact B1155487
  · exact B1155491
  · exact B1155495
  · exact B1155499
  · exact B1155503
  · exact B1155507
  · exact B1155511
  · exact B1155515
  · exact B1155519
  · exact B1155523
  · exact B1155527
  · exact B1155531
  · exact B1155535
  · exact B1155539
  · exact B1155543
  · exact B1155547
  · exact B1155551
  · exact B1155555
  · exact B1155559
  · exact B1155563
  · exact B1155567
  · exact B1155571
  · exact B1155575
  · exact B1155579
  · exact B1155583
  · exact B1155587
  · exact B1155591
  · exact B1155595
  · exact B1155599
  · exact B1155603
  · exact B1155607
  · exact B1155611
  · exact B1155615
  · exact B1155619
  · exact B1155623
  · exact B1155627
  · exact B1155631
  · exact B1155635
  · exact B1155639
  · exact B1155643
  · exact B1155647
  · exact B1155651
  · exact B1155655
  · exact B1155659
  · exact B1155663
  · exact B1155667
  · exact B1155671
  · exact B1155675
  · exact B1155679
  · exact B1155683
  · exact B1155687
  · exact B1155691
  · exact B1155695
  · exact B1155699
  · exact B1155703
  · exact B1155707
  · exact B1155711
  · exact B1155715
  · exact B1155719
  · exact B1155723
  · exact B1155727
  · exact B1155731
  · exact B1155735
  · exact B1155739
  · exact B1155743
  · exact B1155747
  · exact B1155751
  · exact B1155755
  · exact B1155759
  · exact B1155763
  · exact B1155767
  · exact B1155771
  · exact B1155775
  · exact B1155779
  · exact B1155783
  · exact B1155787
  · exact B1155791
  · exact B1155795
  · exact B1155799
  · exact B1155803
  · exact B1155807
  · exact B1155811
  · exact B1155815
  · exact B1155819
  · exact B1155823
  · exact B1155827
  · exact B1155831
  · exact B1155835
  · exact B1155839
  · exact B1155843
  · exact B1155847
  · exact B1155851
  · exact B1155855
  · exact B1155859
  · exact B1155863
  · exact B1155867
  · exact B1155871
  · exact B1155875
  · exact B1155879
  · exact B1155883
  · exact B1155887
  · exact B1155891
  · exact B1155895
  · exact B1155899
  · exact B1155903
  · exact B1155907
  · exact B1155911
  · exact B1155915
  · exact B1155919
  · exact B1155923
  · exact B1155927
  · exact B1155931
  · exact B1155935
  · exact B1155939
  · exact B1155943
  · exact B1155947
  · exact B1155951
  · exact B1155955
  · exact B1155959
  · exact B1155963
  · exact B1155967
  · exact B1155971
  · exact B1155975
  · exact B1155979
  · exact B1155983
  · exact B1155987
  · exact B1155991
  · exact B1155995
  · exact B1155999
  · exact B1156003
  · exact B1156007
  · exact B1156011
  · exact B1156015
  · exact B1156019
  · exact B1156023
  · exact B1156027
  · exact B1156031
  · exact B1156035
  · exact B1156039
  · exact B1156043
  · exact B1156047
  · exact B1156051
  · exact B1156055
  · exact B1156059
  · exact B1156063
  · exact B1156067
  · exact B1156071
  · exact B1156075
  · exact B1156079
  · exact B1156083
  · exact B1156087
  · exact B1156091
  · exact B1156095
  · exact B1156099
  · exact B1156103
  · exact B1156107
  · exact B1156111
  · exact B1156115
  · exact B1156119
  · exact B1156123
  · exact B1156127
  · exact B1156131
  · exact B1156135
  · exact B1156139
  · exact B1156143
  · exact B1156147
  · exact B1156151
  · exact B1156155
  · exact B1156159
  · exact B1156163
  · exact B1156167
  · exact B1156171
  · exact B1156175
  · exact B1156179
  · exact B1156183
  · exact B1156187
  · exact B1156191
  · exact B1156195
  · exact B1156199
  · exact B1156203
  · exact B1156207
  · exact B1156211
  · exact B1156215
  · exact B1156219
  · exact B1156223
  · exact B1156227
  · exact B1156231
  · exact B1156235
  · exact B1156239
  · exact B1156243
  · exact B1156247
  · exact B1156251
  · exact B1156255
  · exact B1156259
  · exact B1156263
  · exact B1156267
  · exact B1156271
  · exact B1156275
  · exact B1156279
  · exact B1156283
  · exact B1156287
  · exact B1156291
  · exact B1156295
  · exact B1156299
  · exact B1156303
  · exact B1156307
  · exact B1156311
  · exact B1156315
  · exact B1156319
  · exact B1156323
  · exact B1156327
  · exact B1156331
  · exact B1156335
  · exact B1156339
  · exact B1156343
  · exact B1156347
  · exact B1156351
  · exact B1156355
  · exact B1156359
  · exact B1156363
  · exact B1156367
  · exact B1156371
  · exact B1156375
  · exact B1156379
  · exact B1156383
  · exact B1156387
  · exact B1156391
  · exact B1156395
  · exact B1156399
  · exact B1156403
  · exact B1156407
  · exact B1156411
  · exact B1156415
  · exact B1156419
  · exact B1156423
  · exact B1156427
  · exact B1156431
  · exact B1156435
  · exact B1156439
  · exact B1156443
  · exact B1156447
  · exact B1156451
  · exact B1156455
  · exact B1156459
  · exact B1156463
  · exact B1156467
  · exact B1156471
  · exact B1156475
  · exact B1156479
  · exact B1156483
  · exact B1156487
  · exact B1156491
  · exact B1156495
  · exact B1156499
  · exact B1156503
  · exact B1156507
  · exact B1156511
  · exact B1156515
  · exact B1156519
  · exact B1156523
  · exact B1156527
  · exact B1156531
  · exact B1156535
  · exact B1156539
  · exact B1156543
  · exact B1156547
  · exact B1156551
  · exact B1156555
  · exact B1156559
  · exact B1156563
  · exact B1156567
  · exact B1156571
  · exact B1156575
  · exact B1156579
  · exact B1156583
  · exact B1156587
  · exact B1156591
  · exact B1156595
  · exact B1156599
  · exact B1156603
  · exact B1156607
  · exact B1156611
  · exact B1156615
  · exact B1156619
  · exact B1156623
  · exact B1156627
  · exact B1156631
  · exact B1156635

theorem solution (m : ℕ) (hlo : 1152637 ≤ m) (hhi : m ≤ 1156637) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 288159 ≤ j := by omega
    have hj2 : j ≤ 289158 := by omega
    have hb : Blo 1152637 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 288859 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
